module

public import DeepLean.Attention.Basic

/-!
# Algebraic recovery from normalized-attention jets

The analytic expansion at a repeated-token input produces rank-one identities of the
form formalized below.  This file isolates the exact linear-algebra cancellation needed
to turn those observable identities into equality of virtual score matrices.
-/

@[expose] public section

namespace NormalizedDeepAttention

private theorem exists_mulVec_ne_zero_of_matrix_ne_zero {m n : ℕ}
    (L : Matrix (Fin m) (Fin n) ℝ) (hL : L ≠ 0) :
    ∃ u : Fin n → ℝ, L.mulVec u ≠ 0 := by
  by_contra h
  push Not at h
  apply hL
  ext r c
  have hc := congrFun (h (Pi.single c 1)) r
  simpa [Matrix.mulVec, Pi.single_apply] using hc

private theorem dotProduct_all_eq_zero_imp_eq_zero {n : ℕ} (z : Fin n → ℝ)
    (hz : ∀ x : Fin n → ℝ, dotProduct x z = 0) : z = 0 := by
  funext c
  have hc := hz (Pi.single c 1)
  simpa [dotProduct, Pi.single_apply] using hc

/-- A nonzero final value map cancels the rank-one covariance probes occurring in the
second-order repeated-token jet.  No injectivity or full-rank assumption on `L` is
needed. -/
theorem matrix_eq_zero_of_rankOne_jet_zero {d dOut : ℕ}
    (L : Matrix (Fin dOut) (Fin d) ℝ) (D : Matrix (Fin d) (Fin d) ℝ)
    (hL : L ≠ 0)
    (hprobe : ∀ (x u : Fin d → ℝ),
      (dotProduct x (D.mulVec u)) • L.mulVec u = 0) :
    D = 0 := by
  obtain ⟨v, hv⟩ := exists_mulVec_ne_zero_of_matrix_ne_zero L hL
  have hDu_of (u : Fin d → ℝ) (hu : L.mulVec u ≠ 0) : D.mulVec u = 0 := by
    apply dotProduct_all_eq_zero_imp_eq_zero
    intro x
    by_contra hs
    exact (smul_ne_zero hs hu) (hprobe x u)
  have hDv : D.mulVec v = 0 := hDu_of v hv
  have hDu (u : Fin d → ℝ) : D.mulVec u = 0 := by
    by_cases hu : L.mulVec u = 0
    · have hvu : L.mulVec (v + u) ≠ 0 := by
        rw [Matrix.mulVec_add, hu, add_zero]
        exact hv
      have hsum := hDu_of (v + u) hvu
      rw [Matrix.mulVec_add, hDv, zero_add] at hsum
      exact hsum
    · exact hDu_of u hu
  ext r c
  have hc := congrFun (hDu (Pi.single c 1)) r
  simpa [Matrix.mulVec, Pi.single_apply] using hc

/-- Equality of every rank-one jet probe identifies the score matrix. -/
theorem matrix_eq_of_rankOne_jets_eq {d dOut : ℕ}
    (L : Matrix (Fin dOut) (Fin d) ℝ)
    (M M' : Matrix (Fin d) (Fin d) ℝ) (hL : L ≠ 0)
    (hprobe : ∀ (x u : Fin d → ℝ),
      (dotProduct x (M.mulVec u)) • L.mulVec u =
        (dotProduct x (M'.mulVec u)) • L.mulVec u) :
    M = M' := by
  have hzero : M - M' = 0 :=
    matrix_eq_zero_of_rankOne_jet_zero L (M - M') hL (by
      intro x u
      rw [Matrix.sub_mulVec, dotProduct_sub, sub_smul]
      exact sub_eq_zero.mpr (hprobe x u))
  exact sub_eq_zero.mp hzero

/-- A matrix has identically zero quadratic form exactly only on the
skew-symmetric locus (the reverse implication is in `Counterexamples.lean`). -/
theorem exists_quadratic_ne_zero_of_not_skew {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.transpose ≠ -M) :
    ∃ u : Fin d → ℝ, dotProduct u (M.mulVec u) ≠ 0 := by
  by_contra h
  push Not at h
  apply hM
  have hswap (x y : Fin d → ℝ) :
      dotProduct x (M.mulVec y) = -dotProduct y (M.mulVec x) := by
    have hx := h x
    have hy := h y
    have hxy := h (x + y)
    simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add] at hxy
    linarith
  ext i j
  have hij := hswap (Pi.single j 1) (Pi.single i 1)
  simpa [Matrix.transpose_apply, Matrix.mulVec, dotProduct, Pi.single_apply] using hij

private theorem exists_scalar_quadratic_and_linear_ne_zero
    (A B C P Q : ℝ) (hC : C ≠ 0) (hlin : P ≠ 0 ∨ Q ≠ 0) :
    ∃ scl : ℝ, A + scl * B + scl ^ 2 * C ≠ 0 ∧ P + scl * Q ≠ 0 := by
  by_contra h
  push Not at h
  have hh (scl : ℝ) :
      A + scl * B + scl ^ 2 * C = 0 ∨ P + scl * Q = 0 := by
    by_cases hp : A + scl * B + scl ^ 2 * C = 0
    · exact Or.inl hp
    · exact Or.inr (h scl hp)
  have h1 := hh 1
  have h2 := hh 2
  have h3 := hh 3
  have h4 := hh 4
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4 <;>
    rcases hlin with hP | hQ
  all_goals first | exact hC (by nlinarith) | exact hP (by nlinarith) |
    exact hQ (by nlinarith)

private theorem quadratic_add_smul {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ) (scl : ℝ) :
    dotProduct (u + scl • v) (M.mulVec (u + scl • v)) =
      dotProduct u (M.mulVec u) +
        scl * (dotProduct u (M.mulVec v) + dotProduct v (M.mulVec u)) +
        scl ^ 2 * dotProduct v (M.mulVec v) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
    smul_dotProduct, dotProduct_add, dotProduct_smul]
  ring

private theorem mulVec_add_smul_apply {d dOut : ℕ}
    (L : Matrix (Fin dOut) (Fin d) ℝ) (u v : Fin d → ℝ)
    (scl : ℝ) (r : Fin dOut) :
    (L.mulVec (u + scl • v)) r = (L.mulVec u) r + scl * (L.mulVec v) r := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul]
  rfl

/-- A nonzero value map and one non-skew score matrix make the directions that are
simultaneously value-visible and quadratically nonisotropic sufficient to identify an
arbitrary bilinear score matrix. -/
theorem matrix_eq_of_eq_on_visible_nonisotropic {d dOut : ℕ}
    (L : Matrix (Fin dOut) (Fin d) ℝ)
    (M N N' : Matrix (Fin d) (Fin d) ℝ)
    (hL : L ≠ 0) (hM : M.transpose ≠ -M)
    (hgood : ∀ u : Fin d → ℝ,
      dotProduct u (M.mulVec u) ≠ 0 → L.mulVec u ≠ 0 →
      ∀ x : Fin d → ℝ,
        dotProduct x (N.mulVec u) = dotProduct x (N'.mulVec u)) :
    N = N' := by
  obtain ⟨p, hpM⟩ := exists_quadratic_ne_zero_of_not_skew M hM
  obtain ⟨w, hwL⟩ := exists_mulVec_ne_zero_of_matrix_ne_zero L hL
  obtain ⟨r, hr⟩ : ∃ r, (L.mulVec w) r ≠ 0 := by
    by_contra h
    push Not at h
    exact hwL (funext h)
  let A := dotProduct w (M.mulVec w)
  let B := dotProduct w (M.mulVec p) + dotProduct p (M.mulVec w)
  let C := dotProduct p (M.mulVec p)
  let P := (L.mulVec w) r
  let Q := (L.mulVec p) r
  obtain ⟨scl, hsclM, hsclL⟩ :=
    exists_scalar_quadratic_and_linear_ne_zero A B C P Q hpM (Or.inl hr)
  let v := w + scl • p
  have hvM : dotProduct v (M.mulVec v) ≠ 0 := by
    rw [quadratic_add_smul]
    exact hsclM
  have hvL : L.mulVec v ≠ 0 := by
    intro h
    have hz := congrFun h r
    rw [mulVec_add_smul_apply] at hz
    exact hsclL hz
  have hv := hgood v hvM hvL
  apply Matrix.ext
  intro i j
  let u : Fin d → ℝ := Pi.single j 1
  obtain ⟨s, hs⟩ : ∃ s, (L.mulVec v) s ≠ 0 := by
    by_contra h
    push Not at h
    exact hvL (funext h)
  let A' := dotProduct u (M.mulVec u)
  let B' := dotProduct u (M.mulVec v) + dotProduct v (M.mulVec u)
  let C' := dotProduct v (M.mulVec v)
  let P' := (L.mulVec u) s
  let Q' := (L.mulVec v) s
  obtain ⟨μ, hμM, hμL⟩ :=
    exists_scalar_quadratic_and_linear_ne_zero A' B' C' P' Q' hvM (Or.inr hs)
  let z := u + μ • v
  have hzM : dotProduct z (M.mulVec z) ≠ 0 := by
    rw [quadratic_add_smul]
    exact hμM
  have hzL : L.mulVec z ≠ 0 := by
    intro h
    have hz := congrFun h s
    rw [mulVec_add_smul_apply] at hz
    exact hμL hz
  have hz := hgood z hzM hzL (Pi.single i 1)
  have hv' := hv (Pi.single i 1)
  simp only [z, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    dotProduct_smul] at hz
  simp only [smul_eq_mul] at hz
  rw [hv'] at hz
  have hu : dotProduct (Pi.single i 1) (N.mulVec u) =
      dotProduct (Pi.single i 1) (N'.mulVec u) := by
    linarith
  simpa [u, Matrix.mulVec, dotProduct, Pi.single_apply] using hu

end NormalizedDeepAttention
