module

public import DeepLean.Attention.JetRecovery
public import Mathlib.Algebra.Polynomial.Roots

/-! # Simultaneous avoidance of finitely many quadratic loci -/

@[expose] public section

namespace NormalizedDeepAttention

open Polynomial

private noncomputable def quadraticScalarPolynomial (A B C : ℝ) : ℝ[X] :=
  Polynomial.C A + Polynomial.C B * Polynomial.X +
    Polynomial.C C * Polynomial.X ^ 2

private noncomputable def linearScalarPolynomial (P Q : ℝ) : ℝ[X] :=
  Polynomial.C P + Polynomial.C Q * Polynomial.X

@[simp] private theorem eval_quadraticScalarPolynomial (A B C s : ℝ) :
    (quadraticScalarPolynomial A B C).eval s = A + s * B + s ^ 2 * C := by
  simp [quadraticScalarPolynomial]
  ring

@[simp] private theorem eval_linearScalarPolynomial (P Q s : ℝ) :
    (linearScalarPolynomial P Q).eval s = P + s * Q := by
  simp [linearScalarPolynomial]
  ring

private theorem quadraticScalarPolynomial_ne_zero (A B C : ℝ)
    (h : A ≠ 0 ∨ C ≠ 0) : quadraticScalarPolynomial A B C ≠ 0 := by
  intro hz
  rcases h with hA | hC
  · have he := congrArg (Polynomial.eval 0) hz
    simp at he
    exact hA he
  · have he := congrArg (fun p : ℝ[X] ↦ p.coeff 2) hz
    simp [quadraticScalarPolynomial] at he
    exact hC he

private theorem linearScalarPolynomial_ne_zero (P Q : ℝ)
    (h : P ≠ 0 ∨ Q ≠ 0) : linearScalarPolynomial P Q ≠ 0 := by
  intro hz
  rcases h with hP | hQ
  · have he := congrArg (Polynomial.eval 0) hz
    simp at he
    exact hP he
  · have he := congrArg (fun p : ℝ[X] ↦ p.coeff 1) hz
    simp [linearScalarPolynomial] at he
    exact hQ he

/-- Two nonzero quadratics and one nonzero linear polynomial can be avoided
simultaneously over `ℝ`. -/
theorem exists_scalar_two_quadratic_linear_ne_zero
    (A₁ B₁ C₁ A₂ B₂ C₂ P Q : ℝ)
    (h₁ : A₁ ≠ 0 ∨ C₁ ≠ 0) (h₂ : A₂ ≠ 0 ∨ C₂ ≠ 0)
    (hlin : P ≠ 0 ∨ Q ≠ 0) :
    ∃ s : ℝ,
      A₁ + s * B₁ + s ^ 2 * C₁ ≠ 0 ∧
      A₂ + s * B₂ + s ^ 2 * C₂ ≠ 0 ∧ P + s * Q ≠ 0 := by
  let f₁ := quadraticScalarPolynomial A₁ B₁ C₁
  let f₂ := quadraticScalarPolynomial A₂ B₂ C₂
  let g := linearScalarPolynomial P Q
  have hf₁ : f₁ ≠ 0 := quadraticScalarPolynomial_ne_zero _ _ _ h₁
  have hf₂ : f₂ ≠ 0 := quadraticScalarPolynomial_ne_zero _ _ _ h₂
  have hg : g ≠ 0 := linearScalarPolynomial_ne_zero _ _ hlin
  have hprod : f₁ * f₂ * g ≠ 0 := mul_ne_zero (mul_ne_zero hf₁ hf₂) hg
  obtain ⟨s, hs⟩ : ∃ s : ℝ, (f₁ * f₂ * g).eval s ≠ 0 := by
    by_contra h
    push Not at h
    exact hprod (Polynomial.zero_of_eval_zero _ h)
  have hsprod : f₁.eval s * f₂.eval s * g.eval s ≠ 0 := by
    simpa using hs
  refine ⟨s, ?_, ?_, ?_⟩
  · simpa [f₁] using (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hsprod).1).1
  · simpa [f₂] using (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hsprod).1).2
  · simpa [g] using (mul_ne_zero_iff.mp hsprod).2

private theorem exists_mulVec_ne_zero_of_matrix_ne_zero₂ {m n : ℕ}
    (L : Matrix (Fin m) (Fin n) ℝ) (hL : L ≠ 0) :
    ∃ u : Fin n → ℝ, L.mulVec u ≠ 0 := by
  by_contra h
  push Not at h
  apply hL
  ext r c
  have hc := congrFun (h (Pi.single c 1)) r
  simpa [Matrix.mulVec, Pi.single_apply] using hc

private theorem quadratic_add_smul₂ {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ) (s : ℝ) :
    dotProduct (u + s • v) (M.mulVec (u + s • v)) =
      dotProduct u (M.mulVec u) +
        s * (dotProduct u (M.mulVec v) + dotProduct v (M.mulVec u)) +
        s ^ 2 * dotProduct v (M.mulVec v) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
    smul_dotProduct, dotProduct_add, dotProduct_smul]
  ring

private theorem mulVec_add_smul_apply₂ {d dOut : ℕ}
    (L : Matrix (Fin dOut) (Fin d) ℝ) (u v : Fin d → ℝ)
    (s : ℝ) (r : Fin dOut) :
    (L.mulVec (u + s • v)) r = (L.mulVec u) r + s * (L.mulVec v) r := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul]
  rfl

/-- A nonzero value map and two non-skew score matrices have a direction that
simultaneously avoids all three exceptional loci. -/
theorem exists_visible_two_nonisotropic {d dOut : ℕ}
    (L : Matrix (Fin dOut) (Fin d) ℝ)
    (M₁ M₂ : Matrix (Fin d) (Fin d) ℝ)
    (hL : L ≠ 0) (hM₁ : M₁.transpose ≠ -M₁) (hM₂ : M₂.transpose ≠ -M₂) :
    ∃ v : Fin d → ℝ,
      dotProduct v (M₁.mulVec v) ≠ 0 ∧
      dotProduct v (M₂.mulVec v) ≠ 0 ∧ L.mulVec v ≠ 0 := by
  obtain ⟨p₁, hp₁⟩ := exists_quadratic_ne_zero_of_not_skew M₁ hM₁
  obtain ⟨p₂, hp₂⟩ := exists_quadratic_ne_zero_of_not_skew M₂ hM₂
  obtain ⟨w, hwL⟩ := exists_mulVec_ne_zero_of_matrix_ne_zero₂ L hL
  obtain ⟨r, hr⟩ : ∃ r, (L.mulVec w) r ≠ 0 := by
    by_contra h
    push Not at h
    exact hwL (funext h)
  obtain ⟨s₁, hs₁M, _, hs₁L⟩ := exists_scalar_two_quadratic_linear_ne_zero
    (dotProduct w (M₁.mulVec w))
    (dotProduct w (M₁.mulVec p₁) + dotProduct p₁ (M₁.mulVec w))
    (dotProduct p₁ (M₁.mulVec p₁))
    1 0 0 (L.mulVec w r) (L.mulVec p₁ r)
    (Or.inr hp₁) (Or.inl one_ne_zero) (Or.inl hr)
  let v₁ := w + s₁ • p₁
  have hv₁M₁ : dotProduct v₁ (M₁.mulVec v₁) ≠ 0 := by
    rw [quadratic_add_smul₂]
    exact hs₁M
  have hv₁L : L.mulVec v₁ ≠ 0 := by
    intro hz
    have he := congrFun hz r
    rw [mulVec_add_smul_apply₂] at he
    exact hs₁L he
  obtain ⟨r₁, hr₁⟩ : ∃ r₁, (L.mulVec v₁) r₁ ≠ 0 := by
    by_contra h
    push Not at h
    exact hv₁L (funext h)
  obtain ⟨s₂, hs₂M₁, hs₂M₂, hs₂L⟩ := exists_scalar_two_quadratic_linear_ne_zero
    (dotProduct v₁ (M₁.mulVec v₁))
    (dotProduct v₁ (M₁.mulVec p₂) + dotProduct p₂ (M₁.mulVec v₁))
    (dotProduct p₂ (M₁.mulVec p₂))
    (dotProduct v₁ (M₂.mulVec v₁))
    (dotProduct v₁ (M₂.mulVec p₂) + dotProduct p₂ (M₂.mulVec v₁))
    (dotProduct p₂ (M₂.mulVec p₂))
    (L.mulVec v₁ r₁) (L.mulVec p₂ r₁)
    (Or.inl hv₁M₁) (Or.inr hp₂) (Or.inl hr₁)
  let v := v₁ + s₂ • p₂
  refine ⟨v, ?_, ?_, ?_⟩
  · rw [quadratic_add_smul₂]
    exact hs₂M₁
  · rw [quadratic_add_smul₂]
    exact hs₂M₂
  · intro hz
    have he := congrFun hz r₁
    rw [mulVec_add_smul_apply₂] at he
    exact hs₂L he

/-- Directions simultaneously visible and nonisotropic for two non-skew matrices
are sufficient to identify an arbitrary bilinear score matrix. -/
theorem matrix_eq_of_eq_on_visible_two_nonisotropic {d dOut : ℕ}
    (L : Matrix (Fin dOut) (Fin d) ℝ)
    (M₁ M₂ N N' : Matrix (Fin d) (Fin d) ℝ)
    (hL : L ≠ 0) (hM₁ : M₁.transpose ≠ -M₁) (hM₂ : M₂.transpose ≠ -M₂)
    (hgood : ∀ u : Fin d → ℝ,
      dotProduct u (M₁.mulVec u) ≠ 0 →
      dotProduct u (M₂.mulVec u) ≠ 0 → L.mulVec u ≠ 0 →
      ∀ x : Fin d → ℝ,
        dotProduct x (N.mulVec u) = dotProduct x (N'.mulVec u)) :
    N = N' := by
  obtain ⟨v, hvM₁, hvM₂, hvL⟩ :=
    exists_visible_two_nonisotropic L M₁ M₂ hL hM₁ hM₂
  have hv := hgood v hvM₁ hvM₂ hvL
  obtain ⟨r, hr⟩ : ∃ r, (L.mulVec v) r ≠ 0 := by
    by_contra h
    push Not at h
    exact hvL (funext h)
  apply Matrix.ext
  intro i j
  let u : Fin d → ℝ := Pi.single j 1
  obtain ⟨s, hsM₁, hsM₂, hsL⟩ := exists_scalar_two_quadratic_linear_ne_zero
    (dotProduct u (M₁.mulVec u))
    (dotProduct u (M₁.mulVec v) + dotProduct v (M₁.mulVec u))
    (dotProduct v (M₁.mulVec v))
    (dotProduct u (M₂.mulVec u))
    (dotProduct u (M₂.mulVec v) + dotProduct v (M₂.mulVec u))
    (dotProduct v (M₂.mulVec v))
    (L.mulVec u r) (L.mulVec v r)
    (Or.inr hvM₁) (Or.inr hvM₂) (Or.inr hr)
  let z := u + s • v
  have hzM₁ : dotProduct z (M₁.mulVec z) ≠ 0 := by
    rw [quadratic_add_smul₂]
    exact hsM₁
  have hzM₂ : dotProduct z (M₂.mulVec z) ≠ 0 := by
    rw [quadratic_add_smul₂]
    exact hsM₂
  have hzL : L.mulVec z ≠ 0 := by
    intro h
    have he := congrFun h r
    rw [mulVec_add_smul_apply₂] at he
    exact hsL he
  have hz := hgood z hzM₁ hzM₂ hzL (Pi.single i 1)
  have hv' := hv (Pi.single i 1)
  simp only [z, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    dotProduct_smul] at hz
  simp only [smul_eq_mul] at hz
  rw [hv'] at hz
  have hu : dotProduct (Pi.single i 1) (N.mulVec u) =
      dotProduct (Pi.single i 1) (N'.mulVec u) := by
    linarith
  simpa [u, Matrix.mulVec, dotProduct, Pi.single_apply] using hu

/-! The list versions below are used for arbitrary finite depth. -/

/-- Finitely many nonzero quadratic polynomials and one nonzero linear
polynomial can be avoided simultaneously over `ℝ`. -/
theorem exists_scalar_quadratics_linear_ne_zero
    (cs : List (ℝ × ℝ × ℝ)) (P Q : ℝ)
    (hcs : ∀ c ∈ cs, c.1 ≠ 0 ∨ c.2.2 ≠ 0)
    (hlin : P ≠ 0 ∨ Q ≠ 0) :
    ∃ s : ℝ, (∀ c ∈ cs, c.1 + s * c.2.1 + s ^ 2 * c.2.2 ≠ 0) ∧
      P + s * Q ≠ 0 := by
  let ps : List ℝ[X] := cs.map fun c ↦ quadraticScalarPolynomial c.1 c.2.1 c.2.2
  let g := linearScalarPolynomial P Q
  have hps : 0 ∉ ps := by
    intro hz
    simp only [ps, List.mem_map] at hz
    obtain ⟨c, hc, hc0⟩ := hz
    rcases c with ⟨A, B, C⟩
    apply quadraticScalarPolynomial_ne_zero A B C (hcs (A, B, C) hc)
    simpa using hc0
  have hprod : ps.prod * g ≠ 0 :=
    mul_ne_zero (List.prod_ne_zero hps) (linearScalarPolynomial_ne_zero _ _ hlin)
  obtain ⟨s, hs⟩ : ∃ s : ℝ, (ps.prod * g).eval s ≠ 0 := by
    by_contra h
    push Not at h
    exact hprod (Polynomial.zero_of_eval_zero _ h)
  refine ⟨s, ?_, ?_⟩
  · intro c hc heval
    have hmem : quadraticScalarPolynomial c.1 c.2.1 c.2.2 ∈ ps := by
      exact List.mem_map.mpr ⟨c, hc, rfl⟩
    have hzprod : ps.prod.eval s = 0 := by
      rw [Polynomial.eval_list_prod, List.prod_eq_zero_iff, List.mem_map]
      exact ⟨quadraticScalarPolynomial c.1 c.2.1 c.2.2, hmem, by simpa using heval⟩
    apply hs
    rw [Polynomial.eval_mul, hzprod, zero_mul]
  · intro heval
    apply hs
    have hg : g.eval s = 0 := by simpa [g] using heval
    rw [Polynomial.eval_mul, hg, mul_zero]

/-- A nonzero value map and any finite family of non-skew score matrices have
a direction visible through the value map and nonisotropic for every score. -/
theorem exists_visible_nonisotropic_list {d dOut : ℕ}
    (L : Matrix (Fin dOut) (Fin d) ℝ) (Ms : List (Matrix (Fin d) (Fin d) ℝ))
    (hL : L ≠ 0) (hMs : ∀ M ∈ Ms, M.transpose ≠ -M) :
    ∃ v : Fin d → ℝ,
      (∀ M ∈ Ms, dotProduct v (M.mulVec v) ≠ 0) ∧ L.mulVec v ≠ 0 := by
  induction Ms with
  | nil =>
      obtain ⟨v, hv⟩ := exists_mulVec_ne_zero_of_matrix_ne_zero₂ L hL
      exact ⟨v, by simp, hv⟩
  | cons M Ms ih =>
      obtain ⟨v, hvMs, hvL⟩ := ih (by
        intro N hN
        exact hMs N (by simp [hN]))
      obtain ⟨p, hp⟩ := exists_quadratic_ne_zero_of_not_skew M (hMs M (by simp))
      obtain ⟨r, hr⟩ : ∃ r, (L.mulVec v) r ≠ 0 := by
        by_contra h
        push Not at h
        exact hvL (funext h)
      let cs : List (ℝ × ℝ × ℝ) := (M :: Ms).map fun N ↦
        (dotProduct v (N.mulVec v),
          dotProduct v (N.mulVec p) + dotProduct p (N.mulVec v),
          dotProduct p (N.mulVec p))
      have hcs : ∀ c ∈ cs, c.1 ≠ 0 ∨ c.2.2 ≠ 0 := by
        intro c hc
        simp only [cs, List.mem_map] at hc
        obtain ⟨N, hN, rfl⟩ := hc
        rcases List.mem_cons.mp hN with rfl | hN
        · exact Or.inr hp
        · exact Or.inl (hvMs N hN)
      obtain ⟨s, hs, hsL⟩ := exists_scalar_quadratics_linear_ne_zero cs
        (L.mulVec v r) (L.mulVec p r) hcs (Or.inl hr)
      let z := v + s • p
      refine ⟨z, ?_, ?_⟩
      · intro N hN
        rw [quadratic_add_smul₂]
        exact hs _ (List.mem_map.mpr ⟨N, hN, rfl⟩)
      · intro hz
        have he := congrFun hz r
        rw [mulVec_add_smul_apply₂] at he
        exact hsL he

/-- Bilinear equality on directions simultaneously visible and nonisotropic for
a finite non-skew family determines the whole matrix. -/
theorem matrix_eq_of_eq_on_visible_nonisotropic_list {d dOut : ℕ}
    (L : Matrix (Fin dOut) (Fin d) ℝ)
    (Ms : List (Matrix (Fin d) (Fin d) ℝ))
    (N N' : Matrix (Fin d) (Fin d) ℝ)
    (hL : L ≠ 0) (hMs : ∀ M ∈ Ms, M.transpose ≠ -M)
    (hgood : ∀ u : Fin d → ℝ,
      (∀ M ∈ Ms, dotProduct u (M.mulVec u) ≠ 0) → L.mulVec u ≠ 0 →
      ∀ x : Fin d → ℝ, dotProduct x (N.mulVec u) = dotProduct x (N'.mulVec u)) :
    N = N' := by
  obtain ⟨v, hvMs, hvL⟩ := exists_visible_nonisotropic_list L Ms hL hMs
  have hv := hgood v hvMs hvL
  ext i j
  let u : Fin d → ℝ := Pi.single j 1
  obtain ⟨r, hr⟩ : ∃ r, (L.mulVec v) r ≠ 0 := by
    by_contra h
    push Not at h
    exact hvL (funext h)
  let cs : List (ℝ × ℝ × ℝ) := Ms.map fun M ↦
    (dotProduct u (M.mulVec u),
      dotProduct u (M.mulVec v) + dotProduct v (M.mulVec u),
      dotProduct v (M.mulVec v))
  have hcs : ∀ c ∈ cs, c.1 ≠ 0 ∨ c.2.2 ≠ 0 := by
    intro c hc
    simp only [cs, List.mem_map] at hc
    obtain ⟨M, hM, rfl⟩ := hc
    exact Or.inr (hvMs M hM)
  obtain ⟨s, hs, hsL⟩ := exists_scalar_quadratics_linear_ne_zero cs
    (L.mulVec u r) (L.mulVec v r) hcs (Or.inr hr)
  let z := u + s • v
  have hzMs : ∀ M ∈ Ms, dotProduct z (M.mulVec z) ≠ 0 := by
    intro M hM
    rw [quadratic_add_smul₂]
    exact hs _ (List.mem_map.mpr ⟨M, hM, rfl⟩)
  have hzL : L.mulVec z ≠ 0 := by
    intro h
    have he := congrFun h r
    rw [mulVec_add_smul_apply₂] at he
    exact hsL he
  have hz := hgood z hzMs hzL (Pi.single i 1)
  have hv' := hv (Pi.single i 1)
  simp only [z, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    dotProduct_smul, smul_eq_mul] at hz
  rw [hv'] at hz
  have hu : dotProduct (Pi.single i 1) (N.mulVec u) =
      dotProduct (Pi.single i 1) (N'.mulVec u) := by linarith
  simpa [u, Matrix.mulVec, dotProduct, Pi.single_apply] using hu

end NormalizedDeepAttention
