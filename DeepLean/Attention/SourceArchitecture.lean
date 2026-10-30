module

public import DeepLean.Attention.Basic

/-!
# Source architecture and the normalized virtual-coordinate bridge

This file connects the paper's variable-width raw `(A,V)` architecture to the
fixed input-space virtual matrices used by the identifiability theorem.  It is
the normalized analogue of `deepLightningAttention_eq_virtual`.
-/

@[expose] public section

namespace NormalizedDeepAttention

/-- The normalized layer is linear in its value matrix. -/
theorem normalizedAttention_mul_value {d m n t : ℕ} (S : ℝ → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin m) (Fin d) ℝ) (X : Matrix (Fin d) (Fin t) ℝ) :
    normalizedAttention S A (B * C) X = B * normalizedAttention S A C X := by
  ext r i
  have hvalue (j : Fin t) : ((B * C).mulVec (X.col j)) r =
      ∑ q : Fin m, B r q * (C.mulVec (X.col j)) q := by
    rw [← Matrix.mulVec_mulVec]
    rfl
  simp only [normalizedAttention, hvalue, Matrix.mul_apply, div_eq_mul_inv,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A change of state coordinates can be moved from the input into both the
score and value matrices. -/
theorem normalizedAttention_input_mul {d m n t : ℕ} (S : ℝ → ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin m) ℝ)
    (L : Matrix (Fin m) (Fin d) ℝ) (X : Matrix (Fin d) (Fin t) ℝ) :
    normalizedAttention S A V (L * X) =
      normalizedAttention S (L.transpose * A * L) (V * L) X := by
  ext r i
  have hcol (j : Fin t) : (L * X).col j = L.mulVec (X.col j) := by
    rfl
  have hscore (j : Fin t) :
      attentionScore A (L * X) i j =
        attentionScore (L.transpose * A * L) X i j := by
    simp only [attentionScore, hcol, Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.dotProduct_mulVec]
  simp only [normalizedAttention, hscore, hcol, Matrix.mulVec_mulVec]

/-- A change of state coordinates can be moved from the input and value map
into the score matrix.  This is the one-layer algebra behind Equation (8). -/
theorem normalizedAttention_change_coordinates {d m n t : ℕ} (S : ℝ → ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin m) ℝ)
    (L : Matrix (Fin m) (Fin d) ℝ) (X : Matrix (Fin d) (Fin t) ℝ) :
    normalizedAttention S A V (L * X) =
      (V * L) * normalizedAttention S (L.transpose * A * L) 1 X := by
  calc
    _ = normalizedAttention S (L.transpose * A * L) (V * L) X :=
      normalizedAttention_input_mul S A V L X
    _ = (V * L) * normalizedAttention S (L.transpose * A * L)
        (1 : Matrix (Fin d) (Fin d) ℝ) X := by
      simpa only [Matrix.mul_one] using
        (normalizedAttention_mul_value (d := d) (m := d) (n := n)
          S (L.transpose * A * L) (V * L) 1 X)

/-- Definition 2 with Equation (15) in every layer, allowing the paper's full
dimension sequence `d₀,…,dₗ`. -/
noncomputable def deepNormalizedPrefixAux {l t : ℕ} {dim : Fin (l + 1) → ℕ}
    (S : ℝ → ℝ) (W : DeepAttentionWeights l dim)
    (X : Matrix (Fin (dim 0)) (Fin t) ℝ)
    (n : ℕ) (hn : n ≤ l) : Matrix (Fin (dim ⟨n, Nat.lt_succ_of_le hn⟩)) (Fin t) ℝ :=
  match n with
  | 0 => X
  | n + 1 =>
      let i : Fin l := ⟨n, Nat.lt_of_succ_le hn⟩
      normalizedAttention S (W.A i) (W.V i)
        (deepNormalizedPrefixAux S W X n (Nat.le_of_succ_le hn))

noncomputable def deepNormalizedPrefix {l t : ℕ} {dim : Fin (l + 1) → ℕ}
    (S : ℝ → ℝ) (W : DeepAttentionWeights l dim)
    (X : Matrix (Fin (dim 0)) (Fin t) ℝ) (i : Fin (l + 1)) :
    Matrix (Fin (dim i)) (Fin t) ℝ :=
  deepNormalizedPrefixAux S W X i.val (Nat.le_of_lt_succ i.isLt)

noncomputable def deepNormalizedAttention {l t : ℕ} {dim : Fin (l + 1) → ℕ}
    (S : ℝ → ℝ) (W : DeepAttentionWeights l dim) :
    Matrix (Fin (dim 0)) (Fin t) ℝ →
      Matrix (Fin (dim (Fin.last l))) (Fin t) ℝ :=
  fun X ↦ deepNormalizedPrefix S W X (Fin.last l)

@[simp] theorem deepNormalizedPrefix_zero {l t : ℕ} {dim : Fin (l + 1) → ℕ}
    (S : ℝ → ℝ) (W : DeepAttentionWeights l dim)
    (X : Matrix (Fin (dim 0)) (Fin t) ℝ) :
    deepNormalizedPrefix S W X 0 = X := by
  rfl

@[simp] theorem deepNormalizedPrefix_succ {l t : ℕ} {dim : Fin (l + 1) → ℕ}
    (S : ℝ → ℝ) (W : DeepAttentionWeights l dim)
    (X : Matrix (Fin (dim 0)) (Fin t) ℝ) (i : Fin l) :
    deepNormalizedPrefix S W X i.succ =
      normalizedAttention S (W.A i) (W.V i)
        (deepNormalizedPrefix S W X i.castSucc) := by
  rfl

/-- Canonical normalized states in the original input space.  At step `i`,
the scores are the paper's virtual matrices `M₁,…,Mᵢ`. -/
noncomputable def normalizedVirtualPrefix {l t : ℕ} {dim : Fin (l + 1) → ℕ}
    (S : ℝ → ℝ) (W : DeepAttentionWeights l dim)
    (X : Matrix (Fin (dim 0)) (Fin t) ℝ) :
    Fin (l + 1) → Matrix (Fin (dim 0)) (Fin t) ℝ :=
  fun i ↦ Fin.induction X
    (fun j Z ↦ normalizedAttention S (virtualM W j) 1 Z) i

@[simp] theorem normalizedVirtualPrefix_zero {l t : ℕ}
    {dim : Fin (l + 1) → ℕ} (S : ℝ → ℝ) (W : DeepAttentionWeights l dim)
    (X : Matrix (Fin (dim 0)) (Fin t) ℝ) :
    normalizedVirtualPrefix S W X 0 = X := by
  simp [normalizedVirtualPrefix]

@[simp] theorem normalizedVirtualPrefix_succ {l t : ℕ}
    {dim : Fin (l + 1) → ℕ} (S : ℝ → ℝ) (W : DeepAttentionWeights l dim)
    (X : Matrix (Fin (dim 0)) (Fin t) ℝ) (i : Fin l) :
    normalizedVirtualPrefix S W X i.succ =
      normalizedAttention S (virtualM W i) 1
        (normalizedVirtualPrefix S W X i.castSucc) := by
  simp [normalizedVirtualPrefix]

/-- Exact variable-width raw-to-virtual equivalence after every prefix. -/
theorem deepNormalizedPrefix_eq_virtual {l t : ℕ} {dim : Fin (l + 1) → ℕ}
    (S : ℝ → ℝ) (W : DeepAttentionWeights l dim)
    (X : Matrix (Fin (dim 0)) (Fin t) ℝ) (i : Fin (l + 1)) :
    deepNormalizedPrefix S W X i =
      valuePrefix W i * normalizedVirtualPrefix S W X i := by
  refine Fin.induction ?_ ?_ i
  · simp
  · intro j ih
    rw [deepNormalizedPrefix_succ, normalizedVirtualPrefix_succ, ih,
      normalizedAttention_change_coordinates, valuePrefix_succ]
    rfl

/-- The paper's variable-width normalized deep network depends only on the
virtual weights `(M,L)`, with all canonical layers living in input width `d₀`.
This justifies the dimensions and placement of `L` in `realizeDeep`. -/
theorem deepNormalizedAttention_eq_virtual {l t : ℕ}
    {dim : Fin (l + 1) → ℕ} (S : ℝ → ℝ) (W : DeepAttentionWeights l dim)
    (X : Matrix (Fin (dim 0)) (Fin t) ℝ) :
    deepNormalizedAttention S W X =
      virtualL W * normalizedVirtualPrefix S W X (Fin.last l) :=
  deepNormalizedPrefix_eq_virtual S W X (Fin.last l)

end NormalizedDeepAttention
