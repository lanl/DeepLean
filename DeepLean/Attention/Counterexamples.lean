module

public import DeepLean.Attention.Basic

/-!
# Exact exceptional fibers of normalized deep attention

These results separate genuine boundary phenomena from the paper's unresolved generic claim.
The main construction shows that two-token exponential attention collapses after a
skew-symmetric first score matrix, so every later virtual score matrix is invisible.
-/

@[expose] public section

namespace NormalizedDeepAttention

/-- The elementary bilinear identity for a skew-symmetric score matrix. -/
theorem skew_bilinear_swap {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.transpose = -M) (x y : Fin d → ℝ) :
    dotProduct x (M.mulVec y) = -dotProduct y (M.mulVec x) := by
  calc
    dotProduct x (M.mulVec y) = dotProduct y (M.transpose.mulVec x) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
    _ = dotProduct y ((-M).mulVec x) := by rw [hM]
    _ = -dotProduct y (M.mulVec x) := by
      rw [Matrix.neg_mulVec, dotProduct_neg]

theorem skew_quadratic_zero {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.transpose = -M) (x : Fin d → ℝ) :
    dotProduct x (M.mulVec x) = 0 := by
  have h := skew_bilinear_swap M hM x x
  linarith

/-- With two tokens and exponential softmax, a skew-symmetric score matrix gives the
same output at both query positions. -/
theorem layer_exp_skew_two_columns_eq {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.transpose = -M)
    (X : Matrix (Fin d) (Fin 2) ℝ) (r : Fin d) :
    layer Real.exp M X r 0 = layer Real.exp M X r 1 := by
  let x := X.col (0 : Fin 2)
  let y := X.col (1 : Fin 2)
  let a := dotProduct x (M.mulVec y)
  have hxx : dotProduct x (M.mulVec x) = 0 := skew_quadratic_zero M hM x
  have hyy : dotProduct y (M.mulVec y) = 0 := skew_quadratic_zero M hM y
  have hyx : dotProduct y (M.mulVec x) = -a := by
    simpa [a] using skew_bilinear_swap M hM y x
  change
    (∑ j : Fin 2, Real.exp (attentionScore M X 0 j) *
        ((1 : Matrix (Fin d) (Fin d) ℝ).mulVec (X.col j)) r) /
      ∑ k : Fin 2, Real.exp (attentionScore M X 0 k) =
    (∑ j : Fin 2, Real.exp (attentionScore M X 1 j) *
        ((1 : Matrix (Fin d) (Fin d) ℝ).mulVec (X.col j)) r) /
      ∑ k : Fin 2, Real.exp (attentionScore M X 1 k)
  simp only [Fin.sum_univ_two, Matrix.one_mulVec, attentionScore]
  change
    (Real.exp (dotProduct x (M.mulVec x)) * x r +
        Real.exp (dotProduct x (M.mulVec y)) * y r) /
        (Real.exp (dotProduct x (M.mulVec x)) +
          Real.exp (dotProduct x (M.mulVec y))) =
      (Real.exp (dotProduct y (M.mulVec x)) * x r +
        Real.exp (dotProduct y (M.mulVec y)) * y r) /
        (Real.exp (dotProduct y (M.mulVec x)) +
          Real.exp (dotProduct y (M.mulVec y)))
  rw [hxx, hyy, hyx, Real.exp_zero, Real.exp_neg]
  have he : Real.exp a ≠ 0 := Real.exp_ne_zero a
  field_simp [he]
  ring

/-- The preceding equality is exactly collapse to a repeated-token sequence. -/
theorem layer_exp_skew_two_eq_constant {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.transpose = -M)
    (X : Matrix (Fin d) (Fin 2) ℝ) :
    layer Real.exp M X =
      constantTokenMatrix (t := 2) ((layer Real.exp M X).col 0) := by
  ext r i
  fin_cases i
  · rfl
  · change layer Real.exp M X r 1 = layer Real.exp M X r 0
    exact (layer_exp_skew_two_columns_eq M hM X r).symm

/-- Once the first two-token exponential layer has a skew score matrix, the second
virtual score matrix is completely invisible. -/
theorem realizeTwo_exp_skew_first_independent_second {d dOut : ℕ}
    (M₁ M₂ M₂' : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin dOut) (Fin d) ℝ) (hM₁ : M₁.transpose = -M₁) :
    realizeTwo (t := 2) Real.exp ⟨M₁, M₂, L⟩ =
      realizeTwo Real.exp ⟨M₁, M₂', L⟩ := by
  funext X
  rw [realizeTwo, realizeTwo, layer_exp_skew_two_eq_constant M₁ hM₁ X,
    layer_constantTokenMatrix Real.exp Real.exp_pos M₂ _ (by omega),
    layer_constantTokenMatrix Real.exp Real.exp_pos M₂' _ (by omega)]

/-- A concrete full-rank skew matrix in dimension two. -/
def skewPlane : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

theorem skewPlane_transpose : skewPlane.transpose = -skewPlane := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [skewPlane]

theorem skewPlane_rank : skewPlane.rank = 2 := by
  apply le_antisymm
  · exact skewPlane.rank_le_height
  · calc
      2 = (1 : Matrix (Fin 2) (Fin 2) ℝ).rank := by simp
      _ = (skewPlane * (-skewPlane)).rank := by
        congr 1
        ext i j
        fin_cases i <;> fin_cases j <;> norm_num [skewPlane, Matrix.mul_apply]
      _ ≤ skewPlane.rank := Matrix.rank_mul_le_left _ _

def explicitSource : TwoLayerWeights 2 2 := ⟨skewPlane, 1, 1⟩
def explicitPartner : TwoLayerWeights 2 2 := ⟨skewPlane, (2 : ℝ) • 1, 1⟩

theorem explicitSource_ne_partner : explicitSource ≠ explicitPartner := by
  intro h
  have hM := congrArg TwoLayerWeights.M₂ h
  have he := congrFun (congrFun hM (0 : Fin 2)) (0 : Fin 2)
  norm_num [explicitSource, explicitPartner] at he

/-- Kernel-checked non-singleton virtual-weight fiber at `t=2`, with nonzero `L` and
full-rank first score matrix.  This is exceptional (the first matrix is skew), so it does
not by itself refute the intended generic `t=3` conjecture. -/
theorem explicit_two_token_nontrivial_fiber :
    explicitSource ≠ explicitPartner ∧
      realizeTwo (t := 2) Real.exp explicitSource =
        realizeTwo Real.exp explicitPartner := by
  exact ⟨explicitSource_ne_partner,
    realizeTwo_exp_skew_first_independent_second skewPlane 1 ((2 : ℝ) • 1) 1
      skewPlane_transpose⟩

end NormalizedDeepAttention
