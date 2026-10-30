module

public import DeepLean.Attention.Basic

/-! # Exact two-token formulas for exponential normalized attention -/

@[expose] public section

namespace NormalizedDeepAttention

/-- For two tokens, exponential attention is a logistic interpolation between the two
value vectors. -/
theorem layer_exp_two_formula {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin 2) ℝ) (r : Fin d) (i : Fin 2) :
    layer Real.exp M X r i =
      X r 1 + Real.sigmoid
        (attentionScore M X i 0 - attentionScore M X i 1) * (X r 0 - X r 1) := by
  change
    (∑ j : Fin 2, Real.exp (attentionScore M X i j) *
        ((1 : Matrix (Fin d) (Fin d) ℝ).mulVec (X.col j)) r) /
      ∑ k : Fin 2, Real.exp (attentionScore M X i k) = _
  simp only [Fin.sum_univ_two, Matrix.one_mulVec]
  let a := attentionScore M X i 0
  let b := attentionScore M X i 1
  change (Real.exp a * X r 0 + Real.exp b * X r 1) /
      (Real.exp a + Real.exp b) =
    X r 1 + Real.sigmoid (a - b) * (X r 0 - X r 1)
  have hea : Real.exp a ≠ 0 := Real.exp_ne_zero a
  have heb : Real.exp b ≠ 0 := Real.exp_ne_zero b
  have hab : Real.exp a + Real.exp b ≠ 0 := by positivity
  rw [Real.sigmoid, neg_sub, Real.exp_sub]
  field_simp [hea, heb, hab]
  ring

/-- The symmetric perturbation of a repeated two-token sequence used for the quadratic
jet at that sequence. -/
def symmetricPerturbation {d : ℕ} (x u : Fin d → ℝ) (ε : ℝ) :
    Matrix (Fin d) (Fin 2) ℝ :=
  fun r i ↦ Fin.cases (x r + ε * u r) (fun _ ↦ x r - ε * u r) i

@[simp] theorem symmetricPerturbation_col_zero {d : ℕ}
    (x u : Fin d → ℝ) (ε : ℝ) :
    (symmetricPerturbation x u ε).col 0 = x + ε • u := by
  ext r
  simp [symmetricPerturbation]

@[simp] theorem symmetricPerturbation_col_one {d : ℕ}
    (x u : Fin d → ℝ) (ε : ℝ) :
    (symmetricPerturbation x u ε).col 1 = x - ε • u := by
  ext r
  have h : (1 : Fin 2) = (0 : Fin 1).succ := by decide
  rw [show (symmetricPerturbation x u ε).col 1 r =
      symmetricPerturbation x u ε r 1 by rfl, h]
  rfl

theorem symmetricPerturbation_scoreDifference_zero {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (x u : Fin d → ℝ) (ε : ℝ) :
    attentionScore M (symmetricPerturbation x u ε) 0 0 -
        attentionScore M (symmetricPerturbation x u ε) 0 1 =
      2 * ε * (dotProduct x (M.mulVec u) +
        ε * dotProduct u (M.mulVec u)) := by
  simp only [attentionScore, symmetricPerturbation_col_zero,
    symmetricPerturbation_col_one, Matrix.mulVec_add, Matrix.mulVec_sub,
    Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    dotProduct_sub, dotProduct_smul, smul_dotProduct]
  ring

theorem symmetricPerturbation_scoreDifference_one {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (x u : Fin d → ℝ) (ε : ℝ) :
    attentionScore M (symmetricPerturbation x u ε) 1 0 -
        attentionScore M (symmetricPerturbation x u ε) 1 1 =
      2 * ε * (dotProduct x (M.mulVec u) -
        ε * dotProduct u (M.mulVec u)) := by
  simp only [attentionScore, symmetricPerturbation_col_zero,
    symmetricPerturbation_col_one, Matrix.mulVec_add, Matrix.mulVec_sub,
    Matrix.mulVec_smul, sub_dotProduct, dotProduct_add,
    dotProduct_sub, dotProduct_smul, smul_dotProduct]
  ring

/-- The scalar logistic factor in a symmetric repeated-token perturbation has the
expected first-order coefficient.  The quadratic term may have either sign. -/
theorem tendsto_two_sigmoid_quadratic_slope (a b : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (2 * Real.sigmoid (2 * ε * (a + ε * b)) - 1) / ε)
      (nhdsWithin 0 {0}ᶜ) (nhds a) := by
  let q : ℝ → ℝ := fun ε ↦ 2 * ε * (a + ε * b)
  have hq : Filter.Tendsto q (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have hc : ContinuousAt q 0 := by
      dsimp [q]
      fun_prop
    simpa [q] using hc.tendsto.mono_left
      (show nhdsWithin (0 : ℝ) ({0}ᶜ) ≤ nhds 0 from nhdsWithin_le_nhds)
  have hdiff : DifferentiableAt ℝ Real.sigmoid 0 :=
    (Real.hasDerivAt_sigmoid 0).differentiableAt
  have hds : Filter.Tendsto (dslope Real.sigmoid 0 ∘ q)
      (nhdsWithin 0 {0}ᶜ) (nhds (1 / 4 : ℝ)) := by
    have hc : ContinuousAt (dslope Real.sigmoid 0) 0 :=
      continuousAt_dslope_same.mpr hdiff
    have hv : dslope Real.sigmoid 0 0 = (1 / 4 : ℝ) := by
      rw [dslope_same, (Real.hasDerivAt_sigmoid 0).deriv]
      norm_num [Real.sigmoid_zero]
    rw [← hv]
    exact hc.tendsto.comp hq
  have hquot : Filter.Tendsto (fun ε : ℝ => q ε / ε)
      (nhdsWithin 0 {0}ᶜ) (nhds (2 * a)) := by
    have heq : (fun ε : ℝ => q ε / ε) =ᶠ[nhdsWithin 0 {0}ᶜ]
        fun ε ↦ 2 * (a + ε * b) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : ε ≠ 0 := hε
      simp only [q]
      field_simp [hε0]
    have hrhs : Filter.Tendsto (fun ε : ℝ ↦ 2 * (a + ε * b))
        (nhdsWithin 0 {0}ᶜ) (nhds (2 * a)) := by
      have hc : ContinuousAt (fun ε : ℝ ↦ 2 * (a + ε * b)) 0 := by
        fun_prop
      simpa using hc.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) ({0}ᶜ) ≤ nhds 0 from nhdsWithin_le_nhds)
    exact hrhs.congr' heq.symm
  have hconst : Filter.Tendsto (fun _ : ℝ ↦ (2 : ℝ))
      (nhdsWithin 0 {0}ᶜ) (nhds 2) := tendsto_const_nhds
  have hprod : Filter.Tendsto
      (fun ε ↦ 2 * (dslope Real.sigmoid 0 (q ε)) * (q ε / ε))
      (nhdsWithin 0 {0}ᶜ) (nhds (2 * (1 / 4 : ℝ) * (2 * a))) := by
    simpa [Function.comp_def] using (hconst.mul hds).mul hquot
  have heq : (fun ε : ℝ =>
      (2 * Real.sigmoid (2 * ε * (a + ε * b)) - 1) / ε) =ᶠ[
        nhdsWithin 0 {0}ᶜ]
      fun ε ↦ 2 * (dslope Real.sigmoid 0 (q ε)) * (q ε / ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : ε ≠ 0 := hε
    have hs := sub_smul_dslope Real.sigmoid 0 (q ε)
    have hs' : q ε * dslope Real.sigmoid 0 (q ε) =
        Real.sigmoid (q ε) - Real.sigmoid 0 := by
      simpa only [sub_zero, smul_eq_mul] using hs
    rw [Real.sigmoid_zero] at hs'
    dsimp [q]
    field_simp [hε0]
    nlinarith [hs']
  have hright : Filter.Tendsto
      (fun ε ↦ 2 * (dslope Real.sigmoid 0 (q ε)) * (q ε / ε))
      (nhdsWithin 0 {0}ᶜ) (nhds a) := by
    have ha : 2 * (1 / 4 : ℝ) * (2 * a) = a := by ring
    rw [ha] at hprod
    exact hprod
  apply Filter.Tendsto.congr' heq.symm
  exact hright

/-- Both output tokens have the same quadratic jet at a repeated-token input.  This is
the first virtual-score observable in a deep normalized network. -/
theorem layer_exp_symmetricPerturbation_quadraticJet {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (x u : Fin d → ℝ)
    (r : Fin d) (i : Fin 2) :
    Filter.Tendsto
      (fun ε : ℝ =>
        (layer Real.exp M (symmetricPerturbation x u ε) r i - x r) / ε ^ 2)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (dotProduct x (M.mulVec u) * u r)) := by
  let a := dotProduct x (M.mulVec u)
  let b := dotProduct u (M.mulVec u)
  fin_cases i
  · have hs := (tendsto_two_sigmoid_quadratic_slope a b).mul_const (u r)
    have heq : (fun ε : ℝ =>
        (layer Real.exp M (symmetricPerturbation x u ε) r 0 - x r) / ε ^ 2) =ᶠ[
          nhdsWithin 0 {0}ᶜ]
        fun ε ↦ ((2 * Real.sigmoid (2 * ε * (a + ε * b)) - 1) / ε) * u r := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : ε ≠ 0 := hε
      rw [layer_exp_two_formula, symmetricPerturbation_scoreDifference_zero]
      simp only [symmetricPerturbation]
      change
        (x r - ε * u r + Real.sigmoid (2 * ε * (a + ε * b)) *
          (x r + ε * u r - (x r - ε * u r)) - x r) / ε ^ 2 = _
      field_simp [hε0]
      ring
    apply Filter.Tendsto.congr' heq.symm
    simpa [a] using hs
  · have hs := (tendsto_two_sigmoid_quadratic_slope a (-b)).mul_const (u r)
    have heq : (fun ε : ℝ =>
        (layer Real.exp M (symmetricPerturbation x u ε) r 1 - x r) / ε ^ 2) =ᶠ[
          nhdsWithin 0 {0}ᶜ]
        fun ε ↦ ((2 * Real.sigmoid (2 * ε * (a + ε * (-b))) - 1) / ε) * u r := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : ε ≠ 0 := hε
      rw [layer_exp_two_formula, symmetricPerturbation_scoreDifference_one]
      simp only [symmetricPerturbation]
      change
        (x r - ε * u r + Real.sigmoid (2 * ε * (a - ε * b)) *
          (x r + ε * u r - (x r - ε * u r)) - x r) / ε ^ 2 = _
      field_simp [hε0]
      ring
    apply Filter.Tendsto.congr' heq.symm
    simpa [a] using hs

/-- Any further exponential two-token layer preserves a common quadratic jet.  Its own
score matrix first contributes at strictly higher order. -/
theorem layer_exp_preserves_common_quadraticJet {d : ℕ}
    (N : Matrix (Fin d) (Fin d) ℝ)
    (Y : ℝ → Matrix (Fin d) (Fin 2) ℝ) (x v : Fin d → ℝ)
    (hY : ∀ (r : Fin d) (i : Fin 2),
      Filter.Tendsto (fun ε ↦ Y ε r i) (nhdsWithin 0 {0}ᶜ) (nhds (x r)))
    (hjet : ∀ (r : Fin d) (i : Fin 2),
      Filter.Tendsto (fun ε ↦ (Y ε r i - x r) / ε ^ 2)
        (nhdsWithin 0 {0}ᶜ) (nhds (v r)))
    (r : Fin d) (i : Fin 2) :
    Filter.Tendsto
      (fun ε ↦ (layer Real.exp N (Y ε) r i - x r) / ε ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (v r)) := by
  let F := nhdsWithin (0 : ℝ) ({0}ᶜ)
  have hscore (p q : Fin 2) :
      Filter.Tendsto (fun ε ↦ attentionScore N (Y ε) p q) F
        (nhds (dotProduct x (N.mulVec x))) := by
    have hmul (k : Fin d) :
        Filter.Tendsto (fun ε ↦ (N.mulVec ((Y ε).col q)) k) F
          (nhds ((N.mulVec x) k)) := by
      simp only [Matrix.mulVec, dotProduct]
      apply tendsto_finsetSum Finset.univ
      intro j _
      exact tendsto_const_nhds.mul (hY j q)
    simp only [attentionScore, dotProduct]
    apply tendsto_finsetSum Finset.univ
    intro k _
    exact (hY k p).mul (hmul k)
  have hweight : Filter.Tendsto
      (fun ε ↦ Real.sigmoid
        (attentionScore N (Y ε) i 0 - attentionScore N (Y ε) i 1)) F
      (nhds (1 / 2 : ℝ)) := by
    have hd := (hscore i 0).sub (hscore i 1)
    have hd0 : Filter.Tendsto
        (fun ε ↦ attentionScore N (Y ε) i 0 - attentionScore N (Y ε) i 1) F
        (nhds 0) := by simpa using hd
    have hs := (Real.hasDerivAt_sigmoid 0).continuousAt.tendsto.comp hd0
    simpa [Function.comp_def, Real.sigmoid_zero] using hs
  have hdiff : Filter.Tendsto
      (fun ε ↦ (Y ε r 0 - x r) / ε ^ 2 - (Y ε r 1 - x r) / ε ^ 2) F
      (nhds 0) := by
    simpa using (hjet r 0).sub (hjet r 1)
  have hrhs := (hjet r 1).add (hweight.mul hdiff)
  have heq : (fun ε ↦ (layer Real.exp N (Y ε) r i - x r) / ε ^ 2) =ᶠ[F]
      fun ε ↦ (Y ε r 1 - x r) / ε ^ 2 +
        Real.sigmoid
          (attentionScore N (Y ε) i 0 - attentionScore N (Y ε) i 1) *
            ((Y ε r 0 - x r) / ε ^ 2 - (Y ε r 1 - x r) / ε ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : ε ≠ 0 := hε
    rw [layer_exp_two_formula]
    field_simp [hε0]
    ring
  apply Filter.Tendsto.congr' heq.symm
  simpa using hrhs

end NormalizedDeepAttention
