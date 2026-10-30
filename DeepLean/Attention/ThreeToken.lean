module

public import DeepLean.Attention.TwoLayer

/-! # Three-token repeated-pattern reduction -/

@[expose] public section

namespace NormalizedDeepAttention

/-- Probability assigned to the singleton key when the other key is repeated twice. -/
noncomputable def weightedLogistic (z : ℝ) : ℝ := Real.exp z / (Real.exp z + 2)

def triplePattern {d : ℕ} (x y : Fin d → ℝ) : Matrix (Fin d) (Fin 3) ℝ :=
  firstAndRepeatedTokenMatrix (n := 2) x y

@[simp] theorem triplePattern_col_zero {d : ℕ} (x y : Fin d → ℝ) :
    (triplePattern x y).col 0 = x := by rfl

@[simp] theorem triplePattern_col_one {d : ℕ} (x y : Fin d → ℝ) :
    (triplePattern x y).col 1 = y := by
  ext r
  have h : (1 : Fin 3) = (0 : Fin 2).succ := by decide
  rw [show (triplePattern x y).col 1 r = triplePattern x y r 1 by rfl, h]
  rfl

@[simp] theorem triplePattern_col_two {d : ℕ} (x y : Fin d → ℝ) :
    (triplePattern x y).col 2 = y := by
  ext r
  have h : (2 : Fin 3) = (1 : Fin 2).succ := by decide
  rw [show (triplePattern x y).col 2 r = triplePattern x y r 2 by rfl, h]
  rfl

theorem layer_exp_triplePattern_formula {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℝ)
    (r : Fin d) (i : Fin 3) :
    layer Real.exp M (triplePattern x y) r i =
      y r + weightedLogistic
        (attentionScore M (triplePattern x y) i 0 -
          attentionScore M (triplePattern x y) i 1) * (x r - y r) := by
  change
    (∑ j : Fin 3, Real.exp (attentionScore M (triplePattern x y) i j) *
        ((1 : Matrix (Fin d) (Fin d) ℝ).mulVec ((triplePattern x y).col j)) r) /
      ∑ k : Fin 3, Real.exp (attentionScore M (triplePattern x y) i k) = _
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [Matrix.one_mulVec]
  change
    (Real.exp (attentionScore M (triplePattern x y) i 0) * x r +
      Real.exp (attentionScore M (triplePattern x y) i 1) * y r +
      Real.exp (attentionScore M (triplePattern x y) i 2) * y r) /
        (Real.exp (attentionScore M (triplePattern x y) i 0) +
          Real.exp (attentionScore M (triplePattern x y) i 1) +
          Real.exp (attentionScore M (triplePattern x y) i 2)) = _
  have hs12 : attentionScore M (triplePattern x y) i 2 =
      attentionScore M (triplePattern x y) i 1 := by
    rw [attentionScore, attentionScore, triplePattern_col_two, triplePattern_col_one]
  rw [hs12]
  let a := attentionScore M (triplePattern x y) i 0
  let b := attentionScore M (triplePattern x y) i 1
  change (Real.exp a * x r + Real.exp b * y r + Real.exp b * y r) /
      (Real.exp a + Real.exp b + Real.exp b) =
    y r + weightedLogistic (a - b) * (x r - y r)
  rw [show Real.exp a * x r + Real.exp b * y r + Real.exp b * y r =
      Real.exp a * x r + 2 * (Real.exp b * y r) by ring,
    show Real.exp a + Real.exp b + Real.exp b =
      Real.exp a + 2 * Real.exp b by ring]
  have hea : Real.exp a ≠ 0 := Real.exp_ne_zero a
  have heb : Real.exp b ≠ 0 := Real.exp_ne_zero b
  have hab : Real.exp a + 2 * Real.exp b ≠ 0 := by positivity
  rw [weightedLogistic, Real.exp_sub]
  field_simp [hea, heb, hab]
  ring

theorem layer_exp_triplePattern_is_triplePattern {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℝ) :
    ∃ x' y', layer Real.exp M (triplePattern x y) = triplePattern x' y' := by
  let x' := (layer Real.exp M (triplePattern x y)).col 0
  let y' := (layer Real.exp M (triplePattern x y)).col 1
  refine ⟨x', y', ?_⟩
  ext r i
  fin_cases i
  · rfl
  · rfl
  · change layer Real.exp M (triplePattern x y) r 2 =
      layer Real.exp M (triplePattern x y) r 1
    rw [layer_exp_triplePattern_formula, layer_exp_triplePattern_formula]
    congr 2

theorem tendsto_weightedLogistic_quadratic_slope (a b : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ ↦
        (3 * weightedLogistic (3 * ε * (a + ε * b)) - 1) / ε)
      (nhdsWithin 0 {0}ᶜ) (nhds (2 * a)) := by
  let q : ℝ → ℝ := fun ε ↦ 3 * ε * (a + ε * b)
  have hq : Filter.Tendsto q (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have hc : ContinuousAt q 0 := by
      dsimp [q]
      fun_prop
    simpa [q] using hc.tendsto.mono_left
      (show nhdsWithin (0 : ℝ) ({0}ᶜ) ≤ nhds 0 from nhdsWithin_le_nhds)
  have hds : Filter.Tendsto (dslope Real.exp 0 ∘ q)
      (nhdsWithin 0 {0}ᶜ) (nhds (1 : ℝ)) := by
    have hc : ContinuousAt (dslope Real.exp 0) 0 :=
      continuousAt_dslope_same.mpr (Real.hasDerivAt_exp 0).differentiableAt
    have hv : dslope Real.exp 0 0 = (1 : ℝ) := by
      rw [dslope_same, (Real.hasDerivAt_exp 0).deriv, Real.exp_zero]
    rw [← hv]
    exact hc.tendsto.comp hq
  have hquot : Filter.Tendsto (fun ε : ℝ ↦ q ε / ε)
      (nhdsWithin 0 {0}ᶜ) (nhds (3 * a)) := by
    have heq : (fun ε : ℝ ↦ q ε / ε) =ᶠ[nhdsWithin 0 {0}ᶜ]
        fun ε ↦ 3 * (a + ε * b) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : ε ≠ 0 := hε
      simp only [q]
      field_simp [hε0]
    have hc : ContinuousAt (fun ε : ℝ ↦ 3 * (a + ε * b)) 0 := by fun_prop
    have ht : Filter.Tendsto (fun ε : ℝ ↦ 3 * (a + ε * b))
        (nhdsWithin 0 {0}ᶜ) (nhds (3 * a)) := by
      simpa using hc.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) ({0}ᶜ) ≤ nhds 0 from nhdsWithin_le_nhds)
    exact ht.congr' heq.symm
  have hden : Filter.Tendsto (fun ε ↦ Real.exp (q ε) + 2)
      (nhdsWithin 0 {0}ᶜ) (nhds 3) := by
    have he := (Real.hasDerivAt_exp 0).continuousAt.tendsto.comp hq
    convert he.add_const 2 using 1 <;> norm_num
  have hnum : Filter.Tendsto
      (fun ε ↦ 2 * dslope Real.exp 0 (q ε) * (q ε / ε))
      (nhdsWithin 0 {0}ᶜ) (nhds (6 * a)) := by
    have hc : Filter.Tendsto (fun _ : ℝ ↦ (2 : ℝ))
        (nhdsWithin 0 {0}ᶜ) (nhds 2) := tendsto_const_nhds
    have hp := (hc.mul hds).mul hquot
    convert hp using 1
    · funext ε
      dsimp
    · congr 1
      ring
  have hratio := hnum.div hden (by norm_num : (3 : ℝ) ≠ 0)
  have heq : (fun ε : ℝ ↦
      (3 * weightedLogistic (3 * ε * (a + ε * b)) - 1) / ε) =ᶠ[
        nhdsWithin 0 {0}ᶜ]
      fun ε ↦ 2 * dslope Real.exp 0 (q ε) * (q ε / ε) /
        (Real.exp (q ε) + 2) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : ε ≠ 0 := hε
    have hs := sub_smul_dslope Real.exp 0 (q ε)
    have hs' : q ε * dslope Real.exp 0 (q ε) = Real.exp (q ε) - 1 := by
      simpa only [sub_zero, smul_eq_mul, Real.exp_zero] using hs
    dsimp [q, weightedLogistic]
    field_simp [hε0, Real.exp_ne_zero]
    nlinarith [hs']
  apply Filter.Tendsto.congr' heq.symm
  convert hratio using 1 <;> congr 1 <;> ring

/-- A centered singleton-plus-repeated perturbation.  Its token average is `x`. -/
def tripleCenteredPerturbation {d : ℕ} (x u : Fin d → ℝ) (ε : ℝ) :
    Matrix (Fin d) (Fin 3) ℝ :=
  triplePattern (x + (2 * ε) • u) (x - ε • u)

@[simp] theorem tripleCenteredPerturbation_col_zero {d : ℕ}
    (x u : Fin d → ℝ) (ε : ℝ) :
    (tripleCenteredPerturbation x u ε).col 0 = x + (2 * ε) • u := by
  rfl

@[simp] theorem tripleCenteredPerturbation_col_one {d : ℕ}
    (x u : Fin d → ℝ) (ε : ℝ) :
    (tripleCenteredPerturbation x u ε).col 1 = x - ε • u := by
  exact triplePattern_col_one _ _

@[simp] theorem tripleCenteredPerturbation_col_two {d : ℕ}
    (x u : Fin d → ℝ) (ε : ℝ) :
    (tripleCenteredPerturbation x u ε).col 2 = x - ε • u := by
  exact triplePattern_col_two _ _

theorem tripleCenteredPerturbation_scoreDifference_zero {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (x u : Fin d → ℝ) (ε : ℝ) :
    attentionScore M (tripleCenteredPerturbation x u ε) 0 0 -
        attentionScore M (tripleCenteredPerturbation x u ε) 0 1 =
      3 * ε * (dotProduct x (M.mulVec u) +
        2 * ε * dotProduct u (M.mulVec u)) := by
  simp only [attentionScore, tripleCenteredPerturbation_col_zero,
    tripleCenteredPerturbation_col_one, Matrix.mulVec_add, Matrix.mulVec_sub,
    Matrix.mulVec_smul, add_dotProduct, dotProduct_add, dotProduct_sub,
    dotProduct_smul, smul_dotProduct]
  ring

theorem tripleCenteredPerturbation_scoreDifference_one {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (x u : Fin d → ℝ) (ε : ℝ) :
    attentionScore M (tripleCenteredPerturbation x u ε) 1 0 -
        attentionScore M (tripleCenteredPerturbation x u ε) 1 1 =
      3 * ε * (dotProduct x (M.mulVec u) -
        ε * dotProduct u (M.mulVec u)) := by
  simp only [attentionScore, tripleCenteredPerturbation_col_zero,
    tripleCenteredPerturbation_col_one, Matrix.mulVec_add, Matrix.mulVec_sub,
    Matrix.mulVec_smul, sub_dotProduct, dotProduct_add, dotProduct_sub,
    dotProduct_smul, smul_dotProduct]
  ring

theorem tripleCenteredPerturbation_scoreDifference_two {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (x u : Fin d → ℝ) (ε : ℝ) :
    attentionScore M (tripleCenteredPerturbation x u ε) 2 0 -
        attentionScore M (tripleCenteredPerturbation x u ε) 2 1 =
      3 * ε * (dotProduct x (M.mulVec u) -
        ε * dotProduct u (M.mulVec u)) := by
  rw [show attentionScore M (tripleCenteredPerturbation x u ε) 2 0 =
      attentionScore M (tripleCenteredPerturbation x u ε) 1 0 by
        simp [attentionScore],
    show attentionScore M (tripleCenteredPerturbation x u ε) 2 1 =
      attentionScore M (tripleCenteredPerturbation x u ε) 1 1 by
        simp [attentionScore]]
  exact tripleCenteredPerturbation_scoreDifference_one M x u ε

/-- All three outputs have the same quadratic jet at a repeated three-token input. -/
theorem layer_exp_tripleCenteredPerturbation_quadraticJet {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (x u : Fin d → ℝ)
    (r : Fin d) (i : Fin 3) :
    Filter.Tendsto
      (fun ε : ℝ ↦
        (layer Real.exp M (tripleCenteredPerturbation x u ε) r i - x r) / ε ^ 2)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (2 * dotProduct x (M.mulVec u) * u r)) := by
  let a := dotProduct x (M.mulVec u)
  let b := dotProduct u (M.mulVec u)
  fin_cases i
  · have hs := (tendsto_weightedLogistic_quadratic_slope a (2 * b)).mul_const (u r)
    have heq : (fun ε : ℝ ↦
        (layer Real.exp M (tripleCenteredPerturbation x u ε) r 0 - x r) / ε ^ 2) =ᶠ[
          nhdsWithin 0 {0}ᶜ]
        fun ε ↦ ((3 * weightedLogistic (3 * ε * (a + ε * (2 * b))) - 1) / ε) *
          u r := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : ε ≠ 0 := hε
      change
        (layer Real.exp M
          (triplePattern (x + (2 * ε) • u) (x - ε • u)) r 0 - x r) / ε ^ 2 = _
      rw [layer_exp_triplePattern_formula,
        show attentionScore M (triplePattern (x + (2 * ε) • u) (x - ε • u)) 0 0 -
            attentionScore M (triplePattern (x + (2 * ε) • u) (x - ε • u)) 0 1 =
            3 * ε * (dotProduct x (M.mulVec u) +
              2 * ε * dotProduct u (M.mulVec u)) by
          exact tripleCenteredPerturbation_scoreDifference_zero M x u ε]
      change
        (x r - ε * u r + weightedLogistic (3 * ε * (a + 2 * ε * b)) *
          (x r + 2 * ε * u r - (x r - ε * u r)) - x r) / ε ^ 2 = _
      field_simp [hε0]
      ring
    apply Filter.Tendsto.congr' heq.symm
    simpa [a] using hs
  · have hs := (tendsto_weightedLogistic_quadratic_slope a (-b)).mul_const (u r)
    have heq : (fun ε : ℝ ↦
        (layer Real.exp M (tripleCenteredPerturbation x u ε) r 1 - x r) / ε ^ 2) =ᶠ[
          nhdsWithin 0 {0}ᶜ]
        fun ε ↦ ((3 * weightedLogistic (3 * ε * (a + ε * (-b))) - 1) / ε) *
          u r := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : ε ≠ 0 := hε
      change
        (layer Real.exp M
          (triplePattern (x + (2 * ε) • u) (x - ε • u)) r 1 - x r) / ε ^ 2 = _
      rw [layer_exp_triplePattern_formula,
        show attentionScore M (triplePattern (x + (2 * ε) • u) (x - ε • u)) 1 0 -
            attentionScore M (triplePattern (x + (2 * ε) • u) (x - ε • u)) 1 1 =
            3 * ε * (dotProduct x (M.mulVec u) -
              ε * dotProduct u (M.mulVec u)) by
          exact tripleCenteredPerturbation_scoreDifference_one M x u ε]
      change
        (x r - ε * u r + weightedLogistic (3 * ε * (a - ε * b)) *
          (x r + 2 * ε * u r - (x r - ε * u r)) - x r) / ε ^ 2 = _
      field_simp [hε0]
      ring
    apply Filter.Tendsto.congr' heq.symm
    simpa [a] using hs
  · have hs := (tendsto_weightedLogistic_quadratic_slope a (-b)).mul_const (u r)
    have heq : (fun ε : ℝ ↦
        (layer Real.exp M (tripleCenteredPerturbation x u ε) r 2 - x r) / ε ^ 2) =ᶠ[
          nhdsWithin 0 {0}ᶜ]
        fun ε ↦ ((3 * weightedLogistic (3 * ε * (a + ε * (-b))) - 1) / ε) *
          u r := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : ε ≠ 0 := hε
      change
        (layer Real.exp M
          (triplePattern (x + (2 * ε) • u) (x - ε • u)) r 2 - x r) / ε ^ 2 = _
      rw [layer_exp_triplePattern_formula,
        show attentionScore M (triplePattern (x + (2 * ε) • u) (x - ε • u)) 2 0 -
            attentionScore M (triplePattern (x + (2 * ε) • u) (x - ε • u)) 2 1 =
            3 * ε * (dotProduct x (M.mulVec u) -
              ε * dotProduct u (M.mulVec u)) by
          exact tripleCenteredPerturbation_scoreDifference_two M x u ε]
      change
        (x r - ε * u r + weightedLogistic (3 * ε * (a - ε * b)) *
          (x r + 2 * ε * u r - (x r - ε * u r)) - x r) / ε ^ 2 = _
      field_simp [hε0]
      ring
    apply Filter.Tendsto.congr' heq.symm
    simpa [a] using hs

/-- A further exponential layer preserves a common quadratic jet on the
singleton-plus-repeated subspace. -/
theorem layer_exp_preserves_triple_common_quadraticJet {d : ℕ}
    (N : Matrix (Fin d) (Fin d) ℝ)
    (Y : ℝ → Matrix (Fin d) (Fin 3) ℝ) (x v : Fin d → ℝ)
    (hpattern : ∀ ε, ∃ y₀ y₁, Y ε = triplePattern y₀ y₁)
    (hY : ∀ (r : Fin d) (i : Fin 3),
      Filter.Tendsto (fun ε ↦ Y ε r i) (nhdsWithin 0 {0}ᶜ) (nhds (x r)))
    (hjet : ∀ (r : Fin d) (i : Fin 3),
      Filter.Tendsto (fun ε ↦ (Y ε r i - x r) / ε ^ 2)
        (nhdsWithin 0 {0}ᶜ) (nhds (v r)))
    (r : Fin d) (i : Fin 3) :
    Filter.Tendsto
      (fun ε ↦ (layer Real.exp N (Y ε) r i - x r) / ε ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (v r)) := by
  let F := nhdsWithin (0 : ℝ) ({0}ᶜ)
  have hscore (p q : Fin 3) :
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
      (fun ε ↦ weightedLogistic
        (attentionScore N (Y ε) i 0 - attentionScore N (Y ε) i 1)) F
      (nhds (1 / 3 : ℝ)) := by
    have hd := (hscore i 0).sub (hscore i 1)
    have hd0 : Filter.Tendsto
        (fun ε ↦ attentionScore N (Y ε) i 0 - attentionScore N (Y ε) i 1) F
        (nhds 0) := by simpa using hd
    have hc : ContinuousAt weightedLogistic 0 := by
      unfold weightedLogistic
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · norm_num
    have hw := hc.tendsto.comp hd0
    convert hw using 1
    · rfl
    · norm_num [weightedLogistic]
  have hdiff : Filter.Tendsto
      (fun ε ↦ (Y ε r 0 - x r) / ε ^ 2 - (Y ε r 1 - x r) / ε ^ 2) F
      (nhds 0) := by
    simpa using (hjet r 0).sub (hjet r 1)
  have hrhs := (hjet r 1).add (hweight.mul hdiff)
  have heq : (fun ε ↦ (layer Real.exp N (Y ε) r i - x r) / ε ^ 2) =ᶠ[F]
      fun ε ↦ (Y ε r 1 - x r) / ε ^ 2 +
        weightedLogistic
          (attentionScore N (Y ε) i 0 - attentionScore N (Y ε) i 1) *
            ((Y ε r 0 - x r) / ε ^ 2 - (Y ε r 1 - x r) / ε ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : ε ≠ 0 := hε
    obtain ⟨y₀, y₁, hy⟩ := hpattern ε
    rw [hy, layer_exp_triplePattern_formula]
    change
      (y₁ r + weightedLogistic
          (attentionScore N (triplePattern y₀ y₁) i 0 -
            attentionScore N (triplePattern y₀ y₁) i 1) * (y₀ r - y₁ r) - x r) /
          ε ^ 2 =
        (y₁ r - x r) / ε ^ 2 +
          weightedLogistic
              (attentionScore N (triplePattern y₀ y₁) i 0 -
                attentionScore N (triplePattern y₀ y₁) i 1) *
            ((y₀ r - x r) / ε ^ 2 - (y₁ r - x r) / ε ^ 2)
    field_simp [hε0]
    ring
  apply Filter.Tendsto.congr' heq.symm
  simpa using hrhs

private theorem tendsto_value_of_triple_quadraticJet
    (f : ℝ → ℝ) (x v : ℝ)
    (hjet : Filter.Tendsto (fun ε ↦ (f ε - x) / ε ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds v)) :
    Filter.Tendsto f (nhdsWithin 0 {0}ᶜ) (nhds x) := by
  let F := nhdsWithin (0 : ℝ) ({0}ᶜ)
  have he2 : Filter.Tendsto (fun ε : ℝ ↦ ε ^ 2) F (nhds 0) := by
    have hc : ContinuousAt (fun ε : ℝ ↦ ε ^ 2) 0 := by fun_prop
    simpa using hc.tendsto.mono_left
      (show F ≤ nhds 0 from nhdsWithin_le_nhds)
  have hp := he2.mul hjet
  have heq : (fun ε ↦ f ε - x) =ᶠ[F]
      fun ε ↦ ε ^ 2 * ((f ε - x) / ε ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : ε ≠ 0 := hε
    field_simp [hε0]
  have hsub : Filter.Tendsto (fun ε ↦ f ε - x) F (nhds 0) := by
    apply Filter.Tendsto.congr' heq.symm
    simpa using hp
  exact tendsto_sub_nhds_zero_iff.mp hsub

/-- The complete two-layer realization on three tokens has a quadratic jet depending
only on the first virtual score and final value matrices. -/
theorem realizeTwo_exp_tripleCenteredPerturbation_quadraticJet {d dOut : ℕ}
    (W : TwoLayerWeights d dOut) (x u : Fin d → ℝ)
    (r : Fin dOut) (i : Fin 3) :
    Filter.Tendsto
      (fun ε : ℝ ↦
        (realizeTwo Real.exp W (tripleCenteredPerturbation x u ε) r i -
          (W.L.mulVec x) r) / ε ^ 2)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (2 * dotProduct x (W.M₁.mulVec u) * (W.L.mulVec u) r)) := by
  let Y : ℝ → Matrix (Fin d) (Fin 3) ℝ :=
    fun ε ↦ layer Real.exp W.M₁ (tripleCenteredPerturbation x u ε)
  let v : Fin d → ℝ := fun c ↦ 2 * dotProduct x (W.M₁.mulVec u) * u c
  have hYjet (c : Fin d) (j : Fin 3) :
      Filter.Tendsto (fun ε ↦ (Y ε c j - x c) / ε ^ 2)
        (nhdsWithin 0 {0}ᶜ) (nhds (v c)) := by
    exact layer_exp_tripleCenteredPerturbation_quadraticJet W.M₁ x u c j
  have hY (c : Fin d) (j : Fin 3) :
      Filter.Tendsto (fun ε ↦ Y ε c j) (nhdsWithin 0 {0}ᶜ) (nhds (x c)) :=
    tendsto_value_of_triple_quadraticJet _ _ _ (hYjet c j)
  have hpattern (ε : ℝ) : ∃ y₀ y₁, Y ε = triplePattern y₀ y₁ := by
    exact layer_exp_triplePattern_is_triplePattern W.M₁ _ _
  let Z : ℝ → Matrix (Fin d) (Fin 3) ℝ := fun ε ↦ layer Real.exp W.M₂ (Y ε)
  have hZjet (c : Fin d) (j : Fin 3) :
      Filter.Tendsto (fun ε ↦ (Z ε c j - x c) / ε ^ 2)
        (nhdsWithin 0 {0}ᶜ) (nhds (v c)) :=
    layer_exp_preserves_triple_common_quadraticJet W.M₂ Y x v hpattern hY hYjet c j
  have hsum : Filter.Tendsto
      (fun ε ↦ ∑ c : Fin d, W.L r c * ((Z ε c i - x c) / ε ^ 2))
      (nhdsWithin 0 {0}ᶜ)
      (nhds (∑ c : Fin d, W.L r c * v c)) := by
    apply tendsto_finsetSum Finset.univ
    intro c _
    exact tendsto_const_nhds.mul (hZjet c i)
  have heq : (fun ε : ℝ ↦
      (realizeTwo Real.exp W (tripleCenteredPerturbation x u ε) r i -
        (W.L.mulVec x) r) / ε ^ 2) =ᶠ[nhdsWithin 0 {0}ᶜ]
      fun ε ↦ ∑ c : Fin d, W.L r c * ((Z ε c i - x c) / ε ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : ε ≠ 0 := hε
    have hpow : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε0
    simp only [realizeTwo, Matrix.mul_apply, Matrix.mulVec, dotProduct, Y, Z]
    apply (div_eq_iff hpow).2
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    field_simp [hpow]
  apply Filter.Tendsto.congr' heq.symm
  have hvsum : (∑ c : Fin d, W.L r c * v c) =
      2 * dotProduct x (W.M₁.mulVec u) * (W.L.mulVec u) r := by
    change (∑ c : Fin d, W.L r c *
        (2 * dotProduct x (W.M₁.mulVec u) * u c)) =
      2 * dotProduct x (W.M₁.mulVec u) *
        (∑ c : Fin d, W.L r c * u c)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  simpa [hvsum] using hsum

/-- Three-token functional equality recovers the first virtual score matrix. -/
theorem firstScore_identifiable_of_realizeTwo_exp_three_eq {d dOut : ℕ}
    (W W' : TwoLayerWeights d dOut) (hL : W.L ≠ 0)
    (hEq : realizeTwo (t := 3) Real.exp W = realizeTwo Real.exp W') :
    W.M₁ = W'.M₁ := by
  have hLL : W.L = W'.L :=
    finalValue_identifiable Real.exp Real.exp_pos W W' (by omega) hEq
  have hprobe (x u : Fin d → ℝ) :
      (dotProduct x (W.M₁.mulVec u)) • W.L.mulVec u =
        (dotProduct x (W'.M₁.mulVec u)) • W.L.mulVec u := by
    funext r
    have hleft := realizeTwo_exp_tripleCenteredPerturbation_quadraticJet W x u r 0
    have hright := realizeTwo_exp_tripleCenteredPerturbation_quadraticJet W' x u r 0
    rw [← hLL] at hright
    have hfun : (fun ε : ℝ ↦
        (realizeTwo Real.exp W (tripleCenteredPerturbation x u ε) r 0 -
          (W.L.mulVec x) r) / ε ^ 2) =
        fun ε ↦
          (realizeTwo Real.exp W' (tripleCenteredPerturbation x u ε) r 0 -
            (W.L.mulVec x) r) / ε ^ 2 := by
      funext ε
      rw [congrFun hEq (tripleCenteredPerturbation x u ε)]
    rw [← hfun] at hright
    have hu := tendsto_nhds_unique hleft hright
    have hu' : 2 * (dotProduct x (W.M₁.mulVec u) * (W.L.mulVec u) r) =
        2 * (dotProduct x (W'.M₁.mulVec u) * (W.L.mulVec u) r) := by
      nlinarith [hu]
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hu')
  exact matrix_eq_of_rankOne_jets_eq W.L W.M₁ W'.M₁ hL hprobe

theorem weightedLogistic_injective : Function.Injective weightedLogistic := by
  intro a b h
  have ha : Real.exp a + 2 ≠ 0 := by positivity
  have hb : Real.exp b + 2 ≠ 0 := by positivity
  unfold weightedLogistic at h
  field_simp [ha, hb] at h
  apply Real.exp_injective
  linarith

theorem postValue_layer_exp_triplePattern_formula {d dOut : ℕ}
    (L : Matrix (Fin dOut) (Fin d) ℝ) (N : Matrix (Fin d) (Fin d) ℝ)
    (y₀ y₁ : Fin d → ℝ) (r : Fin dOut) (i : Fin 3) :
    (L * layer Real.exp N (triplePattern y₀ y₁)) r i =
      (L.mulVec y₁) r +
        weightedLogistic
          (attentionScore N (triplePattern y₀ y₁) i 0 -
            attentionScore N (triplePattern y₀ y₁) i 1) *
          (L.mulVec (y₀ - y₁)) r := by
  let s := weightedLogistic
    (attentionScore N (triplePattern y₀ y₁) i 0 -
      attentionScore N (triplePattern y₀ y₁) i 1)
  change (∑ c : Fin d, L r c * layer Real.exp N (triplePattern y₀ y₁) c i) =
    (∑ c : Fin d, L r c * y₁ c) + s * ∑ c : Fin d, L r c * (y₀ c - y₁ c)
  calc
    _ = ∑ c : Fin d, (L r c * y₁ c + s * (L r c * (y₀ c - y₁ c))) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [layer_exp_triplePattern_formula]
      dsimp [s]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

theorem triple_scoreDifference_eq_of_postValue_layer_eq {d dOut : ℕ}
    (L : Matrix (Fin dOut) (Fin d) ℝ)
    (N N' : Matrix (Fin d) (Fin d) ℝ) (y₀ y₁ : Fin d → ℝ)
    (hvisible : L.mulVec (y₀ - y₁) ≠ 0)
    (hEq : L * layer Real.exp N (triplePattern y₀ y₁) =
      L * layer Real.exp N' (triplePattern y₀ y₁)) (i : Fin 3) :
    attentionScore N (triplePattern y₀ y₁) i 0 -
        attentionScore N (triplePattern y₀ y₁) i 1 =
      attentionScore N' (triplePattern y₀ y₁) i 0 -
        attentionScore N' (triplePattern y₀ y₁) i 1 := by
  obtain ⟨r, hr⟩ : ∃ r, (L.mulVec (y₀ - y₁)) r ≠ 0 := by
    by_contra h
    push Not at h
    exact hvisible (funext h)
  have he := congrFun (congrFun hEq r) i
  rw [postValue_layer_exp_triplePattern_formula,
    postValue_layer_exp_triplePattern_formula] at he
  apply weightedLogistic_injective
  apply mul_right_cancel₀ hr
  linarith

private theorem triple_scoreDifference_eq_dot_sub {d : ℕ}
    (N : Matrix (Fin d) (Fin d) ℝ) (y₀ y₁ : Fin d → ℝ) (i : Fin 3) :
    attentionScore N (triplePattern y₀ y₁) i 0 -
        attentionScore N (triplePattern y₀ y₁) i 1 =
      dotProduct ((triplePattern y₀ y₁).col i) (N.mulVec (y₀ - y₁)) := by
  simp [attentionScore, Matrix.mulVec_sub, dotProduct_sub]

private theorem firstLayer_tripleCentered_difference {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (x u : Fin d → ℝ) :
    let a := dotProduct x (M.mulVec u)
    let b := dotProduct u (M.mulVec u)
    let c := 3 * (weightedLogistic (3 * (a + 2 * b)) -
      weightedLogistic (3 * (a - b)))
    (layer Real.exp M (tripleCenteredPerturbation x u 1)).col 0 -
        (layer Real.exp M (tripleCenteredPerturbation x u 1)).col 1 = c • u := by
  dsimp only
  ext r
  change layer Real.exp M (tripleCenteredPerturbation x u 1) r 0 -
      layer Real.exp M (tripleCenteredPerturbation x u 1) r 1 = _
  simp only [tripleCenteredPerturbation, mul_one, one_smul]
  rw [layer_exp_triplePattern_formula, layer_exp_triplePattern_formula,
    show attentionScore M (triplePattern (x + (2 : ℝ) • u) (x - u)) 0 0 -
        attentionScore M (triplePattern (x + (2 : ℝ) • u) (x - u)) 0 1 =
        3 * (dotProduct x (M.mulVec u) + 2 * dotProduct u (M.mulVec u)) by
      simpa [tripleCenteredPerturbation] using
        tripleCenteredPerturbation_scoreDifference_zero M x u 1,
    show attentionScore M (triplePattern (x + (2 : ℝ) • u) (x - u)) 1 0 -
        attentionScore M (triplePattern (x + (2 : ℝ) • u) (x - u)) 1 1 =
        3 * (dotProduct x (M.mulVec u) - dotProduct u (M.mulVec u)) by
      simpa [tripleCenteredPerturbation] using
        tripleCenteredPerturbation_scoreDifference_one M x u 1]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem firstLayer_tripleCentered_difference_scalar_ne_zero {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (x u : Fin d → ℝ)
    (hb : dotProduct u (M.mulVec u) ≠ 0) :
    3 * (weightedLogistic
        (3 * (dotProduct x (M.mulVec u) + 2 * dotProduct u (M.mulVec u))) -
      weightedLogistic
        (3 * (dotProduct x (M.mulVec u) - dotProduct u (M.mulVec u)))) ≠ 0 := by
  intro h
  have hs : weightedLogistic
      (3 * (dotProduct x (M.mulVec u) + 2 * dotProduct u (M.mulVec u))) =
    weightedLogistic
      (3 * (dotProduct x (M.mulVec u) - dotProduct u (M.mulVec u))) := by
    linarith
  have hi := weightedLogistic_injective hs
  apply hb
  linarith

private theorem firstLayer_tripleCentered_zero_col {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (x u : Fin d → ℝ) :
    (layer Real.exp M (tripleCenteredPerturbation x u 1)).col 0 =
      x + (-1 + 3 * weightedLogistic
        (3 * (dotProduct x (M.mulVec u) + 2 * dotProduct u (M.mulVec u)))) • u := by
  ext r
  change layer Real.exp M (tripleCenteredPerturbation x u 1) r 0 = _
  simp only [tripleCenteredPerturbation, mul_one, one_smul]
  rw [layer_exp_triplePattern_formula,
    show attentionScore M (triplePattern (x + (2 : ℝ) • u) (x - u)) 0 0 -
        attentionScore M (triplePattern (x + (2 : ℝ) • u) (x - u)) 0 1 =
        3 * (dotProduct x (M.mulVec u) + 2 * dotProduct u (M.mulVec u)) by
      simpa [tripleCenteredPerturbation] using
        tripleCenteredPerturbation_scoreDifference_zero M x u 1]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- On every value-visible, first-score-nonisotropic direction, three-token
functional equality identifies the second virtual score's full bilinear action. -/
theorem secondScore_probe_of_realizeTwo_exp_three_eq {d dOut : ℕ}
    (W W' : TwoLayerWeights d dOut)
    (hM₁ : W.M₁ = W'.M₁) (hL : W.L = W'.L)
    (hEq : realizeTwo (t := 3) Real.exp W = realizeTwo Real.exp W')
    (u : Fin d → ℝ) (huM : dotProduct u (W.M₁.mulVec u) ≠ 0)
    (huL : W.L.mulVec u ≠ 0) :
    ∀ x : Fin d → ℝ,
      dotProduct x (W.M₂.mulVec u) = dotProduct x (W'.M₂.mulVec u) := by
  intro x
  let X := tripleCenteredPerturbation x u 1
  let Y := layer Real.exp W.M₁ X
  let y₀ := Y.col 0
  let y₁ := Y.col 1
  let c := 3 * (weightedLogistic
      (3 * (dotProduct x (W.M₁.mulVec u) + 2 * dotProduct u (W.M₁.mulVec u))) -
    weightedLogistic
      (3 * (dotProduct x (W.M₁.mulVec u) - dotProduct u (W.M₁.mulVec u))))
  have hc : c ≠ 0 :=
    firstLayer_tripleCentered_difference_scalar_ne_zero W.M₁ x u huM
  have hdiff : y₀ - y₁ = c • u := by
    exact firstLayer_tripleCentered_difference W.M₁ x u
  have hpattern : Y = triplePattern y₀ y₁ := by
    ext r i
    fin_cases i
    · rfl
    · rfl
    · change layer Real.exp W.M₁ X r 2 = layer Real.exp W.M₁ X r 1
      simp only [X, tripleCenteredPerturbation, mul_one, one_smul]
      rw [layer_exp_triplePattern_formula, layer_exp_triplePattern_formula]
      congr 2
  have hvisible : W.L.mulVec (y₀ - y₁) ≠ 0 := by
    rw [hdiff, Matrix.mulVec_smul]
    exact smul_ne_zero hc huL
  have houter : W.L * layer Real.exp W.M₂ (triplePattern y₀ y₁) =
      W.L * layer Real.exp W'.M₂ (triplePattern y₀ y₁) := by
    have heval := congrFun hEq X
    simp only [realizeTwo, X] at heval
    rw [← hM₁, ← hL] at heval
    change W.L * layer Real.exp W.M₂ Y =
      W.L * layer Real.exp W'.M₂ Y at heval
    simpa only [hpattern] using heval
  have hs0 := triple_scoreDifference_eq_of_postValue_layer_eq
    W.L W.M₂ W'.M₂ y₀ y₁ hvisible houter 0
  have hs1 := triple_scoreDifference_eq_of_postValue_layer_eq
    W.L W.M₂ W'.M₂ y₀ y₁ hvisible houter 1
  rw [triple_scoreDifference_eq_dot_sub, triple_scoreDifference_eq_dot_sub,
    triplePattern_col_zero, hdiff, Matrix.mulVec_smul, Matrix.mulVec_smul,
    dotProduct_smul, dotProduct_smul] at hs0
  rw [triple_scoreDifference_eq_dot_sub, triple_scoreDifference_eq_dot_sub,
    triplePattern_col_one, hdiff, Matrix.mulVec_smul, Matrix.mulVec_smul,
    dotProduct_smul, dotProduct_smul] at hs1
  have hc0 : dotProduct y₀ (W.M₂.mulVec u) =
      dotProduct y₀ (W'.M₂.mulVec u) := mul_left_cancel₀ hc hs0
  have hc1 : dotProduct y₁ (W.M₂.mulVec u) =
      dotProduct y₁ (W'.M₂.mulVec u) := mul_left_cancel₀ hc hs1
  have hquad : dotProduct u (W.M₂.mulVec u) =
      dotProduct u (W'.M₂.mulVec u) := by
    have hsub : dotProduct (y₀ - y₁) (W.M₂.mulVec u) =
        dotProduct (y₀ - y₁) (W'.M₂.mulVec u) := by
      rw [sub_dotProduct, sub_dotProduct, hc0, hc1]
    rw [hdiff, smul_dotProduct, smul_dotProduct] at hsub
    exact mul_left_cancel₀ hc hsub
  have hcol : y₀ = x + (-1 + 3 * weightedLogistic
      (3 * (dotProduct x (W.M₁.mulVec u) + 2 * dotProduct u (W.M₁.mulVec u)))) • u :=
    firstLayer_tripleCentered_zero_col W.M₁ x u
  rw [hcol, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct,
    hquad] at hc0
  linarith

/-- Complete depth-two singleton-fiber theorem for the paper's three-token
experiment, on the explicit regular locus `L ≠ 0` and `M₁ᵀ ≠ -M₁`. -/
theorem realizeTwo_exp_three_fiber_singleton {d dOut : ℕ}
    (W W' : TwoLayerWeights d dOut)
    (hL : W.L ≠ 0) (hM : W.M₁.transpose ≠ -W.M₁)
    (hEq : realizeTwo (t := 3) Real.exp W = realizeTwo Real.exp W') :
    W = W' := by
  have hLL : W.L = W'.L :=
    finalValue_identifiable Real.exp Real.exp_pos W W' (by omega) hEq
  have hM₁ : W.M₁ = W'.M₁ :=
    firstScore_identifiable_of_realizeTwo_exp_three_eq W W' hL hEq
  have hM₂ : W.M₂ = W'.M₂ :=
    matrix_eq_of_eq_on_visible_nonisotropic W.L W.M₁ W.M₂ W'.M₂ hL hM
      (fun u huM huL ↦
        secondScore_probe_of_realizeTwo_exp_three_eq W W' hM₁ hLL hEq u huM huL)
  cases W
  cases W'
  simp_all

end NormalizedDeepAttention
