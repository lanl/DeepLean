module

public import DeepLean.Attention.Genericity

/-!
# General normalization interfaces

This file separates facts valid for every positive normalization from the
exponential-specific deep proof.  In particular it records the exact
one-versus-many dynamics without replacing a ratio of two `S`-values by a
function of a score difference.
-/

@[expose] public section

namespace NormalizedDeepAttention

/-- The four scalar coefficients of a bilinear score on an affine line. -/
def generalLineScore (c a aT b s r : ℝ) : ℝ :=
  c + r * a + s * aT + s * r * b

/-- Distinguished-token coefficient after one general normalized layer. -/
noncomputable def generalStepFirst (S : ℝ → ℝ) (n c a aT b p q : ℝ) : ℝ :=
  (S (generalLineScore c a aT b p p) * p +
      n * S (generalLineScore c a aT b p q) * q) /
    (S (generalLineScore c a aT b p p) +
      n * S (generalLineScore c a aT b p q))

/-- Repeated-token coefficient after one general normalized layer. -/
noncomputable def generalStepRepeated (S : ℝ → ℝ) (n c a aT b p q : ℝ) : ℝ :=
  (S (generalLineScore c a aT b q p) * p +
      n * S (generalLineScore c a aT b q q) * q) /
    (S (generalLineScore c a aT b q p) +
      n * S (generalLineScore c a aT b q q))

/-- Exact general-`S` closure of a one-versus-many affine-line pattern.

Unlike the exponential formula, this retains the absolute row baselines `c`
and `aT`; injectivity and positivity alone do not turn it into a function only
of score differences. -/
theorem layer_general_repeatedLinePattern {d n : ℕ} (hn : 0 < n)
    (S : ℝ → ℝ) (hSpos : ∀ z, 0 < S z)
    (M : ScoreMatrix d) (x u : Fin d → ℝ) (p q : ℝ) :
    layer S M (repeatedLinePattern (n := n) x u p q) =
      repeatedLinePattern x u
        (generalStepFirst S n
          (dotProduct x (M.mulVec x)) (dotProduct x (M.mulVec u))
          (dotProduct u (M.mulVec x)) (dotProduct u (M.mulVec u)) p q)
        (generalStepRepeated S n
          (dotProduct x (M.mulVec x)) (dotProduct x (M.mulVec u))
          (dotProduct u (M.mulVec x)) (dotProduct u (M.mulVec u)) p q) := by
  apply Matrix.ext
  intro r i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change normalizedAttention S M 1
      (firstAndRepeatedTokenMatrix (x + p • u) (x + q • u)) r 0 =
        x r + generalStepFirst S n
          (dotProduct x (M.mulVec x)) (dotProduct x (M.mulVec u))
          (dotProduct u (M.mulVec x)) (dotProduct u (M.mulVec u)) p q * u r
    rw [normalizedAttention_firstAndRepeated_first]
    simp only [Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hpp : dotProduct (x + p • u) (M.mulVec (x + p • u)) =
        generalLineScore (dotProduct x (M.mulVec x)) (dotProduct x (M.mulVec u))
          (dotProduct u (M.mulVec x)) (dotProduct u (M.mulVec u)) p p := by
      simp only [generalLineScore, Matrix.mulVec_add, Matrix.mulVec_smul,
        add_dotProduct, dotProduct_add, dotProduct_smul, smul_dotProduct]
      ring
    have hpq : dotProduct (x + p • u) (M.mulVec (x + q • u)) =
        generalLineScore (dotProduct x (M.mulVec x)) (dotProduct x (M.mulVec u))
          (dotProduct u (M.mulVec x)) (dotProduct u (M.mulVec u)) p q := by
      simp only [generalLineScore, Matrix.mulVec_add, Matrix.mulVec_smul,
        add_dotProduct, dotProduct_add, dotProduct_smul, smul_dotProduct]
      ring
    rw [hpp, hpq]
    unfold generalStepFirst
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hden : S (generalLineScore (dotProduct x (M.mulVec x))
          (dotProduct x (M.mulVec u)) (dotProduct u (M.mulVec x))
          (dotProduct u (M.mulVec u)) p p) +
        n * S (generalLineScore (dotProduct x (M.mulVec x))
          (dotProduct x (M.mulVec u)) (dotProduct u (M.mulVec x))
          (dotProduct u (M.mulVec u)) p q) ≠ 0 := by
      exact ne_of_gt (add_pos (hSpos _) (mul_pos hnR (hSpos _)))
    field_simp [hden]
    ring
  · change normalizedAttention S M 1
      (firstAndRepeatedTokenMatrix (x + p • u) (x + q • u)) r j.succ =
        x r + generalStepRepeated S n
          (dotProduct x (M.mulVec x)) (dotProduct x (M.mulVec u))
          (dotProduct u (M.mulVec x)) (dotProduct u (M.mulVec u)) p q * u r
    rw [normalizedAttention_firstAndRepeated_repeated]
    simp only [Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hqp : dotProduct (x + q • u) (M.mulVec (x + p • u)) =
        generalLineScore (dotProduct x (M.mulVec x)) (dotProduct x (M.mulVec u))
          (dotProduct u (M.mulVec x)) (dotProduct u (M.mulVec u)) q p := by
      simp only [generalLineScore, Matrix.mulVec_add, Matrix.mulVec_smul,
        add_dotProduct, dotProduct_add, dotProduct_smul, smul_dotProduct]
      ring
    have hqq : dotProduct (x + q • u) (M.mulVec (x + q • u)) =
        generalLineScore (dotProduct x (M.mulVec x)) (dotProduct x (M.mulVec u))
          (dotProduct u (M.mulVec x)) (dotProduct u (M.mulVec u)) q q := by
      simp only [generalLineScore, Matrix.mulVec_add, Matrix.mulVec_smul,
        add_dotProduct, dotProduct_add, dotProduct_smul, smul_dotProduct]
      ring
    rw [hqp, hqq]
    unfold generalStepRepeated
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hden : S (generalLineScore (dotProduct x (M.mulVec x))
          (dotProduct x (M.mulVec u)) (dotProduct u (M.mulVec x))
          (dotProduct u (M.mulVec u)) q p) +
        n * S (generalLineScore (dotProduct x (M.mulVec x))
          (dotProduct x (M.mulVec u)) (dotProduct u (M.mulVec x))
          (dotProduct u (M.mulVec u)) q q) ≠ 0 := by
      exact ne_of_gt (add_pos (hSpos _) (mul_pos hnR (hSpos _)))
    field_simp [hden]
    ring

/-- A normalized two-score observation anchored at `S(0)=1`. -/
noncomputable def zeroAnchoredCoefficient (S : ℝ → ℝ) (n q : ℝ) : ℝ :=
  S q / (S q + n)

/-- Zero anchoring recovers an absolute score using exactly the paper's
positivity and injectivity assumptions. -/
theorem zeroAnchoredCoefficient_injective (S : ℝ → ℝ)
    (hSpos : ∀ z, 0 < S z) (hSinj : Function.Injective S)
    {n : ℝ} (hn : 0 < n) : Function.Injective (zeroAnchoredCoefficient S n) := by
  intro a b h
  unfold zeroAnchoredCoefficient at h
  have ha : S a + n ≠ 0 := ne_of_gt (add_pos (hSpos a) hn)
  have hb : S b + n ≠ 0 := ne_of_gt (add_pos (hSpos b) hn)
  field_simp [ha, hb] at h
  apply hSinj
  have hn0 : n ≠ 0 := ne_of_gt hn
  apply mul_left_cancel₀ hn0
  nlinarith

/-- Exponential normalization with an arbitrary nonzero linear log-slope. -/
noncomputable def scaledExponentialNormalization (c z : ℝ) : ℝ := Real.exp (c * z)

/-- Natural repaired normalization class: `log S` is linear with nonzero
slope.  This is a scalar, independently checkable condition. -/
def LogAffineNormalization (S : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧ S = scaledExponentialNormalization c

theorem attentionScore_smul {d t : ℕ} (c : ℝ) (M : ScoreMatrix d)
    (X : Matrix (Fin d) (Fin t) ℝ) (i j : Fin t) :
    attentionScore (c • M) X i j = c * attentionScore M X i j := by
  simp [attentionScore, Matrix.smul_mulVec, dotProduct_smul]

theorem layer_temperature_eq {d t : ℕ} (τ : ℝ) (M : ScoreMatrix d)
    (X : Matrix (Fin d) (Fin t) ℝ) :
    layer (temperatureNormalization τ) M X = layer Real.exp (τ⁻¹ • M) X := by
  ext r i
  simp only [layer, normalizedAttention]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [attentionScore_smul]
    simp [temperatureNormalization, div_eq_inv_mul]
  · apply Finset.sum_congr rfl
    intro j _
    rw [attentionScore_smul]
    simp [temperatureNormalization, div_eq_inv_mul]

theorem layer_scaledExponential_eq {d t : ℕ} (c : ℝ) (M : ScoreMatrix d)
    (X : Matrix (Fin d) (Fin t) ℝ) :
    layer (scaledExponentialNormalization c) M X = layer Real.exp (c • M) X := by
  ext r i
  simp only [layer, normalizedAttention]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [attentionScore_smul]
    rfl
  · apply Finset.sum_congr rfl
    intro j _
    rw [attentionScore_smul]
    rfl

def scaleDeepScores {d dOut : ℕ} (c : ℝ) (W : DeepWeights d dOut) :
    DeepWeights d dOut :=
  ⟨c • W.M₁, W.rest.map (fun M ↦ c • M), W.L⟩

theorem applyLayers_temperature_eq {d t : ℕ} (τ : ℝ)
    (Ms : List (ScoreMatrix d)) (X : Matrix (Fin d) (Fin t) ℝ) :
    applyLayers (temperatureNormalization τ) Ms X =
      applyLayers Real.exp (Ms.map (fun M ↦ τ⁻¹ • M)) X := by
  induction Ms generalizing X with
  | nil => rfl
  | cons M Ms ih =>
      simp only [applyLayers, List.map_cons, layer_temperature_eq, ih]

theorem applyLayers_scaledExponential_eq {d t : ℕ} (c : ℝ)
    (Ms : List (ScoreMatrix d)) (X : Matrix (Fin d) (Fin t) ℝ) :
    applyLayers (scaledExponentialNormalization c) Ms X =
      applyLayers Real.exp (Ms.map (fun M ↦ c • M)) X := by
  induction Ms generalizing X with
  | nil => rfl
  | cons M Ms ih =>
      simp only [applyLayers, List.map_cons, layer_scaledExponential_eq, ih]

theorem realizeDeep_temperature_eq {d dOut t : ℕ} (τ : ℝ)
    (W : DeepWeights d dOut) :
    realizeDeep (t := t) (temperatureNormalization τ) W =
      realizeDeep Real.exp (scaleDeepScores τ⁻¹ W) := by
  funext X
  rw [realizeDeep, realizeDeep, layer_temperature_eq,
    applyLayers_temperature_eq]
  rfl

theorem realizeDeep_scaledExponential_eq {d dOut t : ℕ} (c : ℝ)
    (W : DeepWeights d dOut) :
    realizeDeep (t := t) (scaledExponentialNormalization c) W =
      realizeDeep Real.exp (scaleDeepScores c W) := by
  funext X
  rw [realizeDeep, realizeDeep, layer_scaledExponential_eq,
    applyLayers_scaledExponential_eq]
  rfl

private theorem smul_matrix_injective {d : ℕ} {c : ℝ} (hc : c ≠ 0) :
    Function.Injective (fun M : ScoreMatrix d ↦ c • M) := by
  intro A B h
  ext i j
  have hij := congrFun (congrFun h i) j
  change c * A i j = c * B i j at hij
  exact mul_left_cancel₀ hc hij

theorem scaleDeepScores_injective {d dOut : ℕ} {c : ℝ} (hc : c ≠ 0) :
    Function.Injective (scaleDeepScores (d := d) (dOut := dOut) c) := by
  intro W W' h
  cases W with
  | mk M Ms L =>
    cases W' with
    | mk M' Ms' L' =>
      simp only [scaleDeepScores, DeepWeights.mk.injEq] at h ⊢
      refine ⟨smul_matrix_injective hc h.1, ?_, h.2.2⟩
      exact (List.map_injective_iff.mpr (smul_matrix_injective hc)) h.2.1

private theorem not_skew_smul {d : ℕ} {c : ℝ} (hc : c ≠ 0)
    (M : ScoreMatrix d) (hM : M.transpose ≠ -M) :
    (c • M).transpose ≠ -(c • M) := by
  intro h
  apply hM
  apply smul_matrix_injective hc
  simpa only [Matrix.transpose_smul, smul_neg] using h

theorem regularDeep_scale {d dOut : ℕ} {c : ℝ} (hc : c ≠ 0)
    (W : DeepWeights d dOut) (hW : RegularDeep W) :
    RegularDeep (scaleDeepScores c W) := by
  constructor
  · exact hW.1
  · intro N hN
    simp only [scaleDeepScores, List.mem_cons, List.mem_map] at hN
    rcases hN with hfirst | ⟨M, hMmem, rfl⟩
    · rw [hfirst]
      exact not_skew_smul hc W.M₁ (hW.2 W.M₁ (by simp))
    · exact not_skew_smul hc M (hW.2 M (by simp [hMmem]))

theorem properPrefixNonSkew_map_smul {d : ℕ} {c : ℝ} (hc : c ≠ 0)
    (Ms : List (ScoreMatrix d)) (hMs : ProperPrefixNonSkew Ms) :
    ProperPrefixNonSkew (Ms.map fun M ↦ c • M) := by
  intro N hN
  rw [← List.map_dropLast] at hN
  rcases List.mem_map.mp hN with ⟨M, hM, rfl⟩
  exact not_skew_smul hc M (hMs M hM)

theorem properPrefixNonSkew_scaleDeepScores {d dOut : ℕ} {c : ℝ} (hc : c ≠ 0)
    (W : DeepWeights d dOut) (hW : ProperPrefixNonSkew (W.M₁ :: W.rest)) :
    ProperPrefixNonSkew
      ((scaleDeepScores c W).M₁ :: (scaleDeepScores c W).rest) := by
  simpa [scaleDeepScores] using
    properPrefixNonSkew_map_smul hc (W.M₁ :: W.rest) hW

/-- Positive-temperature identifiability with no regularity requirement on
the terminal source score. -/
theorem realizeDeep_temperature_fiber_singleton_properPrefix {d dOut t : ℕ}
    (τ : ℝ) (hτ : 0 < τ) (ht : 2 ≤ t)
    (W W' : DeepWeights d dOut) (hL : W.L ≠ 0)
    (hproper : ProperPrefixNonSkew (W.M₁ :: W.rest))
    (hdepth : W.rest.length = W'.rest.length)
    (hEq : realizeDeep (t := t) (temperatureNormalization τ) W =
      realizeDeep (temperatureNormalization τ) W') : W = W' := by
  have hc : τ⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hτ)
  apply scaleDeepScores_injective hc
  apply realizeDeep_exp_fiber_singleton_properPrefix ht
    (scaleDeepScores τ⁻¹ W) (scaleDeepScores τ⁻¹ W') hL
    (properPrefixNonSkew_scaleDeepScores hc W hproper)
  · simpa [scaleDeepScores] using hdepth
  · simpa only [← realizeDeep_temperature_eq] using hEq

/-- Nonzero log-slope exponential identifiability with an unrestricted
terminal source score. -/
theorem realizeDeep_scaledExponential_fiber_singleton_properPrefix {d dOut t : ℕ}
    (c : ℝ) (hc : c ≠ 0) (ht : 2 ≤ t)
    (W W' : DeepWeights d dOut) (hL : W.L ≠ 0)
    (hproper : ProperPrefixNonSkew (W.M₁ :: W.rest))
    (hdepth : W.rest.length = W'.rest.length)
    (hEq : realizeDeep (t := t) (scaledExponentialNormalization c) W =
      realizeDeep (scaledExponentialNormalization c) W') : W = W' := by
  apply scaleDeepScores_injective hc
  apply realizeDeep_exp_fiber_singleton_properPrefix ht
    (scaleDeepScores c W) (scaleDeepScores c W') hL
    (properPrefixNonSkew_scaleDeepScores hc W hproper)
  · simpa [scaleDeepScores] using hdepth
  · simpa only [← realizeDeep_scaledExponential_eq] using hEq

/-- Log-affine identifiability with the sharp proper-prefix score condition. -/
theorem realizeDeep_logAffine_fiber_singleton_properPrefix {d dOut t : ℕ}
    (S : ℝ → ℝ) (hS : LogAffineNormalization S) (ht : 2 ≤ t)
    (W W' : DeepWeights d dOut) (hL : W.L ≠ 0)
    (hproper : ProperPrefixNonSkew (W.M₁ :: W.rest))
    (hdepth : W.rest.length = W'.rest.length)
    (hEq : realizeDeep (t := t) S W = realizeDeep S W') : W = W' := by
  rcases hS with ⟨c, hc, rfl⟩
  exact realizeDeep_scaledExponential_fiber_singleton_properPrefix c hc ht W W'
    hL hproper hdepth hEq

/-- The full ordinary softmax temperature family follows from the temperature
one theorem by an injective rescaling of every virtual score matrix. -/
theorem realizeDeep_temperature_fiber_singleton {d dOut t : ℕ}
    (τ : ℝ) (hτ : 0 < τ) (ht : 2 ≤ t)
    (W W' : DeepWeights d dOut) (hregular : RegularDeep W)
    (hdepth : W.rest.length = W'.rest.length)
    (hEq : realizeDeep (t := t) (temperatureNormalization τ) W =
      realizeDeep (temperatureNormalization τ) W') : W = W' := by
  have hc : τ⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hτ)
  apply scaleDeepScores_injective hc
  apply realizeDeep_exp_fiber_singleton ht
    (scaleDeepScores τ⁻¹ W) (scaleDeepScores τ⁻¹ W')
    (regularDeep_scale hc W hregular).1 (regularDeep_scale hc W hregular).2
  · simpa [scaleDeepScores] using hdepth
  · simpa only [← realizeDeep_temperature_eq] using hEq

/-- Full-fiber theorem for every normalization with nonzero linear logarithm. -/
theorem realizeDeep_scaledExponential_fiber_singleton {d dOut t : ℕ}
    (c : ℝ) (hc : c ≠ 0) (ht : 2 ≤ t)
    (W W' : DeepWeights d dOut) (hregular : RegularDeep W)
    (hdepth : W.rest.length = W'.rest.length)
    (hEq : realizeDeep (t := t) (scaledExponentialNormalization c) W =
      realizeDeep (scaledExponentialNormalization c) W') : W = W' := by
  apply scaleDeepScores_injective hc
  apply realizeDeep_exp_fiber_singleton ht
    (scaleDeepScores c W) (scaleDeepScores c W')
    (regularDeep_scale hc W hregular).1 (regularDeep_scale hc W hregular).2
  · simpa [scaleDeepScores] using hdepth
  · simpa only [← realizeDeep_scaledExponential_eq] using hEq

/-- Abstract repaired-`S` theorem. -/
theorem realizeDeep_logAffine_fiber_singleton {d dOut t : ℕ}
    (S : ℝ → ℝ) (hS : LogAffineNormalization S) (ht : 2 ≤ t)
    (W W' : DeepWeights d dOut) (hregular : RegularDeep W)
    (hdepth : W.rest.length = W'.rest.length)
    (hEq : realizeDeep (t := t) S W = realizeDeep S W') : W = W' := by
  rcases hS with ⟨c, hc, rfl⟩
  exact realizeDeep_scaledExponential_fiber_singleton c hc ht W W'
    hregular hdepth hEq

end NormalizedDeepAttention
