module

public import DeepLean.Attention.NormalizationClassCounterexample
public import DeepLean.Attention.SourceArchitecture

/-!
# Manuscript Theorem 1: the normalized-attention counterexample

This is the reviewer-facing entry point for Theorem 1 of `submission.tex`.
It packages the exact scalar statement (`d = d_out = 1`, `t = 2`, depth
`ell = 2`) for the explicit Borel normalizer `exoticNormalization` and the
explicit partner `(m1, m2, l) -> (m1, 4*m2, l)`.

`deepNormalizedAttention_eq_virtual`, imported above, is the formal bridge
from the variable-width source architecture to the column-token virtual model
used here.  The complete realization equalities below are function equalities
on every `1 x 2` real input matrix.
-/

@[expose] public section

namespace Neuroalgebraic.Submission.Theorem1

open NormalizedDeepAttention

/-- Positivity, normalization at zero, injectivity, and real Borel
measurability of the explicit normalizer. -/
theorem normalizer_admissible :
    (∀ x, 0 < exoticNormalization x) ∧
      exoticNormalization 0 = 1 ∧
      Function.Injective exoticNormalization ∧
      Measurable exoticNormalization :=
  ⟨exoticNormalization_pos, exoticNormalization_zero,
    exoticNormalization_injective, exoticNormalization_measurable⟩

/-- The normalizer is discontinuous at zero. The `theorem1_counterexample`
does not use this fact; the strengthened certification interface includes it. -/
theorem normalizer_discontinuous_at_zero :
    ¬ ContinuousAt exoticNormalization 0 :=
  exoticNormalization_not_continuousAt_zero

/-- Four-scaling of every nonzero score. -/
theorem four_scaling {z : ℝ} (hz : z ≠ 0) :
    exoticNormalization (4 * z) = exoticNormalization z / 4 :=
  exoticNormalization_four_mul hz

/-- The domination inequality used in the opposite-sign input cases. -/
theorem mass_domination {z w : ℝ} (hz : 0 < z) (hw : 0 < w) :
    z * exoticNormalization z > w * exoticNormalization (-w) :=
  exotic_positive_mass_gt_negative_mass hz hw

/-- The manuscript's displayed formula for the first output token. -/
theorem scalar_first_output_formula (m a b : ℝ) :
    layer exoticNormalization (scalarScore m) (scalarPair a b) 0 0 =
      (exoticNormalization (m * a * a) * a +
        exoticNormalization (m * a * b) * b) /
      (exoticNormalization (m * a * a) +
        exoticNormalization (m * a * b)) :=
  layer_scalarPair_first m a b

/-- The manuscript's displayed formula for the second output token. -/
theorem scalar_second_output_formula (m a b : ℝ) :
    layer exoticNormalization (scalarScore m) (scalarPair a b) 0 (Fin.succ 0) =
      (exoticNormalization (m * b * a) * a +
        exoticNormalization (m * b * b) * b) /
      (exoticNormalization (m * b * a) +
        exoticNormalization (m * b * b)) :=
  layer_scalarPair_second m a b

/-- Every first-layer output token is nonzero on a nonzero input. -/
theorem first_layer_nonvanishing (m a b : ℝ) (hm : m ≠ 0)
    (hab : a ≠ 0 ∨ b ≠ 0) (i : Fin 2) :
    layer exoticNormalization (scalarScore m) (scalarPair a b) 0 i ≠ 0 :=
  exotic_first_layer_nonzero_of_pair_ne_zero m a b hm hab i

/-- If all scores are nonzero, multiplying the score matrix by four multiplies
every row weight by `1/4`, which cancels under normalization. -/
theorem row_scaling_cancellation {d t : ℕ} (M : ScoreMatrix d)
    (X : Matrix (Fin d) (Fin t) ℝ)
    (hscore : ∀ i j, attentionScore M X i j ≠ 0) :
    layer exoticNormalization ((4 : ℝ) • M) X =
      layer exoticNormalization M X :=
  layer_exotic_four_smul_eq_of_scores_ne_zero M X hscore

/-- Equality already holds for an arbitrary common final scalar `l`; the
manuscript retains `l != 0` only in its nondegenerate open-dense locus. -/
theorem partner_realization_eq_for_arbitrary_final
    (m1 m2 l : ℝ) (hm1 : m1 ≠ 0) (hm2 : m2 ≠ 0) :
    realizeDeep (t := 2) exoticNormalization
        (fixedDepthToDeep (exoticFamilyPartner m1 m2 l)) =
      realizeDeep exoticNormalization
        (fixedDepthToDeep (exoticFamilySource m1 m2 l)) :=
  (exoticFamilySource_realization_eq_partner hm1 hm2).symm

private theorem dense_first_coordinate :
    Dense {p : ScalarDepthTwoParameters | p.1 ≠ 0} := by
  change Dense ((fun p : ScalarDepthTwoParameters ↦ p.1) ⁻¹' ({0}ᶜ : Set ℝ))
  exact (dense_compl_singleton 0).preimage isOpenMap_fst

private theorem dense_second_coordinate :
    Dense {p : ScalarDepthTwoParameters | p.2.1 ≠ 0} := by
  change Dense ((fun p : ScalarDepthTwoParameters ↦ p.2.1) ⁻¹' ({0}ᶜ : Set ℝ))
  exact (dense_compl_singleton 0).preimage (isOpenMap_fst.comp isOpenMap_snd)

private theorem dense_final_coordinate :
    Dense {p : ScalarDepthTwoParameters | p.2.2 ≠ 0} := by
  change Dense ((fun p : ScalarDepthTwoParameters ↦ p.2.2) ⁻¹' ({0}ᶜ : Set ℝ))
  exact (dense_compl_singleton 0).preimage (isOpenMap_snd.comp isOpenMap_snd)

/-- The manuscript parameter set is literally nonempty, Euclidean open, and
dense in `R^3`. -/
theorem parameterLocus_nonempty_open_dense :
    Set.Nonempty parameterLocus ∧ IsOpen parameterLocus ∧ Dense parameterLocus := by
  have hopenFirst : IsOpen {p : ScalarDepthTwoParameters | p.1 ≠ 0} :=
    isOpen_ne_fun (by fun_prop) continuous_const
  have hopenSecond : IsOpen {p : ScalarDepthTwoParameters | p.2.1 ≠ 0} :=
    isOpen_ne_fun (by fun_prop) continuous_const
  have hopenFinal : IsOpen {p : ScalarDepthTwoParameters | p.2.2 ≠ 0} :=
    isOpen_ne_fun (by fun_prop) continuous_const
  have hlocus : parameterLocus =
      {p : ScalarDepthTwoParameters | p.1 ≠ 0} ∩
        ({p | p.2.1 ≠ 0} ∩ {p | p.2.2 ≠ 0}) := by
    ext p
    simp [parameterLocus, and_assoc]
  refine ⟨⟨(1, 1, 1), by norm_num [parameterLocus]⟩, ?_, ?_⟩
  · rw [hlocus]
    exact hopenFirst.inter (hopenSecond.inter hopenFinal)
  · rw [hlocus]
    exact dense_first_coordinate.inter_of_isOpen_right
      (dense_second_coordinate.inter_of_isOpen_right dense_final_coordinate hopenFinal)
      (hopenSecond.inter hopenFinal)

/-- Every point of the displayed locus has exactly the explicit distinct
partner claimed in the manuscript, with equality on the complete input space. -/
theorem explicit_partner (p : ScalarDepthTwoParameters) (hp : p ∈ parameterLocus) :
    source p ≠ partner p ∧
      realizeDeep (t := 2) exoticNormalization (fixedDepthToDeep (partner p)) =
        realizeDeep exoticNormalization (fixedDepthToDeep (source p)) := by
  have hproduct : p.1 * p.2.1 * p.2.2 ≠ 0 := hp
  rcases mul_ne_zero_iff.mp hproduct with ⟨hprefix, _hl⟩
  rcases mul_ne_zero_iff.mp hprefix with ⟨hm1, hm2⟩
  exact ⟨exoticFamilySource_ne_partner hm2,
    partner_realization_eq_for_arbitrary_final p.1 p.2.1 p.2.2 hm1 hm2⟩

/-- Exact formal counterpart of manuscript Theorem 1.

The witness has `d = d_out = 1`, two tokens, and two attention layers.
The equality is extensional equality of the complete realization functions;
the parameter topology is the ordinary product topology on `R x R x R`.
-/
-- APPENDIXTHEOREMONEBEGIN
theorem theorem1_counterexample :
    ∃ S : ℝ → ℝ,
      (∀ x, 0 < S x) ∧
      S 0 = 1 ∧
      Function.Injective S ∧
      Measurable S ∧
      Set.Nonempty parameterLocus ∧
      IsOpen parameterLocus ∧
      Dense parameterLocus ∧
      ∀ p ∈ parameterLocus,
        source p ≠ partner p ∧
        realizeDeep (t := 2) S (fixedDepthToDeep (partner p)) =
          realizeDeep S (fixedDepthToDeep (source p)) := by
  refine ⟨exoticNormalization, normalizer_admissible.1,
    normalizer_admissible.2.1, normalizer_admissible.2.2.1,
    normalizer_admissible.2.2.2, ?_⟩
  exact ⟨parameterLocus_nonempty_open_dense.1,
    parameterLocus_nonempty_open_dense.2.1,
    parameterLocus_nonempty_open_dense.2.2, explicit_partner⟩
-- APPENDIXTHEOREMONEEND

#print axioms normalizer_admissible
#print axioms normalizer_discontinuous_at_zero
#print axioms mass_domination
#print axioms first_layer_nonvanishing
#print axioms row_scaling_cancellation
#print axioms explicit_partner
#print axioms theorem1_counterexample
#print axioms NormalizedDeepAttention.deepNormalizedAttention_eq_virtual

end Neuroalgebraic.Submission.Theorem1
