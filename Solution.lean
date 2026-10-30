module

public import DeepLean

/-!
# Proved deep-attention solution

These declarations have the same names and statements as `Challenge.lean`.
Their proofs use the DeepLean library; the generic clause explicitly includes
the source-regularity containment stated in the manuscript.
-/

@[expose] public section

open NormalizedDeepAttention
open Neuroalgebraic.Submission.Theorem1
open Neuroalgebraic.Submission.Theorem2

namespace DeepLean.Attention

/-- Manuscript Theorem 1: a positive, normalized, injective Borel normalizer,
discontinuous at zero, has explicit distinct scalar depth-two partners on a
nonempty open dense locus.
The realizations agree on every real `1 × 2` input matrix. -/
-- APPENDIXTHEOREMONEBEGIN
theorem normalizer_counterexample :
    ∃ S : ℝ → ℝ,
      (∀ x, 0 < S x) ∧
      S 0 = 1 ∧
      Function.Injective S ∧
      Measurable S ∧
      ¬ ContinuousAt S 0 ∧
      Set.Nonempty parameterLocus ∧
      IsOpen parameterLocus ∧
      Dense parameterLocus ∧
      ∀ p ∈ parameterLocus,
        source p ≠ partner p ∧
        realizeDeep (t := 2) S (fixedDepthToDeep (partner p)) =
          realizeDeep S (fixedDepthToDeep (source p)) :=
  ⟨exoticNormalization, normalizer_admissible.1,
    normalizer_admissible.2.1, normalizer_admissible.2.2.1,
    normalizer_admissible.2.2.2, normalizer_discontinuous_at_zero,
    parameterLocus_nonempty_open_dense.1,
    parameterLocus_nonempty_open_dense.2.1,
    parameterLocus_nonempty_open_dense.2.2, explicit_partner⟩
-- APPENDIXTHEOREMONEEND

/-- Manuscript Theorem 2, pointwise clause: positive-temperature softmax
identifies every source with nonzero final map and non-skew proper prefix
among all parameters of the same positive depth. The terminal source score
and the competing parameter have no regularity requirement. -/
-- APPENDIXTHEOREMTWOPOINTWISEBEGIN
theorem softmax_identifiability {d dOut t : ℕ}
    (τ : ℝ) (hτ : 0 < τ) (ht : 2 ≤ t)
    (W W' : DeepWeights d dOut) (hL : W.L ≠ 0)
    (hscore : ∀ M ∈ (W.M₁ :: W.rest).dropLast, M.transpose ≠ -M)
    (hdepth : W.rest.length = W'.rest.length)
    (hEq : realizeDeep (t := t) (temperatureNormalization τ) W =
      realizeDeep (temperatureNormalization τ) W') : W = W' :=
  Neuroalgebraic.Submission.Theorem2.theorem2_softmax_identifiability
    τ hτ ht W W' hL hscore hdepth hEq
-- APPENDIXTHEOREMTWOPOINTWISEEND

/-- Manuscript Theorem 2, generic clause: the explicit coordinate locus is
nonempty, Euclidean open and dense, lies in the source-regular locus, and has
complete singleton fibers. The depth is `k + 1`; at depth one the proper
prefix condition is empty. -/
-- APPENDIXTHEOREMTWOGENERICBEGIN
theorem softmax_generic_identifiability {d dOut k t : ℕ}
    (τ : ℝ) (hτ : 0 < τ) (ht : 2 ≤ t) (i : Fin d) (o : Fin dOut) :
    Set.Nonempty {W : FixedDepthWeights d dOut k | ProperCoordinateRegular i o W} ∧
      IsOpen {W : FixedDepthWeights d dOut k | ProperCoordinateRegular i o W} ∧
      Dense {W : FixedDepthWeights d dOut k | ProperCoordinateRegular i o W} ∧
      ∀ W : FixedDepthWeights d dOut k, ProperCoordinateRegular i o W →
        ((fixedDepthToDeep W).L ≠ 0 ∧
          ∀ M ∈ ((fixedDepthToDeep W).M₁ :: (fixedDepthToDeep W).rest).dropLast,
            M.transpose ≠ -M) ∧
        FixedDepthFiberFor (t := t) τ W = {W} :=
  ⟨properCoordinateRegular_nonempty i o,
    isOpen_properCoordinateRegular i o,
    dense_properCoordinateRegular i o,
    fun W hW ↦ ⟨properCoordinateRegular_properDeep i o W hW,
      Neuroalgebraic.Submission.Theorem2.theorem2_coordinate_fullFiber
        τ hτ ht i o W hW⟩⟩
-- APPENDIXTHEOREMTWOGENERICEND

end DeepLean.Attention
