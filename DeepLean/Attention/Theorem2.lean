module

public import DeepLean.Attention.GeneralNormalization

/-!
# Manuscript Theorem 2: positive-temperature softmax identifiability

This is the reviewer-facing entry point for Theorem 2 of `submission.tex`.
It exposes the exact pointwise theorem and the explicit nonempty, Euclidean
open-dense coordinate locus.  The target parameter has no regularity premise;
the terminal source score is unrestricted, including at depth one.
-/

@[expose] public section

namespace Neuroalgebraic.Submission.Theorem2

open NormalizedDeepAttention

/-- Exact pointwise identifiability clause of manuscript Theorem 2.

`W.rest` contains the scores after `W.M₁`, so equal tail lengths express equal
positive depth.  Only the proper source prefix `(M₁,...,M_{ell-1})` is assumed
non-skew; no hypothesis is imposed on `W'` or on the terminal source score. -/
-- APPENDIXTHEOREMTWOPOINTWISEBEGIN
theorem theorem2_softmax_identifiability {d dOut t : ℕ}
    (τ : ℝ) (hτ : 0 < τ) (ht : 2 ≤ t)
    (W W' : DeepWeights d dOut) (hL : W.L ≠ 0)
    (hscore : ∀ M ∈ (W.M₁ :: W.rest).dropLast, M.transpose ≠ -M)
    (hdepth : W.rest.length = W'.rest.length)
    (hEq : realizeDeep (t := t) (temperatureNormalization τ) W =
      realizeDeep (temperatureNormalization τ) W') : W = W' :=
  realizeDeep_temperature_fiber_singleton_properPrefix
    τ hτ ht W W' hL hscore hdepth hEq
-- APPENDIXTHEOREMTWOPOINTWISEEND

private theorem properCoordinate_identifiable {d dOut k t : ℕ}
    (τ : ℝ) (hτ : 0 < τ) (ht : 2 ≤ t) (i : Fin d) (o : Fin dOut)
    (W W' : FixedDepthWeights d dOut k) (hW : ProperCoordinateRegular i o W)
    (hEq : realizeDeep (t := t) (temperatureNormalization τ) (fixedDepthToDeep W) =
      realizeDeep (temperatureNormalization τ) (fixedDepthToDeep W')) : W = W' := by
  have hdeep := theorem2_softmax_identifiability τ hτ ht
    (fixedDepthToDeep W) (fixedDepthToDeep W')
    (properCoordinateRegular_properDeep i o W hW).1
    (properCoordinateRegular_properDeep i o W hW).2
    (by simp [fixedDepthToDeep]) hEq
  have hfirst : W.1 = W'.1 := congrArg DeepWeights.M₁ hdeep
  have hrest : W.2.1 = W'.2.1 := by
    apply List.ofFn_injective
    exact congrArg DeepWeights.rest hdeep
  have hfinal : W.2.2 = W'.2.2 := congrArg DeepWeights.L hdeep
  exact Prod.ext hfirst (Prod.ext hrest hfinal)

/-- Every source on the sharp coordinate locus has a literal singleton
complete fiber. -/
theorem theorem2_coordinate_fullFiber {d dOut k t : ℕ}
    (τ : ℝ) (hτ : 0 < τ) (ht : 2 ≤ t) (i : Fin d) (o : Fin dOut)
    (W : FixedDepthWeights d dOut k) (hW : ProperCoordinateRegular i o W) :
    FixedDepthFiberFor (t := t) τ W = {W} := by
  ext W'
  change (realizeDeep (t := t) (temperatureNormalization τ) (fixedDepthToDeep W') =
    realizeDeep (temperatureNormalization τ) (fixedDepthToDeep W)) ↔ W' = W
  constructor
  · intro hEq
    exact (properCoordinate_identifiable τ hτ ht i o W W' hW hEq.symm).symm
  · rintro rfl
    rfl

/-- Exact generic clause of manuscript Theorem 2: the displayed coordinate
locus is nonempty, Euclidean open and dense, and all its fibers are
singletons. -/
-- APPENDIXTHEOREMTWOGENERICBEGIN
theorem theorem2_openDense_coordinate_fibers {d dOut k t : ℕ}
    (τ : ℝ) (hτ : 0 < τ) (ht : 2 ≤ t) (i : Fin d) (o : Fin dOut) :
    Set.Nonempty {W : FixedDepthWeights d dOut k | ProperCoordinateRegular i o W} ∧
      IsOpen {W : FixedDepthWeights d dOut k | ProperCoordinateRegular i o W} ∧
      Dense {W : FixedDepthWeights d dOut k | ProperCoordinateRegular i o W} ∧
      ∀ W : FixedDepthWeights d dOut k, ProperCoordinateRegular i o W →
        FixedDepthFiberFor (t := t) τ W = {W} := by
  exact ⟨properCoordinateRegular_nonempty i o,
    isOpen_properCoordinateRegular i o,
    dense_properCoordinateRegular i o,
    theorem2_coordinate_fullFiber τ hτ ht i o⟩
-- APPENDIXTHEOREMTWOGENERICEND

-- The two manuscript proof lemmas are implemented by these arbitrary-token
-- quadratic/cubic and unequal-suffix limit theorems in `WeightedHierarchy`.
#print axioms NormalizedDeepAttention.tendsto_weightedRun_next_comparison
#print axioms NormalizedDeepAttention.tendsto_weightedRun_preserves_common_comparison
#print axioms theorem2_softmax_identifiability
#print axioms theorem2_coordinate_fullFiber
#print axioms theorem2_openDense_coordinate_fibers

end Neuroalgebraic.Submission.Theorem2
