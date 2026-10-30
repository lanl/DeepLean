module

public import DeepLean.Attention.Counterexamples
public import DeepLean.Attention.GeneralNormalization
public import DeepLean.Attention.Genericity
public import DeepLean.Attention.NormalizationClassCounterexample

/-!
# Submission-facing virtual deep-attention results

This file deliberately imports only the virtual normalized-attention
development used by the conjecture submission.  In particular it has no
dependency on the separate raw query/key/value gauge theory.
-/

@[expose] public section

namespace Neuroalgebraic.Submission.DeepAttentionVirtual

open NormalizedDeepAttention

/-- Admissibility of the counterexample normalizer, including the optional
Borel strengthening. -/
theorem exoticNormalization_admissible :
    Function.Injective exoticNormalization ∧
      exoticNormalization 0 = 1 ∧
      (∀ z, 0 < exoticNormalization z) ∧
      Measurable exoticNormalization :=
  ⟨exoticNormalization_injective, exoticNormalization_zero,
    exoticNormalization_pos, exoticNormalization_measurable⟩

/-- The four-scaling identity that is invisible after row normalization. -/
theorem exoticNormalization_four_scaling {z : ℝ} (hz : z ≠ 0) :
    exoticNormalization (4 * z) = exoticNormalization z / 4 :=
  exoticNormalization_four_mul hz

/-- Every source on the scalar coordinate-regular locus has a distinct
same-depth partner with the same realization on every input. -/
theorem sourceScope_openDense_failure :
    IsOpen {W : FixedDepthWeights 1 1 1 | CoordinateRegular 0 0 W} ∧
      Dense {W : FixedDepthWeights 1 1 1 | CoordinateRegular 0 0 W} ∧
      ∀ W : FixedDepthWeights 1 1 1, CoordinateRegular 0 0 W →
        ∃ W' : FixedDepthWeights 1 1 1,
          W ≠ W' ∧
          realizeDeep (t := 2) exoticNormalization (fixedDepthToDeep W) =
            realizeDeep exoticNormalization (fixedDepthToDeep W') :=
  ⟨isOpen_coordinateRegular 0 0, dense_coordinateRegular 0 0,
    exotic_coordinateRegular_full_locus_has_nontrivial_fiber⟩

/-- The full-rank skew boundary example from Appendix D has a distinct
same-function partner at two tokens. -/
theorem skewBoundary_nontrivialFiber :
    explicitSource ≠ explicitPartner ∧
      realizeTwo (t := 2) Real.exp explicitSource =
        realizeTwo Real.exp explicitPartner :=
  explicit_two_token_nontrivial_fiber

/-- Pointwise source-only rigidity for fixed positive-temperature softmax.
The target has no regularity hypothesis; equal tail lengths are exactly the
same-depth condition. -/
theorem softmax_pointwise_identifiable {d dOut t : ℕ}
    (τ : ℝ) (hτ : 0 < τ) (ht : 2 ≤ t)
    (W W' : DeepWeights d dOut) (hL : W.L ≠ 0)
    (hscore : ∀ M ∈ W.M₁ :: W.rest, M.transpose ≠ -M)
    (hdepth : W.rest.length = W'.rest.length)
    (hEq : realizeDeep (t := t) (temperatureNormalization τ) W =
      realizeDeep (temperatureNormalization τ) W') : W = W' :=
  realizeDeep_temperature_fiber_singleton τ hτ ht W W'
    ⟨hL, hscore⟩ hdepth hEq

/-- The certified extension from positive temperature to every nonzero linear
log-slope S(z) = exp(c*z). -/
theorem logAffine_pointwise_identifiable {d dOut t : ℕ}
    (S : ℝ → ℝ) (hS : LogAffineNormalization S) (ht : 2 ≤ t)
    (W W' : DeepWeights d dOut) (hL : W.L ≠ 0)
    (hscore : ∀ M ∈ W.M₁ :: W.rest, M.transpose ≠ -M)
    (hdepth : W.rest.length = W'.rest.length)
    (hEq : realizeDeep (t := t) S W = realizeDeep S W') : W = W' :=
  realizeDeep_logAffine_fiber_singleton S hS ht W W'
    ⟨hL, hscore⟩ hdepth hEq

/-- Sharp exponential endpoint: only scores in the proper source prefix must
be non-skew.  The terminal score is unrestricted, and the condition is
vacuous at depth one. -/
theorem exp_properPrefix_pointwise_identifiable {d dOut t : ℕ}
    (ht : 2 ≤ t) (W W' : DeepWeights d dOut) (hL : W.L ≠ 0)
    (hscore : ∀ M ∈ (W.M₁ :: W.rest).dropLast, M.transpose ≠ -M)
    (hdepth : W.rest.length = W'.rest.length)
    (hEq : realizeDeep (t := t) Real.exp W = realizeDeep Real.exp W') : W = W' :=
  realizeDeep_exp_fiber_singleton_properPrefix ht W W' hL hscore hdepth hEq

/-- Sharp positive-temperature endpoint with an unrestricted terminal source
score. -/
theorem temperature_properPrefix_pointwise_identifiable {d dOut t : ℕ}
    (τ : ℝ) (hτ : 0 < τ) (ht : 2 ≤ t)
    (W W' : DeepWeights d dOut) (hL : W.L ≠ 0)
    (hscore : ∀ M ∈ (W.M₁ :: W.rest).dropLast, M.transpose ≠ -M)
    (hdepth : W.rest.length = W'.rest.length)
    (hEq : realizeDeep (t := t) (temperatureNormalization τ) W =
      realizeDeep (temperatureNormalization τ) W') : W = W' :=
  realizeDeep_temperature_fiber_singleton_properPrefix τ hτ ht W W'
    hL hscore hdepth hEq

/-- Sharp log-affine endpoint with an unrestricted terminal source score. -/
theorem logAffine_properPrefix_pointwise_identifiable {d dOut t : ℕ}
    (S : ℝ → ℝ) (hS : LogAffineNormalization S) (ht : 2 ≤ t)
    (W W' : DeepWeights d dOut) (hL : W.L ≠ 0)
    (hscore : ∀ M ∈ (W.M₁ :: W.rest).dropLast, M.transpose ≠ -M)
    (hdepth : W.rest.length = W'.rest.length)
    (hEq : realizeDeep (t := t) S W = realizeDeep S W') : W = W' :=
  realizeDeep_logAffine_fiber_singleton_properPrefix S hS ht W W'
    hL hscore hdepth hEq

/-- Submission-facing fixed-depth generic theorem for ordinary softmax. -/
theorem softmax_coordinate_identifiable {d dOut k t : ℕ}
    (ht : 2 ≤ t) (i : Fin d) (o : Fin dOut)
    (W W' : FixedDepthWeights d dOut k) (hW : CoordinateRegular i o W)
    (hEq : realizeDeep (t := t) Real.exp (fixedDepthToDeep W) =
      realizeDeep Real.exp (fixedDepthToDeep W')) : W = W' :=
  coordinateRegular_full_fiber_singleton ht i o W W' hW hEq

/-- Fixed-depth coordinate theorem at every positive softmax temperature. -/
theorem temperature_coordinate_identifiable {d dOut k t : ℕ}
    (τ : ℝ) (hτ : 0 < τ) (ht : 2 ≤ t) (i : Fin d) (o : Fin dOut)
    (W W' : FixedDepthWeights d dOut k) (hW : CoordinateRegular i o W)
    (hEq : realizeDeep (t := t) (temperatureNormalization τ) (fixedDepthToDeep W) =
      realizeDeep (temperatureNormalization τ) (fixedDepthToDeep W')) : W = W' := by
  have hdeep := realizeDeep_temperature_fiber_singleton τ hτ ht
    (fixedDepthToDeep W) (fixedDepthToDeep W')
    (coordinateRegular_regularDeep i o W hW) (by simp [fixedDepthToDeep]) hEq
  have hfirst : W.1 = W'.1 := congrArg DeepWeights.M₁ hdeep
  have hrest : W.2.1 = W'.2.1 := by
    apply List.ofFn_injective
    exact congrArg DeepWeights.rest hdeep
  have hfinal : W.2.2 = W'.2.2 := congrArg DeepWeights.L hdeep
  exact Prod.ext hfirst (Prod.ext hrest hfinal)

/-- Fixed-depth coordinate theorem for every nonzero linear log-slope. -/
theorem logAffine_coordinate_identifiable {d dOut k t : ℕ}
    (S : ℝ → ℝ) (hS : LogAffineNormalization S)
    (ht : 2 ≤ t) (i : Fin d) (o : Fin dOut)
    (W W' : FixedDepthWeights d dOut k) (hW : CoordinateRegular i o W)
    (hEq : realizeDeep (t := t) S (fixedDepthToDeep W) =
      realizeDeep S (fixedDepthToDeep W')) : W = W' := by
  have hdeep := realizeDeep_logAffine_fiber_singleton S hS ht
    (fixedDepthToDeep W) (fixedDepthToDeep W')
    (coordinateRegular_regularDeep i o W hW) (by simp [fixedDepthToDeep]) hEq
  have hfirst : W.1 = W'.1 := congrArg DeepWeights.M₁ hdeep
  have hrest : W.2.1 = W'.2.1 := by
    apply List.ofFn_injective
    exact congrArg DeepWeights.rest hdeep
  have hfinal : W.2.2 = W'.2.2 := congrArg DeepWeights.L hdeep
  exact Prod.ext hfirst (Prod.ext hrest hfinal)

/-- Fixed-depth exponential theorem on the locus omitting the terminal score
diagonal. -/
theorem exp_properCoordinate_identifiable {d dOut k t : ℕ}
    (ht : 2 ≤ t) (i : Fin d) (o : Fin dOut)
    (W W' : FixedDepthWeights d dOut k) (hW : ProperCoordinateRegular i o W)
    (hEq : realizeDeep (t := t) Real.exp (fixedDepthToDeep W) =
      realizeDeep Real.exp (fixedDepthToDeep W')) : W = W' :=
  properCoordinateRegular_full_fiber_singleton ht i o W W' hW hEq

/-- Positive-temperature fixed-depth theorem on the sharp coordinate locus. -/
theorem temperature_properCoordinate_identifiable {d dOut k t : ℕ}
    (τ : ℝ) (hτ : 0 < τ) (ht : 2 ≤ t) (i : Fin d) (o : Fin dOut)
    (W W' : FixedDepthWeights d dOut k) (hW : ProperCoordinateRegular i o W)
    (hEq : realizeDeep (t := t) (temperatureNormalization τ) (fixedDepthToDeep W) =
      realizeDeep (temperatureNormalization τ) (fixedDepthToDeep W')) : W = W' := by
  have hdeep := realizeDeep_temperature_fiber_singleton_properPrefix τ hτ ht
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

/-- Log-affine fixed-depth theorem on the sharp coordinate locus. -/
theorem logAffine_properCoordinate_identifiable {d dOut k t : ℕ}
    (S : ℝ → ℝ) (hS : LogAffineNormalization S)
    (ht : 2 ≤ t) (i : Fin d) (o : Fin dOut)
    (W W' : FixedDepthWeights d dOut k) (hW : ProperCoordinateRegular i o W)
    (hEq : realizeDeep (t := t) S (fixedDepthToDeep W) =
      realizeDeep S (fixedDepthToDeep W')) : W = W' := by
  have hdeep := realizeDeep_logAffine_fiber_singleton_properPrefix S hS ht
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

/-- Complete fixed-depth virtual fiber for a chosen normalizer. -/
def FixedDepthFiberFor {d dOut k t : ℕ} (S : ℝ → ℝ)
    (W : FixedDepthWeights d dOut k) : Set (FixedDepthWeights d dOut k) :=
  {W' | realizeDeep (t := t) S (fixedDepthToDeep W') =
    realizeDeep S (fixedDepthToDeep W)}

/-- Literal singleton-fiber form at positive temperature. -/
theorem temperature_coordinate_fullFiber {d dOut k t : ℕ}
    (τ : ℝ) (hτ : 0 < τ) (ht : 2 ≤ t) (i : Fin d) (o : Fin dOut)
    (W : FixedDepthWeights d dOut k) (hW : CoordinateRegular i o W) :
    FixedDepthFiberFor (t := t) (temperatureNormalization τ) W = {W} := by
  ext W'
  change (realizeDeep (t := t) (temperatureNormalization τ) (fixedDepthToDeep W') =
    realizeDeep (temperatureNormalization τ) (fixedDepthToDeep W)) ↔ W' = W
  constructor
  · intro hEq
    exact (temperature_coordinate_identifiable τ hτ ht i o W W' hW hEq.symm).symm
  · rintro rfl
    rfl

/-- Literal singleton-fiber form for every nonzero linear log-slope. -/
theorem logAffine_coordinate_fullFiber {d dOut k t : ℕ}
    (S : ℝ → ℝ) (hS : LogAffineNormalization S)
    (ht : 2 ≤ t) (i : Fin d) (o : Fin dOut)
    (W : FixedDepthWeights d dOut k) (hW : CoordinateRegular i o W) :
    FixedDepthFiberFor (t := t) S W = {W} := by
  ext W'
  change (realizeDeep (t := t) S (fixedDepthToDeep W') =
    realizeDeep S (fixedDepthToDeep W)) ↔ W' = W
  constructor
  · intro hEq
    exact (logAffine_coordinate_identifiable S hS ht i o W W' hW hEq.symm).symm
  · rintro rfl
    rfl

/-- Literal positive-temperature singleton fiber on the sharp coordinate
locus. -/
theorem temperature_properCoordinate_fullFiber {d dOut k t : ℕ}
    (τ : ℝ) (hτ : 0 < τ) (ht : 2 ≤ t) (i : Fin d) (o : Fin dOut)
    (W : FixedDepthWeights d dOut k) (hW : ProperCoordinateRegular i o W) :
    FixedDepthFiberFor (t := t) (temperatureNormalization τ) W = {W} := by
  ext W'
  change (realizeDeep (t := t) (temperatureNormalization τ) (fixedDepthToDeep W') =
    realizeDeep (temperatureNormalization τ) (fixedDepthToDeep W)) ↔ W' = W
  constructor
  · intro hEq
    exact (temperature_properCoordinate_identifiable τ hτ ht i o W W' hW hEq.symm).symm
  · rintro rfl
    rfl

/-- Literal log-affine singleton fiber on the sharp coordinate locus. -/
theorem logAffine_properCoordinate_fullFiber {d dOut k t : ℕ}
    (S : ℝ → ℝ) (hS : LogAffineNormalization S)
    (ht : 2 ≤ t) (i : Fin d) (o : Fin dOut)
    (W : FixedDepthWeights d dOut k) (hW : ProperCoordinateRegular i o W) :
    FixedDepthFiberFor (t := t) S W = {W} := by
  ext W'
  change (realizeDeep (t := t) S (fixedDepthToDeep W') =
    realizeDeep S (fixedDepthToDeep W)) ↔ W' = W
  constructor
  · intro hEq
    exact (logAffine_properCoordinate_identifiable S hS ht i o W W' hW hEq.symm).symm
  · rintro rfl
    rfl

/-- The selected-coordinate source locus is literally nonempty, Euclidean
open, and dense. -/
theorem coordinateLocus_nonempty_open_dense {d dOut k : ℕ}
    (i : Fin d) (o : Fin dOut) :
    Set.Nonempty {W : FixedDepthWeights d dOut k | CoordinateRegular i o W} ∧
      IsOpen {W : FixedDepthWeights d dOut k | CoordinateRegular i o W} ∧
      Dense {W : FixedDepthWeights d dOut k | CoordinateRegular i o W} :=
  ⟨coordinateRegular_nonempty i o, isOpen_coordinateRegular i o,
    dense_coordinateRegular i o⟩

/-- The sharper selected-coordinate locus is nonempty, Euclidean open, and
dense. -/
theorem properCoordinateLocus_nonempty_open_dense {d dOut k : ℕ}
    (i : Fin d) (o : Fin dOut) :
    Set.Nonempty {W : FixedDepthWeights d dOut k | ProperCoordinateRegular i o W} ∧
      IsOpen {W : FixedDepthWeights d dOut k | ProperCoordinateRegular i o W} ∧
      Dense {W : FixedDepthWeights d dOut k | ProperCoordinateRegular i o W} :=
  ⟨properCoordinateRegular_nonempty i o, isOpen_properCoordinateRegular i o,
    dense_properCoordinateRegular i o⟩

/-- Explicit product equation for the sharp locus.  Its score factor is the
empty product at depth one. -/
theorem properCoordinateLocus_product_iff {d dOut k : ℕ}
    (i : Fin d) (o : Fin dOut) (W : FixedDepthWeights d dOut k) :
    ProperCoordinateRegular i o W ↔
      ((W.1 :: List.ofFn W.2.1).dropLast.map (fun M ↦ M i i)).prod *
        W.2.2 o i ≠ 0 :=
  properCoordinateRegular_iff_product_ne_zero i o W

/-- At depth one the sharp coordinate locus contains no score condition. -/
theorem properCoordinate_depthOne_iff_valueEntry {d dOut : ℕ}
    (i : Fin d) (o : Fin dOut) (W : FixedDepthWeights d dOut 0) :
    ProperCoordinateRegular i o W ↔ W.2.2 o i ≠ 0 :=
  properCoordinateRegular_iff i o W

#print axioms exoticNormalization_admissible
#print axioms sourceScope_openDense_failure
#print axioms skewBoundary_nontrivialFiber
#print axioms softmax_pointwise_identifiable
#print axioms logAffine_pointwise_identifiable
#print axioms exp_properPrefix_pointwise_identifiable
#print axioms temperature_properPrefix_pointwise_identifiable
#print axioms logAffine_properPrefix_pointwise_identifiable
#print axioms softmax_coordinate_identifiable
#print axioms temperature_coordinate_fullFiber
#print axioms logAffine_coordinate_fullFiber
#print axioms coordinateLocus_nonempty_open_dense
#print axioms exp_properCoordinate_identifiable
#print axioms temperature_properCoordinate_fullFiber
#print axioms logAffine_properCoordinate_fullFiber
#print axioms properCoordinateLocus_nonempty_open_dense
#print axioms properCoordinateLocus_product_iff
#print axioms properCoordinate_depthOne_iff_valueEntry

end Neuroalgebraic.Submission.DeepAttentionVirtual
