module

public import Mathlib

/-!
# Definitions for the two deep-attention theorems

This module is the canonical definition interface for the proof library.
`Challenge.lean` repeats its definitions verbatim so that its only import is
Mathlib. `scripts/check-attention-interface.py` checks that the copies agree.
Tokens are columns; all score matrices act on the original embedding space.
Existing declaration namespaces are retained from the original development.
-/

@[expose] public section

/-- The bilinear attention score `x_iᵀ A x_j` used in Equation (15). -/
def attentionScore {d t : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin t) ℝ) (i j : Fin t) : ℝ :=
  dotProduct (X.col i) (A.mulVec (X.col j))

/-- Column-token normalized attention: for each query column `i`, average the
value-transformed columns `V * X` with weights `S (x_iᵀ A x_j)` divided by
their row sum. This is Equation (15) of the background attention paper. -/
noncomputable def normalizedAttention {d d' t : ℕ} (S : ℝ → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) (V : Matrix (Fin d') (Fin d) ℝ) :
    Matrix (Fin d) (Fin t) ℝ → Matrix (Fin d') (Fin t) ℝ :=
  fun X r i ↦
    (∑ j : Fin t, S (attentionScore A X i j) * (V.mulVec (X.col j)) r) /
      ∑ k : Fin t, S (attentionScore A X i k)

namespace NormalizedDeepAttention

/-- One canonical normalized layer in virtual coordinates: normalized attention
with score matrix `M` and identity value map on the embedding space. -/
noncomputable def layer {d t : ℕ} (S : ℝ → ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin t) ℝ → Matrix (Fin d) (Fin t) ℝ :=
  normalizedAttention S M 1

/-- A real bilinear score matrix on the original `d`-dimensional embedding space. -/
abbrev ScoreMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- Repeated canonical normalized layers, ordered from input to output. -/
noncomputable def applyLayers {d t : ℕ} (S : ℝ → ℝ) :
    List (ScoreMatrix d) → Matrix (Fin d) (Fin t) ℝ → Matrix (Fin d) (Fin t) ℝ
  | [], X => X
  | M :: Ms, X => applyLayers S Ms (layer S M X)

/-- Virtual weights at arbitrary positive depth. -/
structure DeepWeights (d dOut : ℕ) where
  M₁ : ScoreMatrix d
  rest : List (ScoreMatrix d)
  L : Matrix (Fin dOut) (Fin d) ℝ

/-- The complete virtual realization: apply the first score and remaining
canonical layers in order, then multiply by the final value matrix. -/
noncomputable def realizeDeep {d dOut t : ℕ} (S : ℝ → ℝ)
    (W : DeepWeights d dOut) :
    Matrix (Fin d) (Fin t) ℝ → Matrix (Fin dOut) (Fin t) ℝ :=
  fun X ↦ W.L * applyLayers S W.rest (layer S W.M₁ X)

/-- Parameters of positive depth `k + 1`, represented as a finite Euclidean
product: first score, `k` further scores, and the final value matrix. -/
abbrev FixedDepthWeights (d dOut k : ℕ) :=
  ScoreMatrix d × ((Fin k → ScoreMatrix d) × Matrix (Fin dOut) (Fin d) ℝ)

/-- Convert finite-product parameters to first-score/list parameters in the
same input-to-output order. This preserves the final value matrix. -/
def fixedDepthToDeep {d dOut k : ℕ} (W : FixedDepthWeights d dOut k) :
    DeepWeights d dOut :=
  ⟨W.1, List.ofFn W.2.1, W.2.2⟩

/-- Sharpened coordinate locus: the selected diagonal is nonzero only for the
proper score prefix, while the selected final-value entry is nonzero.  Thus
at depth one there is no score condition. -/
def ProperCoordinateRegular {d dOut k : ℕ} (i : Fin d) (o : Fin dOut)
    (W : FixedDepthWeights d dOut k) : Prop :=
  (∀ M ∈ (W.1 :: List.ofFn W.2.1).dropLast, M i i ≠ 0) ∧ W.2.2 o i ≠ 0

/-- The exact score regularity used by layer peeling: every score except the
last one is non-skew.  In particular, this is vacuous for an empty or
singleton score list. -/
def ProperPrefixNonSkew {d : ℕ} (Ms : List (ScoreMatrix d)) : Prop :=
  ∀ M ∈ Ms.dropLast, M.transpose ≠ -M

/-- Fixed-temperature exponential normalization. -/
noncomputable def temperatureNormalization (τ z : ℝ) : ℝ := Real.exp (z / τ)

/-- A scalar score matrix, used to exhibit the smallest deep counterexample. -/
def scalarScore (c : ℝ) : ScoreMatrix 1 := fun _ _ ↦ c

/-- The scalar coordinate chart for the source-scope failure locus. -/
def exoticFamilySource (m₁ m₂ l : ℝ) : FixedDepthWeights 1 1 1 :=
  (scalarScore m₁, (fun _ ↦ scalarScore m₂, scalarScore l))

/-- The fiber partner changes only the second virtual score. -/
def exoticFamilyPartner (m₁ m₂ l : ℝ) : FixedDepthWeights 1 1 1 :=
  (scalarScore m₁, (fun _ ↦ scalarScore (4 * m₂), scalarScore l))

end NormalizedDeepAttention

namespace Neuroalgebraic.Submission.Theorem1

open NormalizedDeepAttention

/-- The manuscript's scalar depth-two parameter triple `(m1,m2,l)`. -/
abbrev ScalarDepthTwoParameters := ℝ × ℝ × ℝ

/-- The exact parameter set `{(m1,m2,l) | m1*m2*l != 0}` in Theorem 1. -/
def parameterLocus : Set ScalarDepthTwoParameters :=
  {p | p.1 * p.2.1 * p.2.2 ≠ 0}

/-- The virtual source `(m1,m2,l)` in the fixed-depth formal model. -/
def source (p : ScalarDepthTwoParameters) : FixedDepthWeights 1 1 1 :=
  exoticFamilySource p.1 p.2.1 p.2.2

/-- The explicit partner `(m1,4*m2,l)`. -/
def partner (p : ScalarDepthTwoParameters) : FixedDepthWeights 1 1 1 :=
  exoticFamilyPartner p.1 p.2.1 p.2.2

end Neuroalgebraic.Submission.Theorem1

namespace Neuroalgebraic.Submission.Theorem2

open NormalizedDeepAttention

/-- The manuscript's complete fixed-depth fiber for positive-temperature
softmax, written literally as a set of virtual parameters. -/
def FixedDepthFiberFor {d dOut k t : ℕ} (τ : ℝ)
    (W : FixedDepthWeights d dOut k) : Set (FixedDepthWeights d dOut k) :=
  {W' | realizeDeep (t := t) (temperatureNormalization τ) (fixedDepthToDeep W') =
    realizeDeep (temperatureNormalization τ) (fixedDepthToDeep W)}

end Neuroalgebraic.Submission.Theorem2
