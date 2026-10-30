module

public import DeepLean.Attention.Neuroalgebraic.Attention

/-!
# Normalized deep attention in virtual coordinates

This file gives the column-token, virtual-weight API used by Henry--Marchetti--Kohn,
Conjecture 3.10.  All score matrices act on the original embedding space.  A canonical
virtual layer has identity value map; the final virtual value product `L` is applied only
after all canonical layers.
-/

@[expose] public section

namespace NormalizedDeepAttention

/-- Depth-two virtual weights `(M₁,M₂,L)`. -/
structure TwoLayerWeights (d dOut : ℕ) where
  M₁ : Matrix (Fin d) (Fin d) ℝ
  M₂ : Matrix (Fin d) (Fin d) ℝ
  L : Matrix (Fin dOut) (Fin d) ℝ

/-- The normalized depth-two realization in virtual coordinates. -/
noncomputable def realizeTwo {d dOut t : ℕ} (S : ℝ → ℝ)
    (W : TwoLayerWeights d dOut) :
    Matrix (Fin d) (Fin t) ℝ → Matrix (Fin dOut) (Fin t) ℝ :=
  fun X ↦ W.L * layer S W.M₂ (layer S W.M₁ X)

theorem layer_constantTokenMatrix {d t : ℕ} (S : ℝ → ℝ)
    (hSpos : ∀ z, 0 < S z) (M : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) (ht : 0 < t) :
    layer (t := t) S M (constantTokenMatrix (t := t) x) =
      constantTokenMatrix (t := t) x := by
  change normalizedAttention (t := t) S M 1 (constantTokenMatrix (t := t) x) =
    fun r (_ : Fin t) ↦ x r
  simpa using
    normalizedAttention_constantTokenMatrix S hSpos M
      (1 : Matrix (Fin d) (Fin d) ℝ) x ht

theorem realizeTwo_constantTokenMatrix {d dOut t : ℕ} (S : ℝ → ℝ)
    (hSpos : ∀ z, 0 < S z) (W : TwoLayerWeights d dOut)
    (x : Fin d → ℝ) (ht : 0 < t) :
    realizeTwo (t := t) S W (constantTokenMatrix (t := t) x) =
      constantTokenMatrix (t := t) (W.L.mulVec x) := by
  rw [realizeTwo, layer_constantTokenMatrix S hSpos W.M₁ x ht,
    layer_constantTokenMatrix S hSpos W.M₂ x ht]
  ext r i
  simp [constantTokenMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- Repeated-token probes recover the final virtual value product `L` from every
nonempty depth-two normalized realization, without rank hypotheses. -/
theorem finalValue_identifiable {d dOut t : ℕ} (S : ℝ → ℝ)
    (hSpos : ∀ z, 0 < S z) (W W' : TwoLayerWeights d dOut)
    (ht : 0 < t) (hEq : realizeTwo (t := t) S W = realizeTwo S W') :
    W.L = W'.L := by
  ext r c
  let x : Fin d → ℝ := Pi.single c 1
  have h := congrArg (fun f ↦ f (constantTokenMatrix (t := t) x)) hEq
  rw [realizeTwo_constantTokenMatrix S hSpos W x ht,
    realizeTwo_constantTokenMatrix S hSpos W' x ht] at h
  have he := congrFun (congrFun h r) (⟨0, ht⟩ : Fin t)
  simpa [constantTokenMatrix, x, Matrix.mulVec, Pi.single_apply] using he

end NormalizedDeepAttention
