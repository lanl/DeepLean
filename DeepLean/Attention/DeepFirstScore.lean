module

public import DeepLean.Attention.ThreeToken

/-! # Arbitrary-depth recovery of the first virtual score -/

@[expose] public section

namespace NormalizedDeepAttention

theorem applyLayers_constantTokenMatrix {d t : ℕ} (S : ℝ → ℝ)
    (hSpos : ∀ z, 0 < S z) (Ms : List (ScoreMatrix d))
    (x : Fin d → ℝ) (ht : 0 < t) :
    applyLayers (t := t) S Ms (constantTokenMatrix (t := t) x) =
      constantTokenMatrix (t := t) x := by
  induction Ms with
  | nil => rfl
  | cons M Ms ih =>
      rw [applyLayers, layer_constantTokenMatrix S hSpos M x ht, ih]

theorem realizeDeep_constantTokenMatrix {d dOut t : ℕ} (S : ℝ → ℝ)
    (hSpos : ∀ z, 0 < S z) (W : DeepWeights d dOut)
    (x : Fin d → ℝ) (ht : 0 < t) :
    realizeDeep (t := t) S W (constantTokenMatrix (t := t) x) =
      constantTokenMatrix (t := t) (W.L.mulVec x) := by
  rw [realizeDeep, layer_constantTokenMatrix S hSpos W.M₁ x ht,
    applyLayers_constantTokenMatrix S hSpos W.rest x ht]
  ext r i
  simp [constantTokenMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem deepFinalValue_identifiable {d dOut t : ℕ} (S : ℝ → ℝ)
    (hSpos : ∀ z, 0 < S z) (W W' : DeepWeights d dOut) (ht : 0 < t)
    (hEq : realizeDeep (t := t) S W = realizeDeep S W') :
    W.L = W'.L := by
  ext r c
  let x : Fin d → ℝ := Pi.single c 1
  have h := congrArg (fun f ↦ f (constantTokenMatrix (t := t) x)) hEq
  rw [realizeDeep_constantTokenMatrix S hSpos W x ht,
    realizeDeep_constantTokenMatrix S hSpos W' x ht] at h
  have he := congrFun (congrFun h r) (⟨0, ht⟩ : Fin t)
  simpa [constantTokenMatrix, x, Matrix.mulVec, Pi.single_apply] using he

private theorem tendsto_value_of_deep_quadraticJet
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

theorem applyLayers_exp_preserves_two_common_quadraticJet {d : ℕ}
    (Ms : List (ScoreMatrix d))
    (Y : ℝ → Matrix (Fin d) (Fin 2) ℝ) (x v : Fin d → ℝ)
    (hY : ∀ r i, Filter.Tendsto (fun ε ↦ Y ε r i)
      (nhdsWithin 0 {0}ᶜ) (nhds (x r)))
    (hjet : ∀ r i, Filter.Tendsto (fun ε ↦ (Y ε r i - x r) / ε ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (v r))) (r : Fin d) (i : Fin 2) :
    Filter.Tendsto
      (fun ε ↦ (applyLayers Real.exp Ms (Y ε) r i - x r) / ε ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (v r)) := by
  induction Ms generalizing Y with
  | nil => simpa [applyLayers] using hjet r i
  | cons M Ms ih =>
      let Z : ℝ → Matrix (Fin d) (Fin 2) ℝ := fun ε ↦ layer Real.exp M (Y ε)
      have hZjet (c : Fin d) (j : Fin 2) : Filter.Tendsto
          (fun ε ↦ (Z ε c j - x c) / ε ^ 2)
          (nhdsWithin 0 {0}ᶜ) (nhds (v c)) :=
        layer_exp_preserves_common_quadraticJet M Y x v hY hjet c j
      have hZ (c : Fin d) (j : Fin 2) : Filter.Tendsto
          (fun ε ↦ Z ε c j) (nhdsWithin 0 {0}ᶜ) (nhds (x c)) :=
        tendsto_value_of_deep_quadraticJet _ _ _ (hZjet c j)
      simpa only [applyLayers, Z] using ih Z hZ hZjet

theorem applyLayers_exp_preserves_three_common_quadraticJet {d : ℕ}
    (Ms : List (ScoreMatrix d))
    (Y : ℝ → Matrix (Fin d) (Fin 3) ℝ) (x v : Fin d → ℝ)
    (hpattern : ∀ ε, ∃ y₀ y₁, Y ε = triplePattern y₀ y₁)
    (hY : ∀ r i, Filter.Tendsto (fun ε ↦ Y ε r i)
      (nhdsWithin 0 {0}ᶜ) (nhds (x r)))
    (hjet : ∀ r i, Filter.Tendsto (fun ε ↦ (Y ε r i - x r) / ε ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (v r))) (r : Fin d) (i : Fin 3) :
    Filter.Tendsto
      (fun ε ↦ (applyLayers Real.exp Ms (Y ε) r i - x r) / ε ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (v r)) := by
  induction Ms generalizing Y with
  | nil => simpa [applyLayers] using hjet r i
  | cons M Ms ih =>
      let Z : ℝ → Matrix (Fin d) (Fin 3) ℝ := fun ε ↦ layer Real.exp M (Y ε)
      have hZjet (c : Fin d) (j : Fin 3) : Filter.Tendsto
          (fun ε ↦ (Z ε c j - x c) / ε ^ 2)
          (nhdsWithin 0 {0}ᶜ) (nhds (v c)) :=
        layer_exp_preserves_triple_common_quadraticJet M Y x v hpattern hY hjet c j
      have hZ (c : Fin d) (j : Fin 3) : Filter.Tendsto
          (fun ε ↦ Z ε c j) (nhdsWithin 0 {0}ᶜ) (nhds (x c)) :=
        tendsto_value_of_deep_quadraticJet _ _ _ (hZjet c j)
      have hZpattern (ε : ℝ) : ∃ z₀ z₁, Z ε = triplePattern z₀ z₁ := by
        obtain ⟨y₀, y₁, hy⟩ := hpattern ε
        dsimp [Z]
        rw [hy]
        exact layer_exp_triplePattern_is_triplePattern M y₀ y₁
      simpa only [applyLayers, Z] using ih Z hZpattern hZ hZjet

theorem realizeDeep_exp_two_first_quadraticJet {d dOut : ℕ}
    (W : DeepWeights d dOut) (x u : Fin d → ℝ) (r : Fin dOut) (i : Fin 2) :
    Filter.Tendsto
      (fun ε ↦ (realizeDeep Real.exp W (symmetricPerturbation x u ε) r i -
        (W.L.mulVec x) r) / ε ^ 2)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (dotProduct x (W.M₁.mulVec u) * (W.L.mulVec u) r)) := by
  let Y : ℝ → Matrix (Fin d) (Fin 2) ℝ :=
    fun ε ↦ layer Real.exp W.M₁ (symmetricPerturbation x u ε)
  let v : Fin d → ℝ := fun c ↦ dotProduct x (W.M₁.mulVec u) * u c
  have hYjet (c : Fin d) (j : Fin 2) : Filter.Tendsto
      (fun ε ↦ (Y ε c j - x c) / ε ^ 2) (nhdsWithin 0 {0}ᶜ) (nhds (v c)) :=
    layer_exp_symmetricPerturbation_quadraticJet W.M₁ x u c j
  have hY (c : Fin d) (j : Fin 2) : Filter.Tendsto (fun ε ↦ Y ε c j)
      (nhdsWithin 0 {0}ᶜ) (nhds (x c)) :=
    tendsto_value_of_deep_quadraticJet _ _ _ (hYjet c j)
  have hZjet (c : Fin d) (j : Fin 2) :=
    applyLayers_exp_preserves_two_common_quadraticJet W.rest Y x v hY hYjet c j
  have hsum : Filter.Tendsto
      (fun ε ↦ ∑ c : Fin d, W.L r c *
        ((applyLayers Real.exp W.rest (Y ε) c i - x c) / ε ^ 2))
      (nhdsWithin 0 {0}ᶜ) (nhds (∑ c : Fin d, W.L r c * v c)) := by
    apply tendsto_finsetSum Finset.univ
    intro c _
    exact tendsto_const_nhds.mul (hZjet c i)
  have heq : (fun ε ↦ (realizeDeep Real.exp W (symmetricPerturbation x u ε) r i -
      (W.L.mulVec x) r) / ε ^ 2) =ᶠ[nhdsWithin 0 {0}ᶜ]
      fun ε ↦ ∑ c : Fin d, W.L r c *
        ((applyLayers Real.exp W.rest (Y ε) c i - x c) / ε ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : ε ≠ 0 := hε
    have hpow : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε0
    simp only [realizeDeep, Matrix.mul_apply, Matrix.mulVec, dotProduct, Y]
    apply (div_eq_iff hpow).2
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    field_simp [hε0, hpow]
  apply Filter.Tendsto.congr' heq.symm
  have hvsum : (∑ c : Fin d, W.L r c * v c) =
      dotProduct x (W.M₁.mulVec u) * (W.L.mulVec u) r := by
    change (∑ c : Fin d, W.L r c * (dotProduct x (W.M₁.mulVec u) * u c)) =
      dotProduct x (W.M₁.mulVec u) * ∑ c : Fin d, W.L r c * u c
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  simpa [hvsum] using hsum

/-- At any positive depth, two-token functional equality recovers the first virtual
score matrix whenever the final value product is nonzero. -/
theorem deepFirstScore_identifiable_exp_two {d dOut : ℕ}
    (W W' : DeepWeights d dOut) (hL : W.L ≠ 0)
    (hEq : realizeDeep (t := 2) Real.exp W = realizeDeep Real.exp W') :
    W.M₁ = W'.M₁ := by
  have hLL := deepFinalValue_identifiable Real.exp Real.exp_pos W W' (by omega) hEq
  have hprobe (x u : Fin d → ℝ) :
      (dotProduct x (W.M₁.mulVec u)) • W.L.mulVec u =
        (dotProduct x (W'.M₁.mulVec u)) • W.L.mulVec u := by
    funext r
    have hl := realizeDeep_exp_two_first_quadraticJet W x u r 0
    have hr := realizeDeep_exp_two_first_quadraticJet W' x u r 0
    rw [← hLL] at hr
    have hf : (fun ε ↦ (realizeDeep Real.exp W (symmetricPerturbation x u ε) r 0 -
        (W.L.mulVec x) r) / ε ^ 2) = fun ε ↦
      (realizeDeep Real.exp W' (symmetricPerturbation x u ε) r 0 -
        (W.L.mulVec x) r) / ε ^ 2 := by
      funext ε
      rw [congrFun hEq (symmetricPerturbation x u ε)]
    rw [← hf] at hr
    simpa using tendsto_nhds_unique hl hr
  exact matrix_eq_of_rankOne_jets_eq W.L W.M₁ W'.M₁ hL hprobe

theorem realizeDeep_exp_three_first_quadraticJet {d dOut : ℕ}
    (W : DeepWeights d dOut) (x u : Fin d → ℝ) (r : Fin dOut) (i : Fin 3) :
    Filter.Tendsto
      (fun ε ↦ (realizeDeep Real.exp W (tripleCenteredPerturbation x u ε) r i -
        (W.L.mulVec x) r) / ε ^ 2)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (2 * dotProduct x (W.M₁.mulVec u) * (W.L.mulVec u) r)) := by
  let Y : ℝ → Matrix (Fin d) (Fin 3) ℝ :=
    fun ε ↦ layer Real.exp W.M₁ (tripleCenteredPerturbation x u ε)
  let v : Fin d → ℝ := fun c ↦ 2 * dotProduct x (W.M₁.mulVec u) * u c
  have hYjet (c : Fin d) (j : Fin 3) : Filter.Tendsto
      (fun ε ↦ (Y ε c j - x c) / ε ^ 2) (nhdsWithin 0 {0}ᶜ) (nhds (v c)) :=
    layer_exp_tripleCenteredPerturbation_quadraticJet W.M₁ x u c j
  have hY (c : Fin d) (j : Fin 3) : Filter.Tendsto (fun ε ↦ Y ε c j)
      (nhdsWithin 0 {0}ᶜ) (nhds (x c)) :=
    tendsto_value_of_deep_quadraticJet _ _ _ (hYjet c j)
  have hpattern (ε : ℝ) : ∃ y₀ y₁, Y ε = triplePattern y₀ y₁ :=
    layer_exp_triplePattern_is_triplePattern W.M₁ _ _
  have hZjet (c : Fin d) (j : Fin 3) :=
    applyLayers_exp_preserves_three_common_quadraticJet W.rest Y x v
      hpattern hY hYjet c j
  have hsum : Filter.Tendsto
      (fun ε ↦ ∑ c : Fin d, W.L r c *
        ((applyLayers Real.exp W.rest (Y ε) c i - x c) / ε ^ 2))
      (nhdsWithin 0 {0}ᶜ) (nhds (∑ c : Fin d, W.L r c * v c)) := by
    apply tendsto_finsetSum Finset.univ
    intro c _
    exact tendsto_const_nhds.mul (hZjet c i)
  have heq : (fun ε ↦
      (realizeDeep Real.exp W (tripleCenteredPerturbation x u ε) r i -
        (W.L.mulVec x) r) / ε ^ 2) =ᶠ[nhdsWithin 0 {0}ᶜ]
      fun ε ↦ ∑ c : Fin d, W.L r c *
        ((applyLayers Real.exp W.rest (Y ε) c i - x c) / ε ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : ε ≠ 0 := hε
    have hpow : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε0
    simp only [realizeDeep, Matrix.mul_apply, Matrix.mulVec, dotProduct, Y]
    apply (div_eq_iff hpow).2
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    field_simp [hε0, hpow]
  apply Filter.Tendsto.congr' heq.symm
  have hvsum : (∑ c : Fin d, W.L r c * v c) =
      2 * dotProduct x (W.M₁.mulVec u) * (W.L.mulVec u) r := by
    change (∑ c : Fin d, W.L r c *
        (2 * dotProduct x (W.M₁.mulVec u) * u c)) =
      2 * dotProduct x (W.M₁.mulVec u) * ∑ c : Fin d, W.L r c * u c
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  simpa [hvsum] using hsum

/-- At any positive depth, three-token functional equality recovers the first virtual
score matrix whenever the final value product is nonzero. -/
theorem deepFirstScore_identifiable_exp_three {d dOut : ℕ}
    (W W' : DeepWeights d dOut) (hL : W.L ≠ 0)
    (hEq : realizeDeep (t := 3) Real.exp W = realizeDeep Real.exp W') :
    W.M₁ = W'.M₁ := by
  have hLL := deepFinalValue_identifiable Real.exp Real.exp_pos W W' (by omega) hEq
  have hprobe (x u : Fin d → ℝ) :
      (dotProduct x (W.M₁.mulVec u)) • W.L.mulVec u =
        (dotProduct x (W'.M₁.mulVec u)) • W.L.mulVec u := by
    funext r
    have hl := realizeDeep_exp_three_first_quadraticJet W x u r 0
    have hr := realizeDeep_exp_three_first_quadraticJet W' x u r 0
    rw [← hLL] at hr
    have hf : (fun ε ↦
        (realizeDeep Real.exp W (tripleCenteredPerturbation x u ε) r 0 -
          (W.L.mulVec x) r) / ε ^ 2) = fun ε ↦
      (realizeDeep Real.exp W' (tripleCenteredPerturbation x u ε) r 0 -
        (W.L.mulVec x) r) / ε ^ 2 := by
      funext ε
      rw [congrFun hEq (tripleCenteredPerturbation x u ε)]
    rw [← hf] at hr
    have hu := tendsto_nhds_unique hl hr
    have hu' : 2 * (dotProduct x (W.M₁.mulVec u) * (W.L.mulVec u) r) =
        2 * (dotProduct x (W'.M₁.mulVec u) * (W.L.mulVec u) r) := by
      nlinarith [hu]
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hu')
  exact matrix_eq_of_rankOne_jets_eq W.L W.M₁ W'.M₁ hL hprobe

end NormalizedDeepAttention
