module

public import DeepLean.Attention.JetRecovery
public import DeepLean.Attention.TwoToken

/-! # Depth-two normalized attention: certified first-layer recovery -/

@[expose] public section

namespace NormalizedDeepAttention

private theorem tendsto_value_of_quadraticJet
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

/-- The complete depth-two realization has a quadratic repeated-token jet depending
only on `M₁` and `L`; the second score matrix is absent. -/
theorem realizeTwo_exp_symmetricPerturbation_quadraticJet {d dOut : ℕ}
    (W : TwoLayerWeights d dOut) (x u : Fin d → ℝ)
    (r : Fin dOut) (i : Fin 2) :
    Filter.Tendsto
      (fun ε : ℝ ↦
        (realizeTwo Real.exp W (symmetricPerturbation x u ε) r i -
          (W.L.mulVec x) r) / ε ^ 2)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (dotProduct x (W.M₁.mulVec u) * (W.L.mulVec u) r)) := by
  let Y : ℝ → Matrix (Fin d) (Fin 2) ℝ :=
    fun ε ↦ layer Real.exp W.M₁ (symmetricPerturbation x u ε)
  let v : Fin d → ℝ := fun c ↦ dotProduct x (W.M₁.mulVec u) * u c
  have hYjet (c : Fin d) (j : Fin 2) :
      Filter.Tendsto (fun ε ↦ (Y ε c j - x c) / ε ^ 2)
        (nhdsWithin 0 {0}ᶜ) (nhds (v c)) := by
    exact layer_exp_symmetricPerturbation_quadraticJet W.M₁ x u c j
  have hY (c : Fin d) (j : Fin 2) :
      Filter.Tendsto (fun ε ↦ Y ε c j) (nhdsWithin 0 {0}ᶜ) (nhds (x c)) :=
    tendsto_value_of_quadraticJet _ _ _ (hYjet c j)
  let Z : ℝ → Matrix (Fin d) (Fin 2) ℝ := fun ε ↦ layer Real.exp W.M₂ (Y ε)
  have hZjet (c : Fin d) (j : Fin 2) :
      Filter.Tendsto (fun ε ↦ (Z ε c j - x c) / ε ^ 2)
        (nhdsWithin 0 {0}ᶜ) (nhds (v c)) :=
    layer_exp_preserves_common_quadraticJet W.M₂ Y x v hY hYjet c j
  have hsum : Filter.Tendsto
      (fun ε ↦ ∑ c : Fin d, W.L r c * ((Z ε c i - x c) / ε ^ 2))
      (nhdsWithin 0 {0}ᶜ)
      (nhds (∑ c : Fin d, W.L r c * v c)) := by
    apply tendsto_finsetSum Finset.univ
    intro c _
    exact tendsto_const_nhds.mul (hZjet c i)
  have heq : (fun ε : ℝ ↦
      (realizeTwo Real.exp W (symmetricPerturbation x u ε) r i -
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
      dotProduct x (W.M₁.mulVec u) * (W.L.mulVec u) r := by
    simp only [v, Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  simpa [hvsum] using hsum

/-- Functional equality of two depth-two exponential networks identifies the first
virtual score matrix whenever the final virtual value product is nonzero. -/
theorem firstScore_identifiable_of_realizeTwo_exp_eq {d dOut : ℕ}
    (W W' : TwoLayerWeights d dOut) (hL : W.L ≠ 0)
    (hEq : realizeTwo (t := 2) Real.exp W = realizeTwo Real.exp W') :
    W.M₁ = W'.M₁ := by
  have hLL : W.L = W'.L :=
    finalValue_identifiable Real.exp Real.exp_pos W W' (by omega) hEq
  have hprobe (x u : Fin d → ℝ) :
      (dotProduct x (W.M₁.mulVec u)) • W.L.mulVec u =
        (dotProduct x (W'.M₁.mulVec u)) • W.L.mulVec u := by
    funext r
    have hleft := realizeTwo_exp_symmetricPerturbation_quadraticJet W x u r 0
    have hright := realizeTwo_exp_symmetricPerturbation_quadraticJet W' x u r 0
    rw [← hLL] at hright
    have hfun : (fun ε : ℝ ↦
        (realizeTwo Real.exp W (symmetricPerturbation x u ε) r 0 -
          (W.L.mulVec x) r) / ε ^ 2) =
        fun ε ↦
          (realizeTwo Real.exp W' (symmetricPerturbation x u ε) r 0 -
            (W.L.mulVec x) r) / ε ^ 2 := by
      funext ε
      rw [congrFun hEq (symmetricPerturbation x u ε)]
    rw [← hfun] at hright
    have hu := tendsto_nhds_unique hleft hright
    simpa using hu
  exact matrix_eq_of_rankOne_jets_eq W.L W.M₁ W'.M₁ hL hprobe

theorem postValue_layer_exp_two_formula {d dOut : ℕ}
    (L : Matrix (Fin dOut) (Fin d) ℝ) (N : Matrix (Fin d) (Fin d) ℝ)
    (Y : Matrix (Fin d) (Fin 2) ℝ) (r : Fin dOut) (i : Fin 2) :
    (L * layer Real.exp N Y) r i =
      (L.mulVec (Y.col 1)) r +
        Real.sigmoid (attentionScore N Y i 0 - attentionScore N Y i 1) *
          (L.mulVec (Y.col 0 - Y.col 1)) r := by
  let s := Real.sigmoid (attentionScore N Y i 0 - attentionScore N Y i 1)
  change (∑ c : Fin d, L r c * layer Real.exp N Y c i) =
    (∑ c : Fin d, L r c * Y c 1) + s * ∑ c : Fin d, L r c * (Y c 0 - Y c 1)
  calc
    _ = ∑ c : Fin d, (L r c * Y c 1 + s * (L r c * (Y c 0 - Y c 1))) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [layer_exp_two_formula]
      dsimp [s]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- If the post-value difference of a two-token input is visible, equality after a
normalized layer identifies each row's score difference. -/
theorem scoreDifference_eq_of_postValue_layer_eq {d dOut : ℕ}
    (L : Matrix (Fin dOut) (Fin d) ℝ)
    (N N' : Matrix (Fin d) (Fin d) ℝ)
    (Y : Matrix (Fin d) (Fin 2) ℝ)
    (hvisible : L.mulVec (Y.col 0 - Y.col 1) ≠ 0)
    (hEq : L * layer Real.exp N Y = L * layer Real.exp N' Y)
    (i : Fin 2) :
    attentionScore N Y i 0 - attentionScore N Y i 1 =
      attentionScore N' Y i 0 - attentionScore N' Y i 1 := by
  obtain ⟨r, hr⟩ : ∃ r, (L.mulVec (Y.col 0 - Y.col 1)) r ≠ 0 := by
    by_contra h
    push Not at h
    exact hvisible (funext h)
  have he := congrFun (congrFun hEq r) i
  rw [postValue_layer_exp_two_formula, postValue_layer_exp_two_formula] at he
  have hs : Real.sigmoid
      (attentionScore N Y i 0 - attentionScore N Y i 1) =
      Real.sigmoid
        (attentionScore N' Y i 0 - attentionScore N' Y i 1) := by
    apply mul_right_cancel₀ hr
    linarith
  exact Real.sigmoid_injective hs

private theorem scoreDifference_eq_dot_sub {d : ℕ}
    (N : Matrix (Fin d) (Fin d) ℝ) (Y : Matrix (Fin d) (Fin 2) ℝ)
    (i : Fin 2) :
    attentionScore N Y i 0 - attentionScore N Y i 1 =
      dotProduct (Y.col i) (N.mulVec (Y.col 0 - Y.col 1)) := by
  simp [attentionScore, Matrix.mulVec_sub, dotProduct_sub]

private theorem firstLayer_symmetric_difference {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (x u : Fin d → ℝ) :
    let a := dotProduct x (M.mulVec u)
    let b := dotProduct u (M.mulVec u)
    let c := 2 * (Real.sigmoid (2 * (a + b)) - Real.sigmoid (2 * (a - b)))
    (layer Real.exp M (symmetricPerturbation x u 1)).col 0 -
        (layer Real.exp M (symmetricPerturbation x u 1)).col 1 = c • u := by
  dsimp only
  ext r
  change layer Real.exp M (symmetricPerturbation x u 1) r 0 -
      layer Real.exp M (symmetricPerturbation x u 1) r 1 = _
  rw [layer_exp_two_formula, layer_exp_two_formula,
    symmetricPerturbation_scoreDifference_zero,
    symmetricPerturbation_scoreDifference_one]
  have hzero : symmetricPerturbation x u 1 r 0 = x r + u r := by
    have hcol := congrFun (symmetricPerturbation_col_zero x u 1) r
    simpa using hcol
  have hone : symmetricPerturbation x u 1 r 1 = x r - u r := by
    have hcol := congrFun (symmetricPerturbation_col_one x u 1) r
    simpa using hcol
  rw [hzero, hone]
  simp only [one_mul, mul_one, Pi.smul_apply, smul_eq_mul]
  ring

private theorem firstLayer_symmetric_difference_scalar_ne_zero {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (x u : Fin d → ℝ)
    (hb : dotProduct u (M.mulVec u) ≠ 0) :
    2 * (Real.sigmoid
        (2 * (dotProduct x (M.mulVec u) + dotProduct u (M.mulVec u))) -
      Real.sigmoid
        (2 * (dotProduct x (M.mulVec u) - dotProduct u (M.mulVec u)))) ≠ 0 := by
  intro h
  have hs : Real.sigmoid
      (2 * (dotProduct x (M.mulVec u) + dotProduct u (M.mulVec u))) =
      Real.sigmoid
        (2 * (dotProduct x (M.mulVec u) - dotProduct u (M.mulVec u))) := by
    linarith
  have := Real.sigmoid_injective hs
  apply hb
  linarith

private theorem firstLayer_symmetric_zero_col {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (x u : Fin d → ℝ) :
    (layer Real.exp M (symmetricPerturbation x u 1)).col 0 =
      x + (-1 + 2 * Real.sigmoid
        (2 * (dotProduct x (M.mulVec u) + dotProduct u (M.mulVec u)))) • u := by
  ext r
  change layer Real.exp M (symmetricPerturbation x u 1) r 0 = _
  rw [layer_exp_two_formula, symmetricPerturbation_scoreDifference_zero]
  have hzero : symmetricPerturbation x u 1 r 0 = x r + u r := by
    have hcol := congrFun (symmetricPerturbation_col_zero x u 1) r
    simpa using hcol
  have hone : symmetricPerturbation x u 1 r 1 = x r - u r := by
    have hcol := congrFun (symmetricPerturbation_col_one x u 1) r
    simpa using hcol
  rw [hzero, hone]
  simp only [one_mul, mul_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- On every direction visible through `L` and nonisotropic for `M₁`, functional
equality identifies the full bilinear action of the second score matrix in that
direction. -/
theorem secondScore_probe_of_realizeTwo_exp_eq {d dOut : ℕ}
    (W W' : TwoLayerWeights d dOut)
    (hM₁ : W.M₁ = W'.M₁) (hL : W.L = W'.L)
    (hEq : realizeTwo (t := 2) Real.exp W = realizeTwo Real.exp W')
    (u : Fin d → ℝ)
    (huM : dotProduct u (W.M₁.mulVec u) ≠ 0)
    (huL : W.L.mulVec u ≠ 0) :
    ∀ x : Fin d → ℝ,
      dotProduct x (W.M₂.mulVec u) = dotProduct x (W'.M₂.mulVec u) := by
  intro x
  let X := symmetricPerturbation x u 1
  let Y := layer Real.exp W.M₁ X
  let c := 2 * (Real.sigmoid
      (2 * (dotProduct x (W.M₁.mulVec u) + dotProduct u (W.M₁.mulVec u))) -
    Real.sigmoid
      (2 * (dotProduct x (W.M₁.mulVec u) - dotProduct u (W.M₁.mulVec u))))
  have hc : c ≠ 0 :=
    firstLayer_symmetric_difference_scalar_ne_zero W.M₁ x u huM
  have hdiff : Y.col 0 - Y.col 1 = c • u := by
    exact firstLayer_symmetric_difference W.M₁ x u
  have hvisible : W.L.mulVec (Y.col 0 - Y.col 1) ≠ 0 := by
    rw [hdiff, Matrix.mulVec_smul]
    exact smul_ne_zero hc huL
  have houter : W.L * layer Real.exp W.M₂ Y =
      W.L * layer Real.exp W'.M₂ Y := by
    have heval := congrFun hEq X
    simp only [realizeTwo, X] at heval
    rw [← hM₁, ← hL] at heval
    exact heval
  have hs0 := scoreDifference_eq_of_postValue_layer_eq W.L W.M₂ W'.M₂ Y
    hvisible houter 0
  have hs1 := scoreDifference_eq_of_postValue_layer_eq W.L W.M₂ W'.M₂ Y
    hvisible houter 1
  rw [scoreDifference_eq_dot_sub, scoreDifference_eq_dot_sub, hdiff,
    Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul, dotProduct_smul] at hs0 hs1
  have hc0 : dotProduct (Y.col 0) (W.M₂.mulVec u) =
      dotProduct (Y.col 0) (W'.M₂.mulVec u) := by
    exact mul_left_cancel₀ hc hs0
  have hc1 : dotProduct (Y.col 1) (W.M₂.mulVec u) =
      dotProduct (Y.col 1) (W'.M₂.mulVec u) := by
    exact mul_left_cancel₀ hc hs1
  have hquad : dotProduct u (W.M₂.mulVec u) =
      dotProduct u (W'.M₂.mulVec u) := by
    have hsub : dotProduct (Y.col 0 - Y.col 1) (W.M₂.mulVec u) =
        dotProduct (Y.col 0 - Y.col 1) (W'.M₂.mulVec u) := by
      rw [sub_dotProduct, sub_dotProduct, hc0, hc1]
    rw [hdiff, smul_dotProduct, smul_dotProduct] at hsub
    exact mul_left_cancel₀ hc hsub
  have hcol : Y.col 0 = x + (-1 + 2 * Real.sigmoid
      (2 * (dotProduct x (W.M₁.mulVec u) + dotProduct u (W.M₁.mulVec u)))) • u :=
    firstLayer_symmetric_zero_col W.M₁ x u
  rw [hcol, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct,
    hquad] at hc0
  linarith

/-- Complete depth-two singleton-fiber theorem for two-token exponential normalized
attention on the explicit regular locus `L ≠ 0` and `M₁ᵀ ≠ -M₁`. -/
theorem realizeTwo_exp_two_fiber_singleton {d dOut : ℕ}
    (W W' : TwoLayerWeights d dOut)
    (hL : W.L ≠ 0) (hM : W.M₁.transpose ≠ -W.M₁)
    (hEq : realizeTwo (t := 2) Real.exp W = realizeTwo Real.exp W') :
    W = W' := by
  have hLL : W.L = W'.L :=
    finalValue_identifiable Real.exp Real.exp_pos W W' (by omega) hEq
  have hM₁ : W.M₁ = W'.M₁ :=
    firstScore_identifiable_of_realizeTwo_exp_eq W W' hL hEq
  have hM₂ : W.M₂ = W'.M₂ :=
    matrix_eq_of_eq_on_visible_nonisotropic W.L W.M₁ W.M₂ W'.M₂ hL hM
      (fun u huM huL ↦
        secondScore_probe_of_realizeTwo_exp_eq W W' hM₁ hLL hEq u huM huL)
  cases W
  cases W'
  simp_all

end NormalizedDeepAttention
