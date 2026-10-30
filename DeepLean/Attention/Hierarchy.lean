module

public import DeepLean.Attention.DeepFirstScore

/-!
# Hierarchical two-token coordinates

Every normalized layer preserves an affine line containing a two-token input.  These
coordinates expose the powers `ε, ε³, ε⁹, ...` that separate successive virtual score
matrices in a deep network.
-/

@[expose] public section

namespace NormalizedDeepAttention

/-- The smooth secant factor in a sigmoid difference. -/
noncomputable def sigmoidSecantFactor (a b : ℝ) : ℝ :=
  Real.exp b * dslope Real.exp 0 (a - b) /
    ((Real.exp a + 1) * (Real.exp b + 1))

theorem sigmoid_sub_factor (a b : ℝ) :
    Real.sigmoid a - Real.sigmoid b =
      (a - b) * sigmoidSecantFactor a b := by
  have ha : Real.exp a + 1 ≠ 0 := by positivity
  have hb : Real.exp b + 1 ≠ 0 := by positivity
  have he : (a - b) * dslope Real.exp 0 (a - b) = Real.exp (a - b) - 1 := by
    have h := sub_smul_dslope Real.exp 0 (a - b)
    simpa only [sub_zero, smul_eq_mul, Real.exp_zero] using h
  have hsig (z : ℝ) : Real.sigmoid z = Real.exp z / (Real.exp z + 1) := by
    rw [Real.sigmoid_def, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  rw [hsig a, hsig b]
  unfold sigmoidSecantFactor
  have heab : Real.exp a = Real.exp b * Real.exp (a - b) := by
    rw [Real.exp_sub]
    field_simp [Real.exp_ne_zero]
  have hnum : Real.exp a * (Real.exp b + 1) -
      (Real.exp a + 1) * Real.exp b =
      (a - b) * (Real.exp b * dslope Real.exp 0 (a - b)) := by
    calc
      _ = Real.exp b * (Real.exp (a - b) - 1) := by rw [heab]; ring
      _ = Real.exp b * ((a - b) * dslope Real.exp 0 (a - b)) := by rw [he]
      _ = _ := by ring
  field_simp [Real.exp_ne_zero, ha, hb]
  simpa [mul_assoc, mul_comm, mul_left_comm] using hnum

theorem tendsto_sigmoidSecantFactor_zero
    {α : Type*} {F : Filter α} {a b : α → ℝ}
    (ha : Filter.Tendsto a F (nhds 0)) (hb : Filter.Tendsto b F (nhds 0)) :
    Filter.Tendsto (fun z ↦ sigmoidSecantFactor (a z) (b z)) F
      (nhds (1 / 4 : ℝ)) := by
  have hab : Filter.Tendsto (fun z ↦ a z - b z) F (nhds 0) := by
    simpa using ha.sub hb
  have hds : Filter.Tendsto (fun z ↦ dslope Real.exp 0 (a z - b z)) F
      (nhds (1 : ℝ)) := by
    have hc : ContinuousAt (dslope Real.exp 0) 0 :=
      continuousAt_dslope_same.mpr (Real.hasDerivAt_exp 0).differentiableAt
    have hv : dslope Real.exp 0 0 = (1 : ℝ) := by
      rw [dslope_same, (Real.hasDerivAt_exp 0).deriv, Real.exp_zero]
    rw [← hv]
    exact hc.tendsto.comp hab
  have hea : Filter.Tendsto (fun z ↦ Real.exp (a z)) F (nhds 1) := by
    simpa [Function.comp_def] using (Real.hasDerivAt_exp 0).continuousAt.tendsto.comp ha
  have heb : Filter.Tendsto (fun z ↦ Real.exp (b z)) F (nhds 1) := by
    simpa [Function.comp_def] using (Real.hasDerivAt_exp 0).continuousAt.tendsto.comp hb
  have hnum := heb.mul hds
  have hden := (hea.add_const 1).mul (heb.add_const 1)
  have hdiv := hnum.div hden (by norm_num : ((1 : ℝ) + 1) * (1 + 1) ≠ 0)
  convert hdiv using 1
  · rfl
  · congr 1
    norm_num

/-- A moving pair of logits has the expected sigmoid difference quotient.  Unlike a
one-sided derivative statement, both logits may move at the scale of the quotient. -/
theorem tendsto_sigmoid_sub_div {α : Type*} {F : Filter α}
    (a b scale : α → ℝ) (c : ℝ)
    (ha : Filter.Tendsto a F (nhds 0)) (hb : Filter.Tendsto b F (nhds 0))
    (hquot : Filter.Tendsto (fun z ↦ (a z - b z) / scale z) F (nhds c))
    (hscale : ∀ᶠ z in F, scale z ≠ 0) :
    Filter.Tendsto
      (fun z ↦ (Real.sigmoid (a z) - Real.sigmoid (b z)) / scale z) F
      (nhds (c / 4)) := by
  have hfactor := tendsto_sigmoidSecantFactor_zero ha hb
  have hp := hquot.mul hfactor
  have hp' : Filter.Tendsto
      (fun z ↦ (a z - b z) / scale z * sigmoidSecantFactor (a z) (b z)) F
      (nhds (c / 4)) := by
    convert hp using 1 <;> ring
  apply Filter.Tendsto.congr' _ hp'
  filter_upwards [hscale] with z hz
  rw [sigmoid_sub_factor]
  field_simp [hz]

/-- Two points on the affine line `x + ℝu`, stored as columns. -/
def linePair {d : ℕ} (x u : Fin d → ℝ) (p q : ℝ) :
    Matrix (Fin d) (Fin 2) ℝ :=
  fun r i ↦ Fin.cases (x r + p * u r) (fun _ ↦ x r + q * u r) i

@[simp] theorem linePair_col_zero {d : ℕ} (x u : Fin d → ℝ) (p q : ℝ) :
    (linePair x u p q).col 0 = x + p • u := by
  ext r
  simp [linePair]

@[simp] theorem linePair_col_one {d : ℕ} (x u : Fin d → ℝ) (p q : ℝ) :
    (linePair x u p q).col 1 = x + q • u := by
  ext r
  have h : (1 : Fin 2) = (0 : Fin 1).succ := by decide
  rw [show (linePair x u p q).col 1 r = linePair x u p q r 1 by rfl, h]
  rfl

theorem symmetricPerturbation_eq_linePair {d : ℕ}
    (x u : Fin d → ℝ) (ε : ℝ) :
    symmetricPerturbation x u ε = linePair x u ε (-ε) := by
  ext r i
  fin_cases i
  · rfl
  · change x r - ε * u r = x r + -ε * u r
    ring

noncomputable def scalarStepZero (a b p q : ℝ) : ℝ :=
  q + Real.sigmoid ((p - q) * (a + p * b)) * (p - q)

noncomputable def scalarStepOne (a b p q : ℝ) : ℝ :=
  q + Real.sigmoid ((p - q) * (a + q * b)) * (p - q)

def scalarAt (p q : ℝ) (i : Fin 2) : ℝ :=
  Fin.cases p (fun _ ↦ q) i

@[simp] theorem scalarAt_zero (p q : ℝ) : scalarAt p q 0 = p := by rfl

@[simp] theorem scalarAt_one (p q : ℝ) : scalarAt p q 1 = q := by
  have h : (1 : Fin 2) = (0 : Fin 1).succ := by decide
  rw [h]
  rfl

theorem linePair_scoreDifference_zero {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (x u : Fin d → ℝ) (p q : ℝ) :
    attentionScore M (linePair x u p q) 0 0 -
        attentionScore M (linePair x u p q) 0 1 =
      (p - q) * (dotProduct x (M.mulVec u) +
        p * dotProduct u (M.mulVec u)) := by
  simp only [attentionScore, linePair_col_zero, linePair_col_one,
    Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    dotProduct_sub, dotProduct_smul, smul_dotProduct]
  ring

theorem linePair_scoreDifference_one {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (x u : Fin d → ℝ) (p q : ℝ) :
    attentionScore M (linePair x u p q) 1 0 -
        attentionScore M (linePair x u p q) 1 1 =
      (p - q) * (dotProduct x (M.mulVec u) +
        q * dotProduct u (M.mulVec u)) := by
  simp only [attentionScore, linePair_col_zero, linePair_col_one,
    Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    dotProduct_sub, dotProduct_smul, smul_dotProduct]
  ring

/-- A normalized layer maps an affine-line pair to another pair on the same line. -/
theorem layer_exp_linePair {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (x u : Fin d → ℝ) (p q : ℝ) :
    layer Real.exp M (linePair x u p q) =
      linePair x u
        (scalarStepZero (dotProduct x (M.mulVec u))
          (dotProduct u (M.mulVec u)) p q)
        (scalarStepOne (dotProduct x (M.mulVec u))
          (dotProduct u (M.mulVec u)) p q) := by
  apply Matrix.ext
  intro r i
  fin_cases i
  · change layer Real.exp M (linePair x u p q) r 0 =
      x r + scalarStepZero (dotProduct x (M.mulVec u))
        (dotProduct u (M.mulVec u)) p q * u r
    have hp : linePair x u p q r 0 = x r + p * u r := by
      exact congrFun (linePair_col_zero x u p q) r
    have hq : linePair x u p q r 1 = x r + q * u r := by
      exact congrFun (linePair_col_one x u p q) r
    rw [layer_exp_two_formula, linePair_scoreDifference_zero, hp, hq]
    simp only [linePair, scalarStepZero]
    ring
  · change layer Real.exp M (linePair x u p q) r 1 =
      x r + scalarStepOne (dotProduct x (M.mulVec u))
        (dotProduct u (M.mulVec u)) p q * u r
    have hp : linePair x u p q r 0 = x r + p * u r := by
      exact congrFun (linePair_col_zero x u p q) r
    have hq : linePair x u p q r 1 = x r + q * u r := by
      exact congrFun (linePair_col_one x u p q) r
    rw [layer_exp_two_formula, linePair_scoreDifference_one, hp, hq]
    simp only [linePair, scalarStepOne]
    ring

theorem scalarStep_gap_ne_zero (a b p q : ℝ)
    (hpq : p - q ≠ 0) (hb : b ≠ 0) :
    scalarStepZero a b p q - scalarStepOne a b p q ≠ 0 := by
  intro hz
  have hprod : (Real.sigmoid ((p - q) * (a + p * b)) -
      Real.sigmoid ((p - q) * (a + q * b))) * (p - q) = 0 := by
    dsimp [scalarStepZero, scalarStepOne] at hz
    linarith
  have hsig : Real.sigmoid ((p - q) * (a + p * b)) =
      Real.sigmoid ((p - q) * (a + q * b)) := by
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hpq)
  have hlogit := Real.sigmoid_injective hsig
  have : (p - q) ^ 2 * b = 0 := by
    nlinarith
  exact (mul_ne_zero (pow_ne_zero 2 hpq) hb) this

/-- The first layer turns an `ε` token separation into an `ε³` separation.  Its
leading coefficient is the quadratic form of the score matrix. -/
theorem tendsto_first_scalar_gap_cubic (a b : ℝ) :
    Filter.Tendsto
      (fun ε : ℝ ↦
        (scalarStepZero a b ε (-ε) - scalarStepOne a b ε (-ε)) / ε ^ 3)
      (nhdsWithin 0 {0}ᶜ) (nhds (2 * b)) := by
  let z₀ : ℝ → ℝ := fun ε ↦ 2 * ε * (a + ε * b)
  let z₁ : ℝ → ℝ := fun ε ↦ 2 * ε * (a - ε * b)
  let F := nhdsWithin (0 : ℝ) ({0}ᶜ)
  have hz₀ : Filter.Tendsto z₀ F (nhds 0) := by
    have hc : ContinuousAt z₀ 0 := by
      dsimp [z₀]
      fun_prop
    simpa [z₀] using hc.tendsto.mono_left (show F ≤ nhds 0 from nhdsWithin_le_nhds)
  have hz₁ : Filter.Tendsto z₁ F (nhds 0) := by
    have hc : ContinuousAt z₁ 0 := by
      dsimp [z₁]
      fun_prop
    simpa [z₁] using hc.tendsto.mono_left (show F ≤ nhds 0 from nhdsWithin_le_nhds)
  have hquot : Filter.Tendsto (fun ε ↦ (z₀ ε - z₁ ε) / ε ^ 2) F
      (nhds (4 * b)) := by
    have heq : (fun ε ↦ (z₀ ε - z₁ ε) / ε ^ 2) =ᶠ[F] fun _ ↦ 4 * b := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : ε ≠ 0 := hε
      dsimp [z₀, z₁]
      field_simp [hε0]
      ring
    exact tendsto_const_nhds.congr' heq.symm
  have hs := tendsto_sigmoid_sub_div z₀ z₁ (fun ε ↦ ε ^ 2)
    (4 * b) hz₀ hz₁ hquot (by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact pow_ne_zero 2 hε)
  have heq : (fun ε : ℝ ↦
      (scalarStepZero a b ε (-ε) - scalarStepOne a b ε (-ε)) / ε ^ 3) =ᶠ[F]
      fun ε ↦ 2 * ((Real.sigmoid (z₀ ε) - Real.sigmoid (z₁ ε)) / ε ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : ε ≠ 0 := hε
    dsimp [scalarStepZero, scalarStepOne, z₀, z₁]
    field_simp [hε0]
    ring
  apply Filter.Tendsto.congr' heq.symm
  convert hs.const_mul 2 using 1 <;> ring

/-- The cubic separation law for a general small affine-line pair. -/
theorem tendsto_scalar_gap_cubic {α : Type*} {F : Filter α}
    (a b : ℝ) (p q scale : α → ℝ) (c : ℝ)
    (hp : Filter.Tendsto p F (nhds 0)) (hq : Filter.Tendsto q F (nhds 0))
    (hs : Filter.Tendsto scale F (nhds 0))
    (hgap : Filter.Tendsto (fun z ↦ (p z - q z) / scale z) F (nhds c))
    (hscale : ∀ᶠ z in F, scale z ≠ 0) :
    Filter.Tendsto
      (fun z ↦ (scalarStepZero a b (p z) (q z) -
        scalarStepOne a b (p z) (q z)) / (scale z) ^ 3) F
      (nhds (c ^ 3 * b / 4)) := by
  let gap : α → ℝ := fun z ↦ p z - q z
  let z₀ : α → ℝ := fun z ↦ gap z * (a + p z * b)
  let z₁ : α → ℝ := fun z ↦ gap z * (a + q z * b)
  have hgap0 : Filter.Tendsto gap F (nhds 0) := by
    have hprod := hs.mul hgap
    have heq : gap =ᶠ[F] fun z ↦ scale z * (gap z / scale z) := by
      filter_upwards [hscale] with z hz
      dsimp [gap]
      field_simp [hz]
    apply Filter.Tendsto.congr' heq.symm
    simpa using hprod
  have hz₀ : Filter.Tendsto z₀ F (nhds 0) := by
    have hinner : Filter.Tendsto (fun z ↦ a + p z * b) F (nhds a) := by
      simpa using (tendsto_const_nhds : Filter.Tendsto (fun _ : α ↦ a) F (nhds a)).add
        (hp.mul_const b)
    have := hgap0.mul hinner
    simpa [z₀, gap] using this
  have hz₁ : Filter.Tendsto z₁ F (nhds 0) := by
    have hinner : Filter.Tendsto (fun z ↦ a + q z * b) F (nhds a) := by
      simpa using (tendsto_const_nhds : Filter.Tendsto (fun _ : α ↦ a) F (nhds a)).add
        (hq.mul_const b)
    have := hgap0.mul hinner
    simpa [z₁, gap] using this
  have hfactor := tendsto_sigmoidSecantFactor_zero hz₀ hz₁
  have hcube := (hgap.mul (hgap.mul hgap)).mul_const b
  have hlim := hcube.mul hfactor
  have heq : (fun z ↦ (scalarStepZero a b (p z) (q z) -
      scalarStepOne a b (p z) (q z)) / (scale z) ^ 3) =ᶠ[F]
      fun z ↦ ((gap z / scale z) * (gap z / scale z) *
        (gap z / scale z) * b) * sigmoidSecantFactor (z₀ z) (z₁ z) := by
    filter_upwards [hscale] with z hz
    have hs0 : scale z ^ 3 ≠ 0 := pow_ne_zero 3 hz
    rw [show scalarStepZero a b (p z) (q z) - scalarStepOne a b (p z) (q z) =
        (Real.sigmoid (z₀ z) - Real.sigmoid (z₁ z)) * gap z by
      dsimp [scalarStepZero, scalarStepOne, z₀, z₁, gap]
      ring,
      sigmoid_sub_factor]
    have hlogit : z₀ z - z₁ z = gap z ^ 2 * b := by
      dsimp [z₀, z₁, gap]
      ring
    rw [hlogit]
    field_simp [hz, hs0]
  apply Filter.Tendsto.congr' heq.symm
  convert hlim using 1
  · funext z
    dsimp [gap]
    ring
  · congr 1
    ring

/-- Changing one score matrix changes both output coordinates at the square of
the incoming separation scale. -/
theorem tendsto_scalarStep_comparison {α : Type*} {F : Filter α}
    (a b a' b' : ℝ) (p q scale : α → ℝ) (c : ℝ)
    (hp : Filter.Tendsto p F (nhds 0)) (hq : Filter.Tendsto q F (nhds 0))
    (hs : Filter.Tendsto scale F (nhds 0))
    (hgap : Filter.Tendsto (fun z ↦ (p z - q z) / scale z) F (nhds c))
    (hscale : ∀ᶠ z in F, scale z ≠ 0) (i : Fin 2) :
    let step := fun a b p q ↦ scalarAt (scalarStepZero a b p q)
      (scalarStepOne a b p q) i
    Filter.Tendsto
      (fun z ↦ (step a b (p z) (q z) - step a' b' (p z) (q z)) /
        (scale z) ^ 2) F
      (nhds (c ^ 2 * (a - a') / 4)) := by
  dsimp only
  let gap : α → ℝ := fun z ↦ p z - q z
  let coord : α → ℝ := fun z ↦ scalarAt (p z) (q z) i
  let z₀ : α → ℝ := fun z ↦ gap z * (a + coord z * b)
  let z₁ : α → ℝ := fun z ↦ gap z * (a' + coord z * b')
  have hcoord : Filter.Tendsto coord F (nhds 0) := by
    fin_cases i
    · simpa [coord] using hp
    · simpa [coord] using hq
  have hgap0 : Filter.Tendsto gap F (nhds 0) := by
    have hprod := hs.mul hgap
    have heq : gap =ᶠ[F] fun z ↦ scale z * (gap z / scale z) := by
      filter_upwards [hscale] with z hz
      dsimp [gap]
      field_simp [hz]
    apply Filter.Tendsto.congr' heq.symm
    simpa using hprod
  have hz₀ : Filter.Tendsto z₀ F (nhds 0) := by
    have hinner : Filter.Tendsto (fun z ↦ a + coord z * b) F (nhds a) := by
      simpa using (tendsto_const_nhds : Filter.Tendsto (fun _ : α ↦ a) F (nhds a)).add
        (hcoord.mul_const b)
    have := hgap0.mul hinner
    simpa [z₀] using this
  have hz₁ : Filter.Tendsto z₁ F (nhds 0) := by
    have hinner : Filter.Tendsto (fun z ↦ a' + coord z * b') F (nhds a') := by
      simpa using (tendsto_const_nhds : Filter.Tendsto (fun _ : α ↦ a') F (nhds a')).add
        (hcoord.mul_const b')
    have := hgap0.mul hinner
    simpa [z₁] using this
  have hzquot : Filter.Tendsto (fun z ↦ (z₀ z - z₁ z) / scale z) F
      (nhds (c * (a - a'))) := by
    have hinner : Filter.Tendsto
        (fun z ↦ (a - a') + coord z * (b - b')) F (nhds (a - a')) := by
      simpa using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : α ↦ a - a') F (nhds (a - a'))).add
          (hcoord.mul_const (b - b'))
    have hprod := hgap.mul hinner
    have heq : (fun z ↦ (z₀ z - z₁ z) / scale z) =ᶠ[F]
        fun z ↦ (gap z / scale z) * ((a - a') + coord z * (b - b')) := by
      filter_upwards [hscale] with z hz
      dsimp [z₀, z₁]
      field_simp [hz]
      ring
    apply Filter.Tendsto.congr' heq.symm
    simpa using hprod
  have hsig := tendsto_sigmoid_sub_div z₀ z₁ scale (c * (a - a'))
    hz₀ hz₁ hzquot hscale
  have hprod := hsig.mul hgap
  have heq : (fun z ↦
      (scalarAt (scalarStepZero a b (p z) (q z))
          (scalarStepOne a b (p z) (q z)) i -
        scalarAt (scalarStepZero a' b' (p z) (q z))
          (scalarStepOne a' b' (p z) (q z)) i) /
        (scale z) ^ 2) =ᶠ[F]
      fun z ↦ ((Real.sigmoid (z₀ z) - Real.sigmoid (z₁ z)) / scale z) *
        (gap z / scale z) := by
    filter_upwards [hscale] with z hz
    have hs0 : scale z ^ 2 ≠ 0 := pow_ne_zero 2 hz
    fin_cases i <;> simp only [scalarAt_zero, scalarAt_one] <;>
      dsimp [scalarStepZero, scalarStepOne, z₀, z₁, coord, gap] <;>
      simp only [scalarAt_zero, scalarAt_one] <;>
      field_simp [hz, hs0] <;> ring
  apply Filter.Tendsto.congr' heq.symm
  convert hprod using 1 <;> ring

/-- The two outputs of the first layer converge back to the base point. -/
theorem tendsto_first_scalarStep_zero (a b : ℝ) (i : Fin 2) :
    Filter.Tendsto
      (fun ε : ℝ ↦ scalarAt (scalarStepZero a b ε (-ε))
        (scalarStepOne a b ε (-ε)) i)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  have hc : ContinuousAt
      (fun ε : ℝ ↦ scalarAt (scalarStepZero a b ε (-ε))
        (scalarStepOne a b ε (-ε)) i) 0 := by
    fin_cases i
    · change ContinuousAt (fun ε : ℝ ↦ scalarStepZero a b ε (-ε)) 0
      unfold scalarStepZero
      fun_prop
    · change ContinuousAt (fun ε : ℝ ↦ scalarStepOne a b ε (-ε)) 0
      unfold scalarStepOne
      fun_prop
  convert hc.tendsto.mono_left
    (show nhdsWithin (0 : ℝ) ({0}ᶜ) ≤ nhds 0 from nhdsWithin_le_nhds) using 1 <;>
    fin_cases i <;> norm_num [scalarStepZero, scalarStepOne, Real.sigmoid_zero]

/-- The second score matrix is a sixth-order observable after the first matrix is
fixed.  The coefficient is nonzero exactly when the first quadratic probe is. -/
theorem tendsto_second_scalar_comparison_sixth
    (a₁ b₁ a₂ b₂ a₂' b₂' : ℝ) (i : Fin 2) :
    let p := fun ε ↦ scalarStepZero a₁ b₁ ε (-ε)
    let q := fun ε ↦ scalarStepOne a₁ b₁ ε (-ε)
    let step := fun a b p q ↦ scalarAt (scalarStepZero a b p q)
      (scalarStepOne a b p q) i
    Filter.Tendsto
      (fun ε : ℝ ↦ (step a₂ b₂ (p ε) (q ε) -
        step a₂' b₂' (p ε) (q ε)) / ε ^ 6)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (b₁ ^ 2 * (a₂ - a₂'))) := by
  dsimp only
  let p : ℝ → ℝ := fun ε ↦ scalarStepZero a₁ b₁ ε (-ε)
  let q : ℝ → ℝ := fun ε ↦ scalarStepOne a₁ b₁ ε (-ε)
  let scale : ℝ → ℝ := fun ε ↦ ε ^ 3
  have hp := tendsto_first_scalarStep_zero a₁ b₁ 0
  have hq := tendsto_first_scalarStep_zero a₁ b₁ 1
  have hs : Filter.Tendsto scale (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have hc : ContinuousAt scale 0 := by dsimp [scale]; fun_prop
    simpa [scale] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hgap : Filter.Tendsto (fun ε ↦ (p ε - q ε) / scale ε)
      (nhdsWithin 0 {0}ᶜ) (nhds (2 * b₁)) := by
    exact tendsto_first_scalar_gap_cubic a₁ b₁
  have hscale : ∀ᶠ ε in nhdsWithin (0 : ℝ) ({0}ᶜ), scale ε ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact pow_ne_zero 3 hε
  have h := tendsto_scalarStep_comparison a₂ b₂ a₂' b₂' p q scale
    (2 * b₁) hp hq hs hgap hscale i
  convert h using 1
  · funext ε
    dsimp [scale]
    ring
  · congr 1
    ring

/-- A later normalized layer preserves a comparison that is common to both token
coordinates and dominates the within-pair separations. -/
theorem tendsto_scalarStep_preserves_common_comparison {α : Type*} {F : Filter α}
    (a b a' b' : ℝ) (p q p' q' scale : α → ℝ) (w : ℝ)
    (hp : Filter.Tendsto p F (nhds 0)) (hq : Filter.Tendsto q F (nhds 0))
    (hp' : Filter.Tendsto p' F (nhds 0)) (hq' : Filter.Tendsto q' F (nhds 0))
    (_hpp' : Filter.Tendsto (fun z ↦ (p z - p' z) / scale z) F (nhds w))
    (hqq' : Filter.Tendsto (fun z ↦ (q z - q' z) / scale z) F (nhds w))
    (hgap : Filter.Tendsto (fun z ↦ (p z - q z) / scale z) F (nhds 0))
    (hgap' : Filter.Tendsto (fun z ↦ (p' z - q' z) / scale z) F (nhds 0))
    (hscale : ∀ᶠ z in F, scale z ≠ 0) (i : Fin 2) :
    Filter.Tendsto
      (fun z ↦ (scalarAt
          (scalarStepZero a b (p z) (q z)) (scalarStepOne a b (p z) (q z)) i -
        scalarAt
          (scalarStepZero a' b' (p' z) (q' z))
          (scalarStepOne a' b' (p' z) (q' z)) i) / scale z) F
      (nhds w) := by
  let gap : α → ℝ := fun z ↦ p z - q z
  let gap' : α → ℝ := fun z ↦ p' z - q' z
  let coord : α → ℝ := fun z ↦ scalarAt (p z) (q z) i
  let coord' : α → ℝ := fun z ↦ scalarAt (p' z) (q' z) i
  let logit : α → ℝ := fun z ↦ gap z * (a + coord z * b)
  let logit' : α → ℝ := fun z ↦ gap' z * (a' + coord' z * b')
  have hgap0 : Filter.Tendsto gap F (nhds 0) := by simpa [gap] using hp.sub hq
  have hgap0' : Filter.Tendsto gap' F (nhds 0) := by simpa [gap'] using hp'.sub hq'
  have hcoord : Filter.Tendsto coord F (nhds 0) := by
    fin_cases i
    · simpa [coord] using hp
    · simpa [coord] using hq
  have hcoord' : Filter.Tendsto coord' F (nhds 0) := by
    fin_cases i
    · simpa [coord'] using hp'
    · simpa [coord'] using hq'
  have hlogit : Filter.Tendsto logit F (nhds 0) := by
    have hinner : Filter.Tendsto (fun z ↦ a + coord z * b) F (nhds a) := by
      simpa using (tendsto_const_nhds : Filter.Tendsto (fun _ : α ↦ a) F (nhds a)).add
        (hcoord.mul_const b)
    simpa [logit] using hgap0.mul hinner
  have hlogit' : Filter.Tendsto logit' F (nhds 0) := by
    have hinner : Filter.Tendsto (fun z ↦ a' + coord' z * b') F (nhds a') := by
      simpa using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : α ↦ a') F (nhds a')).add
          (hcoord'.mul_const b')
    simpa [logit'] using hgap0'.mul hinner
  have hsig : Filter.Tendsto (fun z ↦ Real.sigmoid (logit z)) F (nhds (1 / 2 : ℝ)) := by
    have := (Real.hasDerivAt_sigmoid 0).continuousAt.tendsto.comp hlogit
    simpa [Function.comp_def, Real.sigmoid_zero] using this
  have hsig' : Filter.Tendsto (fun z ↦ Real.sigmoid (logit' z)) F
      (nhds (1 / 2 : ℝ)) := by
    have := (Real.hasDerivAt_sigmoid 0).continuousAt.tendsto.comp hlogit'
    simpa [Function.comp_def, Real.sigmoid_zero] using this
  have hlim := hqq'.add ((hsig.mul hgap).sub (hsig'.mul hgap'))
  have heq : (fun z ↦ (scalarAt
      (scalarStepZero a b (p z) (q z)) (scalarStepOne a b (p z) (q z)) i -
    scalarAt
      (scalarStepZero a' b' (p' z) (q' z))
      (scalarStepOne a' b' (p' z) (q' z)) i) / scale z) =ᶠ[F]
    fun z ↦ (q z - q' z) / scale z +
      (Real.sigmoid (logit z) * ((p z - q z) / scale z) -
        Real.sigmoid (logit' z) * ((p' z - q' z) / scale z)) := by
    filter_upwards [hscale] with z hz
    fin_cases i <;> simp only [scalarAt_zero, scalarAt_one] <;>
      dsimp [scalarStepZero, scalarStepOne, logit, logit', coord, coord', gap, gap'] <;>
      simp only [scalarAt_zero, scalarAt_one] <;>
      field_simp [hz] <;> ring
  apply Filter.Tendsto.congr' heq.symm
  simpa using hlim

theorem tendsto_scalarStep_zero {α : Type*} {F : Filter α}
    (a b : ℝ) (p q : α → ℝ)
    (hp : Filter.Tendsto p F (nhds 0)) (hq : Filter.Tendsto q F (nhds 0))
    (i : Fin 2) :
    Filter.Tendsto
      (fun z ↦ scalarAt (scalarStepZero a b (p z) (q z))
        (scalarStepOne a b (p z) (q z)) i) F (nhds 0) := by
  have hgap : Filter.Tendsto (fun z ↦ p z - q z) F (nhds 0) := by
    simpa using hp.sub hq
  have hcoord : Filter.Tendsto (fun z ↦ scalarAt (p z) (q z) i) F (nhds 0) := by
    fin_cases i
    · simpa using hp
    · simpa using hq
  let logit : α → ℝ := fun z ↦
    (p z - q z) * (a + scalarAt (p z) (q z) i * b)
  have hlogit : Filter.Tendsto logit F (nhds 0) := by
    have hinner : Filter.Tendsto
        (fun z ↦ a + scalarAt (p z) (q z) i * b) F (nhds a) := by
      simpa using (tendsto_const_nhds : Filter.Tendsto (fun _ : α ↦ a) F (nhds a)).add
        (hcoord.mul_const b)
    simpa [logit] using hgap.mul hinner
  have hsig : Filter.Tendsto (fun z ↦ Real.sigmoid (logit z)) F
      (nhds (1 / 2 : ℝ)) := by
    have := (Real.hasDerivAt_sigmoid 0).continuousAt.tendsto.comp hlogit
    simpa [Function.comp_def, Real.sigmoid_zero] using this
  have hlim := hq.add (hsig.mul hgap)
  have heq : (fun z ↦ scalarAt (scalarStepZero a b (p z) (q z))
      (scalarStepOne a b (p z) (q z)) i) =
      fun z ↦ q z + Real.sigmoid (logit z) * (p z - q z) := by
    funext z
    fin_cases i <;> simp only [scalarAt_zero, scalarAt_one] <;>
      dsimp [scalarStepZero, scalarStepOne, logit] <;>
      simp only [scalarAt_zero, scalarAt_one]
  rw [heq]
  simpa using hlim

/-- Specialization of suffix preservation: after exposing the second score at order
six, one arbitrary final normalized layer leaves that coefficient unchanged. -/
theorem tendsto_third_scalar_comparison_sixth
    (a₁ b₁ a₂ b₂ a₂' b₂' a₃ b₃ a₃' b₃' : ℝ) (i : Fin 2) :
    let p₁ := fun ε ↦ scalarStepZero a₁ b₁ ε (-ε)
    let q₁ := fun ε ↦ scalarStepOne a₁ b₁ ε (-ε)
    let p₂ := fun ε ↦ scalarStepZero a₂ b₂ (p₁ ε) (q₁ ε)
    let q₂ := fun ε ↦ scalarStepOne a₂ b₂ (p₁ ε) (q₁ ε)
    let p₂' := fun ε ↦ scalarStepZero a₂' b₂' (p₁ ε) (q₁ ε)
    let q₂' := fun ε ↦ scalarStepOne a₂' b₂' (p₁ ε) (q₁ ε)
    Filter.Tendsto
      (fun ε : ℝ ↦ (scalarAt (scalarStepZero a₃ b₃ (p₂ ε) (q₂ ε))
          (scalarStepOne a₃ b₃ (p₂ ε) (q₂ ε)) i -
        scalarAt (scalarStepZero a₃' b₃' (p₂' ε) (q₂' ε))
          (scalarStepOne a₃' b₃' (p₂' ε) (q₂' ε)) i) / ε ^ 6)
      (nhdsWithin 0 {0}ᶜ) (nhds (b₁ ^ 2 * (a₂ - a₂'))) := by
  dsimp only
  let F := nhdsWithin (0 : ℝ) ({0}ᶜ)
  let p₁ : ℝ → ℝ := fun ε ↦ scalarStepZero a₁ b₁ ε (-ε)
  let q₁ : ℝ → ℝ := fun ε ↦ scalarStepOne a₁ b₁ ε (-ε)
  let p₂ : ℝ → ℝ := fun ε ↦ scalarStepZero a₂ b₂ (p₁ ε) (q₁ ε)
  let q₂ : ℝ → ℝ := fun ε ↦ scalarStepOne a₂ b₂ (p₁ ε) (q₁ ε)
  let p₂' : ℝ → ℝ := fun ε ↦ scalarStepZero a₂' b₂' (p₁ ε) (q₁ ε)
  let q₂' : ℝ → ℝ := fun ε ↦ scalarStepOne a₂' b₂' (p₁ ε) (q₁ ε)
  let s₃ : ℝ → ℝ := fun ε ↦ ε ^ 3
  let s₆ : ℝ → ℝ := fun ε ↦ ε ^ 6
  have hp₁ : Filter.Tendsto p₁ F (nhds 0) := tendsto_first_scalarStep_zero a₁ b₁ 0
  have hq₁ : Filter.Tendsto q₁ F (nhds 0) := tendsto_first_scalarStep_zero a₁ b₁ 1
  have hs₃ : Filter.Tendsto s₃ F (nhds 0) := by
    have hc : ContinuousAt s₃ 0 := by dsimp [s₃]; fun_prop
    simpa [s₃] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hgap₁ : Filter.Tendsto (fun ε ↦ (p₁ ε - q₁ ε) / s₃ ε) F
      (nhds (2 * b₁)) := tendsto_first_scalar_gap_cubic a₁ b₁
  have hs₃ne : ∀ᶠ ε in F, s₃ ε ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact pow_ne_zero 3 hε
  have hp₂ : Filter.Tendsto p₂ F (nhds 0) := by
    exact tendsto_scalarStep_zero a₂ b₂ p₁ q₁ hp₁ hq₁ 0
  have hq₂ : Filter.Tendsto q₂ F (nhds 0) := by
    exact tendsto_scalarStep_zero a₂ b₂ p₁ q₁ hp₁ hq₁ 1
  have hp₂' : Filter.Tendsto p₂' F (nhds 0) := by
    exact tendsto_scalarStep_zero a₂' b₂' p₁ q₁ hp₁ hq₁ 0
  have hq₂' : Filter.Tendsto q₂' F (nhds 0) := by
    exact tendsto_scalarStep_zero a₂' b₂' p₁ q₁ hp₁ hq₁ 1
  have hcross0 : Filter.Tendsto (fun ε ↦ (p₂ ε - p₂' ε) / s₆ ε) F
      (nhds (b₁ ^ 2 * (a₂ - a₂'))) := by
    simpa [p₂, p₂', s₆] using
      tendsto_second_scalar_comparison_sixth a₁ b₁ a₂ b₂ a₂' b₂' 0
  have hcross1 : Filter.Tendsto (fun ε ↦ (q₂ ε - q₂' ε) / s₆ ε) F
      (nhds (b₁ ^ 2 * (a₂ - a₂'))) := by
    simpa [q₂, q₂', s₆] using
      tendsto_second_scalar_comparison_sixth a₁ b₁ a₂ b₂ a₂' b₂' 1
  have hgap9 : Filter.Tendsto (fun ε ↦ (p₂ ε - q₂ ε) / (s₃ ε) ^ 3) F
      (nhds ((2 * b₁) ^ 3 * b₂ / 4)) :=
    tendsto_scalar_gap_cubic a₂ b₂ p₁ q₁ s₃ (2 * b₁)
      hp₁ hq₁ hs₃ hgap₁ hs₃ne
  have hgap9' : Filter.Tendsto (fun ε ↦ (p₂' ε - q₂' ε) / (s₃ ε) ^ 3) F
      (nhds ((2 * b₁) ^ 3 * b₂' / 4)) :=
    tendsto_scalar_gap_cubic a₂' b₂' p₁ q₁ s₃ (2 * b₁)
      hp₁ hq₁ hs₃ hgap₁ hs₃ne
  have he3 : Filter.Tendsto (fun ε : ℝ ↦ ε ^ 3) F (nhds 0) := hs₃
  have hgap6 : Filter.Tendsto (fun ε ↦ (p₂ ε - q₂ ε) / s₆ ε) F (nhds 0) := by
    have hp := he3.mul hgap9
    have heq : (fun ε ↦ (p₂ ε - q₂ ε) / s₆ ε) =ᶠ[F]
        fun ε ↦ ε ^ 3 * ((p₂ ε - q₂ ε) / (s₃ ε) ^ 3) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : ε ≠ 0 := hε
      dsimp [s₃, s₆]
      field_simp [hε0]
    have hp0 : Filter.Tendsto
        (fun ε ↦ ε ^ 3 * ((p₂ ε - q₂ ε) / (s₃ ε) ^ 3)) F (nhds 0) := by
      convert hp using 1 <;> norm_num
    exact hp0.congr' heq.symm
  have hgap6' : Filter.Tendsto (fun ε ↦ (p₂' ε - q₂' ε) / s₆ ε) F (nhds 0) := by
    have hp := he3.mul hgap9'
    have heq : (fun ε ↦ (p₂' ε - q₂' ε) / s₆ ε) =ᶠ[F]
        fun ε ↦ ε ^ 3 * ((p₂' ε - q₂' ε) / (s₃ ε) ^ 3) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : ε ≠ 0 := hε
      dsimp [s₃, s₆]
      field_simp [hε0]
    have hp0 : Filter.Tendsto
        (fun ε ↦ ε ^ 3 * ((p₂' ε - q₂' ε) / (s₃ ε) ^ 3)) F (nhds 0) := by
      convert hp using 1 <;> norm_num
    exact hp0.congr' heq.symm
  have hs₆ne : ∀ᶠ ε in F, s₆ ε ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact pow_ne_zero 6 hε
  exact tendsto_scalarStep_preserves_common_comparison a₃ b₃ a₃' b₃'
    p₂ q₂ p₂' q₂' s₆ (b₁ ^ 2 * (a₂ - a₂'))
    hp₂ hq₂ hp₂' hq₂' hcross0 hcross1 hgap6 hgap6' hs₆ne i

end NormalizedDeepAttention
