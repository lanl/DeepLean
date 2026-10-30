module

public import DeepLean.Attention.Multiplicity

/-! # Multiplicity-weighted scalar hierarchy -/

@[expose] public section

namespace NormalizedDeepAttention

noncomputable def weightedSecantFactor (n a b : ℝ) : ℝ :=
  n * Real.exp b * dslope Real.exp 0 (a - b) /
    ((Real.exp a + n) * (Real.exp b + n))

theorem weightedSigmoid_sub_factor (n a b : ℝ) (hn : 0 < n) :
    weightedSigmoid n a - weightedSigmoid n b =
      (a - b) * weightedSecantFactor n a b := by
  have ha : Real.exp a + n ≠ 0 := by positivity
  have hb : Real.exp b + n ≠ 0 := by positivity
  have he : (a - b) * dslope Real.exp 0 (a - b) = Real.exp (a - b) - 1 := by
    have h := sub_smul_dslope Real.exp 0 (a - b)
    simpa only [sub_zero, smul_eq_mul, Real.exp_zero] using h
  have heab : Real.exp a = Real.exp b * Real.exp (a - b) := by
    rw [Real.exp_sub]
    field_simp [Real.exp_ne_zero]
  unfold weightedSigmoid weightedSecantFactor
  field_simp [ha, hb]
  rw [heab]
  rw [show n * Real.exp b * (a - b) * dslope Real.exp 0 (a - b) =
    n * Real.exp b * ((a - b) * dslope Real.exp 0 (a - b)) by ring, he]
  ring

theorem tendsto_weightedSecantFactor_zero {α : Type*} {F : Filter α}
    (n : ℝ) {a b : α → ℝ}
    (ha : Filter.Tendsto a F (nhds 0)) (hb : Filter.Tendsto b F (nhds 0))
    (hn : 0 < n) :
    Filter.Tendsto (fun z ↦ weightedSecantFactor n (a z) (b z)) F
      (nhds (n / (1+n)^2)) := by
  have hab : Filter.Tendsto (fun z ↦ a z-b z) F (nhds 0) := by simpa using ha.sub hb
  have hds : Filter.Tendsto (fun z ↦ dslope Real.exp 0 (a z-b z)) F (nhds 1) := by
    have hc : ContinuousAt (dslope Real.exp 0) 0 :=
      continuousAt_dslope_same.mpr (Real.hasDerivAt_exp 0).differentiableAt
    have hv : dslope Real.exp 0 0 = (1:ℝ) := by
      rw [dslope_same, (Real.hasDerivAt_exp 0).deriv, Real.exp_zero]
    rw [← hv]
    exact hc.tendsto.comp hab
  have hea : Filter.Tendsto (fun z ↦ Real.exp (a z)) F (nhds 1) := by
    simpa [Function.comp_def] using (Real.hasDerivAt_exp 0).continuousAt.tendsto.comp ha
  have heb : Filter.Tendsto (fun z ↦ Real.exp (b z)) F (nhds 1) := by
    simpa [Function.comp_def] using (Real.hasDerivAt_exp 0).continuousAt.tendsto.comp hb
  have hnum : Filter.Tendsto
      (fun z ↦ n * Real.exp (b z) * dslope Real.exp 0 (a z-b z)) F (nhds n) := by
    convert ((tendsto_const_nhds : Filter.Tendsto (fun _ : α ↦ n) F (nhds n)).mul heb).mul hds
      using 1 <;> ring
  have hden := (hea.add_const n).mul (heb.add_const n)
  have hdiv := hnum.div hden (by positivity : (1+n)*(1+n) ≠ 0)
  convert hdiv using 1
  · rfl
  · ring

theorem tendsto_weightedSigmoid_sub_div {α : Type*} {F : Filter α}
    (n : ℝ) (a b scale : α → ℝ) (c : ℝ)
    (hn : 0 < n)
    (ha : Filter.Tendsto a F (nhds 0)) (hb : Filter.Tendsto b F (nhds 0))
    (hquot : Filter.Tendsto (fun z ↦ (a z - b z) / scale z) F (nhds c))
    (hscale : ∀ᶠ z in F, scale z ≠ 0) :
    Filter.Tendsto (fun z ↦
      (weightedSigmoid n (a z) - weightedSigmoid n (b z)) / scale z) F
      (nhds (c * (n / (1 + n) ^ 2))) := by
  have hf := tendsto_weightedSecantFactor_zero n ha hb hn
  have hp := hquot.mul hf
  apply Filter.Tendsto.congr' _ hp
  filter_upwards [hscale] with z hz
  rw [weightedSigmoid_sub_factor n _ _ hn]
  field_simp [hz]

theorem weightedStep_gap_ne_zero (n a b p q : ℝ) (hn : 0 < n)
    (hpq : p - q ≠ 0) (hb : b ≠ 0) :
    weightedStepFirst n a b p q - weightedStepRepeated n a b p q ≠ 0 := by
  intro hz
  have hprod : (weightedSigmoid n ((p-q)*(a+p*b)) -
      weightedSigmoid n ((p-q)*(a+q*b))) * (p-q) = 0 := by
    dsimp [weightedStepFirst, weightedStepRepeated] at hz
    linarith
  have hsig : weightedSigmoid n ((p-q)*(a+p*b)) =
      weightedSigmoid n ((p-q)*(a+q*b)) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hpq)
  have hlogit := weightedSigmoid_injective hn hsig
  have : (p-q)^2*b = 0 := by nlinarith
  exact (mul_ne_zero (pow_ne_zero 2 hpq) hb) this

theorem tendsto_weightedPairStep_zero {α : Type*} {F : Filter α}
    (n a b : ℝ) (z : α → ScalarPair) (hn : 0 < n)
    (hz0 : Filter.Tendsto (fun x ↦ (z x).1) F (nhds 0))
    (hz1 : Filter.Tendsto (fun x ↦ (z x).2) F (nhds 0)) (i : Fin 2) :
    Filter.Tendsto (fun x ↦ scalarAt (weightedPairStep n (a,b) (z x)).1
      (weightedPairStep n (a,b) (z x)).2 i) F (nhds 0) := by
  have hgap := hz0.sub hz1
  have hcoord : Filter.Tendsto (fun x ↦ scalarAt (z x).1 (z x).2 i) F (nhds 0) := by
    fin_cases i
    · simpa using hz0
    · simpa using hz1
  let logit : α → ℝ := fun x ↦ ((z x).1-(z x).2) *
    (a + scalarAt (z x).1 (z x).2 i*b)
  have hlogit : Filter.Tendsto logit F (nhds 0) := by
    have hi : Filter.Tendsto (fun x ↦ a + scalarAt (z x).1 (z x).2 i*b) F
        (nhds a) := by simpa using tendsto_const_nhds.add (hcoord.mul_const b)
    simpa [logit] using hgap.mul hi
  have hs : Filter.Tendsto (fun x ↦ weightedSigmoid n (logit x)) F
      (nhds (1/(1+n))) := by
    have hc : ContinuousAt (weightedSigmoid n) 0 := by
      unfold weightedSigmoid
      exact (Real.hasDerivAt_exp 0).continuousAt.div
        ((Real.hasDerivAt_exp 0).continuousAt.add continuousAt_const) (by positivity)
    simpa [Function.comp_def] using hc.tendsto.comp hlogit
  have hlim := hz1.add (hs.mul hgap)
  have heq : (fun x ↦ scalarAt (weightedPairStep n (a,b) (z x)).1
      (weightedPairStep n (a,b) (z x)).2 i) =
      fun x ↦ (z x).2 + weightedSigmoid n (logit x) * ((z x).1-(z x).2) := by
    funext x
    fin_cases i <;> simp [weightedPairStep, weightedStepFirst,
      weightedStepRepeated, logit]
  rw [heq]
  simpa using hlim

theorem tendsto_weighted_gap_cubic {α : Type*} {F : Filter α}
    (n a b : ℝ) (p q scale : α → ℝ) (c : ℝ) (hn : 0 < n)
    (hp : Filter.Tendsto p F (nhds 0)) (hq : Filter.Tendsto q F (nhds 0))
    (hs : Filter.Tendsto scale F (nhds 0))
    (hgap : Filter.Tendsto (fun z ↦ (p z - q z) / scale z) F (nhds c))
    (hscale : ∀ᶠ z in F, scale z ≠ 0) :
    Filter.Tendsto (fun z ↦
      (weightedStepFirst n a b (p z) (q z) -
        weightedStepRepeated n a b (p z) (q z))/(scale z)^3) F
      (nhds (c^3*b*(n/(1+n)^2))) := by
  let gap : α → ℝ := fun z ↦ p z-q z
  let z0 : α → ℝ := fun z ↦ gap z*(a+p z*b)
  let z1 : α → ℝ := fun z ↦ gap z*(a+q z*b)
  have hgap0 : Filter.Tendsto gap F (nhds 0) := by
    simpa [gap] using hp.sub hq
  have hz0 : Filter.Tendsto z0 F (nhds 0) := by
    have hi : Filter.Tendsto (fun z ↦ a+p z*b) F (nhds a) := by
      simpa using tendsto_const_nhds.add (hp.mul_const b)
    simpa [z0] using hgap0.mul hi
  have hz1 : Filter.Tendsto z1 F (nhds 0) := by
    have hi : Filter.Tendsto (fun z ↦ a+q z*b) F (nhds a) := by
      simpa using tendsto_const_nhds.add (hq.mul_const b)
    simpa [z1] using hgap0.mul hi
  have hf := tendsto_weightedSecantFactor_zero n hz0 hz1 hn
  have hlim := (((hgap.mul hgap).mul hgap).mul_const b).mul hf
  have heq : (fun z ↦
      (weightedStepFirst n a b (p z) (q z) -
        weightedStepRepeated n a b (p z) (q z))/(scale z)^3) =ᶠ[F]
      fun z ↦ (((gap z/scale z)^3*b) * weightedSecantFactor n (z0 z) (z1 z)) := by
    filter_upwards [hscale] with z hz
    rw [show weightedStepFirst n a b (p z) (q z) -
        weightedStepRepeated n a b (p z) (q z) =
        (weightedSigmoid n (z0 z)-weightedSigmoid n (z1 z))*gap z by
      dsimp [weightedStepFirst, weightedStepRepeated, z0, z1, gap]
      ring,
      weightedSigmoid_sub_factor n _ _ hn]
    have hl : z0 z-z1 z = gap z^2*b := by dsimp [z0,z1,gap]; ring
    rw [hl]
    field_simp [hz]
  apply Filter.Tendsto.congr' heq.symm
  have hlim' : Filter.Tendsto
      (fun z ↦ (((gap z/scale z)^3*b) * weightedSecantFactor n (z0 z) (z1 z))) F
      (nhds (c^3*b*(n/(1+n)^2))) := by
    convert hlim using 1
    · funext z
      dsimp [gap]
      ring
    · ring
  exact hlim'

theorem tendsto_weightedStep_comparison {α : Type*} {F : Filter α}
    (n a b a' b' : ℝ) (p q scale : α → ℝ) (c : ℝ) (hn : 0 < n)
    (hp : Filter.Tendsto p F (nhds 0)) (hq : Filter.Tendsto q F (nhds 0))
    (hs : Filter.Tendsto scale F (nhds 0))
    (hgap : Filter.Tendsto (fun z ↦ (p z - q z) / scale z) F (nhds c))
    (hscale : ∀ᶠ z in F, scale z ≠ 0) (i : Fin 2) :
    let step := fun a b p q ↦ scalarAt (weightedStepFirst n a b p q)
      (weightedStepRepeated n a b p q) i
    Filter.Tendsto (fun z ↦
      (step a b (p z) (q z)-step a' b' (p z) (q z))/(scale z)^2) F
      (nhds (c^2*(a-a')*(n/(1+n)^2))) := by
  dsimp only
  let gap : α → ℝ := fun z ↦ p z-q z
  let coord : α → ℝ := fun z ↦ scalarAt (p z) (q z) i
  let z0 : α → ℝ := fun z ↦ gap z*(a+coord z*b)
  let z1 : α → ℝ := fun z ↦ gap z*(a'+coord z*b')
  have hc : Filter.Tendsto coord F (nhds 0) := by
    fin_cases i
    · simpa [coord] using hp
    · simpa [coord] using hq
  have hg0 : Filter.Tendsto gap F (nhds 0) := by simpa [gap] using hp.sub hq
  have hz0 : Filter.Tendsto z0 F (nhds 0) := by
    have hi : Filter.Tendsto (fun z ↦ a+coord z*b) F (nhds a) := by
      simpa using tendsto_const_nhds.add (hc.mul_const b)
    simpa [z0] using hg0.mul hi
  have hz1 : Filter.Tendsto z1 F (nhds 0) := by
    have hi : Filter.Tendsto (fun z ↦ a'+coord z*b') F (nhds a') := by
      simpa using tendsto_const_nhds.add (hc.mul_const b')
    simpa [z1] using hg0.mul hi
  have hzq : Filter.Tendsto (fun z ↦ (z0 z-z1 z)/scale z) F
      (nhds (c*(a-a'))) := by
    have hi : Filter.Tendsto (fun z ↦ (a-a')+coord z*(b-b')) F (nhds (a-a')) := by
      simpa using tendsto_const_nhds.add (hc.mul_const (b-b'))
    have h := hgap.mul hi
    apply Filter.Tendsto.congr' _ h
    filter_upwards [hscale] with z hz
    dsimp [z0,z1,gap]
    field_simp [hz]
    ring
  have hw := tendsto_weightedSigmoid_sub_div n z0 z1 scale (c*(a-a')) hn
    hz0 hz1 hzq hscale
  have hlim := hw.mul hgap
  have heq : (fun z ↦
      (scalarAt (weightedStepFirst n a b (p z) (q z))
          (weightedStepRepeated n a b (p z) (q z)) i -
        scalarAt (weightedStepFirst n a' b' (p z) (q z))
          (weightedStepRepeated n a' b' (p z) (q z)) i)/(scale z)^2) =ᶠ[F]
      fun z ↦ ((weightedSigmoid n (z0 z)-weightedSigmoid n (z1 z))/scale z) *
        (gap z/scale z) := by
    filter_upwards [hscale] with z hz
    fin_cases i <;> simp only [scalarAt_zero, scalarAt_one] <;>
      dsimp [weightedStepFirst, weightedStepRepeated,z0,z1,coord,gap] <;>
      simp only [scalarAt_zero,scalarAt_one] <;> field_simp [hz] <;> ring
  apply Filter.Tendsto.congr' heq.symm
  convert hlim using 1 <;> ring

theorem tendsto_weightedStep_gap_of_gap_zero {α : Type*} {F : Filter α}
    (n a b : ℝ) (p q scale : α → ℝ) (hn : 0 < n)
    (hp : Filter.Tendsto p F (nhds 0)) (hq : Filter.Tendsto q F (nhds 0))
    (hgap : Filter.Tendsto (fun x ↦ (p x - q x) / scale x) F (nhds 0))
    (hscale : ∀ᶠ x in F, scale x ≠ 0) :
    Filter.Tendsto (fun x ↦
      (weightedStepFirst n a b (p x) (q x) -
        weightedStepRepeated n a b (p x) (q x)) / scale x) F (nhds 0) := by
  let gap : α → ℝ := fun x ↦ p x - q x
  let z0 : α → ℝ := fun x ↦ gap x * (a + p x * b)
  let z1 : α → ℝ := fun x ↦ gap x * (a + q x * b)
  have hgap0 : Filter.Tendsto gap F (nhds 0) := by simpa [gap] using hp.sub hq
  have hz0 : Filter.Tendsto z0 F (nhds 0) := by
    have hi : Filter.Tendsto (fun x ↦ a + p x * b) F (nhds a) := by
      simpa using tendsto_const_nhds.add (hp.mul_const b)
    simpa [z0] using hgap0.mul hi
  have hz1 : Filter.Tendsto z1 F (nhds 0) := by
    have hi : Filter.Tendsto (fun x ↦ a + q x * b) F (nhds a) := by
      simpa using tendsto_const_nhds.add (hq.mul_const b)
    simpa [z1] using hgap0.mul hi
  have hs0 : Filter.Tendsto (fun x ↦ weightedSigmoid n (z0 x)) F
      (nhds (1 / (1+n))) := by
    have hc : ContinuousAt (weightedSigmoid n) 0 := by
      unfold weightedSigmoid
      exact (Real.hasDerivAt_exp 0).continuousAt.div
        ((Real.hasDerivAt_exp 0).continuousAt.add continuousAt_const) (by positivity)
    simpa [Function.comp_def] using hc.tendsto.comp hz0
  have hs1 : Filter.Tendsto (fun x ↦ weightedSigmoid n (z1 x)) F
      (nhds (1 / (1+n))) := by
    have hc : ContinuousAt (weightedSigmoid n) 0 := by
      unfold weightedSigmoid
      exact (Real.hasDerivAt_exp 0).continuousAt.div
        ((Real.hasDerivAt_exp 0).continuousAt.add continuousAt_const) (by positivity)
    simpa [Function.comp_def] using hc.tendsto.comp hz1
  have hlim := (hs0.sub hs1).mul hgap
  have heq : (fun x ↦
      (weightedStepFirst n a b (p x) (q x) -
        weightedStepRepeated n a b (p x) (q x)) / scale x) =ᶠ[F]
      fun x ↦ (weightedSigmoid n (z0 x) - weightedSigmoid n (z1 x)) *
        ((p x - q x) / scale x) := by
    filter_upwards [hscale] with x hx
    dsimp [weightedStepFirst, weightedStepRepeated, z0, z1, gap]
    field_simp [hx]
    ring
  apply Filter.Tendsto.congr' heq.symm
  simpa using hlim

theorem tendsto_weightedStep_preserves_common_comparison {α : Type*} {F : Filter α}
    (n a b a' b' : ℝ) (p q p' q' scale : α → ℝ) (w : ℝ) (hn : 0 < n)
    (hp : Filter.Tendsto p F (nhds 0)) (hq : Filter.Tendsto q F (nhds 0))
    (hp' : Filter.Tendsto p' F (nhds 0)) (hq' : Filter.Tendsto q' F (nhds 0))
    (_hpp' : Filter.Tendsto (fun z ↦ (p z - p' z) / scale z) F (nhds w))
    (hqq' : Filter.Tendsto (fun z ↦ (q z - q' z) / scale z) F (nhds w))
    (hgap : Filter.Tendsto (fun z ↦ (p z - q z) / scale z) F (nhds 0))
    (hgap' : Filter.Tendsto (fun z ↦ (p' z - q' z) / scale z) F (nhds 0))
    (hscale : ∀ᶠ z in F, scale z ≠ 0) (i : Fin 2) :
    Filter.Tendsto (fun z ↦
      (scalarAt (weightedStepFirst n a b (p z) (q z))
          (weightedStepRepeated n a b (p z) (q z)) i -
        scalarAt (weightedStepFirst n a' b' (p' z) (q' z))
          (weightedStepRepeated n a' b' (p' z) (q' z)) i) / scale z) F
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
      simpa using tendsto_const_nhds.add (hcoord.mul_const b)
    simpa [logit] using hgap0.mul hinner
  have hlogit' : Filter.Tendsto logit' F (nhds 0) := by
    have hinner : Filter.Tendsto (fun z ↦ a' + coord' z * b') F (nhds a') := by
      simpa using tendsto_const_nhds.add (hcoord'.mul_const b')
    simpa [logit'] using hgap0'.mul hinner
  have hsig : Filter.Tendsto (fun z ↦ weightedSigmoid n (logit z)) F
      (nhds (1/(1+n))) := by
    have hc : ContinuousAt (weightedSigmoid n) 0 := by
      unfold weightedSigmoid
      exact (Real.hasDerivAt_exp 0).continuousAt.div
        ((Real.hasDerivAt_exp 0).continuousAt.add continuousAt_const) (by positivity)
    simpa [Function.comp_def] using hc.tendsto.comp hlogit
  have hsig' : Filter.Tendsto (fun z ↦ weightedSigmoid n (logit' z)) F
      (nhds (1/(1+n))) := by
    have hc : ContinuousAt (weightedSigmoid n) 0 := by
      unfold weightedSigmoid
      exact (Real.hasDerivAt_exp 0).continuousAt.div
        ((Real.hasDerivAt_exp 0).continuousAt.add continuousAt_const) (by positivity)
    simpa [Function.comp_def] using hc.tendsto.comp hlogit'
  have hlim := hqq'.add ((hsig.mul hgap).sub (hsig'.mul hgap'))
  have heq : (fun z ↦
      (scalarAt (weightedStepFirst n a b (p z) (q z))
          (weightedStepRepeated n a b (p z) (q z)) i -
        scalarAt (weightedStepFirst n a' b' (p' z) (q' z))
          (weightedStepRepeated n a' b' (p' z) (q' z)) i) / scale z) =ᶠ[F]
      fun z ↦ (q z - q' z) / scale z +
        (weightedSigmoid n (logit z) * ((p z - q z) / scale z) -
          weightedSigmoid n (logit' z) * ((p' z - q' z) / scale z)) := by
    filter_upwards [hscale] with z hz
    fin_cases i <;> simp only [scalarAt_zero, scalarAt_one] <;>
      dsimp [weightedStepFirst, weightedStepRepeated, logit, logit', coord, coord',
        gap, gap'] <;> simp only [scalarAt_zero, scalarAt_one] <;>
      field_simp [hz] <;> ring
  apply Filter.Tendsto.congr' heq.symm
  simpa using hlim

theorem tendsto_weightedRun_zero {α : Type*} {F : Filter α}
    (n : ℝ) (θs : List ScalarParameter) (z : α → ScalarPair) (hn : 0 < n)
    (hz0 : Filter.Tendsto (fun x ↦ (z x).1) F (nhds 0))
    (hz1 : Filter.Tendsto (fun x ↦ (z x).2) F (nhds 0)) (i : Fin 2) :
    Filter.Tendsto (fun x ↦ scalarAt (weightedRun n θs (z x)).1
      (weightedRun n θs (z x)).2 i) F (nhds 0) := by
  induction θs generalizing z with
  | nil =>
      fin_cases i
      · simpa using hz0
      · simpa using hz1
  | cons θ θs ih =>
      have h0 := tendsto_weightedPairStep_zero n θ.1 θ.2 z hn hz0 hz1 0
      have h1 := tendsto_weightedPairStep_zero n θ.1 θ.2 z hn hz0 hz1 1
      simpa only [weightedRun_cons] using
        ih (fun x ↦ weightedPairStep n θ (z x)) h0 h1

theorem weightedRun_gap_ne_zero (n : ℝ) (θs : List ScalarParameter) (z : ScalarPair)
    (hn : 0 < n) (hz : z.1 - z.2 ≠ 0) (hb : ∀ θ ∈ θs, θ.2 ≠ 0) :
    (weightedRun n θs z).1 - (weightedRun n θs z).2 ≠ 0 := by
  induction θs generalizing z with
  | nil => simpa using hz
  | cons θ θs ih =>
      apply ih (weightedPairStep n θ z)
      · simpa [weightedPairStep] using
          weightedStep_gap_ne_zero n θ.1 θ.2 z.1 z.2 hn hz (hb θ (by simp))
      · intro η hη
        exact hb η (by simp [hη])

theorem tendsto_weightedRun_preserves_common_comparison {α : Type*} {F : Filter α}
    (n : ℝ) (θs θs' : List ScalarParameter) (hlen : θs.length = θs'.length)
    (z z' : α → ScalarPair) (scale : α → ℝ) (w : ℝ) (hn : 0 < n)
    (hz0 : Filter.Tendsto (fun x ↦ (z x).1) F (nhds 0))
    (hz1 : Filter.Tendsto (fun x ↦ (z x).2) F (nhds 0))
    (hz0' : Filter.Tendsto (fun x ↦ (z' x).1) F (nhds 0))
    (hz1' : Filter.Tendsto (fun x ↦ (z' x).2) F (nhds 0))
    (hcross0 : Filter.Tendsto (fun x ↦ ((z x).1 - (z' x).1) / scale x) F
      (nhds w))
    (hcross1 : Filter.Tendsto (fun x ↦ ((z x).2 - (z' x).2) / scale x) F
      (nhds w))
    (hgap : Filter.Tendsto (fun x ↦ ((z x).1 - (z x).2) / scale x) F (nhds 0))
    (hgap' : Filter.Tendsto (fun x ↦ ((z' x).1 - (z' x).2) / scale x) F (nhds 0))
    (hscale : ∀ᶠ x in F, scale x ≠ 0) (i : Fin 2) :
    Filter.Tendsto (fun x ↦
      (scalarAt (weightedRun n θs (z x)).1 (weightedRun n θs (z x)).2 i -
       scalarAt (weightedRun n θs' (z' x)).1 (weightedRun n θs' (z' x)).2 i) /
        scale x) F (nhds w) := by
  induction θs generalizing θs' z z' with
  | nil =>
      cases θs' with
      | nil =>
          fin_cases i
          · simpa using hcross0
          · simpa using hcross1
      | cons _ _ => simp at hlen
  | cons θ θs ih =>
      cases θs' with
      | nil => simp at hlen
      | cons θ' θs' =>
          have hlen' : θs.length = θs'.length := by simpa using hlen
          let y : α → ScalarPair := fun x ↦ weightedPairStep n θ (z x)
          let y' : α → ScalarPair := fun x ↦ weightedPairStep n θ' (z' x)
          have hy0 := tendsto_weightedPairStep_zero n θ.1 θ.2 z hn hz0 hz1 0
          have hy1 := tendsto_weightedPairStep_zero n θ.1 θ.2 z hn hz0 hz1 1
          have hy0' := tendsto_weightedPairStep_zero n θ'.1 θ'.2 z' hn hz0' hz1' 0
          have hy1' := tendsto_weightedPairStep_zero n θ'.1 θ'.2 z' hn hz0' hz1' 1
          have hcross0' := tendsto_weightedStep_preserves_common_comparison
            n θ.1 θ.2 θ'.1 θ'.2 (fun x ↦ (z x).1) (fun x ↦ (z x).2)
            (fun x ↦ (z' x).1) (fun x ↦ (z' x).2) scale w hn
            hz0 hz1 hz0' hz1' hcross0 hcross1 hgap hgap' hscale 0
          have hcross1' := tendsto_weightedStep_preserves_common_comparison
            n θ.1 θ.2 θ'.1 θ'.2 (fun x ↦ (z x).1) (fun x ↦ (z x).2)
            (fun x ↦ (z' x).1) (fun x ↦ (z' x).2) scale w hn
            hz0 hz1 hz0' hz1' hcross0 hcross1 hgap hgap' hscale 1
          have hgapY := tendsto_weightedStep_gap_of_gap_zero n θ.1 θ.2
            (fun x ↦ (z x).1) (fun x ↦ (z x).2) scale hn hz0 hz1 hgap hscale
          have hgapY' := tendsto_weightedStep_gap_of_gap_zero n θ'.1 θ'.2
            (fun x ↦ (z' x).1) (fun x ↦ (z' x).2) scale hn hz0' hz1' hgap' hscale
          simpa only [weightedRun_cons, y, y', weightedPairStep] using
            ih θs' hlen' y y' hy0 hy1 hy0' hy1' hcross0' hcross1' hgapY hgapY'

theorem tendsto_weightedRun_next_comparison {α : Type*} {F : Filter α}
    (n a b a' b' : ℝ) (θs θs' : List ScalarParameter)
    (hlen : θs.length = θs'.length) (p q scale : α → ℝ) (hn : 0 < n)
    (hp : Filter.Tendsto p F (nhds 0)) (hq : Filter.Tendsto q F (nhds 0))
    (hs : Filter.Tendsto scale F (nhds 0))
    (hgap : Filter.Tendsto (fun x ↦ (p x - q x) / scale x) F (nhds 1))
    (hscale : ∀ᶠ x in F, scale x ≠ 0) (i : Fin 2) :
    let y := fun x ↦ weightedPairStep n (a, b) (p x, q x)
    let y' := fun x ↦ weightedPairStep n (a', b') (p x, q x)
    Filter.Tendsto (fun x ↦
      (scalarAt (weightedRun n θs (y x)).1 (weightedRun n θs (y x)).2 i -
       scalarAt (weightedRun n θs' (y' x)).1 (weightedRun n θs' (y' x)).2 i) /
        (scale x)^2) F (nhds ((a-a') * (n/(1+n)^2))) := by
  dsimp only
  let y : α → ScalarPair := fun x ↦ weightedPairStep n (a,b) (p x,q x)
  let y' : α → ScalarPair := fun x ↦ weightedPairStep n (a',b') (p x,q x)
  have hy0 := tendsto_weightedPairStep_zero n a b (fun x ↦ (p x,q x)) hn hp hq 0
  have hy1 := tendsto_weightedPairStep_zero n a b (fun x ↦ (p x,q x)) hn hp hq 1
  have hy0' := tendsto_weightedPairStep_zero n a' b' (fun x ↦ (p x,q x)) hn hp hq 0
  have hy1' := tendsto_weightedPairStep_zero n a' b' (fun x ↦ (p x,q x)) hn hp hq 1
  have hc0 : Filter.Tendsto (fun x ↦ ((y x).1 - (y' x).1) / (scale x)^2) F
      (nhds ((a-a')*(n/(1+n)^2))) := by
    simpa [y, y', weightedPairStep] using
      tendsto_weightedStep_comparison n a b a' b' p q scale 1 hn
        hp hq hs hgap hscale 0
  have hc1 : Filter.Tendsto (fun x ↦ ((y x).2 - (y' x).2) / (scale x)^2) F
      (nhds ((a-a')*(n/(1+n)^2))) := by
    simpa [y, y', weightedPairStep] using
      tendsto_weightedStep_comparison n a b a' b' p q scale 1 hn
        hp hq hs hgap hscale 1
  have hg3 := tendsto_weighted_gap_cubic n a b p q scale 1 hn hp hq hs hgap hscale
  have hg3' := tendsto_weighted_gap_cubic n a' b' p q scale 1 hn hp hq hs hgap hscale
  have hg2 : Filter.Tendsto (fun x ↦ ((y x).1 - (y x).2) / (scale x)^2) F
      (nhds 0) := by
    have h := hs.mul hg3
    apply Filter.Tendsto.congr' _ (by simpa [y, weightedPairStep] using h)
    filter_upwards [hscale] with x hx
    dsimp [y, weightedPairStep]
    field_simp [hx]
  have hg2' : Filter.Tendsto (fun x ↦ ((y' x).1 - (y' x).2) / (scale x)^2) F
      (nhds 0) := by
    have h := hs.mul hg3'
    apply Filter.Tendsto.congr' _ (by simpa [y', weightedPairStep] using h)
    filter_upwards [hscale] with x hx
    dsimp [y', weightedPairStep]
    field_simp [hx]
  have hs2 : ∀ᶠ x in F, (scale x)^2 ≠ 0 := by
    filter_upwards [hscale] with x hx
    exact pow_ne_zero 2 hx
  simpa [y, y', weightedPairStep] using
    tendsto_weightedRun_preserves_common_comparison n θs θs' hlen y y'
      (fun x ↦ (scale x)^2) ((a-a')*(n/(1+n)^2)) hn
      hy0 hy1 hy0' hy1' hc0 hc1 hg2 hg2' hs2 i

end NormalizedDeepAttention
