module

public import DeepLean.Attention.Hierarchy

/-!
# Finite-depth scalar hierarchy

This file packages the two-token affine-line calculation into list operations.
The key point is to use the exact gap emitted by a known prefix as the local
scale.  The next score is visible at the square of this gap, while all later
within-pair gaps are negligible at that scale.
-/

@[expose] public section

namespace NormalizedDeepAttention

abbrev ScalarPair := ℝ × ℝ
abbrev ScalarParameter := ℝ × ℝ

noncomputable def scalarPairStep (θ : ScalarParameter) (z : ScalarPair) : ScalarPair :=
  (scalarStepZero θ.1 θ.2 z.1 z.2, scalarStepOne θ.1 θ.2 z.1 z.2)

noncomputable def scalarRun : List ScalarParameter → ScalarPair → ScalarPair
  | [], z => z
  | θ :: θs, z => scalarRun θs (scalarPairStep θ z)

@[simp] theorem scalarRun_nil (z : ScalarPair) : scalarRun [] z = z := rfl

@[simp] theorem scalarRun_cons (θ : ScalarParameter) (θs : List ScalarParameter)
    (z : ScalarPair) : scalarRun (θ :: θs) z = scalarRun θs (scalarPairStep θ z) := rfl

@[simp] theorem scalarPairStep_fst (a b p q : ℝ) :
    (scalarPairStep (a, b) (p, q)).1 = scalarStepZero a b p q := rfl

@[simp] theorem scalarPairStep_snd (a b p q : ℝ) :
    (scalarPairStep (a, b) (p, q)).2 = scalarStepOne a b p q := rfl

theorem tendsto_scalarPairStep_zero {α : Type*} {F : Filter α}
    (a b : ℝ) (z : α → ScalarPair)
    (hz0 : Filter.Tendsto (fun x ↦ (z x).1) F (nhds 0))
    (hz1 : Filter.Tendsto (fun x ↦ (z x).2) F (nhds 0)) (i : Fin 2) :
    Filter.Tendsto (fun x ↦ scalarAt (scalarPairStep (a, b) (z x)).1
      (scalarPairStep (a, b) (z x)).2 i) F (nhds 0) := by
  simpa [scalarPairStep] using tendsto_scalarStep_zero a b
    (fun x ↦ (z x).1) (fun x ↦ (z x).2)
    hz0 hz1 i

theorem tendsto_scalarRun_zero {α : Type*} {F : Filter α}
    (θs : List ScalarParameter) (z : α → ScalarPair)
    (hz0 : Filter.Tendsto (fun x ↦ (z x).1) F (nhds 0))
    (hz1 : Filter.Tendsto (fun x ↦ (z x).2) F (nhds 0)) (i : Fin 2) :
    Filter.Tendsto (fun x ↦ scalarAt (scalarRun θs (z x)).1
      (scalarRun θs (z x)).2 i) F (nhds 0) := by
  induction θs generalizing z with
  | nil =>
      fin_cases i
      · simpa using hz0
      · simpa using hz1
  | cons θ θs ih =>
      have h0 := tendsto_scalarPairStep_zero θ.1 θ.2 z hz0 hz1 0
      have h1 := tendsto_scalarPairStep_zero θ.1 θ.2 z hz0 hz1 1
      simpa only [scalarRun_cons] using ih (fun x ↦ scalarPairStep θ (z x)) h0 h1

theorem scalarRun_gap_ne_zero (θs : List ScalarParameter) (z : ScalarPair)
    (hz : z.1 - z.2 ≠ 0) (hb : ∀ θ ∈ θs, θ.2 ≠ 0) :
    (scalarRun θs z).1 - (scalarRun θs z).2 ≠ 0 := by
  induction θs generalizing z with
  | nil => simpa using hz
  | cons θ θs ih =>
      apply ih (scalarPairStep θ z)
      · simpa [scalarPairStep] using scalarStep_gap_ne_zero θ.1 θ.2 z.1 z.2 hz
          (hb θ (by simp))
      · intro η hη
        exact hb η (by simp [hη])

theorem tendsto_scalarStep_gap_of_gap_zero {α : Type*} {F : Filter α}
    (a b : ℝ) (p q scale : α → ℝ)
    (hp : Filter.Tendsto p F (nhds 0)) (hq : Filter.Tendsto q F (nhds 0))
    (hgap : Filter.Tendsto (fun x ↦ (p x - q x) / scale x) F (nhds 0))
    (hscale : ∀ᶠ x in F, scale x ≠ 0) :
    Filter.Tendsto (fun x ↦
      (scalarStepZero a b (p x) (q x) - scalarStepOne a b (p x) (q x)) /
        scale x) F (nhds 0) := by
  let gap : α → ℝ := fun x ↦ p x - q x
  let z0 : α → ℝ := fun x ↦ gap x * (a + p x * b)
  let z1 : α → ℝ := fun x ↦ gap x * (a + q x * b)
  have hgap0 : Filter.Tendsto gap F (nhds 0) := by simpa [gap] using hp.sub hq
  have hz0 : Filter.Tendsto z0 F (nhds 0) := by
    have hi : Filter.Tendsto (fun x ↦ a + p x * b) F (nhds a) := by
      simpa using (tendsto_const_nhds.add (hp.mul_const b))
    simpa [z0] using hgap0.mul hi
  have hz1 : Filter.Tendsto z1 F (nhds 0) := by
    have hi : Filter.Tendsto (fun x ↦ a + q x * b) F (nhds a) := by
      simpa using (tendsto_const_nhds.add (hq.mul_const b))
    simpa [z1] using hgap0.mul hi
  have hs0 : Filter.Tendsto (fun x ↦ Real.sigmoid (z0 x)) F (nhds (1 / 2 : ℝ)) := by
    simpa [Function.comp_def, Real.sigmoid_zero] using
      (Real.hasDerivAt_sigmoid 0).continuousAt.tendsto.comp hz0
  have hs1 : Filter.Tendsto (fun x ↦ Real.sigmoid (z1 x)) F (nhds (1 / 2 : ℝ)) := by
    simpa [Function.comp_def, Real.sigmoid_zero] using
      (Real.hasDerivAt_sigmoid 0).continuousAt.tendsto.comp hz1
  have hlim := (hs0.sub hs1).mul hgap
  have heq : (fun x ↦
      (scalarStepZero a b (p x) (q x) - scalarStepOne a b (p x) (q x)) /
        scale x) =ᶠ[F]
      fun x ↦ (Real.sigmoid (z0 x) - Real.sigmoid (z1 x)) *
        ((p x - q x) / scale x) := by
    filter_upwards [hscale] with x hx
    dsimp [scalarStepZero, scalarStepOne, z0, z1, gap]
    field_simp [hx]
    ring
  apply Filter.Tendsto.congr' heq.symm
  simpa using hlim

/-- An arbitrary equally long suffix preserves a common comparison which
dominates both within-pair gaps. -/
theorem tendsto_scalarRun_preserves_common_comparison {α : Type*} {F : Filter α}
    (θs θs' : List ScalarParameter) (hlen : θs.length = θs'.length)
    (z z' : α → ScalarPair) (scale : α → ℝ) (w : ℝ)
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
      (scalarAt (scalarRun θs (z x)).1 (scalarRun θs (z x)).2 i -
       scalarAt (scalarRun θs' (z' x)).1 (scalarRun θs' (z' x)).2 i) / scale x)
      F (nhds w) := by
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
          let y : α → ScalarPair := fun x ↦ scalarPairStep θ (z x)
          let y' : α → ScalarPair := fun x ↦ scalarPairStep θ' (z' x)
          have hy0 : Filter.Tendsto (fun x ↦ (y x).1) F (nhds 0) := by
            simpa [y] using tendsto_scalarPairStep_zero θ.1 θ.2 z hz0 hz1 0
          have hy1 : Filter.Tendsto (fun x ↦ (y x).2) F (nhds 0) := by
            simpa [y] using tendsto_scalarPairStep_zero θ.1 θ.2 z hz0 hz1 1
          have hy0' : Filter.Tendsto (fun x ↦ (y' x).1) F (nhds 0) := by
            simpa [y'] using tendsto_scalarPairStep_zero θ'.1 θ'.2 z' hz0' hz1' 0
          have hy1' : Filter.Tendsto (fun x ↦ (y' x).2) F (nhds 0) := by
            simpa [y'] using tendsto_scalarPairStep_zero θ'.1 θ'.2 z' hz0' hz1' 1
          have hcross0' : Filter.Tendsto
              (fun x ↦ ((y x).1 - (y' x).1) / scale x) F (nhds w) := by
            simpa [y, y', scalarPairStep] using tendsto_scalarStep_preserves_common_comparison
              θ.1 θ.2 θ'.1 θ'.2 (fun x ↦ (z x).1) (fun x ↦ (z x).2)
              (fun x ↦ (z' x).1) (fun x ↦ (z' x).2) scale w
              hz0 hz1 hz0' hz1' hcross0 hcross1 hgap hgap' hscale 0
          have hcross1' : Filter.Tendsto
              (fun x ↦ ((y x).2 - (y' x).2) / scale x) F (nhds w) := by
            simpa [y, y', scalarPairStep] using tendsto_scalarStep_preserves_common_comparison
              θ.1 θ.2 θ'.1 θ'.2 (fun x ↦ (z x).1) (fun x ↦ (z x).2)
              (fun x ↦ (z' x).1) (fun x ↦ (z' x).2) scale w
              hz0 hz1 hz0' hz1' hcross0 hcross1 hgap hgap' hscale 1
          have hgapY : Filter.Tendsto
              (fun x ↦ ((y x).1 - (y x).2) / scale x) F (nhds 0) := by
            simpa [y, scalarPairStep] using tendsto_scalarStep_gap_of_gap_zero θ.1 θ.2
              (fun x ↦ (z x).1) (fun x ↦ (z x).2) scale hz0 hz1 hgap hscale
          have hgapY' : Filter.Tendsto
              (fun x ↦ ((y' x).1 - (y' x).2) / scale x) F (nhds 0) := by
            simpa [y', scalarPairStep] using tendsto_scalarStep_gap_of_gap_zero θ'.1 θ'.2
              (fun x ↦ (z' x).1) (fun x ↦ (z' x).2) scale hz0' hz1' hgap' hscale
          simpa only [scalarRun_cons, y, y'] using
            ih θs' hlen' y y' hy0 hy1 hy0' hy1' hcross0' hcross1'
              hgapY hgapY'

/-- The score immediately after a common prefix is observable through arbitrary
equally long suffixes. -/
theorem tendsto_scalarRun_next_comparison {α : Type*} {F : Filter α}
    (a b a' b' : ℝ) (θs θs' : List ScalarParameter)
    (hlen : θs.length = θs'.length) (p q scale : α → ℝ)
    (hp : Filter.Tendsto p F (nhds 0)) (hq : Filter.Tendsto q F (nhds 0))
    (hs : Filter.Tendsto scale F (nhds 0))
    (hgap : Filter.Tendsto (fun x ↦ (p x - q x) / scale x) F (nhds 1))
    (hscale : ∀ᶠ x in F, scale x ≠ 0) (i : Fin 2) :
    let y := fun x ↦ scalarPairStep (a, b) (p x, q x)
    let y' := fun x ↦ scalarPairStep (a', b') (p x, q x)
    Filter.Tendsto (fun x ↦
      (scalarAt (scalarRun θs (y x)).1 (scalarRun θs (y x)).2 i -
       scalarAt (scalarRun θs' (y' x)).1 (scalarRun θs' (y' x)).2 i) /
        (scale x) ^ 2) F (nhds ((a - a') / 4)) := by
  dsimp only
  let y : α → ScalarPair := fun x ↦ scalarPairStep (a, b) (p x, q x)
  let y' : α → ScalarPair := fun x ↦ scalarPairStep (a', b') (p x, q x)
  have hy0 := tendsto_scalarPairStep_zero a b (fun x ↦ (p x, q x)) hp hq 0
  have hy1 := tendsto_scalarPairStep_zero a b (fun x ↦ (p x, q x)) hp hq 1
  have hy0' := tendsto_scalarPairStep_zero a' b' (fun x ↦ (p x, q x)) hp hq 0
  have hy1' := tendsto_scalarPairStep_zero a' b' (fun x ↦ (p x, q x)) hp hq 1
  have hc0 : Filter.Tendsto (fun x ↦ ((y x).1 - (y' x).1) / (scale x)^2) F
      (nhds ((a-a')/4)) := by
    simpa [y, y', scalarPairStep] using tendsto_scalarStep_comparison a b a' b'
      p q scale 1 hp hq hs hgap hscale 0
  have hc1 : Filter.Tendsto (fun x ↦ ((y x).2 - (y' x).2) / (scale x)^2) F
      (nhds ((a-a')/4)) := by
    simpa [y, y', scalarPairStep] using tendsto_scalarStep_comparison a b a' b'
      p q scale 1 hp hq hs hgap hscale 1
  have hg3 : Filter.Tendsto (fun x ↦ ((y x).1 - (y x).2) / (scale x)^3) F
      (nhds (b/4)) := by
    simpa [y, scalarPairStep] using
      tendsto_scalar_gap_cubic a b p q scale 1 hp hq hs hgap hscale
  have hg3' : Filter.Tendsto (fun x ↦ ((y' x).1 - (y' x).2) / (scale x)^3) F
      (nhds (b'/4)) := by
    simpa [y', scalarPairStep] using
      tendsto_scalar_gap_cubic a' b' p q scale 1 hp hq hs hgap hscale
  have hg2 : Filter.Tendsto (fun x ↦ ((y x).1 - (y x).2) / (scale x)^2) F
      (nhds 0) := by
    have h := hs.mul hg3
    apply Filter.Tendsto.congr' _ (by simpa using h)
    filter_upwards [hscale] with x hx
    field_simp [hx]
  have hg2' : Filter.Tendsto (fun x ↦ ((y' x).1 - (y' x).2) / (scale x)^2) F
      (nhds 0) := by
    have h := hs.mul hg3'
    apply Filter.Tendsto.congr' _ (by simpa using h)
    filter_upwards [hscale] with x hx
    field_simp [hx]
  have hs2 : ∀ᶠ x in F, (scale x)^2 ≠ 0 := by
    filter_upwards [hscale] with x hx
    exact pow_ne_zero 2 hx
  exact tendsto_scalarRun_preserves_common_comparison θs θs' hlen y y'
    (fun x ↦ (scale x)^2) ((a-a')/4) hy0 hy1 hy0' hy1' hc0 hc1 hg2 hg2' hs2 i

end NormalizedDeepAttention
