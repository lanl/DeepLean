module

public import DeepLean.Attention.GeneralNormalization

/-!
# A source-valid normalization with a deep scaling fiber

The source assumptions do not impose continuity or monotonicity.  This module
constructs an explicit positive injective normalization whose values scale by
a common factor under multiplication of every nonzero score by four.  A first
generic scalar layer is arranged never to emit a mixture of zero and nonzero
tokens; consequently a second score matrix and four times that matrix define
the same second layer on the complete image of the first.
-/

@[expose] public section

namespace NormalizedDeepAttention

private noncomputable def logFour : ℝ := Real.log 4

private noncomputable def quarticCoordinate (x : ℝ) : ℝ :=
  Real.log |x| / logFour

private noncomputable def quarticPhase (x : ℝ) : ℝ :=
  Int.fract (quarticCoordinate x)

private noncomputable def quarticShell (x : ℝ) : ℤ :=
  ⌊quarticCoordinate x⌋

/-- Dimensionless logarithmic code.  Positive and negative inputs occupy
disjoint fractional bands, while multiplication by four subtracts one. -/
private noncomputable def exoticCode (x : ℝ) : ℝ :=
  if 0 < x then
    -(quarticShell x : ℝ) + 3 / 4 + quarticPhase x / 8
  else if x < 0 then
    -(quarticShell x : ℝ) - 3 / 4 + quarticPhase x / 8
  else 0

/-- The pathological but source-admissible normalization used below. -/
@[no_expose] noncomputable def exoticNormalization (x : ℝ) : ℝ :=
  Real.exp (exoticCode x * logFour)

private theorem logFour_pos : 0 < logFour := by
  exact Real.log_pos (by norm_num)

private theorem logFour_ne_zero : logFour ≠ 0 := ne_of_gt logFour_pos

@[simp] theorem exoticNormalization_zero : exoticNormalization 0 = 1 := by
  simp [exoticNormalization, exoticCode]

theorem exoticNormalization_pos (x : ℝ) : 0 < exoticNormalization x := by
  exact Real.exp_pos _

private theorem quarticPhase_nonneg (x : ℝ) : 0 ≤ quarticPhase x :=
  Int.fract_nonneg _

private theorem quarticPhase_lt_one (x : ℝ) : quarticPhase x < 1 :=
  Int.fract_lt_one _

private theorem quarticCoordinate_eq_phase_add_shell (x : ℝ) :
    quarticCoordinate x = quarticPhase x + (quarticShell x : ℝ) := by
  exact (Int.fract_add_floor (quarticCoordinate x)).symm

private theorem quarticCoordinate_four_mul {x : ℝ} (hx : x ≠ 0) :
    quarticCoordinate (4 * x) = quarticCoordinate x + 1 := by
  have habs : |4 * x| = 4 * |x| := by rw [abs_mul]; norm_num
  have habs0 : |x| ≠ 0 := abs_ne_zero.mpr hx
  unfold quarticCoordinate logFour
  rw [habs, Real.log_mul (by norm_num) habs0]
  field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 4) (by norm_num)]
  ring

private theorem quarticPhase_four_mul {x : ℝ} (hx : x ≠ 0) :
    quarticPhase (4 * x) = quarticPhase x := by
  unfold quarticPhase
  rw [quarticCoordinate_four_mul hx]
  exact Int.fract_add_one _

private theorem quarticShell_four_mul {x : ℝ} (hx : x ≠ 0) :
    quarticShell (4 * x) = quarticShell x + 1 := by
  unfold quarticShell
  rw [quarticCoordinate_four_mul hx]
  exact Int.floor_add_one _

private theorem exoticCode_four_mul {x : ℝ} (hx : x ≠ 0) :
    exoticCode (4 * x) = exoticCode x - 1 := by
  have hfour : (0 : ℝ) < 4 := by norm_num
  by_cases hxpos : 0 < x
  · have h4xpos : 0 < 4 * x := mul_pos hfour hxpos
    simp only [exoticCode, if_pos hxpos, if_pos h4xpos]
    rw [quarticShell_four_mul hx, quarticPhase_four_mul hx]
    push_cast
    ring
  · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx
    have h4xneg : 4 * x < 0 := mul_neg_of_pos_of_neg hfour hxneg
    simp only [exoticCode, if_neg (not_lt_of_ge (le_of_lt hxneg)), if_pos hxneg,
      if_neg (not_lt_of_ge (le_of_lt h4xneg)), if_pos h4xneg]
    rw [quarticShell_four_mul hx, quarticPhase_four_mul hx]
    push_cast
    ring

/-- All nonzero score weights acquire the same factor `1/4` when their scores
are multiplied by four. -/
theorem exoticNormalization_four_mul {x : ℝ} (hx : x ≠ 0) :
    exoticNormalization (4 * x) = exoticNormalization x / 4 := by
  rw [exoticNormalization, exoticNormalization, exoticCode_four_mul hx]
  have hlog : Real.exp logFour = 4 := by
    exact Real.exp_log (by norm_num)
  rw [sub_mul, Real.exp_sub, one_mul, hlog]

private theorem floor_positiveBand (x : ℝ) :
    ⌊(3 / 4 + quarticPhase x / 8 : ℝ)⌋ = 0 := by
  rw [Int.floor_eq_iff]
  constructor <;> push_cast
  · linarith [quarticPhase_nonneg x]
  · linarith [quarticPhase_lt_one x]

private theorem floor_negativeBand (x : ℝ) :
    ⌊(-3 / 4 + quarticPhase x / 8 : ℝ)⌋ = -1 := by
  rw [Int.floor_eq_iff]
  constructor <;> push_cast
  · linarith [quarticPhase_nonneg x]
  · linarith [quarticPhase_lt_one x]

private theorem floor_exoticCode_of_pos {x : ℝ} (hx : 0 < x) :
    ⌊exoticCode x⌋ = -quarticShell x := by
  rw [exoticCode, if_pos hx]
  conv_lhs =>
    rw [show -(quarticShell x : ℝ) + 3 / 4 + quarticPhase x / 8 =
      (-(quarticShell x) : ℤ) + (3 / 4 + quarticPhase x / 8 : ℝ) by push_cast; ring]
  rw [Int.floor_intCast_add, floor_positiveBand]
  omega

private theorem floor_exoticCode_of_neg {x : ℝ} (hx : x < 0) :
    ⌊exoticCode x⌋ = -quarticShell x - 1 := by
  rw [exoticCode, if_neg (not_lt_of_ge (le_of_lt hx)), if_pos hx]
  conv_lhs =>
    rw [show -(quarticShell x : ℝ) - 3 / 4 + quarticPhase x / 8 =
      (-(quarticShell x) : ℤ) + (-3 / 4 + quarticPhase x / 8 : ℝ) by
        push_cast; ring]
  rw [Int.floor_intCast_add, floor_negativeBand]
  omega

private theorem exoticCode_ne_zero_of_pos {x : ℝ} (hx : 0 < x) :
    exoticCode x ≠ 0 := by
  intro h
  have hf := congrArg Int.floor h
  rw [floor_exoticCode_of_pos hx, Int.floor_zero] at hf
  have hshell : quarticShell x = 0 := by omega
  rw [exoticCode, if_pos hx, hshell] at h
  push_cast at h
  linarith [quarticPhase_nonneg x]

private theorem exoticCode_ne_zero_of_neg {x : ℝ} (hx : x < 0) :
    exoticCode x ≠ 0 := by
  intro h
  have hf := congrArg Int.floor h
  rw [floor_exoticCode_of_neg hx, Int.floor_zero] at hf
  have hshell : quarticShell x = -1 := by omega
  rw [exoticCode, if_neg (not_lt_of_ge (le_of_lt hx)), if_pos hx, hshell] at h
  push_cast at h
  norm_num at h
  linarith [quarticPhase_nonneg x]

private theorem exoticCode_injective : Function.Injective exoticCode := by
  intro x y hxy
  by_cases hxpos : 0 < x
  · by_cases hypos : 0 < y
    · have hf := congrArg Int.floor hxy
      rw [floor_exoticCode_of_pos hxpos, floor_exoticCode_of_pos hypos] at hf
      have hshell : quarticShell x = quarticShell y := by omega
      rw [exoticCode, if_pos hxpos, exoticCode, if_pos hypos, hshell] at hxy
      have hphase : quarticPhase x = quarticPhase y := by linarith
      have hcoord : quarticCoordinate x = quarticCoordinate y := by
        rw [quarticCoordinate_eq_phase_add_shell,
          quarticCoordinate_eq_phase_add_shell, hshell, hphase]
      unfold quarticCoordinate at hcoord
      have hlogabs : Real.log |x| = Real.log |y| := by
        exact (div_left_inj' logFour_ne_zero).mp hcoord
      have habs : |x| = |y| := Real.log_injOn_pos (abs_pos.mpr (ne_of_gt hxpos))
        (abs_pos.mpr (ne_of_gt hypos)) hlogabs
      simpa [abs_of_pos hxpos, abs_of_pos hypos] using habs
    · by_cases hyneg : y < 0
      · have hf := congrArg Int.floor hxy
        rw [floor_exoticCode_of_pos hxpos, floor_exoticCode_of_neg hyneg] at hf
        have hshell : quarticShell y = quarticShell x - 1 := by omega
        rw [exoticCode, if_pos hxpos, exoticCode,
          if_neg (not_lt_of_ge (le_of_lt hyneg)), if_pos hyneg, hshell] at hxy
        push_cast at hxy
        linarith [quarticPhase_nonneg x, quarticPhase_lt_one x,
          quarticPhase_nonneg y, quarticPhase_lt_one y]
      · have hy : y = 0 := le_antisymm (le_of_not_gt hypos) (le_of_not_gt hyneg)
        subst y
        exact (exoticCode_ne_zero_of_pos hxpos (by simpa [exoticCode] using hxy)).elim
  · by_cases hxneg : x < 0
    · by_cases hypos : 0 < y
      · have hf := congrArg Int.floor hxy
        rw [floor_exoticCode_of_neg hxneg, floor_exoticCode_of_pos hypos] at hf
        have hshell : quarticShell x = quarticShell y - 1 := by omega
        rw [exoticCode, if_neg (not_lt_of_ge (le_of_lt hxneg)), if_pos hxneg,
          exoticCode, if_pos hypos, hshell] at hxy
        push_cast at hxy
        linarith [quarticPhase_nonneg x, quarticPhase_lt_one x,
          quarticPhase_nonneg y, quarticPhase_lt_one y]
      · by_cases hyneg : y < 0
        · have hf := congrArg Int.floor hxy
          rw [floor_exoticCode_of_neg hxneg, floor_exoticCode_of_neg hyneg] at hf
          have hshell : quarticShell x = quarticShell y := by omega
          rw [exoticCode, if_neg (not_lt_of_ge (le_of_lt hxneg)), if_pos hxneg,
            exoticCode, if_neg (not_lt_of_ge (le_of_lt hyneg)), if_pos hyneg,
            hshell] at hxy
          have hphase : quarticPhase x = quarticPhase y := by linarith
          have hcoord : quarticCoordinate x = quarticCoordinate y := by
            rw [quarticCoordinate_eq_phase_add_shell,
              quarticCoordinate_eq_phase_add_shell, hshell, hphase]
          unfold quarticCoordinate at hcoord
          have hlogabs : Real.log |x| = Real.log |y| := by
            exact (div_left_inj' logFour_ne_zero).mp hcoord
          have habs : |x| = |y| := Real.log_injOn_pos (abs_pos.mpr (ne_of_lt hxneg))
            (abs_pos.mpr (ne_of_lt hyneg)) hlogabs
          have : -x = -y := by simpa [abs_of_neg hxneg, abs_of_neg hyneg] using habs
          linarith
        · have hy : y = 0 := le_antisymm (le_of_not_gt hypos) (le_of_not_gt hyneg)
          subst y
          exact (exoticCode_ne_zero_of_neg hxneg (by simpa [exoticCode] using hxy)).elim
    · have hx : x = 0 := le_antisymm (le_of_not_gt hxpos) (le_of_not_gt hxneg)
      subst x
      by_cases hypos : 0 < y
      · exact (exoticCode_ne_zero_of_pos hypos (by simpa [exoticCode] using hxy.symm)).elim
      · by_cases hyneg : y < 0
        · exact (exoticCode_ne_zero_of_neg hyneg (by simpa [exoticCode] using hxy.symm)).elim
        · exact le_antisymm (le_of_not_gt hypos) (le_of_not_gt hyneg) |>.symm

theorem exoticNormalization_injective : Function.Injective exoticNormalization := by
  intro x y hxy
  apply exoticCode_injective
  apply mul_right_cancel₀ logFour_ne_zero
  exact Real.exp_injective hxy

/-- The source-valid counterexample can additionally be chosen Borel
measurable.  No such regularity is needed by the source statement. -/
theorem exoticNormalization_measurable : Measurable exoticNormalization := by
  have hcoordinate : Measurable quarticCoordinate := by
    exact (Real.measurable_log.comp measurable_abs).div_const logFour
  have hphase : Measurable quarticPhase := measurable_fract.comp hcoordinate
  have hshell : Measurable quarticShell := Int.measurable_floor.comp hcoordinate
  have hshellCast : Measurable (fun x : ℝ ↦ (quarticShell x : ℝ)) :=
    (measurable_of_countable fun z : ℤ ↦ (z : ℝ)).comp hshell
  have hpositive : Measurable (fun x : ℝ ↦
      -(quarticShell x : ℝ) + 3 / 4 + quarticPhase x / 8) :=
    (hshellCast.neg.add_const (3 / 4)).add (hphase.div_const 8)
  have hnegative : Measurable (fun x : ℝ ↦
      -(quarticShell x : ℝ) - 3 / 4 + quarticPhase x / 8) :=
    (hshellCast.neg.sub_const (3 / 4)).add (hphase.div_const 8)
  have hcode : Measurable exoticCode := by
    unfold exoticCode
    exact Measurable.ite measurableSet_Ioi hpositive
      (Measurable.ite measurableSet_Iio hnegative measurable_const)
  exact Real.measurable_exp.comp (hcode.mul_const logFour)

/-- The counterexample normalizer is discontinuous at zero.  This boundary
property is not used in the fiber construction. -/
theorem exoticNormalization_not_continuousAt_zero :
    ¬ ContinuousAt exoticNormalization 0 := by
  intro hcontinuous
  have hbase : Filter.Tendsto exoticNormalization
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 1) := by
    simpa [exoticNormalization_zero] using
      hcontinuous.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) ({0}ᶜ) ≤ nhds 0 from nhdsWithin_le_nhds)
  have hinput : Filter.Tendsto (fun x : ℝ ↦ 4 * x)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 0) := by
    have hmul : ContinuousAt (fun x : ℝ ↦ 4 * x) 0 := by fun_prop
    simpa using hmul.tendsto.mono_left
      (show nhdsWithin (0 : ℝ) ({0}ᶜ) ≤ nhds 0 from nhdsWithin_le_nhds)
  have hleft : Filter.Tendsto
      (exoticNormalization ∘ fun x : ℝ ↦ 4 * x)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds 1) := by
    simpa only [exoticNormalization_zero] using
      hcontinuous.tendsto.comp hinput
  have heq : (exoticNormalization ∘ fun x : ℝ ↦ 4 * x) =ᶠ[
      nhdsWithin (0 : ℝ) ({0}ᶜ)] (fun x : ℝ ↦ exoticNormalization x / 4) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact exoticNormalization_four_mul hx
  have hright : Filter.Tendsto
      (fun x : ℝ ↦ exoticNormalization x / 4)
      (nhdsWithin (0 : ℝ) ({0}ᶜ)) (nhds (1 / 4 : ℝ)) := by
    simpa using hbase.div_const 4
  have hone : (1 : ℝ) = 1 / 4 :=
    tendsto_nhds_unique hleft (hright.congr' heq.symm)
  norm_num at hone

private theorem quarticCoordinate_neg (x : ℝ) :
    quarticCoordinate (-x) = quarticCoordinate x := by
  simp [quarticCoordinate]

private theorem quarticPhase_neg (x : ℝ) : quarticPhase (-x) = quarticPhase x := by
  simp [quarticPhase, quarticCoordinate_neg]

private theorem quarticShell_neg (x : ℝ) : quarticShell (-x) = quarticShell x := by
  simp [quarticShell, quarticCoordinate_neg]

private theorem pos_mul_exoticNormalization_eq {z : ℝ} (hz : 0 < z) :
    z * exoticNormalization z =
      Real.exp ((3 / 4 + 9 * quarticPhase z / 8) * logFour) := by
  have hlog : Real.log z = quarticCoordinate z * logFour := by
    unfold quarticCoordinate
    rw [abs_of_pos hz]
    field_simp [logFour_ne_zero]
  have hzexp : z = Real.exp (quarticCoordinate z * logFour) := by
    rw [← hlog, Real.exp_log hz]
  calc
    z * exoticNormalization z =
        Real.exp (quarticCoordinate z * logFour) * exoticNormalization z := by
          exact congrArg (fun q => q * exoticNormalization z) hzexp
    _ = Real.exp (quarticCoordinate z * logFour) *
        Real.exp ((-(quarticShell z : ℝ) + 3 / 4 + quarticPhase z / 8) * logFour) := by
          rw [exoticNormalization, exoticCode, if_pos hz]
    _ = Real.exp ((3 / 4 + 9 * quarticPhase z / 8) * logFour) := by
          rw [← Real.exp_add, quarticCoordinate_eq_phase_add_shell]
          congr 1
          ring

private theorem pos_mul_exoticNormalization_neg_eq {z : ℝ} (hz : 0 < z) :
    z * exoticNormalization (-z) =
      Real.exp ((-3 / 4 + 9 * quarticPhase z / 8) * logFour) := by
  have hlog : Real.log z = quarticCoordinate z * logFour := by
    unfold quarticCoordinate
    rw [abs_of_pos hz]
    field_simp [logFour_ne_zero]
  have hzexp : z = Real.exp (quarticCoordinate z * logFour) := by
    rw [← hlog, Real.exp_log hz]
  have hnz : -z < 0 := neg_neg_iff_pos.mpr hz
  have hnpos : ¬ 0 < -z := not_lt_of_ge (neg_nonpos.mpr hz.le)
  calc
    z * exoticNormalization (-z) =
        Real.exp (quarticCoordinate z * logFour) * exoticNormalization (-z) := by
          exact congrArg (fun q => q * exoticNormalization (-z)) hzexp
    _ = Real.exp (quarticCoordinate z * logFour) *
        Real.exp ((-(quarticShell (-z) : ℝ) - 3 / 4 + quarticPhase (-z) / 8) *
          logFour) := by
          rw [exoticNormalization, exoticCode,
            if_neg hnpos, if_pos hnz]
    _ = Real.exp ((-3 / 4 + 9 * quarticPhase z / 8) * logFour) := by
          rw [← Real.exp_add, quarticCoordinate_eq_phase_add_shell,
            quarticPhase_neg, quarticShell_neg]
          congr 1
          ring

/-- Positive-score mass always strictly dominates negative-score mass,
uniformly over unrelated positive magnitudes.  This is the property that
prevents the first scalar layer from producing an isolated zero token. -/
theorem exotic_positive_mass_gt_negative_mass {z w : ℝ}
    (hz : 0 < z) (hw : 0 < w) :
    z * exoticNormalization z > w * exoticNormalization (-w) := by
  rw [pos_mul_exoticNormalization_eq hz,
    pos_mul_exoticNormalization_neg_eq hw]
  apply Real.exp_lt_exp.mpr
  apply mul_lt_mul_of_pos_right _ logFour_pos
  linarith [quarticPhase_nonneg z, quarticPhase_lt_one w]

private theorem exotic_self_cross_numerator_ne_zero (a b : ℝ)
    (hab : a ≠ 0 ∨ b ≠ 0) :
    exoticNormalization (a * a) * a + exoticNormalization (a * b) * b ≠ 0 := by
  by_cases ha0 : a = 0
  · have hb : b ≠ 0 := hab.resolve_left (not_ne_iff.mpr ha0)
    subst a
    simpa using mul_ne_zero (ne_of_gt (exoticNormalization_pos 0)) hb
  · by_cases hb0 : b = 0
    · subst b
      simp only [mul_zero, exoticNormalization_zero, add_zero]
      exact mul_ne_zero (ne_of_gt (exoticNormalization_pos _)) ha0
    · by_cases haPos : 0 < a
      · by_cases hbPos : 0 < b
        · have h₁ : 0 < exoticNormalization (a * a) * a :=
            mul_pos (exoticNormalization_pos _) haPos
          have h₂ : 0 < exoticNormalization (a * b) * b :=
            mul_pos (exoticNormalization_pos _) hbPos
          exact ne_of_gt (add_pos h₁ h₂)
        · have hbNeg : b < 0 := lt_of_le_of_ne (le_of_not_gt hbPos) hb0
          have hmass := exotic_positive_mass_gt_negative_mass
            (mul_pos haPos haPos) (mul_pos haPos (neg_pos.mpr hbNeg))
          have harg : a * b = -(a * (-b)) := by ring
          have hnum : 0 < exoticNormalization (a * a) * a +
              exoticNormalization (a * b) * b := by
            rw [harg]
            nlinarith [haPos]
          exact ne_of_gt hnum
      · have haNeg : a < 0 := lt_of_le_of_ne (le_of_not_gt haPos) ha0
        by_cases hbNeg : b < 0
        · have h₁ : exoticNormalization (a * a) * a < 0 :=
            mul_neg_of_pos_of_neg (exoticNormalization_pos _) haNeg
          have h₂ : exoticNormalization (a * b) * b < 0 :=
            mul_neg_of_pos_of_neg (exoticNormalization_pos _) hbNeg
          exact ne_of_lt (add_neg h₁ h₂)
        · have hbPos : 0 < b := lt_of_le_of_ne (le_of_not_gt hbNeg) (Ne.symm hb0)
          have hmass := exotic_positive_mass_gt_negative_mass
            (mul_pos (neg_pos.mpr haNeg) (neg_pos.mpr haNeg))
            (mul_pos (neg_pos.mpr haNeg) hbPos)
          have hsq : (-a) * (-a) = a * a := by ring
          have harg : -((-a) * b) = a * b := by ring
          have hnum : exoticNormalization (a * a) * a +
              exoticNormalization (a * b) * b < 0 := by
            rw [← hsq, ← harg]
            nlinarith [neg_pos.mpr haNeg]
          exact ne_of_lt hnum

private theorem exotic_scaled_self_cross_numerator_ne_zero (c a b : ℝ)
    (hc : c ≠ 0) (hab : a ≠ 0 ∨ b ≠ 0) :
    exoticNormalization (c * a * a) * a +
      exoticNormalization (c * a * b) * b ≠ 0 := by
  by_cases hcpos : 0 < c
  · let q := Real.sqrt c
    have hqpos : 0 < q := Real.sqrt_pos.2 hcpos
    have hq2 : q * q = c := by
      simpa [q, pow_two] using Real.sq_sqrt hcpos.le
    have habq : q * a ≠ 0 ∨ q * b ≠ 0 := by
      rcases hab with ha | hb
      · exact Or.inl (mul_ne_zero (ne_of_gt hqpos) ha)
      · exact Or.inr (mul_ne_zero (ne_of_gt hqpos) hb)
    have hbase := exotic_self_cross_numerator_ne_zero (q * a) (q * b) habq
    have haa : (q * a) * (q * a) = c * a * a := by rw [← hq2]; ring
    have hab' : (q * a) * (q * b) = c * a * b := by rw [← hq2]; ring
    rw [haa, hab'] at hbase
    intro hzero
    apply hbase
    calc
      exoticNormalization (c * a * a) * (q * a) +
          exoticNormalization (c * a * b) * (q * b) =
        q * (exoticNormalization (c * a * a) * a +
          exoticNormalization (c * a * b) * b) := by ring
      _ = 0 := by rw [hzero, mul_zero]
  · have hcneg : c < 0 := lt_of_le_of_ne (le_of_not_gt hcpos) hc
    by_cases ha0 : a = 0
    · have hb : b ≠ 0 := hab.resolve_left (not_ne_iff.mpr ha0)
      subst a
      simpa using mul_ne_zero (ne_of_gt (exoticNormalization_pos 0)) hb
    · by_cases hb0 : b = 0
      · subst b
        simp only [mul_zero, exoticNormalization_zero, add_zero]
        exact mul_ne_zero (ne_of_gt (exoticNormalization_pos _)) ha0
      · by_cases haPos : 0 < a
        · by_cases hbPos : 0 < b
          · exact ne_of_gt (add_pos
              (mul_pos (exoticNormalization_pos _) haPos)
              (mul_pos (exoticNormalization_pos _) hbPos))
          · have hbNeg : b < 0 := lt_of_le_of_ne (le_of_not_gt hbPos) hb0
            have hcross : 0 < c * a * b :=
              mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hcneg haPos) hbNeg
            have hself : 0 < -(c * a * a) := by nlinarith [mul_pos haPos haPos]
            have hmass := exotic_positive_mass_gt_negative_mass hcross hself
            have harg : -( -(c * a * a)) = c * a * a := by ring
            rw [harg] at hmass
            have hnum : exoticNormalization (c * a * a) * a +
                exoticNormalization (c * a * b) * b < 0 := by
              nlinarith [neg_pos.mpr hcneg, haPos]
            exact ne_of_lt hnum
        · have haNeg : a < 0 := lt_of_le_of_ne (le_of_not_gt haPos) ha0
          by_cases hbNeg : b < 0
          · exact ne_of_lt (add_neg
              (mul_neg_of_pos_of_neg (exoticNormalization_pos _) haNeg)
              (mul_neg_of_pos_of_neg (exoticNormalization_pos _) hbNeg))
          · have hbPos : 0 < b := lt_of_le_of_ne (le_of_not_gt hbNeg) (Ne.symm hb0)
            have hcross : 0 < c * a * b := mul_pos (mul_pos_of_neg_of_neg hcneg haNeg) hbPos
            have hself : 0 < -(c * a * a) := by
              nlinarith [mul_pos_of_neg_of_neg haNeg haNeg]
            have hmass := exotic_positive_mass_gt_negative_mass hcross hself
            have harg : -( -(c * a * a)) = c * a * a := by ring
            rw [harg] at hmass
            have hnum : 0 < exoticNormalization (c * a * a) * a +
                exoticNormalization (c * a * b) * b := by
              nlinarith [neg_pos.mpr hcneg, neg_pos.mpr haNeg]
            exact ne_of_gt hnum

/-- A two-token scalar input with entries `a` and `b`. -/
def scalarPair (a b : ℝ) : Matrix (Fin 1) (Fin 2) ℝ :=
  firstAndRepeatedTokenMatrix (n := 1) (fun _ ↦ a) (fun _ ↦ b)

private theorem attentionScore_scalar {t : ℕ} (c : ℝ)
    (X : Matrix (Fin 1) (Fin t) ℝ) (i j : Fin t) :
    attentionScore (scalarScore c) X i j = X 0 i * (c * X 0 j) := by
  simp [attentionScore, scalarScore, Matrix.mulVec, dotProduct]

/-- First output coordinate of a scalar two-token exotic-normalized layer. -/
theorem layer_scalarPair_first (c a b : ℝ) :
    layer exoticNormalization (scalarScore c) (scalarPair a b) 0 0 =
      (exoticNormalization (c * a * a) * a +
        exoticNormalization (c * a * b) * b) /
      (exoticNormalization (c * a * a) + exoticNormalization (c * a * b)) := by
  rw [layer, scalarPair, normalizedAttention_firstAndRepeated_first]
  simp [scalarScore, Matrix.mulVec, dotProduct]
  ring_nf

/-- Second output coordinate of a scalar two-token exotic-normalized layer. -/
theorem layer_scalarPair_second (c a b : ℝ) :
    layer exoticNormalization (scalarScore c) (scalarPair a b) 0 (Fin.succ 0) =
      (exoticNormalization (c * b * a) * a +
        exoticNormalization (c * b * b) * b) /
      (exoticNormalization (c * b * a) + exoticNormalization (c * b * b)) := by
  rw [layer, scalarPair]
  have h := normalizedAttention_firstAndRepeated_repeated
    exoticNormalization (scalarScore c) (1 : ScoreMatrix 1)
    (fun _ : Fin 1 ↦ a) (fun _ : Fin 1 ↦ b) (0 : Fin 1) (0 : Fin 1)
  simp [scalarScore, Matrix.mulVec, dotProduct] at h ⊢
  ring_nf at h ⊢
  exact h

/-- Every output token of the first scalar layer is nonzero on every nonzero
two-token input when the score parameter is nonzero. -/
theorem exotic_first_layer_nonzero_of_pair_ne_zero (c a b : ℝ)
    (hc : c ≠ 0) (hab : a ≠ 0 ∨ b ≠ 0) (i : Fin 2) :
    layer exoticNormalization (scalarScore c) (scalarPair a b) 0 i ≠ 0 := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [layer_scalarPair_first]
    apply div_ne_zero
    · exact exotic_scaled_self_cross_numerator_ne_zero c a b hc hab
    · exact ne_of_gt (add_pos (exoticNormalization_pos _) (exoticNormalization_pos _))
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rw [layer_scalarPair_second]
    apply div_ne_zero
    · have h := exotic_scaled_self_cross_numerator_ne_zero c b a hc (Or.symm hab)
      simpa [mul_comm, mul_left_comm, mul_assoc, add_comm] using h
    · exact ne_of_gt (add_pos (exoticNormalization_pos _) (exoticNormalization_pos _))

/-- Multiplying every score by four leaves an exotic-normalized layer unchanged
provided no score in the input is zero. -/
theorem layer_exotic_four_smul_eq_of_scores_ne_zero {d t : ℕ}
    (M : ScoreMatrix d) (X : Matrix (Fin d) (Fin t) ℝ)
    (hscore : ∀ i j, attentionScore M X i j ≠ 0) :
    layer exoticNormalization ((4 : ℝ) • M) X = layer exoticNormalization M X := by
  ext r i
  simp only [layer, normalizedAttention]
  have hw (j : Fin t) :
      exoticNormalization (attentionScore ((4 : ℝ) • M) X i j) =
        exoticNormalization (attentionScore M X i j) / 4 := by
    rw [attentionScore_smul]
    exact exoticNormalization_four_mul (hscore i j)
  rw [show (∑ j : Fin t,
      exoticNormalization (attentionScore ((4 : ℝ) • M) X i j) *
        (1 : ScoreMatrix d).mulVec (X.col j) r) =
      (∑ j : Fin t, exoticNormalization (attentionScore M X i j) *
        (1 : ScoreMatrix d).mulVec (X.col j) r) / 4 by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    rw [hw]
    ring]
  rw [show (∑ k : Fin t,
      exoticNormalization (attentionScore ((4 : ℝ) • M) X i k)) =
      (∑ k : Fin t, exoticNormalization (attentionScore M X i k)) / 4 by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    exact hw k]
  have hden : (∑ k : Fin t, exoticNormalization (attentionScore M X i k)) ≠ 0 := by
    exact ne_of_gt (Finset.sum_pos (fun k _ ↦ exoticNormalization_pos _)
      ⟨i, Finset.mem_univ i⟩)
  field_simp [hden]

private theorem scalarPair_eq_zero_iff (a b : ℝ) :
    scalarPair a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have ha := congrFun (congrFun h 0) 0
    have hb := congrFun (congrFun h 0) 1
    change a = 0 at ha
    change b = 0 at hb
    exact ⟨ha, hb⟩
  · rintro ⟨rfl, rfl⟩
    ext i j
    fin_cases i
    fin_cases j <;> rfl

private theorem matrix_one_one_eq_scalarScore_one :
    (1 : ScoreMatrix 1) = scalarScore 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [scalarScore]

private theorem scalarScore_four_mul_eq_smul (c : ℝ) :
    scalarScore (4 * c) = (4 : ℝ) • scalarScore c := by
  ext i j
  simp [scalarScore]

private theorem scalar_input_eq_pair (X : Matrix (Fin 1) (Fin 2) ℝ) :
    X = scalarPair (X 0 0) (X 0 1) := by
  ext i j
  fin_cases i
  fin_cases j <;> rfl

private theorem exotic_second_layer_eq (m₁ m₂ a b : ℝ)
    (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) :
    layer exoticNormalization (scalarScore (4 * m₂))
        (layer exoticNormalization (scalarScore m₁) (scalarPair a b)) =
      layer exoticNormalization (scalarScore m₂)
        (layer exoticNormalization (scalarScore m₁) (scalarPair a b)) := by
  by_cases hab : a ≠ 0 ∨ b ≠ 0
  · let Y := layer exoticNormalization (scalarScore m₁) (scalarPair a b)
    have hy (i : Fin 2) : Y 0 i ≠ 0 :=
      exotic_first_layer_nonzero_of_pair_ne_zero m₁ a b hm₁ hab i
    have hs (i j : Fin 2) : attentionScore (scalarScore m₂) Y i j ≠ 0 := by
      rw [attentionScore_scalar]
      exact mul_ne_zero (hy i) (mul_ne_zero hm₂ (hy j))
    rw [scalarScore_four_mul_eq_smul]
    exact layer_exotic_four_smul_eq_of_scores_ne_zero (scalarScore m₂) Y hs
  · push Not at hab
    rcases hab with ⟨rfl, rfl⟩
    have hp : scalarPair 0 0 = constantTokenMatrix (t := 2) (fun _ : Fin 1 ↦ 0) := by
      ext i j
      fin_cases i
      fin_cases j <;> rfl
    rw [hp, layer_constantTokenMatrix exoticNormalization exoticNormalization_pos
      (scalarScore m₁) (fun _ : Fin 1 ↦ 0) (by norm_num)]
    rw [layer_constantTokenMatrix exoticNormalization exoticNormalization_pos
      (scalarScore (4 * m₂)) (fun _ : Fin 1 ↦ 0) (by norm_num)]
    rw [layer_constantTokenMatrix exoticNormalization exoticNormalization_pos
      (scalarScore m₂) (fun _ : Fin 1 ↦ 0) (by norm_num)]

theorem exoticFamilySource_coordinateRegular {m₁ m₂ l : ℝ}
    (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) (hl : l ≠ 0) :
    CoordinateRegular 0 0 (exoticFamilySource m₁ m₂ l) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [exoticFamilySource, scalarScore] using hm₁
  · intro j
    simpa [exoticFamilySource, scalarScore] using hm₂
  · simpa [exoticFamilySource, scalarScore] using hl

theorem exoticFamilySource_ne_partner {m₁ m₂ l : ℝ} (hm₂ : m₂ ≠ 0) :
    exoticFamilySource m₁ m₂ l ≠ exoticFamilyPartner m₁ m₂ l := by
  intro h
  have he := congrFun (congrFun (congrFun (congrArg (fun W ↦ W.2.1) h) 0) 0) 0
  simp only [exoticFamilySource, exoticFamilyPartner, scalarScore] at he
  apply hm₂
  linarith

theorem exoticFamilySource_realization_eq_partner {m₁ m₂ l : ℝ}
    (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) :
    realizeDeep (t := 2) exoticNormalization
        (fixedDepthToDeep (exoticFamilySource m₁ m₂ l)) =
      realizeDeep exoticNormalization
        (fixedDepthToDeep (exoticFamilyPartner m₁ m₂ l)) := by
  funext X
  rw [scalar_input_eq_pair X]
  have hone : List.ofFn (fun _ : Fin 1 ↦ scalarScore m₂) = [scalarScore m₂] := by
    rw [List.ofFn_succ]
    rfl
  have hfour : List.ofFn (fun _ : Fin 1 ↦ scalarScore (4 * m₂)) =
      [scalarScore (4 * m₂)] := by
    rw [List.ofFn_succ]
    rfl
  simp only [realizeDeep, fixedDepthToDeep, exoticFamilySource, exoticFamilyPartner,
    hone, hfour, applyLayers]
  apply congrArg (fun Y : Matrix (Fin 1) (Fin 2) ℝ ↦ (scalarScore l) * Y)
  exact (exotic_second_layer_eq m₁ m₂ (X 0 0) (X 0 1) hm₁ hm₂).symm

/-- Non-singleton complete fibers occur on the entire scalar
coordinate-regular locus, not at an isolated exceptional point. -/
theorem exotic_coordinateRegular_locus_has_nontrivial_fibers
    (m₁ m₂ l : ℝ) (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) (hl : l ≠ 0) :
    CoordinateRegular 0 0 (exoticFamilySource m₁ m₂ l) ∧
      exoticFamilySource m₁ m₂ l ≠ exoticFamilyPartner m₁ m₂ l ∧
      realizeDeep (t := 2) exoticNormalization
          (fixedDepthToDeep (exoticFamilySource m₁ m₂ l)) =
        realizeDeep exoticNormalization
          (fixedDepthToDeep (exoticFamilyPartner m₁ m₂ l)) := by
  exact ⟨exoticFamilySource_coordinateRegular hm₁ hm₂ hl,
    exoticFamilySource_ne_partner hm₂,
    exoticFamilySource_realization_eq_partner hm₁ hm₂⟩

private theorem scalarFixedDepth_eq_exoticFamilySource
    (W : FixedDepthWeights 1 1 1) :
    W = exoticFamilySource (W.1 0 0) (W.2.1 0 0 0) (W.2.2 0 0) := by
  apply Prod.ext
  · ext i j
    fin_cases i
    fin_cases j
    rfl
  · apply Prod.ext
    · funext k
      ext i j
      fin_cases k
      fin_cases i
      fin_cases j
      rfl
    · ext o i
      fin_cases o
      fin_cases i
      rfl

/-- Direct full-locus form of the generic counterexample: every source point
in the scalar coordinate-regular locus has a distinct same-depth virtual
partner with the same complete realized function. -/
theorem exotic_coordinateRegular_full_locus_has_nontrivial_fiber
    (W : FixedDepthWeights 1 1 1) (hW : CoordinateRegular 0 0 W) :
    ∃ W' : FixedDepthWeights 1 1 1,
      W ≠ W' ∧
      realizeDeep (t := 2) exoticNormalization (fixedDepthToDeep W) =
        realizeDeep exoticNormalization (fixedDepthToDeep W') := by
  let m₁ := W.1 0 0
  let m₂ := W.2.1 0 0 0
  let l := W.2.2 0 0
  have hm₁ : m₁ ≠ 0 := hW.1
  have hm₂ : m₂ ≠ 0 := hW.2.1 0
  have hrepr : W = exoticFamilySource m₁ m₂ l :=
    scalarFixedDepth_eq_exoticFamilySource W
  refine ⟨exoticFamilyPartner m₁ m₂ l, ?_, ?_⟩
  · rw [hrepr]
    exact exoticFamilySource_ne_partner hm₂
  · rw [hrepr]
    exact exoticFamilySource_realization_eq_partner hm₁ hm₂

/-- Generic fixed-depth source point for the counterexample. -/
def exoticSource : FixedDepthWeights 1 1 1 :=
  exoticFamilySource 1 1 1

/-- Distinct partner obtained by multiplying only the second score matrix by four. -/
def exoticPartner : FixedDepthWeights 1 1 1 :=
  exoticFamilyPartner 1 1 1

theorem exoticSource_coordinateRegular : CoordinateRegular 0 0 exoticSource := by
  exact exoticFamilySource_coordinateRegular (by norm_num) (by norm_num) (by norm_num)

theorem exoticSource_ne_partner : exoticSource ≠ exoticPartner := by
  exact exoticFamilySource_ne_partner (by norm_num)

/-- The two distinct depth-two parameters have exactly the same realization on
every two-token scalar input. -/
theorem exoticSource_realization_eq_partner :
    realizeDeep (t := 2) exoticNormalization (fixedDepthToDeep exoticSource) =
      realizeDeep exoticNormalization (fixedDepthToDeep exoticPartner) := by
  exact exoticFamilySource_realization_eq_partner (by norm_num) (by norm_num)

/-- Terminal source-scope counterexample: every normalization hypothesis in
Conjecture 3.10 holds, the source point lies in the certified open dense
coordinate-regular locus, yet its complete functional fiber is non-singleton. -/
theorem conjecture_3_10_source_scope_counterexample :
    Function.Injective exoticNormalization ∧
      exoticNormalization 0 = 1 ∧
      (∀ z, 0 < exoticNormalization z) ∧
      CoordinateRegular 0 0 exoticSource ∧
      exoticSource ≠ exoticPartner ∧
      realizeDeep (t := 2) exoticNormalization (fixedDepthToDeep exoticSource) =
        realizeDeep exoticNormalization (fixedDepthToDeep exoticPartner) := by
  exact ⟨exoticNormalization_injective, exoticNormalization_zero,
    exoticNormalization_pos, exoticSource_coordinateRegular,
    exoticSource_ne_partner, exoticSource_realization_eq_partner⟩

end NormalizedDeepAttention
