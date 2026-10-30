module

public import DeepLean.Attention.DeepHierarchy
public import DeepLean.Attention.MultiAvoidance

/-!
# Generic identifiability at arbitrary finite depth

The theorem in this file proves singleton fibers for every positive finite depth
at two tokens, on the explicit locus where the final value map is nonzero and
all virtual score matrices are non-skew.
-/

@[expose] public section

namespace NormalizedDeepAttention

/-- Explicit source regularity used by the arbitrary-depth full-fiber theorem. -/
def RegularDeep {d dOut : ℕ} (W : DeepWeights d dOut) : Prop :=
  W.L ≠ 0 ∧ ∀ M ∈ W.M₁ :: W.rest, M.transpose ≠ -M

noncomputable def scoreParameters {d : ℕ} (Ms : List (ScoreMatrix d))
    (x u : Fin d → ℝ) : List ScalarParameter :=
  Ms.map fun M ↦ (dotProduct x (M.mulVec u), dotProduct u (M.mulVec u))

theorem scalarRun_append (as bs : List ScalarParameter) (z : ScalarPair) :
    scalarRun (as ++ bs) z = scalarRun bs (scalarRun as z) := by
  induction as generalizing z with
  | nil => rfl
  | cons a as ih => simpa only [List.cons_append, scalarRun_cons] using ih (scalarPairStep a z)

theorem applyLayers_exp_linePair {d : ℕ} (Ms : List (ScoreMatrix d))
    (x u : Fin d → ℝ) (p q : ℝ) :
    applyLayers Real.exp Ms (linePair x u p q) =
      linePair x u (scalarRun (scoreParameters Ms x u) (p, q)).1
        (scalarRun (scoreParameters Ms x u) (p, q)).2 := by
  induction Ms generalizing p q with
  | nil => rfl
  | cons M Ms ih =>
      rw [applyLayers, layer_exp_linePair]
      simpa [scoreParameters, scalarRun, scalarPairStep] using
        ih (scalarStepZero (dotProduct x (M.mulVec u)) (dotProduct u (M.mulVec u)) p q)
          (scalarStepOne (dotProduct x (M.mulVec u)) (dotProduct u (M.mulVec u)) p q)

noncomputable def realizeScoreList {d dOut : ℕ}
    (L : Matrix (Fin dOut) (Fin d) ℝ) (Ms : List (ScoreMatrix d)) :
    Matrix (Fin d) (Fin 2) ℝ → Matrix (Fin dOut) (Fin 2) ℝ :=
  fun X ↦ L * applyLayers Real.exp Ms X

theorem realizeScoreList_linePair_apply {d dOut : ℕ}
    (L : Matrix (Fin dOut) (Fin d) ℝ) (Ms : List (ScoreMatrix d))
    (x u : Fin d → ℝ) (p q : ℝ) (r : Fin dOut) (i : Fin 2) :
    realizeScoreList L Ms (linePair x u p q) r i =
      (L.mulVec x) r +
        scalarAt (scalarRun (scoreParameters Ms x u) (p, q)).1
          (scalarRun (scoreParameters Ms x u) (p, q)).2 i * (L.mulVec u) r := by
  rw [realizeScoreList, applyLayers_exp_linePair]
  let z := scalarRun (scoreParameters Ms x u) (p, q)
  change (∑ c : Fin d, L r c * linePair x u z.1 z.2 c i) =
    (∑ c : Fin d, L r c * x c) + scalarAt z.1 z.2 i * ∑ c : Fin d, L r c * u c
  have hentry (c : Fin d) : linePair x u z.1 z.2 c i =
      x c + scalarAt z.1 z.2 i * u c := by
    fin_cases i
    · simpa using congrFun (linePair_col_zero x u z.1 z.2) c
    · simpa using congrFun (linePair_col_one x u z.1 z.2) c
  calc
    _ = ∑ c : Fin d, (L r c * x c + scalarAt z.1 z.2 i * (L r c * u c)) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [hentry]
      ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

theorem realizeDeep_eq_realizeScoreList {d dOut : ℕ} (W : DeepWeights d dOut) :
    realizeDeep (t := 2) Real.exp W = realizeScoreList W.L (W.M₁ :: W.rest) := by
  rfl

/-- With one token every normalized layer is the identity, so all score
matrices are unobservable. -/
theorem layer_one_token {d : ℕ} (M : ScoreMatrix d)
    (X : Matrix (Fin d) (Fin 1) ℝ) : layer Real.exp M X = X := by
  have hX : X = constantTokenMatrix (t := 1) (X.col 0) := by
    ext r i
    fin_cases i
    rfl
  rw [hX, layer_constantTokenMatrix Real.exp Real.exp_pos M (X.col 0) (by omega)]

theorem applyLayers_one_token {d : ℕ} (Ms : List (ScoreMatrix d))
    (X : Matrix (Fin d) (Fin 1) ℝ) : applyLayers Real.exp Ms X = X := by
  induction Ms generalizing X with
  | nil => rfl
  | cons M Ms ih =>
      rw [applyLayers, layer_one_token, ih]

theorem realizeDeep_one_token {d dOut : ℕ} (W : DeepWeights d dOut)
    (X : Matrix (Fin d) (Fin 1) ℝ) : realizeDeep Real.exp W X = W.L * X := by
  rw [realizeDeep, layer_one_token, applyLayers_one_token]

/-- Exact sequence-length-one failure: equal final value maps give equal
functions regardless of depth or score matrices. -/
theorem realizeDeep_one_token_score_independent {d dOut : ℕ}
    (W W' : DeepWeights d dOut) (hL : W.L = W'.L) :
    realizeDeep (t := 1) Real.exp W = realizeDeep Real.exp W' := by
  funext X
  rw [realizeDeep_one_token, realizeDeep_one_token, hL]

/-- Functional equality recovers the score immediately following a known
prefix, even with arbitrary unknown equally long suffixes. -/
theorem scoreAfterPrefix_probe {d dOut : ℕ}
    (L : Matrix (Fin dOut) (Fin d) ℝ)
    (pref : List (ScoreMatrix d)) (N N' : ScoreMatrix d)
    (suffix suffix' : List (ScoreMatrix d))
    (hlen : suffix.length = suffix'.length)
    (hEq : realizeScoreList L (pref ++ N :: suffix) =
      realizeScoreList L (pref ++ N' :: suffix'))
    (u : Fin d → ℝ)
    (huPrefix : ∀ M ∈ pref, dotProduct u (M.mulVec u) ≠ 0)
    (huL : L.mulVec u ≠ 0) :
    ∀ x : Fin d → ℝ, dotProduct x (N.mulVec u) = dotProduct x (N'.mulVec u) := by
  intro x
  obtain ⟨r, hr⟩ : ∃ r, (L.mulVec u) r ≠ 0 := by
    by_contra h
    push Not at h
    exact huL (funext h)
  let prefixParams := scoreParameters pref x u
  let suffixParams := scoreParameters suffix x u
  let suffixParams' := scoreParameters suffix' x u
  let z : ℝ → ScalarPair := fun ε ↦ scalarRun prefixParams (ε, -ε)
  let scale : ℝ → ℝ := fun ε ↦ (z ε).1 - (z ε).2
  let a := dotProduct x (N.mulVec u)
  let b := dotProduct u (N.mulVec u)
  let a' := dotProduct x (N'.mulVec u)
  let b' := dotProduct u (N'.mulVec u)
  let y : ℝ → ScalarPair := fun ε ↦ scalarPairStep (a, b) (z ε)
  let y' : ℝ → ScalarPair := fun ε ↦ scalarPairStep (a', b') (z ε)
  let out : ℝ → ScalarPair := fun ε ↦ scalarRun suffixParams (y ε)
  let out' : ℝ → ScalarPair := fun ε ↦ scalarRun suffixParams' (y' ε)
  let F := nhdsWithin (0 : ℝ) ({0}ᶜ)
  have he0 : Filter.Tendsto (fun ε : ℝ ↦ ε) F (nhds 0) :=
    Filter.tendsto_id.mono_left nhdsWithin_le_nhds
  have heneg : Filter.Tendsto (fun ε : ℝ ↦ -ε) F (nhds 0) := by
    simpa using he0.neg
  have hz0 : Filter.Tendsto (fun ε ↦ (z ε).1) F (nhds 0) := by
    simpa [z] using tendsto_scalarRun_zero prefixParams (fun ε : ℝ ↦ (ε, -ε))
      he0 heneg 0
  have hz1 : Filter.Tendsto (fun ε ↦ (z ε).2) F (nhds 0) := by
    simpa [z] using tendsto_scalarRun_zero prefixParams (fun ε : ℝ ↦ (ε, -ε))
      he0 heneg 1
  have hs : Filter.Tendsto scale F (nhds 0) := by simpa [scale] using hz0.sub hz1
  have hparam : ∀ θ ∈ prefixParams, θ.2 ≠ 0 := by
    intro θ hθ
    simp only [prefixParams, scoreParameters, List.mem_map] at hθ
    obtain ⟨M, hM, rfl⟩ := hθ
    exact huPrefix M hM
  have hsne : ∀ᶠ ε in F, scale ε ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact scalarRun_gap_ne_zero prefixParams (ε, -ε) (by simpa using sub_ne_zero.mpr hε)
      hparam
  have hgap : Filter.Tendsto (fun ε ↦ ((z ε).1 - (z ε).2) / scale ε) F
      (nhds 1) := by
    have heq : (fun ε ↦ ((z ε).1 - (z ε).2) / scale ε) =ᶠ[F]
        fun _ ↦ (1 : ℝ) := by
      filter_upwards [hsne] with ε hε
      simp [scale, hε]
    exact tendsto_const_nhds.congr' heq.symm
  have hlenParams : suffixParams.length = suffixParams'.length := by
    simpa [suffixParams, suffixParams', scoreParameters] using hlen
  have hlim : Filter.Tendsto (fun ε ↦
      (scalarAt (out ε).1 (out ε).2 0 - scalarAt (out' ε).1 (out' ε).2 0) /
        (scale ε)^2) F (nhds ((a-a')/4)) := by
    simpa [out, out', y, y'] using tendsto_scalarRun_next_comparison
      a b a' b' suffixParams suffixParams' hlenParams
      (fun ε ↦ (z ε).1) (fun ε ↦ (z ε).2) scale hz0 hz1 hs hgap hsne 0
  have hout : out = out' := by
    funext ε
    apply Prod.ext
    · have heval := congrFun hEq (linePair x u ε (-ε))
      have he := congrFun (congrFun heval r) 0
      rw [realizeScoreList_linePair_apply, realizeScoreList_linePair_apply] at he
      simp only [scoreParameters, List.map_append, scalarRun_append, scalarRun_cons,
        prefixParams, suffixParams, suffixParams', z, y, y', out, out'] at he
      change (L.mulVec x) r + (out ε).1 * (L.mulVec u) r =
        (L.mulVec x) r + (out' ε).1 * (L.mulVec u) r at he
      exact mul_right_cancel₀ hr (add_left_cancel he)
    · have heval := congrFun hEq (linePair x u ε (-ε))
      have he := congrFun (congrFun heval r) 1
      rw [realizeScoreList_linePair_apply, realizeScoreList_linePair_apply] at he
      simp only [scoreParameters, List.map_append, scalarRun_append, scalarRun_cons,
        prefixParams, suffixParams, suffixParams', z, y, y', out, out'] at he
      change (L.mulVec x) r + (out ε).2 * (L.mulVec u) r =
        (L.mulVec x) r + (out' ε).2 * (L.mulVec u) r at he
      exact mul_right_cancel₀ hr (add_left_cancel he)
  have hzero : Filter.Tendsto (fun _ : ℝ ↦ (0 : ℝ)) F (nhds ((a-a')/4)) := by
    simpa [hout] using hlim
  have hz := tendsto_nhds_unique tendsto_const_nhds hzero
  have : (a-a')/4 = 0 := by simpa using hz.symm
  exact sub_eq_zero.mp (by linarith)

theorem scoreAfterPrefix_identifiable {d dOut : ℕ}
    (L : Matrix (Fin dOut) (Fin d) ℝ)
    (pref : List (ScoreMatrix d)) (N N' : ScoreMatrix d)
    (suffix suffix' : List (ScoreMatrix d))
    (hL : L ≠ 0) (hreg : ∀ M ∈ pref, M.transpose ≠ -M)
    (hlen : suffix.length = suffix'.length)
    (hEq : realizeScoreList L (pref ++ N :: suffix) =
      realizeScoreList L (pref ++ N' :: suffix')) : N = N' := by
  apply matrix_eq_of_eq_on_visible_nonisotropic_list L pref N N' hL hreg
  intro u huPrefix huL
  exact scoreAfterPrefix_probe L pref N N' suffix suffix' hlen hEq u huPrefix huL

private theorem scoreList_suffix_eq {d dOut : ℕ}
    (L : Matrix (Fin dOut) (Fin d) ℝ) (hL : L ≠ 0)
    (pref Ms Ms' : List (ScoreMatrix d))
    (hprefix : ∀ M ∈ pref, M.transpose ≠ -M)
    (hreg : ∀ M ∈ Ms, M.transpose ≠ -M)
    (hlen : Ms.length = Ms'.length)
    (hEq : realizeScoreList L (pref ++ Ms) = realizeScoreList L (pref ++ Ms')) :
    Ms = Ms' := by
  induction Ms generalizing pref Ms' with
  | nil =>
      cases Ms' with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons N Ms ih =>
      cases Ms' with
      | nil => simp at hlen
      | cons N' Ms' =>
          have hlen' : Ms.length = Ms'.length := by simpa using hlen
          have hN : N = N' := scoreAfterPrefix_identifiable L pref N N' Ms Ms'
            hL hprefix hlen' (by simpa only [List.append_assoc] using hEq)
          subst N'
          congr 1
          apply ih (pref ++ [N]) Ms'
          · intro M hM
            rcases List.mem_append.mp hM with hp | hNmem
            · exact hprefix M hp
            · have hMN : M = N := by simpa using hNmem
              subst M
              exact hreg N (by simp)
          · intro M hM
            exact hreg M (by simp [hM])
          · exact hlen'
          · simpa [List.append_assoc] using hEq

/-- Equal realizations by equally long score lists have equal score lists on
the explicit non-skew locus. -/
theorem scoreList_fiber_singleton {d dOut : ℕ}
    (L : Matrix (Fin dOut) (Fin d) ℝ) (Ms Ms' : List (ScoreMatrix d))
    (hL : L ≠ 0) (hreg : ∀ M ∈ Ms, M.transpose ≠ -M)
    (hlen : Ms.length = Ms'.length)
    (hEq : realizeScoreList L Ms = realizeScoreList L Ms') : Ms = Ms' := by
  exact scoreList_suffix_eq L hL [] Ms Ms' (by simp) hreg hlen (by simpa using hEq)

/-- Arbitrary-positive-depth singleton-fiber theorem for two-token exponential
normalized attention.  The depth is fixed by equality of the `rest` lengths. -/
theorem realizeDeep_exp_two_fiber_singleton {d dOut : ℕ}
    (W W' : DeepWeights d dOut)
    (hL : W.L ≠ 0)
    (hreg : ∀ M ∈ W.M₁ :: W.rest, M.transpose ≠ -M)
    (hdepth : W.rest.length = W'.rest.length)
    (hEq : realizeDeep (t := 2) Real.exp W = realizeDeep Real.exp W') : W = W' := by
  have hLL := deepFinalValue_identifiable Real.exp Real.exp_pos W W' (by omega) hEq
  have hscores : W.M₁ :: W.rest = W'.M₁ :: W'.rest := by
    apply scoreList_fiber_singleton W.L _ _ hL hreg
    · simpa using hdepth
    · have he := hEq
      rw [realizeDeep_eq_realizeScoreList W, realizeDeep_eq_realizeScoreList W'] at he
      rw [← hLL] at he
      exact he
  cases W
  cases W'
  simp_all

end NormalizedDeepAttention
