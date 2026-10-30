module

public import DeepLean.Attention.WeightedHierarchy

/-!
# Identifiability at arbitrary token count

The one-distinguished-versus-repeated probe reduces any token count `n + 1`
with `n > 0` to the multiplicity-weighted scalar hierarchy.
-/

@[expose] public section

namespace NormalizedDeepAttention

theorem weightedRun_append (n : ℝ) (as bs : List ScalarParameter) (z : ScalarPair) :
    weightedRun n (as ++ bs) z = weightedRun n bs (weightedRun n as z) := by
  induction as generalizing z with
  | nil => rfl
  | cons a as ih =>
      simpa only [List.cons_append, weightedRun_cons] using ih (weightedPairStep n a z)

theorem applyLayers_exp_repeatedLinePattern {d n : ℕ} (hn : 0 < n)
    (Ms : List (ScoreMatrix d)) (x u : Fin d → ℝ) (p q : ℝ) :
    applyLayers Real.exp Ms (repeatedLinePattern (n := n) x u p q) =
      repeatedLinePattern x u
        (weightedRun n (scoreParameters Ms x u) (p, q)).1
        (weightedRun n (scoreParameters Ms x u) (p, q)).2 := by
  induction Ms generalizing p q with
  | nil => rfl
  | cons M Ms ih =>
      rw [applyLayers, layer_exp_repeatedLinePattern hn]
      simpa [scoreParameters, weightedRun, weightedPairStep] using
        ih (weightedStepFirst n (dotProduct x (M.mulVec u))
          (dotProduct u (M.mulVec u)) p q)
          (weightedStepRepeated n (dotProduct x (M.mulVec u))
            (dotProduct u (M.mulVec u)) p q)

noncomputable def realizeScoreListAt {d dOut t : ℕ}
    (L : Matrix (Fin dOut) (Fin d) ℝ) (Ms : List (ScoreMatrix d)) :
    Matrix (Fin d) (Fin t) ℝ → Matrix (Fin dOut) (Fin t) ℝ :=
  fun X ↦ L * applyLayers Real.exp Ms X

theorem realizeScoreListAt_repeated_apply {d dOut n : ℕ} (hn : 0 < n)
    (L : Matrix (Fin dOut) (Fin d) ℝ) (Ms : List (ScoreMatrix d))
    (x u : Fin d → ℝ) (p q : ℝ) (r : Fin dOut) (i : Fin (n + 1)) :
    realizeScoreListAt L Ms (repeatedLinePattern (n := n) x u p q) r i =
      (L.mulVec x) r +
        (Fin.cases (weightedRun n (scoreParameters Ms x u) (p, q)).1
          (fun _ ↦ (weightedRun n (scoreParameters Ms x u) (p, q)).2) i) *
          (L.mulVec u) r := by
  rw [realizeScoreListAt, applyLayers_exp_repeatedLinePattern hn]
  let z := weightedRun n (scoreParameters Ms x u) (p, q)
  change (∑ c : Fin d, L r c * repeatedLinePattern x u z.1 z.2 c i) =
    (∑ c : Fin d, L r c * x c) +
      Fin.cases z.1 (fun _ ↦ z.2) i * ∑ c : Fin d, L r c * u c
  have hentry (c : Fin d) : repeatedLinePattern x u z.1 z.2 c i =
      x c + Fin.cases z.1 (fun _ ↦ z.2) i * u c := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa using congrFun (repeatedLinePattern_col_zero x u z.1 z.2) c
    · simpa using congrFun (repeatedLinePattern_col_succ x u z.1 z.2 j) c
  calc
    _ = ∑ c : Fin d, (L r c * x c +
        Fin.cases z.1 (fun _ ↦ z.2) i * (L r c * u c)) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [hentry]
      ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

theorem realizeDeep_eq_realizeScoreListAt {d dOut t : ℕ} (W : DeepWeights d dOut) :
    realizeDeep (t := t) Real.exp W = realizeScoreListAt W.L (W.M₁ :: W.rest) := rfl

/-- If the final virtual value map is zero, every score parameter is invisible. -/
theorem realizeDeep_zero_final_score_independent {d dOut t : ℕ} (S : ℝ → ℝ)
    (M₁ M₁' : ScoreMatrix d) (rest rest' : List (ScoreMatrix d)) :
    realizeDeep (t := t) S
        ⟨M₁, rest, (0 : Matrix (Fin dOut) (Fin d) ℝ)⟩ =
      realizeDeep S ⟨M₁', rest', (0 : Matrix (Fin dOut) (Fin d) ℝ)⟩ := by
  funext X
  simp [realizeDeep]

def zeroFinalSource (d dOut : ℕ) : DeepWeights d dOut := ⟨0,[],0⟩

def zeroFinalPartner (d dOut : ℕ) : DeepWeights d dOut := ⟨1,[],0⟩

theorem zeroFinalSource_ne_partner (d dOut : ℕ) (hd : 0 < d) :
    zeroFinalSource d dOut ≠ zeroFinalPartner d dOut := by
  intro h
  have he := congrFun (congrFun (congrArg DeepWeights.M₁ h) ⟨0,hd⟩) ⟨0,hd⟩
  norm_num [zeroFinalSource, zeroFinalPartner] at he

theorem zero_final_nontrivial_fiber {d dOut t : ℕ} (hd : 0 < d) (S : ℝ → ℝ) :
    zeroFinalSource d dOut ≠ zeroFinalPartner d dOut ∧
      realizeDeep (t := t) S (zeroFinalSource d dOut) =
        realizeDeep S (zeroFinalPartner d dOut) := by
  exact ⟨zeroFinalSource_ne_partner d dOut hd,
    realizeDeep_zero_final_score_independent S 0 1 [] []⟩

theorem scoreAfterPrefix_probeAt {d dOut n : ℕ} (hn : 0 < n)
    (L : Matrix (Fin dOut) (Fin d) ℝ)
    (pref : List (ScoreMatrix d)) (N N' : ScoreMatrix d)
    (suffix suffix' : List (ScoreMatrix d))
    (hlen : suffix.length = suffix'.length)
    (hEq : realizeScoreListAt (t := n + 1) L (pref ++ N :: suffix) =
      realizeScoreListAt L (pref ++ N' :: suffix'))
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
  let z : ℝ → ScalarPair := fun ε ↦ weightedRun n prefixParams (ε,-ε)
  let scale : ℝ → ℝ := fun ε ↦ (z ε).1 - (z ε).2
  let a := dotProduct x (N.mulVec u)
  let b := dotProduct u (N.mulVec u)
  let a' := dotProduct x (N'.mulVec u)
  let b' := dotProduct u (N'.mulVec u)
  let y : ℝ → ScalarPair := fun ε ↦ weightedPairStep n (a,b) (z ε)
  let y' : ℝ → ScalarPair := fun ε ↦ weightedPairStep n (a',b') (z ε)
  let out : ℝ → ScalarPair := fun ε ↦ weightedRun n suffixParams (y ε)
  let out' : ℝ → ScalarPair := fun ε ↦ weightedRun n suffixParams' (y' ε)
  let F := nhdsWithin (0 : ℝ) ({0}ᶜ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he0 : Filter.Tendsto (fun ε : ℝ ↦ ε) F (nhds 0) :=
    Filter.tendsto_id.mono_left nhdsWithin_le_nhds
  have heneg : Filter.Tendsto (fun ε : ℝ ↦ -ε) F (nhds 0) := by
    simpa using he0.neg
  have hz0 : Filter.Tendsto (fun ε ↦ (z ε).1) F (nhds 0) := by
    simpa [z] using tendsto_weightedRun_zero n prefixParams
      (fun ε : ℝ ↦ (ε,-ε)) hnR he0 heneg 0
  have hz1 : Filter.Tendsto (fun ε ↦ (z ε).2) F (nhds 0) := by
    simpa [z] using tendsto_weightedRun_zero n prefixParams
      (fun ε : ℝ ↦ (ε,-ε)) hnR he0 heneg 1
  have hs : Filter.Tendsto scale F (nhds 0) := by simpa [scale] using hz0.sub hz1
  have hparam : ∀ θ ∈ prefixParams, θ.2 ≠ 0 := by
    intro θ hθ
    simp only [prefixParams, scoreParameters, List.mem_map] at hθ
    obtain ⟨M,hM,rfl⟩ := hθ
    exact huPrefix M hM
  have hsne : ∀ᶠ ε in F, scale ε ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact weightedRun_gap_ne_zero n prefixParams (ε,-ε) hnR
      (by simpa using sub_ne_zero.mpr hε) hparam
  have hgap : Filter.Tendsto (fun ε ↦ ((z ε).1 - (z ε).2) / scale ε) F
      (nhds 1) := by
    have heq : (fun ε ↦ ((z ε).1 - (z ε).2) / scale ε) =ᶠ[F]
        fun _ ↦ (1 : ℝ) := by
      filter_upwards [hsne] with ε hε
      simp [scale,hε]
    exact tendsto_const_nhds.congr' heq.symm
  have hlenParams : suffixParams.length = suffixParams'.length := by
    simpa [suffixParams,suffixParams',scoreParameters] using hlen
  have hlim : Filter.Tendsto (fun ε ↦
      (scalarAt (out ε).1 (out ε).2 0 - scalarAt (out' ε).1 (out' ε).2 0) /
        (scale ε)^2) F (nhds ((a-a') * (n/(1+n)^2))) := by
    simpa [out,out',y,y'] using tendsto_weightedRun_next_comparison
      n a b a' b' suffixParams suffixParams' hlenParams
      (fun ε ↦ (z ε).1) (fun ε ↦ (z ε).2) scale hnR hz0 hz1 hs hgap hsne 0
  have hout : out = out' := by
    funext ε
    apply Prod.ext
    · have heval := congrFun hEq (repeatedLinePattern (n := n) x u ε (-ε))
      have he := congrFun (congrFun heval r) 0
      rw [realizeScoreListAt_repeated_apply hn,
        realizeScoreListAt_repeated_apply hn] at he
      simp only [scoreParameters, List.map_append, weightedRun_append, weightedRun_cons,
        prefixParams, suffixParams, suffixParams', z, y, y', out, out'] at he
      change (L.mulVec x) r + (out ε).1 * (L.mulVec u) r =
        (L.mulVec x) r + (out' ε).1 * (L.mulVec u) r at he
      exact mul_right_cancel₀ hr (add_left_cancel he)
    · have heval := congrFun hEq (repeatedLinePattern (n := n) x u ε (-ε))
      have he := congrFun (congrFun heval r) (Fin.succ ⟨0,hn⟩)
      rw [realizeScoreListAt_repeated_apply hn,
        realizeScoreListAt_repeated_apply hn] at he
      simp only [scoreParameters, List.map_append, weightedRun_append, weightedRun_cons,
        prefixParams, suffixParams, suffixParams', z, y, y', out, out'] at he
      change (L.mulVec x) r + (out ε).2 * (L.mulVec u) r =
        (L.mulVec x) r + (out' ε).2 * (L.mulVec u) r at he
      exact mul_right_cancel₀ hr (add_left_cancel he)
  have hzero : Filter.Tendsto (fun _ : ℝ ↦ (0 : ℝ)) F
      (nhds ((a-a') * (n/(1+n)^2))) := by
    simpa [hout] using hlim
  have hz := tendsto_nhds_unique tendsto_const_nhds hzero
  have hprod : (a-a') * (n/(1+n)^2) = 0 := by simpa using hz.symm
  have hk : (n/(1+n)^2 : ℝ) ≠ 0 := by positivity
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hk)

theorem scoreAfterPrefix_identifiableAt {d dOut n : ℕ} (hn : 0 < n)
    (L : Matrix (Fin dOut) (Fin d) ℝ)
    (pref : List (ScoreMatrix d)) (N N' : ScoreMatrix d)
    (suffix suffix' : List (ScoreMatrix d))
    (hL : L ≠ 0) (hreg : ∀ M ∈ pref, M.transpose ≠ -M)
    (hlen : suffix.length = suffix'.length)
    (hEq : realizeScoreListAt (t := n + 1) L (pref ++ N :: suffix) =
      realizeScoreListAt L (pref ++ N' :: suffix')) : N = N' := by
  apply matrix_eq_of_eq_on_visible_nonisotropic_list L pref N N' hL hreg
  intro u huPrefix huL
  exact scoreAfterPrefix_probeAt hn L pref N N' suffix suffix' hlen hEq u huPrefix huL

private theorem scoreList_suffix_eqAt_properPrefix {d dOut n : ℕ} (hn : 0 < n)
    (L : Matrix (Fin dOut) (Fin d) ℝ) (hL : L ≠ 0)
    (pref Ms Ms' : List (ScoreMatrix d))
    (hprefix : ∀ M ∈ pref, M.transpose ≠ -M)
    (hproper : ProperPrefixNonSkew Ms)
    (hlen : Ms.length = Ms'.length)
    (hEq : realizeScoreListAt (t := n + 1) L (pref ++ Ms) =
      realizeScoreListAt L (pref ++ Ms')) : Ms = Ms' := by
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
          have hN : N = N' := scoreAfterPrefix_identifiableAt hn L pref N N' Ms Ms'
            hL hprefix hlen' (by simpa only [List.append_assoc] using hEq)
          subst N'
          cases Ms with
          | nil =>
              cases Ms' with
              | nil => rfl
              | cons _ _ => simp at hlen'
          | cons P Ps =>
              cases Ms' with
              | nil => simp at hlen'
              | cons P' Ps' =>
                  congr 1
                  apply ih (pref ++ [N]) (P' :: Ps')
                  · intro M hM
                    rcases List.mem_append.mp hM with hp | hNmem
                    · exact hprefix M hp
                    · have hMN : M = N := by simpa using hNmem
                      subst M
                      exact hproper N (by simp)
                  · intro M hM
                    exact hproper M (by
                      simp only [ProperPrefixNonSkew, List.dropLast_cons_cons,
                        List.mem_cons] at hproper ⊢
                      exact Or.inr hM)
                  · exact hlen'
                  · simpa [List.append_assoc] using hEq

/-- Equal realizations of equally long score lists identify every score when
only the proper source prefix is non-skew.  The final source score is
unrestricted. -/
theorem scoreList_fiber_singletonAt_properPrefix {d dOut n : ℕ} (hn : 0 < n)
    (L : Matrix (Fin dOut) (Fin d) ℝ) (Ms Ms' : List (ScoreMatrix d))
    (hL : L ≠ 0) (hproper : ProperPrefixNonSkew Ms)
    (hlen : Ms.length = Ms'.length)
    (hEq : realizeScoreListAt (t := n + 1) L Ms = realizeScoreListAt L Ms') : Ms = Ms' := by
  exact scoreList_suffix_eqAt_properPrefix hn L hL [] Ms Ms' (by simp)
    hproper hlen (by simpa using hEq)

/-- Arbitrary-token exponential identifiability with the sharp peeling
hypothesis: the terminal source score may be skew.  At depth one the score
hypothesis is vacuous. -/
theorem realizeDeep_exp_succ_fiber_singleton_properPrefix {d dOut n : ℕ}
    (hn : 0 < n) (W W' : DeepWeights d dOut) (hL : W.L ≠ 0)
    (hproper : ProperPrefixNonSkew (W.M₁ :: W.rest))
    (hdepth : W.rest.length = W'.rest.length)
    (hEq : realizeDeep (t := n + 1) Real.exp W = realizeDeep Real.exp W') : W = W' := by
  have hLL := deepFinalValue_identifiable Real.exp Real.exp_pos W W' (by omega) hEq
  have hscores : W.M₁ :: W.rest = W'.M₁ :: W'.rest := by
    apply scoreList_fiber_singletonAt_properPrefix hn W.L _ _ hL hproper
    · simpa using hdepth
    · have he := hEq
      rw [realizeDeep_eq_realizeScoreListAt W,
        realizeDeep_eq_realizeScoreListAt W'] at he
      rw [← hLL] at he
      exact he
  cases W
  cases W'
  simp_all

/-- Final sharpened exponential theorem: only the proper source score prefix
must be non-skew. -/
theorem realizeDeep_exp_fiber_singleton_properPrefix {d dOut t : ℕ} (ht : 2 ≤ t)
    (W W' : DeepWeights d dOut) (hL : W.L ≠ 0)
    (hproper : ProperPrefixNonSkew (W.M₁ :: W.rest))
    (hdepth : W.rest.length = W'.rest.length)
    (hEq : realizeDeep (t := t) Real.exp W = realizeDeep Real.exp W') : W = W' := by
  cases t with
  | zero => omega
  | succ n =>
      apply realizeDeep_exp_succ_fiber_singleton_properPrefix (n := n) (by omega)
        W W' hL hproper hdepth
      simpa [Nat.succ_eq_add_one] using hEq

private theorem scoreList_suffix_eqAt {d dOut n : ℕ} (hn : 0 < n)
    (L : Matrix (Fin dOut) (Fin d) ℝ) (hL : L ≠ 0)
    (pref Ms Ms' : List (ScoreMatrix d))
    (hprefix : ∀ M ∈ pref, M.transpose ≠ -M)
    (hreg : ∀ M ∈ Ms, M.transpose ≠ -M)
    (hlen : Ms.length = Ms'.length)
    (hEq : realizeScoreListAt (t := n + 1) L (pref ++ Ms) =
      realizeScoreListAt L (pref ++ Ms')) : Ms = Ms' := by
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
          have hN : N = N' := scoreAfterPrefix_identifiableAt hn L pref N N' Ms Ms'
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

theorem scoreList_fiber_singletonAt {d dOut n : ℕ} (hn : 0 < n)
    (L : Matrix (Fin dOut) (Fin d) ℝ) (Ms Ms' : List (ScoreMatrix d))
    (hL : L ≠ 0) (hreg : ∀ M ∈ Ms, M.transpose ≠ -M)
    (hlen : Ms.length = Ms'.length)
    (hEq : realizeScoreListAt (t := n + 1) L Ms = realizeScoreListAt L Ms') : Ms = Ms' := by
  exact scoreList_suffix_eqAt hn L hL [] Ms Ms' (by simp) hreg hlen (by simpa using hEq)

/-- Singleton fibers at every token count `n + 1 ≥ 2` and every positive depth. -/
theorem realizeDeep_exp_succ_fiber_singleton {d dOut n : ℕ} (hn : 0 < n)
    (W W' : DeepWeights d dOut) (hL : W.L ≠ 0)
    (hreg : ∀ M ∈ W.M₁ :: W.rest, M.transpose ≠ -M)
    (hdepth : W.rest.length = W'.rest.length)
    (hEq : realizeDeep (t := n + 1) Real.exp W = realizeDeep Real.exp W') : W = W' := by
  have hLL := deepFinalValue_identifiable Real.exp Real.exp_pos W W' (by omega) hEq
  have hscores : W.M₁ :: W.rest = W'.M₁ :: W'.rest := by
    apply scoreList_fiber_singletonAt hn W.L _ _ hL hreg
    · simpa using hdepth
    · have he := hEq
      rw [realizeDeep_eq_realizeScoreListAt W,
        realizeDeep_eq_realizeScoreListAt W'] at he
      rw [← hLL] at he
      exact he
  cases W
  cases W'
  simp_all

/-- Final arbitrary-token, arbitrary-positive-depth singleton-fiber theorem. -/
theorem realizeDeep_exp_fiber_singleton {d dOut t : ℕ} (ht : 2 ≤ t)
    (W W' : DeepWeights d dOut) (hL : W.L ≠ 0)
    (hreg : ∀ M ∈ W.M₁ :: W.rest, M.transpose ≠ -M)
    (hdepth : W.rest.length = W'.rest.length)
    (hEq : realizeDeep (t := t) Real.exp W = realizeDeep Real.exp W') : W = W' := by
  cases t with
  | zero => omega
  | succ n =>
      apply realizeDeep_exp_succ_fiber_singleton (n := n) (by omega)
        W W' hL hreg hdepth
      simpa [Nat.succ_eq_add_one] using hEq

end NormalizedDeepAttention
