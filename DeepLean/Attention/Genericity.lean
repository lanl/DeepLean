module

public import DeepLean.Attention.ArbitraryTokens

/-!
# A certified open dense fixed-depth locus

For fixed tail depth `k`, parameters form a finite-dimensional Euclidean product.
Requiring one fixed diagonal entry of every score matrix and one fixed entry of
the final value matrix to be nonzero gives an open dense subset of the regular
locus used by the full-fiber theorem.
-/

@[expose] public section

namespace NormalizedDeepAttention

def CoordinateRegular {d dOut k : ℕ} (i : Fin d) (o : Fin dOut)
    (W : FixedDepthWeights d dOut k) : Prop :=
  W.1 i i ≠ 0 ∧ (∀ j, W.2.1 j i i ≠ 0) ∧ W.2.2 o i ≠ 0

/-- Readable depth-indexed form of the sharpened coordinate locus. -/
theorem properCoordinateRegular_iff {d dOut k : ℕ}
    (i : Fin d) (o : Fin dOut) (W : FixedDepthWeights d dOut k) :
    ProperCoordinateRegular i o W ↔
      match k with
      | 0 => W.2.2 o i ≠ 0
      | k + 1 => W.1 i i ≠ 0 ∧
          (∀ j : Fin k, W.2.1 j.castSucc i i ≠ 0) ∧ W.2.2 o i ≠ 0 := by
  cases k with
  | zero => simp [ProperCoordinateRegular]
  | succ k =>
      have hdrop : (W.1 :: List.ofFn W.2.1).dropLast =
          W.1 :: List.ofFn (fun j : Fin k ↦ W.2.1 j.castSucc) := by
        rw [List.ofFn_succ']
        change ((W.1 :: List.ofFn (fun j : Fin k ↦ W.2.1 j.castSucc)).concat
          (W.2.1 (Fin.last k))).dropLast = _
        rw [List.concat_eq_append, List.dropLast_concat]
      rw [ProperCoordinateRegular, hdrop]
      simp only [List.mem_cons, List.mem_ofFn, forall_eq_or_imp]
      aesop

/-- Product form of the sharp locus: the score product ranges over exactly
the proper score prefix and is the empty product at depth one. -/
theorem properCoordinateRegular_iff_product_ne_zero {d dOut k : ℕ}
    (i : Fin d) (o : Fin dOut) (W : FixedDepthWeights d dOut k) :
    ProperCoordinateRegular i o W ↔
      ((W.1 :: List.ofFn W.2.1).dropLast.map (fun M ↦ M i i)).prod *
        W.2.2 o i ≠ 0 := by
  constructor
  · rintro ⟨hscore, hfinal⟩
    exact mul_ne_zero (List.prod_ne_zero fun hzero ↦ by
      rcases List.mem_map.mp hzero with ⟨M, hM, hMi⟩
      exact hscore M hM hMi) hfinal
  · intro hproduct
    rcases mul_ne_zero_iff.mp hproduct with ⟨hscore, hfinal⟩
    refine ⟨?_, hfinal⟩
    intro M hM hzero
    apply hscore
    rw [List.prod_eq_zero_iff]
    exact List.mem_map.mpr ⟨M, hM, hzero⟩

/-- The generic locus is the nonvanishing set of one explicit polynomial: a
product of coordinate projections. -/
theorem coordinateRegular_iff_product_ne_zero {d dOut k : ℕ}
    (i : Fin d) (o : Fin dOut) (W : FixedDepthWeights d dOut k) :
    CoordinateRegular i o W ↔
      W.1 i i * (∏ j : Fin k, W.2.1 j i i) * W.2.2 o i ≠ 0 := by
  constructor
  · rintro ⟨hfirst, hrest, hfinal⟩
    exact mul_ne_zero
      (mul_ne_zero hfirst (Finset.prod_ne_zero_iff.mpr fun j _ ↦ hrest j)) hfinal
  · intro hproduct
    rcases mul_ne_zero_iff.mp hproduct with ⟨hprefix, hfinal⟩
    rcases mul_ne_zero_iff.mp hprefix with ⟨hfirst, hrest⟩
    refine ⟨hfirst, ?_, hfinal⟩
    intro j
    exact Finset.prod_ne_zero_iff.mp hrest j (Finset.mem_univ j)

private theorem matrix_not_skew_of_diag_ne_zero {d : ℕ} (i : Fin d)
    (M : ScoreMatrix d) (hM : M i i ≠ 0) : M.transpose ≠ -M := by
  intro h
  have he := congrFun (congrFun h i) i
  change M i i = -M i i at he
  exact hM (by linarith)

theorem coordinateRegular_regularDeep {d dOut k : ℕ} (i : Fin d) (o : Fin dOut)
    (W : FixedDepthWeights d dOut k) (hW : CoordinateRegular i o W) :
    RegularDeep (fixedDepthToDeep W) := by
  constructor
  · intro hzero
    have he := congrFun (congrFun hzero o) i
    exact hW.2.2 he
  · intro M hM
    change M ∈ W.1 :: List.ofFn W.2.1 at hM
    rw [List.mem_cons] at hM
    rcases hM with hfirst | hrest
    · subst M
      exact matrix_not_skew_of_diag_ne_zero i W.1 hW.1
    · have hrange : M ∈ Set.range W.2.1 := (List.mem_ofFn' W.2.1 M).mp hrest
      obtain ⟨j,rfl⟩ := hrange
      exact matrix_not_skew_of_diag_ne_zero i (W.2.1 j) (hW.2.1 j)

/-- The sharpened coordinate locus implies exactly the nonzero final map and
proper-prefix non-skew hypotheses of the sharp peeling theorem. -/
theorem properCoordinateRegular_properDeep {d dOut k : ℕ}
    (i : Fin d) (o : Fin dOut)
    (W : FixedDepthWeights d dOut k) (hW : ProperCoordinateRegular i o W) :
    (fixedDepthToDeep W).L ≠ 0 ∧
      ProperPrefixNonSkew
        ((fixedDepthToDeep W).M₁ :: (fixedDepthToDeep W).rest) := by
  constructor
  · intro hzero
    have he := congrFun (congrFun hzero o) i
    exact hW.2 he
  · intro M hM
    exact matrix_not_skew_of_diag_ne_zero i M (hW.1 M hM)

private theorem isOpen_firstDiag {d dOut k : ℕ} (i : Fin d) :
    IsOpen {W : FixedDepthWeights d dOut k | W.1 i i ≠ 0} := by
  exact isOpen_ne_fun (by fun_prop) continuous_const

private theorem isOpen_restDiag {d dOut k : ℕ} (i : Fin d) (j : Fin k) :
    IsOpen {W : FixedDepthWeights d dOut k | W.2.1 j i i ≠ 0} := by
  exact isOpen_ne_fun (by fun_prop) continuous_const

private theorem isOpen_finalEntry {d dOut k : ℕ} (i : Fin d) (o : Fin dOut) :
    IsOpen {W : FixedDepthWeights d dOut k | W.2.2 o i ≠ 0} := by
  exact isOpen_ne_fun (by fun_prop) continuous_const

private theorem dense_firstDiag {d dOut k : ℕ} (i : Fin d) :
    Dense {W : FixedDepthWeights d dOut k | W.1 i i ≠ 0} := by
  change Dense ((fun W : FixedDepthWeights d dOut k ↦ W.1 i i) ⁻¹' ({0}ᶜ : Set ℝ))
  apply (dense_compl_singleton 0).preimage
  exact (isOpenMap_eval i).comp ((isOpenMap_eval i).comp isOpenMap_fst)

private theorem dense_restDiag {d dOut k : ℕ} (i : Fin d) (j : Fin k) :
    Dense {W : FixedDepthWeights d dOut k | W.2.1 j i i ≠ 0} := by
  change Dense ((fun W : FixedDepthWeights d dOut k ↦ W.2.1 j i i) ⁻¹'
    ({0}ᶜ : Set ℝ))
  apply (dense_compl_singleton 0).preimage
  exact (isOpenMap_eval i).comp ((isOpenMap_eval i).comp
    ((isOpenMap_eval j).comp (isOpenMap_fst.comp isOpenMap_snd)))

private theorem dense_finalEntry {d dOut k : ℕ} (i : Fin d) (o : Fin dOut) :
    Dense {W : FixedDepthWeights d dOut k | W.2.2 o i ≠ 0} := by
  change Dense ((fun W : FixedDepthWeights d dOut k ↦ W.2.2 o i) ⁻¹'
    ({0}ᶜ : Set ℝ))
  apply (dense_compl_singleton 0).preimage
  exact (isOpenMap_eval i).comp ((isOpenMap_eval o).comp
    (isOpenMap_snd.comp isOpenMap_snd))

private theorem dense_finset_iInter_of_open {X ι : Type*} [TopologicalSpace X]
    (s : ι → Set X) (A : Finset ι)
    (ho : ∀ j, IsOpen (s j)) (hd : ∀ j, Dense (s j)) :
    Dense (⋂ j ∈ A, s j) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
      rw [Finset.set_biInter_insert]
      exact (hd a).inter_of_isOpen_right ih
        (isOpen_biInter_finset fun j _ ↦ ho j)

theorem isOpen_coordinateRegular {d dOut k : ℕ} (i : Fin d) (o : Fin dOut) :
    IsOpen {W : FixedDepthWeights d dOut k | CoordinateRegular i o W} := by
  rw [show {W : FixedDepthWeights d dOut k | CoordinateRegular i o W} =
      {W | W.1 i i ≠ 0} ∩ ((⋂ j, {W | W.2.1 j i i ≠ 0}) ∩
        {W | W.2.2 o i ≠ 0}) by ext W; simp [CoordinateRegular]]
  exact (isOpen_firstDiag i).inter
    ((isOpen_iInter_of_finite fun j ↦ isOpen_restDiag i j).inter
      (isOpen_finalEntry i o))

theorem dense_coordinateRegular {d dOut k : ℕ} (i : Fin d) (o : Fin dOut) :
    Dense {W : FixedDepthWeights d dOut k | CoordinateRegular i o W} := by
  rw [show {W : FixedDepthWeights d dOut k | CoordinateRegular i o W} =
      {W | W.1 i i ≠ 0} ∩ ((⋂ j, {W | W.2.1 j i i ≠ 0}) ∩
        {W | W.2.2 o i ≠ 0}) by ext W; simp [CoordinateRegular]]
  have hrest : Dense (⋂ j, {W : FixedDepthWeights d dOut k | W.2.1 j i i ≠ 0}) := by
    simpa using dense_finset_iInter_of_open
      (fun j : Fin k ↦ {W : FixedDepthWeights d dOut k | W.2.1 j i i ≠ 0})
      Finset.univ (fun j ↦ isOpen_restDiag i j) (fun j ↦ dense_restDiag i j)
  have htail : Dense ((⋂ j, {W : FixedDepthWeights d dOut k | W.2.1 j i i ≠ 0}) ∩
      {W | W.2.2 o i ≠ 0}) :=
    hrest.inter_of_isOpen_right (dense_finalEntry i o) (isOpen_finalEntry i o)
  exact (dense_firstDiag i).inter_of_isOpen_right htail
    ((isOpen_iInter_of_finite fun j ↦ isOpen_restDiag i j).inter
      (isOpen_finalEntry i o))

theorem isOpen_properCoordinateRegular {d dOut k : ℕ} (i : Fin d) (o : Fin dOut) :
    IsOpen {W : FixedDepthWeights d dOut k | ProperCoordinateRegular i o W} := by
  cases k with
  | zero =>
      simpa [properCoordinateRegular_iff] using
        (isOpen_finalEntry (d := d) (dOut := dOut) (k := 0) i o)
  | succ k =>
      rw [show {W : FixedDepthWeights d dOut (k + 1) |
          ProperCoordinateRegular i o W} =
          {W | W.1 i i ≠ 0} ∩
            ((⋂ j : Fin k, {W | W.2.1 j.castSucc i i ≠ 0}) ∩
              {W | W.2.2 o i ≠ 0}) by
        ext W
        simp [properCoordinateRegular_iff]]
      exact (isOpen_firstDiag i).inter
        ((isOpen_iInter_of_finite fun j : Fin k ↦ isOpen_restDiag i j.castSucc).inter
          (isOpen_finalEntry i o))

theorem dense_properCoordinateRegular {d dOut k : ℕ} (i : Fin d) (o : Fin dOut) :
    Dense {W : FixedDepthWeights d dOut k | ProperCoordinateRegular i o W} := by
  cases k with
  | zero =>
      simpa [properCoordinateRegular_iff] using
        (dense_finalEntry (d := d) (dOut := dOut) (k := 0) i o)
  | succ k =>
      rw [show {W : FixedDepthWeights d dOut (k + 1) |
          ProperCoordinateRegular i o W} =
          {W | W.1 i i ≠ 0} ∩
            ((⋂ j : Fin k, {W | W.2.1 j.castSucc i i ≠ 0}) ∩
              {W | W.2.2 o i ≠ 0}) by
        ext W
        simp [properCoordinateRegular_iff]]
      have hrest : Dense
          (⋂ j : Fin k,
            {W : FixedDepthWeights d dOut (k + 1) | W.2.1 j.castSucc i i ≠ 0}) := by
        simpa using dense_finset_iInter_of_open
          (fun j : Fin k ↦
            {W : FixedDepthWeights d dOut (k + 1) | W.2.1 j.castSucc i i ≠ 0})
          Finset.univ (fun j ↦ isOpen_restDiag i j.castSucc)
          (fun j ↦ dense_restDiag i j.castSucc)
      have htail : Dense
          ((⋂ j : Fin k,
              {W : FixedDepthWeights d dOut (k + 1) | W.2.1 j.castSucc i i ≠ 0}) ∩
            {W | W.2.2 o i ≠ 0}) :=
        hrest.inter_of_isOpen_right (dense_finalEntry i o) (isOpen_finalEntry i o)
      exact (dense_firstDiag i).inter_of_isOpen_right htail
        ((isOpen_iInter_of_finite fun j : Fin k ↦ isOpen_restDiag i j.castSucc).inter
          (isOpen_finalEntry i o))

theorem coordinateRegular_nonempty {d dOut k : ℕ} (i : Fin d) (o : Fin dOut) :
    Set.Nonempty {W : FixedDepthWeights d dOut k | CoordinateRegular i o W} := by
  refine ⟨(1, (fun _ ↦ 1, fun _ _ ↦ 1)), ?_⟩
  simp [CoordinateRegular]

theorem properCoordinateRegular_nonempty {d dOut k : ℕ} (i : Fin d) (o : Fin dOut) :
    Set.Nonempty {W : FixedDepthWeights d dOut k | ProperCoordinateRegular i o W} := by
  refine ⟨(1, (fun _ ↦ 1, fun _ _ ↦ 1)), ?_⟩
  cases k <;> simp [properCoordinateRegular_iff]

theorem properCoordinateRegular_full_fiber_singleton {d dOut k t : ℕ}
    (ht : 2 ≤ t) (i : Fin d) (o : Fin dOut)
    (W W' : FixedDepthWeights d dOut k) (hW : ProperCoordinateRegular i o W)
    (hEq : realizeDeep (t := t) Real.exp (fixedDepthToDeep W) =
      realizeDeep Real.exp (fixedDepthToDeep W')) : W = W' := by
  have hdeep := realizeDeep_exp_fiber_singleton_properPrefix ht
    (fixedDepthToDeep W) (fixedDepthToDeep W')
    (properCoordinateRegular_properDeep i o W hW).1
    (properCoordinateRegular_properDeep i o W hW).2
    (by simp [fixedDepthToDeep]) hEq
  have hfirst : W.1 = W'.1 := congrArg DeepWeights.M₁ hdeep
  have hrest : W.2.1 = W'.2.1 := by
    apply List.ofFn_injective
    exact congrArg DeepWeights.rest hdeep
  have hfinal : W.2.2 = W'.2.2 := congrArg DeepWeights.L hdeep
  exact Prod.ext hfirst (Prod.ext hrest hfinal)

theorem coordinateRegular_full_fiber_singleton {d dOut k t : ℕ}
    (ht : 2 ≤ t) (i : Fin d) (o : Fin dOut)
    (W W' : FixedDepthWeights d dOut k) (hW : CoordinateRegular i o W)
    (hEq : realizeDeep (t := t) Real.exp (fixedDepthToDeep W) =
      realizeDeep Real.exp (fixedDepthToDeep W')) : W = W' := by
  have hdeep := realizeDeep_exp_fiber_singleton ht
    (fixedDepthToDeep W) (fixedDepthToDeep W')
    (coordinateRegular_regularDeep i o W hW).1
    (coordinateRegular_regularDeep i o W hW).2 (by simp [fixedDepthToDeep]) hEq
  have hfirst : W.1 = W'.1 := congrArg DeepWeights.M₁ hdeep
  have hrest : W.2.1 = W'.2.1 := by
    apply List.ofFn_injective
    exact congrArg DeepWeights.rest hdeep
  have hfinal : W.2.2 = W'.2.2 := congrArg DeepWeights.L hdeep
  exact Prod.ext hfirst (Prod.ext hrest hfinal)

end NormalizedDeepAttention
