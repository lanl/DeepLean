module

public import DeepLean.Attention.DeepIdentifiability

/-!
# One-versus-many token dynamics

An input with one distinguished token and `n` identical repeated tokens stays
in the same two-class family under normalized attention.  Its scalar dynamics
uses `exp z / (exp z + n)` in place of the ordinary logistic function.
-/

@[expose] public section

namespace NormalizedDeepAttention

/-- Multiplicity-weighted logistic coefficient. -/
noncomputable def weightedSigmoid (n z : ℝ) : ℝ := Real.exp z / (Real.exp z + n)

theorem weightedSigmoid_pos {n z : ℝ} (hn : 0 < n) : 0 < weightedSigmoid n z := by
  unfold weightedSigmoid
  positivity

theorem weightedSigmoid_lt_one {n z : ℝ} (hn : 0 < n) : weightedSigmoid n z < 1 := by
  unfold weightedSigmoid
  have hd : 0 < Real.exp z + n := by positivity
  apply (div_lt_one hd).2
  linarith

theorem weightedSigmoid_injective {n : ℝ} (hn : 0 < n) :
    Function.Injective (weightedSigmoid n) := by
  intro a b h
  have ha : Real.exp a + n ≠ 0 := by positivity
  have hb : Real.exp b + n ≠ 0 := by positivity
  unfold weightedSigmoid at h
  field_simp [ha, hb] at h
  have hn0 : n ≠ 0 := ne_of_gt hn
  have he : Real.exp a = Real.exp b := by
    apply mul_left_cancel₀ hn0
    nlinarith
  exact Real.exp_injective he

@[simp] theorem weightedSigmoid_zero (n : ℝ) :
    weightedSigmoid n 0 = 1 / (1 + n) := by
  simp [weightedSigmoid]

noncomputable def weightedStepFirst (n a b p q : ℝ) : ℝ :=
  q + weightedSigmoid n ((p - q) * (a + p * b)) * (p - q)

noncomputable def weightedStepRepeated (n a b p q : ℝ) : ℝ :=
  q + weightedSigmoid n ((p - q) * (a + q * b)) * (p - q)

noncomputable def weightedPairStep (n : ℝ) (θ : ScalarParameter)
    (z : ScalarPair) : ScalarPair :=
  (weightedStepFirst n θ.1 θ.2 z.1 z.2,
    weightedStepRepeated n θ.1 θ.2 z.1 z.2)

noncomputable def weightedRun (n : ℝ) : List ScalarParameter → ScalarPair → ScalarPair
  | [], z => z
  | θ :: θs, z => weightedRun n θs (weightedPairStep n θ z)

@[simp] theorem weightedRun_nil (n : ℝ) (z : ScalarPair) : weightedRun n [] z = z := rfl

@[simp] theorem weightedRun_cons (n : ℝ) (θ : ScalarParameter)
    (θs : List ScalarParameter) (z : ScalarPair) :
    weightedRun n (θ :: θs) z = weightedRun n θs (weightedPairStep n θ z) := rfl

/-- An affine-line pair represented by one distinguished and `n` repeated tokens. -/
def repeatedLinePattern {d n : ℕ} (x u : Fin d → ℝ) (p q : ℝ) :
    Matrix (Fin d) (Fin (n + 1)) ℝ :=
  firstAndRepeatedTokenMatrix (x + p • u) (x + q • u)

@[simp] theorem repeatedLinePattern_col_zero {d n : ℕ}
    (x u : Fin d → ℝ) (p q : ℝ) :
    (repeatedLinePattern (n := n) x u p q).col 0 = x + p • u := by rfl

@[simp] theorem repeatedLinePattern_col_succ {d n : ℕ}
    (x u : Fin d → ℝ) (p q : ℝ) (j : Fin n) :
    (repeatedLinePattern (n := n) x u p q).col j.succ = x + q • u := by rfl

theorem normalizedAttention_firstAndRepeated_repeated {d d' n : ℕ} (S : ℝ → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) (V : Matrix (Fin d') (Fin d) ℝ)
    (x y : Fin d → ℝ) (r : Fin d') (i : Fin n) :
    normalizedAttention S A V (firstAndRepeatedTokenMatrix (n := n) x y) r i.succ =
      (S (dotProduct y (A.mulVec x)) * (V.mulVec x) r +
        n * S (dotProduct y (A.mulVec y)) * (V.mulVec y) r) /
      (S (dotProduct y (A.mulVec x)) + n * S (dotProduct y (A.mulVec y))) := by
  simp only [normalizedAttention, attentionScore]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  change
    (S (dotProduct y (A.mulVec x)) * (V.mulVec x) r +
      ∑ _ : Fin n, S (dotProduct y (A.mulVec y)) * (V.mulVec y) r) /
        (S (dotProduct y (A.mulVec x)) +
          ∑ _ : Fin n, S (dotProduct y (A.mulVec y))) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private theorem repeatedLine_scoreDifference_first {d n : ℕ} (hn : 0 < n)
    (M : ScoreMatrix d) (x u : Fin d → ℝ) (p q : ℝ) :
    attentionScore M (repeatedLinePattern (n := n) x u p q) 0 0 -
      attentionScore M (repeatedLinePattern (n := n) x u p q) 0
        (Fin.succ ⟨0, hn⟩) =
      (p-q) * (dotProduct x (M.mulVec u) + p * dotProduct u (M.mulVec u)) := by
  simp only [attentionScore, repeatedLinePattern_col_zero, repeatedLinePattern_col_succ,
    Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    dotProduct_smul, smul_dotProduct]
  ring

private theorem repeatedLine_scoreDifference_repeated {d n : ℕ}
    (M : ScoreMatrix d) (x u : Fin d → ℝ) (p q : ℝ) (i : Fin n) :
    attentionScore M (repeatedLinePattern (n := n) x u p q) i.succ 0 -
      attentionScore M (repeatedLinePattern (n := n) x u p q) i.succ i.succ =
      (p-q) * (dotProduct x (M.mulVec u) + q * dotProduct u (M.mulVec u)) := by
  simp only [attentionScore, repeatedLinePattern_col_zero, repeatedLinePattern_col_succ,
    Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    dotProduct_smul, smul_dotProduct]
  ring

/-- Exact closure of the one-versus-`n` affine-line pattern under one layer. -/
theorem layer_exp_repeatedLinePattern {d n : ℕ} (hn : 0 < n)
    (M : ScoreMatrix d) (x u : Fin d → ℝ) (p q : ℝ) :
    layer Real.exp M (repeatedLinePattern (n := n) x u p q) =
      repeatedLinePattern x u
        (weightedStepFirst n (dotProduct x (M.mulVec u))
          (dotProduct u (M.mulVec u)) p q)
        (weightedStepRepeated n (dotProduct x (M.mulVec u))
          (dotProduct u (M.mulVec u)) p q) := by
  apply Matrix.ext
  intro r i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change normalizedAttention Real.exp M 1
      (firstAndRepeatedTokenMatrix (x + p • u) (x + q • u)) r 0 =
      x r + weightedStepFirst n (dotProduct x (M.mulVec u))
      (dotProduct u (M.mulVec u)) p q * u r
    rw [normalizedAttention_firstAndRepeated_first]
    have hdiff := repeatedLine_scoreDifference_first hn M x u p q
    have he : Real.exp (attentionScore M (repeatedLinePattern (n := n) x u p q) 0 0) =
        Real.exp (attentionScore M (repeatedLinePattern (n := n) x u p q) 0
          (Fin.succ ⟨0, hn⟩)) *
          Real.exp ((p-q) * (dotProduct x (M.mulVec u) + p * dotProduct u (M.mulVec u))) := by
      rw [← Real.exp_add, ← hdiff]
      ring_nf
    simp only [attentionScore, repeatedLinePattern_col_zero,
      repeatedLinePattern_col_succ] at he
    simp only [Matrix.one_mulVec, repeatedLinePattern_col_zero,
      repeatedLinePattern_col_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [he]
    have hE : Real.exp (attentionScore M (repeatedLinePattern (n := n) x u p q)
        0 (Fin.succ ⟨0, hn⟩)) ≠ 0 := Real.exp_ne_zero _
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    unfold weightedStepFirst weightedSigmoid
    field_simp [hE, hn0]
    ring
  · change normalizedAttention Real.exp M 1
      (firstAndRepeatedTokenMatrix (x + p • u) (x + q • u)) r j.succ =
      x r + weightedStepRepeated n (dotProduct x (M.mulVec u))
      (dotProduct u (M.mulVec u)) p q * u r
    rw [normalizedAttention_firstAndRepeated_repeated]
    have hdiff := repeatedLine_scoreDifference_repeated M x u p q j
    have he : Real.exp (attentionScore M (repeatedLinePattern (n := n) x u p q) j.succ 0) =
        Real.exp (attentionScore M (repeatedLinePattern (n := n) x u p q) j.succ j.succ) *
          Real.exp ((p-q) * (dotProduct x (M.mulVec u) + q * dotProduct u (M.mulVec u))) := by
      rw [← Real.exp_add, ← hdiff]
      ring_nf
    simp only [attentionScore, repeatedLinePattern_col_zero,
      repeatedLinePattern_col_succ] at he
    simp only [Matrix.one_mulVec, repeatedLinePattern_col_zero,
      repeatedLinePattern_col_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [he]
    have hE : Real.exp (attentionScore M (repeatedLinePattern (n := n) x u p q)
        j.succ j.succ) ≠ 0 := Real.exp_ne_zero _
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    unfold weightedStepRepeated weightedSigmoid
    field_simp [hE, hn0]
    ring

end NormalizedDeepAttention
