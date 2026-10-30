module

public import DeepLean.Attention.Definitions
public import DeepLean.Attention.Neuroalgebraic.Basic

/-! # Lightning self-attention -/

@[expose] public section

/-- Equations (1)--(3): a single lightning self-attention layer in the attention-matrix
parametrization `(A, V)`. -/
def lightningAttention {d d' t : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ)
    (V : Matrix (Fin d') (Fin d) ℝ) :
    Matrix (Fin d) (Fin t) ℝ → Matrix (Fin d') (Fin t) ℝ :=
  fun X ↦ V * X * X.transpose * A * X

/-- Section 3.1: reciprocal rescaling of the attention and value matrices leaves a single
lightning self-attention layer unchanged. -/
theorem lightningAttention_smul_inv_smul {d d' t : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ)
    (V : Matrix (Fin d') (Fin d) ℝ)
    (c : ℝ) (hc : c ≠ 0) :
    lightningAttention (t := t) (c • A) (c⁻¹ • V) =
      lightningAttention (t := t) A V := by
  funext X
  simp [lightningAttention, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc]

/-- Lemma 3.1: full-rank factorizations `KᵀQ` differ by a unique invertible change of
coordinates in the attention space. -/
theorem query_key_factorization_unique {a d : ℕ}
    (Q K Q' K' : Matrix (Fin a) (Fin d) ℝ)
    (hprod : K.transpose * Q = K'.transpose * Q')
    (hrank : (K.transpose * Q).rank = a) :
    ∃! C : Matrix (Fin a) (Fin a) ℝ,
      IsUnit C ∧ K' = C * K ∧ Q' = C⁻¹.transpose * Q := by
  let bₐ := Pi.basisFun ℝ (Fin a)
  let b_d := Pi.basisFun ℝ (Fin d)
  let k := K.transpose.mulVecLin
  let k' := K'.transpose.mulVecLin
  let q := Q.mulVecLin
  let q' := Q'.mulVecLin
  have hK : K.rank = a := by
    apply le_antisymm K.rank_le_height
    calc
      a = (K.transpose * Q).rank := hrank.symm
      _ ≤ K.transpose.rank := Matrix.rank_mul_le_left _ _
      _ = K.rank := Matrix.rank_transpose K
  have hK' : K'.rank = a := by
    apply le_antisymm K'.rank_le_height
    calc
      a = (K'.transpose * Q').rank := by rw [← hprod, hrank]
      _ ≤ K'.transpose.rank := Matrix.rank_mul_le_left _ _
      _ = K'.rank := Matrix.rank_transpose K'
  have hQ : Q.rank = a := by
    apply le_antisymm Q.rank_le_height
    calc
      a = (K.transpose * Q).rank := hrank.symm
      _ ≤ Q.rank := Matrix.rank_mul_le_right _ _
  have hQ' : Q'.rank = a := by
    apply le_antisymm Q'.rank_le_height
    calc
      a = (K'.transpose * Q').rank := by rw [← hprod, hrank]
      _ ≤ Q'.rank := Matrix.rank_mul_le_right _ _
  have hk_inj : Function.Injective k := by
    rw [← LinearMap.ker_eq_bot]
    apply Submodule.finrank_eq_zero.mp
    have hnull := k.finrank_range_add_finrank_ker
    have hrange : Module.finrank ℝ k.range = a := by
      change K.transpose.rank = a
      rw [Matrix.rank_transpose, hK]
    rw [hrange, Module.finrank_fin_fun] at hnull
    omega
  have hk'_inj : Function.Injective k' := by
    rw [← LinearMap.ker_eq_bot]
    apply Submodule.finrank_eq_zero.mp
    have hnull := k'.finrank_range_add_finrank_ker
    have hrange : Module.finrank ℝ k'.range = a := by
      change K'.transpose.rank = a
      rw [Matrix.rank_transpose, hK']
    rw [hrange, Module.finrank_fin_fun] at hnull
    omega
  have hq_range : q.range = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    change Q.rank = Module.finrank ℝ (Fin a → ℝ)
    rw [hQ, Module.finrank_fin_fun]
  have hq'_range : q'.range = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    change Q'.rank = Module.finrank ℝ (Fin a → ℝ)
    rw [hQ', Module.finrank_fin_fun]
  have hkk' : k.range = k'.range := by
    rw [← LinearMap.range_comp_of_range_eq_top k hq_range,
      ← LinearMap.range_comp_of_range_eq_top k' hq'_range,
      ← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, hprod]
  let eK := LinearEquiv.ofInjective k hk_inj
  let eK' := LinearEquiv.ofInjective k' hk'_inj
  let D : (Fin a → ℝ) ≃ₗ[ℝ] (Fin a → ℝ) :=
    eK' |>.trans (LinearEquiv.ofEq k'.range k.range hkk'.symm) |>.trans eK.symm
  let Dm : Matrix (Fin a) (Fin a) ℝ := LinearMap.toMatrix bₐ bₐ D.toLinearMap
  have hkD : k ∘ₗ D.toLinearMap = k' := by
    apply LinearMap.ext
    intro x
    change k (D x) = k' x
    have he : eK (D x) = (LinearEquiv.ofEq k'.range k.range hkk'.symm) (eK' x) := by
      simp [D]
    exact congr_arg Subtype.val he
  have hqD : D.toLinearMap ∘ₗ q' = q := by
    apply LinearMap.ext
    intro x
    apply hk_inj
    have hp : k (q x) = k' (q' x) := by
      dsimp [k, k', q, q']
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hprod]
    have hDx := LinearMap.congr_fun hkD (q' x)
    change k (D.toLinearMap (q' x)) = k (q x)
    rw [show k (D.toLinearMap (q' x)) = k' (q' x) by
      simpa only [LinearMap.comp_apply] using hDx]
    exact hp.symm
  have hDm_unit : IsUnit Dm := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    apply D.injective
    have hDm : Dm.mulVecLin = D.toLinearMap := by
      rw [← Matrix.toLin'_apply', ← Matrix.toLin_eq_toLin', Matrix.toLin_toMatrix]
    change D.toLinearMap x = D.toLinearMap y
    rw [← hDm]
    exact hxy
  have hKt : K'.transpose = K.transpose * Dm := by
    apply (Matrix.toLin bₐ b_d).injective
    rw [Matrix.toLin_mul bₐ bₐ b_d, Matrix.toLin_toMatrix]
    dsimp [bₐ, b_d]
    simpa only [Matrix.toLin_eq_toLin', Matrix.toLin'_apply'] using hkD.symm
  have hDQ : Dm * Q' = Q := by
    apply (Matrix.toLin b_d bₐ).injective
    rw [Matrix.toLin_mul b_d bₐ bₐ, Matrix.toLin_toMatrix]
    dsimp [bₐ, b_d]
    simpa only [Matrix.toLin_eq_toLin', Matrix.toLin'_apply'] using hqD
  let C := Dm.transpose
  have hC_unit : IsUnit C := (Matrix.isUnit_transpose Dm).mpr hDm_unit
  have hCK : K' = C * K := by
    apply Matrix.transpose_injective
    simpa [C, Matrix.transpose_mul] using hKt
  have hCQ : Q' = C⁻¹.transpose * Q := by
    have hdet : IsUnit Dm.det := (Matrix.isUnit_iff_isUnit_det Dm).mp hDm_unit
    calc
      Q' = Dm⁻¹ * (Dm * Q') := (Matrix.nonsing_inv_mul_cancel_left Dm Q' hdet).symm
      _ = Dm⁻¹ * Q := by rw [hDQ]
      _ = C⁻¹.transpose * Q := by simp [C, Matrix.transpose_nonsing_inv]
  refine ⟨C, ⟨hC_unit, hCK, hCQ⟩, ?_⟩
  intro E hE
  apply Matrix.transpose_injective
  have hleft : K.transpose * E.transpose = K.transpose * C.transpose := by
    calc
      K.transpose * E.transpose = (E * K).transpose := (Matrix.transpose_mul E K).symm
      _ = K'.transpose := congr_arg Matrix.transpose hE.2.1.symm
      _ = (C * K).transpose := congr_arg Matrix.transpose hCK
      _ = K.transpose * C.transpose := Matrix.transpose_mul C K
  apply (Matrix.toLin bₐ bₐ).injective
  apply LinearMap.ext
  intro x
  apply hk_inj
  have hx := LinearMap.congr_fun
    (congr_arg (Matrix.toLin bₐ b_d) hleft) x
  dsimp [bₐ, b_d] at hx ⊢
  simpa only [k, Matrix.toLin_mul, Matrix.toLin_eq_toLin', Matrix.toLin'_apply',
    Matrix.mulVecLin_mul, LinearMap.comp_apply] using hx

/-!
### Theorem 3.2 infrastructure audit

Appendix A.2 identifies coefficients in an equality of vector-valued homogeneous cubic polynomial
maps, factors the resulting products of linear and quadratic forms, and uses irreducibility of the
quadratic form associated to a matrix in the required rank cases. Mathlib has multivariate
polynomials, unique factorization results, polynomial laws, and some specialized irreducible
quadratics, but it does not currently connect `lightningAttention` as a matrix-valued function to
coefficientwise multivariate-polynomial identities. It also lacks the needed theorem classifying
factorizations of the general quadratic forms occurring here by matrix rank (the relevant
`MvPolynomial.IrreducibleQuadratic` file explicitly lists general rank-based quadratic
irreducibility as a TODO).

Consequently Theorem 3.2 is not stated with an unproved bridge or replaced by a weaker extensional
surrogate here. A faithful proof first requires that polynomial representation/coefficient bridge
and the appropriate quadratic-factor classification.
-/

/-- Definition 2: parameters for an `l`-layer lightning-attention network with arbitrary
dimension vector `dim = (d₀, ..., dₗ)`. Layer `i` uses the paper's weights `A_{i+1}, V_{i+1}`. -/
structure DeepAttentionWeights (l : ℕ) (dim : Fin (l + 1) → ℕ) where
  A : (i : Fin l) → Matrix (Fin (dim i.castSucc)) (Fin (dim i.castSucc)) ℝ
  V : (i : Fin l) → Matrix (Fin (dim i.succ)) (Fin (dim i.castSucc)) ℝ

/-- Auxiliary recursion for `deepLightningPrefix`. -/
def deepLightningPrefixAux {l t : ℕ} {dim : Fin (l + 1) → ℕ}
    (W : DeepAttentionWeights l dim)
    (X : Matrix (Fin (dim 0)) (Fin t) ℝ)
    (n : ℕ) (hn : n ≤ l) : Matrix (Fin (dim ⟨n, Nat.lt_succ_of_le hn⟩)) (Fin t) ℝ :=
  match n with
  | 0 => X
  | n + 1 =>
      let i : Fin l := ⟨n, Nat.lt_of_succ_le hn⟩
      lightningAttention (W.A i) (W.V i)
        (deepLightningPrefixAux W X n (Nat.le_of_succ_le hn))

/-- Definition 2: output after the first `i` layers, defined by repeated composition of
`lightningAttention`. -/
def deepLightningPrefix {l t : ℕ} {dim : Fin (l + 1) → ℕ}
    (W : DeepAttentionWeights l dim)
    (X : Matrix (Fin (dim 0)) (Fin t) ℝ)
    (i : Fin (l + 1)) : Matrix (Fin (dim i)) (Fin t) ℝ :=
  deepLightningPrefixAux W X i.val (Nat.le_of_lt_succ i.isLt)

/-- Definition 2: the function represented by the full deep network. -/
def deepLightningAttention {l t : ℕ} {dim : Fin (l + 1) → ℕ}
    (W : DeepAttentionWeights l dim) :
    Matrix (Fin (dim 0)) (Fin t) ℝ → Matrix (Fin (dim (Fin.last l))) (Fin t) ℝ :=
  fun X ↦ deepLightningPrefix W X (Fin.last l)

@[simp] theorem deepLightningPrefix_zero {l t : ℕ} {dim : Fin (l + 1) → ℕ}
    (W : DeepAttentionWeights l dim) (X : Matrix (Fin (dim 0)) (Fin t) ℝ) :
    deepLightningPrefix W X 0 = X := by
  rfl

@[simp] theorem deepLightningPrefix_succ {l t : ℕ} {dim : Fin (l + 1) → ℕ}
    (W : DeepAttentionWeights l dim) (X : Matrix (Fin (dim 0)) (Fin t) ℝ) (i : Fin l) :
    deepLightningPrefix W X i.succ =
      lightningAttention (W.A i) (W.V i) (deepLightningPrefix W X i.castSucc) := by
  rfl

/-- Auxiliary recursion for `valuePrefix`. -/
def valuePrefixAux {l : ℕ} {dim : Fin (l + 1) → ℕ}
    (W : DeepAttentionWeights l dim) (n : ℕ) (hn : n ≤ l) :
    Matrix (Fin (dim ⟨n, Nat.lt_succ_of_le hn⟩)) (Fin (dim 0)) ℝ :=
  match n with
  | 0 => by
      have hzero : (⟨0, Nat.lt_succ_of_le hn⟩ : Fin (l + 1)) = 0 := Fin.ext rfl
      exact hzero.symm ▸ (1 : Matrix (Fin (dim 0)) (Fin (dim 0)) ℝ)
  | n + 1 =>
      let i : Fin l := ⟨n, Nat.lt_of_succ_le hn⟩
      have hprev :
          (⟨n, Nat.lt_succ_of_le (Nat.le_of_succ_le hn)⟩ : Fin (l + 1)) = i.castSucc :=
        Fin.ext rfl
      have hnext : (⟨n + 1, Nat.lt_succ_of_le hn⟩ : Fin (l + 1)) = i.succ := Fin.ext rfl
      hnext.symm ▸ (W.V i * (hprev ▸ valuePrefixAux W n (Nat.le_of_succ_le hn)))

/-- Equation (8): `L_i = V_i ⋯ V_1`, including `L_0 = I`. -/
def valuePrefix {l : ℕ} {dim : Fin (l + 1) → ℕ}
    (W : DeepAttentionWeights l dim) (i : Fin (l + 1)) :
    Matrix (Fin (dim i)) (Fin (dim 0)) ℝ :=
  valuePrefixAux W i.val (Nat.le_of_lt_succ i.isLt)

/-- Equation (8): the final value product `L = L_l`. -/
def virtualL {l : ℕ} {dim : Fin (l + 1) → ℕ} (W : DeepAttentionWeights l dim) :
    Matrix (Fin (dim (Fin.last l))) (Fin (dim 0)) ℝ :=
  valuePrefix W (Fin.last l)

/-- Equation (8): `M_i = L_{i-1}ᵀ A_i L_{i-1}`. With zero-based Lean layer indices,
`virtualM W i` is the paper's `M_{i+1}`. -/
def virtualM {l : ℕ} {dim : Fin (l + 1) → ℕ}
    (W : DeepAttentionWeights l dim) (i : Fin l) :
    Matrix (Fin (dim 0)) (Fin (dim 0)) ℝ :=
  (valuePrefix W i.castSucc).transpose * W.A i * valuePrefix W i.castSucc

@[simp] theorem valuePrefix_zero {l : ℕ} {dim : Fin (l + 1) → ℕ}
    (W : DeepAttentionWeights l dim) : valuePrefix W 0 = 1 := by
  simp [valuePrefix, valuePrefixAux]

@[simp] theorem valuePrefix_succ {l : ℕ} {dim : Fin (l + 1) → ℕ}
    (W : DeepAttentionWeights l dim) (i : Fin l) :
    valuePrefix W i.succ = W.V i * valuePrefix W i.castSucc := by
  simp [valuePrefix, valuePrefixAux]
  congr

/-- Equation (10): the recursively defined token-space matrices `D_i`. The equation in the
paper is one continuous matrix product (there is no subtraction). -/
def virtualD {l d t : ℕ} (M : Fin l → Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin t) ℝ) : Fin (l + 1) → Matrix (Fin t) (Fin t) ℝ :=
  fun i ↦ Fin.induction 1
    (fun j D ↦ D * X.transpose * M j * X * D * X.transpose * (M j).transpose * X * D) i

/-- The descending product `Z_i` from Equation (25); Equation (11) uses `Z_l`. -/
def virtualZ {l d t : ℕ} (M : Fin l → Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin t) ℝ) : Fin (l + 1) → Matrix (Fin t) (Fin t) ℝ :=
  fun i ↦ Fin.induction 1
    (fun j Z ↦ virtualD M X j.castSucc * X.transpose * M j * X * Z) i

@[simp] theorem virtualD_zero {l d t : ℕ} (M : Fin l → Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin t) ℝ) : virtualD M X 0 = 1 := by
  simp [virtualD]

@[simp] theorem virtualD_succ {l d t : ℕ} (M : Fin l → Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin t) ℝ) (i : Fin l) :
    virtualD M X i.succ =
      virtualD M X i.castSucc * X.transpose * M i * X * virtualD M X i.castSucc *
        X.transpose * (M i).transpose * X * virtualD M X i.castSucc := by
  simp [virtualD]

@[simp] theorem virtualZ_zero {l d t : ℕ} (M : Fin l → Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin t) ℝ) : virtualZ M X 0 = 1 := by
  simp [virtualZ]

@[simp] theorem virtualZ_succ {l d t : ℕ} (M : Fin l → Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin t) ℝ) (i : Fin l) :
    virtualZ M X i.succ = virtualD M X i.castSucc * X.transpose * M i * X *
      virtualZ M X i.castSucc := by
  simp [virtualZ]

/-- Equation (25): the recursive matrix `D_i` is the Gram product `Z_i Z_iᵀ`. -/
theorem virtualD_eq_virtualZ_mul_transpose {l d t : ℕ}
    (M : Fin l → Matrix (Fin d) (Fin d) ℝ)
    (X : Matrix (Fin d) (Fin t) ℝ) (i : Fin (l + 1)) :
    virtualD M X i = virtualZ M X i * (virtualZ M X i).transpose := by
  refine Fin.induction ?_ ?_ i
  · simp
  · intro j ih
    have hsym : (virtualD M X j.castSucc).transpose = virtualD M X j.castSucc := by
      rw [ih, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [virtualD_succ, virtualZ_succ]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [hsym, ih]
    simp only [Matrix.mul_assoc]

/-- Lemma 3.6, Equation (22): the output after every prefix of the network is expressed using
only its virtual weights. The case `i = Fin.last l` is Equation (11). -/
theorem deepLightningPrefix_eq_virtual {l t : ℕ} {dim : Fin (l + 1) → ℕ}
    (W : DeepAttentionWeights l dim)
    (X : Matrix (Fin (dim 0)) (Fin t) ℝ) (i : Fin (l + 1)) :
    deepLightningPrefix W X i =
      valuePrefix W i * X * virtualZ (virtualM W) X i := by
  refine Fin.induction ?_ ?_ i
  · simp
  · intro j ih
    rw [deepLightningPrefix_succ, valuePrefix_succ, virtualZ_succ]
    unfold lightningAttention
    rw [ih]
    rw [virtualD_eq_virtualZ_mul_transpose]
    simp only [Matrix.transpose_mul, virtualM]
    simp only [Matrix.mul_assoc]

/-- Lemma 3.6, Equation (11): the full deep lightning network in the `(M, L)`
parametrization. -/
theorem deepLightningAttention_eq_virtual {l t : ℕ} {dim : Fin (l + 1) → ℕ}
    (W : DeepAttentionWeights l dim)
    (X : Matrix (Fin (dim 0)) (Fin t) ℝ) :
    deepLightningAttention W X =
      virtualL W * X * virtualZ (virtualM W) X (Fin.last l) :=
  deepLightningPrefix_eq_virtual W X (Fin.last l)

/-!
### Lemma 3.5 and Theorem 3.7 infrastructure

Lemma 3.5 requires an arbitrary-length uniqueness theorem for factorizations of a full-rank
rectangular matrix product, together with dependent transport across the bottleneck equalities
`d_i = δ`. Mathlib has no packaged iterated matrix-factorization result; `query_key_factorization_unique`
only supplies the two-factor case. An exact indexed proof can be built by a separate induction, but
is not introduced here as an ad hoc fixed-depth or constant-width surrogate.

Theorem 3.7 additionally cannot currently be proved by reusing Mathlib's polynomial API. Appendix
A.6 extracts terms of prescribed multidegree from the unrolled Equation (12), applies unique
factorization and rank-based irreducibility of general quadratic forms, and finally invokes
Kronecker's bordered-matrix theorem for `2 × 2` minors. The first two bridges are already identified
as missing above, and Mathlib has no bordered-matrix theorem in this form. Thus no weaker
finite-input fiber statement is substituted for Theorem 3.7.
-/

/-- An input sequence whose every token equals `x`. -/
def constantTokenMatrix {d t : ℕ} (x : Fin d → ℝ) : Matrix (Fin d) (Fin t) ℝ :=
  fun r _ ↦ x r

theorem normalizedAttention_constantTokenMatrix {d d' t : ℕ} (S : ℝ → ℝ)
    (hSpos : ∀ z, 0 < S z) (A : Matrix (Fin d) (Fin d) ℝ)
    (V : Matrix (Fin d') (Fin d) ℝ) (x : Fin d → ℝ) (ht : 0 < t) :
    normalizedAttention (t := t) S A V (constantTokenMatrix (t := t) x) =
      fun r (_ : Fin t) ↦ (V.mulVec x) r := by
  ext r i
  have hcard : (Fintype.card (Fin t) : ℝ) ≠ 0 := by
    simp [ht.ne']
  have hscore : 0 < S (dotProduct x (A.mulVec x)) := hSpos _
  simp only [normalizedAttention, attentionScore]
  have hcol (j : Fin t) : (constantTokenMatrix (t := t) x).col j = x := rfl
  simp_rw [hcol]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Theorem 3.9, zero fiber: for `t ≥ 2` (in fact, for any nonempty sequence), normalized
attention represents the zero function only when `V = 0`. -/
theorem normalizedAttention_eq_zero_imp_value_eq_zero {d d' t : ℕ} (S : ℝ → ℝ)
    (hSpos : ∀ z, 0 < S z) (A : Matrix (Fin d) (Fin d) ℝ)
    (V : Matrix (Fin d') (Fin d) ℝ) (ht : 2 ≤ t)
    (hφ : normalizedAttention (t := t) S A V = 0) : V = 0 := by
  ext r c
  let x : Fin d → ℝ := Pi.single c 1
  have hout := congr_arg (fun f ↦ f (constantTokenMatrix (t := t) x)) hφ
  rw [normalizedAttention_constantTokenMatrix S hSpos A V x (by omega)] at hout
  have hentry := congr_fun (congr_fun hout r) (⟨0, by omega⟩ : Fin t)
  simpa [x, Matrix.mulVec, Pi.single_apply] using hentry

/-- First step of Theorem 3.9: constant-token inputs identify the value matrix. -/
theorem normalizedAttention_value_identifiable {d d' t : ℕ} (S : ℝ → ℝ)
    (hSpos : ∀ z, 0 < S z) (A A' : Matrix (Fin d) (Fin d) ℝ)
    (V V' : Matrix (Fin d') (Fin d) ℝ) (ht : 2 ≤ t)
    (hφ : normalizedAttention (t := t) S A V = normalizedAttention S A' V') :
    V = V' := by
  ext r c
  let x : Fin d → ℝ := Pi.single c 1
  have hout := congr_arg (fun f ↦ f (constantTokenMatrix (t := t) x)) hφ
  rw [normalizedAttention_constantTokenMatrix S hSpos A V x (by omega),
    normalizedAttention_constantTokenMatrix S hSpos A' V' x (by omega)] at hout
  have hentry := congr_fun (congr_fun hout r) (⟨0, by omega⟩ : Fin t)
  simpa [x, Matrix.mulVec, Pi.single_apply] using hentry

/-- The test sequence used in Equations (33)--(35): its first token is `x` and all remaining
tokens are `y`. -/
def firstAndRepeatedTokenMatrix {d n : ℕ} (x y : Fin d → ℝ) :
    Matrix (Fin d) (Fin (n + 1)) ℝ :=
  fun r i ↦ Fin.cases (x r) (fun _ ↦ y r) i

theorem normalizedAttention_firstAndRepeated_first {d d' n : ℕ} (S : ℝ → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) (V : Matrix (Fin d') (Fin d) ℝ)
    (x y : Fin d → ℝ) (r : Fin d') :
    normalizedAttention S A V (firstAndRepeatedTokenMatrix (n := n) x y) r 0 =
      (S (dotProduct x (A.mulVec x)) * (V.mulVec x) r +
        n * S (dotProduct x (A.mulVec y)) * (V.mulVec y) r) /
      (S (dotProduct x (A.mulVec x)) + n * S (dotProduct x (A.mulVec y))) := by
  simp only [normalizedAttention, attentionScore]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  change
    (S (dotProduct x (A.mulVec x)) * (V.mulVec x) r +
      ∑ _ : Fin n, S (dotProduct x (A.mulVec y)) * (V.mulVec y) r) /
        (S (dotProduct x (A.mulVec x)) +
          ∑ _ : Fin n, S (dotProduct x (A.mulVec y))) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private theorem ratio_self_add_nat_injective {n : ℕ} (hn : 0 < n) {s s' : ℝ}
    (hs : 0 < s) (hs' : 0 < s')
    (h : s / (s + n) = s' / (s' + n)) : s = s' := by
  have hd : s + n ≠ 0 := by positivity
  have hd' : s' + n ≠ 0 := by positivity
  field_simp [hd, hd'] at h
  have hn' : (n : ℝ) ≠ 0 := by positivity
  apply (mul_left_cancel₀ hn')
  nlinarith

private theorem weighted_average_weight_injective {n : ℕ} (hn : 0 < n)
    {q s s' u v : ℝ} (hq : 0 < q) (hs : 0 < s) (hs' : 0 < s') (huv : u ≠ v)
    (h : (q * u + n * s * v) / (q + n * s) =
      (q * u + n * s' * v) / (q + n * s')) : s = s' := by
  have hd : q + n * s ≠ 0 := by positivity
  have hd' : q + n * s' ≠ 0 := by positivity
  field_simp [hd, hd'] at h
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hq' : q ≠ 0 := ne_of_gt hq
  have huv' : u - v ≠ 0 := sub_ne_zero.mpr huv
  have hz : (n : ℝ) * q * (u - v) * (s - s') = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hz with hzero | hss
  · rcases mul_eq_zero.mp hzero with hzero | huvzero
    · exact (mul_ne_zero hn' hq') hzero |>.elim
    · exact (huv' huvzero).elim
  · exact sub_eq_zero.mp hss

private theorem quadratic_score_eq_of_value_ne_zero {d d' n : ℕ} (S : ℝ → ℝ)
    (hSinj : Function.Injective S) (hSzero : S 0 = 1) (hSpos : ∀ z, 0 < S z)
    (A A' : Matrix (Fin d) (Fin d) ℝ) (V : Matrix (Fin d') (Fin d) ℝ)
    (hn : 0 < n) (hφ : normalizedAttention (t := n + 1) S A V = normalizedAttention S A' V)
    (x : Fin d → ℝ) (hx : V.mulVec x ≠ 0) :
    dotProduct x (A.mulVec x) = dotProduct x (A'.mulVec x) := by
  obtain ⟨r, hr⟩ : ∃ r, (V.mulVec x) r ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hout := congr_arg (fun f ↦ f (firstAndRepeatedTokenMatrix (n := n) x 0)) hφ
  have hentry := congr_fun (congr_fun hout r) (0 : Fin (n + 1))
  rw [normalizedAttention_firstAndRepeated_first,
    normalizedAttention_firstAndRepeated_first] at hentry
  simp [hSzero] at hentry
  have hratio :
      S (dotProduct x (A.mulVec x)) / (S (dotProduct x (A.mulVec x)) + n) =
        S (dotProduct x (A'.mulVec x)) / (S (dotProduct x (A'.mulVec x)) + n) := by
    apply mul_right_cancel₀ hr
    simpa [div_mul_eq_mul_div] using hentry
  apply hSinj
  exact ratio_self_add_nat_injective hn (hSpos _) (hSpos _) hratio

private theorem quadratic_parallelogram {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (x y : Fin d → ℝ) :
    dotProduct (x + y) (A.mulVec (x + y)) + dotProduct (x - y) (A.mulVec (x - y)) =
      2 * dotProduct x (A.mulVec x) + 2 * dotProduct y (A.mulVec y) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub]
  ring

private theorem exists_mulVec_ne_zero {d d' : ℕ}
    (V : Matrix (Fin d') (Fin d) ℝ) (hV : V ≠ 0) :
    ∃ x : Fin d → ℝ, V.mulVec x ≠ 0 := by
  by_contra h
  push Not at h
  apply hV
  ext r c
  have hc := congr_fun (h (Pi.single c 1)) r
  simpa using hc

private theorem quadratic_scores_eq {d d' n : ℕ} (S : ℝ → ℝ)
    (hSinj : Function.Injective S) (hSzero : S 0 = 1) (hSpos : ∀ z, 0 < S z)
    (A A' : Matrix (Fin d) (Fin d) ℝ) (V : Matrix (Fin d') (Fin d) ℝ)
    (hn : 0 < n) (hV : V ≠ 0)
    (hφ : normalizedAttention (t := n + 1) S A V = normalizedAttention S A' V) :
    ∀ x : Fin d → ℝ, dotProduct x (A.mulVec x) = dotProduct x (A'.mulVec x) := by
  obtain ⟨y, hy⟩ := exists_mulVec_ne_zero V hV
  intro x
  by_cases hx : V.mulVec x = 0
  · have hplus : V.mulVec (x + y) ≠ 0 := by
      rw [Matrix.mulVec_add, hx, zero_add]
      exact hy
    have hminus : V.mulVec (x - y) ≠ 0 := by
      rw [Matrix.mulVec_sub, hx, zero_sub]
      exact neg_ne_zero.mpr hy
    have hyq := quadratic_score_eq_of_value_ne_zero S hSinj hSzero hSpos A A' V hn hφ y hy
    have hp := quadratic_score_eq_of_value_ne_zero S hSinj hSzero hSpos A A' V hn hφ
      (x + y) hplus
    have hm := quadratic_score_eq_of_value_ne_zero S hSinj hSzero hSpos A A' V hn hφ
      (x - y) hminus
    have hpar := quadratic_parallelogram A x y
    have hpar' := quadratic_parallelogram A' x y
    linarith
  · exact quadratic_score_eq_of_value_ne_zero S hSinj hSzero hSpos A A' V hn hφ x hx

private theorem bilinear_score_eq_of_value_ne {d d' n : ℕ} (S : ℝ → ℝ)
    (hSinj : Function.Injective S) (hSpos : ∀ z, 0 < S z)
    (A A' : Matrix (Fin d) (Fin d) ℝ) (V : Matrix (Fin d') (Fin d) ℝ)
    (hn : 0 < n) (hφ : normalizedAttention (t := n + 1) S A V = normalizedAttention S A' V)
    (hq : ∀ z : Fin d → ℝ, dotProduct z (A.mulVec z) = dotProduct z (A'.mulVec z))
    (x y : Fin d → ℝ) (hxy : V.mulVec x ≠ V.mulVec y) :
    dotProduct x (A.mulVec y) = dotProduct x (A'.mulVec y) := by
  obtain ⟨r, hr⟩ : ∃ r, (V.mulVec x) r ≠ (V.mulVec y) r := by
    by_contra h
    push Not at h
    exact hxy (funext h)
  have hout := congr_arg (fun f ↦ f (firstAndRepeatedTokenMatrix (n := n) x y)) hφ
  have hentry := congr_fun (congr_fun hout r) (0 : Fin (n + 1))
  rw [normalizedAttention_firstAndRepeated_first,
    normalizedAttention_firstAndRepeated_first, ← hq x] at hentry
  have hs := weighted_average_weight_injective hn (hSpos _) (hSpos _) (hSpos _) hr hentry
  exact hSinj hs

private theorem bilinear_scores_eq {d d' n : ℕ} (S : ℝ → ℝ)
    (hSinj : Function.Injective S) (hSzero : S 0 = 1) (hSpos : ∀ z, 0 < S z)
    (A A' : Matrix (Fin d) (Fin d) ℝ) (V : Matrix (Fin d') (Fin d) ℝ)
    (hn : 0 < n) (hV : V ≠ 0)
    (hφ : normalizedAttention (t := n + 1) S A V = normalizedAttention S A' V) :
    ∀ x y : Fin d → ℝ, dotProduct x (A.mulVec y) = dotProduct x (A'.mulVec y) := by
  have hq := quadratic_scores_eq S hSinj hSzero hSpos A A' V hn hV hφ
  obtain ⟨z, hz⟩ := exists_mulVec_ne_zero V hV
  intro x y
  by_cases hxy : V.mulVec x = V.mulVec y
  · have hz2 : (2 : ℝ) • V.mulVec z ≠ 0 := smul_ne_zero (by norm_num) hz
    have hvalue₁ : V.mulVec x ≠ V.mulVec (y + z) := by
      rw [Matrix.mulVec_add, ← hxy]
      intro h
      apply hz
      funext r
      have hr := congr_fun h r
      simp only [Pi.add_apply] at hr
      change V.mulVec z r = 0
      linarith
    have hvalue₂ : V.mulVec x ≠ V.mulVec (y + 2 • z) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, ← hxy]
      intro h
      apply hz2
      funext r
      have hr := congr_fun h r
      change 2 * V.mulVec z r = 0
      simp only [Pi.add_apply, Pi.smul_apply] at hr
      rw [two_smul] at hr
      linarith
    have h₁ := bilinear_score_eq_of_value_ne S hSinj hSpos A A' V hn hφ hq
      x (y + z) hvalue₁
    have h₂ := bilinear_score_eq_of_value_ne S hSinj hSpos A A' V hn hφ hq
      x (y + 2 • z) hvalue₂
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul] at h₁ h₂
    rw [two_smul, two_smul] at h₂
    linarith
  · exact bilinear_score_eq_of_value_ne S hSinj hSpos A A' V hn hφ hq x y hxy

private theorem attention_matrix_eq {d d' n : ℕ} (S : ℝ → ℝ)
    (hSinj : Function.Injective S) (hSzero : S 0 = 1) (hSpos : ∀ z, 0 < S z)
    (A A' : Matrix (Fin d) (Fin d) ℝ) (V : Matrix (Fin d') (Fin d) ℝ)
    (hn : 0 < n) (hV : V ≠ 0)
    (hφ : normalizedAttention (t := n + 1) S A V = normalizedAttention S A' V) :
    A = A' := by
  have hbilinear := bilinear_scores_eq S hSinj hSzero hSpos A A' V hn hV hφ
  ext i j
  have hij := hbilinear (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hij

/-- Theorem 3.9, nonzero fibers: for at least two tokens, equality of normalized attention
functions with a nonzero first function identifies both `A` and `V`. -/
theorem normalizedAttention_identifiable {d d' t : ℕ} (S : ℝ → ℝ)
    (hSinj : Function.Injective S) (hSzero : S 0 = 1) (hSpos : ∀ z, 0 < S z)
    (A A' : Matrix (Fin d) (Fin d) ℝ) (V V' : Matrix (Fin d') (Fin d) ℝ)
    (ht : 2 ≤ t) (hφzero : normalizedAttention (t := t) S A V ≠ 0)
    (hφ : normalizedAttention (t := t) S A V = normalizedAttention S A' V') :
    A = A' ∧ V = V' := by
  have hVV := normalizedAttention_value_identifiable S hSpos A A' V V' ht hφ
  subst V'
  have hV : V ≠ 0 := by
    intro h
    subst V
    apply hφzero
    funext X r i
    simp [normalizedAttention]
  constructor
  · cases t with
    | zero => omega
    | succ n =>
      exact attention_matrix_eq S hSinj hSzero hSpos A A' V (by omega) hV hφ
  · rfl

/-- Theorem 3.9 in its two-part form: the zero function forces `V = 0`, while every
nonzero fiber of the normalized single-layer parametrization is a singleton. -/
theorem normalizedAttention_theorem_3_9 {d d' t : ℕ} (S : ℝ → ℝ)
    (hSinj : Function.Injective S) (hSzero : S 0 = 1) (hSpos : ∀ z, 0 < S z)
    (ht : 2 ≤ t) :
    (∀ (A : Matrix (Fin d) (Fin d) ℝ) (V : Matrix (Fin d') (Fin d) ℝ),
      normalizedAttention (t := t) S A V = 0 → V = 0) ∧
    (∀ (A A' : Matrix (Fin d) (Fin d) ℝ) (V V' : Matrix (Fin d') (Fin d) ℝ),
      normalizedAttention (t := t) S A V ≠ 0 →
      normalizedAttention (t := t) S A V = normalizedAttention S A' V' →
      A = A' ∧ V = V') := by
  constructor
  · intro A V hφ
    exact normalizedAttention_eq_zero_imp_value_eq_zero S hSpos A V ht hφ
  · intro A A' V V' hnonzero hφ
    exact normalizedAttention_identifiable S hSinj hSzero hSpos A A' V V' ht hnonzero hφ
