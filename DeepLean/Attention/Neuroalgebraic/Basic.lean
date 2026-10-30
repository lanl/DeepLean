module

public import Mathlib

/-! # Basic matrix-rank results -/

@[expose] public section

/-- The rank of a product of an `N₂ × N₁` matrix and an `N₁ × N₀` matrix
is at most the shared inner dimension `N₁`. -/
theorem rank_mul_le_inner_dimension
    {N₀ N₁ N₂ : ℕ}
    (W₀ : Matrix (Fin N₁) (Fin N₀) ℝ)
    (W₁ : Matrix (Fin N₂) (Fin N₁) ℝ) :
    (W₁ * W₀).rank ≤ N₁ := by
  calc
    (W₁ * W₀).rank ≤ W₀.rank := Matrix.rank_mul_le_right W₁ W₀
    _ ≤ Fintype.card (Fin N₁) := Matrix.rank_le_card_height W₀
    _ = N₁ := Fintype.card_fin N₁

/-- A real matrix of rank at most `N₁` factors through an `N₁`-dimensional space. -/
theorem exists_matrix_factorization_of_rank_le
    {N₀ N₁ N₂ : ℕ}
    (A : Matrix (Fin N₂) (Fin N₀) ℝ)
    (h : A.rank ≤ N₁) :
    ∃ W₀ : Matrix (Fin N₁) (Fin N₀) ℝ,
      ∃ W₁ : Matrix (Fin N₂) (Fin N₁) ℝ, A = W₁ * W₀ := by
  let b₀ := Pi.basisFun ℝ (Fin N₀)
  let b₁ := Pi.basisFun ℝ (Fin N₁)
  let b₂ := Pi.basisFun ℝ (Fin N₂)
  let f := Matrix.toLin b₀ b₂ A
  have hfin : Module.finrank ℝ f.range ≤ Module.finrank ℝ (Fin N₁ → ℝ) := by
    rw [Module.finrank_fin_fun]
    rwa [← A.rank_eq_finrank_range_toLin b₂ b₀]
  obtain ⟨g, hg⟩ := finrank_le_iff_exists_linearMap.mp hfin
  obtain ⟨l, hl⟩ := g.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hg)
  let f₀ : (Fin N₀ → ℝ) →ₗ[ℝ] (Fin N₁ → ℝ) := g ∘ₗ f.rangeRestrict
  let f₁ : (Fin N₁ → ℝ) →ₗ[ℝ] (Fin N₂ → ℝ) := f.range.subtype ∘ₗ l
  refine ⟨LinearMap.toMatrix b₀ b₁ f₀, LinearMap.toMatrix b₁ b₂ f₁, ?_⟩
  rw [← LinearMap.toMatrix_comp]
  apply (Matrix.toLin b₀ b₂).injective
  rw [Matrix.toLin_toMatrix]
  change f = f₁ ∘ₗ f₀
  apply LinearMap.ext
  intro x
  change f x = ((f.range.subtype ∘ₗ l) ∘ₗ (g ∘ₗ f.rangeRestrict)) x
  simp only [LinearMap.comp_apply]
  rw [show l (g (f.rangeRestrict x)) = f.rangeRestrict x by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun hl (f.rangeRestrict x)]
  rfl

/-- A real matrix factors through `ℝ ^ N₁` exactly when its rank is at most `N₁`. -/
theorem exists_matrix_factorization_iff_rank_le
    {N₀ N₁ N₂ : ℕ}
    (A : Matrix (Fin N₂) (Fin N₀) ℝ) :
    (∃ W₀ : Matrix (Fin N₁) (Fin N₀) ℝ,
      ∃ W₁ : Matrix (Fin N₂) (Fin N₁) ℝ, A = W₁ * W₀) ↔
      A.rank ≤ N₁ := by
  constructor
  · rintro ⟨W₀, W₁, rfl⟩
    exact rank_mul_le_inner_dimension W₀ W₁
  · exact exists_matrix_factorization_of_rank_le A

/-- Appendix A: an invertible change of basis in the hidden layer leaves the network map
unchanged. -/
theorem hidden_layer_change_of_basis_invariant
    {N₀ N₁ N₂ : ℕ}
    (W₀ : Matrix (Fin N₁) (Fin N₀) ℝ)
    (W₁ : Matrix (Fin N₂) (Fin N₁) ℝ)
    (T : Matrix (Fin N₁) (Fin N₁) ℝ) [Invertible T] :
    (W₁ * T⁻¹) * (T * W₀) = W₁ * W₀ := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc T⁻¹, Matrix.inv_mul_of_invertible,
    Matrix.one_mul]

/-- Appendix A: the image of a two-layer linear network is exactly the determinantal
rank-`≤ N₁` locus. -/
theorem two_layer_linear_network_image_eq_rank_le_locus
    {N₀ N₁ N₂ : ℕ} :
    Set.range (fun p : Matrix (Fin N₁) (Fin N₀) ℝ × Matrix (Fin N₂) (Fin N₁) ℝ ↦
      p.2 * p.1) =
      {A : Matrix (Fin N₂) (Fin N₀) ℝ | A.rank ≤ N₁} := by
  ext A
  rw [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨W₀, W₁⟩, rfl⟩
    exact rank_mul_le_inner_dimension W₀ W₁
  · intro h
    obtain ⟨W₀, W₁, hA⟩ := exists_matrix_factorization_of_rank_le A h
    exact ⟨(W₀, W₁), hA.symm⟩

/-!
### Appendix A claims not yet supported by Mathlib

**Determinantal characterization.**  The intended next statement is
`A.rank ≤ N₁ ↔ ∀ r c, (A.submatrix r c : Matrix (Fin (N₁ + 1))
(Fin (N₁ + 1)) ℝ).det = 0`.  Mathlib currently provides
`Matrix.rank_submatrix_le` and `Matrix.rank_of_det_ne_zero`, which prove the forward implication,
but it does not provide the converse bridge asserting that a matrix of rank at least `k` has a
nonzero `k × k` minor (or a sufficiently general Cauchy--Binet theorem from which to derive it).
Proving that bridge here would reimplement the missing part of determinant/rank theory, so the
claimed equivalence is deliberately not replaced by a weaker surrogate.

**Singular locus.**  Mathlib has general scheme-theoretic smooth-locus definitions, but no
construction and defining ideal for the generic determinantal variety, and no theorem computing
its singular locus.  Thus the claim that the singular locus of the rank-`≤ N₁` variety is the
rank-`< N₁` locus cannot yet be stated cleanly using existing determinantal-variety infrastructure.

**Eckart--Young.**  Mathlib defines `LinearMap.singularValues` and a Frobenius norm on finite
matrices, but currently has neither a singular-value decomposition/truncation construction nor an
Eckart--Young--Mirsky best-approximation theorem.  Consequently the rank-`N₁` optimal Frobenius-norm
approximation claim is not formalized here rather than being weakened.
-/
