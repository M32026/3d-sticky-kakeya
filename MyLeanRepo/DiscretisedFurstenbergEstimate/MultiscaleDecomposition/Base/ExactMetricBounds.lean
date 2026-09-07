module

/-
  Exact metric covering bounds from dyadic square counts.

  Theorem 2: dyadicSquareCount ≤ 9 * externalCoveringNumber
  Theorem 3: extCover(Δ^b, P∩Q_a) ≥ (∏ N(i)) / 9

  Whiteprint node: exact_dictionary_bounds
  Dependencies: ExactDyadicCount, CoveringBasics
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.ExactDyadicCount
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.CoveringBasics

@[expose] public section

noncomputable section

namespace DirecretisedFurstenbergEstimate.MultiscaleDecomposition

open scoped ENNReal NNReal

/-! # Theorem 2: Dyadic square count vs metric covering number -/

/-- If C is a finite δ-cover of A, then the number of dyadic δ-squares
    intersecting A is at most 9 * |C|. -/
lemma dyadicSquareCount_le_9_mul_cover {δ : ℝ} (hδ : 0 < δ)
    {A : Set EuclideanPlane} {C : Finset EuclideanPlane}
    (hC : Metric.IsCover δ.toNNReal A C) :
    dyadicSquareCount δ A ≤ ↑(9 * C.card) := by
  let S_c : EuclideanPlane → Finset (ℤ × ℤ) := fun c =>
    Classical.choose (ball_dyadic_squares_bound δ hδ c)
  have hS1 : ∀ (c : EuclideanPlane), ∀ (i j : ℤ),
      (Metric.closedBall c δ ∩ dyadicSquare δ i j).Nonempty → (i, j) ∈ S_c c := by
    intro c
    exact (Classical.choose_spec (ball_dyadic_squares_bound δ hδ c)).1
  have hS2 : ∀ (c : EuclideanPlane), (S_c c).card ≤ 9 := by
    intro c
    exact (Classical.choose_spec (ball_dyadic_squares_bound δ hδ c)).2
  let T : Finset (ℤ × ℤ) := C.biUnion S_c
  have h_cover : ∀ (p : ℤ × ℤ), (A ∩ dyadicSquare δ p.1 p.2).Nonempty → p ∈ T := by
    intro p hp
    rcases hp with ⟨x, hxA, hxsq⟩
    have h2 : x ∈ ⋃ c ∈ C, Metric.closedBall c δ.toNNReal :=
      hC.subset_iUnion_closedBall hxA
    rcases Set.mem_iUnion₂.mp h2 with ⟨c, hcC, hcBall⟩
    have hdist : dist x c ≤ δ := by
      have h : dist x c ≤ (δ.toNNReal : ℝ) := hcBall
      have h2 : (δ.toNNReal : ℝ) = δ := by
        have h3 : 0 ≤ δ := by linarith
        exact Real.coe_toNNReal δ h3
      rw [h2] at h
      exact h
    have h_int : (Metric.closedBall c δ ∩ dyadicSquare δ p.1 p.2).Nonempty :=
      ⟨x, by simpa [Metric.mem_closedBall] using hdist, hxsq⟩
    have hps : p ∈ S_c c := hS1 c p.1 p.2 h_int
    exact Finset.mem_biUnion.mpr ⟨c, hcC, hps⟩
  let SqSet : Set (ℤ × ℤ) := {p | (A ∩ dyadicSquare δ p.1 p.2).Nonempty}
  have h_sub : SqSet ⊆ (T : Set (ℤ × ℤ)) := by
    intro p hp
    exact h_cover p hp
  have h_fin : SqSet.Finite := Set.Finite.subset (Finset.finite_toSet T) h_sub
  have h_encard : SqSet.encard ≤ ↑(T.card) := by
    have h : SqSet.encard ≤ (T : Set (ℤ × ℤ)).encard := Set.encard_le_encard h_sub
    have h2 : (T : Set (ℤ × ℤ)).encard = ↑(T.card) := by simp
    rw [h2] at h
    exact h
  have h_T_card : T.card ≤ 9 * C.card := by
    calc T.card
      ≤ ∑ c ∈ C, (S_c c).card := by exact Finset.card_biUnion_le
    _ ≤ ∑ c ∈ C, 9 := Finset.sum_le_sum (fun c _ => hS2 c)
    _ = 9 * C.card := by simp [Finset.sum_const] <;> ring
  have h_main : SqSet.encard ≤ ↑(9 * C.card) := by
    calc SqSet.encard ≤ ↑(T.card) := h_encard
      _ ≤ ↑(9 * C.card) := by exact_mod_cast h_T_card
  simpa [dyadicSquareCount] using h_main

/-- Theorem 2: Dyadic square count is at most 9 times metric covering number. -/
lemma dyadicSquareCount_le_9_mul_externalCoveringNumber {δ : ℝ} (hδ : 0 < δ)
    {A : Set EuclideanPlane} :
    (dyadicSquareCount δ A : ENNReal) ≤
      9 * Metric.externalCoveringNumber δ.toNNReal A := by
  by_cases h_top : Metric.externalCoveringNumber δ.toNNReal A = ⊤
  · rw [h_top] <;> simp
  · have hM : (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) ≠ ⊤ := by
      simpa using h_top
    rcases exists_finite_cover_le (le_refl (Metric.externalCoveringNumber δ.toNNReal A : ENNReal)) hM
      with ⟨C, hC_cover, hC_card⟩
    have h1 : dyadicSquareCount δ A ≤ ↑(9 * C.card) :=
      dyadicSquareCount_le_9_mul_cover hδ hC_cover
    calc (dyadicSquareCount δ A : ENNReal)
      ≤ ↑(9 * C.card) := by exact_mod_cast h1
    _ = 9 * (C.card : ENNReal) := by
      simp [mul_comm] <;> norm_cast
    _ ≤ 9 * Metric.externalCoveringNumber δ.toNNReal A := by
      gcongr
      <;> exact hC_card

/-- Equivalent lower bound: metric covering number ≥ dyadic square count / 9. -/
lemma externalCoveringNumber_ge_dyadicSquareCount_div_9 {δ : ℝ} (hδ : 0 < δ)
    {A : Set EuclideanPlane} :
    (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) ≥
      (dyadicSquareCount δ A : ENNReal) / 9 := by
  set e : ENNReal := ↑(Metric.externalCoveringNumber δ.toNNReal A) with he
  have h : (dyadicSquareCount δ A : ENNReal) ≤ 9 * e :=
    dyadicSquareCount_le_9_mul_externalCoveringNumber hδ (A := A)
  have h9_pos : (0 : ENNReal) < 9 := by norm_num
  have h9_ne_top : (9 : ENNReal) ≠ ⊤ := by simp
  have h_div : (dyadicSquareCount δ A : ENNReal) / 9 ≤ (9 * e) / 9 := by gcongr
  have h_cancel : (9 * e) / 9 = e := by
    have h4 : (9 : ENNReal) ≠ 0 := by simp
    have h5 : (9 : ENNReal) ≠ ⊤ := by simp
    have h6 : (9 : ENNReal) * (9 : ENNReal)⁻¹ = 1 := by exact ENNReal.mul_inv_cancel h4 h9_ne_top
    have h7 : (9 * e) / 9 = (9 * e) * (9 : ENNReal)⁻¹ := by rfl
    rw [h7]
    have h8 : (9 * e) * (9 : ENNReal)⁻¹ = 9 * (9 : ENNReal)⁻¹ * e := by
      simp only [mul_assoc]
      <;> rw [mul_comm e ((9 : ENNReal)⁻¹)]
      <;> simp only [mul_assoc]
    rw [h8, h6]
    <;> simp
  rw [h_cancel] at h_div
  exact h_div

/-! # Theorem 3: Exact product lower bound for metric covering -/

/-- Exact multi-level lower bound: metric covering number at scale Δ^b
    of P ∩ Q_a is at least (∏_{i=a}^{b-1} N(i)) / 9. -/
lemma exactCovering_product_lower
    {P : Set EuclideanPlane} {m a b : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h_uniform : IsDyadicUniform P m Δ N)
    {n : ℕ} (hn_pos : 0 < n) (hΔ_int : (1 : ℝ) = (n : ℝ) * Δ)
    (hab : a ≤ b) (hbm : b ≤ m)
    (i j : ℤ) (hQ : (P ∩ dyadicSquare (Δ ^ a) i j).Nonempty) :
    (Metric.externalCoveringNumber (Δ ^ b).toNNReal
       (P ∩ dyadicSquare (Δ ^ a) i j) : ENNReal) ≥
      (↑(∏ k ∈ Finset.Ico a b, N k) : ENNReal) / 9 := by
  have hΔ_pos : 0 < Δ ^ b := pow_pos h_uniform.1 b
  have h_count : dyadicSquareCount (Δ ^ b) (P ∩ dyadicSquare (Δ ^ a) i j) =
      ↑(∏ k ∈ Finset.Ico a b, N k) :=
    dyadicSquareCount_multilevel h_uniform hn_pos hΔ_int hab hbm i j hQ
  have h_main : (Metric.externalCoveringNumber (Δ ^ b).toNNReal
         (P ∩ dyadicSquare (Δ ^ a) i j) : ENNReal) ≥
       (dyadicSquareCount (Δ ^ b) (P ∩ dyadicSquare (Δ ^ a) i j) : ENNReal) / 9 :=
    externalCoveringNumber_ge_dyadicSquareCount_div_9 hΔ_pos
  rw [h_count] at h_main
  exact h_main

end DirecretisedFurstenbergEstimate.MultiscaleDecomposition
