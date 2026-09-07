module

/-
  P_ready S-set refinement via covering comparison.

  Given:
  - P_oriented is a (δ, t, C_P)-set
  - P_ready ⊆ P_oriented
  - squares_all covers P_oriented
  - squares' ⊆ squares_all, retained with ratio K_band+1
  - every square in squares' meets P_ready

  Prove:
  1. Ncover(P_oriented) ≤ 9*(K_band+1) * Ncover(P_ready)
  2. P_ready is a (δ, t, C_P * 9*(K_band+1))-set

  Uses:
  - SquareCovering for ncover_le_card_squares and squares_card_le_nine_times_ncover
  - SSetRefinement for IsDeltaSSet.subset_with_cover_ratio

  Whiteprint node: section9 / p_ready_sset
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.SquareCovering
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.SSetRefinement
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem

/-- P_ready S-set refinement via covering comparison.

    Given P_oriented is a (δ, t, C_P)-set, P_ready ⊆ P_oriented,
    squares_all covers P_oriented, squares' is retained with ratio K_band+1,
    and every square in squares' meets P_ready, then:
    - Ncover(P_oriented) ≤ 9*(K_band+1) * Ncover(P_ready)
    - P_ready is a (δ, t, C_P * 9*(K_band+1))-set -/
lemma p_ready_sset
    {k : ℕ} {t C_P : ℝ}
    {P_oriented P_ready : Set EuclideanPlane}
    {squares_all squares' : Finset (DyadicSquare k)}
    {K_band : ℕ}
    (hP_oriented_sset : IsDeltaSSet (dyadicDelta k) t C_P P_oriented)
    (hP_ready_sub : P_ready ⊆ P_oriented)
    (hP_oriented_cover : P_oriented ⊆ ⋃ q ∈ squares_all, (q.toSet : Set EuclideanPlane))
    (h_retention : (squares'.card : ℝ) ≥ (squares_all.card : ℝ) / (K_band + 1 : ℝ))
    (h_ready_occupancy : ∀ q ∈ squares', (q.toSet ∩ P_ready).Nonempty)
    (hK_band_pos : 0 < K_band + 1) :
    Metric.externalCoveringNumber (dyadicDelta k).toNNReal P_oriented ≤
      (9 : ENNReal) * (K_band + 1 : ENNReal) * Metric.externalCoveringNumber (dyadicDelta k).toNNReal P_ready ∧
    IsDeltaSSet (dyadicDelta k) t (C_P * (9 * (K_band + 1 : ℝ))) P_ready := by
  let δ := dyadicDelta k

  -- Step 1: Ncover(P_oriented) ≤ card(squares_all)
  have h1 : Metric.externalCoveringNumber δ.toNNReal P_oriented ≤ (squares_all.card : ENNReal) :=
    ncover_le_card_squares hP_oriented_cover

  -- Step 2: card(squares_all) ≤ (K_band+1) * card(squares')
  have hK_real_pos : (0 : ℝ) < (K_band + 1 : ℝ) := by exact_mod_cast hK_band_pos
  have hpos : (K_band + 1 : ℝ) ≠ 0 := hK_real_pos.ne.symm
  have h2 : (squares_all.card : ENNReal) ≤ ((K_band + 1 : ENNReal) * (squares'.card : ENNReal)) := by
    have h_eq : (K_band + 1 : ℝ) * ((squares_all.card : ℝ) / (K_band + 1 : ℝ)) = (squares_all.card : ℝ) := by
      have h : (K_band + 1 : ℝ) ≠ 0 := hpos
      field_simp [h] <;> ring
    have h_mul : (K_band + 1 : ℝ) * ((squares_all.card : ℝ) / (K_band + 1 : ℝ)) ≤ (K_band + 1 : ℝ) * (squares'.card : ℝ) := by
      exact mul_le_mul_of_nonneg_left h_retention hK_real_pos.le
    have h2_real : (squares_all.card : ℝ) ≤ (K_band + 1 : ℝ) * (squares'.card : ℝ) := by
      rw [←h_eq]; exact h_mul
    exact_mod_cast h2_real

  -- Step 3: card(squares') ≤ 9 * Ncover(P_ready)
  have h3 : (squares'.card : ENNReal) ≤ (9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal P_ready :=
    squares_card_le_nine_times_ncover h_ready_occupancy

  -- Combine: Ncover(P_oriented) ≤ 9*(K_band+1) * Ncover(P_ready)
  have h_cover_ratio : Metric.externalCoveringNumber δ.toNNReal P_oriented ≤
      (9 : ENNReal) * (K_band + 1 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal P_ready := by
    calc Metric.externalCoveringNumber δ.toNNReal P_oriented
      ≤ (squares_all.card : ENNReal) := h1
    _ ≤ ((K_band + 1 : ENNReal) * (squares'.card : ENNReal)) := h2
    _ ≤ (K_band + 1 : ENNReal) * ((9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal P_ready) := by gcongr
    _ = (9 : ENNReal) * (K_band + 1 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal P_ready := by ring

  -- Step 4: Apply subset_with_cover_ratio from SSetRefinement
  let K_ratio : ℝ := 9 * (K_band + 1 : ℝ)
  have hK_ratio_pos : 0 < K_ratio := by positivity
  have h_ratio' : (Metric.externalCoveringNumber δ.toNNReal P_oriented : ENNReal) ≤
      ENNReal.ofReal K_ratio * (Metric.externalCoveringNumber δ.toNNReal P_ready) := by
    have h4 : ENNReal.ofReal K_ratio = (9 : ENNReal) * (K_band + 1 : ENNReal) := by
      simp [K_ratio] <;> norm_cast <;> ring
    rw [h4]; exact h_cover_ratio
  have hP_ready_sset : IsDeltaSSet δ t (C_P * K_ratio) P_ready :=
    IsDeltaSSet.subset_with_cover_ratio hK_ratio_pos hP_oriented_sset hP_ready_sub h_ratio'
  have h_const : C_P * K_ratio = C_P * (9 * (K_band + 1 : ℝ)) := by
    simp [K_ratio] <;> ring
  rw [h_const] at hP_ready_sset
  exact ⟨h_cover_ratio, hP_ready_sset⟩

end DirecretisedFurstenbergEstimate.Section9
