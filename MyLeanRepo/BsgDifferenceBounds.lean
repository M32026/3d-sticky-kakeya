module

/-
# BSG Difference-Set Bounds — Corrected

Obligation 4: dense graph + BSG → B1, B2 with explicit difference-set bounds.

## Correction

The previous proof assumed `N(B2) ≤ N(B1)` but used the reverse inequality.
This version takes **two-sided comparability** as a hypothesis and uses
the squared sumset bound directly to avoid one-sided ordering.

## Main results

1. `bsg_two_sided_comparability`: derives B1/B2 comparability from A1/A2
2. `bsg_difference_set_bounds_v2`: N(B1-B1), N(B2-B1) ≤ K_BSG · N(B1)
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.IsRealDeltaSetInheritance
public import MyLeanRepo.DiscretizedPluennecke
public import MyLeanRepo.RuzsaTriangle
public import MyLeanRepo.SetDiscretizationBridge
public import MyLeanRepo.RoundingWrapper
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open ProductLikeIncidence ENNReal Set Bornology Finset Classical

attribute [local instance] Classical.propDecidable

namespace Phase2Bsg

private lemma le_div_of_mul_le {a b c : ENNReal} (hc_pos : c ≠ 0) (hc_top : c ≠ ⊤)
    (h : c * a ≤ b) : a ≤ b / c := by
  calc a
    = a * 1 := by ring
  _ = a * (c * (1 / c)) := by
    have h3 : c * (1 / c) = 1 := by
      simpa [div_eq_mul_inv] using ENNReal.mul_inv_cancel hc_pos hc_top
    rw [h3] <;> ring
  _ = (c * a) * (1 / c) := by ring
  _ ≤ b * (1 / c) := by gcongr
  _ = b / c := by simp [div_eq_mul_inv] <;> ring

private lemma nreal_pos {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ}
    (hA_bdd : IsBounded A) (hA_nonempty : A.Nonempty) : 0 < Nreal δ A := by
  rcases hA_nonempty with ⟨x, hx⟩
  let g : Fin 1 → ℝ := fun (_ : Fin 1) => x
  let p : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 (Fin 1 → ℝ)).symm g
  have h_p0 : p 0 = x := by simp [p, g]
  have hp : p ∈ realLineCopy A := by
    have h : p 0 ∈ A := by rw [h_p0] <;> exact hx
    simpa [realLineCopy] using h
  have h1 : (realLineCopy A).Nonempty := ⟨p, hp⟩
  have h2 : 0 < dyadicCoveringNumber δ (realLineCopy A) :=
    robust_projection.dyadic_covering_number_pos hδ h1
  have h3 : Nreal δ A = ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A)) := by rfl
  rw [h3]; exact_mod_cast h2

private lemma nreal_ne_top {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ}
    (hA_bdd : IsBounded A) : Nreal δ A ≠ ⊤ := by
  have hA_bdd' : IsBounded (realLineCopy A) :=
    SetDiscretizationBridge.realLineCopy_bounded_iff.mpr hA_bdd
  have h1 : (dyadicCubesMeeting δ (realLineCopy A)).Finite :=
    ProductLikeIncidence.dyadicCubesMeeting_finite hδ hA_bdd'
  have h2 : (dyadicCoveringNumber δ (realLineCopy A)) ≠ ⊤ :=
    (Set.encard_lt_top_iff.mpr h1).ne
  have h3 : Nreal δ A = ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A)) := by rfl
  rw [h3]; exact_mod_cast h2

/-- If `x^2 ≤ y^2` in ENNReal and `y ≠ 0`, then `x ≤ y`. -/
private lemma ennreal_le_of_sq_le_sq {x y : ENNReal} (hy_pos : y ≠ 0)
    (h : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  by_contra h4
  have h5 : y < x := lt_of_not_ge h4
  have h_y_ne_top : y ≠ ⊤ := by
    intro h_top
    rw [h_top] at h5
    exact not_top_lt h5
  have h6 : y * y < x * y := ENNReal.mul_lt_mul_left hy_pos h_y_ne_top h5
  have h7 : x * y ≤ x * x := by
    gcongr <;> exact le_of_lt h5
  have h8 : y * y < x * x := lt_of_lt_of_le h6 h7
  have h9 : y ^ 2 < x ^ 2 := by simpa [pow_two] using h8
  exact not_le.mpr h9 h

/-- **Two-sided comparability of B1, B2** from A1, A2 comparability. -/
lemma bsg_two_sided_comparability
    {δ : ℝ} {A1 A2 B1 B2 : Set ℝ}
    {K_A c_ret : ENNReal}
    (hA1_le_A2 : Nreal δ A1 ≤ K_A * Nreal δ A2)
    (hA2_le_A1 : Nreal δ A2 ≤ K_A * Nreal δ A1)
    (h_ret1 : c_ret * Nreal δ A1 ≤ Nreal δ B1)
    (h_ret2 : c_ret * Nreal δ A2 ≤ Nreal δ B2)
    (hB1_sub_A1 : B1 ⊆ A1) (hB2_sub_A2 : B2 ⊆ A2)
    (hc_ret_pos : c_ret ≠ 0) (hc_ret_ne_top : c_ret ≠ ⊤)
    (hK_A_ne_top : K_A ≠ ⊤) :
    ∃ (K_ratio : ENNReal),
      Nreal δ B1 ≤ K_ratio * Nreal δ B2 ∧
      Nreal δ B2 ≤ K_ratio * Nreal δ B1 := by
  have hN_B1_le_A1 : Nreal δ B1 ≤ Nreal δ A1 :=
    robust_projection_main.Nreal_mono_local (h := hB1_sub_A1)
  have hN_B2_le_A2 : Nreal δ B2 ≤ Nreal δ A2 :=
    robust_projection_main.Nreal_mono_local (h := hB2_sub_A2)
  let K_ratio := K_A / c_ret
  have hK_ratio_ne_top : K_ratio ≠ ⊤ := ENNReal.div_ne_top hK_A_ne_top hc_ret_pos

  have hA2_le_B2div : Nreal δ A2 ≤ Nreal δ B2 / c_ret :=
    le_div_of_mul_le hc_ret_pos hc_ret_ne_top h_ret2
  have hA1_le_B1div : Nreal δ A1 ≤ Nreal δ B1 / c_ret :=
    le_div_of_mul_le hc_ret_pos hc_ret_ne_top h_ret1

  have h1 : Nreal δ B1 ≤ K_ratio * Nreal δ B2 := by
    calc Nreal δ B1
      ≤ Nreal δ A1 := hN_B1_le_A1
    _ ≤ K_A * Nreal δ A2 := hA1_le_A2
    _ ≤ K_A * (Nreal δ B2 / c_ret) := by gcongr
    _ = K_ratio * Nreal δ B2 := by
      simp [K_ratio, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] <;> ring

  have h2 : Nreal δ B2 ≤ K_ratio * Nreal δ B1 := by
    calc Nreal δ B2
      ≤ Nreal δ A2 := hN_B2_le_A2
    _ ≤ K_A * Nreal δ A1 := hA2_le_A1
    _ ≤ K_A * (Nreal δ B1 / c_ret) := by gcongr
    _ = K_ratio * Nreal δ B1 := by
      simp [K_ratio, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] <;> ring

  exact ⟨K_ratio, h1, h2⟩

/-- **BSG difference-set bounds** (corrected, obligation 4) -/
lemma bsg_difference_set_bounds_v2
    {δ : ℝ} (hδ : 0 < δ)
    {B1 B2 : Set ℝ}
    (hB1_bdd : IsBounded B1) (hB2_bdd : IsBounded B2)
    (hB1_nonempty : B1.Nonempty) (hB2_nonempty : B2.Nonempty)
    {K_eff K_ratio : ENNReal}
    (h_sum_sq : Nreal δ (Set.image2 (· + ·) B1 B2) ^ 2 ≤
        K_eff * K_eff * Nreal δ B1 * Nreal δ B2)
    (hB2_le_B1 : Nreal δ B2 ≤ K_ratio * Nreal δ B1)
    (hK_ratio_ge_one : 1 ≤ K_ratio)
    (hK_eff_ge_one : 1 ≤ K_eff)
    (hK_eff_ne_top : K_eff ≠ ⊤)
    (hK_ratio_ne_top : K_ratio ≠ ⊤) :
    ∃ (K_BSG : ENNReal),
      Nreal δ (Set.image2 (· - ·) B1 B1) ≤ K_BSG * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· - ·) B2 B1) ≤ K_BSG * Nreal δ B1 := by
  let N_B1 := Nreal δ B1
  let N_B2 := Nreal δ B2
  let N_sum := Nreal δ (Set.image2 (· + ·) B1 B2)

  have hN_B1_pos : 0 < N_B1 := nreal_pos hδ hB1_bdd hB1_nonempty
  have hN_B2_pos : 0 < N_B2 := nreal_pos hδ hB2_bdd hB2_nonempty
  have hN_B1_ne_zero : N_B1 ≠ 0 := hN_B1_pos.ne'
  have hN_B2_ne_zero : N_B2 ≠ 0 := hN_B2_pos.ne'
  have hN_B1_ne_top : N_B1 ≠ ⊤ := nreal_ne_top hδ hB1_bdd
  have hN_B2_ne_top : N_B2 ≠ ⊤ := nreal_ne_top hδ hB2_bdd

  -- B1-B1: use squared bound directly, cancel N_B2
  have h_pr_diff := discretized_pluennecke_ruzsa_diff hδ hB1_bdd hB2_bdd hB2_nonempty
  have h_diff1 : Nreal δ (Set.image2 (· - ·) B1 B1) ≤ (9 * K_eff * K_eff) * N_B1 := by
    have h_raw : Nreal δ (Set.image2 (· - ·) B1 B1) * N_B2 ≤ 9 * N_sum * N_sum := h_pr_diff
    have h9 : 9 * N_sum * N_sum = 9 * N_sum ^ 2 := by ring
    rw [h9] at h_raw
    have h10 : N_sum ^ 2 ≤ K_eff * K_eff * N_B1 * N_B2 := h_sum_sq
    have h11 : Nreal δ (Set.image2 (· - ·) B1 B1) * N_B2 ≤
        (9 * K_eff * K_eff) * N_B1 * N_B2 := by
      calc Nreal δ (Set.image2 (· - ·) B1 B1) * N_B2
        ≤ 9 * N_sum ^ 2 := h_raw
      _ ≤ 9 * (K_eff * K_eff * N_B1 * N_B2) := by gcongr
      _ = (9 * K_eff * K_eff) * N_B1 * N_B2 := by ring
    have h12 : N_B2 * Nreal δ (Set.image2 (· - ·) B1 B1) ≤
        N_B2 * ((9 * K_eff * K_eff) * N_B1) := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using h11
    exact (ENNReal.mul_le_mul_iff_right hN_B2_ne_zero hN_B2_ne_top).mp h12

  -- B2+B2 via Plünnecke-Ruzsa sum
  have h_pr_sum := discretized_pluennecke_ruzsa_sum hδ hB2_bdd hB1_bdd hB1_nonempty
  have h_sum22 : Nreal δ (Set.image2 (· + ·) B2 B2) ≤ (9 * K_eff * K_eff) * N_B2 := by
    have h_comm : Set.image2 (· + ·) B2 B1 = Set.image2 (· + ·) B1 B2 := by
      ext z; constructor <;> rintro ⟨a, ha, b, hb, rfl⟩ <;> exact ⟨b, hb, a, ha, add_comm b a⟩
    have h_raw : Nreal δ (Set.image2 (· + ·) B2 B2) * N_B1 ≤ 9 * N_sum * N_sum := by
      rw [h_comm] at h_pr_sum
      exact h_pr_sum
    have h9 : 9 * N_sum * N_sum = 9 * N_sum ^ 2 := by ring
    rw [h9] at h_raw
    have h10 : N_sum ^ 2 ≤ K_eff * K_eff * N_B1 * N_B2 := h_sum_sq
    have h11 : Nreal δ (Set.image2 (· + ·) B2 B2) * N_B1 ≤
        (9 * K_eff * K_eff) * N_B2 * N_B1 := by
      calc Nreal δ (Set.image2 (· + ·) B2 B2) * N_B1
        ≤ 9 * N_sum ^ 2 := h_raw
      _ ≤ 9 * (K_eff * K_eff * N_B1 * N_B2) := by gcongr
      _ = (9 * K_eff * K_eff) * N_B2 * N_B1 := by ring
    have h12 : N_B1 * Nreal δ (Set.image2 (· + ·) B2 B2) ≤
        N_B1 * ((9 * K_eff * K_eff) * N_B2) := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using h11
    exact (ENNReal.mul_le_mul_iff_right hN_B1_ne_zero hN_B1_ne_top).mp h12

  -- Bound N_sum ≤ K_eff * K_ratio * N_B1
  have h_sum_le : N_sum ≤ K_eff * K_ratio * N_B1 := by
    have h11 : K_eff * K_eff * N_B1 * N_B2 ≤
        K_eff * K_eff * N_B1 * (K_ratio * N_B1) := by gcongr
    have h12 : K_eff * K_eff * N_B1 * (K_ratio * N_B1) =
        K_eff * K_eff * K_ratio * N_B1 * N_B1 := by ring
    have h13 : K_eff * K_eff * K_ratio * N_B1 * N_B1 ≤
        (K_eff * K_ratio * N_B1) * (K_eff * K_ratio * N_B1) := by
      have h14 : K_ratio ≤ K_ratio * K_ratio := by
        calc K_ratio
          = K_ratio * 1 := by ring
        _ ≤ K_ratio * K_ratio := by gcongr <;> exact hK_ratio_ge_one
      calc K_eff * K_eff * K_ratio * N_B1 * N_B1
        = K_eff * K_eff * (K_ratio * N_B1 * N_B1) := by ring
      _ ≤ K_eff * K_eff * (K_ratio * K_ratio * N_B1 * N_B1) := by gcongr
      _ = (K_eff * K_ratio * N_B1) * (K_eff * K_ratio * N_B1) := by ring
    have h13' : K_eff * K_eff * K_ratio * N_B1 * N_B1 ≤ (K_eff * K_ratio * N_B1) ^ 2 := by
      have h_eq : (K_eff * K_ratio * N_B1) ^ 2 =
          (K_eff * K_ratio * N_B1) * (K_eff * K_ratio * N_B1) := by
        simp [pow_two]
      rw [h_eq]
      exact h13
    have h15 : N_sum ^ 2 ≤ (K_eff * K_ratio * N_B1) ^ 2 := by
      calc N_sum ^ 2
        ≤ K_eff * K_eff * N_B1 * N_B2 := h_sum_sq
      _ ≤ K_eff * K_eff * N_B1 * (K_ratio * N_B1) := h11
      _ = K_eff * K_eff * K_ratio * N_B1 * N_B1 := h12
      _ ≤ (K_eff * K_ratio * N_B1) ^ 2 := h13'
    have hN_sum_pos : 0 < N_sum := by
      have h_sum_bdd : IsBounded (Set.image2 (· + ·) B1 B2) :=
        IsBounded.add hB1_bdd hB2_bdd
      have h_sum_nonempty : (Set.image2 (· + ·) B1 B2).Nonempty :=
        Set.Nonempty.image2 hB1_nonempty hB2_nonempty
      exact nreal_pos hδ h_sum_bdd h_sum_nonempty
    have h_y_pos : (K_eff * K_ratio * N_B1) ≠ 0 := by
      have h1 : K_eff ≠ 0 := by
        by_contra h
        rw [h] at h_sum_sq
        have h_cont : (Nreal δ (Set.image2 (· + ·) B1 B2)) ^ 2 ≤ 0 := by
          simpa using h_sum_sq
        have h_nsum_zero : Nreal δ (Set.image2 (· + ·) B1 B2) = 0 := by
          simpa [pow_two] using h_cont
        exact hN_sum_pos.ne' h_nsum_zero
      have h2 : K_ratio ≠ 0 := by
        have h3 : 1 ≤ K_ratio := hK_ratio_ge_one
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one h3)
      have h4 : K_eff * K_ratio ≠ 0 := mul_ne_zero h1 h2
      exact mul_ne_zero h4 hN_B1_ne_zero
    exact ennreal_le_of_sq_le_sq h_y_pos h15

  -- B2-B1 via Ruzsa triangle
  have h_ruzsa := discretized_ruzsa_triangle hδ hB2_bdd hB1_bdd hB2_bdd hB2_nonempty
  have h_mixed : Nreal δ (Set.image2 (· - ·) B2 B1) ≤
      (81 * K_eff * K_eff * K_eff * K_ratio) * N_B1 := by
    have h_comm : Set.image2 (· + ·) B2 B1 = Set.image2 (· + ·) B1 B2 := by
      ext z; constructor <;> rintro ⟨a, ha, b, hb, rfl⟩ <;> exact ⟨b, hb, a, ha, add_comm b a⟩
    have h_raw : Nreal δ (Set.image2 (· - ·) B2 B1) * N_B2 ≤
        9 * Nreal δ (Set.image2 (· + ·) B2 B2) * N_sum := by
      rw [h_comm] at h_ruzsa
      exact h_ruzsa
    have h : Nreal δ (Set.image2 (· - ·) B2 B1) * N_B2 ≤
        (81 * K_eff * K_eff * K_eff * K_ratio) * N_B1 * N_B2 := by
      calc Nreal δ (Set.image2 (· - ·) B2 B1) * N_B2
        ≤ 9 * Nreal δ (Set.image2 (· + ·) B2 B2) * N_sum := h_raw
      _ ≤ 9 * ((9 * K_eff * K_eff) * N_B2) * N_sum := by gcongr
      _ ≤ 9 * ((9 * K_eff * K_eff) * N_B2) * (K_eff * K_ratio * N_B1) := by
          gcongr <;> exact h_sum_le
      _ = (81 * K_eff * K_eff * K_eff * K_ratio) * N_B1 * N_B2 := by ring
    have h12 : N_B2 * Nreal δ (Set.image2 (· - ·) B2 B1) ≤
        N_B2 * ((81 * K_eff * K_eff * K_eff * K_ratio) * N_B1) := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using h
    exact (ENNReal.mul_le_mul_iff_right hN_B2_ne_zero hN_B2_ne_top).mp h12

  let K_BSG := max (9 * K_eff * K_eff) (81 * K_eff * K_eff * K_eff * K_ratio)

  have h_final1 : Nreal δ (Set.image2 (· - ·) B1 B1) ≤ K_BSG * Nreal δ B1 := by
    have h : (9 * K_eff * K_eff) ≤ K_BSG := le_max_left _ _
    calc Nreal δ (Set.image2 (· - ·) B1 B1)
      ≤ (9 * K_eff * K_eff) * Nreal δ B1 := h_diff1
    _ ≤ K_BSG * Nreal δ B1 := by gcongr

  have h_final2 : Nreal δ (Set.image2 (· - ·) B2 B1) ≤ K_BSG * Nreal δ B1 := by
    have h : (81 * K_eff * K_eff * K_eff * K_ratio) ≤ K_BSG := le_max_right _ _
    calc Nreal δ (Set.image2 (· - ·) B2 B1)
      ≤ (81 * K_eff * K_eff * K_eff * K_ratio) * Nreal δ B1 := h_mixed
    _ ≤ K_BSG * Nreal δ B1 := by gcongr

  exact ⟨K_BSG, h_final1, h_final2⟩

/-- **Grid-alignment closure for sector arithmetic**.

If `B1, B2 ⊆ δℤ`, then all difference/sum sets used in the four-sector
Ring expansion remain subsets of `δℤ`:
- `B1 - B1 ⊆ δℤ`
- `B2 - B2 ⊆ δℤ`
- `B2 - B1 ⊆ δℤ`
- `B1 + B2 ⊆ δℤ`

This is needed for the FourSectorChart exact covering equalities. -/
lemma bsg_sector_grid_closure
    {δ : ℝ}
    {B1 B2 : Set ℝ}
    (hB1_grid : B1 ⊆ productLikeIntegerGrid δ)
    (hB2_grid : B2 ⊆ productLikeIntegerGrid δ) :
    (Set.image2 (· - ·) B1 B1 ⊆ productLikeIntegerGrid δ) ∧
    (Set.image2 (· - ·) B2 B2 ⊆ productLikeIntegerGrid δ) ∧
    (Set.image2 (· - ·) B2 B1 ⊆ productLikeIntegerGrid δ) ∧
    (Set.image2 (· + ·) B1 B2 ⊆ productLikeIntegerGrid δ) := by
  have h_grid_sub : ∀ (A B : Set ℝ), A ⊆ productLikeIntegerGrid δ →
      B ⊆ productLikeIntegerGrid δ →
      ∀ (op : ℝ → ℝ → ℝ), (∀ (k j : ℤ), ∃ (m : ℤ), op (δ * (k : ℝ)) (δ * (j : ℝ)) = δ * (m : ℝ)) →
      Set.image2 op A B ⊆ productLikeIntegerGrid δ := by
    intro A B hA hB op hop z hz
    rcases hz with ⟨a, ha, b, hb, rfl⟩
    have ha' : a ∈ productLikeIntegerGrid δ := hA ha
    have hb' : b ∈ productLikeIntegerGrid δ := hB hb
    rcases ha' with ⟨k, rfl⟩
    rcases hb' with ⟨j, rfl⟩
    rcases hop k j with ⟨m, hm⟩
    exact ⟨m, hm⟩
  have h_sub_int : ∀ (k j : ℤ), ∃ (m : ℤ), (δ * (k : ℝ)) - (δ * (j : ℝ)) = δ * (m : ℝ) := by
    intro k j
    refine ⟨k - j, ?_⟩
    simp; ring
  have h_add_int : ∀ (k j : ℤ), ∃ (m : ℤ), (δ * (k : ℝ)) + (δ * (j : ℝ)) = δ * (m : ℝ) := by
    intro k j
    refine ⟨k + j, ?_⟩
    simp; ring
  exact ⟨
    h_grid_sub B1 B1 hB1_grid hB1_grid (· - ·) h_sub_int,
    h_grid_sub B2 B2 hB2_grid hB2_grid (· - ·) h_sub_int,
    h_grid_sub B2 B1 hB2_grid hB1_grid (· - ·) h_sub_int,
    h_grid_sub B1 B2 hB1_grid hB2_grid (· + ·) h_add_int
  ⟩

/-- **2D grid alignment for a graph subset**. If `G` is a subset of the
Euclidean plane whose first coordinate lies in `B1` and second coordinate
lies in `B2`, and `B1, B2 ⊆ δℤ`, then `G ⊆ (δℤ)²`. -/
lemma bsg_graph_grid_closure
    {δ : ℝ}
    {B1 B2 : Set ℝ}
    (hB1_grid : B1 ⊆ productLikeIntegerGrid δ)
    (hB2_grid : B2 ⊆ productLikeIntegerGrid δ)
    {G : Set (EuclideanSpace ℝ (Fin 2))}
    (hG_sub : ∀ z ∈ G, z 0 ∈ B1 ∧ z 1 ∈ B2) :
    ∀ z ∈ G, z 0 ∈ productLikeIntegerGrid δ ∧ z 1 ∈ productLikeIntegerGrid δ := by
  intro z hz
  have h1 : z 0 ∈ B1 ∧ z 1 ∈ B2 := hG_sub z hz
  exact ⟨hB1_grid h1.1, hB2_grid h1.2⟩

/-- **Sector-ready BSG package** — outputs all four difference/sumset bounds
needed for the four-sector Ring expansion, with two-sided comparability
and finiteness/nonzero certificates for K_sector.

Sector mappings:
- Sector 1: A=B2, B=B1 → A-A=B2-B2, B-A=-(B2-B1)
- Sector 2: A=B1, B=B2 → A-A=B1-B1, B-A=B2-B1
- Sector 3: A=-B2, B=B1 → A-A=-(B2-B2), B-A=B1+B2
- Sector 4: A=-B1, B=B2 → A-A=-(B1-B1), B-A=B2+B1

Reflection preserves covering numbers, so N(-S)=N(S).
For sectors where A=B2, convert N(B1)-normalized bounds using N(B1) ≤ K_ratio·N(B2). -/
lemma bsg_sector_ready_package
    {δ : ℝ} (hδ : 0 < δ)
    {B1 B2 : Set ℝ}
    (hB1_bdd : IsBounded B1) (hB2_bdd : IsBounded B2)
    (hB1_nonempty : B1.Nonempty) (hB2_nonempty : B2.Nonempty)
    (hB1_grid : B1 ⊆ productLikeIntegerGrid δ)
    (hB2_grid : B2 ⊆ productLikeIntegerGrid δ)
    {K_eff K_ratio : ENNReal}
    (h_sum_sq : Nreal δ (Set.image2 (· + ·) B1 B2) ^ 2 ≤
        K_eff * K_eff * Nreal δ B1 * Nreal δ B2)
    (hB1_le_B2 : Nreal δ B1 ≤ K_ratio * Nreal δ B2)
    (hB2_le_B1 : Nreal δ B2 ≤ K_ratio * Nreal δ B1)
    (hK_ratio_ge_one : 1 ≤ K_ratio)
    (hK_eff_ge_one : 1 ≤ K_eff)
    (hK_eff_ne_top : K_eff ≠ ⊤)
    (hK_ratio_ne_top : K_ratio ≠ ⊤) :
    ∃ (K_sector : ENNReal),
      Nreal δ (Set.image2 (· - ·) B1 B1) ≤ K_sector * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· - ·) B2 B2) ≤ K_sector * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· - ·) B2 B1) ≤ K_sector * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· + ·) B1 B2) ≤ K_sector * Nreal δ B1 ∧
      K_sector = max (9 * K_eff * K_eff * K_ratio)
        (max (81 * K_eff * K_eff * K_eff * K_ratio) (K_eff * K_ratio)) ∧
      K_sector ≤ 81 * K_eff * K_eff * K_eff * K_ratio ∧
      K_sector ≠ ⊤ ∧
      K_sector ≠ 0 ∧
      (Set.image2 (· - ·) B1 B1 ⊆ productLikeIntegerGrid δ) ∧
      (Set.image2 (· - ·) B2 B2 ⊆ productLikeIntegerGrid δ) ∧
      (Set.image2 (· - ·) B2 B1 ⊆ productLikeIntegerGrid δ) ∧
      (Set.image2 (· + ·) B1 B2 ⊆ productLikeIntegerGrid δ) := by
  let N_B1 := Nreal δ B1
  let N_B2 := Nreal δ B2
  let N_sum := Nreal δ (Set.image2 (· + ·) B1 B2)

  have hN_B1_pos : 0 < N_B1 := nreal_pos hδ hB1_bdd hB1_nonempty
  have hN_B2_pos : 0 < N_B2 := nreal_pos hδ hB2_bdd hB2_nonempty
  have hN_B1_ne_zero : N_B1 ≠ 0 := hN_B1_pos.ne'
  have hN_B2_ne_zero : N_B2 ≠ 0 := hN_B2_pos.ne'
  have hN_B1_ne_top : N_B1 ≠ ⊤ := nreal_ne_top hδ hB1_bdd
  have hN_B2_ne_top : N_B2 ≠ ⊤ := nreal_ne_top hδ hB2_bdd

  -- B1-B1 bound
  have h_pr_diff1 := discretized_pluennecke_ruzsa_diff hδ hB1_bdd hB2_bdd hB2_nonempty
  have h_diff1 : Nreal δ (Set.image2 (· - ·) B1 B1) ≤ (9 * K_eff * K_eff) * N_B1 := by
    have h_raw : Nreal δ (Set.image2 (· - ·) B1 B1) * N_B2 ≤ 9 * N_sum * N_sum := h_pr_diff1
    have h9 : 9 * N_sum * N_sum = 9 * N_sum ^ 2 := by ring
    rw [h9] at h_raw
    have h10 : N_sum ^ 2 ≤ K_eff * K_eff * N_B1 * N_B2 := h_sum_sq
    have h11 : Nreal δ (Set.image2 (· - ·) B1 B1) * N_B2 ≤
        (9 * K_eff * K_eff) * N_B1 * N_B2 := by
      calc Nreal δ (Set.image2 (· - ·) B1 B1) * N_B2
        ≤ 9 * N_sum ^ 2 := h_raw
      _ ≤ 9 * (K_eff * K_eff * N_B1 * N_B2) := by gcongr
      _ = (9 * K_eff * K_eff) * N_B1 * N_B2 := by ring
    have h12 : N_B2 * Nreal δ (Set.image2 (· - ·) B1 B1) ≤
        N_B2 * ((9 * K_eff * K_eff) * N_B1) := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using h11
    exact (ENNReal.mul_le_mul_iff_right hN_B2_ne_zero hN_B2_ne_top).mp h12

  -- B2-B2 bound
  have h_pr_diff2 := discretized_pluennecke_ruzsa_diff hδ hB2_bdd hB1_bdd hB1_nonempty
  have h_comm_sum : Set.image2 (· + ·) B2 B1 = Set.image2 (· + ·) B1 B2 := by
    ext z; constructor <;> rintro ⟨a, ha, b, hb, rfl⟩ <;> exact ⟨b, hb, a, ha, add_comm b a⟩
  have h_diff2 : Nreal δ (Set.image2 (· - ·) B2 B2) ≤
      (9 * K_eff * K_eff * K_ratio) * N_B1 := by
    have h_raw : Nreal δ (Set.image2 (· - ·) B2 B2) * N_B1 ≤
        9 * Nreal δ (Set.image2 (· + ·) B2 B1) * Nreal δ (Set.image2 (· + ·) B2 B1) := h_pr_diff2
    rw [h_comm_sum] at h_raw
    have h9 : 9 * N_sum * N_sum = 9 * N_sum ^ 2 := by ring
    rw [h9] at h_raw
    have h10 : N_sum ^ 2 ≤ K_eff * K_eff * N_B1 * N_B2 := h_sum_sq
    have h11 : N_sum ^ 2 ≤ K_eff * K_eff * K_ratio * N_B1 * N_B1 := by
      calc N_sum ^ 2
        ≤ K_eff * K_eff * N_B1 * N_B2 := h10
      _ ≤ K_eff * K_eff * N_B1 * (K_ratio * N_B1) := by gcongr
      _ = K_eff * K_eff * K_ratio * N_B1 * N_B1 := by ring
    have h12 : Nreal δ (Set.image2 (· - ·) B2 B2) * N_B1 ≤
        (9 * K_eff * K_eff * K_ratio) * N_B1 * N_B1 := by
      calc Nreal δ (Set.image2 (· - ·) B2 B2) * N_B1
        ≤ 9 * N_sum ^ 2 := h_raw
      _ ≤ 9 * (K_eff * K_eff * K_ratio * N_B1 * N_B1) := by gcongr
      _ = (9 * K_eff * K_eff * K_ratio) * N_B1 * N_B1 := by ring
    have h13 : N_B1 * Nreal δ (Set.image2 (· - ·) B2 B2) ≤
        N_B1 * ((9 * K_eff * K_eff * K_ratio) * N_B1) := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using h12
    exact (ENNReal.mul_le_mul_iff_right hN_B1_ne_zero hN_B1_ne_top).mp h13

  -- B2-B1 bound (via Ruzsa triangle + B2+B2)
  have h_pr_sum22 := discretized_pluennecke_ruzsa_sum hδ hB2_bdd hB1_bdd hB1_nonempty
  have h_sum22 : Nreal δ (Set.image2 (· + ·) B2 B2) ≤ (9 * K_eff * K_eff) * N_B2 := by
    have h_raw : Nreal δ (Set.image2 (· + ·) B2 B2) * N_B1 ≤ 9 * N_sum * N_sum := by
      rw [h_comm_sum] at h_pr_sum22
      exact h_pr_sum22
    have h9 : 9 * N_sum * N_sum = 9 * N_sum ^ 2 := by ring
    rw [h9] at h_raw
    have h10 : N_sum ^ 2 ≤ K_eff * K_eff * N_B1 * N_B2 := h_sum_sq
    have h11 : Nreal δ (Set.image2 (· + ·) B2 B2) * N_B1 ≤
        (9 * K_eff * K_eff) * N_B2 * N_B1 := by
      calc Nreal δ (Set.image2 (· + ·) B2 B2) * N_B1
        ≤ 9 * N_sum ^ 2 := h_raw
      _ ≤ 9 * (K_eff * K_eff * N_B1 * N_B2) := by gcongr
      _ = (9 * K_eff * K_eff) * N_B2 * N_B1 := by ring
    have h12 : N_B1 * Nreal δ (Set.image2 (· + ·) B2 B2) ≤
        N_B1 * ((9 * K_eff * K_eff) * N_B2) := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using h11
    exact (ENNReal.mul_le_mul_iff_right hN_B1_ne_zero hN_B1_ne_top).mp h12

  have h_sum_le : N_sum ≤ K_eff * K_ratio * N_B1 := by
    have h11 : K_eff * K_eff * N_B1 * N_B2 ≤
        K_eff * K_eff * N_B1 * (K_ratio * N_B1) := by gcongr
    have h12 : K_eff * K_eff * N_B1 * (K_ratio * N_B1) =
        K_eff * K_eff * K_ratio * N_B1 * N_B1 := by ring
    have h13 : K_eff * K_eff * K_ratio * N_B1 * N_B1 ≤
        (K_eff * K_ratio * N_B1) * (K_eff * K_ratio * N_B1) := by
      have h14 : K_ratio ≤ K_ratio * K_ratio := by
        calc K_ratio
          = K_ratio * 1 := by ring
        _ ≤ K_ratio * K_ratio := by gcongr <;> exact hK_ratio_ge_one
      calc K_eff * K_eff * K_ratio * N_B1 * N_B1
        = K_eff * K_eff * (K_ratio * N_B1 * N_B1) := by ring
      _ ≤ K_eff * K_eff * (K_ratio * K_ratio * N_B1 * N_B1) := by gcongr
      _ = (K_eff * K_ratio * N_B1) * (K_eff * K_ratio * N_B1) := by ring
    have h15 : N_sum ^ 2 ≤ (K_eff * K_ratio * N_B1) ^ 2 := by
      calc N_sum ^ 2
        ≤ K_eff * K_eff * N_B1 * N_B2 := h_sum_sq
      _ ≤ K_eff * K_eff * N_B1 * (K_ratio * N_B1) := h11
      _ = K_eff * K_eff * K_ratio * N_B1 * N_B1 := h12
      _ ≤ (K_eff * K_ratio * N_B1) ^ 2 := by
        have h_eq : (K_eff * K_ratio * N_B1) ^ 2 =
            (K_eff * K_ratio * N_B1) * (K_eff * K_ratio * N_B1) := by
          simp [pow_two]
        rw [h_eq]; exact h13
    have hN_sum_pos : 0 < N_sum := by
      have h_sum_bdd : IsBounded (Set.image2 (· + ·) B1 B2) :=
        IsBounded.add hB1_bdd hB2_bdd
      have h_sum_nonempty : (Set.image2 (· + ·) B1 B2).Nonempty :=
        Set.Nonempty.image2 hB1_nonempty hB2_nonempty
      exact nreal_pos hδ h_sum_bdd h_sum_nonempty
    have hK_eff_ne_zero : K_eff ≠ 0 := by
      by_contra h
      rw [h] at h_sum_sq
      have h_cont : (Nreal δ (Set.image2 (· + ·) B1 B2)) ^ 2 ≤ 0 := by
        simpa using h_sum_sq
      have h_nsum_zero : Nreal δ (Set.image2 (· + ·) B1 B2) = 0 := by
        simpa [pow_two] using h_cont
      exact hN_sum_pos.ne' h_nsum_zero
    have hK_ratio_ne_zero : K_ratio ≠ 0 := by
      have h3 : 1 ≤ K_ratio := hK_ratio_ge_one
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one h3)
    have h_y_pos : (K_eff * K_ratio * N_B1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hK_eff_ne_zero hK_ratio_ne_zero) hN_B1_ne_zero
    exact ennreal_le_of_sq_le_sq h_y_pos h15

  have h_ruzsa := discretized_ruzsa_triangle hδ hB2_bdd hB1_bdd hB2_bdd hB2_nonempty
  have h_mixed : Nreal δ (Set.image2 (· - ·) B2 B1) ≤
      (81 * K_eff * K_eff * K_eff * K_ratio) * N_B1 := by
    have h_raw : Nreal δ (Set.image2 (· - ·) B2 B1) * N_B2 ≤
        9 * Nreal δ (Set.image2 (· + ·) B2 B2) * N_sum := by
      rw [h_comm_sum] at h_ruzsa
      exact h_ruzsa
    have h : Nreal δ (Set.image2 (· - ·) B2 B1) * N_B2 ≤
        (81 * K_eff * K_eff * K_eff * K_ratio) * N_B1 * N_B2 := by
      calc Nreal δ (Set.image2 (· - ·) B2 B1) * N_B2
        ≤ 9 * Nreal δ (Set.image2 (· + ·) B2 B2) * N_sum := h_raw
      _ ≤ 9 * ((9 * K_eff * K_eff) * N_B2) * N_sum := by gcongr
      _ ≤ 9 * ((9 * K_eff * K_eff) * N_B2) * (K_eff * K_ratio * N_B1) := by
          gcongr <;> exact h_sum_le
      _ = (81 * K_eff * K_eff * K_eff * K_ratio) * N_B1 * N_B2 := by ring
    have h12 : N_B2 * Nreal δ (Set.image2 (· - ·) B2 B1) ≤
        N_B2 * ((81 * K_eff * K_eff * K_eff * K_ratio) * N_B1) := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using h
    exact (ENNReal.mul_le_mul_iff_right hN_B2_ne_zero hN_B2_ne_top).mp h12

  let K_sector := max (9 * K_eff * K_eff * K_ratio)
                      (max (81 * K_eff * K_eff * K_eff * K_ratio) (K_eff * K_ratio))

  have h1 : Nreal δ (Set.image2 (· - ·) B1 B1) ≤ K_sector * N_B1 := by
    have h : (9 * K_eff * K_eff) ≤ 9 * K_eff * K_eff * K_ratio := by
      have hK : 1 ≤ K_ratio := hK_ratio_ge_one
      calc (9 * K_eff * K_eff)
        = (9 * K_eff * K_eff) * 1 := by ring
      _ ≤ (9 * K_eff * K_eff) * K_ratio := by gcongr
      _ = 9 * K_eff * K_eff * K_ratio := by ring
    have h2 : (9 * K_eff * K_eff * K_ratio) ≤ K_sector := le_max_left _ _
    calc Nreal δ (Set.image2 (· - ·) B1 B1)
      ≤ (9 * K_eff * K_eff) * N_B1 := h_diff1
    _ ≤ (9 * K_eff * K_eff * K_ratio) * N_B1 := by gcongr
    _ ≤ K_sector * N_B1 := by gcongr

  have h2 : Nreal δ (Set.image2 (· - ·) B2 B2) ≤ K_sector * N_B1 := by
    have h : (9 * K_eff * K_eff * K_ratio) ≤ K_sector := le_max_left _ _
    calc Nreal δ (Set.image2 (· - ·) B2 B2)
      ≤ (9 * K_eff * K_eff * K_ratio) * N_B1 := h_diff2
    _ ≤ K_sector * N_B1 := by gcongr

  have h3 : Nreal δ (Set.image2 (· - ·) B2 B1) ≤ K_sector * N_B1 := by
    have h : (81 * K_eff * K_eff * K_eff * K_ratio) ≤ K_sector := by
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    calc Nreal δ (Set.image2 (· - ·) B2 B1)
      ≤ (81 * K_eff * K_eff * K_eff * K_ratio) * N_B1 := h_mixed
    _ ≤ K_sector * N_B1 := by gcongr

  have h4 : N_sum ≤ K_sector * N_B1 := by
    have h : (K_eff * K_ratio) ≤ K_sector := by
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    calc N_sum
      ≤ K_eff * K_ratio * N_B1 := h_sum_le
    _ = (K_eff * K_ratio) * N_B1 := by ring
    _ ≤ K_sector * N_B1 := by gcongr

  have hK_sector_ne_top : K_sector ≠ ⊤ := by
    have h1 : (9 * K_eff * K_eff * K_ratio) ≠ ⊤ := by
      have h91 : (9 : ENNReal) ≠ ⊤ := by simp
      have h : (9 : ENNReal) * K_eff * K_eff * K_ratio ≠ ⊤ := by
        apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · apply ENNReal.mul_ne_top h91 hK_eff_ne_top
          · exact hK_eff_ne_top
        · exact hK_ratio_ne_top
      simpa [mul_assoc] using h
    have h2 : (81 * K_eff * K_eff * K_eff * K_ratio) ≠ ⊤ := by
      have h81 : (81 : ENNReal) ≠ ⊤ := by simp
      have h : (81 : ENNReal) * K_eff * K_eff * K_eff * K_ratio ≠ ⊤ := by
        apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · apply ENNReal.mul_ne_top
            · apply ENNReal.mul_ne_top h81 hK_eff_ne_top
            · exact hK_eff_ne_top
          · exact hK_eff_ne_top
        · exact hK_ratio_ne_top
      simpa [mul_assoc] using h
    have h3 : (K_eff * K_ratio) ≠ ⊤ := ENNReal.mul_ne_top hK_eff_ne_top hK_ratio_ne_top
    have h4 : max (81 * K_eff * K_eff * K_eff * K_ratio) (K_eff * K_ratio) ≠ ⊤ := by
      intro h
      have h5 : (81 * K_eff * K_eff * K_eff * K_ratio) = ⊤ ∨ (K_eff * K_ratio) = ⊤ := by
        simpa [max_eq_top] using h
      rcases h5 with (h5 | h5) <;> tauto
    intro h
    dsimp only [K_sector] at h
    have h5 : (9 * K_eff * K_eff * K_ratio) = ⊤ ∨
        max (81 * K_eff * K_eff * K_eff * K_ratio) (K_eff * K_ratio) = ⊤ := by
      simpa [max_eq_top] using h
    rcases h5 with (h5 | h5) <;> tauto

  have hK_sector_ne_zero : K_sector ≠ 0 := by
    have hK_eff_ne_zero : K_eff ≠ 0 := by
      by_contra h
      rw [h] at h_sum_sq
      have h_cont : (Nreal δ (Set.image2 (· + ·) B1 B2)) ^ 2 ≤ 0 := by
        simpa using h_sum_sq
      have h_nsum_zero : Nreal δ (Set.image2 (· + ·) B1 B2) = 0 := by
        simpa [pow_two] using h_cont
      have hN_sum_pos : 0 < N_sum := by
        have h_sum_bdd : IsBounded (Set.image2 (· + ·) B1 B2) :=
          IsBounded.add hB1_bdd hB2_bdd
        have h_sum_nonempty : (Set.image2 (· + ·) B1 B2).Nonempty :=
          Set.Nonempty.image2 hB1_nonempty hB2_nonempty
        exact nreal_pos hδ h_sum_bdd h_sum_nonempty
      exact hN_sum_pos.ne' h_nsum_zero
    have hK_ratio_ne_zero : K_ratio ≠ 0 := by
      have h3 : 1 ≤ K_ratio := hK_ratio_ge_one
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one h3)
    have h5 : (K_eff * K_ratio) ≠ 0 := mul_ne_zero hK_eff_ne_zero hK_ratio_ne_zero
    have h6 : (K_eff * K_ratio) ≤ K_sector := by
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    exact ne_bot_of_le_ne_bot h5 h6

  have h_grid := bsg_sector_grid_closure hB1_grid hB2_grid

  -- V3 bound: K_sector ≤ 81 * K_eff^3 * K_ratio
  have hv3_eff2_le : K_eff * K_eff ≤ K_eff * K_eff * K_eff :=
    le_mul_of_one_le_right (by positivity) hK_eff_ge_one
  have hv3_9_le : (9 : ENNReal) * (K_eff * K_eff) ≤ (81 : ENNReal) * (K_eff * K_eff * K_eff) := by
    have h9 : (9 : ENNReal) ≤ 81 := by norm_num
    gcongr
  have hv3_1_le : (9 * K_eff * K_eff * K_ratio) ≤ 81 * K_eff * K_eff * K_eff * K_ratio := by
    have h : (9 : ENNReal) * (K_eff * K_eff) * K_ratio ≤ (81 : ENNReal) * (K_eff * K_eff * K_eff) * K_ratio :=
      mul_le_mul_of_nonneg_right hv3_9_le (by positivity)
    simpa [mul_assoc] using h
  have hv3_one_le_eff2 : (1 : ENNReal) ≤ K_eff * K_eff := by
    have h : (1 : ENNReal) ≤ (1 : ENNReal) * K_eff := le_mul_of_one_le_right (by positivity) hK_eff_ge_one
    simpa using h
  have hv3_1_le_81 : (1 : ENNReal) ≤ 81 * (K_eff * K_eff) := by
    have h81 : (1 : ENNReal) ≤ 81 := by norm_num
    have h : (81 : ENNReal) ≤ 81 * (K_eff * K_eff) :=
      le_mul_of_one_le_right (by positivity) hv3_one_le_eff2
    exact le_trans h81 h
  have hv3_eff_le : K_eff ≤ 81 * K_eff * K_eff * K_eff := by
    calc K_eff
      = 1 * K_eff := by ring
    _ ≤ (81 * (K_eff * K_eff)) * K_eff := by
      exact mul_le_mul_of_nonneg_right hv3_1_le_81 (by positivity)
    _ = 81 * K_eff * K_eff * K_eff := by ring
  have hv3_3_le : (K_eff * K_ratio) ≤ 81 * K_eff * K_eff * K_eff * K_ratio := by
    have h : K_eff * K_ratio ≤ (81 * K_eff * K_eff * K_eff) * K_ratio :=
      mul_le_mul_of_nonneg_right hv3_eff_le (by positivity)
    simpa [mul_assoc] using h
  have hK_sector_le : K_sector ≤ 81 * K_eff * K_eff * K_eff * K_ratio := by
    dsimp only [K_sector]
    have h4 : max (81 * K_eff * K_eff * K_eff * K_ratio) (K_eff * K_ratio) ≤
        81 * K_eff * K_eff * K_eff * K_ratio := by
      apply max_le
      · exact le_refl _
      · exact hv3_3_le
    apply max_le
    · exact hv3_1_le
    · exact h4

  exact ⟨K_sector, h1, h2, h3, h4, rfl, hK_sector_le, hK_sector_ne_top, hK_sector_ne_zero,
    h_grid.1, h_grid.2.1, h_grid.2.2.1, h_grid.2.2.2⟩

/-- **Generic bound for K_sector**. If K_eff ≤ C1 and K_ratio ≤ C2, then
K_sector ≤ max(9·C1²·C2, 81·C1³·C2, C1·C2).
Specialize C1 = δ^(-q_eff), C2 = δ^(-q_ratio) to obtain the power bound. -/
lemma bsg_sector_generic_bound
    {K_eff K_ratio C1 C2 : ENNReal}
    (hK_eff_le : K_eff ≤ C1) (hK_ratio_le : K_ratio ≤ C2)
    (K_sector : ENNReal)
    (hK_sector_def : K_sector = max (9 * K_eff * K_eff * K_ratio)
                         (max (81 * K_eff * K_eff * K_eff * K_ratio) (K_eff * K_ratio))) :
    K_sector ≤ max (9 * C1 * C1 * C2) (max (81 * C1 * C1 * C1 * C2) (C1 * C2)) := by
  rw [hK_sector_def]
  have h1 : (9 * K_eff * K_eff * K_ratio) ≤ (9 * C1 * C1 * C2) := by gcongr
  have h2 : (81 * K_eff * K_eff * K_eff * K_ratio) ≤ (81 * C1 * C1 * C1 * C2) := by gcongr
  have h3 : (K_eff * K_ratio) ≤ (C1 * C2) := by gcongr
  have h4 : max (81 * K_eff * K_eff * K_eff * K_ratio) (K_eff * K_ratio) ≤
      max (81 * C1 * C1 * C1 * C2) (C1 * C2) := by
    exact max_le_max h2 h3
  exact max_le_max h1 h4

/-- **Sector-specific denominator bounds**. Converts the N(B1)-normalized
ledger to bounds relative to N(A) for each sector's Ring set A.

Sectors 2,4 (A=B1 or -B1): use K_sector_B1 = K_sector.
Sectors 1,3 (A=B2 or -B2): use K_sector_B2 = K_sector * K_ratio.

Reflection preserves covering numbers, so N(B1-B2)=N(B2-B1) and N(-(B_i-B_i))=N(B_i-B_i). -/
lemma bsg_sector_denominator_bounds
    {δ : ℝ} {B1 B2 : Set ℝ} {K_eff K_ratio K_sector : ENNReal}
    (hB1_le_B2 : Nreal δ B1 ≤ K_ratio * Nreal δ B2)
    (hB2_le_B1 : Nreal δ B2 ≤ K_ratio * Nreal δ B1)
    (h1 : Nreal δ (Set.image2 (· - ·) B1 B1) ≤ K_sector * Nreal δ B1)
    (h2 : Nreal δ (Set.image2 (· - ·) B2 B2) ≤ K_sector * Nreal δ B1)
    (h3 : Nreal δ (Set.image2 (· - ·) B2 B1) ≤ K_sector * Nreal δ B1)
    (h4 : Nreal δ (Set.image2 (· + ·) B1 B2) ≤ K_sector * Nreal δ B1) :
    ∃ (K_sector_B1 K_sector_B2 : ENNReal),
      -- Sector 2,4: A = B1 or -B1
      Nreal δ (Set.image2 (· - ·) B1 B1) ≤ K_sector_B1 * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· - ·) B2 B1) ≤ K_sector_B1 * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· + ·) B1 B2) ≤ K_sector_B1 * Nreal δ B1 ∧
      -- Sector 1,3: A = B2 or -B2
      Nreal δ (Set.image2 (· - ·) B2 B2) ≤ K_sector_B2 * Nreal δ B2 ∧
      Nreal δ (Set.image2 (· - ·) B2 B1) ≤ K_sector_B2 * Nreal δ B2 ∧
      Nreal δ (Set.image2 (· + ·) B1 B2) ≤ K_sector_B2 * Nreal δ B2 := by
  let K_sector_B1 := K_sector
  let K_sector_B2 := K_sector * K_ratio
  have h5 : Nreal δ (Set.image2 (· - ·) B2 B2) ≤ K_sector_B2 * Nreal δ B2 := by
    calc Nreal δ (Set.image2 (· - ·) B2 B2)
      ≤ K_sector * Nreal δ B1 := h2
    _ ≤ K_sector * (K_ratio * Nreal δ B2) := by gcongr
    _ = K_sector_B2 * Nreal δ B2 := by
      simp [K_sector_B2] <;> ring
  have h6 : Nreal δ (Set.image2 (· - ·) B2 B1) ≤ K_sector_B2 * Nreal δ B2 := by
    calc Nreal δ (Set.image2 (· - ·) B2 B1)
      ≤ K_sector * Nreal δ B1 := h3
    _ ≤ K_sector * (K_ratio * Nreal δ B2) := by gcongr
    _ = K_sector_B2 * Nreal δ B2 := by
      simp [K_sector_B2] <;> ring
  have h7 : Nreal δ (Set.image2 (· + ·) B1 B2) ≤ K_sector_B2 * Nreal δ B2 := by
    calc Nreal δ (Set.image2 (· + ·) B1 B2)
      ≤ K_sector * Nreal δ B1 := h4
    _ ≤ K_sector * (K_ratio * Nreal δ B2) := by gcongr
    _ = K_sector_B2 * Nreal δ B2 := by
      simp [K_sector_B2] <;> ring
  exact ⟨K_sector_B1, K_sector_B2, h1, h3, h4, h5, h6, h7⟩

/-- **Power bound absorption for K_sector**. Given K_eff ≤ δ^(-q_eff) and
K_ratio ≤ δ^(-q_ratio), with δ ≤ 1/2, derive
K_sector ≤ δ^(-(3*q_eff + q_ratio + 7)).
The +7 absorbs the constant 81 (since δ ≤ 1/2 implies δ^(-7) ≥ 128 > 81). -/
lemma bsg_sector_power_bound_absorbed
    {δ : ℝ} (hδ : 0 < δ) (hδ_le_half : δ ≤ 1 / 2)
    {K_eff K_ratio : ENNReal}
    {q_eff q_ratio : ℝ} (hq_eff : 0 ≤ q_eff) (hq_ratio : 0 ≤ q_ratio)
    (hK_eff_pow : K_eff ≤ ENNReal.ofReal (δ ^ (-q_eff)))
    (hK_ratio_pow : K_ratio ≤ ENNReal.ofReal (δ ^ (-q_ratio)))
    (K_sector : ENNReal)
    (hK_sector_def : K_sector = max (9 * K_eff * K_eff * K_ratio)
                         (max (81 * K_eff * K_eff * K_eff * K_ratio) (K_eff * K_ratio))) :
    K_sector ≤ ENNReal.ofReal (δ ^ (-(3 * q_eff + q_ratio + 7))) := by
  set q_diff := 3 * q_eff + q_ratio + 7 with hq_diff_def
  set C1 := ENNReal.ofReal (δ ^ (-q_eff)) with hC1_def
  set C2 := ENNReal.ofReal (δ ^ (-q_ratio)) with hC2_def
  set D := ENNReal.ofReal (δ ^ (-q_diff)) with hD_def
  have h_main : K_sector ≤ max (9 * C1 * C1 * C2) (max (81 * C1 * C1 * C1 * C2) (C1 * C2)) :=
    bsg_sector_generic_bound hK_eff_pow hK_ratio_pow K_sector hK_sector_def
  have h_pos1 : 0 ≤ δ ^ (-q_eff) := by positivity
  have h_pos2 : 0 ≤ δ ^ (-q_ratio) := by positivity
  have h_pos7 : 0 ≤ δ ^ (-7 : ℝ) := by positivity
  have hδ_le_one : δ ≤ 1 := by linarith
  have h_81_real : (81 : ℝ) ≤ δ ^ (-7 : ℝ) := by
    have h4 : 1 / δ ≥ 2 := by
      calc 1 / δ
        ≥ 1 / (1 / 2) := by gcongr
      _ = 2 := by norm_num
    have h5 : (1 / δ) ^ 7 ≥ 128 := by
      have h6 : (1 / δ) ^ 7 ≥ (2 : ℝ) ^ 7 := by gcongr
      have h7 : (2 : ℝ) ^ 7 = 128 := by norm_num
      linarith
    have h8 : δ ^ (-7 : ℝ) = (1 / δ) ^ 7 := by
      have h9 : δ ^ (-7 : ℝ) = (δ ^ (7 : ℝ))⁻¹ := by
        rw [Real.rpow_neg (by linarith)] <;> norm_num
      have h10 : δ ^ (7 : ℝ) = δ ^ 7 := by simp
      have h11 : (1 / δ) ^ 7 = (δ ^ 7)⁻¹ := by
        field_simp [hδ.ne'] <;> ring
      rw [h9, h10, h11]
    rw [h8]
    linarith
  have h_81_ennreal : (81 : ENNReal) ≤ ENNReal.ofReal (δ ^ (-7 : ℝ)) := by
    have h8 : (81 : ENNReal) = ENNReal.ofReal (81 : ℝ) := by simp
    rw [h8]
    exact ENNReal.ofReal_le_ofReal h_81_real
  have h9_ennreal : (9 : ENNReal) ≤ ENNReal.ofReal (δ ^ (-7 : ℝ)) := by
    have h2 : (9 : ENNReal) ≤ (81 : ENNReal) := by norm_num
    exact le_trans h2 h_81_ennreal
  have h_real_eq7 : δ ^ (-7 : ℝ) * δ ^ (-q_eff) * δ ^ (-q_eff) * δ ^ (-q_eff) * δ ^ (-q_ratio) = δ ^ (-q_diff) := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
    <;> simp [hq_diff_def] <;> ring_nf
  have h_real_ineq3 : δ ^ (-7 : ℝ) * δ ^ (-q_eff) * δ ^ (-q_eff) * δ ^ (-q_ratio) ≤ δ ^ (-q_diff) := by
    have h10 : δ ^ (-7 : ℝ) * δ ^ (-q_eff) * δ ^ (-q_eff) * δ ^ (-q_ratio) =
        δ ^ (-7 - 2 * q_eff - q_ratio) := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ] <;> ring_nf
    rw [h10]
    have h11 : -q_diff ≤ -7 - 2 * q_eff - q_ratio := by
      simp [hq_diff_def] <;> linarith
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ_le_one h11
  have h_real3 : δ ^ (-q_eff) * δ ^ (-q_ratio) ≤ δ ^ (-q_diff) := by
    have h10 : δ ^ (-q_eff) * δ ^ (-q_ratio) = δ ^ (-(q_eff + q_ratio)) := by
      rw [← Real.rpow_add hδ] <;> ring_nf
    rw [h10]
    have h11 : -q_diff ≤ -(q_eff + q_ratio) := by
      simp [hq_diff_def] <;> linarith
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ_le_one h11
  have h_pos71 : 0 ≤ δ ^ (-7 : ℝ) * δ ^ (-q_eff) := by positivity
  have h_pos711 : 0 ≤ δ ^ (-7 : ℝ) * δ ^ (-q_eff) * δ ^ (-q_eff) := by positivity
  have h_pos7111 : 0 ≤ δ ^ (-7 : ℝ) * δ ^ (-q_eff) * δ ^ (-q_eff) * δ ^ (-q_eff) := by positivity
  have h_mul4 : ENNReal.ofReal (δ ^ (-7 : ℝ)) * C1 * C1 * C1 * C2 = D := by
    have h_eq : ENNReal.ofReal (δ ^ (-7 : ℝ)) * C1 * C1 * C1 * C2 =
        ENNReal.ofReal (δ ^ (-7 : ℝ) * δ ^ (-q_eff) * δ ^ (-q_eff) * δ ^ (-q_eff) * δ ^ (-q_ratio)) := by
      simp only [C1, C2]
      rw [← ENNReal.ofReal_mul h_pos7, ← ENNReal.ofReal_mul h_pos71,
          ← ENNReal.ofReal_mul h_pos711, ← ENNReal.ofReal_mul h_pos7111]
      <;> ring
    rw [h_eq, h_real_eq7, hD_def]
  have h_mul3 : ENNReal.ofReal (δ ^ (-7 : ℝ)) * C1 * C1 * C2 ≤ D := by
    have h_eq : ENNReal.ofReal (δ ^ (-7 : ℝ)) * C1 * C1 * C2 =
        ENNReal.ofReal (δ ^ (-7 : ℝ) * δ ^ (-q_eff) * δ ^ (-q_eff) * δ ^ (-q_ratio)) := by
      simp only [C1, C2]
      rw [← ENNReal.ofReal_mul h_pos7, ← ENNReal.ofReal_mul h_pos71,
          ← ENNReal.ofReal_mul h_pos711]
      <;> ring
    rw [h_eq]
    rw [hD_def]
    exact ENNReal.ofReal_le_ofReal h_real_ineq3
  have h_term1 : (9 * C1 * C1 * C2) ≤ D := by
    calc (9 * C1 * C1 * C2)
      ≤ ENNReal.ofReal (δ ^ (-7 : ℝ)) * C1 * C1 * C2 := by gcongr
    _ ≤ D := h_mul3
  have h_term2 : (81 * C1 * C1 * C1 * C2) ≤ D := by
    calc (81 * C1 * C1 * C1 * C2)
      ≤ ENNReal.ofReal (δ ^ (-7 : ℝ)) * C1 * C1 * C1 * C2 := by gcongr
    _ = D := h_mul4
  have h_term3 : (C1 * C2) ≤ D := by
    have h_eq : C1 * C2 = ENNReal.ofReal (δ ^ (-q_eff) * δ ^ (-q_ratio)) := by
      simp only [C1, C2]
      rw [← ENNReal.ofReal_mul h_pos1] <;> rfl
    rw [h_eq, hD_def]
    exact ENNReal.ofReal_le_ofReal h_real3
  have h_inner : max (81 * C1 * C1 * C1 * C2) (C1 * C2) ≤ D := max_le h_term2 h_term3
  have h_final : max (9 * C1 * C1 * C2) (max (81 * C1 * C1 * C1 * C2) (C1 * C2)) ≤ D :=
    max_le h_term1 h_inner
  exact le_trans h_main h_final

end Phase2Bsg
