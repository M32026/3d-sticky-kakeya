module

/-
  Direct geometric energy bound — bypasses A6Input entirely.

  Uses coarse_intersection_common_tubes_bound + energy_bound_from_common_tubes
  + t-energy dyadic decomposition to bound E directly.

  This feeds into common_tube_energy_extraction for A7.

  Whiteprint node: appendix_a_alternative / direct_geometric_energy

  Dependencies:
  - CommonCoarseTubesBound (coarse_intersection_common_tubes_bound)
  - EnergyBoundFromCommonTubes (energy_bound_from_common_tubes)
  - CommonTubeEnergyExtraction
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.CommonCoarseTubesBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.EnergyBoundFromCommonTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.EnergyBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CommonTubeEnergyExtraction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HeavySquaresToEnergy
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HCommonWiring
public import MyLeanRepo.OSWPrelude

@[expose] public section


open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Lagoon (squareCenter)
open DirecretisedFurstenbergEstimate.AppendixA
open DirecretisedFurstenbergEstimate.AppendixA3
open DirecretisedFurstenbergEstimate.Phase2
open DirecretisedFurstenbergEstimate.MainAppendix

namespace DirecretisedFurstenbergEstimate.AppendixA

noncomputable section

/-! ### t-energy bound with logarithmic factor

  For a t-dimensional set with ball-growth constant C, the t-energy is
  bounded by K · C · |S|² · log(3/Δ).

  Proof: dyadic shell decomposition. For each x, partition S\{x} into
  shells [2^k Δ, 2^{k+1} Δ). Shell k has ≤ C·(2^{k+1}Δ)^t·|S| points by
  ball-growth, each contributing ≤ (2^k Δ)^{-t}. Shell contribution ≤ C·2^t·|S|.
  Number of shells ≤ 4·log(3/Δ)+1.
-/

/-- Per-point t-energy bound via dyadic shells. -/
lemma point_t_energy_bound_with_log
    {Δ : ℝ} (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    {t : ℝ} (ht_pos : 0 < t)
    {C : ℝ} (hC_pos : 0 < C)
    {S : Finset Plane} {x : Plane} (hx : x ∈ S)
    (hS_sep : SeparatedAt Δ (S : Set Plane))
    (hS_bdd : ∀ p ∈ S, ‖p‖ ≤ 2)
    (h_ball : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((S.filter (fun y => dist y c ≤ r)).card : ℝ) ≤ C * r^t * (S.card : ℝ)) :
    pointEnergy t S x ≤
      (4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t * C * (S.card : ℝ) := by
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_log2_gt_two_thirds : (2 / 3 : ℝ) < Real.log 2 := by
    have h : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    linarith
  have h_inv_log2_lt : 1 / Real.log 2 < 3 / 2 := by
    have h1 : 0 < Real.log 2 := h_log2_pos
    calc 1 / Real.log 2 < 1 / (2 / 3 : ℝ) := by gcongr
      _ = 3 / 2 := by norm_num
  have h_log43_lt_one : Real.log (4 / 3 : ℝ) < 1 := by
    have h : Real.log (4 / 3 : ℝ) ≤ (4 / 3 : ℝ) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have h_log3Δ_gt_one : 1 < Real.log (3 / Δ) := by
    have h1 : (3 : ℝ) < 3 / Δ := by
      have h2 : 0 < Δ := hΔ_pos
      have h3 : Δ < 1 := hΔ_lt_one
      calc (3 : ℝ) = 3 / 1 := by norm_num
        _ < 3 / Δ := by gcongr
    have h2 : Real.log (3 / Δ) > Real.log 3 := Real.log_lt_log (by positivity) h1
    have h3 : (1.0986122885 : ℝ) < Real.log 3 := Real.log_three_gt_d9
    linarith

  let K : ℕ := Nat.ceil (Real.log (4 / Δ) / Real.log 2)
  have hK_ge : (K : ℝ) ≥ Real.log (4 / Δ) / Real.log 2 := Nat.le_ceil _
  have h_4Δ_gt_one : (1 : ℝ) < 4 / Δ := by
    have h2 : 0 < Δ := hΔ_pos
    have h3 : Δ < 1 := hΔ_lt_one
    have h4 : (4 : ℝ) / Δ > (4 : ℝ) / 1 := by gcongr
    have h5 : (4 : ℝ) / 1 = 4 := by norm_num
    rw [h5] at h4
    linarith
  have h_log4Δ_pos : 0 < Real.log (4 / Δ) := Real.log_pos h_4Δ_gt_one
  have hK_arg_nonneg : 0 ≤ Real.log (4 / Δ) / Real.log 2 := by
    apply div_nonneg
    · exact h_log4Δ_pos.le
    · exact h_log2_pos.le
  have hK_lt : (K : ℝ) < Real.log (4 / Δ) / Real.log 2 + 1 := Nat.ceil_lt_add_one hK_arg_nonneg

  have h2K_ge : (2 : ℝ)^K * Δ ≥ 4 := by
    have h1 : (K : ℝ) * Real.log 2 ≥ Real.log (4 / Δ) := by
      have h2 : (K : ℝ) ≥ Real.log (4 / Δ) / Real.log 2 := hK_ge
      have h_pos2 : 0 < Real.log 2 := h_log2_pos
      have h3 : (K : ℝ) * Real.log 2 ≥ (Real.log (4 / Δ) / Real.log 2) * Real.log 2 := mul_le_mul_of_nonneg_right h2 h_pos2.le
      have h4 : (Real.log (4 / Δ) / Real.log 2) * Real.log 2 = Real.log (4 / Δ) := by
        field_simp [h_pos2.ne'] <;> ring
      rw [h4] at h3
      exact h3
    have h4 : Real.log ((2 : ℝ)^K) ≥ Real.log (4 / Δ) := by
      have h5 : Real.log ((2 : ℝ)^K) = (K : ℝ) * Real.log 2 := by
        rw [Real.log_pow] <;> ring
      rw [h5]; exact h1
    have h7 : (2 : ℝ)^K ≥ 4 / Δ := by
      exact (Real.log_le_log_iff (by positivity) (by positivity)).mp h4
    have h8 : 0 < Δ := hΔ_pos
    have h9 : (2 : ℝ)^K * Δ ≥ (4 / Δ) * Δ := by gcongr
    have h10 : (4 / Δ) * Δ = 4 := by
      field_simp [h8.ne'] <;> ring
    rw [h10] at h9
    exact h9

  have hKp1_bound : ((K + 1 : ℕ) : ℝ) ≤ 4 * Real.log (3 / Δ) + 1 := by
    have h1 : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by simp
    rw [h1]
    have h2 : (K : ℝ) < Real.log (4 / Δ) / Real.log 2 + 1 := hK_lt
    have h3 : Real.log (4 / Δ) = Real.log (3 / Δ) + Real.log (4 / 3 : ℝ) := by
      have h4 : (4 / Δ) = (3 / Δ) * (4 / 3 : ℝ) := by ring
      rw [h4, Real.log_mul (by positivity) (by positivity)] <;> ring
    have h4 : Real.log (4 / Δ) / Real.log 2 < (3 / 2 : ℝ) * Real.log (4 / Δ) := by
      have h5 : 0 < Real.log (4 / Δ) := h_log4Δ_pos
      calc Real.log (4 / Δ) / Real.log 2
        = (1 / Real.log 2) * Real.log (4 / Δ) := by ring
        _ < (3 / 2 : ℝ) * Real.log (4 / Δ) := by gcongr
    have h12 : ((K + 1 : ℕ) : ℝ) < (3 / 2 : ℝ) * Real.log (4 / Δ) + 2 := by linarith
    have h13 : Real.log (4 / Δ) ≤ Real.log (3 / Δ) + 1 := by
      rw [h3]
      linarith [h_log43_lt_one]
    have h14 : (3 / 2 : ℝ) * Real.log (4 / Δ) + 2 ≤ (3 / 2 : ℝ) * (Real.log (3 / Δ) + 1) + 2 := by
      gcongr
    have h15 : (3 / 2 : ℝ) * (Real.log (3 / Δ) + 1) + 2 = (3 / 2 : ℝ) * Real.log (3 / Δ) + 7 / 2 := by ring
    have h16 : (3 / 2 : ℝ) * Real.log (3 / Δ) + 7 / 2 ≤ 4 * Real.log (3 / Δ) + 1 := by
      have h17 : 1 < Real.log (3 / Δ) := h_log3Δ_gt_one
      linarith
    linarith [h12, h13, h14, h15, h16]

  let f : Plane → ℕ := fun y => Nat.floor (Real.log (dist x y / Δ) / Real.log 2)

  have h_dist_geΔ : ∀ y ∈ S.erase x, Δ ≤ dist x y := by
    intro y hy
    have h_yS : y ∈ S := (Finset.mem_erase.mp hy).2
    have h_yne : y ≠ x := (Finset.mem_erase.mp hy).1
    have h_sep' : ∀ (a : Plane), a ∈ S → ∀ (b : Plane), b ∈ S → a ≠ b → Δ ≤ dist a b := by
      exact hS_sep
    have h : Δ ≤ dist y x := h_sep' y h_yS x hx h_yne
    have h_comm : dist y x = dist x y := dist_comm y x
    rw [h_comm] at h
    exact h

  have h_dist_le4 : ∀ y ∈ S.erase x, dist x y ≤ 4 := by
    intro y hy
    have h_yS : y ∈ S := (Finset.mem_erase.mp hy).2
    have h1 : ‖x‖ ≤ 2 := hS_bdd x hx
    have h2 : ‖y‖ ≤ 2 := hS_bdd y h_yS
    have h3 : dist x y ≤ ‖x‖ + ‖y‖ := dist_le_norm_add_norm _ _
    linarith

  have h_f_range : ∀ y ∈ S.erase x, f y ∈ Finset.range (K + 1) := by
    intro y hy
    have h2 : dist x y ≤ 4 := h_dist_le4 y hy
    have h4 : Real.log (dist x y / Δ) / Real.log 2 ≤ (K : ℝ) := by
      have h5 : dist x y / Δ ≤ 4 / Δ := by gcongr
      have h_pos_ratio : 0 < dist x y / Δ := by
        have h6 : Δ ≤ dist x y := h_dist_geΔ y hy
        have h7 : 0 < Δ := hΔ_pos
        have h8 : 1 ≤ dist x y / Δ := by
          calc (1 : ℝ) = Δ / Δ := by field_simp
            _ ≤ dist x y / Δ := by gcongr
        linarith
      have h6 : Real.log (dist x y / Δ) ≤ Real.log (4 / Δ) := Real.log_le_log h_pos_ratio h5
      have h7 : Real.log (dist x y / Δ) / Real.log 2 ≤ Real.log (4 / Δ) / Real.log 2 := by gcongr
      linarith [hK_ge]
    have h8 : f y ≤ K := Nat.floor_le_of_le h4
    exact Finset.mem_range.mpr (by omega)

  have h_shell_prop : ∀ (k : ℕ), ∀ y ∈ (S.erase x).filter (fun y => f y = k),
      (2 : ℝ)^k * Δ ≤ dist x y ∧ dist x y < (2 : ℝ)^(k + 1) * Δ := by
    intro k y hy
    have hfy : f y = k := (Finset.mem_filter.mp hy).2
    have h1 : Δ ≤ dist x y := h_dist_geΔ y (Finset.mem_filter.mp hy).1
    have h_ratio_ge_one : (1 : ℝ) ≤ dist x y / Δ := by
      have h2 : 0 < Δ := hΔ_pos
      calc (1 : ℝ) = Δ / Δ := by field_simp
        _ ≤ dist x y / Δ := by gcongr
    have h_pos : 0 < dist x y / Δ := by linarith
    have h_log_nonneg : 0 ≤ Real.log (dist x y / Δ) := by
      have h3 : (1 : ℝ) ≤ dist x y / Δ := h_ratio_ge_one
      have h4 : Real.log 1 ≤ Real.log (dist x y / Δ) := Real.log_le_log (by norm_num) h3
      simpa using h4
    have h_arg_nonneg : 0 ≤ Real.log (dist x y / Δ) / Real.log 2 := by
      apply div_nonneg
      · exact h_log_nonneg
      · exact h_log2_pos.le
    have h_floor1 : (f y : ℝ) ≤ Real.log (dist x y / Δ) / Real.log 2 := Nat.floor_le h_arg_nonneg
    have h_floor2 : Real.log (dist x y / Δ) / Real.log 2 < (f y : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [hfy] at h_floor1 h_floor2
    have h9 : (k : ℝ) * Real.log 2 ≤ Real.log (dist x y / Δ) := by
      have h : (k : ℝ) ≤ Real.log (dist x y / Δ) / Real.log 2 := h_floor1
      have h_pos2 : 0 < Real.log 2 := h_log2_pos
      have h' : (k : ℝ) * Real.log 2 ≤ (Real.log (dist x y / Δ) / Real.log 2) * Real.log 2 := mul_le_mul_of_nonneg_right h h_pos2.le
      have h'' : (Real.log (dist x y / Δ) / Real.log 2) * Real.log 2 = Real.log (dist x y / Δ) := by
        field_simp [h_pos2.ne'] <;> ring
      rw [h''] at h'
      exact h'
    have h10 : Real.log (dist x y / Δ) < ((k : ℝ) + 1) * Real.log 2 := by
      have h : Real.log (dist x y / Δ) / Real.log 2 < (k : ℝ) + 1 := h_floor2
      have h_pos2 : 0 < Real.log 2 := h_log2_pos
      have h' : (Real.log (dist x y / Δ) / Real.log 2) * Real.log 2 < ((k : ℝ) + 1) * Real.log 2 := mul_lt_mul_of_pos_right h h_pos2
      have h'' : (Real.log (dist x y / Δ) / Real.log 2) * Real.log 2 = Real.log (dist x y / Δ) := by
        field_simp [h_pos2.ne'] <;> ring
      rw [h''] at h'
      exact h'
    have h11 : Real.log ((2 : ℝ)^k) ≤ Real.log (dist x y / Δ) := by
      have h12 : Real.log ((2 : ℝ)^k) = (k : ℝ) * Real.log 2 := by
        rw [Real.log_pow]
        <;> simp
        <;> ring
      rw [h12]; exact h9
    have h13 : Real.log (dist x y / Δ) < Real.log ((2 : ℝ)^(k + 1)) := by
      have h14 : Real.log ((2 : ℝ)^(k + 1)) = ((k : ℝ) + 1) * Real.log 2 := by
        rw [Real.log_pow]
        <;> simp [Nat.cast_add]
        <;> ring
      rw [h14]; exact h10
    have h15 : (2 : ℝ)^k ≤ dist x y / Δ := (Real.log_le_log_iff (by positivity) (by positivity)).mp h11
    have h16 : dist x y / Δ < (2 : ℝ)^(k + 1) := (Real.log_lt_log_iff (by positivity) (by positivity)).mp h13
    exact ⟨by
      have h17 : (2 : ℝ)^k * Δ ≤ (dist x y / Δ) * Δ := by gcongr
      have h18 : (dist x y / Δ) * Δ = dist x y := by
        field_simp [hΔ_pos.ne'] <;> ring
      rw [h18] at h17
      exact h17,
    by
      have h17 : dist x y / Δ < (2 : ℝ)^(k + 1) := h16
      have h18 : (dist x y / Δ) * Δ < (2 : ℝ)^(k + 1) * Δ := by gcongr
      have h19 : (dist x y / Δ) * Δ = dist x y := by
        field_simp [hΔ_pos.ne'] <;> ring
      rw [h19] at h18
      exact h18⟩

  have h_shell_bound : ∀ (k : ℕ),
      (((S.erase x).filter (fun y => f y = k)).card : ℝ) ≤
      C * ((2 : ℝ)^(k + 1) * Δ)^t * (S.card : ℝ) := by
    intro k
    have h_subset : (S.erase x).filter (fun y => f y = k) ⊆
        S.filter (fun y => dist y x ≤ (2 : ℝ)^(k + 1) * Δ) := by
      intro y hy
      have h_yS : y ∈ S := (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).2
      have h_dist_lt : dist x y < (2 : ℝ)^(k + 1) * Δ := (h_shell_prop k y hy).2
      simp only [Finset.mem_filter]
      have h_dist_comm : dist y x = dist x y := dist_comm y x
      exact ⟨h_yS, le_of_lt (by rwa [h_dist_comm])⟩
    have h_r_geΔ : Δ ≤ (2 : ℝ)^(k + 1) * Δ := by
      have h1 : (1 : ℝ) ≤ (2 : ℝ)^(k + 1) := by
        have h2 : ∀ n : ℕ, (1 : ℝ) ≤ (2 : ℝ)^n := by
          intro n
          induction n with
          | zero => norm_num
          | succ n ih =>
            calc (1 : ℝ) ≤ (2 : ℝ)^n := ih
              _ ≤ (2 : ℝ)^n * 2 := by linarith
              _ = (2 : ℝ)^(n + 1) := by simp [pow_succ] <;> ring
        exact h2 (k + 1)
      nlinarith
    have h_card : ((S.filter (fun y => dist y x ≤ (2 : ℝ)^(k + 1) * Δ)).card : ℝ) ≤
        C * ((2 : ℝ)^(k + 1) * Δ)^t * (S.card : ℝ) :=
      h_ball x ((2 : ℝ)^(k + 1) * Δ) h_r_geΔ
    have h_card2 : (((S.erase x).filter (fun y => f y = k)).card : ℝ) ≤
        ((S.filter (fun y => dist y x ≤ (2 : ℝ)^(k + 1) * Δ)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card h_subset
    exact h_card2.trans h_card

  have h_shell_energy : ∀ (k : ℕ),
      ∑ y ∈ (S.erase x).filter (fun y => f y = k), Real.rpow (dist x y) (-t) ≤
      C * (2 : ℝ)^t * (S.card : ℝ) := by
    intro k
    have h1 : ∀ y ∈ (S.erase x).filter (fun y => f y = k),
        Real.rpow (dist x y) (-t) ≤ Real.rpow ((2 : ℝ)^k * Δ) (-t) := by
      intro y hy
      have h2 : (2 : ℝ)^k * Δ ≤ dist x y := (h_shell_prop k y hy).1
      have h_pos1 : 0 < (2 : ℝ)^k * Δ := by positivity
      have h_pos2 : 0 < dist x y := by linarith [h_dist_geΔ y (Finset.mem_filter.mp hy).1]
      have h3 : Real.rpow (dist x y) t ≥ Real.rpow ((2 : ℝ)^k * Δ) t :=
        Real.rpow_le_rpow (by linarith) h2 (by linarith)
      have h4 : Real.rpow (dist x y) (-t) = (Real.rpow (dist x y) t)⁻¹ :=
        Real.rpow_neg (by linarith) t
      have h5 : Real.rpow ((2 : ℝ)^k * Δ) (-t) = (Real.rpow ((2 : ℝ)^k * Δ) t)⁻¹ :=
        Real.rpow_neg (by linarith) t
      rw [h4, h5]
      have h6 : 0 < Real.rpow ((2 : ℝ)^k * Δ) t := Real.rpow_pos_of_pos h_pos1 t
      have h7 : 0 < Real.rpow (dist x y) t := Real.rpow_pos_of_pos h_pos2 t
      simpa [one_div] using one_div_le_one_div_of_le h6 h3
    have h4 : ∑ y ∈ (S.erase x).filter (fun y => f y = k), Real.rpow (dist x y) (-t) ≤
        (((S.erase x).filter (fun y => f y = k)).card : ℝ) * Real.rpow ((2 : ℝ)^k * Δ) (-t) := by
      calc _ ≤ ∑ y ∈ _, Real.rpow ((2 : ℝ)^k * Δ) (-t) := Finset.sum_le_sum h1
           _ = _ := by simp [Finset.sum_const] <;> ring
    have hB_nonneg : 0 ≤ Real.rpow ((2 : ℝ)^k * Δ) (-t) := Real.rpow_nonneg (by positivity) (-t)
    have h5 : (((S.erase x).filter (fun y => f y = k)).card : ℝ) * Real.rpow ((2 : ℝ)^k * Δ) (-t) ≤
        (C * ((2 : ℝ)^(k + 1) * Δ)^t * (S.card : ℝ)) * Real.rpow ((2 : ℝ)^k * Δ) (-t) :=
      mul_le_mul_of_nonneg_right (h_shell_bound k) hB_nonneg
    have h6 : (C * ((2 : ℝ)^(k + 1) * Δ)^t * (S.card : ℝ)) * Real.rpow ((2 : ℝ)^k * Δ) (-t) =
        C * (2 : ℝ)^t * (S.card : ℝ) := by
      have h_pos1 : 0 < (2 : ℝ)^(k + 1) * Δ := by positivity
      have h_pos2 : 0 < (2 : ℝ)^k * Δ := by positivity
      have h7 : (((2 : ℝ)^(k + 1) * Δ)^t) * (((2 : ℝ)^k * Δ)^(-t)) = (2 : ℝ)^t := by
        have h_neg : (((2 : ℝ)^k * Δ)^(-t)) = (((2 : ℝ)^k * Δ)^t)⁻¹ := Real.rpow_neg (by positivity) t
        rw [h_neg]
        have h_eq : (((2 : ℝ)^(k + 1) * Δ)^t) * (((2 : ℝ)^k * Δ)^t)⁻¹ =
            (((2 : ℝ)^(k + 1) * Δ)^t) / (((2 : ℝ)^k * Δ)^t) := by ring
        rw [h_eq]
        have h_div : (((2 : ℝ)^(k + 1) * Δ)^t) / (((2 : ℝ)^k * Δ)^t) =
            (((2 : ℝ)^(k + 1) * Δ) / ((2 : ℝ)^k * Δ))^t := by
          rw [← Real.div_rpow (by positivity) (by positivity) t]
        rw [h_div]
        have h_ratio : ((2 : ℝ)^(k + 1) * Δ) / ((2 : ℝ)^k * Δ) = (2 : ℝ) := by
          field_simp [h_pos2.ne'] <;> ring
        rw [h_ratio] <;> norm_num
      have h_goal : (C * ((2 : ℝ)^(k + 1) * Δ)^t * (S.card : ℝ)) * Real.rpow ((2 : ℝ)^k * Δ) (-t) =
          C * ((((2 : ℝ)^(k + 1) * Δ)^t) * (((2 : ℝ)^k * Δ)^(-t))) * (S.card : ℝ) := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      rw [h_goal, h7] <;> ring
    rw [h6] at h5
    exact h4.trans h5

  have h_disjoint : ∀ k1 k2 : ℕ, k1 ≠ k2 →
      Disjoint ((S.erase x).filter (fun y => f y = k1))
        ((S.erase x).filter (fun y => f y = k2)) := by
    intro k1 k2 hne
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    have h1 : f y = k1 := (Finset.mem_filter.mp hy1).2
    have h2 : f y = k2 := (Finset.mem_filter.mp hy2).2
    rw [h1] at h2
    exact hne h2

  have h_union : (S.erase x) =
      Finset.biUnion (Finset.range (K + 1)) (fun k => (S.erase x).filter (fun y => f y = k)) := by
    ext y
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro hy
      have hfy : f y ∈ Finset.range (K + 1) := h_f_range y hy
      exact ⟨f y, hfy, hy, rfl⟩
    · rintro ⟨k, _, hy, _⟩
      exact hy

  have h_disjoint' : Set.PairwiseDisjoint (Finset.range (K + 1) : Set ℕ) (fun k => (S.erase x).filter (fun y => f y = k)) := by
    intro k1 _ k2 _ hne
    exact h_disjoint k1 k2 hne

  dsimp only [pointEnergy]
  rw [h_union, Finset.sum_biUnion h_disjoint']
  have h_sum : ∑ k ∈ Finset.range (K + 1), ∑ y ∈ (S.erase x).filter (fun y => f y = k), Real.rpow (dist x y) (-t) ≤
      ∑ k ∈ Finset.range (K + 1), C * (2 : ℝ)^t * (S.card : ℝ) :=
    Finset.sum_le_sum (fun k _ => h_shell_energy k)
  have h_sum2 : ∑ k ∈ Finset.range (K + 1), C * (2 : ℝ)^t * (S.card : ℝ) =
      ((K + 1 : ℕ) : ℝ) * C * (2 : ℝ)^t * (S.card : ℝ) := by
    have h_card : (Finset.range (K + 1)).card = K + 1 := by simp
    have h_sum : ∑ k ∈ Finset.range (K + 1), C * (2 : ℝ)^t * (S.card : ℝ) =
        ((Finset.range (K + 1)).card : ℝ) * (C * (2 : ℝ)^t * (S.card : ℝ)) := by
      rw [Finset.sum_const]
      <;> ring
    rw [h_sum, h_card]
    <;> simp [Nat.cast_add] <;> ring
  rw [h_sum2] at h_sum
  have h_final : ((K + 1 : ℕ) : ℝ) * C * (2 : ℝ)^t * (S.card : ℝ) ≤
      (4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t * C * (S.card : ℝ) := by
    have h11 : ((K + 1 : ℕ) : ℝ) * (2 : ℝ)^t ≤ (4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t := by
      have h12 : ((K + 1 : ℕ) : ℝ) ≤ 4 * Real.log (3 / Δ) + 1 := hKp1_bound
      have h13 : (2 : ℝ)^t ≤ (4 : ℝ)^t := by
        gcongr <;> norm_num <;> linarith
      gcongr
    calc ((K + 1 : ℕ) : ℝ) * C * (2 : ℝ)^t * (S.card : ℝ)
      = C * (S.card : ℝ) * (((K + 1 : ℕ) : ℝ) * (2 : ℝ)^t) := by ring
    _ ≤ C * (S.card : ℝ) * ((4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t) := by
      have h_nonneg : 0 ≤ C * (S.card : ℝ) := mul_nonneg hC_pos.le (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left h11 h_nonneg
    _ = (4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t * C * (S.card : ℝ) := by ring
  exact h_sum.trans h_final

/-- Dyadic shell decomposition: bound t-energy of a separated set with ball-growth. -/
lemma t_energy_bound_with_log
    {Δ : ℝ} (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    {t : ℝ} (ht_pos : 0 < t)
    {C : ℝ} (hC_pos : 0 < C)
    {S : Finset Plane}
    (hS_sep : SeparatedAt Δ (S : Set Plane))
    (hS_bdd : ∀ p ∈ S, ‖p‖ ≤ 2)
    (h_ball : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((S.filter (fun y => dist y c ≤ r)).card : ℝ) ≤ C * r^t * (S.card : ℝ)) :
    pairEnergy t S ≤
      (4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t * C * (S.card : ℝ)^2 := by
  by_cases hS_empty : S = ∅
  · rw [hS_empty]
    simp [pairEnergy, pointEnergy]
    <;> positivity
  have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
  have h_main : ∀ x ∈ S,
      pointEnergy t S x ≤
        (4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t * C * (S.card : ℝ) := by
    intro x hx
    exact point_t_energy_bound_with_log hΔ_pos hΔ_lt_one ht_pos hC_pos hx hS_sep hS_bdd h_ball
  have h_total : pairEnergy t S ≤
      ∑ x ∈ S, ((4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t * C * (S.card : ℝ)) := by
    dsimp only [pairEnergy]
    exact Finset.sum_le_sum h_main
  have h_sum_const : ∑ x ∈ S, ((4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t * C * (S.card : ℝ)) =
      (S.card : ℝ) * ((4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t * C * (S.card : ℝ)) := by
    simp [Finset.sum_const] <;> ring
  rw [h_sum_const] at h_total
  have h_final : (S.card : ℝ) * ((4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t * C * (S.card : ℝ)) =
      (4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t * C * (S.card : ℝ)^2 := by ring
  rw [h_final] at h_total
  exact h_total

/-! ### Direct geometric energy data construction

  Given Qset with C_pi families, construct centers, C_global, fiber,
  and bound the total pairEnergy.
-/

/-- Direct geometric energy data: produces fiber, I, E, L for extraction. -/
lemma direct_geometric_energy_data
    {Δ δ s t ε : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2) (hε_pos : 0 < ε)
    -- Qset
    (Qset : Finset (CoarseSquare Δ))
    (hQset_nonempty : Qset.Nonempty)
    (hQset_bdd : ∀ p ∈ Qset.image (squareCenter Δ), ‖p‖ ≤ 2)
    (hQset_le_3 : ∀ (p1 : Plane) (hp1 : p1 ∈ Qset.image (squareCenter Δ))
      (p2 : Plane) (hp2 : p2 ∈ Qset.image (squareCenter Δ)), dist p1 p2 ≤ 3)
    -- Ball growth for Qset centers
    (C_Qset : ℝ) (hC_Qset_pos : 0 < C_Qset)
    (hQset_ball : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((Qset.image (squareCenter Δ)).filter (fun y => dist y c ≤ r)).card ≤
        C_Qset * r^t * (Qset.image (squareCenter Δ)).card)
    -- C_pi per square
    (C_pi : CoarseSquare Δ → Finset CoarseTube)
    (C_T M k : ℝ)
    (hC_T_pos : 0 < C_T) (hM_pos : 0 < M) (hk : 1 ≤ k)
    (hC_pi_sset : ∀ Q ∈ Qset, IsDeltaSSet Δ s C_T (C_pi Q : Set CoarseTube))
    (hC_pi_sep : ∀ Q ∈ Qset, SeparatedAt Δ (C_pi Q : Set CoarseTube))
    (hC_pi_card : ∀ Q ∈ Qset, (C_pi Q).card ≤ M)
    (hC_pi_near : ∀ Q ∈ Qset, ∀ T ∈ C_pi Q,
      squareCenter Δ Q ∈ Metric.cthickening (k * Δ) (T.1 : Set EuclideanPlane))
    (hC_pi_nonempty : ∀ Q ∈ Qset, (C_pi Q).Nonempty)
    -- Intersection constant
    (C_int : ℝ)
    (hC_int_eq : C_int = (affineLine_packing_constant : ℝ) * C_T * ((800 * k) : ℝ)^s * M * Real.rpow Δ s)
    :
    ∃ (E I L : ℝ) (centers : Finset Plane)
      (C_global : Finset CoarseTube) (fiber : CoarseTube → Finset Plane),
      0 < I ∧ 0 ≤ E ∧ 0 < L ∧
      SeparatedAt Δ (centers : Set Plane) ∧
      (∀ T ∈ C_global, fiber T ⊆ centers) ∧
      (C_global.card : ℝ) ≤ L ∧
      I = ∑ T ∈ C_global, ((fiber T).card : ℝ) ∧
      centers = Qset.image (squareCenter Δ) ∧
      C_global = Qset.biUnion C_pi ∧
      E = ∑ T ∈ C_global, pairEnergy (t - s) (fiber T) ∧
      (∀ T, fiber T = (Qset.filter (fun Q => T ∈ C_pi Q)).image (squareCenter Δ)) ∧
      E ≤ C_int * (4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t * C_Qset * (Qset.card : ℝ)^2 := by
  classical
  let u : ℝ := t - s
  have hu_pos : 0 < u := by linarith
  let centers : Finset Plane := Qset.image (squareCenter Δ)
  let C_global : Finset CoarseTube := Qset.biUnion C_pi
  let fiber (T : CoarseTube) : Finset Plane :=
    (Qset.filter (fun Q => T ∈ C_pi Q)).image (squareCenter Δ)
  let I : ℝ := ∑ Q ∈ Qset, (C_pi Q).card
  let L : ℝ := (C_global.card : ℝ)
  let E : ℝ := ∑ T ∈ C_global, pairEnergy u (fiber T)

  have h_inj : Function.Injective (squareCenter Δ) := Phase2.squareCenter_injective hΔ_pos

  have hI_pos : 0 < I := by
    dsimp only [I]
    apply Finset.sum_pos
    · intro Q hQ
      have h : (C_pi Q).Nonempty := hC_pi_nonempty Q hQ
      have h' : 0 < (C_pi Q).card := Finset.card_pos.mpr h
      exact_mod_cast h'
    · exact hQset_nonempty

  have hcenters_sep : SeparatedAt Δ (centers : Set Plane) :=
    squareCenters_separated hΔ_pos

  have hfiber : ∀ T ∈ C_global, fiber T ⊆ centers := by
    intro T _
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨Q, hQ, rfl⟩
    have hQ' : Q ∈ Qset := (Finset.mem_filter.mp hQ).1
    exact Finset.mem_image.mpr ⟨Q, hQ', rfl⟩

  have hcard : (C_global.card : ℝ) ≤ L := by simp [L]

  have hL_pos : 0 < L := by
    dsimp only [L]
    rcases hQset_nonempty with ⟨Q, hQ⟩
    rcases hC_pi_nonempty Q hQ with ⟨T, hT⟩
    have h : T ∈ C_global := Finset.mem_biUnion.mpr ⟨Q, hQ, hT⟩
    exact_mod_cast Finset.card_pos.mpr ⟨T, h⟩

  -- Double counting: I = Σ_T |fiber T|
  have h_fiber_card : ∀ T ∈ C_global, (fiber T).card = (Qset.filter (fun Q => T ∈ C_pi Q)).card := by
    intro T _
    rw [Finset.card_image_of_injective _ h_inj]

  let f : CoarseSquare Δ → CoarseTube → ℝ := fun Q T => if T ∈ C_pi Q then 1 else 0
  have h1 : ∀ Q ∈ Qset, ((C_pi Q).card : ℝ) = ∑ T ∈ C_global, f Q T := by
    intro Q hQ
    have h3 : C_pi Q ⊆ C_global := by
      intro T hT
      exact Finset.mem_biUnion.mpr ⟨Q, hQ, hT⟩
    have h2 : ∑ T ∈ C_global, f Q T = ((C_pi Q).card : ℝ) := by
      have h4 : ∑ T ∈ C_global, f Q T = ∑ T ∈ C_global.filter (fun T => T ∈ C_pi Q), (1 : ℝ) := by
        rw [Finset.sum_ite] <;> simp [f] <;> rfl
      rw [h4]
      have h5 : C_global.filter (fun T => T ∈ C_pi Q) = C_pi Q := by
        ext T; simp [h3] <;> tauto
      rw [h5]
      <;> simp
    exact h2.symm
  have h4 : ∀ T ∈ C_global, ((Qset.filter (fun Q => T ∈ C_pi Q)).card : ℝ) = ∑ Q ∈ Qset, f Q T := by
    intro T hT
    have h5 : ∑ Q ∈ Qset, f Q T = ∑ Q ∈ Qset.filter (fun Q => T ∈ C_pi Q), (1 : ℝ) := by
      rw [Finset.sum_ite] <;> simp [f] <;> rfl
    rw [h5]
    <;> simp
  have hincidence_eq : I = ∑ T ∈ C_global, ((fiber T).card : ℝ) := by
    dsimp only [I]
    calc (∑ Q ∈ Qset, (C_pi Q).card : ℝ)
      = ∑ Q ∈ Qset, ∑ T ∈ C_global, f Q T :=
        Finset.sum_congr rfl (fun Q hQ => h1 Q hQ)
    _ = ∑ T ∈ C_global, ∑ Q ∈ Qset, f Q T := by rw [Finset.sum_comm]
    _ = ∑ T ∈ C_global, ((Qset.filter (fun Q => T ∈ C_pi Q)).card : ℝ) :=
      Finset.sum_congr rfl (fun T hT => (h4 T hT).symm)
    _ = ∑ T ∈ C_global, ((fiber T).card : ℝ) :=
      Finset.sum_congr rfl (fun T hT => by rw [h_fiber_card T hT])

  -- Intersection bound for common tubes
  have hC_int_pos : 0 < C_int := by
    rw [hC_int_eq]
    have h1 : 0 < (affineLine_packing_constant : ℝ) := by exact_mod_cast affineLine_packing_constant_pos
    have h2 : 0 < C_T := hC_T_pos
    have h3 : 0 < ((800 * k) : ℝ) := by positivity
    have h4 : 0 < Real.rpow ((800 * k) : ℝ) s := Real.rpow_pos_of_pos h3 s
    have h5 : 0 < M := hM_pos
    have h6 : 0 < Real.rpow Δ s := Real.rpow_pos_of_pos hΔ_pos s
    positivity

  have h_common : ∀ (p1 : Plane) (hp1 : p1 ∈ centers) (p2 : Plane) (hp2 : p2 ∈ centers),
      p1 ≠ p2 →
        ((C_global.filter (fun T => p1 ∈ fiber T ∧ p2 ∈ fiber T)).card : ℝ) ≤
          C_int * Real.rpow (dist p1 p2) (-s) := by
    intro p1 hp1 p2 hp2 hne
    rcases Finset.mem_image.mp hp1 with ⟨Q1, hQ1, rfl⟩
    rcases Finset.mem_image.mp hp2 with ⟨Q2, hQ2, rfl⟩
    have hQne : Q1 ≠ Q2 := by intro h; apply hne; rw [h]
    have hd : Δ ≤ dist (squareCenter Δ Q1) (squareCenter Δ Q2) :=
      hcenters_sep hp1 hp2 hne
    have hr_le_3 : dist (squareCenter Δ Q1) (squareCenter Δ Q2) ≤ 3 :=
      hQset_le_3 (squareCenter Δ Q1) hp1 (squareCenter Δ Q2) hp2
    have hQ1_bound : ‖squareCenter Δ Q1‖ ≤ 2 := hQset_bdd (squareCenter Δ Q1) hp1
    have hQ2_bound : ‖squareCenter Δ Q2‖ ≤ 2 := hQset_bdd (squareCenter Δ Q2) hp2
    have h_fiber_iff : ∀ (Q : CoarseSquare Δ), Q ∈ Qset → ∀ (T : CoarseTube),
        squareCenter Δ Q ∈ fiber T ↔ T ∈ C_pi Q := by
      intro Q hQ T
      constructor
      · intro h
        rcases Finset.mem_image.mp h with ⟨Q', hQ', h_eq⟩
        have hQ'eq : Q' = Q := h_inj h_eq
        rw [hQ'eq] at hQ'
        exact (Finset.mem_filter.mp hQ').2
      · intro hT
        exact Finset.mem_image.mpr ⟨Q, Finset.mem_filter.mpr ⟨hQ, hT⟩, rfl⟩
    have h_eq_filter : (C_global.filter (fun T =>
        (squareCenter Δ Q1) ∈ fiber T ∧ (squareCenter Δ Q2) ∈ fiber T)) =
        C_pi Q1 ∩ C_pi Q2 := by
      ext T
      have h1 : (squareCenter Δ Q1) ∈ fiber T ↔ T ∈ C_pi Q1 := h_fiber_iff Q1 hQ1 T
      have h2 : (squareCenter Δ Q2) ∈ fiber T ↔ T ∈ C_pi Q2 := h_fiber_iff Q2 hQ2 T
      simp only [Finset.mem_filter, Finset.mem_inter]
      rw [h1, h2]
      constructor
      · rintro ⟨hT_global, hT1, hT2⟩
        exact ⟨hT1, hT2⟩
      · rintro ⟨hT1, hT2⟩
        have hT_global : T ∈ C_global := Finset.mem_biUnion.mpr ⟨Q1, hQ1, hT1⟩
        exact ⟨hT_global, hT1, hT2⟩
    rw [h_eq_filter]
    have h_dist_pos : 0 < dist (squareCenter Δ Q1) (squareCenter Δ Q2) := by
      apply dist_pos.mpr
      intro h
      exact hne h
    have h_bound := coarse_intersection_common_tubes_bound
      hk hΔ_pos hs hC_T_pos hM_pos
      (hQ_bound := hQ1_bound) (hR_bound := hQ2_bound)
      hd hr_le_3 C_pi
      (hC_pi_sset Q1 hQ1)
      (hC_pi_near Q1 hQ1)
      (hC_pi_card Q1 hQ1)
      (hC_pi_sep Q1 hQ1)
      (hC_pi_near Q2 hQ2)
    have h_rpow_eq : ((Δ / dist (squareCenter Δ Q1) (squareCenter Δ Q2)) ^ s) =
        Real.rpow Δ s * Real.rpow (dist (squareCenter Δ Q1) (squareCenter Δ Q2)) (-s) := by
      have h_pos1 : 0 < Δ := hΔ_pos
      have h_pos2 : 0 < dist (squareCenter Δ Q1) (squareCenter Δ Q2) := h_dist_pos
      have h1 : ((Δ / dist (squareCenter Δ Q1) (squareCenter Δ Q2)) ^ s) =
          Real.rpow Δ s / Real.rpow (dist (squareCenter Δ Q1) (squareCenter Δ Q2)) s :=
        by exact Real.div_rpow (by linarith) (by linarith) s
      rw [h1]
      have h2 : Real.rpow (dist (squareCenter Δ Q1) (squareCenter Δ Q2)) (-s) =
          (Real.rpow (dist (squareCenter Δ Q1) (squareCenter Δ Q2)) s)⁻¹ :=
        Real.rpow_neg h_pos2.le s
      rw [h2]
      <;> ring
    rw [h_rpow_eq] at h_bound
    rw [hC_int_eq]
    have h_final : (affineLine_packing_constant : ℝ) * C_T * ((800 * k) : ℝ)^s * M *
        (Real.rpow Δ s * Real.rpow (dist (squareCenter Δ Q1) (squareCenter Δ Q2)) (-s)) =
      (affineLine_packing_constant : ℝ) * C_T * ((800 * k) : ℝ)^s * M * Real.rpow Δ s *
        Real.rpow (dist (squareCenter Δ Q1) (squareCenter Δ Q2)) (-s) := by ring
    rw [h_final] at h_bound
    exact h_bound

  -- Energy bound via energy_bound_from_common_tubes
  have hE_bound : E ≤ C_int * pairEnergy t centers :=
    energy_bound_from_common_tubes
      (show 0 ≤ s from by linarith)
      (show 0 ≤ t from by linarith)
      (show s ≤ t from by linarith)
      (show 0 ≤ C_int from hC_int_pos.le)
      centers C_global fiber hfiber h_common

  -- t-energy bound
  have h_t_energy : pairEnergy t centers ≤
      (4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t * C_Qset * (centers.card : ℝ)^2 :=
    t_energy_bound_with_log hΔ_pos (by linarith) (by linarith) hC_Qset_pos
      hcenters_sep hQset_bdd hQset_ball

  have hcenters_card : centers.card = Qset.card := by
    rw [Finset.card_image_of_injective _ h_inj]

  have hE_final : E ≤ C_int * (4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t * C_Qset * (Qset.card : ℝ)^2 := by
    calc E
      ≤ C_int * pairEnergy t centers := hE_bound
    _ ≤ C_int * ((4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t * C_Qset * (centers.card : ℝ)^2) := by
        exact mul_le_mul_of_nonneg_left h_t_energy hC_int_pos.le
    _ = C_int * (4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t * C_Qset * (Qset.card : ℝ)^2 := by
        rw [hcenters_card] <;> ring

  have hE_nonneg : 0 ≤ E := by
    dsimp only [E]
    apply Finset.sum_nonneg
    intro T _
    dsimp only [pairEnergy]
    apply Finset.sum_nonneg
    intro x _
    apply Finset.sum_nonneg
    intro y _
    exact Real.rpow_nonneg dist_nonneg _

  have hE_def : E = ∑ T ∈ C_global, pairEnergy (t - s) (fiber T) := by rfl
  have hcenters_eq : centers = Qset.image (squareCenter Δ) := by rfl
  have hCglobal_eq : C_global = Qset.biUnion C_pi := by rfl
  have hfiber_eq : ∀ T, fiber T = (Qset.filter (fun Q => T ∈ C_pi Q)).image (squareCenter Δ) := by
    intro T; rfl
  exact ⟨E, I, L, centers, C_global, fiber,
    hI_pos, hE_nonneg, hL_pos, hcenters_sep, hfiber, hcard,
    hincidence_eq, hcenters_eq, hCglobal_eq, hE_def, hfiber_eq, hE_final⟩

/-- Direct A7 extraction: combines direct geometric energy with common tube extraction.

    Takes Qset + per-square C_pi data (all available from A4 directly, no A5 needed).
    Returns T0, Q0_phys, E, I, L with:
    - Q0_phys ⊆ centers (square centers)
    - |Q0_phys| ≥ I/(4L)
    - Q0_phys is a (Δ, t-s, C_sset)-set
    - Pointwise energy bound 4E/I and ball growth
-/
lemma a7_direct_extraction
    {Δ δ s t ε : ℝ} (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2) (hε_pos : 0 < ε)
    (Qset : Finset (CoarseSquare Δ)) (hQset_nonempty : Qset.Nonempty)
    (hQset_bdd : ∀ p ∈ Qset.image (squareCenter Δ), ‖p‖ ≤ 2)
    (hQset_le_3 : ∀ (p1 : Plane) (hp1 : p1 ∈ Qset.image (squareCenter Δ))
      (p2 : Plane) (hp2 : p2 ∈ Qset.image (squareCenter Δ)), dist p1 p2 ≤ 3)
    (C_Qset : ℝ) (hC_Qset_pos : 0 < C_Qset)
    (hQset_ball : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((Qset.image (squareCenter Δ)).filter (fun y => dist y c ≤ r)).card ≤
        C_Qset * r^t * (Qset.image (squareCenter Δ)).card)
    (C_pi : CoarseSquare Δ → Finset CoarseTube)
    (C_T M k : ℝ)
    (hC_T_pos : 0 < C_T) (hM_pos : 0 < M) (hk : 1 ≤ k)
    (hC_pi_sset : ∀ Q ∈ Qset, IsDeltaSSet Δ s C_T (C_pi Q : Set CoarseTube))
    (hC_pi_sep : ∀ Q ∈ Qset, SeparatedAt Δ (C_pi Q : Set CoarseTube))
    (hC_pi_card : ∀ Q ∈ Qset, (C_pi Q).card ≤ M)
    (hC_pi_near : ∀ Q ∈ Qset, ∀ T ∈ C_pi Q,
      squareCenter Δ Q ∈ Metric.cthickening (k * Δ) (T.1 : Set EuclideanPlane))
    (hC_pi_nonempty : ∀ Q ∈ Qset, (C_pi Q).Nonempty)
    (C_int : ℝ)
    (hC_int_eq : C_int = (affineLine_packing_constant : ℝ) * C_T * ((800 * k) : ℝ)^s * M * Real.rpow Δ s) :
    ∃ (T0 : CoarseTube) (Q0_phys centers : Finset Plane)
      (C_global : Finset CoarseTube) (C_sset E I L : ℝ),
      T0 ∈ C_global ∧
      Q0_phys.Nonempty ∧
      Q0_phys ⊆ centers ∧
      centers = Qset.image (squareCenter Δ) ∧
      C_global = Qset.biUnion C_pi ∧
      IsDeltaSSet Δ (t - s) C_sset (Q0_phys : Set Plane) ∧
      I / (4 * L) ≤ (Q0_phys.card : ℝ) ∧
      E ≤ C_int * (4 * Real.log (3 / Δ) + 1) * (4 : ℝ)^t * C_Qset * (Qset.card : ℝ)^2 := by
  classical
  let u : ℝ := t - s
  have hu_pos : 0 < u := by linarith

  have h_data := direct_geometric_energy_data (δ := δ)
    hΔ_pos hΔ_lt_half hs hs1 hst ht2 hε_pos
    Qset hQset_nonempty hQset_bdd hQset_le_3 C_Qset hC_Qset_pos hQset_ball
    C_pi C_T M k hC_T_pos hM_pos hk
    hC_pi_sset hC_pi_sep hC_pi_card hC_pi_near hC_pi_nonempty
    C_int hC_int_eq

  rcases h_data with ⟨E, I, L, centers, C_global, fiber,
    hI_pos, hE_nonneg, hL_pos, hcenters_sep, hfiber, hcard,
    hincidence_eq, hcenters_eq, hCglobal_eq, hE_def, hfiber_eq, hE_bound⟩

  have hincidence : I ≤ ∑ T ∈ C_global, ((fiber T).card : ℝ) := by
    rw [hincidence_eq]

  have henergy : ∑ T ∈ C_global, pairEnergy u (fiber T) ≤ E := by
    rw [hE_def]

  have h_main := common_tube_energy_extraction
    (δ := Δ) (u := u) (I := I) (E := E) (L := L)
    (Q := centers) (𝒯 := C_global) (fiber := fiber)
    hΔ_pos hu_pos hI_pos hE_nonneg hL_pos hcenters_sep hfiber hcard hincidence henergy

  rcases h_main with ⟨T0, hT0_in, Q0_phys, hQ0_sub, hQ0_card, hPE_bound, h_growth⟩

  let C_sset : ℝ := (2 : ℝ)^u * (Real.rpow Δ (-u) + 4 * E / I)

  have h_sset_result := energy_extraction_to_sset
    (Q := centers) (𝒯 := C_global) (fiber := fiber)
    hΔ_pos hu_pos hI_pos hE_nonneg hL_pos
    T0 hT0_in Q0_phys hQ0_sub hQ0_card h_growth

  have hQ0_nonempty : Q0_phys.Nonempty := by
    by_contra h
    have h' : Q0_phys.card = 0 := by simpa [Finset.not_nonempty_iff_eq_empty] using h
    rw [h'] at hQ0_card
    have h_contra : (I : ℝ) ≤ 0 := by simpa using hQ0_card
    exact False.elim (not_le.mpr hI_pos h_contra)

  have hQ0_sub_centers : Q0_phys ⊆ centers := by
    exact hQ0_sub.trans (hfiber T0 hT0_in)

  exact ⟨T0, Q0_phys, centers, C_global, C_sset, E, I, L,
    hT0_in, hQ0_nonempty, hQ0_sub_centers, hcenters_eq, hCglobal_eq,
    h_sset_result.1, h_sset_result.2, hE_bound⟩

end
end DirecretisedFurstenbergEstimate.AppendixA
