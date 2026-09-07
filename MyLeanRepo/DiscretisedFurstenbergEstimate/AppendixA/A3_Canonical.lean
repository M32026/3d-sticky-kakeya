module

/-
  Appendix A, Step A3: Uniformize local outputs via dyadic pigeonholing.

  Given A2's per-square outputs (K_Q, H_Q, |C_Q|), partition Qset into
  dyadic bins and select the largest bin. Output uniform parameters and
  preserve the S-set property with polylogarithmic loss absorbed into
  the ε-budget.

  Whiteprint node: appendix_a_alternative / A3
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineParams
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HeavySquareRefinement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.CommonCoarseTubesBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.SimpleIncidence
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A3_CardBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.AppendixA3

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Lagoon (squareCenter point_in_square_close_to_center)
open DirecretisedFurstenbergEstimate.Phase2 (squareCenter_injective)

/-! ========================================================================
   A3 uses canonical types from Interfaces.lean
   ======================================================================== -/

open DirecretisedFurstenbergEstimate.AppendixA

/-! ========================================================================
   Helper lemmas
   ======================================================================== -/

/-- Dyadic bin count bound: number of parameter bins is polylog in 1/Δ. -/
lemma a3_bin_count_bound {Δ ε s t : ℝ} (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hΔ_small : 1000 * (Real.log (1 / Δ) + 1)^3 ≤ Real.rpow Δ (-ε))
    {Qset_all : Finset (CoarseSquare Δ)}
    {K H C : CoarseSquare Δ → ℝ}
    (hK_lower : ∀ Q ∈ Qset_all, Real.rpow Δ (2 * ε) ≤ K Q)
    (hK_upper : ∀ Q ∈ Qset_all, K Q ≤ Real.rpow Δ (-ε))
    (hH_lower : ∀ Q ∈ Qset_all, 2 * Real.rpow Δ (-(s + t)) ≤ H Q)
    (hH_upper : ∀ Q ∈ Qset_all, H Q ≤ Real.rpow Δ (-t - s - ε))
    (hC_lower : ∀ Q ∈ Qset_all, 2 * Real.rpow Δ (-s + ε) ≤ C Q)
    (hC_upper : ∀ Q ∈ Qset_all, C Q ≤ Real.rpow Δ (-s - ε))
    (binTriple : CoarseSquare Δ → ℤ × ℤ × ℤ)
    (hbin : ∀ Q ∈ Qset_all,
      binTriple Q = (Int.floor (Real.logb 2 (K Q)), Int.floor (Real.logb 2 (H Q)), Int.floor (Real.logb 2 (C Q)))) :
    (Qset_all.image binTriple).card ≤ 1000 * (Real.log (1 / Δ) + 1)^3 := by
  let L : ℝ := Real.logb 2 (1 / Δ)
  have h_base : (1 : ℝ) < 2 := by norm_num
  have hL_one : 1 ≤ L := by
    have h1 : (2 : ℝ) ≤ 1 / Δ := by
      have h2 : 0 < Δ := hΔ_pos
      have h3 : 2 * Δ < 1 := by linarith
      calc (2 : ℝ) = (2 * Δ) / Δ := by field_simp [h2.ne'] <;> ring
        _ ≤ 1 / Δ := by gcongr
    have hpos1 : (0 : ℝ) < 2 := by norm_num
    have hpos2 : 0 < (1 / Δ) := by positivity
    have h_iff : Real.logb 2 2 ≤ Real.logb 2 (1 / Δ) ↔ (2 : ℝ) ≤ 1 / Δ :=
      Real.logb_le_logb h_base hpos1 hpos2
    have h2 : Real.logb 2 2 ≤ L := h_iff.mpr h1
    have h3 : Real.logb 2 2 = 1 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    linarith
  have h_logb_negL : Real.logb 2 Δ = -L := by
    have h4 : L = Real.logb 2 (1 / Δ) := rfl
    have h5 : Real.logb 2 (1 / Δ) = -Real.logb 2 Δ := by
      rw [Real.logb_div (by norm_num) (by positivity)]
      <;> simp [Real.logb_one] <;> ring
    linarith
  have h_logb_rpow : ∀ (y : ℝ), Real.logb 2 (Real.rpow Δ y) = -y * L := by
    intro y
    have h1 : Real.logb 2 (Real.rpow Δ y) = Real.log (Real.rpow Δ y) / Real.log 2 := by rfl
    rw [h1]
    have h2 : Real.log (Real.rpow Δ y) = y * Real.log Δ := by
      simpa using Real.log_rpow hΔ_pos y
    rw [h2]
    have h3 : y * Real.log Δ / Real.log 2 = y * (Real.log Δ / Real.log 2) := by ring
    rw [h3]
    have h4 : Real.log Δ / Real.log 2 = Real.logb 2 Δ := by rfl
    rw [h4, h_logb_negL] <;> ring
  have h_logb_2rpow : ∀ (y : ℝ), Real.logb 2 (2 * Real.rpow Δ y) = 1 - y * L := by
    intro y
    have hpos : 0 < Real.rpow Δ y := Real.rpow_pos_of_pos hΔ_pos y
    have hlog : Real.log (2 * Real.rpow Δ y) = Real.log 2 + Real.log (Real.rpow Δ y) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hpos)] <;> ring
    have h_main : Real.logb 2 (2 * Real.rpow Δ y) = Real.log (2 * Real.rpow Δ y) / Real.log 2 := by rfl
    rw [h_main, hlog]
    have h2 : (Real.log 2 + Real.log (Real.rpow Δ y)) / Real.log 2 =
        Real.log 2 / Real.log 2 + Real.log (Real.rpow Δ y) / Real.log 2 := by rw [add_div]
    rw [h2]
    have h3 : Real.log 2 / Real.log 2 = 1 := by field_simp [Real.log_ne_zero]
    rw [h3]
    have h4 : Real.log (Real.rpow Δ y) / Real.log 2 = Real.logb 2 (Real.rpow Δ y) := by rfl
    rw [h4, h_logb_rpow y] <;> ring
  have h_logpos : 0 < Real.log (1 / Δ) := by
    have h1 : (1 : ℝ) < 1 / Δ := by
      have h2 : 0 < Δ := hΔ_pos
      have h3 : Δ < 1 := by linarith
      calc 1 = Δ / Δ := by field_simp [h2.ne']
        _ < 1 / Δ := by gcongr
    exact Real.log_pos h1
  have h_1000 : (1000 : ℝ) ≤ 1000 * (Real.log (1 / Δ) + 1)^3 := by
    have h3 : 1 ≤ Real.log (1 / Δ) + 1 := by linarith [h_logpos]
    have h4 : 0 ≤ Real.log (1 / Δ) + 1 := by linarith
    have h5 : 1 ≤ (Real.log (1 / Δ) + 1)^3 := by
      have h6 : 1 ≤ Real.log (1 / Δ) + 1 := h3
      calc 1 = (1 : ℝ)^3 := by norm_num
        _ ≤ (Real.log (1 / Δ) + 1)^3 := by gcongr
    nlinarith
  have h_ge_1000 : (1000 : ℝ) ≤ Real.rpow Δ (-ε) := h_1000.trans hΔ_small
  have h_ge_2 : (2 : ℝ) ≤ Real.rpow Δ (-ε) := by linarith
  have h_eq : Real.rpow 2 (ε * L) = Real.rpow Δ (-ε) := by
    have hpos' : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos hΔ_pos (-ε)
    have h5 : Real.rpow 2 (Real.logb 2 (Real.rpow Δ (-ε))) = Real.rpow Δ (-ε) :=
      Real.rpow_logb (by norm_num) (by norm_num) hpos'
    have h6 : Real.logb 2 (Real.rpow Δ (-ε)) = ε * L := by
      rw [h_logb_rpow (-ε)] <;> ring
    rw [h6] at h5
    exact h5
  have h7 : Real.rpow 2 (1 : ℝ) ≤ Real.rpow 2 (ε * L) := by
    have h71 : Real.rpow 2 (1 : ℝ) = (2 : ℝ) := by simp
    rw [h71, h_eq]
    exact h_ge_2
  have h_εL : 1 ≤ ε * L := by
    by_contra h8
    have h9 : ε * L < 1 := by linarith
    have h10 : Real.rpow 2 (ε * L) < Real.rpow 2 (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h9
    have h11 : Real.rpow 2 (1 : ℝ) = 2 := by simp
    rw [h11] at h10
    linarith
  let k_min := Int.floor (-2 * ε * L)
  let k_max := Int.floor (ε * L)
  let h_min := Int.floor (1 + (s + t) * L)
  let h_max := Int.floor ((t + s + ε) * L)
  let c_min := Int.floor (1 + (s - ε) * L)
  let c_max := Int.floor ((s + ε) * L)
  let K_bins : Finset ℤ := Finset.Icc k_min k_max
  let H_bins : Finset ℤ := Finset.Icc h_min h_max
  let C_bins : Finset ℤ := Finset.Icc c_min c_max
  have h_Icc_card : ∀ (a b : ℤ), a ≤ b → ((Finset.Icc a b).card : ℝ) = (b : ℝ) - (a : ℝ) + 1 := by
    intro a b h
    have h1 : a ≤ b + 1 := by linarith
    have h2 : ((Finset.Icc a b).card : ℤ) = (b : ℤ) + 1 - (a : ℤ) := Int.card_Icc_of_le a b h1
    have h3 : ((Finset.Icc a b).card : ℝ) = (b : ℝ) + 1 - (a : ℝ) := by exact_mod_cast h2
    rw [h3] <;> ring
  have hK_range : ∀ Q ∈ Qset_all, Int.floor (Real.logb 2 (K Q)) ∈ K_bins := by
    intro Q hQ
    have hpos1 : 0 < Real.rpow Δ (2 * ε) := Real.rpow_pos_of_pos hΔ_pos (2 * ε)
    have hpos2 : 0 < K Q := by exact lt_of_lt_of_le hpos1 (hK_lower Q hQ)
    have hpos3 : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos hΔ_pos (-ε)
    have h4 : Real.logb 2 (Real.rpow Δ (2 * ε)) ≤ Real.logb 2 (K Q) :=
      (Real.logb_le_logb h_base hpos1 hpos2).mpr (hK_lower Q hQ)
    have h5 : Real.logb 2 (K Q) ≤ Real.logb 2 (Real.rpow Δ (-ε)) :=
      (Real.logb_le_logb h_base hpos2 hpos3).mpr (hK_upper Q hQ)
    have h6 : Real.logb 2 (Real.rpow Δ (2 * ε)) = -2 * ε * L := by
      rw [h_logb_rpow (2 * ε)] <;> ring
    have h7 : Real.logb 2 (Real.rpow Δ (-ε)) = ε * L := by
      rw [h_logb_rpow (-ε)] <;> ring
    rw [h6] at h4; rw [h7] at h5
    simp only [K_bins, Finset.mem_Icc]
    exact ⟨Int.floor_le_floor h4, Int.floor_le_floor h5⟩
  have hH_range : ∀ Q ∈ Qset_all, Int.floor (Real.logb 2 (H Q)) ∈ H_bins := by
    intro Q hQ
    have hpos1 : 0 < Real.rpow Δ (-(s + t)) := Real.rpow_pos_of_pos hΔ_pos (-(s + t))
    have hpos1' : 0 < 2 * Real.rpow Δ (-(s + t)) := by positivity
    have hpos2 : 0 < H Q := by exact lt_of_lt_of_le hpos1' (hH_lower Q hQ)
    have hpos3 : 0 < Real.rpow Δ (-t - s - ε) := Real.rpow_pos_of_pos hΔ_pos (-t - s - ε)
    have h4 : Real.logb 2 (2 * Real.rpow Δ (-(s + t))) ≤ Real.logb 2 (H Q) :=
      (Real.logb_le_logb h_base hpos1' hpos2).mpr (hH_lower Q hQ)
    have h5 : Real.logb 2 (H Q) ≤ Real.logb 2 (Real.rpow Δ (-t - s - ε)) :=
      (Real.logb_le_logb h_base hpos2 hpos3).mpr (hH_upper Q hQ)
    have h6 : Real.logb 2 (2 * Real.rpow Δ (-(s + t))) = 1 + (s + t) * L := by
      rw [h_logb_2rpow (-(s + t))] <;> ring
    have h7 : Real.logb 2 (Real.rpow Δ (-t - s - ε)) = (t + s + ε) * L := by
      rw [h_logb_rpow (-t - s - ε)] <;> ring
    rw [h6] at h4; rw [h7] at h5
    simp only [H_bins, Finset.mem_Icc]
    exact ⟨Int.floor_le_floor h4, Int.floor_le_floor h5⟩
  have hC_range : ∀ Q ∈ Qset_all, Int.floor (Real.logb 2 (C Q)) ∈ C_bins := by
    intro Q hQ
    have hpos1 : 0 < Real.rpow Δ (-s + ε) := Real.rpow_pos_of_pos hΔ_pos (-s + ε)
    have hpos1' : 0 < 2 * Real.rpow Δ (-s + ε) := by positivity
    have hpos2 : 0 < C Q := by exact lt_of_lt_of_le hpos1' (hC_lower Q hQ)
    have hpos3 : 0 < Real.rpow Δ (-s - ε) := Real.rpow_pos_of_pos hΔ_pos (-s - ε)
    have h4 : Real.logb 2 (2 * Real.rpow Δ (-s + ε)) ≤ Real.logb 2 (C Q) :=
      (Real.logb_le_logb h_base hpos1' hpos2).mpr (hC_lower Q hQ)
    have h5 : Real.logb 2 (C Q) ≤ Real.logb 2 (Real.rpow Δ (-s - ε)) :=
      (Real.logb_le_logb h_base hpos2 hpos3).mpr (hC_upper Q hQ)
    have h6 : Real.logb 2 (2 * Real.rpow Δ (-s + ε)) = 1 + (s - ε) * L := by
      rw [h_logb_2rpow (-s + ε)] <;> ring
    have h7 : Real.logb 2 (Real.rpow Δ (-s - ε)) = (s + ε) * L := by
      rw [h_logb_rpow (-s - ε)] <;> ring
    rw [h6] at h4; rw [h7] at h5
    simp only [C_bins, Finset.mem_Icc]
    exact ⟨Int.floor_le_floor h4, Int.floor_le_floor h5⟩
  have h_sub : Qset_all.image binTriple ⊆ K_bins ×ˢ (H_bins ×ˢ C_bins) := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨Q, hQ, h_eq⟩
    have h4 := hbin Q hQ
    have h5 : b = (Int.floor (Real.logb 2 (K Q)), Int.floor (Real.logb 2 (H Q)), Int.floor (Real.logb 2 (C Q))) := by
      calc b = binTriple Q := h_eq.symm
        _ = _ := h4
    rw [h5]
    simp only [Finset.mem_product]
    exact ⟨hK_range Q hQ, hH_range Q hQ, hC_range Q hQ⟩
  have hK_card : (K_bins.card : ℝ) ≤ 5 * L := by
    have h1 : k_min ≤ k_max := by
      have h2 : (-2 * ε * L : ℝ) ≤ ε * L := by
        have h3 : 0 ≤ ε * L := by exact mul_nonneg (by linarith) (by linarith)
        linarith
      exact Int.floor_le_floor h2
    have h3 : (K_bins.card : ℝ) = (k_max : ℝ) - (k_min : ℝ) + 1 := by
      have h4 : K_bins = Finset.Icc k_min k_max := by rfl
      rw [h4]
      exact h_Icc_card k_min k_max h1
    rw [h3]
    have h4 : (k_max : ℝ) ≤ ε * L := Int.floor_le _
    have h5 : (k_min : ℝ) > -2 * ε * L - 1 := Int.sub_one_lt_floor (-2 * ε * L)
    have h6 : (k_max : ℝ) - (k_min : ℝ) + 1 < 3 * ε * L + 2 := by linarith
    have h7 : 3 * ε * L + 2 ≤ 5 * L := by
      have h8 : 0 < L := by linarith [hL_one]
      have h9 : 3 * ε * L < 3 * L := by
        have hL_pos : 0 < L := by linarith [hL_one]
        nlinarith
      have h10 : 2 ≤ 2 * L := by
        have hL_pos : 0 ≤ L := by linarith [hL_one]
        nlinarith
      linarith
    exact h6.le.trans h7
  have hH_card : (H_bins.card : ℝ) ≤ 2 * L := by
    have h1 : h_min ≤ h_max := by
      have h2 : (1 + (s + t) * L : ℝ) ≤ (t + s + ε) * L := by
        have h3 : 1 ≤ ε * L := h_εL
        linarith
      exact Int.floor_le_floor h2
    have h3 : (H_bins.card : ℝ) = (h_max : ℝ) - (h_min : ℝ) + 1 := by
      have h4 : H_bins = Finset.Icc h_min h_max := by rfl
      rw [h4]
      exact h_Icc_card h_min h_max h1
    rw [h3]
    have h4 : (h_max : ℝ) ≤ (t + s + ε) * L := Int.floor_le _
    have h5 : (h_min : ℝ) > (s + t) * L := by
      have h51 := Int.sub_one_lt_floor (1 + (s + t) * L)
      have h52 : (1 + (s + t) * L) - 1 = (s + t) * L := by ring
      rw [h52] at h51
      exact h51
    have h6 : (h_max : ℝ) - (h_min : ℝ) + 1 < ε * L + 1 := by linarith
    have h7 : ε * L + 1 ≤ 2 * L := by
      have h8 : 0 < L := by linarith [hL_one]
      have h9 : ε * L < L := by nlinarith
      have h10 : 1 ≤ L := hL_one
      linarith
    exact h6.le.trans h7
  have hC_card : (C_bins.card : ℝ) ≤ 3 * L := by
    have h1 : c_min ≤ c_max := by
      have h2 : (1 + (s - ε) * L : ℝ) ≤ (s + ε) * L := by
        have h3 : 1 ≤ 2 * ε * L := by linarith [h_εL]
        linarith
      exact Int.floor_le_floor h2
    have h3 : (C_bins.card : ℝ) = (c_max : ℝ) - (c_min : ℝ) + 1 := by
      have h4 : C_bins = Finset.Icc c_min c_max := by rfl
      rw [h4]
      exact h_Icc_card c_min c_max h1
    rw [h3]
    have h4 : (c_max : ℝ) ≤ (s + ε) * L := Int.floor_le _
    have h5 : (c_min : ℝ) > (s - ε) * L := by
      have h51 := Int.sub_one_lt_floor (1 + (s - ε) * L)
      have h52 : (1 + (s - ε) * L) - 1 = (s - ε) * L := by ring
      rw [h52] at h51
      exact h51
    have h6 : (c_max : ℝ) - (c_min : ℝ) + 1 < 2 * ε * L + 1 := by linarith
    have h7 : 2 * ε * L + 1 ≤ 3 * L := by
      have h8 : 0 < L := by linarith [hL_one]
      have h9 : 2 * ε * L < 2 * L := by nlinarith
      have h10 : 1 ≤ L := hL_one
      linarith
    exact h6.le.trans h7
  have h4 : L ≤ 2 * Real.log (1 / Δ) := by
    have h_log_nonneg : 0 ≤ Real.log (1 / Δ) := by
      have h1 : (1 : ℝ) < 1 / Δ := by
        have h2 : 0 < Δ := hΔ_pos
        have h3 : Δ < 1 := by linarith [hΔ_lt_half]
        have h4 : 1 / Δ > 1 := by apply one_lt_one_div <;> linarith
        exact h4
      exact Real.log_pos h1 |>.le
    have h5 : Real.log 2 ≥ 1 / 2 := by
      have h6 : Real.log (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by norm_num)
      have h7 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        rw [Real.log_div (by norm_num) (by norm_num)] <;> simp
      linarith
    calc
      L = Real.log (1 / Δ) / Real.log 2 := by rfl
      _ ≤ Real.log (1 / Δ) / (1 / 2) := by gcongr <;> linarith
      _ = 2 * Real.log (1 / Δ) := by ring
  calc
    ((Qset_all.image binTriple).card : ℝ)
      ≤ ((K_bins ×ˢ (H_bins ×ˢ C_bins)).card : ℝ) := by exact_mod_cast Finset.card_le_card h_sub
    _ = (K_bins.card : ℝ) * (H_bins.card : ℝ) * (C_bins.card : ℝ) := by
      simp [Finset.card_product] <;> ring
    _ ≤ (5 * L) * (2 * L) * (3 * L) := by gcongr <;> linarith
    _ = 30 * L^3 := by ring
    _ ≤ 30 * (2 * Real.log (1 / Δ))^3 := by gcongr
    _ = 240 * (Real.log (1 / Δ))^3 := by ring
    _ ≤ 1000 * (Real.log (1 / Δ) + 1)^3 := by
      have h5 : 0 ≤ Real.log (1 / Δ) := by linarith [h_logpos]
      have h6 : Real.log (1 / Δ) ≤ Real.log (1 / Δ) + 1 := by linarith
      have h7 : (Real.log (1 / Δ))^3 ≤ (Real.log (1 / Δ) + 1)^3 := by gcongr
      have h8 : 240 * (Real.log (1 / Δ))^3 ≤ 1000 * (Real.log (1 / Δ) + 1)^3 := by
        calc 240 * (Real.log (1 / Δ))^3 ≤ 240 * (Real.log (1 / Δ) + 1)^3 := by gcongr
          _ ≤ 1000 * (Real.log (1 / Δ) + 1)^3 := by
            have h9 : 0 ≤ (Real.log (1 / Δ) + 1)^3 := by positivity
            nlinarith
      exact h8

/-! ========================================================================
   A3: Uniformize local outputs  (OS (A.15)-(A.20))
   ======================================================================== -/

/-- Generalized bin count bound for canonical A2 exponents.
    Bounds the number of dyadic bins for (K, H, C) by 10000 * (log(1/Δ) + 1)^3. -/
lemma a3_bin_count_bound_canonical {Δ ε s t : ℝ} (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hs_ge_12ε : 12 * ε ≤ s) (hs_lt_one : s < 1)
    {Qset_all : Finset (CoarseSquare Δ)}
    {K H C : CoarseSquare Δ → ℝ}
    (hK_lower : ∀ Q ∈ Qset_all, Real.rpow Δ (2 * ε) ≤ K Q)
    (hK_upper : ∀ Q ∈ Qset_all, K Q ≤ Real.rpow Δ (-ε))
    (hH_lower : ∀ Q ∈ Qset_all, Real.rpow Δ (-(s + t) + 13 * ε) ≤ H Q)
    (hH_upper : ∀ Q ∈ Qset_all, H Q ≤ Real.rpow Δ (-(s + t) - 10 * ε))
    (hC_lower : ∀ Q ∈ Qset_all, Real.rpow Δ (-s + 11 * ε) ≤ C Q)
    (hC_upper : ∀ Q ∈ Qset_all, C Q ≤ Real.rpow Δ (-s - 5 * ε))
    (binTriple : CoarseSquare Δ → ℤ × ℤ × ℤ)
    (hbin : ∀ Q ∈ Qset_all,
      binTriple Q = (Int.floor (Real.logb 2 (K Q)), Int.floor (Real.logb 2 (H Q)), Int.floor (Real.logb 2 (C Q)))) :
    (Qset_all.image binTriple).card ≤ 50000 * (Real.log (1 / Δ) + 1)^3 := by
  let L : ℝ := Real.logb 2 (1 / Δ)
  have h_base : (1 : ℝ) < 2 := by norm_num
  have hL_one : 1 ≤ L := by
    have h1 : (2 : ℝ) ≤ 1 / Δ := by
      have h2 : 0 < Δ := hΔ_pos
      have h3 : 2 * Δ < 1 := by linarith
      calc (2 : ℝ) = (2 * Δ) / Δ := by field_simp [h2.ne'] <;> ring
        _ ≤ 1 / Δ := by gcongr
    have hpos1 : (0 : ℝ) < 2 := by norm_num
    have hpos2 : 0 < (1 / Δ) := by positivity
    have h_iff : Real.logb 2 2 ≤ Real.logb 2 (1 / Δ) ↔ (2 : ℝ) ≤ 1 / Δ :=
      Real.logb_le_logb h_base hpos1 hpos2
    have h2 : Real.logb 2 2 ≤ L := h_iff.mpr h1
    have h3 : Real.logb 2 2 = 1 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    linarith
  have hL_pos : 0 < L := by linarith [hL_one]
  have h_logb_negL : Real.logb 2 Δ = -L := by
    have h4 : L = Real.logb 2 (1 / Δ) := rfl
    have h5 : Real.logb 2 (1 / Δ) = -Real.logb 2 Δ := by
      rw [Real.logb_div (by norm_num) (by positivity)]
      <;> simp [Real.logb_one] <;> ring
    linarith
  have h_logb_rpow : ∀ (y : ℝ), Real.logb 2 (Real.rpow Δ y) = -y * L := by
    intro y
    have h1 : Real.logb 2 (Real.rpow Δ y) = Real.log (Real.rpow Δ y) / Real.log 2 := by rfl
    rw [h1]
    have h2 : Real.log (Real.rpow Δ y) = y * Real.log Δ := by
      simpa using Real.log_rpow hΔ_pos y
    rw [h2]
    have h3 : y * Real.log Δ / Real.log 2 = y * (Real.log Δ / Real.log 2) := by ring
    rw [h3]
    have h4 : Real.log Δ / Real.log 2 = Real.logb 2 Δ := by rfl
    rw [h4, h_logb_negL] <;> ring
  let k_min := Int.floor (-2 * ε * L)
  let k_max := Int.floor (ε * L)
  let h_min := Int.floor ((s + t - 13 * ε) * L)
  let h_max := Int.floor ((s + t + 10 * ε) * L)
  let c_min := Int.floor ((s - 11 * ε) * L)
  let c_max := Int.floor ((s + 5 * ε) * L)
  let K_bins : Finset ℤ := Finset.Icc k_min k_max
  let H_bins : Finset ℤ := Finset.Icc h_min h_max
  let C_bins : Finset ℤ := Finset.Icc c_min c_max
  have h_Icc_card : ∀ (a b : ℤ), a ≤ b → ((Finset.Icc a b).card : ℝ) = (b : ℝ) - (a : ℝ) + 1 := by
    intro a b h
    have h1 : a ≤ b + 1 := by linarith
    have h2 : ((Finset.Icc a b).card : ℤ) = (b : ℤ) + 1 - (a : ℤ) := Int.card_Icc_of_le a b h1
    have h3 : ((Finset.Icc a b).card : ℝ) = (b : ℝ) + 1 - (a : ℝ) := by exact_mod_cast h2
    rw [h3] <;> ring
  have hK_range : ∀ Q ∈ Qset_all, Int.floor (Real.logb 2 (K Q)) ∈ K_bins := by
    intro Q hQ
    have hpos1 : 0 < Real.rpow Δ (2 * ε) := Real.rpow_pos_of_pos hΔ_pos (2 * ε)
    have hpos2 : 0 < K Q := by exact lt_of_lt_of_le hpos1 (hK_lower Q hQ)
    have hpos3 : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos hΔ_pos (-ε)
    have h4 : Real.logb 2 (Real.rpow Δ (2 * ε)) ≤ Real.logb 2 (K Q) :=
      (Real.logb_le_logb h_base hpos1 hpos2).mpr (hK_lower Q hQ)
    have h5 : Real.logb 2 (K Q) ≤ Real.logb 2 (Real.rpow Δ (-ε)) :=
      (Real.logb_le_logb h_base hpos2 hpos3).mpr (hK_upper Q hQ)
    have h6 : Real.logb 2 (Real.rpow Δ (2 * ε)) = -2 * ε * L := by
      rw [h_logb_rpow (2 * ε)] <;> ring
    have h7 : Real.logb 2 (Real.rpow Δ (-ε)) = ε * L := by
      rw [h_logb_rpow (-ε)] <;> ring
    rw [h6] at h4; rw [h7] at h5
    simp only [K_bins, Finset.mem_Icc]
    exact ⟨Int.floor_le_floor h4, Int.floor_le_floor h5⟩
  have hH_range : ∀ Q ∈ Qset_all, Int.floor (Real.logb 2 (H Q)) ∈ H_bins := by
    intro Q hQ
    have hpos1 : 0 < Real.rpow Δ (-(s + t) + 13 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have hpos2 : 0 < H Q := by exact lt_of_lt_of_le hpos1 (hH_lower Q hQ)
    have hpos3 : 0 < Real.rpow Δ (-(s + t) - 10 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h4 : Real.logb 2 (Real.rpow Δ (-(s + t) + 13 * ε)) ≤ Real.logb 2 (H Q) :=
      (Real.logb_le_logb h_base hpos1 hpos2).mpr (hH_lower Q hQ)
    have h5 : Real.logb 2 (H Q) ≤ Real.logb 2 (Real.rpow Δ (-(s + t) - 10 * ε)) :=
      (Real.logb_le_logb h_base hpos2 hpos3).mpr (hH_upper Q hQ)
    have h6 : Real.logb 2 (Real.rpow Δ (-(s + t) + 13 * ε)) = (s + t - 13 * ε) * L := by
      rw [h_logb_rpow (-(s + t) + 13 * ε)] <;> ring
    have h7 : Real.logb 2 (Real.rpow Δ (-(s + t) - 10 * ε)) = (s + t + 10 * ε) * L := by
      rw [h_logb_rpow (-(s + t) - 10 * ε)] <;> ring
    rw [h6] at h4; rw [h7] at h5
    simp only [H_bins, Finset.mem_Icc]
    exact ⟨Int.floor_le_floor h4, Int.floor_le_floor h5⟩
  have hC_range : ∀ Q ∈ Qset_all, Int.floor (Real.logb 2 (C Q)) ∈ C_bins := by
    intro Q hQ
    have hpos1 : 0 < Real.rpow Δ (-s + 11 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have hpos2 : 0 < C Q := by exact lt_of_lt_of_le hpos1 (hC_lower Q hQ)
    have hpos3 : 0 < Real.rpow Δ (-s - 5 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h4 : Real.logb 2 (Real.rpow Δ (-s + 11 * ε)) ≤ Real.logb 2 (C Q) :=
      (Real.logb_le_logb h_base hpos1 hpos2).mpr (hC_lower Q hQ)
    have h5 : Real.logb 2 (C Q) ≤ Real.logb 2 (Real.rpow Δ (-s - 5 * ε)) :=
      (Real.logb_le_logb h_base hpos2 hpos3).mpr (hC_upper Q hQ)
    have h6 : Real.logb 2 (Real.rpow Δ (-s + 11 * ε)) = (s - 11 * ε) * L := by
      rw [h_logb_rpow (-s + 11 * ε)] <;> ring
    have h7 : Real.logb 2 (Real.rpow Δ (-s - 5 * ε)) = (s + 5 * ε) * L := by
      rw [h_logb_rpow (-s - 5 * ε)] <;> ring
    rw [h6] at h4; rw [h7] at h5
    simp only [C_bins, Finset.mem_Icc]
    exact ⟨Int.floor_le_floor h4, Int.floor_le_floor h5⟩
  have h_sub : Qset_all.image binTriple ⊆ K_bins ×ˢ (H_bins ×ˢ C_bins) := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨Q, hQ, h_eq⟩
    have h4 := hbin Q hQ
    have h5 : b = (Int.floor (Real.logb 2 (K Q)), Int.floor (Real.logb 2 (H Q)), Int.floor (Real.logb 2 (C Q))) := by
      calc b = binTriple Q := h_eq.symm
        _ = _ := h4
    rw [h5]
    simp only [Finset.mem_product]
    exact ⟨hK_range Q hQ, hH_range Q hQ, hC_range Q hQ⟩
  have hK_card : (K_bins.card : ℝ) ≤ 5 * L := by
    have h1 : k_min ≤ k_max := by
      have h2 : (-2 * ε * L : ℝ) ≤ ε * L := by
        have h3 : 0 ≤ ε * L := by exact mul_nonneg (by linarith) (by linarith)
        linarith
      exact Int.floor_le_floor h2
    have h3 : (K_bins.card : ℝ) = (k_max : ℝ) - (k_min : ℝ) + 1 := by
      rw [show K_bins = Finset.Icc k_min k_max from rfl]
      exact h_Icc_card k_min k_max h1
    rw [h3]
    have h4 : (k_max : ℝ) ≤ ε * L := Int.floor_le _
    have h5 : (k_min : ℝ) > -2 * ε * L - 1 := Int.sub_one_lt_floor _
    have h6 : (k_max : ℝ) - (k_min : ℝ) + 1 < 3 * ε * L + 2 := by linarith
    have h7 : 3 * ε * L + 2 ≤ 5 * L := by
      have h8 : 3 * ε * L < 3 * L := by nlinarith
      have h9 : 2 ≤ 2 * L := by nlinarith [hL_one]
      linarith
    exact h6.le.trans h7
  have hH_card : (H_bins.card : ℝ) ≤ 25 * L := by
    have h1 : h_min ≤ h_max := by
      have h2 : ((s + t - 13 * ε) * L : ℝ) ≤ (s + t + 10 * ε) * L := by
        have h3 : 0 ≤ 23 * ε * L := by positivity
        linarith
      exact Int.floor_le_floor h2
    have h3 : (H_bins.card : ℝ) = (h_max : ℝ) - (h_min : ℝ) + 1 := by
      rw [show H_bins = Finset.Icc h_min h_max from rfl]
      exact h_Icc_card h_min h_max h1
    rw [h3]
    have h4 : (h_max : ℝ) ≤ (s + t + 10 * ε) * L := Int.floor_le _
    have h5 : (h_min : ℝ) > (s + t - 13 * ε) * L - 1 := Int.sub_one_lt_floor _
    have h6 : (h_max : ℝ) - (h_min : ℝ) + 1 < 23 * ε * L + 2 := by linarith
    have h7 : 23 * ε * L + 2 ≤ 25 * L := by
      have h8 : 23 * ε < 23 := by nlinarith [hε_lt_one]
      have h9 : 23 * ε * L < 23 * L := by nlinarith [hL_pos]
      have h10 : 2 ≤ 2 * L := by nlinarith [hL_one]
      nlinarith
    exact h6.le.trans h7
  have hC_card : (C_bins.card : ℝ) ≤ 18 * L := by
    have h1 : c_min ≤ c_max := by
      have h2 : ((s - 11 * ε) * L : ℝ) ≤ (s + 5 * ε) * L := by
        have h3 : 0 ≤ 16 * ε * L := by positivity
        linarith
      exact Int.floor_le_floor h2
    have h3 : (C_bins.card : ℝ) = (c_max : ℝ) - (c_min : ℝ) + 1 := by
      rw [show C_bins = Finset.Icc c_min c_max from rfl]
      exact h_Icc_card c_min c_max h1
    rw [h3]
    have h4 : (c_max : ℝ) ≤ (s + 5 * ε) * L := Int.floor_le _
    have h5 : (c_min : ℝ) > (s - 11 * ε) * L - 1 := Int.sub_one_lt_floor _
    have h6 : (c_max : ℝ) - (c_min : ℝ) + 1 < 16 * ε * L + 2 := by linarith
    have h7 : 16 * ε * L + 2 ≤ 18 * L := by
      have h8 : 16 * ε * L < 16 * L := by nlinarith
      have h9 : 2 ≤ 2 * L := by nlinarith [hL_one]
      linarith
    exact h6.le.trans h7
  have h4 : L ≤ 2 * Real.log (1 / Δ) := by
    have h_log_nonneg : 0 ≤ Real.log (1 / Δ) := by
      have h1 : (1 : ℝ) < 1 / Δ := by
        have h2 : 0 < Δ := hΔ_pos
        have h3 : Δ < 1 := by linarith [hΔ_lt_half]
        have h4 : 1 / Δ > 1 := by apply one_lt_one_div <;> linarith
        exact h4
      exact Real.log_pos h1 |>.le
    have h5 : Real.log 2 ≥ 1 / 2 := by
      have h6 : Real.log (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by norm_num)
      have h7 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        rw [Real.log_div (by norm_num) (by norm_num)] <;> simp
      linarith
    calc
      L = Real.log (1 / Δ) / Real.log 2 := by rfl
      _ ≤ Real.log (1 / Δ) / (1 / 2) := by gcongr <;> linarith
      _ = 2 * Real.log (1 / Δ) := by ring
  have hΔ_lt_one : Δ < 1 := by linarith [hΔ_lt_half]
  have h_logpos : 0 < Real.log (1 / Δ) := by
    have h1 : (1 : ℝ) < 1 / Δ := by
      have h2 : 0 < Δ := hΔ_pos
      have h3 : Δ < 1 := hΔ_lt_one
      have h4 : 1 / Δ > 1 := by
        apply one_lt_one_div
        <;> linarith
      exact h4
    exact Real.log_pos h1
  calc
    ((Qset_all.image binTriple).card : ℝ)
      ≤ ((K_bins ×ˢ (H_bins ×ˢ C_bins)).card : ℝ) := by exact_mod_cast Finset.card_le_card h_sub
    _ = (K_bins.card : ℝ) * (H_bins.card : ℝ) * (C_bins.card : ℝ) := by
      simp [Finset.card_product] <;> ring
    _ ≤ (5 * L) * (25 * L) * (18 * L) := by gcongr <;> linarith
    _ = 2250 * L^3 := by ring
    _ ≤ 2250 * (2 * Real.log (1 / Δ))^3 := by gcongr
    _ = 18000 * (Real.log (1 / Δ))^3 := by ring
    _ ≤ 50000 * (Real.log (1 / Δ) + 1)^3 := by
      have h5 : 0 ≤ Real.log (1 / Δ) := by linarith [h_logpos]
      have h_log_nonneg : 0 ≤ Real.log (1 / Δ) := by linarith [h_logpos]
      have h_le : Real.log (1 / Δ) ≤ Real.log (1 / Δ) + 1 := by linarith
      have h6 : (Real.log (1 / Δ))^3 ≤ (Real.log (1 / Δ) + 1)^3 := by
        gcongr <;> linarith
      have h7 : 17280 * (Real.log (1 / Δ))^3 ≤ 17280 * (Real.log (1 / Δ) + 1)^3 := by
        gcongr <;> linarith
      have h8 : 0 ≤ (Real.log (1 / Δ) + 1)^3 := by positivity
      linarith

/-- Weak H_Q lower bound: H_Q ≥ 1 = Δ^0, since H_Q is a positive natural. -/
lemma a3_H_Q_lower_weak {Δ δ s t ε : ℝ} {Q : CoarseSquare Δ}
    (sd : A2_SquareData Δ δ s t ε Q) (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2) :
    Real.rpow Δ 0 ≤ sd.H_Q := by
  have h1 : Real.rpow Δ 0 = 1 := by simp
  rw [h1]
  exact sd.hH_Q_ge_one

/-- Weak bin count bound using H_lower = 1 and C_upper = Δ^{-1-5ε}.
    Range is O(L) per dimension, total ≤ 50000*L³. -/
lemma a3_bin_count_bound_weak {Δ ε s t : ℝ} (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hs_nonneg : 0 ≤ s) (hs_lt_one : s < 1)
    (ht_nonneg : 0 ≤ t) (ht_lt_two : t < 2)
    {Qset_all : Finset (CoarseSquare Δ)}
    {K H C : CoarseSquare Δ → ℝ}
    (hK_lower : ∀ Q ∈ Qset_all, Real.rpow Δ (2 * ε) ≤ K Q)
    (hK_upper : ∀ Q ∈ Qset_all, K Q ≤ Real.rpow Δ (-ε))
    (hH_lower : ∀ Q ∈ Qset_all, Real.rpow Δ 0 ≤ H Q)
    (hH_upper : ∀ Q ∈ Qset_all, H Q ≤ Real.rpow Δ (-(s + t) - 10 * ε))
    (hC_lower : ∀ Q ∈ Qset_all, Real.rpow Δ (-s + 11 * ε) ≤ C Q)
    (hC_upper : ∀ Q ∈ Qset_all, C Q ≤ Real.rpow Δ (-1 - 5 * ε))
    (binTriple : CoarseSquare Δ → ℤ × ℤ × ℤ)
    (hbin : ∀ Q ∈ Qset_all,
      binTriple Q = (Int.floor (Real.logb 2 (K Q)), Int.floor (Real.logb 2 (H Q)), Int.floor (Real.logb 2 (C Q)))) :
    (Qset_all.image binTriple).card ≤ 50000 * (Real.log (1 / Δ) + 1)^3 := by
  let L : ℝ := Real.logb 2 (1 / Δ)
  have h_base : (1 : ℝ) < 2 := by norm_num
  have hL_one : 1 ≤ L := by
    have h1 : (2 : ℝ) ≤ 1 / Δ := by
      have h2 : 0 < Δ := hΔ_pos
      have h3 : 2 * Δ < 1 := by linarith
      calc (2 : ℝ) = (2 * Δ) / Δ := by field_simp [h2.ne'] <;> ring
        _ ≤ 1 / Δ := by gcongr
    have hpos1 : (0 : ℝ) < 2 := by norm_num
    have hpos2 : 0 < (1 / Δ) := by positivity
    have h_iff : Real.logb 2 2 ≤ Real.logb 2 (1 / Δ) ↔ (2 : ℝ) ≤ 1 / Δ :=
      Real.logb_le_logb h_base hpos1 hpos2
    have h2 : Real.logb 2 2 ≤ L := h_iff.mpr h1
    have h3 : Real.logb 2 2 = 1 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    linarith
  have hL_pos : 0 < L := by linarith [hL_one]
  have h_logb_rpow : ∀ (y : ℝ), Real.logb 2 (Real.rpow Δ y) = -y * L := by
    intro y
    have h1 : Real.logb 2 (Real.rpow Δ y) = Real.log (Real.rpow Δ y) / Real.log 2 := by rfl
    rw [h1]
    have h2 : Real.log (Real.rpow Δ y) = y * Real.log Δ := by simpa using Real.log_rpow hΔ_pos y
    rw [h2]
    have h3 : (y * Real.log Δ) / Real.log 2 = y * (Real.log Δ / Real.log 2) := by ring
    rw [h3]
    have h4 : Real.log Δ / Real.log 2 = Real.logb 2 Δ := by rfl
    have h5 : Real.logb 2 Δ = -L := by
      have h6 : L = Real.logb 2 (1 / Δ) := rfl
      have h7 : Real.logb 2 (1 / Δ) = -Real.logb 2 Δ := by
        rw [Real.logb_div (by norm_num) (by positivity)] <;> simp [Real.logb_one] <;> ring
      linarith
    rw [h4, h5] <;> ring
  let k_min := Int.floor (-2 * ε * L)
  let k_max := Int.floor (ε * L)
  let h_min := (0 : ℤ)
  let h_max := Int.floor ((s + t + 10 * ε) * L)
  let c_min := Int.floor ((s - 11 * ε) * L)
  let c_max := Int.floor ((1 + 5 * ε) * L)
  let K_bins : Finset ℤ := Finset.Icc k_min k_max
  let H_bins : Finset ℤ := Finset.Icc h_min h_max
  let C_bins : Finset ℤ := Finset.Icc c_min c_max
  have h_Icc_card : ∀ (a b : ℤ), a ≤ b → ((Finset.Icc a b).card : ℝ) = (b : ℝ) - (a : ℝ) + 1 := by
    intro a b h
    have h1 : a ≤ b + 1 := by linarith
    have h2 : ((Finset.Icc a b).card : ℤ) = (b : ℤ) + 1 - (a : ℤ) := Int.card_Icc_of_le a b h1
    have h3 : ((Finset.Icc a b).card : ℝ) = (b : ℝ) + 1 - (a : ℝ) := by exact_mod_cast h2
    rw [h3] <;> ring
  have hK_range : ∀ Q ∈ Qset_all, Int.floor (Real.logb 2 (K Q)) ∈ K_bins := by
    intro Q hQ
    have hpos2 : 0 < K Q := by exact lt_of_lt_of_le (Real.rpow_pos_of_pos hΔ_pos (2 * ε)) (hK_lower Q hQ)
    have h4 : Real.logb 2 (Real.rpow Δ (2 * ε)) ≤ Real.logb 2 (K Q) :=
      (Real.logb_le_logb h_base (Real.rpow_pos_of_pos hΔ_pos (2 * ε)) hpos2).mpr (hK_lower Q hQ)
    have h5 : Real.logb 2 (K Q) ≤ Real.logb 2 (Real.rpow Δ (-ε)) :=
      (Real.logb_le_logb h_base hpos2 (Real.rpow_pos_of_pos hΔ_pos (-ε))).mpr (hK_upper Q hQ)
    have h6 : Real.logb 2 (Real.rpow Δ (2 * ε)) = -2 * ε * L := by rw [h_logb_rpow (2 * ε)] <;> ring
    have h7 : Real.logb 2 (Real.rpow Δ (-ε)) = ε * L := by rw [h_logb_rpow (-ε)] <;> ring
    rw [h6] at h4; rw [h7] at h5
    simp only [K_bins, Finset.mem_Icc]
    exact ⟨Int.floor_le_floor h4, Int.floor_le_floor h5⟩
  have hH_range : ∀ Q ∈ Qset_all, Int.floor (Real.logb 2 (H Q)) ∈ H_bins := by
    intro Q hQ
    have hpos2 : 0 < H Q := by
      have h1 : Real.rpow Δ 0 ≤ H Q := hH_lower Q hQ
      have h2 : Real.rpow Δ 0 = 1 := by simp
      rw [h2] at h1
      linarith
    have h4 : (0 : ℝ) ≤ Real.logb 2 (H Q) := by
      have h5 : (1 : ℝ) ≤ H Q := by
        have h6 : Real.rpow Δ 0 ≤ H Q := hH_lower Q hQ
        have h7 : Real.rpow Δ 0 = 1 := by simp
        rw [h7] at h6; exact h6
      have h8 : Real.logb 2 1 = 0 := by simp
      have h9 : Real.logb 2 1 ≤ Real.logb 2 (H Q) :=
        (Real.logb_le_logb h_base (by norm_num) hpos2).mpr h5
      rw [h8] at h9; exact h9
    have h5 : Real.logb 2 (H Q) ≤ Real.logb 2 (Real.rpow Δ (-(s + t) - 10 * ε)) :=
      (Real.logb_le_logb h_base hpos2 (Real.rpow_pos_of_pos hΔ_pos (-(s + t) - 10 * ε))).mpr (hH_upper Q hQ)
    have h7 : Real.logb 2 (Real.rpow Δ (-(s + t) - 10 * ε)) = (s + t + 10 * ε) * L := by
      rw [h_logb_rpow (-(s + t) - 10 * ε)] <;> ring
    rw [h7] at h5
    simp only [H_bins, Finset.mem_Icc]
    exact ⟨Int.floor_nonneg.mpr h4, Int.floor_le_floor h5⟩
  have hC_range : ∀ Q ∈ Qset_all, Int.floor (Real.logb 2 (C Q)) ∈ C_bins := by
    intro Q hQ
    have hpos2 : 0 < C Q := by exact lt_of_lt_of_le (Real.rpow_pos_of_pos hΔ_pos (-s + 11 * ε)) (hC_lower Q hQ)
    have h4 : Real.logb 2 (Real.rpow Δ (-s + 11 * ε)) ≤ Real.logb 2 (C Q) :=
      (Real.logb_le_logb h_base (Real.rpow_pos_of_pos hΔ_pos (-s + 11 * ε)) hpos2).mpr (hC_lower Q hQ)
    have h5 : Real.logb 2 (C Q) ≤ Real.logb 2 (Real.rpow Δ (-1 - 5 * ε)) :=
      (Real.logb_le_logb h_base hpos2 (Real.rpow_pos_of_pos hΔ_pos (-1 - 5 * ε))).mpr (hC_upper Q hQ)
    have h6 : Real.logb 2 (Real.rpow Δ (-s + 11 * ε)) = (s - 11 * ε) * L := by
      rw [h_logb_rpow (-s + 11 * ε)] <;> ring
    have h7 : Real.logb 2 (Real.rpow Δ (-1 - 5 * ε)) = (1 + 5 * ε) * L := by
      rw [h_logb_rpow (-1 - 5 * ε)] <;> ring
    rw [h6] at h4; rw [h7] at h5
    simp only [C_bins, Finset.mem_Icc]
    exact ⟨Int.floor_le_floor h4, Int.floor_le_floor h5⟩
  have h_sub : Qset_all.image binTriple ⊆ K_bins ×ˢ (H_bins ×ˢ C_bins) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨Q, hQ, rfl⟩
    have h1 := hK_range Q hQ
    have h2 := hH_range Q hQ
    have h3 := hC_range Q hQ
    have h4 : binTriple Q = (Int.floor (Real.logb 2 (K Q)), Int.floor (Real.logb 2 (H Q)), Int.floor (Real.logb 2 (C Q))) := hbin Q hQ
    rw [h4]
    simp only [Finset.mem_product] at * <;> tauto
  have hK_card : (K_bins.card : ℝ) ≤ 5 * L := by
    have h1 : k_min ≤ k_max := by
      have h2 : -2 * ε * L ≤ ε * L := by
        have h3 : 0 ≤ 3 * ε * L := by positivity
        linarith
      exact Int.floor_le_floor h2
    have h3 : (K_bins.card : ℝ) = (k_max : ℝ) - (k_min : ℝ) + 1 := h_Icc_card k_min k_max h1
    rw [h3]
    have h4 : (k_max : ℝ) ≤ ε * L := Int.floor_le _
    have h5 : (k_min : ℝ) > -2 * ε * L - 1 := Int.sub_one_lt_floor _
    have h6 : (k_max : ℝ) - (k_min : ℝ) + 1 < 3 * ε * L + 2 := by linarith
    have h7 : 3 * ε * L + 2 ≤ 5 * L := by
      have h8 : 3 * ε * L < 3 * L := by nlinarith [hε_lt_one]
      have h9 : 2 ≤ 2 * L := by nlinarith [hL_one]
      linarith
    exact h6.le.trans h7
  have hH_card : (H_bins.card : ℝ) ≤ 24 * L := by
    have h1 : h_min ≤ h_max := by
      have h2 : (0 : ℝ) ≤ (s + t + 10 * ε) * L := by
        have h21 : 0 ≤ s + t + 10 * ε := by linarith [hs_nonneg, ht_nonneg, hε_pos]
        positivity
      simpa [h_min] using Int.floor_nonneg.mpr h2
    have h3 : (H_bins.card : ℝ) = (h_max : ℝ) - (h_min : ℝ) + 1 := h_Icc_card h_min h_max h1
    rw [h3]
    have h4 : (h_max : ℝ) ≤ (s + t + 10 * ε) * L := Int.floor_le _
    have h5 : (h_min : ℝ) = 0 := by simp [h_min]
    rw [h5]
    have h6 : (h_max : ℝ) - 0 + 1 < (s + t + 10 * ε) * L + 2 := by linarith
    have h7 : (s + t + 10 * ε) * L + 2 ≤ 24 * L := by
      have h8 : s + t + 10 * ε < 22 := by
        have h9 : s + t < 3 := by linarith [hs_lt_one, ht_lt_two]
        have h10 : 10 * ε < 10 := by nlinarith [hε_lt_one]
        linarith
      have h11 : (s + t + 10 * ε) * L < 22 * L := by nlinarith [hL_pos]
      have h12 : 2 ≤ 2 * L := by nlinarith [hL_one]
      linarith
    exact h6.le.trans h7
  have hC_card : (C_bins.card : ℝ) ≤ 19 * L := by
    have h1 : c_min ≤ c_max := by
      have h2 : (s - 11 * ε) * L ≤ (1 + 5 * ε) * L := by
        have h3 : 0 ≤ (1 - s + 16 * ε) * L := by
          have h4 : 0 < 1 - s + 16 * ε := by
            nlinarith [hs_lt_one, hε_pos]
          positivity
        linarith
      exact Int.floor_le_floor h2
    have h3 : (C_bins.card : ℝ) = (c_max : ℝ) - (c_min : ℝ) + 1 := h_Icc_card c_min c_max h1
    rw [h3]
    have h4 : (c_max : ℝ) ≤ (1 + 5 * ε) * L := Int.floor_le _
    have h5 : (c_min : ℝ) > (s - 11 * ε) * L - 1 := Int.sub_one_lt_floor _
    have h6 : (c_max : ℝ) - (c_min : ℝ) + 1 < (1 - s + 16 * ε) * L + 2 := by linarith
    have h7 : (1 - s + 16 * ε) * L + 2 ≤ 19 * L := by
      have h8 : (1 - s + 16 * ε) * L < 17 * L := by
        have h9 : 1 - s + 16 * ε < 17 := by
          nlinarith [hs_lt_one, hε_lt_one]
        nlinarith [hL_pos]
      have h10 : 2 ≤ 2 * L := by nlinarith [hL_one]
      linarith
    exact h6.le.trans h7
  have h4 : L ≤ 2 * Real.log (1 / Δ) := by
    have h_log_nonneg : 0 ≤ Real.log (1 / Δ) := by
      have h1 : (1 : ℝ) < 1 / Δ := by
        have h2 : 0 < Δ := hΔ_pos
        have h3 : Δ < 1 := by linarith [hΔ_lt_half]
        have h4 : 1 / Δ > 1 := by apply one_lt_one_div <;> linarith
        exact h4
      exact Real.log_pos h1 |>.le
    have h5 : Real.log 2 ≥ 1 / 2 := by
      have h6 : Real.log (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      have h7 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        rw [Real.log_div (by norm_num) (by norm_num)] <;> simp
      linarith
    calc
      L = Real.log (1 / Δ) / Real.log 2 := by rfl
      _ ≤ Real.log (1 / Δ) / (1 / 2) := by gcongr <;> linarith
      _ = 2 * Real.log (1 / Δ) := by ring
  have h_logpos : 0 < Real.log (1 / Δ) := by
    have h1 : (1 : ℝ) < 1 / Δ := by
      have h2 : 0 < Δ := hΔ_pos
      have h3 : Δ < 1 := by linarith [hΔ_lt_half]
      have h4 : 1 / Δ > 1 := by apply one_lt_one_div <;> linarith
      exact h4
    exact Real.log_pos h1
  calc
    ((Qset_all.image binTriple).card : ℝ)
      ≤ ((K_bins ×ˢ (H_bins ×ˢ C_bins)).card : ℝ) := by exact_mod_cast Finset.card_le_card h_sub
    _ = (K_bins.card : ℝ) * (H_bins.card : ℝ) * (C_bins.card : ℝ) := by
      simp [Finset.card_product] <;> ring
    _ ≤ (5 * L) * (24 * L) * (19 * L) := by gcongr <;> linarith
    _ = 2280 * L^3 := by ring
    _ ≤ 2280 * (2 * Real.log (1 / Δ))^3 := by gcongr
    _ = 18240 * (Real.log (1 / Δ))^3 := by ring
    _ ≤ 50000 * (Real.log (1 / Δ) + 1)^3 := by
      have h5 : 0 ≤ Real.log (1 / Δ) := by linarith [h_logpos]
      have h6 : (Real.log (1 / Δ))^3 ≤ (Real.log (1 / Δ) + 1)^3 := by gcongr <;> linarith
      have h7 : 18240 * (Real.log (1 / Δ))^3 ≤ 18240 * (Real.log (1 / Δ) + 1)^3 := by gcongr
      have h8 : 0 ≤ (Real.log (1 / Δ) + 1)^3 := by positivity
      linarith

/-- Helper: derive H_Q ≥ Δ^{-s-t+50ε} from balance + strong card bound. -/
lemma a3_HQ_lower_from_card
    {Δ s t ε M orig K_Q H_Q CQ_card K_pack : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2) (hε_pos : 0 < ε)
    (hM_lower : M ≥ Real.rpow Δ (-2 * s + 2 * ε) / K_pack)
    (horig : Real.rpow Δ (-t + 3 * ε) ≤ orig)
    (hKQ : K_Q ≤ Real.rpow Δ (-ε))
    (hKpack_bound : K_pack ≤ Real.rpow Δ (-2 * ε) / 6)
    (hKpack_pos : 0 < K_pack)
    (hcard : CQ_card ≤ Real.rpow Δ (-s - 40 * ε))
    (hbal : M * orig ≤ K_Q * H_Q * CQ_card)
    (hKQ_pos : 0 < K_Q) (hcard_pos : 0 < CQ_card) :
    H_Q ≥ Real.rpow Δ (-s - t + 52 * ε) := by
  let A := Real.rpow Δ (-2 * s + 2 * ε) / K_pack
  let B := Real.rpow Δ (-t + 3 * ε)
  let D := Real.rpow Δ (-s - 41 * ε)
  have hA_pos : 0 < A := div_pos (Real.rpow_pos_of_pos hΔ_pos _) hKpack_pos
  have hB_pos : 0 < B := Real.rpow_pos_of_pos hΔ_pos _
  have hD_pos : 0 < D := Real.rpow_pos_of_pos hΔ_pos _
  have hM_pos : 0 < M := hA_pos.trans_le hM_lower
  have h_den_pos : 0 < K_Q * CQ_card := mul_pos hKQ_pos hcard_pos
  have h_rpow_nonneg : ∀ (x : ℝ), 0 ≤ Real.rpow Δ x := fun x => Real.rpow_nonneg hΔ_pos.le x
  have rpow_add : ∀ (x y : ℝ), Real.rpow Δ x * Real.rpow Δ y = Real.rpow Δ (x + y) :=
    fun x y => (Real.rpow_add hΔ_pos x y).symm
  have rpow_sub : ∀ (x y : ℝ), Real.rpow Δ x / Real.rpow Δ y = Real.rpow Δ (x - y) :=
    fun x y => (Real.rpow_sub hΔ_pos x y).symm
  have h_step1 : H_Q ≥ M * orig / (K_Q * CQ_card) := by
    have h : M * orig / (K_Q * CQ_card) ≤ (K_Q * H_Q * CQ_card) / (K_Q * CQ_card) :=
      div_le_div_of_nonneg_right hbal h_den_pos.le
    have h2 : (K_Q * H_Q * CQ_card) / (K_Q * CQ_card) = H_Q := by
      field_simp [h_den_pos.ne'] <;> ring
    rw [h2] at h
    exact h
  have h_step2 : M * orig ≥ A * B := by
    have h1 : A * B ≤ M * B := mul_le_mul_of_nonneg_right hM_lower hB_pos.le
    have h2 : M * B ≤ M * orig := mul_le_mul_of_nonneg_left horig hM_pos.le
    exact le_trans h1 h2
  have h_step3 : K_Q * CQ_card ≤ D := by
    have h : K_Q * CQ_card ≤ Real.rpow Δ (-ε) * Real.rpow Δ (-s - 40 * ε) := by
      have h1 : K_Q * CQ_card ≤ Real.rpow Δ (-ε) * CQ_card :=
        mul_le_mul_of_nonneg_right hKQ hcard_pos.le
      have h2 : Real.rpow Δ (-ε) * CQ_card ≤ Real.rpow Δ (-ε) * Real.rpow Δ (-s - 40 * ε) :=
        mul_le_mul_of_nonneg_left hcard (h_rpow_nonneg _)
      exact le_trans h1 h2
    have h2 : Real.rpow Δ (-ε) * Real.rpow Δ (-s - 40 * ε) = D := by
      have h3 := rpow_add (-ε) (-s - 40 * ε)
      have h4 : (-ε) + (-s - 40 * ε) = -s - 41 * ε := by ring
      rw [h3, h4] <;> rfl
    rw [h2] at h
    exact h
  have h_inv : 1 / K_pack ≥ 6 * Real.rpow Δ (2 * ε) := by
    have h1 : 1 / K_pack ≥ 1 / (Real.rpow Δ (-2 * ε) / 6) := by
      gcongr
      <;> linarith
    have h3 : Real.rpow Δ (-2 * ε) * Real.rpow Δ (2 * ε) = 1 := by
      have h4 := rpow_add (-2 * ε) (2 * ε)
      have h5 : (-2 * ε) + (2 * ε) = 0 := by ring
      rw [h4, h5] <;> simp
    have h2 : 1 / (Real.rpow Δ (-2 * ε) / 6) = 6 * Real.rpow Δ (2 * ε) := by
      have h4 : 1 / (Real.rpow Δ (-2 * ε) / 6) = 6 / Real.rpow Δ (-2 * ε) := by
        field_simp
        <;> ring
      rw [h4]
      have h5 : (Real.rpow Δ (-2 * ε))⁻¹ = Real.rpow Δ (2 * ε) := by
        exact inv_eq_of_mul_eq_one_right h3
      rw [div_eq_mul_inv, h5] <;> ring
    rw [h2] at h1
    exact h1
  have hAB : A * B = (1 / K_pack) * (Real.rpow Δ (-2 * s + 2 * ε) * Real.rpow Δ (-t + 3 * ε)) := by
    simp [A, B] <;> ring
  have h_rpow2 : Real.rpow Δ (-2 * s + 2 * ε) * Real.rpow Δ (-t + 3 * ε) = Real.rpow Δ (-2 * s - t + 5 * ε) := by
    have h4 := rpow_add (-2 * s + 2 * ε) (-t + 3 * ε)
    rw [h4] <;> ring_nf
  have h_rpow3 : Real.rpow Δ (2 * ε) * Real.rpow Δ (-2 * s - t + 5 * ε) / Real.rpow Δ (-s - 41 * ε) =
      Real.rpow Δ (-s - t + 48 * ε) := by
    have h4 : Real.rpow Δ (2 * ε) * Real.rpow Δ (-2 * s - t + 5 * ε) = Real.rpow Δ (-2 * s - t + 7 * ε) := by
      have h5 := rpow_add (2 * ε) (-2 * s - t + 5 * ε)
      rw [h5] <;> ring_nf
    rw [h4]
    have h5 : Real.rpow Δ (-2 * s - t + 7 * ε) / Real.rpow Δ (-s - 41 * ε) =
        Real.rpow Δ ((-2 * s - t + 7 * ε) - (-s - 41 * ε)) := by
      exact rpow_sub (-2 * s - t + 7 * ε) (-s - 41 * ε)
    rw [h5]
    have h6 : (-2 * s - t + 7 * ε) - (-s - 41 * ε) = -s - t + 48 * ε := by ring
    rw [h6]
  have h_final : (6 : ℝ) * Real.rpow Δ (-s - t + 48 * ε) ≥ Real.rpow Δ (-s - t + 52 * ε) := by
    have h9 : Real.rpow Δ (-s - t + 52 * ε) = Real.rpow Δ (-s - t + 48 * ε) * Real.rpow Δ (4 * ε) := by
      have h10 := rpow_add (-s - t + 48 * ε) (4 * ε)
      rw [h10] <;> ring_nf
    rw [h9]
    have h10 : Real.rpow Δ (4 * ε) ≤ 1 := by
      have h11 : Δ ≤ 1 := by linarith
      have h12 : 0 ≤ 4 * ε := by linarith
      exact Real.rpow_le_one hΔ_pos.le h11 h12
    have h13 : 0 ≤ Real.rpow Δ (-s - t + 48 * ε) := h_rpow_nonneg _
    nlinarith
  have h_middle_pos : 0 ≤ Real.rpow Δ (-2 * s - t + 5 * ε) := h_rpow_nonneg _
  calc H_Q
    ≥ M * orig / (K_Q * CQ_card) := h_step1
  _ ≥ A * B / (K_Q * CQ_card) := by
    exact div_le_div_of_nonneg_right h_step2 h_den_pos.le
  _ ≥ A * B / D := by
    gcongr
    <;> exact h_step3
  _ = (1 / K_pack) * Real.rpow Δ (-2 * s - t + 5 * ε) / D := by
    rw [hAB, h_rpow2] <;> ring
  _ ≥ (6 * Real.rpow Δ (2 * ε)) * Real.rpow Δ (-2 * s - t + 5 * ε) / D := by
    have h_ineq : (1 / K_pack) * Real.rpow Δ (-2 * s - t + 5 * ε) ≥
        (6 * Real.rpow Δ (2 * ε)) * Real.rpow Δ (-2 * s - t + 5 * ε) := by
      exact mul_le_mul_of_nonneg_right h_inv h_middle_pos
    exact div_le_div_of_nonneg_right h_ineq hD_pos.le
  _ = 6 * Real.rpow Δ (-s - t + 48 * ε) := by
    have h_assoc : (6 * Real.rpow Δ (2 * ε)) * Real.rpow Δ (-2 * s - t + 5 * ε) / D =
        6 * (Real.rpow Δ (2 * ε) * Real.rpow Δ (-2 * s - t + 5 * ε) / D) := by ring
    rw [h_assoc]
    rw [h_rpow3] <;> ring
  _ ≥ Real.rpow Δ (-s - t + 52 * ε) := h_final

/-- Improved H_Q lower bound: H_Q ≥ 6·Δ^{-s-t+37ε}.
    Uses tighter C_Q bound Δ^{-s-29ε} and K_pack bound Δ^{-2ε}/6. -/
lemma a3_HQ_lower_improved
    {Δ s t ε M orig K_Q H_Q CQ_card K_pack : ℝ}
    (hΔ_pos : 0 < Δ) (hε_pos : 0 < ε)
    (hM_lower : M ≥ Real.rpow Δ (-2 * s + 2 * ε) / K_pack)
    (horig : Real.rpow Δ (-t + 3 * ε) ≤ orig)
    (hKQ : K_Q ≤ Real.rpow Δ (-ε))
    (hKpack_bound : K_pack ≤ Real.rpow Δ (-2 * ε) / 6)
    (hKpack_pos : 0 < K_pack)
    (hcard : CQ_card ≤ Real.rpow Δ (-s - 29 * ε))
    (hbal : M * orig ≤ K_Q * H_Q * CQ_card)
    (hKQ_pos : 0 < K_Q) (hcard_pos : 0 < CQ_card) :
    H_Q ≥ 6 * Real.rpow Δ (-s - t + 37 * ε) := by
  have rpow_add : ∀ (x y : ℝ), Real.rpow Δ x * Real.rpow Δ y = Real.rpow Δ (x + y) :=
    fun x y => (Real.rpow_add hΔ_pos x y).symm
  have rpow_nonneg : ∀ (x : ℝ), 0 ≤ Real.rpow Δ x := fun x => Real.rpow_nonneg hΔ_pos.le x
  have rpow_pos : ∀ (x : ℝ), 0 < Real.rpow Δ x := fun x => Real.rpow_pos_of_pos hΔ_pos x
  have h_den_pos : 0 < K_Q * CQ_card := mul_pos hKQ_pos hcard_pos
  have hM_pos : 0 < M := by
    have h : 0 < Real.rpow Δ (-2 * s + 2 * ε) / K_pack := div_pos (rpow_pos _) hKpack_pos
    exact h.trans_le hM_lower
  have h_step1 : H_Q ≥ M * orig / (K_Q * CQ_card) := by
    have h : M * orig / (K_Q * CQ_card) ≤ (K_Q * H_Q * CQ_card) / (K_Q * CQ_card) :=
      div_le_div_of_nonneg_right hbal h_den_pos.le
    have h2 : (K_Q * H_Q * CQ_card) / (K_Q * CQ_card) = H_Q := by
      field_simp [h_den_pos.ne'] <;> ring
    rw [h2] at h; exact h
  have h_step2 : M * orig ≥ Real.rpow Δ (-2 * s - t + 5 * ε) / K_pack := by
    have h1 : (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) * Real.rpow Δ (-t + 3 * ε) ≤ M * orig := by
      calc (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) * Real.rpow Δ (-t + 3 * ε)
          ≤ M * Real.rpow Δ (-t + 3 * ε) := mul_le_mul_of_nonneg_right hM_lower (rpow_nonneg _)
        _ ≤ M * orig := mul_le_mul_of_nonneg_left horig hM_pos.le
    have h2 : (Real.rpow Δ (-2 * s + 2 * ε) * Real.rpow Δ (-t + 3 * ε)) = Real.rpow Δ (-2 * s - t + 5 * ε) := by
      have h3 := rpow_add (-2 * s + 2 * ε) (-t + 3 * ε)
      have h4 : (-2 * s + 2 * ε) + (-t + 3 * ε) = -2 * s - t + 5 * ε := by ring
      rw [h3, h4]
    have h5 : (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) * Real.rpow Δ (-t + 3 * ε) =
        (Real.rpow Δ (-2 * s + 2 * ε) * Real.rpow Δ (-t + 3 * ε)) / K_pack := by ring
    rw [h5, h2] at h1; exact h1
  have h_step3 : K_Q * CQ_card ≤ Real.rpow Δ (-s - 30 * ε) := by
    have h : K_Q * CQ_card ≤ Real.rpow Δ (-ε) * Real.rpow Δ (-s - 29 * ε) := by
      have h1 : K_Q * CQ_card ≤ Real.rpow Δ (-ε) * CQ_card :=
        mul_le_mul_of_nonneg_right hKQ hcard_pos.le
      have h2 : Real.rpow Δ (-ε) * CQ_card ≤ Real.rpow Δ (-ε) * Real.rpow Δ (-s - 29 * ε) :=
        mul_le_mul_of_nonneg_left hcard (rpow_nonneg _)
      exact le_trans h1 h2
    have h2 : Real.rpow Δ (-ε) * Real.rpow Δ (-s - 29 * ε) = Real.rpow Δ (-s - 30 * ε) := by
      have h3 := rpow_add (-ε) (-s - 29 * ε)
      have h4 : (-ε) + (-s - 29 * ε) = -s - 30 * ε := by ring
      rw [h3, h4] <;> rfl
    rw [h2] at h; exact h
  have h_inv : 1 / K_pack ≥ 6 * Real.rpow Δ (2 * ε) := by
    have h1 : 1 / K_pack ≥ 1 / (Real.rpow Δ (-2 * ε) / 6) := by gcongr <;> linarith
    have h2 : Real.rpow Δ (-2 * ε) * Real.rpow Δ (2 * ε) = 1 := by
      have h3 := rpow_add (-2 * ε) (2 * ε)
      have h4 : (-2 * ε) + (2 * ε) = 0 := by ring
      rw [h3, h4] <;> simp
    have h5 : 1 / (Real.rpow Δ (-2 * ε) / 6) = 6 * Real.rpow Δ (2 * ε) := by
      have h6 : 1 / (Real.rpow Δ (-2 * ε) / 6) = 6 / Real.rpow Δ (-2 * ε) := by field_simp <;> ring
      rw [h6]
      have h7 : (Real.rpow Δ (-2 * ε))⁻¹ = Real.rpow Δ (2 * ε) := by
        exact inv_eq_of_mul_eq_one_right h2
      rw [div_eq_mul_inv, h7] <;> ring
    rw [h5] at h1; exact h1
  have h_div : (Real.rpow Δ (-2 * s - t + 5 * ε) / K_pack) / Real.rpow Δ (-s - 30 * ε) =
      (1 / K_pack) * Real.rpow Δ (-s - t + 35 * ε) := by
    have h4 : Real.rpow Δ (-2 * s - t + 5 * ε) / Real.rpow Δ (-s - 30 * ε) =
        Real.rpow Δ ((-2 * s - t + 5 * ε) - (-s - 30 * ε)) := by
      exact (Real.rpow_sub hΔ_pos (-2 * s - t + 5 * ε) (-s - 30 * ε)).symm
    have h5 : (-2 * s - t + 5 * ε) - (-s - 30 * ε) = -s - t + 35 * ε := by ring
    have h6 : Real.rpow Δ (-2 * s - t + 5 * ε) / Real.rpow Δ (-s - 30 * ε) =
        Real.rpow Δ (-s - t + 35 * ε) := by rw [h4, h5]
    calc (Real.rpow Δ (-2 * s - t + 5 * ε) / K_pack) / Real.rpow Δ (-s - 30 * ε)
      = (Real.rpow Δ (-2 * s - t + 5 * ε) / Real.rpow Δ (-s - 30 * ε)) / K_pack := by ring
    _ = Real.rpow Δ (-s - t + 35 * ε) / K_pack := by rw [h6]
    _ = (1 / K_pack) * Real.rpow Δ (-s - t + 35 * ε) := by ring
  have h_mul : (6 * Real.rpow Δ (2 * ε)) * Real.rpow Δ (-s - t + 35 * ε) =
      6 * Real.rpow Δ (-s - t + 37 * ε) := by
    have h7 : Real.rpow Δ ((2 * ε) + (-s - t + 35 * ε)) =
        Real.rpow Δ (2 * ε) * Real.rpow Δ (-s - t + 35 * ε) :=
      (rpow_add (2 * ε) (-s - t + 35 * ε)).symm
    have h8 : (2 * ε) + (-s - t + 35 * ε) = -s - t + 37 * ε := by ring
    have h9 : Real.rpow Δ (2 * ε) * Real.rpow Δ (-s - t + 35 * ε) = Real.rpow Δ (-s - t + 37 * ε) := by
      rw [← h7, h8]
    have h10 : 6 * (Real.rpow Δ (2 * ε) * Real.rpow Δ (-s - t + 35 * ε)) =
        6 * Real.rpow Δ (-s - t + 37 * ε) := by rw [h9]
    simpa [mul_assoc] using h10
  have h_num_nonneg : 0 ≤ Real.rpow Δ (-2 * s - t + 5 * ε) := rpow_nonneg _
  calc H_Q
    ≥ M * orig / (K_Q * CQ_card) := h_step1
  _ ≥ (Real.rpow Δ (-2 * s - t + 5 * ε) / K_pack) / (K_Q * CQ_card) := by
      exact div_le_div_of_nonneg_right h_step2 h_den_pos.le
  _ ≥ (Real.rpow Δ (-2 * s - t + 5 * ε) / K_pack) / Real.rpow Δ (-s - 30 * ε) := by
      have hA_nonneg : 0 ≤ Real.rpow Δ (-2 * s - t + 5 * ε) / K_pack :=
        div_nonneg h_num_nonneg hKpack_pos.le
      have h : (Real.rpow Δ (-2 * s - t + 5 * ε) / K_pack) / Real.rpow Δ (-s - 30 * ε) ≤
          (Real.rpow Δ (-2 * s - t + 5 * ε) / K_pack) / (K_Q * CQ_card) := by
        gcongr <;> linarith
      exact h
  _ = (1 / K_pack) * Real.rpow Δ (-s - t + 35 * ε) := h_div
  _ ≥ (6 * Real.rpow Δ (2 * ε)) * Real.rpow Δ (-s - t + 35 * ε) := by
      have h6 : 0 ≤ Real.rpow Δ (-s - t + 35 * ε) := rpow_nonneg _
      exact mul_le_mul_of_nonneg_right h_inv h6
  _ = 6 * Real.rpow Δ (-s - t + 37 * ε) := h_mul

/-- Exact H_Q lower bound: H_Q ≥ Δ^{-s-t+32ε}.
    Uses K_pack ≤ Δ^{-ε} (constant absorption for small Δ). -/
lemma a3_HQ_lower_36ε
    {Δ s t ε M orig K_Q H_Q CQ_card K_pack : ℝ}
    (hΔ_pos : 0 < Δ) (hε_pos : 0 < ε)
    (hM_lower : M ≥ Real.rpow Δ (-2 * s + 2 * ε) / K_pack)
    (horig : Real.rpow Δ (-t + 3 * ε) ≤ orig)
    (hKQ : K_Q ≤ Real.rpow Δ (-ε))
    (hKpack_bound : K_pack ≤ Real.rpow Δ (-ε))
    (hKpack_pos : 0 < K_pack)
    (hcard : CQ_card ≤ Real.rpow Δ (-s - 29 * ε))
    (hbal : M * orig ≤ K_Q * H_Q * CQ_card)
    (hKQ_pos : 0 < K_Q) (hcard_pos : 0 < CQ_card) :
    H_Q ≥ Real.rpow Δ (-s - t + 36 * ε) := by
  have rpow_add : ∀ (x y : ℝ), Real.rpow Δ x * Real.rpow Δ y = Real.rpow Δ (x + y) :=
    fun x y => (Real.rpow_add hΔ_pos x y).symm
  have rpow_nonneg : ∀ (x : ℝ), 0 ≤ Real.rpow Δ x := fun x => Real.rpow_nonneg hΔ_pos.le x
  have rpow_pos : ∀ (x : ℝ), 0 < Real.rpow Δ x := fun x => Real.rpow_pos_of_pos hΔ_pos x
  have h_den_pos : 0 < K_Q * CQ_card := mul_pos hKQ_pos hcard_pos
  have hM_pos : 0 < M := by
    have h : 0 < Real.rpow Δ (-2 * s + 2 * ε) / K_pack := div_pos (rpow_pos _) hKpack_pos
    exact h.trans_le hM_lower
  have h_step1 : H_Q ≥ M * orig / (K_Q * CQ_card) := by
    have h : M * orig / (K_Q * CQ_card) ≤ (K_Q * H_Q * CQ_card) / (K_Q * CQ_card) :=
      div_le_div_of_nonneg_right hbal h_den_pos.le
    have h2 : (K_Q * H_Q * CQ_card) / (K_Q * CQ_card) = H_Q := by
      field_simp [h_den_pos.ne'] <;> ring
    rw [h2] at h; exact h
  have h_step2 : M * orig ≥ Real.rpow Δ (-2 * s - t + 5 * ε) / K_pack := by
    have h1 : (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) * Real.rpow Δ (-t + 3 * ε) ≤ M * orig := by
      calc (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) * Real.rpow Δ (-t + 3 * ε)
          ≤ M * Real.rpow Δ (-t + 3 * ε) := mul_le_mul_of_nonneg_right hM_lower (rpow_nonneg _)
        _ ≤ M * orig := mul_le_mul_of_nonneg_left horig hM_pos.le
    have h2 : (Real.rpow Δ (-2 * s + 2 * ε) * Real.rpow Δ (-t + 3 * ε)) = Real.rpow Δ (-2 * s - t + 5 * ε) := by
      have h3 := rpow_add (-2 * s + 2 * ε) (-t + 3 * ε)
      have h4 : (-2 * s + 2 * ε) + (-t + 3 * ε) = -2 * s - t + 5 * ε := by ring
      rw [h3, h4]
    have h5 : (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) * Real.rpow Δ (-t + 3 * ε) =
        (Real.rpow Δ (-2 * s + 2 * ε) * Real.rpow Δ (-t + 3 * ε)) / K_pack := by ring
    rw [h5, h2] at h1; exact h1
  have h_step3 : K_Q * CQ_card ≤ Real.rpow Δ (-s - 30 * ε) := by
    have h : K_Q * CQ_card ≤ Real.rpow Δ (-ε) * Real.rpow Δ (-s - 29 * ε) := by
      have h1 : K_Q * CQ_card ≤ Real.rpow Δ (-ε) * CQ_card :=
        mul_le_mul_of_nonneg_right hKQ hcard_pos.le
      have h2 : Real.rpow Δ (-ε) * CQ_card ≤ Real.rpow Δ (-ε) * Real.rpow Δ (-s - 29 * ε) :=
        mul_le_mul_of_nonneg_left hcard (rpow_nonneg _)
      exact le_trans h1 h2
    have h2 : Real.rpow Δ (-ε) * Real.rpow Δ (-s - 29 * ε) = Real.rpow Δ (-s - 30 * ε) := by
      have h3 := rpow_add (-ε) (-s - 29 * ε)
      have h4 : (-ε) + (-s - 29 * ε) = -s - 30 * ε := by ring
      rw [h3, h4] <;> rfl
    rw [h2] at h; exact h
  have h_inv : 1 / K_pack ≥ Real.rpow Δ ε := by
    have h1 : 1 / K_pack ≥ 1 / Real.rpow Δ (-ε) := by gcongr <;> linarith
    have h2 : Real.rpow Δ (-ε) * Real.rpow Δ ε = 1 := by
      have h3 := rpow_add (-ε) ε
      have h4 : (-ε) + ε = 0 := by ring
      rw [h3, h4] <;> simp
    have h5 : (Real.rpow Δ (-ε))⁻¹ = Real.rpow Δ ε := by
      exact inv_eq_of_mul_eq_one_right h2
    have h6 : 1 / Real.rpow Δ (-ε) = Real.rpow Δ ε := by
      rw [div_eq_mul_inv, h5] <;> ring
    rw [h6] at h1; exact h1
  have h_div : (Real.rpow Δ (-2 * s - t + 5 * ε) / K_pack) / Real.rpow Δ (-s - 30 * ε) =
      (1 / K_pack) * Real.rpow Δ (-s - t + 35 * ε) := by
    have h4 : Real.rpow Δ (-2 * s - t + 5 * ε) / Real.rpow Δ (-s - 30 * ε) =
        Real.rpow Δ ((-2 * s - t + 5 * ε) - (-s - 30 * ε)) := by
      exact (Real.rpow_sub hΔ_pos (-2 * s - t + 5 * ε) (-s - 30 * ε)).symm
    have h5 : (-2 * s - t + 5 * ε) - (-s - 30 * ε) = -s - t + 35 * ε := by ring
    have h6 : Real.rpow Δ (-2 * s - t + 5 * ε) / Real.rpow Δ (-s - 30 * ε) =
        Real.rpow Δ (-s - t + 35 * ε) := by rw [h4, h5]
    calc (Real.rpow Δ (-2 * s - t + 5 * ε) / K_pack) / Real.rpow Δ (-s - 30 * ε)
      = (Real.rpow Δ (-2 * s - t + 5 * ε) / Real.rpow Δ (-s - 30 * ε)) / K_pack := by ring
    _ = Real.rpow Δ (-s - t + 35 * ε) / K_pack := by rw [h6]
    _ = (1 / K_pack) * Real.rpow Δ (-s - t + 35 * ε) := by ring
  have h_mul : Real.rpow Δ ε * Real.rpow Δ (-s - t + 35 * ε) = Real.rpow Δ (-s - t + 36 * ε) := by
    have h7 := rpow_add ε (-s - t + 35 * ε)
    have h8 : ε + (-s - t + 35 * ε) = -s - t + 36 * ε := by ring
    rw [h7, h8]
  have h_num_nonneg : 0 ≤ Real.rpow Δ (-2 * s - t + 5 * ε) := rpow_nonneg _
  calc H_Q
    ≥ M * orig / (K_Q * CQ_card) := h_step1
  _ ≥ (Real.rpow Δ (-2 * s - t + 5 * ε) / K_pack) / (K_Q * CQ_card) := by
      exact div_le_div_of_nonneg_right h_step2 h_den_pos.le
  _ ≥ (Real.rpow Δ (-2 * s - t + 5 * ε) / K_pack) / Real.rpow Δ (-s - 30 * ε) := by
      have hA_nonneg : 0 ≤ Real.rpow Δ (-2 * s - t + 5 * ε) / K_pack :=
        div_nonneg h_num_nonneg hKpack_pos.le
      have h : (Real.rpow Δ (-2 * s - t + 5 * ε) / K_pack) / Real.rpow Δ (-s - 30 * ε) ≤
          (Real.rpow Δ (-2 * s - t + 5 * ε) / K_pack) / (K_Q * CQ_card) := by
        gcongr <;> linarith
      exact h
  _ = (1 / K_pack) * Real.rpow Δ (-s - t + 35 * ε) := h_div
  _ ≥ Real.rpow Δ ε * Real.rpow Δ (-s - t + 35 * ε) := by
      have h6 : 0 ≤ Real.rpow Δ (-s - t + 35 * ε) := rpow_nonneg _
      exact mul_le_mul_of_nonneg_right h_inv h6
  _ = Real.rpow Δ (-s - t + 36 * ε) := h_mul

/-- Restrict energy bound from all Qset centers to a subset Q0.
    Uses |Qset_all| ≤ Δ^{-ε} · |Q0| from binning. -/
lemma a3_energy_Q0_from_all
    {Δ ε s : ℝ} {Qset_all Q0 : Finset (CoarseSquare Δ)} {bins : Finset (ℤ × ℤ × ℤ)}
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2) (hε_pos : 0 < ε)
    (hQ0_sub : Q0 ⊆ Qset_all)
    (h_card_ratio : (Qset_all.card : ℝ) ≤ (bins.card : ℝ) * (Q0.card : ℝ))
    (h_bins_le : (bins.card : ℝ) ≤ Real.rpow Δ (-ε))
    (h_energy_all : ∑ p ∈ (Qset_all.image (squareCenter Δ)),
        ∑ q ∈ (Qset_all.image (squareCenter Δ)).erase p, Real.rpow (dist p q) (-s) ≤
        Real.rpow Δ (-12 * ε) * ((Qset_all.image (squareCenter Δ)).card : ℝ)^2) :
    ∑ p ∈ (Q0.image (squareCenter Δ)),
        ∑ q ∈ (Q0.image (squareCenter Δ)).erase p, Real.rpow (dist p q) (-s) ≤
        Real.rpow Δ (-14 * ε) * ((Q0.image (squareCenter Δ)).card : ℝ)^2 := by
  let P_all := Qset_all.image (squareCenter Δ)
  let P_Q0 := Q0.image (squareCenter Δ)
  have hP_Q0_sub : P_Q0 ⊆ P_all := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨Q, hQ, rfl⟩
    exact Finset.mem_image.mpr ⟨Q, hQ0_sub hQ, rfl⟩
  have h_inj : Function.Injective (squareCenter Δ) := squareCenter_injective hΔ_pos
  have hP_all_card : P_all.card = Qset_all.card := Finset.card_image_of_injective _ h_inj
  have hP_Q0_card : P_Q0.card = Q0.card := Finset.card_image_of_injective _ h_inj
  have h_nonneg1 : ∀ (p q : Plane), 0 ≤ Real.rpow (dist p q) (-s) := by
    intro p q
    have h : 0 ≤ dist p q := by positivity
    exact Real.rpow_nonneg h _
  have h_inner : ∀ p ∈ P_Q0,
      ∑ q ∈ P_Q0.erase p, Real.rpow (dist p q) (-s) ≤
      ∑ q ∈ P_all.erase p, Real.rpow (dist p q) (-s) := by
    intro p hp
    have h_sub : P_Q0.erase p ⊆ P_all.erase p := Finset.erase_subset_erase p hP_Q0_sub
    exact Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun q _ _ => h_nonneg1 p q)
  have h1 : ∑ p ∈ P_Q0, ∑ q ∈ P_Q0.erase p, Real.rpow (dist p q) (-s) ≤
      ∑ p ∈ P_Q0, ∑ q ∈ P_all.erase p, Real.rpow (dist p q) (-s) :=
    Finset.sum_le_sum h_inner
  have h2 : ∑ p ∈ P_Q0, ∑ q ∈ P_all.erase p, Real.rpow (dist p q) (-s) ≤
      ∑ p ∈ P_all, ∑ q ∈ P_all.erase p, Real.rpow (dist p q) (-s) :=
    Finset.sum_le_sum_of_subset_of_nonneg hP_Q0_sub
      (fun p _ _ => Finset.sum_nonneg (fun q _ => h_nonneg1 p q))
  have h3 : ∑ p ∈ P_all, ∑ q ∈ P_all.erase p, Real.rpow (dist p q) (-s) ≤
      Real.rpow Δ (-12 * ε) * (P_all.card : ℝ)^2 := h_energy_all
  have h4 : (P_all.card : ℝ) ≤ Real.rpow Δ (-ε) * (P_Q0.card : ℝ) := by
    rw [hP_all_card, hP_Q0_card]
    have h5 : (Qset_all.card : ℝ) ≤ Real.rpow Δ (-ε) * (Q0.card : ℝ) := by
      have h6 : (Qset_all.card : ℝ) ≤ (bins.card : ℝ) * (Q0.card : ℝ) := h_card_ratio
      have h7 : (bins.card : ℝ) ≤ Real.rpow Δ (-ε) := h_bins_le
      calc (Qset_all.card : ℝ)
        ≤ (bins.card : ℝ) * (Q0.card : ℝ) := h6
      _ ≤ Real.rpow Δ (-ε) * (Q0.card : ℝ) := by
        have h8 : 0 ≤ (Q0.card : ℝ) := Nat.cast_nonneg Q0.card
        exact mul_le_mul_of_nonneg_right h7 h8
    exact h5
  have h5 : Real.rpow Δ (-12 * ε) * (P_all.card : ℝ)^2 ≤
      Real.rpow Δ (-14 * ε) * (P_Q0.card : ℝ)^2 := by
    have h4' : 0 ≤ (P_all.card : ℝ) := Nat.cast_nonneg P_all.card
    have h_rpow_nonneg : 0 ≤ Real.rpow Δ (-ε) := Real.rpow_nonneg hΔ_pos.le (-ε)
    have h_Q0_nonneg : 0 ≤ (P_Q0.card : ℝ) := Nat.cast_nonneg P_Q0.card
    have h4'' : 0 ≤ Real.rpow Δ (-ε) * (P_Q0.card : ℝ) := mul_nonneg h_rpow_nonneg h_Q0_nonneg
    have h6 : (P_all.card : ℝ)^2 ≤ (Real.rpow Δ (-ε) * (P_Q0.card : ℝ))^2 := by
      nlinarith [h4, h4', h4'']
    have h_pos12 : 0 ≤ Real.rpow Δ (-12 * ε) := Real.rpow_nonneg hΔ_pos.le _
    have h_sq2 : (Real.rpow Δ (-ε))^2 = Real.rpow Δ (-2 * ε) := by
      have h91 : (Real.rpow Δ (-ε))^2 = Real.rpow Δ (-ε) * Real.rpow Δ (-ε) := by
        simp [pow_two]
      rw [h91]
      have h92 : Real.rpow Δ (-ε) * Real.rpow Δ (-ε) = Real.rpow Δ ((-ε) + (-ε)) :=
        (Real.rpow_add hΔ_pos (-ε) (-ε)).symm
      have h93 : (-ε) + (-ε) = -2 * ε := by ring
      rw [h92, h93]
    have h8 : Real.rpow Δ (-12 * ε) * Real.rpow Δ (-2 * ε) = Real.rpow Δ (-14 * ε) := by
      have h9 : Real.rpow Δ (-12 * ε) * Real.rpow Δ (-2 * ε) = Real.rpow Δ ((-12 * ε) + (-2 * ε)) :=
        (Real.rpow_add hΔ_pos (-12 * ε) (-2 * ε)).symm
      have h10 : (-12 * ε) + (-2 * ε) = -14 * ε := by ring
      rw [h9, h10]
    have h7 : Real.rpow Δ (-12 * ε) * (Real.rpow Δ (-ε) * (P_Q0.card : ℝ))^2 =
        Real.rpow Δ (-14 * ε) * (P_Q0.card : ℝ)^2 := by
      have h_sq : (Real.rpow Δ (-ε) * (P_Q0.card : ℝ))^2 =
          (Real.rpow Δ (-ε))^2 * (P_Q0.card : ℝ)^2 := by
        rw [mul_pow] <;> ring
      rw [h_sq, h_sq2, ← mul_assoc, h8]
    have h_step1 : Real.rpow Δ (-12 * ε) * (P_all.card : ℝ)^2 ≤
        Real.rpow Δ (-12 * ε) * (Real.rpow Δ (-ε) * (P_Q0.card : ℝ))^2 :=
      mul_le_mul_of_nonneg_left h6 h_pos12
    calc Real.rpow Δ (-12 * ε) * (P_all.card : ℝ)^2
      ≤ Real.rpow Δ (-12 * ε) * (Real.rpow Δ (-ε) * (P_Q0.card : ℝ))^2 := h_step1
    _ = Real.rpow Δ (-14 * ε) * (P_Q0.card : ℝ)^2 := h7
  calc ∑ p ∈ P_Q0, ∑ q ∈ P_Q0.erase p, Real.rpow (dist p q) (-s)
    ≤ ∑ p ∈ P_Q0, ∑ q ∈ P_all.erase p, Real.rpow (dist p q) (-s) := h1
  _ ≤ ∑ p ∈ P_all, ∑ q ∈ P_all.erase p, Real.rpow (dist p q) (-s) := h2
  _ ≤ Real.rpow Δ (-12 * ε) * (P_all.card : ℝ)^2 := h3
  _ ≤ Real.rpow Δ (-14 * ε) * (P_Q0.card : ℝ)^2 := h5

/-- Canonical A3 uniformization: takes canonical A2_Output + Qset S-set,
    produces canonical A3_Output via dyadic pigeonholing. -/
def A3_uniformize_canonical
    (Δ δ s t ε : ℝ) (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (ht_pos : 0 < t) (ht_lt_two : t < 2)
    (hst : s < t)
    (hΔ_small : 50000 * (Real.log (1 / Δ) + 1)^3 ≤ Real.rpow Δ (-ε))
    -- Constant absorption: 8 * K_pack^2 * (800*7)^s ≤ Δ^{-ε}
    (hΔ_absorb1 : 8 * (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (54 : ℝ)) : ℝ)^s ≤ Real.rpow Δ (-2 * ε))
    -- Constant absorption: 8 * K_pack ≤ Δ^{s-t-19ε} (relaxed from 21ε for Qset bound)
    (hΔ_absorb2 : (8 : ℝ) ≤ Real.rpow Δ (s - t - 22 * ε))
    -- Energy bound requires s ≥ 12ε
    (hs_ge_12ε : 12 * ε ≤ s)
    (a2 : A2_Output Δ δ s t ε)
    (hQset_sset_in : IsDeltaSSet Δ t (Real.rpow Δ (-20 * ε)) (a2.Qset : Set (CoarseSquare Δ)))
    (hC_global_card_upper : (a2.C_global.card : ℝ) ≤ Real.rpow Δ (-2 * s - 3 * ε))
    (hC_Q_sub_global : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a2.Qset),
      (a2.perSquare Q hQ).C_Q ⊆ a2.C_global)
    -- Geometric bounds on square centers
    (hCenter_bound : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a2.Qset), ‖squareCenter Δ Q‖ ≤ 2)
    (hDist_le_3 : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a2.Qset) (R : CoarseSquare Δ) (hR : R ∈ a2.Qset),
      dist (squareCenter Δ Q) (squareCenter Δ R) ≤ 3)
    -- Qset cardinality lower bound
    (hQset_card_lower : (a2.Qset.card : ℝ) ≥ Real.rpow Δ (-t + 3 * ε))
    -- Qset cardinality upper bound
    (hQset_card_upper : (a2.Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε))
    -- Energy bound for all Qset centers (degraded to -12ε due to phys_growth -11ε)
    (h_energy_all : ∑ p ∈ (a2.Qset.image (squareCenter Δ)),
        ∑ q ∈ (a2.Qset.image (squareCenter Δ)).erase p, Real.rpow (dist p q) (-s) ≤
        Real.rpow Δ (-12 * ε) * ((a2.Qset.image (squareCenter Δ)).card : ℝ)^2)
    -- K_pack is a fixed constant, so for small Δ it is ≤ Δ^{-ε}
    (hKpack_ε : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a2.Qset),
      (a2.perSquare Q hQ).K_pack ≤ Real.rpow Δ (-ε))
    -- Physical ball-growth bound for Qset centers (from A2, at -11ε)
    (hQset_phys_growth_in : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((a2.Qset.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).card : ℝ) ≤
        Real.rpow Δ (-11 * ε) * r^t * (a2.Qset.card : ℝ)) :
    A3_Output Δ δ s t ε := by
  let Qset_all := a2.Qset
  have hQset_nonempty : Qset_all.Nonempty := hQset_sset_in.1
  let bin : ℝ → ℤ := fun x => Int.floor (Real.logb 2 x)
  have h_bin_prop : ∀ (x : ℝ), 0 < x →
      (2 : ℝ)^((bin x : ℝ)) ≤ x ∧ x < (2 : ℝ)^((bin x : ℝ) + 1) := by
    intro x hx
    have h1 : (bin x : ℝ) ≤ Real.logb 2 x := Int.floor_le (Real.logb 2 x)
    have h2 : Real.logb 2 x < (bin x : ℝ) + 1 := Int.lt_floor_add_one (Real.logb 2 x)
    have h3 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
    have h3' : (1 : ℝ) < (2 : ℝ) := by norm_num
    have h4 : (2 : ℝ)^((bin x : ℝ)) ≤ (2 : ℝ)^(Real.logb 2 x) :=
      Real.rpow_le_rpow_of_exponent_le h3 h1
    have h5 : (2 : ℝ)^(Real.logb 2 x) < (2 : ℝ)^((bin x : ℝ) + 1) :=
      Real.rpow_lt_rpow_of_exponent_lt h3' h2
    have h6 : (2 : ℝ)^(Real.logb 2 x) = x := by
      rw [Real.rpow_logb] <;> norm_num <;> linarith
    constructor
    · calc (2 : ℝ)^((bin x : ℝ)) ≤ (2 : ℝ)^(Real.logb 2 x) := h4
         _ = x := h6
    · calc x = (2 : ℝ)^(Real.logb 2 x) := h6.symm
         _ < (2 : ℝ)^((bin x : ℝ) + 1) := h5
  let sd (Q : CoarseSquare Δ) (hQ : Q ∈ Qset_all) := a2.perSquare Q hQ
  let binTriple (Q : CoarseSquare Δ) : ℤ × ℤ × ℤ :=
    if hQ : Q ∈ Qset_all then
      (bin (sd Q hQ).K_Q, bin (sd Q hQ).H_Q, bin ((sd Q hQ).C_Q.card : ℝ))
    else (0, 0, 0)
  let bins : Finset (ℤ × ℤ × ℤ) := Qset_all.image binTriple
  let squaresInBin (b : ℤ × ℤ × ℤ) : Finset (CoarseSquare Δ) :=
    Qset_all.filter (fun Q => binTriple Q = b)
  have h_bins_nonempty : bins.Nonempty := hQset_nonempty.image binTriple
  have h_exists_max : ∃ (b : ℤ × ℤ × ℤ), b ∈ bins ∧ ∀ b' ∈ bins, (squaresInBin b').card ≤ (squaresInBin b).card :=
    Finset.exists_max_image bins (fun b => (squaresInBin b).card) h_bins_nonempty
  let b_max := Classical.choose h_exists_max
  have hb_max_spec : b_max ∈ bins ∧ ∀ b' ∈ bins, (squaresInBin b').card ≤ (squaresInBin b_max).card :=
    Classical.choose_spec h_exists_max
  have hb_max_in : b_max ∈ bins := hb_max_spec.1
  have hb_max : ∀ b' ∈ bins, (squaresInBin b').card ≤ (squaresInBin b_max).card := hb_max_spec.2
  let Q0 := squaresInBin b_max
  have hQ0_sub : Q0 ⊆ Qset_all := Finset.filter_subset _ _
  have hQ0_nonempty : Q0.Nonempty := by
    rcases Finset.mem_image.mp hb_max_in with ⟨Q, hQ, h_eq⟩
    exact ⟨Q, Finset.mem_filter.mpr ⟨hQ, h_eq⟩⟩
  let K_uniform : ℝ := (2 : ℝ)^((b_max.1 : ℝ))
  let H_uniform : ℝ := (2 : ℝ)^((b_max.2.1 : ℝ))
  let C_card_uniform : ℝ := (2 : ℝ)^((b_max.2.2 : ℝ))
  let C2_uniform : ℝ := Real.rpow Δ (-10 * ε)
  have h_bin_eq : ∀ Q ∈ Q0, binTriple Q = b_max := by
    intro Q hQ; exact (Finset.mem_filter.mp hQ).2
  have hC_card_pos : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0), 0 < ((sd Q (hQ0_sub hQ)).C_Q.card : ℝ) := by
    intro Q hQ
    have h : Real.rpow Δ (-s + 11 * ε) ≤ ((sd Q (hQ0_sub hQ)).C_Q.card : ℝ) :=
      (sd Q (hQ0_sub hQ)).hC_card_lower
    have hpos1 : 0 < Real.rpow Δ (-s + 11 * ε) := Real.rpow_pos_of_pos hΔ_pos (-s + 11 * ε)
    exact lt_of_lt_of_le hpos1 h
  have h_binTriple_eq : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Qset_all),
      binTriple Q = (bin (sd Q hQ).K_Q, bin (sd Q hQ).H_Q, bin ((sd Q hQ).C_Q.card : ℝ)) := by
    intro Q hQ
    simp [binTriple, hQ]
  have h_rpow2_succ : ∀ (k : ℝ), (2 : ℝ)^(k + 1) = 2 * (2 : ℝ)^k := by
    intro k
    have h : (2 : ℝ)^(k + 1) = (2 : ℝ)^k * (2 : ℝ)^(1 : ℝ) := by
      rw [Real.rpow_add] <;> norm_num
    rw [h]
    have h2 : (2 : ℝ)^(1 : ℝ) = 2 := by simp
    rw [h2] <;> ring
  have hK_direct : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0),
      K_uniform ≤ (sd Q (hQ0_sub hQ)).K_Q ∧ (sd Q (hQ0_sub hQ)).K_Q < 2 * K_uniform := by
    intro Q hQ
    let hQ' := hQ0_sub hQ
    have h7 : bin (sd Q hQ').K_Q = b_max.1 := by
      have h_binT := h_binTriple_eq Q hQ'
      have h_eq2 := h_bin_eq Q hQ
      rw [h_binT] at h_eq2
      have h : (bin (sd Q hQ').K_Q, bin (sd Q hQ').H_Q, bin ((sd Q hQ').C_Q.card : ℝ)).1 = b_max.1 :=
        congr_arg (fun p : ℤ × ℤ × ℤ => p.1) h_eq2
      simpa using h
    have h8 := h_bin_prop (sd Q hQ').K_Q (sd Q hQ').hK_Q_pos
    have h9 : K_uniform = (2 : ℝ)^((bin (sd Q hQ').K_Q : ℝ)) := by rw [h7] <;> rfl
    have h10 := h_rpow2_succ ((bin (sd Q hQ').K_Q : ℝ))
    constructor
    · rw [h9]; exact h8.1
    · rw [h9]; rw [h10] at h8; exact h8.2
  have hH_direct : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0),
      H_uniform ≤ (sd Q (hQ0_sub hQ)).H_Q ∧ (sd Q (hQ0_sub hQ)).H_Q < 2 * H_uniform := by
    intro Q hQ
    let hQ' := hQ0_sub hQ
    have h7 : bin (sd Q hQ').H_Q = b_max.2.1 := by
      have h_binT := h_binTriple_eq Q hQ'
      have h_eq2 := h_bin_eq Q hQ
      rw [h_binT] at h_eq2
      have h : (bin (sd Q hQ').K_Q, bin (sd Q hQ').H_Q, bin ((sd Q hQ').C_Q.card : ℝ)).2.1 = b_max.2.1 :=
        congr_arg (fun p : ℤ × ℤ × ℤ => p.2.1) h_eq2
      simpa using h
    have h8 := h_bin_prop (sd Q hQ').H_Q (sd Q hQ').hH_Q_pos
    have h9 : H_uniform = (2 : ℝ)^((bin (sd Q hQ').H_Q : ℝ)) := by rw [h7] <;> rfl
    have h10 := h_rpow2_succ ((bin (sd Q hQ').H_Q : ℝ))
    constructor
    · rw [h9]; exact h8.1
    · rw [h9]; rw [h10] at h8; exact h8.2
  have hC_direct : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0),
      C_card_uniform ≤ ((sd Q (hQ0_sub hQ)).C_Q.card : ℝ) ∧ ((sd Q (hQ0_sub hQ)).C_Q.card : ℝ) < 2 * C_card_uniform := by
    intro Q hQ
    let hQ' := hQ0_sub hQ
    have h7 : bin ((sd Q hQ').C_Q.card : ℝ) = b_max.2.2 := by
      have h_binT := h_binTriple_eq Q hQ'
      have h_eq2 := h_bin_eq Q hQ
      rw [h_binT] at h_eq2
      have h : (bin (sd Q hQ').K_Q, bin (sd Q hQ').H_Q, bin ((sd Q hQ').C_Q.card : ℝ)).2.2 = b_max.2.2 :=
        congr_arg (fun p : ℤ × ℤ × ℤ => p.2.2) h_eq2
      simpa using h
    have h8 := h_bin_prop ((sd Q hQ').C_Q.card : ℝ) (hC_card_pos Q hQ)
    have h9 : C_card_uniform = (2 : ℝ)^((bin ((sd Q hQ').C_Q.card : ℝ) : ℝ)) := by rw [h7] <;> rfl
    have h10 := h_rpow2_succ ((bin ((sd Q hQ').C_Q.card : ℝ) : ℝ))
    constructor
    · rw [h9]; exact h8.1
    · rw [h9]; rw [h10] at h8; exact h8.2
  have hK_uniform' : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0),
      (sd Q (hQ0_sub hQ)).K_Q ∈ Set.Icc (K_uniform / 2) (2 * K_uniform) := by
    intro Q hQ
    have h10 := hK_direct Q hQ
    constructor
    · linarith
    · linarith
  have hH_uniform' : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0),
      (sd Q (hQ0_sub hQ)).H_Q ∈ Set.Icc (H_uniform / 2) (2 * H_uniform) := by
    intro Q hQ
    have h10 := hH_direct Q hQ
    constructor
    · linarith
    · linarith
  have hC_card_uniform' : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0),
      ((sd Q (hQ0_sub hQ)).C_Q.card : ℝ) ∈ Set.Icc (C_card_uniform / 2) (2 * C_card_uniform) := by
    intro Q hQ
    have h10 := hC_direct Q hQ
    constructor
    · linarith
    · linarith
  have hΔ_ε_le_half : Real.rpow Δ ε ≤ 1 / 2 := by
    have h1 : 0 < Real.log (1 / Δ) := by
      have h2 : (1 : ℝ) < 1 / Δ := by
        have h3 : 0 < Δ := hΔ_pos
        have h4 : Δ < 1 := by linarith [hΔ_lt_half]
        have h5 : 1 / Δ > 1 := by apply one_lt_one_div <;> linarith
        exact h5
      exact Real.log_pos h2
    have h2 : 1 < (Real.log (1 / Δ) + 1)^3 := by
      have h3 : 1 < Real.log (1 / Δ) + 1 := by linarith
      have h4 : 0 ≤ Real.log (1 / Δ) + 1 := by linarith
      have h5 : (1 : ℝ)^3 < (Real.log (1 / Δ) + 1)^3 := by
        gcongr
        <;> linarith
      simpa using h5
    have h3 : (50000 : ℝ) < Real.rpow Δ (-ε) := by
      have h_pos50k : (0 : ℝ) < 50000 := by norm_num
      have h_mul : (50000 : ℝ) < 50000 * (Real.log (1 / Δ) + 1)^3 := by
        have h : (50000 : ℝ) = 50000 * 1 := by ring
        rw [h]
        have h' : 50000 * 1 < 50000 * (Real.log (1 / Δ) + 1)^3 := mul_lt_mul_of_pos_left h2 h_pos50k
        simpa using h'
      exact h_mul.trans_le hΔ_small
    have h4 : Real.rpow Δ (-ε) > 2 := by linarith
    have h5 : Real.rpow Δ ε = (Real.rpow Δ (-ε))⁻¹ := by
      have h_mult : Real.rpow Δ ε * Real.rpow Δ (-ε) = 1 := by
        have h_add : Real.rpow Δ (ε + (-ε)) = Real.rpow Δ ε * Real.rpow Δ (-ε) := Real.rpow_add hΔ_pos ε (-ε)
        have h_zero : ε + (-ε) = 0 := by ring
        rw [h_zero] at h_add
        have h_rpow0 : Real.rpow Δ 0 = 1 := by simp
        rw [h_rpow0] at h_add
        exact h_add.symm
      have h_pos : 0 < Real.rpow Δ ε := Real.rpow_pos_of_pos hΔ_pos ε
      have h_pos2 : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos hΔ_pos (-ε)
      field_simp [h_pos.ne', h_pos2.ne']
      <;> exact h_mult
    rw [h5]
    have h8 : (Real.rpow Δ (-ε))⁻¹ ≤ 1 / 2 := by
      have h9 : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos hΔ_pos (-ε)
      have h10 : (Real.rpow Δ (-ε))⁻¹ ≤ (2 : ℝ)⁻¹ := by gcongr <;> linarith
      simpa using h10
    exact h8
  -- hC_global_card_upper is given as a hypothesis (direct cardinality bound).
  -- Tight card bound will be proved after h_bins_le using a3_card_bound_genuine
  have hK_loss' : K_uniform ≤ Real.rpow Δ (-ε) := by
    rcases hQ0_nonempty with ⟨Q, hQ⟩
    have h9 : K_uniform ≤ (sd Q (hQ0_sub hQ)).K_Q := (hK_direct Q hQ).1
    have h10 : (sd Q (hQ0_sub hQ)).K_Q ≤ Real.rpow Δ (-ε) :=
      (sd Q (hQ0_sub hQ)).hK_Q_loss
    linarith
  have hC_card_exp_lower' : Real.rpow Δ (-s + 12 * ε) ≤ C_card_uniform := by
    rcases hQ0_nonempty with ⟨Q, hQ⟩
    let hQ' := hQ0_sub hQ
    have h1 : ((sd Q hQ').C_Q.card : ℝ) < 2 * C_card_uniform := (hC_direct Q hQ).2
    have h2 : ((sd Q hQ').C_Q.card : ℝ) ≥ Real.rpow Δ (-s + 11 * ε) := (sd Q hQ').hC_card_lower
    have h3 : C_card_uniform > Real.rpow Δ (-s + 11 * ε) / 2 := by linarith
    have h4 : Real.rpow Δ (-s + 11 * ε) / 2 ≥ Real.rpow Δ (-s + 12 * ε) := by
      have h_add : (-s + 11 * ε) + ε = -s + 12 * ε := by ring
      have h_rpow : Real.rpow Δ ((-s + 11 * ε) + ε) =
          Real.rpow Δ (-s + 11 * ε) * Real.rpow Δ ε := Real.rpow_add hΔ_pos _ _
      have h5 : Real.rpow Δ (-s + 12 * ε) = Real.rpow Δ (-s + 11 * ε) * Real.rpow Δ ε := by
        rw [h_add] at h_rpow
        exact h_rpow
      rw [h5]
      have h6 : 0 ≤ Real.rpow Δ (-s + 11 * ε) := Real.rpow_nonneg hΔ_pos.le _
      have h7 : Real.rpow Δ ε ≤ 1 / 2 := hΔ_ε_le_half
      nlinarith
    linarith
  -- hC_card_exp_upper' will be proved after h_tight_card
  let K' (Q : CoarseSquare Δ) : ℝ := if hQ : Q ∈ Qset_all then (sd Q hQ).K_Q else 0
  let H' (Q : CoarseSquare Δ) : ℝ := if hQ : Q ∈ Qset_all then (sd Q hQ).H_Q else 0
  let C' (Q : CoarseSquare Δ) : ℝ := if hQ : Q ∈ Qset_all then ((sd Q hQ).C_Q.card : ℝ) else 0
  have hK'_lower : ∀ Q ∈ Qset_all, Real.rpow Δ (2 * ε) ≤ K' Q := by
    intro Q hQ; simp [K', hQ]; exact (sd Q hQ).hK_Q_lower
  have hK'_upper : ∀ Q ∈ Qset_all, K' Q ≤ Real.rpow Δ (-ε) := by
    intro Q hQ; simp [K', hQ]; exact (sd Q hQ).hK_Q_loss
  have hH'_lower : ∀ Q ∈ Qset_all, Real.rpow Δ 0 ≤ H' Q := by
    intro Q hQ
    have hH_eq : H' Q = (sd Q hQ).H_Q := by simp [H', hQ]
    rw [hH_eq]
    exact a3_H_Q_lower_weak (sd Q hQ) hΔ_pos hΔ_lt_half
  have hH'_upper : ∀ Q ∈ Qset_all, H' Q ≤ Real.rpow Δ (-(s + t) - 10 * ε) := by
    intro Q hQ
    have h_eq : H' Q = (sd Q hQ).H_Q := by simp [H', hQ]
    have h_ineq : (sd Q hQ).H_Q ≤ Real.rpow Δ (-(s + t) - 10 * ε) := by
      have h_tmp : (sd Q hQ).H_Q ≤ Real.rpow Δ (-t - s - 10 * ε) := (sd Q hQ).hH_Q_upper
      have h_exp : (-t - s - 10 * ε) = (-(s + t) - 10 * ε) := by ring
      rw [h_exp] at h_tmp
      exact h_tmp
    rw [h_eq]
    exact h_ineq
  have hC'_lower : ∀ Q ∈ Qset_all, Real.rpow Δ (-s + 11 * ε) ≤ C' Q := by
    intro Q hQ; simp [C', hQ]; exact (sd Q hQ).hC_card_lower
  have hC'_upper : ∀ Q ∈ Qset_all, C' Q ≤ Real.rpow Δ (-1 - 5 * ε) := by
    intro Q hQ; simp [C', hQ]; exact (sd Q hQ).hC_card_upper_weak
  have hbin' : ∀ Q ∈ Qset_all, binTriple Q = (bin (K' Q), bin (H' Q), bin (C' Q)) := by
    intro Q hQ
    simp [binTriple, K', H', C', hQ, dif_pos hQ] <;> rfl
  have h_bins_bound : (bins.card : ℝ) ≤ 50000 * (Real.log (1 / Δ) + 1)^3 :=
    a3_bin_count_bound_weak hΔ_pos hΔ_lt_half hε_pos hε_lt_one
      hs_pos.le hs_lt_one ht_pos.le ht_lt_two
      hK'_lower hK'_upper hH'_lower hH'_upper hC'_lower hC'_upper binTriple hbin'
  have h1 : Qset_all = bins.biUnion squaresInBin := by
    ext Q; simp only [Finset.mem_biUnion, bins, squaresInBin]
    constructor
    · intro hQ; exact ⟨binTriple Q, Finset.mem_image.mpr ⟨Q, hQ, rfl⟩, Finset.mem_filter.mpr ⟨hQ, rfl⟩⟩
    · rintro ⟨b, _, hQ⟩; exact (Finset.mem_filter.mp hQ).1
  have h_card_ratio : (Qset_all.card : ℝ) ≤ (bins.card : ℝ) * (Q0.card : ℝ) := by
    have h2 : Qset_all.card ≤ ∑ b ∈ bins, (squaresInBin b).card := by
      rw [h1]
      exact Finset.card_biUnion_le
    have h3 : ∑ b ∈ bins, (squaresInBin b).card ≤ bins.card * Q0.card := by
      calc
        ∑ b ∈ bins, (squaresInBin b).card
          ≤ ∑ _ ∈ bins, Q0.card := Finset.sum_le_sum fun i _ => hb_max i ‹_›
        _ = bins.card * Q0.card := by
          rw [Finset.sum_const]
          <;> rfl
    have h4 : Qset_all.card ≤ bins.card * Q0.card := h2.trans h3
    have h5 : (Qset_all.card : ℝ) ≤ ↑(bins.card * Q0.card) := Nat.cast_le.mpr h4
    have h6 : (↑(bins.card * Q0.card) : ℝ) = (bins.card : ℝ) * (Q0.card : ℝ) := by
      rw [Nat.cast_mul]
    rw [h6] at h5
    exact h5
  have h_cover_eq := a3_covering_eq hΔ_pos hΔ_lt_half
  have h_bins_le : (bins.card : ℝ) ≤ Real.rpow Δ (-ε) := by
    calc
      (bins.card : ℝ) ≤ 50000 * (Real.log (1 / Δ) + 1)^3 := h_bins_bound
      _ ≤ Real.rpow Δ (-ε) := hΔ_small
  have hQset_sset' : IsDeltaSSet Δ t (Real.rpow Δ (-25 * ε)) (Q0 : Set (CoarseSquare Δ)) := by
    have h_pos : 0 < Real.rpow Δ (-25 * ε) := Real.rpow_pos_of_pos hΔ_pos (-25 * ε)
    have ht_nonneg : 0 ≤ t := hQset_sset_in.2.2.2.1
    refine ⟨hQ0_nonempty, hΔ_pos, h_pos, ht_nonneg, fun x r hr => ?_⟩
    have h_sset_all : (Metric.externalCoveringNumber Δ.toNNReal ((Qset_all : Set (CoarseSquare Δ)) ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal (Real.rpow Δ (-20 * ε)) * (ENNReal.ofReal r) ^ t *
          (Metric.externalCoveringNumber Δ.toNNReal (Qset_all : Set (CoarseSquare Δ)) : ENNReal) :=
      hQset_sset_in.2.2.2.2 x r hr
    have h_mono : (Metric.externalCoveringNumber Δ.toNNReal ((Q0 : Set (CoarseSquare Δ)) ∩ Metric.closedBall x r) : ENNReal) ≤
        (Metric.externalCoveringNumber Δ.toNNReal ((Qset_all : Set (CoarseSquare Δ)) ∩ Metric.closedBall x r) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set (by gcongr)
    have h_cover_all : (Metric.externalCoveringNumber Δ.toNNReal (Qset_all : Set (CoarseSquare Δ)) : ENNReal) = ↑Qset_all.card := by
      exact_mod_cast h_cover_eq Qset_all
    have h_cover_Q0 : (Metric.externalCoveringNumber Δ.toNNReal (Q0 : Set (CoarseSquare Δ)) : ENNReal) = ↑Q0.card := by
      exact_mod_cast h_cover_eq Q0
    calc
      (Metric.externalCoveringNumber Δ.toNNReal ((Q0 : Set (CoarseSquare Δ)) ∩ Metric.closedBall x r) : ENNReal)
        ≤ (Metric.externalCoveringNumber Δ.toNNReal ((Qset_all : Set (CoarseSquare Δ)) ∩ Metric.closedBall x r) : ENNReal) := h_mono
      _ ≤ ENNReal.ofReal (Real.rpow Δ (-20 * ε)) * (ENNReal.ofReal r) ^ t *
            (Metric.externalCoveringNumber Δ.toNNReal (Qset_all : Set (CoarseSquare Δ)) : ENNReal) := h_sset_all
      _ = ENNReal.ofReal (Real.rpow Δ (-20 * ε)) * (ENNReal.ofReal r) ^ t * ↑Qset_all.card := by
        rw [h_cover_all]
      _ ≤ ENNReal.ofReal (Real.rpow Δ (-20 * ε)) * (ENNReal.ofReal r) ^ t *
            (ENNReal.ofReal (Real.rpow Δ (-ε)) * ↑Q0.card) := by
        have h41 : (Qset_all.card : ℝ) ≤ Real.rpow Δ (-ε) * (Q0.card : ℝ) := by
          have h_card : (Qset_all.card : ℝ) ≤ (bins.card : ℝ) * (Q0.card : ℝ) := h_card_ratio
          have h_nonneg : 0 ≤ (Q0.card : ℝ) := Nat.cast_nonneg Q0.card
          have h_mul : (bins.card : ℝ) * (Q0.card : ℝ) ≤ Real.rpow Δ (-ε) * (Q0.card : ℝ) :=
            mul_le_mul_of_nonneg_right h_bins_le h_nonneg
          exact h_card.trans h_mul
        have h42 : (↑Qset_all.card : ENNReal) = ENNReal.ofReal (Qset_all.card : ℝ) := by simp
        have h44 : 0 ≤ Real.rpow Δ (-ε) := Real.rpow_nonneg hΔ_pos.le (-ε)
        have h45 : 0 ≤ (Q0.card : ℝ) := Nat.cast_nonneg Q0.card
        have h43 : ENNReal.ofReal (Real.rpow Δ (-ε)) * (↑Q0.card : ENNReal) = ENNReal.ofReal (Real.rpow Δ (-ε) * (Q0.card : ℝ)) := by
          have h_card_cast : (↑Q0.card : ENNReal) = ENNReal.ofReal (Q0.card : ℝ) := by simp
          rw [h_card_cast]
          rw [← ENNReal.ofReal_mul h44]
        have h4 : (↑Qset_all.card : ENNReal) ≤ ENNReal.ofReal (Real.rpow Δ (-ε)) * ↑Q0.card := by
          rw [h42, h43]
          exact ENNReal.ofReal_le_ofReal h41
        have h_left : 0 ≤ ENNReal.ofReal (Real.rpow Δ (-20 * ε)) * (ENNReal.ofReal r) ^ t := by positivity
        exact mul_le_mul_of_nonneg_left h4 h_left
      _ = ENNReal.ofReal (Real.rpow Δ (-21 * ε)) * (ENNReal.ofReal r) ^ t * ↑Q0.card := by
        have h5 : Real.rpow Δ (-21 * ε) = Real.rpow Δ (-20 * ε) * Real.rpow Δ (-ε) := by
          have h51 : (-21 * ε) = (-20 * ε) + (-ε) := by ring
          rw [h51]
          exact Real.rpow_add hΔ_pos (-20 * ε) (-ε)
        have h53 : 0 ≤ Real.rpow Δ (-20 * ε) := Real.rpow_nonneg hΔ_pos.le (-20 * ε)
        have h52 : ENNReal.ofReal (Real.rpow Δ (-20 * ε)) * ENNReal.ofReal (Real.rpow Δ (-ε)) =
            ENNReal.ofReal (Real.rpow Δ (-21 * ε)) := by
          rw [← ENNReal.ofReal_mul h53, h5] <;> rfl
        have h_assoc : ENNReal.ofReal (Real.rpow Δ (-20 * ε)) * (ENNReal.ofReal r) ^ t * (ENNReal.ofReal (Real.rpow Δ (-ε)) * ↑Q0.card)
            = (ENNReal.ofReal (Real.rpow Δ (-20 * ε)) * ENNReal.ofReal (Real.rpow Δ (-ε))) * ((ENNReal.ofReal r) ^ t * ↑Q0.card) := by
          simp only [mul_assoc] <;> ring
        rw [h_assoc, h52] <;> simp only [mul_assoc]
      _ = ENNReal.ofReal (Real.rpow Δ (-21 * ε)) * (ENNReal.ofReal r) ^ t *
            (Metric.externalCoveringNumber Δ.toNNReal (Q0 : Set (CoarseSquare Δ)) : ENNReal) := by rw [h_cover_Q0]
      _ ≤ ENNReal.ofReal (Real.rpow Δ (-25 * ε)) * (ENNReal.ofReal r) ^ t *
            (Metric.externalCoveringNumber Δ.toNNReal (Q0 : Set (CoarseSquare Δ)) : ENNReal) := by
        have h6 : Real.rpow Δ (-21 * ε) ≤ Real.rpow Δ (-25 * ε) := by
          have h61 : (-25 * ε) ≤ (-21 * ε) := by linarith
          exact Real.rpow_le_rpow_of_exponent_ge hΔ_pos (by linarith) h61
        have h62 : ENNReal.ofReal (Real.rpow Δ (-21 * ε)) ≤ ENNReal.ofReal (Real.rpow Δ (-25 * ε)) :=
          ENNReal.ofReal_le_ofReal h6
        have h63 : ENNReal.ofReal (Real.rpow Δ (-21 * ε)) * ((ENNReal.ofReal r) ^ t * (Metric.externalCoveringNumber Δ.toNNReal (Q0 : Set (CoarseSquare Δ)) : ENNReal)) ≤
            ENNReal.ofReal (Real.rpow Δ (-25 * ε)) * ((ENNReal.ofReal r) ^ t * (Metric.externalCoveringNumber Δ.toNNReal (Q0 : Set (CoarseSquare Δ)) : ENNReal)) :=
          have h_right : 0 ≤ (ENNReal.ofReal r) ^ t * (Metric.externalCoveringNumber Δ.toNNReal (Q0 : Set (CoarseSquare Δ)) : ENNReal) := by positivity
          mul_le_mul_of_nonneg_right h62 h_right
        simpa [mul_assoc] using h63
  -- =====================================================================
  -- Card bound via a3_card_bound_genuine
  -- =====================================================================
  have hQ0_card_lower : (Q0.card : ℝ) ≥ (Qset_all.card : ℝ) / Real.rpow Δ (-ε) := by
    have h : (Qset_all.card : ℝ) ≤ (bins.card : ℝ) * (Q0.card : ℝ) := h_card_ratio
    have h2 : (bins.card : ℝ) ≤ Real.rpow Δ (-ε) := h_bins_le
    have h3 : 0 ≤ (Q0.card : ℝ) := Nat.cast_nonneg Q0.card
    have h4 : (Qset_all.card : ℝ) ≤ Real.rpow Δ (-ε) * (Q0.card : ℝ) :=
      calc (Qset_all.card : ℝ)
        ≤ (bins.card : ℝ) * (Q0.card : ℝ) := h
      _ ≤ Real.rpow Δ (-ε) * (Q0.card : ℝ) := mul_le_mul_of_nonneg_right h2 h3
    have h5 : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h6 : (Qset_all.card : ℝ) / Real.rpow Δ (-ε) ≤ (Q0.card : ℝ) := by
      calc (Qset_all.card : ℝ) / Real.rpow Δ (-ε)
        ≤ (Real.rpow Δ (-ε) * (Q0.card : ℝ)) / Real.rpow Δ (-ε) := by gcongr
      _ = (Q0.card : ℝ) := by
        field_simp [h5.ne'] <;> ring
    exact h6
  have h_energy_Q0 : ∑ p ∈ (Q0.image (squareCenter Δ)),
      ∑ q ∈ (Q0.image (squareCenter Δ)).erase p, Real.rpow (dist p q) (-s) ≤
      Real.rpow Δ (-14 * ε) * ((Q0.image (squareCenter Δ)).card : ℝ)^2 :=
    a3_energy_Q0_from_all
      (hΔ_pos := hΔ_pos) (hΔ_lt_half := hΔ_lt_half) (hε_pos := hε_pos)
      (hQ0_sub := hQ0_sub) (h_card_ratio := h_card_ratio) (h_bins_le := h_bins_le)
      (h_energy_all := h_energy_all)
  have h_card_absorb_genuine : (8 * (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (54 : ℝ)) : ℝ)^s) * (1 : ℝ) *
      Real.rpow Δ (-s - 27 * ε) ≤ Real.rpow Δ (-s - 29 * ε) := by
    have h_pos : 0 < Real.rpow Δ (-s - 27 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h : (8 * (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (54 : ℝ)) : ℝ)^s) ≤ Real.rpow Δ (-2 * ε) := hΔ_absorb1
    have h2 : Real.rpow Δ (-2 * ε) * Real.rpow Δ (-s - 27 * ε) = Real.rpow Δ (-s - 29 * ε) := by
      have h3 := Real.rpow_add hΔ_pos (-2 * ε) (-s - 27 * ε)
      have h4 : (-2 * ε) + (-s - 27 * ε) = -s - 29 * ε := by ring
      rw [h4] at h3; exact h3.symm
    have h_main : (8 * (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (54 : ℝ)) : ℝ)^s) * (1 : ℝ) * Real.rpow Δ (-s - 27 * ε) =
        (8 * (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (54 : ℝ)) : ℝ)^s) * Real.rpow Δ (-s - 27 * ε) := by ring
    rw [h_main]
    calc (8 * (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (54 : ℝ)) : ℝ)^s) * Real.rpow Δ (-s - 27 * ε)
      ≤ Real.rpow Δ (-2 * ε) * Real.rpow Δ (-s - 27 * ε) := by gcongr
    _ = Real.rpow Δ (-s - 29 * ε) := h2
  have h_card_absorb_smallK : (8 : ℝ) * (1 : ℝ) *
      Real.rpow Δ (t - 2 * s - 7 * ε) ≤ Real.rpow Δ (-s - 29 * ε) := by
    have h_pos : 0 < Real.rpow Δ (t - 2 * s - 7 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h : (8 : ℝ) ≤ Real.rpow Δ (s - t - 22 * ε) := hΔ_absorb2
    have h2 : Real.rpow Δ (s - t - 22 * ε) * Real.rpow Δ (t - 2 * s - 7 * ε) = Real.rpow Δ (-s - 29 * ε) := by
      have h3 := Real.rpow_add hΔ_pos (s - t - 22 * ε) (t - 2 * s - 7 * ε)
      have h4 : (s - t - 22 * ε) + (t - 2 * s - 7 * ε) = -s - 29 * ε := by ring
      rw [h4] at h3; exact h3.symm
    have h_rpow_pos : 0 < Real.rpow Δ (t - 2 * s - 7 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h_main : (8 : ℝ) * (1 : ℝ) * Real.rpow Δ (t - 2 * s - 7 * ε) =
        (8 : ℝ) * Real.rpow Δ (t - 2 * s - 7 * ε) := by ring
    rw [h_main]
    calc (8 : ℝ) * Real.rpow Δ (t - 2 * s - 7 * ε)
      ≤ Real.rpow Δ (s - t - 22 * ε) * Real.rpow Δ (t - 2 * s - 7 * ε) :=
        mul_le_mul_of_nonneg_right h h_rpow_pos.le
    _ = Real.rpow Δ (-s - 29 * ε) := h2
  have hC_card_uniform_pos : 0 < C_card_uniform := by
    rcases hQ0_nonempty with ⟨Q, hQ⟩
    have h1 : ((sd Q (hQ0_sub hQ)).C_Q.card : ℝ) < 2 * C_card_uniform := (hC_direct Q hQ).2
    have h2 : 0 < ((sd Q (hQ0_sub hQ)).C_Q.card : ℝ) := hC_card_pos Q hQ
    have h3 : 0 < 2 * C_card_uniform := lt_trans h2 h1
    linarith
  have h_tight_card : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0),
      ((sd Q (hQ0_sub hQ)).C_Q.card : ℝ) ≤ Real.rpow Δ (-s - 29 * ε) :=
    a3_card_bound_genuine
      (hΔ_pos := hΔ_pos) (hΔ_lt_half := hΔ_lt_half) (hδ_pos := hδ_pos) (hδ_le_Δ := hδ_le_Δ)
      (hε_pos := hε_pos) (hs_pos := hs_pos) (hs_lt_one := hs_lt_one)
      (ht_pos := ht_pos) (hst := hst)
      (sd := sd) (hQ0_sub := hQ0_sub) (hQ0_nonempty := hQ0_nonempty)
      (C_card_uniform := C_card_uniform) (hC_card_pos := hC_card_uniform_pos)
      (hC_direct := hC_direct) (K_card := (1 : ℝ)) (hK_card_pos := by norm_num)
      (C_global := a2.C_global)
      (hC_global_card_upper := by simpa [mul_one] using hC_global_card_upper)
      (hC_Q_sub_global := fun Q hQ => hC_Q_sub_global Q (hQ0_sub hQ))
      (hCenter_bound := fun Q hQ => hCenter_bound Q (hQ0_sub hQ))
      (hDist_le_3 := fun Q hQ R hR => hDist_le_3 Q (hQ0_sub hQ) R (hQ0_sub hR))
      (h_energy := h_energy_Q0)
      (hQ0_card_lower := hQ0_card_lower) (hQset_card_lower := hQset_card_lower)
      (h_card_absorb_genuine := h_card_absorb_genuine)
      (h_card_absorb_smallK := h_card_absorb_smallK)
  -- =====================================================================
  -- H_Q lower bound via a3_HQ_lower_36ε (uses K_pack ≤ Δ^{-ε})
  -- =====================================================================
  have hH_Q_lower' : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0),
      (sd Q (hQ0_sub hQ)).H_Q ≥ Real.rpow Δ (-s - t + 36 * ε) := by
    intro Q hQ
    let sdQ := sd Q (hQ0_sub hQ)
    exact a3_HQ_lower_36ε
        (hΔ_pos := hΔ_pos) (hε_pos := hε_pos)
        (hM_lower := sdQ.hM_lower)
        (horig := sdQ.horigPointsCard_lower)
        (hKQ := sdQ.hK_Q_loss)
        (hKpack_bound := hKpack_ε Q (hQ0_sub hQ))
        (hKpack_pos := sdQ.hKpack_pos)
        (hcard := h_tight_card Q hQ)
        (hbal := sdQ.h_balance_lower)
        (hKQ_pos := sdQ.hK_Q_pos)
        (hcard_pos := hC_card_pos Q hQ)
  have hC_card_exp_upper' : C_card_uniform ≤ Real.rpow Δ (-s - 29 * ε) := by
    rcases hQ0_nonempty with ⟨Q, hQ⟩
    have h9 : C_card_uniform ≤ ((sd Q (hQ0_sub hQ)).C_Q.card : ℝ) := (hC_direct Q hQ).1
    have h10 : ((sd Q (hQ0_sub hQ)).C_Q.card : ℝ) ≤ Real.rpow Δ (-s - 29 * ε) := h_tight_card Q hQ
    exact le_trans h9 h10
  have hH_uniform_lower' : H_uniform ≥ Real.rpow Δ (-(s + t) + 37 * ε) := by
    rcases hQ0_nonempty with ⟨Q, hQ⟩
    let hQ' := hQ0_sub hQ
    have h1 : (sd Q hQ').H_Q < 2 * H_uniform := (hH_direct Q hQ).2
    have h2 : (sd Q hQ').H_Q ≥ Real.rpow Δ (-s - t + 36 * ε) := hH_Q_lower' Q hQ
    have h3 : H_uniform > Real.rpow Δ (-s - t + 36 * ε) / 2 := by linarith
    have h4 : Real.rpow Δ (-s - t + 36 * ε) / 2 ≥ Real.rpow Δ (-s - t + 37 * ε) := by
      have h_add : (-s - t + 36 * ε) + ε = -s - t + 37 * ε := by ring
      have h_rpow : Real.rpow Δ ((-s - t + 36 * ε) + ε) =
          Real.rpow Δ (-s - t + 36 * ε) * Real.rpow Δ ε := Real.rpow_add hΔ_pos _ _
      have h5 : Real.rpow Δ (-s - t + 37 * ε) =
          Real.rpow Δ (-s - t + 36 * ε) * Real.rpow Δ ε := by
        rw [h_add] at h_rpow; exact h_rpow
      rw [h5]
      have h6 : 0 ≤ Real.rpow Δ (-s - t + 36 * ε) := Real.rpow_nonneg hΔ_pos.le _
      have h7 : Real.rpow Δ ε ≤ 1 / 2 := hΔ_ε_le_half
      have h_goal : Real.rpow Δ (-s - t + 36 * ε) * Real.rpow Δ ε ≤ Real.rpow Δ (-s - t + 36 * ε) / 2 := by
        have h_div : Real.rpow Δ (-s - t + 36 * ε) / 2 = Real.rpow Δ (-s - t + 36 * ε) * (1 / 2 : ℝ) := by ring
        rw [h_div]
        exact mul_le_mul_of_nonneg_left h7 h6
      exact h_goal
    have h_eq : Real.rpow Δ (-s - t + 37 * ε) = Real.rpow Δ (-(s + t) + 37 * ε) := by
      congr 1 <;> ring
    linarith [h_eq]
  -- Physical ball-growth transfer from Qset_all to Q0
  -- Q0 ⊆ Qset_all and |Qset_all| ≤ Δ^{-ε} * |Q0|, so constant degrades by Δ^{-ε}:
  -- Δ^{-10ε} * Δ^{-ε} = Δ^{-11ε} ≤ Δ^{-20ε}
  have hQ0_phys_growth : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((Q0.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).card : ℝ) ≤
        Real.rpow Δ (-20 * ε) * r^t * (Q0.card : ℝ) := by
    intro c r hr
    have h_filter_sub : Q0.filter (fun Q => dist (squareCenter Δ Q) c ≤ r) ⊆
        Qset_all.filter (fun Q => dist (squareCenter Δ Q) c ≤ r) :=
      Finset.filter_subset_filter _ hQ0_sub
    have h1 : (Q0.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).card ≤
        (Qset_all.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).card :=
      Finset.card_le_card h_filter_sub
    have h_pos_rpow : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h2 : (Qset_all.card : ℝ) ≤ Real.rpow Δ (-ε) * (Q0.card : ℝ) := by
      have h21 : (Q0.card : ℝ) ≥ (Qset_all.card : ℝ) / Real.rpow Δ (-ε) := hQ0_card_lower
      have h22 : (Q0.card : ℝ) * Real.rpow Δ (-ε) ≥ (Qset_all.card : ℝ) := by
        calc (Q0.card : ℝ) * Real.rpow Δ (-ε)
          ≥ ((Qset_all.card : ℝ) / Real.rpow Δ (-ε)) * Real.rpow Δ (-ε) := by gcongr
        _ = (Qset_all.card : ℝ) := by field_simp [h_pos_rpow.ne'] <;> ring
      have h23 : Real.rpow Δ (-ε) * (Q0.card : ℝ) = (Q0.card : ℝ) * Real.rpow Δ (-ε) := by ring
      rw [h23]
      exact h22
    have h3 := hQset_phys_growth_in c r hr
    have h4 : Real.rpow Δ (-11 * ε) * r^t * (Qset_all.card : ℝ) ≤
        Real.rpow Δ (-20 * ε) * r^t * (Q0.card : ℝ) := by
      have h5 : 0 ≤ r^t := Real.rpow_nonneg (by linarith) t
      have h_card_nonneg : 0 ≤ (Q0.card : ℝ) := Nat.cast_nonneg _
      have h_rpow_nonneg : 0 ≤ Real.rpow Δ (-11 * ε) := Real.rpow_nonneg hΔ_pos.le _
      have h_rpow_add : Real.rpow Δ (-11 * ε) * Real.rpow Δ (-ε) = Real.rpow Δ (-12 * ε) := by
        have h : Real.rpow Δ (-11 * ε) * Real.rpow Δ (-ε) = Real.rpow Δ ((-11 * ε) + (-ε)) :=
          (Real.rpow_add hΔ_pos (-11 * ε) (-ε)).symm
        rw [h]
        have h_exp : (-11 * ε) + (-ε) = -12 * ε := by ring
        rw [h_exp]
      have h6 : Real.rpow Δ (-12 * ε) ≤ Real.rpow Δ (-20 * ε) := by
        have h7 : -12 * ε ≥ -20 * ε := by linarith
        have h8 : Δ < 1 := by linarith
        exact Real.rpow_le_rpow_of_exponent_ge hΔ_pos h8.le h7
      have h_product_nonneg : 0 ≤ Real.rpow Δ (-11 * ε) * r^t :=
        mul_nonneg h_rpow_nonneg h5
      have h_step1 : Real.rpow Δ (-11 * ε) * r^t * (Qset_all.card : ℝ) ≤
          Real.rpow Δ (-11 * ε) * r^t * (Real.rpow Δ (-ε) * (Q0.card : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 h_product_nonneg
      have h_step2 : Real.rpow Δ (-11 * ε) * r^t * (Real.rpow Δ (-ε) * (Q0.card : ℝ)) =
          (Real.rpow Δ (-11 * ε) * Real.rpow Δ (-ε)) * r^t * (Q0.card : ℝ) := by ring
      have h_step3 : (Real.rpow Δ (-11 * ε) * Real.rpow Δ (-ε)) * r^t * (Q0.card : ℝ) =
          Real.rpow Δ (-12 * ε) * r^t * (Q0.card : ℝ) := by
        rw [h_rpow_add] <;> ring
      have h_step4 : Real.rpow Δ (-12 * ε) * r^t * (Q0.card : ℝ) ≤
          Real.rpow Δ (-20 * ε) * r^t * (Q0.card : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h6 h5) h_card_nonneg
      calc Real.rpow Δ (-11 * ε) * r^t * (Qset_all.card : ℝ)
        ≤ Real.rpow Δ (-11 * ε) * r^t * (Real.rpow Δ (-ε) * (Q0.card : ℝ)) := h_step1
      _ = (Real.rpow Δ (-11 * ε) * Real.rpow Δ (-ε)) * r^t * (Q0.card : ℝ) := h_step2
      _ = Real.rpow Δ (-12 * ε) * r^t * (Q0.card : ℝ) := h_step3
      _ ≤ Real.rpow Δ (-20 * ε) * r^t * (Q0.card : ℝ) := h_step4
    calc ((Q0.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).card : ℝ)
      ≤ ((Qset_all.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).card : ℝ) := by exact_mod_cast h1
    _ ≤ Real.rpow Δ (-11 * ε) * r^t * (Qset_all.card : ℝ) := h3
    _ ≤ Real.rpow Δ (-20 * ε) * r^t * (Q0.card : ℝ) := h4
  exact
    { Qset := Q0
      perSquare := fun Q hQ => sd Q (hQ0_sub hQ)
      hQset_sset := hQset_sset'
      hQset_card_lower := by
        have h1 : (Q0.card : ℝ) ≥ (Qset_all.card : ℝ) / Real.rpow Δ (-ε) := hQ0_card_lower
        have h2 : (Qset_all.card : ℝ) ≥ Real.rpow Δ (-t + 3 * ε) := hQset_card_lower
        have h4 : (Real.rpow Δ (-ε))⁻¹ = Real.rpow Δ ε := by
          have h5 : Real.rpow Δ (-ε) = (Real.rpow Δ ε)⁻¹ := Real.rpow_neg hΔ_pos.le ε
          rw [h5]; simp
        have h3 : Real.rpow Δ (-t + 3 * ε) / Real.rpow Δ (-ε) = Real.rpow Δ (-t + 4 * ε) := by
          have h_pos1 : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos hΔ_pos _
          rw [div_eq_mul_inv, h4]
          have h_sum : (-t + 3 * ε) + ε = -t + 4 * ε := by ring
          have h_add : Real.rpow Δ ((-t + 3 * ε) + ε) =
              Real.rpow Δ (-t + 3 * ε) * Real.rpow Δ ε := by
            simpa [h_sum] using Real.rpow_add (x := Δ) hΔ_pos (-t + 3 * ε) ε
          rw [h_sum] at h_add
          exact h_add.symm
        have h5 : (Q0.card : ℝ) ≥ Real.rpow Δ (-t + 4 * ε) := by
          have h_pos_b : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos hΔ_pos _
          calc (Q0.card : ℝ)
            ≥ (Qset_all.card : ℝ) / Real.rpow Δ (-ε) := h1
          _ ≥ Real.rpow Δ (-t + 3 * ε) / Real.rpow Δ (-ε) := by
            exact div_le_div_of_nonneg_right h2 h_pos_b.le
          _ = Real.rpow Δ (-t + 4 * ε) := h3
        exact h5
      hQset_card_upper := by
        have h1 : (Q0.card : ℝ) ≤ (Qset_all.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hQ0_sub
        have h2 : (Qset_all.card : ℝ) ≤ Real.rpow Δ (-t - ε) := by
          simpa using hQset_card_upper
        exact h1.trans h2
      K_uniform := K_uniform
      H_uniform := H_uniform
      C2_uniform := C2_uniform
      C_card_uniform := C_card_uniform
      hK_uniform := hK_uniform'
      hH_uniform := hH_uniform'
      hH_uniform_lower := hH_uniform_lower'
      hC2_uniform := fun Q hQ => (sd Q (hQ0_sub hQ)).hC2_Q_loss
      hC_card_uniform := hC_card_uniform'
      hK_loss := hK_loss'
      hC2_loss := le_refl _
      hC_card_exp_lower := hC_card_exp_lower'
      hC_card_exp_upper := hC_card_exp_upper'
      hC_card_upper := fun Q hQ => h_tight_card Q hQ
      hC_Q_slope_cover_upper := fun Q hQ => by
        let sdQ := sd Q (hQ0_sub hQ)
        let S : Set CoarseTube := (sdQ.C_Q : Set CoarseTube)
        let slopeSet : Set ℝ := tubeSlope '' S
        have h1 : (sdQ.C_Q.card : ℝ) ≤ Real.rpow Δ (-s - 29 * ε) := h_tight_card Q hQ
        have hS_finite : S.Finite := Finset.finite_toSet _
        have hSlope_finite : slopeSet.Finite := Set.Finite.image _ hS_finite
        have h2 : Metric.externalCoveringNumber Δ.toNNReal slopeSet ≤
            ENNReal.ofReal (sdQ.C_Q.card : ℝ) := by
          have h21 : (Metric.externalCoveringNumber Δ.toNNReal slopeSet : ENNReal) ≤
              (↑(Set.encard slopeSet) : ENNReal) := by
            exact_mod_cast Metric.externalCoveringNumber_le_encard_self (ε := Δ.toNNReal) slopeSet
          let imgFin : Finset ℝ := Finset.image tubeSlope sdQ.C_Q
          have h_img : (imgFin : Set ℝ) = slopeSet := by
            ext x; simp [slopeSet, S, imgFin]
          have h22 : (↑(Set.encard slopeSet) : ENNReal) ≤ ENNReal.ofReal (sdQ.C_Q.card : ℝ) := by
            have h_enc : Set.encard slopeSet = ↑imgFin.card := by
              rw [← h_img]
              simp
            rw [h_enc]
            have h_card : imgFin.card ≤ sdQ.C_Q.card := Finset.card_image_le
            exact_mod_cast h_card
          exact le_trans h21 h22
        calc Metric.externalCoveringNumber Δ.toNNReal slopeSet
          ≤ ENNReal.ofReal (sdQ.C_Q.card : ℝ) := h2
        _ ≤ ENNReal.ofReal (Real.rpow Δ (-s - 29 * ε)) := by
          exact ENNReal.ofReal_le_ofReal h1
      hH_Q_lower := fun Q hQ => by
        have h := hH_Q_lower' Q hQ
        have h_eq : -s - t + 36 * ε = -(s + t) + 36 * ε := by ring
        rw [h_eq] at h
        exact h
      hQset_phys_growth := hQ0_phys_growth }

end DirecretisedFurstenbergEstimate.AppendixA3
