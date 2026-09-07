import MyLeanRepo.Kakeya.Cinematic.Section5.PolynomialScaleCoarseCountInputs
import MyLeanRepo.Kakeya.Cinematic.Targets.CoarseRectangleCount.DoublingCover
import MyLeanRepo.Kakeya.Cinematic.Targets.CoarseRectangleCount.ProximityComparability
import MyLeanRepo.Kakeya.Cinematic.Targets.CoarseRectangleCount.MidpointPacking

/-!
# Count incomparable rectangles at polynomially large scale

Adaptation of `coarse_rectangle_count` to the regime `t ≤ T / δ`.
The midpoint separation scale becomes `Ω(δ / √T)` instead of `Ω(√δ)`,
giving a per-ball packing bound `O(δ⁻¹)` instead of `O(δ⁻¹ᐟ²)`.
-/

noncomputable section

open Kakeya.Cinematic Set Finset

namespace Kakeya.Cinematic

theorem polynomial_scale_coarse_rectangle_count :
    PolynomialScaleCoarseRectangleCountStatement := by
  intro D hD
  let C0 : ℝ := Real.log D / Real.log 2
  let C : ℝ := C0 + 2
  have hC0_nonneg : 0 ≤ C0 := by
    have h1 : 0 ≤ Real.log D := Real.log_nonneg hD
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact div_nonneg h1 h2.le
  have hC_pos : 0 < C := by linarith
  refine' ⟨C, hC_pos, _⟩
  intro K T hK hT
  let B : ℝ := Real.sqrt T / 9 + 1
  let A : ℝ := D * (4 * K + 1) ^ C0 * B
  have hB_pos : 0 < B := by positivity
  have hA_pos : 0 < A := by positivity
  let delta₀ : ℝ := min 1 (1 / A)
  have hdelta₀_pos : 0 < delta₀ := by
    have h1 : 0 < 1 / A := by positivity
    exact lt_min (by norm_num) h1
  have hdelta₀_le_one : delta₀ ≤ 1 := min_le_left _ _
  refine' ⟨delta₀, hdelta₀_pos, hdelta₀_le_one, _⟩
  intro delta hδ hδ₀ t lambda hδt ht₁ hlam hadm family hcin I hI
  intro R hRin hRquarter hRincomp

  have hδ_le_one : delta ≤ 1 := by
    have h : delta ≤ delta₀ := hδ₀
    have h2 : delta₀ ≤ 1 := hdelta₀_le_one
    linarith

  have hA_mul_le_one : A * delta ≤ 1 := by
    have h3 : delta ≤ 1 / A := by
      have h4 : delta ≤ delta₀ := hδ₀
      have h5 : delta₀ ≤ 1 / A := min_le_right _ _
      linarith
    have h6 : A * delta ≤ A * (1 / A) := by gcongr
    have h7 : A * (1 / A) = 1 := by
      field_simp [hA_pos.ne']
    rw [h7] at h6
    exact h6

  by_cases hRempty : R.card = 0
  · rw [hRempty]
    have h_pos : 0 < Real.rpow delta (-C) := Real.rpow_pos_of_pos hδ _
    exact_mod_cast h_pos.le

  have hR_pos : 0 < R.card := Nat.pos_of_ne_zero hRempty

  -- Step 1: Doubling cover at radius δ/2
  rcases doubling_cover hK hD hcin (delta / 2) (by linarith) with
    ⟨centers, hcenters_sub, hcenters_cover, hcenters_card⟩

  -- Step 2: Define indices near each center
  let indices : C2Function → Finset (Fin R.card) := fun c =>
    Finset.univ.filter (fun i : Fin R.card =>
      c2Distance (R.rectangle i).function c ≤ delta / 2)

  have h_every_index_covered : ∀ (i : Fin R.card), ∃ c ∈ centers, i ∈ indices c := by
    intro i
    have hfi : (R.rectangle i).function ∈ family := hRin i
    rcases hcenters_cover (R.rectangle i).function hfi with ⟨c, hc, hdist⟩
    exact ⟨c, hc, by
      simp only [indices, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hdist⟩

  have h_univ_covered : (Finset.univ : Finset (Fin R.card)) ⊆
      centers.biUnion indices := by
    intro i _
    rcases h_every_index_covered i with ⟨c, hc, hi⟩
    exact Finset.mem_biUnion.mpr ⟨c, hc, hi⟩

  have h_card_sum : (R.card : ℝ) ≤ ∑ c ∈ centers, ((indices c).card : ℝ) := by
    have h1 : (Finset.univ : Finset (Fin R.card)).card = R.card := by simp
    have h2 : (Finset.univ : Finset (Fin R.card)).card ≤
        (centers.biUnion indices).card := Finset.card_le_card h_univ_covered
    have h3 : (centers.biUnion indices).card ≤ ∑ c ∈ centers, (indices c).card :=
      Finset.card_biUnion_le
    have h4 : ((Finset.univ : Finset (Fin R.card)).card : ℝ) ≤
        ∑ c ∈ centers, ((indices c).card : ℝ) := by
      exact_mod_cast h2.trans h3
    simpa [h1] using h4

  -- Step 3: Separation scale
  let s : ℝ := (Real.sqrt lambda - 1) * Real.sqrt (delta / t)
  have hs_pos : 0 < s := by
    have h1 : 9 ≤ Real.sqrt lambda := by
      nlinarith [Real.sqrt_nonneg lambda, Real.sq_sqrt (show 0 ≤ lambda by linarith)]
    have h2 : 0 < Real.sqrt (delta / t) := Real.sqrt_pos.mpr (div_pos hδ (by linarith))
    have h3 : 0 < Real.sqrt lambda - 1 := by linarith
    exact mul_pos h3 h2

  have hT_pos : 0 < T := by linarith

  have h_s_lower : s ≥ 9 * delta / Real.sqrt T := by
    have h1 : 9 ≤ Real.sqrt lambda - 1 := by
      nlinarith [Real.sqrt_nonneg lambda, Real.sq_sqrt (show 0 ≤ lambda by linarith)]
    have h2 : Real.sqrt (delta / t) ≥ delta / Real.sqrt T := by
      have h3 : delta / t ≥ delta ^ 2 / T := by
        have h4 : t ≤ T / delta := ht₁
        have h5 : 0 < t := by linarith
        have h6 : delta / t ≥ delta / (T / delta) := by gcongr
        have h7 : delta / (T / delta) = delta ^ 2 / T := by
          field_simp [hδ.ne', hT_pos.ne']
        rw [h7] at h6
        exact h6
      have h4 : Real.sqrt (delta / t) ≥ Real.sqrt (delta ^ 2 / T) :=
        Real.sqrt_le_sqrt h3
      have h5 : Real.sqrt (delta ^ 2 / T) = delta / Real.sqrt T := by
        have hpos1 : 0 < delta / Real.sqrt T := by positivity
        have hsq : (delta / Real.sqrt T) ^ 2 = delta ^ 2 / T := by
          calc (delta / Real.sqrt T) ^ 2
            = delta ^ 2 / (Real.sqrt T) ^ 2 := by ring
          _ = delta ^ 2 / T := by
            have hT2 : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt (by linarith)
            rw [hT2]
        rw [←hsq]
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_pos hpos1]
      rw [h5] at h4
      exact h4
    have h6 : s ≥ 9 * Real.sqrt (delta / t) := by
      dsimp only [s]
      have h7 : (Real.sqrt lambda - 1) * Real.sqrt (delta / t) ≥ 9 * Real.sqrt (delta / t) :=
        mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
      exact h7
    have h8 : 9 * Real.sqrt (delta / t) ≥ 9 * (delta / Real.sqrt T) :=
      mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 9 by norm_num)
    have h9 : 9 * (delta / Real.sqrt T) = 9 * delta / Real.sqrt T := by ring
    rw [h9] at h8
    linarith

  -- Separation within each ball
  have h_sep_within : ∀ (c : C2Function), c ∈ centers →
      ∀ (i j : Fin R.card), i ∈ indices c → j ∈ indices c → i ≠ j →
        |(R.rectangle i).interval.midpoint - (R.rectangle j).interval.midpoint| > s := by
    intro c hc i j hi hj hij
    have hfi : (R.rectangle i).function ∈ family := hRin i
    have hfj : (R.rectangle j).function ∈ family := hRin j
    have hRi : (R.rectangle i).IsOverCentralQuarterOf I := hRquarter i
    have hRj : (R.rectangle j).IsOverCentralQuarterOf I := hRquarter j
    have hdi : c2Distance (R.rectangle i).function c ≤ delta / 2 := by
      simp only [indices, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hi
    have hdj : c2Distance (R.rectangle j).function c ≤ delta / 2 := by
      simp only [indices, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hj
    have hdij : c2Distance (R.rectangle i).function (R.rectangle j).function ≤ delta := by
      have h_sym : c2Distance c (R.rectangle j).function = c2Distance (R.rectangle j).function c := by
        simp [c2Distance_eq_dist, dist_comm]
      calc c2Distance (R.rectangle i).function (R.rectangle j).function
        ≤ c2Distance (R.rectangle i).function c + c2Distance c (R.rectangle j).function :=
          dist_triangle _ _ _
      _ = c2Distance (R.rectangle i).function c + c2Distance (R.rectangle j).function c := by
        rw [h_sym]
      _ ≤ delta / 2 + delta / 2 := by gcongr
      _ = delta := by ring
    have h_incomp : ¬(R.rectangle i).AreLambdaComparable (R.rectangle j) family lambda :=
      hRincomp i j hij
    by_contra h
    have h' : |(R.rectangle i).interval.midpoint - (R.rectangle j).interval.midpoint| ≤ s := by
      linarith
    have h_comp : (R.rectangle i).AreLambdaComparable (R.rectangle j) family lambda :=
      proximity_implies_comparability hδ (by linarith) hlam hadm hfi hfj hRi hRj hdij h'
    exact h_incomp h_comp

  -- Per-ball bound
  have h_per_ball : ∀ (c : C2Function), c ∈ centers →
      ((indices c).card : ℝ) ≤ B * delta ^ (-1 : ℝ) := by
    intro c hc
    let midpoints : Finset ℝ := Finset.image
      (fun i : Fin R.card => (R.rectangle i).interval.midpoint) (indices c)

    have h_inj : Set.InjOn (fun i : Fin R.card => (R.rectangle i).interval.midpoint) (indices c) := by
      intro i hi j hj heq
      by_contra hne
      have h_sep := h_sep_within c hc i j hi hj hne
      have heq' : (R.rectangle i).interval.midpoint = (R.rectangle j).interval.midpoint := by
        simpa using heq
      rw [heq'] at h_sep
      have h_abs : |(R.rectangle j).interval.midpoint - (R.rectangle j).interval.midpoint| = 0 := by
        rw [sub_self, abs_zero]
      rw [h_abs] at h_sep
      linarith [hs_pos]

    have h_card_eq : midpoints.card = (indices c).card := by
      rw [Finset.card_image_of_injOn h_inj]

    have h_mid_in_Icc : ∀ x ∈ midpoints, x ∈ Set.Icc (0 : ℝ) 1 := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      have h1 : 0 ≤ (R.rectangle i).interval.left := (R.rectangle i).interval.left_mem.1
      have h2 : (R.rectangle i).interval.right ≤ 1 := (R.rectangle i).interval.right_mem.2
      have h_lr : (R.rectangle i).interval.left ≤ (R.rectangle i).interval.right :=
        (R.rectangle i).interval.left_le_right
      have h3 : (R.rectangle i).interval.left ≤ (R.rectangle i).interval.midpoint := by
        simp only [ParameterInterval.midpoint]
        linarith
      have h4 : (R.rectangle i).interval.midpoint ≤ (R.rectangle i).interval.right := by
        simp only [ParameterInterval.midpoint]
        linarith
      exact ⟨by linarith, by linarith⟩

    have h_mid_sep : ∀ x ∈ midpoints, ∀ y ∈ midpoints, x ≠ y → |x - y| > s := by
      intro x hx y hy hxy
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
      have hij : i ≠ j := by
        intro h; rw [h] at hxy; simp at hxy
      exact h_sep_within c hc i j hi hj hij

    have h_pack : (midpoints.card : ℝ) ≤ (1 - 0) / s + 1 :=
      midpoint_packing_bound hs_pos (by norm_num) midpoints h_mid_in_Icc h_mid_sep

    have h1 : 1 / s + 1 ≤ B * delta ^ (-1 : ℝ) := by
      have h2 : 1 / s ≤ 1 / (9 * delta / Real.sqrt T) := by gcongr
      have h3 : 1 / (9 * delta / Real.sqrt T) = (Real.sqrt T / 9) * (1 / delta) := by
        field_simp [hδ.ne', hT_pos.ne']
      have h4 : 1 / delta = delta ^ (-1 : ℝ) := by
        have h41 : delta ^ (-1 : ℝ) = (delta : ℝ)⁻¹ := Real.rpow_neg_one delta
        have h42 : (delta : ℝ)⁻¹ = 1 / delta := by simp
        have h43 : delta ^ (-1 : ℝ) = 1 / delta := by
          rw [h41, h42]
        exact h43.symm
      have h5 : 1 / s ≤ (Real.sqrt T / 9) * delta ^ (-1 : ℝ) := by
        calc 1 / s
          ≤ 1 / (9 * delta / Real.sqrt T) := h2
        _ = (Real.sqrt T / 9) * (1 / delta) := h3
        _ = (Real.sqrt T / 9) * delta ^ (-1 : ℝ) := by rw [h4]
      have h6 : 1 ≤ delta ^ (-1 : ℝ) := by
        have h7 : delta ≤ 1 := hδ_le_one
        have h8 : 0 < delta := hδ
        have h9 : delta ^ (-1 : ℝ) = 1 / delta := by
          have h91 : delta ^ (-1 : ℝ) = (delta : ℝ)⁻¹ := Real.rpow_neg_one delta
          rw [h91]; simp
        rw [h9]
        apply one_le_one_div <;> linarith
      have h10 : 1 / s + 1 ≤ (Real.sqrt T / 9 + 1) * delta ^ (-1 : ℝ) := by
        calc 1 / s + 1
          ≤ (Real.sqrt T / 9) * delta ^ (-1 : ℝ) + 1 := by linarith
        _ ≤ (Real.sqrt T / 9) * delta ^ (-1 : ℝ) + delta ^ (-1 : ℝ) := by gcongr
        _ = (Real.sqrt T / 9 + 1) * delta ^ (-1 : ℝ) := by ring
      simpa [B] using h10

    have h_pack' : (midpoints.card : ℝ) ≤ 1 / s + 1 := by
      have h_simp : (1 - 0 : ℝ) / s + 1 = 1 / s + 1 := by ring
      rw [h_simp] at h_pack
      exact h_pack
    have h_card_real : (midpoints.card : ℝ) = ((indices c).card : ℝ) := by
      exact_mod_cast h_card_eq
    rw [h_card_real] at h_pack'
    exact h_pack'.trans h1

  -- Step 4: Sum over centers
  have h_total : (R.card : ℝ) ≤
      (centers.card : ℝ) * (B * delta ^ (-1 : ℝ)) := by
    calc (R.card : ℝ)
      ≤ ∑ c ∈ centers, ((indices c).card : ℝ) := h_card_sum
    _ ≤ ∑ c ∈ centers, (B * delta ^ (-1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro c hc
      exact h_per_ball c hc
    _ = (centers.card : ℝ) * (B * delta ^ (-1 : ℝ)) := by
      simp [Finset.sum_const]

  -- Step 5: Bound centers.card
  have h_centers_bound : (centers.card : ℝ) ≤ D * (4 * K / delta + 1) ^ C0 := by
    have h := hcenters_card
    have h5 : 2 * K / (delta / 2) = 4 * K / delta := by
      field_simp [hδ.ne']; ring
    rw [h5] at h
    exact h

  -- Step 6: Final absorption
  have h6 : (R.card : ℝ) ≤
      D * (4 * K / delta + 1) ^ C0 * (B * delta ^ (-1 : ℝ)) := by
    calc (R.card : ℝ)
      ≤ (centers.card : ℝ) * (B * delta ^ (-1 : ℝ)) := h_total
    _ ≤ (D * (4 * K / delta + 1) ^ C0) * (B * delta ^ (-1 : ℝ)) := by gcongr

  have h7 : D * (4 * K / delta + 1) ^ C0 * (B * delta ^ (-1 : ℝ)) ≤
      A * delta ^ (-(C0 + 1 : ℝ)) := by
    have h8 : 4 * K / delta + 1 ≤ (4 * K + 1) / delta := by
      have h9 : 0 < delta := hδ
      have h10 : 1 ≤ 1 / delta := by
        apply one_le_one_div <;> linarith
      calc 4 * K / delta + 1
        ≤ 4 * K / delta + 1 / delta := by gcongr
      _ = (4 * K + 1) / delta := by field_simp [h9.ne']
    have h9 : (4 * K / delta + 1) ^ C0 ≤ ((4 * K + 1) / delta) ^ C0 := by
      exact Real.rpow_le_rpow (by positivity) h8 hC0_nonneg
    have h10 : ((4 * K + 1) / delta) ^ C0 = (4 * K + 1) ^ C0 * delta ^ (-C0) := by
      have h11 : ((4 * K + 1) / delta) ^ C0 = (4 * K + 1) ^ C0 / delta ^ C0 := by
        rw [Real.div_rpow (by positivity) (by positivity)]
      rw [h11]
      have h12 : delta ^ (-C0) = (delta ^ C0)⁻¹ := Real.rpow_neg (by linarith) C0
      have h13 : (delta ^ C0)⁻¹ = 1 / delta ^ C0 := by field_simp
      have h14 : delta ^ (-C0) = 1 / delta ^ C0 := by rw [h12, h13]
      rw [h14]; ring
    have h13 : delta ^ (-C0) * delta ^ (-1 : ℝ) = delta ^ (-(C0 + 1 : ℝ)) := by
      rw [←Real.rpow_add hδ]
      congr 1; ring
    have h9' : (4 * K / delta + 1) ^ C0 ≤ (4 * K + 1) ^ C0 * delta ^ (-C0) := by
      rw [h10] at h9
      exact h9
    have hD_pos : 0 < D := by linarith
    have h_factor_pos : 0 < B * delta ^ (-1 : ℝ) := by positivity
    have h_ineq1 : D * (4 * K / delta + 1) ^ C0 * (B * delta ^ (-1 : ℝ)) ≤
        D * ((4 * K + 1) ^ C0 * delta ^ (-C0)) * (B * delta ^ (-1 : ℝ)) := by
      have h : D * (4 * K / delta + 1) ^ C0 ≤ D * ((4 * K + 1) ^ C0 * delta ^ (-C0)) :=
        mul_le_mul_of_nonneg_left h9' hD_pos.le
      exact mul_le_mul_of_nonneg_right h h_factor_pos.le
    calc D * (4 * K / delta + 1) ^ C0 * (B * delta ^ (-1 : ℝ))
      ≤ D * ((4 * K + 1) ^ C0 * delta ^ (-C0)) * (B * delta ^ (-1 : ℝ)) := h_ineq1
    _ = D * (4 * K + 1) ^ C0 * B * (delta ^ (-C0) * delta ^ (-1 : ℝ)) := by ring
    _ = D * (4 * K + 1) ^ C0 * B * delta ^ (-(C0 + 1 : ℝ)) := by rw [h13]
    _ = A * delta ^ (-(C0 + 1 : ℝ)) := by
      simp only [A]

  have h14 : A * delta ^ (-(C0 + 1 : ℝ)) ≤ delta ^ (-C) := by
    have h15 : -(C0 + 1 : ℝ) = -C + 1 := by
      simp only [C]; ring
    rw [h15]
    have h16 : delta ^ (-C + 1 : ℝ) = delta ^ (1 : ℝ) * delta ^ (-C) := by
      rw [←Real.rpow_add hδ]
      congr 1; ring
    rw [h16]
    have h17 : delta ^ (1 : ℝ) = delta := by simp
    rw [h17]
    have h18 : 0 ≤ delta ^ (-C) := by positivity
    calc A * (delta * delta ^ (-C))
      = (A * delta) * delta ^ (-C) := by ring
    _ ≤ 1 * delta ^ (-C) := by gcongr
    _ = delta ^ (-C) := by ring

  exact h6.trans (h7.trans h14)

end Kakeya.Cinematic
