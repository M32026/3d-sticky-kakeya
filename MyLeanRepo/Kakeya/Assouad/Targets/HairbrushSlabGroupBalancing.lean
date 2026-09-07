import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.DyadicBalancing
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.MassWeightedRetention
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.DyadicPigeonhole
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.SlabGroupBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

open MeasureTheory Finset BigOperators

/-!
# Balancing raw slab incidence groups

This is equations (B.34)--(B.36) of the self-contained Appendix-B proof.

Discard raw groups below the supplied average-density floor, then pigeonhole
the surviving groups simultaneously by tube cardinality and average shading
density.  Retain a polynomial fraction of the total incidence mass.

This target is finite combinatorics and ENNReal arithmetic.  Do not alter the
groups geometrically and do not invoke Frostman or the local hairbrush.
-/

noncomputable section

namespace Kakeya.Assouad

theorem hairbrush_slab_group_balancing :
    HairbrushSlabGroupBalancingStatement := by
  intro inputExponent densityFloor cardExponent balanceLoss
    h_input_pos h_floor_pos h_card_pos h_balance_pos

  have h_densityFloor_pos : 0 < densityFloor := by linarith [h_input_pos, h_floor_pos]

  -- Absorption 1: low-density discard (includes 2000000 constant absorption)
  rcases low_density_discard_bound inputExponent densityFloor h_input_pos h_floor_pos with
    ⟨δ_low, hδ_low_pos, hδ_low_one, h_low_discard⟩

  -- Constant for log absorption
  let C_log : ℝ := 2 * (cardExponent / Real.log 2 + 1) * (densityFloor / Real.log 2 + 1)
  have h_log2_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC_log_nonneg : 0 ≤ C_log := by
    have h1 : 0 ≤ cardExponent / Real.log 2 + 1 := by
      have h11 : 0 < Real.log 2 := h_log2_pos'
      positivity
    have h2 : 0 ≤ densityFloor / Real.log 2 + 1 := by
      have h21 : 0 < Real.log 2 := h_log2_pos'
      have h22 : 0 < densityFloor := h_densityFloor_pos
      positivity
    have h3 : 0 ≤ 2 * (cardExponent / Real.log 2 + 1) := by positivity
    positivity

  -- Absorption 2: C_log * (log(1/δ))^2 ≤ δ^{-balanceLoss}
  rcases exists_delta_log_sq_absorbed C_log hC_log_nonneg h_balance_pos with
    ⟨δ_log, hδ_log_pos, hδ_log_one, h_absorb_log⟩

  -- Need δ ≤ exp(-1) so log(1/δ) ≥ 1
  let δ₃ : ℝ := Real.exp (-1)
  have hδ₃_pos : 0 < δ₃ := by positivity
  have hδ₃_one : δ₃ ≤ 1 := by
    have h : Real.exp (-1 : ℝ) < Real.exp (0 : ℝ) := Real.exp_strictMono (by norm_num)
    have h0 : Real.exp (0 : ℝ) = 1 := by simp
    rw [h0] at h
    exact h.le

  let delta₀ : ℝ := min (min δ_low (min δ_log δ₃)) (1 / 1000)
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_le_1000 : delta₀ ≤ 1 / 1000 := min_le_right _ _
  have hdelta₀_le_low : delta₀ ≤ δ_low :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hdelta₀_le_log : delta₀ ≤ δ_log :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdelta₀_le_δ₃ : delta₀ ≤ δ₃ :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

  refine ⟨delta₀, hdelta₀_pos, hdelta₀_le_1000, ?_⟩
  intro δ hδ_pos hδ_le

  have hδ_le_one : δ ≤ 1 := by linarith [hdelta₀_le_1000]
  have hδ_le_low : δ ≤ δ_low := hδ_le.trans hdelta₀_le_low
  have hδ_le_log : δ ≤ δ_log := hδ_le.trans hdelta₀_le_log
  have hδ_le_δ₃ : δ ≤ δ₃ := hδ_le.trans hdelta₀_le_δ₃

  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_logInvDelta_ge_one : 1 ≤ Real.log (1 / δ) := by
    have h1 : 1 / δ ≥ 1 / δ₃ := by gcongr
    have h2 : Real.log (1 / δ) ≥ Real.log (1 / δ₃) := Real.log_le_log (by positivity) h1
    have h3 : 1 / δ₃ = Real.exp 1 := by
      simp [δ₃] <;> field_simp <;> rw [Real.exp_neg] <;> field_simp
    rw [h3] at h2
    have h4 : Real.log (Real.exp 1) = 1 := by simp
    rw [h4] at h2
    linarith

  intro eta stopLoss F Y hF_nonempty hF_card angular h_aggregate grouping

  rcases tube_volume_scaling with ⟨h_tube_vol_eq, h_tube_vol_pos, _⟩
  let V := Kakeya.deltaTubeVolume δ
  have hV_pos : 0 < V := (h_tube_vol_pos δ hδ_pos hδ_le_one).1
  have hV_ne_top : V ≠ ⊤ := (h_tube_vol_pos δ hδ_pos hδ_le_one).2

  let N := grouping.groupCount
  have hN_pos : 0 < N := grouping.groupCount_pos

  let mass : Fin N → ENNReal := fun j => (grouping.shading j).mass
  let card : Fin N → ℕ := fun j => (grouping.family j).card
  let enncard : Fin N → ENNReal := fun j => (grouping.family j).enncard

  have h_card_j_pos : ∀ j, 0 < card j := by
    intro j
    exact Finset.Nonempty.card_pos (grouping.family_nonempty j)

  have h_enncard_pos : ∀ j, 0 < enncard j := by
    intro j
    have h_eq : enncard j = (card j : ENNReal) := by
      dsimp only [enncard] <;> rfl
    rw [h_eq]
    exact_mod_cast h_card_j_pos j

  have h_enncard_ne_top : ∀ j, enncard j ≠ ⊤ := by
    intro j
    have h_eq : enncard j = (card j : ENNReal) := by
      dsimp only [enncard] <;> rfl
    rw [h_eq]
    exact ENNReal.natCast_ne_top (card j)

  -- mass j ≤ enncard j * V
  have h_mass_le : ∀ j, mass j ≤ enncard j * V := by
    intro j
    exact shading_mass_le_card_mul_volume (grouping.shading j) hδ_pos

  have h_mass_ne_top : ∀ j, mass j ≠ ⊤ := by
    intro j
    have h5 : enncard j * V ≠ ⊤ := ENNReal.mul_ne_top (h_enncard_ne_top j) hV_ne_top
    exact ne_top_of_le_ne_top h5 (h_mass_le j)

  have h_angular_mass_ne_top : angular.shading.mass ≠ ⊤ := by
    have h1 : angular.shading.mass ≤ Y.mass := by
      simp only [Kakeya.Shading.mass]
      apply Finset.sum_le_sum
      intro T hT
      exact measure_mono (angular.shading_subset T hT)
    have h2 : Y.mass ≤ F.enncard * V := shading_mass_le_card_mul_volume Y hδ_pos
    have hF_enncard_eq : F.enncard = (F.card : ENNReal) := by rfl
    have h6 : F.enncard * V ≠ ⊤ := by
      rw [hF_enncard_eq]
      apply ENNReal.mul_ne_top
      · exact ENNReal.natCast_ne_top _
      · exact hV_ne_top
    exact ne_top_of_le_ne_top h6 (h1.trans h2)

  have h_total_mass : ∑ j : Fin N, mass j = angular.shading.mass :=
    grouping.incidence_mass_additive

  have h_aggregate' : Kakeya.realRpowENN δ inputExponent * F.enncard * V ≤ angular.shading.mass :=
    h_aggregate

  have h_occurrence : ∑ j : Fin N, enncard j ≤ 1000000 * F.enncard :=
    grouping.tube_occurrence_bound

  -- Step 1: Discard low-density groups using helper.
  let densityFloorENN := Kakeya.realRpowENN δ densityFloor

  let S_low : Finset (Fin N) :=
    Finset.univ.filter (fun j => mass j < densityFloorENN * enncard j * V)

  let H : Finset (Fin N) := Finset.univ \ S_low

  have hH_def : H = Finset.univ.filter (fun j => densityFloorENN * enncard j * V ≤ mass j) := by
    ext j
    simp only [H, S_low, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and]
    <;> simp [not_lt]
    <;> tauto

  have h_low_mass : ∑ j ∈ S_low, mass j ≤ angular.shading.mass / 2 :=
    h_low_discard δ hδ_pos hδ_le_low N F.enncard V angular.shading.mass enncard mass
      h_occurrence h_aggregate'

  -- High-density mass ≥ half total
  have h_disj : Disjoint H S_low := by
    have h : Disjoint S_low (Finset.univ \ S_low) := Finset.disjoint_sdiff
    exact h.symm
  have h_union : H ∪ S_low = Finset.univ := by
    exact Finset.sdiff_union_of_subset (Finset.subset_univ S_low)
  have h_H_sum : ∑ j ∈ H, mass j + ∑ j ∈ S_low, mass j = angular.shading.mass := by
    rw [← Finset.sum_union h_disj, h_union, h_total_mass]

  set highMass : ENNReal := ∑ j ∈ H, mass j with highMass_def
  set lowMass : ENNReal := ∑ j ∈ S_low, mass j with lowMass_def
  set totalMass : ENNReal := angular.shading.mass with totalMass_def

  have h_high_mass : totalMass / 2 ≤ highMass := by
    have h_eq : highMass + lowMass = totalMass := h_H_sum
    have h_low : lowMass ≤ totalMass / 2 := h_low_mass
    have h_ne_top : totalMass ≠ ⊤ := h_angular_mass_ne_top
    have h1 : totalMass ≤ highMass + totalMass / 2 := by
      calc totalMass = highMass + lowMass := h_eq.symm
        _ ≤ highMass + totalMass / 2 := by gcongr
    have h2 : (2 : ENNReal) * totalMass ≤ (2 : ENNReal) * highMass + totalMass := by
      have h3 : (2 : ENNReal) * totalMass ≤ (2 : ENNReal) * (highMass + totalMass / 2) := by gcongr
      have h4 : (2 : ENNReal) * (highMass + totalMass / 2) =
          (2 : ENNReal) * highMass + (2 : ENNReal) * (totalMass / 2) := by
        rw [mul_add]
      have h5 : (2 : ENNReal) * (totalMass / 2) = totalMass := by
        have h6 : totalMass / 2 = (2 : ENNReal)⁻¹ * totalMass := by
          simp [div_eq_mul_inv]
          <;> ring
        rw [h6]
        have h7 : (2 : ENNReal) * ((2 : ENNReal)⁻¹ * totalMass) =
            ((2 : ENNReal) * (2 : ENNReal)⁻¹) * totalMass := by rw [mul_assoc]
        rw [h7]
        have h8 : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 :=
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
        rw [h8, one_mul]
      rw [h4, h5] at h3
      exact h3
    have h9 : totalMass + totalMass ≤ (2 : ENNReal) * highMass + totalMass := by
      have h10 : (2 : ENNReal) * totalMass = totalMass + totalMass := by
        simp [two_mul] <;> rfl
      rw [h10] at h2
      exact h2
    have h11 : totalMass ≤ (2 : ENNReal) * highMass :=
      (ENNReal.add_le_add_iff_right h_ne_top).mp h9
    have h12 : totalMass / 2 ≤ highMass := by
      have h13 : totalMass / 2 = (2 : ENNReal)⁻¹ * totalMass := by
        simp [div_eq_mul_inv] <;> ring
      rw [h13]
      have h14 : (2 : ENNReal)⁻¹ * totalMass ≤ (2 : ENNReal)⁻¹ * ((2 : ENNReal) * highMass) := by gcongr
      have h15 : (2 : ENNReal)⁻¹ * ((2 : ENNReal) * highMass) = highMass := by
        rw [← mul_assoc]
        have h16 : (2 : ENNReal)⁻¹ * (2 : ENNReal) = 1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
        rw [h16, one_mul]
      rw [h15] at h14
      exact h14
    exact h12

  have hH_nonempty : H.Nonempty := by
    by_contra h
    have h' : H = ∅ := by simpa using h
    have h_zero : highMass = 0 := by
      rw [highMass_def, h']
      <;> simp
    rw [h_zero] at h_high_mass
    have h_pos : 0 < totalMass :=
      lt_of_le_of_ne (by positivity) (mass_pos_from_aggregate hδ_pos h_input_pos hF_nonempty hV_pos.ne' h_aggregate').symm
    have h_contra : totalMass / 2 ≤ 0 := h_high_mass
    have h_totalMass_zero : totalMass = 0 := by
      have h1 : totalMass / 2 = 0 := by simpa using h_contra
      have h2 : totalMass / 2 = (2 : ENNReal)⁻¹ * totalMass := by
        simp [div_eq_mul_inv] <;> ring
      rw [h2] at h1
      have h3 : (2 : ENNReal)⁻¹ * totalMass = 0 := h1
      have h4 : totalMass = 0 := by
        by_contra h6
        have h7 : (2 : ENNReal)⁻¹ * totalMass ≠ 0 := (ENNReal.mul_pos (by norm_num) h6).ne'
        exact h7 h3
      exact h4
    exact h_pos.ne' h_totalMass_zero

  -- Step 2: Define dyadic bin counts.
  let logInvDelta : ℝ := Real.log (1 / δ)
  have h_logInvDelta_nonneg : 0 ≤ logInvDelta := by linarith

  let K_card : ℕ := Nat.floor (cardExponent * logInvDelta / Real.log 2) + 1
  let K_density : ℕ := Nat.floor (densityFloor * logInvDelta / Real.log 2) + 1

  have hK_card_bound := dyadic_K_bound cardExponent h_card_pos hδ_pos hδ_le_one
  have hK_density_bound := dyadic_K_bound densityFloor h_densityFloor_pos hδ_pos hδ_le_one

  have hK_card_pos : 0 < K_card := hK_card_bound.1
  have hK_density_pos : 0 < K_density := hK_density_bound.1
  have hK_card_gt : (2 : ℝ)^K_card > Real.rpow δ (-cardExponent) := hK_card_bound.2.2
  have hK_density_gt : (2 : ℝ)^K_density > Real.rpow δ (-densityFloor) := hK_density_bound.2.2

  have h_K_product_le : (K_card * K_density : ℝ) ≤
      ((cardExponent / Real.log 2 + 1) * (densityFloor / Real.log 2 + 1)) * logInvDelta^2 :=
    dyadic_K_product_bound cardExponent densityFloor h_card_pos h_densityFloor_pos hδ_pos hδ_le_one
      h_logInvDelta_ge_one

  have h_log_absorb' : C_log * logInvDelta^2 ≤ Real.rpow δ (-balanceLoss) :=
    h_absorb_log δ hδ_pos hδ_le_log

  have h_K_product_ennreal : (2 * K_card * K_density : ENNReal) ≤ Kakeya.realRpowENN δ (-balanceLoss) := by
    have h4 : (2 * K_card * K_density : ℝ) ≤ Real.rpow δ (-balanceLoss) := by
      calc (2 * K_card * K_density : ℝ)
          = 2 * (K_card : ℝ) * (K_density : ℝ) := by norm_cast
        _ = 2 * (K_card * K_density : ℝ) := by ring
        _ ≤ 2 * (((cardExponent / Real.log 2 + 1) * (densityFloor / Real.log 2 + 1)) * logInvDelta^2) := by
          gcongr
        _ = C_log * logInvDelta^2 := by simp [C_log] <;> ring
        _ ≤ Real.rpow δ (-balanceLoss) := h_log_absorb'
    have h5 : (2 * K_card * K_density : ENNReal) = ENNReal.ofReal (2 * K_card * K_density : ℝ) := by
      norm_cast
    rw [h5]
    exact ENNReal.ofReal_mono h4

  -- Step 3: Assign cardinality bins.
  let k : Fin N → ℕ := fun j => Nat.log 2 (card j)

  have h_k_lower : ∀ j, 2 ^ k j ≤ card j := by
    intro j
    have h_pos : 0 < card j := h_card_j_pos j
    exact Nat.pow_log_le_self 2 (h_card_j_pos j).ne'

  have h_k_upper : ∀ j, card j < 2 ^ (k j + 1) := by
    intro j
    exact Nat.lt_pow_succ_log_self (by norm_num) (card j)

  have hF_card_real : (F.card : ℝ) ≤ Real.rpow δ (-cardExponent) :=
    card_le_rpow_real hδ_pos hF_card

  have h_k_bound : ∀ j ∈ H, k j < K_card := by
    intro j _
    have h1 : card j ≤ F.card := Finset.card_le_card (grouping.family_subset j)
    have h2 : (card j : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast h1
    have h3 : (card j : ℝ) ≤ Real.rpow δ (-cardExponent) := h2.trans hF_card_real
    have h4 : (2 ^ k j : ℝ) ≤ (card j : ℝ) := by exact_mod_cast h_k_lower j
    have h5 : (2 ^ k j : ℝ) ≤ Real.rpow δ (-cardExponent) := h4.trans h3
    have h6 : Real.rpow δ (-cardExponent) < (2 : ℝ)^K_card := hK_card_gt
    have h7 : (2 ^ k j : ℝ) < (2 : ℝ)^K_card := h5.trans_lt h6
    have h7' : (2 ^ k j : ℕ) < (2 ^ K_card : ℕ) := by exact_mod_cast h7
    have h8 : k j < K_card := (Nat.pow_lt_pow_iff_right (by norm_num)).mp h7'
    exact h8

  -- Step 4: Assign density bins using Nat.findGreatest.
  let P (j : Fin N) (l : ℕ) : Prop :=
    (2 ^ l : ENNReal) * densityFloorENN * enncard j * V ≤ mass j

  have hP0 : ∀ j ∈ H, P j 0 := by
    intro j hj
    rw [hH_def] at hj
    simpa [P, Finset.mem_filter] using (Finset.mem_filter.mp hj).2

  -- P(K_density) is false for all j
  have h_not_P_K : ∀ j, ¬ P j K_density := by
    intro j
    intro h_contra
    have h4 : mass j ≤ enncard j * V := h_mass_le j
    have h_pos1 : 0 < enncard j * V := ENNReal.mul_pos (h_enncard_pos j).ne' hV_pos.ne'
    have h_ne_top1 : enncard j * V ≠ ⊤ := ENNReal.mul_ne_top (h_enncard_ne_top j) hV_ne_top
    have h5 : (2 ^ K_density : ENNReal) * densityFloorENN ≤ 1 := by
      have h_raw : (2 ^ K_density : ENNReal) * densityFloorENN * enncard j * V ≤ enncard j * V :=
        le_trans h_contra h4
      have h_eq : (2 ^ K_density : ENNReal) * densityFloorENN * enncard j * V =
          (enncard j * V) * ((2 ^ K_density : ENNReal) * densityFloorENN) := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      have h_comm : (enncard j * V) * ((2 ^ K_density : ENNReal) * densityFloorENN) ≤ enncard j * V := by
        rw [← h_eq]
        exact h_raw
      have h6 : (enncard j * V) * ((2 ^ K_density : ENNReal) * densityFloorENN) ≤ (enncard j * V) * 1 := by
        simpa [one_mul] using h_comm
      exact (ENNReal.mul_le_mul_iff_right h_pos1.ne' h_ne_top1).mp h6
    have h7 : ((2 ^ K_density : ℝ) * Real.rpow δ densityFloor) ≤ 1 := by
      have h8 : (2 ^ K_density : ENNReal) * densityFloorENN =
          ENNReal.ofReal ((2 ^ K_density : ℝ) * Real.rpow δ densityFloor) := by
        simp [densityFloorENN, Kakeya.realRpowENN]
        <;> rw [ENNReal.ofReal_mul] <;> positivity
      rw [h8] at h5
      exact_mod_cast h5
    have h9 : (1 : ℝ) < (2 : ℝ)^K_density * Real.rpow δ densityFloor := by
      have h10 : (2 : ℝ)^K_density > Real.rpow δ (-densityFloor) := hK_density_gt
      have h_pos_rpow : 0 < Real.rpow δ densityFloor := Real.rpow_pos_of_pos hδ_pos densityFloor
      have h11 : (2 : ℝ)^K_density * Real.rpow δ densityFloor > Real.rpow δ (-densityFloor) * Real.rpow δ densityFloor := by
        gcongr
      have h12 : Real.rpow δ (-densityFloor) * Real.rpow δ densityFloor = 1 := by
        have h_sum : Real.rpow δ ((-densityFloor) + densityFloor) =
            Real.rpow δ (-densityFloor) * Real.rpow δ densityFloor :=
          Real.rpow_add hδ_pos (-densityFloor) densityFloor
        have h13 : Real.rpow δ (-densityFloor) * Real.rpow δ densityFloor =
            Real.rpow δ ((-densityFloor) + densityFloor) := h_sum.symm
        rw [h13]
        have h14 : (-densityFloor) + densityFloor = 0 := by ring
        simp [h14]
      rw [h12] at h11
      exact h11
    linarith

  let l (j : Fin N) : ℕ := Nat.findGreatest (P j) K_density

  have h_l_le_K : ∀ j, l j ≤ K_density := by
    intro j
    exact Nat.findGreatest_le (n := K_density)

  have h_P_l : ∀ j ∈ H, P j (l j) := by
    intro j hj
    have h_exists : ∃ n : ℕ, n ≤ K_density ∧ P j n :=
      ⟨0, by omega, hP0 j hj⟩
    exact Nat.findGreatest_spec (hmb := by omega) (hm := hP0 j hj)

  have h_l_lt_K : ∀ j ∈ H, l j < K_density := by
    intro j hj
    have h_le : l j ≤ K_density := h_l_le_K j
    by_contra h
    have h' : l j = K_density := by omega
    have h_p : P j (l j) := h_P_l j hj
    rw [h'] at h_p
    exact h_not_P_K j h_p

  have h_not_P_succ : ∀ j ∈ H, ¬ P j (l j + 1) := by
    intro j hj
    have h_lt : l j < K_density := h_l_lt_K j hj
    have h_le : l j + 1 ≤ K_density := by omega
    by_contra h2
    have h3 : l j + 1 ≤ l j := by
      have h4 : l j + 1 ≤ Nat.findGreatest (P j) K_density := Nat.le_findGreatest (hmb := h_le) (hm := h2)
      simpa [l] using h4
    omega

  -- Step 5: Two-dimensional pigeonhole.
  let numBins : ℕ := K_card * K_density
  have h_numBins_pos : 0 < numBins := by positivity

  let bin : Fin N → Fin numBins := fun j =>
    if h : k j < K_card ∧ l j < K_density then
      ⟨k j * K_density + l j, by
        have h1 : k j < K_card := h.1
        have h2 : l j < K_density := h.2
        have h3 : k j * K_density + l j < K_card * K_density := by
          calc k j * K_density + l j
            < k j * K_density + K_density := by gcongr
          _ = (k j + 1) * K_density := by ring
          _ ≤ K_card * K_density := by
            have h4 : k j + 1 ≤ K_card := by omega
            nlinarith
        exact h3⟩
    else
      ⟨0, by positivity⟩

  let massH : Fin N → ENNReal := fun j => if j ∈ H then mass j else 0

  have h_sum_massH : ∑ j : Fin N, massH j = ∑ j ∈ H, mass j := by
    rw [Finset.sum_ite]
    <;> simp

  let total : ENNReal := totalMass / 2
  have h_total : total ≤ ∑ j : Fin N, massH j := by
    rw [h_sum_massH]
    exact h_high_mass

  rcases finset_pigeonhole_mass hN_pos h_numBins_pos massH bin total h_total with
    ⟨idx, h_idx_mass⟩

  -- Decode idx into (k0, l0)
  let k0 : ℕ := idx.val / K_density
  let l0 : ℕ := idx.val % K_density
  have h_k0_lt : k0 < K_card := by
    have h1 : idx.val < K_card * K_density := by simpa [numBins] using idx.is_lt
    exact (Nat.div_lt_iff_lt_mul hK_density_pos).mpr h1
  have h_l0_lt : l0 < K_density := by
    have h1 : idx.val % K_density < K_density := Nat.mod_lt idx.val hK_density_pos
    exact h1

  let selectedSet : Finset (Fin N) := H.filter (fun j => bin j = idx)

  have h_selected_sum : ∑ j : Fin N, (if bin j = idx then massH j else 0) =
      ∑ j ∈ selectedSet, mass j := by
    have h1 : ∑ j : Fin N, (if bin j = idx then massH j else 0) =
        ∑ j ∈ (Finset.univ.filter (fun j => bin j = idx)), massH j := by
      rw [Finset.sum_ite]
      <;> simp
    rw [h1]
    have h2 : ∑ j ∈ (Finset.univ.filter (fun j => bin j = idx)), massH j =
        ∑ j ∈ selectedSet, mass j := by
      simp [massH, selectedSet, Finset.sum_ite, Finset.filter_filter]
      <;> congr
      <;> ext x
      <;> simp [and_comm]
      <;> tauto
    exact h2

  have h_mass_bin : total / (numBins : ENNReal) ≤ ∑ j ∈ selectedSet, mass j := by
    rw [h_selected_sum] at h_idx_mass
    exact h_idx_mass

  have h_selected_nonempty : selectedSet.Nonempty := by
    by_contra h
    have h' : selectedSet = ∅ := by simpa using h
    have h_contra : total / (numBins : ENNReal) ≤ 0 := by
      rw [h'] at h_mass_bin
      simpa using h_mass_bin
    have h_ne_zero : totalMass ≠ 0 := mass_pos_from_aggregate hδ_pos h_input_pos hF_nonempty hV_pos.ne' h_aggregate'
    have h_pos : 0 < totalMass := lt_of_le_of_ne (by positivity) h_ne_zero.symm
    have h_total_pos : 0 < total := by
      dsimp only [total]
      exact ENNReal.half_pos h_ne_zero
    have h_numBins_ne_top : (numBins : ENNReal) ≠ ⊤ := by exact_mod_cast (by simp)
    have h5 : 0 < total / (numBins : ENNReal) := by
      simpa [div_eq_mul_inv] using ENNReal.mul_pos h_total_pos.ne' (ENNReal.inv_ne_zero.mpr h_numBins_ne_top)
    have h6 : ¬ (total / (numBins : ENNReal) ≤ 0) := by
      intro h7
      have h8 : total / (numBins : ENNReal) = 0 := by simpa using h7
      rw [h8] at h5
      simpa using h5
    exact h6 h_contra

  -- Extract selected indices using helper
  rcases finset_extract_fin h_selected_nonempty mass with
    ⟨selectedCount, h_selectedCount_pos, select, h_select_injective, h_select_range, h_sum_select⟩

  have h_select_in_selected : ∀ i, select i ∈ selectedSet := by
    intro i
    have h1 : select i ∈ Set.range select := Set.mem_range_self i
    rw [h_select_range] at h1
    exact h1

  have h_select_in_H : ∀ i, select i ∈ H := by
    intro i
    have h1 : select i ∈ selectedSet := h_select_in_selected i
    exact (Finset.mem_filter.mp h1).1

  have h_bin_eq : ∀ i, bin (select i) = idx := by
    intro i
    have h1 : select i ∈ selectedSet := h_select_in_selected i
    exact (Finset.mem_filter.mp h1).2

  -- For selected groups, k(select i) = k0 and l(select i) = l0
  have h_bin_val : ∀ i, (bin (select i)).val = k (select i) * K_density + l (select i) := by
    intro i
    have h1 : k (select i) < K_card := h_k_bound (select i) (h_select_in_H i)
    have h2 : l (select i) < K_density := h_l_lt_K (select i) (h_select_in_H i)
    have h_isLt : k (select i) * K_density + l (select i) < numBins := by
      have h3 : k (select i) * K_density + l (select i) < (k (select i) + 1) * K_density := by
        nlinarith
      have h4 : (k (select i) + 1) * K_density ≤ K_card * K_density := by
        gcongr <;> omega
      have h5 : K_card * K_density = numBins := by rfl
      exact lt_of_lt_of_le h3 (h4.trans_eq h5)
    have h3 : bin (select i) = ⟨k (select i) * K_density + l (select i), h_isLt⟩ := by
      unfold bin
      rw [dif_pos (And.intro h1 h2)]
      <;> rfl
    rw [h3]
    <;> rfl

  have h_k_eq : ∀ i, k (select i) = k0 := by
    intro i
    have h1 : (bin (select i)).val = k (select i) * K_density + l (select i) := h_bin_val i
    have h2 : bin (select i) = idx := h_bin_eq i
    have h3 : k (select i) * K_density + l (select i) = idx.val := by
      rw [← h1, h2]
    have h4 : l (select i) < K_density := h_l_lt_K (select i) (h_select_in_H i)
    have h5 : idx.val / K_density = k (select i) := by
      have h_eq : idx.val = k (select i) * K_density + l (select i) := h3.symm
      rw [h_eq]
      have h_div : (k (select i) * K_density + l (select i)) / K_density = k (select i) := by
        have h_comm : k (select i) * K_density + l (select i) = l (select i) + k (select i) * K_density := by ring
        rw [h_comm]
        rw [Nat.add_mul_div_right _ _ hK_density_pos]
        have h_l_div : l (select i) / K_density = 0 := by
          apply Nat.div_eq_of_lt
          exact h4
        rw [h_l_div]
        <;> ring
      exact h_div
    simpa [k0] using h5.symm

  have h_l_eq : ∀ i, l (select i) = l0 := by
    intro i
    have h1 : (bin (select i)).val = k (select i) * K_density + l (select i) := h_bin_val i
    have h2 : bin (select i) = idx := h_bin_eq i
    have h3 : k (select i) * K_density + l (select i) = idx.val := by
      rw [← h1, h2]
    have h4 : l (select i) < K_density := h_l_lt_K (select i) (h_select_in_H i)
    have h5 : l (select i) = idx.val % K_density := by
      have h_eq : idx.val = k (select i) * K_density + l (select i) := h3.symm
      have h_mod : idx.val % K_density = l (select i) := by
        rw [h_eq]
        have h : (k (select i) * K_density + l (select i)) % K_density = l (select i) := by
          have h' : (k (select i) * K_density + l (select i)) % K_density = l (select i) % K_density := by
            rw [add_comm (k (select i) * K_density) (l (select i))]
            exact Nat.add_mul_mod_self_right (l (select i)) (k (select i)) K_density
          rw [h', Nat.mod_eq_of_lt h4]
        exact h
      exact h_mod.symm
    simpa [l0] using h5

  -- Step 6: Construct output data.
  let typicalCard : ℕ := 2 ^ k0
  let typicalDensity : ENNReal := (2 ^ l0 : ENNReal) * densityFloorENN

  have h_typicalCard_pos : 0 < typicalCard := by positivity

  have h_typicalDensity_pos : typicalDensity ≠ 0 := by
    have h1 : (2 ^ l0 : ENNReal) ≠ 0 := by positivity
    have h2 : densityFloorENN ≠ 0 := by
      simp [densityFloorENN, Kakeya.realRpowENN] <;> positivity
    exact mul_ne_zero h1 h2

  have h_typicalDensity_ne_top : typicalDensity ≠ ⊤ := by
    have h1 : (2 ^ l0 : ENNReal) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
    have h2 : densityFloorENN ≠ ⊤ := by
      simp [densityFloorENN, Kakeya.realRpowENN] <;> exact ENNReal.ofReal_ne_top
    exact ENNReal.mul_ne_top h1 h2

  have h_density_floor : densityFloorENN ≤ typicalDensity := by
    have h1 : (1 : ENNReal) ≤ (2 ^ l0 : ENNReal) := by
      exact_mod_cast Nat.one_le_pow l0 2 (by norm_num)
    calc densityFloorENN
        = (1 : ENNReal) * densityFloorENN := by simp
      _ ≤ (2 ^ l0 : ENNReal) * densityFloorENN := by gcongr
      _ = typicalDensity := by rfl

  have h_card_lower : ∀ i, typicalCard ≤ card (select i) := by
    intro i
    have h2 : k (select i) = k0 := h_k_eq i
    have h3 : 2 ^ k (select i) ≤ card (select i) := h_k_lower (select i)
    rw [h2] at h3
    simpa [typicalCard] using h3

  have h_card_upper : ∀ i, card (select i) < 2 * typicalCard := by
    intro i
    have h2 : k (select i) = k0 := h_k_eq i
    have h3 : card (select i) < 2 ^ (k (select i) + 1) := h_k_upper (select i)
    rw [h2] at h3
    have h4 : 2 ^ (k0 + 1) = 2 * typicalCard := by
      simp [typicalCard, pow_succ]
      <;> ring
    rw [h4] at h3
    exact h3

  have h_density_lower : ∀ i, typicalDensity * enncard (select i) * V ≤ mass (select i) := by
    intro i
    have h2 : l (select i) = l0 := h_l_eq i
    have h3 : P (select i) (l (select i)) := h_P_l (select i) (h_select_in_H i)
    rw [h2] at h3
    simpa [typicalDensity, P] using h3

  have h_density_upper : ∀ i, mass (select i) < 2 * typicalDensity * enncard (select i) * V := by
    intro i
    have h2 : l (select i) = l0 := h_l_eq i
    have h3 : ¬ P (select i) (l (select i) + 1) := h_not_P_succ (select i) (h_select_in_H i)
    rw [h2] at h3
    have h4 : ¬ ((2 ^ (l0 + 1) : ENNReal) * densityFloorENN * enncard (select i) * V ≤ mass (select i)) := h3
    have h_eq : (2 ^ (l0 + 1) : ENNReal) * densityFloorENN = 2 * typicalDensity := by
      have h_pow : (2 ^ (l0 + 1) : ENNReal) = (2 : ENNReal) * (2 ^ l0 : ENNReal) := by
        norm_cast <;> simp [pow_succ] <;> ring
      rw [h_pow]
      simp [typicalDensity, mul_assoc]
    have h5 : ¬ (2 * typicalDensity * enncard (select i) * V ≤ mass (select i)) := by
      rw [← h_eq]
      exact h4
    exact lt_of_not_ge h5

  -- Mass retention
  have h2numBins_pos : (2 * numBins : ENNReal) ≠ 0 := by
    exact_mod_cast (show 0 < 2 * numBins by positivity).ne'
  have h2numBins_top : (2 * numBins : ENNReal) ≠ ⊤ := by
    have h : (2 * numBins : ENNReal) = ↑(2 * numBins) := by norm_cast
    rw [h]
    exact ENNReal.natCast_ne_top _

  have h_rpow_neg_pos : Kakeya.realRpowENN δ (-balanceLoss) ≠ 0 := by
    simp [Kakeya.realRpowENN] <;> positivity
  have h_rpow_neg_top : Kakeya.realRpowENN δ (-balanceLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN] <;> exact ENNReal.ofReal_ne_top

  have h8 : (2 * numBins : ENNReal) ≤ Kakeya.realRpowENN δ (-balanceLoss) := by
    have h9 : 2 * K_card * K_density = 2 * numBins := by
      simp [numBins] <;> ring
    have h10 : (2 * K_card * K_density : ENNReal) = (2 * numBins : ENNReal) := by exact_mod_cast h9
    rw [← h10]
    exact h_K_product_ennreal

  have h7 : Kakeya.realRpowENN δ balanceLoss ≤ (2 * numBins : ENNReal)⁻¹ := by
    have h10 : Kakeya.realRpowENN δ balanceLoss = (Kakeya.realRpowENN δ (-balanceLoss))⁻¹ := by
      have h11 := realRpowENN_add hδ_pos balanceLoss (-balanceLoss)
      have h12 : balanceLoss + (-balanceLoss) = 0 := by ring
      rw [h12] at h11
      have h13 : Kakeya.realRpowENN δ 0 = 1 := by
        simp [Kakeya.realRpowENN]
      rw [h13] at h11
      exact ENNReal.eq_inv_of_mul_eq_one_left h11.symm
    rw [h10]
    exact ENNReal.inv_le_inv.mpr h8

  have h_mass_retention : Kakeya.realRpowENN δ balanceLoss * totalMass ≤
      ∑ i : Fin selectedCount, mass (select i) := by
    rw [h_sum_select]
    have h4 : total / (numBins : ENNReal) ≤ ∑ j ∈ selectedSet, mass j := h_mass_bin
    have h5 : total / (numBins : ENNReal) =
        ((2 * numBins : ENNReal)⁻¹) * totalMass := by
      have h6 : total = totalMass / 2 := by rfl
      rw [h6]
      have h_inv : (2 * numBins : ENNReal)⁻¹ = (2 : ENNReal)⁻¹ * (numBins : ENNReal)⁻¹ := by
        rw [ENNReal.mul_inv] <;> simp [h2numBins_pos, h2numBins_top] <;> norm_num
      rw [h_inv]
      simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    rw [h5] at h4
    calc ∑ j ∈ selectedSet, mass j
      ≥ ((2 * numBins : ENNReal)⁻¹) * totalMass := h4
    _ ≥ Kakeya.realRpowENN δ balanceLoss * totalMass := by
      gcongr
      <;> exact h7

  exact ⟨selectedCount, h_selectedCount_pos, select, h_select_injective,
    typicalCard, h_typicalCard_pos, typicalDensity, h_typicalDensity_pos,
    h_typicalDensity_ne_top, h_density_floor, h_card_lower, h_card_upper,
    h_density_lower, h_density_upper, h_mass_retention⟩

end Kakeya.Assouad
