module

/-
  B1 Assembly — Package the entire B1 bridge construction.

  Given a NiceConfiguration and supporting data, this module:
  1. Applies b1_fine_card_lower_general (ε/5) for pre-filter fine lower
  2. Heavy parent filtering to retain only heavy coarse squares
  3. Restricts the NiceConfiguration to heavy points
  4. Transfers S-set and ball growth to restricted centers via half-retention
  5. Constructs the full B1BridgeDecomposition for the restricted config

  Main theorem: `b1_assembly` returns restricted config + B1BridgeDecomposition.

  Whiteprint node: b1_assembly
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicBridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.B1FineCardLower
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.HeavyParentFiltering
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.B1CardBounds
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.B1HardFields
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.ScaleConversionHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.SquareGeometry
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.B1BridgeWiring
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.B1PerSquareViaRef
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction.B1InductionApplication
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction.SsetExtractionBounds
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.DyadicSquareCenterSeparation
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.UniformAppendixAAlternative
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.B1ToA1Skeleton
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Phase2Support
public import MyLeanRepo.OSWPrelude

@[expose] public section

set_option maxHeartbeats 500000

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas.B1Assembly

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction
open DiscretisedFurstenbergEstimate.CombiningTheorem
open HeavyParentFiltering
open InductionConfigurations
open B1HardFields
open SquareGeometry

abbrev NiceConfig n s C₁ M := CombiningTheorem.NiceConfiguration n s C₁ M
abbrev DSquare n := DiscretisedFurstenbergEstimate.DyadicSquare n
abbrev DTube n := DiscretisedFurstenbergEstimate.DyadicTube n

/-! ### Restricted S-set helper

    Transfer S-set from superset B to subset A when A retains ≥ half cardinality
    and B is δ-separated. Constant multiplies by 50.
-/

/-- Transfer S-set from B to A with |B| ≤ 2|A| and B δ-separated. -/
lemma restricted_sset_half_retention
    {δ u C : ℝ}
    {A B : Finset EuclideanPlane}
    (hδ_pos : 0 < δ)
    (hu_nonneg : 0 ≤ u)
    (hC_pos : 0 < C)
    (hA_nonempty : A.Nonempty)
    (hA_sub_B : A ⊆ B)
    (h_card_ratio : (B.card : ℝ) ≤ 2 * (A.card : ℝ))
    (hB_sep : Set.Pairwise (B : Set EuclideanPlane) (fun p q => δ ≤ dist p q))
    (hB_sset : IsDeltaSSet δ u C (B : Set EuclideanPlane)) :
    IsDeltaSSet δ u (50 * C) (A : Set EuclideanPlane) := by
  have hA_sep : Set.Pairwise (A : Set EuclideanPlane) (fun p q => δ ≤ dist p q) :=
    fun p hp q hq hne => hB_sep (hA_sub_B hp) (hA_sub_B hq) hne
  have hN_B_le_card : (Metric.externalCoveringNumber δ.toNNReal (B : Set EuclideanPlane) : ENNReal) ≤
      (B.card : ENNReal) := by
    have h : Metric.externalCoveringNumber δ.toNNReal (B : Set EuclideanPlane) ≤
        (B : Set EuclideanPlane).encard := Metric.externalCoveringNumber_le_encard_self _
    have h2 : (B : Set EuclideanPlane).encard = ↑B.card := by simp
    rw [h2] at h
    exact_mod_cast h
  have hcard_A_le_25N_A : (A.card : ENNReal) ≤
      (25 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (A : Set EuclideanPlane) : ENNReal) := by
    have h : (A.card : ENat) ≤ 25 * Metric.externalCoveringNumber δ.toNNReal (A : Set EuclideanPlane) :=
      separated_card_le_25_cover hδ_pos (hS_sep := hA_sep)
    exact_mod_cast h
  have hN_B_le_50_N_A : (Metric.externalCoveringNumber δ.toNNReal (B : Set EuclideanPlane) : ENNReal) ≤
      ENNReal.ofReal (50 : ℝ) * (Metric.externalCoveringNumber δ.toNNReal (A : Set EuclideanPlane) : ENNReal) := by
    calc (Metric.externalCoveringNumber δ.toNNReal (B : Set EuclideanPlane) : ENNReal)
      ≤ (B.card : ENNReal) := hN_B_le_card
    _ ≤ (2 : ENNReal) * (A.card : ENNReal) := by exact_mod_cast h_card_ratio
    _ ≤ (2 : ENNReal) * ((25 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (A : Set EuclideanPlane) : ENNReal)) := by gcongr
    _ = (50 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal (A : Set EuclideanPlane) : ENNReal) := by ring_nf
    _ = ENNReal.ofReal (50 : ℝ) * (Metric.externalCoveringNumber δ.toNNReal (A : Set EuclideanPlane) : ENNReal) := by simp
  exact B1HardFields.subset_sset_with_ncover_ratio hδ_pos hu_nonneg hC_pos (by norm_num)
    hA_nonempty (show (A : Set EuclideanPlane) ⊆ (B : Set EuclideanPlane) from hA_sub_B)
    hB_sset hN_B_le_50_N_A

/-! ### Main B1 assembly theorem -/

/-- Assemble the B1 bridge decomposition with heavy parent filtering. -/
theorem b1_assembly
    {n m : ℕ} (hnm : m ≤ n) (hn_even : n % 2 = 0)
    {s C₁ : ℝ} {M : ℕ}
    (config : NiceConfig n s C₁ M)
    {Δ δ_n δ u ε εA ρ_mass C C_Pbar : ℝ}
    -- Numerical
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hδ_n_pos : 0 < δ_n)
    (hδ_n_eq : δ_n = DiscretisedFurstenbergEstimate.dyadicDelta n)
    (hδ_n_eq2 : δ_n = Δ ^ 2)
    (hΔ_eq : Δ = DiscretisedFurstenbergEstimate.dyadicDelta m)
    (hδ_ge : δ_n / 4 ≤ δ)
    (hu_nonneg : 0 ≤ u) (hε_pos : 0 < ε) (hεA_pos : 0 < εA)
    (hρ_mass_nonneg : 0 ≤ ρ_mass)
    (hC_pos : 0 < C) (hC_Pbar_pos : 0 < C_Pbar)
    (hC_eq : C = 81 * Real.rpow δ (-εA))
    (h_exponent_eps5 : 2 * εA + 2 * ρ_mass < ε / 5)
    (hΔ_small_eps5 : (1 / 810000 : ℝ) * Real.rpow 4 (-εA) ≥
        Real.rpow Δ (ε / 5 - 2 * εA - 2 * ρ_mass))
    -- Pbar data
    {Pbar : Finset EuclideanPlane}
    (hPbar_sset : IsDeltaSSet δ_n u C_Pbar (Pbar : Set EuclideanPlane))
    (hPbar_sep : Set.Pairwise (Pbar : Set EuclideanPlane) (fun p q => δ_n ≤ dist p q))
    (hPbar_ncover_lower : Metric.externalCoveringNumber δ_n.toNNReal (Pbar : Set EuclideanPlane) ≥
        ENNReal.ofReal ((1 / 10000 : ℝ) * C⁻¹ * Real.rpow δ_n (-u)))
    -- pointSet data
    {pointSet : Set EuclideanPlane}
    (hpointSet_sub : pointSet ⊆
      ⋃ p ∈ (config.P₀ : Set (DSquare n)), (p.toSet : Set EuclideanPlane))
    (hNcover_pointSet_lower : Metric.externalCoveringNumber δ_n.toNNReal pointSet ≥
        ENNReal.ofReal (Real.rpow δ_n ρ_mass) *
          Metric.externalCoveringNumber δ_n.toNNReal (Pbar : Set EuclideanPlane))
    -- P_oriented data
    {P_oriented : Set EuclideanPlane}
    (hP_oriented_sub_Pbar : P_oriented ⊆ (Pbar : Set EuclideanPlane))
    (hP_oriented_sub_pointSet : P_oriented ⊆ pointSet)
    (h_squares_meet : ∀ (q : DSquare n), q ∈ config.P₀ →
        ((q.toSet : Set EuclideanPlane) ∩ P_oriented).Nonempty)
    (h_absorb_sset : (25 : ℝ) * 625 * (2 : ℝ)^u * Real.rpow δ_n (-ρ_mass) * C_Pbar ≤
        Real.rpow δ_n (-ε))
    -- Card bounds
    (h_fine_card_upper_orig : (config.P₀.card : ℝ) ≤ Real.rpow Δ (-2 * u - ε / 4))
    (h_coarse_card_upper_orig :
        ((config.P₀.image (InductionConfigurations.containingSquare hnm)).card : ℝ) ≤
        Real.rpow Δ (-u - ε / 2))
    (h_per_square_upper_orig : ∀ Q ∈ config.P₀.image (InductionConfigurations.containingSquare hnm),
        ((config.P₀.filter (fun p => InductionConfigurations.containingSquare hnm p = Q)).card : ℝ) ≤
          Real.rpow Δ (-u - 3 * ε / 5))
    -- Tube and M
    (h_tubes_strip : ∀ (T : DTube n), T ∈ config.T₀ →
        -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ))
    (h_tubes_intercept : ∀ (p : DSquare n) (hp : p ∈ config.P₀) (T : DTube n),
        T ∈ config.tubeFamily p hp → |T.intercept| ≤ 3)
    (hM_even : M % 2 = 0)
    (hC_fine_bound : C₁ ≤ Real.rpow δ_n (-ε / 2))
    (hC₁ : 1 ≤ C₁)
    (h_tube_sset_absorb : (4000 : ℝ) * 44^s ≤ Real.rpow δ_n (-ε / 2))
    (hM_fine_lower : (M : ℝ) / 2 ≥ Real.rpow Δ (-2 * s + 2 * ε))
    (hM_fine_upper : (M : ℝ) ≤ Real.rpow Δ (-2 * s - ε))
    -- K_pack
    (K_pack : ℝ) (hK_pack_pos : 0 < K_pack)
    (hK_pack_bound : K_pack ≤ Real.rpow Δ (-2 * ε) / 6)
    -- Smallness
    (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    (h_small2 : Real.rpow Δ (ε / 20) ≤ 1 / 2)
    (h_small3 : Real.rpow Δ (3 * ε / 10) ≤ 1 / 2)
    -- Geometric
    (h_points_in_ball_R :
        ((config.P₀.image localSquareCenter) : Set (EuclideanSpace ℝ (Fin 2))) ⊆
        Metric.closedBall 0 (1 + Real.sqrt 2 * δ_n / 2))
    (h_tubes_bounded : config.T₀.card ≤ 12 * 16 ^ n) :
    ∃ (config' : NiceConfig n s C₁ M)
      (b1 : B1BridgeDecomposition n m hnm s C₁ M config' Δ δ_n u ε),
      config'.P₀ ⊆ config.P₀ ∧ config'.T₀ = config.T₀ := by
  let csq : DSquare n → DSquare m := InductionConfigurations.containingSquare hnm
  let coarseP₀_orig : Finset (DSquare m) := config.P₀.image csq
  let m_threshold : ℝ := Real.rpow Δ (-u + ε)

  -- Step 1: Pre-filter fine card lower at ε/5
  have h_fine_lower_eps5 : Real.rpow Δ (-2 * u + ε / 5) ≤ (config.P₀.card : ℝ) :=
    b1_fine_card_lower_general (ε / 5) (by linarith)
      hΔ_pos hΔ_lt_one hδ_n_pos hδ_n_eq hδ_n_eq2 hδ_ge
      hε_pos hεA_pos hρ_mass_nonneg hu_nonneg
      (Pbar := Pbar) (P₀ := config.P₀) (pointSet := pointSet)
      hpointSet_sub hPbar_ncover_lower hNcover_pointSet_lower
      hC_eq h_exponent_eps5 hΔ_small_eps5

  have hconfig_P0_nonempty : config.P₀.Nonempty := by
    have h_pos : 0 < Real.rpow Δ (-2 * u + ε / 5) := Real.rpow_pos_of_pos hΔ_pos _
    have h_card_pos : 0 < (config.P₀.card : ℝ) := lt_of_lt_of_le h_pos h_fine_lower_eps5
    exact Finset.card_pos.mp (by exact_mod_cast h_card_pos)

  -- Step 2: Heavy filtering
  have h_light_bound : (∑ Q ∈ Qlight config.P₀ csq m_threshold,
      (fiber config.P₀ csq Q).card : ℝ) ≤
      (1 / 2 : ℝ) * Real.rpow Δ (-2 * u + ε / 5) :=
    heavy_filter_light_bound config.P₀ csq Δ u ε
      hΔ_pos hΔ_lt_one hε_pos m_threshold rfl
      h_coarse_card_upper_orig h_small3

  have h_retained_mass : (∑ Q ∈ Qheavy config.P₀ csq m_threshold,
      (fiber config.P₀ csq Q).card : ℝ) ≥
      Real.rpow Δ (-2 * u + ε / 4) :=
    heavy_filter_retained_mass config.P₀ csq Δ u ε
      hΔ_pos hΔ_lt_one hε_pos m_threshold
      h_fine_lower_eps5 h_light_bound h_small2

  have h_coarse_lower : (Qheavy config.P₀ csq m_threshold).card ≥
      Real.rpow Δ (-u + ε) :=
    heavy_filter_coarse_lower config.P₀ csq Δ u ε
      hΔ_pos hΔ_lt_one hε_pos m_threshold h_retained_mass
      (fun Q hQ => h_per_square_upper_orig Q ((Finset.mem_filter.mp hQ).1))

  -- Step 3: Restrict config
  let P₀' : Finset (DSquare n) := restrictPoints config.P₀ csq m_threshold
  have hP'_subset : P₀' ⊆ config.P₀ := restrictPoints_subset config.P₀ csq m_threshold
  let config' : NiceConfig n s C₁ M := config.restrictP P₀' hP'_subset

  have hm_threshold_pos : 0 < m_threshold := Real.rpow_pos_of_pos hΔ_pos _

  have h_coarseP'_eq : coarseP₀ P₀' csq = Qheavy config.P₀ csq m_threshold :=
    restricted_coarse_eq config.P₀ csq m_threshold hm_threshold_pos

  -- Card equality
  have hP'_card_eq : (P₀'.card : ℝ) =
      ∑ Q ∈ Qheavy config.P₀ csq m_threshold, ((fiber config.P₀ csq Q).card : ℝ) := by
    have h2 : (P₀'.card : ℝ) =
        ∑ Q ∈ coarseP₀ P₀' csq, ((fiber P₀' csq Q).card : ℝ) := by
      exact_mod_cast card_eq_sum_fibers P₀' csq
    rw [h2, h_coarseP'_eq]
    have h3 : ∑ Q ∈ Qheavy config.P₀ csq m_threshold, ((fiber P₀' csq Q).card : ℝ) =
        ∑ Q ∈ Qheavy config.P₀ csq m_threshold, ((fiber config.P₀ csq Q).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro Q hQ
      have h4 : fiber P₀' csq Q = fiber config.P₀ csq Q :=
        restricted_fiber_eq_heavy config.P₀ csq m_threshold Q hQ
      rw [h4]
    exact h3

  -- Card ratio: |config.P₀| ≤ 2 * |P₀'|
  have h_sum_partition : (config.P₀.card : ℝ) =
      (∑ Q ∈ Qheavy config.P₀ csq m_threshold, ((fiber config.P₀ csq Q).card : ℝ)) +
      (∑ Q ∈ Qlight config.P₀ csq m_threshold, ((fiber config.P₀ csq Q).card : ℝ)) := by
    have h_part := heavy_light_partition config.P₀ csq m_threshold
    have h_sum : (∑ Q ∈ coarseP₀ config.P₀ csq, ((fiber config.P₀ csq Q).card : ℝ)) =
        (∑ Q ∈ Qheavy config.P₀ csq m_threshold, ((fiber config.P₀ csq Q).card : ℝ)) +
        (∑ Q ∈ Qlight config.P₀ csq m_threshold, ((fiber config.P₀ csq Q).card : ℝ)) := by
      have h4 : Qheavy config.P₀ csq m_threshold ∪ Qlight config.P₀ csq m_threshold =
          coarseP₀ config.P₀ csq := h_part.1
      have h5 : (∑ Q ∈ Qheavy config.P₀ csq m_threshold ∪ Qlight config.P₀ csq m_threshold,
            ((fiber config.P₀ csq Q).card : ℝ)) =
          (∑ Q ∈ coarseP₀ config.P₀ csq, ((fiber config.P₀ csq Q).card : ℝ)) := by
        rw [h4]
      have h6 : (∑ Q ∈ Qheavy config.P₀ csq m_threshold ∪ Qlight config.P₀ csq m_threshold,
            ((fiber config.P₀ csq Q).card : ℝ)) =
          (∑ Q ∈ Qheavy config.P₀ csq m_threshold, ((fiber config.P₀ csq Q).card : ℝ)) +
          (∑ Q ∈ Qlight config.P₀ csq m_threshold, ((fiber config.P₀ csq Q).card : ℝ)) := by
        rw [Finset.sum_union h_part.2] <;> rfl
      linarith
    have h6 := card_eq_sum_fibers config.P₀ csq
    rw [h6]
    exact h_sum
  have h_card_ratio : (config.P₀.card : ℝ) ≤ 2 * (P₀'.card : ℝ) := by
    rw [hP'_card_eq] at *
    have h7 : 2 * (∑ Q ∈ Qlight config.P₀ csq m_threshold, ((fiber config.P₀ csq Q).card : ℝ)) ≤
        (config.P₀.card : ℝ) := by
      calc 2 * (∑ Q ∈ Qlight config.P₀ csq m_threshold, ((fiber config.P₀ csq Q).card : ℝ))
        ≤ 2 * ((1 / 2 : ℝ) * Real.rpow Δ (-2 * u + ε / 5)) := by gcongr
      _ = Real.rpow Δ (-2 * u + ε / 5) := by ring
      _ ≤ (config.P₀.card : ℝ) := h_fine_lower_eps5
    linarith [h_sum_partition]

  -- Step 4: Bounds for restricted config
  have h_fine_card_lower' : Real.rpow Δ (-2 * u + ε / 4) ≤ (P₀'.card : ℝ) := by
    rw [hP'_card_eq]
    exact h_retained_mass

  have h_fine_card_upper' : (P₀'.card : ℝ) ≤ Real.rpow Δ (-2 * u - ε / 4) := by
    have h1 : (P₀'.card : ℝ) ≤ (config.P₀.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hP'_subset
    exact le_trans h1 h_fine_card_upper_orig

  let coarseP₀' : Finset (DSquare m) := Qheavy config.P₀ csq m_threshold

  have h_coarse_card_lower' : Real.rpow Δ (-u + ε) ≤ (coarseP₀'.card : ℝ) := h_coarse_lower

  have h_coarse_card_upper' : (coarseP₀'.card : ℝ) ≤ Real.rpow Δ (-u - ε / 2) := by
    have h1 : coarseP₀' ⊆ coarseP₀_orig := Finset.filter_subset _ _
    have h2 : (coarseP₀'.card : ℝ) ≤ (coarseP₀_orig.card : ℝ) := by
      exact_mod_cast Finset.card_le_card h1
    exact le_trans h2 h_coarse_card_upper_orig

  have h_per_square_lower' : ∀ Q ∈ coarseP₀',
      Real.rpow Δ (-u + ε) ≤ ((P₀'.filter (fun p => csq p = Q)).card : ℝ) := by
    intro Q hQ
    have h4 : P₀'.filter (fun p => csq p = Q) = fiber config.P₀ csq Q := by
      ext p
      simp only [P₀', restrictPoints, fiber, Finset.mem_filter]
      <;> aesop
    rw [h4]
    have h5 : m_threshold ≤ (fiber config.P₀ csq Q).card := (Finset.mem_filter.mp hQ).2
    exact_mod_cast h5

  have h_per_square_upper' : ∀ Q ∈ coarseP₀',
      ((P₀'.filter (fun p => csq p = Q)).card : ℝ) ≤ Real.rpow Δ (-u - ε) := by
    intro Q hQ
    have h4 : P₀'.filter (fun p => csq p = Q) = fiber config.P₀ csq Q := by
      ext p
      simp only [P₀', restrictPoints, fiber, Finset.mem_filter] <;> aesop
    rw [h4]
    have h5 : ((fiber config.P₀ csq Q).card : ℝ) ≤ Real.rpow Δ (-u - 3 * ε / 5) :=
      h_per_square_upper_orig Q ((Finset.mem_filter.mp hQ).1)
    have h6 : Real.rpow Δ (-u - 3 * ε / 5) ≤ Real.rpow Δ (-u - ε) :=
      weaken_per_square_upper Δ u ε hΔ_pos hΔ_lt_one hε_pos
    exact le_trans h5 h6

  -- Step 5: Original centers strong S-set
  let B : Finset EuclideanPlane := config.P₀.image localSquareCenter
  let A : Finset EuclideanPlane := P₀'.image localSquareCenter

  have h_local_eq_dyadic : (localSquareCenter : DSquare n → EuclideanPlane) =
      (dyadicSquareCenter : DSquare n → EuclideanPlane) := by
    funext q
    ext i
    simp [localSquareCenter, dyadicSquareCenter] <;> split_ifs <;> tauto

  have hB_sep : Set.Pairwise (B : Set EuclideanPlane) (fun p q => δ_n ≤ dist p q) := by
    have h := dyadicSquareCenters_separated config.P₀
    have hB_eq : (B : Set EuclideanPlane) = (config.P₀.image dyadicSquareCenter : Set EuclideanPlane) := by
      ext x; simp [B, h_local_eq_dyadic]
    rw [hB_eq]
    simpa [SSetBridges.SeparatedAt, hδ_n_eq] using h

  have hP_oriented_sub_union : P_oriented ⊆
      ⋃ p ∈ (config.P₀ : Set (DSquare n)), (p.toSet : Set EuclideanPlane) :=
    Set.Subset.trans hP_oriented_sub_pointSet hpointSet_sub

  have hNcover_union_lower : Metric.externalCoveringNumber δ_n.toNNReal
      (⋃ p ∈ (config.P₀ : Set (DSquare n)), (p.toSet : Set EuclideanPlane)) ≥
      ENNReal.ofReal (Real.rpow δ_n ρ_mass) *
        Metric.externalCoveringNumber δ_n.toNNReal (Pbar : Set EuclideanPlane) := by
    have h1 : pointSet ⊆ (⋃ p ∈ (config.P₀ : Set (DSquare n)), (p.toSet : Set EuclideanPlane)) :=
      hpointSet_sub
    have h2 : Metric.externalCoveringNumber δ_n.toNNReal pointSet ≤
        Metric.externalCoveringNumber δ_n.toNNReal
          (⋃ p ∈ (config.P₀ : Set (DSquare n)), (p.toSet : Set EuclideanPlane)) :=
      Metric.externalCoveringNumber_mono_set h1
    have h2' : (Metric.externalCoveringNumber δ_n.toNNReal pointSet : ENNReal) ≤
        (Metric.externalCoveringNumber δ_n.toNNReal
          (⋃ p ∈ (config.P₀ : Set (DSquare n)), (p.toSet : Set EuclideanPlane)) : ENNReal) := by
      exact_mod_cast h2
    exact le_trans hNcover_pointSet_lower h2'

  have hB_sset_strong : IsDeltaSSet δ_n u (Real.rpow δ_n (-ε))
      (B : Set EuclideanPlane) := by
    have hB_eq : (B : Set EuclideanPlane) = (config.P₀.image dyadicSquareCenter : Set EuclideanPlane) := by
      ext x; simp [B, h_local_eq_dyadic]
    rw [hB_eq]
    exact b1_hPfin_sset_strong
      hδ_n_pos hδ_n_eq hu_nonneg hε_pos hC_Pbar_pos hρ_mass_nonneg
      hconfig_P0_nonempty hPbar_sset hPbar_sep
      hP_oriented_sub_Pbar hP_oriented_sub_union
      h_squares_meet hNcover_union_lower h_absorb_sset

  have hA_nonempty : A.Nonempty := by
    have h_pos : 0 < (P₀'.card : ℝ) := by
      have h : 0 < Real.rpow Δ (-2 * u + ε / 4) := Real.rpow_pos_of_pos hΔ_pos _
      exact lt_of_lt_of_le h h_fine_card_lower'
    have h_card_pos : 0 < P₀'.card := by exact_mod_cast h_pos
    have hP'_nonempty : P₀'.Nonempty := Finset.card_pos.mp h_card_pos
    exact Finset.Nonempty.image hP'_nonempty _

  have hA_sub_B : A ⊆ B := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    exact Finset.mem_image.mpr ⟨p, hP'_subset hp, rfl⟩

  have h_card_ratio' : (B.card : ℝ) ≤ 2 * (A.card : ℝ) := by
    have hB_card : B.card = config.P₀.card := by
      rw [Finset.card_image_of_injective _ localSquareCenter_injective]
    have hA_card : A.card = P₀'.card := by
      rw [Finset.card_image_of_injective _ localSquareCenter_injective]
    rw [hB_card, hA_card]
    exact h_card_ratio

  -- Step 6: Restricted S-set
  have hA_sset_50 : IsDeltaSSet δ_n u (50 * Real.rpow δ_n (-ε))
      (A : Set EuclideanPlane) :=
    restricted_sset_half_retention
      hδ_n_pos hu_nonneg (Real.rpow_pos_of_pos hδ_n_pos (-ε))
      hA_nonempty hA_sub_B h_card_ratio' hB_sep hB_sset_strong

  have h_absorb_50 : 50 * Real.rpow δ_n (-ε) ≤ Real.rpow δ_n (-2 * ε) := by
    have h2 : (50 : ℝ) ≤ Real.rpow δ_n (-ε) := by
      rw [hδ_n_eq2]
      have h4 : Real.rpow (Δ ^ 2) (-ε) = Real.rpow Δ (-2 * ε) := by
        have h_pos2 : 0 ≤ Δ := by linarith
        have h_eq1 : (Δ ^ 2 : ℝ) = Real.rpow Δ 2 := (Real.rpow_natCast Δ 2).symm
        have h5 : Real.rpow (Real.rpow Δ 2) (-ε) = Real.rpow Δ (2 * (-ε)) :=
          (Real.rpow_mul h_pos2 2 (-ε)).symm
        calc Real.rpow (Δ ^ 2) (-ε)
          = Real.rpow (Real.rpow Δ 2) (-ε) := by rw [h_eq1]
        _ = Real.rpow Δ (2 * (-ε)) := h5
        _ = Real.rpow Δ (-2 * ε) := by congr 1; ring
      rw [h4]
      have h5 : Real.rpow Δ (2 * ε) ≤ 1 / 50 := by
        have h6 : 2 * ε ≥ ε / 4 := by linarith
        have h7 : Real.rpow Δ (2 * ε) ≤ Real.rpow Δ (ε / 4) :=
          Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le h6
        have h8 : Real.rpow Δ (ε / 4) ≤ 1 / 100 := h_small
        calc Real.rpow Δ (2 * ε)
          ≤ Real.rpow Δ (ε / 4) := h7
        _ ≤ 1 / 100 := h8
        _ ≤ 1 / 50 := by norm_num
      have h9 : Real.rpow Δ (-2 * ε) = (Real.rpow Δ (2 * ε))⁻¹ := by
        have h10 : -2 * ε = -(2 * ε) := by ring
        rw [h10]
        exact Real.rpow_neg (by linarith) (2 * ε)
      rw [h9]
      have h10 : 0 < Real.rpow Δ (2 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      have h11 : (Real.rpow Δ (2 * ε))⁻¹ ≥ (1 / 50 : ℝ)⁻¹ := by gcongr
      norm_num at h11 ⊢; exact h11
    have h3 : 0 ≤ Real.rpow δ_n (-ε) := Real.rpow_nonneg hδ_n_pos.le _
    have h4 : Real.rpow δ_n (-ε) * Real.rpow δ_n (-ε) = Real.rpow δ_n (-2 * ε) := by
      have h5 : Real.rpow δ_n (-ε) * Real.rpow δ_n (-ε) = Real.rpow δ_n ((-ε) + (-ε)) :=
        (Real.rpow_add hδ_n_pos (-ε) (-ε)).symm
      rw [h5]
      have h6 : (-ε) + (-ε) = -2 * ε := by ring
      rw [h6]
    have h4' : Real.rpow δ_n (-2 * ε) = Real.rpow δ_n (-ε) * Real.rpow δ_n (-ε) := h4.symm
    rw [h4']
    nlinarith

  have hPfin_sset' : IsDeltaSSet δ_n u (Real.rpow δ_n (-2 * ε))
      (A : Set EuclideanPlane) := by
    rcases hA_sset_50 with ⟨hne, hδ, hC50_pos, hs, hmain⟩
    have hC'_pos : 0 < Real.rpow δ_n (-2 * ε) := Real.rpow_pos_of_pos hδ_n_pos _
    refine' ⟨hne, hδ, hC'_pos, hs, _⟩
    intro x r hr
    have h4 := hmain x r hr
    have h5 : ENNReal.ofReal (50 * Real.rpow δ_n (-ε)) ≤ ENNReal.ofReal (Real.rpow δ_n (-2 * ε)) :=
      ENNReal.ofReal_le_ofReal h_absorb_50
    have h6 : ENNReal.ofReal (50 * Real.rpow δ_n (-ε)) * (ENNReal.ofReal r) ^ u *
        (Metric.externalCoveringNumber δ_n.toNNReal (A : Set EuclideanPlane) : ENNReal) ≤
      ENNReal.ofReal (Real.rpow δ_n (-2 * ε)) * (ENNReal.ofReal r) ^ u *
        (Metric.externalCoveringNumber δ_n.toNNReal (A : Set EuclideanPlane) : ENNReal) := by
      gcongr <;> exact h5
    exact le_trans h4 h6

  -- Step 7: Restricted ball growth
  have hB_ball_growth_raw : ∀ (c : EuclideanPlane) (r : ℝ), δ_n ≤ r →
      ((B.filter (fun y => dist c y ≤ r)).card : ℝ) ≤
        (25 : ℝ) * Real.rpow δ_n (-ε) * r^u * (B.card : ℝ) :=
    sset_ball_growth hδ_n_pos hu_nonneg (Real.rpow_pos_of_pos hδ_n_pos (-ε))
      hB_sep hB_sset_strong

  have h_absorb_ball_50 : (50 : ℝ) * Real.rpow δ_n (-ε) ≤ Real.rpow Δ (-9 * ε / 4) := by
    have h1 : Real.rpow δ_n (-ε) = Real.rpow Δ (-2 * ε) := by
      rw [hδ_n_eq2]
      have h_pos2 : 0 ≤ Δ := by linarith
      have h_eq1 : (Δ ^ 2 : ℝ) = Real.rpow Δ 2 := (Real.rpow_natCast Δ 2).symm
      have h5 : Real.rpow (Real.rpow Δ 2) (-ε) = Real.rpow Δ (2 * (-ε)) :=
        (Real.rpow_mul h_pos2 2 (-ε)).symm
      calc Real.rpow (Δ ^ 2) (-ε)
        = Real.rpow (Real.rpow Δ 2) (-ε) := by rw [h_eq1]
      _ = Real.rpow Δ (2 * (-ε)) := h5
      _ = Real.rpow Δ (-2 * ε) := by congr 1; ring
    have h3 : (50 : ℝ) ≤ Real.rpow Δ (-ε / 4) := by
      have h4 : Real.rpow Δ (ε / 4) ≤ 1 / 50 := by
        calc Real.rpow Δ (ε / 4)
          ≤ 1 / 100 := h_small
        _ ≤ 1 / 50 := by norm_num
      have h5 : Real.rpow Δ (-ε / 4) = (Real.rpow Δ (ε / 4))⁻¹ := by
        have h6 : -ε / 4 = -(ε / 4) := by ring
        rw [h6]
        exact Real.rpow_neg (by linarith) (ε / 4)
      rw [h5]
      have h6 : 0 < Real.rpow Δ (ε / 4) := Real.rpow_pos_of_pos hΔ_pos _
      have h7 : (Real.rpow Δ (ε / 4))⁻¹ ≥ (1 / 50 : ℝ)⁻¹ := by gcongr
      norm_num at h7 ⊢; exact h7
    have h8 : Real.rpow Δ (-2 * ε) * Real.rpow Δ (-ε / 4) = Real.rpow Δ (-9 * ε / 4) := by
      have h9 : Real.rpow Δ (-2 * ε) * Real.rpow Δ (-ε / 4) = Real.rpow Δ ((-2 * ε) + (-ε / 4)) :=
        (Real.rpow_add hΔ_pos (-2 * ε) (-ε / 4)).symm
      rw [h9]
      have h10 : (-2 * ε) + (-ε / 4) = -9 * ε / 4 := by ring
      rw [h10]
    calc (50 : ℝ) * Real.rpow δ_n (-ε)
      = (50 : ℝ) * Real.rpow Δ (-2 * ε) := by rw [h1]
    _ ≤ Real.rpow Δ (-ε / 4) * Real.rpow Δ (-2 * ε) := by
      gcongr
      <;> linarith
    _ = Real.rpow Δ (-9 * ε / 4) := by
      rw [mul_comm]
      exact h8

  have hP_ball_growth' : ∀ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ), Δ ≤ r →
      ((A.filter (fun y => dist c y ≤ r)).card : ℝ) ≤
        Real.rpow Δ (-9 * ε / 4) * r^u * (A.card : ℝ) := by
    intro c r hr
    have hδ_n_le_Δ : δ_n ≤ Δ := by
      rw [hδ_n_eq2]
      have h : Δ ^ 2 ≤ Δ := by nlinarith [hΔ_pos, hΔ_lt_one]
      exact h
    have hδ_n_le_r : δ_n ≤ r := by linarith
    have h1 : A.filter (fun y => dist c y ≤ r) ⊆ B.filter (fun y => dist c y ≤ r) := by
      intro x hx
      have h2 : x ∈ A := (Finset.mem_filter.mp hx).1
      exact Finset.mem_filter.mpr ⟨hA_sub_B h2, (Finset.mem_filter.mp hx).2⟩
    have h2 : ((A.filter (fun y => dist c y ≤ r)).card : ℝ) ≤
        ((B.filter (fun y => dist c y ≤ r)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card h1
    have h3 := hB_ball_growth_raw c r hδ_n_le_r
    have h5 : (B.card : ℝ) ≤ 2 * (A.card : ℝ) := h_card_ratio'
    calc ((A.filter (fun y => dist c y ≤ r)).card : ℝ)
      ≤ ((B.filter (fun y => dist c y ≤ r)).card : ℝ) := h2
    _ ≤ (25 : ℝ) * Real.rpow δ_n (-ε) * r^u * (B.card : ℝ) := h3
    _ ≤ (25 : ℝ) * Real.rpow δ_n (-ε) * r^u * (2 * (A.card : ℝ)) := by
      have hr_pos : 0 ≤ r := by linarith
      have h1 : 0 ≤ Real.rpow δ_n (-ε) := Real.rpow_nonneg hδ_n_pos.le _
      have h2 : 0 ≤ r^u := Real.rpow_nonneg hr_pos u
      have h_pos : 0 ≤ (25 : ℝ) * Real.rpow δ_n (-ε) * r^u := by
        apply mul_nonneg
        · apply mul_nonneg
          · norm_num
          · exact h1
        · exact h2
      exact mul_le_mul_of_nonneg_left h_card_ratio' h_pos
    _ = (50 : ℝ) * Real.rpow δ_n (-ε) * r^u * (A.card : ℝ) := by
      let x := Real.rpow δ_n (-ε)
      let y := r^u
      let z := (A.card : ℝ)
      have h_eq : (25 : ℝ) * x * y * (2 * z) = (50 : ℝ) * x * y * z := by
        simp only [mul_assoc]
        <;> ring
      exact h_eq
    _ ≤ Real.rpow Δ (-9 * ε / 4) * r^u * (A.card : ℝ) := by
      have h6 : 0 ≤ r^u := Real.rpow_nonneg (by linarith) u
      have h7 : 0 ≤ (A.card : ℝ) := by positivity
      gcongr <;> exact h_absorb_ball_50

  have h_points_in_ball_R' : (A : Set (EuclideanSpace ℝ (Fin 2))) ⊆
      Metric.closedBall 0 (1 + Real.sqrt 2 * δ_n / 2) := by
    have h1 : (A : Set (EuclideanSpace ℝ (Fin 2))) ⊆ (B : Set (EuclideanSpace ℝ (Fin 2))) :=
      hA_sub_B
    exact Set.Subset.trans h1 h_points_in_ball_R

  -- Step 8: Construct B1BridgeDecomposition
  have hCoarse_eq : coarseP₀' = config'.P₀.image csq := by
    have h1 : coarseP₀ P₀' csq = P₀'.image csq := by rfl
    have h2 : coarseP₀' = coarseP₀ P₀' csq := h_coarseP'_eq.symm
    rw [h2, h1]
    <;> rfl

  have hContaining : ∀ p ∈ config'.P₀, csq p ∈ coarseP₀' := by
    intro p hp
    have h_in_P0' : p ∈ P₀' := by
      have h_eq : config'.P₀ = P₀' := by rfl
      rw [←h_eq] <;> exact hp
    have h6 : csq p ∈ Qheavy config.P₀ csq m_threshold :=
      (Finset.mem_filter.mp h_in_P0').2
    simpa [coarseP₀'] using h6

  have h_tubes_intercept' : ∀ (p : DSquare n) (hp : p ∈ config'.P₀) (T : DTube n),
      T ∈ config'.tubeFamily p hp → |T.intercept| ≤ 3 := by
    intro p hp T hT
    have h_orig : T ∈ config.tubeFamily p (hP'_subset hp) := hT
    exact h_tubes_intercept p (hP'_subset hp) T h_orig

  have b1 : B1BridgeDecomposition n m hnm s C₁ M config' Δ δ_n u ε :=
    b1_induction_application
      hnm config'
      hΔ_eq hδ_n_eq
      h_points_in_ball_R'
      h_tubes_strip h_tubes_bounded hM_even
      hP_ball_growth' hPfin_sset'
      h_fine_card_lower' h_fine_card_upper'
      hC_fine_bound hC₁ h_tube_sset_absorb
      hM_fine_lower hM_fine_upper
      K_pack hK_pack_pos hK_pack_bound
      coarseP₀' csq
      hCoarse_eq
      hContaining
      rfl
      h_coarse_card_lower' h_coarse_card_upper'
      h_per_square_lower' h_per_square_upper'
      h_tubes_intercept'
  exact ⟨config', b1, hP'_subset, rfl⟩

end DirecretisedFurstenbergEstimate.FrontEndLemmas.B1Assembly

end
