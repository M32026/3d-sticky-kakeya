import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.Hairbrush.ExpandedAssemblyAlgebra
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound
import MyLeanRepo.Kakeya.Assouad.Targets.HairbrushStableParentCardBound

/-!
# Self-contained global Appendix-B assembly

This target assembles (B.30)--(B.42) around the canonical local Lemma B.3 and
exports `HairbrushExpandedEstimate`.  It is a conditional composition theorem
and does not reprove any local or geometric leaf.
-/

noncomputable section

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- Convert per-tube density to aggregate density. -/
private lemma per_tube_to_aggregate_dense
    {δ : ℝ} {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}
    {density : ENNReal}
    (h : HairbrushPerTubeDense Y density) :
    HairbrushAggregateDense Y density := by
  have h_vol_eq : ∀ (T : Kakeya.DeltaTube δ), T.volume = Kakeya.deltaTubeVolume δ :=
    tube_volume_scaling.1 δ
  have h1 : ∑ T ∈ F, density * T.volume ≤ ∑ T ∈ F, volume (Y.carrier T) := by
    apply Finset.sum_le_sum
    intro T hT
    exact h T hT
  have h2 : ∑ T ∈ F, density * T.volume = density * F.enncard * Kakeya.deltaTubeVolume δ := by
    have h3 : ∑ T ∈ F, density * T.volume = density * ∑ T ∈ F, T.volume := by
      rw [Finset.mul_sum]
    rw [h3]
    have h4 : ∑ T ∈ F, T.volume = F.enncard * Kakeya.deltaTubeVolume δ := by
      have h5 : ∀ T ∈ F, T.volume = Kakeya.deltaTubeVolume δ := fun T _ => h_vol_eq T
      have h6 : ∑ T ∈ F, T.volume = ∑ T ∈ F, Kakeya.deltaTubeVolume δ := by
        apply Finset.sum_congr rfl
        intro T hT
        exact h5 T hT
      rw [h6]
      simp [Kakeya.TubeFamily.enncard, Finset.sum_const]
      <;> ring
    rw [h4] <;> ring
  have h_main : density * F.enncard * Kakeya.deltaTubeVolume δ ≤ Y.mass := by
    calc
      density * F.enncard * Kakeya.deltaTubeVolume δ
        = ∑ T ∈ F, density * T.volume := h2.symm
      _ ≤ ∑ T ∈ F, volume (Y.carrier T) := h1
      _ = Y.mass := by rfl
  exact h_main

/-- Transfer cardinality retention through square roots. -/
private lemma card_retention_sqrt_transfer
    {δ a : ℝ} {F G : Kakeya.TubeFamily δ}
    (hδ : 0 < δ)
    (h : Kakeya.realRpowENN δ a * F.enncard ≤ G.enncard) :
    Kakeya.realRpowENN δ (a / 2) * ENNReal.rpow F.enncard (1 / 2 : ℝ) ≤
      ENNReal.rpow G.enncard (1 / 2 : ℝ) := by
  have h1 : ENNReal.rpow (Kakeya.realRpowENN δ a * F.enncard) (1 / 2 : ℝ) ≤
      ENNReal.rpow G.enncard (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow h (by norm_num)
  have h2 : ENNReal.rpow (Kakeya.realRpowENN δ a * F.enncard) (1 / 2 : ℝ) =
      ENNReal.rpow (Kakeya.realRpowENN δ a) (1 / 2 : ℝ) *
      ENNReal.rpow F.enncard (1 / 2 : ℝ) :=
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  have h3 : ENNReal.rpow (Kakeya.realRpowENN δ a) (1 / 2 : ℝ) =
      Kakeya.realRpowENN δ (a / 2) := by
    rw [hairbrush_realRpowENN_rpow hδ a (1 / 2 : ℝ)]
    <;> ring_nf
  rw [h2, h3] at h1
  exact h1

/-- Polynomial cardinality upper bound from KT + unit ball. -/
private lemma expanded_card_bound {δ : ℝ} {F : Kakeya.TubeFamily δ}
    (hδ : 0 < δ)
    (hδ_small : δ ≤ 3 / (4 * Real.pi))
    {eta : ℝ} (_heta : 0 < eta)
    (hF_ball : F.IsInUnitBall)
    (hKT : Kakeya.KatzTaoConvexWolffBound F (Real.rpow δ (-eta))) :
    F.enncard ≤ Kakeya.realRpowENN δ (-(eta + 3)) := by
  have hC_nonneg : 0 ≤ Real.rpow δ (-eta) := Real.rpow_nonneg hδ.le _
  have h_card : (F.card : ℝ) ≤
      (4 * Real.pi / 3) * Real.rpow δ (-eta) * δ ^ (-2 : ℝ) :=
    katz_tao_card_bound hδ hF_ball hC_nonneg hKT
  have h_const : (4 * Real.pi / 3) ≤ 1 / δ := by
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have h : (4 * Real.pi / 3) * δ ≤ 1 := by
      calc
        (4 * Real.pi / 3) * δ
          ≤ (4 * Real.pi / 3) * (3 / (4 * Real.pi)) := by gcongr
        _ = 1 := by field_simp [hpi_pos.ne']
    have hδ' : 0 < δ := hδ
    calc
      (4 * Real.pi / 3)
        = ((4 * Real.pi / 3) * δ) / δ := by field_simp [hδ'.ne'] <;> ring
      _ ≤ 1 / δ := by gcongr
  have h_exp1 : (-eta : ℝ) + (-2 : ℝ) = -(eta + 2) := by ring
  have h_rpow1 : Real.rpow δ (-eta) * δ ^ (-2 : ℝ) = δ ^ (-(eta + 2)) := by
    have h1 : Real.rpow δ (-eta) = δ ^ (-eta : ℝ) := by rfl
    rw [h1]
    have h2 : δ ^ (-eta : ℝ) * δ ^ (-2 : ℝ) = δ ^ ((-eta : ℝ) + (-2 : ℝ)) :=
      (Real.rpow_add hδ (-eta) (-2)).symm
    rw [h2, h_exp1]
  have h_exp2 : (-1 : ℝ) + (-(eta + 2)) = -(eta + 3) := by ring
  have h_main : (4 * Real.pi / 3) * Real.rpow δ (-eta) * δ ^ (-2 : ℝ) ≤
      δ ^ (-(eta + 3)) := by
    calc
      (4 * Real.pi / 3) * Real.rpow δ (-eta) * δ ^ (-2 : ℝ)
        = (4 * Real.pi / 3) * (Real.rpow δ (-eta) * δ ^ (-2 : ℝ)) := by ring
      _ = (4 * Real.pi / 3) * δ ^ (-(eta + 2)) := by rw [h_rpow1]
      _ ≤ (1 / δ) * δ ^ (-(eta + 2)) := by gcongr
      _ = δ ^ (-1 : ℝ) * δ ^ (-(eta + 2)) := by
        have h2 : (1 / δ : ℝ) = δ ^ (-1 : ℝ) := by
          rw [Real.rpow_neg hδ.le]; simp
        rw [h2]
      _ = δ ^ ((-1 : ℝ) + (-(eta + 2))) := by
        rw [← Real.rpow_add hδ (-1) (-(eta + 2))]
      _ = δ ^ (-(eta + 3)) := by rw [h_exp2]
  have h_card2 : (F.card : ℝ) ≤ δ ^ (-(eta + 3)) := h_card.trans h_main
  have hF_card : F.enncard = ENNReal.ofReal (F.card : ℝ) := by
    simp [Kakeya.TubeFamily.enncard]
  have h_nonneg : 0 ≤ δ ^ (-(eta + 3)) := by positivity
  rw [hF_card, Kakeya.realRpowENN]
  exact ENNReal.ofReal_le_ofReal_iff h_nonneg |>.mpr h_card2

/-- Push aggregate density through a mass-retention step. -/
private lemma angular_mass_transfer_aggregate
    {δ : ℝ} {F : Kakeya.TubeFamily δ}
    {Y Z : Kakeya.Shading F} {density : ENNReal} {stopLoss : ℝ}
    (h_mass_retention : Kakeya.realRpowENN δ stopLoss * Y.mass ≤ Z.mass)
    (h_agg : HairbrushAggregateDense Y density) :
    HairbrushAggregateDense Z (density * Kakeya.realRpowENN δ stopLoss) := by
  have h1 : density * F.enncard * Kakeya.deltaTubeVolume δ ≤ Y.mass := h_agg
  have h2 : Kakeya.realRpowENN δ stopLoss *
      (density * F.enncard * Kakeya.deltaTubeVolume δ) ≤
      Kakeya.realRpowENN δ stopLoss * Y.mass := by
    gcongr
  have h3 : Kakeya.realRpowENN δ stopLoss *
      (density * F.enncard * Kakeya.deltaTubeVolume δ) =
      (density * Kakeya.realRpowENN δ stopLoss) * F.enncard *
        Kakeya.deltaTubeVolume δ := by
    simp [mul_assoc, mul_comm, mul_left_comm]
  rw [h3] at h2
  exact le_trans h2 h_mass_retention

theorem hairbrush_self_contained_expanded_assembly :
    HairbrushSelfContainedExpandedAssemblyStatement := by
  intro hPrep hAngular hCoarseGrouping hCard hBalancing hFrostman hSummation hFiber
  intro epsilon hepsilon

  set localLoss : ℝ := epsilon / 10 with hlocalLoss_def
  have hlocalLoss_pos : 0 < localLoss := by positivity

  -- Fiber estimate gives eta and delta₀_fiber
  rcases hFiber localLoss hlocalLoss_pos with
    ⟨eta, delta₀_fiber, heta_pos, heta_le, hdelta₀_fiber_pos, hdelta₀_fiber_le, hFiberMain⟩

  have heta_le_localLoss : eta ≤ localLoss / 100 :=
    le_trans heta_le (min_le_left _ _)
  have heta_le_one_hundredth : eta ≤ 1 / 100 :=
    le_trans heta_le (min_le_right _ _)

  set stopLoss : ℝ := 2 * eta with hstopLoss_def
  set prepEta : ℝ := eta with hprepEta_def
  set inputExponent : ℝ := 3 * eta with hinputExponent_def
  set densityFloor : ℝ := 4 * eta with hdensityFloor_def
  set balanceLoss : ℝ := eta / 10 with hbalanceLoss_def
  set frostmanExponent : ℝ := eta with hfrostmanExponent_def
  set cardExponent : ℝ := eta + 3 with hcardExponent_def
  set totalLoss : ℝ := 5 * eta with htotalLoss_def
  set coarseLoss : ℝ := 7 * eta with hcoarseLoss_def
  set outputLoss : ℝ := 27 * localLoss / 25 with houtputLoss_def

  -- Parameter inequalities
  have h_eta_lt_stop : eta < stopLoss := by
    simp [hstopLoss_def] <;> linarith
  have h_input_pos : 0 < inputExponent := by
    simp [hinputExponent_def] <;> linarith
  have h_input_lt_floor : inputExponent < densityFloor := by
    simp [hinputExponent_def, hdensityFloor_def] <;> linarith
  have h_cardExponent_pos : 0 < cardExponent := by
    simp [hcardExponent_def] <;> linarith
  have h_balanceLoss_pos : 0 < balanceLoss := by
    simp [hbalanceLoss_def] <;> linarith
  have h_frostmanExponent_nonneg : 0 ≤ frostmanExponent := by
    simp [hfrostmanExponent_def] <;> linarith
  have h_input_balance_lt_total : inputExponent + balanceLoss < totalLoss := by
    simp [hinputExponent_def, hbalanceLoss_def, htotalLoss_def] <;> linarith
  have h_total_frostman_lt_coarse : totalLoss + frostmanExponent < coarseLoss := by
    simp [htotalLoss_def, hfrostmanExponent_def, hcoarseLoss_def] <;> linarith
  have h_summation_ineq : localLoss + (totalLoss + coarseLoss) / 2 < outputLoss := by
    have h1 : (totalLoss + coarseLoss) / 2 = 6 * eta := by
      simp [htotalLoss_def, hcoarseLoss_def] <;> ring
    rw [h1]
    have h21 : eta ≤ localLoss / 100 := heta_le_localLoss
    have h2 : 6 * eta ≤ 6 * (localLoss / 100) := by
      exact mul_le_mul_of_nonneg_left h21 (by norm_num)
    have h3 : 6 * (localLoss / 100) = (6 * localLoss) / 100 := by ring
    rw [h3] at h2
    linarith [hlocalLoss_def, houtputLoss_def]
  have h_output_epsilon : outputLoss + prepEta / 2 < epsilon := by
    have h1 : prepEta / 2 ≤ localLoss / 200 := by
      simp [hprepEta_def] <;> linarith [heta_le_localLoss]
    linarith [hlocalLoss_def, houtputLoss_def]
  have h_outputLoss_pos : 0 < outputLoss := by
    simp [houtputLoss_def] <;> positivity

  -- Apply leaves to get delta₀ values
  rcases hPrep prepEta (by positivity) with
    ⟨inputEta, delta₀_prep, hinputEta_pos, hdelta₀_prep_pos, hdelta₀_prep_one, hPrepMain⟩
  rcases hAngular eta stopLoss heta_pos h_eta_lt_stop with
    ⟨delta₀_angular, hdelta₀_angular_pos, hdelta₀_angular_one, hAngularMain⟩
  rcases hBalancing inputExponent densityFloor cardExponent balanceLoss
      h_input_pos h_input_lt_floor h_cardExponent_pos h_balanceLoss_pos with
    ⟨delta₀_balancing, hdelta₀_balancing_pos, hdelta₀_balancing_le, hBalancingMain⟩
  rcases hFrostman inputExponent balanceLoss frostmanExponent totalLoss coarseLoss
      h_input_pos h_balanceLoss_pos h_frostmanExponent_nonneg
      h_input_balance_lt_total h_total_frostman_lt_coarse with
    ⟨delta₀_frostman, hdelta₀_frostman_pos, hdelta₀_frostman_le, hFrostmanMain⟩
  rcases hSummation localLoss totalLoss coarseLoss outputLoss
      hlocalLoss_pos h_summation_ineq with
    ⟨delta₀_summation, hdelta₀_summation_pos, hdelta₀_summation_le, hSummationMain⟩

  set delta₀ : ℝ := min delta₀_fiber
      (min delta₀_prep
        (min delta₀_angular
          (min delta₀_balancing
            (min delta₀_frostman
              (min delta₀_summation (1 / 8)))))) with hdelta₀_def

  have hdelta₀_pos : 0 < delta₀ := by
    dsimp only [delta₀]
    apply lt_min hdelta₀_fiber_pos
    apply lt_min hdelta₀_prep_pos
    apply lt_min hdelta₀_angular_pos
    apply lt_min hdelta₀_balancing_pos
    apply lt_min hdelta₀_frostman_pos
    apply lt_min hdelta₀_summation_pos
    norm_num
  have hdelta₀_one : delta₀ ≤ 1 := by
    dsimp only [delta₀]
    have h : delta₀ ≤ delta₀_fiber := min_le_left _ _
    exact le_trans h (le_trans hdelta₀_fiber_le (by norm_num))

  refine ⟨1, inputEta, delta₀, by norm_num, hinputEta_pos, hdelta₀_pos, hdelta₀_one, ?_⟩

  intro δ hδ hδle₀ F hF_ball hF_ed Y hY_dense hKT hFrostman

  have hδle_fiber : δ ≤ delta₀_fiber := by
    simp [hdelta₀_def] at hδle₀ <;> linarith
  have hδle_prep : δ ≤ delta₀_prep := by
    simp [hdelta₀_def] at hδle₀ <;> linarith
  have hδle_angular : δ ≤ delta₀_angular := by
    simp [hdelta₀_def] at hδle₀ <;> linarith
  have hδle_balancing : δ ≤ delta₀_balancing := by
    simp [hdelta₀_def] at hδle₀ <;> linarith
  have hδle_frostman : δ ≤ delta₀_frostman := by
    simp [hdelta₀_def] at hδle₀ <;> linarith
  have hδle_summation : δ ≤ delta₀_summation := by
    simp [hdelta₀_def] at hδle₀ <;> linarith
  have hδ_le_eighth : δ ≤ 1 / 8 := by
    simp [hdelta₀_def] at hδle₀ <;> linarith
  have hδ_lt_one : δ < 1 := by linarith
  have hδ_le_one : δ ≤ 1 := by linarith

  by_cases hF_empty : F = ∅
  · simp [hF_empty, Kakeya.TubeFamily.enncard] <;> simp

  have hF_nonempty : F.Nonempty := by
    simpa [Finset.nonempty_iff_ne_empty] using hF_empty

  -- Step 1: Preprocessing
  rcases hPrepMain δ hδ hδle_prep F hF_nonempty hF_ball hF_ed Y hY_dense hKT hFrostman with ⟨P⟩

  -- Step 2: Per-tube to aggregate density
  have h_agg_P : HairbrushAggregateDense P.shading (Kakeya.realRpowENN δ prepEta) :=
    per_tube_to_aggregate_dense P.per_tube_dense

  -- Step 3: Cardinality upper bound via KT + unit ball
  have h_eighth_le : (1 : ℝ) / 8 ≤ 3 / (4 * Real.pi) := by
    have h_pos : 0 < 4 * Real.pi := by positivity
    have h : 4 * Real.pi ≤ 24 := by linarith [Real.pi_lt_four]
    calc (1 : ℝ) / 8
        = (4 * Real.pi) / (8 * (4 * Real.pi)) := by field_simp [h_pos.ne'] <;> ring
      _ ≤ 24 / (8 * (4 * Real.pi)) := by
        apply div_le_div_of_nonneg_right
        <;> linarith <;> positivity
      _ = 3 / (4 * Real.pi) := by field_simp [h_pos.ne'] <;> ring
  have hδ_le_3over4pi : δ ≤ 3 / (4 * Real.pi) := by
    calc δ ≤ 1 / 8 := hδ_le_eighth
         _ ≤ 3 / (4 * Real.pi) := h_eighth_le
  have h_card_bound : P.family.enncard ≤ Kakeya.realRpowENN δ (-cardExponent) :=
    expanded_card_bound (eta := prepEta) hδ hδ_le_3over4pi heta_pos P.in_unit_ball P.katz_tao

  -- Step 4: Angular stopping
  rcases hAngularMain δ hδ hδle_angular P.family P.shading with ⟨angular⟩

  -- Transfer aggregate density through angular stopping
  have h_agg_angular : HairbrushAggregateDense angular.shading
      (Kakeya.realRpowENN δ inputExponent) := by
    have h1 : Kakeya.realRpowENN δ inputExponent =
        Kakeya.realRpowENN δ prepEta * Kakeya.realRpowENN δ stopLoss := by
      have h2 : inputExponent = prepEta + stopLoss := by
        simp [hinputExponent_def, hprepEta_def, hstopLoss_def] <;> ring
      rw [h2]
      exact (hairbrush_realRpowENN_mul hδ).symm
    rw [h1]
    exact angular_mass_transfer_aggregate angular.mass_retention h_agg_P

  -- Mass non-zero for coarse grouping
  have h_mass_ne_zero : angular.shading.mass ≠ 0 := by
    have hP_nonempty : P.family.Nonempty := P.nonempty
    have h_vol_pos : 0 < Kakeya.deltaTubeVolume δ :=
      (tube_volume_scaling.2.1 δ hδ hδ_le_one).1
    have h_density_pos : 0 < Kakeya.realRpowENN δ prepEta := by
      simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hδ] <;> positivity
    have h61 : 0 < P.family.card := Finset.card_pos.mpr hP_nonempty
    have h62 : P.family.card ≠ 0 := by linarith
    have h_card_ne : P.family.enncard ≠ 0 := by
      simpa [Kakeya.TubeFamily.enncard] using h62
    have h_density_ne : (Kakeya.realRpowENN δ prepEta) ≠ 0 := by
      simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hδ]
    have h_mul1_ne : (Kakeya.realRpowENN δ prepEta * P.family.enncard) ≠ 0 :=
      mul_ne_zero h_density_ne h_card_ne
    have h5 : 0 < Kakeya.realRpowENN δ prepEta * P.family.enncard * Kakeya.deltaTubeVolume δ :=
      ENNReal.mul_pos h_mul1_ne h_vol_pos.ne'
    have h7 : 0 < P.shading.mass := by
      have h8 : _ ≤ P.shading.mass := h_agg_P
      exact lt_of_lt_of_le h5 h8
    have h9 : 0 < Kakeya.realRpowENN δ stopLoss := by
      simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hδ] <;> positivity
    have h10 : 0 < Kakeya.realRpowENN δ stopLoss * P.shading.mass := ENNReal.mul_pos (ne_of_gt h9) (ne_of_gt h7)
    have h11 : _ ≤ angular.shading.mass := angular.mass_retention
    exact ne_of_gt (lt_of_lt_of_le h10 h11)

  -- Step 5: Coarse grouping
  rcases hCoarseGrouping δ eta stopLoss hδ P.family P.shading P.in_unit_ball
      angular h_mass_ne_zero with ⟨coarse⟩
  let grouping := coarse.grouping

  -- Step 6: Balancing
  rcases hBalancingMain δ hδ hδle_balancing eta stopLoss P.family P.shading
      P.nonempty h_card_bound angular h_agg_angular grouping with ⟨balanced⟩

  -- Step 7: Frostman count
  rcases hFrostmanMain δ hδ hδle_frostman eta stopLoss densityFloor P.family P.shading
      P.nonempty P.frostman_slab angular h_agg_angular grouping balanced with ⟨counts⟩

  -- Step 8: Per-group local fiber estimate
  have h_per_group : ∀ (j : Fin balanced.selectedCount),
      HairbrushFiberTarget (theta := angular.theta) (loss := localLoss)
        (grouping.shading (balanced.select j)) := by
    intro j
    let G := grouping.family (balanced.select j)
    let Z := grouping.shading (balanced.select j)
    have hG_sub : G ⊆ P.family := grouping.family_subset (balanced.select j)
    have hG_nonempty : G.Nonempty := grouping.family_nonempty (balanced.select j)
    have hG_ball : G.IsInUnitBall := by
      intro T hT; exact P.in_unit_ball (hG_sub hT)
    have hG_ed : G.IsEssentiallyDistinct := by
      intro T hT U hU hne
      exact P.essentially_distinct (hG_sub hT) (hG_sub hU) hne
    have hG_angle_sep : HairbrushAngleSeparated G := by
      intro T hT U hU hne h_inter
      exact P.angle_separated T (hG_sub hT) U (hG_sub hU) hne h_inter
    have hG_confined : HairbrushAngularlyConfined G angular.capRadius :=
      grouping.angular_confinement (balanced.select j)
    have hG_two_broad : IsTwoBroadAtScale Z angular.theta eta :=
      grouping.two_broad (balanced.select j)
    have hG_kt : Kakeya.KatzTaoConvexWolffBound G (Real.rpow δ (-eta)) := by
      intro W hW
      have h1 : G.containedCount W ≤ P.family.containedCount W := by
        dsimp only [Kakeya.TubeFamily.containedCount]
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hG_sub)
      exact h1.trans (P.katz_tao W hW)
    have hG_card : G.enncard ≤
        ENNReal.ofReal 100000000 * Kakeya.realRpowENN δ (-eta) *
        ENNReal.ofReal ((angular.theta / δ) ^ 2) := by
      have h_eta_nonneg : 0 ≤ Real.rpow δ (-eta) := Real.rpow_nonneg hδ.le _
      have h_main := hCard δ eta stopLoss (Real.rpow δ (-eta)) hδ h_eta_nonneg
        P.family P.shading P.katz_tao angular coarse (canonical_volume_lower hδ)
      exact h_main (balanced.select j)
    have hG_dense : HairbrushAggregateDense Z (Kakeya.realRpowENN δ (4 * eta)) := by
      have h1 : Kakeya.realRpowENN δ densityFloor ≤ balanced.typicalDensity :=
        balanced.density_floor
      have h1' : Kakeya.realRpowENN δ (4 * eta) ≤ balanced.typicalDensity := by
        simpa [hdensityFloor_def] using h1
      have h3 : balanced.typicalDensity * G.enncard * Kakeya.deltaTubeVolume δ ≤ Z.mass :=
        balanced.density_lower j
      calc
        Kakeya.realRpowENN δ (4 * eta) * G.enncard * Kakeya.deltaTubeVolume δ
          ≤ balanced.typicalDensity * G.enncard * Kakeya.deltaTubeVolume δ := by gcongr
        _ ≤ Z.mass := h3
    exact hFiberMain δ angular.theta angular.capRadius hδ hδle_fiber
      angular.delta_le_theta angular.theta_le_capRadius
      angular.capRadius_le_six_theta angular.capRadius_le_one
      G hG_nonempty hG_ball hG_ed hG_angle_sep hG_confined
      Z hG_dense hG_kt hG_card hG_two_broad

  -- Step 9: Summation
  have h_sum : HairbrushFiberTarget (theta := 1) (loss := outputLoss) angular.shading :=
    hSummationMain δ hδ hδle_summation eta stopLoss densityFloor balanceLoss frostmanExponent
      P.family P.shading P.nonempty angular grouping balanced counts h_per_group

  -- Step 10: Transfer to original family
  have h_sum' : Kakeya.realRpowENN δ (3 / 2 + outputLoss) *
      ENNReal.rpow P.family.enncard (1 / 2 : ℝ) ≤ volume angular.shading.union := by
    simpa [HairbrushFiberTarget, Real.sqrt_one] using h_sum

  have h_card_sqrt : Kakeya.realRpowENN δ (prepEta / 2) *
      ENNReal.rpow F.enncard (1 / 2 : ℝ) ≤
      ENNReal.rpow P.family.enncard (1 / 2 : ℝ) :=
    card_retention_sqrt_transfer hδ P.card_retention

  have h_main : Kakeya.realRpowENN δ (3 / 2 + outputLoss + prepEta / 2) *
      ENNReal.rpow F.enncard (1 / 2 : ℝ) ≤ volume angular.shading.union := by
    have h_exp_mul : Kakeya.realRpowENN δ (3 / 2 + outputLoss + prepEta / 2) =
        Kakeya.realRpowENN δ (3 / 2 + outputLoss) * Kakeya.realRpowENN δ (prepEta / 2) :=
      (hairbrush_realRpowENN_mul hδ).symm
    calc
      Kakeya.realRpowENN δ (3 / 2 + outputLoss + prepEta / 2) *
          ENNReal.rpow F.enncard (1 / 2 : ℝ)
        = (Kakeya.realRpowENN δ (3 / 2 + outputLoss) * Kakeya.realRpowENN δ (prepEta / 2)) *
            ENNReal.rpow F.enncard (1 / 2 : ℝ) := by rw [h_exp_mul]
      _ = Kakeya.realRpowENN δ (3 / 2 + outputLoss) *
            (Kakeya.realRpowENN δ (prepEta / 2) * ENNReal.rpow F.enncard (1 / 2 : ℝ)) := by ring
      _ ≤ Kakeya.realRpowENN δ (3 / 2 + outputLoss) *
            ENNReal.rpow P.family.enncard (1 / 2 : ℝ) := by gcongr
      _ ≤ volume angular.shading.union := h_sum'

  have h_union1 : angular.shading.union ⊆ P.shading.union := by
    intro x hx
    rcases hx with ⟨T, hT, hxT⟩
    refine ⟨T, hT, ?_⟩
    exact angular.shading_subset T hT hxT

  have h_volume_transfer : volume angular.shading.union ≤ volume Y.union :=
    measure_mono (h_union1.trans P.union_subset)

  have h_exp_le : 3 / 2 + outputLoss + prepEta / 2 ≤ 3 / 2 + epsilon := by
    linarith [h_output_epsilon]

  have h_rpow_le : Kakeya.realRpowENN δ (3 / 2 + epsilon) ≤
      Kakeya.realRpowENN δ (3 / 2 + outputLoss + prepEta / 2) :=
    hairbrush_rpow_antitone hδ hδ_le_one h_exp_le

  have h_final : Kakeya.realRpowENN δ (3 / 2 + epsilon) *
      ENNReal.rpow F.enncard (1 / 2 : ℝ) ≤ volume Y.union := by
    calc
      Kakeya.realRpowENN δ (3 / 2 + epsilon) * ENNReal.rpow F.enncard (1 / 2 : ℝ)
        ≤ Kakeya.realRpowENN δ (3 / 2 + outputLoss + prepEta / 2) *
            ENNReal.rpow F.enncard (1 / 2 : ℝ) := by gcongr
      _ ≤ volume angular.shading.union := h_main
      _ ≤ volume Y.union := h_volume_transfer

  simpa using h_final

end Kakeya.Assouad
