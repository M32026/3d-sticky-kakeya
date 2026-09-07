import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.Hairbrush.ExpandedAssemblyAlgebra

/-!
# Sum balanced local hairbrush estimates

This is the square-root summation in (B.39)--(B.42).

Sum the local fiber estimates using disjoint group unions, then use the
selected total-cardinality and Frostman coarse-count lower bounds to cancel
the group count and the common angular scale.

This target is pure ENNReal/rpow assembly.
-/

open MeasureTheory

namespace Kakeya.Assouad

theorem hairbrush_balanced_group_summation :
    HairbrushBalancedGroupSummationStatement := by
  intro localLoss totalLoss coarseLoss outputLoss _ hGap
  use 1 / 1000
  constructor
  · norm_num
  constructor
  · norm_num
  intro δ hδ hδ₀ eta stopLoss densityFloor balanceLoss frostmanExponent F Y _ angular grouping balanced counts hFibers

  set q : ENNReal := (balanced.selectedCount : ENNReal) with hq_def
  set M : ENNReal := (balanced.typicalCard : ENNReal) with hM_def
  set theta_enn : ENNReal := ENNReal.ofReal angular.theta with htheta_def
  set deltaTotal : ENNReal := Kakeya.realRpowENN δ totalLoss with hdeltaTotal_def
  set deltaCoarse : ENNReal := Kakeya.realRpowENN δ coarseLoss with hdeltaCoarse_def
  set deltaLocal : ENNReal := Kakeya.realRpowENN δ (3 / 2 + localLoss) with hdeltaLocal_def

  have htheta_pos : 0 < angular.theta := by linarith [angular.delta_le_theta]
  have htheta_nonneg : 0 ≤ angular.theta := by linarith
  have hq0 : q ≠ 0 := by
    simp [hq_def, balanced.selectedCount_pos.ne'] <;> omega
  have hq_top : q ≠ ⊤ := ENNReal.natCast_ne_top balanced.selectedCount
  have hM0 : M ≠ 0 := by
    simp [hM_def, balanced.typicalCard_pos.ne'] <;> omega
  have hM_top : M ≠ ⊤ := ENNReal.natCast_ne_top balanced.typicalCard
  have htheta0 : theta_enn ≠ 0 := by
    simp [htheta_def, htheta_pos.ne'] <;> linarith
  have htheta_top : theta_enn ≠ ⊤ := by
    simp [htheta_def] <;> exact ENNReal.ofReal_ne_top
  have hdt0 : deltaTotal ≠ 0 := by
    rw [hdeltaTotal_def, Kakeya.realRpowENN]
    simp [Real.rpow_pos_of_pos hδ]
  have hdt_top : deltaTotal ≠ ⊤ := by
    rw [hdeltaTotal_def, Kakeya.realRpowENN] <;> exact ENNReal.ofReal_ne_top
  have hdc0 : deltaCoarse ≠ 0 := by
    rw [hdeltaCoarse_def, Kakeya.realRpowENN]
    simp [Real.rpow_pos_of_pos hδ]
  have hdc_top : deltaCoarse ≠ ⊤ := by
    rw [hdeltaCoarse_def, Kakeya.realRpowENN]
    exact ENNReal.ofReal_ne_top

  let A : Fin balanced.selectedCount → Set Point3 :=
    fun j => (grouping.shading (balanced.select j)).union
  let card : Fin balanced.selectedCount → ENNReal :=
    fun j => (grouping.family (balanced.select j)).enncard

  -- Step 1: Rewrite each fiber target using ENNReal square root
  have h1 : ∀ j : Fin balanced.selectedCount,
      deltaLocal * theta_enn ^ (1 / 2 : ℝ) * (card j) ^ (1 / 2 : ℝ) ≤
        volume (A j) := by
    intro j
    have hfj := hFibers j
    simp only [HairbrushFiberTarget] at hfj
    have hsqrt : ENNReal.ofReal (Real.sqrt angular.theta) = theta_enn ^ (1 / 2 : ℝ) :=
      hairbrush_ofReal_sqrt htheta_nonneg
    rw [hsqrt] at hfj
    exact hfj

  -- Step 2: Sum the fiber lower bounds
  have h_sum_const : ∑ j : Fin balanced.selectedCount,
        deltaLocal * theta_enn ^ (1 / 2 : ℝ) * (card j) ^ (1 / 2 : ℝ) =
      deltaLocal * theta_enn ^ (1 / 2 : ℝ) * ∑ j, (card j) ^ (1 / 2 : ℝ) := by
    have h2 : ∑ j, deltaLocal * theta_enn ^ (1 / 2 : ℝ) * (card j) ^ (1 / 2 : ℝ) =
        ∑ j, (deltaLocal * theta_enn ^ (1 / 2 : ℝ)) * (card j) ^ (1 / 2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j _
      simp [mul_assoc]
    rw [h2, Finset.mul_sum]

  have h_sum_fibers :
      deltaLocal * theta_enn ^ (1 / 2 : ℝ) * ∑ j, (card j) ^ (1 / 2 : ℝ) ≤
        ∑ j, volume (A j) := by
    rw [←h_sum_const]
    apply Finset.sum_le_sum
    intro j _
    exact h1 j

  -- Step 3: Disjoint union volume bound
  have h_disj : ∀ (j k : Fin balanced.selectedCount), j ≠ k → Disjoint (A j) (A k) := by
    intro j k hjk
    have hsel : balanced.select j ≠ balanced.select k :=
      balanced.select_injective.ne hjk
    exact grouping.union_disjoint (balanced.select j) (balanced.select k) hsel

  have h_sub : ∀ j, A j ⊆ angular.shading.union := by
    intro j
    have h : A j ⊆ (⋃ k : Fin grouping.groupCount, (grouping.shading k).union) := by
      intro x hx
      simpa [A, Set.mem_iUnion] using ⟨balanced.select j, hx⟩
    have h' : (⋃ k : Fin grouping.groupCount, (grouping.shading k).union) = angular.shading.union :=
      grouping.union_exact
    rw [h'] at h
    exact h

  have h_meas : ∀ j, MeasurableSet (A j) := by
    intro j
    have h : A j = ⋃ T ∈ grouping.family (balanced.select j),
        (grouping.shading (balanced.select j)).carrier T := by
      ext x
      simp [A, Kakeya.Shading.union, Set.mem_iUnion]
      <;> tauto
    rw [h]
    exact Finset.measurableSet_biUnion _
      fun T _ => (grouping.shading (balanced.select j)).measurable_carrier ‹_›

  have h_volume_sum : ∑ j, volume (A j) ≤ volume angular.shading.union := by
    have h_union_sub : (⋃ j : Fin balanced.selectedCount, A j) ⊆ angular.shading.union := by
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨j, hxj⟩
      exact h_sub j hxj
    have h_iUnion_eq : (⋃ j : Fin balanced.selectedCount, A j) =
        ⋃ j ∈ (Finset.univ : Finset (Fin balanced.selectedCount)), A j := by
      ext x
      simp [Set.mem_iUnion]
    have h_sum_eq : volume (⋃ j : Fin balanced.selectedCount, A j) =
        ∑ j : Fin balanced.selectedCount, volume (A j) := by
      rw [h_iUnion_eq]
      exact MeasureTheory.measure_biUnion_finset
        (show Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin balanced.selectedCount))) A from
          fun j _ k _ hne => h_disj j k hne)
        (fun b _ => h_meas b)
    rw [←h_sum_eq]
    exact measure_mono h_union_sub

  -- Step 4: Lower bound sum of square roots by q * sqrt(M)
  have h_card_lower : ∀ j, M ≤ card j := by
    intro j
    have hnat : balanced.typicalCard ≤ (grouping.family (balanced.select j)).card :=
      balanced.card_lower j
    have h1 : (balanced.typicalCard : ENNReal) ≤ ((grouping.family (balanced.select j)).card : ENNReal) := by
      exact_mod_cast hnat
    have h2 : ((grouping.family (balanced.select j)).card : ENNReal) = (grouping.family (balanced.select j)).enncard := by
      rfl
    rw [h2] at h1
    exact h1

  have h_sqrt_lower : ∀ j, M ^ (1 / 2 : ℝ) ≤ (card j) ^ (1 / 2 : ℝ) := by
    intro j
    exact ENNReal.rpow_le_rpow (h_card_lower j) (by norm_num)

  have h_sum_lower : q * M ^ (1 / 2 : ℝ) ≤ ∑ j, (card j) ^ (1 / 2 : ℝ) := by
    have h : ∑ j : Fin balanced.selectedCount, M ^ (1 / 2 : ℝ) = q * M ^ (1 / 2 : ℝ) := by
      simp [hq_def, Finset.sum_const]
      <;> simp [mul_assoc]
    have h' : ∑ j : Fin balanced.selectedCount, M ^ (1 / 2 : ℝ) ≤ ∑ j, (card j) ^ (1 / 2 : ℝ) :=
      Finset.sum_le_sum fun j _ => h_sqrt_lower j
    rw [h] at h'
    exact h'

  -- Step 5: Core algebra — multiply the two lower bounds
  have h_total : deltaTotal * F.enncard ≤ q * M := counts.selected_cardinality_lower
  have h_coarse : deltaCoarse ≤ theta_enn * q := counts.coarse_count_lower

  have h_core : (deltaTotal * deltaCoarse) ^ (1 / 2 : ℝ) * F.enncard ^ (1 / 2 : ℝ) ≤
      theta_enn ^ (1 / 2 : ℝ) * q * M ^ (1 / 2 : ℝ) :=
    hairbrush_two_bound_sqrt_cancellation
      deltaTotal deltaCoarse theta_enn q M F.enncard
      h_coarse h_total
      htheta0 htheta_top hq0 hq_top hdt0 hdt_top hdc0 hdc_top

  have h_delta_mul : deltaTotal * deltaCoarse = Kakeya.realRpowENN δ (totalLoss + coarseLoss) := by
    rw [hdeltaTotal_def, hdeltaCoarse_def, hairbrush_realRpowENN_mul hδ]

  have h_delta_sqrt : (deltaTotal * deltaCoarse) ^ (1 / 2 : ℝ) =
      Kakeya.realRpowENN δ ((totalLoss + coarseLoss) / 2) := by
    calc
      (deltaTotal * deltaCoarse) ^ (1 / 2 : ℝ)
        = (Kakeya.realRpowENN δ (totalLoss + coarseLoss)) ^ (1 / 2 : ℝ) := by rw [h_delta_mul]
      _ = Kakeya.realRpowENN δ ((totalLoss + coarseLoss) * (1 / 2 : ℝ)) :=
          hairbrush_realRpowENN_rpow hδ (totalLoss + coarseLoss) (1 / 2 : ℝ)
      _ = Kakeya.realRpowENN δ ((totalLoss + coarseLoss) / 2) := by
          congr 1
          ring

  rw [h_delta_sqrt] at h_core

  -- Step 6: Combine all lower bounds
  have h6 : deltaLocal * theta_enn ^ (1 / 2 : ℝ) * (q * M ^ (1 / 2 : ℝ)) ≤
      volume angular.shading.union := by
    calc
      deltaLocal * theta_enn ^ (1 / 2 : ℝ) * (q * M ^ (1 / 2 : ℝ))
        ≤ deltaLocal * theta_enn ^ (1 / 2 : ℝ) * ∑ j, (card j) ^ (1 / 2 : ℝ) := by
          exact mul_le_mul_of_nonneg_left h_sum_lower (by positivity)
      _ ≤ ∑ j, volume (A j) := h_sum_fibers
      _ ≤ volume angular.shading.union := h_volume_sum

  have h_core' : Kakeya.realRpowENN δ ((totalLoss + coarseLoss) / 2) * F.enncard ^ (1 / 2 : ℝ) ≤
      theta_enn ^ (1 / 2 : ℝ) * q * M ^ (1 / 2 : ℝ) := h_core

  have h8 : deltaLocal * Kakeya.realRpowENN δ ((totalLoss + coarseLoss) / 2) =
      Kakeya.realRpowENN δ (3 / 2 + localLoss + (totalLoss + coarseLoss) / 2) := by
    rw [hdeltaLocal_def, hairbrush_realRpowENN_mul hδ]
    <;> ring

  have h9 : Kakeya.realRpowENN δ (3 / 2 + localLoss + (totalLoss + coarseLoss) / 2) * F.enncard ^ (1 / 2 : ℝ) ≤
      volume angular.shading.union := by
    calc
      Kakeya.realRpowENN δ (3 / 2 + localLoss + (totalLoss + coarseLoss) / 2) * F.enncard ^ (1 / 2 : ℝ)
        = (deltaLocal * Kakeya.realRpowENN δ ((totalLoss + coarseLoss) / 2)) * F.enncard ^ (1 / 2 : ℝ) := by
          rw [h8]
      _ = deltaLocal * (Kakeya.realRpowENN δ ((totalLoss + coarseLoss) / 2) * F.enncard ^ (1 / 2 : ℝ)) := by
          simp [mul_assoc]
      _ ≤ deltaLocal * (theta_enn ^ (1 / 2 : ℝ) * q * M ^ (1 / 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left h_core' (by positivity)
      _ = deltaLocal * theta_enn ^ (1 / 2 : ℝ) * (q * M ^ (1 / 2 : ℝ)) := by
          simp [mul_assoc]
      _ ≤ volume angular.shading.union := h6

  -- Step 7: Absorb strict exponent gap using antitone property
  have h11 : 3 / 2 + localLoss + (totalLoss + coarseLoss) / 2 ≤ 3 / 2 + outputLoss := by linarith

  have h12 : Kakeya.realRpowENN δ (3 / 2 + outputLoss) ≤
      Kakeya.realRpowENN δ (3 / 2 + localLoss + (totalLoss + coarseLoss) / 2) :=
    hairbrush_rpow_antitone hδ (by linarith) h11

  have h13 : Kakeya.realRpowENN δ (3 / 2 + outputLoss) * F.enncard ^ (1 / 2 : ℝ) ≤
      volume angular.shading.union := by
    calc
      Kakeya.realRpowENN δ (3 / 2 + outputLoss) * F.enncard ^ (1 / 2 : ℝ)
        ≤ Kakeya.realRpowENN δ (3 / 2 + localLoss + (totalLoss + coarseLoss) / 2) * F.enncard ^ (1 / 2 : ℝ) := by
          exact mul_le_mul_of_nonneg_right h12 (by positivity)
      _ ≤ volume angular.shading.union := h9

  -- Step 8: Convert to HairbrushFiberTarget with theta := 1
  have h14 : ENNReal.ofReal (Real.sqrt (1 : ℝ)) = 1 := by
    have h : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
    rw [h]
    simp

  simpa [HairbrushFiberTarget, h14] using h13

end Kakeya.Assouad
