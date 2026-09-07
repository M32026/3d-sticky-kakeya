import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureExternalWeightRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SourceWitnessCoarsePlaneMapBalanced
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SourceWitnessCoarseFiberMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.StickyFiberCardinalityRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CoarseTopLevelCWABridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WeakenLoss
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCardinalityRetention
import MyLeanRepo.Kakeya.Assouad.WZ1.DyadicBand

/-!
# One-pass regularization of a sampled coarse shading

The weights in this module are the actual carrier masses of a sampled
source-witness coarse shading.  We first keep a factor-two band of complete
fine-fiber cardinalities, weighted by those carrier masses, and then run the
pure nearby-scale regularizer once on the ambient coarse family.  The final
parent set therefore simultaneously supports nearby CWA, a sampled coarse
shading, and the complete rebalanced fine fibers.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Logarithmic price of regularizing complete fine-fiber cardinalities. -/
def sampledCoarseFiberBandLoss (fineCard : ℕ) : ENNReal :=
  ENNReal.ofReal (Real.logb 2 ((fineCard : ℝ) / 1) + 1)

/-- A sampled coarse family, its complete fine pullback, and reconstructed
nearby CWA, all synchronized on one nonempty set of coarse parents. -/
structure PureWZ2SampledCoarseFiberRegularizationData
    {delta rho target : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    {sourceWitness :
      PureWZ2SourceWitnessCoarseShadingData balanced}
    (sampled : PureWZ2SourceWitnessCoarseLipschitzBalancedData
      (target := target) sourceWitness)
    {ambientConstant outputConstant normalizationWeight weightUpper :
      ENNReal}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := coarse) ambientConstant outputConstant levelCount) where
  bandLower : ℝ
  bandLower_pos : 0 < bandLower
  bandParents : Finset (Fin coarse.card)
  fiber_band : ∀ parent ∈ bandParents,
    ENNReal.ofReal bandLower ≤
        ((cover.toPaperTubeCover.fiberIndices parent).card : ENNReal) ∧
      ((cover.toPaperTubeCover.fiberIndices parent).card : ENNReal) ≤
        ENNReal.ofReal (2 * bandLower)
  band_mass_retention :
    sampled.selected.mass ≤
      sampledCoarseFiberBandLoss fine.card *
        ∑ parent ∈ bandParents,
          volume (sampled.selected.carrier parent)
  externalWeight : Fin coarse.card → ENNReal
  externalWeight_eq : ∀ parent, externalWeight parent =
    if parent ∈ bandParents then
      volume (sampled.selected.carrier parent) else 0
  regularized : WZ2PaperPureExternalWeightRegularizationData schedule
    normalizationWeight weightUpper externalWeight
  support : ∀ parent : Fin regularized.selected.family.card,
    regularized.selected.embedding parent ∈ bandParents
  selectedShading :
    WZ1PaperTubeShading regularized.selected.family
  selectedShading_eq : selectedShading =
    restrictPaperShading regularized.selected sampled.selected
  selected_cubical : WZ1PaperIsCubicalShading selectedShading
  selected_mass_eq : selectedShading.mass =
    ∑ parent : Fin regularized.selected.family.card,
      externalWeight (regularized.selected.embedding parent)
  retained_coarse_mass :
    sampled.selected.mass ≤
      (sampledCoarseFiberBandLoss fine.card *
        regularized.regularizationLoss) * selectedShading.mass
  restriction : PureWZ2Section6CompleteParentRestrictionData
    cover fineShading regularized.selectedIndices
  restriction_coarse_eq :
    restriction.selectedCoarse = regularized.selected
  selected_fine_mass_eq :
    restriction.selectedFineShading.mass =
      ∑ parent : Fin regularized.selected.family.card,
        cover.toPaperTubeCover.fiberShadedMass fineShading
          (regularized.selected.embedding parent)
  selected_fiber_band :
    ∀ parent : Fin regularized.selected.family.card,
      ENNReal.ofReal bandLower ≤
          ((cover.toPaperTubeCover.fiberIndices
            (regularized.selected.embedding parent)).card : ENNReal) ∧
        ((cover.toPaperTubeCover.fiberIndices
          (regularized.selected.embedding parent)).card : ENNReal) ≤
          ENNReal.ofReal (2 * bandLower)

/-- Select a cardinality band with sampled carrier weights and run the pure
nearby regularizer once. -/
theorem sampled_coarse_fiber_regularization
    {delta rho target : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    {sourceWitness :
      PureWZ2SourceWitnessCoarseShadingData balanced}
    (sampled : PureWZ2SourceWitnessCoarseLipschitzBalancedData
      (target := target) sourceWitness)
    {ambientConstant outputConstant normalizationWeight weightUpper :
      ENNReal}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := coarse) ambientConstant outputConstant levelCount)
    (ambient : WZ2PaperPureCWAAtNearbyScales coarse ambientConstant)
    (coarseNonempty : coarse.Nonempty)
    (hfineCubical : WZ1PaperIsCubicalShading fineShading)
    (normalizationWeight_ne_zero : normalizationWeight ≠ 0)
    (normalizationWeight_ne_top : normalizationWeight ≠ ⊤)
    (weightUpper_ne_top : weightUpper ≠ ⊤)
    (mass_lower :
      sampledCoarseFiberBandLoss fine.card *
          (normalizationWeight * coarse.enncard) ≤
        sampled.selected.mass)
    (weight_upper : ∀ parent,
      volume (sampled.selected.carrier parent) ≤ weightUpper)
    (output_finite : WZ2PaperFiniteErrorConstant outputConstant)
    (absorb :
      let degreeConstant :=
        16 * (schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * coarse.card) + 1 : ENNReal) ^
            schedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * coarse.card) + 1 : ENNReal) ^
            (schedule.scaleCount + 1)
      max degreeConstant
          ((normalizationWeight⁻¹ *
              (ambientConstant *
                (regularizationLoss * weightUpper) *
                degreeConstant)) *
            ambientConstant) ≤
        outputConstant) :
    Nonempty (PureWZ2SampledCoarseFiberRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) sampled schedule) := by
  classical
  let parents : Finset (Fin coarse.card) := Finset.univ
  let fiberCard : Fin coarse.card → ENNReal := fun parent =>
    (cover.toPaperTubeCover.fiberIndices parent).card
  let coarseWeight : Fin coarse.card → ENNReal := fun parent =>
    volume (sampled.selected.carrier parent)
  have hfineNonempty : fine.Nonempty := by
    let parent : Fin coarse.card := ⟨0, coarseNonempty⟩
    rcases cover.toPaperTubeCover.parent_surjective parent with
      ⟨source, _hsource⟩
    exact Nat.zero_lt_of_lt source.isLt
  have hfiberLower : ∀ parent ∈ parents,
      ENNReal.ofReal 1 ≤ fiberCard parent := by
    intro parent _
    rcases cover.toPaperTubeCover.parent_surjective parent with
      ⟨source, hsource⟩
    have hmem : source ∈ cover.toPaperTubeCover.fiberIndices parent :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsource⟩
    have hcard : 1 ≤
        (cover.toPaperTubeCover.fiberIndices parent).card :=
      Finset.one_le_card.mpr ⟨source, hmem⟩
    simpa [fiberCard] using (show (1 : ENNReal) ≤
        ((cover.toPaperTubeCover.fiberIndices parent).card : ENNReal) by
      exact_mod_cast hcard)
  have hfiberUpper : ∀ parent ∈ parents,
      fiberCard parent ≤ ENNReal.ofReal (fine.card : ℝ) := by
    intro parent _
    have hcard : (cover.toPaperTubeCover.fiberIndices parent).card ≤
        fine.card := by
      simpa using Finset.card_le_card
        (Finset.subset_univ
          (cover.toPaperTubeCover.fiberIndices parent) :
          cover.toPaperTubeCover.fiberIndices parent ⊆
            (Finset.univ : Finset (Fin fine.card)))
    simpa [fiberCard] using (show
      ((cover.toPaperTubeCover.fiberIndices parent).card : ENNReal) ≤
        (fine.card : ENNReal) by exact_mod_cast hcard)
  rcases mass_weighted_dyadic_band parents fiberCard coarseWeight
      1 (fine.card : ℝ) (by norm_num)
      (by exact_mod_cast hfineNonempty) hfiberLower hfiberUpper with
    ⟨bandLower, bandParents, hbandLower, _hbandSubset,
      hband, hbandMass⟩
  let externalWeight : Fin coarse.card → ENNReal := fun parent =>
    if parent ∈ bandParents then coarseWeight parent else 0
  have hexternalSum :
      (∑ parent : Fin coarse.card, externalWeight parent) =
        ∑ parent ∈ bandParents, coarseWeight parent := by
    simp [externalWeight]
  have htotalWeight :
      (∑ parent ∈ parents, coarseWeight parent) =
        sampled.selected.mass := by
    simp only [parents, coarseWeight, Finset.sum_filter,
      Finset.mem_univ, if_true]
    rfl
  have hbandLossPos : 0 < sampledCoarseFiberBandLoss fine.card := by
    apply ENNReal.ofReal_pos.mpr
    have hcard : (1 : ℝ) ≤ (fine.card : ℝ) / 1 := by
      norm_num
      exact_mod_cast hfineNonempty
    have hlog : 0 ≤ Real.logb 2 ((fine.card : ℝ) / 1) :=
      Real.logb_nonneg (by norm_num) hcard
    change 0 < Real.logb 2 ((fine.card : ℝ) / 1) + 1
    linarith
  have hbandLossTop : sampledCoarseFiberBandLoss fine.card ≠ ⊤ := by
    simp [sampledCoarseFiberBandLoss]
  have hexternalMassLower :
      normalizationWeight * coarse.enncard ≤
        ∑ parent : Fin coarse.card, externalWeight parent := by
    rw [hexternalSum]
    have hscaled :
        sampledCoarseFiberBandLoss fine.card *
            (normalizationWeight * coarse.enncard) ≤
          sampledCoarseFiberBandLoss fine.card *
            (∑ parent ∈ bandParents, coarseWeight parent) := by
      calc
        sampledCoarseFiberBandLoss fine.card *
              (normalizationWeight * coarse.enncard) ≤
            sampled.selected.mass := mass_lower
        _ ≤ (∑ parent ∈ bandParents, coarseWeight parent) *
              sampledCoarseFiberBandLoss fine.card := by
          rw [← htotalWeight]
          simpa [sampledCoarseFiberBandLoss] using hbandMass
        _ = sampledCoarseFiberBandLoss fine.card *
            (∑ parent ∈ bandParents, coarseWeight parent) := by ring
    exact (ENNReal.mul_le_mul_iff_right
      hbandLossPos.ne' hbandLossTop).mp hscaled
  have hexternalUpper : ∀ parent, externalWeight parent ≤ weightUpper := by
    intro parent
    by_cases hparent : parent ∈ bandParents
    · simpa [externalWeight, hparent, coarseWeight] using
        weight_upper parent
    · simp [externalWeight, hparent]
  rcases schedule.regularizeExternalWeight ambient coarseNonempty
      externalWeight normalizationWeight_ne_zero
      normalizationWeight_ne_top weightUpper_ne_top
      hexternalMassLower hexternalUpper output_finite absorb with
    ⟨regularized⟩
  have hsupport : ∀ parent : Fin regularized.selected.family.card,
      regularized.selected.embedding parent ∈ bandParents := by
    intro parent
    by_contra hnot
    have hzero : externalWeight
        (regularized.selected.embedding parent) = 0 := by
      simp [externalWeight, hnot]
    have hlower := (regularized.weight_band parent).1
    rw [hzero] at hlower
    exact (not_le.mpr regularized.weightLevel_pos) hlower
  let selectedShading :=
    restrictPaperShading regularized.selected sampled.selected
  have hselectedMass : selectedShading.mass =
      ∑ parent : Fin regularized.selected.family.card,
        externalWeight (regularized.selected.embedding parent) := by
    rw [restrictPaperShading_mass]
    apply Finset.sum_congr rfl
    intro parent _
    rw [show externalWeight (regularized.selected.embedding parent) =
        coarseWeight (regularized.selected.embedding parent) by
      simp [externalWeight, hsupport parent]]
  have hretainedCoarse : sampled.selected.mass ≤
      (sampledCoarseFiberBandLoss fine.card *
        regularized.regularizationLoss) * selectedShading.mass := by
    calc
      sampled.selected.mass ≤
          sampledCoarseFiberBandLoss fine.card *
            (∑ parent ∈ bandParents, coarseWeight parent) := by
        rw [← htotalWeight]
        simpa [sampledCoarseFiberBandLoss, mul_comm] using hbandMass
      _ = sampledCoarseFiberBandLoss fine.card *
          (∑ parent : Fin coarse.card, externalWeight parent) := by
        rw [hexternalSum]
      _ ≤ sampledCoarseFiberBandLoss fine.card *
          (regularized.regularizationLoss *
            ∑ parent : Fin regularized.selected.family.card,
              externalWeight (regularized.selected.embedding parent)) := by
        gcongr
        exact regularized.retained_weight
      _ = (sampledCoarseFiberBandLoss fine.card *
          regularized.regularizationLoss) * selectedShading.mass := by
        rw [hselectedMass]
        ring
  have hselectedIndicesNonempty :
      regularized.selectedIndices.Nonempty := by
    by_contra hnot
    have hempty : regularized.selectedIndices = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnot
    have hselectedCard : regularized.selected.family.card = 0 := by
      rw [regularized.selected_eq, hempty]
      rfl
    exact (Nat.ne_of_gt regularized.selected_nonempty) hselectedCard
  rcases pure_wz2_section6_complete_parent_restriction cover fineShading
      hfineCubical regularized.selectedIndices
      hselectedIndicesNonempty with ⟨restriction⟩
  have hcoarseEq : restriction.selectedCoarse =
      regularized.selected := by
    rw [restriction.selectedCoarse_eq, regularized.selected_eq]
  have hselectedFineMass : restriction.selectedFineShading.mass =
      ∑ parent : Fin regularized.selected.family.card,
        cover.toPaperTubeCover.fiberShadedMass fineShading
          (regularized.selected.embedding parent) := by
    rw [restriction.selected_mass_eq_finset]
    rw [show regularized.selectedIndices =
        Finset.image regularized.selected.embedding Finset.univ by
      rw [regularized.selected_eq]
      exact (Finset.image_orderEmbOfFin_univ
        regularized.selectedIndices rfl).symm]
    rw [Finset.sum_image (fun first _ second _ heq =>
      regularized.selected.embedding.injective heq)]
  have hselectedFiberBand :
      ∀ parent : Fin regularized.selected.family.card,
        ENNReal.ofReal bandLower ≤
            ((cover.toPaperTubeCover.fiberIndices
              (regularized.selected.embedding parent)).card : ENNReal) ∧
          ((cover.toPaperTubeCover.fiberIndices
            (regularized.selected.embedding parent)).card : ENNReal) ≤
            ENNReal.ofReal (2 * bandLower) := by
    intro parent
    exact hband _ (hsupport parent)
  exact ⟨{
    bandLower := bandLower
    bandLower_pos := lt_of_lt_of_le (by norm_num) hbandLower
    bandParents := bandParents
    fiber_band := hband
    band_mass_retention := by
      rw [← htotalWeight]
      simpa [sampledCoarseFiberBandLoss, mul_comm] using hbandMass
    externalWeight := externalWeight
    externalWeight_eq := fun _ => rfl
    regularized := regularized
    support := hsupport
    selectedShading := selectedShading
    selectedShading_eq := rfl
    selected_cubical :=
      restrictPaperShading_cubical regularized.selected sampled.cubical
    selected_mass_eq := hselectedMass
    retained_coarse_mass := hretainedCoarse
    restriction := restriction
    restriction_coarse_eq := hcoarseEq
    selected_fine_mass_eq := hselectedFineMass
    selected_fiber_band := hselectedFiberBand
  }⟩

/-- Sum any parentwise sampled-carrier versus complete-fiber comparison over
the synchronized parent set selected by the one-pass regularizer. -/
theorem PureWZ2SampledCoarseFiberRegularizationData.selected_coarse_to_complete_fine_mass
    {delta rho target : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    {sourceWitness :
      PureWZ2SourceWitnessCoarseShadingData balanced}
    {sampled : PureWZ2SourceWitnessCoarseLipschitzBalancedData
      (target := target) sourceWitness}
    {ambientConstant outputConstant normalizationWeight weightUpper :
      ENNReal}
    {levelCount : ℕ}
    {schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := coarse) ambientConstant outputConstant levelCount}
    (data : PureWZ2SampledCoarseFiberRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) sampled schedule)
    (fineCellVolume coarseCellVolume : ENNReal)
    (hparent : ∀ parent : Fin coarse.card,
      volume (sampled.selected.carrier parent) * fineCellVolume ≤
        coarseCellVolume *
          cover.toPaperTubeCover.fiberShadedMass fineShading parent) :
    data.selectedShading.mass * fineCellVolume ≤
      coarseCellVolume * data.restriction.selectedFineShading.mass := by
  rw [data.selectedShading_eq, restrictPaperShading_mass,
    data.selected_fine_mass_eq]
  calc
    (∑ parent : Fin data.regularized.selected.family.card,
        volume (sampled.selected.carrier
          (data.regularized.selected.embedding parent))) *
          fineCellVolume =
        ∑ parent : Fin data.regularized.selected.family.card,
          volume (sampled.selected.carrier
            (data.regularized.selected.embedding parent)) *
              fineCellVolume := by
      rw [Finset.sum_mul]
    _ ≤ ∑ parent : Fin data.regularized.selected.family.card,
        coarseCellVolume *
          cover.toPaperTubeCover.fiberShadedMass fineShading
            (data.regularized.selected.embedding parent) := by
      apply Finset.sum_le_sum
      intro parent _
      exact hparent (data.regularized.selected.embedding parent)
    _ = coarseCellVolume *
        ∑ parent : Fin data.regularized.selected.family.card,
          cover.toPaperTubeCover.fiberShadedMass fineShading
            (data.regularized.selected.embedding parent) := by
      rw [Finset.mul_sum]

/-- The synchronized complete fine restriction is carrierwise contained in
the same tube subfamily's restriction of any ambient shading containing the
fine source used by the regularizer. -/
theorem PureWZ2SampledCoarseFiberRegularizationData.restricted_mass_le_ambient_restrict
    {delta rho target : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading ambientFineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    {sourceWitness :
      PureWZ2SourceWitnessCoarseShadingData balanced}
    {sampled : PureWZ2SourceWitnessCoarseLipschitzBalancedData
      (target := target) sourceWitness}
    {ambientConstant outputConstant normalizationWeight weightUpper :
      ENNReal}
    {levelCount : ℕ}
    {schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := coarse) ambientConstant outputConstant levelCount}
    (data : PureWZ2SampledCoarseFiberRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) sampled schedule)
    (hsub : PaperIsSubshading fineShading ambientFineShading) :
    data.restriction.selectedFineShading.mass ≤
      (restrictPaperShading data.restriction.selectedFine
        ambientFineShading).mass := by
  rw [data.restriction.selectedFineShading_eq,
    restrictPaperShading_mass, restrictPaperShading_mass]
  apply Finset.sum_le_sum
  intro index _
  exact measure_mono (hsub (data.restriction.selectedFine.embedding index))

/-- Ambient fine density and an explicit retained-mass inequality transfer a
top-level Convex--Wolff bound to the complete selected fine restriction. -/
theorem PureWZ2SampledCoarseFiberRegularizationData.restricted_fine_top_level_cwa
    {delta rho target sigma sourceLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading ambientFineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    {sourceWitness :
      PureWZ2SourceWitnessCoarseShadingData balanced}
    {sampled : PureWZ2SourceWitnessCoarseLipschitzBalancedData
      (target := target) sourceWitness}
    {ambientConstant outputConstant normalizationWeight weightUpper :
      ENNReal}
    {levelCount : ℕ}
    {schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := coarse) ambientConstant outputConstant levelCount}
    (data : PureWZ2SampledCoarseFiberRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) sampled schedule)
    (ambientExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss fine ambientFineShading)
    (ambientLine : WZ1PaperIsLineClass fine)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hsub : PaperIsSubshading fineShading ambientFineShading)
    (selectionLoss C : ENNReal)
    (hretained : ambientFineShading.mass ≤
      selectionLoss * data.restriction.selectedFineShading.mass)
    (ambientCWA : WZ2PaperConvexWolffBound fine C) :
    WZ2PaperConvexWolffBound data.restriction.selectedFine.family
      (((Kakeya.realRpowENN delta sourceLoss)⁻¹ *
        (selectionLoss * (55296 * Kakeya.deltaTubeVolume 1))) * C) := by
  let density : ENNReal := Kakeya.realRpowENN delta sourceLoss
  let geometryConstant : ENNReal := 55296 * Kakeya.deltaTubeVolume 1
  have hdensityZero : density ≠ 0 := by
    simp [density, Kakeya.realRpowENN,
      Real.rpow_pos_of_pos ambientExtremal.delta_pos]
  have hdensityTop : density ≠ ⊤ := by
    simp [density, Kakeya.realRpowENN]
  have hbody : Kakeya.realRpowENN delta 2 * fine.enncard ≤
      (wz1PaperBodyFamily fine).mass :=
    paperBodyFamily_mass_lower_rpow_two ambientExtremal.delta_pos
      (hdeltaSmall.trans (by norm_num)) ambientLine
  have hambientMass : density * fine.enncard *
      Kakeya.realRpowENN delta 2 ≤ ambientFineShading.mass := by
    calc
      density * fine.enncard * Kakeya.realRpowENN delta 2 =
          density * (Kakeya.realRpowENN delta 2 * fine.enncard) := by
        ring
      _ ≤ density * (wz1PaperBodyFamily fine).mass := by gcongr
      _ ≤ ambientFineShading.mass := ambientExtremal.dense
  have hretainedAmbient : ambientFineShading.mass ≤
      selectionLoss *
        (restrictPaperShading data.restriction.selectedFine
          ambientFineShading).mass := by
    calc
      ambientFineShading.mass ≤
          selectionLoss * data.restriction.selectedFineShading.mass :=
        hretained
      _ ≤ selectionLoss *
          (restrictPaperShading data.restriction.selectedFine
            ambientFineShading).mass := by
        gcongr
        exact data.restricted_mass_le_ambient_restrict hsub
  have hcardinality : density * fine.enncard ≤
      (selectionLoss * geometryConstant) *
        data.restriction.selectedFine.family.enncard := by
    simpa [geometryConstant] using
      wz2PaperWeightedCardinality_retained_from_subfamily_mass
        ambientExtremal.delta_pos hdeltaSmall ambientLine
        ambientFineShading data.restriction.selectedFine
        density selectionLoss hambientMass hretainedAmbient
  change WZ2PaperConvexWolffBound
    data.restriction.selectedFine.family
      ((density⁻¹ * (selectionLoss * geometryConstant)) * C)
  exact ambientCWA.subfamily_of_weighted_cardinality
    data.restriction.selectedFine hdensityZero hdensityTop hcardinality

/-- The factor-two complete-fiber cardinality band transfers top-level CWA
from the synchronized selected fine family to the selected coarse family. -/
theorem PureWZ2SampledCoarseFiberRegularizationData.selected_coarse_top_level_cwa
    {delta rho target : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    {sourceWitness :
      PureWZ2SourceWitnessCoarseShadingData balanced}
    {sampled : PureWZ2SourceWitnessCoarseLipschitzBalancedData
      (target := target) sourceWitness}
    {ambientConstant outputConstant normalizationWeight weightUpper :
      ENNReal}
    {levelCount : ℕ}
    {schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := coarse) ambientConstant outputConstant levelCount}
    (data : PureWZ2SampledCoarseFiberRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) sampled schedule)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hscale : 6 * delta ≤ rho)
    (C : ENNReal)
    (fineCWA : WZ2PaperConvexWolffBound
      data.restriction.selectedFine.family C) :
    WZ2PaperConvexWolffBound data.regularized.selected.family (2 * C) := by
  let restrictedCover := data.restriction.restrictedCover.toPaperTubeCover
  have hfiberUniform :
      ∀ first second : Fin data.restriction.selectedCoarse.family.card,
        ((restrictedCover.fiberIndices first).card : ENNReal) ≤
          2 * ((restrictedCover.fiberIndices second).card : ENNReal) := by
    intro first second
    rw [data.restriction.full_fiber_card_eq,
      data.restriction.full_fiber_card_eq]
    have hfirstMem : data.restriction.selectedCoarse.embedding first ∈
        data.regularized.selectedIndices :=
      data.restriction.selectedCoarse_embedding_mem first
    have hsecondMem : data.restriction.selectedCoarse.embedding second ∈
        data.regularized.selectedIndices :=
      data.restriction.selectedCoarse_embedding_mem second
    rcases data.regularized.selected_embedding_surjective
        _ hfirstMem with ⟨regularizedFirst, hfirst⟩
    rcases data.regularized.selected_embedding_surjective
        _ hsecondMem with ⟨regularizedSecond, hsecond⟩
    have hfirstBand := data.selected_fiber_band regularizedFirst
    have hsecondBand := data.selected_fiber_band regularizedSecond
    rw [← hfirst, ← hsecond]
    calc
      ((cover.toPaperTubeCover.fiberIndices
          (data.regularized.selected.embedding regularizedFirst)).card :
          ENNReal) ≤ ENNReal.ofReal (2 * data.bandLower) :=
        hfirstBand.2
      _ = 2 * ENNReal.ofReal data.bandLower := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ ≤ 2 *
          ((cover.toPaperTubeCover.fiberIndices
            (data.regularized.selected.embedding regularizedSecond)).card :
            ENNReal) := by
        gcongr
        exact hsecondBand.1
  have hcoarseCWA : WZ2PaperConvexWolffBound
      data.restriction.selectedCoarse.family (2 * C) := by
    apply paperConvexWolffBound_of_uniform_cover
        restrictedCover.parent restrictedCover.parent_surjective
        (fun fineIndex => ?_) 2 C hfiberUniform fineCWA
    exact wz2PaperTubeCarrierCovers_of_strict_cover
      hdelta hrho hscale
      (data.restriction.restrictedCover.fine_line_class fineIndex)
      (data.restriction.restrictedCover.coarse_line_class
        (restrictedCover.parent fineIndex))
      (restrictedCover.parent_covers fineIndex)
  rw [data.restriction_coarse_eq] at hcoarseCWA
  exact hcoarseCWA

/-- Recover cropped extremality on the synchronized selected coarse family
from explicit indexed-mass retention.  Nearby CWA comes from the one-pass
regularizer; density is the only place where the loss factor is absorbed. -/
theorem PureWZ2SampledCoarseFiberRegularizationData.selected_coarse_extremal
    {delta rho target sigma sourceLoss outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading}
    {sourceWitness :
      PureWZ2SourceWitnessCoarseShadingData balanced}
    {sampled : PureWZ2SourceWitnessCoarseLipschitzBalancedData
      (target := target) sourceWitness}
    {ambientConstant outputConstant normalizationWeight weightUpper :
      ENNReal}
    {levelCount : ℕ}
    {schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := coarse) ambientConstant outputConstant levelCount}
    (data : PureWZ2SampledCoarseFiberRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) sampled schedule)
    (ambientExtremal : WZ2PaperCroppedIsExtremal
      sigma sourceLoss coarse coarseShading)
    (hselectedSub : ∀ index, data.selectedShading.carrier index ⊆
      coarseShading.carrier (data.regularized.selected.embedding index))
    (massLoss : ENNReal)
    (hmassLossPos : 0 < massLoss)
    (hmassLossTop : massLoss ≠ ⊤)
    (hmass : coarseShading.mass ≤ massLoss * data.selectedShading.mass)
    (hloss : sourceLoss ≤ outputLoss)
    (hnearby : outputConstant ≤
      Kakeya.realRpowENN rho (-outputLoss))
    (hslack : massLoss * Kakeya.realRpowENN rho outputLoss ≤
      Kakeya.realRpowENN rho sourceLoss)
    (houtputLoss : 0 < outputLoss) :
    WZ2PaperCroppedIsExtremal sigma outputLoss
      data.regularized.selected.family data.selectedShading := by
  have houtputFinite : WZ2PaperFiniteErrorConstant
      (Kakeya.realRpowENN rho (-outputLoss)) := by
    have hone : (1 : ENNReal) ≤
        Kakeya.realRpowENN rho (-outputLoss) := by
      have hreal : 1 ≤ Real.rpow rho (-outputLoss) := by
        have hzero : Real.rpow rho 0 ≤ Real.rpow rho (-outputLoss) :=
          Real.rpow_le_rpow_of_exponent_ge ambientExtremal.delta_pos
            ambientExtremal.delta_le_one (by linarith)
        simpa using hzero
      simpa [Kakeya.realRpowENN] using ENNReal.ofReal_mono hreal
    exact ⟨hone, by simp [Kakeya.realRpowENN]⟩
  have hcwaNearby : WZ2PaperPureCWAAtNearbyScales
      data.regularized.selected.family
      (Kakeya.realRpowENN rho (-outputLoss)) :=
    weaken_cwa_nearby_scales data.regularized.pure_cwa_nearby
      hnearby houtputFinite
  have hbodyMass : (wz1PaperBodyFamily
      data.regularized.selected.family).mass ≤
      (wz1PaperBodyFamily coarse).mass := by
    change
      (∑ index : Fin data.regularized.selected.family.card,
        volume (wz1PaperTubeCarrier
          (data.regularized.selected.family.tube index))) ≤
      ∑ index : Fin coarse.card,
        volume (wz1PaperTubeCarrier (coarse.tube index))
    let image : Finset (Fin coarse.card) :=
      Finset.image data.regularized.selected.embedding Finset.univ
    calc
      (∑ index : Fin data.regularized.selected.family.card,
          volume (wz1PaperTubeCarrier
            (data.regularized.selected.family.tube index))) =
          ∑ ambientIndex ∈ image,
            volume (wz1PaperTubeCarrier (coarse.tube ambientIndex)) := by
        rw [Finset.sum_image (fun first _ second _ heq =>
          data.regularized.selected.embedding.injective heq)]
        apply Finset.sum_congr rfl
        intro index _
        rw [data.regularized.selected.tube_eq]
      _ ≤ ∑ index : Fin coarse.card,
          volume (wz1PaperTubeCarrier (coarse.tube index)) := by
        exact Finset.sum_le_sum_of_subset
          (Finset.subset_univ image)
  have hdense : Kakeya.realRpowENN rho outputLoss *
      (wz1PaperBodyFamily data.regularized.selected.family).mass ≤
        data.selectedShading.mass := by
    have hsourceDense : Kakeya.realRpowENN rho sourceLoss *
        (wz1PaperBodyFamily coarse).mass ≤ coarseShading.mass :=
      ambientExtremal.dense
    have hscaled : massLoss *
        (Kakeya.realRpowENN rho outputLoss *
          (wz1PaperBodyFamily
            data.regularized.selected.family).mass) ≤
        massLoss * data.selectedShading.mass := by
      calc
        massLoss * (Kakeya.realRpowENN rho outputLoss *
            (wz1PaperBodyFamily
              data.regularized.selected.family).mass) =
            (massLoss * Kakeya.realRpowENN rho outputLoss) *
              (wz1PaperBodyFamily
                data.regularized.selected.family).mass := by ring
        _ ≤ Kakeya.realRpowENN rho sourceLoss *
            (wz1PaperBodyFamily
              data.regularized.selected.family).mass := by gcongr
        _ ≤ Kakeya.realRpowENN rho sourceLoss *
            (wz1PaperBodyFamily coarse).mass := by gcongr
        _ ≤ coarseShading.mass := hsourceDense
        _ ≤ massLoss * data.selectedShading.mass := hmass
    exact (ENNReal.mul_le_mul_iff_right
      hmassLossPos.ne' hmassLossTop).mp hscaled
  have hvolume : volume data.selectedShading.union ≤
      Kakeya.realRpowENN rho (sigma - outputLoss) := by
    have hunion : data.selectedShading.union ⊆ coarseShading.union := by
      rintro point ⟨index, hpoint⟩
      exact ⟨data.regularized.selected.embedding index,
        hselectedSub index hpoint⟩
    calc
      volume data.selectedShading.union ≤ volume coarseShading.union :=
        measure_mono hunion
      _ ≤ Kakeya.realRpowENN rho (sigma - sourceLoss) :=
        ambientExtremal.volume_upper
      _ ≤ Kakeya.realRpowENN rho (sigma - outputLoss) := by
        apply ENNReal.ofReal_mono
        exact Real.rpow_le_rpow_of_exponent_ge
          ambientExtremal.delta_pos ambientExtremal.delta_le_one
          (by linarith)
  exact {
    delta_pos := ambientExtremal.delta_pos
    delta_le_one := ambientExtremal.delta_le_one
    nonempty := data.regularized.selected_nonempty
    cwa_nearby_scales := hcwaNearby
    cubical := data.selected_cubical
    dense := hdense
    volume_upper := hvolume
  }

end Kakeya.Assouad.PureWZ2

end
