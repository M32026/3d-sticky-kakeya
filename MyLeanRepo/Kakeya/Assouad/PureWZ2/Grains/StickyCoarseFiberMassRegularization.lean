import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureExternalWeightRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.StickyFiberCardinalityRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WeakenLoss
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper

/-!
# Coarse regularization weighted by complete fine-fiber shaded mass

Start with the closed factor-two cardinality band of the original complete
sticky fibers.  Extend the complete-fiber shaded mass by zero outside that
band and run the pure nearby-scale regularizer once on the original coarse
family.  The final selected coarse family therefore has all of the following
on exactly the same indices:

* reconstructed pure nearby-scale CWA;
* factor-two original fine-fiber cardinality;
* a complete fine-fiber restriction;
* quantitative retention of the original refined fine shaded mass.

No CWA inheritance is asserted for the intermediate cardinality band.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- One synchronized selected coarse family and its complete fine pullback. -/
structure PureWZ2StickyCoarseFiberMassRegularizationData
    {delta sigma stickyLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    {outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sticky.coarse)
        (Kakeya.realRpowENN rho.1 (-stickyLoss))
        outputConstant levelCount) where
  cardinalityBand : PureWZ2StickyFiberCardinalityRegularizationData sticky
  externalWeight : Fin sticky.coarse.card → ENNReal
  externalWeight_eq : ∀ parent, externalWeight parent =
    if parent ∈ cardinalityBand.selectedParents then
      sticky.cover.toPaperTubeCover.fiberShadedMass
        sticky.refined parent else 0
  regularized : WZ2PaperPureExternalWeightRegularizationData schedule
    normalizationWeight weightUpper externalWeight
  support : ∀ parent : Fin regularized.selected.family.card,
    regularized.selected.embedding parent ∈ cardinalityBand.selectedParents
  restriction : PureWZ2Section6CompleteParentRestrictionData
    sticky.cover sticky.refined regularized.selectedIndices
  restriction_coarse_eq :
    restriction.selectedCoarse = regularized.selected
  selected_fiber_band :
    ∀ parent : Fin regularized.selected.family.card,
      ENNReal.ofReal cardinalityBand.bandLower ≤
          ((sticky.cover.toPaperTubeCover.fiberIndices
            (regularized.selected.embedding parent)).card : ENNReal) ∧
        ((sticky.cover.toPaperTubeCover.fiberIndices
          (regularized.selected.embedding parent)).card : ENNReal) ≤
          ENNReal.ofReal (2 * cardinalityBand.bandLower)
  selected_fine_mass_eq :
    restriction.selectedFineShading.mass =
      ∑ parent : Fin regularized.selected.family.card,
        externalWeight (regularized.selected.embedding parent)
  retained_fine_mass :
    sticky.refined.mass ≤
      (ENNReal.ofReal
          (Real.logb 2
            ((sticky.selected.family.card : ℝ) / 1) + 1) *
        regularized.regularizationLoss) *
          restriction.selectedFineShading.mass

/-- Run complete-fiber cardinality banding and finite nearby regularization
with the complete-fiber shaded masses as external weights. -/
theorem pure_wz2_sticky_coarse_fiber_mass_regularization
    {delta sigma stickyLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    {outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sticky.coarse)
        (Kakeya.realRpowENN rho.1 (-stickyLoss))
        outputConstant levelCount)
    (normalizationWeight_ne_zero : normalizationWeight ≠ 0)
    (normalizationWeight_ne_top : normalizationWeight ≠ ⊤)
    (weightUpper_ne_top : weightUpper ≠ ⊤)
    (mass_lower :
      ENNReal.ofReal
          (Real.logb 2
            ((sticky.selected.family.card : ℝ) / 1) + 1) *
        (normalizationWeight * sticky.coarse.enncard) ≤
          sticky.refined.mass)
    (weight_upper : ∀ parent,
      sticky.cover.toPaperTubeCover.fiberShadedMass
        sticky.refined parent ≤ weightUpper)
    (output_finite : WZ2PaperFiniteErrorConstant outputConstant)
    (absorb :
      let degreeConstant :=
        16 * (schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * sticky.coarse.card) + 1 : ENNReal) ^
            schedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * sticky.coarse.card) + 1 : ENNReal) ^
            (schedule.scaleCount + 1)
      max degreeConstant
          ((normalizationWeight⁻¹ *
              (Kakeya.realRpowENN rho.1 (-stickyLoss) *
                (regularizationLoss * weightUpper) *
                degreeConstant)) *
            Kakeya.realRpowENN rho.1 (-stickyLoss)) ≤
        outputConstant) :
    Nonempty (PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) sticky schedule) := by
  classical
  rcases pure_wz2_sticky_fiber_cardinality_regularization sticky with
    ⟨cardinalityBand⟩
  let fiberWeight : Fin sticky.coarse.card → ENNReal := fun parent =>
    sticky.cover.toPaperTubeCover.fiberShadedMass sticky.refined parent
  let externalWeight : Fin sticky.coarse.card → ENNReal := fun parent =>
    if parent ∈ cardinalityBand.selectedParents then
      fiberWeight parent else 0
  have hexternalSum :
      (∑ parent : Fin sticky.coarse.card, externalWeight parent) =
        cardinalityBand.restriction.selectedFineShading.mass := by
    rw [cardinalityBand.restriction.selected_mass_eq_finset]
    simp [externalWeight, fiberWeight]
  have hbandFactorTop :
      ENNReal.ofReal
          (Real.logb 2
            ((sticky.selected.family.card : ℝ) / 1) + 1) ≠ ⊤ := by
    simp
  have hbandFactorPos : 0 <
      ENNReal.ofReal
        (Real.logb 2
          ((sticky.selected.family.card : ℝ) / 1) + 1) := by
    apply ENNReal.ofReal_pos.mpr
    have hcard : (1 : ℝ) ≤
        (sticky.selected.family.card : ℝ) / 1 := by
      norm_num
      exact_mod_cast sticky.selected_nonempty
    have hlog : 0 ≤ Real.logb 2
        ((sticky.selected.family.card : ℝ) / 1) :=
      Real.logb_nonneg (by norm_num) hcard
    linarith
  have hexternalMassLower :
      normalizationWeight * sticky.coarse.enncard ≤
        ∑ parent : Fin sticky.coarse.card, externalWeight parent := by
    rw [hexternalSum]
    have hpositive : 0 < sticky.refined.mass := by
      have hleft : 0 < ENNReal.ofReal
          (Real.logb 2
            ((sticky.selected.family.card : ℝ) / 1) + 1) *
          (normalizationWeight * sticky.coarse.enncard) := by
        apply ENNReal.mul_pos hbandFactorPos.ne'
        exact (ENNReal.mul_pos normalizationWeight_ne_zero (by
          simpa [Kakeya.Streamlined.TubeFamily.enncard] using
            sticky.coarse_extremal.nonempty.ne')).ne'
      exact hleft.trans_le mass_lower
    have hselectedPositive :
        0 < cardinalityBand.restriction.selectedFineShading.mass := by
      by_contra hzero
      have heq :
          cardinalityBand.restriction.selectedFineShading.mass = 0 := by
        simpa [not_lt] using hzero
      have hretained := cardinalityBand.retained_mass
      rw [heq, zero_mul] at hretained
      exact (not_le.mpr hpositive) hretained
    have hscaled :
        (normalizationWeight * sticky.coarse.enncard) *
          ENNReal.ofReal
            (Real.logb 2
              ((sticky.selected.family.card : ℝ) / 1) + 1) ≤
        cardinalityBand.restriction.selectedFineShading.mass *
          ENNReal.ofReal
            (Real.logb 2
              ((sticky.selected.family.card : ℝ) / 1) + 1) := by
      calc
        (normalizationWeight * sticky.coarse.enncard) * ENNReal.ofReal
              (Real.logb 2
                ((sticky.selected.family.card : ℝ) / 1) + 1) =
            ENNReal.ofReal
              (Real.logb 2
                ((sticky.selected.family.card : ℝ) / 1) + 1) *
              (normalizationWeight * sticky.coarse.enncard) := by ring
        _ ≤ sticky.refined.mass := mass_lower
        _ ≤ cardinalityBand.restriction.selectedFineShading.mass *
              ENNReal.ofReal
                (Real.logb 2
                  ((sticky.selected.family.card : ℝ) / 1) + 1) :=
          cardinalityBand.retained_mass
        _ = _ := by ring
    exact (ENNReal.mul_le_mul_iff_left
      hbandFactorPos.ne' hbandFactorTop).mp hscaled
  have hexternalUpper : ∀ parent, externalWeight parent ≤ weightUpper := by
    intro parent
    by_cases hparent : parent ∈ cardinalityBand.selectedParents
    · simp [externalWeight, hparent, fiberWeight, weight_upper parent]
    · simp [externalWeight, hparent]
  rcases schedule.regularizeExternalWeight
      sticky.coarse_extremal.cwa_nearby_scales
      sticky.coarse_extremal.nonempty externalWeight
      normalizationWeight_ne_zero normalizationWeight_ne_top
      weightUpper_ne_top hexternalMassLower hexternalUpper
      output_finite absorb with
    ⟨regularized⟩
  have hsupport : ∀ parent : Fin regularized.selected.family.card,
      regularized.selected.embedding parent ∈
        cardinalityBand.selectedParents := by
    intro parent
    by_contra hnot
    have hzero : externalWeight (regularized.selected.embedding parent) = 0 := by
      simp [externalWeight, hnot]
    have hlower := (regularized.weight_band parent).1
    rw [hzero] at hlower
    exact (not_le.mpr regularized.weightLevel_pos) hlower
  have hselectedIndicesNonempty : regularized.selectedIndices.Nonempty := by
    by_contra hnot
    have hempty : regularized.selectedIndices = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnot
    have hselectedCard : regularized.selected.family.card = 0 := by
      rw [regularized.selected_eq, hempty]
      rfl
    exact (Nat.ne_of_gt regularized.selected_nonempty) hselectedCard
  rcases pure_wz2_section6_complete_parent_restriction sticky.cover sticky.refined
      sticky.refined_cubical regularized.selectedIndices
      hselectedIndicesNonempty with
    ⟨restriction⟩
  have hcoarseEq : restriction.selectedCoarse = regularized.selected := by
    rw [restriction.selectedCoarse_eq, regularized.selected_eq]
  have hselectedFiberBand :
      ∀ parent : Fin regularized.selected.family.card,
        ENNReal.ofReal cardinalityBand.bandLower ≤
            ((sticky.cover.toPaperTubeCover.fiberIndices
              (regularized.selected.embedding parent)).card : ENNReal) ∧
          ((sticky.cover.toPaperTubeCover.fiberIndices
            (regularized.selected.embedding parent)).card : ENNReal) ≤
            ENNReal.ofReal (2 * cardinalityBand.bandLower) := by
    intro parent
    have hmember := hsupport parent
    let member : cardinalityBand.selectedParents :=
      ⟨regularized.selected.embedding parent, hmember⟩
    let bandParent : Fin
        cardinalityBand.restriction.selectedCoarse.family.card :=
      cardinalityBand.restriction.selectedCoarseEquiv.symm member
    have hambient :
        cardinalityBand.restriction.selectedCoarse.embedding bandParent =
          regularized.selected.embedding parent := by
      rw [← cardinalityBand.restriction.selectedCoarseEquiv_val]
      exact congrArg Subtype.val
        (cardinalityBand.restriction.selectedCoarseEquiv.apply_symm_apply
          member)
    have hband := cardinalityBand.fiber_cardinality_band bandParent
    rw [cardinalityBand.restriction.full_fiber_card_eq, hambient] at hband
    exact hband
  have hselectedFineMass :
      restriction.selectedFineShading.mass =
        ∑ parent : Fin regularized.selected.family.card,
          externalWeight (regularized.selected.embedding parent) := by
    rw [restriction.selected_mass_eq_finset]
    rw [show regularized.selectedIndices =
        Finset.image regularized.selected.embedding Finset.univ by
      rw [regularized.selected_eq]
      exact (Finset.image_orderEmbOfFin_univ
        regularized.selectedIndices rfl).symm]
    rw [Finset.sum_image (fun first _ second _ heq =>
      regularized.selected.embedding.injective heq)]
    apply Finset.sum_congr rfl
    intro parent _
    rw [show externalWeight (regularized.selected.embedding parent) =
        fiberWeight (regularized.selected.embedding parent) by
      simp [externalWeight, hsupport parent]]
  have hretainedFine :
      sticky.refined.mass ≤
        (ENNReal.ofReal
            (Real.logb 2
              ((sticky.selected.family.card : ℝ) / 1) + 1) *
          regularized.regularizationLoss) *
            restriction.selectedFineShading.mass := by
    calc
      sticky.refined.mass ≤
          cardinalityBand.restriction.selectedFineShading.mass *
            ENNReal.ofReal
              (Real.logb 2
                ((sticky.selected.family.card : ℝ) / 1) + 1) :=
        cardinalityBand.retained_mass
      _ = (∑ parent : Fin sticky.coarse.card, externalWeight parent) *
          ENNReal.ofReal
            (Real.logb 2
              ((sticky.selected.family.card : ℝ) / 1) + 1) := by
        rw [hexternalSum]
      _ ≤ (regularized.regularizationLoss *
            ∑ parent : Fin regularized.selected.family.card,
              externalWeight (regularized.selected.embedding parent)) *
          ENNReal.ofReal
            (Real.logb 2
              ((sticky.selected.family.card : ℝ) / 1) + 1) := by
        gcongr
        exact regularized.retained_weight
      _ = (ENNReal.ofReal
            (Real.logb 2
              ((sticky.selected.family.card : ℝ) / 1) + 1) *
          regularized.regularizationLoss) *
            restriction.selectedFineShading.mass := by
        rw [hselectedFineMass]
        ring
  exact ⟨{
    cardinalityBand := cardinalityBand
    externalWeight := externalWeight
    externalWeight_eq := fun parent => rfl
    regularized := regularized
    support := hsupport
    restriction := restriction
    restriction_coarse_eq := hcoarseEq
    selected_fiber_band := hselectedFiberBand
    selected_fine_mass_eq := hselectedFineMass
    retained_fine_mass := hretainedFine
  }⟩

/-- The synchronized complete-fiber shading is a genuine restriction of the
original source shading after composing both tube-subfamily embeddings. -/
theorem PureWZ2StickyCoarseFiberMassRegularizationData.restricted_mass_le_source_restrict
    {delta sigma stickyLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent}
    {outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    {schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sticky.coarse)
        (Kakeya.realRpowENN rho.1 (-stickyLoss))
        outputConstant levelCount}
    (data : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) sticky schedule) :
    data.restriction.selectedFineShading.mass ≤
      (restrictPaperShading
        (sticky.selected.comp data.restriction.selectedFine)
        sourceShading).mass := by
  rw [data.restriction.selectedFineShading_eq,
    restrictPaperShading_mass, restrictPaperShading_mass]
  apply Finset.sum_le_sum
  intro index _
  apply measure_mono
  exact sticky.subshading
    (data.restriction.selectedFine.embedding index)

/-- Compose the sticky refinement retention with the complete-fiber
regularizer's retained-mass bound.  This is the exact loss paid when the
original source extremizer is replaced by the synchronized selected fine
shading. -/
theorem PureWZ2StickyCoarseFiberMassRegularizationData.source_mass_retained
    {delta sigma stickyLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent}
    {outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    {schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sticky.coarse)
        (Kakeya.realRpowENN rho.1 (-stickyLoss))
        outputConstant levelCount}
    (data : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) sticky schedule)
    (hdelta : 0 < delta)
    (hdeltaLtOne : delta < 1) :
    ((wz2PaperPureRefinementFraction delta logExponent)⁻¹ *
        (ENNReal.ofReal
            (Real.logb 2
              ((sticky.selected.family.card : ℝ) / 1) + 1) *
          data.regularized.regularizationLoss))⁻¹ *
        sourceShading.mass ≤
      data.restriction.selectedFineShading.mass := by
  let fraction := wz2PaperPureRefinementFraction delta logExponent
  let selectedLoss := ENNReal.ofReal
      (Real.logb 2
        ((sticky.selected.family.card : ℝ) / 1) + 1) *
    data.regularized.regularizationLoss
  have fractionZero : fraction ≠ 0 := by
    exact wz1PaperRefinementFraction_ne_zero
      hdelta hdeltaLtOne logExponent
  have fractionTop : fraction ≠ ⊤ := by
    exact wz1PaperRefinementFraction_ne_top
      hdelta hdeltaLtOne logExponent
  have selectedLossZero : selectedLoss ≠ 0 := by
    dsimp only [selectedLoss]
    apply mul_ne_zero
    · apply (ENNReal.ofReal_pos.mpr ?_).ne'
      have cardOne : (1 : ℝ) ≤
          (sticky.selected.family.card : ℝ) / 1 := by
        norm_num
        exact_mod_cast sticky.selected_nonempty
      have logNonnegative : 0 ≤ Real.logb 2
          ((sticky.selected.family.card : ℝ) / 1) :=
        Real.logb_nonneg (by norm_num) cardOne
      linarith
    · rw [data.regularized.regularizationLoss_eq]
      apply mul_ne_zero (by norm_num)
      exact pow_ne_zero _ (by norm_num)
  have selectedLossTop : selectedLoss ≠ ⊤ := by
    dsimp only [selectedLoss]
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    rw [data.regularized.regularizationLoss_eq]
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top (by simp))
  have sourceToRefined : sourceShading.mass ≤
      fraction⁻¹ * sticky.refined.mass := by
    calc
      sourceShading.mass =
          (fraction⁻¹ * fraction) * sourceShading.mass := by
        rw [ENNReal.inv_mul_cancel fractionZero fractionTop, one_mul]
      _ = fraction⁻¹ * (fraction * sourceShading.mass) := by ring
      _ ≤ fraction⁻¹ * sticky.refined.mass := by
        gcongr
        exact sticky.retained_mass
  have combined : sourceShading.mass ≤
      (fraction⁻¹ * selectedLoss) *
        data.restriction.selectedFineShading.mass := by
    calc
      sourceShading.mass ≤ fraction⁻¹ * sticky.refined.mass :=
        sourceToRefined
      _ ≤ fraction⁻¹ *
          (selectedLoss * data.restriction.selectedFineShading.mass) := by
        gcongr
        exact data.retained_fine_mass
      _ = (fraction⁻¹ * selectedLoss) *
          data.restriction.selectedFineShading.mass := by ring
  have totalZero : fraction⁻¹ * selectedLoss ≠ 0 :=
    mul_ne_zero (ENNReal.inv_ne_zero.mpr fractionTop) selectedLossZero
  have totalTop : fraction⁻¹ * selectedLoss ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr fractionZero) selectedLossTop
  have scaled := mul_le_mul_left' combined
    (fraction⁻¹ * selectedLoss)⁻¹
  rw [show (fraction⁻¹ * selectedLoss)⁻¹ *
      ((fraction⁻¹ * selectedLoss) *
        data.restriction.selectedFineShading.mass) =
      ((fraction⁻¹ * selectedLoss)⁻¹ *
        (fraction⁻¹ * selectedLoss)) *
          data.restriction.selectedFineShading.mass by ring,
    ENNReal.inv_mul_cancel totalZero totalTop, one_mul] at scaled
  exact scaled

/-- Source top-level CWA transfers to the synchronized complete fine
restriction.  Every selection loss is displayed in the output constant. -/
theorem PureWZ2StickyCoarseFiberMassRegularizationData.restricted_fine_top_level_cwa
    {delta sigma sourceLoss stickyLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent}
    {outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    {schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sticky.coarse)
        (Kakeya.realRpowENN rho.1 (-stickyLoss))
        outputConstant levelCount}
    (data : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) sticky schedule)
    (sourceExtremal :
      WZ2PaperCroppedIsExtremal
        sigma sourceLoss source sourceShading)
    (sourceLine : WZ1PaperIsLineClass source)
    (hdeltaSmall : delta ≤ 1 / 24)
    (C : ENNReal)
    (sourceCWA : WZ2PaperConvexWolffBound source C) :
    WZ2PaperConvexWolffBound
      data.restriction.selectedFine.family
      (((Kakeya.realRpowENN delta sourceLoss)⁻¹ *
          ((wz2PaperPureRefinementFraction delta logExponent)⁻¹ *
            (ENNReal.ofReal
                (Real.logb 2
                  ((sticky.selected.family.card : ℝ) / 1) + 1) *
              data.regularized.regularizationLoss) *
            (55296 * Kakeya.deltaTubeVolume 1))) * C) := by
  let density : ENNReal := Kakeya.realRpowENN delta sourceLoss
  let fraction : ENNReal :=
    wz2PaperPureRefinementFraction delta logExponent
  let selectionLoss : ENNReal :=
    ENNReal.ofReal
        (Real.logb 2
          ((sticky.selected.family.card : ℝ) / 1) + 1) *
      data.regularized.regularizationLoss
  let geometryConstant : ENNReal :=
    55296 * Kakeya.deltaTubeVolume 1
  let totalLoss : ENNReal := fraction⁻¹ * selectionLoss
  let composed := sticky.selected.comp data.restriction.selectedFine
  have hdeltaStrict : delta < 1 := by linarith
  have hfractionZero : fraction ≠ 0 := by
    change wz1PaperRefinementFraction delta logExponent ≠ 0
    exact wz1PaperRefinementFraction_ne_zero
      sourceExtremal.delta_pos hdeltaStrict logExponent
  have hfractionTop : fraction ≠ ⊤ := by
    change wz1PaperRefinementFraction delta logExponent ≠ ⊤
    exact wz1PaperRefinementFraction_ne_top
      sourceExtremal.delta_pos hdeltaStrict logExponent
  have hdensityZero : density ≠ 0 := by
    simp [density, Kakeya.realRpowENN,
      Real.rpow_pos_of_pos sourceExtremal.delta_pos]
  have hdensityTop : density ≠ ⊤ := by
    simp [density, Kakeya.realRpowENN]
  have hbody : Kakeya.realRpowENN delta 2 * source.enncard ≤
      (wz1PaperBodyFamily source).mass :=
    PureWZ2.paperBodyFamily_mass_lower_rpow_two
      sourceExtremal.delta_pos
      (hdeltaSmall.trans (by norm_num)) sourceLine
  have hambientMass : density * source.enncard *
      Kakeya.realRpowENN delta 2 ≤ sourceShading.mass := by
    calc
      density * source.enncard * Kakeya.realRpowENN delta 2 =
          density * (Kakeya.realRpowENN delta 2 * source.enncard) := by
        ring
      _ ≤ density * (wz1PaperBodyFamily source).mass := by gcongr
      _ ≤ sourceShading.mass := sourceExtremal.dense
  have hsourceToRefined :
      sourceShading.mass ≤ fraction⁻¹ * sticky.refined.mass := by
    calc
      sourceShading.mass =
          (fraction⁻¹ * fraction) * sourceShading.mass := by
        rw [ENNReal.inv_mul_cancel hfractionZero hfractionTop, one_mul]
      _ = fraction⁻¹ * (fraction * sourceShading.mass) := by ring
      _ ≤ fraction⁻¹ * sticky.refined.mass := by
        gcongr
        exact sticky.retained_mass
  have hretained : sourceShading.mass ≤
      totalLoss * (restrictPaperShading composed sourceShading).mass := by
    calc
      sourceShading.mass ≤ fraction⁻¹ * sticky.refined.mass :=
        hsourceToRefined
      _ ≤ fraction⁻¹ *
          (selectionLoss * data.restriction.selectedFineShading.mass) := by
        gcongr
        exact data.retained_fine_mass
      _ = totalLoss * data.restriction.selectedFineShading.mass := by
        simp only [totalLoss]
        ring
      _ ≤ totalLoss *
          (restrictPaperShading composed sourceShading).mass := by
        gcongr
        exact data.restricted_mass_le_source_restrict
  have hcardinality : density * source.enncard ≤
      (totalLoss * geometryConstant) * composed.family.enncard := by
    simpa [geometryConstant] using
      wz2PaperWeightedCardinality_retained_from_subfamily_mass
        sourceExtremal.delta_pos hdeltaSmall sourceLine
        sourceShading composed density totalLoss hambientMass hretained
  change WZ2PaperConvexWolffBound composed.family
    (((Kakeya.realRpowENN delta sourceLoss)⁻¹ *
        ((wz2PaperPureRefinementFraction delta logExponent)⁻¹ *
          (ENNReal.ofReal
              (Real.logb 2
                ((sticky.selected.family.card : ℝ) / 1) + 1) *
            data.regularized.regularizationLoss) *
          (55296 * Kakeya.deltaTubeVolume 1))) * C)
  simpa [density, fraction, selectionLoss, totalLoss, geometryConstant] using
    sourceCWA.subfamily_of_weighted_cardinality
      composed hdensityZero hdensityTop hcardinality

/-- The factor-two original fine-fiber band transfers any top-level CWA on
the complete selected fine restriction to the synchronized selected coarse
family. -/
theorem PureWZ2StickyCoarseFiberMassRegularizationData.selected_coarse_top_level_cwa
    {delta sigma stickyLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent}
    {outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    {schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sticky.coarse)
        (Kakeya.realRpowENN rho.1 (-stickyLoss))
        outputConstant levelCount}
    (data : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) sticky schedule)
    (hdelta : 0 < delta)
    (hscale : 6 * delta ≤ rho.1)
    (C : ENNReal)
    (fineCWA : WZ2PaperConvexWolffBound
      data.restriction.selectedFine.family C) :
    WZ2PaperConvexWolffBound data.regularized.selected.family (2 * C) := by
  let cover := data.restriction.restrictedCover.toPaperTubeCover
  have hfiberUniform :
      ∀ first second : Fin data.restriction.selectedCoarse.family.card,
        ((cover.fiberIndices first).card : ENNReal) ≤
          2 * ((cover.fiberIndices second).card : ENNReal) := by
    intro first second
    have hfirstCard := data.restriction.full_fiber_card_eq first
    have hsecondCard := data.restriction.full_fiber_card_eq second
    have hfirstBand :
        ENNReal.ofReal data.cardinalityBand.bandLower ≤
            ((sticky.cover.toPaperTubeCover.fiberIndices
              (data.restriction.selectedCoarse.embedding first)).card :
              ENNReal) ∧
          ((sticky.cover.toPaperTubeCover.fiberIndices
            (data.restriction.selectedCoarse.embedding first)).card :
            ENNReal) ≤
              ENNReal.ofReal (2 * data.cardinalityBand.bandLower) := by
      have hfirstMem :
          data.restriction.selectedCoarse.embedding first ∈
            data.regularized.selectedIndices :=
        data.restriction.selectedCoarse_embedding_mem first
      rcases data.regularized.selected_embedding_surjective
          _ hfirstMem with ⟨regularizedFirst, hembedding⟩
      simpa [hembedding] using data.selected_fiber_band regularizedFirst
    have hsecondBand :
        ENNReal.ofReal data.cardinalityBand.bandLower ≤
            ((sticky.cover.toPaperTubeCover.fiberIndices
              (data.restriction.selectedCoarse.embedding second)).card :
              ENNReal) ∧
          ((sticky.cover.toPaperTubeCover.fiberIndices
            (data.restriction.selectedCoarse.embedding second)).card :
            ENNReal) ≤
              ENNReal.ofReal (2 * data.cardinalityBand.bandLower) := by
      have hsecondMem :
          data.restriction.selectedCoarse.embedding second ∈
            data.regularized.selectedIndices :=
        data.restriction.selectedCoarse_embedding_mem second
      rcases data.regularized.selected_embedding_surjective
          _ hsecondMem with ⟨regularizedSecond, hembedding⟩
      simpa [hembedding] using data.selected_fiber_band regularizedSecond
    rw [hfirstCard, hsecondCard]
    calc
      ((sticky.cover.toPaperTubeCover.fiberIndices
        (data.restriction.selectedCoarse.embedding first)).card : ENNReal) ≤
          ENNReal.ofReal (2 * data.cardinalityBand.bandLower) :=
        hfirstBand.2
      _ = 2 * ENNReal.ofReal data.cardinalityBand.bandLower := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ ≤ 2 *
          ((sticky.cover.toPaperTubeCover.fiberIndices
            (data.restriction.selectedCoarse.embedding second)).card :
            ENNReal) := by
        gcongr
        exact hsecondBand.1
  have hcoarseCWA : WZ2PaperConvexWolffBound
      data.restriction.selectedCoarse.family (2 * C) := by
    apply paperConvexWolffBound_of_uniform_cover
        cover.parent cover.parent_surjective (fun fineIndex => ?_)
        2 C hfiberUniform fineCWA
    exact wz2PaperTubeCarrierCovers_of_strict_cover
      hdelta sticky.coarse_extremal.delta_pos hscale
      (data.restriction.restrictedCover.fine_line_class fineIndex)
      (data.restriction.restrictedCover.coarse_line_class
        (cover.parent fineIndex))
      (cover.parent_covers fineIndex)
  rw [data.restriction_coarse_eq] at hcoarseCWA
  exact hcoarseCWA

/-- Assemble cropped extremality on the synchronized selected coarse family.
The density cost is exactly the fine-mass selection loss times the frozen
fiber-multiplicity cap; all power absorption remains explicit. -/
theorem PureWZ2StickyCoarseFiberMassRegularizationData.selected_coarse_extremal
    {delta sigma stickyLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent}
    {outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    {schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sticky.coarse)
        (Kakeya.realRpowENN rho.1 (-stickyLoss))
        outputConstant levelCount}
    (data : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) sticky schedule)
    (hdelta : 0 < delta)
    (hloss : stickyLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hnearby : outputConstant ≤
      Kakeya.realRpowENN rho.1 (-outputLoss))
    (hselectedBodyBudget :
      ((ENNReal.ofReal
          (Real.logb 2
            ((sticky.selected.family.card : ℝ) / 1) + 1) *
        data.regularized.regularizationLoss) *
          (Kakeya.realRpowENN (delta / rho.1)
            (2 - sigma - stickyLoss) *
            ENNReal.ofReal (2 * data.cardinalityBand.bandLower))) *
        (Kakeya.realRpowENN rho.1 outputLoss *
          (wz1PaperBodyFamily data.regularized.selected.family).mass) ≤
        sticky.refined.mass) :
    WZ2PaperCroppedIsExtremal sigma outputLoss
      data.regularized.selected.family
      (restrictPaperShading data.regularized.selected
        sticky.croppedCoarseShading) := by
  let selectedCoarseShading :=
    restrictPaperShading data.regularized.selected
      sticky.croppedCoarseShading
  have hrho : 0 < rho.1 := sticky.coarse_extremal.delta_pos
  have hrhoOne : rho.1 ≤ 1 := sticky.coarse_extremal.delta_le_one
  have houtputFinite : WZ2PaperFiniteErrorConstant
      (Kakeya.realRpowENN rho.1 (-outputLoss)) := by
    have hone : (1 : ENNReal) ≤
        Kakeya.realRpowENN rho.1 (-outputLoss) := by
      have hreal : 1 ≤ Real.rpow rho.1 (-outputLoss) := by
        have hzero : Real.rpow rho.1 0 ≤
            Real.rpow rho.1 (-outputLoss) :=
          Real.rpow_le_rpow_of_exponent_ge hrho hrhoOne (by linarith)
        simpa using hzero
      simpa [Kakeya.realRpowENN] using ENNReal.ofReal_mono hreal
    exact ⟨hone, by simp [Kakeya.realRpowENN]⟩
  have hcwaNearby : WZ2PaperPureCWAAtNearbyScales
      data.regularized.selected.family
      (Kakeya.realRpowENN rho.1 (-outputLoss)) :=
    weaken_cwa_nearby_scales data.regularized.pure_cwa_nearby
      hnearby houtputFinite
  have hcubical : WZ1PaperIsCubicalShading selectedCoarseShading :=
    restrictPaperShading_cubical data.regularized.selected
      sticky.balanced.coarse_cubical
  have hvolume : volume selectedCoarseShading.union ≤
      Kakeya.realRpowENN rho.1 (sigma - outputLoss) := by
    have hunion : selectedCoarseShading.union ⊆
        sticky.croppedCoarseShading.union := by
      rintro point ⟨parent, hpoint⟩
      exact ⟨data.regularized.selected.embedding parent, hpoint⟩
    calc
      volume selectedCoarseShading.union ≤
          volume sticky.croppedCoarseShading.union := measure_mono hunion
      _ ≤ Kakeya.realRpowENN rho.1 (sigma - stickyLoss) :=
        sticky.coarse_extremal.volume_upper
      _ ≤ Kakeya.realRpowENN rho.1 (sigma - outputLoss) := by
        apply ENNReal.ofReal_mono
        exact Real.rpow_le_rpow_of_exponent_ge hrho hrhoOne (by linarith)
  have hfiberCap : ∀ parent point,
      (data.restriction.restrictedCover.toPaperTubeCover
          |>.fiberPointMultiplicity
            data.restriction.selectedFineShading parent point : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho.1)
            (2 - sigma - stickyLoss) *
          ENNReal.ofReal (2 * data.cardinalityBand.bandLower) := by
    intro parent point
    rw [data.restriction.full_fiber_pointMultiplicity_eq]
    rw [← sticky.cover.fullFiberPointMultiplicity_eq]
    have hmultiplicity := sticky.fiber_multiplicity_upper
      (data.restriction.selectedCoarse.embedding parent) point
    exact hmultiplicity.trans <| by
      gcongr
      have hparentMem : data.restriction.selectedCoarse.embedding parent ∈
          data.regularized.selectedIndices :=
        data.restriction.selectedCoarse_embedding_mem parent
      rcases data.regularized.selected_embedding_surjective
          _ hparentMem with ⟨regularizedParent, hembedding⟩
      have hcard := (data.selected_fiber_band regularizedParent).2
      rw [hembedding] at hcard
      rw [sticky.cover.fullFiberIndices_eq]
      exact hcard
  have hfineToCoarse : data.restriction.selectedFineShading.mass ≤
      (Kakeya.realRpowENN (delta / rho.1)
          (2 - sigma - stickyLoss) *
        ENNReal.ofReal (2 * data.cardinalityBand.bandLower)) *
          (restrictPaperShading data.restriction.selectedCoarse
            sticky.croppedCoarseShading).mass := by
    exact data.restriction.restrictedCover.toPaperTubeCover
      |>.fine_mass_le_fiberCap_mul_coarse_mass
        data.restriction.selectedFineShading
        (restrictPaperShading data.restriction.selectedCoarse
          sticky.croppedCoarseShading)
        (data.restriction.point_compatibility sticky.balanced) hfiberCap
  have hselectedCoarseMass :
      (restrictPaperShading data.restriction.selectedCoarse
        sticky.croppedCoarseShading).mass = selectedCoarseShading.mass := by
    rw [data.restriction_coarse_eq]
  rw [hselectedCoarseMass] at hfineToCoarse
  have hdense : Kakeya.realRpowENN rho.1 outputLoss *
      (wz1PaperBodyFamily data.regularized.selected.family).mass ≤
        selectedCoarseShading.mass := by
    let selectionLoss : ENNReal :=
      ENNReal.ofReal
          (Real.logb 2
            ((sticky.selected.family.card : ℝ) / 1) + 1) *
        data.regularized.regularizationLoss
    let fiberCap : ENNReal :=
      Kakeya.realRpowENN (delta / rho.1)
          (2 - sigma - stickyLoss) *
        ENNReal.ofReal (2 * data.cardinalityBand.bandLower)
    have hselectedMass : sticky.refined.mass ≤
        (selectionLoss * fiberCap) * selectedCoarseShading.mass := by
      calc
        sticky.refined.mass ≤ selectionLoss *
            data.restriction.selectedFineShading.mass :=
          data.retained_fine_mass
        _ ≤ selectionLoss * (fiberCap * selectedCoarseShading.mass) := by
          gcongr
        _ = (selectionLoss * fiberCap) * selectedCoarseShading.mass := by
          ring
    have hselectionLossPos : 0 < selectionLoss := by
      dsimp only [selectionLoss]
      apply ENNReal.mul_pos
      · exact (ENNReal.ofReal_pos.mpr (by
        have hcard : (1 : ℝ) ≤
            (sticky.selected.family.card : ℝ) / 1 := by
          norm_num
          exact_mod_cast sticky.selected_nonempty
        have hlog : 0 ≤ Real.logb 2
            ((sticky.selected.family.card : ℝ) / 1) :=
          Real.logb_nonneg (by norm_num) hcard
        linarith)).ne'
      · rw [data.regularized.regularizationLoss_eq]
        apply mul_ne_zero (by norm_num)
        exact pow_ne_zero _ (by norm_num)
    have hselectionLossTop : selectionLoss ≠ ⊤ := by
      dsimp only [selectionLoss]
      apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      rw [data.regularized.regularizationLoss_eq]
      exact ENNReal.mul_ne_top (by norm_num)
        (ENNReal.pow_ne_top (by simp))
    have hfiberCapPos : 0 < fiberCap := by
      dsimp only [fiberCap]
      apply ENNReal.mul_pos
      · exact (ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos (div_pos hdelta hrho) _)).ne'
      · exact (ENNReal.ofReal_pos.mpr (by
          linarith [data.cardinalityBand.bandLower_pos])).ne'
    have hfiberCapTop : fiberCap ≠ ⊤ := by
      dsimp only [fiberCap]
      exact ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN])
        ENNReal.ofReal_ne_top
    have hcostZero : selectionLoss * fiberCap ≠ 0 :=
      mul_ne_zero hselectionLossPos.ne' hfiberCapPos.ne'
    have hcostTop : selectionLoss * fiberCap ≠ ⊤ :=
      ENNReal.mul_ne_top hselectionLossTop hfiberCapTop
    have hbudget : (selectionLoss * fiberCap) *
        (Kakeya.realRpowENN rho.1 outputLoss *
          (wz1PaperBodyFamily data.regularized.selected.family).mass) ≤
        sticky.refined.mass := by
      simpa [selectionLoss, fiberCap] using hselectedBodyBudget
    have hscaled : (selectionLoss * fiberCap) *
        (Kakeya.realRpowENN rho.1 outputLoss *
          (wz1PaperBodyFamily data.regularized.selected.family).mass) ≤
        (selectionLoss * fiberCap) * selectedCoarseShading.mass :=
      hbudget.trans hselectedMass
    exact (ENNReal.mul_le_mul_iff_right hcostZero hcostTop).mp hscaled
  exact {
    delta_pos := hrho
    delta_le_one := hrhoOne
    nonempty := data.regularized.selected_nonempty
    cwa_nearby_scales := hcwaNearby
    cubical := hcubical
    dense := hdense
    volume_upper := hvolume
  }

end Kakeya.Assouad

end
