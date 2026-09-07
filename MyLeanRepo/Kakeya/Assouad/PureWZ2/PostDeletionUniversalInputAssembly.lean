import MyLeanRepo.Kakeya.Assouad.PureWZ2.ActualFiberWeightUpper
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CallerGeometricSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyPositiveParentDeletion
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationTopLevelAssembly
import MyLeanRepo.Kakeya.Assouad.ExtremalInfrastructure

/-!
# Universal same-family post-deletion input assembly

For one normalized cropped source and one arbitrary caller-requested scale,
this module constructs every dependent object before the final quantitative
leaves:

* an actual nearby-scale witness;
* the quotient-net caller cover and its positive support;
* a caller-relative coordinate schedule;
* simultaneous complete-fiber regularization and its merged family;
* the same-family caller selection;
* fixed-origin balancing;
* positive whole-parent deletion.

The genuinely scalar and geometric premises are concentrated in
`PureWZ2PostDeletionUniversalConstructionWitness`.  The output record contains
no final coarse-density, coarse-volume, multiplicity-cap, or rescaled-fiber
leaf.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The canonical per-actual-fiber mass bound used by the regularizer. -/
def pureWZ2PostDeletionActualWeightUpper (delta : ℝ) : ENNReal :=
  (55296 * Kakeya.deltaTubeVolume 1) *
    Kakeya.realRpowENN delta 2

/--
The caller-relative requested scales used simultaneously by complete-parent
regularization and the later same-family caller selection.
-/
def pureWZ2PostDeletionRequestedSchedule
    {delta epsilon : ℝ}
    (hdelta : 0 < delta)
    (caller : WZ2PaperRequestedScale delta)
    (callerLtOne : caller.1 < 1)
    (epsilonPos : 0 < epsilon)
    (coordinate :
      Fin (geometricScaleCount epsilon)) :
    WZ2PaperRequestedScale delta :=
  pureWZ2CallerGeometricRequestedScales
    caller (hdelta.trans_le caller.2.1) callerLtOne epsilonPos
    (geometricScaleCount epsilon) coordinate

/--
Choose the ambient Definition 2.12 witness at every canonical caller-relative
requested scale.
-/
noncomputable def pureWZ2PostDeletionNearbySchedule
    {delta epsilon : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (caller : WZ2PaperRequestedScale delta)
    (callerLtOne : caller.1 < 1)
    (epsilonPos : 0 < epsilon)
    (coordinate :
      Fin (geometricScaleCount epsilon)) :
    WZ2PaperPureNearbyScaleCoverData
      fine
      (pureWZ2PostDeletionRequestedSchedule
        ambient.1 caller callerLtOne epsilonPos coordinate)
      ambientConstant :=
  pureWZ2CallerGeometricScheduled
    ambient caller (ambient.1.trans_le caller.2.1) callerLtOne epsilonPos
    (geometricScaleCount epsilon) coordinate

/--
The exact scalar leaf needed by caller-class regularization.  The degree and
retention constants are the formulas actually produced by the finite
selection; only the runtime caller normalization weight remains quantified.
-/
def PureWZ2PostDeletionActualFormulaRestrictionAbsorption
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent)
    (actualRequested callerRequested : WZ2PaperRequestedScale delta)
    (scheduleEpsilon : ℝ)
    (fiberConstant : ENNReal) : Prop :=
  ∀ (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        normalized.croppedFamily actualRequested
        (Kakeya.realRpowENN delta (-normalizationLoss)))
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested normalized.croppedRefined)
    (parent :
      Fin (quotient.callerCover.hitParentSubfamily
        quotient.positiveCallerFine).family.card),
      wz2PaperPureNearbyRestrictionConstant
          (Kakeya.realRpowENN delta (-normalizationLoss))
          (quotient.callerActualWeight
              ((quotient.callerCover.hitParentSubfamily
                quotient.positiveCallerFine).embedding parent) *
            normalized.croppedFamily.enncard⁻¹)
          (max (Kakeya.realRpowENN delta (-normalizationLoss))
            (Kakeya.realRpowENN delta (-normalizationLoss) *
              pureWZ2CompleteParentDegreeConstant
                actualNearby.scaleData.coarse.card
                (geometricScaleCount scheduleEpsilon)))
          (pureWZ2CompleteParentRegularizationLoss
              actualNearby.scaleData.coarse.card
              (geometricScaleCount scheduleEpsilon) *
            pureWZ2PostDeletionActualWeightUpper delta) ≤
        fiberConstant

/--
The non-mechanical boundary of the post-deletion construction.

Every field is either a scalar absorption, a scale-separation fact, a bounded
cropped-source fact, or the geometric input to the closed balancing
constructor.  All families, subfamilies, covers, supports, regularizations,
and deletions are constructed below.
-/
structure PureWZ2PostDeletionUniversalConstructionWitness
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent)
    (callerRequested : WZ2PaperRequestedScale delta)
    (deletionExponent : ℕ) where
  actualRequested : WZ2PaperRequestedScale delta
  cropped_mass_pos : 0 < normalized.croppedRefined.mass
  cropped_base_bound :
    ∀ index, ‖(normalized.croppedFamily.tube index).base‖ ≤ 5
  actual_small :
    ∀ actualNearby :
        WZ2PaperPureNearbyScaleCoverData
          normalized.croppedFamily actualRequested
          (Kakeya.realRpowENN delta (-normalizationLoss)),
      actualNearby.rho ≤ 1 / 10000
  actual_to_caller :
    ∀ actualNearby :
        WZ2PaperPureNearbyScaleCoverData
          normalized.croppedFamily actualRequested
          (Kakeya.realRpowENN delta (-normalizationLoss)),
      2400000 * actualNearby.rho ≤ callerRequested.1
  scheduleEpsilon : ℝ
  scheduleEpsilon_pos : 0 < scheduleEpsilon
  caller_lt_one : callerRequested.1 < 1
  schedule_gap :
    ∀ (actualNearby :
        WZ2PaperPureNearbyScaleCoverData
          normalized.croppedFamily actualRequested
          (Kakeya.realRpowENN delta (-normalizationLoss)))
      (coordinate : Fin (geometricScaleCount scheduleEpsilon)),
        4 *
              ((pureWZ2PostDeletionNearbySchedule
                normalized.final_extremal.cwa_nearby_scales
                callerRequested caller_lt_one scheduleEpsilon_pos
                coordinate).rho - delta) ≤
            actualNearby.rho ∨
          4 * (actualNearby.rho - delta) ≤
            (pureWZ2PostDeletionNearbySchedule
              normalized.final_extremal.cwa_nearby_scales
              callerRequested caller_lt_one scheduleEpsilon_pos
              coordinate).rho
  regularizationConstant : ENNReal
  regularizationConstant_pos : 0 < regularizationConstant
  regularizationConstant_ne_top : regularizationConstant ≠ ⊤
  regularizationConstant_one : 1 ≤ regularizationConstant
  fiberConstant : ENNReal
  fiberConstant_ne_top : fiberConstant ≠ ⊤
  regularization_rounding :
    ∀ requested : WZ2PaperRequestedScale delta,
      ∃ coordinate : Fin (geometricScaleCount scheduleEpsilon),
        requested.1 ≤
            (pureWZ2PostDeletionRequestedSchedule
              normalized.final_extremal.delta_pos callerRequested
              caller_lt_one scheduleEpsilon_pos coordinate).1 ∧
          ENNReal.ofReal
              (pureWZ2PostDeletionRequestedSchedule
                normalized.final_extremal.delta_pos callerRequested
                caller_lt_one scheduleEpsilon_pos coordinate).1 <
            regularizationConstant * ENNReal.ofReal requested.1
  regularization_window_absorption :
    regularizationConstant *
        Kakeya.realRpowENN delta (-normalizationLoss) ≤
      fiberConstant
  regularization_restriction_absorption :
    PureWZ2PostDeletionActualFormulaRestrictionAbsorption
      normalized actualRequested callerRequested scheduleEpsilon fiberConstant
  coarseConstant : ENNReal
  coarseConstant_one : 1 ≤ coarseConstant
  coarseConstant_ne_top : coarseConstant ≠ ⊤
  caller_rounding_absorption :
    (19 : ENNReal) *
          Kakeya.realRpowENN delta (-normalizationLoss) *
          ENNReal.ofReal
            (Real.rpow callerRequested.1 (-scheduleEpsilon)) ≤
      coarseConstant
  same_family_scale_absorption :
    ∀ (actualNearby :
        WZ2PaperPureNearbyScaleCoverData
          normalized.croppedFamily actualRequested
          (Kakeya.realRpowENN delta (-normalizationLoss)))
      (quotient :
        PureWZ2ParentQuotientNetSelectionData
          actualNearby callerRequested normalized.croppedRefined)
      (coordinate : Fin (geometricScaleCount scheduleEpsilon)),
        max
            (pureWZ2FiniteCallerCenterDegreeConstant
              (geometricScaleCount scheduleEpsilon)
              (quotient.callerCover.hitParentSubfamily
                quotient.positiveCallerFine).family.card)
            ((27 : ENNReal) *
              Kakeya.deltaTubeVolume
                (19 *
                  (pureWZ2PostDeletionNearbySchedule
                    normalized.final_extremal.cwa_nearby_scales
                    callerRequested caller_lt_one scheduleEpsilon_pos
                    coordinate).rho) *
              (Kakeya.deltaTubeVolume callerRequested.1)⁻¹) ≤
          coarseConstant
  scale_separation : 18 * delta ≤ callerRequested.1
  fixed_balancing_input :
    ∀ (actualNearby :
        WZ2PaperPureNearbyScaleCoverData
          normalized.croppedFamily actualRequested
          (Kakeya.realRpowENN delta (-normalizationLoss)))
      (quotient :
        PureWZ2ParentQuotientNetSelectionData
          actualNearby callerRequested normalized.croppedRefined)
      (support : PureWZ2PositiveCallerSupportData quotient)
      (regularized :
        PureWZ2AllPositiveCallerRegularizationData
          (outputConstant := fiberConstant)
          actualNearby quotient support
          (geometricScaleCount scheduleEpsilon))
      (merged :
        PureWZ2MergedCallerClassRegularizationData
          actualNearby quotient support
          (geometricScaleCount scheduleEpsilon) regularized)
      (sameFamily :
        PureWZ2SameFamilyCallerNearbyAssemblyData
          (coarseConstant := coarseConstant)
          actualNearby quotient support
          (geometricScaleCount scheduleEpsilon) regularized merged
          (pureWZ2PostDeletionRequestedSchedule
            normalized.final_extremal.delta_pos callerRequested
            caller_lt_one scheduleEpsilon_pos)
          (pureWZ2PostDeletionNearbySchedule
            normalized.final_extremal.cwa_nearby_scales
            callerRequested caller_lt_one scheduleEpsilon_pos))
      (scaleSeparation : 18 * delta ≤ callerRequested.1),
        WZ2PaperDirectGeometricInputData
          (sameFamily.pullback.internalPartitioningCover scaleSeparation)
          sameFamily.pullback.selectedFineShading
          actualNearby.scaleData.delta_pos
          (actualNearby.scaleData.delta_pos.trans_le
            callerRequested.2.1)
  deletion_fraction_small :
    wz1PaperRefinementFraction delta deletionExponent ≤
      (1 / 2 : ENNReal)

/--
All dependent objects on the same-family route through positive deletion.
This is the input expected by the separate final quantitative-leaf assembly.
-/
structure PureWZ2CroppedPostDeletionUniversalInput
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent)
    (callerRequested : WZ2PaperRequestedScale delta)
    (deletionExponent : ℕ) where
  actualRequested : WZ2PaperRequestedScale delta
  actualNearby :
    WZ2PaperPureNearbyScaleCoverData
      normalized.croppedFamily actualRequested
      (Kakeya.realRpowENN delta (-normalizationLoss))
  quotient :
    PureWZ2ParentQuotientNetSelectionData
      actualNearby callerRequested normalized.croppedRefined
  support : PureWZ2PositiveCallerSupportData quotient
  scheduleEpsilon : ℝ
  scheduleEpsilon_pos : 0 < scheduleEpsilon
  caller_lt_one : callerRequested.1 < 1
  fiberConstant : ENNReal
  coordinateCount : ℕ
  coordinateCount_eq :
    coordinateCount = geometricScaleCount scheduleEpsilon
  scales : Fin coordinateCount → WZ2PaperRequestedScale delta
  scheduled :
    ∀ coordinate,
      WZ2PaperPureNearbyScaleCoverData
        normalized.croppedFamily (scales coordinate)
        (Kakeya.realRpowENN delta (-normalizationLoss))
  regularized :
    PureWZ2AllPositiveCallerRegularizationData
      (outputConstant := fiberConstant)
      actualNearby quotient support coordinateCount
  merged :
    PureWZ2MergedCallerClassRegularizationData
      actualNearby quotient support coordinateCount regularized
  coarseConstant : ENNReal
  sameFamily :
    PureWZ2SameFamilyCallerNearbyAssemblyData
      (coarseConstant := coarseConstant)
      actualNearby quotient support coordinateCount regularized merged
      scales scheduled
  scaleSeparation : 18 * delta ≤ callerRequested.1
  fixedBalancing :
    PureWZ2SameFamilyFixedOriginBalancingData
      actualNearby quotient support coordinateCount regularized merged
      scales scheduled sameFamily scaleSeparation
  positiveDeletion :
    PureWZ2SameFamilyPositiveParentDeletionData
      actualNearby quotient support coordinateCount regularized merged
      scales scheduled sameFamily scaleSeparation fixedBalancing
      deletionExponent

/--
Run the closed constructors in dependency order.  No final quantitative leaf
is used.
-/
theorem pureWZ2_cropped_post_deletion_universal_input
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent deletionExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent)
    (callerRequested : WZ2PaperRequestedScale delta)
    (witness :
      PureWZ2PostDeletionUniversalConstructionWitness
        normalized callerRequested deletionExponent) :
    Nonempty
      (PureWZ2CroppedPostDeletionUniversalInput
        normalized callerRequested deletionExponent) := by
  let ambient :=
    normalized.final_extremal.cwa_nearby_scales
  let actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        normalized.croppedFamily witness.actualRequested
        (Kakeya.realRpowENN delta (-normalizationLoss)) :=
    Classical.choice <|
      ambient.2.2.2 witness.actualRequested
  let quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested normalized.croppedRefined :=
    Classical.choice <|
      pure_wz2_parent_quotient_net_selection
        actualNearby callerRequested normalized.croppedRefined
        normalized.final_extremal.nonempty witness.cropped_mass_pos
        normalized.line_class witness.cropped_base_bound
        (witness.actual_small actualNearby)
        (witness.actual_to_caller actualNearby)
  have selectedMassPos : 0 < quotient.selectedShading.mass := by
    by_contra hmass
    have selectedMassZero :
        quotient.selectedShading.mass = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp hmass)
    have retained := quotient.retained_mass
    rw [selectedMassZero, mul_zero] at retained
    exact (not_le_of_gt witness.cropped_mass_pos) retained
  let support : PureWZ2PositiveCallerSupportData quotient :=
    Classical.choice <|
      positive_caller_support quotient selectedMassPos
  let coordinateCount := geometricScaleCount witness.scheduleEpsilon
  have coordinateCountPos : 0 < coordinateCount := by
    dsimp only [coordinateCount, geometricScaleCount]
    omega
  let scales : Fin coordinateCount → WZ2PaperRequestedScale delta :=
    pureWZ2PostDeletionRequestedSchedule
      normalized.final_extremal.delta_pos callerRequested
      witness.caller_lt_one witness.scheduleEpsilon_pos
  let scheduled :
      ∀ coordinate : Fin coordinateCount,
        WZ2PaperPureNearbyScaleCoverData
          normalized.croppedFamily (scales coordinate)
          (Kakeya.realRpowENN delta (-normalizationLoss)) :=
    pureWZ2PostDeletionNearbySchedule
      ambient callerRequested witness.caller_lt_one
      witness.scheduleEpsilon_pos
  have deltaSmall : delta ≤ 1 / 24 := by
    have deltaActual : delta ≤ actualNearby.rho :=
      witness.actualRequested.2.1.trans actualNearby.requested_le
    exact deltaActual.trans <|
      (witness.actual_small actualNearby).trans (by norm_num)
  have weightUpper_ne_top :
      pureWZ2PostDeletionActualWeightUpper delta ≠ ⊤ := by
    exact
      ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num)
          deltaTubeVolume_one_ne_top)
        ENNReal.ofReal_ne_top
  have actualWeightUpper :
      ∀ actualParent,
        pureWZ2ActualFiberShadedMass
            normalized.croppedRefined actualParent ≤
          pureWZ2PostDeletionActualWeightUpper delta *
            wz2PaperOrdinaryFullFiberCount
              normalized.croppedFamily
              actualNearby.scaleData.coarse actualParent := by
    intro actualParent
    exact
      pureWZ2_actual_fiber_shaded_mass_upper
        normalized.final_extremal.delta_pos deltaSmall
        normalized.line_class normalized.croppedRefined actualParent
  have scaleGap :
      ∀ coordinate : Fin coordinateCount,
        4 * ((scheduled coordinate).rho - delta) ≤
            actualNearby.rho ∨
          4 * (actualNearby.rho - delta) ≤
            (scheduled coordinate).rho := by
    intro coordinate
    simpa [scheduled, ambient, coordinateCount] using
      witness.schedule_gap actualNearby coordinate
  let regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := witness.fiberConstant)
        actualNearby quotient support coordinateCount :=
    Classical.choice <|
      all_positive_caller_schedule_regularization
        ambient actualNearby quotient support
        normalized.final_extremal.nonempty
        (pureWZ2PostDeletionActualWeightUpper delta)
        weightUpper_ne_top actualWeightUpper
        coordinateCount coordinateCountPos scales scheduled scaleGap
        witness.regularizationConstant_pos
        witness.regularizationConstant_ne_top
        witness.regularizationConstant_one
        (by
          intro requested
          simpa [scales, coordinateCount] using
            witness.regularization_rounding requested)
        witness.regularization_window_absorption
        witness.fiberConstant_ne_top
        (witness.regularization_restriction_absorption
          actualNearby quotient)
  let merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized :=
    Classical.choice <|
      merge_caller_class_regularizations
        actualNearby quotient support coordinateCount regularized
        normalized.final_extremal.nonempty
  have callerScheduled :
      ∀ coordinate : Fin coordinateCount,
        callerRequested.1 ≤ (scheduled coordinate).rho := by
    intro coordinate
    change
      callerRequested.1 ≤
        (pureWZ2CallerGeometricScheduled
          ambient callerRequested
          (ambient.1.trans_le callerRequested.2.1)
          witness.caller_lt_one witness.scheduleEpsilon_pos
          (geometricScaleCount witness.scheduleEpsilon)
          coordinate).rho
    exact
      pureWZ2CallerGeometricScheduled_caller_le
        ambient callerRequested
        (normalized.final_extremal.delta_pos.trans_le
          callerRequested.2.1)
        witness.caller_lt_one witness.scheduleEpsilon_pos
        (geometricScaleCount witness.scheduleEpsilon) coordinate
  have callerRounding :
      ∀ requested : WZ2PaperRequestedScale callerRequested.1,
        ∃ coordinate : Fin coordinateCount,
          requested.1 ≤ 19 * (scheduled coordinate).rho ∧
          ENNReal.ofReal (19 * (scheduled coordinate).rho) <
            witness.coarseConstant * ENNReal.ofReal requested.1 := by
    intro requested
    change
      ∃ coordinate : Fin (geometricScaleCount witness.scheduleEpsilon),
        requested.1 ≤
            19 *
              (pureWZ2CallerGeometricScheduled
                ambient callerRequested
                (ambient.1.trans_le callerRequested.2.1)
                witness.caller_lt_one witness.scheduleEpsilon_pos
                (geometricScaleCount witness.scheduleEpsilon)
                coordinate).rho ∧
          ENNReal.ofReal
              (19 *
                (pureWZ2CallerGeometricScheduled
                  ambient callerRequested
                  (ambient.1.trans_le callerRequested.2.1)
                  witness.caller_lt_one witness.scheduleEpsilon_pos
                  (geometricScaleCount witness.scheduleEpsilon)
                  coordinate).rho) <
            witness.coarseConstant * ENNReal.ofReal requested.1
    exact
      pureWZ2_caller_geometric_scheduled_rounding
        ambient callerRequested
        (normalized.final_extremal.delta_pos.trans_le
          callerRequested.2.1)
        witness.caller_lt_one witness.scheduleEpsilon_pos
        (rfl :
          geometricScaleCount witness.scheduleEpsilon =
            geometricScaleCount witness.scheduleEpsilon)
        witness.caller_rounding_absorption requested
  let sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := witness.coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled :=
    Classical.choice <|
      pureWZ2_same_family_caller_nearby_assembly
        actualNearby quotient support coordinateCount coordinateCountPos
        regularized merged normalized.final_extremal.nonempty
        normalized.ordinary_bounded_base witness.cropped_mass_pos
        scales scheduled callerScheduled
        witness.coarseConstant_one witness.coarseConstant_ne_top
        (by
          intro coordinate
          simpa [scheduled, ambient, coordinateCount] using
            witness.same_family_scale_absorption
              actualNearby quotient coordinate)
        callerRounding
  have scaleSeparation : 18 * delta ≤ callerRequested.1 :=
    witness.scale_separation
  let fixedBalancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation :=
    Classical.choice <|
      pureWZ2_same_family_fixed_origin_balancing
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation
        (by
          simpa [scales, scheduled, ambient, coordinateCount] using
            witness.fixed_balancing_input
              actualNearby quotient support regularized merged
              sameFamily scaleSeparation)
  let positiveDeletion :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation fixedBalancing
        deletionExponent :=
    Classical.choice <|
      pureWZ2_same_family_positive_parent_deletion
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation fixedBalancing
        deletionExponent witness.deletion_fraction_small
  exact
    ⟨{
      actualRequested := witness.actualRequested
      actualNearby := actualNearby
      quotient := quotient
      support := support
      scheduleEpsilon := witness.scheduleEpsilon
      scheduleEpsilon_pos := witness.scheduleEpsilon_pos
      caller_lt_one := witness.caller_lt_one
      fiberConstant := witness.fiberConstant
      coordinateCount := coordinateCount
      coordinateCount_eq := rfl
      scales := scales
      scheduled := scheduled
      regularized := regularized
      merged := merged
      coarseConstant := witness.coarseConstant
      sameFamily := sameFamily
      scaleSeparation := scaleSeparation
      fixedBalancing := fixedBalancing
      positiveDeletion := positiveDeletion
    }⟩

/--
The concentrated construction leaf with exactly the quantifier order of
`PureWZ2CroppedPropStickyUniversalLeafAt`.
-/
def PureWZ2CroppedPostDeletionUniversalLeafAt
    (normalizationExponent deletionExponent : ℕ) : Prop :=
  ∀ sigma : ℝ,
    ∀ critical : PureWZ2CriticalPackage sigma,
    ∀ outputLoss : ℝ, 0 < outputLoss →
      ∃ delta₀ : ℝ,
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ source :
              PureWZ2ExtremalConfiguration
                sigma outputLoss delta,
            ∀ normalized :
                PureWZ2CroppedCriticalNormalizationData
                  (outputLoss := outputLoss)
                  source normalizationExponent,
                ∀ rho : WZ2PaperRequestedScale delta,
                  Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                  rho.1 ≤ Real.rpow delta outputLoss →
                    Nonempty
                      (PureWZ2CroppedPostDeletionUniversalInput
                        normalized rho deletionExponent)

/--
It is enough to produce the concentrated scalar/geometric witness in the
same universal quantifier order; the dependent objects are then assembled
mechanically.
-/
def PureWZ2PostDeletionUniversalConstructionWitnessLeafAt
    (normalizationExponent deletionExponent : ℕ) : Prop :=
  ∀ sigma : ℝ,
    ∀ critical : PureWZ2CriticalPackage sigma,
    ∀ outputLoss : ℝ, 0 < outputLoss →
      ∃ delta₀ : ℝ,
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ source :
              PureWZ2ExtremalConfiguration
                sigma outputLoss delta,
            ∀ normalized :
                PureWZ2CroppedCriticalNormalizationData
                  (outputLoss := outputLoss)
                  source normalizationExponent,
                ∀ rho : WZ2PaperRequestedScale delta,
                  Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                  rho.1 ≤ Real.rpow delta outputLoss →
                    Nonempty
                      (PureWZ2PostDeletionUniversalConstructionWitness
                        normalized rho deletionExponent)

theorem pureWZ2_cropped_post_deletion_universal_leaf_of_construction_witness
    (normalizationExponent deletionExponent : ℕ)
    (leaf :
      PureWZ2PostDeletionUniversalConstructionWitnessLeafAt
        normalizationExponent deletionExponent) :
    PureWZ2CroppedPostDeletionUniversalLeafAt
      normalizationExponent deletionExponent := by
  intro sigma critical outputLoss outputLossPos
  rcases leaf sigma critical outputLoss outputLossPos with
    ⟨delta₀, delta₀Pos, delta₀One, produce⟩
  refine ⟨delta₀, delta₀Pos, delta₀One, ?_⟩
  intro delta deltaPos deltaSmall source normalized rho rhoLower rhoUpper
  rcases
      produce delta deltaPos deltaSmall source normalized rho
        rhoLower rhoUpper
    with
    ⟨witness⟩
  exact
    pureWZ2_cropped_post_deletion_universal_input
      normalized rho witness

end Kakeya.Assouad

end
