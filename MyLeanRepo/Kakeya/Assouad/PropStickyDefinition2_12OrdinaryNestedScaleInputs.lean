import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryNestedLocalization
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryRescaledLocality
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PreparedOneParentPureSchedule

/-!
# Inputs for one ordinary nested pure scale

This module extracts the line-cover, parent-anchor, strong-separation, and
localization inputs consumed by the ordinary nested-scale producer.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Dependent-cover core used by the scale-data wrapper below. -/
private theorem
    wz2PaperPureInternal_parent_covers_of_coarse_cover_heq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {pureCoarse internalCoarse :
      Kakeya.Streamlined.TubeFamily rho}
    {pureCover :
      WZ2PaperPurePartitioningCover fine pureCoarse}
    {internalCover :
      WZ2PaperPartitioningCover fine internalCoarse}
    (synchronization :
      WZ2PaperPureInternalCoverSynchronization
        fine internalCoarse internalCover)
    (coarse_eq : pureCoarse = internalCoarse)
    (cover_eq :
      HEq pureCover synchronization.publicCover) :
    ∀ source,
      WZ1PaperTubeCovers
        (fine.tube source)
        (pureCoarse.tube (pureCover.parent source)) := by
  subst internalCoarse
  rw [heq_iff_eq] at cover_eq
  intro source
  rw [cover_eq, synchronization.parent_eq source]
  exact internalCover.parent_covers source

/--
Synchronization with an aligned internal exact-scale cover exposes the
internal strict line cover at the parent selected by the pure cover.
-/
theorem WZ2PaperPureScaleCoverData.parent_covers_of_internalSynchronization
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {scale : Kakeya.Streamlined.AdmissibleScale delta}
    {pureConstant internalConstant : ENNReal}
    (pureScale :
      WZ2PaperPureScaleCoverData fine scale.1 pureConstant)
    (internalScale :
      WZ2PaperScaleCoverData fine scale internalConstant)
    (synchronization :
      WZ2PaperPureInternalCoverSynchronization
        fine internalScale.coarse internalScale.cover)
    (coarse_eq : pureScale.coarse = internalScale.coarse)
    (cover_eq :
      HEq pureScale.cover synchronization.publicCover) :
    ∀ source,
      WZ1PaperTubeCovers
        (fine.tube source)
        (pureScale.coarse.tube (pureScale.cover.parent source)) := by
  exact
    wz2PaperPureInternal_parent_covers_of_coarse_cover_heq
      synchronization coarse_eq cover_eq

/--
Every surjective coarse parent is within the factor-two line-cover relation
of a common anchor once its fine child is strictly covered by both.
-/
theorem WZ2PaperScaleCoverData.coarse_parent_dilated_covers_anchor
    {delta sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actual : Kakeya.Streamlined.AdmissibleScale delta}
    {C : ENNReal}
    (data : WZ2PaperScaleCoverData fine actual C)
    (anchor : Kakeya.DeltaTube sigma)
    (hactualSigma : actual.1 ≤ sigma)
    (hFineAnchor :
      ∀ source, WZ1PaperTubeCovers (fine.tube source) anchor) :
    ∀ parent,
      WZ2PaperDilatedTubeCovers 2
        (data.coarse.tube parent) anchor := by
  intro parent
  rcases data.cover.parent_surjective parent with ⟨source, hsource⟩
  have hparent := data.cover.parent_covers source
  rw [hsource] at hparent
  have hanchor := hFineAnchor source
  have htriangle :=
    wz1PaperLineDistance_triangle
      (data.coarse.tube parent) (fine.tube source) anchor
  have hsymmetry :
      wz1PaperLineDistance
          (data.coarse.tube parent) (fine.tube source) =
        wz1PaperLineDistance
          (fine.tube source) (data.coarse.tube parent) :=
    wz1PaperLineDistance_symm _ _
  rw [hsymmetry] at htriangle
  unfold WZ1PaperTubeCovers at hparent hanchor
  unfold WZ2PaperDilatedTubeCovers
  linarith

/-- The four inputs consumed by the ordinary nested-scale producer. -/
structure WZ2PaperPreparedOneParentOrdinaryNestedScaleInputs
    {delta sigma sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (aligned :
      WZ2PaperAlignedPureExactSource
        sigma sourceLoss source shading)
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (parent : Fin prepared.callerStrict.coarse.card)
    (selection :
      WZ2PaperPreparedOneParentSelectionData prepared parent)
    (quantitative :
      WZ2PaperPreparedOneParentQuantitativeData
        prepared parent selection)
    (restrictedConstant : ENNReal)
    (restricted :
      WZ2PaperPreparedOneParentRestrictedScheduleData
        prepared parent selection restrictedConstant)
    (pureSchedule :
      WZ2PaperPreparedOneParentPureScheduleData
        aligned prepared parent selection quantitative
          restrictedConstant restricted)
    (coordinate :
      Fin (wz2PaperPreparedOneParentFineScaleCount
        prepared parent)) where
  hFineMiddle :
    ∀ sourceIndex,
      WZ1PaperTubeCovers
        (selection.refinement.selected.family.tube sourceIndex)
        ((pureSchedule.pureScale coordinate).coarse.tube
          ((pureSchedule.pureScale coordinate).cover.parent sourceIndex))
  hMiddleAnchor :
    ∀ middleParent,
      WZ2PaperDilatedTubeCovers 2
        ((pureSchedule.pureScale coordinate).coarse.tube middleParent)
        (prepared.callerStrict.coarse.tube parent)
  hMiddleSeparated :
    ∀ first second, first ≠ second →
      wz2PaperLiteralSourceSeparationFactor *
            (prepared.strictScale
              (wz2PaperPreparedOneParentFineCoordinate
                prepared parent coordinate)).1 <
        wz1PaperLineDistance
          ((pureSchedule.pureScale coordinate).coarse.tube first)
          ((pureSchedule.pureScale coordinate).coarse.tube second)
  localization :
    WZ2PaperOrdinaryNestedTargetLocalization
      selection.refinement.selected.family
      (pureSchedule.pureScale coordinate).coarse
      (prepared.callerStrict.coarse.tube parent)
      prepared.callerStrict.rho_pos

/--
Package all ordinary nested-scale inputs at one tail coordinate.

The scale comparison is explicit because the pure schedule records the
chosen exact scale and its cover provenance, but not its numerical order
relative to the caller scale.
-/
noncomputable def
    WZ2PaperPreparedOneParentPureScheduleData.ordinaryNestedScaleInputs
    {delta sigma sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {aligned :
      WZ2PaperAlignedPureExactSource
        sigma sourceLoss source shading}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    {parent : Fin prepared.callerStrict.coarse.card}
    {selection :
      WZ2PaperPreparedOneParentSelectionData prepared parent}
    {quantitative :
      WZ2PaperPreparedOneParentQuantitativeData
        prepared parent selection}
    {restrictedConstant : ENNReal}
    {restricted :
      WZ2PaperPreparedOneParentRestrictedScheduleData
        prepared parent selection restrictedConstant}
    (pureSchedule :
      WZ2PaperPreparedOneParentPureScheduleData
        aligned prepared parent selection quantitative
          restrictedConstant restricted)
    (coordinate :
      Fin (wz2PaperPreparedOneParentFineScaleCount
        prepared parent))
    (hactualCaller :
      (prepared.strictScale
        (wz2PaperPreparedOneParentFineCoordinate
          prepared parent coordinate)).1 ≤ caller.1) :
    WZ2PaperPreparedOneParentOrdinaryNestedScaleInputs
      aligned prepared parent selection quantitative
        restrictedConstant restricted pureSchedule coordinate := by
  let selected := selection.refinement.selected
  let callerFiber := wz2PaperPreparedOneParentFiber prepared parent
  let pureScale := pureSchedule.pureScale coordinate
  let internalScale := restricted.scaleData coordinate
  let anchor := prepared.callerStrict.coarse.tube parent
  have hFineMiddle :
      ∀ sourceIndex,
        WZ1PaperTubeCovers
          (selected.family.tube sourceIndex)
          (pureScale.coarse.tube
            (pureScale.cover.parent sourceIndex)) :=
    pureScale.parent_covers_of_internalSynchronization
      internalScale (pureSchedule.synchronization coordinate)
      (pureSchedule.coarse_eq coordinate)
      (pureSchedule.cover_eq coordinate)
  have hFineAnchor :
      ∀ sourceIndex,
        WZ1PaperTubeCovers
          (selected.family.tube sourceIndex) anchor := by
    intro sourceIndex
    have hcovered :=
      prepared.callerStrict.cover.fullFiberSubfamily_covered parent
        (selected.embedding sourceIndex)
    simpa [selected, callerFiber, anchor,
      wz2PaperPreparedOneParentFiber, selected.tube_eq] using hcovered
  have hMiddleAnchorInternal :
      ∀ middleParent,
        WZ2PaperDilatedTubeCovers 2
          (internalScale.coarse.tube middleParent) anchor :=
    internalScale.coarse_parent_dilated_covers_anchor
      anchor hactualCaller hFineAnchor
  have hMiddleAnchor :
      ∀ middleParent,
        WZ2PaperDilatedTubeCovers 2
          (pureScale.coarse.tube middleParent) anchor := by
    rw [pureSchedule.coarse_eq coordinate]
    exact hMiddleAnchorInternal
  have hMiddleSeparated :
      ∀ first second, first ≠ second →
        wz2PaperLiteralSourceSeparationFactor *
              (prepared.strictScale
                (wz2PaperPreparedOneParentFineCoordinate
                  prepared parent coordinate)).1 <
          wz1PaperLineDistance
            (pureScale.coarse.tube first)
            (pureScale.coarse.tube second) := by
    rw [pureSchedule.coarse_eq coordinate]
    exact restricted.coarse_strongly_separated coordinate
  have hSelectedLine : WZ1PaperIsLineClass selected.family :=
    (prepared.cwa_nearby.2.1.subfamily callerFiber).subfamily selected
  have hAnchorLine : WZ1PaperTubeInLineClass anchor :=
    prepared.callerStrict.coarse_line_class parent
  have hMiddleLine : WZ1PaperIsLineClass pureScale.coarse := by
    rw [pureSchedule.coarse_eq coordinate]
    exact internalScale.coarse_line_class
  have hPreparedUnit :
      prepared.refinement.selected.family.IsInUnitBall :=
    wz2PaperTubeSubfamily_isInUnitBall
      prepared.refinement.selected aligned.unit_ball
  have hFiberUnit : callerFiber.family.IsInUnitBall :=
    wz2PaperTubeSubfamily_isInUnitBall callerFiber hPreparedUnit
  have hSelectedUnit : selected.family.IsInUnitBall :=
    wz2PaperTubeSubfamily_isInUnitBall selected hFiberUnit
  have hTargetFineLocal :
      ∀ target,
        ‖wz2PaperTubeMidpoint
          ((wz2PaperLiteralOrdinaryRescaledFamily
            selected.family anchor
            prepared.callerStrict.rho_pos).tube target)‖ ≤ 3 := by
    intro target
    exact
      wz2PaperLiteralOrdinaryRescaledTube_midpoint_norm_le_three
        prepared.delta_pos prepared.callerStrict.rho_pos caller.2.2
        (selected.family.tube target) anchor
        (hSelectedUnit target) (hSelectedLine target)
        (hFineAnchor target)
  refine
    {
      hFineMiddle := hFineMiddle
      hMiddleAnchor := hMiddleAnchor
      hMiddleSeparated := hMiddleSeparated
      localization := ?_
    }
  exact
    wz2PaperOrdinaryNestedTargetLocalization_of_sourceCovers
      prepared.delta_pos pureScale.rho_pos
      prepared.callerStrict.rho_pos caller.2.2
      selected.family pureScale.coarse anchor
      hSelectedLine hMiddleLine hAnchorLine
      hFineAnchor hMiddleAnchor hTargetFineLocal

end Kakeya.Assouad

end
