import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CallerParameterSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentStrongSeparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientFinalRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientFiberCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientMetricFiberUniformity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientUpperGeometryConstruction

/-!
# Proposition 6.2 metric-parent V4 certificate

This is the statement-independent terminal certificate consumed by the
paper-facing Target 3 wrapper.  It records only the final refinement, genuine
metric cover, strong separation of the final coarse family, parent nearby
CWA, canonical rescaled-fiber inputs and nearby CWA, and the two metric-parent
conclusions.

The module does not import the V4 statement file.  Cleanup is represented only
through an already constructed quotient metric-core output and its provenance
equalities; no cleanup theorem is called here.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
Statement-independent terminal data for the V4 metric-parent result.

The separate field `fine` and its equality with the refinement family retain
the exact provenance needed to transport this record into the dependent V4
output without making another family choice.
-/
structure PureWZ2Prop62MetricParentsV4Certificate
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading source)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (c0 : ℝ)
    (parentConstant fiberConstant : ENNReal) where
  rho_pos : 0 < rho.1
  c0_pos : 0 < c0
  refinement : WZ1PaperRefinement shading 10
  fine : Kakeya.Streamlined.TubeFamily delta
  refinement_selected_family_eq :
    refinement.selected.family = fine
  refined_nonempty : refinement.selected.family.Nonempty
  refined_cubical : WZ1PaperIsCubicalShading refinement.refined
  coarse : Kakeya.Streamlined.TubeFamily rho.1
  coarse_centered :
    ∀ parent,
      wz2PaperCenteredLineTube (targetScale := rho.1)
          (coarse.tube parent) =
        coarse.tube parent
  section6Cover : PureWZ2Section6Cover fine coarse
  cover : WZ1PaperTubeCover fine coarse
  cover_eq :
    cover = section6Cover.toWZ1PaperTubeCover
  full_fiber_uniform :
    ∀ first second,
      wz2PaperFullFiberCount fine coarse first ≤
        parentConstant * wz2PaperFullFiberCount fine coarse second
  coarse_cwa :
    WZ2PaperPureCWAAtNearbyScales coarse parentConstant
  coarse_strongly_separated :
    ∀ first second, first ≠ second →
      1600 * rho.1 <
        wz1PaperLineDistance
          (coarse.tube first) (coarse.tube second)
  sourceFiberConstant : ENNReal
  fiberConstant_eq :
    fiberConstant = (81000000 : ENNReal) * sourceFiberConstant
  fiber_rescaling :
    ∀ parent : Fin coarse.card,
      PureWZ2Prop62MetricFiberRescalingInput
        section6Cover parent sourceFiberConstant
  fiber_public_cwa :
    ∀ parent : Fin coarse.card,
      WZ2PaperPureCWAAtNearbyScales
        (fiber_rescaling parent).certificate.publicFamily
        fiberConstant
  metric_fiber :
    ∀ sourceIndex parent,
      cover.parent sourceIndex = parent ↔
        wz1PaperLineDistance
            (fine.tube sourceIndex)
            (coarse.tube parent) ≤
          rho.1 / 2
  fine_parent_close :
    ∀ sourceIndex,
      wz1PaperLineDistance
          (fine.tube sourceIndex)
          (coarse.tube (cover.parent sourceIndex)) ≤
        c0 * rho.1

theorem pureWZ2_prop62_metric_parents_v4_certificate
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading source)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (c0 : ℝ)
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        source ambientConstant scaleWindow)
    (sourceNonempty : source.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule sourceNonempty)
    (packetCoordinate : Fin schedule.levelCount)
    (weight : Fin source.card → ENNReal)
    (parameters :
      PureWZ2Prop62CallerParameterData c0 rho.1)
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho.1) schedule sourceNonempty quotient
          parameters.width packetCoordinate parameters.strideBase weight)
    {SourceColor : Type*}
    [Fintype SourceColor] [DecidableEq SourceColor]
    [Nonempty SourceColor]
    {coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho.1 packetCoordinate}
    {sourceColor : Fin source.card → SourceColor}
    (preCore :
      PureWZ2Prop62ProxyQuotientPreCoreAdapterData
        schedule sourceNonempty quotient parameters.width packetCoordinate
        parameters.strideBase weight metricCore.metric coloring
        SourceColor sourceColor)
    (preliminary_eq :
      metricCore.cleanup.preliminary = preCore.preCore.preliminary)
    (finalRefinement :
      PureWZ2Prop62ProxyQuotientFinalRefinementData
        shading metricCore)
    (parentConstant sourceFiberConstant fiberConstant Λ : ENNReal)
    (coarseCWA :
      WZ2PaperPureCWAAtNearbyScales
        metricCore.restriction.coarseSelected.family parentConstant)
    (fiberCWA :
      PureWZ2Prop62ProxyQuotientFiberCWAData
        metricCore sourceFiberConstant)
    (fiberConstant_eq :
      fiberConstant = (81000000 : ENNReal) * sourceFiberConstant)
    (fineLine : WZ1PaperIsLineClass source)
    (fineBase : ∀ index, ‖(source.tube index).base‖ ≤ 5)
    (packetScaleLt :
      schedule.actualScale packetCoordinate < rho.1 / parameters.K)
    (densityLoss_le :
      metricCore.quotientDensityLoss ≤ Λ)
    (uniformity_absorption :
      2 * Λ ≤ parentConstant)
    :
    Nonempty
      (PureWZ2Prop62MetricParentsV4Certificate
        shading rho c0 parentConstant fiberConstant) := by
  let fine := metricCore.restriction.fineSelected.family
  let coarse := metricCore.restriction.coarseSelected.family
  let section6Cover := metricCore.restriction.section6Cover
  let cover := section6Cover.toWZ1PaperTubeCover
  have KOne : 1 ≤ parameters.K := by
    rw [parameters.K_eq, pureWZ2Prop62CallerK,
      ← parameters.theta_eq]
    rw [le_div_iff₀ parameters.theta_pos]
    nlinarith [parameters.theta_le_one]
  have packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho.1 :=
    packetScaleLt.le.trans <|
      div_le_self parameters.rho_pos.le KOne
  have rawUniform :
      ∀ first second,
        wz2PaperFullFiberCount fine coarse first ≤
          (2 * Λ) * wz2PaperFullFiberCount fine coarse second := by
    exact
      metricCore.finalMetricFullFibers_uniform
        preCore preliminary_eq fineLine fineBase parameters.rho_pos
        parameters.width_pos packetScaleLeRho parameters.six_width_le
        Λ densityLoss_le
  have fullFiberUniform :
      ∀ first second,
        wz2PaperFullFiberCount fine coarse first ≤
          parentConstant * wz2PaperFullFiberCount fine coarse second := by
    intro first second
    exact (rawUniform first second).trans <| by
      gcongr
  have fiberPublicCWA :
      ∀ parent : Fin coarse.card,
        WZ2PaperPureCWAAtNearbyScales
          (fiberCWA.input parent).certificate.publicFamily
          fiberConstant := by
    intro parent
    rw [fiberConstant_eq]
    exact fiberCWA.public_cwa parent
  have coarseStronglySeparated :
      ∀ first second, first ≠ second →
        1600 * rho.1 <
          wz1PaperLineDistance
            (coarse.tube first) (coarse.tube second) := by
    exact
      metricCore.finalMetricParents_strongly_separated
        fineLine parameters.width_pos
          parameters.literal_strong_separation
  have metricFiber :
      ∀ sourceIndex parent,
        cover.parent sourceIndex = parent ↔
          wz1PaperLineDistance
              (fine.tube sourceIndex)
              (coarse.tube parent) ≤
            rho.1 / 2 := by
    intro sourceIndex parent
    change
      cover.parent sourceIndex = parent ↔
        WZ1PaperTubeCovers
          (fine.tube sourceIndex) (coarse.tube parent)
    constructor
    · intro parentEq
      rw [← parentEq]
      exact cover.parent_covers sourceIndex
    · intro covered
      exact (cover.parent_unique sourceIndex parent covered).symm
  have fineParentClose :
      ∀ sourceIndex,
        wz1PaperLineDistance
            (fine.tube sourceIndex)
            (coarse.tube (cover.parent sourceIndex)) ≤
          c0 * rho.1 := by
    intro sourceIndex
    let selectedSource :=
      metricCore.restriction.fineSelected.embedding sourceIndex
    let oldParent :=
      metricCore.metric.mesh.restrictedOldData.cover.parent selectedSource
    have sourceInOldFiber :
        selectedSource ∈
          wz2PaperOrdinaryFullFiberIndices
            metricCore.metric.selectedFine
            metricCore.metric.mesh.restrictedOldData.coarse oldParent :=
      metricCore.metric.mesh.restrictedOldData.cover
        |>.parent_mem_fullFiber selectedSource
    have close :=
      parameters.fine_parent_close
        (packetScale := schedule.actualScale packetCoordinate)
        rfl packetScaleLt metricCore.metric oldParent selectedSource
        sourceInOldFiber
    have finalParentCovers :
        WZ1PaperTubeCovers
          (metricCore.metric.selectedFine.tube selectedSource)
          (metricCore.metric.metricParents.tube
            (metricCore.restriction.coarseSelected.embedding
              (cover.parent sourceIndex))) := by
      have localCover := cover.parent_covers sourceIndex
      simpa only [fine, coarse, selectedSource,
        metricCore.restriction.fineSelected.tube_eq,
        metricCore.restriction.coarseSelected.tube_eq] using localCover
    have finalParentEq :
        metricCore.restriction.coarseSelected.embedding
            (cover.parent sourceIndex) =
          metricCore.metric.metricInput.packetParent oldParent := by
      calc
        metricCore.restriction.coarseSelected.embedding
            (cover.parent sourceIndex) =
            metricCore.metric.section6Cover.toWZ1PaperTubeCover.parent
              selectedSource :=
          metricCore.metric.section6Cover.toWZ1PaperTubeCover
            |>.parent_unique selectedSource
              (metricCore.restriction.coarseSelected.embedding
                (cover.parent sourceIndex))
              finalParentCovers
        _ = metricCore.metric.metricInput.packetParent oldParent := by
          exact
            metricCore.metric.metricInput.section6_parent_eq_packetParent
              selectedSource
    simpa only [fine, coarse, selectedSource,
      metricCore.restriction.fineSelected.tube_eq,
      metricCore.restriction.coarseSelected.tube_eq,
      finalParentEq] using close
  exact
    ⟨{
      rho_pos := parameters.rho_pos
      c0_pos := parameters.theta_pos.trans_le parameters.theta_le_c0
      refinement := finalRefinement.refinement
      fine := fine
      refinement_selected_family_eq :=
        finalRefinement.selected_family_eq
      refined_nonempty := finalRefinement.selected_nonempty
      refined_cubical := finalRefinement.refined_cubical
      coarse := coarse
      coarse_centered := by
        intro parent
        rw [metricCore.restriction.coarseSelected.tube_eq]
        exact
          metricCore.upperGeometry_metricParents_centered
            fineLine
            (metricCore.restriction.coarseSelected.embedding parent)
      section6Cover := section6Cover
      cover := cover
      cover_eq := rfl
      full_fiber_uniform := fullFiberUniform
      coarse_cwa := coarseCWA
      coarse_strongly_separated := coarseStronglySeparated
      sourceFiberConstant := sourceFiberConstant
      fiberConstant_eq := fiberConstant_eq
      fiber_rescaling := fiberCWA.input
      fiber_public_cwa := fiberPublicCWA
      metric_fiber := metricFiber
      fine_parent_close := fineParentClose
    }⟩

end Kakeya.Assouad

end
