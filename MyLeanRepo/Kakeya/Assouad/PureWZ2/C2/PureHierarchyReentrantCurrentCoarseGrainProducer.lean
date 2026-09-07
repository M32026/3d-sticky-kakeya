import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantSynchronizedOwnerProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PaperADSixDeltaPerturbation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADTransport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ExtremalCWATransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SourceWitnessCoarseMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicADTransfer

/-!
# Current-grain transport to the exact first coarse overlay

The first sticky coarse shading is not a subshading of the supplied current
shading: it is indexed by a different, coarser tube family.  Consequently the
same-family `restrict` operations for global and local grains do not apply.

This module first replaces the coarse shading by its canonical honest
source-witness refinement.  That refinement has the same spatial union as the
first coarse shading, but every retained parent-cell membership has a genuine
fine source witness.  The only remaining input is then the geometric
transport receipt below:

* target global projections are within `6 * rho` of current same-height
  projections;
* target local projections are within `6 * R` of current local projections
  at every queried radius `R`;
* the transported plane field is unit, one-Lipschitz, incident to the honest
  coarse memberships, and retains the vertical bound.

No grain configuration, Proposition 6.3 output, same-extremizer restoration,
or family-valued callback is accepted.  From this geometric receipt all AD,
extremality, CWA, volume, and slope fields of the requested grain refinement
are constructed below.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- Indexed-mass price of replacing the exact first coarse shading by its
honest source-witness refinement. -/
def pureWZ2HierarchyReentrantCurrentCoarseMultiplicityLoss
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    (firstOverlay : PureWZ2HierarchyReentrantFirstOverlayReceipt
      (current := current) kernelOutput) : ENNReal :=
  Kakeya.realRpowENN kernelOutput.requested.1
      (2 - sigma - lossSchedule.ownerSchedule.stickyLoss) *
    firstOverlay.ambient.coarse.enncard

/-- Exact whole-cell provenance furnished by the first owner call.

Every point of the honest coarse reconstruction is paired with a point of the
first ambient fine refinement in the same literal `rho`-cell.  The latter is
then embedded into the supplied current shading through the *actual*
`ambient.data.subshading`; no same-family identification of the fine and
coarse families is made. -/
structure PureWZ2HierarchyReentrantCurrentCoarseSourceProvenance
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    (firstOverlay : PureWZ2HierarchyReentrantFirstOverlayReceipt
      (current := current) kernelOutput) where
  sourceWitness :
    PureWZ2.PureWZ2SourceWitnessCoarseShadingData
      firstOverlay.ambient.data.balanced
  sourcePoint :
    {point : Point3 // point ∈ sourceWitness.shading.union} →
      {point : Point3 // point ∈ current.grain.shading.union}
  sourcePoint_mem_refined :
    ∀ point, (sourcePoint point : Point3) ∈
      firstOverlay.ambient.data.refined.union
  sourcePoint_same_cell :
    ∀ point,
      wz1PaperGridIndex kernelOutput.requested.1 (sourcePoint point : Point3) =
        wz1PaperGridIndex kernelOutput.requested.1 (point : Point3)
  sourcePoint_dist_lt :
    ∀ point, dist (sourcePoint point : Point3) (point : Point3) <
      2 * kernelOutput.requested.1

namespace PureWZ2HierarchyReentrantCurrentCoarseSourceProvenance

variable
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    {firstOverlay : PureWZ2HierarchyReentrantFirstOverlayReceipt
      (current := current) kernelOutput}

/-- The supplied current normal sampled at the honest source point. -/
noncomputable def sourceNormal
    (provenance :
      PureWZ2HierarchyReentrantCurrentCoarseSourceProvenance firstOverlay)
    (point : {point : Point3 // point ∈ provenance.sourceWitness.shading.union}) :
    Point3 :=
  current.grain.localGrains.planeMap (provenance.sourcePoint point)

theorem sourceNormal_unit
    (provenance :
      PureWZ2HierarchyReentrantCurrentCoarseSourceProvenance firstOverlay)
    (point : {point : Point3 // point ∈ provenance.sourceWitness.shading.union}) :
    ‖provenance.sourceNormal point‖ = 1 :=
  current.grain.localGrains.planeMap_unit _

theorem sourceNormal_vertical
    (provenance :
      PureWZ2HierarchyReentrantCurrentCoarseSourceProvenance firstOverlay)
    (point : {point : Point3 // point ∈ provenance.sourceWitness.shading.union}) :
    |provenance.sourceNormal point (2 : Fin 3)| ≤ 1 / 2 :=
  current.grain.planeMap_vertical_bound _

/-- The only honest cross-anchor continuity statement: the right-hand metric
is the metric between genuine occupied source points, not between their
coarse target positions. -/
theorem sourceNormal_dist_le_source_dist
    (provenance :
      PureWZ2HierarchyReentrantCurrentCoarseSourceProvenance firstOverlay)
    (first second :
      {point : Point3 // point ∈ provenance.sourceWitness.shading.union}) :
    dist (provenance.sourceNormal first) (provenance.sourceNormal second) ≤
      dist (provenance.sourcePoint first)
        (provenance.sourcePoint second) := by
  have h := current.grain.localGrains.planeMap_lipschitz
    (provenance.sourcePoint first) (provenance.sourcePoint second)
  simpa [sourceNormal, edist_dist] using h

/-- The current local AD receipt at the honest source point, before any
cross-family ball or plane-field transport. -/
theorem sourceNormal_local_ad
    (provenance :
      PureWZ2HierarchyReentrantCurrentCoarseSourceProvenance firstOverlay)
    (queryScale : ℝ) (hdelta : delta ≤ queryScale)
    (hone : queryScale ≤ 1)
    (point : {point : Point3 // point ∈ provenance.sourceWitness.shading.union}) :
    PureWZ2PaperADSet1
      (scalarProjection (provenance.sourceNormal point)
        (current.grain.shading.union ∩
          Metric.closedBall (provenance.sourcePoint point : Point3)
            (Real.sqrt queryScale)))
      queryScale (1 - sigma)
      (Kakeya.realRpowENN delta (-inputLoss)) :=
  current.grain.localGrains.local_ad queryScale hdelta hone _

end PureWZ2HierarchyReentrantCurrentCoarseSourceProvenance

/-- Construct all source-witness and current-embedding data directly from the
exact first owner overlay.  This is the provenance part of the desired
transport and has no additional receipt input. -/
theorem
    pureWZ2_hierarchy_reentrant_current_coarse_sourceProvenance_nonempty
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    (firstOverlay : PureWZ2HierarchyReentrantFirstOverlayReceipt
      (current := current) kernelOutput) :
    Nonempty
      (PureWZ2HierarchyReentrantCurrentCoarseSourceProvenance firstOverlay) := by
  classical
  rcases PureWZ2.source_witness_coarse_shading
      firstOverlay.ambient.data.balanced with ⟨sourceWitness⟩
  have source_exists :
      ∀ point : {point : Point3 // point ∈ sourceWitness.shading.union},
        ∃ source :
            {point : Point3 // point ∈ current.grain.shading.union},
          (source : Point3) ∈ firstOverlay.ambient.data.refined.union ∧
            wz1PaperGridIndex kernelOutput.requested.1 (source : Point3) =
              wz1PaperGridIndex kernelOutput.requested.1 (point : Point3) := by
    intro point
    have hcoarse :
        (point : Point3) ∈
          firstOverlay.ambient.data.croppedCoarseShading.union := by
      rw [← PureWZ2.source_witness_coarse_shading_union_eq sourceWitness]
      exact point.property
    rw [firstOverlay.ambient.data.balanced.coarse_union_eq] at hcoarse
    rcases Set.mem_iUnion₂.mp hcoarse with ⟨cell, hcell, hpointCell⟩
    let sourceRaw :=
      firstOverlay.ambient.data.balanced.cellRep cell hcell
    have hsourceFine :
        sourceRaw ∈ firstOverlay.ambient.data.refined.union :=
      firstOverlay.ambient.data.balanced.cellRep_in_union cell hcell
    rcases hsourceFine with ⟨sourceIndex, hsourceCarrier⟩
    have hsourceCurrent :
        sourceRaw ∈ current.grain.shading.carrier
          (firstOverlay.ambient.data.selected.embedding sourceIndex) :=
      firstOverlay.ambient.data.subshading sourceIndex hsourceCarrier
    refine
      ⟨⟨sourceRaw,
          ⟨firstOverlay.ambient.data.selected.embedding sourceIndex,
            hsourceCurrent⟩⟩,
        ⟨sourceIndex, hsourceCarrier⟩, ?_⟩
    exact
      ((mem_wz1PaperGridCube kernelOutput.requested.1 cell sourceRaw).mp
        (firstOverlay.ambient.data.balanced.cellRep_in_cell cell hcell)).trans
      ((mem_wz1PaperGridCube kernelOutput.requested.1 cell point).mp
        hpointCell).symm
  let sourcePoint :
      {point : Point3 // point ∈ sourceWitness.shading.union} →
        {point : Point3 // point ∈ current.grain.shading.union} :=
    fun point => Classical.choose (source_exists point)
  have sourcePoint_spec : ∀ point,
      (sourcePoint point : Point3) ∈ firstOverlay.ambient.data.refined.union ∧
        wz1PaperGridIndex kernelOutput.requested.1
            (sourcePoint point : Point3) =
          wz1PaperGridIndex kernelOutput.requested.1 (point : Point3) :=
    fun point => Classical.choose_spec (source_exists point)
  refine ⟨{
    sourceWitness := sourceWitness
    sourcePoint := sourcePoint
    sourcePoint_mem_refined := fun point => (sourcePoint_spec point).1
    sourcePoint_same_cell := fun point => (sourcePoint_spec point).2
    sourcePoint_dist_lt := ?_
  }⟩
  intro point
  have hrho : 0 < kernelOutput.requested.1 :=
    firstOverlay.ambient.coarse_extremal.delta_pos
  have hsourceCell :
      (sourcePoint point : Point3) ∈
        wz1PaperGridCube kernelOutput.requested.1
          (wz1PaperGridIndex kernelOutput.requested.1 (point : Point3)) :=
    (mem_wz1PaperGridCube kernelOutput.requested.1 _ _).mpr
      (sourcePoint_spec point).2
  have hpointCell :
      (point : Point3) ∈
        wz1PaperGridCube kernelOutput.requested.1
          (wz1PaperGridIndex kernelOutput.requested.1 (point : Point3)) :=
    (mem_wz1PaperGridCube kernelOutput.requested.1 _ _).mpr rfl
  exact wz1_paper_grid_cube_diameter_lt_two_rho hrho
    hsourceCell hpointCell

/-- Minimal current-source receipt for synchronized post-grain selection.

It contains only exact owner-call provenance and scalar loss absorptions.
Normals remain sampled at genuine points of the supplied current shading;
there is deliberately no plane map, Lipschitz extension, or local AD claim on
the enlarged coarse union. -/
structure PureWZ2HierarchyReentrantCurrentCoarseAnchoredReceipt
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    (firstOverlay : PureWZ2HierarchyReentrantFirstOverlayReceipt
      (current := current) kernelOutput) where
  provenance :
    PureWZ2HierarchyReentrantCurrentCoarseSourceProvenance firstOverlay
  grainLoss : ℝ
  grainLoss_pos : 0 < grainLoss
  ambient_loss_le_grain :
    lossSchedule.ownerSchedule.stickyLoss ≤ grainLoss
  ancestor_normalization_loss_le_grain :
    firstOverlay.ambient.seed.coarseNormalizationLoss ≤ grainLoss
  extremal_absorption :
    pureWZ2HierarchyReentrantCurrentCoarseMultiplicityLoss firstOverlay *
        Kakeya.realRpowENN kernelOutput.requested.1 grainLoss ≤
      Kakeya.realRpowENN kernelOutput.requested.1
        lossSchedule.ownerSchedule.stickyLoss

namespace PureWZ2HierarchyReentrantCurrentCoarseAnchoredReceipt

variable
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    {firstOverlay : PureWZ2HierarchyReentrantFirstOverlayReceipt
      (current := current) kernelOutput}

/-- Structural coarse source consumed by synchronized selection.  All analytic
normal values remain available through `receipt.provenance.sourceNormal` on
the honest source subtype. -/
noncomputable def toAnchoredCoarseSource
    (receipt : PureWZ2HierarchyReentrantCurrentCoarseAnchoredReceipt
      firstOverlay) :
    PureWZ2Node05AnchoredCoarseSource
      (grainLoss := receipt.grainLoss) firstOverlay.ambient := by
  let rho := kernelOutput.requested.1
  let massLoss :=
    pureWZ2HierarchyReentrantCurrentCoarseMultiplicityLoss firstOverlay
  have rho_pos : 0 < rho :=
    firstOverlay.ambient.coarse_extremal.delta_pos
  have rho_le_one : rho ≤ 1 :=
    firstOverlay.ambient.coarse_extremal.delta_le_one
  have massLoss_pos : 0 < massLoss := by
    have power_pos :
        0 < Kakeya.realRpowENN rho
          (2 - sigma - lossSchedule.ownerSchedule.stickyLoss) := by
      simp only [Kakeya.realRpowENN]
      exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos rho_pos _)
    have card_ne_zero : firstOverlay.ambient.coarse.enncard ≠ 0 := by
      simpa [Kakeya.Streamlined.TubeFamily.enncard] using
        firstOverlay.ambient.coarse_extremal.nonempty.ne'
    exact ENNReal.mul_pos power_pos.ne' card_ne_zero
  have massLoss_ne_top : massLoss ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · simp [Kakeya.realRpowENN]
    · simp [Kakeya.Streamlined.TubeFamily.enncard]
  have sourceWitness_mass :
      massLoss⁻¹ * firstOverlay.ambient.croppedCoarseShading.mass ≤
        receipt.provenance.sourceWitness.shading.mass := by
    simpa [massLoss,
      pureWZ2HierarchyReentrantCurrentCoarseMultiplicityLoss] using
      PureWZ2.source_witness_coarse_shading_mass_lower_of_sticky
        receipt.provenance.sourceWitness
  have target_extremal :
      WZ2PaperCroppedIsExtremal sigma receipt.grainLoss
        firstOverlay.ambient.coarse
          receipt.provenance.sourceWitness.shading :=
    transfer_cropped_extremal_to_subshading massLoss massLoss_pos
      massLoss_ne_top firstOverlay.ambient.coarse_extremal
      receipt.provenance.sourceWitness.subshading sourceWitness_mass
      receipt.provenance.sourceWitness.balanced.coarse_cubical
      receipt.ambient_loss_le_grain receipt.extremal_absorption
      rho_pos rho_le_one receipt.grainLoss_pos
  have target_cwa :
      WZ2PaperConvexWolffBound firstOverlay.ambient.coarse
        (Kakeya.realRpowENN rho (-receipt.grainLoss)) :=
    PureWZ2.transfer_cwa_to_subshading
      (_shading1 := firstOverlay.ambient.croppedCoarseShading)
      (_shading2 := receipt.provenance.sourceWitness.shading)
      firstOverlay.ancestor.cropped_top_level_cwa
      receipt.ancestor_normalization_loss_le_grain rho_pos rho_le_one
  have target_volume :
      Kakeya.realRpowENN rho (sigma + receipt.grainLoss) ≤
        volume receipt.provenance.sourceWitness.shading.union := by
    calc
      Kakeya.realRpowENN rho (sigma + receipt.grainLoss) ≤
          Kakeya.realRpowENN rho
            (sigma + lossSchedule.ownerSchedule.stickyLoss) := by
        exact pure_wz2_rpowENN_antitone rho_pos rho_le_one
          (by linarith [receipt.ambient_loss_le_grain])
      _ ≤ volume firstOverlay.ambient.croppedCoarseShading.union :=
        firstOverlay.ambient.coarse_volume_lower
      _ = volume receipt.provenance.sourceWitness.shading.union := by
        rw [PureWZ2.source_witness_coarse_shading_union_eq
          receipt.provenance.sourceWitness]
  exact
    { shading := receipt.provenance.sourceWitness.shading
      subshading := receipt.provenance.sourceWitness.subshading
      line_class := firstOverlay.ambient.cover.coarse_line_class
      cubical := receipt.provenance.sourceWitness.balanced.coarse_cubical
      extremal := target_extremal
      top_level_cwa := target_cwa
      volume_lower := target_volume }

end PureWZ2HierarchyReentrantCurrentCoarseAnchoredReceipt

/-- The irreducible cross-family geometry needed to transport the supplied
current grains to the exact first coarse overlay.

The target shading is an honest source-witness refinement selected inside the
receipt.  The analytic fields below are geometric projection and plane-field
facts, not a preassembled grain output. -/
structure PureWZ2HierarchyReentrantCurrentCoarseTransportReceipt
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    (firstOverlay : PureWZ2HierarchyReentrantFirstOverlayReceipt
      (current := current) kernelOutput) where
  provenance :
    PureWZ2HierarchyReentrantCurrentCoarseSourceProvenance firstOverlay
  grainLoss : ℝ
  grainLoss_pos : 0 < grainLoss
  ambient_loss_le_grain :
    lossSchedule.ownerSchedule.stickyLoss ≤ grainLoss
  ancestor_normalization_loss_le_grain :
    firstOverlay.ambient.seed.coarseNormalizationLoss ≤ grainLoss
  extremal_absorption :
    pureWZ2HierarchyReentrantCurrentCoarseMultiplicityLoss firstOverlay *
        Kakeya.realRpowENN kernelOutput.requested.1 grainLoss ≤
      Kakeya.realRpowENN kernelOutput.requested.1
        lossSchedule.ownerSchedule.stickyLoss
  ad_constant_absorption :
    192 * Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN kernelOutput.requested.1 (-grainLoss)
  planeMap :
    {point : Point3 // point ∈ provenance.sourceWitness.shading.union} → Point3
  planeMap_lipschitz : LipschitzWith 1 planeMap
  planeMap_unit : ∀ point, ‖planeMap point‖ = 1
  planeMap_incidence :
    ∀ index point,
      ∀ hpoint : point ∈ provenance.sourceWitness.shading.carrier index,
        |inner ℝ (firstOverlay.ambient.coarse.tube index).direction
          (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤
            kernelOutput.requested.1
  planeMap_vertical_bound :
    ∀ point, |planeMap point (2 : Fin 3)| ≤ 1 / 2
  global_projection_transport :
    ∀ height : PureWZ2UnitInterval,
      ∀ value ∈
        scalarProjection
          (globalGrainDirection (current.grain.globalGrains.f height))
          (horizontalSlice provenance.sourceWitness.shading.union height.1),
        ∃ sourceValue ∈
          scalarProjection
            (globalGrainDirection (current.grain.globalGrains.f height))
            (horizontalSlice current.grain.shading.union height.1),
          |value - sourceValue| ≤ 6 * kernelOutput.requested.1
  local_projection_transport :
    ∀ queryScale : ℝ,
      kernelOutput.requested.1 ≤ queryScale →
      queryScale ≤ 1 →
      ∀ point :
          {point : Point3 // point ∈ provenance.sourceWitness.shading.union},
        ∀ value ∈
          scalarProjection (planeMap point)
            (provenance.sourceWitness.shading.union ∩
              Metric.closedBall (point : Point3) (Real.sqrt queryScale)),
          ∃ sourceValue ∈
            scalarProjection
              (current.grain.localGrains.planeMap
                (provenance.sourcePoint point))
              (current.grain.shading.union ∩
                Metric.closedBall (provenance.sourcePoint point : Point3)
                  (Real.sqrt queryScale)),
            |value - sourceValue| ≤ 6 * queryScale

namespace PureWZ2HierarchyReentrantCurrentCoarseTransportReceipt

variable
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    {firstOverlay : PureWZ2HierarchyReentrantFirstOverlayReceipt
      (current := current) kernelOutput}

/-- Assemble the complete current-slope coarse grain from the exact geometric
transport receipt. -/
noncomputable def toCurrentCoarseGrainReceipt
    (transport : PureWZ2HierarchyReentrantCurrentCoarseTransportReceipt
      firstOverlay) :
    PureWZ2HierarchyReentrantCurrentCoarseGrainReceipt firstOverlay := by
  let rho := kernelOutput.requested.1
  let massLoss :=
    pureWZ2HierarchyReentrantCurrentCoarseMultiplicityLoss firstOverlay
  have rho_pos : 0 < rho :=
    firstOverlay.ambient.coarse_extremal.delta_pos
  have rho_le_one : rho ≤ 1 :=
    firstOverlay.ambient.coarse_extremal.delta_le_one
  have massLoss_pos : 0 < massLoss := by
    have power_pos :
        0 < Kakeya.realRpowENN rho
          (2 - sigma - lossSchedule.ownerSchedule.stickyLoss) := by
      simp only [Kakeya.realRpowENN]
      exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos rho_pos _)
    have card_ne_zero : firstOverlay.ambient.coarse.enncard ≠ 0 := by
      simpa [Kakeya.Streamlined.TubeFamily.enncard] using
        firstOverlay.ambient.coarse_extremal.nonempty.ne'
    exact ENNReal.mul_pos power_pos.ne' card_ne_zero
  have massLoss_ne_top : massLoss ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · simp [Kakeya.realRpowENN]
    · simp [Kakeya.Streamlined.TubeFamily.enncard]
  have sourceWitness_mass :
      massLoss⁻¹ * firstOverlay.ambient.croppedCoarseShading.mass ≤
        transport.provenance.sourceWitness.shading.mass := by
    simpa [massLoss,
      pureWZ2HierarchyReentrantCurrentCoarseMultiplicityLoss] using
      PureWZ2.source_witness_coarse_shading_mass_lower_of_sticky
        transport.provenance.sourceWitness
  have target_extremal :
      WZ2PaperCroppedIsExtremal sigma transport.grainLoss
        firstOverlay.ambient.coarse
          transport.provenance.sourceWitness.shading :=
    transfer_cropped_extremal_to_subshading massLoss massLoss_pos
      massLoss_ne_top firstOverlay.ambient.coarse_extremal
      transport.provenance.sourceWitness.subshading sourceWitness_mass
      transport.provenance.sourceWitness.balanced.coarse_cubical
      transport.ambient_loss_le_grain transport.extremal_absorption
      rho_pos rho_le_one transport.grainLoss_pos
  have target_cwa :
      WZ2PaperConvexWolffBound firstOverlay.ambient.coarse
        (Kakeya.realRpowENN rho (-transport.grainLoss)) :=
    PureWZ2.transfer_cwa_to_subshading
      (_shading1 := firstOverlay.ambient.croppedCoarseShading)
      (_shading2 := transport.provenance.sourceWitness.shading)
      firstOverlay.ancestor.cropped_top_level_cwa
      transport.ancestor_normalization_loss_le_grain rho_pos rho_le_one
  have target_volume :
      Kakeya.realRpowENN rho (sigma + transport.grainLoss) ≤
        volume transport.provenance.sourceWitness.shading.union := by
    calc
      Kakeya.realRpowENN rho (sigma + transport.grainLoss) ≤
          Kakeya.realRpowENN rho
            (sigma + lossSchedule.ownerSchedule.stickyLoss) := by
        exact pure_wz2_rpowENN_antitone rho_pos rho_le_one
          (by linarith [transport.ambient_loss_le_grain])
      _ ≤ volume firstOverlay.ambient.croppedCoarseShading.union :=
        firstOverlay.ambient.coarse_volume_lower
      _ = volume transport.provenance.sourceWitness.shading.union := by
        rw [PureWZ2.source_witness_coarse_shading_union_eq
          transport.provenance.sourceWitness]
  let globalGrains :
      PureWZ2LipschitzGlobalGrainData
        transport.provenance.sourceWitness.shading sigma
        (Kakeya.realRpowENN rho (-transport.grainLoss)) :=
    { f := current.grain.globalGrains.f
      lipschitz := current.grain.globalGrains.lipschitz
      paper_ad := by
        intro height
        have sourceAD :=
          current.grain.globalGrains.paper_ad height
        have coarseAD :=
          sourceAD.weaken_scale rho_pos kernelOutput.requested.property.1
        have perturbed :=
          coarseAD.perturb_by_six_delta
            (transport.global_projection_transport height)
        exact perturbed.mono_const transport.ad_constant_absorption
          (by simp [Kakeya.realRpowENN]) }
  let localGrains :
      PureWZ2LocalGrainData transport.provenance.sourceWitness.shading sigma
        (Kakeya.realRpowENN rho (-transport.grainLoss)) :=
    { planeMap := transport.planeMap
      planeMap_lipschitz := transport.planeMap_lipschitz
      planeMap_unit := transport.planeMap_unit
      planeMap_incidence := transport.planeMap_incidence
      local_ad := by
        intro queryScale rho_le_query query_le_one point
        have delta_le_query :
            delta ≤ queryScale :=
          kernelOutput.requested.property.1.trans rho_le_query
        have sourceAD :=
          current.grain.localGrains.local_ad queryScale delta_le_query
            query_le_one (transport.provenance.sourcePoint point)
        have perturbed :=
          sourceAD.perturb_by_six_delta
            (transport.local_projection_transport queryScale rho_le_query
              query_le_one point)
        exact perturbed.mono_const transport.ad_constant_absorption
          (by simp [Kakeya.realRpowENN]) }
  let coarseGrains : PureWZ2GrainRefinementData
      firstOverlay.ambient.croppedCoarseShading sigma transport.grainLoss :=
    { shading := transport.provenance.sourceWitness.shading
      subshading := by
        intro index point hpoint
        exact transport.provenance.sourceWitness.subshading index hpoint
      line_class := firstOverlay.ambient.cover.coarse_line_class
      cubical := transport.provenance.sourceWitness.balanced.coarse_cubical
      extremal := target_extremal
      top_level_cwa := target_cwa
      volume_lower := target_volume
      globalGrains := globalGrains
      localGrains := localGrains
      planeMap_vertical_bound := transport.planeMap_vertical_bound }
  exact
    { grainLoss := transport.grainLoss
      coarseGrains := coarseGrains
      coarse_slope_eq := rfl }

end PureWZ2HierarchyReentrantCurrentCoarseTransportReceipt

/-- Exact-current geometric transport producer.

The quantifier order is identical to
`PureWZ2HierarchyReentrantCurrentCoarseGrainAt`; the result is tied to the
supplied current source, kernel output, and exact first-overlay receipt. -/
def PureWZ2HierarchyReentrantCurrentCoarseTransportAt
    (capability : PureWZ2PropStickyCapability) (sigma : ℝ) : Prop :=
  ∀ {outputLoss sourceLossCeiling : ℝ},
    ∀ lossSchedule :
        PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
          outputLoss sourceLossCeiling,
      ∀ inputLoss : ℝ,
        0 < inputLoss → inputLoss ≤ sourceLossCeiling →
          ∀ delta : ℝ,
            0 < delta → delta ≤ lossSchedule.ownerSchedule.delta₀ →
              ∀ current : PureWZ2ReentrantGrainSource sigma inputLoss delta
                  capability.normalizationExponent,
                ∀ targetRho : ℝ,
                  delta ≤ targetRho → targetRho ≤ 1 →
                    Real.rpow delta (1 - outputLoss) ≤ targetRho →
                      targetRho ≤ Real.rpow delta outputLoss →
                        ∀ outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
                            delta targetRho
                            lossSchedule.ownerSchedule.stickyLoss outputLoss,
                          ∀ kernelOutput :
                              PureWZ2HierarchyReentrantOrdinaryKernelOutput
                                (current := current)
                                lossSchedule.ownerSchedule outer,
                            ∀ firstOverlay :
                                PureWZ2HierarchyReentrantFirstOverlayReceipt
                                  (current := current) kernelOutput,
                              Nonempty
                                (PureWZ2HierarchyReentrantCurrentCoarseTransportReceipt
                                  firstOverlay)

/-- Once the exact cross-family geometric transport is available, the frozen
current-coarse-grain target follows without any further grain callback or
Proposition 6.3 invocation. -/
theorem pureWZ2_hierarchy_reentrant_current_coarse_grain_of_transport
    {capability : PureWZ2PropStickyCapability} {sigma : ℝ}
    (transport :
      PureWZ2HierarchyReentrantCurrentCoarseTransportAt capability sigma) :
    PureWZ2HierarchyReentrantCurrentCoarseGrainAt capability sigma := by
  intro outputLoss sourceLossCeiling lossSchedule inputLoss hinput
    hinputCeiling delta hdelta hdeltaSmall current targetRho hdeltaRho
    hrhoOne hrhoLower hrhoUpper outer kernelOutput firstOverlay
  rcases transport lossSchedule inputLoss hinput hinputCeiling delta hdelta
      hdeltaSmall current targetRho hdeltaRho hrhoOne hrhoLower hrhoUpper
      outer kernelOutput firstOverlay with ⟨receipt⟩
  exact ⟨receipt.toCurrentCoarseGrainReceipt⟩

end Kakeya.Assouad

end
