import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4WindowedCoarseTrace
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropStickyReentry

/-!
# Exact frozen coarse provenance for Proposition 6.2 re-entry

The final coarse shading is frozen before the random whole-cell balancing
sample.  This module works with that full parent--coarse-cell relation, rather
than the smaller set of cells still hit by the sampled final fine shading.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace Prop62V4RichCertificateCompanionData

variable
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent}
    {rho : WZ2PaperRequestedScale delta}
    {hdelta : 0 < delta}
    {preparation :
      FixedGridPreparationData
        (rho := rho.1) normalized.croppedRefined hdelta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {metricCertificate :
      PureWZ2Prop62MetricParentsV4Certificate
        preparation.cleanup.refined rho fineParentDistanceConstant
          parentConstant fiberConstant}
    {eta : ℝ}
    {packetDensityExponent cwaLossExponent polylogExponent : ℕ}
    (rich :
      Prop62V4RichCertificateCompanionData
        (eta := eta)
        (packetDensityExponent := packetDensityExponent)
        (cwaLossExponent := cwaLossExponent)
        (polylogExponent := polylogExponent)
        hdelta
        (prop62V4FixedGridMetricCompanionOfCertificate
          normalized preparation metricCertificate))

/-- Every frozen coarse cell attached to one exact final parent. -/
def finalFrozenParentCells
    (parent : Fin rich.outputCertificate.coarse.family.card) :
    Finset WZ2PaperCellIndex :=
  rich.packetInput.frozenCoarseCellsAt
    rich.multiplicity rich.parentClass rich.treeCleanup
    rich.exactification rich.core.ranges
    (rich.families.restriction.coarseSelected.embedding parent)

/--
The exact final cropped coarse shading is the union of all frozen cells, not
only the cells hit after the random sample.
-/
theorem finalFrozenCoarseShading_carrier
    (parent : Fin rich.outputCertificate.coarse.family.card) :
    rich.outputCertificate.coarseShading.carrier parent =
      wz2RetainedCellsUnion rho.1
        (rich.finalFrozenParentCells parent) := by
  change
    rich.producer.output.output.coarseShading.carrier parent =
      wz2RetainedCellsUnion rho.1
        (rich.finalFrozenParentCells parent)
  rw [rich.producer.output.output.coarseShading_eq]
  rfl

/-- Every exact terminal parent has at least one frozen coarse cell. -/
theorem finalFrozenParentCells_nonempty
    (parent : Fin rich.outputCertificate.coarse.family.card) :
    (rich.finalFrozenParentCells parent).Nonempty := by
  have parentMem :
      rich.families.restriction.coarseSelected.embedding parent ∈
        rich.families.terminalParents := by
    rw [← rich.families.coarse_image_univ]
    exact
      Finset.mem_image.mpr
        ⟨parent, Finset.mem_univ parent, rfl⟩
  rw [rich.families.terminalParents_eq] at parentMem
  rcases Finset.mem_image.mp parentMem with
    ⟨edge, edgeTerminal, edgeParent⟩
  refine
    ⟨rich.exactification.incidence.edgeCoarseCell edge, ?_⟩
  exact
    Finset.mem_image.mpr
      ⟨edge,
        Finset.mem_filter.mpr
          ⟨edgeTerminal, edgeParent⟩,
        rfl⟩

/-- Every post-sample selected parent cell belongs to the full frozen relation. -/
theorem selectedParentCells_subset_finalFrozen
    (parent : Fin rich.outputCertificate.coarse.family.card) :
    rich.outputCertificate.selectedParentCells parent ⊆
      rich.finalFrozenParentCells parent := by
  intro cell cellMem
  let point := cellCorner rho.1 cell
  have pointCell :
      point ∈ wz1PaperGridCube rho.1 cell :=
    cellCorner_mem_gridCube metricCertificate.rho_pos cell
  have pointCoarse :
      point ∈ rich.outputCertificate.coarseShading.carrier parent :=
    rich.outputCertificate.selectedParentCell_subset_coarseShading
      parent cell cellMem pointCell
  rw [rich.finalFrozenCoarseShading_carrier parent] at pointCoarse
  rcases Set.mem_iUnion₂.mp pointCoarse with
    ⟨frozenCell, frozenMem, pointFrozen⟩
  have cellEq :
      cell = frozenCell := by
    exact
      ((mem_wz1PaperGridCube rho.1 cell point).mp pointCell).symm.trans
        ((mem_wz1PaperGridCube rho.1 frozenCell point).mp pointFrozen)
  simpa only [cellEq] using frozenMem

/--
The pre-sampling packet shading restricted to the exact final complete fine
family.  Unlike `fixedGridComposedShading`, this retains every terminal edge
cell and is used only to recover ordinary provenance.
-/
def frozenPreSampleFineShading :
    WZ1PaperTubeShading
      rich.outputCertificate.refinement.selected.family :=
  restrictPaperShading
    rich.outputCertificate.refinement.selected
    (prop62V4FixedGridMetricCompanionOfCertificate
      normalized preparation metricCertificate
    ).metric.refinement.refined

/-- The pre-sampling exact fine shading still lies in the root cropped pair. -/
theorem frozenPreSampleFineShading_sub_normalized
    (index :
      Fin rich.outputCertificate.refinement.selected.family.card) :
    rich.frozenPreSampleFineShading.carrier index ⊆
      normalized.croppedRefined.carrier
        (rich.fixedGridComposedSelected.embedding index) := by
  intro point pointMem
  let metric :=
    (prop62V4FixedGridMetricCompanionOfCertificate
      normalized preparation metricCertificate).metric
  have pointMetric :
      point ∈ metric.refinement.refined.carrier
        (rich.outputCertificate.refinement.selected.embedding index) := by
    exact pointMem
  have pointCleanup :
      point ∈ preparation.cleanup.refined.carrier
        (metric.refinement.selected.embedding
          (rich.outputCertificate.refinement.selected.embedding index)) :=
    metric.refinement.subshading
      (rich.outputCertificate.refinement.selected.embedding index)
      pointMetric
  have pointNormalized :
      point ∈ normalized.croppedRefined.carrier
        (preparation.fixedGridRefinement.selected.embedding
          (metric.refinement.selected.embedding
            (rich.outputCertificate.refinement.selected.embedding index))) :=
    preparation.fixedGridRefinement.subshading
      (metric.refinement.selected.embedding
        (rich.outputCertificate.refinement.selected.embedding index))
      pointCleanup
  simpa only [fixedGridComposedSelected_embedding] using pointNormalized

/--
The small metric-parent distance requested by the normalized rich producer
survives the exact terminal fine/coarse reindexing.
-/
theorem finalFine_parent_close_strong
    (distanceConstant :
      fineParentDistanceConstant = (1 / 100 : ℝ))
    (sourceIndex :
      Fin rich.outputCertificate.refinement.selected.family.card) :
    wz1PaperLineDistance
        (rich.outputCertificate.refinement.selected.family.tube sourceIndex)
        (rich.outputCertificate.coarse.family.tube
          (rich.outputCertificate.cover.toWZ1PaperTubeCover.parent
            sourceIndex)) ≤
      rho.1 / 100 := by
  let metric :=
    (prop62V4FixedGridMetricCompanionOfCertificate
      normalized preparation metricCertificate).metric
  let ambientSource :=
    rich.outputCertificate.refinement.selected.embedding sourceIndex
  have parentCommutes :=
    rich.outputCertificate.parent_commutes sourceIndex
  have closeRaw :=
    metric.fine_parent_close ambientSource
  rw [
    rich.outputCertificate.refinement.selected.tube_eq,
    rich.outputCertificate.coarse.tube_eq
  ]
  have parentEq :
      metric.scaleData.cover.parent ambientSource =
        rich.outputCertificate.coarse.embedding
          (rich.outputCertificate.cover.toWZ1PaperTubeCover.parent
            sourceIndex) := by
    symm
    apply metric.scaleData.cover.parent_unique
    have covered :=
      rich.outputCertificate.cover.toWZ1PaperTubeCover.parent_covers
        sourceIndex
    rw [
      rich.outputCertificate.refinement.selected.tube_eq,
      rich.outputCertificate.coarse.tube_eq
    ] at covered
    simpa only [metric, ambientSource] using covered
  rw [← parentEq]
  simpa [metric, ambientSource, distanceConstant, div_eq_mul_inv, mul_comm]
    using closeRaw

/--
Every frozen parent--coarse-cell incidence has an exact final fine index and
a pre-sampling whole fine cell in that parent and coarse cell.
-/
theorem finalFrozenParentCell_fineWitness
    (parent : Fin rich.outputCertificate.coarse.family.card)
    (coarseCell : WZ2PaperCellIndex)
    (cellMem : coarseCell ∈ rich.finalFrozenParentCells parent) :
    ∃ sourceIndex :
        Fin rich.outputCertificate.refinement.selected.family.card,
      rich.outputCertificate.cover.toWZ1PaperTubeCover.parent sourceIndex =
          parent ∧
        ∃ fineCell : WZ2PaperCellIndex,
          wz1PaperGridCube delta fineCell ⊆
              rich.frozenPreSampleFineShading.carrier sourceIndex ∧
            wz1PaperGridCube delta fineCell ⊆
              wz1PaperGridCube rho.1 coarseCell := by
  let ambientCover :=
    (prop62V4FixedGridMetricCompanionOfCertificate
      normalized preparation metricCertificate
    ).metric.scaleData.section6Cover
  rcases Finset.mem_image.mp cellMem with
    ⟨edge, edgeMem, edgeCoarse⟩
  have edgeData := Finset.mem_filter.mp edgeMem
  have edgeTerminal : edge ∈ rich.core.ranges.terminalEdges :=
    edgeData.1
  have edgeParent :
      rich.exactification.incidence.edgeParent edge =
        rich.families.restriction.coarseSelected.embedding parent :=
    edgeData.2
  have selectedSourcesNonempty :
      (rich.exactification.selectedSources
        (rich.packetInput.referencePairOfEdge
          rich.multiplicity rich.parentClass rich.treeCleanup
          rich.exactification edge)).Nonempty := by
    apply Finset.card_pos.mp
    rw [rich.exactification.selectedSources_card]
    exact rich.multiplicity.muFine_pos
  rcases selectedSourcesNonempty with
    ⟨ambientSource, sourceSelected⟩
  let pair :=
    rich.packetInput.referencePairOfEdge
      rich.multiplicity rich.parentClass rich.treeCleanup
      rich.exactification edge
  have sourceFiber :
      ambientSource ∈
        wz2PaperFullFiberIndices
          _ _ (rich.exactification.incidence.edgeParent edge) :=
    PureWZ2Prop62PacketCellInput.PacketCellExactificationData.selectedSource_mem_fullFiber
      rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
      rich.exactification pair sourceSelected
  have edgeParentCanonical :
      rich.exactification.incidence.edgeParent edge =
        ambientCover.toWZ1PaperTubeCover.parent ambientSource := by
    apply ambientCover.toWZ1PaperTubeCover.parent_unique
    exact
      (mem_wz2PaperFullFiberIndices_iff
        (rich.exactification.incidence.edgeParent edge)
        ambientSource).mp sourceFiber
  have edgeParentTerminal :
      rich.exactification.incidence.edgeParent edge ∈
        rich.families.terminalParents := by
    rw [rich.families.terminalParents_eq]
    exact
      Finset.mem_image.mpr
        ⟨edge, edgeTerminal, rfl⟩
  have ambientSourceTerminal :
      ambientSource ∈ rich.families.terminalFine := by
    rw [rich.families.terminalFine_eq]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ ambientSource, ?_⟩
    rw [← rich.families.terminalParents_eq]
    rw [← edgeParentCanonical]
    exact edgeParentTerminal
  have ambientSourceImage :
      ambientSource ∈
        Finset.image
          rich.families.restriction.fineSelected.embedding
          Finset.univ := by
    rw [rich.families.restriction.fine_image_univ]
    exact ambientSourceTerminal
  have ambientSourceOutputImage :
      ambientSource ∈
        Finset.image
          rich.outputCertificate.refinement.selected.embedding
          Finset.univ := by
    change
      ambientSource ∈
        Finset.image
          rich.families.restriction.fineSelected.embedding
          Finset.univ
    exact ambientSourceImage
  rcases Finset.mem_image.mp ambientSourceOutputImage with
    ⟨finalSource, _sourceUniv, finalSourceEq⟩
  have finalParentEq :
      rich.outputCertificate.cover.toWZ1PaperTubeCover.parent finalSource =
        parent := by
    apply
      rich.families.restriction.coarseSelected.embedding.injective
    calc
      rich.families.restriction.coarseSelected.embedding
          (rich.outputCertificate.cover.toWZ1PaperTubeCover.parent
            finalSource) =
          ambientCover.toWZ1PaperTubeCover.parent
            (rich.outputCertificate.refinement.selected.embedding
              finalSource) :=
        (rich.outputCertificate.parent_commutes finalSource).symm
      _ = ambientCover.toWZ1PaperTubeCover.parent ambientSource := by
        rw [finalSourceEq]
      _ = rich.exactification.incidence.edgeParent edge :=
        edgeParentCanonical.symm
      _ = rich.families.restriction.coarseSelected.embedding parent :=
        edgeParent
  let fineCell := rich.exactification.incidence.edgeFineCell edge
  have wholeAmbient :
      wz1PaperGridCube delta fineCell ⊆
        (prop62V4FixedGridMetricCompanionOfCertificate
          normalized preparation metricCertificate
        ).metric.refinement.refined.carrier ambientSource := by
    exact
      PureWZ2Prop62PacketCellInput.PacketCellExactificationData.selectedCell_subset_carrier
        rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
        rich.exactification pair sourceSelected
  have wholeFinal :
      wz1PaperGridCube delta fineCell ⊆
        rich.frozenPreSampleFineShading.carrier finalSource := by
    intro point pointMem
    change
      point ∈
        (prop62V4FixedGridMetricCompanionOfCertificate
          normalized preparation metricCertificate
        ).metric.refinement.refined.carrier
          (rich.outputCertificate.refinement.selected.embedding finalSource)
    rw [finalSourceEq]
    exact wholeAmbient pointMem
  have packetData :=
    rich.exactification.selectedSources_subset pair sourceSelected
  have packetMem :=
    (rich.packetInput.mem_packetCellSources_iff
      pair.1.1 pair.1.2 ambientSource).mp packetData
  have fineCellMem : fineCell ∈ rich.packetInput.fineCells :=
    packetMem.1
  have fineToCoarse :
      wz1PaperGridCube delta fineCell ⊆
        wz1PaperGridCube rho.1 coarseCell := by
    have containment :=
      rich.packetInput.fine_cell_containment fineCell fineCellMem
    change
      wz1PaperGridCube delta fineCell ⊆
        wz1PaperGridCube rho.1
          (rich.packetInput.coarseCellOf fineCell) at containment
    have coarseEq :
        rich.packetInput.coarseCellOf fineCell = coarseCell := by
      calc
        rich.packetInput.coarseCellOf fineCell =
            rich.exactification.incidence.edgeCoarseCell edge := by
          dsimp only [fineCell]
          unfold PureWZ2Prop62FourDegreeIncidenceData.edgeCoarseCell
          rw [rich.exactification.incidence_coarseCellOf_eq]
        _ = coarseCell := edgeCoarse
    rwa [coarseEq] at containment
  exact
    ⟨finalSource, finalParentEq, fineCell, wholeFinal, fineToCoarse⟩

/--
Every frozen parent--coarse-cell incidence contains a point of the original
ordinary normalization trace, even when the random balancing sample removed
all final fine shading from that parent and cell.
-/
theorem finalFrozenParentCell_exists_ordinaryPoint
    (parent : Fin rich.outputCertificate.coarse.family.card)
    (coarseCell : WZ2PaperCellIndex)
    (cellMem : coarseCell ∈ rich.finalFrozenParentCells parent) :
    ∃ sourceIndex :
        Fin rich.outputCertificate.refinement.selected.family.card,
      rich.outputCertificate.cover.toWZ1PaperTubeCover.parent sourceIndex =
          parent ∧
        ∃ point,
          point ∈
              normalized.frame ''
                normalized.ordinaryRefined.carrier
                  (PureWZ2CroppedCriticalNormalizationData.ordinaryIndex
                    normalized rich.fixedGridComposedSelected sourceIndex) ∧
            point ∈ wz1PaperGridCube rho.1 coarseCell := by
  rcases rich.finalFrozenParentCell_fineWitness
      parent coarseCell cellMem with
    ⟨sourceIndex, parentEq, fineCell, wholePreSample, fineToCoarse⟩
  let ordinaryIndex :=
    PureWZ2CroppedCriticalNormalizationData.ordinaryIndex
      normalized rich.fixedGridComposedSelected sourceIndex
  let ordinarySource : Set Point3 :=
    normalized.frame ''
      normalized.ordinaryRefined.carrier ordinaryIndex
  let finePoint := cellCorner delta fineCell
  have finePointCell :
      finePoint ∈ wz1PaperGridCube delta fineCell :=
    cellCorner_mem_gridCube normalized.final_extremal.delta_pos fineCell
  have finePointIndex :
      wz1PaperGridIndex delta finePoint = fineCell :=
    (mem_wz1PaperGridCube delta fineCell finePoint).mp finePointCell
  have finePointPreSample :
      finePoint ∈ rich.frozenPreSampleFineShading.carrier sourceIndex :=
    wholePreSample finePointCell
  have finePointNormalized :
      finePoint ∈
        normalized.croppedRefined.carrier
          (rich.fixedGridComposedSelected.embedding sourceIndex) :=
    rich.frozenPreSampleFineShading_sub_normalized
      sourceIndex finePointPreSample
  have indexEq :
      normalized.indexEquiv ordinaryIndex =
        rich.fixedGridComposedSelected.embedding sourceIndex :=
    normalized.indexEquiv.apply_symm_apply
      (rich.fixedGridComposedSelected.embedding sourceIndex)
  have pointDense :
      finePoint ∈
        pureWZ2DenseCubicalization
          (normalized.croppedFamily.tube
            (rich.fixedGridComposedSelected.embedding sourceIndex))
          ordinarySource := by
    have normalizedEq :=
      normalized.cropped_carrier_eq_dense_cubicalization ordinaryIndex
    rw [indexEq] at normalizedEq
    rw [← normalizedEq]
    exact finePointNormalized
  have ordinarySourceVolumePos : 0 < volume ordinarySource := by
    have ordinaryDensity :
        (Kakeya.realRpowENN delta sourceLoss / 2) *
              volume
                (normalized.croppedFamily.tube
                  (rich.fixedGridComposedSelected.embedding
                    sourceIndex)).carrier ≤
          volume ordinarySource := by
      simpa only [ordinarySource, ordinaryIndex] using
        normalized.framed_ordinary_per_tube
          rich.fixedGridComposedSelected sourceIndex
    have densityPos :
        0 < Kakeya.realRpowENN delta sourceLoss / 2 := by
      apply ENNReal.div_pos
      · simp [Kakeya.realRpowENN,
          Real.rpow_pos_of_pos normalized.final_extremal.delta_pos]
      · norm_num
    have tubeVolumePos :
        0 <
          volume
            (normalized.croppedFamily.tube
              (rich.fixedGridComposedSelected.embedding
                sourceIndex)).carrier :=
      wz2_paper_ordinary_tube_volume_pos
        (normalized.croppedFamily.tube
          (rich.fixedGridComposedSelected.embedding sourceIndex))
        normalized.final_extremal.delta_pos
    exact
      (ENNReal.mul_pos densityPos.ne' tubeVolumePos.ne').trans_le
        ordinaryDensity
  have tubeVolumeTop :
      volume
          (normalized.croppedFamily.tube
            (rich.fixedGridComposedSelected.embedding
              sourceIndex)).carrier ≠ ⊤ :=
    wz2_paper_ordinary_tube_volume_ne_top
      (normalized.croppedFamily.tube
        (rich.fixedGridComposedSelected.embedding sourceIndex))
      normalized.final_extremal.delta_pos
  have fineCellDensity :
      (100 : ENNReal)⁻¹ *
            volume ordinarySource *
            (volume
              (normalized.croppedFamily.tube
                (rich.fixedGridComposedSelected.embedding
                  sourceIndex)).carrier)⁻¹ *
            volume (wz1PaperGridCube delta fineCell) ≤
        volume
          (ordinarySource ∩ wz1PaperGridCube delta fineCell) := by
    simpa only [pureWZ2DenseCubicalization, finePointIndex] using pointDense.2
  have fineCellTraceVolumePos :
      0 <
        volume
          (ordinarySource ∩ wz1PaperGridCube delta fineCell) := by
    have thresholdPos :
        0 <
          (100 : ENNReal)⁻¹ *
              volume ordinarySource *
              (volume
                (normalized.croppedFamily.tube
                  (rich.fixedGridComposedSelected.embedding
                    sourceIndex)).carrier)⁻¹ *
              volume (wz1PaperGridCube delta fineCell) := by
      exact
        ENNReal.mul_pos
          (ENNReal.mul_pos
            (ENNReal.mul_pos
              (ENNReal.inv_ne_zero.mpr (by norm_num))
              ordinarySourceVolumePos.ne').ne'
            (ENNReal.inv_ne_zero.mpr tubeVolumeTop)).ne'
          (wz1PaperGridCube_volume_pos
            normalized.final_extremal.delta_pos fineCell).ne'
    exact thresholdPos.trans_le fineCellDensity
  rcases nonempty_of_measure_ne_zero fineCellTraceVolumePos.ne' with
    ⟨ordinaryPoint, ordinaryPointSource, ordinaryPointFineCell⟩
  exact
    ⟨sourceIndex, parentEq, ordinaryPoint,
      by simpa only [ordinarySource, ordinaryIndex] using ordinaryPointSource,
      fineToCoarse ordinaryPointFineCell⟩

/--
Every frozen parent--coarse-cell incidence contributes a fixed-volume piece
to the exact ordinary carrier of that final parent.
-/
theorem finalFrozenParentCell_ordinary_overlap
    (ratioSmall : delta / rho.1 ≤ 1 / 24)
    (parent : Fin rich.outputCertificate.coarse.family.card)
    (coarseCell : WZ2PaperCellIndex)
    (cellMem : coarseCell ∈ rich.finalFrozenParentCells parent) :
    ENNReal.ofReal ((1 / 100000 : ℝ) * rho.1 ^ 3) ≤
      volume
        (wz1PaperGridCube rho.1 coarseCell ∩
          (rich.outputCertificate.coarse.family.tube parent).carrier) := by
  rcases
      rich.finalFrozenParentCell_exists_ordinaryPoint
        parent coarseCell cellMem
    with ⟨sourceIndex, parentEq, point, pointOrdinary, pointCell⟩
  let ordinaryIndex :=
    PureWZ2CroppedCriticalNormalizationData.ordinaryIndex
      normalized rich.fixedGridComposedSelected sourceIndex
  let ordinarySource : Set Point3 :=
    normalized.frame ''
      normalized.ordinaryRefined.carrier ordinaryIndex
  have indexEq :
      normalized.indexEquiv ordinaryIndex =
        rich.fixedGridComposedSelected.embedding sourceIndex :=
    normalized.indexEquiv.apply_symm_apply
      (rich.fixedGridComposedSelected.embedding sourceIndex)
  have ordinarySubset :
      ordinarySource ⊆
        (rich.outputCertificate.refinement.selected.family.tube
          sourceIndex).carrier := by
    intro tracePoint tracePointMem
    have carrierEq :=
      normalized.ordinary_carrier_image_eq ordinaryIndex
    rw [indexEq] at carrierEq
    change
      tracePoint ∈
        (rich.fixedGridComposedSelected.family.tube sourceIndex).carrier
    rw [rich.fixedGridComposedSelected.tube_eq sourceIndex, carrierEq]
    rcases tracePointMem with ⟨ordinaryPoint, pointMem, rfl⟩
    exact
      ⟨ordinaryPoint,
        normalized.ordinaryRefined.subset_body ordinaryIndex pointMem,
        rfl⟩
  have parentClose :
      wz1PaperLineDistance
          (rich.outputCertificate.refinement.selected.family.tube sourceIndex)
          (rich.outputCertificate.coarse.family.tube parent) ≤
        rho.1 / 2 := by
    have covered :=
      rich.outputCertificate.cover.toWZ1PaperTubeCover.parent_covers
        sourceIndex
    rwa [parentEq] at covered
  have axisWitness :
      ∃ axisPoint ∈
          Kakeya.unitSegment
            (rich.outputCertificate.coarse.family.tube parent).base
            (rich.outputCertificate.coarse.family.tube parent).direction,
        dist point axisPoint ≤ 5 * rho.1 / 6 := by
    apply
      fineOrdinaryTrace_exists_centeredParent_axisPoint
        normalized.final_extremal.delta_pos metricCertificate.rho_pos
        (rich.outputCertificate.refinement.selected.family.tube sourceIndex)
        (rich.outputCertificate.coarse.family.tube parent)
        (rich.outputCertificate.cover.fine_line_class sourceIndex)
        (rich.outputCertificate.cover.coarse_line_class parent)
        (rich.finalParentsCentered parent)
        ratioSmall parentClose ordinarySource ordinarySubset
    · intro tracePoint tracePointMem
      exact
        (normalized.ordinary_axial_window
          ordinaryIndex tracePoint tracePointMem).trans (by norm_num)
    · simpa only [ordinarySource, ordinaryIndex] using pointOrdinary
  exact
    ordinaryTube_gridCube_overlap_volume_lower_of_exists
      metricCertificate.rho_pos
      (rich.outputCertificate.coarse.family.tube parent)
      coarseCell pointCell axisWitness

/--
Strong overlap on every frozen cell for the `1 / 100` metric-parent route.
This is the local estimate used to recover the exact dense cubicalization.
-/
theorem finalFrozenParentCell_ordinary_overlap_strong
    (distanceConstant :
      fineParentDistanceConstant = (1 / 100 : ℝ))
    (ratioSmall : delta / rho.1 ≤ 1 / 24)
    (parent : Fin rich.outputCertificate.coarse.family.card)
    (coarseCell : WZ2PaperCellIndex)
    (cellMem : coarseCell ∈ rich.finalFrozenParentCells parent) :
    ENNReal.ofReal ((1 / 100 : ℝ) * rho.1 ^ 3) ≤
      volume
        (wz1PaperGridCube rho.1 coarseCell ∩
          (rich.outputCertificate.coarse.family.tube parent).carrier) := by
  rcases
      rich.finalFrozenParentCell_exists_ordinaryPoint
        parent coarseCell cellMem
    with ⟨sourceIndex, parentEq, point, pointOrdinary, pointCell⟩
  let ordinaryIndex :=
    PureWZ2CroppedCriticalNormalizationData.ordinaryIndex
      normalized rich.fixedGridComposedSelected sourceIndex
  let ordinarySource : Set Point3 :=
    normalized.frame ''
      normalized.ordinaryRefined.carrier ordinaryIndex
  have indexEq :
      normalized.indexEquiv ordinaryIndex =
        rich.fixedGridComposedSelected.embedding sourceIndex :=
    normalized.indexEquiv.apply_symm_apply
      (rich.fixedGridComposedSelected.embedding sourceIndex)
  have ordinarySubset :
      ordinarySource ⊆
        (rich.outputCertificate.refinement.selected.family.tube
          sourceIndex).carrier := by
    intro tracePoint tracePointMem
    have carrierEq :=
      normalized.ordinary_carrier_image_eq ordinaryIndex
    rw [indexEq] at carrierEq
    change
      tracePoint ∈
        (rich.fixedGridComposedSelected.family.tube sourceIndex).carrier
    rw [rich.fixedGridComposedSelected.tube_eq sourceIndex, carrierEq]
    rcases tracePointMem with ⟨ordinaryPoint, pointMem, rfl⟩
    exact
      ⟨ordinaryPoint,
        normalized.ordinaryRefined.subset_body ordinaryIndex pointMem,
        rfl⟩
  have parentClose :
      wz1PaperLineDistance
          (rich.outputCertificate.refinement.selected.family.tube sourceIndex)
          (rich.outputCertificate.coarse.family.tube parent) ≤
        rho.1 / 100 := by
    have close :=
      rich.finalFine_parent_close_strong distanceConstant sourceIndex
    rwa [parentEq] at close
  have axisWitness :
      ∃ axisPoint ∈
          Kakeya.unitSegment
            (rich.outputCertificate.coarse.family.tube parent).base
            (rich.outputCertificate.coarse.family.tube parent).direction,
        dist point axisPoint ≤ rho.1 / 10 := by
    apply
      fineOrdinaryTrace_exists_centeredParent_axisPoint_strong
        normalized.final_extremal.delta_pos metricCertificate.rho_pos
        (rich.outputCertificate.refinement.selected.family.tube sourceIndex)
        (rich.outputCertificate.coarse.family.tube parent)
        (rich.outputCertificate.cover.fine_line_class sourceIndex)
        (rich.outputCertificate.cover.coarse_line_class parent)
        (rich.finalParentsCentered parent)
        ratioSmall parentClose ordinarySource ordinarySubset
    · intro tracePoint tracePointMem
      exact
        (normalized.ordinary_axial_window
          ordinaryIndex tracePoint tracePointMem).trans (by norm_num)
    · simpa only [ordinarySource, ordinaryIndex] using pointOrdinary
  rcases axisWitness with ⟨axisPoint, axisPointMem, pointAxis⟩
  exact
    ordinaryTube_gridCube_overlap_volume_lower_strong
      metricCertificate.rho_pos
      (rich.outputCertificate.coarse.family.tube parent)
      coarseCell pointCell axisPointMem pointAxis

/--
A fixed fraction of the selected-incidence cropped mass reaches the canonical
ordinary trace, parent by parent.
-/
theorem selectedIncidence_to_finalCoarseTrace_parent_strong
    (distanceConstant :
      fineParentDistanceConstant = (1 / 100 : ℝ))
    (ratioSmall : delta / rho.1 ≤ 1 / 24)
    (parent : Fin rich.outputCertificate.coarse.family.card) :
    (100 : ENNReal)⁻¹ *
        volume
          (rich.outputCertificate.selectedIncidenceCoarseShading.carrier
            parent) ≤
      volume
        (rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent) := by
  let cells := rich.outputCertificate.selectedParentCells parent
  have cellsDisjoint :
      Set.PairwiseDisjoint (↑cells)
        (fun cell =>
          wz1PaperGridCube rho.1 cell ∩
            (rich.outputCertificate.coarse.family.tube parent).carrier) := by
    intro first _firstMem second _secondMem distinct
    exact
      (wz1PaperGridCube_disjoint distinct).mono
        Set.inter_subset_left Set.inter_subset_left
  have cellsMeasurable :
      ∀ cell ∈ cells,
        MeasurableSet
          (wz1PaperGridCube rho.1 cell ∩
            (rich.outputCertificate.coarse.family.tube parent).carrier) := by
    intro cell _cellMem
    exact
      (wz1PaperGridCube_measurable cell).inter
        Metric.isClosed_cthickening.measurableSet
  have ordinaryCarrierContains :
      (⋃ cell ∈ cells,
          wz1PaperGridCube rho.1 cell ∩
            (rich.outputCertificate.coarse.family.tube parent).carrier) ⊆
        rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent := by
    intro point pointMem
    rcases Set.mem_iUnion₂.mp pointMem with
      ⟨cell, cellMem, pointCell, pointTube⟩
    exact
      ⟨rich.outputCertificate.selectedParentCell_subset_coarseShading
          parent cell cellMem pointCell,
        pointTube⟩
  calc
    (100 : ENNReal)⁻¹ *
          volume
            (rich.outputCertificate.selectedIncidenceCoarseShading.carrier
              parent) =
        ∑ cell ∈ cells,
          (100 : ENNReal)⁻¹ *
            volume (wz1PaperGridCube rho.1 cell) := by
      rw [
        rich.outputCertificate.selectedIncidenceCoarseShading_carrier_volume
          metricCertificate.rho_pos parent
      ]
      calc
        (100 : ENNReal)⁻¹ *
              (((rich.outputCertificate.selectedParentCells parent).card :
                  ENNReal) *
                volume (wz1PaperGridCube rho.1 (0, 0, 0))) =
            ((rich.outputCertificate.selectedParentCells parent).card :
                ENNReal) *
              ((100 : ENNReal)⁻¹ *
                volume (wz1PaperGridCube rho.1 (0, 0, 0))) := by
          ring
        _ =
            ∑ _cell ∈ cells,
              (100 : ENNReal)⁻¹ *
                volume (wz1PaperGridCube rho.1 (0, 0, 0)) := by
          simp [cells, Finset.sum_const]
        _ =
            ∑ cell ∈ cells,
              (100 : ENNReal)⁻¹ *
                volume (wz1PaperGridCube rho.1 cell) := by
          apply Finset.sum_congr rfl
          intro cell _cellMem
          rw [wz1PaperGridCube_volume_eq
            metricCertificate.rho_pos cell (0, 0, 0)]
    _ ≤
        ∑ cell ∈ cells,
          volume
            (wz1PaperGridCube rho.1 cell ∩
              (rich.outputCertificate.coarse.family.tube parent).carrier) := by
      apply Finset.sum_le_sum
      intro cell cellMem
      have frozenMem :=
        rich.selectedParentCells_subset_finalFrozen parent cellMem
      have overlap :=
        rich.finalFrozenParentCell_ordinary_overlap_strong
          distanceConstant ratioSmall parent cell frozenMem
      have cellVolume :=
        wz1PaperGridCube_volume_exact metricCertificate.rho_pos
      rw [wz1PaperGridCube_volume_eq
        metricCertificate.rho_pos cell (0, 0, 0), cellVolume]
      have hundredInv :
          (100 : ENNReal)⁻¹ =
            ENNReal.ofReal (1 / 100 : ℝ) := by
        rw [show (1 / 100 : ℝ) = (100 : ℝ)⁻¹ by norm_num]
        rw [ENNReal.ofReal_inv_of_pos
          (by norm_num : (0 : ℝ) < 100)]
        norm_num
      rw [hundredInv, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 100)]
      exact overlap
    _ =
        volume
          (⋃ cell ∈ cells,
            wz1PaperGridCube rho.1 cell ∩
              (rich.outputCertificate.coarse.family.tube parent).carrier) := by
      rw [MeasureTheory.measure_biUnion_finset
        cellsDisjoint cellsMeasurable]
    _ ≤
        volume
          (rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent) :=
      measure_mono ordinaryCarrierContains

/--
Parentwise ordinary density obtained from packet density and strong frozen-cell
overlap.
-/
theorem finalCoarseOrdinaryTrace_parent_dense
    (distanceConstant :
      fineParentDistanceConstant = (1 / 100 : ℝ))
    (ratioSmall : delta / rho.1 ≤ 1 / 24)
    (rhoSmall : rho.1 ≤ 1 / 24)
    (lambda : ENNReal)
    (scalar :
      PureWZ2Prop62FourDegreeOutputCertificate.SelectedIncidenceDensityScalar
        (densityConstant :=
          Kakeya.realRpowENN delta
            ((packetDensityExponent : ℝ) * eta))
        lambda)
    (parent : Fin rich.outputCertificate.coarse.family.card) :
    ((100 : ENNReal)⁻¹ * lambda) *
          volume
            (rich.outputCertificate.coarse.family.tube parent).carrier ≤
      volume
        (rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent) := by
  have ordinaryToPaper :
      volume
          (rich.outputCertificate.coarse.family.tube parent).carrier ≤
        volume
          (wz1PaperTubeCarrier
            (rich.outputCertificate.coarse.family.tube parent)) := by
    calc
      volume
          (rich.outputCertificate.coarse.family.tube parent).carrier =
          volume
            (wz2PaperInnerTube
              (rich.outputCertificate.coarse.family.tube parent)).carrier := by
        exact
          Kakeya.Streamlined.tube_volume_eq
            (rich.outputCertificate.coarse.family.tube parent)
            (wz2PaperInnerTube
              (rich.outputCertificate.coarse.family.tube parent))
      _ ≤
          volume
            (wz1PaperTubeCarrier
              (rich.outputCertificate.coarse.family.tube parent)) :=
        measure_mono
          (wz2PaperInnerTube_carrier_subset
            metricCertificate.rho_pos
            (rhoSmall.trans (by norm_num))
            (rich.outputCertificate.coarse.family.tube parent)
            (rich.outputCertificate.cover.coarse_line_class parent))
  have selectedDense :=
    rich.outputCertificate.selectedIncidenceCoarseShading_parent_dense
      normalized.final_extremal.delta_pos
      metricCertificate.rho_pos rhoSmall lambda scalar parent
  have selectedToTrace :=
    rich.selectedIncidence_to_finalCoarseTrace_parent_strong
      distanceConstant ratioSmall parent
  calc
    ((100 : ENNReal)⁻¹ * lambda) *
          volume
            (rich.outputCertificate.coarse.family.tube parent).carrier =
        (100 : ENNReal)⁻¹ *
          (lambda *
            volume
              (rich.outputCertificate.coarse.family.tube parent).carrier) := by
      ring
    _ ≤
        (100 : ENNReal)⁻¹ *
          (lambda *
            volume
              (wz1PaperTubeCarrier
                (rich.outputCertificate.coarse.family.tube parent))) := by
      gcongr
    _ ≤
        (100 : ENNReal)⁻¹ *
          volume
            (rich.outputCertificate.selectedIncidenceCoarseShading.carrier
              parent) := by
      gcongr
    _ ≤
        volume
          (rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent) :=
      selectedToTrace

/-- The canonical ordinary trace of every exact final parent has positive volume. -/
theorem finalCoarseOrdinaryTrace_volume_pos_strong
    (distanceConstant :
      fineParentDistanceConstant = (1 / 100 : ℝ))
    (ratioSmall : delta / rho.1 ≤ 1 / 24)
    (parent : Fin rich.outputCertificate.coarse.family.card) :
    0 <
      volume
        (rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent) := by
  rcases rich.finalFrozenParentCells_nonempty parent with
    ⟨coarseCell, cellMem⟩
  have overlap :=
    rich.finalFrozenParentCell_ordinary_overlap_strong
      distanceConstant ratioSmall parent coarseCell cellMem
  have coefficientPos :
      0 < ENNReal.ofReal ((1 / 100 : ℝ) * rho.1 ^ 3) := by
    apply ENNReal.ofReal_pos.mpr
    exact
      mul_pos (by norm_num)
        (pow_pos metricCertificate.rho_pos 3)
  have localPos :
      0 <
        volume
          (wz1PaperGridCube rho.1 coarseCell ∩
            (rich.outputCertificate.coarse.family.tube parent).carrier) :=
    coefficientPos.trans_le overlap
  apply localPos.trans_le
  apply measure_mono
  intro point pointMem
  refine ⟨?_, pointMem.2⟩
  rw [rich.finalFrozenCoarseShading_carrier parent]
  exact
    Set.mem_iUnion₂.mpr
      ⟨coarseCell, cellMem, pointMem.1⟩

/--
The canonical ordinary trace realizes exactly the full frozen cropped coarse
shading under dense cubicalization.
-/
theorem finalCoarseOrdinaryTrace_denseCubicalization
    (distanceConstant :
      fineParentDistanceConstant = (1 / 100 : ℝ))
    (ratioSmall : delta / rho.1 ≤ 1 / 24)
    (parent : Fin rich.outputCertificate.coarse.family.card) :
    rich.outputCertificate.coarseShading.carrier parent =
      pureWZ2DenseCubicalization
        (rich.outputCertificate.coarse.family.tube parent)
        (rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent) := by
  ext point
  let cell := wz1PaperGridIndex rho.1 point
  have cellVolume :
      volume (wz1PaperGridCube rho.1 cell) =
        ENNReal.ofReal (rho.1 ^ 3) := by
    calc
      volume (wz1PaperGridCube rho.1 cell) =
          volume (wz1PaperGridCube rho.1 (0, 0, 0)) :=
        wz1PaperGridCube_volume_eq metricCertificate.rho_pos cell (0, 0, 0)
      _ = ENNReal.ofReal (rho.1 ^ 3) :=
        wz1PaperGridCube_volume_exact metricCertificate.rho_pos
  have tubeVolumePos :
      0 <
        volume
          (rich.outputCertificate.coarse.family.tube parent).carrier :=
    wz2_paper_ordinary_tube_volume_pos
      (rich.outputCertificate.coarse.family.tube parent)
      metricCertificate.rho_pos
  have tubeVolumeTop :
      volume
          (rich.outputCertificate.coarse.family.tube parent).carrier ≠ ⊤ :=
    wz2_paper_ordinary_tube_volume_ne_top
      (rich.outputCertificate.coarse.family.tube parent)
      metricCertificate.rho_pos
  have traceVolumePos :=
    rich.finalCoarseOrdinaryTrace_volume_pos_strong
      distanceConstant ratioSmall parent
  constructor
  · intro pointCoarse
    have wholeCell :
        wz1PaperGridCube rho.1 cell ⊆
          rich.outputCertificate.coarseShading.carrier parent := by
      simpa only [cell] using
        rich.outputCertificate.balanced.coarse_cubical
          parent point pointCoarse
    have cellMem : cell ∈ rich.finalFrozenParentCells parent := by
      have pointUnion := pointCoarse
      rw [rich.finalFrozenCoarseShading_carrier parent] at pointUnion
      rcases Set.mem_iUnion₂.mp pointUnion with
        ⟨frozenCell, frozenMem, pointFrozen⟩
      have indexEq :
          wz1PaperGridIndex rho.1 point = frozenCell :=
        (mem_wz1PaperGridCube rho.1 frozenCell point).mp pointFrozen
      simpa only [cell, indexEq] using frozenMem
    have traceLeTube :
        volume
            (rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent) ≤
          volume
            (rich.outputCertificate.coarse.family.tube parent).carrier :=
      measure_mono
        (rich.outputCertificate.finalCoarseOrdinaryTrace.subset_body parent)
    have traceRatioLe :
        volume
              (rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent) *
            (volume
              (rich.outputCertificate.coarse.family.tube parent).carrier)⁻¹ ≤
          1 := by
      calc
        _ ≤
            volume
                (rich.outputCertificate.coarse.family.tube parent).carrier *
              (volume
                (rich.outputCertificate.coarse.family.tube parent).carrier)⁻¹ := by
          gcongr
        _ = 1 :=
          ENNReal.mul_inv_cancel tubeVolumePos.ne' tubeVolumeTop
    have localEq :
        volume
            (rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent ∩
              wz1PaperGridCube rho.1 cell) =
          volume
            (wz1PaperGridCube rho.1 cell ∩
              (rich.outputCertificate.coarse.family.tube parent).carrier) := by
      congr 1
      ext localPoint
      constructor
      · rintro ⟨⟨_pointCoarse, pointTube⟩, pointCell⟩
        exact ⟨pointCell, pointTube⟩
      · rintro ⟨pointCell, pointTube⟩
        exact ⟨⟨wholeCell pointCell, pointTube⟩, pointCell⟩
    change
      wz1PaperGridCube rho.1 cell ⊆
          wz1PaperTubeCarrier
            (rich.outputCertificate.coarse.family.tube parent) ∧
        (100 : ENNReal)⁻¹ *
              volume
                (rich.outputCertificate.finalCoarseOrdinaryTrace.carrier
                  parent) *
              (volume
                (rich.outputCertificate.coarse.family.tube parent).carrier)⁻¹ *
              volume (wz1PaperGridCube rho.1 cell) ≤
            volume
              (rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent ∩
                wz1PaperGridCube rho.1 cell)
    constructor
    · exact wholeCell.trans
        (rich.outputCertificate.coarseShading.subset_body parent)
    · rw [localEq, cellVolume]
      calc
        (100 : ENNReal)⁻¹ *
              volume
                (rich.outputCertificate.finalCoarseOrdinaryTrace.carrier
                  parent) *
              (volume
                (rich.outputCertificate.coarse.family.tube parent).carrier)⁻¹ *
              ENNReal.ofReal (rho.1 ^ 3) ≤
            (100 : ENNReal)⁻¹ * 1 *
              ENNReal.ofReal (rho.1 ^ 3) := by
          calc
            _ =
                (100 : ENNReal)⁻¹ *
                  (volume
                      (rich.outputCertificate.finalCoarseOrdinaryTrace.carrier
                        parent) *
                    (volume
                      (rich.outputCertificate.coarse.family.tube
                        parent).carrier)⁻¹) *
                  ENNReal.ofReal (rho.1 ^ 3) := by ring
            _ ≤
                (100 : ENNReal)⁻¹ * 1 *
                  ENNReal.ofReal (rho.1 ^ 3) := by
              gcongr
        _ = ENNReal.ofReal ((1 / 100 : ℝ) * rho.1 ^ 3) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 100)]
          have hundredInv :
              (100 : ENNReal)⁻¹ =
                ENNReal.ofReal (1 / 100 : ℝ) := by
            rw [show (1 / 100 : ℝ) = (100 : ℝ)⁻¹ by norm_num]
            rw [ENNReal.ofReal_inv_of_pos
              (by norm_num : (0 : ℝ) < 100)]
            norm_num
          rw [hundredInv]
          simp
        _ ≤
            volume
              (wz1PaperGridCube rho.1 cell ∩
                (rich.outputCertificate.coarse.family.tube parent).carrier) :=
          rich.finalFrozenParentCell_ordinary_overlap_strong
            distanceConstant ratioSmall parent cell cellMem
  · intro pointDense
    change
      wz1PaperGridCube rho.1 cell ⊆
          wz1PaperTubeCarrier
            (rich.outputCertificate.coarse.family.tube parent) ∧
        (100 : ENNReal)⁻¹ *
              volume
                (rich.outputCertificate.finalCoarseOrdinaryTrace.carrier
                  parent) *
              (volume
                (rich.outputCertificate.coarse.family.tube parent).carrier)⁻¹ *
              volume (wz1PaperGridCube rho.1 cell) ≤
            volume
              (rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent ∩
                wz1PaperGridCube rho.1 cell) at pointDense
    have thresholdPos :
        0 <
          (100 : ENNReal)⁻¹ *
              volume
                (rich.outputCertificate.finalCoarseOrdinaryTrace.carrier
                  parent) *
              (volume
                (rich.outputCertificate.coarse.family.tube parent).carrier)⁻¹ *
              volume (wz1PaperGridCube rho.1 cell) := by
      exact
        ENNReal.mul_pos
          (ENNReal.mul_pos
            (ENNReal.mul_pos
              (ENNReal.inv_ne_zero.mpr (by norm_num))
              traceVolumePos.ne').ne'
            (ENNReal.inv_ne_zero.mpr tubeVolumeTop)).ne'
          (wz1PaperGridCube_volume_pos
            metricCertificate.rho_pos cell).ne'
    have localPos :
        0 <
          volume
            (rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent ∩
              wz1PaperGridCube rho.1 cell) :=
      thresholdPos.trans_le pointDense.2
    rcases nonempty_of_measure_ne_zero localPos.ne' with
      ⟨sourcePoint, sourceTrace, sourceCell⟩
    have sourceIndexEq :
        wz1PaperGridIndex rho.1 sourcePoint = cell :=
      (mem_wz1PaperGridCube rho.1 cell sourcePoint).mp sourceCell
    have wholeSourceCell :=
      rich.outputCertificate.balanced.coarse_cubical
        parent sourcePoint sourceTrace.1
    have pointCell :
        point ∈ wz1PaperGridCube rho.1 cell :=
      (mem_wz1PaperGridCube rho.1 cell point).mpr rfl
    rw [sourceIndexEq] at wholeSourceCell
    exact wholeSourceCell pointCell

/-- Centered exact final parents have base norm at most four. -/
theorem finalCoarse_bounded_base_four :
    HasBoundedBase rich.outputCertificate.coarse.family 4 := by
  intro parent
  let tube := rich.outputCertificate.coarse.family.tube parent
  let midpoint := wz2PaperTubeMidpoint tube
  have midpointNorm : ‖midpoint‖ ≤ 1 := by
    dsimp only [midpoint, tube]
    rw [← rich.finalParentsCentered parent]
    exact
      wz2PaperCenteredLineTube_midpoint_norm_le_one
        (rich.outputCertificate.cover.coarse_line_class parent)
  have baseEq :
      tube.base =
        midpoint - (1 / 2 : ℝ) • tube.direction := by
    have midpointDefinition :
        midpoint =
          tube.base + (1 / 2 : ℝ) • tube.direction := by
      rfl
    rw [midpointDefinition]
    abel
  rw [baseEq]
  calc
    ‖midpoint - (1 / 2 : ℝ) • tube.direction‖ ≤
        ‖midpoint‖ + ‖(1 / 2 : ℝ) • tube.direction‖ :=
      norm_sub_le _ _
    _ = ‖midpoint‖ + 1 / 2 := by
      rw [norm_smul, tube.direction_unit]
      norm_num
    _ ≤ 4 := by linarith

/--
The ordinary carrier of a centered final parent lies in its corresponding
cropped paper carrier.
-/
theorem finalCoarseOrdinaryTrace_carrier_subset_paper
    (parent : Fin rich.outputCertificate.coarse.family.card) :
    rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent ⊆
      wz1PaperTubeCarrier
        (rich.outputCertificate.coarse.family.tube parent) := by
  intro point pointMem
  exact
    rich.outputCertificate.coarseShading.subset_body parent pointMem.1

/--
For centered line-class parents at scale at most `1 / 24`, the full ordinary
unit-segment carrier lies in the cropped paper carrier.
-/
theorem finalCoarse_fullOrdinaryCarrier_subset_paper
    (rhoSmall : rho.1 ≤ 1 / 24)
    (parent : Fin rich.outputCertificate.coarse.family.card) :
    (rich.outputCertificate.coarse.family.tube parent).carrier ⊆
      wz1PaperTubeCarrier
        (rich.outputCertificate.coarse.family.tube parent) := by
  let tube := rich.outputCertificate.coarse.family.tube parent
  have tubeLine : WZ1PaperTubeInLineClass tube :=
    rich.outputCertificate.cover.coarse_line_class parent
  have centered :
      wz2PaperCenteredLineTube (targetScale := rho.1) tube = tube :=
    rich.finalParentsCentered parent
  have directionEq :
      tube.direction = wz1PaperDirection tube := by
    have raw :
        (wz2PaperCenteredLineTube
          (targetScale := rho.1) tube).direction =
            wz1PaperDirection tube := rfl
    rwa [centered] at raw
  have baseEq :
      tube.base =
        wz1TubeAxisZeroPoint tube -
          (1 / 2 : ℝ) • wz1PaperDirection tube := by
    have raw :=
      congrArg Kakeya.DeltaTube.base centered
    change
      wz1TubeAxisZeroPoint tube -
          (1 / 2 : ℝ) • wz1PaperDirection tube =
        tube.base at raw
    exact raw.symm
  intro point pointMem
  rcases exists_closest_on_axis
      metricCertificate.rho_pos.le tube point pointMem with
    ⟨parameter, parameterMem, pointAxis⟩
  let axisPoint := tube.base + parameter • tube.direction
  have axisPointSegment :
      axisPoint ∈ Kakeya.unitSegment tube.base tube.direction :=
    ⟨parameter, parameterMem, rfl⟩
  have axisPointLine :
      axisPoint ∈ tubeAxisLine tube :=
    wz2_paper_unitSegment_subset_axisLine tube axisPointSegment
  have pointAxisLe : dist point axisPoint ≤ rho.1 := by
    simpa [axisPoint] using pointAxis
  constructor
  · exact
      Metric.mem_cthickening_of_dist_le
        point axisPoint (6 * rho.1) (tubeAxisLine tube)
        axisPointLine
        (pointAxisLe.trans <| by
          nlinarith [metricCertificate.rho_pos])
  · have parameterBound :
        |parameter - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [parameterMem.1, parameterMem.2]
    have axisEq :
        axisPoint =
          wz1TubeAxisZeroPoint tube +
            (parameter - 1 / 2) • wz1PaperDirection tube := by
      dsimp only [axisPoint]
      rw [baseEq, directionEq]
      module
    have directionCoord :
        ∀ coordinate : Fin 3,
          |wz1PaperDirection tube coordinate| ≤ 1 := by
      intro coordinate
      exact
        (PiLp.norm_apply_le (wz1PaperDirection tube) coordinate).trans_eq
          (wz1PaperDirection_norm tube)
    have pointDifference :
        ∀ coordinate : Fin 3,
          |point coordinate - axisPoint coordinate| ≤ rho.1 := by
      intro coordinate
      exact (abs_coord_sub_le_dist coordinate).trans pointAxisLe
    have axisZeroTwo :
        wz1TubeAxisZeroPoint tube (2 : Fin 3) = 0 :=
      wz1TubeAxisZeroPoint_coord_two tube tubeLine.vertical
    have axisZeroBound :
        ∀ coordinate : Fin 3,
          |wz1TubeAxisZeroPoint tube coordinate| ≤ 1 / 3 := by
      intro coordinate
      fin_cases coordinate
      · exact tubeLine.2.1
      · exact tubeLine.2.2
      · simp [axisZeroTwo]
    have axisBound :
        ∀ coordinate : Fin 3,
          |axisPoint coordinate| ≤ 5 / 6 := by
      intro coordinate
      rw [axisEq]
      have triangle :
          |wz1TubeAxisZeroPoint tube coordinate +
              (parameter - 1 / 2) *
                wz1PaperDirection tube coordinate| ≤
            |wz1TubeAxisZeroPoint tube coordinate| +
              |parameter - 1 / 2| *
                |wz1PaperDirection tube coordinate| := by
        calc
          _ ≤
              |wz1TubeAxisZeroPoint tube coordinate| +
                |(parameter - 1 / 2) *
                  wz1PaperDirection tube coordinate| :=
            abs_add_le _ _
          _ = _ := by rw [abs_mul]
      exact triangle.trans <| by
        nlinarith [axisZeroBound coordinate, parameterBound,
          directionCoord coordinate,
          abs_nonneg (wz1TubeAxisZeroPoint tube coordinate),
          abs_nonneg (wz1PaperDirection tube coordinate)]
    have pointBound :
        ∀ coordinate : Fin 3, |point coordinate| ≤ 1 := by
      intro coordinate
      have triangle :
          |point coordinate| ≤
            |axisPoint coordinate| +
              |point coordinate - axisPoint coordinate| := by
        calc
          |point coordinate| =
              |axisPoint coordinate +
                (point coordinate - axisPoint coordinate)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      exact triangle.trans <| by
        nlinarith [axisBound coordinate, pointDifference coordinate]
    simpa [Kakeya.Streamlined.axisBox] using
      ⟨pointBound 0, pointBound 1, pointBound 2⟩

/-- Two points in one half-open `rho`-cube differ by less than `rho` in height. -/
private theorem same_gridCube_height_sub_lt
    {rho : ℝ}
    (rhoPos : 0 < rho)
    (cell : WZ2PaperCellIndex)
    {first second : Point3}
    (firstMem : first ∈ wz1PaperGridCube rho cell)
    (secondMem : second ∈ wz1PaperGridCube rho cell) :
    |first (2 : Fin 3) - second (2 : Fin 3)| < rho := by
  rw [wz1PaperGridCube_eq_Ico rhoPos cell] at firstMem secondMem
  have firstLower := firstMem.2.2.2.2.1
  have firstUpper := firstMem.2.2.2.2.2
  have secondLower := secondMem.2.2.2.2.1
  have secondUpper := secondMem.2.2.2.2.2
  rw [abs_lt]
  constructor <;> linarith

/--
The first coarse ordinary trace remains inside the reusable quarter-height
window when the root normalization supplies its stronger eighth-height
certificate.
-/
theorem finalCoarseOrdinaryTrace_axial_window
    (rootAxialWindow :
      ∀ index point,
        point ∈
            normalized.frame ''
              normalized.ordinaryRefined.carrier index →
          |point (2 : Fin 3)| ≤ 1 / 8)
    (rhoSmall : rho.1 ≤ 1 / 24)
    (parent : Fin rich.outputCertificate.coarse.family.card)
    (point : Point3)
    (pointTrace :
      point ∈
        rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent) :
    |point (2 : Fin 3)| ≤ 1 / 4 := by
  have pointCoarse :
      point ∈ rich.outputCertificate.coarseShading.carrier parent :=
    pointTrace.1
  rw [rich.finalFrozenCoarseShading_carrier parent] at pointCoarse
  rcases Set.mem_iUnion₂.mp pointCoarse with
    ⟨coarseCell, cellMem, pointCell⟩
  rcases
      rich.finalFrozenParentCell_exists_ordinaryPoint
        parent coarseCell cellMem
    with ⟨sourceIndex, _parentEq, ordinaryPoint,
      ordinaryPointSource, ordinaryPointCell⟩
  let ordinaryIndex :=
    PureWZ2CroppedCriticalNormalizationData.ordinaryIndex
      normalized rich.fixedGridComposedSelected sourceIndex
  have ordinaryHeight :
      |ordinaryPoint (2 : Fin 3)| ≤ 1 / 8 := by
    exact rootAxialWindow ordinaryIndex ordinaryPoint ordinaryPointSource
  have heightDifference :
      |point (2 : Fin 3) - ordinaryPoint (2 : Fin 3)| < rho.1 :=
    same_gridCube_height_sub_lt
      metricCertificate.rho_pos coarseCell pointCell ordinaryPointCell
  have triangle :
      |point (2 : Fin 3)| ≤
        |ordinaryPoint (2 : Fin 3)| +
          |point (2 : Fin 3) - ordinaryPoint (2 : Fin 3)| := by
    have h :=
      abs_add_le
        (ordinaryPoint (2 : Fin 3))
        (point (2 : Fin 3) - ordinaryPoint (2 : Fin 3))
    have sumEq :
        ordinaryPoint (2 : Fin 3) +
            (point (2 : Fin 3) - ordinaryPoint (2 : Fin 3)) =
          point (2 : Fin 3) := by
      ring
    rwa [sumEq] at h
  linarith

/-- A root axial certificate carrying one full coarse-grid cell of slack
survives the frozen coarse cubicalization with the original `1 / 8` bound.
This is the sharp provenance form needed by a subsequent re-entry: the
coarse point is compared with an actual root ordinary point in the same
`rho`-cube, and exactly that `rho` error is consumed. -/
theorem finalCoarseOrdinaryTrace_axial_window_of_margin
    (rootAxialMargin :
      ∀ index point,
        point ∈
            normalized.frame ''
              normalized.ordinaryRefined.carrier index →
          |point (2 : Fin 3)| + rho.1 ≤ 1 / 8)
    (parent : Fin rich.outputCertificate.coarse.family.card)
    (point : Point3)
    (pointTrace :
      point ∈
        rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent) :
    |point (2 : Fin 3)| ≤ 1 / 8 := by
  have pointCoarse :
      point ∈ rich.outputCertificate.coarseShading.carrier parent :=
    pointTrace.1
  rw [rich.finalFrozenCoarseShading_carrier parent] at pointCoarse
  rcases Set.mem_iUnion₂.mp pointCoarse with
    ⟨coarseCell, cellMem, pointCell⟩
  rcases
      rich.finalFrozenParentCell_exists_ordinaryPoint
        parent coarseCell cellMem
    with ⟨sourceIndex, _parentEq, ordinaryPoint,
      ordinaryPointSource, ordinaryPointCell⟩
  let ordinaryIndex :=
    PureWZ2CroppedCriticalNormalizationData.ordinaryIndex
      normalized rich.fixedGridComposedSelected sourceIndex
  have ordinaryMargin :
      |ordinaryPoint (2 : Fin 3)| + rho.1 ≤ 1 / 8 :=
    rootAxialMargin ordinaryIndex ordinaryPoint ordinaryPointSource
  have heightDifference :
      |point (2 : Fin 3) - ordinaryPoint (2 : Fin 3)| < rho.1 :=
    same_gridCube_height_sub_lt
      metricCertificate.rho_pos coarseCell pointCell ordinaryPointCell
  have triangle :
      |point (2 : Fin 3)| ≤
        |ordinaryPoint (2 : Fin 3)| +
          |point (2 : Fin 3) - ordinaryPoint (2 : Fin 3)| := by
    have h :=
      abs_add_le
        (ordinaryPoint (2 : Fin 3))
        (point (2 : Fin 3) - ordinaryPoint (2 : Fin 3))
    have sumEq :
        ordinaryPoint (2 : Fin 3) +
            (point (2 : Fin 3) - ordinaryPoint (2 : Fin 3)) =
          point (2 : Fin 3) := by
      ring
    rwa [sumEq] at h
  linarith

/--
Package the exact final coarse pair as re-entry data once the scalar loss
schedule, ordinary extremality, axial window, and bounded-base facts are
available.
-/
noncomputable def exactCoarseReentryData
    (distanceConstant :
      fineParentDistanceConstant = (1 / 100 : ℝ))
    (ratioSmall : delta / rho.1 ≤ 1 / 24)
    (rhoSmall : rho.1 ≤ 1 / 24)
    (lambda : ENNReal)
    (lambdaPos : 0 < lambda)
    (scalar :
      PureWZ2Prop62FourDegreeOutputCertificate.SelectedIncidenceDensityScalar
        (densityConstant :=
          Kakeya.realRpowENN delta
            ((packetDensityExponent : ℝ) * eta))
        lambda)
    (reentrySourceLoss reentryNormalizationLoss : ℝ)
    (sourceLossPos : 0 < reentrySourceLoss)
    (normalizationLossPos : 0 < reentryNormalizationLoss)
    (sourceLossHalf :
      reentrySourceLoss ≤ reentryNormalizationLoss / 2)
    (ordinaryDensityBudget :
      Kakeya.realRpowENN rho.1 reentrySourceLoss / 2 ≤
        (100 : ENNReal)⁻¹ * lambda)
    (ordinaryExtremal :
      WZ2PaperPureIsExtremal
        sigma reentrySourceLoss
        rich.outputCertificate.coarse.family
        rich.outputCertificate.finalCoarseOrdinaryTrace)
    (ordinaryAxialWindow :
      ∀ parent point,
        point ∈
            rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent →
          |point (2 : Fin 3)| ≤ 1 / 4)
    (croppedTopLevelCWA :
      WZ2PaperConvexWolffBound
        rich.outputCertificate.coarse.family
        (Kakeya.realRpowENN rho.1 (-reentryNormalizationLoss)))
    (croppedExtremal :
      WZ2PaperCroppedIsExtremal
        sigma reentryNormalizationLoss
        rich.outputCertificate.coarse.family
        rich.outputCertificate.coarseShading) :
    PureWZ2PropStickyReentryData
      (sigma := sigma)
      rich.outputCertificate.coarseShading 0
      reentrySourceLoss reentryNormalizationLoss := by
  let ordinarySource :
      PureWZ2ExtremalConfiguration
        sigma reentrySourceLoss rho.1 :=
    {
      family := rich.outputCertificate.coarse.family
      shading := rich.outputCertificate.finalCoarseOrdinaryTrace
      extremal := ordinaryExtremal
    }
  let selected :
      Kakeya.Streamlined.TubeSubfamily ordinarySource.family :=
    {
      family := ordinarySource.family
      embedding := Function.Embedding.refl _
      tube_eq := fun _ => rfl
    }
  refine
    {
      sourceLoss_pos := sourceLossPos
      normalizationLoss_pos := normalizationLossPos
      sourceLoss_le_half := sourceLossHalf
      ordinarySource := ordinarySource
      geometry := {
        selected := selected
        selected_nonempty := ordinaryExtremal.nonempty
        ordinaryRefined := ordinarySource.shading
        ordinary_subshading := by
          intro index point pointMem
          exact pointMem
        retained_mass := by
          simp [selected, ordinarySource, wz2PaperPureRefinementFraction]
        frame := AffineIsometryEquiv.refl ℝ Point3
        indexEquiv := Equiv.refl _
        ordinary_carrier_image_eq := by
          intro index
          change
            (rich.outputCertificate.coarse.family.tube index).carrier =
              (AffineIsometryEquiv.refl ℝ Point3) ''
                (rich.outputCertificate.coarse.family.tube index).carrier
          simp
        ordinaryDensity := (100 : ENNReal)⁻¹ * lambda
        ordinaryDensity_pos := by
          exact ENNReal.mul_pos (by norm_num) lambdaPos.ne'
        ordinary_per_tube := by
          intro parent
          change
            ((100 : ENNReal)⁻¹ * lambda) *
                  volume
                    (rich.outputCertificate.coarse.family.tube parent).carrier ≤
              volume
                (rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent)
          exact
            rich.finalCoarseOrdinaryTrace_parent_dense
              distanceConstant ratioSmall rhoSmall lambda scalar parent
        ordinary_axial_window := by
          intro parent point pointMem
          change
            point ∈
                (AffineIsometryEquiv.refl ℝ Point3) ''
                  rich.outputCertificate.finalCoarseOrdinaryTrace.carrier
                    parent at pointMem
          rcases pointMem with ⟨sourcePoint, sourcePointMem, rfl⟩
          simpa using
            ordinaryAxialWindow parent sourcePoint sourcePointMem
        cropped_carrier_eq_dense_cubicalization := by
          intro parent
          change
            rich.outputCertificate.coarseShading.carrier parent =
              pureWZ2DenseCubicalization
                (rich.outputCertificate.coarse.family.tube parent)
                ((AffineIsometryEquiv.refl ℝ Point3) ''
                  rich.outputCertificate.finalCoarseOrdinaryTrace.carrier
                    parent)
          simpa using
            rich.finalCoarseOrdinaryTrace_denseCubicalization
              distanceConstant ratioSmall parent
        cropped_cubical :=
          rich.outputCertificate.balanced.coarse_cubical
        line_class := rich.outputCertificate.cover.coarse_line_class
        ordinary_cell_containment := by
          intro parent cell cellMeets
          rcases cellMeets with ⟨point, pointFrame, pointCell⟩
          rcases pointFrame with
            ⟨sourcePoint, pointTrace, pointEq⟩
          subst point
          have wholeCell :=
            rich.outputCertificate.balanced.coarse_cubical
              parent sourcePoint pointTrace.1
          have pointIndex :
              wz1PaperGridIndex rho.1 sourcePoint = cell :=
            (mem_wz1PaperGridCube rho.1 cell sourcePoint).mp pointCell
          have containment :=
            wholeCell.trans
              (rich.outputCertificate.coarseShading.subset_body parent)
          rw [pointIndex] at containment
          change
            wz1PaperGridCube rho.1 cell ⊆
              wz1PaperTubeCarrier
                (rich.outputCertificate.coarse.family.tube
                  ((Equiv.refl _) parent))
          have parentRefl :
              (Equiv.refl
                (Fin rich.outputCertificate.coarse.family.card)) parent =
                parent := rfl
          rw [parentRefl]
          exact containment
        ordinary_bounded_base := by
          exact rich.finalCoarse_bounded_base_four
      }
      ordinary_density_budget := ordinaryDensityBudget
      cropped_top_level_cwa := croppedTopLevelCWA
      cropped_extremal := croppedExtremal
    }

end Prop62V4RichCertificateCompanionData

end Kakeya.Assouad.Prop62PaperAudit.V4

end
