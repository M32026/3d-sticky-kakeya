import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CanonicalParameterSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CanonicalBalancingFromDensity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreeOutputCertificate
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FixedGridCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4FourDegreeThresholdCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PacketCellMultiplicity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PacketCellLocalInput
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PacketCellParentMassUpper
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4RatioSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4SchedulePowerCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4Pipeline
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TerminalParentCWABound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TwoLayerCardinality
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment

/-!
# Proposition 6.2: feed metric parents into the four-degree construction

The fixed-grid cleanup is performed before the metric-parent selection.  Its
per-tube shaded masses are the weights used by the one-pass ancestry
construction.  After the final metric core is selected, the shading is only
reindexed along the two existing tube-subfamily embeddings; no further tube
selection occurs.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62MetricParentsOutput

variable
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData fine scale C}
    {sourceShading : WZ1PaperTubeShading fine}
    {deltaPos : 0 < delta}
    (cleanup :
      PureWZ2Prop62FixedGridCleanupData
        (rho := rho) sourceShading deltaPos)
    (output :
      PureWZ2Prop62MetricParentsOutput (rho := rho) oldData
        (fun source => volume (cleanup.refined.carrier source)) 10)

/-- The final metric core viewed as one subfamily of the pre-cleanup family. -/
noncomputable def finalFineSubfamily :
    Kakeya.Streamlined.TubeSubfamily fine :=
  output.metric.mesh.complete.selectedFine.toTubeSubfamily.comp
    output.restriction.fineSelected

/--
The fixed-grid shading restricted to the final metric core.  This changes
only the index type; every surviving carrier is literally the corresponding
carrier of `cleanup.refined`.
-/
noncomputable def finalFineShading :
    WZ1PaperTubeShading output.restriction.fineSelected.family :=
  restrictPaperShading
    (output.finalFineSubfamily cleanup)
    cleanup.refined

@[simp] theorem finalFineShading_carrier
    (source : Fin output.restriction.fineSelected.family.card) :
    (output.finalFineShading cleanup).carrier source =
      cleanup.refined.carrier
        (output.metric.mesh.complete.selectedFine.embedding
          (output.restriction.fineSelected.embedding source)) := by
  rfl

theorem finalFineShading_mass :
    (output.finalFineShading cleanup).mass =
      ∑ source : Fin output.restriction.fineSelected.family.card,
        volume
          (cleanup.refined.carrier
            (output.metric.mesh.complete.selectedFine.embedding
              (output.restriction.fineSelected.embedding source))) := by
  rfl

theorem finalFineFamily_enncard_le_ambient :
    output.restriction.fineSelected.family.enncard ≤ fine.enncard := by
  have first :
      output.restriction.fineSelected.family.card ≤
        output.metric.selectedFine.card := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective
        output.restriction.fineSelected.embedding
        output.restriction.fineSelected.embedding.injective
  have second :
      output.metric.selectedFine.card ≤ fine.card := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective
        output.metric.mesh.complete.selectedFine.embedding
        output.metric.mesh.complete.selectedFine.embedding.injective
  change
    (output.restriction.fineSelected.family.card : ENNReal) ≤
      (fine.card : ENNReal)
  exact_mod_cast first.trans second

theorem finalFineFamily_nonempty :
    output.restriction.fineSelected.family.Nonempty := by
  rcases output.restriction.core_nonempty with ⟨source, sourceMem⟩
  have sourceImage :
      source ∈
        Finset.image
          output.restriction.fineSelected.embedding Finset.univ := by
    rw [output.restriction.fine_image_univ]
    exact sourceMem
  rcases Finset.mem_image.mp sourceImage with
    ⟨selected, _selectedMem, _⟩
  exact Nat.zero_lt_of_lt selected.isLt

theorem finalFineFamily_ordinary_distinct
    (ambientDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct fine) :
    WZ2PaperOrdinaryIsEssentiallyDistinct
      output.restriction.fineSelected.family := by
  let selected : WZ2PaperPureTubeSubfamily fine :=
    {
      family := output.restriction.fineSelected.family
      embedding := (output.finalFineSubfamily cleanup).embedding
      tube_eq := (output.finalFineSubfamily cleanup).tube_eq
    }
  exact ambientDistinct.subfamily selected

theorem finalFineFamily_bounded_base
    (ambientBoundedBase : HasBoundedBase fine 4) :
    HasBoundedBase output.restriction.fineSelected.family 4 := by
  intro source
  rw [output.restriction.fineSelected.tube_eq,
    output.metric.mesh.complete.selectedFine.tube_eq]
  exact
    ambientBoundedBase
      (output.metric.mesh.complete.selectedFine.embedding
        (output.restriction.fineSelected.embedding source))

/--
The fixed-grid half-mass estimate and the canonical metric-core
`log^-10` estimate preserve an explicit aggregate density on the exact
shading fed to the four-degree argument.
-/
theorem finalFineShading_density_from_source
    (densityConstant : ENNReal)
    (sourceDensity :
      densityConstant * fine.enncard *
          Kakeya.realRpowENN delta 2 ≤
        sourceShading.mass) :
    ((wz2PaperPureRefinementFraction delta 10 / 2) *
        densityConstant) *
          output.restriction.fineSelected.family.enncard *
          Kakeya.realRpowENN delta 2 ≤
      (output.finalFineShading cleanup).mass := by
  have finalCardDensity :
      densityConstant *
          output.restriction.fineSelected.family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        sourceShading.mass := by
    calc
      densityConstant *
            output.restriction.fineSelected.family.enncard *
            Kakeya.realRpowENN delta 2 ≤
          densityConstant * fine.enncard *
            Kakeya.realRpowENN delta 2 := by
        gcongr
        exact output.finalFineFamily_enncard_le_ambient cleanup
      _ ≤ sourceShading.mass := sourceDensity
  have cleanupDensity :
      (densityConstant *
          output.restriction.fineSelected.family.enncard *
          Kakeya.realRpowENN delta 2) / 2 ≤
        cleanup.refined.mass :=
    (ENNReal.div_le_div_right finalCardDensity 2).trans
      cleanup.mass_retention
  calc
    ((wz2PaperPureRefinementFraction delta 10 / 2) *
          densityConstant) *
            output.restriction.fineSelected.family.enncard *
            Kakeya.realRpowENN delta 2 =
        wz2PaperPureRefinementFraction delta 10 *
          ((densityConstant *
            output.restriction.fineSelected.family.enncard *
            Kakeya.realRpowENN delta 2) / 2) := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤
        wz2PaperPureRefinementFraction delta 10 *
          cleanup.refined.mass := by
      gcongr
    _ ≤ (output.finalFineShading cleanup).mass := by
      rw [output.finalFineShading_mass cleanup]
      exact output.core_weight_retention

/--
The normalized cropped extremal density supplies the source-density premise
used by `finalFineShading_density_from_source`.  The conclusion keeps the
literal fixed-grid and metric-core factor `log^-10 / 2`.
-/
theorem finalFineShading_density_from_croppedExtremal
    {sigma outputLoss : ℝ}
    (deltaSmall : delta ≤ 1 / 12)
    (lineClass : WZ1PaperIsLineClass fine)
    (extremal :
      WZ2PaperCroppedIsExtremal
        sigma outputLoss fine sourceShading) :
    ((wz2PaperPureRefinementFraction delta 10 / 2) *
        Kakeya.realRpowENN delta outputLoss) *
          output.restriction.fineSelected.family.enncard *
          Kakeya.realRpowENN delta 2 ≤
      (output.finalFineShading cleanup).mass := by
  apply
    output.finalFineShading_density_from_source cleanup
      (Kakeya.realRpowENN delta outputLoss)
  calc
    Kakeya.realRpowENN delta outputLoss *
          fine.enncard *
          Kakeya.realRpowENN delta 2 =
        Kakeya.realRpowENN delta outputLoss *
          (fine.enncard * Kakeya.realRpowENN delta 2) := by
      ring
    _ ≤
        Kakeya.realRpowENN delta outputLoss *
          (wz1PaperBodyFamily fine).mass := by
      gcongr
      exact
        pureWZ2_prop62_paper_body_mass_lower
          deltaPos deltaSmall lineClass
    _ ≤ sourceShading.mass := extremal.dense

/--
Power-form density on the exact final fine shading.  The only asymptotic input
is the displayed scalar absorption of the explicit `log^-10 / 2` loss.
-/
theorem finalFineShading_power_density_from_croppedExtremal
    {sigma outputLoss densityExponent : ℝ}
    (deltaSmall : delta ≤ 1 / 12)
    (lineClass : WZ1PaperIsLineClass fine)
    (extremal :
      WZ2PaperCroppedIsExtremal
        sigma outputLoss fine sourceShading)
    (densityAbsorption :
      Kakeya.realRpowENN delta densityExponent ≤
        (wz2PaperPureRefinementFraction delta 10 / 2) *
          Kakeya.realRpowENN delta outputLoss) :
    Kakeya.realRpowENN delta densityExponent *
          output.restriction.fineSelected.family.enncard *
          Kakeya.realRpowENN delta 2 ≤
      (output.finalFineShading cleanup).mass := by
  calc
    Kakeya.realRpowENN delta densityExponent *
          output.restriction.fineSelected.family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        ((wz2PaperPureRefinementFraction delta 10 / 2) *
          Kakeya.realRpowENN delta outputLoss) *
          output.restriction.fineSelected.family.enncard *
          Kakeya.realRpowENN delta 2 := by
      gcongr
    _ ≤ (output.finalFineShading cleanup).mass :=
      output.finalFineShading_density_from_croppedExtremal
        cleanup deltaSmall lineClass extremal

theorem finalFineShading_cubical :
    WZ1PaperIsCubicalShading
      (output.finalFineShading cleanup) :=
  restrictPaperShading_cubical
    (output.finalFineSubfamily cleanup) cleanup.cubical

theorem finalFineShading_mass_pos :
    0 < cleanup.refined.mass →
      0 < (output.finalFineShading cleanup).mass := by
  intro refinedMassPos
  have fractionPos :
      0 < wz2PaperPureRefinementFraction delta 10 := by
    unfold wz2PaperPureRefinementFraction
    exact
      ENNReal.pow_pos
        (ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top) 10
  have sourcePos :
      0 <
        wz2PaperPureRefinementFraction delta 10 *
          cleanup.refined.mass :=
    ENNReal.mul_pos fractionPos.ne' refinedMassPos.ne'
  apply sourcePos.trans_le
  change
    wz2PaperPureRefinementFraction delta 10 *
          (∑ source : Fin fine.card,
            volume (cleanup.refined.carrier source)) ≤
      ∑ source : Fin output.restriction.fineSelected.family.card,
        volume
          (cleanup.refined.carrier
            (output.metric.mesh.complete.selectedFine.embedding
              (output.restriction.fineSelected.embedding source)))
  exact output.core_weight_retention

theorem finalFineCells_nonempty
    (refinedMassPos : 0 < cleanup.refined.mass) :
    (wz1PaperActiveCells
      (output.finalFineShading cleanup) deltaPos).Nonempty := by
  by_contra notNonempty
  have cellsEmpty :
      wz1PaperActiveCells
          (output.finalFineShading cleanup) deltaPos =
        ∅ := by
    simpa [Finset.not_nonempty_iff_eq_empty] using notNonempty
  have unionEmpty :
      (output.finalFineShading cleanup).union = ∅ := by
    rw [output.finalFineShading_cubical cleanup
      |>.union_eq_activeCells deltaPos, cellsEmpty]
    simp
  have massZero :
      (output.finalFineShading cleanup).mass = 0 := by
    change
      (∑ source : Fin output.restriction.fineSelected.family.card,
        volume ((output.finalFineShading cleanup).carrier source)) = 0
    apply Finset.sum_eq_zero
    intro source _sourceMem
    have carrierEmpty :
        (output.finalFineShading cleanup).carrier source = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro point pointMem
      have pointUnion :
          point ∈ (output.finalFineShading cleanup).union :=
        ⟨source, pointMem⟩
      rw [unionEmpty] at pointUnion
      exact pointUnion
    rw [carrierEmpty]
    simp
  have massPos :=
    output.finalFineShading_mass_pos cleanup refinedMassPos
  rw [massZero] at massPos
  exact (lt_self_iff_false 0).mp
    massPos

theorem activeCell_mem_cleanup
    {cell : WZ2PaperCellIndex}
    (cellActive :
      cell ∈ wz1PaperActiveCells
        (output.finalFineShading cleanup) deltaPos) :
    cell ∈ cleanup.retainedFineCells := by
  rcases
      ((mem_wz1PaperActiveCells
        (output.finalFineShading cleanup) deltaPos cell).mp
        cellActive).2
    with ⟨point, pointUnion, pointCell⟩
  rcases pointUnion with ⟨source, pointCarrier⟩
  have pointRefined :
      point ∈
        cleanup.refined.carrier
          (output.metric.mesh.complete.selectedFine.embedding
            (output.restriction.fineSelected.embedding source)) := by
    simpa only [output.finalFineShading_carrier cleanup] using pointCarrier
  have pointRetainedUnion :
      point ∈
        wz2RetainedCellsUnion delta cleanup.retainedFineCells := by
    let ambientSource : Fin fine.card :=
      output.metric.mesh.complete.selectedFine.embedding
        (output.restriction.fineSelected.embedding source)
    have pointRefined' :
        point ∈ cleanup.refined.carrier ambientSource := by
      simpa only [ambientSource] using pointRefined
    have carrierEq :
        cleanup.refined.carrier ambientSource =
          (wz2RefinedShading sourceShading
            cleanup.retainedFineCells).carrier ambientSource :=
      congrArg (fun refined => refined.carrier ambientSource)
        cleanup.refined_eq
    have pointExplicit :
        point ∈
          (wz2RefinedShading sourceShading
            cleanup.retainedFineCells).carrier ambientSource :=
      carrierEq ▸ pointRefined'
    exact
      (show
        point ∈ sourceShading.carrier ambientSource ∩
          wz2RetainedCellsUnion delta cleanup.retainedFineCells
        from pointExplicit).2
  rcases Set.mem_iUnion₂.mp pointRetainedUnion with
    ⟨retainedCell, retainedMem, pointRetained⟩
  have cellEq : retainedCell = cell := by
    have retainedIndex :
        wz1PaperGridIndex delta point = retainedCell :=
      (mem_wz1PaperGridCube delta retainedCell point).mp pointRetained
    have cellIndex :
        wz1PaperGridIndex delta point = cell :=
      (mem_wz1PaperGridCube delta cell point).mp pointCell
    exact retainedIndex.symm.trans cellIndex
  rwa [← cellEq]

noncomputable def packetCellInput
    (refinedMassPos : 0 < cleanup.refined.mass)
    (rhoPos : 0 < rho)
    (scaleSeparation : 100 * delta ≤ rho) :
    PureWZ2Prop62PacketCellInput
      output.restriction.section6Cover
      (output.finalFineShading cleanup) where
  delta_pos := deltaPos
  rho_pos := rhoPos
  cubical := output.finalFineShading_cubical cleanup
  fineCells :=
    wz1PaperActiveCells (output.finalFineShading cleanup) deltaPos
  fineCells_eq := rfl
  fineCells_nonempty :=
    output.finalFineCells_nonempty cleanup refinedMassPos
  coarseCellOf := cleanup.parent
  fine_cell_containment := by
    intro cell cellMem
    exact cleanup.parent_containment cell <|
      output.activeCell_mem_cleanup cleanup cellMem
  parent_cell_containment := by
    intro parent cell source cellMem sourceMem wholeCell
    have retainedCell :
        cell ∈ cleanup.retainedFineCells :=
      output.activeCell_mem_cleanup cleanup cellMem
    have eighteenDeltaLeRho : 18 * delta ≤ rho := by
      nlinarith
    apply
      wz2_prop_sticky_coarse_cell_containment
        deltaPos rhoPos eighteenDeltaLeRho
        (output.restriction.fineSelected.family.tube source)
        (output.restriction.coarseSelected.family.tube parent)
        (output.restriction.section6Cover.fine_line_class source)
        (output.restriction.section6Cover.coarse_line_class parent)
        ((mem_wz2PaperFullFiberIndices_iff parent source).mp sourceMem)
        (cleanup.parent cell)
    · let point := cellCorner delta cell
      have pointFine :
          point ∈ wz1PaperGridCube delta cell :=
        cellCorner_mem_gridCube deltaPos cell
      have pointShading :
          point ∈ (output.finalFineShading cleanup).carrier source :=
        wholeCell pointFine
      exact
        ⟨point,
          cleanup.parent_containment cell retainedCell pointFine,
          (output.finalFineShading cleanup).subset_body source pointShading⟩
    · exact cleanup.parent_crop cell retainedCell

end PureWZ2Prop62MetricParentsOutput

end Kakeya.Assouad

end
