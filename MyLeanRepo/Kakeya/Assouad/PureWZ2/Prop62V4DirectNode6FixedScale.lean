import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4DirectCroppedProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4CellIncidenceBounds
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4BoundedFinalFiberCriticalWitness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FineOnlyCriticalTail
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4PureFinalAssemblyInputs
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4FixedGridBoundaryRemoval
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4OnePassTreeCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Node6FixedScaleOutput

/-!
# Direct Proposition 6.2 output used by Node 6

This module joins the direct cropped V4 producer to the deliberately small
fixed-scale record consumed in Section 6.  It never constructs the stronger
historical `PureWZ2PropStickyData`: only the final refinement, balanced cover,
two volume upper bounds, and the global fine multiplicity cap are retained.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open MeasureTheory
open Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace Prop62V4DirectCroppedProducerData

variable
    {delta sigma sourceLoss workingEta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta}
    {rho : WZ2PaperRequestedScale delta}
    {hdelta : 0 < delta}
    (produced :
      Prop62V4DirectCroppedProducerData
        (workingEta := workingEta) cfg rho hdelta)

/-- The metric ten-log and terminal fifty-log refinements, composed without
changing the witness chosen by the direct producer. -/
noncomputable def innerRefinement :
    WZ1PaperRefinement produced.fixedGrid.preparation.cleanup.refined 60 := by
  simpa using
    (Classical.choice <|
      wz2_paper_refinement_composition
        produced.fixedGrid.preparation.cleanup.refined 10 50
        (prop62V4DirectCroppedMetricCompanionOfCertificate
          produced.fixedGrid produced.metricCertificate).metric.refinement
        produced.rich.outputCertificate.refinement).toRefinement

/-- The complete one-plus-ten-plus-fifty logarithmic refinement of the input
C2 shading. -/
noncomputable def finalRefinement :
    WZ1PaperRefinement cfg.shading 61 :=
  produced.fixedGrid.preparation.composeSixtyLogRefinement
    produced.innerRefinement

@[simp] theorem finalRefinement_selected_family :
    produced.finalRefinement.selected.family =
      produced.rich.outputCertificate.refinement.selected.family :=
  rfl

@[simp] theorem finalRefinement_refined :
    produced.finalRefinement.refined =
      produced.rich.outputCertificate.refinement.refined :=
  rfl

@[simp] theorem outputCertificate_selected_family :
    produced.rich.outputCertificate.refinement.selected.family =
      produced.rich.families.restriction.fineSelected.family :=
  rfl

@[simp] theorem outputCertificate_refined :
    produced.rich.outputCertificate.refinement.refined =
      produced.rich.canonicalOutput.fineShading :=
  rfl

@[simp] theorem outputCertificate_coarse_family :
    produced.rich.outputCertificate.coarse.family =
      produced.rich.families.restriction.coarseSelected.family :=
  rfl

@[simp] theorem outputCertificate_coarseShading :
    produced.rich.outputCertificate.coarseShading =
      produced.rich.canonicalOutput.coarseShading :=
  rfl

/-- The final selected family inherits the bounded ordinary representatives
from the input C2 configuration through the actual composed subfamily. -/
theorem final_bounded_base :
    HasBoundedBase
      produced.rich.outputCertificate.refinement.selected.family 4 := by
  intro index
  change ‖(produced.finalRefinement.selected.family.tube index).base‖ ≤ 4
  rw [produced.finalRefinement.selected.tube_eq]
  exact cfg.bounded_base _

/-- The source mass lower bound used in the product estimate, on the exact
metric-refined shading preceding the terminal fifty-log refinement. -/
theorem source_mass_lower
    (deltaSmall : delta ≤ 1 / 12) :
    wz1PaperRefinementFraction delta 11 *
          Kakeya.realRpowENN delta sourceLoss *
          produced.rich.outputCertificate.refinement.selected.family.enncard *
          Kakeya.realRpowENN delta 2 ≤
      (prop62V4DirectCroppedMetricCompanionOfCertificate
        produced.fixedGrid produced.metricCertificate
      ).metric.refinement.refined.mass := by
  have finalCardLe :
      produced.rich.outputCertificate.refinement.selected.family.enncard ≤
        cfg.family.enncard := by
    change
      (produced.finalRefinement.selected.family.card : ENNReal) ≤
        (cfg.family.card : ENNReal)
    have cardBound :
        produced.finalRefinement.selected.family.card ≤ cfg.family.card := by
      simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective
          produced.finalRefinement.selected.embedding
          produced.finalRefinement.selected.embedding.injective
    exact_mod_cast cardBound
  have sourceDensity :
      Kakeya.realRpowENN delta sourceLoss *
            produced.rich.outputCertificate.refinement.selected.family.enncard *
            Kakeya.realRpowENN delta 2 ≤
        cfg.shading.mass := by
    calc
      Kakeya.realRpowENN delta sourceLoss *
            produced.rich.outputCertificate.refinement.selected.family.enncard *
            Kakeya.realRpowENN delta 2 ≤
          Kakeya.realRpowENN delta sourceLoss * cfg.family.enncard *
            Kakeya.realRpowENN delta 2 := by gcongr
      _ = Kakeya.realRpowENN delta sourceLoss *
            (cfg.family.enncard * Kakeya.realRpowENN delta 2) := by ring
      _ ≤ Kakeya.realRpowENN delta sourceLoss *
            (wz1PaperBodyFamily cfg.family).mass := by
        gcongr
        exact pureWZ2_prop62_paper_body_mass_lower
          hdelta deltaSmall cfg.line_class
      _ ≤ cfg.shading.mass := cfg.extremal.dense
  calc
    wz1PaperRefinementFraction delta 11 *
          Kakeya.realRpowENN delta sourceLoss *
          produced.rich.outputCertificate.refinement.selected.family.enncard *
          Kakeya.realRpowENN delta 2 =
        wz1PaperRefinementFraction delta 11 *
          (Kakeya.realRpowENN delta sourceLoss *
            produced.rich.outputCertificate.refinement.selected.family.enncard *
            Kakeya.realRpowENN delta 2) := by ring
    _ ≤ wz1PaperRefinementFraction delta 11 * cfg.shading.mass := by gcongr
    _ = wz1PaperRefinementFraction delta 10 *
          (wz1PaperRefinementFraction delta 1 * cfg.shading.mass) := by
      simp only [wz1PaperRefinementFraction]
      rw [show 11 = 10 + 1 by norm_num, pow_add]
      ring
    _ ≤ wz1PaperRefinementFraction delta 10 *
          produced.fixedGrid.preparation.cleanup.refined.mass := by
      gcongr
      exact produced.fixedGrid.preparation.refinement_retained
    _ ≤ (prop62V4DirectCroppedMetricCompanionOfCertificate
          produced.fixedGrid produced.metricCertificate
        ).metric.refinement.refined.mass :=
      (prop62V4DirectCroppedMetricCompanionOfCertificate
        produced.fixedGrid produced.metricCertificate
      ).metric.refinement.retained_mass

/-- The source union-volume upper bound for the same metric-refined shading. -/
theorem source_volume_upper :
    volume (prop62V4DirectCroppedMetricCompanionOfCertificate
      produced.fixedGrid produced.metricCertificate
    ).metric.refinement.refined.union ≤
      Kakeya.realRpowENN delta (sigma - sourceLoss) := by
  have subset :
      (prop62V4DirectCroppedMetricCompanionOfCertificate
        produced.fixedGrid produced.metricCertificate
      ).metric.refinement.refined.union ⊆ cfg.shading.union := by
    rintro point ⟨index, pointMem⟩
    refine ⟨produced.fixedGrid.preparation.fixedGridRefinement.selected.embedding
      ((prop62V4DirectCroppedMetricCompanionOfCertificate
        produced.fixedGrid produced.metricCertificate
      ).metric.refinement.selected.embedding index), ?_⟩
    exact produced.fixedGrid.preparation.fixedGridRefinement.subshading _ <|
      (prop62V4DirectCroppedMetricCompanionOfCertificate
        produced.fixedGrid produced.metricCertificate
      ).metric.refinement.subshading index pointMem
  exact (measure_mono subset).trans cfg.extremal.volume_upper

/-- The final fine union-volume upper bound at the internal strong loss. -/
theorem fine_volume_upper
    {polylogExponent cwaPower packetDensityExponent cwaLossExponent : ℕ}
    {outputLoss : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss}
    (sourceLoss_le_final :
      sourceLoss ≤ routing.numerics.hierarchy.finalStrongLoss) :
    volume produced.finalRefinement.refined.union ≤
      Kakeya.realRpowENN delta
        (sigma - routing.numerics.hierarchy.finalStrongLoss) := by
  have subset : produced.finalRefinement.refined.union ⊆ cfg.shading.union := by
    rintro point ⟨index, pointMem⟩
    exact ⟨produced.finalRefinement.selected.embedding index,
      produced.finalRefinement.subshading index pointMem⟩
  have powerLe :
      Kakeya.realRpowENN delta (sigma - sourceLoss) ≤
        Kakeya.realRpowENN delta
          (sigma - routing.numerics.hierarchy.finalStrongLoss) :=
    pure_wz2_rpowENN_antitone hdelta cfg.extremal.delta_le_one (by linarith)
  exact (measure_mono subset).trans (cfg.extremal.volume_upper.trans powerLe)

/-- The canonical packet-density lower bound, rewritten from the common
fiber floor to the cardinality of the exact final complete fiber. -/
theorem packet_mass_lower
    {polylogExponent cwaPower cwaLossExponent : ℕ}
    {outputLoss : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData
        polylogExponent cwaPower 2 cwaLossExponent sigma outputLoss}
    (workingEta_eq : workingEta = routing.numerics.hierarchy.stableLoss)
    (parent : Fin produced.rich.outputCertificate.coarse.family.card) :
    ((2 : ENNReal)⁻¹ *
          Kakeya.realRpowENN delta
            (2 * routing.numerics.hierarchy.stableLoss)) *
          (wz2PaperFullFiberSubfamily
            produced.rich.outputCertificate.refinement.selected.family
            produced.rich.outputCertificate.coarse.family parent).family.enncard *
          Kakeya.realRpowENN delta 2 ≤
      (restrictPaperShading
        (wz2PaperFullFiberSubfamily
          produced.rich.outputCertificate.refinement.selected.family
          produced.rich.outputCertificate.coarse.family parent)
        produced.rich.outputCertificate.refinement.refined).mass := by
  have fiberCardUpper :
      (wz2PaperFullFiberSubfamily
        produced.rich.outputCertificate.refinement.selected.family
        produced.rich.outputCertificate.coarse.family parent).family.enncard ≤
        (2 * produced.rich.outputCertificate.fiberFloor : ℕ) := by
    change
      (wz2PaperFullFiberCount
        produced.rich.outputCertificate.refinement.selected.family
        produced.rich.outputCertificate.coarse.family parent : ENNReal) ≤
          (2 * produced.rich.outputCertificate.fiberFloor : ℕ)
    exact_mod_cast
      (produced.rich.outputCertificate.fiber_cardinality parent).2.le
  calc
    ((2 : ENNReal)⁻¹ *
          Kakeya.realRpowENN delta
            (2 * routing.numerics.hierarchy.stableLoss)) *
          (wz2PaperFullFiberSubfamily
            produced.rich.outputCertificate.refinement.selected.family
            produced.rich.outputCertificate.coarse.family parent).family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        ((2 : ENNReal)⁻¹ *
          Kakeya.realRpowENN delta
            (2 * routing.numerics.hierarchy.stableLoss)) *
          (2 * produced.rich.outputCertificate.fiberFloor : ℕ) *
          Kakeya.realRpowENN delta 2 := by gcongr
    _ = Kakeya.realRpowENN delta
            (2 * routing.numerics.hierarchy.stableLoss) *
          (produced.rich.outputCertificate.fiberFloor : ENNReal) *
          Kakeya.realRpowENN delta 2 := by
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      calc
        _ = ((2 : ENNReal)⁻¹ * 2) *
            (Kakeya.realRpowENN delta
                (2 * routing.numerics.hierarchy.stableLoss) *
              (produced.rich.outputCertificate.fiberFloor : ENNReal) *
              Kakeya.realRpowENN delta 2) := by ring
        _ = _ := by rw [ENNReal.inv_mul_cancel] <;> norm_num
    _ ≤ _ := by
      simpa [workingEta_eq] using
        produced.rich.outputCertificate.packet_density parent

/-- The bounded-base certificate on the source family stored by the exact
final-fiber rescaling input. -/
theorem rescaling_source_bounded_base
    (parent : Fin produced.rich.outputCertificate.coarse.family.card) :
    HasBoundedBase
      (produced.rich.outputCertificate.rescaled_fiber_input parent).sourceFamily 4 := by
  intro index
  rw [(produced.rich.outputCertificate.rescaled_fiber_input parent).source_tube_eq]
  exact produced.final_bounded_base
    ((produced.rich.outputCertificate.rescaled_fiber_input parent).sourceEquiv index).1

/-- Every retained final fine cell lies in the canonical active coarse cell
assigned to it by the packet construction. -/
theorem fine_cell_nested
    (source : Fin produced.rich.outputCertificate.refinement.selected.family.card)
    (point : Point3)
    (pointMem :
      point ∈ produced.rich.outputCertificate.refinement.refined.carrier source) :
    ∃ cell ∈ produced.rich.outputCertificate.balanced.activeCells,
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
        wz1PaperGridCube rho.1 cell := by
  let fineCell := wz1PaperGridIndex delta point
  let parent := produced.rich.outputCertificate.cover.toWZ1PaperTubeCover.parent source
  have wholeCell :
      wz1PaperGridCube delta fineCell ⊆
        produced.rich.outputCertificate.refinement.refined.carrier source :=
    produced.rich.outputCertificate.refined_cubical source point pointMem
  have fineActive :
      fineCell ∈ wz1PaperActiveCells
        produced.rich.outputCertificate.refinement.refined hdelta := by
    rw [mem_wz1PaperActiveCells]
    refine ⟨?_, ⟨point, ⟨source, pointMem⟩, ?_⟩⟩
    · exact paper_point_gridIndex_in_window hdelta
        (produced.rich.outputCertificate.refinement.refined.subset_body
          source pointMem).2
    · exact (mem_wz1PaperGridCube delta fineCell point).mpr rfl
  have sourceFiber :
      source ∈ wz2PaperFullFiberIndices
        produced.rich.outputCertificate.refinement.selected.family
        produced.rich.outputCertificate.coarse.family parent :=
    (mem_wz2PaperFullFiberIndices_iff parent source).mpr
      (produced.rich.outputCertificate.cover.toWZ1PaperTubeCover.parent_covers source)
  have packetMem :
      (parent, fineCell) ∈ produced.rich.outputCertificate.packetCells := by
    rw [produced.rich.outputCertificate.packetCells_eq]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, fineActive⟩,
        ⟨source, Finset.mem_filter.mpr ⟨sourceFiber, wholeCell⟩⟩⟩
  have support :=
    produced.rich.outputCertificate.packet_coarse_support
      (parent, fineCell) packetMem
  have active :
      produced.rich.outputCertificate.coarseOfFine fineCell ∈
        produced.rich.outputCertificate.balanced.activeCells := by
    rw [← produced.rich.outputCertificate.active_coarse_cells_eq]
    exact support.1
  exact ⟨produced.rich.outputCertificate.coarseOfFine fineCell, active, support.2.1⟩

end Prop62V4DirectCroppedProducerData

namespace Prop62V4DirectNode6FixedScale

variable
    {delta sigma outputLoss : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData 10 8 2 51 sigma outputLoss}
    (scalar : Prop62V4PureScalarInputs 10 8 2 51 sigma outputLoss routing)
    (cfg :
      PureWZ2C2GrainConfiguration
        sigma routing.numerics.hierarchy.sourceLoss delta)
    (rho : WZ2PaperRequestedScale delta)
    (hdelta : 0 < delta)
    (produced :
      Prop62V4DirectCroppedProducerData
        (workingEta := routing.numerics.hierarchy.stableLoss)
        cfg rho hdelta)

/-- Assemble the exact direct V4 witness into the fixed-scale data actually
used by Node 6.  No full `PureWZ2PropStickyData` is constructed. -/
noncomputable def assemble
    (deltaLe : delta ≤ scalar.delta₀)
    (outputLossLeOne : outputLoss ≤ 1)
    (rhoLower : Real.rpow delta (1 - outputLoss) ≤ rho.1)
    (rhoUpper : rho.1 ≤ Real.rpow delta outputLoss) :
    PureWZ2Node6FixedScaleOutput
      (sigma := sigma)
      (outputLoss := routing.numerics.hierarchy.finalStrongLoss)
      cfg.shading rho 61 := by
  let rich := produced.rich
  let output := rich.canonicalOutput
  let peelingA0 := produced.rich.packetInput.canonicalPeelingA0
    produced.rich.multiplicity produced.rich.parentClass
    produced.rich.treeCleanup produced.rich.exactification
    produced.rich.producer.initial.bins
  let critical := Prop62V4PureScalarInputs.criticalForCap (routing := routing)
  have deltaSmall : delta ≤ 1 / 12 :=
    deltaLe.trans <| scalar.delta₀_le_one_hundred.trans (by norm_num)
  have sourceLossLeFinal :
      routing.numerics.hierarchy.sourceLoss ≤
        routing.numerics.hierarchy.finalStrongLoss := by
    rw [routing.numerics.hierarchy.sourceLoss_eq,
      routing.numerics.hierarchy.finalStrongLoss_eq]
    dsimp only [wz2PaperFinalSourceLoss, wz2PaperFinalStrongLoss]
    have structuralLe :
        routing.critical.structuralLoss ≤ outputLoss ^ 2 / 1000 :=
      routing.critical.structuralLoss_le.trans (min_le_left _ _)
    have outputLossPos : 0 < outputLoss := by
      have hfinal := routing.numerics.hierarchy.finalStrongLoss_pos
      rw [routing.numerics.hierarchy.finalStrongLoss_eq] at hfinal
      dsimp only [wz2PaperFinalStrongLoss] at hfinal
      linarith
    have outputSqLe : outputLoss ^ 2 ≤ outputLoss := by nlinarith
    have structuralLeOutput :
        routing.critical.structuralLoss ≤ outputLoss := by
      calc
        routing.critical.structuralLoss ≤ outputLoss ^ 2 / 1000 := structuralLe
        _ ≤ outputLoss := by nlinarith
    have structuralLeOne : routing.critical.structuralLoss ≤ 1 :=
      structuralLeOutput.trans outputLossLeOne
    have structuralSqLe :
        routing.critical.structuralLoss ^ 2 ≤
          routing.critical.structuralLoss := by
      nlinarith [routing.critical.structuralLoss_pos]
    calc
      routing.critical.structuralLoss ^ 2 / 20 ≤
          routing.critical.structuralLoss / 20 := by nlinarith
      _ ≤ outputLoss / 4 := by nlinarith
  let fineInputs :
      output.FineCriticalMultiplicityInputsData
        rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
          rich.exactification rich.parentDegree rich.core rich.good
          rich.families critical :=
    { ratio_small :=
        scalar.ratio_small hdelta deltaLe produced.metricCertificate.rho_pos rhoLower
      ratio_critical :=
        scalar.ratio_critical hdelta deltaLe produced.metricCertificate.rho_pos rhoLower
      fiber_witness := fun parent =>
        ⟨by
          let raw :=
            Prop62V4BoundedFinalFiber.witness
                (structuralLoss := routing.critical.structuralLoss)
                (produced.rich.outputCertificate.rescaled_fiber_input parent)
                (restrictPaperShading
                  (wz2PaperFullFiberSubfamily
                    produced.rich.outputCertificate.refinement.selected.family
                    produced.rich.outputCertificate.coarse.family parent)
                  produced.rich.outputCertificate.refinement.refined)
                (produced.rescaling_source_bounded_base parent)
                ((2 : ENNReal)⁻¹ *
                  Kakeya.realRpowENN delta
                    (2 * routing.numerics.hierarchy.stableLoss))
                (produced.packet_mass_lower (routing := routing) rfl parent)
                (produced.rich.terminal_fiber_constant_bound.trans <|
                  scalar.fiber_cwa hdelta deltaLe
                    produced.metricCertificate.rho_pos rhoLower)
                (scalar.fiber_density hdelta deltaLe
                  produced.metricCertificate.rho_pos rhoLower)
          exact raw⟩
      fine_constant_absorption :=
        by
          simpa [critical, Prop62V4PureScalarInputs.criticalForCap,
            routing.numerics.hierarchy.criticalFloorLoss_eq] using
            scalar.fiber_constant hdelta deltaLe
              produced.metricCertificate.rho_pos rhoLower }
  let productInputs :=
    scalar.productMultiplicityInputs
      rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
      rich.exactification rich.parentDegree rich.core rich.good rich.families
      (output := output) deltaLe rhoLower rhoUpper rich.regularity_bound
      (by
        change
          wz1PaperRefinementFraction delta 11 *
                Kakeya.realRpowENN delta
                  routing.numerics.hierarchy.sourceLoss *
                produced.rich.outputCertificate.refinement.selected.family.enncard *
                Kakeya.realRpowENN delta 2 ≤
            (prop62V4DirectCroppedMetricCompanionOfCertificate
              produced.fixedGrid produced.metricCertificate
            ).metric.refinement.refined.mass
        exact produced.source_mass_lower deltaSmall)
      (by
        change volume (prop62V4DirectCroppedMetricCompanionOfCertificate
              produced.fixedGrid produced.metricCertificate
            ).metric.refinement.refined.union ≤
          Kakeya.realRpowENN delta
            (sigma - routing.numerics.hierarchy.sourceLoss)
        exact produced.source_volume_upper)
  let componentInputs :=
    scalar.componentMultiplicityFloorInputs
      rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
      rich.exactification rich.parentDegree rich.core rich.good rich.families
      (output := output) deltaLe rhoLower rhoUpper rich.regularity_bound
  let volumeAbsorption :=
    scalar.extremalVolumeAbsorption deltaLe hdelta produced.metricCertificate.rho_pos
  have coarseVolume :=
    output.coarse_volume_upper_of_fine_critical_inputs
      rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
        rich.exactification rich.parentDegree rich.core rich.good rich.families
        (scalar.rho_small hdelta deltaLe rhoUpper) critical fineInputs
        productInputs componentInputs volumeAbsorption
  have fineMultiplicityCap :=
    output.fine_pointMultiplicity_upper_by_fine_critical_fiber_sum
      rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
        rich.exactification rich.parentDegree rich.core rich.good rich.families
        critical fineInputs
  refine
    { delta_pos := hdelta
      selected := produced.finalRefinement.selected
      selected_nonempty := by
        simpa using produced.rich.outputCertificate.refined_nonempty
      refined := produced.finalRefinement.refined
      subshading := produced.finalRefinement.subshading
      retained_mass := by
        simpa [wz2PaperPureRefinementFraction, wz1PaperRefinementFraction] using
          produced.finalRefinement.retained_mass
      refined_cubical := by
        simpa using produced.rich.outputCertificate.refined_cubical
      fine_volume_upper := produced.fine_volume_upper sourceLossLeFinal
      coarse := produced.rich.outputCertificate.coarse.family
      cover := produced.rich.outputCertificate.cover
      croppedCoarseShading := produced.rich.outputCertificate.coarseShading
      balanced :=
        { point_compatibility := by
            intro source parent hparent point hpoint
            have parentEq :
                parent =
                  (produced.rich.outputCertificate.cover.toWZ1PaperTubeCover
                    ).parent source :=
              (produced.rich.outputCertificate.cover.toWZ1PaperTubeCover
                ).parent_unique source parent hparent
            subst parent
            exact produced.rich.outputCertificate.balanced
              |>.point_compatibility source point hpoint
          coarse_cubical :=
            produced.rich.outputCertificate.balanced.coarse_cubical
          activeCells :=
            produced.rich.outputCertificate.balanced.activeCells
          coarse_union_eq :=
            produced.rich.outputCertificate.balanced.coarse_union_eq
          cellMass := produced.rich.outputCertificate.balanced.cellMass
          cellMass_pos := produced.rich.outputCertificate.balanced.cellMass_pos
          cellMass_ne_top :=
            produced.rich.outputCertificate.balanced.cellMass_ne_top
          fine_cell_mass :=
            produced.rich.outputCertificate.balanced.fine_cell_mass }
      coarse_volume_upper := coarseVolume
      fine_pointMultiplicity_upper := ?_
      cellIndexedMassBase :=
        (((output.muFine *
          (produced.rich.packetInput.fineCellThreshold
            produced.rich.multiplicity produced.rich.parentClass
            produced.rich.treeCleanup produced.rich.exactification
            produced.rich.producer.initial.bins peelingA0 *
            produced.rich.core.ranges.commonFineCellCount) : ℕ) : ENNReal) *
          volume (wz1PaperGridCube delta (0, 0, 0)))
      cellIndexedMassBase_pos := by
        exact produced.rich.packetInput.indexedCellMass_bandBase_pos
          produced.rich.multiplicity produced.rich.parentClass
          produced.rich.treeCleanup produced.rich.exactification
          produced.rich.parentDegree produced.rich.core produced.rich.good
          produced.rich.families output
      cellIndexedMassBase_ne_top := by
        exact produced.rich.packetInput.indexedCellMass_bandBase_ne_top
          produced.rich.multiplicity produced.rich.parentClass
          produced.rich.treeCleanup produced.rich.exactification
          produced.rich.parentDegree produced.rich.core produced.rich.good
          produced.rich.families output
      cellIndexedMassRatio := ((2 * peelingA0 : ℕ) : ENNReal)
      cellIndexedMassRatio_pos := by
        simpa [peelingA0] using
          produced.rich.packetInput.indexedCellMass_bandFactor_pos
          produced.rich.multiplicity produced.rich.parentClass
          produced.rich.treeCleanup produced.rich.exactification
          produced.rich.parentDegree produced.rich.core
      cellIndexedMassRatio_ne_top := ENNReal.natCast_ne_top _
      cellIndexedMassRatio_le_logarithmicLoss := by
        have hA0 : 0 < peelingA0 := by
          dsimp only [peelingA0]
          exact produced.rich.packetInput.canonicalPeelingA0_pos
            produced.rich.multiplicity produced.rich.parentClass
            produced.rich.treeCleanup produced.rich.exactification
            produced.rich.producer.initial.bins
        have htwoA0 : (2 * peelingA0 : ℕ) ≤ 4 * peelingA0 ^ 2 := by
          nlinarith
        have hratioToCoarse :
            ((2 * peelingA0 : ℕ) : ENNReal) ≤
              (output.coarseLoss : ENNReal) := by
          rw [output.coarseLoss_eq]
          change ((2 * peelingA0 : ℕ) : ENNReal) ≤
            ((4 * peelingA0 ^ 2 : ℕ) : ENNReal)
          exact_mod_cast htwoA0
        exact hratioToCoarse.trans <| by
          simpa [logarithmicLoss] using rich.regularity_bound
      cellIndexedMass := fun cell =>
        produced.rich.packetInput.indexedCellMass
          produced.rich.multiplicity produced.rich.parentClass
          produced.rich.treeCleanup produced.rich.exactification
          produced.rich.parentDegree produced.rich.core produced.rich.good
          produced.rich.families output cell
      cellIndexedMass_eq := by
        intro cell
        exact produced.rich.packetInput.indexedCellMass_eq_source_sum
          produced.rich.multiplicity produced.rich.parentClass
          produced.rich.treeCleanup produced.rich.exactification
          produced.rich.parentDegree produced.rich.core produced.rich.good
          produced.rich.families output cell
      cellIndexedMass_band := by
        intro cell hcell
        have hactive : cell ∈ produced.rich.outputCertificate.activeCoarseCells := by
          rw [produced.rich.outputCertificate.active_coarse_cells_eq]
          exact hcell
        simpa [peelingA0] using
          produced.rich.packetInput.indexedCellMass_band
            produced.rich.multiplicity produced.rich.parentClass
            produced.rich.treeCleanup produced.rich.exactification
            produced.rich.parentDegree produced.rich.core produced.rich.good
            produced.rich.families output
            ⟨cell, hactive⟩
      fine_cell_nested := by
        simpa only [wz1PaperBodyFamily, id_eq,
          produced.finalRefinement_selected_family,
          produced.finalRefinement_refined,
          produced.outputCertificate_selected_family,
          produced.outputCertificate_refined,
          produced.outputCertificate_coarse_family]
          using produced.fine_cell_nested }
  intro point
  calc
    (produced.finalRefinement.refined.pointMultiplicity point : ENNReal) =
        (output.fineShading.pointMultiplicity point : ENNReal) := rfl
    _ ≤ Kakeya.realRpowENN (delta / rho.1)
          (2 - sigma - routing.numerics.hierarchy.capLoss) *
        produced.finalRefinement.selected.family.enncard := by
      simpa only [rich, output,
        produced.outputCertificate_selected_family,
        produced.finalRefinement_selected_family]
        using fineMultiplicityCap point
    _ ≤ Kakeya.realRpowENN (delta / rho.1)
          (2 - sigma - routing.numerics.hierarchy.finalStrongLoss) *
        produced.finalRefinement.selected.family.enncard := by
      gcongr
      exact scalar.final_fiber_multiplicity hdelta deltaLe
        produced.metricCertificate.rho_pos rhoLower

/-- Uniform Node-6-facing fixed-scale provider.  The critical package, scalar
routing, and structural lemmas are chosen before the runtime C2 configuration
and requested scale. -/
theorem provider
    (criticalPackage : PureWZ2CriticalPackage sigma)
    (outputLossPos : 0 < outputLoss)
    (outputLossLeOne : outputLoss ≤ 1) :
    ∃ inputLoss delta₀ : ℝ,
      0 < inputLoss ∧
      inputLoss ≤ outputLoss ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta,
          ∀ rho : WZ2PaperRequestedScale delta,
            Real.rpow delta (1 - outputLoss) ≤ rho.1 →
            rho.1 ≤ Real.rpow delta outputLoss →
              Nonempty
                (PureWZ2Node6FixedScaleOutput
                  (sigma := sigma) (outputLoss := outputLoss)
                  cfg.shading rho 61) := by
  rcases
      Kakeya.Assouad.Prop62PaperAudit.V4.PureWZ2CriticalPackage.prop62V4_pure_scalar_routing
        criticalPackage
        10 8 2 51 outputLossPos outputLossLeOne
    with ⟨scalarRouting⟩
  let routing := scalarRouting.routing
  let scalar := scalarRouting.scalar
  let inputLoss := routing.numerics.hierarchy.sourceLoss
  rcases prop62V4_direct_cropped_producer
      (sigma := sigma)
      (outputLoss := outputLoss)
      (sourceLoss := routing.numerics.hierarchy.sourceLoss)
      (workingEta := routing.numerics.hierarchy.stableLoss)
      routing.numerics.hierarchy.sourceLoss_pos outputLossPos
      (by
        rw [routing.numerics.hierarchy.sourceLoss_eq]
        dsimp only [wz2PaperFinalSourceLoss]
        have structuralLe :
            routing.critical.structuralLoss ≤ outputLoss ^ 2 / 1000 :=
          routing.critical.structuralLoss_le.trans (min_le_left _ _)
        have structuralLeOne : routing.critical.structuralLoss ≤ 1 := by
          have structuralLeOutput :
              routing.critical.structuralLoss ≤ outputLoss := by
            calc
              routing.critical.structuralLoss ≤ outputLoss ^ 2 / 1000 :=
                structuralLe
              _ ≤ outputLoss := by nlinarith
          exact structuralLeOutput.trans outputLossLeOne
        have structuralSqLe :
            routing.critical.structuralLoss ^ 2 ≤
              routing.critical.structuralLoss := by
          nlinarith [routing.critical.structuralLoss_pos]
        nlinarith)
      routing.numerics.hierarchy.source_stable
      (routing.numerics.hierarchy.sourceLoss_pos.trans
        routing.numerics.hierarchy.source_stable)
      scalar.metric_loss scalar.packet_loss
      fixed_grid_boundary_removal one_pass_tree_cleanup
    with ⟨producerReceipt⟩
  let delta₀ := min scalar.delta₀ producerReceipt.delta₀
  refine ⟨inputLoss, delta₀,
    routing.numerics.hierarchy.sourceLoss_pos, ?_, ?_, ?_, ?_⟩
  · have sourceLeFinal :
        routing.numerics.hierarchy.sourceLoss ≤
          routing.numerics.hierarchy.finalStrongLoss := by
      rw [routing.numerics.hierarchy.sourceLoss_eq,
        routing.numerics.hierarchy.finalStrongLoss_eq]
      dsimp only [wz2PaperFinalSourceLoss, wz2PaperFinalStrongLoss]
      have structuralLe :
          routing.critical.structuralLoss ≤ outputLoss ^ 2 / 1000 :=
        routing.critical.structuralLoss_le.trans (min_le_left _ _)
      have structuralLeOutput :
          routing.critical.structuralLoss ≤ outputLoss := by
        calc
          routing.critical.structuralLoss ≤ outputLoss ^ 2 / 1000 := structuralLe
          _ ≤ outputLoss := by nlinarith
      have structuralLeOne : routing.critical.structuralLoss ≤ 1 :=
        structuralLeOutput.trans outputLossLeOne
      have structuralSqLe :
          routing.critical.structuralLoss ^ 2 ≤
            routing.critical.structuralLoss := by
        nlinarith [routing.critical.structuralLoss_pos]
      nlinarith
    exact sourceLeFinal.trans <| by
      nlinarith [routing.numerics.hierarchy.final_output_budget]
  · exact lt_min scalar.delta₀_pos producerReceipt.delta₀_pos
  · exact (min_le_left _ _).trans <|
      scalar.delta₀_le_one_hundred.trans (by norm_num)
  · intro delta hdelta hdeltaLe cfg rho rhoLower rhoUpper
    have deltaScalar : delta ≤ scalar.delta₀ :=
      hdeltaLe.trans (min_le_left _ _)
    have deltaProducer : delta ≤ producerReceipt.delta₀ :=
      hdeltaLe.trans (min_le_right _ _)
    rcases producerReceipt.produce hdelta deltaProducer cfg rho
        rhoLower rhoUpper with ⟨produced⟩
    let internal := assemble scalar cfg rho hdelta produced
      deltaScalar outputLossLeOne rhoLower rhoUpper
    have finalLeOutput :
        routing.numerics.hierarchy.finalStrongLoss ≤ outputLoss := by
      have := routing.numerics.hierarchy.final_output_budget
      nlinarith [routing.numerics.hierarchy.finalStrongLoss_pos]
    exact ⟨internal.mono_loss hdelta finalLeOutput⟩

/-- The direct V4 construction supplies the minimal fixed-scale interface
used by Node 6. -/
theorem fixedScaleStatement : PureWZ2Node6FixedScaleStatement := by
  refine ⟨61, ?_⟩
  intro sigma critical outputLoss houtputLoss houtputLossOne
  exact provider critical houtputLoss houtputLossOne

end Prop62V4DirectNode6FixedScale

end Kakeya.Assouad.Prop62PaperAudit.V4

end
