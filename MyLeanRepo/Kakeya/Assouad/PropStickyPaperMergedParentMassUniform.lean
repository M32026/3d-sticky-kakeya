import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMergedParentMassLower
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralMergedFiberOutputs
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper

/-!
# Uniform comparison of merged complete-parent masses

The prepared caller fibers have uniformly comparable cardinalities.  Every
source tube carries the same absolute shaded-mass floor, while every cropped
paper tube has the same quadratic carrier-volume upper bound.  The one-parent
structural refinement retains one fixed fourth power of the paper logarithmic
fraction.  Combining these facts compares the merged shaded masses over any
two caller parents.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

def wz2PaperPreparedMergedParentMassWeight
    (delta sourceLoss : ℝ) : ENNReal :=
  wz1PaperRefinementFraction delta 4 *
    ((1 / 2 : ENNReal) *
      Kakeya.realRpowENN delta sourceLoss)

def wz2PaperPreparedMergedParentMassConstant
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent) : ENNReal :=
  (55296 * Kakeya.deltaTubeVolume 1) *
    prepared.structuralConstant

theorem wz2_paper_prepared_merged_parent_mass_uniform
    {delta sourceLoss stableLoss sigma floorLoss strongLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (critical :
      WZ2PaperCriticalFloorSelectionData
        sigma floorLoss strongLoss)
    (structural :
      WZ2PaperPreparedParentwiseStructuralProducerData
        (outputLoss := outputLoss) prepared critical) :
    ∀ first second : Fin prepared.callerStrict.coarse.card,
      wz2PaperPreparedMergedParentMassWeight delta sourceLoss *
          wz2PaperPreparedMergedParentMass structural first ≤
        wz2PaperPreparedMergedParentMassConstant prepared *
          wz2PaperPreparedMergedParentMass structural second := by
  intro first second
  let firstFiber :=
    wz2PaperPreparedOneParentFiber prepared first
  let secondFiber :=
    wz2PaperPreparedOneParentFiber prepared second
  let firstShading :=
    wz2PaperPreparedOneParentShading prepared first
  let secondShading :=
    wz2PaperPreparedOneParentShading prepared second
  let firstLocal :=
    (structural.fiberProducer first).structural
  let secondLocal :=
    (structural.fiberProducer second).structural
  let fraction := wz1PaperRefinementFraction delta 4
  let density :=
    (1 / 2 : ENNReal) *
      Kakeya.realRpowENN delta sourceLoss
  let geometry : ENNReal :=
    55296 * Kakeya.deltaTubeVolume 1
  let tubeScale := Kakeya.realRpowENN delta 2
  have hDeltaSmall : delta ≤ 1 / 24 := by
    have hCallerOne : caller.1 ≤ 1 := caller.2.2
    linarith [prepared.caller_tree_safe]
  have hFirstUpper :
      firstLocal.refinement.refined.mass ≤
        geometry * tubeScale * firstFiber.family.enncard := by
    calc
      firstLocal.refinement.refined.mass ≤ firstShading.mass :=
        paper_refinement_mass_monotone firstLocal.refinement
      _ ≤ geometry * tubeScale * firstFiber.family.enncard := by
        simpa [geometry, tubeScale, firstShading, firstFiber] using
          wz2_paper_shading_mass_upper
            prepared.delta_pos hDeltaSmall
            (prepared.cwa_nearby.2.1.subfamily firstFiber)
            firstShading
  have hFiberCardinality :
      firstFiber.family.enncard ≤
        prepared.structuralConstant *
          secondFiber.family.enncard := by
    exact prepared.callerStrict.full_fiber_uniform first second
  have hSecondSourceLower :
      density * tubeScale * secondFiber.family.enncard ≤
        secondShading.mass := by
    calc
      density * tubeScale * secondFiber.family.enncard =
          ∑ _index : Fin secondFiber.family.card,
            density * tubeScale := by
        simp [Kakeya.Streamlined.TubeFamily.enncard,
          Finset.sum_const, mul_comm]
      _ ≤
          ∑ index : Fin secondFiber.family.card,
            volume (secondShading.carrier index) := by
        apply Finset.sum_le_sum
        intro index _
        change
          (1 / 2 : ENNReal) *
                Kakeya.realRpowENN delta sourceLoss *
                Kakeya.realRpowENN delta 2 ≤
            volume
              (prepared.refinement.refined.carrier
                (secondFiber.embedding index))
        exact prepared.per_tube (secondFiber.embedding index)
      _ = secondShading.mass := rfl
  have hSecondLower :
      fraction *
            (density * tubeScale *
              secondFiber.family.enncard) ≤
        secondLocal.refinement.refined.mass := by
    calc
      fraction *
            (density * tubeScale *
              secondFiber.family.enncard) ≤
          fraction * secondShading.mass := by
        gcongr
      _ ≤ secondLocal.refinement.refined.mass :=
        secondLocal.refinement.retained_mass
  rw [
    wz2_paper_prepared_merged_parent_mass_eq_local
      prepared critical structural first,
    wz2_paper_prepared_merged_parent_mass_eq_local
      prepared critical structural second
  ]
  change
    (fraction * density) *
        firstLocal.refinement.refined.mass ≤
      (geometry * prepared.structuralConstant) *
        secondLocal.refinement.refined.mass
  calc
    (fraction * density) *
          firstLocal.refinement.refined.mass ≤
        (fraction * density) *
          (geometry * tubeScale * firstFiber.family.enncard) := by
      gcongr
    _ ≤
        (fraction * density) *
          (geometry * tubeScale *
            (prepared.structuralConstant *
              secondFiber.family.enncard)) := by
      gcongr
    _ =
        (geometry * prepared.structuralConstant) *
          (fraction *
            (density * tubeScale *
              secondFiber.family.enncard)) := by
      ring
    _ ≤
        (geometry * prepared.structuralConstant) *
          secondLocal.refinement.refined.mass := by
      gcongr

end Kakeya.Assouad

end
