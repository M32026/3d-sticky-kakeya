import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyPostDeletionStructure
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PaperShadingMassFinite
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCompleteFiberMassMonotone
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDirectPositiveHalfMass

/-!
# Coarse cardinality retention after positive parent deletion

The H1 caller selection already puts all selected caller-fiber masses in one
dyadic band.  Direct balancing pays its explicit finite loss, and positive
whole-parent deletion retains half the resulting mass.  Since every surviving
fiber is complete and still has mass at most twice the original band level,
the number of surviving coarse parents retains the original coarse
cardinality up to `4 * balancingLoss`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2SameFamilyPositiveParentDeletionData

theorem parentMassLevel_ne_top
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {support : PureWZ2PositiveCallerSupportData quotient}
    {coordinateCount : ℕ}
    {regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount}
    {merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized}
    {scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    {sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled}
    {scaleSeparation : 18 * delta ≤ callerRequested.1}
    {balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation}
    {deletionExponent : ℕ}
    (data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent) :
    sameFamily.parentMassLevel ≠ ⊤ := by
  let parent : Fin sameFamily.selectedCoarse.family.card :=
    ⟨0, sameFamily.selectedCoarse_nonempty⟩
  let fiberShading :=
    restrictPaperShading
      ((sameFamily.pullback.internalPartitioningCover scaleSeparation)
        |>.fullFiberSubfamily parent)
      sameFamily.pullback.selectedFineShading
  have lower : sameFamily.parentMassLevel ≤ fiberShading.mass := by
    rw [(sameFamily.pullback.internalPartitioningCover scaleSeparation)
      |>.fullFiberShading_mass
        sameFamily.pullback.selectedFineShading parent]
    exact (sameFamily.parent_mass_band parent).1
  exact
    ne_top_of_le_ne_top
      (wz1PaperTubeShading_mass_ne_top fiberShading) lower

theorem retained_coarse_cardinality
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {support : PureWZ2PositiveCallerSupportData quotient}
    {coordinateCount : ℕ}
    {regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount}
    {merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized}
    {scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    {sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled}
    {scaleSeparation : 18 * delta ≤ callerRequested.1}
    {balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation}
    {deletionExponent : ℕ}
    (data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent) :
    sameFamily.selectedCoarse.family.enncard ≤
      (4 * pureWZ2SameFamilyFixedOriginBalancingLoss
        balancing.balanced) *
        data.selectedCoarse.family.enncard := by
  let level := sameFamily.parentMassLevel
  let preFine := sameFamily.pullback.selectedFineShading
  let balancedFine :=
    balancing.balanced.finalData.producer.coarseBand.selectedFineShading
  let finalFine := data.finalFineShading
  let ambientCover :=
    sameFamily.pullback.internalPartitioningCover scaleSeparation
  let restriction := data.post.postDeletion.deletion.restriction
  let finalCover := data.internalCover
  have preCardMass :
      level * sameFamily.selectedCoarse.family.enncard ≤
        preFine.mass := by
    rw [← ambientCover.sum_fullFiberShading_mass preFine]
    calc
      level * sameFamily.selectedCoarse.family.enncard =
          ∑ _parent : Fin sameFamily.selectedCoarse.family.card,
            level := by
        simp [Kakeya.Streamlined.TubeFamily.enncard,
          Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤
          ∑ parent : Fin sameFamily.selectedCoarse.family.card,
            (restrictPaperShading
              (ambientCover.fullFiberSubfamily parent) preFine).mass := by
        exact
          Finset.sum_le_sum fun parent _ => by
            rw [ambientCover.fullFiberShading_mass preFine parent]
            exact (sameFamily.parent_mass_band parent).1
  have finalFiberUpper :
      ∀ parent : Fin data.selectedCoarse.family.card,
        (restrictPaperShading
          (finalCover.fullFiberSubfamily parent) finalFine).mass ≤
            2 * level := by
    intro parent
    let ambientParent := data.selectedCoarse.embedding parent
    calc
      (restrictPaperShading
          (finalCover.fullFiberSubfamily parent) finalFine).mass ≤
          (restrictPaperShading
            (ambientCover.fullFiberSubfamily ambientParent)
            preFine).mass := by
        apply
          wz2_paper_complete_fiber_mass_le
            ambientCover data.selectedFine finalCover
            finalFine preFine
        · intro index
          exact
            (data.post.postDeletion.deletion.final_subshading index).trans
              (balancing.finalFine_subshading
                (data.selectedFine.embedding index))
        · exact restriction.full_fiber_complete parent
      _ ≤ 2 * level := by
        rw [ambientCover.fullFiberShading_mass preFine ambientParent]
        exact (sameFamily.parent_mass_band ambientParent).2
  have finalMassUpper :
      finalFine.mass ≤
        (2 * level) * data.selectedCoarse.family.enncard := by
    rw [← finalCover.sum_fullFiberShading_mass finalFine]
    calc
      (∑ parent : Fin data.selectedCoarse.family.card,
          (restrictPaperShading
            (finalCover.fullFiberSubfamily parent) finalFine).mass) ≤
          ∑ _parent : Fin data.selectedCoarse.family.card,
            2 * level := by
        exact Finset.sum_le_sum fun parent _ => finalFiberUpper parent
      _ = (2 * level) * data.selectedCoarse.family.enncard := by
        simp [Kakeya.Streamlined.TubeFamily.enncard,
          Finset.sum_const, nsmul_eq_mul]
        ring
  have weighted :
      level * sameFamily.selectedCoarse.family.enncard ≤
        level *
          ((4 * pureWZ2SameFamilyFixedOriginBalancingLoss
            balancing.balanced) *
            data.selectedCoarse.family.enncard) := by
    calc
      level * sameFamily.selectedCoarse.family.enncard ≤
          preFine.mass := preCardMass
      _ ≤
          pureWZ2SameFamilyFixedOriginBalancingLoss balancing.balanced *
            balancedFine.mass :=
        balancing.selected_mass_retention
      _ ≤
          pureWZ2SameFamilyFixedOriginBalancingLoss balancing.balanced *
            (2 * finalFine.mass) := by
        gcongr
        exact wz2_paper_direct_positive_half_mass data.post
      _ ≤
          pureWZ2SameFamilyFixedOriginBalancingLoss balancing.balanced *
            (2 * ((2 * level) *
              data.selectedCoarse.family.enncard)) := by
        gcongr
      _ =
          level *
            ((4 * pureWZ2SameFamilyFixedOriginBalancingLoss
              balancing.balanced) *
              data.selectedCoarse.family.enncard) := by ring
  have weightedRight :
      sameFamily.selectedCoarse.family.enncard * level ≤
        ((4 * pureWZ2SameFamilyFixedOriginBalancingLoss
          balancing.balanced) *
          data.selectedCoarse.family.enncard) * level := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using weighted
  exact
    (ENNReal.mul_le_mul_iff_left
      sameFamily.parentMassLevel_pos.ne'
      (data.parentMassLevel_ne_top)).mp weightedRight

end PureWZ2SameFamilyPositiveParentDeletionData

end Kakeya.Assouad

end
