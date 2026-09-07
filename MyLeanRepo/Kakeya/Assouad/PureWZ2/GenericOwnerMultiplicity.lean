import MyLeanRepo.Kakeya.Assouad.PureWZ2.GenericOwnerStructure
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GenericMultiplicityScalarNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureCWATopCardinalityLower
import MyLeanRepo.Kakeya.Assouad.PropStickyMultiplicityNormalization

/-!
# Multiplicity bounds for the generic owner-parent ABI

The owner preparation already supplies one dyadic point-multiplicity band on
every retained complete fiber.  The balanced pullback preserves those
complete fibers and their point multiplicities.  This module transports the
absolute cap to the generic final family and performs the two scalar
normalizations used by the frozen Node 3 output.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2GenericOwnerSelectedData

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) fineShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover fineShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover fineShading coarseCells availableFineCells
        balancing coarseData}
    {owner : WZ2PaperDirectOwnerPreparationData producer}
    {outputConstant : ENNReal}
    (data : PureWZ2GenericOwnerSelectedData owner outputConstant)

theorem final_fiber_shading_multiplicity_band :
    ∀ parent point,
      point ∈
          (restrictPaperShading
            (data.internalCover.fullFiberSubfamily parent)
            data.finalFineShading).union →
        (2 ^ producer.fiberBand.level : ENNReal) ≤
            ((restrictPaperShading
              (data.internalCover.fullFiberSubfamily parent)
              data.finalFineShading).pointMultiplicity point : ENNReal) ∧
          ((restrictPaperShading
            (data.internalCover.fullFiberSubfamily parent)
            data.finalFineShading).pointMultiplicity point : ENNReal) ≤
            (2 ^ (producer.fiberBand.level + 1) : ENNReal) := by
  intro parent point pointMem
  let ownerFiber :=
    owner.exactified.restrictedCover.fullFiberSubfamily
      (data.selectedPacked.embedding parent)
  let selectedFiber :=
    data.internalCover.fullFiberSubfamily parent
  let ownerShading :=
    restrictPaperShading ownerFiber owner.exactified.refined
  let selectedShading :=
    restrictPaperShading selectedFiber data.finalFineShading
  have pointEq :
      selectedShading.pointMultiplicity point =
        ownerShading.pointMultiplicity point :=
    data.balancedPullback.pullback.full_fiber_pointMultiplicity_eq
      parent point
  have selectedMultiplicityPos :
      0 < selectedShading.pointMultiplicity point := by
    rcases pointMem with ⟨index, indexMem⟩
    unfold Kakeya.Streamlined.Shading.pointMultiplicity
    exact
      Finset.card_pos.mpr
        ⟨index,
          Finset.mem_filter.mpr
            ⟨Finset.mem_univ index, indexMem⟩⟩
  have ownerMultiplicityPos :
      0 < ownerShading.pointMultiplicity point := by
    rwa [← pointEq]
  have ownerPoint : point ∈ ownerShading.union := by
    rcases Finset.card_pos.mp ownerMultiplicityPos with
      ⟨index, indexMem⟩
    exact ⟨index, (Finset.mem_filter.mp indexMem).2⟩
  have ownerBand :=
    owner.fiber_multiplicity_band
      (data.selectedPacked.embedding parent) point ownerPoint
  rw [pointEq]
  exact ⟨ownerBand.1, ownerBand.2.le⟩

theorem raw_fiber_pointMultiplicity_eq
    (parent : Fin data.selectedPacked.family.card)
    (point : Point3) :
    (((wz2PaperFullFiberIndices
        data.selectedFine.family data.selectedPacked.family parent).filter
        fun index =>
          point ∈ data.finalFineShading.carrier index).card : ENNReal) =
      ((restrictPaperShading
        (data.internalCover.fullFiberSubfamily parent)
        data.finalFineShading).pointMultiplicity point : ENNReal) := by
  have rawEq :
      (((wz2PaperFullFiberIndices
          data.selectedFine.family data.selectedPacked.family parent).filter
          fun index =>
            point ∈ data.finalFineShading.carrier index).card : ENNReal) =
        (data.internalCover.toWZ1PaperTubeCover.fiberPointMultiplicity
          data.finalFineShading parent point : ENNReal) := by
    unfold WZ1PaperTubeCover.fiberPointMultiplicity
    rw [← data.internalCover.fullFiberIndices_eq parent]
  rw [rawEq]
  rw [← data.internalCover.restrict_fullFiber_pointMultiplicity_eq
    data.finalFineShading parent point]

theorem final_fiber_pointMultiplicity_le_cap :
    ∀ parent point,
      (((wz2PaperFullFiberIndices
          data.selectedFine.family data.selectedPacked.family parent).filter
          fun index =>
            point ∈ data.finalFineShading.carrier index).card :
        ENNReal) ≤
          (2 ^ (producer.fiberBand.level + 1) : ENNReal) := by
  intro parent point
  let ownerFiber :=
    owner.exactified.restrictedCover.fullFiberSubfamily
      (data.selectedPacked.embedding parent)
  have pointEq :
      (restrictPaperShading
        (data.internalCover.fullFiberSubfamily parent)
        data.finalFineShading).pointMultiplicity point =
      (restrictPaperShading ownerFiber
        owner.exactified.refined).pointMultiplicity point :=
    data.balancedPullback.pullback.full_fiber_pointMultiplicity_eq
      parent point
  have ownerBand :
      ∀ point ∈
          (restrictPaperShading ownerFiber
            owner.exactified.refined).union,
        (2 ^ producer.fiberBand.level : ENNReal) ≤
            ((restrictPaperShading ownerFiber
              owner.exactified.refined).pointMultiplicity point :
              ENNReal) ∧
          ((restrictPaperShading ownerFiber
            owner.exactified.refined).pointMultiplicity point :
              ENNReal) <
            (2 ^ (producer.fiberBand.level + 1) : ENNReal) :=
    owner.fiber_multiplicity_band
      (data.selectedPacked.embedding parent)
  have multiplicityEq :
      (((wz2PaperFullFiberIndices
          data.selectedFine.family data.selectedPacked.family parent).filter
          fun index =>
            point ∈ data.finalFineShading.carrier index).card :
        ENNReal) =
      (data.internalCover.toWZ1PaperTubeCover.fiberPointMultiplicity
        data.finalFineShading parent point : ENNReal) := by
    unfold WZ1PaperTubeCover.fiberPointMultiplicity
    rw [← data.internalCover.fullFiberIndices_eq parent]
  rw [multiplicityEq]
  rw [← data.internalCover.restrict_fullFiber_pointMultiplicity_eq
    data.finalFineShading parent point]
  rw [pointEq]
  by_cases pointMem :
      point ∈
        (restrictPaperShading ownerFiber
          owner.exactified.refined).union
  · exact (ownerBand point pointMem).2.le
  · have pointMultiplicityZero :
        (restrictPaperShading ownerFiber
          owner.exactified.refined).pointMultiplicity point = 0 := by
      simp [Kakeya.Streamlined.Shading.pointMultiplicity,
        show ∀ index,
            point ∉
              (restrictPaperShading ownerFiber
                owner.exactified.refined).carrier index by
          intro index indexMem
          exact pointMem ⟨index, indexMem⟩]
    rw [pointMultiplicityZero]
    simp

theorem coarse_multiplicity_of_scalar
    {sigma outputLoss : ℝ}
    (scalar :
      (1 : ENNReal) ≤
        Kakeya.realRpowENN rho (2 - sigma - outputLoss) *
          data.selectedPacked.family.enncard) :
    ∀ point,
      (data.finalCoarseShading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN rho (2 - sigma - outputLoss) *
          data.selectedPacked.family.enncard := by
  intro point
  exact data.coarse_pointMultiplicity_le_one point |>.trans scalar

theorem coarse_multiplicity_of_cardinality_lower
    {sigma strongLoss outputLoss : ℝ}
    (rho_le_one : rho ≤ 1)
    (sigma_pos : 0 < sigma)
    (strongLoss_nonneg : 0 ≤ strongLoss)
    (loss_budget : 3 * strongLoss ≤ outputLoss)
    (cardinality_lower :
      Kakeya.realRpowENN rho (-2 + 2 * strongLoss) ≤
        data.selectedPacked.family.enncard) :
    ∀ point,
      (data.finalCoarseShading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN rho (2 - sigma - outputLoss) *
          data.selectedPacked.family.enncard := by
  apply data.coarse_multiplicity_of_scalar
  exact
    pureWZ2_coarse_multiplicity_scalar_of_cardinality_lower
      hrho rho_le_one sigma_pos strongLoss_nonneg loss_budget
      cardinality_lower

theorem coarse_multiplicity_of_pure_cwa
    {sigma strongLoss outputLoss : ℝ}
    (rho_le_one : rho ≤ 1)
    (sigma_pos : 0 < sigma)
    (strongLoss_nonneg : 0 ≤ strongLoss)
    (loss_budget : 3 * strongLoss ≤ outputLoss)
    (cardinality_absorption :
      (48 : ENNReal) * outputConstant ≤
        Kakeya.realRpowENN rho (-2 * strongLoss)) :
    ∀ point,
      (data.finalCoarseShading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN rho (2 - sigma - outputLoss) *
          data.selectedPacked.family.enncard := by
  apply data.coarse_multiplicity_of_cardinality_lower
    rho_le_one sigma_pos strongLoss_nonneg loss_budget
  exact
    pureWZ2_pure_cwa_cardinality_lower
      hrho rho_le_one data.selected_nonempty data.pure_cwa
      cardinality_absorption

theorem rescaled_fiber_source_cardinality_lower
    {sigma strongLoss outputLoss : ℝ}
    (ratio_pos : 0 < delta / rho)
    (ratio_le_one : delta / rho ≤ 1)
    (rescaledFiber :
      ∀ parent : Fin data.selectedPacked.family.card,
        Nonempty
          (WZ2PaperPureRescaledFullFiberOutput
            (sigma := sigma) (loss := outputLoss)
            (restrictPaperShading
              (data.internalCover.fullFiberSubfamily parent)
              data.finalFineShading)
            (data.selectedPacked.family.tube parent) hrho))
    (cardinality_absorption :
      (48 : ENNReal) *
            Kakeya.realRpowENN (delta / rho) (-outputLoss) ≤
        Kakeya.realRpowENN (delta / rho) (-2 * strongLoss)) :
    ∀ parent : Fin data.selectedPacked.family.card,
      Kakeya.realRpowENN (delta / rho)
          (-2 + 2 * strongLoss) ≤
        ((wz2PaperFullFiberIndices
          data.selectedFine.family
          data.selectedPacked.family parent).card : ENNReal) := by
  intro parent
  let output := Classical.choice (rescaledFiber parent)
  have publicLower :
      Kakeya.realRpowENN (delta / rho)
          (-2 + 2 * strongLoss) ≤
        output.rescalingCertificate.publicFamily.enncard :=
    pureWZ2_pure_cwa_cardinality_lower
      ratio_pos ratio_le_one output.extremal.nonempty
      output.extremal.cwa_nearby_scales cardinality_absorption
  have sourceCardinality :
      output.rescalingCertificate.publicFamily.enncard =
        ((wz2PaperFullFiberIndices
          data.selectedFine.family
          data.selectedPacked.family parent).card : ENNReal) := by
    calc
      output.rescalingCertificate.publicFamily.enncard =
          (data.internalCover.fullFiberSubfamily parent).family.enncard :=
        output.source_cardinality_eq
      _ =
          ((wz2PaperFullFiberIndices
            data.selectedFine.family
            data.selectedPacked.family parent).card : ENNReal) := by
        rfl
  rw [sourceCardinality] at publicLower
  exact publicLower

theorem fiber_multiplicity_of_cap
    {sigma outputLoss : ℝ}
    (capUpper :
      ∀ parent : Fin data.selectedPacked.family.card,
        (2 ^ (producer.fiberBand.level + 1) : ENNReal) ≤
          Kakeya.realRpowENN (delta / rho)
              (2 - sigma - outputLoss) *
            ((wz2PaperFullFiberIndices
              data.selectedFine.family
              data.selectedPacked.family parent).card : ENNReal)) :
    ∀ parent point,
      (((wz2PaperFullFiberIndices
          data.selectedFine.family data.selectedPacked.family parent).filter
          fun index =>
            point ∈ data.finalFineShading.carrier index).card : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - outputLoss) *
          ((wz2PaperFullFiberIndices
            data.selectedFine.family
            data.selectedPacked.family parent).card : ENNReal) := by
  intro parent point
  exact
    (data.final_fiber_pointMultiplicity_le_cap parent point).trans
      (capUpper parent)

theorem fiber_multiplicity_of_strong_cap_and_cardinality_lower
    {sigma strongLoss outputLoss : ℝ}
    (ratio_pos : 0 < delta / rho)
    (ratio_le_one : delta / rho ≤ 1)
    (loss_budget : 3 * strongLoss ≤ outputLoss)
    (strong_cap :
      (2 ^ (producer.fiberBand.level + 1) : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
          (-sigma - strongLoss))
    (cardinality_lower :
      ∀ parent : Fin data.selectedPacked.family.card,
        Kakeya.realRpowENN (delta / rho)
            (-2 + 2 * strongLoss) ≤
          ((wz2PaperFullFiberIndices
            data.selectedFine.family
            data.selectedPacked.family parent).card : ENNReal)) :
    ∀ parent point,
      (((wz2PaperFullFiberIndices
          data.selectedFine.family data.selectedPacked.family parent).filter
          fun index =>
            point ∈ data.finalFineShading.carrier index).card : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - outputLoss) *
          ((wz2PaperFullFiberIndices
            data.selectedFine.family
            data.selectedPacked.family parent).card : ENNReal) := by
  apply data.fiber_multiplicity_of_cap
  intro parent
  exact
    pureWZ2_fiber_cap_upper_of_strong_cap_and_cardinality_lower
      ratio_pos ratio_le_one loss_budget strong_cap
      (cardinality_lower parent)

end PureWZ2GenericOwnerSelectedData

end Kakeya.Assouad

end
