import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDirectOwnerPreparation
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperOwnerParentBalancedPullback
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperOwnerParentBalancedMultiplicity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky

/-!
# Generic public structure after owner-parent selection

This file exposes the owner-parent pullback without retaining the historical
quotient-net types used to construct the ambient balanced producer.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2GenericOwnerSelectedData
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
    (owner : WZ2PaperDirectOwnerPreparationData producer)
    (outputConstant : ENNReal) where
  selectedPacked :
    Kakeya.Streamlined.TubeSubfamily
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        coarse owner.exactified.retainedParents).family
  selected_nonempty : selectedPacked.family.Nonempty
  regularizationLoss : ENNReal
  regularizationLoss_ne_top : regularizationLoss ≠ ⊤
  selectedFiberMassLevel : ENNReal
  selectedFiberMassLevel_pos : 0 < selectedFiberMassLevel
  selectedFiberMassLevel_ne_top : selectedFiberMassLevel ≠ ⊤
  balancedPullback :
    WZ2PaperOwnerParentBalancedPullbackData owner selectedPacked
  retained_selected_mass :
    owner.exactified.refined.mass ≤
      regularizationLoss *
        balancedPullback.pullback.selectedFineShading.mass
  selected_fiber_mass_band :
    ∀ parent : Fin selectedPacked.family.card,
      selectedFiberMassLevel ≤
          (restrictPaperShading
            (owner.exactified.restrictedCover.fullFiberSubfamily
              (selectedPacked.embedding parent))
            owner.exactified.refined).mass ∧
        (restrictPaperShading
          (owner.exactified.restrictedCover.fullFiberSubfamily
            (selectedPacked.embedding parent))
          owner.exactified.refined).mass ≤
          2 * selectedFiberMassLevel
  pure_cwa :
    WZ2PaperPureCWAAtNearbyScales
      selectedPacked.family outputConstant

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

noncomputable def packed :
    Kakeya.Streamlined.TubeSubfamily coarse :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset
    coarse owner.exactified.retainedParents

noncomputable def selectedCoarse :
    Kakeya.Streamlined.TubeSubfamily coarse :=
  (packed (owner := owner)).comp data.selectedPacked

noncomputable def selectedFine :
    Kakeya.Streamlined.TubeSubfamily fine :=
  owner.exactified.selected.comp
    data.balancedPullback.pullback.selectedFine

noncomputable def finalFineShading :
    WZ1PaperTubeShading data.selectedFine.family :=
  data.balancedPullback.pullback.selectedFineShading

noncomputable def finalCoarseShading :
    WZ1PaperTubeShading data.selectedPacked.family :=
  data.balancedPullback.pullback.selectedCoarseShading

noncomputable def internalCover :
    WZ2PaperPartitioningCover
      data.selectedFine.family data.selectedPacked.family :=
  data.balancedPullback.pullback.restrictedCover

noncomputable def section6Cover
    (fineLine : WZ1PaperIsLineClass fine)
    (coarseLine : WZ1PaperIsLineClass coarse)
    (coarseDistinct : WZ1PaperIsEssentiallyDistinct coarse) :
    PureWZ2Section6Cover
      data.selectedFine.family data.selectedPacked.family := by
  let restricted := data.internalCover
  exact
    {
      fine_line_class := fineLine.subfamily data.selectedFine
      coarse_line_class :=
        coarseLine.subfamily (selectedCoarse data)
      covers := fun source =>
        ⟨restricted.parent source,
          restricted.parent_covers source⟩
      parent_hit := by
        intro parent
        rcases restricted.parent_surjective parent with
          ⟨source, hsource⟩
        exact
          ⟨source, hsource ▸ restricted.parent_covers source⟩
      coarse_essentially_distinct :=
        coarseDistinct.subfamily (selectedCoarse data)
    }

noncomputable def publicBalanced
    (fineLine : WZ1PaperIsLineClass fine)
    (coarseLine : WZ1PaperIsLineClass coarse)
    (coarseDistinct : WZ1PaperIsEssentiallyDistinct coarse) :
    PureWZ2BalancedCoverData
      (data.section6Cover fineLine coarseLine coarseDistinct)
      data.finalFineShading data.finalCoarseShading := by
  let historical := data.balancedPullback.balanced
  let restricted := data.internalCover
  exact
    {
      point_compatibility := by
        intro source parent hcovered point hpoint
        have hparent : parent = restricted.parent source :=
          restricted.parent_unique source parent hcovered
        subst parent
        exact historical.point_compatibility source point hpoint
      coarse_cubical := historical.coarse_cubical
      activeCells := historical.activeCells
      coarse_union_eq := historical.coarse_union_eq
      cellMass := historical.cellMass
      cellMass_pos := historical.cellMass_pos
      cellMass_ne_top := historical.cellMass_ne_top
      fine_cell_mass := historical.fine_cell_mass
    }

theorem coarse_pointMultiplicity_le_one :
    ∀ point,
      (data.finalCoarseShading.pointMultiplicity point : ENNReal) ≤ 1 :=
  data.balancedPullback.coarse_pointMultiplicity_le_one

/-- The generic owner's selected parent family remains a subfamily of the
ambient coarse family. -/
theorem selectedPacked_enncard_le_coarse :
    data.selectedPacked.family.enncard ≤ coarse.enncard := by
  change
    (data.selectedPacked.family.card : ENNReal) ≤
      (coarse.card : ENNReal)
  have cardLe :
      data.selectedPacked.family.card ≤ coarse.card := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective
        (data.selectedPacked.embedding.trans
          (packed (owner := owner)).embedding)
        (data.selectedPacked.embedding.trans
          (packed (owner := owner)).embedding).injective
  exact_mod_cast cardLe

/-- The selected fiber mass band gives a sharp factor-two upper bound for
each final fine fiber. -/
theorem finalFiber_mass_upper
    (parent : Fin data.selectedPacked.family.card) :
    (restrictPaperShading
      (data.internalCover.fullFiberSubfamily parent)
      data.finalFineShading).mass ≤
        2 * data.selectedFiberMassLevel := by
  calc
    (restrictPaperShading
        (data.internalCover.fullFiberSubfamily parent)
        data.finalFineShading).mass =
      (restrictPaperShading
        (owner.exactified.restrictedCover.fullFiberSubfamily
          (data.selectedPacked.embedding parent))
        owner.exactified.refined).mass :=
      data.balancedPullback.pullback.full_fiber_mass_eq parent
    _ ≤ 2 * data.selectedFiberMassLevel :=
      (data.selected_fiber_mass_band parent).2

/-- Summing the selected fiber mass band bounds the final fine shading. -/
theorem finalFineShading_mass_upper :
    data.finalFineShading.mass ≤
      data.selectedPacked.family.enncard *
        (2 * data.selectedFiberMassLevel) := by
  rw [← data.internalCover.sum_fullFiberShading_mass
    data.finalFineShading]
  calc
    (∑ parent : Fin data.selectedPacked.family.card,
        (restrictPaperShading
          (data.internalCover.fullFiberSubfamily parent)
          data.finalFineShading).mass) ≤
        ∑ _parent : Fin data.selectedPacked.family.card,
          2 * data.selectedFiberMassLevel := by
      apply Finset.sum_le_sum
      intro parent _
      exact data.finalFiber_mass_upper parent
    _ =
        data.selectedPacked.family.enncard *
          (2 * data.selectedFiberMassLevel) := by
      simp [Kakeya.Streamlined.TubeFamily.enncard,
        Finset.sum_const]

/-- The second weighted selection retains an explicit lower bound for its
common fiber-mass level. The selected-parent cardinality is bounded by the
ambient coarse cardinality, which cancels the normalization denominator. -/
theorem normalizationWeight_le_selectedFiberMassLevel :
    owner.exactified.refined.mass / coarse.enncard ≤
      (data.regularizationLoss * 2) * data.selectedFiberMassLevel := by
  have coarseNonempty : coarse.Nonempty := by
    let parent : Fin data.selectedPacked.family.card :=
      ⟨0, data.selected_nonempty⟩
    exact
      lt_of_le_of_lt
        (Nat.zero_le ((data.selectedCoarse).embedding parent).val)
        ((data.selectedCoarse).embedding parent).isLt
  have coarseZero : coarse.enncard ≠ 0 := by
    change (coarse.card : ENNReal) ≠ 0
    exact_mod_cast (Nat.ne_of_gt coarseNonempty)
  have coarseTop : coarse.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have totalMassUpper :
      owner.exactified.refined.mass ≤
        ((data.regularizationLoss * 2) *
          data.selectedFiberMassLevel) * coarse.enncard := by
    calc
      owner.exactified.refined.mass ≤
          data.regularizationLoss * data.finalFineShading.mass :=
        data.retained_selected_mass
      _ ≤
          data.regularizationLoss *
            (data.selectedPacked.family.enncard *
              (2 * data.selectedFiberMassLevel)) := by
        gcongr
        exact data.finalFineShading_mass_upper
      _ ≤
          data.regularizationLoss *
            (coarse.enncard * (2 * data.selectedFiberMassLevel)) := by
        gcongr
        exact data.selectedPacked_enncard_le_coarse
      _ =
          ((data.regularizationLoss * 2) *
            data.selectedFiberMassLevel) * coarse.enncard := by ring
  rw [ENNReal.div_le_iff coarseZero coarseTop]
  simpa [mul_comm] using totalMassUpper

end PureWZ2GenericOwnerSelectedData

end Kakeya.Assouad

end
