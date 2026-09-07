import MyLeanRepo.Kakeya.Assouad.PureWZ2.PaperShadingMassFinite
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyFixedOriginBalancing
import MyLeanRepo.Kakeya.Assouad.PureWZ2.WeightedDegreeUniformRestrictedCWA
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PreparedScaleRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureCWAReindex
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCompleteFiberReindex
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCompleteFiberMassMonotone
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDirectOwnerPreparation
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDominantOwnerRefinement
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperOwnerParentBalancedPullback

/-!
# Same-family owner-parent selection

Run one weighted simultaneous degree selection on the complete dominant-owner
parents produced after whole-cell balancing.  The selected coarse family is
then realized by complete fibers and whole owned cells.  Consequently the
same final coarse family carries both pure nearby-scale CWA and the exact
balanced-cover certificate.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

noncomputable def pureWZ2SameFamilyDirectOwner
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
    (balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation) :
    WZ2PaperDirectOwnerPreparationData
      balancing.balanced.finalData.producer :=
  Classical.choice
    (wz2_paper_direct_owner_preparation
      balancing.balanced.finalData.producer)

def pureWZ2SameFamilyOwnerLoss
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
    (balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation)
    (owner :
      WZ2PaperDirectOwnerPreparationData
        balancing.balanced.finalData.producer) : ENNReal :=
  pureWZ2SameFamilyFixedOriginBalancingLoss balancing.balanced *
    wz2PaperDominantOwnerLoss owner.exactified

structure WZ2PaperOwnerParentSelectedData
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
    (owner :
      WZ2PaperDirectOwnerPreparationData producer)
    (outputConstant : ENNReal) where
  selectedPacked :
    Kakeya.Streamlined.TubeSubfamily
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        coarse owner.exactified.retainedParents).family
  selected_nonempty : selectedPacked.family.Nonempty
  selectionEpsilon : ℝ
  selectionEpsilon_pos : 0 < selectionEpsilon
  degreeConstant : ENNReal
  degreeConstant_ne_top : degreeConstant ≠ ⊤
  degreeConstant_eq :
    degreeConstant =
      16 * (geometricScaleCount selectionEpsilon : ENNReal) *
        (Nat.log 2 (2 *
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            coarse owner.exactified.retainedParents).family.card) + 1 :
          ENNReal) ^ geometricScaleCount selectionEpsilon
  regularizationLoss : ENNReal
  regularizationLoss_ne_top : regularizationLoss ≠ ⊤
  regularizationLoss_eq :
    regularizationLoss =
      8 *
        (Nat.log 2 (2 *
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            coarse owner.exactified.retainedParents).family.card) + 1 :
          ENNReal) ^ (geometricScaleCount selectionEpsilon + 1)
  selectedFiberMassLevel : ENNReal
  selectedFiberMassLevel_pos : 0 < selectedFiberMassLevel
  selectedFiberMassLevel_ne_top : selectedFiberMassLevel ≠ ⊤
  retained_fiber_mass :
    owner.exactified.refined.mass ≤
      regularizationLoss *
        ∑ parent : Fin selectedPacked.family.card,
          (restrictPaperShading
            (owner.exactified.restrictedCover.fullFiberSubfamily
              (selectedPacked.embedding parent))
            owner.exactified.refined).mass
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
  balancedPullback :
    WZ2PaperOwnerParentBalancedPullbackData owner selectedPacked
  retained_selected_mass :
    owner.exactified.refined.mass ≤
      regularizationLoss *
        balancedPullback.pullback.selectedFineShading.mass
  pure_cwa :
    WZ2PaperPureCWAAtNearbyScales
      selectedPacked.family outputConstant

theorem pureWZ2_same_family_owner_parent_selection
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (support : PureWZ2PositiveCallerSupportData quotient)
    (coordinateCount : ℕ)
    (regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount)
    (merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized)
    (scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled)
    (scaleSeparation : 18 * delta ≤ callerRequested.1)
    (balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation)
    (epsilon : ℝ)
    (epsilon_pos : 0 < epsilon)
    (caller_lt_one : callerRequested.1 < 1)
    (output_ne_top : outputConstant ≠ ⊤)
    (rounding_absorption :
      ENNReal.ofReal
          (Real.rpow callerRequested.1 (-epsilon)) *
          coarseConstant ≤
        outputConstant)
    (restriction_absorption :
      wz2PaperPureNearbyRestrictionConstant
          coarseConstant
          (sameFamily.parentMassLevel /
            pureWZ2SameFamilyOwnerLoss balancing
              (pureWZ2SameFamilyDirectOwner balancing))
          (pureWZ2WeightedDegreeConstant epsilon
            (WZ2PaperPureTubeSubfamily.ofTubeSubfamily
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                sameFamily.selectedCoarse.family
                (pureWZ2SameFamilyDirectOwner
                  balancing).exactified.retainedParents)).family.card)
          (pureWZ2WeightedRegularizationLoss epsilon
              (WZ2PaperPureTubeSubfamily.ofTubeSubfamily
                (Kakeya.Streamlined.TubeSubfamily.fromFinset
                  sameFamily.selectedCoarse.family
                  (pureWZ2SameFamilyDirectOwner
                    balancing).exactified.retainedParents)).family.card *
            (2 * sameFamily.parentMassLevel)) ≤
        outputConstant) :
    Nonempty
      (WZ2PaperOwnerParentSelectedData
        (pureWZ2SameFamilyDirectOwner balancing) outputConstant) := by
  let owner :
      WZ2PaperDirectOwnerPreparationData
        balancing.balanced.finalData.producer :=
    pureWZ2SameFamilyDirectOwner balancing
  let packed :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      sameFamily.selectedCoarse.family
      owner.exactified.retainedParents
  let preSelected :=
    WZ2PaperPureTubeSubfamily.ofTubeSubfamily packed
  let ownerFiberMass : Fin packed.family.card → ENNReal :=
    fun parent =>
      (restrictPaperShading
        (owner.exactified.restrictedCover.fullFiberSubfamily parent)
        owner.exactified.refined).mass
  let ownerLoss := pureWZ2SameFamilyOwnerLoss balancing owner
  let normalizationWeight := sameFamily.parentMassLevel / ownerLoss
  have parentMassLevel_ne_top :
      sameFamily.parentMassLevel ≠ ⊤ := by
    let parent : Fin sameFamily.selectedCoarse.family.card :=
      ⟨0, sameFamily.selectedCoarse_nonempty⟩
    let fiberShading :=
      restrictPaperShading
        ((sameFamily.pullback.internalPartitioningCover scaleSeparation)
          |>.fullFiberSubfamily parent)
        sameFamily.pullback.selectedFineShading
    have lower :
        sameFamily.parentMassLevel ≤ fiberShading.mass := by
      rw [(sameFamily.pullback.internalPartitioningCover scaleSeparation)
        |>.fullFiberShading_mass
          sameFamily.pullback.selectedFineShading parent]
      exact (sameFamily.parent_mass_band parent).1
    exact
      ne_top_of_le_ne_top
        (wz1PaperTubeShading_mass_ne_top fiberShading)
        lower
  have ownerLoss_ne_zero : ownerLoss ≠ 0 := by
    dsimp only [ownerLoss, pureWZ2SameFamilyOwnerLoss]
    unfold pureWZ2SameFamilyFixedOriginBalancingLoss
    unfold wz2PaperFinalBalancedCoverLoss
    unfold wz2PaperDominantOwnerLoss
    rw [owner.exactified.countBins_eq]
    simp only [wz2PaperBalancedParentDegreeCap]
    positivity
  have ownerLoss_ne_top : ownerLoss ≠ ⊤ := by
    dsimp only [ownerLoss, pureWZ2SameFamilyOwnerLoss]
    unfold pureWZ2SameFamilyFixedOriginBalancingLoss
    unfold wz2PaperFinalBalancedCoverLoss
    unfold wz2PaperDominantOwnerLoss
    rw [owner.exactified.countBins_eq]
    simp only [wz2PaperBalancedParentDegreeCap]
    repeat' apply ENNReal.mul_ne_top
    all_goals
      first
      | exact ENNReal.natCast_ne_top _
      | exact
          ENNReal.add_ne_top.mpr
            ⟨ENNReal.natCast_ne_top _, by norm_num⟩
      | norm_num
  have normalizationWeight_ne_zero : normalizationWeight ≠ 0 := by
    dsimp only [normalizationWeight]
    exact
      ENNReal.div_ne_zero.mpr
        ⟨sameFamily.parentMassLevel_pos.ne', ownerLoss_ne_top⟩
  have normalizationWeight_ne_top : normalizationWeight ≠ ⊤ := by
    dsimp only [normalizationWeight]
    exact ENNReal.div_ne_top parentMassLevel_ne_top ownerLoss_ne_zero
  have ownerFiberUpper :
      ∀ parent : Fin packed.family.card,
        ownerFiberMass parent ≤
          2 * sameFamily.parentMassLevel := by
    intro parent
    let ambientCover :=
      sameFamily.pullback.internalPartitioningCover scaleSeparation
    calc
      ownerFiberMass parent ≤
          (restrictPaperShading
            (ambientCover.fullFiberSubfamily
              (packed.embedding parent))
            sameFamily.pullback.selectedFineShading).mass := by
        apply
          wz2_paper_complete_fiber_mass_le
            ambientCover owner.exactified.selected
            owner.exactified.restrictedCover
            owner.exactified.refined
            sameFamily.pullback.selectedFineShading
        · intro index
          exact
            (owner.exactified_subshading index).trans
              (balancing.finalFine_subshading
                (owner.exactified.selected.embedding index))
        · exact owner.exactified.full_fiber_complete parent
      _ ≤ 2 * sameFamily.parentMassLevel := by
        rw [ambientCover.fullFiberShading_mass
          sameFamily.pullback.selectedFineShading
          (packed.embedding parent)]
        exact
          (sameFamily.parent_mass_band
            (packed.embedding parent)).2
  have ownerMassSum :
      (∑ parent : Fin packed.family.card, ownerFiberMass parent) =
        owner.exactified.refined.mass := by
    exact
      owner.exactified.restrictedCover
        |>.sum_fullFiberShading_mass owner.exactified.refined
  have preCardMass :
      sameFamily.parentMassLevel *
          sameFamily.selectedCoarse.family.enncard ≤
        sameFamily.pullback.selectedFineShading.mass := by
    let ambientCover :=
      sameFamily.pullback.internalPartitioningCover scaleSeparation
    rw [← ambientCover.sum_fullFiberShading_mass
      sameFamily.pullback.selectedFineShading]
    calc
      sameFamily.parentMassLevel *
            sameFamily.selectedCoarse.family.enncard =
          ∑ _parent : Fin sameFamily.selectedCoarse.family.card,
            sameFamily.parentMassLevel := by
        simp [Kakeya.Streamlined.TubeFamily.enncard,
          Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤
          ∑ parent : Fin sameFamily.selectedCoarse.family.card,
            (restrictPaperShading
              (ambientCover.fullFiberSubfamily parent)
              sameFamily.pullback.selectedFineShading).mass := by
        exact
          Finset.sum_le_sum fun parent _ => by
            rw [ambientCover.fullFiberShading_mass
              sameFamily.pullback.selectedFineShading parent]
            exact (sameFamily.parent_mass_band parent).1
  have ownerMassRetention :
      sameFamily.parentMassLevel *
          sameFamily.selectedCoarse.family.enncard ≤
        ownerLoss * owner.exactified.refined.mass := by
    let finalBalancedFine :=
      balancing.balanced.finalData.producer.coarseBand
        |>.selectedFineShading
    calc
      sameFamily.parentMassLevel *
            sameFamily.selectedCoarse.family.enncard ≤
          sameFamily.pullback.selectedFineShading.mass :=
        preCardMass
      _ ≤
          pureWZ2SameFamilyFixedOriginBalancingLoss balancing.balanced *
            finalBalancedFine.mass :=
        balancing.selected_mass_retention
      _ =
          pureWZ2SameFamilyFixedOriginBalancingLoss balancing.balanced *
            owner.exactAdapter.exact.refined.mass := by
        rw [owner.exactAdapter.exact_refined_eq]
      _ ≤
          pureWZ2SameFamilyFixedOriginBalancingLoss balancing.balanced *
            (wz2PaperDominantOwnerLoss owner.exactified *
              owner.exactified.refined.mass) := by
        gcongr
        exact
          wz2_paper_dominant_owner_mass_comparison
            owner.degree owner.dominant owner.exactified
      _ = ownerLoss * owner.exactified.refined.mass := by
        simp only [ownerLoss, pureWZ2SameFamilyOwnerLoss]
        ring
  have totalWeightLower :
      normalizationWeight *
          sameFamily.selectedCoarse.family.enncard ≤
        ∑ parent : Fin packed.family.card, ownerFiberMass parent := by
    rw [ownerMassSum]
    have divided :
        (sameFamily.parentMassLevel *
            sameFamily.selectedCoarse.family.enncard) / ownerLoss ≤
          owner.exactified.refined.mass := by
      rw [ENNReal.div_le_iff ownerLoss_ne_zero ownerLoss_ne_top]
      simpa [mul_comm] using ownerMassRetention
    simpa [normalizationWeight, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using divided
  rcases
      weighted_degree_uniform_restricted_cwa
        sameFamily.coarse_pure_cwa preSelected
        owner.exactified.retainedParents_nonempty.card_pos
        ownerFiberMass normalizationWeight
        (2 * sameFamily.parentMassLevel)
        normalizationWeight_ne_zero normalizationWeight_ne_top
        (ENNReal.mul_ne_top (by norm_num) parentMassLevel_ne_top)
        totalWeightLower ownerFiberUpper epsilon epsilon_pos
        (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
        caller_lt_one
        output_ne_top rounding_absorption
        (by
          simpa [owner, ownerLoss, normalizationWeight,
            preSelected, packed] using
            restriction_absorption)
    with
    ⟨selectedCoarse, selectedPacked, degreeConstant,
      regularizationLoss, selectedFiberMassLevel,
      selectedNonempty, degreeTop, regularizationTop,
      selectedFiberMassLevelPos, selectedFiberMassLevelTop,
      degreeEq, regularizationEq,
      familyEq, selectedEq, _cardEq,
      _reindex, retainedWeight, selectedWeightBand,
      _cardinalityRetention, pureCWA⟩
  let selectedPackedOrdinary := selectedPacked.toTubeSubfamily
  have selectedPackedNonempty :
      selectedPackedOrdinary.family.Nonempty := by
    change selectedPacked.family.Nonempty
    rw [← familyEq]
    exact selectedNonempty
  let balancedPullback :
      WZ2PaperOwnerParentBalancedPullbackData
        owner selectedPackedOrdinary :=
    Classical.choice <|
      wz2_paper_owner_subfamily_balanced_pullback
        owner selectedPackedOrdinary selectedPackedNonempty
  have retainedSelectedMass :
      owner.exactified.refined.mass ≤
        regularizationLoss *
          balancedPullback.pullback.selectedFineShading.mass := by
    calc
      owner.exactified.refined.mass =
          ∑ parent : Fin packed.family.card,
            ownerFiberMass parent := ownerMassSum.symm
      _ ≤
          regularizationLoss *
            ∑ parent : Fin selectedPacked.family.card,
              ownerFiberMass (selectedPacked.embedding parent) :=
        retainedWeight
      _ =
          regularizationLoss *
            balancedPullback.pullback.selectedFineShading.mass := by
        rw [balancedPullback.pullback.selectedFineShading_mass_eq]
        rfl
  exact
    ⟨{
      selectedPacked := selectedPackedOrdinary
      selected_nonempty := selectedPackedNonempty
      selectionEpsilon := epsilon
      selectionEpsilon_pos := epsilon_pos
      degreeConstant := degreeConstant
      degreeConstant_ne_top := degreeTop
      degreeConstant_eq := by
        change
          degreeConstant =
            16 * (geometricScaleCount epsilon : ENNReal) *
              (Nat.log 2 (2 * preSelected.family.card) + 1 :
                ENNReal) ^ geometricScaleCount epsilon
        exact degreeEq
      regularizationLoss := regularizationLoss
      regularizationLoss_ne_top := regularizationTop
      regularizationLoss_eq := by
        change
          regularizationLoss =
            8 *
              (Nat.log 2 (2 * preSelected.family.card) + 1 :
                ENNReal) ^ (geometricScaleCount epsilon + 1)
        exact regularizationEq
      selectedFiberMassLevel := selectedFiberMassLevel
      selectedFiberMassLevel_pos := selectedFiberMassLevelPos
      selectedFiberMassLevel_ne_top := selectedFiberMassLevelTop
      retained_fiber_mass := by
        change
          owner.exactified.refined.mass ≤
            regularizationLoss *
              ∑ parent : Fin selectedPacked.family.card,
                ownerFiberMass (selectedPacked.embedding parent)
        rw [← ownerMassSum]
        exact retainedWeight
      selected_fiber_mass_band := by
        intro parent
        change
          selectedFiberMassLevel ≤
              ownerFiberMass (selectedPacked.embedding parent) ∧
            ownerFiberMass (selectedPacked.embedding parent) ≤
              2 * selectedFiberMassLevel
        exact selectedWeightBand parent
      balancedPullback := balancedPullback
      retained_selected_mass := retainedSelectedMass
      pure_cwa := by
        change
          WZ2PaperPureCWAAtNearbyScales
            selectedPacked.family outputConstant
        rw [← familyEq]
        exact pureCWA
    }⟩

theorem pureWZ2_same_family_owner_selected_fiber_pure_cwa
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {constant : ENNReal}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    {selectedCoarse : Kakeya.Streamlined.TubeFamily rho}
    (restrictedCover :
      WZ2PaperPartitioningCover selected.family selectedCoarse)
    (parent : Fin selectedCoarse.card)
    (ambientParent : Fin coarse.card)
    (complete :
      Finset.image selected.embedding
          (wz2PaperFullFiberIndices
            selected.family selectedCoarse parent) =
        wz2PaperFullFiberIndices fine coarse ambientParent)
    (ambientCWA :
      WZ2PaperPureCWAAtNearbyScales
        (cover.fullFiberSubfamily ambientParent).family constant) :
    WZ2PaperPureCWAAtNearbyScales
      (restrictedCover.fullFiberSubfamily parent).family constant := by
  let localFiber := restrictedCover.fullFiberSubfamily parent
  let ambientFiber := cover.fullFiberSubfamily ambientParent
  let reindex :=
    Classical.choice <|
      wz2_paper_complete_fiber_reindex
        cover selected restrictedCover parent ambientParent complete
  let indexEquiv :
      Fin localFiber.family.card ≃ Fin ambientFiber.family.card :=
    Equiv.ofBijective reindex.localIndex reindex.localIndex_bijective
  have tubeEq :
      ∀ index,
        localFiber.family.tube index =
          ambientFiber.family.tube (indexEquiv index) := by
    intro index
    rw [localFiber.tube_eq, ambientFiber.tube_eq, selected.tube_eq]
    exact congrArg fine.tube (reindex.ambient_eq index)
  exact ambientCWA.reindex indexEquiv tubeEq

theorem pureWZ2_same_family_owner_final_fiber_pure_cwa
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
    (owner :
      WZ2PaperDirectOwnerPreparationData
        balancing.balanced.finalData.producer)
    (selectedPacked :
      Kakeya.Streamlined.TubeSubfamily
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          sameFamily.selectedCoarse.family
          owner.exactified.retainedParents).family)
    (pullback :
      WZ2PaperOwnerParentBalancedPullbackData
        owner selectedPacked)
    (parent : Fin selectedPacked.family.card) :
    WZ2PaperPureCWAAtNearbyScales
      (pullback.pullback.restrictedCover.fullFiberSubfamily parent).family
      fiberConstant := by
  let ambientCover :=
    sameFamily.pullback.internalPartitioningCover scaleSeparation
  let packed :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      sameFamily.selectedCoarse.family
      owner.exactified.retainedParents
  let ownerParent := selectedPacked.embedding parent
  let ambientParent := packed.embedding ownerParent
  have ownerCWA :
      WZ2PaperPureCWAAtNearbyScales
        (owner.exactified.restrictedCover.fullFiberSubfamily
          ownerParent).family fiberConstant :=
    pureWZ2_same_family_owner_selected_fiber_pure_cwa
      ambientCover owner.exactified.selected
      owner.exactified.restrictedCover ownerParent ambientParent
      (owner.exactified.full_fiber_complete ownerParent)
      (sameFamily.pullback.fiber_pure_cwa ambientParent)
  exact
    pureWZ2_same_family_owner_selected_fiber_pure_cwa
      owner.exactified.restrictedCover
      pullback.pullback.selectedFine
      pullback.pullback.restrictedCover parent ownerParent
      (pullback.pullback.full_fiber_complete parent) ownerCWA

end Kakeya.Assouad

end
