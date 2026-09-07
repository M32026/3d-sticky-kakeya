import MyLeanRepo.Kakeya.Assouad.PureWZ2.GenericOwnerStructure
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PaperShadingMassFinite
import MyLeanRepo.Kakeya.Assouad.PureWZ2.WeightedDegreeUniformRestrictedCWA
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PreparedScaleRestriction

/-!
# Generic weighted owner-parent selection

Select owner parents by their complete refined-fiber shaded masses.  The
normalization uses the total refined mass divided by the ambient coarse
cardinality, so no caller-specific mass band is required.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem pureWZ2_generic_owner_selection
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
    {ambientConstant outputConstant : ENNReal}
    (ambientCWA :
      WZ2PaperPureCWAAtNearbyScales coarse ambientConstant)
    (epsilon : ℝ)
    (epsilonPos : 0 < epsilon)
    (rhoLtOne : rho < 1)
    (outputTop : outputConstant ≠ ⊤)
    (roundingAbsorption :
      ENNReal.ofReal (Real.rpow rho (-epsilon)) *
          ambientConstant ≤
        outputConstant)
    (restrictionAbsorption :
      wz2PaperPureNearbyRestrictionConstant
          ambientConstant
          (owner.exactified.refined.mass / coarse.enncard)
          (pureWZ2WeightedDegreeConstant epsilon
            (WZ2PaperPureTubeSubfamily.ofTubeSubfamily
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                coarse owner.exactified.retainedParents)).family.card)
          (pureWZ2WeightedRegularizationLoss epsilon
              (WZ2PaperPureTubeSubfamily.ofTubeSubfamily
                (Kakeya.Streamlined.TubeSubfamily.fromFinset
                  coarse owner.exactified.retainedParents)).family.card *
            owner.exactified.refined.mass) ≤
        outputConstant) :
    Nonempty
      (PureWZ2GenericOwnerSelectedData owner outputConstant) := by
  let packed :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      coarse owner.exactified.retainedParents
  let preSelected :=
    WZ2PaperPureTubeSubfamily.ofTubeSubfamily packed
  let fiberWeight : Fin packed.family.card → ENNReal :=
    fun parent =>
      (restrictPaperShading
        (owner.exactified.restrictedCover.fullFiberSubfamily parent)
        owner.exactified.refined).mass
  let totalMass := owner.exactified.refined.mass
  let normalizationWeight := totalMass / coarse.enncard
  have packedNonempty : packed.family.Nonempty :=
    owner.exactified.retainedParents_nonempty.card_pos
  have coarseNonempty : coarse.Nonempty := by
    let parent : Fin packed.family.card := ⟨0, packedNonempty⟩
    exact lt_of_le_of_lt (Nat.zero_le (packed.embedding parent).val)
      (packed.embedding parent).isLt
  have coarseENNZero : coarse.enncard ≠ 0 := by
    change (coarse.card : ENNReal) ≠ 0
    exact_mod_cast (Nat.ne_of_gt coarseNonempty)
  have coarseENNTop : coarse.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have weightSum :
      (∑ parent : Fin packed.family.card, fiberWeight parent) =
        totalMass := by
    dsimp only [fiberWeight, totalMass]
    exact
      owner.exactified.restrictedCover
        |>.sum_fullFiberShading_mass owner.exactified.refined
  have totalMassPos : 0 < totalMass := by
    let parent : Fin packed.family.card := ⟨0, packedNonempty⟩
    have floorPos : 0 < owner.exactified.balanced_cellMass := by
      rw [owner.exactified.balanced_cellMass_eq]
      exact ENNReal.mul_pos
        (by positivity : (2 ^ owner.exactified.level : ENNReal) ≠ 0)
        owner.active.fiberCellMass_pos.ne'
    have floorLe : owner.exactified.balanced_cellMass ≤ fiberWeight parent :=
      owner.exactified.parent_fiber_mass_floor parent
    have termLe :
        fiberWeight parent ≤
          ∑ current : Fin packed.family.card, fiberWeight current := by
      exact Finset.single_le_sum
        (fun _ _ => by positivity)
        (Finset.mem_univ parent)
    rw [weightSum] at termLe
    exact floorPos.trans_le (floorLe.trans termLe)
  have totalMassTop : totalMass ≠ ⊤ := by
    dsimp only [totalMass]
    exact wz1PaperTubeShading_mass_ne_top owner.exactified.refined
  have normalizationZero : normalizationWeight ≠ 0 := by
    dsimp only [normalizationWeight]
    exact ENNReal.div_ne_zero.mpr ⟨totalMassPos.ne', coarseENNTop⟩
  have normalizationTop : normalizationWeight ≠ ⊤ := by
    dsimp only [normalizationWeight]
    exact ENNReal.div_ne_top totalMassTop coarseENNZero
  have normalizationIdentity :
      normalizationWeight * coarse.enncard = totalMass := by
    dsimp only [normalizationWeight]
    exact ENNReal.div_mul_cancel coarseENNZero coarseENNTop
  have totalWeightLower :
      normalizationWeight * coarse.enncard ≤
        ∑ parent : Fin packed.family.card, fiberWeight parent := by
    rw [normalizationIdentity, weightSum]
  have weightUpper : ∀ parent, fiberWeight parent ≤ totalMass := by
    intro parent
    rw [← weightSum]
    exact Finset.single_le_sum
      (fun _ _ => by positivity)
      (Finset.mem_univ parent)
  rcases
      weighted_degree_uniform_restricted_cwa
        ambientCWA preSelected packedNonempty fiberWeight
        normalizationWeight totalMass
        normalizationZero normalizationTop totalMassTop
        totalWeightLower weightUpper
        epsilon epsilonPos hrho rhoLtOne
        outputTop roundingAbsorption
        (by
          simpa [normalizationWeight, totalMass, preSelected, packed] using
            restrictionAbsorption)
    with
    ⟨selected, selectedPre, _degreeConstant,
      regularizationLoss, selectedWeightLevel,
      selectedNonempty, _degreeTop, regularizationTop,
      selectedLevelPos, selectedLevelTop,
      _degreeEq, _regularizationEq,
      familyEq, selectedEq, _cardEq, _reindex,
      retainedWeight, selectedWeightBand,
      _cardinalityRetention, selectedCWA⟩
  let selectedPacked :
      Kakeya.Streamlined.TubeSubfamily packed.family :=
    {
      family := selectedPre.family
      embedding := selectedPre.embedding
      tube_eq := selectedPre.tube_eq
    }
  have selectedPackedNonempty : selectedPacked.family.Nonempty := by
    change selectedPre.family.Nonempty
    rw [← familyEq]
    exact selectedNonempty
  let balancedPullback :
      WZ2PaperOwnerParentBalancedPullbackData
        owner selectedPacked :=
    Classical.choice <|
      wz2_paper_owner_subfamily_balanced_pullback
        owner selectedPacked selectedPackedNonempty
  have selectedWeightSum :
      (∑ parent : Fin selectedPre.family.card,
          fiberWeight (selectedPre.embedding parent)) =
        balancedPullback.pullback.selectedFineShading.mass := by
    rw [balancedPullback.pullback.selectedFineShading_mass_eq]
    rfl
  have retainedSelectedMass :
      owner.exactified.refined.mass ≤
        regularizationLoss *
          balancedPullback.pullback.selectedFineShading.mass := by
    change
      totalMass ≤
        regularizationLoss *
          balancedPullback.pullback.selectedFineShading.mass
    rw [← weightSum, ← selectedWeightSum]
    exact retainedWeight
  exact
    ⟨{
      selectedPacked := selectedPacked
      selected_nonempty := selectedPackedNonempty
      regularizationLoss := regularizationLoss
      regularizationLoss_ne_top := regularizationTop
      selectedFiberMassLevel := selectedWeightLevel
      selectedFiberMassLevel_pos := selectedLevelPos
      selectedFiberMassLevel_ne_top := selectedLevelTop
      balancedPullback := balancedPullback
      retained_selected_mass := retainedSelectedMass
      selected_fiber_mass_band := by
        intro parent
        change
          selectedWeightLevel ≤
              fiberWeight (selectedPre.embedding parent) ∧
            fiberWeight (selectedPre.embedding parent) ≤
              2 * selectedWeightLevel
        exact selectedWeightBand parent
      pure_cwa := by
        change
          WZ2PaperPureCWAAtNearbyScales
            selectedPre.family outputConstant
        rw [← familyEq]
        exact selectedCWA
    }⟩

end Kakeya.Assouad

end
