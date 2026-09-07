import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoarseOwnerRegularizationStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperExternalWeightRegularization
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPositiveExternalWeightSupport
import MyLeanRepo.Kakeya.Assouad.PropStickyConvexWolffSubfamilyTransfer
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperNearbyCWAAdapters
import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteNearbySchedule

/-! # Ambient nearby-scale regularization of retained coarse owners -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_coarse_owner_regularization :
    WZ2PaperCoarseOwnerRegularizationStatement := by
  intro regularize recoverSupport delta rho hdelta hrho hrhoOne
    fine coarse cover
    sourceShading coarseCells availableFineCells balancing coarseData
    active multiplicityLevel degree dominant owned exactified
    ambientConstant outputConstant normalizationWeight weightUpper
    packedConstant hNormZero hNormTop hWeightTop hTotalLower
    hSourceWeightUpper levelCount hAmbient hAmbientTop hPower
    hOutput hLine hDistinct hNearby hTopLevel
    degreeConstant regularizationLoss hAbsorb
  let packed : Kakeya.Streamlined.TubeSubfamily coarse :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      coarse exactified.retainedParents
  let sourceWeight : Fin packed.family.card → ENNReal :=
    fun index =>
      MeasureTheory.volume
        (exactified.coarseShading.carrier index)
  let externalWeight : Fin coarse.card → ENNReal :=
    wz2PaperZeroExtendedExternalWeight packed sourceWeight
  have hCoarseNonempty : coarse.Nonempty := by
    dsimp only [Kakeya.Streamlined.TubeFamily.Nonempty]
    have hPackedCard : 0 < packed.family.card := by
      dsimp only [packed,
        Kakeya.Streamlined.TubeSubfamily.fromFinset]
      simpa using exactified.retainedParents_nonempty.card_pos
    have hCard :
        packed.family.card ≤ coarse.card := by
      simpa [Fintype.card_fin] using
        Fintype.card_le_of_injective
          packed.embedding packed.embedding.injective
    omega
  have hTotalWeight :
      (∑ index : Fin coarse.card, externalWeight index) =
        exactified.coarseShading.mass := by
    rw [sum_wz2PaperZeroExtendedExternalWeight]
    rfl
  have hWeightUpper :
      ∀ index, externalWeight index ≤ weightUpper := by
    apply wz2PaperZeroExtendedExternalWeight_le
    intro index
    exact hSourceWeightUpper index
  rcases
      regularize
        wz2_prop_sticky_finite_nearby_schedule
        hrho hrhoOne hCoarseNonempty hLine
        ambientConstant outputConstant normalizationWeight
        weightUpper hNormZero hNormTop hWeightTop
        externalWeight
        (by simpa [hTotalWeight] using hTotalLower)
        hWeightUpper levelCount hAmbient hAmbientTop hPower
        hOutput hNearby hAbsorb
    with ⟨regularized⟩
  rcases
      recoverSupport packed sourceWeight regularized.selected
        regularized.selected_weight_pos
    with ⟨support⟩
  let selectedShading : WZ1PaperTubeShading regularized.selected.family :=
    restrictPaperShading support.toPackedSubfamily
      exactified.coarseShading
  have hSelectedNonempty :
      regularized.selected.family.Nonempty :=
    regularized.selected_nonempty
  have hSelectedDistinct :
      WZ1PaperIsEssentiallyDistinct regularized.selected.family :=
    hDistinct.subfamily regularized.selected
  have hSelectedCWA :
      WZ2PaperCWAAtNearbyScales
        regularized.selected.family outputConstant :=
    regularized.cwa_nearby.withEssentiallyDistinct
      hSelectedDistinct
  have hSelectedWeight :
      regularized.selectedWeight = selectedShading.mass := by
    rw [regularized.selectedWeight_eq]
    rw [support.selected_weight_eq]
    apply Finset.sum_congr rfl
    intro index _
    rfl
  have hMassRetention :
      exactified.coarseShading.mass ≤
        regularized.regularizationLoss *
          selectedShading.mass := by
    rw [← hTotalWeight, ← hSelectedWeight]
    exact regularized.retained_weight
  have hTop :
      WZ2PaperConvexWolffBound
        regularized.selected.family
        ((normalizationWeight⁻¹ *
            (regularized.regularizationLoss * weightUpper)) *
          packedConstant) := by
    have hCardinality :
        normalizationWeight * coarse.enncard ≤
          (regularized.regularizationLoss * weightUpper) *
            regularized.selected.family.enncard :=
      regularized.cardinality_retention
    exact
      hTopLevel.subfamily_of_weighted_cardinality
        regularized.selected hNormZero hNormTop hCardinality
  exact ⟨{
    packed := packed
    packed_eq := rfl
    sourceWeight := sourceWeight
    sourceWeight_eq := fun _ => rfl
    externalWeight := externalWeight
    externalWeight_eq := rfl
    regularized := regularized
    support := support
    selectedShading := selectedShading
    selectedShading_eq := rfl
    selected_nonempty := hSelectedNonempty
    selected_cwa_nearby := hSelectedCWA
    selected_top_level_convex_wolff := hTop
    ambient_mass_lower := hTotalLower
    selected_mass_retention := hMassRetention
  }⟩

end Kakeya.Assouad

end
