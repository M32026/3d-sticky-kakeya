import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCompleteCoarseSelectionPullback
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperExternalWeightRegularization
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPositiveExternalWeightSupport
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperNearbyCWAAdapters
import MyLeanRepo.Kakeya.Assouad.PropStickyConvexWolffSubfamilyTransfer
import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteNearbySchedule

/-!
# Complete-fiber-mass regularization after final parent deletion

The paper's second coarse-parent pigeonholing must preserve complete fine
fibers.  Its external weight is therefore the full shaded mass of one
surviving parent fiber, not the volume of an arbitrarily reassigned
owner-cell carrier.

The resulting selected coarse family has restored nearby-scale CWA.  Pulling
back all complete selected fibers preserves the selected weight exactly, so
the external-weight retention theorem becomes a genuine retained-mass
estimate for the selected fine shading.  Every selected complete fiber also
lies in one common factor-two mass band.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperPostDeletionFiberMassRegularizationData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambient : Kakeya.Streamlined.TubeFamily rho}
    (packed : Kakeya.Streamlined.TubeSubfamily ambient)
    (cover : WZ2PaperPartitioningCover fine packed.family)
    (fineShading : WZ1PaperTubeShading fine)
    (packedCoarseShading : WZ1PaperTubeShading packed.family)
    (ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal)
    (levelCount : ℕ) where
  sourceWeight : Fin packed.family.card → ENNReal
  sourceWeight_eq :
    ∀ parent,
      sourceWeight parent =
        (restrictPaperShading
          (cover.fullFiberSubfamily parent)
          fineShading).mass
  externalWeight : Fin ambient.card → ENNReal
  externalWeight_eq :
    externalWeight =
      wz2PaperZeroExtendedExternalWeight packed sourceWeight
  regularized :
    WZ2PaperExternalWeightRegularizationData
      (family := ambient)
      ambientConstant outputConstant normalizationWeight weightUpper
      levelCount externalWeight
  support :
    WZ2PaperPositiveExternalWeightSupportData
      packed sourceWeight regularized.selected
  pullback :
    WZ2PaperCompleteCoarseSelectionPullbackData
      cover fineShading packedCoarseShading
      support.toPackedSubfamily
  selected_essentially_distinct :
    WZ1PaperIsEssentiallyDistinct regularized.selected.family
  selected_cwa_nearby :
    WZ2PaperCWAAtNearbyScales
      regularized.selected.family outputConstant
  selected_top_level_convex_wolff :
    WZ2PaperConvexWolffBound
      regularized.selected.family
      ((normalizationWeight⁻¹ *
          (regularized.regularizationLoss * weightUpper)) *
        packedConstant)
  selectedFine_mass_eq :
    regularized.selectedWeight =
      pullback.selectedFineShading.mass
  retained_mass :
    fineShading.mass ≤
      regularized.regularizationLoss *
        pullback.selectedFineShading.mass
  selectedFiberMassLevel : ENNReal
  selectedFiberMassLevel_pos : 0 < selectedFiberMassLevel
  selectedFiberMassLevel_ne_top : selectedFiberMassLevel ≠ ⊤
  selected_fiber_mass_band :
    ∀ parent : Fin regularized.selected.family.card,
      selectedFiberMassLevel ≤
          (restrictPaperShading
            (pullback.restrictedCover.fullFiberSubfamily parent)
            pullback.selectedFineShading).mass ∧
        (restrictPaperShading
          (pullback.restrictedCover.fullFiberSubfamily parent)
          pullback.selectedFineShading).mass ≤
            2 * selectedFiberMassLevel

theorem wz2_paper_post_deletion_fiber_mass_regularization
    {delta rho : ℝ}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambient : Kakeya.Streamlined.TubeFamily rho}
    (packed : Kakeya.Streamlined.TubeSubfamily ambient)
    (cover : WZ2PaperPartitioningCover fine packed.family)
    (fineShading : WZ1PaperTubeShading fine)
    (packedCoarseShading : WZ1PaperTubeShading packed.family)
    (hAmbientNonempty : ambient.Nonempty)
    (hAmbientLine : WZ1PaperIsLineClass ambient)
    (hAmbientDistinct : WZ1PaperIsEssentiallyDistinct ambient)
    (hFineCubical : WZ1PaperIsCubicalShading fineShading)
    (hCoarseCubical : WZ1PaperIsCubicalShading packedCoarseShading)
    (hCompatibility :
      ∀ source point,
        point ∈ fineShading.carrier source →
          point ∈ packedCoarseShading.carrier (cover.parent source))
    (ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal)
    (hNormZero : normalizationWeight ≠ 0)
    (hNormTop : normalizationWeight ≠ ⊤)
    (hWeightTop : weightUpper ≠ ⊤)
    (hTotalLower :
      normalizationWeight * ambient.enncard ≤
        fineShading.mass)
    (hWeightUpper :
      ∀ parent,
        (restrictPaperShading
          (cover.fullFiberSubfamily parent)
          fineShading).mass ≤
            weightUpper)
    (levelCount : ℕ)
    (hAmbient : 2 < ambientConstant)
    (hAmbientTop : ambientConstant ≠ ⊤)
    (hPower :
      ENNReal.ofReal (1 / rho) ≤
        ambientConstant ^ levelCount)
    (hOutput :
      ambientConstant * ambientConstant ≤ outputConstant)
    (hNearby :
      WZ2PaperCWACoversAtNearbyScales ambient ambientConstant)
    (hPackedTop :
      WZ2PaperConvexWolffBound packed.family packedConstant)
    (hAbsorb :
      let degreeConstant :=
        16 * ((levelCount + 1 : ℕ) : ENNReal) *
          (Nat.log 2 (2 * ambient.card) + 1 : ENNReal) ^
            (levelCount + 1)
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * ambient.card) + 1 : ENNReal) ^
            (levelCount + 2)
      max degreeConstant
          ((normalizationWeight⁻¹ *
              (ambientConstant *
                (regularizationLoss * weightUpper) *
                degreeConstant)) *
            ambientConstant) ≤
        outputConstant) :
    Nonempty
      (WZ2PaperPostDeletionFiberMassRegularizationData
        packed cover fineShading packedCoarseShading
        ambientConstant outputConstant normalizationWeight weightUpper
        packedConstant levelCount) := by
  let sourceWeight : Fin packed.family.card → ENNReal :=
    fun parent =>
      (restrictPaperShading
        (cover.fullFiberSubfamily parent)
        fineShading).mass
  let externalWeight : Fin ambient.card → ENNReal :=
    wz2PaperZeroExtendedExternalWeight packed sourceWeight
  have hSourceSum :
      (∑ parent : Fin packed.family.card, sourceWeight parent) =
        fineShading.mass := by
    dsimp only [sourceWeight]
    exact cover.sum_fullFiberShading_mass fineShading
  have hExternalSum :
      (∑ index : Fin ambient.card, externalWeight index) =
        fineShading.mass := by
    rw [show externalWeight =
        wz2PaperZeroExtendedExternalWeight packed sourceWeight by rfl]
    rw [sum_wz2PaperZeroExtendedExternalWeight, hSourceSum]
  have hExternalUpper :
      ∀ index, externalWeight index ≤ weightUpper := by
    apply wz2PaperZeroExtendedExternalWeight_le
    intro parent
    exact hWeightUpper parent
  rcases
      wz2_paper_external_weight_regularization
        wz2_prop_sticky_finite_nearby_schedule
        hrho hrhoOne hAmbientNonempty hAmbientLine
        ambientConstant outputConstant normalizationWeight weightUpper
        hNormZero hNormTop hWeightTop externalWeight
        (by simpa [hExternalSum] using hTotalLower)
        hExternalUpper levelCount hAmbient hAmbientTop hPower hOutput
        hNearby hAbsorb
    with ⟨regularized⟩
  rcases
      wz2_paper_positive_external_weight_support
        packed sourceWeight regularized.selected
        regularized.selected_weight_pos
    with ⟨support⟩
  rcases
      wz2_paper_complete_coarse_selection_pullback
        cover fineShading packedCoarseShading
        hFineCubical hCoarseCubical hCompatibility
        support.toPackedSubfamily
    with ⟨pullback⟩
  have hSelectedDistinct :
      WZ1PaperIsEssentiallyDistinct regularized.selected.family :=
    hAmbientDistinct.subfamily regularized.selected
  have hSelectedCWA :
      WZ2PaperCWAAtNearbyScales
        regularized.selected.family outputConstant :=
    regularized.cwa_nearby.withEssentiallyDistinct hSelectedDistinct
  have hSelectedWeight :
      regularized.selectedWeight =
        pullback.selectedFineShading.mass := by
    calc
      regularized.selectedWeight =
          ∑ parent : Fin regularized.selected.family.card,
            externalWeight (regularized.selected.embedding parent) :=
        regularized.selectedWeight_eq
      _ =
          ∑ parent : Fin regularized.selected.family.card,
            sourceWeight (support.packedIndex parent) := by
        simpa [externalWeight] using support.selected_weight_eq
      _ =
          ∑ parent : Fin regularized.selected.family.card,
            (restrictPaperShading
              (pullback.restrictedCover.fullFiberSubfamily parent)
              pullback.selectedFineShading).mass := by
        apply Finset.sum_congr rfl
        intro parent _
        rw [pullback.full_fiber_mass_eq parent]
        rfl
      _ = pullback.selectedFineShading.mass :=
        pullback.restrictedCover
          |>.sum_fullFiberShading_mass pullback.selectedFineShading
  have hRetained :
      fineShading.mass ≤
        regularized.regularizationLoss *
          pullback.selectedFineShading.mass := by
    calc
      fineShading.mass =
          ∑ index : Fin ambient.card, externalWeight index :=
        hExternalSum.symm
      _ ≤
          regularized.regularizationLoss *
            regularized.selectedWeight :=
        regularized.retained_weight
      _ =
          regularized.regularizationLoss *
            pullback.selectedFineShading.mass := by
        rw [hSelectedWeight]
  have hPackedCardinality :
      normalizationWeight * packed.family.enncard ≤
        (regularized.regularizationLoss * weightUpper) *
          regularized.selected.family.enncard := by
    have hPackedCard : packed.family.card ≤ ambient.card := by
      simpa only [Fintype.card_fin] using
        Fintype.card_le_of_injective
          packed.embedding packed.embedding.injective
    have hPackedENN : packed.family.enncard ≤ ambient.enncard := by
      change (packed.family.card : ENNReal) ≤
        (ambient.card : ENNReal)
      exact_mod_cast hPackedCard
    calc
      normalizationWeight * packed.family.enncard ≤
          normalizationWeight * ambient.enncard := by
        gcongr
      _ ≤
          (regularized.regularizationLoss * weightUpper) *
            regularized.selected.family.enncard :=
        regularized.cardinality_retention
  have hTopLevel :
      WZ2PaperConvexWolffBound
        regularized.selected.family
        ((normalizationWeight⁻¹ *
            (regularized.regularizationLoss * weightUpper)) *
          packedConstant) :=
    hPackedTop.subfamily_of_weighted_cardinality
      (K := regularized.regularizationLoss * weightUpper)
      support.toPackedSubfamily hNormZero hNormTop
      hPackedCardinality
  have hFiberBand :
      ∀ parent : Fin regularized.selected.family.card,
        regularized.selectedWeightLevel ≤
            (restrictPaperShading
              (pullback.restrictedCover.fullFiberSubfamily parent)
              pullback.selectedFineShading).mass ∧
          (restrictPaperShading
            (pullback.restrictedCover.fullFiberSubfamily parent)
            pullback.selectedFineShading).mass ≤
              2 * regularized.selectedWeightLevel := by
    intro parent
    have hBand := regularized.selected_weight_band parent
    have hPointWeight :
        externalWeight (regularized.selected.embedding parent) =
          sourceWeight (support.packedIndex parent) := by
      simpa [externalWeight] using support.point_weight_eq parent
    have hFiberMass :
        (restrictPaperShading
          (pullback.restrictedCover.fullFiberSubfamily parent)
          pullback.selectedFineShading).mass =
            sourceWeight (support.packedIndex parent) := by
      calc
        (restrictPaperShading
            (pullback.restrictedCover.fullFiberSubfamily parent)
            pullback.selectedFineShading).mass =
            (restrictPaperShading
              (cover.fullFiberSubfamily
                (support.toPackedSubfamily.embedding parent))
              fineShading).mass :=
          pullback.full_fiber_mass_eq parent
        _ = sourceWeight (support.packedIndex parent) := by
          rfl
    constructor
    · calc
        regularized.selectedWeightLevel ≤
            externalWeight (regularized.selected.embedding parent) :=
          hBand.1
        _ = sourceWeight (support.packedIndex parent) :=
          hPointWeight
        _ =
            (restrictPaperShading
              (pullback.restrictedCover.fullFiberSubfamily parent)
              pullback.selectedFineShading).mass :=
          hFiberMass.symm
    · calc
        (restrictPaperShading
            (pullback.restrictedCover.fullFiberSubfamily parent)
            pullback.selectedFineShading).mass =
            sourceWeight (support.packedIndex parent) :=
          hFiberMass
        _ = externalWeight (regularized.selected.embedding parent) :=
          hPointWeight.symm
        _ ≤ 2 * regularized.selectedWeightLevel :=
          hBand.2
  exact
    ⟨{
      sourceWeight := sourceWeight
      sourceWeight_eq := fun _ => rfl
      externalWeight := externalWeight
      externalWeight_eq := rfl
      regularized := regularized
      support := support
      pullback := pullback
      selected_essentially_distinct := hSelectedDistinct
      selected_cwa_nearby := hSelectedCWA
      selected_top_level_convex_wolff := hTopLevel
      selectedFine_mass_eq := hSelectedWeight
      retained_mass := hRetained
      selectedFiberMassLevel := regularized.selectedWeightLevel
      selectedFiberMassLevel_pos :=
        regularized.selectedWeightLevel_pos
      selectedFiberMassLevel_ne_top :=
        regularized.selectedWeightLevel_ne_top
      selected_fiber_mass_band := hFiberBand
    }⟩

end Kakeya.Assouad

end
