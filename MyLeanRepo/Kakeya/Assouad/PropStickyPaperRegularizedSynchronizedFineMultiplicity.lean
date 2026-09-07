import MyLeanRepo.Kakeya.Assouad.PropStickyPaperSynchronizedFineMultiplicity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPostDeletionFiberMassRegularization

/-!
# Nearby-CWA regularization after synchronizing `mu_fine`

First synchronize the fine multiplicity level across complete coarse fibers.
Then regularize those coarse parents by their complete-fiber shaded masses.
Because the second step pulls back complete fibers, both the common density
floor and the common pointwise `mu_fine` band are preserved exactly.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperRegularizedSynchronizedFineMultiplicityData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {sourceDensity : ENNReal}
    (synchronized :
      WZ2PaperSynchronizedFineMultiplicityData
        cover fineShading coarseShading sourceDensity)
    (ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal)
    (levelCount : ℕ) where
  joint :
    WZ2PaperPostDeletionFiberMassRegularizationData
      synchronized.selectedCoarse
      synchronized.pullback.restrictedCover
      synchronized.pullback.selectedFineShading
      synchronized.pullback.selectedCoarseShading
      ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant levelCount
  fiber_mass_lower :
    ∀ parent,
      synchronized.selectedDensity *
            (joint.pullback.restrictedCover.fullFiberSubfamily
              parent).family.enncard *
            Kakeya.realRpowENN delta 2 ≤
        (restrictPaperShading
          (joint.pullback.restrictedCover.fullFiberSubfamily parent)
          joint.pullback.selectedFineShading).mass
  fiber_multiplicity_band :
    ∀ parent point,
      point ∈
          (restrictPaperShading
            (joint.pullback.restrictedCover.fullFiberSubfamily parent)
            joint.pullback.selectedFineShading).union →
        (2 ^ synchronized.commonLevel.val : ENNReal) ≤
            ((restrictPaperShading
              (joint.pullback.restrictedCover.fullFiberSubfamily parent)
              joint.pullback.selectedFineShading).pointMultiplicity point :
                ENNReal) ∧
          ((restrictPaperShading
            (joint.pullback.restrictedCover.fullFiberSubfamily parent)
            joint.pullback.selectedFineShading).pointMultiplicity point :
              ENNReal) <
            (2 ^ (synchronized.commonLevel.val + 1) : ENNReal)

theorem wz2_paper_regularized_synchronized_fine_multiplicity
    {delta rho : ℝ}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {sourceDensity : ENNReal}
    (synchronized :
      WZ2PaperSynchronizedFineMultiplicityData
        cover fineShading coarseShading sourceDensity)
    (hCoarseNonempty : coarse.Nonempty)
    (hCoarseLine : WZ1PaperIsLineClass coarse)
    (hCoarseDistinct : WZ1PaperIsEssentiallyDistinct coarse)
    (ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal)
    (hNormZero : normalizationWeight ≠ 0)
    (hNormTop : normalizationWeight ≠ ⊤)
    (hWeightTop : weightUpper ≠ ⊤)
    (hTotalLower :
      normalizationWeight * coarse.enncard ≤
        synchronized.pullback.selectedFineShading.mass)
    (hWeightUpper :
      ∀ parent,
        (restrictPaperShading
          (synchronized.pullback.restrictedCover.fullFiberSubfamily
            parent)
          synchronized.pullback.selectedFineShading).mass ≤
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
      WZ2PaperCWACoversAtNearbyScales coarse ambientConstant)
    (hPackedTop :
      WZ2PaperConvexWolffBound
        synchronized.selectedCoarse.family packedConstant)
    (hAbsorb :
      let degreeConstant :=
        16 * ((levelCount + 1 : ℕ) : ENNReal) *
          (Nat.log 2 (2 * coarse.card) + 1 : ENNReal) ^
            (levelCount + 1)
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * coarse.card) + 1 : ENNReal) ^
            (levelCount + 2)
      max degreeConstant
          ((normalizationWeight⁻¹ *
              (ambientConstant *
                (regularizationLoss * weightUpper) *
                degreeConstant)) *
            ambientConstant) ≤
        outputConstant) :
    Nonempty
      (WZ2PaperRegularizedSynchronizedFineMultiplicityData
        synchronized ambientConstant outputConstant normalizationWeight
        weightUpper packedConstant levelCount) := by
  rcases
      wz2_paper_post_deletion_fiber_mass_regularization
        hrho hrhoOne synchronized.selectedCoarse
        synchronized.pullback.restrictedCover
        synchronized.pullback.selectedFineShading
        synchronized.pullback.selectedCoarseShading
        hCoarseNonempty hCoarseLine hCoarseDistinct
        synchronized.pullback.selectedFine_cubical
        synchronized.pullback.selectedCoarse_cubical
        synchronized.pullback.point_compatibility
        ambientConstant outputConstant normalizationWeight weightUpper
        packedConstant hNormZero hNormTop hWeightTop
        hTotalLower hWeightUpper levelCount hAmbient hAmbientTop
        hPower hOutput hNearby hPackedTop hAbsorb
    with ⟨joint⟩
  have hFiberMass :
      ∀ parent,
        synchronized.selectedDensity *
              (joint.pullback.restrictedCover.fullFiberSubfamily
                parent).family.enncard *
              Kakeya.realRpowENN delta 2 ≤
          (restrictPaperShading
            (joint.pullback.restrictedCover.fullFiberSubfamily parent)
            joint.pullback.selectedFineShading).mass := by
    intro parent
    let packedParent := joint.support.packedIndex parent
    let reindex :
        WZ2PaperCompleteFiberReindexData
          synchronized.pullback.restrictedCover
          joint.pullback.selectedFine
          joint.pullback.restrictedCover
          parent packedParent
          (joint.pullback.full_fiber_complete parent) :=
      Classical.choice <|
        wz2_paper_complete_fiber_reindex
          synchronized.pullback.restrictedCover
          joint.pullback.selectedFine
          joint.pullback.restrictedCover
          parent packedParent
          (joint.pullback.full_fiber_complete parent)
    have hCardNat :
        (joint.pullback.restrictedCover.fullFiberSubfamily
            parent).family.card =
          (synchronized.pullback.restrictedCover.fullFiberSubfamily
            packedParent).family.card := by
      simpa only [Fintype.card_fin] using
        Fintype.card_congr
          (Equiv.ofBijective reindex.localIndex
            reindex.localIndex_bijective)
    have hCard :
        (joint.pullback.restrictedCover.fullFiberSubfamily
            parent).family.enncard =
          (synchronized.pullback.restrictedCover.fullFiberSubfamily
            packedParent).family.enncard := by
      change
        ((joint.pullback.restrictedCover.fullFiberSubfamily
            parent).family.card : ENNReal) =
          ((synchronized.pullback.restrictedCover.fullFiberSubfamily
            packedParent).family.card : ENNReal)
      exact congrArg (fun value : ℕ => (value : ENNReal)) hCardNat
    calc
      synchronized.selectedDensity *
            (joint.pullback.restrictedCover.fullFiberSubfamily
              parent).family.enncard *
            Kakeya.realRpowENN delta 2 =
          synchronized.selectedDensity *
            (synchronized.pullback.restrictedCover.fullFiberSubfamily
              packedParent).family.enncard *
            Kakeya.realRpowENN delta 2 := by
        rw [hCard]
      _ ≤
          (restrictPaperShading
            (synchronized.pullback.restrictedCover.fullFiberSubfamily
              packedParent)
            synchronized.pullback.selectedFineShading).mass :=
        synchronized.fiber_mass_lower packedParent
      _ =
          (restrictPaperShading
            (joint.pullback.restrictedCover.fullFiberSubfamily parent)
            joint.pullback.selectedFineShading).mass :=
        (joint.pullback.full_fiber_mass_eq parent).symm
  have hFiberBand :
      ∀ parent point,
        point ∈
            (restrictPaperShading
              (joint.pullback.restrictedCover.fullFiberSubfamily parent)
              joint.pullback.selectedFineShading).union →
          (2 ^ synchronized.commonLevel.val : ENNReal) ≤
              ((restrictPaperShading
                (joint.pullback.restrictedCover.fullFiberSubfamily parent)
                joint.pullback.selectedFineShading).pointMultiplicity point :
                  ENNReal) ∧
            ((restrictPaperShading
              (joint.pullback.restrictedCover.fullFiberSubfamily parent)
              joint.pullback.selectedFineShading).pointMultiplicity point :
                ENNReal) <
              (2 ^ (synchronized.commonLevel.val + 1) : ENNReal) := by
    intro parent point hpoint
    let packedParent := joint.support.packedIndex parent
    have hPoint :
        point ∈
          (restrictPaperShading
            (synchronized.pullback.restrictedCover.fullFiberSubfamily
              packedParent)
            synchronized.pullback.selectedFineShading).union := by
      rcases hpoint with ⟨index, hindex⟩
      let reindex :
          WZ2PaperCompleteFiberReindexData
            synchronized.pullback.restrictedCover
            joint.pullback.selectedFine
            joint.pullback.restrictedCover
            parent packedParent
            (joint.pullback.full_fiber_complete parent) :=
        Classical.choice <|
          wz2_paper_complete_fiber_reindex
            synchronized.pullback.restrictedCover
            joint.pullback.selectedFine
            joint.pullback.restrictedCover
            parent packedParent
            (joint.pullback.full_fiber_complete parent)
      refine ⟨reindex.localIndex index, ?_⟩
      rw [joint.pullback.selectedFineShading_eq] at hindex
      change
        point ∈ synchronized.pullback.selectedFineShading.carrier
          (joint.pullback.selectedFine.embedding
            ((joint.pullback.restrictedCover.fullFiberSubfamily
              parent).embedding index)) at hindex
      rw [reindex.ambient_eq index] at hindex
      exact hindex
    have hBand :=
      synchronized.fiber_multiplicity_band
        packedParent point hPoint
    have hMultiplicity :=
      joint.pullback.full_fiber_pointMultiplicity_eq parent point
    rw [hMultiplicity]
    exact hBand
  exact
    ⟨{
      joint := joint
      fiber_mass_lower := hFiberMass
      fiber_multiplicity_band := hFiberBand
    }⟩

end Kakeya.Assouad

end
