import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalBalancedCoverV2Statements

/-!
# Final coarse/fiber multiplicity comparison data

Package the two dyadic multiplicity bands of the final balanced cover and the
global lower bound for their product.  This is the literal formal version of
the `mu_fine mu_coarse` comparison in the paper.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperFinalMultiplicityComparisonData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (coarseShading : WZ1PaperTubeShading coarse)
    (balanced :
      WZ1PaperBalancedCoverData
        cover.toWZ1PaperTubeCover fineShading coarseShading)
    (coarseLevel fiberLevel : ℕ)
    (massLower volumeUpper : ENNReal) where
  coarseCap : ENNReal
  coarseCap_eq :
    coarseCap = (2 ^ (coarseLevel + 1) : ENNReal)
  fiberCap : ENNReal
  fiberCap_eq :
    fiberCap = (2 ^ (fiberLevel + 1) : ENNReal)
  coarse_band :
    ∀ point ∈ coarseShading.union,
      (2 ^ coarseLevel : ENNReal) ≤
          (coarseShading.pointMultiplicity point : ENNReal) ∧
        (coarseShading.pointMultiplicity point : ENNReal) <
          coarseCap
  fiber_band :
    ∀ parent point,
      point ∈
          (restrictPaperShading
            (cover.fullFiberSubfamily parent)
            fineShading).union →
        (2 ^ fiberLevel : ENNReal) ≤
            ((restrictPaperShading
              (cover.fullFiberSubfamily parent)
              fineShading).pointMultiplicity point : ENNReal) ∧
          ((restrictPaperShading
            (cover.fullFiberSubfamily parent)
            fineShading).pointMultiplicity point : ENNReal) <
            fiberCap
  mass_lower : massLower ≤ fineShading.mass
  volume_upper :
    MeasureTheory.volume fineShading.union ≤ volumeUpper
  product_lower :
    massLower ≤
      (coarseCap * fiberCap) * volumeUpper

def WZ2PaperFinalMultiplicityComparisonStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ (cover : WZ2PaperPartitioningCover fine coarse),
          ∀ (fineShading : WZ1PaperTubeShading fine),
            ∀ (coarseShading : WZ1PaperTubeShading coarse),
              ∀ (balanced :
                  WZ1PaperBalancedCoverData
                    cover.toWZ1PaperTubeCover
                    fineShading coarseShading),
                ∀ (coarseLevel fiberLevel : ℕ),
                  (∀ point ∈ coarseShading.union,
                    (2 ^ coarseLevel : ENNReal) ≤
                        (coarseShading.pointMultiplicity point : ENNReal) ∧
                      (coarseShading.pointMultiplicity point : ENNReal) <
                        (2 ^ (coarseLevel + 1) : ENNReal)) →
                  (∀ parent point,
                    point ∈
                        (restrictPaperShading
                          (cover.fullFiberSubfamily parent)
                          fineShading).union →
                      (2 ^ fiberLevel : ENNReal) ≤
                          ((restrictPaperShading
                            (cover.fullFiberSubfamily parent)
                            fineShading).pointMultiplicity point : ENNReal) ∧
                        ((restrictPaperShading
                          (cover.fullFiberSubfamily parent)
                          fineShading).pointMultiplicity point : ENNReal) <
                          (2 ^ (fiberLevel + 1) : ENNReal)) →
                  ∀ (massLower volumeUpper : ENNReal),
                    massLower ≤ fineShading.mass →
                    MeasureTheory.volume fineShading.union ≤ volumeUpper →
                    Nonempty
                      (WZ2PaperFinalMultiplicityComparisonData
                        cover fineShading coarseShading balanced
                        coarseLevel fiberLevel massLower volumeUpper)

end Kakeya.Assouad

end
