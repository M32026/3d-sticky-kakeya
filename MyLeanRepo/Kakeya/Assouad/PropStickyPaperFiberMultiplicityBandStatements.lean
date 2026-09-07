import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGlobalMultiplicityHelpers

/-!
# One common multiplicity band in every complete parent fiber

WZ Proposition 3.2 first refines the fine shading so that there is one number
`mu_fine` with the same factor-two point-multiplicity band in every retained
coarse parent fiber.

For each level, restrict every fine tube by the multiplicity band of its own
complete parent fiber.  Summing over all levels partitions the total shaded
mass, because the geometric parent map partitions the fine tube indices.
Select one common level retaining a logarithmic fraction of the total mass.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

def wz2PaperFiberMultiplicityBand
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (level : ℕ)
    (source : Fin fine.card) : Set Point3 :=
  wz1PaperDyadicMultiplicityBand
    (restrictPaperShading
      (cover.fullFiberSubfamily (cover.parent source))
      shading)
    level

structure WZ2PaperFiberMultiplicityBandData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine) where
  level : ℕ
  refined : WZ1PaperTubeShading fine
  refined_carrier_eq :
    ∀ source,
      refined.carrier source =
        shading.carrier source ∩
          wz2PaperFiberMultiplicityBand
            cover shading level source
  refined_subshading :
    ∀ source,
      refined.carrier source ⊆ shading.carrier source
  refined_cubical :
    WZ1PaperIsCubicalShading refined
  retained_mass :
    shading.mass /
          ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal) ≤
      refined.mass
  fiber_pointMultiplicity_eq :
    ∀ parent point,
      point ∈
          (restrictPaperShading
            (cover.fullFiberSubfamily parent)
            refined).union →
        (restrictPaperShading
            (cover.fullFiberSubfamily parent)
            refined).pointMultiplicity point =
          (restrictPaperShading
            (cover.fullFiberSubfamily parent)
            shading).pointMultiplicity point
  fiber_multiplicity_band :
    ∀ parent point,
      point ∈
          (restrictPaperShading
            (cover.fullFiberSubfamily parent)
            refined).union →
        (2 ^ level : ENNReal) ≤
            ((restrictPaperShading
              (cover.fullFiberSubfamily parent)
              refined).pointMultiplicity point : ENNReal) ∧
          ((restrictPaperShading
              (cover.fullFiberSubfamily parent)
              refined).pointMultiplicity point : ENNReal) <
            (2 ^ (level + 1) : ENNReal)

def WZ2PaperFiberMultiplicityBandStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ (cover : WZ2PaperPartitioningCover fine coarse),
          ∀ (shading : WZ1PaperTubeShading fine),
            WZ1PaperIsCubicalShading shading →
              Nonempty
                (WZ2PaperFiberMultiplicityBandData
                  cover shading)

end Kakeya.Assouad

end
