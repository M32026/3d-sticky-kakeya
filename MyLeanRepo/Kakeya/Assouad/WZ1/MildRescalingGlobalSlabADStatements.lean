import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingPopularBoxStatements

/-!
# Global-slab AD transport through the Proposition 9 similarity

The source slope may have Lipschitz constant `L`, and the selected box center
may have horizontal coordinate bounded by `K`.  Across one source
`sourceDelta` slab, the affine translation term therefore varies at scale
`K * L * sourceDelta`.

The proof must first coarsen the source AD minimum scale to
`max sourceDelta (K * L * sourceDelta)`, apply the isotropic affine-thickening
transport, and then refine back to the target tube radius.  Treating the
translation term as merely `sourceDelta`-small is false when `K * L > 1`.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Transport the global slab AD certificate through one isotropic similarity.

The target shading may be a cleanup subfamily: only containment in the exact
source image is required.  No target UTS is used by this geometric leaf.
-/
def WZ1MildRescalingGlobalSlabADTransportStatement : Prop :=
  ∀ {sourceDelta sigma scale : ℝ},
    0 < sourceDelta →
    1 ≤ scale →
    scale * sourceDelta ≤ 1 →
      ∀ {F : Kakeya.Streamlined.TubeFamily sourceDelta},
        ∀ {Y : Kakeya.Streamlined.TubeShading F},
          ∀ {C : ENNReal},
            ∀ sourceSlope : ℝ → ℝ,
              HasGlobalSlabAD Y sourceSlope sigma C →
              ∀ L K : NNReal,
                LipschitzOnWith L sourceSlope
                  (Set.Icc (-1 : ℝ) 1) →
                Y.union ⊆ wz1MildRescalingSourceWindow →
                ∀ center : Point3,
                  |center 1| ≤ (K : ℝ) →
                  scale *
                      max sourceDelta
                        ((K : ℝ) * (L : ℝ) * sourceDelta) ≤
                    1 →
                  ∀ targetSlope : ℝ → ℝ,
                    (∀ p ∈ Y.union,
                      targetSlope
                          (scale * (p 2 - center 2)) =
                        sourceSlope (p 2)) →
                    ∀ {targetFamily :
                        Kakeya.Streamlined.TubeFamily
                          (scale * sourceDelta)},
                      ∀ targetShading :
                          Kakeya.Streamlined.TubeShading
                            targetFamily,
                        targetShading.union ⊆
                          wz1IsotropicRescalingMap center scale ''
                            Y.union →
                        (∀ z ∈ Set.Icc (-1 : ℝ) 1,
                          globalGrainProjection targetSlope
                              (globalGrainSlab
                                targetShading.union z
                                (scale * sourceDelta)) ⊆
                            Set.Icc (-4 : ℝ) 4) →
                          HasGlobalSlabAD
                            targetShading targetSlope sigma
                            (60 *
                              max (1 : ENNReal)
                                ((K : ENNReal) * (L : ENNReal)) *
                              C)

end Kakeya.Assouad
