import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingGlobalSlabADStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingLocalADStatements

/-!
# Normalized grain packages after the Proposition 9 similarity

The global- and local-AD transport leaves prove only covering estimates.
This module freezes the two independent assembly boundaries that turn those
estimates into complete `1`-Lipschitz grain packages while retaining the exact
source slope and plane-normal provenance.

Neither boundary constructs or assumes a target `UniformTubeStructure`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The inverse of the positive isotropic similarity. -/
def wz1IsotropicRescalingInverse
    (center : Point3) (scale : ℝ) (q : Point3) : Point3 :=
  center + scale⁻¹ • q

/--
Complete normalized local-grain output on a cleaned isotropic target.

For an isotropic similarity the inverse-transpose normal is a positive scalar
multiple of the source unit normal.  Normalization therefore recovers the
source normal exactly.
-/
structure WZ1MildRescalingNormalizedLocalData
    {sourceDelta sigma scale : ℝ}
    {sourceFamily :
      Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading :
      Kakeya.Streamlined.TubeShading sourceFamily}
    {C : ENNReal}
    (sourceLocal :
      WZ1LocalGrainData sourceShading sigma C)
    (center : Point3)
    {targetFamily :
      Kakeya.Streamlined.TubeFamily (scale * sourceDelta)}
    (targetShading :
      Kakeya.Streamlined.TubeShading targetFamily) where
  localGrains :
    WZ1LocalGrainData targetShading sigma C
  lipschitzConstant_eq :
    localGrains.lipschitzConstant = 1
  planeMap_eq :
    localGrains.planeMap =
      fun q =>
        sourceLocal.planeMap
          (wz1IsotropicRescalingInverse center scale q)
  planeMap_on_image :
    ∀ p ∈ sourceShading.union,
      localGrains.planeMap
          (wz1IsotropicRescalingMap center scale p) =
        sourceLocal.planeMap p
  normalized_normal_on_image :
    ∀ p ∈ sourceShading.union,
      localGrains.planeMap
          (wz1IsotropicRescalingMap center scale p) =
        wz1NormalizeNormal
          (wz1MildRescalingNormal
            (point3 scale scale scale)
            (sourceLocal.planeMap p))

/--
Assemble the complete `1`-Lipschitz local-grain package.

The target carrier of each cleaned child must retain its actual source parent.
This supplies both incidence and the source witness consumed by the closed
local-AD transport theorem.
-/
def WZ1MildRescalingNormalizedLocalGrainStatement : Prop :=
  WZ1MildRescalingLocalADTransportStatement →
    ∀ {sourceDelta sigma scale : ℝ},
      0 < sourceDelta →
      1 ≤ scale →
      scale * sourceDelta ≤ 1 →
        ∀ {sourceFamily :
            Kakeya.Streamlined.TubeFamily sourceDelta},
          ∀ {sourceShading :
              Kakeya.Streamlined.TubeShading sourceFamily},
            ∀ {C : ENNReal},
              ∀ sourceLocal :
                  WZ1LocalGrainData sourceShading sigma C,
                (sourceLocal.lipschitzConstant : ℝ) ≤ scale →
                  ∀ center : Point3,
                    ∀ {targetFamily :
                        Kakeya.Streamlined.TubeFamily
                          (scale * sourceDelta)},
                      ∀ targetShading :
                          Kakeya.Streamlined.TubeShading targetFamily,
                        ∀ sourceParent :
                            Fin targetFamily.card →
                              Fin sourceFamily.card,
                          (∀ j,
                            (targetFamily.tube j).direction =
                              (sourceFamily.tube
                                (sourceParent j)).direction) →
                          (∀ j,
                            targetShading.carrier j ⊆
                              wz1IsotropicRescalingMap
                                  center scale ''
                                sourceShading.carrier
                                  (sourceParent j)) →
                          targetShading.union ⊆
                            wz1CoordinateWindow →
                            Nonempty
                              (WZ1MildRescalingNormalizedLocalData
                                sourceLocal center targetShading)

/--
Complete normalized global-grain output on a cleaned isotropic target.
-/
structure WZ1MildRescalingNormalizedGlobalData
    {sourceDelta sigma scale : ℝ}
    {sourceFamily :
      Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading :
      Kakeya.Streamlined.TubeShading sourceFamily}
    {C : ENNReal}
    (sourceGlobal :
      WZ1LipschitzGlobalGrainData sourceShading sigma C)
    (center : Point3)
    {targetFamily :
      Kakeya.Streamlined.TubeFamily (scale * sourceDelta)}
    (targetShading :
      Kakeya.Streamlined.TubeShading targetFamily)
    (K : NNReal) where
  globalGrains :
    WZ1LipschitzGlobalGrainData targetShading sigma
      (60 *
        max (1 : ENNReal)
          ((K : ENNReal) *
            (sourceGlobal.lipschitzConstant : ENNReal)) *
        C)
  lipschitzConstant_eq :
    globalGrains.lipschitzConstant = 1
  slope_eq :
    globalGrains.slope =
      wz1MildRescaledSlope
        center (point3 scale scale scale)
        sourceGlobal.slope
  slope_on_image :
    ∀ p ∈ sourceShading.union,
      globalGrains.slope
          ((wz1IsotropicRescalingMap center scale p) 2) =
        sourceGlobal.slope (p 2)
  slope_bound :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |globalGrains.slope z| ≤ 3

/--
Assemble the complete `1`-Lipschitz global-grain package.

The horizontal-center budget is explicit because the closed slab-AD transport
must pay for the height-dependent affine translation.
-/
def WZ1MildRescalingNormalizedGlobalGrainStatement : Prop :=
  WZ1MildRescalingGlobalSlabADTransportStatement →
    ∀ {sourceDelta sigma scale : ℝ},
      0 < sourceDelta →
      1 ≤ scale →
      scale * sourceDelta ≤ 1 →
        ∀ {sourceFamily :
            Kakeya.Streamlined.TubeFamily sourceDelta},
          ∀ {sourceShading :
              Kakeya.Streamlined.TubeShading sourceFamily},
            ∀ {C : ENNReal},
              ∀ sourceGlobal :
                  WZ1LipschitzGlobalGrainData
                    sourceShading sigma C,
                (sourceGlobal.lipschitzConstant : ℝ) ≤ scale →
                sourceShading.union ⊆
                  wz1MildRescalingSourceWindow →
                (∀ z ∈ Set.Icc (-1 : ℝ) 1,
                  |sourceGlobal.slope z| ≤ 3) →
                  ∀ center : Point3,
                    ∀ K : NNReal,
                      |center 1| ≤ (K : ℝ) →
                      scale *
                          max sourceDelta
                            ((K : ℝ) *
                              (sourceGlobal.lipschitzConstant : ℝ) *
                              sourceDelta) ≤
                        1 →
                        ∀ {targetFamily :
                            Kakeya.Streamlined.TubeFamily
                              (scale * sourceDelta)},
                          ∀ targetShading :
                              Kakeya.Streamlined.TubeShading
                                targetFamily,
                            targetShading.union ⊆
                              wz1IsotropicRescalingMap
                                  center scale ''
                                sourceShading.union →
                            (∀ z ∈ Set.Icc (-1 : ℝ) 1,
                              globalGrainProjection
                                  (wz1MildRescaledSlope
                                    center
                                      (point3 scale scale scale)
                                    sourceGlobal.slope)
                                  (globalGrainSlab
                                    targetShading.union z
                                    (scale * sourceDelta)) ⊆
                                Set.Icc (-4 : ℝ) 4) →
                              Nonempty
                                (WZ1MildRescalingNormalizedGlobalData
                                  sourceGlobal center targetShading K)

/--
Transfer the source vertical-normal bound to a normalized target local-grain
package.

The isotropic inverse-transpose normalization recovers the source unit normal
exactly on the actual source image, so no additional distortion factor is
present.
-/
def WZ1MildRescalingNormalizedLocalVerticalBoundStatement : Prop :=
  ∀ {sourceDelta sigma scale : ℝ},
    0 < scale →
    ∀ {sourceFamily :
        Kakeya.Streamlined.TubeFamily sourceDelta},
      ∀ {sourceShading :
          Kakeya.Streamlined.TubeShading sourceFamily},
        ∀ {C : ENNReal},
          ∀ sourceLocal :
              WZ1LocalGrainData sourceShading sigma C,
            (∀ p ∈ sourceShading.union,
              |sourceLocal.planeMap p (2 : Fin 3)| ≤ 1 / 2) →
              ∀ center : Point3,
                ∀ {targetFamily :
                    Kakeya.Streamlined.TubeFamily
                      (scale * sourceDelta)},
                  ∀ targetShading :
                      Kakeya.Streamlined.TubeShading targetFamily,
                    ∀ normalized :
                        WZ1MildRescalingNormalizedLocalData
                          sourceLocal center targetShading,
                      targetShading.union ⊆
                        wz1IsotropicRescalingMap center scale ''
                          sourceShading.union →
                        ∀ q ∈ targetShading.union,
                          |normalized.localGrains.planeMap q
                              (2 : Fin 3)| ≤ 1 / 2

end Kakeya.Assouad
