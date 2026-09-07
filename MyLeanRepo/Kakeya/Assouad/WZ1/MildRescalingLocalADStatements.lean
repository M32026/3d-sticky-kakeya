import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingStatements

/-!
# Local-grain AD transport through the Proposition 9 similarity

At target scale `rho`, the inverse isotropic image of a
`sqrt rho` target ball has radius `sqrt rho / scale`, which is no larger
than the source local-grain radius `sqrt (rho / scale)`.

The target scalar projection is an affine image with slope `scale` of the
source scalar projection.  This leaf proves only the local AD conclusion; the
target plane map's measurability, unit norm, Lipschitz bound, and incidence
are separate obligations.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Transport every-scale local AD control through one isotropic similarity.

Every target point and its target normal retain an actual source witness.
This prevents replacing the source plane-map value by an unrelated normal.
-/
def WZ1MildRescalingLocalADTransportStatement : Prop :=
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
              ∀ center : Point3,
                ∀ {targetFamily :
                    Kakeya.Streamlined.TubeFamily
                      (scale * sourceDelta)},
                  ∀ targetShading :
                      Kakeya.Streamlined.TubeShading targetFamily,
                    ∀ targetPlaneMap : Point3 → Point3,
                      targetShading.union ⊆
                        wz1IsotropicRescalingMap center scale ''
                          sourceShading.union →
                      targetShading.union ⊆
                        wz1CoordinateWindow →
                      (∀ q ∈ targetShading.union,
                        ∃ p ∈ sourceShading.union,
                          q =
                              wz1IsotropicRescalingMap
                                center scale p ∧
                            targetPlaneMap q =
                              sourceLocal.planeMap p) →
                        ∀ rho : ℝ,
                          scale * sourceDelta ≤ rho →
                          rho ≤ 1 →
                          ∀ q ∈ targetShading.union,
                            IsADSet1
                              (scalarProjection
                                (targetPlaneMap q)
                                (targetShading.union ∩
                                  Metric.closedBall q
                                    (Real.sqrt rho)))
                              rho (1 - sigma) C

end Kakeya.Assouad
