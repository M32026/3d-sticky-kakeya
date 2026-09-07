import MyLeanRepo.Kakeya.Assouad.WZ1.ScaleChangedLipschitzStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.VerticalConeStatements

/-!
# Vertical components of scale-changed plane maps

The source weak plane map is almost orthogonal to every incident fine tube.
If all fine directions lie in a narrow cone about the vertical axis, this
bounds the vertical component of the source normal.  The scale-changed plane
map is close to that source normal at the balanced-cell representative, so
the same bound survives with one additional half-scale error.

This is the quantitative direction estimate used inside the anchored
global-grain transport.  It is stronger and more precise than trying to infer
a plane-normal bound from `IsInVerticalChart`.
-/

namespace Kakeya.Assouad

/--
Narrow fine directions, source incidence, and representative closeness bound
the vertical component of the scale-changed plane map.
-/
def WZ1ScaleChangedPlaneMapVerticalBoundStatement : Prop :=
  ∀ {fineDelta sigma balancedLoss outputLoss sourceIncidenceScale
      aperture : ℝ},
    ∀ {F : Kakeya.Streamlined.TubeFamily fineDelta},
      ∀ {U : Kakeya.Streamlined.UniformTubeStructure F},
        ∀ {Y : Kakeya.Streamlined.TubeShading F},
          ∀ {coarseScale :
              Kakeya.Streamlined.AdmissibleScale fineDelta},
            ∀ (balanced :
                WZ1BalancedCoverData
                  (sigma := sigma) (epsilon := balancedLoss)
                  U Y coarseScale),
              ∀ (sourcePlaneMap :
                  WZ1WeakPlaneMapData Y sourceIncidenceScale),
                ∀ (changed :
                    WZ1ScaleChangedLipschitzPlaneMapData
                      (sigma := sigma)
                      (balancedLoss := balancedLoss)
                      (outputLoss := outputLoss)
                      U Y coarseScale balanced sourcePlaneMap),
                  IsInNarrowVerticalCone F aperture →
                    ∀ p ∈ changed.shading.union,
                      |(changed.planeMap.planeMap p) (2 : Fin 3)| ≤
                        aperture + sourceIncidenceScale +
                          coarseScale.1 / 2

end Kakeya.Assouad
