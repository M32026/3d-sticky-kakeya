import MyLeanRepo.Kakeya.Assouad.WZ1.Statements

/-!
# Dependent scale-changed Lipschitz plane maps

WZ1 Proposition 9 applies the planiness machinery twice.  The second
application starts from the particular unit-rescaled extremal fiber selected
in Step 1, and changes from its fine radius to the already fixed global-grain
scale.  An existential theorem producing some unrelated configuration cannot
serve this purpose.

This module freezes the missing dependent boundary after Proposition 5 has
already supplied a balanced cover.  The source weak plane map is supplied on
the actual fine shading, and the output retains the same balanced cover, a
coarse subshading of its induced shading, and the Lipschitz plane map on that
same coarse family.
-/

noncomputable section

namespace Kakeya.Assouad

/--
The WZ1 Lemma 12--15 output at one prescribed coarse scale.
-/
structure WZ1ScaleChangedLipschitzPlaneMapData
    {fineDelta sigma balancedLoss outputLoss sourceIncidenceScale : ℝ}
    {F : Kakeya.Streamlined.TubeFamily fineDelta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (coarseScale : Kakeya.Streamlined.AdmissibleScale fineDelta)
    (balanced :
    WZ1BalancedCoverData
      (sigma := sigma) (epsilon := balancedLoss)
      U Y coarseScale)
    (sourcePlaneMap :
      WZ1WeakPlaneMapData Y sourceIncidenceScale) where
  shading :
    Kakeya.Streamlined.TubeShading
      (U.coarse coarseScale)
  subshading :
    IsSubshading shading balanced.coarseShading
  induced_subshading :
    (U.cover coarseScale).toFactoring.IsInducedSubshading
      balanced.refined shading coarseScale.1
  extremal :
    WZ1ExtremalPair sigma outputLoss
      (U.coarse coarseScale)
      balanced.coarseUniform shading
  planeMap : WZ1PlaneMapData shading
  planeMap_lipschitz_bound :
    (planeMap.lipschitzConstant : ENNReal) ≤
      Kakeya.realRpowENN coarseScale.1 (-outputLoss)
  planeMap_close_to_source :
    ∀ p ∈ shading.union,
      dist (planeMap.planeMap p)
        (sourcePlaneMap.planeMap
          (balanced.representative (balanced.cell p))) ≤
            coarseScale.1 / 2

/--
Construct the scale-changed Lipschitz plane map from a supplied Proposition 5
cover and a weak plane map on the same fine shading.

The balanced-cover loss controls the Proposition 5 scale window.  It is
strictly smaller than the final Lipschitz loss, which absorbs the finite
cell-selection and iteration losses.  The source weak plane map has incidence
no larger than the actual coarse scale; this is the precise input used by WZ1
Lemma 12.  The conclusion returns a refinement of the induced coarse shading,
so downstream arguments retain the exact source provenance.
-/
def WZ1ScaleChangedLipschitzPlaneMapConclusion : Prop :=
  ∀ sigma outputLoss : ℝ,
    0 < sigma → sigma < 1 → 0 < outputLoss →
    HasCriticalVolumeFloor sigma →
      ∃ balancedLoss delta₀ : ℝ,
        0 < balancedLoss ∧
        balancedLoss < outputLoss ∧
        balancedLoss < sigma / 2 ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ fineDelta : ℝ,
          0 < fineDelta → fineDelta ≤ delta₀ →
          ∀ F : Kakeya.Streamlined.TubeFamily fineDelta,
            ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
              ∀ Y : Kakeya.Streamlined.TubeShading F,
                ∀ coarseScale :
                    Kakeya.Streamlined.AdmissibleScale fineDelta,
                  Real.rpow fineDelta (1 - balancedLoss) ≤
                      coarseScale.1 →
                  coarseScale.1 ≤
                      Real.rpow fineDelta balancedLoss →
                    ∀ balanced :
                        WZ1BalancedCoverData
                          (sigma := sigma) (epsilon := balancedLoss)
                          U Y coarseScale,
                      ∀ {sourceIncidenceScale : ℝ},
                        ∀ sourcePlaneMap :
                            WZ1WeakPlaneMapData Y sourceIncidenceScale,
                          sourceIncidenceScale ≤ coarseScale.1 →
                            Nonempty
                              (WZ1ScaleChangedLipschitzPlaneMapData
                                (sigma := sigma)
                                (balancedLoss := balancedLoss)
                                (outputLoss := outputLoss)
                                U Y coarseScale balanced sourcePlaneMap)

/--
Assemble the dependent second scale change from the direct WZ1 Lemma 15
conclusion, which records that its output map is the supplied input map.  The
coarse-plane and balanced-cell-coloring constructions are closed repository
infrastructure used by the proof target.
-/
def WZ1ScaleChangedLipschitzPlaneMapStatement : Prop :=
  WZ1LipschitzPlaneMapConclusion →
    WZ1ScaleChangedLipschitzPlaneMapConclusion

end Kakeya.Assouad
