import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains

/-!
# Relaxed local grain data with arbitrary Lipschitz constant

This module defines `PureWZ2RelaxedLocalGrainData`, a version of
`PureWZ2LocalGrainData` where the plane map has `LipschitzWith L` for an
arbitrary `L : NNReal` (rather than `LipschitzWith 1`).

This is used in the mild rescaling pipeline:
1. Build pre-normalized grains with Lip L (e.g., L = 6)
2. Rescale isotropically to normalize to Lip 1

## Whiteprint node

`PureWZ2/Grains/RelaxedLocalGrainData`
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/--
Relaxed local grain data with arbitrary Lipschitz constant `L`.

Like `PureWZ2LocalGrainData` but the plane map has `LipschitzWith L`
instead of `LipschitzWith 1`. The AD bound is unchanged.

When `L = 1`, use `to_strict` to recover `PureWZ2LocalGrainData`.
-/
structure PureWZ2RelaxedLocalGrainData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (sigma : ℝ) (C : ENNReal) (L : NNReal) where
  planeMap : {point : Point3 // point ∈ shading.union} → Point3
  planeMap_lipschitz : LipschitzWith L planeMap
  planeMap_unit : ∀ point, ‖planeMap point‖ = 1
  planeMap_incidence :
    ∀ (index : Fin family.card) (point : Point3),
      ∀ (hpoint : point ∈ shading.carrier index),
        |inner ℝ (family.tube index).direction
            (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ delta
  local_ad :
    ∀ (rho : ℝ), delta ≤ rho → rho ≤ 1 →
      ∀ (point : {point : Point3 // point ∈ shading.union}),
        PureWZ2PaperADSet1
          (scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)))
          rho (1 - sigma) C

/-- Convert relaxed data with L=1 to strict `PureWZ2LocalGrainData`. -/
def PureWZ2RelaxedLocalGrainData.to_strict
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family} {sigma : ℝ} {C : ENNReal}
    (data : PureWZ2RelaxedLocalGrainData shading sigma C 1) :
    PureWZ2LocalGrainData shading sigma C :=
  { planeMap := data.planeMap
  , planeMap_lipschitz := data.planeMap_lipschitz
  , planeMap_unit := data.planeMap_unit
  , planeMap_incidence := data.planeMap_incidence
  , local_ad := data.local_ad }

end Kakeya.Assouad

end
