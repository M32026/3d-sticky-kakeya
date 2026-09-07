import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains

/-!
# Pre-grain data structure for PureWZ2

Extracts `PureWZ2PreGrainData` to its own module to avoid circular imports
between `Dilate.lean` and `ADTransport.lean`.

Pre-grain data at scale `delta'` with WZ1-standard relaxed bounds.
This is the input to the Route C dilation. The incidence bound is `≤ 6 * delta'`
and the Lipschitz constant is `≤ 6`; both become tight after dilation by 6.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/--
Pre-grain data at scale `delta'` with WZ1-standard relaxed bounds.

This is the input to the Route C dilation. The incidence bound is `≤ 6 * delta'`
and the Lipschitz constant is `≤ 6`; both become tight after dilation by 6.
-/
structure PureWZ2PreGrainData
    {delta' : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta'}
    (shading : WZ1PaperTubeShading family)
    (sigma loss_src : ℝ) where
  planeMap : {point : Point3 // point ∈ shading.union} → Point3
  planeMap_lipschitz : LipschitzWith 6 planeMap
  planeMap_unit : ∀ point, ‖planeMap point‖ = 1
  planeMap_incidence :
    ∀ (index : Fin family.card) (point : Point3),
      ∀ (hpoint : point ∈ shading.carrier index),
        |inner ℝ (family.tube index).direction
            (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ 6 * delta'
  slope : ℝ → ℝ
  slope_lipschitz : LipschitzOnWith 6 slope (Set.Icc (-1 : ℝ) 1)
  local_ad :
    ∀ rho : ℝ, delta' ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ shading.union},
        PureWZ2PaperADSet1
          (scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)))
          rho (1 - sigma) (Kakeya.realRpowENN delta' (-loss_src))
  global_ad :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope z))
          (horizontalSlice shading.union z))
        delta' (1 - sigma) (Kakeya.realRpowENN delta' (-loss_src))

end Kakeya.Assouad

end
