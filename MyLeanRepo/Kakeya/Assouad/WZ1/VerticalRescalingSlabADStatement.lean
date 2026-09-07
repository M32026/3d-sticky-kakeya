import MyLeanRepo.Kakeya.Assouad.WZ1.VerticalRescalingADStatement

/-!
# Slab global-AD transport under vertical rescaling

Paper-faithful companion to the completed exact-slice theorem
`wz1_vertical_rescaling_ad`.

The target slab radius is `delta / M^2`.  Under the vertical coordinate
change it pulls back to radius `h * delta / M^2`, which is at most the source
radius `delta` when `h ≤ 1 ≤ M`.  The height-dependent global-grain coordinate
is simultaneously dilated by `M⁻²`.
-/

namespace Kakeya.Assouad

def WZ1VerticalRescalingSlabADStatement : Prop :=
  ∀ (g : SlopeFunction) (c h M delta sigma : ℝ) (C : ENNReal),
    0 < h →
    h ≤ 1 →
    1 ≤ M →
    0 < delta →
    delta ≤ 1 →
    0 < sigma →
    sigma < 1 →
    (∀ t ∈ Set.Icc (-1 : ℝ) 1,
      c + h * t ∈ Set.Icc (-1 : ℝ) 1) →
    ∀ E : Set Point3,
      (∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (globalGrainProjection g
            (globalGrainSlab E z delta))
          delta (1 - sigma) C) →
        let delta' : ℝ := delta / M ^ 2
        (∀ t ∈ Set.Icc (-1 : ℝ) 1,
          globalGrainProjection
              (wz1VerticalRescaledSlope g c h M)
              (globalGrainSlab
                (wz1VerticalRescalingMap c h M '' E)
                t delta') ⊆
            (fun u : ℝ => u / M ^ 2) ''
              globalGrainProjection g
                (globalGrainSlab E (c + h * t) delta)) ∧
          ∀ t ∈ Set.Icc (-1 : ℝ) 1,
            IsADSet1
              (globalGrainProjection
                (wz1VerticalRescaledSlope g c h M)
                (globalGrainSlab
                  (wz1VerticalRescalingMap c h M '' E)
                  t delta'))
              delta' (1 - sigma) (10 * C)

end Kakeya.Assouad
