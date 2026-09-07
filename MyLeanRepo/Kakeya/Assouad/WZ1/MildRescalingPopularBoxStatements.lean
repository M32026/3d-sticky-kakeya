import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingStatements

/-!
# Mass-popular source box for the Proposition 9 mild rescaling

This is the first independent part of WZ1 Lemma 8.  It chooses one
axis-parallel source box and the isotropic similarity that normalizes that
box.  The output is still a shading of the original source family.

No target tube family, essential-distinct cleanup, or target
`UniformTubeStructure` is asserted here.  Those are later rediscretization
and transport obligations.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The fixed source coordinate cube used in the paper's Lemma 8. -/
def wz1MildRescalingSourceWindow : Set Point3 :=
  {p | ∀ i, |p i| ≤ 1}

/--
The source rectangular prism is the intersection of a centered isotropic box
with the fixed source coordinate cube.
-/
def wz1MildRescalingSourceBox
    (center halfWidth : Point3) : Set Point3 :=
  wz1AxisBox center halfWidth ∩ wz1MildRescalingSourceWindow

/--
Finite three-dimensional box pigeonhole in the exact form used by Lemma 8.

The center can be selected inside the fixed source window.  Boundary boxes
are clipped to that window; this does not lose source mass because the input
shading already lies there.
-/
def WZ1MildRescalingBoxPigeonholeStatement : Prop :=
  ∀ {F : Kakeya.Streamlined.BodyFamily},
    ∀ Y : Kakeya.Streamlined.Shading F,
        Y.union ⊆ wz1MildRescalingSourceWindow →
          ∀ h : ℝ, 0 < h → h ≤ 1 →
            ∃ center : Point3,
              (∀ i : Fin 3, |center i| ≤ 1 - h / 2) ∧
                center ∈ wz1MildRescalingSourceWindow ∧
                ENNReal.ofReal (h ^ 3 / 27) * Y.mass ≤
                  ∑ i,
                    MeasureTheory.volume
                      (Y.carrier i ∩
                        wz1MildRescalingSourceBox center
                          (point3 (h / 2) (h / 2) (h / 2)))

/--
One mass-popular source box and its normalizing isotropic similarity.

The exact box restriction is retained.  A later essential-distinct cleanup
may refine `selected`, but may not replace it by an unrelated shading.
-/
structure WZ1MildRescalingPopularBoxData
    {sigma inputLoss sourceDelta targetDelta₀ : ℝ}
    (source :
      WZ1PreNormalizedPlaninessGraininessData
        sigma inputLoss sourceDelta) where
  center : Point3
  center_mem_source_window :
    center ∈ wz1MildRescalingSourceWindow
  halfWidth : Point3
  halfWidth_pos : ∀ i, 0 < halfWidth i
  scale : Point3
  scale_eq :
    ∀ i, scale i = Real.rpow sourceDelta (-inputLoss)
  one_le_scale : ∀ i, 1 ≤ scale i
  scale_isotropic :
    scale 0 = scale 1 ∧ scale 1 = scale 2
  halfWidth_eq :
    ∀ i, halfWidth i = 1 / (4 * scale i)
  selected :
    Kakeya.Streamlined.TubeShading source.family
  selected_carrier_eq :
    ∀ i,
      selected.carrier i =
        source.shading.carrier i ∩
          wz1MildRescalingSourceBox center halfWidth
  selected_subshading :
    IsSubshading selected source.shading
  selected_mass :
    Kakeya.realRpowENN sourceDelta (10 * inputLoss) *
        source.shading.mass ≤
      selected.mass
  box_maps_to_window :
    wz1MildRescalingMap center scale ''
        wz1MildRescalingSourceBox center halfWidth ⊆
      wz1CoordinateWindow
  slope_lipschitz_le_scale :
    (source.global_grains.lipschitzConstant : ℝ) ≤ scale 0
  planeMap_lipschitz_le_scale :
    (source.local_grains.lipschitzConstant : ℝ) ≤ scale 0
  targetDelta : ℝ
  targetDelta_pos : 0 < targetDelta
  targetDelta_eq :
    targetDelta = sourceDelta * scale 0
  sourceDelta_le_targetDelta :
    sourceDelta ≤ targetDelta
  targetDelta_le_quarter :
    targetDelta ≤ 1 / 4
  targetDelta_le_one_thousand :
    targetDelta ≤ 1 / 1000
  targetDelta_le_target :
    targetDelta ≤ targetDelta₀
  targetDelta_le_source_power :
    targetDelta ≤ Real.rpow sourceDelta (1 - inputLoss)

/--
Select a mass-popular source box at the isotropic scale
`sourceDelta^(-inputLoss)`.

The small source threshold absorbs the fixed finite covering constant and
ensures that the enlarged target radius stays below the caller's threshold.
-/
def WZ1MildRescalingPopularBoxStatement : Prop :=
  WZ1MildRescalingBoxPigeonholeStatement →
    ∀ sigma inputLoss targetDelta₀ : ℝ,
      0 < sigma → sigma < 1 →
      0 < inputLoss → inputLoss < 1 / 4 →
      0 < targetDelta₀ →
        ∃ sourceDelta₀ : ℝ,
          0 < sourceDelta₀ ∧ sourceDelta₀ ≤ 1 / 10000 ∧
          ∀ sourceDelta : ℝ,
            0 < sourceDelta → sourceDelta ≤ sourceDelta₀ →
              ∀ source :
                  WZ1PreNormalizedPlaninessGraininessData
                    sigma inputLoss sourceDelta,
                Nonempty
                  (WZ1MildRescalingPopularBoxData
                    (targetDelta₀ := targetDelta₀) source)

end Kakeya.Assouad
