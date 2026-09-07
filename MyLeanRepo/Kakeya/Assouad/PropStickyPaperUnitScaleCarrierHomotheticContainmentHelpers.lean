import MyLeanRepo.Kakeya.Assouad.PropStickyPaperUnitRescalingBasics
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometryHelpers

/-!
# Helpers for unit-scale carrier homothetic containment

At coarse scale one, the paper linear map is
`transverseScaleLin 100` after the Householder reflection.  This file records
the explicit inverse and its norm bound.
-/

noncomputable section

namespace Kakeya.Assouad

lemma wz1PaperUnitRescalingLinear_eq_at_one
    (coarse : Kakeya.DeltaTube 1) (vector : Point3) :
    wz1PaperUnitRescalingLinear coarse vector =
      transverseScaleLin (100 : ℝ)
        (householderToE3
          (wz1PaperDirection coarse)
          (wz1PaperDirection_norm coarse) vector) := by
  have hscale : (100 * (1 : ℝ)) = 100 := by
    norm_num
  dsimp only [wz1PaperUnitRescalingLinear, unitRescalingLinear]
  rw [hscale]
  rfl

lemma wz1PaperUnitRescalingLinear_left_inverse
    (coarse : Kakeya.DeltaTube 1) (vector : Point3) :
    (householderToE3
        (wz1PaperDirection coarse)
        (wz1PaperDirection_norm coarse))
      (transverseScaleLin (1 / 100 : ℝ)
        (wz1PaperUnitRescalingLinear coarse vector)) =
      vector := by
  let rotation :=
    householderToE3
      (wz1PaperDirection coarse)
      (wz1PaperDirection_norm coarse)
  rw [wz1PaperUnitRescalingLinear_eq_at_one]
  have hscaling :
      transverseScaleLin (1 / 100 : ℝ)
          (transverseScaleLin (100 : ℝ) (rotation vector)) =
        rotation vector := by
    ext coordinate
    fin_cases coordinate <;>
      simp [transverseScaleLin_coord0,
        transverseScaleLin_coord1,
        transverseScaleLin_coord2]
  rw [hscaling]
  exact householderToE3_involution _ _ _

lemma wz1PaperUnitRescalingLinear_right_inverse
    (coarse : Kakeya.DeltaTube 1) (vector : Point3) :
    wz1PaperUnitRescalingLinear coarse
        ((householderToE3
          (wz1PaperDirection coarse)
          (wz1PaperDirection_norm coarse))
          (transverseScaleLin (1 / 100 : ℝ) vector)) =
      vector := by
  let rotation :=
    householderToE3
      (wz1PaperDirection coarse)
      (wz1PaperDirection_norm coarse)
  let preimage :=
    rotation (transverseScaleLin (1 / 100 : ℝ) vector)
  have hrotation :
      rotation preimage =
        transverseScaleLin (1 / 100 : ℝ) vector := by
    simpa [preimage] using
      householderToE3_involution
        (wz1PaperDirection coarse)
        (wz1PaperDirection_norm coarse)
        (transverseScaleLin (1 / 100 : ℝ) vector)
  rw [wz1PaperUnitRescalingLinear_eq_at_one,
    show
      householderToE3
          (wz1PaperDirection coarse)
          (wz1PaperDirection_norm coarse)
          ((householderToE3
            (wz1PaperDirection coarse)
            (wz1PaperDirection_norm coarse))
            (transverseScaleLin (1 / 100 : ℝ) vector)) =
        transverseScaleLin (1 / 100 : ℝ) vector by
      exact hrotation]
  ext coordinate
  fin_cases coordinate <;>
    simp [transverseScaleLin_coord0,
      transverseScaleLin_coord1,
      transverseScaleLin_coord2]

lemma wz1PaperUnitRescalingLinear_inv_norm_le
    (coarse : Kakeya.DeltaTube 1) (vector : Point3) :
    ‖(householderToE3
        (wz1PaperDirection coarse)
        (wz1PaperDirection_norm coarse))
      (transverseScaleLin (1 / 100 : ℝ) vector)‖ ≤
      100 * ‖vector‖ := by
  rw [householderToE3_norm]
  have hbound :
      ‖transverseScaleLin (1 / 100 : ℝ) vector‖ ≤
        (1 / (1 / 100 : ℝ)) * ‖vector‖ :=
    transverseScaleLin_norm_bound
      (1 / 100 : ℝ) (by norm_num) (by norm_num) vector
  norm_num at hbound ⊢
  exact hbound

lemma wz1TubeAxisLine_smul_about_zero_point
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (hvertical : (1 / 2 : ℝ) ≤ |tube.direction 2|)
    {axisPoint : Point3}
    (haxisPoint : axisPoint ∈ tubeAxisLine tube)
    (scale : ℝ) :
    wz1TubeAxisZeroPoint tube +
        scale • (axisPoint - wz1TubeAxisZeroPoint tube) ∈
      tubeAxisLine tube := by
  let zeroPoint := wz1TubeAxisZeroPoint tube
  have haxis := tubeAxisLine_eq_affineSpan tube hvertical
  rw [haxis] at haxisPoint ⊢
  rcases haxisPoint with ⟨parameter, hparameter⟩
  refine ⟨scale * parameter, ?_⟩
  rw [hparameter]
  have hsimplify :
      zeroPoint +
          scale •
            (zeroPoint +
                parameter • wz1PaperDirection tube -
              zeroPoint) =
        zeroPoint +
          (scale * parameter) •
            wz1PaperDirection tube := by
    module
  exact hsimplify

lemma wz1PaperUnitRescalingMap_smul_about_zero_point
    {delta rho : ℝ}
    (coarse : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    {source : Kakeya.DeltaTube delta}
    (axisPoint : Point3) (scale : ℝ) :
    wz1PaperUnitRescalingMap coarse hrho
        (wz1TubeAxisZeroPoint source +
          scale •
            (axisPoint - wz1TubeAxisZeroPoint source)) =
      wz1PaperUnitRescalingMap coarse hrho
          (wz1TubeAxisZeroPoint source) +
        scale •
          (wz1PaperUnitRescalingMap coarse hrho axisPoint -
            wz1PaperUnitRescalingMap coarse hrho
              (wz1TubeAxisZeroPoint source)) := by
  let zeroPoint := wz1TubeAxisZeroPoint source
  let rescaling := wz1PaperUnitRescalingMap coarse hrho
  let linearMap := wz1PaperUnitRescalingLinear coarse
  have hadd :
      rescaling
          (zeroPoint +
            scale • (axisPoint - zeroPoint)) =
        rescaling zeroPoint +
          linearMap
            (scale • (axisPoint - zeroPoint)) :=
    wz1PaperUnitRescalingMap_add
      coarse hrho zeroPoint
        (scale • (axisPoint - zeroPoint))
  have hlinear :
      linearMap (scale • (axisPoint - zeroPoint)) =
        scale • linearMap (axisPoint - zeroPoint) :=
    linearMap.map_smul scale (axisPoint - zeroPoint)
  have hsub :
      rescaling axisPoint - rescaling zeroPoint =
        linearMap (axisPoint - zeroPoint) :=
    wz1PaperUnitRescalingMap_sub
      coarse hrho axisPoint zeroPoint
  change
    rescaling
        (zeroPoint + scale • (axisPoint - zeroPoint)) =
      rescaling zeroPoint +
        scale • (rescaling axisPoint - rescaling zeroPoint)
  rw [hadd, hlinear, ← hsub]

end Kakeya.Assouad

end
