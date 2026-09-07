import MyLeanRepo.Kakeya.Assouad.PureWZ2.CanonicalLineTube
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometryHelpers

/-!
# Midpoint-centered representative of a WZ paper line

The paper tube model depends only on the supporting line.  Ordinary
Definition 2.12 additionally remembers a finite unit segment, so arbitrary
longitudinal parametrizations can destroy ordinary essential distinctness.

This constructor keeps the supporting line and paper line metric exactly,
but centers the ordinary unit segment at the line's `z = 0` intercept.
-/

noncomputable section

namespace Kakeya.Assouad

def wz2PaperCenteredLineTube
    {sourceScale targetScale : ℝ}
    (tube : Kakeya.DeltaTube sourceScale) :
    Kakeya.DeltaTube targetScale where
  base :=
    wz1TubeAxisZeroPoint tube -
      (1 / 2 : ℝ) • wz1PaperDirection tube
  direction := wz1PaperDirection tube
  direction_unit := wz1PaperDirection_norm tube

@[simp] theorem wz2PaperCenteredLineTube_midpoint
    {sourceScale targetScale : ℝ}
    (tube : Kakeya.DeltaTube sourceScale) :
    wz2PaperTubeMidpoint
        (wz2PaperCenteredLineTube
          (targetScale := targetScale) tube) =
      wz1TubeAxisZeroPoint tube := by
  unfold wz2PaperTubeMidpoint wz2PaperCenteredLineTube
  module

@[simp] theorem wz2PaperCenteredLineTube_axis
    {sourceScale targetScale : ℝ}
    (tube : Kakeya.DeltaTube sourceScale)
    (line : WZ1PaperTubeInLineClass tube) :
    tubeAxisLine
        (wz2PaperCenteredLineTube
          (targetScale := targetScale) tube) =
      tubeAxisLine tube := by
  have sourceVertical :
      (1 / 2 : ℝ) ≤ |tube.direction (2 : Fin 3)| :=
    line.vertical
  rw [tubeAxisLine_eq_affineSpan tube sourceVertical]
  unfold tubeAxisLine
  ext point
  constructor
  · rintro ⟨parameter, rfl⟩
    refine ⟨parameter - 1 / 2, ?_⟩
    simp only [wz2PaperCenteredLineTube]
    module
  · rintro ⟨parameter, rfl⟩
    refine ⟨parameter + 1 / 2, ?_⟩
    simp only [wz2PaperCenteredLineTube]
    module

@[simp] theorem wz2PaperCenteredLineTube_paperDirection
    {sourceScale targetScale : ℝ}
    {tube : Kakeya.DeltaTube sourceScale}
    (line : WZ1PaperTubeInLineClass tube) :
    wz1PaperDirection
        (wz2PaperCenteredLineTube
          (targetScale := targetScale) tube) =
      wz1PaperDirection tube := by
  have positive :
      0 ≤ wz1PaperDirection tube (2 : Fin 3) :=
    le_trans (by norm_num) line.1
  change
    (if 0 ≤ wz1PaperDirection tube (2 : Fin 3) then
        wz1PaperDirection tube
      else
        -wz1PaperDirection tube) =
      wz1PaperDirection tube
  rw [if_pos positive]

@[simp] theorem wz2PaperCenteredLineTube_axisZero
    {sourceScale targetScale : ℝ}
    {tube : Kakeya.DeltaTube sourceScale}
    (line : WZ1PaperTubeInLineClass tube) :
    wz1TubeAxisZeroPoint
        (wz2PaperCenteredLineTube
          (targetScale := targetScale) tube) =
      wz1TubeAxisZeroPoint tube := by
  apply
    wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
      (show
        (1 / 2 : ℝ) ≤
          |(wz2PaperCenteredLineTube
            (targetScale := targetScale) tube).direction
              (2 : Fin 3)| by
        change
          (1 / 2 : ℝ) ≤
            |wz1PaperDirection tube (2 : Fin 3)|
        rw [abs_of_nonneg (le_trans (by norm_num) line.1)]
        exact line.1)
  · rw [wz2PaperCenteredLineTube_axis tube line]
    exact wz1TubeAxisZeroPoint_mem_axis tube
  · exact wz1TubeAxisZeroPoint_coord_two tube line.vertical

theorem wz2PaperCenteredLineTube_lineClass
    {sourceScale targetScale : ℝ}
    {tube : Kakeya.DeltaTube sourceScale}
    (line : WZ1PaperTubeInLineClass tube) :
    WZ1PaperTubeInLineClass
      (wz2PaperCenteredLineTube
        (targetScale := targetScale) tube) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [wz2PaperCenteredLineTube_paperDirection line]
    exact line.1
  · rw [wz2PaperCenteredLineTube_axisZero line]
    exact line.2.1
  · rw [wz2PaperCenteredLineTube_axisZero line]
    exact line.2.2

@[simp] theorem wz2PaperCenteredLineTube_idem
    {scale : ℝ}
    {tube : Kakeya.DeltaTube scale}
    (line : WZ1PaperTubeInLineClass tube) :
    wz2PaperCenteredLineTube
        (targetScale := scale)
        (wz2PaperCenteredLineTube
          (targetScale := scale) tube) =
      wz2PaperCenteredLineTube
        (targetScale := scale) tube := by
  rw [Kakeya.DeltaTube.mk.injEq]
  constructor
  · change
      wz1TubeAxisZeroPoint
          (wz2PaperCenteredLineTube
            (targetScale := scale) tube) -
          (1 / 2 : ℝ) •
            wz1PaperDirection
              (wz2PaperCenteredLineTube
                (targetScale := scale) tube) =
        wz1TubeAxisZeroPoint tube -
          (1 / 2 : ℝ) • wz1PaperDirection tube
    rw [wz2PaperCenteredLineTube_axisZero line,
      wz2PaperCenteredLineTube_paperDirection line]
  · exact wz2PaperCenteredLineTube_paperDirection line

@[simp] theorem wz2PaperCenteredLineTube_recenter
    {sourceScale middleScale targetScale : ℝ}
    {tube : Kakeya.DeltaTube sourceScale}
    (line : WZ1PaperTubeInLineClass tube) :
    wz2PaperCenteredLineTube
        (targetScale := targetScale)
        (wz2PaperCenteredLineTube
          (targetScale := middleScale) tube) =
      wz2PaperCenteredLineTube
        (targetScale := targetScale) tube := by
  rw [Kakeya.DeltaTube.mk.injEq]
  constructor
  · change
      wz1TubeAxisZeroPoint
          (wz2PaperCenteredLineTube
            (targetScale := middleScale) tube) -
          (1 / 2 : ℝ) •
            wz1PaperDirection
              (wz2PaperCenteredLineTube
                (targetScale := middleScale) tube) =
        wz1TubeAxisZeroPoint tube -
          (1 / 2 : ℝ) • wz1PaperDirection tube
    rw [wz2PaperCenteredLineTube_axisZero line,
      wz2PaperCenteredLineTube_paperDirection line]
  · exact wz2PaperCenteredLineTube_paperDirection line

@[simp] theorem wz1PaperLineDistance_centeredLineTube_right
    {firstScale secondScale targetScale : ℝ}
    {first : Kakeya.DeltaTube firstScale}
    {second : Kakeya.DeltaTube secondScale}
    (firstLine : WZ1PaperTubeInLineClass first)
    (secondLine : WZ1PaperTubeInLineClass second) :
    wz1PaperLineDistance first
        (wz2PaperCenteredLineTube
          (targetScale := targetScale) second) =
      wz1PaperLineDistance first second := by
  unfold wz1PaperLineDistance
  rw [wz2PaperCenteredLineTube_axisZero secondLine,
    wz2PaperCenteredLineTube_paperDirection secondLine]

@[simp] theorem wz1PaperLineDistance_centeredLineTube_both
    {firstScale secondScale targetScale : ℝ}
    {first : Kakeya.DeltaTube firstScale}
    {second : Kakeya.DeltaTube secondScale}
    (firstLine : WZ1PaperTubeInLineClass first)
    (secondLine : WZ1PaperTubeInLineClass second) :
    wz1PaperLineDistance
        (wz2PaperCenteredLineTube
          (targetScale := targetScale) first)
        (wz2PaperCenteredLineTube
          (targetScale := targetScale) second) =
      wz1PaperLineDistance first second := by
  unfold wz1PaperLineDistance
  rw [wz2PaperCenteredLineTube_axisZero firstLine,
    wz2PaperCenteredLineTube_axisZero secondLine,
    wz2PaperCenteredLineTube_paperDirection firstLine,
    wz2PaperCenteredLineTube_paperDirection secondLine]

@[simp] theorem wz1PaperTubeCarrier_centeredLineTube
    {sourceScale targetScale : ℝ}
    (tube : Kakeya.DeltaTube sourceScale)
    (line : WZ1PaperTubeInLineClass tube) :
    wz1PaperTubeCarrier
        (wz2PaperCenteredLineTube
          (targetScale := targetScale) tube) =
      Metric.cthickening (6 * targetScale)
          (tubeAxisLine tube) ∩
        Kakeya.Streamlined.axisBox 2 2 2 := by
  simp [wz1PaperTubeCarrier, wz2PaperCenteredLineTube_axis tube line]

theorem wz2PaperCenteredLineTube_midpoint_norm_le_one
    {sourceScale targetScale : ℝ}
    {tube : Kakeya.DeltaTube sourceScale}
    (line : WZ1PaperTubeInLineClass tube) :
    ‖wz2PaperTubeMidpoint
        (wz2PaperCenteredLineTube
          (targetScale := targetScale) tube)‖ ≤ 1 := by
  rw [wz2PaperCenteredLineTube_midpoint]
  let zero := wz1TubeAxisZeroPoint tube
  have zeroTwo : zero (2 : Fin 3) = 0 :=
    wz1TubeAxisZeroPoint_coord_two tube line.vertical
  have normSq := point3_coord_norm_sq zero
  rw [zeroTwo] at normSq
  have xSq :
      (zero (0 : Fin 3)) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
    have absBound : |zero (0 : Fin 3)| ≤ 1 / 3 := line.2.1
    have sqBound := sq_le_sq₀ (abs_nonneg (zero (0 : Fin 3)))
      (by norm_num : (0 : ℝ) ≤ 1 / 3) |>.2 absBound
    simpa [sq_abs] using sqBound
  have ySq :
      (zero (1 : Fin 3)) ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
    have absBound : |zero (1 : Fin 3)| ≤ 1 / 3 := line.2.2
    have sqBound := sq_le_sq₀ (abs_nonneg (zero (1 : Fin 3)))
      (by norm_num : (0 : ℝ) ≤ 1 / 3) |>.2 absBound
    simpa [sq_abs] using sqBound
  nlinarith [norm_nonneg zero]

end Kakeya.Assouad

end
