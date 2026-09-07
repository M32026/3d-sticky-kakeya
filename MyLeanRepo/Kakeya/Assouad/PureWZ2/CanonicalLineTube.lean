import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryRescaledTube
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralCommonRescalingLineCoverHelpers

/-!
# Canonical orientation of one WZ tube

A WZ line-class tube has a preferred positive direction.  Reversing the
stored unit segment when necessary preserves the ordinary carrier and the
paper line metric.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The same ordinary tube carrier, stored in the paper-positive orientation. -/
def wz2PaperCanonicalLineTube
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    Kakeya.DeltaTube delta :=
  if 0 ≤ tube.direction (2 : Fin 3) then tube else reverseTube tube

@[simp] theorem wz2PaperCanonicalLineTube_carrier
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    (wz2PaperCanonicalLineTube tube).carrier = tube.carrier := by
  unfold wz2PaperCanonicalLineTube
  split_ifs
  · rfl
  · exact reverseTube_carrier tube

@[simp] theorem wz2PaperCanonicalLineTube_paperDirection
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (hline : WZ1PaperTubeInLineClass tube) :
    wz1PaperDirection (wz2PaperCanonicalLineTube tube) =
      wz1PaperDirection tube := by
  unfold wz2PaperCanonicalLineTube
  split_ifs with horientation
  · rfl
  · exact wz1PaperDirection_reverse_of_lineClass hline

theorem wz2PaperCanonicalLineTube_axis
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    tubeAxisLine (wz2PaperCanonicalLineTube tube) =
      tubeAxisLine tube := by
  unfold wz2PaperCanonicalLineTube
  split_ifs with horientation
  · rfl
  · ext point
    constructor
    · rintro ⟨parameter, rfl⟩
      refine ⟨1 - parameter, ?_⟩
      simp [reverseTube]
      module
    · rintro ⟨parameter, rfl⟩
      refine ⟨1 - parameter, ?_⟩
      simp [reverseTube]
      module

@[simp] theorem wz2PaperCanonicalLineTube_axisZero
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (hline : WZ1PaperTubeInLineClass tube) :
    wz1TubeAxisZeroPoint (wz2PaperCanonicalLineTube tube) =
      wz1TubeAxisZeroPoint tube := by
  apply
    wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
      (show
        (1 / 2 : ℝ) ≤
          |(wz2PaperCanonicalLineTube tube).direction (2 : Fin 3)| by
        unfold wz2PaperCanonicalLineTube
        split_ifs
        · exact hline.vertical
        · simpa using hline.vertical)
  · rw [wz2PaperCanonicalLineTube_axis]
    exact wz1TubeAxisZeroPoint_mem_axis tube
  · exact wz1TubeAxisZeroPoint_coord_two tube hline.vertical

theorem wz2PaperCanonicalLineTube_lineClass
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (hline : WZ1PaperTubeInLineClass tube) :
    WZ1PaperTubeInLineClass (wz2PaperCanonicalLineTube tube) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [wz2PaperCanonicalLineTube_paperDirection hline]
    exact hline.1
  · rw [wz2PaperCanonicalLineTube_axisZero hline]
    exact hline.2.1
  · rw [wz2PaperCanonicalLineTube_axisZero hline]
    exact hline.2.2

@[simp] theorem wz1PaperLineDistance_canonicalLineTube
    {firstScale secondScale : ℝ}
    {first : Kakeya.DeltaTube firstScale}
    {second : Kakeya.DeltaTube secondScale}
    (firstLine : WZ1PaperTubeInLineClass first)
    (secondLine : WZ1PaperTubeInLineClass second) :
    wz1PaperLineDistance
        (wz2PaperCanonicalLineTube first)
        (wz2PaperCanonicalLineTube second) =
      wz1PaperLineDistance first second := by
  unfold wz1PaperLineDistance
  rw [wz2PaperCanonicalLineTube_axisZero firstLine,
    wz2PaperCanonicalLineTube_axisZero secondLine,
    wz2PaperCanonicalLineTube_paperDirection firstLine,
    wz2PaperCanonicalLineTube_paperDirection secondLine]

end Kakeya.Assouad

end
