import MyLeanRepo.Kakeya.Assouad.PropStickyPaperUnitRescalingBasics
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLongitudinalCompressionLineDistanceAxisHelpers

/-!
# Paper line class is an invariant of the coaxial line

Two formal tubes may use different base points and opposite unit directions
while representing the same full affine line.  The fixed paper line class
depends only on that line: it uses the positively oriented unit direction and
the unique intersection with `z = 0`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Set

@[simp] lemma paperDirection_coord_two_eq_abs_direction
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    wz1PaperDirection tube (2 : Fin 3) =
      |tube.direction (2 : Fin 3)| := by
  unfold wz1PaperDirection
  split_ifs with hdirection
  · exact (abs_of_nonneg hdirection).symm
  · simp [abs_of_neg (lt_of_not_ge hdirection)]

/-- Coaxial tubes have the same positively oriented paper direction.  This
removes the arbitrary sign and basepoint choices in their stored unit
directions. -/
lemma paperDirection_eq_of_same_axis
    {firstDelta secondDelta : ℝ}
    {first : Kakeya.DeltaTube firstDelta}
    {second : Kakeya.DeltaTube secondDelta}
    (hfirstLine : WZ1PaperTubeInLineClass first)
    (hsecondLine : WZ1PaperTubeInLineClass second)
    (haxis : tubeAxisLine first = tubeAxisLine second) :
    wz1PaperDirection first = wz1PaperDirection second := by
  rcases Kakeya.Assouad.axisLine_eq_iff_direction_parallel haxis with
    ⟨scale, _scaleNe, hsecondDirection⟩
  have hscaleAbs : |scale| = 1 := by
    have hnorm := congrArg norm hsecondDirection
    rw [second.direction_unit, norm_smul, first.direction_unit, mul_one,
      Real.norm_eq_abs] at hnorm
    exact hnorm.symm
  have hfirstPaperSign : ∃ firstSign : ℝ,
      (firstSign = 1 ∨ firstSign = -1) ∧
        first.direction = firstSign • wz1PaperDirection first := by
    unfold wz1PaperDirection
    split_ifs <;> simp
  have hsecondPaperSign : ∃ secondSign : ℝ,
      (secondSign = 1 ∨ secondSign = -1) ∧
        second.direction = secondSign • wz1PaperDirection second := by
    unfold wz1PaperDirection
    split_ifs <;> simp
  rcases hfirstPaperSign with
    ⟨firstSign, hfirstSign, hfirstDirection⟩
  rcases hsecondPaperSign with
    ⟨secondSign, hsecondSign, hsecondDirection'⟩
  have hpaperParallel : wz1PaperDirection second =
      (secondSign * scale * firstSign) • wz1PaperDirection first := by
    have hfirstSignSq : firstSign * firstSign = 1 := by
      rcases hfirstSign with rfl | rfl <;> norm_num
    calc
      wz1PaperDirection second = secondSign • second.direction := by
        rw [hsecondDirection']
        rcases hsecondSign with rfl | rfl <;> simp
      _ = secondSign • (scale • first.direction) := by rw [hsecondDirection]
      _ = secondSign • (scale •
          (firstSign • wz1PaperDirection first)) := by rw [hfirstDirection]
      _ = (secondSign * scale * firstSign) •
          wz1PaperDirection first := by simp [smul_smul]; ring
  have hcoefficientAbs : |secondSign * scale * firstSign| = 1 := by
    rcases hfirstSign with rfl | rfl <;>
      rcases hsecondSign with rfl | rfl <;> simp [hscaleAbs]
  have hcoefficient : secondSign * scale * firstSign = 1 := by
    have hcoordinate := congrArg (fun vector : Point3 => vector (2 : Fin 3))
      hpaperParallel
    simp only [PiLp.smul_apply, smul_eq_mul] at hcoordinate
    have hcases : secondSign * scale * firstSign = 1 ∨
        secondSign * scale * firstSign = -1 :=
      (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hcoefficientAbs
    rcases hcases with h | h
    · exact h
    · rw [h] at hcoordinate
      norm_num at hcoordinate
      have hfirstAbs : (1 / 2 : ℝ) ≤ |first.direction (2 : Fin 3)| := by
        simpa only [paperDirection_coord_two_eq_abs_direction] using
          hfirstLine.1
      nlinarith [hfirstAbs, abs_nonneg (second.direction (2 : Fin 3))]
  rw [hpaperParallel, hcoefficient, one_smul]

/-- Coaxial tubes share membership in the fixed paper line class. -/
lemma paperTubeInLineClass_of_same_axis
    {firstDelta secondDelta : ℝ}
    {first : Kakeya.DeltaTube firstDelta}
    {second : Kakeya.DeltaTube secondDelta}
    (hsecond : WZ1PaperTubeInLineClass second)
    (haxis : tubeAxisLine first = tubeAxisLine second) :
    WZ1PaperTubeInLineClass first := by
  let secondZero := wz1TubeAxisZeroPoint second
  let secondDirection := wz1PaperDirection second
  have hsecondZeroAxis : secondZero ∈ tubeAxisLine second :=
    wz1TubeAxisZeroPoint_mem_axis second
  have hsecondOneAxis : secondZero + secondDirection ∈ tubeAxisLine second :=
    wz1TubeAxisZeroPoint_add_paperDirection_mem_axis second
  have hsecondZeroFirst : secondZero ∈ tubeAxisLine first := by
    rw [haxis]
    exact hsecondZeroAxis
  have hsecondOneFirst : secondZero + secondDirection ∈ tubeAxisLine first := by
    rw [haxis]
    exact hsecondOneAxis
  rcases hsecondZeroFirst with ⟨zeroParameter, hzeroParameter⟩
  rcases hsecondOneFirst with ⟨oneParameter, honeParameter⟩
  have hdirection : secondDirection =
      (oneParameter - zeroParameter) • first.direction := by
    rw [show secondDirection =
        (secondZero + secondDirection) - secondZero by abel,
      honeParameter, hzeroParameter]
    module
  have hscaleAbs : |oneParameter - zeroParameter| = 1 := by
    have hnorm := congrArg norm hdirection
    rw [wz1PaperDirection_norm, norm_smul, first.direction_unit, mul_one,
      Real.norm_eq_abs] at hnorm
    exact hnorm.symm
  have hverticalAbs :
      |secondDirection (2 : Fin 3)| =
        |first.direction (2 : Fin 3)| := by
    have hcoord := congrArg (fun vector : Point3 => vector (2 : Fin 3))
      hdirection
    rw [hcoord, PiLp.smul_apply, smul_eq_mul, abs_mul, hscaleAbs, one_mul]
  have hsecondDirectionVertical :
      (1 / 2 : ℝ) ≤ |secondDirection (2 : Fin 3)| := by
    have hnonnegative : 0 ≤ secondDirection (2 : Fin 3) := by
      unfold secondDirection wz1PaperDirection
      split_ifs with hsign
      · exact hsign
      · simp only [PiLp.neg_apply]
        exact neg_nonneg.mpr (le_of_not_ge hsign)
    rw [abs_of_nonneg hnonnegative]
    exact hsecond.1
  have hfirstVerticalAbs :
      (1 / 2 : ℝ) ≤ |first.direction (2 : Fin 3)| := by
    rw [← hverticalAbs]
    exact hsecondDirectionVertical
  have hfirstPaperVertical :
      (1 / 2 : ℝ) ≤ wz1PaperDirection first (2 : Fin 3) := by
    unfold wz1PaperDirection
    split_ifs with hsign
    · simpa [abs_of_nonneg hsign] using hfirstVerticalAbs
    · have hnegative : first.direction (2 : Fin 3) < 0 :=
        lt_of_not_ge hsign
      simpa [abs_of_neg hnegative] using hfirstVerticalAbs
  have hfirstZero : wz1TubeAxisZeroPoint first = secondZero := by
    apply wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
      hfirstVerticalAbs
    · rw [haxis]
      exact hsecondZeroAxis
    dsimp only [secondZero]
    exact wz1TubeAxisZeroPoint_coord_two second hsecond.vertical
  refine ⟨hfirstPaperVertical, ?_, ?_⟩
  · rw [hfirstZero]
    exact hsecond.2.1
  · rw [hfirstZero]
    exact hsecond.2.2

end Kakeya.Assouad.PureWZ2

end
