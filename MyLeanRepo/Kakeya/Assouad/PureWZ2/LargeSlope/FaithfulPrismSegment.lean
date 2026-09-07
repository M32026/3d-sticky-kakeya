import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FaithfulPrismGeometry
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometryHelpers
import MyLeanRepo.Kakeya.Assouad.LargeSlope.Step4WitnessGeometry

/-!
# Paper slab inside one short axis segment
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

theorem pureWZ2_paper_tube_slab_in_segment
    {delta a b rho : ℝ}
    (hdelta : 0 < delta) (hab : a < b) (hrho : 0 < rho)
    (hlength : 2 * (b - a + 12 * delta) ≤ Real.sqrt rho)
    {tube : Kakeya.DeltaTube delta}
    (hvertical : (1 / 2 : ℝ) ≤ |tube.direction 2|) :
    ∃ start : ℝ,
      wz1PaperTubeCarrier tube ∩ horizontalSlab a b ⊆
        tubeSegmentCarrier (6 * delta) tube.base tube.direction start rho := by
  let d2 := tube.direction 2
  have hd2 : d2 ≠ 0 := by
    intro hzero
    have hzero' : tube.direction 2 = 0 := by simpa [d2] using hzero
    rw [hzero', abs_zero] at hvertical
    norm_num at hvertical
  have hlineClosed : IsClosed (tubeAxisLine tube) :=
    isClosed_tubeAxisLine tube
  let width := b - a
  have hthickness : 0 < 6 * delta := by positivity
  by_cases hd2Pos : 0 < d2
  · let start := (a - 6 * delta - tube.base 2) / d2
    refine ⟨start, ?_⟩
    intro point hpoint
    rcases exists_dist_le_of_mem_cthickening_closed hlineClosed
        (by positivity) hpoint.1.1 with
      ⟨axisPoint, haxisPoint, hdistance⟩
    rcases haxisPoint with ⟨parameter, rfl⟩
    let onAxis := tube.base + parameter • tube.direction
    have hnorm : ‖point - onAxis‖ ≤ 6 * delta := by
      simpa [dist_eq_norm] using hdistance
    have hz : |point 2 - onAxis 2| ≤ 6 * delta :=
      (PiLp.norm_apply_le (point - onAxis) 2).trans hnorm
    have honAxis : onAxis 2 = tube.base 2 + parameter * d2 := by
      simp [onAxis, d2] <;> abel
    have hlower : a - 6 * delta ≤ onAxis 2 := by
      linarith [hpoint.2.1, abs_le.mp hz]
    have hupper : onAxis 2 ≤ b + 6 * delta := by
      linarith [hpoint.2.2, abs_le.mp hz]
    have hstart : start ≤ parameter := by
      dsimp only [start]
      apply (div_le_iff₀ hd2Pos).2
      rw [honAxis] at hlower
      linarith
    have hspan : parameter - start ≤ 2 * (width + 12 * delta) := by
      have hraw : parameter * d2 -
          (a - 6 * delta - tube.base 2) ≤ width + 12 * delta := by
        rw [honAxis] at hupper
        dsimp only [width]
        linarith
      have hdivide : parameter - start ≤ (width + 12 * delta) / d2 := by
        dsimp only [start]
        rw [show parameter -
            (a - 6 * delta - tube.base 2) / d2 =
          (parameter * d2 - (a - 6 * delta - tube.base 2)) / d2 by
            field_simp [hd2Pos.ne'] <;> ring]
        exact (div_le_div_iff_of_pos_right hd2Pos).2 hraw
      have hinv : 1 / d2 ≤ 2 := by
        have habs : |d2| = d2 := abs_of_pos hd2Pos
        rw [habs] at hvertical
        calc
          1 / d2 ≤ 1 / (1 / 2 : ℝ) := by gcongr
          _ = 2 := by norm_num
      calc
        parameter - start ≤ (width + 12 * delta) / d2 := hdivide
        _ = (width + 12 * delta) * (1 / d2) := by ring
        _ ≤ (width + 12 * delta) * 2 := by gcongr <;> positivity
        _ = 2 * (width + 12 * delta) := by ring
    have hparameter : parameter ∈ Set.Icc start
        (start + Real.sqrt rho) := ⟨hstart, by linarith⟩
    exact mem_tube_segment (delta := 6 * delta) hparameter
      hdistance hthickness
  · have hd2Neg : d2 < 0 := by
      have hle : d2 ≤ 0 := le_of_not_gt hd2Pos
      exact lt_of_le_of_ne hle hd2
    let start := (b + 6 * delta - tube.base 2) / d2
    refine ⟨start, ?_⟩
    intro point hpoint
    rcases exists_dist_le_of_mem_cthickening_closed hlineClosed
        (by positivity) hpoint.1.1 with
      ⟨axisPoint, haxisPoint, hdistance⟩
    rcases haxisPoint with ⟨parameter, rfl⟩
    let onAxis := tube.base + parameter • tube.direction
    have hnorm : ‖point - onAxis‖ ≤ 6 * delta := by
      simpa [dist_eq_norm] using hdistance
    have hz : |point 2 - onAxis 2| ≤ 6 * delta :=
      (PiLp.norm_apply_le (point - onAxis) 2).trans hnorm
    have honAxis : onAxis 2 = tube.base 2 + parameter * d2 := by
      simp [onAxis, d2] <;> abel
    have hlower : a - 6 * delta ≤ onAxis 2 := by
      linarith [hpoint.2.1, abs_le.mp hz]
    have hupper : onAxis 2 ≤ b + 6 * delta := by
      linarith [hpoint.2.2, abs_le.mp hz]
    have hstart : start ≤ parameter := by
      dsimp only [start]
      rw [div_le_iff_of_neg hd2Neg]
      rw [honAxis] at hupper
      linarith
    have habs : |d2| = -d2 := abs_of_neg hd2Neg
    have hspan : parameter - start ≤ 2 * (width + 12 * delta) := by
      have hraw : -(parameter * d2 -
          (b + 6 * delta - tube.base 2)) ≤ width + 12 * delta := by
        rw [honAxis] at hlower
        dsimp only [width]
        linarith
      have heq : parameter - start =
          (-(parameter * d2 -
            (b + 6 * delta - tube.base 2))) / |d2| := by
        dsimp only [start]
        rw [habs]
        field_simp [hd2Neg.ne] <;> ring
      rw [heq]
      have hdivide :
          (-(parameter * d2 - (b + 6 * delta - tube.base 2))) / |d2| ≤
            (width + 12 * delta) / |d2| := by gcongr
      have hinv : 1 / |d2| ≤ 2 := by
        calc
          1 / |d2| ≤ 1 / (1 / 2 : ℝ) := by gcongr
          _ = 2 := by norm_num
      calc
        (-(parameter * d2 - (b + 6 * delta - tube.base 2))) / |d2| ≤
            (width + 12 * delta) / |d2| := hdivide
        _ = (width + 12 * delta) * (1 / |d2|) := by ring
        _ ≤ (width + 12 * delta) * 2 := by gcongr <;> positivity
        _ = 2 * (width + 12 * delta) := by ring
    have hparameter : parameter ∈ Set.Icc start
        (start + Real.sqrt rho) := ⟨hstart, by linarith⟩
    exact mem_tube_segment (delta := 6 * delta) hparameter
      hdistance hthickness

end Kakeya.Assouad

end
