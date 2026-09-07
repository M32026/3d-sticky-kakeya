import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49RadialProjectionStatements

/-!
# Radial cone diameter for WZ1 Lemma 49

Two source points lie in one narrow strip and stay on the same positive side
of a viewpoint.  If their normalized radial directions are close, then the
source points themselves are close.  This is the geometric injectivity and
local-fiber estimate used by the radial Frostman transport.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Inner product of a normalized radial vector. -/
private lemma wz1Lemma49_radial_inner
    (vector direction : Point2) (hvector : 0 < ‖vector‖) :
    inner ℝ ((‖vector‖⁻¹ : ℝ) • vector) direction =
      inner ℝ vector direction / ‖vector‖ := by
  rw [real_inner_smul_left]
  field_simp [hvector.ne']

/--
The partial cone estimate.  It does not require the angular scale to dominate
the strip width divided by the viewpoint-side separation.
-/
theorem wz1_lemma49_partial_cone_diameter_bounded
    {base direction viewpoint first second : Point2}
    {width side angularRadius bound : ℝ}
    (hdirection : ‖direction‖ = 1)
    (hwidth : 0 < width) (hside : 0 < side)
    (hbound : 0 < bound)
    (hfirstStrip :
      |inner ℝ (first - base) (wz1Perp2 direction)| ≤ width / 2)
    (hsecondStrip :
      |inner ℝ (second - base) (wz1Perp2 direction)| ≤ width / 2)
    (hfirstSide :
      side / 2 ≤
        inner ℝ (first - viewpoint) (wz1Perp2 direction))
    (hsecondSide :
      side / 2 ≤
        inner ℝ (second - viewpoint) (wz1Perp2 direction))
    (hangularRadius : 0 < angularRadius)
    (hangular :
      ‖wz1Lemma49RadialDirection viewpoint first -
          wz1Lemma49RadialDirection viewpoint second‖ ≤
        angularRadius)
    (hfirstBound : ‖first - viewpoint‖ ≤ bound)
    (hsecondBound : ‖second - viewpoint‖ ≤ bound) :
    dist first second ≤
      bound * angularRadius +
        2 * bound ^ 2 * angularRadius / side +
        width + 2 * bound * width / side := by
  let parallel := direction
  let perpendicular := wz1Perp2 direction
  let firstVector := first - viewpoint
  let secondVector := second - viewpoint
  let firstNorm := ‖firstVector‖
  let secondNorm := ‖secondVector‖
  let firstParallel := inner ℝ firstVector parallel
  let secondParallel := inner ℝ secondVector parallel
  let firstPerp := inner ℝ firstVector perpendicular
  let secondPerp := inner ℝ secondVector perpendicular
  let parallelDifference := firstParallel - secondParallel
  let perpDifference := firstPerp - secondPerp
  have hperpendicularNorm : ‖perpendicular‖ = 1 := by
    have hsquare :
        ‖perpendicular‖ ^ 2 = ‖parallel‖ ^ 2 := by
      rw [norm2_sq perpendicular, norm2_sq parallel,
        (wz1Perp2_coords parallel).1,
        (wz1Perp2_coords parallel).2]
      ring
    rw [hdirection] at hsquare
    nlinarith [norm_nonneg perpendicular]
  have hfirstNormLower : side / 2 ≤ firstNorm := by
    have hinner :
        |firstPerp| ≤ firstNorm := by
      calc
        |firstPerp|
            ≤ ‖firstVector‖ * ‖perpendicular‖ :=
          abs_real_inner_le_norm firstVector perpendicular
        _ = firstNorm := by rw [hperpendicularNorm, mul_one]
    have hfirstPerpPos : 0 < firstPerp := by
      linarith
    rw [abs_of_pos hfirstPerpPos] at hinner
    exact hfirstSide.trans hinner
  have hsecondNormLower : side / 2 ≤ secondNorm := by
    have hinner :
        |secondPerp| ≤ secondNorm := by
      calc
        |secondPerp|
            ≤ ‖secondVector‖ * ‖perpendicular‖ :=
          abs_real_inner_le_norm secondVector perpendicular
        _ = secondNorm := by rw [hperpendicularNorm, mul_one]
    have hsecondPerpPos : 0 < secondPerp := by
      linarith
    rw [abs_of_pos hsecondPerpPos] at hinner
    exact hsecondSide.trans hinner
  have hfirstNormUpper : firstNorm ≤ bound := hfirstBound
  have hsecondNormUpper : secondNorm ≤ bound := hsecondBound
  have hfirstNormPos : 0 < firstNorm := by linarith
  have hsecondNormPos : 0 < secondNorm := by linarith
  have hperpDifference :
      |perpDifference| ≤ width := by
    have hfirst :
        inner ℝ (first - viewpoint) perpendicular =
          inner ℝ first perpendicular -
            inner ℝ viewpoint perpendicular := by
      rw [inner_sub_left]
    have hsecond :
        inner ℝ (second - viewpoint) perpendicular =
          inner ℝ second perpendicular -
            inner ℝ viewpoint perpendicular := by
      rw [inner_sub_left]
    have hfirstBase :
        inner ℝ (first - base) perpendicular =
          inner ℝ first perpendicular -
            inner ℝ base perpendicular := by
      rw [inner_sub_left]
    have hsecondBase :
        inner ℝ (second - base) perpendicular =
          inner ℝ second perpendicular -
            inner ℝ base perpendicular := by
      rw [inner_sub_left]
    have heq :
        perpDifference =
          inner ℝ (first - base) perpendicular -
            inner ℝ (second - base) perpendicular := by
      dsimp only [perpDifference, firstPerp, secondPerp,
        firstVector, secondVector]
      rw [hfirst, hsecond, hfirstBase, hsecondBase]
      ring
    rw [heq]
    exact (abs_sub _ _).trans (by
      calc
        |inner ℝ (first - base) perpendicular| +
              |inner ℝ (second - base) perpendicular|
            ≤ width / 2 + width / 2 := by
          gcongr
        _ = width := by ring)
  have hangularPerp :
      |firstPerp / firstNorm - secondPerp / secondNorm| ≤
        angularRadius := by
    have heq :
        inner ℝ
            (wz1Lemma49RadialDirection viewpoint first -
              wz1Lemma49RadialDirection viewpoint second)
            perpendicular =
          firstPerp / firstNorm -
            secondPerp / secondNorm := by
      rw [inner_sub_left]
      exact congrArg₂ (· - ·)
        (wz1Lemma49_radial_inner
          firstVector perpendicular hfirstNormPos)
        (wz1Lemma49_radial_inner
          secondVector perpendicular hsecondNormPos)
    have hinner :
        |inner ℝ
            (wz1Lemma49RadialDirection viewpoint first -
              wz1Lemma49RadialDirection viewpoint second)
            perpendicular| ≤
          ‖wz1Lemma49RadialDirection viewpoint first -
            wz1Lemma49RadialDirection viewpoint second‖ := by
      calc
        |inner ℝ
            (wz1Lemma49RadialDirection viewpoint first -
              wz1Lemma49RadialDirection viewpoint second)
            perpendicular|
            ≤
          ‖wz1Lemma49RadialDirection viewpoint first -
              wz1Lemma49RadialDirection viewpoint second‖ *
            ‖perpendicular‖ := abs_real_inner_le_norm _ _
        _ =
          ‖wz1Lemma49RadialDirection viewpoint first -
            wz1Lemma49RadialDirection viewpoint second‖ := by
          rw [hperpendicularNorm, mul_one]
    rw [heq] at hinner
    exact hinner.trans hangular
  have hangularParallel :
      |firstParallel / firstNorm -
          secondParallel / secondNorm| ≤ angularRadius := by
    have heq :
        inner ℝ
            (wz1Lemma49RadialDirection viewpoint first -
              wz1Lemma49RadialDirection viewpoint second)
            parallel =
          firstParallel / firstNorm -
            secondParallel / secondNorm := by
      rw [inner_sub_left]
      exact congrArg₂ (· - ·)
        (wz1Lemma49_radial_inner
          firstVector parallel hfirstNormPos)
        (wz1Lemma49_radial_inner
          secondVector parallel hsecondNormPos)
    have hinner :
        |inner ℝ
            (wz1Lemma49RadialDirection viewpoint first -
              wz1Lemma49RadialDirection viewpoint second)
            parallel| ≤
          ‖wz1Lemma49RadialDirection viewpoint first -
            wz1Lemma49RadialDirection viewpoint second‖ := by
      calc
        |inner ℝ
            (wz1Lemma49RadialDirection viewpoint first -
              wz1Lemma49RadialDirection viewpoint second)
            parallel|
            ≤
          ‖wz1Lemma49RadialDirection viewpoint first -
              wz1Lemma49RadialDirection viewpoint second‖ *
            ‖parallel‖ := abs_real_inner_le_norm _ _
        _ =
          ‖wz1Lemma49RadialDirection viewpoint first -
            wz1Lemma49RadialDirection viewpoint second‖ := by
          rw [hdirection, mul_one]
    rw [heq] at hinner
    exact hinner.trans hangular
  have hnormDifference :
      |secondNorm - firstNorm| ≤
        2 * bound ^ 2 * angularRadius / side +
          2 * bound * width / side := by
    have hcross :
        |firstPerp * secondNorm -
            secondPerp * firstNorm| ≤
          angularRadius * firstNorm * secondNorm := by
      have heq :
          firstPerp * secondNorm -
              secondPerp * firstNorm =
            (firstPerp / firstNorm -
              secondPerp / secondNorm) *
                (firstNorm * secondNorm) := by
        field_simp [hfirstNormPos.ne', hsecondNormPos.ne']
      rw [heq, abs_mul, abs_of_nonneg (by positivity :
        0 ≤ firstNorm * secondNorm)]
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_right hangularPerp
          (mul_nonneg hfirstNormPos.le hsecondNormPos.le)
    have hidentity :
        firstPerp * secondNorm -
            secondPerp * firstNorm =
          perpDifference * secondNorm +
            secondPerp * (secondNorm - firstNorm) := by
      dsimp only [perpDifference]
      ring
    have hsecondPerpPositive : 0 < secondPerp := by
      linarith
    have hbound :
        secondPerp * |secondNorm - firstNorm| ≤
          angularRadius * firstNorm * secondNorm +
            width * secondNorm := by
      have htriangle :
          |secondPerp * (secondNorm - firstNorm)| ≤
            |firstPerp * secondNorm -
                secondPerp * firstNorm| +
              |perpDifference * secondNorm| := by
        have heq :
            secondPerp * (secondNorm - firstNorm) =
              (firstPerp * secondNorm -
                secondPerp * firstNorm) -
                perpDifference * secondNorm := by
          rw [hidentity]
          ring
        rw [heq]
        exact abs_sub _ _
      rw [abs_mul, abs_of_pos hsecondPerpPositive,
        abs_mul, abs_of_nonneg (by positivity : 0 ≤ secondNorm)]
        at htriangle
      calc
        secondPerp * |secondNorm - firstNorm|
            ≤
          |firstPerp * secondNorm -
              secondPerp * firstNorm| +
            |perpDifference| * secondNorm := htriangle
        _ ≤
          angularRadius * firstNorm * secondNorm +
            width * secondNorm := by
          gcongr
    calc
      |secondNorm - firstNorm|
          ≤
        (angularRadius * firstNorm * secondNorm +
          width * secondNorm) / secondPerp := by
        exact (le_div_iff₀ hsecondPerpPositive).2
          (by simpa [mul_comm] using hbound)
      _ ≤
        (angularRadius * bound * bound + width * bound) /
          (side / 2) := by
        gcongr
      _ =
        2 * bound ^ 2 * angularRadius / side +
          2 * bound * width / side := by
        field_simp [hside.ne'] <;> ring
  have hparallelDifference :
      |parallelDifference| ≤
        bound * angularRadius + |secondNorm - firstNorm| := by
    have hcross :
        |firstParallel * secondNorm -
            secondParallel * firstNorm| ≤
          angularRadius * firstNorm * secondNorm := by
      have heq :
          firstParallel * secondNorm -
              secondParallel * firstNorm =
            (firstParallel / firstNorm -
              secondParallel / secondNorm) *
                (firstNorm * secondNorm) := by
        field_simp [hfirstNormPos.ne', hsecondNormPos.ne']
      rw [heq, abs_mul, abs_of_nonneg (by positivity :
        0 ≤ firstNorm * secondNorm)]
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_right hangularParallel
          (mul_nonneg hfirstNormPos.le hsecondNormPos.le)
    have hidentity :
        firstParallel * secondNorm -
            secondParallel * firstNorm =
          firstParallel * (secondNorm - firstNorm) +
            parallelDifference * firstNorm := by
      dsimp only [parallelDifference]
      ring
    have hbound :
        |parallelDifference| * firstNorm ≤
          angularRadius * firstNorm * secondNorm +
            firstNorm * |secondNorm - firstNorm| := by
      have htriangle :
          |parallelDifference * firstNorm| ≤
            |firstParallel * secondNorm -
                secondParallel * firstNorm| +
              |firstParallel * (secondNorm - firstNorm)| := by
        have heq :
            parallelDifference * firstNorm =
              (firstParallel * secondNorm -
                secondParallel * firstNorm) -
                firstParallel * (secondNorm - firstNorm) := by
          rw [hidentity]
          ring
        rw [heq]
        exact abs_sub _ _
      have hfirstParallelBound : |firstParallel| ≤ firstNorm := by
        calc
          |firstParallel| ≤
              ‖firstVector‖ * ‖parallel‖ :=
            abs_real_inner_le_norm firstVector parallel
          _ = firstNorm := by rw [hdirection, mul_one]
      have htriangle' :
          |parallelDifference| * firstNorm ≤
            |firstParallel * secondNorm -
                secondParallel * firstNorm| +
              |firstParallel| * |secondNorm - firstNorm| := by
        simpa [abs_mul, abs_of_pos hfirstNormPos] using htriangle
      calc
        |parallelDifference| * firstNorm
            ≤
          |firstParallel * secondNorm -
              secondParallel * firstNorm| +
            |firstParallel| * |secondNorm - firstNorm| := htriangle'
        _ ≤
          angularRadius * firstNorm * secondNorm +
            firstNorm * |secondNorm - firstNorm| := by
          gcongr
    calc
      |parallelDifference|
          ≤
        (angularRadius * firstNorm * secondNorm +
            firstNorm * |secondNorm - firstNorm|) / firstNorm := by
        exact (le_div_iff₀ hfirstNormPos).2 hbound
      _ =
        angularRadius * secondNorm +
          |secondNorm - firstNorm| := by
        field_simp [hfirstNormPos.ne']
      _ ≤ bound * angularRadius + |secondNorm - firstNorm| := by
        have hmul :
            angularRadius * secondNorm ≤ angularRadius * bound :=
          mul_le_mul_of_nonneg_left hsecondNormUpper
            hangularRadius.le
        linarith
  have hparallelFinal :
      |parallelDifference| ≤
        bound * angularRadius +
          2 * bound ^ 2 * angularRadius / side +
          2 * bound * width / side := by
    linarith
  have hdecomposition :
      first - second =
        parallelDifference • parallel +
          perpDifference • perpendicular := by
    have h :=
      orthonormal_decomp (first - second) parallel hdirection
    have hparallel :
        parallelDifference =
          inner ℝ (first - second) parallel := by
      dsimp only [parallelDifference, firstParallel,
        secondParallel, firstVector, secondVector]
      rw [inner_sub_left, inner_sub_left, inner_sub_left]
      ring
    have hperp :
        perpDifference =
          inner ℝ (first - second) perpendicular := by
      dsimp only [perpDifference, firstPerp,
        secondPerp, firstVector, secondVector]
      rw [inner_sub_left, inner_sub_left, inner_sub_left]
      ring
    rw [hparallel, hperp]
    exact h
  have hnorm :
      ‖first - second‖ ≤
        |parallelDifference| + |perpDifference| := by
    rw [hdecomposition]
    calc
      ‖parallelDifference • parallel +
          perpDifference • perpendicular‖
          ≤
        ‖parallelDifference • parallel‖ +
          ‖perpDifference • perpendicular‖ := norm_add_le _ _
      _ =
        |parallelDifference| + |perpDifference| := by
        rw [norm_smul, norm_smul, hdirection,
          hperpendicularNorm, mul_one, mul_one]
        exact congrArg₂ (· + ·)
          (Real.norm_eq_abs parallelDifference)
          (Real.norm_eq_abs perpDifference)
  calc
    dist first second = ‖first - second‖ := by
      simp [dist_eq_norm]
    _ ≤ |parallelDifference| + |perpDifference| := hnorm
    _ ≤
      (bound * angularRadius +
          2 * bound ^ 2 * angularRadius / side +
          2 * bound * width / side) +
        width := by
      gcongr
    _ =
      bound * angularRadius +
        2 * bound ^ 2 * angularRadius / side +
        width + 2 * bound * width / side := by ring

/--
Unit-ball compatibility form of the bounded cone estimate.
-/
theorem wz1_lemma49_partial_cone_diameter
    {base direction viewpoint first second : Point2}
    {width side angularRadius : ℝ}
    (hdirection : ‖direction‖ = 1)
    (hwidth : 0 < width) (hside : 0 < side)
    (hfirstStrip :
      |inner ℝ (first - base) (wz1Perp2 direction)| ≤ width / 2)
    (hsecondStrip :
      |inner ℝ (second - base) (wz1Perp2 direction)| ≤ width / 2)
    (hfirstSide :
      side / 2 ≤
        inner ℝ (first - viewpoint) (wz1Perp2 direction))
    (hsecondSide :
      side / 2 ≤
        inner ℝ (second - viewpoint) (wz1Perp2 direction))
    (hangularRadius : 0 < angularRadius)
    (hangular :
      ‖wz1Lemma49RadialDirection viewpoint first -
          wz1Lemma49RadialDirection viewpoint second‖ ≤
        angularRadius)
    (hfirstBall : ‖first‖ ≤ 1)
    (hsecondBall : ‖second‖ ≤ 1)
    (hviewpointBall : ‖viewpoint‖ ≤ 1) :
    dist first second ≤
      2 * angularRadius +
        8 * angularRadius / side +
        width + 4 * width / side := by
  have hfirstBound : ‖first - viewpoint‖ ≤ 2 := by
    calc
      ‖first - viewpoint‖ ≤ ‖first‖ + ‖viewpoint‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by linarith
      _ = 2 := by norm_num
  have hsecondBound : ‖second - viewpoint‖ ≤ 2 := by
    calc
      ‖second - viewpoint‖ ≤ ‖second‖ + ‖viewpoint‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by linarith
      _ = 2 := by norm_num
  convert
    (wz1_lemma49_partial_cone_diameter_bounded
      hdirection hwidth hside (by norm_num : (0 : ℝ) < 2)
      hfirstStrip hsecondStrip hfirstSide hsecondSide
      hangularRadius hangular hfirstBound hsecondBound) using 1 <;>
    norm_num

end

end Kakeya.Assouad
