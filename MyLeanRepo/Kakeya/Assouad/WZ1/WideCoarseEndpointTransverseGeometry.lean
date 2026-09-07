import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseAffineMaps

/-!
# Transverse exact-pullback geometry for endpoint line synthesis
-/

namespace Kakeya.Assouad

/-- A large perpendicular-frame coefficient gives the exact `1 / width`
lower bound on the strip-normal pullback. -/
lemma wideCoarseEndpoint_transverse_pullback_norm_lower
    {direction normal : Point2} {width : ℝ}
    (hwidth : 0 < width)
    (hdirection : ‖direction‖ = 1)
    (hcoefficient :
      1 / 2 ≤
        |inner ℝ normal (wz1Perp2 direction)|) :
    1 / (2 * width) ≤
      ‖wideCoarsePhiGPullbackVector direction width normal‖ := by
  have hpullbackSquare :=
    wideCoarsePhiGPullbackVector_norm_sq
      (w := width) (normal := normal) hdirection
  have hcoefficientScaled :
      1 / (2 * width) ≤
        |inner ℝ normal (wz1Perp2 direction) / width| := by
    rw [abs_div, abs_of_pos hwidth]
    calc
      1 / (2 * width) = (1 / 2 : ℝ) / width := by ring
      _ ≤ |inner ℝ normal (wz1Perp2 direction)| / width :=
        div_le_div_of_nonneg_right hcoefficient hwidth.le
  have hnonnegative :
      0 ≤ ‖wideCoarsePhiGPullbackVector direction width normal‖ :=
    norm_nonneg _
  have hsquareCoefficient :
      (1 / (2 * width)) ^ 2 ≤
        (inner ℝ normal (wz1Perp2 direction) / width) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_pos hwidth] using hcoefficientScaled
  have hsquarePullback :
      (1 / (2 * width)) ^ 2 ≤
        ‖wideCoarsePhiGPullbackVector direction width normal‖ ^ 2 := by
    rw [hpullbackSquare]
    exact hsquareCoefficient.trans
      (le_add_of_nonneg_left (sq_nonneg _))
  exact
    (sq_le_sq₀ (by positivity) hnonnegative).1 hsquarePullback

/-- In the transverse coefficient regime, enlarging the exact source radius
to the source cutoff `delta` still costs at most `4 * width * radius`. -/
lemma wideCoarseEndpoint_transverse_rawRadius_upper
    {direction normal : Point2}
    {delta width radius : ℝ}
    (hdelta : 0 < delta)
    (hwidth : 0 < width)
    (hradius : delta / width ≤ radius)
    (hdirection : ‖direction‖ = 1)
    (hcoefficient :
      1 / 2 ≤
        |inner ℝ normal (wz1Perp2 direction)|) :
    max delta
        ((radius + delta / width) /
          ‖wideCoarsePhiGPullbackVector direction width normal‖) ≤
      4 * width * radius := by
  have hpullbackLower :=
    wideCoarseEndpoint_transverse_pullback_norm_lower
      hwidth hdirection hcoefficient
  have hpullbackPos :
      0 <
        ‖wideCoarsePhiGPullbackVector direction width normal‖ := by
    have hleft : 0 < 1 / (2 * width) := by positivity
    exact hleft.trans_le hpullbackLower
  have hradiusNonnegative : 0 ≤ radius := by
    exact (div_pos hdelta hwidth).le.trans hradius
  have hdeltaWidth :
      delta ≤ width * radius := by
    have h := (div_le_iff₀ hwidth).1 hradius
    simpa [mul_comm] using h
  have hsourceRadius :
      (radius + delta / width) /
          ‖wideCoarsePhiGPullbackVector direction width normal‖ ≤
        4 * width * radius := by
    have hinverseBound :
        1 /
            ‖wideCoarsePhiGPullbackVector direction width normal‖ ≤
          2 * width := by
      have hleft : 0 < 1 / (2 * width) := by positivity
      have hinverse :=
        (one_div_le_one_div_of_le hleft hpullbackLower)
      have hsimplify :
          1 / (1 / (2 * width)) = 2 * width := by
        field_simp [hwidth.ne']
      simpa [hsimplify] using hinverse
    calc
      (radius + delta / width) /
            ‖wideCoarsePhiGPullbackVector direction width normal‖ =
          (radius + delta / width) *
            (1 /
              ‖wideCoarsePhiGPullbackVector direction width normal‖) := by
            rw [div_eq_mul_inv, one_div]
      _ ≤
          (radius + delta / width) * (2 * width) := by
            exact mul_le_mul_of_nonneg_left
              hinverseBound
              (add_nonneg hradiusNonnegative
                (div_pos hdelta hwidth).le)
      _ ≤ 4 * width * radius := by
        have hdeltaRatio : delta / width ≤ radius := hradius
        nlinarith
  apply max_le
  · calc
      delta ≤ width * radius := hdeltaWidth
      _ ≤ 4 * width * radius := by
        have hproduct : 0 ≤ width * radius :=
          mul_nonneg hwidth.le hradiusNonnegative
        nlinarith
  · exact hsourceRadius

end Kakeya.Assouad
