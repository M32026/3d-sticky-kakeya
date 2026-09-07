import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12

/-!
# Projective direction triangle

If a common unit direction is transversely close to two unit directions, then
the latter are projectively close.  This isolated geometric leaf avoids the
unrelated large shifted-copy module that historically contained the same
argument.
-/

noncomputable section

namespace Kakeya.Assouad

private theorem pureWZ2_orthogonal_projection_norm_le
    {vector direction : Point3}
    (hdirection : ‖direction‖ = 1) :
    ‖vector - inner ℝ vector direction • direction‖ ≤
      ‖vector‖ := by
  let coefficient := inner ℝ vector direction
  have hnorm :
      ‖vector - coefficient • direction‖ ^ 2 =
        ‖vector‖ ^ 2 - coefficient ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right,
      norm_smul, hdirection]
    simp [coefficient, Real.norm_eq_abs, sq_abs]
    ring
  have hsquared :
      ‖vector - coefficient • direction‖ ^ 2 ≤
        ‖vector‖ ^ 2 := by
    rw [hnorm]
    exact sub_le_self _ (sq_nonneg coefficient)
  nlinarith [
    norm_nonneg vector,
    norm_nonneg (vector - coefficient • direction)]

/--
Projective triangle inequality in transverse-component form.
-/
theorem pureWZ2_projective_direction_triangle
    {first second common : Point3}
    (hfirst : ‖first‖ = 1)
    (hsecond : ‖second‖ = 1)
    (hcommon : ‖common‖ = 1)
    {error : ℝ}
    (herror : 0 ≤ error)
    (herrorSmall : error ≤ 1 / 2)
    (hcommonFirst :
      ‖common -
          inner ℝ common first • first‖ ≤ error)
    (hcommonSecond :
      ‖common -
          inner ℝ common second • second‖ ≤ error) :
    ‖second -
        inner ℝ second first • first‖ ≤
      4 * error := by
  let firstCoefficient := inner ℝ common first
  let secondCoefficient := inner ℝ common second
  let mutualCoefficient := inner ℝ second first
  let commonPerpFirst :=
    common - firstCoefficient • first
  let commonPerpSecond :=
    common - secondCoefficient • second
  let secondPerpFirst :=
    second - mutualCoefficient • first
  have hperpFirst :
      ‖commonPerpFirst‖ ≤ error :=
    hcommonFirst
  have hperpSecond :
      ‖commonPerpSecond‖ ≤ error :=
    hcommonSecond
  have hinner :
      inner ℝ commonPerpSecond first =
        firstCoefficient -
          secondCoefficient * mutualCoefficient := by
    dsimp only [commonPerpSecond, firstCoefficient,
      secondCoefficient, mutualCoefficient]
    rw [inner_sub_left, real_inner_smul_left]
  have hidentity :
      secondCoefficient • secondPerpFirst =
        commonPerpFirst -
          (commonPerpSecond -
            inner ℝ commonPerpSecond first • first) := by
    have hcommonFirstIdentity :
        common =
          firstCoefficient • first + commonPerpFirst := by
      dsimp only [commonPerpFirst]
      abel
    have hcommonSecondIdentity :
        common =
          secondCoefficient • second + commonPerpSecond := by
      dsimp only [commonPerpSecond]
      abel
    have hsecondIdentity :
        second =
          mutualCoefficient • first + secondPerpFirst := by
      dsimp only [secondPerpFirst]
      abel
    have hscaledSecond :
        secondCoefficient • second =
          (secondCoefficient * mutualCoefficient) • first +
            secondCoefficient • secondPerpFirst := by
      rw [hsecondIdentity, smul_add, smul_smul]
    have hcommonComparison :
        firstCoefficient • first + commonPerpFirst =
          secondCoefficient • second + commonPerpSecond := by
      rw [← hcommonFirstIdentity, ← hcommonSecondIdentity]
    rw [hscaledSecond] at hcommonComparison
    rw [hinner]
    module
  have hprojectedSecond :
      ‖commonPerpSecond -
          inner ℝ commonPerpSecond first • first‖ ≤
        ‖commonPerpSecond‖ :=
    pureWZ2_orthogonal_projection_norm_le hfirst
  have hscaled :
      ‖secondCoefficient • secondPerpFirst‖ ≤
        2 * error := by
    rw [hidentity]
    exact
      (norm_sub_le _ _).trans
        (by linarith [hperpFirst, hperpSecond,
          hprojectedSecond])
  have hsecondCoefficientSq :
      secondCoefficient ^ 2 ≥
        1 - error ^ 2 := by
    have hnorm :
        ‖commonPerpSecond‖ ^ 2 =
          1 - secondCoefficient ^ 2 := by
      dsimp only [commonPerpSecond, secondCoefficient]
      rw [norm_sub_sq_real, inner_smul_right,
        norm_smul, hcommon, hsecond]
      simp [Real.norm_eq_abs, sq_abs]
      ring
    have hsquared :
        ‖commonPerpSecond‖ ^ 2 ≤ error ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) herror).mpr
        hperpSecond
    linarith
  have habsCoefficient :
      1 / 2 ≤ |secondCoefficient| := by
    have hsquared :
        (1 / 2 : ℝ) ^ 2 ≤ secondCoefficient ^ 2 := by
      nlinarith
    nlinarith [sq_abs secondCoefficient,
      abs_nonneg secondCoefficient]
  have hcoefficientPositive :
      0 < |secondCoefficient| := by linarith
  have hnormScaled :
      ‖secondCoefficient • secondPerpFirst‖ =
        |secondCoefficient| * ‖secondPerpFirst‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have hdivide :
      ‖secondPerpFirst‖ ≤
        (2 * error) / |secondCoefficient| := by
    rw [hnormScaled] at hscaled
    exact
      (le_div_iff₀ hcoefficientPositive).mpr
        (by simpa [mul_comm] using hscaled)
  have hfinal :
      (2 * error) / |secondCoefficient| ≤
        4 * error := by
    have hnonnegative : 0 ≤ 2 * error := by positivity
    calc
      (2 * error) / |secondCoefficient|
          ≤ (2 * error) / (1 / 2 : ℝ) := by
        exact
          div_le_div_of_nonneg_left hnonnegative
            (by norm_num) habsCoefficient
      _ = 4 * error := by ring
  exact hdivide.trans hfinal

end Kakeya.Assouad

end
