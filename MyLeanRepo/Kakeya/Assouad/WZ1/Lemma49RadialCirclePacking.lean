import MyLeanRepo.Kakeya.Assouad.WZ1.AngleGeometryBase
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LipschitzGraphFrostman

/-!
# Unit-circle cap packing for WZ1 Lemma 49

The radial image in the residual Kaufman branch lies on the unit circle.
Inside a ball of radius at most `1/2`, the tangential coordinate is bounded
by the cap radius and separates distinct radial directions up to the absolute
factor `sqrt 3 / 2`.  The resulting one-dimensional packing estimate is the
geometric input used to transfer Frostman control through radial projection.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Squared norm in the frame `(direction, perp direction)`. -/
private lemma wz1Lemma49_circle_coordinates_sq
    (point direction : Point2) (hdirection : ‖direction‖ = 1) :
    (inner ℝ point direction) ^ 2 +
        (inner ℝ point (wz1Perp2 direction)) ^ 2 =
      ‖point‖ ^ 2 := by
  have h :=
    norm_cross_identity point direction hdirection
  have hcross :
      cross2 point direction =
        -inner ℝ point (wz1Perp2 direction) := by
    simp [cross2, wz1Perp2, inner2_eq]
    ring
  rw [hcross] at h
  nlinarith

/--
On the upper half of the unit circle with parallel coordinate at least
`sqrt 3 / 2`, tangential displacement controls Euclidean displacement.
-/
private lemma wz1Lemma49_upper_circle_tangent_separation
    {first second direction : Point2}
    (hdirection : ‖direction‖ = 1)
    (hfirstUnit : ‖first‖ = 1)
    (hsecondUnit : ‖second‖ = 1)
    (hfirstParallel :
      Real.sqrt 3 / 2 ≤ inner ℝ first direction)
    (hsecondParallel :
      Real.sqrt 3 / 2 ≤ inner ℝ second direction) :
    (Real.sqrt 3 / 2) * dist first second ≤
      |inner ℝ first (wz1Perp2 direction) -
        inner ℝ second (wz1Perp2 direction)| := by
  let firstParallel := inner ℝ first direction
  let secondParallel := inner ℝ second direction
  let firstTangent := inner ℝ first (wz1Perp2 direction)
  let secondTangent := inner ℝ second (wz1Perp2 direction)
  have hfirstCoords :
      firstParallel ^ 2 + firstTangent ^ 2 = 1 := by
    have h :=
      wz1Lemma49_circle_coordinates_sq first direction hdirection
    rw [hfirstUnit] at h
    simpa [firstParallel, firstTangent] using h
  have hsecondCoords :
      secondParallel ^ 2 + secondTangent ^ 2 = 1 := by
    have h :=
      wz1Lemma49_circle_coordinates_sq second direction hdirection
    rw [hsecondUnit] at h
    simpa [secondParallel, secondTangent] using h
  have hfirstTangent :
      |firstTangent| ≤ 1 / 2 := by
    have hsqrt : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    have hparallelSq :
        3 / 4 ≤ firstParallel ^ 2 := by
      rw [← hsqrt]
      exact pow_le_pow_left₀
        (by positivity)
        hfirstParallel 2
    have htangentSq : firstTangent ^ 2 ≤ 1 / 4 := by
      nlinarith
    rw [show firstTangent ^ 2 = |firstTangent| ^ 2 by
      rw [sq_abs]] at htangentSq
    nlinarith [abs_nonneg firstTangent]
  have hsecondTangent :
      |secondTangent| ≤ 1 / 2 := by
    have hsqrt : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    have hparallelSq :
        3 / 4 ≤ secondParallel ^ 2 := by
      rw [← hsqrt]
      exact pow_le_pow_left₀
        (by positivity)
        hsecondParallel 2
    have htangentSq : secondTangent ^ 2 ≤ 1 / 4 := by
      nlinarith
    rw [show secondTangent ^ 2 = |secondTangent| ^ 2 by
      rw [sq_abs]] at htangentSq
    nlinarith [abs_nonneg secondTangent]
  have hparallelDifference :
      |firstParallel - secondParallel| ≤
        |firstTangent - secondTangent| / Real.sqrt 3 := by
    have hfactor :
        (firstParallel - secondParallel) *
            (firstParallel + secondParallel) =
          (secondTangent - firstTangent) *
            (secondTangent + firstTangent) := by
      nlinarith
    have hparallelSum :
        Real.sqrt 3 ≤ firstParallel + secondParallel := by
      linarith
    have hparallelSumNonneg :
        0 ≤ firstParallel + secondParallel := by
      linarith [Real.sqrt_nonneg 3]
    have htangentSum :
        |secondTangent + firstTangent| ≤ 1 := by
      exact (abs_add_le _ _).trans (by linarith)
    have habsFactor :
        |firstParallel - secondParallel| *
            (firstParallel + secondParallel) =
          |secondTangent - firstTangent| *
            |secondTangent + firstTangent| := by
      have hleft :
          |(firstParallel - secondParallel) *
              (firstParallel + secondParallel)| =
            |firstParallel - secondParallel| *
              (firstParallel + secondParallel) := by
        rw [abs_mul, abs_of_nonneg hparallelSumNonneg]
      have hright :
          |(secondTangent - firstTangent) *
              (secondTangent + firstTangent)| =
            |secondTangent - firstTangent| *
              |secondTangent + firstTangent| := by
        rw [abs_mul]
      rw [← hleft, hfactor, hright]
    have hscaled :
        |firstParallel - secondParallel| * Real.sqrt 3 ≤
          |firstTangent - secondTangent| := by
      calc
        |firstParallel - secondParallel| * Real.sqrt 3
            ≤
          |firstParallel - secondParallel| *
            (firstParallel + secondParallel) := by
          gcongr
        _ =
          |secondTangent - firstTangent| *
            |secondTangent + firstTangent| := habsFactor
        _ ≤ |secondTangent - firstTangent| * 1 := by
          gcongr
        _ = |firstTangent - secondTangent| := by
          rw [abs_sub_comm]
          ring
    exact (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))).2
      hscaled
  have hdistanceSq :
      dist first second ^ 2 =
        (firstParallel - secondParallel) ^ 2 +
          (firstTangent - secondTangent) ^ 2 := by
    have h :=
      wz1Lemma49_circle_coordinates_sq
        (first - second) direction hdirection
    rw [inner_sub_left, inner_sub_left] at h
    simpa [dist_eq_norm, firstParallel, secondParallel,
      firstTangent, secondTangent] using h.symm
  have hparallelSq :
      (firstParallel - secondParallel) ^ 2 ≤
        (1 / 3 : ℝ) *
          (firstTangent - secondTangent) ^ 2 := by
    have hsqrt : 0 < Real.sqrt 3 :=
      Real.sqrt_pos.mpr (by norm_num)
    have hsquare :
        |firstParallel - secondParallel| ^ 2 ≤
          (|firstTangent - secondTangent| / Real.sqrt 3) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hparallelDifference 2
    have hrewrite :
        (|firstTangent - secondTangent| / Real.sqrt 3) ^ 2 =
          (1 / 3 : ℝ) *
            (firstTangent - secondTangent) ^ 2 := by
      rw [div_pow, sq_abs, Real.sq_sqrt (by norm_num)]
      ring
    rw [show |firstParallel - secondParallel| ^ 2 =
        (firstParallel - secondParallel) ^ 2 by rw [sq_abs],
      hrewrite] at hsquare
    exact hsquare
  have hdistanceBound :
      dist first second ^ 2 ≤
        (4 / 3 : ℝ) *
          (firstTangent - secondTangent) ^ 2 := by
    rw [hdistanceSq]
    linarith
  have htargetSq :
      ((Real.sqrt 3 / 2) * dist first second) ^ 2 ≤
        |firstTangent - secondTangent| ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num),
      sq_abs]
    nlinarith
  nlinarith [Real.sqrt_nonneg 3,
    (dist_nonneg : 0 ≤ dist first second),
    abs_nonneg (firstTangent - secondTangent)]

/--
The tangential coordinate of a unit vector in a radius-`r` cap, `r ≤ 1/2`,
lies in `[-r,r]`.
-/
private lemma wz1Lemma49_unit_cap_tangent_bound
    {point center direction : Point2} {r : ℝ}
    (hr : 0 < r) (hrHalf : r ≤ 1 / 2)
    (hpointUnit : ‖point‖ = 1)
    (hcenter : center ≠ 0)
    (hpointCenter : dist point center ≤ r)
    (hdirection :
      direction = (‖center‖⁻¹ : ℝ) • center) :
    |inner ℝ point (wz1Perp2 direction)| ≤ r ∧
      Real.sqrt 3 / 2 ≤ inner ℝ point direction := by
  have hcenterNorm : 0 < ‖center‖ :=
    norm_pos_iff.mpr hcenter
  have hdirectionUnit : ‖direction‖ = 1 := by
    rw [hdirection, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hcenterNorm)]
    field_simp [hcenterNorm.ne']
  have hcenterEq : ‖center‖ • direction = center := by
    rw [hdirection, smul_smul]
    field_simp [hcenterNorm.ne']
    simp
  let parallel := inner ℝ point direction
  let tangent := inner ℝ point (wz1Perp2 direction)
  have hdistance :
      ‖point - center‖ ^ 2 ≤ r ^ 2 := by
    have hnorm : ‖point - center‖ ≤ r := by
      simpa [dist_eq_norm] using hpointCenter
    nlinarith [norm_nonneg (point - center)]
  have hdistanceFormula :
      ‖point - center‖ ^ 2 =
        1 + ‖center‖ ^ 2 - 2 * ‖center‖ * parallel := by
    rw [← hcenterEq, norm_sub_sq_real,
      hpointUnit, norm_smul, hdirectionUnit,
      real_inner_smul_right]
    simp [parallel, Real.norm_eq_abs,
      abs_of_pos hcenterNorm]
    ring
  have hrSquare : 0 ≤ 1 - r ^ 2 := by
    nlinarith
  have hparallelRoot :
      Real.sqrt (1 - r ^ 2) ≤ parallel := by
    have hnumerator :
        2 * ‖center‖ * Real.sqrt (1 - r ^ 2) ≤
          1 + ‖center‖ ^ 2 - r ^ 2 := by
      nlinarith [Real.sq_sqrt hrSquare,
        sq_nonneg (‖center‖ - Real.sqrt (1 - r ^ 2))]
    rw [hdistanceFormula] at hdistance
    nlinarith
  have hcoords :
      parallel ^ 2 + tangent ^ 2 = 1 := by
    have h :=
      wz1Lemma49_circle_coordinates_sq point direction hdirectionUnit
    rw [hpointUnit] at h
    simpa [parallel, tangent] using h
  have hparallelSq : 1 - r ^ 2 ≤ parallel ^ 2 := by
    have hsqrtNonneg := Real.sqrt_nonneg (1 - r ^ 2)
    nlinarith [Real.sq_sqrt hrSquare]
  have htangentSq : tangent ^ 2 ≤ r ^ 2 := by
    nlinarith
  have htangent : |tangent| ≤ r := by
    rw [show tangent ^ 2 = |tangent| ^ 2 by rw [sq_abs]]
      at htangentSq
    nlinarith [abs_nonneg tangent]
  have hrootThree :
      Real.sqrt 3 / 2 ≤ Real.sqrt (1 - r ^ 2) := by
    have hbase : 3 / 4 ≤ 1 - r ^ 2 := by
      nlinarith
    have hsqrt :=
      Real.sqrt_le_sqrt hbase
    have heq : Real.sqrt (3 / 4) = Real.sqrt 3 / 2 := by
      rw [Real.sqrt_div (by norm_num)]
      have hsqrtFour : Real.sqrt 4 = 2 := by
        rw [Real.sqrt_eq_cases] <;> norm_num
      rw [hsqrtFour]
    rw [heq] at hsqrt
    exact hsqrt
  exact ⟨htangent, hrootThree.trans hparallelRoot⟩

/--
A delta-separated finite subset of the unit circle has at most
`(4 / sqrt 3 + 1) * r / delta` points in a radius-`r` cap for
`delta ≤ r ≤ 1/2`.
-/
theorem wz1_lemma49_unit_circle_cap_packing
    {directions : DiscreteSet 2}
    {delta r : ℝ} {center : Point2}
    (hdelta : 0 < delta) (hr : 0 < r) (hrHalf : r ≤ 1 / 2)
    (hunit : ∀ direction ∈ directions, ‖direction‖ = 1)
    (hseparated : directions.IsDeltaSeparated delta)
    (hdeltaR : delta ≤ r) :
    ((directions.filter fun direction =>
        dist direction center ≤ r).card : ℝ) ≤
      (4 / Real.sqrt 3 + 1) * r / delta := by
  let cap :=
    directions.filter fun direction =>
      dist direction center ≤ r
  change (cap.card : ℝ) ≤
    (4 / Real.sqrt 3 + 1) * r / delta
  by_cases hcapEmpty : cap = ∅
  · rw [hcapEmpty]
    simp
    positivity
  have hcapNonempty : cap.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hcapEmpty
  have hcenter : center ≠ 0 := by
    intro hzero
    rcases hcapNonempty with ⟨direction, hdirection⟩
    have hdirectionMem :=
      (Finset.mem_filter.mp hdirection).1
    have hdist :=
      (Finset.mem_filter.mp hdirection).2
    rw [hzero] at hdist
    have hnorm := hunit direction hdirectionMem
    have hone : (1 : ℝ) ≤ r := by
      simpa [dist_zero_right, hnorm] using hdist
    linarith
  let axis : Point2 := (‖center‖⁻¹ : ℝ) • center
  have haxisUnit : ‖axis‖ = 1 := by
    have hcenterNorm : 0 < ‖center‖ :=
      norm_pos_iff.mpr hcenter
    change ‖(‖center‖⁻¹ : ℝ) • center‖ = 1
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hcenterNorm)]
    field_simp [hcenterNorm.ne']
  let tangent := wz1Perp2 axis
  let coordinate : Point2 → ℝ :=
    fun direction => inner ℝ direction tangent
  let values : Finset ℝ := cap.image coordinate
  have hcapBounds :
      ∀ direction ∈ cap,
        |coordinate direction| ≤ r ∧
          Real.sqrt 3 / 2 ≤ inner ℝ direction axis := by
    intro direction hdirection
    exact
      wz1Lemma49_unit_cap_tangent_bound
        hr hrHalf
        (hunit direction (Finset.mem_filter.mp hdirection).1)
        hcenter (Finset.mem_filter.mp hdirection).2 rfl
  have hcoordinateSeparated :
      ∀ first ∈ cap, ∀ second ∈ cap, first ≠ second →
        (Real.sqrt 3 / 2) * delta ≤
          |coordinate first - coordinate second| := by
    intro first hfirst second hsecond hne
    have hdist :=
      hseparated
        (Finset.mem_filter.mp hfirst).1
        (Finset.mem_filter.mp hsecond).1 hne
    have htangent :=
      wz1Lemma49_upper_circle_tangent_separation
        haxisUnit
        (hunit first (Finset.mem_filter.mp hfirst).1)
        (hunit second (Finset.mem_filter.mp hsecond).1)
        (hcapBounds first hfirst).2
        (hcapBounds second hsecond).2
    calc
      (Real.sqrt 3 / 2) * delta
          ≤ (Real.sqrt 3 / 2) * dist first second := by
        gcongr
      _ ≤ |coordinate first - coordinate second| := by
        simpa [coordinate, tangent] using htangent
  have hcoordinateInjective :
      Set.InjOn coordinate (cap : Set Point2) := by
    intro first hfirst second hsecond heq
    by_contra hne
    have hsep :=
      hcoordinateSeparated first hfirst second hsecond hne
    rw [heq, sub_self, abs_zero] at hsep
    have hpositive :
        0 < (Real.sqrt 3 / 2) * delta := by
      positivity
    linarith
  have hvaluesCard : values.card = cap.card :=
    Finset.card_image_of_injOn hcoordinateInjective
  have hvaluesNonempty : values.Nonempty :=
    hcapNonempty.image coordinate
  have hvaluesBounds :
      ∀ value ∈ values, -r ≤ value ∧ value ≤ r := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with
      ⟨direction, hdirection, rfl⟩
    exact abs_le.mp (hcapBounds direction hdirection).1
  have hvaluesSeparated :
      ∀ first ∈ values, ∀ second ∈ values, first ≠ second →
        (Real.sqrt 3 / 2) * delta ≤ |first - second| := by
    intro first hfirst second hsecond hne
    rcases Finset.mem_image.mp hfirst with
      ⟨firstDirection, hfirstDirection, rfl⟩
    rcases Finset.mem_image.mp hsecond with
      ⟨secondDirection, hsecondDirection, rfl⟩
    have hneDirections : firstDirection ≠ secondDirection := by
      intro heq
      subst secondDirection
      exact hne rfl
    exact hcoordinateSeparated
      firstDirection hfirstDirection
      secondDirection hsecondDirection hneDirections
  have hpacking :=
    lemma23_separated_real_finset_card_le
      (d := (Real.sqrt 3 / 2) * delta)
      (a := -r) (b := r)
      (by positivity) hvaluesNonempty
      hvaluesBounds hvaluesSeparated
  rw [hvaluesCard] at hpacking
  calc
    (cap.card : ℝ)
        ≤ (r - -r) / ((Real.sqrt 3 / 2) * delta) + 1 :=
      hpacking
    _ = (4 / Real.sqrt 3) * r / delta + 1 := by
      field_simp [hdelta.ne',
        (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne']
      ring
    _ ≤
        (4 / Real.sqrt 3) * r / delta + r / delta := by
      have hone : 1 ≤ r / delta :=
        (le_div_iff₀ hdelta).2 (by simpa using hdeltaR)
      linarith
    _ = (4 / Real.sqrt 3 + 1) * r / delta := by
      ring

end

end Kakeya.Assouad
