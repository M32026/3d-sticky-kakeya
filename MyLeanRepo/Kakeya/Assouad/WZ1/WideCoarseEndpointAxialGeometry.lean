import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointTransverseGeometry

/-!
# Exact axial pullback geometry for endpoint line synthesis
-/

namespace Kakeya.Assouad

/-- Choose the representative of a projective normal whose inner product
with a reference normal is nonnegative. -/
noncomputable def wideCoarseEndpointSignedNormal
    (reference normal : Point2) : Point2 :=
  if 0 ≤ inner ℝ reference normal then normal else -normal

/-- Negate the strip level exactly when its normal is negated. -/
noncomputable def wideCoarseEndpointSignedLevel
    (reference normal : Point2) (level : ℝ) : ℝ :=
  if 0 ≤ inner ℝ reference normal then level else -level

/-- Signing a unit normal preserves unit norm. -/
lemma wideCoarseEndpoint_signedNormal_unit
    {reference normal : Point2}
    (hnormal : ‖normal‖ = 1) :
    ‖wideCoarseEndpointSignedNormal reference normal‖ = 1 := by
  by_cases hsign : 0 ≤ inner ℝ reference normal
  · simp [wideCoarseEndpointSignedNormal, hsign, hnormal]
  · simp [wideCoarseEndpointSignedNormal, hsign, hnormal]

/-- The signed representative has the absolute projective inner product. -/
lemma wideCoarseEndpoint_inner_signedNormal
    (reference normal : Point2) :
    inner ℝ reference
        (wideCoarseEndpointSignedNormal reference normal) =
      |inner ℝ reference normal| := by
  by_cases hsign : 0 ≤ inner ℝ reference normal
  · simp [wideCoarseEndpointSignedNormal, hsign,
      abs_of_nonneg hsign]
  · have hnegative : inner ℝ reference normal < 0 := by
      linarith
    simp [wideCoarseEndpointSignedNormal, hsign,
      inner_neg_right, abs_of_neg hnegative]

/-- Simultaneously signing a strip normal and level leaves its absolute
strip functional unchanged. -/
lemma wideCoarseEndpoint_signed_strip_eq
    (reference normal point : Point2) (level : ℝ) :
    |inner ℝ point
        (wideCoarseEndpointSignedNormal reference normal) -
        wideCoarseEndpointSignedLevel reference normal level| =
      |inner ℝ point normal - level| := by
  by_cases hsign : 0 ≤ inner ℝ reference normal
  · simp [wideCoarseEndpointSignedNormal,
      wideCoarseEndpointSignedLevel, hsign]
  · rw [wideCoarseEndpointSignedNormal,
      wideCoarseEndpointSignedLevel,
      if_neg hsign, if_neg hsign, inner_neg_right]
    have heq :
        -inner ℝ point normal - -level =
          -(inner ℝ point normal - level) := by ring
    rw [heq, abs_neg]

/-- Any two unit normals with nonnegative inner product are at distance at
most `sqrt 2`. -/
lemma wideCoarseEndpoint_signedNormal_dist_upper
    {reference normal : Point2}
    (href : ‖reference‖ = 1)
    (hnormal : ‖normal‖ = 1) :
    ‖reference -
        wideCoarseEndpointSignedNormal reference normal‖ ≤
      Real.sqrt 2 := by
  have hsignedUnit :=
    wideCoarseEndpoint_signedNormal_unit
      (reference := reference) hnormal
  have hinnerNonnegative :
      0 ≤
        inner ℝ reference
          (wideCoarseEndpointSignedNormal reference normal) := by
    rw [wideCoarseEndpoint_inner_signedNormal]
    exact abs_nonneg _
  have hdiff :=
    unit_diff_sq reference
      (wideCoarseEndpointSignedNormal reference normal)
      href hsignedUnit
  have hsqrtNonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrtSquare : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  nlinarith [norm_nonneg
    (reference -
      wideCoarseEndpointSignedNormal reference normal)]

/-- If the projective inner product is at most `1/2`, the signed unit
representative is at distance at least one from the reference normal. -/
lemma wideCoarseEndpoint_signedNormal_dist_lower
    {reference normal : Point2}
    (href : ‖reference‖ = 1)
    (hnormal : ‖normal‖ = 1)
    (hinner : |inner ℝ reference normal| ≤ 1 / 2) :
    1 ≤
      ‖reference -
        wideCoarseEndpointSignedNormal reference normal‖ := by
  have hsignedUnit :=
    wideCoarseEndpoint_signedNormal_unit
      (reference := reference) hnormal
  have hinnerSigned :
      inner ℝ reference
          (wideCoarseEndpointSignedNormal reference normal) ≤
        1 / 2 := by
    rw [wideCoarseEndpoint_inner_signedNormal]
    exact hinner
  have hdiff :=
    unit_diff_sq reference
      (wideCoarseEndpointSignedNormal reference normal)
      href hsignedUnit
  nlinarith [norm_nonneg
    (reference -
      wideCoarseEndpointSignedNormal reference normal)]

/-- A unit coarse normal with perpendicular-frame coefficient below `1 / 2`
has a uniformly large coefficient parallel to the common strip. -/
lemma wideCoarseEndpoint_axial_parallel_lower
    {direction normal : Point2}
    (hdirection : ‖direction‖ = 1)
    (hnormal : ‖normal‖ = 1)
    (haxial :
      |inner ℝ normal (wz1Perp2 direction)| < 1 / 2) :
    3 / 4 < |inner ℝ normal direction| := by
  have hpullbackAtOne :
      wideCoarsePhiGPullbackVector direction 1 normal = normal := by
    rw [wideCoarsePhiGPullbackVector]
    simpa using
      (orthonormal_decomp normal direction hdirection).symm
  have hframe :=
    wideCoarsePhiGPullbackVector_norm_sq
      (w := (1 : ℝ)) (normal := normal) hdirection
  rw [hpullbackAtOne, hnormal] at hframe
  norm_num at hframe
  have hperpendicularSquare :
      (inner ℝ normal (wz1Perp2 direction)) ^ 2 < 1 / 4 := by
    have habsSquare :
        |inner ℝ normal (wz1Perp2 direction)| ^ 2 <
          (1 / 2 : ℝ) ^ 2 := by
      nlinarith [abs_nonneg
        (inner ℝ normal (wz1Perp2 direction))]
    norm_num [sq_abs] at habsSquare ⊢
    exact habsSquare
  have hparallelSquare :
      3 / 4 <
        (inner ℝ normal direction) ^ 2 := by
    nlinarith
  have habsParallelNonnegative :
      0 ≤ |inner ℝ normal direction| :=
    abs_nonneg _
  rw [← sq_abs] at hparallelSquare
  nlinarith

/-- The pullback norm dominates its parallel-frame coefficient. -/
lemma wideCoarseEndpoint_pullback_norm_ge_parallel
    {direction normal : Point2} {width : ℝ}
    (hdirection : ‖direction‖ = 1) :
    |inner ℝ normal direction| ≤
      ‖wideCoarsePhiGPullbackVector direction width normal‖ := by
  have hpullbackSquare :=
    wideCoarsePhiGPullbackVector_norm_sq
      (w := width) (normal := normal) hdirection
  have hsquare :
      |inner ℝ normal direction| ^ 2 ≤
        ‖wideCoarsePhiGPullbackVector direction width normal‖ ^ 2 := by
    rw [hpullbackSquare, sq_abs]
    exact le_add_of_nonneg_right (sq_nonneg _)
  exact
    (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).1 hsquare

/-- The pullback norm dominates the perpendicular-frame coefficient divided
by the common-strip width. -/
lemma wideCoarseEndpoint_pullback_norm_ge_scaled_perp
    {direction normal : Point2} {width : ℝ}
    (hwidth : 0 < width)
    (hdirection : ‖direction‖ = 1) :
    |inner ℝ normal (wz1Perp2 direction)| / width ≤
      ‖wideCoarsePhiGPullbackVector direction width normal‖ := by
  have hpullbackSquare :=
    wideCoarsePhiGPullbackVector_norm_sq
      (w := width) (normal := normal) hdirection
  have hscaledNonnegative :
      0 ≤ |inner ℝ normal (wz1Perp2 direction)| / width := by
    positivity
  have hsquare :
      (|inner ℝ normal (wz1Perp2 direction)| / width) ^ 2 ≤
        ‖wideCoarsePhiGPullbackVector direction width normal‖ ^ 2 := by
    rw [hpullbackSquare]
    have hrewrite :
        (|inner ℝ normal (wz1Perp2 direction)| / width) ^ 2 =
          (inner ℝ normal (wz1Perp2 direction) / width) ^ 2 := by
      rw [div_pow, div_pow, sq_abs]
    rw [hrewrite]
    exact le_add_of_nonneg_left (sq_nonneg _)
  exact
    (sq_le_sq₀ hscaledNonnegative (norm_nonneg _)).1 hsquare

/-- In the fixed-projective-angle axial branch, the normalized pullback has
common-strip-normal coefficient at most `1 / 2`. -/
lemma wideCoarseEndpoint_projective_source_perp_upper
    {direction normal : Point2} {width : ℝ}
    (hwidth : 0 < width)
    (hdirection : ‖direction‖ = 1)
    (hnormal : ‖normal‖ = 1)
    (haxial :
      |inner ℝ normal (wz1Perp2 direction)| < 1 / 2)
    (hprojective :
      |inner ℝ normal (wz1Perp2 direction)| / width ≤
        |inner ℝ normal direction| / 2) :
    let pullback :=
      wideCoarsePhiGPullbackVector direction width normal
    let sourceNormal := (1 / ‖pullback‖) • pullback
    |inner ℝ (wz1Perp2 direction) sourceNormal| ≤ 1 / 2 := by
  dsimp only
  let pullback :=
    wideCoarsePhiGPullbackVector direction width normal
  have hparallel :=
    wideCoarseEndpoint_axial_parallel_lower
      hdirection hnormal haxial
  have hpullbackParallel :=
    wideCoarseEndpoint_pullback_norm_ge_parallel
      (width := width) (normal := normal) hdirection
  have hpullbackPos : 0 < ‖pullback‖ := by
    change
      0 <
        ‖wideCoarsePhiGPullbackVector direction width normal‖
    linarith
  have hperpUnit : ‖wz1Perp2 direction‖ = 1 := by
    rw [wz1Lemma49_norm_perp, hdirection]
  have horthogonal :
      inner ℝ (wz1Perp2 direction) direction = 0 := by
    rw [real_inner_comm]
    exact wz1Lemma49_inner_perp_self direction
  have hself :
      inner ℝ (wz1Perp2 direction)
        (wz1Perp2 direction) = 1 := by
    rw [real_inner_self_eq_norm_sq, hperpUnit]
    norm_num
  have hinnerPullback :
      inner ℝ (wz1Perp2 direction) pullback =
        inner ℝ normal (wz1Perp2 direction) / width := by
    simp only [pullback, wideCoarsePhiGPullbackVector,
      inner_add_right, real_inner_smul_right,
      horthogonal, hself, mul_zero, zero_add, mul_one]
  have hinnerSource :
      |inner ℝ (wz1Perp2 direction)
          ((1 / ‖pullback‖) • pullback)| =
        (1 / ‖pullback‖) *
          |inner ℝ normal (wz1Perp2 direction) / width| := by
    rw [inner_smul_right, abs_mul,
      abs_of_pos (one_div_pos.mpr hpullbackPos),
      hinnerPullback]
  rw [hinnerSource, abs_div, abs_of_pos hwidth]
  have hscaled :
      |inner ℝ normal (wz1Perp2 direction)| / width ≤
        ‖pullback‖ / 2 := by
    calc
      |inner ℝ normal (wz1Perp2 direction)| / width
          ≤ |inner ℝ normal direction| / 2 := hprojective
      _ ≤ ‖pullback‖ / 2 := by
        exact div_le_div_of_nonneg_right
          hpullbackParallel (by norm_num)
  have hinverseNonnegative : 0 ≤ 1 / ‖pullback‖ := by
    positivity
  calc
    1 / ‖pullback‖ *
          (|inner ℝ normal (wz1Perp2 direction)| / width)
        ≤ 1 / ‖pullback‖ * (‖pullback‖ / 2) := by
          exact mul_le_mul_of_nonneg_left
            hscaled hinverseNonnegative
    _ = 1 / 2 := by
      field_simp [hpullbackPos.ne']

/-- The parallel pullback coefficient divided by the pullback norm is a
lower bound for the projective distance from the common-strip normal. -/
lemma wideCoarseEndpoint_parallel_ratio_le_signedNormal_dist
    {direction normal : Point2} {width : ℝ}
    (hwidth : 0 < width)
    (hdirection : ‖direction‖ = 1)
    (hnormal : ‖normal‖ = 1)
    (haxial :
      |inner ℝ normal (wz1Perp2 direction)| < 1 / 2) :
    let pullback :=
      wideCoarsePhiGPullbackVector direction width normal
    let sourceNormal := (1 / ‖pullback‖) • pullback
    |inner ℝ normal direction| / ‖pullback‖ ≤
      ‖wz1Perp2 direction -
        wideCoarseEndpointSignedNormal
          (wz1Perp2 direction) sourceNormal‖ := by
  dsimp only
  let pullback :=
    wideCoarsePhiGPullbackVector direction width normal
  let sourceNormal := (1 / ‖pullback‖) • pullback
  let signedNormal :=
    wideCoarseEndpointSignedNormal
      (wz1Perp2 direction) sourceNormal
  have hparallel :=
    wideCoarseEndpoint_axial_parallel_lower
      hdirection hnormal haxial
  have hpullbackParallel :=
    wideCoarseEndpoint_pullback_norm_ge_parallel
      (width := width) (normal := normal) hdirection
  have hpullbackPos : 0 < ‖pullback‖ := by
    change
      0 <
        ‖wideCoarsePhiGPullbackVector direction width normal‖
    linarith
  have hperpOrthogonal :
      inner ℝ direction (wz1Perp2 direction) = 0 :=
    wz1Lemma49_inner_perp_self direction
  have hdirectionSelf :
      inner ℝ direction direction = 1 := by
    rw [real_inner_self_eq_norm_sq, hdirection]
    norm_num
  have hinnerPullback :
      inner ℝ direction pullback =
        inner ℝ normal direction := by
    simp only [pullback, wideCoarsePhiGPullbackVector,
      inner_add_right, real_inner_smul_right,
      hdirectionSelf, hperpOrthogonal, mul_one, mul_zero,
      add_zero]
  have hinnerSource :
      |inner ℝ direction sourceNormal| =
        |inner ℝ normal direction| / ‖pullback‖ := by
    rw [show
      inner ℝ direction sourceNormal =
        (1 / ‖pullback‖) *
          inner ℝ normal direction by
      simp only [sourceNormal, inner_smul_right, hinnerPullback]]
    rw [abs_mul, abs_of_pos (one_div_pos.mpr hpullbackPos)]
    field_simp [hpullbackPos.ne']
  have hinnerSigned :
      |inner ℝ direction signedNormal| =
        |inner ℝ direction sourceNormal| := by
    by_cases hsign :
        0 ≤ inner ℝ (wz1Perp2 direction) sourceNormal
    · simp [signedNormal, wideCoarseEndpointSignedNormal, hsign]
    · simp [signedNormal, wideCoarseEndpointSignedNormal, hsign,
        inner_neg_right, abs_neg]
  have hprojection :
      |inner ℝ direction
          (wz1Perp2 direction - signedNormal)| =
        |inner ℝ normal direction| / ‖pullback‖ := by
    rw [inner_sub_right, hperpOrthogonal, zero_sub, abs_neg,
      hinnerSigned, hinnerSource]
  have hcauchy :
      |inner ℝ direction
          (wz1Perp2 direction - signedNormal)| ≤
        ‖direction‖ *
          ‖wz1Perp2 direction - signedNormal‖ :=
    abs_real_inner_le_norm _ _
  rw [hprojection, hdirection, one_mul] at hcauchy
  simpa [pullback, sourceNormal, signedNormal] using hcauchy

/-- In the entire axial coarse-normal regime, the enlarged exact source
radius is at most four times the coarse test radius. -/
lemma wideCoarseEndpoint_axial_rawRadius_upper
    {direction normal : Point2}
    {delta width radius : ℝ}
    (hdelta : 0 < delta)
    (hwidth : 0 < width)
    (hwidthOne : width ≤ 1)
    (hradius : delta / width ≤ radius)
    (hdirection : ‖direction‖ = 1)
    (hnormal : ‖normal‖ = 1)
    (haxial :
      |inner ℝ normal (wz1Perp2 direction)| < 1 / 2) :
    max delta
        ((radius + delta / width) /
          ‖wideCoarsePhiGPullbackVector direction width normal‖) ≤
      4 * radius := by
  have hparallel :=
    wideCoarseEndpoint_axial_parallel_lower
      hdirection hnormal haxial
  have hpullbackParallel :=
    wideCoarseEndpoint_pullback_norm_ge_parallel
      (width := width) (normal := normal) hdirection
  have hpullbackLower :
      3 / 4 <
        ‖wideCoarsePhiGPullbackVector direction width normal‖ :=
    hparallel.trans_le hpullbackParallel
  have hpullbackPos :
      0 <
        ‖wideCoarsePhiGPullbackVector direction width normal‖ := by
    linarith
  have hradiusNonnegative : 0 ≤ radius := by
    exact (div_pos hdelta hwidth).le.trans hradius
  have hdeltaWidth :
      delta ≤ width * radius := by
    have h := (div_le_iff₀ hwidth).1 hradius
    simpa [mul_comm] using h
  have hdeltaRadius : delta ≤ radius := by
    calc
      delta ≤ width * radius := hdeltaWidth
      _ ≤ radius := by
        nlinarith
  have hinverseBound :
      1 /
          ‖wideCoarsePhiGPullbackVector direction width normal‖ ≤
        2 := by
    have hinverse :=
      one_div_le_one_div_of_le
        (show (0 : ℝ) < 3 / 4 by norm_num)
        hpullbackLower.le
    have hsimplify : 1 / (3 / 4 : ℝ) = 4 / 3 := by norm_num
    rw [hsimplify] at hinverse
    linarith
  have hsourceRadius :
      (radius + delta / width) /
          ‖wideCoarsePhiGPullbackVector direction width normal‖ ≤
        4 * radius := by
    calc
      (radius + delta / width) /
            ‖wideCoarsePhiGPullbackVector direction width normal‖ =
          (radius + delta / width) *
            (1 /
              ‖wideCoarsePhiGPullbackVector direction width normal‖) := by
            rw [div_eq_mul_inv, one_div]
      _ ≤ (radius + delta / width) * 2 := by
            exact mul_le_mul_of_nonneg_left
              hinverseBound
              (add_nonneg hradiusNonnegative
                (div_pos hdelta hwidth).le)
      _ ≤ 4 * radius := by
            nlinarith
  exact max_le (hdeltaRadius.trans (by nlinarith)) hsourceRadius

/-- When the perpendicular coefficient is nonzero, the exact denominator
gives the enlarged source radius a factor `width / |b|`. -/
lemma wideCoarseEndpoint_axial_denominator_rawRadius_upper
    {direction normal : Point2}
    {delta width radius : ℝ}
    (hdelta : 0 < delta)
    (hwidth : 0 < width)
    (hradius : delta / width ≤ radius)
    (hdirection : ‖direction‖ = 1)
    (hnormal : ‖normal‖ = 1)
    (hperpendicular :
      0 < |inner ℝ normal (wz1Perp2 direction)|) :
    max delta
        ((radius + delta / width) /
          ‖wideCoarsePhiGPullbackVector direction width normal‖) ≤
      4 * width * radius /
        |inner ℝ normal (wz1Perp2 direction)| := by
  let coefficient :=
    |inner ℝ normal (wz1Perp2 direction)|
  have hpullbackLower :=
    wideCoarseEndpoint_pullback_norm_ge_scaled_perp
      (normal := normal) hwidth hdirection
  have hpullbackPos :
      0 <
        ‖wideCoarsePhiGPullbackVector direction width normal‖ := by
    have hscaled : 0 < coefficient / width := by
      exact div_pos hperpendicular hwidth
    exact hscaled.trans_le hpullbackLower
  have hcoefficientOne : coefficient ≤ 1 := by
    have hperpUnit : ‖wz1Perp2 direction‖ = 1 := by
      rw [wz1Lemma49_norm_perp, hdirection]
    calc
      coefficient =
          |inner ℝ normal (wz1Perp2 direction)| := rfl
      _ ≤ ‖normal‖ * ‖wz1Perp2 direction‖ :=
        abs_real_inner_le_norm _ _
      _ = 1 := by rw [hnormal, hperpUnit, one_mul]
  have hradiusNonnegative : 0 ≤ radius := by
    exact (div_pos hdelta hwidth).le.trans hradius
  have hdeltaWidth :
      delta ≤ width * radius := by
    have h := (div_le_iff₀ hwidth).1 hradius
    simpa [mul_comm] using h
  have hinverseBound :
      1 /
          ‖wideCoarsePhiGPullbackVector direction width normal‖ ≤
        width / coefficient := by
    have hscaled : 0 < coefficient / width := by
      exact div_pos hperpendicular hwidth
    have hinverse :=
      one_div_le_one_div_of_le hscaled hpullbackLower
    have hsimplify :
        1 / (coefficient / width) = width / coefficient := by
      field_simp [hperpendicular.ne', hwidth.ne']
    simpa [coefficient, hsimplify] using hinverse
  have hsourceRadius :
      (radius + delta / width) /
          ‖wideCoarsePhiGPullbackVector direction width normal‖ ≤
        4 * width * radius / coefficient := by
    calc
      (radius + delta / width) /
            ‖wideCoarsePhiGPullbackVector direction width normal‖ =
          (radius + delta / width) *
            (1 /
              ‖wideCoarsePhiGPullbackVector direction width normal‖) := by
            rw [div_eq_mul_inv, one_div]
      _ ≤
          (radius + delta / width) * (width / coefficient) := by
            exact mul_le_mul_of_nonneg_left
              hinverseBound
              (add_nonneg hradiusNonnegative
                (div_pos hdelta hwidth).le)
      _ ≤ 4 * width * radius / coefficient := by
        have hleft :
            radius + delta / width ≤ 2 * radius := by
          linarith
        have hfactor : 0 ≤ width / coefficient := by positivity
        calc
          (radius + delta / width) * (width / coefficient)
              ≤ (2 * radius) * (width / coefficient) := by
                exact mul_le_mul_of_nonneg_right hleft hfactor
          _ = 2 * width * radius / coefficient := by
                field_simp [hperpendicular.ne']
          _ ≤ 4 * width * radius / coefficient := by
                exact div_le_div_of_nonneg_right
                  (by
                    have hproduct : 0 ≤ width * radius :=
                      mul_nonneg hwidth.le hradiusNonnegative
                    nlinarith)
                  hperpendicular.le
  have hdeltaTarget :
      delta ≤ 4 * width * radius / coefficient := by
    calc
      delta ≤ width * radius := hdeltaWidth
      _ ≤ 4 * width * radius / coefficient := by
        have hproduct : 0 ≤ width * radius :=
          mul_nonneg hwidth.le hradiusNonnegative
        have hcoefficientPos : 0 < coefficient :=
          hperpendicular
        apply (le_div_iff₀ hcoefficientPos).2
        nlinarith
  simpa [coefficient] using max_le hdeltaTarget hsourceRadius

end Kakeya.Assouad
