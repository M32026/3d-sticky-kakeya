import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49StripNormalization
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements

/-!
# Affine normalization maps for the wide coarse preparation

These are the affine maps in the wide branch of PDF Proposition 8.9.  The
maps on `G₁` and `G₂` expand perpendicular to the common strip, while the map
on `F` is the matching transpose normalization.
-/

namespace Kakeya.Assouad

open scoped ENNReal

noncomputable section

/-- Strip normalization for a `G` coordinate class. -/
def wideCoarsePhiG
    (v : Point2) (w : ℝ) (hw : 0 < w)
    (base anchor : Point2) (hv : ‖v‖ = 1) :
    Point2 ≃ᵃ[ℝ] Point2 :=
  wz1Lemma49StripNormalizationMap base v w hw anchor hv

/-- Orthogonal transpose normalization for the `F` coordinate class. -/
def wideCoarsePhiF
    (v : Point2) (w : ℝ) (hw : 0 < w)
    (hv : ‖v‖ = 1) :
    Point2 ≃ᵃ[ℝ] Point2 :=
  let u := wz1Perp2 v
  let hu : ‖u‖ = 1 := by
    rw [wz1Lemma49_norm_perp v, hv]
  wz1Lemma49StripNormalizationMap 0 u w hw 0 hu

/-- `wz1Perp2` is an involution up to sign. -/
private lemma perp2_involution (v : Point2) :
    wz1Perp2 (wz1Perp2 v) = -v := by
  ext i
  fin_cases i <;> simp [wz1Perp2] <;> decide

/-- The inverse of `wideCoarsePhiG` is nonexpansive when `w ≤ 1`. -/
lemma wideCoarsePhiG_symm_nonexpansive
    {v : Point2} {w : ℝ} {hw : 0 < w} {hw_le_one : w ≤ 1}
    {base anchor : Point2} {hv : ‖v‖ = 1} :
    ∀ (x y : Point2),
      dist ((wideCoarsePhiG v w hw base anchor hv).symm x)
           ((wideCoarsePhiG v w hw base anchor hv).symm y) ≤
      dist x y :=
  wz1Lemma49StripNormalizationMap_symm_nonexpansive
    hw hw_le_one anchor hv

/-- The inverse of `wideCoarsePhiF` is nonexpansive when `w ≤ 1`. -/
lemma wideCoarsePhiF_symm_nonexpansive
    {v : Point2} {w : ℝ} {hw : 0 < w} {hw_le_one : w ≤ 1}
    {hv : ‖v‖ = 1} :
    ∀ (x y : Point2),
      dist ((wideCoarsePhiF v w hw hv).symm x)
           ((wideCoarsePhiF v w hw hv).symm y) ≤
      dist x y :=
  let u := wz1Perp2 v
  let hu : ‖u‖ = 1 := by
    rw [wz1Lemma49_norm_perp v, hv]
  wz1Lemma49StripNormalizationMap_symm_nonexpansive
    hw hw_le_one (0 : Point2) hu

/-- `wideCoarsePhiG` maps a diameter-`1/10` strip subset into the radius-two ball. -/
lemma wideCoarsePhiG_image_bounded
    {v : Point2} {w : ℝ} {hw : 0 < w}
    {base anchor : Point2} {hv : ‖v‖ = 1}
    {setG : DiscreteSet 2}
    (hanchor : anchor ∈ setG)
    (hstrip : ∀ p ∈ setG,
      |inner ℝ (p - base) (wz1Perp2 v)| ≤ w)
    (hdiameter : ∀ x ∈ setG, ∀ y ∈ setG, dist x y ≤ 1 / 10) :
    ∀ p ∈ setG,
      dist (wideCoarsePhiG v w hw base anchor hv p) 0 ≤ 2 :=
  wz1Lemma49StripNormalizationMap_image_bounded
    hw anchor setG hanchor hv
    (fun p hp => hstrip p hp) hdiameter

/-- Coordinate formula for the endpoint normalization. -/
lemma wideCoarsePhiG_apply
    (v : Point2) (w : ℝ) (hw : 0 < w)
    (base anchor : Point2) (hv : ‖v‖ = 1)
    (point : Point2) :
    wideCoarsePhiG v w hw base anchor hv point =
      inner ℝ (point - anchor) v • v +
        (inner ℝ (point - base) (wz1Perp2 v) / w) •
          wz1Perp2 v := by
  let perpendicular := wz1Perp2 v
  let center := wz1Lemma49StripProjection base v anchor
  have hvv : inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hv] <;> norm_num
  have horthogonal :
      inner ℝ v perpendicular = 0 :=
    wz1Lemma49_inner_perp_self v
  have hcenter_v :
      inner ℝ center v = inner ℝ anchor v := by
    have h :
        inner ℝ center v =
          inner ℝ base v +
            inner ℝ (anchor - base) v * inner ℝ v v := by
      simp [center, wz1Lemma49StripProjection,
        inner_add_left, real_inner_smul_left]
      <;> rfl
    rw [h, hvv]
    have hsub :
        inner ℝ (anchor - base) v =
          inner ℝ anchor v - inner ℝ base v :=
      inner_sub_left anchor base v
    rw [hsub] <;> ring
  have hcenter_perpendicular :
      inner ℝ center perpendicular =
        inner ℝ base perpendicular := by
    have h :
        inner ℝ center perpendicular =
          inner ℝ base perpendicular +
            inner ℝ (anchor - base) v *
              inner ℝ v perpendicular := by
      simp [center, wz1Lemma49StripProjection,
        inner_add_left, real_inner_smul_left]
      <;> rfl
    rw [h, horthogonal] <;> ring
  rw [wideCoarsePhiG, wz1Lemma49StripNormalizationMap_apply]
  have hparallel :
      inner ℝ (point - center) v =
        inner ℝ (point - anchor) v := by
    rw [inner_sub_left, inner_sub_left, hcenter_v]
  have hperpendicular :
      inner ℝ (point - center) perpendicular =
        inner ℝ (point - base) perpendicular := by
    rw [inner_sub_left, inner_sub_left, hcenter_perpendicular]
  rw [hparallel, hperpendicular]

/-- Endpoint normalization divides perpendicular difference coordinates by
the strip width. -/
lemma wideCoarsePhiG_sub_inner_perp
    (v : Point2) (w : ℝ) (hw : 0 < w)
    (base anchor : Point2) (hv : ‖v‖ = 1)
    (first second : Point2) :
    inner ℝ
        (wideCoarsePhiG v w hw base anchor hv first -
          wideCoarsePhiG v w hw base anchor hv second)
        (wz1Perp2 v) =
      inner ℝ (first - second) (wz1Perp2 v) / w := by
  have horthogonal :
      inner ℝ v (wz1Perp2 v) = 0 :=
    wz1Lemma49_inner_perp_self v
  rw [wideCoarsePhiG_apply, wideCoarsePhiG_apply]
  simp only [inner_sub_left, inner_add_left,
    real_inner_smul_left, horthogonal, mul_zero, zero_add]
  rw [real_inner_self_eq_norm_sq, wz1Lemma49_norm_perp, hv]
  simp only [one_pow, mul_one]
  ring

/-- Norm squared in an orthonormal frame. -/
private lemma wide_coarse_norm_orthonormal
    {first second : Point2} {a b : ℝ}
    (hfirst : ‖first‖ = 1)
    (hsecond : ‖second‖ = 1)
    (horthogonal : inner ℝ first second = 0) :
    ‖a • first + b • second‖ ^ 2 = a ^ 2 + b ^ 2 := by
  have hfirstSq : first 0 ^ 2 + first 1 ^ 2 = 1 := by
    have h := norm2_sq first
    rw [hfirst] at h <;> nlinarith
  have hsecondSq : second 0 ^ 2 + second 1 ^ 2 = 1 := by
    have h := norm2_sq second
    rw [hsecond] at h <;> nlinarith
  have hcross : first 0 * second 0 + first 1 * second 1 = 0 := by
    simpa [inner2_eq] using horthogonal
  rw [norm2_sq]
  have hc : ∀ i : Fin 2,
      (a • first + b • second) i = a * first i + b * second i := by
    intro i
    simp
  rw [hc 0, hc 1]
  calc
    (a * first 0 + b * second 0) ^ 2 +
        (a * first 1 + b * second 1) ^ 2 =
      a ^ 2 * (first 0 ^ 2 + first 1 ^ 2) +
      2 * a * b * (first 0 * second 0 + first 1 * second 1) +
      b ^ 2 * (second 0 ^ 2 + second 1 ^ 2) := by ring
    _ = a ^ 2 + b ^ 2 := by
      rw [hfirstSq, hcross, hsecondSq] <;> ring

/-- The self-adjoint pullback of a target strip normal under the endpoint
normalization. -/
def wideCoarsePhiGPullbackVector
    (v : Point2) (w : ℝ) (normal : Point2) : Point2 :=
  inner ℝ normal v • v +
    (inner ℝ normal (wz1Perp2 v) / w) • wz1Perp2 v

/-- Squared norm of the endpoint strip-normal pullback in the strip frame. -/
lemma wideCoarsePhiGPullbackVector_norm_sq
    {v normal : Point2} {w : ℝ}
    (hv : ‖v‖ = 1) :
    ‖wideCoarsePhiGPullbackVector v w normal‖ ^ 2 =
      (inner ℝ normal v) ^ 2 +
        (inner ℝ normal (wz1Perp2 v) / w) ^ 2 := by
  have hu : ‖wz1Perp2 v‖ = 1 := by
    rw [wz1Lemma49_norm_perp, hv]
  exact
    wide_coarse_norm_orthonormal
      hv hu (wz1Lemma49_inner_perp_self v)

/-- For a strip width at most one, pulling back a unit target normal never
decreases its norm. -/
lemma wideCoarsePhiGPullbackVector_norm_lower
    {v normal : Point2} {w : ℝ}
    (hw : 0 < w) (hwOne : w ≤ 1)
    (hv : ‖v‖ = 1) (hnormal : ‖normal‖ = 1) :
    1 ≤ ‖wideCoarsePhiGPullbackVector v w normal‖ := by
  let u := wz1Perp2 v
  let parallel := inner ℝ normal v
  let perpendicular := inner ℝ normal u
  have hnormalDecomposition :
      normal = parallel • v + perpendicular • u :=
    orthonormal_decomp normal v hv
  have hu : ‖u‖ = 1 := by
    rw [wz1Lemma49_norm_perp, hv]
  have hnormalSquare :
      parallel ^ 2 + perpendicular ^ 2 = 1 := by
    have hnorm :=
      wide_coarse_norm_orthonormal
        hv hu (wz1Lemma49_inner_perp_self v)
        (a := parallel) (b := perpendicular)
    rw [← hnormalDecomposition, hnormal] at hnorm
    norm_num at hnorm
    exact hnorm.symm
  have hperpendicular :
      perpendicular ^ 2 ≤ (perpendicular / w) ^ 2 := by
    have hinverse : 1 ≤ 1 / w := by
      exact (le_div_iff₀ hw).2 (by simpa using hwOne)
    have habs :
        |perpendicular| ≤ |perpendicular / w| := by
      rw [abs_div, abs_of_pos hw]
      calc
        |perpendicular| = |perpendicular| / 1 := by ring
        _ ≤ |perpendicular| / w := by
          gcongr
    simpa [sq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hpullbackSquare :=
    wideCoarsePhiGPullbackVector_norm_sq
      (w := w) (normal := normal) hv
  have hnormNonnegative :
      0 ≤ ‖wideCoarsePhiGPullbackVector v w normal‖ :=
    norm_nonneg _
  dsimp only [parallel, perpendicular, u] at *
  nlinarith

/-- Exact affine-functional identity used to pull a target strip back to the
original endpoint plane. -/
lemma wideCoarsePhiG_inner_eq_pullback
    (v : Point2) (w : ℝ) (hw : 0 < w)
    (base anchor : Point2) (hv : ‖v‖ = 1)
    (point normal : Point2) :
    inner ℝ
        (wideCoarsePhiG v w hw base anchor hv point) normal =
      inner ℝ point
          (wideCoarsePhiGPullbackVector v w normal) +
        inner ℝ
          (wideCoarsePhiG v w hw base anchor hv 0) normal := by
  rw [wideCoarsePhiG_apply, wideCoarsePhiG_apply]
  simp only [wideCoarsePhiGPullbackVector,
    inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    inner_sub_left]
  rw [real_inner_comm v normal,
    real_inner_comm (wz1Perp2 v) normal]
  simp only [inner_zero_left, mul_zero, add_zero]
  ring

/-- Exact pullback of a target strip through the endpoint normalization,
including the normalizing factor that produces the transverse width gain. -/
lemma wideCoarsePhiG_strip_pullback_exact
    {v : Point2} {w : ℝ} (hw : 0 < w) (hwOne : w ≤ 1)
    (base anchor : Point2) (hv : ‖v‖ = 1)
    (normal : Point2) (hnormal : ‖normal‖ = 1)
    (level radius error : ℝ)
    (hradius : 0 ≤ radius) (herror : 0 ≤ error)
    (point assigned : Point2)
    (hclose :
      dist
        (wideCoarsePhiG v w hw base anchor hv point)
        assigned ≤ error)
    (hstrip :
      |inner ℝ assigned normal - level| ≤ radius) :
    let pullback := wideCoarsePhiGPullbackVector v w normal
    let pullbackNorm := ‖pullback‖
    let sourceNormal := (1 / pullbackNorm) • pullback
    let sourceLevel :=
      (level -
        inner ℝ
          (wideCoarsePhiG v w hw base anchor hv 0) normal) /
        pullbackNorm
    let sourceRadius := (radius + error) / pullbackNorm
    ‖sourceNormal‖ = 1 ∧
      0 ≤ sourceRadius ∧
      |inner ℝ point sourceNormal - sourceLevel| ≤ sourceRadius := by
  dsimp only
  let pullback := wideCoarsePhiGPullbackVector v w normal
  let pullbackNorm := ‖pullback‖
  have hpullbackLower :
      1 ≤ pullbackNorm := by
    exact
      wideCoarsePhiGPullbackVector_norm_lower
        hw hwOne hv hnormal
  have hpullbackPos : 0 < pullbackNorm := by
    linarith
  have hsourceNormal :
      ‖(1 / pullbackNorm) • pullback‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < (1 / pullbackNorm : ℝ))]
    have hpullbackNe :
        ‖pullback‖ ≠ 0 := by
      simpa [pullbackNorm] using hpullbackPos.ne'
    change (1 / ‖pullback‖) * ‖pullback‖ = 1
    field_simp [hpullbackNe]
  have hsourceRadius :
      0 ≤ (radius + error) / pullbackNorm := by
    positivity
  have hinnerError :
      |inner ℝ
          (wideCoarsePhiG v w hw base anchor hv point) normal -
        inner ℝ assigned normal| ≤ error := by
    calc
      |inner ℝ
          (wideCoarsePhiG v w hw base anchor hv point) normal -
        inner ℝ assigned normal| =
          |inner ℝ
            (wideCoarsePhiG v w hw base anchor hv point -
              assigned) normal| := by
                rw [inner_sub_left]
      _ ≤
          ‖wideCoarsePhiG v w hw base anchor hv point -
              assigned‖ * ‖normal‖ :=
        abs_real_inner_le_norm _ _
      _ =
          dist
            (wideCoarsePhiG v w hw base anchor hv point)
            assigned := by
              rw [hnormal, mul_one, dist_eq_norm]
      _ ≤ error := hclose
  have htarget :
      |inner ℝ
          (wideCoarsePhiG v w hw base anchor hv point) normal -
        level| ≤ radius + error := by
    have hdecomposition :
        inner ℝ
            (wideCoarsePhiG v w hw base anchor hv point) normal -
          level =
        (inner ℝ
            (wideCoarsePhiG v w hw base anchor hv point) normal -
          inner ℝ assigned normal) +
        (inner ℝ assigned normal - level) := by
      ring
    rw [hdecomposition]
    exact
      (abs_add_le _ _).trans
        (by linarith [hinnerError, hstrip])
  have hsourceIdentity :
      inner ℝ point ((1 / pullbackNorm) • pullback) -
          (level -
            inner ℝ
              (wideCoarsePhiG v w hw base anchor hv 0) normal) /
            pullbackNorm =
        (inner ℝ
            (wideCoarsePhiG v w hw base anchor hv point) normal -
          level) / pullbackNorm := by
    rw [inner_smul_right]
    have hpullbackIdentity :=
      wideCoarsePhiG_inner_eq_pullback
        v w hw base anchor hv point normal
    dsimp only [pullback]
    rw [hpullbackIdentity]
    ring
  constructor
  · exact hsourceNormal
  constructor
  · exact hsourceRadius
  · rw [hsourceIdentity, abs_div, abs_of_pos hpullbackPos]
    exact div_le_div_of_nonneg_right htarget hpullbackPos.le

/-- The endpoint normalization has lower Lipschitz factor
`1 / max 1 w` for every positive width. -/
lemma wideCoarsePhiG_lower_lipschitz
    {v : Point2} {w : ℝ} (hw : 0 < w)
    (base anchor : Point2) (hv : ‖v‖ = 1) :
    ∀ first second : Point2,
      (1 / max 1 w) * dist first second ≤
        dist
          (wideCoarsePhiG v w hw base anchor hv first)
          (wideCoarsePhiG v w hw base anchor hv second) := by
  let u := wz1Perp2 v
  have hu : ‖u‖ = 1 := by
    rw [wz1Lemma49_norm_perp v, hv]
  have horthogonal :
      inner ℝ v u = 0 :=
    wz1Lemma49_inner_perp_self v
  intro first second
  let difference := first - second
  let a := inner ℝ difference v
  let b := inner ℝ difference u
  have hsource :
      difference = a • v + b • u :=
    orthonormal_decomp difference v hv
  have himage :
      wideCoarsePhiG v w hw base anchor hv first -
          wideCoarsePhiG v w hw base anchor hv second =
        a • v + (b / w) • u := by
    rw [wideCoarsePhiG_apply, wideCoarsePhiG_apply]
    dsimp only [a, b, difference, u]
    simp only [inner_sub_left]
    module
  have hsourceSquare :
      ‖difference‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [hsource]
    exact wide_coarse_norm_orthonormal
      hv hu horthogonal
  have himageSquare :
      ‖a • v + (b / w) • u‖ ^ 2 =
        a ^ 2 + (b / w) ^ 2 :=
    wide_coarse_norm_orthonormal
      hv hu horthogonal
  let aspect := max 1 w
  have haspect : 0 < aspect := by
    dsimp only [aspect]
    exact zero_lt_one.trans_le (le_max_left _ _)
  have hwAspect : w ≤ aspect := by
    dsimp only [aspect]
    exact le_max_right _ _
  have honeAspect : 1 ≤ aspect := by
    dsimp only [aspect]
    exact le_max_left _ _
  have hfirstCoordinate :
      (a / aspect) ^ 2 ≤ a ^ 2 := by
    have habs :
        |a / aspect| ≤ |a| := by
      rw [abs_div, abs_of_pos haspect]
      exact div_le_self (abs_nonneg a) honeAspect
    simpa [sq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hsecondCoordinate :
      (b / aspect) ^ 2 ≤ (b / w) ^ 2 := by
    have habs :
        |b / aspect| ≤ |b / w| := by
      rw [abs_div, abs_div, abs_of_pos haspect,
        abs_of_pos hw]
      gcongr
    simpa [sq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hsquare :
      (‖difference‖ / aspect) ^ 2 ≤
        ‖a • v + (b / w) • u‖ ^ 2 := by
    rw [div_pow, hsourceSquare, himageSquare]
    have hrearrange :
        (a ^ 2 + b ^ 2) / aspect ^ 2 =
          (a / aspect) ^ 2 + (b / aspect) ^ 2 := by
      field_simp [haspect.ne']
    rw [hrearrange]
    linarith
  have hnonnegative :
      0 ≤ ‖difference‖ / aspect := by positivity
  have himageNonnegative :
      0 ≤ ‖a • v + (b / w) • u‖ :=
    norm_nonneg _
  have hnorm :
      ‖difference‖ / aspect ≤
        ‖a • v + (b / w) • u‖ := by
    nlinarith
  rw [dist_eq_norm, dist_eq_norm, himage]
  simpa [difference, aspect, div_eq_mul_inv,
    mul_comm] using hnorm

/-- The common half-scaling leaves the endpoint lower Lipschitz factor
`1 / (2 * max 1 w)`. -/
lemma wideCoarsePhiG_half_lower_lipschitz
    {v : Point2} {w : ℝ} (hw : 0 < w)
    (base anchor : Point2) (hv : ‖v‖ = 1) :
    ∀ first second : Point2,
      (1 / (2 * max 1 w)) * dist first second ≤
        dist
          ((1 / 2 : ℝ) •
            wideCoarsePhiG v w hw base anchor hv first)
          ((1 / 2 : ℝ) •
            wideCoarsePhiG v w hw base anchor hv second) := by
  intro first second
  have hlower :=
    wideCoarsePhiG_lower_lipschitz
      hw base anchor hv first second
  have hdistance :
      dist
          ((1 / 2 : ℝ) •
            wideCoarsePhiG v w hw base anchor hv first)
          ((1 / 2 : ℝ) •
            wideCoarsePhiG v w hw base anchor hv second) =
        (1 / 2 : ℝ) *
          dist
            (wideCoarsePhiG v w hw base anchor hv first)
            (wideCoarsePhiG v w hw base anchor hv second) := by
    simp only [dist_eq_norm]
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    norm_num
  rw [hdistance]
  calc
    (1 / (2 * max 1 w)) * dist first second =
        (1 / 2 : ℝ) *
          ((1 / max 1 w) * dist first second) := by ring
    _ ≤
        (1 / 2 : ℝ) *
          dist
            (wideCoarsePhiG v w hw base anchor hv first)
            (wideCoarsePhiG v w hw base anchor hv second) := by
      gcongr

/--
The common zero-anchor endpoint normalization maps every unit-ball strip
subset into the radius-two ball.

Using the same anchor for `G₁` and `G₂` is essential for the exact transpose
dot identity; the anchor is therefore not required to belong to either set.
-/
lemma wideCoarsePhiG_zero_anchor_image_bounded
    {v : Point2} {w : ℝ} {hw : 0 < w}
    {base : Point2} {hv : ‖v‖ = 1}
    {setG : DiscreteSet 2}
    (hstrip : ∀ p ∈ setG,
      |inner ℝ (p - base) (wz1Perp2 v)| ≤ w)
    (hball : setG.IsInUnitBall) :
    ∀ p ∈ setG,
      dist (wideCoarsePhiG v w hw base 0 hv p) 0 ≤ 2 := by
  let perpendicular := wz1Perp2 v
  have hperpendicular : ‖perpendicular‖ = 1 := by
    rw [wz1Lemma49_norm_perp v, hv]
  have horthogonal :
      inner ℝ v perpendicular = 0 :=
    wz1Lemma49_inner_perp_self v
  intro point hpoint
  let parallelCoordinate := inner ℝ point v
  let perpendicularCoordinate :=
    inner ℝ (point - base) perpendicular / w
  have hpointNorm : ‖point‖ ≤ 1 := by
    simpa [dist_zero_right] using hball point hpoint
  have hparallelAbs : |parallelCoordinate| ≤ 1 := by
    calc
      |parallelCoordinate|
          ≤ ‖point‖ * ‖v‖ :=
        abs_real_inner_le_norm point v
      _ = ‖point‖ := by rw [hv, mul_one]
      _ ≤ 1 := hpointNorm
  have hperpendicularAbs :
      |perpendicularCoordinate| ≤ 1 := by
    have hsource :=
      hstrip point hpoint
    have habs :
        |perpendicularCoordinate| =
          |inner ℝ (point - base) perpendicular| / w := by
      simp [perpendicularCoordinate, abs_div, abs_of_pos hw]
    rw [habs]
    calc
      |inner ℝ (point - base) perpendicular| / w
          ≤ w / w := by gcongr
      _ = 1 := by field_simp [hw.ne']
  have hparallelSq : parallelCoordinate ^ 2 ≤ 1 := by
    nlinarith [abs_le.mp hparallelAbs]
  have hperpendicularSq : perpendicularCoordinate ^ 2 ≤ 1 := by
    nlinarith [abs_le.mp hperpendicularAbs]
  rw [wideCoarsePhiG_apply]
  simp only [sub_zero]
  have hnormSq :
      ‖parallelCoordinate • v +
          perpendicularCoordinate • perpendicular‖ ^ 2 ≤ 2 := by
    rw [wide_coarse_norm_orthonormal
      hv hperpendicular horthogonal]
    linarith
  have hnorm :
      ‖parallelCoordinate • v +
          perpendicularCoordinate • perpendicular‖ ≤ 2 := by
    nlinarith
      [norm_nonneg
        (parallelCoordinate • v +
          perpendicularCoordinate • perpendicular)]
  simpa [parallelCoordinate, perpendicularCoordinate,
    perpendicular, dist_zero_right] using hnorm

/-- `wideCoarsePhiF` maps a unit-ball orthogonal-strip subset into the radius-two ball. -/
lemma wideCoarsePhiF_image_bounded
    {v : Point2} {w : ℝ} {hw : 0 < w}
    {hv : ‖v‖ = 1}
    {setF : DiscreteSet 2}
    (hstrip : ∀ p ∈ setF, |inner ℝ p v| ≤ w)
    (hball : setF.IsInUnitBall) :
    ∀ p ∈ setF,
      dist (wideCoarsePhiF v w hw hv p) 0 ≤ 2 := by
  let u := wz1Perp2 v
  have hu : ‖u‖ = 1 := by
    rw [wz1Lemma49_norm_perp v, hv]
  have horthogonal : inner ℝ v u = 0 := wz1Lemma49_inner_perp_self v
  have h_perp2 : wz1Perp2 u = -v := perp2_involution v
  intro p hp
  have h_v : |inner ℝ p v| ≤ w := hstrip p hp
  have h_norm_p : ‖p‖ ≤ 1 := by
    simpa [dist_zero_right] using hball p hp
  have h_u : |inner ℝ p u| ≤ 1 := by
    calc
      |inner ℝ p u| ≤ ‖p‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ = ‖p‖ := by rw [hu, mul_one]
      _ ≤ 1 := h_norm_p
  set a := inner ℝ p v / w with ha_def
  set b := inner ℝ p u with hb_def
  have ha : |a| ≤ 1 := by
    have h_abs : |a| = |inner ℝ p v| / w := by
      rw [ha_def, abs_div, abs_of_pos hw] <;> rfl
    rw [h_abs]
    have h : |inner ℝ p v| / w ≤ 1 := by
      calc
        |inner ℝ p v| / w ≤ w / w := by gcongr
        _ = 1 := by field_simp [hw.ne'] <;> norm_num
    exact h
  have hb : |b| ≤ 1 := h_u
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [abs_le.mp ha]
  have hb2 : b ^ 2 ≤ 1 := by nlinarith [abs_le.mp hb]
  have hcenter : wz1Lemma49StripProjection 0 u 0 = 0 := by
    simp [wz1Lemma49StripProjection]
  have h_main : wideCoarsePhiF v w hw hv p = a • v + b • u := by
    simp only [wideCoarsePhiF]
    rw [wz1Lemma49StripNormalizationMap_apply, hcenter, h_perp2]
    have h_eq : inner ℝ (p - 0) (wz1Perp2 v) = b := by
      simp [hb_def, sub_zero] <;> rfl
    rw [h_eq]
    have h_neg : inner ℝ (p - 0) (-v) = -inner ℝ p v := by
      simp [inner_neg_right, sub_zero]
    rw [h_neg]
    have h_smul : (-inner ℝ p v / w) • (-v) = a • v := by
      have h5 : -inner ℝ p v / w = -a := by
        rw [ha_def] <;> ring
      rw [h5, neg_smul_neg]
    rw [h_smul]
    have h_uv : wz1Perp2 v = u := by rfl
    rw [h_uv, add_comm]
  rw [h_main]
  have h3 : ‖a • v + b • u‖ ^ 2 ≤ 2 := by
    rw [wide_coarse_norm_orthonormal hv hu horthogonal] <;> linarith
  have h_nonneg : 0 ≤ ‖a • v + b • u‖ := norm_nonneg _
  have h4 : ‖a • v + b • u‖ ≤ 2 := by
    by_contra h5
    have h6 : ‖a • v + b • u‖ > 2 := by linarith
    have h7 : ‖a • v + b • u‖ ^ 2 > 4 := by nlinarith
    linarith
  simpa [dist_zero_right] using h4

/-- Coordinate formula for the transpose normalization. -/
lemma wideCoarsePhiF_apply
    (v : Point2) (w : ℝ) (hw : 0 < w)
    (hv : ‖v‖ = 1) (point : Point2) :
    wideCoarsePhiF v w hw hv point =
      (inner ℝ point v / w) • v +
        inner ℝ point (wz1Perp2 v) • wz1Perp2 v := by
  let u := wz1Perp2 v
  have hu : ‖u‖ = 1 := by
    rw [wz1Lemma49_norm_perp v, hv]
  have hperp : wz1Perp2 u = -v :=
    perp2_involution v
  have hcenter :
      wz1Lemma49StripProjection 0 u 0 = 0 := by
    simp [wz1Lemma49StripProjection]
  simp only [wideCoarsePhiF]
  rw [wz1Lemma49StripNormalizationMap_apply, hcenter,
    hperp]
  have hfirst :
      inner ℝ (point - 0) u = inner ℝ point u := by
    simp
  have hsecond :
      inner ℝ (point - 0) (-v) =
        -inner ℝ point v := by
    simp [inner_neg_right]
  rw [hfirst, hsecond]
  have hscaled :
      (-inner ℝ point v / w) • (-v) =
        (inner ℝ point v / w) • v := by
    have hscalar :
        -inner ℝ point v / w =
          -(inner ℝ point v / w) := by ring
    rw [hscalar, neg_smul_neg]
  rw [hscaled, add_comm]

/-- The transpose normalization has lower Lipschitz factor
`1 / max 1 w` for every positive width. -/
lemma wideCoarsePhiF_lower_lipschitz
    {v : Point2} {w : ℝ} (hw : 0 < w)
    (hv : ‖v‖ = 1) :
    ∀ first second : Point2,
      (1 / max 1 w) * dist first second ≤
        dist
          (wideCoarsePhiF v w hw hv first)
          (wideCoarsePhiF v w hw hv second) := by
  let u := wz1Perp2 v
  have hu : ‖u‖ = 1 := by
    rw [wz1Lemma49_norm_perp v, hv]
  have horthogonal :
      inner ℝ v u = 0 :=
    wz1Lemma49_inner_perp_self v
  intro first second
  let difference := first - second
  let a := inner ℝ difference v
  let b := inner ℝ difference u
  have hsource :
      difference = a • v + b • u :=
    orthonormal_decomp difference v hv
  have himage :
      wideCoarsePhiF v w hw hv first -
          wideCoarsePhiF v w hw hv second =
        (a / w) • v + b • u := by
    rw [wideCoarsePhiF_apply, wideCoarsePhiF_apply]
    dsimp only [a, b, difference, u]
    rw [inner_sub_left, inner_sub_left]
    module
  have hsourceSquare :
      ‖difference‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [hsource]
    exact wide_coarse_norm_orthonormal
      hv hu horthogonal
  have himageSquare :
      ‖(a / w) • v + b • u‖ ^ 2 =
        (a / w) ^ 2 + b ^ 2 :=
    wide_coarse_norm_orthonormal
      hv hu horthogonal
  let aspect := max 1 w
  have haspect : 0 < aspect := by
    dsimp only [aspect]
    exact zero_lt_one.trans_le (le_max_left _ _)
  have hwAspect : w ≤ aspect := by
    dsimp only [aspect]
    exact le_max_right _ _
  have honeAspect : 1 ≤ aspect := by
    dsimp only [aspect]
    exact le_max_left _ _
  have hfirstCoordinate :
      (a / aspect) ^ 2 ≤ (a / w) ^ 2 := by
    have habs :
        |a / aspect| ≤ |a / w| := by
      rw [abs_div, abs_div, abs_of_pos haspect,
        abs_of_pos hw]
      gcongr
    simpa [sq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hsecondCoordinate :
      (b / aspect) ^ 2 ≤ b ^ 2 := by
    have habs :
        |b / aspect| ≤ |b| := by
      rw [abs_div, abs_of_pos haspect]
      exact div_le_self (abs_nonneg b) honeAspect
    simpa [sq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hsquare :
      (‖difference‖ / aspect) ^ 2 ≤
        ‖(a / w) • v + b • u‖ ^ 2 := by
    rw [div_pow, hsourceSquare, himageSquare]
    have haspectSquare : 0 < aspect ^ 2 := by positivity
    have hrearrange :
        (a ^ 2 + b ^ 2) / aspect ^ 2 =
          (a / aspect) ^ 2 + (b / aspect) ^ 2 := by
      field_simp [haspect.ne']
    rw [hrearrange]
    linarith
  have hnonnegative :
      0 ≤ ‖difference‖ / aspect := by positivity
  have himageNonnegative :
      0 ≤ ‖(a / w) • v + b • u‖ :=
    norm_nonneg _
  have hnorm :
      ‖difference‖ / aspect ≤
        ‖(a / w) • v + b • u‖ := by
    nlinarith
  rw [dist_eq_norm, dist_eq_norm, himage]
  simpa [difference, aspect, div_eq_mul_inv,
    mul_comm] using hnorm

/-- The common half-scaling leaves lower Lipschitz factor
`1 / (2 * max 1 w)`. -/
lemma wideCoarsePhiF_half_lower_lipschitz
    {v : Point2} {w : ℝ} (hw : 0 < w)
    (hv : ‖v‖ = 1) :
    ∀ first second : Point2,
      (1 / (2 * max 1 w)) * dist first second ≤
        dist
          ((1 / 2 : ℝ) • wideCoarsePhiF v w hw hv first)
          ((1 / 2 : ℝ) • wideCoarsePhiF v w hw hv second) := by
  intro first second
  have hlower :=
    wideCoarsePhiF_lower_lipschitz hw hv first second
  have hdistance :
      dist
          ((1 / 2 : ℝ) • wideCoarsePhiF v w hw hv first)
          ((1 / 2 : ℝ) • wideCoarsePhiF v w hw hv second) =
        (1 / 2 : ℝ) *
          dist
            (wideCoarsePhiF v w hw hv first)
            (wideCoarsePhiF v w hw hv second) := by
    simp only [dist_eq_norm]
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    norm_num
  rw [hdistance]
  calc
    (1 / (2 * max 1 w)) * dist first second =
        (1 / 2 : ℝ) *
          ((1 / max 1 w) * dist first second) := by ring
    _ ≤
        (1 / 2 : ℝ) *
          dist
            (wideCoarsePhiF v w hw hv first)
            (wideCoarsePhiF v w hw hv second) := by
      gcongr

/--
The exact transpose identity from PDF Proposition 8.9:
`sourceDot = width * transformedDot`.
-/
lemma wideCoarseDotIdentity
    (v : Point2) (w : ℝ) (hw : 0 < w)
    (hv : ‖v‖ = 1)
    (base anchor : Point2)
    (f g₁ g₂ : Point2) :
    inner ℝ f (g₁ - g₂) =
      w * inner ℝ
        (wideCoarsePhiF v w hw hv f)
        (wideCoarsePhiG v w hw base anchor hv g₁ -
         wideCoarsePhiG v w hw base anchor hv g₂) := by
  let u := wz1Perp2 v
  have hu : ‖u‖ = 1 := by
    rw [wz1Lemma49_norm_perp v, hv]
  have horthogonal : inner ℝ v u = 0 := wz1Lemma49_inner_perp_self v
  have hcomm : inner ℝ u v = 0 := by
    rw [real_inner_comm]
    exact horthogonal
  have hvv : inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hv] <;> norm_num
  have huu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, hu] <;> norm_num
  have h_perp2 : wz1Perp2 u = -v := perp2_involution v

  let phiF := wideCoarsePhiF v w hw hv
  let phiG := wideCoarsePhiG v w hw base anchor hv
  let centerG := wz1Lemma49StripProjection base v anchor

  have hcenterG_v : inner ℝ centerG v = inner ℝ anchor v := by
    have h : inner ℝ centerG v =
        inner ℝ base v + inner ℝ (anchor - base) v * inner ℝ v v := by
      simp [centerG, wz1Lemma49StripProjection, inner_add_left,
        real_inner_smul_left]
      <;> rfl
    rw [h, hvv]
    have h2 : inner ℝ (anchor - base) v =
        inner ℝ anchor v - inner ℝ base v := by
      rw [inner_sub_left]
      <;> rfl
    rw [h2] <;> ring
  have hcenterG_u : inner ℝ centerG u = inner ℝ base u := by
    have h : inner ℝ centerG u =
        inner ℝ base u + inner ℝ (anchor - base) v * inner ℝ v u := by
      simp [centerG, wz1Lemma49StripProjection, inner_add_left,
        real_inner_smul_left]
      <;> rfl
    rw [h, horthogonal] <;> ring

  have hcenterF : wz1Lemma49StripProjection 0 u 0 = 0 := by
    simp [wz1Lemma49StripProjection]

  have h_uv : wz1Perp2 v = u := by rfl
  have hphiF : phiF f =
      (inner ℝ f v / w) • v + inner ℝ f u • u := by
    simp only [phiF, wideCoarsePhiF]
    rw [wz1Lemma49StripNormalizationMap_apply, hcenterF, h_perp2]
    have h1 : inner ℝ (f - 0) (wz1Perp2 v) = inner ℝ f u := by
      rw [show f - 0 = f by simp, h_uv]
    rw [h1]
    have h2 : inner ℝ (f - 0) (-v) = -inner ℝ f v := by
      rw [show f - 0 = f by simp, inner_neg_right]
    rw [h2]
    have h3 : (-inner ℝ f v / w) • (-v) =
        (inner ℝ f v / w) • v := by
      have h4 : -inner ℝ f v / w = -(inner ℝ f v / w) := by ring
      rw [h4, neg_smul_neg]
    rw [h3, h_uv, add_comm]

  have hphiG : ∀ (g : Point2),
      phiG g =
        inner ℝ (g - anchor) v • v +
          (inner ℝ (g - base) u / w) • u := by
    intro g
    simp only [phiG, wideCoarsePhiG]
    rw [wz1Lemma49StripNormalizationMap_apply]
    have h1 : inner ℝ (g - centerG) v =
        inner ℝ (g - anchor) v := by
      have h : inner ℝ (g - centerG) v =
          inner ℝ g v - inner ℝ centerG v :=
        inner_sub_left g centerG v
      rw [h, hcenterG_v]
      exact Eq.symm (inner_sub_left g anchor v)
    have h2 : inner ℝ (g - centerG) u =
        inner ℝ (g - base) u := by
      have h : inner ℝ (g - centerG) u =
          inner ℝ g u - inner ℝ centerG u :=
        inner_sub_left g centerG u
      rw [h, hcenterG_u]
      exact Eq.symm (inner_sub_left g base u)
    rw [h1, h2]

  have hdecomp : f = inner ℝ f v • v + inner ℝ f u • u :=
    orthonormal_decomp f v hv

  have h_inner : ∀ (g : Point2),
      inner ℝ (phiF f) (phiG g) =
        (inner ℝ f v * inner ℝ (g - anchor) v +
         inner ℝ f u * inner ℝ (g - base) u) / w := by
    intro g
    rw [hphiF, hphiG g]
    have hnorm_v2 : ‖v‖ ^ 2 = 1 := by rw [hv] <;> norm_num
    have hnorm_u2 : ‖u‖ ^ 2 = 1 := by rw [hu] <;> norm_num
    simp [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hvv, huu, horthogonal, hcomm,
      hnorm_v2, hnorm_u2]
    <;> ring

  have h_diff_v : inner ℝ (g₁ - g₂) v =
      inner ℝ (g₁ - anchor) v - inner ℝ (g₂ - anchor) v := by
    have h1 : inner ℝ (g₁ - g₂) v = inner ℝ g₁ v - inner ℝ g₂ v := by
      rw [inner_sub_left] <;> rfl
    have h2 : inner ℝ (g₁ - anchor) v =
        inner ℝ g₁ v - inner ℝ anchor v := by
      rw [inner_sub_left] <;> rfl
    have h3 : inner ℝ (g₂ - anchor) v =
        inner ℝ g₂ v - inner ℝ anchor v := by
      rw [inner_sub_left] <;> rfl
    rw [h1, h2, h3] <;> ring

  have h_diff_u : inner ℝ (g₁ - g₂) u =
      inner ℝ (g₁ - base) u - inner ℝ (g₂ - base) u := by
    have h1 : inner ℝ (g₁ - g₂) u = inner ℝ g₁ u - inner ℝ g₂ u := by
      rw [inner_sub_left] <;> rfl
    have h2 : inner ℝ (g₁ - base) u =
        inner ℝ g₁ u - inner ℝ base u := by
      rw [inner_sub_left] <;> rfl
    have h3 : inner ℝ (g₂ - base) u =
        inner ℝ g₂ u - inner ℝ base u := by
      rw [inner_sub_left] <;> rfl
    rw [h1, h2, h3] <;> ring

  have h_main_expand : inner ℝ f (g₁ - g₂) =
      inner ℝ f v * inner ℝ (g₁ - g₂) v +
      inner ℝ f u * inner ℝ (g₁ - g₂) u := by
    have h1 : inner ℝ f (g₁ - g₂) =
        inner ℝ
          (inner ℝ f v • v + inner ℝ f u • u)
          (g₁ - g₂) := by
      exact congrArg (fun x => inner ℝ x (g₁ - g₂)) hdecomp
    rw [h1]
    have h2 :
        inner ℝ
            (inner ℝ f v • v + inner ℝ f u • u)
            (g₁ - g₂) =
          inner ℝ f v * inner ℝ v (g₁ - g₂) +
          inner ℝ f u * inner ℝ u (g₁ - g₂) := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      <;> rfl
    rw [h2]
    have hv_comm :
        inner ℝ v (g₁ - g₂) = inner ℝ (g₁ - g₂) v := by
      rw [real_inner_comm]
    have hu_comm :
        inner ℝ u (g₁ - g₂) = inner ℝ (g₁ - g₂) u := by
      rw [real_inner_comm]
    rw [hv_comm, hu_comm]

  calc
    inner ℝ f (g₁ - g₂)
      = inner ℝ f v * inner ℝ (g₁ - g₂) v +
        inner ℝ f u * inner ℝ (g₁ - g₂) u := h_main_expand
    _ = inner ℝ f v *
          (inner ℝ (g₁ - anchor) v - inner ℝ (g₂ - anchor) v) +
        inner ℝ f u *
          (inner ℝ (g₁ - base) u - inner ℝ (g₂ - base) u) := by
      rw [h_diff_v, h_diff_u] <;> ring
    _ = (inner ℝ f v * inner ℝ (g₁ - anchor) v +
           inner ℝ f u * inner ℝ (g₁ - base) u) -
         (inner ℝ f v * inner ℝ (g₂ - anchor) v +
           inner ℝ f u * inner ℝ (g₂ - base) u) := by ring
    _ = w *
        (inner ℝ (phiF f) (phiG g₁) -
          inner ℝ (phiF f) (phiG g₂)) := by
      rw [h_inner g₁, h_inner g₂] <;>
        field_simp [hw.ne'] <;> ring
    _ = w * inner ℝ (phiF f) (phiG g₁ - phiG g₂) := by
      rw [inner_sub_right]

end

end Kakeya.Assouad
