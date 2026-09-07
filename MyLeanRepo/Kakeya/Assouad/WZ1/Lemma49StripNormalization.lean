import MyLeanRepo.Kakeya.Assouad.WZ1.AnisotropicFrostmanRescaling
import MyLeanRepo.Kakeya.Assouad.WZ1.AngleGeometryBase

/-!
# Strip normalization for the WZ1 Lemma 49 Kaufman branch

This module constructs the affine map that sends a width-`W` strip to a
bounded two-dimensional window.  It scales only the perpendicular coordinate
by `W⁻¹`, its inverse is nonexpansive for `W ≤ 1`, and a diameter-`1/10`
subset of the source strip maps into the radius-two ball.  The final theorem
feeds these two geometric facts directly into the closed anisotropic
Frostman-rescaling theorem.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Norm preservation under the planar quarter turn. -/
lemma wz1Lemma49_norm_perp (vector : Point2) :
    ‖wz1Perp2 vector‖ = ‖vector‖ := by
  have hcoordinates := wz1Perp2_coords vector
  have hsquare :
      ‖wz1Perp2 vector‖ ^ 2 = ‖vector‖ ^ 2 := by
    rw [norm2_sq (wz1Perp2 vector), norm2_sq vector,
      hcoordinates.1, hcoordinates.2]
    ring
  nlinarith [norm_nonneg (wz1Perp2 vector), norm_nonneg vector]

/-- A vector is orthogonal to its planar quarter turn. -/
lemma wz1Lemma49_inner_perp_self (vector : Point2) :
    inner ℝ vector (wz1Perp2 vector) = 0 := by
  have hcoordinates := wz1Perp2_coords vector
  rw [inner2_eq vector (wz1Perp2 vector),
    hcoordinates.1, hcoordinates.2]
  ring

/-- The linear functional `point ↦ inner point vector`. -/
private def wz1Lemma49InnerFunctional
    (vector : Point2) : Point2 →ₗ[ℝ] ℝ where
  toFun point := inner ℝ point vector
  map_add' first second := by
    rw [inner_add_left]
  map_smul' scalar point := by
    rw [real_inner_smul_left]
    rfl

/-- The rank-one linear map `point ↦ functional point • vector`. -/
private def wz1Lemma49DualSMul
    (functional : Point2 →ₗ[ℝ] ℝ) (vector : Point2) :
    Point2 →ₗ[ℝ] Point2 where
  toFun point := functional point • vector
  map_add' first second := by
    rw [functional.map_add, add_smul]
  map_smul' scalar point := by
    rw [functional.map_smul, smul_smul]
    rfl

/-- Inner product of orthogonal coordinates with the first frame vector. -/
private lemma wz1Lemma49_inner_combination_first
    (first second : Point2) (a b : ℝ)
    (hfirst : ‖first‖ = 1)
    (horthogonal : inner ℝ first second = 0) :
    inner ℝ (a • first + b • second) first = a := by
  rw [inner_add_left, real_inner_smul_left,
    real_inner_smul_left]
  have hreverse :
      inner ℝ second first = 0 := by
    rw [real_inner_comm]
    exact horthogonal
  rw [hreverse, mul_zero, add_zero]
  have hself :
      inner ℝ first first = 1 := by
    rw [real_inner_self_eq_norm_sq, hfirst]
    norm_num
  rw [hself, mul_one]

/-- Inner product of orthogonal coordinates with the second frame vector. -/
private lemma wz1Lemma49_inner_combination_second
    (first second : Point2) (a b : ℝ)
    (hsecond : ‖second‖ = 1)
    (horthogonal : inner ℝ first second = 0) :
    inner ℝ (a • first + b • second) second = b := by
  rw [inner_add_left, real_inner_smul_left,
    real_inner_smul_left, horthogonal, mul_zero, zero_add]
  have hself :
      inner ℝ second second = 1 := by
    rw [real_inner_self_eq_norm_sq, hsecond]
    norm_num
  rw [hself, mul_one]

/-- Norm squared in a planar orthonormal frame. -/
private lemma wz1Lemma49_norm_orthonormal
    {first second : Point2} {a b : ℝ}
    (hfirst : ‖first‖ = 1)
    (hsecond : ‖second‖ = 1)
    (horthogonal : inner ℝ first second = 0) :
    ‖a • first + b • second‖ ^ 2 = a ^ 2 + b ^ 2 := by
  have hfirstSq :
      first 0 ^ 2 + first 1 ^ 2 = 1 := by
    have h := norm2_sq first
    rw [hfirst] at h
    nlinarith
  have hsecondSq :
      second 0 ^ 2 + second 1 ^ 2 = 1 := by
    have h := norm2_sq second
    rw [hsecond] at h
    nlinarith
  have hcross :
      first 0 * second 0 + first 1 * second 1 = 0 := by
    simpa [inner2_eq] using horthogonal
  rw [norm2_sq]
  have hcoordinate :
      ∀ i : Fin 2,
        (a • first + b • second) i =
          a * first i + b * second i := by
    intro i
    simp
  rw [hcoordinate 0, hcoordinate 1]
  calc
    (a * first 0 + b * second 0) ^ 2 +
          (a * first 1 + b * second 1) ^ 2 =
        a ^ 2 * (first 0 ^ 2 + first 1 ^ 2) +
          2 * a * b *
            (first 0 * second 0 + first 1 * second 1) +
          b ^ 2 * (second 0 ^ 2 + second 1 ^ 2) := by
      ring
    _ = a ^ 2 + b ^ 2 := by
      rw [hfirstSq, hcross, hsecondSq]
      ring

/-- Linear part of the strip normalization. -/
def wz1Lemma49StripNormalizationLinear
    (direction : Point2) (width : ℝ) :
    Point2 →ₗ[ℝ] Point2 :=
  let perpendicular := wz1Perp2 direction
  wz1Lemma49DualSMul
      (wz1Lemma49InnerFunctional direction) direction +
    (1 / width : ℝ) •
      wz1Lemma49DualSMul
        (wz1Lemma49InnerFunctional perpendicular) perpendicular

/-- Coordinate formula for the linear normalization. -/
lemma wz1Lemma49StripNormalizationLinear_apply
    (direction : Point2) (width : ℝ) (point : Point2) :
    wz1Lemma49StripNormalizationLinear direction width point =
      inner ℝ point direction • direction +
        (inner ℝ point (wz1Perp2 direction) / width) •
          wz1Perp2 direction := by
  let perpendicular := wz1Perp2 direction
  change
    inner ℝ point direction • direction +
        (1 / width : ℝ) •
          (inner ℝ point perpendicular • perpendicular) =
      inner ℝ point direction • direction +
        (inner ℝ point perpendicular / width) • perpendicular
  rw [smul_smul]
  congr 2
  ring

/-- Linear inverse of the strip normalization. -/
def wz1Lemma49StripNormalizationLinearInv
    (direction : Point2) (width : ℝ) :
    Point2 →ₗ[ℝ] Point2 :=
  let perpendicular := wz1Perp2 direction
  wz1Lemma49DualSMul
      (wz1Lemma49InnerFunctional direction) direction +
    width •
      wz1Lemma49DualSMul
        (wz1Lemma49InnerFunctional perpendicular) perpendicular

/-- Coordinate formula for the inverse linear map. -/
lemma wz1Lemma49StripNormalizationLinearInv_apply
    (direction : Point2) (width : ℝ) (point : Point2) :
    wz1Lemma49StripNormalizationLinearInv direction width point =
      inner ℝ point direction • direction +
        (width * inner ℝ point (wz1Perp2 direction)) •
          wz1Perp2 direction := by
  let perpendicular := wz1Perp2 direction
  change
    inner ℝ point direction • direction +
        width • (inner ℝ point perpendicular • perpendicular) =
      inner ℝ point direction • direction +
        (width * inner ℝ point perpendicular) • perpendicular
  rw [smul_smul]

/-- The proposed inverse is a left inverse. -/
private lemma wz1Lemma49StripNormalizationLinear_left_inv
    {direction : Point2} {width : ℝ}
    (hwidth : width ≠ 0) (hdirection : ‖direction‖ = 1) :
    ∀ point,
      wz1Lemma49StripNormalizationLinearInv direction width
          (wz1Lemma49StripNormalizationLinear direction width point) =
        point := by
  let perpendicular := wz1Perp2 direction
  have hperpendicular : ‖perpendicular‖ = 1 := by
    rw [wz1Lemma49_norm_perp direction, hdirection]
  have horthogonal :
      inner ℝ direction perpendicular = 0 :=
    wz1Lemma49_inner_perp_self direction
  intro point
  let normalized :=
    wz1Lemma49StripNormalizationLinear direction width point
  have hnormalized :
      normalized =
        inner ℝ point direction • direction +
          (inner ℝ point perpendicular / width) • perpendicular :=
    wz1Lemma49StripNormalizationLinear_apply direction width point
  have hfirst :
      inner ℝ normalized direction = inner ℝ point direction := by
    rw [hnormalized]
    exact wz1Lemma49_inner_combination_first
      direction perpendicular _ _ hdirection horthogonal
  have hsecond :
      inner ℝ normalized perpendicular =
        inner ℝ point perpendicular / width := by
    rw [hnormalized]
    exact wz1Lemma49_inner_combination_second
      direction perpendicular _ _ hperpendicular horthogonal
  rw [wz1Lemma49StripNormalizationLinearInv_apply,
    hfirst, hsecond]
  have hcancel :
      width * (inner ℝ point perpendicular / width) =
        inner ℝ point perpendicular := by
    field_simp [hwidth]
  rw [hcancel]
  exact (orthonormal_decomp point direction hdirection).symm

/-- The proposed inverse is a right inverse. -/
private lemma wz1Lemma49StripNormalizationLinear_right_inv
    {direction : Point2} {width : ℝ}
    (hwidth : width ≠ 0) (hdirection : ‖direction‖ = 1) :
    ∀ point,
      wz1Lemma49StripNormalizationLinear direction width
          (wz1Lemma49StripNormalizationLinearInv direction width point) =
        point := by
  let perpendicular := wz1Perp2 direction
  have hperpendicular : ‖perpendicular‖ = 1 := by
    rw [wz1Lemma49_norm_perp direction, hdirection]
  have horthogonal :
      inner ℝ direction perpendicular = 0 :=
    wz1Lemma49_inner_perp_self direction
  intro point
  let expanded :=
    wz1Lemma49StripNormalizationLinearInv direction width point
  have hexpanded :
      expanded =
        inner ℝ point direction • direction +
          (width * inner ℝ point perpendicular) • perpendicular :=
    wz1Lemma49StripNormalizationLinearInv_apply direction width point
  have hfirst :
      inner ℝ expanded direction = inner ℝ point direction := by
    rw [hexpanded]
    exact wz1Lemma49_inner_combination_first
      direction perpendicular _ _ hdirection horthogonal
  have hsecond :
      inner ℝ expanded perpendicular =
        width * inner ℝ point perpendicular := by
    rw [hexpanded]
    exact wz1Lemma49_inner_combination_second
      direction perpendicular _ _ hperpendicular horthogonal
  rw [wz1Lemma49StripNormalizationLinear_apply,
    hfirst, hsecond]
  have hcancel :
      width * inner ℝ point perpendicular / width =
        inner ℝ point perpendicular := by
    field_simp [hwidth]
  rw [hcancel]
  exact (orthonormal_decomp point direction hdirection).symm

/-- Linear equivalence attached to the strip normalization. -/
def wz1Lemma49StripNormalizationLinearEquiv
    (direction : Point2) (width : ℝ)
    (hwidth : 0 < width) (hdirection : ‖direction‖ = 1) :
    Point2 ≃ₗ[ℝ] Point2 where
  toFun := wz1Lemma49StripNormalizationLinear direction width
  invFun := wz1Lemma49StripNormalizationLinearInv direction width
  left_inv :=
    wz1Lemma49StripNormalizationLinear_left_inv
      hwidth.ne' hdirection
  right_inv :=
    wz1Lemma49StripNormalizationLinear_right_inv
      hwidth.ne' hdirection
  map_add' :=
    (wz1Lemma49StripNormalizationLinear direction width).map_add
  map_smul' :=
    (wz1Lemma49StripNormalizationLinear direction width).map_smul

/-- Projection of an anchor onto the center line of a strip. -/
def wz1Lemma49StripProjection
    (base direction anchor : Point2) : Point2 :=
  base + inner ℝ (anchor - base) direction • direction

/-- Affine normalization of a strip. -/
def wz1Lemma49StripNormalizationMap
    (base direction : Point2) (width : ℝ)
    (hwidth : 0 < width) (anchor : Point2)
    (hdirection : ‖direction‖ = 1) :
    Point2 ≃ᵃ[ℝ] Point2 :=
  let center := wz1Lemma49StripProjection base direction anchor
  let linear :=
    wz1Lemma49StripNormalizationLinearEquiv
      direction width hwidth hdirection
  let map : Point2 → Point2 := fun point => linear (point - center)
  AffineEquiv.mk' map linear center (by
    intro point
    simp [map])

/-- Coordinate formula for the affine normalization. -/
lemma wz1Lemma49StripNormalizationMap_apply
    (base direction : Point2) (width : ℝ)
    (hwidth : 0 < width) (anchor : Point2)
    (hdirection : ‖direction‖ = 1) (point : Point2) :
    wz1Lemma49StripNormalizationMap
        base direction width hwidth anchor hdirection point =
      inner ℝ
          (point - wz1Lemma49StripProjection base direction anchor)
          direction • direction +
        (inner ℝ
            (point - wz1Lemma49StripProjection base direction anchor)
            (wz1Perp2 direction) / width) •
          wz1Perp2 direction := by
  exact
    wz1Lemma49StripNormalizationLinear_apply
      direction width
      (point - wz1Lemma49StripProjection base direction anchor)

/-- Coordinate formula for the inverse affine map. -/
lemma wz1Lemma49StripNormalizationMap_symm_apply
    (base direction : Point2) (width : ℝ)
    (hwidth : 0 < width) (anchor : Point2)
    (hdirection : ‖direction‖ = 1) (point : Point2) :
    (wz1Lemma49StripNormalizationMap
        base direction width hwidth anchor hdirection).symm point =
      wz1Lemma49StripProjection base direction anchor +
        (inner ℝ point direction • direction +
          (width * inner ℝ point (wz1Perp2 direction)) •
            wz1Perp2 direction) := by
  let center := wz1Lemma49StripProjection base direction anchor
  let linear :=
    wz1Lemma49StripNormalizationLinearEquiv
      direction width hwidth hdirection
  let phi :=
    wz1Lemma49StripNormalizationMap
      base direction width hwidth anchor hdirection
  have hpreimage : phi (center + linear.symm point) = point := by
    change linear ((center + linear.symm point) - center) = point
    rw [show (center + linear.symm point) - center =
      linear.symm point by abel]
    exact linear.right_inv point
  have hsymm : phi.symm point = center + linear.symm point := by
    exact phi.injective
      ((phi.right_inv point).trans hpreimage.symm)
  rw [hsymm]
  apply congrArg (fun value : Point2 => center + value)
  exact wz1Lemma49StripNormalizationLinearInv_apply
    direction width point

/-- The inverse normalization does not increase distances for `width ≤ 1`. -/
lemma wz1Lemma49StripNormalizationMap_symm_nonexpansive
    {base direction : Point2} {width : ℝ}
    (hwidth : 0 < width) (hwidthOne : width ≤ 1)
    (anchor : Point2) (hdirection : ‖direction‖ = 1) :
    ∀ first second,
      dist
          ((wz1Lemma49StripNormalizationMap
            base direction width hwidth anchor hdirection).symm first)
          ((wz1Lemma49StripNormalizationMap
            base direction width hwidth anchor hdirection).symm second) ≤
        dist first second := by
  let perpendicular := wz1Perp2 direction
  have hperpendicular : ‖perpendicular‖ = 1 := by
    rw [wz1Lemma49_norm_perp direction, hdirection]
  have horthogonal :
      inner ℝ direction perpendicular = 0 :=
    wz1Lemma49_inner_perp_self direction
  intro first second
  let vector := first - second
  let a := inner ℝ vector direction
  let b := inner ℝ vector perpendicular
  have hsub :
      (wz1Lemma49StripNormalizationMap
            base direction width hwidth anchor hdirection).symm first -
          (wz1Lemma49StripNormalizationMap
            base direction width hwidth anchor hdirection).symm second =
        a • direction + (width * b) • perpendicular := by
    rw [wz1Lemma49StripNormalizationMap_symm_apply,
      wz1Lemma49StripNormalizationMap_symm_apply]
    dsimp only [a, b, vector]
    rw [inner_sub_left, inner_sub_left]
    module
  have hvector :
      vector = a • direction + b • perpendicular :=
    orthonormal_decomp vector direction hdirection
  rw [dist_eq_norm, dist_eq_norm, hsub]
  change
    ‖a • direction + (width * b) • perpendicular‖ ≤ ‖vector‖
  rw [hvector]
  have hscaled :
      ‖a • direction + (width * b) • perpendicular‖ ^ 2 =
        a ^ 2 + (width * b) ^ 2 :=
    wz1Lemma49_norm_orthonormal
      hdirection hperpendicular horthogonal
  have hunscaled :
      ‖a • direction + b • perpendicular‖ ^ 2 =
        a ^ 2 + b ^ 2 :=
    wz1Lemma49_norm_orthonormal
      hdirection hperpendicular horthogonal
  have hwidthSq : width ^ 2 ≤ 1 := by
    nlinarith
  have hsquare :
      a ^ 2 + (width * b) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    nlinarith [sq_nonneg b]
  nlinarith
    [norm_nonneg (a • direction + (width * b) • perpendicular),
      norm_nonneg (a • direction + b • perpendicular)]

/-- A diameter-`1/10` subset of the source strip maps into radius two. -/
lemma wz1Lemma49StripNormalizationMap_image_bounded
    {base direction : Point2} {width : ℝ}
    (hwidth : 0 < width)
    (anchor : Point2) (set : DiscreteSet 2)
    (hanchor : anchor ∈ set) (hdirection : ‖direction‖ = 1)
    (hstrip :
      ∀ point ∈ set,
        point ∈ wz1LineNeighborhood base direction width)
    (hdiameter :
      ∀ first ∈ set, ∀ second ∈ set,
        dist first second ≤ 1 / 10) :
    ∀ point ∈ set,
      dist
          (wz1Lemma49StripNormalizationMap
            base direction width hwidth anchor hdirection point)
          0 ≤ 2 := by
  let perpendicular := wz1Perp2 direction
  let center := wz1Lemma49StripProjection base direction anchor
  have hperpendicular : ‖perpendicular‖ = 1 := by
    rw [wz1Lemma49_norm_perp direction, hdirection]
  have horthogonal :
      inner ℝ direction perpendicular = 0 :=
    wz1Lemma49_inner_perp_self direction
  have hanchorParallel :
      inner ℝ (anchor - center) direction = 0 := by
    simp only [center, wz1Lemma49StripProjection]
    rw [show
      anchor -
          (base +
            inner ℝ (anchor - base) direction • direction) =
        (anchor - base) -
          inner ℝ (anchor - base) direction • direction by abel,
      inner_sub_left, real_inner_smul_left]
    have hself :
        inner ℝ direction direction = 1 := by
      rw [real_inner_self_eq_norm_sq, hdirection]
      norm_num
    rw [hself, mul_one, sub_self]
  have hcenterPerp :
      inner ℝ (center - base) perpendicular = 0 := by
    simp only [center, wz1Lemma49StripProjection]
    rw [show
      base +
          inner ℝ (anchor - base) direction • direction -
          base =
        inner ℝ (anchor - base) direction • direction by abel,
      real_inner_smul_left, horthogonal, mul_zero]
  intro point hpoint
  have hparallel :
      |inner ℝ (point - center) direction| ≤ 1 / 10 := by
    have heq :
        inner ℝ (point - center) direction =
          inner ℝ (point - anchor) direction := by
      rw [show point - center =
        (point - anchor) + (anchor - center) by abel,
        inner_add_left, hanchorParallel, add_zero]
    rw [heq]
    calc
      |inner ℝ (point - anchor) direction|
          ≤ ‖point - anchor‖ * ‖direction‖ :=
        abs_real_inner_le_norm _ _
      _ = dist point anchor := by
        rw [hdirection, mul_one]
        simp [dist_eq_norm]
      _ ≤ 1 / 10 :=
        hdiameter point hpoint anchor hanchor
  have hperp :
      |inner ℝ (point - center) perpendicular| ≤ width := by
    have hpointStrip := hstrip point hpoint
    have heq :
        inner ℝ (point - center) perpendicular =
          inner ℝ (point - base) perpendicular := by
      rw [show point - center =
        (point - base) - (center - base) by abel,
        inner_sub_left, hcenterPerp, sub_zero]
    rw [heq]
    exact hpointStrip
  rw [wz1Lemma49StripNormalizationMap_apply]
  let a := inner ℝ (point - center) direction
  let b := inner ℝ (point - center) perpendicular / width
  have hnorm :
      ‖a • direction + b • perpendicular‖ ^ 2 =
        a ^ 2 + b ^ 2 :=
    wz1Lemma49_norm_orthonormal
      hdirection hperpendicular horthogonal
  have ha : a ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := by
    rw [show a ^ 2 = |a| ^ 2 by rw [sq_abs]]
    gcongr
  have hbAbs : |b| ≤ 1 := by
    calc
      |b| =
          |inner ℝ (point - center) perpendicular| / width := by
        simp [b, abs_div, abs_of_pos hwidth]
      _ ≤ width / width := by gcongr
      _ = 1 := by field_simp [hwidth.ne']
  have hb : b ^ 2 ≤ 1 := by
    rw [show b ^ 2 = |b| ^ 2 by rw [sq_abs]]
    have hproduct :
        0 ≤ |b| * (1 - |b|) :=
      mul_nonneg (abs_nonneg b) (sub_nonneg.mpr hbAbs)
    nlinarith
  have hsquare :
      ‖a • direction + b • perpendicular‖ ^ 2 ≤ 4 := by
    rw [hnorm]
    nlinarith
  have hnormBound :
      ‖a • direction + b • perpendicular‖ ≤ 2 := by
    nlinarith [norm_nonneg (a • direction + b • perpendicular)]
  simpa [a, b, center, dist_zero_right] using hnormBound

/--
Apply the closed anisotropic Frostman-rescaling theorem to the canonical
strip normalization.
-/
theorem wz1_lemma49_strip_normalization_frostman_rescaling
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ (delta width : ℝ)
        (hdelta : 0 < delta) (hdeltaSmall : delta ≤ delta₀)
        (hdeltaWidth : delta ≤ width) (hwidthOne : width ≤ 1)
        (hpower : Real.rpow delta (1 - epsilon) ≤ width)
        (set : DiscreteSet 2) (hset : set.Nonempty)
        (C : ENNReal) (hC : 1 ≤ C)
        (hseparated : set.IsDeltaSeparated delta)
        (hFrostman : set.IsFrostman delta 1 C)
        (base direction : Point2) (hdirection : ‖direction‖ = 1)
        (anchor : Point2) (hanchor : anchor ∈ set)
        (hstrip : ∀ point ∈ set,
          point ∈ wz1LineNeighborhood base direction width)
        (hdiameter : ∀ first ∈ set, ∀ second ∈ set,
          dist first second ≤ 1 / 10),
          Nonempty
            (WZ1AnisotropicFrostmanRescalingData
              set
              (wz1Lemma49StripNormalizationMap
                base direction width
                  (show 0 < width from
                    lt_of_lt_of_le hdelta hdeltaWidth)
                  anchor hdirection)
              delta width epsilon C) := by
  rcases
      wz1_anisotropic_frostman_rescaling epsilon hepsilon with
    ⟨delta₀, hdelta₀, hdelta₀One, hrescale⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta width hdelta hdeltaSmall
    hdeltaWidth hwidthOne hpower
    set hset C hC hseparated hFrostman
    base direction hdirection anchor hanchor hstrip hdiameter
  have hwidth : 0 < width := hdelta.trans_le hdeltaWidth
  let phi :=
    wz1Lemma49StripNormalizationMap
      base direction width hwidth anchor hdirection
  have hinverse :
      ∀ first second,
        dist (phi.symm first) (phi.symm second) ≤
          dist first second :=
    wz1Lemma49StripNormalizationMap_symm_nonexpansive
      hwidth hwidthOne anchor hdirection
  have hbounded :
      ∀ point ∈ set, dist (phi point) 0 ≤ 2 :=
    wz1Lemma49StripNormalizationMap_image_bounded
      hwidth anchor set hanchor hdirection hstrip hdiameter
  exact
    hrescale delta width hdelta hdeltaSmall
      hdeltaWidth hwidthOne hpower set hset C hC
      hseparated hFrostman phi hinverse hbounded

end

end Kakeya.Assouad
