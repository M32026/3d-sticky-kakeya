import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import MyLeanRepo.Kakeya.Assouad.WZ1.CoreHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49ActiveWidthGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49ArithmeticGeometricLemmas

/-!
# Sanity checks for the faithful Lemma 8.13 freeze

These are prerequisite mathematical consequences of the residual input. They
are proved before any new Seed target is launched, so the frozen statement
does not hide an inconsistent scale window.
-/

namespace Kakeya.Assouad

noncomputable section

/-- The active common width is bounded by `2 + width`: compare every active
endpoint to one point of `G₁` already known to lie in the source strip. -/
lemma wz1Lemma8_13_activeWidth_le_two_add_width
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta) :
    wz1Lemma8_13FaithfulActiveWidth input ≤ 2 + input.width := by
  let perpendicular := wz1Perp2 input.direction
  have hperpendicular : ‖perpendicular‖ = 1 := by
    rw [wz1Lemma49_norm_perp input.direction, input.direction_unit]
  rcases input.G₁_nonempty with ⟨anchor, hanchor⟩
  have hanchorStrip :
      |inner ℝ (anchor - input.base) perpendicular| ≤ input.width :=
    input.G₁_strip anchor hanchor
  have hendpoint :
      ∀ endpoint ∈ input.G₁ ∪ input.G₂,
        |inner ℝ (endpoint - input.base) perpendicular| ≤
          2 + input.width := by
    intro endpoint hendpoint
    have hendpointBall : ‖endpoint‖ ≤ 1 := by
      rcases Finset.mem_union.mp hendpoint with (hfirst | hsecond)
      · simpa [dist_zero_right] using
          input.G₁_ball endpoint hfirst
      · simpa [dist_zero_right] using
          input.G₂_ball endpoint hsecond
    have hanchorBall : ‖anchor‖ ≤ 1 := by
      simpa [dist_zero_right] using input.G₁_ball anchor hanchor
    have hdistance : dist endpoint anchor ≤ 2 := by
      calc
        dist endpoint anchor = ‖endpoint - anchor‖ := by
          rw [dist_eq_norm]
        _ ≤ ‖endpoint‖ + ‖anchor‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by linarith
        _ = 2 := by norm_num
    have hcoordinate :
        |inner ℝ (endpoint - anchor) perpendicular| ≤ 2 := by
      calc
        |inner ℝ (endpoint - anchor) perpendicular|
            ≤ ‖endpoint - anchor‖ * ‖perpendicular‖ :=
          abs_real_inner_le_norm _ _
        _ = dist endpoint anchor := by
          rw [hperpendicular, mul_one, dist_eq_norm]
        _ ≤ 2 := hdistance
    have hdecomposition :
        inner ℝ (endpoint - input.base) perpendicular =
          inner ℝ (endpoint - anchor) perpendicular +
            inner ℝ (anchor - input.base) perpendicular := by
      rw [show endpoint - input.base =
        (endpoint - anchor) + (anchor - input.base) by abel]
      rw [inner_add_left]
    rw [hdecomposition]
    exact (abs_add_le _ _).trans
      ((add_le_add hcoordinate hanchorStrip).trans_eq
        (by ring))
  let widths : Finset ℝ :=
    input.H.image fun edge =>
      max
        |inner ℝ (edge.2.1 - input.base) perpendicular|
        |inner ℝ (edge.2.2 - input.base) perpendicular|
  have hwidths : widths.Nonempty :=
    input.density.1.image _
  have hall :
      ∀ value ∈ widths, value ≤ 2 + input.width := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with ⟨edge, hedge, rfl⟩
    have hsupport :=
      wz1_uniform_density_support input.density edge hedge
    exact max_le
      (hendpoint edge.2.1
        (Finset.mem_union_left _ hsupport.2.1))
      (hendpoint edge.2.2
        (Finset.mem_union_right _ hsupport.2.2))
  have hmax :
      widths.max' hwidths ≤ 2 + input.width :=
    Finset.max'_le widths hwidths _ hall
  change
    max delta (widths.max' hwidths) ≤ 2 + input.width
  apply max_le
  · have hdeltaWidth := input.delta_le_width
    linarith [input.width_pos]
  · exact hmax

/-- If the residual factor is at least four, the residual large-width
inequality and the preceding active-width bound force `width < 1`. -/
lemma wz1Lemma8_13_width_lt_one
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hfactor :
      4 ≤ Real.rpow delta
        (-epsilon + wz1Lemma8_13FaithfulEpsilonOne epsilon)) :
    input.width < 1 := by
  have hactive :=
    wz1Lemma8_13_activeWidth_le_two_add_width input
  have hlarge := input.active_width_large
  change
    Real.rpow delta
        (-epsilon + wz1Lemma49AuxiliaryEpsilon epsilon) *
        input.width <
      wz1Lemma8_13FaithfulActiveWidth input at hlarge
  have hepsilonOne :
      wz1Lemma8_13FaithfulEpsilonOne epsilon =
        wz1Lemma49AuxiliaryEpsilon epsilon := by
    rfl
  rw [← hepsilonOne] at hlarge
  have hfour :
      4 * input.width ≤
        Real.rpow delta
            (-epsilon + wz1Lemma8_13FaithfulEpsilonOne epsilon) *
          input.width := by
    gcongr
    exact input.width_pos.le
  linarith

/-- The fixed loss ledger has the strict room needed to absorb affine,
coarsening, and graph-refinement losses. -/
lemma wz1Lemma8_13_loss_gap
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    4 * wz1Lemma8_13FaithfulEta epsilon +
        2 * wz1Lemma8_13FaithfulEpsilonOne epsilon <
      wz1Lemma8_13FaithfulNormalizedEta epsilon := by
  dsimp only [wz1Lemma8_13FaithfulEta,
    wz1Lemma8_13FaithfulEpsilonOne,
    wz1Lemma8_13FaithfulNormalizedEta]
  nlinarith [sq_pos_of_pos hepsilon]

/-- The source-density loss is strictly smaller than the affine loss. -/
lemma wz1Lemma8_13_eta_lt_epsilonOne
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    wz1Lemma8_13FaithfulEta epsilon <
      wz1Lemma8_13FaithfulEpsilonOne epsilon := by
  dsimp only [wz1Lemma8_13FaithfulEta,
    wz1Lemma8_13FaithfulEpsilonOne]
  nlinarith [sq_pos_of_pos hepsilon]

/--
After paying the worst one-dimensional coarsening loss
`delta^(-epsilon₁)`, the Kaufman gain still has a strict power advantage.
-/
lemma wz1Lemma8_13_closing_exponent_gap
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon < 1) :
    4 * wz1Lemma8_13FaithfulNormalizedEta epsilon +
        wz1Lemma8_13FaithfulEpsilonOne epsilon <
      epsilon ^ 2 / 2 +
        2 * epsilon *
          wz1Lemma8_13FaithfulNormalizedEta epsilon := by
  dsimp only [wz1Lemma8_13FaithfulNormalizedEta,
    wz1Lemma8_13FaithfulEpsilonOne]
  have hepsilonSq : 0 < epsilon ^ 2 :=
    sq_pos_of_pos hepsilon
  nlinarith [mul_lt_mul_of_pos_left hepsilonOne hepsilonSq]

/-- The normalized loss is below the `epsilon / 4` Kaufman budget. -/
lemma wz1Lemma8_13_normalizedEta_lt_quarter
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilonOne : epsilon < 1) :
    wz1Lemma8_13FaithfulNormalizedEta epsilon < epsilon / 4 := by
  dsimp only [wz1Lemma8_13FaithfulNormalizedEta]
  nlinarith [mul_lt_mul_of_pos_left hepsilonOne hepsilon]

/-- The faithful graph density is positive. -/
lemma wz1Lemma8_13_graphDensity_pos
    {delta epsilon : ℝ} (hdelta : 0 < delta) :
    0 < wz1Lemma8_13FaithfulGraphDensity delta epsilon := by
  exact Real.rpow_pos_of_pos hdelta _

/-- The radial cardinality parameter is positive. -/
lemma wz1Lemma8_13_directionKappa_pos
    {delta epsilon : ℝ} (hdelta : 0 < delta) :
    0 < wz1Lemma8_13FaithfulDirectionKappa delta epsilon := by
  dsimp only [wz1Lemma8_13FaithfulDirectionKappa]
  exact div_pos (Real.rpow_pos_of_pos hdelta _) (by norm_num)

/--
The direct radial-projection window is a pure two-parameter inequality.

Here `power = delta^epsilon₁`, `ratio = width / activeWidth`,
`angularScale = power * ratio`, `side = power * (1 - ratio)`, and
`sourceScale = 64 * ratio`.  The weak bound `ratio ≤ 1/2` leaves far more
than the required room in both geometric inequalities.
-/
lemma wz1Lemma8_13_radial_scale_window
    {power ratio : ℝ}
    (hpower : 0 < power)
    (hpowerOne : power ≤ 1)
    (hratio : 0 < ratio)
    (hratioHalf : ratio ≤ 1 / 2) :
    let angularScale := power * ratio
    let side := power * (1 - ratio)
    let sourceScale := 64 * ratio
    0 < side ∧
      angularScale + 4 * angularScale / side < sourceScale ∧
      angularScale ≤
        (sourceScale - angularScale - 4 * angularScale / side) /
          (2 + 8 / side) := by
  dsimp only
  have honeMinusRatio : 0 < 1 - ratio := by
    linarith
  have hside : 0 < power * (1 - ratio) :=
    mul_pos hpower honeMinusRatio
  have hangularLe : power * ratio ≤ ratio := by
    nlinarith
  have hquotient :
      power * ratio / (power * (1 - ratio)) =
        ratio / (1 - ratio) := by
    field_simp [hpower.ne', honeMinusRatio.ne']
  have hquotientLe :
      ratio / (1 - ratio) ≤ 2 * ratio := by
    apply (div_le_iff₀ honeMinusRatio).2
    nlinarith
  refine ⟨hside, ?_, ?_⟩
  · have herror :
        4 * (power * ratio) / (power * (1 - ratio)) ≤
          8 * ratio := by
      calc
        4 * (power * ratio) / (power * (1 - ratio)) =
            4 * (power * ratio / (power * (1 - ratio))) := by ring
        _ = 4 * (ratio / (1 - ratio)) := by rw [hquotient]
        _ ≤ 4 * (2 * ratio) := by gcongr
        _ = 8 * ratio := by ring
    nlinarith
  · have hdenominator :
        0 < 2 + 8 / (power * (1 - ratio)) := by
      positivity
    apply (le_div_iff₀ hdenominator).2
    have hleft :
        power * ratio *
            (2 + 8 / (power * (1 - ratio))) ≤
          18 * ratio := by
      calc
        power * ratio *
              (2 + 8 / (power * (1 - ratio))) =
            2 * (power * ratio) +
              8 * (power * ratio /
                (power * (1 - ratio))) := by ring
        _ = 2 * (power * ratio) +
              8 * (ratio / (1 - ratio)) := by rw [hquotient]
        _ ≤ 2 * ratio + 8 * (2 * ratio) := by
          gcongr
        _ = 18 * ratio := by ring
    have hright :
        55 * ratio ≤
          64 * ratio - power * ratio -
            4 * (power * ratio /
              (power * (1 - ratio))) := by
      rw [hquotient]
      nlinarith
    have hleftStrict :
        power * ratio *
            (2 + 8 / (power * (1 - ratio))) <
          55 * ratio := by
      nlinarith
    have hrightActual :
        55 * ratio ≤
          64 * ratio - power * ratio -
            4 * (power * ratio) / (power * (1 - ratio)) := by
      convert hright using 1 <;> ring
    exact hleftStrict.le.trans hrightActual

/-- The common normalization width has the paper upper bound after the
residual geometry has forced `width < 1`. -/
lemma wz1Lemma8_13_normalizationWidth_upper
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hdelta : 0 < delta)
    (hwidthOne : input.width ≤ 1)
    (hdeltaOne : delta ≤ 1) :
    wz1Lemma8_13FaithfulNormalizationWidth input ≤
      3 * Real.rpow delta
        (-wz1Lemma8_13FaithfulEpsilonOne epsilon) := by
  have hactive :
      wz1Lemma8_13FaithfulActiveWidth input ≤ 3 :=
    wz1Lemma49_activeWidth_le_three
      input.density input.base input.direction
      input.direction_unit input.width_pos hwidthOne hdeltaOne
      input.G₁_nonempty input.G₁_ball input.G₂_ball
      input.G₁_strip
  dsimp only [wz1Lemma8_13FaithfulNormalizationWidth]
  calc
    Real.rpow delta
          (-wz1Lemma8_13FaithfulEpsilonOne epsilon) *
        wz1Lemma8_13FaithfulActiveWidth input
        ≤
      Real.rpow delta
          (-wz1Lemma8_13FaithfulEpsilonOne epsilon) * 3 :=
        mul_le_mul_of_nonneg_left hactive
          (Real.rpow_nonneg hdelta.le _)
    _ =
      3 * Real.rpow delta
        (-wz1Lemma8_13FaithfulEpsilonOne epsilon) := by ring

/-- The normalization width is never smaller than
`delta^(1 - epsilon₁)`. -/
lemma wz1Lemma8_13_normalizationWidth_lower
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hdelta : 0 < delta) :
    Real.rpow delta
        (1 - wz1Lemma8_13FaithfulEpsilonOne epsilon) ≤
      wz1Lemma8_13FaithfulNormalizationWidth input := by
  have hactive :
      delta ≤ wz1Lemma8_13FaithfulActiveWidth input :=
    wz1Lemma49_delta_le_activeCommonWidth
      input.density.1 input.base input.direction
  have hpower :
      Real.rpow delta
          (1 - wz1Lemma8_13FaithfulEpsilonOne epsilon) =
        Real.rpow delta
            (-wz1Lemma8_13FaithfulEpsilonOne epsilon) *
          delta := by
    calc
      Real.rpow delta
            (1 - wz1Lemma8_13FaithfulEpsilonOne epsilon) =
          Real.rpow delta
            (-wz1Lemma8_13FaithfulEpsilonOne epsilon + 1) := by
        congr 1
        ring
      _ =
          Real.rpow delta
              (-wz1Lemma8_13FaithfulEpsilonOne epsilon) *
            Real.rpow delta 1 :=
        Real.rpow_add hdelta _ _
      _ =
          Real.rpow delta
              (-wz1Lemma8_13FaithfulEpsilonOne epsilon) *
            delta := by
        congr 1
        exact Real.rpow_one delta
  rw [hpower]
  dsimp only [wz1Lemma8_13FaithfulNormalizationWidth]
  exact mul_le_mul_of_nonneg_left hactive
    (Real.rpow_nonneg hdelta.le _)

/-- The contraction ledger has the same paper upper bound as the
normalization width. -/
lemma wz1Lemma8_13_aspect_upper
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hnormalization :
      wz1Lemma8_13FaithfulNormalizationWidth input ≤
        3 * Real.rpow delta
          (-wz1Lemma8_13FaithfulEpsilonOne epsilon)) :
    wz1Lemma8_13FaithfulAspect input ≤
      3 * Real.rpow delta
        (-wz1Lemma8_13FaithfulEpsilonOne epsilon) := by
  dsimp only [wz1Lemma8_13FaithfulAspect]
  apply max_le
  · have hpower :
        1 ≤ Real.rpow delta
          (-wz1Lemma8_13FaithfulEpsilonOne epsilon) := by
      apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        hdelta hdeltaOne
      dsimp only [wz1Lemma8_13FaithfulEpsilonOne]
      have : 0 ≤ epsilon ^ 2 := sq_nonneg epsilon
      nlinarith
    nlinarith
  · exact hnormalization

/-- The Kaufman angular scale exactly cancels the affine normalization width. -/
lemma wz1Lemma8_13_normalizationWidth_mul_angularScale
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hdelta : 0 < delta) :
    wz1Lemma8_13FaithfulNormalizationWidth input *
        wz1Lemma8_13FaithfulAngularScale input =
      input.width := by
  have hactive :
      0 < wz1Lemma8_13FaithfulActiveWidth input := by
    exact hdelta.trans_le
      (wz1Lemma49_delta_le_activeCommonWidth
        input.density.1 input.base input.direction)
  have hnormalization :
      0 < wz1Lemma8_13FaithfulNormalizationWidth input := by
    dsimp only [wz1Lemma8_13FaithfulNormalizationWidth]
    exact mul_pos (Real.rpow_pos_of_pos hdelta _) hactive
  dsimp only [wz1Lemma8_13FaithfulAngularScale]
  field_simp [hnormalization.ne']

/-- Ratio form of the normalized angular scale. -/
lemma wz1Lemma8_13_angularScale_eq
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hdelta : 0 < delta) :
    wz1Lemma8_13FaithfulAngularScale input =
      Real.rpow delta
          (wz1Lemma8_13FaithfulEpsilonOne epsilon) *
        (input.width /
          wz1Lemma8_13FaithfulActiveWidth input) := by
  dsimp only [wz1Lemma8_13FaithfulAngularScale,
    wz1Lemma8_13FaithfulNormalizationWidth]
  have hpower :
      Real.rpow delta
          (-wz1Lemma8_13FaithfulEpsilonOne epsilon) =
        (Real.rpow delta
          (wz1Lemma8_13FaithfulEpsilonOne epsilon))⁻¹ :=
    Real.rpow_neg hdelta.le _
  rw [hpower]
  field_simp
    [(Real.rpow_pos_of_pos hdelta _).ne']

/-- The normalized strip side has the ratio form
`delta^epsilon₁ * (1 - width / activeWidth)`. -/
lemma wz1Lemma8_13_side_eq
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hdelta : 0 < delta) :
    wz1Lemma8_13FaithfulSide input =
      Real.rpow delta
          (wz1Lemma8_13FaithfulEpsilonOne epsilon) *
        (1 -
          input.width /
            wz1Lemma8_13FaithfulActiveWidth input) := by
  have hactive :
      0 < wz1Lemma8_13FaithfulActiveWidth input := by
    exact hdelta.trans_le
      (wz1Lemma49_delta_le_activeCommonWidth
        input.density.1 input.base input.direction)
  have hpower :
      Real.rpow delta
          (-wz1Lemma8_13FaithfulEpsilonOne epsilon) =
        (Real.rpow delta
          (wz1Lemma8_13FaithfulEpsilonOne epsilon))⁻¹ :=
    Real.rpow_neg hdelta.le _
  dsimp only [wz1Lemma8_13FaithfulSide,
    wz1Lemma8_13FaithfulNormalizationWidth]
  rw [hpower]
  field_simp
    [hactive.ne',
      (Real.rpow_pos_of_pos hdelta
        (wz1Lemma8_13FaithfulEpsilonOne epsilon)).ne']

/-- The residual large-width branch is exactly the small ratio estimate
`width / activeWidth < delta^(epsilon - epsilon₁)`. -/
lemma wz1Lemma8_13_width_div_active_lt_rpow
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hdelta : 0 < delta) :
    input.width / wz1Lemma8_13FaithfulActiveWidth input <
      Real.rpow delta
        (epsilon - wz1Lemma8_13FaithfulEpsilonOne epsilon) := by
  have hactive :
      0 < wz1Lemma8_13FaithfulActiveWidth input := by
    exact hdelta.trans_le
      (wz1Lemma49_delta_le_activeCommonWidth
        input.density.1 input.base input.direction)
  have hlarge := input.active_width_large
  change
    Real.rpow delta
        (-epsilon + wz1Lemma49AuxiliaryEpsilon epsilon) *
        input.width <
      wz1Lemma8_13FaithfulActiveWidth input at hlarge
  have hepsilonOne :
      wz1Lemma8_13FaithfulEpsilonOne epsilon =
        wz1Lemma49AuxiliaryEpsilon epsilon := by
    rfl
  have hpower :
      Real.rpow delta
          (-epsilon +
            wz1Lemma8_13FaithfulEpsilonOne epsilon) =
        (Real.rpow delta
          (epsilon -
            wz1Lemma8_13FaithfulEpsilonOne epsilon))⁻¹ := by
    rw [show
      -epsilon + wz1Lemma8_13FaithfulEpsilonOne epsilon =
        -(epsilon -
          wz1Lemma8_13FaithfulEpsilonOne epsilon) by ring]
    exact Real.rpow_neg hdelta.le _
  rw [← hepsilonOne, hpower] at hlarge
  have hpositive :
      0 <
        Real.rpow delta
          (epsilon -
            wz1Lemma8_13FaithfulEpsilonOne epsilon) :=
    Real.rpow_pos_of_pos hdelta _
  exact (div_lt_iff₀ hactive).2
    ((inv_mul_lt_iff₀ hpositive).1
      (by simpa [mul_comm] using hlarge))

/-- The residual branch makes the normalized angular scale smaller than
`delta^epsilon`. -/
lemma wz1Lemma8_13_angularScale_lt_rpow
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hdelta : 0 < delta) :
    wz1Lemma8_13FaithfulAngularScale input <
      Real.rpow delta epsilon := by
  have hactive :
      0 < wz1Lemma8_13FaithfulActiveWidth input := by
    exact hdelta.trans_le
      (wz1Lemma49_delta_le_activeCommonWidth
        input.density.1 input.base input.direction)
  have hnormalization :
      0 < wz1Lemma8_13FaithfulNormalizationWidth input := by
    dsimp only [wz1Lemma8_13FaithfulNormalizationWidth]
    exact mul_pos (Real.rpow_pos_of_pos hdelta _) hactive
  have hratio :
      input.width / wz1Lemma8_13FaithfulActiveWidth input <
        Real.rpow delta
          (epsilon -
            wz1Lemma8_13FaithfulEpsilonOne epsilon) :=
    wz1Lemma8_13_width_div_active_lt_rpow input hdelta
  have hfactor :
      Real.rpow delta
          (wz1Lemma8_13FaithfulEpsilonOne epsilon) *
        (input.width /
          wz1Lemma8_13FaithfulActiveWidth input) <
      Real.rpow delta epsilon := by
    calc
      Real.rpow delta
            (wz1Lemma8_13FaithfulEpsilonOne epsilon) *
          (input.width /
            wz1Lemma8_13FaithfulActiveWidth input)
          <
        Real.rpow delta
            (wz1Lemma8_13FaithfulEpsilonOne epsilon) *
          Real.rpow delta
            (epsilon -
              wz1Lemma8_13FaithfulEpsilonOne epsilon) := by
          exact mul_lt_mul_of_pos_left hratio
            (Real.rpow_pos_of_pos hdelta _)
      _ =
          Real.rpow delta
            (wz1Lemma8_13FaithfulEpsilonOne epsilon +
              (epsilon -
                wz1Lemma8_13FaithfulEpsilonOne epsilon)) :=
        (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta epsilon := by
        congr 1
        ring
  have hrewrite :=
    wz1Lemma8_13_angularScale_eq input hdelta
  rw [hrewrite]
  exact hfactor

/-- The common contraction ledger makes the affine fine scale no larger than
the Kaufman angular scale. -/
lemma wz1Lemma8_13_fineScale_le_angularScale
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hnormalization :
      0 < wz1Lemma8_13FaithfulNormalizationWidth input) :
    wz1Lemma8_13FaithfulFineScale input ≤
      wz1Lemma8_13FaithfulAngularScale input := by
  let normalizationWidth :=
    wz1Lemma8_13FaithfulNormalizationWidth input
  let aspect :=
    wz1Lemma8_13FaithfulAspect input
  have haspectOne : 1 ≤ aspect := by
    dsimp only [aspect, wz1Lemma8_13FaithfulAspect]
    exact le_max_left _ _
  have haspectPos : 0 < aspect :=
    zero_lt_one.trans_le haspectOne
  have hnormalizationAspect :
      normalizationWidth ≤ aspect := by
    dsimp only [normalizationWidth, aspect,
      wz1Lemma8_13FaithfulAspect]
    exact le_max_right _ _
  have hproduct :
      delta * normalizationWidth ≤
        input.width * (2 * aspect) := by
    calc
      delta * normalizationWidth ≤
          input.width * normalizationWidth :=
        mul_le_mul_of_nonneg_right input.delta_le_width
          hnormalization.le
      _ ≤ input.width * aspect :=
        mul_le_mul_of_nonneg_left hnormalizationAspect
          input.width_pos.le
      _ ≤ input.width * (2 * aspect) := by
        have : aspect ≤ 2 * aspect := by linarith
        exact mul_le_mul_of_nonneg_left this
          input.width_pos.le
  dsimp only [wz1Lemma8_13FaithfulFineScale,
    wz1Lemma8_13FaithfulAngularScale]
  exact
    (div_le_div_iff₀ (by
      simpa [aspect] using
        (mul_pos (by norm_num : (0 : ℝ) < 2) haspectPos))
      hnormalization).2
      (by
        simpa [normalizationWidth, aspect, mul_comm,
          mul_left_comm, mul_assoc] using hproduct)

/-- All numerical fields needed before constructing the fixed-viewpoint
affine package, including the exact hypotheses of
`strip_radial_projection_frostman`. -/
structure WZ1Lemma8_13FaithfulParameterWindow
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta) where
  normalizationWidth_pos :
    0 < wz1Lemma8_13FaithfulNormalizationWidth input
  normalizationWidth_upper :
    wz1Lemma8_13FaithfulNormalizationWidth input ≤
      3 * Real.rpow delta
        (-wz1Lemma8_13FaithfulEpsilonOne epsilon)
  normalizationWidth_lower :
    Real.rpow delta
        (1 - wz1Lemma8_13FaithfulEpsilonOne epsilon) ≤
      wz1Lemma8_13FaithfulNormalizationWidth input
  aspect_upper :
    wz1Lemma8_13FaithfulAspect input ≤
      3 * Real.rpow delta
        (-wz1Lemma8_13FaithfulEpsilonOne epsilon)
  width_le_eighth :
    input.width ≤ 1 / 8
  angularScale_pos :
    0 < wz1Lemma8_13FaithfulAngularScale input
  angularScale_le_quarter :
    wz1Lemma8_13FaithfulAngularScale input ≤ 1 / 4
  fineScale_pos :
    0 < wz1Lemma8_13FaithfulFineScale input
  fineScale_le_angular :
    wz1Lemma8_13FaithfulFineScale input ≤
      wz1Lemma8_13FaithfulAngularScale input
  selectionScale_pos :
    0 < wz1Lemma8_13FaithfulSelectionScale input
  delta_le_selectionScale :
    delta ≤ wz1Lemma8_13FaithfulSelectionScale input
  selectionScale_le_one :
    wz1Lemma8_13FaithfulSelectionScale input ≤ 1
  sourceScale_pos :
    0 < wz1Lemma8_13FaithfulSourceScale input
  sourceScale_le_one :
    wz1Lemma8_13FaithfulSourceScale input ≤ 1
  side_pos :
    0 < wz1Lemma8_13FaithfulSide input
  radial_threshold :
    wz1Lemma8_13FaithfulAngularScale input +
          4 * wz1Lemma8_13FaithfulAngularScale input /
            wz1Lemma8_13FaithfulSide input <
      wz1Lemma8_13FaithfulSourceScale input
  radial_angular_bound :
    wz1Lemma8_13FaithfulAngularScale input ≤
      (wz1Lemma8_13FaithfulSourceScale input -
          wz1Lemma8_13FaithfulAngularScale input -
          4 * wz1Lemma8_13FaithfulAngularScale input /
            wz1Lemma8_13FaithfulSide input) /
        (2 + 8 / wz1Lemma8_13FaithfulSide input)

/-- The complete faithful parameter window holds uniformly for every
sufficiently small residual input. -/
theorem wz1Lemma8_13_faithful_parameter_window :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
      ∃ delta₀ : ℝ,
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
          ∀ eta : ℝ,
            ∀ input :
              WZ1Lemma8_13ResidualInput delta epsilon eta,
              Nonempty
                (WZ1Lemma8_13FaithfulParameterWindow input) := by
  intro epsilon hepsilon hepsilonOne
  let epsilonOne :=
    wz1Lemma8_13FaithfulEpsilonOne epsilon
  let ratioGap := epsilon - epsilonOne
  let aspectGap := epsilon - 2 * epsilonOne
  have hepsilonOne : 0 < epsilonOne := by
    dsimp only [epsilonOne,
      wz1Lemma8_13FaithfulEpsilonOne]
    positivity
  have hratioGap : 0 < ratioGap := by
    dsimp only [ratioGap, epsilonOne,
      wz1Lemma8_13FaithfulEpsilonOne]
    have hepsilonSq : 0 < epsilon ^ 2 :=
      sq_pos_of_pos hepsilon
    nlinarith [mul_lt_mul_of_pos_left hepsilonOne hepsilon]
  have haspectGap : 0 < aspectGap := by
    dsimp only [aspectGap, epsilonOne,
      wz1Lemma8_13FaithfulEpsilonOne]
    have hepsilonSq : 0 < epsilon ^ 2 :=
      sq_pos_of_pos hepsilon
    nlinarith [mul_lt_mul_of_pos_left hepsilonOne hepsilon]
  rcases
      exists_delta_mul_rpow_le_rpow
        256 (by norm_num)
        (alpha := ratioGap) (beta := 0)
        (by linarith) with
    ⟨ratioScale, hratioScale, hratioScaleOne,
      hratioSmall⟩
  rcases
      exists_delta_mul_rpow_le_rpow
        384 (by norm_num)
        (alpha := aspectGap) (beta := 0)
        (by linarith) with
    ⟨aspectScale, haspectScale, haspectScaleOne,
      haspectSmall⟩
  rcases
      exists_delta_mul_rpow_le_rpow
        4 (by norm_num)
        (alpha := epsilon) (beta := 0)
        (by linarith) with
    ⟨angularScale, hangularScale, hangularScaleOne,
      hangularSmall⟩
  let delta₀ :=
    min ratioScale (min aspectScale angularScale)
  have hdelta₀ : 0 < delta₀ := by
    simp [delta₀, hratioScale, haspectScale,
      hangularScale]
  have hdelta₀One : delta₀ ≤ 1 :=
    (min_le_left _ _).trans hratioScaleOne
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hdeltaSmall eta input
  have hdeltaOne : delta ≤ 1 :=
    hdeltaSmall.trans hdelta₀One
  have hdeltaRatio : delta ≤ ratioScale :=
    hdeltaSmall.trans (min_le_left _ _)
  have hdeltaAspect : delta ≤ aspectScale :=
    hdeltaSmall.trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hdeltaAngular : delta ≤ angularScale :=
    hdeltaSmall.trans
      ((min_le_right _ _).trans (min_le_right _ _))
  let activeWidth :=
    wz1Lemma8_13FaithfulActiveWidth input
  let normalizationWidth :=
    wz1Lemma8_13FaithfulNormalizationWidth input
  let aspect :=
    wz1Lemma8_13FaithfulAspect input
  let ratio := input.width / activeWidth
  let power := Real.rpow delta epsilonOne
  have hactiveWidth : 0 < activeWidth := by
    dsimp only [activeWidth,
      wz1Lemma8_13FaithfulActiveWidth]
    exact hdelta.trans_le
      (wz1Lemma49_delta_le_activeCommonWidth
        input.density.1 input.base input.direction)
  have hratio : 0 < ratio := by
    dsimp only [ratio]
    exact div_pos input.width_pos hactiveWidth
  have hratioRaw :
      ratio < Real.rpow delta ratioGap := by
    dsimp only [ratio, ratioGap, epsilonOne]
    exact
      wz1Lemma8_13_width_div_active_lt_rpow
        input hdelta
  have hratioPower :
      256 * Real.rpow delta ratioGap ≤ 1 := by
    simpa using
      hratioSmall delta hdelta hdeltaRatio
  have hratioBound : ratio ≤ 1 / 256 := by
    have hpowerPos :
        0 < Real.rpow delta ratioGap :=
      Real.rpow_pos_of_pos hdelta _
    nlinarith
  have hratioThird : ratio ≤ 1 / 3 := by
    linarith
  have hratioHalf : ratio ≤ 1 / 2 := by
    linarith
  have hratioSixtyFour : ratio ≤ 1 / 64 := by
    linarith
  have hactiveUpper :
      activeWidth ≤ 2 + input.width := by
    dsimp only [activeWidth]
    exact
      wz1Lemma8_13_activeWidth_le_two_add_width input
  have hwidthActiveThird :
      input.width ≤ activeWidth / 3 := by
    dsimp only [ratio] at hratioThird
    have h :=
      (div_le_iff₀ hactiveWidth).1 hratioThird
    simpa [div_eq_mul_inv, mul_comm] using h
  have hactiveThree : activeWidth ≤ 3 := by
    linarith
  have hwidthOne : input.width ≤ 1 := by
    linarith
  have hwidthEighth : input.width ≤ 1 / 8 := by
    have hratioActive :
        ratio * activeWidth = input.width := by
      dsimp only [ratio]
      field_simp [hactiveWidth.ne']
    have hproduct :
        ratio * activeWidth ≤ (1 / 256) * 3 :=
      mul_le_mul hratioBound hactiveThree
        hactiveWidth.le (by norm_num)
    rw [hratioActive] at hproduct
    linarith
  have hnormalizationPos :
      0 < normalizationWidth := by
    dsimp only [normalizationWidth,
      wz1Lemma8_13FaithfulNormalizationWidth]
    exact mul_pos
      (Real.rpow_pos_of_pos hdelta _) hactiveWidth
  have hnormalizationUpper :
      normalizationWidth ≤
        3 * Real.rpow delta (-epsilonOne) := by
    dsimp only [normalizationWidth, epsilonOne]
    exact
      wz1Lemma8_13_normalizationWidth_upper
        input hdelta hwidthOne hdeltaOne
  have haspectOne : 1 ≤ aspect := by
    exact le_max_left _ _
  have hnormalizationAspect :
      normalizationWidth ≤ aspect := by
    exact le_max_right _ _
  have haspectPos : 0 < aspect :=
    zero_lt_one.trans_le haspectOne
  have hpower : 0 < power := by
    dsimp only [power]
    exact Real.rpow_pos_of_pos hdelta _
  have hpowerOne : power ≤ 1 := by
    dsimp only [power]
    exact Real.rpow_le_one hdelta.le hdeltaOne
      hepsilonOne.le
  have haspectRatio :
      aspect * ratio ≤ 1 / 128 := by
    have hratioSmallTerm : ratio ≤ 1 / 128 := by
      linarith
    have hnormalizationRatio :
        normalizationWidth * ratio ≤ 1 / 128 := by
      have hwidthRatio :
          input.width <
            activeWidth * Real.rpow delta ratioGap :=
        by
          simpa [mul_comm] using
            (div_lt_iff₀ hactiveWidth).1 hratioRaw
      have hscaledWidth :
          Real.rpow delta (-epsilonOne) *
              input.width <
            3 * Real.rpow delta aspectGap := by
        calc
          Real.rpow delta (-epsilonOne) *
                input.width
              <
            Real.rpow delta (-epsilonOne) *
              (activeWidth *
                Real.rpow delta ratioGap) := by
              exact mul_lt_mul_of_pos_left hwidthRatio
                (Real.rpow_pos_of_pos hdelta _)
          _ ≤
            Real.rpow delta (-epsilonOne) *
              (3 * Real.rpow delta ratioGap) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hactiveThree
                  (Real.rpow_nonneg hdelta.le _))
                (Real.rpow_nonneg hdelta.le _)
          _ =
            3 * Real.rpow delta aspectGap := by
              calc
                Real.rpow delta (-epsilonOne) *
                      (3 * Real.rpow delta ratioGap) =
                    3 *
                      (Real.rpow delta (-epsilonOne) *
                        Real.rpow delta ratioGap) := by ring
                _ =
                    3 * Real.rpow delta
                      (-epsilonOne + ratioGap) := by
                      exact congrArg (fun value : ℝ => 3 * value)
                        (Real.rpow_add hdelta
                          (-epsilonOne) ratioGap).symm
                _ = 3 * Real.rpow delta aspectGap := by
                      congr 2
                      dsimp only [aspectGap, ratioGap]
                      ring
      have haspectPower :
          384 * Real.rpow delta aspectGap ≤ 1 := by
        simpa using
          haspectSmall delta hdelta hdeltaAspect
      have hnormalizationRatioEq :
          normalizationWidth * ratio =
            Real.rpow delta (-epsilonOne) *
              input.width := by
        change
          (Real.rpow delta (-epsilonOne) * activeWidth) *
              (input.width / activeWidth) =
            Real.rpow delta (-epsilonOne) * input.width
        field_simp [hactiveWidth.ne']
      rw [hnormalizationRatioEq]
      nlinarith
    dsimp only [aspect,
      wz1Lemma8_13FaithfulAspect]
    rw [max_mul_of_nonneg _ _ hratio.le]
    exact max_le
      (by simpa using hratioSmallTerm)
      (by simpa [normalizationWidth] using
        hnormalizationRatio)
  have hselectionEq :
      wz1Lemma8_13FaithfulSelectionScale input =
        128 * (aspect * ratio) := by
    dsimp only [wz1Lemma8_13FaithfulSelectionScale,
      aspect, ratio, activeWidth]
    ring
  have hselectionPos :
      0 < wz1Lemma8_13FaithfulSelectionScale input := by
    rw [hselectionEq]
    positivity
  have hselectionUpper :
      wz1Lemma8_13FaithfulSelectionScale input ≤ 1 := by
    rw [hselectionEq]
    nlinarith
  have hdeltaRatioLower : delta / 3 ≤ ratio := by
    have hdeltaActive :
        delta * activeWidth ≤
          input.width * 3 := by
      calc
        delta * activeWidth ≤
            delta * 3 :=
          mul_le_mul_of_nonneg_left hactiveThree hdelta.le
        _ ≤ input.width * 3 :=
          mul_le_mul_of_nonneg_right
            input.delta_le_width (by norm_num)
    exact
      (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3)
        hactiveWidth).2 hdeltaActive
  have hselectionLower :
      delta ≤
        wz1Lemma8_13FaithfulSelectionScale input := by
    have haspectRatioLower : ratio ≤ aspect * ratio := by
      simpa [one_mul] using
        mul_le_mul_of_nonneg_right haspectOne hratio.le
    rw [hselectionEq]
    nlinarith
  have hsourceEq :
      wz1Lemma8_13FaithfulSourceScale input =
        64 * ratio := by
    dsimp only [wz1Lemma8_13FaithfulSourceScale,
      ratio, activeWidth]
    ring
  have hsourcePos :
      0 < wz1Lemma8_13FaithfulSourceScale input := by
    rw [hsourceEq]
    positivity
  have hsourceUpper :
      wz1Lemma8_13FaithfulSourceScale input ≤ 1 := by
    rw [hsourceEq]
    nlinarith
  have hangularPos :
      0 < wz1Lemma8_13FaithfulAngularScale input := by
    dsimp only [wz1Lemma8_13FaithfulAngularScale]
    exact div_pos input.width_pos hnormalizationPos
  have hangularUpperPower :
      wz1Lemma8_13FaithfulAngularScale input <
        Real.rpow delta epsilon :=
    wz1Lemma8_13_angularScale_lt_rpow input hdelta
  have hangularPower :
      4 * Real.rpow delta epsilon ≤ 1 := by
    simpa using
      hangularSmall delta hdelta hdeltaAngular
  have hangularQuarter :
      wz1Lemma8_13FaithfulAngularScale input ≤
        1 / 4 := by
    nlinarith
  have hfinePos :
      0 < wz1Lemma8_13FaithfulFineScale input := by
    dsimp only [wz1Lemma8_13FaithfulFineScale]
    positivity
  have hfineAngular :
      wz1Lemma8_13FaithfulFineScale input ≤
        wz1Lemma8_13FaithfulAngularScale input :=
    wz1Lemma8_13_fineScale_le_angularScale
      input hnormalizationPos
  have hradial :=
    wz1Lemma8_13_radial_scale_window
      hpower hpowerOne hratio hratioHalf
  have hangularEq :
      wz1Lemma8_13FaithfulAngularScale input =
        power * ratio := by
    dsimp only [power, epsilonOne]
    exact wz1Lemma8_13_angularScale_eq input hdelta
  have hsideEq :
      wz1Lemma8_13FaithfulSide input =
        power * (1 - ratio) := by
    dsimp only [power, epsilonOne]
    exact wz1Lemma8_13_side_eq input hdelta
  exact
    ⟨{
      normalizationWidth_pos := hnormalizationPos
      normalizationWidth_upper := by
        simpa [normalizationWidth, epsilonOne] using
          hnormalizationUpper
      normalizationWidth_lower :=
        wz1Lemma8_13_normalizationWidth_lower input hdelta
      aspect_upper := by
        exact wz1Lemma8_13_aspect_upper
          input hdelta hdeltaOne
            (by
              simpa [normalizationWidth, epsilonOne] using
                hnormalizationUpper)
      width_le_eighth := hwidthEighth
      angularScale_pos := hangularPos
      angularScale_le_quarter := hangularQuarter
      fineScale_pos := hfinePos
      fineScale_le_angular := hfineAngular
      selectionScale_pos := hselectionPos
      delta_le_selectionScale := hselectionLower
      selectionScale_le_one := hselectionUpper
      sourceScale_pos := hsourcePos
      sourceScale_le_one := hsourceUpper
      side_pos := by
        rw [hsideEq]
        exact hradial.1
      radial_threshold := by
        rw [hangularEq, hsideEq, hsourceEq]
        exact hradial.2.1
      radial_angular_bound := by
        rw [hangularEq, hsideEq, hsourceEq]
        exact hradial.2.2
    }⟩

end

end Kakeya.Assouad
