import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescalingStatements

/-!
# Canonical exact image-axis paper tube for the literal WZ2 rescaling

Construct the target tube directly from the image of the source axis under
`wz2PaperLiteralUnitRescalingMap`. The literal map applies a global factor
`1 / 100` in addition to the transverse `1 / rho` scaling.

The `1 / 100` global scalar cancels in direction normalization, so the
direction-verticality proof uses `unitRescalingLinear rho` directly. The
perpendicular norm bound is identical to the WZ1 map because the global
`1 / 100` and the transverse `1 / rho` combine to `1 / (100 * rho)`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Linear part of the literal paper unit-rescaling map. -/
def wz2PaperLiteralUnitRescalingLinear
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho) :
    Point3 →ₗ[ℝ] Point3 :=
  (1 / 100 : ℝ) • unitRescalingLinear
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor)
      rho

lemma wz2PaperLiteralUnitRescalingMap_sub
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) (point₁ point₂ : Point3) :
    wz2PaperLiteralUnitRescalingMap anchor hrho point₁ -
        wz2PaperLiteralUnitRescalingMap anchor hrho point₂ =
      wz2PaperLiteralUnitRescalingLinear anchor (point₁ - point₂) := by
  let anchorZero := wz1TubeAxisZeroPoint anchor
  let anchorDir := wz1PaperDirection anchor
  let hd := wz1PaperDirection_norm anchor
  have h :
      wz2PaperLiteralUnitRescalingMap anchor hrho point₁ -
          wz2PaperLiteralUnitRescalingMap anchor hrho point₂ =
        (1 / 100 : ℝ) •
          (unitRescalingMap anchorZero anchorDir hd rho hrho point₁ -
            unitRescalingMap anchorZero anchorDir hd rho hrho point₂) := by
    simp [wz2PaperLiteralUnitRescalingMap, smul_sub]
    <;> rfl
  rw [h]
  have h2 :
      unitRescalingMap anchorZero anchorDir hd rho hrho point₁ -
          unitRescalingMap anchorZero anchorDir hd rho hrho point₂ =
        unitRescalingLinear anchorDir hd rho (point₁ - point₂) := by
    simp [unitRescalingMap, unitRescalingLinear, map_sub]
    <;> rfl
  rw [h2]
  <;> rfl

lemma wz2PaperLiteralUnitRescalingMap_add
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) (point vector : Point3) :
    wz2PaperLiteralUnitRescalingMap anchor hrho (point + vector) =
      wz2PaperLiteralUnitRescalingMap anchor hrho point +
        wz2PaperLiteralUnitRescalingLinear anchor vector := by
  have hsub :=
    wz2PaperLiteralUnitRescalingMap_sub
      anchor hrho (point + vector) point
  have hdiff : point + vector - point = vector := by
    ext i; simp
  rw [hdiff] at hsub
  have h : wz2PaperLiteralUnitRescalingMap anchor hrho (point + vector) =
      wz2PaperLiteralUnitRescalingMap anchor hrho point +
        (wz2PaperLiteralUnitRescalingMap anchor hrho (point + vector) -
          wz2PaperLiteralUnitRescalingMap anchor hrho point) := by
    ext i; simp
  rw [h, hsub]

lemma wz2PaperLiteralUnitRescalingMap_coord2
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) (point : Point3) :
    (wz2PaperLiteralUnitRescalingMap anchor hrho point) 2 =
      (1 / 100 : ℝ) * inner ℝ
        (point - wz1TubeAxisZeroPoint anchor)
        (wz1PaperDirection anchor) := by
  simp [wz2PaperLiteralUnitRescalingMap, unitRescalingMap_coord2,
    PiLp.smul_apply, smul_eq_mul]

lemma wz2PaperLiteralUnitRescalingMap_image_range
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) (zero direction : Point3) :
    wz2PaperLiteralUnitRescalingMap anchor hrho ''
        Set.range (fun parameter : ℝ => zero + parameter • direction) =
      Set.range (fun parameter : ℝ =>
        wz2PaperLiteralUnitRescalingMap anchor hrho zero +
          parameter • wz2PaperLiteralUnitRescalingLinear anchor direction) := by
  ext point
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨sourcePoint, ⟨parameter, rfl⟩, rfl⟩
    refine ⟨parameter, ?_⟩
    rw [wz2PaperLiteralUnitRescalingMap_add, map_smul]
  · rintro ⟨parameter, rfl⟩
    refine ⟨zero + parameter • direction, ⟨parameter, rfl⟩, ?_⟩
    rw [wz2PaperLiteralUnitRescalingMap_add, map_smul]

lemma wz2PaperLiteralUnitRescalingLinear_perp_norm
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) (vector : Point3)
    (hperp : inner ℝ vector (wz1PaperDirection anchor) = 0) :
    ‖wz2PaperLiteralUnitRescalingLinear anchor vector‖ =
      ‖vector‖ / (100 * rho) := by
  let uLinear := unitRescalingLinear
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor) rho
  have hsmul_apply :
      wz2PaperLiteralUnitRescalingLinear anchor vector =
        (1 / 100 : ℝ) • (uLinear vector) := by rfl
  rw [hsmul_apply]
  have hbase : ‖uLinear vector‖ = ‖vector‖ / rho :=
    unitRescalingLinear_perp_norm
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor)
      rho hrho vector hperp
  rw [norm_smul, hbase]
  have habs : ‖(1 / 100 : ℝ)‖ = 1 / 100 := by
    simp [Real.norm_eq_abs]
  rw [habs]
  <;> field_simp [hrho.ne'] <;> ring

lemma wz2PaperLiteralUnitRescalingLinear_norm_le
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1) (v : Point3) :
    ‖wz2PaperLiteralUnitRescalingLinear anchor v‖ ≤
      ‖v‖ / (100 * rho) := by
  let uLinear := unitRescalingLinear
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor) rho
  have hsmul :
      wz2PaperLiteralUnitRescalingLinear anchor v =
        (1 / 100 : ℝ) • (uLinear v) := by
    rfl
  rw [hsmul]
  have hbase : ‖uLinear v‖ ≤ ‖v‖ / rho := by
    let rotation := householderToE3
        (wz1PaperDirection anchor)
        (wz1PaperDirection_norm anchor)
    have happly :
        uLinear v = transverseScaleLin rho (rotation v) := by
      simp [uLinear, unitRescalingLinear]
      <;> rfl
    rw [happly]
    have h2 :
        ‖transverseScaleLin rho (rotation v)‖ ≤
          (1 / rho) * ‖rotation v‖ :=
      transverseScaleLin_norm_bound rho hrho hrhoOne _
    have h3 : ‖rotation v‖ = ‖v‖ :=
      householderToE3_norm _ _ _
    rw [h3] at h2
    have h4 : (1 / rho) * ‖v‖ = ‖v‖ / rho := by
      field_simp [hrho.ne']
      <;> ring
    rw [h4] at h2
    exact h2
  rw [norm_smul]
  have habs : ‖(1 / 100 : ℝ)‖ = 1 / 100 := by
    simp [Real.norm_eq_abs]
  rw [habs]
  calc
    (1 / 100 : ℝ) * ‖uLinear v‖
        ≤ (1 / 100 : ℝ) * (‖v‖ / rho) := by gcongr
    _ = ‖v‖ / (100 * rho) := by
      field_simp [hrho.ne']
      <;> ring

lemma wz2PaperLiteralUnitRescalingLinear_injective
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    Function.Injective (wz2PaperLiteralUnitRescalingLinear anchor) := by
  let baseLinear := unitRescalingLinear
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor) rho
  have hinj : Function.Injective baseLinear := by
    let rotation := householderToE3
        (wz1PaperDirection anchor)
        (wz1PaperDirection_norm anchor)
    let scaling := transverseScaleLin rho
    have hrotation : Function.Injective rotation := rotation.injective
    have hscaling : Function.Injective scaling := by
      intro first second heq
      have h0 := congrArg (fun point : Point3 => point 0) heq
      have h1 := congrArg (fun point : Point3 => point 1) heq
      have h2 := congrArg (fun point : Point3 => point 2) heq
      rw [transverseScaleLin_coord0, transverseScaleLin_coord0] at h0
      rw [transverseScaleLin_coord1, transverseScaleLin_coord1] at h1
      rw [transverseScaleLin_coord2, transverseScaleLin_coord2] at h2
      apply PiLp.ext
      intro coordinate
      fin_cases coordinate
      · field_simp [hrho.ne'] at h0; exact h0
      · field_simp [hrho.ne'] at h1; exact h1
      · exact h2
    exact hscaling.comp hrotation
  intro first second heq
  have h1 : (1 / 100 : ℝ) • baseLinear first =
      (1 / 100 : ℝ) • baseLinear second := by
    simpa [wz2PaperLiteralUnitRescalingLinear] using heq
  have h2 : baseLinear first = baseLinear second := by
    simpa [smul_left_injective] using h1
  exact hinj h2

lemma literal_direction_ne_zero
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho) :
    wz2PaperLiteralUnitRescalingLinear anchor
        (wz1PaperDirection source) ≠ 0 := by
  intro hzero
  have hmapZero :
      wz2PaperLiteralUnitRescalingLinear anchor
          (wz1PaperDirection source) =
        wz2PaperLiteralUnitRescalingLinear anchor 0 := by
    simpa using hzero
  have hsourceZero :
      wz1PaperDirection source = 0 :=
    wz2PaperLiteralUnitRescalingLinear_injective
      anchor hrho hmapZero
  have hnorm := wz1PaperDirection_norm source
  rw [hsourceZero, norm_zero] at hnorm
  norm_num at hnorm

/--
The underlying `unitRescalingLinear rho` image of a covered source direction
is within distance `1/2` of `e3`.
-/
lemma literal_unitRescalingLinear_direction_close_e3
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hcover : WZ1PaperTubeCovers source anchor) :
    ‖unitRescalingLinear
        (wz1PaperDirection anchor)
        (wz1PaperDirection_norm anchor)
        rho
        (wz1PaperDirection source) - e3‖ ≤ 1 / 2 := by
  let rotation := householderToE3
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor)
  let scale := rho
  have hrotation_coarse :
      rotation (wz1PaperDirection anchor) = e3 :=
    householderToE3_sends_d_to_e3
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor)
  have hscale_e3 :
      transverseScaleLin scale e3 = e3 := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;>
      simp [transverseScaleLin_coord0, transverseScaleLin_coord1,
        transverseScaleLin_coord2, e3]
  have hsource_chord :
      ‖wz1PaperDirection source -
          wz1PaperDirection anchor‖ ≤ rho / 2 :=
    (unit_norm_sub_le_angle
      (wz1PaperDirection_norm source)
      (wz1PaperDirection_norm anchor)).trans
      hcover.components.2
  have hrotation_chord :
      ‖rotation
          (wz1PaperDirection source -
            wz1PaperDirection anchor)‖ ≤ rho / 2 := by
    rw [rotation.norm_map]
    exact hsource_chord
  have hrewrite :
      unitRescalingLinear
          (wz1PaperDirection anchor)
          (wz1PaperDirection_norm anchor)
          rho
          (wz1PaperDirection source) - e3 =
        transverseScaleLin scale
          (rotation
            (wz1PaperDirection source -
              wz1PaperDirection anchor)) := by
    calc
      unitRescalingLinear
          (wz1PaperDirection anchor)
          (wz1PaperDirection_norm anchor)
          rho
          (wz1PaperDirection source) - e3 =
          transverseScaleLin scale
                (rotation (wz1PaperDirection source)) -
            transverseScaleLin scale
                (rotation (wz1PaperDirection anchor)) := by
          rw [hrotation_coarse, hscale_e3] <;> rfl
      _ = transverseScaleLin scale
          (rotation (wz1PaperDirection source) -
            rotation (wz1PaperDirection anchor)) := by
        exact (map_sub (transverseScaleLin scale)
          (rotation (wz1PaperDirection source))
          (rotation (wz1PaperDirection anchor))).symm
      _ = transverseScaleLin scale
          (rotation
            (wz1PaperDirection source -
              wz1PaperDirection anchor)) := by
        exact congrArg (transverseScaleLin scale)
          (map_sub rotation
            (wz1PaperDirection source)
            (wz1PaperDirection anchor)).symm
  rw [hrewrite]
  calc
    ‖transverseScaleLin scale
        (rotation
          (wz1PaperDirection source -
            wz1PaperDirection anchor))‖
        ≤ (1 / scale) *
            ‖rotation
              (wz1PaperDirection source -
                wz1PaperDirection anchor)‖ :=
      transverseScaleLin_norm_bound scale hrho hrhoOne _
    _ ≤ (1 / scale) * (rho / 2) := by gcongr
    _ = 1 / 2 := by
      dsimp only [scale]
      field_simp [hrho.ne'] <;> ring

/--
Norm bounds for the underlying `unitRescalingLinear rho` image direction.
-/
private lemma literal_unitRescalingLinear_direction_norm_bounds
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hcover : WZ1PaperTubeCovers source anchor) :
    1 / 2 ≤
        ‖unitRescalingLinear
          (wz1PaperDirection anchor)
          (wz1PaperDirection_norm anchor)
          rho
          (wz1PaperDirection source)‖ ∧
      ‖unitRescalingLinear
          (wz1PaperDirection anchor)
          (wz1PaperDirection_norm anchor)
          rho
          (wz1PaperDirection source)‖ ≤ 3 / 2 := by
  let u := unitRescalingLinear
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor)
      rho
      (wz1PaperDirection source)
  have hclose :=
    literal_unitRescalingLinear_direction_close_e3
      hrho hrhoOne hcover
  constructor
  · have hreverse :
        ‖e3‖ - ‖u‖ ≤ ‖e3 - u‖ :=
      norm_sub_norm_le e3 u
    rw [e3_norm, norm_sub_rev] at hreverse
    linarith
  · calc
      ‖u‖ ≤ ‖u - e3‖ + ‖e3‖ := by
        have := norm_add_le (u - e3) e3
        simpa only [sub_add_cancel] using this
      _ ≤ 3 / 2 := by rw [e3_norm]; linarith

/--
The literal WZ image of a covered source direction has length at most
`3 / 200`.  This public wrapper is used when rediscretizing the exact affine
image into an ordinary unit-segment tube.
-/
theorem wz2PaperLiteralUnitRescalingLinear_sourceDirection_norm_le
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hcover : WZ1PaperTubeCovers source anchor) :
    ‖wz2PaperLiteralUnitRescalingLinear anchor source.direction‖ ≤
      3 / 200 := by
  have hpaper :
      ‖wz2PaperLiteralUnitRescalingLinear anchor
          (wz1PaperDirection source)‖ ≤
        3 / 200 := by
    have hbounds :=
      literal_unitRescalingLinear_direction_norm_bounds
        hrho hrhoOne hcover
    change
      ‖(1 / 100 : ℝ) •
          unitRescalingLinear
            (wz1PaperDirection anchor)
            (wz1PaperDirection_norm anchor)
            rho
            (wz1PaperDirection source)‖ ≤
        3 / 200
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    nlinarith [hbounds.2]
  unfold wz1PaperDirection at hpaper
  split at hpaper
  · exact hpaper
  · simpa using hpaper

/--
The normalized literal image direction has vertical coordinate at least `1/2`.

Since the global `1 / 100` scalar cancels in normalization, this reduces to
the same bound as the non-literal proof: `inner ≥ 7/8` and `‖u‖ ≤ 3/2` give
normalized coord2 `≥ (7/8) / (3/2) = 7/12 > 1/2`.
-/
private lemma literal_normalized_direction_vertical
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hcover : WZ1PaperTubeCovers source anchor) :
    1 / 2 ≤
      (NormedSpace.normalize
        (wz2PaperLiteralUnitRescalingLinear anchor
          (wz1PaperDirection source))) (2 : Fin 3) := by
  let u := unitRescalingLinear
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor)
      rho
      (wz1PaperDirection source)
  let literalImage := wz2PaperLiteralUnitRescalingLinear anchor
      (wz1PaperDirection source)
  have hliteral_def : literalImage = (1 / 100 : ℝ) • u := by rfl
  have hnormalize_same :
      NormedSpace.normalize literalImage = NormedSpace.normalize u := by
    rw [hliteral_def]
    rw [NormedSpace.normalize_smul_of_pos (by norm_num : (0 : ℝ) < 1 / 100)]
  rw [hnormalize_same]
  have hinner :
      7 / 8 ≤ inner ℝ (wz1PaperDirection source)
          (wz1PaperDirection anchor) :=
    wz1PaperTubeCovers.inner_direction_ge_seven_eighths
      hrhoOne hcover
  have hcoord : u (2 : Fin 3) =
      inner ℝ (wz1PaperDirection source)
        (wz1PaperDirection anchor) :=
    unitRescalingLinear_coord2
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor) rho _
  have hcoordPos : 0 < u (2 : Fin 3) := by
    rw [hcoord]
    linarith
  have hnormBounds :=
    literal_unitRescalingLinear_direction_norm_bounds
      hrho hrhoOne hcover
  have hnormPos : 0 < ‖u‖ := by linarith [hnormBounds.1]
  change 1 / 2 ≤ (‖u‖⁻¹ • u) (2 : Fin 3)
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ hnormPos).mpr (by
    rw [hcoord]
    nlinarith [hnormBounds.2])

private lemma literal_orthogonal_section_image_horizontal_norm_le
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hcover : WZ1PaperTubeCovers source anchor) :
    ‖wz2PaperLiteralUnitRescalingMap anchor hrho
        (wz1PaperOrthogonalSectionPoint source anchor)‖ ≤
      3 / 200 := by
  let sourcePoint :=
    wz1PaperOrthogonalSectionPoint source anchor
  let sourceZero := wz1TubeAxisZeroPoint source
  let anchorZero := wz1TubeAxisZeroPoint anchor
  let sourceDirection := wz1PaperDirection source
  let parameter :=
    wz1PaperOrthogonalSectionParameter source anchor
  have hparameter : |parameter| ≤ rho := by
    exact abs_wz1PaperOrthogonalSectionParameter_le
      hrho hrhoOne hcover
  have hzero :
      dist sourceZero anchorZero ≤ rho / 2 :=
    hcover.components.1
  have hsourcePoint :
      sourcePoint = sourceZero + parameter • sourceDirection := rfl
  have hsourceDistance :
      ‖sourcePoint - anchorZero‖ ≤ 3 * rho / 2 := by
    rw [hsourcePoint]
    have hrewrite :
        sourceZero + parameter • sourceDirection - anchorZero =
          (sourceZero - anchorZero) + parameter • sourceDirection := by
      ext i; simp <;> ring
    rw [hrewrite]
    calc
      ‖(sourceZero - anchorZero) + parameter • sourceDirection‖
          ≤ ‖sourceZero - anchorZero‖ +
              ‖parameter • sourceDirection‖ := norm_add_le _ _
      _ = dist sourceZero anchorZero + |parameter| := by
        rw [dist_eq_norm, norm_smul,
          wz1PaperDirection_norm, mul_one]
        simp only [Real.norm_eq_abs]
      _ ≤ 3 * rho / 2 := by linarith
  have hinner :=
    wz1PaperTubeCovers.inner_direction_ge_seven_eighths
      hrhoOne hcover
  have hinnerNe :
      inner ℝ sourceDirection (wz1PaperDirection anchor) ≠ 0 := by
    dsimp only [sourceDirection]
    linarith
  have hperp :
      inner ℝ (sourcePoint - anchorZero)
        (wz1PaperDirection anchor) = 0 := by
    exact wz1PaperOrthogonalSectionPoint_perp hinnerNe
  have hmapDifference :
      wz2PaperLiteralUnitRescalingMap anchor hrho sourcePoint =
        wz2PaperLiteralUnitRescalingLinear anchor
          (sourcePoint - anchorZero) := by
    have hzeroMap :
        wz2PaperLiteralUnitRescalingMap anchor hrho anchorZero = 0 := by
      dsimp only [anchorZero]
      simp [wz2PaperLiteralUnitRescalingMap, unitRescalingMap]
    have hsub :=
      wz2PaperLiteralUnitRescalingMap_sub
        anchor hrho sourcePoint anchorZero
    rw [hzeroMap, sub_zero] at hsub
    exact hsub
  rw [hmapDifference,
    wz2PaperLiteralUnitRescalingLinear_perp_norm
      anchor hrho _ hperp]
  calc
    ‖sourcePoint - anchorZero‖ / (100 * rho)
        ≤ (3 * rho / 2) / (100 * rho) := by gcongr
    _ = 3 / 200 := by
      field_simp [hrho.ne'] <;> ring

lemma literal_canonical_rescaled_axis
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho) :
    let imageDirection :=
      wz2PaperLiteralUnitRescalingLinear anchor
        (wz1PaperDirection source)
    let sourcePoint :=
      wz1PaperOrthogonalSectionPoint source anchor
    let target : Kakeya.DeltaTube (delta / rho) :=
      { base :=
          wz2PaperLiteralUnitRescalingMap anchor hrho sourcePoint
        direction := NormedSpace.normalize imageDirection
        direction_unit := by
          apply NormedSpace.norm_normalize
          exact literal_direction_ne_zero hrho }
    tubeAxisLine target =
      wz2PaperLiteralUnitRescalingMap anchor hrho ''
        tubeAxisLine source := by
  dsimp only
  let imageDirection :=
    wz2PaperLiteralUnitRescalingLinear anchor
      (wz1PaperDirection source)
  let sourcePoint :=
    wz1PaperOrthogonalSectionPoint source anchor
  let targetBase :=
    wz2PaperLiteralUnitRescalingMap anchor hrho sourcePoint
  have himageNe : imageDirection ≠ 0 := by
    exact literal_direction_ne_zero hrho
  have hsourcePointAxis :
      sourcePoint ∈ tubeAxisLine source :=
    wz1PaperOrthogonalSectionPoint_mem_axis source anchor
  ext point
  constructor
  · rintro ⟨parameter, rfl⟩
    have hnormalize :
        NormedSpace.normalize imageDirection =
          ‖imageDirection‖⁻¹ • imageDirection := rfl
    let sourceParameter := parameter * ‖imageDirection‖⁻¹
    let sourceAxisPoint :=
      sourcePoint + sourceParameter • wz1PaperDirection source
    have hsourceAxisPoint :
        sourceAxisPoint ∈ tubeAxisLine source := by
      rcases hsourcePointAxis with ⟨offset, hoffset⟩
      refine ⟨offset +
          (if 0 ≤ source.direction (2 : Fin 3)
            then sourceParameter else -sourceParameter), ?_⟩
      unfold sourceAxisPoint wz1PaperDirection
      split_ifs with hsign
      · rw [hoffset] <;> module
      · rw [hoffset] <;> module
    refine ⟨sourceAxisPoint, hsourceAxisPoint, ?_⟩
    rw [wz2PaperLiteralUnitRescalingMap_add]
    dsimp only [sourceAxisPoint, sourceParameter, targetBase,
      imageDirection]
    rw [map_smul, hnormalize]
    <;> module
  · rintro ⟨sourceAxisPoint, hsourceAxisPoint, rfl⟩
    rcases hsourcePointAxis with ⟨sourceOffset, hsourceOffset⟩
    rcases hsourceAxisPoint with ⟨pointOffset, hpointOffset⟩
    let signedDifference : ℝ :=
      if 0 ≤ source.direction (2 : Fin 3)
      then pointOffset - sourceOffset
      else sourceOffset - pointOffset
    have hpoint :
        sourceAxisPoint =
          sourcePoint +
            signedDifference • wz1PaperDirection source := by
      unfold signedDifference wz1PaperDirection
      split_ifs with hsign
      · rw [hpointOffset, hsourceOffset] <;> module
      · rw [hpointOffset, hsourceOffset] <;> module
    rw [hpoint, wz2PaperLiteralUnitRescalingMap_add, map_smul]
    refine ⟨signedDifference * ‖imageDirection‖, ?_⟩
    have hnormalize :
        NormedSpace.normalize imageDirection =
          ‖imageDirection‖⁻¹ • imageDirection := rfl
    have hnormNe : ‖imageDirection‖ ≠ 0 :=
      norm_ne_zero_iff.mpr himageNe
    change
      wz2PaperLiteralUnitRescalingMap anchor hrho sourcePoint +
          signedDifference • imageDirection =
        targetBase +
          (signedDifference * ‖imageDirection‖) •
            NormedSpace.normalize imageDirection
    rw [hnormalize]
    dsimp only [targetBase]
    have hcancel :
        ‖imageDirection‖ * ‖imageDirection‖⁻¹ = 1 := by
      exact mul_inv_cancel₀ hnormNe
    rw [smul_smul]
    have hcoeff :
        (signedDifference * ‖imageDirection‖) *
            ‖imageDirection‖⁻¹ =
          signedDifference := by
      rw [mul_assoc, hcancel, mul_one]
    rw [hcoeff]

theorem wz2_paper_literal_canonical_unit_rescaled_tube_from_geometry :
    WZ2PaperLiteralCanonicalUnitRescaledTubeStatement := by
  intro delta rho hrho hrhoOne source anchor
    hsource hanchor hcover
  let imageDirection :=
    wz2PaperLiteralUnitRescalingLinear anchor
      (wz1PaperDirection source)
  let sourcePoint :=
    wz1PaperOrthogonalSectionPoint source anchor
  have himageNe : imageDirection ≠ 0 := by
    exact literal_direction_ne_zero hrho
  let target : Kakeya.DeltaTube (delta / rho) :=
    { base :=
        wz2PaperLiteralUnitRescalingMap anchor hrho sourcePoint
      direction := NormedSpace.normalize imageDirection
      direction_unit := NormedSpace.norm_normalize himageNe }
  have htargetVertical :
      1 / 2 ≤ wz1PaperDirection target (2 : Fin 3) := by
    have hnormalizedVertical :=
      literal_normalized_direction_vertical hrho hrhoOne hcover
    have hstoredVertical :
        0 < target.direction (2 : Fin 3) := by
      dsimp only [target, imageDirection]
      linarith
    unfold wz1PaperDirection
    rw [if_pos hstoredVertical.le]
    exact hnormalizedVertical
  have htargetZero :
      wz1TubeAxisZeroPoint target = target.base := by
    have hvertical : target.direction (2 : Fin 3) ≠ 0 := by
      have hstoredVertical :
          0 < target.direction (2 : Fin 3) := by
        have hnormalizedVertical :=
          literal_normalized_direction_vertical hrho hrhoOne hcover
        dsimp only [target, imageDirection]
        linarith
      exact hstoredVertical.ne'
    have hbaseTwo : target.base (2 : Fin 3) = 0 := by
      dsimp only [target, sourcePoint]
      rw [wz2PaperLiteralUnitRescalingMap_coord2]
      have hinner :
          inner ℝ (wz1PaperDirection source)
            (wz1PaperDirection anchor) ≠ 0 := by
        have h :=
          wz1PaperTubeCovers.inner_direction_ge_seven_eighths
            hrhoOne hcover
        linarith
      have hperp := wz1PaperOrthogonalSectionPoint_perp hinner
      rw [hperp]
      <;> ring
    simp [wz1TubeAxisZeroPoint, hbaseTwo, hvertical]
  have hbaseNorm :
      ‖target.base‖ ≤ 3 / 200 := by
    dsimp only [target, sourcePoint]
    exact literal_orthogonal_section_image_horizontal_norm_le
      hrho hrhoOne hcover
  have hcoord0 :
      |wz1TubeAxisZeroPoint target (0 : Fin 3)| ≤ 1 / 3 := by
    rw [htargetZero]
    have hcoord : |target.base (0 : Fin 3)| ≤ ‖target.base‖ := by
      simpa [Real.norm_eq_abs] using
        PiLp.norm_apply_le target.base (0 : Fin 3)
    exact hcoord.trans (hbaseNorm.trans (by norm_num))
  have hcoord1 :
      |wz1TubeAxisZeroPoint target (1 : Fin 3)| ≤ 1 / 3 := by
    rw [htargetZero]
    have hcoord : |target.base (1 : Fin 3)| ≤ ‖target.base‖ := by
      simpa [Real.norm_eq_abs] using
        PiLp.norm_apply_le target.base (1 : Fin 3)
    exact hcoord.trans (hbaseNorm.trans (by norm_num))
  refine ⟨{
    target := target
    target_line_class := ⟨htargetVertical, hcoord0, hcoord1⟩
    target_axis := ?_ }⟩
  exact literal_canonical_rescaled_axis hrho

theorem wz2_paper_literal_canonical_unit_rescaled_tube :
    WZ2PaperLiteralCanonicalUnitRescaledTubeStatement :=
  wz2_paper_literal_canonical_unit_rescaled_tube_from_geometry

/-- Determinant of the literal WZ2 rescaling linear map.

The map scales all three coordinates by `1/100` and the two transverse
coordinates by an additional `1/rho`, so the determinant is
`(1/100)^3 * (1/rho)^2`. -/
lemma wz2PaperLiteralUnitRescalingLinear_det
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho) :
    |LinearMap.det (wz2PaperLiteralUnitRescalingLinear anchor)| =
      (1 / 100 : ℝ) ^ 3 * (1 / rho) ^ 2 := by
  let lineDir := wz1PaperDirection anchor
  let hd := wz1PaperDirection_norm anchor
  have h1 : wz2PaperLiteralUnitRescalingLinear anchor =
      (1 / 100 : ℝ) • unitRescalingLinear lineDir hd rho := by
    rfl
  rw [h1]
  have h2 : LinearMap.det ((1 / 100 : ℝ) • unitRescalingLinear lineDir hd rho) =
      (1 / 100 : ℝ) ^ 3 * LinearMap.det (unitRescalingLinear lineDir hd rho) := by
    rw [LinearMap.det_smul (1 / 100 : ℝ) (unitRescalingLinear lineDir hd rho)]
    have hfinrank : Module.finrank ℝ Point3 = 3 := by simp
    rw [hfinrank]
    <;> norm_num
  rw [h2]
  have h3 : |LinearMap.det (unitRescalingLinear lineDir hd rho)| = (1 / rho) ^ 2 := by
    have h1 : LinearMap.det (unitRescalingLinear lineDir hd rho) =
        LinearMap.det (transverseScaleLin rho) *
        LinearMap.det (householderToE3 lineDir hd).toLinearMap := by
      simp [unitRescalingLinear, LinearMap.det_comp] <;> ring
    rw [h1, transverseScaleLin_det rho hrho]
    rw [abs_mul, householderToE3_abs_det lineDir hd]
    have hpos : 0 ≤ (1 / rho) ^ 2 := by positivity
    rw [abs_of_nonneg hpos] <;> ring
  have h4 : |(1 / 100 : ℝ) ^ 3 * LinearMap.det (unitRescalingLinear lineDir hd rho)| =
      |(1 / 100 : ℝ) ^ 3| * |LinearMap.det (unitRescalingLinear lineDir hd rho)| := by
    rw [abs_mul]
  rw [h4, h3]
  have h5 : 0 ≤ (1 / 100 : ℝ) ^ 3 := by positivity
  rw [abs_of_nonneg h5] <;> ring

end Kakeya.Assouad

end
