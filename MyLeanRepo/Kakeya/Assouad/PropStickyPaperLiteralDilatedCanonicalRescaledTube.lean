import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralDilatedCanonicalRescaledTubeStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralCanonicalRescaledTube
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCanonicalDilatedDirection

/-!
# Canonical exact image-axis literal tube from a doubled-anchor cover

The paper fiber tree only places an intermediate source tube in the doubled
anchor. This module proves that the normalized literal image direction still
lies in the positive `L₃` cone and that the image base remains in the fixed
horizontal window.
-/

noncomputable section

namespace Kakeya.Assouad

private lemma dilated_literal_polynomial_bound
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 ≤ (1 + 3 * x) * (1 - x / 2) ^ 2 := by
  have h :
      (1 + 3 * x) * (1 - x / 2) ^ 2 - 1 =
        x * (3 * x - 8) * (x - 1) / 4 := by
    ring
  have hpos : 0 ≤ x * (3 * x - 8) * (x - 1) := by
    have hsecond : 3 * x - 8 ≤ 0 := by linarith
    have hthird : x - 1 ≤ 0 := by linarith
    have hproduct : 0 ≤ (3 * x - 8) * (x - 1) := by
      nlinarith
    nlinarith
  linarith [div_nonneg hpos (by norm_num : (0 : ℝ) ≤ 4)]

private lemma point3_coord2_eq_inner_e3 (vector : Point3) :
    inner ℝ vector e3 = vector (2 : Fin 3) := by
  simp [e3, PiLp.inner_apply]
  <;> ring

private lemma dilated_literal_normalized_direction_vertical
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hcover : WZ2PaperDilatedTubeCovers 2 source anchor) :
    1 / 2 ≤
      (NormedSpace.normalize
        (wz2PaperLiteralUnitRescalingLinear anchor
          (wz1PaperDirection source))) (2 : Fin 3) := by
  let unitImage :=
    unitRescalingLinear
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor)
      rho
      (wz1PaperDirection source)
  let literalImage :=
    wz2PaperLiteralUnitRescalingLinear anchor
      (wz1PaperDirection source)
  have hliteralDef :
      literalImage = (1 / 100 : ℝ) • unitImage := by
    rfl
  have hnormalize :
      NormedSpace.normalize literalImage =
        NormedSpace.normalize unitImage := by
    rw [hliteralDef]
    rw [NormedSpace.normalize_smul_of_pos
      (by norm_num : (0 : ℝ) < 1 / 100)]
  rw [hnormalize]
  set cosine :=
    inner ℝ
      (wz1PaperDirection source)
      (wz1PaperDirection anchor) with hcosine
  have hcoord :
      unitImage (2 : Fin 3) = cosine :=
    unitRescalingLinear_coord2
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor) rho _
  have hcosineHalf : 1 / 2 ≤ cosine :=
    hcover.inner_direction_ge_half hrhoOne
  have hcosinePos : 0 < cosine := by linarith
  let angle :=
    InnerProductGeometry.angle
      (wz1PaperDirection source)
      (wz1PaperDirection anchor)
  have hangleLe : angle ≤ rho := hcover.components.2
  have hangleNonneg : 0 ≤ angle :=
    InnerProductGeometry.angle_nonneg _ _
  have hcosineEq : cosine = Real.cos angle := by
    simp only [hcosine]
    exact
      InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one
        (wz1PaperDirection_norm source)
        (wz1PaperDirection_norm anchor)
  have hcosineLower : cosine ≥ 1 - rho ^ 2 / 2 := by
    have hcosineMonotone : Real.cos angle ≥ Real.cos rho := by
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      <;> linarith [Real.pi_pos, Real.pi_gt_three]
    have hcosineRho :
        1 - rho ^ 2 / 2 ≤ Real.cos rho :=
      Real.one_sub_sq_div_two_le_cos
    linarith
  have hbaseNonneg : 0 ≤ 1 - rho ^ 2 / 2 := by
    nlinarith
  have hpolynomial :
      1 ≤ cosine ^ 2 * (1 + 3 * rho ^ 2) := by
    have hsquare :
        (1 - rho ^ 2 / 2) ^ 2 ≤ cosine ^ 2 := by
      gcongr
    have hbound :
        1 ≤
          (1 + 3 * rho ^ 2) *
            (1 - rho ^ 2 / 2) ^ 2 :=
      dilated_literal_polynomial_bound
        (by positivity) (by nlinarith)
    nlinarith
  let rotation :=
    householderToE3
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor)
  let rotatedSource :=
    rotation (wz1PaperDirection source)
  have hrotatedNorm : ‖rotatedSource‖ = 1 := by
    rw [householderToE3_norm, wz1PaperDirection_norm]
  have hunitImage :
      unitImage = transverseScaleLin rho rotatedSource := by
    simp [unitImage, unitRescalingLinear, rotatedSource]
    <;> rfl
  have hrotatedCoord :
      rotatedSource (2 : Fin 3) = cosine := by
    have hsame :
        unitImage (2 : Fin 3) =
          rotatedSource (2 : Fin 3) := by
      rw [hunitImage, transverseScaleLin_coord2]
    linarith
  have htransverseRotated :
      ‖transversePart rotatedSource‖ ^ 2 =
        1 - cosine ^ 2 := by
    have hdecomposition :
        rotatedSource =
          transversePart rotatedSource + cosine • e3 := by
      apply PiLp.ext
      intro coordinate
      fin_cases coordinate <;>
        simp [transversePart_coord0, transversePart_coord1,
          transversePart_coord2, hrotatedCoord, e3,
          PiLp.add_apply, PiLp.smul_apply]
    have horthogonal :
        inner ℝ (transversePart rotatedSource)
            (cosine • e3) = 0 := by
      rw [inner_smul_right]
      have h :
          inner ℝ (transversePart rotatedSource) e3 = 0 := by
        rw [point3_coord2_eq_inner_e3, transversePart_coord2]
        <;> ring
      rw [h]
      <;> ring
    have hpythagoras :=
      norm_add_sq_eq_norm_sq_add_norm_sq_real horthogonal
    rw [← hdecomposition, hrotatedNorm] at hpythagoras
    have hcosineNorm : ‖cosine • e3‖ = cosine := by
      rw [norm_smul, e3_norm, mul_one]
      simp [Real.norm_eq_abs, abs_of_pos hcosinePos]
    rw [hcosineNorm] at hpythagoras
    nlinarith
  have htransverseUnit :
      ‖transversePart unitImage‖ ^ 2 =
        (1 - cosine ^ 2) / rho ^ 2 := by
    have htransverse :
        transversePart unitImage =
          transverseScaleLin rho
            (transversePart rotatedSource) := by
      simp [unitImage, unitRescalingLinear,
        transversePart_transverseScaleLin, rotatedSource]
      <;> rfl
    rw [htransverse]
    have hnorm :
        ‖transverseScaleLin rho
            (transversePart rotatedSource)‖ =
          ‖transversePart rotatedSource‖ / rho :=
      transverseScaleLin_norm_of_coord2_zero rho hrho _
        (by simp [transversePart_coord2])
    rw [hnorm, div_pow, htransverseRotated]
  have hunitNorm :
      ‖unitImage‖ ^ 2 =
        cosine ^ 2 + (1 - cosine ^ 2) / rho ^ 2 := by
    have hdecomposition :
        unitImage =
          transversePart unitImage +
            (unitImage (2 : Fin 3)) • e3 := by
      apply PiLp.ext
      intro coordinate
      fin_cases coordinate <;>
        simp [transversePart_coord0, transversePart_coord1,
          transversePart_coord2, e3, PiLp.add_apply,
          PiLp.smul_apply]
    have horthogonal :
        inner ℝ (transversePart unitImage)
            ((unitImage (2 : Fin 3)) • e3) = 0 := by
      rw [inner_smul_right]
      have h :
          inner ℝ (transversePart unitImage) e3 = 0 := by
        rw [point3_coord2_eq_inner_e3, transversePart_coord2]
        <;> ring
      rw [h]
      <;> ring
    have hpythagoras :
        ‖unitImage‖ ^ 2 =
          ‖transversePart unitImage‖ ^ 2 +
            (unitImage (2 : Fin 3)) ^ 2 := by
      have h1 :
          ‖unitImage‖ ^ 2 =
            ‖transversePart unitImage +
                (unitImage (2 : Fin 3)) • e3‖ ^ 2 :=
        congrArg (fun vector : Point3 => ‖vector‖ ^ 2)
          hdecomposition
      have h3 :
          ‖transversePart unitImage +
                (unitImage (2 : Fin 3)) • e3‖ *
              ‖transversePart unitImage +
                (unitImage (2 : Fin 3)) • e3‖ =
            ‖transversePart unitImage‖ *
                ‖transversePart unitImage‖ +
              ‖(unitImage (2 : Fin 3)) • e3‖ *
                ‖(unitImage (2 : Fin 3)) • e3‖ :=
        norm_add_sq_eq_norm_sq_add_norm_sq_real horthogonal
      clear hdecomposition
      have h2 :
          ‖transversePart unitImage +
                (unitImage (2 : Fin 3)) • e3‖ ^ 2 =
            ‖transversePart unitImage‖ ^ 2 +
              ‖(unitImage (2 : Fin 3)) • e3‖ ^ 2 := by
        convert h3 using 1 <;> ring
      have h4 :
          ‖(unitImage (2 : Fin 3)) • e3‖ ^ 2 =
            (unitImage (2 : Fin 3)) ^ 2 := by
        simp [norm_smul, e3_norm]
      rw [h1, h2, h4]
    rw [hcoord, htransverseUnit] at hpythagoras
    linarith
  have hunitNormLe : ‖unitImage‖ ≤ 2 * cosine := by
    have hfraction :
        (1 - cosine ^ 2) / rho ^ 2 ≤ 3 * cosine ^ 2 := by
      have hnumerator :
          1 - cosine ^ 2 ≤
            3 * rho ^ 2 * cosine ^ 2 := by
        nlinarith
      exact (div_le_iff₀ (sq_pos_of_pos hrho)).mpr (by
        nlinarith)
    have hsquare :
        ‖unitImage‖ ^ 2 ≤ (2 * cosine) ^ 2 := by
      rw [hunitNorm]
      nlinarith
    nlinarith [norm_nonneg unitImage]
  have hunitNe : unitImage ≠ 0 := by
    intro hzero
    have : unitImage (2 : Fin 3) = 0 := by rw [hzero]; rfl
    linarith
  have hnormPos : 0 < ‖unitImage‖ := norm_pos_iff.mpr hunitNe
  change 1 / 2 ≤ (‖unitImage‖⁻¹ • unitImage) (2 : Fin 3)
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [inv_mul_eq_div, hcoord]
  exact (le_div_iff₀ hnormPos).mpr (by linarith)

private lemma dilated_literal_abs_parameter_le
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hcover : WZ2PaperDilatedTubeCovers 2 source anchor) :
    |wz1PaperOrthogonalSectionParameter source anchor| ≤ 2 * rho := by
  have hinner := hcover.inner_direction_ge_half hrhoOne
  have hinnerPos :
      0 <
        inner ℝ
          (wz1PaperDirection source)
          (wz1PaperDirection anchor) := by
    linarith
  have hzero :
      dist
          (wz1TubeAxisZeroPoint source)
          (wz1TubeAxisZeroPoint anchor) ≤ rho :=
    hcover.components.1
  have hnumerator :
      |inner ℝ
          (wz1TubeAxisZeroPoint source -
            wz1TubeAxisZeroPoint anchor)
          (wz1PaperDirection anchor)| ≤ rho := by
    calc
      |inner ℝ
          (wz1TubeAxisZeroPoint source -
            wz1TubeAxisZeroPoint anchor)
          (wz1PaperDirection anchor)|
          ≤ ‖wz1TubeAxisZeroPoint source -
                wz1TubeAxisZeroPoint anchor‖ *
              ‖wz1PaperDirection anchor‖ :=
        abs_real_inner_le_norm _ _
      _ = dist
            (wz1TubeAxisZeroPoint source)
            (wz1TubeAxisZeroPoint anchor) := by
        rw [wz1PaperDirection_norm, mul_one, dist_eq_norm]
      _ ≤ rho := hzero
  unfold wz1PaperOrthogonalSectionParameter
  rw [abs_div, abs_neg, abs_of_pos hinnerPos]
  exact (div_le_iff₀ hinnerPos).mpr (by nlinarith)

private lemma dilated_literal_orthogonal_section_image_horizontal_norm_le
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hcover : WZ2PaperDilatedTubeCovers 2 source anchor) :
    ‖wz2PaperLiteralUnitRescalingMap anchor hrho
        (wz1PaperOrthogonalSectionPoint source anchor)‖ ≤
      3 / 100 := by
  let sourcePoint :=
    wz1PaperOrthogonalSectionPoint source anchor
  let sourceZero := wz1TubeAxisZeroPoint source
  let anchorZero := wz1TubeAxisZeroPoint anchor
  let sourceDirection := wz1PaperDirection source
  let parameter :=
    wz1PaperOrthogonalSectionParameter source anchor
  have hparameter : |parameter| ≤ 2 * rho :=
    dilated_literal_abs_parameter_le hrho hrhoOne hcover
  have hzero : dist sourceZero anchorZero ≤ rho :=
    hcover.components.1
  have hsourcePoint :
      sourcePoint = sourceZero + parameter • sourceDirection := rfl
  have hsourceDistance :
      ‖sourcePoint - anchorZero‖ ≤ 3 * rho := by
    rw [hsourcePoint]
    have hrewrite :
        sourceZero + parameter • sourceDirection - anchorZero =
          (sourceZero - anchorZero) +
            parameter • sourceDirection := by
      abel
    rw [hrewrite]
    calc
      ‖(sourceZero - anchorZero) +
          parameter • sourceDirection‖
          ≤ ‖sourceZero - anchorZero‖ +
              ‖parameter • sourceDirection‖ :=
        norm_add_le _ _
      _ = dist sourceZero anchorZero + |parameter| := by
        rw [dist_eq_norm, norm_smul,
          wz1PaperDirection_norm, mul_one]
        simp [Real.norm_eq_abs]
      _ ≤ 3 * rho := by linarith
  have hinner := hcover.inner_direction_ge_half hrhoOne
  have hinnerNe :
      inner ℝ sourceDirection
          (wz1PaperDirection anchor) ≠ 0 := by
    dsimp only [sourceDirection]
    linarith
  have hperpendicular :
      inner ℝ (sourcePoint - anchorZero)
          (wz1PaperDirection anchor) = 0 :=
    wz1PaperOrthogonalSectionPoint_perp hinnerNe
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
      anchor hrho _ hperpendicular]
  calc
    ‖sourcePoint - anchorZero‖ / (100 * rho)
        ≤ (3 * rho) / (100 * rho) := by gcongr
    _ = 3 / 100 := by
      field_simp [hrho.ne']
      <;> ring

theorem wz2_paper_literal_canonical_dilated_unit_rescaled_tube :
    WZ2PaperLiteralCanonicalDilatedUnitRescaledTubeStatement := by
  intro delta rho hrho hrhoOne source anchor
    _hsource _hanchor hcover
  let imageDirection :=
    wz2PaperLiteralUnitRescalingLinear anchor
      (wz1PaperDirection source)
  let sourcePoint :=
    wz1PaperOrthogonalSectionPoint source anchor
  have himageNe : imageDirection ≠ 0 :=
    literal_direction_ne_zero hrho
  let target : Kakeya.DeltaTube (delta / rho) :=
    { base :=
        wz2PaperLiteralUnitRescalingMap anchor hrho sourcePoint
      direction := NormedSpace.normalize imageDirection
      direction_unit := NormedSpace.norm_normalize himageNe }
  have hnormalizedVertical :
      1 / 2 ≤
        (NormedSpace.normalize imageDirection) (2 : Fin 3) :=
    dilated_literal_normalized_direction_vertical
      hrho hrhoOne hcover
  have htargetVertical :
      1 / 2 ≤ wz1PaperDirection target (2 : Fin 3) := by
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
        dsimp only [target, imageDirection]
        linarith
      exact hstoredVertical.ne'
    have hbaseTwo : target.base (2 : Fin 3) = 0 := by
      dsimp only [target, sourcePoint]
      rw [wz2PaperLiteralUnitRescalingMap_coord2]
      have hinner :
          inner ℝ
              (wz1PaperDirection source)
              (wz1PaperDirection anchor) ≠ 0 := by
        have h := hcover.inner_direction_ge_half hrhoOne
        linarith
      rw [wz1PaperOrthogonalSectionPoint_perp hinner]
      ring
    simp [wz1TubeAxisZeroPoint, hbaseTwo, hvertical]
  have hbaseNorm : ‖target.base‖ ≤ 3 / 100 := by
    dsimp only [target, sourcePoint]
    exact
      dilated_literal_orthogonal_section_image_horizontal_norm_le
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
  refine
    ⟨{
      target := target
      target_line_class := ⟨htargetVertical, hcoord0, hcoord1⟩
      target_axis := ?_ }⟩
  exact literal_canonical_rescaled_axis hrho

end Kakeya.Assouad

end
