import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCanonicalDilatedRescaledTubeStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCanonicalDilatedDirection

/-!
# Canonical exact image-axis paper tube

Construct the target tube directly from the image of the source axis:

* the base is the image of the source axis's intersection with the
  anchor-orthogonal plane;
* the direction is the normalization of the linear image of the source paper
  direction.

The fixed transverse factor `1 / (100 * rho)` puts the target zero point well
inside the horizontal `L₃` window.
-/

noncomputable section

namespace Kakeya.Assouad

private lemma rescaled_paper_direction_ne_zero
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho) :
    wz1PaperUnitRescalingLinear anchor
        (wz1PaperDirection source) ≠
      0 := by
  intro hzero
  have hmapZero :
      wz1PaperUnitRescalingLinear anchor
          (wz1PaperDirection source) =
        wz1PaperUnitRescalingLinear anchor 0 := by
    simpa using hzero
  have hsourceZero :
      wz1PaperDirection source = 0 :=
    wz1PaperUnitRescalingLinear_injective
      anchor hrho hmapZero
  have hnorm := wz1PaperDirection_norm source
  rw [hsourceZero, norm_zero] at hnorm
  norm_num at hnorm

private lemma normalized_image_direction_vertical
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hcover : WZ1PaperTubeCovers source anchor) :
    1 / 2 ≤
      (NormedSpace.normalize
        (wz1PaperUnitRescalingLinear anchor
          (wz1PaperDirection source))) (2 : Fin 3) := by
  let imageDirection :=
    wz1PaperUnitRescalingLinear anchor (wz1PaperDirection source)
  have hinner :
      7 / 8 ≤
        inner ℝ (wz1PaperDirection source)
          (wz1PaperDirection anchor) :=
    wz1PaperTubeCovers.inner_direction_ge_seven_eighths
      hrhoOne hcover
  have hcoord :
      imageDirection (2 : Fin 3) =
        inner ℝ (wz1PaperDirection source)
          (wz1PaperDirection anchor) :=
    wz1PaperUnitRescalingLinear_coord2 anchor _
  have hcoordPos : 0 < imageDirection (2 : Fin 3) := by
    rw [hcoord]
    linarith
  have hnormBounds :
      1 / 2 ≤ ‖imageDirection‖ ∧
        ‖imageDirection‖ ≤ 3 / 2 :=
    wz1PaperUnitRescalingLinear_direction_norm_bounds
      hrho hrhoOne hcover
  have hnormPos : 0 < ‖imageDirection‖ := by
    linarith [hnormBounds.1]
  change 1 / 2 ≤ (‖imageDirection‖⁻¹ • imageDirection) (2 : Fin 3)
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ hnormPos).mpr (by
    rw [hcoord]
    nlinarith [hnormBounds.2])

private lemma orthogonal_section_image_horizontal_norm_le
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hcover : WZ1PaperTubeCovers source anchor) :
    ‖wz1PaperUnitRescalingMap anchor hrho
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
    calc
      ‖sourceZero + parameter • sourceDirection - anchorZero‖
          ≤ ‖sourceZero - anchorZero‖ +
              ‖parameter • sourceDirection‖ := by
        have hrewrite :
            sourceZero + parameter • sourceDirection - anchorZero =
              (sourceZero - anchorZero) +
                parameter • sourceDirection := by abel
        rw [hrewrite]
        exact norm_add_le _ _
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
      wz1PaperUnitRescalingMap anchor hrho sourcePoint =
        wz1PaperUnitRescalingLinear anchor
          (sourcePoint - anchorZero) := by
    have hzeroMap :
        wz1PaperUnitRescalingMap anchor hrho anchorZero = 0 := by
      dsimp only [anchorZero]
      simp [wz1PaperUnitRescalingMap, unitRescalingMap]
    have hsub :=
      wz1PaperUnitRescalingMap_sub
        anchor hrho sourcePoint anchorZero
    rw [hzeroMap, sub_zero] at hsub
    exact hsub
  rw [hmapDifference,
    wz1PaperUnitRescalingLinear_perp_norm
      anchor hrho _ hperp]
  calc
    ‖sourcePoint - anchorZero‖ / (100 * rho)
        ≤ (3 * rho / 2) / (100 * rho) := by
      gcongr
    _ = 3 / 200 := by
      field_simp [hrho.ne']
      ring

private lemma canonical_rescaled_axis
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho) :
    let imageDirection :=
      wz1PaperUnitRescalingLinear anchor
        (wz1PaperDirection source)
    let sourcePoint :=
      wz1PaperOrthogonalSectionPoint source anchor
    let target : Kakeya.DeltaTube (delta / rho) :=
      { base :=
          wz1PaperUnitRescalingMap anchor hrho sourcePoint
        direction := NormedSpace.normalize imageDirection
        direction_unit := by
          apply NormedSpace.norm_normalize
          exact rescaled_paper_direction_ne_zero hrho }
    tubeAxisLine target =
      wz1PaperUnitRescalingMap anchor hrho ''
        tubeAxisLine source := by
  dsimp only
  let imageDirection :=
    wz1PaperUnitRescalingLinear anchor
      (wz1PaperDirection source)
  let sourcePoint :=
    wz1PaperOrthogonalSectionPoint source anchor
  let targetBase :=
    wz1PaperUnitRescalingMap anchor hrho sourcePoint
  have himageNe : imageDirection ≠ 0 := by
    exact rescaled_paper_direction_ne_zero hrho
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
      · rw [hoffset]
        module
      · rw [hoffset]
        module
    refine ⟨sourceAxisPoint, hsourceAxisPoint, ?_⟩
    rw [wz1PaperUnitRescalingMap_add]
    dsimp only [sourceAxisPoint, sourceParameter, targetBase,
      imageDirection]
    rw [map_smul, hnormalize]
    module
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
      · rw [hpointOffset, hsourceOffset]
        module
      · rw [hpointOffset, hsourceOffset]
        module
    rw [hpoint, wz1PaperUnitRescalingMap_add, map_smul]
    refine ⟨signedDifference * ‖imageDirection‖, ?_⟩
    have hnormalize :
        NormedSpace.normalize imageDirection =
          ‖imageDirection‖⁻¹ • imageDirection := rfl
    have hnormNe : ‖imageDirection‖ ≠ 0 :=
      norm_ne_zero_iff.mpr himageNe
    change
      wz1PaperUnitRescalingMap anchor hrho sourcePoint +
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

theorem wz2_paper_canonical_unit_rescaled_tube_from_geometry :
    WZ2PaperCanonicalUnitRescaledTubeStatement := by
  intro delta rho hrho hrhoOne source anchor
    hsource hanchor hcover
  let imageDirection :=
    wz1PaperUnitRescalingLinear anchor
      (wz1PaperDirection source)
  let sourcePoint :=
    wz1PaperOrthogonalSectionPoint source anchor
  have himageNe : imageDirection ≠ 0 := by
    exact rescaled_paper_direction_ne_zero hrho
  let target : Kakeya.DeltaTube (delta / rho) :=
    { base :=
        wz1PaperUnitRescalingMap anchor hrho sourcePoint
      direction := NormedSpace.normalize imageDirection
      direction_unit := NormedSpace.norm_normalize himageNe }
  have htargetVertical :
      1 / 2 ≤ wz1PaperDirection target (2 : Fin 3) := by
    have hnormalizedVertical :=
      normalized_image_direction_vertical hrho hrhoOne hcover
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
          normalized_image_direction_vertical hrho hrhoOne hcover
        dsimp only [target, imageDirection]
        linarith
      exact hstoredVertical.ne'
    have hbaseTwo : target.base (2 : Fin 3) = 0 := by
      dsimp only [target, sourcePoint]
      rw [wz1PaperUnitRescalingMap_coord2]
      have hinner :=
        wz1PaperTubeCovers.inner_direction_ge_seven_eighths
          hrhoOne hcover
      apply wz1PaperOrthogonalSectionPoint_perp
      linarith
    simp [wz1TubeAxisZeroPoint, hbaseTwo, hvertical]
  have hbaseNorm :
      ‖target.base‖ ≤ 3 / 200 := by
    dsimp only [target, sourcePoint]
    exact orthogonal_section_image_horizontal_norm_le
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
  exact canonical_rescaled_axis hrho

private lemma abs_wz1PaperOrthogonalSectionParameter_le_of_dilated
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hcover : WZ2PaperDilatedTubeCovers 2 source anchor) :
    |wz1PaperOrthogonalSectionParameter source anchor| ≤
      2 * rho := by
  have hinner :=
    hcover.inner_direction_ge_half hrhoOne
  have hinnerPos :
      0 <
        inner ℝ
          (wz1PaperDirection source)
          (wz1PaperDirection anchor) := by
    linarith
  have hzero :
      dist
          (wz1TubeAxisZeroPoint source)
          (wz1TubeAxisZeroPoint anchor) ≤
        rho :=
    hcover.components.1
  have hnumerator :
      |inner ℝ
          (wz1TubeAxisZeroPoint source -
            wz1TubeAxisZeroPoint anchor)
          (wz1PaperDirection anchor)| ≤
        rho := by
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

private lemma dilated_orthogonal_section_image_horizontal_norm_le
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hcover : WZ2PaperDilatedTubeCovers 2 source anchor) :
    ‖wz1PaperUnitRescalingMap anchor hrho
        (wz1PaperOrthogonalSectionPoint source anchor)‖ ≤
      3 / 100 := by
  let sourcePoint :=
    wz1PaperOrthogonalSectionPoint source anchor
  let sourceZero := wz1TubeAxisZeroPoint source
  let anchorZero := wz1TubeAxisZeroPoint anchor
  let sourceDirection := wz1PaperDirection source
  let parameter :=
    wz1PaperOrthogonalSectionParameter source anchor
  have hparameter : |parameter| ≤ 2 * rho := by
    exact abs_wz1PaperOrthogonalSectionParameter_le_of_dilated
      hrho hrhoOne hcover
  have hzero :
      dist sourceZero anchorZero ≤ rho :=
    hcover.components.1
  have hsourcePoint :
      sourcePoint = sourceZero + parameter • sourceDirection := rfl
  have hsourceDistance :
      ‖sourcePoint - anchorZero‖ ≤ 3 * rho := by
    rw [hsourcePoint]
    calc
      ‖sourceZero + parameter • sourceDirection - anchorZero‖
          ≤ ‖sourceZero - anchorZero‖ +
              ‖parameter • sourceDirection‖ := by
        have hrewrite :
            sourceZero + parameter • sourceDirection - anchorZero =
              (sourceZero - anchorZero) +
                parameter • sourceDirection := by abel
        rw [hrewrite]
        exact norm_add_le _ _
      _ = dist sourceZero anchorZero + |parameter| := by
        rw [dist_eq_norm, norm_smul,
          wz1PaperDirection_norm, mul_one]
        simp only [Real.norm_eq_abs]
      _ ≤ 3 * rho := by linarith
  have hinner :=
    hcover.inner_direction_ge_half hrhoOne
  have hinnerNe :
      inner ℝ sourceDirection (wz1PaperDirection anchor) ≠ 0 := by
    dsimp only [sourceDirection]
    linarith
  have hperp :
      inner ℝ (sourcePoint - anchorZero)
        (wz1PaperDirection anchor) = 0 := by
    exact wz1PaperOrthogonalSectionPoint_perp hinnerNe
  have hmapDifference :
      wz1PaperUnitRescalingMap anchor hrho sourcePoint =
        wz1PaperUnitRescalingLinear anchor
          (sourcePoint - anchorZero) := by
    have hzeroMap :
        wz1PaperUnitRescalingMap anchor hrho anchorZero = 0 := by
      dsimp only [anchorZero]
      simp [wz1PaperUnitRescalingMap, unitRescalingMap]
    have hsub :=
      wz1PaperUnitRescalingMap_sub
        anchor hrho sourcePoint anchorZero
    rw [hzeroMap, sub_zero] at hsub
    exact hsub
  rw [hmapDifference,
    wz1PaperUnitRescalingLinear_perp_norm
      anchor hrho _ hperp]
  calc
    ‖sourcePoint - anchorZero‖ / (100 * rho)
        ≤ (3 * rho) / (100 * rho) := by
      gcongr
    _ = 3 / 100 := by
      field_simp [hrho.ne']

theorem wz2_paper_canonical_dilated_unit_rescaled_tube_from_geometry :
    WZ2PaperCanonicalDilatedUnitRescaledTubeStatement := by
  intro delta rho hrho hrhoOne source anchor
    hsource hanchor hcover
  let imageDirection :=
    wz1PaperUnitRescalingLinear anchor
      (wz1PaperDirection source)
  let sourcePoint :=
    wz1PaperOrthogonalSectionPoint source anchor
  have himageNe : imageDirection ≠ 0 := by
    exact rescaled_direction_ne_zero hrho
  let target : Kakeya.DeltaTube (delta / rho) :=
    { base :=
        wz1PaperUnitRescalingMap anchor hrho sourcePoint
      direction := NormedSpace.normalize imageDirection
      direction_unit := NormedSpace.norm_normalize himageNe }
  have hnormalizedVertical :
      1 / 2 ≤
        (NormedSpace.normalize imageDirection) (2 : Fin 3) := by
    exact
      wz1PaperDilatedUnitRescaling_normalized_direction_vertical
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
      rw [wz1PaperUnitRescalingMap_coord2]
      apply wz1PaperOrthogonalSectionPoint_perp
      have hinner :=
        hcover.inner_direction_ge_half hrhoOne
      linarith
    simp [wz1TubeAxisZeroPoint, hbaseTwo, hvertical]
  have hbaseNorm :
      ‖target.base‖ ≤ 3 / 100 := by
    dsimp only [target, sourcePoint]
    exact dilated_orthogonal_section_image_horizontal_norm_le
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
  exact canonical_rescaled_axis hrho

end Kakeya.Assouad

end
