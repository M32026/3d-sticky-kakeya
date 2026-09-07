import MyLeanRepo.Kakeya.Assouad.PropStickyPaperUnitRescalingBasics

/-!
# Direction control for a doubled-anchor paper rescaling

The paper fiber tree only places an intermediate source tube in the doubled
anchor.  Even with this weaker angle bound, the normalized linear image stays
in the positive `L₃` cap.
-/

noncomputable section

namespace Kakeya.Assouad

theorem WZ2PaperDilatedTubeCovers.components
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hcover : WZ2PaperDilatedTubeCovers 2 source anchor) :
    dist (wz1TubeAxisZeroPoint source)
          (wz1TubeAxisZeroPoint anchor) ≤ rho ∧
      InnerProductGeometry.angle
          (wz1PaperDirection source)
          (wz1PaperDirection anchor) ≤ rho := by
  have hsum :
      wz1PaperLineDistance source anchor ≤ rho := by
    simpa [WZ2PaperDilatedTubeCovers] using hcover
  have hdist : 0 ≤ dist
      (wz1TubeAxisZeroPoint source)
      (wz1TubeAxisZeroPoint anchor) := dist_nonneg
  have hangle : 0 ≤ InnerProductGeometry.angle
      (wz1PaperDirection source)
      (wz1PaperDirection anchor) :=
    InnerProductGeometry.angle_nonneg _ _
  dsimp only [wz1PaperLineDistance] at hsum
  exact ⟨by linarith, by linarith⟩

theorem WZ2PaperDilatedTubeCovers.inner_direction_ge_half
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrhoOne : rho ≤ 1)
    (hcover : WZ2PaperDilatedTubeCovers 2 source anchor) :
    1 / 2 ≤ inner ℝ
      (wz1PaperDirection source)
      (wz1PaperDirection anchor) := by
  let angle :=
    InnerProductGeometry.angle
      (wz1PaperDirection source)
      (wz1PaperDirection anchor)
  have hangleNonneg : 0 ≤ angle :=
    InnerProductGeometry.angle_nonneg _ _
  have hangle : angle ≤ rho := hcover.components.2
  have hcos :
      1 - angle ^ 2 / 2 ≤ Real.cos angle :=
    Real.one_sub_sq_div_two_le_cos
  have hinner :
      inner ℝ
          (wz1PaperDirection source)
          (wz1PaperDirection anchor) =
        Real.cos angle := by
    rw [
      InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one
        (wz1PaperDirection_norm source)
        (wz1PaperDirection_norm anchor)]
  rw [hinner]
  nlinarith [sq_nonneg (rho - angle)]

lemma transversePart_transverseScaleLin
    (scale : ℝ) (vector : Point3) :
    transversePart (transverseScaleLin scale vector) =
      transverseScaleLin scale (transversePart vector) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [transversePart_coord0, transversePart_coord1,
      transversePart_coord2, transverseScaleLin_coord0,
      transverseScaleLin_coord1, transverseScaleLin_coord2]

theorem WZ2PaperDilatedTubeCovers.rotated_transverse_norm_le
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hcover : WZ2PaperDilatedTubeCovers 2 source anchor) :
    ‖transversePart
        (householderToE3
          (wz1PaperDirection anchor)
          (wz1PaperDirection_norm anchor)
          (wz1PaperDirection source))‖ ≤ rho := by
  let rotation :=
    householderToE3
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor)
  let rotatedSource :=
    rotation (wz1PaperDirection source)
  have hrotationAnchor :
      rotation (wz1PaperDirection anchor) = e3 :=
    householderToE3_sends_d_to_e3
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor)
  have htransverseDifference :
      transversePart rotatedSource =
        transversePart (rotatedSource - e3) := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;>
      simp [rotatedSource, transversePart_coord0,
        transversePart_coord1, transversePart_coord2, e3]
  rw [htransverseDifference]
  calc
    ‖transversePart (rotatedSource - e3)‖
        ≤ ‖rotatedSource - e3‖ :=
      transversePart_norm_le _
    _ = ‖wz1PaperDirection source -
          wz1PaperDirection anchor‖ := by
      rw [← hrotationAnchor, ← map_sub, rotation.norm_map]
    _ ≤ InnerProductGeometry.angle
          (wz1PaperDirection source)
          (wz1PaperDirection anchor) :=
      unit_norm_sub_le_angle
        (wz1PaperDirection_norm source)
        (wz1PaperDirection_norm anchor)
    _ ≤ rho := hcover.components.2

lemma rescaled_direction_ne_zero
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho) :
    wz1PaperUnitRescalingLinear anchor
        (wz1PaperDirection source) ≠ 0 := by
  intro hzero
  have hmapZero :
      wz1PaperUnitRescalingLinear anchor
          (wz1PaperDirection source) =
        wz1PaperUnitRescalingLinear anchor 0 := by
    simpa using hzero
  have hsourceZero :
      wz1PaperDirection source = 0 :=
    wz1PaperUnitRescalingLinear_injective anchor hrho hmapZero
  have hnorm := wz1PaperDirection_norm source
  rw [hsourceZero, norm_zero] at hnorm
  norm_num at hnorm

theorem wz1PaperDilatedUnitRescaling_transverse_norm_le
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hcover : WZ2PaperDilatedTubeCovers 2 source anchor) :
    ‖transversePart
        (wz1PaperUnitRescalingLinear anchor
          (wz1PaperDirection source))‖ ≤ 1 / 100 := by
  let rotatedSource :=
    householderToE3
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor)
      (wz1PaperDirection source)
  have hrewrite :
      transversePart
          (wz1PaperUnitRescalingLinear anchor
            (wz1PaperDirection source)) =
        transverseScaleLin (100 * rho)
          (transversePart rotatedSource) := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;>
      simp [wz1PaperUnitRescalingLinear, unitRescalingLinear,
        rotatedSource, transversePart_coord0, transversePart_coord1,
        transversePart_coord2, transverseScaleLin_coord0,
        transverseScaleLin_coord1, transverseScaleLin_coord2]
  rw [hrewrite]
  calc
    ‖transverseScaleLin (100 * rho)
        (transversePart rotatedSource)‖
        = ‖transversePart rotatedSource‖ / (100 * rho) := by
      apply transverseScaleLin_norm_of_coord2_zero
      · positivity
      · simp [transversePart_coord2]
    _ ≤ rho / (100 * rho) := by
      gcongr
      exact hcover.rotated_transverse_norm_le
    _ = 1 / 100 := by
      field_simp [hrho.ne']

private theorem normalized_coord2_ge_half_of_transverse_norm_le
    (vector : Point3)
    (hcoord : 1 / 2 ≤ vector (2 : Fin 3))
    (htransverse : ‖transversePart vector‖ ≤ 1 / 100) :
    1 / 2 ≤
      (NormedSpace.normalize vector) (2 : Fin 3) := by
  have hcoordPos : 0 < vector (2 : Fin 3) := by
    linarith
  have hvectorNe : vector ≠ 0 := by
    intro hzero
    rw [hzero] at hcoordPos
    simp at hcoordPos
  have hnormalize :
      (NormedSpace.normalize vector) (2 : Fin 3) =
        vector (2 : Fin 3) / ‖vector‖ := by
    change
      (‖vector‖⁻¹ • vector) (2 : Fin 3) =
        vector (2 : Fin 3) / ‖vector‖
    simp [PiLp.smul_apply, inv_mul_eq_div]
  rw [hnormalize]
  have hnormPos : 0 < ‖vector‖ :=
    norm_pos_iff.mpr hvectorNe
  apply (le_div_iff₀ hnormPos).mpr
  have hdecompose :
      vector =
        transversePart vector +
          (vector (2 : Fin 3)) • e3 := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;>
      simp [transversePart_coord0, transversePart_coord1,
        transversePart_coord2, e3]
  have hnorm :
      ‖vector‖ ≤
        ‖transversePart vector‖ +
          vector (2 : Fin 3) := by
    nth_rewrite 1 [hdecompose]
    calc
      ‖transversePart vector +
          vector (2 : Fin 3) • e3‖
          ≤ ‖transversePart vector‖ +
              ‖vector (2 : Fin 3) • e3‖ :=
        norm_add_le _ _
      _ = ‖transversePart vector‖ +
            vector (2 : Fin 3) := by
        rw [norm_smul, e3_norm, mul_one]
        simp [Real.norm_eq_abs, abs_of_pos hcoordPos]
  nlinarith

theorem wz1PaperDilatedUnitRescaling_normalized_direction_vertical
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {anchor : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hcover : WZ2PaperDilatedTubeCovers 2 source anchor) :
    1 / 2 ≤
      (NormedSpace.normalize
        (wz1PaperUnitRescalingLinear anchor
          (wz1PaperDirection source))) (2 : Fin 3) := by
  apply normalized_coord2_ge_half_of_transverse_norm_le
  · rw [wz1PaperUnitRescalingLinear_coord2]
    exact hcover.inner_direction_ge_half hrhoOne
  · exact
      wz1PaperDilatedUnitRescaling_transverse_norm_le
        hrho hcover

end Kakeya.Assouad

end
