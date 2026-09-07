import MyLeanRepo.Kakeya.Assouad.WZ1.UnitRescaling

/-!
# Contraction of the anchored normal transform

The inverse-transpose normal map for the anchored rescaling is contractive
when the transverse scale `100 * rho` is at most one.
-/

noncomputable section

namespace Kakeya.Assouad

private lemma transverseScaleLin_norm_le_local
    {scale : ℝ} (hscale : 1 ≤ scale) (vector : Point3) :
    ‖transverseScaleLin scale vector‖ ≤ ‖vector‖ := by
  have hscale_pos : 0 < scale := zero_lt_one.trans_le hscale
  have hscale_ne : scale ≠ 0 := hscale_pos.ne'
  have hcoord0 :
      (transverseScaleLin scale vector) 0 = vector 0 / scale :=
    transverseScaleLin_coord0 scale vector
  have hcoord1 :
      (transverseScaleLin scale vector) 1 = vector 1 / scale :=
    transverseScaleLin_coord1 scale vector
  have hcoord2 :
      (transverseScaleLin scale vector) 2 = vector 2 :=
    transverseScaleLin_coord2 scale vector
  have hnorm_sq : ∀ point : Point3,
      ‖point‖ ^ 2 = point 0 ^ 2 + point 1 ^ 2 + point 2 ^ 2 := by
    intro point
    rw [EuclideanSpace.real_norm_sq_eq point, Fin.sum_univ_three]
  have hscale_sq : 1 ≤ scale ^ 2 := by nlinarith
  have hfirst : (vector 0 / scale) ^ 2 ≤ vector 0 ^ 2 := by
    rw [div_pow]
    exact div_le_self (sq_nonneg _) hscale_sq
  have hsecond : (vector 1 / scale) ^ 2 ≤ vector 1 ^ 2 := by
    rw [div_pow]
    exact div_le_self (sq_nonneg _) hscale_sq
  have hsquares :
      ‖transverseScaleLin scale vector‖ ^ 2 ≤ ‖vector‖ ^ 2 := by
    rw [hnorm_sq, hnorm_sq, hcoord0, hcoord1, hcoord2]
    linarith
  nlinarith [norm_nonneg (transverseScaleLin scale vector), norm_nonneg vector]

/-- The anchored normal-rescaling linear map is contractive when `100 * rho ≤ 1`. -/
lemma anchoredNormalLinear_contraction
    {delta : ℝ} (anchor : Kakeya.DeltaTube delta) (rho : ℝ) (hrho : 0 < rho)
    (h_rho_small : 100 * rho ≤ 1) (v : Point3) :
    ‖wz1AnchoredUnitRescalingNormalLinear anchor rho v‖ ≤ ‖v‖ := by
  let R := householderToE3 anchor.direction anchor.direction_unit
  let w : Point3 := R v
  have hR_norm : ‖w‖ = ‖v‖ :=
    householderToE3_norm anchor.direction anchor.direction_unit v
  let a : ℝ := 100 * rho
  have ha_pos : 0 < a := by positivity
  have ha_le_one : a ≤ 1 := h_rho_small
  have h_s_ge_one : 1 ≤ 1 / a := by
    apply one_le_one_div
    · exact ha_pos
    · exact ha_le_one
  have h_eq : wz1AnchoredUnitRescalingNormalLinear anchor rho v =
      transverseScaleLin (1 / a) w := by
    have h1 : wz1AnchoredUnitRescalingNormalLinear anchor rho =
        unitRescalingNormalLinear anchor.direction anchor.direction_unit a := by
      rfl
    rw [h1]
    have h2 : unitRescalingNormalLinear anchor.direction anchor.direction_unit a v =
        transverseScaleLin (1 / a) (R v) := by
      unfold unitRescalingNormalLinear
      simp [R]
    rw [h2]
  rw [h_eq]
  have h_main : ‖transverseScaleLin (1 / a) w‖ ≤ ‖w‖ :=
    transverseScaleLin_norm_le_local h_s_ge_one w
  rw [hR_norm] at h_main
  exact h_main

end Kakeya.Assouad
