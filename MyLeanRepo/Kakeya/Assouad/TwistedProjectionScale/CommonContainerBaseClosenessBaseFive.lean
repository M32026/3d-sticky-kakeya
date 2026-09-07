import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CommonContainerDirectionCloseness
import Mathlib.Tactic

/-!
# Base closeness from common container (radius-five basepoint window)

Given two rho-tubes A, B both contained in one tau-tube U, there is a point P
on B's axis line that is close to A.base and has norm at most 6.

This is the radius-five variant of `base_closeness_from_common_containment`.
The only change is the weakened basepoint hypothesis `‖A.base‖ ≤ 5` and the
correspondingly relaxed conclusion `‖P‖ ≤ 6`.

Whiteprint node: `base_closeness_base_five`.
-/

noncomputable section

namespace Kakeya.Assouad

open BigOperators

/-- A tube's basepoint lies in its carrier (it is the start of the unit segment). -/
private lemma base_in_carrier_base_five {delta : ℝ} (T : Kakeya.DeltaTube delta)
    (hdelta : 0 ≤ delta) : T.base ∈ T.carrier := by
  have h1 : T.base ∈ Kakeya.unitSegment T.base T.direction := by
    refine ⟨0, by norm_num, ?_⟩
    simp
  exact Metric.mem_cthickening_of_dist_le T.base T.base delta _ h1 (by simp [hdelta])

/--
For any vector `x` and unit vector `u`, the perpendicular component
`x - (inner ℝ x u) • u` has norm at most `‖x‖`.
-/
private lemma perp_component_le_self_base_five {u x : Point3} (hu : ‖u‖ = 1) :
    ‖x - (inner ℝ x u) • u‖ ≤ ‖x‖ := by
  set p : ℝ := inner ℝ x u with hp
  set y : Point3 := x - p • u with hy
  have h_iuu : inner ℝ u u = 1 := by
    have h : inner ℝ u u = ‖u‖ ^ 2 :=
      inner_self_eq_norm_sq_to_K (𝕜 := ℝ) u
    rw [h, hu] <;> norm_num
  have h_comm : inner ℝ u x = p := by
    have h_c : inner ℝ u x = inner ℝ x u :=
      real_inner_comm x u
    rw [h_c, hp]
  have h_orth : inner ℝ (p • u) y = 0 := by
    rw [hy]
    have h2 : inner ℝ (p • u) (x - p • u) =
        inner ℝ (p • u) x - inner ℝ (p • u) (p • u) := by
      rw [inner_sub_right]
    rw [h2]
    have h3 : inner ℝ (p • u) x = p * inner ℝ u x := by
      rw [inner_smul_left] <;> simp
    have h4 : inner ℝ (p • u) (p • u) = p * p * inner ℝ u u := by
      rw [inner_smul_left, inner_smul_right] <;> simp <;> ring
    rw [h3, h4, h_comm, h_iuu] <;> ring
  have h_decomp : x = (p • u) + y := by
    simp [hy] <;> abel
  have h_pyth : ‖x‖ ^ 2 = ‖(p • u)‖ ^ 2 + ‖y‖ ^ 2 := by
    rw [h_decomp]
    have h_eq : ‖(p • u) + y‖ * ‖(p • u) + y‖ =
        ‖(p • u)‖ * ‖(p • u)‖ + ‖y‖ * ‖y‖ :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (p • u) y h_orth
    simpa [pow_two] using h_eq
  have h_ineq : ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [h_pyth] <;> nlinarith [sq_nonneg ‖(p • u)‖]
  have h_nonneg : 0 ≤ ‖y‖ := by positivity
  have h_x_nonneg : 0 ≤ ‖x‖ := by positivity
  nlinarith

/--
Orthogonal decomposition bound: if `‖v - t • u‖ ≤ tau` with `‖u‖ = 1`,
then both the axial error and the perpendicular component are at most `tau`.
-/
private lemma orthogonal_decomp_bound_base_five {u v : Point3} {t tau : ℝ}
    (hu : ‖u‖ = 1) (h : ‖v - t • u‖ ≤ tau) (htau : 0 ≤ tau) :
    |inner ℝ v u - t| ≤ tau ∧
    ‖v - (inner ℝ v u) • u‖ ≤ tau := by
  set w : Point3 := v - t • u with hw
  have h_iuu : inner ℝ u u = 1 := by
    have h5 : inner ℝ u u = ‖u‖ ^ 2 :=
      inner_self_eq_norm_sq_to_K (𝕜 := ℝ) u
    rw [h5, hu] <;> norm_num
  have h1 : inner ℝ v u - t = inner ℝ w u := by
    calc
      inner ℝ v u - t
        = inner ℝ v u - inner ℝ (t • u) u := by
          have h_smul : inner ℝ (t • u) u = t * inner ℝ u u := by
            simpa using inner_smul_left u u t
          rw [h_smul, h_iuu] <;> ring
      _ = inner ℝ (v - t • u) u := by
        rw [←inner_sub_left] <;> rfl
      _ = inner ℝ w u := by rw [hw]
  have h_cauchy : |inner ℝ w u| ≤ ‖w‖ * ‖u‖ :=
    abs_real_inner_le_norm w u
  have h_abs : |inner ℝ v u - t| ≤ tau := by
    rw [h1]
    rw [hu] at h_cauchy
    have h5 : |inner ℝ w u| ≤ ‖w‖ := by simpa using h_cauchy
    have h6 : ‖w‖ ≤ tau := h
    exact le_trans h5 h6
  have h5 : inner ℝ w u = inner ℝ v u - t := h1.symm
  have h_eq : v - (inner ℝ v u) • u = w - (inner ℝ w u) • u := by
    have h6 : w - (inner ℝ w u) • u = (v - t • u) - (inner ℝ v u - t) • u := by
      rw [hw, h5] <;> rfl
    rw [h6]
    have h7 : (inner ℝ v u - t) • u = (inner ℝ v u) • u - t • u := by
      rw [sub_smul]
    rw [h7] <;> abel
  have h_perp : ‖w - (inner ℝ w u) • u‖ ≤ ‖w‖ :=
    perp_component_le_self_base_five hu
  have h7 : ‖v - (inner ℝ v u) • u‖ ≤ ‖w‖ := by
    rw [h_eq] <;> exact h_perp
  have h8 : ‖w‖ ≤ tau := h
  exact ⟨h_abs, le_trans h7 h8⟩

/--
Given two rho-tubes A, B both contained in a tau-tube U, there exists a point
P on B's axis line within `20*tau` of A.base and with norm at most 6.

This is the radius-five basepoint variant: the hypothesis is `‖A.base‖ ≤ 5`
and the conclusion is `‖P‖ ≤ 6`.
-/
lemma base_closeness_from_common_containment_base_five {rho tau : ℝ}
    (hrho_nonneg : 0 ≤ rho) (htau_nonneg : 0 ≤ tau)
    (A B : Kakeya.DeltaTube rho) (U : Kakeya.DeltaTube tau)
    (hA_cont : A.carrier ⊆ U.carrier)
    (hB_cont : B.carrier ⊆ U.carrier)
    (hAbase : ‖A.base‖ ≤ 5)
    (htau_small : tau ≤ 1 / 10000) :
    ∃ (P : Point3), P ∈ tubeAxisLine B ∧
      ‖A.base - P‖ ≤ 20 * tau ∧ ‖P‖ ≤ 6 := by
  set u := U.direction with hu_def
  have hu : ‖u‖ = 1 := U.direction_unit
  set vA := A.base - U.base with hvA_def
  set vB := B.base - U.base with hvB_def
  set dB := B.direction with hdB_def
  have hA_base_in : A.base ∈ A.carrier := base_in_carrier_base_five A hrho_nonneg
  have hB_base_in : B.base ∈ B.carrier := base_in_carrier_base_five B hrho_nonneg
  have hA_in_U : A.base ∈ U.carrier := hA_cont hA_base_in
  have hB_in_U : B.base ∈ U.carrier := hB_cont hB_base_in
  let axisU := Kakeya.unitSegment U.base U.direction
  have h_compactU : IsCompact axisU := by
    apply IsCompact.image isCompact_Icc
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hU_eq : U.carrier = ⋃ y ∈ axisU, Metric.closedBall y tau :=
    h_compactU.cthickening_eq_biUnion_closedBall htau_nonneg
  rcases Set.mem_iUnion₂.mp (by rw [←hU_eq]; exact hA_in_U) with ⟨yA, hyA_seg, hdistA⟩
  rcases hyA_seg with ⟨tA, htA_int, rfl⟩
  have htA0 : 0 ≤ tA := htA_int.1
  have htA1 : tA ≤ 1 := htA_int.2
  have h_normA : ‖vA - tA • u‖ ≤ tau := by
    have h1 : ‖A.base - (U.base + tA • U.direction)‖ ≤ tau := by
      simpa [dist_eq_norm] using hdistA
    have h2 : A.base - (U.base + tA • U.direction) = vA - tA • u := by
      simp [hvA_def, hu_def] <;> abel
    rw [h2] at h1
    exact h1
  rcases Set.mem_iUnion₂.mp (by rw [←hU_eq]; exact hB_in_U) with ⟨yB, hyB_seg, hdistB⟩
  rcases hyB_seg with ⟨tB, htB_int, rfl⟩
  have htB0 : 0 ≤ tB := htB_int.1
  have htB1 : tB ≤ 1 := htB_int.2
  have h_normB : ‖vB - tB • u‖ ≤ tau := by
    have h1 : ‖B.base - (U.base + tB • U.direction)‖ ≤ tau := by
      simpa [dist_eq_norm] using hdistB
    have h2 : B.base - (U.base + tB • U.direction) = vB - tB • u := by
      simp [hvB_def, hu_def] <;> abel
    rw [h2] at h1
    exact h1
  rcases direction_closeness_from_containment hrho_nonneg htau_nonneg B U hB_cont
    with ⟨sign, hsign, hdir_close⟩
  set parA := inner ℝ vA u with hparA_def
  set parB := inner ℝ vB u with hparB_def
  set pardB := inner ℝ dB u with hpardB_def
  set perpA := vA - parA • u with hperpA_def
  set perpB := vB - parB • u with hperpB_def
  set perpdB := dB - pardB • u with hperpdB_def
  have ⟨h_parA_err, h_perpA_bound⟩ :=
    orthogonal_decomp_bound_base_five hu h_normA htau_nonneg
  have ⟨h_parB_err, h_perpB_bound⟩ :=
    orthogonal_decomp_bound_base_five hu h_normB htau_nonneg
  have h_dir_norm : ‖dB - sign • u‖ ≤ 4 * tau := hdir_close
  have ⟨h_pardB_err, h_perpdB_bound⟩ :=
    orthogonal_decomp_bound_base_five hu h_dir_norm (by positivity)
  have h_pardB_abs : |pardB| ≥ 1 - 4 * tau := by
    rcases hsign with (rfl | rfl)
    · have h : |pardB - 1| ≤ 4 * tau := h_pardB_err
      have h' : pardB ≥ 1 - 4 * tau := by linarith [abs_le.mp h]
      have h'' : 0 ≤ pardB := by linarith [htau_small]
      rw [abs_of_nonneg h''] <;> linarith
    · have h : |pardB - (-1 : ℝ)| ≤ 4 * tau := h_pardB_err
      have h' : pardB ≤ -1 + 4 * tau := by linarith [abs_le.mp h]
      have h'' : pardB < 0 := by linarith [htau_small]
      rw [abs_of_neg h''] <;> linarith
  have h_pardB_ne_zero : pardB ≠ 0 := by
    have h_pos : 0 < 1 - 4 * tau := by linarith [htau_small]
    have h : |pardB| > 0 := by linarith
    exact abs_pos.mp h
  have h_parA_lower : -tau ≤ parA := by linarith [abs_le.mp h_parA_err, htA0]
  have h_parA_upper : parA ≤ 1 + tau := by linarith [abs_le.mp h_parA_err, htA1]
  have h_parB_lower : -tau ≤ parB := by linarith [abs_le.mp h_parB_err, htB0]
  have h_parB_upper : parB ≤ 1 + tau := by linarith [abs_le.mp h_parB_err, htB1]
  set s : ℝ := (parA - parB) / pardB with hs_def
  set P : Point3 := B.base + s • dB with hP_def
  have hP_in_axis : P ∈ tubeAxisLine B := by
    refine ⟨s, ?_⟩
    simp [hP_def, hdB_def, tubeAxisLine]
  have h_diff_bound : |parA - parB| ≤ 1 + 2 * tau := by
    rw [abs_le]
    constructor <;> linarith
  have h_s_abs : |s| ≤ 2 := by
    have h1 : |s| = |parA - parB| / |pardB| := by
      rw [hs_def, abs_div] <;> rfl
    rw [h1]
    have h2 : |parA - parB| / |pardB| ≤ (1 + 2 * tau) / (1 - 4 * tau) := by
      gcongr <;> linarith
    have h4 : 0 < 1 - 4 * tau := by linarith [htau_small]
    have h5 : (1 + 2 * tau) ≤ 2 * (1 - 4 * tau) := by linarith [htau_small]
    have h6 : (1 + 2 * tau) / (1 - 4 * tau) ≤ 2 := by
      calc
        (1 + 2 * tau) / (1 - 4 * tau)
          ≤ (2 * (1 - 4 * tau)) / (1 - 4 * tau) := by gcongr
        _ = 2 := by field_simp [h4.ne'] <;> ring
    linarith
  have h_parP : inner ℝ (P - U.base) u = parA := by
    have h : P - U.base = vB + s • dB := by
      simp [hP_def, hvB_def, hdB_def] <;> abel
    rw [h]
    have h_add : inner ℝ (vB + s • dB) u = inner ℝ vB u + inner ℝ (s • dB) u := by
      exact inner_add_left _ _ _
    have h_smul : inner ℝ (s • dB) u = s * inner ℝ dB u := by
      simpa [inner_smul_left] using rfl
    rw [h_add, h_smul]
    have h9 : inner ℝ vB u + s * inner ℝ dB u = parB + s * pardB := by
      rw [←hparB_def, ←hpardB_def] <;> ring
    rw [h9, hs_def]
    field_simp [h_pardB_ne_zero] <;> ring
  set perpP := (P - U.base) - (inner ℝ (P - U.base) u) • u with hperpP_def
  have h_perpP_eq : perpP = perpB + s • perpdB := by
    have h1 : P - U.base = vB + s • dB := by
      simp [hP_def, hvB_def, hdB_def] <;> abel
    have h_inner : inner ℝ (vB + s • dB) u = parA := by
      rw [←h1]
      exact h_parP
    have h_parA_eq : parA = parB + s * pardB := by
      rw [hs_def]
      field_simp [h_pardB_ne_zero] <;> ring
    have h_goal : vB + s • dB - parA • u = perpB + s • perpdB := by
      have h_smul1 : (parB + s * pardB) • u = parB • u + s • (pardB • u) := by
        rw [add_smul, smul_smul] <;> ring
      have h_step1 : vB + s • dB - (parB • u + s • (pardB • u)) =
          (vB - parB • u) + (s • dB - s • (pardB • u)) := by abel
      have h_step2 : s • dB - s • (pardB • u) = s • (dB - pardB • u) := by
        rw [←smul_sub]
      have h_main : vB + s • dB - parA • u =
          (vB - parB • u) + s • (dB - pardB • u) := by
        calc
          vB + s • dB - parA • u
            = vB + s • dB - (parB + s * pardB) • u := by rw [h_parA_eq]
          _ = vB + s • dB - (parB • u + s • (pardB • u)) := by rw [h_smul1]
          _ = (vB - parB • u) + (s • dB - s • (pardB • u)) := h_step1
          _ = (vB - parB • u) + s • (dB - pardB • u) := by rw [h_step2]
      have h_perp : (vB - parB • u) + s • (dB - pardB • u) =
          perpB + s • perpdB := by
        simp [hperpB_def, hperpdB_def] <;> abel
      exact h_main.trans h_perp
    have h_main2 :
        (P - U.base) - (inner ℝ (P - U.base) u) • u = perpB + s • perpdB := by
      rw [h1, h_inner]
      exact h_goal
    rw [hperpP_def]
    exact h_main2
  have h_perpP_bound : ‖perpP‖ ≤ 9 * tau := by
    rw [h_perpP_eq]
    calc
      ‖perpB + s • perpdB‖
        ≤ ‖perpB‖ + ‖s • perpdB‖ := norm_add_le _ _
      _ = ‖perpB‖ + |s| * ‖perpdB‖ := by
        have hns : ‖s‖ = |s| := by simp [Real.norm_eq_abs]
        rw [norm_smul, hns] <;> ring
      _ ≤ tau + 2 * (4 * tau) := by gcongr <;> linarith
      _ = 9 * tau := by ring
  have h_diff : P - A.base = perpP - perpA := by
    have h1 : P - U.base = (inner ℝ (P - U.base) u) • u + perpP := by
      simp [hperpP_def] <;> abel
    have h21 : perpA = vA - parA • u := by rfl
    have h22 : parA • u + perpA = vA := by
      rw [h21] <;> abel
    have h23 : vA = A.base - U.base := by rfl
    have h2 : A.base - U.base = parA • u + perpA := by
      rw [←h23, ←h22]
    have h3 : P - A.base = (P - U.base) - (A.base - U.base) := by abel
    rw [h3, h1, h2, h_parP] <;> abel
  have h_dist : ‖P - A.base‖ ≤ 20 * tau := by
    rw [h_diff]
    calc
      ‖perpP - perpA‖
        ≤ ‖perpP‖ + ‖perpA‖ := norm_sub_le _ _
      _ ≤ 9 * tau + tau := by gcongr
      _ = 10 * tau := by ring
      _ ≤ 20 * tau := by linarith [htau_nonneg]
  have h_normP : ‖P‖ ≤ 6 := by
    have h : ‖P‖ ≤ ‖A.base‖ + ‖P - A.base‖ := by
      calc
        ‖P‖ = dist P 0 := by simp
        _ ≤ dist P A.base + dist A.base 0 := dist_triangle P A.base 0
        _ = ‖P - A.base‖ + ‖A.base‖ := by simp [dist_eq_norm]
        _ = ‖A.base‖ + ‖P - A.base‖ := by ring
    have h9 : ‖A.base‖ + ‖P - A.base‖ ≤ 5 + 20 * tau := by
      gcongr <;> linarith
    have h10 : 5 + 20 * tau ≤ 6 := by
      linarith [htau_small]
    linarith
  have h_dist' : ‖A.base - P‖ ≤ 20 * tau := by
    have h_eq : ‖A.base - P‖ = ‖P - A.base‖ := by rw [norm_sub_rev]
    rw [h_eq]
    exact h_dist
  exact ⟨P, hP_in_axis, h_dist', h_normP⟩

end Kakeya.Assouad
