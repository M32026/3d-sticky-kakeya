import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.LocalGrainCubeCountStatements
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Slab containment for WZ1 Lemma 17 Córdoba argument

Shows that selected propertyOne tube pieces near a point `p` whose scalar
projection is close to `t` are contained in the slab
`{x | |inner(x, normal) - t| ≤ 20 * max(1, L) * rho}`.

The key geometric fact: two points in a δ-tube with direction `dir` have
projection difference onto a unit normal `n` bounded by
`2δ + (dist + 2δ) * |inner(dir, n)|`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

/--
Geometric bound: for two points `x`, `p` in the same δ-tube with direction
`dir`, the absolute difference of their projections onto a unit vector `n`
is bounded by `2δ + (‖x-p‖ + 2δ) * |inner(dir, n)|`.
-/
lemma tube_two_point_projection_bound
    {δ : ℝ} (hδ : 0 ≤ δ)
    (T : Kakeya.DeltaTube δ) (n : Point3) (hn : ‖n‖ = 1)
    (x p : Point3) (hx : x ∈ T.carrier) (hp : p ∈ T.carrier) :
    |inner ℝ (x - p) n| ≤ 2 * δ + (‖x - p‖ + 2 * δ) * |inner ℝ T.direction n| := by
  have hcarrier : T.carrier = Metric.cthickening δ (unitSegment T.base T.direction) := by
    simp [Kakeya.DeltaTube.carrier]
  have hcompact : IsCompact (unitSegment T.base T.direction) := by
    exact isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  rw [hcarrier] at hx hp
  rw [hcompact.cthickening_eq_biUnion_closedBall hδ] at hx hp
  rcases Set.mem_iUnion₂.mp hx with ⟨zx, hzx_seg, hzx_ball⟩
  rcases Set.mem_iUnion₂.mp hp with ⟨zp, hzp_seg, hzp_ball⟩
  rcases hzx_seg with ⟨ax, _, rfl⟩
  rcases hzp_seg with ⟨ap, _, rfl⟩
  set zx' : Point3 := T.base + ax • T.direction with hzx_def
  set zp' : Point3 := T.base + ap • T.direction with hzp_def
  have hdist_x : ‖x - zx'‖ ≤ δ := by
    simpa [dist_eq_norm] using hzx_ball
  have hdist_p : ‖p - zp'‖ ≤ δ := by
    simpa [dist_eq_norm] using hzp_ball
  have hvec : x - p = (x - zx') + (ax - ap) • T.direction + (zp' - p) := by
    have h2 : (x - zx') + (ax - ap) • T.direction + (zp' - p) = x - p := by
      calc
        (x - zx') + (ax - ap) • T.direction + (zp' - p)
          = x - zx' + ((ax - ap) • T.direction + zp' - p) := by abel
        _ = x - (T.base + ax • T.direction) + ((ax - ap) • T.direction + (T.base + ap • T.direction) - p) := by
          rw [hzx_def, hzp_def] <;> rfl
        _ = x - p := by
          have h3 : x - (T.base + ax • T.direction) + ((ax - ap) • T.direction + (T.base + ap • T.direction) - p) =
              x - p := by
            have h4 : (ax - ap) • T.direction = ax • T.direction - ap • T.direction := by
              rw [sub_smul]
            rw [h4]
            simp [sub_eq_add_neg] <;> abel
          exact h3
    exact h2.symm
  have h1 : inner ℝ (x - p) n =
      inner ℝ (x - zx') n + (ax - ap) * inner ℝ T.direction n + inner ℝ (zp' - p) n := by
    rw [hvec]
    simp [inner_add_left, inner_smul_left] <;> ring
  have h2 : |inner ℝ (x - zx') n| ≤ δ := by
    have hcs : |inner ℝ (x - zx') n| ≤ ‖x - zx'‖ * ‖n‖ :=
      abs_real_inner_le_norm (x - zx') n
    have hcs2 : |inner ℝ (x - zx') n| ≤ ‖x - zx'‖ := by
      rw [hn] at hcs
      simpa using hcs
    exact hcs2.trans hdist_x
  have h3 : |inner ℝ (zp' - p) n| ≤ δ := by
    have hcs : |inner ℝ (zp' - p) n| ≤ ‖zp' - p‖ * ‖n‖ :=
      abs_real_inner_le_norm (zp' - p) n
    have hcs2 : |inner ℝ (zp' - p) n| ≤ ‖zp' - p‖ := by
      rw [hn] at hcs
      simpa using hcs
    have hnorm2 : ‖zp' - p‖ = ‖p - zp'‖ := by rw [norm_sub_rev]
    rw [hnorm2] at hcs2
    exact hcs2.trans hdist_p
  have h4 : |ax - ap| ≤ ‖x - p‖ + 2 * δ := by
    have h5 : ‖zx' - zp'‖ = |ax - ap| := by
      have h6 : zx' - zp' = (ax - ap) • T.direction := by
        have h61 : zx' - zp' = (T.base + ax • T.direction) - (T.base + ap • T.direction) := by
          rw [hzx_def, hzp_def] <;> rfl
        rw [h61]
        have h62 : (T.base + ax • T.direction) - (T.base + ap • T.direction) =
            ax • T.direction - ap • T.direction := by simp
        rw [h62]
        have h63 : ax • T.direction - ap • T.direction = (ax - ap) • T.direction := by
          rw [sub_smul]
        exact h63
      rw [h6]
      have h7 : ‖(ax - ap) • T.direction‖ = |ax - ap| * ‖T.direction‖ := by
        exact norm_smul (ax - ap) T.direction
      rw [h7, T.direction_unit]
      <;> simp
    have h7 : ‖zx' - zp'‖ ≤ ‖zx' - x‖ + ‖x - p‖ + ‖p - zp'‖ := by
      have h71 : zx' - zp' = (zx' - x) + (x - zp') := by abel
      rw [h71]
      have h72 : ‖(zx' - x) + (x - zp')‖ ≤ ‖zx' - x‖ + ‖x - zp'‖ := by
        apply norm_add_le
      have h73 : ‖x - zp'‖ ≤ ‖x - p‖ + ‖p - zp'‖ := by
        have h74 : x - zp' = (x - p) + (p - zp') := by abel
        rw [h74]
        apply norm_add_le
      linarith
    have h9 : ‖zx' - x‖ = ‖x - zx'‖ := by rw [norm_sub_rev]
    rw [h5, h9] at h7
    linarith
  let a := inner ℝ (x - zx') n
  let b := (ax - ap) * inner ℝ T.direction n
  let c := inner ℝ (zp' - p) n
  have h_abs1 : |a + b + c| ≤ |a| + |b| + |c| := by
    have h_tri1 : |a + b + c| ≤ |a + b| + |c| := by
      have h : |(a + b) + c| ≤ |a + b| + |c| := by
        have h1 : (a + b) + c ≤ |a + b| + |c| := by linarith [le_abs_self (a+b), le_abs_self c]
        have h2a : -(a + b) ≤ |a + b| := by
          calc -(a + b) ≤ |-(a + b)| := le_abs_self (-(a + b))
            _ = |a + b| := by rw [abs_neg]
        have h2c : -c ≤ |c| := by
          calc -c ≤ |-c| := le_abs_self (-c)
            _ = |c| := by rw [abs_neg]
        have h2 : -((a + b) + c) ≤ |a + b| + |c| := by linarith
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      simpa [add_assoc] using h
    have h_tri2 : |a + b| ≤ |a| + |b| := by
      have h1 : a + b ≤ |a| + |b| := by linarith [le_abs_self a, le_abs_self b]
      have h2a : -a ≤ |a| := by
        calc -a ≤ |-a| := le_abs_self (-a)
          _ = |a| := by rw [abs_neg]
      have h2b : -b ≤ |b| := by
        calc -b ≤ |-b| := le_abs_self (-b)
          _ = |b| := by rw [abs_neg]
      have h2 : -(a + b) ≤ |a| + |b| := by linarith
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have h_bound : |a + b + c| ≤ 2 * δ + (‖x - p‖ + 2 * δ) * |inner ℝ T.direction n| := by
    calc
      |a + b + c|
        ≤ |a| + |b| + |c| := h_abs1
      _ ≤ δ + |ax - ap| * |inner ℝ T.direction n| + δ := by
        simp only [a, b, c, abs_mul] <;> linarith
      _ ≤ δ + (‖x - p‖ + 2 * δ) * |inner ℝ T.direction n| + δ := by
        gcongr <;> linarith
      _ = 2 * δ + (‖x - p‖ + 2 * δ) * |inner ℝ T.direction n| := by ring
  have h_eq : inner ℝ (x - p) n = a + b + c := by
    exact h1
  have h_goal : |inner ℝ (x - p) n| ≤ 2 * δ + (‖x - p‖ + 2 * δ) * |inner ℝ T.direction n| := by
    have h_eq2 : |inner ℝ (x - p) n| = |a + b + c| := by
      rw [h_eq]
    rw [h_eq2]
    exact h_bound
  exact h_goal

end Kakeya.Assouad

namespace Kakeya.Assouad

open MeasureTheory Metric Set

/--
Real arithmetic helper: the Córdoba slab width absorbs the tube projection
variation when `rho ≤ 1/1000` and `tau ≤ sqrt rho`.
-/
lemma cordoba_slab_width_absorbs_variation
    (rho tau L : ℝ)
    (normal : Point3)
    (x p : Point3)
    (hrho_pos : 0 < rho)
    (hrho_small : rho ≤ 1 / 1000)
    (htau : rho ≤ tau)
    (htau_sqrt : tau ≤ Real.sqrt rho)
    (hL : 0 ≤ L)
    (hdist : ‖x - p‖ ≤ 4 * tau)
    (hbound : |inner ℝ (x - p) normal| ≤
        2 * rho + (4 * tau + 2 * rho) * (10 * rho + L * (tau + 4 * rho))) :
    |inner ℝ (x - p) normal| ≤ 20 * max 1 L * rho := by
  have h_sqrt_bound : Real.sqrt rho ≤ 1 / 30 := by
    have h2 : Real.sqrt rho ≤ Real.sqrt (1 / 1000) := Real.sqrt_le_sqrt (by linarith)
    have h3 : Real.sqrt (1 / 1000) ≤ 1 / 30 := by
      nlinarith [Real.sqrt_nonneg (1 / 1000), Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 1000 by norm_num)]
    linarith
  have h4 : tau ≤ 1 / 30 := by linarith [htau_sqrt, h_sqrt_bound]
  have h5 : tau * rho ≤ rho / 30 := by
    have h6 : tau * rho ≤ (1 / 30) * rho := by gcongr <;> linarith
    linarith
  have h7 : tau ^ 2 ≤ rho := by
    have htau_nonneg : 0 ≤ tau := by linarith
    nlinarith [Real.sqrt_nonneg rho, Real.sq_sqrt (show 0 ≤ rho by linarith)]
  have h10 : rho ^ 2 ≤ rho / 1000 := by nlinarith
  by_cases hL1 : L ≤ 1
  · have hmax : max 1 L = 1 := by simp [hL1] <;> linarith
    rw [hmax]
    nlinarith
  · have hL1' : 1 < L := by linarith
    have hmax : max 1 L = L := by simp [hL1'] <;> linarith
    rw [hmax]
    nlinarith [mul_nonneg hL (show 0 ≤ rho by linarith)]

/--
Cross-tube slab containment core.

Given two rho-tubes T_i and T_j intersecting at p_m, with p on T_i and x on T_j,
both within tau of p_m, and direction incidences bounded by C_i, C_j, then
|inner(x-p, n)| ≤ (tau + 2*rho) * (C_i + C_j) + 4*rho.
-/
lemma slab_containment_core
    {rho : ℝ} (hrho : 0 ≤ rho)
    {tau : ℝ}
    {n : Point3} (hn : ‖n‖ = 1)
    {T_i T_j : DeltaTube rho}
    {p p_m x : Point3}
    (hp_i : p ∈ T_i.carrier) (hpm_i : p_m ∈ T_i.carrier)
    (hpm_j : p_m ∈ T_j.carrier) (hx_j : x ∈ T_j.carrier)
    (hdist_p : dist p p_m ≤ tau)
    (hdist_x : dist x p_m ≤ tau)
    {C_i C_j : ℝ}
    (hC_i_nonneg : 0 ≤ C_i)
    (hC_j_nonneg : 0 ≤ C_j)
    (hC_i : |inner ℝ T_i.direction n| ≤ C_i)
    (hC_j : |inner ℝ T_j.direction n| ≤ C_j) :
    |inner ℝ (x - p) n| ≤ (tau + 2 * rho) * (C_i + C_j) + 4 * rho := by
  have h1 : |inner ℝ (p_m - p) n| ≤ 2 * rho + (dist p_m p + 2 * rho) * C_i := by
    have h_raw := tube_two_point_projection_bound hrho T_i n hn p_m p hpm_i hp_i
    have h_nonneg : 0 ≤ dist p_m p + 2 * rho := by positivity
    calc |inner ℝ (p_m - p) n|
      ≤ 2 * rho + (dist p_m p + 2 * rho) * |inner ℝ T_i.direction n| := h_raw
    _ ≤ 2 * rho + (dist p_m p + 2 * rho) * C_i := by
      gcongr
      <;> exact hC_i
  have h2 : |inner ℝ (x - p_m) n| ≤ 2 * rho + (dist x p_m + 2 * rho) * C_j := by
    have h_raw := tube_two_point_projection_bound hrho T_j n hn x p_m hx_j hpm_j
    have h_nonneg : 0 ≤ dist x p_m + 2 * rho := by positivity
    calc |inner ℝ (x - p_m) n|
      ≤ 2 * rho + (dist x p_m + 2 * rho) * |inner ℝ T_j.direction n| := h_raw
    _ ≤ 2 * rho + (dist x p_m + 2 * rho) * C_j := by
      gcongr
      <;> exact hC_j
  have h3 : inner ℝ (x - p) n = inner ℝ (x - p_m) n + inner ℝ (p_m - p) n := by
    have h : x - p = (x - p_m) + (p_m - p) := by abel
    rw [h, inner_add_left]
  rw [h3]
  have h4 : |inner ℝ (x - p_m) n + inner ℝ (p_m - p) n| ≤
      |inner ℝ (x - p_m) n| + |inner ℝ (p_m - p) n| := by
    simpa [Real.norm_eq_abs] using norm_add_le (E := ℝ) (inner ℝ (x - p_m) n) (inner ℝ (p_m - p) n)
  have h5 : dist p_m p = dist p p_m := dist_comm _ _
  have h1' : |inner ℝ (p_m - p) n| ≤ 2 * rho + (dist p p_m + 2 * rho) * C_i := by
    rw [h5] at h1
    exact h1
  calc
    |inner ℝ (x - p_m) n + inner ℝ (p_m - p) n|
      ≤ |inner ℝ (x - p_m) n| + |inner ℝ (p_m - p) n| := h4
    _ ≤ (2 * rho + (dist x p_m + 2 * rho) * C_j) +
        (2 * rho + (dist p p_m + 2 * rho) * C_i) := by gcongr
    _ = (dist x p_m + 2 * rho) * C_j + (dist p p_m + 2 * rho) * C_i + 4 * rho := by ring
    _ ≤ (tau + 2 * rho) * C_j + (tau + 2 * rho) * C_i + 4 * rho := by
      have h6 : (dist x p_m + 2 * rho) * C_j ≤ (tau + 2 * rho) * C_j :=
        mul_le_mul_of_nonneg_right (by linarith) hC_j_nonneg
      have h7 : (dist p p_m + 2 * rho) * C_i ≤ (tau + 2 * rho) * C_i :=
        mul_le_mul_of_nonneg_right (by linarith) hC_i_nonneg
      linarith
    _ = (tau + 2 * rho) * (C_i + C_j) + 4 * rho := by ring

/--
Arithmetic: the cross-tube slab containment bound fits in 20*max(1,L)*rho.

Given C_i = 10*rho + L*(tau + 4*rho), C_j = 10*rho + L*(2*tau + 4*rho),
with 0 < rho ≤ 1/1000, rho ≤ tau, tau^2 ≤ rho, 0 ≤ L, we have
(tau + 2*rho) * (C_i + C_j) + 4*rho ≤ 20 * max(1, L) * rho.
-/
lemma slab_containment_constant
    (rho tau L : ℝ)
    (hrho_pos : 0 < rho)
    (hrho_small : rho ≤ 1 / 1000)
    (hrho_le_tau : rho ≤ tau)
    (htau_sq : tau ^ 2 ≤ rho)
    (hL_nonneg : 0 ≤ L)
    (C_i C_j : ℝ)
    (hCi : C_i = 10 * rho + L * (tau + 4 * rho))
    (hCj : C_j = 10 * rho + L * (2 * tau + 4 * rho)) :
    (tau + 2 * rho) * (C_i + C_j) + 4 * rho ≤ 20 * max 1 L * rho := by
  rw [hCi, hCj]
  have htau_nonneg : 0 ≤ tau := by linarith
  have hsqrt_le_1_30 : Real.sqrt rho ≤ 1 / 30 := by
    have h1 : Real.sqrt rho ≤ Real.sqrt (1 / 1000) := Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt (1 / 1000) ≤ 1 / 30 := by
      rw [Real.sqrt_le_left] <;> norm_num
    linarith
  have htau_le_1_30 : tau ≤ 1 / 30 := by
    have h3 : tau ≤ Real.sqrt rho := by
      have h4 : 0 ≤ tau := htau_nonneg
      nlinarith [Real.sqrt_nonneg rho, Real.sq_sqrt (show 0 ≤ rho by linarith)]
    linarith [hsqrt_le_1_30]
  have htau_rho_le : tau * rho ≤ rho / 30 := by
    calc tau * rho ≤ (1 / 30) * rho := by gcongr
      _ = rho / 30 := by ring
  have hrho2_le : rho ^ 2 ≤ rho / 1000 := by nlinarith
  by_cases hL1 : L ≤ 1
  · have hmax : max 1 L = 1 := by simp [hL1] <;> linarith
    rw [hmax]
    nlinarith
  · have hL1' : 1 < L := by linarith
    have hmax : max 1 L = L := by simp [hL1'] <;> linarith
    rw [hmax]
    nlinarith [mul_nonneg hL_nonneg (show 0 ≤ rho by linarith)]

/--
The same slab-containment arithmetic with the enlarged-ball condition
`tau ^ 2 ≤ 4 * rho`.

This is the form needed after the fine parent-cell pullback: if the target
radius is at most `sqrt rho`, then the actual doubled Córdoba radius has
square at most `4 * rho`.  The original slab width still absorbs the fixed
enlargement.
-/
lemma slab_containment_constant_four
    (rho tau L : ℝ)
    (hrho_pos : 0 < rho)
    (hrho_small : rho ≤ 1 / 1000)
    (hrho_le_tau : rho ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * rho)
    (hL_nonneg : 0 ≤ L)
    (C_i C_j : ℝ)
    (hCi : C_i = 10 * rho + L * (tau + 4 * rho))
    (hCj : C_j = 10 * rho + L * (2 * tau + 4 * rho)) :
    (tau + 2 * rho) * (C_i + C_j) + 4 * rho ≤
      20 * max 1 L * rho := by
  rw [hCi, hCj]
  have hrho_nonneg : 0 ≤ rho := hrho_pos.le
  have htau_nonneg : 0 ≤ tau := hrho_nonneg.trans hrho_le_tau
  have htau_sq_small : tau ^ 2 ≤ 4 / 1000 := by
    calc
      tau ^ 2 ≤ 4 * rho := htau_sq
      _ ≤ 4 * (1 / 1000 : ℝ) := by gcongr
      _ = 4 / 1000 := by ring
  have htau_le_one_fifteenth : tau ≤ 1 / 15 := by
    nlinarith [sq_nonneg (tau - 1 / 15)]
  have htau_rho_le : tau * rho ≤ rho / 15 := by
    calc
      tau * rho ≤ (1 / 15 : ℝ) * rho := by gcongr
      _ = rho / 15 := by ring
  have hrho2_le : rho ^ 2 ≤ rho / 1000 := by
    nlinarith
  by_cases hL1 : L ≤ 1
  · have hmax : max 1 L = 1 := by simp [hL1]
    rw [hmax]
    have hLtauSq : L * tau ^ 2 ≤ tau ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hL1) (sq_nonneg tau)]
    have hLtauRho : L * (tau * rho) ≤ tau * rho := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hL1)
        (mul_nonneg htau_nonneg hrho_nonneg)]
    have hLrhoSq : L * rho ^ 2 ≤ rho ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hL1) (sq_nonneg rho)]
    nlinarith
  · have hL1' : 1 < L := lt_of_not_ge hL1
    have hmax : max 1 L = L := by simp [hL1'.le]
    rw [hmax]
    have hnonLrho : rho ≤ L * rho := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hL1'.le) hrho_nonneg]
    have hnonLtauRho : tau * rho ≤ L * (tau * rho) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hL1'.le)
        (mul_nonneg htau_nonneg hrho_nonneg)]
    have hnonLrhoSq : rho ^ 2 ≤ L * rho ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hL1'.le) (sq_nonneg rho)]
    nlinarith [mul_nonneg hL_nonneg htau_nonneg,
      mul_nonneg hL_nonneg hrho_nonneg]

/--
WZ1 slab projection variation: for two points in the same propertyOne tube
within the 3*tau ball around q, their projections onto the cell normal differ
by at most `20 * max(1, L) * rho`.

This is the geometric containment step of the Córdoba argument.
-/
lemma wz1_slab_projection_variation
    {delta sigma epsilon₁ epsilon₂ epsilon₃ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (first : WZ1BalancedCoverData (sigma := sigma) (epsilon := epsilon₁) U Y rho)
    (plane : WZ1PlaneMapData Y)
    (tau : Kakeya.Streamlined.AdmissibleScale delta)
    (tauAtRho : Kakeya.Streamlined.AdmissibleScale rho.1)
    (tauCover : WZ1BalancedCoverData (sigma := sigma) (epsilon := epsilon₂)
      first.coarseUniform first.coarseShading tauAtRho)
    (robustScale : Kakeya.Streamlined.AdmissibleScale rho.1)
    (robustCover : WZ1BalancedCoverData (sigma := sigma) (epsilon := epsilon₁)
      first.coarseUniform tauCover.refined robustScale)
    (data : WZ1Lemma17RefinementData (epsilon₃ := epsilon₃)
      first plane tau tauAtRho tauCover robustScale robustCover)
    (q : Point3)
    (hq : q ∈ data.propertyThree.union)
    (j : Fin (U.coarse rho).card)
    (p x : Point3)
    (hp_p : p ∈ data.propertyOne.carrier j)
    (hp_q : dist p q ≤ tau.1)
    (hx_p : x ∈ data.propertyOne.carrier j)
    (hx_q : dist x q ≤ 3 * tau.1)
    (hrho_pos : 0 < rho.1)
    (hrho_small : rho.1 ≤ 1 / 1000)
    (htau : rho.1 ≤ tau.1)
    (htau_sqrt : tau.1 ≤ Real.sqrt rho.1) :
    |inner ℝ x (wz1Lemma17CellNormal first plane q) -
     inner ℝ p (wz1Lemma17CellNormal first plane q)| ≤
    20 * max 1 (plane.lipschitzConstant : ℝ) * rho.1 := by
  set normal := wz1Lemma17CellNormal first plane q with hnormal_def
  set rep_p := first.representative (first.cell p) with hrep_p_def
  set rep_q := first.representative (first.cell q) with hrep_q_def
  set T_j := (U.coarse rho).tube j with hT_j_def

  -- Subshading chain: propertyOne → robustCover.refined → tauCover.refined → first.coarseShading
  have h_p_coarse : p ∈ first.coarseShading.carrier j :=
    tauCover.subshading j (robustCover.subshading j (data.propertyOne_sub_robust j hp_p))
  have h_p_union : p ∈ first.coarseShading.union := ⟨j, h_p_coarse⟩

  have h_refined_to_coarse : first.refined.union ⊆ first.coarseShading.union := by
    intro x hx
    rcases hx with ⟨i, hi⟩
    exact ⟨(U.cover rho).parent i, first.point_compatibility i x hi⟩

  have h_prop3_to_const : data.propertyThree.union ⊆ data.constantShading.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, data.propertyThree_subshading i hi⟩
  have h_const_to_prop1 : data.constantShading.union ⊆ data.propertyOne.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, data.constant_subshading i hi⟩
  have h_prop1_to_robust : data.propertyOne.union ⊆ robustCover.refined.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, data.propertyOne_sub_robust i hi⟩
  have h_robust_to_tau : robustCover.refined.union ⊆ tauCover.refined.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, robustCover.subshading i hi⟩
  have h_tau_to_coarse : tauCover.refined.union ⊆ first.coarseShading.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, tauCover.subshading i hi⟩
  have h_q_coarse : q ∈ first.coarseShading.union :=
    h_tau_to_coarse (h_robust_to_tau (h_prop1_to_robust (h_const_to_prop1 (h_prop3_to_const hq))))

  -- Cell fine witnesses
  have hrep_p_witness : rep_p ∈ first.refined.union ∧ first.cell rep_p = first.cell p :=
    first.cell_fine_witness p h_p_union
  have hrep_q_witness : rep_q ∈ first.refined.union ∧ first.cell rep_q = first.cell q :=
    first.cell_fine_witness q h_q_coarse

  have hrep_p_refined : rep_p ∈ first.refined.union := hrep_p_witness.1
  have hrep_q_refined : rep_q ∈ first.refined.union := hrep_q_witness.1
  have hrep_p_coarse : rep_p ∈ first.coarseShading.union := h_refined_to_coarse hrep_p_refined
  have hrep_q_coarse : rep_q ∈ first.coarseShading.union := h_refined_to_coarse hrep_q_refined

  -- Cell diameter bounds
  have hcell_p : dist p rep_p ≤ 2 * rho.1 := by
    have hsame : first.cell p = first.cell rep_p := hrep_p_witness.2.symm
    exact first.cell_diameter p h_p_union rep_p hrep_p_coarse hsame
  have hcell_q : dist q rep_q ≤ 2 * rho.1 := by
    have hsame : first.cell q = first.cell rep_q := hrep_q_witness.2.symm
    exact first.cell_diameter q h_q_coarse rep_q hrep_q_coarse hsame

  -- Distance between representatives
  have hdist_rep : dist rep_p rep_q ≤ tau.1 + 4 * rho.1 := by
    have h1 : dist rep_p rep_q ≤ dist rep_p p + dist p rep_q := dist_triangle _ _ _
    have h2 : dist p rep_q ≤ dist p q + dist q rep_q := dist_triangle _ _ _
    have h3 : dist rep_p p = dist p rep_p := dist_comm _ _
    linarith [hcell_p, hcell_q, hp_q]

  -- Representatives are in Y.union
  have h_refined_to_Y : first.refined.union ⊆ Y.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, first.subshading i hi⟩
  have hrep_p_Y : rep_p ∈ Y.union := h_refined_to_Y hrep_p_refined
  have hrep_q_Y : rep_q ∈ Y.union := h_refined_to_Y hrep_q_refined

  -- Normal is unit
  have hnormal_unit : ‖normal‖ = 1 := by
    simpa [hnormal_def, wz1Lemma17CellNormal] using plane.unit rep_q hrep_q_Y

  -- Direction bound via representative_associated
  rcases first.representative_associated j p h_p_coarse with ⟨i, hparent, hrep_i⟩
  have hrep_i_Y : rep_p ∈ Y.carrier i := first.subshading i hrep_i

  rcases first.direction_alignment i with ⟨sign, hsign, halign⟩
  have hdir_eq : (U.coarse rho).tube ((U.cover rho).parent i) = T_j := by
    congr
    <;> exact hparent
  rw [hdir_eq] at halign

  have hincidence : |inner ℝ (F.tube i).direction (plane.planeMap rep_p)| ≤ 6 * delta :=
    plane.incidence i rep_p hrep_i_Y

  have h_planeMap_unit : ‖plane.planeMap rep_p‖ = 1 := plane.unit rep_p hrep_p_Y
  have h_abs_sign : |sign| = 1 := by rcases hsign with (rfl | rfl) <;> norm_num

  have hdir1 : |inner ℝ T_j.direction (plane.planeMap rep_p)| ≤ 6 * delta + 4 * rho.1 := by
    have h_eq : T_j.direction = (T_j.direction - sign • (F.tube i).direction) + sign • (F.tube i).direction := by abel
    have h1 : |inner ℝ T_j.direction (plane.planeMap rep_p)| ≤
        |inner ℝ (T_j.direction - sign • (F.tube i).direction) (plane.planeMap rep_p)| +
        |inner ℝ (sign • (F.tube i).direction) (plane.planeMap rep_p)| := by
      let a : ℝ := inner ℝ (T_j.direction - sign • (F.tube i).direction) (plane.planeMap rep_p)
      let b : ℝ := inner ℝ (sign • (F.tube i).direction) (plane.planeMap rep_p)
      have h_eq2 : inner ℝ T_j.direction (plane.planeMap rep_p) = a + b := by
        rw [h_eq, inner_add_left] <;> rfl
      rw [h_eq2]
      have h_tri : |a + b| ≤ |a| + |b| := by
        have h1 : a + b ≤ |a| + |b| := by linarith [le_abs_self a, le_abs_self b]
        have h2a : -a ≤ |a| := by
          calc -a ≤ |-a| := le_abs_self (-a)
            _ = |a| := by rw [abs_neg]
        have h2b : -b ≤ |b| := by
          calc -b ≤ |-b| := le_abs_self (-b)
            _ = |b| := by rw [abs_neg]
        have h2 : -(a + b) ≤ |a| + |b| := by linarith
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      exact h_tri
    have h2 : |inner ℝ (T_j.direction - sign • (F.tube i).direction) (plane.planeMap rep_p)| ≤
        ‖T_j.direction - sign • (F.tube i).direction‖ := by
      have h_cs := abs_real_inner_le_norm (T_j.direction - sign • (F.tube i).direction) (plane.planeMap rep_p)
      have h_unit : ‖plane.planeMap rep_p‖ = 1 := h_planeMap_unit
      have h : ‖T_j.direction - sign • (F.tube i).direction‖ * ‖plane.planeMap rep_p‖ = ‖T_j.direction - sign • (F.tube i).direction‖ := by
        rw [h_unit] <;> ring
      rw [h] at h_cs
      exact h_cs
    have h3 : |inner ℝ (sign • (F.tube i).direction) (plane.planeMap rep_p)| ≤ 6 * delta := by
      have h4 : inner ℝ (sign • (F.tube i).direction) (plane.planeMap rep_p) =
          sign * inner ℝ (F.tube i).direction (plane.planeMap rep_p) := by
        simpa [inner_smul_left, starRingEnd_apply] using rfl
      rw [h4, abs_mul, h_abs_sign, one_mul]
      exact hincidence
    linarith [h1, h2, h3, halign]

  have hdelta_le_rho : delta ≤ rho.1 := rho.2.1
  have hdir1' : |inner ℝ T_j.direction (plane.planeMap rep_p)| ≤ 10 * rho.1 := by
    linarith

  -- Lipschitz bound
  have hlipschitz : dist (plane.planeMap rep_p) (plane.planeMap rep_q) ≤
      (plane.lipschitzConstant : ℝ) * dist rep_p rep_q :=
    plane.lipschitz.dist_le_mul rep_p hrep_p_Y rep_q hrep_q_Y

  have hL_nonneg : 0 ≤ (plane.lipschitzConstant : ℝ) := by exact_mod_cast plane.lipschitzConstant.prop

  have hdir2 : |inner ℝ T_j.direction normal| ≤
      10 * rho.1 + (plane.lipschitzConstant : ℝ) * (tau.1 + 4 * rho.1) := by
    have h_diff : inner ℝ T_j.direction normal - inner ℝ T_j.direction (plane.planeMap rep_p) =
        inner ℝ T_j.direction (normal - plane.planeMap rep_p) := by
      rw [inner_sub_right] <;> ring
    have h_tri : |inner ℝ T_j.direction normal| ≤
        |inner ℝ T_j.direction (plane.planeMap rep_p)| + |inner ℝ T_j.direction (normal - plane.planeMap rep_p)| := by
      let a : ℝ := inner ℝ T_j.direction (plane.planeMap rep_p)
      let b : ℝ := inner ℝ T_j.direction (normal - plane.planeMap rep_p)
      have h_eq : inner ℝ T_j.direction normal = a + b := by
        dsimp only [a, b]
        rw [← h_diff] <;> ring
      rw [h_eq]
      have h_abs : |a + b| ≤ |a| + |b| := by
        have h1 : a + b ≤ |a| + |b| := by linarith [le_abs_self a, le_abs_self b]
        have h2a : -a ≤ |a| := by
          calc -a ≤ |-a| := le_abs_self (-a)
            _ = |a| := by rw [abs_neg]
        have h2b : -b ≤ |b| := by
          calc -b ≤ |-b| := le_abs_self (-b)
            _ = |b| := by rw [abs_neg]
        have h2 : -(a + b) ≤ |a| + |b| := by linarith
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      exact h_abs
    have h_bound2 : |inner ℝ T_j.direction (normal - plane.planeMap rep_p)| ≤ ‖normal - plane.planeMap rep_p‖ := by
      have h_cs : |inner ℝ T_j.direction (normal - plane.planeMap rep_p)| ≤
          ‖T_j.direction‖ * ‖normal - plane.planeMap rep_p‖ :=
        abs_real_inner_le_norm T_j.direction (normal - plane.planeMap rep_p)
      have h_unit : ‖T_j.direction‖ = 1 := T_j.direction_unit
      have h : ‖T_j.direction‖ * ‖normal - plane.planeMap rep_p‖ = ‖normal - plane.planeMap rep_p‖ := by
        rw [h_unit] <;> ring
      rw [h] at h_cs
      exact h_cs
    have h_dist_eq : ‖normal - plane.planeMap rep_p‖ = dist (plane.planeMap rep_p) (plane.planeMap rep_q) := by
      have h4 : ‖normal - plane.planeMap rep_p‖ = ‖plane.planeMap rep_q - plane.planeMap rep_p‖ := by rfl
      rw [h4]
      have h5 : ‖plane.planeMap rep_q - plane.planeMap rep_p‖ = ‖plane.planeMap rep_p - plane.planeMap rep_q‖ := by
        have h6 : plane.planeMap rep_q - plane.planeMap rep_p = -(plane.planeMap rep_p - plane.planeMap rep_q) := by abel
        rw [h6, norm_neg]
      rw [h5]
      exact (dist_eq_norm (plane.planeMap rep_p) (plane.planeMap rep_q)).symm
    calc
      |inner ℝ T_j.direction normal|
        ≤ |inner ℝ T_j.direction (plane.planeMap rep_p)| + |inner ℝ T_j.direction (normal - plane.planeMap rep_p)| := h_tri
      _ ≤ |inner ℝ T_j.direction (plane.planeMap rep_p)| + ‖normal - plane.planeMap rep_p‖ := by
        linarith [h_bound2]
      _ = |inner ℝ T_j.direction (plane.planeMap rep_p)| + dist (plane.planeMap rep_p) (plane.planeMap rep_q) := by
        rw [h_dist_eq]
      _ ≤ 10 * rho.1 + (plane.lipschitzConstant : ℝ) * dist rep_p rep_q := by linarith [hdir1', hlipschitz]
      _ ≤ 10 * rho.1 + (plane.lipschitzConstant : ℝ) * (tau.1 + 4 * rho.1) := by
        have h : (plane.lipschitzConstant : ℝ) * dist rep_p rep_q ≤ (plane.lipschitzConstant : ℝ) * (tau.1 + 4 * rho.1) := by
          exact mul_le_mul_of_nonneg_left hdist_rep hL_nonneg
        linarith

  -- Tube membership
  have htube_p : p ∈ T_j.carrier := data.propertyOne.subset_body j hp_p
  have htube_x : x ∈ T_j.carrier := data.propertyOne.subset_body j hx_p

  -- Distance bound
  have hdist_xp : dist x p ≤ 4 * tau.1 := by
    have h1 : dist x p ≤ dist x q + dist q p := dist_triangle _ _ _
    have h2 : dist q p = dist p q := dist_comm _ _
    rw [h2] at h1
    linarith [hx_q, hp_q]
  have hnorm_xp : ‖x - p‖ ≤ 4 * tau.1 := by
    simpa [dist_eq_norm] using hdist_xp

  -- Geometric bound
  have hgeom := tube_two_point_projection_bound (by linarith) T_j normal hnormal_unit x p htube_x htube_p
  have h_nonneg_dir : 0 ≤ 10 * rho.1 + (plane.lipschitzConstant : ℝ) * (tau.1 + 4 * rho.1) := by
    have h1 : 0 ≤ tau.1 := by linarith
    have h2 : 0 ≤ tau.1 + 4 * rho.1 := by linarith
    have h3 : 0 ≤ (plane.lipschitzConstant : ℝ) * (tau.1 + 4 * rho.1) := mul_nonneg hL_nonneg h2
    linarith
  have h_le1 : ‖x - p‖ + 2 * rho.1 ≤ 4 * tau.1 + 2 * rho.1 := by linarith [hnorm_xp]
  have hbound : |inner ℝ (x - p) normal| ≤
      2 * rho.1 + (4 * tau.1 + 2 * rho.1) * (10 * rho.1 + (plane.lipschitzConstant : ℝ) * (tau.1 + 4 * rho.1)) := by
    have h_step1 : |inner ℝ (x - p) normal| ≤
        2 * rho.1 + (‖x - p‖ + 2 * rho.1) * |inner ℝ T_j.direction normal| := hgeom
    have h_step2 : (‖x - p‖ + 2 * rho.1) * |inner ℝ T_j.direction normal| ≤
        (‖x - p‖ + 2 * rho.1) * (10 * rho.1 + (plane.lipschitzConstant : ℝ) * (tau.1 + 4 * rho.1)) := by
      exact mul_le_mul_of_nonneg_left hdir2 (by positivity)
    have h_step3 : (‖x - p‖ + 2 * rho.1) * (10 * rho.1 + (plane.lipschitzConstant : ℝ) * (tau.1 + 4 * rho.1)) ≤
        (4 * tau.1 + 2 * rho.1) * (10 * rho.1 + (plane.lipschitzConstant : ℝ) * (tau.1 + 4 * rho.1)) := by
      exact mul_le_mul_of_nonneg_right h_le1 h_nonneg_dir
    linarith [h_step1, h_step2, h_step3]

  -- Convert inner(x, normal) - inner(p, normal) to inner(x-p, normal)
  have hfinal : inner ℝ x normal - inner ℝ p normal = inner ℝ (x - p) normal := by
    rw [inner_sub_left] <;> ring
  rw [hfinal]

  -- Apply arithmetic lemma
  exact cordoba_slab_width_absorbs_variation rho.1 tau.1 (plane.lipschitzConstant : ℝ) normal x p
    hrho_pos hrho_small htau htau_sqrt hL_nonneg hnorm_xp hbound

/--
Direction-normal bound extracted from the slab projection variation proof.

For a propertyOne tube `j` incident to a point `p` within `tau` of `q`
(where `q` lies in propertyThree), the inner product of the tube direction
with the cell normal is bounded by `10 * rho + L * (tau + 4 * rho)`.
-/
lemma wz1_direction_normal_bound
    {delta sigma epsilon₁ epsilon₂ epsilon₃ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (first : WZ1BalancedCoverData (sigma := sigma) (epsilon := epsilon₁) U Y rho)
    (plane : WZ1PlaneMapData Y)
    (tau : Kakeya.Streamlined.AdmissibleScale delta)
    (tauAtRho : Kakeya.Streamlined.AdmissibleScale rho.1)
    (tauCover : WZ1BalancedCoverData (sigma := sigma) (epsilon := epsilon₂)
      first.coarseUniform first.coarseShading tauAtRho)
    (robustScale : Kakeya.Streamlined.AdmissibleScale rho.1)
    (robustCover : WZ1BalancedCoverData (sigma := sigma) (epsilon := epsilon₁)
      first.coarseUniform tauCover.refined robustScale)
    (data : WZ1Lemma17RefinementData (epsilon₃ := epsilon₃)
      first plane tau tauAtRho tauCover robustScale robustCover)
    (q : Point3)
    (hq : q ∈ data.propertyThree.union)
    (j : Fin (U.coarse rho).card)
    (p : Point3)
    (hp_p : p ∈ data.propertyOne.carrier j)
    (hp_q : dist p q ≤ tau.1) :
    |inner ℝ ((U.coarse rho).tube j).direction (wz1Lemma17CellNormal first plane q)| ≤
    10 * rho.1 + (plane.lipschitzConstant : ℝ) * (tau.1 + 4 * rho.1) := by
  set normal := wz1Lemma17CellNormal first plane q with hnormal_def
  set rep_p := first.representative (first.cell p) with hrep_p_def
  set rep_q := first.representative (first.cell q) with hrep_q_def
  set T_j := (U.coarse rho).tube j with hT_j_def

  have h_p_coarse : p ∈ first.coarseShading.carrier j :=
    tauCover.subshading j (robustCover.subshading j (data.propertyOne_sub_robust j hp_p))
  have h_p_union : p ∈ first.coarseShading.union := ⟨j, h_p_coarse⟩

  have h_refined_to_coarse : first.refined.union ⊆ first.coarseShading.union := by
    intro x hx
    rcases hx with ⟨i, hi⟩
    exact ⟨(U.cover rho).parent i, first.point_compatibility i x hi⟩

  have h_prop3_to_const : data.propertyThree.union ⊆ data.constantShading.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, data.propertyThree_subshading i hi⟩
  have h_const_to_prop1 : data.constantShading.union ⊆ data.propertyOne.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, data.constant_subshading i hi⟩
  have h_prop1_to_robust : data.propertyOne.union ⊆ robustCover.refined.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, data.propertyOne_sub_robust i hi⟩
  have h_robust_to_tau : robustCover.refined.union ⊆ tauCover.refined.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, robustCover.subshading i hi⟩
  have h_tau_to_coarse : tauCover.refined.union ⊆ first.coarseShading.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, tauCover.subshading i hi⟩
  have h_q_coarse : q ∈ first.coarseShading.union :=
    h_tau_to_coarse (h_robust_to_tau (h_prop1_to_robust (h_const_to_prop1 (h_prop3_to_const hq))))

  have hrep_p_witness : rep_p ∈ first.refined.union ∧ first.cell rep_p = first.cell p :=
    first.cell_fine_witness p h_p_union
  have hrep_q_witness : rep_q ∈ first.refined.union ∧ first.cell rep_q = first.cell q :=
    first.cell_fine_witness q h_q_coarse

  have hrep_p_refined : rep_p ∈ first.refined.union := hrep_p_witness.1
  have hrep_q_refined : rep_q ∈ first.refined.union := hrep_q_witness.1
  have hrep_p_coarse : rep_p ∈ first.coarseShading.union := h_refined_to_coarse hrep_p_refined
  have hrep_q_coarse : rep_q ∈ first.coarseShading.union := h_refined_to_coarse hrep_q_refined

  have hcell_p : dist p rep_p ≤ 2 * rho.1 := by
    have hsame : first.cell p = first.cell rep_p := hrep_p_witness.2.symm
    exact first.cell_diameter p h_p_union rep_p hrep_p_coarse hsame
  have hcell_q : dist q rep_q ≤ 2 * rho.1 := by
    have hsame : first.cell q = first.cell rep_q := hrep_q_witness.2.symm
    exact first.cell_diameter q h_q_coarse rep_q hrep_q_coarse hsame

  have hdist_rep : dist rep_p rep_q ≤ tau.1 + 4 * rho.1 := by
    have h1 : dist rep_p rep_q ≤ dist rep_p p + dist p rep_q := dist_triangle _ _ _
    have h2 : dist p rep_q ≤ dist p q + dist q rep_q := dist_triangle _ _ _
    have h3 : dist rep_p p = dist p rep_p := dist_comm _ _
    linarith [hcell_p, hcell_q, hp_q]

  have h_refined_to_Y : first.refined.union ⊆ Y.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, first.subshading i hi⟩
  have hrep_p_Y : rep_p ∈ Y.union := h_refined_to_Y hrep_p_refined
  have hrep_q_Y : rep_q ∈ Y.union := h_refined_to_Y hrep_q_refined

  rcases first.representative_associated j p h_p_coarse with ⟨i, hparent, hrep_i⟩
  have hrep_i_Y : rep_p ∈ Y.carrier i := first.subshading i hrep_i

  rcases first.direction_alignment i with ⟨sign, hsign, halign⟩
  have hdir_eq : (U.coarse rho).tube ((U.cover rho).parent i) = T_j := by
    congr <;> exact hparent
  rw [hdir_eq] at halign

  have hincidence : |inner ℝ (F.tube i).direction (plane.planeMap rep_p)| ≤ 6 * delta :=
    plane.incidence i rep_p hrep_i_Y

  have h_planeMap_unit : ‖plane.planeMap rep_p‖ = 1 := plane.unit rep_p hrep_p_Y
  have h_abs_sign : |sign| = 1 := by rcases hsign with (rfl | rfl) <;> norm_num

  have hdir1 : |inner ℝ T_j.direction (plane.planeMap rep_p)| ≤ 6 * delta + 4 * rho.1 := by
    have h_eq : T_j.direction = (T_j.direction - sign • (F.tube i).direction) + sign • (F.tube i).direction := by abel
    have h1 : |inner ℝ T_j.direction (plane.planeMap rep_p)| ≤
        |inner ℝ (T_j.direction - sign • (F.tube i).direction) (plane.planeMap rep_p)| +
        |inner ℝ (sign • (F.tube i).direction) (plane.planeMap rep_p)| := by
      let a : ℝ := inner ℝ (T_j.direction - sign • (F.tube i).direction) (plane.planeMap rep_p)
      let b : ℝ := inner ℝ (sign • (F.tube i).direction) (plane.planeMap rep_p)
      have h_eq2 : inner ℝ T_j.direction (plane.planeMap rep_p) = a + b := by
        rw [h_eq, inner_add_left] <;> rfl
      rw [h_eq2]
      have h_tri : |a + b| ≤ |a| + |b| := by
        have h1 : a + b ≤ |a| + |b| := by linarith [le_abs_self a, le_abs_self b]
        have h2a : -a ≤ |a| := by
          calc -a ≤ |-a| := le_abs_self (-a)
            _ = |a| := by rw [abs_neg]
        have h2b : -b ≤ |b| := by
          calc -b ≤ |-b| := le_abs_self (-b)
            _ = |b| := by rw [abs_neg]
        have h2 : -(a + b) ≤ |a| + |b| := by linarith
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      exact h_tri
    have h2 : |inner ℝ (T_j.direction - sign • (F.tube i).direction) (plane.planeMap rep_p)| ≤
        ‖T_j.direction - sign • (F.tube i).direction‖ := by
      have h_cs := abs_real_inner_le_norm (T_j.direction - sign • (F.tube i).direction) (plane.planeMap rep_p)
      have h_unit : ‖plane.planeMap rep_p‖ = 1 := h_planeMap_unit
      have h : ‖T_j.direction - sign • (F.tube i).direction‖ * ‖plane.planeMap rep_p‖ = ‖T_j.direction - sign • (F.tube i).direction‖ := by
        rw [h_unit] <;> ring
      rw [h] at h_cs
      exact h_cs
    have h3 : |inner ℝ (sign • (F.tube i).direction) (plane.planeMap rep_p)| ≤ 6 * delta := by
      have h4 : inner ℝ (sign • (F.tube i).direction) (plane.planeMap rep_p) =
          sign * inner ℝ (F.tube i).direction (plane.planeMap rep_p) := by
        simpa [inner_smul_left, starRingEnd_apply] using rfl
      rw [h4, abs_mul, h_abs_sign, one_mul]
      exact hincidence
    linarith [h1, h2, h3, halign]

  have hdelta_le_rho : delta ≤ rho.1 := rho.2.1
  have hdir1' : |inner ℝ T_j.direction (plane.planeMap rep_p)| ≤ 10 * rho.1 := by
    linarith

  have hlipschitz : dist (plane.planeMap rep_p) (plane.planeMap rep_q) ≤
      (plane.lipschitzConstant : ℝ) * dist rep_p rep_q :=
    plane.lipschitz.dist_le_mul rep_p hrep_p_Y rep_q hrep_q_Y

  have hL_nonneg : 0 ≤ (plane.lipschitzConstant : ℝ) := by exact_mod_cast plane.lipschitzConstant.prop

  have hdir2 : |inner ℝ T_j.direction normal| ≤
      10 * rho.1 + (plane.lipschitzConstant : ℝ) * (tau.1 + 4 * rho.1) := by
    have h_diff : inner ℝ T_j.direction normal - inner ℝ T_j.direction (plane.planeMap rep_p) =
        inner ℝ T_j.direction (normal - plane.planeMap rep_p) := by
      rw [inner_sub_right] <;> ring
    have h_tri : |inner ℝ T_j.direction normal| ≤
        |inner ℝ T_j.direction (plane.planeMap rep_p)| + |inner ℝ T_j.direction (normal - plane.planeMap rep_p)| := by
      let a : ℝ := inner ℝ T_j.direction (plane.planeMap rep_p)
      let b : ℝ := inner ℝ T_j.direction (normal - plane.planeMap rep_p)
      have h_eq : inner ℝ T_j.direction normal = a + b := by
        dsimp only [a, b]
        rw [← h_diff] <;> ring
      rw [h_eq]
      have h_abs : |a + b| ≤ |a| + |b| := by
        have h1 : a + b ≤ |a| + |b| := by linarith [le_abs_self a, le_abs_self b]
        have h2a : -a ≤ |a| := by
          calc -a ≤ |-a| := le_abs_self (-a)
            _ = |a| := by rw [abs_neg]
        have h2b : -b ≤ |b| := by
          calc -b ≤ |-b| := le_abs_self (-b)
            _ = |b| := by rw [abs_neg]
        have h2 : -(a + b) ≤ |a| + |b| := by linarith
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      exact h_abs
    have h_bound2 : |inner ℝ T_j.direction (normal - plane.planeMap rep_p)| ≤ ‖normal - plane.planeMap rep_p‖ := by
      have h_cs : |inner ℝ T_j.direction (normal - plane.planeMap rep_p)| ≤
          ‖T_j.direction‖ * ‖normal - plane.planeMap rep_p‖ :=
        abs_real_inner_le_norm T_j.direction (normal - plane.planeMap rep_p)
      have h_unit : ‖T_j.direction‖ = 1 := T_j.direction_unit
      have h : ‖T_j.direction‖ * ‖normal - plane.planeMap rep_p‖ = ‖normal - plane.planeMap rep_p‖ := by
        rw [h_unit] <;> ring
      rw [h] at h_cs
      exact h_cs
    have h_dist_eq : ‖normal - plane.planeMap rep_p‖ = dist (plane.planeMap rep_p) (plane.planeMap rep_q) := by
      have h4 : ‖normal - plane.planeMap rep_p‖ = ‖plane.planeMap rep_q - plane.planeMap rep_p‖ := by rfl
      rw [h4]
      have h5 : ‖plane.planeMap rep_q - plane.planeMap rep_p‖ = ‖plane.planeMap rep_p - plane.planeMap rep_q‖ := by
        have h6 : plane.planeMap rep_q - plane.planeMap rep_p = -(plane.planeMap rep_p - plane.planeMap rep_q) := by abel
        rw [h6, norm_neg]
      rw [h5]
      exact (dist_eq_norm (plane.planeMap rep_p) (plane.planeMap rep_q)).symm
    calc
      |inner ℝ T_j.direction normal|
        ≤ |inner ℝ T_j.direction (plane.planeMap rep_p)| + |inner ℝ T_j.direction (normal - plane.planeMap rep_p)| := h_tri
      _ ≤ |inner ℝ T_j.direction (plane.planeMap rep_p)| + ‖normal - plane.planeMap rep_p‖ := by
        linarith [h_bound2]
      _ = |inner ℝ T_j.direction (plane.planeMap rep_p)| + dist (plane.planeMap rep_p) (plane.planeMap rep_q) := by
        rw [h_dist_eq]
      _ ≤ 10 * rho.1 + (plane.lipschitzConstant : ℝ) * dist rep_p rep_q := by linarith [hdir1', hlipschitz]
      _ ≤ 10 * rho.1 + (plane.lipschitzConstant : ℝ) * (tau.1 + 4 * rho.1) := by
        have h : (plane.lipschitzConstant : ℝ) * dist rep_p rep_q ≤ (plane.lipschitzConstant : ℝ) * (tau.1 + 4 * rho.1) := by
          exact mul_le_mul_of_nonneg_left hdist_rep hL_nonneg
        linarith
  exact hdir2

/--
Generalized direction-normal bound: for a propertyOne tube `j` incident to a
point `p` within distance `d` of `q` (where `q` lies in propertyThree), the
inner product of the tube direction with the cell normal is bounded by
`10 * rho + L * (d + 4 * rho)`.
-/
lemma wz1_direction_normal_bound_general
    {delta sigma epsilon₁ epsilon₂ epsilon₃ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (first : WZ1BalancedCoverData (sigma := sigma) (epsilon := epsilon₁) U Y rho)
    (plane : WZ1PlaneMapData Y)
    (tau : Kakeya.Streamlined.AdmissibleScale delta)
    (tauAtRho : Kakeya.Streamlined.AdmissibleScale rho.1)
    (tauCover : WZ1BalancedCoverData (sigma := sigma) (epsilon := epsilon₂)
      first.coarseUniform first.coarseShading tauAtRho)
    (robustScale : Kakeya.Streamlined.AdmissibleScale rho.1)
    (robustCover : WZ1BalancedCoverData (sigma := sigma) (epsilon := epsilon₁)
      first.coarseUniform tauCover.refined robustScale)
    (data : WZ1Lemma17RefinementData (epsilon₃ := epsilon₃)
      first plane tau tauAtRho tauCover robustScale robustCover)
    (q : Point3)
    (hq : q ∈ data.propertyThree.union)
    (j : Fin (U.coarse rho).card)
    (p : Point3)
    (d : ℝ)
    (hp_p : p ∈ data.propertyOne.carrier j)
    (hp_q : dist p q ≤ d) :
    |inner ℝ ((U.coarse rho).tube j).direction (wz1Lemma17CellNormal first plane q)| ≤
    10 * rho.1 + (plane.lipschitzConstant : ℝ) * (d + 4 * rho.1) := by
  set normal := wz1Lemma17CellNormal first plane q with hnormal_def
  set rep_p := first.representative (first.cell p) with hrep_p_def
  set rep_q := first.representative (first.cell q) with hrep_q_def
  set T_j := (U.coarse rho).tube j with hT_j_def

  have h_p_coarse : p ∈ first.coarseShading.carrier j :=
    tauCover.subshading j (robustCover.subshading j (data.propertyOne_sub_robust j hp_p))
  have h_p_union : p ∈ first.coarseShading.union := ⟨j, h_p_coarse⟩

  have h_refined_to_coarse : first.refined.union ⊆ first.coarseShading.union := by
    intro x hx
    rcases hx with ⟨i, hi⟩
    exact ⟨(U.cover rho).parent i, first.point_compatibility i x hi⟩

  have h_prop3_to_const : data.propertyThree.union ⊆ data.constantShading.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, data.propertyThree_subshading i hi⟩
  have h_const_to_prop1 : data.constantShading.union ⊆ data.propertyOne.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, data.constant_subshading i hi⟩
  have h_prop1_to_robust : data.propertyOne.union ⊆ robustCover.refined.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, data.propertyOne_sub_robust i hi⟩
  have h_robust_to_tau : robustCover.refined.union ⊆ tauCover.refined.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, robustCover.subshading i hi⟩
  have h_tau_to_coarse : tauCover.refined.union ⊆ first.coarseShading.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, tauCover.subshading i hi⟩
  have h_q_coarse : q ∈ first.coarseShading.union :=
    h_tau_to_coarse (h_robust_to_tau (h_prop1_to_robust (h_const_to_prop1 (h_prop3_to_const hq))))

  have hrep_p_witness : rep_p ∈ first.refined.union ∧ first.cell rep_p = first.cell p :=
    first.cell_fine_witness p h_p_union
  have hrep_q_witness : rep_q ∈ first.refined.union ∧ first.cell rep_q = first.cell q :=
    first.cell_fine_witness q h_q_coarse

  have hrep_p_refined : rep_p ∈ first.refined.union := hrep_p_witness.1
  have hrep_q_refined : rep_q ∈ first.refined.union := hrep_q_witness.1
  have hrep_p_coarse : rep_p ∈ first.coarseShading.union := h_refined_to_coarse hrep_p_refined
  have hrep_q_coarse : rep_q ∈ first.coarseShading.union := h_refined_to_coarse hrep_q_refined

  have hcell_p : dist p rep_p ≤ 2 * rho.1 := by
    have hsame : first.cell p = first.cell rep_p := hrep_p_witness.2.symm
    exact first.cell_diameter p h_p_union rep_p hrep_p_coarse hsame
  have hcell_q : dist q rep_q ≤ 2 * rho.1 := by
    have hsame : first.cell q = first.cell rep_q := hrep_q_witness.2.symm
    exact first.cell_diameter q h_q_coarse rep_q hrep_q_coarse hsame

  have hdist_rep : dist rep_p rep_q ≤ d + 4 * rho.1 := by
    have h1 : dist rep_p rep_q ≤ dist rep_p p + dist p rep_q := dist_triangle _ _ _
    have h2 : dist p rep_q ≤ dist p q + dist q rep_q := dist_triangle _ _ _
    have h3 : dist rep_p p = dist p rep_p := dist_comm _ _
    linarith [hcell_p, hcell_q, hp_q]

  have h_refined_to_Y : first.refined.union ⊆ Y.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, first.subshading i hi⟩
  have hrep_p_Y : rep_p ∈ Y.union := h_refined_to_Y hrep_p_refined
  have hrep_q_Y : rep_q ∈ Y.union := h_refined_to_Y hrep_q_refined

  rcases first.representative_associated j p h_p_coarse with ⟨i, hparent, hrep_i⟩
  have hrep_i_Y : rep_p ∈ Y.carrier i := first.subshading i hrep_i

  rcases first.direction_alignment i with ⟨sign, hsign, halign⟩
  have hdir_eq : (U.coarse rho).tube ((U.cover rho).parent i) = T_j := by
    congr <;> exact hparent
  rw [hdir_eq] at halign

  have hincidence : |inner ℝ (F.tube i).direction (plane.planeMap rep_p)| ≤ 6 * delta :=
    plane.incidence i rep_p hrep_i_Y

  have h_planeMap_unit : ‖plane.planeMap rep_p‖ = 1 := plane.unit rep_p hrep_p_Y
  have h_abs_sign : |sign| = 1 := by rcases hsign with (rfl | rfl) <;> norm_num

  have hdir1 : |inner ℝ T_j.direction (plane.planeMap rep_p)| ≤ 6 * delta + 4 * rho.1 := by
    have h_eq : T_j.direction = (T_j.direction - sign • (F.tube i).direction) + sign • (F.tube i).direction := by abel
    have h1 : |inner ℝ T_j.direction (plane.planeMap rep_p)| ≤
        |inner ℝ (T_j.direction - sign • (F.tube i).direction) (plane.planeMap rep_p)| +
        |inner ℝ (sign • (F.tube i).direction) (plane.planeMap rep_p)| := by
      let a : ℝ := inner ℝ (T_j.direction - sign • (F.tube i).direction) (plane.planeMap rep_p)
      let b : ℝ := inner ℝ (sign • (F.tube i).direction) (plane.planeMap rep_p)
      have h_eq2 : inner ℝ T_j.direction (plane.planeMap rep_p) = a + b := by
        rw [h_eq, inner_add_left] <;> rfl
      rw [h_eq2]
      have h_tri : |a + b| ≤ |a| + |b| := by
        have h1 : a + b ≤ |a| + |b| := by linarith [le_abs_self a, le_abs_self b]
        have h2a : -a ≤ |a| := by
          calc -a ≤ |-a| := le_abs_self (-a)
            _ = |a| := by rw [abs_neg]
        have h2b : -b ≤ |b| := by
          calc -b ≤ |-b| := le_abs_self (-b)
            _ = |b| := by rw [abs_neg]
        have h2 : -(a + b) ≤ |a| + |b| := by linarith
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      exact h_tri
    have h2 : |inner ℝ (T_j.direction - sign • (F.tube i).direction) (plane.planeMap rep_p)| ≤
        ‖T_j.direction - sign • (F.tube i).direction‖ := by
      have h_cs := abs_real_inner_le_norm (T_j.direction - sign • (F.tube i).direction) (plane.planeMap rep_p)
      have h_unit : ‖plane.planeMap rep_p‖ = 1 := h_planeMap_unit
      have h : ‖T_j.direction - sign • (F.tube i).direction‖ * ‖plane.planeMap rep_p‖ = ‖T_j.direction - sign • (F.tube i).direction‖ := by
        rw [h_unit] <;> ring
      rw [h] at h_cs
      exact h_cs
    have h3 : |inner ℝ (sign • (F.tube i).direction) (plane.planeMap rep_p)| ≤ 6 * delta := by
      have h4 : inner ℝ (sign • (F.tube i).direction) (plane.planeMap rep_p) =
          sign * inner ℝ (F.tube i).direction (plane.planeMap rep_p) := by
        simpa [inner_smul_left, starRingEnd_apply] using rfl
      rw [h4, abs_mul, h_abs_sign, one_mul]
      exact hincidence
    linarith [h1, h2, h3, halign]

  have hdelta_le_rho : delta ≤ rho.1 := rho.2.1
  have hdir1' : |inner ℝ T_j.direction (plane.planeMap rep_p)| ≤ 10 * rho.1 := by linarith

  have hlipschitz : dist (plane.planeMap rep_p) (plane.planeMap rep_q) ≤
      (plane.lipschitzConstant : ℝ) * dist rep_p rep_q :=
    plane.lipschitz.dist_le_mul rep_p hrep_p_Y rep_q hrep_q_Y

  have hL_nonneg : 0 ≤ (plane.lipschitzConstant : ℝ) := by exact_mod_cast plane.lipschitzConstant.prop

  have hdir2 : |inner ℝ T_j.direction normal| ≤
      10 * rho.1 + (plane.lipschitzConstant : ℝ) * (d + 4 * rho.1) := by
    have h_diff : inner ℝ T_j.direction normal - inner ℝ T_j.direction (plane.planeMap rep_p) =
        inner ℝ T_j.direction (normal - plane.planeMap rep_p) := by
      rw [inner_sub_right] <;> ring
    have h_tri : |inner ℝ T_j.direction normal| ≤
        |inner ℝ T_j.direction (plane.planeMap rep_p)| + |inner ℝ T_j.direction (normal - plane.planeMap rep_p)| := by
      let a : ℝ := inner ℝ T_j.direction (plane.planeMap rep_p)
      let b : ℝ := inner ℝ T_j.direction (normal - plane.planeMap rep_p)
      have h_eq : inner ℝ T_j.direction normal = a + b := by
        dsimp only [a, b]
        rw [← h_diff] <;> ring
      rw [h_eq]
      have h_abs : |a + b| ≤ |a| + |b| := by
        have h1 : a + b ≤ |a| + |b| := by linarith [le_abs_self a, le_abs_self b]
        have h2a : -a ≤ |a| := by
          calc -a ≤ |-a| := le_abs_self (-a)
            _ = |a| := by rw [abs_neg]
        have h2b : -b ≤ |b| := by
          calc -b ≤ |-b| := le_abs_self (-b)
            _ = |b| := by rw [abs_neg]
        have h2 : -(a + b) ≤ |a| + |b| := by linarith
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      exact h_abs
    have h_bound2 : |inner ℝ T_j.direction (normal - plane.planeMap rep_p)| ≤ ‖normal - plane.planeMap rep_p‖ := by
      have h_cs : |inner ℝ T_j.direction (normal - plane.planeMap rep_p)| ≤
          ‖T_j.direction‖ * ‖normal - plane.planeMap rep_p‖ :=
        abs_real_inner_le_norm T_j.direction (normal - plane.planeMap rep_p)
      have h_unit : ‖T_j.direction‖ = 1 := T_j.direction_unit
      have h : ‖T_j.direction‖ * ‖normal - plane.planeMap rep_p‖ = ‖normal - plane.planeMap rep_p‖ := by
        rw [h_unit] <;> ring
      rw [h] at h_cs
      exact h_cs
    have h_dist_eq : ‖normal - plane.planeMap rep_p‖ = dist (plane.planeMap rep_p) (plane.planeMap rep_q) := by
      have h4 : ‖normal - plane.planeMap rep_p‖ = ‖plane.planeMap rep_q - plane.planeMap rep_p‖ := by rfl
      rw [h4]
      have h5 : ‖plane.planeMap rep_q - plane.planeMap rep_p‖ = ‖plane.planeMap rep_p - plane.planeMap rep_q‖ := by
        have h6 : plane.planeMap rep_q - plane.planeMap rep_p = -(plane.planeMap rep_p - plane.planeMap rep_q) := by abel
        rw [h6, norm_neg]
      rw [h5]
      exact (dist_eq_norm (plane.planeMap rep_p) (plane.planeMap rep_q)).symm
    calc
      |inner ℝ T_j.direction normal|
        ≤ |inner ℝ T_j.direction (plane.planeMap rep_p)| + |inner ℝ T_j.direction (normal - plane.planeMap rep_p)| := h_tri
      _ ≤ |inner ℝ T_j.direction (plane.planeMap rep_p)| + ‖normal - plane.planeMap rep_p‖ := by
        linarith [h_bound2]
      _ = |inner ℝ T_j.direction (plane.planeMap rep_p)| + dist (plane.planeMap rep_p) (plane.planeMap rep_q) := by
        rw [h_dist_eq]
      _ ≤ 10 * rho.1 + (plane.lipschitzConstant : ℝ) * dist rep_p rep_q := by linarith [hdir1', hlipschitz]
      _ ≤ 10 * rho.1 + (plane.lipschitzConstant : ℝ) * (d + 4 * rho.1) := by
        have h : (plane.lipschitzConstant : ℝ) * dist rep_p rep_q ≤ (plane.lipschitzConstant : ℝ) * (d + 4 * rho.1) := by
          exact mul_le_mul_of_nonneg_left hdist_rep hL_nonneg
        linarith
  exact hdir2

/-- The cell normal is a unit vector. -/
lemma wz1_cell_normal_unit
    {delta sigma epsilon₁ epsilon₂ epsilon₃ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (first : WZ1BalancedCoverData (sigma := sigma) (epsilon := epsilon₁) U Y rho)
    (plane : WZ1PlaneMapData Y)
    (tau : Kakeya.Streamlined.AdmissibleScale delta)
    (tauAtRho : Kakeya.Streamlined.AdmissibleScale rho.1)
    (tauCover : WZ1BalancedCoverData (sigma := sigma) (epsilon := epsilon₂)
      first.coarseUniform first.coarseShading tauAtRho)
    (robustScale : Kakeya.Streamlined.AdmissibleScale rho.1)
    (robustCover : WZ1BalancedCoverData (sigma := sigma) (epsilon := epsilon₁)
      first.coarseUniform tauCover.refined robustScale)
    (data : WZ1Lemma17RefinementData (epsilon₃ := epsilon₃)
      first plane tau tauAtRho tauCover robustScale robustCover)
    (q : Point3)
    (hq : q ∈ data.propertyThree.union) :
    ‖wz1Lemma17CellNormal first plane q‖ = 1 := by
  have h_prop3_to_const : data.propertyThree.union ⊆ data.constantShading.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, data.propertyThree_subshading i hi⟩
  have h_const_to_prop1 : data.constantShading.union ⊆ data.propertyOne.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, data.constant_subshading i hi⟩
  have h_prop1_to_robust : data.propertyOne.union ⊆ robustCover.refined.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, data.propertyOne_sub_robust i hi⟩
  have h_robust_to_tau : robustCover.refined.union ⊆ tauCover.refined.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, robustCover.subshading i hi⟩
  have h_tau_to_coarse : tauCover.refined.union ⊆ first.coarseShading.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, tauCover.subshading i hi⟩
  have h_q_coarse : q ∈ first.coarseShading.union :=
    h_tau_to_coarse (h_robust_to_tau (h_prop1_to_robust (h_const_to_prop1 (h_prop3_to_const hq))))
  have hrep_q_witness : first.representative (first.cell q) ∈ first.refined.union ∧
      first.cell (first.representative (first.cell q)) = first.cell q :=
    first.cell_fine_witness q h_q_coarse
  have h_refined_to_Y : first.refined.union ⊆ Y.union := by
    intro x hx; rcases hx with ⟨i, hi⟩; exact ⟨i, first.subshading i hi⟩
  have hrep_q_Y : first.representative (first.cell q) ∈ Y.union :=
    h_refined_to_Y hrep_q_witness.1
  simpa [wz1Lemma17CellNormal] using plane.unit (first.representative (first.cell q)) hrep_q_Y

end Kakeya.Assouad
