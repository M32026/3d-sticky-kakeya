import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DiagonalRescaling
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DiagonalReTubing
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CWANearbyScalesTransfer
import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CommonContainerDirectionCloseness
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Tube closeness lemmas for diagonal CWA transfer

Geometric foundation for transferring CWA nearby-scales under the diagonal
rescaling φ(x,y,z) = (x, m²/100·y, 100/m·z).

## Main results

- `tube_containment_from_closeness`: if base and direction are close enough,
  the thinner tube is contained in the thicker one.
- `diagonal_zero_point_closeness`: if T.carrier ⊆ G.carrier and both tubes
  have vertical direction component ≥ 1/2, then their WZ1 axis zero points
  are within 200·ρ.

## Whiteprint node

DiagonalCWATransfer — depends on DiagonalRescaling, CommonContainerDirectionCloseness.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set Finset

/-- Component bound for Point3. -/
private lemma point3_component_le_norm (x : Point3) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have h2 : ‖x‖ ^ 2 = (x 0)^2 + (x 1)^2 + (x 2)^2 := by
    have h_norm_sq : ‖x‖ ^ 2 = ∑ j : Fin 3, (x j)^2 :=
      EuclideanSpace.real_norm_sq_eq x
    rw [h_norm_sq]
    simp [Fin.sum_univ_succ] <;> ring
  have h3 : (x i)^2 ≤ ‖x‖^2 := by
    rw [h2]
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have h4 : 0 ≤ |x i| := by positivity
  have h5 : 0 ≤ ‖x‖ := by positivity
  have h6 : |x i| ^ 2 = (x i)^2 := by simp
  have h7 : |x i| ^ 2 ≤ ‖x‖ ^ 2 := by rw [h6]; exact h3
  nlinarith [sq_nonneg (|x i| - ‖x‖)]

/-- If |x| ≥ 1/2, then |x⁻¹| ≤ 2. -/
private lemma abs_inv_le_two {x : ℝ} (h : (1 / 2 : ℝ) ≤ |x|) : |x⁻¹| ≤ 2 := by
  have hx_ne_zero : x ≠ 0 := by
    intro h4; rw [h4] at h; simp at h <;> linarith
  have h1 : |x⁻¹| = (|x|)⁻¹ := by rw [abs_inv]
  rw [h1]
  have h2 : (|x|)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := by
    gcongr <;> linarith
  have h3 : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
  rw [h3] at h2
  exact h2

/-- If |x|, |y| ≥ 1/2 and |x - y| ≤ 4ρ, then |x⁻¹ - y⁻¹| ≤ 16ρ. -/
private lemma abs_inv_diff_bound {x y rho : ℝ}
    (hx : (1 / 2 : ℝ) ≤ |x|) (hy : (1 / 2 : ℝ) ≤ |y|)
    (h_diff : |x - y| ≤ 4 * rho) (hrho : 0 ≤ rho) :
    |x⁻¹ - y⁻¹| ≤ 16 * rho := by
  have hx0 : x ≠ 0 := by intro h4; rw [h4] at hx; simp at hx <;> linarith
  have hy0 : y ≠ 0 := by intro h4; rw [h4] at hy; simp at hy <;> linarith
  have h_denom : (1 / 2 : ℝ) * (1 / 2 : ℝ) ≤ |x| * |y| := by
    have h5 : (1 / 2 : ℝ) ≤ |x| := hx
    have h6 : (1 / 2 : ℝ) ≤ |y| := hy
    have h7 : 0 ≤ |x| := by positivity
    have h8 : 0 ≤ |y| := by positivity
    nlinarith
  have h_pos_denom : 0 < |x| * |y| := by positivity
  have h_main : |x⁻¹ - y⁻¹| = |x - y| / (|x| * |y|) := by
    have h1 : x⁻¹ - y⁻¹ = (y - x) / (x * y) := by
      field_simp [hx0, hy0] <;> ring
    rw [h1]
    have h2 : |(y - x) / (x * y)| = |y - x| / (|x| * |y|) := by
      rw [abs_div, abs_mul]
    rw [h2]
    have h3 : |y - x| = |x - y| := by
      have h4 : y - x = -(x - y) := by ring
      rw [h4, abs_neg]
    rw [h3]
  rw [h_main]
  have h91 : |x - y| / (|x| * |y|) ≤ (4 * rho) / (|x| * |y|) := by
    apply div_le_div_of_nonneg_right h_diff (le_of_lt h_pos_denom)
  have h_pos4 : 0 ≤ 4 * rho := by positivity
  have h92 : (4 * rho) / (|x| * |y|) ≤ (4 * rho) / ((1 / 2 : ℝ) * (1 / 2 : ℝ)) := by
    apply div_le_div_of_nonneg_left h_pos4 (by norm_num) h_denom
  have h10 : (1 / 2 : ℝ) * (1 / 2 : ℝ) = 1 / 4 := by norm_num
  have h11 : (4 * rho) / ((1 / 2 : ℝ) * (1 / 2 : ℝ)) = 16 * rho := by
    rw [h10] <;> field_simp <;> ring
  have h12 : |x - y| / (|x| * |y|) ≤ 16 * rho := by
    calc |x - y| / (|x| * |y|)
      ≤ (4 * rho) / (|x| * |y|) := h91
    _ ≤ (4 * rho) / ((1 / 2 : ℝ) * (1 / 2 : ℝ)) := h92
    _ = 16 * rho := h11
  exact h12

/--
Tube containment from base/direction closeness.
-/
lemma tube_containment_from_closeness
    {δ R : ℝ} (hδ_nonneg : 0 ≤ δ) (hR_nonneg : 0 ≤ R)
    (T : Kakeya.DeltaTube δ) (G : Kakeya.DeltaTube R)
    (h : ‖T.base - G.base‖ + ‖T.direction - G.direction‖ + δ ≤ R) :
    T.carrier ⊆ G.carrier := by
  have h_compactT : IsCompact (unitSegment T.base T.direction) := by
    apply IsCompact.image isCompact_Icc
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hT_eq : T.carrier = ⋃ y ∈ unitSegment T.base T.direction, Metric.closedBall y δ :=
    h_compactT.cthickening_eq_biUnion_closedBall hδ_nonneg
  intro p hp
  rw [hT_eq] at hp
  rcases Set.mem_iUnion₂.mp hp with ⟨q, hq_seg, hq_ball⟩
  have hq_dist : dist p q ≤ δ := by simpa [Metric.mem_closedBall] using hq_ball
  rcases hq_seg with ⟨t, ht, hq_eq⟩
  have hq_eq' : q = T.base + t • T.direction := hq_eq.symm
  let q' := G.base + t • G.direction
  have hq'_seg : q' ∈ unitSegment G.base G.direction := ⟨t, ht, rfl⟩
  have h_ht0 : 0 ≤ t := ht.1
  have h_ht1 : t ≤ 1 := ht.2
  have h_abs_t : |t| ≤ 1 := by
    rw [abs_of_nonneg h_ht0] <;> linarith
  have h_vec : (T.base + t • T.direction) - (G.base + t • G.direction) =
      (T.base - G.base) + t • (T.direction - G.direction) := by
    have h : (T.base + t • T.direction) - (G.base + t • G.direction) =
        (T.base - G.base) + (t • T.direction - t • G.direction) := by abel
    rw [h]
    have h2 : t • T.direction - t • G.direction = t • (T.direction - G.direction) := by
      rw [←smul_sub]
    rw [h2]
  have h_diff : ‖(T.base + t • T.direction) - q'‖ ≤
      ‖T.base - G.base‖ + ‖T.direction - G.direction‖ := by
    have h_vec2 : (T.base + t • T.direction) - q' = (T.base - G.base) + t • (T.direction - G.direction) := by
      simp [q', h_vec] <;> abel
    rw [h_vec2]
    have h4 : ‖(T.base - G.base) + t • (T.direction - G.direction)‖ ≤
        ‖T.base - G.base‖ + ‖t • (T.direction - G.direction)‖ := norm_add_le _ _
    have h5 : ‖t • (T.direction - G.direction)‖ = |t| * ‖T.direction - G.direction‖ := by
      simpa using norm_smul t (T.direction - G.direction)
    rw [h5] at h4
    have h6 : |t| * ‖T.direction - G.direction‖ ≤ ‖T.direction - G.direction‖ := by
      have h7 : 0 ≤ ‖T.direction - G.direction‖ := by positivity
      have h8 : |t| ≤ 1 := h_abs_t
      nlinarith
    linarith
  have h3 : dist p q' ≤ R := by
    have h7 : dist p q' ≤ dist p q + dist q q' := dist_triangle _ _ _
    have h8 : dist p q ≤ δ := hq_dist
    have h9 : dist q q' ≤ ‖T.base - G.base‖ + ‖T.direction - G.direction‖ := by
      rw [hq_eq']
      simpa [dist_eq_norm] using h_diff
    linarith
  have h4 : p ∈ Metric.closedBall q' R := by
    simpa [Metric.mem_closedBall] using h3
  have h_compactG : IsCompact (unitSegment G.base G.direction) := by
    apply IsCompact.image isCompact_Icc
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hG_eq : G.carrier = ⋃ y ∈ unitSegment G.base G.direction, Metric.closedBall y R :=
    h_compactG.cthickening_eq_biUnion_closedBall hR_nonneg
  rw [hG_eq]
  exact Set.mem_iUnion₂.mpr ⟨q', hq'_seg, h4⟩

/--
If T.carrier ⊆ G.carrier, both have |direction 2| ≥ 1/2, and ‖T.base‖ ≤ 2,
then dist(wz1TubeAxisZeroPoint T, wz1TubeAxisZeroPoint G) ≤ 200 * rho.
-/
lemma diagonal_zero_point_closeness
    {delta rho : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (hrho_nonneg : 0 ≤ rho)
    (T : Kakeya.DeltaTube delta) (G : Kakeya.DeltaTube rho)
    (h_cont : T.carrier ⊆ G.carrier)
    (hT_vert : (1 / 2 : ℝ) ≤ |T.direction 2|)
    (hG_vert : (1 / 2 : ℝ) ≤ |G.direction 2|)
    (hbase_bound : ‖T.base‖ ≤ 2) :
    dist (wz1TubeAxisZeroPoint T) (wz1TubeAxisZeroPoint G) ≤ 200 * rho := by
  let p0T := wz1TubeAxisZeroPoint T
  let p0G := wz1TubeAxisZeroPoint G
  let dT := T.direction
  let dG := G.direction

  have hT2_ne_zero : dT 2 ≠ 0 := by
    intro h4; rw [h4] at hT_vert; simp at hT_vert <;> linarith
  have hG2_ne_zero : dG 2 ≠ 0 := by
    intro h4; rw [h4] at hG_vert; simp at hG_vert <;> linarith

  have hp0T_z : p0T 2 = 0 := wz1TubeAxisZeroPoint_coord_two T hT_vert
  have hp0G_z : p0G 2 = 0 := wz1TubeAxisZeroPoint_coord_two G hG_vert

  have h_base_in_T : T.base ∈ T.carrier := by
    have h2 : T.base ∈ unitSegment T.base T.direction := by
      refine ⟨0, by norm_num, ?_⟩
      simp
    exact Metric.mem_cthickening_of_dist_le T.base T.base delta _ h2 (by simp [hdelta_nonneg])
  have h_base_in_G : T.base ∈ G.carrier := h_cont h_base_in_T

  have h_compact : IsCompact (unitSegment G.base G.direction) := by
    apply IsCompact.image isCompact_Icc
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hU_eq : G.carrier = ⋃ y ∈ unitSegment G.base G.direction, Metric.closedBall y rho :=
    h_compact.cthickening_eq_biUnion_closedBall hrho_nonneg
  rcases Set.mem_iUnion₂.mp (by rw [←hU_eq]; exact h_base_in_G) with ⟨q, hq_seg, hq_ball⟩
  have hq_dist : dist T.base q ≤ rho := by simpa [Metric.mem_closedBall] using hq_ball
  rcases hq_seg with ⟨t, ht, hq_eq⟩
  have hq_eq' : q = G.base + t • dG := hq_eq.symm
  have hq_norm : ‖T.base - q‖ ≤ rho := by simpa [dist_eq_norm] using hq_dist

  rcases direction_closeness_from_containment hdelta_nonneg hrho_nonneg T G h_cont
    with ⟨sign, hsign, hdir⟩

  let t0 : ℝ := T.base 2 / dT 2
  let s : ℝ := q 2 / dG 2
  have hTbase_eq : T.base = p0T + t0 • dT := by
    simp [p0T, wz1TubeAxisZeroPoint, t0] <;> abel
  have hq2_param : q 2 = G.base 2 + t * dG 2 := by
    rw [hq_eq'] <;> simp <;> ring
  have hs_eq : s = G.base 2 / dG 2 + t := by
    simp [s, hq2_param] <;> field_simp [hG2_ne_zero] <;> ring
  have hq_eq2 : q = p0G + s • dG := by
    have h_p0G_def : p0G = G.base - (G.base 2 / dG 2) • dG := by rfl
    rw [h_p0G_def, hs_eq, hq_eq'] <;> simp [add_smul] <;> abel

  have h_t0_bound : |t0| ≤ 4 := by
    have h4 : |t0| = |T.base 2| / |dT 2| := by simp [t0, abs_div] <;> ring
    rw [h4]
    have h5 : |T.base 2| ≤ ‖T.base‖ := point3_component_le_norm T.base 2
    have h7 : |dT 2| ≥ (1 / 2 : ℝ) := hT_vert
    calc |T.base 2| / |dT 2|
      ≤ ‖T.base‖ / |dT 2| := by gcongr
      _ ≤ 2 / (1 / 2 : ℝ) := by gcongr <;> exact hbase_bound
      _ = 4 := by norm_num

  have hq2_diff : |q 2 - T.base 2| ≤ rho := by
    have h : |(q - T.base) 2| ≤ ‖q - T.base‖ := point3_component_le_norm (q - T.base) 2
    have h2 : q 2 - T.base 2 = (q - T.base) 2 := by simp <;> ring
    rw [h2]
    exact h.trans (by rw [norm_sub_rev]; exact hq_norm)

  by_cases hsign1 : sign = 1
  · -- Case sign = 1
    have hdir' : ‖dT - dG‖ ≤ 4 * rho := by
      rw [hsign1] at hdir <;> simpa using hdir
    have hdir2 : |dT 2 - dG 2| ≤ 4 * rho := by
      have h : |(dT - dG) 2| ≤ ‖dT - dG‖ := point3_component_le_norm (dT - dG) 2
      exact h.trans hdir'
    have hdir2' : |dG 2 - dT 2| ≤ 4 * rho := by
      have h : |dG 2 - dT 2| = |dT 2 - dG 2| := by
        have h' : dG 2 - dT 2 = -(dT 2 - dG 2) := by ring
        rw [h', abs_neg]
      rw [h]; exact hdir2
    have h_inv_diff : |(dG 2)⁻¹ - (dT 2)⁻¹| ≤ 16 * rho :=
      abs_inv_diff_bound (x := dG 2) (y := dT 2) hG_vert hT_vert hdir2' hrho_nonneg

    have h61 : |q 2 - T.base 2| ≤ rho := hq2_diff
    have h62 : |(dG 2)⁻¹| ≤ 2 := abs_inv_le_two hG_vert
    have h6 : |(q 2 - T.base 2) * (dG 2)⁻¹| ≤ 2 * rho := by
      rw [abs_mul]
      calc |q 2 - T.base 2| * |(dG 2)⁻¹|
        ≤ rho * |(dG 2)⁻¹| := by exact mul_le_mul_of_nonneg_right h61 (by positivity)
      _ ≤ rho * 2 := by exact mul_le_mul_of_nonneg_left h62 (by positivity)
      _ = 2 * rho := by ring

    have h71 : |T.base 2| ≤ ‖T.base‖ := point3_component_le_norm T.base 2
    have h72 : |T.base 2| ≤ 2 := h71.trans hbase_bound
    have h7 : |T.base 2 * ((dG 2)⁻¹ - (dT 2)⁻¹)| ≤ 2 * (16 * rho) := by
      rw [abs_mul]
      calc |T.base 2| * |(dG 2)⁻¹ - (dT 2)⁻¹|
        ≤ 2 * |(dG 2)⁻¹ - (dT 2)⁻¹| := by exact mul_le_mul_of_nonneg_right h72 (by positivity)
      _ ≤ 2 * (16 * rho) := by exact mul_le_mul_of_nonneg_left h_inv_diff (by positivity)

    have h_s_diff : |s - t0| ≤ 36 * rho := by
      have h_eq : s - t0 = (q 2 - T.base 2) * (dG 2)⁻¹ + T.base 2 * ((dG 2)⁻¹ - (dT 2)⁻¹) := by
        simp [s, t0] <;> field_simp [hG2_ne_zero, hT2_ne_zero] <;> ring
      rw [h_eq]
      have h_tri : |(q 2 - T.base 2) * (dG 2)⁻¹ + T.base 2 * ((dG 2)⁻¹ - (dT 2)⁻¹)| ≤
          |(q 2 - T.base 2) * (dG 2)⁻¹| + |T.base 2 * ((dG 2)⁻¹ - (dT 2)⁻¹)| := by
        exact abs_add_le _ _
      linarith

    have h_main_eq : p0T - p0G = (T.base - q) + (s - t0) • dG + t0 • (dG - dT) := by
      have h1 : p0T = T.base - t0 • dT := by
        have h11 : T.base = p0T + t0 • dT := hTbase_eq
        calc p0T
          = p0T + t0 • dT - t0 • dT := by simp [sub_smul] <;> abel
        _ = T.base - t0 • dT := by rw [h11]
      have h2 : p0G = q - s • dG := by
        have h21 : q = p0G + s • dG := hq_eq2
        calc p0G
          = p0G + s • dG - s • dG := by simp [sub_smul] <;> abel
        _ = q - s • dG := by rw [h21]
      have h3 : p0T - p0G = (T.base - t0 • dT) - (q - s • dG) := by
        rw [h1, h2]
      rw [h3]
      ext i
      fin_cases i <;> simp [sub_smul, add_smul] <;> ring

    have h_ndG : ‖dG - dT‖ ≤ 4 * rho := by
      have h : ‖dG - dT‖ = ‖dT - dG‖ := by
        have h2 : dG - dT = -(dT - dG) := by abel
        rw [h2, norm_neg]
      rw [h]; exact hdir'

    have h_norm1 : ‖(s - t0) • dG‖ = |s - t0| := by
      have h : ‖(s - t0) • dG‖ = ‖s - t0‖ * ‖dG‖ := norm_smul (s - t0) dG
      have h2 : ‖s - t0‖ = |s - t0| := by simp
      rw [h, h2, G.direction_unit] <;> ring
    have h_norm2 : ‖t0 • (dG - dT)‖ = |t0| * ‖dG - dT‖ := by
      have h : ‖t0 • (dG - dT)‖ = ‖t0‖ * ‖dG - dT‖ := norm_smul t0 (dG - dT)
      have h2 : ‖t0‖ = |t0| := by simp
      rw [h, h2]

    have h_bound : ‖(T.base - q) + (s - t0) • dG + t0 • (dG - dT)‖ ≤ 53 * rho := by
      have h2 : ‖((T.base - q) + (s - t0) • dG) + t0 • (dG - dT)‖ ≤
          ‖(T.base - q) + (s - t0) • dG‖ + ‖t0 • (dG - dT)‖ := norm_add_le _ _
      have h3 : ‖(T.base - q) + (s - t0) • dG‖ ≤ ‖T.base - q‖ + ‖(s - t0) • dG‖ := norm_add_le _ _
      have h4 : ‖(T.base - q) + (s - t0) • dG + t0 • (dG - dT)‖ ≤
          ‖T.base - q‖ + ‖(s - t0) • dG‖ + ‖t0 • (dG - dT)‖ := by linarith
      rw [h_norm1, h_norm2] at h4
      have h5 : ‖T.base - q‖ ≤ rho := hq_norm
      have h6 : |s - t0| ≤ 36 * rho := h_s_diff
      have h7 : |t0| ≤ 4 := h_t0_bound
      have h8 : ‖dG - dT‖ ≤ 4 * rho := h_ndG
      have h9 : |t0| * ‖dG - dT‖ ≤ 16 * rho := by
        calc |t0| * ‖dG - dT‖
          ≤ 4 * ‖dG - dT‖ := by exact mul_le_mul_of_nonneg_right h7 (by positivity)
        _ ≤ 4 * (4 * rho) := by exact mul_le_mul_of_nonneg_left h8 (by positivity)
        _ = 16 * rho := by ring
      linarith

    have h_final : ‖p0T - p0G‖ ≤ 53 * rho := by
      have h9 : p0T - p0G = (T.base - q) + (s - t0) • dG + t0 • (dG - dT) := h_main_eq
      rw [h9]
      exact h_bound

    have h9 : ‖p0T - p0G‖ ≤ 200 * rho := by
      have h10 : ‖p0T - p0G‖ ≤ 53 * rho := h_final
      have h11 : 0 ≤ rho := hrho_nonneg
      linarith
    simpa [dist_eq_norm] using h9

  · -- Case sign = -1
    have hsign_neg : sign = -1 := by rcases hsign with (rfl | rfl) <;> tauto
    have hdir' : ‖dT + dG‖ ≤ 4 * rho := by
      rw [hsign_neg] at hdir <;> simpa using hdir
    have hdir2 : |dT 2 + dG 2| ≤ 4 * rho := by
      have h : |(dT + dG) 2| ≤ ‖dT + dG‖ := point3_component_le_norm (dT + dG) 2
      exact h.trans hdir'

    have h_denom : (1 / 2 : ℝ) * (1 / 2 : ℝ) ≤ |dT 2| * |dG 2| := by
      have h5 : (1 / 2 : ℝ) ≤ |dT 2| := hT_vert
      have h6 : (1 / 2 : ℝ) ≤ |dG 2| := hG_vert
      have h7 : 0 ≤ |dT 2| := by positivity
      have h8 : 0 ≤ |dG 2| := by positivity
      nlinarith
    have h_pos_denom : 0 ≤ |dT 2| * |dG 2| := by positivity
    have h_inv_sum : |(dT 2)⁻¹ + (dG 2)⁻¹| ≤ 16 * rho := by
      have h1 : (dT 2)⁻¹ + (dG 2)⁻¹ = (dT 2 + dG 2) / ((dT 2) * (dG 2)) := by
        field_simp [hT2_ne_zero, hG2_ne_zero] <;> ring
      have h_main : |(dT 2)⁻¹ + (dG 2)⁻¹| = |dT 2 + dG 2| / (|dT 2| * |dG 2|) := by
        rw [h1, abs_div, abs_mul]
      rw [h_main]
      have h_pos4 : 0 ≤ 4 * rho := by positivity
      have h91 : |dT 2 + dG 2| / (|dT 2| * |dG 2|) ≤ (4 * rho) / (|dT 2| * |dG 2|) := by
        apply div_le_div_of_nonneg_right hdir2 (by positivity)
      have h92 : (4 * rho) / (|dT 2| * |dG 2|) ≤ (4 * rho) / ((1 / 2 : ℝ) * (1 / 2 : ℝ)) := by
        apply div_le_div_of_nonneg_left h_pos4 (by norm_num) h_denom
      have h10 : (1 / 2 : ℝ) * (1 / 2 : ℝ) = 1 / 4 := by norm_num
      have h11 : (4 * rho) / ((1 / 2 : ℝ) * (1 / 2 : ℝ)) = 16 * rho := by
        rw [h10] <;> field_simp <;> ring
      calc |dT 2 + dG 2| / (|dT 2| * |dG 2|)
        ≤ (4 * rho) / (|dT 2| * |dG 2|) := h91
      _ ≤ (4 * rho) / ((1 / 2 : ℝ) * (1 / 2 : ℝ)) := h92
      _ = 16 * rho := h11

    have h61 : |q 2 - T.base 2| ≤ rho := hq2_diff
    have h62 : |(dG 2)⁻¹| ≤ 2 := abs_inv_le_two hG_vert
    have h6 : |(q 2 - T.base 2) * (dG 2)⁻¹| ≤ 2 * rho := by
      rw [abs_mul]
      calc |q 2 - T.base 2| * |(dG 2)⁻¹|
        ≤ rho * |(dG 2)⁻¹| := by exact mul_le_mul_of_nonneg_right h61 (by positivity)
      _ ≤ rho * 2 := by exact mul_le_mul_of_nonneg_left h62 (by positivity)
      _ = 2 * rho := by ring

    have h71 : |T.base 2| ≤ ‖T.base‖ := point3_component_le_norm T.base 2
    have h72 : |T.base 2| ≤ 2 := h71.trans hbase_bound
    have h7 : |T.base 2 * ((dT 2)⁻¹ + (dG 2)⁻¹)| ≤ 2 * (16 * rho) := by
      rw [abs_mul]
      calc |T.base 2| * |(dT 2)⁻¹ + (dG 2)⁻¹|
        ≤ 2 * |(dT 2)⁻¹ + (dG 2)⁻¹| := by exact mul_le_mul_of_nonneg_right h72 (by positivity)
      _ ≤ 2 * (16 * rho) := by exact mul_le_mul_of_nonneg_left h_inv_sum (by positivity)

    have h_sum : |s + t0| ≤ 36 * rho := by
      have h_eq : s + t0 = (q 2 - T.base 2) * (dG 2)⁻¹ + T.base 2 * ((dT 2)⁻¹ + (dG 2)⁻¹) := by
        simp [s, t0] <;> field_simp [hG2_ne_zero, hT2_ne_zero] <;> ring
      rw [h_eq]
      have h_tri : |(q 2 - T.base 2) * (dG 2)⁻¹ + T.base 2 * ((dT 2)⁻¹ + (dG 2)⁻¹)| ≤
          |(q 2 - T.base 2) * (dG 2)⁻¹| + |T.base 2 * ((dT 2)⁻¹ + (dG 2)⁻¹)| := by
        exact abs_add_le _ _
      linarith

    have h_main_eq : p0T - p0G = (T.base - q) - t0 • (dT + dG) + (s + t0) • dG := by
      have h1 : p0T = T.base - t0 • dT := by
        have h11 : T.base = p0T + t0 • dT := hTbase_eq
        calc p0T
          = p0T + t0 • dT - t0 • dT := by simp [sub_smul] <;> abel
        _ = T.base - t0 • dT := by rw [h11]
      have h2 : p0G = q - s • dG := by
        have h21 : q = p0G + s • dG := hq_eq2
        calc p0G
          = p0G + s • dG - s • dG := by simp [sub_smul] <;> abel
        _ = q - s • dG := by rw [h21]
      have h3 : p0T - p0G = (T.base - t0 • dT) - (q - s • dG) := by
        rw [h1, h2]
      rw [h3]
      ext i
      fin_cases i <;> simp [sub_smul, add_smul] <;> ring

    have h_norm1 : ‖t0 • (dT + dG)‖ = |t0| * ‖dT + dG‖ := by
      have h : ‖t0 • (dT + dG)‖ = ‖t0‖ * ‖dT + dG‖ := norm_smul t0 (dT + dG)
      have h2 : ‖t0‖ = |t0| := by simp
      rw [h, h2]
    have h_norm2 : ‖(s + t0) • dG‖ = |s + t0| := by
      have h : ‖(s + t0) • dG‖ = ‖s + t0‖ * ‖dG‖ := norm_smul (s + t0) dG
      have h2 : ‖s + t0‖ = |s + t0| := by simp
      rw [h, h2, G.direction_unit] <;> ring

    have h_bound : ‖(T.base - q) - t0 • (dT + dG) + (s + t0) • dG‖ ≤ 53 * rho := by
      have h2 : ‖((T.base - q) - t0 • (dT + dG)) + (s + t0) • dG‖ ≤
          ‖(T.base - q) - t0 • (dT + dG)‖ + ‖(s + t0) • dG‖ := norm_add_le _ _
      have h3 : ‖(T.base - q) - t0 • (dT + dG)‖ ≤ ‖T.base - q‖ + ‖t0 • (dT + dG)‖ := by
        exact norm_sub_le (T.base - q) (t0 • (dT + dG))
      have h5 : ‖(T.base - q) - t0 • (dT + dG) + (s + t0) • dG‖ ≤
          ‖T.base - q‖ + ‖t0 • (dT + dG)‖ + ‖(s + t0) • dG‖ := by linarith
      rw [h_norm1, h_norm2] at h5
      have h6 : ‖T.base - q‖ ≤ rho := hq_norm
      have h7 : |t0| ≤ 4 := h_t0_bound
      have h8 : ‖dT + dG‖ ≤ 4 * rho := hdir'
      have h9 : |s + t0| ≤ 36 * rho := h_sum
      have h10 : |t0| * ‖dT + dG‖ ≤ 16 * rho := by
        calc |t0| * ‖dT + dG‖
          ≤ 4 * ‖dT + dG‖ := by exact mul_le_mul_of_nonneg_right h7 (by positivity)
        _ ≤ 4 * (4 * rho) := by exact mul_le_mul_of_nonneg_left h8 (by positivity)
        _ = 16 * rho := by ring
      linarith

    have h_final : ‖p0T - p0G‖ ≤ 53 * rho := by
      have h10 : p0T - p0G = (T.base - q) - t0 • (dT + dG) + (s + t0) • dG := h_main_eq
      rw [h10]
      exact h_bound

    have h9 : ‖p0T - p0G‖ ≤ 200 * rho := by
      have h10 : ‖p0T - p0G‖ ≤ 53 * rho := h_final
      have h11 : 0 ≤ rho := hrho_nonneg
      linarith
    simpa [dist_eq_norm] using h9

end Kakeya.Assouad

end
