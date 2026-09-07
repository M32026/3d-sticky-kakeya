import MyLeanRepo.Kakeya.Assouad.WZ1.GlobalPlaninessTransportStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.SlopeConstructionHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.UnitRescaling
import MyLeanRepo.Kakeya.Assouad.WZ1.AnchoredNormalLinearContraction
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Discrete-grid slope construction via McShane extension

Construct a global Lipschitz slope function by:
1. Parameterizing the distinguished tube centerline by height
2. Evaluating the source plane map along the centerline
3. Transporting normals via inverse-transpose
4. Proving Lipschitz on the active height interval
5. Extending to all of ℝ via McShane
6. Clipping to [-3, 3]

Key lemmas:
- `tubeCenterline_lipschitz`: centerline is Lipschitz in z
- `transportedNormal_lipschitz`: composition of planeMap + transport + normalization
- `discreteSlope_lipschitz`: ratio Lipschitz on the active set
- `globalSlope_lipschitz`: McShane extension preserves Lipschitz
- `globalSlope_bound`: clipping preserves bound
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

variable {δ : ℝ}

/-- Centerline point of tube T at height z. -/
def centerlineAtHeight (T : Kakeya.DeltaTube δ) (z : ℝ) : Point3 :=
  T.base + ((z - T.base 2) / T.direction 2) • T.direction

lemma centerlineAtHeight_height (T : Kakeya.DeltaTube δ) (z : ℝ) (hd2 : T.direction 2 ≠ 0) :
    (centerlineAtHeight T z) 2 = z := by
  have h : (centerlineAtHeight T z) 2 = T.base 2 + ((z - T.base 2) / T.direction 2) * T.direction 2 := by
    simp [centerlineAtHeight]
    <;> rfl
  rw [h]
  have h2 : ((z - T.base 2) / T.direction 2) * T.direction 2 = z - T.base 2 := by
    field_simp [hd2] <;> ring
  rw [h2] <;> ring

/-- Centerline parameterization is Lipschitz with constant 1/|d2|. -/
lemma centerlineAtHeight_lipschitz (T : Kakeya.DeltaTube δ) (hd2 : T.direction 2 ≠ 0) :
    ∀ z1 z2 : ℝ, dist (centerlineAtHeight T z1) (centerlineAtHeight T z2) ≤
      (1 / |T.direction 2|) * |z1 - z2| := by
  intro z1 z2
  have h : centerlineAtHeight T z1 - centerlineAtHeight T z2 =
      ((z1 - z2) / T.direction 2) • T.direction := by
    have h1 : centerlineAtHeight T z1 = T.base + ((z1 - T.base 2) / T.direction 2) • T.direction := by
      rfl
    have h2 : centerlineAtHeight T z2 = T.base + ((z2 - T.base 2) / T.direction 2) • T.direction := by
      rfl
    rw [h1, h2]
    have h3 : (T.base + ((z1 - T.base 2) / T.direction 2) • T.direction) -
        (T.base + ((z2 - T.base 2) / T.direction 2) • T.direction) =
        (((z1 - T.base 2) / T.direction 2) - ((z2 - T.base 2) / T.direction 2)) • T.direction := by
      have h4 : (T.base + ((z1 - T.base 2) / T.direction 2) • T.direction) -
          (T.base + ((z2 - T.base 2) / T.direction 2) • T.direction) =
          ((z1 - T.base 2) / T.direction 2) • T.direction - ((z2 - T.base 2) / T.direction 2) • T.direction := by
        simp [add_assoc]
        <;> abel
      rw [h4]
      rw [←sub_smul]
    rw [h3]
    have h4 : ((z1 - T.base 2) / T.direction 2) - ((z2 - T.base 2) / T.direction 2) =
        (z1 - z2) / T.direction 2 := by ring
    rw [h4]
  have h_dist : dist (centerlineAtHeight T z1) (centerlineAtHeight T z2) =
      ‖centerlineAtHeight T z1 - centerlineAtHeight T z2‖ := by rfl
  rw [h_dist, h]
  have h2 : ‖((z1 - z2) / T.direction 2) • T.direction‖ =
      |(z1 - z2) / T.direction 2| * ‖T.direction‖ := by
    rw [norm_smul]
    <;> rfl
  rw [h2, T.direction_unit]
  have h3 : |(z1 - z2) / T.direction 2| = |z1 - z2| / |T.direction 2| := by
    rw [abs_div]
  rw [h3]
  have h4 : (|z1 - z2| / |T.direction 2|) * (1 : ℝ) =
      (1 / |T.direction 2|) * |z1 - z2| := by ring
  rw [h4]

/--
Transported normal at a point.
-/
def transportedNormal (T : Kakeya.DeltaTube δ) (rho : ℝ) (hrho : 0 < rho)
    (planeMap : Point3 → Point3) (p : Point3) : Point3 :=
  let Nv := wz1AnchoredUnitRescalingNormalLinear T rho (planeMap p)
  (1 / ‖Nv‖) • Nv

/--
Slope at a point using the transported normal.
For chart.first: n1/n0. For chart.second: n0/n1.
-/
def slopeAtNormal (chart : WZ1HorizontalChart) (n : Point3) : ℝ :=
  match chart with
  | WZ1HorizontalChart.first => n 1 / n 0
  | WZ1HorizontalChart.second => n 0 / n 1

/--
Slope along the tube centerline at height z.
-/
def slopeAlongCenterline (T : Kakeya.DeltaTube δ) (rho : ℝ) (hrho : 0 < rho)
    (planeMap : Point3 → Point3) (chart : WZ1HorizontalChart) (z : ℝ) : ℝ :=
  slopeAtNormal chart (transportedNormal T rho hrho planeMap (centerlineAtHeight T z))

/-- Helper to get the chart component index. -/
def chartIndex (chart : WZ1HorizontalChart) : Fin 3 :=
  match chart with
  | WZ1HorizontalChart.first => 0
  | WZ1HorizontalChart.second => 1

/-- Normalization map is `2/r`-Lipschitz on vectors of norm at least `r`. -/
lemma normalize_lipschitz_bound {r : ℝ} (hr : 0 < r)
    {x y : Point3} (hx : r ≤ ‖x‖) (hy : r ≤ ‖y‖) :
    dist ((1 / ‖x‖) • x) ((1 / ‖y‖) • y) ≤ (2 / r) * dist x y := by
  set nx := (1 / ‖x‖) • x with hnx
  set ny := (1 / ‖y‖) • y with hny
  have hx_pos : 0 < ‖x‖ := by linarith
  have hy_pos : 0 < ‖y‖ := by linarith
  have h_abs_diff : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by
    have h1 : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
      calc ‖y‖ = ‖x + (y - x)‖ := by abel
        _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
    have h2 : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
      calc ‖x‖ = ‖y + (x - y)‖ := by abel
        _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
    have h3 : ‖y - x‖ = ‖x - y‖ := norm_sub_rev _ _
    rw [h3] at h1
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have h_main : ‖nx - ny‖ ≤ (2 / ‖x‖) * ‖x - y‖ := by
    have h4 : nx - ny = (1 / (‖x‖ * ‖y‖)) • (‖y‖ • x - ‖x‖ • y) := by
      apply PiLp.ext
      intro i
      simp [hnx, hny, smul_sub, sub_smul]
      <;> field_simp [hx_pos.ne', hy_pos.ne'] <;> ring
    rw [h4]
    have h5 : ‖(1 / (‖x‖ * ‖y‖)) • (‖y‖ • x - ‖x‖ • y)‖ =
        (1 / (‖x‖ * ‖y‖)) * ‖‖y‖ • x - ‖x‖ • y‖ := by
      rw [norm_smul]
      have h51 : ‖(1 / (‖x‖ * ‖y‖) : ℝ)‖ = 1 / (‖x‖ * ‖y‖) := by
        rw [Real.norm_eq_abs, abs_of_pos] <;> positivity
      rw [h51]
    rw [h5]
    have h6 : ‖‖y‖ • x - ‖x‖ • y‖ ≤ 2 * ‖y‖ * ‖x - y‖ := by
      have h61 : ‖y‖ • x - ‖x‖ • y = ‖y‖ • (x - y) + (‖y‖ - ‖x‖) • y := by
        simp [smul_sub, sub_smul] <;> abel
      rw [h61]
      have h62 : ‖‖y‖ • (x - y) + (‖y‖ - ‖x‖) • y‖ ≤
          ‖‖y‖ • (x - y)‖ + ‖(‖y‖ - ‖x‖) • y‖ := norm_add_le _ _
      have h63 : ‖‖y‖ • (x - y)‖ = ‖y‖ * ‖x - y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg] <;> positivity
      have h64 : ‖(‖y‖ - ‖x‖) • y‖ = |‖y‖ - ‖x‖| * ‖y‖ := by
        rw [norm_smul, Real.norm_eq_abs] <;> rfl
      calc
        ‖‖y‖ • (x - y) + (‖y‖ - ‖x‖) • y‖
          ≤ ‖y‖ * ‖x - y‖ + |‖y‖ - ‖x‖| * ‖y‖ := by
            rw [h63, h64] at h62; exact h62
        _ ≤ ‖y‖ * ‖x - y‖ + ‖x - y‖ * ‖y‖ := by
          gcongr
          <;> exact h_abs_diff
        _ = 2 * ‖y‖ * ‖x - y‖ := by ring
    have h7 : (1 / (‖x‖ * ‖y‖)) * ‖‖y‖ • x - ‖x‖ • y‖ ≤
        (1 / (‖x‖ * ‖y‖)) * (2 * ‖y‖ * ‖x - y‖) := by
      gcongr
    have h8 : (1 / (‖x‖ * ‖y‖)) * (2 * ‖y‖ * ‖x - y‖) =
        (2 / ‖x‖) * ‖x - y‖ := by
      field_simp [hx_pos.ne', hy_pos.ne'] <;> ring
    rw [h8] at h7
    exact h7
  have h9 : (2 / ‖x‖) * ‖x - y‖ ≤ (2 / r) * ‖x - y‖ := by
    gcongr <;> linarith
  have h10 : ‖nx - ny‖ ≤ (2 / r) * ‖x - y‖ := by
    calc ‖nx - ny‖ ≤ (2 / ‖x‖) * ‖x - y‖ := h_main
      _ ≤ (2 / r) * ‖x - y‖ := h9
  simpa [dist_eq_norm] using h10

/-- Norm squared formula for Point3. -/
private lemma point3_norm_sq (p : Point3) :
    ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 := by
  have h1 : ‖p‖ ^ 2 = inner ℝ p p := by rw [← real_inner_self_eq_norm_sq]
  rw [h1]
  have h2 : inner ℝ p p = ∑ i : Fin 3, p i ^ 2 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct] <;> simp [pow_two] <;> rfl
  rw [h2]
  simp [Fin.sum_univ_succ] <;> ring


/--
Lipschitz bound for slopeAlongCenterline on a set s.

Assumptions:
- Centerline points for z ∈ s are in the shading
- |d2| ≥ d2_min > 0
- Plane map Lipschitz with constant L
- Transported normal norm ≥ rho (for normalization Lipschitz)
- Selected chart component ≥ c > 0
- Both components ≤ 1

The Lipschitz constant is:
  K = (1/d2_min) * L * 1 * (2/rho) * (2/c^2) = 4 * L / (d2_min * rho * c^2)

TODO: prove the composition carefully. The main steps are:
1. z ↦ p(z): Lipschitz with 1/d2_min
2. p ↦ planeMap(p): Lipschitz with L (on shading)
3. v ↦ Nv: linear with norm ≤ 1
4. Nv ↦ n = Nv/‖Nv‖: Lipschitz with 2/rho (when ‖Nv‖ ≥ rho)
5. n ↦ n1/n0: Lipschitz with 2/c² (when |n0| ≥ c, |n0|≤1, |n1|≤1)
-/
lemma slopeAlongCenterline_lipschitz
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (T : Kakeya.DeltaTube δ) (rho : ℝ) (hrho : 0 < rho)
    (h_rho_small : 100 * rho ≤ 1)
    (planeMap : Point3 → Point3)
    (Y : Kakeya.Streamlined.TubeShading F)
    (L : NNReal)
    (hL : LipschitzOnWith L planeMap Y.union)
    (chart : WZ1HorizontalChart)
    (s : Set ℝ)
    (h_in_shading : ∀ z ∈ s, centerlineAtHeight T z ∈ Y.union)
    (d2_min : ℝ) (hd2_min : 0 < d2_min)
    (hd2 : d2_min ≤ |T.direction 2|)
    (c : ℝ) (hc_pos : 0 < c)
    (hNv_lower : ∀ z ∈ s,
      rho ≤ ‖wz1AnchoredUnitRescalingNormalLinear T rho (planeMap (centerlineAtHeight T z))‖)
    (hn_chart : ∀ z ∈ s,
      c ≤ |(transportedNormal T rho hrho planeMap (centerlineAtHeight T z)) (chartIndex chart)|)
    (hn_upper0 : ∀ z ∈ s,
      |(transportedNormal T rho hrho planeMap (centerlineAtHeight T z)) 0| ≤ 1)
    (hn_upper1 : ∀ z ∈ s,
      |(transportedNormal T rho hrho planeMap (centerlineAtHeight T z)) 1| ≤ 1) :
    ∃ (K : NNReal), LipschitzOnWith K (slopeAlongCenterline T rho hrho planeMap chart) s := by
  have hd2_ne_zero : T.direction 2 ≠ 0 := by
    have h : 0 < |T.direction 2| := by linarith
    exact abs_ne_zero.mp h.ne'
  let p : ℝ → Point3 := centerlineAtHeight T
  let v : ℝ → Point3 := fun z => planeMap (p z)
  let Nv : ℝ → Point3 := fun z => wz1AnchoredUnitRescalingNormalLinear T rho (v z)
  let n : ℝ → Point3 := fun z => transportedNormal T rho hrho planeMap (p z)
  have h_n_def : ∀ z, n z = (1 / ‖Nv z‖) • Nv z := by
    intro z
    dsimp only [n, transportedNormal]
    <;> rfl
  set L_n : ℝ := (2 / rho) * (L : ℝ) * (1 / d2_min) with hL_n_def
  have hL_n_nonneg : 0 ≤ L_n := by positivity
  have h_cent : ∀ z1 z2 : ℝ, dist (p z1) (p z2) ≤ (1 / |T.direction 2|) * |z1 - z2| :=
    centerlineAtHeight_lipschitz T hd2_ne_zero
  have h_cent2 : ∀ z1 z2 : ℝ, dist (p z1) (p z2) ≤ (1 / d2_min) * |z1 - z2| := by
    intro z1 z2
    have h1 : (1 / |T.direction 2|) ≤ (1 / d2_min) := by
      apply one_div_le_one_div_of_le
      <;> linarith
    calc
      dist (p z1) (p z2) ≤ (1 / |T.direction 2|) * |z1 - z2| := h_cent z1 z2
      _ ≤ (1 / d2_min) * |z1 - z2| := by gcongr
  have h_lin_contract : ∀ (x y : Point3),
      dist (wz1AnchoredUnitRescalingNormalLinear T rho x)
           (wz1AnchoredUnitRescalingNormalLinear T rho y) ≤ dist x y := by
    intro x y
    let f := wz1AnchoredUnitRescalingNormalLinear T rho
    have h1 : f x - f y = f (x - y) := by
      exact (map_sub f x y).symm
    have h2 : ‖f (x - y)‖ ≤ ‖x - y‖ :=
      anchoredNormalLinear_contraction T rho hrho h_rho_small (x - y)
    have h3 : dist (f x) (f y) = ‖f x - f y‖ := by rfl
    rw [h3, h1]
    exact h2
  have h_n_lipschitz : ∀ z1 ∈ s, ∀ z2 ∈ s, dist (n z1) (n z2) ≤ L_n * |z1 - z2| := by
    intro z1 hz1 z2 hz2
    have hp1 : p z1 ∈ Y.union := h_in_shading z1 hz1
    have hp2 : p z2 ∈ Y.union := h_in_shading z2 hz2
    have hL' := lipschitzOnWith_iff_dist_le_mul.mp hL
    have h1 : dist (v z1) (v z2) ≤ (L : ℝ) * dist (p z1) (p z2) :=
      hL' (p z1) hp1 (p z2) hp2
    have h2 : dist (Nv z1) (Nv z2) ≤ dist (v z1) (v z2) := h_lin_contract (v z1) (v z2)
    have hNv1 : rho ≤ ‖Nv z1‖ := hNv_lower z1 hz1
    have hNv2 : rho ≤ ‖Nv z2‖ := hNv_lower z2 hz2
    have h3 : dist (n z1) (n z2) ≤ (2 / rho) * dist (Nv z1) (Nv z2) :=
      normalize_lipschitz_bound hrho hNv1 hNv2
    have h4 : dist (p z1) (p z2) ≤ (1 / d2_min) * |z1 - z2| := h_cent2 z1 z2
    calc
      dist (n z1) (n z2)
        ≤ (2 / rho) * dist (Nv z1) (Nv z2) := h3
      _ ≤ (2 / rho) * dist (v z1) (v z2) := by gcongr
      _ ≤ (2 / rho) * ((L : ℝ) * dist (p z1) (p z2)) := by gcongr
      _ ≤ (2 / rho) * ((L : ℝ) * ((1 / d2_min) * |z1 - z2|)) := by gcongr
      _ = L_n * |z1 - z2| := by
        simp [hL_n_def] <;> ring
  set K_real : ℝ := 2 * L_n / c ^ 2 with hK_real_def
  have hK_real_nonneg : 0 ≤ K_real := by positivity
  match chart with
  | WZ1HorizontalChart.first =>
    have hn0 : ∀ t ∈ s, c ≤ |n t 0| := by
      intro t ht
      simpa [chartIndex] using hn_chart t ht
    have h_slope_lipschitz : ∀ t ∈ s, ∀ u ∈ s,
        |n t 1 / n t 0 - n u 1 / n u 0| ≤ K_real * |t - u| := by
      intro t ht u hu
      have h := ratio_lipschitz_on_real hL_n_nonneg h_n_lipschitz hc_pos hn0 hn_upper0 hn_upper1 t ht u hu
      simpa [hK_real_def] using h
    let K : NNReal := ⟨K_real, hK_real_nonneg⟩
    have h_final : LipschitzOnWith K (slopeAlongCenterline T rho hrho planeMap WZ1HorizontalChart.first) s := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro t ht u hu
      have h_eq_t : slopeAlongCenterline T rho hrho planeMap WZ1HorizontalChart.first t = n t 1 / n t 0 := by rfl
      have h_eq_u : slopeAlongCenterline T rho hrho planeMap WZ1HorizontalChart.first u = n u 1 / n u 0 := by rfl
      rw [h_eq_t, h_eq_u]
      have h := h_slope_lipschitz t ht u hu
      have h_dist1 : dist (n t 1 / n t 0) (n u 1 / n u 0) =
          |n t 1 / n t 0 - n u 1 / n u 0| := by rw [Real.dist_eq]
      have h_dist2 : dist t u = |t - u| := by rw [Real.dist_eq]
      rw [h_dist1, h_dist2]
      exact h
    exact ⟨K, h_final⟩
  | WZ1HorizontalChart.second =>
    let n' : ℝ → Point3 := fun z => point3 (n z 1) (n z 0) (n z 2)
    have h_swap_dist : ∀ z1 z2 : ℝ, dist (n' z1) (n' z2) = dist (n z1) (n z2) := by
      intro z1 z2
      have h_perm : ∀ (a b : Point3),
          dist (point3 (a 1) (a 0) (a 2)) (point3 (b 1) (b 0) (b 2)) = dist a b := by
        intro a b
        have h_sub : point3 (a 1) (a 0) (a 2) - point3 (b 1) (b 0) (b 2) =
            point3 (a 1 - b 1) (a 0 - b 0) (a 2 - b 2) := by
          simp [point3, sub_smul] <;> abel
        have h_norm : ‖point3 (a 1 - b 1) (a 0 - b 0) (a 2 - b 2)‖ = ‖a - b‖ := by
          set q := point3 (a 1 - b 1) (a 0 - b 0) (a 2 - b 2) with hq_def
          have hq0 : q 0 = a 1 - b 1 := by
            simp [hq_def, point3, EuclideanSpace.single_apply] <;> ring
          have hq1 : q 1 = a 0 - b 0 := by
            simp [hq_def, point3, EuclideanSpace.single_apply] <;> ring
          have hq2 : q 2 = a 2 - b 2 := by
            simp [hq_def, point3, EuclideanSpace.single_apply] <;> ring
          have h1 : ‖q‖ ^ 2 = q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 := point3_norm_sq q
          have h2 : ‖a - b‖ ^ 2 = (a - b) 0 ^ 2 + (a - b) 1 ^ 2 + (a - b) 2 ^ 2 := point3_norm_sq (a - b)
          have h3 : q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 = (a - b) 0 ^ 2 + (a - b) 1 ^ 2 + (a - b) 2 ^ 2 := by
            rw [hq0, hq1, hq2]
            <;> simp [Fin.sum_univ_succ] <;> ring
          have h4 : ‖q‖ ^ 2 = ‖a - b‖ ^ 2 := by
            calc ‖q‖ ^ 2 = q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 := h1
              _ = (a - b) 0 ^ 2 + (a - b) 1 ^ 2 + (a - b) 2 ^ 2 := h3
              _ = ‖a - b‖ ^ 2 := h2.symm
          have h5 : 0 ≤ ‖q‖ := by positivity
          have h6 : 0 ≤ ‖a - b‖ := by positivity
          nlinarith
        have h : dist (point3 (a 1) (a 0) (a 2)) (point3 (b 1) (b 0) (b 2)) =
            ‖point3 (a 1) (a 0) (a 2) - point3 (b 1) (b 0) (b 2)‖ := by rfl
        rw [h, h_sub, h_norm]
        <;> rfl
      exact h_perm (n z1) (n z2)
    have h_n'_lipschitz : ∀ t ∈ s, ∀ u ∈ s, dist (n' t) (n' u) ≤ L_n * |t - u| := by
      intro t ht u hu
      rw [h_swap_dist t u]
      exact h_n_lipschitz t ht u hu
    have hn'0 : ∀ t ∈ s, c ≤ |n' t 0| := by
      intro t ht
      have h : n' t 0 = n t 1 := by simp [n', point3]
      rw [h]
      simpa [chartIndex] using hn_chart t ht
    have hn'0_bound : ∀ t ∈ s, |n' t 0| ≤ 1 := by
      intro t ht
      have h : n' t 0 = n t 1 := by simp [n', point3]
      rw [h]
      exact hn_upper1 t ht
    have hn'1 : ∀ t ∈ s, |n' t 1| ≤ 1 := by
      intro t ht
      have h : n' t 1 = n t 0 := by simp [n', point3]
      rw [h]
      exact hn_upper0 t ht
    have h_slope_lipschitz : ∀ t ∈ s, ∀ u ∈ s,
        |n' t 1 / n' t 0 - n' u 1 / n' u 0| ≤ K_real * |t - u| := by
      intro t ht u hu
      have h := ratio_lipschitz_on_real hL_n_nonneg h_n'_lipschitz hc_pos hn'0 hn'0_bound hn'1 t ht u hu
      simpa [hK_real_def] using h
    let K : NNReal := ⟨K_real, hK_real_nonneg⟩
    have h_final : LipschitzOnWith K (slopeAlongCenterline T rho hrho planeMap WZ1HorizontalChart.second) s := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      intro t ht u hu
      have h_eq_t : slopeAlongCenterline T rho hrho planeMap WZ1HorizontalChart.second t = n t 0 / n t 1 := by rfl
      have h_eq_u : slopeAlongCenterline T rho hrho planeMap WZ1HorizontalChart.second u = n u 0 / n u 1 := by rfl
      have h_eq1 : n' t 1 / n' t 0 = n t 0 / n t 1 := by
        simp [n', point3] <;> ring
      have h_eq2 : n' u 1 / n' u 0 = n u 0 / n u 1 := by
        simp [n', point3] <;> ring
      rw [h_eq_t, h_eq_u, ←h_eq1, ←h_eq2]
      have h := h_slope_lipschitz t ht u hu
      have h_dist1 : dist (n' t 1 / n' t 0) (n' u 1 / n' u 0) =
          |n' t 1 / n' t 0 - n' u 1 / n' u 0| := by rw [Real.dist_eq]
      have h_dist2 : dist t u = |t - u| := by rw [Real.dist_eq]
      rw [h_dist1, h_dist2]
      exact h
    exact ⟨K, h_final⟩

/--
Slope bound: |slope| ≤ 3 when ‖n‖ = 1 and chart component ≥ 1/2.
-/
lemma slopeAlongCenterline_bound
    (T : Kakeya.DeltaTube δ) (rho : ℝ) (hrho : 0 < rho)
    (planeMap : Point3 → Point3)
    (chart : WZ1HorizontalChart)
    (z : ℝ)
    (hnorm : ‖transportedNormal T rho hrho planeMap (centerlineAtHeight T z)‖ = 1)
    (hn0_half :
      match chart with
      | WZ1HorizontalChart.first => 1 / 2 ≤ |(transportedNormal T rho hrho planeMap (centerlineAtHeight T z)) 0|
      | WZ1HorizontalChart.second => 1 / 2 ≤ |(transportedNormal T rho hrho planeMap (centerlineAtHeight T z)) 1|) :
    |slopeAlongCenterline T rho hrho planeMap chart z| ≤ 3 := by
  let n := transportedNormal T rho hrho planeMap (centerlineAtHeight T z)
  have hnorm' : ‖n‖ = 1 := hnorm
  cases chart with
  | first =>
    have hn0 : 1 / 2 ≤ |n 0| := hn0_half
    exact slope_bound_from_normal n hnorm' hn0
  | second =>
    have hn1 : 1 / 2 ≤ |n 1| := hn0_half
    have hn0 : |n 0| ≤ 1 := by
      let e0 : Point3 := EuclideanSpace.single 0 (1 : ℝ)
      have hinner : inner ℝ n e0 = n 0 := by
        rw [EuclideanSpace.inner_single_right] <;> simp
      have hbound : |inner ℝ n e0| ≤ ‖n‖ * ‖e0‖ := abs_real_inner_le_norm n e0
      have he0 : ‖e0‖ = 1 := by rw [PiLp.norm_single] <;> norm_num
      rw [hinner, he0, hnorm'] at hbound
      simpa using hbound
    calc
      |n 0 / n 1| = |n 0| / |n 1| := by rw [abs_div]
      _ ≤ 1 / |n 1| := by gcongr
      _ ≤ 1 / (1 / 2 : ℝ) := by gcongr
      _ = 2 := by norm_num
      _ ≤ 3 := by norm_num

/--
Construct global slope by McShane extension and clipping.

Given a slope function f that is Lipschitz on a set s and bounded by 3 on s,
extend to all of ℝ and clip to [-3, 3].
-/
def extendAndClip (f : ℝ → ℝ) (s : Set ℝ) (K : NNReal)
    (hK : LipschitzOnWith K f s) : ℝ → ℝ :=
  let g : ℝ → ℝ := Classical.choose hK.extend_real
  fun z => max (min (g z) 3) (-3)

/-- The extended and clipped slope is Lipschitz with constant K. -/
lemma extendAndClip_lipschitz (f : ℝ → ℝ) (s : Set ℝ) (K : NNReal)
    (hK : LipschitzOnWith K f s) :
    LipschitzWith K (extendAndClip f s K hK) := by
  let g : ℝ → ℝ := Classical.choose hK.extend_real
  have hg : LipschitzWith K g := (Classical.choose_spec hK.extend_real).1
  have hconst3 : LipschitzWith K (fun (_ : ℝ) => (3 : ℝ)) := by
    intro x y
    simp [Real.dist_eq]
    <;> exact NNReal.coe_nonneg K
  have hconst_neg3 : LipschitzWith K (fun (_ : ℝ) => (-3 : ℝ)) := by
    intro x y
    simp [Real.dist_eq]
    <;> exact NNReal.coe_nonneg K
  have h1 : LipschitzWith K (fun z : ℝ => min (g z) (3 : ℝ)) :=
    hg.min_const (3 : ℝ)
  exact h1.max_const (-3 : ℝ)

/-- The extended and clipped slope is bounded by 3. -/
lemma extendAndClip_bound (f : ℝ → ℝ) (s : Set ℝ) (K : NNReal)
    (hK : LipschitzOnWith K f s) (z : ℝ) :
    |extendAndClip f s K hK z| ≤ 3 := by
  have h1 : -3 ≤ extendAndClip f s K hK z := by
    simp [extendAndClip] <;> exact le_max_right _ _
  have h2 : extendAndClip f s K hK z ≤ 3 := by
    simp [extendAndClip]
    <;> exact max_le (min_le_right _ _) (by norm_num)
  exact abs_le.mpr ⟨h1, h2⟩

end Kakeya.Assouad
