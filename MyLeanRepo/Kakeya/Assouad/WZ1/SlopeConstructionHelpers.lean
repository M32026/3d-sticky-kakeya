import MyLeanRepo.Kakeya.Assouad.WZ1.GlobalSlabADTransportStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.ADAffineThickeningTransport

/-!
# Supporting lemmas for slope construction in anchored global grain transport

1. Generalized horizontalization: accepts `|normal 2| ≤ c * |normal 0|` for `c ≤ 1`
2. Ratio Lipschitz: if `n` is Lipschitz and `|n_0| ≥ c`, then `n_1/n_0` is Lipschitz
3. Slope bound: `|n_1/n_0| ≤ 3` when `|n_0| ≥ 1/2` and `‖n‖ = 1`
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/--
Generalized horizontalization: the grain-direction projection lies in the
`delta`-thickening of an affine image of the normal projection, whenever
`|normal 2| ≤ c * |normal 0|` with `c ≤ 1`.
-/
lemma wz1_horizontalize_slab_projection_generalized
    (E : Set Point3) (normal : Point3) (z delta c : ℝ)
    (hdelta : 0 < delta)
    (hnorm : ‖normal‖ = 1)
    (hn0 : 1 / 3 ≤ |normal 0|)
    (hc : c ≤ 1)
    (hn2 : |normal 2| ≤ c * |normal 0|)
    (hslab : ∀ p ∈ E, p 2 ∈ Set.Icc (z - delta) (z + delta)) :
    scalarProjection (globalGrainDirection (normal 1 / normal 0)) E ⊆
      Metric.cthickening delta
        ((fun u : ℝ => u / normal 0 - normal 2 * z / normal 0) ''
          scalarProjection normal E) := by
  have hn0_pos : 0 < |normal 0| := by linarith
  have hn0_ne_zero : normal 0 ≠ 0 := abs_ne_zero.mp hn0_pos.ne'
  have h_ratio : |normal 2 / normal 0| ≤ c := by
    calc
      |normal 2 / normal 0| = |normal 2| / |normal 0| := by rw [abs_div]
      _ ≤ (c * |normal 0|) / |normal 0| := by gcongr
      _ = c := by
        field_simp [hn0_pos.ne'] <;> ring
  have h_ratio_le_one : |normal 2 / normal 0| ≤ 1 := h_ratio.trans hc
  intro y hy
  rcases hy with ⟨p, hp, rfl⟩
  let u : ℝ := inner ℝ p normal
  have hu : u ∈ scalarProjection normal E := ⟨p, hp, rfl⟩
  let x : ℝ := u / normal 0 - normal 2 * z / normal 0
  have hx : x ∈ (fun u : ℝ => u / normal 0 - normal 2 * z / normal 0) '' scalarProjection normal E :=
    ⟨u, hu, rfl⟩
  have h_sum3 : ∀ (a b : Point3), inner ℝ a b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
    intro a b
    rw [PiLp.inner_apply]
    simp [Fin.sum_univ_succ, mul_comm] <;> ring
  have h_inner_dir : inner ℝ p (globalGrainDirection (normal 1 / normal 0)) =
      p 0 + (normal 1 / normal 0) * p 1 := by
    rw [h_sum3]
    simp [globalGrainDirection] <;> ring
  have h_inner_normal : inner ℝ p normal =
      normal 0 * p 0 + normal 1 * p 1 + normal 2 * p 2 := by
    rw [h_sum3] <;> ring
  have h_u : u = normal 0 * p 0 + normal 1 * p 1 + normal 2 * p 2 := h_inner_normal
  have h_x_eq : x = p 0 + (normal 1 / normal 0) * p 1 + (normal 2 / normal 0) * (p 2 - z) := by
    have h : x = (u - normal 2 * z) / normal 0 := by
      simp only [x] <;> ring
    rw [h, h_u]
    field_simp [hn0_ne_zero] <;> ring
  have h_main : |inner ℝ p (globalGrainDirection (normal 1 / normal 0)) - x| ≤ delta := by
    rw [h_inner_dir, h_x_eq]
    have h5 : (p 0 + (normal 1 / normal 0) * p 1) -
          (p 0 + (normal 1 / normal 0) * p 1 + (normal 2 / normal 0) * (p 2 - z)) =
        -((normal 2 / normal 0) * (p 2 - z)) := by ring
    rw [h5]
    have h_abs : |-((normal 2 / normal 0) * (p 2 - z))| =
        |normal 2 / normal 0| * |p 2 - z| := by
      calc
        |-((normal 2 / normal 0) * (p 2 - z))|
          = |(normal 2 / normal 0) * (p 2 - z)| := by rw [abs_neg]
        _ = |normal 2 / normal 0| * |p 2 - z| := by rw [abs_mul]
    rw [h_abs]
    have h8 : p 2 ∈ Set.Icc (z - delta) (z + delta) := hslab p hp
    have h7 : |p 2 - z| ≤ delta := by
      have h73 : -delta ≤ p 2 - z := by linarith [h8.1]
      have h74 : p 2 - z ≤ delta := by linarith [h8.2]
      exact abs_le.mpr ⟨h73, h74⟩
    have h9 : |normal 2 / normal 0| * |p 2 - z| ≤ 1 * delta := by
      gcongr <;> linarith
    simpa using h9
  exact Metric.mem_cthickening_of_dist_le (inner ℝ p (globalGrainDirection (normal 1 / normal 0))) x delta
    ((fun u : ℝ => u / normal 0 - normal 2 * z / normal 0) '' scalarProjection normal E)
    hx h_main

/--
Lipschitz bound for the ratio `n_1 / n_0` when `|n_0| ≥ c > 0`.

If `n : ℝ → Point3` is Lipschitz with real constant `L` and `|n(t)_0| ≥ c`
and `|n(t)_1| ≤ 1` for all t, then `f(t) = n(t)_1 / n(t)_0` is Lipschitz
with real constant `2 * L / c^2`.
-/
lemma ratio_lipschitz_on_real
    {n : ℝ → Point3} {L c : ℝ} {s : Set ℝ}
    (hL_nonneg : 0 ≤ L)
    (hL : ∀ t ∈ s, ∀ u ∈ s, dist (n t) (n u) ≤ L * dist t u)
    (hc_pos : 0 < c)
    (hn0 : ∀ t ∈ s, c ≤ |n t 0|)
    (hn0_bound : ∀ t ∈ s, |n t 0| ≤ 1)
    (hn1 : ∀ t ∈ s, |n t 1| ≤ 1) :
    ∀ t ∈ s, ∀ u ∈ s,
      |n t 1 / n t 0 - n u 1 / n u 0| ≤ (2 * L / c ^ 2) * |t - u| := by
  intro t ht u hu
  have h_dist_n : dist (n t) (n u) ≤ L * dist t u := hL t ht u hu
  have h0 : |n t 0 - n u 0| ≤ L * |t - u| := by
    have h : |n t 0 - n u 0| ≤ ‖n t - n u‖ := PiLp.norm_apply_le (n t - n u) 0
    have h2 : ‖n t - n u‖ = dist (n t) (n u) := by rfl
    rw [h2] at h
    simpa [Real.dist_eq] using h.trans h_dist_n
  have h1 : |n t 1 - n u 1| ≤ L * |t - u| := by
    have h : |n t 1 - n u 1| ≤ ‖n t - n u‖ := PiLp.norm_apply_le (n t - n u) 1
    have h2 : ‖n t - n u‖ = dist (n t) (n u) := by rfl
    rw [h2] at h
    simpa [Real.dist_eq] using h.trans h_dist_n
  have hnt0 : c ≤ |n t 0| := hn0 t ht
  have hnu0 : c ≤ |n u 0| := hn0 u hu
  have hnt1 : |n t 1| ≤ 1 := hn1 t ht
  have hnu1 : |n u 1| ≤ 1 := hn1 u hu
  have h_ne_t : n t 0 ≠ 0 := by
    have : 0 < |n t 0| := by linarith
    exact abs_ne_zero.mp this.ne'
  have h_ne_u : n u 0 ≠ 0 := by
    have : 0 < |n u 0| := by linarith
    exact abs_ne_zero.mp this.ne'
  have h_eq : n t 1 / n t 0 - n u 1 / n u 0 =
      (n t 1 * n u 0 - n u 1 * n t 0) / (n t 0 * n u 0) := by
    field_simp [h_ne_t, h_ne_u] <;> ring
  rw [h_eq]
  have h_abs_tu : 0 ≤ |t - u| := abs_nonneg _
  have h_num : |n t 1 * n u 0 - n u 1 * n t 0| ≤ 2 * L * |t - u| := by
    have h_alg : n t 1 * n u 0 - n u 1 * n t 0 =
        n t 1 * (n u 0 - n t 0) + n t 0 * (n t 1 - n u 1) := by ring
    have h_triangle : |n t 1 * (n u 0 - n t 0) + n t 0 * (n t 1 - n u 1)| ≤
        |n t 1 * (n u 0 - n t 0)| + |n t 0 * (n t 1 - n u 1)| := by
      exact abs_add_le (n t 1 * (n u 0 - n t 0)) (n t 0 * (n t 1 - n u 1))
    have h6 : |n t 1 * (n u 0 - n t 0)| = |n t 1| * |n u 0 - n t 0| := by rw [abs_mul]
    have h7 : |n t 0 * (n t 1 - n u 1)| = |n t 0| * |n t 1 - n u 1| := by rw [abs_mul]
    have h_tri : |n t 1 * (n u 0 - n t 0) + n t 0 * (n t 1 - n u 1)| ≤
        |n t 1| * |n u 0 - n t 0| + |n t 0| * |n t 1 - n u 1| := by
      rw [h6, h7] at h_triangle
      exact h_triangle
    have h0' : |n u 0 - n t 0| ≤ L * |t - u| := by
      have h_abs : |n u 0 - n t 0| = |n t 0 - n u 0| := by rw [show n u 0 - n t 0 = -(n t 0 - n u 0) by ring, abs_neg]
      rw [h_abs]
      exact h0
    have h3 : |n t 1| * |n u 0 - n t 0| ≤ L * |t - u| := by
      calc
        |n t 1| * |n u 0 - n t 0| ≤ 1 * |n u 0 - n t 0| := by gcongr
        _ = |n u 0 - n t 0| := by ring
        _ ≤ L * |t - u| := h0'
    have hnt0_bound : |n t 0| ≤ 1 := hn0_bound t ht
    have h4 : |n t 0| * |n t 1 - n u 1| ≤ L * |t - u| := by
      calc
        |n t 0| * |n t 1 - n u 1| ≤ 1 * |n t 1 - n u 1| := by
          exact mul_le_mul_of_nonneg_right hnt0_bound (abs_nonneg _)
        _ = |n t 1 - n u 1| := by ring
        _ ≤ L * |t - u| := h1
    have h9 : |n t 1 * (n u 0 - n t 0) + n t 0 * (n t 1 - n u 1)| ≤ 2 * L * |t - u| := by
      calc
        _ ≤ |n t 1| * |n u 0 - n t 0| + |n t 0| * |n t 1 - n u 1| := h_tri
        _ ≤ L * |t - u| + L * |t - u| := add_le_add h3 h4
        _ = 2 * L * |t - u| := by ring
    rw [h_alg]
    exact h9
  have h_den : |n t 0 * n u 0| ≥ c ^ 2 := by
    calc
      |n t 0 * n u 0| = |n t 0| * |n u 0| := by rw [abs_mul]
      _ ≥ c * c := by gcongr
      _ = c ^ 2 := by ring
  have hc2_pos : 0 < c ^ 2 := by positivity
  have h_den_pos : 0 < |n t 0 * n u 0| := by
    have h1 : 0 < c ^ 2 := hc2_pos
    have h2 : c ^ 2 ≤ |n t 0 * n u 0| := h_den
    linarith
  have h_main2 : |n t 1 * n u 0 - n u 1 * n t 0| / |n t 0 * n u 0| ≤
      (2 * L * |t - u|) / c ^ 2 := by
    have h_div1 : |n t 1 * n u 0 - n u 1 * n t 0| / |n t 0 * n u 0| ≤
        (2 * L * |t - u|) / |n t 0 * n u 0| := by
      apply div_le_div_of_nonneg_right h_num
      exact le_of_lt h_den_pos
    have h_num_nonneg : 0 ≤ 2 * L * |t - u| := by positivity
    have h_div2 : (2 * L * |t - u|) / |n t 0 * n u 0| ≤ (2 * L * |t - u|) / c ^ 2 := by
      have h_inv : 1 / |n t 0 * n u 0| ≤ 1 / c ^ 2 := by
        apply one_div_le_one_div_of_le
        · positivity
        · exact h_den
      calc
        (2 * L * |t - u|) / |n t 0 * n u 0|
          = (2 * L * |t - u|) * (1 / |n t 0 * n u 0|) := by ring
        _ ≤ (2 * L * |t - u|) * (1 / c ^ 2) := by gcongr
        _ = (2 * L * |t - u|) / c ^ 2 := by ring
    exact h_div1.trans h_div2
  calc
    |(n t 1 * n u 0 - n u 1 * n t 0) / (n t 0 * n u 0)|
      = |n t 1 * n u 0 - n u 1 * n t 0| / |n t 0 * n u 0| := by rw [abs_div]
    _ ≤ (2 * L * |t - u|) / c ^ 2 := h_main2
    _ = (2 * L / c ^ 2) * |t - u| := by ring

/--
Normalization is Lipschitz with constant `2 / r` on the set where `‖x‖ ≥ r`.
-/
lemma normalize_lipschitz_on
    {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (hr : 0 < r) {s : Set E} (hs : ∀ x ∈ s, r ≤ ‖x‖) :
    LipschitzOnWith ⟨2 / r, by positivity⟩ (fun x : E => (1 / ‖x‖) • x) s := by
  intro x hx y hy
  have hxr : r ≤ ‖x‖ := hs x hx
  have hyr : r ≤ ‖y‖ := hs y hy
  have hx_pos : 0 < ‖x‖ := by linarith
  have hy_pos : 0 < ‖y‖ := by linarith
  set c : ℝ := 1 / (‖x‖ * ‖y‖) with hc_def
  have hc_nonneg : 0 ≤ c := by positivity
  have h_main : ‖(1 / ‖x‖) • x - (1 / ‖y‖) • y‖ ≤ (2 / r) * ‖x - y‖ := by
    have h1 : (1 / ‖x‖) • x - (1 / ‖y‖) • y =
        c • (‖y‖ • x - ‖x‖ • y) := by
      have h11 : (1 / ‖x‖) • x = c • (‖y‖ • x) := by
        have h : (1 / ‖x‖) = c * ‖y‖ := by
          simp [hc_def] <;> field_simp [hx_pos.ne', hy_pos.ne'] <;> ring
        rw [h, mul_smul]
      have h12 : (1 / ‖y‖) • y = c • (‖x‖ • y) := by
        have h : (1 / ‖y‖) = c * ‖x‖ := by
          simp [hc_def] <;> field_simp [hx_pos.ne', hy_pos.ne'] <;> ring
        rw [h, mul_smul]
      rw [h11, h12]
      exact (smul_sub c (‖y‖ • x) (‖x‖ • y)).symm
    rw [h1]
    have h2 : ‖c • (‖y‖ • x - ‖x‖ • y)‖ = c * ‖‖y‖ • x - ‖x‖ • y‖ := by
      have h21 : ‖c • (‖y‖ • x - ‖x‖ • y)‖ = |c| * ‖‖y‖ • x - ‖x‖ • y‖ := by
        rw [norm_smul] <;> rfl
      rw [h21, abs_of_nonneg hc_nonneg]
    rw [h2]
    have h3 : ‖‖y‖ • x - ‖x‖ • y‖ ≤ 2 * ‖y‖ * ‖x - y‖ := by
      have h4 : ‖y‖ • x - ‖x‖ • y = ‖y‖ • (x - y) + (‖y‖ - ‖x‖) • y := by
        rw [smul_sub, sub_smul] <;> abel
      rw [h4]
      have h5 : ‖‖y‖ • (x - y) + (‖y‖ - ‖x‖) • y‖ ≤
          ‖‖y‖ • (x - y)‖ + ‖(‖y‖ - ‖x‖) • y‖ := norm_add_le _ _
      have h6 : ‖‖y‖ • (x - y)‖ = ‖y‖ * ‖x - y‖ := by
        have h61 : ‖‖y‖ • (x - y)‖ = |‖y‖| * ‖x - y‖ := by
          rw [norm_smul] <;> rfl
        rw [h61, abs_of_nonneg (norm_nonneg y)]
      have h7 : ‖(‖y‖ - ‖x‖) • y‖ = |‖y‖ - ‖x‖| * ‖y‖ := by
        have h71 : ‖(‖y‖ - ‖x‖) • y‖ = |‖y‖ - ‖x‖| * ‖y‖ := by
          rw [norm_smul] <;> rfl
        exact h71
      have h8 : |‖y‖ - ‖x‖| = |‖x‖ - ‖y‖| := by rw [show ‖y‖ - ‖x‖ = -(‖x‖ - ‖y‖) by ring, abs_neg]
      have h9 : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
      have h10 : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by rw [h8] <;> exact h9
      calc
        _ ≤ ‖‖y‖ • (x - y)‖ + ‖(‖y‖ - ‖x‖) • y‖ := h5
        _ = ‖y‖ * ‖x - y‖ + |‖y‖ - ‖x‖| * ‖y‖ := by rw [h6, h7]
        _ ≤ ‖y‖ * ‖x - y‖ + ‖x - y‖ * ‖y‖ := by gcongr
        _ = 2 * ‖y‖ * ‖x - y‖ := by ring
    have h9 : c * ‖‖y‖ • x - ‖x‖ • y‖ ≤ c * (2 * ‖y‖ * ‖x - y‖) := by gcongr
    have h10 : c * (2 * ‖y‖ * ‖x - y‖) = (2 / ‖x‖) * ‖x - y‖ := by
      simp [hc_def] <;> field_simp [hx_pos.ne', hy_pos.ne'] <;> ring
    rw [h10] at h9
    have h11 : (2 / ‖x‖) * ‖x - y‖ ≤ (2 / r) * ‖x - y‖ := by gcongr <;> linarith
    exact h9.trans h11
  let K : NNReal := ⟨2 / r, by positivity⟩
  have h_goal : edist ((1 / ‖x‖) • x) ((1 / ‖y‖) • y) ≤
      (K : ENNReal) * edist x y := by
    have h_dist : dist ((1 / ‖x‖) • x) ((1 / ‖y‖) • y) ≤ (2 / r) * dist x y := by
      simpa [dist_eq_norm] using h_main
    have hK_nonneg : 0 ≤ (2 / r : ℝ) := by positivity
    have h_edist1 : edist ((1 / ‖x‖) • x) ((1 / ‖y‖) • y) =
        ENNReal.ofReal (dist ((1 / ‖x‖) • x) ((1 / ‖y‖) • y)) := edist_dist _ _
    rw [h_edist1]
    have h_mul : ENNReal.ofReal ((2 / r) * dist x y) =
        ENNReal.ofReal (2 / r) * ENNReal.ofReal (dist x y) := by
      rw [ENNReal.ofReal_mul hK_nonneg]
    have h_le : ENNReal.ofReal (dist ((1 / ‖x‖) • x) ((1 / ‖y‖) • y)) ≤
        ENNReal.ofReal ((2 / r) * dist x y) :=
      ENNReal.ofReal_le_ofReal h_dist
    rw [h_mul] at h_le
    have h_edist2 : edist x y = ENNReal.ofReal (dist x y) := edist_dist _ _
    have hK_eq : (K : ENNReal) = ENNReal.ofReal (2 / r) := by
      have h : (K : ENNReal) = ENNReal.ofReal (K : ℝ) := by
        exact ENNReal.coe_nnreal_eq K
      rw [h]
      have hK_val : (K : ℝ) = 2 / r := by
        exact Subtype.coe_mk (2 / r) _
      rw [hK_val]
    rw [hK_eq, h_edist2]
    exact h_le
  exact h_goal

/--
Slope bound: if `‖n‖ = 1` and `|n 0| ≥ 1/2`, then `|n 1 / n 0| ≤ 2 < 3`.
-/
lemma slope_bound_from_normal (n : Point3) (hnorm : ‖n‖ = 1) (hn0 : 1 / 2 ≤ |n 0|) :
    |n 1 / n 0| ≤ 3 := by
  have hn1 : |n 1| ≤ 1 := by
    let e1 : Point3 := EuclideanSpace.single 1 (1 : ℝ)
    have hinner : inner ℝ n e1 = n 1 := by
      rw [EuclideanSpace.inner_single_right] <;> simp
    have hbound : |inner ℝ n e1| ≤ ‖n‖ * ‖e1‖ := abs_real_inner_le_norm n e1
    have he1 : ‖e1‖ = 1 := by rw [PiLp.norm_single] <;> norm_num
    rw [hinner, he1, hnorm] at hbound
    simpa using hbound
  have hn0_pos : 0 < |n 0| := by linarith
  calc
    |n 1 / n 0| = |n 1| / |n 0| := by rw [abs_div]
    _ ≤ 1 / |n 0| := by gcongr
    _ ≤ 1 / (1 / 2 : ℝ) := by gcongr
    _ = 2 := by norm_num
    _ ≤ 3 := by norm_num

end Kakeya.Assouad
