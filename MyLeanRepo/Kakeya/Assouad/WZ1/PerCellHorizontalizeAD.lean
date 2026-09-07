import MyLeanRepo.Kakeya.Assouad.WZ1.HorizontalizeSlabProjection
import MyLeanRepo.Kakeya.Assouad.WZ1.ADAffineThickeningTransport

/-!
# Per-cell horizontalization and affine AD transport

Compose the completed horizontal-projection containment and affine-thickening
AD stability for one slab-local set.
-/

namespace Kakeya.Assouad

lemma per_cell_horizontalize_ad_transport
    (E : Set Point3) (normal : Point3)
    (z delta alpha : ℝ) (C : ENNReal)
    (hdelta : 0 < delta)
    (hdelta_one : delta ≤ 1)
    (halpha : 0 < alpha)
    (halpha_one : alpha ≤ 1)
    (hnorm : ‖normal‖ = 1)
    (hn0 : 1 / 3 ≤ |normal 0|)
    (hn2 : |normal 2| ≤ 1 / 10)
    (hslab :
      ∀ p ∈ E,
        p 2 ∈ Set.Icc (z - delta) (z + delta))
    (hE_unitBall :
      E ⊆ Metric.closedBall (0 : Point3) 1)
    (hAD :
      IsADSet1
        (scalarProjection normal E) delta alpha C) :
    IsADSet1
      (scalarProjection
        (globalGrainDirection (normal 1 / normal 0)) E)
      delta alpha (100000 * C) := by
  let a : ℝ := 1 / normal 0
  let b : ℝ := -normal 2 * z / normal 0
  let direction : Point3 :=
    globalGrainDirection (normal 1 / normal 0)
  let target : Set ℝ := scalarProjection direction E
  let source : Set ℝ := scalarProjection normal E
  have hn0_pos : 0 < |normal 0| := by
    linarith
  have hcoord0 : |normal 0| ≤ 1 := by
    let e0 : Point3 :=
      EuclideanSpace.single 0 (1 : ℝ)
    have hinner : inner ℝ normal e0 = normal 0 := by
      rw [EuclideanSpace.inner_single_right]
      simp
    have hbound :
        |inner ℝ normal e0| ≤ ‖normal‖ * ‖e0‖ :=
      abs_real_inner_le_norm normal e0
    have he0 : ‖e0‖ = 1 := by
      rw [PiLp.norm_single]
      norm_num
    rw [hinner, he0, hnorm] at hbound
    simpa using hbound
  have hcoord1 : |normal 1| ≤ 1 := by
    let e1 : Point3 :=
      EuclideanSpace.single 1 (1 : ℝ)
    have hinner : inner ℝ normal e1 = normal 1 := by
      rw [EuclideanSpace.inner_single_right]
      simp
    have hbound :
        |inner ℝ normal e1| ≤ ‖normal‖ * ‖e1‖ :=
      abs_real_inner_le_norm normal e1
    have he1 : ‖e1‖ = 1 := by
      rw [PiLp.norm_single]
      norm_num
    rw [hinner, he1, hnorm] at hbound
    simpa using hbound
  have hthickRaw :
      scalarProjection direction E ⊆
        Metric.cthickening delta
          ((fun value : ℝ =>
              value / normal 0 -
                normal 2 * z / normal 0) '' source) :=
    wz1_horizontalize_slab_projection
      E normal z delta hdelta hnorm hn0 hn2 hslab
  have haffine :
      (fun value : ℝ =>
        value / normal 0 - normal 2 * z / normal 0) =
        (fun value : ℝ => a * value + b) := by
    funext value
    simp [a, b]
    ring
  have hthick :
      target ⊆
        Metric.cthickening delta
          ((fun value : ℝ => a * value + b) '' source) := by
    rw [haffine] at hthickRaw
    exact hthickRaw
  have habsa : |a| = 1 / |normal 0| := by
    simp [a, abs_div]
  have haLower : 1 / 4 ≤ |a| := by
    rw [habsa]
    apply one_div_le_one_div_of_le
    · linarith
    · linarith
  have haUpper : |a| ≤ 4 := by
    rw [habsa]
    have h :
        (1 : ℝ) / |normal 0| ≤
          1 / (1 / 3 : ℝ) := by
      gcongr
    norm_num at h ⊢
    linarith
  have hslope : |normal 1 / normal 0| ≤ 3 := by
    rw [abs_div]
    calc
      |normal 1| / |normal 0|
          ≤ 1 / |normal 0| := by gcongr
      _ ≤ 1 / (1 / 3 : ℝ) := by gcongr
      _ = 3 := by norm_num
  have hdirection : ‖direction‖ ≤ 4 := by
    let e0 : Point3 :=
      EuclideanSpace.single 0 (1 : ℝ)
    let e1 : Point3 :=
      EuclideanSpace.single 1 (1 : ℝ)
    have heq :
        direction =
          e0 + (normal 1 / normal 0) • e1 := by
      ext i
      fin_cases i <;>
        simp [direction, globalGrainDirection, e0, e1] <;>
        norm_num
    rw [heq]
    have he0 : ‖e0‖ = 1 := by
      rw [PiLp.norm_single]
      norm_num
    have he1 : ‖e1‖ = 1 := by
      rw [PiLp.norm_single]
      norm_num
    calc
      ‖e0 + (normal 1 / normal 0) • e1‖
          ≤ ‖e0‖ +
              ‖(normal 1 / normal 0) • e1‖ :=
        norm_add_le _ _
      _ = 1 + |normal 1 / normal 0| := by
        rw [he0, norm_smul, he1]
        simp only [mul_one, Real.norm_eq_abs]
      _ ≤ 1 + 3 := by gcongr
      _ = 4 := by norm_num
  have htargetBound :
      target ⊆ Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨p, hp, rfl⟩
    have hpNorm : ‖p‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using
        hE_unitBall hp
    have hinner :
        |inner ℝ p direction| ≤ ‖p‖ * ‖direction‖ :=
      abs_real_inner_le_norm p direction
    have hbound : |inner ℝ p direction| ≤ 4 := by
      calc
        |inner ℝ p direction| ≤ ‖p‖ * ‖direction‖ :=
          hinner
        _ ≤ 1 * 4 := by gcongr
        _ = 4 := by ring
    exact (abs_le.mp hbound)
  exact
    wz1_ad_affine_thickening_transport
      source target delta alpha a b C
      hdelta hdelta_one halpha halpha_one
      haLower haUpper hAD htargetBound hthick

/--
Second-chart version of `per_cell_horizontalize_ad_transport`.

Horizontalizes a normal projection to the `chart.second` grain direction
`point3 (normal 0 / normal 1) 1 0`. Requires `|normal 1| ≥ 1/3` instead of
`|normal 0| ≥ 1/3`.
-/
lemma per_cell_horizontalize_ad_transport_second
    (E : Set Point3) (normal : Point3)
    (z delta alpha : ℝ) (C : ENNReal)
    (hdelta : 0 < delta)
    (hdelta_one : delta ≤ 1)
    (halpha : 0 < alpha)
    (halpha_one : alpha ≤ 1)
    (hnorm : ‖normal‖ = 1)
    (hn1 : 1 / 3 ≤ |normal 1|)
    (hn2 : |normal 2| ≤ 1 / 10)
    (hslab :
      ∀ p ∈ E,
        p 2 ∈ Set.Icc (z - delta) (z + delta))
    (hE_unitBall :
      E ⊆ Metric.closedBall (0 : Point3) 1)
    (hAD :
      IsADSet1
        (scalarProjection normal E) delta alpha C) :
    IsADSet1
      (scalarProjection
        (Kakeya.Assouad.point3 (normal 0 / normal 1) 1 0) E)
      delta alpha (100000 * C) := by
  let a : ℝ := 1 / normal 1
  let b : ℝ := -normal 2 * z / normal 1
  let direction : Point3 := Kakeya.Assouad.point3 (normal 0 / normal 1) 1 0
  let target : Set ℝ := scalarProjection direction E
  let source : Set ℝ := scalarProjection normal E
  have hn1_pos : 0 < |normal 1| := by linarith
  have hn1_ne_zero : normal 1 ≠ 0 := abs_ne_zero.mp hn1_pos.ne'
  have hcoord0 : |normal 0| ≤ 1 := by
    let e0 : Point3 := EuclideanSpace.single 0 (1 : ℝ)
    have hinner : inner ℝ normal e0 = normal 0 := by
      rw [EuclideanSpace.inner_single_right] <;> simp
    have hbound : |inner ℝ normal e0| ≤ ‖normal‖ * ‖e0‖ := abs_real_inner_le_norm normal e0
    have he0 : ‖e0‖ = 1 := by rw [PiLp.norm_single] <;> norm_num
    rw [hinner, he0, hnorm] at hbound
    simpa using hbound
  have hcoord1 : |normal 1| ≤ 1 := by
    let e1 : Point3 := EuclideanSpace.single 1 (1 : ℝ)
    have hinner : inner ℝ normal e1 = normal 1 := by
      rw [EuclideanSpace.inner_single_right] <;> simp
    have hbound : |inner ℝ normal e1| ≤ ‖normal‖ * ‖e1‖ := abs_real_inner_le_norm normal e1
    have he1 : ‖e1‖ = 1 := by rw [PiLp.norm_single] <;> norm_num
    rw [hinner, he1, hnorm] at hbound
    simpa using hbound
  have h_ratio : |normal 2 / normal 1| ≤ 1 := by
    calc
      |normal 2 / normal 1| = |normal 2| / |normal 1| := by rw [abs_div]
      _ ≤ (1 / 10 : ℝ) / |normal 1| := by gcongr
      _ ≤ (1 / 10 : ℝ) / (1 / 3 : ℝ) := by gcongr
      _ = 3 / 10 := by norm_num
      _ ≤ 1 := by norm_num
  have hthick :
      target ⊆ Metric.cthickening delta ((fun value : ℝ => a * value + b) '' source) := by
    intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    let u : ℝ := inner ℝ p normal
    have hu : u ∈ source := ⟨p, hp, rfl⟩
    let x : ℝ := a * u + b
    have hx : x ∈ (fun value : ℝ => a * value + b) '' source := ⟨u, hu, rfl⟩
    have h_sum3 : ∀ (a b : Point3), inner ℝ a b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
      intro a b
      rw [PiLp.inner_apply] <;> simp [Fin.sum_univ_succ, mul_comm] <;> ring
    have h_inner_dir : inner ℝ p direction = (normal 0 / normal 1) * p 0 + p 1 := by
      rw [h_sum3]
      simp [direction, Kakeya.Assouad.point3] <;> ring
    have h_inner_normal : inner ℝ p normal = normal 0 * p 0 + normal 1 * p 1 + normal 2 * p 2 := by
      rw [h_sum3] <;> ring
    have h_u : u = normal 0 * p 0 + normal 1 * p 1 + normal 2 * p 2 := h_inner_normal
    have h_x_eq : x = (normal 0 / normal 1) * p 0 + p 1 + (normal 2 / normal 1) * (p 2 - z) := by
      have h : x = (u - normal 2 * z) / normal 1 := by
        simp only [x, a, b] <;> ring
      rw [h, h_u]
      field_simp [hn1_ne_zero] <;> ring
    have h_main : |inner ℝ p direction - x| ≤ delta := by
      rw [h_inner_dir, h_x_eq]
      have h5 : ((normal 0 / normal 1) * p 0 + p 1) -
            ((normal 0 / normal 1) * p 0 + p 1 + (normal 2 / normal 1) * (p 2 - z)) =
          -((normal 2 / normal 1) * (p 2 - z)) := by ring
      rw [h5]
      have h_abs : |-((normal 2 / normal 1) * (p 2 - z))| =
          |normal 2 / normal 1| * |p 2 - z| := by
        calc
          |-((normal 2 / normal 1) * (p 2 - z))|
            = |(normal 2 / normal 1) * (p 2 - z)| := by rw [abs_neg]
          _ = |normal 2 / normal 1| * |p 2 - z| := by rw [abs_mul]
      rw [h_abs]
      have h8 : p 2 ∈ Set.Icc (z - delta) (z + delta) := hslab p hp
      have h7 : |p 2 - z| ≤ delta := by
        have h73 : -delta ≤ p 2 - z := by linarith [h8.1]
        have h74 : p 2 - z ≤ delta := by linarith [h8.2]
        exact abs_le.mpr ⟨h73, h74⟩
      have h9 : |normal 2 / normal 1| * |p 2 - z| ≤ 1 * delta := by
        gcongr <;> linarith
      simpa using h9
    exact Metric.mem_cthickening_of_dist_le (inner ℝ p direction) x delta _ hx h_main
  have habsa : |a| = 1 / |normal 1| := by
    simp [a, abs_div]
  have haLower : 1 / 4 ≤ |a| := by
    rw [habsa]
    apply one_div_le_one_div_of_le <;> linarith
  have haUpper : |a| ≤ 4 := by
    rw [habsa]
    have h : (1 : ℝ) / |normal 1| ≤ 1 / (1 / 3 : ℝ) := by gcongr
    norm_num at h ⊢ <;> linarith
  have hslope : |normal 0 / normal 1| ≤ 3 := by
    rw [abs_div]
    calc
      |normal 0| / |normal 1|
          ≤ 1 / |normal 1| := by gcongr
      _ ≤ 1 / (1 / 3 : ℝ) := by gcongr
      _ = 3 := by norm_num
  have hdir0 : direction 0 = normal 0 / normal 1 := by
    simp [direction, Kakeya.Assouad.point3, EuclideanSpace.single_apply] <;> ring
  have hdir1 : direction 1 = 1 := by
    simp [direction, Kakeya.Assouad.point3, EuclideanSpace.single_apply] <;> ring
  have hdir2 : direction 2 = 0 := by
    simp [direction, Kakeya.Assouad.point3, EuclideanSpace.single_apply] <;> ring
  have hdirection_norm_sq : ‖direction‖ ^ 2 = (normal 0 / normal 1) ^ 2 + 1 := by
    rw [EuclideanSpace.real_norm_sq_eq direction]
    have h_sum : ∑ i : Fin 3, (direction i) ^ 2 = direction 0 ^ 2 + direction 1 ^ 2 + direction 2 ^ 2 := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] <;> simp <;> ring
    rw [h_sum, hdir0, hdir1, hdir2] <;> ring
  have hdirection : ‖direction‖ ≤ 4 := by
    have h2 : (normal 0 / normal 1) ^ 2 ≤ 9 := by
      have h3 : |normal 0 / normal 1| ≤ 3 := hslope
      have h4 : -3 ≤ normal 0 / normal 1 := by linarith [abs_le.mp h3]
      have h5 : normal 0 / normal 1 ≤ 3 := by linarith [abs_le.mp h3]
      nlinarith
    have h3 : ‖direction‖ ^ 2 ≤ 16 := by
      rw [hdirection_norm_sq] <;> linarith
    have h4 : 0 ≤ ‖direction‖ := by positivity
    nlinarith
  have htargetBound : target ⊆ Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨p, hp, rfl⟩
    have hpNorm : ‖p‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hE_unitBall hp
    have hinner : |inner ℝ p direction| ≤ ‖p‖ * ‖direction‖ := abs_real_inner_le_norm p direction
    have hbound : |inner ℝ p direction| ≤ 4 := by
      calc
        |inner ℝ p direction| ≤ ‖p‖ * ‖direction‖ := hinner
        _ ≤ 1 * 4 := by gcongr
        _ = 4 := by ring
    exact (abs_le.mp hbound)
  exact
    wz1_ad_affine_thickening_transport
      source target delta alpha a b C
      hdelta hdelta_one halpha halpha_one
      haLower haUpper hAD htargetBound hthick

end Kakeya.Assouad
