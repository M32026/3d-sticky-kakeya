import MyLeanRepo.Kakeya.Assouad.WZ1.GeneralizedHorizontalize
import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import Mathlib.Tactic

/-!
# Second-chart horizontalization with large vertical component

This is the index-swapped counterpart to `generalized_per_cell_horizontalize_ad`.
Where the first chart uses `normal 0` as the dominant horizontal component and
the direction `globalGrainDirection (normal 1 / normal 0)`, this second chart
uses `normal 1` as dominant and the direction `point3 (normal 0 / normal 1) 1 0`.

The proof is identical up to swapping indices 0 and 1.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/--
Second-chart slab containment: the grain projection along `point3 (n0/n1) 1 0`
is within `2*δ` of the affine image `u/n1 - n2*z/n1` of the normal projection.
-/
lemma generalized_horizontalize_slab_containment_second
    {E : Set Point3} {normal : Point3} {z delta : ℝ}
    (hnorm : ‖normal‖ = 1)
    (hn1 : 1 / 3 ≤ |normal 1|)
    (hn2 : |normal 2| ≤ 1 / 2)
    (hslab : ∀ p ∈ E, p 2 ∈ Set.Icc (z - delta) (z + delta))
    (hdelta : 0 < delta) :
    scalarProjection (point3 (normal 0 / normal 1) 1 0) E ⊆
    Metric.cthickening (2 * delta)
      ((fun u : ℝ => u / normal 1 - normal 2 * z / normal 1) ''
        (scalarProjection normal E)) := by
  have hn1_pos : 0 < |normal 1| := by linarith
  have hn1_ne : normal 1 ≠ 0 := abs_ne_zero.mp hn1_pos.ne'
  have h_ratio : |normal 2| / |normal 1| ≤ 3 / 2 := by
    calc
      |normal 2| / |normal 1| ≤ (1 / 2 : ℝ) / |normal 1| := by gcongr
      _ ≤ (1 / 2 : ℝ) / (1 / 3 : ℝ) := by gcongr
      _ = 3 / 2 := by norm_num
  intro y hy
  rcases hy with ⟨p, hp, rfl⟩
  let u : ℝ := inner ℝ p normal
  have hu : u ∈ scalarProjection normal E := ⟨p, hp, rfl⟩
  let x : ℝ := u / normal 1 - normal 2 * z / normal 1
  have hx : x ∈ (fun u : ℝ => u / normal 1 - normal 2 * z / normal 1) ''
      (scalarProjection normal E) := ⟨u, hu, rfl⟩
  have h_sum3 : ∀ (a b : Point3), inner ℝ a b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
    intro a b
    rw [PiLp.inner_apply]
    simp [Fin.sum_univ_succ, mul_comm] <;> ring
  have h_dir_eq : point3 (normal 0 / normal 1) 1 0 =
      (normal 0 / normal 1) • EuclideanSpace.single (0 : Fin 3) 1 +
        EuclideanSpace.single (1 : Fin 3) 1 := by
    ext i
    fin_cases i <;> simp [point3] <;> norm_num
  have h_inner_dir : inner ℝ p (point3 (normal 0 / normal 1) 1 0) =
      (normal 0 / normal 1) * p 0 + p 1 := by
    rw [h_dir_eq]
    rw [h_sum3]
    <;> simp [EuclideanSpace.inner_single_right] <;> ring
  have h_inner_normal1 : inner ℝ p normal =
      normal 0 * p 0 + normal 1 * p 1 + normal 2 * p 2 := by
    rw [h_sum3] <;> ring
  have h_inner_normal : u = normal 0 * p 0 + normal 1 * p 1 + normal 2 * p 2 :=
    h_inner_normal1
  have h_x_eq : x = (normal 0 / normal 1) * p 0 + p 1 + (normal 2 / normal 1) * (p 2 - z) := by
    have h : x = (u - normal 2 * z) / normal 1 := by
      simp only [x] <;> ring
    rw [h, h_inner_normal]
    field_simp [hn1_ne] <;> ring
  have h_main : |inner ℝ p (point3 (normal 0 / normal 1) 1 0) - x| ≤ 2 * delta := by
    rw [h_inner_dir, h_x_eq]
    have h5 : ((normal 0 / normal 1) * p 0 + p 1) -
          ((normal 0 / normal 1) * p 0 + p 1 + (normal 2 / normal 1) * (p 2 - z)) =
        -((normal 2 / normal 1) * (p 2 - z)) := by ring
    rw [h5]
    have h_abs : |-((normal 2 / normal 1) * (p 2 - z))| =
        |normal 2| / |normal 1| * |p 2 - z| := by
      calc
        |-((normal 2 / normal 1) * (p 2 - z))|
          = |(normal 2 / normal 1) * (p 2 - z)| := by rw [abs_neg]
        _ = |normal 2 / normal 1| * |p 2 - z| := by rw [abs_mul]
        _ = |normal 2| / |normal 1| * |p 2 - z| := by rw [abs_div]
    rw [h_abs]
    have h8 : p 2 ∈ Set.Icc (z - delta) (z + delta) := hslab p hp
    have h7 : |p 2 - z| ≤ delta := by
      have h73 : -delta ≤ p 2 - z := by linarith [h8.1]
      have h74 : p 2 - z ≤ delta := by linarith [h8.2]
      exact abs_le.mpr ⟨h73, h74⟩
    have h9 : |normal 2| / |normal 1| * |p 2 - z| ≤ (3 / 2 : ℝ) * delta := by
      calc
        |normal 2| / |normal 1| * |p 2 - z|
          ≤ (3 / 2 : ℝ) * |p 2 - z| := by gcongr
        _ ≤ (3 / 2 : ℝ) * delta := by gcongr
    have h10 : (3 / 2 : ℝ) * delta ≤ 2 * delta := by linarith
    exact h9.trans h10
  let affine_set : Set ℝ := (fun u : ℝ => u / normal 1 - normal 2 * z / normal 1) ''
      (scalarProjection normal E)
  exact Metric.mem_cthickening_of_dist_le
    (inner ℝ p (point3 (normal 0 / normal 1) 1 0)) x (2 * delta)
    affine_set hx h_main

/--
Second-chart generalized per-cell horizontalization AD transport.

Swaps indices 0 and 1 relative to `generalized_per_cell_horizontalize_ad`:
uses `|normal 1| ≥ 1/3` as the dominant horizontal component and the direction
`point3 (normal 0 / normal 1) 1 0`.

Constant blowup: affine factor 10 × thickening factor 36 = 360.
-/
lemma generalized_per_cell_horizontalize_ad_second
    {E : Set Point3} {normal : Point3} {z delta alpha : ℝ} {C : ENNReal}
    (hdelta : 0 < delta)
    (hdelta_one : delta ≤ 1)
    (halpha : 0 < alpha)
    (halpha_one : alpha ≤ 1)
    (hnorm : ‖normal‖ = 1)
    (hn1 : 1 / 3 ≤ |normal 1|)
    (hn2 : |normal 2| ≤ 1 / 2)
    (hslab : ∀ p ∈ E, p 2 ∈ Set.Icc (z - delta) (z + delta))
    (hE_unitBall : E ⊆ Metric.closedBall (0 : Point3) 1)
    (hAD : IsADSet1 (scalarProjection normal E) delta alpha C) :
    IsADSet1 (scalarProjection (point3 (normal 0 / normal 1) 1 0) E)
      delta alpha (360 * C) := by
  let a : ℝ := 1 / normal 1
  let b : ℝ := -normal 2 * z / normal 1
  let affine_image : Set ℝ := (fun u : ℝ => u / normal 1 - normal 2 * z / normal 1) '' (scalarProjection normal E)
  let target : Set ℝ := scalarProjection (point3 (normal 0 / normal 1) 1 0) E
  have hn1_le_one : |normal 1| ≤ 1 := by
    have h : |normal 1| ≤ ‖normal‖ := PiLp.norm_apply_le normal 1
    rw [hnorm] at h
    exact h
  have haLower : 1 / 4 ≤ |a| := by
    have h1 : |a| = 1 / |normal 1| := by
      have h_eq : a = 1 / normal 1 := by rfl
      rw [h_eq, abs_div] <;> simp
    rw [h1]
    have h2 : 1 ≤ 1 / |normal 1| := by
      calc 1 / |normal 1| ≥ 1 / (1 : ℝ) := by gcongr
           _ = 1 := by norm_num
    linarith
  have haUpper : |a| ≤ 4 := by
    have h1 : |a| = 1 / |normal 1| := by
      have h_eq : a = 1 / normal 1 := by rfl
      rw [h_eq, abs_div] <;> simp
    rw [h1]
    have h2 : 1 / |normal 1| ≤ 1 / (1 / 3 : ℝ) := by gcongr
    norm_num at h2 ⊢ <;> linarith
  have htargetBound : target ⊆ Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨p, hp, rfl⟩
    have hpNorm : ‖p‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hE_unitBall hp
    let direction := point3 (normal 0 / normal 1) 1 0
    have hdir_norm : ‖direction‖ ≤ 4 := by
      let e0 : Point3 := EuclideanSpace.single 0 (1 : ℝ)
      let e1 : Point3 := EuclideanSpace.single 1 (1 : ℝ)
      have heq : direction = (normal 0 / normal 1) • e0 + e1 := by
        ext i; fin_cases i <;> simp [direction, point3, e0, e1] <;> norm_num
      rw [heq]
      have he0 : ‖e0‖ = 1 := by rw [PiLp.norm_single] <;> norm_num
      have he1 : ‖e1‖ = 1 := by rw [PiLp.norm_single] <;> norm_num
      have hslope : |normal 0 / normal 1| ≤ 3 := by
        rw [abs_div]
        have h1 : |normal 0| ≤ 1 := by
          let e0_local : Point3 := EuclideanSpace.single 0 (1 : ℝ)
          have hinner : inner ℝ normal e0_local = normal 0 := by
            rw [EuclideanSpace.inner_single_right] <;> simp
          have hnorm0 : ‖e0_local‖ = 1 := by rw [PiLp.norm_single] <;> norm_num
          have hbound : |inner ℝ normal e0_local| ≤ ‖normal‖ * ‖e0_local‖ := abs_real_inner_le_norm normal e0_local
          rw [hinner, hnorm, hnorm0] at hbound
          simpa using hbound
        calc |normal 0| / |normal 1| ≤ 1 / |normal 1| := by gcongr
             _ ≤ 1 / (1 / 3 : ℝ) := by gcongr
             _ = 3 := by norm_num
      calc ‖(normal 0 / normal 1) • e0 + e1‖
          ≤ ‖(normal 0 / normal 1) • e0‖ + ‖e1‖ := norm_add_le _ _
        _ = |normal 0 / normal 1| + 1 := by rw [norm_smul, he0, he1] <;> simp only [mul_one, Real.norm_eq_abs]
        _ ≤ 3 + 1 := by gcongr
        _ = 4 := by norm_num
    have hinner : |inner ℝ p direction| ≤ ‖p‖ * ‖direction‖ := abs_real_inner_le_norm p direction
    have hbound : |inner ℝ p direction| ≤ 4 := by
      calc |inner ℝ p direction| ≤ ‖p‖ * ‖direction‖ := hinner
           _ ≤ 1 * 4 := by gcongr
           _ = 4 := by ring
    exact (abs_le.mp hbound)
  have hthick : target ⊆ Metric.cthickening (2 * delta) affine_image := by
    simpa [target, affine_image, a, b] using generalized_horizontalize_slab_containment_second hnorm hn1 hn2 hslab hdelta
  have h_affine_eq : (fun u : ℝ => a * u + b) = (fun u : ℝ => u / normal 1 - normal 2 * z / normal 1) := by
    funext u; simp [a, b] <;> ring
  have hthick2 : target ⊆ Metric.cthickening (2 * delta) ((fun u : ℝ => a * u + b) '' scalarProjection normal E) := by
    rw [h_affine_eq]
    exact hthick
  have h2δ_pos : 0 < 2 * delta := by positivity
  have h_final : IsADSet1 target delta alpha
      ((2 * (Nat.ceil ((2 * delta) / delta) + 1) : ENNReal) ^ 2 * (10 * C)) :=
    affine_generalized_thickening_transport
      (E := scalarProjection normal E) (B := target) (δ := delta) (α := alpha) (ε := 2 * delta)
      (C := C) (a := a) (b := b)
      hAD haLower haUpper hthick2 htargetBound hdelta halpha halpha_one h2δ_pos
  have h_ceil : Nat.ceil ((2 * delta) / delta) = 2 := by
    have hdiv : (2 * delta) / delta = 2 := by
      field_simp [hdelta.ne'] <;> ring
    rw [hdiv] <;> norm_num
  rw [h_ceil] at h_final
  have h_eq : ((2 * (2 + 1) : ENNReal) ^ 2 * (10 * C)) = (360 * C) := by
    have h1 : (2 * (2 + 1) : ENNReal) = 6 := by norm_num
    rw [h1]
    have h2 : (6 : ENNReal) ^ 2 = 36 := by norm_num
    rw [h2]
    have h3 : (36 : ENNReal) * (10 * C) = 360 * C := by
      calc (36 : ENNReal) * (10 * C) = (36 * (10 : ENNReal)) * C := by rw [mul_assoc]
        _ = (360 : ENNReal) * C := by norm_cast
        _ = 360 * C := by rfl
    exact h3
  exact h_eq ▸ h_final

end Kakeya.Assouad
