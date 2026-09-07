import MyLeanRepo.Kakeya.Assouad.WZ1.GlobalSlabADTransportStatements

/-!
WZ1 Proposition 9: remove the small vertical component of a projection normal
on one `delta`-height slab.
-/

namespace Kakeya.Assouad

theorem wz1_horizontalize_slab_projection :
    WZ1HorizontalizeSlabProjectionStatement := by
  intro E normal z delta hdelta hnorm hn0 hn2 hslab
  have hn0_ne_zero : normal 0 ≠ 0 := by
    have : 0 < |normal 0| := by linarith
    exact abs_ne_zero.mp this.ne'
  have h1 : |normal 2| / |normal 0| ≤ 3 / 10 := by
    calc
      |normal 2| / |normal 0| ≤ (1 / 10 : ℝ) / |normal 0| := by gcongr
      _ ≤ (1 / 10 : ℝ) / (1 / 3 : ℝ) := by gcongr
      _ = 3 / 10 := by norm_num
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
    simp [Fin.sum_univ_succ, mul_comm]
    ; ring
  have h_inner_dir : inner ℝ p (globalGrainDirection (normal 1 / normal 0)) =
      p 0 + (normal 1 / normal 0) * p 1 := by
    rw [h_sum3]
    simp [globalGrainDirection]
    ; ring
  have h_inner_normal : inner ℝ p normal =
      normal 0 * p 0 + normal 1 * p 1 + normal 2 * p 2 := by
    rw [h_sum3] ; ring
  have h_u : u = normal 0 * p 0 + normal 1 * p 1 + normal 2 * p 2 := h_inner_normal
  have h_x_eq : x = p 0 + (normal 1 / normal 0) * p 1 + (normal 2 / normal 0) * (p 2 - z) := by
    have h : x = (u - normal 2 * z) / normal 0 := by
      simp only [x] ; ring
    rw [h, h_u]
    field_simp [hn0_ne_zero] ; ring
  have h_main : |inner ℝ p (globalGrainDirection (normal 1 / normal 0)) - x| ≤ delta := by
    rw [h_inner_dir, h_x_eq]
    have h5 : (p 0 + (normal 1 / normal 0) * p 1) -
          (p 0 + (normal 1 / normal 0) * p 1 + (normal 2 / normal 0) * (p 2 - z)) =
        -((normal 2 / normal 0) * (p 2 - z)) := by ring
    rw [h5]
    have h_abs : |-((normal 2 / normal 0) * (p 2 - z))| =
        |normal 2| / |normal 0| * |p 2 - z| := by
      calc
        |-((normal 2 / normal 0) * (p 2 - z))|
          = |(normal 2 / normal 0) * (p 2 - z)| := by rw [abs_neg]
        _ = |normal 2 / normal 0| * |p 2 - z| := by rw [abs_mul]
        _ = |normal 2| / |normal 0| * |p 2 - z| := by rw [abs_div]
    rw [h_abs]
    have h8 : p 2 ∈ Set.Icc (z - delta) (z + delta) := hslab p hp
    have h7 : |p 2 - z| ≤ delta := by
      have h73 : -delta ≤ p 2 - z := by linarith [h8.1]
      have h74 : p 2 - z ≤ delta := by linarith [h8.2]
      exact abs_le.mpr ⟨h73, h74⟩
    have h9 : |normal 2| / |normal 0| * |p 2 - z| ≤ (3 / 10 : ℝ) * delta := by
      calc
        |normal 2| / |normal 0| * |p 2 - z|
          ≤ (3 / 10 : ℝ) * |p 2 - z| := by gcongr
        _ ≤ (3 / 10 : ℝ) * delta := by gcongr
    have h10 : (3 / 10 : ℝ) * delta ≤ delta := by
      exact mul_le_of_le_one_left (by linarith) (by norm_num)
    exact h9.trans h10
  exact Metric.mem_cthickening_of_dist_le (inner ℝ p (globalGrainDirection (normal 1 / normal 0))) x delta
    ((fun u : ℝ => u / normal 0 - normal 2 * z / normal 0) '' scalarProjection normal E)
    hx h_main

end Kakeya.Assouad
