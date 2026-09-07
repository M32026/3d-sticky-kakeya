import MyLeanRepo.Kakeya.CV.HausdorffMeasureSphere.Geometry


open MeasureTheory Metric Set Filter
open scoped ENNReal Pointwise

namespace Kakeya.CV

noncomputable section

lemma dist_northPole_sq {p : Point 3} (hp : p ∈ unitSphere 3) :
    dist p northPole ^2 = 2 - 2 * p 0 := by
  have h_norm : ‖p‖ = 1 := by
    simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hp
  have h1 : ‖p‖^2 = (p 0)^2 + (p 1)^2 + (p 2)^2 := norm_sq_point3 p
  have h2 : (p 0)^2 + (p 1)^2 + (p 2)^2 = 1 := by
    have h3 : ‖p‖^2 = 1 := by rw [h_norm] <;> norm_num
    linarith [h1]
  have h4 : dist p northPole = ‖p - northPole‖ := by simp [dist_eq_norm]
  rw [h4]
  have h5 : ‖p - northPole‖^2 = (p 0 - 1)^2 + (p 1)^2 + (p 2)^2 := by
    simp [northPole, norm_sq_point3, mkPoint3_apply]
  rw [h5]
  linarith [h2]

/-- Helper: cone_low ⊆ sector ∪ null_set for cap bounds. -/
lemma cap_cone_low_subset (r : ℝ) (hr : 0 < r) (hr2 : r < Real.sqrt 2)
    (a R2 : ℝ) (ha_pos : 0 < a) (hR2_nonneg : 0 ≤ R2) (h_a2_R2 : a^2 + R2 = 1)
    (ha_def : a = 1 - r^2 / 2) (hR2_def : R2 = r^2 - r^4 / 4) :
    let cap_set : Set (Point 3) := sphereCap northPole r
    let sector : Set (Point 3) := Set.image2 (· • ·) (Set.Ioo (0 : ℝ) 1) cap_set
    let cone_low : Set (Point 3) := {p | 0 ≤ p 0 ∧ p 0 ≤ a ∧ (p 1)^2 + (p 2)^2 ≤ (p 0 / a)^2 * R2}
    let null_set : Set (Point 3) := unitSphere 3 ∪ {0}
    cone_low ⊆ sector ∪ null_set := by
  dsimp only
  let cap_set : Set (Point 3) := sphereCap northPole r
  let sector : Set (Point 3) := Set.image2 (· • ·) (Set.Ioo (0 : ℝ) 1) cap_set
  let cone_low : Set (Point 3) := {p | 0 ≤ p 0 ∧ p 0 ≤ a ∧ (p 1)^2 + (p 2)^2 ≤ (p 0 / a)^2 * R2}
  let null_set : Set (Point 3) := unitSphere 3 ∪ {0}
  intro p hp
  have hx_pos : 0 ≤ p 0 := hp.1
  have hx_le : p 0 ≤ a := hp.2.1
  have hyz : (p 1)^2 + (p 2)^2 ≤ (p 0 / a)^2 * R2 := hp.2.2
  by_cases h0 : p 0 = 0
  · have h1 : (p 1)^2 + (p 2)^2 ≤ 0 := by
      have h4 : (p 0 / a)^2 * R2 = 0 := by rw [h0]; ring
      rw [h4] at hyz; exact hyz
    have h2 : p 1 = 0 := by nlinarith
    have h3 : p 2 = 0 := by nlinarith
    have h_p0 : p = 0 := by
      ext i; fin_cases i <;> simp [h0, h2, h3] <;> rfl
    have h_in_null : p ∈ null_set := by
      rw [h_p0]; simp [null_set]
    exact Or.inr h_in_null
  · have hx_pos' : 0 < p 0 := by by_contra h; exact h0 (by linarith)
    set t : ℝ := ‖p‖ with ht_def
    have ht_pos : 0 < t := by
      have h1 : 0 ≤ ‖p‖ := norm_nonneg p
      by_contra h2
      have h3 : ‖p‖ = 0 := by linarith
      have h4 : p = 0 := by simpa [norm_eq_zero] using h3
      have h5 : p 0 = 0 := by rw [h4] <;> simp
      exact h0 h5
    have h_norm_sq : ‖p‖^2 = (p 0)^2 + (p 1)^2 + (p 2)^2 := norm_sq_point3 p
    have h_t2 : t^2 = (p 0)^2 + (p 1)^2 + (p 2)^2 := by
      rw [ht_def, h_norm_sq]
    have h_t_sq_le : t^2 ≤ (p 0 / a)^2 := by
      have h : (p 0)^2 + (p 1)^2 + (p 2)^2 ≤ (p 0)^2 + (p 0 / a)^2 * R2 := by linarith
      have h2 : (p 0)^2 + (p 0 / a)^2 * R2 = (p 0 / a)^2 := by
        field_simp [ha_pos.ne'] <;> nlinarith [h_a2_R2]
      linarith
    have h_p0_div_a_nonneg : 0 ≤ p 0 / a := by positivity
    have h_t_le_p0_div_a : t ≤ p 0 / a := by
      have h11 : 0 ≤ t := by positivity
      nlinarith [h_t_sq_le]
    have h_t_le_one : t ≤ 1 := by
      have h5 : p 0 / a ≤ 1 := by
        have h6 : p 0 ≤ a := hx_le
        have h7 : 0 < a := ha_pos
        calc p 0 / a ≤ a / a := by gcongr
          _ = 1 := by field_simp [h7.ne']
      linarith [h_t_le_p0_div_a]
    by_cases h_t1 : t < 1
    · let u : Point 3 := (1 / t) • p
      have hu_norm : ‖u‖ = 1 := by
        have h1 : ‖u‖ = |1 / t| * ‖p‖ := norm_smul (1 / t) p
        rw [h1]
        have h2 : |1 / t| = 1 / t := by
          have h3 : 0 < 1 / t := by positivity
          rw [abs_of_pos h3]
        rw [h2, ht_def]
        have h3 : (1 / t) * t = 1 := by field_simp [ht_pos.ne'] <;> ring
        exact h3
      have hu_sphere : u ∈ unitSphere 3 := by
        simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hu_norm
      have hu0 : u 0 ≥ a := by
        have h : u 0 = p 0 / t := by simp [u] <;> ring
        rw [h]
        have h13 : a * t ≤ p 0 := by
          have h14 : t ≤ p 0 / a := h_t_le_p0_div_a
          have h15 : 0 < a := ha_pos
          calc a * t ≤ a * (p 0 / a) := by gcongr
            _ = p 0 := by field_simp [h15.ne'] <;> ring
        have h16 : 0 < t := ht_pos
        calc a = (a * t) / t := by field_simp [h16.ne'] <;> ring
          _ ≤ (p 0) / t := by gcongr
      have h_dist_sq : dist u northPole ^2 = 2 - 2 * u 0 := dist_northPole_sq hu_sphere
      have h6 : 2 - 2 * u 0 ≤ r^2 := by
        have h7 : u 0 ≥ a := hu0
        have h8 : 2 - 2 * u 0 ≤ 2 - 2 * a := by gcongr
        have h9 : 2 - 2 * a = r^2 := by rw [ha_def] <;> ring
        linarith
      have h_dist : dist u northPole ≤ r := by
        have h10 : 0 ≤ dist u northPole := by positivity
        have h11 : dist u northPole ^2 ≤ r^2 := by
          rw [h_dist_sq]; exact h6
        nlinarith [hr]
      have hu_cap : u ∈ cap_set := ⟨hu_sphere, h_dist⟩
      have h_eq : t • u = p := by
        rw [show u = (1 / t) • p from rfl]
        rw [smul_smul]
        have h9 : t * (1 / t) = 1 := by field_simp [ht_pos.ne'] <;> ring
        rw [h9, one_smul]
      have h_in_sector : p ∈ sector := by
        exact ⟨t, ⟨ht_pos, h_t1⟩, u, hu_cap, h_eq⟩
      exact Or.inl h_in_sector
    · have h_t_eq : t = 1 := by linarith
      have h_p_sphere : p ∈ unitSphere 3 := by
        have h9 : ‖p‖ = t := by rfl
        simpa [unitSphere, Metric.mem_sphere, dist_zero_right, h9, h_t_eq] using rfl
      have h_in_null : p ∈ null_set := by
        simp [null_set, h_p_sphere]
      exact Or.inr h_in_null

end

end Kakeya.CV
