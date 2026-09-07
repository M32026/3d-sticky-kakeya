import MyLeanRepo.Kakeya.CV.HausdorffMeasureSphere.CapBounds.Subset
import MyLeanRepo.Kakeya.CV.HausdorffMeasureSphere.Cone


open MeasureTheory Metric Set Filter
open scoped ENNReal Pointwise

namespace Kakeya.CV

noncomputable section

-- ======================================================================
-- Sector and cap bounds
-- ======================================================================

/-- Bounds on toSphere of a cap: πR²a ≤ toSphere(cap) ≤ πR²/a²,
where a = 1-r²/2, R² = r²-r⁴/4. -/
lemma toSphere_cap_bounds (r : ℝ) (hr : 0 < r) (hr2 : r < Real.sqrt 2) :
    let a := 1 - r^2 / 2
    let R2 := r^2 - r^4 / 4
    ENNReal.ofReal (Real.pi * R2 * a) ≤
      (volume : Measure (Point 3)).toSphere (Subtype.val ⁻¹' (sphereCap northPole r)) ∧
    (volume : Measure (Point 3)).toSphere (Subtype.val ⁻¹' (sphereCap northPole r)) ≤
      ENNReal.ofReal (Real.pi * R2 / a^2) := by
  set a : ℝ := 1 - r^2 / 2 with ha_def
  set R2 : ℝ := r^2 - r^4 / 4 with hR2_def
  have ha_pos : 0 < a := by
    have h1 : r^2 < 2 := by
      have h2 : 0 ≤ r := by linarith
      have h3 : r^2 < (Real.sqrt 2)^2 := by gcongr
      have h4 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
      rw [h4] at h3; exact h3
    nlinarith
  have hR2_nonneg : 0 ≤ R2 := by nlinarith
  have h_a2_R2 : a^2 + R2 = 1 := by nlinarith
  let cap_set : Set (Point 3) := sphereCap northPole r
  let sector : Set (Point 3) := Set.image2 (· • ·) (Set.Ioo (0 : ℝ) 1) cap_set
  let cone_low : Set (Point 3) := {p | 0 ≤ p 0 ∧ p 0 ≤ a ∧ (p 1)^2 + (p 2)^2 ≤ (p 0 / a)^2 * R2}
  let null_set : Set (Point 3) := unitSphere 3 ∪ {0}
  -- Sphere has measure zero
  have h_sphere_zero : volume (unitSphere 3) = 0 := by
    have h5 : volume (sphere (0 : Point 3) 1) = 0 :=
      MeasureTheory.Measure.addHaar_sphere volume 0 1
    have h6 : unitSphere 3 = sphere (0 : Point 3) 1 := by
      ext x; simp [unitSphere, sphere, dist_zero_right]
    rw [h6]; exact h5
  have h_null_zero : volume null_set = 0 := by
    have h_disj : Disjoint (unitSphere 3) ({0} : Set (Point 3)) := by
      simp [unitSphere] <;> norm_num
    have h7 : volume null_set = volume (unitSphere 3) + volume ({0} : Set (Point 3)) := by
      rw [measure_union h_disj (by simp)] <;> rfl
    rw [h7, h_sphere_zero] <;> simp
  -- Use helper lemma for cone_low ⊆ sector ∪ null_set
  have h_low_cover : cone_low ⊆ sector ∪ null_set :=
    cap_cone_low_subset r hr hr2 a R2 ha_pos hR2_nonneg h_a2_R2 ha_def hR2_def
  have h_vol_low : volume cone_low ≤ volume sector := by
    have h_cover : cone_low ⊆ sector ∪ null_set := h_low_cover
    have h_le : volume cone_low ≤ volume (sector ∪ null_set) := measure_mono h_cover
    have h_union : volume (sector ∪ null_set) = volume sector := by
      have h_null : volume null_set = 0 := h_null_zero
      have h : volume (sector ∪ null_set) ≤ volume sector + volume null_set := measure_union_le _ _
      have h2 : volume sector ≤ volume (sector ∪ null_set) := by
        apply measure_mono; simp
      rw [h_null] at h
      simp at h
      exact le_antisymm h h2
    rw [h_union] at h_le
    exact h_le
  -- Upper bound
  let cone_high : Set (Point 3) := {p | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ (p 1)^2 + (p 2)^2 ≤ (p 0 / a)^2 * R2}
  have h_high_sub : sector ⊆ cone_high := by
    intro p hp
    rcases hp with ⟨t, ht_mem, u, hu_cap, rfl⟩
    have ht_pos : 0 < t := ht_mem.1
    have ht_lt_one : t < 1 := ht_mem.2
    have hux : u 0 ≥ a := by
      have h1 : u ∈ cap_set := hu_cap
      have h2 : dist u northPole ≤ r := h1.2
      have h3 : dist u northPole ^2 = 2 - 2 * u 0 := dist_northPole_sq h1.1
      have h4 : dist u northPole ^2 ≤ r^2 := by
        have h5 : 0 ≤ dist u northPole := by positivity
        have h6 : 0 ≤ r := by linarith
        nlinarith
      rw [h3] at h4
      have h7 : 2 - 2 * a = r^2 := by rw [ha_def] <;> ring
      nlinarith
    have hux_le_one : u 0 ≤ 1 := by
      have h1 : (u 0)^2 + (u 1)^2 + (u 2)^2 = 1 := sphere_eq_sq_sum u hu_cap.1
      nlinarith
    have hux_pos : 0 ≤ u 0 := by linarith [hux, ha_pos]
    have hpx_pos : 0 ≤ t * u 0 := by positivity
    have hpx_le_one : t * u 0 ≤ 1 := by
      have h : t * u 0 ≤ t * 1 := mul_le_mul_of_nonneg_left hux_le_one ht_pos.le
      have h2 : t * 1 ≤ 1 := by linarith
      linarith
    have h6 : (u 1)^2 + (u 2)^2 ≤ (u 0 / a)^2 * R2 := by
      have h4 : (u 1)^2 + (u 2)^2 = 1 - (u 0)^2 := by
        have h5 := sphere_eq_sq_sum u hu_cap.1
        nlinarith
      have ha2_pos : 0 < a^2 := by positivity
      have h_ineq : a^2 * ((u 1)^2 + (u 2)^2) ≤ (u 0)^2 * R2 := by
        rw [h4]
        have h2 : a^2 ≤ (u 0)^2 := by nlinarith [ha_pos]
        nlinarith [h_a2_R2]
      have h_final : (u 1)^2 + (u 2)^2 ≤ ((u 0)^2 / a^2) * R2 := by
        calc
          (u 1)^2 + (u 2)^2
            = (a^2 * ((u 1)^2 + (u 2)^2)) / a^2 := by field_simp [ha2_pos.ne'] <;> ring
          _ ≤ ((u 0)^2 * R2) / a^2 := by gcongr
          _ = ((u 0)^2 / a^2) * R2 := by ring
      have h_eq2 : ((u 0)^2 / a^2) * R2 = ((u 0 / a)^2) * R2 := by
        field_simp [ha_pos.ne'] <;> ring
      rw [h_eq2] at h_final
      exact h_final
    have hyz : (t * u 1)^2 + (t * u 2)^2 ≤ ((t * u 0) / a)^2 * R2 := by
      calc
        (t * u 1)^2 + (t * u 2)^2 = t^2 * ((u 1)^2 + (u 2)^2) := by ring
        _ ≤ t^2 * ((u 0 / a)^2 * R2) := by gcongr
        _ = ((t * u 0) / a)^2 * R2 := by ring
    exact ⟨hpx_pos, hpx_le_one, hyz⟩
  have hR2_sqrt : (Real.sqrt R2)^2 = R2 := Real.sq_sqrt hR2_nonneg
  have h_vol_low_eq : volume cone_low = ENNReal.ofReal (Real.pi * R2 * a / 3) := by
    have h := cone_volume_exact a (Real.sqrt R2) ha_pos (by positivity)
    simpa [hR2_sqrt] using h
  have hR2' : (Real.sqrt R2 / a)^2 = R2 / a^2 := by
    have hpos : 0 ≤ R2 := hR2_nonneg
    field_simp [ha_pos.ne'] <;> nlinarith [Real.sq_sqrt hpos]
  have h_cone_high_eq : cone_high =
      {p : Point 3 | 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ (p 1)^2 + (p 2)^2 ≤ (p 0 / (1 : ℝ))^2 * (Real.sqrt R2 / a)^2} := by
    ext p
    simp only [cone_high, Set.mem_setOf_eq]
    have h_eq3 : (p 0 / a)^2 * R2 = (p 0 / (1 : ℝ))^2 * (Real.sqrt R2 / a)^2 := by
      rw [hR2'] <;> ring_nf
    rw [h_eq3]
  have h_vol_high_eq : volume cone_high = ENNReal.ofReal (Real.pi * R2 / (3 * a^2)) := by
    rw [h_cone_high_eq]
    have h := cone_volume_exact (1 : ℝ) (Real.sqrt R2 / a) (by norm_num) (by positivity)
    have h10 : Real.pi * (Real.sqrt R2 / a)^2 * (1 : ℝ) / 3 = Real.pi * R2 / (3 * a^2) := by
      rw [hR2'] <;> ring_nf
    rw [h, h10]
  have h1 : volume sector ≤ volume cone_high := measure_mono h_high_sub
  -- Measurability
  have h_cap_set_meas : MeasurableSet cap_set := by
    have h1 : IsClosed (unitSphere 3) := by
      simpa [unitSphere] using (isClosed_sphere : IsClosed (sphere (0 : Point 3) 1))
    have h2 : IsClosed (closedBall northPole r) := isClosed_closedBall
    have h3 : IsClosed cap_set := by simpa [cap_set, sphereCap] using h1.inter h2
    exact h3.measurableSet
  let s_cap : Set (sphere (0 : Point 3) 1) :=
    (fun (x : sphere (0 : Point 3) 1) => (x : Point 3)) ⁻¹' cap_set
  have h_val_meas : Measurable (fun (x : sphere (0 : Point 3) 1) => (x : Point 3)) :=
    measurable_subtype_coe
  have h_cap_meas : MeasurableSet s_cap :=
    h_cap_set_meas.preimage h_val_meas
  have h_img : (fun (x : sphere (0 : Point 3) 1) => (x : Point 3)) '' s_cap = cap_set := by
    ext x
    simp only [s_cap, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      have h_x_sphere : x ∈ sphere (0 : Point 3) 1 := by
        have h2 : x ∈ unitSphere 3 := hx.1
        simpa [unitSphere, sphere, dist_zero_right] using h2
      exact ⟨⟨x, h_x_sphere⟩, hx, rfl⟩
  have h_toSphere : (volume : Measure (Point 3)).toSphere s_cap =
      ENNReal.ofReal 3 * volume sector := by
    rw [MeasureTheory.Measure.toSphere_apply' volume h_cap_meas]
    have h_img2 : Subtype.val '' s_cap = cap_set := by exact h_img
    rw [h_img2]
    have h_finrank : Module.finrank ℝ (Point 3) = 3 := by
      exact finrank_euclideanSpace_fin
    have h_finrank' : (↑(Module.finrank ℝ (Point 3)) : ENNReal) = ENNReal.ofReal 3 := by
      rw [h_finrank] <;> norm_num
    rw [h_finrank']
    have h_set_eq : ((Ioo (0 : ℝ) 1) • cap_set) = sector := by
      ext z
      simp [sector, Set.mem_image2]
      <;> rfl
    rw [h_set_eq]
    <;> norm_num
  have h8 : ENNReal.ofReal 3 * ENNReal.ofReal (Real.pi * R2 * a / 3) = ENNReal.ofReal (Real.pi * R2 * a) := by
    rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 3 by norm_num)] <;> ring_nf <;> norm_num <;> ring
  have h9 : ENNReal.ofReal 3 * ENNReal.ofReal (Real.pi * R2 / (3 * a^2)) = ENNReal.ofReal (Real.pi * R2 / a^2) := by
    rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 3 by norm_num)] <;> ring_nf <;> norm_num <;> ring
  have h_main : ENNReal.ofReal (Real.pi * R2 * a) ≤
      (volume : Measure (Point 3)).toSphere s_cap ∧
    (volume : Measure (Point 3)).toSphere s_cap ≤
      ENNReal.ofReal (Real.pi * R2 / a^2) := by
    rw [h_toSphere]
    constructor
    · calc
        ENNReal.ofReal (Real.pi * R2 * a)
          = ENNReal.ofReal 3 * volume cone_low := by rw [h_vol_low_eq, h8]
        _ ≤ ENNReal.ofReal 3 * volume sector := by gcongr
    · calc
        ENNReal.ofReal 3 * volume sector
          ≤ ENNReal.ofReal 3 * volume cone_high := by gcongr
        _ = ENNReal.ofReal (Real.pi * R2 / a^2) := by rw [h_vol_high_eq, h9]
  simpa [ha_def, hR2_def] using h_main

end

end Kakeya.CV
