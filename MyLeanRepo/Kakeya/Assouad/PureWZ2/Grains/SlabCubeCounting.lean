import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CubicalSlabLower
import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers
import MyLeanRepo.Kakeya.Assouad.LargeSlope.OrientedUnitSlabVolume

/-!
# Slab-ball volume and grid-cube counting

Geometric lemmas for the cube-counting approach to local AD bounds.

1. `slab_ball_volume`: volume of slab ∩ ball ≤ 8 * w * R²
2. `grid_cubes_contained_count`: number of L-grid cubes contained in E ≤ volume(E) / L³

These are used by the cube-counting route to bound projection covering numbers.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Volume of a slab intersected with a ball of radius R.

A slab `{x | |inner(x - center, v)| ≤ w}` intersected with `ball(0, R)`
has volume at most `8 * w * R²`.

Proof: scale by `1/R` to reduce to the unit-ball slab bound
`oriented_unit_slab_volume`.
-/
lemma slab_ball_volume
    {v : Point3} (hv_unit : ‖v‖ = 1)
    {center : Point3} {w R : ℝ} (hw_nonneg : 0 ≤ w) (hR_pos : 0 < R) :
    volume ({x : Point3 | |inner ℝ (x - center) v| ≤ w} ∩ Metric.closedBall 0 R) ≤
      ENNReal.ofReal (8 * w * R^2) := by
  let scaleCL : Point3 ≃L[ℝ] Point3 :=
    { toFun := fun x : Point3 => (1 / R : ℝ) • x
      invFun := fun y : Point3 => R • y
      left_inv := by
        intro x
        have h : R • ((1 / R : ℝ) • x) = x := by
          rw [smul_smul]
          have h2 : R * (1 / R : ℝ) = 1 := by field_simp [hR_pos.ne'] <;> ring
          rw [h2, one_smul]
        exact h
      right_inv := by
        intro y
        have h : (1 / R : ℝ) • (R • y) = y := by
          rw [smul_smul]
          have h2 : (1 / R : ℝ) * R = 1 := by field_simp [hR_pos.ne'] <;> ring
          rw [h2, one_smul]
        exact h
      map_add' := by
        intro x y
        simp [add_smul]
        <;> rfl
      map_smul' := by
        intro c x
        have h : (1 / R : ℝ) • (c • x) = c • ((1 / R : ℝ) • x) := by
          rw [smul_smul, smul_smul]
          <;> ring
        exact h }
  let E : Set Point3 :=
    {x | |inner ℝ (x - center) v| ≤ w} ∩ Metric.closedBall 0 R
  let center' : Point3 := scaleCL center
  let w' : ℝ := w / R
  have hw'_nonneg : 0 ≤ w' := by positivity
  have h_image : scaleCL '' E = orientedUnitSlab center' v w' := by
    ext y
    simp only [Set.mem_image, orientedUnitSlab, Set.mem_inter_iff, Set.mem_setOf_eq,
      Kakeya.DeltaTube.unitBall]
    constructor
    · rintro ⟨x, ⟨hx_slab, hx_ball⟩, rfl⟩
      have h1 : |inner ℝ (x - center) v| ≤ w := hx_slab
      have h_scaleCL_x : inner ℝ (scaleCL x) v = (1 / R) * inner ℝ x v := by
        simp [scaleCL, inner_smul_left] <;> ring
      have h_center'_v : inner ℝ center' v = (1 / R) * inner ℝ center v := by
        simp [center', scaleCL, inner_smul_left] <;> ring
      have h2 : inner ℝ (scaleCL x - center') v = (1 / R) * inner ℝ (x - center) v := by
        rw [inner_sub_left, h_scaleCL_x, inner_sub_left, h_center'_v] <;> ring
      have h_pos1R : 0 < (1 / R : ℝ) := by positivity
      have h3 : |inner ℝ (scaleCL x - center') v| ≤ w' := by
        rw [h2]
        have h4 : |(1 / R : ℝ) * inner ℝ (x - center) v| = (1 / R) * |inner ℝ (x - center) v| := by
          rw [abs_mul, abs_of_pos h_pos1R]
        rw [h4]
        have h12 : (1 / R) * |inner ℝ (x - center) v| ≤ (1 / R) * w :=
          mul_le_mul_of_nonneg_left h1 h_pos1R.le
        have h13 : (1 / R) * w = w / R := by field_simp [hR_pos.ne'] <;> ring
        rw [h13] at h12
        exact h12
      have h5 : ‖scaleCL x‖ ≤ 1 := by
        have h6 : ‖scaleCL x‖ = |(1 / R : ℝ)| * ‖x‖ := by
          have h61 : scaleCL x = (1 / R : ℝ) • x := by rfl
          rw [h61]
          exact norm_smul (1 / R : ℝ) x
        have h7 : |(1 / R : ℝ)| = 1 / R := by
          rw [abs_of_pos h_pos1R]
        rw [h6, h7]
        have h8 : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall] using hx_ball
        have h9 : (1 / R) * ‖x‖ ≤ (1 / R) * R := by
          exact mul_le_mul_of_nonneg_left h8 h_pos1R.le
        have h10 : (1 / R) * R = 1 := by field_simp [hR_pos.ne'] <;> ring
        rw [h10] at h9
        exact h9
      exact ⟨by simpa [Metric.mem_closedBall] using h5, h3⟩
    · rintro ⟨h_ball, h3⟩
      let x : Point3 := R • y
      have hfx : scaleCL x = y := by
        simp [x, scaleCL, smul_smul]
        <;> field_simp [hR_pos.ne'] <;> simp
      have h4 : ‖x‖ ≤ R := by
        have h5 : ‖x‖ = R * ‖y‖ := by
          simp [x, norm_smul, Real.norm_of_nonneg hR_pos.le]
        rw [h5]
        have h6 : ‖y‖ ≤ 1 := by simpa [Metric.mem_closedBall] using h_ball
        have h7 : R * ‖y‖ ≤ R * 1 := by exact mul_le_mul_of_nonneg_left h6 hR_pos.le
        linarith
      have h_center' : inner ℝ center' v = (1 / R) * inner ℝ center v := by
        simp [center', scaleCL, inner_smul_left] <;> ring
      have hx : inner ℝ x v = R * inner ℝ y v := by
        simp [x, inner_smul_left] <;> ring
      have h8 : inner ℝ (x - center) v = R * inner ℝ (y - center') v := by
        have h_rhs : R * inner ℝ (y - center') v = R * inner ℝ y v - inner ℝ center v := by
          rw [inner_sub_left, h_center']
          have h : R * (inner ℝ y v - (1 / R) * inner ℝ center v) =
              R * inner ℝ y v - inner ℝ center v := by
            field_simp [hR_pos.ne'] <;> ring
          exact h
        have h_lhs : inner ℝ (x - center) v = R * inner ℝ y v - inner ℝ center v := by
          rw [inner_sub_left, hx] <;> ring
        rw [h_lhs, h_rhs]
      have h9 : |inner ℝ (x - center) v| = R * |inner ℝ (y - center') v| := by
        rw [h8, abs_mul, abs_of_nonneg hR_pos.le]
      have h10 : R * |inner ℝ (y - center') v| ≤ w := by
        have h101 : R * |inner ℝ (y - center') v| ≤ R * w' := by
          exact mul_le_mul_of_nonneg_left h3 hR_pos.le
        have h102 : R * w' = w := by
          dsimp only [w']
          field_simp [hR_pos.ne'] <;> ring
        rw [h102] at h101
        exact h101
      have h7 : |inner ℝ (x - center) v| ≤ w := by
        rw [h9]
        exact h10
      exact ⟨x, ⟨h7, by simpa [Metric.mem_closedBall] using h4⟩, hfx⟩
  have h_det : |LinearMap.det (scaleCL : Point3 →ₗ[ℝ] Point3)| = (1 / R) ^ 3 := by
    have h1 : (scaleCL : Point3 →ₗ[ℝ] Point3) = (1 / R : ℝ) • LinearMap.id := by
      ext x
      simp [scaleCL]
      <;> rfl
    rw [h1]
    have h_finrank : Module.finrank ℝ Point3 = 3 := by
      simpa [Point3] using rfl
    rw [LinearMap.det_smul, h_finrank, LinearMap.det_id]
    have h2 : |(1 / R : ℝ) ^ 3 * 1| = (1 / R) ^ 3 := by
      rw [mul_one, abs_of_pos] <;> positivity
    exact h2
  have h_vol_scale : volume (scaleCL '' E) =
      ENNReal.ofReal ((1 / R) ^ 3) * volume E := by
    rw [MeasureTheory.Measure.addHaar_image_continuousLinearEquiv volume scaleCL E, h_det]
    <;> rfl
  rw [h_image] at h_vol_scale
  have h_main : volume (orientedUnitSlab center' v w') ≤ ENNReal.ofReal (8 * w') :=
    oriented_unit_slab_volume center' v w' hv_unit hw'_nonneg
  have h : ENNReal.ofReal ((1 / R) ^ 3) * volume E ≤ ENNReal.ofReal (8 * w') :=
    h_vol_scale ▸ h_main
  have hR3_pos' : 0 < (1 / R) ^ 3 := by positivity
  have h_ne_top : ENNReal.ofReal ((1 / R) ^ 3) ≠ ⊤ := by
    simp [hR3_pos']
  have h_cancel : ENNReal.ofReal (R ^ 3) * ENNReal.ofReal ((1 / R) ^ 3) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have h : R ^ 3 * (1 / R) ^ 3 = 1 := by
      field_simp [hR_pos.ne'] <;> ring
    rw [h]
    <;> simp
  have h_mul : ENNReal.ofReal (R ^ 3) * (ENNReal.ofReal ((1 / R) ^ 3) * volume E) ≤
      ENNReal.ofReal (R ^ 3) * ENNReal.ofReal (8 * w') := by
    gcongr
  have h' : volume E ≤ ENNReal.ofReal (R ^ 3) * ENNReal.ofReal (8 * w') := by
    have h_eq : ENNReal.ofReal (R ^ 3) * (ENNReal.ofReal ((1 / R) ^ 3) * volume E) = volume E := by
      rw [← mul_assoc, h_cancel, one_mul]
    rw [h_eq] at h_mul
    exact h_mul
  have h_final : ENNReal.ofReal (R ^ 3) * ENNReal.ofReal (8 * w') =
      ENNReal.ofReal (8 * w * R ^ 2) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have h : R ^ 3 * (8 * (w / R)) = 8 * w * R ^ 2 := by
      field_simp [hR_pos.ne'] <;> ring
    rw [h]
  rw [h_final] at h'
  exact h'

/-- Count grid cubes contained in a measurable set.

If `cells` is a finite set of grid indices and every corresponding cube
is contained in `E`, then `cells.card * L^3 ≤ volume E`.
-/
lemma grid_cubes_contained_count
    {L : ℝ} (hL_pos : 0 < L)
    {E : Set Point3} (hE_meas : MeasurableSet E)
    {cells : Finset (ℤ × ℤ × ℤ)}
    (h_sub : ∀ cell ∈ cells, wz1PaperGridCube L cell ⊆ E) :
    (cells.card : ENNReal) * ENNReal.ofReal (L^3) ≤ volume E := by
  have h_disj : ∀ c1 ∈ cells, ∀ c2 ∈ cells, c1 ≠ c2 →
      Disjoint (wz1PaperGridCube L c1) (wz1PaperGridCube L c2) := by
    intro c1 _ c2 _ hne
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have h1 : wz1PaperGridIndex L x = c1 := by simpa [mem_wz1PaperGridCube] using hx1
    have h2 : wz1PaperGridIndex L x = c2 := by simpa [mem_wz1PaperGridCube] using hx2
    have h_eq : c1 = c2 := h1.symm.trans h2
    exact hne h_eq
  have h_union : (⋃ cell ∈ cells, wz1PaperGridCube L cell) ⊆ E := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨cell, hcell, hxcube⟩
    exact h_sub cell hcell hxcube
  have h_meas : ∀ cell ∈ cells, MeasurableSet (wz1PaperGridCube L cell) :=
    fun cell _ => wz1PaperGridCube_measurable cell
  have h_vol_union : volume (⋃ cell ∈ cells, wz1PaperGridCube L cell) =
      (cells.card : ENNReal) * ENNReal.ofReal (L^3) := by
    rw [MeasureTheory.measure_biUnion_finset (s := cells) (f := fun c => wz1PaperGridCube L c)
        h_disj h_meas]
    rw [Finset.sum_congr rfl (fun cell _ => wz1PaperGridCube_volume_any hL_pos cell)]
    simp [Finset.sum_const]
  rw [← h_vol_union]
  exact measure_mono h_union

end Kakeya.Assouad.PureWZ2
