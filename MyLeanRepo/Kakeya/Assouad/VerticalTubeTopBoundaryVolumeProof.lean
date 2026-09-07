import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.LargeSlope.Step4WitnessMassBounds
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Assouad.WZ1.HorizontalChartNormalization.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Vertical tube top-boundary volume bound

Proves `VerticalTubeTopBoundaryVolumeStatement` by adapting the geometric
core of `tube_slab_volume_upper`. The restrictive conditions on slab
thickness are removed; the final numeric bound uses `8 * Real.pi < 100`.
-/

noncomputable section

open Metric Set Finset MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- General tube-slab volume upper bound with an explicit axial speed. -/
lemma tube_slab_volume_upper_of_speed
    {delta a b : ℝ} (hdelta : 0 < delta) (hab : a < b)
    {T : Kakeya.DeltaTube delta}
    {speed : ℝ} (hspeed : 0 < speed)
    (hvert : speed ≤ |T.direction (2 : Fin 3)|) :
    MeasureTheory.volume (T.carrier ∩ horizontalSlab a b) ≤
    ENNReal.ofReal
      (Real.pi * delta^2 *
        ((b - a + 2 * delta) / speed + 2 * delta)) := by
  let e3 : Point3 := EuclideanSpace.single 2 (1 : ℝ)
  let d := T.direction
  let b0 := T.base
  let K : Submodule ℝ Point3 := (Submodule.span ℝ {d - e3})ᗮ
  let A : Point3 ≃ₗᵢ[ℝ] Point3 := K.reflection

  have he3_norm : ‖e3‖ = 1 := by
    have h : ‖e3‖ ^ 2 = ∑ i : Fin 3, (e3 i)^2 :=
      EuclideanSpace.real_norm_sq_eq e3
    have h2 : ∑ i : Fin 3, (e3 i)^2 = 1 := by
      have h_univ3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
      rw [h_univ3]
      simp [e3, Finset.sum_insert, Finset.sum_singleton,
        EuclideanSpace.single_apply] <;> norm_num
    have h3 : ‖e3‖ ^ 2 = 1 := by rw [h, h2]
    have h4 : 0 ≤ ‖e3‖ := norm_nonneg e3
    nlinarith

  have hA_dir : A d = e3 :=
    Submodule.reflection_sub (T.direction_unit.trans he3_norm.symm)

  let c := A b0
  let c2 : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 (fun i : Fin 2 => c (Fin.castSucc i))
  let d2 := d (2 : Fin 3)
  have h_d2_ne_zero : d2 ≠ 0 := by
    intro h
    have hvert' : speed ≤ |d2| := by simpa [d2, d] using hvert
    rw [h] at hvert'
    simp at hvert'
    linarith

  let S := T.carrier ∩ horizontalSlab a b

  have h_seg_compact : IsCompact (unitSegment b0 d) :=
    isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))

  have hT_meas : MeasurableSet T.carrier := by
    have h_closed : IsClosed (Metric.cthickening delta (unitSegment b0 d)) :=
      Metric.isClosed_cthickening
    have h_eq : T.carrier = Metric.cthickening delta (unitSegment b0 d) := by
      rfl
    rw [h_eq]
    exact h_closed.measurableSet

  have hSlab_meas : MeasurableSet (horizontalSlab a b) := by
    have h2 : Continuous (fun x : Point3 => x (2 : Fin 3)) := by fun_prop
    have h_eq :
        horizontalSlab a b =
          (fun x : Point3 => x (2 : Fin 3)) ⁻¹' Set.Icc a b := by
      ext x
      simp [horizontalSlab]
    rw [h_eq]
    exact isClosed_Icc.measurableSet.preimage h2.measurable

  have hS_meas : MeasurableSet S := hT_meas.inter hSlab_meas

  let A_meas : Point3 ≃ᵐ Point3 := A.toMeasurableEquiv
  let S' := A '' S
  have h_preimg : A ⁻¹' S' = S := Set.preimage_image_eq S A.injective
  have h_vol : volume S = volume S' := by
    have h : volume (A ⁻¹' S') = volume S' :=
      A.measurePreserving.measure_preimage_emb A_meas.measurableEmbedding S'
    rw [h_preimg] at h
    exact h

  set tlo :=
    if 0 < d2 then
      (a - delta - b0 (2 : Fin 3)) / d2
    else
      (b + delta - b0 (2 : Fin 3)) / d2 with htlo
  set thi :=
    if 0 < d2 then
      (b + delta - b0 (2 : Fin 3)) / d2
    else
      (a - delta - b0 (2 : Fin 3)) / d2 with hthi
  set zlo := c (2 : Fin 3) + tlo - delta with hzlo
  set zhi := c (2 : Fin 3) + thi + delta with hzhi

  have h_t_bounds : ∀ (p : Point3), p ∈ S →
      ∃ (t : ℝ) (v : Point3),
        ‖v‖ ≤ delta ∧ p = b0 + t • d + v ∧ tlo ≤ t ∧ t ≤ thi := by
    intro p hp
    rcases tube_carrier_witness hdelta hp.1 with ⟨t, _ht, hdist⟩
    let v := p - (b0 + t • d)
    have hv_norm : ‖v‖ ≤ delta := by
      have h : dist p (b0 + t • d) ≤ delta := hdist
      simpa [dist_eq_norm] using h
    have hv_eq : p = b0 + t • d + v := by
      simp [v] <;> abel
    have h_p2 : a ≤ p (2 : Fin 3) ∧ p (2 : Fin 3) ≤ b := hp.2
    have h_v2 : |v (2 : Fin 3)| ≤ delta := by
      have h : |v (2 : Fin 3)| ≤ ‖v‖ := coord_abs_le_norm v 2
      linarith
    have h_lower : a - delta ≤ b0 (2 : Fin 3) + t * d2 := by
      have h_eq :
          b0 (2 : Fin 3) + t * d2 =
            p (2 : Fin 3) - v (2 : Fin 3) := by
        simp [v, d2] <;> ring
      rw [h_eq]
      linarith [abs_le.mp h_v2, h_p2.1]
    have h_upper : b0 (2 : Fin 3) + t * d2 ≤ b + delta := by
      have h_eq :
          b0 (2 : Fin 3) + t * d2 =
            p (2 : Fin 3) - v (2 : Fin 3) := by
        simp [v, d2] <;> ring
      rw [h_eq]
      linarith [abs_le.mp h_v2, h_p2.2]
    by_cases hpos : 0 < d2
    · have h_tlo' : tlo ≤ t := by
        rw [htlo, if_pos hpos]
        have h : a - delta - b0 (2 : Fin 3) ≤ t * d2 := by linarith
        have h' :
            (a - delta - b0 (2 : Fin 3)) / d2 ≤ (t * d2) / d2 := by
          gcongr
        have h'' : (t * d2) / d2 = t := by
          field_simp [hpos.ne'] <;> ring
        rw [h''] at h'
        exact h'
      have h_thi' : t ≤ thi := by
        rw [hthi, if_pos hpos]
        have h : t * d2 ≤ b + delta - b0 (2 : Fin 3) := by linarith
        have h' :
            (t * d2) / d2 ≤ (b + delta - b0 (2 : Fin 3)) / d2 := by
          gcongr
        have h'' : (t * d2) / d2 = t := by
          field_simp [hpos.ne'] <;> ring
        rw [h''] at h'
        exact h'
      exact ⟨t, v, hv_norm, hv_eq, h_tlo', h_thi'⟩
    · have hneg : d2 < 0 := by
        by_contra h
        exact h_d2_ne_zero (by linarith)
      have h_tlo' : tlo ≤ t := by
        rw [htlo, if_neg (show ¬(0 < d2) from by linarith)]
        have h9 : b + delta - b0 (2 : Fin 3) - t * d2 ≥ 0 := by
          linarith
        have h10 : (b + delta - b0 (2 : Fin 3)) / d2 - t ≤ 0 := by
          have h11 :
              (b + delta - b0 (2 : Fin 3)) / d2 - t =
                (b + delta - b0 (2 : Fin 3) - t * d2) / d2 := by
            field_simp [hneg.ne] <;> ring
          rw [h11]
          apply div_nonpos_of_nonneg_of_nonpos h9 <;> linarith
        linarith
      have h_thi' : t ≤ thi := by
        rw [hthi, if_neg (show ¬(0 < d2) from by linarith)]
        have h9 : t * d2 - (a - delta - b0 (2 : Fin 3)) ≥ 0 := by
          linarith
        have h10 : t - (a - delta - b0 (2 : Fin 3)) / d2 ≤ 0 := by
          have h11 :
              t - (a - delta - b0 (2 : Fin 3)) / d2 =
                (t * d2 - (a - delta - b0 (2 : Fin 3))) / d2 := by
            field_simp [hneg.ne] <;> ring
          rw [h11]
          apply div_nonpos_of_nonneg_of_nonpos h9 <;> linarith
        linarith
      exact ⟨t, v, hv_norm, hv_eq, h_tlo', h_thi'⟩

  have h_thi_tlo_nonneg : 0 ≤ thi - tlo := by
    by_cases hpos : 0 < d2
    · rw [htlo, hthi, if_pos hpos, if_pos hpos]
      have h :
          (b + delta - b0 (2 : Fin 3)) / d2 -
              (a - delta - b0 (2 : Fin 3)) / d2 =
            (b - a + 2 * delta) / d2 := by
        field_simp [hpos.ne'] <;> ring
      rw [h]
      apply div_nonneg <;> linarith
    · have hneg : d2 < 0 := by
        by_contra h
        exact h_d2_ne_zero (by linarith)
      rw [htlo, hthi, if_neg (show ¬(0 < d2) from by linarith),
        if_neg (show ¬(0 < d2) from by linarith)]
      have h_abs : |d2| = -d2 := abs_of_neg hneg
      have h2 :
          (a - delta - b0 (2 : Fin 3)) / d2 -
              (b + delta - b0 (2 : Fin 3)) / d2 =
            (b - a + 2 * delta) / |d2| := by
        rw [h_abs]
        field_simp [hneg.ne] <;> ring
      rw [h2]
      apply div_nonneg <;> linarith

  have h_zlo_le_zhi : zlo ≤ zhi := by
    have h : zhi - zlo = thi - tlo + 2 * delta := by
      dsimp only [zlo, zhi]
      ring
    have h' : 0 ≤ thi - tlo := h_thi_tlo_nonneg
    have h'' : 0 ≤ zhi - zlo := by
      rw [h]
      linarith [hdelta]
    exact sub_nonneg.mp h''

  have h_height :
      zhi - zlo ≤
        (b - a + 2 * delta) / speed + 2 * delta := by
    have h_diff : zhi - zlo = thi - tlo + 2 * delta := by
      dsimp only [zlo, zhi]
      ring
    rw [h_diff]
    by_cases hpos : 0 < d2
    · have h1 : thi - tlo = (b - a + 2 * delta) / d2 := by
        rw [htlo, hthi, if_pos hpos, if_pos hpos]
        field_simp [hpos.ne'] <;> ring
      rw [h1]
      have hspeedD2 : speed ≤ d2 := by
        have hspeedAbs : speed ≤ |d2| := by
          simpa [d2, d] using hvert
        rwa [abs_of_pos hpos] at hspeedAbs
      have h3 : 1 / d2 ≤ 1 / speed := by
        gcongr
      have h5 : 0 ≤ b - a + 2 * delta := by linarith
      have h6 :
          (b - a + 2 * delta) / d2 ≤
            (b - a + 2 * delta) / speed := by
        calc
          (b - a + 2 * delta) / d2
              = (b - a + 2 * delta) * (1 / d2) := by ring
          _ ≤ (b - a + 2 * delta) * (1 / speed) := by gcongr
          _ = (b - a + 2 * delta) / speed := by ring
      linarith
    · have hneg : d2 < 0 := by
        by_contra h
        exact h_d2_ne_zero (by linarith)
      have h_abs : |d2| = -d2 := abs_of_neg hneg
      have h1 : thi - tlo = (b - a + 2 * delta) / |d2| := by
        rw [htlo, hthi, if_neg (show ¬(0 < d2) from by linarith),
          if_neg (show ¬(0 < d2) from by linarith), h_abs]
        field_simp [hneg.ne] <;> ring
      rw [h1]
      have h3 : 1 / |d2| ≤ 1 / speed := by
        gcongr
      have h4 : 0 ≤ b - a + 2 * delta := by linarith
      have h6 :
          (b - a + 2 * delta) / |d2| ≤
            (b - a + 2 * delta) / speed := by
        calc
          (b - a + 2 * delta) / |d2|
              = (b - a + 2 * delta) * (1 / |d2|) := by ring
          _ ≤ (b - a + 2 * delta) * (1 / speed) := by gcongr
          _ = (b - a + 2 * delta) / speed := by ring
      linarith

  let Cyl : Set Point3 := {p |
    dist (WithLp.toLp 2 (fun i : Fin 2 => p (Fin.castSucc i))) c2 ≤ delta ∧
    zlo ≤ p (2 : Fin 3) ∧ p (2 : Fin 3) ≤ zhi}

  have h_contain : S' ⊆ Cyl := by
    intro q hq
    rcases hq with ⟨p, hp, rfl⟩
    rcases h_t_bounds p hp with ⟨t, v, hv_norm, hv_eq, htlo, hthi⟩
    let w := A v
    have hw_norm : ‖w‖ ≤ delta := by
      have h : ‖w‖ = ‖v‖ := A.norm_map v
      rw [h]
      exact hv_norm
    have hq_eq : A p = c + t • e3 + w := by
      rw [hv_eq]
      simp [c, hA_dir, A.map_add, A.map_smul] <;> abel
    have h_xy :
        dist (WithLp.toLp 2 (fun i : Fin 2 => (A p) (Fin.castSucc i))) c2 ≤
          delta := by
      have h1 :
          (fun i : Fin 2 => (A p) (Fin.castSucc i)) -
              (fun i : Fin 2 => c (Fin.castSucc i)) =
            (fun i : Fin 2 => w (Fin.castSucc i)) := by
        funext i
        have h_ne_two : (Fin.castSucc i : Fin 3) ≠ 2 := by
          fin_cases i <;> simp [Fin.castSucc] <;> decide
        rw [hq_eq]
        simp [e3, EuclideanSpace.single_apply, h_ne_two] <;> ring
      have h2 :
          dist (WithLp.toLp 2 (fun i : Fin 2 => (A p) (Fin.castSucc i))) c2 =
            ‖(WithLp.toLp 2 (fun i : Fin 2 => w (Fin.castSucc i)))‖ := by
        have h_c2 :
            c2 = WithLp.toLp 2 (fun i : Fin 2 => c (Fin.castSucc i)) := by
          rfl
        rw [h_c2, dist_eq_norm]
        have h3 :
            (WithLp.toLp 2 (fun i : Fin 2 => (A p) (Fin.castSucc i))) -
                (WithLp.toLp 2 (fun i : Fin 2 => c (Fin.castSucc i))) =
              WithLp.toLp 2 (fun i : Fin 2 => w (Fin.castSucc i)) := by
          have h4 :
              (WithLp.toLp 2 (fun i : Fin 2 => (A p) (Fin.castSucc i))) -
                  (WithLp.toLp 2 (fun i : Fin 2 => c (Fin.castSucc i))) =
                WithLp.toLp 2
                  ((fun i : Fin 2 => (A p) (Fin.castSucc i)) -
                    (fun i : Fin 2 => c (Fin.castSucc i))) := by
            simpa [WithLp.toLp_sub] using rfl
          rw [h4, h1]
        rw [h3]
      rw [h2]
      have h5 :
          ‖(WithLp.toLp 2 (fun i : Fin 2 => w (Fin.castSucc i)))‖ ≤ ‖w‖ :=
        xy_proj_norm_le w
      linarith
    have h_z :
        zlo ≤ (A p) (2 : Fin 3) ∧ (A p) (2 : Fin 3) ≤ zhi := by
      have h3 :
          (A p) (2 : Fin 3) = c (2 : Fin 3) + t + w (2 : Fin 3) := by
        rw [hq_eq]
        simp [e3, EuclideanSpace.single_apply] <;> ring
      have h4 : |w (2 : Fin 3)| ≤ delta := by
        have h5 : |w (2 : Fin 3)| ≤ ‖w‖ := coord_abs_le_norm w 2
        linarith
      rw [h3, hzlo, hzhi]
      constructor <;> linarith [abs_le.mp h4]
    exact ⟨h_xy, h_z.1, h_z.2⟩

  have h_cyl_vol :
      volume Cyl = ENNReal.ofReal (Real.pi * delta^2 * (zhi - zlo)) :=
    step4_cylinder_volume c2 delta hdelta.le zlo zhi h_zlo_le_zhi

  have h9 : 0 ≤ Real.pi * delta^2 := by positivity
  have h_num :
      Real.pi * delta^2 * (zhi - zlo) ≤
        Real.pi * delta^2 *
          ((b - a + 2 * delta) / speed + 2 * delta) :=
    mul_le_mul_of_nonneg_left h_height h9

  calc
    volume S
        = volume S' := h_vol
    _ ≤ volume Cyl := measure_mono h_contain
    _ = ENNReal.ofReal (Real.pi * delta^2 * (zhi - zlo)) := h_cyl_vol
    _ ≤ ENNReal.ofReal
        (Real.pi * delta^2 *
          ((b - a + 2 * delta) / speed + 2 * delta)) :=
      ENNReal.ofReal_mono h_num

/--
General tube-slab volume upper bound without restrictive thickness conditions.

The intersection of a vertical-chart `δ`-tube with a horizontal slab of width
`b - a` has volume at most `π * δ² * (2*(b-a) + 6*δ)`.
-/
lemma tube_slab_volume_upper_general
    {delta a b : ℝ} (hdelta : 0 < delta) (hab : a < b)
    {T : Kakeya.DeltaTube delta}
    (hvert : (1 / 2 : ℝ) ≤ |T.direction (2 : Fin 3)|) :
    MeasureTheory.volume (T.carrier ∩ horizontalSlab a b) ≤
    ENNReal.ofReal (Real.pi * delta^2 * (2 * (b - a) + 6 * delta)) := by
  have h :=
    tube_slab_volume_upper_of_speed
      hdelta hab (speed := (1 / 2 : ℝ)) (by norm_num) hvert
  convert h using 1
  congr 2
  ring

/-- The closed coordinate slab used by the fixed-origin paper grid. -/
def coordinateSlab
    (coordinate : Fin 3) (a b : ℝ) : Set Point3 :=
  {point | a ≤ point coordinate ∧ point coordinate ≤ b}

/-- The explicit-speed tube-slab bound in any coordinate direction. -/
lemma tube_coordinate_slab_volume_upper_of_speed
    {delta a b : ℝ} (hdelta : 0 < delta) (hab : a < b)
    {T : Kakeya.DeltaTube delta}
    (coordinate : Fin 3)
    {speed : ℝ} (hspeed : 0 < speed)
    (hcoordinate : speed ≤ |T.direction coordinate|) :
    MeasureTheory.volume
        (T.carrier ∩ coordinateSlab coordinate a b) ≤
      ENNReal.ofReal
        (Real.pi * delta^2 *
          ((b - a + 2 * delta) / speed + 2 * delta)) := by
  let permutation : Equiv.Perm (Fin 3) :=
    Equiv.swap coordinate 2
  let isometry : Point3 ≃ₗᵢ[ℝ] Point3 :=
    LinearIsometryEquiv.piLpCongrLeft
      (2 : ENNReal) ℝ ℝ permutation
  let rotated := transportTube isometry T
  have hisometryApply :
      ∀ point : Point3, ∀ index : Fin 3,
        isometry point index = point (permutation index) := by
    intro point index
    simp [isometry, permutation,
      LinearIsometryEquiv.piLpCongrLeft_apply]
  have hswapTwo : permutation 2 = coordinate := by
    simp [permutation, Equiv.swap_apply_def]
  have hrotatedDirection :
      rotated.direction (2 : Fin 3) = T.direction coordinate := by
    dsimp only [rotated, transportTube]
    rw [hisometryApply, hswapTwo]
  have hslabImage :
      isometry '' coordinateSlab coordinate a b =
        horizontalSlab a b := by
    ext point
    constructor
    · rintro ⟨source, hsource, rfl⟩
      change a ≤ isometry source 2 ∧ isometry source 2 ≤ b
      rw [hisometryApply, hswapTwo]
      exact hsource
    · intro hpoint
      refine ⟨isometry.symm point, ?_, isometry.apply_symm_apply point⟩
      change
        a ≤ (isometry.symm point) coordinate ∧
          (isometry.symm point) coordinate ≤ b
      have hinvolutive :
          ∀ source : Point3, isometry (isometry source) = source := by
        intro source
        ext index
        rw [hisometryApply, hisometryApply]
        have hsymmPermutation :
            permutation.symm = permutation := by
          simp [permutation]
        have h :=
          permutation.symm_apply_apply index
        rw [hsymmPermutation] at h
        rw [h]
      have hsymm : isometry.symm point = isometry point := by
        apply isometry.injective
        rw [isometry.apply_symm_apply, hinvolutive]
      rw [hsymm, hisometryApply]
      have hswapCoordinate : permutation coordinate = 2 := by
        simp [permutation, Equiv.swap_apply_def]
      rw [hswapCoordinate]
      exact hpoint
  have hintersectionImage :
      isometry ''
          (T.carrier ∩ coordinateSlab coordinate a b) =
        rotated.carrier ∩ horizontalSlab a b := by
    rw [Set.image_inter isometry.injective,
      ← transportTube_carrier isometry T, hslabImage]
  have hvolume :
      volume
          (T.carrier ∩ coordinateSlab coordinate a b) =
        volume (rotated.carrier ∩ horizontalSlab a b) := by
    rw [← hintersectionImage, volume_image]
  rw [hvolume]
  apply tube_slab_volume_upper_of_speed hdelta hab hspeed
  simpa [hrotatedDirection] using hcoordinate

/--
The top-boundary cap of a vertical-chart tube has volume at most `100 * rho³`.
-/
lemma vertical_tube_top_boundary_volume :
    VerticalTubeTopBoundaryVolumeStatement := by
  intro rho hrho hrho_le T hvert
  have h_main :
      MeasureTheory.volume
          (T.carrier ∩ horizontalSlab 1 (1 + rho)) ≤
        ENNReal.ofReal
          (Real.pi * rho^2 * (2 * ((1 + rho) - 1) + 6 * rho)) :=
    tube_slab_volume_upper_general
      (delta := rho) (a := 1) (b := 1 + rho) hrho (by linarith) hvert
  have h_simp :
      Real.pi * rho^2 * (2 * ((1 + rho) - 1) + 6 * rho) =
        8 * Real.pi * rho^3 := by
    ring
  rw [h_simp] at h_main
  have h_bound : 8 * Real.pi * rho^3 ≤ 100 * rho^3 := by
    have h2 : 8 * Real.pi ≤ 100 := by linarith [Real.pi_lt_four]
    have h3 : 0 ≤ rho^3 := by positivity
    nlinarith
  exact h_main.trans (ENNReal.ofReal_mono h_bound)

end Kakeya.Assouad
