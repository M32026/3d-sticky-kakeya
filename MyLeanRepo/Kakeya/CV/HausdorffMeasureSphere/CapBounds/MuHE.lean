import MyLeanRepo.Kakeya.CV.HausdorffMeasureSphere.CapBounds.Basic

local notation "graphMap" => Kakeya.CV.northSphereGraphMap


open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace Kakeya.CV

noncomputable section

private lemma sphereCap_north_subset_graphMap_disk
    {r a R2 R : ℝ}
    (hr : 0 < r)
    (ha_pos : 0 < a)
    (ha_def : a = 1 - r^2 / 2)
    (hR2_eq : R^2 = R2)
    (h_a2 : a^2 + R2 = 1)
    (hR_nonneg : 0 ≤ R) :
    sphereCap northPole r ⊆
      graphMap '' closedBall (0 : Point 2) R := by
  intro p hp
  change p ∈ unitSphere 3 ∧ p ∈ closedBall northPole r at hp
  rcases hp with ⟨hp_sphere, hp_dist⟩
  have h_dist_le : dist p northPole ≤ r := by
    simpa only [mem_closedBall] using hp_dist
  have h_x_ge : a ≤ p 0 := by
    have hdist_sq : dist p northPole ^ 2 = 2 - 2 * p 0 :=
      dist_northPole_sq hp_sphere
    have hsq_le : dist p northPole ^ 2 ≤ r^2 := by
      gcongr
    have hidentity : 2 - 2 * a = r^2 := by
      rw [ha_def]
      ring
    rw [hdist_sq] at hsq_le
    linarith
  let q : Point 2 := mkPoint2 fun i : Fin 2 => p (Fin.succ i)
  have hq_norm_sq : ‖q‖^2 = (q 0)^2 + (q 1)^2 := norm_sq_point2 q
  have hq_coord_sq : (q 0)^2 + (q 1)^2 ≤ R2 := by
    have hcoords : (q 0)^2 + (q 1)^2 = (p 1)^2 + (p 2)^2 := by
      simp [q, mkPoint2_apply]
      <;> rfl
    rw [hcoords]
    have hsphere := sphere_eq_sq_sum p hp_sphere
    nlinarith [h_a2]
  have hq_in : q ∈ closedBall (0 : Point 2) R := by
    have hnorm_sq_le : ‖q‖^2 ≤ R^2 := by
      rw [hq_norm_sq, hR2_eq]
      exact hq_coord_sq
    have hnorm_le : ‖q‖ ≤ R := by
      have hnorm_nonneg : 0 ≤ ‖q‖ := norm_nonneg q
      nlinarith
    simpa only [mem_closedBall, dist_zero_right] using hnorm_le
  have hgraph : graphMap q = p := by
    ext i
    fin_cases i
    · have hcoords : (q 0)^2 + (q 1)^2 = (p 1)^2 + (p 2)^2 := by
        simp [q, mkPoint2_apply]
        <;> rfl
      have hsphere :
          (p 0)^2 + (p 1)^2 + (p 2)^2 = 1 :=
        sphere_eq_sq_sum p hp_sphere
      have hsqrt_arg : 1 - (q 0)^2 - (q 1)^2 = (p 0)^2 := by
        nlinarith
      have hp0_nonneg : 0 ≤ p 0 := by linarith
      have hsqrt :
          Real.sqrt (1 - (q 0)^2 - (q 1)^2) = p 0 := by
        rw [hsqrt_arg, Real.sqrt_sq hp0_nonneg]
      simpa [graphMap_apply0] using hsqrt
    · simpa [graphMap_apply1, q, mkPoint2_apply] using rfl
    · simpa [graphMap_apply2, q, mkPoint2_apply] using rfl
  exact ⟨q, hq_in, hgraph⟩

private lemma graphMap_disk_subset_sphereCap_north
    {r a R2 R : ℝ}
    (hr : 0 < r)
    (ha_pos : 0 < a)
    (ha_def : a = 1 - r^2 / 2)
    (hR2_eq : R^2 = R2)
    (h_a2 : a^2 + R2 = 1) :
    graphMap '' closedBall (0 : Point 2) R ⊆
      sphereCap northPole r := by
  intro p hp
  rcases hp with ⟨q, hq, rfl⟩
  have hq_norm_sq : ‖q‖^2 = (q 0)^2 + (q 1)^2 :=
    norm_sq_point2 q
  have hcoord_sq : (q 0)^2 + (q 1)^2 ≤ R2 := by
    have hnorm_le : ‖q‖ ≤ R := by
      simpa only [mem_closedBall, dist_zero_right] using hq
    have hnorm_sq_le : ‖q‖^2 ≤ R^2 := by gcongr
    rw [hq_norm_sq, hR2_eq] at hnorm_sq_le
    exact hnorm_sq_le
  have hsqrt_arg_nonneg : 0 ≤ 1 - (q 0)^2 - (q 1)^2 := by
    nlinarith
  have h_sphere : graphMap q ∈ unitSphere 3 := by
    have hsum :
        (graphMap q 0)^2 + (graphMap q 1)^2 +
            (graphMap q 2)^2 = 1 := by
      simp [graphMap_apply0, graphMap_apply1, graphMap_apply2,
        Real.sq_sqrt hsqrt_arg_nonneg]
      <;> ring
    have hnorm_sq :
        ‖graphMap q‖^2 =
          (graphMap q 0)^2 + (graphMap q 1)^2 +
            (graphMap q 2)^2 :=
      norm_sq_point3 (graphMap q)
    have hnorm_one : ‖graphMap q‖ = 1 := by
      have hnorm_nonneg : 0 ≤ ‖graphMap q‖ := norm_nonneg _
      nlinarith
    simpa only [unitSphere, mem_sphere, dist_zero_right] using hnorm_one
  have h_dist : dist (graphMap q) northPole ≤ r := by
    have hdist_sq :
        dist (graphMap q) northPole ^ 2 =
          2 - 2 * Real.sqrt (1 - (q 0)^2 - (q 1)^2) := by
      have hnorm_expansion :
          dist (graphMap q) northPole ^ 2 =
            (graphMap q 0 - 1)^2 + (graphMap q 1)^2 +
              (graphMap q 2)^2 := by
        simp [dist_eq_norm, norm_sq_point3, northPole, mkPoint3_apply]
        <;> ring
      rw [hnorm_expansion]
      simp [graphMap_apply0, graphMap_apply1, graphMap_apply2]
      <;> ring_nf
      <;> nlinarith [Real.sq_sqrt hsqrt_arg_nonneg]
    have hsqrt_lower :
        a ≤ Real.sqrt (1 - (q 0)^2 - (q 1)^2) := by
      have harg_lower :
          a^2 ≤ 1 - (q 0)^2 - (q 1)^2 := by
        nlinarith
      have hsqrt :=
        Real.sqrt_le_sqrt harg_lower
      rw [Real.sqrt_sq_eq_abs, abs_of_pos ha_pos] at hsqrt
      exact hsqrt
    have hdist_sq_le : dist (graphMap q) northPole ^ 2 ≤ r^2 := by
      rw [hdist_sq]
      have hlinear :
          2 - 2 * Real.sqrt (1 - (q 0)^2 - (q 1)^2) ≤
            2 - 2 * a := by
        linarith
      have hidentity : 2 - 2 * a = r^2 := by
        rw [ha_def]
        ring
      linarith
    have hdist_nonneg : 0 ≤ dist (graphMap q) northPole := dist_nonneg
    nlinarith
  change graphMap q ∈ unitSphere 3 ∧ graphMap q ∈ closedBall northPole r
  exact ⟨h_sphere, by simpa only [mem_closedBall] using h_dist⟩

lemma muHE_cap_bounds (r : ℝ) (hr : 0 < r) (hr2 : r < Real.sqrt 2) :
    let a := 1 - r^2 / 2
    let R2 := r^2 - r^4 / 4
    ENNReal.ofReal (Real.pi * R2) ≤ (μHE[2] : Measure (Point 3)) (sphereCap northPole r) ∧
    (μHE[2] : Measure (Point 3)) (sphereCap northPole r) ≤ ENNReal.ofReal (Real.pi * R2 / a^2) := by
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
  have h_a2 : a^2 + R2 = 1 := by nlinarith
  let R : ℝ := Real.sqrt R2
  let disk : Set (Point 2) := closedBall 0 R
  have hR2_eq : R^2 = R2 := by
    simp [R, Real.sq_sqrt hR2_nonneg]
  have hR_lt_one : R < 1 := by
    have h1 : R2 < 1 := by
      have h2 : r^2 < 2 := by
        have h3 : 0 ≤ r := by linarith
        have h4 : r^2 < (Real.sqrt 2)^2 := by gcongr
        have h5 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
        rw [h5] at h4; exact h4
      nlinarith [sq_pos_of_pos hr]
    have h2 : R^2 < 1 := by
      simpa [R, Real.sq_sqrt hR2_nonneg] using h1
    have h3 : 0 ≤ R := by positivity
    nlinarith
  have h_sqrt_eq : Real.sqrt (1 - R^2) = a := by
    have h1 : 1 - R^2 = a^2 := by
      rw [hR2_eq] <;> linarith [h_a2]
    rw [h1]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos ha_pos]
  have h_cap_eq : sphereCap northPole r = graphMap '' disk := by
    apply Set.Subset.antisymm
    · exact sphereCap_north_subset_graphMap_disk
        hr ha_pos ha_def hR2_eq h_a2 (by positivity)
    · exact graphMap_disk_subset_sphereCap_north
        hr ha_pos ha_def hR2_eq h_a2
  -- Lipschitz bound for graphMap
  let K_nn : NNReal := ⟨1 / a, by positivity⟩
  have h_disk_eq : disk = {q : Point 2 | (q 0)^2 + (q 1)^2 ≤ R^2} := by
    ext q
    simp only [disk, closedBall, dist_zero_right, Set.mem_setOf_eq]
    have h_norm_sq : ‖q‖^2 = (q 0)^2 + (q 1)^2 := norm_sq_point2 q
    have h : ‖q‖ ≤ R ↔ (q 0)^2 + (q 1)^2 ≤ R^2 := by
      rw [← h_norm_sq]
      have hR_nonneg : 0 ≤ R := by positivity
      constructor
      · intro h; gcongr
      · intro h; nlinarith [norm_nonneg q]
    exact h
  let K_orig : NNReal := ⟨1 / Real.sqrt (1 - R^2), by positivity⟩
  have hK_eq : K_orig = K_nn := by
    apply Subtype.ext
    have h : (1 / Real.sqrt (1 - R^2) : ℝ) = 1 / a := by
      rw [h_sqrt_eq]
    exact h
  have h2 := graphMap_lipschitzOnWith (Real.sqrt_nonneg R2) hR_lt_one
  have h3 : LipschitzOnWith K_nn graphMap {q : Point 2 | (q 0)^2 + (q 1)^2 ≤ R^2} := by
    convert h2 using 1
    exact hK_eq.symm
  have h_lip : LipschitzOnWith K_nn graphMap disk := by
    rw [h_disk_eq]
    exact h3
  have hK2 : (K_nn : ENNReal)^2 = ENNReal.ofReal (1 / a^2) := by
    have hK_ennreal : (K_nn : ENNReal) = ENNReal.ofReal (1 / a) := by
      have h1 : (K_nn : ENNReal) = ENNReal.ofReal (K_nn : ℝ) := ENNReal.coe_nnreal_eq K_nn
      rw [h1]
      have h2 : (K_nn : ℝ) = 1 / a := rfl
      rw [h2]
    rw [hK_ennreal]
    have h_pos : 0 ≤ 1 / a := by positivity
    have h_sq : (ENNReal.ofReal (1 / a)) ^ 2 = ENNReal.ofReal (1 / a) * ENNReal.ofReal (1 / a) := by ring
    rw [h_sq]
    have h : ENNReal.ofReal (1 / a) * ENNReal.ofReal (1 / a) = ENNReal.ofReal ((1 / a) * (1 / a)) := by
      rw [← ENNReal.ofReal_mul h_pos] <;> ring
    rw [h]
    have h2 : (1 / a) * (1 / a) = 1 / a^2 := by field_simp [ha_pos.ne'] <;> ring
    rw [h2]
  have h_upper : (μHE[2] : Measure (Point 3)) (graphMap '' disk) ≤
      ENNReal.ofReal (1 / a^2) * (μHE[2] : Measure (Point 2)) disk := by
    have h := lipschitzOnWith_muHE2_image_le h_lip
    rw [hK2] at h
    exact h
  -- Volume of disk
  have h_vol_disk : (μHE[2] : Measure (Point 2)) disk = ENNReal.ofReal (Real.pi * R2) := by
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume 2]
    rw [EuclideanSpace.volume_closedBall_fin_two (0 : Point 2) R]
    have hR_pos : 0 ≤ R := by positivity
    have h1 : (ENNReal.ofReal R) ^ 2 * ENNReal.ofReal Real.pi = ENNReal.ofReal (Real.pi * R2) := by
      have h2 : (ENNReal.ofReal R) ^ 2 = ENNReal.ofReal (R^2) := by
        calc
          (ENNReal.ofReal R) ^ 2
            = ENNReal.ofReal R * ENNReal.ofReal R := by ring
          _ = ENNReal.ofReal (R * R) := by rw [← ENNReal.ofReal_mul hR_pos] <;> ring
          _ = ENNReal.ofReal (R^2) := by ring_nf
      rw [h2]
      have h3 : R^2 = R2 := Real.sq_sqrt hR2_nonneg
      rw [h3]
      rw [← ENNReal.ofReal_mul (by positivity)] <;> ring_nf
    exact h1
  -- Projection lower bound
  let proj : Point 3 → Point 2 := projYZ
  have h_proj_lip : LipschitzWith 1 proj := projYZ_lipschitz
  have h_proj_surj : proj '' (graphMap '' disk) = disk := by
    ext q
    simp only [Set.mem_image]
    constructor
    · rintro ⟨p, ⟨q', hq', rfl⟩, rfl⟩
      have h_eq : proj (graphMap q') = q' := by
        ext i; fin_cases i <;> simp [proj, projYZ, graphMap_apply1, graphMap_apply2, mkPoint2_apply] <;> rfl
      rw [h_eq]
      exact hq'
    · intro hq
      refine ⟨graphMap q, ⟨q, hq, rfl⟩, ?_⟩
      ext i; fin_cases i <;> simp [proj, projYZ, graphMap_apply1, graphMap_apply2, mkPoint2_apply] <;> rfl
  have h_proj_lip_on : LipschitzOnWith (1 : NNReal) proj (graphMap '' disk) :=
    h_proj_lip.lipschitzOnWith
  have h_lower : (μHE[2] : Measure (Point 2)) disk ≤ (μHE[2] : Measure (Point 3)) (graphMap '' disk) := by
    have h : (μHE[2] : Measure (Point 2)) (proj '' (graphMap '' disk)) ≤
        (1 : ENNReal)^2 * (μHE[2] : Measure (Point 3)) (graphMap '' disk) :=
      lipschitzOnWith_muHE2_image_le h_proj_lip_on
    have h1 : (1 : ENNReal)^2 = 1 := by norm_num
    rw [h1] at h
    rw [h_proj_surj] at h
    simpa using h
  have h_main : ENNReal.ofReal (Real.pi * R2) ≤ (μHE[2] : Measure (Point 3)) (sphereCap northPole r) ∧
      (μHE[2] : Measure (Point 3)) (sphereCap northPole r) ≤ ENNReal.ofReal (Real.pi * R2 / a^2) := by
    rw [h_cap_eq]
    constructor
    · rw [h_vol_disk] at h_lower
      exact h_lower
    · rw [h_vol_disk] at h_upper
      have h_mul : ENNReal.ofReal (1 / a^2) * ENNReal.ofReal (Real.pi * R2) =
          ENNReal.ofReal (Real.pi * R2 / a^2) := by
        rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 / a^2 by positivity)]
        <;> ring_nf
      rw [h_mul] at h_upper
      exact h_upper
  simpa [ha_def, hR2_def] using h_main

end

end Kakeya.CV
