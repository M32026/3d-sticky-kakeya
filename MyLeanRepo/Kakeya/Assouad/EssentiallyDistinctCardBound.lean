import MyLeanRepo.Kakeya.Assouad.CylinderVolume
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.AnisotropicPacking
import MyLeanRepo.Kakeya.Streamlined.Families
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Polynomial cardinality bound for essentially distinct δ-tube families

Proves that a family of pairwise essentially distinct δ-tubes contained in the
unit ball has cardinality at most `35^6 / δ^6`.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Assouad

private abbrev e0 : Point3 := EuclideanSpace.single 0 1

/-- Coordinate bound: each coordinate absolute value ≤ Euclidean norm. -/
private lemma coord_le_norm (x : Point3) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have h_pos : 0 ≤ ∑ j : Fin 3, (x j)^2 := by positivity
  have h_norm : ‖x‖ = Real.sqrt (∑ j : Fin 3, (x j)^2) := by
    rw [PiLp.norm_eq_of_L2]
    congr
    ext j
    simp
  have h2 : (x i)^2 ≤ ∑ j : Fin 3, (x j)^2 := by
    have h3 : ∀ j ∈ Finset.univ, 0 ≤ (x j)^2 := by intro j _; positivity
    exact Finset.single_le_sum h3 (Finset.mem_univ i)
  have h4 : |x i|^2 = (x i)^2 := by rw [sq_abs]
  have h5 : |x i|^2 ≤ ‖x‖^2 := by
    rw [h4, h_norm]
    rw [Real.sq_sqrt h_pos]
    exact h2
  have h6 : 0 ≤ |x i| := by positivity
  have h7 : 0 ≤ ‖x‖ := by positivity
  nlinarith

/-- The canonical δ-tube contains the standard cylinder of radius δ, length 1. -/
lemma canonical_tube_contains_cylinder {δ : ℝ} (hδ : 0 < δ) :
    stdCylinder δ 1 ⊆ Metric.cthickening δ (unitSegment 0 e0) := by
  intro x hx
  have h1 : (x 1)^2 + (x 2)^2 ≤ δ^2 := hx.1
  have h2 : 0 ≤ x 0 := hx.2.1
  have h3 : x 0 ≤ 1 := hx.2.2
  let t : ℝ := x 0
  have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨h2, h3⟩
  let q : Point3 := t • e0
  have hq : q ∈ unitSegment 0 e0 := ⟨t, ht, by simp [q]⟩
  let w : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => 0
    | 1 => x 1
    | 2 => x 2
  have hdiff : x - q = WithLp.toLp 2 w := by
    ext i
    fin_cases i <;> simp [q, w, t, e0]
  have hdist : dist x q ≤ δ := by
    rw [dist_eq_norm, hdiff, PiLp.norm_eq_of_L2]
    have hsum2 : ∑ i : Fin 3, ‖(WithLp.toLp 2 w) i‖ ^ 2 = (x 1)^2 + (x 2)^2 := by
      simp [w, Fin.sum_univ_succ]
    rw [hsum2]
    have hsqrt : Real.sqrt ((x 1)^2 + (x 2)^2) ≤ δ := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨by positivity, h1⟩
    exact hsqrt
  exact Metric.mem_cthickening_of_dist_le x q δ (unitSegment 0 e0) hq hdist

/-- Lower bound: every δ-tube has volume at least `πδ²`. -/
lemma tube_volume_lower_pi {δ : ℝ} (hδ : 0 < δ) (T : Kakeya.DeltaTube δ) :
    ENNReal.ofReal (Real.pi * δ^2) ≤ T.volume := by
  have hvol : TubeVolumeScalingStatement := tube_volume_scaling
  have hT : T.volume = Kakeya.deltaTubeVolume δ := hvol.1 δ T
  rw [hT]
  have h : stdCylinder δ 1 ⊆ _ := canonical_tube_contains_cylinder hδ
  have h' : volume (stdCylinder δ 1) ≤ volume _ := measure_mono h
  have hvol_cyl : volume (stdCylinder δ 1) = ENNReal.ofReal (Real.pi * δ^2) := by
    have h9 := volume_stdCylinder δ 1 hδ.le (by norm_num)
    simpa using h9
  rw [hvol_cyl] at h'
  exact h'

/-- The canonical δ-tube is contained in a shifted cylinder of radius δ, length `1+2δ`. -/
lemma canonical_tube_subset_shifted_cylinder {δ : ℝ} (hδ : 0 < δ) :
    Metric.cthickening δ (unitSegment 0 e0) ⊆
      {x : Point3 | (x 1)^2 + (x 2)^2 ≤ δ^2 ∧ -δ ≤ x 0 ∧ x 0 ≤ 1 + δ} := by
  have h_compact : IsCompact (unitSegment 0 e0) := by
    apply IsCompact.image
    · exact isCompact_Icc
    · continuity
  have h_eq : Metric.cthickening δ (unitSegment 0 e0) =
      ⋃ y ∈ (unitSegment 0 e0), Metric.closedBall y δ :=
    h_compact.cthickening_eq_biUnion_closedBall hδ.le
  rw [h_eq]
  intro x hx
  rcases Set.mem_iUnion₂.mp hx with ⟨y, hy, hxy⟩
  rcases hy with ⟨t, ht, rfl⟩
  have hdist : dist x (t • e0) ≤ δ := by
    simpa [Metric.mem_closedBall] using hxy
  have hnorm : ‖x - t • e0‖ ≤ δ := hdist
  have h21 : (x - t • e0) 1 = x 1 := by simp [e0]
  have h22 : (x - t • e0) 2 = x 2 := by simp [e0]
  have h23 : (x - t • e0) 0 = x 0 - t := by simp [e0]
  have h_sum_eq : ∑ j : Fin 3, ‖(x - t • e0) j‖ ^ 2 = ∑ j : Fin 3, ((x - t • e0) j)^2 := by
    apply Finset.sum_congr rfl
    intro j _
    have h1 : ‖(x - t • e0) j‖ = |(x - t • e0) j| := by simp [Real.norm_eq_abs]
    rw [h1, sq_abs]
  have h_norm2 : ‖x - t • e0‖ ^ 2 = ∑ j : Fin 3, ((x - t • e0) j)^2 := by
    have h : ‖x - t • e0‖ = Real.sqrt (∑ j : Fin 3, ‖(x - t • e0) j‖ ^ 2) := by
      rw [PiLp.norm_eq_of_L2] <;> rfl
    rw [h, h_sum_eq, Real.sq_sqrt (by positivity)]
  have h9 : ‖x - t • e0‖ ^ 2 ≤ δ^2 := by
    have h10 : ‖x - t • e0‖ ≤ δ := hnorm
    have h11 : 0 ≤ ‖x - t • e0‖ := by positivity
    nlinarith
  have h_sum2 : (x 1)^2 + (x 2)^2 ≤ ∑ j : Fin 3, ((x - t • e0) j)^2 := by
    simp [Fin.sum_univ_succ, h21, h22] <;> positivity
  have h1 : (x 1)^2 + (x 2)^2 ≤ δ^2 := by
    rw [h_norm2] at h9
    linarith
  have h4 : |x 0 - t| ≤ δ := by
    have h5 : |(x - t • e0) 0| ≤ ‖x - t • e0‖ := coord_le_norm (x - t • e0) 0
    rw [h23] at h5
    exact h5.trans hnorm
  have h5 : -δ ≤ x 0 := by
    have h7 : x 0 - t ≥ -δ := by linarith [abs_le.mp h4]
    linarith [ht.1]
  have h6 : x 0 ≤ 1 + δ := by
    have h7 : x 0 - t ≤ δ := by linarith [abs_le.mp h4]
    linarith [ht.2]
  exact ⟨h1, h5, h6⟩

/-- Upper bound: every δ-tube has volume at most `πδ²(1+2δ)`. -/
lemma tube_volume_upper_pi {δ : ℝ} (hδ : 0 < δ) (T : Kakeya.DeltaTube δ) :
    T.volume ≤ ENNReal.ofReal (Real.pi * δ^2 * (1 + 2 * δ)) := by
  have hvol : TubeVolumeScalingStatement := tube_volume_scaling
  have hT : T.volume = Kakeya.deltaTubeVolume δ := hvol.1 δ T
  rw [hT]
  have h_sub := canonical_tube_subset_shifted_cylinder hδ
  let S : Set Point3 := {x | (x 1)^2 + (x 2)^2 ≤ δ^2 ∧ -δ ≤ x 0 ∧ x 0 ≤ 1 + δ}
  have h_meas1 : volume (Metric.cthickening δ (unitSegment 0 e0)) ≤ volume S :=
    measure_mono h_sub
  let shift : Point3 ≃ᵐ Point3 :=
    { toFun := fun x => x - δ • e0
      invFun := fun y => y + δ • e0
      left_inv := by intro x; ext i; fin_cases i <;> simp [e0] <;> ring
      right_inv := by intro y; ext i; fin_cases i <;> simp [e0] <;> ring
      measurable_toFun := measurable_id.sub measurable_const
      measurable_invFun := measurable_id.add measurable_const }
  have hmp_shift : MeasurePreserving shift volume volume :=
    measurePreserving_sub_right volume (δ • e0)
  have h_image : shift '' stdCylinder δ (1 + 2 * δ) = S := by
    ext y
    simp only [S, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 : (x 1)^2 + (x 2)^2 ≤ δ^2 := hx.1
      have h2 : 0 ≤ x 0 := hx.2.1
      have h3 : x 0 ≤ 1 + 2 * δ := hx.2.2
      have h41 : (x - δ • e0) 1 = x 1 := by simp [e0]
      have h42 : (x - δ • e0) 2 = x 2 := by simp [e0]
      have h43 : (x - δ • e0) 0 = x 0 - δ := by simp [e0]
      have h_goal1 : ((x - δ • e0) 1)^2 + ((x - δ • e0) 2)^2 ≤ δ^2 := by
        rw [h41, h42]; exact h1
      have h_goal2 : -δ ≤ (x - δ • e0) 0 := by
        rw [h43]; linarith
      have h_goal3 : (x - δ • e0) 0 ≤ 1 + δ := by
        rw [h43]; linarith
      exact ⟨h_goal1, h_goal2, h_goal3⟩
    · rintro ⟨h1, h2, h3⟩
      let x : Point3 := y + δ • e0
      have hx0 : x 0 = y 0 + δ := by simp [x, e0]
      have hx1 : x 1 = y 1 := by simp [x, e0]
      have hx2 : x 2 = y 2 := by simp [x, e0]
      have h_in : x ∈ stdCylinder δ (1 + 2 * δ) := by
        have h1' : (x 1)^2 + (x 2)^2 ≤ δ^2 := by
          rw [hx1, hx2]; exact h1
        have h2' : 0 ≤ x 0 := by
          rw [hx0]; linarith
        have h3' : x 0 ≤ 1 + 2 * δ := by
          rw [hx0]; linarith [h3]
        exact ⟨h1', h2', h3'⟩
      have h_shift_x : shift x = y := by
        ext i
        fin_cases i <;> simp [shift, x, e0] <;> ring
      exact ⟨x, h_in, h_shift_x⟩
  have h_meas_set : MeasurableSet (stdCylinder δ (1 + 2 * δ)) := by
    have h11 : Measurable (fun x : Point3 => (x 1)^2 + (x 2)^2) := by fun_prop
    have h21 : Measurable (fun x : Point3 => x 0) := by fun_prop
    exact (measurableSet_le h11 (by fun_prop)).inter (h21 measurableSet_Icc)
  have hmp_symm : MeasurePreserving shift.symm volume volume := hmp_shift.symm shift
  have h_img_eq : shift '' stdCylinder δ (1 + 2 * δ) = shift.symm ⁻¹' (stdCylinder δ (1 + 2 * δ)) := by
    ext z
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hz
      exact ⟨shift.symm z, hz, shift.apply_symm_apply z⟩
  have h_vol2 : volume (shift '' stdCylinder δ (1 + 2 * δ)) =
      volume (stdCylinder δ (1 + 2 * δ)) := by
    rw [h_img_eq]
    exact hmp_symm.measure_preimage h_meas_set.nullMeasurableSet
  have h_S_vol : volume S = volume (stdCylinder δ (1 + 2 * δ)) := by
    rw [←h_image, h_vol2]
  rw [h_S_vol] at h_meas1
  have hvol_cyl : volume (stdCylinder δ (1 + 2 * δ)) =
      ENNReal.ofReal (Real.pi * δ^2 * (1 + 2 * δ)) :=
    volume_stdCylinder δ (1 + 2 * δ) hδ.le (by linarith)
  rw [hvol_cyl] at h_meas1
  exact h_meas1

/-- If two δ-tubes have close bases and directions, they are NOT essentially distinct. -/
lemma close_tubes_not_essentially_distinct
    {δ : ℝ} (hδ : 0 < δ) (hδ_small : δ < 1 / 16)
    {T U : Kakeya.DeltaTube δ}
    (hbase : ‖T.base - U.base‖ ≤ δ / 8)
    (hdir : ‖T.direction - U.direction‖ ≤ δ / 8) :
    ¬ T.EssentiallyDistinct U := by
  set d : ℝ := δ / 8 with hd_def
  set r : ℝ := δ - 2 * d with hr_def
  have hr_pos : 0 < r := by linarith
  have hr_eq : r = 3 * δ / 4 := by linarith

  let T' : Kakeya.DeltaTube r := ⟨T.base, T.direction, T.direction_unit⟩

  have h_seg_compact : IsCompact (unitSegment T'.base T'.direction) := by
    apply IsCompact.image
    · exact isCompact_Icc
    · continuity

  have h1 : T'.carrier ⊆ T.carrier := by
    intro x hx
    have h_eq : T'.carrier = ⋃ y ∈ (unitSegment T'.base T'.direction), Metric.closedBall y r :=
      h_seg_compact.cthickening_eq_biUnion_closedBall hr_pos.le
    rw [h_eq] at hx
    rcases Set.mem_iUnion₂.mp hx with ⟨y, hy, hxy⟩
    rcases hy with ⟨t, ht, rfl⟩
    have hdist : dist x (T.base + t • T.direction) ≤ r := by
      simpa [Metric.mem_closedBall] using hxy
    have h' : dist x (T.base + t • T.direction) ≤ δ := by linarith
    exact Metric.mem_cthickening_of_dist_le x (T.base + t • T.direction) δ
      (unitSegment T.base T.direction) ⟨t, ht, rfl⟩ h'

  have h2 : T'.carrier ⊆ U.carrier := by
    intro x hx
    have h_eq : T'.carrier = ⋃ y ∈ (unitSegment T'.base T'.direction), Metric.closedBall y r :=
      h_seg_compact.cthickening_eq_biUnion_closedBall hr_pos.le
    rw [h_eq] at hx
    rcases Set.mem_iUnion₂.mp hx with ⟨y, hy, hxy⟩
    rcases hy with ⟨t, ht, rfl⟩
    have hdist_xp : dist x (T.base + t • T.direction) ≤ r := by
      simpa [Metric.mem_closedBall] using hxy
    let p := T.base + t • T.direction
    let q := U.base + t • U.direction
    have h_t_nonneg : 0 ≤ t := ht.1
    have h_t_le_one : t ≤ 1 := ht.2
    have h_eq1 : p - q = T.base - U.base + t • (T.direction - U.direction) := by
      ext i; fin_cases i <;> simp [p, q] <;> ring
    have h_pq : dist p q ≤ 2 * d := by
      dsimp only [dist, p, q]
      calc
        ‖p - q‖
          = ‖T.base - U.base + t • (T.direction - U.direction)‖ := by rw [h_eq1]
        _ ≤ ‖T.base - U.base‖ + ‖t • (T.direction - U.direction)‖ := norm_add_le _ _
        _ = ‖T.base - U.base‖ + |t| * ‖T.direction - U.direction‖ := by
          have h_smul : ‖t • (T.direction - U.direction)‖ = |t| * ‖T.direction - U.direction‖ := by
            rw [norm_smul, Real.norm_eq_abs]
          rw [h_smul]
        _ = ‖T.base - U.base‖ + t * ‖T.direction - U.direction‖ := by
          have h_abs : |t| = t := abs_of_nonneg h_t_nonneg
          rw [h_abs]
        _ ≤ d + t * d := by
          have h1 : ‖T.base - U.base‖ ≤ d := hbase
          have h2 : t * ‖T.direction - U.direction‖ ≤ t * d :=
            mul_le_mul_of_nonneg_left hdir h_t_nonneg
          have h_d_nonneg : 0 ≤ d := by linarith
          linarith
        _ ≤ 2 * d := by
          have h_d_nonneg : 0 ≤ d := by linarith
          have h3 : t * d ≤ d := by
            have h4 : t * d = d * t := by ring
            rw [h4]
            exact mul_le_of_le_one_right h_d_nonneg h_t_le_one
          linarith
    have h_xq : dist x q ≤ δ := by
      calc
        dist x q ≤ dist x p + dist p q := dist_triangle _ _ _
        _ ≤ r + 2 * d := by gcongr
        _ = δ := by linarith
    exact Metric.mem_cthickening_of_dist_le x q δ
      (unitSegment U.base U.direction) ⟨t, ht, rfl⟩ h_xq

  have h3 : T'.carrier ⊆ T.carrier ∩ U.carrier := by
    intro x hx
    exact ⟨h1 hx, h2 hx⟩
  have h4 : T'.volume ≤ volume (T.carrier ∩ U.carrier) := measure_mono h3

  have h_lower : ENNReal.ofReal (Real.pi * r^2) ≤ T'.volume :=
    tube_volume_lower_pi hr_pos T'
  have h_upper_T : T.volume ≤ ENNReal.ofReal (Real.pi * δ^2 * (1 + 2 * δ)) :=
    tube_volume_upper_pi hδ T
  have h_upper_U : U.volume ≤ ENNReal.ofReal (Real.pi * δ^2 * (1 + 2 * δ)) :=
    tube_volume_upper_pi hδ U
  have h_upper_max : max T.volume U.volume ≤
      ENNReal.ofReal (Real.pi * δ^2 * (1 + 2 * δ)) := max_le h_upper_T h_upper_U

  have h_real1 : Real.pi * r^2 > Real.pi * δ^2 * (1 + 2 * δ) / 2 := by
    have h5 : r = 3 * δ / 4 := by linarith
    rw [h5]
    have h7 : (3 * δ / 4)^2 > δ^2 * (1 + 2 * δ) / 2 := by
      have h9 : 16 * δ < 1 := by linarith [hδ_small]
      nlinarith [sq_pos_of_pos hδ, h9]
    have h6 : Real.pi * (3 * δ / 4)^2 > Real.pi * (δ^2 * (1 + 2 * δ) / 2) :=
      mul_lt_mul_of_pos_left h7 Real.pi_pos
    have h8 : Real.pi * (δ^2 * (1 + 2 * δ) / 2) = Real.pi * δ^2 * (1 + 2 * δ) / 2 := by ring
    rw [h8] at h6
    exact h6

  have h_pos_r : 0 < Real.pi * r^2 := by positivity
  have h_enn1 : ENNReal.ofReal (Real.pi * δ^2 * (1 + 2 * δ) / 2) <
      ENNReal.ofReal (Real.pi * r^2) := by
    have h_iff : ENNReal.ofReal (Real.pi * δ^2 * (1 + 2 * δ) / 2) <
        ENNReal.ofReal (Real.pi * r^2) ↔
        Real.pi * δ^2 * (1 + 2 * δ) / 2 < Real.pi * r^2 :=
      ENNReal.ofReal_lt_ofReal_iff h_pos_r
    exact h_iff.mpr h_real1

  have h_step1 : (1 / 2 : ENNReal) * max T.volume U.volume ≤
      (1 / 2 : ENNReal) * ENNReal.ofReal (Real.pi * δ^2 * (1 + 2 * δ)) :=
    mul_le_mul' (le_refl _) h_upper_max
  have h_step2 : (1 / 2 : ENNReal) * ENNReal.ofReal (Real.pi * δ^2 * (1 + 2 * δ)) =
      ENNReal.ofReal (Real.pi * δ^2 * (1 + 2 * δ) / 2) := by
    let y : ℝ := Real.pi * δ^2 * (1 + 2 * δ)
    have h_y2_pos : 0 ≤ y / 2 := by positivity
    have h_y_eq : y = y / 2 + y / 2 := by ring
    have h7 : ENNReal.ofReal y = ENNReal.ofReal (y / 2 + y / 2) :=
      congr_arg ENNReal.ofReal h_y_eq
    have h_add : ENNReal.ofReal (y / 2 + y / 2) = ENNReal.ofReal (y / 2) + ENNReal.ofReal (y / 2) :=
      ENNReal.ofReal_add h_y2_pos h_y2_pos
    have h3 : ENNReal.ofReal y = (2 : ENNReal) * ENNReal.ofReal (y / 2) := by
      calc
        ENNReal.ofReal y = ENNReal.ofReal (y / 2 + y / 2) := h7
        _ = ENNReal.ofReal (y / 2) + ENNReal.ofReal (y / 2) := h_add
        _ = (2 : ENNReal) * ENNReal.ofReal (y / 2) := by
          exact (two_mul (ENNReal.ofReal (y / 2))).symm
    have h4 : (1 / 2 : ENNReal) * ((2 : ENNReal) * ENNReal.ofReal (y / 2)) = ENNReal.ofReal (y / 2) := by
      rw [←mul_assoc]
      have h51 : (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ := by simp
      rw [h51]
      have h52 : (2 : ENNReal) ≠ 0 := by simp
      have h53 : (2 : ENNReal) ≠ ⊤ := by simp
      have h54 : (2 : ENNReal)⁻¹ * (2 : ENNReal) = 1 := by
        rw [mul_comm]
        exact ENNReal.mul_inv_cancel h52 h53
      rw [h54, one_mul]
    calc
      (1 / 2 : ENNReal) * ENNReal.ofReal y
        = (1 / 2 : ENNReal) * ((2 : ENNReal) * ENNReal.ofReal (y / 2)) := by rw [h3]
      _ = ENNReal.ofReal (y / 2) := h4
  have h_half_max : (1 / 2 : ENNReal) * max T.volume U.volume ≤
      ENNReal.ofReal (Real.pi * δ^2 * (1 + 2 * δ) / 2) :=
    le_trans h_step1 h_step2.le

  have h_main : (1 / 2 : ENNReal) * max T.volume U.volume <
      volume (T.carrier ∩ U.carrier) := by
    calc
      (1 / 2 : ENNReal) * max T.volume U.volume
        ≤ ENNReal.ofReal (Real.pi * δ^2 * (1 + 2 * δ) / 2) := h_half_max
      _ < ENNReal.ofReal (Real.pi * r^2) := h_enn1
      _ ≤ T'.volume := h_lower
      _ ≤ volume (T.carrier ∩ U.carrier) := h4
  intro h_distinct
  have h_contra : volume (T.carrier ∩ U.carrier) ≤ (1 / 2 : ENNReal) * max T.volume U.volume := by
    simpa [Kakeya.DeltaTube.EssentiallyDistinct] using h_distinct
  have h_bad : volume (T.carrier ∩ U.carrier) < volume (T.carrier ∩ U.carrier) :=
    calc volume (T.carrier ∩ U.carrier)
      ≤ (1 / 2 : ENNReal) * max T.volume U.volume := h_contra
    _ < volume (T.carrier ∩ U.carrier) := h_main
  exact lt_irrefl _ h_bad

/-- Grid coordinate function for a 3D point. -/
private def grid3 (r : ℝ) (p : Point3) : Fin 3 → ℤ :=
  fun i => ⌊(p i) / r⌋

/-- If two points have the same grid, their Euclidean distance is `< √3 * r`. -/
private lemma grid3_eq_imp_dist_lt {r : ℝ} (hr : 0 < r) {p q : Point3}
    (h : grid3 r p = grid3 r q) : ‖p - q‖ < Real.sqrt 3 * r := by
  have h1 : ∀ i : Fin 3, |(p - q) i| < r := by
    intro i
    have h2 : ⌊(p i) / r⌋ = ⌊(q i) / r⌋ := congr_fun h i
    have h3 : |(p i) / r - (q i) / r| < 1 :=
      Int.abs_sub_lt_one_of_floor_eq_floor h2
    have h4 : |((p i) - (q i)) / r| < 1 := by
      have h5 : ((p i) - (q i)) / r = (p i) / r - (q i) / r := by ring
      rw [h5]; exact h3
    have h6 : |(p i) - (q i)| < r := by
      have h7 : |((p i) - (q i)) / r| = |(p i) - (q i)| / r := by
        rw [abs_div]
        <;> simp [abs_of_pos hr]
      rw [h7] at h4
      calc
        |(p i) - (q i)| = (|(p i) - (q i)| / r) * r := by field_simp [hr.ne'] <;> ring
        _ < 1 * r := by gcongr
        _ = r := by ring
    simpa using h6
  have h2 : ∑ i : Fin 3, ((p - q) i)^2 < 3 * r^2 := by
    have h4 : ∀ i : Fin 3, ((p - q) i)^2 < r^2 := by
      intro i
      have h5 : |(p - q) i| < r := h1 i
      have h6 : |(p - q) i|^2 < r^2 := by
        have h7 : 0 ≤ r := by positivity
        nlinarith [abs_nonneg ((p - q) i)]
      have h8 : |(p - q) i|^2 = ((p - q) i)^2 := by rw [sq_abs]
      rw [h8] at h6; exact h6
    have h5 : ∑ i : Fin 3, ((p - q) i)^2 < ∑ i : Fin 3, r^2 := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact ⟨0, by simp⟩
      · intro i _; exact h4 i
    simpa using h5
  have h_sum_eq : ∑ i : Fin 3, ‖(p - q) i‖ ^ 2 = ∑ i : Fin 3, ((p - q) i)^2 := by
    apply Finset.sum_congr rfl
    intro i _
    have h1 : ‖(p - q) i‖ = |(p - q) i| := by
      simp [Real.norm_eq_abs]
    rw [h1, sq_abs]
  have h_pos : 0 ≤ ∑ i : Fin 3, ((p - q) i)^2 := by positivity
  have h_norm2 : ‖p - q‖ ^ 2 = ∑ i : Fin 3, ((p - q) i)^2 := by
    have h : ‖p - q‖ = Real.sqrt (∑ i : Fin 3, ‖(p - q) i‖ ^ 2) := by
      rw [PiLp.norm_eq_of_L2] <;> rfl
    rw [h, h_sum_eq, Real.sq_sqrt h_pos]
  have h6 : ‖p - q‖ ^ 2 < 3 * r^2 := by
    rw [h_norm2]; exact h2
  have h7 : 0 ≤ ‖p - q‖ := by positivity
  have h8 : 0 ≤ Real.sqrt 3 * r := by positivity
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

/-- Polynomial cardinality bound for essentially distinct tube families. -/
lemma essentially_distinct_card_bound
    {δ : ℝ} (hδ : 0 < δ) (hδ_one : δ ≤ 1) (hδ_small : δ < 1 / 16)
    {F : Kakeya.Streamlined.TubeFamily δ}
    (hF_ball : F.IsInUnitBall)
    (hF_distinct : F.IsEssentiallyDistinct) :
    (F.card : ℝ) ≤ (35 : ℝ)^6 * δ^(-6 : ℝ) := by
  set r : ℝ := δ / 16 with hr_def
  have hr_pos : 0 < r := by positivity
  have hsqrt3_lt_2 : Real.sqrt 3 < 2 := by
    have h : Real.sqrt 3 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have h2 : Real.sqrt 4 = 2 := by rw [Real.sqrt_eq_cases] <;> norm_num
    linarith

  let f : Fin F.card → (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
    fun i => (grid3 r (F.tube i).base, grid3 r (F.tube i).direction)

  have h_inj : Set.InjOn f Set.univ := by
    intro i _ j _ h_eq
    by_contra h_ne
    have h_base_eq : grid3 r (F.tube i).base = grid3 r (F.tube j).base :=
      congr_arg Prod.fst h_eq
    have h_dir_eq : grid3 r (F.tube i).direction = grid3 r (F.tube j).direction :=
      congr_arg Prod.snd h_eq
    have h_base : ‖(F.tube i).base - (F.tube j).base‖ < δ / 8 := by
      have h9 : ‖(F.tube i).base - (F.tube j).base‖ < Real.sqrt 3 * r :=
        grid3_eq_imp_dist_lt hr_pos h_base_eq
      have h10 : Real.sqrt 3 * r < δ / 8 := by
        rw [hr_def]
        nlinarith [hsqrt3_lt_2, hδ]
      linarith
    have h_dir : ‖(F.tube i).direction - (F.tube j).direction‖ < δ / 8 := by
      have h9 : ‖(F.tube i).direction - (F.tube j).direction‖ < Real.sqrt 3 * r :=
        grid3_eq_imp_dist_lt hr_pos h_dir_eq
      have h10 : Real.sqrt 3 * r < δ / 8 := by
        rw [hr_def]
        nlinarith [hsqrt3_lt_2, hδ]
      linarith
    have h_not_distinct : ¬ (F.tube i).EssentiallyDistinct (F.tube j) :=
      close_tubes_not_essentially_distinct hδ hδ_small h_base.le h_dir.le
    have h_distinct : (F.tube i).EssentiallyDistinct (F.tube j) :=
      hF_distinct i j h_ne
    exact h_not_distinct h_distinct

  have h_base_in_ball : ∀ i : Fin F.card, ‖(F.tube i).base‖ ≤ 1 := by
    intro i
    have h : (F.tube i).carrier ⊆ Metric.closedBall (0 : Point3) 1 := hF_ball i
    have h0 : (F.tube i).base ∈ unitSegment (F.tube i).base (F.tube i).direction := by
      exact ⟨0, by norm_num, by simp⟩
    have h_dist : dist (F.tube i).base (F.tube i).base ≤ δ := by
      have h : dist (F.tube i).base (F.tube i).base = 0 := dist_self _
      rw [h]
      exact hδ.le
    have h_seg : (F.tube i).base ∈ (F.tube i).carrier :=
      Metric.mem_cthickening_of_dist_le (F.tube i).base (F.tube i).base δ
        (unitSegment (F.tube i).base (F.tube i).direction) h0 h_dist
    have h_in_ball : (F.tube i).base ∈ Metric.closedBall (0 : Point3) 1 := h h_seg
    have h_goal : ‖(F.tube i).base‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using h_in_ball
    exact h_goal

  have h_dir_unit : ∀ i : Fin F.card, ‖(F.tube i).direction‖ = 1 :=
    fun i => (F.tube i).direction_unit

  have h_coord_bound : ∀ (p : Point3), ‖p‖ ≤ 1 → ∀ i : Fin 3, |p i| ≤ 1 := by
    intro p hp i
    have h : |p i| ≤ ‖p‖ := coord_le_norm p i
    linarith

  let N : ℤ := ⌈1 / r⌉
  have hN1 : 1 / r ≤ (N : ℝ) := Int.le_ceil _
  have hN2 : (N : ℝ) ≤ 1 / r + 1 := (Int.ceil_lt_add_one (1 / r)).le

  let S : Finset ℤ := Finset.Icc (-N) N
  let S2 : Finset (ℤ × ℤ) := S ×ˢ S
  let S3 : Finset ((ℤ × ℤ) × ℤ) := S2 ×ˢ S
  let S6 : Finset (((ℤ × ℤ) × ℤ) × ((ℤ × ℤ) × ℤ)) := S3 ×ˢ S3

  have h_coord_in_S : ∀ (p : Point3), ‖p‖ ≤ 1 → ∀ i : Fin 3, grid3 r p i ∈ S := by
    intro p hp i
    have h1 : |p i| ≤ 1 := h_coord_bound p hp i
    have h2 : -1 ≤ p i := by linarith [abs_le.mp h1]
    have h3 : p i ≤ 1 := by linarith [abs_le.mp h1]
    have h4 : -1 / r ≤ (p i) / r := by gcongr
    have h5 : (p i) / r ≤ 1 / r := by gcongr
    have hN_neg : (↑(-N) : ℝ) ≤ -1 / r := by
      have hN1' : (1 / r : ℝ) ≤ (N : ℝ) := hN1
      have h2 : (↑(-N) : ℝ) = -(N : ℝ) := by simp
      rw [h2]
      have h4 : -(1 / r : ℝ) = -1 / r := by ring
      have h5 : -(N : ℝ) ≤ -(1 / r : ℝ) := by linarith [hN1']
      rw [h4] at h5
      exact h5
    have h6 : (↑(-N) : ℝ) ≤ (p i) / r := by linarith [hN_neg, h4]
    have h7 : -N ≤ ⌊(p i) / r⌋ := Int.le_floor.mpr h6
    have h8 : ⌊(p i) / r⌋ ≤ N := by
      have h9 : (⌊(p i) / r⌋ : ℝ) ≤ (p i) / r := Int.floor_le _
      have h10 : (p i) / r ≤ (N : ℝ) := by linarith
      exact_mod_cast h9.trans h10
    exact Finset.mem_Icc.mpr ⟨h7, h8⟩

  let encode3 (p : Point3) : (ℤ × ℤ) × ℤ :=
    ((grid3 r p 0, grid3 r p 1), grid3 r p 2)

  let encode6 (i : Fin F.card) : ((ℤ × ℤ) × ℤ) × ((ℤ × ℤ) × ℤ) :=
    (encode3 (F.tube i).base, encode3 (F.tube i).direction)

  have h_encode3_in_S3 : ∀ (p : Point3), ‖p‖ ≤ 1 → encode3 p ∈ S3 := by
    intro p hp
    have h1 : grid3 r p 0 ∈ S := h_coord_in_S p hp 0
    have h2 : grid3 r p 1 ∈ S := h_coord_in_S p hp 1
    have h3 : grid3 r p 2 ∈ S := h_coord_in_S p hp 2
    simp only [encode3, S3, S2, Finset.mem_product]
    exact ⟨⟨h1, h2⟩, h3⟩

  have h_image_subset : Finset.image encode6 Finset.univ ⊆ S6 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, _, rfl⟩
    have h1 : ‖(F.tube i).base‖ ≤ 1 := h_base_in_ball i
    have h2 : ‖(F.tube i).direction‖ ≤ 1 := by
      rw [h_dir_unit i] <;> norm_num
    simp only [encode6, S6, Finset.mem_product]
    exact ⟨h_encode3_in_S3 (F.tube i).base h1, h_encode3_in_S3 (F.tube i).direction h2⟩

  have h_inj : Set.InjOn encode6 (Finset.univ : Finset (Fin F.card)) := by
    intro i _ j _ h_eq
    by_contra h_ne
    have h_base_eq : grid3 r (F.tube i).base = grid3 r (F.tube j).base := by
      have h : encode3 (F.tube i).base = encode3 (F.tube j).base := congr_arg Prod.fst h_eq
      have h0 : grid3 r (F.tube i).base 0 = grid3 r (F.tube j).base 0 := by
        exact congr_arg (fun x : (ℤ × ℤ) × ℤ => x.1.1) h
      have h1 : grid3 r (F.tube i).base 1 = grid3 r (F.tube j).base 1 := by
        exact congr_arg (fun x : (ℤ × ℤ) × ℤ => x.1.2) h
      have h2 : grid3 r (F.tube i).base 2 = grid3 r (F.tube j).base 2 := by
        exact congr_arg (fun x : (ℤ × ℤ) × ℤ => x.2) h
      funext k
      fin_cases k <;> assumption
    have h_dir_eq : grid3 r (F.tube i).direction = grid3 r (F.tube j).direction := by
      have h : encode3 (F.tube i).direction = encode3 (F.tube j).direction := congr_arg Prod.snd h_eq
      have h0 : grid3 r (F.tube i).direction 0 = grid3 r (F.tube j).direction 0 := by
        exact congr_arg (fun x : (ℤ × ℤ) × ℤ => x.1.1) h
      have h1 : grid3 r (F.tube i).direction 1 = grid3 r (F.tube j).direction 1 := by
        exact congr_arg (fun x : (ℤ × ℤ) × ℤ => x.1.2) h
      have h2 : grid3 r (F.tube i).direction 2 = grid3 r (F.tube j).direction 2 := by
        exact congr_arg (fun x : (ℤ × ℤ) × ℤ => x.2) h
      funext k
      fin_cases k <;> assumption
    have h_base : ‖(F.tube i).base - (F.tube j).base‖ < δ / 8 := by
      have h9 : ‖(F.tube i).base - (F.tube j).base‖ < Real.sqrt 3 * r :=
        grid3_eq_imp_dist_lt hr_pos h_base_eq
      have h10 : Real.sqrt 3 * r < δ / 8 := by
        rw [hr_def]
        nlinarith [hsqrt3_lt_2, hδ]
      linarith
    have h_dir : ‖(F.tube i).direction - (F.tube j).direction‖ < δ / 8 := by
      have h9 : ‖(F.tube i).direction - (F.tube j).direction‖ < Real.sqrt 3 * r :=
        grid3_eq_imp_dist_lt hr_pos h_dir_eq
      have h10 : Real.sqrt 3 * r < δ / 8 := by
        rw [hr_def]
        nlinarith [hsqrt3_lt_2, hδ]
      linarith
    have h_not_distinct : ¬ (F.tube i).EssentiallyDistinct (F.tube j) :=
      close_tubes_not_essentially_distinct hδ hδ_small h_base.le h_dir.le
    have h_distinct : (F.tube i).EssentiallyDistinct (F.tube j) := hF_distinct i j h_ne
    exact h_not_distinct h_distinct

  have h_card_S6 : S6.card = S.card ^ 6 := by
    simp [S6, S3, S2, Finset.card_product]
    <;> ring

  have hN_nonneg : 0 ≤ N := by
    have h1 : 0 < 1 / r := by positivity
    have h2 : 0 < N := Int.ceil_pos.mpr h1
    linarith

  have hN_bound : (N : ℝ) ≤ 35 / δ := by
    have h1 : (N : ℝ) ≤ 1 / r + 1 := hN2
    have h2 : 1 / r = 16 / δ := by
      rw [hr_def] <;> field_simp [hδ.ne'] <;> ring
    rw [h2] at h1
    have h3 : 16 / δ + 1 ≤ 35 / δ := by
      have h4 : 0 < δ := hδ
      field_simp [h4.ne']
      <;> nlinarith
    linarith

  have h_card_S : (S.card : ℝ) = 2 * (N : ℝ) + 1 := by
    have h : (-N : ℤ) ≤ N + 1 := by linarith
    have h' : (↑(Finset.Icc (-N) N).card : ℤ) = N + 1 - (-N) := Int.card_Icc_of_le (-N) N h
    have h_eq : (S.card : ℤ) = ↑(Finset.Icc (-N) N).card := by
      simp [S]
    have h4 : (S.card : ℤ) = N + 1 - (-N) := by
      rw [h_eq, h']
    have h5 : (S.card : ℝ) = ↑(S.card : ℤ) := by simp
    rw [h5, h4]
    <;> simp [hN_nonneg] <;> norm_cast <;> ring

  have h_S_bound : (S.card : ℝ) ≤ 35 / δ := by
    rw [h_card_S]
    have h3 : (N : ℝ) ≤ 1 / r + 1 := hN2
    have h4 : 1 / r = 16 / δ := by
      rw [hr_def] <;> field_simp [hδ.ne'] <;> ring
    have h3' : (N : ℝ) ≤ 16 / δ + 1 := by
      rw [h4] at h3 <;> exact h3
    have h_posδ : 0 < δ := hδ
    have h6 : 2 * (N : ℝ) + 1 ≤ 32 / δ + 3 :=
      calc 2 * (N : ℝ) + 1 ≤ 2 * (16 / δ + 1) + 1 := by gcongr
        _ = 32 / δ + 3 := by ring
    have h7 : 32 / δ + 3 ≤ 35 / δ := by
      have h8 : 3 ≤ 3 / δ := by
        have h9 : δ ≤ 1 := hδ_one
        have h10 : 3 / δ ≥ 3 := by
          calc 3 / δ ≥ 3 / 1 := by gcongr
            _ = 3 := by norm_num
        exact h10
      have h11 : 32 / δ + 3 ≤ 32 / δ + 3 / δ := by gcongr
      have h12 : 32 / δ + 3 / δ = 35 / δ := by
        field_simp [h_posδ.ne'] <;> ring
      rw [h12] at h11
      exact h11
    linarith

  have h_final : (Finset.image encode6 Finset.univ).card = F.card := by
    rw [Finset.card_image_of_injOn h_inj]
    simp

  have h_card_image : (Finset.image encode6 Finset.univ).card ≤ S6.card :=
    Finset.card_le_card h_image_subset

  rw [h_final] at h_card_image
  have h_main : (F.card : ℝ) ≤ (S6.card : ℝ) := by exact_mod_cast h_card_image
  have h_S6_eq : (S6.card : ℝ) = (S.card : ℝ)^6 := by
    rw [h_card_S6] <;> norm_cast
  have h_main2 : (F.card : ℝ) ≤ (S.card : ℝ)^6 := by
    rw [h_S6_eq] at h_main
    exact h_main
  have h6 : (S.card : ℝ)^6 ≤ (35 / δ)^6 := by
    gcongr
    <;> linarith [h_S_bound]
  have h7 : (F.card : ℝ) ≤ (35 / δ)^6 := by
    calc (F.card : ℝ) ≤ (S.card : ℝ)^6 := h_main2
      _ ≤ (35 / δ)^6 := h6
  have h8 : (35 / δ)^6 = (35 : ℝ)^6 * δ^(-6 : ℝ) := by
    have h_posδ : 0 < δ := hδ
    have h9 : (35 / δ)^6 = (35 : ℝ)^6 / δ^6 := by
      field_simp [h_posδ.ne'] <;> ring
    have h10 : (35 : ℝ)^6 * δ^(-6 : ℝ) = (35 : ℝ)^6 / δ^6 := by
      have h11 : δ^(-6 : ℝ) = (δ^6)⁻¹ := by
        have h12 : 0 ≤ δ := by linarith
        rw [Real.rpow_neg h12]
        <;> norm_cast <;> field_simp
      rw [h11]
      <;> field_simp
    rw [h9, h10]
  rw [h8] at h7
  exact h7

/--
Polynomial cardinality bound for an essentially-distinct family supported
in a fixed ball of radius `R`.
-/
lemma essentially_distinct_card_bound_fixed_ball
    {δ R : ℝ}
    (hδ : 0 < δ)
    (hδ_one : δ ≤ 1)
    (hδ_small : δ < 1 / 16)
    (hR : 1 ≤ R)
    {F : Kakeya.Streamlined.TubeFamily δ}
    (hF_ball :
      ∀ index,
        (F.tube index).carrier ⊆
          Metric.closedBall (0 : Point3) R)
    (hF_distinct : F.IsEssentiallyDistinct) :
    (F.card : ℝ) ≤
      (37 * R : ℝ) ^ 6 * δ ^ (-6 : ℝ) := by
  set r : ℝ := δ / 16 with hr_def
  have hr_pos : 0 < r := by positivity
  have hsqrt3_lt_2 : Real.sqrt 3 < 2 := by
    have h : Real.sqrt 3 < Real.sqrt 4 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have h2 : Real.sqrt 4 = 2 := by
      rw [Real.sqrt_eq_cases] <;> norm_num
    linarith
  let parameter :
      Fin F.card → (Fin 6 → ℝ) := fun index coordinate =>
    if hcoordinate : coordinate.val < 3 then
      (F.tube index).base ⟨coordinate.val, hcoordinate⟩
    else
      (F.tube index).direction
        ⟨coordinate.val - 3, by omega⟩
  let parameters : Finset (Fin 6 → ℝ) :=
    Finset.image parameter Finset.univ
  have hbase : ∀ index, ‖(F.tube index).base‖ ≤ R := by
    intro index
    have hbaseCarrier :
        (F.tube index).base ∈
          (F.tube index).carrier := by
      exact
        Metric.mem_cthickening_of_dist_le
          (F.tube index).base (F.tube index).base δ
          (unitSegment
            (F.tube index).base (F.tube index).direction)
          ⟨0, by norm_num, by simp⟩
          (by simpa using hδ.le)
    have hball :=
      hF_ball index hbaseCarrier
    simpa [Metric.mem_closedBall, dist_zero_right] using hball
  have hparameterBound :
      ∀ value ∈ parameters,
        ∀ coordinate : Fin 6,
          |value coordinate| ≤ R := by
    intro value hvalue coordinate
    rcases Finset.mem_image.mp hvalue with
      ⟨index, _, rfl⟩
    by_cases hcoordinate : coordinate.val < 3
    · dsimp only [parameter]
      rw [dif_pos hcoordinate]
      exact
        (coord_le_norm
          (F.tube index).base
          ⟨coordinate.val, hcoordinate⟩).trans
          (hbase index)
    · dsimp only [parameter]
      rw [dif_neg hcoordinate]
      exact
        (coord_le_norm
          (F.tube index).direction
          ⟨coordinate.val - 3, by omega⟩).trans
          ((F.tube index).direction_unit.le.trans hR)
  have hparameterInjective :
      Set.InjOn parameter
        (Finset.univ : Finset (Fin F.card)) := by
    intro first _ second _ heq
    by_contra hne
    have hbaseClose :
        ‖(F.tube first).base -
            (F.tube second).base‖ ≤ δ / 8 := by
      have hcoordinate :
          ∀ coordinate : Fin 3,
            (F.tube first).base coordinate =
              (F.tube second).base coordinate := by
        intro coordinate
        have hvalue :=
          congrFun heq
            ⟨coordinate.val, by omega⟩
        simpa [parameter] using hvalue
      rw [show (F.tube first).base =
          (F.tube second).base by
        ext coordinate
        exact hcoordinate coordinate]
      simp
      linarith
    have hdirectionClose :
        ‖(F.tube first).direction -
            (F.tube second).direction‖ ≤ δ / 8 := by
      have hcoordinate :
          ∀ coordinate : Fin 3,
            (F.tube first).direction coordinate =
              (F.tube second).direction coordinate := by
        intro coordinate
        have hvalue :=
          congrFun heq
            ⟨coordinate.val + 3, by omega⟩
        simpa [parameter] using hvalue
      rw [show (F.tube first).direction =
          (F.tube second).direction by
        ext coordinate
        exact hcoordinate coordinate]
      simp
      linarith
    exact
      (close_tubes_not_essentially_distinct
        hδ hδ_small hbaseClose hdirectionClose)
        (hF_distinct first second hne)
  have hparameterCard :
      parameters.card = F.card := by
    rw [Finset.card_image_of_injOn hparameterInjective]
    simp [parameters]
  let cellSize : Fin 6 → ℝ := fun _ => r
  let radius : Fin 6 → ℝ := fun _ => R
  have hseparation :
      ∀ first ∈ parameters,
        ∀ second ∈ parameters,
          first ≠ second →
            ∃ coordinate : Fin 6,
              |first coordinate - second coordinate| ≥
                cellSize coordinate := by
    intro first hfirst second hsecond hne
    rcases Finset.mem_image.mp hfirst with
      ⟨firstIndex, _, rfl⟩
    rcases Finset.mem_image.mp hsecond with
      ⟨secondIndex, _, rfl⟩
    have hindexNe : firstIndex ≠ secondIndex := by
      intro heq
      apply hne
      rw [heq]
    by_contra hnot
    simp only [not_exists, not_le] at hnot
    have hbaseCoordinate :
        ∀ coordinate : Fin 3,
          |(F.tube firstIndex).base coordinate -
              (F.tube secondIndex).base coordinate| < r := by
      intro coordinate
      have hclose :=
        hnot ⟨coordinate.val, by omega⟩
      simpa [parameter, cellSize] using hclose
    have hdirectionCoordinate :
        ∀ coordinate : Fin 3,
          |(F.tube firstIndex).direction coordinate -
              (F.tube secondIndex).direction coordinate| < r := by
      intro coordinate
      have hclose :=
        hnot ⟨coordinate.val + 3, by omega⟩
      simpa [parameter, cellSize] using hclose
    have hnormOfCoordinates :
        ∀ vector : Point3,
          (∀ coordinate : Fin 3, |vector coordinate| < r) →
            ‖vector‖ < δ / 8 := by
      intro vector hvector
      have hzero :
          vector 0 ^ 2 < r ^ 2 := by
        nlinarith [sq_abs (vector 0),
          abs_nonneg (vector 0), hvector 0, hr_pos]
      have hone :
          vector 1 ^ 2 < r ^ 2 := by
        nlinarith [sq_abs (vector 1),
          abs_nonneg (vector 1), hvector 1, hr_pos]
      have htwo :
          vector 2 ^ 2 < r ^ 2 := by
        nlinarith [sq_abs (vector 2),
          abs_nonneg (vector 2), hvector 2, hr_pos]
      have hnormSq :
          ‖vector‖ ^ 2 =
            vector 0 ^ 2 + vector 1 ^ 2 + vector 2 ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp [Fin.sum_univ_succ]
        ring
      rw [hr_def] at hzero hone htwo
      nlinarith [hnormSq, norm_nonneg vector]
    have hbaseClose :
        ‖(F.tube firstIndex).base -
            (F.tube secondIndex).base‖ ≤ δ / 8 := by
      exact
        (hnormOfCoordinates
          ((F.tube firstIndex).base -
            (F.tube secondIndex).base)
          (by
            intro coordinate
            simpa [Pi.sub_apply] using
              hbaseCoordinate coordinate)).le
    have hdirectionClose :
        ‖(F.tube firstIndex).direction -
            (F.tube secondIndex).direction‖ ≤ δ / 8 := by
      exact
        (hnormOfCoordinates
          ((F.tube firstIndex).direction -
            (F.tube secondIndex).direction)
          (by
            intro coordinate
            simpa [Pi.sub_apply] using
              hdirectionCoordinate coordinate)).le
    exact
      (close_tubes_not_essentially_distinct
        hδ hδ_small hbaseClose hdirectionClose)
        (hF_distinct firstIndex secondIndex hindexNe)
  have hpack :=
    anisotropic_cell_pack
      (s := cellSize) (R := radius)
      (fun _ => hr_pos)
      (fun _ => by linarith)
      hparameterBound hseparation
  have hproduct :
      (∏ _coordinate : Fin 6,
        (2 * Nat.ceil (R / r) + 1)) =
          (2 * Nat.ceil (R / r) + 1) ^ 6 := by
    simp [Fin.prod_const]
  have hcardNat :
      F.card ≤ (2 * Nat.ceil (R / r) + 1) ^ 6 := by
    rw [hparameterCard, hproduct] at hpack
    exact hpack
  have hceil :
      (Nat.ceil (R / r) : ℝ) ≤ 17 * (R / δ) := by
    let x := R / δ
    have hceilLt :
        (Nat.ceil (R / r) : ℝ) <
          R / r + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hratio : R / r = 16 * x := by
      dsimp only [x]
      rw [hr_def]
      field_simp [hδ.ne']
    rw [hratio] at hceilLt
    have hone : 1 ≤ x := by
      have h : δ ≤ R := hδ_one.trans hR
      have h' : (1 : ℝ) * δ ≤ R := by simpa using h
      exact (le_div_iff₀ hδ).mpr h'
    rw [hratio]
    linarith
  have hfactor :
      (2 * Nat.ceil (R / r) + 1 : ℝ) ≤
        37 * (R / δ) := by
    let x := R / δ
    have hx : 1 ≤ x := by
      have h : δ ≤ R := hδ_one.trans hR
      have h' : (1 : ℝ) * δ ≤ R := by simpa using h
      exact (le_div_iff₀ hδ).mpr h'
    have hceilX :
        (Nat.ceil (R / r) : ℝ) ≤ 17 * x := by
      exact hceil
    have hcast :
        (2 * Nat.ceil (R / r) + 1 : ℝ) =
          2 * (Nat.ceil (R / r) : ℝ) + 1 := by
      norm_num
    rw [hcast]
    have hbound :
        2 * (Nat.ceil (R / r) : ℝ) + 1 ≤ 37 * x := by
      nlinarith
    exact hbound
  have hcardReal :
      (F.card : ℝ) ≤
        (2 * Nat.ceil (R / r) + 1 : ℝ) ^ 6 := by
    exact_mod_cast hcardNat
  calc
    (F.card : ℝ) ≤
        (2 * Nat.ceil (R / r) + 1 : ℝ) ^ 6 :=
      hcardReal
    _ ≤ (37 * (R / δ)) ^ 6 := by gcongr
    _ = (37 * R : ℝ) ^ 6 * δ ^ (-6 : ℝ) := by
      have hdeltaPower :
          δ ^ (-6 : ℝ) = (δ ^ 6)⁻¹ := by
        rw [Real.rpow_neg hδ.le]
        norm_num
      rw [hdeltaPower]
      field_simp [hδ.ne']

end Kakeya.Assouad
