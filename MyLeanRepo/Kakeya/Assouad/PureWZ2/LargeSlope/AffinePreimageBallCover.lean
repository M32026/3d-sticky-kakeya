import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.OffsetProjectiveTotalNormal
import Mathlib.Data.Int.Interval

/-!
# Finite ball covers for an offset-diagonal preimage

The map `pureWZ2OffsetProjectiveTotalLinear a b S lambda` contracts only one
potentially dangerous source direction, by the factor `b`.  We cover that
direction by an integer grid.  The grid centers include the compensating
shear `x = -a*y`, so every covering ball has radius comparable to the target
radius, while the number of balls is `O(b⁻¹)` and is independent of that
radius.
-/

noncomputable section

namespace Kakeya.Assouad

open Set Metric

/-- The explicit formula is also a right inverse when all diagonal factors
are nonzero. -/
theorem pureWZ2OffsetProjectiveTotal_apply_inverse
    {a b S lambda : ℝ} (hb : b ≠ 0) (hS : S ≠ 0)
    (hlambda : lambda ≠ 0) (point : Point3) :
    pureWZ2OffsetProjectiveTotalLinear a b S lambda
        (pureWZ2OffsetProjectiveTotalInverse a b S lambda point) = point := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2OffsetProjectiveTotalInverse,
      pureWZ2OffsetProjectiveTotalLinear, point3] <;>
    field_simp [hb, hS, hlambda]

/-- A target ball of radius `r` has an `O(b⁻¹)` finite-ball cover after
pullback by the offset-diagonal map.  The source radius is `3*r`; notably it
does not contain `b⁻¹`. -/
theorem pureWZ2OffsetProjectiveTotal_preimage_closedBall_finite_cover
    {a b S lambda r : ℝ}
    (ha : |a| ≤ 1 / 2) (hb : 0 < b) (hb_one : b ≤ 1)
    (hS : 1 ≤ S) (hlambda : 1 ≤ lambda) (hr : 0 < r)
    (target : Point3) :
    ∃ centers : Finset Point3,
      (centers.card : ℝ) ≤ 7 * b⁻¹ ∧
      pureWZ2OffsetProjectiveTotalLinear a b S lambda ⁻¹'
          Metric.closedBall target r ⊆
        ⋃ center ∈ centers, Metric.closedBall center (3 * r) := by
  let sourceCenter :=
    pureWZ2OffsetProjectiveTotalInverse a b S lambda target
  let indexBound : ℤ := Nat.ceil (1 / b + 1)
  let indices : Finset ℤ := Finset.Icc (-indexBound) indexBound
  let gridCenter : ℤ → Point3 := fun index =>
    sourceCenter + point3 (-a * ((index : ℝ) * r)) ((index : ℝ) * r) 0
  let centers : Finset Point3 := indices.image gridCenter
  have hb_ne : b ≠ 0 := hb.ne'
  have hS_pos : 0 < S := zero_lt_one.trans_le hS
  have hlambda_pos : 0 < lambda := zero_lt_one.trans_le hlambda
  have hbound_nonneg : 0 ≤ indexBound := by
    dsimp only [indexBound]
    exact_mod_cast Nat.zero_le (Nat.ceil (1 / b + 1))
  have hbound_real : 1 / b + 1 ≤ (indexBound : ℝ) := by
    dsimp only [indexBound]
    exact Nat.le_ceil (1 / b + 1)
  have hbound_lt : (indexBound : ℝ) < 1 / b + 2 := by
    have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 1 / b + 1)
    have hcast : (indexBound : ℝ) = (Nat.ceil (1 / b + 1) : ℝ) := by
      simp [indexBound]
    rw [hcast]
    linarith
  have hcard_indices : (indices.card : ℤ) = 2 * indexBound + 1 := by
    dsimp only [indices]
    rw [Int.card_Icc_of_le]
    · ring
    · omega
  have hcard_centers : (centers.card : ℝ) ≤ 2 * (indexBound : ℝ) + 1 := by
    have hcard_nat : centers.card ≤ indices.card := by
      exact Finset.card_image_le
    have hcard_int : (centers.card : ℤ) ≤ 2 * indexBound + 1 := by
      calc
        (centers.card : ℤ) ≤ (indices.card : ℤ) := by exact_mod_cast hcard_nat
        _ = 2 * indexBound + 1 := hcard_indices
    exact_mod_cast hcard_int
  have hcard : (centers.card : ℝ) ≤ 7 * b⁻¹ := by
    calc
      (centers.card : ℝ) ≤ 2 * (indexBound : ℝ) + 1 := hcard_centers
      _ ≤ 7 * b⁻¹ := by
        have hinv_one : 1 ≤ b⁻¹ := by
          rw [one_le_inv₀ hb]
          exact hb_one
        have hbound_le : (indexBound : ℝ) ≤ 1 / b + 2 := hbound_lt.le
        rw [div_eq_mul_inv] at hbound_le
        nlinarith
  refine ⟨centers, hcard, ?_⟩
  intro source hsource
  have hsourceCenterImage :
      pureWZ2OffsetProjectiveTotalLinear a b S lambda sourceCenter = target := by
    dsimp only [sourceCenter]
    exact pureWZ2OffsetProjectiveTotal_apply_inverse hb_ne hS_pos.ne'
      hlambda_pos.ne' target
  let difference : Point3 := source - sourceCenter
  let index : ℤ := Int.floor (difference 1 / r)
  let transverse : ℝ := (index : ℝ) * r
  have himageNorm :
      ‖pureWZ2OffsetProjectiveTotalLinear a b S lambda source - target‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hsource
  have hcoord (coordinate : Fin 3) :
      |(pureWZ2OffsetProjectiveTotalLinear a b S lambda source - target) coordinate| ≤ r := by
    calc
      |(pureWZ2OffsetProjectiveTotalLinear a b S lambda source - target) coordinate| ≤
          ‖pureWZ2OffsetProjectiveTotalLinear a b S lambda source - target‖ := by
        simpa [Real.norm_eq_abs] using
          PiLp.norm_apply_le
            (pureWZ2OffsetProjectiveTotalLinear a b S lambda source - target)
            coordinate
      _ ≤ r := himageNorm
  have hcoord_zero : |lambda * (difference 0 + a * difference 1)| ≤ r := by
    have h := hcoord 0
    rw [← hsourceCenterImage] at h
    have hform :
        lambda * (difference 0 + a * difference 1) =
          lambda * (source 0 + a * source 1) -
            lambda * (sourceCenter 0 + a * sourceCenter 1) := by
      simp [difference]
      ring
    rw [hform]
    simpa [pureWZ2OffsetProjectiveTotalLinear, point3] using h
  have hcoord_one : |b * difference 1| ≤ r := by
    have h := hcoord 1
    rw [← hsourceCenterImage] at h
    simpa [difference, pureWZ2OffsetProjectiveTotalLinear, point3,
      mul_sub] using h
  have hcoord_two : |lambda * S * difference 2| ≤ r := by
    have h := hcoord 2
    rw [← hsourceCenterImage] at h
    simpa [difference, pureWZ2OffsetProjectiveTotalLinear, point3,
      mul_sub] using h
  have hzero : |difference 0 + a * difference 1| ≤ r := by
    rw [abs_mul, abs_of_pos hlambda_pos] at hcoord_zero
    nlinarith [abs_nonneg (difference 0 + a * difference 1)]
  have hone_div : |difference 1| ≤ r / b := by
    rw [abs_mul, abs_of_pos hb] at hcoord_one
    apply (le_div_iff₀ hb).2
    simpa [mul_comm] using hcoord_one
  have htwo : |difference 2| ≤ r := by
    rw [abs_mul, abs_mul, abs_of_pos hlambda_pos, abs_of_pos hS_pos] at hcoord_two
    have hfactor : 1 ≤ lambda * S :=
      one_le_mul_of_one_le_of_one_le hlambda hS
    nlinarith [abs_nonneg (difference 2)]
  have hnormalized_abs : |difference 1 / r| ≤ 1 / b := by
    rw [abs_div, abs_of_pos hr]
    calc
      |difference 1| / r ≤ (r / b) / r :=
        (div_le_div_iff_of_pos_right hr).2 hone_div
      _ = 1 / b := by field_simp [hb.ne', hr.ne']
  have hindex_lower_real : -(indexBound : ℝ) ≤ (index : ℝ) := by
    have hfloor_lower : difference 1 / r - 1 < (index : ℝ) := by
      exact Int.sub_one_lt_floor (difference 1 / r)
    have hnormalized_lower : -(1 / b) ≤ difference 1 / r :=
      (abs_le.mp hnormalized_abs).1
    linarith
  have hindex_upper_real : (index : ℝ) ≤ (indexBound : ℝ) := by
    have hfloor_upper : (index : ℝ) ≤ difference 1 / r :=
      Int.floor_le (difference 1 / r)
    have hnormalized_upper : difference 1 / r ≤ 1 / b :=
      (abs_le.mp hnormalized_abs).2
    linarith
  have hindex_mem : index ∈ indices := by
    simp only [indices, Finset.mem_Icc]
    constructor
    · exact_mod_cast hindex_lower_real
    · exact_mod_cast hindex_upper_real
  have htransverse : |difference 1 - transverse| ≤ r := by
    have hlower : (index : ℝ) ≤ difference 1 / r :=
      Int.floor_le (difference 1 / r)
    have hupper : difference 1 / r < (index : ℝ) + 1 :=
      Int.lt_floor_add_one (difference 1 / r)
    have hlower_scaled : (index : ℝ) * r ≤ difference 1 := by
      have := mul_le_mul_of_nonneg_right hlower hr.le
      field_simp [hr.ne'] at this ⊢
      exact this
    have hupper_scaled : difference 1 < ((index : ℝ) + 1) * r := by
      have := mul_lt_mul_of_pos_right hupper hr
      field_simp [hr.ne'] at this ⊢
      exact this
    rw [abs_le]
    constructor <;> dsimp only [transverse] <;> linarith
  have hcenter_mem : gridCenter index ∈ centers := by
    exact Finset.mem_image.mpr ⟨index, hindex_mem, rfl⟩
  have hzero_center :
      |(source - gridCenter index) 0| ≤ 3 / 2 * r := by
    have hdecompose :
        (source - gridCenter index) 0 =
          (difference 0 + a * difference 1) -
            a * (difference 1 - transverse) := by
      simp [gridCenter, difference, transverse, point3]
      ring
    rw [hdecompose]
    calc
      |(difference 0 + a * difference 1) -
          a * (difference 1 - transverse)| ≤
          |difference 0 + a * difference 1| +
            |a * (difference 1 - transverse)| := abs_sub _ _
      _ ≤ r + (1 / 2) * r := by
        rw [abs_mul]
        gcongr
      _ = 3 / 2 * r := by ring
  have hone_center : |(source - gridCenter index) 1| ≤ r := by
    have heq : (source - gridCenter index) 1 = difference 1 - transverse := by
      simp [gridCenter, difference, transverse, point3]
      ring
    rw [heq]
    exact htransverse
  have htwo_center : |(source - gridCenter index) 2| ≤ r := by
    simpa [gridCenter, difference, point3] using htwo
  let offset := source - gridCenter index
  have hoffset_zero : |offset 0| ≤ 3 / 2 * r := hzero_center
  have hoffset_one : |offset 1| ≤ r := hone_center
  have hoffset_two : |offset 2| ≤ r := htwo_center
  have hoffset_norm : ‖offset‖ ≤ 3 * r := by
    have hnorm_sq := point3_coord_norm_sq offset
    have hzero_sq : (offset 0) ^ 2 ≤ (3 / 2 * r) ^ 2 := by
      rw [sq_le_sq]
      rw [abs_of_pos (mul_pos (by norm_num) hr)]
      exact hoffset_zero
    have hone_sq : (offset 1) ^ 2 ≤ r ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_pos hr] using hoffset_one
    have htwo_sq : (offset 2) ^ 2 ≤ r ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_pos hr] using hoffset_two
    have hsquare : ‖offset‖ ^ 2 ≤ (3 * r) ^ 2 := by
      rw [hnorm_sq]
      calc
        (offset 0) ^ 2 + (offset 1) ^ 2 + (offset 2) ^ 2 ≤
            (3 / 2 * r) ^ 2 + r ^ 2 + r ^ 2 := by gcongr
        _ ≤ (3 * r) ^ 2 := by nlinarith [sq_nonneg r]
    exact (sq_le_sq₀ (norm_nonneg offset)
      (mul_nonneg (by norm_num) hr.le)).mp hsquare
  have hcenter_dist : dist source (gridCenter index) ≤ 3 * r := by
    simpa [offset, dist_eq_norm] using hoffset_norm
  rw [Set.mem_iUnion]
  refine ⟨gridCenter index, ?_⟩
  rw [Set.mem_iUnion]
  exact ⟨hcenter_mem, hcenter_dist⟩

/-- Sharp zero-centered form of the offset-diagonal preimage cover.  A grid
with step `r / 2` in the contracted source coordinate gives radius
`7 * r / 4` and at most `9 * b⁻¹` centers. -/
theorem pureWZ2OffsetProjectiveTotal_preimage_zero_closedBall_sharp_finite_cover
    {a b S lambda r : ℝ}
    (ha : |a| ≤ 1 / 2) (hb : 0 < b) (hb_one : b ≤ 1)
    (hS : 1 ≤ S) (hlambda : 1 ≤ lambda) (hr : 0 < r) :
    ∃ centers : Finset Point3,
      (centers.card : ℝ) ≤ 9 * b⁻¹ ∧
      pureWZ2OffsetProjectiveTotalLinear a b S lambda ⁻¹'
          Metric.closedBall (0 : Point3) r ⊆
        ⋃ center ∈ centers, Metric.closedBall center (7 * r / 4) := by
  let step : ℝ := r / 2
  let indexBound : ℤ := Nat.ceil (2 / b + 1)
  let indices : Finset ℤ := Finset.Icc (-indexBound) indexBound
  let gridCenter : ℤ → Point3 := fun index =>
    point3 (-a * ((index : ℝ) * step)) ((index : ℝ) * step) 0
  let centers : Finset Point3 := indices.image gridCenter
  have hstep : 0 < step := by positivity
  have hS_pos : 0 < S := zero_lt_one.trans_le hS
  have hlambda_pos : 0 < lambda := zero_lt_one.trans_le hlambda
  have hbound_nonneg : 0 ≤ indexBound := by
    dsimp only [indexBound]
    exact_mod_cast Nat.zero_le (Nat.ceil (2 / b + 1))
  have hbound_real : 2 / b + 1 ≤ (indexBound : ℝ) := by
    dsimp only [indexBound]
    exact Nat.le_ceil (2 / b + 1)
  have hbound_lt : (indexBound : ℝ) < 2 / b + 2 := by
    have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 / b + 1)
    have hcast : (indexBound : ℝ) = (Nat.ceil (2 / b + 1) : ℝ) := by
      simp [indexBound]
    rw [hcast]
    linarith
  have hcard_indices : (indices.card : ℤ) = 2 * indexBound + 1 := by
    dsimp only [indices]
    rw [Int.card_Icc_of_le]
    · ring
    · omega
  have hcard_centers : (centers.card : ℝ) ≤ 2 * (indexBound : ℝ) + 1 := by
    have hcard_nat : centers.card ≤ indices.card := Finset.card_image_le
    have hcard_int : (centers.card : ℤ) ≤ 2 * indexBound + 1 := by
      calc
        (centers.card : ℤ) ≤ (indices.card : ℤ) := by exact_mod_cast hcard_nat
        _ = 2 * indexBound + 1 := hcard_indices
    exact_mod_cast hcard_int
  have hcard : (centers.card : ℝ) ≤ 9 * b⁻¹ := by
    calc
      (centers.card : ℝ) ≤ 2 * (indexBound : ℝ) + 1 := hcard_centers
      _ ≤ 9 * b⁻¹ := by
        have hinv_one : 1 ≤ b⁻¹ := by
          rw [one_le_inv₀ hb]
          exact hb_one
        have hbound_le : (indexBound : ℝ) ≤ 2 / b + 2 := hbound_lt.le
        rw [div_eq_mul_inv] at hbound_le
        nlinarith
  refine ⟨centers, hcard, ?_⟩
  intro source hsource
  have himageNorm :
      ‖pureWZ2OffsetProjectiveTotalLinear a b S lambda source‖ ≤ r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hsource
  have hcoord (coordinate : Fin 3) :
      |pureWZ2OffsetProjectiveTotalLinear a b S lambda source coordinate| ≤ r := by
    calc
      |pureWZ2OffsetProjectiveTotalLinear a b S lambda source coordinate| ≤
          ‖pureWZ2OffsetProjectiveTotalLinear a b S lambda source‖ := by
        simpa [Real.norm_eq_abs] using
          PiLp.norm_apply_le
            (pureWZ2OffsetProjectiveTotalLinear a b S lambda source) coordinate
      _ ≤ r := himageNorm
  have hcoord_zero : |lambda * (source 0 + a * source 1)| ≤ r := by
    simpa [pureWZ2OffsetProjectiveTotalLinear, point3] using hcoord 0
  have hcoord_one : |b * source 1| ≤ r := by
    simpa [pureWZ2OffsetProjectiveTotalLinear, point3] using hcoord 1
  have hcoord_two : |lambda * S * source 2| ≤ r := by
    simpa [pureWZ2OffsetProjectiveTotalLinear, point3] using hcoord 2
  have hzero : |source 0 + a * source 1| ≤ r := by
    rw [abs_mul, abs_of_pos hlambda_pos] at hcoord_zero
    nlinarith [abs_nonneg (source 0 + a * source 1)]
  have hone_div : |source 1| ≤ r / b := by
    rw [abs_mul, abs_of_pos hb] at hcoord_one
    apply (le_div_iff₀ hb).2
    simpa [mul_comm] using hcoord_one
  have htwo : |source 2| ≤ r := by
    rw [abs_mul, abs_mul, abs_of_pos hlambda_pos, abs_of_pos hS_pos] at hcoord_two
    have hfactor : 1 ≤ lambda * S :=
      one_le_mul_of_one_le_of_one_le hlambda hS
    nlinarith [abs_nonneg (source 2)]
  let index : ℤ := Int.floor (source 1 / step)
  let transverse : ℝ := (index : ℝ) * step
  have hnormalized_abs : |source 1 / step| ≤ 2 / b := by
    rw [abs_div, abs_of_pos hstep]
    calc
      |source 1| / step ≤ (r / b) / step :=
        (div_le_div_iff_of_pos_right hstep).2 hone_div
      _ = 2 / b := by
        dsimp only [step]
        field_simp [hb.ne', hr.ne']
  have hindex_lower_real : -(indexBound : ℝ) ≤ (index : ℝ) := by
    have hfloor_lower : source 1 / step - 1 < (index : ℝ) :=
      Int.sub_one_lt_floor (source 1 / step)
    have hnormalized_lower : -(2 / b) ≤ source 1 / step :=
      (abs_le.mp hnormalized_abs).1
    linarith
  have hindex_upper_real : (index : ℝ) ≤ (indexBound : ℝ) := by
    have hfloor_upper : (index : ℝ) ≤ source 1 / step :=
      Int.floor_le (source 1 / step)
    have hnormalized_upper : source 1 / step ≤ 2 / b :=
      (abs_le.mp hnormalized_abs).2
    linarith
  have hindex_mem : index ∈ indices := by
    simp only [indices, Finset.mem_Icc]
    constructor
    · exact_mod_cast hindex_lower_real
    · exact_mod_cast hindex_upper_real
  have htransverse : |source 1 - transverse| ≤ step := by
    have hlower : (index : ℝ) ≤ source 1 / step :=
      Int.floor_le (source 1 / step)
    have hupper : source 1 / step < (index : ℝ) + 1 :=
      Int.lt_floor_add_one (source 1 / step)
    have hlower_scaled : (index : ℝ) * step ≤ source 1 := by
      have := mul_le_mul_of_nonneg_right hlower hstep.le
      field_simp [hstep.ne'] at this ⊢
      exact this
    have hupper_scaled : source 1 < ((index : ℝ) + 1) * step := by
      have := mul_lt_mul_of_pos_right hupper hstep
      field_simp [hstep.ne'] at this ⊢
      exact this
    rw [abs_le]
    constructor <;> dsimp only [transverse] <;> linarith
  have hcenter_mem : gridCenter index ∈ centers :=
    Finset.mem_image.mpr ⟨index, hindex_mem, rfl⟩
  have hzero_center : |(source - gridCenter index) 0| ≤ 5 * r / 4 := by
    have hdecompose :
        (source - gridCenter index) 0 =
          (source 0 + a * source 1) - a * (source 1 - transverse) := by
      simp [gridCenter, transverse, point3]
      ring
    rw [hdecompose]
    calc
      |(source 0 + a * source 1) - a * (source 1 - transverse)| ≤
          |source 0 + a * source 1| + |a * (source 1 - transverse)| :=
        abs_sub _ _
      _ ≤ r + (1 / 2) * step := by
        rw [abs_mul]
        gcongr
      _ = 5 * r / 4 := by simp [step]; ring
  have hone_center : |(source - gridCenter index) 1| ≤ r / 2 := by
    have heq : (source - gridCenter index) 1 = source 1 - transverse := by
      simp [gridCenter, transverse, point3]
    rw [heq]
    simpa [step] using htransverse
  have htwo_center : |(source - gridCenter index) 2| ≤ r := by
    simpa [gridCenter, point3] using htwo
  let offset := source - gridCenter index
  have hoffset_zero : |offset 0| ≤ 5 * r / 4 := hzero_center
  have hoffset_one : |offset 1| ≤ r / 2 := hone_center
  have hoffset_two : |offset 2| ≤ r := htwo_center
  have hoffset_norm : ‖offset‖ ≤ 7 * r / 4 := by
    have hnorm_sq := point3_coord_norm_sq offset
    have hzero_sq : (offset 0) ^ 2 ≤ (5 * r / 4) ^ 2 := by
      rw [sq_le_sq, abs_of_pos (by positivity : 0 < 5 * r / 4)]
      exact hoffset_zero
    have hone_sq : (offset 1) ^ 2 ≤ (r / 2) ^ 2 := by
      rw [sq_le_sq, abs_of_pos (by positivity : 0 < r / 2)]
      exact hoffset_one
    have htwo_sq : (offset 2) ^ 2 ≤ r ^ 2 := by
      rw [sq_le_sq, abs_of_pos hr]
      exact hoffset_two
    have hsquare : ‖offset‖ ^ 2 ≤ (7 * r / 4) ^ 2 := by
      rw [hnorm_sq]
      calc
        (offset 0) ^ 2 + (offset 1) ^ 2 + (offset 2) ^ 2 ≤
            (5 * r / 4) ^ 2 + (r / 2) ^ 2 + r ^ 2 := by gcongr
        _ ≤ (7 * r / 4) ^ 2 := by nlinarith [sq_nonneg r]
    exact (sq_le_sq₀ (norm_nonneg offset) (by positivity)).mp hsquare
  have hcenter_dist : dist source (gridCenter index) ≤ 7 * r / 4 := by
    simpa [offset, dist_eq_norm] using hoffset_norm
  rw [Set.mem_iUnion]
  refine ⟨gridCenter index, ?_⟩
  rw [Set.mem_iUnion]
  exact ⟨hcenter_mem, hcenter_dist⟩

/-- The square-root-scale specialization used by the large-slope argument.
The cardinality bound is independent of `rho`. -/
theorem pureWZ2OffsetProjectiveTotal_preimage_sqrtBall_finite_cover
    {a b S lambda rho : ℝ}
    (ha : |a| ≤ 1 / 2) (hb : 0 < b) (hb_one : b ≤ 1)
    (hS : 1 ≤ S) (hlambda : 1 ≤ lambda) (hrho : 0 < rho)
    (target : Point3) :
    ∃ centers : Finset Point3,
      (centers.card : ℝ) ≤ 7 * b⁻¹ ∧
      pureWZ2OffsetProjectiveTotalLinear a b S lambda ⁻¹'
          Metric.closedBall target (Real.sqrt rho) ⊆
        ⋃ center ∈ centers,
          Metric.closedBall center (3 * Real.sqrt rho) := by
  exact pureWZ2OffsetProjectiveTotal_preimage_closedBall_finite_cover
    ha hb hb_one hS hlambda (Real.sqrt_pos.2 hrho) target

/-- Translation-invariant form of the finite-cover theorem.  The map `F`
may contain arbitrary source and target translations: the only required
interface is that differences from the chosen center are given by the
offset-diagonal linear map.  This is the form intended for direct
instantiation by affine terminal maps. -/
theorem pureWZ2OffsetProjectiveTotal_difference_preimage_closedBall_finite_cover
    {F : Point3 → Point3} {a b S lambda r : ℝ}
    (ha : |a| ≤ 1 / 2) (hb : 0 < b) (hb_one : b ≤ 1)
    (hS : 1 ≤ S) (hlambda : 1 ≤ lambda) (hr : 0 < r)
    (center : Point3)
    (hdifference : ∀ point,
      F point - F center =
        pureWZ2OffsetProjectiveTotalLinear a b S lambda
          (point - center)) :
    ∃ centers : Finset Point3,
      (centers.card : ℝ) ≤ 7 * b⁻¹ ∧
      F ⁻¹' Metric.closedBall (F center) r ⊆
        ⋃ sourceCenter ∈ centers,
          Metric.closedBall sourceCenter (3 * r) := by
  rcases pureWZ2OffsetProjectiveTotal_preimage_closedBall_finite_cover
      ha hb hb_one hS hlambda hr (0 : Point3) with
    ⟨differenceCenters, hcard, hcover⟩
  let centers : Finset Point3 :=
    differenceCenters.image (fun differenceCenter => center + differenceCenter)
  have hcentersCard : centers.card ≤ differenceCenters.card := by
    exact Finset.card_image_le
  refine ⟨centers, ?_, ?_⟩
  · have hcentersCardReal :
        (centers.card : ℝ) ≤ (differenceCenters.card : ℝ) := by
      exact_mod_cast hcentersCard
    exact hcentersCardReal.trans hcard
  · intro point hpoint
    have hdifferenceMem : point - center ∈
        pureWZ2OffsetProjectiveTotalLinear a b S lambda ⁻¹'
          Metric.closedBall (0 : Point3) r := by
      have himage :
          ‖pureWZ2OffsetProjectiveTotalLinear a b S lambda
              (point - center)‖ ≤ r := by
        rw [← hdifference point]
        simpa [Metric.mem_closedBall, dist_eq_norm] using hpoint
      simpa [Metric.mem_closedBall, dist_eq_norm] using himage
    have hdifferenceCovered := hcover hdifferenceMem
    rw [Set.mem_iUnion] at hdifferenceCovered
    rcases hdifferenceCovered with ⟨differenceCenter, hdifferenceCovered⟩
    rw [Set.mem_iUnion] at hdifferenceCovered
    rcases hdifferenceCovered with
      ⟨hdifferenceCenter, hdifferenceBall⟩
    have hsourceCenter : center + differenceCenter ∈ centers := by
      exact Finset.mem_image.mpr
        ⟨differenceCenter, hdifferenceCenter, rfl⟩
    have hsourceBall :
        point ∈ Metric.closedBall (center + differenceCenter) (3 * r) := by
      have hdist :
          dist point (center + differenceCenter) =
            dist (point - center) differenceCenter := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        abel
      rw [Metric.mem_closedBall, hdist]
      exact hdifferenceBall
    rw [Set.mem_iUnion]
    refine ⟨center + differenceCenter, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨hsourceCenter, hsourceBall⟩

/-- Sharp translation-invariant cover for an affine terminal map whose
difference map is `pureWZ2OffsetProjectiveTotalLinear`. -/
theorem pureWZ2OffsetProjectiveTotal_difference_preimage_closedBall_sharp_finite_cover
    {F : Point3 → Point3} {a b S lambda r : ℝ}
    (ha : |a| ≤ 1 / 2) (hb : 0 < b) (hb_one : b ≤ 1)
    (hS : 1 ≤ S) (hlambda : 1 ≤ lambda) (hr : 0 < r)
    (center : Point3)
    (hdifference : ∀ point,
      F point - F center =
        pureWZ2OffsetProjectiveTotalLinear a b S lambda
          (point - center)) :
    ∃ centers : Finset Point3,
      (centers.card : ℝ) ≤ 9 * b⁻¹ ∧
      F ⁻¹' Metric.closedBall (F center) r ⊆
        ⋃ sourceCenter ∈ centers,
          Metric.closedBall sourceCenter (7 * r / 4) := by
  rcases pureWZ2OffsetProjectiveTotal_preimage_zero_closedBall_sharp_finite_cover
      ha hb hb_one hS hlambda hr with
    ⟨differenceCenters, hcard, hcover⟩
  let centers : Finset Point3 :=
    differenceCenters.image (fun differenceCenter => center + differenceCenter)
  have hcentersCard : centers.card ≤ differenceCenters.card :=
    Finset.card_image_le
  refine ⟨centers, ?_, ?_⟩
  · have hcentersCardReal :
        (centers.card : ℝ) ≤ (differenceCenters.card : ℝ) := by
      exact_mod_cast hcentersCard
    exact hcentersCardReal.trans hcard
  · intro point hpoint
    have hdifferenceMem : point - center ∈
        pureWZ2OffsetProjectiveTotalLinear a b S lambda ⁻¹'
          Metric.closedBall (0 : Point3) r := by
      have himage :
          ‖pureWZ2OffsetProjectiveTotalLinear a b S lambda
              (point - center)‖ ≤ r := by
        rw [← hdifference point]
        simpa [Metric.mem_closedBall, dist_eq_norm] using hpoint
      simpa [Metric.mem_closedBall, dist_eq_norm] using himage
    have hdifferenceCovered := hcover hdifferenceMem
    rw [Set.mem_iUnion] at hdifferenceCovered
    rcases hdifferenceCovered with ⟨differenceCenter, hdifferenceCovered⟩
    rw [Set.mem_iUnion] at hdifferenceCovered
    rcases hdifferenceCovered with
      ⟨hdifferenceCenter, hdifferenceBall⟩
    have hsourceCenter : center + differenceCenter ∈ centers :=
      Finset.mem_image.mpr ⟨differenceCenter, hdifferenceCenter, rfl⟩
    have hsourceBall :
        point ∈ Metric.closedBall
          (center + differenceCenter) (7 * r / 4) := by
      have hdist :
          dist point (center + differenceCenter) =
            dist (point - center) differenceCenter := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        abel
      rw [Metric.mem_closedBall, hdist]
      exact hdifferenceBall
    rw [Set.mem_iUnion]
    refine ⟨center + differenceCenter, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨hsourceCenter, hsourceBall⟩

/-- Square-root-scale sharp translation-invariant cover.  It uses at most
`9 * b⁻¹` source balls of radius `7 * sqrt rho / 4`. -/
theorem pureWZ2OffsetProjectiveTotal_difference_preimage_sqrtBall_sharp_finite_cover
    {F : Point3 → Point3} {a b S lambda rho : ℝ}
    (ha : |a| ≤ 1 / 2) (hb : 0 < b) (hb_one : b ≤ 1)
    (hS : 1 ≤ S) (hlambda : 1 ≤ lambda) (hrho : 0 < rho)
    (center : Point3)
    (hdifference : ∀ point,
      F point - F center =
        pureWZ2OffsetProjectiveTotalLinear a b S lambda
          (point - center)) :
    ∃ centers : Finset Point3,
      (centers.card : ℝ) ≤ 9 * b⁻¹ ∧
      F ⁻¹' Metric.closedBall (F center) (Real.sqrt rho) ⊆
        ⋃ sourceCenter ∈ centers,
          Metric.closedBall
            sourceCenter (7 * Real.sqrt rho / 4) := by
  exact
    pureWZ2OffsetProjectiveTotal_difference_preimage_closedBall_sharp_finite_cover
      ha hb hb_one hS hlambda (Real.sqrt_pos.2 hrho) center hdifference

/-- Square-root-scale specialization of the translation-invariant theorem.
Its number of source balls remains independent of `rho`. -/
theorem pureWZ2OffsetProjectiveTotal_difference_preimage_sqrtBall_finite_cover
    {F : Point3 → Point3} {a b S lambda rho : ℝ}
    (ha : |a| ≤ 1 / 2) (hb : 0 < b) (hb_one : b ≤ 1)
    (hS : 1 ≤ S) (hlambda : 1 ≤ lambda) (hrho : 0 < rho)
    (center : Point3)
    (hdifference : ∀ point,
      F point - F center =
        pureWZ2OffsetProjectiveTotalLinear a b S lambda
          (point - center)) :
    ∃ centers : Finset Point3,
      (centers.card : ℝ) ≤ 7 * b⁻¹ ∧
      F ⁻¹' Metric.closedBall (F center) (Real.sqrt rho) ⊆
        ⋃ sourceCenter ∈ centers,
          Metric.closedBall sourceCenter (3 * Real.sqrt rho) := by
  exact
    pureWZ2OffsetProjectiveTotal_difference_preimage_closedBall_finite_cover
      ha hb hb_one hS hlambda (Real.sqrt_pos.2 hrho) center hdifference

end Kakeya.Assouad

end
