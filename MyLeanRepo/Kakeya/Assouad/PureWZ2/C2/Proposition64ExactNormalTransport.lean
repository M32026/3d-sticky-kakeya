import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64ExactMapFactorization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64TubeTransport

/-!
# Exact normal transport for Proposition 6.4

This file records the inverse and inverse-transpose formulas for the exact
affine map in Proposition 6.4.  In particular, the local plane normal is
transported together with the tube direction.  No rotation or replacement
of the source normal is used.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Explicit inverse of the translated Proposition 6.4 map. -/
def pureWZ2Proposition64TranslatedInverse
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation point : Point3) : Point3 :=
  point3
    (normalization * (point 0 - translation 0) -
      g anchorHeight * (point 1 - translation 1))
    (point 1 - translation 1)
    (slabCenter + halfHeight * (point 2 - translation 2))

theorem pureWZ2Proposition64TranslatedMap_inverse
    (g : ℝ → ℝ) (slabCenter anchorHeight : ℝ)
    {halfHeight normalization : ℝ}
    (translation point : Point3)
    (hhalfHeight : halfHeight ≠ 0)
    (hnormalization : normalization ≠ 0) :
    pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
        normalization translation
        (pureWZ2Proposition64TranslatedInverse g slabCenter anchorHeight
          halfHeight normalization translation point) = point := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2Proposition64TranslatedMap,
      pureWZ2Proposition64TranslatedInverse,
      pureWZ2Proposition64Map, point3] <;>
    field_simp [hhalfHeight, hnormalization] <;> ring

theorem pureWZ2Proposition64TranslatedInverse_map
    (g : ℝ → ℝ) (slabCenter anchorHeight : ℝ)
    {halfHeight normalization : ℝ}
    (translation point : Point3)
    (hhalfHeight : halfHeight ≠ 0)
    (hnormalization : normalization ≠ 0) :
    pureWZ2Proposition64TranslatedInverse g slabCenter anchorHeight halfHeight
        normalization translation
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation point) = point := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2Proposition64TranslatedMap,
      pureWZ2Proposition64TranslatedInverse,
      pureWZ2Proposition64Map, point3] <;>
    field_simp [hhalfHeight, hnormalization] <;> ring

/-- Differences under the explicit inverse. -/
theorem pureWZ2Proposition64TranslatedInverse_sub
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation first second : Point3) :
    pureWZ2Proposition64TranslatedInverse g slabCenter anchorHeight halfHeight
        normalization translation first -
      pureWZ2Proposition64TranslatedInverse g slabCenter anchorHeight halfHeight
        normalization translation second =
      point3
        (normalization * (first - second) 0 -
          g anchorHeight * (first - second) 1)
        ((first - second) 1)
        (halfHeight * (first - second) 2) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2Proposition64TranslatedInverse, point3] <;> ring

/-- The inverse of the exact map has a scale-independent Lipschitz bound once
the fixed horizontal normalization is exposed. -/
theorem pureWZ2Proposition64TranslatedInverse_norm_sub_le
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation first second : Point3)
    (hhalfHeight : |halfHeight| ≤ 1)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hnormalization : 9 ≤ normalization) :
    ‖pureWZ2Proposition64TranslatedInverse g slabCenter anchorHeight
          halfHeight normalization translation first -
        pureWZ2Proposition64TranslatedInverse g slabCenter anchorHeight
          halfHeight normalization translation second‖ ≤
      3 * normalization * ‖first - second‖ := by
  let difference := first - second
  let inverseDifference := point3
    (normalization * difference 0 - g anchorHeight * difference 1)
    (difference 1) (halfHeight * difference 2)
  have hnormalizationPos : 0 < normalization := by linarith
  have hcoord (coordinate : Fin 3) :
      |difference coordinate| ≤ ‖difference‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le difference coordinate
  have hfirst : |inverseDifference 0| ≤
      2 * normalization * ‖difference‖ := by
    have hraw :
        |normalization * difference 0 - g anchorHeight * difference 1| ≤
          normalization * |difference 0| +
            |g anchorHeight| * |difference 1| := by
      calc
        _ ≤ |normalization * difference 0| +
              |g anchorHeight * difference 1| := abs_sub _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_pos hnormalizationPos]
    have hsum : normalization + 8 ≤ 2 * normalization := by linarith
    have hbound := hraw.trans <| calc
      normalization * |difference 0| +
            |g anchorHeight| * |difference 1| ≤
          normalization * ‖difference‖ + 8 * ‖difference‖ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hcoord 0) hnormalizationPos.le)
          (mul_le_mul hanchorSlope (hcoord 1) (abs_nonneg _) (by norm_num))
      _ = (normalization + 8) * ‖difference‖ := by ring
      _ ≤ 2 * normalization * ‖difference‖ := by
        exact mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
    simpa [inverseDifference, point3] using hbound
  have hsecond : |inverseDifference 1| ≤ ‖difference‖ := by
    simpa [inverseDifference, point3] using hcoord (1 : Fin 3)
  have hthird : |inverseDifference 2| ≤ ‖difference‖ := by
    rw [show inverseDifference 2 = halfHeight * difference 2 by
      simp [inverseDifference, point3], abs_mul]
    calc
      |halfHeight| * |difference 2| ≤ 1 * ‖difference‖ := by
        exact mul_le_mul hhalfHeight (hcoord 2) (abs_nonneg _) (by norm_num)
      _ = ‖difference‖ := by ring
  have hfirstSq : inverseDifference 0 ^ 2 ≤
      (2 * normalization * ‖difference‖) ^ 2 := by
    nlinarith [abs_nonneg (inverseDifference 0), sq_abs (inverseDifference 0)]
  have hsecondSq : inverseDifference 1 ^ 2 ≤ ‖difference‖ ^ 2 := by
    nlinarith [abs_nonneg (inverseDifference 1), sq_abs (inverseDifference 1)]
  have hthirdSq : inverseDifference 2 ^ 2 ≤ ‖difference‖ ^ 2 := by
    nlinarith [abs_nonneg (inverseDifference 2), sq_abs (inverseDifference 2)]
  have hinverseSq : ‖inverseDifference‖ ^ 2 ≤
      (3 * normalization * ‖difference‖) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
    have hnormalizationSq : 1 ≤ normalization ^ 2 := by nlinarith
    nlinarith [sq_nonneg normalization, sq_nonneg (‖difference‖)]
  have hfinal : ‖inverseDifference‖ ≤
      3 * normalization * ‖difference‖ := by
    have hrhsNonneg : 0 ≤ 3 * normalization * ‖difference‖ :=
      mul_nonneg
        (mul_nonneg (by norm_num) hnormalizationPos.le)
        (norm_nonneg difference)
    nlinarith [norm_nonneg inverseDifference, hrhsNonneg]
  rw [pureWZ2Proposition64TranslatedInverse_sub]
  simpa only [difference, inverseDifference] using hfinal

/-- Metric form of the inverse Lipschitz estimate. -/
theorem pureWZ2Proposition64TranslatedInverse_dist_le
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation first second : Point3)
    (hhalfHeight : |halfHeight| ≤ 1)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hnormalization : 9 ≤ normalization) :
    dist
        (pureWZ2Proposition64TranslatedInverse g slabCenter anchorHeight
          halfHeight normalization translation first)
        (pureWZ2Proposition64TranslatedInverse g slabCenter anchorHeight
          halfHeight normalization translation second) ≤
      3 * normalization * dist first second := by
  simpa only [dist_eq_norm] using
    pureWZ2Proposition64TranslatedInverse_norm_sub_le g slabCenter
      anchorHeight halfHeight normalization translation first second
      hhalfHeight hanchorSlope hnormalization

/-- Global Lipschitz packaging of the explicit inverse. -/
theorem pureWZ2Proposition64TranslatedInverse_lipschitz
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : |halfHeight| ≤ 1)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hnormalization : 9 ≤ normalization) :
    LipschitzWith
      ⟨3 * normalization,
        mul_nonneg (by norm_num) (by linarith : 0 ≤ normalization)⟩
      (pureWZ2Proposition64TranslatedInverse g slabCenter anchorHeight
        halfHeight normalization translation) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  exact pureWZ2Proposition64TranslatedInverse_dist_le g slabCenter
    anchorHeight halfHeight normalization translation first second
    hhalfHeight hanchorSlope hnormalization

/-- Inverse transpose of the linear part of the exact Proposition 6.4 map. -/
def pureWZ2Proposition64InverseTranspose
    (anchorSlope halfHeight normalization : ℝ) (normal : Point3) : Point3 :=
  point3
    (normalization * normal 0)
    (normal 1 - anchorSlope * normal 0)
    (halfHeight * normal 2)

/-- Linear-map packaging of the inverse transpose. -/
def pureWZ2Proposition64InverseTransposeLinear
    (anchorSlope halfHeight normalization : ℝ) : Point3 →ₗ[ℝ] Point3 where
  toFun := pureWZ2Proposition64InverseTranspose
    anchorSlope halfHeight normalization
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2Proposition64InverseTranspose, point3] <;> ring
  map_smul' scalar normal := by
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2Proposition64InverseTranspose, point3] <;> ring

/-- Fixed operator bound for the inverse transpose. -/
theorem pureWZ2Proposition64InverseTranspose_norm_le
    {anchorSlope halfHeight normalization : ℝ}
    (hhalfHeight : |halfHeight| ≤ 1)
    (hanchorSlope : |anchorSlope| ≤ 8)
    (hnormalization : 9 ≤ normalization)
    (normal : Point3) :
    ‖pureWZ2Proposition64InverseTranspose anchorSlope halfHeight
        normalization normal‖ ≤ 3 * normalization * ‖normal‖ := by
  let transported := pureWZ2Proposition64InverseTranspose
    anchorSlope halfHeight normalization normal
  have hnormalizationPos : 0 < normalization := by linarith
  have hcoord (coordinate : Fin 3) : |normal coordinate| ≤ ‖normal‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le normal coordinate
  have hzero : |transported 0| ≤ normalization * ‖normal‖ := by
    have hcoordinate : transported 0 = normalization * normal 0 := by
      simp [transported, pureWZ2Proposition64InverseTranspose, point3]
    rw [hcoordinate]
    rw [abs_mul, abs_of_pos hnormalizationPos]
    exact mul_le_mul_of_nonneg_left (hcoord 0) hnormalizationPos.le
  have hone : |transported 1| ≤ 9 * ‖normal‖ := by
    have hcoordinate : transported 1 = normal 1 - anchorSlope * normal 0 := by
      simp [transported, pureWZ2Proposition64InverseTranspose, point3]
    rw [hcoordinate]
    calc
      |normal 1 - anchorSlope * normal 0| ≤
          |normal 1| + |anchorSlope| * |normal 0| := by
        simpa [abs_mul] using abs_sub (normal 1) (anchorSlope * normal 0)
      _ ≤ ‖normal‖ + 8 * ‖normal‖ := by
        exact add_le_add (hcoord 1)
          (mul_le_mul hanchorSlope (hcoord 0) (abs_nonneg _) (by norm_num))
      _ = 9 * ‖normal‖ := by ring
  have htwo : |transported 2| ≤ ‖normal‖ := by
    have hcoordinate : transported 2 = halfHeight * normal 2 := by
      simp [transported, pureWZ2Proposition64InverseTranspose, point3]
    rw [hcoordinate]
    rw [abs_mul]
    calc
      |halfHeight| * |normal 2| ≤ 1 * ‖normal‖ := by
        exact mul_le_mul hhalfHeight (hcoord 2) (abs_nonneg _) (by norm_num)
      _ = ‖normal‖ := by ring
  have hzeroSq : transported 0 ^ 2 ≤
      (normalization * ‖normal‖) ^ 2 := by
    nlinarith [abs_nonneg (transported 0), sq_abs (transported 0)]
  have honeSq : transported 1 ^ 2 ≤ (9 * ‖normal‖) ^ 2 := by
    nlinarith [abs_nonneg (transported 1), sq_abs (transported 1)]
  have htwoSq : transported 2 ^ 2 ≤ ‖normal‖ ^ 2 := by
    nlinarith [abs_nonneg (transported 2), sq_abs (transported 2)]
  have hnormSq : ‖transported‖ ^ 2 ≤
      (3 * normalization * ‖normal‖) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
    have hnormalizationSq : 81 ≤ normalization ^ 2 := by nlinarith
    nlinarith [sq_nonneg normalization, sq_nonneg (‖normal‖)]
  have hfinal : ‖transported‖ ≤ 3 * normalization * ‖normal‖ := by
    have hrhsNonneg : 0 ≤ 3 * normalization * ‖normal‖ :=
      mul_nonneg
        (mul_nonneg (by norm_num) hnormalizationPos.le)
        (norm_nonneg normal)
    nlinarith [norm_nonneg transported, hrhsNonneg]
  exact hfinal

/-- Global Lipschitz packaging of the inverse-transpose estimate. -/
theorem pureWZ2Proposition64InverseTranspose_lipschitz
    {anchorSlope halfHeight normalization : ℝ}
    (hhalfHeight : |halfHeight| ≤ 1)
    (hanchorSlope : |anchorSlope| ≤ 8)
    (hnormalization : 9 ≤ normalization) :
    LipschitzWith
      ⟨3 * normalization,
        mul_nonneg (by norm_num) (by linarith : 0 ≤ normalization)⟩
      (pureWZ2Proposition64InverseTranspose anchorSlope halfHeight
        normalization) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [dist_eq_norm, dist_eq_norm]
  have hsub :=
    (pureWZ2Proposition64InverseTransposeLinear anchorSlope halfHeight
      normalization).map_sub first second
  change pureWZ2Proposition64InverseTranspose anchorSlope halfHeight
      normalization (first - second) =
    pureWZ2Proposition64InverseTranspose anchorSlope halfHeight
        normalization first -
      pureWZ2Proposition64InverseTranspose anchorSlope halfHeight
        normalization second at hsub
  rw [← hsub]
  exact_mod_cast
    pureWZ2Proposition64InverseTranspose_norm_le
      hhalfHeight hanchorSlope hnormalization (first - second)

@[simp] theorem pureWZ2Proposition64InverseTranspose_apply_zero
    (anchorSlope halfHeight normalization : ℝ) (normal : Point3) :
    pureWZ2Proposition64InverseTranspose anchorSlope halfHeight
        normalization normal 0 = normalization * normal 0 := by
  simp [pureWZ2Proposition64InverseTranspose, point3]

@[simp] theorem pureWZ2Proposition64InverseTranspose_apply_one
    (anchorSlope halfHeight normalization : ℝ) (normal : Point3) :
    pureWZ2Proposition64InverseTranspose anchorSlope halfHeight
        normalization normal 1 = normal 1 - anchorSlope * normal 0 := by
  simp [pureWZ2Proposition64InverseTranspose, point3]

@[simp] theorem pureWZ2Proposition64InverseTranspose_apply_two
    (anchorSlope halfHeight normalization : ℝ) (normal : Point3) :
    pureWZ2Proposition64InverseTranspose anchorSlope halfHeight
        normalization normal 2 = halfHeight * normal 2 := by
  simp [pureWZ2Proposition64InverseTranspose, point3]

/-- Exact covariance of directions and plane normals. -/
theorem pureWZ2Proposition64Linear_inner_inverseTranspose
    {halfHeight normalization : ℝ}
    (anchorSlope : ℝ)
    (hhalfHeight : halfHeight ≠ 0)
    (hnormalization : normalization ≠ 0)
    (direction normal : Point3) :
    inner ℝ
        (pureWZ2Proposition64Linear anchorSlope halfHeight normalization
          direction)
        (pureWZ2Proposition64InverseTranspose anchorSlope halfHeight
          normalization normal) =
      inner ℝ direction normal := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ,
    pureWZ2Proposition64Linear,
    pureWZ2Proposition64InverseTranspose, point3]
  field_simp [hhalfHeight, hnormalization]
  ring

/-- The inverse-transpose image of a unit source normal with controlled
vertical component stays uniformly away from zero.  The bound is absolute
under the fixed Proposition 6.4 bounds on the shear and normalization. -/
theorem pureWZ2Proposition64InverseTranspose_norm_lower
    {anchorSlope halfHeight normalization : ℝ}
    (hanchorSlope : |anchorSlope| ≤ 8)
    (hnormalization : 9 ≤ normalization)
    {normal : Point3}
    (hnormalUnit : ‖normal‖ = 1)
    (hnormalVertical : |normal 2| ≤ 1 / 2) :
    (1 / 4 : ℝ) ≤
      ‖pureWZ2Proposition64InverseTranspose anchorSlope halfHeight
        normalization normal‖ := by
  let transported := pureWZ2Proposition64InverseTranspose
    anchorSlope halfHeight normalization normal
  have htransportedNonneg : 0 ≤ ‖transported‖ := norm_nonneg _
  have hzero : |transported 0| ≤ ‖transported‖ := by
    simpa [Real.norm_eq_abs] using
      (PiLp.norm_apply_le transported (0 : Fin 3))
  have hone : |transported 1| ≤ ‖transported‖ := by
    simpa [Real.norm_eq_abs] using
      (PiLp.norm_apply_le transported (1 : Fin 3))
  have hnormalizationPos : 0 < normalization := by linarith
  have hnzero : |normal 0| ≤ ‖transported‖ / 9 := by
    have hcoord : transported 0 = normalization * normal 0 := by
      simp [transported]
    have hmul : 9 * |normal 0| ≤ |transported 0| := by
      rw [hcoord, abs_mul, abs_of_pos hnormalizationPos]
      exact mul_le_mul_of_nonneg_right hnormalization (abs_nonneg _)
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 9)).2
    simpa [mul_comm] using hmul.trans hzero
  have hnone : |normal 1| ≤ (17 / 9 : ℝ) * ‖transported‖ := by
    have hcoord : normal 1 = transported 1 + anchorSlope * normal 0 := by
      simp [transported]
    rw [hcoord]
    calc
      |transported 1 + anchorSlope * normal 0| ≤
          |transported 1| + |anchorSlope| * |normal 0| := by
        simpa [abs_mul] using
          abs_add_le (transported 1) (anchorSlope * normal 0)
      _ ≤ ‖transported‖ + 8 * (‖transported‖ / 9) := by gcongr
      _ = (17 / 9 : ℝ) * ‖transported‖ := by ring
  have hnzeroSq : normal 0 ^ 2 ≤ (‖transported‖ / 9) ^ 2 := by
    nlinarith [abs_nonneg (normal 0), sq_abs (normal 0)]
  have hnoneSq : normal 1 ^ 2 ≤
      ((17 / 9 : ℝ) * ‖transported‖) ^ 2 := by
    nlinarith [abs_nonneg (normal 1), sq_abs (normal 1)]
  have hntwoSq : normal 2 ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith [abs_nonneg (normal 2), sq_abs (normal 2)]
  have hnormalSq :
      normal 0 ^ 2 + normal 1 ^ 2 + normal 2 ^ 2 = 1 := by
    have hnormSq := EuclideanSpace.real_norm_sq_eq normal
    rw [hnormalUnit] at hnormSq
    simpa [Fin.sum_univ_succ, add_assoc] using hnormSq.symm
  by_contra hbound
  have htransportedSmall : ‖transported‖ < 1 / 4 := lt_of_not_ge hbound
  have hnzeroSmall : normal 0 ^ 2 < (1 / 36 : ℝ) ^ 2 := by
    calc
      normal 0 ^ 2 ≤ (‖transported‖ / 9) ^ 2 := hnzeroSq
      _ < ((1 / 4 : ℝ) / 9) ^ 2 := by
        gcongr
      _ = (1 / 36 : ℝ) ^ 2 := by norm_num
  have hnoneSmall : normal 1 ^ 2 < (17 / 36 : ℝ) ^ 2 := by
    calc
      normal 1 ^ 2 ≤ ((17 / 9 : ℝ) * ‖transported‖) ^ 2 := hnoneSq
      _ < ((17 / 9 : ℝ) * (1 / 4)) ^ 2 := by
        gcongr
      _ = (17 / 36 : ℝ) ^ 2 := by norm_num
  nlinarith

/-- Normalization is Lipschitz away from the origin. -/
theorem pureWZ2Proposition64_normalization_lipschitz
    {first second : Point3} {lower : ℝ}
    (hlower : 0 < lower)
    (hfirst : lower ≤ ‖first‖) (hsecond : lower ≤ ‖second‖) :
    ‖(‖first‖⁻¹ : ℝ) • first - (‖second‖⁻¹ : ℝ) • second‖ ≤
      (2 / lower) * ‖first - second‖ := by
  have hfirstPos : 0 < ‖first‖ := hlower.trans_le hfirst
  have hsecondPos : 0 < ‖second‖ := hlower.trans_le hsecond
  have hdecompose :
      (‖first‖⁻¹ : ℝ) • first - (‖second‖⁻¹ : ℝ) • second =
        (‖first‖⁻¹ : ℝ) • (first - second) +
          ((‖first‖⁻¹ - ‖second‖⁻¹ : ℝ) • second) := by
    rw [smul_sub, sub_smul]
    abel
  have hinverseDiff :
      |(‖first‖⁻¹ - ‖second‖⁻¹ : ℝ)| =
        |‖first‖ - ‖second‖| / (‖first‖ * ‖second‖) := by
    rw [show (‖first‖⁻¹ - ‖second‖⁻¹ : ℝ) =
        (‖second‖ - ‖first‖) / (‖first‖ * ‖second‖) by
      field_simp [hfirstPos.ne', hsecondPos.ne'] <;> ring]
    rw [abs_div, abs_mul, abs_of_pos hfirstPos, abs_of_pos hsecondPos,
      abs_sub_comm]
  have hnormDiff : |‖first‖ - ‖second‖| ≤ ‖first - second‖ := by
    have hforward : ‖first‖ - ‖second‖ ≤ ‖first - second‖ :=
      norm_sub_norm_le first second
    have hbackward : ‖second‖ - ‖first‖ ≤ ‖first - second‖ := by
      simpa [norm_sub_rev] using norm_sub_norm_le second first
    exact abs_le.mpr ⟨by linarith, hforward⟩
  rw [hdecompose]
  calc
    ‖(‖first‖⁻¹ : ℝ) • (first - second) +
        ((‖first‖⁻¹ - ‖second‖⁻¹ : ℝ) • second)‖ ≤
      ‖(‖first‖⁻¹ : ℝ) • (first - second)‖ +
        ‖((‖first‖⁻¹ - ‖second‖⁻¹ : ℝ) • second)‖ := norm_add_le _ _
    _ = ‖first‖⁻¹ * ‖first - second‖ +
        |‖first‖⁻¹ - ‖second‖⁻¹| * ‖second‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hfirstPos)]
      rfl
    _ = ‖first‖⁻¹ * ‖first - second‖ +
        |‖first‖ - ‖second‖| / ‖first‖ := by
      rw [hinverseDiff]
      field_simp [hfirstPos.ne', hsecondPos.ne']
    _ ≤ ‖first‖⁻¹ * ‖first - second‖ +
        ‖first - second‖ / ‖first‖ := by
      gcongr
    _ = 2 * ‖first‖⁻¹ * ‖first - second‖ := by
      field_simp [hfirstPos.ne']
      ring
    _ ≤ (2 / lower) * ‖first - second‖ := by
      have hinverse : ‖first‖⁻¹ ≤ lower⁻¹ := by
        exact (inv_le_inv₀ hfirstPos hlower).2 hfirst
      calc
        2 * ‖first‖⁻¹ * ‖first - second‖ ≤
            2 * lower⁻¹ * ‖first - second‖ := by gcongr
        _ = (2 / lower) * ‖first - second‖ := by
          rw [div_eq_mul_inv]

/-- Normalize the inverse-transpose image of a source normal. -/
def pureWZ2Proposition64TransportedNormal
    (anchorSlope halfHeight normalization : ℝ) (normal : Point3) : Point3 :=
  let transported := pureWZ2Proposition64InverseTranspose
    anchorSlope halfHeight normalization normal
  (‖transported‖⁻¹ : ℝ) • transported

/-- A transported unit normal with the source vertical bound remains a unit
normal. -/
theorem pureWZ2Proposition64TransportedNormal_unit
    {anchorSlope halfHeight normalization : ℝ}
    (hanchorSlope : |anchorSlope| ≤ 8)
    (hnormalization : 9 ≤ normalization)
    {normal : Point3}
    (hnormalUnit : ‖normal‖ = 1)
    (hnormalVertical : |normal 2| ≤ 1 / 2) :
    ‖pureWZ2Proposition64TransportedNormal anchorSlope halfHeight
        normalization normal‖ = 1 := by
  let transported := pureWZ2Proposition64InverseTranspose
    anchorSlope halfHeight normalization normal
  have hnorm : 0 < ‖transported‖ := by
    exact lt_of_lt_of_le (by norm_num)
      (pureWZ2Proposition64InverseTranspose_norm_lower
        hanchorSlope hnormalization hnormalUnit hnormalVertical)
  change ‖(‖transported‖⁻¹ : ℝ) • transported‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm)]
  exact inv_mul_cancel₀ hnorm.ne'

/-- The normalized inverse-transpose field has an explicit fixed Lipschitz
constant after composition with a unit-Lipschitz source plane map and the
inverse exact coordinate change. -/
theorem pureWZ2Proposition64TransportedNormal_lipschitz
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeightAbs : |halfHeight| ≤ 1)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hnormalization : 9 ≤ normalization)
    {source target : Set Point3}
    (sourcePlaneMap : {point : Point3 // point ∈ source} → Point3)
    (hsourceLipschitz : LipschitzWith 1 sourcePlaneMap)
    (sourcePoint : {point : Point3 // point ∈ target} →
      {point : Point3 // point ∈ source})
    (hsourcePoint : ∀ first second,
      dist (sourcePoint first) (sourcePoint second) ≤
        3 * normalization * dist first second)
    (hunit : ∀ point, ‖sourcePlaneMap point‖ = 1)
    (hvertical : ∀ point, |sourcePlaneMap point 2| ≤ 1 / 2) :
    LipschitzWith
      ⟨288 * normalization ^ 2,
        mul_nonneg (by norm_num) (sq_nonneg normalization)⟩
      (fun point =>
        pureWZ2Proposition64TransportedNormal (g anchorHeight) halfHeight
          normalization (sourcePlaneMap (sourcePoint point))) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  let firstNormal := sourcePlaneMap (sourcePoint first)
  let secondNormal := sourcePlaneMap (sourcePoint second)
  let firstTransported := pureWZ2Proposition64InverseTranspose
    (g anchorHeight) halfHeight normalization firstNormal
  let secondTransported := pureWZ2Proposition64InverseTranspose
    (g anchorHeight) halfHeight normalization secondNormal
  have hfirstLower : (1 / 4 : ℝ) ≤ ‖firstTransported‖ := by
    exact pureWZ2Proposition64InverseTranspose_norm_lower
      hanchorSlope hnormalization (hunit (sourcePoint first))
        (hvertical (sourcePoint first))
  have hsecondLower : (1 / 4 : ℝ) ≤ ‖secondTransported‖ := by
    exact pureWZ2Proposition64InverseTranspose_norm_lower
      hanchorSlope hnormalization (hunit (sourcePoint second))
        (hvertical (sourcePoint second))
  have hnormalized := pureWZ2Proposition64_normalization_lipschitz
    (lower := (1 / 4 : ℝ)) (by norm_num : (0 : ℝ) < 1 / 4)
      hfirstLower hsecondLower
  have hlinear := pureWZ2Proposition64InverseTranspose_lipschitz
    hhalfHeightAbs hanchorSlope hnormalization
    |>.dist_le_mul firstNormal secondNormal
  have hsource := hsourceLipschitz.dist_le_mul
    (sourcePoint first) (sourcePoint second)
  have hsourceDist := hsourcePoint first second
  change dist
      (pureWZ2Proposition64TransportedNormal (g anchorHeight) halfHeight
        normalization firstNormal)
      (pureWZ2Proposition64TransportedNormal (g anchorHeight) halfHeight
        normalization secondNormal) ≤ _
  rw [dist_eq_norm]
  have hnormalizedEight :
      ‖(‖firstTransported‖⁻¹ : ℝ) • firstTransported -
          (‖secondTransported‖⁻¹ : ℝ) • secondTransported‖ ≤
        8 * ‖firstTransported - secondTransported‖ := by
    convert hnormalized using 1 <;> norm_num
  have hlinearReal :
      ‖firstTransported - secondTransported‖ ≤
        3 * normalization * dist firstNormal secondNormal := by
    have hraw :
        ‖pureWZ2Proposition64InverseTranspose (g anchorHeight) halfHeight
              normalization firstNormal -
            pureWZ2Proposition64InverseTranspose (g anchorHeight) halfHeight
              normalization secondNormal‖ ≤
          3 * normalization * ‖firstNormal - secondNormal‖ := by
      exact_mod_cast hlinear
    simpa only [firstTransported, secondTransported, dist_eq_norm] using hraw
  calc
    ‖pureWZ2Proposition64TransportedNormal (g anchorHeight) halfHeight
          normalization firstNormal -
        pureWZ2Proposition64TransportedNormal (g anchorHeight) halfHeight
          normalization secondNormal‖ ≤
        8 * ‖firstTransported - secondTransported‖ := by
      simpa [pureWZ2Proposition64TransportedNormal,
        firstTransported, secondTransported] using hnormalizedEight
    _ ≤ 8 * (3 * normalization * dist firstNormal secondNormal) := by
      exact mul_le_mul_of_nonneg_left hlinearReal (by norm_num)
    _ ≤ 8 * (3 * normalization *
          (dist (sourcePoint first) (sourcePoint second))) := by
      gcongr
      simpa using hsource
    _ ≤ 8 * (3 * normalization *
          (3 * normalization * dist first second)) := by
      gcongr
    _ = (72 * normalization ^ 2) * dist first second := by ring
    _ ≤ (288 * normalization ^ 2) * dist first second := by
      have hnonneg : 0 ≤ normalization ^ 2 * dist first second := by positivity
      nlinarith

/-- The transported normal remains transverse to the vertical direction.
This is the quantitative normalization input used by the final isotropic
stage of Lemma 3.5. -/
theorem pureWZ2Proposition64TransportedNormal_vertical_bound
    {anchorSlope halfHeight normalization : ℝ}
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightSmall : halfHeight ≤ 1 / 20)
    (hanchorSlope : |anchorSlope| ≤ 8)
    (hnormalization : 9 ≤ normalization)
    {normal : Point3}
    (hnormalUnit : ‖normal‖ = 1)
    (hnormalVertical : |normal 2| ≤ 1 / 2) :
    |pureWZ2Proposition64TransportedNormal anchorSlope halfHeight
        normalization normal 2| ≤ 1 / 10 := by
  let transported := pureWZ2Proposition64InverseTranspose
    anchorSlope halfHeight normalization normal
  have hnorm : (1 / 4 : ℝ) ≤ ‖transported‖ :=
    pureWZ2Proposition64InverseTranspose_norm_lower
      hanchorSlope hnormalization hnormalUnit hnormalVertical
  have hnormPos : 0 < ‖transported‖ := by linarith
  have hcoordinate : transported 2 = halfHeight * normal 2 := by
    simp [transported]
  change |(‖transported‖⁻¹ • transported) 2| ≤ 1 / 10
  simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_norm]
  rw [hcoordinate, abs_mul, abs_of_pos hhalfHeight]
  have hnumerator : halfHeight * |normal 2| ≤ 1 / 40 := by
    nlinarith [abs_nonneg (normal 2)]
  have hinverse : ‖transported‖⁻¹ ≤ 4 := by
    have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
    have := (inv_le_inv₀ hnormPos hquarter).2 hnorm
    norm_num at this ⊢
    exact this
  calc
    ‖transported‖⁻¹ * (halfHeight * |normal 2|) ≤
        4 * (1 / 40 : ℝ) := by gcongr <;> positivity
    _ = 1 / 10 := by norm_num

/-- The normalized image direction and normalized inverse-transpose normal
preserve the source incidence estimate.  The short vertical scale makes the
product of the two normalizing norms larger than one. -/
theorem pureWZ2Proposition64ImageTube_inner_transportedNormal
    {sourceDelta targetDelta : ℝ}
    (g : ℝ → ℝ) (slabCenter anchorHeight : ℝ)
    (translation : Point3)
    {halfHeight normalization : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightSmall : halfHeight ≤ 1 / 20)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hsourceVertical : (1 / 2 : ℝ) ≤ |sourceTube.direction 2|)
    (normal : Point3)
    (hnormalUnit : ‖normal‖ = 1)
    (hnormalVertical : |normal 2| ≤ 1 / 2)
    (hsourceIncidence :
      |inner ℝ sourceTube.direction normal| ≤ sourceDelta) :
    |inner ℝ
        (pureWZ2Proposition64ImageTube targetDelta g slabCenter anchorHeight
          halfHeight normalization translation hhalfHeight (by linarith)
          sourceTube).direction
        (pureWZ2Proposition64TransportedNormal (g anchorHeight) halfHeight
          normalization normal)| ≤ sourceDelta := by
  let directionImage := pureWZ2Proposition64ImageDirection g anchorHeight
    halfHeight normalization sourceTube.direction
  let normalImage := pureWZ2Proposition64InverseTranspose
    (g anchorHeight) halfHeight normalization normal
  have hdirectionCoordinate :
      directionImage 2 = sourceTube.direction 2 / halfHeight := by
    simp [directionImage, pureWZ2Proposition64ImageDirection,
      pureWZ2Proposition64Linear, point3]
  have hdirectionCoordNorm : |directionImage 2| ≤ ‖directionImage‖ := by
    simpa [Real.norm_eq_abs] using
      PiLp.norm_apply_le directionImage (2 : Fin 3)
  have hdirectionNorm : 10 ≤ ‖directionImage‖ := by
    rw [hdirectionCoordinate, abs_div, abs_of_pos hhalfHeight]
      at hdirectionCoordNorm
    have hratio : 10 ≤ |sourceTube.direction 2| / halfHeight := by
      apply (le_div_iff₀ hhalfHeight).2
      nlinarith
    exact hratio.trans hdirectionCoordNorm
  have hnormalNorm : (1 / 4 : ℝ) ≤ ‖normalImage‖ := by
    exact pureWZ2Proposition64InverseTranspose_norm_lower
      hanchorSlope hnormalization hnormalUnit hnormalVertical
  have hdirectionPos : 0 < ‖directionImage‖ := by linarith
  have hnormalPos : 0 < ‖normalImage‖ := by linarith
  have hproduct : 1 ≤ ‖directionImage‖ * ‖normalImage‖ := by
    have hmul : 10 * (1 / 4 : ℝ) ≤
        ‖directionImage‖ * ‖normalImage‖ :=
      mul_le_mul hdirectionNorm hnormalNorm
        (by norm_num : (0 : ℝ) ≤ 1 / 4) (norm_nonneg directionImage)
    linarith
  have hinner : inner ℝ directionImage normalImage =
      inner ℝ sourceTube.direction normal := by
    exact pureWZ2Proposition64Linear_inner_inverseTranspose
      (g anchorHeight) hhalfHeight.ne' (by linarith) _ _
  change |inner ℝ
      ((‖directionImage‖⁻¹ : ℝ) • directionImage)
      ((‖normalImage‖⁻¹ : ℝ) • normalImage)| ≤ sourceDelta
  rw [inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply, star_trivial, abs_mul, abs_inv, abs_norm]
  rw [hinner]
  have hcoefficient :
      ‖directionImage‖⁻¹ * ‖normalImage‖⁻¹ ≤ 1 := by
    have hinverse :
        (‖directionImage‖ * ‖normalImage‖)⁻¹ ≤ (1 : ℝ) := by
      apply (inv_le_one₀ (mul_pos hdirectionPos hnormalPos)).2
      exact hproduct
    calc
      ‖directionImage‖⁻¹ * ‖normalImage‖⁻¹ =
          (‖directionImage‖ * ‖normalImage‖)⁻¹ := by
        field_simp [hdirectionPos.ne', hnormalPos.ne']
      _ ≤ 1 := hinverse
  calc
    ‖directionImage‖⁻¹ *
          (‖normalImage‖⁻¹ * |inner ℝ sourceTube.direction normal|) ≤
        1 * |inner ℝ sourceTube.direction normal| := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hcoefficient (abs_nonneg _)
    _ ≤ sourceDelta := by simpa using hsourceIncidence

end Kakeya.Assouad
