import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64AffineMap

/-!
# The two stages of the exact Proposition 6.4 map

The coordinate change in Proposition 6.4 first applies a fixed horizontal
shear/contraction while preserving height, and then expands the selected
short vertical slab to the standard height interval.  Keeping these stages
separate is useful when transporting the nearby-scale CWA certificates: the
first stage is a fixed linear map, whereas all scale change occurs in the
second stage.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The height-preserving horizontal linear stage of Proposition 6.4. -/
def pureWZ2Proposition64HorizontalLinear
    (anchorSlope normalization : ℝ) : Point3 →ₗ[ℝ] Point3 where
  toFun point := point3
    ((point 0 + anchorSlope * point 1) / normalization)
    (point 1)
    (point 2)
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> simp [point3] <;> ring
  map_smul' scalar point := by
    ext coordinate
    fin_cases coordinate <;> simp [point3] <;> ring

/-- The vertical affine stage of Proposition 6.4. -/
def pureWZ2Proposition64VerticalStretch
    (slabCenter halfHeight : ℝ) (point : Point3) : Point3 :=
  point3 (point 0) (point 1) ((point 2 - slabCenter) / halfHeight)

@[simp] theorem pureWZ2Proposition64HorizontalLinear_apply_zero
    (anchorSlope normalization : ℝ) (point : Point3) :
    pureWZ2Proposition64HorizontalLinear anchorSlope normalization point 0 =
      (point 0 + anchorSlope * point 1) / normalization := by
  simp [pureWZ2Proposition64HorizontalLinear, point3]

@[simp] theorem pureWZ2Proposition64HorizontalLinear_apply_one
    (anchorSlope normalization : ℝ) (point : Point3) :
    pureWZ2Proposition64HorizontalLinear anchorSlope normalization point 1 =
      point 1 := by
  simp [pureWZ2Proposition64HorizontalLinear, point3]

@[simp] theorem pureWZ2Proposition64HorizontalLinear_apply_two
    (anchorSlope normalization : ℝ) (point : Point3) :
    pureWZ2Proposition64HorizontalLinear anchorSlope normalization point 2 =
      point 2 := by
  simp [pureWZ2Proposition64HorizontalLinear, point3]

@[simp] theorem pureWZ2Proposition64VerticalStretch_apply_zero
    (slabCenter halfHeight : ℝ) (point : Point3) :
    pureWZ2Proposition64VerticalStretch slabCenter halfHeight point 0 =
      point 0 := by
  simp [pureWZ2Proposition64VerticalStretch, point3]

@[simp] theorem pureWZ2Proposition64VerticalStretch_apply_one
    (slabCenter halfHeight : ℝ) (point : Point3) :
    pureWZ2Proposition64VerticalStretch slabCenter halfHeight point 1 =
      point 1 := by
  simp [pureWZ2Proposition64VerticalStretch, point3]

@[simp] theorem pureWZ2Proposition64VerticalStretch_apply_two
    (slabCenter halfHeight : ℝ) (point : Point3) :
    pureWZ2Proposition64VerticalStretch slabCenter halfHeight point 2 =
      (point 2 - slabCenter) / halfHeight := by
  simp [pureWZ2Proposition64VerticalStretch, point3]

/-- The first stage preserves every horizontal slice exactly. -/
theorem pureWZ2Proposition64HorizontalLinear_height
    (anchorSlope normalization : ℝ) (point : Point3) :
    pureWZ2Proposition64HorizontalLinear anchorSlope normalization point 2 =
      point 2 := by
  simp

/-- Pointwise factorization of the exact map displayed in Proposition 6.4. -/
theorem pureWZ2Proposition64Map_factorization
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (point : Point3) :
    pureWZ2Proposition64VerticalStretch slabCenter halfHeight
        (pureWZ2Proposition64HorizontalLinear
          (g anchorHeight) normalization point) =
      pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
        normalization point := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2Proposition64VerticalStretch,
      pureWZ2Proposition64HorizontalLinear,
      pureWZ2Proposition64Map, point3]

/-- Under the bounds supplied by Proposition 6.4, the changed horizontal
coordinate is a contraction of the source vector. -/
theorem pureWZ2Proposition64HorizontalLinear_first_abs_le_norm
    {anchorSlope normalization : ℝ}
    (hanchorSlope : |anchorSlope| ≤ 8)
    (hnormalization : 9 ≤ normalization)
    (point : Point3) :
    |pureWZ2Proposition64HorizontalLinear
        anchorSlope normalization point 0| ≤ ‖point‖ := by
  have hnormalizationPos : 0 < normalization := by linarith
  have hzero : |point 0| ≤ ‖point‖ := by
    simpa [Real.norm_eq_abs] using
      (PiLp.norm_apply_le point (0 : Fin 3))
  have hone : |point 1| ≤ ‖point‖ := by
    simpa [Real.norm_eq_abs] using
      (PiLp.norm_apply_le point (1 : Fin 3))
  rw [pureWZ2Proposition64HorizontalLinear_apply_zero,
    abs_div, abs_of_pos hnormalizationPos]
  apply (div_le_iff₀ hnormalizationPos).2
  calc
    |point 0 + anchorSlope * point 1| ≤
        |point 0| + |anchorSlope| * |point 1| := by
      simpa [abs_mul] using abs_add_le (point 0) (anchorSlope * point 1)
    _ ≤ ‖point‖ + 8 * ‖point‖ := by gcongr
    _ = 9 * ‖point‖ := by ring
    _ ≤ normalization * ‖point‖ := by
      exact mul_le_mul_of_nonneg_right hnormalization (norm_nonneg point)
    _ = ‖point‖ * normalization := by ring

/-- Consequently the full height-preserving stage has a fixed absolute
Lipschitz bound.  The bound two is deliberately coarse and independent of
the selected scale. -/
theorem pureWZ2Proposition64HorizontalLinear_norm_le_two
    {anchorSlope normalization : ℝ}
    (hanchorSlope : |anchorSlope| ≤ 8)
    (hnormalization : 9 ≤ normalization)
    (point : Point3) :
    ‖pureWZ2Proposition64HorizontalLinear
        anchorSlope normalization point‖ ≤ 2 * ‖point‖ := by
  have hfirst :=
    pureWZ2Proposition64HorizontalLinear_first_abs_le_norm
      hanchorSlope hnormalization point
  have hfirstSq :
      (pureWZ2Proposition64HorizontalLinear
          anchorSlope normalization point 0) ^ 2 ≤ ‖point‖ ^ 2 := by
    nlinarith [abs_nonneg
      (pureWZ2Proposition64HorizontalLinear
        anchorSlope normalization point 0), norm_nonneg point,
      sq_abs (pureWZ2Proposition64HorizontalLinear
        anchorSlope normalization point 0)]
  have hrest : point 1 ^ 2 + point 2 ^ 2 ≤ ‖point‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
    positivity
  have hsquares :
      ‖pureWZ2Proposition64HorizontalLinear
          anchorSlope normalization point‖ ^ 2 ≤
        2 * ‖point‖ ^ 2 := by
    calc
      ‖pureWZ2Proposition64HorizontalLinear
          anchorSlope normalization point‖ ^ 2 =
          (pureWZ2Proposition64HorizontalLinear
              anchorSlope normalization point 0) ^ 2 +
            (pureWZ2Proposition64HorizontalLinear
              anchorSlope normalization point 1) ^ 2 +
            (pureWZ2Proposition64HorizontalLinear
              anchorSlope normalization point 2) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp [Fin.sum_univ_succ]
        ring
      _ ≤ ‖point‖ ^ 2 + ‖point‖ ^ 2 := by
        rw [pureWZ2Proposition64HorizontalLinear_apply_one,
          pureWZ2Proposition64HorizontalLinear_apply_two]
        linarith
      _ = 2 * ‖point‖ ^ 2 := by ring
  nlinarith [norm_nonneg point,
    norm_nonneg
      (pureWZ2Proposition64HorizontalLinear
        anchorSlope normalization point), sq_nonneg (‖point‖)]

end Kakeya.Assouad
