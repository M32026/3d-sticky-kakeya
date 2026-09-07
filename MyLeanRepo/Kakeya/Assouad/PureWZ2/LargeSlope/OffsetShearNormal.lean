import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains

/-!
# A bounded horizontal shear for the omitted local-grain transport

The paper's final diagonal rescaling normalizes the global slope but does not
explain why the local plane map remains Lipschitz.  This file records only the
elementary linear algebra for a possible repair.  It is not a restatement of
the rescaling lemma in the paper.

The shear `(x,y,z) ↦ (x + a*y,y,z)` changes a projection slope `f` to `f-a`
without changing its derivatives.  Its inverse transpose changes a normal
`n` to `(n₀,n₁-a*n₀,n₂)`.  Choosing `a` half a unit from an anchor slope
makes the second coordinate uniformly nonzero whenever the internal Node-5
compatibility estimates hold.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Move an anchor slope half a unit toward zero. -/
def pureWZ2HalfOffset (anchorSlope : ℝ) : ℝ :=
  if 0 ≤ anchorSlope then anchorSlope - 1 / 2 else anchorSlope + 1 / 2

theorem pureWZ2HalfOffset_abs_le
    {anchorSlope : ℝ} (hanchor : |anchorSlope| ≤ 1) :
    |pureWZ2HalfOffset anchorSlope| ≤ 1 / 2 := by
  rw [abs_le] at hanchor ⊢
  by_cases hsign : 0 ≤ anchorSlope
  · simp only [pureWZ2HalfOffset, if_pos hsign]
    constructor <;> linarith [hanchor.1, hanchor.2]
  · have hnegative : anchorSlope < 0 := lt_of_not_ge hsign
    simp only [pureWZ2HalfOffset, if_neg hsign]
    constructor <;> linarith [hanchor.1, hanchor.2]

theorem pureWZ2HalfOffset_abs_sub (anchorSlope : ℝ) :
    |anchorSlope - pureWZ2HalfOffset anchorSlope| = 1 / 2 := by
  by_cases hsign : 0 ≤ anchorSlope
  · simp [pureWZ2HalfOffset, hsign]
  · simp [pureWZ2HalfOffset, hsign]

/-- The bounded horizontal shear `(x,y,z) ↦ (x+a*y,y,z)`. -/
def pureWZ2OffsetShearLinear (a : ℝ) : Point3 →ₗ[ℝ] Point3 where
  toFun point := point3 (point 0 + a * point 1) (point 1) (point 2)
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> simp [point3] <;> ring
  map_smul' scalar point := by
    ext coordinate
    fin_cases coordinate <;> simp [point3] <;> ring

/-- The inverse linear shear. -/
def pureWZ2OffsetShearInverseLinear (a : ℝ) : Point3 →ₗ[ℝ] Point3 where
  toFun point := point3 (point 0 - a * point 1) (point 1) (point 2)
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> simp [point3] <;> ring
  map_smul' scalar point := by
    ext coordinate
    fin_cases coordinate <;> simp [point3] <;> ring

/-- Linear-equivalence packaging of the bounded horizontal shear. -/
def pureWZ2OffsetShearEquiv (a : ℝ) : Point3 ≃ₗ[ℝ] Point3 :=
  LinearEquiv.mk (pureWZ2OffsetShearLinear a)
    (pureWZ2OffsetShearInverseLinear a)
    (by
      intro point
      ext coordinate
      fin_cases coordinate <;>
        simp [pureWZ2OffsetShearLinear,
          pureWZ2OffsetShearInverseLinear, point3] <;> ring)
    (by
      intro point
      ext coordinate
      fin_cases coordinate <;>
        simp [pureWZ2OffsetShearLinear,
          pureWZ2OffsetShearInverseLinear, point3] <;> ring)

@[simp] theorem pureWZ2OffsetShearEquiv_coord_zero
    (a : ℝ) (point : Point3) :
    pureWZ2OffsetShearEquiv a point 0 = point 0 + a * point 1 := by
  simp [pureWZ2OffsetShearEquiv, pureWZ2OffsetShearLinear, point3]

@[simp] theorem pureWZ2OffsetShearEquiv_coord_one
    (a : ℝ) (point : Point3) :
    pureWZ2OffsetShearEquiv a point 1 = point 1 := by
  simp [pureWZ2OffsetShearEquiv, pureWZ2OffsetShearLinear, point3]

@[simp] theorem pureWZ2OffsetShearEquiv_coord_two
    (a : ℝ) (point : Point3) :
    pureWZ2OffsetShearEquiv a point 2 = point 2 := by
  simp [pureWZ2OffsetShearEquiv, pureWZ2OffsetShearLinear, point3]

/-- The exact inverse-transpose action of the horizontal shear on normals. -/
def pureWZ2OffsetShearNormal (a : ℝ) (normal : Point3) : Point3 :=
  point3 (normal 0) (normal 1 - a * normal 0) (normal 2)

@[simp] theorem pureWZ2OffsetShearNormal_coord_zero
    (a : ℝ) (normal : Point3) :
    pureWZ2OffsetShearNormal a normal 0 = normal 0 := by
  simp [pureWZ2OffsetShearNormal, point3]

@[simp] theorem pureWZ2OffsetShearNormal_coord_one
    (a : ℝ) (normal : Point3) :
    pureWZ2OffsetShearNormal a normal 1 = normal 1 - a * normal 0 := by
  simp [pureWZ2OffsetShearNormal, point3]

@[simp] theorem pureWZ2OffsetShearNormal_coord_two
    (a : ℝ) (normal : Point3) :
    pureWZ2OffsetShearNormal a normal 2 = normal 2 := by
  simp [pureWZ2OffsetShearNormal, point3]

/-- The shear and its inverse transpose preserve the incidence pairing. -/
theorem pureWZ2OffsetShear_inner
    (a : ℝ) (direction normal : Point3) :
    inner ℝ (pureWZ2OffsetShearEquiv a direction)
        (pureWZ2OffsetShearNormal a normal) =
      inner ℝ direction normal := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp [pureWZ2OffsetShearNormal, point3, Fin.sum_univ_succ]
  ring

/-- The inverse-transpose shear has operator norm at most `2` when the shear
parameter has absolute value at most one half. -/
theorem pureWZ2OffsetShearNormal_norm_le_two
    {a : ℝ} (ha : |a| ≤ 1 / 2) (normal : Point3) :
    ‖pureWZ2OffsetShearNormal a normal‖ ≤ 2 * ‖normal‖ := by
  have hsource := point3_coord_norm_sq normal
  have htarget := point3_coord_norm_sq
    (pureWZ2OffsetShearNormal a normal)
  have hcoordZero : |normal 0| ≤ ‖normal‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le normal (0 : Fin 3)
  have hcoordOne : |normal 1| ≤ ‖normal‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le normal (1 : Fin 3)
  have hmiddle : |normal 1 - a * normal 0| ≤ 3 / 2 * ‖normal‖ := by
    calc
      |normal 1 - a * normal 0| ≤ |normal 1| + |a| * |normal 0| := by
        simpa [abs_mul] using abs_sub (normal 1) (a * normal 0)
      _ ≤ ‖normal‖ + (1 / 2) * ‖normal‖ := by gcongr
      _ = 3 / 2 * ‖normal‖ := by ring
  have hnormNonnegative : 0 ≤ ‖normal‖ := norm_nonneg _
  have hmiddleSq : (normal 1 - a * normal 0) ^ 2 ≤
      (3 / 2 * ‖normal‖) ^ 2 := by
    nlinarith [sq_abs (normal 1 - a * normal 0), abs_nonneg (normal 1 - a * normal 0)]
  have hzeroSq : normal 0 ^ 2 ≤ ‖normal‖ ^ 2 := by
    nlinarith [sq_abs (normal 0), abs_nonneg (normal 0)]
  have htwoSq : normal 2 ^ 2 ≤ ‖normal‖ ^ 2 := by
    have hcoordTwo : |normal 2| ≤ ‖normal‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le normal (2 : Fin 3)
    nlinarith [sq_abs (normal 2), abs_nonneg (normal 2)]
  have htargetSq :
      ‖pureWZ2OffsetShearNormal a normal‖ ^ 2 ≤ (2 * ‖normal‖) ^ 2 := by
    rw [htarget]
    simp only [pureWZ2OffsetShearNormal, point3_coord0, point3_coord1,
      point3_coord2]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp htargetSq

theorem pureWZ2OffsetShearNormal_sub
    (a : ℝ) (first second : Point3) :
    pureWZ2OffsetShearNormal a first -
        pureWZ2OffsetShearNormal a second =
      pureWZ2OffsetShearNormal a (first - second) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2OffsetShearNormal, point3, PiLp.sub_apply] <;> ring

/-- A half-unit offset shear enlarges distances between normals by at most a
fixed factor two. -/
theorem pureWZ2OffsetShearNormal_sub_norm_le_two
    {a : ℝ} (ha : |a| ≤ 1 / 2) (first second : Point3) :
    ‖pureWZ2OffsetShearNormal a first -
        pureWZ2OffsetShearNormal a second‖ ≤
      2 * ‖first - second‖ := by
  rw [pureWZ2OffsetShearNormal_sub]
  exact pureWZ2OffsetShearNormal_norm_le_two ha (first - second)

theorem pureWZ2OffsetShearNormal_lipschitz
    {X : Type*} [PseudoMetricSpace X]
    {a : ℝ} {K : NNReal} {rawNormal : X → Point3}
    (ha : |a| ≤ 1 / 2) (hraw : LipschitzWith K rawNormal) :
    LipschitzWith (2 * K)
      (fun point => pureWZ2OffsetShearNormal a (rawNormal point)) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  change ‖pureWZ2OffsetShearNormal a (rawNormal first) -
      pureWZ2OffsetShearNormal a (rawNormal second)‖ ≤
    ((2 * K : NNReal) : ℝ) * dist first second
  calc
    ‖pureWZ2OffsetShearNormal a (rawNormal first) -
        pureWZ2OffsetShearNormal a (rawNormal second)‖ ≤
        2 * ‖rawNormal first - rawNormal second‖ :=
      pureWZ2OffsetShearNormal_sub_norm_le_two ha _ _
    _ ≤ 2 * ((K : ℝ) * dist first second) := by
      gcongr
      simpa [dist_eq_norm] using hraw.dist_le_mul first second
    _ = ((2 * K : NNReal) : ℝ) * dist first second := by
      simp [NNReal.coe_mul]
      ring

/-- The shear changes `x+f(z)y` to the slope `f-a` exactly. -/
theorem pureWZ2OffsetShear_projection
    (a slope : ℝ) (point : Point3) :
    inner ℝ (pureWZ2OffsetShearEquiv a point)
        (globalGrainDirection (slope - a)) =
      inner ℝ point (globalGrainDirection slope) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp [globalGrainDirection, point3, Fin.sum_univ_succ]
  ring

/-- Internal global/local compatibility makes the sheared normal's unscaled
second coordinate uniformly nonzero on a sufficiently short slope window. -/
theorem pureWZ2OffsetShearNormal_coord_one_lower
    {sourceSlope anchorSlope : ℝ} {normal : Point3}
    (hfirst : (1 / 4 : ℝ) ≤ |normal 0|)
    (htilt : |normal 1 - sourceSlope * normal 0| ≤ 1 / 10)
    (hclose : |sourceSlope - anchorSlope| ≤ 1 / 200) :
    (1 / 50 : ℝ) <
      |pureWZ2OffsetShearNormal (pureWZ2HalfOffset anchorSlope) normal 1| := by
  let a := pureWZ2HalfOffset anchorSlope
  have hanchorOffset : |anchorSlope - a| = 1 / 2 := by
    exact pureWZ2HalfOffset_abs_sub anchorSlope
  have hsourceOffset : (99 / 200 : ℝ) ≤ |sourceSlope - a| := by
    have htriangle := abs_add_le (anchorSlope - sourceSlope)
      (sourceSlope - a)
    have hsum : anchorSlope - sourceSlope + (sourceSlope - a) =
        anchorSlope - a := by ring
    rw [hsum, abs_sub_comm anchorSlope sourceSlope, hanchorOffset] at htriangle
    linarith
  have hproduct : (99 / 800 : ℝ) ≤
      |(sourceSlope - a) * normal 0| := by
    rw [abs_mul]
    have hmul := mul_le_mul hsourceOffset hfirst
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (abs_nonneg (sourceSlope - a))
    norm_num at hmul ⊢
    exact hmul
  have hreverse :
      |(sourceSlope - a) * normal 0| ≤
        |normal 1 - a * normal 0| +
          |normal 1 - sourceSlope * normal 0| := by
    have htriangle := abs_add_le
      (normal 1 - a * normal 0)
      (-(normal 1 - sourceSlope * normal 0))
    have hsum :
        normal 1 - a * normal 0 -
            (normal 1 - sourceSlope * normal 0) =
          (sourceSlope - a) * normal 0 := by ring
    calc
      |(sourceSlope - a) * normal 0| =
          |normal 1 - a * normal 0 -
            (normal 1 - sourceSlope * normal 0)| := congrArg abs hsum.symm
      _ = |normal 1 - a * normal 0 +
            -(normal 1 - sourceSlope * normal 0)| := by rw [sub_eq_add_neg]
      _ ≤ |normal 1 - a * normal 0| +
          |-(normal 1 - sourceSlope * normal 0)| := htriangle
      _ = |normal 1 - a * normal 0| +
          |normal 1 - sourceSlope * normal 0| := by rw [abs_neg]
  rw [pureWZ2OffsetShearNormal_coord_one]
  linarith

/-- The internal Node-5 compatibility record supplies the hypotheses of the
shear-coordinate estimate at every genuine point of the same configuration.
This theorem intentionally consumes construction provenance rather than adding
an assumption to the paper-facing local-grain API. -/
theorem PureWZ2LocalGlobalCompatibility.offsetShearNormal_coord_one_lower
    {sigma loss delta anchorSlope : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma loss delta}
    (compatibility : PureWZ2LocalGlobalCompatibility cfg)
    (point : {point : Point3 // point ∈ cfg.shading.union})
    (hclose :
      |cfg.globalGrains.slope (point.1 2) - anchorSlope| ≤ 1 / 200) :
    (1 / 50 : ℝ) <
      |pureWZ2OffsetShearNormal (pureWZ2HalfOffset anchorSlope)
          (cfg.localGrains.planeMap point) 1| := by
  exact pureWZ2OffsetShearNormal_coord_one_lower
    (compatibility.normal_first point)
    (compatibility.normal_tilt point) hclose

end Kakeya.Assouad

end
