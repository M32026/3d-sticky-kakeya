import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LineClassNormalizationFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CombinedAffineLocalAD

/-!
# Exact normals for the line-class-compatible normalization

The map `diag(lambda, 1, lambda)` preserves both the public slope derivative
and the paper vertical line class.  Its inverse transpose is
`diag(lambda⁻¹, 1, lambda⁻¹)`.  On the image of a literal constant-`y`
source slice, the inverse metric supplies the missing `lambda⁻¹` factor, so
normalization of the transported plane field costs only a fixed factor two.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- Linear-map packaging of the inverse transpose. -/
def pureWZ2LineClassNormalizationNormalLinear
    (lambda : ℝ) : Point3 →ₗ[ℝ] Point3 where
  toFun := pureWZ2LineClassNormalizationNormal lambda
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2LineClassNormalizationNormal, point3] <;> ring
  map_smul' scalar normal := by
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2LineClassNormalizationNormal, point3] <;> ring

@[simp] theorem pureWZ2LineClassNormalizationNormalLinear_apply
    (lambda : ℝ) (normal : Point3) :
    pureWZ2LineClassNormalizationNormalLinear lambda normal =
      pureWZ2LineClassNormalizationNormal lambda normal :=
  rfl

/-- The inverse transpose is injective at nonzero scale. -/
theorem pureWZ2LineClassNormalizationNormal_injective
    {lambda : ℝ} (hlambda : lambda ≠ 0) :
    Function.Injective (pureWZ2LineClassNormalizationNormal lambda) := by
  intro first second heq
  have hzero := congrArg (fun point : Point3 => point 0) heq
  have hone := congrArg (fun point : Point3 => point 1) heq
  have htwo := congrArg (fun point : Point3 => point 2) heq
  simp only [pureWZ2LineClassNormalizationNormal, point3_coord0] at hzero
  simp only [pureWZ2LineClassNormalizationNormal, point3_coord1] at hone
  simp only [pureWZ2LineClassNormalizationNormal, point3_coord2] at htwo
  ext coordinate
  fin_cases coordinate
  · exact (div_left_inj' hlambda).mp hzero
  · exact hone
  · exact (div_left_inj' hlambda).mp htwo

/-- A unit normal keeps norm at least `lambda⁻¹`. -/
theorem pureWZ2LineClassNormalizationNormal_norm_lower_of_unit
    {lambda : ℝ} (hlambda : 1 ≤ lambda)
    {normal : Point3} (hnormal : ‖normal‖ = 1) :
    1 / lambda ≤
      ‖pureWZ2LineClassNormalizationNormal lambda normal‖ := by
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  have hsource := point3_coord_norm_sq normal
  have htarget := point3_coord_norm_sq
    (pureWZ2LineClassNormalizationNormal lambda normal)
  have hsquare : (1 / lambda) ^ 2 ≤
      ‖pureWZ2LineClassNormalizationNormal lambda normal‖ ^ 2 := by
    rw [htarget]
    simp only [pureWZ2LineClassNormalizationNormal, point3_coord0,
      point3_coord1, point3_coord2]
    rw [show (1 / lambda) ^ 2 =
      (1 / lambda ^ 2) * ‖normal‖ ^ 2 by rw [hnormal]; ring, hsource]
    field_simp [hlambdaPos.ne']
    have hscale : 1 ≤ lambda ^ 2 := by nlinarith [sq_nonneg lambda]
    have hone : normal 1 ^ 2 ≤ lambda ^ 2 * normal 1 ^ 2 := by
      nlinarith [sq_nonneg (normal 1)]
    nlinarith [sq_nonneg (normal 0), sq_nonneg (normal 2)]
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsquare

/-- Chosen exact preimage under the line-class affine equivalence. -/
def pureWZ2LineClassNormalizationExactSourcePoint
    {source : Set Point3} (center : Point3) {lambda : ℝ}
    (hlambda : 0 < lambda)
    (target : {point : Point3 //
      point ∈ pureWZ2LineClassNormalizationMap center lambda '' source}) :
    {point : Point3 // point ∈ source} :=
  let equivalence :=
    pureWZ2LineClassNormalizationAffineEquiv center lambda hlambda
  ⟨equivalence.symm target, by
    rcases target.property with ⟨sourcePoint, hsourcePoint, heq⟩
    have heq' : (target : Point3) = equivalence sourcePoint := by
      rw [pureWZ2LineClassNormalizationAffineEquiv_apply]
      exact heq.symm
    rw [heq', AffineEquiv.symm_apply_apply]
    exact hsourcePoint⟩

@[simp] theorem pureWZ2LineClassNormalizationMap_exactSourcePoint
    {source : Set Point3} (center : Point3) {lambda : ℝ}
    (hlambda : 0 < lambda)
    (target : {point : Point3 //
      point ∈ pureWZ2LineClassNormalizationMap center lambda '' source}) :
    pureWZ2LineClassNormalizationMap center lambda
        (pureWZ2LineClassNormalizationExactSourcePoint center hlambda target) =
      target := by
  rw [← pureWZ2LineClassNormalizationAffineEquiv_apply]
  exact (pureWZ2LineClassNormalizationAffineEquiv center lambda hlambda)
    |>.apply_symm_apply target

/-- Exact normalized inverse-transpose plane field on the image. -/
def pureWZ2LineClassNormalizationExactPlaneMap
    {source : Set Point3}
    (rawNormal : {point : Point3 // point ∈ source} → Point3)
    (center : Point3) {lambda : ℝ} (hlambda : 0 < lambda)
    (target : {point : Point3 //
      point ∈ pureWZ2LineClassNormalizationMap center lambda '' source}) :
    Point3 :=
  let transported := pureWZ2LineClassNormalizationNormal lambda
    (rawNormal
      (pureWZ2LineClassNormalizationExactSourcePoint center hlambda target))
  (‖transported‖⁻¹ : ℝ) • transported

theorem pureWZ2LineClassNormalizationExactPlaneMap_unit
    {source : Set Point3}
    (rawNormal : {point : Point3 // point ∈ source} → Point3)
    (hrawUnit : ∀ point, ‖rawNormal point‖ = 1)
    (center : Point3) {lambda : ℝ} (hlambda : 0 < lambda)
    (target : {point : Point3 //
      point ∈ pureWZ2LineClassNormalizationMap center lambda '' source}) :
    ‖pureWZ2LineClassNormalizationExactPlaneMap rawNormal center hlambda
      target‖ = 1 := by
  let sourcePoint :=
    pureWZ2LineClassNormalizationExactSourcePoint center hlambda target
  let transported := pureWZ2LineClassNormalizationNormal lambda
    (rawNormal sourcePoint)
  have hrawNonzero : rawNormal sourcePoint ≠ 0 := by
    intro hzero
    have hunit := hrawUnit sourcePoint
    rw [hzero, norm_zero] at hunit
    norm_num at hunit
  have htransported : transported ≠ 0 := by
    exact fun hzero => hrawNonzero
      (pureWZ2LineClassNormalizationNormal_injective hlambda.ne' <| by
        simpa [transported, pureWZ2LineClassNormalizationNormal, point3]
          using hzero)
  change ‖(‖transported‖⁻¹ : ℝ) • transported‖ = 1
  exact norm_smul_inv_norm htransported

/-- On the exact image of a constant-`y` source slice, normal transport has
Lipschitz constant at most twice the source constant, independently of
`lambda`. -/
theorem pureWZ2LineClassNormalizationExactPlaneMap_lipschitz_on_slice
    {source : Set Point3} {y0 : ℝ}
    (hsourceSlice : ∀ point ∈ source, point 1 = y0)
    {rawNormal : {point : Point3 // point ∈ source} → Point3}
    {K : NNReal} (hrawLipschitz : LipschitzWith K rawNormal)
    (hrawUnit : ∀ point, ‖rawNormal point‖ = 1)
    (center : Point3) {lambda : ℝ} (hlambda : 1 ≤ lambda) :
    LipschitzWith (2 * K)
      (pureWZ2LineClassNormalizationExactPlaneMap rawNormal center
        (lt_of_lt_of_le (by norm_num) hlambda)) := by
  let lambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  let sourcePoint :=
    pureWZ2LineClassNormalizationExactSourcePoint
      (source := source) center lambdaPos
  apply LipschitzWith.of_dist_le_mul
  intro first second
  let firstRaw := rawNormal (sourcePoint first)
  let secondRaw := rawNormal (sourcePoint second)
  let firstTransported :=
    pureWZ2LineClassNormalizationNormal lambda firstRaw
  let secondTransported :=
    pureWZ2LineClassNormalizationNormal lambda secondRaw
  have hfirstLower : 1 / lambda ≤ ‖firstTransported‖ := by
    exact pureWZ2LineClassNormalizationNormal_norm_lower_of_unit hlambda
      (hrawUnit (sourcePoint first))
  have hsecondLower : 1 / lambda ≤ ‖secondTransported‖ := by
    exact pureWZ2LineClassNormalizationNormal_norm_lower_of_unit hlambda
      (hrawUnit (sourcePoint second))
  have hnormalization := normalization_lipschitz
    (by positivity : 0 < 1 / lambda) hfirstLower hsecondLower
  have htransport : ‖firstTransported - secondTransported‖ ≤
      ‖firstRaw - secondRaw‖ := by
    have heq : firstTransported - secondTransported =
        pureWZ2LineClassNormalizationNormal lambda
          (firstRaw - secondRaw) := by
      ext coordinate
      fin_cases coordinate <;>
        simp [firstTransported, secondTransported,
          pureWZ2LineClassNormalizationNormal, point3, PiLp.sub_apply] <;> ring
    rw [heq]
    exact pureWZ2LineClassNormalizationNormal_norm_le hlambda _
  have hraw := hrawLipschitz.dist_le_mul
    (sourcePoint first) (sourcePoint second)
  rw [dist_eq_norm] at hraw
  have hinverse :=
    pureWZ2LineClassNormalization_inverse_dist_le_of_same_y
      hsourceSlice center hlambda first second
  change lambda * dist (sourcePoint first) (sourcePoint second) ≤
    dist (first : Point3) (second : Point3) at hinverse
  rw [dist_eq_norm]
  calc
    ‖pureWZ2LineClassNormalizationExactPlaneMap rawNormal center lambdaPos
          first -
        pureWZ2LineClassNormalizationExactPlaneMap rawNormal center lambdaPos
          second‖
        ≤ (2 / (1 / lambda)) *
            ‖firstTransported - secondTransported‖ := by
          simpa only [pureWZ2LineClassNormalizationExactPlaneMap,
            sourcePoint, firstRaw, secondRaw, firstTransported,
            secondTransported] using hnormalization
    _ ≤ (2 / (1 / lambda)) * ‖firstRaw - secondRaw‖ := by gcongr
    _ ≤ (2 / (1 / lambda)) *
          ((K : ℝ) * dist (sourcePoint first) (sourcePoint second)) := by
        gcongr
    _ ≤ ((2 * K : NNReal) : ℝ) * dist first second := by
      rw [NNReal.coe_mul]
      have hsourceDist : lambda *
          dist (sourcePoint first) (sourcePoint second) ≤
            dist (first : Point3) (second : Point3) := by
        simpa only [sourcePoint, Subtype.dist_eq] using hinverse
      have hKNonnegative : 0 ≤ (K : ℝ) := K.2
      have hsourceDistNonnegative :
          0 ≤ dist (sourcePoint first) (sourcePoint second) := dist_nonneg
      have hfactor : 2 / (1 / lambda) = 2 * lambda := by
        field_simp [lambdaPos.ne']
      rw [hfactor]
      calc
        2 * lambda * ((K : ℝ) *
            dist (sourcePoint first) (sourcePoint second)) =
          2 * (K : ℝ) *
            (lambda * dist (sourcePoint first) (sourcePoint second)) := by ring
        _ ≤ 2 * (K : ℝ) * dist (first : Point3) (second : Point3) := by
          exact mul_le_mul_of_nonneg_left hinverse
            (mul_nonneg (by norm_num) hKNonnegative)

/-- If the source normal has a uniformly nonzero second coordinate, the
line-class normalization gains the full inverse factor `lambda` on a
constant-`y` slice.  This is the quantitative form needed after completing
the Node-5 normal: the second coordinate is left unchanged by
`diag(lambda, 1, lambda)`, while source distances on the slice contract by
`lambda`. -/
theorem
    pureWZ2LineClassNormalizationExactPlaneMap_lipschitz_on_slice_of_coord_one_lower
    {source : Set Point3} {y0 lower : ℝ}
    (hsourceSlice : ∀ point ∈ source, point 1 = y0)
    {rawNormal : {point : Point3 // point ∈ source} → Point3}
    {K : NNReal} (hrawLipschitz : LipschitzWith K rawNormal)
    (hrawCoordLower : ∀ point, lower ≤ |rawNormal point 1|)
    (hlower : 0 < lower)
    (center : Point3) {lambda : ℝ} (hlambda : 1 ≤ lambda) :
    LipschitzWith
      ⟨2 * (K : ℝ) / (lower * lambda), by positivity⟩
      (pureWZ2LineClassNormalizationExactPlaneMap rawNormal center
        (lt_of_lt_of_le (by norm_num) hlambda)) := by
  let lambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  let sourcePoint :=
    pureWZ2LineClassNormalizationExactSourcePoint
      (source := source) center lambdaPos
  apply LipschitzWith.of_dist_le_mul
  intro first second
  let firstRaw := rawNormal (sourcePoint first)
  let secondRaw := rawNormal (sourcePoint second)
  let firstTransported :=
    pureWZ2LineClassNormalizationNormal lambda firstRaw
  let secondTransported :=
    pureWZ2LineClassNormalizationNormal lambda secondRaw
  have hfirstLower : lower ≤ ‖firstTransported‖ := by
    have hcoordinate := PiLp.norm_apply_le firstTransported (1 : Fin 3)
    have hcoordinateValue : firstTransported 1 = firstRaw 1 := by
      simp [firstTransported,
        pureWZ2LineClassNormalizationNormal, point3]
    rw [Real.norm_eq_abs, hcoordinateValue] at hcoordinate
    exact (hrawCoordLower (sourcePoint first)).trans hcoordinate
  have hsecondLower : lower ≤ ‖secondTransported‖ := by
    have hcoordinate := PiLp.norm_apply_le secondTransported (1 : Fin 3)
    have hcoordinateValue : secondTransported 1 = secondRaw 1 := by
      simp [secondTransported,
        pureWZ2LineClassNormalizationNormal, point3]
    rw [Real.norm_eq_abs, hcoordinateValue] at hcoordinate
    exact (hrawCoordLower (sourcePoint second)).trans hcoordinate
  have hnormalization := normalization_lipschitz hlower
    hfirstLower hsecondLower
  have htransport : ‖firstTransported - secondTransported‖ ≤
      ‖firstRaw - secondRaw‖ := by
    have heq : firstTransported - secondTransported =
        pureWZ2LineClassNormalizationNormal lambda
          (firstRaw - secondRaw) := by
      ext coordinate
      fin_cases coordinate <;>
        simp [firstTransported, secondTransported,
          pureWZ2LineClassNormalizationNormal, point3, PiLp.sub_apply] <;> ring
    rw [heq]
    exact pureWZ2LineClassNormalizationNormal_norm_le hlambda _
  have hraw := hrawLipschitz.dist_le_mul
    (sourcePoint first) (sourcePoint second)
  rw [dist_eq_norm] at hraw
  have hinverse :=
    pureWZ2LineClassNormalization_inverse_dist_le_of_same_y
      hsourceSlice center hlambda first second
  change lambda * dist (sourcePoint first) (sourcePoint second) ≤
    dist (first : Point3) (second : Point3) at hinverse
  rw [dist_eq_norm]
  calc
    ‖pureWZ2LineClassNormalizationExactPlaneMap rawNormal center lambdaPos
          first -
        pureWZ2LineClassNormalizationExactPlaneMap rawNormal center lambdaPos
          second‖
        ≤ (2 / lower) * ‖firstTransported - secondTransported‖ := by
          simpa only [pureWZ2LineClassNormalizationExactPlaneMap,
            sourcePoint, firstRaw, secondRaw, firstTransported,
            secondTransported] using hnormalization
    _ ≤ (2 / lower) * ‖firstRaw - secondRaw‖ := by gcongr
    _ ≤ (2 / lower) *
          ((K : ℝ) * dist (sourcePoint first) (sourcePoint second)) := by
        gcongr
    _ ≤ (⟨2 * (K : ℝ) / (lower * lambda), by positivity⟩ : NNReal) *
          dist first second := by
      change (2 / lower) * ((K : ℝ) *
          dist (sourcePoint first) (sourcePoint second)) ≤
        (2 * (K : ℝ) / (lower * lambda)) *
          dist (first : Point3) (second : Point3)
      have hfactor : 0 ≤ 2 * (K : ℝ) / lower := by positivity
      calc
        (2 / lower) * ((K : ℝ) *
            dist (sourcePoint first) (sourcePoint second)) =
          (2 * (K : ℝ) / lower) *
            dist (sourcePoint first) (sourcePoint second) := by ring
        _ ≤ (2 * (K : ℝ) / lower) *
            (dist (first : Point3) (second : Point3) / lambda) := by
          gcongr
          exact (le_div_iff₀ lambdaPos).2 (by simpa [mul_comm] using hinverse)
        _ = (2 * (K : ℝ) / (lower * lambda)) *
            dist (first : Point3) (second : Point3) := by
          field_simp [hlower.ne', lambdaPos.ne']

/-- A constant second coordinate of the raw normal field is enough to gain
the full inverse factor `lambda`; the source set itself need not lie in a
constant-`y` slice. -/
theorem
    pureWZ2LineClassNormalizationExactPlaneMap_lipschitz_of_constant_coord_one
    {source : Set Point3} {normalY lower : ℝ}
    {rawNormal : {point : Point3 // point ∈ source} → Point3}
    {K : NNReal} (hrawLipschitz : LipschitzWith K rawNormal)
    (hrawY : ∀ point, rawNormal point 1 = normalY)
    (hrawCoordLower : lower ≤ |normalY|)
    (hlower : 0 < lower)
    (center : Point3) {lambda : ℝ} (hlambda : 1 ≤ lambda) :
    LipschitzWith
      ⟨2 * (K : ℝ) / (lower * lambda), by positivity⟩
      (pureWZ2LineClassNormalizationExactPlaneMap rawNormal center
        (lt_of_lt_of_le (by norm_num) hlambda)) := by
  let lambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  let sourcePoint :=
    pureWZ2LineClassNormalizationExactSourcePoint
      (source := source) center lambdaPos
  apply LipschitzWith.of_dist_le_mul
  intro first second
  let firstRaw := rawNormal (sourcePoint first)
  let secondRaw := rawNormal (sourcePoint second)
  let firstTransported :=
    pureWZ2LineClassNormalizationNormal lambda firstRaw
  let secondTransported :=
    pureWZ2LineClassNormalizationNormal lambda secondRaw
  have hfirstLower : lower ≤ ‖firstTransported‖ := by
    have hcoordinate := PiLp.norm_apply_le firstTransported (1 : Fin 3)
    have hcoordinateValue : firstTransported 1 = normalY := by
      simp [firstTransported, firstRaw, hrawY,
        pureWZ2LineClassNormalizationNormal, point3]
    rw [Real.norm_eq_abs, hcoordinateValue] at hcoordinate
    exact hrawCoordLower.trans hcoordinate
  have hsecondLower : lower ≤ ‖secondTransported‖ := by
    have hcoordinate := PiLp.norm_apply_le secondTransported (1 : Fin 3)
    have hcoordinateValue : secondTransported 1 = normalY := by
      simp [secondTransported, secondRaw, hrawY,
        pureWZ2LineClassNormalizationNormal, point3]
    rw [Real.norm_eq_abs, hcoordinateValue] at hcoordinate
    exact hrawCoordLower.trans hcoordinate
  have hnormalization := normalization_lipschitz hlower
    hfirstLower hsecondLower
  have hrawDifferenceY : (firstRaw - secondRaw) 1 = 0 := by
    simp [firstRaw, secondRaw, PiLp.sub_apply, hrawY]
  have htransport : ‖firstTransported - secondTransported‖ =
      ‖firstRaw - secondRaw‖ / lambda := by
    have heq : firstTransported - secondTransported =
        pureWZ2LineClassNormalizationNormal lambda
          (firstRaw - secondRaw) := by
      ext coordinate
      fin_cases coordinate <;>
        simp [firstTransported, secondTransported,
          pureWZ2LineClassNormalizationNormal, point3, PiLp.sub_apply] <;> ring
    rw [heq]
    have hvector :
        pureWZ2LineClassNormalizationNormal lambda
            (firstRaw - secondRaw) =
          (1 / lambda : ℝ) • (firstRaw - secondRaw) := by
      ext coordinate
      fin_cases coordinate <;>
        simp [pureWZ2LineClassNormalizationNormal, point3,
          PiLp.sub_apply, PiLp.smul_apply, hrawDifferenceY] <;>
        field_simp [lambdaPos.ne']
    rw [hvector, norm_smul, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr lambdaPos)]
    ring
  have hraw := hrawLipschitz.dist_le_mul
    (sourcePoint first) (sourcePoint second)
  have hinverse := pureWZ2LineClassNormalization_source_dist_le
    center hlambda (sourcePoint first) (sourcePoint second)
  rw [dist_eq_norm]
  calc
    ‖pureWZ2LineClassNormalizationExactPlaneMap rawNormal center lambdaPos
          first -
        pureWZ2LineClassNormalizationExactPlaneMap rawNormal center lambdaPos
          second‖
        ≤ (2 / lower) * ‖firstTransported - secondTransported‖ := by
          simpa only [pureWZ2LineClassNormalizationExactPlaneMap,
            sourcePoint, firstRaw, secondRaw, firstTransported,
            secondTransported] using hnormalization
    _ = (2 / lower) * (‖firstRaw - secondRaw‖ / lambda) := by rw [htransport]
    _ ≤ (2 / lower) *
          (((K : ℝ) * dist (sourcePoint first) (sourcePoint second)) /
            lambda) := by
        gcongr
        simpa [dist_eq_norm] using hraw
    _ ≤ (2 / lower) *
          (((K : ℝ) * dist (first : Point3) (second : Point3)) /
            lambda) := by
        gcongr
        exact pureWZ2LineClassNormalization_source_dist_le center hlambda
          (sourcePoint first) (sourcePoint second) |>.trans_eq <| by
            rw [pureWZ2LineClassNormalizationMap_exactSourcePoint,
              pureWZ2LineClassNormalizationMap_exactSourcePoint]
    _ = (⟨2 * (K : ℝ) / (lower * lambda), by positivity⟩ : NNReal) *
          dist first second := by
      change (2 / lower) * (((K : ℝ) *
          dist (first : Point3) (second : Point3)) / lambda) =
        (2 * (K : ℝ) / (lower * lambda)) *
          dist (first : Point3) (second : Point3)
      field_simp [hlower.ne', lambdaPos.ne']

/-- Exact projection covariance for a fixed normal under the line-class
normalization. -/
theorem pureWZ2LineClassNormalization_local_projection_difference
    (center first second normal : Point3)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    let transported := pureWZ2LineClassNormalizationNormal lambda normal
    let normalized := (‖transported‖⁻¹ : ℝ) • transported
    inner ℝ (pureWZ2LineClassNormalizationMap center lambda first) normalized -
        inner ℝ (pureWZ2LineClassNormalizationMap center lambda second)
          normalized =
      (1 / ‖transported‖) *
        (inner ℝ first normal - inner ℝ second normal) := by
  dsimp only
  let transported := pureWZ2LineClassNormalizationNormal lambda normal
  have hmapDifference :
      pureWZ2LineClassNormalizationMap center lambda first -
          pureWZ2LineClassNormalizationMap center lambda second =
        pureWZ2LineClassNormalizationLinear lambda (first - second) := by
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2LineClassNormalizationMap,
        pureWZ2LineClassNormalizationLinear, point3, PiLp.sub_apply] <;> ring
  rw [← inner_sub_left, hmapDifference, inner_smul_right,
    pureWZ2LineClassNormalization_inner_identity hlambda, inner_sub_left]
  ring

/-- Local AD transfer through the line-class normalization on an arbitrary
target subset inside a specified ball. -/
theorem pureWZ2_lineClassNormalization_local_ad_of_image_in_ball
    {sourceDelta sourceRho targetRho targetRadius sigma y0 : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {C : ENNReal}
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (hsourceSlice : ∀ point ∈ sourceShading.union, point 1 = y0)
    (center : Point3) {lambda : ℝ} (hlambda : 1 ≤ lambda)
    (sourcePoint : {point : Point3 // point ∈ sourceShading.union})
    (targetPoint : Point3)
    (htargetPoint : targetPoint =
      pureWZ2LineClassNormalizationMap center lambda sourcePoint)
    (targetSet : Set Point3)
    (htargetImage : targetSet ⊆
      pureWZ2LineClassNormalizationMap center lambda '' sourceShading.union)
    (htargetBall : targetSet ⊆ Metric.closedBall targetPoint targetRadius)
    (hsourceRho : sourceDelta ≤ sourceRho)
    (hsourceRhoOne : sourceRho ≤ 1)
    (hball : targetRadius / lambda ≤ Real.sqrt sourceRho)
    (hbase : (1 /
        ‖pureWZ2LineClassNormalizationNormal lambda
          (sourceLocal.planeMap sourcePoint)‖) * sourceRho ≤ targetRho)
    (htargetRho : 0 < targetRho) :
    let transported := pureWZ2LineClassNormalizationNormal lambda
      (sourceLocal.planeMap sourcePoint)
    let targetNormal := (‖transported‖⁻¹ : ℝ) • transported
    PureWZ2PaperADSet1
      (scalarProjection targetNormal targetSet)
      targetRho (1 - sigma) C := by
  dsimp only
  let lambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  let transported := pureWZ2LineClassNormalizationNormal lambda
    (sourceLocal.planeMap sourcePoint)
  have hsourceNonzero : sourceLocal.planeMap sourcePoint ≠ 0 := by
    intro hzero
    have hunit := sourceLocal.planeMap_unit sourcePoint
    rw [hzero, norm_zero] at hunit
    norm_num at hunit
  have htransported : transported ≠ 0 := by
    exact fun hzero => hsourceNonzero
      (pureWZ2LineClassNormalizationNormal_injective lambdaPos.ne' <| by
        simpa [transported, pureWZ2LineClassNormalizationNormal, point3]
          using hzero)
  have htransportedNorm : 0 < ‖transported‖ :=
    norm_pos_iff.mpr htransported
  let targetNormal := (‖transported‖⁻¹ : ℝ) • transported
  let a := 1 / ‖transported‖
  let b := inner ℝ targetPoint targetNormal -
    a * inner ℝ (sourcePoint : Point3) (sourceLocal.planeMap sourcePoint)
  have ha : 0 < a := by positivity
  have hprojection : scalarProjection targetNormal targetSet ⊆
      (fun value : ℝ => a * value + b) ''
        scalarProjection (sourceLocal.planeMap sourcePoint)
          (sourceShading.union ∩
            Metric.closedBall (sourcePoint : Point3)
              (Real.sqrt sourceRho)) := by
    rintro value ⟨target, htargetSet, rfl⟩
    rcases htargetImage htargetSet with
      ⟨source, hsource, hsourceTargetEq⟩
    have hsourceDistance : dist source (sourcePoint : Point3) ≤
        dist target targetPoint / lambda := by
      have hscaled := pureWZ2LineClassNormalization_source_dist_le_of_same_y
        hlambda center source sourcePoint <| by
          rw [hsourceSlice source hsource,
            hsourceSlice sourcePoint sourcePoint.property]
      apply (le_div_iff₀ lambdaPos).2
      simpa [hsourceTargetEq, htargetPoint, mul_comm] using hscaled
    have hsourceBall : source ∈
        Metric.closedBall (sourcePoint : Point3) (Real.sqrt sourceRho) := by
      rw [Metric.mem_closedBall]
      exact hsourceDistance.trans <| hball.trans' <| by
        gcongr
        exact htargetBall htargetSet
    refine ⟨inner ℝ source (sourceLocal.planeMap sourcePoint),
      ⟨source, ⟨hsource, hsourceBall⟩, rfl⟩, ?_⟩
    have hdifference := pureWZ2LineClassNormalization_local_projection_difference
      center source sourcePoint (sourceLocal.planeMap sourcePoint) lambdaPos
    dsimp only [transported, targetNormal, a, b] at hdifference ⊢
    rw [htargetPoint]
    calc
      1 /
              ‖pureWZ2LineClassNormalizationNormal lambda
                (sourceLocal.planeMap sourcePoint)‖ *
            inner ℝ source (sourceLocal.planeMap sourcePoint) +
          (inner ℝ
              (pureWZ2LineClassNormalizationMap center lambda sourcePoint)
              ((‖pureWZ2LineClassNormalizationNormal lambda
                  (sourceLocal.planeMap sourcePoint)‖⁻¹ : ℝ) •
                pureWZ2LineClassNormalizationNormal lambda
                  (sourceLocal.planeMap sourcePoint)) -
            1 /
              ‖pureWZ2LineClassNormalizationNormal lambda
                (sourceLocal.planeMap sourcePoint)‖ *
              inner ℝ (sourcePoint : Point3)
                (sourceLocal.planeMap sourcePoint)) =
          inner ℝ
            (pureWZ2LineClassNormalizationMap center lambda source)
            ((‖pureWZ2LineClassNormalizationNormal lambda
                (sourceLocal.planeMap sourcePoint)‖⁻¹ : ℝ) •
              pureWZ2LineClassNormalizationNormal lambda
                (sourceLocal.planeMap sourcePoint)) := by
            linarith [hdifference]
      _ = inner ℝ target
            ((‖pureWZ2LineClassNormalizationNormal lambda
                (sourceLocal.planeMap sourcePoint)‖⁻¹ : ℝ) •
              pureWZ2LineClassNormalizationNormal lambda
                (sourceLocal.planeMap sourcePoint)) := by
            exact congrArg (fun point => inner ℝ point _) hsourceTargetEq
  exact pureWZ2_combined_affine_isotropic_local_ad sourceLocal sourcePoint
    targetNormal targetSet hsourceRho hsourceRhoOne ha htargetRho hbase
    hprojection

end Kakeya.Assouad

end
