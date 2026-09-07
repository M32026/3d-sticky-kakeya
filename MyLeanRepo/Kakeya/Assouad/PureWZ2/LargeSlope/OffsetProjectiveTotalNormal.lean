import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.OffsetShearProjectiveNormal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LineClassNormalizationFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalGrainTransfer

/-!
# Total offset-projective normal transport

This is the elementary linear algebra for the bounded offset shear followed by
the diagonal map `(x,y,z) ↦ (lambda*x,b*y,lambda*S*z)`.  The normal formula
keeps track of the projective scalar explicitly: it is not an equality with
the unprojectivized shear normal.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The point map `diag(lambda,b,lambda*S) ∘ H_a`. -/
def pureWZ2OffsetProjectiveTotalLinear
    (a b S lambda : ℝ) : Point3 → Point3 :=
  fun point => point3 (lambda * (point 0 + a * point 1))
    (b * point 1) (lambda * S * point 2)

/-- The explicit inverse of `pureWZ2OffsetProjectiveTotalLinear`. -/
def pureWZ2OffsetProjectiveTotalInverse
    (a b S lambda : ℝ) : Point3 → Point3 :=
  fun point => point3 (point 0 / lambda - a * (point 1 / b))
    (point 1 / b) (point 2 / (lambda * S))

/-- The exact inverse-transpose map on unprojectivized normals. -/
def pureWZ2OffsetProjectiveTotalExactNormal
    (a b S lambda : ℝ) : Point3 → Point3 :=
  fun normal => point3 (normal 0 / lambda)
    ((normal 1 - a * normal 0) / b) (normal 2 / (lambda * S))

/-- The representative in the chart whose middle coordinate is one. -/
def pureWZ2OffsetProjectiveTotalNormal
    (b S lambda : ℝ) : Point3 → Point3 :=
  fun projectiveNormal => point3 (b / lambda * projectiveNormal 0) 1
    (b / (lambda * S) * projectiveNormal 2)

/-- Unit representative of the transported projective normal. -/
def pureWZ2OffsetProjectiveTotalNormalizedNormal
    (b S lambda : ℝ) : Point3 → Point3 :=
  fun projectiveNormal => ‖pureWZ2OffsetProjectiveTotalNormal b S lambda projectiveNormal‖⁻¹ •
    pureWZ2OffsetProjectiveTotalNormal b S lambda projectiveNormal

/-- The total linear map is exactly the Section-6 triangular differential
followed by `diag(lambda,1,lambda)`. -/
theorem pureWZ2OffsetProjectiveTotalLinear_eq_lineClass_dPhi
    (g : SlopeFunction) (c d m lambda : ℝ) (direction : Point3) :
    pureWZ2OffsetProjectiveTotalLinear
        (g (c + (d - c) / 2)) (m * (d - c) / 2)
        (2 / (d - c)) lambda direction =
      pureWZ2LineClassNormalizationLinear lambda
        (dPhiLin g c d m direction) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2OffsetProjectiveTotalLinear,
      pureWZ2LineClassNormalizationLinear, dPhiLin, point3] <;> ring

/-- Normalizing after the triangular differential and after the final
line-class map is the same as normalizing the one total linear image. -/
theorem pureWZ2LineClassNormalizationDirection_dPhi_eq
    (g : SlopeFunction) {c d m lambda : ℝ}
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    {direction : Point3} (hdirection : direction ≠ 0) :
    pureWZ2LineClassNormalizationDirection lambda hlambda
        ((‖dPhiLin g c d m direction‖⁻¹ : ℝ) •
          dPhiLin g c d m direction) =
      (‖pureWZ2OffsetProjectiveTotalLinear
          (g (c + (d - c) / 2)) (m * (d - c) / 2)
          (2 / (d - c)) lambda direction‖⁻¹ : ℝ) •
        pureWZ2OffsetProjectiveTotalLinear
          (g (c + (d - c) / 2)) (m * (d - c) / 2)
          (2 / (d - c)) lambda direction := by
  let firstImage := dPhiLin g c d m direction
  have hfirstImage : firstImage ≠ 0 := by
    intro hzero
    apply hdirection
    apply dPhiLin_injective g c d m hcd hm
    simpa [firstImage, dPhiLin, point3] using hzero
  let totalImage := pureWZ2LineClassNormalizationLinear lambda firstImage
  have hlinear :
      pureWZ2LineClassNormalizationLinear lambda
          ((‖firstImage‖⁻¹ : ℝ) • firstImage) =
        ‖firstImage‖⁻¹ • totalImage := by
    ext coordinate
    fin_cases coordinate <;>
      simp [firstImage, totalImage, pureWZ2LineClassNormalizationLinear,
        point3, PiLp.smul_apply] <;> ring
  have hleft :
      pureWZ2LineClassNormalizationDirection lambda hlambda
          ((‖firstImage‖⁻¹ : ℝ) • firstImage) =
        NormedSpace.normalize
          (pureWZ2LineClassNormalizationLinear lambda
            ((‖firstImage‖⁻¹ : ℝ) • firstImage)) := by
    simp only [pureWZ2LineClassNormalizationDirection,
      pureWZ2LineClassNormalizationLinearEquiv_apply, NormedSpace.normalize]
  have hright :
      (‖pureWZ2OffsetProjectiveTotalLinear
          (g (c + (d - c) / 2)) (m * (d - c) / 2)
          (2 / (d - c)) lambda direction‖⁻¹ : ℝ) •
        pureWZ2OffsetProjectiveTotalLinear
          (g (c + (d - c) / 2)) (m * (d - c) / 2)
          (2 / (d - c)) lambda direction =
        NormedSpace.normalize totalImage := by
    rw [pureWZ2OffsetProjectiveTotalLinear_eq_lineClass_dPhi]
    rfl
  change pureWZ2LineClassNormalizationDirection lambda hlambda
      ((‖firstImage‖⁻¹ : ℝ) • firstImage) = _
  rw [hleft, hright, hlinear]
  exact NormedSpace.normalize_smul_of_pos
    (inv_pos.mpr (norm_pos_iff.mpr hfirstImage)) totalImage

/-- A vertical-chart source direction has total-image norm at least one once
the final line-class scale is at least the selected interval length. -/
theorem pureWZ2OffsetProjectiveTotalLinear_norm_lower_one
    {a b S lambda : ℝ} (hS : 0 < S) (hlambda : 0 < lambda)
    (hscale : 1 ≤ lambda * S / 2)
    (direction : Point3) (hvertical : 1 / 2 ≤ |direction 2|) :
    1 ≤ ‖pureWZ2OffsetProjectiveTotalLinear a b S lambda direction‖ := by
  have hcoord := PiLp.norm_apply_le
    (pureWZ2OffsetProjectiveTotalLinear a b S lambda direction) (2 : Fin 3)
  have hcoordValue :
      |pureWZ2OffsetProjectiveTotalLinear a b S lambda direction 2| =
        (lambda * S) * |direction 2| := by
    simp [pureWZ2OffsetProjectiveTotalLinear, point3, abs_mul,
      abs_of_pos hlambda, abs_of_pos hS]
  rw [Real.norm_eq_abs, hcoordValue] at hcoord
  have hproduct : 1 ≤ (lambda * S) * |direction 2| := by
    calc
      1 ≤ (lambda * S) * (1 / 2 : ℝ) := by simpa [div_eq_mul_inv] using hscale
      _ ≤ (lambda * S) * |direction 2| := by
        gcongr
  exact hproduct.trans hcoord

/-- A vector in the projective chart has norm at least one. -/
theorem pureWZ2OffsetProjectiveTotalNormal_norm_lower
    (b S lambda : ℝ) (projectiveNormal : Point3) :
    1 ≤ ‖pureWZ2OffsetProjectiveTotalNormal b S lambda projectiveNormal‖ := by
  have hcoord := PiLp.norm_apply_le
    (pureWZ2OffsetProjectiveTotalNormal b S lambda projectiveNormal) (1 : Fin 3)
  simpa [pureWZ2OffsetProjectiveTotalNormal, point3, Real.norm_eq_abs] using hcoord

theorem pureWZ2OffsetProjectiveTotalNormalizedNormal_unit
    (b S lambda : ℝ) (projectiveNormal : Point3) :
    ‖pureWZ2OffsetProjectiveTotalNormalizedNormal b S lambda projectiveNormal‖ = 1 := by
  apply NormedSpace.norm_normalize
  apply norm_pos_iff.mp
  exact zero_lt_one.trans_le
    (pureWZ2OffsetProjectiveTotalNormal_norm_lower b S lambda projectiveNormal)

theorem pureWZ2OffsetProjectiveTotal_inverse_apply
    {a b S lambda : ℝ} (hb : b ≠ 0) (hS : S ≠ 0) (hlambda : lambda ≠ 0)
    (point : Point3) :
    pureWZ2OffsetProjectiveTotalInverse a b S lambda
      (pureWZ2OffsetProjectiveTotalLinear a b S lambda point) = point := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2OffsetProjectiveTotalInverse,
      pureWZ2OffsetProjectiveTotalLinear, point3] <;>
    field_simp [hb, hS, hlambda] <;> ring

/-- Exact incidence before projectivizing the shear normal. -/
theorem pureWZ2OffsetProjectiveTotal_exactNormal_inner
    {a b S lambda : ℝ} (hb : b ≠ 0) (hS : S ≠ 0) (hlambda : lambda ≠ 0)
    (direction normal : Point3) :
    inner ℝ (pureWZ2OffsetProjectiveTotalLinear a b S lambda direction)
      (pureWZ2OffsetProjectiveTotalExactNormal a b S lambda normal) =
      inner ℝ direction normal := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp [pureWZ2OffsetProjectiveTotalLinear,
    pureWZ2OffsetProjectiveTotalExactNormal, point3, Fin.sum_univ_succ]
  field_simp [hb, hS, hlambda]
  ring

/-- Projective incidence includes precisely the scalar used to make the
second coordinate one. -/
theorem pureWZ2OffsetProjectiveTotal_projective_inner
    {a b S lambda : ℝ} (hb : b ≠ 0) (hS : S ≠ 0) (hlambda : lambda ≠ 0)
    (direction normal : Point3)
    (hw : pureWZ2OffsetShearNormal a normal 1 ≠ 0) :
    inner ℝ (pureWZ2OffsetProjectiveTotalLinear a b S lambda direction)
      (pureWZ2OffsetProjectiveTotalNormal b S lambda
        (pureWZ2OffsetShearProjectiveNormal a normal)) =
      (b / pureWZ2OffsetShearNormal a normal 1) * inner ℝ direction normal := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp [pureWZ2OffsetProjectiveTotalLinear,
    pureWZ2OffsetProjectiveTotalNormal, pureWZ2OffsetShearProjectiveNormal,
    pureWZ2OffsetShearNormal, point3, Fin.sum_univ_succ]
  have hw' : normal 1 - a * normal 0 ≠ 0 := by
    simpa [pureWZ2OffsetShearNormal, point3] using hw
  field_simp [hb, hS, hlambda, hw']
  ring

/-- In the projective chart, diagonal transport contracts differences by
`b/lambda`; the middle coordinate cancels. -/
theorem pureWZ2OffsetProjectiveTotalNormal_sub_norm_le
    {b S lambda : ℝ} (hb : 0 < b) (hS : 1 ≤ S) (hlambda : 1 ≤ lambda)
    (first second : Point3) (hfirst : first 1 = 1) (hsecond : second 1 = 1) :
    ‖pureWZ2OffsetProjectiveTotalNormal b S lambda first -
        pureWZ2OffsetProjectiveTotalNormal b S lambda second‖ ≤
      (b / lambda) * ‖first - second‖ := by
  have hlambda_pos : 0 < lambda := zero_lt_one.trans_le hlambda
  have hS_pos : 0 < S := zero_lt_one.trans_le hS
  have hcoeff : 0 ≤ b / lambda := div_nonneg hb.le hlambda_pos.le
  have hthird : (b / (lambda * S)) ^ 2 ≤ (b / lambda) ^ 2 := by
    rw [div_pow, div_pow]
    have hSsquare : 1 ≤ S ^ 2 := by nlinarith [sq_nonneg S]
    have hdenom : lambda ^ 2 ≤ (lambda * S) ^ 2 := by
      rw [mul_pow]
      simpa using mul_le_mul_of_nonneg_left hSsquare (sq_nonneg lambda)
    exact div_le_div_of_nonneg_left (sq_nonneg b) (sq_pos_of_pos hlambda_pos) hdenom
  have hsource := point3_coord_norm_sq (first - second)
  have htarget := point3_coord_norm_sq
    (pureWZ2OffsetProjectiveTotalNormal b S lambda first -
      pureWZ2OffsetProjectiveTotalNormal b S lambda second)
  have hsquares :
      ‖pureWZ2OffsetProjectiveTotalNormal b S lambda first -
          pureWZ2OffsetProjectiveTotalNormal b S lambda second‖ ^ 2 ≤
        ((b / lambda) * ‖first - second‖) ^ 2 := by
    rw [htarget]
    rw [show (b / lambda * ‖first - second‖) ^ 2 =
      (b / lambda) ^ 2 * ((first - second) 0 ^ 2 +
        (first - second) 1 ^ 2 + (first - second) 2 ^ 2) by
      rw [mul_pow, hsource]]
    simp [pureWZ2OffsetProjectiveTotalNormal, point3, hfirst, hsecond]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hcoeff (norm_nonneg _))).mp hsquares

/-- A pointwise version usable for composing a source Lipschitz field. -/
theorem pureWZ2OffsetProjectiveTotalNormal_lipschitz
    {X : Type*} [PseudoMetricSpace X] {b S lambda : ℝ} {K : NNReal}
    {field : X → Point3}
    (hb : 0 < b) (hS : 1 ≤ S) (hlambda : 1 ≤ lambda)
    (hfield : LipschitzWith K field) (hcoord : ∀ point, field point 1 = 1) :
    LipschitzWith ⟨(b / lambda) * K, by positivity⟩
      (fun point => pureWZ2OffsetProjectiveTotalNormal b S lambda (field point)) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  change ‖pureWZ2OffsetProjectiveTotalNormal b S lambda (field first) -
      pureWZ2OffsetProjectiveTotalNormal b S lambda (field second)‖ ≤
    ((⟨b / lambda * K, by positivity⟩ : NNReal) : ℝ) * dist first second
  calc
    ‖pureWZ2OffsetProjectiveTotalNormal b S lambda (field first) -
        pureWZ2OffsetProjectiveTotalNormal b S lambda (field second)‖ ≤
      (b / lambda) * ‖field first - field second‖ :=
        pureWZ2OffsetProjectiveTotalNormal_sub_norm_le hb hS hlambda _ _
          (hcoord first) (hcoord second)
    _ ≤ (b / lambda) * ((K : ℝ) * dist first second) := by
      gcongr
      simpa [dist_eq_norm] using hfield.dist_le_mul first second
    _ = ((⟨b / lambda * K, by positivity⟩ : NNReal) : ℝ) * dist first second := by
      simp [NNReal.coe_mul]
      ring

/-- Combining projective transport with a controlled preimage map and final
normalization.  The stated constant leaves a factor two of slack. -/
theorem pureWZ2OffsetProjectiveTotalNormalizedNormal_lipschitz_preimage
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {b S lambda : ℝ} {K : NNReal} {preimage : X → Y} {field : Y → Point3}
    (hb : 0 < b) (hb_one : b ≤ 1) (hS : 1 ≤ S) (hlambda : 1 ≤ lambda)
    (hpreimage : ∀ first second,
      b * dist (preimage first) (preimage second) ≤ 3 * dist first second)
    (hfield : LipschitzWith K field)
    (hcoord : ∀ point, field point 1 = 1) :
    LipschitzWith ⟨6 * (K : ℝ) / lambda, by positivity⟩
      (fun point => pureWZ2OffsetProjectiveTotalNormalizedNormal b S lambda
        (field (preimage point))) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  have hlambda_pos : 0 < lambda := zero_lt_one.trans_le hlambda
  let imageFirst := pureWZ2OffsetProjectiveTotalNormal b S lambda
    (field (preimage first))
  let imageSecond := pureWZ2OffsetProjectiveTotalNormal b S lambda
    (field (preimage second))
  have hfirst_norm : 1 ≤ ‖imageFirst‖ :=
    by simpa [imageFirst] using
      pureWZ2OffsetProjectiveTotalNormal_norm_lower b S lambda (field (preimage first))
  have hsecond_norm : 1 ≤ ‖imageSecond‖ :=
    by simpa [imageSecond] using
      pureWZ2OffsetProjectiveTotalNormal_norm_lower b S lambda (field (preimage second))
  have hraw : ‖imageFirst - imageSecond‖ ≤
      (3 * (K : ℝ) / lambda) * dist first second := by
    calc
      ‖imageFirst - imageSecond‖ ≤
          (b / lambda) * ‖field (preimage first) - field (preimage second)‖ :=
        pureWZ2OffsetProjectiveTotalNormal_sub_norm_le hb hS hlambda _ _
          (hcoord _) (hcoord _)
      _ ≤ (b / lambda) * ((K : ℝ) * dist (preimage first) (preimage second)) := by
        gcongr
        simpa [dist_eq_norm] using hfield.dist_le_mul (preimage first) (preimage second)
      _ = (K : ℝ) / lambda *
          (b * dist (preimage first) (preimage second)) := by ring
      _ ≤ (K : ℝ) / lambda * (3 * dist first second) := by
        exact mul_le_mul_of_nonneg_left (hpreimage first second)
          (div_nonneg K.2 hlambda_pos.le)
      _ = (3 * (K : ℝ) / lambda) * dist first second := by ring
  change ‖NormedSpace.normalize imageFirst - NormedSpace.normalize imageSecond‖ ≤
    ((⟨6 * (K : ℝ) / lambda, by positivity⟩ : NNReal) : ℝ) * dist first second
  calc
    ‖NormedSpace.normalize imageFirst - NormedSpace.normalize imageSecond‖ ≤
        ‖imageFirst - imageSecond‖ :=
      norm_normalize_sub_normalize_le_norm_sub hfirst_norm hsecond_norm
    _ ≤ (3 * (K : ℝ) / lambda) * dist first second := hraw
    _ ≤ (6 * (K : ℝ) / lambda) * dist first second := by
      have hK : 0 ≤ (K : ℝ) := K.2
      have hdist : 0 ≤ dist first second := dist_nonneg
      have hcoeff : 0 ≤ (K : ℝ) / lambda :=
        div_nonneg hK hlambda_pos.le
      calc
        (3 * (K : ℝ) / lambda) * dist first second =
            3 * ((K : ℝ) / lambda * dist first second) := by ring
        _ ≤ 6 * ((K : ℝ) / lambda * dist first second) := by
          exact mul_le_mul_of_nonneg_right (by norm_num)
            (mul_nonneg hcoeff hdist)
        _ = (6 * (K : ℝ) / lambda) * dist first second := by ring
    _ = ((⟨6 * (K : ℝ) / lambda, by positivity⟩ : NNReal) : ℝ) *
        dist first second := by simp

/-- After unit normalization, projective incidence is bounded by the source
incidence and the chart denominator. -/
theorem pureWZ2OffsetProjectiveTotal_normalized_inner_abs_le
    {a b S lambda c delta : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hS : S ≠ 0) (hlambda : lambda ≠ 0)
    (direction normal : Point3)
    (hw : pureWZ2OffsetShearNormal a normal 1 ≠ 0)
    (hw_lower : c ≤ |pureWZ2OffsetShearNormal a normal 1|)
    (hsource : |inner ℝ direction normal| ≤ delta) :
    |inner ℝ (pureWZ2OffsetProjectiveTotalLinear a b S lambda direction)
      (pureWZ2OffsetProjectiveTotalNormalizedNormal b S lambda
        (pureWZ2OffsetShearProjectiveNormal a normal))| ≤ (b / c) * delta := by
  let image := pureWZ2OffsetProjectiveTotalNormal b S lambda
    (pureWZ2OffsetShearProjectiveNormal a normal)
  have himage : 1 ≤ ‖image‖ := by
    simpa [image] using
      (pureWZ2OffsetProjectiveTotalNormal_norm_lower b S lambda
        (pureWZ2OffsetShearProjectiveNormal a normal))
  have hprojective := pureWZ2OffsetProjectiveTotal_projective_inner
    (a := a) hb.ne' hS hlambda direction normal hw
  have hraw : |inner ℝ (pureWZ2OffsetProjectiveTotalLinear a b S lambda direction) image| ≤
      (b / c) * delta := by
    rw [hprojective, abs_mul]
    have hratio : |b / pureWZ2OffsetShearNormal a normal 1| ≤ b / c := by
      rw [abs_div, abs_of_pos hb]
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le hc hw_lower) hb.le
    have hdelta : 0 ≤ delta := (abs_nonneg _).trans hsource
    gcongr
  change |inner ℝ (pureWZ2OffsetProjectiveTotalLinear a b S lambda direction)
      (NormedSpace.normalize image)| ≤ _
  rw [NormedSpace.normalize, inner_smul_right]
  simp only [starRingEnd_apply, star_trivial, abs_mul, Real.norm_eq_abs, abs_inv, abs_norm]
  calc
    ‖image‖⁻¹ * |inner ℝ (pureWZ2OffsetProjectiveTotalLinear a b S lambda direction) image| ≤
        1 * |inner ℝ (pureWZ2OffsetProjectiveTotalLinear a b S lambda direction) image| := by
      gcongr
      exact (inv_le_one₀ (zero_lt_one.trans_le himage)).mpr himage
    _ = |inner ℝ (pureWZ2OffsetProjectiveTotalLinear a b S lambda direction) image| := by ring
    _ ≤ (b / c) * delta := hraw

/-- Normalizing the transported direction does not enlarge the projective
incidence bound when the total linear image has norm at least one. -/
theorem pureWZ2OffsetProjectiveTotal_normalizedDirection_inner_abs_le
    {a b S lambda c sourceDelta targetDelta : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hS : S ≠ 0)
    (hlambda : lambda ≠ 0)
    (direction normal : Point3)
    (hw : pureWZ2OffsetShearNormal a normal 1 ≠ 0)
    (hw_lower : c ≤ |pureWZ2OffsetShearNormal a normal 1|)
    (hsource : |inner ℝ direction normal| ≤ sourceDelta)
    (hdirectionNorm : 1 ≤
      ‖pureWZ2OffsetProjectiveTotalLinear a b S lambda direction‖)
    (hbudget : (b / c) * sourceDelta ≤ targetDelta) :
    |inner ℝ
        ((‖pureWZ2OffsetProjectiveTotalLinear a b S lambda direction‖⁻¹ : ℝ) •
          pureWZ2OffsetProjectiveTotalLinear a b S lambda direction)
        (pureWZ2OffsetProjectiveTotalNormalizedNormal b S lambda
          (pureWZ2OffsetShearProjectiveNormal a normal))| ≤ targetDelta := by
  have hraw := pureWZ2OffsetProjectiveTotal_normalized_inner_abs_le
    hb hc hS hlambda direction normal hw hw_lower hsource
  have hnormPos : 0 <
      ‖pureWZ2OffsetProjectiveTotalLinear a b S lambda direction‖ :=
    zero_lt_one.trans_le hdirectionNorm
  have hinv :
      ‖pureWZ2OffsetProjectiveTotalLinear a b S lambda direction‖⁻¹ ≤ 1 :=
    (inv_le_one₀ hnormPos).2 hdirectionNorm
  rw [inner_smul_left]
  simp only [starRingEnd_apply, star_trivial, abs_mul, Real.norm_eq_abs,
    abs_inv, abs_norm]
  calc
    ‖pureWZ2OffsetProjectiveTotalLinear a b S lambda direction‖⁻¹ *
        |inner ℝ (pureWZ2OffsetProjectiveTotalLinear a b S lambda direction)
          (pureWZ2OffsetProjectiveTotalNormalizedNormal b S lambda
            (pureWZ2OffsetShearProjectiveNormal a normal))| ≤
        1 * ((b / c) * sourceDelta) := by gcongr
    _ = (b / c) * sourceDelta := one_mul _
    _ ≤ targetDelta := hbudget

/-- With `0 < b ≤ 1`, the inverse point map costs at most a safe factor
three after multiplying distances by `b`. -/
theorem pureWZ2OffsetProjectiveTotal_inverse_sub_norm_le_three
    {a b S lambda : ℝ} (hb : 0 < b) (hb_one : b ≤ 1)
    (hS : 1 ≤ S) (hlambda : 1 ≤ lambda) (ha : |a| ≤ 1 / 2)
    (first second : Point3) :
    b * ‖pureWZ2OffsetProjectiveTotalInverse a b S lambda first -
        pureWZ2OffsetProjectiveTotalInverse a b S lambda second‖ ≤
      3 * ‖first - second‖ := by
  have hlambda_pos : 0 < lambda := zero_lt_one.trans_le hlambda
  have hS_pos : 0 < S := zero_lt_one.trans_le hS
  let difference := first - second
  have hformula : pureWZ2OffsetProjectiveTotalInverse a b S lambda first -
      pureWZ2OffsetProjectiveTotalInverse a b S lambda second =
      point3 (difference 0 / lambda - a * (difference 1 / b))
        (difference 1 / b) (difference 2 / (lambda * S)) := by
    ext coordinate
    fin_cases coordinate <;>
      simp [pureWZ2OffsetProjectiveTotalInverse, difference, point3,
        PiLp.sub_apply] <;> ring
  have hzero : |b * (difference 0 / lambda - a * (difference 1 / b))| ≤
      3 / 2 * ‖difference‖ := by
    calc
      |b * (difference 0 / lambda - a * (difference 1 / b))| ≤
          |b * (difference 0 / lambda)| + |a * difference 1| := by
        have hrewrite : b * (difference 0 / lambda - a * (difference 1 / b)) =
            b * (difference 0 / lambda) - a * difference 1 := by
          field_simp [hb.ne']
        rw [hrewrite]
        have hb0 : b ≠ 0 := hb.ne'
        simpa [abs_mul] using abs_sub (b * (difference 0 / lambda)) (a * difference 1)
      _ ≤ ‖difference‖ + (1 / 2) * ‖difference‖ := by
        have h0 : |b * (difference 0 / lambda)| ≤ ‖difference‖ := by
          calc
            |b * (difference 0 / lambda)| = (b / lambda) * |difference 0| := by
              rw [abs_mul, abs_div, abs_of_pos hb, abs_of_pos hlambda_pos]
              ring
            _ ≤ 1 * ‖difference‖ := by
              have hratio : b / lambda ≤ 1 := by
                calc b / lambda ≤ b := (div_le_iff₀ hlambda_pos).mpr (by nlinarith)
                _ ≤ 1 := hb_one
              gcongr
              simpa [Real.norm_eq_abs] using PiLp.norm_apply_le difference (0 : Fin 3)
            _ = ‖difference‖ := by ring
        have h1 : |a * difference 1| ≤ (1 / 2) * ‖difference‖ := by
          rw [abs_mul]
          gcongr
          simpa [Real.norm_eq_abs] using PiLp.norm_apply_le difference (1 : Fin 3)
        linarith
      _ = 3 / 2 * ‖difference‖ := by ring
  have hone : |b * (difference 1 / b)| ≤ ‖difference‖ := by
    rw [abs_mul, abs_div, abs_of_pos hb]
    field_simp [hb.ne']
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le difference (1 : Fin 3)
  have htwo : |b * (difference 2 / (lambda * S))| ≤ ‖difference‖ := by
    calc
      |b * (difference 2 / (lambda * S))| = (b / (lambda * S)) * |difference 2| := by
        rw [abs_mul, abs_div, abs_of_pos hb, abs_of_pos (mul_pos hlambda_pos hS_pos)]
        ring
      _ ≤ 1 * ‖difference‖ := by
        have hratio : b / (lambda * S) ≤ 1 := by
          apply (div_le_one₀ (mul_pos hlambda_pos hS_pos)).mpr
          exact hb_one.trans (one_le_mul_of_one_le_of_one_le hlambda hS)
        gcongr
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le difference (2 : Fin 3)
      _ = ‖difference‖ := by ring
  have htarget := point3_coord_norm_sq
    (pureWZ2OffsetProjectiveTotalInverse a b S lambda first -
      pureWZ2OffsetProjectiveTotalInverse a b S lambda second)
  have hsource := point3_coord_norm_sq difference
  have hsquares :
      (b * ‖pureWZ2OffsetProjectiveTotalInverse a b S lambda first -
        pureWZ2OffsetProjectiveTotalInverse a b S lambda second‖) ^ 2 ≤
        (3 * ‖difference‖) ^ 2 := by
    have hform :
        (b * ‖pureWZ2OffsetProjectiveTotalInverse a b S lambda first -
          pureWZ2OffsetProjectiveTotalInverse a b S lambda second‖) ^ 2 =
        (b * (difference 0 / lambda - a * (difference 1 / b))) ^ 2 +
          (b * (difference 1 / b)) ^ 2 +
          (b * (difference 2 / (lambda * S))) ^ 2 := by
      rw [mul_pow, htarget, hformula]
      simp only [point3_coord0, point3_coord1, point3_coord2]
      ring
    rw [hform]
    have hzero_sq : (b * (difference 0 / lambda - a * (difference 1 / b))) ^ 2 ≤
        (3 / 2 * ‖difference‖) ^ 2 := by
      nlinarith [sq_abs (b * (difference 0 / lambda - a * (difference 1 / b))),
        abs_nonneg (b * (difference 0 / lambda - a * (difference 1 / b)))]
    have hone_sq : (b * (difference 1 / b)) ^ 2 ≤ ‖difference‖ ^ 2 := by
      nlinarith [sq_abs (b * (difference 1 / b)),
        abs_nonneg (b * (difference 1 / b))]
    have htwo_sq : (b * (difference 2 / (lambda * S))) ^ 2 ≤ ‖difference‖ ^ 2 := by
      nlinarith [sq_abs (b * (difference 2 / (lambda * S))),
        abs_nonneg (b * (difference 2 / (lambda * S)))]
    nlinarith [sq_nonneg ‖difference‖]
  exact (sq_le_sq₀ (mul_nonneg hb.le (norm_nonneg _)) (by positivity)).mp hsquares

end Kakeya.Assouad

end
