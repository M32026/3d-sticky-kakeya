import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalNormalizationAffineEquiv
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalGrainTransfer

/-!
# Exact normal under horizontal normalization

This file isolates the inverse-transpose calculation for the post-Section-6
horizontal dilation `(x,y,z) ↦ (lambda*x,lambda*y,z)`.  Unlike an isotropic
similarity, this dilation preserves the already normalized slope while
allowing the large horizontal components of the exact normal to be divided by
`lambda`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Inverse transpose of the horizontal dilation. -/
def pureWZ2HorizontalNormalizedNormal (lambda : ℝ) (normal : Point3) : Point3 :=
  point3 (normal 0 / lambda) (normal 1 / lambda) (normal 2)

/-- The inverse-transpose identity for horizontal dilation. -/
theorem pureWZ2HorizontalNormalized_inner_identity
    {lambda : ℝ} (hlambda : lambda ≠ 0)
    (direction normal : Point3) :
    inner ℝ (point3 (lambda * direction 0) (lambda * direction 1)
        (direction 2))
      (pureWZ2HorizontalNormalizedNormal lambda normal) =
      inner ℝ direction normal := by
  simp [pureWZ2HorizontalNormalizedNormal, point3, PiLp.inner_apply,
    Fin.sum_univ_succ]
  field_simp [hlambda]

/-- Composition of the triangular inverse transpose and the horizontal
normalization inverse transpose. -/
def pureWZ2HorizontalNormalizedExactNormal
    (g : SlopeFunction) (c d m lambda : ℝ) (normal : Point3) : Point3 :=
  pureWZ2HorizontalNormalizedNormal lambda (dPhiInvT g c d m normal)

/-- The combined affine linear map and its exact inverse-transpose normal
preserve the incidence pairing. -/
theorem pureWZ2HorizontalNormalizedAffineEquiv_inner_identity
    (g : SlopeFunction) {c d m lambda : ℝ}
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (anisotropicCenter horizontalCenter direction normal : Point3) :
    inner ℝ
        ((pureWZ2HorizontalNormalizedAffineEquiv
          g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda).linear
          direction)
        (pureWZ2HorizontalNormalizedExactNormal g c d m lambda normal) =
      inner ℝ direction normal := by
  rw [pureWZ2HorizontalNormalizedAffineEquiv_linear_apply]
  change inner ℝ
      (point3
        (lambda * (dPhiLin g c d m direction) 0)
        (lambda * (dPhiLin g c d m direction) 1)
        ((dPhiLin g c d m direction) 2))
      (pureWZ2HorizontalNormalizedNormal lambda
        (dPhiInvT g c d m normal)) = _
  rw [pureWZ2HorizontalNormalized_inner_identity hlambda.ne']
  exact dPhi_inner_identity g c d m hcd hm direction normal

/-- The horizontal inverse-transpose factor is injective for nonzero scale. -/
theorem pureWZ2HorizontalNormalizedNormal_injective
    {lambda : ℝ} (hlambda : lambda ≠ 0) :
    Function.Injective (pureWZ2HorizontalNormalizedNormal lambda) := by
  intro first second heq
  have hzero := congrArg (fun point : Point3 => point 0) heq
  have hone := congrArg (fun point : Point3 => point 1) heq
  have htwo := congrArg (fun point : Point3 => point 2) heq
  simp only [pureWZ2HorizontalNormalizedNormal, point3_coord0] at hzero
  simp only [pureWZ2HorizontalNormalizedNormal, point3_coord1] at hone
  simp only [pureWZ2HorizontalNormalizedNormal, point3_coord2] at htwo
  ext coordinate
  fin_cases coordinate
  · exact (div_left_inj' hlambda).mp hzero
  · exact (div_left_inj' hlambda).mp hone
  · exact htwo

/-- Normalizing the transformed direction and exact inverse-transpose normal
divides the original incidence only by the two transformation norms. -/
theorem pureWZ2HorizontalNormalized_incidence_preservation
    (g : SlopeFunction) {c d m lambda : ℝ}
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (anisotropicCenter horizontalCenter direction normal : Point3)
    (hdirection : direction ≠ 0) (hnormal : normal ≠ 0) :
    let imageDirection :=
      (pureWZ2HorizontalNormalizedAffineEquiv
        g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda).linear
        direction
    let imageNormal :=
      pureWZ2HorizontalNormalizedExactNormal g c d m lambda normal
    inner ℝ (‖imageDirection‖⁻¹ • imageDirection)
        (‖imageNormal‖⁻¹ • imageNormal) =
      inner ℝ direction normal / (‖imageDirection‖ * ‖imageNormal‖) := by
  dsimp only
  let equivalence := pureWZ2HorizontalNormalizedAffineEquiv
    g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
  let imageDirection := equivalence.linear direction
  let imageNormal :=
    pureWZ2HorizontalNormalizedExactNormal g c d m lambda normal
  have himageDirection : imageDirection ≠ 0 := by
    intro hzero
    apply hdirection
    apply equivalence.linear.injective
    simpa [imageDirection] using hzero
  have himageNormal : imageNormal ≠ 0 := by
    intro hzero
    have hinverseZero : dPhiInvT g c d m normal = 0 := by
      apply pureWZ2HorizontalNormalizedNormal_injective hlambda.ne'
      have hleft : pureWZ2HorizontalNormalizedNormal lambda
          (dPhiInvT g c d m normal) = 0 := by
        simpa only [imageNormal,
          pureWZ2HorizontalNormalizedExactNormal] using hzero
      rw [hleft]
      simp [pureWZ2HorizontalNormalizedNormal, point3]
    apply hnormal
    apply dPhiInvT_injective g c d m hcd hm
    simpa [dPhiInvT, point3] using hinverseZero
  have hinner : inner ℝ imageDirection imageNormal =
      inner ℝ direction normal := by
    simpa only [equivalence, imageDirection, imageNormal] using
      pureWZ2HorizontalNormalizedAffineEquiv_inner_identity
        g hcd hm hlambda anisotropicCenter horizontalCenter direction normal
  rw [inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply, star_trivial]
  rw [hinner]
  field_simp [norm_ne_zero_iff.mpr himageDirection,
    norm_ne_zero_iff.mpr himageNormal]

/-- A positive lower bound `q` for the product of the two transformation
norms turns source incidence `sourceDelta` into target incidence
`sourceDelta / q`. -/
theorem pureWZ2HorizontalNormalized_incidence_le_div
    (g : SlopeFunction) {c d m lambda sourceDelta q : ℝ}
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (anisotropicCenter horizontalCenter direction normal : Point3)
    (hdirection : direction ≠ 0) (hnormal : normal ≠ 0)
    (hsource : |inner ℝ direction normal| ≤ sourceDelta)
    (hq : 0 < q)
    (hproduct :
      q ≤
        ‖(pureWZ2HorizontalNormalizedAffineEquiv
          g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda).linear
            direction‖ *
        ‖pureWZ2HorizontalNormalizedExactNormal g c d m lambda normal‖) :
    let imageDirection :=
      (pureWZ2HorizontalNormalizedAffineEquiv
        g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda).linear
        direction
    let imageNormal :=
      pureWZ2HorizontalNormalizedExactNormal g c d m lambda normal
    |inner ℝ (‖imageDirection‖⁻¹ • imageDirection)
        (‖imageNormal‖⁻¹ • imageNormal)| ≤ sourceDelta / q := by
  dsimp only
  rw [pureWZ2HorizontalNormalized_incidence_preservation
    g hcd hm hlambda anisotropicCenter horizontalCenter direction normal
      hdirection hnormal, abs_div, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hsourceNonneg : 0 ≤ sourceDelta :=
    (abs_nonneg (inner ℝ direction normal)).trans hsource
  exact div_le_div₀ hsourceNonneg hsource hq hproduct

/-- Compatibility form of `pureWZ2HorizontalNormalized_incidence_le_div`
at the traditional lower bound `q = 1/3`. -/
theorem pureWZ2HorizontalNormalized_incidence_le_three_mul
    (g : SlopeFunction) {c d m lambda sourceDelta : ℝ}
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (anisotropicCenter horizontalCenter direction normal : Point3)
    (hdirection : direction ≠ 0) (hnormal : normal ≠ 0)
    (hsource : |inner ℝ direction normal| ≤ sourceDelta)
    (hproduct :
      1 / 3 ≤
        ‖(pureWZ2HorizontalNormalizedAffineEquiv
          g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda).linear
            direction‖ *
        ‖pureWZ2HorizontalNormalizedExactNormal g c d m lambda normal‖) :
    let imageDirection :=
      (pureWZ2HorizontalNormalizedAffineEquiv
        g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda).linear
        direction
    let imageNormal :=
      pureWZ2HorizontalNormalizedExactNormal g c d m lambda normal
    |inner ℝ (‖imageDirection‖⁻¹ • imageDirection)
        (‖imageNormal‖⁻¹ • imageNormal)| ≤ 3 * sourceDelta := by
  have hresult := pureWZ2HorizontalNormalized_incidence_le_div
    g hcd hm hlambda anisotropicCenter horizontalCenter direction normal
      hdirection hnormal hsource (q := (1 / 3 : ℝ)) (by norm_num) hproduct
  simpa [div_eq_mul_inv, mul_comm] using hresult

/-- The horizontal normalization does not enlarge the triangular transported
normal when `lambda >= 1`. -/
theorem pureWZ2HorizontalNormalizedExactNormal_norm_le
    (g : SlopeFunction) (c d m : ℝ) {lambda : ℝ}
    (hlambda : 1 ≤ lambda) (normal : Point3) :
    ‖pureWZ2HorizontalNormalizedExactNormal g c d m lambda normal‖ ≤
      ‖dPhiInvT g c d m normal‖ := by
  let transported := dPhiInvT g c d m normal
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  have hcoord := point3_coord_norm_sq transported
  have htarget := point3_coord_norm_sq
    (pureWZ2HorizontalNormalizedExactNormal g c d m lambda normal)
  have hzero : pureWZ2HorizontalNormalizedExactNormal g c d m lambda normal 0 =
      transported 0 / lambda := by
    simp [pureWZ2HorizontalNormalizedExactNormal,
      pureWZ2HorizontalNormalizedNormal, transported, point3]
  have hone : pureWZ2HorizontalNormalizedExactNormal g c d m lambda normal 1 =
      transported 1 / lambda := by
    simp [pureWZ2HorizontalNormalizedExactNormal,
      pureWZ2HorizontalNormalizedNormal, transported, point3]
  have htwo : pureWZ2HorizontalNormalizedExactNormal g c d m lambda normal 2 =
      transported 2 := by
    simp [pureWZ2HorizontalNormalizedExactNormal,
      pureWZ2HorizontalNormalizedNormal, transported, point3]
  have hdivZero : (transported 0 / lambda) ^ 2 ≤ transported 0 ^ 2 := by
    have hsquare : 1 ≤ lambda ^ 2 := by nlinarith [sq_nonneg lambda]
    rw [div_pow]
    exact div_le_self (sq_nonneg _) hsquare
  have hdivOne : (transported 1 / lambda) ^ 2 ≤ transported 1 ^ 2 := by
    have hsquare : 1 ≤ lambda ^ 2 := by nlinarith [sq_nonneg lambda]
    rw [div_pow]
    exact div_le_self (sq_nonneg _) hsquare
  have hsquares :
      ‖pureWZ2HorizontalNormalizedExactNormal g c d m lambda normal‖ ^ 2 ≤
        ‖transported‖ ^ 2 := by
    rw [htarget, hcoord, hzero, hone, htwo]
    linarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquares

/-- The horizontal normalization retains the vertical component of the exact
normal and hence any lower bound coming from that coordinate. -/
theorem pureWZ2HorizontalNormalizedExactNormal_norm_ge_vertical
    (g : SlopeFunction) (c d m lambda : ℝ) (normal : Point3) :
    |dPhiInvT g c d m normal 2| ≤
      ‖pureWZ2HorizontalNormalizedExactNormal g c d m lambda normal‖ := by
  have hcoord := PiLp.norm_apply_le
    (pureWZ2HorizontalNormalizedExactNormal g c d m lambda normal)
    (2 : Fin 3)
  simpa [pureWZ2HorizontalNormalizedExactNormal,
    pureWZ2HorizontalNormalizedNormal, point3, Real.norm_eq_abs] using hcoord

end Kakeya.Assouad

end
