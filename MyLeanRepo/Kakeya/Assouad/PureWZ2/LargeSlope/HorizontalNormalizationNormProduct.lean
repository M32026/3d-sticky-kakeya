import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalNormalizationNormal

/-!
# Direction-normal products under horizontal normalization

A horizontal dilation divides the first two covector coordinates by `lambda`
while leaving the third unchanged, and expands the first two vector
coordinates by `lambda`.  For `lambda >= 1`, the resulting direction-normal
product loses at most the explicit factor `lambda`.
-/

noncomputable section

namespace Kakeya.Assouad

theorem pureWZ2HorizontalNormalizedNormal_norm_ge_div
    {lambda : ℝ} (hlambda : 1 ≤ lambda) (normal : Point3) :
    ‖normal‖ / lambda ≤
      ‖pureWZ2HorizontalNormalizedNormal lambda normal‖ := by
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  have hsource := point3_coord_norm_sq normal
  have htarget := point3_coord_norm_sq
    (pureWZ2HorizontalNormalizedNormal lambda normal)
  have hzero : pureWZ2HorizontalNormalizedNormal lambda normal 0 =
      normal 0 / lambda := by
    simp [pureWZ2HorizontalNormalizedNormal, point3]
  have hone : pureWZ2HorizontalNormalizedNormal lambda normal 1 =
      normal 1 / lambda := by
    simp [pureWZ2HorizontalNormalizedNormal, point3]
  have htwo : pureWZ2HorizontalNormalizedNormal lambda normal 2 =
      normal 2 := by
    simp [pureWZ2HorizontalNormalizedNormal, point3]
  have hlambdaSq : 1 ≤ lambda ^ 2 := by nlinarith
  have hsquares : ‖normal‖ ^ 2 ≤
      (lambda *
        ‖pureWZ2HorizontalNormalizedNormal lambda normal‖) ^ 2 := by
    rw [hsource, mul_pow, htarget, hzero, hone, htwo]
    field_simp [hlambdaPos.ne']
    nlinarith [sq_nonneg (normal 0), sq_nonneg (normal 1),
      sq_nonneg (normal 2),
      mul_le_mul_of_nonneg_right hlambdaSq (sq_nonneg (normal 2))]
  have hnorm : ‖normal‖ ≤
      lambda * ‖pureWZ2HorizontalNormalizedNormal lambda normal‖ :=
    (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hlambdaPos.le (norm_nonneg _))).mp hsquares
  exact (div_le_iff₀ hlambdaPos).2 (by simpa [mul_comm] using hnorm)

theorem pureWZ2HorizontalNormalizedLinear_norm_ge
    (g : SlopeFunction) {c d m lambda : ℝ}
    (hcd : c < d) (hm : 0 < m) (hlambda : 1 ≤ lambda)
    (anisotropicCenter horizontalCenter vector : Point3) :
    ‖dPhiLin g c d m vector‖ ≤
      ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
        horizontalCenter lambda hcd hm (lt_of_lt_of_le (by norm_num) hlambda)).linear
          vector‖ := by
  let source := dPhiLin g c d m vector
  let target :=
    (pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
      horizontalCenter lambda hcd hm (lt_of_lt_of_le (by norm_num) hlambda)).linear
        vector
  have hsourceSq := point3_coord_norm_sq source
  have htargetSq := point3_coord_norm_sq target
  have hcoords : target =
      point3 (lambda * source 0) (lambda * source 1) (source 2) := by
    simp [target, source, pureWZ2HorizontalNormalizedAffineEquiv_linear_apply]
  have hlambdaSq : 1 ≤ lambda ^ 2 := by nlinarith
  have hzero : source 0 ^ 2 ≤ (lambda * source 0) ^ 2 := by
    nlinarith [sq_nonneg (source 0),
      mul_le_mul_of_nonneg_right hlambdaSq (sq_nonneg (source 0))]
  have hone : source 1 ^ 2 ≤ (lambda * source 1) ^ 2 := by
    nlinarith [sq_nonneg (source 1),
      mul_le_mul_of_nonneg_right hlambdaSq (sq_nonneg (source 1))]
  have hsquares : ‖source‖ ^ 2 ≤ ‖target‖ ^ 2 := by
    rw [hsourceSq, htargetSq, hcoords]
    simp [point3]
    nlinarith [sq_nonneg (source 2)]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquares

theorem pureWZ2HorizontalNormalized_norm_product_ge
    (g : SlopeFunction) {c d m lambda : ℝ}
    (hcd : c < d) (hm : 0 < m) (hlambda : 1 ≤ lambda)
    (anisotropicCenter horizontalCenter direction normal : Point3) :
    ‖dPhiLin g c d m direction‖ * ‖dPhiInvT g c d m normal‖ ≤
      lambda *
        (‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m
            anisotropicCenter horizontalCenter lambda hcd hm
              (lt_of_lt_of_le (by norm_num) hlambda)).linear direction‖ *
          ‖pureWZ2HorizontalNormalizedExactNormal g c d m lambda normal‖) := by
  have hdirection := pureWZ2HorizontalNormalizedLinear_norm_ge g hcd hm
    hlambda anisotropicCenter horizontalCenter direction
  have hnormal := pureWZ2HorizontalNormalizedNormal_norm_ge_div hlambda
    (dPhiInvT g c d m normal)
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  have hnormal' : ‖dPhiInvT g c d m normal‖ ≤
      lambda *
        ‖pureWZ2HorizontalNormalizedExactNormal g c d m lambda normal‖ := by
    have hscaled := (div_le_iff₀ hlambdaPos).mp hnormal
    simpa [pureWZ2HorizontalNormalizedExactNormal, mul_comm] using hscaled
  calc
    ‖dPhiLin g c d m direction‖ * ‖dPhiInvT g c d m normal‖ ≤
        ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m
            anisotropicCenter horizontalCenter lambda hcd hm hlambdaPos).linear
            direction‖ *
          (lambda *
            ‖pureWZ2HorizontalNormalizedExactNormal g c d m lambda normal‖) := by
      exact mul_le_mul hdirection hnormal' (norm_nonneg _) (norm_nonneg _)
    _ = lambda *
        (‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m
            anisotropicCenter horizontalCenter lambda hcd hm hlambdaPos).linear
            direction‖ *
          ‖pureWZ2HorizontalNormalizedExactNormal g c d m lambda normal‖) := by
      ring

end Kakeya.Assouad

end
