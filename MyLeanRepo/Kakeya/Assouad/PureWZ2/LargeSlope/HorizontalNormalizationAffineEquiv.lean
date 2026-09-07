import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicCenteredMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalMap

/-!
# Affine packaging of the slope-preserving horizontal normalization

The post-Section-6 map scales the two horizontal coordinates by the same
positive factor and leaves height unchanged.  This file packages that map,
and its composition with the exact triangular map, as affine equivalences so
all later family, shading, measure, and normal transports can share one map.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- Linear horizontal dilation by `lambda`, leaving height unchanged. -/
noncomputable def pureWZ2HorizontalDilationLinearEquiv
    (lambda : ℝ) (hlambda : 0 < lambda) : Point3 ≃ₗ[ℝ] Point3 :=
  pureWZ2AffineDiagonalLinearEquiv 0 (1 / lambda) 1 lambda
    (one_div_ne_zero hlambda.ne') (by norm_num) hlambda.ne'

/-- The horizontal dilation about `horizontalCenter` as an affine equivalence. -/
noncomputable def pureWZ2HorizontalDilationAffineEquiv
    (horizontalCenter : Point3) (lambda : ℝ) (hlambda : 0 < lambda) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  AffineEquiv.ofLinearEquiv
    (pureWZ2HorizontalDilationLinearEquiv lambda hlambda)
    horizontalCenter 0

@[simp] theorem pureWZ2HorizontalDilationLinearEquiv_apply
    (lambda : ℝ) (hlambda : 0 < lambda) (vector : Point3) :
    pureWZ2HorizontalDilationLinearEquiv lambda hlambda vector =
      point3 (lambda * vector 0) (lambda * vector 1) (vector 2) := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2HorizontalDilationLinearEquiv,
      pureWZ2AffineDiagonalLinearEquiv, pureWZ2AffineDiagonalLinear,
      pureWZ2HorizontalNorm, point3, hlambda.ne']

@[simp] theorem pureWZ2HorizontalDilationAffineEquiv_apply
    (horizontalCenter : Point3) (lambda : ℝ) (hlambda : 0 < lambda)
    (point : Point3) :
    pureWZ2HorizontalDilationAffineEquiv horizontalCenter lambda hlambda point =
      point3
        (lambda * (point 0 - horizontalCenter 0))
        (lambda * (point 1 - horizontalCenter 1))
        (point 2 - horizontalCenter 2) := by
  rw [pureWZ2HorizontalDilationAffineEquiv,
    AffineEquiv.ofLinearEquiv_apply]
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2HorizontalDilationLinearEquiv,
      pureWZ2AffineDiagonalLinearEquiv, pureWZ2AffineDiagonalLinear,
      pureWZ2HorizontalNorm, point3, hlambda.ne']

/-- The exact triangular map followed by horizontal dilation. -/
def pureWZ2HorizontalNormalizedMap
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (point : Point3) : Point3 :=
  let image := anisotropicCenteredRescalingMap g c d m anisotropicCenter point
  point3
    (lambda * (image 0 - horizontalCenter 0))
    (lambda * (image 1 - horizontalCenter 1))
    (image 2 - horizontalCenter 2)

/-- The combined triangular and horizontal normalization as one affine
equivalence. -/
noncomputable def pureWZ2HorizontalNormalizedAffineEquiv
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  (anisotropicCenteredRescalingAffineEquiv
    g c d m anisotropicCenter hcd hm).trans
      (pureWZ2HorizontalDilationAffineEquiv
        horizontalCenter lambda hlambda)

@[simp] theorem pureWZ2HorizontalNormalizedAffineEquiv_apply
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (point : Point3) :
    pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda point =
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
        horizontalCenter lambda point := by
  rw [pureWZ2HorizontalNormalizedAffineEquiv, AffineEquiv.trans_apply,
    anisotropicCenteredRescalingAffineEquiv_apply,
    pureWZ2HorizontalDilationAffineEquiv_apply]
  rfl

@[simp] theorem pureWZ2HorizontalNormalizedAffineEquiv_linear
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda) :
    (pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
      horizontalCenter lambda hcd hm hlambda).linear =
      (anisotropicCenteredRescalingAffineEquiv
        g c d m anisotropicCenter hcd hm).linear.trans
        (pureWZ2HorizontalDilationAffineEquiv
          horizontalCenter lambda hlambda).linear :=
  rfl

@[simp] theorem pureWZ2HorizontalNormalizedAffineEquiv_linear_apply
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (vector : Point3) :
    (pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
      horizontalCenter lambda hcd hm hlambda).linear vector =
      point3
        (lambda * (dPhiLin g c d m vector) 0)
        (lambda * (dPhiLin g c d m vector) 1)
        ((dPhiLin g c d m vector) 2) := by
  rw [pureWZ2HorizontalNormalizedAffineEquiv_linear]
  change pureWZ2HorizontalDilationLinearEquiv lambda hlambda
      ((anisotropicCenteredRescalingAffineEquiv
        g c d m anisotropicCenter hcd hm).linear vector) = _
  rw [anisotropicCenteredRescalingAffineEquiv_linear]
  change pureWZ2HorizontalDilationLinearEquiv lambda hlambda
      (anisotropicRescalingLinearEquiv g c d m hcd hm vector) = _
  rw [anisotropicRescalingLinearEquiv_apply,
    pureWZ2HorizontalDilationLinearEquiv_apply,
    anisotropicRescalingLinearMap_apply_eq_dPhiLin]

/-- Exact Jacobian of horizontal dilation. -/
theorem pureWZ2HorizontalDilationLinearEquiv_abs_det
    (lambda : ℝ) (hlambda : 0 < lambda) :
    |LinearMap.det
      (pureWZ2HorizontalDilationLinearEquiv lambda hlambda :
        Point3 →ₗ[ℝ] Point3)| = lambda ^ 2 := by
  let linear : Point3 →ₗ[ℝ] Point3 :=
    (pureWZ2HorizontalDilationLinearEquiv lambda hlambda :
      Point3 →ₗ[ℝ] Point3)
  let basis : Module.Basis (Fin 3) ℝ Point3 := PiLp.basisFun 2 ℝ (Fin 3)
  have hmatrix : LinearMap.toMatrix basis basis linear =
      !![lambda, 0, 0; 0, lambda, 0; 0, 0, 1] := by
    ext i j
    have hentry : (LinearMap.toMatrix basis basis linear) i j =
        (linear (basis j)) i := by
      rw [LinearMap.toMatrix_apply]
      exact PiLp.basisFun_repr 2 ℝ (Fin 3) (linear (basis j)) i
    rw [hentry]
    fin_cases i <;> fin_cases j <;>
      simp [linear, basis, pureWZ2HorizontalDilationLinearEquiv,
        pureWZ2AffineDiagonalLinearEquiv, pureWZ2AffineDiagonalLinear,
        pureWZ2HorizontalNorm, PiLp.basisFun_apply, point3, hlambda.ne']
  change |LinearMap.det linear| = lambda ^ 2
  rw [← LinearMap.det_toMatrix basis linear, hmatrix, Matrix.det_fin_three]
  simp [abs_of_pos hlambda]
  ring

/-- Exact Jacobian of the combined triangular and horizontal map. -/
theorem pureWZ2HorizontalNormalizedAffineEquiv_abs_det
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda) :
    |LinearMap.det
      ((pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
        horizontalCenter lambda hcd hm hlambda).linear :
          Point3 →ₗ[ℝ] Point3)| = m * lambda ^ 2 := by
  rw [pureWZ2HorizontalNormalizedAffineEquiv_linear]
  change |LinearMap.det
      (((pureWZ2HorizontalDilationAffineEquiv horizontalCenter lambda hlambda).linear :
        Point3 →ₗ[ℝ] Point3).comp
        ((anisotropicCenteredRescalingAffineEquiv
          g c d m anisotropicCenter hcd hm).linear :
            Point3 →ₗ[ℝ] Point3))| = _
  rw [LinearMap.det_comp, abs_mul]
  have hanisotropic :
      |LinearMap.det
        ((anisotropicCenteredRescalingAffineEquiv
          g c d m anisotropicCenter hcd hm).linear :
            Point3 →ₗ[ℝ] Point3)| = m := by
    rw [anisotropicCenteredRescalingAffineEquiv_linear]
    change |LinearMap.det (anisotropicRescalingLinearMap g c d m)| = m
    rw [anisotropicRescalingLinear_det g hcd hm, abs_of_pos hm]
  have hhorizontal :
      |LinearMap.det
        ((pureWZ2HorizontalDilationAffineEquiv horizontalCenter lambda hlambda).linear :
          Point3 →ₗ[ℝ] Point3)| = lambda ^ 2 :=
    pureWZ2HorizontalDilationLinearEquiv_abs_det lambda hlambda
  rw [hanisotropic, hhorizontal]
  ring

/-- Exact volume scaling for the combined normalization. -/
theorem volume_image_pureWZ2HorizontalNormalizedMap
    (g : SlopeFunction) (c d m : ℝ)
    (anisotropicCenter horizontalCenter : Point3) (lambda : ℝ)
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (source : Set Point3) :
    volume
        (pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' source) =
      ENNReal.ofReal (m * lambda ^ 2) * volume source := by
  let equivalence := pureWZ2HorizontalNormalizedAffineEquiv
    g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
  have himage :
      pureWZ2HorizontalNormalizedMap g c d m anisotropicCenter
          horizontalCenter lambda '' source = equivalence '' source := by
    ext point
    simp only [Set.mem_image]
    constructor
    · rintro ⟨preimage, hpreimage, rfl⟩
      exact ⟨preimage, hpreimage,
        (pureWZ2HorizontalNormalizedAffineEquiv_apply
          g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
          preimage)⟩
    · rintro ⟨preimage, hpreimage, rfl⟩
      exact ⟨preimage, hpreimage,
        (pureWZ2HorizontalNormalizedAffineEquiv_apply
          g c d m anisotropicCenter horizontalCenter lambda hcd hm hlambda
          preimage).symm⟩
  rw [himage, wz2PaperAffineEquiv_volume_image_eq,
    pureWZ2HorizontalNormalizedAffineEquiv_abs_det]

end Kakeya.Assouad

end
