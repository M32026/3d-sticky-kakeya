import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.VolumeScaling
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalGrainTransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.TransferredLocalGrains

/-!
# The exact affine equivalence in Proposition 6.5

This is the affine map written in `wz2_65.tex`, with no replacement by a
fixed rotation or a diagonal surrogate:

`(x,y,z) ↦ (x + g((c+d)/2)y, (m(d-c)/2)y, 2(z-c)/(d-c)-1)`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The two existing definitions of the linear part of the Section 6 map
agree. -/
theorem anisotropicRescalingLinearMap_apply_eq_dPhiLin
    (g : SlopeFunction) (c d m : ℝ) (vector : Point3) :
    anisotropicRescalingLinearMap g c d m vector =
      dPhiLin g c d m vector := by
  ext coordinate
  fin_cases coordinate <;>
    simp [anisotropicRescalingLinearMap_apply_zero,
      anisotropicRescalingLinearMap_apply_one,
      anisotropicRescalingLinearMap_apply_two, dPhiLin, point3]

/-- Invertible linear part of the exact Section 6 anisotropic map. -/
noncomputable def anisotropicRescalingLinearEquiv
    (g : SlopeFunction) (c d m : ℝ)
    (hcd : c < d) (hm : 0 < m) :
    Point3 ≃ₗ[ℝ] Point3 :=
  LinearEquiv.ofInjectiveEndo
    (anisotropicRescalingLinearMap g c d m) <| by
      intro first second heq
      apply dPhiLin_injective g c d m hcd hm
      rw [← anisotropicRescalingLinearMap_apply_eq_dPhiLin,
        ← anisotropicRescalingLinearMap_apply_eq_dPhiLin]
      exact heq

@[simp] theorem anisotropicRescalingLinearEquiv_apply
    (g : SlopeFunction) (c d m : ℝ)
    (hcd : c < d) (hm : 0 < m) (vector : Point3) :
    anisotropicRescalingLinearEquiv g c d m hcd hm vector =
      anisotropicRescalingLinearMap g c d m vector := by
  rfl

/-- The exact triangular map as one affine equivalence. -/
noncomputable def anisotropicRescalingAffineEquiv
    (g : SlopeFunction) (c d m : ℝ)
    (hcd : c < d) (hm : 0 < m) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  AffineEquiv.ofLinearEquiv
    (anisotropicRescalingLinearEquiv g c d m hcd hm)
    0 (point3 0 0 (2 * (-c) / (d - c) - 1))

@[simp] theorem anisotropicRescalingAffineEquiv_apply
    (g : SlopeFunction) (c d m : ℝ)
    (hcd : c < d) (hm : 0 < m) (point : Point3) :
    anisotropicRescalingAffineEquiv g c d m hcd hm point =
      anisotropicRescalingMap g c d m point := by
  rw [anisotropicRescalingAffineEquiv, AffineEquiv.ofLinearEquiv_apply]
  rw [vsub_eq_sub, sub_zero, vadd_eq_add]
  change anisotropicRescalingLinearMap g c d m point +
      point3 0 0 (2 * (-c) / (d - c) - 1) = _
  exact (anisotropicRescalingMap_eq g c d m point).symm

@[simp] theorem anisotropicRescalingAffineEquiv_symm_apply
    (g : SlopeFunction) (c d m : ℝ)
    (hcd : c < d) (hm : 0 < m) (point : Point3) :
    (anisotropicRescalingAffineEquiv g c d m hcd hm).symm point =
      anisotropicRescalingInverse g c d m point := by
  apply (anisotropicRescalingAffineEquiv g c d m hcd hm).injective
  rw [AffineEquiv.apply_symm_apply, anisotropicRescalingAffineEquiv_apply]
  exact (anisotropicRescaling_left_inverse g c d m hcd hm point).symm

@[simp] theorem anisotropicRescalingAffineEquiv_linear
    (g : SlopeFunction) (c d m : ℝ)
    (hcd : c < d) (hm : 0 < m) :
    (anisotropicRescalingAffineEquiv g c d m hcd hm).linear =
      anisotropicRescalingLinearEquiv g c d m hcd hm := by
  rfl

end Kakeya.Assouad

end
