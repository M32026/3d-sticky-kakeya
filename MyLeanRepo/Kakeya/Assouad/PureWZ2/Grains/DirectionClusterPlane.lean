import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FinestCellPlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperDirectionPacking

/-!
# Plane incidence for one concentrated direction cluster

The dense-close half of the plane-map dichotomy does not need a transverse
pair.  A unit normal to one central tube direction is automatically almost
orthogonal to every unit direction in the same small cross-product cluster.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open InnerProductGeometry

/-- If `n` is a unit vector orthogonal to the unit vector `u`, then the
incidence of another unit vector `v` with `n` is controlled by the sine of
the angle between `u` and `v`. -/
lemma abs_inner_le_cross_norm_of_orthogonal_unit
    (u v n : Point3)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hn : ‖n‖ = 1)
    (hun : inner ℝ u n = 0) :
    |inner ℝ v n| ≤ ‖wz1Cross u v‖ := by
  let a : ℝ := inner ℝ u v
  have hinner : inner ℝ (v - a • u) n = inner ℝ v n := by
    rw [inner_sub_left, inner_smul_left, hun]
    simp
  have hcs : |inner ℝ (v - a • u) n| ≤ ‖v - a • u‖ := by
    have h := abs_real_inner_le_norm (v - a • u) n
    rw [hn, mul_one] at h
    exact h
  have hresidual_sq : ‖v - a • u‖ ^ 2 = 1 - a ^ 2 := by
    rw [norm_sub_sq_real, hv, norm_smul, hu, mul_one, inner_smul_right]
    have huv : inner ℝ v u = a := by
      dsimp only [a]
      exact (real_inner_comm v u).symm
    rw [huv]
    simp only [Real.norm_eq_abs]
    nlinarith [sq_abs a]
  have hcross_sq : ‖wz1Cross u v‖ ^ 2 = 1 - a ^ 2 := by
    simpa only [a] using cross_norm_sq u v hu hv
  have hnorm_eq : ‖v - a • u‖ = ‖wz1Cross u v‖ := by
    nlinarith [norm_nonneg (v - a • u), norm_nonneg (wz1Cross u v)]
  rw [← hinner]
  exact hcs.trans_eq hnorm_eq

/-- The canonical unit normal used by the finest-cell construction controls
every direction in the close cluster of its center. -/
lemma orthogonalNormal_cluster_incidence
    (u v : Point3)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |inner ℝ v (orthogonalNormal u)| ≤ ‖wz1Cross u v‖ := by
  exact abs_inner_le_cross_norm_of_orthogonal_unit
    u v (orthogonalNormal u) hu hv
    (orthogonalNormal_unit u) (orthogonalNormal_orthogonal u)

/-- Strict cluster membership yields the weak incidence inequality at the
same threshold. -/
lemma orthogonalNormal_incidence_of_cross_lt
    (u v : Point3)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {kappa : ℝ} (hclose : ‖wz1Cross u v‖ < kappa) :
    |inner ℝ v (orthogonalNormal u)| ≤ kappa :=
  (orthogonalNormal_cluster_incidence u v hu hv).trans hclose.le

end Kakeya.Assouad.PureWZ2

end
