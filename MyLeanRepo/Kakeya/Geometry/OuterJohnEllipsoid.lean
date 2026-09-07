import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Existence
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.SymmetricCenter
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.SymmetricInclusion
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.GeneralInclusionMain
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Uniqueness

/-!
# Full outer John ellipsoid theorem

Adapted from `full_john_ellipsoid.tar.gz`; the source project records
upstream mathlib-extension commit `fe432d890160909112d6017e5fbced1eff9418de`.
-/


noncomputable section

open MeasureTheory
open scoped Pointwise Real

namespace JohnEllipsoid
namespace IsConvexBody

variable {n : ℕ} {K : Set (E n)}

theorem outerJohnEllipsoid_unique (hK : IsConvexBody K) (c : E n) (A : E n ≃ₗ[ℝ] E n)
    (h : IsOuterJohnEllipsoid K c A) :
    ellipsoid c A = hK.outerJohnEllipsoid := by
  let c0 : E n := hK.outerJohnEllipsoidCenter
  let A0 : E n ≃ₗ[ℝ] E n := hK.outerJohnEllipsoidMap
  have hE0 : IsOuterJohnEllipsoid K c0 A0 := hK.outerJohnEllipsoid_spec
  have h_main : ellipsoid c A = ellipsoid c0 A0 :=
    outerJohnEllipsoid_unique_main n hK c c0 A A0 h hE0
  have h_def : hK.outerJohnEllipsoid = ellipsoid c0 A0 := by rfl
  rw [h_def]
  exact h_main

/-- The outer Löwner–John ellipsoid theorem: `(1 / n) • (L - c) + c ⊆ K ⊆ L`. -/
theorem homothety_subset_outerJohnEllipsoid (hK : IsConvexBody K) :
    AffineMap.homothety hK.outerJohnEllipsoidCenter (n : ℝ)⁻¹ '' hK.outerJohnEllipsoid ⊆ K :=
  homothety_subset_outerJohnEllipsoid_main hK

/-- The outer Löwner–John ellipsoid theorem, centrally symmetric case: `(1 / √n) • (L - c) + c ⊆ K ⊆ L`. -/
theorem homothety_subset_outerJohnEllipsoid_of_symmetric (hK : IsConvexBody K)
    {z : E n} (hz : ∀ x : E n, x ∈ K → z + (z - x) ∈ K) :
    z = hK.outerJohnEllipsoidCenter ∧ AffineMap.homothety z (√(n : ℝ))⁻¹ '' hK.outerJohnEllipsoid ⊆ K := by
  by_cases hn : 0 < n
  · -- Case n > 0
    let c0 : E n := hK.outerJohnEllipsoidCenter
    let A0 : E n ≃ₗ[ℝ] E n := hK.outerJohnEllipsoidMap
    have hE0 : IsOuterJohnEllipsoid K c0 A0 := hK.outerJohnEllipsoid_spec
    have h_center : c0 = z := symmetric_center_eq_direct hn hz c0 A0 hE0 hK
    have h_incl : AffineMap.homothety z (√(n : ℝ))⁻¹ '' ellipsoid c0 A0 ⊆ K :=
      symmetric_inclusion hn hK hz hE0 h_center.symm
    have h_def : hK.outerJohnEllipsoid = ellipsoid c0 A0 := by rfl
    exact ⟨h_center.symm, by rw [h_def]; exact h_incl⟩
  · -- Case n = 0
    have hn0 : n = 0 := by omega
    haveI : Subsingleton (E n) := by
      rw [hn0]
      infer_instance
    have h_all_eq : ∀ (a b : E n), a = b := fun a b => Subsingleton.elim a b
    have hz_eq : z = hK.outerJohnEllipsoidCenter := h_all_eq z _
    have hK_nonempty : K.Nonempty := hK.2.2.mono interior_subset
    rcases hK_nonempty with ⟨x, hx⟩
    have hz_in_K : z ∈ K := by
      have h : z = x := h_all_eq z x
      rw [h]
      exact hx
    have hsqrt_zero : (√(n : ℝ))⁻¹ = 0 := by
      rw [hn0]
      norm_num
    have h_image : AffineMap.homothety z (√(n : ℝ))⁻¹ '' hK.outerJohnEllipsoid ⊆ K := by
      rw [hsqrt_zero]
      intro y hy
      rcases hy with ⟨w, _, rfl⟩
      simpa [AffineMap.homothety_apply] using hz_in_K
    exact ⟨hz_eq, h_image⟩

end JohnEllipsoid.IsConvexBody

open JohnEllipsoid.IsConvexBody
