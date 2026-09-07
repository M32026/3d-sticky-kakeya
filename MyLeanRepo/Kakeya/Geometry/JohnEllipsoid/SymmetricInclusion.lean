/-
# Symmetric 1/√n inclusion theorem

If K is a centrally symmetric convex body and ellipsoid c A is an outer John ellipsoid
with center of symmetry z = c, then the 1/√n homothety of the ellipsoid about z is
contained in K.

## Proof outline

1. Normalize: let K' := A⁻¹ '' ((-z) +ᵥ K). Then K' ⊆ B(0,1), K' is symmetric about 0,
   convex, closed, nonempty.
2. B(0,1) is minimal-volume for K': if K' ⊆ ellipsoid 0 A', then K ⊆ ellipsoid z (A'.trans A),
   so by minimality for K, det comparison gives 1 ≤ |det A'|, hence volume(B) ≤ volume(ellipsoid 0 A').
3. If there exists x ∉ K' with ‖x‖ ≤ 1/√n, symmetric_separation_norm_bound gives w with
   |⟨y,w⟩| ≤ 1 on K' and ‖w‖² > n.
4. deformation_contradiction gives False from such w and minimality.
5. Hence (1/√n) • B ⊆ K'.
6. Mapping back: z + A '' ((1/√n) • B) ⊆ K, which is the desired homothety image.

## Whiteprint node
symmetric_inclusion
-/

import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Basic
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.ConvexityUtils
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.DeformationMain
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.VolumeUtils
import Mathlib.Tactic

noncomputable section

open MeasureTheory
open scoped Pointwise Real

namespace JohnEllipsoid

variable {n : ℕ}

/-- Symmetric inclusion: if K is centrally symmetric about z=c and ellipsoid c A is an
    outer John ellipsoid, then the 1/√n homothety of the ellipsoid about z is contained in K. -/
lemma symmetric_inclusion (hn : 0 < n) {K : Set (E n)} {z c : E n} {A : E n ≃ₗ[ℝ] E n}
    (hK : IsConvexBody K) (hz : ∀ x, x ∈ K → z + (z - x) ∈ K)
    (hJ : IsOuterJohnEllipsoid K c A) (hzc : z = c) :
    AffineMap.homothety z (Real.sqrt (n : ℝ))⁻¹ '' ellipsoid c A ⊆ K := by
  let B := Metric.closedBall (0 : E n) 1
  let K' := A.symm '' ((-z) +ᵥ K)

  -- K' ⊆ B
  have hK'_sub : K' ⊆ B := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases hx with ⟨k, hk, rfl⟩
    have h2 : k ∈ ellipsoid c A := hJ.1 hk
    rcases h2 with ⟨s, hs, h_eq⟩
    rcases hs with ⟨a, ha, rfl⟩
    have h3 : (-z) + k = A a := by
      have h41 : c +ᵥ A a = k := by simpa [vadd_eq_add] using h_eq
      have h4 : k = c +ᵥ A a := h41.symm
      rw [h4, hzc]
      <;> simp [vadd_eq_add] <;> abel
    have h5 : A.symm ((-z) + k) = a := by
      rw [h3]
      exact A.symm_apply_apply a
    have h6 : A.symm ((-z) +ᵥ k) = a := by
      have h7 : (-z) +ᵥ k = (-z) + k := by simp [vadd_eq_add]
      rw [h7]
      exact h5
    rw [h6]
    exact ha

  -- K' is symmetric about 0
  have hK'_sym : ∀ y ∈ K', -y ∈ K' := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases hx with ⟨k, hk, rfl⟩
    let k' : E n := z + (z - k)
    have hk' : k' ∈ K := hz k hk
    have h_eq1 : (-z) + k' = -((-z) + k) := by
      simp [k', vadd_eq_add] <;> abel
    have h_goal : A.symm ((-z) + k') = -A.symm ((-z) + k) := by
      have h_neg : A.symm (-((-z) + k)) = -A.symm ((-z) + k) := A.symm.map_neg _
      rw [h_eq1]
      exact h_neg
    exact ⟨(-z) + k', ⟨k', hk', by simp [vadd_eq_add]⟩, h_goal⟩

  -- K' is convex
  have hK'_conv : Convex ℝ K' := by
    have h1 : Convex ℝ ((-z) +ᵥ K) := hK.1.vadd (-z)
    exact h1.linear_image A.symm.toLinearMap

  -- K' is closed
  have hK'_closed : IsClosed K' := by
    have h1 : IsCompact ((-z) +ᵥ K) := hK.2.1.vadd (-z)
    have h2 : IsCompact K' := h1.image A.symm.toLinearMap.continuous_of_finiteDimensional
    exact h2.isClosed

  -- K' is nonempty
  have hK'_nonempty : K'.Nonempty := by
    have h1 : (interior K).Nonempty := hK.2.2
    have h2 : K.Nonempty := h1.mono interior_subset
    have h3 : ((-z) +ᵥ K).Nonempty := h2.image _
    exact h3.image _

  -- B is minimal-volume for K'
  let A_comp (A' : E n ≃ₗ[ℝ] E n) : E n ≃ₗ[ℝ] E n := A'.trans A

  have h_min : ∀ (A' : E n ≃ₗ[ℝ] E n), K' ⊆ ellipsoid 0 A' →
      volume (ellipsoid 0 (1 : E n ≃ₗ[ℝ] E n)) ≤ volume (ellipsoid 0 A') := by
    intro A' hsub
    have h3 : K ⊆ ellipsoid c (A_comp A') := by
      intro k hk
      have h4 : A.symm ((-z) + k) ∈ K' := Set.mem_image_of_mem _ ⟨k, hk, by simp [vadd_eq_add]⟩
      have h5 : A.symm ((-z) + k) ∈ ellipsoid 0 A' := hsub h4
      rcases h5 with ⟨s, hs, h_eq5⟩
      rcases hs with ⟨b, hb, rfl⟩
      have h_eq6 : A' b = A.symm ((-z) + k) := by simpa [vadd_eq_add] using h_eq5
      have h6 : A (A' b) = (-z) + k := by
        have h7 : A (A.symm ((-z) + k)) = (-z) + k := A.apply_symm_apply ((-z) + k)
        have h8 : A (A' b) = A (A.symm ((-z) + k)) := by rw [h_eq6]
        rw [h8, h7]
      have h9 : (A_comp A') b = A (A' b) := by rfl
      refine ⟨(A_comp A') b, Set.mem_image_of_mem _ hb, ?_⟩
      have h10 : c +ᵥ (A_comp A') b = k := by
        have h11 : c +ᵥ (A_comp A') b = c + A (A' b) := by
          simp [vadd_eq_add, h9] <;> rfl
        rw [h11, h6, hzc] <;> simp [vadd_eq_add] <;> abel
      exact h10
    have h4 : volume (ellipsoid c A) ≤ volume (ellipsoid c (A_comp A')) := hJ.2 c (A_comp A') h3
    have h5 : |LinearMap.det (A : E n →ₗ[ℝ] E n)| ≤ |LinearMap.det ((A_comp A') : E n →ₗ[ℝ] E n)| :=
      (volume_ellipsoid_le_iff c A c (A_comp A')).mp h4
    have h6 : LinearMap.det ((A_comp A') : E n →ₗ[ℝ] E n) =
        LinearMap.det (A : E n →ₗ[ℝ] E n) * LinearMap.det (A' : E n →ₗ[ℝ] E n) := by
      have h_det : LinearMap.det ((A_comp A') : E n →ₗ[ℝ] E n) =
          LinearMap.det ((A : E n →ₗ[ℝ] E n).comp (A' : E n →ₗ[ℝ] E n)) := by rfl
      rw [h_det, LinearMap.det_comp]
    have h7 : |LinearMap.det ((A_comp A') : E n →ₗ[ℝ] E n)| =
        |LinearMap.det (A : E n →ₗ[ℝ] E n)| * |LinearMap.det (A' : E n →ₗ[ℝ] E n)| := by
      rw [h6, abs_mul]
    rw [h7] at h5
    have hdet_pos : 0 < |LinearMap.det (A : E n →ₗ[ℝ] E n)| := by
      have h : IsUnit (LinearMap.det (A : E n →ₗ[ℝ] E n)) :=
        LinearEquiv.isUnit_det' A
      exact abs_pos.mpr h.ne_zero
    have h8 : (1 : ℝ) ≤ |LinearMap.det (A' : E n →ₗ[ℝ] E n)| := by nlinarith
    have h9 : |LinearMap.det (1 : E n →ₗ[ℝ] E n)| ≤ |LinearMap.det (A' : E n →ₗ[ℝ] E n)| := by
      simpa using h8
    exact (volume_ellipsoid_le_iff (0 : E n) (1 : E n ≃ₗ[ℝ] E n) (0 : E n) A').mpr h9

  -- (1/√n) • B ⊆ K'
  have h_main : (Real.sqrt (n : ℝ))⁻¹ • B ⊆ K' := by
    intro x hx
    by_contra hnx
    have hx_norm : ‖x‖ ≤ (Real.sqrt (n : ℝ))⁻¹ := by
      rcases hx with ⟨b, hb, rfl⟩
      have hbn : ‖b‖ ≤ 1 := by simpa [B, Metric.mem_closedBall] using hb
      have h : ‖(Real.sqrt (n : ℝ))⁻¹ • b‖ = ‖(Real.sqrt (n : ℝ))⁻¹‖ * ‖b‖ := by
        rw [norm_smul]
      rw [h]
      have hpos : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ := by positivity
      have hnorm : ‖(Real.sqrt (n : ℝ))⁻¹‖ = (Real.sqrt (n : ℝ))⁻¹ := by
        simpa [norm_norm, abs_of_nonneg hpos] using rfl
      rw [hnorm]
      nlinarith
    have h_sep : ∃ (w : E n), (∀ y ∈ K', |inner ℝ w y| ≤ 1) ∧ (n : ℝ) < ‖w‖^2 :=
      symmetric_separation_norm_bound hn hK'_conv hK'_closed hK'_sym hK'_nonempty hnx hx_norm
    rcases h_sep with ⟨w, hw_bound, hw_norm2⟩
    have hw_bound' : ∀ x ∈ K', |inner ℝ x w| ≤ 1 := by
      intro x hx
      have h : inner ℝ x w = inner ℝ w x := real_inner_comm w x
      rw [h]
      exact hw_bound x hx
    exact deformation_contradiction hn hK'_sub h_min hw_bound' hw_norm2

  -- Map back to K
  intro p hp
  rcases hp with ⟨w, hw_in, rfl⟩
  rcases hw_in with ⟨s, hs, h_eq1⟩
  rcases hs with ⟨b, hb, rfl⟩
  let y : E n := (Real.sqrt (n : ℝ))⁻¹ • b
  have hy_smul : y ∈ (Real.sqrt (n : ℝ))⁻¹ • B := ⟨b, hb, rfl⟩
  have hy_K' : y ∈ K' := h_main hy_smul
  rcases hy_K' with ⟨x', hx', h_eq2⟩
  rcases hx' with ⟨k, hk, rfl⟩
  have h9 : A.symm ((-z) + k) = y := h_eq2
  have h10 : A y = (-z) + k := by
    have h11 : A (A.symm ((-z) + k)) = (-z) + k := A.apply_symm_apply ((-z) + k)
    rw [h9] at h11
    exact h11
  have h12 : k = z + A y := by
    have h13 : (-z) + k = A y := h10.symm
    have h14 : k = z + ((-z) + k) := by simp [vadd_eq_add] <;> abel
    rw [h14, h13] <;> abel
  have h15 : w = c +ᵥ A b := by
    have h16 : c +ᵥ A b = w := by simpa [vadd_eq_add] using h_eq1
    exact h16.symm
  have h17 : AffineMap.homothety z (Real.sqrt (n : ℝ))⁻¹ w = k := by
    rw [h15]
    have h18 : AffineMap.homothety z (Real.sqrt (n : ℝ))⁻¹ (c +ᵥ A b) =
        z + (Real.sqrt (n : ℝ))⁻¹ • ((c +ᵥ A b) - z) := by
      simp [AffineMap.homothety_apply, vadd_eq_add] <;> abel
    rw [h18]
    have h19 : (c +ᵥ A b) - z = A b := by
      simp [vadd_eq_add, hzc] <;> abel
    rw [h19]
    have h20 : (Real.sqrt (n : ℝ))⁻¹ • (A b) = A y := by
      simp [y, A.map_smul] <;> rfl
    rw [h20]
    <;> exact h12.symm
  rw [h17]
  exact hk

end JohnEllipsoid
