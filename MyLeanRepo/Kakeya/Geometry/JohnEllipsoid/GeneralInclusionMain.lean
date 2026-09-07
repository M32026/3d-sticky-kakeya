import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.GeneralInclusion
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Centering
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Existence
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.VolumeUtils
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.EllipsoidProps
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.GeneralFritzJohn
import Mathlib.Tactic

noncomputable section

open MeasureTheory
open scoped Pointwise Real

namespace JohnEllipsoid
namespace IsConvexBody

variable {n : ℕ} {K : Set (E n)}

/-- The outer Löwner–John ellipsoid theorem: `(1 / n) • (L - c) + c ⊆ K ⊆ L`.
Proof via augmented Fritz John conditions. -/
theorem homothety_subset_outerJohnEllipsoid_main (hK : IsConvexBody K) :
    AffineMap.homothety (outerJohnEllipsoidCenter hK) (n : ℝ)⁻¹ '' outerJohnEllipsoid hK ⊆ K := by
  by_cases hn : 0 < n
  · -- Case n > 0
    set c0 : E n := outerJohnEllipsoidCenter hK with hc0_def
    set A0 : E n ≃ₗ[ℝ] E n := outerJohnEllipsoidMap hK with hA0_def
    have hE0 : IsOuterJohnEllipsoid K c0 A0 := outerJohnEllipsoid_spec hK
    have hK_sub : K ⊆ ellipsoid c0 A0 := hE0.1
    have h_min_K : ∀ (c' : E n) (A' : E n ≃ₗ[ℝ] E n),
        K ⊆ ellipsoid c' A' → volume (ellipsoid c0 A0) ≤ volume (ellipsoid c' A') := hE0.2

    -- Normalize: K' = A0.symm '' ((-c0) +ᵥ K)
    let K' : Set (E n) := A0.symm '' ((-c0) +ᵥ K)

    -- Step 1: K' ⊆ B(0,1)
    have hK'_sub : K' ⊆ Metric.closedBall (0 : E n) 1 := by
      intro y hy
      rcases hy with ⟨x', hx', rfl⟩
      rcases hx' with ⟨x, hx, rfl⟩
      have h1 : x ∈ ellipsoid c0 A0 := hK_sub hx
      have h2 : ‖A0.symm (x - c0)‖ ≤ 1 := (ellipsoid_mem_iff c0 A0 x).mp h1
      have h_comm : (-c0 : E n) +ᵥ x = x - c0 := by
        simp [vadd_eq_add] <;> abel
      rw [Metric.mem_closedBall, dist_zero_right]
      have h_goal : A0.symm (((-c0 : E n) +ᵥ x)) = A0.symm (x - c0) := by rw [h_comm]
      rw [h_goal]
      exact h2

    -- Step 2: K' is a convex body
    have hK'_conv : Convex ℝ K' := by
      have h1 : Convex ℝ K := hK.1
      have h2 : Convex ℝ ((-c0) +ᵥ K) := h1.vadd (-c0)
      exact h2.linear_image A0.symm.toLinearMap
    have hK'_compact : IsCompact K' := by
      have h1 : IsCompact K := hK.2.1
      have h2 : IsCompact ((-c0) +ᵥ K) := h1.vadd (-c0)
      have h3 : Continuous A0.symm := A0.symm.toLinearMap.continuous_of_finiteDimensional
      exact h2.image h3
    have hK'_interior : (interior K').Nonempty := by
      rcases hK.2.2 with ⟨x, hx⟩
      -- x ∈ interior K, so there exists ε > 0 with ball x ε ⊆ K
      rcases Metric.isOpen_iff.mp isOpen_interior x hx with ⟨ε, hε_pos, hball⟩
      let x' : E n := (-c0) +ᵥ x
      let y : E n := A0.symm x'
      -- The set A0.symm '' ((-c0) +ᵥ ball x ε) is open and contained in K'
      have h_contA : Continuous A0.symm := A0.symm.toLinearMap.continuous_of_finiteDimensional
      have h_contAinv : Continuous A0 := A0.toLinearMap.continuous_of_finiteDimensional
      let h_homeo : Homeomorph (E n) (E n) :=
        { toFun := A0.symm, invFun := A0,
          left_inv := A0.apply_symm_apply,
          right_inv := A0.symm_apply_apply,
          continuous_toFun := h_contA, continuous_invFun := h_contAinv }
      have h_open1 : IsOpen (Metric.ball x ε) := Metric.isOpen_ball
      have h_open2 : IsOpen ((-c0) +ᵥ Metric.ball x ε) := h_open1.vadd (-c0)
      have h_open3 : IsOpen (A0.symm '' ((-c0) +ᵥ Metric.ball x ε)) := h_homeo.isOpenMap _ h_open2
      have h_sub4 : A0.symm '' ((-c0) +ᵥ Metric.ball x ε) ⊆ K' := by
        intro z hz
        rcases hz with ⟨w, hw, rfl⟩
        rcases hw with ⟨v, hv, rfl⟩
        have h5 : v ∈ K := interior_subset (hball hv)
        exact ⟨(-c0) +ᵥ v, ⟨v, h5, rfl⟩, rfl⟩
      have h_y_in : y ∈ A0.symm '' ((-c0) +ᵥ Metric.ball x ε) := by
        refine ⟨x', ?_, rfl⟩
        exact ⟨x, Metric.mem_ball_self hε_pos, rfl⟩
      have h7 : A0.symm '' ((-c0) +ᵥ Metric.ball x ε) ⊆ interior K' :=
        h_open3.subset_interior_iff.mpr h_sub4
      have h6 : y ∈ interior K' := h7 h_y_in
      exact ⟨y, h6⟩
    let hK'_body : IsConvexBody K' := ⟨hK'_conv, hK'_compact, hK'_interior⟩

    -- Step 3: B(0,1) is minimal for K'
    have h_min' : ∀ (c' : E n) (A' : E n ≃ₗ[ℝ] E n),
        K' ⊆ ellipsoid c' A' →
        volume (ellipsoid (0 : E n) (1 : E n ≃ₗ[ℝ] E n)) ≤ volume (ellipsoid c' A') := by
      intro c' A' hK'_ellip
      have h1 : K ⊆ ellipsoid (c0 + A0 c') (A'.trans A0) := by
        intro x hx
        let z := A0.symm (x - c0)
        have hz_in_K' : z ∈ K' := by
          refine ⟨x - c0, ?_, rfl⟩
          refine ⟨x, hx, ?_⟩
          simp [vadd_eq_add] <;> abel
        have h2 : z ∈ ellipsoid c' A' := hK'_ellip hz_in_K'
        have h3 : ‖A'.symm (z - c')‖ ≤ 1 := (ellipsoid_mem_iff c' A' z).mp h2
        have h41 : A0.symm (x - (c0 + A0 c')) = z - c' := by
          have h : A0.symm (x - (c0 + A0 c')) = A0.symm (x - c0) - A0.symm (A0 c') := by
            rw [show x - (c0 + A0 c') = (x - c0) - A0 c' by abel, map_sub]
          rw [h]
          have h2 : A0.symm (A0 c') = c' := A0.symm_apply_apply c'
          rw [h2] <;> rfl
        have h_trans_symm : (A'.trans A0).symm = A0.symm.trans A'.symm := by
          ext y
          simp [LinearEquiv.trans_apply]
          <;> rfl
        have h4 : (A'.trans A0).symm (x - (c0 + A0 c')) = A'.symm (z - c') := by
          rw [h_trans_symm]
          have h42 : (A0.symm.trans A'.symm) (x - (c0 + A0 c')) = A'.symm (A0.symm (x - (c0 + A0 c'))) := by
            simp [LinearEquiv.trans_apply]
            <;> rfl
          rw [h42, h41]
        have h5 : ‖(A'.trans A0).symm (x - (c0 + A0 c'))‖ ≤ 1 := by
          rw [h4] <;> exact h3
        exact (ellipsoid_mem_iff (c0 + A0 c') (A'.trans A0) x).mpr h5
      have h_vol := h_min_K (c0 + A0 c') (A'.trans A0) h1
      rw [volume_ellipsoid_le_iff c0 A0 (c0 + A0 c') (A'.trans A0)] at h_vol
      have h_det : LinearMap.det ((A'.trans A0 : E n →ₗ[ℝ] E n)) =
          LinearMap.det (A0 : E n →ₗ[ℝ] E n) * LinearMap.det (A' : E n →ₗ[ℝ] E n) := by
        have h : LinearMap.det ((A'.trans A0 : E n →ₗ[ℝ] E n)) =
            LinearMap.det (A0 : E n →ₗ[ℝ] E n) * LinearMap.det (A' : E n →ₗ[ℝ] E n) := by
          simpa [LinearEquiv.trans_apply, mul_comm] using LinearMap.det_comp (A0 : E n →ₗ[ℝ] E n) (A' : E n →ₗ[ℝ] E n)
        exact h
      rw [h_det] at h_vol
      have h_det0_ne : LinearMap.det (A0 : E n →ₗ[ℝ] E n) ≠ 0 :=
        (LinearEquiv.isUnit_det' A0).ne_zero
      have h_abs : |LinearMap.det (A0 : E n →ₗ[ℝ] E n) * LinearMap.det (A' : E n →ₗ[ℝ] E n)| =
          |LinearMap.det (A0 : E n →ₗ[ℝ] E n)| * |LinearMap.det (A' : E n →ₗ[ℝ] E n)| := by
        rw [abs_mul]
      rw [h_abs] at h_vol
      have h_pos0 : 0 < |LinearMap.det (A0 : E n →ₗ[ℝ] E n)| := abs_pos.mpr h_det0_ne
      have h6 : (1 : ℝ) ≤ |LinearMap.det (A' : E n →ₗ[ℝ] E n)| := by nlinarith
      rw [volume_ellipsoid_le_iff (0 : E n) (1 : E n ≃ₗ[ℝ] E n) c' A']
      simpa using h6

    -- Step 4: Apply augmented Fritz John conditions
    rcases general_fritz_john_augmented hn hK'_body hK'_sub h_min' with
      ⟨m, u, c, hu_in_K_norm, hc_nonneg, hc_sum, h_sum_u, h_sum_tensor⟩
    have hu_in_K : ∀ i, u i ∈ K' := fun i => (hu_in_K_norm i).1
    have hu_norm : ∀ i, ‖u i‖ = 1 := fun i => (hu_in_K_norm i).2

    -- Step 5: Apply general inclusion lemma
    have h_incl : ((n : ℝ)⁻¹ • Metric.closedBall (0 : E n) 1) ⊆ K' :=
      general_inclusion_of_fritz_john hn hK'_conv u c hu_in_K hu_norm hc_nonneg hc_sum h_sum_u h_sum_tensor

    -- Step 6: Map back: c0 +ᵥ A0 '' ((1/n) • B) ⊆ K
    have h_A0_K' : A0 '' K' = (-c0) +ᵥ K := by
      ext y
      simp only [K', Set.mem_image, Set.mem_vadd]
      constructor
      · rintro ⟨z, ⟨x', ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
        refine ⟨x, hx, ?_⟩
        simp [A0.apply_symm_apply] <;> abel
      · rintro ⟨x, hx, rfl⟩
        refine ⟨A0.symm (x - c0), ⟨x - c0, ⟨x, hx, by simp [vadd_eq_add] <;> abel⟩, rfl⟩, ?_⟩
        simp [A0.apply_symm_apply] <;> abel
    have h_map_back : c0 +ᵥ A0 '' ((n : ℝ)⁻¹ • Metric.closedBall (0 : E n) 1) ⊆ K := by
      have h_sub2 : A0 '' ((n : ℝ)⁻¹ • Metric.closedBall (0 : E n) 1) ⊆ A0 '' K' := by
        intro z hz
        rcases hz with ⟨w, hw, rfl⟩
        exact ⟨w, h_incl hw, rfl⟩
      have h_sub3 : c0 +ᵥ A0 '' ((n : ℝ)⁻¹ • Metric.closedBall (0 : E n) 1) ⊆ c0 +ᵥ A0 '' K' := by
        intro y hy
        rcases hy with ⟨z, hz, rfl⟩
        exact ⟨z, h_sub2 hz, rfl⟩
      rw [h_A0_K'] at h_sub3
      have h_final : c0 +ᵥ ((-c0) +ᵥ K) = K := by
        ext z
        simp [vadd_eq_add] <;> abel
      rw [h_final] at h_sub3
      exact h_sub3

    -- Step 7: Show homothety image equals c0 +ᵥ A0 '' ((1/n) • B)
    have h_pos : 0 < (n : ℝ) := by exact_mod_cast hn
    have h_eq_hom : AffineMap.homothety c0 (n : ℝ)⁻¹ '' ellipsoid c0 A0 =
        c0 +ᵥ A0 '' ((n : ℝ)⁻¹ • Metric.closedBall (0 : E n) 1) := by
      ext y
      simp only [Set.mem_image, ellipsoid, Set.mem_vadd_set]
      constructor
      · rintro ⟨w, hw, rfl⟩
        rcases hw with ⟨z, hz, rfl⟩
        rcases hz with ⟨v, hv_in_ball, rfl⟩
        refine ⟨A0 ((n : ℝ)⁻¹ • v), ?_, ?_⟩
        · refine ⟨(n : ℝ)⁻¹ • v, ?_, rfl⟩
          exact ⟨v, hv_in_ball, rfl⟩
        · simp [AffineMap.homothety_apply, vadd_eq_add, smul_smul] <;> abel
      · rintro ⟨z, hz, rfl⟩
        rcases hz with ⟨w, hw_in_scaled, rfl⟩
        rcases hw_in_scaled with ⟨v, hv_in_ball, rfl⟩
        let w_ellipsoid : E n := c0 + A0 v
        have hw_ellipsoid_in : w_ellipsoid ∈ ellipsoid c0 A0 := by
          refine ⟨A0 v, ?_, by simp [w_ellipsoid, vadd_eq_add] <;> abel⟩
          exact ⟨v, hv_in_ball, rfl⟩
        refine ⟨w_ellipsoid, hw_ellipsoid_in, ?_⟩
        simp [w_ellipsoid, AffineMap.homothety_apply, vadd_eq_add, smul_smul] <;> abel
    have h_def : outerJohnEllipsoid hK = ellipsoid c0 A0 := by rfl
    rw [h_def]
    rw [h_eq_hom]
    exact h_map_back

  · -- Case n = 0
    have hn0 : n = 0 := by omega
    haveI : Subsingleton (E n) := by
      rw [hn0]
      infer_instance
    have h_all_eq : ∀ (a b : E n), a = b := fun a b => Subsingleton.elim a b
    let c0 : E n := outerJohnEllipsoidCenter hK
    have hK_nonempty : K.Nonempty := hK.2.2.mono interior_subset
    rcases hK_nonempty with ⟨x, hx⟩
    have hc0_in_K : c0 ∈ K := by
      have h : c0 = x := h_all_eq c0 x
      rw [h]
      exact hx
    have h_inv_zero : (n : ℝ)⁻¹ = 0 := by
      rw [hn0] <;> norm_num
    have h_image : AffineMap.homothety c0 (n : ℝ)⁻¹ '' outerJohnEllipsoid hK ⊆ K := by
      rw [h_inv_zero]
      intro y hy
      rcases hy with ⟨w, _, rfl⟩
      simpa [AffineMap.homothety_apply] using hc0_in_K
    exact h_image

end JohnEllipsoid.IsConvexBody
