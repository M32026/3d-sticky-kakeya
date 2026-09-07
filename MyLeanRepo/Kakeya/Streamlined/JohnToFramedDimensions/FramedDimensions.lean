import MyLeanRepo.Kakeya.Streamlined.JohnToFramedDimensions.PrincipalAxes
import MyLeanRepo.Kakeya.Streamlined.JohnToFramedDimensions.BoxHelpers
import MyLeanRepo.Kakeya.Streamlined.JohnDimensions
import MyLeanRepo.Kakeya.Streamlined.Geometry

/-!
# Outer John ellipsoid to framed dimensions (closed module)

This module proves `john_to_framed_dimensions_closed`: every 3D convex body has
uniformly comparable framed dimensions, derived from its outer John ellipsoid.

Constant: `A = 3 * Real.sqrt 3`.
-/

noncomputable section

open JohnEllipsoid

namespace Kakeya.Streamlined

/-- Stronger version exposing the explicit constant A = 3√3 ≤ 10. -/
theorem john_to_framed_dimensions_with_bound :
    ∃ A : ℝ, 1 ≤ A ∧ A ≤ 10 ∧
      ∀ K : Body, JohnEllipsoid.IsConvexBody K.carrier →
        ∃ a b c : ℝ, ∃ frame : Point3 ≃ᵃⁱ[ℝ] Point3,
          K.HasDimensionsInFrame frame a b c A := by
  let A_const : ℝ := 3 * Real.sqrt 3
  have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hA_one : 1 ≤ A_const := by
    have h1 : 1 ≤ Real.sqrt 3 := by
      rw [Real.le_sqrt (by norm_num)] <;> norm_num
    linarith
  have hA_le : A_const ≤ 10 := by
    have h1 : Real.sqrt 3 ≤ 10 / 3 := by
      have h2 : (Real.sqrt 3) ^ 2 ≤ (10 / 3 : ℝ) ^ 2 := by
        rw [Real.sq_sqrt (by norm_num)] <;> norm_num
      nlinarith [Real.sqrt_nonneg 3]
    linarith
  refine' ⟨A_const, hA_one, hA_le, _⟩
  intro K hK
  set c : E 3 := hK.outerJohnEllipsoidCenter with hc_def
  set A_map : E 3 ≃ₗ[ℝ] E 3 := hK.outerJohnEllipsoidMap with hA_def
  have hE : IsOuterJohnEllipsoid K.carrier c A_map := hK.outerJohnEllipsoid_spec
  have hK_sub : K.carrier ⊆ ellipsoid c A_map := hE.1
  have hJohn : AffineMap.homothety c (3 : ℝ)⁻¹ '' ellipsoid c A_map ⊆ K.carrier :=
    hK.homothety_subset_outerJohnEllipsoid
  rcases principalAxesSvd A_map with ⟨σ, v, u, hσ_pos, hσ_anti, hAu⟩
  let u' : OrthonormalBasis (Fin 3) ℝ (E 3) := u.reindex Fin.revPerm
  let e_std : OrthonormalBasis (Fin 3) ℝ (E 3) := EuclideanSpace.basisFun (Fin 3) ℝ
  let W : E 3 ≃ₗᵢ[ℝ] E 3 := e_std.equiv u' (Equiv.refl (Fin 3))
  have hW_apply : ∀ (x : E 3), W x = ∑ i : Fin 3, x i • u' i := by
    intro x
    exact OrthonormalBasis.equiv_apply_euclideanSpace u' x
  have hW_basis : ∀ i, W (e_std i) = u' i := by
    intro i
    exact OrthonormalBasis.equiv_apply_basis e_std u' (Equiv.refl (Fin 3)) i
  let frame : E 3 ≃ᵃⁱ[ℝ] E 3 :=
    AffineIsometryEquiv.mk' (fun x : E 3 => c +ᵥ W x) W (0 : E 3)
      (fun x => by simp [vadd_comm] <;> abel)
  set a : ℝ := 2 * σ 2 / (3 * Real.sqrt 3) with ha_def
  set b : ℝ := 2 * σ 1 / (3 * Real.sqrt 3) with hb_def
  set c_dim : ℝ := 2 * σ 0 / (3 * Real.sqrt 3) with hc_dim_def
  have hσ2_pos : 0 < σ 2 := hσ_pos 2
  have hσ1_pos : 0 < σ 1 := hσ_pos 1
  have hσ0_pos : 0 < σ 0 := hσ_pos 0
  have ha_pos : 0 < a := by
    rw [ha_def]
    exact div_pos (mul_pos (by norm_num) hσ2_pos) (by positivity)
  have hσ2_le_σ1 : σ 2 ≤ σ 1 := hσ_anti (show (1 : Fin 3) ≤ (2 : Fin 3) from by decide)
  have hσ1_le_σ0 : σ 1 ≤ σ 0 := hσ_anti (show (0 : Fin 3) ≤ (1 : Fin 3) from by decide)
  have hab : a ≤ b := by
    rw [ha_def, hb_def]
    have h : 2 * σ 2 ≤ 2 * σ 1 := by linarith
    exact div_le_div_of_nonneg_right h (by positivity)
  have hbc : b ≤ c_dim := by
    rw [hb_def, hc_dim_def]
    have h : 2 * σ 1 ≤ 2 * σ 0 := by linarith
    exact div_le_div_of_nonneg_right h (by positivity)
  have hA_a : A_const * a = 2 * σ 2 := by
    rw [ha_def]
    have h : (3 * Real.sqrt 3) * (2 * σ 2 / (3 * Real.sqrt 3)) = 2 * σ 2 := by
      field_simp [hsqrt3_pos.ne'] <;> ring
    exact h
  have hA_b : A_const * b = 2 * σ 1 := by
    rw [hb_def]
    have h : (3 * Real.sqrt 3) * (2 * σ 1 / (3 * Real.sqrt 3)) = 2 * σ 1 := by
      field_simp [hsqrt3_pos.ne'] <;> ring
    exact h
  have hA_c : A_const * c_dim = 2 * σ 0 := by
    rw [hc_dim_def]
    have h : (3 * Real.sqrt 3) * (2 * σ 0 / (3 * Real.sqrt 3)) = 2 * σ 0 := by
      field_simp [hsqrt3_pos.ne'] <;> ring
    exact h
  have h_smul_div : ∀ (x : ℝ) {y : ℝ}, 0 < y → ∀ (v : E 3), (x / y) • (y • v) = x • v := by
    intro x y hy v
    rw [smul_smul]
    have h : (x / y) * y = x := by
      field_simp [hy.ne'] <;> ring
    rw [h]
  have h_inner : frame '' axisBox a b c_dim ⊆ K.carrier := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    have hz0 : |z 0| ≤ σ 2 / (3 * Real.sqrt 3) := by
      have h : |z 0| ≤ a / 2 := hz.1
      have h2 : a / 2 = σ 2 / (3 * Real.sqrt 3) := by
        rw [ha_def] <;> field_simp [hsqrt3_pos.ne'] <;> ring
      rw [h2] at h
      exact h
    have hz1 : |z 1| ≤ σ 1 / (3 * Real.sqrt 3) := by
      have h : |z 1| ≤ b / 2 := hz.2.1
      have h2 : b / 2 = σ 1 / (3 * Real.sqrt 3) := by
        rw [hb_def] <;> field_simp [hsqrt3_pos.ne'] <;> ring
      rw [h2] at h
      exact h
    have hz2 : |z 2| ≤ σ 0 / (3 * Real.sqrt 3) := by
      have h : |z 2| ≤ c_dim / 2 := hz.2.2
      have h2 : c_dim / 2 = σ 0 / (3 * Real.sqrt 3) := by
        rw [hc_dim_def] <;> field_simp [hsqrt3_pos.ne'] <;> ring
      rw [h2] at h
      exact h
    let l : Fin 3 → ℝ := ![z 2 / σ 0, z 1 / σ 1, z 0 / σ 2]
    let w : E 3 := ∑ i : Fin 3, l i • v i
    have h_w_def : w = (z 2 / σ 0) • v 0 + (z 1 / σ 1) • v 1 + (z 0 / σ 2) • v 2 := by
      simp [w, l, Fin.sum_univ_succ] <;> abel
    have hAw : A_map w = W z := by
      have h1 : A_map w = z 2 • u 0 + z 1 • u 1 + z 0 • u 2 := by
        rw [h_w_def, map_add, map_add]
        rw [map_smul, map_smul, map_smul]
        rw [hAu 0, hAu 1, hAu 2]
        rw [h_smul_div (z 2) hσ0_pos (u 0), h_smul_div (z 1) hσ1_pos (u 1), h_smul_div (z 0) hσ2_pos (u 2)]
        <;> abel
      have hWz : W z = z 0 • u 2 + z 1 • u 1 + z 2 • u 0 := by
        rw [hW_apply]
        have h4 : ∑ i : Fin 3, z i • u' i = z 0 • u' 0 + z 1 • u' 1 + z 2 • u' 2 := by
          simp [Fin.sum_univ_succ] <;> abel
        rw [h4]
        have h5 : u' 0 = u 2 := by simp [u', OrthonormalBasis.reindex_apply] <;> rfl
        have h6 : u' 1 = u 1 := by simp [u', OrthonormalBasis.reindex_apply] <;> rfl
        have h7 : u' 2 = u 0 := by simp [u', OrthonormalBasis.reindex_apply] <;> rfl
        rw [h5, h6, h7] <;> abel
      rw [h1, hWz] <;> abel
    have hnorm2 : ‖w‖ ^ 2 ≤ 1 / 9 := by
      have h3 : ‖w‖ ^ 2 = (z 2 / σ 0)^2 + (z 1 / σ 1)^2 + (z 0 / σ 2)^2 := by
        rw [norm_of_orthonormal_combination (v := v) (l := l)]
        have h4 : ∑ i : Fin 3, (l i)^2 = (l 0)^2 + (l 1)^2 + (l 2)^2 := by
          simp [Fin.sum_univ_succ] <;> ring
        rw [h4]
        have h5 : l 0 = z 2 / σ 0 := by simp [l] <;> rfl
        have h6 : l 1 = z 1 / σ 1 := by simp [l] <;> rfl
        have h7 : l 2 = z 0 / σ 2 := by simp [l] <;> rfl
        rw [h5, h6, h7] <;> ring
      rw [h3]
      have h8 : (z 2 / σ 0)^2 ≤ 1 / 27 := div_sq_bound hσ0_pos hz2
      have h9 : (z 1 / σ 1)^2 ≤ 1 / 27 := div_sq_bound hσ1_pos hz1
      have h10 : (z 0 / σ 2)^2 ≤ 1 / 27 := div_sq_bound hσ2_pos hz0
      linarith
    have hnorm : ‖w‖ ≤ 1 / 3 := by
      nlinarith [norm_nonneg w]
    let x : E 3 := (3 : ℝ) • w
    have hx_norm : ‖x‖ ≤ 1 := by
      have h : ‖x‖ = 3 * ‖w‖ := by
        simp [x, norm_smul] <;> rw [abs_of_pos (show (0 : ℝ) < 3 by norm_num)] <;> ring
      rw [h]
      linarith
    have hx_in : x ∈ Metric.closedBall (0 : E 3) 1 := by
      simpa [Metric.mem_closedBall] using hx_norm
    have h_ellipsoid_point : c +ᵥ A_map x ∈ ellipsoid c A_map := by
      have h_goal : ∃ (a : E 3), a ∈ Metric.closedBall (0 : E 3) 1 ∧ c +ᵥ A_map a = c +ᵥ A_map x :=
        ⟨x, hx_in, by simp⟩
      simpa [ellipsoid, Set.mem_vadd_set, Set.mem_image] using h_goal
    have h_homothety : c +ᵥ A_map w ∈ AffineMap.homothety c (3 : ℝ)⁻¹ '' ellipsoid c A_map := by
      simp only [Set.mem_image]
      refine ⟨c +ᵥ A_map x, h_ellipsoid_point, ?_⟩
      have h_eq : AffineMap.homothety c (3 : ℝ)⁻¹ (c +ᵥ A_map x) = c +ᵥ A_map w := by
        simp [AffineMap.homothety_apply, x, hAw] <;> abel
      exact h_eq
    have h_frame_eq : frame z = c +ᵥ A_map w := by
      simp [frame, AffineIsometryEquiv.coe_mk', hAw] <;> abel
    rw [h_frame_eq]
    exact hJohn h_homothety
  have h_outer : K.carrier ⊆ frame '' axisBox (A_const * a) (A_const * b) (A_const * c_dim) := by
    intro y hy
    have h_y_in_ellipsoid : y ∈ ellipsoid c A_map := hK_sub hy
    have h_y_def : ∃ (x_pre : E 3), x_pre ∈ Metric.closedBall (0 : E 3) 1 ∧ y = c +ᵥ A_map x_pre := by
      have h : ∃ (a : E 3), a ∈ Metric.closedBall (0 : E 3) 1 ∧ c +ᵥ A_map a = y := by
        simpa [ellipsoid, Set.mem_vadd_set, Set.mem_image] using h_y_in_ellipsoid
      rcases h with ⟨a, ha, h_eq⟩
      exact ⟨a, ha, h_eq.symm⟩
    rcases h_y_def with ⟨x_pre, hx_pre, rfl⟩
    have hx_norm : ‖x_pre‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hx_pre
    let z : E 3 := W.symm (A_map x_pre)
    have h_frame_z : frame z = c +ᵥ A_map x_pre := by
      simp [frame, AffineIsometryEquiv.coe_mk', z] <;> rfl
    have h_inner_eval : ∀ (y : E 3) (j : Fin 3), inner ℝ (e_std j) y = y j := by
      intro y j
      simp [e_std, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left] <;> rfl
    have h4 : A_map x_pre = ∑ j : Fin 3, (v.repr x_pre j * σ j) • u j := by
      have h5 : x_pre = ∑ j : Fin 3, v.repr x_pre j • v j := (v.sum_repr x_pre).symm
      have h6 : A_map x_pre = A_map (∑ j : Fin 3, v.repr x_pre j • v j) := by
        exact congr_arg (fun x : E 3 => A_map x) h5
      rw [h6, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      have h7 : A_map (v.repr x_pre j • v j) = (v.repr x_pre j * σ j) • u j := by
        rw [A_map.map_smul, hAu j]
        <;> exact smul_smul ((v.repr x_pre).ofLp j) (σ j) (u j)
      exact h7
    have h_coord : ∀ i : Fin 3, z i = v.repr x_pre (Fin.revPerm i) * σ (Fin.revPerm i) := by
      intro i
      have h1 : z i = inner ℝ (e_std i) z := (h_inner_eval z i).symm
      rw [h1]
      have h2 : inner ℝ (e_std i) z = inner ℝ (W (e_std i)) (A_map x_pre) :=
        Eq.symm (LinearIsometryEquiv.inner_map_eq_flip W (e_std i) (A_map x_pre))
      rw [h2, hW_basis]
      have h3 : u' i = u (Fin.revPerm i) := by
        simp [u', OrthonormalBasis.reindex_apply] <;> rfl
      rw [h3]
      have h_real_symm : inner ℝ (u (Fin.revPerm i)) (A_map x_pre) = inner ℝ (A_map x_pre) (u (Fin.revPerm i)) := by
        exact real_inner_comm (A_map x_pre) (u (Fin.revPerm i))
      rw [h_real_symm]
      have h_sum : inner ℝ (A_map x_pre) (u (Fin.revPerm i)) = v.repr x_pre (Fin.revPerm i) * σ (Fin.revPerm i) := by
        rw [h4]
        have h_orth : Orthonormal ℝ u := u.orthonormal
        have h := Orthonormal.inner_left_sum h_orth (fun j : Fin 3 => v.repr x_pre j * σ j) (Finset.mem_univ (Fin.revPerm i))
        simpa [starRingEnd] using h
      exact h_sum
    have h_bound : ∀ i : Fin 3, |z i| ≤ σ (Fin.revPerm i) := by
      intro i
      rw [h_coord i]
      have h5 : |v.repr x_pre (Fin.revPerm i)| ≤ ‖x_pre‖ := by
        have h6 : v.repr x_pre (Fin.revPerm i) = inner ℝ (v (Fin.revPerm i)) x_pre :=
          OrthonormalBasis.repr_apply_apply v x_pre (Fin.revPerm i)
        rw [h6]
        have h7 : |inner ℝ (v (Fin.revPerm i)) x_pre| ≤ ‖v (Fin.revPerm i)‖ * ‖x_pre‖ := abs_real_inner_le_norm _ _
        have h8 : ‖v (Fin.revPerm i)‖ = 1 := OrthonormalBasis.norm_eq_one v (Fin.revPerm i)
        rw [h8] at h7
        <;> simpa using h7
      have h7 : |v.repr x_pre (Fin.revPerm i) * σ (Fin.revPerm i)| = |v.repr x_pre (Fin.revPerm i)| * σ (Fin.revPerm i) := by
        rw [abs_mul, abs_of_pos (hσ_pos (Fin.revPerm i))]
      rw [h7]
      have h8 : |v.repr x_pre (Fin.revPerm i)| ≤ 1 := by linarith [hx_norm]
      have h9 : |v.repr x_pre (Fin.revPerm i)| * σ (Fin.revPerm i) ≤ σ (Fin.revPerm i) := by
        have h10 : 0 ≤ σ (Fin.revPerm i) := (hσ_pos (Fin.revPerm i)).le
        exact mul_le_of_le_one_left h10 h8
      exact h9
    have h_z_in_box : z ∈ axisBox (2 * σ 2) (2 * σ 1) (2 * σ 0) := by
      simp only [axisBox, Set.mem_setOf_eq]
      have h0 : |z 0| ≤ σ 2 := by simpa using h_bound 0
      have h1 : |z 1| ≤ σ 1 := by simpa using h_bound 1
      have h2 : |z 2| ≤ σ 0 := by simpa using h_bound 2
      exact ⟨by linarith, by linarith, by linarith⟩
    have h_final : z ∈ axisBox (A_const * a) (A_const * b) (A_const * c_dim) := by
      rw [hA_a, hA_b, hA_c]
      exact h_z_in_box
    exact ⟨z, h_final, h_frame_z⟩
  exact ⟨a, b, c_dim, frame, ⟨ha_pos, hab, hbc, hA_one, h_inner, h_outer⟩⟩

theorem john_to_framed_dimensions_closed :
    JohnToFramedDimensionsStatement := by
  rcases john_to_framed_dimensions_with_bound with ⟨A, hA_one, hA_le, h⟩
  exact ⟨A, hA_one, h⟩

end Kakeya.Streamlined
