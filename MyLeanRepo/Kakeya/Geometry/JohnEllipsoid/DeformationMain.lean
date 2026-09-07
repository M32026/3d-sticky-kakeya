import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.DeformationHelpers

open scoped MatrixOrder Pointwise
open MeasureTheory

namespace JohnEllipsoid

variable {n : ℕ}

/-- The full deformation contradiction: if K ⊆ B, B is minimal volume,
    and there exists w with |w·x|≤1 on K and ‖w‖² > n, then contradiction. -/
lemma deformation_contradiction (hn : 0 < n)
    {K : Set (E n)}
    (hK_sub : K ⊆ Metric.closedBall (0 : E n) 1)
    (h_min : ∀ (A' : E n ≃ₗ[ℝ] E n), K ⊆ ellipsoid 0 A' →
        volume (ellipsoid 0 (1 : E n ≃ₗ[ℝ] E n)) ≤ volume (ellipsoid 0 A'))
    {w : E n} (hw_bound : ∀ x ∈ K, |inner ℝ x w| ≤ 1)
    (hw_norm2 : (n : ℝ) < ‖w‖^2) :
    False := by
  let w' : Fin n → ℝ := fun i => w i
  set S : ℝ := ‖w‖^2 with hS
  have hS_norm2 : S = ∑ i : Fin n, w' i ^ 2 := by
    have h_norm : ‖w‖ = Real.sqrt (∑ i : Fin n, w' i ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      <;> congr
      <;> funext i
      <;> simp [w']
      <;> rfl
    have h3 : ‖w‖^2 = ∑ i : Fin n, w' i ^ 2 := by
      rw [h_norm]
      have h4 : 0 ≤ ∑ i : Fin n, w' i ^ 2 := by positivity
      rw [Real.sq_sqrt h4]
    rw [hS, h3]
  have hS_gt_n : (n : ℝ) < S := by rw [hS] <;> exact hw_norm2
  obtain ⟨t, ht_pos, ht_lt_one, h_det_gt_one⟩ := exists_t_det_gt_one hn hS_gt_n
  have ht1 : t ≠ 1 := by linarith
  have h1mt_pos : 0 < 1 - t := by linarith
  let M_mat : Matrix (Fin n) (Fin n) ℝ := (1 - t) • 1 + t • Matrix.vecMulVec w' w'
  have hI_pd : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef :=
    Matrix.PosDef.diagonal (fun i => by norm_num)
  have h1t_pd : ((1 - t) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
    Matrix.PosDef.smul hI_pd h1mt_pos
  have houter_psd : (Matrix.vecMulVec w' w').PosSemidef := by
    have h : (Matrix.vecMulVec w' (star w')).PosSemidef := Matrix.posSemidef_vecMulVec_self_star w'
    simpa [star] using h
  have htouter_psd : (t • Matrix.vecMulVec w' w').PosSemidef :=
    Matrix.PosSemidef.smul houter_psd (by linarith)
  have hM_posdef : M_mat.PosDef := Matrix.PosDef.add_posSemidef h1t_pd htouter_psd
  have hM_psd : M_mat.PosSemidef := hM_posdef.posSemidef
  have h_det_formula : M_mat.det = (1 - t)^(n - 1) * (1 + t * (S - 1)) := by
    rw [det_rank_one_update hn w' t ht1, hS_norm2] <;> rfl
  have h_det_gt_one' : 1 < M_mat.det := by
    rw [h_det_formula]; exact h_det_gt_one
  have h_det_pos : 0 < M_mat.det := by linarith
  let S_mat : Matrix (Fin n) (Fin n) ℝ := CFC.sqrt M_mat
  have hS_mat_sq : S_mat * S_mat = M_mat := CFC.sqrt_mul_sqrt_self M_mat
  have hS_mat_nonneg : 0 ≤ S_mat := CFC.sqrt_nonneg M_mat
  have hS_mat_psd : S_mat.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hS_mat_nonneg
  have hS_mat_det : S_mat.det = Real.sqrt M_mat.det := by
    have h := Matrix.PosSemidef.det_sqrt hM_psd
    simpa [S_mat] using h
  have hS_mat_det_pos : 0 < S_mat.det := by
    rw [hS_mat_det]; exact Real.sqrt_pos.mpr h_det_pos
  have hS_mat_det_gt_one : 1 < S_mat.det := by
    rw [hS_mat_det]
    have h2 : Real.sqrt 1 < Real.sqrt M_mat.det := Real.sqrt_lt_sqrt (by norm_num) h_det_gt_one'
    simpa using h2
  have hS_mat_symm : S_mat.IsHermitian := hS_mat_psd.isHermitian
  let M_lin : E n →ₗ[ℝ] E n := Matrix.toEuclideanLin M_mat
  let S_lin : E n →ₗ[ℝ] E n := Matrix.toEuclideanLin S_mat
  let A_mat : Matrix (Fin n) (Fin n) ℝ := S_mat⁻¹
  let A_lin : E n →ₗ[ℝ] E n := Matrix.toEuclideanLin A_mat
  have hS_lin_sq : S_lin.comp S_lin = M_lin := by
    have h : Matrix.toEuclideanLin (S_mat * S_mat) = S_lin.comp S_lin := by
      exact Matrix.toLpLin_mul 2 2 2 S_mat S_mat
    rw [hS_mat_sq] at h
    exact h.symm
  have hS_mat_unit : IsUnit S_mat.det := IsUnit.mk0 S_mat.det hS_mat_det_pos.ne'
  have hSA : S_lin.comp A_lin = .id := by
    have h : S_mat * A_mat = 1 := Matrix.mul_nonsing_inv (A := S_mat) hS_mat_unit
    have h2 : Matrix.toEuclideanLin (S_mat * A_mat) = S_lin.comp A_lin := by
      exact Matrix.toLpLin_mul 2 2 2 S_mat A_mat
    rw [h] at h2
    have h3 : Matrix.toEuclideanLin (1 : Matrix (Fin n) (Fin n) ℝ) = (LinearMap.id : E n →ₗ[ℝ] E n) := by simp
    rw [h3] at h2
    exact h2.symm
  have hAS : A_lin.comp S_lin = .id := by
    have h : A_mat * S_mat = 1 := Matrix.nonsing_inv_mul (A := S_mat) hS_mat_unit
    have h2 : Matrix.toEuclideanLin (A_mat * S_mat) = A_lin.comp S_lin := by
      exact Matrix.toLpLin_mul 2 2 2 A_mat S_mat
    rw [h] at h2
    have h3 : Matrix.toEuclideanLin (1 : Matrix (Fin n) (Fin n) ℝ) = (LinearMap.id : E n →ₗ[ℝ] E n) := by simp
    rw [h3] at h2
    exact h2.symm
  let A_t : E n ≃ₗ[ℝ] E n := LinearEquiv.ofLinear A_lin S_lin hAS hSA
  have hS_lin_symm : S_lin.IsSymmetric := by
    have h_iff : (Matrix.toEuclideanLin S_mat).IsSymmetric ↔ S_mat.IsHermitian :=
      Matrix.isSymmetric_toLin_iff (EuclideanSpace.basisFun (Fin n) ℝ) (A := S_mat)
    exact h_iff.mpr hS_mat_symm
  have h_norm_sq : ∀ (x : E n), ‖S_lin x‖^2 = inner ℝ x (M_lin x) := by
    intro x
    have h1 : inner ℝ (S_lin x) (S_lin x) = ‖S_lin x‖^2 := real_inner_self_eq_norm_sq (S_lin x)
    have h2 : inner ℝ (S_lin x) (S_lin x) = inner ℝ x (S_lin (S_lin x)) := hS_lin_symm x (S_lin x)
    have h3 : S_lin (S_lin x) = M_lin x := by
      have h4 := congr_arg (fun (f : E n →ₗ[ℝ] E n) => f x) hS_lin_sq
      exact h4
    have h4 : ‖S_lin x‖^2 = inner ℝ (S_lin x) (S_lin x) := h1.symm
    rw [h4, h2, h3]
  have hinner_eq : ∀ (x : E n), inner ℝ x w = ∑ i : Fin n, x i * w' i := by
    intro x
    have h1 : inner ℝ x w = (WithLp.ofLp w) ⬝ᵥ star (WithLp.ofLp x) :=
      EuclideanSpace.inner_eq_star_dotProduct x w
    rw [h1]
    have h2 : star (WithLp.ofLp x) = WithLp.ofLp x := by funext i; simp
    rw [h2]
    have h3 : (WithLp.ofLp w) ⬝ᵥ (WithLp.ofLp x) = ∑ i : Fin n, (WithLp.ofLp w i) * (WithLp.ofLp x i) := by rfl
    rw [h3]
    apply Finset.sum_congr rfl
    intro i _; ring
  have hM_lin_apply : ∀ (x : E n), M_lin x = (1 - t) • x + t • (inner ℝ x w) • w := by
    intro x
    let x' : Fin n → ℝ := WithLp.ofLp x
    have hinner : inner ℝ x w = ∑ i : Fin n, x' i * w' i := hinner_eq x
    have hdot : w' ⬝ᵥ x' = inner ℝ x w := by
      have h : w' ⬝ᵥ x' = ∑ i : Fin n, w' i * x' i := by rfl
      rw [h, hinner]
      apply Finset.sum_congr rfl
      intro i _; ring
    have h_mat : M_mat.mulVec x' = (1 - t) • x' + t • (inner ℝ x w) • w' := by
      have h_sum : M_mat = (1 - t) • (1 : Matrix (Fin n) (Fin n) ℝ) + t • Matrix.vecMulVec w' w' := by rfl
      rw [h_sum]
      have h1 : ((1 - t) • (1 : Matrix (Fin n) (Fin n) ℝ) + t • Matrix.vecMulVec w' w').mulVec x' =
          ((1 - t) • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec x' + (t • Matrix.vecMulVec w' w').mulVec x' := by
        exact Matrix.add_mulVec ((1 - t) • (1 : Matrix (Fin n) (Fin n) ℝ)) (t • Matrix.vecMulVec w' w') x'
      rw [h1]
      have h2 : ((1 - t) • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec x' = (1 - t) • x' := by
        have h21 : ((1 - t) • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec x' = (1 - t) • (1 : Matrix (Fin n) (Fin n) ℝ).mulVec x' := by
          exact Matrix.smul_mulVec (1 - t) (1 : Matrix (Fin n) (Fin n) ℝ) x'
        rw [h21]
        have h22 : (1 : Matrix (Fin n) (Fin n) ℝ).mulVec x' = x' := by
          exact Matrix.one_mulVec x'
        rw [h22] <;> rfl
      have h3 : (t • Matrix.vecMulVec w' w').mulVec x' = t • (Matrix.vecMulVec w' w').mulVec x' := by
        exact Matrix.smul_mulVec t (Matrix.vecMulVec w' w') x'
      rw [h2, h3]
      have h4 : (Matrix.vecMulVec w' w').mulVec x' = (w' ⬝ᵥ x') • w' := by
        rw [Matrix.vecMulVec_mulVec w' w' x'] <;> simp
      rw [h4, hdot] <;> rfl
    have h4 : M_lin x = WithLp.toLp 2 (M_mat.mulVec x') := by
      simp [M_lin, Matrix.toEuclideanLin_apply] <;> rfl
    rw [h4, h_mat]
    have h_toLp : WithLp.toLp 2 ((1 - t) • x' + t • (inner ℝ x w) • w') =
        (1 - t) • x + t • (inner ℝ x w) • w := by
      ext i
      simp [WithLp.toLp, x', w', Pi.add_apply, Pi.smul_apply] <;> ring
    exact h_toLp
  have h_main_identity : ∀ (x : E n), ‖S_lin x‖^2 = (1 - t) * ‖x‖^2 + t * (inner ℝ x w)^2 := by
    intro x
    have h_eq : inner ℝ x (M_lin x) = (1 - t) * ‖x‖^2 + t * (inner ℝ x w)^2 := by
      rw [hM_lin_apply x]
      have h_add : inner ℝ x ((1 - t) • x + t • (inner ℝ x w) • w) =
          inner ℝ x ((1 - t) • x) + inner ℝ x (t • (inner ℝ x w) • w) := by
        exact inner_add_right _ _ _
      rw [h_add]
      have h_smul1 : inner ℝ x ((1 - t) • x) = (1 - t) * inner ℝ x x := by
        rw [inner_smul_right] <;> ring
      have h_smul2 : inner ℝ x (t • (inner ℝ x w) • w) = t * (inner ℝ x w) * inner ℝ x w := by
        rw [inner_smul_right, inner_smul_right] <;> ring
      rw [h_smul1, h_smul2]
      have h_self : inner ℝ x x = ‖x‖^2 := real_inner_self_eq_norm_sq x
      rw [h_self] <;> ring
    rw [h_norm_sq x, h_eq]
  have hK_sub_et : K ⊆ ellipsoid 0 A_t := by
    intro x hx
    have h1' : x ∈ Metric.closedBall (0 : E n) 1 := hK_sub hx
    have h1 : ‖x‖ ≤ 1 := by
      rw [Metric.mem_closedBall] at h1'
      simpa [dist_zero_right] using h1'
    have h2 : |inner ℝ x w| ≤ 1 := hw_bound x hx
    have h3 : ‖S_lin x‖ ≤ 1 := by
      have h4 : ‖S_lin x‖^2 ≤ 1 := by
        rw [h_main_identity x]
        have h5 : 0 ≤ ‖x‖ := by positivity
        have h6 : ‖x‖^2 ≤ 1 := by nlinarith
        have h7 : (inner ℝ x w)^2 ≤ 1 := by
          have h8 : |inner ℝ x w| ≤ 1 := h2
          rw [abs_le] at h8; nlinarith
        nlinarith
      have h9 : 0 ≤ ‖S_lin x‖ := by positivity
      nlinarith
    have h5 : S_lin x ∈ Metric.closedBall (0 : E n) 1 := by
      simpa [Metric.mem_closedBall] using h3
    have h6 : x ∈ A_t '' Metric.closedBall (0 : E n) 1 := by
      use S_lin x
      constructor
      · exact h5
      · have h7 : A_t (S_lin x) = x := by
          have h8 : A_lin (S_lin x) = x := by
            have h9 := congr_arg (fun (f : E n →ₗ[ℝ] E n) => f x) hAS
            exact h9
          exact h8
        exact h7
    have h8 : x ∈ ellipsoid 0 A_t := by
      simpa [ellipsoid] using h6
    exact h8
  have h_det_S_lin : LinearMap.det S_lin = S_mat.det := LinearMap.det_toLpLin 2 S_mat
  have h_det_A_lin : LinearMap.det A_lin = A_mat.det := LinearMap.det_toLpLin 2 A_mat
  have h_det_A_mat : A_mat.det = (S_mat.det)⁻¹ := by
    have h : A_mat.det = Ring.inverse S_mat.det := Matrix.det_nonsing_inv S_mat
    rw [h, Ring.inverse_eq_inv]
  have h_det_A_t : LinearMap.det (A_t : E n →ₗ[ℝ] E n) = (S_mat.det)⁻¹ := by
    simpa [A_t, h_det_A_lin, h_det_A_mat] using rfl
  have h_det_A_t_pos : 0 < LinearMap.det (A_t : E n →ₗ[ℝ] E n) := by rw [h_det_A_t]; positivity
  have h_det_A_t_lt_one : LinearMap.det (A_t : E n →ₗ[ℝ] E n) < 1 := by
    rw [h_det_A_t]
    have h1 : 1 < S_mat.det := hS_mat_det_gt_one
    have h_pos : 0 < S_mat.det := by linarith
    have h2 : (S_mat.det)⁻¹ < 1 := by
      have h3 : (S_mat.det)⁻¹ * S_mat.det = 1 := by
        field_simp [h_pos.ne'] <;> ring
      nlinarith
    exact h2
  have h_vol : volume (ellipsoid 0 A_t) =
      ENNReal.ofReal (|LinearMap.det (A_t : E n →ₗ[ℝ] E n)|) * volume (Metric.closedBall (0 : E n) 1) := by
    simpa [ellipsoid] using MeasureTheory.Measure.addHaar_image_linearMap volume (A_t : E n →ₗ[ℝ] E n) (Metric.closedBall (0 : E n) 1)
  have h_vol_B : volume (ellipsoid 0 (1 : E n ≃ₗ[ℝ] E n)) = volume (Metric.closedBall (0 : E n) 1) := by
    simp [ellipsoid] <;> rfl
  have h_abs_det : |LinearMap.det (A_t : E n →ₗ[ℝ] E n)| = LinearMap.det (A_t : E n →ₗ[ℝ] E n) := by
    rw [abs_of_pos h_det_A_t_pos]
  have hB_pos : 0 < volume (Metric.closedBall (0 : E n) 1) := by
    exact Metric.measure_closedBall_pos volume (0 : E n) (by norm_num)
  have hB_lt_top : volume (Metric.closedBall (0 : E n) 1) < ⊤ := by
    exact measure_closedBall_lt_top
  have h_vol_lt : volume (ellipsoid 0 A_t) < volume (ellipsoid 0 (1 : E n ≃ₗ[ℝ] E n)) := by
    rw [h_vol, h_vol_B, h_abs_det]
    have h : ENNReal.ofReal (LinearMap.det (A_t : E n →ₗ[ℝ] E n)) < 1 := by
      rw [ENNReal.ofReal_lt_one] <;> linarith
    have h_mul_lt : ENNReal.ofReal (LinearMap.det (A_t : E n →ₗ[ℝ] E n)) * volume (Metric.closedBall (0 : E n) 1) < volume (Metric.closedBall (0 : E n) 1) := by
      calc
        ENNReal.ofReal (LinearMap.det (A_t : E n →ₗ[ℝ] E n)) * volume (Metric.closedBall (0 : E n) 1)
          < 1 * volume (Metric.closedBall (0 : E n) 1) := by
            gcongr <;> exact hB_lt_top.ne
        _ = volume (Metric.closedBall (0 : E n) 1) := by simp
    simpa using h_mul_lt
  have h_le : volume (ellipsoid 0 (1 : E n ≃ₗ[ℝ] E n)) ≤ volume (ellipsoid 0 A_t) := h_min A_t hK_sub_et
  have h_contra : ¬ volume (ellipsoid 0 A_t) < volume (ellipsoid 0 (1 : E n ≃ₗ[ℝ] E n)) := by
    simpa [not_lt] using h_le
  exact h_contra h_vol_lt

end JohnEllipsoid
