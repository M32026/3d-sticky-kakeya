import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.ShapeSpace
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.VolumeUtils

/-!
# Bounded bands in ellipsoid shape space

An outer-radius bound controls the operator norm of an ellipsoid map. A
positive volume lower bound controls its inverse norm in dimension three.
-/

namespace Kakeya.CV

open MeasureTheory

/-- Bound for a 2×2 determinant in terms of entry bounds. -/
private lemma abs_det2_le {a b c d B : ℝ} (hB : 0 ≤ B)
    (ha : |a| ≤ B) (hb : |b| ≤ B) (hc : |c| ≤ B) (hd : |d| ≤ B) :
    |a * d - b * c| ≤ 2 * B^2 := by
  have h1 : |a * d - b * c| ≤ |a * d| + |b * c| :=
    abs_sub (a * d) (b * c)
  have h2 : |a * d| = |a| * |d| := by rw [abs_mul]
  have h3 : |b * c| = |b| * |c| := by rw [abs_mul]
  rw [h2, h3] at h1
  have h4 : |a| * |d| ≤ B * B := by gcongr
  have h5 : |b| * |c| ≤ B * B := by gcongr
  linarith

/-- Norm squared of a Euclidean vector equals the sum of squared components. -/
private lemma norm_sq_eq_sum {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = ∑ i : Fin n, (x i)^2 := by
  exact EuclideanSpace.real_norm_sq_eq x

/-- Bound for a negated 2×2 determinant in terms of entry bounds. -/
private lemma abs_neg_det2_le {a b c d B : ℝ} (hB : 0 ≤ B)
    (ha : |a| ≤ B) (hb : |b| ≤ B) (hc : |c| ≤ B) (hd : |d| ≤ B) :
    |-(a * d) + b * c| ≤ 2 * B^2 := by
  have h : |-(a * d) + b * c| = |a * d - b * c| := by
    have h' : -(a * d) + b * c = -(a * d - b * c) := by ring
    rw [h', abs_neg]
  rw [h]
  exact abs_det2_le hB ha hb hc hd

/-- If all entries of a 3×3 real matrix are bounded by `B ≥ 0`, then the
operator norm of the induced Euclidean linear map is at most `3 * B`. -/
private lemma opNorm_le_3_entry_bound {B : ℝ} (hB : 0 ≤ B)
    (N : Matrix (Fin 3) (Fin 3) ℝ)
    (hN : ∀ i j, |N i j| ≤ B) :
    ‖(Matrix.toEuclideanLin N).toContinuousLinearMap‖ ≤ 3 * B := by
  let f : Point 3 →L[ℝ] Point 3 :=
    (Matrix.toEuclideanLin N).toContinuousLinearMap
  have h_component : ∀ (x : Point 3) (i : Fin 3),
      (f x) i = ∑ j : Fin 3, N i j * x j := by
    intro x i
    have h : f x = Matrix.toEuclideanLin N x := rfl
    rw [h]
    have h2 := Matrix.toEuclideanLin_apply N x
    rw [h2]
    simp [Matrix.mulVec] <;> rfl
  have h_abs_sum : ∀ (x : Point 3),
      ∑ j : Fin 3, |x j| ≤ Real.sqrt 3 * ‖x‖ := by
    intro x
    have h1 :
        ∑ j : Fin 3, |x j| * (1 : ℝ) ≤
          Real.sqrt (∑ j : Fin 3, (|x j|)^2) *
            Real.sqrt (∑ j : Fin 3, (1 : ℝ)^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun j => |x j|) (fun _ => (1 : ℝ))
    have h2 : ∑ j : Fin 3, |x j| * (1 : ℝ) =
        ∑ j : Fin 3, |x j| := by simp
    have h3 : ∑ j : Fin 3, (|x j|)^2 =
        ∑ j : Fin 3, (x j)^2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [sq_abs]
    have h4 : ∑ j : Fin 3, (1 : ℝ)^2 = 3 := by
      simp [Finset.sum_const]
    have h5 : ‖x‖ ^ 2 = ∑ j : Fin 3, (x j)^2 :=
      norm_sq_eq_sum x
    rw [h2, h3, h4] at h1
    have h6 : Real.sqrt (∑ j : Fin 3, (x j)^2) = ‖x‖ := by
      rw [← h5, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)]
    rw [h6] at h1
    have h7 : ‖x‖ * Real.sqrt 3 = Real.sqrt 3 * ‖x‖ := by ring
    rw [h7] at h1
    exact h1
  have h_main : ∀ x : Point 3, ‖f x‖ ≤ 3 * B * ‖x‖ := by
    intro x
    have h1 : ∀ i : Fin 3,
        |(f x) i| ≤ Real.sqrt 3 * B * ‖x‖ := by
      intro i
      rw [h_component x i]
      have h2 :
          |∑ j : Fin 3, N i j * x j| ≤
            ∑ j : Fin 3, |N i j * x j| :=
        Finset.abs_sum_le_sum_abs (fun j => N i j * x j) Finset.univ
      have h3 :
          ∑ j : Fin 3, |N i j * x j| ≤
            ∑ j : Fin 3, |N i j| * |x j| := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
      have h41 :
          ∑ j : Fin 3, |N i j| * |x j| ≤
            ∑ j : Fin 3, B * |x j| := by
        apply Finset.sum_le_sum
        intro j _
        have h6 : |N i j| ≤ B := hN i j
        gcongr
      have h42 :
          ∑ j : Fin 3, B * |x j| =
            B * ∑ j : Fin 3, |x j| := by
        rw [Finset.mul_sum]
      have h4 :
          ∑ j : Fin 3, |N i j| * |x j| ≤
            B * ∑ j : Fin 3, |x j| := by
        rw [← h42]
        exact h41
      have h7 :
          B * ∑ j : Fin 3, |x j| ≤
            B * (Real.sqrt 3 * ‖x‖) := by
        gcongr
        exact h_abs_sum x
      calc
        |∑ j : Fin 3, N i j * x j|
            ≤ ∑ j : Fin 3, |N i j * x j| := h2
        _ ≤ ∑ j : Fin 3, |N i j| * |x j| := h3
        _ ≤ B * ∑ j : Fin 3, |x j| := h4
        _ ≤ B * (Real.sqrt 3 * ‖x‖) := h7
        _ = Real.sqrt 3 * B * ‖x‖ := by ring
    have h9 : ‖f x‖ ^ 2 = ∑ i : Fin 3, (f x) i ^ 2 :=
      norm_sq_eq_sum (f x)
    have h_bound_nonneg : 0 ≤ Real.sqrt 3 * B * ‖x‖ := by
      positivity
    have h10 :
        ∑ i : Fin 3, (f x) i ^ 2 ≤
          ∑ i : Fin 3, (Real.sqrt 3 * B * ‖x‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h11 : |(f x) i| ≤ Real.sqrt 3 * B * ‖x‖ := h1 i
      have h_abs : |Real.sqrt 3 * B * ‖x‖| =
          Real.sqrt 3 * B * ‖x‖ :=
        abs_of_nonneg h_bound_nonneg
      rw [sq_le_sq, h_abs]
      exact h11
    have h12 :
        ∑ i : Fin 3, (Real.sqrt 3 * B * ‖x‖) ^ 2 =
          9 * B^2 * ‖x‖^2 := by
      have h121 :
          ∑ i : Fin 3, (Real.sqrt 3 * B * ‖x‖) ^ 2 =
            3 * (Real.sqrt 3 * B * ‖x‖) ^ 2 := by
        simp [Finset.sum_const]
      rw [h121]
      have h123 : (Real.sqrt 3) ^ 2 = 3 :=
        Real.sq_sqrt (by norm_num)
      calc
        3 * (Real.sqrt 3 * B * ‖x‖) ^ 2
            = 3 * ((Real.sqrt 3) ^ 2 * B^2 * ‖x‖^2) := by ring
        _ = 9 * B^2 * ‖x‖^2 := by rw [h123] <;> ring
    have h14 : ‖f x‖ ^ 2 ≤ 9 * B^2 * ‖x‖^2 := by
      calc
        ‖f x‖ ^ 2 = ∑ i : Fin 3, (f x) i ^ 2 := h9
        _ ≤ ∑ i : Fin 3, (Real.sqrt 3 * B * ‖x‖) ^ 2 := h10
        _ = 9 * B^2 * ‖x‖^2 := h12
    have h17 : ‖f x‖ ^ 2 ≤ (3 * B * ‖x‖) ^ 2 := by
      simpa [show (3 * B * ‖x‖) ^ 2 = 9 * B^2 * ‖x‖^2 by ring]
        using h14
    have h18 : 0 ≤ 3 * B * ‖x‖ := by positivity
    have h19 : |‖f x‖| ≤ |3 * B * ‖x‖| := sq_le_sq.mp h17
    simpa [abs_of_nonneg (norm_nonneg (f x)), abs_of_nonneg h18] using h19
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) h_main

theorem bounded_ellipsoid_shape_band :
    BoundedEllipsoidShapeBandStatement := by
  intro R v hR hv
  let Vball := volume (Metric.closedBall (0 : Point 3) 1)
  have hVball_pos : 0 < Vball :=
    Metric.measure_closedBall_pos volume 0 (by norm_num)
  have hVball_ne_top : Vball ≠ ⊤ :=
    (isCompact_closedBall (0 : Point 3) 1).measure_ne_top
  let vball : ℝ := Vball.toReal
  have hvball_pos : 0 < vball := by
    exact ENNReal.toReal_pos hVball_pos.ne' hVball_ne_top
  set C : ℝ := max R (6 * R^2 * vball / v) with hC_def
  have hC_pos : 0 < C := by
    exact lt_of_lt_of_le hR (le_max_left _ _)
  refine ⟨C, hC_pos, fun A hsub hvol => ?_⟩
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let M : Matrix (Fin 3) (Fin 3) ℝ :=
    LinearMap.toMatrix b.toBasis b.toBasis A.toLinearMap
  have h_opNorm_A : ‖ShapeSpace.clm A‖ ≤ R := by
    have h_unit : ∀ x : Point 3, ‖x‖ ≤ 1 → ‖A x‖ ≤ R := by
      intro x hx
      have hxball : x ∈ Metric.closedBall (0 : Point 3) 1 := by
        simpa [Metric.mem_closedBall] using hx
      have hAx : A x ∈ JohnEllipsoid.ellipsoid 0 A := by
        refine ⟨A x, ⟨x, hxball, rfl⟩, by simp⟩
      simpa [Metric.mem_closedBall] using hsub hAx
    have h_all : ∀ x : Point 3, ‖A x‖ ≤ R * ‖x‖ := by
      intro x
      by_cases hx : x = 0
      · simp [hx]
      · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
        let u : Point 3 := (‖x‖⁻¹ : ℝ) • x
        have hu_norm : ‖u‖ = 1 := by
          simp [u, norm_smul, hpos.ne']
        have h_bound : ‖A u‖ ≤ R := h_unit u hu_norm.le
        have h_eq : A u = (‖x‖⁻¹ : ℝ) • A x := by
          simp [u, A.map_smul]
        rw [h_eq, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hpos)] at h_bound
        calc
          ‖A x‖ = ‖x‖ * (‖x‖⁻¹ * ‖A x‖) := by
            field_simp [hpos.ne']
          _ ≤ ‖x‖ * R := by gcongr
          _ = R * ‖x‖ := by ring
    exact ContinuousLinearMap.opNorm_le_bound _ hR.le h_all
  have h_det_eq : M.det = LinearMap.det A.toLinearMap :=
    LinearMap.det_toMatrix b.toBasis A.toLinearMap
  have h_vol_eq :
      volume (JohnEllipsoid.ellipsoid 0 A) =
        ENNReal.ofReal |M.det| * Vball := by
    rw [JohnEllipsoid.volume_ellipsoid_eq, h_det_eq]
  have hVball_eq : Vball = ENNReal.ofReal vball := by
    rw [ENNReal.ofReal_toReal hVball_ne_top]
  have h_det_lower : v ≤ |M.det| * vball := by
    rw [h_vol_eq, hVball_eq] at hvol
    have h :
        ENNReal.ofReal v ≤ ENNReal.ofReal (|M.det| * vball) := by
      simpa [ENNReal.ofReal_mul] using hvol
    exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mp h
  have h_det_ne_zero : M.det ≠ 0 := by
    rw [h_det_eq]
    exact (LinearEquiv.isUnit_det' A).ne_zero
  have h_det_pos : 0 < |M.det| := abs_pos.mpr h_det_ne_zero
  have h_det_isUnit : IsUnit M.det :=
    IsUnit.mk0 M.det h_det_ne_zero
  have h_entry : ∀ i j : Fin 3, |M i j| ≤ R := by
    intro i j
    have h1 : M i j = (A (b j)) i := by
      simp [M, LinearMap.toMatrix_apply, b, EuclideanSpace.basisFun_repr]
    rw [h1]
    have h2 : |(A (b j)) i| ≤ ‖A (b j)‖ := by
      have h_comp_sq :
          (A (b j)) i ^ 2 ≤ ∑ k : Fin 3, (A (b j)) k ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ i)
      have h_norm_sq :
          ‖A (b j)‖ ^ 2 = ∑ k : Fin 3, (A (b j)) k ^ 2 :=
        norm_sq_eq_sum (A (b j))
      have h' : (A (b j)) i ^ 2 ≤ ‖A (b j)‖ ^ 2 := by
        rwa [h_norm_sq]
      have h_abs : |(A (b j)) i| ≤ |‖A (b j)‖| :=
        sq_le_sq.mp h'
      simpa [abs_of_nonneg (norm_nonneg (A (b j)))] using h_abs
    have h3 : ‖A (b j)‖ ≤ ‖ShapeSpace.clm A‖ * ‖b j‖ :=
      ContinuousLinearMap.le_opNorm (ShapeSpace.clm A) (b j)
    have h4 : ‖b j‖ = 1 := b.orthonormal.1 j
    rw [h4, mul_one] at h3
    exact h2.trans (h3.trans h_opNorm_A)
  have hR_nonneg : 0 ≤ R := hR.le
  have h_adjugate :
      ∀ i j : Fin 3, |M.adjugate i j| ≤ 2 * R^2 := by
    rw [Matrix.adjugate_fin_three M]
    intro i j
    fin_cases i <;> fin_cases j
    · exact abs_det2_le hR_nonneg
        (h_entry 1 1) (h_entry 1 2) (h_entry 2 1) (h_entry 2 2)
    · exact abs_neg_det2_le hR_nonneg
        (h_entry 0 1) (h_entry 0 2) (h_entry 2 1) (h_entry 2 2)
    · exact abs_det2_le hR_nonneg
        (h_entry 0 1) (h_entry 0 2) (h_entry 1 1) (h_entry 1 2)
    · exact abs_neg_det2_le hR_nonneg
        (h_entry 1 0) (h_entry 1 2) (h_entry 2 0) (h_entry 2 2)
    · exact abs_det2_le hR_nonneg
        (h_entry 0 0) (h_entry 0 2) (h_entry 2 0) (h_entry 2 2)
    · exact abs_neg_det2_le hR_nonneg
        (h_entry 0 0) (h_entry 0 2) (h_entry 1 0) (h_entry 1 2)
    · exact abs_det2_le hR_nonneg
        (h_entry 1 0) (h_entry 1 1) (h_entry 2 0) (h_entry 2 1)
    · exact abs_neg_det2_le hR_nonneg
        (h_entry 0 0) (h_entry 0 1) (h_entry 2 0) (h_entry 2 1)
    · exact abs_det2_le hR_nonneg
        (h_entry 0 0) (h_entry 0 1) (h_entry 1 0) (h_entry 1 1)
  have h_inv_def : M⁻¹ = (M.det)⁻¹ • M.adjugate := by
    have h : M⁻¹ = Ring.inverse M.det • M.adjugate :=
      Matrix.inv_def M
    rw [h]
    have h2 : Ring.inverse M.det = (M.det)⁻¹ := by
      rw [Ring.inverse_eq_inv] <;> exact h_det_ne_zero
    rw [h2]
  have h_inv_entry :
      ∀ i j : Fin 3, |(M⁻¹) i j| ≤ 2 * R^2 / |M.det| := by
    intro i j
    rw [h_inv_def]
    have h :
        |((M.det)⁻¹ • M.adjugate) i j| =
          |M.det|⁻¹ * |M.adjugate i j| := by
      simp [smul_eq_mul, abs_mul, abs_inv]
    rw [h]
    have h6 :
        |M.det|⁻¹ * |M.adjugate i j| ≤
          |M.det|⁻¹ * (2 * R^2) := by
      gcongr
      exact h_adjugate i j
    have h7 :
        |M.det|⁻¹ * (2 * R^2) = 2 * R^2 / |M.det| := by
      field_simp [h_det_pos.ne'] <;> ring
    rw [h7] at h6
    exact h6
  let Minv_lin : Point 3 →ₗ[ℝ] Point 3 :=
    Matrix.toEuclideanLin M⁻¹
  let Minv_clm : Point 3 →L[ℝ] Point 3 :=
    Minv_lin.toContinuousLinearMap
  have hM_clm :
      (Matrix.toEuclideanLin M).toContinuousLinearMap =
        ShapeSpace.clm A := by
    have h_eq1 : (LinearMap.toMatrixOrthonormal b) A.toLinearMap = M := rfl
    have h_eq2 :
        (LinearMap.toMatrixOrthonormal b).symm M = A.toLinearMap := by
      rw [← h_eq1]
      exact (LinearMap.toMatrixOrthonormal b).symm_apply_apply A.toLinearMap
    exact ContinuousLinearMap.ext fun x =>
      congr_arg (fun f : Point 3 →ₗ[ℝ] Point 3 => f x) h_eq2
  have hM_inv_clm : Minv_clm = ShapeSpace.clm A.symm := by
    have h2 :
        Minv_clm * (Matrix.toEuclideanLin M).toContinuousLinearMap = 1 := by
      have h3 :
          Minv_lin * Matrix.toEuclideanLin M =
            Matrix.toEuclideanLin (M⁻¹ * M) :=
        (Matrix.toLpLin_mul 2 2 2 M⁻¹ M).symm
      have h4 : M⁻¹ * M = 1 :=
        Matrix.nonsing_inv_mul M h_det_isUnit
      have h5 :
          Minv_lin * Matrix.toEuclideanLin M =
            (1 : Point 3 →ₗ[ℝ] Point 3) := by
        rw [h3, h4] <;> simp <;> rfl
      exact ContinuousLinearMap.ext fun x =>
        congr_arg (fun f : Point 3 →ₗ[ℝ] Point 3 => f x) h5
    have h5 : ShapeSpace.clm A * ShapeSpace.clm A.symm = 1 := by
      exact ContinuousLinearMap.ext fun x => by
        simp [ShapeSpace.clm]
    have h_product : Minv_clm * ShapeSpace.clm A = 1 := by
      rw [← hM_clm]
      exact h2
    calc
      Minv_clm = Minv_clm * 1 := (mul_one Minv_clm).symm
      _ = Minv_clm * (ShapeSpace.clm A * ShapeSpace.clm A.symm) := by
        rw [h5]
      _ = (Minv_clm * ShapeSpace.clm A) * ShapeSpace.clm A.symm := by
        rw [mul_assoc]
      _ = ShapeSpace.clm A.symm := by rw [h_product, one_mul]
  have hB_inv_nonneg : 0 ≤ 2 * R^2 / |M.det| := by positivity
  have h_opNorm_inv :
      ‖ShapeSpace.clm A.symm‖ ≤ 3 * (2 * R^2 / |M.det|) := by
    rw [← hM_inv_clm]
    exact opNorm_le_3_entry_bound hB_inv_nonneg M⁻¹ h_inv_entry
  have h_final1 : ‖ShapeSpace.clm A‖ ≤ C :=
    h_opNorm_A.trans (le_max_left _ _)
  have h_bound :
      3 * (2 * R^2 / |M.det|) ≤ 6 * R^2 * vball / v := by
    have h15 : v / vball ≤ |M.det| := by
      rw [div_le_iff₀ hvball_pos]
      exact h_det_lower
    calc
      3 * (2 * R^2 / |M.det|) = 6 * R^2 / |M.det| := by ring
      _ ≤ 6 * R^2 / (v / vball) := by gcongr
      _ = 6 * R^2 * vball / v := by
        field_simp [hv.ne', hvball_pos.ne'] <;> ring
  have h_final2 : ‖ShapeSpace.clm A.symm‖ ≤ C := by
    exact h_opNorm_inv.trans <|
      h_bound.trans (le_max_right _ _)
  exact ⟨h_final2, h_final1⟩

end Kakeya.CV
