import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.VisibilityDegreeBound.Helpers
import MyLeanRepo.Kakeya.CV.UnitSphereHausdorffArea

/-!
# Principal-axis mollified many-bisections

The coefficient-ball averaging bridge in Carbery--Valdimarsson Lemma 9.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal Real BigOperators

namespace Kakeya.CV

theorem principalAxes_mollified_many_bisections.{u} :
    PrincipalAxesMollifiedManyBisectionsStatement.{u} := by
  intro hMain hGeneric hSingular hCylinder
  rcases hMain with ⟨C_main, hC_main_pos, hMain_est⟩
  rcases hCylinder with ⟨C_cyl, hC_cyl_pos, hCyl_est⟩
  refine' ⟨C_main, hC_main_pos, _⟩
  intro k P U c ε x ι _ A η z b ℓ hU_meas hU hε hInt hη hη1 ℓ_pos hA hSubset hDisjoint hCut

  let B := Metric.ball x ε
  let p_y : CoefficientSpace P.dim → MvPolynomial (Fin 3) ℝ := parameterPolynomial P
  let LHS_ennreal : ENNReal :=
    (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal (η ^ 2 * ∏ i, ℓ i) *
      codimensionOneMeasure 3 (unitSphere 3)

  have h_sphere_eq : standardSurfaceArea3 (unitSphere 3) =
      (3 : ENNReal) * volume (unitBall 3) :=
    unitSphere_standardArea_eq_three_mul_volume
  have h1 : standardSurfaceArea3 (unitSphere 3) =
      ENNReal.ofReal (Real.pi / 4) * codimensionOneMeasure 3 (unitSphere 3) := by rfl
  have h_sphere_eq2 : ENNReal.ofReal (Real.pi / 4) * codimensionOneMeasure 3 (unitSphere 3) =
      (3 : ENNReal) * volume (unitBall 3) := by
    calc
      ENNReal.ofReal (Real.pi / 4) * codimensionOneMeasure 3 (unitSphere 3)
        = standardSurfaceArea3 (unitSphere 3) := h1.symm
      _ = (3 : ENNReal) * volume (unitBall 3) := h_sphere_eq
  have h_ball_lt_top : (3 : ENNReal) * volume (unitBall 3) < ⊤ := by
    apply ENNReal.mul_lt_top
    · norm_num
    · exact Metric.isBounded_closedBall.measure_lt_top
  have h3 : ENNReal.ofReal (Real.pi / 4) * codimensionOneMeasure 3 (unitSphere 3) < ⊤ := by
    rw [h_sphere_eq2] <;> exact h_ball_lt_top
  have h4 : ENNReal.ofReal (Real.pi / 4) ≠ 0 := by positivity
  have h_sphere_finite : codimensionOneMeasure 3 (unitSphere 3) < ⊤ := by
    have h6 := (ENNReal.mul_lt_top_iff).mp h3
    rcases h6 with (h6 | h6 | h6)
    · exact h6.2
    · exfalso; exact h4 h6
    · rw [h6] <;> simp

  have h_lhs_finite : LHS_ennreal ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · exact ENNReal.natCast_ne_top _
      · exact ENNReal.ofReal_lt_top.ne
    · exact h_sphere_finite.ne

  have h_reg_ball : ∀ᵐ y ∂(volume.restrict B),
      p_y y ≠ 0 ∧ Squarefree (p_y y) :=
    hGeneric k P x ε hε

  have h_sing_ball : ∀ᵐ y ∂(volume.restrict B),
      HasNegligibleSingularSet (p_y y) := by
    filter_upwards [h_reg_ball] with y hy
    exact hSingular (p_y y) hy.1 hy.2

  have hbnorm : ∀ i : Fin 3, ‖b i‖ = 1 := by
    intro i
    exact b.orthonormal.1 i

  have hU_tube : ∀ i : Fin 3, U ⊆ unitTube c (b i) := by
    intro i
    calc
      U ⊆ Metric.closedBall c 1 := hU
      _ ⊆ unitTube c (b i) := unitBall_subset_unitTube c (b i) (hbnorm i)

  have h_dsa_finite : ∀ᵐ y ∂(volume.restrict B),
      ∀ i : Fin 3, directionalSurfaceArea (b i) (p_y y)
        (polynomialZeroSet (p_y y) ∩ U) ≠ ⊤ := by
    filter_upwards [h_reg_ball, h_sing_ball] with y hreg hsing
    intro i
    have h_deg : (p_y y).totalDegree ≤ k := (P.equiv y).property
    have h_cyl : directionalSurfaceArea (b i) (p_y y)
        (polynomialZeroSet (p_y y) ∩ unitTube c (b i)) ≤
        (C_cyl : ℝ≥0∞) * (k : ℝ≥0∞) :=
      hCyl_est k (p_y y) c (b i) hreg.1 hsing h_deg (hbnorm i)
    have h_subset : polynomialZeroSet (p_y y) ∩ U ⊆
        polynomialZeroSet (p_y y) ∩ unitTube c (b i) :=
      Set.inter_subset_inter_right _ (hU_tube i)
    have h : directionalSurfaceArea (b i) (p_y y)
        (polynomialZeroSet (p_y y) ∩ U) ≤
        (C_cyl : ℝ≥0∞) * (k : ℝ≥0∞) :=
      (directionalSurfaceArea_mono (b i) (p_y y) h_subset).trans h_cyl
    have h_top : (C_cyl : ℝ≥0∞) * (k : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) (by simp)
    exact ne_top_of_le_ne_top h_top h

  have h_union_subset : (⋃ j : ι, scaledEllipsoid A η (z j)) ⊆ U := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
    exact hSubset j hj

  have hB_ae : ∀ᵐ y ∂(volume.restrict B), y ∈ B := by
    rw [ae_iff]
    have h_meas : MeasurableSet B := Metric.isOpen_ball.measurableSet
    have h : (volume.restrict B) Bᶜ = 0 := by
      rw [Measure.restrict_apply' h_meas]
      <;> simp
    have h' : Bᶜ = {y | y ∉ B} := by ext y; simp
    rw [h'] at h
    exact h

  have h_pointwise : ∀ᵐ y ∂(volume.restrict B),
      LHS_ennreal ≤ (C_main : ℝ≥0∞) * ∑ i : Fin 3,
        ENNReal.ofReal (ℓ i) * directionalSurfaceArea (b i) (p_y y)
          (polynomialZeroSet (p_y y) ∩ U) := by
    filter_upwards [h_reg_ball, h_sing_ball, hB_ae] with y hreg hsing hyB
    have h_main_y := hMain_est ι (p_y y) A η z b ℓ
      hreg.1 hsing hη hη1 ℓ_pos hA hDisjoint
      (fun j => hCut y hyB j)
    have h_mono : ∀ i : Fin 3,
        directionalSurfaceArea (b i) (p_y y)
          (polynomialZeroSet (p_y y) ∩ ⋃ j, scaledEllipsoid A η (z j)) ≤
        directionalSurfaceArea (b i) (p_y y)
          (polynomialZeroSet (p_y y) ∩ U) := by
      intro i
      apply directionalSurfaceArea_mono
      exact Set.inter_subset_inter_right _ h_union_subset
    have h_sum_mono : ∑ i : Fin 3, ENNReal.ofReal (ℓ i) * directionalSurfaceArea (b i) (p_y y)
          (polynomialZeroSet (p_y y) ∩ ⋃ j, scaledEllipsoid A η (z j)) ≤
        ∑ i : Fin 3, ENNReal.ofReal (ℓ i) * directionalSurfaceArea (b i) (p_y y)
          (polynomialZeroSet (p_y y) ∩ U) := by
      apply Finset.sum_le_sum
      intro i _
      have h5 : ENNReal.ofReal (ℓ i) * directionalSurfaceArea (b i) (p_y y)
            (polynomialZeroSet (p_y y) ∩ ⋃ j, scaledEllipsoid A η (z j)) ≤
          ENNReal.ofReal (ℓ i) * directionalSurfaceArea (b i) (p_y y)
            (polynomialZeroSet (p_y y) ∩ U) := by
        exact mul_le_mul_right (h_mono i) _
      exact h5
    calc
      LHS_ennreal ≤ (C_main : ℝ≥0∞) * ∑ i : Fin 3,
          ENNReal.ofReal (ℓ i) * directionalSurfaceArea (b i) (p_y y)
            (polynomialZeroSet (p_y y) ∩ ⋃ j, scaledEllipsoid A η (z j)) := h_main_y
      _ ≤ (C_main : ℝ≥0∞) * ∑ i : Fin 3,
          ENNReal.ofReal (ℓ i) * directionalSurfaceArea (b i) (p_y y)
            (polynomialZeroSet (p_y y) ∩ U) := by
        exact mul_le_mul_right h_sum_mono _

  let LHS_real : ℝ := LHS_ennreal.toReal

  have h_finite_and_pointwise : ∀ᵐ y ∂(volume.restrict B),
      (∀ i : Fin 3, directionalSurfaceArea (b i) (p_y y)
        (polynomialZeroSet (p_y y) ∩ U) ≠ ⊤) ∧
      LHS_ennreal ≤ (C_main : ℝ≥0∞) * ∑ i : Fin 3,
        ENNReal.ofReal (ℓ i) * directionalSurfaceArea (b i) (p_y y)
          (polynomialZeroSet (p_y y) ∩ U) := by
    filter_upwards [h_dsa_finite, h_pointwise] with y hfin hle
    exact ⟨hfin, hle⟩

  have h_real : ∀ᵐ y ∂(volume.restrict B),
      LHS_real ≤ (C_main : ℝ) * ∑ i : Fin 3,
        ℓ i * coefficientSurfaceFunctional P (b i) U y := by
    filter_upwards [h_finite_and_pointwise] with y h
    rcases h with ⟨hfin, hle⟩
    let RHS_ennreal : ENNReal := (C_main : ℝ≥0∞) * ∑ i : Fin 3,
      ENNReal.ofReal (ℓ i) * directionalSurfaceArea (b i) (p_y y)
        (polynomialZeroSet (p_y y) ∩ U)
    have h_rhs_fin : RHS_ennreal ≠ ⊤ := by
      dsimp only [RHS_ennreal]
      apply ENNReal.mul_ne_top
      · simp
      · rw [ENNReal.sum_ne_top]
        intro i _
        apply ENNReal.mul_ne_top
        · simp
        · exact hfin i
    have h1 : LHS_ennreal.toReal ≤ RHS_ennreal.toReal :=
      (ENNReal.toReal_le_toReal h_lhs_finite h_rhs_fin).mpr hle
    have h2 : RHS_ennreal.toReal = (C_main : ℝ) * ∑ i : Fin 3,
        ℓ i * coefficientSurfaceFunctional P (b i) U y := by
      dsimp only [RHS_ennreal, coefficientSurfaceFunctional]
      rw [ENNReal.toReal_mul, ENNReal.toReal_sum]
      · congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (ℓ_pos i).le]
      · intro i _
        apply ENNReal.mul_ne_top
        · simp
        · exact hfin i
    rw [h2] at h1
    exact h1

  have h_compact : IsCompact (Metric.closedBall x ε) := isCompact_closedBall x ε
  have h_int_on : ∀ i : Fin 3,
      IntegrableOn (coefficientSurfaceFunctional P (b i) U) B volume := by
    intro i
    have h_loc : LocallyIntegrable (coefficientSurfaceFunctional P (b i) U) volume := hInt i
    exact (h_loc.integrableOn_isCompact h_compact).mono_set Metric.ball_subset_closedBall

  have h_int_const : IntegrableOn (fun _ : CoefficientSpace P.dim => LHS_real) B volume := by
    have h_cont : Continuous (fun _ : CoefficientSpace P.dim => LHS_real) := continuous_const
    have h_loc : LocallyIntegrable (fun _ => LHS_real) volume := h_cont.locallyIntegrable
    exact (h_loc.integrableOn_isCompact h_compact).mono_set Metric.ball_subset_closedBall

  have h1_int : ∀ i : Fin 3, Integrable (coefficientSurfaceFunctional P (b i) U) (volume.restrict B) := by
    intro i; exact h_int_on i
  have h2_scaled : ∀ i : Fin 3, Integrable (fun y : CoefficientSpace P.dim => ℓ i * coefficientSurfaceFunctional P (b i) U y) (volume.restrict B) := by
    intro i; exact (h1_int i).smul (ℓ i)

  have h_int_rhs : IntegrableOn (fun y : CoefficientSpace P.dim =>
      (C_main : ℝ) * ∑ i : Fin 3, ℓ i * coefficientSurfaceFunctional P (b i) U y) B volume := by
    let f : Fin 3 → CoefficientSpace P.dim → ℝ := fun i y => ℓ i * coefficientSurfaceFunctional P (b i) U y
    have h3 : Integrable (fun y : CoefficientSpace P.dim => ∑ i : Fin 3, f i y) (volume.restrict B) :=
      integrable_finsetSum' (Finset.univ) (fun i _ => h2_scaled i)
    exact h3.smul (C_main : ℝ)

  have h5 : ∫ y in B, LHS_real ≤ ∫ y in B,
      (C_main : ℝ) * ∑ i : Fin 3, ℓ i * coefficientSurfaceFunctional P (b i) U y :=
    integral_mono_ae h_int_const h_int_rhs h_real

  have hvol_pos : 0 < volume B := by
    have h_open : IsOpen B := Metric.isOpen_ball
    have hne : B.Nonempty := Metric.nonempty_ball.mpr hε
    exact h_open.measure_pos volume hne
  have hvol_ne_top : volume B ≠ ⊤ := Metric.isBounded_ball.measure_lt_top.ne
  have hvol_toReal_pos : 0 < (volume B).toReal := by
    rw [ENNReal.toReal_pos_iff] <;> exact ⟨hvol_pos, hvol_ne_top.lt_top⟩

  have h6 : ∫ y in B, LHS_real = LHS_real * (volume B).toReal := by
    haveI : IsFiniteMeasure (volume.restrict B) := by
      constructor
      simpa using hvol_ne_top.lt_top
    have h_const : ∫ y, LHS_real ∂(volume.restrict B) =
        (volume.restrict B).real Set.univ • LHS_real :=
      integral_const (μ := volume.restrict B) LHS_real
    have h9 : (volume.restrict B).real Set.univ • LHS_real =
        LHS_real * (volume.restrict B Set.univ).toReal := by
      have h_real : (volume.restrict B).real Set.univ = ((volume.restrict B) Set.univ).toReal := by rfl
      rw [h_real, smul_eq_mul, mul_comm]
    have h10 : (volume.restrict B Set.univ) = volume B := by simp
    have h11 : ∫ y, LHS_real ∂(volume.restrict B) = LHS_real * (volume B).toReal := by
      rw [h_const, h9, h10]
    exact h11

  have h7 : ∫ y in B, (C_main : ℝ) * ∑ i : Fin 3, ℓ i * coefficientSurfaceFunctional P (b i) U y =
      (C_main : ℝ) * ∑ i : Fin 3, ℓ i * ∫ y in B, coefficientSurfaceFunctional P (b i) U y := by
    have h1_int2 : ∀ i : Fin 3, Integrable (coefficientSurfaceFunctional P (b i) U) (volume.restrict B) := by
      intro i; exact h_int_on i
    rw [integral_const_mul, integral_finsetSum]
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul]
    · intro i _
      exact h2_scaled i

  rw [h6, h7] at h5

  have hvol_translate : volume (Metric.ball (0 : CoefficientSpace P.dim) ε) = volume B :=
    (Measure.addHaar_ball_center volume x ε).symm

  have h8 : LHS_real ≤ (C_main : ℝ) * ∑ i : Fin 3,
      ℓ i * concreteMollifiedDirectionalArea P ε x (b i) U := by
    have h10 : 0 < (volume B).toReal := hvol_toReal_pos
    have h11 : LHS_real ≤ ((C_main : ℝ) * ∑ i : Fin 3, ℓ i * ∫ y in B, coefficientSurfaceFunctional P (b i) U y) / (volume B).toReal := by
      calc
        LHS_real = (LHS_real * (volume B).toReal) / (volume B).toReal := by
          field_simp [h10.ne']
        _ ≤ ((C_main : ℝ) * ∑ i : Fin 3, ℓ i * ∫ y in B, coefficientSurfaceFunctional P (b i) U y) / (volume B).toReal := by gcongr
    have h12 : ((C_main : ℝ) * ∑ i : Fin 3, ℓ i * ∫ y in B, coefficientSurfaceFunctional P (b i) U y) / (volume B).toReal =
        (C_main : ℝ) * ∑ i : Fin 3, ℓ i * concreteMollifiedDirectionalArea P ε x (b i) U := by
      have h13 : ∀ i : Fin 3, concreteMollifiedDirectionalArea P ε x (b i) U =
          (volume B).toReal⁻¹ * ∫ y in B, coefficientSurfaceFunctional P (b i) U y := by
        intro i
        simp only [concreteMollifiedDirectionalArea, ballAverage]
        rw [hvol_translate]
      have h14 : ∑ i : Fin 3, ℓ i * concreteMollifiedDirectionalArea P ε x (b i) U =
          (volume B).toReal⁻¹ * ∑ i : Fin 3, ℓ i * ∫ y in B, coefficientSurfaceFunctional P (b i) U y := by
        have h15 : ∑ i : Fin 3, ℓ i * concreteMollifiedDirectionalArea P ε x (b i) U =
            ∑ i : Fin 3, ℓ i * ((volume B).toReal⁻¹ * ∫ y in B, coefficientSurfaceFunctional P (b i) U y) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [h13 i]
        rw [h15]
        have h16 : ∑ i : Fin 3, ℓ i * ((volume B).toReal⁻¹ * ∫ y in B, coefficientSurfaceFunctional P (b i) U y) =
            (volume B).toReal⁻¹ * ∑ i : Fin 3, ℓ i * ∫ y in B, coefficientSurfaceFunctional P (b i) U y := by
          have h17 : ∀ i : Fin 3, ℓ i * ((volume B).toReal⁻¹ * ∫ y in B, coefficientSurfaceFunctional P (b i) U y) =
              (volume B).toReal⁻¹ * (ℓ i * ∫ y in B, coefficientSurfaceFunctional P (b i) U y) := by
            intro i
            exact mul_left_comm (ℓ i) ((volume B).toReal⁻¹) (∫ y in B, coefficientSurfaceFunctional P (b i) U y)
          rw [Finset.sum_congr rfl (fun i _ => h17 i)]
          rw [Finset.mul_sum]
        exact h16
      rw [h14]
      field_simp [h10.ne']
    rw [h12] at h11
    exact h11

  have h_nonneg_area : ∀ i : Fin 3, 0 ≤ concreteMollifiedDirectionalArea P ε x (b i) U := by
    intro i
    have h : 0 ≤ coefficientSurfaceFunctional P (b i) U := by
      intro y
      simp only [coefficientSurfaceFunctional]
      have h' : 0 ≤ (directionalSurfaceArea (b i) (parameterPolynomial P y) (polynomialZeroSet (parameterPolynomial P y) ∩ U)).toReal := ENNReal.toReal_nonneg
      exact h'
    have h_int_nonneg : 0 ≤ ∫ y in B, coefficientSurfaceFunctional P (b i) U y :=
      integral_nonneg h
    have h_vol_nonneg : 0 ≤ (volume (Metric.ball (0 : CoefficientSpace P.dim) ε)).toReal := by positivity
    simp only [concreteMollifiedDirectionalArea, ballAverage]
    exact mul_nonneg (inv_nonneg.mpr h_vol_nonneg) h_int_nonneg

  have h13 : 0 ≤ (C_main : ℝ) * ∑ i : Fin 3, ℓ i * concreteMollifiedDirectionalArea P ε x (b i) U := by
    have h_sum_nonneg : 0 ≤ ∑ i : Fin 3, ℓ i * concreteMollifiedDirectionalArea P ε x (b i) U := by
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (ℓ_pos i).le (h_nonneg_area i)
    exact mul_nonneg hC_main_pos.le h_sum_nonneg

  have h14 : LHS_ennreal ≤ ENNReal.ofReal ((C_main : ℝ) * ∑ i : Fin 3, ℓ i * concreteMollifiedDirectionalArea P ε x (b i) U) := by
    have h15 : LHS_ennreal = ENNReal.ofReal LHS_real :=
      (ENNReal.ofReal_toReal h_lhs_finite).symm
    rw [h15]
    exact ENNReal.ofReal_le_ofReal h8

  have h16 : ENNReal.ofReal ((C_main : ℝ) * ∑ i : Fin 3, ℓ i * concreteMollifiedDirectionalArea P ε x (b i) U) =
      (C_main : ℝ≥0∞) * ∑ i : Fin 3, ENNReal.ofReal (ℓ i) * ENNReal.ofReal (concreteMollifiedDirectionalArea P ε x (b i) U) := by
    have h_nonneg1 : ∀ i : Fin 3, 0 ≤ ℓ i := fun i => (ℓ_pos i).le
    have h161 : ENNReal.ofReal ((C_main : ℝ) * ∑ i : Fin 3, ℓ i * concreteMollifiedDirectionalArea P ε x (b i) U) =
        ENNReal.ofReal (C_main : ℝ) * ENNReal.ofReal (∑ i : Fin 3, ℓ i * concreteMollifiedDirectionalArea P ε x (b i) U) :=
      ENNReal.ofReal_mul hC_main_pos.le
    have h162 : ENNReal.ofReal (∑ i : Fin 3, ℓ i * concreteMollifiedDirectionalArea P ε x (b i) U) =
        ∑ i : Fin 3, ENNReal.ofReal (ℓ i * concreteMollifiedDirectionalArea P ε x (b i) U) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i _
      exact mul_nonneg (h_nonneg1 i) (h_nonneg_area i)
    have h163 : ∀ i : Fin 3, ENNReal.ofReal (ℓ i * concreteMollifiedDirectionalArea P ε x (b i) U) =
        ENNReal.ofReal (ℓ i) * ENNReal.ofReal (concreteMollifiedDirectionalArea P ε x (b i) U) := by
      intro i
      rw [ENNReal.ofReal_mul (h_nonneg1 i)]
    have h164 : ENNReal.ofReal (C_main : ℝ) = (C_main : ℝ≥0∞) := by simp
    rw [h161, h162, h164]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact h163 i

  rw [h16] at h14
  exact h14

end Kakeya.CV
