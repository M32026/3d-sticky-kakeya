import MyLeanRepo.Kakeya.CV.MultilinearKakeya.ColumnGeometry

/-!
# Mollified directional-area column budgets

Finite lattice-cube column estimates are preserved by normalized averaging
over polynomial coefficient space.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Kakeya.CV

/--
The concrete mollified directional areas of all active cubes meeting one
unit line have a uniform degree-linear column budget.
-/
lemma concreteMollifiedDirectionalArea_column_le
    {k : ℕ} (P : PolynomialParameterization k)
    (hSurface : ConcreteMollifiedSurfaceStatement)
    (offsets : Finset (Point 3))
    (hoffsets : ∀ (a e : Point 3),
      {x | Metric.infDist x (affineLine a e) ≤ 3} ⊆
        ⋃ c ∈ offsets, unitTube (a + c) e)
    (ε : ℝ) (x : CoefficientSpace P.dim) (hε : 0 < ε)
    (F : UnitLineFamily) (i : Fin F.card)
    (active : Finset UnitLatticeCube)
    (hmeet : ∀ q ∈ active, unitLineMeetsLatticeCube F i q) :
    ∑ q ∈ active,
        concreteMollifiedDirectionalArea P ε x (F.direction i)
          (unitCube (latticeCubeCenter q)) ≤
      (8 * (offsets.card : ENNReal) *
        (12 * planeConstant * ENNReal.ofReal Real.pi * (k : ENNReal))).toReal := by
  classical
  let C : ENNReal :=
    8 * (offsets.card : ENNReal) *
      (12 * planeConstant * ENNReal.ofReal Real.pi * (k : ENNReal))
  let B : Set (CoefficientSpace P.dim) := Metric.ball x ε
  have hC_ne_top : C ≠ ⊤ := by
    dsimp only [C]
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top <;> simp
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · exact ENNReal.mul_ne_top (by simp) planeConstant_ne_top
        · simp
      · simp
  have hpoint_ennreal : ∀ y : CoefficientSpace P.dim,
      ∑ q ∈ active,
          directionalSurfaceArea (F.direction i) (parameterPolynomial P y)
            (polynomialZeroSet (parameterPolynomial P y) ∩
              unitCube (latticeCubeCenter q)) ≤ C := by
    intro y
    exact parameterDirectionalSurfaceArea_column_le P offsets hoffsets y
      F i active hmeet
  have hterm_ne_top : ∀ y : CoefficientSpace P.dim, ∀ q ∈ active,
      directionalSurfaceArea (F.direction i) (parameterPolynomial P y)
        (polynomialZeroSet (parameterPolynomial P y) ∩
          unitCube (latticeCubeCenter q)) ≠ ⊤ := by
    intro y q hq
    apply ne_top_of_le_ne_top hC_ne_top
    exact (Finset.single_le_sum
      (fun r _ => bot_le :
        ∀ r ∈ active,
          (0 : ENNReal) ≤
            directionalSurfaceArea (F.direction i) (parameterPolynomial P y)
              (polynomialZeroSet (parameterPolynomial P y) ∩
                unitCube (latticeCubeCenter r)))
      hq).trans (hpoint_ennreal y)
  have hpoint_real : ∀ y : CoefficientSpace P.dim,
      ∑ q ∈ active,
          coefficientSurfaceFunctional P (F.direction i)
            (unitCube (latticeCubeCenter q)) y ≤ C.toReal := by
    intro y
    change
      (∑ q ∈ active,
        (directionalSurfaceArea (F.direction i) (parameterPolynomial P y)
          (polynomialZeroSet (parameterPolynomial P y) ∩
            unitCube (latticeCubeCenter q))).toReal) ≤ C.toReal
    have hsum_ne_top :
        (∑ q ∈ active,
          directionalSurfaceArea (F.direction i) (parameterPolynomial P y)
            (polynomialZeroSet (parameterPolynomial P y) ∩
              unitCube (latticeCubeCenter q))) ≠ ⊤ :=
      ne_top_of_le_ne_top hC_ne_top (hpoint_ennreal y)
    rw [← ENNReal.toReal_sum (hterm_ne_top y)]
    exact (ENNReal.toReal_le_toReal hsum_ne_top hC_ne_top).mpr
      (hpoint_ennreal y)
  have h_compact : IsCompact (Metric.closedBall x ε) :=
    isCompact_closedBall x ε
  have h_integrable : ∀ q ∈ active,
      Integrable
        (coefficientSurfaceFunctional P (F.direction i)
          (unitCube (latticeCubeCenter q)))
        (volume.restrict B) := by
    intro q _
    have hlocal :=
      (hSurface k P (unitCube (latticeCubeCenter q))
        (latticeCubeCenter q) ε
        (unitCube_measurableSet (latticeCubeCenter q))
        (unitCube_subset_closedBall (latticeCubeCenter q)) hε).1
        (F.direction i)
    exact (hlocal.integrableOn_isCompact h_compact).mono_set
      Metric.ball_subset_closedBall
  have hsum_integrable :
      Integrable
        (fun y : CoefficientSpace P.dim =>
          ∑ q ∈ active,
            coefficientSurfaceFunctional P (F.direction i)
              (unitCube (latticeCubeCenter q)) y)
        (volume.restrict B) :=
    integrable_finsetSum active h_integrable
  have hconst_integrable :
      Integrable (fun _ : CoefficientSpace P.dim => C.toReal)
        (volume.restrict B) := by
    exact integrableOn_const
  have hintegral :
      ∫ y in B,
          ∑ q ∈ active,
            coefficientSurfaceFunctional P (F.direction i)
              (unitCube (latticeCubeCenter q)) y ≤
        ∫ _y in B, C.toReal := by
    exact integral_mono hsum_integrable hconst_integrable hpoint_real
  have hvol_pos : 0 < volume B := by
    exact Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr hε)
  have hvol_ne_top : volume B ≠ ⊤ :=
    Metric.isBounded_ball.measure_lt_top.ne
  have hvol_real_pos : 0 < (volume B).toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨hvol_pos, hvol_ne_top.lt_top⟩
  have hvol_translate :
      volume (Metric.ball (0 : CoefficientSpace P.dim) ε) = volume B :=
    (Measure.addHaar_ball_center volume x ε).symm
  have hsum_average :
      ∑ q ∈ active,
          concreteMollifiedDirectionalArea P ε x (F.direction i)
            (unitCube (latticeCubeCenter q)) =
        (volume B).toReal⁻¹ *
          ∫ y in B,
            ∑ q ∈ active,
              coefficientSurfaceFunctional P (F.direction i)
                (unitCube (latticeCubeCenter q)) y := by
    simp only [concreteMollifiedDirectionalArea, ballAverage, hvol_translate]
    rw [← Finset.mul_sum, integral_finsetSum active h_integrable]
  have hconst_integral :
      ∫ _y in B, C.toReal = C.toReal * (volume B).toReal := by
    rw [setIntegral_const]
    have hreal : volume.real B = (volume B).toReal := rfl
    rw [hreal, smul_eq_mul, mul_comm]
  change
    (∑ q ∈ active,
      concreteMollifiedDirectionalArea P ε x (F.direction i)
        (unitCube (latticeCubeCenter q))) ≤ C.toReal
  rw [hsum_average]
  calc
    (volume B).toReal⁻¹ *
        ∫ y in B,
          ∑ q ∈ active,
            coefficientSurfaceFunctional P (F.direction i)
              (unitCube (latticeCubeCenter q)) y
      ≤ (volume B).toReal⁻¹ * (∫ _y in B, C.toReal) := by
        exact mul_le_mul_of_nonneg_left hintegral (by positivity)
    _ = (volume B).toReal⁻¹ * (C.toReal * (volume B).toReal) := by
      rw [hconst_integral]
    _ = C.toReal := by
      field_simp [hvol_real_pos.ne']

end Kakeya.CV
