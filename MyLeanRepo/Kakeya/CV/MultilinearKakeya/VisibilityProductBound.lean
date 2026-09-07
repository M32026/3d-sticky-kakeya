import MyLeanRepo.Kakeya.CV.MultilinearKakeya.MollifiedColumnBudget

/-!
# Visibility product bound

The directional visibility estimate is converted into the pointwise
three-factor inequality used in the lattice factorization.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Kakeya.CV

private lemma cubeRoot_cube (a : ℝ) (ha : 0 ≤ a) :
    (Real.rpow a (1 / 3 : ℝ)) ^ 3 = a := by
  rw [← Real.rpow_natCast]
  convert Real.rpow_inv_natCast_pow ha
    (show (3 : ℕ) ≠ 0 by norm_num) using 1
  norm_num

/--
For three unit directions, visibility cubed times their triple volume is
controlled by the product of one plus their mollified directional areas.
-/
lemma exists_mollified_visibility_product_bound
    (hBody : ConcreteMollifiedVisibilityStatement)
    (hDirectional : VisibilityDirectionalBoundStatement) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {k : ℕ} (P : PolynomialParameterization k)
          (U : Set (Point 3)) (c : Point 3) (ε : ℝ)
          (x : CoefficientSpace P.dim) (v : Fin 3 → Point 3),
        MeasurableSet U →
        U ⊆ Metric.closedBall c 1 →
        0 < ε →
        (∀ i, ‖v i‖ = 1) →
        tripleVolume v * (concreteMollifiedVisibility P ε x U) ^ 3 ≤
          C ^ 3 *
            ∏ i, (1 +
              concreteMollifiedDirectionalArea P ε x (v i) U) := by
  rcases hDirectional with ⟨C, hC, hDirectional⟩
  refine ⟨C, hC, ?_⟩
  intro k P U c ε x v hU_meas hU hε hv
  let K : Set (Point 3) := concreteMollifiedVisibilityBody P ε x U
  let s : Fin 3 → ℝ := fun i =>
    1 + concreteMollifiedDirectionalArea P ε x (v i) U
  have hbody := hBody k P U c ε x hU_meas hU hε
  have hs_pos : ∀ i, 0 < s i := by
    intro i
    dsimp only [s]
    have harea :=
      concreteMollifiedDirectionalArea_nonneg P ε x (v i) U
    linarith
  have hscaled_mem : ∀ i, (s i)⁻¹ • v i ∈ K := by
    intro i
    have hinv_pos : 0 < (s i)⁻¹ := inv_pos.mpr (hs_pos i)
    have hinv_le : (s i)⁻¹ ≤ 1 := by
      apply (inv_le_one₀ (hs_pos i)).2
      dsimp only [s]
      linarith [concreteMollifiedDirectionalArea_nonneg P ε x (v i) U]
    have hnorm :
        ‖(s i)⁻¹ • v i‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hinv_pos, hv i]
      simpa using hinv_le
    have harea_scale :
        concreteMollifiedDirectionalArea P ε x ((s i)⁻¹ • v i) U =
          (s i)⁻¹ *
            concreteMollifiedDirectionalArea P ε x (v i) U :=
      concreteMollifiedDirectionalArea_homogeneous P ε x (s i)⁻¹
        (v i) U hinv_pos.le
    have harea_le :
        (s i)⁻¹ *
            concreteMollifiedDirectionalArea P ε x (v i) U ≤ 1 := by
      rw [inv_mul_le_iff₀ (hs_pos i)]
      dsimp only [s]
      linarith
    exact ⟨by
      simpa [unitBall, Metric.mem_closedBall] using hnorm, by
      change
        concreteMollifiedDirectionalArea P ε x ((s i)⁻¹ • v i) U ≤ 1
      rw [harea_scale]
      exact harea_le⟩
  have hroot :=
    hDirectional K hbody.1 hbody.2 v s hv hs_pos hscaled_mem
  have htv_nonneg : 0 ≤ tripleVolume v := abs_nonneg _
  have hvis_nonneg :
      0 ≤ concreteMollifiedVisibility P ε x U :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hsprod_nonneg : 0 ≤ ∏ i, s i :=
    Finset.prod_nonneg fun i _ => (hs_pos i).le
  have hleft_nonneg :
      0 ≤ Real.rpow (tripleVolume v) (1 / 3 : ℝ) *
        concreteMollifiedVisibility P ε x U :=
    mul_nonneg (Real.rpow_nonneg htv_nonneg _) hvis_nonneg
  have hright_nonneg :
      0 ≤ C * Real.rpow (∏ i, s i) (1 / 3 : ℝ) :=
    mul_nonneg hC.le (Real.rpow_nonneg hsprod_nonneg _)
  have hcubed :
      (Real.rpow (tripleVolume v) (1 / 3 : ℝ) *
          concreteMollifiedVisibility P ε x U) ^ 3 ≤
        (C * Real.rpow (∏ i, s i) (1 / 3 : ℝ)) ^ 3 :=
    pow_le_pow_left₀ hleft_nonneg hroot 3
  rw [mul_pow, cubeRoot_cube (tripleVolume v) htv_nonneg,
    mul_pow, cubeRoot_cube (∏ i, s i) hsprod_nonneg] at hcubed
  simpa [s] using hcubed

end Kakeya.CV
