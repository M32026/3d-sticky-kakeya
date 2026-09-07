import MyLeanRepo.Kakeya.CV.VisibilityDegreeBound.Helpers
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Local integrability of the coefficient surface functional

Once coefficient-space measurability is known, generic regularity and the
polynomial cylinder estimate give a uniform almost-everywhere bound on every
bounded spatial region.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal Real

namespace Kakeya.CV

lemma coefficientSurfaceFunctional_locallyIntegrable
    {k : ℕ} {P : PolynomialParameterization k}
    {U : Set (Point 3)} {c : Point 3} {u : Point 3}
    (hU : U ⊆ Metric.closedBall c 1)
    (hGeneric : GenericPolynomialRegularityStatement)
    (hCylinder : PolynomialCylinderEstimateStatement)
    (hSingular : SquarefreeSingularSetNullStatement)
    (h_meas : AEMeasurable (coefficientSurfaceFunctional P u U) volume) :
    LocallyIntegrable (coefficientSurfaceFunctional P u U) volume := by
  rcases hCylinder with ⟨C, hC_pos, hCyl_est⟩
  let p_x : CoefficientSpace P.dim → MvPolynomial (Fin 3) ℝ := parameterPolynomial P
  let Bad : Set (CoefficientSpace P.dim) :=
    {x | ¬(p_x x ≠ 0 ∧ Squarefree (p_x x))}
  have hBad_ball : ∀ (n : ℕ),
      volume (Bad ∩ Metric.ball (0 : CoefficientSpace P.dim) (n + 1)) = 0 := by
    intro n
    let ball_n := Metric.ball (0 : CoefficientSpace P.dim) (n + 1)
    have h_ball_meas : MeasurableSet ball_n := isOpen_ball.measurableSet
    have h : ∀ᵐ (y : CoefficientSpace P.dim) ∂(volume.restrict ball_n),
        p_x y ≠ 0 ∧ Squarefree (p_x y) :=
      hGeneric k P (0 : CoefficientSpace P.dim) (n + 1 : ℝ) (by positivity)
    have h1 : (volume.restrict ball_n) Bad = 0 := by
      simpa [ae_iff, Bad] using h
    have h2 : (volume.restrict ball_n) Bad = volume (Bad ∩ ball_n) :=
      MeasureTheory.Measure.restrict_apply' (hs := h_ball_meas)
    rw [h2] at h1
    exact h1
  have hCover : (⋃ n : ℕ, Metric.ball (0 : CoefficientSpace P.dim) (n + 1)) =
      (Set.univ : Set (CoefficientSpace P.dim)) := by
    apply Set.Subset.antisymm (by simp)
    intro x _
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    exact Set.mem_iUnion.mpr ⟨n, by
      simpa [Metric.mem_ball, dist_zero_right] using (show ‖x‖ < (n + 1 : ℝ) by linarith)⟩
  have hBad_null : volume Bad = 0 := by
    have h1 : Bad ⊆ ⋃ n : ℕ, (Bad ∩ Metric.ball (0 : CoefficientSpace P.dim) (n + 1)) := by
      intro x hx
      have h2 : x ∈ (⋃ n : ℕ, Metric.ball (0 : CoefficientSpace P.dim) (n + 1)) := by
        rw [hCover]
        trivial
      rcases Set.mem_iUnion.mp h2 with ⟨n, hn⟩
      exact Set.mem_iUnion.mpr ⟨n, ⟨hx, hn⟩⟩
    have h3 : volume (⋃ n : ℕ, (Bad ∩ Metric.ball (0 : CoefficientSpace P.dim) (n + 1))) = 0 := by
      rw [MeasureTheory.measure_iUnion_null]
      exact hBad_ball
    exact nonpos_iff_eq_zero.mp (le_trans (measure_mono h1) (le_of_eq h3))
  have h_reg_ae : ∀ᵐ (x : CoefficientSpace P.dim) ∂volume,
      p_x x ≠ 0 ∧ Squarefree (p_x x) := by
    simpa [ae_iff, Bad] using hBad_null
  let B : ℝ := ‖u‖ * (C : ℝ) * (k : ℝ)
  have hB_nonneg : 0 ≤ B := by positivity
  have h_bdd : ∀ᵐ (x : CoefficientSpace P.dim) ∂volume,
      ‖coefficientSurfaceFunctional P u U x‖ ≤ B := by
    filter_upwards [h_reg_ae] with x hx
    set p : MvPolynomial (Fin 3) ℝ := p_x x with hp
    set S : Set (Point 3) := polynomialZeroSet p ∩ U with hS
    have hp_ne : p ≠ 0 := hx.1
    have hp_sq : Squarefree p := hx.2
    have hp_sing : HasNegligibleSingularSet p := hSingular p hp_ne hp_sq
    have hp_deg : p.totalDegree ≤ k := (P.equiv x).property
    have h_expand :
        coefficientSurfaceFunctional P u U x = (directionalSurfaceArea u p S).toReal := by
      simp only [coefficientSurfaceFunctional]
      have h_eq1 : parameterPolynomial P x = p := hp.symm
      rw [h_eq1, ← hS]
    by_cases hu : u = 0
    · have h0 : directionalSurfaceArea u p S = 0 := by
        rw [hu]
        have h := directionalSurfaceArea_homogeneity 0 (by norm_num) (0 : Point 3) p S
        simpa using h
      have h_f : coefficientSurfaceFunctional P u U x = 0 := by
        rw [h_expand, h0]
        simp
      rw [h_f]
      simp [B, hB_nonneg]
    · have hnorm_pos : 0 < ‖u‖ := by
        rw [norm_pos_iff]
        exact hu
      set e : Point 3 := ‖u‖⁻¹ • u with he
      have he_norm : ‖e‖ = 1 := by
        simp [e, norm_smul, hnorm_pos.ne']
      have hU_tube : U ⊆ unitTube c e := by
        calc
          U ⊆ Metric.closedBall c 1 := hU
          _ ⊆ unitTube c e := unitBall_subset_unitTube c e he_norm
      have hS_subset : S ⊆ polynomialZeroSet p ∩ unitTube c e :=
        Set.inter_subset_inter_right _ hU_tube
      have h_cyl : directionalSurfaceArea e p (polynomialZeroSet p ∩ unitTube c e) ≤
          (C : ℝ≥0∞) * (k : ℝ≥0∞) :=
        hCyl_est k p c e hp_ne hp_sing hp_deg he_norm
      have h_area_e : directionalSurfaceArea e p S ≤ (C : ℝ≥0∞) * (k : ℝ≥0∞) :=
        (directionalSurfaceArea_mono e p hS_subset).trans h_cyl
      have h_u_eq : u = ‖u‖ • e := by
        simp [e, smul_smul]
        field_simp [hnorm_pos.ne']
        simp
      have h_tmp : directionalSurfaceArea (‖u‖ • e) p S =
          ENNReal.ofReal ‖u‖ * directionalSurfaceArea e p S :=
        directionalSurfaceArea_homogeneity ‖u‖ (by positivity) e p S
      have h_hom : directionalSurfaceArea u p S =
          ENNReal.ofReal ‖u‖ * directionalSurfaceArea e p S := by
        have h_eq1 : directionalSurfaceArea u p S =
            directionalSurfaceArea (‖u‖ • e) p S :=
          congr_arg (fun v : Point 3 => directionalSurfaceArea v p S) h_u_eq
        exact Eq.trans h_eq1 h_tmp
      have hC_coe : (C : ℝ≥0∞) = ENNReal.ofReal (C : ℝ) := by simp
      have hk_coe : (k : ℝ≥0∞) = ENNReal.ofReal (k : ℝ) := by simp
      have h6 :
          ENNReal.ofReal ‖u‖ * ((C : ℝ≥0∞) * (k : ℝ≥0∞)) = ENNReal.ofReal B := by
        rw [hC_coe, hk_coe]
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp [B]
        ring
      have h_bound_ennreal : directionalSurfaceArea u p S ≤ ENNReal.ofReal B := by
        calc
          directionalSurfaceArea u p S
              = ENNReal.ofReal ‖u‖ * directionalSurfaceArea e p S := h_hom
          _ ≤ ENNReal.ofReal ‖u‖ * ((C : ℝ≥0∞) * (k : ℝ≥0∞)) := by gcongr
          _ = ENNReal.ofReal B := h6
      rw [h_expand]
      have h4 : (directionalSurfaceArea u p S).toReal ≤ B :=
        ENNReal.toReal_le_of_le_ofReal hB_nonneg h_bound_ennreal
      have h_nonneg : 0 ≤ (directionalSurfaceArea u p S).toReal := ENNReal.toReal_nonneg
      simpa [Real.norm_eq_abs, abs_of_nonneg h_nonneg] using h4
  have h_strong : AEStronglyMeasurable (coefficientSurfaceFunctional P u U) volume :=
    h_meas.aestronglyMeasurable
  have h_main : ∀ (K : Set (CoefficientSpace P.dim)), IsCompact K →
      IntegrableOn (coefficientSurfaceFunctional P u U) K volume := by
    intro K hK
    have hK_finite : volume K ≠ ⊤ := hK.measure_ne_top
    have h_bdd_K : ∀ᵐ (y : CoefficientSpace P.dim) ∂(volume.restrict K),
        ‖coefficientSurfaceFunctional P u U y‖ ≤ B := by
      have h' : ∀ᵐ (x : CoefficientSpace P.dim) ∂volume,
          x ∈ K → ‖coefficientSurfaceFunctional P u U x‖ ≤ B :=
        h_bdd.mono (fun x hx _ => hx)
      rw [MeasureTheory.ae_restrict_iff' (hs := hK.measurableSet)]
      exact h'
    exact MeasureTheory.Measure.integrableOn_of_bounded hK_finite h_strong h_bdd_K
  exact locallyIntegrable_iff.mpr h_main

end Kakeya.CV
