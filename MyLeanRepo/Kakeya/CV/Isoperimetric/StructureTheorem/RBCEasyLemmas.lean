import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.DistributionalDerivative
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.TrueReducedBoundary
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.PerimeterVariation
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.SmoothApprox
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.PerimeterDefinition
import Mathlib.Tactic

/-!
# RBC Easy Lemmas (M4, M5, M6)

Proves three auxiliary lemmas for the Reduced Boundary Cover theorem:
- M4: Besicovitch differentiation for perimeter measure (weak form)
- M5: Measurability of trueReducedBoundary
- M6: perimeterIn upper bound → perimeterMeasure upper bound
-/


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry.StructureTheorem

open Perimeter

variable {n : ℕ}

-- ============================================================================
-- M4: Besicovitch differentiation theorem for perimeter measure (weak form)
-- ============================================================================

/-- **Besicovitch differentiation for perimeter measure** (weak form).

For each fixed integrable `g`, differentiation holds `perimeterMeasure U`-a.e. -/
theorem lebesgue_diff_perimeter_measure_weak
    {U : Set (E n)} (h_perim_finite : perimeter U < ⊤)
    (g : E n → ℝ) (hg : Integrable g (perimeterMeasure U)) :
    ∀ᵐ (x : E n) ∂(perimeterMeasure U),
      Tendsto (fun r : ℝ =>
        (∫ y in closedBall x r, g y ∂(perimeterMeasure U)) /
          (perimeterMeasure U (closedBall x r)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (g x)) := by
  let μ := perimeterMeasure U
  have hD_eq : (distributionalDerivative U).variation = μ := by rfl
  have h_fin : μ Set.univ < ⊤ := by
    have h_eq : perimeter U = (distributionalDerivative U).variation Set.univ :=
      perimeter_eq_variation U h_perim_finite
    rw [← hD_eq]
    exact h_eq ▸ h_perim_finite
  letI : IsFiniteMeasure μ := ⟨h_fin⟩
  let v := Besicovitch.vitaliFamily μ
  have hgl : LocallyIntegrable g μ := hg.locallyIntegrable

  have h_avg : ∀ᵐ (x : E n) ∂μ,
      Tendsto (fun A : Set (E n) => ⨍ (y : E n) in A, g y ∂μ)
        (v.filterAt x) (nhds (g x)) :=
    VitaliFamily.ae_tendsto_average v hgl

  have h_ball_tendsto : ∀ (x : E n),
      Tendsto (fun r : ℝ => closedBall x r)
        (nhdsWithin 0 (Set.Ioi 0)) (v.filterAt x) := by
    intro x
    have h_basis : (v.filterAt x).HasBasis (fun ε : ℝ => 0 < ε)
        (fun ε => {t : Set (E n) | t ∈ v.setsAt x ∧ t ⊆ closedBall x ε}) :=
      VitaliFamily.filterAt_basis_closedBall v x
    rw [h_basis.tendsto_right_iff]
    intro ε hε
    have h_event : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
        closedBall x r ∈ v.setsAt x ∧ closedBall x r ⊆ closedBall x ε := by
      have h_nhds : Set.Ioo (0 : ℝ) ε ∈ nhdsWithin 0 (Set.Ioi 0) := by
        have h1 : Set.Iio ε ∈ nhds (0 : ℝ) := Iio_mem_nhds hε
        have h2 : Set.Iio ε ∈ nhdsWithin 0 (Set.Ioi 0) := Filter.mem_inf_of_left h1
        have h3 : Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0) := self_mem_nhdsWithin
        have h4 : Set.Ioo (0 : ℝ) ε = Set.Iio ε ∩ Set.Ioi (0 : ℝ) := by
          ext x; simp [Set.mem_Ioo, Set.mem_Iio, Set.mem_Ioi] <;> tauto
        rw [h4]
        exact inter_mem h2 h3
      filter_upwards [h_nhds] with r hr
      have hr_pos : 0 < r := hr.1
      have hr_lt : r < ε := hr.2
      have h1 : closedBall x r ∈ v.setsAt x := by
        simpa [Besicovitch.vitaliFamily, Set.mem_image] using ⟨r, hr_pos, rfl⟩
      have h2 : closedBall x r ⊆ closedBall x ε :=
        closedBall_subset_closedBall hr_lt.le
      exact ⟨h1, h2⟩
    exact h_event

  filter_upwards [h_avg] with x hx
  have h_comp : Tendsto (fun r : ℝ => ⨍ (y : E n) in closedBall x r, g y ∂μ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (g x)) :=
    hx.comp (h_ball_tendsto x)
  have h_eq_avg : (fun r : ℝ => ⨍ (y : E n) in closedBall x r, g y ∂μ) =
      (fun r : ℝ => (∫ y in closedBall x r, g y ∂μ) / (μ (closedBall x r)).toReal) := by
    funext r
    simp [MeasureTheory.average, div_eq_inv_mul]
    <;> ring
  rw [h_eq_avg] at h_comp
  exact h_comp

-- ============================================================================
-- M5: Measurability of trueReducedBoundary
-- ============================================================================

/-- The `trueReducedBoundary` is a measurable set. -/
lemma trb_measurable {U : Set (E n)} (h_perim_finite : perimeter U < ⊤) :
    MeasurableSet (trueReducedBoundary U) := by
  let μ := perimeterMeasure U
  -- The condition `∀ r > 0, 0 < μ (ball x r)` is exactly `x ∈ μ.support`
  have h1 : {x : E n | ∀ (r : ℝ), 0 < r → 0 < μ (ball x r)} = μ.support := by
    ext x
    simp only [Set.mem_setOf_eq]
    have h_ball_basis : (nhds x).HasBasis (fun r : ℝ => 0 < r) (fun r : ℝ => ball x r) :=
      Metric.nhds_basis_ball
    rw [h_ball_basis.mem_measureSupport]
    <;> rfl
  have h1' : MeasurableSet μ.support :=
    (MeasureTheory.Measure.isClosed_support (μ := μ)).measurableSet
  have h_meas : Measurable (measureTheoreticNormal U) :=
    measureTheoreticNormal_measurable h_perim_finite
  have h_norm_meas : Measurable (fun x : E n => ‖measureTheoreticNormal U x‖) := h_meas.norm
  have h2 : MeasurableSet {x : E n | ‖measureTheoreticNormal U x‖ = 1} := by
    have h_set_eq : {x : E n | ‖measureTheoreticNormal U x‖ = 1} =
        (fun x : E n => ‖measureTheoreticNormal U x‖) ⁻¹' {(1 : ℝ)} := by
      ext x; simp
    rw [h_set_eq]
    exact h_norm_meas (MeasurableSet.singleton 1)
  have h3 : trueReducedBoundary U =
      μ.support ∩ {x | ‖measureTheoreticNormal U x‖ = 1} := by
    ext x
    simp only [trueReducedBoundary, Set.mem_inter_iff, Set.mem_setOf_eq]
    have h4 : (∀ (r : ℝ), 0 < r → 0 < μ (ball x r)) ↔ x ∈ μ.support := by
      have h5 : x ∈ {x : E n | ∀ (r : ℝ), 0 < r → 0 < μ (ball x r)} ↔ x ∈ μ.support := by
        rw [h1]
      simpa using h5
    constructor
    · rintro ⟨h, hnorm⟩
      exact ⟨h4.mp h, hnorm⟩
    · rintro ⟨h, hnorm⟩
      exact ⟨h4.mpr h, hnorm⟩
  rw [h3]
  exact h1'.inter h2

-- ============================================================================
-- M6 helper: perimeterMeasure on closed ball ≤ perimeterIn on larger open ball
-- ============================================================================

/-- Localized variation inequality: the perimeter measure on a closed ball
is bounded by the local perimeter in a strictly larger open ball. -/
lemma perimeterMeasure_closedBall_le_perimeterIn_ball
    {U : Set (E n)} {x : E n} {r r' : ℝ} (hr : 0 < r) (hr' : r < r')
    (h_perim_finite : perimeter U < ⊤) :
    perimeterMeasure U (closedBall x r) ≤ perimeterIn U (ball x r') := by
  let D := distributionalDerivative U
  let μ := D.variation
  have h_fin : μ Set.univ < ⊤ := by
    have h_eq : perimeter U = μ Set.univ := perimeter_eq_variation U h_perim_finite
    exact h_eq ▸ h_perim_finite
  letI : IsFiniteMeasure μ := ⟨h_fin⟩

  let K := closedBall x r
  let Ω := ball x r'
  have hK_meas : MeasurableSet K := isClosed_closedBall.measurableSet
  have hμK_ne_top : μ K ≠ ⊤ := measure_ne_top μ K

  -- Radial cutoff: ψ = 1 on K, support = Ω, 0 ≤ ψ ≤ 1, smooth
  let bump : ContDiffBump x := ⟨r, r', hr, hr'⟩
  let ψ : E n → ℝ := bump
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := bump.contDiff (n := (⊤ : ℕ∞))
  have hψ_one : ∀ y ∈ K, ψ y = 1 := fun y hy => bump.one_of_mem_closedBall hy
  have hψ_supp_eq : Function.support ψ = Ω := bump.support_eq
  have hψ_nonneg : ∀ y, 0 ≤ ψ y := fun y => bump.nonneg
  have hψ_le_one : ∀ y, ψ y ≤ 1 := fun y => bump.le_one

  have hPIn_le : perimeterIn U Ω ≤ perimeter U := by
    apply iSup_le
    intro Φ
    exact le_iSup (fun (ψ : TestVectorField) => ENNReal.ofReal |∫ x in U, divergence ψ.toFun x|) Φ.val
  have hPIn_lt_top : perimeterIn U Ω < ⊤ :=
    hPIn_le.trans_lt h_perim_finite

  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hP_lt
  set ε2 : NNReal := ε / 2 with hε2_def
  have hε2_pos : 0 < ε2 := by positivity
  set ε2r : ℝ := (ε2 : ℝ) with hε2r_def
  have hε2r_pos : 0 < ε2r := by positivity

  -- Finite partition approximating the variation on K
  rcases VectorMeasure.exists_variation_le_add D hK_meas hε2_pos hμK_ne_top with
    ⟨P, hP_sub, hP_disj, hP_meas, hP_sum⟩

  -- Polar function: v(p) = D(p)/‖D(p)‖
  let v : Set (E n) → E n := fun p =>
    if h : D p = 0 then 0 else (‖D p‖⁻¹ : ℝ) • D p
  have hv_bound : ∀ p ∈ P, ‖v p‖ ≤ 1 := by
    intro p _
    dsimp only [v]
    by_cases h : D p = 0
    · rw [dif_pos h]; simp
    · rw [dif_neg h]
      have hpos : 0 < ‖D p‖ := norm_pos_iff.mpr h
      have hnorm : ‖(‖D p‖⁻¹ : ℝ) • D p‖ = 1 := by
        rw [norm_smul]
        have h5 : ‖(‖D p‖⁻¹ : ℝ)‖ = ‖D p‖⁻¹ := by
          simp [abs_of_pos (show 0 < (‖D p‖⁻¹ : ℝ) from by positivity)]
        rw [h5]
        field_simp [hpos.ne'] <;> ring
      rw [hnorm] <;> norm_num
  have hv_inner : ∀ p ∈ P, inner ℝ (v p) (D p) = ‖D p‖ := by
    intro p _
    dsimp only [v]
    by_cases h : D p = 0
    · rw [dif_pos h, h]; simp
    · rw [dif_neg h]
      have hpos : 0 < ‖D p‖ := norm_pos_iff.mpr h
      have h1 : inner ℝ ((‖D p‖⁻¹ : ℝ) • D p) (D p) = (‖D p‖⁻¹ : ℝ) * inner ℝ (D p) (D p) := by
        rw [inner_smul_left] <;> simp
      rw [h1]
      have h2 : inner ℝ (D p) (D p) = ‖D p‖ ^ 2 := by
        have h21 : inner ℝ (D p) (D p) = ↑‖D p‖ ^ 2 := inner_self_eq_norm_sq_to_K (D p)
        exact_mod_cast h21
      rw [h2]
      field_simp [hpos.ne'] <;> ring

  -- Construct simple function g = Σ v(p) · 1_p inline
  let g_p (p : Set (E n)) : E n → E n := Set.indicator p (fun _ : E n => v p)
  let g : E n → E n := ∑ p ∈ P, g_p p
  have h_supp_gp : ∀ p ∈ P, Function.support (g_p p) ⊆ p := by
    intro p _ y hy
    by_contra h
    have h6 : g_p p y = 0 := by simp [g_p, h]
    exact hy (by simpa [Function.support] using h6)
  have h_disj : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint (Function.support (g_p p)) (Function.support (g_p q)) := by
    intro p hp q hq hne
    have hP_disj' : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint p q := by
      intro p hp q hq hne
      simpa [Function.onFun] using hP_disj hp hq hne
    exact Disjoint.mono (h_supp_gp p hp) (h_supp_gp q hq) (hP_disj' p hp q hq hne)
  have h_bound_gp : ∀ p ∈ P, ∀ x, ‖g_p p x‖ ≤ 1 := by
    intro p hp x
    by_cases hx : x ∈ p
    · simpa [g_p, hx] using hv_bound p hp
    · simp [g_p, hx] <;> norm_num
  have hg_bound : ∀ x, ‖g x‖ ≤ 1 := by
    simpa [g] using norm_sum_disjoint_le_one h_disj h_bound_gp
  have hgp_int : ∀ p ∈ P, D.Integrable (g_p p) := by
      intro p hp
      have hpm : MeasurableSet p := hP_meas p hp
      have h3 : Measurable (g_p p) := measurable_const.indicator hpm
      have h4 : AEStronglyMeasurable (g_p p) D.variation := h3.aestronglyMeasurable
      have h6 : ∀ x, ‖g_p p x‖ₑ ≤ 1 := by
        intro x; by_cases hx : x ∈ p <;> simp [g_p, hx] <;> simpa [enorm] using ENNReal.ofReal_le_one.mpr (hv_bound p ‹_›)
      have h7 : ∫⁻ x, ‖g_p p x‖ₑ ∂D.variation < ⊤ := by
        calc ∫⁻ x, ‖g_p p x‖ₑ ∂D.variation ≤ ∫⁻ x, (1 : ENNReal) ∂D.variation := lintegral_mono h6
          _ = D.variation Set.univ := by simp
          _ < ⊤ := h_fin
      exact ⟨h4, h7⟩
  have hg_int : D.Integrable g := VectorMeasure.Integrable.finsetSum P hgp_int
  have hg_integral : ∫ᵛ x, g x ∂[innerBilinear; D] = ∑ p ∈ P, innerBilinear (v p) (D p) := by
    have h_indicator_int : ∀ p ∈ P, ∫ᵛ x, g_p p x ∂[innerBilinear; D] = innerBilinear (v p) (D p) := by
      intro p hp
      have hpm : MeasurableSet p := hP_meas p hp
      have hνp : D.variation p ≠ ⊤ := measure_ne_top D.variation p
      exact indicatorIntegral D hpm hνp (v p)
    have h1 : ∫ᵛ x, g x ∂[innerBilinear; D] = ∑ p ∈ P, ∫ᵛ x, g_p p x ∂[innerBilinear; D] := by
      have hg_def : g = fun x => ∑ p ∈ P, g_p p x := by funext x; simp [g]
      rw [hg_def]
      exact VectorMeasure.integral_finsetSum P (fun p _ => hgp_int p ‹_›)
    rw [h1]
    apply Finset.sum_congr rfl
    intro p hp
    exact h_indicator_int p hp
  have hg_supp : Function.support g ⊆ K := by
    intro y hy
    have h : g y ≠ 0 := by simpa [Function.support] using hy
    have h2 : ∃ p ∈ P, y ∈ p := by
      by_contra h3
      push Not at h3
      have h4 : ∀ p ∈ P, g_p p y = 0 := by
        intro p hp
        simp [g_p, h3 p hp]
      have h5 : g y = 0 := by
        have h6 : ∑ p ∈ P, g_p p y = 0 := Finset.sum_eq_zero h4
        simpa [g] using h6
      exact h h5
    rcases h2 with ⟨p, hp, hyp⟩
    exact hP_sub p hp hyp

  -- Smooth approximation of g (global, not yet localized)
  rcases smooth_approx_simpleFunc D g hg_int hg_bound (hε := hε2r_pos) with
    ⟨φ0, hφ0_smooth, hφ0_supp, hφ0_bound, hφ0_L1⟩
  have hφ0_int : D.Integrable φ0 :=
    hφ0_smooth.continuous.integrable_of_hasCompactSupport hφ0_supp

  -- Localize: φ = ψ • φ0
  let φ : E n → E n := fun y => ψ y • φ0 y
  have hφ_smooth_top : ContDiff ℝ (⊤ : ℕ∞) φ := hψ_smooth.smul hφ0_smooth
  have hφ_supp : HasCompactSupport φ := by
    have h : Function.support φ ⊆ Function.support φ0 := by
      intro y hy
      by_contra h2
      have h3 : φ0 y = 0 := by simpa [Function.support] using h2
      have h4 : φ y = 0 := by
        simp [φ, h3] <;> simp
      exact hy (by simpa [Function.support] using h4)
    exact HasCompactSupport.mono hφ0_supp h
  have hφ_suppΩ : Function.support φ ⊆ Ω := by
    intro y hy
    have hψy : ψ y ≠ 0 := by
      by_contra h
      have hφy : φ y = 0 := by simp [φ, h] <;> simp
      exact hy hφy
    have h : y ∈ Function.support ψ := by simpa [Function.support] using hψy
    rw [hψ_supp_eq] at h
    exact h
  have hφ_bound : ∀ y, ‖φ y‖ ≤ 1 := by
    intro y
    have h : ‖φ y‖ = |ψ y| * ‖φ0 y‖ := by rw [norm_smul] <;> rfl
    rw [h]
    have h2 : |ψ y| ≤ 1 := by
      exact abs_le.mpr ⟨by linarith [hψ_nonneg y], hψ_le_one y⟩
    have h3 : ‖φ0 y‖ ≤ 1 := hφ0_bound y
    have h4 : 0 ≤ |ψ y| := abs_nonneg _
    have h5 : 0 ≤ ‖φ0 y‖ := norm_nonneg _
    calc |ψ y| * ‖φ0 y‖ ≤ 1 * ‖φ0 y‖ := by gcongr
      _ = ‖φ0 y‖ := one_mul _
      _ ≤ 1 := h3
  have hφ_int : D.Integrable φ :=
    hφ_smooth_top.continuous.integrable_of_hasCompactSupport hφ_supp

  -- L¹ estimate: ‖φ - g‖ ≤ ‖φ0 - g‖ pointwise
  have h_pointwise : ∀ y, ‖φ y - g y‖ ≤ ‖φ0 y - g y‖ := by
    intro y
    by_cases hy : y ∈ K
    · have hψy : ψ y = 1 := hψ_one y hy
      have h : φ y = φ0 y := by
        simp [φ, hψy] <;> simp
      rw [h]
    · have hgy : g y = 0 := by
        by_contra h
        exact hy (hg_supp (by simpa [Function.support] using h))
      have h : φ y - g y = φ y := by rw [hgy] <;> simp
      rw [h]
      have h2 : ‖φ y‖ ≤ ‖φ0 y‖ := by
        have h3 : ‖φ y‖ = |ψ y| * ‖φ0 y‖ := by rw [norm_smul] <;> rfl
        rw [h3]
        have h4 : |ψ y| ≤ 1 := by
          exact abs_le.mpr ⟨by linarith [hψ_nonneg y], hψ_le_one y⟩
        have h5 : 0 ≤ ‖φ0 y‖ := norm_nonneg _
        exact mul_le_of_le_one_left h5 h4
      have h3 : ‖φ0 y - g y‖ = ‖φ0 y‖ := by rw [hgy] <;> simp
      rw [h3]
      exact h2

  have h_L1 : ∫ y, ‖φ y - g y‖ ∂μ < ε2r := by
    have h_int1 : Integrable (fun y => ‖φ y - g y‖) μ := (hφ_int.sub hg_int).norm
    have h_int2 : Integrable (fun y => ‖φ0 y - g y‖) μ := (hφ0_int.sub hg_int).norm
    have h3 : ∫ y, ‖φ y - g y‖ ∂μ ≤ ∫ y, ‖φ0 y - g y‖ ∂μ :=
      integral_mono h_int1 h_int2 h_pointwise
    exact h3.trans_lt hφ0_L1

  -- Integral difference bound
  have h_sub : D.Integrable (g - φ) := hg_int.sub hφ_int
  have h_bound2 : |∫ᵛ x, (g - φ) x ∂[innerBilinear; D]| ≤ ∫ x, ‖(g - φ) x‖ ∂D.variation :=
    vectorMeasure_integral_abs_bound D (g - φ) h_sub
  have h4 : ∫ x, ‖(g - φ) x‖ ∂D.variation = ∫ y, ‖φ y - g y‖ ∂μ := by
    congr with z
    exact norm_sub_rev (g z) (φ z)
  have h_diff : |∫ᵛ x, (g - φ) x ∂[innerBilinear; D]| < ε2r := by
    rw [h4] at h_bound2
    exact h_bound2.trans_lt h_L1
  have h_eq_int : ∫ᵛ y, g y ∂[innerBilinear; D] - ∫ᵛ y, φ y ∂[innerBilinear; D] =
      ∫ᵛ x, (g - φ) x ∂[innerBilinear; D] := by
    exact (VectorMeasure.integral_fun_sub hg_int hφ_int).symm
  have h_diff' : |∫ᵛ y, g y ∂[innerBilinear; D] - ∫ᵛ y, φ y ∂[innerBilinear; D]| < ε2r := by
    rw [h_eq_int]
    exact h_diff

  -- Integral formula: ∫ φ · dD = ∫_U div φ
  have h_phi_eq : ∫ᵛ y, φ y ∂[innerBilinear; D] = ∫ y in U, divergence φ y :=
    distributionalDerivative_integral_formula U h_perim_finite φ hφ_smooth_top hφ_supp

  -- Bound by perimeterIn
  let θ : TestVectorField :=
    { toFun := φ, smooth := hφ_smooth_top, compact := hφ_supp, bound := hφ_bound }
  let θ' : {Φ : TestVectorField // Function.support Φ.toFun ⊆ Ω} :=
    ⟨θ, hφ_suppΩ⟩
  have h_phi_le : ENNReal.ofReal |∫ᵛ y, φ y ∂[innerBilinear; D]| ≤ perimeterIn U Ω := by
    rw [h_phi_eq]
    exact le_iSup (fun (Φ : {Φ : TestVectorField // Function.support Φ.toFun ⊆ Ω}) =>
      ENNReal.ofReal |∫ x in U, divergence Φ.val.toFun x|) θ'

  have h_phi_abs_le : |∫ᵛ y, φ y ∂[innerBilinear; D]| ≤ (perimeterIn U Ω).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hP_lt.ne).mp h_phi_le
  have h_phi_bound_real : (∫ᵛ y, φ y ∂[innerBilinear; D]) ≤ (perimeterIn U Ω).toReal := by
    calc (∫ᵛ y, φ y ∂[innerBilinear; D])
      ≤ |∫ᵛ y, φ y ∂[innerBilinear; D]| := le_abs_self _
    _ ≤ (perimeterIn U Ω).toReal := h_phi_abs_le

  -- g integral equals sum of ‖D(p)‖
  have hI : ∫ᵛ y, g y ∂[innerBilinear; D] = ∑ p ∈ P, ‖D p‖ := by
    rw [hg_integral]
    apply Finset.sum_congr rfl
    intro p _
    rw [innerBilinear_apply, hv_inner p ‹_›]

  have h_sum_nonneg : ∀ p ∈ P, 0 ≤ ‖D p‖ := by intro p _; positivity
  have h_sum_enorm : ∑ p ∈ P, ‖D p‖ₑ = ENNReal.ofReal (∑ p ∈ P, ‖D p‖) := by
    have h1 : ∀ p ∈ P, ‖D p‖ₑ = ENNReal.ofReal ‖D p‖ := by
      intro p _; simp [enorm] <;> rfl
    rw [Finset.sum_congr rfl h1]
    rw [ENNReal.ofReal_sum_of_nonneg h_sum_nonneg]

  have h_abs_lt : (∫ᵛ y, g y ∂[innerBilinear; D]) - (∫ᵛ y, φ y ∂[innerBilinear; D]) < ε2r := by
    calc (∫ᵛ y, g y ∂[innerBilinear; D]) - (∫ᵛ y, φ y ∂[innerBilinear; D])
      ≤ |(∫ᵛ y, g y ∂[innerBilinear; D]) - (∫ᵛ y, φ y ∂[innerBilinear; D])| := le_abs_self _
    _ < ε2r := h_diff'

  have hI_le : (∑ p ∈ P, ‖D p‖) ≤ (perimeterIn U Ω).toReal + ε2r := by
    rw [hI.symm]
    have h_sum : (∫ᵛ y, g y ∂[innerBilinear; D]) =
        (∫ᵛ y, φ y ∂[innerBilinear; D]) + ((∫ᵛ y, g y ∂[innerBilinear; D]) - (∫ᵛ y, φ y ∂[innerBilinear; D])) := by ring
    rw [h_sum]
    linarith [h_phi_bound_real, h_abs_lt]

  have h_eps2_ne_top : (↑ε2 : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h9 : ENNReal.ofReal (∑ p ∈ P, ‖D p‖) ≤ perimeterIn U Ω + ↑ε2 := by
    have h_eps2_lt_top : (↑ε2 : ENNReal) < ⊤ := ENNReal.coe_lt_top
    rw [ENNReal.ofReal_le_iff_le_toReal (ENNReal.add_lt_top.mpr ⟨hP_lt, h_eps2_lt_top⟩).ne]
    have h10 : (perimeterIn U Ω + ↑ε2).toReal =
        (perimeterIn U Ω).toReal + (↑ε2 : ENNReal).toReal :=
      ENNReal.toReal_add hP_lt.ne h_eps2_ne_top
    rw [h10]
    simpa [ε2r] using hI_le

  have h11 : (↑ε2 : ENNReal) + (↑ε2 : ENNReal) = (↑ε : ENNReal) := by
    have h12 : (↑(ε2 + ε2) : ENNReal) = (↑ε2 : ENNReal) + (↑ε2 : ENNReal) := by
      simpa using NNReal.coe_add ε2 ε2
    have h13 : ε2 + ε2 = ε := by
      apply NNReal.coe_injective
      simp [hε2_def] <;> ring
    rw [←h12, h13]

  calc μ K
    ≤ ∑ p ∈ P, ‖D p‖ₑ + ↑ε2 := hP_sum
    _ = ENNReal.ofReal (∑ p ∈ P, ‖D p‖) + ↑ε2 := by rw [h_sum_enorm]
    _ ≤ perimeterIn U Ω + ↑ε2 + ↑ε2 := by gcongr
    _ = perimeterIn U Ω + (↑ε2 + ↑ε2) := by exact add_assoc (perimeterIn U Ω) (↑ε2) (↑ε2)
    _ = perimeterIn U Ω + ↑ε := by rw [h11]

-- ============================================================================
-- M6: perimeterIn upper bound → perimeterMeasure upper bound
-- ============================================================================

/-- Convert an upper bound on `perimeterIn U (ball x r)` to an upper bound on
`perimeterMeasure U (closedBall x r)` with adjusted constants. -/
lemma upper_bound_perimeterMeasure_from_perimeterIn
    {U : Set (E n)} {x : E n} {C r0 : ℝ} (h_perim_finite : perimeter U < ⊤)
    (hC : 0 < C) (hr0 : 0 < r0)
    (h : ∀ r, 0 < r → r < r0 →
      perimeterIn U (ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1)))
    (hn : 2 ≤ n) :
    ∃ (C' : ℝ) (r0' : ℝ), 0 < C' ∧ 0 < r0' ∧
      ∀ r, 0 < r → r < r0' →
        perimeterMeasure U (closedBall x r) ≤ ENNReal.ofReal (C' * r ^ (n - 1)) := by
  set C' : ℝ := C * (2 : ℝ) ^ (n - 1) with hC'_def
  set r0' : ℝ := r0 / 2 with hr0'_def
  have hC'_pos : 0 < C' := by positivity
  have hr0'_pos : 0 < r0' := by positivity
  refine ⟨C', r0', hC'_pos, hr0'_pos, ?_⟩
  intro r hr hr_lt
  have h2r_lt_r0 : 2 * r < r0 := by
    calc 2 * r < 2 * r0' := by gcongr
      _ = r0 := by
        simp [hr0'_def] <;> ring
  have hr_pos : 0 < r := hr
  have hr_lt_2r : r < 2 * r := by linarith
  have h_main : perimeterMeasure U (closedBall x r) ≤ perimeterIn U (ball x (2 * r)) :=
    perimeterMeasure_closedBall_le_perimeterIn_ball hr_pos hr_lt_2r h_perim_finite
  have h_bound : perimeterIn U (ball x (2 * r)) ≤ ENNReal.ofReal (C * (2 * r) ^ (n - 1)) :=
    h (2 * r) (by positivity) h2r_lt_r0
  have h_final : perimeterMeasure U (closedBall x r) ≤ ENNReal.ofReal (C * (2 * r) ^ (n - 1)) :=
    h_main.trans h_bound
  have h_eq : C * (2 * r) ^ (n - 1) = C' * r ^ (n - 1) := by
    rw [hC'_def]
    ring
  rw [h_eq] at h_final
  exact h_final

end Geometry.StructureTheorem
