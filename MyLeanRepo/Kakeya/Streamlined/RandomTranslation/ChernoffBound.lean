import MyLeanRepo.Kakeya.Streamlined.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic

/-!
# Chernoff-type concentration bound for bounded non-negative random variables

For independent X_i with 0 ≤ X_i ≤ M a.e., for any S > 0:
  μ{Σ X_i ≥ S} ≤ exp(-S/M + C · Σ E[X_i] / M)

where C = e - 1 (any constant works for our application).
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Kakeya.Streamlined.RandomTranslation

/-- For t ∈ [0,1], exp(t) ≤ 1 + t*(e-1). This is the secant line, valid by convexity of exp. -/
lemma exp_linear_bound {t : ℝ} (ht1 : 0 ≤ t) (ht2 : t ≤ 1) :
    Real.exp t ≤ 1 + t * (Real.exp 1 - 1) := by
  have h_cv : ConvexOn ℝ Set.univ Real.exp := convexOn_exp
  have h_main : Real.exp ((1 - t) • (0 : ℝ) + t • (1 : ℝ)) ≤
      (1 - t) • Real.exp 0 + t • Real.exp 1 := by
    exact h_cv.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
      (show 0 ≤ (1 - t) by linarith) (show 0 ≤ t by linarith)
      (show (1 - t) + t = 1 by ring)
  have h_bound : Real.exp t ≤ 1 - t + t * Real.exp 1 := by
    simpa [smul_eq_mul, Real.exp_zero] using h_main
  have h_eq : 1 - t + t * Real.exp 1 = 1 + t * (Real.exp 1 - 1) := by ring
  rw [h_eq] at h_bound
  exact h_bound

/-- For x ∈ [0, M], exp(x/M) ≤ 1 + (x/M)*(e-1). -/
lemma exp_scaled_bound {x M : ℝ} (hx1 : 0 ≤ x) (hx2 : x ≤ M) (hM : 0 < M) :
    Real.exp (x / M) ≤ 1 + (x / M) * (Real.exp 1 - 1) := by
  have hy1 : 0 ≤ x / M := by positivity
  have hy2 : x / M ≤ 1 := by
    calc x / M ≤ M / M := by gcongr
      _ = 1 := by field_simp [hM.ne']
  exact exp_linear_bound hy1 hy2

/-- Helper: on a finite measure space, a bounded measurable real function is integrable. -/
lemma bounded_measurable_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (_hC : 0 ≤ C)
    (h_bound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C) : Integrable f μ := by
  have h1 : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  have h2 : Integrable (fun (_ : Ω) => C) μ := integrable_const C
  exact Integrable.mono' h2 h1 h_bound

/-- Chernoff bound for a sum of independent bounded non-negative random variables.

Given independent X_i with 0 ≤ X_i ≤ M a.e., for any S > 0:
  μ{Σ X_i ≥ S} ≤ exp(-S/M + e · Σ E[X_i] / M)
-/
theorem chernoff_bounded_sum {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i))
    {M : ℝ} (hM_pos : 0 < M)
    (h_bound : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ X i ω ∧ X i ω ≤ M)
    {S : ℝ} (hS_pos : 0 < S) :
    μ.real {ω | S ≤ ∑ i, X i ω} ≤
      Real.exp (-S / M + (Real.exp 1 - 1) * ∑ i : ι, integral μ (X i) / M) := by
  -- Each X_i is integrable
  have h_int : ∀ i, Integrable (X i) μ := by
    intro i
    have h1 : ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ M := by
      filter_upwards [h_bound i] with ω hω
      have h2 : 0 ≤ X i ω := hω.1
      rw [Real.norm_eq_abs, abs_of_nonneg h2] <;> linarith
    exact bounded_measurable_integrable (h_meas i) (by linarith) h1

  -- Define f_i(ω) = exp(X_i(ω)/M)
  let f : ι → Ω → ℝ := fun i ω => Real.exp (X i ω / M)

  have h_f_meas : ∀ i, Measurable (f i) := by
    intro i
    have h1 : Measurable (fun ω => X i ω / M) := (h_meas i).div_const M
    exact Real.measurable_exp.comp h1

  have h_f_bound_all : ∀ᵐ ω ∂μ, ∀ i : ι, 0 ≤ f i ω ∧ f i ω ≤ Real.exp 1 := by
    rw [ae_all_iff]
    intro i
    filter_upwards [h_bound i] with ω hω
    have hxi1 : 0 ≤ X i ω := hω.1
    have hxi2 : X i ω ≤ M := hω.2
    constructor
    · exact Real.exp_pos _ |>.le
    · dsimp only [f]
      have h5 : X i ω / M ≤ 1 := by
        calc X i ω / M ≤ M / M := by gcongr
          _ = 1 := by field_simp [hM_pos.ne']
      exact Real.exp_monotone h5

  have h_f_int : ∀ i, Integrable (f i) μ := by
    intro i
    have h1 : ∀ᵐ ω ∂μ, ‖f i ω‖ ≤ Real.exp 1 := by
      filter_upwards [h_f_bound_all] with ω hω
      have h2 : 0 ≤ f i ω := (hω i).1
      rw [Real.norm_eq_abs, abs_of_nonneg h2] <;> exact (hω i).2
    exact bounded_measurable_integrable (h_f_meas i) (by positivity) h1

  have h_f_aestrong : ∀ i, AEStronglyMeasurable (f i) μ := by
    intro i
    exact (h_f_meas i).aestronglyMeasurable

  -- Bound E[f_i] using linear bound
  have h_exp_bound : ∀ i, integral μ (f i) ≤ 1 + (integral μ (X i) / M) * (Real.exp 1 - 1) := by
    intro i
    let g : Ω → ℝ := fun ω => 1 + (X i ω / M) * (Real.exp 1 - 1)
    have h1 : ∀ᵐ ω ∂μ, f i ω ≤ g ω := by
      filter_upwards [h_bound i] with ω hω
      exact exp_scaled_bound hω.1 hω.2 hM_pos
    have hg_meas : Measurable g := by
      dsimp only [g]
      exact measurable_const.add ((h_meas i).div_const M |>.mul_const (Real.exp 1 - 1))
    have hg_int : Integrable g μ := by
      have h_e_sub : 0 ≤ Real.exp 1 - 1 := by
        have h : (1 : ℝ) < Real.exp 1 := by
          have h0 : Real.exp 0 < Real.exp 1 := Real.exp_strictMono (by norm_num)
          simpa using h0
        linarith
      have h1 : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ 1 + (Real.exp 1 - 1) := by
        filter_upwards [h_bound i] with ω hω
        have h2 : 0 ≤ X i ω := hω.1
        have h3 : X i ω ≤ M := hω.2
        have h4 : 0 ≤ g ω := by
          dsimp only [g]
          have h5 : 0 ≤ (X i ω / M) * (Real.exp 1 - 1) := mul_nonneg (by positivity) h_e_sub
          linarith
        have h5 : g ω ≤ 1 + (Real.exp 1 - 1) := by
          dsimp only [g]
          have h6 : X i ω / M ≤ 1 := by
            calc X i ω / M ≤ M / M := by gcongr
              _ = 1 := by field_simp [hM_pos.ne']
          nlinarith [h_e_sub]
        rw [Real.norm_eq_abs, abs_of_nonneg h4]
        exact h5
      exact bounded_measurable_integrable hg_meas (by linarith [h_e_sub]) h1
    have h2 : integral μ (f i) ≤ integral μ g :=
      integral_mono_ae (h_f_int i) hg_int h1
    have h_int1 : Integrable (fun ω : Ω => (X i ω / M) * (Real.exp 1 - 1)) μ := by
      have h_eq : (fun ω : Ω => (X i ω / M) * (Real.exp 1 - 1)) = fun ω : Ω => (Real.exp 1 - 1) • (M⁻¹ • X i ω) := by
        funext ω; simp [smul_eq_mul, div_eq_mul_inv]; ring
      rw [h_eq]
      exact Integrable.smul (Real.exp 1 - 1) (Integrable.smul M⁻¹ (h_int i))
    have h3 : integral μ g = 1 + (integral μ (X i) / M) * (Real.exp 1 - 1) := by
      dsimp only [g]
      rw [integral_add (integrable_const (1 : ℝ)) h_int1]
      have h4 : integral μ (fun ω : Ω => (X i ω / M) * (Real.exp 1 - 1)) =
          (integral μ (X i) / M) * (Real.exp 1 - 1) := by
        have h5 : integral μ (fun ω : Ω => (X i ω / M) * (Real.exp 1 - 1)) =
            (Real.exp 1 - 1) * integral μ (fun ω : Ω => X i ω / M) := by
          have h_eq1 : (fun ω : Ω => (X i ω / M) * (Real.exp 1 - 1)) = fun ω : Ω => (Real.exp 1 - 1) • (X i ω / M) := by
            funext ω; ring
          rw [h_eq1, integral_smul] <;> rfl
        rw [h5]
        have h6 : integral μ (fun ω : Ω => X i ω / M) = M⁻¹ * integral μ (X i) := by
          have h_eq2 : (fun ω : Ω => X i ω / M) = fun ω : Ω => M⁻¹ • X i ω := by
            funext ω; simp [div_eq_mul_inv, smul_eq_mul]; ring
          rw [h_eq2, integral_smul] <;> ring
        rw [h6] <;> ring
      rw [h4, integral_const]
      simp
    rw [h3] at h2
    exact h2

  -- Product F(ω) = ∏ f_i(ω) = exp(Σ X_i(ω) / M)
  let F : Ω → ℝ := fun ω => ∏ i : ι, f i ω

  have hF_meas : Measurable F :=
    Finset.measurable_prod _ (fun i _ => h_f_meas i)

  let C : ℝ := (Real.exp 1) ^ Fintype.card ι

  have hF_bound : ∀ᵐ ω ∂μ, 0 ≤ F ω ∧ F ω ≤ C := by
    filter_upwards [h_f_bound_all] with ω hω
    constructor
    · apply Finset.prod_nonneg
      intro i hi
      exact (hω i).1
    · have h2 : ∀ i ∈ (Finset.univ : Finset ι), f i ω ≤ Real.exp 1 := by
        intro i hi
        exact (hω i).2
      calc F ω
        = ∏ i ∈ (Finset.univ : Finset ι), f i ω := by rfl
      _ ≤ ∏ i ∈ (Finset.univ : Finset ι), Real.exp 1 := by
        apply Finset.prod_le_prod
        · intro i hi
          exact (hω i).1
        · intro i hi
          exact h2 i hi
      _ = C := by
        simp [C, Finset.prod_const]

  have hF_norm : ∀ᵐ ω ∂μ, ‖F ω‖ ≤ C := by
    filter_upwards [hF_bound] with ω hω
    have h2 : 0 ≤ F ω := hω.1
    rw [Real.norm_eq_abs, abs_of_nonneg h2]
    exact hω.2

  have hF_aestrong : AEStronglyMeasurable F μ :=
    Finset.aestronglyMeasurable_fun_prod Finset.univ fun i _ =>
      h_f_aestrong i
  have hF_int : Integrable F μ := by
    have h2 : Integrable (fun (_ : Ω) => C) μ := integrable_const C
    exact Integrable.mono' h2 hF_aestrong hF_norm

  have hF_eq : ∀ ω, F ω = Real.exp ((∑ i : ι, X i ω) / M) := by
    intro ω
    dsimp only [F, f]
    have h4 : ∏ i : ι, Real.exp (X i ω / M) = Real.exp (∑ i : ι, X i ω / M) := by
      rw [← Real.exp_sum] <;> rfl
    rw [h4]
    have h5 : ∑ i : ι, X i ω / M = (∑ i : ι, X i ω) / M := by
      rw [Finset.sum_div] <;> rfl
    rw [h5]

  -- Product formula for independent functions
  let g_map : ι → ℝ → ℝ := fun i x => Real.exp (x / M)
  have hg_map_meas : ∀ i, Measurable (g_map i) := by
    intro i; fun_prop
  have h_indep_f : iIndepFun f μ := h_indep.comp g_map hg_map_meas
  have h_prod : integral μ F = ∏ i : ι, integral μ (f i) := by
    rw [show F = fun ω => ∏ i : ι, f i ω from rfl]
    exact h_indep_f.integral_fun_prod_eq_prod_integral h_f_aestrong

  -- Markov inequality
  have h_markov : (Real.exp (S / M)) * μ.real {ω | S ≤ ∑ i, X i ω} ≤ integral μ F := by
    have h4 : ∀ᵐ ω ∂μ, 0 ≤ F ω := by
      filter_upwards [hF_bound] with ω hω
      exact hω.1
    have h6 := mul_meas_ge_le_integral_of_nonneg h4 hF_int (Real.exp (S / M))
    have h7 : ∀ ω, (Real.exp (S / M) ≤ F ω) ↔ (S ≤ ∑ i, X i ω) := by
      intro ω
      have h8 : F ω = Real.exp ((∑ i, X i ω) / M) := hF_eq ω
      rw [h8]
      constructor
      · intro h
        have h10 : S / M ≤ (∑ i, X i ω) / M := Real.exp_le_exp.mp h
        have h11 : S ≤ ∑ i, X i ω := by
          calc S
            = (S / M) * M := by field_simp [hM_pos.ne'] <;> ring
          _ ≤ ((∑ i, X i ω) / M) * M := by gcongr
          _ = ∑ i, X i ω := by field_simp [hM_pos.ne'] <;> ring
        exact h11
      · intro h
        have h10 : S / M ≤ (∑ i, X i ω) / M := by gcongr
        exact Real.exp_monotone h10
    have h10 : {ω | Real.exp (S / M) ≤ F ω} = {ω | S ≤ ∑ i, X i ω} := by
      ext ω; exact h7 ω
    rw [h10] at h6
    exact h6

  have h_pos_exp : 0 < Real.exp (S / M) := Real.exp_pos _
  have h_div1 : (Real.exp (S / M) * μ.real {ω | S ≤ ∑ i, X i ω}) / Real.exp (S / M) ≤ (integral μ F) / Real.exp (S / M) :=
    div_le_div_of_nonneg_right h_markov (by positivity)
  have h_div2 : (Real.exp (S / M) * μ.real {ω | S ≤ ∑ i, X i ω}) / Real.exp (S / M) = μ.real {ω | S ≤ ∑ i, X i ω} := by
    field_simp [h_pos_exp.ne'] <;> ring
  have h_div : μ.real {ω | S ≤ ∑ i, X i ω} ≤ (integral μ F) / Real.exp (S / M) := by
    rw [h_div2] at h_div1
    exact h_div1
  have h9 : (integral μ F) / Real.exp (S / M) = (integral μ F) * Real.exp (-S / M) := by
    have h10 : -S / M = -(S / M) := by ring
    have h11 : Real.exp (-S / M) = (Real.exp (S / M))⁻¹ := by
      rw [h10]
      exact Real.exp_neg (S / M)
    rw [h11] <;> ring
  have h7 : μ.real {ω | S ≤ ∑ i, X i ω} ≤ (integral μ F) * Real.exp (-S / M) := by
    rw [h9] at h_div
    exact h_div

  -- Bound product using ∏(1 + y_i) ≤ exp(Σ y_i)
  let y : ι → ℝ := fun i => (integral μ (X i) / M) * (Real.exp 1 - 1)
  have h_e_sub : 0 ≤ Real.exp 1 - 1 := by
    have h : (1 : ℝ) < Real.exp 1 := by
      have h0 : Real.exp 0 < Real.exp 1 := Real.exp_strictMono (by norm_num)
      simpa using h0
    linarith
  have h_y_nonneg : ∀ i, 0 ≤ y i := by
    intro i
    have h_i_nonneg : 0 ≤ integral μ (X i) := by
      have h : ∀ᵐ ω ∂μ, 0 ≤ X i ω := by
        filter_upwards [h_bound i] with ω hω; exact hω.1
      exact integral_nonneg_of_ae h
    dsimp only [y]
    have h : 0 ≤ (integral μ (X i) / M) * (Real.exp 1 - 1) :=
      mul_nonneg (by positivity) h_e_sub
    exact h
  have h9 : ∏ i : ι, (1 + y i) ≤ Real.exp (∑ i : ι, y i) :=
    Real.prod_one_add_le_exp_sum Finset.univ h_y_nonneg
  have h_sum : ∑ i : ι, y i = (Real.exp 1 - 1) * ∑ i : ι, integral μ (X i) / M := by
    dsimp only [y]
    rw [← Finset.sum_mul]
    <;> ring
  have h10 : (∏ i : ι, integral μ (f i)) * Real.exp (-S / M) ≤
      Real.exp (-S / M + (Real.exp 1 - 1) * ∑ i : ι, integral μ (X i) / M) := by
    have h_nonneg2 : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ integral μ (f i) := by
      intro i hi
      have h_nonneg : ∀ᵐ ω ∂μ, 0 ≤ f i ω := by
        filter_upwards [h_f_bound_all] with ω hω; exact (hω i).1
      exact integral_nonneg_of_ae h_nonneg
    have h_le2 : ∀ i ∈ (Finset.univ : Finset ι), integral μ (f i) ≤ 1 + y i := by
      intro i hi
      exact h_exp_bound i
    have h_prod_le : ∏ i : ι, integral μ (f i) ≤ ∏ i : ι, (1 + y i) :=
      Finset.prod_le_prod h_nonneg2 h_le2
    have h_step1 : (∏ i : ι, integral μ (f i)) * Real.exp (-S / M) ≤
        (∏ i : ι, (1 + y i)) * Real.exp (-S / M) :=
      mul_le_mul_of_nonneg_right h_prod_le (by positivity)
    have h_step2 : (∏ i : ι, (1 + y i)) * Real.exp (-S / M) ≤
        Real.exp (∑ i : ι, y i) * Real.exp (-S / M) :=
      mul_le_mul_of_nonneg_right h9 (by positivity)
    have h_step3 : Real.exp (∑ i : ι, y i) * Real.exp (-S / M) =
        Real.exp (-S / M + (Real.exp 1 - 1) * ∑ i : ι, integral μ (X i) / M) := by
      have h_eq : Real.exp (∑ i : ι, y i) * Real.exp (-S / M) = Real.exp ((∑ i : ι, y i) + (-S / M)) := by
        rw [← Real.exp_add]
      rw [h_eq]
      have h2 : (∑ i : ι, y i) + (-S / M) = -S / M + (Real.exp 1 - 1) * ∑ i : ι, integral μ (X i) / M := by
        rw [h_sum, add_comm] <;> ring
      rw [h2]
    rw [h_step3] at h_step2
    exact h_step1.trans h_step2

  have h_final1 : μ.real {ω | S ≤ ∑ i, X i ω} ≤ (∏ i : ι, integral μ (f i)) * Real.exp (-S / M) := by
    calc μ.real {ω | S ≤ ∑ i, X i ω}
      ≤ (integral μ F) * Real.exp (-S / M) := h7
    _ = (∏ i : ι, integral μ (f i)) * Real.exp (-S / M) := by rw [h_prod]
  exact h_final1.trans h10

end Kakeya.Streamlined.RandomTranslation
