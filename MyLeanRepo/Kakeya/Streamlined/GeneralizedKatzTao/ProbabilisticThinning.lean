import MyLeanRepo.Kakeya.Streamlined.Basic
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.Estimates
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.ChernoffBound
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleBounds
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Probabilistic thinning infrastructure

Generic Bernoulli selection on `Fin n → Bool` with product measure,
coordinate independence, expectations, and Chernoff bounds.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open Kakeya.Streamlined.RandomTranslation
open scoped unitInterval

namespace Kakeya.Streamlined.ProbabilisticThinning

/-! ### Generic Bernoulli selection infrastructure -/

variable {n : ℕ} {pI : unitInterval}

/-- Product Bernoulli measure on Fin n → Bool. -/
def selectionMeasure (n : ℕ) (pI : unitInterval) :
    Measure (Fin n → Bool) :=
  Measure.pi fun (_ : Fin n) => ProbabilityTheory.bernoulliMeasure true false pI

/-- Coordinate indicator: 1 if selected, 0 otherwise. -/
def coordIndicator (i : Fin n) (v : Fin n → Bool) : ℝ :=
  if v i then 1 else 0

/-- Each coordinate indicator is measurable. -/
lemma coordIndicator_measurable (i : Fin n) :
    Measurable (coordIndicator i) := by
  exact Measurable.of_discrete

/-- Each coordinate indicator is bounded in [0, 1]. -/
lemma coordIndicator_bound (i : Fin n) (v : Fin n → Bool) :
    0 ≤ coordIndicator i v ∧ coordIndicator i v ≤ 1 := by
  dsimp only [coordIndicator]
  split_ifs <;> norm_num

/-- Coordinate indicators are independent under the product measure. -/
lemma coordIndicators_independent (n : ℕ) (pI : unitInterval) :
    iIndepFun (fun i (v : Fin n → Bool) => coordIndicator i v)
      (selectionMeasure n pI) := by
  let X : Fin n → Bool → ℝ := fun _ b => if b then 1 else 0
  have hX_meas : ∀ i, Measurable (X i) := by
    intro i
    exact Real.measurable_of_measurable_exp fun ⦃t⦄ _ => trivial
  have h_ae : ∀ i, AEMeasurable (X i) (ProbabilityTheory.bernoulliMeasure true false pI) := by
    intro i
    exact (hX_meas i).aemeasurable
  have h_main : iIndepFun (fun i v => X i (v i)) (selectionMeasure n pI) :=
    iIndepFun_pi h_ae
  have h_eq : (fun i (v : Fin n → Bool) => coordIndicator i v) =
      (fun i v => X i (v i)) := by
    funext i v
    rfl
  rw [h_eq]
  exact h_main

/-- Expected value of a single coordinate indicator equals pI. -/
lemma coordIndicator_expectation (n : ℕ) (pI : unitInterval) (i : Fin n) :
    integral (selectionMeasure n pI) (coordIndicator i) = (pI : ℝ) := by
  let f : Bool → ℝ := fun b => if b then 1 else 0
  let μi := ProbabilityTheory.bernoulliMeasure true false pI
  let μs : Fin n → Measure Bool := fun _ => μi
  let φ : (Fin n → Bool) → Bool := Function.eval i
  have hφ_meas : Measurable φ := measurable_pi_apply i
  have h_map_raw : (selectionMeasure n pI).map φ =
      (∏ j ∈ Finset.univ.erase i, (μs j) Set.univ) • μs i := by
    dsimp only [selectionMeasure]
    exact Measure.pi_map_eval μs i
  have h_prod : (∏ j ∈ Finset.univ.erase i, (μs j) Set.univ) = 1 := by
    apply Finset.prod_eq_one
    intro j _
    exact measure_univ
  have h_map : (selectionMeasure n pI).map φ = μi := by
    rw [h_map_raw, h_prod, one_smul]
  have h_eq1 : coordIndicator i = f ∘ φ := by
    funext v
    rfl
  have hfm : AEStronglyMeasurable f μi :=
    AEStronglyMeasurable.of_discrete
  have hfm' : AEStronglyMeasurable f ((selectionMeasure n pI).map φ) := by
    rw [h_map]
    exact hfm
  have h_integral_map : integral ((selectionMeasure n pI).map φ) f =
      integral (selectionMeasure n pI) (f ∘ φ) :=
    integral_map hφ_meas.aemeasurable hfm'
  have h_integral : integral μi f = integral (selectionMeasure n pI) (f ∘ φ) := by
    rw [← h_map]
    exact h_integral_map
  calc integral (selectionMeasure n pI) (coordIndicator i)
    = integral (selectionMeasure n pI) (f ∘ φ) := by rw [h_eq1]
  _ = integral μi f := h_integral.symm
  _ = (pI : ℝ) := by
    rw [ProbabilityTheory.integral_bernoulliMeasure true false pI f]
    simp [f] <;> norm_num

/-- Chernoff bound on the number of selected indices. -/
lemma chernoff_selection_count (n : ℕ) (pI : unitInterval)
    {S : ℝ} (hS_pos : 0 < S) :
    (selectionMeasure n pI).real
      {v : Fin n → Bool | S ≤ ∑ i : Fin n, coordIndicator i v} ≤
      Real.exp (-S + (Real.exp 1 - 1) * (n : ℝ) * (pI : ℝ)) := by
  letI h_prob : IsProbabilityMeasure (selectionMeasure n pI) := by
    dsimp only [selectionMeasure]
    haveI : ∀ (j : Fin n), IsProbabilityMeasure (ProbabilityTheory.bernoulliMeasure true false pI) :=
      fun _ => by infer_instance
    exact Measure.pi.instIsProbabilityMeasure fun x => Ber(true, false, pI)
  have h_indep := coordIndicators_independent n pI
  have h_meas : ∀ i : Fin n, Measurable (coordIndicator i) :=
    coordIndicator_measurable
  have h_bound : ∀ i : Fin n, ∀ᵐ (v : Fin n → Bool) ∂(selectionMeasure n pI),
      0 ≤ coordIndicator i v ∧ coordIndicator i v ≤ 1 := by
    intro i
    filter_upwards with v
    exact coordIndicator_bound i v
  have h_sum_expect : ∑ i : Fin n, integral (selectionMeasure n pI) (coordIndicator i) =
      (n : ℝ) * (pI : ℝ) := by
    have h : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        integral (selectionMeasure n pI) (coordIndicator i) = (pI : ℝ) := by
      intro i _
      exact coordIndicator_expectation n pI i
    rw [Finset.sum_congr rfl h]
    simp [Finset.sum_const]
  have h_main := chernoff_bounded_sum (M := 1)
    (h_indep := h_indep) (h_meas := h_meas) (hM_pos := by norm_num)
    (h_bound := h_bound) (hS_pos := hS_pos)
  have h_sum_div1 : ∑ i : Fin n, (integral (selectionMeasure n pI) (coordIndicator i) / 1) =
      ∑ i : Fin n, integral (selectionMeasure n pI) (coordIndicator i) := by
    simp
  rw [h_sum_div1, h_sum_expect] at h_main
  simpa [div_one, mul_assoc] using h_main

/-! ### Volume-weighted indicators for density control -/

/-- Volume-weighted coordinate indicator. -/
def coordVolumeIndicator (Vreal : ℝ) (i : Fin n) (v : Fin n → Bool) : ℝ :=
  Vreal * coordIndicator i v

/-- Volume-weighted indicator is measurable. -/
lemma coordVolumeIndicator_measurable (Vreal : ℝ) (i : Fin n) :
    Measurable (coordVolumeIndicator Vreal i) :=
  (coordIndicator_measurable i).const_mul Vreal

/-- Volume-weighted indicators are independent. -/
lemma coordVolumeIndicators_independent (Vreal : ℝ) (n : ℕ) (pI : unitInterval) :
    iIndepFun (fun i (v : Fin n → Bool) => coordVolumeIndicator Vreal i v)
      (selectionMeasure n pI) := by
  let g : Fin n → ℝ → ℝ := fun _ x => Vreal * x
  have hg_meas : ∀ i, Measurable (g i) := by
    intro i
    exact measurable_id.const_mul Vreal
  exact (coordIndicators_independent n pI).comp g hg_meas

/-- Expected value of volume-weighted indicator. -/
lemma coordVolumeIndicator_expectation (Vreal : ℝ) (n : ℕ) (pI : unitInterval) (i : Fin n) :
    integral (selectionMeasure n pI) (coordVolumeIndicator Vreal i) =
      (pI : ℝ) * Vreal := by
  letI h_prob : IsProbabilityMeasure (selectionMeasure n pI) := by
    dsimp only [selectionMeasure]
    haveI : ∀ (j : Fin n), IsProbabilityMeasure (ProbabilityTheory.bernoulliMeasure true false pI) :=
      fun _ => by infer_instance
    exact Measure.pi.instIsProbabilityMeasure fun x => Ber(true, false, pI)
  have h_smul : (coordVolumeIndicator Vreal i) = Vreal • (coordIndicator i) := by
    funext v
    simp [coordVolumeIndicator, smul_eq_mul]
    <;> ring
  rw [h_smul]
  have h_int : Integrable (coordIndicator i) (selectionMeasure n pI) := by
    have h1 : ∀ᵐ v ∂(selectionMeasure n pI), ‖coordIndicator i v‖ ≤ 1 := by
      filter_upwards with v
      have h2 := coordIndicator_bound i v
      rw [Real.norm_eq_abs, abs_of_nonneg h2.1]
      exact h2.2
    exact bounded_measurable_integrable (coordIndicator_measurable i) (by norm_num) h1
  letI h_int' : Integrable (coordIndicator i) (selectionMeasure n pI) := h_int
  have h_mul : integral (selectionMeasure n pI) (Vreal • coordIndicator i) =
      Vreal * integral (selectionMeasure n pI) (coordIndicator i) := by
    have h : integral (selectionMeasure n pI) (Vreal • coordIndicator i) =
        Vreal • integral (selectionMeasure n pI) (coordIndicator i) :=
      integral_smul (μ := selectionMeasure n pI) (c := Vreal) (f := coordIndicator i)
    simpa [smul_eq_mul] using h
  rw [h_mul, coordIndicator_expectation n pI i]
  <;> ring

/-- Selected volume mass in a finset of indices. -/
def selectedVolumeMass (Vreal : ℝ) (s : Finset (Fin n)) (v : Fin n → Bool) : ℝ :=
  ∑ i ∈ s, coordVolumeIndicator Vreal i v

/-- Chernoff bound for selected volume mass in a set of indices. -/
lemma chernoff_selectedVolumeMass (n : ℕ) (pI : unitInterval)
    (Vreal : ℝ) (hVreal_pos : 0 < Vreal)
    (s : Finset (Fin n)) {S : ℝ} (hS_pos : 0 < S) :
    (selectionMeasure n pI).real
      {v | S ≤ selectedVolumeMass Vreal s v} ≤
      Real.exp (-S / Vreal + (Real.exp 1 - 1) * (pI : ℝ) * (s.card : ℝ)) := by
  letI h_prob : IsProbabilityMeasure (selectionMeasure n pI) := by
    dsimp only [selectionMeasure]
    haveI : ∀ (j : Fin n), IsProbabilityMeasure (ProbabilityTheory.bernoulliMeasure true false pI) :=
      fun _ => by infer_instance
    exact Measure.pi.instIsProbabilityMeasure fun x => Ber(true, false, pI)
  let g : Fin n → ℝ → ℝ := fun i x => if i ∈ s then x else 0
  let Y : Fin n → (Fin n → Bool) → ℝ := fun i v =>
    g i (coordVolumeIndicator Vreal i v)
  have hg_meas : ∀ i, Measurable (g i) := by
    intro i
    by_cases h : i ∈ s
    · simp [g, h]
      exact measurable_id
    · have hgi : g i = fun (_ : ℝ) => (0 : ℝ) := by
        funext x
        simp [g, h]
      rw [hgi]
      exact measurable_const
  have h_indep : iIndepFun Y (selectionMeasure n pI) :=
    (coordVolumeIndicators_independent Vreal n pI).comp g hg_meas
  have h_meas : ∀ i, Measurable (Y i) := by
    intro i
    exact (hg_meas i).comp (coordVolumeIndicator_measurable Vreal i)
  have h_bound : ∀ i, ∀ᵐ v ∂(selectionMeasure n pI),
      0 ≤ Y i v ∧ Y i v ≤ Vreal := by
    intro i
    filter_upwards with v
    dsimp only [Y, g]
    by_cases h : i ∈ s
    · rw [if_pos h]
      have h_b1 : 0 ≤ coordIndicator i v := (coordIndicator_bound i v).1
      have h_b2 : coordIndicator i v ≤ 1 := (coordIndicator_bound i v).2
      exact ⟨mul_nonneg hVreal_pos.le h_b1,
        calc Vreal * coordIndicator i v ≤ Vreal * 1 := by gcongr
          _ = Vreal := by ring⟩
    · rw [if_neg h]
      <;> simp [hVreal_pos.le]
  have h_sum_eq : ∀ v, ∑ i : Fin n, Y i v = selectedVolumeMass Vreal s v := by
    intro v
    dsimp only [Y, g, selectedVolumeMass]
    rw [Finset.sum_ite]
    <;> simp
  have h_expect : ∀ i, integral (selectionMeasure n pI) (Y i) =
      if i ∈ s then (pI : ℝ) * Vreal else 0 := by
    intro i
    by_cases h : i ∈ s
    · have hY : Y i = coordVolumeIndicator Vreal i := by
        funext v
        simp [Y, g, h]
      rw [hY, if_pos h]
      exact coordVolumeIndicator_expectation Vreal n pI i
    · have hY : Y i = fun _ => 0 := by
        funext v
        simp [Y, g, h]
      rw [hY, if_neg h]
      simp
  have h_sum : ∑ i : Fin n, integral (selectionMeasure n pI) (Y i) =
      (pI : ℝ) * Vreal * (s.card : ℝ) := by
    have h3 : ∑ i : Fin n, integral (selectionMeasure n pI) (Y i) =
        ∑ i ∈ s, (pI : ℝ) * Vreal := by
      rw [Finset.sum_congr rfl (fun i _ => h_expect i)]
      rw [Finset.sum_ite]
      <;> simp
    rw [h3]
    simp [Finset.sum_const]
    <;> ring
  have h_main := chernoff_bounded_sum (M := Vreal)
    (h_indep := h_indep) (h_meas := h_meas) (hM_pos := hVreal_pos)
    (h_bound := h_bound) (hS_pos := hS_pos)
  have h_set : {ω | S ≤ ∑ i, Y i ω} = {v | S ≤ selectedVolumeMass Vreal s v} := by
    ext v
    simp only [Set.mem_setOf_eq, h_sum_eq]
  rw [h_set] at h_main
  have h_sum_div : ∑ i : Fin n, (integral (selectionMeasure n pI) (Y i) / Vreal) =
      (∑ i : Fin n, integral (selectionMeasure n pI) (Y i)) / Vreal := by
    rw [Finset.sum_div]
  have h_final : (selectionMeasure n pI).real {v | S ≤ selectedVolumeMass Vreal s v} ≤
      Real.exp (-S / Vreal + (Real.exp 1 - 1) * (pI : ℝ) * (s.card : ℝ)) := by
    have h9 : (selectionMeasure n pI).real {v | S ≤ selectedVolumeMass Vreal s v} ≤
        Real.exp (-S / Vreal + (Real.exp 1 - 1) * ∑ i : Fin n, (integral (selectionMeasure n pI) (Y i) / Vreal)) := h_main
    rw [h_sum_div] at h9
    rw [h_sum] at h9
    have h10 : Real.exp (-S / Vreal + (Real.exp 1 - 1) * (((pI : ℝ) * Vreal * (s.card : ℝ)) / Vreal)) =
        Real.exp (-S / Vreal + (Real.exp 1 - 1) * (pI : ℝ) * (s.card : ℝ)) := by
      congr 1
      field_simp [hVreal_pos.ne'] <;> ring
    rw [h10] at h9
    exact h9
  exact h_final

/-! ### Paley-Zygmund lower bound -/

/-- Paley-Zygmund lower bound via AM-GM inequality.

If `0 ≤ X`, `E[X] = μ_val > 0`, and `E[X^2] ≤ V * μ_val + μ_val^2`, then
`P(X ≥ μ_val/2) ≥ μ_val / (4 * (V + μ_val))`. -/
lemma paley_zygmund_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (V : ℝ) (hV_nonneg : 0 ≤ V)
    {X : Ω → ℝ} (hX_meas : Measurable X)
    (hX_nonneg : ∀ ω, 0 ≤ X ω)
    (h_int : Integrable X μ)
    (h_int2 : Integrable (fun ω => X ω^2) μ)
    (μ_val : ℝ) (hμ : integral μ X = μ_val) (hμ_pos : 0 < μ_val)
    (E2_bound : integral μ (fun ω => X ω^2) ≤ V * μ_val + μ_val^2) :
    μ.real {ω | μ_val / 2 ≤ X ω} ≥ μ_val / (4 * (V + μ_val)) := by
  let A : Set Ω := {ω | μ_val / 2 ≤ X ω}
  have hA_meas : MeasurableSet A := hX_meas measurableSet_Ici
  let X_A : Ω → ℝ := Set.indicator A X
  let one_A : Ω → ℝ := Set.indicator A (fun _ => (1 : ℝ))
  set EA := integral μ X_A with hEA_def
  set E2 := integral μ (fun ω => X ω^2) with hE2_def
  set PA := μ.real A with hPA_def

  have h_int_A : Integrable X_A μ := h_int.indicator hA_meas
  have h_int_one : Integrable one_A μ := (integrable_const (1 : ℝ)).indicator hA_meas

  -- E[X_A] ≥ μ_val/2
  have h1 : ∀ ω, X ω ≤ μ_val / 2 + X_A ω := by
    intro ω
    by_cases h : ω ∈ A
    · simp [X_A, Set.indicator, h] <;> linarith
    · have h' : X ω < μ_val / 2 := by simpa [A] using h
      simp [X_A, Set.indicator, h] <;> linarith
  have h1ae : ∀ᵐ ω ∂μ, X ω ≤ μ_val / 2 + X_A ω := by
    filter_upwards with ω
    exact h1 ω
  have h_int_rhs : Integrable (fun ω : Ω => μ_val / 2 + X_A ω) μ :=
    (integrable_const (μ_val / 2)).add h_int_A
  have hE_XA : EA ≥ μ_val / 2 := by
    have h : integral μ X ≤ integral μ (fun ω : Ω => μ_val / 2 + X_A ω) :=
      integral_mono_ae h_int h_int_rhs h1ae
    have h2 : integral μ (fun ω : Ω => μ_val / 2 + X_A ω) = μ_val / 2 + EA := by
      rw [integral_add (integrable_const _) h_int_A]
      <;> simp [hEA_def, integral_const] <;> ring
    rw [h2] at h
    rw [hμ] at h
    <;> linarith

  -- E[X_A^2] ≤ E[X^2]
  have hXA2_le : ∀ ω, (X_A ω)^2 ≤ (X ω)^2 := by
    intro ω
    by_cases h : ω ∈ A
    · simp [X_A, Set.indicator, h] <;> nlinarith [hX_nonneg ω]
    · simp [X_A, Set.indicator, h] <;> nlinarith [hX_nonneg ω]
  have hXA2_meas : Measurable (fun ω : Ω => (X_A ω)^2) := by fun_prop
  have hXA2_bound : ∀ᵐ ω ∂μ, ‖(X_A ω)^2‖ ≤ (X ω)^2 := by
    filter_upwards with ω
    have h : (X_A ω)^2 ≤ (X ω)^2 := hXA2_le ω
    have h1 : 0 ≤ (X_A ω)^2 := by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg h1] using h
  have h_int_XA2 : Integrable (fun ω : Ω => (X_A ω)^2) μ :=
    h_int2.mono' hXA2_meas.aestronglyMeasurable hXA2_bound
  have hE_XA2_le : integral μ (fun ω : Ω => (X_A ω)^2) ≤ E2 :=
    integral_mono h_int_XA2 h_int2 hXA2_le

  -- X_A * one_A = X_A and one_A^2 = one_A
  have h_mul : ∀ ω, X_A ω * one_A ω = X_A ω := by
    intro ω
    by_cases h : ω ∈ A <;> simp [X_A, one_A, Set.indicator, h] <;> ring
  have h_sq : ∀ ω, (one_A ω)^2 = one_A ω := by
    intro ω
    by_cases h : ω ∈ A <;> simp [one_A, Set.indicator, h] <;> ring

  -- E[one_A] = PA
  have hE_one : integral μ one_A = PA := by
    simp [one_A, Set.indicator, integral_indicator, hA_meas, integral_const, PA] <;> rfl

  -- AM-GM: 2ab ≤ εa^2 + b^2/ε for ε > 0
  have h_amgm : ∀ (a b ε : ℝ), 0 < ε → 2 * a * b ≤ ε * a^2 + b^2 / ε := by
    intro a b ε hε
    have h : (ε * a - b)^2 ≥ 0 := by positivity
    have h2 : 2 * ε * a * b ≤ ε^2 * a^2 + b^2 := by nlinarith
    calc 2 * a * b
      = (2 * ε * a * b) / ε := by field_simp [hε.ne'] <;> ring
    _ ≤ (ε^2 * a^2 + b^2) / ε := by gcongr
    _ = ε * a^2 + b^2 / ε := by field_simp [hε.ne'] <;> ring

  -- EA^2 ≤ E[X_A^2] * PA via AM-GM
  set EA2 := integral μ (fun ω : Ω => (X_A ω)^2) with hEA2_def
  have hEA_pos : 0 < EA := by linarith [hE_XA, hμ_pos]
  have hEA2_pos : 0 < EA2 := by
    by_contra h
    have h0 : EA2 ≤ 0 := by linarith
    have h_nonneg : 0 ≤ EA2 := integral_nonneg (fun ω => sq_nonneg (X_A ω))
    have h_eq : EA2 = 0 := by linarith
    have h'_ae : 0 ≤ᵐ[μ] (fun ω : Ω => (X_A ω)^2) := by
      filter_upwards with ω; exact sq_nonneg _
    have h_ae : (fun ω : Ω => (X_A ω)^2) =ᵐ[μ] fun _ => (0 : ℝ) :=
      (integral_eq_zero_iff_of_nonneg_ae h'_ae h_int_XA2).mp h_eq
    have h_ae2 : ∀ᵐ ω ∂μ, X_A ω = 0 := h_ae.mono (fun ω h => sq_eq_zero_iff.mp h)
    have h3 : integral μ X_A = integral μ (fun (_ : Ω) => (0 : ℝ)) := integral_congr_ae h_ae2
    have h4 : integral μ (fun (_ : Ω) => (0 : ℝ)) = 0 := by simp
    have h5 : integral μ X_A = 0 := by rw [h3, h4]
    have h_EA0 : EA = 0 := by simpa [hEA_def] using h5
    linarith [hEA_pos, h_EA0]
  set ε : ℝ := EA / EA2 with hε_def
  have hε_pos : 0 < ε := by positivity
  have h_pointwise : ∀ ω, 2 * X_A ω ≤ ε * (X_A ω)^2 + (1 / ε) * one_A ω := by
    intro ω
    have h := h_amgm (X_A ω) (one_A ω) ε hε_pos
    have h1 : 2 * (X_A ω) * (one_A ω) = 2 * X_A ω := by
      calc 2 * (X_A ω) * (one_A ω)
        = 2 * (X_A ω * one_A ω) := by ring
      _ = 2 * X_A ω := by rw [h_mul ω]
    rw [h1] at h
    have h2 : (one_A ω)^2 = one_A ω := h_sq ω
    rw [h2] at h
    have h3 : (one_A ω) / ε = (1 / ε) * one_A ω := by ring
    rw [h3] at h
    exact h
  have h_int_eps : Integrable (fun ω : Ω => ε * (X_A ω)^2) μ := h_int_XA2.const_mul ε
  have h_int_div : Integrable (fun ω : Ω => (1 / ε) * one_A ω) μ := h_int_one.const_mul (1 / ε)
  have h_int_amgm : Integrable (fun ω : Ω => ε * (X_A ω)^2 + (1 / ε) * one_A ω) μ :=
    h_int_eps.add h_int_div
  have h_integral_ineq : 2 * EA ≤ ε * EA2 + (1 / ε) * PA := by
    have h3 : ∀ᵐ ω ∂μ, 2 * X_A ω ≤ ε * (X_A ω)^2 + (1 / ε) * one_A ω :=
      Filter.Eventually.of_forall h_pointwise
    have h4 : integral μ (fun ω : Ω => 2 * X_A ω) ≤
        integral μ (fun ω : Ω => ε * (X_A ω)^2 + (1 / ε) * one_A ω) :=
      integral_mono_ae (h_int_A.const_mul _) h_int_amgm h3
    have h5 : integral μ (fun ω : Ω => 2 * X_A ω) = 2 * EA := by
      rw [integral_const_mul] <;> simp [hEA_def] <;> ring
    have h6 : integral μ (fun ω : Ω => ε * (X_A ω)^2 + (1 / ε) * one_A ω) =
        ε * EA2 + (1 / ε) * PA := by
      rw [integral_add h_int_eps h_int_div]
      have h7 : integral μ (fun ω : Ω => ε * (X_A ω)^2) = ε * EA2 := by
        rw [integral_const_mul, hEA2_def] <;> ring
      have h8 : integral μ (fun ω : Ω => (1 / ε) * one_A ω) = (1 / ε) * PA := by
        rw [integral_const_mul, hE_one] <;> ring
      rw [h7, h8] <;> ring
    rw [h5, h6] at h4
    exact h4
  have h_cs : EA^2 ≤ EA2 * PA := by
    rw [hε_def] at h_integral_ineq
    have h_pos1 : 0 < EA2 := hEA2_pos
    have h_pos2 : 0 < EA := hEA_pos
    have h : 2 * EA ≤ (EA / EA2) * EA2 + (1 / (EA / EA2)) * PA := h_integral_ineq
    have h_div : (1 / (EA / EA2)) * PA = PA * EA2 / EA := by
      field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
    have h_eq2 : (EA / EA2) * EA2 = EA := by
      field_simp [h_pos1.ne'] <;> ring
    rw [h_div, h_eq2] at h
    have h9 : EA ≤ PA * EA2 / EA := by linarith
    have h10 : EA^2 ≤ PA * EA2 := by
      calc EA^2
        = EA * EA := by ring
      _ ≤ (PA * EA2 / EA) * EA := by gcongr
      _ = PA * EA2 := by
        field_simp [h_pos2.ne'] <;> ring
    have h11 : EA^2 ≤ EA2 * PA := by
      have h12 : PA * EA2 = EA2 * PA := by ring
      rw [h12] at h10
      exact h10
    exact h11

  -- E2 > 0
  have hE2_nonneg : 0 ≤ E2 := by
    have h : 0 ≤ᵐ[μ] fun ω => X ω^2 := by filter_upwards with ω; exact sq_nonneg (X ω)
    exact integral_nonneg (fun ω => sq_nonneg (X ω))
  have hE2_pos : 0 < E2 := by
    by_contra h
    have h20 : E2 = 0 := by linarith [hE2_nonneg]
    have h21 : 0 ≤ᵐ[μ] fun ω => X ω^2 := by filter_upwards with ω; exact sq_nonneg (X ω)
    have h22 : (fun ω : Ω => X ω^2) =ᵐ[μ] fun _ => (0 : ℝ) :=
      (integral_eq_zero_iff_of_nonneg_ae h21 h_int2).mp h20
    have h23 : ∀ᵐ ω ∂μ, X ω = 0 := h22.mono (fun ω h => sq_eq_zero_iff.mp h)
    have h24 : integral μ X = 0 := by
      rw [integral_congr_ae (h23.mono (fun ω h => by rw [h]))] <;> simp
    rw [hμ] at h24
    linarith

  -- Final bound
  have h4 : PA ≥ EA^2 / E2 := by
    have h2 : EA^2 ≤ E2 * PA := by
      calc EA^2 ≤ EA2 * PA := h_cs
           _ ≤ E2 * PA := by gcongr <;> exact hE_XA2_le
    have h4' : 0 < E2 := hE2_pos
    have h5 : 0 ≤ E2 * PA - EA^2 := by linarith
    have h6 : 0 ≤ PA - EA^2 / E2 := by
      field_simp [h4'.ne'] <;> linarith
    linarith
  have hEA_nonneg : 0 ≤ EA := by
    apply integral_nonneg
    intro ω
    exact Set.indicator_nonneg (fun _ _ => hX_nonneg _) _
  have h5 : PA ≥ (μ_val / 2)^2 / E2 := by
    have h7 : (μ_val / 2)^2 ≤ EA^2 := by nlinarith [hE_XA]
    calc PA ≥ EA^2 / E2 := h4
         _ ≥ (μ_val / 2)^2 / E2 := by gcongr
  have h9 : 0 < V + μ_val := by linarith [hV_nonneg, hμ_pos]
  calc PA
    ≥ (μ_val / 2)^2 / E2 := h5
  _ ≥ (μ_val / 2)^2 / (V * μ_val + μ_val^2) := by gcongr <;> linarith [E2_bound]
  _ = μ_val / (4 * (V + μ_val)) := by
      field_simp [h9.ne'] <;> ring


/-! ### Full probabilistic thinning lemma -/

/--
Probabilistic thinning: extract a subfamily with controlled deltaMax and mass retention.

Given a tube family T with deltaMax ≤ D, select each tube independently with
probability p = δ^(-η')/D. With positive probability, the selected subfamily S has:
- deltaMax(S) ≤ net.lossFactor * 10 * δ^(-η')
- |S| ≤ 2 * p * |T|
- shading mass ≥ p/2 * original shading mass

Uses Paley-Zygmund for constant mass-retention probability ≥ 1/8 (when μ ≥ V).
The hypothesis `h_union_bound` ensures the union bound beats the bad-event probability.
-/
lemma probabilistic_thinning_bounded
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {T : TubeFamily δ} (hT_nonempty : T.Nonempty)
    (hT_support :
      ∀ i, (T.tube i).carrier ⊆ Metric.closedBall (0 : Point3) 10)
    (Z : TubeShading T)
    (D : ENNReal) (hD : T.toBodyFamily.deltaMax ≤ D) (hD_ne_top : D ≠ ⊤)
    (η' : ℝ) (hη'_pos : 0 < η')
    (h_thin : Kakeya.realRpowENN δ (-η') ≤ D)
    (net : TubeDensityTestNet δ)
    (h_mu_ge_V : Kakeya.deltaTubeVolume δ ≤ (Kakeya.realRpowENN δ (-η') / D) * Z.mass)
    (h_union_bound :
      let p := (Kakeya.realRpowENN δ (-η')).toReal / D.toReal
      (net.testSets.card : ℝ) * Real.exp (-(11 - Real.exp 1) * (Kakeya.realRpowENN δ (-η')).toReal) +
      Real.exp (-(3 - Real.exp 1) * p * (T.card : ℝ)) < 1 / 8)
    :
    ∃ (T' : TubeSubfamily T),
      T'.family.toBodyFamily.deltaMax ≤ net.lossFactor * (10 : ENNReal) * Kakeya.realRpowENN δ (-η') ∧
      T'.family.enncard ≤ 2 * (Kakeya.realRpowENN δ (-η') / D) * T.enncard ∧
      (T'.restrictShading Z).mass ≥
        (1/2 : ENNReal) * (Kakeya.realRpowENN δ (-η') / D) * Z.mass := by
  let V : ENNReal := Kakeya.deltaTubeVolume δ
  have hV_pos : 0 < V := by
    have h1 : ENNReal.ofReal (2 * δ ^ 2) ≤ V := tube_volume_ge_two_delta_sq δ hδ
    have h2 : 0 < ENNReal.ofReal (2 * δ ^ 2) := by
      apply ENNReal.ofReal_pos.mpr
      positivity
    exact lt_of_lt_of_le h2 h1
  have hV_ne_top : V ≠ ⊤ := by
    have h1 : V ≤ ENNReal.ofReal (Real.pi * δ ^ 2 + (8 / 3 : ℝ) * Real.pi * δ ^ 3) :=
      GeometricLemmas.capsule_upper_bound_instantiation δ hδ
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  let Vreal : ℝ := V.toReal
  have hVreal_pos : 0 < Vreal := by
    exact ENNReal.toReal_pos hV_pos.ne' hV_ne_top
  have h_vol_eq : ∀ i, (T.tube i).volume = V := by
    intro i
    let canonical : Kakeya.DeltaTube δ :=
      { base := 0
        direction := EuclideanSpace.single (0 : Fin 3) 1
        direction_unit := by simp [EuclideanSpace.norm_eq] <;> norm_num }
    have h1 : (T.tube i).volume = canonical.volume := tube_volume_eq (T.tube i) canonical
    have h2 : canonical.volume = V := by rfl
    rw [h1, h2]

  let target : ENNReal := Kakeya.realRpowENN δ (-η')
  have htarget_pos : 0 < target := by
    simp [target, Kakeya.realRpowENN, Real.rpow_pos_of_pos hδ] <;> positivity
  have htarget_ne_top : target ≠ ⊤ := by
    simp [target, Kakeya.realRpowENN]
    <;> exact ENNReal.ofReal_ne_top
  let p : ℝ := target.toReal / D.toReal
  have hp_nonneg : 0 ≤ p := by
    dsimp only [p]
    positivity
  have hp_le_one : p ≤ 1 := by
    dsimp only [p]
    have h1 : target.toReal ≤ D.toReal := by
      exact (ENNReal.toReal_le_toReal htarget_ne_top hD_ne_top).mpr h_thin
    have hD_pos : 0 < D := lt_of_lt_of_le htarget_pos h_thin
    have h2 : 0 < D.toReal := by
      have h3 : D ≠ 0 := hD_pos.ne'
      have h4 : D.toReal ≠ 0 := by
        intro h
        have h5 : D = 0 ∨ D = ⊤ := by
          exact (ENNReal.toReal_eq_zero_iff D).mp h
        rcases h5 with (h5 | h5)
        · exact h3 h5
        · exact hD_ne_top h5
      exact lt_of_le_of_ne (by positivity) h4.symm
    calc target.toReal / D.toReal
      ≤ D.toReal / D.toReal := by gcongr
    _ = 1 := by field_simp [h2.ne'] <;> ring
  let pI : unitInterval := ⟨p, hp_nonneg, hp_le_one⟩
  let μ := selectionMeasure T.card pI
  letI h_prob : IsProbabilityMeasure μ := by
    dsimp only [μ, selectionMeasure]
    letI : ∀ (j : Fin T.card), IsProbabilityMeasure (ProbabilityTheory.bernoulliMeasure true false pI) :=
      fun _ => by infer_instance
    exact Measure.pi.instIsProbabilityMeasure fun x => Ber(true, false, pI)

  -- For each test set K, define the bad density event
  let badDensity (K : Set Point3) : Set (Fin T.card → Bool) :=
    {v | (10 : ℝ) * target.toReal * (volume K).toReal ≤
        selectedVolumeMass Vreal (T.toBodyFamily.containedIndices K) v}

  -- Chernoff bound per test set
  have h_chernoff : ∀ K ∈ net.testSets,
      μ.real (badDensity K) ≤ Real.exp (-(11 - Real.exp 1) * target.toReal) := by
    intro K hK
    let s := T.toBodyFamily.containedIndices K
    have hK_convex : Convex ℝ K := net.testSets_convex K hK
    have hK_vol_ne_top : volume K ≠ ⊤ := net.testSets_volume_ne_top K hK
    have hK_vol_pos : 0 < volume K := net.testSets_volume_pos K hK
    have hK_vol_real_pos : 0 < (volume K).toReal :=
      ENNReal.toReal_pos hK_vol_pos.ne' hK_vol_ne_top
    by_cases h_s_empty : s = ∅
    · have h_event_empty : badDensity K = ∅ := by
        ext v
        simp only [badDensity, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        have h_mass_zero : selectedVolumeMass Vreal s v = 0 := by
          rw [h_s_empty] <;> simp [selectedVolumeMass]
        rw [h_mass_zero]
        have h_target_real_pos : 0 < target.toReal := ENNReal.toReal_pos htarget_pos.ne' htarget_ne_top
        have h_pos : 0 < (10 : ℝ) * target.toReal * (volume K).toReal := by
          exact mul_pos (mul_pos (by norm_num) h_target_real_pos) hK_vol_real_pos
        linarith
      rw [h_event_empty] <;> simp [measure_empty] <;> positivity
    · have h_s_nonempty : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_s_empty
      rcases h_s_nonempty with ⟨i, hi⟩
      have h_density_le_deltaMax : T.toBodyFamily.density K ≤ T.toBodyFamily.deltaMax := by
        apply le_sSup
        exact ⟨K, hK_convex, rfl⟩
      have h_density_le_D : T.toBodyFamily.density K ≤ D := h_density_le_deltaMax.trans hD
      have h_containedMass_le : T.toBodyFamily.containedMass K ≤ D * volume K := by
        have h_div : T.toBodyFamily.density K = T.toBodyFamily.containedMass K / volume K := by rfl
        rw [h_div] at h_density_le_D
        have h : T.toBodyFamily.containedMass K / volume K ≤ D := h_density_le_D
        have h2 : T.toBodyFamily.containedMass K / volume K * volume K ≤ D * volume K := by gcongr
        have h3 : T.toBodyFamily.containedMass K / volume K * volume K = T.toBodyFamily.containedMass K := by
          rw [ENNReal.div_mul_cancel hK_vol_pos.ne' hK_vol_ne_top]
          <;> ring
        rw [h3] at h2
        exact h2
      have h_body_vol : ∀ j, (T.toBodyFamily.body j).volume = V := by
        intro j
        have h5 : (T.toBodyFamily.body j).volume = (T.tube j).volume := by rfl
        rw [h5, h_vol_eq j]
      have h_containedMass_eq : T.toBodyFamily.containedMass K = (s.card : ENNReal) * V := by
        simp [BodyFamily.containedMass, h_body_vol, Finset.sum_const] <;> ring
      rw [h_containedMass_eq] at h_containedMass_le
      have h_real_ineq : (s.card : ℝ) * Vreal ≤ D.toReal * (volume K).toReal := by
        have h_all_finite : ((s.card : ENNReal) * V) ≠ ⊤ :=
          ENNReal.mul_ne_top (by exact ENNReal.natCast_ne_top s.card) hV_ne_top
        have h_rhs_finite : (D * volume K) ≠ ⊤ := ENNReal.mul_ne_top hD_ne_top hK_vol_ne_top
        have h := (ENNReal.toReal_le_toReal h_all_finite h_rhs_finite).mpr h_containedMass_le
        simpa [ENNReal.toReal_mul] using h
      have h_i_contained : (T.toBodyFamily.body i).carrier ⊆ K :=
        BodyFamily.mem_containedIndices_iff.mp hi
      have hV_le_volK : V ≤ volume K := by
        have h8 : V = volume (T.toBodyFamily.body i).carrier := by
          have h9 : (T.toBodyFamily.body i).volume = V := h_body_vol i
          exact h9.symm
        rw [h8]
        exact measure_mono h_i_contained
      have hVreal_le_volKreal : Vreal ≤ (volume K).toReal :=
        (ENNReal.toReal_le_toReal hV_ne_top hK_vol_ne_top).mpr hV_le_volK
      have h_target_pos' : 0 < target.toReal := ENNReal.toReal_pos htarget_pos.ne' htarget_ne_top
      have hD_pos : 0 < D := lt_of_lt_of_le htarget_pos h_thin
      have hD_real_pos : 0 < D.toReal := ENNReal.toReal_pos hD_pos.ne' hD_ne_top
      let S : ℝ := 10 * target.toReal * (volume K).toReal
      have hS_pos : 0 < S := by
        have h1 : 0 < target.toReal := h_target_pos'
        have h2 : 0 < (volume K).toReal := hK_vol_real_pos
        positivity
      have h_p_card_le : p * (s.card : ℝ) ≤ target.toReal * (volume K).toReal / Vreal := by
        have h1 : p * (s.card : ℝ) * Vreal ≤ target.toReal * (volume K).toReal := by
          calc p * (s.card : ℝ) * Vreal
            = (target.toReal / D.toReal) * ((s.card : ℝ) * Vreal) := by ring
          _ ≤ (target.toReal / D.toReal) * (D.toReal * (volume K).toReal) := by gcongr
          _ = target.toReal * (volume K).toReal := by field_simp [hD_real_pos.ne'] <;> ring
        calc p * (s.card : ℝ)
          = (p * (s.card : ℝ) * Vreal) / Vreal := by field_simp [hVreal_pos.ne'] <;> ring
        _ ≤ (target.toReal * (volume K).toReal) / Vreal := by gcongr
      have h_exp_lt_10 : Real.exp 1 < 10 := by
        have h : Real.exp 1 < 3 := Real.exp_one_lt_three
        linarith
      have h10_minus_e_pos : 0 < 11 - Real.exp 1 := by linarith
      have h_exp_bound : -S / Vreal + (Real.exp 1 - 1) * p * (s.card : ℝ) ≤
          -(11 - Real.exp 1) * target.toReal := by
        have h_e_sub_pos : 0 ≤ Real.exp 1 - 1 := by
          have h : (1 : ℝ) < Real.exp 1 := by
            have h0 : Real.exp 0 < Real.exp 1 := Real.exp_strictMono (by norm_num)
            simpa using h0
          linarith
        have h_mul : (Real.exp 1 - 1) * p * (s.card : ℝ) ≤
            (Real.exp 1 - 1) * (target.toReal * (volume K).toReal / Vreal) := by
          calc (Real.exp 1 - 1) * p * (s.card : ℝ)
            = (Real.exp 1 - 1) * (p * (s.card : ℝ)) := by ring
          _ ≤ (Real.exp 1 - 1) * (target.toReal * (volume K).toReal / Vreal) :=
            mul_le_mul_of_nonneg_left h_p_card_le h_e_sub_pos
        have h3 : -S / Vreal + (Real.exp 1 - 1) * p * (s.card : ℝ) ≤
            -S / Vreal + (Real.exp 1 - 1) * (target.toReal * (volume K).toReal / Vreal) := by
          linarith [h_mul]
        have h4 : -S / Vreal + (Real.exp 1 - 1) * (target.toReal * (volume K).toReal / Vreal) =
            -(11 - Real.exp 1) * target.toReal * ((volume K).toReal / Vreal) := by
          simp [S] <;> ring
        have h5 : (volume K).toReal / Vreal ≥ 1 := by
          have h7 : 0 < Vreal := hVreal_pos
          calc (volume K).toReal / Vreal
            ≥ Vreal / Vreal := by gcongr
          _ = 1 := by field_simp [h7.ne'] <;> ring
        have hA_pos : 0 < (11 - Real.exp 1) * target.toReal := by positivity
        rw [h4] at h3
        nlinarith
      have h_chernoff2 : μ.real (badDensity K) ≤ Real.exp (-S / Vreal + (Real.exp 1 - 1) * p * (s.card : ℝ)) :=
        chernoff_selectedVolumeMass T.card pI Vreal hVreal_pos s hS_pos
      have h_final : Real.exp (-S / Vreal + (Real.exp 1 - 1) * p * (s.card : ℝ)) ≤
          Real.exp (-(11 - Real.exp 1) * target.toReal) := Real.exp_monotone h_exp_bound
      exact h_chernoff2.trans h_final

  -- Union bound for density
  have h_union_density : μ.real (⋃ K ∈ net.testSets, badDensity K) ≤
      (net.testSets.card : ℝ) * Real.exp (-(11 - Real.exp 1) * target.toReal) := by
    have h_bd_meas : ∀ K ∈ net.testSets, MeasurableSet (badDensity K) := by
      intro K _
      exact measurableSet_le measurable_const (Finset.measurable_sum _ (fun i _ => coordVolumeIndicator_measurable Vreal i))
    have h1_enn : μ (⋃ K ∈ net.testSets, badDensity K) ≤ ∑ K ∈ net.testSets, μ (badDensity K) :=
      MeasureTheory.measure_biUnion_finset_le net.testSets badDensity
    have h_le_sum : (∑ K ∈ net.testSets, μ (badDensity K)) ≤ (net.testSets.card : ENNReal) := by
      have h : ∀ K ∈ net.testSets, μ (badDensity K) ≤ (1 : ENNReal) := by
        intro K _
        have h1 : μ (badDensity K) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        have h2 : μ Set.univ = 1 := measure_univ
        rw [h2] at h1
        exact h1
      have h2 : ∑ K ∈ net.testSets, μ (badDensity K) ≤ ∑ K ∈ net.testSets, (1 : ENNReal) := Finset.sum_le_sum h
      simpa [Finset.sum_const] using h2
    have h_fin : (∑ K ∈ net.testSets, μ (badDensity K)) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) h_le_sum
    have h_sum_toReal : (∑ K ∈ net.testSets, μ.real (badDensity K)) = (∑ K ∈ net.testSets, μ (badDensity K)).toReal := by
      have h : ∀ K ∈ net.testSets, μ (badDensity K) ≠ ⊤ := fun K _ => measure_ne_top μ _
      exact (ENNReal.toReal_sum h).symm
    have h1 : μ.real (⋃ K ∈ net.testSets, badDensity K) ≤ ∑ K ∈ net.testSets, μ.real (badDensity K) := by
      rw [h_sum_toReal]
      exact (ENNReal.toReal_le_toReal (measure_ne_top μ _) h_fin).mpr h1_enn
    have h2 : ∑ K ∈ net.testSets, μ.real (badDensity K) ≤
        ∑ K ∈ net.testSets, Real.exp (-(11 - Real.exp 1) * target.toReal) := by
      apply Finset.sum_le_sum
      intro K hK
      exact h_chernoff K hK
    have h3 : ∑ K ∈ net.testSets, Real.exp (-(11 - Real.exp 1) * target.toReal) =
        (net.testSets.card : ℝ) * Real.exp (-(11 - Real.exp 1) * target.toReal) := by
      simp [Finset.sum_const]
      <;> ring
    linarith

  -- Count bound event
  let badCount : Set (Fin T.card → Bool) :=
    {v | 2 * p * (T.card : ℝ) ≤ ∑ i : Fin T.card, coordIndicator i v}

  have h_chernoff_count : μ.real badCount ≤ Real.exp (-(3 - Real.exp 1) * p * (T.card : ℝ)) := by
    have hS_pos : 0 < 2 * p * (T.card : ℝ) := by
      have hp_pos : 0 < p := by
        dsimp only [p]
        have h1 : 0 < target.toReal := ENNReal.toReal_pos htarget_pos.ne' htarget_ne_top
        have hD_pos' : 0 < D := lt_of_lt_of_le htarget_pos h_thin
        have h3 : 0 < D.toReal := ENNReal.toReal_pos hD_pos'.ne' hD_ne_top
        positivity
      have hT_card_pos : 0 < (T.card : ℝ) := Nat.cast_pos.mpr hT_nonempty
      positivity
    have h_main := chernoff_selection_count T.card pI hS_pos
    have hpi : (pI : ℝ) = p := by rfl
    have h_eq : Real.exp (-(2 * p * (T.card : ℝ)) + (Real.exp 1 - 1) * (T.card : ℝ) * (pI : ℝ)) =
        Real.exp (-(3 - Real.exp 1) * p * (T.card : ℝ)) := by
      have h_arg : (-(2 * p * (T.card : ℝ)) + (Real.exp 1 - 1) * (T.card : ℝ) * (pI : ℝ)) =
          (-(3 - Real.exp 1) * p * (T.card : ℝ)) := by
        rw [hpi]
        <;> ring
      rw [h_arg]
    rw [h_eq] at h_main
    exact h_main

  -- Shading mass event
  let Mreal : ℝ := Z.mass.toReal
  have hZ_mass_ne_top : Z.mass ≠ ⊤ := by
    exact ENNReal.sum_ne_top.mpr (fun i _ => by
      have h6 : volume (Z.carrier i) ≤ volume (T.tube i).carrier := measure_mono (Z.subset_body i)
      have h7 : volume (T.tube i).carrier = V := h_vol_eq i
      rw [h7] at h6
      exact ne_top_of_le_ne_top hV_ne_top h6)
  have hD_pos : 0 < D := lt_of_lt_of_le htarget_pos h_thin
  have hD_ne_zero : D ≠ 0 := hD_pos.ne'
  have h_target_div_D_ne_top : (target / D) ≠ ⊤ :=
    ENNReal.div_ne_top htarget_ne_top hD_ne_zero
  have h_prod_ne_top : ((target / D) * Z.mass) ≠ ⊤ :=
    ENNReal.mul_ne_top h_target_div_D_ne_top hZ_mass_ne_top
  have h_mu_ge_V_real : Vreal ≤ p * Mreal := by
    have h1 : V ≤ (target / D) * Z.mass := h_mu_ge_V
    have h2 : ((target / D) * Z.mass).toReal = p * Mreal := by
      have h3 : ((target / D) * Z.mass).toReal =
          (target / D).toReal * Z.mass.toReal :=
        ENNReal.toReal_mul
      rw [h3]
      have h4 : (target / D).toReal = target.toReal / D.toReal :=
        ENNReal.toReal_div target D
      rw [h4] <;> rfl
    have h5 : Vreal ≤ ((target / D) * Z.mass).toReal :=
      (ENNReal.toReal_le_toReal hV_ne_top h_prod_ne_top).mpr h_mu_ge_V
    rw [h2] at h5
    exact h5
  let selectedShading (v : Fin T.card → Bool) : ℝ :=
    ∑ i : Fin T.card, (volume (Z.carrier i)).toReal * coordIndicator i v

  have h_mass_nonneg : ∀ v, 0 ≤ selectedShading v := by
    intro v
    apply Finset.sum_nonneg
    intro i _
    have h1 : 0 ≤ (volume (Z.carrier i)).toReal := by positivity
    have h2 : 0 ≤ coordIndicator i v := (coordIndicator_bound i v).1
    exact mul_nonneg h1 h2

  have h_mass_le_M : ∀ v, selectedShading v ≤ Mreal := by
    intro v
    have h1 : selectedShading v ≤ ∑ i : Fin T.card, (volume (Z.carrier i)).toReal := by
      apply Finset.sum_le_sum
      intro i _
      have h2 : 0 ≤ coordIndicator i v := (coordIndicator_bound i v).1
      have h3 : coordIndicator i v ≤ 1 := (coordIndicator_bound i v).2
      have h4 : 0 ≤ (volume (Z.carrier i)).toReal := by positivity
      calc (volume (Z.carrier i)).toReal * coordIndicator i v
        ≤ (volume (Z.carrier i)).toReal * 1 := by gcongr
      _ = (volume (Z.carrier i)).toReal := by ring
    have h_vol_fin : ∀ i, volume (Z.carrier i) ≠ ⊤ := by
      intro i
      have h6 : volume (Z.carrier i) ≤ volume (T.tube i).carrier := measure_mono (Z.subset_body i)
      have h7 : volume (T.tube i).carrier = V := h_vol_eq i
      rw [h7] at h6
      exact ne_top_of_le_ne_top hV_ne_top h6
    have h_sum_real : (∑ i : Fin T.card, (volume (Z.carrier i)).toReal) = (∑ i : Fin T.card, volume (Z.carrier i)).toReal :=
      (ENNReal.toReal_sum (hf := fun i _ => h_vol_fin i)).symm
    have h5 : (∑ i : Fin T.card, (volume (Z.carrier i)).toReal) = Mreal := by
      rw [h_sum_real] <;> rfl
    rw [h5] at h1
    exact h1

  have h_int_shading : Integrable selectedShading μ := by
    have h_int_ci : ∀ i, Integrable (coordIndicator i) μ := by
      intro i
      have h1 : ∀ᵐ v ∂μ, ‖coordIndicator i v‖ ≤ 1 := by
        filter_upwards with v
        have h2 := coordIndicator_bound i v
        rw [Real.norm_eq_abs, abs_of_nonneg h2.1]
        exact h2.2
      exact bounded_measurable_integrable (coordIndicator_measurable i) (by norm_num) h1
    let f : Fin T.card → (Fin T.card → Bool) → ℝ := fun i v => (volume (Z.carrier i)).toReal * coordIndicator i v
    have h_int2 : ∀ i, Integrable (f i) μ := by
      intro i
      exact (h_int_ci i).const_mul _
    have h : selectedShading = fun v => ∑ i : Fin T.card, f i v := by rfl
    rw [h]
    exact integrable_finset_sum Finset.univ (fun i _ => h_int2 i)

  have h_vol_fin2 : ∀ i, volume (Z.carrier i) ≠ ⊤ := by
    intro i
    have h6 : volume (Z.carrier i) ≤ volume (T.tube i).carrier := measure_mono (Z.subset_body i)
    have h7 : volume (T.tube i).carrier = V := h_vol_eq i
    rw [h7] at h6
    exact ne_top_of_le_ne_top hV_ne_top h6

  have h_expect_mass : integral μ selectedShading = p * Mreal := by
    let c : Fin T.card → ℝ := fun i => (volume (Z.carrier i)).toReal
    let f : Fin T.card → (Fin T.card → Bool) → ℝ := fun i v => c i * coordIndicator i v
    have h_int_ci : ∀ i, Integrable (coordIndicator i) μ := by
      intro i
      have h1 : ∀ᵐ v ∂μ, ‖coordIndicator i v‖ ≤ 1 := by
        filter_upwards with v
        have h2 := coordIndicator_bound i v
        rw [Real.norm_eq_abs, abs_of_nonneg h2.1]
        exact h2.2
      exact bounded_measurable_integrable (coordIndicator_measurable i) (by norm_num) h1
    have h_int_f : ∀ i, Integrable (f i) μ := fun i => (h_int_ci i).const_mul (c i)
    have h_eq_shading : selectedShading = fun v => ∑ i : Fin T.card, f i v := by rfl
    have h_sum_int : integral μ (fun v => ∑ i : Fin T.card, f i v) = ∑ i : Fin T.card, integral μ (f i) := by
      exact integral_finsetSum Finset.univ fun i _ => h_int_f i
    have h_eq1 : integral μ selectedShading = ∑ i : Fin T.card, c i * integral μ (coordIndicator i) := by
      rw [h_eq_shading, h_sum_int]
      apply Finset.sum_congr rfl
      intro i _
      have h3 : integral μ (f i) = c i * integral μ (coordIndicator i) := by
        have h4 : f i = c i • coordIndicator i := by funext v; simp [f, smul_eq_mul]
        rw [h4]
        have h5 : integral μ (c i • coordIndicator i) = c i • integral μ (coordIndicator i) :=
          integral_smul (μ := μ) (c := c i) (f := coordIndicator i)
        simpa [smul_eq_mul] using h5
      exact h3
    rw [h_eq1]
    have h3 : ∑ i : Fin T.card, c i * integral μ (coordIndicator i) = ∑ i : Fin T.card, c i * p := by
      apply Finset.sum_congr rfl
      intro i _
      rw [coordIndicator_expectation T.card pI i] <;> ring
    rw [h3]
    have h4 : ∑ i : Fin T.card, c i * p = p * ∑ i : Fin T.card, c i := by
      have h_comm : ∑ i : Fin T.card, c i * p = ∑ i : Fin T.card, p * c i := by
        apply Finset.sum_congr rfl
        intro i _; ring
      rw [h_comm, ← Finset.mul_sum]
      <;> ring
    rw [h4]
    have h_sum_real2 : (∑ i : Fin T.card, c i) = (∑ i : Fin T.card, volume (Z.carrier i)).toReal := by
      dsimp only [c]
      exact (ENNReal.toReal_sum (hf := fun i _ => h_vol_fin2 i)).symm
    have h6 : (∑ i : Fin T.card, c i) = Mreal := by
      rw [h_sum_real2] <;> rfl
    rw [h6] <;> ring

  have h_mass_event : μ.real {v | p * Mreal / 2 ≤ selectedShading v} ≥ 1 / 8 := by
    by_cases hM : Mreal = 0
    · have h_all_zero : ∀ v, selectedShading v = 0 := by
        intro v
        have h_nonneg : 0 ≤ selectedShading v := h_mass_nonneg v
        have h_le : selectedShading v ≤ Mreal := h_mass_le_M v
        rw [hM] at h_le
        linarith
      have h_event_univ : {v | p * Mreal / 2 ≤ selectedShading v} = Set.univ := by
        ext v
        simp [h_all_zero v, hM] <;> linarith
      rw [h_event_univ]
      <;> simp [measure_univ] <;> norm_num
    · have hM_pos : 0 < Mreal := by
        have h_nonneg : 0 ≤ Mreal := by positivity
        exact lt_of_le_of_ne h_nonneg (Ne.symm hM)
      set μ_val : ℝ := p * Mreal with hμ_val_def
      have hμ_val_pos : 0 < μ_val := by
        dsimp only [μ_val]
        have hp_pos : 0 < p := by
          dsimp only [p]
          have h1 : 0 < target.toReal := ENNReal.toReal_pos htarget_pos.ne' htarget_ne_top
          have hD_pos' : 0 < D := lt_of_lt_of_le htarget_pos h_thin
          have h3 : 0 < D.toReal := ENNReal.toReal_pos hD_pos'.ne' hD_ne_top
          positivity
        positivity
      let c : Fin T.card → ℝ := fun i => (volume (Z.carrier i)).toReal
      let f : Fin T.card → (Fin T.card → Bool) → ℝ := fun i v => c i * coordIndicator i v
      have hc_nonneg : ∀ i, 0 ≤ c i := by intro i; positivity
      have hc_le_V : ∀ i, c i ≤ Vreal := by
        intro i
        have h6 : volume (Z.carrier i) ≤ volume (T.tube i).carrier := measure_mono (Z.subset_body i)
        have h7 : volume (T.tube i).carrier = V := h_vol_eq i
        rw [h7] at h6
        have h_iff : (volume (Z.carrier i)).toReal ≤ V.toReal ↔ volume (Z.carrier i) ≤ V :=
          ENNReal.toReal_le_toReal (h_vol_fin2 i) hV_ne_top
        exact h_iff.mpr h6
      have h_int_ci : ∀ i, Integrable (coordIndicator i) μ := by
        intro i
        have h1 : ∀ᵐ v ∂μ, ‖coordIndicator i v‖ ≤ 1 := by
          filter_upwards with v
          have h2 := coordIndicator_bound i v
          rw [Real.norm_eq_abs, abs_of_nonneg h2.1]
          exact h2.2
        exact bounded_measurable_integrable (coordIndicator_measurable i) (by norm_num) h1
      have h_int_f : ∀ i, Integrable (f i) μ := fun i => (h_int_ci i).const_mul (c i)
      have h_indep : iIndepFun (fun i v => coordIndicator i v) μ := coordIndicators_independent T.card pI
      have h_f_nonneg : ∀ i v, 0 ≤ f i v := by
        intro i v
        dsimp only [f]
        have h21 : 0 ≤ c i := by positivity
        have h22 : 0 ≤ coordIndicator i v := (coordIndicator_bound i v).1
        exact mul_nonneg h21 h22
      have h_f_le_V : ∀ i v, f i v ≤ Vreal := by
        intro i v
        dsimp only [f]
        have h4 : c i ≤ Vreal := hc_le_V i
        have h5 : coordIndicator i v ≤ 1 := (coordIndicator_bound i v).2
        have h6 : 0 ≤ c i := by positivity
        have h7 : c i * coordIndicator i v ≤ c i := by
          have h8 : c i * coordIndicator i v ≤ c i * (1 : ℝ) := mul_le_mul_of_nonneg_left h5 h6
          simpa using h8
        exact h7.trans h4
      have h_int_f2 : ∀ i, Integrable (fun v => (f i v)^2) μ := by
        intro i
        have h_bdd : ∀ v, ‖(f i v)^2‖ ≤ Vreal^2 := by
          intro v
          have h7 : (f i v)^2 ≤ Vreal^2 := by nlinarith [h_f_nonneg i v, h_f_le_V i v]
          rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (f i v)^2 by positivity)]
          exact h7
        have h_meas : Measurable (fun v => (f i v)^2) := by fun_prop
        exact bounded_measurable_integrable h_meas (by positivity) (Filter.Eventually.of_forall h_bdd)
      have h_sq_le : ∀ i, integral μ (fun v => (f i v)^2) ≤ Vreal * integral μ (f i) := by
        intro i
        have h1 : ∀ v, (f i v)^2 ≤ Vreal * f i v := by
          intro v
          have h2 : 0 ≤ f i v := h_f_nonneg i v
          have h3 : f i v ≤ Vreal := h_f_le_V i v
          nlinarith
        have h_int_rhs : Integrable (fun v => Vreal * f i v) μ := (h_int_f i).const_mul Vreal
        have h_ae : ∀ᵐ v ∂μ, (f i v)^2 ≤ Vreal * f i v := Filter.Eventually.of_forall h1
        have h_main : integral μ (fun v => (f i v)^2) ≤ integral μ (fun v => Vreal * f i v) :=
          integral_mono_ae (h_int_f2 i) h_int_rhs h_ae
        have h_rhs : integral μ (fun v => Vreal * f i v) = Vreal * integral μ (f i) := by
          rw [integral_const_mul]
        exact h_main.trans (le_of_eq h_rhs)
      have h_indep_mul : ∀ i j, i ≠ j → integral μ (fun v => f i v * f j v) = integral μ (f i) * integral μ (f j) := by
        intro i j hne
        have h1 : iIndepFun f μ := h_indep.comp (fun i x => c i * x) (fun i => by fun_prop)
        have h2 : IndepFun (f i) (f j) μ := h1.indepFun hne
        exact h2.integral_mul_eq_mul_integral (h_int_f i).aestronglyMeasurable (h_int_f j).aestronglyMeasurable
      have h_int2_shading : Integrable (fun v => selectedShading v ^ 2) μ := by
        have h1 : ∀ v, |selectedShading v ^ 2| ≤ Mreal ^ 2 := by
          intro v
          have h2 : 0 ≤ selectedShading v := h_mass_nonneg v
          have h3 : selectedShading v ≤ Mreal := h_mass_le_M v
          have h4 : selectedShading v ^ 2 ≤ Mreal ^ 2 := by nlinarith
          rw [abs_of_nonneg (show 0 ≤ selectedShading v ^ 2 by positivity)]
          exact h4
        have h_meas : Measurable (fun v => selectedShading v ^ 2) := by fun_prop
        exact bounded_measurable_integrable h_meas (by positivity) (Filter.Eventually.of_forall h1)
      have hE2 : integral μ (fun v => selectedShading v ^ 2) ≤ Vreal * μ_val + μ_val^2 := by
        let s : Finset (Fin T.card) := Finset.univ
        have h_expand : integral μ (fun v => selectedShading v ^ 2) =
            ∑ i ∈ s, integral μ (fun v => (f i v)^2) +
            ∑ i ∈ s, ∑ j ∈ s.erase i, integral μ (fun v => f i v * f j v) := by
          have h1 : (fun v => selectedShading v ^ 2) = fun v => (∑ i ∈ s, f i v) ^ 2 := by rfl
          rw [h1]
          have h2 : ∀ v, (∑ i ∈ s, f i v)^2 = ∑ i ∈ s, (f i v)^2 + ∑ i ∈ s, ∑ j ∈ s.erase i, f i v * f j v := by
            intro v
            have h_sum2 : (∑ i ∈ s, f i v)^2 = ∑ i ∈ s, ∑ j ∈ s, (f i v) * (f j v) := by
              have h_sq : (∑ i ∈ s, f i v)^2 = (∑ i ∈ s, f i v) * (∑ j ∈ s, f j v) := by ring
              rw [h_sq, Finset.sum_mul_sum]
            rw [h_sum2]
            have h3 : ∑ i ∈ s, ∑ j ∈ s, (f i v) * (f j v) =
                ∑ i ∈ s, ((f i v)^2 + ∑ j ∈ s.erase i, (f i v) * (f j v)) := by
              apply Finset.sum_congr rfl
              intro i hi
              have h4 : ∑ j ∈ s, (f i v) * (f j v) = (f i v)^2 + ∑ j ∈ s.erase i, (f i v) * (f j v) := by
                have h5 : ∑ j ∈ s.erase i, (f i v) * (f j v) = (∑ j ∈ s, (f i v) * (f j v)) - (f i v) * (f i v) := by
                  exact Finset.sum_erase_eq_sub hi
                linarith
              exact h4
            rw [h3, Finset.sum_add_distrib]
          have h3 : integral μ (fun v => (∑ i ∈ s, f i v)^2) =
              integral μ (fun v => ∑ i ∈ s, (f i v)^2 + ∑ i ∈ s, ∑ j ∈ s.erase i, f i v * f j v) := by
            apply integral_congr_ae
            filter_upwards with v
            exact h2 v
          rw [h3]
          simp [integral_add, integral_finset_sum] <;> ring
        rw [h_expand]
        have h4 : ∑ i ∈ s, integral μ (fun v => (f i v)^2) ≤ Vreal * ∑ i ∈ s, integral μ (f i) := by
          calc ∑ i ∈ s, integral μ (fun v => (f i v)^2)
            ≤ ∑ i ∈ s, (Vreal * integral μ (f i)) := Finset.sum_le_sum (fun i _ => h_sq_le i)
          _ = Vreal * ∑ i ∈ s, integral μ (f i) := by rw [Finset.mul_sum]
        have h5 : ∑ i ∈ s, ∑ j ∈ s.erase i, integral μ (fun v => f i v * f j v) =
            ∑ i ∈ s, ∑ j ∈ s.erase i, (integral μ (f i)) * (integral μ (f j)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j hj
          exact h_indep_mul i j (Ne.symm (Finset.mem_erase.mp hj |>.1))
        rw [h5]
        have h6 : ∑ i ∈ s, ∑ j ∈ s.erase i, (integral μ (f i)) * (integral μ (f j)) ≤
            (∑ i ∈ s, integral μ (f i)) ^ 2 := by
          have h_nonneg_int : ∀ i, 0 ≤ integral μ (f i) := by
            intro i
            exact integral_nonneg (fun v => h_f_nonneg i v)
          have h7 : ∑ i ∈ s, ∑ j ∈ s.erase i, (integral μ (f i)) * (integral μ (f j)) ≤
              ∑ i ∈ s, ∑ j ∈ s, (integral μ (f i)) * (integral μ (f j)) := by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.erase_subset i s
            · intro j _ _
              exact mul_nonneg (h_nonneg_int i) (h_nonneg_int j)
          have h8 : ∑ i ∈ s, ∑ j ∈ s, (integral μ (f i)) * (integral μ (f j)) =
              (∑ i ∈ s, integral μ (f i)) ^ 2 := by
            have h9 : (∑ i ∈ s, integral μ (f i)) * (∑ j ∈ s, integral μ (f j)) =
                ∑ i ∈ s, ∑ j ∈ s, (integral μ (f i)) * (integral μ (f j)) := by
              rw [Finset.sum_mul_sum]
            rw [←h9] <;> ring
          exact le_trans h7 (le_of_eq h8)
        have h9 : ∑ i ∈ s, integral μ (f i) = μ_val := by
          have h_sum_int : integral μ (fun v => ∑ i ∈ s, f i v) =
              ∑ i ∈ s, integral μ (f i) :=
            integral_finsetSum s fun i _ => h_int_f i
          have h_eq : selectedShading = fun v => ∑ i ∈ s, f i v := by rfl
          have h : ∑ i ∈ s, integral μ (f i) = integral μ selectedShading := by
            rw [←h_sum_int, ←h_eq]
          rw [h, h_expect_mass] <;> rfl
        calc _
          ≤ Vreal * ∑ i ∈ s, integral μ (f i) + (∑ i ∈ s, integral μ (f i)) ^ 2 := by gcongr
        _ = Vreal * μ_val + μ_val^2 := by rw [h9] <;> ring
      have h_pz := paley_zygmund_lower_bound Vreal (by positivity)
        (Finset.measurable_sum _ (fun i _ => (coordIndicator_measurable i).const_mul _))
        h_mass_nonneg h_int_shading h_int2_shading μ_val h_expect_mass hμ_val_pos hE2
      have h_ge : Vreal ≤ μ_val := h_mu_ge_V_real
      have h_final : μ_val / (4 * (Vreal + μ_val)) ≥ 1 / 8 := by
        calc μ_val / (4 * (Vreal + μ_val))
          ≥ μ_val / (4 * (μ_val + μ_val)) := by gcongr <;> linarith
        _ = 1 / 8 := by
          have h6 : 0 < μ_val := hμ_val_pos
          field_simp [h6.ne'] <;> ring
      exact le_trans h_final h_pz

  -- Existence (density + cardinality + mass)
  have h_exists : ∃ (v : Fin T.card → Bool),
      v ∉ (badCount ∪ (⋃ K ∈ net.testSets, badDensity K)) ∧
      p * Mreal / 2 ≤ selectedShading v := by
    let badUnion := badCount ∪ (⋃ K ∈ net.testSets, badDensity K)
    let A := badUnionᶜ
    let C := {v | p * Mreal / 2 ≤ selectedShading v}
    have h_bd_meas2 : ∀ K ∈ net.testSets, MeasurableSet (badDensity K) := by
      intro K _
      exact measurableSet_le measurable_const (Finset.measurable_sum _ (fun i _ => coordVolumeIndicator_measurable Vreal i))
    have h_bc_meas : MeasurableSet badCount :=
      measurableSet_le measurable_const (Finset.measurable_sum _ (fun i _ => coordIndicator_measurable i))
    have hA_meas : MeasurableSet A := by
      apply MeasurableSet.compl
      apply h_bc_meas.union
      apply Finset.measurableSet_biUnion
      intro K _
      exact h_bd_meas2 K ‹_›
    have hC_meas : MeasurableSet C := measurableSet_le measurable_const (Finset.measurable_sum _ (fun i _ => (coordIndicator_measurable i).const_mul _))
    have h_union_total : μ.real badUnion < 1 / 8 := by
      have h1 : μ.real badUnion ≤ μ.real badCount + μ.real (⋃ K ∈ net.testSets, badDensity K) :=
        MeasureTheory.measureReal_union_le _ _
      have h2 : μ.real (⋃ K ∈ net.testSets, badDensity K) ≤
          (net.testSets.card : ℝ) * Real.exp (-(11 - Real.exp 1) * target.toReal) := h_union_density
      have h3 : μ.real badCount ≤ Real.exp (-(3 - Real.exp 1) * p * (T.card : ℝ)) := h_chernoff_count
      linarith [h_union_bound]
    have hA_gt : μ.real A > 7 / 8 := by
      have h_density_union_meas : MeasurableSet (⋃ K ∈ net.testSets, badDensity K) := by
        apply Finset.measurableSet_biUnion
        intro K hK
        exact h_bd_meas2 K hK
      have h_union_meas : MeasurableSet badUnion := h_bc_meas.union h_density_union_meas
      have h1 : μ.real A = 1 - μ.real badUnion := by
        have h2 : μ.real A = μ.real Set.univ - μ.real badUnion :=
          MeasureTheory.measureReal_compl h_union_meas
        have h3 : μ.real Set.univ = 1 := by simp
        rw [h2, h3] <;> ring
      rw [h1]
      linarith [h_union_total]
    have hC_ge : μ.real C ≥ 1 / 8 := h_mass_event
    have h_intersection : μ.real (A ∩ C) > 0 := by
      have hAC_meas : MeasurableSet (A ∩ C) := hA_meas.inter hC_meas
      have h_union_meas2 : MeasurableSet (A ∪ C) := hA_meas.union hC_meas
      have h_union_eq : μ.real (A ∪ C) + μ.real (A ∩ C) = μ.real A + μ.real C := by
        have h : μ (A ∪ C) + μ (A ∩ C) = μ A + μ C := measure_union_add_inter A hC_meas
        have h_ne_top1 : μ (A ∪ C) ≠ ⊤ := measure_ne_top μ _
        have h_ne_top2 : μ (A ∩ C) ≠ ⊤ := measure_ne_top μ _
        have h_ne_top3 : μ A ≠ ⊤ := measure_ne_top μ _
        have h_ne_top4 : μ C ≠ ⊤ := measure_ne_top μ _
        have h_toReal : ENNReal.toReal (μ (A ∪ C) + μ (A ∩ C)) =
            ENNReal.toReal (μ A + μ C) := by rw [h]
        have h_left : ENNReal.toReal (μ (A ∪ C) + μ (A ∩ C)) =
            μ.real (A ∪ C) + μ.real (A ∩ C) := by
          rw [ENNReal.toReal_add h_ne_top1 h_ne_top2] <;> rfl
        have h_right : ENNReal.toReal (μ A + μ C) = μ.real A + μ.real C := by
          rw [ENNReal.toReal_add h_ne_top3 h_ne_top4] <;> rfl
        rw [h_left, h_right] at h_toReal
        exact h_toReal
      have h_union_le_one : μ.real (A ∪ C) ≤ 1 := by
        have h : μ (A ∪ C) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        have h_ne_top : μ (A ∪ C) ≠ ⊤ := measure_ne_top μ _
        have h_univ_top : μ Set.univ ≠ ⊤ := by simp
        have h4 : μ.real (A ∪ C) ≤ μ.real Set.univ :=
          (ENNReal.toReal_le_toReal h_ne_top h_univ_top).mpr h
        simpa [measure_univ] using h4
      linarith
    have h_nonempty : (A ∩ C).Nonempty := by
      by_contra h
      have h_empty : A ∩ C = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using h
      rw [h_empty] at h_intersection
      simp [measure_empty] at h_intersection <;> linarith
    rcases h_nonempty with ⟨v, hv⟩
    exact ⟨v, hv.1, hv.2⟩

  rcases h_exists with ⟨v, hv_good_density, hv_mass⟩

  -- Construct subfamily
  classical
  let selected : Finset (Fin T.card) := Finset.univ.filter (fun i => v i)
  let T' : TubeSubfamily T := TubeSubfamily.fromFinset T selected

  refine ⟨T', ?_, ?_, ?_⟩

  · -- deltaMax bound
    have h_density_control : ∀ K ∈ net.testSets, T'.family.toBodyFamily.density K ≤ (10 : ENNReal) * target := by
      intro K hK
      have h_not_bad : v ∉ badDensity K := by
        intro h
        have h_in_union : v ∈ (⋃ K ∈ net.testSets, badDensity K) := by
          simpa [Finset.mem_biUnion] using ⟨K, hK, h⟩
        have h_in_badUnion : v ∈ badCount ∪ (⋃ K ∈ net.testSets, badDensity K) := Or.inr h_in_union
        exact hv_good_density h_in_badUnion
      let s := T.toBodyFamily.containedIndices K
      let selected_s := selected ∩ s
      have hK_vol_ne_top : volume K ≠ ⊤ := net.testSets_volume_ne_top K hK
      have hK_vol_pos : 0 < volume K := net.testSets_volume_pos K hK
      have h_selected_mass_le : selectedVolumeMass Vreal s v < (10 : ℝ) * target.toReal * (volume K).toReal := by
        simpa [badDensity] using h_not_bad
      have h_body_vol2 : ∀ j, (T.toBodyFamily.body j).volume = V := by
        intro j
        have h5 : (T.toBodyFamily.body j).volume = (T.tube j).volume := by rfl
        rw [h5, h_vol_eq j]
      -- Step 1: selectedVolumeMass = Vreal * selected_s.card
      have h1 : selectedVolumeMass Vreal s v = Vreal * (selected_s.card : ℝ) := by
        have h1a : selectedVolumeMass Vreal s v = Vreal * ∑ i ∈ s, coordIndicator i v := by
          simp [selectedVolumeMass, coordVolumeIndicator, Finset.mul_sum] <;> ring
        rw [h1a]
        have h1b : ∑ i ∈ s, coordIndicator i v = (selected_s.card : ℝ) := by
          have h : ∑ i ∈ s, coordIndicator i v = (s.filter (fun i => v i)).card := by
            simp [coordIndicator, Finset.sum_ite] <;> norm_cast
          rw [h]
          have h2 : s.filter (fun i => v i) = selected_s := by
            ext x
            simp [selected_s, selected, Finset.mem_filter]
            <;> tauto
          rw [h2] <;> norm_cast
        rw [h1b] <;> ring
      rw [h1] at h_selected_mass_le
      -- Step 2: subfamily containedMass = selected_s.card * V
      have h2a : ∀ i : Fin T'.family.card, (T'.family.toBodyFamily.body i).volume = V := by
        intro i
        have h_eq : (T'.family.toBodyFamily.body i).volume = (T.tube (T'.embedding i)).volume := by rfl
        rw [h_eq, h_vol_eq (T'.embedding i)]
      let A := Finset.univ.filter (fun i : Fin T'.family.card => T'.embedding i ∈ s)
      have h2c_A : A.card ≤ selected_s.card := by
        classical
        let e := T'.embedding
        have h_image_subset : A.image e ⊆ selected_s := by
          intro y hy
          rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
          have h5 : e i ∈ s := (Finset.mem_filter.mp hi).2
          have h6 : e i ∈ selected := Finset.orderEmbOfFin_mem selected rfl i
          exact Finset.mem_inter.mpr ⟨h6, h5⟩
        have h_inj : Set.InjOn e A := fun x _ y _ h => e.inj' h
        have h_card_img : (A.image e).card = A.card := Finset.card_image_of_injOn h_inj
        rw [←h_card_img]
        exact Finset.card_le_card h_image_subset
      have h2c : (T'.family.toBodyFamily.containedIndices K).card ≤ selected_s.card := by
        have h_subset : T'.family.toBodyFamily.containedIndices K ⊆ A := by
          intro i hi
          have h1 : (T'.family.toBodyFamily.body i).carrier ⊆ K := BodyFamily.mem_containedIndices_iff.mp hi
          have h3 : (T'.family.toBodyFamily.body i).carrier = (T'.family.tube i).carrier := by rfl
          rw [h3, T'.tube_eq i] at h1
          have h4 : T'.embedding i ∈ s := BodyFamily.mem_containedIndices_iff.mpr h1
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h4⟩
        exact (Finset.card_le_card h_subset).trans h2c_A
      have h2 : T'.family.toBodyFamily.containedMass K ≤ (selected_s.card : ENNReal) * V := by
        have h_subset : T'.family.toBodyFamily.containedIndices K ⊆ A := by
          intro i hi
          have h1 : (T'.family.toBodyFamily.body i).carrier ⊆ K := BodyFamily.mem_containedIndices_iff.mp hi
          have h3 : (T'.family.toBodyFamily.body i).carrier = (T'.family.tube i).carrier := by rfl
          rw [h3, T'.tube_eq i] at h1
          have h4 : T'.embedding i ∈ s := BodyFamily.mem_containedIndices_iff.mpr h1
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h4⟩
        have h_sum1 : T'.family.toBodyFamily.containedMass K = ∑ i ∈ T'.family.toBodyFamily.containedIndices K, V := by
          dsimp only [BodyFamily.containedMass]
          apply Finset.sum_congr rfl
          intro i _
          exact h2a i
        rw [h_sum1]
        have h_sum2 : ∑ i ∈ T'.family.toBodyFamily.containedIndices K, V ≤ ∑ i ∈ A, V :=
          Finset.sum_le_sum_of_subset_of_nonneg h_subset (fun i _ _ => by positivity)
        have h_sum3 : ∑ i ∈ A, V = (A.card : ENNReal) * V := by
          rw [Finset.sum_const] <;> ring
        rw [h_sum3] at h_sum2
        have h_card : (A.card : ENNReal) ≤ (selected_s.card : ENNReal) := by exact_mod_cast h2c_A
        exact h_sum2.trans (by gcongr)
      -- Step 3: Convert real inequality to ENNReal
      have h31 : ((selected_s.card : ENNReal) * V).toReal = (selected_s.card : ℝ) * Vreal := by
        have h : ((selected_s.card : ENNReal) * V).toReal = (selected_s.card : ℝ) * V.toReal := by
          rw [ENNReal.toReal_mul]
          <;> norm_cast
        rw [h]
        <;> rfl
      have h32 : ((10 : ENNReal) * target * volume K).toReal = (10 : ℝ) * target.toReal * (volume K).toReal := by
        simp [ENNReal.toReal_mul]
        <;> ring
      have h3 : ((selected_s.card : ENNReal) * V).toReal ≤ ((10 : ENNReal) * target * volume K).toReal := by
        rw [h31, h32]
        have h_comm : Vreal * (selected_s.card : ℝ) = (selected_s.card : ℝ) * Vreal := by ring
        rw [h_comm] at h_selected_mass_le
        exact h_selected_mass_le.le
      have h_lhs_fin : ((selected_s.card : ENNReal) * V) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hV_ne_top
      have h_rhs_fin : ((10 : ENNReal) * target * volume K) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) htarget_ne_top) hK_vol_ne_top
      have h4 : (selected_s.card : ENNReal) * V ≤ (10 : ENNReal) * target * volume K :=
        (ENNReal.toReal_le_toReal h_lhs_fin h_rhs_fin).mp h3
      -- Step 4: Conclude density ≤ 10 * target
      have h5 : T'.family.toBodyFamily.containedMass K ≤ (10 : ENNReal) * target * volume K :=
        h2.trans h4
      have h6 : T'.family.toBodyFamily.density K ≤ (10 : ENNReal) * target := by
        have h_div : T'.family.toBodyFamily.density K = T'.family.toBodyFamily.containedMass K / volume K := by rfl
        rw [h_div]
        rw [ENNReal.div_le_iff hK_vol_pos.ne' hK_vol_ne_top]
        exact h5
      exact h6
    have h_ball : ∀ i, (T'.family.tube i).carrier ⊆ Metric.closedBall (0 : Point3) 10 := by
      intro i
      have h1 : (T'.family.tube i).carrier = (T.tube (T'.embedding i)).carrier := by
        rw [T'.tube_eq i]
      rw [h1]
      exact hT_support (T'.embedding i)
    have h_main : T'.family.toBodyFamily.deltaMax ≤ net.lossFactor * ((10 : ENNReal) * target) :=
      net.density_suffices T'.family h_ball ((10 : ENNReal) * target) h_density_control
    have h_assoc : net.lossFactor * ((10 : ENNReal) * target) = net.lossFactor * (10 : ENNReal) * target := by
      ring
    rw [h_assoc] at h_main
    exact h_main

  · -- cardinality bound
    have h_not_badCount : v ∉ badCount := by
      intro h
      have h_in : v ∈ (badCount ∪ (⋃ K ∈ net.testSets, badDensity K)) := Or.inl h
      exact hv_good_density h_in
    have h_count_lt : (selected.card : ℝ) < 2 * p * (T.card : ℝ) := by
      have h1 : (selected.card : ℝ) = ∑ i : Fin T.card, coordIndicator i v := by
        simp [selected, coordIndicator, Finset.sum_ite] <;> norm_cast
      rw [h1]
      simpa [badCount] using h_not_badCount
    have h_p_real : p = (target / D).toReal := by
      simp [p, ENNReal.toReal_div] <;> ring
    have hD_pos : 0 < D := lt_of_lt_of_le htarget_pos h_thin
    have hD_ne_zero : D ≠ 0 := hD_pos.ne'
    have h1 : (selected.card : ENNReal) ≤ 2 * (target / D) * T.enncard := by
      have h2 : (selected.card : ℝ) ≤ 2 * p * (T.card : ℝ) := by linarith
      have h_lhs : (selected.card : ENNReal).toReal = (selected.card : ℝ) := by simp
      have h_rhs : (2 * (target / D) * T.enncard).toReal = 2 * (target / D).toReal * (T.card : ℝ) := by
        simp [TubeFamily.enncard, ENNReal.toReal_mul, ENNReal.toReal_div] <;> ring
      have h3 : (selected.card : ENNReal).toReal ≤ (2 * (target / D) * T.enncard).toReal := by
        rw [h_lhs, h_rhs]
        have h4 : (selected.card : ℝ) ≤ 2 * (target / D).toReal * (T.card : ℝ) := by
          rw [h_p_real] at h2
          exact h2
        exact h4
      have h4 : (selected.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
      have h5 : (2 * (target / D) * T.enncard) ≠ ⊤ := by
        apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · simp
          · exact ENNReal.div_ne_top htarget_ne_top hD_ne_zero
        · exact ENNReal.natCast_ne_top _
      exact (ENNReal.toReal_le_toReal h4 h5).mp h3
    have h_card_eq : T'.family.card = selected.card := by
      exact Nat.add_zero
        (List.filter
          (fun b => decide ((fun i => v i = true) b))
          (List.finRange T.card)).length
    have h_enncard_eq : T'.family.enncard = (selected.card : ENNReal) := by
      simp [TubeFamily.enncard, h_card_eq]
    rw [h_enncard_eq]
    exact h1

  · -- mass retention
    have hD_pos2 : 0 < D := lt_of_lt_of_le htarget_pos h_thin
    have hD_ne_zero2 : D ≠ 0 := hD_pos2.ne'
    have h_vol_fin3 : ∀ i, volume (Z.carrier i) ≠ ⊤ := by
      intro i
      have h6 : volume (Z.carrier i) ≤ volume (T.tube i).carrier := measure_mono (Z.subset_body i)
      have h7 : volume (T.tube i).carrier = V := h_vol_eq i
      rw [h7] at h6
      exact ne_top_of_le_ne_top hV_ne_top h6
    have hZ_mass_fin : Z.mass ≠ ⊤ := by
      have h_le1 : Z.mass ≤ ∑ i : Fin T.card, V := by
        dsimp only [Shading.mass]
        apply Finset.sum_le_sum
        intro i _
        have h : volume (Z.carrier i) ≤ V := by
          have h6 : volume (Z.carrier i) ≤ volume (T.tube i).carrier := measure_mono (Z.subset_body i)
          have h7 : volume (T.tube i).carrier = V := h_vol_eq i
          rw [h7] at h6
          exact h6
        exact h
      have h_le2 : (∑ i : Fin T.card, V) = (T.card : ENNReal) * V := by
        have h_univ : (Finset.univ : Finset (Fin T.card)).card = T.card := by simp
        have h : (∑ i : Fin T.card, V) = (Finset.univ : Finset (Fin T.card)).card • V := Finset.sum_const _
        rw [h, h_univ]
        <;> simp [nsmul_eq_mul]
        <;> norm_cast
      have h_le : Z.mass ≤ (T.card : ENNReal) * V := h_le1.trans (le_of_eq h_le2)
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hV_ne_top) h_le
    -- selectedShading v = sum over selected of volume(Z.carrier i).toReal
    have h_sel_shading : selectedShading v = ∑ i ∈ selected, (volume (Z.carrier i)).toReal := by
      have h : selectedShading v = ∑ i : Fin T.card, (volume (Z.carrier i)).toReal * coordIndicator i v := by rfl
      rw [h]
      have h3 : ∀ i : Fin T.card, (volume (Z.carrier i)).toReal * coordIndicator i v = if v i then (volume (Z.carrier i)).toReal else 0 := by
        intro i
        simp [coordIndicator]
        <;> split_ifs <;> ring
      have h4 : ∑ i : Fin T.card, (volume (Z.carrier i)).toReal * coordIndicator i v =
          ∑ i : Fin T.card, (if v i then (volume (Z.carrier i)).toReal else 0) := by
        apply Finset.sum_congr rfl; intro i _; exact h3 i
      rw [h4]
      have h5 : ∑ i : Fin T.card, (if v i then (volume (Z.carrier i)).toReal else 0) =
          ∑ i ∈ selected, (volume (Z.carrier i)).toReal := by
        simp [selected, Finset.sum_ite, Finset.filter]
        <;> rfl
      exact h5
    -- (T'.restrictShading Z).mass = sum over selected of volume(Z.carrier i)
    have h_restrict_mass : (T'.restrictShading Z).mass = ∑ i ∈ selected, volume (Z.carrier i) := by
      have h1 : (T'.restrictShading Z).mass = ∑ i : Fin T'.family.card, volume (Z.carrier (T'.embedding i)) := by
        dsimp only [Shading.mass, TubeSubfamily.restrictShading]
        <;> rfl
      rw [h1]
      have h_inj : Function.Injective T'.embedding := fun x y h => T'.embedding.inj' h
      have h_inj_on : Set.InjOn T'.embedding (Finset.univ : Finset (Fin T'.family.card)) :=
        fun x _ y _ h => T'.embedding.inj' h
      have h_image : Finset.image T'.embedding Finset.univ = selected := by
        have h_sub : Finset.image T'.embedding Finset.univ ⊆ selected := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
          exact Finset.orderEmbOfFin_mem selected rfl i
        have h_card_eq : (Finset.image T'.embedding Finset.univ).card = selected.card := by
          have h1 : (Finset.image T'.embedding Finset.univ).card = (Finset.univ : Finset (Fin T'.family.card)).card :=
            Finset.card_image_of_injOn h_inj_on
          have h2 : (Finset.univ : Finset (Fin T'.family.card)).card = T'.family.card := by simp
          have h3 : T'.family.card = selected.card := by
            exact Nat.add_zero
              (List.filter
                (fun b => decide ((fun i => v i = true) b))
                (List.finRange T.card)).length
          rw [h1, h2, h3]
        exact Finset.eq_of_subset_of_card_le h_sub (by rw [h_card_eq])
      have h_sum_img : ∑ i : Fin T'.family.card, volume (Z.carrier (T'.embedding i)) =
          ∑ y ∈ Finset.image T'.embedding Finset.univ, volume (Z.carrier y) := by
        let s : Finset (Fin T'.family.card) := Finset.univ
        let f : Fin T'.family.card → Fin T.card := T'.embedding
        let g : Fin T.card → ENNReal := fun y => volume (Z.carrier y)
        have h_goal : ∑ x ∈ s, g (f x) = ∑ y ∈ Finset.image f s, g y := by
          exact (Finset.sum_image h_inj_on).symm
        simpa [s, f, g] using h_goal
      rw [h_sum_img, h_image]
    -- selectedShading v = ((T'.restrictShading Z).mass).toReal
    have h_real_eq : selectedShading v = ((T'.restrictShading Z).mass).toReal := by
      rw [h_sel_shading, h_restrict_mass]
      have h_sum_toReal : (∑ i ∈ selected, volume (Z.carrier i)).toReal =
          ∑ i ∈ selected, (volume (Z.carrier i)).toReal := by
        simp [ENNReal.toReal_sum, h_vol_fin3]
      exact h_sum_toReal.symm
    -- p = (target / D).toReal
    have h_p_real : p = (target / D).toReal := by
      simp [p, ENNReal.toReal_div]
      <;> ring
    -- p * Mreal / 2 = ((1/2 : ENNReal) * (target / D) * Z.mass).toReal
    have h_lhs_real : p * Mreal / 2 = ((1/2 : ENNReal) * (target / D) * Z.mass).toReal := by
      rw [h_p_real]
      have h_toReal : ((1/2 : ENNReal) * (target / D) * Z.mass).toReal =
          ((1/2 : ENNReal)).toReal * (target / D).toReal * Z.mass.toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul] <;> ring
      rw [h_toReal]
      <;> simp [Mreal] <;> ring
    -- Convert hv_mass to ENNReal
    rw [h_real_eq] at hv_mass
    rw [h_lhs_real] at hv_mass
    have h_fin1 : ((1/2 : ENNReal) * (target / D) * Z.mass) ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · simp
        · exact ENNReal.div_ne_top htarget_ne_top hD_ne_zero2
      · exact hZ_mass_fin
    have h_restrict_fin : (T'.restrictShading Z).mass ≠ ⊤ := by
      rw [h_restrict_mass]
      have h_le1 : (∑ i ∈ selected, volume (Z.carrier i)) ≤ ∑ i ∈ selected, V := by
        apply Finset.sum_le_sum
        intro i _
        have h : volume (Z.carrier i) ≤ V := by
          have h6 : volume (Z.carrier i) ≤ volume (T.tube i).carrier := measure_mono (Z.subset_body i)
          have h7 : volume (T.tube i).carrier = V := h_vol_eq i
          rw [h7] at h6
          exact h6
        exact h
      have h_le2 : (∑ i ∈ selected, V) = (selected.card : ENNReal) * V := by
        rw [Finset.sum_const] <;> ring
      have h_le : (∑ i ∈ selected, volume (Z.carrier i)) ≤ (selected.card : ENNReal) * V :=
        h_le1.trans (le_of_eq h_le2)
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hV_ne_top) h_le
    exact (ENNReal.toReal_le_toReal h_fin1 h_restrict_fin).mp hv_mass

/-- Backwards-compatible unit-ball specialization of
`probabilistic_thinning_bounded`. -/
lemma probabilistic_thinning
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {T : TubeFamily δ} (hT_nonempty : T.Nonempty) (hT_ball : T.IsInUnitBall)
    (Z : TubeShading T)
    (D : ENNReal) (hD : T.toBodyFamily.deltaMax ≤ D) (hD_ne_top : D ≠ ⊤)
    (η' : ℝ) (hη'_pos : 0 < η')
    (h_thin : Kakeya.realRpowENN δ (-η') ≤ D)
    (net : TubeDensityTestNet δ)
    (h_mu_ge_V : Kakeya.deltaTubeVolume δ ≤
      (Kakeya.realRpowENN δ (-η') / D) * Z.mass)
    (h_union_bound :
      let p := (Kakeya.realRpowENN δ (-η')).toReal / D.toReal
      (net.testSets.card : ℝ) *
          Real.exp (-(11 - Real.exp 1) *
            (Kakeya.realRpowENN δ (-η')).toReal) +
        Real.exp (-(3 - Real.exp 1) * p * (T.card : ℝ)) < 1 / 8) :
    ∃ (T' : TubeSubfamily T),
      T'.family.toBodyFamily.deltaMax ≤
          net.lossFactor * (10 : ENNReal) *
            Kakeya.realRpowENN δ (-η') ∧
      T'.family.enncard ≤
          2 * (Kakeya.realRpowENN δ (-η') / D) * T.enncard ∧
      (T'.restrictShading Z).mass ≥
        (1 / 2 : ENNReal) *
          (Kakeya.realRpowENN δ (-η') / D) * Z.mass := by
  apply probabilistic_thinning_bounded
    (hδ := hδ) (hδ1 := hδ1) (hT_nonempty := hT_nonempty)
    (hT_support := fun i => (hT_ball i).trans (by
      simpa [Kakeya.DeltaTube.unitBall] using
        (Metric.closedBall_subset_closedBall
          (x := (0 : Point3)) (by norm_num : (1 : ℝ) ≤ 10))))
    (Z := Z) (D := D) hD hD_ne_top η' hη'_pos h_thin net
    h_mu_ge_V h_union_bound

end Kakeya.Streamlined.ProbabilisticThinning
