module

/-
# Energy to Large-Mass Delta-Set Extraction

Given a probability measure ν on a finite δ-separated subset of ℝ with bounded
(2κ)-energy, extract a subset S that is an `IsRealDeltaSet` with exponent κ' < κ
and retains at least 3/4 of the original mass.

Uses multi-level weight decomposition to avoid the mass loss from thinning.
-/

public import MyLeanRepo.Energy.AverageProjectionEnergy
public import MyLeanRepo.Energy.FrostmanMeasureToDeltaSet
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.UnionDeltaSets
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ENNReal Set Classical Finset

set_option maxHeartbeats 500000

namespace robust_projection_main

/-- Good-set extraction with retention ≥ 3/4.

Uses threshold 4K in Markov, giving ν(Aᶜ) ≤ 1/4, hence ν(A) ≥ 3/4.
Pointwise Frostman bound: ν(closedBall x r) ≤ 4K · r^κ for x ∈ A. -/
lemma energy_to_frostman_good_set_34
    {δ κ K : ℝ} (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hκ_pos : 0 < κ) (hK_pos : 0 < K)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h_energy : rieszEnergy (2 * κ) (hδ := hδ) ν ≤ ENNReal.ofReal K) :
    ∃ (A : Set ℝ), MeasurableSet A ∧
      ν Aᶜ ≤ (1 / 4 : ENNReal) ∧
      ∀ (x : ℝ), x ∈ A → ∀ (r : ℝ), δ ≤ r → r ≤ 1 →
        ν (Metric.closedBall x r) ≤ ENNReal.ofReal (4 * K * r ^ κ) := by
  let s : ℝ := 2 * κ
  have hs_pos : 0 < s := by positivity
  let K_enr : ENNReal := ENNReal.ofReal K
  have hK_enr_pos : 0 < K_enr := ENNReal.ofReal_pos.mpr hK_pos
  have hK_enr_ne_top : K_enr ≠ ⊤ := ENNReal.ofReal_ne_top
  let threshold : ENNReal := 4 * K_enr
  have hth_pos : 0 < threshold := by positivity
  have hth_ne_top : threshold ≠ ⊤ := by
    simp only [threshold]; exact mul_ne_top (by simp) hK_enr_ne_top

  let f : ℝ → ENNReal := fun x =>
    ∫⁻ (y : ℝ), ENNReal.ofReal ((max (dist x y) δ) ^ (-s)) ∂ν
  have hf_meas : Measurable f := by fun_prop
  have h_total : ∫⁻ (x : ℝ), f x ∂ν ≤ K_enr := h_energy

  let A : Set ℝ := {x | f x ≤ threshold}
  have hA_meas : MeasurableSet A := hf_meas measurableSet_Iic

  have h_markov : ν {x | threshold ≤ f x} ≤ (∫⁻ (x : ℝ), f x ∂ν) / threshold :=
    MeasureTheory.meas_ge_le_lintegral_div (μ := ν) hf_meas.aemeasurable hth_pos.ne' hth_ne_top

  have h_div : K_enr / threshold = (1 / 4 : ENNReal) := by
    have h1 : K_enr / threshold = K_enr * threshold⁻¹ := by exact division_def K_enr threshold
    rw [h1]
    have h2 : threshold⁻¹ = (4 : ENNReal)⁻¹ * K_enr⁻¹ := by
      apply ENNReal.mul_inv <;> simp [hK_enr_pos.ne', hK_enr_ne_top]
    rw [h2]
    have h3 : K_enr * ((4 : ENNReal)⁻¹ * K_enr⁻¹) = (4 : ENNReal)⁻¹ * (K_enr * K_enr⁻¹) := by ring
    rw [h3]
    have h4 : K_enr * K_enr⁻¹ = 1 := ENNReal.mul_inv_cancel hK_enr_pos.ne' hK_enr_ne_top
    rw [h4, mul_one] <;> norm_num

  have h_compl_le : ν Aᶜ ≤ (1 / 4 : ENNReal) := by
    have h1 : Aᶜ ⊆ {x | threshold ≤ f x} := by
      intro x hx
      simp only [A, Set.mem_compl_iff, Set.mem_setOf_eq] at hx
      have h2 : ¬(f x ≤ threshold) := hx
      have h3 : threshold < f x := not_le.mp h2
      exact le_of_lt h3
    have h4 : (∫⁻ (x : ℝ), f x ∂ν) / threshold ≤ K_enr / threshold := by gcongr
    have h5 : ν {x | threshold ≤ f x} ≤ K_enr / threshold := h_markov.trans h4
    rw [h_div] at h5
    exact le_trans (measure_mono h1) h5

  -- Pointwise bound (reuse the exact same argument as energy_to_frostman_good_set)
  have h_pointwise : ∀ (x : ℝ), x ∈ A → ∀ (r : ℝ), δ ≤ r →
      ν (Metric.closedBall x r) ≤ threshold * ENNReal.ofReal (r ^ s) := by
    intro x hx r hr
    have hr_pos : 0 < r := by linarith
    let B := Metric.closedBall x r
    have hB_meas : MeasurableSet B := by exact measurableSet_closedBall
    let g : ℝ → ENNReal := fun y => ENNReal.ofReal ((max (dist x y) δ) ^ (-s))
    let c : ENNReal := ENNReal.ofReal (r ^ (-s))
    have h1 : ∀ (y : ℝ), y ∈ B → g y ≥ c := by
      intro y hy
      have h2 : dist y x ≤ r := Metric.mem_closedBall.mp hy
      have h2' : dist x y ≤ r := by rw [dist_comm] <;> exact h2
      have h3 : max (dist x y) δ ≤ r := max_le h2' (by linarith)
      have h4 : 0 < max (dist x y) δ := by positivity
      have h5 : r ^ (-s) ≤ (max (dist x y) δ) ^ (-s) := by
        have h_antitone : ∀ {a b : ℝ}, 0 < a → a ≤ b → b ^ (-s) ≤ a ^ (-s) := by
          intro a b ha hab
          have hb_nonneg : 0 ≤ b := by linarith
          have ha_nonneg : 0 ≤ a := by linarith
          have h8 : b ^ (-s) = (b⁻¹) ^ s := by
            have h9 : b ^ (-s) = (b ^ s)⁻¹ := by rw [← Real.rpow_neg hb_nonneg]
            have h10 : (b⁻¹) ^ s = (b ^ s)⁻¹ := by rw [Real.inv_rpow (by linarith)]
            rw [h9, ←h10]
          have h11 : a ^ (-s) = (a⁻¹) ^ s := by
            have h12 : a ^ (-s) = (a ^ s)⁻¹ := by rw [← Real.rpow_neg ha_nonneg]
            have h13 : (a⁻¹) ^ s = (a ^ s)⁻¹ := by rw [Real.inv_rpow (by linarith)]
            rw [h12, ←h13]
          rw [h8, h11]
          have h14 : b⁻¹ ≤ a⁻¹ := by gcongr
          have h15 : 0 ≤ b⁻¹ := by positivity
          exact Real.rpow_le_rpow h15 h14 (by linarith)
        exact h_antitone h4 h3
      exact ENNReal.ofReal_le_ofReal h5
    let h_ind : ℝ → ENNReal := fun y => if y ∈ B then c else 0
    have h_indic : ∫⁻ (y : ℝ), h_ind y ∂ν = c * ν B := by
      have h_eq : h_ind = fun y => Set.indicator B (fun _ => c) y := by
        funext y; simp [h_ind, Set.indicator_apply] <;> split_ifs
      rw [h_eq, lintegral_indicator hB_meas] <;> simp [lintegral_const]
    have h_mono : h_ind ≤ g := by
      intro y
      dsimp only [h_ind]
      by_cases hy : y ∈ B
      · simp [hy] <;> exact h1 y hy
      · simp [hy]
    have h_set_integral : c * ν B ≤ ∫⁻ (y : ℝ), g y ∂ν := by
      rw [←h_indic]; exact lintegral_mono h_mono
    have h9 : f x ≤ threshold := hx
    have h10 : c * ν B ≤ threshold := h_set_integral.trans h9
    have h_rs_nonneg : 0 ≤ r ^ s := by positivity
    have h_rneg_nonneg : 0 ≤ r ^ (-s) := by positivity
    have h11 : c * ENNReal.ofReal (r ^ s) = 1 := by
      have h_c : c = ENNReal.ofReal (r ^ (-s)) := rfl
      rw [h_c]
      have h12 : ENNReal.ofReal (r ^ (-s)) * ENNReal.ofReal (r ^ s) =
          ENNReal.ofReal ((r ^ (-s)) * (r ^ s)) := by
        have h_mul : ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b →
            ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal (a * b) := by
          intro a b ha hb; exact Eq.symm (ofReal_mul ha)
        exact h_mul (r ^ (-s)) (r ^ s) h_rneg_nonneg h_rs_nonneg
      rw [h12]
      have h13 : (r ^ (-s)) * (r ^ s) = 1 := by
        have h14 : r ^ (-s) * r ^ s = r ^ ((-s) + s) := by rw [← Real.rpow_add hr_pos]
        rw [h14]
        have h15 : (-s) + s = 0 := by ring
        rw [h15]
        simp
      rw [h13] <;> simp
    have h16 : ν B ≤ threshold * ENNReal.ofReal (r ^ s) := by
      calc
        ν B = (c * ENNReal.ofReal (r ^ s)) * ν B := by rw [h11] <;> ring
        _ = ENNReal.ofReal (r ^ s) * (c * ν B) := by ring
        _ ≤ ENNReal.ofReal (r ^ s) * threshold := by gcongr
        _ = threshold * ENNReal.ofReal (r ^ s) := by ring
    exact h16

  have h6_threshold : threshold = ENNReal.ofReal (4 * K) := by
    dsimp only [threshold, K_enr]
    have h_coe : (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) := by simp
    rw [h_coe]
    have h_mul : ENNReal.ofReal ((4 : ℝ) * K) = ENNReal.ofReal (4 : ℝ) * ENNReal.ofReal K :=
      ENNReal.ofReal_mul (by norm_num)
    exact h_mul.symm

  have h_final : ∀ (x : ℝ), x ∈ A → ∀ (r : ℝ), δ ≤ r → r ≤ 1 →
      ν (Metric.closedBall x r) ≤ ENNReal.ofReal (4 * K * r ^ κ) := by
    intro x hx r hrδ hr1
    have h1 := h_pointwise x hx r hrδ
    have hr_nonneg : 0 ≤ r := by linarith
    have h4 : κ ≤ s := by linarith [hκ_pos]
    have h2 : r ^ s ≤ r ^ κ := by
      by_cases h6 : r = 0
      · rw [h6]; have h7 : (0 : ℝ) ^ s = 0 := Real.zero_rpow (by linarith)
        have h8 : (0 : ℝ) ^ κ = 0 := Real.zero_rpow (by linarith)
        rw [h7, h8]
      · have h9 : 0 < r := by exact lt_of_le_of_ne hr_nonneg (Ne.symm h6)
        have h10 : r ^ s = r ^ κ * r ^ (s - κ) := by rw [← Real.rpow_add h9] <;> ring_nf
        rw [h10]
        have h11 : r ^ (s - κ) ≤ 1 := by apply Real.rpow_le_one <;> linarith
        have h12 : 0 ≤ r ^ κ := by positivity
        nlinarith
    have h_4K_nonneg : 0 ≤ 4 * K := by positivity
    have h_rs_nonneg : 0 ≤ r ^ s := by positivity
    have h7 : threshold * ENNReal.ofReal (r ^ s) ≤ ENNReal.ofReal (4 * K * r ^ κ) := by
      rw [h6_threshold]
      have h8 : ENNReal.ofReal (4 * K) * ENNReal.ofReal (r ^ s) =
          ENNReal.ofReal ((4 * K) * r ^ s) := by
        have h_mul : ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b →
            ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal (a * b) := by
          intro a b ha hb; exact Eq.symm (ofReal_mul ha)
        exact h_mul (4 * K) (r ^ s) h_4K_nonneg h_rs_nonneg
      rw [h8]
      have h10 : (4 * K) * r ^ s ≤ (4 * K) * r ^ κ := by gcongr <;> linarith
      exact ENNReal.ofReal_le_ofReal h10
    exact h1.trans h7

  exact ⟨A, hA_meas, h_compl_le, h_final⟩

/-- Parameterized good-set extraction.

Uses threshold L*K in Markov, giving ν(Aᶜ) ≤ 1/L.
Pointwise Frostman bound: ν(closedBall x r) ≤ L*K · r^κ for x ∈ A. -/
lemma energy_to_frostman_good_set_L
    {δ κ K L : ℝ} (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hκ_pos : 0 < κ) (hK_pos : 0 < K) (hL_pos : 0 < L) (hL_ge_one : 1 ≤ L)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h_energy : rieszEnergy (2 * κ) (hδ := hδ) ν ≤ ENNReal.ofReal K) :
    ∃ (A : Set ℝ), MeasurableSet A ∧
      ν Aᶜ ≤ ENNReal.ofReal (1 / L) ∧
      ∀ (x : ℝ), x ∈ A → ∀ (r : ℝ), δ ≤ r → r ≤ 1 →
        ν (Metric.closedBall x r) ≤ ENNReal.ofReal (L * K * r ^ κ) := by
  let s : ℝ := 2 * κ
  have hs_pos : 0 < s := by positivity
  let K_enr : ENNReal := ENNReal.ofReal K
  have hK_enr_pos : 0 < K_enr := ENNReal.ofReal_pos.mpr hK_pos
  have hK_enr_ne_top : K_enr ≠ ⊤ := ENNReal.ofReal_ne_top
  let L_enr : ENNReal := ENNReal.ofReal L
  have hL_enr_pos : 0 < L_enr := ENNReal.ofReal_pos.mpr hL_pos
  have hL_enr_ne_top : L_enr ≠ ⊤ := ENNReal.ofReal_ne_top
  let threshold : ENNReal := L_enr * K_enr
  have hth_pos : 0 < threshold := ENNReal.mul_pos hL_enr_pos.ne' hK_enr_pos.ne'
  have hth_ne_top : threshold ≠ ⊤ := mul_ne_top hL_enr_ne_top hK_enr_ne_top

  let f : ℝ → ENNReal := fun x =>
    ∫⁻ (y : ℝ), ENNReal.ofReal ((max (dist x y) δ) ^ (-s)) ∂ν
  have hf_meas : Measurable f := by fun_prop
  have h_total : ∫⁻ (x : ℝ), f x ∂ν ≤ K_enr := h_energy

  let A : Set ℝ := {x | f x ≤ threshold}
  have hA_meas : MeasurableSet A := hf_meas measurableSet_Iic

  have h_markov : ν {x | threshold ≤ f x} ≤ (∫⁻ (x : ℝ), f x ∂ν) / threshold :=
    MeasureTheory.meas_ge_le_lintegral_div (μ := ν) hf_meas.aemeasurable hth_pos.ne' hth_ne_top

  have h_div : K_enr / threshold = ENNReal.ofReal (1 / L) := by
    have h1 : K_enr / threshold = K_enr * threshold⁻¹ := by exact division_def K_enr threshold
    rw [h1]
    have h2 : threshold = L_enr * K_enr := by rfl
    rw [h2]
    have h3 : (L_enr * K_enr)⁻¹ = L_enr⁻¹ * K_enr⁻¹ := by
      apply ENNReal.mul_inv <;> simp [hL_enr_pos.ne', hL_enr_ne_top, hK_enr_pos.ne', hK_enr_ne_top]
    rw [h3]
    have h4 : K_enr * (L_enr⁻¹ * K_enr⁻¹) = L_enr⁻¹ * (K_enr * K_enr⁻¹) := by ring
    rw [h4]
    have h5 : K_enr * K_enr⁻¹ = 1 := ENNReal.mul_inv_cancel hK_enr_pos.ne' hK_enr_ne_top
    rw [h5, mul_one]
    have h6 : L_enr⁻¹ = ENNReal.ofReal (1 / L) := by
      dsimp only [L_enr]
      have h7 : (1 / L) = L⁻¹ := by field_simp
      rw [h7]
      exact (ENNReal.ofReal_inv_of_pos hL_pos).symm
    rw [h6]

  have h_compl_le : ν Aᶜ ≤ ENNReal.ofReal (1 / L) := by
    have h1 : Aᶜ ⊆ {x | threshold ≤ f x} := by
      intro x hx
      simp only [A, Set.mem_compl_iff, Set.mem_setOf_eq] at hx
      have h2 : ¬(f x ≤ threshold) := hx
      have h3 : threshold < f x := not_le.mp h2
      exact le_of_lt h3
    have h4 : (∫⁻ (x : ℝ), f x ∂ν) / threshold ≤ K_enr / threshold := by gcongr
    have h5 : ν {x | threshold ≤ f x} ≤ K_enr / threshold := h_markov.trans h4
    rw [h_div] at h5
    exact le_trans (measure_mono h1) h5

  -- Pointwise bound
  have h_pointwise : ∀ (x : ℝ), x ∈ A → ∀ (r : ℝ), δ ≤ r →
      ν (Metric.closedBall x r) ≤ threshold * ENNReal.ofReal (r ^ s) := by
    intro x hx r hr
    have hr_pos : 0 < r := by linarith
    let B := Metric.closedBall x r
    have hB_meas : MeasurableSet B := by exact measurableSet_closedBall
    let g : ℝ → ENNReal := fun y => ENNReal.ofReal ((max (dist x y) δ) ^ (-s))
    let c : ENNReal := ENNReal.ofReal (r ^ (-s))
    have h1 : ∀ (y : ℝ), y ∈ B → g y ≥ c := by
      intro y hy
      have h2 : dist y x ≤ r := Metric.mem_closedBall.mp hy
      have h2' : dist x y ≤ r := by rw [dist_comm] <;> exact h2
      have h3 : max (dist x y) δ ≤ r := max_le h2' (by linarith)
      have h4 : 0 < max (dist x y) δ := by positivity
      have h5 : r ^ (-s) ≤ (max (dist x y) δ) ^ (-s) := by
        have h_antitone : ∀ {a b : ℝ}, 0 < a → a ≤ b → b ^ (-s) ≤ a ^ (-s) := by
          intro a b ha hab
          have hb_nonneg : 0 ≤ b := by linarith
          have ha_nonneg : 0 ≤ a := by linarith
          have h8 : b ^ (-s) = (b⁻¹) ^ s := by
            have h9 : b ^ (-s) = (b ^ s)⁻¹ := by rw [← Real.rpow_neg hb_nonneg]
            have h10 : (b⁻¹) ^ s = (b ^ s)⁻¹ := by rw [Real.inv_rpow (by linarith)]
            rw [h9, ←h10]
          have h11 : a ^ (-s) = (a⁻¹) ^ s := by
            have h12 : a ^ (-s) = (a ^ s)⁻¹ := by rw [← Real.rpow_neg ha_nonneg]
            have h13 : (a⁻¹) ^ s = (a ^ s)⁻¹ := by rw [Real.inv_rpow (by linarith)]
            rw [h12, ←h13]
          rw [h8, h11]
          have h14 : b⁻¹ ≤ a⁻¹ := by gcongr
          have h15 : 0 ≤ b⁻¹ := by positivity
          exact Real.rpow_le_rpow h15 h14 (by linarith)
        exact h_antitone h4 h3
      exact ENNReal.ofReal_le_ofReal h5
    let h_ind : ℝ → ENNReal := fun y => if y ∈ B then c else 0
    have h_indic : ∫⁻ (y : ℝ), h_ind y ∂ν = c * ν B := by
      have h_eq : h_ind = fun y => Set.indicator B (fun _ => c) y := by
        funext y; simp [h_ind, Set.indicator_apply] <;> split_ifs
      rw [h_eq, lintegral_indicator hB_meas] <;> simp [lintegral_const]
    have h_mono : h_ind ≤ g := by
      intro y
      dsimp only [h_ind]
      by_cases hy : y ∈ B
      · simp [hy] <;> exact h1 y hy
      · simp [hy]
    have h_set_integral : c * ν B ≤ ∫⁻ (y : ℝ), g y ∂ν := by
      rw [←h_indic]; exact lintegral_mono h_mono
    have h9 : f x ≤ threshold := hx
    have h10 : c * ν B ≤ threshold := h_set_integral.trans h9
    have h_rs_nonneg : 0 ≤ r ^ s := by positivity
    have h_rneg_nonneg : 0 ≤ r ^ (-s) := by positivity
    have h11 : c * ENNReal.ofReal (r ^ s) = 1 := by
      dsimp only [c]
      have h12 : ENNReal.ofReal (r ^ (-s)) * ENNReal.ofReal (r ^ s) =
          ENNReal.ofReal ((r ^ (-s)) * (r ^ s)) := by
        have h_mul : ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b →
            ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal (a * b) := by
          intro a b ha hb; exact Eq.symm (ofReal_mul ha)
        exact h_mul (r ^ (-s)) (r ^ s) h_rneg_nonneg h_rs_nonneg
      rw [h12]
      have h13 : (r ^ (-s)) * (r ^ s) = 1 := by
        have h14 : r ^ (-s) * r ^ s = r ^ ((-s) + s) := by rw [← Real.rpow_add hr_pos]
        rw [h14]
        have h15 : (-s) + s = 0 := by ring
        rw [h15]
        simp
      rw [h13] <;> simp
    have h16 : ν B ≤ threshold * ENNReal.ofReal (r ^ s) := by
      calc
        ν B = (c * ENNReal.ofReal (r ^ s)) * ν B := by rw [h11] <;> ring
        _ = ENNReal.ofReal (r ^ s) * (c * ν B) := by ring
        _ ≤ ENNReal.ofReal (r ^ s) * threshold := by gcongr
        _ = threshold * ENNReal.ofReal (r ^ s) := by ring
    exact h16

  have h6_threshold : threshold = ENNReal.ofReal (L * K) := by
    dsimp only [threshold, L_enr, K_enr]
    have h_coe : ENNReal.ofReal L * ENNReal.ofReal K = ENNReal.ofReal (L * K) := by
      rw [← ENNReal.ofReal_mul (by linarith)]
      <;> ring
    exact h_coe

  have h_final : ∀ (x : ℝ), x ∈ A → ∀ (r : ℝ), δ ≤ r → r ≤ 1 →
      ν (Metric.closedBall x r) ≤ ENNReal.ofReal (L * K * r ^ κ) := by
    intro x hx r hrδ hr1
    have h1 := h_pointwise x hx r hrδ
    have hr_nonneg : 0 ≤ r := by linarith
    have h4 : κ ≤ s := by linarith [hκ_pos]
    have h2 : r ^ s ≤ r ^ κ := by
      by_cases h6 : r = 0
      · rw [h6]; have h7 : (0 : ℝ) ^ s = 0 := Real.zero_rpow (by linarith)
        have h8 : (0 : ℝ) ^ κ = 0 := Real.zero_rpow (by linarith)
        rw [h7, h8]
      · have h9 : 0 < r := by exact lt_of_le_of_ne hr_nonneg (Ne.symm h6)
        have h10 : r ^ s = r ^ κ * r ^ (s - κ) := by rw [← Real.rpow_add h9] <;> ring_nf
        rw [h10]
        have h11 : r ^ (s - κ) ≤ 1 := by apply Real.rpow_le_one <;> linarith
        have h12 : 0 ≤ r ^ κ := by positivity
        nlinarith
    have h_LK_nonneg : 0 ≤ L * K := by positivity
    have h_rs_nonneg : 0 ≤ r ^ s := by positivity
    have h7 : threshold * ENNReal.ofReal (r ^ s) ≤ ENNReal.ofReal (L * K * r ^ κ) := by
      rw [h6_threshold]
      have h8 : ENNReal.ofReal (L * K) * ENNReal.ofReal (r ^ s) =
          ENNReal.ofReal ((L * K) * r ^ s) := by
        have h_mul : ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b →
            ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal (a * b) := by
          intro a b ha hb; exact Eq.symm (ofReal_mul ha)
        exact h_mul (L * K) (r ^ s) h_LK_nonneg h_rs_nonneg
      rw [h8]
      have h10 : (L * K) * r ^ s ≤ (L * K) * r ^ κ := by gcongr <;> linarith
      exact ENNReal.ofReal_le_ofReal h10
    exact h1.trans h7

  exact ⟨A, hA_meas, h_compl_le, h_final⟩

/-- Ball-counting bound for a single weight level.

If S is δ-separated, all atomic weights w(a) lie in [m, 2m), and μ is a Frostman
measure with constant C supported on S, then the number of points of S in any
ball of radius r is bounded by (2C/W) * |S| * r^τ, where W is the total weight. -/
lemma weight_level_ball_counting
    {δ τ C : ℝ} {S : Finset ℝ} {μ : Measure ℝ}
    (hδ : 0 < δ) (hτ_pos : 0 < τ) (hC_pos : 0 < C)
    (hS_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y ≥ δ)
    (hμ_frost : IsDirectionFrostman δ τ C μ)
    (hμ_support : μ.support ⊆ (S : Set ℝ))
    (w : ℝ → ℝ) (hw : ∀ a ∈ S, μ {a} = ENNReal.ofReal (w a))
    (m : ℝ) (hm_pos : 0 < m)
    (h_weights : ∀ a ∈ S, m ≤ w a ∧ w a < 2 * m)
    (W : ℝ) (hW : ∑ a ∈ S, w a = W) (hW_pos : 0 < W) :
    ∀ (p : ℝ) (r : ℝ), δ ≤ r → r ≤ 1 → r ∈ dyadicScales →
      (S.filter (fun q => dist p q < r)).card ≤ (2 * C / W) * (S.card : ℝ) * r ^ τ := by
  intro p r hr_geδ hr_le1 hr_dyadic
  let S_I : Finset ℝ := S.filter (fun q => dist p q < r)
  have hS_I_sub : S_I ⊆ S := filter_subset _ _
  have h_weights_lower : ∀ q ∈ S_I, m ≤ w q := by
    intro q hq
    exact (h_weights q (hS_I_sub hq)).1
  have h_sum_lower : m * (S_I.card : ℝ) ≤ ∑ q ∈ S_I, w q := by
    have h : ∑ q ∈ S_I, m ≤ ∑ q ∈ S_I, w q := Finset.sum_le_sum h_weights_lower
    have h2 : ∑ q ∈ S_I, m = m * (S_I.card : ℝ) := by
      simp [Finset.sum_const] <;> ring
    rw [h2] at h
    exact h
  have h_in_interval : (S_I : Set ℝ) ⊆ Set.Icc (p - r) (p + r) := by
    intro q hq
    have h2 : dist p q < r := (Finset.mem_filter.mp hq).2
    have h3 : |p - q| < r := by simpa [Real.dist_eq] using h2
    rw [abs_lt] at h3
    constructor <;> linarith
  have h_finite_all : ∀ (s : Set ℝ), μ s ≠ ⊤ := by
    intro s
    have h1 : μ s ≤ μ Set.univ := measure_mono (by simp)
    have h2 : μ Set.univ = 1 := hμ_frost.1
    rw [h2] at h1
    exact ne_top_of_le_ne_top (by simp) h1
  have h_sum_real : ∑ q ∈ S_I, w q ≤ C * r ^ τ := by
    have h1 : μ (S_I : Set ℝ) = ∑ q ∈ S_I, μ {q} := robust_projection.finset_measure_sum μ
    have h2 : μ (S_I : Set ℝ) ≤ μ (Set.Icc (p - r) (p + r)) := measure_mono h_in_interval
    have h3 : (∑ q ∈ S_I, μ {q}).toReal ≤ (μ (Set.Icc (p - r) (p + r))).toReal := by
      rw [← h1] at *
      exact ENNReal.toReal_mono (h_finite_all _) h2
    have h4 : (∑ q ∈ S_I, μ {q}).toReal = ∑ q ∈ S_I, w q := by
      rw [ENNReal.toReal_sum (fun q _ => h_finite_all _)]
      apply Finset.sum_congr rfl
      intro q hq
      rw [hw q (hS_I_sub hq)]
      have h_nonneg : 0 ≤ w q := by linarith [(h_weights q (hS_I_sub hq)).1]
      rw [ENNReal.toReal_ofReal h_nonneg]
    have h5 : μ (Set.Icc (p - r) (p + r)) ≤ ENNReal.ofReal (C * r ^ τ) :=
      hμ_frost.2.2 p r hr_geδ hr_le1
    have h6 : (μ (Set.Icc (p - r) (p + r))).toReal ≤ (ENNReal.ofReal (C * r ^ τ)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top h5
    have h7_nonneg : 0 ≤ C * r ^ τ := by
      have h11 : 0 < r := by linarith
      have h12 : 0 < r ^ τ := by positivity
      exact (mul_pos hC_pos h12).le
    have h7 : (ENNReal.ofReal (C * r ^ τ)).toReal = C * r ^ τ := by
      rw [ENNReal.toReal_ofReal h7_nonneg]
    rw [← h4]
    exact le_trans h3 (le_trans h6 (by rw [h7]))
  have h6 : m * (S_I.card : ℝ) ≤ C * r ^ τ := le_trans h_sum_lower h_sum_real
  have hS_nonempty : S.Nonempty := by
    by_contra h
    have h' : S = ∅ := by simpa using h
    rw [h'] at hW
    have h0 : W = 0 := by
      have h1 : (0 : ℝ) = W := by simpa using hW
      exact h1.symm
    rw [h0] at hW_pos
    simp at hW_pos
  have h_card_pos : 0 < (S.card : ℝ) := by
    exact_mod_cast hS_nonempty.card_pos
  have h_weights_upper : ∀ q ∈ S, w q < 2 * m := fun q hq => (h_weights q hq).2
  have h_weights_le : ∀ q ∈ S, w q ≤ 2 * m := fun q hq => (h_weights_upper q hq).le
  have h_strict : ∃ i ∈ S, w i < 2 * m := by
    rcases hS_nonempty with ⟨i, hi⟩
    exact ⟨i, hi, h_weights_upper i hi⟩
  have hW_upper : W < 2 * m * (S.card : ℝ) := by
    rw [←hW]
    have h : ∑ q ∈ S, w q < ∑ q ∈ S, (2 * m) :=
      Finset.sum_lt_sum h_weights_le h_strict
    have h2 : ∑ q ∈ S, (2 * m) = 2 * m * (S.card : ℝ) := by
      simp [Finset.sum_const] <;> ring
    rw [h2] at h
    exact h
  have h7 : (S_I.card : ℝ) ≤ (C * r ^ τ) / m := by
    have h8 : m * (S_I.card : ℝ) ≤ C * r ^ τ := h6
    have h9 : (S_I.card : ℝ) = (m * (S_I.card : ℝ)) / m := by
      field_simp [hm_pos.ne'] <;> ring
    rw [h9]
    gcongr
  have h10 : 0 ≤ C * r ^ τ := by
    have h11 : 0 < r := by linarith
    have h12 : 0 < r ^ τ := by positivity
    exact (mul_pos hC_pos h12).le
  have h11 : 1 / m ≤ 2 * (S.card : ℝ) / W := by
    have h12 : W / (2 * (S.card : ℝ)) < m := by
      have h13 : W < 2 * m * (S.card : ℝ) := hW_upper
      have h14 : 0 < 2 * (S.card : ℝ) := by positivity
      calc
        W / (2 * (S.card : ℝ)) < (2 * m * (S.card : ℝ)) / (2 * (S.card : ℝ)) := by gcongr
        _ = m := by
          field_simp [h14.ne'] <;> ring
    have h15 : 0 < W / (2 * (S.card : ℝ)) := by positivity
    have h16 : 1 / m ≤ 1 / (W / (2 * (S.card : ℝ))) := by gcongr
    have h17 : 1 / (W / (2 * (S.card : ℝ))) = 2 * (S.card : ℝ) / W := by
      field_simp [hW_pos.ne', h_card_pos.ne'] <;> ring
    rw [h17] at h16
    exact h16
  calc (S_I.card : ℝ)
    ≤ (C * r ^ τ) / m := h7
  _ = C * r ^ τ * (1 / m) := by ring
  _ ≤ C * r ^ τ * (2 * (S.card : ℝ) / W) := by
    exact mul_le_mul_of_nonneg_left h11 h10
  _ = (2 * C / W) * (S.card : ℝ) * r ^ τ := by ring

/-- Direct conversion from comparable-weight Frostman measure to delta-set.

No exponent loss: the output delta-set has the same exponent τ as the Frostman
bound. Uses the fact that for δ-separated sets, covering number = cardinality. -/
lemma weight_level_to_delta_set_direct
    {δ τ C : ℝ} {S : Finset ℝ} {μ : Measure ℝ}
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales) (hδ_lt_one : δ < 1)
    (hτ_pos : 0 < τ) (hτ_le_one : τ ≤ 1) (hC_pos : 0 < C)
    (hS_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y ≥ δ)
    (hS_nonempty : S.Nonempty)
    (hμ_frost : IsDirectionFrostman δ τ C μ)
    (hμ_support : μ.support ⊆ (S : Set ℝ))
    (w : ℝ → ℝ) (hw : ∀ a ∈ S, μ {a} = ENNReal.ofReal (w a))
    (m : ℝ) (hm_pos : 0 < m)
    (h_weights : ∀ a ∈ S, m ≤ w a ∧ w a < 2 * m)
    (W : ℝ) (hW : ∑ a ∈ S, w a = W) (hW_pos : 0 < W) :
    IsRealDeltaSet δ τ (2 * C / W) (S : Set ℝ) := by
  let P : Set (EuclideanSpace ℝ (Fin 1)) := realLineCopy (S : Set ℝ)
  have hS_bdd : Bornology.IsBounded (S : Set ℝ) := by
    have h1 : BddAbove (S : Set ℝ) := Finset.bddAbove S
    have h2 : BddBelow (S : Set ℝ) := Finset.bddBelow S
    exact h1.isBounded h2
  have hP_bdd : Bornology.IsBounded P := by
    have h : P = realLineCopy (S : Set ℝ) := rfl
    rw [h]
    exact ProductLikeIncidence.productLikeRealLineCopy_bounded hS_bdd
  have hP_nonempty : P.Nonempty := by
    rcases hS_nonempty with ⟨x, hx⟩
    let p : EuclideanSpace ℝ (Fin 1) := (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun (_ : Fin 1) => x)
    refine ⟨p, ?_⟩
    have h_goal : p 0 ∈ (S : Set ℝ) := by simpa [p] using hx
    simpa [P, realLineCopy] using h_goal
  have hC'_pos : 0 < 2 * C / W := by positivity
  have h_cover_eq : ENat.toENNReal (dyadicCoveringNumber δ P) = (S.card : ENNReal) := by
    have h := robust_projection.covering_number_eq_card_of_separated hδ hS_sep
    exact_mod_cast h
  have h_finite_all : ∀ (s : Set ℝ), μ s ≠ ⊤ := by
    intro s
    have h1 : μ s ≤ μ Set.univ := measure_mono (by simp)
    have h2 : μ Set.univ = 1 := hμ_frost.1
    rw [h2] at h1
    exact ne_top_of_le_ne_top (by simp) h1
  have h_main_bound : ∀ (r : ℝ) (Q : Set (EuclideanSpace ℝ (Fin 1))),
      r ∈ dyadicScales → Q ∈ dyadicCubes 1 r → δ ≤ r → r ≤ 1 →
      ENat.toENNReal (dyadicCoveringNumber δ (P ∩ Q)) ≤
        ENNReal.ofReal (2 * C / W) * ENat.toENNReal (dyadicCoveringNumber δ P) *
          ENNReal.ofReal (r ^ τ) := by
    intro r Q hr hQ hδr hr1
    rcases hQ with ⟨k, rfl⟩
    let a : ℝ := r * (k 0 : ℝ)
    let b : ℝ := r * ((k 0 : ℝ) + 1)
    have hrb_pos : 0 < r := by
      rcases hr with ⟨n, rfl⟩
      positivity
    let I : Set ℝ := Set.Ico a b
    let S_Q : Finset ℝ := S.filter (fun x => x ∈ I)
    have h_sep_Q : ∀ p ∈ S_Q, ∀ q ∈ S_Q, p ≠ q → dist p q ≥ δ := by
      intro p hp q hq
      have hp' : p ∈ S := (Finset.mem_filter.mp hp).1
      have hq' : q ∈ S := (Finset.mem_filter.mp hq).1
      exact hS_sep p hp' q hq'
    have h_inter_eq : P ∩ dyadicCube r k = realLineCopy ((S_Q : Set ℝ)) := by
      ext x
      simp only [P, realLineCopy, S_Q, I, dyadicCube, Set.mem_inter_iff, Set.mem_setOf_eq,
        Finset.mem_filter]
      <;> constructor <;> intro h <;> aesop <;> tauto
    have h_cover_Q_eq : ENat.toENNReal (dyadicCoveringNumber δ (P ∩ dyadicCube r k)) =
        (S_Q.card : ENNReal) := by
      rw [h_inter_eq]
      have h := robust_projection.covering_number_eq_card_of_separated hδ h_sep_Q
      exact_mod_cast h
    let S_Icc : Finset ℝ := S.filter (fun x => x ∈ Set.Icc a b)
    have hS_Q_sub : S_Q ⊆ S_Icc := by
      intro x hx
      have hxi : x ∈ I := (Finset.mem_filter.mp hx).2
      have h_in_Icc : x ∈ Set.Icc a b := by
        exact ⟨hxi.1, le_of_lt hxi.2⟩
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, h_in_Icc⟩
    -- Interval bound via Frostman: m * |S_Icc| ≤ μ(Icc(a,b)) ≤ C * r^τ
    have h_weights_lower : ∀ q ∈ S_Icc, m ≤ w q := by
      intro q hq
      exact (h_weights q ((Finset.mem_filter.mp hq).1)).1
    have h_sum_lower : m * (S_Icc.card : ℝ) ≤ ∑ q ∈ S_Icc, w q := by
      have h : ∑ q ∈ S_Icc, m ≤ ∑ q ∈ S_Icc, w q := Finset.sum_le_sum h_weights_lower
      have h2 : ∑ q ∈ S_Icc, m = m * (S_Icc.card : ℝ) := by
        simp [Finset.sum_const] <;> ring
      rw [h2] at h
      exact h
    have h_in_interval : (S_Icc : Set ℝ) ⊆ Set.Icc a b := by
      intro q hq
      exact (Finset.mem_filter.mp hq).2
    have h_sum_real : ∑ q ∈ S_Icc, w q ≤ C * r ^ τ := by
      have h1 : μ (S_Icc : Set ℝ) = ∑ q ∈ S_Icc, μ {q} := robust_projection.finset_measure_sum μ
      have h2 : μ (S_Icc : Set ℝ) ≤ μ (Set.Icc a b) := measure_mono h_in_interval
      have h3 : (∑ q ∈ S_Icc, μ {q}).toReal ≤ (μ (Set.Icc a b)).toReal := by
        rw [← h1] at *
        exact ENNReal.toReal_mono (h_finite_all _) h2
      have h4 : (∑ q ∈ S_Icc, μ {q}).toReal = ∑ q ∈ S_Icc, w q := by
        rw [ENNReal.toReal_sum (fun q _ => h_finite_all _)]
        apply Finset.sum_congr rfl
        intro q hq
        rw [hw q (Finset.mem_filter.mp hq |>.1)]
        have h_nonneg : 0 ≤ w q := by linarith [(h_weights q (Finset.mem_filter.mp hq |>.1)).1]
        rw [ENNReal.toReal_ofReal h_nonneg]
      have h_sub : Set.Icc a b ⊆ Set.Icc (a - r) (a + r) := by
        intro z hz
        have h1 : a ≤ z := hz.1
        have h2 : z ≤ b := hz.2
        have h3 : b = a + r := by simp [b, a] <;> ring
        constructor <;> linarith
      have h5 : μ (Set.Icc a b) ≤ ENNReal.ofReal (C * r ^ τ) := by
        have h6 : μ (Set.Icc a b) ≤ μ (Set.Icc (a - r) (a + r)) := measure_mono h_sub
        have h7 : μ (Set.Icc (a - r) (a + r)) ≤ ENNReal.ofReal (C * r ^ τ) :=
          hμ_frost.2.2 a r hδr hr1
        exact le_trans h6 h7
      have h6 : (μ (Set.Icc a b)).toReal ≤ (ENNReal.ofReal (C * r ^ τ)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h5
      have h7_nonneg : 0 ≤ C * r ^ τ := by
        have h11 : 0 < r ^ τ := by positivity
        exact (mul_pos hC_pos h11).le
      have h7 : (ENNReal.ofReal (C * r ^ τ)).toReal = C * r ^ τ := by
        rw [ENNReal.toReal_ofReal h7_nonneg]
      rw [← h4]
      exact le_trans h3 (le_trans h6 (by rw [h7]))
    have h6 : m * (S_Icc.card : ℝ) ≤ C * r ^ τ := le_trans h_sum_lower h_sum_real
    have hS_nonempty' : S.Nonempty := hS_nonempty
    have h_card_pos : 0 < (S.card : ℝ) := by exact_mod_cast hS_nonempty'.card_pos
    have h_weights_upper : ∀ q ∈ S, w q < 2 * m := fun q hq => (h_weights q hq).2
    have hW_upper : W < 2 * m * (S.card : ℝ) := by
      rw [←hW]
      have h_strict : ∃ i ∈ S, w i < 2 * m := by
        rcases hS_nonempty' with ⟨i, hi⟩
        exact ⟨i, hi, h_weights_upper i hi⟩
      have h_le : ∀ q ∈ S, w q ≤ 2 * m := fun q hq => (h_weights_upper q hq).le
      have h : ∑ q ∈ S, w q < ∑ q ∈ S, (2 * m) := Finset.sum_lt_sum h_le h_strict
      have h2 : ∑ q ∈ S, (2 * m) = 2 * m * (S.card : ℝ) := by
        simp [Finset.sum_const] <;> ring
      rw [h2] at h
      exact h
    have h11 : 1 / m ≤ 2 * (S.card : ℝ) / W := by
      have h12 : W / (2 * (S.card : ℝ)) < m := by
        have h13 : W < 2 * m * (S.card : ℝ) := hW_upper
        have h14 : 0 < 2 * (S.card : ℝ) := by positivity
        calc
          W / (2 * (S.card : ℝ)) < (2 * m * (S.card : ℝ)) / (2 * (S.card : ℝ)) := by gcongr
          _ = m := by field_simp [h14.ne'] <;> ring
      have h15 : 0 < W / (2 * (S.card : ℝ)) := by positivity
      have h16 : 1 / m ≤ 1 / (W / (2 * (S.card : ℝ))) := by gcongr
      have h17 : 1 / (W / (2 * (S.card : ℝ))) = 2 * (S.card : ℝ) / W := by
        field_simp [hW_pos.ne', h_card_pos.ne'] <;> ring
      rw [h17] at h16
      exact h16
    have h10 : 0 ≤ C * r ^ τ := by
      have h11 : 0 < r ^ τ := by positivity
      exact (mul_pos hC_pos h11).le
    have h_card_bound : (S_Icc.card : ℝ) ≤ (2 * C / W) * (S.card : ℝ) * r ^ τ := by
      have h7 : (S_Icc.card : ℝ) ≤ (C * r ^ τ) / m := by
        have h8 : m * (S_Icc.card : ℝ) ≤ C * r ^ τ := h6
        have h9 : (S_Icc.card : ℝ) = (m * (S_Icc.card : ℝ)) / m := by
          field_simp [hm_pos.ne'] <;> ring
        rw [h9]
        gcongr
      calc (S_Icc.card : ℝ)
        ≤ (C * r ^ τ) / m := h7
      _ = C * r ^ τ * (1 / m) := by ring
      _ ≤ C * r ^ τ * (2 * (S.card : ℝ) / W) := by exact mul_le_mul_of_nonneg_left h11 h10
      _ = (2 * C / W) * (S.card : ℝ) * r ^ τ := by ring
    have h_card_Q_bound : S_Q.card ≤ S_Icc.card := Finset.card_le_card hS_Q_sub
    have h_final : (S_Q.card : ℝ) ≤ (2 * C / W) * (S.card : ℝ) * r ^ τ := by
      calc (S_Q.card : ℝ) ≤ (S_Icc.card : ℝ) := by exact_mod_cast h_card_Q_bound
        _ ≤ (2 * C / W) * (S.card : ℝ) * r ^ τ := h_card_bound
    rw [h_cover_Q_eq, h_cover_eq]
    have h_pos_r : 0 ≤ r ^ τ := by positivity
    have h5 : (S_Q.card : ENNReal) ≤
        ENNReal.ofReal ((2 * C / W) * (S.card : ℝ) * r ^ τ) := by
      have h_eq_cast : (S_Q.card : ENNReal) = ENNReal.ofReal (S_Q.card : ℝ) := by norm_cast
      rw [h_eq_cast]
      have h51 : 0 ≤ (S_Q.card : ℝ) := by positivity
      exact ENNReal.ofReal_le_ofReal h_final
    have h6 : ENNReal.ofReal ((2 * C / W) * (S.card : ℝ) * r ^ τ) =
        ENNReal.ofReal (2 * C / W) * (S.card : ENNReal) * ENNReal.ofReal (r ^ τ) := by
      have h7 : 0 ≤ 2 * C / W := by positivity
      have h8 : 0 ≤ (S.card : ℝ) := by positivity
      have h9 : 0 ≤ r ^ τ := by positivity
      calc
        ENNReal.ofReal ((2 * C / W) * (S.card : ℝ) * r ^ τ)
          = ENNReal.ofReal ((2 * C / W) * ((S.card : ℝ) * r ^ τ)) := by ring_nf
        _ = ENNReal.ofReal (2 * C / W) * ENNReal.ofReal ((S.card : ℝ) * r ^ τ) := by
          rw [ENNReal.ofReal_mul h7]
        _ = ENNReal.ofReal (2 * C / W) * ((S.card : ENNReal) * ENNReal.ofReal (r ^ τ)) := by
          rw [ENNReal.ofReal_mul h8] <;> norm_cast <;> ring
        _ = ENNReal.ofReal (2 * C / W) * (S.card : ENNReal) * ENNReal.ofReal (r ^ τ) := by ring
    rw [h6] at h5
    exact h5
  have hτ_nonneg : 0 ≤ τ := by linarith
  have hτ_le_one' : τ ≤ (1 : ℕ) := by exact_mod_cast hτ_le_one
  have h_main : @IsDeltaSCSet 1 δ τ (2 * C / W) P :=
    ⟨hP_bdd, hP_nonempty, by norm_num, hδ_dyadic, hδ, hτ_nonneg, hτ_le_one', hC'_pos, h_main_bound⟩
  exact h_main

/-- Cardinality bound: a δ-separated subset of [0,1] has at most 2/δ points. -/
lemma card_bound_delta_separated {δ : ℝ} (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    {A : Finset ℝ} (hA_sep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → dist x y ≥ δ)
    (hA_sub : (A : Set ℝ) ⊆ Set.Icc 0 1) :
    (A.card : ℝ) ≤ 2 / δ := by
  let f : ℝ → ℕ := fun x => (⌊x / δ⌋).toNat
  have h_nonneg1 : ∀ x ∈ (A : Set ℝ), 0 ≤ ⌊x / δ⌋ := by
    intro x hx
    have h3 : 0 ≤ x := (hA_sub hx).1
    apply Int.floor_nonneg.mpr
    positivity
  have h_inj : Set.InjOn f (A : Set ℝ) := by
    intro x hx y hy hxy
    have h1 : ⌊x / δ⌋ = ⌊y / δ⌋ := by
      have h2 : (⌊x / δ⌋).toNat = (⌊y / δ⌋).toNat := hxy
      have hnx : 0 ≤ ⌊x / δ⌋ := h_nonneg1 x hx
      have hny : 0 ≤ ⌊y / δ⌋ := h_nonneg1 y hy
      have h3 : ((⌊x / δ⌋).toNat : ℤ) = ((⌊y / δ⌋).toNat : ℤ) := by exact_mod_cast h2
      rw [Int.toNat_of_nonneg hnx, Int.toNat_of_nonneg hny] at h3
      exact h3
    have h1' : (⌊x / δ⌋ : ℝ) = (⌊y / δ⌋ : ℝ) := by exact_mod_cast h1
    have h21 : (⌊x / δ⌋ : ℝ) ≤ x / δ := Int.floor_le (x / δ)
    have h22 : x / δ < (⌊x / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
    have h23 : (⌊y / δ⌋ : ℝ) ≤ y / δ := Int.floor_le (y / δ)
    have h24 : y / δ < (⌊y / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one (y / δ)
    have h23' : (⌊x / δ⌋ : ℝ) ≤ y / δ := by
      calc (⌊x / δ⌋ : ℝ) = (⌊y / δ⌋ : ℝ) := h1'
        _ ≤ y / δ := h23
    have h24' : y / δ < (⌊x / δ⌋ : ℝ) + 1 := by
      calc y / δ < (⌊y / δ⌋ : ℝ) + 1 := h24
        _ = (⌊x / δ⌋ : ℝ) + 1 := by rw [←h1']
    have h3 : |x / δ - y / δ| < 1 := by
      rw [abs_lt] <;> constructor <;> linarith
    have h4 : |x - y| < δ := by
      have h5 : |x / δ - y / δ| = |x - y| / δ := by
        have h6 : x / δ - y / δ = (x - y) / δ := by ring
        rw [h6, abs_div, abs_of_pos hδ]
      rw [h5] at h3
      exact (div_lt_one hδ).mp h3
    by_cases h7 : x ≠ y
    · have h8 : dist x y ≥ δ := hA_sep x hx y hy h7
      have h9 : dist x y = |x - y| := by simp [Real.dist_eq]
      rw [h9] at h8
      linarith
    · exact Classical.not_not.mp h7
  have h1 : (A.card : ℝ) = (Finset.image f A).card := by
    exact_mod_cast (Finset.card_image_of_injOn h_inj).symm
  rw [h1]
  have h_nonneg_floor : 0 ≤ ⌊1 / δ⌋ := by
    apply Int.floor_nonneg.mpr
    have h : 0 ≤ 1 / δ := by positivity
    exact h
  let N : ℕ := (⌊1 / δ⌋).toNat
  have hN_eq : (N : ℝ) = (⌊1 / δ⌋ : ℝ) := by
    have h : (N : ℤ) = ⌊1 / δ⌋ := Int.toNat_of_nonneg h_nonneg_floor
    exact_mod_cast h
  have h2 : Finset.image f A ⊆ Finset.range (N + 1) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    have h3 : 0 ≤ x := (hA_sub hx).1
    have h4 : x ≤ 1 := (hA_sub hx).2
    have h5 : 0 ≤ ⌊x / δ⌋ := h_nonneg1 x hx
    have h6 : ⌊x / δ⌋ ≤ ⌊1 / δ⌋ := Int.floor_mono (by gcongr)
    have h7 : (⌊x / δ⌋).toNat ≤ N := by
      omega
    have h8 : (⌊x / δ⌋).toNat < N + 1 := by omega
    exact Finset.mem_range.mpr h8
  have h3 : (Finset.image f A).card ≤ (Finset.range (N + 1)).card :=
    Finset.card_le_card h2
  have h4 : (Finset.range (N + 1)).card = N + 1 := by simp
  have h5 : ((Finset.image f A).card : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show (Finset.image f A).card ≤ N + 1 from by rw [h4] at h3; exact h3)
  have h6 : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by simp
  rw [h6] at h5
  have h7 : (N : ℝ) + 1 ≤ 1 / δ + 1 := by
    rw [hN_eq]
    have h8 : (⌊1 / δ⌋ : ℝ) ≤ 1 / δ := Int.floor_le (1 / δ)
    linarith
  have h9 : 1 / δ + 1 ≤ 2 / δ := by
    have h10 : 1 ≤ 1 / δ := (one_le_div hδ).mpr hδ_le_one
    calc 1 / δ + 1 ≤ 1 / δ + 1 / δ := by gcongr
      _ = 2 / δ := by ring
  have h_final : ((Finset.image f A).card : ℝ) ≤ 2 / δ := by
    calc ((Finset.image f A).card : ℝ)
      ≤ (N : ℝ) + 1 := h5
    _ ≤ 1 / δ + 1 := h7
    _ ≤ 2 / δ := h9
  exact h_final

/-- Riesz energy of a probability measure on [0,1] is at least 1. -/
lemma rieszEnergy_ge_one {δ κ : ℝ} (hδ : 0 < δ) (hδ_lt_one : δ < 1) (hκ_pos : 0 < κ)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν_supp : ν.support ⊆ Set.Icc 0 1) :
    (1 : ENNReal) ≤ rieszEnergy (2 * κ) (hδ := hδ) ν := by
  let f : ℝ → ℝ → ENNReal := fun x y =>
    ENNReal.ofReal ((max (dist x y) δ) ^ (-2 * κ))
  have hIcc_null : ν (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
    have h1 : (Set.Icc (0 : ℝ) 1)ᶜ ⊆ ν.supportᶜ := by
      intro x hx h2
      exact hx (hν_supp h2)
    exact measure_mono_null h1 (by exact Measure.measure_compl_support)
  have h_ae_Icc : ∀ᵐ x ∂ν, x ∈ Set.Icc (0 : ℝ) 1 := by
    have h_set : {x : ℝ | x ∉ Set.Icc (0 : ℝ) 1} = (Set.Icc (0 : ℝ) 1)ᶜ := by ext x; simp
    have h2 : ν {x : ℝ | x ∉ Set.Icc (0 : ℝ) 1} = 0 := by rw [h_set]; exact hIcc_null
    rw [ae_iff]; exact h2
  have h_kernel_ge_one : ∀ (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 →
      ∀ (y : ℝ), y ∈ Set.Icc (0 : ℝ) 1 → (1 : ENNReal) ≤ f x y := by
    intro x hx y hy
    have h_dist : dist x y ≤ 1 := by
      simpa [dist_eq_norm, Real.norm_eq_abs] using
        show |x - y| ≤ 1 from by
          have hx1 : 0 ≤ x := hx.1
          have hx2 : x ≤ 1 := hx.2
          have hy1 : 0 ≤ y := hy.1
          have hy2 : y ≤ 1 := hy.2
          rw [abs_le] <;> constructor <;> linarith
    have h_max : max (dist x y) δ ≤ 1 := max_le h_dist (by linarith)
    have h_pos : 0 < max (dist x y) δ := by positivity
    have h_exp_neg : -2 * κ < 0 := by linarith
    have h : (1 : ℝ) ≤ (max (dist x y) δ) ^ (-2 * κ) := by
      have h2 : (max (dist x y) δ) ≤ 1 := h_max
      have h3 : 0 < max (dist x y) δ := h_pos
      have h4 : (max (dist x y) δ) ^ (-2 * κ) ≥ 1 :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos h_pos h_max (by linarith)
      exact h4
    have h5 : (1 : ENNReal) ≤ f x y := by
      dsimp only [f]
      convert ENNReal.ofReal_le_ofReal h <;> simp
    exact h5
  have h_inner : ∀ (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 →
      (1 : ENNReal) ≤ ∫⁻ y, f x y ∂ν := by
    intro x hx
    have h_ae : ∀ᵐ y ∂ν, (1 : ENNReal) ≤ f x y := by
      filter_upwards [h_ae_Icc] with y hy
      exact h_kernel_ge_one x hx y hy
    have h : ∫⁻ y, (1 : ENNReal) ∂ν ≤ ∫⁻ y, f x y ∂ν :=
      lintegral_mono_ae h_ae
    have h2 : ∫⁻ y, (1 : ENNReal) ∂ν = 1 := by
      simp [IsProbabilityMeasure.measure_univ]
    rw [h2] at h
    exact h
  have h_outer : ∀ᵐ x ∂ν, (1 : ENNReal) ≤ ∫⁻ y, f x y ∂ν := by
    filter_upwards [h_ae_Icc] with x hx
    exact h_inner x hx
  have h : ∫⁻ x, (1 : ENNReal) ∂ν ≤ ∫⁻ x, (∫⁻ y, f x y ∂ν) ∂ν :=
    lintegral_mono_ae h_outer
  simpa [rieszEnergy, f, lintegral_one, IsProbabilityMeasure.measure_univ] using h

/-- Riesz energy of a finite-support measure as a double sum. -/
lemma rieszEnergy_finite_sum {δ κ : ℝ} (hδ : 0 < δ) (hκ_pos : 0 < κ)
    {A_fin : Finset ℝ} {μ : Measure ℝ} [SFinite μ] (hμ_supp : μ.support ⊆ (A_fin : Set ℝ)) :
    rieszEnergy (2 * κ) (hδ := hδ) μ =
      ∑ a ∈ A_fin, ∑ b ∈ A_fin, μ {a} * μ {b} *
        ENNReal.ofReal ((max (dist a b) δ) ^ (-2 * κ)) := by
  have h_ae : ∀ᵐ (x : ℝ) ∂μ, x ∈ (A_fin : Set ℝ) := by
    have h1 : μ (μ.supportᶜ) = 0 := MeasureTheory.Measure.measure_compl_support
    have h2 : (A_fin : Set ℝ)ᶜ ⊆ μ.supportᶜ := by
      intro x hx
      intro h3
      exact hx (hμ_supp h3)
    have h3 : μ ((A_fin : Set ℝ)ᶜ) = 0 := by
      have h31 : μ ((A_fin : Set ℝ)ᶜ) ≤ μ (μ.supportᶜ) := by exact OuterMeasureClass.measure_mono μ h2
      rw [h1] at h31
      exact le_zero_iff.mp h31
    have h4 : {x : ℝ | x ∉ (A_fin : Set ℝ)} = (A_fin : Set ℝ)ᶜ := by ext x; simp
    have h5 : μ {x : ℝ | x ∉ (A_fin : Set ℝ)} = 0 := by
      rw [h4]; exact h3
    simpa [ae_iff] using h5
  have hμ_eq : μ = ∑ a ∈ A_fin, μ {a} • Measure.dirac a :=
    (MeasureTheory.Measure.ae_mem_finset_iff (s := A_fin)).mp h_ae
  have h_sum_lintegral : ∀ (S : Finset ℝ), ∀ (g : ℝ → ENNReal),
      ∫⁻ x, g x ∂(∑ a ∈ S, μ {a} • Measure.dirac a) = ∑ a ∈ S, μ {a} * g a := by
    intro S
    induction S using Finset.induction with
    | empty =>
      intro g
      simp
    | @insert a S ha ih =>
      intro g
      have h_add : ∫⁻ x, g x ∂((μ {a} • Measure.dirac a) + ∑ b ∈ S, μ {b} • Measure.dirac b) =
          ∫⁻ x, g x ∂(μ {a} • Measure.dirac a) + ∫⁻ x, g x ∂(∑ b ∈ S, μ {b} • Measure.dirac b) :=
        MeasureTheory.lintegral_add_measure g _ _
      have h_dirac : ∫⁻ x, g x ∂(μ {a} • Measure.dirac a) = μ {a} * g a := by
        have h1 : ∫⁻ x, g x ∂(μ {a} • Measure.dirac a) = μ {a} * ∫⁻ x, g x ∂(Measure.dirac a) :=
          MeasureTheory.lintegral_smul_measure (μ := Measure.dirac a) (μ {a}) g
        rw [h1]
        have h2 : ∫⁻ x, g x ∂(Measure.dirac a) = g a :=
          MeasureTheory.lintegral_dirac (α := ℝ) a g
        rw [h2] <;> ring
      have h_eq1 : (∑ x ∈ insert a S, μ {x} • Measure.dirac x) =
          (μ {a} • Measure.dirac a) + ∑ b ∈ S, μ {b} • Measure.dirac b := by
        rw [Finset.sum_insert ha] <;> rfl
      rw [h_eq1, h_add, h_dirac, ih g, Finset.sum_insert ha] <;> ring
  dsimp only [rieszEnergy]
  let g : ℝ → ℝ → ENNReal := fun x y =>
    ENNReal.ofReal ((max (dist x y) δ) ^ (-2 * κ))
  let h_inner : ℝ → ENNReal := fun x => ∫⁻ y, g x y ∂μ
  have h_main1 : ∫⁻ x, h_inner x ∂μ = ∫⁻ x, h_inner x ∂(∑ a ∈ A_fin, μ {a} • Measure.dirac a) := by
    apply congr_arg (fun m : Measure ℝ => ∫⁻ x, h_inner x ∂m) hμ_eq
  have h_main2 : ∫⁻ x, h_inner x ∂(∑ a ∈ A_fin, μ {a} • Measure.dirac a) =
      ∑ a ∈ A_fin, μ {a} * h_inner a :=
    h_sum_lintegral A_fin h_inner
  have h_inner_sum : ∀ a ∈ A_fin, h_inner a = ∑ b ∈ A_fin, μ {b} * g a b := by
    intro a _
    have h10 : h_inner a = ∫⁻ y, g a y ∂(∑ b ∈ A_fin, μ {b} • Measure.dirac b) := by
      dsimp only [h_inner]
      apply congr_arg (fun m : Measure ℝ => ∫⁻ y, g a y ∂m) hμ_eq
    rw [h10]
    exact h_sum_lintegral A_fin (g a)
  have h_final1 : ∫⁻ x, h_inner x ∂μ = ∑ a ∈ A_fin, μ {a} * h_inner a := by
    rw [h_main1, h_main2]
  have h_final2 : ∑ a ∈ A_fin, μ {a} * h_inner a = ∑ a ∈ A_fin, μ {a} * (∑ b ∈ A_fin, μ {b} * g a b) := by
    apply Finset.sum_congr rfl
    intro a ha
    exact congr_arg (fun x => μ {a} * x) (h_inner_sum a ha)
  have h_final3 : ∑ a ∈ A_fin, μ {a} * (∑ b ∈ A_fin, μ {b} * g a b) = ∑ a ∈ A_fin, ∑ b ∈ A_fin, μ {a} * μ {b} * g a b := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    simp [mul_assoc]
  have h_goal : ∫⁻ x, (∫⁻ y, g x y ∂μ) ∂μ = ∑ a ∈ A_fin, ∑ b ∈ A_fin, μ {a} * μ {b} * g a b := by
    have h1 : ∫⁻ x, (∫⁻ y, g x y ∂μ) ∂μ = ∫⁻ x, h_inner x ∂μ := by rfl
    rw [h1, h_final1, h_final2, h_final3]
  simpa [g] using h_goal

/-- Output constant for `energy_to_large_mass_delta_set`. -/
noncomputable def energyToLargeMassDeltaSetC (δ κ K : ℝ) : ℝ :=
  64 * (10 * K * (2 : ℝ) ^ κ) * (Nat.ceil (Real.logb 2 (δ ^ (-(κ + 1)))) + 1 : ℝ)^2

/-- Main theorem: energy bound on finite δ-separated support → large-mass delta-set.

Given a probability measure ν on a finite δ-separated set A ⊆ [0,1] with
δ-regularized (2κ)-energy ≤ K, extract S ⊆ A with:
- `IsRealDeltaSet δ κ C S` (same exponent κ, NO halving)
- `ν(S) ≥ 3/4`
- `C = O(K * 2^κ * (log 1/δ)^2)`

Mass ledger: good-set loss ≤ 1/8, tiny-weight loss ≤ 1/64, low-level loss ≤ 1/32,
total loss ≤ 11/64, so retention ≥ 53/64 > 3/4. -/
lemma energy_to_large_mass_delta_set
    {δ κ K : ℝ} {A : Finset ℝ}
    (hδ : 0 < δ) (hδ_lt_one : δ < 1) (hδ_dyadic : δ ∈ dyadicScales)
    (hκ_pos : 0 < κ) (hκ_le_one : κ ≤ 1) (hK_pos : 0 < K)
    (hA_sep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → dist x y ≥ δ)
    (hA_sub : (A : Set ℝ) ⊆ Set.Icc 0 1)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν_supp : ν.support ⊆ (A : Set ℝ))
    (h_energy : rieszEnergy (2 * κ) (hδ := hδ) ν ≤ ENNReal.ofReal K)
    (hδ_small : δ ^ κ ≤ 1 / 128) :
    ∃ (S : Finset ℝ),
      S ⊆ A ∧
      IsRealDeltaSet δ κ (energyToLargeMassDeltaSetC δ κ K) (S : Set ℝ) ∧
      ENNReal.ofReal (3 / 4 : ℝ) ≤ ν (S : Set ℝ) := by
  -- Step 1: Good set extraction with threshold 8K (retention 7/8)
  obtain ⟨A_good, hA_good_meas, hA_good_compl_le, h_pointwise⟩ :=
    energy_to_frostman_good_set_L (L := (8 : ℝ)) hδ (by linarith) hκ_pos hK_pos (by norm_num) (by norm_num) h_energy
  let A_fin : Finset ℝ := A.filter (fun x => x ∈ A_good)
  have hA_fin_sub : A_fin ⊆ A := filter_subset _ _
  have hA_fin_in_Icc : (A_fin : Set ℝ) ⊆ Set.Icc 0 1 := by
    intro x hx
    exact hA_sub (hA_fin_sub hx)
  have hνA_compl_zero : ν ((A : Set ℝ)ᶜ) = 0 := by
    have h1 : ν (ν.supportᶜ) = 0 := by exact Measure.measure_compl_support
    have h2 : (A : Set ℝ)ᶜ ⊆ ν.supportᶜ := by
      intro x hx
      simp only [Set.mem_compl_iff] at hx ⊢
      intro h3
      exact hx (hν_supp h3)
    exact measure_mono_null h2 h1
  have h1_set : (A_fin : Set ℝ) = A_good ∩ (A : Set ℝ) := by
    ext x; simp [A_fin] <;> tauto
  have h2_meas : ν (A_fin : Set ℝ) = ν A_good := by
    rw [h1_set]
    have h_meas1 : MeasurableSet (A_good ∩ (A : Set ℝ)) := hA_good_meas.inter (Finset.measurableSet A)
    have h_meas2 : MeasurableSet (A_good \ (A : Set ℝ)) := hA_good_meas.diff (Finset.measurableSet A)
    have h_disj : Disjoint (A_good ∩ (A : Set ℝ)) (A_good \ (A : Set ℝ)) := by exact Disjoint.symm Set.disjoint_sdiff_inter
    have h_eq : A_good = (A_good ∩ (A : Set ℝ)) ∪ (A_good \ (A : Set ℝ)) := by
      ext x; simp [Set.mem_diff] <;> tauto
    have h4 : ν (A_good \ (A : Set ℝ)) = 0 := by
      apply measure_mono_null (show A_good \ (A : Set ℝ) ⊆ (A : Set ℝ)ᶜ from by simp)
      exact hνA_compl_zero
    have h51 : ν A_good = ν ((A_good ∩ (A : Set ℝ)) ∪ (A_good \ (A : Set ℝ))) := by
      exact congr_arg ν h_eq
    have h_union : ν ((A_good ∩ (A : Set ℝ)) ∪ (A_good \ (A : Set ℝ))) =
        ν (A_good ∩ (A : Set ℝ)) + ν (A_good \ (A : Set ℝ)) := by exact measure_union h_disj h_meas2
    have h5 : ν A_good = ν (A_good ∩ (A : Set ℝ)) + ν (A_good \ (A : Set ℝ)) := by
      rw [h51, h_union]
    have h6 : ν A_good = ν (A_good ∩ (A : Set ℝ)) := by
      calc ν A_good = ν (A_good ∩ (A : Set ℝ)) + ν (A_good \ (A : Set ℝ)) := h5
        _ = ν (A_good ∩ (A : Set ℝ)) + 0 := by rw [h4]
        _ = ν (A_good ∩ (A : Set ℝ)) := by simp
    exact h6.symm
  have h_add : ν A_good + ν A_goodᶜ = 1 := by
    letI : MeasurableSet A_good := hA_good_meas
    have h_meas_compl : MeasurableSet A_goodᶜ := hA_good_meas.compl
    have h : ν (A_good ∪ A_goodᶜ) = ν A_good + ν A_goodᶜ :=
      measure_union disjoint_compl_right h_meas_compl
    have h5 : A_good ∪ A_goodᶜ = Set.univ := by simp
    have h6 : ν Set.univ = 1 := by exact measure_univ
    rw [h5] at h
    rw [h6] at h
    exact h.symm
  have hνA_good_ne_top : ν A_good ≠ ⊤ := by
    have h6 : ν A_good ≤ 1 := by
      have h7 : ν A_good ≤ ν A_good + ν A_goodᶜ := by simp
      rw [h_add] at h7
      exact h7
    exact ne_top_of_le_ne_top (by simp) h6
  have hνA_good_compl_ne_top : ν A_goodᶜ ≠ ⊤ := by
    have h : ν A_goodᶜ ≤ 1 := by
      have h2 : ν A_goodᶜ ≤ ν A_good + ν A_goodᶜ := by simp
      rw [h_add] at h2
      exact h2
    exact ne_top_of_le_ne_top (by simp) h
  have h_toReal_add : (ν A_good).toReal + (ν A_goodᶜ).toReal = 1 := by
    have h1 : (ν A_good + ν A_goodᶜ).toReal = (1 : ENNReal).toReal := by rw [h_add]
    have h2 : (ν A_good + ν A_goodᶜ).toReal = (ν A_good).toReal + (ν A_goodᶜ).toReal := by
      rw [ENNReal.toReal_add hνA_good_ne_top hνA_good_compl_ne_top]
    rw [h2] at h1
    simpa using h1
  have h_compl_le_real : (ν A_goodᶜ).toReal ≤ 1 / 8 := by
    have h3 : ν A_goodᶜ ≤ (1 / 8 : ENNReal) := by simpa using hA_good_compl_le
    have h_b_top : (1 / 8 : ENNReal) ≠ ⊤ := by simp
    have h4 : (ν A_goodᶜ).toReal ≤ ((1 / 8 : ENNReal)).toReal := ENNReal.toReal_mono h_b_top h3
    have h5 : ((1 / 8 : ENNReal)).toReal = (1 / 8 : ℝ) := by simp
    rw [h5] at h4
    exact h4
  have h_good_ge_real : (7 / 8 : ℝ) ≤ (ν A_good).toReal := by linarith
  have hνA_fin_ge : (7 / 8 : ENNReal) ≤ ν (A_fin : Set ℝ) := by
    rw [h2_meas]
    have h5 : ν A_good = ENNReal.ofReal (ν A_good).toReal := by
      rw [ENNReal.ofReal_toReal hνA_good_ne_top]
    have h7 : (7 / 8 : ENNReal) = ENNReal.ofReal (7 / 8 : ℝ) := by
      have h_pos : (0 : ℝ) < 8 := by norm_num
      have h_eq1 : ENNReal.ofReal (7 / 8 : ℝ) = ENNReal.ofReal (7 : ℝ) / ENNReal.ofReal (8 : ℝ) := by
        rw [show (7 / 8 : ℝ) = (7 : ℝ) / (8 : ℝ) by norm_num]
        rw [ENNReal.ofReal_div_of_pos h_pos]
      rw [h_eq1]
      <;> norm_cast
    rw [h7, h5]
    exact ENNReal.ofReal_le_ofReal h_good_ge_real
  have hνA_fin_ne_zero : ν (A_fin : Set ℝ) ≠ 0 := by
    have h : (7 / 8 : ENNReal) ≤ ν (A_fin : Set ℝ) := hνA_fin_ge
    have h' : (7 / 8 : ENNReal) ≠ 0 := by simp
    exact ne_bot_of_le_ne_bot h' h
  have hνA_fin_ne_top : ν (A_fin : Set ℝ) ≠ ⊤ := by
    have h : ν (A_fin : Set ℝ) ≤ 1 := by
      have h_univ : ν Set.univ = 1 := by exact measure_univ
      exact le_trans (measure_mono (Set.subset_univ _)) h_univ.le
    exact ne_top_of_le_ne_top (by simp) h
  -- Step 2: Normalize
  let c : ENNReal := (ν (A_fin : Set ℝ))⁻¹
  let μ : Measure ℝ := c • ν.restrict (A_fin : Set ℝ)
  have hμ_prob : μ Set.univ = 1 := by
    have h5 : μ Set.univ = c * ν (A_fin : Set ℝ) := by
      simp [μ, Measure.restrict_apply (Finset.measurableSet A_fin)] <;> rfl
    rw [h5, ENNReal.inv_mul_cancel hνA_fin_ne_zero hνA_fin_ne_top] <;> simp
  have hμ_finite : ∀ (s : Set ℝ), μ s ≠ ⊤ := by
    intro s
    have h1 : μ s ≤ μ Set.univ := measure_mono (by simp)
    rw [hμ_prob] at h1
    exact ne_top_of_le_ne_top (by simp) h1
  have h_c_le_87 : c ≤ (8 / 7 : ENNReal) := by
    dsimp only [c]
    have h1 : (7 / 8 : ENNReal) ≤ ν (A_fin : Set ℝ) := hνA_fin_ge
    have h2 : (ν (A_fin : Set ℝ))⁻¹ ≤ ((7 / 8 : ENNReal))⁻¹ := ENNReal.inv_le_inv.mpr h1
    have h4 : (7 / 8 : ENNReal) ≠ 0 := by
      have h : (0 : ENNReal) < 7 / 8 := by norm_num
      exact h.ne'
    have h5 : (7 / 8 : ENNReal) ≠ ⊤ := by exact ne_top_of_le_ne_top hνA_fin_ne_top hνA_fin_ge
    have h6 : ((7 / 8 : ENNReal)).toReal = (7 / 8 : ℝ) := by simp
    have h_inv_ne_top : ((7 / 8 : ENNReal))⁻¹ ≠ ⊤ := by
      simpa using h4
    have h9 : ENNReal.ofReal (((7 / 8 : ENNReal))⁻¹.toReal) = ((7 / 8 : ENNReal))⁻¹ :=
      ENNReal.ofReal_toReal h_inv_ne_top
    have h10 : (((7 / 8 : ENNReal))⁻¹.toReal) = ((7 / 8 : ENNReal)).toReal⁻¹ := by
      rw [ENNReal.toReal_inv]
    have h7 : ((7 / 8 : ENNReal))⁻¹ = ENNReal.ofReal (((7 / 8 : ENNReal)).toReal⁻¹) := by
      rw [← h9, h10]
    rw [h7, h6] at h2
    have h8 : (7 / 8 : ℝ)⁻¹ = (8 / 7 : ℝ) := by norm_num
    rw [h8] at h2
    have h11 : ENNReal.ofReal (8 / 7 : ℝ) = (8 / 7 : ENNReal) := by
      have h_pos : (0 : ℝ) < 7 := by norm_num
      have h_eq1 : ENNReal.ofReal (8 / 7 : ℝ) = ENNReal.ofReal (8 : ℝ) / ENNReal.ofReal (7 : ℝ) := by
        rw [show (8 / 7 : ℝ) = (8 : ℝ) / (7 : ℝ) by norm_num]
        rw [ENNReal.ofReal_div_of_pos h_pos]
      rw [h_eq1] <;> norm_cast
    rw [h11] at h2
    exact h2
  -- Step 3: Frostman bound for μ
  let C_frost : ℝ := 10 * K * (2 : ℝ) ^ κ
  have hC_frost_pos : 0 < C_frost := by
    dsimp only [C_frost]
    have h1 : 0 < K := hK_pos
    have h2 : 0 < (2 : ℝ) ^ κ := by positivity
    positivity
  have hK_ge_one : (1 : ℝ) ≤ K := by
    have h1 := rieszEnergy_ge_one hδ hδ_lt_one hκ_pos (hν_supp.trans hA_sub)
    have h2 : rieszEnergy (2 * κ) (hδ := hδ) ν ≤ ENNReal.ofReal K := h_energy
    have h3 : (1 : ENNReal) ≤ ENNReal.ofReal K := le_trans h1 h2
    have h4 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
    rw [h4] at h3
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp h3
  have hμ_A_fin_compl_null : μ ((A_fin : Set ℝ)ᶜ) = 0 := by
    dsimp only [μ]
    have h1 : (c • ν.restrict (A_fin : Set ℝ)) ((A_fin : Set ℝ)ᶜ) =
        c * (ν.restrict (A_fin : Set ℝ)) ((A_fin : Set ℝ)ᶜ) := by exact (toReal_eq_toReal_iff' (hμ_finite (↑A_fin)ᶜ) (hμ_finite (↑A_fin)ᶜ)).mp rfl
    rw [h1]
    have h2 : (ν.restrict (A_fin : Set ℝ)) ((A_fin : Set ℝ)ᶜ) = 0 := by
      have hA_meas : MeasurableSet (A_fin : Set ℝ) := Finset.measurableSet A_fin
      have h : (ν.restrict (A_fin : Set ℝ)) ((A_fin : Set ℝ)ᶜ) = ν (((A_fin : Set ℝ)ᶜ) ∩ (A_fin : Set ℝ)) := by exact Measure.restrict_apply' hA_meas
      rw [h]
      <;> simp
    rw [h2] <;> simp
  have hμ_supp : μ.support ⊆ (A_fin : Set ℝ) := by
    have h_closed : IsClosed (A_fin : Set ℝ) := by exact Finset.isClosed A_fin
    have h : μ.support ⊆ (A_fin : Set ℝ) := by
      exact Measure.support_subset_of_isClosed h_closed hμ_A_fin_compl_null
    exact h
  have hμ_supp_Icc : μ.support ⊆ Set.Icc 0 1 := by
    intro x hx
    exact hA_fin_in_Icc (hμ_supp hx)
  have hEμ_le : rieszEnergy (2 * κ) (hδ := hδ) μ ≤ c^2 * ENNReal.ofReal K := by
    dsimp only [μ]
    let μ0 := ν.restrict (A_fin : Set ℝ)
    let f : ℝ → ℝ → ENNReal := fun x y => ENNReal.ofReal ((max (dist x y) δ) ^ (-(2 * κ)))
    have h1 : ∀ (g : ℝ → ENNReal), ∫⁻ x, g x ∂(c • μ0) = c * ∫⁻ x, g x ∂μ0 := by
      intro g
      exact MeasureTheory.lintegral_smul_measure c g
    have h_meas : Measurable (fun x : ℝ => ∫⁻ y : ℝ, f x y ∂μ0) := by
      have h_joint : Measurable (fun p : ℝ × ℝ => f p.1 p.2) := by fun_prop
      exact Measurable.lintegral_prod_right h_joint
    let g : ℝ → ENNReal := fun x => ∫⁻ y, f x y ∂μ0
    let h : ℝ → ENNReal := fun x => c * g x
    have h_meas_h : Measurable h := h_meas.const_mul c
    have h_inner_eq : (fun x : ℝ => ∫⁻ y, f x y ∂(c • μ0)) = h := by
      funext x
      exact h1 (f x)
    have h_scale : ∫⁻ x, (∫⁻ y, f x y ∂(c • μ0)) ∂(c • μ0) = c^2 * ∫⁻ x, g x ∂μ0 := by
      have h_step1 : ∫⁻ x, (∫⁻ y, f x y ∂(c • μ0)) ∂(c • μ0) = ∫⁻ x, h x ∂(c • μ0) := by
        rw [h_inner_eq]
      have h_step2 : ∫⁻ x, h x ∂(c • μ0) = c * ∫⁻ x, h x ∂μ0 := h1 h
      have h_step3 : ∫⁻ x, h x ∂μ0 = (∫⁻ x, g x ∂μ0) * c := by
        have h_comm : h = fun x : ℝ => g x * c := by
          funext x; exact mul_comm _ _
        rw [h_comm]
        exact MeasureTheory.lintegral_mul_const c (hf := h_meas)
      rw [h_step1, h_step2, h_step3] <;> ring
    have h_restrict_le : ∀ (k : ℝ → ENNReal), ∫⁻ x, k x ∂μ0 ≤ ∫⁻ x, k x ∂ν := by
      intro k
      have h_eq : ∫⁻ x, k x ∂μ0 = ∫⁻ x in (A_fin : Set ℝ), k x ∂ν := by rfl
      rw [h_eq]
      exact MeasureTheory.setLIntegral_le_lintegral (A_fin : Set ℝ) k
    have h5 : ∫⁻ x, g x ∂μ0 ≤ ∫⁻ x, (∫⁻ y, f x y ∂ν) ∂ν := by
      have h_outer : ∫⁻ x, g x ∂μ0 ≤ ∫⁻ x, g x ∂ν := h_restrict_le g
      have h_inner2 : ∀ x, g x ≤ ∫⁻ y, f x y ∂ν := fun x => h_restrict_le (f x)
      have h_middle : ∫⁻ x, g x ∂ν ≤ ∫⁻ x, (∫⁻ y, f x y ∂ν) ∂ν :=
        MeasureTheory.lintegral_mono h_inner2
      exact le_trans h_outer h_middle
    have h_main : rieszEnergy (2 * κ) (hδ := hδ) μ ≤ c^2 * rieszEnergy (2 * κ) (hδ := hδ) ν := by
      have h_eq1 : rieszEnergy (2 * κ) (hδ := hδ) μ = ∫⁻ x, (∫⁻ y, f x y ∂(c • μ0)) ∂(c • μ0) := by
        rfl
      have h_eq2 : rieszEnergy (2 * κ) (hδ := hδ) ν = ∫⁻ x, (∫⁻ y, f x y ∂ν) ∂ν := by rfl
      rw [h_eq1, h_eq2, h_scale]
      exact mul_le_mul_left' h5 (c^2)
    have h_final : c^2 * rieszEnergy (2 * κ) (hδ := hδ) ν ≤ c^2 * ENNReal.ofReal K :=
      mul_le_mul_left' h_energy (c^2)
    exact le_trans h_main h_final
  have h_bound : ∀ (a r : ℝ), δ ≤ r → r ≤ 1 →
      μ (Set.Icc (a - r) (a + r)) ≤ ENNReal.ofReal (C_frost * r ^ κ) := by
    intro a r hδ_le_r hr_le_one
    let I := Set.Icc (a - r) (a + r)
    let S : Finset ℝ := A_fin.filter (fun x => x ∈ I)
    have hS_eq : (S : Set ℝ) = (A_fin : Set ℝ) ∩ I := by
      ext x; simp [S] <;> tauto
    have hA_fin_meas : MeasurableSet (A_fin : Set ℝ) := Finset.measurableSet A_fin
    have h2 : μ ((A_fin : Set ℝ)ᶜ) = 0 := hμ_A_fin_compl_null
    have h31 : μ I ≤ μ ((A_fin : Set ℝ) ∩ I) := by
      have h : I ⊆ ((A_fin : Set ℝ) ∩ I) ∪ (A_fin : Set ℝ)ᶜ := by
        intro x hx
        by_cases h4 : x ∈ (A_fin : Set ℝ)
        · exact Or.inl ⟨h4, hx⟩
        · exact Or.inr h4
      have h5 : μ I ≤ μ (((A_fin : Set ℝ) ∩ I) ∪ (A_fin : Set ℝ)ᶜ) := by
        exact OuterMeasureClass.measure_mono μ h
      have h6 : μ (((A_fin : Set ℝ) ∩ I) ∪ (A_fin : Set ℝ)ᶜ) ≤
          μ ((A_fin : Set ℝ) ∩ I) + μ ((A_fin : Set ℝ)ᶜ) :=
        measure_union_le _ _
      rw [h2] at h6
      simpa using h5.trans h6
    have h32 : μ ((A_fin : Set ℝ) ∩ I) ≤ μ I := by
      have h_sub : (A_fin : Set ℝ) ∩ I ⊆ I := by
        intro z hz
        exact hz.2
      exact OuterMeasureClass.measure_mono μ h_sub
    have h3 : μ I = μ ((A_fin : Set ℝ) ∩ I) := le_antisymm h31 h32
    have hμI_eq : μ I = μ (S : Set ℝ) := by
      rw [h3]
      have h4 : (A_fin : Set ℝ) ∩ I = (S : Set ℝ) := by
        rw [hS_eq] <;> simp [Set.inter_comm]
      rw [h4]
    have h_energy_sum : rieszEnergy (2 * κ) (hδ := hδ) μ =
        ∑ x ∈ A_fin, ∑ y ∈ A_fin, μ {x} * μ {y} *
          ENNReal.ofReal ((max (dist x y) δ) ^ (-2 * κ)) :=
      rieszEnergy_finite_sum hδ hκ_pos hμ_supp
    have hS_sub : S ⊆ A_fin := by
      intro x hx
      exact (Finset.mem_filter.mp hx).1
    have h_pair_lower : ∑ x ∈ S, ∑ y ∈ S, μ {x} * μ {y} *
          ENNReal.ofReal ((max (dist x y) δ) ^ (-2 * κ)) ≤
        rieszEnergy (2 * κ) (hδ := hδ) μ := by
      rw [h_energy_sum]
      let F : ℝ → ℝ → ENNReal := fun x y => μ {x} * μ {y} * ENNReal.ofReal ((max (dist x y) δ) ^ (-2 * κ))
      have h_sum_subset : ∀ (s₁ s₂ : Finset ℝ) (f : ℝ → ENNReal), s₁ ⊆ s₂ → ∑ x ∈ s₁, f x ≤ ∑ x ∈ s₂, f x := by
        intro s₁ s₂ f h_sub
        have h_disj : Disjoint s₁ (s₂ \ s₁) := Finset.disjoint_sdiff
        have h_union : s₁ ∪ (s₂ \ s₁) = s₂ := by
          ext x; simp [h_sub] <;> tauto
        have h_nonneg : 0 ≤ ∑ x ∈ (s₂ \ s₁), f x := by positivity
        calc
          ∑ x ∈ s₁, f x
            ≤ ∑ x ∈ s₁, f x + ∑ x ∈ (s₂ \ s₁), f x := le_add_of_nonneg_right h_nonneg
          _ = ∑ x ∈ (s₁ ∪ (s₂ \ s₁)), f x := by rw [Finset.sum_union h_disj]
          _ = ∑ x ∈ s₂, f x := by rw [h_union]
      have h2 : ∑ x ∈ S, ∑ y ∈ S, F x y ≤ ∑ x ∈ S, ∑ y ∈ A_fin, F x y := by
        apply Finset.sum_le_sum
        intro x _
        exact h_sum_subset S A_fin (F x) hS_sub
      have h3 : ∑ x ∈ S, ∑ y ∈ A_fin, F x y ≤ ∑ x ∈ A_fin, ∑ y ∈ A_fin, F x y :=
        h_sum_subset S A_fin (fun x => ∑ y ∈ A_fin, F x y) hS_sub
      exact le_trans h2 h3
    have h_kernel_lower : ∀ x ∈ S, ∀ y ∈ S,
        ENNReal.ofReal ((2 * r) ^ (-2 * κ)) ≤
          ENNReal.ofReal ((max (dist x y) δ) ^ (-2 * κ)) := by
      intro x hx y hy
      have hxI : x ∈ I := (Finset.mem_filter.mp hx).2
      have hyI : y ∈ I := (Finset.mem_filter.mp hy).2
      have hx1 : a - r ≤ x := hxI.1
      have hx2 : x ≤ a + r := hxI.2
      have hy1 : a - r ≤ y := hyI.1
      have hy2 : y ≤ a + r := hyI.2
      have h_dist : dist x y ≤ 2 * r := by
        simpa [dist_eq_norm, Real.norm_eq_abs] using
          show |x - y| ≤ 2 * r from by
            have h1 : x - y ≤ 2 * r := by linarith
            have h2 : -(2 * r) ≤ x - y := by linarith
            exact abs_le.mpr ⟨h2, h1⟩
      have h_max : max (dist x y) δ ≤ 2 * r := max_le h_dist (by linarith)
      have h_pos1 : 0 < max (dist x y) δ := by
        have hδ_pos : 0 < δ := hδ
        exact lt_of_lt_of_le hδ_pos (le_max_right _ _)
      have h_pos2 : 0 ≤ 2 * r := by linarith
      have h_neg : -2 * κ ≤ 0 := by linarith [hκ_pos]
      have h : (2 * r) ^ (-2 * κ) ≤ (max (dist x y) δ) ^ (-2 * κ) :=
        Real.rpow_le_rpow_of_nonpos h_pos1 h_max h_neg
      exact ENNReal.ofReal_le_ofReal h
    let K_kernel : ENNReal := ENNReal.ofReal ((2 * r) ^ (-2 * κ))
    have hK_finite : K_kernel ≠ ⊤ := ENNReal.ofReal_ne_top
    have h4 : ∑ x ∈ S, ∑ y ∈ S, μ {x} * μ {y} * K_kernel ≤
        ∑ x ∈ S, ∑ y ∈ S, μ {x} * μ {y} *
          ENNReal.ofReal ((max (dist x y) δ) ^ (-2 * κ)) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      have h_k : K_kernel ≤ ENNReal.ofReal ((max (dist x y) δ) ^ (-2 * κ)) :=
        h_kernel_lower x hx y hy
      have h1 : (μ {x} * μ {y}) * K_kernel ≤ (μ {x} * μ {y}) *
          ENNReal.ofReal ((max (dist x y) δ) ^ (-2 * κ)) :=
        mul_le_mul_left' h_k (μ {x} * μ {y})
      simpa [mul_assoc] using h1
    have h_sumS : ∑ z ∈ S, μ {z} = μ (S : Set ℝ) := by
      rw [robust_projection.finset_measure_sum μ]
    have h51 : ∀ (x : ℝ), ∑ y ∈ S, μ {x} * μ {y} * K_kernel =
        (K_kernel * μ {x}) * (∑ y ∈ S, μ {y}) := by
      intro x
      have h_j : ∑ y ∈ S, μ {x} * μ {y} * K_kernel = ∑ y ∈ S, (K_kernel * μ {x}) * μ {y} := by
        apply Finset.sum_congr rfl
        intro y _
        ring
      rw [h_j]
      exact (Finset.mul_sum S (fun y => μ {y}) (K_kernel * μ {x})).symm
    have h52 : ∑ x ∈ S, ∑ y ∈ S, μ {x} * μ {y} * K_kernel =
        ∑ x ∈ S, (K_kernel * μ {x}) * (∑ y ∈ S, μ {y}) := by
      apply Finset.sum_congr rfl
      intro x _
      exact h51 x
    let C : ENNReal := ∑ y ∈ S, μ {y}
    have h53 : ∑ x ∈ S, (K_kernel * μ {x}) * C = C * ∑ x ∈ S, K_kernel * μ {x} := by
      have h_comm : ∑ x ∈ S, (K_kernel * μ {x}) * C = ∑ x ∈ S, C * (K_kernel * μ {x}) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      rw [h_comm, Finset.mul_sum]
    have h54 : C * ∑ x ∈ S, K_kernel * μ {x} = C * (K_kernel * ∑ x ∈ S, μ {x}) := by
      have h_inner : ∑ x ∈ S, K_kernel * μ {x} = K_kernel * ∑ x ∈ S, μ {x} := by
        exact (Finset.mul_sum S (fun x => μ {x}) K_kernel).symm
      rw [h_inner]
    have h5 : ∑ x ∈ S, ∑ y ∈ S, μ {x} * μ {y} * K_kernel =
        K_kernel * μ (S : Set ℝ) * μ (S : Set ℝ) := by
      have h_sumS' : ∑ x ∈ S, μ {x} = μ (S : Set ℝ) := by
        rw [robust_projection.finset_measure_sum μ]
      calc
        ∑ x ∈ S, ∑ y ∈ S, μ {x} * μ {y} * K_kernel
          = ∑ x ∈ S, (K_kernel * μ {x}) * (∑ y ∈ S, μ {y}) := h52
        _ = (∑ y ∈ S, μ {y}) * ∑ x ∈ S, K_kernel * μ {x} := h53
        _ = (∑ y ∈ S, μ {y}) * (K_kernel * ∑ x ∈ S, μ {x}) := by rw [h54]
        _ = μ (S : Set ℝ) * (K_kernel * μ (S : Set ℝ)) := by
          have h_goal : (∑ y ∈ S, μ {y}) * (K_kernel * ∑ x ∈ S, μ {x}) =
              μ (S : Set ℝ) * (K_kernel * μ (S : Set ℝ)) := by
            simp only [h_sumS']
            <;> ring
          exact h_goal
        _ = K_kernel * μ (S : Set ℝ) * μ (S : Set ℝ) := by ring
    have h6 : K_kernel * μ (S : Set ℝ) * μ (S : Set ℝ) ≤
        rieszEnergy (2 * κ) (hδ := hδ) μ := by
      rw [← h5]
      exact le_trans h4 h_pair_lower
    have h7 : μ (S : Set ℝ) ≠ ⊤ := hμ_finite (S : Set ℝ)
    have hc_ne_top : c ≠ ⊤ := by
      dsimp only [c]
      intro h
      have h9 : (ν (A_fin : Set ℝ))⁻¹ = ⊤ := h
      have h10 : ν (A_fin : Set ℝ) = 0 := by
        simpa [ENNReal.inv_eq_top] using h9
      exact hνA_fin_ne_zero h10
    have h_pow2_fin : c^2 ≠ ⊤ := ENNReal.pow_ne_top (ha := hc_ne_top)
    have h_energy_finite : rieszEnergy (2 * κ) (hδ := hδ) μ ≠ ⊤ := by
      have h : rieszEnergy (2 * κ) (hδ := hδ) μ ≤ c^2 * ENNReal.ofReal K := hEμ_le
      have h_fin : (c^2 * ENNReal.ofReal K) ≠ ⊤ :=
        mul_ne_top h_pow2_fin ENNReal.ofReal_ne_top
      exact ne_top_of_le_ne_top h_fin h
    have h_prod_finite : K_kernel * μ (S : Set ℝ) * μ (S : Set ℝ) ≠ ⊤ :=
      mul_ne_top (mul_ne_top hK_finite h7) h7
    have h9 : (K_kernel * μ (S : Set ℝ) * μ (S : Set ℝ)).toReal ≤
        (rieszEnergy (2 * κ) (hδ := hδ) μ).toReal :=
      (ENNReal.toReal_le_toReal h_prod_finite h_energy_finite).mpr h6
    have h10 : (K_kernel * μ (S : Set ℝ) * μ (S : Set ℝ)).toReal =
        (2 * r) ^ (-2 * κ) * (μ (S : Set ℝ)).toReal ^ 2 := by
      have h103 : K_kernel.toReal = (2 * r) ^ (-2 * κ) := by
        have hr_pos : 0 < r := by linarith [hδ_le_r, hδ]
        have h_pos : 0 < (2 * r) := by linarith
        have h_pos2 : 0 < (2 * r) ^ (-2 * κ) := Real.rpow_pos_of_pos h_pos (-2 * κ)
        have h_nonneg : 0 ≤ (2 * r) ^ (-2 * κ) := le_of_lt h_pos2
        have hK_def : K_kernel = ENNReal.ofReal ((2 * r) ^ (-2 * κ)) := by rfl
        rw [hK_def, ENNReal.toReal_ofReal h_nonneg]
      set a : ENNReal := K_kernel with ha_def
      set b : ENNReal := μ (S : Set ℝ) with hb_def
      have h : (a * b * b).toReal = a.toReal * b.toReal ^ 2 := by
        have h1 : (a * b * b).toReal = ((a * b) * b).toReal := by rfl
        rw [h1]
        have h2 : ((a * b) * b).toReal = (a * b).toReal * b.toReal := by
          rw [ENNReal.toReal_mul]
        rw [h2]
        have h3 : (a * b).toReal = a.toReal * b.toReal := by
          rw [ENNReal.toReal_mul]
        rw [h3] <;> ring
      rw [h, h103] <;> ring
    have h11 : 0 < (2 * r) ^ (-2 * κ) := by
      apply Real.rpow_pos_of_pos
      have hr_pos : 0 < r := by linarith [hδ_le_r, hδ]
      linarith
    have h12 : (2 * r) ^ (-2 * κ) * (μ (S : Set ℝ)).toReal ^ 2 ≤
        (rieszEnergy (2 * κ) (hδ := hδ) μ).toReal := by
      rw [h10] at h9
      exact h9
    have h14 : ((2 * r) ^ (-2 * κ))⁻¹ = (2 * r) ^ (2 * κ) := by
      rw [← Real.rpow_neg (by linarith)] <;> ring_nf
    have h15 : (μ (S : Set ℝ)).toReal ^ 2 =
        ((2 * r) ^ (-2 * κ))⁻¹ * ((2 * r) ^ (-2 * κ) * (μ (S : Set ℝ)).toReal ^ 2) := by
      set b : ℝ := (2 * r) ^ (-2 * κ) with hb_def
      set a : ℝ := (μ (S : Set ℝ)).toReal with ha_def
      have h_b_pos : 0 < b := h11
      have h : b⁻¹ * (b * a ^ 2) = a ^ 2 := by
        have h_ne : b ≠ 0 := h_b_pos.ne'
        field_simp [h_ne] <;> ring
      exact h.symm
    have h16 : ((2 * r) ^ (-2 * κ))⁻¹ * ((2 * r) ^ (-2 * κ) * (μ (S : Set ℝ)).toReal ^ 2) ≤
        ((2 * r) ^ (-2 * κ))⁻¹ * (rieszEnergy (2 * κ) (hδ := hδ) μ).toReal := by
      have h_nonneg : 0 ≤ ((2 * r) ^ (-2 * κ))⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_left h12 h_nonneg
    have h17 : ((2 * r) ^ (-2 * κ))⁻¹ * (rieszEnergy (2 * κ) (hδ := hδ) μ).toReal =
        (rieszEnergy (2 * κ) (hδ := hδ) μ).toReal * (2 * r) ^ (2 * κ) := by
      rw [h14] <;> ring
    have h8 : (μ (S : Set ℝ)).toReal ^ 2 ≤
        (rieszEnergy (2 * κ) (hδ := hδ) μ).toReal * (2 * r) ^ (2 * κ) := by
      rw [h15]
      exact le_trans h16 (by rw [h17])
    have h_c_real : c.toReal ≤ (8 / 7 : ℝ) := by
      have h87 : (8 / 7 : ENNReal) ≠ ⊤ := by
        have h1 : (8 : ENNReal) ≠ ⊤ := by simp
        have h2 : (7 : ENNReal) ≠ 0 := by norm_num
        have h3 : (7 : ENNReal)⁻¹ ≠ ⊤ := by
          simpa [ENNReal.inv_eq_top] using h2
        have h4 : (8 / 7 : ENNReal) = (8 : ENNReal) * (7 : ENNReal)⁻¹ := by
          simp [div_eq_mul_inv]
        rw [h4]
        exact mul_ne_top h1 h3
      have h : c.toReal ≤ (8 / 7 : ENNReal).toReal := ENNReal.toReal_mono h87 h_c_le_87
      have h5 : (8 / 7 : ENNReal).toReal = (8 / 7 : ℝ) := by simp
      rw [h5] at h
      exact h
    have h15b : (rieszEnergy (2 * κ) (hδ := hδ) μ).toReal ≤ c.toReal ^ 2 * K := by
      have h16 : rieszEnergy (2 * κ) (hδ := hδ) μ ≤ c^2 * ENNReal.ofReal K := hEμ_le
      have h17 : (c^2 * ENNReal.ofReal K).toReal = c.toReal ^ 2 * K := by
        set x : ENNReal := c^2 with hx_def
        set y : ENNReal := ENNReal.ofReal K with hy_def
        have h1 : (x * y).toReal = x.toReal * y.toReal := by
          rw [ENNReal.toReal_mul]
        have h2 : x.toReal = c.toReal ^ 2 := by
          have h21 : x = c * c := by
            simp [x, pow_two] <;> ring
          rw [h21]
          have h22 : (c * c).toReal = c.toReal * c.toReal := by
            rw [ENNReal.toReal_mul]
          rw [h22] <;> ring
        have h3 : y.toReal = K := by
          have hK_nonneg : 0 ≤ K := by linarith
          have h_y_def : y = ENNReal.ofReal K := by rfl
          rw [h_y_def, ENNReal.toReal_ofReal hK_nonneg]
        rw [h1, h2, h3] <;> ring
      have h_fin : (c^2 * ENNReal.ofReal K) ≠ ⊤ :=
        mul_ne_top h_pow2_fin ENNReal.ofReal_ne_top
      have h_ef : rieszEnergy (2 * κ) (hδ := hδ) μ ≠ ⊤ :=
        ne_top_of_le_ne_top h_fin h16
      have h_res : (rieszEnergy (2 * κ) (hδ := hδ) μ).toReal ≤ (c^2 * ENNReal.ofReal K).toReal :=
        (ENNReal.toReal_le_toReal h_ef h_fin).mpr h16
      rw [h17] at h_res
      exact h_res
    have h17b : (μ (S : Set ℝ)).toReal ≤ c.toReal * Real.sqrt K * (2 * r) ^ κ := by
      set a : ℝ := (μ (S : Set ℝ)).toReal with ha_def
      set b : ℝ := c.toReal * Real.sqrt K * (2 * r) ^ κ with hb_def
      have ha_nonneg : 0 ≤ a := by positivity
      have hr_pos : 0 ≤ 2 * r := by linarith [hδ_le_r, hδ]
      have hb_nonneg : 0 ≤ b := by
        dsimp only [b]
        apply mul_nonneg
        · apply mul_nonneg
          · positivity
          · exact Real.sqrt_nonneg K
        · exact Real.rpow_nonneg hr_pos _
      have hK_sq : Real.sqrt K ^ 2 = K := Real.sq_sqrt (by linarith)
      have hr_sq : ((2 * r) ^ κ) ^ 2 = (2 * r) ^ (2 * κ) := by
        have h1 : ((2 * r) ^ κ) ^ 2 = (2 * r) ^ κ * (2 * r) ^ κ := by rw [pow_two]
        rw [h1]
        have hr_strict : 0 < 2 * r := by linarith [hδ_le_r, hδ]
        have h2 : (2 * r) ^ (κ + κ) = (2 * r) ^ κ * (2 * r) ^ κ := Real.rpow_add hr_strict κ κ
        have h3 : κ + κ = 2 * κ := by ring
        have h4 : (2 * r) ^ (κ + κ) = (2 * r) ^ (2 * κ) := by rw [h3]
        exact h2.symm.trans h4
      have h_b_sq : b ^ 2 = c.toReal ^ 2 * K * (2 * r) ^ (2 * κ) := by
        simp only [hb_def]
        calc
          (c.toReal * Real.sqrt K * (2 * r) ^ κ) ^ 2
            = (c.toReal * Real.sqrt K)^2 * ((2 * r) ^ κ)^2 := by ring
          _ = c.toReal ^ 2 * (Real.sqrt K)^2 * ((2 * r) ^ κ)^2 := by ring
          _ = c.toReal ^ 2 * K * ((2 * r) ^ κ)^2 := by rw [hK_sq] <;> ring
          _ = c.toReal ^ 2 * K * (2 * r) ^ (2 * κ) := by rw [hr_sq]
      have h4 : 0 ≤ (2 * r) ^ (2 * κ) := Real.rpow_nonneg hr_pos _
      have h_a_sq_le : a ^ 2 ≤ b ^ 2 := by
        calc a ^ 2
          ≤ (rieszEnergy (2 * κ) (hδ := hδ) μ).toReal * (2 * r) ^ (2 * κ) := h8
        _ ≤ (c.toReal ^ 2 * K) * (2 * r) ^ (2 * κ) := by
            exact mul_le_mul_of_nonneg_right h15b h4
        _ = b ^ 2 := by exact h_b_sq.symm
      have h_main : a ≤ b := by
        nlinarith [ha_nonneg, hb_nonneg, h_a_sq_le]
      exact h_main
    have h22 : c.toReal * Real.sqrt K ≤ 10 * K := by
      have h23 : Real.sqrt K ≤ K := by
        have h24 : 1 ≤ K := hK_ge_one
        have h25 : Real.sqrt K ≤ Real.sqrt (K * K) := Real.sqrt_le_sqrt (by nlinarith)
        have h26 : Real.sqrt (K * K) = K := by
          have h27 : 0 ≤ K := by linarith
          rw [show K * K = K ^ 2 by ring]
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h27]
        rw [h26] at h25
        exact h25
      have h28 : c.toReal ≤ (8 / 7 : ℝ) := h_c_real
      have h29 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
      nlinarith
    have h27 : (2 * r) ^ κ = (2 : ℝ) ^ κ * r ^ κ := by
      have h28 : 0 ≤ (2 : ℝ) := by norm_num
      have h29 : 0 ≤ r := by linarith [hδ_le_r, hδ]
      rw [Real.mul_rpow h28 h29]
    have h26 : (μ (S : Set ℝ)).toReal ≤ C_frost * r ^ κ := by
      have h_nonneg_pow : 0 ≤ (2 : ℝ) ^ κ * r ^ κ := by
        apply mul_nonneg
        · exact Real.rpow_nonneg (by norm_num) _
        · exact Real.rpow_nonneg (by linarith [hδ_le_r, hδ]) _
      have h_step : c.toReal * Real.sqrt K * (2 : ℝ) ^ κ * r ^ κ ≤ (10 * K) * (2 : ℝ) ^ κ * r ^ κ := by
        have h : (c.toReal * Real.sqrt K) * ((2 : ℝ) ^ κ * r ^ κ) ≤ (10 * K) * ((2 : ℝ) ^ κ * r ^ κ) :=
          mul_le_mul_of_nonneg_right h22 h_nonneg_pow
        have h_assoc1 : c.toReal * Real.sqrt K * (2 : ℝ) ^ κ * r ^ κ =
            (c.toReal * Real.sqrt K) * ((2 : ℝ) ^ κ * r ^ κ) := by ring
        have h_assoc2 : (10 * K) * (2 : ℝ) ^ κ * r ^ κ =
            (10 * K) * ((2 : ℝ) ^ κ * r ^ κ) := by ring
        rw [h_assoc1, h_assoc2]
        exact h
      calc
        (μ (S : Set ℝ)).toReal
          ≤ c.toReal * Real.sqrt K * (2 * r) ^ κ := h17b
        _ = c.toReal * Real.sqrt K * (2 : ℝ) ^ κ * r ^ κ := by
            rw [h27] <;> ring
        _ ≤ (10 * K) * (2 : ℝ) ^ κ * r ^ κ := h_step
        _ = C_frost * r ^ κ := by
            dsimp only [C_frost] <;> ring
    have h28 : μ (S : Set ℝ) = ENNReal.ofReal (μ (S : Set ℝ)).toReal := by
      exact (ENNReal.ofReal_toReal h7).symm
    rw [hμI_eq, h28]
    exact ENNReal.ofReal_le_ofReal h26
  have hμ_frost : IsDirectionFrostman δ κ C_frost μ :=
    ⟨hμ_prob, hμ_supp_Icc, h_bound⟩
  -- Step 4: Define weights and w_min
  let w : ℝ → ℝ := fun a => (μ {a}).toReal
  let w_min : ℝ := δ ^ (κ + 1)
  have hw_min_pos : 0 < w_min := by positivity
  let A_signif : Finset ℝ := A_fin.filter (fun a => w_min ≤ w a)
  have hA_signif_sub : A_signif ⊆ A_fin := filter_subset _ _
  -- Tiny weight loss in μ: ≤ 2 * δ^κ
  have h_tiny_loss : μ ((A_fin : Set ℝ) \ (A_signif : Set ℝ)) ≤ ENNReal.ofReal (2 * δ ^ κ) := by
    let A_tiny : Finset ℝ := A_fin.filter (fun a => w a < w_min)
    have h1 : (A_tiny : Set ℝ) = (A_fin : Set ℝ) \ (A_signif : Set ℝ) := by
      ext x
      have h2 : x ∈ A_tiny ↔ x ∈ A_fin ∧ w x < w_min := by
        simp [A_tiny, Finset.mem_filter]
        <;> rfl
      have h3 : x ∈ (A_fin : Set ℝ) \ (A_signif : Set ℝ) ↔ x ∈ A_fin ∧ w x < w_min := by
        constructor
        · rintro ⟨hfin, hnot⟩
          have hlt : w x < w_min := by
            by_contra h
            have h' : w_min ≤ w x := by
              simpa [not_lt] using h
            have hsign : x ∈ (A_signif : Set ℝ) := by
              simpa [A_signif, Finset.mem_filter, Finset.mem_coe] using ⟨hfin, h'⟩
            exact hnot hsign
          exact ⟨hfin, hlt⟩
        · rintro ⟨hfin, hlt⟩
          have hnot : x ∉ A_signif := by
            intro hsign
            have h4 : w_min ≤ w x := (Finset.mem_filter.mp hsign).2
            linarith
          exact ⟨hfin, hnot⟩
      constructor
      · intro h; exact h3.mpr (h2.mp h)
      · intro h; exact h2.mpr (h3.mp h)
    have h2 : ∀ a ∈ A_tiny, μ {a} ≤ ENNReal.ofReal w_min := by
      intro a ha
      have h3 : w a < w_min := (Finset.mem_filter.mp ha).2
      have h4 : ENNReal.ofReal (w a) = μ {a} := ENNReal.ofReal_toReal (hμ_finite {a})
      have h5 : μ {a} ≤ ENNReal.ofReal w_min := by
        rw [← h4]
        exact ENNReal.ofReal_le_ofReal h3.le
      exact h5
    have h3 : μ (A_tiny : Set ℝ) = ∑ a ∈ A_tiny, μ {a} := by
      rw [robust_projection.finset_measure_sum μ]
    have h_card : (A_tiny.card : ℝ) ≤ 2 / δ := by
      have h6 : A_tiny ⊆ A := by
        intro x hx
        exact hA_fin_sub (Finset.mem_filter.mp hx |>.1)
      have h7 : (A_tiny.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_le_card h6
      have h8 := card_bound_delta_separated hδ (by linarith) hA_sep hA_sub
      linarith
    have h10 : (A_tiny.card : ℝ) * w_min ≤ 2 * δ ^ κ := by
      calc (A_tiny.card : ℝ) * w_min
        ≤ (2 / δ) * w_min := by gcongr
      _ = (2 / δ) * δ ^ (κ + 1) := by rfl
      _ = 2 * δ ^ κ := by
        have h11 : δ ^ (κ + 1) = δ * δ ^ κ := by
          have h12 : δ ^ (κ + 1) = δ ^ κ * δ ^ (1 : ℝ) := Real.rpow_add hδ κ 1
          rw [h12]
          have h13 : δ ^ (1 : ℝ) = δ := by simp
          rw [h13] <;> ring
        rw [h11] <;> field_simp [hδ.ne'] <;> ring
    have h_sum_eq : ∑ a ∈ A_tiny, ENNReal.ofReal w_min = ENNReal.ofReal ((A_tiny.card : ℝ) * w_min) := by
      have h11 : ∑ a ∈ A_tiny, ENNReal.ofReal w_min = (A_tiny.card : ENNReal) * ENNReal.ofReal w_min := by
        simp [Finset.sum_const]
        <;> ring
      rw [h11]
      have h12 : (A_tiny.card : ENNReal) * ENNReal.ofReal w_min = ENNReal.ofReal ((A_tiny.card : ℝ) * w_min) := by
        have h121 : (A_tiny.card : ENNReal) = ENNReal.ofReal (A_tiny.card : ℝ) := by
          simp
        rw [h121]
        rw [ENNReal.ofReal_mul (show 0 ≤ (A_tiny.card : ℝ) from by positivity)]
      exact h12
    calc
      μ ((A_fin : Set ℝ) \ (A_signif : Set ℝ))
        = μ (A_tiny : Set ℝ) := by rw [←h1]
      _ = ∑ a ∈ A_tiny, μ {a} := h3
      _ ≤ ∑ a ∈ A_tiny, ENNReal.ofReal w_min := Finset.sum_le_sum h2
      _ = ENNReal.ofReal ((A_tiny.card : ℝ) * w_min) := h_sum_eq
      _ ≤ ENNReal.ofReal (2 * δ ^ κ) := ENNReal.ofReal_le_ofReal h10
  -- Step 5: Weight levels
  let M : ℕ := Nat.ceil (Real.logb 2 (1 / w_min)) + 1
  let ε : ℝ := 1 / (32 * (M : ℝ))
  have hε_pos : 0 < ε := by positivity
  let levelSet (j : ℕ) : Finset ℝ :=
    A_signif.filter (fun a => (2 : ℝ)^j * w_min ≤ w a ∧ w a < (2 : ℝ)^(j+1) * w_min)
  let keptLevels : Finset ℕ := (Finset.range M).filter (fun j =>
    ε ≤ ∑ a ∈ levelSet j, w a)
  let S : Finset ℝ := Finset.biUnion keptLevels levelSet
  have hS_sub_A : S ⊆ A := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨j, _, hxj⟩
    have h1 : x ∈ levelSet j := hxj
    have h2 : x ∈ A_signif := (Finset.mem_filter.mp h1).1
    have h3 : x ∈ A_fin := hA_signif_sub h2
    exact hA_fin_sub h3
  -- Step 6: Low-level mass loss in μ
  have h_low_loss : μ ((A_signif : Set ℝ) \ (S : Set ℝ)) ≤ ENNReal.ofReal (1 / 32 : ℝ) := by
    let discarded := (Finset.range M).filter (fun j => ¬(ε ≤ ∑ a ∈ levelSet j, w a))
    have h_coverage : ∀ a ∈ A_signif, ∃ j ∈ Finset.range M, a ∈ levelSet j := by
      intro a ha
      have hwa_ge : w_min ≤ w a := (Finset.mem_filter.mp ha).2
      have hwa_pos : 0 < w a := by linarith [hw_min_pos]
      have hwa_le_one : w a ≤ 1 := by
        have h1 : μ {a} ≤ (1 : ENNReal) := by
          have h2 : μ {a} ≤ μ Set.univ := measure_mono (by simp)
          rw [hμ_prob] at h2
          exact h2
        have h3 : (μ {a}).toReal ≤ 1 := by
          have h4 : (μ {a}).toReal ≤ (1 : ENNReal).toReal :=
            (ENNReal.toReal_le_toReal (hμ_finite {a}) (by simp)).mpr h1
          have h5 : (1 : ENNReal).toReal = 1 := by simp
          rw [h5] at h4
          exact h4
        simpa [w] using h3
      set x : ℝ := w a / w_min with hx_def
      have hx_pos : 0 < x := by positivity
      have hx_ge_one : 1 ≤ x := by
        rw [hx_def]
        have h5 : w a / w_min ≥ 1 := by
          calc w a / w_min ≥ w_min / w_min := by gcongr
            _ = 1 := by field_simp [hw_min_pos.ne']
        exact h5
      set y : ℝ := Real.logb 2 (1 / w_min) with hy_def
      have hM_def : (M : ℝ) = (Nat.ceil y : ℝ) + 1 := by
        dsimp only [M, y] <;> norm_cast
      have hM_gt_y : (M : ℝ) > y := by
        rw [hM_def]
        have h3 : (Nat.ceil y : ℝ) ≥ y := Nat.le_ceil _
        linarith
      have h_2M_gt : (2 : ℝ)^M > 1 / w_min := by
        have h4 : (2 : ℝ)^(M : ℝ) > (2 : ℝ)^y := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          <;> norm_num <;> exact hM_gt_y
        have h5 : (2 : ℝ)^y = 1 / w_min := by
          rw [Real.rpow_logb] <;> norm_num <;> positivity
        rw [h5] at h4
        exact_mod_cast h4
      have hx_lt_2M : x < (2 : ℝ)^M := by
        have h6 : x ≤ 1 / w_min := by
          rw [hx_def]
          gcongr <;> linarith
        have h7 : x < (2 : ℝ)^M := by
          calc x ≤ 1 / w_min := h6
            _ < (2 : ℝ)^M := h_2M_gt
        exact h7
      let j : ℕ := Nat.floor (Real.logb 2 x)
      have hlog_nonneg : 0 ≤ Real.logb 2 x := by
        have h : Real.logb 2 1 ≤ Real.logb 2 x :=
          Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith)
        have h2 : Real.logb 2 1 = 0 := by
          rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
        linarith
      have hj1 : (j : ℝ) ≤ Real.logb 2 x := Nat.floor_le hlog_nonneg
      have hj2 : Real.logb 2 x < (j : ℝ) + 1 := Nat.lt_floor_add_one _
      have h_jpow1 : (2 : ℝ)^j ≤ x := by
        have h_eq : (2 : ℝ)^j = (2 : ℝ)^(j : ℝ) := by norm_cast
        rw [h_eq]
        have h : (2 : ℝ)^(j : ℝ) ≤ (2 : ℝ)^(Real.logb 2 x) := by gcongr <;> norm_num
        have h2 : (2 : ℝ)^(Real.logb 2 x) = x := by
          rw [Real.rpow_logb] <;> norm_num <;> positivity
        rw [h2] at h; exact h
      have h_jpow2 : x < (2 : ℝ)^(j + 1) := by
        have h_eq : (2 : ℝ)^(j + 1) = (2 : ℝ)^(((j + 1 : ℕ) : ℝ)) := by norm_cast
        rw [h_eq]
        have h : (2 : ℝ)^(Real.logb 2 x) < (2 : ℝ)^(((j + 1 : ℕ) : ℝ)) := by
          apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
          have h_exp : Real.logb 2 x < ((j + 1 : ℕ) : ℝ) := by simpa using hj2
          exact h_exp
        have h2 : (2 : ℝ)^(Real.logb 2 x) = x := by
          rw [Real.rpow_logb] <;> norm_num <;> positivity
        rw [h2] at h; exact h
      have h3 : (2 : ℝ)^j * w_min ≤ w a := by
        have h4 : (2 : ℝ)^j * w_min ≤ x * w_min := by gcongr
        have h5 : x * w_min = w a := by
          rw [hx_def]; field_simp [hw_min_pos.ne'] <;> ring
        rw [h5] at h4; exact h4
      have h4 : w a < (2 : ℝ)^(j + 1) * w_min := by
        have h5 : x * w_min < (2 : ℝ)^(j + 1) * w_min := by gcongr
        have h6 : x * w_min = w a := by
          rw [hx_def]; field_simp [hw_min_pos.ne'] <;> ring
        rw [h6] at h5; exact h5
      have hj_lt_M : j < M := by
        have h9 : Real.logb 2 x < (M : ℝ) := by
          have h10 : x < (2 : ℝ)^M := hx_lt_2M
          have h11 : Real.logb 2 x < Real.logb 2 ((2 : ℝ)^M) := by
            rw [Real.logb_lt_logb_iff (by norm_num) (by positivity) (by positivity)]
            exact h10
          have h12 : Real.logb 2 ((2 : ℝ)^M) = (M : ℝ) := by
            have h13 : (2 : ℝ)^M = (2 : ℝ)^(M : ℝ) := by norm_cast
            rw [h13]
            exact Real.logb_rpow (b_pos := by norm_num) (b_ne_one := by norm_num)
          rw [h12] at h11; exact h11
        have h13 : (j : ℝ) < (M : ℝ) := by linarith
        exact_mod_cast h13
      have h_in_levelSet : a ∈ levelSet j := by
        simp only [levelSet, Finset.mem_filter]
        exact ⟨ha, ⟨h3, h4⟩⟩
      exact ⟨j, Finset.mem_range.mpr hj_lt_M, h_in_levelSet⟩
    have h_complement : ∀ j ∈ Finset.range M, j ∈ discarded ↔ j ∉ keptLevels := by
      intro j hj
      simp only [discarded, keptLevels, Finset.mem_filter, hj, true_and]
      <;> tauto
    have h_incl : (A_signif : Set ℝ) \ (S : Set ℝ) ⊆ ⋃ j ∈ discarded, (levelSet j : Set ℝ) := by
      intro x hx
      have hx_signif : x ∈ A_signif := hx.1
      have hx_not_S : x ∉ (S : Set ℝ) := hx.2
      obtain ⟨j, hj_range, hj_level⟩ := h_coverage x hx_signif
      have hj_not_kept : j ∉ keptLevels := by
        intro h_kept
        have h_in_S : x ∈ (S : Set ℝ) := Finset.mem_biUnion.mpr ⟨j, h_kept, hj_level⟩
        exact hx_not_S h_in_S
      have hj_discarded : j ∈ discarded := (h_complement j hj_range).mpr hj_not_kept
      exact Set.mem_iUnion₂.mpr ⟨j, hj_discarded, hj_level⟩
    have h1 : μ ((A_signif : Set ℝ) \ (S : Set ℝ)) ≤ μ (⋃ j ∈ discarded, (levelSet j : Set ℝ)) :=
      measure_mono h_incl
    have h2 : μ (⋃ j ∈ discarded, (levelSet j : Set ℝ)) ≤ ∑ j ∈ discarded, μ (levelSet j : Set ℝ) :=
      MeasureTheory.measure_biUnion_finset_le discarded (fun j => (levelSet j : Set ℝ))
    have h3 : ∀ j ∈ discarded, μ (levelSet j : Set ℝ) < ENNReal.ofReal ε := by
      intro j hj
      have h4 : ¬(ε ≤ ∑ a ∈ levelSet j, w a) := (Finset.mem_filter.mp hj).2
      have h5 : ∑ a ∈ levelSet j, w a < ε := by exact lt_of_not_ge h4
      have h6 : μ (levelSet j : Set ℝ) = ENNReal.ofReal (∑ a ∈ levelSet j, w a) := by
        rw [robust_projection.finset_measure_sum μ]
        have h_sum1 : ∑ a ∈ levelSet j, μ {a} = ∑ a ∈ levelSet j, ENNReal.ofReal (w a) := by
          congr with a
          have h7 : μ {a} = ENNReal.ofReal (w a) := by
            dsimp only [w]
            exact (ENNReal.ofReal_toReal (hμ_finite {a})).symm
          exact h7
        rw [h_sum1]
        have h_nonneg : ∀ a ∈ levelSet j, 0 ≤ w a := fun a ha =>
          have h9 : (2 : ℝ)^j * w_min ≤ w a := (Finset.mem_filter.mp ha).2.1
          have h10 : (1 : ℝ) ≤ (2 : ℝ)^j := by
            have h : ∀ n : ℕ, (1 : ℝ) ≤ (2 : ℝ)^n := by
              intro n; induction n with
              | zero => norm_num
              | succ n ih => simp [pow_succ] at * <;> linarith
            exact h j
          have h11 : w_min ≤ (2 : ℝ)^j * w_min := by
            have h12 : 0 ≤ w_min := by positivity
            nlinarith
          have h13 : w_min ≤ w a := le_trans h11 h9
          have h14 : 0 ≤ w_min := by positivity
          le_trans h14 h13
        rw [ENNReal.ofReal_sum_of_nonneg h_nonneg]
      rw [h6]
      have h_pos1 : 0 ≤ ∑ a ∈ levelSet j, w a := by positivity
      exact (ENNReal.ofReal_lt_ofReal_iff (h := hε_pos)).mpr h5
    have h4 : ∑ j ∈ discarded, μ (levelSet j : Set ℝ) ≤ ∑ j ∈ discarded, ENNReal.ofReal ε := by
      apply Finset.sum_le_sum
      intro j hj
      exact (h3 j hj).le
    have h5 : discarded ⊆ Finset.range M := by
      intro j hj
      exact (Finset.mem_filter.mp hj).1
    have h6 : ∑ j ∈ discarded, ENNReal.ofReal ε ≤ ∑ j ∈ Finset.range M, ENNReal.ofReal ε := by
      apply Finset.sum_le_sum_of_subset_of_nonneg h5
      intro _ _ _; positivity
    have h7 : ∑ j ∈ Finset.range M, ENNReal.ofReal ε = (M : ENNReal) * ENNReal.ofReal ε := by
      simp [Finset.sum_const] <;> ring
    have hM_cast : (M : ENNReal) = ENNReal.ofReal (M : ℝ) := by norm_cast
    have h8 : (M : ENNReal) * ENNReal.ofReal ε = ENNReal.ofReal ((M : ℝ) * ε) := by
      rw [hM_cast]
      have hM_nonneg : 0 ≤ (M : ℝ) := by positivity
      have hε_nonneg : 0 ≤ ε := by positivity
      have h : ENNReal.ofReal (M : ℝ) * ENNReal.ofReal ε = ENNReal.ofReal ((M : ℝ) * ε) := by
        exact Eq.symm (ofReal_mul hM_nonneg)
      exact h
    have h9 : (M : ℝ) * ε = 1 / 32 := by
      dsimp only [ε]
      have hM_pos : (0 : ℝ) < (M : ℝ) := by positivity
      field_simp [hM_pos.ne'] <;> ring
    have h10 : ∑ j ∈ discarded, ENNReal.ofReal ε ≤ ENNReal.ofReal (1 / 32) := by
      calc
        ∑ j ∈ discarded, ENNReal.ofReal ε
          ≤ ∑ j ∈ Finset.range M, ENNReal.ofReal ε := h6
        _ = (M : ENNReal) * ENNReal.ofReal ε := by rw [h7]
        _ = ENNReal.ofReal ((M : ℝ) * ε) := h8
        _ = ENNReal.ofReal (1 / 32) := by rw [h9]
    exact le_trans h1 (le_trans h2 (le_trans h4 h10))
  -- Step 7: Each kept level is a delta-set
  have h_each_level : ∀ j ∈ keptLevels,
      IsRealDeltaSet δ κ (2 * (C_frost / (∑ a ∈ levelSet j, w a))) ((levelSet j) : Set ℝ) := by
    intro j hj
    let S_j := levelSet j
    let W_j : ℝ := ∑ a ∈ S_j, w a
    have hW_j_ge_ε : ε ≤ W_j := (Finset.mem_filter.mp hj).2
    have hW_j_pos : 0 < W_j := by linarith
    have hS_j_nonempty : S_j.Nonempty := by
      by_contra h
      have h' : S_j = ∅ := by simpa using h
      have h_empty : W_j = 0 := by
        dsimp only [W_j]
        rw [h'] <;> simp
      rw [h_empty] at hW_j_ge_ε
      linarith [hε_pos]
    let m_j : ℝ := (2 : ℝ)^j * w_min
    have hm_j_pos : 0 < m_j := by positivity
    have h_weights : ∀ a ∈ S_j, m_j ≤ w a ∧ w a < 2 * m_j := by
      intro a ha
      have h := (Finset.mem_filter.mp ha).2
      have h9 : (2 : ℝ)^(j+1) * w_min = 2 * m_j := by
        dsimp only [m_j] <;> ring
      have h10 : w a < (2 : ℝ)^(j+1) * w_min := h.2
      have h11 : w a < 2 * m_j := by
        calc w a < (2 : ℝ)^(j+1) * w_min := h10
          _ = 2 * m_j := h9
      exact ⟨h.1, h11⟩
    let μ_j : Measure ℝ := (ENNReal.ofReal (1 / W_j)) • μ.restrict (S_j : Set ℝ)
    have hμ_j_prob : μ_j Set.univ = 1 := by
      dsimp only [μ_j]
      have h3 : μ (S_j : Set ℝ) = ENNReal.ofReal W_j := by
        rw [robust_projection.finset_measure_sum μ]
        have h_sum1 : ∑ a ∈ S_j, μ {a} = ∑ a ∈ S_j, ENNReal.ofReal (w a) := by
          congr with a
          have h5 : ENNReal.ofReal (w a) = μ {a} := by
            rw [ENNReal.ofReal_toReal (hμ_finite {a})]
          exact h5.symm
        rw [h_sum1]
        have h_nonneg : ∀ a ∈ S_j, 0 ≤ w a := fun a ha => by
          have h9 : m_j ≤ w a := (h_weights a ha).1
          linarith [hm_j_pos]
        have h_ofReal_sum : ∑ a ∈ S_j, ENNReal.ofReal (w a) = ENNReal.ofReal (∑ a ∈ S_j, w a) := by
          have h_main2 : ∀ (s : Finset ℝ), (∀ x ∈ s, 0 ≤ w x) →
            ∑ a ∈ s, ENNReal.ofReal (w a) = ENNReal.ofReal (∑ a ∈ s, w a) := by
            intro s
            induction s using Finset.induction with
            | empty => intro _; simp
            | @insert a s ha ih =>
              intro h_all
              have h_na : 0 ≤ w a := h_all a (Finset.mem_insert_self a s)
              have h_ns : ∀ x ∈ s, 0 ≤ w x := fun x hx => h_all x (Finset.mem_insert_of_mem hx)
              rw [Finset.sum_insert ha, Finset.sum_insert ha]
              rw [ENNReal.ofReal_add h_na (by positivity), ih h_ns]
          exact h_main2 S_j h_nonneg
        rw [h_ofReal_sum] <;> rfl
      have h_pos1 : 0 ≤ (1 / W_j) := by positivity
      have h_smul : μ_j Set.univ = ENNReal.ofReal (1 / W_j) * μ (S_j : Set ℝ) := by
        dsimp only [μ_j]
        simp [Measure.restrict_apply]
        <;> rfl
      rw [h_smul, h3]
      have h5 : ENNReal.ofReal (1 / W_j) * ENNReal.ofReal W_j = ENNReal.ofReal ((1 / W_j) * W_j) := by
        rw [← ENNReal.ofReal_mul h_pos1]
      rw [h5]
      have h6 : (1 / W_j) * W_j = 1 := by field_simp [hW_j_pos.ne'] <;> ring
      rw [h6]
      <;> simp
    have hμ_j_finite : ∀ (s : Set ℝ), μ_j s ≠ ⊤ := by
      intro s
      have h1 : μ_j s ≤ μ_j Set.univ := measure_mono (by simp)
      rw [hμ_j_prob] at h1
      exact ne_top_of_le_ne_top (by simp) h1
    have hμ_j_support : μ_j.support ⊆ (S_j : Set ℝ) := by
      have h_Sj_closed : IsClosed (S_j : Set ℝ) := by exact Finset.isClosed S_j
      have h_null : μ_j ((S_j : Set ℝ)ᶜ) = 0 := by
        dsimp only [μ_j]
        have h1 : μ.restrict (S_j : Set ℝ) ((S_j : Set ℝ)ᶜ) = 0 := by
          have h_meas : MeasurableSet (S_j : Set ℝ) := Finset.measurableSet S_j
          have h_eq1 : μ.restrict (S_j : Set ℝ) ((S_j : Set ℝ)ᶜ) = μ (((S_j : Set ℝ)ᶜ) ∩ (S_j : Set ℝ)) := by exact Measure.restrict_apply' h_meas
          rw [h_eq1]
          have h_inter : ((S_j : Set ℝ)ᶜ) ∩ (S_j : Set ℝ) = ∅ := by simp
          rw [h_inter] <;> simp
        have h_smul : ((ENNReal.ofReal (1 / W_j)) • μ.restrict (S_j : Set ℝ)) ((S_j : Set ℝ)ᶜ) =
            ENNReal.ofReal (1 / W_j) * μ.restrict (S_j : Set ℝ) ((S_j : Set ℝ)ᶜ) := by exact (toReal_eq_toReal_iff' (hμ_j_finite (↑S_j)ᶜ) (hμ_j_finite (↑S_j)ᶜ)).mp rfl
        rw [h_smul, h1] <;> simp
      have h_in : (S_j : Set ℝ) ∈ {t : Set ℝ | IsClosed t ∧ μ_j tᶜ = 0} := ⟨h_Sj_closed, h_null⟩
      rw [MeasureTheory.Measure.support_eq_sInter]
      exact Set.sInter_subset_of_mem h_in
    have hμ_j_frost : IsDirectionFrostman δ κ (C_frost / W_j) μ_j := by
      have h1 : μ_j Set.univ = 1 := hμ_j_prob
      have h2 : μ_j.support ⊆ Set.Icc 0 1 := by
        intro x hx
        have h3 : x ∈ (S_j : Set ℝ) := hμ_j_support hx
        exact hA_fin_in_Icc (hA_signif_sub ((Finset.mem_filter.mp h3).1))
      have h3 : ∀ (a r : ℝ), δ ≤ r → r ≤ 1 →
          μ_j (Set.Icc (a - r) (a + r)) ≤ ENNReal.ofReal ((C_frost / W_j) * r ^ κ) := by
        intro a r hδr hr1
        dsimp only [μ_j]
        have h4 : μ_j (Set.Icc (a - r) (a + r)) =
            ENNReal.ofReal (1 / W_j) * μ.restrict (S_j : Set ℝ) (Set.Icc (a - r) (a + r)) := by
          rw [Measure.smul_apply] <;> ring
        rw [h4]
        have hr_pos : 0 ≤ r := by linarith [hδ, hδr]
        have h5 : μ.restrict (S_j : Set ℝ) (Set.Icc (a - r) (a + r)) ≤
            μ (Set.Icc (a - r) (a + r)) := by
          have h_meas : MeasurableSet (Set.Icc (a - r) (a + r)) := by exact measurableSet_Icc
          have h_eq : μ.restrict (S_j : Set ℝ) (Set.Icc (a - r) (a + r)) =
              μ ((Set.Icc (a - r) (a + r)) ∩ (S_j : Set ℝ)) := by
            rw [Measure.restrict_apply h_meas]
          rw [h_eq]
          have h_sub : (Set.Icc (a - r) (a + r)) ∩ (S_j : Set ℝ) ⊆ Set.Icc (a - r) (a + r) := by
            intro x hx
            exact hx.1
          exact measure_mono h_sub
        have h6 : μ (Set.Icc (a - r) (a + r)) ≤ ENNReal.ofReal (C_frost * r ^ κ) :=
          hμ_frost.2.2 a r hδr hr1
        have h7 : μ.restrict (S_j : Set ℝ) (Set.Icc (a - r) (a + r)) ≤
            ENNReal.ofReal (C_frost * r ^ κ) := le_trans h5 h6
        have h_pos1 : 0 ≤ 1 / W_j := by positivity
        have h_pos2 : 0 ≤ C_frost * r ^ κ := by
          have hC_pos : 0 < C_frost := hC_frost_pos
          have hrp_pos : 0 ≤ r ^ κ := Real.rpow_nonneg hr_pos κ
          exact mul_nonneg hC_pos.le hrp_pos
        have h8 : ENNReal.ofReal (1 / W_j) * μ.restrict (S_j : Set ℝ) (Set.Icc (a - r) (a + r)) ≤
            ENNReal.ofReal (1 / W_j) * ENNReal.ofReal (C_frost * r ^ κ) :=
          mul_le_mul_left' h7 _
        have h9 : ENNReal.ofReal (1 / W_j) * ENNReal.ofReal (C_frost * r ^ κ) =
            ENNReal.ofReal ((1 / W_j) * (C_frost * r ^ κ)) :=
          (ENNReal.ofReal_mul (hp := h_pos1)).symm
        have h10 : (1 / W_j) * (C_frost * r ^ κ) = (C_frost / W_j) * r ^ κ := by ring
        calc
          ENNReal.ofReal (1 / W_j) * μ.restrict (S_j : Set ℝ) (Set.Icc (a - r) (a + r))
            ≤ ENNReal.ofReal (1 / W_j) * ENNReal.ofReal (C_frost * r ^ κ) := h8
          _ = ENNReal.ofReal ((1 / W_j) * (C_frost * r ^ κ)) := h9
          _ = ENNReal.ofReal ((C_frost / W_j) * r ^ κ) := by rw [h10]
      exact ⟨h1, h2, h3⟩
    let w_j : ℝ → ℝ := fun a => (μ_j {a}).toReal
    have h_w_j : ∀ a ∈ S_j, μ_j {a} = ENNReal.ofReal (w_j a) := by
      intro a _
      have h_eq : ENNReal.ofReal (w_j a) = μ_j {a} := by
        rw [ENNReal.ofReal_toReal (hμ_j_finite {a})]
      exact h_eq.symm
    have h_weights_j : ∀ a ∈ S_j, m_j / W_j ≤ w_j a ∧ w_j a < 2 * (m_j / W_j) := by
      intro a ha
      have h_pos1 : 0 < 1 / W_j := by positivity
      have h_restrict : μ.restrict (S_j : Set ℝ) {a} = μ {a} := by
        have h_meas : MeasurableSet (S_j : Set ℝ) := Finset.measurableSet S_j
        have h_eq1 : μ.restrict (S_j : Set ℝ) {a} = μ ({a} ∩ (S_j : Set ℝ)) := by exact Measure.restrict_apply' h_meas
        rw [h_eq1]
        have h_inter : {a} ∩ (S_j : Set ℝ) = {a} := by
          ext x; simp [ha] <;> tauto
        rw [h_inter]
      have h_smul : μ_j {a} = ENNReal.ofReal (1 / W_j) * μ.restrict (S_j : Set ℝ) {a} := by
        dsimp only [μ_j]
        exact (toReal_eq_toReal_iff' (hμ_j_finite {a}) (hμ_j_finite {a})).mp rfl
      have h_μa : μ {a} = ENNReal.ofReal (w a) := by
        have h4 : ENNReal.ofReal (w a) = μ {a} := by
          rw [ENNReal.ofReal_toReal (hμ_finite {a})]
        exact h4.symm
      have h1 : μ_j {a} = ENNReal.ofReal ((1 / W_j) * w a) := by
        rw [h_smul, h_restrict, h_μa]
        rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
      have h4 : w_j a = (1 / W_j) * w a := by
        dsimp only [w_j]
        rw [h1]
        have h5 : 0 ≤ (1 / W_j) * w a := by positivity
        rw [ENNReal.toReal_ofReal h5]
      rw [h4]
      have h5 : m_j ≤ w a := (h_weights a ha).1
      have h6 : w a < 2 * m_j := (h_weights a ha).2
      have h7 : 0 < 1 / W_j := by positivity
      constructor
      · have h7 : 0 ≤ 1 / W_j := by positivity
        have h10 : (1 / W_j) * m_j ≤ (1 / W_j) * w a := mul_le_mul_of_nonneg_left h5 h7
        have h11 : (1 / W_j) * m_j = m_j / W_j := by ring
        rw [h11] at h10
        exact h10
      · have h7 : 0 < 1 / W_j := by positivity
        have h8 : (1 / W_j) * w a < (1 / W_j) * (2 * m_j) := by
          exact mul_lt_mul_of_pos_left h6 h7
        have h9 : (1 / W_j) * (2 * m_j) = 2 * (m_j / W_j) := by ring
        rw [h9] at h8
        exact h8
    have hW_j_norm : ∑ a ∈ S_j, w_j a = (1 : ℝ) := by
      have hSj_meas : MeasurableSet (S_j : Set ℝ) := Finset.measurableSet S_j
      have h_compl_null : μ_j ((S_j : Set ℝ)ᶜ) = 0 := by
        dsimp only [μ_j]
        have h1 : μ.restrict (S_j : Set ℝ) ((S_j : Set ℝ)ᶜ) = 0 := by
          have h_meas : MeasurableSet (S_j : Set ℝ) := Finset.measurableSet S_j
          have h_eq1 : μ.restrict (S_j : Set ℝ) ((S_j : Set ℝ)ᶜ) = μ (((S_j : Set ℝ)ᶜ) ∩ (S_j : Set ℝ)) := by exact Measure.restrict_apply' hSj_meas
          rw [h_eq1]
          have h_inter : ((S_j : Set ℝ)ᶜ) ∩ (S_j : Set ℝ) = ∅ := by simp
          rw [h_inter] <;> simp
        have h_smul : ((ENNReal.ofReal (1 / W_j)) • μ.restrict (S_j : Set ℝ)) ((S_j : Set ℝ)ᶜ) =
            ENNReal.ofReal (1 / W_j) * μ.restrict (S_j : Set ℝ) ((S_j : Set ℝ)ᶜ) := by exact (toReal_eq_toReal_iff' (hμ_j_finite (↑S_j)ᶜ) (hμ_j_finite (↑S_j)ᶜ)).mp rfl
        rw [h_smul, h1] <;> simp
      have h2 : μ_j (S_j : Set ℝ) = μ_j Set.univ := by
        have h_disj : Disjoint (S_j : Set ℝ) ((S_j : Set ℝ)ᶜ) := by exact HasSubset.Subset.disjoint_compl_right fun ⦃a⦄ a_1 => a_1
        have h_union : (S_j : Set ℝ) ∪ ((S_j : Set ℝ)ᶜ) = Set.univ := by simp
        have h3 : μ_j Set.univ = μ_j (S_j : Set ℝ) + μ_j ((S_j : Set ℝ)ᶜ) := by
          rw [← h_union]
          exact measure_union h_disj hSj_meas.compl
        rw [h3, h_compl_null] <;> simp
      have h1 : ∑ a ∈ S_j, μ_j {a} = μ_j (S_j : Set ℝ) := by
        exact (robust_projection.finset_measure_sum μ_j).symm
      have h3 : ∀ a ∈ S_j, μ_j {a} ≠ ⊤ := fun a _ => hμ_j_finite {a}
      have h4 : (∑ a ∈ S_j, w_j a) = (∑ a ∈ S_j, μ_j {a}).toReal := by
        rw [ENNReal.toReal_sum h3]
        <;> rfl
      rw [h4, h1, h2, hμ_j_prob] <;> simp
    have h_main_raw : IsRealDeltaSet δ κ (2 * (C_frost / W_j) / 1) (S_j : Set ℝ) :=
      weight_level_to_delta_set_direct (S := S_j) (μ := μ_j)
        hδ hδ_dyadic hδ_lt_one hκ_pos hκ_le_one (show 0 < C_frost / W_j from by positivity)
        (fun (x : ℝ) (hx : x ∈ S_j) (y : ℝ) (hy : y ∈ S_j) (hne : x ≠ y) =>
          hA_sep x (hA_fin_sub (hA_signif_sub ((Finset.mem_filter.mp hx).1)))
            y (hA_fin_sub (hA_signif_sub ((Finset.mem_filter.mp hy).1))) hne)
        hS_j_nonempty hμ_j_frost hμ_j_support w_j h_w_j (m_j / W_j) (by positivity) h_weights_j
        (1 : ℝ) hW_j_norm (by positivity)
    have h_div_one : (2 * (C_frost / W_j) / 1 : ℝ) = 2 * (C_frost / W_j) := by ring
    have h_main : IsRealDeltaSet δ κ (2 * (C_frost / W_j)) (S_j : Set ℝ) := by
      rw [h_div_one] at h_main_raw
      exact h_main_raw
    exact h_main
  -- Step 8: Union is delta-set
  have h_c_ge_one : (1 : ENNReal) ≤ c := by
    dsimp only [c]
    have h1 : ν (A_fin : Set ℝ) ≤ 1 := by
      have h2 : ν (A_fin : Set ℝ) ≤ ν Set.univ := measure_mono (by simp)
      have hν_univ : ν Set.univ = 1 := by exact measure_univ
      rw [hν_univ] at h2; exact h2
    have h3 : (ν (A_fin : Set ℝ))⁻¹ ≥ 1 := by
      have h4 : (1 : ENNReal) ≤ (ν (A_fin : Set ℝ))⁻¹ := ENNReal.one_le_inv.mpr h1
      exact h4
    exact h3
  have hνA_fin_ne_top : ν (A_fin : Set ℝ) ≠ ⊤ := by
    have h1 : ν (A_fin : Set ℝ) ≤ 1 := by
      have h2 : ν (A_fin : Set ℝ) ≤ ν Set.univ := measure_mono (by simp)
      have hν_univ : ν Set.univ = 1 := by exact measure_univ
      rw [hν_univ] at h2; exact h2
    exact ne_top_of_le_ne_top (by simp) h1
  have hc_ne_zero : c ≠ 0 := by
    dsimp only [c]
    exact ENNReal.inv_ne_zero.mpr hνA_fin_ne_top
  have hc_ne_top : c ≠ ⊤ := by
    dsimp only [c]
    exact ENNReal.inv_ne_top.mpr hνA_fin_ne_zero
  have h_div_le_self : ∀ (x : ENNReal), x / c ≤ x := by
    intro x
    rw [ENNReal.div_le_iff' hc_ne_zero hc_ne_top]
    have h : c * x ≥ x := by
      calc c * x ≥ (1 : ENNReal) * x := by gcongr
        _ = x := by simp
    exact h
  have h_ν_div_c : ∀ (s : Set ℝ), s ⊆ (A_fin : Set ℝ) → ν s = μ s / c := by
    intro s hs
    dsimp only [μ]
    have h_s_meas : MeasurableSet s := by
      have h_fin : Set.Finite s := Set.Finite.subset (Finset.finite_toSet A_fin) hs
      exact h_fin.measurableSet
    have h_meas : μ s = c * ν s := by
      rw [Measure.smul_apply, Measure.restrict_apply h_s_meas]
      have h_inter : s ∩ (A_fin : Set ℝ) = s := by
        ext y; simp only [Set.mem_inter_iff] <;> tauto
      rw [h_inter] <;> ring
    have h_cancel : c * ν s / c = ν s := by
      rw [mul_comm c (ν s)]
      exact ENNReal.mul_div_cancel_right hc_ne_zero hc_ne_top
    rw [h_meas, h_cancel]
  have hS_sub_signif : (S : Set ℝ) ⊆ (A_signif : Set ℝ) := by
    dsimp only [S]
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨j, _, hxj⟩
    have h1 : x ∈ levelSet j := hxj
    exact (Finset.mem_filter.mp h1).1
  have h_decomp : (A_fin : Set ℝ) = ((A_fin : Set ℝ) \ (A_signif : Set ℝ)) ∪ (((A_signif : Set ℝ) \ (S : Set ℝ)) ∪ (S : Set ℝ)) := by
    ext x
    simp only [Set.mem_union, Set.mem_diff]
    constructor
    · intro hx
      by_cases h : x ∈ (A_signif : Set ℝ)
      · by_cases hS : x ∈ (S : Set ℝ)
        · exact Or.inr (Or.inr hS)
        · exact Or.inr (Or.inl ⟨h, hS⟩)
      · exact Or.inl ⟨hx, h⟩
    · intro h
      rcases h with (h | h)
      · exact h.1
      · rcases h with (h' | h')
        · have h1 : x ∈ (A_fin : Set ℝ) := hA_signif_sub h'.1
          exact h1
        · have h1 : x ∈ (A_signif : Set ℝ) := hS_sub_signif h'
          have h2 : x ∈ (A_fin : Set ℝ) := hA_signif_sub h1
          exact h2
  have h_union_bound : ν (A_fin : Set ℝ) ≤ ν ((A_fin : Set ℝ) \ (A_signif : Set ℝ)) + ν ((A_signif : Set ℝ) \ (S : Set ℝ)) + ν (S : Set ℝ) := by
    let X := (A_fin : Set ℝ) \ (A_signif : Set ℝ)
    let Y := (A_signif : Set ℝ) \ (S : Set ℝ)
    let Z := (S : Set ℝ)
    have h_eq : ν (A_fin : Set ℝ) = ν (X ∪ (Y ∪ Z)) := by
      rw [show (A_fin : Set ℝ) = X ∪ (Y ∪ Z) from h_decomp]
    rw [h_eq]
    have h_u1 : ν (X ∪ (Y ∪ Z)) ≤ ν X + ν (Y ∪ Z) := by
      exact measure_union_le X (Y ∪ Z)
    have h_u2 : ν (Y ∪ Z) ≤ ν Y + ν Z := by
      exact measure_union_le Y Z
    have h_u3 : ν X + ν (Y ∪ Z) ≤ ν X + (ν Y + ν Z) := by
      gcongr
      <;> exact h_u2
    have h_u4 : ν X + (ν Y + ν Z) = ν X + ν Y + ν Z := by
      rw [add_assoc]
    calc
      ν (X ∪ (Y ∪ Z)) ≤ ν X + ν (Y ∪ Z) := h_u1
      _ ≤ ν X + (ν Y + ν Z) := h_u3
      _ = ν X + ν Y + ν Z := h_u4
  have hS_nonempty : (S : Set ℝ).Nonempty := by
    by_contra h
    have h_empty : (S : Set ℝ) = ∅ := by simpa using h
    have hνS : ν (S : Set ℝ) = 0 := by rw [h_empty] <;> simp
    have h1 : ν (A_fin : Set ℝ) ≥ ENNReal.ofReal (7 / 8 : ℝ) := by
      have h1' : (7 / 8 : ENNReal) ≤ ν (A_fin : Set ℝ) := hνA_fin_ge
      have h_eq : (7 / 8 : ENNReal) = ENNReal.ofReal (7 / 8 : ℝ) := by
        have h_pos8 : (0 : ℝ) < 8 := by norm_num
        have h : ENNReal.ofReal (7 / 8 : ℝ) = (7 / 8 : ENNReal) := by
          rw [show (7 / 8 : ℝ) = (7 : ℝ) / (8 : ℝ) by norm_num]
          rw [ENNReal.ofReal_div_of_pos h_pos8]
          <;> norm_cast
        exact h.symm
      rw [h_eq] at h1'
      exact h1'
    have h2 : ν ((A_fin : Set ℝ) \ (A_signif : Set ℝ)) ≤ μ ((A_fin : Set ℝ) \ (A_signif : Set ℝ)) := by
      have h3 := h_ν_div_c ((A_fin : Set ℝ) \ (A_signif : Set ℝ)) (by simp)
      rw [h3]
      exact h_div_le_self _
    have h3 : ν ((A_signif : Set ℝ) \ (S : Set ℝ)) ≤ μ ((A_signif : Set ℝ) \ (S : Set ℝ)) := by
      have h4 : ((A_signif : Set ℝ) \ (S : Set ℝ)) ⊆ (A_fin : Set ℝ) := by
        apply Set.Subset.trans (by simp) hA_signif_sub
      have h5 := h_ν_div_c _ h4
      rw [h5]
      exact h_div_le_self _
    have h4' : ν (A_fin : Set ℝ) ≤ ν ((A_fin : Set ℝ) \ (A_signif : Set ℝ)) + ν ((A_signif : Set ℝ) \ (S : Set ℝ)) := by
      have h5 := h_union_bound
      rw [hνS] at h5
      simpa using h5
    have h6 : ν (A_fin : Set ℝ) ≤ ENNReal.ofReal (2 * δ ^ κ) + ENNReal.ofReal (1 / 32 : ℝ) := by
      calc ν (A_fin : Set ℝ)
        ≤ ν ((A_fin : Set ℝ) \ (A_signif : Set ℝ)) + ν ((A_signif : Set ℝ) \ (S : Set ℝ)) := h4'
      _ ≤ μ ((A_fin : Set ℝ) \ (A_signif : Set ℝ)) + μ ((A_signif : Set ℝ) \ (S : Set ℝ)) := by gcongr
      _ ≤ ENNReal.ofReal (2 * δ ^ κ) + ENNReal.ofReal (1 / 32 : ℝ) := by
        exact add_le_add h_tiny_loss h_low_loss
    have h7 : ENNReal.ofReal (7 / 8 : ℝ) ≤ ENNReal.ofReal (2 * δ ^ κ) + ENNReal.ofReal (1 / 32 : ℝ) := le_trans h1 h6
    have h8 : 2 * δ ^ κ ≤ 1 / 64 := by
      have h9 : δ ^ κ ≤ 1 / 128 := hδ_small
      calc 2 * δ ^ κ ≤ 2 * (1 / 128 : ℝ) := by gcongr
        _ = 1 / 64 := by norm_num
    have h10 : ENNReal.ofReal (2 * δ ^ κ) + ENNReal.ofReal (1 / 32 : ℝ) ≤ ENNReal.ofReal (3 / 64 : ℝ) := by
      have h11 : 2 * δ ^ κ + 1 / 32 ≤ 3 / 64 := by
        have h12 : 2 * δ ^ κ ≤ 1 / 64 := h8
        linarith
      have h13 : 0 ≤ 2 * δ ^ κ := by positivity
      have h14 : 0 ≤ (1 / 32 : ℝ) := by positivity
      have h15 : ENNReal.ofReal (2 * δ ^ κ) + ENNReal.ofReal (1 / 32 : ℝ) = ENNReal.ofReal (2 * δ ^ κ + 1 / 32) := by
        rw [← ENNReal.ofReal_add h13 h14]
      rw [h15]
      exact ENNReal.ofReal_le_ofReal h11
    have h_contra : ENNReal.ofReal (7 / 8 : ℝ) ≤ ENNReal.ofReal (3 / 64 : ℝ) :=
      le_trans h7 h10
    have h_false : (7 / 8 : ℝ) ≤ (3 / 64 : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h_contra
    norm_num at h_false
  let C_j : ℕ → ℝ := fun j => 2 * (C_frost / (∑ a ∈ levelSet j, w a))
  have hC_j_pos : ∀ j ∈ keptLevels, 0 < C_j j := by
    intro j hj
    dsimp only [C_j]
    have hW_ge : ε ≤ ∑ a ∈ levelSet j, w a := (Finset.mem_filter.mp hj).2
    have hW_pos : 0 < ∑ a ∈ levelSet j, w a := by linarith [hε_pos]
    have h : 0 < C_frost / (∑ a ∈ levelSet j, w a) := by
      apply div_pos hC_frost_pos hW_pos
    positivity
  have h_each' : ∀ j ∈ keptLevels, IsRealDeltaSet δ κ (C_j j) ((levelSet j) : Set ℝ) := by
    intro j hj
    have h := h_each_level j hj
    simpa [C_j] using h
  have h_sum_le : ∑ j ∈ keptLevels, C_j j ≤ 64 * C_frost * (M : ℝ)^2 := by
    have h1 : ∀ j ∈ keptLevels, C_j j ≤ 2 * C_frost * (32 * (M : ℝ)) := by
      intro j hj
      let W_j : ℝ := ∑ a ∈ levelSet j, w a
      have hW_ge : ε ≤ W_j := (Finset.mem_filter.mp hj).2
      dsimp only [C_j]
      have hM_pos : (0 : ℝ) < (M : ℝ) := by positivity
      have h2 : 1 / W_j ≤ 32 * (M : ℝ) := by
        have h3 : ε ≤ W_j := hW_ge
        have h4 : 1 / W_j ≤ 1 / ε := by gcongr
        have h5 : 1 / ε = 32 * (M : ℝ) := by
          dsimp only [ε]
          field_simp [hM_pos.ne'] <;> ring
        rw [h5] at h4
        exact h4
      have h3 : 2 * (C_frost / W_j) ≤ 2 * C_frost * (32 * (M : ℝ)) := by
        have h4 : C_frost / W_j = C_frost * (1 / W_j) := by ring
        rw [h4]
        have h5 : 0 ≤ C_frost := by linarith [hC_frost_pos]
        have h6 : C_frost * (1 / W_j) ≤ C_frost * (32 * (M : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 h5
        linarith
      exact h3
    have h2 : ∑ j ∈ keptLevels, C_j j ≤ ∑ j ∈ keptLevels, (2 * C_frost * (32 * (M : ℝ))) := by
      apply Finset.sum_le_sum
      intro j hj
      exact h1 j hj
    have h3 : keptLevels ⊆ Finset.range M := by
      intro j hj
      exact (Finset.mem_filter.mp hj).1
    have h4 : ∑ j ∈ keptLevels, (2 * C_frost * (32 * (M : ℝ))) ≤ ∑ j ∈ Finset.range M, (2 * C_frost * (32 * (M : ℝ))) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg h3
      intro _ _ _; positivity
    have h5 : ∑ j ∈ Finset.range M, (2 * C_frost * (32 * (M : ℝ))) = (M : ℝ) * (2 * C_frost * (32 * (M : ℝ))) := by
      simp [Finset.sum_const] <;> ring
    have h6 : (M : ℝ) * (2 * C_frost * (32 * (M : ℝ))) = 64 * C_frost * (M : ℝ)^2 := by ring
    calc
      ∑ j ∈ keptLevels, C_j j ≤ ∑ j ∈ keptLevels, (2 * C_frost * (32 * (M : ℝ))) := h2
      _ ≤ ∑ j ∈ Finset.range M, (2 * C_frost * (32 * (M : ℝ))) := h4
      _ = (M : ℝ) * (2 * C_frost * (32 * (M : ℝ))) := h5
      _ = 64 * C_frost * (M : ℝ)^2 := h6
  have h_union_raw : IsRealDeltaSet δ κ (∑ j ∈ keptLevels, C_j j) (S : Set ℝ) :=
    robust_projection.union_real_delta_sets keptLevels levelSet C_j hδ hδ_dyadic hκ_pos hκ_le_one hC_j_pos hS_nonempty h_each'
  have h_mono : ∀ (C1 C2 : ℝ), C1 ≤ C2 → IsRealDeltaSet δ κ C1 (S : Set ℝ) → IsRealDeltaSet δ κ C2 (S : Set ℝ) := by
    intro C1 C2 hle h
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    refine ⟨h1, h2, h3, h4, h5, h6, h7, by linarith, ?_⟩
    intro r Q hr hQ hδr hr1
    have h10 := h9 hr hQ hδr hr1
    calc ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy (S : Set ℝ) ∩ Q))
      ≤ ENNReal.ofReal C1 * ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy (S : Set ℝ))) * ENNReal.ofReal (r ^ κ) := h10
    _ ≤ ENNReal.ofReal C2 * ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy (S : Set ℝ))) * ENNReal.ofReal (r ^ κ) := by
      gcongr
  have h_union : IsRealDeltaSet δ κ (64 * C_frost * (M : ℝ)^2) (S : Set ℝ) :=
    h_mono (∑ j ∈ keptLevels, C_j j) (64 * C_frost * (M : ℝ)^2) h_sum_le h_union_raw
  -- Step 9: Mass retention in ν
  have h_mass_retention : ENNReal.ofReal (3 / 4 : ℝ) ≤ ν (S : Set ℝ) := by
    have h1 : ν (A_fin : Set ℝ) ≥ ENNReal.ofReal (7 / 8 : ℝ) := by
      have h1' : (7 / 8 : ENNReal) ≤ ν (A_fin : Set ℝ) := hνA_fin_ge
      have h_eq : (7 / 8 : ENNReal) = ENNReal.ofReal (7 / 8 : ℝ) := by
        have h_pos8 : (0 : ℝ) < 8 := by norm_num
        have h : ENNReal.ofReal (7 / 8 : ℝ) = (7 / 8 : ENNReal) := by
          rw [show (7 / 8 : ℝ) = (7 : ℝ) / (8 : ℝ) by norm_num]
          rw [ENNReal.ofReal_div_of_pos h_pos8]
          <;> norm_cast
        exact h.symm
      rw [h_eq] at h1'
      exact h1'
    have h2 : ν ((A_fin : Set ℝ) \ (A_signif : Set ℝ)) ≤ μ ((A_fin : Set ℝ) \ (A_signif : Set ℝ)) := by
      have h3 := h_ν_div_c ((A_fin : Set ℝ) \ (A_signif : Set ℝ)) (by simp)
      rw [h3]
      exact h_div_le_self _
    have h3 : ν ((A_signif : Set ℝ) \ (S : Set ℝ)) ≤ μ ((A_signif : Set ℝ) \ (S : Set ℝ)) := by
      have h4 : ((A_signif : Set ℝ) \ (S : Set ℝ)) ⊆ (A_fin : Set ℝ) := by
        apply Set.Subset.trans (by simp) hA_signif_sub
      have h5 := h_ν_div_c _ h4
      rw [h5]
      exact h_div_le_self _
    have h2' : ν ((A_fin : Set ℝ) \ (A_signif : Set ℝ)) ≤ ENNReal.ofReal (2 * δ ^ κ) :=
      le_trans h2 h_tiny_loss
    have h3' : ν ((A_signif : Set ℝ) \ (S : Set ℝ)) ≤ ENNReal.ofReal (1 / 32 : ℝ) :=
      le_trans h3 h_low_loss
    have h_union_bound2 : ν (A_fin : Set ℝ) ≤ ENNReal.ofReal (2 * δ ^ κ) + ENNReal.ofReal (1 / 32 : ℝ) + ν (S : Set ℝ) := by
      calc ν (A_fin : Set ℝ)
        ≤ ν ((A_fin : Set ℝ) \ (A_signif : Set ℝ)) + ν ((A_signif : Set ℝ) \ (S : Set ℝ)) + ν (S : Set ℝ) := h_union_bound
      _ ≤ ENNReal.ofReal (2 * δ ^ κ) + ENNReal.ofReal (1 / 32 : ℝ) + ν (S : Set ℝ) := by gcongr
    have h4 : ν (A_fin : Set ℝ) - ENNReal.ofReal (2 * δ ^ κ) - ENNReal.ofReal (1 / 32 : ℝ) ≤ ν (S : Set ℝ) := by
      have h5 : ν (A_fin : Set ℝ) ≤ (ENNReal.ofReal (1 / 32 : ℝ) + ν (S : Set ℝ)) + ENNReal.ofReal (2 * δ ^ κ) := by
        have h51 := h_union_bound2
        simpa [add_assoc, add_comm, add_left_comm] using h51
      have h6 : ν (A_fin : Set ℝ) - ENNReal.ofReal (2 * δ ^ κ) ≤ ENNReal.ofReal (1 / 32 : ℝ) + ν (S : Set ℝ) :=
        tsub_le_iff_right.mpr h5
      have h6' : ν (A_fin : Set ℝ) - ENNReal.ofReal (2 * δ ^ κ) ≤ ν (S : Set ℝ) + ENNReal.ofReal (1 / 32 : ℝ) := by
        have h_comm : ENNReal.ofReal (1 / 32 : ℝ) + ν (S : Set ℝ) = ν (S : Set ℝ) + ENNReal.ofReal (1 / 32 : ℝ) := by
          apply add_comm
        rw [h_comm] at h6
        exact h6
      exact tsub_le_iff_right.mpr h6'
    have h7 : ENNReal.ofReal (7 / 8 : ℝ) - ENNReal.ofReal (2 * δ ^ κ) - ENNReal.ofReal (1 / 32 : ℝ) ≤ ν (A_fin : Set ℝ) - ENNReal.ofReal (2 * δ ^ κ) - ENNReal.ofReal (1 / 32 : ℝ) := by
      gcongr
    have h8 : ENNReal.ofReal (7 / 8 : ℝ) - ENNReal.ofReal (2 * δ ^ κ) - ENNReal.ofReal (1 / 32 : ℝ) ≤ ν (S : Set ℝ) :=
      le_trans h7 h4
    have h91 : (2 * δ ^ κ : ℝ) ≤ 7 / 8 := by linarith [hδ_small]
    have h92 : (7 / 8 : ℝ) - 2 * δ ^ κ ≥ 1 / 32 := by linarith [hδ_small]
    have h_eq1 : ENNReal.ofReal (7 / 8 : ℝ) - ENNReal.ofReal (2 * δ ^ κ) = ENNReal.ofReal ((7 / 8 : ℝ) - 2 * δ ^ κ) := by
      have hq : 0 ≤ (2 * δ ^ κ : ℝ) := by positivity
      have h : ENNReal.ofReal ((7 / 8 : ℝ) - (2 * δ ^ κ)) = ENNReal.ofReal (7 / 8 : ℝ) - ENNReal.ofReal (2 * δ ^ κ) :=
        ENNReal.ofReal_sub (7 / 8 : ℝ) (hq := hq)
      exact h.symm
    have h_eq2 : ENNReal.ofReal ((7 / 8 : ℝ) - 2 * δ ^ κ) - ENNReal.ofReal (1 / 32 : ℝ) = ENNReal.ofReal ((7 / 8 : ℝ) - 2 * δ ^ κ - 1 / 32) := by
      have hq : 0 ≤ (1 / 32 : ℝ) := by positivity
      have h : ENNReal.ofReal (((7 / 8 : ℝ) - 2 * δ ^ κ) - (1 / 32 : ℝ)) = ENNReal.ofReal ((7 / 8 : ℝ) - 2 * δ ^ κ) - ENNReal.ofReal (1 / 32 : ℝ) :=
        ENNReal.ofReal_sub ((7 / 8 : ℝ) - 2 * δ ^ κ) (hq := hq)
      exact h.symm
    have h93 : (7 / 8 : ℝ) - 2 * δ ^ κ - 1 / 32 ≥ 3 / 4 := by linarith [hδ_small]
    have h10 : ENNReal.ofReal ((7 / 8 : ℝ) - 2 * δ ^ κ - 1 / 32) ≥ ENNReal.ofReal (3 / 4 : ℝ) :=
      ENNReal.ofReal_le_ofReal h93
    rw [h_eq1, h_eq2] at h8
    exact le_trans h10 h8
  have h_C_out_eq : (64 * C_frost * (M : ℝ)^2) = energyToLargeMassDeltaSetC δ κ K := by
    dsimp only [energyToLargeMassDeltaSetC, C_frost, M, w_min]
    have h9 : 1 / δ ^ (κ + 1) = δ ^ (-(κ + 1)) := by
      rw [Real.rpow_neg (by positivity)]
      <;> field_simp
    rw [h9]
    have h10 : -(κ + 1) = -1 - κ := by ring
    rw [h10]
    have h11 : ((Nat.ceil (Real.logb 2 (δ ^ (-1 - κ))) + 1 : ℕ) : ℝ) =
        (Nat.ceil (Real.logb 2 (δ ^ (-1 - κ))) : ℝ) + 1 := by
      simp
      <;> norm_cast
    rw [h11]
    <;> ring
  have h_delta_set : IsRealDeltaSet δ κ (energyToLargeMassDeltaSetC δ κ K) (S : Set ℝ) := by
    rw [←h_C_out_eq]
    exact h_union
  exact ⟨S, hS_sub_A, h_delta_set, h_mass_retention⟩

end robust_projection_main

/-! ### Application corollary

For any `η > 0`, the output constant is bounded by `δ^(-2η)` for sufficiently
small `δ`, provided `K ≤ δ^(-η)`. -/

namespace robust_projection_main

/-- General analytic lemma: for any `C > 0` and `η > 0`, there exists `δ₀ > 0`
such that for all `0 < δ ≤ δ₀`, `C * (log(1/δ))^2 ≤ δ^(-η)`. -/
lemma log_sq_bound_by_rpow {C η : ℝ} (hC_pos : 0 < C) (hη_pos : 0 < η) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      C * (Real.log (1 / δ))^2 ≤ δ ^ (-η) := by
  let A : ℝ := 16 * C / η^2
  have hA_pos : 0 < A := by positivity
  let X₀ : ℝ := A ^ (2 / η)
  have hX₀_pos : 0 < X₀ := by positivity
  let δ₀ : ℝ := min 1 X₀⁻¹
  have hδ₀_pos : 0 < δ₀ := by positivity
  refine ⟨δ₀, hδ₀_pos, fun δ hδ_pos hδ_le => ?_⟩
  have hδ_le_one : δ ≤ 1 := le_trans hδ_le (min_le_left _ _)
  have hδ_le_X₀_inv : δ ≤ X₀⁻¹ := le_trans hδ_le (min_le_right _ _)
  set x : ℝ := 1 / δ with hx_def
  have hx_pos : 0 < x := by positivity
  have hx_ge_one : 1 ≤ x := by
    have h' : 1 ≤ 1 / δ := by
      apply one_le_one_div <;> linarith
    simpa [hx_def] using h'
  have hx_ge_X₀ : x ≥ X₀ := by
    have h3 : 1 / δ ≥ 1 / X₀⁻¹ := by
      apply one_div_le_one_div_of_le hδ_pos hδ_le_X₀_inv
    have h4 : 1 / X₀⁻¹ = X₀ := by
      field_simp [hX₀_pos.ne'] <;> ring
    rw [h4] at h3
    exact h3
  have h_log_bound : Real.log x ≤ (4 / η) * x ^ (η / 4) := by
    have h2 : Real.log x ≤ x ^ (η / 4) / (η / 4) :=
      Real.log_le_rpow_div (by positivity) (by positivity)
    have h3 : x ^ (η / 4) / (η / 4) = (4 / η) * x ^ (η / 4) := by ring
    rw [h3] at h2
    exact h2
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx_ge_one
  have h_rpow2 : (x ^ (η / 4)) ^ 2 = x ^ (η / 2) := by
    have h71 : (x ^ (η / 4)) ^ 2 = (x ^ (η / 4)) * (x ^ (η / 4)) := by ring
    rw [h71]
    have h72 : (x ^ (η / 4)) * (x ^ (η / 4)) = x ^ (η / 4 + η / 4) := by
      rw [← Real.rpow_add hx_pos]
    rw [h72]
    have h73 : η / 4 + η / 4 = η / 2 := by ring
    rw [h73]
  have h4 : (Real.log x)^2 ≤ (4 / η)^2 * x ^ (η / 2) := by
    have h5 : (Real.log x)^2 ≤ ((4 / η) * x ^ (η / 4))^2 := by gcongr
    have h6 : ((4 / η) * x ^ (η / 4))^2 = (4 / η)^2 * (x ^ (η / 4))^2 := by ring
    rw [h6] at h5
    rw [h_rpow2] at h5
    exact h5
  have h9 : C * (Real.log x)^2 ≤ A * x ^ (η / 2) := by
    dsimp only [A]
    calc
      C * (Real.log x)^2 ≤ C * ((4 / η)^2 * x ^ (η / 2)) := by gcongr
      _ = (16 * C / η^2) * x ^ (η / 2) := by ring
  have h_X0_rpow : X₀ ^ (η / 2) = A := by
    dsimp only [X₀]
    have h : (A ^ (2 / η)) ^ (η / 2) = A ^ ((2 / η) * (η / 2)) :=
      (Real.rpow_mul hA_pos.le (2 / η) (η / 2)).symm
    rw [h]
    have h13 : (2 / η) * (η / 2) = 1 := by
      field_simp [hη_pos.ne'] <;> ring
    rw [h13, Real.rpow_one]
  have h10 : x ^ (η / 2) ≥ A := by
    have h11 : x ^ (η / 2) ≥ X₀ ^ (η / 2) := by gcongr <;> positivity
    rw [h_X0_rpow] at h11
    exact h11
  have h21 : A * x ^ (η / 2) ≤ x ^ η := by
    have h22 : x ^ (η / 2) * x ^ (η / 2) = x ^ η := by
      have h_sum : η / 2 + η / 2 = η := by ring
      rw [← Real.rpow_add hx_pos, h_sum]
    have h23 : A * x ^ (η / 2) ≤ x ^ (η / 2) * x ^ (η / 2) := by
      gcongr
      <;> linarith
    rw [h22] at h23
    exact h23
  have h24 : x ^ η = δ ^ (-η) := by
    have h25 : x = δ⁻¹ := by simp [hx_def] <;> ring
    rw [h25]
    have h26 : δ⁻¹ ^ η = (δ ^ η)⁻¹ := Real.inv_rpow hδ_pos.le η
    have h27 : δ ^ (-η) = (δ ^ η)⁻¹ := Real.rpow_neg hδ_pos.le η
    exact Eq.trans h26 h27.symm
  have h25 : C * (Real.log x)^2 ≤ x ^ η := le_trans h9 h21
  have h26 : C * (Real.log x)^2 ≤ δ ^ (-η) := by
    calc
      C * (Real.log x)^2 ≤ x ^ η := h25
      _ = δ ^ (-η) := h24
  simpa [hx_def] using h26

/-- Application corollary: for any `η > 0`, `κ > 0`, `κ ≤ 1`, and `K > 0`,
there exists `δ₀ > 0` such that for all sufficiently small dyadic `δ`,
if `K ≤ δ^(-η)`, then the output constant satisfies
`energyToLargeMassDeltaSetC δ κ K ≤ δ^(-2η)`. -/
lemma energy_to_large_mass_delta_set_corollary_constant_bound
    {η κ K : ℝ} (hη_pos : 0 < η) (hκ_pos : 0 < κ) (hκ_le_one : κ ≤ 1)
    (hK_pos : 0 < K) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ {δ : ℝ}, δ ∈ dyadicScales → 0 < δ → δ ≤ δ₀ →
      K ≤ δ ^ (-η) →
      energyToLargeMassDeltaSetC δ κ K ≤ δ ^ (-2 * η) := by
  let C_const : ℝ := 20480 / (Real.log 2)^2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC_pos : 0 < C_const := by positivity
  obtain ⟨δ₁, hδ₁_pos, hδ₁_bound⟩ := log_sq_bound_by_rpow hC_pos hη_pos
  let δ₀ := min (1 / 4) δ₁
  have hδ₀_pos : 0 < δ₀ := by positivity
  refine ⟨δ₀, hδ₀_pos, fun {δ} hδ_dyadic hδ_pos hδ_le hK_le => ?_⟩
  have hδ_le_quarter : δ ≤ 1 / 4 := le_trans hδ_le (min_le_left _ _)
  have hδ_le_δ₁ : δ ≤ δ₁ := le_trans hδ_le (min_le_right _ _)
  set M : ℝ := (Nat.ceil (Real.logb 2 (δ ^ (-(κ + 1)))) + 1 : ℝ) with hM_def
  have h1_logb : Real.logb 2 (δ ^ (-(κ + 1))) = (κ + 1) * Real.logb 2 (1 / δ) := by
    have h2_pos : 0 < (1 / δ) := by positivity
    have h2 : δ ^ (-(κ + 1)) = (1 / δ) ^ (κ + 1) := by
      have h21 : δ ^ (-(κ + 1)) = (δ ^ (κ + 1))⁻¹ := Real.rpow_neg hδ_pos.le (κ + 1)
      have h23 : (1 / δ) = δ⁻¹ := by ring
      have h22 : (1 / δ) ^ (κ + 1) = (δ ^ (κ + 1))⁻¹ := by
        rw [h23]
        exact Real.inv_rpow hδ_pos.le (κ + 1)
      exact Eq.trans h21 h22.symm
    rw [h2]
    rw [Real.logb_rpow_eq_mul_logb_of_pos h2_pos]
    <;> ring
  have hM_bound : M ≤ 4 * Real.logb 2 (1 / δ) := by
    rw [hM_def, h1_logb]
    have h_logb_nonneg : 0 ≤ (κ + 1) * Real.logb 2 (1 / δ) := by
      have h5 : 1 / δ ≥ 4 := by
        have h51 : δ ≤ 1 / 4 := hδ_le_quarter
        have h52 : 0 < δ := hδ_pos
        calc
          1 / δ ≥ 1 / (1 / 4) := by gcongr
          _ = 4 := by norm_num
      have h6 : Real.logb 2 (1 / δ) ≥ 2 := by
        have h7 : Real.log (1 / δ) ≥ Real.log 4 := Real.log_le_log (by norm_num) h5
        have h8 : Real.log 4 = 2 * Real.log 2 := by
          have h81 : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
          rw [h81, Real.log_pow] <;> ring
        have h9 : Real.logb 2 (1 / δ) = Real.log (1 / δ) / Real.log 2 := by rw [Real.logb]
        rw [h9]
        have h10 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        calc
          Real.log (1 / δ) / Real.log 2 ≥ Real.log 4 / Real.log 2 := by gcongr
          _ = (2 * Real.log 2) / Real.log 2 := by rw [h8]
          _ = 2 := by field_simp [h10.ne'] <;> ring
      have h9 : 0 ≤ κ + 1 := by linarith
      exact mul_nonneg h9 (by linarith)
    have h3 : (Nat.ceil ((κ + 1) * Real.logb 2 (1 / δ)) : ℝ) ≤
        (κ + 1) * Real.logb 2 (1 / δ) + 1 := by
      have h31 : (Nat.ceil ((κ + 1) * Real.logb 2 (1 / δ)) : ℝ) - 1 < (κ + 1) * Real.logb 2 (1 / δ) := by
        have h : (Nat.ceil ((κ + 1) * Real.logb 2 (1 / δ)) : ℝ) < (κ + 1) * Real.logb 2 (1 / δ) + 1 :=
          Nat.ceil_lt_add_one h_logb_nonneg
        linarith
      linarith
    have h4 : Real.logb 2 (1 / δ) ≥ 2 := by
      have h5 : 1 / δ ≥ 4 := by
        have h51 : δ ≤ 1 / 4 := hδ_le_quarter
        have h52 : 0 < δ := hδ_pos
        calc
          1 / δ ≥ 1 / (1 / 4) := by gcongr
          _ = 4 := by norm_num
      have h6 : Real.log 4 ≤ Real.log (1 / δ) :=
        Real.log_le_log (by norm_num) h5
      have h7 : Real.log 4 = 2 * Real.log 2 := by
        have h71 : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
        rw [h71, Real.log_pow] <;> ring
      have h8 : Real.logb 2 (1 / δ) = Real.log (1 / δ) / Real.log 2 := by rw [Real.logb]
      rw [h8]
      have h9 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      calc
        Real.log (1 / δ) / Real.log 2 ≥ Real.log 4 / Real.log 2 := by gcongr
        _ = (2 * Real.log 2) / Real.log 2 := by rw [h7]
        _ = 2 := by
          field_simp [h9.ne'] <;> ring
    have h5 : κ + 1 ≤ 2 := by linarith
    calc
      (Nat.ceil ((κ + 1) * Real.logb 2 (1 / δ)) : ℝ) + 1
        ≤ (κ + 1) * Real.logb 2 (1 / δ) + 2 := by linarith
      _ ≤ 2 * Real.logb 2 (1 / δ) + 2 := by gcongr
      _ ≤ 3 * Real.logb 2 (1 / δ) := by linarith
      _ ≤ 4 * Real.logb 2 (1 / δ) := by linarith
  have hlogb_eq : Real.logb 2 (1 / δ) = Real.log (1 / δ) / Real.log 2 := by
    rw [Real.logb]
  have hM_nonneg : 0 ≤ M := by positivity
  have hM_sq_bound : M^2 ≤ 16 / (Real.log 2)^2 * (Real.log (1 / δ))^2 := by
    have h6 : M ≤ 4 * (Real.log (1 / δ) / Real.log 2) := by
      rw [hlogb_eq] at hM_bound
      exact hM_bound
    have h7 : M^2 ≤ (4 * (Real.log (1 / δ) / Real.log 2))^2 := by gcongr
    have h8 : (4 * (Real.log (1 / δ) / Real.log 2))^2 =
        16 / (Real.log 2)^2 * (Real.log (1 / δ))^2 := by
      field_simp <;> ring
    rw [h8] at h7
    exact h7
  have h_two_pow : (2 : ℝ) ^ κ ≤ 2 := by
    have h10 : κ ≤ 1 := hκ_le_one
    have h11 : (2 : ℝ) ^ κ ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h10
    have h12 : (2 : ℝ) ^ (1 : ℝ) = 2 := by simp
    rw [h12] at h11
    exact h11
  have h8_eq : (Nat.ceil (Real.logb 2 (δ ^ (-(κ + 1)))) + 1 : ℝ) = M := by
    simp [hM_def]
  have h_main : energyToLargeMassDeltaSetC δ κ K ≤ δ ^ (-2 * η) := by
    have h12 : 64 * (10 * K * (2 : ℝ) ^ κ) * M^2 ≤
        1280 * (δ ^ (-η)) * M^2 := by
      calc
        64 * (10 * K * (2 : ℝ) ^ κ) * M^2
          = 640 * K * ((2 : ℝ) ^ κ) * M^2 := by ring
        _ ≤ 640 * (δ ^ (-η)) * ((2 : ℝ) ^ κ) * M^2 := by
          gcongr <;> exact hK_le
        _ ≤ 640 * (δ ^ (-η)) * (2 : ℝ) * M^2 := by
          gcongr <;> exact h_two_pow
        _ = 1280 * (δ ^ (-η)) * M^2 := by ring
    have h13 : 1280 * (δ ^ (-η)) * M^2 ≤
        1280 * (δ ^ (-η)) * (16 / (Real.log 2)^2 * (Real.log (1 / δ))^2) := by
      gcongr <;> exact hM_sq_bound <;> positivity
    have h14 : 1280 * (δ ^ (-η)) * (16 / (Real.log 2)^2 * (Real.log (1 / δ))^2) =
        (δ ^ (-η)) * (C_const * (Real.log (1 / δ))^2) := by
      dsimp only [C_const] <;> ring
    have h15 : C_const * (Real.log (1 / δ))^2 ≤ δ ^ (-η) :=
      hδ₁_bound δ hδ_pos hδ_le_δ₁
    have h16 : (δ ^ (-η)) * (C_const * (Real.log (1 / δ))^2) ≤
        (δ ^ (-η)) * (δ ^ (-η)) := by
      gcongr <;> positivity
    have h17 : (δ ^ (-η)) * (δ ^ (-η)) = δ ^ (-2 * η) := by
      have h_sum : (-η) + (-η) = -2 * η := by ring
      have h_rpow : (δ ^ (-η)) * (δ ^ (-η)) = δ ^ ((-η) + (-η)) := by
        exact (Real.rpow_add hδ_pos (-η) (-η)).symm
      rw [h_rpow, h_sum]
    have h18 : 64 * (10 * K * (2 : ℝ) ^ κ) * M^2 ≤ δ ^ (-2 * η) :=
      calc
        64 * (10 * K * (2 : ℝ) ^ κ) * M^2
          ≤ 1280 * (δ ^ (-η)) * M^2 := h12
        _ ≤ 1280 * (δ ^ (-η)) * (16 / (Real.log 2)^2 * (Real.log (1 / δ))^2) := h13
        _ = (δ ^ (-η)) * (C_const * (Real.log (1 / δ))^2) := h14
        _ ≤ (δ ^ (-η)) * (δ ^ (-η)) := h16
        _ = δ ^ (-2 * η) := h17
    have hC_def : energyToLargeMassDeltaSetC δ κ K = 64 * (10 * K * (2 : ℝ) ^ κ) * M^2 := by
      simp [energyToLargeMassDeltaSetC, hM_def]
      <;> ring
    rw [hC_def]
    exact h18
  exact h_main

end robust_projection_main
