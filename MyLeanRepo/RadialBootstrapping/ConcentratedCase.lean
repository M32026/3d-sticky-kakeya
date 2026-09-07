module

/-
  ConcentratedCase.lean

  Steps 4-5 of the concentrated case in the OSW bootstrapping argument.

  Step 4: Fix ξ by pigeonhole over dyadic annulus scales.
  Step 5: Fix y by Fubini's theorem.

  Whiteprint node: concentrated-case
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.PigeonholeHelpers

@[expose] public section


open MeasureTheory Metric Set Finset

noncomputable section

namespace RadialBootstrapping

/-! ============================================================================
    Step 4: Fix ξ by pigeonhole
   ============================================================================ -/

/-- Fix a single annulus scale ξ₀ by pigeonhole.

Given `H'` partitioned into finitely many pieces `H''_ξ ξ₀` indexed by
`scales : Finset ℝ`, where `|scales| ≤ (1/6)·r^(-η)`, and
`(μ×ν)(H') ≥ r^(7η)`, there exists `ξ₀ ∈ scales` such that
`(μ×ν)(H''_ξ ξ₀) ≥ r^(8η)`.
-/
lemma fix_xi
    {μ ν : Measure Point} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (r η κ : ℝ)
    (hr : 0 < r)
    (heta : 0 < η)
    (scales : Finset ℝ)
    (h_scales_bounds : ∀ ξ ∈ scales, r ≤ ξ ∧ ξ ≤ Real.rpow r κ)
    (h_scales_card : (scales.card : ℝ) ≤ (1 / 6 : ℝ) * Real.rpow r (-η))
    (H' : Set (Point × Point))
    (hH'_meas : MeasurableSet H')
    (H''_ξ : ℝ → Set (Point × Point))
    (h_partition : H' = ⋃ ξ₀ ∈ scales, H''_ξ ξ₀)
    (h_disj : ∀ ξ₁ ∈ scales, ∀ ξ₂ ∈ scales, ξ₁ ≠ ξ₂ →
      Disjoint (H''_ξ ξ₁) (H''_ξ ξ₂))
    (h_meas : ∀ ξ₀ ∈ scales, MeasurableSet (H''_ξ ξ₀))
    (hH'_ge : (μ.prod ν) H' ≥ ENNReal.ofReal (Real.rpow r (7 * η))) :
    ∃ (ξ₀ : ℝ), ξ₀ ∈ scales ∧ r ≤ ξ₀ ∧ ξ₀ ≤ Real.rpow r κ ∧
      (μ.prod ν) (H''_ξ ξ₀) ≥ ENNReal.ofReal (Real.rpow r (8 * η)) := by
  have h_scales_nonempty : scales.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at h_partition
    simp at h_partition
    rw [h_partition] at hH'_ge
    have h_pos : 0 < Real.rpow r (7 * η) := Real.rpow_pos_of_pos hr _
    have h_zero : (μ.prod ν) (∅ : Set (Point × Point)) = 0 := by simp
    rw [h_zero] at hH'_ge
    have h_false : ¬ (0 : ENNReal) ≥ ENNReal.ofReal (Real.rpow r (7 * η)) := by
      simpa [h_pos.ne'] using not_le.mpr (ENNReal.ofReal_pos.mpr h_pos)
    exact h_false hH'_ge
  have h_sum : (μ.prod ν) H' = ∑ ξ₀ ∈ scales, (μ.prod ν) (H''_ξ ξ₀) := by
    rw [h_partition]
    exact measure_biUnion_finset h_disj h_meas
  have h_sum_ge : ∑ ξ₀ ∈ scales, (μ.prod ν) (H''_ξ ξ₀) ≥
      ENNReal.ofReal (Real.rpow r (7 * η)) := by
    rw [← h_sum]
    exact hH'_ge
  set c7 : ENNReal := ENNReal.ofReal (Real.rpow r (7 * η)) with hc7_def
  have hc7_ne_top : c7 ≠ ⊤ := ENNReal.ofReal_ne_top
  rcases finset_pigeonhole_ennreal (fun ξ₀ => (μ.prod ν) (H''_ξ ξ₀))
      hc7_ne_top h_scales_nonempty h_sum_ge with ⟨ξ₀, hξ₀_in, h_ge⟩
  have h_bounds : r ≤ ξ₀ ∧ ξ₀ ≤ Real.rpow r κ := h_scales_bounds ξ₀ hξ₀_in
  have h_card_bound : (scales.card : ENNReal) ≤
      ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (-η)) := by
    have h1 : (scales.card : ℝ) ≤ (1 / 6 : ℝ) * Real.rpow r (-η) := h_scales_card
    have h2 : (scales.card : ENNReal) = ENNReal.ofReal (scales.card : ℝ) := by simp
    rw [h2]
    exact ENNReal.ofReal_le_ofReal h1
  have h_posB : 0 < (1 / 6 : ℝ) * Real.rpow r (-η) := by
    have h : 0 < Real.rpow r (-η) := Real.rpow_pos_of_pos hr _
    positivity
  have h_div_goal : c7 / (scales.card : ENNReal) ≥
      ENNReal.ofReal (Real.rpow r (8 * η)) := by
    have h_inv : (ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (-η)))⁻¹ ≤
        (scales.card : ENNReal)⁻¹ := ENNReal.inv_le_inv.mpr h_card_bound
    have h_mult : c7 * (ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (-η)))⁻¹ ≤
        c7 * (scales.card : ENNReal)⁻¹ := by gcongr
    have h2 : c7 / (scales.card : ENNReal) ≥
        c7 / ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (-η)) := by
      simpa [div_eq_mul_inv] using h_mult
    have h3 : c7 / ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (-η)) =
        ENNReal.ofReal (6 * Real.rpow r (8 * η)) := by
      simp only [hc7_def]
      have h4 : ENNReal.ofReal (Real.rpow r (7 * η) / ((1 / 6 : ℝ) * Real.rpow r (-η))) =
          ENNReal.ofReal (Real.rpow r (7 * η)) /
          ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (-η)) :=
        ENNReal.ofReal_div_of_pos (x := Real.rpow r (7 * η)) h_posB
      rw [← h4]
      have h_pos_rpow : ∀ (x : ℝ), 0 < Real.rpow r x := fun _ => Real.rpow_pos_of_pos hr _
      have h_sum_rpow : Real.rpow r (7 * η) * Real.rpow r η = Real.rpow r (8 * η) := by
        calc
          Real.rpow r (7 * η) * Real.rpow r η
            = Real.rpow r ((7 * η) + η) := (Real.rpow_add hr (7 * η) η).symm
          _ = Real.rpow r (8 * η) := by ring_nf
      have h9 : Real.rpow r (-η) * Real.rpow r η = 1 := by
        calc
          Real.rpow r (-η) * Real.rpow r η
            = Real.rpow r ((-η) + η) := (Real.rpow_add hr (-η) η).symm
          _ = Real.rpow r 0 := by ring_nf
          _ = 1 := by simp
      have h_inv_rpow : (Real.rpow r (-η))⁻¹ = Real.rpow r η :=
        inv_eq_of_mul_eq_one_right h9
      have h5 : Real.rpow r (7 * η) / ((1 / 6 : ℝ) * Real.rpow r (-η)) =
          6 * Real.rpow r (8 * η) := by
        calc
          Real.rpow r (7 * η) / ((1 / 6 : ℝ) * Real.rpow r (-η))
            = 6 * (Real.rpow r (7 * η) * (Real.rpow r (-η))⁻¹) := by
              field_simp [(h_pos_rpow (-η)).ne'] <;> ring
          _ = 6 * (Real.rpow r (7 * η) * Real.rpow r η) := by rw [h_inv_rpow]
          _ = 6 * Real.rpow r (8 * η) := by rw [h_sum_rpow]
      rw [h5] <;> rfl
    rw [h3] at h2
    have h6 : (6 * Real.rpow r (8 * η)) ≥ Real.rpow r (8 * η) := by
      have h7 : 0 < Real.rpow r (8 * η) := Real.rpow_pos_of_pos hr _
      linarith
    have h7 : ENNReal.ofReal (6 * Real.rpow r (8 * η)) ≥
        ENNReal.ofReal (Real.rpow r (8 * η)) := ENNReal.ofReal_le_ofReal h6
    exact le_trans h7 h2
  exact ⟨ξ₀, hξ₀_in, h_bounds.1, h_bounds.2, le_trans h_div_goal h_ge⟩

/-! ============================================================================
    Step 5: Fix y by Fubini
   ============================================================================ -/

/-- Fix a point `y` such that the vertical fiber has measure at least `c`.

Uses Fubini's theorem. If every vertical fiber had measure `< c`,
then the product measure would be `< c` (since ν is a probability measure),
contradicting the hypothesis.
-/
lemma fix_y
    {μ ν : Measure Point} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H'' : Set (Point × Point))
    (hH''_meas : MeasurableSet H'')
    (c : ENNReal)
    (hc_ne_top : c ≠ ⊤)
    (h : (μ.prod ν) H'' ≥ c) :
    ∃ (y : Point), μ {x : Point | (x, y) ∈ H''} ≥ c := by
  let f : Point → ENNReal := fun y => μ {x : Point | (x, y) ∈ H''}
  have h_f_meas : Measurable f := by exact measurable_measure_prodMk_right hH''_meas
  have h_fubini : (μ.prod ν) H'' = ∫⁻ y, f y ∂ν := by exact Measure.prod_apply_symm hH''_meas
  rw [h_fubini] at h
  by_contra h'
  push Not at h'
  have h1 : ∀ y, f y < c := h'
  -- c = 0 case: f y < 0 is impossible in ENNReal
  by_cases h_c0 : c = 0
  · rw [h_c0] at h1
    have h_nonempty : Nonempty Point := by
      by_contra h_empty
      have h_univ_empty : (Set.univ : Set Point) = ∅ := by
        simpa [Set.univ_eq_empty_iff] using h_empty
      have h_μ_univ : μ Set.univ = 0 := by rw [h_univ_empty] <;> simp
      have h_prob : μ Set.univ = 1 := by simp
      rw [h_μ_univ] at h_prob <;> norm_num at h_prob
    let y : Point := h_nonempty.some
    have h_cont : f y < 0 := h1 y
    simp at h_cont
  -- Now c ≠ 0 and c ≠ ⊤, so c_real > 0
  have h_c_pos_real : 0 < c.toReal := ENNReal.toReal_pos h_c0 hc_ne_top
  have h_f_bounded : ∀ y, f y ≤ 1 := fun _ => prob_le_one
  have h_f_ne_top : ∀ y, f y ≠ ⊤ := by
    intro y
    have h_le : f y ≤ 1 := h_f_bounded y
    intro h_eq
    rw [h_eq] at h_le
    simp at h_le
  have h_f_lt_top : ∀ y, f y < ⊤ := fun y =>
    lt_top_iff_ne_top.mpr (h_f_ne_top y)
  let g : Point → ℝ := fun y => (f y).toReal
  let c_real : ℝ := c.toReal
  have h_g_meas : Measurable g := h_f_meas.ennreal_toReal
  have h_g_nonneg : ∀ y, 0 ≤ g y := fun _ => by positivity
  have h_g_le_one : ∀ y, g y ≤ 1 := by
    intro y
    have h7 : f y ≤ 1 := h_f_bounded y
    have h8 : (1 : ENNReal) ≠ ⊤ := by simp
    have h9 : (f y).toReal ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono h8 h7
    simpa using h9
  have h_g_bounded : ∀ y, ‖g y‖ ≤ 1 := by
    intro y
    have h5 : 0 ≤ g y := h_g_nonneg y
    have h6 : g y ≤ 1 := h_g_le_one y
    have h7 : ‖g y‖ = g y := by
      rw [Real.norm_eq_abs, abs_of_nonneg h5]
    rw [h7]
    exact h6
  have h_ae : ∀ᵐ (y : Point) ∂ν, ‖g y‖ ≤ 1 := .of_forall h_g_bounded
  have h_g_integrable : Integrable g ν :=
    Integrable.of_bound h_g_meas.aestronglyMeasurable 1 h_ae
  have h_lintegral_le_one : (∫⁻ y, f y ∂ν) ≤ 1 := by
    have h : (∫⁻ y, f y ∂ν) ≤ ∫⁻ (_ : Point), (1 : ENNReal) ∂ν := lintegral_mono h_f_bounded
    have h2 : (∫⁻ (_ : Point), (1 : ENNReal) ∂ν) = 1 := by simp
    rw [h2] at h
    exact h
  have h_lintegral_ne_top : (∫⁻ y, f y ∂ν) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) h_lintegral_le_one
  have h_toReal : ∫ y, g y ∂ν = (∫⁻ y, f y ∂ν).toReal :=
    MeasureTheory.integral_toReal h_f_meas.aemeasurable
      (by filter_upwards with y using h_f_lt_top y)
  have h_ge : c_real ≤ ∫ y, g y ∂ν := by
    rw [h_toReal]
    exact ENNReal.toReal_mono h_lintegral_ne_top h
  have h_g_lt : ∀ y, g y < c_real := by
    intro y
    have hfin : f y ≠ ⊤ := h_f_ne_top y
    exact ENNReal.toReal_lt_toReal hfin hc_ne_top |>.mpr (h1 y)
  -- Countable cover: Set.univ ⊆ ⋃ n, {y | g y ≤ c_real - 1/(n+1)}
  have h_cov : Set.univ ⊆ ⋃ n : ℕ, {y | g y ≤ c_real - 1 / (n + 1 : ℝ)} := by
    intro y _
    have h_lt : g y < c_real := h_g_lt y
    have h_pos : 0 < c_real - g y := by linarith
    have h_exists : ∃ n : ℕ, 1 / (n + 1 : ℝ) < c_real - g y :=
      exists_nat_one_div_lt h_pos
    rcases h_exists with ⟨n, hn⟩
    have h_leq : g y ≤ c_real - 1 / (n + 1 : ℝ) := by linarith
    exact Set.mem_iUnion.mpr ⟨n, h_leq⟩
  have h_pos_meas : ∃ n : ℕ, 0 < ν {y | g y ≤ c_real - 1 / (n + 1 : ℝ)} := by
    by_contra h_all
    push Not at h_all
    have h_univ_le : ν Set.univ ≤ ∑' n : ℕ, ν {y | g y ≤ c_real - 1 / (n + 1 : ℝ)} :=
      calc ν Set.univ
        ≤ ν (⋃ n : ℕ, {y | g y ≤ c_real - 1 / (n + 1 : ℝ)}) := measure_mono h_cov
      _ ≤ ∑' n : ℕ, ν {y | g y ≤ c_real - 1 / (n + 1 : ℝ)} := measure_iUnion_le _
    have h_all_zero : ∀ n : ℕ, ν {y | g y ≤ c_real - 1 / (n + 1 : ℝ)} = 0 := by
      intro n
      have h9 : ν {y | g y ≤ c_real - 1 / (n + 1 : ℝ)} ≤ 0 := h_all n
      exact le_zero_iff.mp h9
    have h_sum_zero : ∑' n : ℕ, ν {y | g y ≤ c_real - 1 / (n + 1 : ℝ)} = 0 := by
      rw [tsum_congr h_all_zero]
      <;> simp
    have h_univ_zero : ν Set.univ ≤ 0 := by
      rw [h_sum_zero] at h_univ_le
      exact h_univ_le
    have h_univ_one : ν Set.univ = 1 := by simp
    rw [h_univ_one] at h_univ_zero
    <;> norm_num at h_univ_zero
  rcases h_pos_meas with ⟨n, hn⟩
  let A := {y : Point | g y ≤ c_real - 1 / (n + 1 : ℝ)}
  have hA_meas : MeasurableSet A := by
    have h_preimage : A = g ⁻¹' Set.Iic (c_real - 1 / (n + 1 : ℝ)) := by
      ext y
      simp [A, Set.mem_preimage, Set.mem_Iic]
      <;> rfl
    rw [h_preimage]
    exact h_g_meas measurableSet_Iic
  have h_split : ∫ y, g y ∂ν = ∫ y in A, g y ∂ν + ∫ y in Aᶜ, g y ∂ν :=
    (MeasureTheory.integral_add_compl hA_meas h_g_integrable).symm
  have h_neg_integrable : Integrable (-g) ν := h_g_integrable.neg
  -- Upper bound on A
  have h_bd_A : ∫ y in A, g y ∂ν ≤ (c_real - 1 / (n + 1 : ℝ)) * (ν A).toReal := by
    have h1 : ∀ y ∈ A, -(c_real - 1 / (n + 1 : ℝ)) ≤ -g y := by
      intro y hy
      simp only [A, Set.mem_setOf_eq] at hy
      linarith
    have h2 : -(c_real - 1 / (n + 1 : ℝ)) * (ν A).toReal ≤ ∫ y in A, -g y ∂ν :=
      MeasureTheory.setIntegral_ge_of_const_le_real hA_meas (measure_ne_top ν A) h1
        h_neg_integrable.integrableOn
    have h3 : ∫ y in A, -g y ∂ν = -∫ y in A, g y ∂ν := by
      simp [integral_neg]
    linarith
  -- Upper bound on Aᶜ
  have h_bd_Ac : ∫ y in Aᶜ, g y ∂ν ≤ c_real * (ν Aᶜ).toReal := by
    have h1 : ∀ y ∈ Aᶜ, -c_real ≤ -g y := by
      intro y _
      have h2 : g y < c_real := h_g_lt y
      linarith
    have h2 : -c_real * (ν Aᶜ).toReal ≤ ∫ y in Aᶜ, -g y ∂ν :=
      MeasureTheory.setIntegral_ge_of_const_le_real hA_meas.compl (measure_ne_top ν Aᶜ) h1
        h_neg_integrable.integrableOn
    have h3 : ∫ y in Aᶜ, -g y ∂ν = -∫ y in Aᶜ, g y ∂ν := by
      simp [integral_neg]
    linarith
  have h4 : (ν A).toReal + (ν Aᶜ).toReal = 1 := by
    have h_disj : Disjoint A Aᶜ := disjoint_compl_right
    have h5 : ν (A ∪ Aᶜ) = ν A + ν Aᶜ :=
      MeasureTheory.measure_union' (s₁ := A) (s₂ := Aᶜ) h_disj hA_meas
    have h_union : A ∪ Aᶜ = Set.univ := by simp
    have h6 : ν A + ν Aᶜ = ν Set.univ := by
      rw [← h5, h_union]
    have h7 : (ν A + ν Aᶜ).toReal = (ν A).toReal + (ν Aᶜ).toReal :=
      ENNReal.toReal_add (measure_ne_top ν A) (measure_ne_top ν Aᶜ)
    have h8 : (ν Set.univ).toReal = 1 := by simp
    have h9 : (ν A + ν Aᶜ).toReal = (ν Set.univ).toReal := by rw [h6]
    rw [← h7, h9, h8]
  have h_strict : ∫ y, g y ∂ν < c_real := by
    calc
      ∫ y, g y ∂ν
        = ∫ y in A, g y ∂ν + ∫ y in Aᶜ, g y ∂ν := h_split
      _ ≤ (c_real - 1 / (n + 1 : ℝ)) * (ν A).toReal + c_real * (ν Aᶜ).toReal := by gcongr
      _ = c_real * ((ν A).toReal + (ν Aᶜ).toReal) - (1 / (n + 1 : ℝ)) * (ν A).toReal := by ring
      _ = c_real - (1 / (n + 1 : ℝ)) * (ν A).toReal := by rw [h4] <;> ring
      _ < c_real := by
        have h5 : 0 < (ν A).toReal := ENNReal.toReal_pos_iff.mpr
          ⟨hn, lt_top_iff_ne_top.mpr (measure_ne_top ν A)⟩
        have h6 : 0 < (1 / (n + 1 : ℝ)) * (ν A).toReal := by positivity
        linarith
  have h_cont : c_real < c_real := calc
    c_real ≤ ∫ y, g y ∂ν := h_ge
    _ < c_real := h_strict
  exact lt_irrefl c_real h_cont

end RadialBootstrapping

end
