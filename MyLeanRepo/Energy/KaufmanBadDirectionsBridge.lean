module

/-
# Kaufman Bad Directions Bridge

Bridges `average_projection_energy_bound` to the `kaufman_bad_directions` interface
used in the Phase 2 pipeline skeleton.

## Main results
- `kaufmanAveragingConstant`: the Kaufman averaging constant
- `kaufman_averaging_bound`: direct application of `average_projection_energy_bound`
- `kaufman_bad_directions_bridge`: specialized bad-directions lemma matching
  the skeleton's `kaufman_bad_directions` interface

## Whiteprint node
`phase2_bourgain_pipeline/kaufman_bad_directions`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.Energy.AverageProjectionEnergy
public import MyLeanRepo.Energy.AverageProjectionEnergyGen
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Classical

namespace robust_projection_main

/-- Kaufman averaging constant from `average_projection_energy_bound`. -/
def kaufmanAveragingConstant (C_ν τ κ : ℝ) : ℝ :=
  1 + (C_ν + 1) * (6 * Real.sqrt 2) ^ (2 * κ) * (1 + (2 * κ) / (τ - 2 * κ))

/--
Riesz energy is strictly positive for any probability measure, because the
integrand is everywhere positive and the measure has total mass 1.
-/
lemma rieszEnergy_pos {α δ : ℝ} (hδ : 0 < δ) (_ : 0 < α)
    {X : Type*} [MeasurableSpace X] [MetricSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X]
    {ν : Measure X} [IsProbabilityMeasure ν] :
    0 < rieszEnergy α hδ ν := by
  let k : X → X → ENNReal := fun x y =>
    ENNReal.ofReal ((max (dist x y) δ) ^ (-α))
  have h_k_pos : ∀ (x y : X), 0 < k x y := by
    intro x y
    dsimp only [k]
    have h1 : 0 < max (dist x y) δ := by positivity
    have h2 : 0 < (max (dist x y) δ) ^ (-α) := Real.rpow_pos_of_pos h1 _
    exact ENNReal.ofReal_pos.mpr h2
  have hk_meas : Measurable (fun p : X × X =>
      ENNReal.ofReal ((max (dist p.1 p.2) δ) ^ (-α))) := by
    have h1 : Measurable (fun p : X × X => dist p.1 p.2) := measurable_dist
    have h2 : Measurable (fun p : X × X => max (dist p.1 p.2) δ) :=
      h1.max measurable_const
    have h3 : Measurable (fun p : X × X => (max (dist p.1 p.2) δ) ^ (-α)) :=
      h2.pow measurable_const
    exact h3.ennreal_ofReal
  have hk_x_meas : ∀ (x : X), Measurable (fun y : X => k x y) := by
    intro x
    have h4 : (fun y : X => k x y) = (fun p : X × X =>
        ENNReal.ofReal ((max (dist p.1 p.2) δ) ^ (-α))) ∘ (fun y : X => (x, y)) := by
      funext y; rfl
    rw [h4]
    have h_map : Measurable (fun y : X => (x, y)) := by
      exact measurable_prodMk_left
    exact hk_meas.comp h_map
  have h_inner_meas : Measurable (fun x : X => ∫⁻ (y : X), k x y ∂ν) :=
    hk_meas.lintegral_prod_right'
  have h_inner_pos : ∀ (x : X), 0 < ∫⁻ (y : X), k x y ∂ν := by
    intro x
    have h1 : Function.support (k x) = Set.univ := by
      ext y
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact ne_of_gt (h_k_pos x y)
    have h : 0 < ∫⁻ (y : X), k x y ∂ν := by
      rw [MeasureTheory.lintegral_pos_iff_support (hk_x_meas x), h1]
      <;> simp [measure_univ]
    exact h
  have h_outer_support : Function.support (fun x : X => ∫⁻ (y : X), k x y ∂ν) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (h_inner_pos x)
  have h_outer_pos : 0 < ∫⁻ (x : X), (∫⁻ (y : X), k x y ∂ν) ∂ν := by
    rw [MeasureTheory.lintegral_pos_iff_support h_inner_meas, h_outer_support]
    <;> simp [measure_univ]
  have h_main : (∫⁻ (x : X), (∫⁻ (y : X), k x y ∂ν) ∂ν) = rieszEnergy α hδ ν := by
    rfl
  rw [← h_main]
  exact h_outer_pos

/--
Direct bridge: apply `average_projection_energy_bound` to bound the average
directional Riesz energy over a Frostman direction measure by the Kaufman
constant times the planar Riesz energy.
-/
lemma kaufman_averaging_bound
    {δ τ κ C_ν : ℝ}
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {ν : Measure (EuclideanSpace ℝ (Fin 2))} [IsFiniteMeasure ν]
    (hτ_pos : 0 < τ) (hκ_pos : 0 < κ) (hτ_gt_2κ : τ > 2 * κ)
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1) (hCν_pos : 0 < C_ν)
    (hμ_frost : IsDirectionFrostman δ τ C_ν μ)
    (hμ_support_bdd : μ.support ⊆ Set.Icc 0 1)
    (hν_support_bdd : ν.support ⊆ {p | ∀ i, p i ∈ Set.Icc (-3 : ℝ) 3}) :
    ∫⁻ (y : ℝ), rieszEnergy (2 * κ) (hδ := hδ_pos)
        (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 0 * y + p 1) ν) ∂μ ≤
      ENNReal.ofReal (kaufmanAveragingConstant C_ν τ κ) *
        rieszEnergy (2 * κ) (hδ := hδ_pos) ν := by
  have h_main := average_projection_energy_bound
    hτ_pos hκ_pos hτ_gt_2κ hδ_pos hδ_le_one hCν_pos
    hμ_frost hμ_support_bdd hν_support_bdd
  simpa [kaufmanAveragingConstant] using h_main

/--
Specialized Kaufman bad-directions lemma matching the skeleton's
`kaufman_bad_directions` interface.

Given:
- A Frostman direction measure ν on Ybar
- A uniform probability measure μE on a finite point set E in the unit box
- A planar Riesz energy bound `rieszEnergy(μE) ≤ C_plan`
- An absorption condition `C_Kaufman * C_plan * δ^(3ε) ≤ δ^(2ε)`

Outputs a set Θ_bad ⊆ Ybar with:
- ν(Θ_bad) ≤ δ^(2ε)
- Every y ∈ Θ_bad has directional energy > δ^(-3ε)
-/
lemma kaufman_bad_directions_bridge
    {δ ε κ0 τ C_ν C_Kaufman C_plan : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (_ : 0 < ε) (hkappa_pos : 0 < κ0)
    (hτ_gt_2κ0 : 2 * κ0 < τ)
    (hC_ν_pos : 0 < C_ν)
    (_ : 0 < C_Kaufman)
    (hC_Kaufman_eq : C_Kaufman = 1 + (C_ν + 1) * (6 * Real.sqrt 2) ^ (2 * κ0) *
        (1 + 2 * κ0 / (τ - 2 * κ0)))
    {E : Finset (EuclideanSpace ℝ (Fin 2))}
    {μE : Measure (EuclideanSpace ℝ (Fin 2))} [IsProbabilityMeasure μE]
    (hμE_supp : μE.support = (E : Set _))
    (hμE_support_bdd : μE.support ⊆ {p : EuclideanSpace ℝ (Fin 2) | ∀ i, p i ∈ Set.Icc (-3 : ℝ) 3})
    {Ybar : Set ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hYbar_fin : Ybar.Finite)
    (_ : ν.support = Ybar)
    (hν_frost : IsDirectionFrostman δ τ C_ν ν)
    (h_energy : rieszEnergy (2 * κ0) hδ_pos μE ≤ ENNReal.ofReal C_plan)
    (h_kaufman_absorb : C_Kaufman * C_plan * δ ^ (3 * ε) ≤ δ ^ (2 * ε)) :
    ∃ (Θ_bad : Set ℝ),
      Θ_bad = {y ∈ Ybar | rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 0 * y + p 1) μE) >
        ENNReal.ofReal (δ ^ (-3 * ε))} ∧
      ν Θ_bad ≤ ENNReal.ofReal (δ ^ (2 * ε)) := by
  let f : ℝ → ENNReal := fun y =>
    rieszEnergy (2 * κ0) hδ_pos
      (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 0 * y + p 1) μE)
  let threshold : ENNReal := ENNReal.ofReal (δ ^ (-3 * ε))
  let C_avg : ℝ := kaufmanAveragingConstant C_ν τ κ0

  have hδ_le_one : δ ≤ 1 := by linarith
  have hτ_pos : 0 < τ := by linarith
  have hτ_gt_2κ0' : τ > 2 * κ0 := by linarith
  have hC_avg_pos : 0 < C_avg := by
    dsimp only [C_avg, kaufmanAveragingConstant] <;> positivity
  have hC_Kaufman_eq_avg : C_Kaufman = C_avg := by
    rw [hC_Kaufman_eq] <;> rfl

  -- Support bounds for Kaufman averaging
  have hν_support_bdd : ν.support ⊆ Set.Icc 0 1 := hν_frost.2.1
  have hμE_support_bdd' : μE.support ⊆ {p : EuclideanSpace ℝ (Fin 2) | ∀ i, p i ∈ Set.Icc (-3 : ℝ) 3} := hμE_support_bdd

  -- Step 1: Kaufman averaging bound
  have h_avg : ∫⁻ (y : ℝ), f y ∂ν ≤
      ENNReal.ofReal C_avg * rieszEnergy (2 * κ0) hδ_pos μE :=
    kaufman_averaging_bound
      hτ_pos hkappa_pos hτ_gt_2κ0' hδ_pos hδ_le_one hC_ν_pos
      hν_frost hν_support_bdd hμE_support_bdd

  -- C_plan must be non-negative (energy is positive)
  have hC_plan_nonneg : 0 ≤ C_plan := by
    by_contra h
    have h' : C_plan < 0 := by exact lt_of_not_ge h
    have h'' : ENNReal.ofReal C_plan = 0 := by
      rw [ENNReal.ofReal_eq_zero.mpr] <;> linarith
    rw [h''] at h_energy
    have h_energy_pos : 0 < rieszEnergy (2 * κ0) hδ_pos μE :=
      rieszEnergy_pos hδ_pos (by linarith)
    exact False.elim (not_le.mpr h_energy_pos h_energy)

  -- Step 2: Combine with planar energy bound
  have h_avg2 : ∫⁻ (y : ℝ), f y ∂ν ≤ ENNReal.ofReal (C_avg * C_plan) := by
    calc ∫⁻ (y : ℝ), f y ∂ν
        ≤ ENNReal.ofReal C_avg * rieszEnergy (2 * κ0) hδ_pos μE := h_avg
      _ ≤ ENNReal.ofReal C_avg * ENNReal.ofReal C_plan := by
          exact mul_le_mul_of_nonneg_left h_energy (by positivity)
      _ = ENNReal.ofReal (C_avg * C_plan) := by
          exact (ENNReal.ofReal_mul hC_avg_pos.le).symm

  -- Step 3: Define bad set (subset of finite Ybar, hence measurable)
  let Θ_bad : Set ℝ := {y | y ∈ Ybar ∧ f y > threshold}
  have h9 : Θ_bad ⊆ Ybar := by intro y hy; exact hy.1
  have h10 : ∀ y ∈ Θ_bad, f y > threshold := by intro y hy; exact hy.2
  have hΘ_bad_meas : MeasurableSet Θ_bad :=
    (hYbar_fin.subset h9).measurableSet

  have h_threshold_pos : 0 < δ ^ (-3 * ε) := by positivity
  have h_threshold_ne_zero : threshold ≠ 0 := by
    have h : threshold = ENNReal.ofReal (δ ^ (-3 * ε)) := rfl
    rw [h]
    have hpos : 0 < δ ^ (-3 * ε) := by positivity
    exact (ENNReal.ofReal_pos.mpr hpos).ne'
  have h_threshold_ne_top : threshold ≠ ⊤ := by
    simp [threshold] <;> exact ENNReal.coe_ne_top

  -- Markov inequality: threshold * ν Θ_bad ≤ ∫ f dν
  let g : ℝ → ENNReal := Set.indicator Θ_bad (fun _ => threshold)
  have h1 : ∀ y, g y ≤ f y := by
    intro y
    by_cases hy : y ∈ Θ_bad
    · have h2 : f y > threshold := hy.2
      have h3 : g y = threshold := by
        unfold g; simp [hy, Set.indicator]
      rw [h3]; exact h2.le
    · have h3 : g y = 0 := by
        unfold g; simp [hy, Set.indicator]
      rw [h3]; exact bot_le
  have h2 : ∫⁻ (y : ℝ), g y ∂ν ≤ ∫⁻ (y : ℝ), f y ∂ν := lintegral_mono h1
  have h3 : ∫⁻ (y : ℝ), g y ∂ν = threshold * ν Θ_bad := by
    unfold g
    rw [lintegral_indicator hΘ_bad_meas (fun (_ : ℝ) => threshold)]
    have h_eq1 : ∫⁻ (y : ℝ), (fun (_ : ℝ) => threshold) y ∂(ν.restrict Θ_bad) =
        ∫⁻ (_ : ℝ), threshold ∂(ν.restrict Θ_bad) := by
      congr with y <;> rfl
    rw [h_eq1, lintegral_const] <;> simp <;> rfl
  have h_markov : threshold * ν Θ_bad ≤ ∫⁻ (y : ℝ), f y ∂ν := by
    rw [← h3]; exact h2

  -- Step 4: threshold * target = ofReal(C_avg * C_plan), cancel threshold
  have h_target : threshold * ENNReal.ofReal (C_avg * C_plan * δ ^ (3 * ε)) =
      ENNReal.ofReal (C_avg * C_plan) := by
    have h4 : threshold = ENNReal.ofReal (δ ^ (-3 * ε)) := rfl
    rw [h4]
    have h_pos1 : 0 ≤ δ ^ (-3 * ε) := by positivity
    have h5 : ENNReal.ofReal (δ ^ (-3 * ε)) * ENNReal.ofReal (C_avg * C_plan * δ ^ (3 * ε)) =
        ENNReal.ofReal (δ ^ (-3 * ε) * (C_avg * C_plan * δ ^ (3 * ε))) := by
      rw [ENNReal.ofReal_mul h_pos1] <;> rfl
    rw [h5]
    have h61 : δ ^ (-3 * ε) * δ ^ (3 * ε) = 1 := by
      rw [← Real.rpow_add hδ_pos] <;> ring_nf <;> rw [Real.rpow_zero] <;> ring
    have h6 : δ ^ (-3 * ε) * (C_avg * C_plan * δ ^ (3 * ε)) = C_avg * C_plan := by
      have h_reorder : δ ^ (-3 * ε) * (C_avg * C_plan * δ ^ (3 * ε)) =
          (C_avg * C_plan) * (δ ^ (-3 * ε) * δ ^ (3 * ε)) := by ring
      rw [h_reorder, h61] <;> ring
    rw [h6] <;> rfl

  have h6 : threshold * ν Θ_bad ≤ threshold * ENNReal.ofReal (C_avg * C_plan * δ ^ (3 * ε)) := by
    calc threshold * ν Θ_bad
        ≤ ∫⁻ (y : ℝ), f y ∂ν := h_markov
      _ ≤ ENNReal.ofReal (C_avg * C_plan) := h_avg2
      _ = threshold * ENNReal.ofReal (C_avg * C_plan * δ ^ (3 * ε)) := h_target.symm

  have h7 : ν Θ_bad ≤ ENNReal.ofReal (C_avg * C_plan * δ ^ (3 * ε)) := by
    exact (ENNReal.mul_le_mul_iff_right h_threshold_ne_zero h_threshold_ne_top).mp h6

  have h8 : C_avg * C_plan * δ ^ (3 * ε) ≤ δ ^ (2 * ε) := by
    have h9 : C_Kaufman * C_plan * δ ^ (3 * ε) = C_avg * C_plan * δ ^ (3 * ε) := by
      rw [hC_Kaufman_eq_avg]
    rw [← h9]
    exact h_kaufman_absorb

  have h_final : ν Θ_bad ≤ ENNReal.ofReal (δ ^ (2 * ε)) := by
    calc ν Θ_bad
        ≤ ENNReal.ofReal (C_avg * C_plan * δ ^ (3 * ε)) := h7
      _ ≤ ENNReal.ofReal (δ ^ (2 * ε)) := ENNReal.ofReal_le_ofReal h8

  have h_eq : Θ_bad = {y ∈ Ybar | f y > threshold} := by
    ext y
    simp [Θ_bad, threshold]
    <;> rfl
  exact ⟨Θ_bad, h_eq, h_final⟩

/-- Generalized Kaufman bad-directions lemma for arbitrary box radius `R ≥ 1`.

Uses threshold `δ^(-q_bad)` instead of fixed `δ^(-3ε)`. -/
lemma kaufman_bad_directions_bridge_gen
    {δ ε κ0 τ C_ν C_Kaufman C_plan q_bad R : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (_ : 0 < ε) (hkappa_pos : 0 < κ0)
    (hτ_gt_2κ0 : 2 * κ0 < τ)
    (hC_ν_pos : 0 < C_ν)
    (_ : 0 < C_Kaufman)
    (hq_bad_pos : 0 < q_bad)
    (hR_ge1 : 1 ≤ R)
    (hC_Kaufman_eq : C_Kaufman = 1 + (C_ν + 1) * (2 * R * Real.sqrt 2) ^ (2 * κ0) *
        (1 + 2 * κ0 / (τ - 2 * κ0)))
    {E : Finset (EuclideanSpace ℝ (Fin 2))}
    {μE : Measure (EuclideanSpace ℝ (Fin 2))} [IsProbabilityMeasure μE]
    (hμE_supp : μE.support = (E : Set _))
    (hμE_support_bdd : μE.support ⊆ {p : EuclideanSpace ℝ (Fin 2) | ∀ i, p i ∈ Set.Icc (-R) R})
    {Ybar : Set ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hYbar_fin : Ybar.Finite)
    (_ : ν.support = Ybar)
    (hν_frost : IsDirectionFrostman δ τ C_ν ν)
    (h_energy : rieszEnergy (2 * κ0) hδ_pos μE ≤ ENNReal.ofReal C_plan)
    (h_kaufman_absorb : C_Kaufman * C_plan * δ ^ q_bad ≤ δ ^ (2 * ε)) :
    ∃ (Θ_bad : Set ℝ),
      Θ_bad = {y ∈ Ybar | rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 0 * y + p 1) μE) >
        ENNReal.ofReal (δ ^ (-q_bad))} ∧
      ν Θ_bad ≤ ENNReal.ofReal (δ ^ (2 * ε)) := by
  let f : ℝ → ENNReal := fun y =>
    rieszEnergy (2 * κ0) hδ_pos
      (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 0 * y + p 1) μE)
  let threshold : ENNReal := ENNReal.ofReal (δ ^ (-q_bad))
  let C_avg : ℝ := 1 + (C_ν + 1) * (2 * R * Real.sqrt 2) ^ (2 * κ0) *
      (1 + (2 * κ0) / (τ - 2 * κ0))
  have hδ_le_one : δ ≤ 1 := by linarith
  have hτ_pos : 0 < τ := by linarith
  have hτ_gt_2κ0' : τ > 2 * κ0 := by linarith
  have hC_avg_pos : 0 < C_avg := by dsimp only [C_avg] <;> positivity
  have hC_Kaufman_eq_avg : C_Kaufman = C_avg := by
    rw [hC_Kaufman_eq] <;> rfl
  have hν_support_bdd : ν.support ⊆ Set.Icc 0 1 := hν_frost.2.1
  have h_avg : ∫⁻ (y : ℝ), f y ∂ν ≤
      ENNReal.ofReal C_avg * rieszEnergy (2 * κ0) hδ_pos μE :=
    average_projection_energy_bound_gen
      hτ_pos hkappa_pos hτ_gt_2κ0' hδ_pos hδ_le_one hC_ν_pos
      hν_frost hν_support_bdd hR_ge1 hμE_support_bdd
  have hC_plan_nonneg : 0 ≤ C_plan := by
    by_contra h
    have h' : C_plan < 0 := by exact lt_of_not_ge h
    have h'' : ENNReal.ofReal C_plan = 0 := by
      rw [ENNReal.ofReal_eq_zero.mpr] <;> linarith
    rw [h''] at h_energy
    have h_energy_pos : 0 < rieszEnergy (2 * κ0) hδ_pos μE :=
      rieszEnergy_pos hδ_pos (by linarith)
    exact False.elim (not_le.mpr h_energy_pos h_energy)
  have h_avg2 : ∫⁻ (y : ℝ), f y ∂ν ≤ ENNReal.ofReal (C_avg * C_plan) := by
    calc ∫⁻ (y : ℝ), f y ∂ν
        ≤ ENNReal.ofReal C_avg * rieszEnergy (2 * κ0) hδ_pos μE := h_avg
      _ ≤ ENNReal.ofReal C_avg * ENNReal.ofReal C_plan := by
          exact mul_le_mul_of_nonneg_left h_energy (by positivity)
      _ = ENNReal.ofReal (C_avg * C_plan) := by
          exact (ENNReal.ofReal_mul hC_avg_pos.le).symm
  let Θ_bad : Set ℝ := {y | y ∈ Ybar ∧ f y > threshold}
  have h9 : Θ_bad ⊆ Ybar := by intro y hy; exact hy.1
  have h10 : ∀ y ∈ Θ_bad, f y > threshold := by intro y hy; exact hy.2
  have hΘ_bad_meas : MeasurableSet Θ_bad :=
    (hYbar_fin.subset h9).measurableSet
  have h_threshold_pos : 0 < δ ^ (-q_bad) := by positivity
  have h_threshold_ne_zero : threshold ≠ 0 := by
    have h : threshold = ENNReal.ofReal (δ ^ (-q_bad)) := rfl
    rw [h]
    have hpos : 0 < δ ^ (-q_bad) := by positivity
    exact (ENNReal.ofReal_pos.mpr hpos).ne'
  have h_threshold_ne_top : threshold ≠ ⊤ := by
    simp [threshold] <;> exact ENNReal.coe_ne_top
  let g : ℝ → ENNReal := Set.indicator Θ_bad (fun _ => threshold)
  have h1 : ∀ y, g y ≤ f y := by
    intro y
    by_cases hy : y ∈ Θ_bad
    · have h2 : f y > threshold := hy.2
      have h3 : g y = threshold := by
        unfold g; simp [hy, Set.indicator]
      rw [h3]; exact h2.le
    · have h3 : g y = 0 := by
        unfold g; simp [hy, Set.indicator]
      rw [h3]; exact bot_le
  have h2 : ∫⁻ (y : ℝ), g y ∂ν ≤ ∫⁻ (y : ℝ), f y ∂ν := lintegral_mono h1
  have h3 : ∫⁻ (y : ℝ), g y ∂ν = threshold * ν Θ_bad := by
    unfold g
    rw [lintegral_indicator hΘ_bad_meas (fun (_ : ℝ) => threshold)]
    have h_eq1 : ∫⁻ (y : ℝ), (fun (_ : ℝ) => threshold) y ∂(ν.restrict Θ_bad) =
        ∫⁻ (_ : ℝ), threshold ∂(ν.restrict Θ_bad) := by
      congr with y <;> rfl
    rw [h_eq1, lintegral_const] <;> simp <;> rfl
  have h_markov : threshold * ν Θ_bad ≤ ∫⁻ (y : ℝ), f y ∂ν := by
    rw [← h3]; exact h2
  have h_target : threshold * ENNReal.ofReal (C_avg * C_plan * δ ^ q_bad) =
      ENNReal.ofReal (C_avg * C_plan) := by
    have h4 : threshold = ENNReal.ofReal (δ ^ (-q_bad)) := rfl
    rw [h4]
    have h_pos1 : 0 ≤ δ ^ (-q_bad) := by positivity
    have h5 : ENNReal.ofReal (δ ^ (-q_bad)) * ENNReal.ofReal (C_avg * C_plan * δ ^ q_bad) =
        ENNReal.ofReal (δ ^ (-q_bad) * (C_avg * C_plan * δ ^ q_bad)) := by
      rw [ENNReal.ofReal_mul h_pos1] <;> rfl
    rw [h5]
    have h61 : δ ^ (-q_bad) * δ ^ q_bad = 1 := by
      rw [← Real.rpow_add hδ_pos] <;> ring_nf <;> rw [Real.rpow_zero] <;> ring
    have h6 : δ ^ (-q_bad) * (C_avg * C_plan * δ ^ q_bad) = C_avg * C_plan := by
      have h_reorder : δ ^ (-q_bad) * (C_avg * C_plan * δ ^ q_bad) =
          (C_avg * C_plan) * (δ ^ (-q_bad) * δ ^ q_bad) := by ring
      rw [h_reorder, h61] <;> ring
    rw [h6] <;> rfl
  have h6 : threshold * ν Θ_bad ≤ threshold * ENNReal.ofReal (C_avg * C_plan * δ ^ q_bad) := by
    calc threshold * ν Θ_bad
        ≤ ∫⁻ (y : ℝ), f y ∂ν := h_markov
      _ ≤ ENNReal.ofReal (C_avg * C_plan) := h_avg2
      _ = threshold * ENNReal.ofReal (C_avg * C_plan * δ ^ q_bad) := h_target.symm
  have h7 : ν Θ_bad ≤ ENNReal.ofReal (C_avg * C_plan * δ ^ q_bad) := by
    exact (ENNReal.mul_le_mul_iff_right h_threshold_ne_zero h_threshold_ne_top).mp h6
  have h8 : C_avg * C_plan * δ ^ q_bad ≤ δ ^ (2 * ε) := by
    have h9 : C_Kaufman * C_plan * δ ^ q_bad = C_avg * C_plan * δ ^ q_bad := by
      rw [hC_Kaufman_eq_avg]
    rw [← h9]
    exact h_kaufman_absorb
  have h_final : ν Θ_bad ≤ ENNReal.ofReal (δ ^ (2 * ε)) := by
    calc ν Θ_bad
        ≤ ENNReal.ofReal (C_avg * C_plan * δ ^ q_bad) := h7
      _ ≤ ENNReal.ofReal (δ ^ (2 * ε)) := ENNReal.ofReal_le_ofReal h8
  have h_eq : Θ_bad = {y ∈ Ybar | f y > threshold} := by
    ext y
    simp [Θ_bad, threshold]
    <;> rfl
  exact ⟨Θ_bad, h_eq, h_final⟩

end robust_projection_main
