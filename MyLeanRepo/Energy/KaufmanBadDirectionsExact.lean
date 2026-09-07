module

/-
# Kaufman Bad Directions Bridge — Exact Mass Version

Generalizes `kaufman_bad_directions_bridge_gen` to output an **exact bad mass
bound** `bad_mass` instead of the exponent bound `δ^(2*ε)`.

## Why this is needed

The old interface required:
  `C_Kaufman * C_plan * δ^q_bad ≤ δ^(2*ε)`

When `q_bad` is large (due to C_Pbar regularity, Kaufman R^(2κ0) factor, etc.),
this condition forces `ε` to be large, which conflicts with the Phase 3 density
budget `3ε + qG + q_absorb ≤ η`. The condition `δ^ε ≤ c/4` then becomes
impossible for small δ.

The exact-mass version decouples the bad-direction mass from ε:
  - `threshold`: energy threshold for "bad" directions (e.g. `δ^(-rho_exc)`)
  - `bad_mass`: explicit target mass bound (e.g. `c/8`)
  - Condition: `C_Kaufman * C_plan ≤ threshold * bad_mass`

This is the Markov inequality in its cleanest form:
  threshold · ν(Θ_bad) ≤ ∫ E_y dν ≤ C_Kaufman · C_plan
  ⟹ ν(Θ_bad) ≤ C_Kaufman · C_plan / threshold ≤ bad_mass

## Main result

`kaufman_bad_directions_exact`: given explicit `threshold` and `bad_mass`,
outputs Θ_bad with ν(Θ_bad) ≤ bad_mass.

## Whiteprint node

`phase2_bourgain_pipeline/kaufman_bad_directions_exact`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.Energy.AverageProjectionEnergy
public import MyLeanRepo.Energy.AverageProjectionEnergyGen
public import MyLeanRepo.Energy.KaufmanBadDirectionsBridge
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Classical

namespace robust_projection_main

/-- **Exact-mass Kaufman bad-directions lemma**.

Given explicit `threshold > 0` and `bad_mass ≥ 0`, and the absorption
condition `C_Kaufman * C_plan ≤ threshold * bad_mass`, outputs a set
Θ_bad of directions with energy above `threshold` and proves
`ν(Θ_bad) ≤ bad_mass`.

This decouples the bad-mass bound from the ε budget, allowing the caller
to choose `threshold = δ^(-rho_exc)` and `bad_mass = c/8` (or any other
exact constant) independently.

### Parameters
- `threshold`: energy threshold for "bad" directions (real, positive)
- `bad_mass`: target upper bound on ν(Θ_bad) (real, non-negative)
- `h_absorb`: `C_Kaufman * C_plan ≤ threshold * bad_mass`

### Proof sketch
1. Kaufman averaging: ∫ E_y dν ≤ C_Kaufman · C_plan
2. Markov: threshold · ν(Θ_bad) ≤ ∫ E_y dν
3. Combine with h_absorb: threshold · ν(Θ_bad) ≤ threshold · bad_mass
4. Cancel threshold (positive, finite): ν(Θ_bad) ≤ bad_mass
-/
lemma kaufman_bad_directions_exact
    {δ κ0 τ C_ν C_Kaufman C_plan R : ℝ}
    (threshold bad_mass : ℝ)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hkappa_pos : 0 < κ0)
    (hτ_gt_2κ0 : 2 * κ0 < τ)
    (hC_ν_pos : 0 < C_ν)
    (hC_Kaufman_pos : 0 < C_Kaufman)
    (hR_ge1 : 1 ≤ R)
    (hC_Kaufman_eq : C_Kaufman = 1 + (C_ν + 1) * (2 * R * Real.sqrt 2) ^ (2 * κ0) *
        (1 + 2 * κ0 / (τ - 2 * κ0)))
    (h_threshold_pos : 0 < threshold)
    (h_bad_mass_nonneg : 0 ≤ bad_mass)
    (h_absorb : C_Kaufman * C_plan ≤ threshold * bad_mass)
    {E : Finset (EuclideanSpace ℝ (Fin 2))}
    {μE : Measure (EuclideanSpace ℝ (Fin 2))} [IsProbabilityMeasure μE]
    (hμE_supp : μE.support = (E : Set _))
    (hμE_support_bdd : μE.support ⊆ {p : EuclideanSpace ℝ (Fin 2) | ∀ i, p i ∈ Set.Icc (-R) R})
    {Ybar : Set ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hYbar_fin : Ybar.Finite)
    (hν_supp_eq : ν.support = Ybar)
    (hν_frost : IsDirectionFrostman δ τ C_ν ν)
    (h_energy : rieszEnergy (2 * κ0) hδ_pos μE ≤ ENNReal.ofReal C_plan) :
    ∃ (Θ_bad : Set ℝ),
      Θ_bad = {y ∈ Ybar | rieszEnergy (2 * κ0) hδ_pos
          (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 0 * y + p 1) μE) >
        ENNReal.ofReal threshold} ∧
      ν Θ_bad ≤ ENNReal.ofReal bad_mass := by
  let f : ℝ → ENNReal := fun y =>
    rieszEnergy (2 * κ0) hδ_pos
      (Measure.map (fun p : EuclideanSpace ℝ (Fin 2) => p 0 * y + p 1) μE)
  let threshold' : ENNReal := ENNReal.ofReal threshold
  let C_avg : ℝ := 1 + (C_ν + 1) * (2 * R * Real.sqrt 2) ^ (2 * κ0) *
      (1 + (2 * κ0) / (τ - 2 * κ0))

  have hδ_le_one : δ ≤ 1 := by linarith
  have hτ_pos : 0 < τ := by linarith
  have hτ_gt_2κ0' : τ > 2 * κ0 := by linarith
  have hC_avg_pos : 0 < C_avg := by dsimp only [C_avg] <;> positivity
  have hC_Kaufman_eq_avg : C_Kaufman = C_avg := by
    rw [hC_Kaufman_eq] <;> rfl

  -- Support bounds for Kaufman averaging
  have hν_support_bdd : ν.support ⊆ Set.Icc 0 1 := hν_frost.2.1

  -- Step 1: Kaufman averaging bound (R-generalized)
  have h_avg : ∫⁻ (y : ℝ), f y ∂ν ≤
      ENNReal.ofReal C_avg * rieszEnergy (2 * κ0) hδ_pos μE :=
    average_projection_energy_bound_gen
      hτ_pos hkappa_pos hτ_gt_2κ0' hδ_pos hδ_le_one hC_ν_pos
      hν_frost hν_support_bdd hR_ge1 hμE_support_bdd

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
  let Θ_bad : Set ℝ := {y | y ∈ Ybar ∧ f y > threshold'}
  have h9 : Θ_bad ⊆ Ybar := by intro y hy; exact hy.1
  have h10 : ∀ y ∈ Θ_bad, f y > threshold' := by intro y hy; exact hy.2
  have hΘ_bad_meas : MeasurableSet Θ_bad :=
    (hYbar_fin.subset h9).measurableSet

  have h_threshold_ne_zero : threshold' ≠ 0 := by
    have h : threshold' = ENNReal.ofReal threshold := rfl
    rw [h]
    exact (ENNReal.ofReal_pos.mpr h_threshold_pos).ne'
  have h_threshold_ne_top : threshold' ≠ ⊤ := by
    simp [threshold']

  -- Step 4: Markov inequality: threshold' * ν Θ_bad ≤ ∫ f dν
  let g : ℝ → ENNReal := Set.indicator Θ_bad (fun _ => threshold')
  have h1 : ∀ y, g y ≤ f y := by
    intro y
    by_cases hy : y ∈ Θ_bad
    · have h2 : f y > threshold' := hy.2
      have h3 : g y = threshold' := by
        unfold g; simp [hy, Set.indicator]
      rw [h3]; exact h2.le
    · have h3 : g y = 0 := by
        unfold g; simp [hy, Set.indicator]
      rw [h3]; exact bot_le
  have h2 : ∫⁻ (y : ℝ), g y ∂ν ≤ ∫⁻ (y : ℝ), f y ∂ν := lintegral_mono h1
  have h3 : ∫⁻ (y : ℝ), g y ∂ν = threshold' * ν Θ_bad := by
    unfold g
    rw [lintegral_indicator hΘ_bad_meas (fun (_ : ℝ) => threshold')]
    have h_eq1 : ∫⁻ (y : ℝ), (fun (_ : ℝ) => threshold') y ∂(ν.restrict Θ_bad) =
        ∫⁻ (_ : ℝ), threshold' ∂(ν.restrict Θ_bad) := by
      congr with y <;> rfl
    rw [h_eq1, lintegral_const] <;> simp <;> rfl
  have h_markov : threshold' * ν Θ_bad ≤ ∫⁻ (y : ℝ), f y ∂ν := by
    rw [← h3]; exact h2

  -- Step 5: Use exact absorption condition
  -- C_avg * C_plan ≤ threshold * bad_mass
  have h_absorb' : C_avg * C_plan ≤ threshold * bad_mass := by
    have h9 : C_Kaufman * C_plan = C_avg * C_plan := by
      rw [hC_Kaufman_eq_avg]
    rw [← h9]
    exact h_absorb

  -- threshold' * ENNReal.ofReal bad_mass = ENNReal.ofReal (threshold * bad_mass)
  have h_mul_distrib : threshold' * ENNReal.ofReal bad_mass =
      ENNReal.ofReal (threshold * bad_mass) := by
    have h4 : threshold' = ENNReal.ofReal threshold := rfl
    rw [h4, ENNReal.ofReal_mul h_threshold_pos.le]

  have h6 : threshold' * ν Θ_bad ≤ threshold' * ENNReal.ofReal bad_mass := by
    calc threshold' * ν Θ_bad
        ≤ ∫⁻ (y : ℝ), f y ∂ν := h_markov
      _ ≤ ENNReal.ofReal (C_avg * C_plan) := h_avg2
      _ ≤ ENNReal.ofReal (threshold * bad_mass) := ENNReal.ofReal_le_ofReal h_absorb'
      _ = threshold' * ENNReal.ofReal bad_mass := h_mul_distrib.symm

  -- Step 6: Cancel threshold' to get ν Θ_bad ≤ bad_mass
  have h7 : ν Θ_bad ≤ ENNReal.ofReal bad_mass := by
    exact (ENNReal.mul_le_mul_iff_right h_threshold_ne_zero h_threshold_ne_top).mp h6

  have h_eq : Θ_bad = {y ∈ Ybar | f y > threshold'} := by
    ext y
    simp [Θ_bad, threshold']
    <;> rfl
  exact ⟨Θ_bad, h_eq, h7⟩

end robust_projection_main
