module

/-
# Kaufman Exact Bridge — Endgame Integration Helper

Thin wrappers around `kaufman_bad_directions_exact` specialized for the
Phase1/ExactEndgame_v3 interface.

## Main results
- `kaufman_exact_for_endgame`: sets `threshold = δ^(-rho_exc)`, `bad_mass = c/8`
- `kaufman_absorption_for_endgame`: proves the absorption condition
  `C_Kaufman * C_plan ≤ δ^(-rho_exc) * (c/8)` from a product bound and
  a δ-smallness condition using WireBudgets-style exponent accounting.

## Usage in ExactEndgame_v3

1. Choose `rho_exc > q_total` where `q_total` bounds `C_Kaufman * C_plan ≤ δ^{-q_total}`
2. Set `q_extra = rho_exc - q_total > 0`
3. Ensure `δ^{q_extra} ≤ c/8` (δ sufficiently small)
4. Call `kaufman_absorption_for_endgame` to get the absorption condition
5. Call `kaufman_exact_for_endgame` to get `ν Θ_bad ≤ c/8`

## Whiteprint node
`phase2_bourgain_pipeline/kaufman_exact_for_endgame`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.Energy.AverageProjectionEnergy
public import MyLeanRepo.Energy.AverageProjectionEnergyGen
public import MyLeanRepo.Energy.KaufmanBadDirectionsBridge
public import MyLeanRepo.Energy.KaufmanBadDirectionsExact
public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Classical

namespace robust_projection_main

/-- **Endgame Kaufman wrapper**: exact bad-mass bound `ν Θ_bad ≤ c/8`.

Specializes `kaufman_bad_directions_exact` with:
- `threshold = δ^(-rho_exc)` (directions with energy above this are "bad")
- `bad_mass = c/8` (exact constant mass bound)

The absorption condition `C_Kaufman * C_plan ≤ δ^(-rho_exc) * (c/8)` must be
supplied; use `kaufman_absorption_for_endgame` to prove it from WireBudgets-style
bounds.
-/
lemma kaufman_exact_for_endgame
    {δ κ0 τ C_ν C_Kaufman C_plan R c rho_exc : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hkappa_pos : 0 < κ0)
    (hτ_gt_2κ0 : 2 * κ0 < τ)
    (hC_ν_pos : 0 < C_ν)
    (hC_Kaufman_pos : 0 < C_Kaufman)
    (hR_ge1 : 1 ≤ R)
    (hC_Kaufman_eq : C_Kaufman = 1 + (C_ν + 1) * (2 * R * Real.sqrt 2) ^ (2 * κ0) *
        (1 + 2 * κ0 / (τ - 2 * κ0)))
    (hc_pos : 0 < c)
    (hrho_exc_pos : 0 < rho_exc)
    (h_absorb : C_Kaufman * C_plan ≤ δ ^ (-rho_exc) * (c / 8))
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
        ENNReal.ofReal (δ ^ (-rho_exc))} ∧
      ν Θ_bad ≤ ENNReal.ofReal (c / 8) := by
  have h_threshold_pos : 0 < δ ^ (-rho_exc) := by positivity
  have h_bad_mass_nonneg : 0 ≤ c / 8 := by positivity
  exact kaufman_bad_directions_exact
    (threshold := δ ^ (-rho_exc))
    (bad_mass := c / 8)
    (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
    (hkappa_pos := hkappa_pos) (hτ_gt_2κ0 := hτ_gt_2κ0)
    (hC_ν_pos := hC_ν_pos) (hC_Kaufman_pos := hC_Kaufman_pos)
    (hR_ge1 := hR_ge1) (hC_Kaufman_eq := hC_Kaufman_eq)
    (h_threshold_pos := h_threshold_pos)
    (h_bad_mass_nonneg := h_bad_mass_nonneg)
    (h_absorb := h_absorb)
    (hμE_supp := hμE_supp)
    (hμE_support_bdd := hμE_support_bdd)
    (hYbar_fin := hYbar_fin) (hν_supp_eq := hν_supp_eq)
    (hν_frost := hν_frost)
    (h_energy := h_energy)

/-- **Absorption helper for endgame Kaufman bridge**.

Given:
- `h_product_bound`: `C_Kaufman * C_plan ≤ δ^{-q_total}`
- `hrho_exc_eq`: `rho_exc = q_total + q_extra`
- `hq_extra_pos`: `0 < q_extra`
- `hδ_small`: `δ^{q_extra} ≤ c/8`

Concludes: `C_Kaufman * C_plan ≤ δ^{-rho_exc} * (c/8)`.

This is the WireBudgets-style absorption: the extra exponent `q_extra` provides
room to absorb the constant factor `c/8` by making δ small enough.
-/
lemma kaufman_absorption_for_endgame
    {δ c C_Kaufman C_plan q_total rho_exc q_extra : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hc_pos : 0 < c)
    (hC_product_nonneg : 0 ≤ C_Kaufman * C_plan)
    (h_product_bound : C_Kaufman * C_plan ≤ δ ^ (-q_total))
    (hrho_exc_eq : rho_exc = q_total + q_extra)
    (hq_extra_pos : 0 < q_extra)
    (hδ_small : δ ^ q_extra ≤ c / 8) :
    C_Kaufman * C_plan ≤ δ ^ (-rho_exc) * (c / 8) := by
  have h1 : δ ^ (-q_total) = δ ^ q_extra * δ ^ (-rho_exc) := by
    have h_exp : q_extra + (-rho_exc) = -q_total := by
      rw [hrho_exc_eq] <;> ring
    have h_rpow : δ ^ q_extra * δ ^ (-rho_exc) = δ ^ (q_extra + (-rho_exc)) := by
      rw [← Real.rpow_add hδ_pos] <;> ring
    rw [h_rpow, h_exp]
  calc
    C_Kaufman * C_plan ≤ δ ^ (-q_total) := h_product_bound
    _ = δ ^ q_extra * δ ^ (-rho_exc) := h1
    _ ≤ (c / 8) * δ ^ (-rho_exc) := by
      gcongr
      <;> exact hδ_small
    _ = δ ^ (-rho_exc) * (c / 8) := by ring

end robust_projection_main
