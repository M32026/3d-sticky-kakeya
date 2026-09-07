module

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.CommonScaleComparability
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-
# K_A Wrapper — Common-Scale Comparability for S1, S2

Takes upper/lower bounds relative to a common scale X
(typically `X = sqrt(Nplane δ Pbar)`) and produces the full K_A
comparability block needed by the endgame skeleton.

## Cardinal route (operator-mandated)

Use cardinality-based lower bound WITHOUT occupancy loss:
- Upper: `N(S_i) ≤ C_upper · δ^{-α} · X`
- Lower: `N(S_i) ≥ C_lower · δ^{α+3ρ_sel} · X`
- `q_KA_card = 2α + 3ρ_sel + e_absorb`

The generic wrapper is parameterized over `e_upper`, `e_lower`, `e_absorb`
so it works for any exponent pair.

## Budget fit

For V4: global `qKAV4 = 2α + qMassV4 + 3ρ_sel + 2qAbsorb`
(enlarged 01-12PDT by +3ρ_sel/2 for α_K K_A route).
The occupancy-route theorem computes its own local exponent from the passed α;
when called with α_K = α + 3ρ_sel/2 it yields `qKAV4_old + 3ρ_sel`,
which is tighter than the global budget and can be weakened to `δ^{-qKAV4}`.
With `α = L·η/2`, `qMassV4 = 2ρ_sep + qAbsorb`:
global `qKAV4 = L·η + 2ρ_sep + 3ρ_sel + 3qAbsorb`.
Cardinal route exponent: `q_KA_card = 2α + 3ρ_sel + e_absorb`.
Fit condition: `e_absorb ≤ 2ρ_sep + 3qAbsorb`.

## Whiteprint node
`K_A_wrapper_common_scale`
-/

namespace ProductLikeIncidence.ProductReduction

open ENNReal

/-- **K_A wrapper (generic exponents)**: takes common-scale upper/lower bounds
with explicit exponents, absorbs the constant ratio via `e_absorb`,
and outputs the full K_A comparability block.

For the cardinal route set `e_upper = -α`, `e_lower = α + 3ρ_sel`. -/
lemma K_A_from_common_scale_bounds
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    {e_upper e_lower e_absorb : ℝ}
    (h_exp_nonpos : e_upper - e_lower - e_absorb ≤ 0)
    {X : ENNReal} (hX_pos : 0 < X) (hX_ne_top : X ≠ ⊤)
    {S1 S2 : Set ℝ}
    {C_upper C_lower : ENNReal}
    (hC_lower_pos : 0 < C_lower) (hC_lower_ne_top : C_lower ≠ ⊤)
    (h_absorb : C_upper ≤ C_lower * ENNReal.ofReal (δ ^ (-e_absorb)))
    -- Upper bounds
    (hS1_upper : Nreal δ S1 ≤ C_upper * ENNReal.ofReal (δ ^ e_upper) * X)
    (hS2_upper : Nreal δ S2 ≤ C_upper * ENNReal.ofReal (δ ^ e_upper) * X)
    -- Lower bounds
    (hS1_lower : C_lower * ENNReal.ofReal (δ ^ e_lower) * X ≤ Nreal δ S1)
    (hS2_lower : C_lower * ENNReal.ofReal (δ ^ e_lower) * X ≤ Nreal δ S2)
    : ∃ (K_A : ENNReal),
        (Nreal δ S1 ≤ K_A * Nreal δ S2) ∧
        (Nreal δ S2 ≤ K_A * Nreal δ S1) ∧
        (1 ≤ K_A) ∧
        (K_A ≠ ⊤) ∧
        (K_A ≤ ENNReal.ofReal (δ ^ (e_upper - e_lower - e_absorb))) := by
  let q_KA := e_upper - e_lower - e_absorb

  have h_comp := common_scale_comparability hδ_pos
    (e_upper := e_upper) (e_lower := e_lower) (e_absorb := e_absorb)
    hX_pos hX_ne_top
    (C_upper := C_upper) (C_lower := C_lower)
    hC_lower_pos hC_lower_ne_top h_absorb
    hS1_upper hS1_lower hS2_upper hS2_lower

  let K_A : ENNReal := ENNReal.ofReal (δ ^ q_KA)
  have hK_A_def : K_A = ENNReal.ofReal (δ ^ q_KA) := by rfl

  have hS1_le_S2 : Nreal δ S1 ≤ K_A * Nreal δ S2 := by
    simpa [K_A] using h_comp.1
  have hS2_le_S1 : Nreal δ S2 ≤ K_A * Nreal δ S1 := by
    simpa [K_A] using h_comp.2

  have hq_KA_nonpos : q_KA ≤ 0 := h_exp_nonpos
  have hK_A_ge_one : 1 ≤ K_A := by
    have h1 : δ ^ q_KA ≥ 1 := by
      have h2 : q_KA ≤ (0 : ℝ) := hq_KA_nonpos
      have h3 : δ ^ q_KA ≥ δ ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hδ_pos (by linarith) h2
      simpa using h3
    have h4 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (δ ^ q_KA) := by
      gcongr
    simpa [K_A] using h4

  have hK_A_ne_top : K_A ≠ ⊤ := by
    simp [K_A]

  have hK_A_le : K_A ≤ ENNReal.ofReal (δ ^ q_KA) := by
    simp [K_A]

  exact ⟨K_A, hS1_le_S2, hS2_le_S1, hK_A_ge_one, hK_A_ne_top, hK_A_le⟩

/-- **Cardinal-route K_A** (NOT CURRENTLY APPLICABLE): convenience wrapper
with exponents `e_upper = -α`, `e_lower = α + 3ρ_sel`.

Its lower-bound hypothesis `N(S_i) ≥ C_lower · δ^{α+3ρ_sel} · X` is stronger
than what the current Cobalt witnesses provide (they lose mass/occupancy).
Kept for reference; use `K_A_occupancy_route` instead.

Output exponent: `q_KA_card = 2α + 3ρ_sel + e_absorb`. -/
lemma K_A_cardinal_route
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    {α rho_sel e_absorb : ℝ}
    (h_exp_nonneg : 0 ≤ 2 * α + 3 * rho_sel + e_absorb)
    {X : ENNReal} (hX_pos : 0 < X) (hX_ne_top : X ≠ ⊤)
    {S1 S2 : Set ℝ}
    {C_upper C_lower : ENNReal}
    (hC_lower_pos : 0 < C_lower) (hC_lower_ne_top : C_lower ≠ ⊤)
    (h_absorb : C_upper ≤ C_lower * ENNReal.ofReal (δ ^ (-e_absorb)))
    -- Upper: N(S_i) ≤ C_upper · δ^{-α} · X
    (hS1_upper : Nreal δ S1 ≤ C_upper * ENNReal.ofReal (δ ^ (-α)) * X)
    (hS2_upper : Nreal δ S2 ≤ C_upper * ENNReal.ofReal (δ ^ (-α)) * X)
    -- Lower: N(S_i) ≥ C_lower · δ^{α+3ρ_sel} · X
    (hS1_lower : C_lower * ENNReal.ofReal (δ ^ (α + 3 * rho_sel)) * X ≤ Nreal δ S1)
    (hS2_lower : C_lower * ENNReal.ofReal (δ ^ (α + 3 * rho_sel)) * X ≤ Nreal δ S2)
    : ∃ (K_A : ENNReal),
        (Nreal δ S1 ≤ K_A * Nreal δ S2) ∧
        (Nreal δ S2 ≤ K_A * Nreal δ S1) ∧
        (1 ≤ K_A) ∧
        (K_A ≠ ⊤) ∧
        (K_A ≤ ENNReal.ofReal (δ ^ (-(2 * α + 3 * rho_sel + e_absorb)))) := by
  have h_exp_nonpos' : (-α) - (α + 3 * rho_sel) - e_absorb ≤ 0 := by
    have h : (-α) - (α + 3 * rho_sel) - e_absorb = -(2 * α + 3 * rho_sel + e_absorb) := by ring
    rw [h]
    exact neg_nonpos.mpr h_exp_nonneg
  have h_main := K_A_from_common_scale_bounds
    hδ_pos hδ_lt_one
    (e_upper := -α) (e_lower := α + 3 * rho_sel) (e_absorb := e_absorb)
    h_exp_nonpos' hX_pos hX_ne_top
    (C_upper := C_upper) (C_lower := C_lower)
    hC_lower_pos hC_lower_ne_top h_absorb
    hS1_upper hS2_upper hS1_lower hS2_lower
  rcases h_main with ⟨K_A, hS1_le_S2, hS2_le_S1, hK_A_ge_one, hK_A_ne_top, hK_A_le⟩
  have h_exp_eq : (-α) - (α + 3 * rho_sel) - e_absorb = -(2 * α + 3 * rho_sel + e_absorb) := by ring
  rw [h_exp_eq] at hK_A_le
  exact ⟨K_A, hS1_le_S2, hS2_le_S1, hK_A_ge_one, hK_A_ne_top, hK_A_le⟩

/-- **Budget fit for cardinal route (updated qKAV4)**: proves
`2α + 3ρ_sel + e_absorb ≤ 2α + qMassV4 + (3/2)ρ_sel + 2qAbsorb`.

With `qMassV4 = 2ρ_sep + qAbsorb`, this simplifies to
`1.5ρ_sel + e_absorb ≤ 2ρ_sep + 3qAbsorb`,
which holds when `e_absorb ≤ 2ρ_sep + 3qAbsorb - 1.5ρ_sel`. -/
lemma cardinal_KA_fits_qKAV4
    {α rho_sel rho_sep qAbsorb e_absorb qMassV4 : ℝ}
    (h_qMass : qMassV4 = 2 * rho_sep + qAbsorb)
    (h_fit : e_absorb ≤ 2 * rho_sep + 3 * qAbsorb - (3 * rho_sel) / 2)
    : 2 * α + 3 * rho_sel + e_absorb ≤
      2 * α + qMassV4 + (3 * rho_sel) / 2 + 2 * qAbsorb := by
  rw [h_qMass]
  linarith

/-- **Occupancy-route K_A** (operator-mandated, current route): uses
Cobalt's occupancy-aware lower bounds.

Exponents:
- `e_upper = -α`
- `e_lower = α + qMassV4 + (3/2)ρ_sel`
- `e_absorb = 2·qAbsorb`

The comparability exponent is exactly `qKAV4`:
`e_upper - e_lower - e_absorb = -(2α + qMassV4 + 1.5ρ_sel + 2qAbsorb) = -qKAV4`.

Thus `K_A ≤ δ^{-qKAV4}`, fitting the V4 budget exactly. -/
lemma K_A_occupancy_route
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    {α qMassV4 rho_sel qAbsorb : ℝ}
    (hqKAV4_nonneg : 0 ≤ 2 * α + qMassV4 + (3 * rho_sel) / 2 + 2 * qAbsorb)
    {X : ENNReal} (hX_pos : 0 < X) (hX_ne_top : X ≠ ⊤)
    {S1 S2 : Set ℝ}
    {C_upper C_lower : ENNReal}
    (hC_lower_pos : 0 < C_lower) (hC_lower_ne_top : C_lower ≠ ⊤)
    (h_absorb : C_upper ≤ C_lower * ENNReal.ofReal (δ ^ (-(2 * qAbsorb))))
    -- Upper: N(S_i) ≤ C_upper · δ^{-α} · X
    (hS1_upper : Nreal δ S1 ≤ C_upper * ENNReal.ofReal (δ ^ (-α)) * X)
    (hS2_upper : Nreal δ S2 ≤ C_upper * ENNReal.ofReal (δ ^ (-α)) * X)
    -- Lower: N(S_i) ≥ C_lower · δ^{α + qMassV4 + 1.5ρ_sel} · X
    (hS1_lower : C_lower * ENNReal.ofReal (δ ^ (α + qMassV4 + (3 * rho_sel) / 2)) * X ≤ Nreal δ S1)
    (hS2_lower : C_lower * ENNReal.ofReal (δ ^ (α + qMassV4 + (3 * rho_sel) / 2)) * X ≤ Nreal δ S2)
    : ∃ (K_A : ENNReal),
        (Nreal δ S1 ≤ K_A * Nreal δ S2) ∧
        (Nreal δ S2 ≤ K_A * Nreal δ S1) ∧
        (1 ≤ K_A) ∧
        (K_A ≠ ⊤) ∧
        (K_A ≤ ENNReal.ofReal (δ ^ (-(2 * α + qMassV4 + (3 * rho_sel) / 2 + 2 * qAbsorb)))) := by
  let e_upper := -α
  let e_lower := α + qMassV4 + (3 * rho_sel) / 2
  let e_absorb := 2 * qAbsorb
  let qKAV4 := 2 * α + qMassV4 + (3 * rho_sel) / 2 + 2 * qAbsorb

  have h_exp_nonpos : e_upper - e_lower - e_absorb ≤ 0 := by
    have h : e_upper - e_lower - e_absorb = -qKAV4 := by
      simp [e_upper, e_lower, e_absorb, qKAV4] <;> ring
    rw [h]
    exact neg_nonpos.mpr hqKAV4_nonneg

  have h_main := K_A_from_common_scale_bounds
    hδ_pos hδ_lt_one
    (e_upper := e_upper) (e_lower := e_lower) (e_absorb := e_absorb)
    h_exp_nonpos hX_pos hX_ne_top
    (C_upper := C_upper) (C_lower := C_lower)
    hC_lower_pos hC_lower_ne_top h_absorb
    hS1_upper hS2_upper hS1_lower hS2_lower

  rcases h_main with ⟨K_A, hS1_le_S2, hS2_le_S1, hK_A_ge_one, hK_A_ne_top, hK_A_le⟩
  have h_exp_eq : e_upper - e_lower - e_absorb = -qKAV4 := by
    simp [e_upper, e_lower, e_absorb, qKAV4] <;> ring
  rw [h_exp_eq] at hK_A_le
  exact ⟨K_A, hS1_le_S2, hS2_le_S1, hK_A_ge_one, hK_A_ne_top, hK_A_le⟩

end ProductLikeIncidence.ProductReduction
