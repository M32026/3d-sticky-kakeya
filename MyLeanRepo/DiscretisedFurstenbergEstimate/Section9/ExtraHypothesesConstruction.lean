module

/-
  CombiningExtraHypotheses_v2 construction helper.

  Constructs the `CombiningExtraHypotheses_v2` structure from:
  - `h_slope` as explicit geometric hypothesis (orientation/coordinate partition)
  - `multiscaleToCombining` output for `h_tj_ge_t` and `h_tj_le_two`
  - `UniformIncidenceData` for `hε_inc_pos`
  - Combining induction smallness condition for `h_exp_condition`

  Whiteprint node: section9 / extra_hypotheses_construction
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.RestructuredStatement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9Assembly

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.CombiningTheoremRework
open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.FormatConversion

/-- Derive slope bound `|T.slope| ≤ 1` from `B1BridgeHypotheses.h_tubes_strip`.

    Since `T.slope = T.a * dyadicDelta k = T.a / 2^k` and
    `h_tubes_strip` gives `-2^k ≤ T.a < 2^k`, we have `|T.a| ≤ 2^k`,
    hence `|T.slope| ≤ 1`. -/
lemma slope_bound_from_b1
    {k : ℕ} {s C : ℝ} {M : ℕ}
    {config : CTNiceConfiguration k s C M}
    (hB1 : DirecretisedFurstenbergEstimate.FormatConversion.M2.B1BridgeHypotheses k config) :
    ∀ T ∈ config.T₀, |T.slope| ≤ 1 := by
  intro T hT
  have h_strip := hB1.h_tubes_strip T hT
  have h1 : -(2 ^ k : ℤ) ≤ T.a := h_strip.1
  have h2 : T.a < (2 ^ k : ℤ) := h_strip.2
  have h3 : |(T.a : ℝ)| ≤ (2 ^ k : ℝ) := by
    rw [abs_le]
    constructor
    · -- Left: -(2^k) ≤ T.a
      have h1' : (-(2 ^ k : ℤ) : ℝ) ≤ (T.a : ℝ) := by exact_mod_cast h1
      have h1'' : (-(2 ^ k : ℝ)) ≤ (T.a : ℝ) := by
        simpa using h1'
      exact h1''
    · -- Right: T.a ≤ 2^k
      have h2' : (T.a : ℝ) < ((2 ^ k : ℤ) : ℝ) := by exact_mod_cast h2
      have h2'' : (T.a : ℝ) ≤ (2 ^ k : ℝ) := by
        have h3' : ((2 ^ k : ℤ) : ℝ) = (2 ^ k : ℝ) := by norm_cast
        rw [h3'] at h2'
        exact h2'.le
      exact h2''
  have h_slope_def : T.slope = (T.a : ℝ) * DiscretisedFurstenbergEstimate.dyadicDelta k := by
    rfl
  have h_dd_pos : 0 < DiscretisedFurstenbergEstimate.dyadicDelta k :=
    DiscretisedFurstenbergEstimate.dyadicDelta_pos k
  have h4 : |T.slope| = |(T.a : ℝ)| * DiscretisedFurstenbergEstimate.dyadicDelta k := by
    rw [h_slope_def, abs_mul]
    have h_abs_dd : |DiscretisedFurstenbergEstimate.dyadicDelta k| = DiscretisedFurstenbergEstimate.dyadicDelta k := by
      rw [abs_of_pos h_dd_pos]
    rw [h_abs_dd]
  rw [h4]
  have h5 : DiscretisedFurstenbergEstimate.dyadicDelta k = 1 / (2 : ℝ) ^ k := by
    simp [DiscretisedFurstenbergEstimate.dyadicDelta] <;> ring
  rw [h5]
  have h6 : |(T.a : ℝ)| * (1 / (2 : ℝ) ^ k) ≤ 1 := by
    calc |(T.a : ℝ)| * (1 / (2 : ℝ) ^ k)
        ≤ (2 ^ k : ℝ) * (1 / (2 : ℝ) ^ k) := by gcongr
      _ = 1 := by
        field_simp <;> ring
  exact h6

/-- Construct `CombiningExtraHypotheses_v2` from available data.

    Note: `h_slope` can be derived from `B1BridgeHypotheses` via
    `slope_bound_from_b1`, since `h_tubes_strip` gives `|T.a| < 2^k`,
    hence `|T.slope| = |T.a| / 2^k < 1`.

    `h_tj_ge_t` and `h_tj_le_two` are both returned by
    `multiscaleToCombining` (as of the updated conclusion).

    `h_exp_condition` follows from the combining induction smallness
    condition applied at the chosen ε_G, η.
-/
lemma construct_extra_hypotheses
    -- ===== Basic parameters =====
    (s t ε_G η ε_N C_P ε_inc : ℝ)
    -- ===== Scale decomposition data =====
    (n : ℕ) (lam : ℝ) (k M : ℕ)
    (config : CTNiceConfiguration k s (Real.rpow (DiscretisedFurstenbergEstimate.dyadicDelta k) (-lam)) M)
    (Δ : Fin (n + 1) → ℝ)
    (scaleClass : Fin n → ScaleClass)
    -- ===== From multiscaleToCombining =====
    (h_tj_ge_t : ∀ (j : Fin n) (t_j' : ℝ),
        scaleClass j = ScaleClass.good t_j' → t ≤ t_j')
    (h_tj_le_two : ∀ (j : Fin n) (t_j' : ℝ),
        scaleClass j = ScaleClass.good t_j' → t_j' ≤ 2)
    -- ===== Geometric slope bound (non-mechanical input) =====
    (h_slope : ∀ T ∈ config.T₀, |T.slope| ≤ 1)
    -- ===== Uniform incidence data =====
    (h_uniform : UniformIncidenceData s t ε_inc)
    -- ===== Smallness condition from combining induction =====
    (h_small : (η + 2 * ε_G) * (1 - s) / (min t 1 - s) + η ≤ ε_inc)
    :
    CombiningExtraHypotheses_v2 s t ε_G η ε_N C_P ε_inc n lam k M config Δ scaleClass :=
  { h_slope := h_slope
    h_tj_ge_t := h_tj_ge_t
    h_tj_le_two := h_tj_le_two
    hε_inc_pos := h_uniform.hε_inc_pos
    h_exp_condition := h_small }

end DirecretisedFurstenbergEstimate.Section9Assembly
