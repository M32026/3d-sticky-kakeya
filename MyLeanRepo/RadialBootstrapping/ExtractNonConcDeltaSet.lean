module

/-
  ExtractNonConcDeltaSet.lean

  Extract a finite (r,1)-delta set P from a positive-measure subset X_nonconc
  localized to the unit ball, with explicit C_X constant and bound.

  Uses measure_extract_delta_set_explicit from MeasureExtractDeltaSet.lean.
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.MeasureExtractDeltaSetOuter
public import MyLeanRepo.RadialBootstrapping.FurstenbergCaller
public import MyLeanRepo.RadialBootstrapping.StepA_Extract
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set Finset Classical
open scoped ENNReal NNReal


noncomputable section

namespace RadialBootstrapping

/-- Extract a finite (r,1)-delta set P from X_nonconc ⊆ unit ball.

    Given X_nonconc with mass ≥ r^τ/2 and Frostman bound ν(ball x ρ) ≤ C*ρ,
    extract P ⊆ X_nonconc that is a (r,1,C_X)-delta set.

    The bound `hC_X_bound` requires `τ < εF` and r sufficiently small.
    We take the explicit inequality as a hypothesis. -/
lemma extract_nonconc_delta_set
    {ν₁ : Measure Point} [IsProbabilityMeasure ν₁]
    (X_nonconc : Set Point)
    (hX_nonconc_ball : X_nonconc ⊆ closedBall (0 : Point) 1)
    (r τ C εF : ℝ)
    (hr : 0 < r) (hr_lt_one : r < 1) (hτ : 0 < τ) (hC_pos : 0 < C) (hεF_pos : 0 < εF)
    (hX_nonconc_mass : ν₁ X_nonconc ≥ ENNReal.ofReal (Real.rpow r τ / 2))
    (hν_frostman_open : ∀ (x : Point) (ρ : ℝ), 0 < ρ →
      ν₁ (Metric.ball x ρ) ≤ ENNReal.ofReal (C * ρ))
    (hC_X_bound_goal :
      let m := Real.rpow r τ / 2
      let L := max 0 (Real.log (2000 * C / (m * r))) + 1
      let C_X := 100 * C * L / m
      C_X * (Point_exists_doubling.choose : ℝ) ≤ Real.rpow (2 * r) (-εF))
    : ∃ (P : Set Point) (C_X : ℝ) (hC_X_nonneg : 0 ≤ C_X),
        P ⊆ X_nonconc ∧ P.Nonempty ∧ P.Finite ∧
        P ⊆ closedBall (0 : Point) 1 ∧
        IsDeltaSet r 1 C_X hr (by norm_num) hC_X_nonneg P ∧
        C_X * (Point_exists_doubling.choose : ℝ) ≤ Real.rpow (2 * r) (-εF) := by
  let m : ℝ := Real.rpow r τ / 2
  have h1_rpow_pos : 0 < Real.rpow r τ := Real.rpow_pos_of_pos hr τ
  have hm_pos : 0 < m := by
    dsimp only [m]
    positivity
  have hν_frostman_closed : ∀ (x : Point) (ρ : ℝ), 0 < ρ →
      ν₁ (Metric.closedBall x ρ) ≤ ENNReal.ofReal (C * ρ) :=
    frostman_open_to_closed hC_pos hν_frostman_open
  rcases measure_extract_delta_set_explicit_outer
    hX_nonconc_ball ν₁ hm_pos hC_pos
    hX_nonconc_mass hν_frostman_closed hr hr_lt_one
    with ⟨P, hP_sub, hP_nonempty, hP_finite, hP_delta, _h_mass_bound⟩
  let L : ℝ := max 0 (Real.log (2000 * C / (m * r))) + 1
  let C_X : ℝ := 100 * C * L / m
  have hC_X_nonneg : 0 ≤ C_X := by positivity
  have hP_ball : P ⊆ closedBall (0 : Point) 1 :=
    hP_sub.trans hX_nonconc_ball
  have hC_X_bound : C_X * (Point_exists_doubling.choose : ℝ) ≤ Real.rpow (2 * r) (-εF) :=
    hC_X_bound_goal
  exact ⟨P, C_X, hC_X_nonneg,
    hP_sub, hP_nonempty, hP_finite, hP_ball, hP_delta, hC_X_bound⟩

end RadialBootstrapping
