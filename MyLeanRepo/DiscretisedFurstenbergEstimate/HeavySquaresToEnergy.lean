module

/-
  Bridge: HeavySquareRefinement → energy bound.

  Connects three existing components:
  1. `qset_nonconcentration` — ball-growth for Qset centers
  2. `pair_energy_bound` — t-energy bound from ball-growth
  3. `energy_upper_bound_general` — total energy from common-tube bound + t-energy

  Main theorem `heavy_squares_to_energy`: given heavy squares with ball-growth,
  tube families, and a common-tube intersection bound, produce the total
  per-tube energy bound needed by `heavy_squares_refined`.

  Whiteprint node: Phase2 / HeavySquaresToEnergy
  Dependencies: HeavySquareRefinement, HeavySquareEnergyBound, HeavySquaresBridge
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.HeavySquareRefinement
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.Phase2

open DirecretisedFurstenbergEstimate.Lagoon

local notation "Plane" => EuclideanPlane

/-- Centers of coarse squares as a Finset in Plane. -/
def QsetCenters (Δ : ℝ) (Qset : Finset (ℤ × ℤ)) : Finset Plane :=
  Qset.image (squareCenter Δ)

/-- If two integers are distinct, their absolute difference is at least 1. -/
lemma int_abs_diff_ge_one {a b : ℤ} (h : a ≠ b) : 1 ≤ |a - b| := by
  have h1 : a - b ≠ 0 := by omega
  by_cases h2 : 0 ≤ a - b
  · have h3 : 0 < a - b := by omega
    have h4 : 1 ≤ a - b := by omega
    have h5 : |a - b| = a - b := by
      rw [abs_of_nonneg] <;> omega
    rw [h5] <;> omega
  · have h3 : a - b < 0 := by omega
    have h4 : a - b ≤ -1 := by omega
    have h5 : |a - b| = -(a - b) := by
      rw [abs_of_neg] <;> omega
    rw [h5] <;> omega

/-- Norm of a Euclidean plane vector is at least absolute value of each coordinate. -/
lemma norm_ge_coord_abs (v : Plane) (i : Fin 2) : ‖v‖ ≥ |v i| := by
  have h2 : ‖v‖ ^ 2 = (v 0)^2 + (v 1)^2 := by
    rw [EuclideanSpace.norm_eq]
    have h3 : Real.sqrt ((v 0)^2 + (v 1)^2) ^ 2 = (v 0)^2 + (v 1)^2 := by
      rw [Real.sq_sqrt] <;> positivity
    simpa [Fin.sum_univ_two] using h3
  have h3 : ‖v‖ ^ 2 ≥ (v i)^2 := by
    rw [h2]
    fin_cases i <;> simp [Fin.sum_univ_two] <;> nlinarith
  have h4 : 0 ≤ ‖v‖ := by positivity
  have h5 : 0 ≤ |v i| := by positivity
  nlinarith [sq_abs (v i)]

/-- Distinct Δ-squares have distinct centers. -/
lemma squareCenter_injective {Δ : ℝ} (hΔ_pos : 0 < Δ) :
    Function.Injective (squareCenter Δ) := by
  intro Q1 Q2 h
  have h1 : squareCenter Δ Q1 0 = squareCenter Δ Q2 0 := by rw [h]
  have h2 : squareCenter Δ Q1 1 = squareCenter Δ Q2 1 := by rw [h]
  have hq1 : Δ * ((Q1.1 : ℝ) + 1 / 2) = Δ * ((Q2.1 : ℝ) + 1 / 2) := by
    simpa [squareCenter_zero] using h1
  have hq2 : Δ * ((Q1.2 : ℝ) + 1 / 2) = Δ * ((Q2.2 : ℝ) + 1 / 2) := by
    simpa [squareCenter_one] using h2
  have h11 : (Q1.1 : ℝ) = (Q2.1 : ℝ) := by
    apply mul_left_cancel₀ hΔ_pos.ne'
    linarith
  have h22 : (Q1.2 : ℝ) = (Q2.2 : ℝ) := by
    apply mul_left_cancel₀ hΔ_pos.ne'
    linarith
  have hQ11 : Q1.1 = Q2.1 := by exact_mod_cast h11
  have hQ22 : Q1.2 = Q2.2 := by exact_mod_cast h22
  ext <;> tauto

end DirecretisedFurstenbergEstimate.Phase2
