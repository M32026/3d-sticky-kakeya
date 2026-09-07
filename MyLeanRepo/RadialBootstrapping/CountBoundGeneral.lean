module

/-
  CountBoundGeneral.lean

  General count bound for the concentrated case that works with arbitrary
  distance bound D (not just D ≤ 3r/2).

  Key identity: W * ξ₀ ≤ C₁ * r where W = r + (D+r)*r/(8ξ₀)
  Then W^σ * ξ₀ ≤ C₁^σ * r^(σ+14τ), giving the count bound
  for small enough r.
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set Finset Classical
open scoped ENNReal NNReal


noncomputable section

namespace RadialBootstrapping

/-- General count bound for concentrated case.

    Given direction extraction cardinality lower bound with arbitrary W,
    prove |S| * m > 26 * C * ξ₀ using the identity W*ξ₀ ≤ C₁*r
    and κ(1-σ)=14τ.

    Requires small-r condition: r^(2τ) < 1 / (390 * K * C * C₁^σ).
-/
lemma concentrated_count_bound_general
    {α : Type*} {S : Finset α}
    (r τ σ ξ₀ κ K C W m D C₁ : ℝ)
    (hr : 0 < r) (hr_small : r < 1)
    (hτ : 0 < τ) (hσ : 0 ≤ σ) (hσ_lt_one : σ < 1)
    (hξ₀_pos : 0 < ξ₀) (hξ₀_le_rκ : ξ₀ ≤ Real.rpow r κ)
    (hκ : κ = 14 * τ / (1 - σ)) (hκ_pos : 0 < κ)
    (hK : 1 ≤ K) (hC : 1 ≤ C)
    (hW_pos : 0 < W) (hm_pos : 0 < m)
    (hm_eq : m = Real.rpow r (σ + 4 * τ))
    (hWξ_bound : W * ξ₀ ≤ C₁ * r)
    (hC₁_pos : 0 < C₁)
    (h_card_lower : (S.card : ℝ) ≥
        Real.rpow r (8 * τ) / (15 * K * Real.rpow W σ))
    (h_small : Real.rpow r (2 * τ) < 1 / (390 * K * C * Real.rpow C₁ σ)) :
    (S.card : ℝ) * m > 26 * C * ξ₀ := by
  have h1mσ : 0 < 1 - σ := by linarith
  have hκ14τ : κ * (1 - σ) = 14 * τ := by
    rw [hκ]
    field_simp [h1mσ.ne'] <;> ring
  have hWσ_pos : 0 < Real.rpow W σ := Real.rpow_pos_of_pos hW_pos σ
  have hK_pos : 0 < K := by linarith
  have hC_pos : 0 < C := by linarith
  have hC₁σ_pos : 0 < Real.rpow C₁ σ := Real.rpow_pos_of_pos hC₁_pos σ
  have h_r2τ_pos : 0 < Real.rpow r (2 * τ) := Real.rpow_pos_of_pos hr (2 * τ)

  -- W^σ * ξ₀ ≤ C₁^σ * r^(σ+14τ)
  have h_rpow_Wξ : Real.rpow W σ * ξ₀ ≤ Real.rpow C₁ σ * Real.rpow r (σ + 14 * τ) := by
    have h_mul_rpow : Real.rpow W σ * Real.rpow ξ₀ σ = Real.rpow (W * ξ₀) σ := by
      have h : Real.rpow (W * ξ₀) σ = Real.rpow W σ * Real.rpow ξ₀ σ :=
        Real.mul_rpow hW_pos.le hξ₀_pos.le
      exact h.symm
    have h2 : Real.rpow (W * ξ₀) σ ≤ Real.rpow (C₁ * r) σ :=
      Real.rpow_le_rpow (by positivity) hWξ_bound hσ
    have h3 : Real.rpow (C₁ * r) σ = Real.rpow C₁ σ * Real.rpow r σ :=
      Real.mul_rpow hC₁_pos.le hr.le
    have h41 : Real.rpow ξ₀ (1 - σ) * Real.rpow ξ₀ σ = ξ₀ := by
      have h5 : Real.rpow ξ₀ ((1 - σ) + σ) = Real.rpow ξ₀ (1 - σ) * Real.rpow ξ₀ σ :=
        Real.rpow_add hξ₀_pos (1 - σ) σ
      have h6 : (1 - σ) + σ = 1 := by ring
      have h7 : Real.rpow ξ₀ 1 = ξ₀ := by simp
      have h8 : Real.rpow ξ₀ ((1 - σ) + σ) = ξ₀ := by rw [h6, h7]
      exact h5 ▸ h8
    have hξ1σ_nonneg : 0 ≤ Real.rpow ξ₀ (1 - σ) := Real.rpow_nonneg (by linarith) (1 - σ)
    calc
      Real.rpow W σ * ξ₀
        = Real.rpow W σ * (Real.rpow ξ₀ (1 - σ) * Real.rpow ξ₀ σ) := by rw [h41]
      _ = Real.rpow ξ₀ (1 - σ) * (Real.rpow W σ * Real.rpow ξ₀ σ) := by ring
      _ = Real.rpow ξ₀ (1 - σ) * Real.rpow (W * ξ₀) σ := by rw [h_mul_rpow]
      _ ≤ Real.rpow ξ₀ (1 - σ) * Real.rpow (C₁ * r) σ := by
          exact mul_le_mul_of_nonneg_left h2 hξ1σ_nonneg
      _ = Real.rpow ξ₀ (1 - σ) * (Real.rpow C₁ σ * Real.rpow r σ) := by rw [h3]
      _ = Real.rpow C₁ σ * (Real.rpow ξ₀ (1 - σ) * Real.rpow r σ) := by ring
      _ ≤ Real.rpow C₁ σ * (Real.rpow (Real.rpow r κ) (1 - σ) * Real.rpow r σ) := by
          have h_ξ_le : Real.rpow ξ₀ (1 - σ) ≤ Real.rpow (Real.rpow r κ) (1 - σ) :=
            Real.rpow_le_rpow (by positivity) hξ₀_le_rκ (by linarith)
          have h_rσ_nonneg : 0 ≤ Real.rpow r σ := Real.rpow_nonneg hr.le σ
          have h_C₁σ_nonneg : 0 ≤ Real.rpow C₁ σ := Real.rpow_nonneg hC₁_pos.le σ
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h_ξ_le h_rσ_nonneg) h_C₁σ_nonneg
      _ = Real.rpow C₁ σ * Real.rpow r (κ * (1 - σ)) * Real.rpow r σ := by
        have h8 : Real.rpow (Real.rpow r κ) (1 - σ) = Real.rpow r (κ * (1 - σ)) := by
          simpa [Real.rpow_mul hr.le] using rfl
        rw [h8] <;> ring
      _ = Real.rpow C₁ σ * Real.rpow r (σ + 14 * τ) := by
        have h91 : Real.rpow r (κ * (1 - σ)) = Real.rpow r (14 * τ) := by rw [hκ14τ]
        rw [h91]
        have h92 : Real.rpow r (14 * τ) * Real.rpow r σ = Real.rpow r ((14 * τ) + σ) := by
          exact (Real.rpow_add hr (14 * τ) σ).symm
        have h93 : (14 * τ) + σ = σ + 14 * τ := by ring
        have h94 : Real.rpow C₁ σ * Real.rpow r (14 * τ) * Real.rpow r σ =
            Real.rpow C₁ σ * (Real.rpow r (14 * τ) * Real.rpow r σ) := by ring
        rw [h94, h92, h93]

  -- |S| * m ≥ r^(σ+12τ) / (15 * K * W^σ)
  have h_rpow_sum1 : Real.rpow r (8 * τ) * Real.rpow r (σ + 4 * τ) = Real.rpow r (σ + 12 * τ) := by
    have h : Real.rpow r ((8 * τ) + (σ + 4 * τ)) = Real.rpow r (8 * τ) * Real.rpow r (σ + 4 * τ) :=
      Real.rpow_add hr (8 * τ) (σ + 4 * τ)
    have h2 : (8 * τ) + (σ + 4 * τ) = σ + 12 * τ := by ring
    rw [h2] at h
    exact h.symm
  have h_main : (S.card : ℝ) * m ≥
      Real.rpow r (σ + 12 * τ) / (15 * K * Real.rpow W σ) := by
    rw [hm_eq]
    have h1 : (S.card : ℝ) * Real.rpow r (σ + 4 * τ) ≥
        (Real.rpow r (8 * τ) / (15 * K * Real.rpow W σ)) * Real.rpow r (σ + 4 * τ) := by
      gcongr <;> exact (Real.rpow_pos_of_pos hr (σ + 4 * τ)).le
    have h2 : (Real.rpow r (8 * τ) / (15 * K * Real.rpow W σ)) * Real.rpow r (σ + 4 * τ) =
        (Real.rpow r (8 * τ) * Real.rpow r (σ + 4 * τ)) / (15 * K * Real.rpow W σ) := by ring
    rw [h2, h_rpow_sum1] at h1
    exact h1

  -- r^(-2τ) > 390 * K * C * C₁^σ
  have h_rneg2τ : Real.rpow r (-2 * τ) > 390 * K * C * Real.rpow C₁ σ := by
    have h13 : Real.rpow r (-2 * τ) * Real.rpow r (2 * τ) = 1 := by
      have h14 : Real.rpow r ((-2 * τ) + (2 * τ)) = Real.rpow r (-2 * τ) * Real.rpow r (2 * τ) :=
        Real.rpow_add hr (-2 * τ) (2 * τ)
      have h15 : (-2 * τ) + (2 * τ) = 0 := by ring
      have h16 : Real.rpow r ((-2 * τ) + (2 * τ)) = 1 := by rw [h15]; simp
      exact h14 ▸ h16
    have h_inv : Real.rpow r (-2 * τ) = (Real.rpow r (2 * τ))⁻¹ := by
      exact eq_inv_of_mul_eq_one_left h13
    rw [h_inv]
    have h12 : 0 < 390 * K * C * Real.rpow C₁ σ := by positivity
    have h_const_pos : 0 < 1 / (390 * K * C * Real.rpow C₁ σ) := by positivity
    have h17 : (Real.rpow r (2 * τ))⁻¹ > (1 / (390 * K * C * Real.rpow C₁ σ))⁻¹ := by
      have h : Real.rpow r (2 * τ) < 1 / (390 * K * C * Real.rpow C₁ σ) := h_small
      have h' : (Real.rpow r (2 * τ))⁻¹ > (1 / (390 * K * C * Real.rpow C₁ σ))⁻¹ := by
        gcongr
      exact h'
    have h18 : (1 / (390 * K * C * Real.rpow C₁ σ))⁻¹ = 390 * K * C * Real.rpow C₁ σ := by
      field_simp [h12.ne'] <;> ring
    rw [h18] at h17
    exact h17

  -- r^(σ+12τ) = r^(σ+14τ) * r^(-2τ)
  have h_rpow_split : Real.rpow r (σ + 12 * τ) =
      Real.rpow r (σ + 14 * τ) * Real.rpow r (-2 * τ) := by
    have h : Real.rpow r ((σ + 14 * τ) + (-2 * τ)) =
        Real.rpow r (σ + 14 * τ) * Real.rpow r (-2 * τ) :=
      Real.rpow_add hr (σ + 14 * τ) (-2 * τ)
    have h2 : (σ + 14 * τ) + (-2 * τ) = σ + 12 * τ := by ring
    rw [h2] at h
    exact h

  have h4 : Real.rpow r (σ + 12 * τ) >
      390 * K * C * (Real.rpow W σ * ξ₀) := by
    have h5 : 390 * K * C * (Real.rpow W σ * ξ₀) ≤
        390 * K * C * (Real.rpow C₁ σ * Real.rpow r (σ + 14 * τ)) := by
      gcongr <;> exact h_rpow_Wξ
    have h6 : Real.rpow r (σ + 12 * τ) =
        Real.rpow r (σ + 14 * τ) * Real.rpow r (-2 * τ) := by
      exact h_rpow_split
    rw [h6]
    have h7 : Real.rpow r (σ + 14 * τ) * Real.rpow r (-2 * τ) >
        Real.rpow r (σ + 14 * τ) * (390 * K * C * Real.rpow C₁ σ) := by
      have h_pos14 : 0 < Real.rpow r (σ + 14 * τ) := Real.rpow_pos_of_pos hr (σ + 14 * τ)
      gcongr
      <;> exact h_pos14
      <;> exact h_rneg2τ
    have h8 : Real.rpow r (σ + 14 * τ) * (390 * K * C * Real.rpow C₁ σ) =
        390 * K * C * (Real.rpow C₁ σ * Real.rpow r (σ + 14 * τ)) := by ring
    rw [h8] at h7
    calc
      Real.rpow r (σ + 14 * τ) * Real.rpow r (-2 * τ)
        > 390 * K * C * (Real.rpow C₁ σ * Real.rpow r (σ + 14 * τ)) := h7
      _ ≥ 390 * K * C * (Real.rpow W σ * ξ₀) := h5

  have h_denom_pos : 0 < 15 * K * Real.rpow W σ := by positivity
  have h_goal : Real.rpow r (σ + 12 * τ) / (15 * K * Real.rpow W σ) > 26 * C * ξ₀ := by
    have h9 : Real.rpow r (σ + 12 * τ) > 15 * K * Real.rpow W σ * (26 * C * ξ₀) := by
      have h10 : 15 * K * Real.rpow W σ * (26 * C * ξ₀) = 390 * K * C * (Real.rpow W σ * ξ₀) := by ring
      rw [h10]
      exact h4
    have h11 : Real.rpow r (σ + 12 * τ) / (15 * K * Real.rpow W σ) >
        (15 * K * Real.rpow W σ * (26 * C * ξ₀)) / (15 * K * Real.rpow W σ) := by
      apply div_lt_div_of_pos_right h9 h_denom_pos
    have h12 : (15 * K * Real.rpow W σ * (26 * C * ξ₀)) / (15 * K * Real.rpow W σ) = 26 * C * ξ₀ := by
      field_simp [h_denom_pos.ne'] <;> ring
    rw [h12] at h11
    exact h11
  calc
    (S.card : ℝ) * m ≥ Real.rpow r (σ + 12 * τ) / (15 * K * Real.rpow W σ) := h_main
    _ > 26 * C * ξ₀ := h_goal

end RadialBootstrapping
