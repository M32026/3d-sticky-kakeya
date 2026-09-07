module

/-
  ConcentratedParameterSelection.lean

  Parameter selection for the concentrated case with bounded support.

  With R_low = 1/2, R_high = 2 (automatic from mutual distance ≥ 1/2 and
  supports in closedBall(0,1)), shows that for sufficiently small r:
  - r ≤ 1/8
  - ∃ N > 0 with 4 + r ≤ r * 2^N
  - r^(σ+3τ) ≥ C*r + 792*N*r^(σ+4τ)  (logarithmic absorption)
  - r^τ * (floor(64π) + 1) * K * 2^σ ≤ 396  (parameter bound)

  Whiteprint node: concentrated-param-selection
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.OSWPrelude

@[expose] public section

set_option maxHeartbeats 500000

open MeasureTheory Metric Set
open scoped ENNReal NNReal

noncomputable section

namespace RadialBootstrapping
namespace ConcentratedParam

/-- The constant F = floor(64π) + 1 used in concentrated parameter selection. -/
def F_conc : ℕ := Nat.floor (16 * Real.pi * (2 : ℝ) / (1 / 2)) + 1

/-- Explicit threshold for the concentrated parameter selection.
This is the exact value constructed by `concentrated_param_selection_bounded`. -/
noncomputable def concentrated_r_conc (σ τ C K κ : ℝ) : ℝ :=
  let F : ℕ := F_conc
  let target_param : ℝ := 396 / ((F : ℝ) * K * (2 : ℝ)^σ)
  let target_param_strengthened : ℝ := 66 / ((F : ℝ) * K * (2 : ℝ)^σ)
  let target_2 : ℝ := 1 / (4 * C)
  let target_N : ℝ := (1 / 8 : ℝ) / (792 * (2 / (τ * Real.log 2) + 2 + Real.log 5 / Real.log 2))
  let A_card : ℝ := 2 * (1 - κ) / (τ * Real.log 2)
  let target_card1 : ℝ := (1 / 3168 : ℝ) / A_card
  let target_card2 : ℝ := 1 / 6336
  let target_count : ℝ := 1 / ((10^7 : ℝ) * K * C * (17 / 32 : ℝ)^σ)
  let target_log : ℝ := τ / 200
  let target_final : ℝ := 1 / (20 * C)
  let target_inner : ℝ := 1 / (18 * C)
  let r1 := Real.rpow target_param (1 / τ)
  let r10 := Real.rpow target_param_strengthened (1 / τ)
  let r2 := Real.rpow target_2 (1 / (1 - σ - 3 * τ))
  let r3 := Real.rpow target_N (1 / (τ / 2))
  let r4 := Real.rpow target_card1 (1 / (τ / 2))
  let r5 := Real.rpow target_card2 (1 / τ)
  let r6 := Real.rpow target_count (1 / (2 * τ))
  let r7 := Real.rpow target_log (1 / (τ / 2))
  let r8 := Real.rpow target_final (1 / τ)
  let r9 := Real.rpow target_inner (1 / (1 - σ - 3 * τ))
  min (1 / 8) (min r1 (min r10 (min r2 (min r3 (min r4 (min r5 (min r6 (min r7 (min r8 r9)))))))))

/-- Bound: for 0 < r ≤ 1 and β > 0, log(1/r) ≤ (1/β) * r^(-β).

    Proof: let x = 1/r ≥ 1. From log(x^β) ≤ x^β - 1, get β*log x ≤ x^β,
    so log x ≤ x^β/β = r^(-β)/β. -/
lemma log_bound {r β : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hβ : 0 < β) :
    Real.log (1 / r) ≤ (1 / β) * Real.rpow r (-β) := by
  set x : ℝ := 1 / r with hx_def
  have hx_pos : 0 < x := by positivity
  have hx1 : x ≥ 1 := by
    dsimp only [x]
    field_simp [hr.ne'] <;> linarith
  have h1 : Real.log (x ^ β) ≤ x ^ β - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log (x ^ β) = β * Real.log x := by
    rw [Real.log_rpow hx_pos] <;> ring
  have h3 : β * Real.log x ≤ x ^ β - 1 := by linarith
  have h4 : β * Real.log x ≤ x ^ β := by linarith
  have h5 : Real.log x ≤ (1 / β) * x ^ β := by
    calc Real.log x
      = (β * Real.log x) / β := by field_simp [hβ.ne'] <;> ring
    _ ≤ (x ^ β) / β := by gcongr
    _ = (1 / β) * x ^ β := by ring
  have h6 : x ^ β = Real.rpow r (-β) := by
    have h71 : x = Real.rpow r (-1) := by
      simp [x, Real.rpow_neg hr.le] <;> field_simp
    have h : (Real.rpow r (-1)) ^ β = Real.rpow r ((-1 : ℝ) * β) :=
      (Real.rpow_mul hr.le (-1) β).symm
    rw [h71, h]
    have h9 : (-1 : ℝ) * β = -β := by ring
    rw [h9]
  rw [h6] at h5
  exact h5

/-- Concentrated parameter selection: for sufficiently small r, all conditions hold.

    Uses R_low = 1/2, R_high = 2.
    Requires τ < (1-σ)/14 (so σ + 4τ < 1). -/
lemma concentrated_param_selection_bounded
    {σ τ C K κ : ℝ}
    (hσ_pos : 0 < σ) (hσ_lt_one : σ < 1)
    (hτ : 0 < τ) (hτ_small : τ < (1 - σ) / 14)
    (hκ : κ = 14 * τ / (1 - σ))
    (hC : 1 ≤ C) (hK : 1 ≤ K) :
    ∃ (r_conc : ℝ), 0 < r_conc ∧ r_conc = concentrated_r_conc σ τ C K κ ∧ ∀ (r : ℝ), 0 < r → r < r_conc →
      r ≤ 1 / 8 ∧
      ∃ (N : ℕ), 0 < N ∧
        2 * (2 : ℝ) + r ≤ r * (2 : ℝ)^N ∧
        Real.rpow r (σ + 3 * τ) ≥ C * r + 792 * (N : ℝ) * Real.rpow r (σ + 4 * τ) ∧
        Real.rpow r τ * (((Nat.floor (16 * Real.pi * (2 : ℝ) / (1 / 2)) + 1 : ℕ) : ℝ)) * K * (2 : ℝ)^σ ≤ 396 ∧
        Real.rpow r τ * (((Nat.floor (16 * Real.pi * (2 : ℝ) / (1 / 2)) + 1 : ℕ) : ℝ)) * K * (2 : ℝ)^σ ≤ 66 ∧
        (Nat.ceil ((1 - κ) * Real.log (1 / r) / Real.log 2) + 1 : ℝ) ≤
          (1 / 1584 : ℝ) * Real.rpow r (-τ) ∧
        Real.rpow r (-2 * τ) > (10^7 : ℝ) * K * C * Real.rpow ((2 + r) / 4) σ ∧
        Real.rpow r τ * Real.log (1 / r) ≤ (1 / 100 : ℝ) ∧
        20 * C * Real.rpow r τ < 1 ∧
        18 * C * r ≤ Real.rpow r (σ + 3 * τ) := by
  have h1mσ3τ_pos : 0 < 1 - σ - 3 * τ := by linarith
  have hστ4_lt_one : σ + 4 * τ < 1 := by linarith
  have hτ2_pos : 0 < τ / 2 := by linarith

  let F : ℕ := F_conc
  have hF_pos : 0 < F := by
    dsimp only [F, F_conc]
    exact Nat.succ_pos _
  have hF_le : (F : ℝ) ≤ 16 * Real.pi * 4 + 1 := by
    have h_pos : 0 ≤ 16 * Real.pi * (2 : ℝ) / (1 / 2) := by positivity
    have h1 : (Nat.floor (16 * Real.pi * (2 : ℝ) / (1 / 2)) : ℝ) ≤ 16 * Real.pi * (2 : ℝ) / (1 / 2) :=
      Nat.floor_le h_pos
    have hF_def : (F : ℝ) = (Nat.floor (16 * Real.pi * (2 : ℝ) / (1 / 2)) : ℝ) + 1 := by
      have h : F = F_conc := rfl
      rw [h]
      dsimp only [F_conc]
      <;> norm_cast
    rw [hF_def]
    have h3 : 16 * Real.pi * (2 : ℝ) / (1 / 2) = 16 * Real.pi * 4 := by ring
    linarith [h1, h3]

  -- Helper: explicit rpow bound
  have explicit_lt : ∀ (α C : ℝ), 0 < α → 0 < C →
      ∀ (r : ℝ), 0 < r → r < Real.rpow C (1 / α) → Real.rpow r α < C := by
    intro α C hα hC r hr hrlt
    have h1 : Real.rpow r α < Real.rpow (Real.rpow C (1 / α)) α :=
      Real.rpow_lt_rpow hr.le hrlt hα
    have h21 : Real.rpow (Real.rpow C (1 / α)) α = Real.rpow C ((1 / α) * α) :=
      (Real.rpow_mul hC.le (1 / α) α).symm
    have h3 : (1 / α) * α = 1 := by field_simp [hα.ne'] <;> ring
    have h2 : Real.rpow (Real.rpow C (1 / α)) α = C := by
      rw [h21, h3]
      simp
    rw [h2] at h1
    exact h1

  let target_param : ℝ := 396 / ((F : ℝ) * K * (2 : ℝ)^σ)
  have htarget_pos : 0 < target_param := by positivity

  -- Condition 1: r^τ < target_param
  let r1 := Real.rpow target_param (1 / τ)
  have hr1_pos : 0 < r1 := Real.rpow_pos_of_pos htarget_pos (1 / τ)
  have h1 : ∀ (r : ℝ), 0 < r → r < r1 → Real.rpow r τ < target_param :=
    explicit_lt τ target_param hτ htarget_pos

  -- Condition 1b (strengthened): r^τ < 66 / (F * K * 2^σ)
  let target_param_strengthened : ℝ := 66 / ((F : ℝ) * K * (2 : ℝ)^σ)
  have htarget_strengthened_pos : 0 < target_param_strengthened := by positivity
  let r10 := Real.rpow target_param_strengthened (1 / τ)
  have hr10_pos : 0 < r10 := Real.rpow_pos_of_pos htarget_strengthened_pos (1 / τ)
  have h10 : ∀ (r : ℝ), 0 < r → r < r10 → Real.rpow r τ < target_param_strengthened :=
    explicit_lt τ target_param_strengthened hτ htarget_strengthened_pos

  -- Condition 2: C * r^(1-σ-3τ) < 1/4
  let target_2 : ℝ := 1 / (4 * C)
  have htarget_2_pos : 0 < target_2 := by positivity
  let r2 := Real.rpow target_2 (1 / (1 - σ - 3 * τ))
  have hr2_pos : 0 < r2 := Real.rpow_pos_of_pos htarget_2_pos (1 / (1 - σ - 3 * τ))
  have h2 : ∀ (r : ℝ), 0 < r → r < r2 → Real.rpow r (1 - σ - 3 * τ) < target_2 :=
    explicit_lt (1 - σ - 3 * τ) target_2 h1mσ3τ_pos htarget_2_pos

  -- Condition 3: r^(τ/2) small enough for N bound
  let target_N : ℝ := (1 / 8 : ℝ) / (792 * (2 / (τ * Real.log 2) + 2 + Real.log 5 / Real.log 2))
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htarget_N_pos : 0 < target_N := by positivity
  let r3 := Real.rpow target_N (1 / (τ / 2))
  have hr3_pos : 0 < r3 := Real.rpow_pos_of_pos htarget_N_pos (1 / (τ / 2))
  have h3 : ∀ (r : ℝ), 0 < r → r < r3 → Real.rpow r (τ / 2) < target_N :=
    explicit_lt (τ / 2) target_N hτ2_pos htarget_N_pos

  have hκ_lt_one : κ < 1 := by
    rw [hκ]
    have h1 : 14 * τ < 1 - σ := by linarith
    have h2 : 0 < 1 - σ := by linarith [hσ_lt_one]
    have h3 : 14 * τ / (1 - σ) < (1 - σ) / (1 - σ) := by gcongr
    have h4 : (1 - σ) / (1 - σ) = 1 := by field_simp [h2.ne'] <;> ring
    rw [h4] at h3
    exact h3
  have h1mκ_pos : 0 < 1 - κ := by linarith

  -- Condition 4: card_strong: A * r^(τ/2) + 2 * r^τ ≤ 1/1584
  let A_card : ℝ := 2 * (1 - κ) / (τ * Real.log 2)
  have hA_card_pos : 0 < A_card := by positivity
  let target_card1 : ℝ := (1 / 3168 : ℝ) / A_card
  have htarget_card1_pos : 0 < target_card1 := by positivity
  let r4 := Real.rpow target_card1 (1 / (τ / 2))
  have hr4_pos : 0 < r4 := Real.rpow_pos_of_pos htarget_card1_pos (1 / (τ / 2))
  have h4 : ∀ (r : ℝ), 0 < r → r < r4 → Real.rpow r (τ / 2) < target_card1 :=
    explicit_lt (τ / 2) target_card1 hτ2_pos htarget_card1_pos
  let target_card2 : ℝ := 1 / 6336
  have htarget_card2_pos : 0 < target_card2 := by norm_num
  let r5 := Real.rpow target_card2 (1 / τ)
  have hr5_pos : 0 < r5 := Real.rpow_pos_of_pos htarget_card2_pos (1 / τ)
  have h5 : ∀ (r : ℝ), 0 < r → r < r5 → Real.rpow r τ < target_card2 :=
    explicit_lt τ target_card2 hτ htarget_card2_pos

  -- Condition 5: count_small: r^(-2τ) > (10^7 : ℝ) * K * C * (17/32)^σ
  let target_count : ℝ := 1 / ((10^7 : ℝ) * K * C * (17 / 32 : ℝ)^σ)
  have htarget_count_pos : 0 < target_count := by positivity
  have h2τ_pos : 0 < 2 * τ := by linarith
  let r6 := Real.rpow target_count (1 / (2 * τ))
  have hr6_pos : 0 < r6 := Real.rpow_pos_of_pos htarget_count_pos (1 / (2 * τ))
  have h6 : ∀ (r : ℝ), 0 < r → r < r6 → Real.rpow r (2 * τ) < target_count :=
    explicit_lt (2 * τ) target_count h2τ_pos htarget_count_pos

  -- Condition 6: h_r_log_small: r^τ * log(1/r) ≤ 1/100
  -- Using log(1/r) ≤ (2/τ) * r^(-τ/2), need (2/τ) * r^(τ/2) ≤ 1/100
  let target_log : ℝ := τ / 200
  have htarget_log_pos : 0 < target_log := by positivity
  let r7 := Real.rpow target_log (1 / (τ / 2))
  have hr7_pos : 0 < r7 := Real.rpow_pos_of_pos htarget_log_pos (1 / (τ / 2))
  have h7 : ∀ (r : ℝ), 0 < r → r < r7 → Real.rpow r (τ / 2) < target_log :=
    explicit_lt (τ / 2) target_log hτ2_pos htarget_log_pos

  -- Condition 7: h_r_final: 20 * C * r^τ < 1
  let target_final : ℝ := 1 / (20 * C)
  have htarget_final_pos : 0 < target_final := by positivity
  let r8 := Real.rpow target_final (1 / τ)
  have hr8_pos : 0 < r8 := Real.rpow_pos_of_pos htarget_final_pos (1 / τ)
  have h8 : ∀ (r : ℝ), 0 < r → r < r8 → Real.rpow r τ < target_final :=
    explicit_lt τ target_final hτ htarget_final_pos

  -- Condition 8: h_inner_cond: 18 * C * r ≤ r^(σ+3τ)
  -- Equivalent: r^(1-σ-3τ) ≤ 1/(18*C)
  have h1mσ3τ_pos' : 0 < 1 - σ - 3 * τ := h1mσ3τ_pos
  let target_inner : ℝ := 1 / (18 * C)
  have htarget_inner_pos : 0 < target_inner := by positivity
  let r9 := Real.rpow target_inner (1 / (1 - σ - 3 * τ))
  have hr9_pos : 0 < r9 := Real.rpow_pos_of_pos htarget_inner_pos (1 / (1 - σ - 3 * τ))
  have h9 : ∀ (r : ℝ), 0 < r → r < r9 → Real.rpow r (1 - σ - 3 * τ) < target_inner :=
    explicit_lt (1 - σ - 3 * τ) target_inner h1mσ3τ_pos' htarget_inner_pos

  let r_conc := min (1 / 8) (min r1 (min r10 (min r2 (min r3 (min r4 (min r5 (min r6 (min r7 (min r8 r9)))))))))
  have hr_conc_pos : 0 < r_conc := by
    have h1' : 0 < (1 / 8 : ℝ) := by norm_num
    exact lt_min h1' (lt_min hr1_pos (lt_min hr10_pos (lt_min hr2_pos (lt_min hr3_pos (lt_min hr4_pos (lt_min hr5_pos (lt_min hr6_pos (lt_min hr7_pos (lt_min hr8_pos hr9_pos)))))))))

  have hr_conc_eq : r_conc = concentrated_r_conc σ τ C K κ := by
    unfold concentrated_r_conc
    <;> rfl

  refine' ⟨r_conc, hr_conc_pos, hr_conc_eq, _⟩
  intro r hr hrlt

  have hle1 : r ≤ 1 / 8 := by
    have h : r_conc ≤ 1 / 8 := min_le_left _ _
    exact lt_of_lt_of_le hrlt h |>.le
  have hr1' : r ≤ 1 := by linarith
  have hlt_r1 : r < r1 := by
    have h : r_conc ≤ r1 := by
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    exact lt_of_lt_of_le hrlt h
  have hlt_r10 : r < r10 := by
    have h : r_conc ≤ r10 := by
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    exact lt_of_lt_of_le hrlt h
  have hlt_r2 : r < r2 := by
    have h : r_conc ≤ r2 := by
      dsimp only [r_conc]
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      exact min_le_left _ _
    exact lt_of_lt_of_le hrlt h
  have hlt_r3 : r < r3 := by
    have h : r_conc ≤ r3 := by
      dsimp only [r_conc]
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      exact min_le_left _ _
    exact lt_of_lt_of_le hrlt h
  have hlt_r4 : r < r4 := by
    have h : r_conc ≤ r4 := by
      dsimp only [r_conc]
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      exact min_le_left _ _
    exact lt_of_lt_of_le hrlt h
  have hlt_r5 : r < r5 := by
    have h : r_conc ≤ r5 := by
      dsimp only [r_conc]
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      exact min_le_left _ _
    exact lt_of_lt_of_le hrlt h
  have hlt_r6 : r < r6 := by
    have h : r_conc ≤ r6 := by
      dsimp only [r_conc]
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      exact min_le_left _ _
    exact lt_of_lt_of_le hrlt h
  have hlt_r7 : r < r7 := by
    have h : r_conc ≤ r7 := by
      dsimp only [r_conc]
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      exact min_le_left _ _
    exact lt_of_lt_of_le hrlt h
  have hlt_r8 : r < r8 := by
    have h : r_conc ≤ r8 := by
      dsimp only [r_conc]
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      exact min_le_left _ _
    exact lt_of_lt_of_le hrlt h
  have hlt_r9 : r < r9 := by
    have h : r_conc ≤ r9 := by
      dsimp only [r_conc]
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      apply le_trans (min_le_right _ _)
      exact min_le_right _ _
    exact lt_of_lt_of_le hrlt h

  -- h_param
  have h_rτ_lt : Real.rpow r τ < target_param := h1 r hr hlt_r1
  have h_param : Real.rpow r τ * (F : ℝ) * K * (2 : ℝ)^σ ≤ 396 := by
    have h_pos : 0 < (F : ℝ) * K * (2 : ℝ)^σ := by positivity
    have h_goal : Real.rpow r τ * ((F : ℝ) * K * (2 : ℝ)^σ) < 396 := by
      dsimp only [target_param] at h_rτ_lt
      calc Real.rpow r τ * ((F : ℝ) * K * (2 : ℝ)^σ)
        < (396 / ((F : ℝ) * K * (2 : ℝ)^σ)) * ((F : ℝ) * K * (2 : ℝ)^σ) := by gcongr
      _ = 396 := by
        field_simp [h_pos.ne'] <;> ring
    have h_assoc : Real.rpow r τ * (F : ℝ) * K * (2 : ℝ)^σ =
        Real.rpow r τ * ((F : ℝ) * K * (2 : ℝ)^σ) := by ring
    rw [h_assoc]
    exact h_goal.le

  -- h_param_strengthened
  have h_rτ_lt_strengthened : Real.rpow r τ < target_param_strengthened := h10 r hr hlt_r10
  have h_param_strengthened : Real.rpow r τ * (F : ℝ) * K * (2 : ℝ)^σ ≤ 66 := by
    have h_pos : 0 < (F : ℝ) * K * (2 : ℝ)^σ := by positivity
    have h_goal : Real.rpow r τ * ((F : ℝ) * K * (2 : ℝ)^σ) < 66 := by
      dsimp only [target_param_strengthened] at h_rτ_lt_strengthened
      calc Real.rpow r τ * ((F : ℝ) * K * (2 : ℝ)^σ)
        < (66 / ((F : ℝ) * K * (2 : ℝ)^σ)) * ((F : ℝ) * K * (2 : ℝ)^σ) := by gcongr
      _ = 66 := by
        field_simp [h_pos.ne'] <;> ring
    have h_assoc : Real.rpow r τ * (F : ℝ) * K * (2 : ℝ)^σ =
        Real.rpow r τ * ((F : ℝ) * K * (2 : ℝ)^σ) := by ring
    rw [h_assoc]
    exact h_goal.le

  -- Choose N = ceil(log2((4+r)/r)) + 1
  let b : ℝ := (4 + r) / r
  have hb_pos : 0 < b := by positivity
  let N : ℕ := Nat.ceil (Real.logb 2 b) + 1
  have hN_pos : 0 < N := by
    dsimp only [N]
    have h : 0 ≤ Nat.ceil (Real.logb 2 b) := Nat.zero_le _
    omega
  have hN_gt_logb : (N : ℝ) > Real.logb 2 b := by
    have h2 : (N : ℝ) = (Nat.ceil (Real.logb 2 b) : ℝ) + 1 := by
      simp [N] <;> norm_cast
    rw [h2]
    have h3 : (Nat.ceil (Real.logb 2 b) : ℝ) ≥ Real.logb 2 b := Nat.le_ceil _
    linarith
  have hR : 2 * (2 : ℝ) + r ≤ r * (2 : ℝ)^N := by
    have h4 : (2 : ℝ)^(Real.logb 2 b) = b := by
      have h41 : (2 : ℝ)^(Real.logb 2 b) = Real.exp (Real.log 2 * Real.logb 2 b) := by
        rw [Real.rpow_def_of_pos (by norm_num)]
      rw [h41]
      have h42 : Real.log 2 * Real.logb 2 b = Real.log b := by
        rw [Real.logb]
        <;> field_simp [hlog2_pos.ne'] <;> ring
      rw [h42]
      rw [Real.exp_log hb_pos]
    have h5 : (2 : ℝ)^(N : ℝ) > b := by
      have h6 : Real.logb 2 b < (N : ℝ) := hN_gt_logb
      have h7 : (2 : ℝ)^(Real.logb 2 b) < (2 : ℝ)^(N : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h6
      rw [h4] at h7
      exact h7
    have h5' : (2 : ℝ)^N > b := by exact_mod_cast h5
    have h9 : r * b < r * (2 : ℝ)^N := by gcongr <;> exact h5'
    have h_eq : r * b = 4 + r := by
      dsimp only [b]
      field_simp [hr.ne'] <;> ring
    rw [h_eq] at h9
    linarith
  have hN_le : (N : ℝ) ≤ Real.logb 2 b + 2 := by
    have h1 : (N : ℝ) = (Nat.ceil (Real.logb 2 b) : ℝ) + 1 := by
      simp [N] <;> norm_cast
    rw [h1]
    have h2 : (Nat.ceil (Real.logb 2 b) : ℝ) < Real.logb 2 b + 1 := by
      have h_nonneg : 0 ≤ Real.logb 2 b := by
        have h_big : b > 4 := by
          dsimp only [b]
          field_simp [hr.ne'] <;> linarith
        have h : Real.logb 2 b > Real.logb 2 4 := by
          apply Real.logb_lt_logb
          <;> norm_num <;> linarith
        have h4 : Real.logb 2 4 = 2 := by
          rw [Real.logb]
          have h5 : Real.log 4 = 2 * Real.log 2 := by
            rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)] <;> ring
          rw [h5] <;> field_simp [hlog2_pos.ne'] <;> ring
        linarith
      exact Nat.ceil_lt_add_one h_nonneg
    linarith
  have hb_le : b ≤ 5 / r := by
    dsimp only [b]
    field_simp [hr.ne'] <;> linarith
  have hlogb_le : Real.logb 2 b ≤ Real.logb 2 (5 / r) := by
    have h : Real.log b ≤ Real.log (5 / r) := Real.log_le_log hb_pos hb_le
    have hpos : 0 < Real.log 2 := hlog2_pos
    calc Real.logb 2 b
      = Real.log b / Real.log 2 := by rw [Real.logb] <;> ring
    _ ≤ Real.log (5 / r) / Real.log 2 := by gcongr
    _ = Real.logb 2 (5 / r) := by rw [Real.logb] <;> ring
  have hN_le2 : (N : ℝ) ≤ Real.logb 2 (5 / r) + 2 := by linarith

  -- Bound N * r^τ using log(1/r) ≤ (2/τ) * r^(-τ/2)
  have h_log_bound : Real.log (1 / r) ≤ (2 / τ) * Real.rpow r (-(τ / 2)) := by
    have h := log_bound hr hr1' hτ2_pos
    have h_eq : (1 : ℝ) / (τ / 2) = 2 / τ := by field_simp [hτ.ne'] <;> ring
    rw [h_eq] at h
    exact h
  have h_log2_eq : Real.logb 2 (5 / r) = (Real.log 5 + Real.log (1 / r)) / Real.log 2 := by
    rw [Real.logb]
    have h2 : Real.log (5 / r) = Real.log 5 + Real.log (1 / r) := by
      rw [← Real.log_mul (by norm_num) (by positivity)] <;> field_simp [hr.ne'] <;> ring
    rw [h2] <;> ring

  let C1 : ℝ := Real.log 5 / Real.log 2 + 2
  let C2 : ℝ := 2 / (τ * Real.log 2)
  let A : ℝ := C1 + C2
  have hA_pos : 0 < A := by positivity

  have hτ2_leτ : τ / 2 ≤ τ := by linarith [hτ]
  have h_rτ_le_rτ2 : Real.rpow r τ ≤ Real.rpow r (τ / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1' hτ2_leτ

  have h_mult : Real.rpow r (-(τ / 2)) * Real.rpow r τ = Real.rpow r (τ / 2) := by
    have h_eq : (-(τ / 2)) + τ = τ / 2 := by ring
    have h : Real.rpow r (-(τ / 2)) * Real.rpow r τ = Real.rpow r ((-(τ / 2)) + τ) :=
      (Real.rpow_add hr (-(τ / 2)) τ).symm
    rw [h, h_eq]

  have h_N_le : (N : ℝ) ≤ C1 + C2 * Real.rpow r (-(τ / 2)) := by
    have h1 : (N : ℝ) ≤ Real.logb 2 (5 / r) + 2 := hN_le2
    rw [h_log2_eq] at h1
    have h2 : (Real.log 5 + Real.log (1 / r)) / Real.log 2 + 2 ≤ C1 + C2 * Real.rpow r (-(τ / 2)) := by
      dsimp only [C1, C2]
      have h3 : Real.log (1 / r) ≤ (2 / τ) * Real.rpow r (-(τ / 2)) := h_log_bound
      have h4 : 0 < Real.log 2 := hlog2_pos
      calc (Real.log 5 + Real.log (1 / r)) / Real.log 2 + 2
        = Real.log 5 / Real.log 2 + Real.log (1 / r) / Real.log 2 + 2 := by ring
      _ ≤ Real.log 5 / Real.log 2 + ((2 / τ) * Real.rpow r (-(τ / 2))) / Real.log 2 + 2 := by gcongr
      _ = (Real.log 5 / Real.log 2 + 2) + (2 / (τ * Real.log 2)) * Real.rpow r (-(τ / 2)) := by ring
    linarith

  have h_N_rτ_bound : (N : ℝ) * Real.rpow r τ ≤ A * Real.rpow r (τ / 2) := by
    have h_step1 : (N : ℝ) * Real.rpow r τ ≤ (C1 + C2 * Real.rpow r (-(τ / 2))) * Real.rpow r τ :=
      mul_le_mul_of_nonneg_right h_N_le (Real.rpow_nonneg hr.le τ)
    calc (N : ℝ) * Real.rpow r τ
      ≤ (C1 + C2 * Real.rpow r (-(τ / 2))) * Real.rpow r τ := h_step1
    _ = C1 * Real.rpow r τ + C2 * (Real.rpow r (-(τ / 2)) * Real.rpow r τ) := by ring
    _ = C1 * Real.rpow r τ + C2 * Real.rpow r (τ / 2) := by rw [h_mult] <;> ring
    _ ≤ C1 * Real.rpow r (τ / 2) + C2 * Real.rpow r (τ / 2) := by gcongr
    _ = A * Real.rpow r (τ / 2) := by dsimp only [A] <;> ring

  have h_rτ2_small : Real.rpow r (τ / 2) < target_N := h3 r hr hlt_r3

  have h_N_rτ : 792 * (N : ℝ) * Real.rpow r τ < 1 / 4 := by
    have h5 : 792 * (N : ℝ) * Real.rpow r τ ≤ 792 * A * Real.rpow r (τ / 2) := by
      calc 792 * (N : ℝ) * Real.rpow r τ
        = 792 * ((N : ℝ) * Real.rpow r τ) := by ring
      _ ≤ 792 * (A * Real.rpow r (τ / 2)) := by gcongr
      _ = 792 * A * Real.rpow r (τ / 2) := by ring
    dsimp only [target_N] at h_rτ2_small
    have h6 : 792 * A * Real.rpow r (τ / 2) < 792 * A * target_N := by gcongr
    have h7 : 792 * A * target_N = 1 / 8 := by
      have hA_eq : A = 2 / (τ * Real.log 2) + 2 + Real.log 5 / Real.log 2 := by
        dsimp only [A, C1, C2] <;> ring
      simp only [target_N]
      rw [hA_eq]
      field_simp [hlog2_pos.ne', hτ.ne'] <;> ring
    rw [h7] at h6
    linarith

  -- h_log_absorb
  have h_C_small : C * Real.rpow r (1 - σ - 3 * τ) < 1 / 4 := by
    have h := h2 r hr hlt_r2
    have h' : C * Real.rpow r (1 - σ - 3 * τ) < C * (1 / (4 * C)) := by gcongr
    have h'' : C * (1 / (4 * C)) = 1 / 4 := by
      field_simp [(show (0 : ℝ) < C by linarith).ne'] <;> ring
    rw [h''] at h' <;> exact h'

  have h_absorb1 : C * r < Real.rpow r (σ + 3 * τ) / 2 := by
    have h_exp : Real.rpow r (σ + 3 * τ) = r * Real.rpow r (σ + 3 * τ - 1) := by
      have h := Real.rpow_add hr 1 (σ + 3 * τ - 1)
      have h_eq : (1 + (σ + 3 * τ - 1) : ℝ) = σ + 3 * τ := by ring
      rw [h_eq] at h
      simpa using h
    have h_pos2 : 0 < Real.rpow r (σ + 3 * τ - 1) := Real.rpow_pos_of_pos hr (σ + 3 * τ - 1)
    have h : C < Real.rpow r (σ + 3 * τ - 1) / 2 := by
      set x : ℝ := Real.rpow r (1 - σ - 3 * τ) with hx_def
      have hx_pos : 0 < x := Real.rpow_pos_of_pos hr (1 - σ - 3 * τ)
      have h1 : C * x < 1 / 4 := h_C_small
      have h2 : C < x⁻¹ / 4 := by
        calc C
          = (C * x) / x := by field_simp [hx_pos.ne'] <;> ring
        _ < (1 / 4 : ℝ) / x := by gcongr
        _ = x⁻¹ / 4 := by ring
      have h3 : x⁻¹ / 4 < x⁻¹ / 2 := by
        have h4 : 0 < x⁻¹ := by positivity
        linarith
      have h_inv : Real.rpow r (σ + 3 * τ - 1) = x⁻¹ := by
        have h_eq : σ + 3 * τ - 1 = -(1 - σ - 3 * τ) := by ring
        rw [h_eq]
        simpa [hx_def] using Real.rpow_neg hr.le (1 - σ - 3 * τ)
      rw [h_inv]
      exact lt_trans h2 h3
    have h9 : C * r < r * (Real.rpow r (σ + 3 * τ - 1) / 2) := by
      have h91 : C * r < (Real.rpow r (σ + 3 * τ - 1) / 2) * r := mul_lt_mul_of_pos_right h hr
      have h92 : (Real.rpow r (σ + 3 * τ - 1) / 2) * r = r * (Real.rpow r (σ + 3 * τ - 1) / 2) := by ring
      rw [h92] at h91
      exact h91
    have h10 : r * (Real.rpow r (σ + 3 * τ - 1) / 2) = Real.rpow r (σ + 3 * τ) / 2 := by
      have h11 : r * (Real.rpow r (σ + 3 * τ - 1) / 2) = (r * Real.rpow r (σ + 3 * τ - 1)) / 2 := by ring
      rw [h11, h_exp] <;> ring
    exact lt_of_lt_of_eq h9 h10

  have h_absorb2 : 792 * (N : ℝ) * Real.rpow r (σ + 4 * τ) < Real.rpow r (σ + 3 * τ) / 2 := by
    have h_exp : Real.rpow r (σ + 4 * τ) = Real.rpow r (σ + 3 * τ) * Real.rpow r τ := by
      have h : Real.rpow r ((σ + 3 * τ) + τ) = Real.rpow r (σ + 3 * τ) * Real.rpow r τ :=
        Real.rpow_add hr (σ + 3 * τ) τ
      have h_eq : σ + 4 * τ = (σ + 3 * τ) + τ := by ring
      rw [h_eq]
      exact h
    rw [h_exp]
    have h : 792 * (N : ℝ) * Real.rpow r τ < 1 / 2 := by linarith [h_N_rτ]
    have h_pos4 : 0 < Real.rpow r (σ + 3 * τ) := Real.rpow_pos_of_pos hr (σ + 3 * τ)
    calc 792 * (N : ℝ) * (Real.rpow r (σ + 3 * τ) * Real.rpow r τ)
      = (792 * (N : ℝ) * Real.rpow r τ) * Real.rpow r (σ + 3 * τ) := by ring
    _ < (1 / 2 : ℝ) * Real.rpow r (σ + 3 * τ) := by
      exact mul_lt_mul_of_pos_right h h_pos4
    _ = Real.rpow r (σ + 3 * τ) / 2 := by ring

  have h_log_absorb : Real.rpow r (σ + 3 * τ) ≥
      C * r + 792 * (N : ℝ) * Real.rpow r (σ + 4 * τ) := by
    have h_sum : C * r + 792 * (N : ℝ) * Real.rpow r (σ + 4 * τ) <
        Real.rpow r (σ + 3 * τ) / 2 + Real.rpow r (σ + 3 * τ) / 2 :=
      add_lt_add h_absorb1 h_absorb2
    have h_eq2 : Real.rpow r (σ + 3 * τ) / 2 + Real.rpow r (σ + 3 * τ) / 2 =
        Real.rpow r (σ + 3 * τ) := by ring
    rw [h_eq2] at h_sum
    exact h_sum.le

  -- h_card_strong
  have h_card1 : A_card * Real.rpow r (τ / 2) ≤ 1 / 3168 := by
    have h : Real.rpow r (τ / 2) < target_card1 := h4 r hr hlt_r4
    have h_eq : A_card * Real.rpow r (τ / 2) < A_card * target_card1 := by gcongr
    have h2 : A_card * target_card1 = 1 / 3168 := by
      dsimp only [target_card1]
      field_simp [hA_card_pos.ne'] <;> ring
    rw [h2] at h_eq
    exact h_eq.le
  have h_card2 : 2 * Real.rpow r τ ≤ 1 / 3168 := by
    have h : Real.rpow r τ < target_card2 := h5 r hr hlt_r5
    have h2 : 2 * Real.rpow r τ < 2 * target_card2 := by gcongr
    have h3 : 2 * target_card2 = 1 / 3168 := by
      dsimp only [target_card2] <;> norm_num
    rw [h3] at h2
    exact h2.le
  have h_log_bound2 : Real.log (1 / r) ≤ (2 / τ) * Real.rpow r (-(τ / 2)) := by
    have hlb : Real.log (1 / r) ≤ (1 / (τ / 2)) * Real.rpow r (-(τ / 2)) := log_bound hr hr1' hτ2_pos
    have h_eq : (1 / (τ / 2)) = (2 / τ) := by field_simp [hτ.ne'] <;> ring
    rw [h_eq] at hlb
    exact hlb
  have h_card_strong : (Nat.ceil ((1 - κ) * Real.log (1 / r) / Real.log 2) + 1 : ℝ) ≤
      (1 / 1584 : ℝ) * Real.rpow r (-τ) := by
    have h1mκ_pos : 0 < 1 - κ := by linarith
    have h_log1r_pos : 0 < Real.log (1 / r) := Real.log_pos (by
      have h3 : 1 < 1 / r := by
        have h4 : r < 1 := by linarith [hle1]
        have h5 : 0 < r := hr
        field_simp [h5.ne'] <;> linarith
      exact h3)
    have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    set x : ℝ := (1 - κ) * Real.log (1 / r) / Real.log 2 with hx_def
    have hx_pos : 0 < x := by positivity
    have h1 : x ≤ A_card * Real.rpow r (-(τ / 2)) := by
      calc x
        = (1 - κ) * Real.log (1 / r) / Real.log 2 := by rfl
      _ ≤ (1 - κ) * ((2 / τ) * Real.rpow r (-(τ / 2))) / Real.log 2 := by gcongr
      _ = A_card * Real.rpow r (-(τ / 2)) := by
        dsimp only [A_card] <;> ring
    have h_n_pos : 0 < Nat.ceil x := by
      have h1 : 1 ≤ Nat.ceil x := Nat.one_le_ceil_iff.mpr hx_pos
      omega
    let n : ℕ := Nat.ceil x - 1
    have h21 : n < Nat.ceil x := by dsimp only [n] <;> omega
    have h22 : (n : ℝ) < x := (Nat.lt_ceil).mp h21
    have h23 : (n : ℝ) = (Nat.ceil x : ℝ) - 1 := by
      dsimp only [n]
      have h24 : ((Nat.ceil x - 1 : ℕ) : ℝ) = (Nat.ceil x : ℝ) - 1 := by exact Nat.cast_pred h_n_pos
      exact h24
    have h2 : (Nat.ceil x : ℝ) ≤ x + 1 := by
      rw [h23] at h22
      linarith
    have h3 : (Nat.ceil x + 1 : ℝ) ≤ A_card * Real.rpow r (-(τ / 2)) + 2 := by
      have h31 : (Nat.ceil x : ℝ) ≤ x + 1 := h2
      have h32 : x ≤ A_card * Real.rpow r (-(τ / 2)) := h1
      linarith
    have h_pos1 : 0 < Real.rpow r (τ / 2) := Real.rpow_pos_of_pos hr (τ / 2)
    have h_pos2 : 0 < Real.rpow r τ := Real.rpow_pos_of_pos hr τ
    have h4 : A_card * Real.rpow r (-(τ / 2)) + 2 ≤ (1 / 1584 : ℝ) * Real.rpow r (-τ) := by
      have h_posτ : 0 < Real.rpow r τ := Real.rpow_pos_of_pos hr τ
      have h_eq_left : (A_card * Real.rpow r (-(τ / 2)) + 2) * Real.rpow r τ =
          A_card * Real.rpow r (τ / 2) + 2 * Real.rpow r τ := by
        rw [add_mul]
        have h1 : A_card * Real.rpow r (-(τ / 2)) * Real.rpow r τ = A_card * Real.rpow r (τ / 2) := by
          have h_exp : Real.rpow r (-(τ / 2)) * Real.rpow r τ = Real.rpow r (τ / 2) := by
            have h : Real.rpow r ((-(τ / 2)) + τ) = Real.rpow r (-(τ / 2)) * Real.rpow r τ := Real.rpow_add hr (-(τ / 2)) τ
            have h_eq2 : (-(τ / 2)) + τ = τ / 2 := by ring
            rw [h_eq2] at h
            exact h.symm
          rw [mul_assoc A_card, h_exp] <;> ring
        rw [h1] <;> ring
      have h_eq_right : ((1 / 1584 : ℝ) * Real.rpow r (-τ)) * Real.rpow r τ = 1 / 1584 := by
        have h_exp : Real.rpow r (-τ) * Real.rpow r τ = 1 := by
          have h : Real.rpow r ((-τ) + τ) = Real.rpow r (-τ) * Real.rpow r τ := Real.rpow_add hr (-τ) τ
          have h_eq2 : (-τ) + τ = 0 := by ring
          rw [h_eq2] at h
          have h' : Real.rpow r 0 = 1 := by simp
          rw [h'] at h
          exact h.symm
        rw [mul_assoc (1 / 1584 : ℝ), h_exp] <;> ring
      have h_le : (A_card * Real.rpow r (-(τ / 2)) + 2) * Real.rpow r τ ≤
          ((1 / 1584 : ℝ) * Real.rpow r (-τ)) * Real.rpow r τ := by
        rw [h_eq_left, h_eq_right]
        linarith [h_card1, h_card2]
      exact le_of_mul_le_mul_right h_le h_posτ
    have h5 : (Nat.ceil ((1 - κ) * Real.log (1 / r) / Real.log 2) + 1 : ℝ) =
        (Nat.ceil x + 1 : ℝ) := by
      simp [hx_def]
    rw [h5]
    exact le_trans h3 h4

  -- h_count_small
  have h_count_small : Real.rpow r (-2 * τ) > (10^7 : ℝ) * K * C * Real.rpow ((2 + r) / 4) σ := by
    have h1 : (2 + r) / 4 ≤ 17 / 32 := by linarith
    have h2 : 0 < (2 + r) / 4 := by linarith
    have h3 : Real.rpow ((2 + r) / 4) σ ≤ Real.rpow (17 / 32 : ℝ) σ :=
      Real.rpow_le_rpow (by linarith) h1 (by linarith [hσ_pos])
    have h4 : Real.rpow r (2 * τ) < target_count := h6 r hr hlt_r6
    have h5 : Real.rpow r (-2 * τ) = (Real.rpow r (2 * τ))⁻¹ := by
      have h_eq : -2 * τ = -(2 * τ) := by ring
      rw [h_eq]
      exact Real.rpow_neg hr.le (2 * τ)
    rw [h5]
    have h6' : (Real.rpow r (2 * τ))⁻¹ > (target_count)⁻¹ := by
      have h_pos1 : 0 < Real.rpow r (2 * τ) := Real.rpow_pos_of_pos hr (2 * τ)
      have h_pos2 : 0 < target_count := htarget_count_pos
      have h4' : Real.rpow r (2 * τ) < target_count := h4
      have h : (target_count)⁻¹ < (Real.rpow r (2 * τ))⁻¹ := by
        gcongr
      exact h
    have h7 : (target_count)⁻¹ = (10^7 : ℝ) * K * C * Real.rpow (17 / 32 : ℝ) σ := by
      dsimp only [target_count]
      have h_rpow_pos : 0 < Real.rpow (17 / 32 : ℝ) σ := Real.rpow_pos_of_pos (by norm_num) σ
      have h_all_pos : 0 < (10^7 : ℝ) * K * C * Real.rpow (17 / 32 : ℝ) σ := by
        have hK_pos : 0 < K := by linarith
        have hC_pos : 0 < C := by linarith
        positivity
      have h9 : (1 / ((10^7 : ℝ) * K * C * Real.rpow (17 / 32 : ℝ) σ))⁻¹ = (10^7 : ℝ) * K * C * Real.rpow (17 / 32 : ℝ) σ := by
        field_simp [h_all_pos.ne'] <;> ring
      exact h9
    rw [h7] at h6'
    have h8 : (10^7 : ℝ) * K * C * Real.rpow (17 / 32 : ℝ) σ ≥ (10^7 : ℝ) * K * C * Real.rpow ((2 + r) / 4) σ := by
      gcongr
      <;> exact h3
    calc (Real.rpow r (2 * τ))⁻¹
      > (10^7 : ℝ) * K * C * Real.rpow (17 / 32 : ℝ) σ := h6'
    _ ≥ (10^7 : ℝ) * K * C * Real.rpow ((2 + r) / 4) σ := h8

  -- h_r_log_small: r^τ * log(1/r) ≤ 1/100
  have h_r_log_small : Real.rpow r τ * Real.log (1 / r) ≤ (1 / 100 : ℝ) := by
    have hlb : Real.log (1 / r) ≤ (2 / τ) * Real.rpow r (-(τ / 2)) := h_log_bound
    have h_pos : 0 ≤ Real.rpow r τ := Real.rpow_nonneg hr.le τ
    have h1 : Real.rpow r τ * Real.log (1 / r) ≤ Real.rpow r τ * ((2 / τ) * Real.rpow r (-(τ / 2))) := by
      gcongr
    have h_exp : Real.rpow r τ * Real.rpow r (-(τ / 2)) = Real.rpow r (τ / 2) := by
      have h : Real.rpow r (τ + (-(τ / 2))) = Real.rpow r τ * Real.rpow r (-(τ / 2)) := Real.rpow_add hr τ (-(τ / 2))
      have h_eq : τ + (-(τ / 2)) = τ / 2 := by ring
      rw [h_eq] at h
      exact h.symm
    have h2 : Real.rpow r τ * ((2 / τ) * Real.rpow r (-(τ / 2))) = (2 / τ) * Real.rpow r (τ / 2) := by
      have h_comm : Real.rpow r τ * ((2 / τ) * Real.rpow r (-(τ / 2))) = (2 / τ) * (Real.rpow r τ * Real.rpow r (-(τ / 2))) := by ring
      rw [h_comm, h_exp] <;> ring
    rw [h2] at h1
    have h3 : (2 / τ) * Real.rpow r (τ / 2) ≤ (1 / 100 : ℝ) := by
      have h4 : Real.rpow r (τ / 2) < target_log := h7 r hr hlt_r7
      have h5 : (2 / τ) * Real.rpow r (τ / 2) < (2 / τ) * target_log := by gcongr
      have h6 : (2 / τ) * target_log = (1 / 100 : ℝ) := by
        dsimp only [target_log]
        field_simp [hτ.ne'] <;> ring
      rw [h6] at h5
      exact h5.le
    exact le_trans h1 h3

  -- h_r_final: 20 * C * r^τ < 1
  have h_r_final : 20 * C * Real.rpow r τ < 1 := by
    have h1 : Real.rpow r τ < target_final := h8 r hr hlt_r8
    have h2 : 20 * C * Real.rpow r τ < 20 * C * target_final := by gcongr
    have h3 : 20 * C * target_final = 1 := by
      dsimp only [target_final]
      field_simp [(show (0 : ℝ) < C by linarith).ne'] <;> ring
    rw [h3] at h2
    exact h2

  -- h_inner_cond: 18 * C * r ≤ r^(σ+3τ)
  have h_inner_cond : 18 * C * r ≤ Real.rpow r (σ + 3 * τ) := by
    have h1 : Real.rpow r (1 - σ - 3 * τ) < target_inner := h9 r hr hlt_r9
    have h_pos : 0 < Real.rpow r (σ + 3 * τ) := Real.rpow_pos_of_pos hr (σ + 3 * τ)
    have h2 : 18 * C * Real.rpow r (1 - σ - 3 * τ) < 1 := by
      have h3 : 18 * C * Real.rpow r (1 - σ - 3 * τ) < 18 * C * target_inner := by gcongr
      have h4 : 18 * C * target_inner = 1 := by
        dsimp only [target_inner]
        field_simp [(show (0 : ℝ) < C by linarith).ne'] <;> ring
      rw [h4] at h3
      exact h3
    have h5 : Real.rpow r (1 - σ - 3 * τ) * Real.rpow r (σ + 3 * τ) = r := by
      have h_exp : Real.rpow r ((1 - σ - 3 * τ) + (σ + 3 * τ)) = Real.rpow r (1 - σ - 3 * τ) * Real.rpow r (σ + 3 * τ) := Real.rpow_add hr (1 - σ - 3 * τ) (σ + 3 * τ)
      have h_eq : (1 - σ - 3 * τ) + (σ + 3 * τ) = 1 := by ring
      rw [h_eq] at h_exp
      have h6 : Real.rpow r 1 = r := by simp
      rw [h6] at h_exp
      exact h_exp.symm
    have h7 : 18 * C * r ≤ Real.rpow r (σ + 3 * τ) := by
      calc 18 * C * r
        = 18 * C * (Real.rpow r (1 - σ - 3 * τ) * Real.rpow r (σ + 3 * τ)) := by rw [h5]
      _ = (18 * C * Real.rpow r (1 - σ - 3 * τ)) * Real.rpow r (σ + 3 * τ) := by ring
      _ ≤ (1 : ℝ) * Real.rpow r (σ + 3 * τ) := by gcongr <;> linarith
      _ = Real.rpow r (σ + 3 * τ) := by ring
    exact h7

  exact ⟨hle1, N, hN_pos, hR, h_log_absorb, h_param, h_param_strengthened, h_card_strong, h_count_small, h_r_log_small, h_r_final, h_inner_cond⟩

end ConcentratedParam
end RadialBootstrapping

end
