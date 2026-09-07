import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Tactic

/-!
# LOW case AD via trivial diameter bound

When `ρ ≥ 48L²` (LOW case), the AD bound follows from a trivial
diameter-based covering argument.

The projection `E` has diameter ≤ 2√ρ, so it is contained in an interval
of length 2√ρ. A trivial covering gives `covering ≤ 2√ρ/ρ' + 2`.
With `C = 1/L`, `L ≤ 1/10000`, and `ρ ≥ 48L²`:
`2√ρ/ρ' + 2 ≤ 2/√ρ + 2 ≤ 2/(√48·L) + 2 < 1/L ≤ C·(r/ρ')^(1-σ)`.

## Main result

`low_case_trivial_ad`: `IsADSet1 E ρ (1-σ) (1/L)` when `ρ ≥ 48L²`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Metric Set ENNReal Real

attribute [local instance] Classical.propDecidable

/-- Any `S ⊆ Icc a b` has covering number at most `(b-a)/ε + 2`. -/
lemma covering_by_interval {S : Set ℝ} {ε a b : ℝ} (hε : 0 < ε)
    (hS : S ⊆ Set.Icc a b) (hle : a ≤ b) :
    (Metric.externalCoveringNumber (⟨ε, hε.le⟩ : NNReal) S : ENNReal) ≤
      ENNReal.ofReal ((b - a) / ε + 2) := by
  let n : ℕ := Nat.ceil ((b - a) / ε)
  let centers : Finset ℝ := Finset.image (fun k : ℕ => a + (k : ℝ) * ε) (Finset.range (n + 1))
  have hn : (n : ℝ) ≥ (b - a) / ε := Nat.le_ceil _
  have hcover : ∀ (x : ℝ), x ∈ Set.Icc a b → ∃ (c : ℝ), c ∈ centers ∧ |x - c| ≤ ε := by
    intro x hx
    have hxa : a ≤ x := hx.1
    have hxb : x ≤ b := hx.2
    have h_nonneg : 0 ≤ (x - a) / ε := by
      apply div_nonneg
      · linarith
      · linarith
    set k : ℕ := Nat.floor ((x - a) / ε) with hk_def
    have hk1 : (k : ℝ) ≤ (x - a) / ε := Nat.floor_le (a := (x - a) / ε) h_nonneg
    have hk2 : (x - a) / ε < (k : ℝ) + 1 := Nat.lt_floor_add_one ((x - a) / ε)
    have h_k_lt : (k : ℝ) < (n : ℝ) + 1 := by
      have h1 : (k : ℝ) < (x - a) / ε + 1 := by linarith
      have h2 : (x - a) / ε ≤ (b - a) / ε := by
        apply div_le_div_of_nonneg_right
        · linarith
        · linarith
      have h3 : (x - a) / ε + 1 ≤ (b - a) / ε + 1 := by linarith
      have h4 : (b - a) / ε + 1 ≤ (n : ℝ) + 1 := by
        have h5 : (b - a) / ε ≤ (n : ℝ) := hn
        linarith
      linarith
    have hk_lt_n : k < n + 1 := by exact_mod_cast h_k_lt
    have hk_in : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr hk_lt_n
    set c : ℝ := a + (k : ℝ) * ε with hc_def
    have hc_in : c ∈ centers := Finset.mem_image.mpr ⟨k, hk_in, rfl⟩
    have h1 : (k : ℝ) * ε ≤ x - a := by
      have h11 : (k : ℝ) ≤ (x - a) / ε := hk1
      have h : (k : ℝ) * ε ≤ ((x - a) / ε) * ε := by
        exact mul_le_mul_of_nonneg_right h11 (by linarith)
      have h2 : ((x - a) / ε) * ε = x - a := by
        field_simp [hε.ne']
      rw [h2] at h
      exact h
    have h2 : x - a < ((k : ℝ) + 1) * ε := by
      have h21 : (x - a) / ε < (k : ℝ) + 1 := hk2
      have h : ((x - a) / ε) * ε < ((k : ℝ) + 1) * ε := by
        exact mul_lt_mul_of_pos_right h21 hε
      have h3 : ((x - a) / ε) * ε = x - a := by
        field_simp [hε.ne']
      rw [h3] at h
      exact h
    have hdist : |x - c| ≤ ε := by
      rw [hc_def]
      rw [abs_le]
      constructor <;> linarith
    exact ⟨c, hc_in, hdist⟩
  let centersSet : Set ℝ := (centers : Set ℝ)
  let eps : NNReal := ⟨ε, hε.le⟩
  have hC : Metric.IsCover eps S centersSet := by
    intro x hx
    have h_x_in_Icc : x ∈ Set.Icc a b := hS hx
    rcases hcover x h_x_in_Icc with ⟨c, hc_in, hdist⟩
    refine ⟨c, hc_in, ?_⟩
    have h_dist : dist x c ≤ ε := by simpa [dist_eq_norm] using hdist
    have h_edist : edist x c ≤ (eps : ENNReal) := by
      rw [edist_dist]
      exact_mod_cast h_dist
    exact h_edist
  have h_main : Metric.externalCoveringNumber eps S ≤ centersSet.encard :=
    Metric.IsCover.externalCoveringNumber_le_encard hC
  have h_card : centers.card ≤ n + 1 := by
    have h1 : centers.card ≤ (Finset.range (n + 1)).card := Finset.card_image_le
    simpa using h1
  have h_real : (centers.card : ℝ) ≤ (b - a) / ε + 2 := by
    have h' : (centers.card : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast h_card
    have h'' : (n : ℝ) < (b - a) / ε + 1 := Nat.ceil_lt_add_one (show 0 ≤ (b - a) / ε by positivity)
    linarith
  have h_main_coe : (Metric.externalCoveringNumber eps S : ENNReal) ≤ (centersSet.encard : ENNReal) := by
    exact_mod_cast h_main
  have h_encard_coe : (centersSet.encard : ENNReal) = (centers.card : ENNReal) := by
    simp [centersSet]
  have h_final : (centers.card : ENNReal) ≤ ENNReal.ofReal ((b - a) / ε + 2) := by
    have h_eq : (centers.card : ENNReal) = ENNReal.ofReal (centers.card : ℝ) := by simp
    rw [h_eq]
    exact ENNReal.ofReal_le_ofReal h_real
  rw [h_encard_coe] at h_main_coe
  exact h_main_coe.trans h_final

/-- **LOW case AD**: trivial diameter bound proves `IsADSet1`. -/
lemma low_case_trivial_ad
    {sigma rho L : ℝ}
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hL_pos : 0 < L)
    (hL_small : L ≤ 1 / 10000)
    (hrho_pos : 0 < rho)
    (hrho_low : 48 * L^2 ≤ rho)
    (E : Set ℝ)
    (hE_sub : E ⊆ Set.Icc (-4 : ℝ) 4)
    (hE_center : ∃ (c : ℝ), E ⊆ Set.Icc (c - Real.sqrt rho) (c + Real.sqrt rho)) :
    IsADSet1 E rho (1 - sigma) (Kakeya.realRpowENN L (-1)) := by
  rcases hE_center with ⟨c, hE_center⟩
  have h1_pos : 0 < 1 - sigma := by linarith
  have hsqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho_pos
  have hsqrt48_pos : 0 < Real.sqrt 48 := by positivity
  have h_rho_sqrt : Real.sqrt rho ≥ Real.sqrt 48 * L := by
    have h : 48 * L^2 ≤ rho := hrho_low
    have h' : Real.sqrt (48 * L^2) ≤ Real.sqrt rho := Real.sqrt_le_sqrt h
    have h'' : Real.sqrt (48 * L^2) = Real.sqrt 48 * L := by
      calc
        Real.sqrt (48 * L^2) = Real.sqrt 48 * Real.sqrt (L^2) := by
          rw [Real.sqrt_mul]; positivity
        _ = Real.sqrt 48 * L := by rw [Real.sqrt_sq hL_pos.le]
    rw [h''] at h'
    exact h'
  have h4 : 2 * L < 1 - 2 / Real.sqrt 48 := by
    have h5 : 2 / Real.sqrt 48 < 1 / 2 := by
      have h7 : Real.sqrt 48 > 4 := by
        nlinarith [Real.sqrt_nonneg 48, Real.sq_sqrt (show (0 : ℝ) ≤ 48 by norm_num)]
      calc 2 / Real.sqrt 48 < 2 / 4 := by gcongr
           _ = 1 / 2 := by norm_num
    have h6 : 2 * L ≤ 1 / 5000 := by
      have h7 : L ≤ 1 / 10000 := hL_small
      linarith
    linarith
  have h10 : (2 / Real.sqrt 48) + 2 * L ≤ 1 := by linarith [h4]
  have h_key_real : 2 / (Real.sqrt 48 * L) + 2 ≤ 1 / L := by
    have h8 : 2 / (Real.sqrt 48 * L) + 2 = ((2 / Real.sqrt 48) + 2 * L) / L := by
      field_simp [hL_pos.ne']
    rw [h8]
    apply div_le_div_of_nonneg_right h10
    exact hL_pos.le
  have h_rpow_L : L.rpow (-1) = 1 / L := by
    have h1 : L.rpow (-1) = (L.rpow 1)⁻¹ := by
      apply Real.rpow_neg
      exact hL_pos.le
    rw [h1]
    have h2 : L.rpow 1 = L := by simp
    rw [h2]
    field_simp [hL_pos.ne']
  have hC_one : (1 : ENNReal) ≤ Kakeya.realRpowENN L (-1) := by
    have h : (1 : ℝ) ≤ 1 / L := by
      have h9 : L ≤ 1 / 10000 := hL_small
      have h10 : 0 < L := hL_pos
      have h11 : 1 / L ≥ 10000 := by
        calc 1 / L ≥ 1 / (1 / 10000 : ℝ) := by gcongr
             _ = 10000 := by norm_num
      linarith
    have h' : Kakeya.realRpowENN L (-1) = ENNReal.ofReal (1 / L) := by
      have h_def : Kakeya.realRpowENN L (-1) = ENNReal.ofReal (L.rpow (-1)) := by
        simp [Kakeya.realRpowENN]
      rw [h_def, h_rpow_L]
    rw [h']
    have h_ennreal : (1 : ENNReal) ≤ ENNReal.ofReal (1 / L) := by
      have h1 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (1 / L) := ENNReal.ofReal_le_ofReal h
      have h2 : ENNReal.ofReal (1 : ℝ) = (1 : ENNReal) := by simp
      rw [h2] at h1
      exact h1
    exact h_ennreal
  refine' ⟨by linarith, h1_pos, by linarith, hC_one, hE_sub, _⟩
  intro rho' hrho' hrho_ge_rho hrho'_le_one x r hr_le_r hr_le_one
  have hrho'_pos : 0 < rho' := by linarith
  have h_ab : c - Real.sqrt rho ≤ c + Real.sqrt rho := by linarith [hsqrt_pos]
  have h_set : E ∩ Metric.closedBall x r ⊆ Set.Icc (c - Real.sqrt rho) (c + Real.sqrt rho) := by
    intro y hy
    exact hE_center hy.1
  have h_len : (c + Real.sqrt rho) - (c - Real.sqrt rho) = 2 * Real.sqrt rho := by ring
  have h_cover : (Metric.externalCoveringNumber (⟨rho', hrho'_pos.le⟩ : NNReal)
      (E ∩ Metric.closedBall x r) : ENNReal) ≤
      ENNReal.ofReal (2 * Real.sqrt rho / rho' + 2) := by
    have h1 := covering_by_interval hrho'_pos h_set h_ab
    rw [h_len] at h1
    exact h1
  have h_real_ineq : 2 * Real.sqrt rho / rho' + 2 ≤ (1 / L) * (r / rho') ^ (1 - sigma) := by
    have h3 : 2 * Real.sqrt rho / rho' + 2 ≤ 2 / Real.sqrt rho + 2 := by
      have h4 : rho' ≥ rho := hrho_ge_rho
      have h5 : 2 * Real.sqrt rho / rho' ≤ 2 * Real.sqrt rho / rho := by
        have h_a_nonneg : 0 ≤ 2 * Real.sqrt rho := by positivity
        have h : (2 * Real.sqrt rho) / rho' - (2 * Real.sqrt rho) / rho ≤ 0 := by
          have h2 : (2 * Real.sqrt rho) / rho' - (2 * Real.sqrt rho) / rho =
              (2 * Real.sqrt rho) * (rho - rho') / (rho * rho') := by
            field_simp [hrho_pos.ne', hrho'_pos.ne']
          rw [h2]
          have h3 : (2 * Real.sqrt rho) * (rho - rho') ≤ 0 := by
            have h4 : rho - rho' ≤ 0 := by linarith
            nlinarith [Real.sqrt_nonneg rho]
          have h5 : 0 < rho * rho' := by positivity
          exact div_nonpos_of_nonpos_of_nonneg h3 (by positivity)
        linarith
      have h6 : 2 * Real.sqrt rho / rho = 2 / Real.sqrt rho := by
        have hsqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho_pos
        have hsq : (Real.sqrt rho)^2 = rho := Real.sq_sqrt (by linarith)
        have h_div : Real.sqrt rho / rho = 1 / Real.sqrt rho := by
          have h' : Real.sqrt rho / rho = Real.sqrt rho / (Real.sqrt rho)^2 := by
            apply congr_arg (fun x : ℝ => Real.sqrt rho / x) hsq.symm
          rw [h']
          field_simp [hsqrt_pos.ne']
        have h : 2 * Real.sqrt rho / rho = 2 * (Real.sqrt rho / rho) := by ring
        rw [h, h_div]
        ring
      rw [h6] at h5
      linarith
    have h7 : 2 / Real.sqrt rho + 2 ≤ 2 / (Real.sqrt 48 * L) + 2 := by
      have h8 : 2 / Real.sqrt rho ≤ 2 / (Real.sqrt 48 * L) := by
        gcongr
      linarith
    have h9 : 2 / (Real.sqrt 48 * L) + 2 ≤ 1 / L := h_key_real
    have h11 : 1 ≤ r / rho' := by
      have h12 : rho' ≤ r := hr_le_r
      have h13 : 0 < rho' := hrho'_pos
      have h14 : rho' / rho' ≤ r / rho' := by gcongr
      have h15 : rho' / rho' = 1 := by field_simp [h13.ne']
      rw [h15] at h14
      exact h14
    have h12 : (1 : ℝ) ≤ (r / rho') ^ (1 - sigma) := by
      exact one_le_rpow h11 (by linarith)
    have h13 : 1 / L ≤ (1 / L) * (r / rho') ^ (1 - sigma) := by
      have h14 : 0 ≤ 1 / L := by positivity
      nlinarith
    calc
      2 * Real.sqrt rho / rho' + 2 ≤ 2 / Real.sqrt rho + 2 := h3
      _ ≤ 2 / (Real.sqrt 48 * L) + 2 := h7
      _ ≤ 1 / L := h9
      _ ≤ (1 / L) * (r / rho') ^ (1 - sigma) := h13
  have h_rpow_r : Kakeya.realRpowENN (r / rho') (1 - sigma) =
      ENNReal.ofReal ((r / rho') ^ (1 - sigma)) := by
    simp only [Kakeya.realRpowENN]
    rfl
  have h_rpow_L' : Kakeya.realRpowENN L (-1) = ENNReal.ofReal (1 / L) := by
    simp only [Kakeya.realRpowENN]
    <;> rw [h_rpow_L]
    <;> rfl
  have h_enreal_ineq : ENNReal.ofReal (2 * Real.sqrt rho / rho' + 2) ≤
      Kakeya.realRpowENN L (-1) * Kakeya.realRpowENN (r / rho') (1 - sigma) := by
    rw [h_rpow_L', h_rpow_r]
    have h_nonneg1 : 0 ≤ 1 / L := by positivity
    rw [← ENNReal.ofReal_mul h_nonneg1]
    exact ENNReal.ofReal_le_ofReal h_real_ineq
  exact h_cover.trans h_enreal_ineq

/-- **Improved LOW case AD**: `IsADSet1 E ρ (1-σ) (1/L)` when `ρ ≥ 5L²`.

Same proof as `low_case_trivial_ad` but with constant 5 instead of 48,
using `2/√5 + 2L ≤ 1` for `L ≤ 1/10000`. -/
lemma low_case_trivial_ad_v2
    {sigma rho L : ℝ}
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hL_pos : 0 < L)
    (hL_small : L ≤ 1 / 10000)
    (hrho_pos : 0 < rho)
    (hrho_low : 5 * L^2 ≤ rho)
    (E : Set ℝ)
    (hE_sub : E ⊆ Set.Icc (-4 : ℝ) 4)
    (hE_center : ∃ (c : ℝ), E ⊆ Set.Icc (c - Real.sqrt rho) (c + Real.sqrt rho)) :
    IsADSet1 E rho (1 - sigma) (Kakeya.realRpowENN L (-1)) := by
  rcases hE_center with ⟨c, hE_center⟩
  have h1_pos : 0 < 1 - sigma := by linarith
  have hsqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho_pos
  have hsqrt5_pos : 0 < Real.sqrt 5 := by positivity
  have h_rho_sqrt : Real.sqrt rho ≥ Real.sqrt 5 * L := by
    have h : 5 * L^2 ≤ rho := hrho_low
    have h' : Real.sqrt (5 * L^2) ≤ Real.sqrt rho := Real.sqrt_le_sqrt h
    have h'' : Real.sqrt (5 * L^2) = Real.sqrt 5 * L := by
      calc
        Real.sqrt (5 * L^2) = Real.sqrt 5 * Real.sqrt (L^2) := by
          rw [Real.sqrt_mul] <;> positivity
        _ = Real.sqrt 5 * L := by rw [Real.sqrt_sq hL_pos.le]
    rw [h''] at h'
    exact h'
  have h10 : (2 / Real.sqrt 5) + 2 * L ≤ 1 := by
    have h1 : (2 : ℝ) / Real.sqrt 5 ≤ 9 / 10 := by
      have h2 : (0 : ℝ) < Real.sqrt 5 := by positivity
      have h3 : (2 : ℝ) ≤ (9 / 10 : ℝ) * Real.sqrt 5 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      have h4 : (2 : ℝ) / Real.sqrt 5 ≤ ((9 / 10 : ℝ) * Real.sqrt 5) / Real.sqrt 5 := by gcongr
      have h5 : ((9 / 10 : ℝ) * Real.sqrt 5) / Real.sqrt 5 = 9 / 10 := by
        field_simp [h2.ne'] <;> ring
      rw [h5] at h4
      exact h4
    have h6 : 2 * L ≤ 1 / 10 := by
      have h7 : L ≤ 1 / 10000 := hL_small
      linarith
    have h7 : (2 / Real.sqrt 5) + 2 * L ≤ 9 / 10 + 1 / 10 := by gcongr
    have h8 : (9 / 10 : ℝ) + 1 / 10 = 1 := by norm_num
    rw [h8] at h7
    exact h7
  have h_key_real : 2 / (Real.sqrt 5 * L) + 2 ≤ 1 / L := by
    have h8 : 2 / (Real.sqrt 5 * L) + 2 = ((2 / Real.sqrt 5) + 2 * L) / L := by
      field_simp [hL_pos.ne'] <;> ring
    rw [h8]
    apply div_le_div_of_nonneg_right h10
    exact hL_pos.le
  have h_rpow_L : L.rpow (-1) = 1 / L := by
    have h1 : L.rpow (-1) = (L.rpow 1)⁻¹ := by
      apply Real.rpow_neg
      exact hL_pos.le
    rw [h1]
    have h2 : L.rpow 1 = L := by simp
    rw [h2]
    field_simp [hL_pos.ne']
  have hC_one : (1 : ENNReal) ≤ Kakeya.realRpowENN L (-1) := by
    have h : (1 : ℝ) ≤ 1 / L := by
      have h9 : L ≤ 1 / 10000 := hL_small
      have h10 : 0 < L := hL_pos
      have h11 : 1 / L ≥ 10000 := by
        calc 1 / L ≥ 1 / (1 / 10000 : ℝ) := by gcongr
           _ = 10000 := by norm_num
      linarith
    have h' : Kakeya.realRpowENN L (-1) = ENNReal.ofReal (1 / L) := by
      have h_def : Kakeya.realRpowENN L (-1) = ENNReal.ofReal (Real.rpow L (-1)) := by
        simp [Kakeya.realRpowENN]
      rw [h_def, h_rpow_L]
    rw [h']
    have h_ennreal : (1 : ENNReal) ≤ ENNReal.ofReal (1 / L) := by
      have h1 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (1 / L) := ENNReal.ofReal_le_ofReal h
      have h2 : ENNReal.ofReal (1 : ℝ) = (1 : ENNReal) := by simp
      rw [h2] at h1
      exact h1
    exact h_ennreal
  refine' ⟨by linarith, h1_pos, by linarith, hC_one, hE_sub, _⟩
  intro rho' hrho' hrho_ge_rho hrho'_le_one x r hr_le_r hr_le_one
  have hrho'_pos : 0 < rho' := by linarith
  have h_ab : c - Real.sqrt rho ≤ c + Real.sqrt rho := by linarith [hsqrt_pos]
  have h_set : E ∩ Metric.closedBall x r ⊆ Set.Icc (c - Real.sqrt rho) (c + Real.sqrt rho) := by
    intro y hy
    exact hE_center hy.1
  have h_len : (c + Real.sqrt rho) - (c - Real.sqrt rho) = 2 * Real.sqrt rho := by ring
  have h_cover : (Metric.externalCoveringNumber (⟨rho', hrho'_pos.le⟩ : NNReal)
      (E ∩ Metric.closedBall x r) : ENNReal) ≤
      ENNReal.ofReal (2 * Real.sqrt rho / rho' + 2) := by
    have h1 := covering_by_interval hrho'_pos h_set h_ab
    rw [h_len] at h1
    exact h1
  have h_real_ineq : 2 * Real.sqrt rho / rho' + 2 ≤ (1 / L) * (r / rho') ^ (1 - sigma) := by
    have h3 : 2 * Real.sqrt rho / rho' + 2 ≤ 2 / Real.sqrt rho + 2 := by
      have h4 : rho' ≥ rho := hrho_ge_rho
      have h5 : 2 * Real.sqrt rho / rho' ≤ 2 * Real.sqrt rho / rho := by gcongr
      have h6 : 2 * Real.sqrt rho / rho = 2 / Real.sqrt rho := by
        have hsqrt_pos' : 0 < Real.sqrt rho := hsqrt_pos
        have hsq : (Real.sqrt rho)^2 = rho := Real.sq_sqrt (by linarith)
        have h_div : Real.sqrt rho / rho = 1 / Real.sqrt rho := by
          have h' : Real.sqrt rho / rho = Real.sqrt rho / (Real.sqrt rho)^2 := by
            apply congr_arg (fun x : ℝ => Real.sqrt rho / x) hsq.symm
          rw [h']
          field_simp [hsqrt_pos'.ne']
        have h : 2 * Real.sqrt rho / rho = 2 * (Real.sqrt rho / rho) := by ring
        rw [h, h_div] <;> ring
      rw [h6] at h5
      linarith
    have h7 : 2 / Real.sqrt rho + 2 ≤ 2 / (Real.sqrt 5 * L) + 2 := by
      have h8 : 2 / Real.sqrt rho ≤ 2 / (Real.sqrt 5 * L) := by gcongr
      linarith
    have h9 : 2 / (Real.sqrt 5 * L) + 2 ≤ 1 / L := h_key_real
    have h11 : 1 ≤ r / rho' := by
      have h12 : rho' ≤ r := hr_le_r
      have h13 : 0 < rho' := hrho'_pos
      have h14 : rho' / rho' ≤ r / rho' := by gcongr
      have h15 : rho' / rho' = 1 := by field_simp [h13.ne']
      rw [h15] at h14
      exact h14
    have h12 : (1 : ℝ) ≤ (r / rho') ^ (1 - sigma) := by
      exact one_le_rpow h11 (by linarith)
    have h13 : 1 / L ≤ (1 / L) * (r / rho') ^ (1 - sigma) := by
      have h14 : 0 ≤ 1 / L := by positivity
      nlinarith
    calc
      2 * Real.sqrt rho / rho' + 2 ≤ 2 / Real.sqrt rho + 2 := h3
      _ ≤ 2 / (Real.sqrt 5 * L) + 2 := h7
      _ ≤ 1 / L := h9
      _ ≤ (1 / L) * (r / rho') ^ (1 - sigma) := h13
  have h_rpow_r : Kakeya.realRpowENN (r / rho') (1 - sigma) =
      ENNReal.ofReal ((r / rho') ^ (1 - sigma)) := by
    simp only [Kakeya.realRpowENN] <;> rfl
  have h_rpow_L' : Kakeya.realRpowENN L (-1) = ENNReal.ofReal (1 / L) := by
    have h_def : Kakeya.realRpowENN L (-1) = ENNReal.ofReal (Real.rpow L (-1)) := by
      simp [Kakeya.realRpowENN]
    rw [h_def, h_rpow_L]
  have h_enreal_ineq : ENNReal.ofReal (2 * Real.sqrt rho / rho' + 2) ≤
      Kakeya.realRpowENN L (-1) * Kakeya.realRpowENN (r / rho') (1 - sigma) := by
    rw [h_rpow_L', h_rpow_r]
    have h_nonneg1 : 0 ≤ 1 / L := by positivity
    rw [← ENNReal.ofReal_mul h_nonneg1]
    exact ENNReal.ofReal_le_ofReal h_real_ineq
  exact h_cover.trans h_enreal_ineq

end Kakeya.Assouad.PureWZ2

end
