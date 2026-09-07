import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.GridCenter
import MyLeanRepo.Kakeya.Assouad.WZ1.NatCellBalancing
import MyLeanRepo.Kakeya.Assouad.WZ1.AsymptoticHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.PackingHelpers
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
# WZ1 Lemma 47: Anisotropic Frostman Rescaling

Proof: grid coarsening + dyadic equal-occupancy pigeonhole + Frostman transfer.
Uses `gridCenter` for grid construction and `nat_cell_balance_pigeonhole` for
the equal-occupancy selection.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal
open Finset

theorem wz1_anisotropic_frostman_rescaling :
    WZ1AnisotropicFrostmanRescalingStatement := by
  intro epsilon hepsilon

  let alpha : ℝ := epsilon ^ 2
  have halpha : 0 < alpha := by positivity
  have halpha2 : 0 < alpha / 2 := by positivity

  have h_log_ineq : ∀ (y : ℝ), y ≥ 1 → ∀ (β : ℝ), 0 < β →
      Real.log y ≤ y^β / β := by
    intro y hy β hβ
    have h_pos : 0 < y^β := by positivity
    have h1 : Real.log (y^β) ≤ y^β - 1 := Real.log_le_sub_one_of_pos h_pos
    have h2 : Real.log (y^β) = β * Real.log y := by
      rw [Real.log_rpow (by linarith)]
    have h3 : β * Real.log y ≤ y^β - 1 := by linarith
    have h4 : Real.log y ≤ (y^β - 1) / β := by
      have h41 : (β * Real.log y) / β ≤ (y^β - 1) / β := by
        apply div_le_div_of_nonneg_right h3
        linarith
      have h42 : (β * Real.log y) / β = Real.log y := by
        field_simp [hβ.ne'] <;> ring
      rw [h42] at h41
      exact h41
    have h5 : (y^β - 1) / β ≤ y^β / β := by
      apply div_le_div_of_nonneg_right
      · linarith
      · linarith
    exact h4.trans h5

  let K_main : ℝ := 1 / 200
  let threshold : ℝ := K_main * alpha * Real.log 2 / 2
  have hthreshold_pos : 0 < threshold := by positivity
  let delta₀_asym : ℝ := threshold ^ (1 / (alpha / 2))
  have hdelta₀_asym_pos : 0 < delta₀_asym := by positivity
  let delta₀_quarter : ℝ := (1 / 4 : ℝ) ^ (1 / alpha)
  let delta₀ : ℝ := min (1 / 2) (min delta₀_asym (min ((1 / 2 : ℝ) ^ (1 / epsilon)) delta₀_quarter))
  have hδ₀_pos : 0 < delta₀ := by positivity
  have hδ₀_le_half : delta₀ ≤ 1 / 2 := min_le_left _ _
  have hδ₀_le_asym : delta₀ ≤ delta₀_asym :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ₀_le_eps : delta₀ ≤ (1 / 2 : ℝ) ^ (1 / epsilon) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ₀_le_quarter : delta₀ ≤ delta₀_quarter :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))

  have h_asym_prop : ∀ δ, 0 < δ → δ ≤ delta₀ →
      δ ^ alpha * Real.logb 2 (1 / δ) ≤ K_main := by
    intro δ hδ hδ_le
    have hδ_le_asym : δ ≤ delta₀_asym := hδ_le.trans hδ₀_le_asym
    have h1 : δ ^ (alpha / 2) ≤ threshold := by
      have h2 : δ ≤ threshold ^ (1 / (alpha / 2)) := hδ_le_asym
      have h3 : δ ^ (alpha / 2) ≤ (threshold ^ (1 / (alpha / 2))) ^ (alpha / 2) := by
        gcongr <;> positivity
      have h41 : (1 / (alpha / 2)) * (alpha / 2) = 1 := by field_simp [halpha2.ne'] <;> ring
      have h4 : (threshold ^ (1 / (alpha / 2))) ^ (alpha / 2) = threshold := by
        rw [←Real.rpow_mul (by positivity), h41, Real.rpow_one]
      linarith
    have h5 : 1 / δ ≥ 1 := by
      have h6 : δ ≤ 1 / 2 := hδ_le.trans hδ₀_le_half
      have h7 : δ ≤ 1 := by linarith
      exact one_le_one_div (by linarith) (by linarith)
    have h6 : Real.log (1 / δ) ≤ (1 / δ) ^ (alpha / 2) / (alpha / 2) :=
      h_log_ineq (1 / δ) h5 (alpha / 2) halpha2
    have h7 : Real.logb 2 (1 / δ) = Real.log (1 / δ) / Real.log 2 := by
      rw [Real.logb]
    rw [h7]
    have h8 : δ ^ alpha * (Real.log (1 / δ) / Real.log 2) ≤
        δ ^ alpha * (((1 / δ) ^ (alpha / 2) / (alpha / 2)) / Real.log 2) := by
      gcongr
    have h9 : δ ^ alpha * (((1 / δ) ^ (alpha / 2) / (alpha / 2)) / Real.log 2) =
        δ ^ (alpha / 2) * (2 / (alpha * Real.log 2)) := by
      have h11 : (1 / δ) ^ (alpha / 2) = (δ ^ (alpha / 2))⁻¹ := by
        have h111 : (1 / δ) = δ⁻¹ := by field_simp [hδ.ne'] <;> ring
        rw [h111, Real.inv_rpow (by linarith)]
      have h10 : δ ^ alpha * (1 / δ) ^ (alpha / 2) = δ ^ (alpha / 2) := by
        rw [h11]
        have h13 : 0 < δ ^ (alpha / 2) := by positivity
        have h14 : δ ^ (alpha - (alpha / 2)) = δ ^ alpha * (δ ^ (alpha / 2))⁻¹ := by
          rw [Real.rpow_sub (by linarith)]
          <;> field_simp [h13.ne'] <;> ring
        have h15 : alpha - (alpha / 2) = alpha / 2 := by ring
        rw [h15] at h14
        exact h14.symm
      have h91 : δ ^ alpha * (((1 / δ) ^ (alpha / 2) / (alpha / 2)) / Real.log 2) =
          δ ^ (alpha / 2) * (2 / (alpha * Real.log 2)) := by
        have h_pos_log : 0 < Real.log 2 := Real.log_pos (by norm_num)
        calc
          δ ^ alpha * (((1 / δ) ^ (alpha / 2) / (alpha / 2)) / Real.log 2)
            = (δ ^ alpha * (1 / δ) ^ (alpha / 2)) * (1 / ((alpha / 2) * Real.log 2)) := by ring
          _ = δ ^ (alpha / 2) * (1 / ((alpha / 2) * Real.log 2)) := by rw [h10]
          _ = δ ^ (alpha / 2) * (2 / (alpha * Real.log 2)) := by
            have h : 1 / ((alpha / 2) * Real.log 2) = 2 / (alpha * Real.log 2) := by
              field_simp [halpha.ne', h_pos_log.ne'] <;> ring
            rw [h]
      exact h91
    rw [h9] at h8
    have h10 : δ ^ (alpha / 2) * (2 / (alpha * Real.log 2)) ≤ K_main := by
      have h_mult_le : δ ^ (alpha / 2) * (2 / (alpha * Real.log 2)) ≤
          threshold * (2 / (alpha * Real.log 2)) := by
        gcongr
        <;> linarith
      have h_pos_log : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h_eq : threshold * (2 / (alpha * Real.log 2)) = K_main := by
        dsimp only [threshold, K_main]
        field_simp [halpha.ne', h_pos_log.ne'] <;> ring
      rw [h_eq] at h_mult_le
      exact h_mult_le
    exact h8.trans h10

  have h_eps_half : ∀ δ, 0 < δ → δ ≤ delta₀ → δ ^ epsilon ≤ 1 / 2 := by
    intro δ hδ hδ_le
    have h1 : δ ≤ (1 / 2 : ℝ) ^ (1 / epsilon) := hδ_le.trans hδ₀_le_eps
    have h2 : δ ^ epsilon ≤ ((1 / 2 : ℝ) ^ (1 / epsilon)) ^ epsilon := by gcongr <;> positivity
    have h31 : (1 / epsilon) * epsilon = 1 := by field_simp [hepsilon.ne'] <;> ring
    have h3 : ((1 / 2 : ℝ) ^ (1 / epsilon)) ^ epsilon = 1 / 2 := by
      rw [←Real.rpow_mul (by norm_num), h31, Real.rpow_one]
    rw [h3] at h2
    exact h2

  have h_alpha_quarter : ∀ δ, 0 < δ → δ ≤ delta₀ → δ ^ alpha ≤ 1 / 4 := by
    intro δ hδ hδ_le
    have h1 : δ ≤ delta₀_quarter := hδ_le.trans hδ₀_le_quarter
    have h2 : δ ^ alpha ≤ delta₀_quarter ^ alpha := by
      gcongr <;> positivity
    have h3 : delta₀_quarter ^ alpha = 1 / 4 := by
      simp only [delta₀_quarter]
      rw [←Real.rpow_mul (by norm_num)]
      have h4 : (1 / alpha) * alpha = 1 := by field_simp [halpha.ne'] <;> ring
      rw [h4, Real.rpow_one]
    rw [h3] at h2
    exact h2

  have hδ₀_le_one : delta₀ ≤ 1 := hδ₀_le_half.trans (by norm_num)
  refine ⟨delta₀, hδ₀_pos, hδ₀_le_one, ?_⟩
  intro delta w hdelta hdelta_le hdelta_w hw h_w_lower E hE_nonempty C hC_one hE_sep hE_frost phi h_nonexp h_bound

  have hw_pos : 0 < w := lt_of_lt_of_le hdelta hdelta_w
  set rho : ℝ := delta / w with hrho_def
  have hrho_pos : 0 < rho := by positivity
  have hrho_le_one : rho ≤ 1 := by
    rw [hrho_def]
    have h : delta / w ≤ 1 := by
      apply (div_le_one hw_pos).mpr
      exact hdelta_w
    exact h
  have hrho_ge_delta : delta ≤ rho := by
    rw [hrho_def]
    have h : delta ≤ delta / w := by
      have h1 : w ≤ 1 := hw
      have h2 : 0 < delta := hdelta
      have h3 : delta / 1 ≤ delta / w := by
        apply div_le_div_of_nonneg_left
        · linarith
        · linarith
        · linarith
      simpa using h3
    exact h
  have hrho_le_delta_eps : rho ≤ delta ^ epsilon := by
    rw [hrho_def]
    have h1 : w ≥ Real.rpow delta (1 - epsilon) := h_w_lower
    have h2 : delta / w ≤ delta / Real.rpow delta (1 - epsilon) := by
      have h_rpow_pos : 0 < Real.rpow delta (1 - epsilon) := Real.rpow_pos_of_pos hdelta (1 - epsilon)
      apply div_le_div_of_nonneg_left
      · linarith
      · linarith
      · linarith
    have h3 : delta / Real.rpow delta (1 - epsilon) = Real.rpow delta epsilon := by
      have h4 : 0 < Real.rpow delta (1 - epsilon) := Real.rpow_pos_of_pos hdelta (1 - epsilon)
      have h51 : delta ^ (epsilon + (1 - epsilon)) = delta ^ epsilon * delta ^ (1 - epsilon) :=
        Real.rpow_add hdelta epsilon (1 - epsilon)
      have h52 : epsilon + (1 - epsilon) = 1 := by ring
      have h5 : Real.rpow delta epsilon * Real.rpow delta (1 - epsilon) = delta := by
        have h53 : delta ^ (epsilon + (1 - epsilon)) = delta := by
          rw [h52, Real.rpow_one]
        have h54 : delta ^ epsilon * delta ^ (1 - epsilon) = delta := by
          rw [←h51, h53]
        exact h54
      have h_goal : delta / Real.rpow delta (1 - epsilon) = Real.rpow delta epsilon := by
        calc
          delta / Real.rpow delta (1 - epsilon)
            = (Real.rpow delta epsilon * Real.rpow delta (1 - epsilon)) / Real.rpow delta (1 - epsilon) := by rw [h5]
          _ = Real.rpow delta epsilon := by
            field_simp [h4.ne'] <;> ring
      exact h_goal
    rw [h3] at h2
    exact h2
  have hrho_eps_le_quarter : rho ^ epsilon ≤ 1 / 4 := by
    have h1 : rho ^ epsilon ≤ (delta ^ epsilon) ^ epsilon := by gcongr <;> positivity
    have h2 : (delta ^ epsilon) ^ epsilon = delta ^ alpha := by
      have h21 : (delta ^ epsilon) ^ epsilon = delta ^ (epsilon * epsilon) := by
        rw [←Real.rpow_mul (le_of_lt hdelta)]
      rw [h21]
      have h22 : epsilon * epsilon = alpha := by
        simp [alpha] <;> ring
      rw [h22]
    rw [h2] at h1
    exact h1.trans (h_alpha_quarter delta hdelta hdelta_le)
  have hrho_le_half : rho ≤ 1 / 2 := by
    have h1 : rho ≤ delta ^ epsilon := hrho_le_delta_eps
    have h2 : delta ^ epsilon ≤ 1 / 2 := h_eps_half delta hdelta hdelta_le
    exact h1.trans h2

  -- Packing bound: |E| ≤ 81 / delta^2 using delivered helper
  have hdelta_le_one : delta ≤ 1 := hdelta_le.trans (hδ₀_le_half.trans (by norm_num))
  have h_ball' : ∀ x ∈ E, dist x (phi.symm 0) ≤ 2 := by
    intro x hx
    have h_eq : phi.symm (phi x) = x := phi.left_inv x
    have h : dist (phi.symm (phi x)) (phi.symm 0) ≤ 2 :=
      (h_nonexp (phi x) 0).trans (h_bound x hx)
    rw [h_eq] at h
    exact h
  have h_pack : (E.card : ℝ) ≤ 81 / delta ^ 2 :=
    separated_set_packing_bound hdelta hdelta_le_one hE_sep (phi.symm 0) h_ball'


  -- Log bound
  have h_log_bound : Real.logb 2 (E.card : ℝ) + 1 ≤ 10 * Real.logb 2 (1 / delta) := by
    by_cases h1 : E.card = 1
    · have h_goal : Real.logb 2 ((E.card : ℝ)) + 1 ≤ 10 * Real.logb 2 (1 / delta) := by
        have h2 : Real.logb 2 ((E.card : ℝ)) = 0 := by
          rw [h1]
          have h3 : Real.logb 2 (1 : ℝ) = 0 := by
            rw [Real.logb]
            have h4 : Real.log (1 : ℝ) = 0 := Real.log_one
            rw [h4] <;> ring
          simpa using h3
        rw [h2]
        have h3 : 1 ≤ Real.logb 2 (1 / delta) := by
          have h4 : 1 / delta ≥ 2 := by
            have h5 : delta ≤ 1 / 2 := hdelta_le.trans hδ₀_le_half
            calc
              1 / delta ≥ 1 / (1 / 2) := by gcongr
              _ = 2 := by norm_num
          have h7 : Real.logb 2 2 ≤ Real.logb 2 (1 / delta) :=
            (Real.logb_le_logb (by norm_num) (by norm_num) (by positivity)).mpr h4
          have h8 : Real.logb 2 2 = 1 := by
            rw [Real.logb]
            have h_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
            field_simp [h_pos.ne'] <;> ring
          linarith
        linarith
      exact h_goal
    · have h1' : 2 ≤ E.card := by
        have h : E.card ≥ 1 := Finset.card_pos.mpr hE_nonempty
        omega
      have h_pos1 : 0 < (E.card : ℝ) := by exact_mod_cast (show 0 < E.card from by omega)
      have h2 : (E.card : ℝ) ≤ 81 / delta ^ 2 := h_pack
      have h3 : Real.logb 2 (E.card : ℝ) ≤ Real.logb 2 (81 / delta ^ 2) := by
        have h_pos2 : 0 < (81 / delta ^ 2 : ℝ) := by positivity
        exact (Real.logb_le_logb (by norm_num) h_pos1 h_pos2).mpr h2
      have h41 : (81 / delta ^ 2 : ℝ) = (81 : ℝ) / (delta ^ 2) := by ring
      have h4 : Real.logb 2 (81 / delta ^ 2) = Real.logb 2 81 + 2 * Real.logb 2 (1 / delta) := by
        have h5 : Real.logb 2 (81 / delta ^ 2) = Real.logb 2 81 - Real.logb 2 (delta ^ 2) := by
          rw [Real.logb_div (by norm_num) (show (delta ^ 2 : ℝ) ≠ 0 from by positivity)]
          <;> ring
        have h61 : (1 / delta : ℝ) ^ 2 = 1 / delta ^ 2 := by
          field_simp [hdelta.ne'] <;> ring
        have h6 : Real.logb 2 (delta ^ 2) = -2 * Real.logb 2 (1 / delta) := by
          have h7 : Real.logb 2 (1 / delta ^ 2) = 2 * Real.logb 2 (1 / delta) := by
            have h8 : Real.logb 2 ((1 / delta) ^ 2) = 2 * Real.logb 2 (1 / delta) := by
              rw [Real.logb_pow] <;> norm_num
            rw [h61] at *
            <;> exact h8
          have h9 : Real.logb 2 (delta ^ 2) + Real.logb 2 (1 / delta ^ 2) = 0 := by
            have h10 : Real.logb 2 ((delta ^ 2) * (1 / delta ^ 2)) = Real.logb 2 (delta ^ 2) + Real.logb 2 (1 / delta ^ 2) := by
              rw [Real.logb_mul (by positivity) (by positivity)] <;> ring
            have h11 : (delta ^ 2) * (1 / delta ^ 2) = 1 := by
              field_simp [hdelta.ne'] <;> ring
            rw [h11] at h10
            have h12 : Real.logb 2 (1 : ℝ) = 0 := by
              rw [Real.logb] <;> rw [Real.log_one] <;> ring
            linarith
          linarith
        linarith
      rw [h4] at h3
      have h5 : Real.logb 2 81 ≤ 7 := by
        have h_pos2 : (0 : ℝ) < 128 := by norm_num
        have h6 : Real.logb 2 81 ≤ Real.logb 2 128 :=
          (Real.logb_le_logb (by norm_num) (by norm_num) h_pos2).mpr (by norm_num)
        have h7 : Real.logb 2 128 = 7 := by
          rw [Real.logb]
          have h_log : Real.log 128 = 7 * Real.log 2 := by
            have h128 : (128 : ℝ) = (2 : ℝ) ^ 7 := by norm_num
            rw [h128, Real.log_pow] <;> norm_num
          rw [h_log]
          have h_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
          field_simp [h_pos.ne'] <;> ring
        linarith
      have h6 : 1 ≤ Real.logb 2 (1 / delta) := by
        have h7 : 1 / delta ≥ 2 := by
          have h8 : delta ≤ 1 / 2 := hdelta_le.trans hδ₀_le_half
          calc
            1 / delta ≥ 1 / (1 / 2) := by gcongr
            _ = 2 := by norm_num
        have h_pos2 : (0 : ℝ) < 1 / delta := by positivity
        have h9 : Real.logb 2 2 ≤ Real.logb 2 (1 / delta) :=
          (Real.logb_le_logb (by norm_num) (by norm_num) h_pos2).mpr h7
        have h10 : Real.logb 2 2 = 1 := by
          rw [Real.logb]
          have h_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
          field_simp [h_pos.ne'] <;> ring
        linarith
      linarith

  -- Grid center function using helper
  let gridCenter' : Point2 → Point2 := gridCenter rho
  have h_grid_close : ∀ (p : Point2), dist p (gridCenter' p) ≤ rho :=
    gridCenter_rho_close rho hrho_pos
  have h_grid_sep : ∀ (p q : Point2), gridCenter' p ≠ gridCenter' q →
      rho ≤ dist (gridCenter' p) (gridCenter' q) :=
    gridCenter_separated rho hrho_pos

  -- Cell assignment
  let Q : DiscreteSet 2 := E.image (fun x => gridCenter' (phi x))
  let fiber : Point2 → DiscreteSet 2 := fun q =>
    E.filter (fun x => gridCenter' (phi x) = q)
  have hQ_nonempty : Q.Nonempty := hE_nonempty.image _
  have h_fiber_nonempty : ∀ q ∈ Q, (fiber q).Nonempty := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨x, hx, rfl⟩
    refine ⟨x, Finset.mem_filter.mpr ⟨hx, by simp [fiber]⟩⟩
  have h_fiber_card_pos : ∀ q ∈ Q, 0 < (fiber q).card := by
    intro q hq
    exact Finset.card_pos.mpr (h_fiber_nonempty q hq)
  have h_fiber_le_E : ∀ q ∈ Q, (fiber q).card ≤ E.card := by
    intro q _
    exact Finset.card_le_card (Finset.filter_subset _ _)

  have h_sum_fibers : (∑ q ∈ Q, (fiber q).card : ENNReal) = (E.card : ENNReal) := by
    have h_disj : ∀ q ∈ Q, ∀ q' ∈ Q, q ≠ q' → Disjoint (fiber q) (fiber q') := by
      intro q _ q' _ hneq
      simp only [Finset.disjoint_left]
      intro x hx1 hx2
      have h4 : gridCenter' (phi x) = q := (Finset.mem_filter.mp hx1).2
      have h5 : gridCenter' (phi x) = q' := (Finset.mem_filter.mp hx2).2
      rw [h4] at h5
      exact hneq h5
    have h_union : Q.biUnion fiber = E := by
      ext x
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨q, hq, hx⟩
        have h_in_E : x ∈ E := (Finset.mem_filter.mp hx).1
        exact h_in_E
      · intro hx
        have hq : gridCenter' (phi x) ∈ Q := Finset.mem_image.mpr ⟨x, hx, rfl⟩
        have h_in_fiber : x ∈ fiber (gridCenter' (phi x)) :=
          Finset.mem_filter.mpr ⟨hx, rfl⟩
        exact ⟨gridCenter' (phi x), hq, h_in_fiber⟩
    have h_card : (Q.biUnion fiber).card = ∑ q ∈ Q, (fiber q).card :=
      Finset.card_biUnion h_disj
    have h' : ∑ q ∈ Q, (fiber q).card = E.card := by
      calc
        ∑ q ∈ Q, (fiber q).card = (Q.biUnion fiber).card := h_card.symm
        _ = E.card := by rw [h_union]
    exact_mod_cast h'

  -- Pigeonhole using nat_cell_balance_pigeonhole
  rcases nat_cell_balance_pigeonhole Q (fun q => (fiber q).card)
    (fun q hq => h_fiber_card_pos q hq) E.card
    (fun q hq => h_fiber_le_E q hq) with ⟨m, Q', hQ'_sub, h_balanced, h_retention_pigeon⟩

  let coarse : DiscreteSet 2 := Q'
  let selected : DiscreteSet 2 := E.filter (fun x => gridCenter' (phi x) ∈ Q')
  let assignment : Point2 → Point2 := fun x => gridCenter' (phi x)

  have hQ'_nonempty : Q'.Nonempty := by
    by_contra h
    have h' : Q' = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using h
    have h_sum_empty : (∑ q ∈ Q', (fiber q).card : ENNReal) = 0 := by
      rw [h'] <;> simp
    rw [h_sum_empty] at h_retention_pigeon
    have h_pos_ne : (E.card : ENNReal) ≠ 0 := by
      have h41 : 0 < E.card := Finset.card_pos.mpr hE_nonempty
      simpa [Nat.cast_eq_zero] using h41.ne'
    have h_top_ne : ENNReal.ofReal (Real.logb 2 ((E.card : ℝ) / 1) + 1) ≠ ⊤ := by
      exact ENNReal.ofReal_ne_top
    have h_pos2 : 0 < (E.card : ENNReal) / ENNReal.ofReal (Real.logb 2 ((E.card : ℝ) / 1) + 1) := by
      exact ENNReal.div_pos h_pos_ne h_top_ne
    have h_rhs : (∑ q ∈ Q, (fiber q).card : ENNReal) / ENNReal.ofReal (Real.logb 2 (E.card : ℝ) + 1) =
        (E.card : ENNReal) / ENNReal.ofReal (Real.logb 2 ((E.card : ℝ) / 1) + 1) := by
      rw [h_sum_fibers] <;> ring_nf
    rw [h_rhs] at h_retention_pigeon
    exact False.elim (not_le.mpr h_pos2 h_retention_pigeon)

  have hm_pos : 0 < m := by
    rcases hQ'_nonempty with ⟨q, hq⟩
    have h_pos_fiber : 0 < (fiber q).card := h_fiber_card_pos q (hQ'_sub hq)
    have h_upper : (fiber q).card ≤ 2 * m := (h_balanced q hq).2
    by_contra h_m0
    have h_m_eq0 : m = 0 := by omega
    rw [h_m_eq0] at h_upper
    omega

  have h_selected_sum : (selected.card : ENNReal) = ∑ q ∈ Q', (fiber q).card := by
    have h : selected = Q'.biUnion fiber := by
      ext x
      simp only [selected, Finset.mem_filter, Finset.mem_biUnion]
      constructor
      · intro hx
        refine ⟨gridCenter' (phi x), hx.2, ?_⟩
        exact Finset.mem_filter.mpr ⟨hx.1, rfl⟩
      · rintro ⟨q, hq, hx⟩
        have h1 : x ∈ E := (Finset.mem_filter.mp hx).1
        have h2 : gridCenter' (phi x) = q := (Finset.mem_filter.mp hx).2
        exact ⟨h1, h2 ▸ hq⟩
    have h_disj : ∀ q ∈ Q', ∀ q' ∈ Q', q ≠ q' → Disjoint (fiber q) (fiber q') := by
      intro q _ q' _ hneq
      simp only [Finset.disjoint_left]
      intro x hx1 hx2
      have h4 : gridCenter' (phi x) = q := (Finset.mem_filter.mp hx1).2
      have h5 : gridCenter' (phi x) = q' := (Finset.mem_filter.mp hx2).2
      rw [h4] at h5
      exact hneq h5
    have h_card : (Q'.biUnion fiber).card = ∑ q ∈ Q', (fiber q).card :=
      Finset.card_biUnion h_disj
    rw [h]
    exact_mod_cast h_card

  have h_retention_strong : (4 : ENNReal) * Kakeya.realRpowENN rho epsilon * E.enncard ≤ selected.enncard := by
    have h1 : selected.enncard ≥ E.enncard / ENNReal.ofReal (Real.logb 2 (E.card : ℝ) + 1) := by
      have h_sel : selected.enncard = (∑ q ∈ Q', ((fiber q).card : ENNReal)) := by
        have h : selected.enncard = ↑(selected.card) := by rfl
        rw [h, h_selected_sum]
        rw [Nat.cast_sum]
      have h_sum : (∑ q ∈ Q, ((fiber q).card : ENNReal)) = E.enncard := by
        exact h_sum_fibers
      calc selected.enncard
        = (∑ q ∈ Q', ((fiber q).card : ENNReal)) := h_sel
      _ ≥ (∑ q ∈ Q, ((fiber q).card : ENNReal)) / ENNReal.ofReal (Real.logb 2 (E.card : ℝ) + 1) := h_retention_pigeon
      _ = E.enncard / ENNReal.ofReal (Real.logb 2 (E.card : ℝ) + 1) := by rw [h_sum]
    have h2 : Real.logb 2 (E.card : ℝ) + 1 ≤ 10 * Real.logb 2 (1 / delta) := h_log_bound
    have h3 : ENNReal.ofReal (Real.logb 2 (E.card : ℝ) + 1) ≤
        ENNReal.ofReal (10 * Real.logb 2 (1 / delta)) :=
      ENNReal.ofReal_le_ofReal h2
    have h4 : E.enncard / ENNReal.ofReal (Real.logb 2 (E.card : ℝ) + 1) ≥
        E.enncard / ENNReal.ofReal (10 * Real.logb 2 (1 / delta)) := by
      gcongr
    have h5 : Real.logb 2 (1 / delta) > 0 := by
      have h6 : 1 / delta ≥ 2 := by
        have h7 : delta ≤ 1 / 2 := hdelta_le.trans hδ₀_le_half
        calc
          1 / delta ≥ 1 / (1 / 2) := by gcongr
          _ = 2 := by norm_num
      have h_pos1 : (0 : ℝ) < 1 := by norm_num
      have h_pos2 : (0 : ℝ) < 1 / delta := by positivity
      have h9 : Real.logb 2 1 < Real.logb 2 (1 / delta) :=
        (Real.logb_lt_logb_iff (by norm_num) h_pos1 h_pos2).mpr (by linarith)
      have h10 : Real.logb 2 1 = 0 := by simp [Real.logb]
      linarith
    have h6 : 10 * Real.logb 2 (1 / delta) ≤ 1 / (20 * delta ^ alpha) := by
      have h7 : delta ^ alpha * Real.logb 2 (1 / delta) ≤ K_main := h_asym_prop delta hdelta hdelta_le
      have h8 : Real.logb 2 (1 / delta) ≤ K_main / delta ^ alpha := by
        calc
          Real.logb 2 (1 / delta)
            = (delta ^ alpha * Real.logb 2 (1 / delta)) / delta ^ alpha := by
              field_simp [show (0 : ℝ) < delta ^ alpha by positivity] <;> ring
          _ ≤ K_main / delta ^ alpha := by gcongr
      have h9 : K_main / delta ^ alpha = 1 / (200 * delta ^ alpha) := by
        simp [K_main] <;> ring
      rw [h9] at h8
      calc
        10 * Real.logb 2 (1 / delta) ≤ 10 * (1 / (200 * delta ^ alpha)) := by gcongr
        _ = 1 / (20 * delta ^ alpha) := by ring
    have h7 : ENNReal.ofReal (10 * Real.logb 2 (1 / delta)) ≤
        ENNReal.ofReal (1 / (20 * delta ^ alpha)) := by
      exact ENNReal.ofReal_le_ofReal h6
    have h8 : E.enncard / ENNReal.ofReal (10 * Real.logb 2 (1 / delta)) ≥
        E.enncard / ENNReal.ofReal (1 / (20 * delta ^ alpha)) := by
      gcongr
    have h9 : E.enncard / ENNReal.ofReal (1 / (20 * delta ^ alpha)) =
        ENNReal.ofReal (20 * delta ^ alpha) * E.enncard := by
      set x : ENNReal := ENNReal.ofReal (20 * delta ^ alpha) with hx_def
      have hx_pos : x ≠ 0 := by
        rw [hx_def]
        have h_pos : (0 : ℝ) < 20 * delta ^ alpha := by positivity
        have h : 0 < ENNReal.ofReal (20 * delta ^ alpha) := ENNReal.ofReal_pos.mpr h_pos
        exact h.ne'
      have hx_top : x ≠ ⊤ := by
        rw [hx_def]
        exact ENNReal.ofReal_ne_top
      have h10 : ENNReal.ofReal (1 / (20 * delta ^ alpha)) = x⁻¹ := by
        have h_pos : (0 : ℝ) < 20 * delta ^ alpha := by positivity
        have h_eq : (1 / (20 * delta ^ alpha)) = (20 * delta ^ alpha)⁻¹ := by
          field_simp [h_pos.ne'] <;> ring
        rw [h_eq]
        exact ENNReal.ofReal_inv_of_pos h_pos
      rw [h10]
      have h11 : E.enncard / x⁻¹ = E.enncard * (x⁻¹)⁻¹ := by
        rw [div_eq_mul_inv]
      rw [h11]
      have h12 : (x⁻¹)⁻¹ = x := by
        simp [hx_pos, hx_top]
      rw [h12, mul_comm]
    rw [h9] at h8
    have h10 : rho ^ epsilon ≤ delta ^ alpha := by
      have h11 : rho ^ epsilon ≤ (delta ^ epsilon) ^ epsilon := by gcongr <;> positivity
      have h12 : (delta ^ epsilon) ^ epsilon = delta ^ alpha := by
        have h_eps_mul : epsilon * epsilon = alpha := by
          simp [alpha] <;> ring
        rw [←Real.rpow_mul (le_of_lt hdelta), h_eps_mul]
      rw [h12] at h11
      exact h11
    have h13 : Kakeya.realRpowENN rho epsilon ≤ Kakeya.realRpowENN delta alpha := by
      exact ENNReal.ofReal_mono h10
    have h14 : (4 : ENNReal) * Kakeya.realRpowENN rho epsilon * E.enncard ≤
        ENNReal.ofReal (20 * delta ^ alpha) * E.enncard := by
      have h15 : (4 : ENNReal) * Kakeya.realRpowENN rho epsilon ≤ ENNReal.ofReal (20 * delta ^ alpha) := by
        calc
          (4 : ENNReal) * Kakeya.realRpowENN rho epsilon
            ≤ (4 : ENNReal) * Kakeya.realRpowENN delta alpha := by gcongr
          _ = ENNReal.ofReal (4 * delta ^ alpha) := by
            simp [Kakeya.realRpowENN] <;> norm_cast
          _ ≤ ENNReal.ofReal (20 * delta ^ alpha) := by
            have h_pos_alpha : 0 < delta ^ alpha := by positivity
            exact ENNReal.ofReal_le_ofReal (by linarith)
      exact mul_le_mul_right' h15 E.enncard
    have h_chain1 : ENNReal.ofReal (20 * delta ^ alpha) * E.enncard ≤
        E.enncard / ENNReal.ofReal (10 * Real.logb 2 (1 / delta)) := by
      exact h8
    have h_chain2 : E.enncard / ENNReal.ofReal (10 * Real.logb 2 (1 / delta)) ≤
        E.enncard / ENNReal.ofReal (Real.logb 2 (E.card : ℝ) + 1) := by
      exact h4
    have h_chain3 : E.enncard / ENNReal.ofReal (Real.logb 2 (E.card : ℝ) + 1) ≤ selected.enncard := h1
    exact h14.trans (h_chain1.trans (h_chain2.trans h_chain3))

  have h_retention : Kakeya.realRpowENN rho epsilon * E.enncard ≤ selected.enncard := by
    have h : (4 : ENNReal) * Kakeya.realRpowENN rho epsilon * E.enncard ≤ selected.enncard := h_retention_strong
    have h2 : Kakeya.realRpowENN rho epsilon * E.enncard ≤ (4 : ENNReal) * Kakeya.realRpowENN rho epsilon * E.enncard := by
      have h3 : (1 : ENNReal) ≤ (4 : ENNReal) := by norm_num
      have h4 : Kakeya.realRpowENN rho epsilon * E.enncard ≤ (4 : ENNReal) * (Kakeya.realRpowENN rho epsilon * E.enncard) := by
        exact le_mul_of_one_le_left (by simp) h3
      simpa [mul_assoc] using h4
    exact h2.trans h

  have h_selected_nonempty : selected.Nonempty := by
    have h3 : Kakeya.realRpowENN rho epsilon ≠ 0 := by
      simp [Kakeya.realRpowENN, hrho_pos, hepsilon] <;> positivity
    have h4 : E.enncard ≠ 0 := by
      have h41 : 0 < E.card := Finset.card_pos.mpr hE_nonempty
      have h42 : E.enncard = ↑(E.card) := by rfl
      rw [h42]
      simp [h41.ne']
    have h2 : 0 < Kakeya.realRpowENN rho epsilon * E.enncard :=
      ENNReal.mul_pos h3 h4
    have h : 0 < selected.enncard := h2.trans_le h_retention
    have h_card_pos : 0 < selected.card := by
      by_contra h0
      have h1 : selected.card = 0 := by omega
      have h2' : selected.enncard = 0 := by
        have h3' : selected.enncard = ↑(selected.card) := by rfl
        rw [h3', h1] <;> simp
      rw [h2'] at h
      exact lt_irrefl 0 h
    exact Finset.card_pos.mp h_card_pos

  have h_selected_subset : selected ⊆ E := Finset.filter_subset _ _
  have h_coarse_nonempty : coarse.Nonempty := hQ'_nonempty

  have h_coarse_sep : coarse.IsDeltaSeparated rho := by
    intro p hp q hq hne
    have h_p_in_Q : p ∈ Q := hQ'_sub hp
    have h_q_in_Q : q ∈ Q := hQ'_sub hq
    rcases Finset.mem_image.mp h_p_in_Q with ⟨x, hx, hpx⟩
    rcases Finset.mem_image.mp h_q_in_Q with ⟨y, hy, hqy⟩
    have h_idem_p : gridCenter' p = p := by
      have h : p = gridCenter' (phi x) := hpx.symm
      rw [h]
      exact gridCenter_idempotent rho hrho_pos (phi x)
    have h_idem_q : gridCenter' q = q := by
      have h : q = gridCenter' (phi y) := hqy.symm
      rw [h]
      exact gridCenter_idempotent rho hrho_pos (phi y)
    have h_ne' : gridCenter' p ≠ gridCenter' q := by
      rw [h_idem_p, h_idem_q]
      exact hne
    have h_result : rho ≤ dist (gridCenter' p) (gridCenter' q) := h_grid_sep p q h_ne'
    rw [h_idem_p, h_idem_q] at h_result
    exact h_result

  have h_coarse_frostman : coarse.IsFrostman rho 1
      (Kakeya.realRpowENN (w / delta) epsilon * C) := by
    intro q r hrho_r hr_one
    by_cases h_half : r ≥ 1 / 2
    · -- Case r ≥ 1/2
      have h1 : coarse.ballCount q r ≤ coarse.enncard := by
        have h_ball : coarse.ballCount q r = ↑((coarse.filter (fun q' => dist q' q ≤ r)).card) := by
          simp only [DiscreteSet.ballCount] <;> rfl
        rw [h_ball]
        have h_filter : (coarse.filter (fun q' => dist q' q ≤ r)).card ≤ coarse.card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        exact Nat.cast_le.mpr h_filter
      have h2 : (1 : ENNReal) ≤ Kakeya.realRpowENN (w / delta) epsilon * C * Kakeya.realRpowENN r 1 := by
        have h3 : Kakeya.realRpowENN (w / delta) epsilon = (Kakeya.realRpowENN rho epsilon)⁻¹ := by
          have h4 : w / delta = 1 / rho := by
            rw [hrho_def] <;> field_simp [hdelta.ne', (show (0 : ℝ) < w by linarith)] <;> ring
          rw [h4]
          have h_pos : 0 < rho := hrho_pos
          have h_mul : (1 / rho) ^ epsilon * rho ^ epsilon = 1 := by
            have h_nonneg1 : 0 ≤ (1 / rho) := by positivity
            have h_nonneg2 : 0 ≤ rho := by linarith
            have h_rpow : (1 / rho) ^ epsilon * rho ^ epsilon = ((1 / rho) * rho) ^ epsilon :=
              (Real.mul_rpow h_nonneg1 h_nonneg2).symm
            rw [h_rpow]
            have h_prod : (1 / rho) * rho = 1 := by field_simp [h_pos.ne']
            rw [h_prod]
            have h_one : (1 : ℝ) ^ epsilon = 1 := Real.one_rpow epsilon
            exact h_one
          have h25 : (1 / rho) ^ epsilon = (rho ^ epsilon)⁻¹ :=
            eq_inv_of_mul_eq_one_left h_mul
          have h26 : 0 < rho ^ epsilon := by positivity
          have h27 : Kakeya.realRpowENN (1 / rho) epsilon = ENNReal.ofReal ((1 / rho) ^ epsilon) := by rfl
          rw [h27, h25]
          rw [ENNReal.ofReal_inv_of_pos h26]
          <;> rfl
        rw [h3]
        have h5 : rho ^ epsilon ≤ 1 / 4 := hrho_eps_le_quarter
        have h6 : (Kakeya.realRpowENN rho epsilon)⁻¹ ≥ (4 : ENNReal) := by
          have h7 : Kakeya.realRpowENN rho epsilon ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
            exact ENNReal.ofReal_le_ofReal h5
          have h8 : (Kakeya.realRpowENN rho epsilon)⁻¹ ≥ (ENNReal.ofReal (1 / 4 : ℝ))⁻¹ := by gcongr
          have h9 : (ENNReal.ofReal (1 / 4 : ℝ))⁻¹ = (4 : ENNReal) := by simp
          rw [h9] at h8
          exact h8
        have h10 : C ≥ (1 : ENNReal) := hC_one
        have h11 : Kakeya.realRpowENN r 1 ≥ ENNReal.ofReal (1 / 2 : ℝ) := by
          have h_r1 : Kakeya.realRpowENN r 1 = ENNReal.ofReal r := by
            simp [Kakeya.realRpowENN] <;> ring
          rw [h_r1]
          exact ENNReal.ofReal_le_ofReal h_half
        have h_base : (1 : ENNReal) ≤ (4 : ENNReal) * (1 : ENNReal) * ENNReal.ofReal (1 / 2 : ℝ) := by
          have h1 : (4 : ENNReal) * (1 : ENNReal) = (4 : ENNReal) := by simp
          have h2 : (4 : ENNReal) * ENNReal.ofReal (1 / 2 : ℝ) = ENNReal.ofReal (2 : ℝ) := by
            have h3 : (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) := by simp
            rw [h3]
            have h4 : ENNReal.ofReal (4 : ℝ) * ENNReal.ofReal (1 / 2 : ℝ) = ENNReal.ofReal ((4 : ℝ) * (1 / 2 : ℝ)) := by
              rw [←ENNReal.ofReal_mul (by norm_num)]
            rw [h4]
            have h5 : (4 : ℝ) * (1 / 2 : ℝ) = (2 : ℝ) := by norm_num
            rw [h5] <;> rfl
          rw [h1, h2]
          <;> simp
        calc
          (1 : ENNReal)
            ≤ (4 : ENNReal) * (1 : ENNReal) * ENNReal.ofReal (1 / 2 : ℝ) := h_base
          _ ≤ (Kakeya.realRpowENN rho epsilon)⁻¹ * C * Kakeya.realRpowENN r 1 := by
            gcongr
      have h12 : coarse.enncard ≤ Kakeya.realRpowENN (w / delta) epsilon * C * Kakeya.realRpowENN r 1 * coarse.enncard := by
        exact le_mul_of_one_le_left (by simp) h2
      exact h1.trans h12
    · -- Case r < 1/2
      have h_r_lt_half : r < 1 / 2 := by linarith
      have h_r_plus_rho_le_one : r + rho ≤ 1 := by linarith [hrho_le_half]
      have h_delta_le : delta ≤ r + rho := by linarith [hrho_ge_delta]
      let S : Finset Point2 := coarse.filter (fun q' => dist q' q ≤ r)
      have h_main1 : ∀ q' ∈ S, ∀ x ∈ fiber q', dist x (phi.symm q) ≤ r + rho := by
        intro q' hq' x hx
        have h4 : gridCenter' (phi x) = q' := (Finset.mem_filter.mp hx).2
        have h5 : dist (phi x) q' ≤ rho := by
          rw [←h4]
          exact h_grid_close (phi x)
        have h6 : dist q' q ≤ r := (Finset.mem_filter.mp hq').2
        have h7 : dist (phi x) q ≤ r + rho := by
          calc
            dist (phi x) q ≤ dist (phi x) q' + dist q' q := dist_triangle _ _ _
            _ ≤ rho + r := by linarith
            _ = r + rho := by ring
        have h8 : dist x (phi.symm q) = dist (phi.symm (phi x)) (phi.symm q) := by simp
        rw [h8]
        exact (h_nonexp (phi x) q).trans h7
      have h_disj_fibers : ∀ q' ∈ S, ∀ q'' ∈ S, q' ≠ q'' → Disjoint (fiber q') (fiber q'') := by
        intro q' _ q'' _ hneq
        simp only [fiber, Finset.disjoint_left]
        intro x hx1 hx2
        have h4 : gridCenter' (phi x) = q' := (Finset.mem_filter.mp hx1).2
        have h5 : gridCenter' (phi x) = q'' := (Finset.mem_filter.mp hx2).2
        rw [h4] at h5
        exact hneq h5
      have h_union : (S.biUnion fiber) ⊆ E.filter (fun x => dist x (phi.symm q) ≤ r + rho) := by
        intro x hx
        rcases Finset.mem_biUnion.mp hx with ⟨q', hq', hx'⟩
        have h_in_E : x ∈ E := (Finset.mem_filter.mp hx').1
        have h_dist : dist x (phi.symm q) ≤ r + rho := h_main1 q' hq' x hx'
        exact Finset.mem_filter.mpr ⟨h_in_E, h_dist⟩
      have h_sum : (m : ENNReal) * (S.card : ENNReal) ≤ ∑ q' ∈ S, ((fiber q').card : ENNReal) := by
        have h : ∀ q' ∈ S, (m : ENNReal) ≤ ((fiber q').card : ENNReal) := by
          intro q' hq'
          have hq'_in_Q' : q' ∈ Q' := (Finset.mem_filter.mp hq').1
          exact_mod_cast (h_balanced q' hq'_in_Q').1
        have h_eq : (m : ENNReal) * (S.card : ENNReal) = ∑ _q' ∈ S, (m : ENNReal) := by
          have h : ∑ _q' ∈ S, (m : ENNReal) = (S.card : ENNReal) * (m : ENNReal) := by
            simp [Finset.sum_const]
          rw [h, mul_comm]
        rw [h_eq]
        exact Finset.sum_le_sum h
      have h_sum2 : ∑ q' ∈ S, ((fiber q').card : ENNReal) = ((S.biUnion fiber).card : ENNReal) := by
        have h : (S.biUnion fiber).card = ∑ q' ∈ S, (fiber q').card := Finset.card_biUnion h_disj_fibers
        have h' : ∑ q' ∈ S, ((fiber q').card : ENNReal) = ↑(∑ q' ∈ S, (fiber q').card) := by
          rw [Nat.cast_sum]
        rw [h', ←h]
        <;> rfl
      have h_frost := hE_frost (phi.symm q) (r + rho) h_delta_le h_r_plus_rho_le_one
      have h9 : ((S.biUnion fiber).card : ENNReal) ≤ E.ballCount (phi.symm q) (r + rho) := by
        have h_card_le : (S.biUnion fiber).card ≤ (E.filter (fun x => dist x (phi.symm q) ≤ r + rho)).card :=
          Finset.card_le_card h_union
        have h_ball : E.ballCount (phi.symm q) (r + rho) = ↑((E.filter (fun x => dist x (phi.symm q) ≤ r + rho)).card) := by
          simp only [DiscreteSet.ballCount] <;> rfl
        rw [h_ball]
        exact_mod_cast h_card_le
      have h10 : (m : ENNReal) * (S.card : ENNReal) ≤ E.ballCount (phi.symm q) (r + rho) := by
        calc
          (m : ENNReal) * (S.card : ENNReal)
            ≤ ∑ q' ∈ S, ((fiber q').card : ENNReal) := h_sum
          _ = ((S.biUnion fiber).card : ENNReal) := h_sum2
          _ ≤ E.ballCount (phi.symm q) (r + rho) := h9
      have h11 : E.ballCount (phi.symm q) (r + rho) ≤
          C * ENNReal.ofReal (r + rho) * E.enncard := by
        simpa [Kakeya.realRpowENN] using h_frost
      have h12 : (m : ENNReal) * (S.card : ENNReal) ≤
          C * ENNReal.ofReal (r + rho) * E.enncard := h10.trans h11
      have h_selected_le : selected.enncard ≤ (2 : ENNReal) * (m : ENNReal) * coarse.enncard := by
        have h_sel_sum : selected.enncard = ∑ q ∈ coarse, ((fiber q).card : ENNReal) := by
          have h : selected.enncard = ↑(selected.card) := by rfl
          rw [h, h_selected_sum] <;> rw [Nat.cast_sum]
        rw [h_sel_sum]
        have h2 : ∑ q ∈ coarse, ((fiber q).card : ENNReal) ≤ ∑ q ∈ coarse, (2 * m : ENNReal) := by
          apply Finset.sum_le_sum
          intro q hq
          have h_bal : (fiber q).card ≤ 2 * m := (h_balanced q hq).2
          exact_mod_cast h_bal
        have h3 : ∑ q ∈ coarse, (2 * m : ENNReal) = (2 * m : ENNReal) * coarse.enncard := by
          have h4 : ∑ q ∈ coarse, (2 * m : ENNReal) = (coarse.card : ENNReal) * (2 * m : ENNReal) := by
            rw [Finset.sum_const, nsmul_eq_mul] <;> rfl
          have h5 : (coarse.card : ENNReal) = coarse.enncard := by rfl
          rw [h4, h5, mul_comm]
        exact h2.trans h3.le
      have h_m_pos' : (m : ENNReal) ≠ 0 := by
        simpa [Nat.cast_eq_zero] using hm_pos.ne'
      have h_m_top : (m : ENNReal) ≠ ⊤ := by
        exact ENNReal.natCast_ne_top m
      have h13 : (S.card : ENNReal) ≤
          C * ENNReal.ofReal (r + rho) * (E.enncard / (m : ENNReal)) := by
        have h : (m : ENNReal) * (S.card : ENNReal) ≤ C * ENNReal.ofReal (r + rho) * E.enncard := h12
        have h' : (S.card : ENNReal) ≤ (m : ENNReal)⁻¹ * (C * ENNReal.ofReal (r + rho) * E.enncard) :=
          (ENNReal.mul_le_iff_le_inv h_m_pos' h_m_top).mp h
        have h_div : (m : ENNReal)⁻¹ * (C * ENNReal.ofReal (r + rho) * E.enncard) =
            C * ENNReal.ofReal (r + rho) * (E.enncard / (m : ENNReal)) := by
          have h1 : E.enncard / (m : ENNReal) = E.enncard * (m : ENNReal)⁻¹ := by
            rw [div_eq_mul_inv]
          rw [h1]
          <;> ring
        rw [h_div] at h'
        exact h'
      have h15 : selected.enncard ≠ 0 := by
        have h_card_pos : 0 < selected.card := Finset.card_pos.mpr h_selected_nonempty
        have h : selected.enncard = ↑(selected.card) := by rfl
        rw [h]
        simp [h_card_pos.ne']
      have h_sel_top : selected.enncard ≠ ⊤ := by
        exact ENNReal.natCast_ne_top selected.card
      have h14 : E.enncard / (m : ENNReal) ≤
          (2 : ENNReal) * coarse.enncard * E.enncard / selected.enncard := by
        set X : ENNReal := (2 : ENNReal) * coarse.enncard * E.enncard with hX
        have h1 : E.enncard * selected.enncard ≤ X * (m : ENNReal) := by
          have h_sel : selected.enncard ≤ (2 : ENNReal) * (m : ENNReal) * coarse.enncard := h_selected_le
          have h2 : E.enncard * selected.enncard ≤ E.enncard * ((2 : ENNReal) * (m : ENNReal) * coarse.enncard) := by gcongr
          have h3 : E.enncard * ((2 : ENNReal) * (m : ENNReal) * coarse.enncard) = X * (m : ENNReal) := by
            have h31 : E.enncard * ((2 : ENNReal) * (m : ENNReal) * coarse.enncard) =
                (2 : ENNReal) * (m : ENNReal) * coarse.enncard * E.enncard := by
              simp [mul_assoc, mul_comm, mul_left_comm]
            rw [h31]
            have h32 : (2 : ENNReal) * (m : ENNReal) * coarse.enncard * E.enncard = X * (m : ENNReal) := by
              simp [hX, mul_assoc, mul_comm, mul_left_comm]
            exact h32
          rw [h3] at h2
          exact h2
        have h4 : E.enncard ≤ (X * (m : ENNReal)) / selected.enncard := by
          have h : E.enncard * selected.enncard * selected.enncard⁻¹ ≤ (X * (m : ENNReal)) * selected.enncard⁻¹ := by gcongr
          rw [ENNReal.mul_inv_cancel_right h15 h_sel_top] at h
          simpa [div_eq_mul_inv] using h
        have h5 : (X * (m : ENNReal)) / selected.enncard = (X / selected.enncard) * (m : ENNReal) := by
          simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
        rw [h5] at h4
        have h6 : E.enncard / (m : ENNReal) ≤ X / selected.enncard := by
          have h : E.enncard * (m : ENNReal)⁻¹ ≤ ((X / selected.enncard) * (m : ENNReal)) * (m : ENNReal)⁻¹ := by gcongr
          rw [ENNReal.mul_inv_cancel_right h_m_pos' h_m_top] at h
          simpa [div_eq_mul_inv] using h
        exact h6
      have h16 : E.enncard / selected.enncard ≤ (1 : ENNReal) / ((4 : ENNReal) * Kakeya.realRpowENN rho epsilon) := by
        set y : ENNReal := (4 : ENNReal) * Kakeya.realRpowENN rho epsilon with hy_def
        have h17 : y * E.enncard ≤ selected.enncard := h_retention_strong
        have hy_pos : y ≠ 0 := by
          rw [hy_def]
          have h1 : (4 : ENNReal) ≠ 0 := by norm_num
          have h2 : Kakeya.realRpowENN rho epsilon ≠ 0 := by
            rw [Kakeya.realRpowENN]
            have h_pos : 0 < rho ^ epsilon := Real.rpow_pos_of_pos hrho_pos epsilon
            exact ENNReal.ofReal_ne_zero_iff.mpr h_pos
          exact mul_ne_zero h1 h2
        have hy_top : y ≠ ⊤ := by
          rw [hy_def, Kakeya.realRpowENN]
          intro h
          have : (4 : ENNReal) = ⊤ ∨ ENNReal.ofReal (rho ^ epsilon) = ⊤ := by
            simpa [ENNReal.mul_eq_top] using h
          rcases this with (h4 | h2)
          · simp at h4
          · simp at h2
        have h18 : E.enncard ≤ y⁻¹ * selected.enncard := by
          have h : y⁻¹ * (y * E.enncard) ≤ y⁻¹ * selected.enncard := by gcongr
          rw [ENNReal.inv_mul_cancel_left hy_pos hy_top] at h
          exact h
        have h19 : E.enncard * selected.enncard⁻¹ ≤ y⁻¹ := by
          calc
            E.enncard * selected.enncard⁻¹
              ≤ (y⁻¹ * selected.enncard) * selected.enncard⁻¹ := by gcongr
            _ = y⁻¹ * (selected.enncard * selected.enncard⁻¹) := by rw [mul_assoc]
            _ = y⁻¹ * 1 := by rw [ENNReal.mul_inv_cancel h15 h_sel_top]
            _ = y⁻¹ := by rw [mul_one]
        have h20 : E.enncard / selected.enncard = E.enncard * selected.enncard⁻¹ := by
          rw [div_eq_mul_inv]
        have h21 : (1 : ENNReal) / y = y⁻¹ := by
          rw [one_div]
        rw [h20, h21]
        exact h19
      have h17 : (S.card : ENNReal) ≤
          C * ENNReal.ofReal (r + rho) * ((2 : ENNReal) * coarse.enncard * E.enncard / selected.enncard) := by
        calc
          (S.card : ENNReal)
            ≤ C * ENNReal.ofReal (r + rho) * (E.enncard / (m : ENNReal)) := h13
          _ ≤ C * ENNReal.ofReal (r + rho) * ((2 : ENNReal) * coarse.enncard * E.enncard / selected.enncard) := by gcongr
      have h18 : (S.card : ENNReal) ≤
          C * ENNReal.ofReal (r + rho) * (2 : ENNReal) * coarse.enncard * (E.enncard / selected.enncard) := by
        have h_rearrange : C * ENNReal.ofReal (r + rho) * ((2 : ENNReal) * coarse.enncard * E.enncard / selected.enncard) =
            C * ENNReal.ofReal (r + rho) * (2 : ENNReal) * coarse.enncard * (E.enncard / selected.enncard) := by
          have h : ((2 : ENNReal) * coarse.enncard * E.enncard) / selected.enncard =
              (2 : ENNReal) * coarse.enncard * (E.enncard / selected.enncard) := by
            have hdiv : E.enncard / selected.enncard = E.enncard * selected.enncard⁻¹ := by rw [div_eq_mul_inv]
            rw [hdiv, div_eq_mul_inv]
            <;> simp [mul_assoc, mul_comm, mul_left_comm]
          rw [h]
          <;> simp [mul_assoc]
        rw [h_rearrange] at h17
        exact h17
      have h19 : (S.card : ENNReal) ≤
          C * ENNReal.ofReal r * coarse.enncard / Kakeya.realRpowENN rho epsilon := by
        set x : ENNReal := Kakeya.realRpowENN rho epsilon with hx_def
        have hx_pos' : x ≠ 0 := by
          rw [hx_def, Kakeya.realRpowENN]
          have h : 0 < rho ^ epsilon := by positivity
          exact ENNReal.ofReal_ne_zero_iff.mpr h
        have hx_top' : x ≠ ⊤ := by
          rw [hx_def, Kakeya.realRpowENN] <;> exact ENNReal.ofReal_ne_top
        have h4_pos : (4 : ENNReal) ≠ 0 := by norm_num
        have h4_top : (4 : ENNReal) ≠ ⊤ := by simp
        have h_eq1 : ((4 : ENNReal) * x) * ((4 : ENNReal)⁻¹ * x⁻¹) = 1 := by
          have h_comm : ((4 : ENNReal) * x) * ((4 : ENNReal)⁻¹ * x⁻¹) =
              ((4 : ENNReal) * (4 : ENNReal)⁻¹) * (x * x⁻¹) := by
            simp only [mul_assoc, mul_comm, mul_left_comm]
            <;> rfl
          rw [h_comm]
          have h_c1 : (4 : ENNReal) * (4 : ENNReal)⁻¹ = 1 := ENNReal.mul_inv_cancel h4_pos h4_top
          have h_c2 : x * x⁻¹ = 1 := ENNReal.mul_inv_cancel hx_pos' hx_top'
          rw [h_c1, h_c2] <;> simp
        have h_eq2 : ((4 : ENNReal)⁻¹ * x⁻¹) * ((4 : ENNReal) * x) = 1 := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using h_eq1
        have h_inv_eq : ((4 : ENNReal) * x)⁻¹ = (4 : ENNReal)⁻¹ * x⁻¹ :=
          (ENNReal.eq_inv_of_mul_eq_one_left h_eq2).symm
        have h_cancel : (4 : ENNReal) * (((4 : ENNReal) * x)⁻¹) = x⁻¹ := by
          rw [h_inv_eq]
          have h : (4 : ENNReal) * ((4 : ENNReal)⁻¹ * x⁻¹) = ((4 : ENNReal) * (4 : ENNReal)⁻¹) * x⁻¹ := by
            rw [mul_assoc]
          rw [h, ENNReal.mul_inv_cancel h4_pos h4_top, one_mul]
        have h20 : r + rho ≤ 2 * r := by linarith [hrho_r]
        have h21 : ENNReal.ofReal (r + rho) ≤ ENNReal.ofReal (2 * r) := ENNReal.ofReal_le_ofReal h20
        have h22 : ENNReal.ofReal (2 * r) = (2 : ENNReal) * ENNReal.ofReal r := by
          have h : (2 * r : ℝ) = (2 : ℝ) * r := by ring
          rw [h, ENNReal.ofReal_mul (by norm_num)] <;> norm_cast
        set inv : ENNReal := ((4 : ENNReal) * x)⁻¹ with hinv
        have h_step1 : C * ENNReal.ofReal (r + rho) * (2 : ENNReal) * coarse.enncard * inv ≤
            C * ENNReal.ofReal (2 * r) * (2 : ENNReal) * coarse.enncard * inv := by gcongr
        have h_step2 : C * ENNReal.ofReal (2 * r) * (2 : ENNReal) * coarse.enncard * inv =
            C * ENNReal.ofReal r * ((4 : ENNReal) * inv) * coarse.enncard := by
          rw [h22]
          have h4 : (2 : ENNReal) * (2 : ENNReal) = (4 : ENNReal) := by norm_num
          simp [h4, mul_assoc, mul_comm, mul_left_comm] <;> rfl
        have h_step3 : C * ENNReal.ofReal r * ((4 : ENNReal) * inv) * coarse.enncard =
            C * ENNReal.ofReal r * coarse.enncard * ((4 : ENNReal) * inv) := by
          simp [mul_assoc, mul_comm, mul_left_comm]
        have h_main : C * ENNReal.ofReal (r + rho) * (2 : ENNReal) * coarse.enncard * inv ≤
            C * ENNReal.ofReal r * coarse.enncard * x⁻¹ := by
          calc
            C * ENNReal.ofReal (r + rho) * (2 : ENNReal) * coarse.enncard * inv
              ≤ C * ENNReal.ofReal (2 * r) * (2 : ENNReal) * coarse.enncard * inv := h_step1
            _ = C * ENNReal.ofReal r * ((4 : ENNReal) * inv) * coarse.enncard := h_step2
            _ = C * ENNReal.ofReal r * coarse.enncard * ((4 : ENNReal) * inv) := h_step3
            _ = C * ENNReal.ofReal r * coarse.enncard * x⁻¹ := by rw [h_cancel]
        have h16' : E.enncard / selected.enncard ≤ inv := by
          have h_eq : inv = (1 : ENNReal) / ((4 : ENNReal) * x) := by
            simp [hinv, div_eq_mul_inv]
          rw [h_eq]
          exact h16
        have h18' : (S.card : ENNReal) ≤ C * ENNReal.ofReal (r + rho) * (2 : ENNReal) * coarse.enncard * inv := by
          calc
            (S.card : ENNReal)
              ≤ C * ENNReal.ofReal (r + rho) * (2 : ENNReal) * coarse.enncard * (E.enncard / selected.enncard) := h18
            _ ≤ C * ENNReal.ofReal (r + rho) * (2 : ENNReal) * coarse.enncard * inv := by gcongr
        have h_final : C * ENNReal.ofReal r * coarse.enncard * x⁻¹ = C * ENNReal.ofReal r * coarse.enncard / x := by
          have h : C * ENNReal.ofReal r * coarse.enncard / x = C * ENNReal.ofReal r * coarse.enncard * x⁻¹ := by
            rw [div_eq_mul_inv] <;> simp [mul_assoc]
          exact h.symm
        have h_result : (S.card : ENNReal) ≤ C * ENNReal.ofReal r * coarse.enncard * x⁻¹ :=
          h18'.trans h_main
        rw [←h_final]
        exact h_result
      have h23 : Kakeya.realRpowENN (w / delta) epsilon = (Kakeya.realRpowENN rho epsilon)⁻¹ := by
        have h24 : w / delta = 1 / rho := by
          rw [hrho_def] <;> field_simp [hdelta.ne', (show (0 : ℝ) < w by linarith)] <;> ring
        rw [h24]
        have h_pos : 0 < rho := hrho_pos
        have h26 : 0 < rho ^ epsilon := by positivity
        have h_left : Kakeya.realRpowENN (1 / rho) epsilon = ENNReal.ofReal ((1 / rho) ^ epsilon) := by rfl
        rw [h_left]
        have h_mul : (1 / rho) ^ epsilon * rho ^ epsilon = 1 := by
          have h_nonneg1 : 0 ≤ (1 / rho) := by positivity
          have h_nonneg2 : 0 ≤ rho := by linarith
          have h_rpow : ((1 / rho) * rho) ^ epsilon = (1 / rho) ^ epsilon * rho ^ epsilon :=
            Real.mul_rpow (x := 1 / rho) (y := rho) (z := epsilon) h_nonneg1 h_nonneg2
          have h_eq : (1 / rho) ^ epsilon * rho ^ epsilon = ((1 / rho) * rho) ^ epsilon := h_rpow.symm
          rw [h_eq]
          have h_prod : (1 / rho) * rho = 1 := by field_simp [h_pos.ne']
          rw [h_prod, Real.one_rpow epsilon]
        have h25 : (1 / rho) ^ epsilon = (rho ^ epsilon)⁻¹ :=
          eq_inv_of_mul_eq_one_left h_mul
        rw [h25]
        have h27 : ENNReal.ofReal ((rho ^ epsilon)⁻¹) = (ENNReal.ofReal (rho ^ epsilon))⁻¹ :=
          ENNReal.ofReal_inv_of_pos h26
        rw [h27]
        <;> rfl
      rw [h23]
      have h_r1 : Kakeya.realRpowENN r 1 = ENNReal.ofReal r := by
        simp [Kakeya.realRpowENN] <;> ring
      have h19' : (S.card : ENNReal) ≤ C * ENNReal.ofReal r * coarse.enncard * (Kakeya.realRpowENN rho epsilon)⁻¹ := by
        simpa [div_eq_mul_inv] using h19
      have h_comm : C * ENNReal.ofReal r * coarse.enncard * (Kakeya.realRpowENN rho epsilon)⁻¹ =
          (Kakeya.realRpowENN rho epsilon)⁻¹ * C * ENNReal.ofReal r * coarse.enncard := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      have h_final : (S.card : ENNReal) ≤
          (Kakeya.realRpowENN rho epsilon)⁻¹ * C * Kakeya.realRpowENN r 1 * coarse.enncard := by
        rw [h_r1]
        rw [h_comm] at h19'
        exact h19'
      have h_ball : S = coarse.filter (fun q' => dist q' q ≤ r) := by rfl
      rw [h_ball] at h_final
      simpa [DiscreteSet.ballCount] using h_final

  have h_assignment_mem : ∀ x ∈ selected, assignment x ∈ coarse := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2

  have h_assignment_close : ∀ x ∈ selected, dist (phi x) (assignment x) ≤ rho := by
    intro x _
    exact h_grid_close (phi x)

  have h_assignment_surj : ∀ q ∈ coarse, ∃ x ∈ selected, assignment x = q := by
    intro q hq
    have hq_in_Q : q ∈ Q := hQ'_sub hq
    rcases h_fiber_nonempty q hq_in_Q with ⟨x, hx⟩
    have h4 : gridCenter' (phi x) = q := (Finset.mem_filter.mp hx).2
    refine ⟨x, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, ?_⟩, ?_⟩
    · rw [h4]; exact hq
    · simpa [assignment] using h4

  have h_fiber_comparable : ∀ q ∈ coarse,
      m ≤ (selected.filter fun x => assignment x = q).card ∧
        (selected.filter fun x => assignment x = q).card ≤ 2 * m := by
    intro q hq
    have h1 : (selected.filter fun x => assignment x = q) = fiber q := by
      ext x
      simp only [selected, assignment, fiber, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hxE, _⟩, h_eq⟩
        exact ⟨hxE, h_eq⟩
      · rintro ⟨hxE, h_eq⟩
        have hQ' : gridCenter' (phi x) ∈ Q' := by
          rw [h_eq]
          exact hq
        exact ⟨⟨hxE, hQ'⟩, h_eq⟩
    rw [h1]
    exact ⟨(h_balanced q hq).1, (h_balanced q hq).2⟩

  exact ⟨selected, h_selected_subset, h_selected_nonempty, h_retention,
    coarse, h_coarse_nonempty, h_coarse_sep, h_coarse_frostman,
    assignment, h_assignment_mem, h_assignment_close, h_assignment_surj,
    m, hm_pos, h_fiber_comparable⟩

end Kakeya.Assouad
