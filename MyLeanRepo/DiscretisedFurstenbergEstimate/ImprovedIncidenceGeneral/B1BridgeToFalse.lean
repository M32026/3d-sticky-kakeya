module

/-
  B1 Bridge → A1 → A10 → A11 → False (COMBINED THEOREM)

  Takes destructured B1 bridge output + main theorem data + A-chain parameters
  and produces False via the product-like incidence axiom.

  Composition:
  1. b1_output_to_a1_output_exists : B1 data → A1_Output
  2. A1_to_A10_assembly_numerical : A1_Output → A10_Output
  3. A11_product_contradiction : A10_Output → False

  Sub-proofs:
  - h_fine_sset: S-set transfer through thinning
  - h_fine_size: exact cardinality from bridge bound
  - hQ4_sub_a1: Qset inclusion via a1-as-parameter refactoring
  - h_u_lt_two: u=2 boundary case via the limiting argument
  - hη_upper_lt: η_upper < η_axiom

  Whiteprint node: b1_bridge_to_false
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.B1ToA1Skeleton
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A1_to_A10_Assembly_Numerical
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A11_Assembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AssemblyNumericalHypotheses
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Phase2Support
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A10_Fixed
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A10_SSetUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable


noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA
open DirecretisedFurstenbergEstimate.Phase2
open DirecretisedFurstenbergEstimate.Lagoon
open DirecretisedFurstenbergEstimate.AppendixA5
open DirecretisedFurstenbergEstimate.AssemblyNumerical
open DirecretisedFurstenbergEstimate.ProductContradiction
open DirecretisedFurstenbergEstimate.A10
open CoordinatePartition

/-- Helper: bound norm of square center from A1 point data. -/
lemma center_bound_from_a1_points
    {Δ δ t s ε : ℝ} (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (a1 : A1_Output Δ δ t s ε) :
    ∀ Q ∈ a1.Qset, ‖squareCenter Δ Q‖ ≤ 2 := by
  intro Q hQ
  have h_card_pos : 0 < (a1.points Q hQ).card := by
    have h_lower : Real.rpow Δ (-t + 3 * ε) ≤ (a1.points Q hQ).card :=
      a1.h_points_card_lower Q hQ
    have h_pos : 0 < Real.rpow Δ (-t + 3 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    exact_mod_cast lt_of_lt_of_le h_pos h_lower
  rcases Finset.card_pos.mp h_card_pos with ⟨p, hp⟩
  have h_p_in_square : p ∈ Lagoon.squareSet Δ Q := a1.h_points_in_square Q hQ p hp
  have h_p_norm : ‖p‖ ≤ Real.sqrt 2 := by
    have h : p ∈ Metric.closedBall 0 (Real.sqrt 2) := a1.h_points_in_ball Q hQ hp
    simpa [Metric.mem_closedBall] using h
  have h_dist : dist p (squareCenter Δ Q) ≤ Real.sqrt 2 * Δ / 2 :=
    point_in_square_close_to_center hΔ_pos Q p h_p_in_square
  have h1 : ‖squareCenter Δ Q‖ ≤ ‖p‖ + ‖squareCenter Δ Q - p‖ := by
    calc
      ‖squareCenter Δ Q‖ = ‖p + (squareCenter Δ Q - p)‖ := by simp [add_sub_cancel]
      _ ≤ ‖p‖ + ‖squareCenter Δ Q - p‖ := norm_add_le p (squareCenter Δ Q - p)
  have h2 : ‖squareCenter Δ Q - p‖ = dist p (squareCenter Δ Q) := by
    rw [dist_eq_norm, norm_sub_rev]
  rw [h2] at h1
  have h3 : ‖squareCenter Δ Q‖ ≤ ‖p‖ + dist p (squareCenter Δ Q) := h1
  have h4 : Real.sqrt 2 + Real.sqrt 2 * Δ / 2 ≤ 2 := by
    have h4 : Δ ≤ 1 / 2 := by linarith
    have h_sqrt2_pos : 0 < Real.sqrt 2 := by positivity
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  linarith

/-- Convert TwoSBound to TwoSBoundWithLower with exponent -2s+210ε. -/
lemma two_s_bound_to_with_lower
    {Δ s t ε : ℝ} {CoarseTube : Type*} [DecidableEq CoarseTube]
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1) (hε_pos : 0 < ε)
    (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    {Qset : Finset (AppendixA.CoarseSquare Δ)}
    {C : (Q : AppendixA.CoarseSquare Δ) → Q ∈ Qset → Finset CoarseTube}
    {T_Δ : Finset CoarseTube}
    (h : TwoSBound Δ s t ε Qset C T_Δ) :
    TwoSBoundWithLower Δ s t ε Qset C T_Δ (-2 * s + 210 * ε) := by
  set c : ℝ := Real.rpow Δ (-212 * ε) with hc_def
  have hc_pos : 0 < c := Real.rpow_pos_of_pos hΔ_pos _
  have h1 : c ≥ Real.rpow Δ ε := by
    rw [hc_def]
    have h_add : Real.rpow Δ (-212 * ε) = Real.rpow Δ ε * Real.rpow Δ (-213 * ε) := by
      have h : Real.rpow Δ (ε + (-213 * ε)) = Real.rpow Δ ε * Real.rpow Δ (-213 * ε) :=
        Real.rpow_add hΔ_pos ε (-213 * ε)
      have h_sum : ε + (-213 * ε) = -212 * ε := by ring
      rw [h_sum] at h
      exact h
    rw [h_add]
    have h_neg_exp : -213 * ε < 0 := by linarith
    have h_pos_exp : 0 < 213 * ε := by positivity
    have h_lt_one : Real.rpow Δ (213 * ε) < 1 := by
      apply Real.rpow_lt_one (by linarith) (by linarith) h_pos_exp
    have h_pos2 : 0 < Real.rpow Δ (213 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h_mul_id : Real.rpow Δ (213 * ε) * Real.rpow Δ (-213 * ε) = 1 := by
      have h : Real.rpow Δ ((213 * ε) + (-213 * ε)) = Real.rpow Δ (213 * ε) * Real.rpow Δ (-213 * ε) :=
        Real.rpow_add hΔ_pos (213 * ε) (-213 * ε)
      have h_sum : (213 * ε) + (-213 * ε) = 0 := by ring
      rw [h_sum] at h
      have h0 : Real.rpow Δ 0 = 1 := by simp
      rw [h0] at h
      exact h.symm
    have h_gt_one : 1 < Real.rpow Δ (-213 * ε) := by
      have h_ne : Real.rpow Δ (213 * ε) ≠ 0 := h_pos2.ne'
      have h_inv : Real.rpow Δ (-213 * ε) = (Real.rpow Δ (213 * ε))⁻¹ := by
        exact (inv_eq_of_mul_eq_one_right h_mul_id).symm
      rw [h_inv]
      have h : (Real.rpow Δ (213 * ε))⁻¹ > 1 := by
        have h3 : (Real.rpow Δ (213 * ε))⁻¹ = 1 / Real.rpow Δ (213 * ε) := by simp
        rw [h3]
        have h4 : 1 / Real.rpow Δ (213 * ε) > 1 / (1 : ℝ) := by gcongr
        have h5 : 1 / (1 : ℝ) = 1 := by norm_num
        rw [h5] at h4
        exact h4
      exact h
    have h_pos : 0 < Real.rpow Δ ε := Real.rpow_pos_of_pos hΔ_pos _
    have h : Real.rpow Δ ε * Real.rpow Δ (-213 * ε) ≥ Real.rpow Δ ε := by
      have h' : Real.rpow Δ ε * Real.rpow Δ (-213 * ε) > Real.rpow Δ ε * (1 : ℝ) :=
        mul_lt_mul_of_pos_left h_gt_one h_pos
      have h'' : Real.rpow Δ ε * (1 : ℝ) = Real.rpow Δ ε := by ring
      linarith
    exact h
  have h21 : (2 : ℝ) * Real.rpow Δ (213 * ε) ≤ 1 := by
    have h_nonneg : 0 ≤ Real.rpow Δ (ε / 4) := Real.rpow_nonneg hΔ_pos.le _
    have h_pow : Real.rpow Δ (213 * ε) = (Real.rpow Δ (ε / 4)) ^ 852 := by
      have h3 : (213 * ε) = (ε / 4) * (852 : ℝ) := by ring
      rw [h3]
      have h4 : Real.rpow Δ ((ε / 4) * (852 : ℝ)) = Real.rpow (Real.rpow Δ (ε / 4)) (852 : ℝ) :=
        Real.rpow_mul hΔ_pos.le (ε / 4) (852 : ℝ)
      rw [h4]
      have h5 : Real.rpow (Real.rpow Δ (ε / 4)) (852 : ℝ) = (Real.rpow Δ (ε / 4)) ^ 852 := by
        simp
      exact h5
    rw [h_pow]
    have h4 : (Real.rpow Δ (ε / 4)) ^ 852 ≤ (1 / 100 : ℝ) ^ 852 := by
      gcongr <;> linarith
    have h51 : (1 / 100 : ℝ) ≤ 1 := by norm_num
    have h52 : 0 ≤ (1 / 100 : ℝ) := by norm_num
    have h5 : (1 / 100 : ℝ) ^ 852 ≤ 1 := by
      exact pow_le_one₀ h52 h51
    have h6 : (Real.rpow Δ (ε / 4)) ^ 852 ≤ 1 / 2 := by
      calc
        (Real.rpow Δ (ε / 4)) ^ 852 ≤ (1 / 100 : ℝ) ^ 852 := h4
        _ ≤ (1 / 100 : ℝ) := by
          have h_le1 : (1 / 100 : ℝ) ^ 852 ≤ (1 / 100 : ℝ) ^ 1 := by
            apply pow_le_pow_of_le_one
            <;> norm_num
          norm_num at h_le1 ⊢
          exact h_le1
        _ ≤ 1 / 2 := by norm_num
    linarith
  have h2 : (2 : ℝ) / c ≤ Real.rpow Δ (-ε) := by
    rw [hc_def]
    have h_pos208 : 0 < Real.rpow Δ (212 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h_mul1 : Real.rpow Δ (-212 * ε) * Real.rpow Δ (212 * ε) = 1 := by
      have h_add : Real.rpow Δ ((-212 * ε) + (212 * ε)) =
          Real.rpow Δ (-212 * ε) * Real.rpow Δ (212 * ε) :=
        Real.rpow_add hΔ_pos (-212 * ε) (212 * ε)
      have h_sum : (-212 * ε) + (212 * ε) = 0 := by ring
      rw [h_sum] at h_add
      have h_rpow0 : Real.rpow Δ 0 = 1 := by simp
      rw [h_rpow0] at h_add
      exact h_add.symm
    have h_inv : (2 : ℝ) / Real.rpow Δ (-212 * ε) = (2 : ℝ) * Real.rpow Δ (212 * ε) := by
      have h_ne : Real.rpow Δ (-212 * ε) ≠ 0 := (Real.rpow_pos_of_pos hΔ_pos _).ne'
      have h_eq : (Real.rpow Δ (-212 * ε))⁻¹ = Real.rpow Δ (212 * ε) := by
        exact inv_eq_of_mul_eq_one_right h_mul1
      have h : (2 : ℝ) / Real.rpow Δ (-212 * ε) = (2 : ℝ) * (Real.rpow Δ (-212 * ε))⁻¹ := by
        rw [div_eq_mul_inv]
      rw [h, h_eq] <;> ring
    rw [h_inv]
    have h_mul2 : Real.rpow Δ (213 * ε) * Real.rpow Δ (-ε) = Real.rpow Δ (212 * ε) := by
      have h_add : Real.rpow Δ ((213 * ε) + (-ε)) =
          Real.rpow Δ (213 * ε) * Real.rpow Δ (-ε) :=
        Real.rpow_add hΔ_pos (213 * ε) (-ε)
      have h_sum : (213 * ε) + (-ε) = 212 * ε := by ring
      rw [h_sum] at h_add
      exact h_add.symm
    have h_nonneg : 0 ≤ Real.rpow Δ (-ε) := Real.rpow_nonneg hΔ_pos.le _
    have h : (2 : ℝ) * (Real.rpow Δ (213 * ε) * Real.rpow Δ (-ε)) ≤ Real.rpow Δ (-ε) := by
      have h' : (2 : ℝ) * Real.rpow Δ (213 * ε) ≤ 1 := h21
      have h'' : ((2 : ℝ) * Real.rpow Δ (213 * ε)) * Real.rpow Δ (-ε) ≤ (1 : ℝ) * Real.rpow Δ (-ε) :=
        mul_le_mul_of_nonneg_right h' h_nonneg
      simpa [mul_assoc] using h''
    rw [h_mul2] at h
    exact h
  refine' ⟨c, hc_pos, h1, h2, _⟩
  intro Qsub hQsub_sub D hD_sub hQsub_large hD_card
  let S : Finset CoarseTube := T_Δ.filter (fun T => ∃ Q hQ, T ∈ D Q hQ)
  have h_main : (S.card : ℝ) ≥ Real.rpow Δ (-2 * s - 2 * ε) :=
    h Qsub hQsub_sub D hD_sub hQsub_large hD_card
  have h3 : c * Real.rpow Δ (-2 * s + 210 * ε) = Real.rpow Δ (-2 * s - 2 * ε) := by
    rw [hc_def]
    have h_add : Real.rpow Δ ((-212 * ε) + (-2 * s + 210 * ε)) =
        Real.rpow Δ (-212 * ε) * Real.rpow Δ (-2 * s + 210 * ε) :=
      Real.rpow_add hΔ_pos (-212 * ε) (-2 * s + 210 * ε)
    have h_sum : (-212 * ε) + (-2 * s + 210 * ε) = -2 * s - 2 * ε := by ring
    rw [h_sum] at h_add
    exact h_add.symm
  have hS_mem : ∀ T, T ∈ S ↔ T ∈ T_Δ ∧ ∃ Q hQ, T ∈ D Q hQ := by
    intro T
    simp [S, Finset.mem_filter]
    <;> tauto
  have hS_card : (S.card : ℝ) ≥ c * Real.rpow Δ (-2 * s + 210 * ε) := by
    rw [h3]
    exact h_main
  exact ⟨S, hS_mem, hS_card⟩

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- Combined theorem: A1 output + A4 output + A-chain params → False.

    The caller is responsible for constructing `a1` from B1 bridge data and
    for providing `hQ4_sub_a1` (typically from `linkedA2_to_A4_v2` subtype).

    Requires strict `u < 2`; callers with `u ≤ 2` should handle the u=2 boundary
    by decreasing u slightly and weakening S-sets.
-/
theorem b1_bridge_to_false
    -- =====================================================================
    -- Scale and parameter setup
    -- =====================================================================
    {n m : ℕ} (hnm : m ≤ n)
    {Δ δ t ε : ℝ}
    (hΔ_eq : Δ = dyadicDelta m)
    (hδ_eq : δ = dyadicDelta n)
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hδ_pos : 0 < δ) (hδ_le_D : δ ≤ Δ)
    (ht : 0 < t) (ht_lt_two : t < 2)
    (s u : ℝ) (htu : t ≤ u) (hu2 : u < 2)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hε_pos : 0 < ε) (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    (hst : s < t) (ht2 : t < 2)
    (hε_lt_one : ε < 1) (hε_le_one : ε ≤ 1)
    (hδ_eq2 : δ = Δ ^ 2)
    (hΔ_lt_one : Δ < 1) (hΔ_lt_third : Δ < 1 / 3)
    -- =====================================================================
    -- A1 output (constructed by caller from B1 bridge data)
    -- =====================================================================
    (a1 : A1_Output Δ δ u s ε)
    (h_points_in_ball' : ∀ Q hQ, (a1.points Q hQ : Set Plane) ⊆
      Metric.closedBall 0 (1 + Real.sqrt 2 * δ / 2))
    -- =====================================================================
    -- A4 output and C_global
    -- =====================================================================
    (T_source : Finset AppendixA.FineTube)
    (a4_v2 : AppendixA.A4_Output_v2 Δ δ s u ε T_source)
    (hQ4_sub_a1 : a4_v2.Qset ⊆ a1.Qset)
    (hQset_card_lower : Real.rpow Δ (-u + 4 * ε) ≤ (a4_v2.Qset.card : ℝ))
    (hQset_card_upper : (a4_v2.Qset.card : ℝ) ≤ Real.rpow Δ (-u - ε))
    (C_global_A2 : Finset AppendixA.CoarseTube)
    (hC_global_eq : C_global_A2 = a4_v2.Qset.biUnion (fun Q =>
      if h : Q ∈ a4_v2.Qset then (a4_v2.perSquare Q h).base.C_Q else ∅))
    (hC_global_card : C_global_A2.card ≤ Real.rpow Δ (-2 * s - 3 * ε))
    (hC_global_A2_distinct : ∀ (U1 : AppendixA.CoarseTube), U1 ∈ C_global_A2 →
      ∀ (U2 : AppendixA.CoarseTube), U2 ∈ C_global_A2 → U1 ≠ U2 →
        AppendixA.parentCell Δ hΔ_pos U1 ≠ AppendixA.parentCell Δ hΔ_pos U2)
    (hRKP_cond : 576 * ε < u - s)
    (hT_full_upper : ∀ (a4 : AppendixA.A4_Output_v2 Δ δ s u ε T_source),
      (a5FullFineFamily Δ δ s u ε a4.Qset a4.perSquare).card ≤
        Real.rpow Δ (-(4 * s + 3 * ε)))
    (h_2s_bound :
      ∀ (a4 : AppendixA.A4_Output_v2 Δ δ s u ε T_source)
        (C_global_A2 : Finset AppendixA5.CoarseTube),
        (∀ (Q : AppendixA.CoarseSquare Δ) (hQ : Q ∈ a4.Qset), (a4.perSquare Q hQ).C_Q_pi ⊆ C_global_A2) →
        (∀ (Q : AppendixA.CoarseSquare Δ) (hQ : Q ∈ a4.Qset), ‖Lagoon.squareCenter Δ Q‖ ≤ 2) →
        (∀ (Q : AppendixA.CoarseSquare Δ) (hQ : Q ∈ a4.Qset) (R : AppendixA.CoarseSquare Δ) (hR : R ∈ a4.Qset), dist (Lagoon.squareCenter Δ Q) (Lagoon.squareCenter Δ R) ≤ 3) →
        (a4.Qset.card : ℝ) ≤ Real.rpow Δ (-u - ε) →
        TwoSBoundWithLower Δ s u ε a4.Qset
          (fun Q hQ => (a4.perSquare Q hQ).C_Q_pi) C_global_A2
          (-2 * s + 210 * ε))
    (h_slope_bound_A7 : ∀ T, T ∈ C_global_A2 →
      (LemmaE.getDirV T) 1 ≠ 0 ∧ |tubeSlope T| ≤ 1 ∧ |tubeIntercept T| ≤ 3)
    (h_pack_absorb_A7 : (MainAppendix.affineLine_packing_constant : ℝ) ≤ Real.rpow Δ (-ε))
    (h_const_absorb_A7 : (MainAppendix.affineLine_packing_constant : ℝ)^2 * ((800 * (53 : ℝ)) : ℝ)^s * (4 : ℝ)^u + 1 ≤ Real.rpow Δ (-ε))
    -- =====================================================================
    -- A11 product contradiction parameters
    -- =====================================================================
    (η_axiom δ₀_axiom : ℝ)
    (hη_axiom_pos : 0 < η_axiom)
    (hδ₀_axiom_pos : 0 < δ₀_axiom)
    (hΔ_le_δ₀_axiom : Δ ≤ δ₀_axiom)
    (h_absorb_Y : (9 * 3 ^ (t - s)) * Real.rpow Δ (-10000 * ε) ≤ Real.rpow Δ (-η_axiom))
    (h_absorb_X : (729 * 50 ^ s) * Real.rpow Δ (-600 * ε) ≤ Real.rpow Δ (-η_axiom))
    (h_absorb_T : (81 ^ 3 * 16 * 50 ^ s) * Real.rpow Δ (-600 * ε) ≤ Real.rpow Δ (-η_axiom))
    (hA7 : ProductContradiction.ProductPropBoundedTheorem s (min (t - s) 1) η_axiom δ₀_axiom)
    (η_upper : ℝ)
    (hη_upper_pos : 0 < η_upper)
    (hη_upper_gt_214ε : 214 * ε < η_upper)
    (hΔ_small_allFine : (2000 : ℝ) * 2 < Real.rpow Δ (-(η_upper - 214 * ε)))
    (hη_upper_lt_axiom : η_upper < η_axiom)
    (h_num : AssemblyNumericalBounds Δ s u ε)
    (h_log_absorb : 4 * Real.log (3 / Δ) + 1 ≤ Real.rpow Δ (-3 * ε))
    : False := by
  -- =====================================================================
  -- Auxiliary bounds
  -- =====================================================================
  have hΔ_le_quarter : Δ ≤ 1 / 4 := by
    have h_eq : Δ = 1 / (2 : ℝ)^m := by
      rw [hΔ_eq, dyadicDelta]
    rw [h_eq]
    have hm2 : 2 ≤ m := by
      by_contra h
      have h' : m ≤ 1 := by omega
      rw [h_eq] at hΔ_lt_half
      interval_cases m <;> norm_num at hΔ_lt_half <;> linarith
    have h7 : (4 : ℝ) ≤ (2 : ℝ)^m := by
      have h8 : 2 ≤ m := hm2
      obtain ⟨k, hk⟩ : ∃ k : ℕ, m = 2 + k := by
        refine' ⟨m - 2, _⟩; omega
      rw [hk]
      have h9 : (2 : ℝ)^(2 + k) = 4 * (2 : ℝ)^k := by
        rw [pow_add] <;> norm_num
      rw [h9]
      have h10 : (1 : ℝ) ≤ (2 : ℝ)^k := by
        have h11 : (1 : ℕ) ≤ (2 : ℕ)^k := by
          apply Nat.one_le_pow <;> norm_num
        exact_mod_cast h11
      linarith
    have h10 : 0 < (4 : ℝ) := by norm_num
    exact one_div_le_one_div_of_le h10 h7
  have hm_pos : 1 ≤ m := by
    by_contra h
    have h0 : m = 0 := by omega
    rw [h0] at hΔ_eq
    have h1 : Δ = 1 := by simpa [dyadicDelta] using hΔ_eq
    rw [h1] at hΔ_lt_half
    <;> norm_num at hΔ_lt_half <;> linarith
  -- =====================================================================
  -- Step 3: A1_Output + A4_v2 → A10_Output
  -- =====================================================================
  let a10 : A10_Output Δ s u ε :=
    A1_to_A10_assembly_numerical
      (η_upper := η_upper)
      T_source a4_v2 a1
      hs_pos hs_lt_one (show s < u from lt_of_lt_of_le hst htu) hu2
      hε_pos hε_lt_one hε_le_one
      hδ_pos hδ_eq2
      hΔ_pos hΔ_lt_one hΔ_lt_half hΔ_lt_third
      n m hδ_eq hΔ_eq hnm hm_pos hΔ_le_quarter
      h_points_in_ball'
      hQ4_sub_a1
      hQset_card_lower hQset_card_upper
      C_global_A2 hC_global_eq
      hC_global_card hC_global_A2_distinct
      hRKP_cond
      hT_full_upper h_2s_bound
      h_slope_bound_A7
      h_pack_absorb_A7 h_const_absorb_A7
      h_log_absorb
      hη_upper_pos hη_upper_gt_214ε hΔ_small_allFine
      h_num
  -- =====================================================================
  -- Step 4: τ bridge — weaken tau_u=min(u-s,1) to tau0=min(t-s,1) ≤ tau_u
  -- =====================================================================
  have hη_upper_lt : a10.η_upper < η_axiom := by
    have h_eq : a10.η_upper = η_upper := by rfl
    rw [h_eq]
    exact hη_upper_lt_axiom
  let tau0 : ℝ := min (t - s) 1
  have h_tau0_pos : 0 < tau0 := by
    have h1 : 0 < t - s := by linarith
    positivity
  have h_tau0_le_one : tau0 ≤ 1 := min_le_right _ _
  have h_tau0_le_u_sub_s : tau0 ≤ u - s := by
    have h1 : tau0 ≤ t - s := min_le_left _ _
    linarith
  have h_a10_tau_eq : a10.τ = min (u - s) 1 := by rfl
  have h_tau0_le_a10 : tau0 ≤ a10.τ := by
    rw [h_a10_tau_eq]
    have h2 : t - s ≤ u - s := by linarith
    exact min_le_min h2 (by norm_num)
  have hC_ge1 : (1 : ℝ) ≤ Real.rpow Δ (-10000 * ε) := by
    have h2 : 0 < Δ := hΔ_pos
    have h3 : Δ ≤ 1 := by linarith
    have h4 : (-10000 * ε) ≤ 0 := by linarith
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos h2 h3 h4
  have hY_sset0 : IsDeltaSSet Δ tau0 (Real.rpow Δ (-10000 * ε)) a10.Y :=
    IsDeltaSSet.weaken_exponent a10.hY_sset (by linarith) h_tau0_le_a10 (le_refl _) hC_ge1
  let a10' : A10_Output Δ s u ε :=
    { a10 with
      τ := tau0
      hτ_pos := h_tau0_pos
      hτ_le_one := h_tau0_le_one
      hτ_le_t_sub_s := h_tau0_le_u_sub_s
      hY_sset := hY_sset0 }
  have hA7_inst : ProductPropBoundedTheorem s a10'.τ η_axiom δ₀_axiom := by
    have hτ : a10'.τ = min (t - s) 1 := by rfl
    rw [hτ]
    exact hA7
  have h_absorb_Y' : (9 * 3 ^ a10'.τ) * Real.rpow Δ (-10000 * ε) ≤ Real.rpow Δ (-η_axiom) := by
    have hτ_le : a10'.τ ≤ t - s := min_le_left _ _
    have h3 : (3 : ℝ) ^ a10'.τ ≤ (3 : ℝ) ^ (t - s) := by
      apply Real.rpow_le_rpow_of_exponent_le <;> norm_num <;> linarith
    have h9 : (9 : ℝ) * (3 : ℝ) ^ a10'.τ ≤ (9 : ℝ) * (3 : ℝ) ^ (t - s) := by gcongr
    have h_rpow_nonneg : 0 ≤ Real.rpow Δ (-10000 * ε) := Real.rpow_nonneg hΔ_pos.le _
    have h10 : ((9 : ℝ) * (3 : ℝ) ^ a10'.τ) * Real.rpow Δ (-10000 * ε) ≤
        ((9 : ℝ) * (3 : ℝ) ^ (t - s)) * Real.rpow Δ (-10000 * ε) :=
      mul_le_mul_of_nonneg_right h9 h_rpow_nonneg
    exact le_trans h10 h_absorb_Y
  exact A11.A11_product_contradiction
    a10' a10'.h_upper
    hs_pos hs_lt_one
    hΔ_pos hΔ_lt_one
    hε_pos
    η_axiom δ₀_axiom
    hη_axiom_pos
    hη_upper_lt
    hδ₀_axiom_pos
    hΔ_le_δ₀_axiom
    hA7_inst
    h_absorb_Y' h_absorb_X h_absorb_T

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
