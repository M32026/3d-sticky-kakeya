module

/-
  A4_v2→A10 Assembly

  Takes a concrete A4_Output_v2 (single source of truth for both fine and
  coarse data) and A1_Output (for center bounds), produces A10_Output.

  C_global_A2 is DERIVED from a4_v2.perSquare(Q).base.C_Q by biUnion,
  ensuring coarse CounterData and fine CounterData apply to the same
  underlying objects (operator-mandated linkage design).

  Chain: A4_v2 → (derive C_global) → A5 → A7 → A8 → A9 → A10.
  A1 is used only for ball-based center norm/distance bounds.

  All hypotheses are explicit parameters. No internal sorrys.

  Whiteprint node: appendix_a_alternative / a1_to_a10_assembly
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A3_Canonical
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A4_RKP
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A5_canonical
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A7_PhysicalSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A8_FineFiberPopularity
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A9_Canonical
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A10_Fixed
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A10_FineRescalable
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A10_AllFineUpper
public import MyLeanRepo.DiscretisedFurstenbergEstimate.QTTC_Assembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.AffineLinePackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.SSetRestriction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section


open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.AppendixA

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.QTTC_Assembly
open DirecretisedFurstenbergEstimate.AppendixA4
open DirecretisedFurstenbergEstimate.AppendixA3
open DirecretisedFurstenbergEstimate.AppendixA5
open DirecretisedFurstenbergEstimate.AppendixA.A10
open DirecretisedFurstenbergEstimate.Lagoon

/-- Tight norm bound for square centers from ball point data. -/
lemma center_norm_tight_from_ball
    {Δ δ t s ε R : ℝ} (hΔ_pos : 0 < Δ)
    (a1 : A1_Output Δ δ t s ε)
    (h_points_in_ball : ∀ Q hQ, (a1.points Q hQ : Set Plane) ⊆ Metric.closedBall 0 R) :
    ∀ Q ∈ a1.Qset, ‖squareCenter Δ Q‖ ≤ R + Real.sqrt 2 * Δ / 2 := by
  intro Q hQ
  have h_card_pos : 0 < (a1.points Q hQ).card := by
    have h_lower : Real.rpow Δ (-t + 3 * ε) ≤ (a1.points Q hQ).card :=
      a1.h_points_card_lower Q hQ
    have h_pos : 0 < Real.rpow Δ (-t + 3 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    exact_mod_cast lt_of_lt_of_le h_pos h_lower
  rcases Finset.card_pos.mp h_card_pos with ⟨p, hp⟩
  have h_p_in_square : p ∈ Lagoon.squareSet Δ Q := a1.h_points_in_square Q hQ p hp
  have h_p_norm : ‖p‖ ≤ R := by
    have h : p ∈ Metric.closedBall (0 : Plane) R := h_points_in_ball Q hQ hp
    simpa [Metric.mem_closedBall] using h
  have h_dist : dist p (squareCenter Δ Q) ≤ Real.sqrt 2 * Δ / 2 :=
    point_in_square_close_to_center hΔ_pos Q p h_p_in_square
  have h1 : ‖squareCenter Δ Q‖ ≤ ‖p‖ + dist p (squareCenter Δ Q) := by
    calc
      ‖squareCenter Δ Q‖ = ‖p + (squareCenter Δ Q - p)‖ := by simp [add_sub_cancel]
      _ ≤ ‖p‖ + ‖squareCenter Δ Q - p‖ := norm_add_le p (squareCenter Δ Q - p)
      _ = ‖p‖ + dist p (squareCenter Δ Q) := by rw [dist_eq_norm, norm_sub_rev]
  linarith

/-- Norm bound ≤ 2 for square centers from tight ball R = 1 + √2*δ/2 (Δ ≤ 1/4). -/
lemma center_norm_le_two_from_ball
    {Δ δ t s ε : ℝ} (hΔ_pos : 0 < Δ) (hΔ_le_quarter : Δ ≤ 1 / 4)
    (hδ_eq : δ = Δ ^ 2)
    (a1 : A1_Output Δ δ t s ε)
    (h_points_in_ball : ∀ Q hQ, (a1.points Q hQ : Set Plane) ⊆ Metric.closedBall 0 (1 + Real.sqrt 2 * δ / 2)) :
    ∀ Q ∈ a1.Qset, ‖squareCenter Δ Q‖ ≤ 2 := by
  let R := 1 + Real.sqrt 2 * δ / 2
  have h_tight := center_norm_tight_from_ball hΔ_pos a1 h_points_in_ball
  intro Q hQ
  have h1 : ‖squareCenter Δ Q‖ ≤ R + Real.sqrt 2 * Δ / 2 := h_tight Q hQ
  have h_sqrt2_le2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff] <;> norm_num
  have h_sum_le : Δ ^ 2 + Δ ≤ 5 / 16 := by
    have h1 : Δ ^ 2 ≤ 1 / 16 := by
      calc Δ ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by gcongr
           _ = 1 / 16 := by norm_num
    have h2 : Δ ≤ 4 / 16 := by
      have h3 : Δ ≤ 1 / 4 := hΔ_le_quarter
      linarith
    linarith
  have h_mul_le : Real.sqrt 2 * (Δ ^ 2 + Δ) / 2 ≤ 1 := by
    have h51 : Real.sqrt 2 * (Δ ^ 2 + Δ) ≤ 2 * (Δ ^ 2 + Δ) :=
      mul_le_mul_of_nonneg_right h_sqrt2_le2 (by positivity)
    have h52 : (Real.sqrt 2 * (Δ ^ 2 + Δ)) / 2 ≤ Δ ^ 2 + Δ := by
      calc (Real.sqrt 2 * (Δ ^ 2 + Δ)) / 2
        ≤ (2 * (Δ ^ 2 + Δ)) / 2 := by gcongr
      _ = Δ ^ 2 + Δ := by ring
    have h53 : Δ ^ 2 + Δ ≤ 5 / 16 := h_sum_le
    have h54 : (Real.sqrt 2 * (Δ ^ 2 + Δ)) / 2 ≤ 5 / 16 := by linarith
    linarith
  have h2 : R + Real.sqrt 2 * Δ / 2 ≤ 2 := by
    dsimp only [R]
    rw [hδ_eq]
    have h_expand : (1 + Real.sqrt 2 * Δ ^ 2 / 2 + Real.sqrt 2 * Δ / 2) =
        1 + Real.sqrt 2 * (Δ ^ 2 + Δ) / 2 := by ring
    rw [h_expand]
    have h_final : 1 + Real.sqrt 2 * (Δ ^ 2 + Δ) / 2 ≤ 2 := by
      have h : Real.sqrt 2 * (Δ ^ 2 + Δ) / 2 ≤ 1 := h_mul_le
      linarith
    exact h_final
  exact le_trans h1 h2

/-- Distance bound ≤ 3 for square centers from tight ball radius R = 1 + √2*δ/2.
    Uses δ = Δ² and Δ ≤ 1/4: 2*(R + √2*Δ/2) = 2 + √2*(δ + Δ) ≤ 2 + √2*(5/16) < 3. -/
lemma center_dist_le_three_from_ball
    {Δ δ t s ε : ℝ} (hΔ_pos : 0 < Δ) (hΔ_le_quarter : Δ ≤ 1 / 4)
    (hδ_eq : δ = Δ ^ 2)
    (a1 : A1_Output Δ δ t s ε)
    (h_points_in_ball : ∀ Q hQ, (a1.points Q hQ : Set Plane) ⊆ Metric.closedBall 0 (1 + Real.sqrt 2 * δ / 2)) :
    ∀ (Q1 Q2 : CoarseSquare Δ), Q1 ∈ a1.Qset → Q2 ∈ a1.Qset →
      dist (squareCenter Δ Q1) (squareCenter Δ Q2) ≤ 3 := by
  let R := 1 + Real.sqrt 2 * δ / 2
  have h_tight := center_norm_tight_from_ball hΔ_pos a1 h_points_in_ball
  intro Q1 Q2 hQ1 hQ2
  have h1 : ‖squareCenter Δ Q1‖ ≤ R + Real.sqrt 2 * Δ / 2 := h_tight Q1 hQ1
  have h2 : ‖squareCenter Δ Q2‖ ≤ R + Real.sqrt 2 * Δ / 2 := h_tight Q2 hQ2
  have h3 : dist (squareCenter Δ Q1) (squareCenter Δ Q2) ≤
      ‖squareCenter Δ Q1‖ + ‖squareCenter Δ Q2‖ := by
    rw [dist_eq_norm]; exact norm_sub_le _ _
  have h_sqrt2_le2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff] <;> norm_num
  have h_sum_le : Δ ^ 2 + Δ ≤ 5 / 16 := by
    have h1 : Δ ^ 2 ≤ 1 / 16 := by
      calc Δ ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by gcongr
           _ = 1 / 16 := by norm_num
    linarith [hΔ_le_quarter, h1]
  have h_sqrt2_mul_le : Real.sqrt 2 * (Δ ^ 2 + Δ) ≤ 1 := by
    have h_nonneg : 0 ≤ Δ ^ 2 + Δ := by positivity
    have h_sqrt2_le2' : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_iff] <;> norm_num
    have h1 : Real.sqrt 2 * (Δ ^ 2 + Δ) ≤ 2 * (Δ ^ 2 + Δ) :=
      mul_le_mul_of_nonneg_right h_sqrt2_le2' h_nonneg
    have h2 : 2 * (Δ ^ 2 + Δ) ≤ 5 / 8 := by
      have h21 : Δ ^ 2 + Δ ≤ 5 / 16 := h_sum_le
      linarith
    linarith
  have h4 : 2 * (R + Real.sqrt 2 * Δ / 2) ≤ 3 := by
    dsimp only [R]
    rw [hδ_eq]
    have h_expand : 2 * (1 + Real.sqrt 2 * Δ ^ 2 / 2 + Real.sqrt 2 * Δ / 2) =
        2 + Real.sqrt 2 * (Δ ^ 2 + Δ) := by ring
    rw [h_expand]
    linarith
  linarith

/-- A4_v2→A10 assembly: takes concrete A4_Output_v2 (single source of truth)
    and A1_Output (for center bounds), produces A10_Output.

    C_global_A2 is DERIVED from a4_v2.perSquare(Q).base.C_Q by biUnion,
    ensuring coarse and fine data refer to the same underlying objects.
    All hypotheses are explicit parameters (no internal sorrys). -/
noncomputable def A1_to_A10_assembly
    {Δ δ s t ε η_upper : ℝ}
    -- Fixed source family: image(toAffineLine, config.T₀)
    (T_source : Finset FineTube)
    -- Concrete A4 output with source provenance (single source of truth)
    (a4_v2 : A4_Output_v2 Δ δ s t ε T_source)
    -- A1 output (needed for center-bound derivation from ball point data)
    (a1 : A1_Output Δ δ t s ε)
    (h_points_in_ball : ∀ Q hQ, (a1.points Q hQ : Set Plane) ⊆ Metric.closedBall 0 (1 + Real.sqrt 2 * δ / 2))
    -- Qset subset for center bounds
    (hQ4_sub_a1 : a4_v2.Qset ⊆ a1.Qset)
    -- Qset card bounds from A3 construction
    (hQset_card_lower : Real.rpow Δ (-t + 4 * ε) ≤ (a4_v2.Qset.card : ℝ))
    (hQset_card_upper : (a4_v2.Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε))
    (h_small_delta : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    -- Parameter conditions
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2)
    (hε_pos : 0 < ε) (hε_lt_one : ε < 1) (hε_le_one : ε ≤ 1)
    (hδ_pos : 0 < δ) (hδ_eq : δ = Δ ^ 2)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1) (hΔ_lt_half : Δ < 1 / 2)
    (hΔ_lt_third : Δ < 1 / 3)
    -- Dyadic scale parameters
    (n m0 : ℕ)
    (hδ_dyadic : δ = dyadicDelta n)
    (hΔ_dyadic : Δ = dyadicDelta m0)
    (hnm : m0 ≤ n)
    (hm_pos : 1 ≤ m0)
    -- Scale separation
    (hΔ_le_quarter : Δ ≤ 1 / 4)
    -- Derived coarse family (biUnion of base.C_Q from a4_v2)
    (C_global_A2 : Finset CoarseTube)
    (hC_global_eq : C_global_A2 = a4_v2.Qset.biUnion (fun Q =>
      if h : Q ∈ a4_v2.Qset then (a4_v2.perSquare Q h).base.C_Q else ∅))
    -- Concrete C_global bound
    (hC_global_card : C_global_A2.card ≤ Real.rpow Δ (-2 * s - 3 * ε))
    -- C_global distinct parent cells
    (hC_global_A2_distinct : ∀ (U1 : CoarseTube), U1 ∈ C_global_A2 →
      ∀ (U2 : CoarseTube), U2 ∈ C_global_A2 → U1 ≠ U2 →
        parentCell Δ hΔ_pos U1 ≠ parentCell Δ hΔ_pos U2)
    (hRKP_cond : 576 * ε < t - s)
    -- Counter-assumption: fine tube family cardinality bound via A4_v2 (fixed T_source)
    (hT_full_upper : ∀ (a4 : A4_Output_v2 Δ δ s t ε T_source),
      (a5FullFineFamily Δ δ s t ε a4.Qset a4.perSquare).card ≤
        Real.rpow Δ (-(4 * s + 3 * ε)))
    -- Two-s bound via A4_v2
    (h_2s_bound :
      ∀ (a4 : A4_Output_v2 Δ δ s t ε T_source) (C_global_A2 : Finset AppendixA5.CoarseTube),
        (∀ Q hQ, (a4.perSquare Q hQ).C_Q_pi ⊆ C_global_A2) →
        (∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4.Qset), ‖Lagoon.squareCenter Δ Q‖ ≤ 2) →
        (∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4.Qset) (R : CoarseSquare Δ) (hR : R ∈ a4.Qset), dist (Lagoon.squareCenter Δ Q) (Lagoon.squareCenter Δ R) ≤ 3) →
        (a4.Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε) →
        TwoSBoundWithLower Δ s t ε a4.Qset
          (fun Q hQ => (a4.perSquare Q hQ).C_Q_pi) C_global_A2
          (-2 * s + 210 * ε))
    (hK_bound : (4 * s + 3 * ε) * Real.log (1 / Δ) / Real.log 2 + 1 ≤
        Real.rpow Δ (-2 * ε) / 2)
    (hΔ_3ε : Real.rpow Δ (-3 * ε) ≥ 2)
    -- A7 conditions
    (h_small_half : Real.rpow Δ ε ≤ 1 / 2)
    (h_small2 : 4 + 16 * (2 : ℝ)^(t - s) ≤ Real.rpow Δ (-4 * ε))
    (h_slope_bound_A7 : ∀ T, T ∈ C_global_A2 →
      (LemmaE.getDirV T) 1 ≠ 0 ∧ |tubeSlope T| ≤ 1 ∧ |tubeIntercept T| ≤ 3)
    -- A8 conditions
    (hΔ_small_A8 : (25 : ℝ) ≤ Real.rpow Δ (-2 * ε))
    -- A9 conditions
    (hΔ_cover_A9 : (10000 : ℝ) ≤ Real.rpow Δ (-2 * s - ε))
    (hΔ_packing_A9 : Δ ^ (10 * ε) ≤ 1 / 144)
    (hΔ_small_A9 : 7 * Δ ≤ 1)
    (hΔ_coarse_absorb_A9 : (2 * 10^13 : ℝ) ≤ Real.rpow Δ (-ε))
    (hΔ_fine_absorb_A9 : (16 * (MainAppendix.affineLine_packing_constant : ℝ)^2 *
        (2 * 20 * 1048576 * 256 * (3 / 2 : ℝ) * 256 * 16)) ≤ Real.rpow Δ (-453 * ε))
    -- A7 physical extraction conditions
    (h_pack_absorb_A7 : (MainAppendix.affineLine_packing_constant : ℝ) ≤ Real.rpow Δ (-ε))
    (h_const_absorb_A7 : (MainAppendix.affineLine_packing_constant : ℝ)^2 * ((800 * (53 : ℝ)) : ℝ)^s * (4 : ℝ)^t + 1 ≤ Real.rpow Δ (-ε))
    (h_log_absorb : 4 * Real.log (3 / Δ) + 1 ≤ Real.rpow Δ (-3 * ε))
    -- A10 conditions
    (hΔ_lt_1_16 : Δ < 1 / 16)
    (hη_upper_pos : 0 < η_upper)
    (hη_upper_gt_214ε : 214 * ε < η_upper)
    (hΔ_small_allFine : (2000 : ℝ) * 2 < Real.rpow Δ (-(η_upper - 214 * ε)))
    (h_absorb_shear : (400 : ℝ) * (Real.sqrt 2) ^ s * (2 : ℝ) ^ s *
        Real.rpow Δ (-501 * ε) ≤ Real.rpow Δ (-600 * ε))
    (h_absorb_union : (120 : ℝ) * Real.rpow Δ (-576 * ε) ≤ Real.rpow Δ (-600 * ε))
    :
    A10_Output Δ s t ε := by
  have hδ_le_quarter_Delta : δ ≤ Δ / 4 := by
    rw [hδ_eq]
    nlinarith [hΔ_le_quarter, hΔ_pos]
  -- ### C_global_A2 is derived from a4_v2 base fields by biUnion
  have hCglobal_A2_upper : (C_global_A2.card : ℝ) ≤ Real.rpow Δ (-2 * s - 3 * ε) :=
    hC_global_card
  have hC_global_A2_distinct' : ∀ (U1 : CoarseTube), U1 ∈ C_global_A2 →
      ∀ (U2 : CoarseTube), U2 ∈ C_global_A2 → U1 ≠ U2 →
        parentCell Δ hΔ_pos U1 ≠ parentCell Δ hΔ_pos U2 :=
    hC_global_A2_distinct
  -- Linkage by construction: base.C_Q ⊆ C_global_A2 for every Q ∈ a4_v2.Qset
  have hC_Q_sub_global : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4_v2.Qset),
      (a4_v2.perSquare Q hQ).base.C_Q ⊆ C_global_A2 := by
    intro Q hQ
    rw [hC_global_eq]
    intro T hT
    simp only [Finset.mem_biUnion]
    refine' ⟨Q, hQ, _⟩
    simpa [hQ] using hT

  -- ### Construct old A4 from concrete a4_v2
  let a4 : A4_Output Δ δ s t ε :=
    { Qset := a4_v2.Qset
      perSquare := a4_v2.perSquare
      hQset_sset := a4_v2.hQset_sset
      K_uniform := a4_v2.K_uniform
      H_uniform := a4_v2.H_uniform
      C2_uniform := a4_v2.C2_uniform
      C_card_uniform := a4_v2.C_card_uniform
      hK_loss := a4_v2.hK_loss
      hC2_loss := a4_v2.hC2_loss
      hH_uniform_lower := a4_v2.hH_uniform_lower
      hH_uniform := a4_v2.hH_uniform
      hC_card_lower := a4_v2.hC_card_lower
      hC_card_upper := a4_v2.hC_card_upper
      hC_card_uniform := a4_v2.hC_card_uniform
      hQset_phys_growth := a4_v2.hQset_phys_growth }

  -- Center bounds for Qset subsets (proved from a1 ball data)
  have h_a1_center_bdd : ∀ Q ∈ a1.Qset, ‖squareCenter Δ Q‖ ≤ 2 :=
    center_norm_le_two_from_ball hΔ_pos hΔ_le_quarter hδ_eq a1 h_points_in_ball
  have h_a1_center_dist : ∀ (Q1 Q2 : CoarseSquare Δ), Q1 ∈ a1.Qset → Q2 ∈ a1.Qset →
      dist (squareCenter Δ Q1) (squareCenter Δ Q2) ≤ 3 :=
    center_dist_le_three_from_ball hΔ_pos hΔ_le_quarter hδ_eq a1 h_points_in_ball
  have h_a4_sub_a1 : a4.Qset ⊆ a1.Qset := hQ4_sub_a1

  -- ### Step 4: A4 → A5
  have hε_small : 55 * ε ≤ 2 * (t - s) := by linarith [hRKP_cond]
  classical
  have h_linkage : ∀ Q hQ, (a4.perSquare Q hQ).C_Q_pi ⊆ C_global_A2 :=
    fun Q hQ => by
      have h1 : (a4.perSquare Q hQ).C_Q_pi ⊆ (a4.perSquare Q hQ).base.C_Q :=
        (a4.perSquare Q hQ).hC_Q_pi_sub
      have h2 : (a4.perSquare Q hQ).base.C_Q ⊆ C_global_A2 := hC_Q_sub_global Q hQ
      exact Finset.Subset.trans h1 h2
  have h_a4_center_bdd : ∀ Q ∈ a4.Qset, ‖squareCenter Δ Q‖ ≤ 2 :=
    fun Q hQ => h_a1_center_bdd Q (h_a4_sub_a1 hQ)
  have h_a4_center_dist : ∀ (Q : CoarseSquare Δ), Q ∈ a4.Qset → ∀ (R : CoarseSquare Δ), R ∈ a4.Qset →
      dist (squareCenter Δ Q) (squareCenter Δ R) ≤ 3 :=
    fun Q hQ R hR => h_a1_center_dist Q R (h_a4_sub_a1 hQ) (h_a4_sub_a1 hR)
  have h_a4_card_upper : (a4.Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε) :=
    hQset_card_upper
  have h_2s_bound' : TwoSBoundWithLower Δ s t ε a4.Qset
      (fun Q hQ => (a4.perSquare Q hQ).C_Q_pi) C_global_A2
      (-2 * s + 210 * ε) :=
    h_2s_bound a4_v2 C_global_A2 h_linkage h_a4_center_bdd h_a4_center_dist h_a4_card_upper
  have h_a5_main : ∃ (out : A5_Output Δ δ s t ε),
      out.C_global_input = C_global_A2 ∧ out.Qset ⊆ a4.Qset :=
    A5_freeze_multiplicities_main Δ δ s t ε
      hΔ_pos hΔ_lt_half hs hs1 hst ht2 hε_pos hε_lt_one hε_small a4
      C_global_A2 hCglobal_A2_upper
      (hC_Q_pi_sub_global := h_linkage)
      (hT_full_upper := hT_full_upper a4_v2)
      (hC_global_A2_distinct := hC_global_A2_distinct')
      (h_2s_bound := h_2s_bound')
      (hQset_size_lower := hQset_card_lower)
      (hQset_size_upper := hQset_card_upper)
      hK_bound hΔ_3ε
  let a5 : A5_Output Δ δ s t ε := Classical.choose h_a5_main
  have h_a5_spec : a5.C_global_input = C_global_A2 ∧ a5.Qset ⊆ a4.Qset :=
    Classical.choose_spec h_a5_main
  have hC_input_eq : a5.C_global_input = C_global_A2 := h_a5_spec.1
  have hQ5_sub_Q4 : a5.Qset ⊆ a4.Qset := h_a5_spec.2
  have hQ5_sub_Q1 : a5.Qset ⊆ a1.Qset :=
    Finset.Subset.trans hQ5_sub_Q4 h_a4_sub_a1
  have hQ5_bdd : ∀ p ∈ a5.Qset.image (squareCenter Δ), ‖p‖ ≤ 2 := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨Q, hQ, rfl⟩
    exact h_a1_center_bdd Q (hQ5_sub_Q1 hQ)
  have hQ5_le_3 : ∀ (p1 : Plane) (hp1 : p1 ∈ a5.Qset.image (squareCenter Δ))
      (p2 : Plane) (hp2 : p2 ∈ a5.Qset.image (squareCenter Δ)), dist p1 p2 ≤ 3 := by
    intro p1 hp1 p2 hp2
    rcases Finset.mem_image.mp hp1 with ⟨Q1, hQ1, rfl⟩
    rcases Finset.mem_image.mp hp2 with ⟨Q2, hQ2, rfl⟩
    exact h_a1_center_dist Q1 Q2 (hQ5_sub_Q1 hQ1) (hQ5_sub_Q1 hQ2)

  -- ### Step 6: A5 → A7 (direct geometric energy path)
  have h_absorb_A7 : (6500 : ℝ) ≤ Real.rpow Δ (-ε) := by
    have h1 : Real.rpow Δ (ε / 4) ≤ 1 / 100 := h_small_delta
    have h2 : Real.rpow Δ ε ≤ (1 / 100 : ℝ)^4 := by
      have h3 : Real.rpow Δ ε = (Real.rpow Δ (ε / 4)) ^ 4 := by
        have h41 : Real.rpow Δ ε = Real.rpow Δ ((ε / 4) * (4 : ℝ)) := by
          congr 1 <;> ring
        have h42 : Real.rpow Δ ((ε / 4) * (4 : ℝ)) = (Real.rpow Δ (ε / 4)) ^ (4 : ℝ) :=
          Real.rpow_mul hΔ_pos.le (ε / 4) (4 : ℝ)
        have h43 : (Real.rpow Δ (ε / 4)) ^ (4 : ℝ) = (Real.rpow Δ (ε / 4)) ^ 4 :=
          Real.rpow_natCast (Real.rpow Δ (ε / 4)) 4
        exact h41.trans (h42.trans h43)
      rw [h3]
      have h_pos : 0 ≤ Real.rpow Δ (ε / 4) := Real.rpow_nonneg hΔ_pos.le (ε / 4)
      have h_ineq : (Real.rpow Δ (ε / 4)) ^ 4 ≤ (1 / 100 : ℝ) ^ 4 := by
        gcongr <;> linarith
      exact h_ineq
    have h5 : Real.rpow Δ (-ε) ≥ 10^8 := by
      have h6 : Real.rpow Δ (-ε) = (Real.rpow Δ ε)⁻¹ := by
        have h7 := Real.rpow_neg hΔ_pos.le ε
        simpa using h7
      rw [h6]
      have h_pos : 0 < Real.rpow Δ ε := Real.rpow_pos_of_pos hΔ_pos ε
      have h_pos2 : 0 < (1 / 100 : ℝ)^4 := by positivity
      have h8 : (Real.rpow Δ ε)⁻¹ ≥ ((1 / 100 : ℝ)^4)⁻¹ := by
        have h9 : 1 / ((1 / 100 : ℝ)^4) ≤ 1 / (Real.rpow Δ ε) :=
          one_div_le_one_div_of_le h_pos h2
        simpa [one_div] using h9
      have h9 : ((1 / 100 : ℝ)^4)⁻¹ = (10^8 : ℝ) := by norm_num
      rw [h9] at h8
      exact h8
    linarith
  have hδ_le_Δ : δ ≤ Δ := by
    rw [hδ_eq]
    have h : Δ ^ 2 ≤ Δ := by
      have h1 : 0 < Δ := hΔ_pos
      have h2 : Δ < 1 := hΔ_lt_one
      nlinarith
    exact h
  let a7 : A7_Output Δ δ s t ε :=
    A7_physical_full_output hΔ_pos hΔ_lt_half hs hs1 hst ht2 hε_pos
      hδ_pos hδ_le_Δ a5
      hQ5_bdd hQ5_le_3 h_log_absorb h_pack_absorb_A7 h_const_absorb_A7
      h_small_half h_small2 h_absorb_A7
      (fun T hT =>
        have h_in : T ∈ C_global_A2 := by
          rw [← hC_input_eq]
          exact a5.hC_global_sub hT
        h_slope_bound_A7 T h_in)

  -- ### Step 7: A7 → A8
  let a8 : A8_Output Δ δ s t ε :=
    A8_fine_fiber_popularity Δ δ s t ε hΔ_pos hΔ_lt_half hδ_eq hs hst hε_pos
      hΔ_small_A8
      (have h : (50 : ℝ) ≤ (2 * 10^13 : ℝ) := by norm_num
       le_trans h hΔ_coarse_absorb_A9)
      a7

  -- ### Step 8: A8 → A9
  let a9 : A9_Output Δ δ s t ε :=
    A9_affine_normalize Δ δ s t ε hΔ_pos hΔ_lt_half hδ_eq hs hs1 hst ht2 hε_pos
      hΔ_cover_A9 hΔ_packing_A9 hΔ_small_A9 hΔ_coarse_absorb_A9 hΔ_fine_absorb_A9 a8

  -- ### Step 9: A9 → A10
  have hQ0_nonempty : a9.Q0.Nonempty := a9.hQ0_sset.1
  have h_a9_τ : a9.τ = min (t - s) 1 := by
    rfl
  have hη_upper_gt_ε : ε < η_upper := by linarith
  have h_diff_pos : 0 < η_upper - 214 * ε := by linarith
  have h_allFine_upper' : (2000 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal
      (allFineParamsEuclidean a9) <
    ENNReal.ofReal (Real.rpow Δ (-(2 * s + η_upper))) :=
    allFineUpper_from_cells a9
      (hε_pos := hε_pos)
      (hη_upper_pos := hη_upper_pos)
      (hη_upper_gt_214ε := hη_upper_gt_214ε)
      (hδ_eq := hδ_eq)
      (hΔ_pos := hΔ_pos)
      (hΔ_lt_one := hΔ_lt_one)
      (hΔ_small := hΔ_small_allFine)
  have hC_fine_le : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a9.Q0),
      16 * (a9.perSquare Q hQ).C_fine_resc ≤ Real.rpow Δ (-501 * ε) :=
    fun Q hQ => (a9.perSquare Q hQ).hC_fine_resc_le_499
  exact A10_from_A9_full
    (a9 := a9)
    (hs := hs) (hs1 := hs1) (hst := hst) (ht2 := ht2)
    (hε_pos := hε_pos)
    (hη_upper_pos := hη_upper_pos)
    (hη_upper_gt_ε := hη_upper_gt_ε)
    (hδ_eq := hδ_eq)
    (hΔ_pos := hΔ_pos) (hΔ_lt_one := hΔ_lt_one)
    (hΔ_lt_third := hΔ_lt_third)
    (hΔ_lt_1_16 := hΔ_lt_1_16)
    (hε_le_one := hε_le_one)
    (hQ0_nonempty := hQ0_nonempty)
    (h_a9_τ := h_a9_τ)
    (h_absorb_shear := h_absorb_shear)
    (h_absorb_union := h_absorb_union)
    (h_allFine_upper := h_allFine_upper')
    (hC_fine_le := hC_fine_le)


end DirecretisedFurstenbergEstimate.AppendixA
