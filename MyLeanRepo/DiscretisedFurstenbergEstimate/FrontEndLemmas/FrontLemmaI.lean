module

/-
  FrontLemmaI_v2 — Final contradiction (I lemma) consuming HOutput.

  Takes GOutput + HOutput + downstream data, returns False by calling
  uniform_appendix_A_alternative.

  Does NOT rebuild C-global — uses h.C_global_A2 and its properties directly.
  Does NOT ask for dyadic slope/intercept facts — those were used by H.

  Whiteprint node: front_end_lemmas / final_contradiction
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.UniformAppendixAAlternative
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A1_to_A4_v2_Assembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.TwoSBoundHelper
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.TDeltaGlobalConstruction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AssemblyNumericalHypotheses
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.GOutput
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable


noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas.FrontEndComposition

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA
open DirecretisedFurstenbergEstimate.AppendixA5
open DirecretisedFurstenbergEstimate.AssemblyNumerical
open DirecretisedFurstenbergEstimate.ProductContradiction
open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
open DiscretisedFurstenbergEstimate.CombiningTheorem

/--
  Output of the H lemma (A2→A4 assembly + C_global construction).

  Consumes GOutput and produces:
  - a4_v2 with Qset bounds
  - C_global_A2 with ALL properties (eq, sub_T_Delta, card, distinct, slope)
  - per-square fixed-T_Delta preservation
  - h_points_in_ball' (derived from a1)
-/
structure HOutput
    {n m : ℕ} {hnm : m ≤ n} {Δ δ_n s u ε : ℝ} {T_oriented : Set AffineLine}
    (g : GOutput n m hnm Δ δ_n s u ε T_oriented) where

  -- A4 output
  a4_v2 : A4_Output_v2 Δ δ_n s u ε g.T_source
  hQ4_sub_a1 : a4_v2.Qset ⊆ g.a1.Qset
  hQset_card_lower : Real.rpow Δ (-u + 4 * ε) ≤ (a4_v2.Qset.card : ℝ)
  hQset_card_upper : (a4_v2.Qset.card : ℝ) ≤ Real.rpow Δ (-u - ε)

  -- C_global coarse family
  C_global_A2 : Finset AppendixA.CoarseTube
  hC_global_eq : C_global_A2 = a4_v2.Qset.biUnion (fun Q =>
      if h : Q ∈ a4_v2.Qset then (a4_v2.perSquare Q h).base.C_Q else ∅)
  hC_global_sub_T_Delta : C_global_A2 ⊆ g.T_Delta
  hC_global_card : (C_global_A2.card : ℝ) ≤ Real.rpow Δ (-2 * s - 3 * ε)
  hC_global_A2_distinct : ∀ (U1 : AppendixA.CoarseTube), U1 ∈ C_global_A2 →
      ∀ (U2 : AppendixA.CoarseTube), U2 ∈ C_global_A2 → U1 ≠ U2 →
        parentCell Δ g.hΔ_pos U1 ≠ parentCell Δ g.hΔ_pos U2

  -- Slope/intercept bounds
  h_slope_bound_A7 : ∀ (T : AppendixA.CoarseTube), T ∈ C_global_A2 →
      (LemmaE.getDirV T) 1 ≠ 0 ∧ |tubeSlope T| ≤ 1 ∧ |tubeIntercept T| ≤ 3

  -- Per-square fixed-T_Delta preservation
  h_perSquare_T_Delta_eq : ∀ (Q : AppendixA.CoarseSquare Δ) (hQ : Q ∈ a4_v2.Qset),
      (a4_v2.perSquare Q hQ).base.T_Delta = g.T_Delta

  -- A1 point bounds (derived by H from a1)
  h_points_in_ball' : ∀ Q hQ, (g.a1.points Q hQ : Set EuclideanPlane) ⊆
      Metric.closedBall 0 (1 + Real.sqrt 2 * δ_n / 2)

/-- Final contradiction (I lemma): consumes GOutput + HOutput + downstream
    bounds and calls uniform_appendix_A_alternative → False.

    # Inputs
    - g : GOutput (A1, source family, provenance, numerical)
    - h : HOutput g (A4, C_global with all properties)
    - t dimension bridge (s < t ≤ u)
    - hT_full_upper: fine family upper bound
    - h_2s_bound: two-s bound from A5
    - h_pack_absorb_A7: affineLine_packing_constant ≤ Δ^{-ε}
      (derivable from g.h_num_u.h_const_absorb_A7, but taken as input for simplicity)
    - product axiom parameters
    - h_log_absorb
-/
lemma final_contradiction_I
    {n m : ℕ} {hnm : m ≤ n} {Δ δ_n s t u ε : ℝ} {T_oriented : Set AffineLine}
    (g : GOutput n m hnm Δ δ_n s u ε T_oriented)
    (h : HOutput g)
    -- Scale equalities (not in GOutput)
    (hΔ_eq : Δ = DiscretisedFurstenbergEstimate.dyadicDelta m)
    (hδ_eq : δ_n = DiscretisedFurstenbergEstimate.dyadicDelta n)
    (hΔ_lt_third : Δ < 1 / 3)
    -- t dimension bridge
    (ht_pos : 0 < t) (ht_lt_two : t < 2) (hst : s < t) (hu_t : t ≤ u)
    -- Downstream bounds
    (hT_full_upper : ∀ (a4 : A4_Output_v2 Δ δ_n s u ε g.T_source),
        (a5FullFineFamily Δ δ_n s u ε a4.Qset a4.perSquare).card ≤
          Real.rpow Δ (-(4 * s + 3 * ε)))
    (h_2s_bound : ∀ (a4 : A4_Output_v2 Δ δ_n s u ε g.T_source)
        (C_global_A2 : Finset AppendixA.CoarseTube),
        (∀ (Q : AppendixA.CoarseSquare Δ) (hQ : Q ∈ a4.Qset),
          (a4.perSquare Q hQ).C_Q_pi ⊆ C_global_A2) →
        (∀ (Q : AppendixA.CoarseSquare Δ) (hQ : Q ∈ a4.Qset),
          ‖Lagoon.squareCenter Δ Q‖ ≤ 2) →
        (∀ (Q : AppendixA.CoarseSquare Δ) (hQ : Q ∈ a4.Qset)
          (R : AppendixA.CoarseSquare Δ) (hR : R ∈ a4.Qset),
          dist (Lagoon.squareCenter Δ Q) (Lagoon.squareCenter Δ R) ≤ 3) →
        (a4.Qset.card : ℝ) ≤ Real.rpow Δ (-u - ε) →
        TwoSBoundWithLower Δ s u ε a4.Qset
          (fun Q hQ => (a4.perSquare Q hQ).C_Q_pi) C_global_A2
          (-2 * s + 210 * ε))
    -- Packing absorption
    (h_pack_absorb_A7 : (MainAppendix.affineLine_packing_constant : ℝ) ≤
        Real.rpow Δ (-ε))
    -- Product axiom parameters
    (η_axiom δ₀_axiom : ℝ)
    (hη_axiom_pos : 0 < η_axiom)
    (hδ₀_axiom_pos : 0 < δ₀_axiom)
    (hΔ_le_δ₀_axiom : Δ ≤ δ₀_axiom)
    (h_absorb_Y : (9 * 3 ^ (t - s)) * Real.rpow Δ (-10000 * ε) ≤
        Real.rpow Δ (-η_axiom))
    (h_absorb_X : (729 * 50 ^ s) * Real.rpow Δ (-600 * ε) ≤
        Real.rpow Δ (-η_axiom))
    (h_absorb_T : (81 ^ 3 * 16 * 50 ^ s) * Real.rpow Δ (-600 * ε) ≤
        Real.rpow Δ (-η_axiom))
    (hA7 : ProductContradiction.ProductPropBoundedTheorem s (min (t - s) 1)
        η_axiom δ₀_axiom)
    (η_upper : ℝ)
    (hη_upper_pos : 0 < η_upper)
    (h214ε_lt : 214 * ε < η_upper)
    (hΔ_small_allFine : (2000 : ℝ) * 2 <
        Real.rpow Δ (-(η_upper - 214 * ε)))
    (hη_upper_lt : η_upper < η_axiom)
    -- Numerical
    (h_log_absorb : 4 * Real.log (3 / Δ) + 1 ≤ Real.rpow Δ (-3 * ε))
    : False := by

  -- Derive h_const_absorb_A7 from g.h_num_u
  have h_const_absorb_A7 : (MainAppendix.affineLine_packing_constant : ℝ)^2 *
      ((800 * (53 : ℝ)) : ℝ)^s * (4 : ℝ)^u + 1 ≤ Real.rpow Δ (-ε) := by
    have h1 : ((800 * (53 : ℝ)) : ℝ)^s ≤ (800 * (53 : ℝ)) := by
      have h11 : (1 : ℝ) < (800 * (53 : ℝ)) := by norm_num
      have h12 : s ≤ 1 := by linarith [g.hs_lt_one]
      have h13 : ((800 * (53 : ℝ)) : ℝ)^s ≤ ((800 * (53 : ℝ)) : ℝ)^(1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h11.le h12
      have h14 : ((800 * (53 : ℝ)) : ℝ)^(1 : ℝ) = (800 * (53 : ℝ)) := by simp
      rw [h14] at h13
      exact h13
    have h2 : (4 : ℝ)^u ≤ (16 : ℝ) := by
      have h21 : (1 : ℝ) < (4 : ℝ) := by norm_num
      have h22 : u ≤ 2 := by linarith [g.h_run_lt_two]
      have h23 : (4 : ℝ)^u ≤ (4 : ℝ)^(2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h21.le h22
      have h24 : (4 : ℝ)^(2 : ℝ) = (16 : ℝ) := by norm_num
      rw [h24] at h23
      exact h23
    have h3 : ((800 * (53 : ℝ)) : ℝ)^s * (4 : ℝ)^u ≤
        ((800 * (53 : ℝ)) : ℝ) * (16 : ℝ) := by
      have h4 : 0 ≤ ((800 * (53 : ℝ)) : ℝ)^s := by positivity
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have h5 : (MainAppendix.affineLine_packing_constant : ℝ)^2 *
        ((800 * (53 : ℝ)) : ℝ)^s * (4 : ℝ)^u + 1 ≤
        (MainAppendix.affineLine_packing_constant : ℝ)^2 *
        ((800 * (53 : ℝ)) : ℝ) * (16 : ℝ) + 1 := by
      have h6 : 0 ≤ (MainAppendix.affineLine_packing_constant : ℝ)^2 := by positivity
      gcongr <;> linarith
    exact le_trans h5 g.h_num_u.h_const_absorb_A7

  have hε_le_one : ε ≤ 1 := by linarith [g.hε_lt_one]
  have hΔ_lt_one : Δ < 1 := by linarith [g.hΔ_lt_half]

  -- Call uniform_appendix_A_alternative → False
  exact uniform_appendix_A_alternative
    hnm
    g.hs_pos g.hs_lt_one ht_pos ht_lt_two hst
    hΔ_eq hδ_eq
    g.hΔ_pos g.hΔ_lt_half g.hδ_n_pos g.hδ_le_D g.hε_pos g.hε_lt_one hε_le_one
    g.hδ_n_eq hΔ_lt_one hΔ_lt_third g.h_small_eps
    hu_t g.h_run_lt_two
    g.a1 h.h_points_in_ball'
    g.T_source h.a4_v2 h.hQ4_sub_a1 h.hQset_card_lower h.hQset_card_upper
    h.C_global_A2 h.hC_global_eq h.hC_global_card h.hC_global_A2_distinct
    g.hRKP_cond_u hT_full_upper h_2s_bound
    h.h_slope_bound_A7 h_pack_absorb_A7 h_const_absorb_A7
    η_axiom δ₀_axiom hη_axiom_pos hδ₀_axiom_pos hΔ_le_δ₀_axiom
    h_absorb_Y h_absorb_X h_absorb_T
    hA7 η_upper hη_upper_pos h214ε_lt hΔ_small_allFine hη_upper_lt
    g.h_num_u h_log_absorb

end DirecretisedFurstenbergEstimate.FrontEndLemmas.FrontEndComposition
