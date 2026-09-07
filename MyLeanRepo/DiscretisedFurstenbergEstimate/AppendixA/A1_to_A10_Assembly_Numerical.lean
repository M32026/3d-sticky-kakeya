module

/-
  A1→A10 Assembly Wrapper with Numerical Hypotheses (v2.5 interface).

  Takes a concrete `A4_Output_v2` (single source of truth) and destructures
  `AssemblyNumericalBounds` into the individual numerical bounds required by
  `A1_to_A10_assembly`.

  C_global_A2 is DERIVED from a4_v2.perSquare(Q).base.C_Q by biUnion,
  ensuring coarse and fine data refer to the same underlying objects.

  Whiteprint node: appendix_a_alternative / a1_to_a10_assembly_numerical
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AssemblyNumericalHypotheses
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A1_to_A10_Assembly
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AssemblyNumerical
open DirecretisedFurstenbergEstimate.QTTC_Assembly
open DirecretisedFurstenbergEstimate.AppendixA.A2
open DirecretisedFurstenbergEstimate.AppendixA4
open DirecretisedFurstenbergEstimate.AppendixA3
open DirecretisedFurstenbergEstimate.AppendixA5
open DirecretisedFurstenbergEstimate.AppendixA.A10
open DirecretisedFurstenbergEstimate.Lagoon

/-- A1→A10 assembly wrapper (v2.5): takes concrete `A4_Output_v2` and
    `AssemblyNumericalBounds`, produces `A10_Output`.

    C_global_A2 is DERIVED from a4_v2.perSquare(Q).base.C_Q by biUnion,
    ensuring coarse and fine data refer to the same underlying objects. -/
noncomputable def A1_to_A10_assembly_numerical
    {Δ δ s t ε η_upper : ℝ}
    -- Fixed source family: image(toAffineLine, config.T₀)
    (T_source : Finset FineTube)
    -- Concrete A4 output with source provenance (single source of truth)
    (a4_v2 : A4_Output_v2 Δ δ s t ε T_source)
    -- A1 output (needed for center-bound derivation from ball point data)
    (a1 : A1_Output Δ δ t s ε)
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
    -- Ball membership for center bounds
    (h_points_in_ball : ∀ Q hQ, (a1.points Q hQ : Set Plane) ⊆ Metric.closedBall 0 (1 + Real.sqrt 2 * δ / 2))
    -- Qset subset for center bounds
    (hQ4_sub_a1 : a4_v2.Qset ⊆ a1.Qset)
    -- Qset card bounds from A3 construction
    (hQset_card_lower : Real.rpow Δ (-t + 4 * ε) ≤ (a4_v2.Qset.card : ℝ))
    (hQset_card_upper : (a4_v2.Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε))
    -- Derived coarse family (biUnion of base.C_Q from a4_v2)
    (C_global_A2 : Finset CoarseTube)
    (hC_global_eq : C_global_A2 = a4_v2.Qset.biUnion (fun Q =>
      if h : Q ∈ a4_v2.Qset then (a4_v2.perSquare Q h).base.C_Q else ∅))
    -- C_global properties
    (hC_global_card : C_global_A2.card ≤ Real.rpow Δ (-2 * s - 3 * ε))
    (hC_global_A2_distinct : ∀ (U1 : CoarseTube), U1 ∈ C_global_A2 →
      ∀ (U2 : CoarseTube), U2 ∈ C_global_A2 → U1 ≠ U2 →
        parentCell Δ hΔ_pos U1 ≠ parentCell Δ hΔ_pos U2)
    (hRKP_cond : 576 * ε < t - s)
    -- Counter-assumptions
    (hT_full_upper : ∀ (a4 : A4_Output_v2 Δ δ s t ε T_source),
      (a5FullFineFamily Δ δ s t ε a4.Qset a4.perSquare).card ≤
        Real.rpow Δ (-(4 * s + 3 * ε)))
    (h_2s_bound :
      ∀ (a4 : A4_Output_v2 Δ δ s t ε T_source) (C_global_A2 : Finset AppendixA5.CoarseTube),
        (∀ Q hQ, (a4.perSquare Q hQ).C_Q_pi ⊆ C_global_A2) →
        (∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4.Qset), ‖Lagoon.squareCenter Δ Q‖ ≤ 2) →
        (∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4.Qset) (R : CoarseSquare Δ) (hR : R ∈ a4.Qset), dist (Lagoon.squareCenter Δ Q) (Lagoon.squareCenter Δ R) ≤ 3) →
        (a4.Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε) →
        TwoSBoundWithLower Δ s t ε a4.Qset
          (fun Q hQ => (a4.perSquare Q hQ).C_Q_pi) C_global_A2
          (-2 * s + 210 * ε))
    -- A7 slope bound for derived C_global
    (h_slope_bound_A7 : ∀ T, T ∈ C_global_A2 →
      (LemmaE.getDirV T) 1 ≠ 0 ∧ |tubeSlope T| ≤ 1 ∧ |tubeIntercept T| ≤ 3)
    -- A7 physical extraction conditions
    (h_pack_absorb_A7 : (MainAppendix.affineLine_packing_constant : ℝ) ≤ Real.rpow Δ (-ε))
    (h_const_absorb_A7 : (MainAppendix.affineLine_packing_constant : ℝ)^2 * ((800 * (53 : ℝ)) : ℝ)^s * (4 : ℝ)^t + 1 ≤ Real.rpow Δ (-ε))
    (h_log_absorb : 4 * Real.log (3 / Δ) + 1 ≤ Real.rpow Δ (-3 * ε))
    -- A10 conditions
    (hη_upper_pos : 0 < η_upper)
    (hη_upper_gt_214ε : 214 * ε < η_upper)
    (hΔ_small_allFine : (2000 : ℝ) * 2 < Real.rpow Δ (-(η_upper - 214 * ε)))
    -- Numerical bounds record
    (h_num : AssemblyNumericalBounds Δ s t ε) :
    A10_Output Δ s t ε :=
  A1_to_A10_assembly
    (a4_v2 := a4_v2)
    (a1 := a1)
    (h_points_in_ball := h_points_in_ball)
    (hQ4_sub_a1 := hQ4_sub_a1)
    (hQset_card_lower := hQset_card_lower)
    (hQset_card_upper := hQset_card_upper)
    (h_small_delta := h_num.h_small_delta)
    (hs := hs) (hs1 := hs1) (hst := hst) (ht2 := ht2)
    (hε_pos := hε_pos) (hε_lt_one := hε_lt_one) (hε_le_one := hε_le_one)
    (hδ_pos := hδ_pos) (hδ_eq := hδ_eq)
    (hΔ_pos := hΔ_pos) (hΔ_lt_one := hΔ_lt_one) (hΔ_lt_half := hΔ_lt_half)
    (hΔ_lt_third := hΔ_lt_third)
    (n := n) (m0 := m0) (hδ_dyadic := hδ_dyadic) (hΔ_dyadic := hΔ_dyadic)
    (hnm := hnm) (hm_pos := hm_pos)
    (hΔ_le_quarter := hΔ_le_quarter)
    (T_source := T_source)
    (C_global_A2 := C_global_A2)
    (hC_global_eq := hC_global_eq)
    (hC_global_card := hC_global_card)
    (hC_global_A2_distinct := hC_global_A2_distinct)
    (hRKP_cond := hRKP_cond)
    (hT_full_upper := hT_full_upper)
    (h_2s_bound := h_2s_bound)
    (hK_bound := h_num.hK_bound)
    (hΔ_3ε := h_num.hΔ_3ε)
    (h_small_half := h_num.h_small_half)
    (h_small2 := h_num.h_small2)
    (h_slope_bound_A7 := h_slope_bound_A7)
    (hΔ_small_A8 := h_num.hΔ_small_A8)
    (hΔ_cover_A9 := h_num.hΔ_cover_A9)
    (hΔ_packing_A9 := h_num.hΔ_packing_A9)
    (hΔ_small_A9 := h_num.hΔ_small_A9)
    (hΔ_coarse_absorb_A9 := h_num.hΔ_coarse_absorb_A9)
    (hΔ_fine_absorb_A9 := h_num.hΔ_fine_absorb_A9)
    (h_pack_absorb_A7 := h_pack_absorb_A7)
    (h_const_absorb_A7 := h_const_absorb_A7)
    (h_log_absorb := h_log_absorb)
    (hΔ_lt_1_16 := h_num.hΔ_lt_1_16)
    (hη_upper_pos := hη_upper_pos)
    (hη_upper_gt_214ε := hη_upper_gt_214ε)
    (hΔ_small_allFine := hΔ_small_allFine)
    (h_absorb_shear := h_num.h_absorb_shear)
    (h_absorb_union := h_num.h_absorb_union)

end DirecretisedFurstenbergEstimate.AppendixA
