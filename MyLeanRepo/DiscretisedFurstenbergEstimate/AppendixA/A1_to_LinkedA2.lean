module

/-
  A1 → LinkedA2Outputs packaging.

  Takes per-square A2 data (constructed by caller via `a2_per_square` with
  global T_Delta) and packages it into `LinkedA2Outputs` containing both
  old A2_Output and v2 A2_Output_v2 sharing the same per-square data.

  Whiteprint node: a1_to_linked_a2
  Dependencies: Interfaces
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA

open CoordinatePartition (swapLine)

/-- Package per-square A2 data into `LinkedA2Outputs`.

    The caller constructs `a2_perSquare` (typically via `A2.a2_per_square`
    with `T_Delta` overridden to the global cover) and provides all
    global provenance properties. -/
noncomputable def A1_to_linkedA2
    {Δ δ s t ε : ℝ}
    (a1 : A1_Output Δ δ t s ε)
    -- Per-square data with T_Delta already overridden to global cover
    (a2_perSquare : ∀ (Q : CoarseSquare Δ), Q ∈ a1.Qset → A2_SquareData Δ δ s t ε Q)
    -- Fixed source family
    (T_source : Finset FineTube)
    -- Ambient oriented tube family for provenance
    (T_oriented : Set AffineLine)
    -- Global separated coarse family
    (T_Delta : Finset CoarseTube)
    -- All per-square T_Delta fields equal the global cover
    (hT_Delta_eq : ∀ Q hQ, (a2_perSquare Q hQ).T_Delta = T_Delta)
    -- Per-square C_Q subset of global T_Delta
    (hC_Q_sub_TDelta : ∀ Q hQ, (a2_perSquare Q hQ).C_Q ⊆ T_Delta)
    -- Global coarse family cardinality upper bound (from counter-assumption)
    (hC_global_card_upper :
      ((a1.Qset.biUnion (fun Q =>
        if h : Q ∈ a1.Qset then (a2_perSquare Q h).C_Q else ∅)).card : ℝ) ≤
        Real.rpow Δ (-2 * s - 3 * ε))
    -- T_Delta provenance
    (hT_Delta_provenance : (T_Delta : Set CoarseTube) ⊆ Metric.cthickening (17 * Δ) (swapLine '' T_oriented))
    -- Per-square fine family inclusion in fixed source T_source
    (hT_Q_sub_Tsource : ∀ Q hQ p, (a2_perSquare Q hQ).T_Q p ⊆ T_source)
    -- Parent cell injectivity on global C_global
    (h_parent_injective : ∀ (hΔ_pos : 0 < Δ),
      ∀ (U1 : CoarseTube), U1 ∈ (a1.Qset.biUnion (fun Q =>
        if h : Q ∈ a1.Qset then (a2_perSquare Q h).C_Q else ∅)) →
      ∀ (U2 : CoarseTube), U2 ∈ (a1.Qset.biUnion (fun Q =>
        if h : Q ∈ a1.Qset then (a2_perSquare Q h).C_Q else ∅)) →
      U1 ≠ U2 → parentCell Δ hΔ_pos U1 ≠ parentCell Δ hΔ_pos U2) :
    LinkedA2Outputs Δ δ s t ε T_oriented T_source := by
  let a2_Qset := a1.Qset
  let a2_C_global : Finset CoarseTube :=
    a2_Qset.biUnion (fun Q => if h : Q ∈ a2_Qset then (a2_perSquare Q h).C_Q else ∅)
  let old : A2_Output Δ δ s t ε :=
    { Qset := a2_Qset
      perSquare := a2_perSquare
      C_global := a2_C_global
      T_Delta := T_Delta
      hC_global_eq := by rfl
      hQset_phys_growth := a1.hQset_phys_growth
      hT_Delta_eq := hT_Delta_eq
      hC_global_card_upper := hC_global_card_upper }
  let v2 : A2_Output_v2 Δ δ s t ε T_oriented :=
    { Qset := a2_Qset
      perSquare := a2_perSquare
      C_global := a2_C_global
      T_Delta := T_Delta
      hC_global_eq := by rfl
      hQset_phys_growth := a1.hQset_phys_growth
      hT_Delta_eq := hT_Delta_eq
      hT_Delta_provenance := hT_Delta_provenance
      hC_Q_sub_T_Delta := hC_Q_sub_TDelta }
  exact
    { Qset := a2_Qset
      perSquare := a2_perSquare
      old := old
      v2 := v2
      h_same_Qset := by rfl
      h_same_perSquare := by intro Q hQ; rfl
      h_v2_same_Qset := by rfl
      h_v2_same_perSquare := by intro Q hQ; rfl
      hC_Q_sub_TDelta := hC_Q_sub_TDelta
      hT_Q_sub_Tsource := hT_Q_sub_Tsource
      h_parent_injective := h_parent_injective }

end DirecretisedFurstenbergEstimate.AppendixA
