module

/-
  A1→A4_v2 Assembly: chains A2→A3→A4 and wraps into A4_Output_v2.

  Takes a LinkedA2Outputs (old + v2 sharing per-square data) and produces
  A4_Output_v2 with T_source provenance, plus hQ4_sub_a1.

  Whiteprint node: a1_to_a4_v2_assembly
  Dependencies: Interfaces, A2_to_A3_Bridge, A4_RKP
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_to_A3_Bridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A4_RKP
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Lagoon
open DirecretisedFurstenbergEstimate.AppendixA4

/-- Chain LinkedA2Outputs → A3 → A4 → A4_Output_v2.

    Returns a subtype of A4_Output_v2 with:
    - Qset ⊆ a1.Qset
    - Qset card lower bound: Δ^{-t+4ε} ≤ card
    - Qset card upper bound: card ≤ Δ^{-t-ε}

    The Qset is preserved through A2→A3→A4, so if linked.Qset = a1.Qset,
    the inclusion holds by construction. Card bounds come from a3. -/
noncomputable def linkedA2_to_A4_v2
    {Δ δ s t ε : ℝ}
    -- Fixed source family and ambient oriented family
    (T_source : Finset FineTube)
    (T_oriented : Set AffineLine)
    -- A1 output (for Qset comparison)
    (a1 : A1_Output Δ δ t s ε)
    -- Linked A2 outputs (old + v2 sharing per-square data)
    (linked : LinkedA2Outputs Δ δ s t ε T_oriented T_source)
    -- Qset equality (typically linked.Qset = a1.Qset)
    (hQset_eq : linked.Qset = a1.Qset)
    -- =====================================================================
    -- A2→A3 bridge parameters
    -- =====================================================================
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (ht_pos : 0 < t) (ht_lt_two : t < 2)
    (hst : s < t)
    -- A3 numerical conditions
    (hΔ_small : 50000 * (Real.log (1 / Δ) + 1)^3 ≤ Real.rpow Δ (-ε))
    (hΔ_absorb1 : 8 * (MainAppendix.affineLine_packing_constant : ℝ) * ((800 * (54 : ℝ)) : ℝ)^s ≤ Real.rpow Δ (-2 * ε))
    (hΔ_absorb2 : (8 : ℝ) ≤ Real.rpow Δ (s - t - 22 * ε))
    (hs_ge_12ε : 12 * ε ≤ s)
    (hKpack_le_ε : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ linked.old.Qset),
      (linked.old.perSquare Q hQ).K_pack ≤ Real.rpow Δ (-ε))
    -- Energy bound for Qset centers
    (h_energy_all : ∑ p ∈ (linked.old.Qset.image (squareCenter Δ)),
        ∑ q ∈ (linked.old.Qset.image (squareCenter Δ)).erase p, Real.rpow (dist p q) (-s) ≤
        Real.rpow Δ (-12 * ε) * ((linked.old.Qset.image (squareCenter Δ)).card : ℝ)^2)
    -- =====================================================================
    -- A4 RKP parameters
    -- =====================================================================
    (hΔ_small_rkp : Real.rpow Δ ε ≤ 1 / 81)
    (hΔ_small_pack : (4000 : ENNReal) * (affinePackingM : ENNReal) ≤
        ENNReal.ofReal (Real.rpow Δ (-ε)))
    (hδ_eq : δ = Δ ^ 2)
    (ht : t ≤ 2)
    (hRKP_at_Δ : ∀ (P : Set Plane) (directions : Set ℝ),
      InUnitSquare P →
      directions ⊆ Set.Icc (-1 : ℝ) 1 →
      IsDeltaSSet Δ t (Real.rpow Δ (-48 * ε)) P →
      IsDeltaSSet Δ s (Real.rpow Δ (-48 * ε)) directions →
      ENNReal.ofReal (Real.rpow Δ (48 * ε - t)) ≤ _root_.Ncover Δ P →
      _root_.Ncover Δ P ≤ ENNReal.ofReal (Real.rpow Δ (-t - 48 * ε)) →
      ENNReal.ofReal (Real.rpow Δ (48 * ε - s)) ≤ _root_.Ncover Δ directions →
      _root_.Ncover Δ directions ≤ ENNReal.ofReal (Real.rpow Δ (-s - 29 * ε)) →
      ∃ goodDirections : Set ℝ,
        goodDirections ⊆ directions ∧
        _root_.Ncover Δ directions ≤ 2 * _root_.Ncover Δ goodDirections ∧
        ∀ σ ∈ goodDirections,
          ∀ P' : Set Plane, P' ⊆ P →
            ENNReal.ofReal (Real.rpow Δ (48 * ε)) * _root_.Ncover Δ P ≤ _root_.Ncover Δ P' →
            ∃ X : Set ℝ,
              X ⊆ RobustKaufmanProjection.affineProjection σ P' ∧
              IsDeltaSSet Δ s (Real.rpow Δ (-576 * ε)) X ∧
              ENNReal.ofReal (Real.rpow Δ (576 * ε - s)) ≤ _root_.Ncover Δ X)
    : {a4_v2 : A4_Output_v2 Δ δ s t ε T_source //
        a4_v2.Qset ⊆ a1.Qset ∧
        Real.rpow Δ (-t + 4 * ε) ≤ (a4_v2.Qset.card : ℝ) ∧
        (a4_v2.Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε) ∧
        ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4_v2.Qset),
          (a4_v2.perSquare Q hQ).base.T_Delta = linked.old.T_Delta} := by
  -- Step 1: A2 (old) → A3
  have hQset_eq_old : linked.old.Qset = a1.Qset := by
    rw [linked.h_same_Qset, hQset_eq]
  have hC_Q_sub_global : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ linked.old.Qset),
      (linked.old.perSquare Q hQ).C_Q ⊆ linked.old.C_global := by
    intro Q hQ
    rw [linked.old.hC_global_eq]
    intro T hT
    simp only [Finset.mem_biUnion]
    refine' ⟨Q, hQ, _⟩
    simpa [hQ] using hT
  let a3 : A3_Output Δ δ s t ε :=
    A2_to_A3_bridge a1 linked.old
      hΔ_pos hΔ_lt_half hδ_pos hδ_le_Δ
      hε_pos hε_lt_one hs_pos hs_lt_one ht_pos ht_lt_two hst
      hΔ_small hΔ_absorb1 hΔ_absorb2 hs_ge_12ε
      hKpack_le_ε
      hQset_eq_old
      hC_Q_sub_global
      h_energy_all

  -- Step 2: A3 → A4 (old)
  let a4 : A4_Output Δ δ s t ε :=
    A4_rkp_refinement Δ δ s t ε hΔ_pos hΔ_lt_half
      hΔ_small_rkp hΔ_small_pack hδ_eq
      hs_pos hs_lt_one hst hε_pos ht
      hRKP_at_Δ a3

  -- Step 3: Prove a5FullFineFamily ⊆ T_source from linked.hT_Q_sub_Tsource.
  -- Base A2_SquareData is preserved through A3→A4:
  --   (a4.perSquare Q hQ).base = a3.perSquare Q hQ = linked.old.perSquare Q hQ_old
  --   = linked.perSquare Q hQ_linked
  have h7_sub : a3.Qset ⊆ linked.old.Qset := by
    dsimp only [a3, A2_to_A3_bridge, AppendixA3.A3_uniformize_canonical]
    exact Finset.filter_subset _ _
  have hT_full_subset_source' :
      a5FullFineFamily Δ δ s t ε a4.Qset a4.perSquare ⊆ T_source := by
    intro T hT
    have h1 : ∃ (Q' : {Q // Q ∈ a4.Qset}), T ∈ (a4.perSquare Q'.val Q'.property).base.P_Q.biUnion
        (fun p => (a4.perSquare Q'.val Q'.property).base.T_Q p) := by
      simpa [a5FullFineFamily, Finset.mem_biUnion] using hT
    rcases h1 with ⟨Q', h2⟩
    let Q : CoarseSquare Δ := Q'.val
    let hQ_a4 : Q ∈ a4.Qset := Q'.property
    have h3 : ∃ (p : Plane), p ∈ (a4.perSquare Q hQ_a4).base.P_Q ∧
        T ∈ (a4.perSquare Q hQ_a4).base.T_Q p := by
      simpa [Finset.mem_biUnion] using h2
    rcases h3 with ⟨p, hp, hT_mem⟩
    have hQ_a3 : Q ∈ a3.Qset := by
      have h_eq : a4.Qset = a3.Qset := by rfl
      rw [h_eq] at hQ_a4; exact hQ_a4
    have hQ_old : Q ∈ linked.old.Qset := h7_sub hQ_a3
    have hQ_linked : Q ∈ linked.Qset := by
      have h3 : linked.old.Qset = linked.Qset := linked.h_same_Qset
      rw [←h3]; exact hQ_old
    have h_base_TQ_eq : (a4.perSquare Q hQ_a4).base.T_Q p =
        (linked.perSquare Q hQ_linked).T_Q p := by
      have h1 : (a4.perSquare Q hQ_a4).base = a3.perSquare Q hQ_a3 := by rfl
      have h2 : a3.perSquare Q hQ_a3 = linked.old.perSquare Q hQ_old := by
        dsimp only [a3, A2_to_A3_bridge, AppendixA3.A3_uniformize_canonical]
        <;> congr
      have h3 : linked.old.perSquare Q hQ_old = linked.perSquare Q hQ_linked :=
        linked.h_same_perSquare Q hQ_linked
      rw [h1, h2, h3]
    rw [h_base_TQ_eq] at hT_mem
    exact linked.hT_Q_sub_Tsource Q hQ_linked p hT_mem

  -- Step 4: Wrap A4_Output into A4_Output_v2
  let a4_v2 : A4_Output_v2 Δ δ s t ε T_source :=
    { Qset := a4.Qset
      perSquare := a4.perSquare
      hQset_sset := a4.hQset_sset
      K_uniform := a4.K_uniform
      H_uniform := a4.H_uniform
      C2_uniform := a4.C2_uniform
      C_card_uniform := a4.C_card_uniform
      hK_loss := a4.hK_loss
      hC2_loss := a4.hC2_loss
      hH_uniform_lower := a4.hH_uniform_lower
      hH_uniform := a4.hH_uniform
      hC_card_lower := a4.hC_card_lower
      hC_card_upper := a4.hC_card_upper
      hC_card_uniform := a4.hC_card_uniform
      hQset_phys_growth := a4.hQset_phys_growth
      hT_full_subset_source := hT_full_subset_source' }

  -- Step 5: Prove a4_v2.Qset ⊆ a1.Qset
  -- A4 preserves Qset from A3; A3 selects Q0 ⊆ a2.Qset
  have h3 : linked.old.Qset = linked.Qset := linked.h_same_Qset
  have h4 : linked.Qset = a1.Qset := hQset_eq
  have h5 : a4_v2.Qset = a4.Qset := by rfl
  have h6 : a4.Qset = a3.Qset := by rfl
  have hQ4_sub_a1 : a4_v2.Qset ⊆ a1.Qset := by
    rw [h5, h6]
    rw [h3, h4] at h7_sub
    exact h7_sub

  -- Step 6: Card bounds from A3 (Qset preserved through A3→A4)
  have hQ4_eq_a3 : a4_v2.Qset = a3.Qset := by
    rw [h5, h6]
  have hQset_card_lower : Real.rpow Δ (-t + 4 * ε) ≤ (a4_v2.Qset.card : ℝ) := by
    rw [hQ4_eq_a3]
    exact a3.hQset_card_lower
  have hQset_card_upper : (a4_v2.Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε) := by
    rw [hQ4_eq_a3]
    exact a3.hQset_card_upper

  -- Step 7: Base T_Delta preservation through A2→A3→A4
  have h_base_T_Delta_eq : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4_v2.Qset),
      (a4_v2.perSquare Q hQ).base.T_Delta = linked.old.T_Delta := by
    intro Q hQ
    have hQ_a4 : Q ∈ a4.Qset := by
      have h_eq : a4_v2.Qset = a4.Qset := by rfl
      rw [h_eq] at hQ; exact hQ
    have hQ_a3 : Q ∈ a3.Qset := by
      have h_eq : a4.Qset = a3.Qset := by rfl
      rw [h_eq] at hQ_a4; exact hQ_a4
    have hQ_old : Q ∈ linked.old.Qset := h7_sub hQ_a3
    have h1 : (a4_v2.perSquare Q hQ).base = a3.perSquare Q hQ_a3 := by rfl
    have h2 : a3.perSquare Q hQ_a3 = linked.old.perSquare Q hQ_old := by
      dsimp only [a3, A2_to_A3_bridge, AppendixA3.A3_uniformize_canonical]
      <;> congr
    rw [h1, h2]
    exact linked.old.hT_Delta_eq Q hQ_old

  exact ⟨a4_v2, hQ4_sub_a1, hQset_card_lower, hQset_card_upper, h_base_T_Delta_eq⟩

end DirecretisedFurstenbergEstimate.AppendixA
