module

/-
  H lemma: A2→A4 assembly consuming GOutput and producing HOutput.

  Chains per-square A2 construction → A1_to_linkedA2 → linkedA2_to_A4_v2,
  then constructs C_global_A2 with all required provenance properties.

  Does NOT reconstruct A1 or source families — uses g.a1, g.T_source, etc.

  Whiteprint node: front_end_lemmas / H_assembly
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.GOutput
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.FrontLemmaI
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_FromA1
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A1_to_LinkedA2
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A1_to_A4_v2_Assembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_to_A3_Bridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.TDeltaGlobalConstruction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AssemblyNumericalHypotheses
public import MyLeanRepo.DiscretisedFurstenbergEstimate.SnappingSSetTransfer
public import MyLeanRepo.OSWPrelude

@[expose] public section


open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas.FrontEndComposition

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA
open DirecretisedFurstenbergEstimate.AppendixA.A2
open DirecretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
open DirecretisedFurstenbergEstimate.AppendixA.TDeltaGlobal
open DirecretisedFurstenbergEstimate.Lagoon
open DirecretisedFurstenbergEstimate.AssemblyNumerical
open DirecretisedFurstenbergEstimate.QTTC_Assembly (C_PACK)
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction (ParameterSelectionQTTC)
open DirecretisedFurstenbergEstimate.AppendixA.A2TypedQTTCAdapter (GEOM_CONST)
open CoordinatePartition (swapLine)

/-- H: assemble A2→A4 from GOutput.

    Takes additional parameters not in GOutput:
    - hQTTC_full: full QTTC theorem
    - h12ε: 12ε ≤ s
    - h_points_in_ball': point bound derived from NiceConfiguration
-/
def front_H
    {n m : ℕ} {hnm : m ≤ n} {Δ δ_n s u ε : ℝ} {T_oriented : Set AffineLine}
    (g : GOutput n m hnm Δ δ_n s u ε T_oriented)
    -- Exponent constraint for A3
    (h12ε : 12 * ε ≤ s)
    -- Point bound (derived from NiceConfiguration, not from a1 alone)
    (h_points_in_ball' : ∀ Q hQ, (g.a1.points Q hQ : Set EuclideanPlane) ⊆
        Metric.closedBall 0 (1 + Real.sqrt 2 * δ_n / 2))
    : HOutput g := by

  -- Step 1: RKP specialized to Δ
  have hRKP_at_Delta : ∀ (P : Set EuclideanPlane) (directions : Set ℝ),
      InUnitSquare P →
      directions ⊆ Set.Icc (-1 : ℝ) 1 →
      IsDeltaSSet Δ u (Real.rpow Δ (-48 * ε)) P →
      IsDeltaSSet Δ s (Real.rpow Δ (-48 * ε)) directions →
      ENNReal.ofReal (Real.rpow Δ (48 * ε - u)) ≤ _root_.Ncover Δ P →
      _root_.Ncover Δ P ≤ ENNReal.ofReal (Real.rpow Δ (-u - 48 * ε)) →
      ENNReal.ofReal (Real.rpow Δ (48 * ε - s)) ≤ _root_.Ncover Δ directions →
      _root_.Ncover Δ directions ≤ ENNReal.ofReal (Real.rpow Δ (-s - 29 * ε)) →
      ∃ goodDirections : Set ℝ,
        goodDirections ⊆ directions ∧
        _root_.Ncover Δ directions ≤ 2 * _root_.Ncover Δ goodDirections ∧
        ∀ σ ∈ goodDirections,
          ∀ P' : Set EuclideanPlane, P' ⊆ P →
            ENNReal.ofReal (Real.rpow Δ (48 * ε)) * _root_.Ncover Δ P ≤ _root_.Ncover Δ P' →
            ∃ X : Set ℝ,
              X ⊆ RobustKaufmanProjection.affineProjection σ P' ∧
              IsDeltaSSet Δ s (Real.rpow Δ (-576 * ε)) X ∧
              ENNReal.ofReal (Real.rpow Δ (576 * ε - s)) ≤ _root_.Ncover Δ X :=
    g.hRKP_u.2.2 Δ g.hΔ_pos (by linarith [g.hΔ_lt_half]) g.hΔ_le_RKP

  -- Step 2: Energy bound
  have h_energy_all : ∑ p ∈ (g.a1.Qset.image (squareCenter Δ)),
      ∑ q ∈ (g.a1.Qset.image (squareCenter Δ)).erase p,
        Real.rpow (dist p q) (-s) ≤
      Real.rpow Δ (-12 * ε) * ((g.a1.Qset.image (squareCenter Δ)).card : ℝ)^2 :=
    energy_all_from_a1_exact
      g.hΔ_pos g.hΔ_lt_half g.hδ_n_pos g.hδ_n_eq
      g.h_small_eps g.hε_pos
      g.hs_pos g.hs_lt_one g.hu_pos g.h_run_lt_two g.hsu
      g.a1 g.h_center_bdd g.hQset_nonempty g.h_absorb_energy

  -- Unfold QTTC once (ParameterSelectionQTTC is [irreducible])
  have hQTTC_unfolded : ParameterSelectionQTTC s g.A := g.hQTTC
  simp only [ParameterSelectionQTTC, GEOM_CONST] at hQTTC_unfolded

  -- Step 3: Per-square A2 data
  let a2_perSquare : ∀ (Q : CoarseSquare Δ), Q ∈ g.a1.Qset →
      A2_SquareData Δ δ_n s u ε Q :=
    fun Q hQ =>
      a2_square_data_from_a1_auto
        (t := u) (u := u)
        g.hδ_eq g.hΔ_eq hnm g.hm_pos
        g.a1 Q hQ
        g.K_pack g.hK_pack_eq
        g.A g.hA_one hQTTC_unfolded g.h_small_A2
        g.hs_pos g.hs_lt_one
        g.hδ_n_eq g.h_small_eps g.hε_pos g.hu_pos.le
        g.T_source (fun p _ => g.hT_sub_source p)
        g.T_Delta g.hT_Delta_eq
        g.hδ_le_quarter g.hδ_n_pos

  -- Helper: per-square T_Delta equals global T_Delta (via projection lemma)
  have h_a2_T_Delta : ∀ Q hQ, (a2_perSquare Q hQ).T_Delta = g.T_Delta :=
    fun Q hQ =>
      a2_square_data_from_a1_auto_T_Delta_eq
        (t := u) (u := u) (n := n) (m0 := m)
        g.hδ_eq g.hΔ_eq hnm g.hm_pos
        g.a1 Q hQ
        g.K_pack g.hK_pack_eq
        g.A g.hA_one hQTTC_unfolded
        g.h_small_A2
        g.hs_pos g.hs_lt_one
        g.hδ_n_eq g.h_small_eps g.hε_pos g.hu_pos.le
        g.T_source (fun p _ => g.hT_sub_source p)
        g.T_Delta g.hT_Delta_eq
        g.hδ_le_quarter g.hδ_n_pos

  -- Helper: per-square T_original equals a1.tubes (via projection lemma)
  have h_a2_T_original : ∀ Q hQ p, (a2_perSquare Q hQ).T_original p = g.a1.tubes p :=
    fun Q hQ p =>
      a2_square_data_from_a1_auto_T_original_eq
        (t := u) (u := u) (n := n) (m0 := m)
        g.hδ_eq g.hΔ_eq hnm g.hm_pos
        g.a1 Q hQ
        g.K_pack g.hK_pack_eq
        g.A g.hA_one hQTTC_unfolded
        g.h_small_A2
        g.hs_pos g.hs_lt_one
        g.hδ_n_eq g.h_small_eps g.hε_pos g.hu_pos.le
        g.T_source (fun p _ => g.hT_sub_source p)
        g.T_Delta g.hT_Delta_eq
        g.hδ_le_quarter g.hδ_n_pos
        p

  -- Step 4: C_global_pre and cardinality bound
  let C_global_pre : Finset AppendixA.CoarseTube :=
    @Finset.biUnion (CoarseSquare Δ) AppendixA.CoarseTube (fun a b => Subtype.instDecidableEq a b)
      g.a1.Qset (fun Q => if h : Q ∈ g.a1.Qset then (a2_perSquare Q h).C_Q else ∅)

  have hC_global_pre_sub : C_global_pre ⊆ g.T_Delta := by
    intro c hc
    have h_mem : ∃ (Q : CoarseSquare Δ), Q ∈ g.a1.Qset ∧
        c ∈ (if h : Q ∈ g.a1.Qset then (a2_perSquare Q h).C_Q else ∅) := by
      simpa [C_global_pre, Finset.mem_biUnion] using hc
    rcases h_mem with ⟨Q, hQ, hcQ⟩
    have h1 : c ∈ (a2_perSquare Q hQ).C_Q := by simpa [hQ] using hcQ
    have h2 : (a2_perSquare Q hQ).C_Q ⊆ (a2_perSquare Q hQ).T_Delta :=
      (a2_perSquare Q hQ).hC_Q_sub_TDelta
    have h3 : (a2_perSquare Q hQ).T_Delta = g.T_Delta := h_a2_T_Delta Q hQ
    rw [h3] at h2
    exact h2 h1

  have hC_global_pre_sub' : C_global_pre ⊆ T_Delta_global hnm g.T_source := by
    rw [←g.hT_Delta_eq]
    exact hC_global_pre_sub

  have h_exp_eq : -(2 * s + 3 * ε) = -2 * s - 3 * ε := by ring
  have h_dyadic' : (T_Delta_global_dyadic hnm g.T_source).card ≤
      Real.rpow Δ (-2 * s - 3 * ε) := by
    rw [←h_exp_eq]
    exact g.h_dyadic

  have hC_global_card_upper : (C_global_pre.card : ℝ) ≤
      Real.rpow Δ (-2 * s - 3 * ε) :=
    TDeltaGlobal.card_C_global_le_bound hC_global_pre_sub' h_dyadic'

  -- Step 5: hT_Q_sub_Tsource
  have hT_Q_sub_Tsource : ∀ Q hQ p, (a2_perSquare Q hQ).T_Q p ⊆ g.T_source := by
    intro Q hQ p
    by_cases hp : p ∈ (a2_perSquare Q hQ).P_Q
    · have h1 : (a2_perSquare Q hQ).T_Q p ⊆ (a2_perSquare Q hQ).T_original p :=
        (a2_perSquare Q hQ).hT_Q_sub_original p hp
      have h2 : (a2_perSquare Q hQ).T_original p = g.a1.tubes p :=
        h_a2_T_original Q hQ p
      rw [h2] at h1
      exact Finset.Subset.trans h1 (g.hT_sub_source p)
    · have h3 : (a2_perSquare Q hQ).T_Q p = ∅ :=
        (a2_perSquare Q hQ).hT_Q_empty_outside p hp
      rw [h3] <;> simp

  -- Step 6: Parent cell injectivity on C_global_pre
  have hΔ_pos' : 0 < DiscretisedFurstenbergEstimate.dyadicDelta m := by
    rw [←g.hΔ_eq]
    exact g.hΔ_pos
  have h_parent_injective : ∀ (hΔ_pos : 0 < Δ),
      ∀ (U1 : AppendixA.CoarseTube), U1 ∈ C_global_pre →
      ∀ (U2 : AppendixA.CoarseTube), U2 ∈ C_global_pre →
      U1 ≠ U2 → parentCell Δ hΔ_pos U1 ≠ parentCell Δ hΔ_pos U2 := by
    intro hΔ_pos U1 hU1 U2 hU2 hne
    have h_main : parentCell (DiscretisedFurstenbergEstimate.dyadicDelta m) hΔ_pos' U1 ≠
        parentCell (DiscretisedFurstenbergEstimate.dyadicDelta m) hΔ_pos' U2 :=
      TDeltaGlobal.T_Delta_global_distinct_parentCells hΔ_pos' U1
        (hC_global_pre_sub' hU1) U2 (hC_global_pre_sub' hU2) hne
    intro h_cont
    have h_cont' : parentCell (DiscretisedFurstenbergEstimate.dyadicDelta m) hΔ_pos' U1 =
        parentCell (DiscretisedFurstenbergEstimate.dyadicDelta m) hΔ_pos' U2 := by
      exact g.hΔ_eq ▸ h_cont
    exact h_main h_cont'

  -- Step 7: A1_to_linkedA2
  let linked : LinkedA2Outputs Δ δ_n s u ε T_oriented g.T_source :=
    A1_to_linkedA2 g.a1 a2_perSquare g.T_source T_oriented g.T_Delta
      (fun Q hQ => h_a2_T_Delta Q hQ)
      (fun Q hQ => by
        have h : (a2_perSquare Q hQ).C_Q ⊆ (a2_perSquare Q hQ).T_Delta :=
          (a2_perSquare Q hQ).hC_Q_sub_TDelta
        rw [h_a2_T_Delta Q hQ] at h
        exact h)
      (by have h := hC_global_card_upper; simp only [C_global_pre] at h; exact h)
      g.hT_Delta_provenance
      hT_Q_sub_Tsource
      (by have h := h_parent_injective; simp only [C_global_pre] at h; exact h)

  -- Step 8: linkedA2_to_A4_v2
  have hQset_eq : linked.Qset = g.a1.Qset := by rfl

  have h_absorb1' : 8 * (MainAppendix.affineLine_packing_constant : ℝ) *
      ((800 * (54 : ℝ)) : ℝ)^s ≤ Real.rpow Δ (-2 * ε) := by
    have h_eq : (800 * (54 : ℝ)) = (43200 : ℝ) := by norm_num
    rw [h_eq]
    exact g.h_num_u.hΔ_absorb1

  have hu_le_two : u ≤ 2 := le_of_lt g.h_run_lt_two

  let result := linkedA2_to_A4_v2
    g.T_source T_oriented g.a1 linked hQset_eq
    g.hΔ_pos g.hΔ_lt_half g.hδ_n_pos g.hδ_le_D
    g.hε_pos g.hε_lt_one g.hs_pos g.hs_lt_one g.hu_pos g.h_run_lt_two g.hsu
    g.h_num_u.hΔ_small_A3
    h_absorb1'
    g.h_num_u.hΔ_absorb2
    h12ε
    (fun Q hQ => (a2_perSquare Q hQ).hKpack_le_ε)
    h_energy_all
    g.h_num_u.hΔ_small_A4
    g.h_num_u.hΔ_small_pack_A4
    g.hδ_n_eq hu_le_two
    hRKP_at_Delta

  let a4_v2 : A4_Output_v2 Δ δ_n s u ε g.T_source := result.val
  let hQ4_sub_a1 : a4_v2.Qset ⊆ g.a1.Qset := result.property.1
  let hQset_card_lower : Real.rpow Δ (-u + 4 * ε) ≤ (a4_v2.Qset.card : ℝ) :=
    result.property.2.1
  let hQset_card_upper : (a4_v2.Qset.card : ℝ) ≤ Real.rpow Δ (-u - ε) :=
    result.property.2.2.1
  let h_base_T_Delta_eq : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4_v2.Qset),
      (a4_v2.perSquare Q hQ).base.T_Delta = linked.old.T_Delta :=
    result.property.2.2.2

  -- Step 9: C_global_A2 from a4_v2
  let C_global_A2 : Finset AppendixA.CoarseTube :=
    a4_v2.Qset.biUnion (fun Q =>
      if h : Q ∈ a4_v2.Qset then (a4_v2.perSquare Q h).base.C_Q else ∅)

  have hC_global_eq : C_global_A2 = a4_v2.Qset.biUnion (fun Q =>
      if h : Q ∈ a4_v2.Qset then (a4_v2.perSquare Q h).base.C_Q else ∅) := by
    simp [C_global_A2]

  have hC_global_sub_T_Delta : C_global_A2 ⊆ g.T_Delta := by
    intro T hT
    rcases Finset.mem_biUnion.mp hT with ⟨Q, hQ, hTQ⟩
    have h1 : T ∈ (a4_v2.perSquare Q hQ).base.C_Q := by simpa [hQ] using hTQ
    have h2 : (a4_v2.perSquare Q hQ).base.C_Q ⊆ (a4_v2.perSquare Q hQ).base.T_Delta :=
      (a4_v2.perSquare Q hQ).base.hC_Q_sub_TDelta
    have h3 : (a4_v2.perSquare Q hQ).base.T_Delta = g.T_Delta := by
      have h4 : (a4_v2.perSquare Q hQ).base.T_Delta = linked.old.T_Delta :=
        h_base_T_Delta_eq Q hQ
      rw [h4] <;> rfl
    rw [h3] at h2
    exact h2 h1

  have hT_Delta_card : (g.T_Delta.card : ℝ) ≤ Real.rpow Δ (-2 * s - 3 * ε) := by
    have h4 : g.T_Delta = T_Delta_global hnm g.T_source := g.hT_Delta_eq
    rw [h4]
    have h5 : (T_Delta_global hnm g.T_source).card =
        (T_Delta_global_dyadic hnm g.T_source).card :=
      TDeltaGlobal.card_T_Delta_global_eq (hnm := hnm) (T_source := g.T_source)
    rw [h5]
    exact_mod_cast h_dyadic'

  have hC_global_card : (C_global_A2.card : ℝ) ≤ Real.rpow Δ (-2 * s - 3 * ε) := by
    calc (C_global_A2.card : ℝ)
      ≤ (g.T_Delta.card : ℝ) := by exact_mod_cast Finset.card_le_card hC_global_sub_T_Delta
    _ ≤ Real.rpow Δ (-2 * s - 3 * ε) := hT_Delta_card

  have h_slope_bound_A7 : ∀ (T : AppendixA.CoarseTube), T ∈ C_global_A2 →
      (LemmaE.getDirV T) 1 ≠ 0 ∧ |tubeSlope T| ≤ 1 ∧ |tubeIntercept T| ≤ 3 := by
    intro T hT
    have hT_in_TDelta : T ∈ g.T_Delta := hC_global_sub_T_Delta hT
    have hT_in_global : T ∈ T_Delta_global hnm g.T_source := by
      rw [←g.hT_Delta_eq] <;> exact hT_in_TDelta
    exact TDeltaGlobal.T_Delta_global_affine_bounds
      g.h_slope_T_Delta_dyadic g.h_intercept_T_Delta_dyadic T hT_in_global

  have hC_global_A2_distinct : ∀ (U1 : AppendixA.CoarseTube), U1 ∈ C_global_A2 →
      ∀ (U2 : AppendixA.CoarseTube), U2 ∈ C_global_A2 → U1 ≠ U2 →
      parentCell Δ g.hΔ_pos U1 ≠ parentCell Δ g.hΔ_pos U2 := by
    intro U1 hU1 U2 hU2 hne
    have hC_global_A2_sub' : C_global_A2 ⊆ T_Delta_global hnm g.T_source := by
      rw [←g.hT_Delta_eq]
      exact hC_global_sub_T_Delta
    have h_main2 : parentCell (DiscretisedFurstenbergEstimate.dyadicDelta m) hΔ_pos' U1 ≠
        parentCell (DiscretisedFurstenbergEstimate.dyadicDelta m) hΔ_pos' U2 :=
      TDeltaGlobal.C_global_distinct_parentCells hC_global_A2_sub' hΔ_pos' U1 hU1 U2 hU2 hne
    intro h_cont
    have h_cont' : parentCell (DiscretisedFurstenbergEstimate.dyadicDelta m) hΔ_pos' U1 =
        parentCell (DiscretisedFurstenbergEstimate.dyadicDelta m) hΔ_pos' U2 := by
      exact g.hΔ_eq ▸ h_cont
    exact h_main2 h_cont'

  have h_perSquare_T_Delta_eq : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ a4_v2.Qset),
      (a4_v2.perSquare Q hQ).base.T_Delta = g.T_Delta := by
    intro Q hQ
    have h4 : (a4_v2.perSquare Q hQ).base.T_Delta = linked.old.T_Delta :=
      h_base_T_Delta_eq Q hQ
    rw [h4] <;> rfl

  exact
    { a4_v2 := a4_v2
      hQ4_sub_a1 := hQ4_sub_a1
      hQset_card_lower := hQset_card_lower
      hQset_card_upper := hQset_card_upper
      C_global_A2 := C_global_A2
      hC_global_eq := hC_global_eq
      hC_global_sub_T_Delta := hC_global_sub_T_Delta
      hC_global_card := hC_global_card
      hC_global_A2_distinct := hC_global_A2_distinct
      h_slope_bound_A7 := h_slope_bound_A7
      h_perSquare_T_Delta_eq := h_perSquare_T_Delta_eq
      h_points_in_ball' := h_points_in_ball' }

end DirecretisedFurstenbergEstimate.FrontEndLemmas.FrontEndComposition

end
