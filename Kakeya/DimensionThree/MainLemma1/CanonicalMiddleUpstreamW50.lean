module

public import Kakeya.DimensionThree.MainLemma1.CoarseFibre
public import Kakeya.DimensionThree.MainLemma1.TwoScaleRichW49
public import Kakeya.DimensionThree.MainLemma1.W45H5Consumer

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50CanonicalMiddle

noncomputable section

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- A global retained share descends to one selected fibre when the complete
canonical fibres and the active fibres are both pairwise comparable. -/
theorem canonical_activeFibre_card_share_w50
    {iota kappa : Type*} [DecidableEq kappa]
    {source active : Finset iota} {parents activeParents : Finset kappa}
    (parent : iota -> kappa) {A D r : ENNReal}
    (hsource : source.Nonempty)
    (hmaps : ∀ i ∈ source, parent i ∈ parents)
    (hactiveMaps : ∀ i ∈ active, parent i ∈ activeParents)
    (hactiveParents : activeParents ⊆ parents)
    (hcompleteBand : ∀ k ∈ parents, ∀ k' ∈ parents,
      ((fibre source parent k).card : ENNReal) <=
        D * ((fibre source parent k').card : ENNReal))
    (hactiveBand : ∀ k ∈ activeParents, ∀ k' ∈ activeParents,
      ((fibre active parent k).card : ENNReal) <=
        A * ((fibre active parent k').card : ENNReal))
    (hretained : r * (source.card : ENNReal) <= (active.card : ENNReal))
    {k : kappa} (hk : k ∈ activeParents) :
    r * ((fibre source parent k).card : ENNReal) <=
      A * D * ((fibre active parent k).card : ENNReal) := by
  classical
  have hparents : parents.Nonempty := by
    obtain ⟨i, hi⟩ := hsource
    exact ⟨parent i, hmaps i hi⟩
  have hsourceSum : (source.card : ENNReal) =
      ∑ k' ∈ parents, ((fibre source parent k').card : ENNReal) := by
    have hnat : source.card =
        ∑ k' ∈ parents, (fibre source parent k').card := by
      simpa [fibre] using Finset.card_eq_sum_card_fiberwise hmaps
    exact_mod_cast hnat
  have hactiveSum : (active.card : ENNReal) =
      ∑ k' ∈ activeParents, ((fibre active parent k').card : ENNReal) := by
    have hnat : active.card =
        ∑ k' ∈ activeParents, (fibre active parent k').card := by
      simpa [fibre] using Finset.card_eq_sum_card_fiberwise hactiveMaps
    exact_mod_cast hnat
  have hcomplete : (parents.card : ENNReal) *
      ((fibre source parent k).card : ENNReal) <=
        D * (source.card : ENNReal) := by
    calc
      (parents.card : ENNReal) * ((fibre source parent k).card : ENNReal) =
          ∑ _k' ∈ parents, ((fibre source parent k).card : ENNReal) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ <= ∑ k' ∈ parents,
          D * ((fibre source parent k').card : ENNReal) := by
            exact Finset.sum_le_sum fun k' hk' =>
              hcompleteBand k (hactiveParents hk) k' hk'
      _ = D * (source.card : ENNReal) := by
            rw [← Finset.mul_sum, ← hsourceSum]
  have hactiveUpper : (active.card : ENNReal) <=
      (activeParents.card : ENNReal) *
        (A * ((fibre active parent k).card : ENNReal)) := by
    rw [hactiveSum]
    calc
      (∑ k' ∈ activeParents, ((fibre active parent k').card : ENNReal)) <=
          ∑ _k' ∈ activeParents,
            A * ((fibre active parent k).card : ENNReal) :=
        Finset.sum_le_sum fun k' hk' => hactiveBand k' hk' k hk
      _ = (activeParents.card : ENNReal) *
          (A * ((fibre active parent k).card : ENNReal)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
  have hcard0 : (parents.card : ENNReal) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hparents)
  have hcardTop : (parents.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  apply (ENNReal.mul_le_mul_iff_left hcard0 hcardTop).mp
  calc
    (r * ((fibre source parent k).card : ENNReal)) *
          (parents.card : ENNReal) =
        r * ((parents.card : ENNReal) *
          ((fibre source parent k).card : ENNReal)) := by ring
    _ <= r * (D * (source.card : ENNReal)) := by gcongr
    _ <= D * (active.card : ENNReal) := by
      calc
        r * (D * (source.card : ENNReal)) =
            D * (r * (source.card : ENNReal)) := by ring
        _ <= D * (active.card : ENNReal) := by gcongr
    _ <= D * ((activeParents.card : ENNReal) *
        (A * ((fibre active parent k).card : ENNReal))) := by gcongr
    _ <= D * ((parents.card : ENNReal) *
        (A * ((fibre active parent k).card : ENNReal))) := by
      gcongr
    _ = (A * D * ((fibre active parent k).card : ENNReal)) *
        (parents.card : ENNReal) := by ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- Complete canonical hierarchy fibres are pairwise `C^5`-comparable. -/
theorem canonical_completeFibre_card_band_w50
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    {s : Finset iota} (T : iota -> Tube delta E) {N a b : Nat} {C : NNReal}
    (hC : 1 <= C) (U : Tube.UniformTubeSet s T N C)
    {parent : iota -> iota} (hparent : IsCoarseNodeParents U a b parent)
    (hbne : (U.cover.indexSet b).Nonempty)
    {l l' : iota} (hl : l ∈ U.cover.indexSet a)
    (hl' : l' ∈ U.cover.indexSet a) :
    ((fibre (U.cover.indexSet b) parent l).card : ENNReal) <=
      (C : ENNReal) ^ 5 *
        ((fibre (U.cover.indexSet b) parent l').card : ENNReal) := by
  classical
  let B : Real := (U.branchingN b : Real)
  have hBpos : 0 < B := by
    obtain ⟨k, hk⟩ := hbne
    obtain ⟨i, hi, hik⟩ := hparent.nodes_carry_leaf k hk
    have hiclass : i ∈ Tube.coverClass s (U.cover.assign b) k := by
      simp [Tube.coverClass, hi, hik]
    have hcardpos : (0 : Real) <
        ((Tube.coverClass s (U.cover.assign b) k).card : Real) := by
      exact_mod_cast Finset.card_pos.mpr ⟨i, hiclass⟩
    have hupper : ((Tube.coverClass s (U.cover.assign b) k).card : Real) <=
        (C : Real) * B := by
      exact_mod_cast U.card_class_le b hparent.le_gridLen k hk
    exact pos_of_mul_pos_right (hcardpos.trans_le hupper)
      (by exact_mod_cast (zero_le.trans hC))
  let F := fibre (U.cover.indexSet b) parent l
  let F' := fibre (U.cover.indexSet b) parent l'
  let NI := U.nodesIn b (U.cover.tube a l).toConvexSpaceBody
  have hFNI : (F.card : Real) <= (NI.card : Real) := by
    exact_mod_cast Finset.card_le_card
      (card_nodesIn_le_card_coarseFibre hC U hparent hl).1
  have h1 : B * (F.card : Real) <=
      (C : Real) ^ 3 * (U.branchingN a : Real) := by
    calc
      B * (F.card : Real) <= B * (NI.card : Real) := by gcongr
      _ <= (C : Real) ^ 3 * (U.branchingN a : Real) := by
        simpa [B, NI] using
          branching_mul_card_nodesIn_le U hparent.le_index hparent.le_gridLen l
  have h2 : (U.branchingN a : Real) <=
      (C : Real) ^ 2 * B * (F'.card : Real) := by
    simpa [B, F'] using branching_le_mul_card_coarseFibre U hparent hl'
  have hchain : B * (F.card : Real) <=
      B * ((C : Real) ^ 5 * (F'.card : Real)) := by
    calc
      B * (F.card : Real) <= (C : Real) ^ 3 * (U.branchingN a : Real) := h1
      _ <= (C : Real) ^ 3 * ((C : Real) ^ 2 * B * (F'.card : Real)) := by
        gcongr
      _ = B * ((C : Real) ^ 5 * (F'.card : Real)) := by ring
  have hreal : (F.card : Real) <= (C : Real) ^ 5 * (F'.card : Real) :=
    le_of_mul_le_mul_left hchain hBpos
  exact_mod_cast hreal

/-- The selected canonical middle fibre inherits the complete-fibre Frostman
bound without a `tc.card` loss.  This is the pTheta0 transport needed before
any representative quotient is introduced. -/
theorem canonical_selectedMiddle_frostman_w50
    {delta : NNReal} {iota : Type u} [DecidableEq iota]
    {s : Finset iota} (T : iota -> Tube delta E) {N a b : Nat} {C : NNReal}
    (hC : 1 <= C) (U : Tube.UniformTubeSet s T N C)
    {parent : iota -> iota} (hparent : IsCoarseNodeParents U a b parent)
    {sm tc : Finset iota}
    (hsm : sm ⊆ U.cover.indexSet b)
    (htc : tc ⊆ U.cover.indexSet a)
    (hmaps : ∀ k ∈ sm, parent k ∈ tc)
    (hband : ∀ l ∈ tc, ∀ l' ∈ tc,
      ((fibre sm parent l).card : ENNReal) <=
        2 * ((fibre sm parent l').card : ENNReal))
    {r : ENNReal} (hr : r ≠ 0)
    (hretained : r * ((U.cover.indexSet b).card : ENNReal) <=
      (sm.card : ENNReal))
    {l : iota} (hl : l ∈ tc) (hactive : (fibre sm parent l).Nonempty)
    {A : ENNReal}
    (hraw : frostmanConstIn (fibre (U.cover.indexSet b) parent l)
        (fun k => (U.cover.tube b k).toConvexSpaceBody)
        (U.cover.tube a l).toConvexSpaceBody <= A) :
    frostmanConstIn (fibre sm parent l)
        (fun k => (U.cover.tube b k).toConvexSpaceBody)
        (U.cover.tube a l).toConvexSpaceBody <=
      (r * (2 * (C : ENNReal) ^ 5)⁻¹)⁻¹ * A := by
  classical
  have hbne : (U.cover.indexSet b).Nonempty := hactive.mono <| by
    intro k hk
    exact hsm (Finset.mem_filter.mp hk).1
  have hcompleteBand : ∀ q ∈ U.cover.indexSet a,
      ∀ q' ∈ U.cover.indexSet a,
        ((fibre (U.cover.indexSet b) parent q).card : ENNReal) <=
          (C : ENNReal) ^ 5 *
            ((fibre (U.cover.indexSet b) parent q').card : ENNReal) := by
    intro q hq q' hq'
    exact canonical_completeFibre_card_band_w50 T hC U hparent hbne hq hq'
  have hshare := canonical_activeFibre_card_share_w50 parent hbne
    (fun k hk => hparent.parent.mapsTo k hk) hmaps htc
    hcompleteBand hband hretained hl
  have hsub : fibre sm parent l ⊆
      fibre (U.cover.indexSet b) parent l := by
    intro k hk
    exact Finset.mem_filter.mpr
      ⟨hsm (Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2⟩
  have hfullNe := hactive.mono hsub
  let v : ENNReal := volume (U.cover.tube b hactive.choose).carrier
  have hvol : ∀ k ∈ fibre (U.cover.indexSet b) parent l,
      volume (U.cover.tube b k).carrier = v := by
    intro k hk
    simpa [v] using Tube.volume_carrier_eq_volume_carrier
      (U.cover.tube b k) (U.cover.tube b hactive.choose)
  have hcontain : ∀ k ∈ fibre (U.cover.indexSet b) parent l,
      (U.cover.tube b k).toConvexSpaceBody <=
        (U.cover.tube a l).toConvexSpaceBody := by
    intro k hk
    have hkMem := (Finset.mem_filter.mp hk).1
    have hkEq := (Finset.mem_filter.mp hk).2
    simpa [hkEq] using hparent.parent.le_parent k hkMem
  have hD0 : (2 * (C : ENNReal) ^ 5) ≠ 0 := by
    refine mul_ne_zero (by norm_num) (pow_ne_zero _ ?_)
    exact ENNReal.coe_ne_zero.mpr (lt_of_lt_of_le zero_lt_one hC).ne'
  have hDtop : (2 * (C : ENNReal) ^ 5) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hkappa : r * (2 * (C : ENNReal) ^ 5)⁻¹ ≠ 0 :=
    mul_ne_zero hr (ENNReal.inv_ne_zero.mpr hDtop)
  have hcard : (r * (2 * (C : ENNReal) ^ 5)⁻¹) *
      ((fibre (U.cover.indexSet b) parent l).card : ENNReal) <=
        ((fibre sm parent l).card : ENNReal) := by
    calc
      (r * (2 * (C : ENNReal) ^ 5)⁻¹) *
            ((fibre (U.cover.indexSet b) parent l).card : ENNReal) =
          (2 * (C : ENNReal) ^ 5)⁻¹ *
            (r * ((fibre (U.cover.indexSet b) parent l).card : ENNReal)) := by ring
      _ <= (2 * (C : ENNReal) ^ 5)⁻¹ *
          ((2 * (C : ENNReal) ^ 5) *
            ((fibre sm parent l).card : ENNReal)) := by gcongr
      _ = ((fibre sm parent l).card : ENNReal) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hD0 hDtop, one_mul]
  have htransport := ConvexSpaceBody.frostmanConstIn_subfamily_le
    hfullNe hvol hcontain hsub hkappa hcard
  exact htransport.trans (mul_le_mul_left' hraw _)

#print axioms canonical_activeFibre_card_share_w50
#print axioms canonical_completeFibre_card_band_w50
#print axioms canonical_selectedMiddle_frostman_w50

end
end Kakeya.ml1Boot.W50CanonicalMiddle
