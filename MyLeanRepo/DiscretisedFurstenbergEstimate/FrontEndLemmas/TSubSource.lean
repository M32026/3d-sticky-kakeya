module

/-
  TSubSource: Projection lemma hT_sub_source for A4_v2 integration.

  Main result: `niceConfig_to_a1_output_tubes_subset_Tsource`
    ∀ p, a1.tubes p ⊆ T_source

  Works with ORIGINAL definitions (no modifications to B1ToA1Skeleton).

  Key insight: Both a1.tubes and T_source are built from the SAME config'.tubeFamily.
  We use definitional unfolding through niceConfig_to_a1_output → b1_output_to_a1_output_exists
  → a1_stage, where tubes := Tp', and Tp' p' = (Tp (swapCoords p')).image swapLine.

  Whiteprint node: FrontEndLemmas / t_sub_source
  Status: COMPLETE
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.NiceConfigToA1
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
open DiscretisedFurstenbergEstimate.CombiningTheorem (NiceConfiguration)
open DirecretisedFurstenbergEstimate.AppendixA
open DirecretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter (dyadicTubeToA2)
open CoordinatePartition (swapCoords swapLine)
open DyadicCardToNcover (toAffineLine)

/-- Main projection lemma: a1.tubes p ⊆ T_source for all p.

    T_source is the image under dyadicTubeToA2 of the biUnion of config.tubeFamily
    over config.P₀.

    Proof: By definitional unfolding, a1.tubes p' equals
    (fullImage (swapCoords p')).image swapLine, where fullImage p is either
    ∅ or (config.tubeFamily p_dy hp).image toAffineLine.
    Since dyadicTubeToA2 = swapLine ∘ toAffineLine, this is a subset of T_source.
-/
lemma niceConfig_to_a1_output_tubes_subset_Tsource
    {n m : ℕ} (hnm : m ≤ n)
    {s C₁ : ℝ} {M : ℕ}
    {config : NiceConfiguration n s C₁ M}
    {Δ δ t ε : ℝ}
    (b1 : B1BridgeDecomposition n m hnm s C₁ M config Δ δ t ε)
    (hΔ_eq : Δ = dyadicDelta m)
    (hδ_eq : δ = dyadicDelta n)
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2) (hδ_pos : 0 < δ)
    (ht : 0 < t) (ht_lt_two : t < 2)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hε_pos : 0 < ε)
    (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    (T_source_dyadic : Finset (DyadicTube n))
    (hT_source_dyadic : ∀ (p : DyadicSquare n) (hp : p ∈ config.P₀),
      config.tubeFamily p hp ⊆ T_source_dyadic) :
    ∀ (p : EuclideanPlane),
      (AppendixA.NiceConfigToA1.niceConfig_to_a1_output
        (hnm := hnm) (b1 := b1) hΔ_eq hδ_eq hΔ_pos hΔ_lt_half
        hδ_pos ht ht_lt_two hs_pos hs_lt_one hε_pos h_small).tubes p ⊆
      T_source_dyadic.image dyadicTubeToA2 := by
  let a1 := AppendixA.NiceConfigToA1.niceConfig_to_a1_output
    (hnm := hnm) (b1 := b1) hΔ_eq hδ_eq hΔ_pos hΔ_lt_half
    hδ_pos ht ht_lt_two hs_pos hs_lt_one hε_pos h_small

  intro p'

  -- Use unfold to expose the internal tube map (same approach as niceConfig_to_a1_output_P_all)
  unfold AppendixA.NiceConfigToA1.niceConfig_to_a1_output
    b1_output_to_a1_output_exists A1_Assembly.a1_stage

  -- After unfolding, a1.tubes p' reduces to:
  --   (fullImage (swapCoords p')).image swapLine
  -- where fullImage is the if-then-else on config.tubeFamily
  dsimp only

  let p := swapCoords p'

  -- Now do case analysis
  by_cases h : ∃ (p_dy : DyadicSquare n), p_dy ∈ config.P₀ ∧ localSquareCenter p_dy = p

  · -- Case 1: Found a dyadic square
    rw [dif_pos h]
    -- Convert to Set inclusion to avoid DecidableEq instance mismatch
    refine' Finset.coe_subset.mpr _
    intro T' hT'
    -- hT' : T' ∈ (↑(Finset.image swapLine (Finset.image toAffineLine tubes)) : Set AffineLine)
    have h1 : ∃ (T : AffineLine),
        T ∈ (↑(Finset.image toAffineLine (config.tubeFamily (Classical.choose h)
          (Classical.choose_spec h).1)) : Set AffineLine) ∧ swapLine T = T' := by
      simpa [Finset.coe_image, Set.mem_image] using hT'
    rcases h1 with ⟨T, hT, rfl⟩
    have h2 : ∃ (U : DyadicTube n),
        U ∈ (config.tubeFamily (Classical.choose h) (Classical.choose_spec h).1 : Set (DyadicTube n)) ∧
        toAffineLine U = T := by
      simpa [Finset.coe_image, Set.mem_image] using hT
    rcases h2 with ⟨U, hU, rfl⟩
    have hU' : U ∈ config.tubeFamily (Classical.choose h) (Classical.choose_spec h).1 := by
      exact_mod_cast hU
    have hU_in : U ∈ T_source_dyadic :=
      hT_source_dyadic (Classical.choose h) (Classical.choose_spec h).1 hU'
    have h_final : swapLine (toAffineLine U) ∈
        (↑(T_source_dyadic.image dyadicTubeToA2) : Set AffineLine) := by
      simpa [Finset.mem_image, Finset.mem_coe] using ⟨U, hU_in, rfl⟩
    exact h_final

  · -- Case 2: No dyadic square — empty set
    rw [dif_neg h]
    simp

end DirecretisedFurstenbergEstimate.FrontEndLemmas

end
