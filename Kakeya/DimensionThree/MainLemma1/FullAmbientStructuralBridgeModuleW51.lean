module

public import Kakeya.DimensionThree.MainLemma1.ScalarFactorization
public import Kakeya.DimensionThree.MainLemma1.BlockSkeleton

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W51FullAmbientStructuralBridgeModule

noncomputable section
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-! The full-ambient endpoint selector has an identity first parent map. -/
theorem fullAmbient_selector_fields_module_w51
    {iota : Type u} [DecidableEq iota]
    {delta : NNReal} {c L : ENNReal}
    {s act' tAct : Finset iota}
    {V Z' : iota -> ShadedTube delta E}
    {ZTau : iota -> ShadedTube delta E}
    {kF : iota} {lamP lamF : NNReal}
    (h1 : IsOneScaleSelected c L s s V s
      (fun i => (V i).toTube) id act' Z' tAct ZTau kF lamP lamF) :
    (∀ i, i ∈ s -> id i ∈ s) ∧
      tAct ⊆ s ∧
      kF ∈ s ∧
      (fibre s id kF).Nonempty := by
  refine ⟨?_, h1.parent_subset, ?_, h1.sel_nonempty⟩
  · intro i hi
    simpa using hi
  · exact h1.parent_subset h1.sel_mem

/-! The fixed `IsTwoScaleFactors` fields are the adapter's `hskMiddle` and `hcard`. -/
theorem twoScale_skeleton_mid_and_card_module_w51
    {iota kappa lc : Type u} [DecidableEq iota] [DecidableEq kappa]
      [DecidableEq lc]
    {delta tau theta : NNReal} {Lfact Lcard : ENNReal}
    {amb : Finset iota} {V : iota -> ShadedTube delta E}
    {tTau : Finset kappa} {VTau : kappa -> Tube tau E}
    {pTau : iota -> kappa}
    {tTheta : Finset lc} {VTheta : lc -> Tube theta E}
    {pTheta : kappa -> lc} {kF : kappa}
    {Yf : iota -> ShadedTube delta E} {lamF : NNReal}
    {lM : lc} {Ym : kappa -> ShadedTube tau E} {lamM : NNReal}
    {tAct : Finset lc} {Yc : lc -> ShadedTube theta E} {lamC : NNReal}
    (hfac : IsTwoScaleFactors Lfact Lcard amb V tTau VTau pTau
      tTheta VTheta pTheta kF Yf lamF lM Ym lamM tAct Yc lamC) :
    (∀ k, k ∈ tTau -> pTheta k ∈ tTheta) ∧
      ((fibre amb pTau kF).card : ENNReal) *
          ((fibre tTau pTheta lM).card : ENNReal) *
            (tAct.card : ENNReal) <= Lcard * (amb.card : ENNReal) := by
  exact ⟨hfac.skeleton_mid, hfac.branch_card⟩

/-! Counted block skeleton maps every fine-end node into the coarse carrier. -/
theorem counted_block_skeleton_hskMiddle_module_w51
    {iota : Type u} [DecidableEq iota]
    {delta : NNReal} {s : Finset iota}
    {T : iota -> Tube delta E} {N a b : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s T N C)
    (hab : a <= b) (hb : b <= N) (hs : s.Nonempty) :
    ∃ (tTau tTheta : Finset iota) (pTau pTheta : iota -> iota),
      tTau ⊆ U.cover.indexSet b ∧
      tTheta ⊆ U.cover.indexSet a ∧
      (∀ i, pTau i ∈ tTau) ∧
      (∀ k, pTheta k ∈ tTheta) ∧
      IsParentFamily s T tTau (U.cover.tube b) pTau ∧
      IsParentFamily tTau (U.cover.tube b) tTheta (U.cover.tube a) pTheta := by
  obtain ⟨tTau, tTheta, pTau, pTheta, htTau, htTheta, hpTau, hpTheta,
      hparentFine, hparentTheta⟩ := exists_blockSkeleton U hab hb hs
  exact ⟨tTau, tTheta, pTau, pTheta,
    htTau, htTheta, hpTau, hpTheta, hparentFine, hparentTheta⟩

end
end Kakeya.ml1Boot.W51FullAmbientStructuralBridgeModule

#print axioms Kakeya.ml1Boot.W51FullAmbientStructuralBridgeModule.fullAmbient_selector_fields_module_w51
#print axioms Kakeya.ml1Boot.W51FullAmbientStructuralBridgeModule.twoScale_skeleton_mid_and_card_module_w51
#print axioms Kakeya.ml1Boot.W51FullAmbientStructuralBridgeModule.counted_block_skeleton_hskMiddle_module_w51

end
