module

public import Kakeya.DimensionThree.MainLemma1.UpstreamCountedRawProducerW50Module

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W51RawCountedAdapterFields

noncomputable section
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-!
The counted raw packet already contains the two total skeleton maps.  The
cardinality lemma is uniform in the eventual coarse label, so it can be fed
to the honest adapter (which asks for the bound for every `good`, rather than
only for the selected `lM`).
-/
theorem fields_of_counted_raw_packet_w51
    {iota : Type u} [DecidableEq iota]
    {delta : NNReal} {sPrime : Finset iota}
    {V : iota -> ShadedTube delta E}
    {N a b C : Nat} {Cd : NNReal}
    (U : Tube.UniformTubeSet sPrime (fun i => (V i).toTube) N Cd)
    (hab : a <= b) (hb : b <= N)
    {tTau tTheta : Finset iota} {pTau pTheta : iota -> iota}
    {tm sf tc sm : Finset iota}
    {ZTau : iota -> ShadedTube (Tube.gridScale delta N b) E}
    {Zf : iota -> ShadedTube delta E}
    {uCell : Finset iota} {v0 : E}
    {Zc : iota -> ShadedTube (Tube.gridScale delta N a) E}
    {Zm : iota -> ShadedTube (Tube.gridScale delta N b) E}
    {kF lM : iota}
    (htTau : tTau ⊆ U.cover.indexSet b)
    (htTheta : tTheta ⊆ U.cover.indexSet a)
    (hpTau : ∀ i, pTau i ∈ tTau)
    (hpTheta : ∀ k, pTheta k ∈ tTheta)
    (hparentFine : IsParentFamily sPrime (fun i => (V i).toTube)
      tTau (U.cover.tube b) pTau)
    (hparentTheta : IsParentFamily tTau (U.cover.tube b)
      tTheta (U.cover.tube a) pTheta)
    (hfac : W50Upstream.IsCaseTwoDirectFactorsUpstreamW50 sPrime V
      tTau (U.cover.tube b) pTau tTheta (U.cover.tube a) pTheta
      C tm sf ZTau Zf uCell v0 tc sm Zc Zm kF lM) :
    (∀ i, i ∈ sPrime -> pTau i ∈ tTau) ∧
      (∀ k, k ∈ tTau -> pTheta k ∈ tTheta) ∧
      (∀ good, good ∈ tc ->
        ((fibre sPrime pTau kF).card : ENNReal) *
            ((fibre tTau pTheta good).card : ENNReal) *
              (tc.card : ENNReal) <=
          (Cd : ENNReal) ^ 6 * (sPrime.card : ENNReal)) := by
  refine ⟨fun i _ => hpTau i, fun k _ => hpTheta k, ?_⟩
  intro good hgood
  exact W50Upstream.b3_branch_card_of_dedup_hierarchy_upstream_w50
    U hab hb htTau htTheta hparentFine hparentTheta
    (hfac.mid_subset hfac.fine_mem)
    (hfac.coarse_subset hgood) hfac.coarse_subset

#print axioms fields_of_counted_raw_packet_w51

end
end Kakeya.ml1Boot.W51RawCountedAdapterFields

end
