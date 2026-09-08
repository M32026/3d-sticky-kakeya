module

public import Kakeya.DimensionThree.MainLemma1.UpstreamCountedRawProducerW50Module
public import Kakeya.DimensionThree.MainLemma1.FineEndpointCountedW50

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50AllCountedApplyUpstream

noncomputable section
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/- The module-safe form uses the upstream direct-factor record, whose fields
   are definitionally the same counted fine subset/nonempty data. -/
theorem fine_field_of_counted_direct_endpoint_upstream_w50
    {p : Params} {gamma : Real} {m : Nat} {delta : NNReal}
    {iota : Type u} [DecidableEq iota]
    {s : Finset iota} {T : iota -> ShadedTube delta E}
    {N a : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s (fun i => (T i).toTube) N C)
    {tTau tTheta : Finset iota}
    {pTau pTheta repTau : iota -> iota}
    {M : Nat} {tm sf : Finset iota}
    {Ztau : iota -> ShadedTube (Tube.gridScale delta N N) E}
    {Zf : iota -> ShadedTube delta E}
    {uMid : Finset iota} {v0 : E} {tc sm : Finset iota}
    {Zc : iota -> ShadedTube (Tube.gridScale delta N a) E}
    {Zm : iota -> ShadedTube (Tube.gridScale delta N N) E}
    {kF lM : iota}
    {beta gammaZero : Real} (hp : p.Spec beta gammaZero)
    (hm : m < p.N) (hN : 0 < N) (hNdef : N = p.N)
    (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    (hED : (s : Set iota).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier))
    (hfac : W50Upstream.IsCaseTwoDirectFactorsUpstreamW50 s T
      tTau (U.cover.tube N) pTau
      tTheta (U.cover.tube a) pTheta
      M tm sf Ztau Zf uMid v0 tc sm Zc Zm kF lM)
    (hpTauRep : ∀ i, i ∈ s ->
      pTau i = repTau (U.cover.assign N i))
    (hrep : ∀ j, j ∈ U.cover.indexSet N ->
      repTau j ∈ tTau /\
        (U.cover.tube N (repTau j)).toConvexSpaceBody =
          (U.cover.tube N j).toConvexSpaceBody) :
    ShadedBody.multiplicity (fibre sf pTau kF)
        (fun i => (Zf i).toShadedBody) <=
      (delta : ENNReal) ^ (-4 * (p.η m + 2 * p.ε')) *
        ((delta / Tube.gridScale delta N N : NNReal) : ENNReal) ^ (-2 * gamma) *
        (((fibre sf pTau kF).card : ENNReal) *
          ((delta / Tube.gridScale delta N N : NNReal) : ENNReal) ^ (2 : Nat)) ^
            (1 - gamma / 2) := by
  subst N
  exact W50EndpointCounted.endpoint_fine_bound_counted_w50
    (theta := Tube.gridScale delta p.N a)
    (tTheta := tTheta) (tc := tc)
    (TTheta := U.cover.tube a) (pTheta := pTheta)
    (lM := lM) (Yf := Zf) (Ym := Zf) (Yc := Zc)
    hp hm hN hdelta0 hdelta1 U hED hpTauRep hrep
    hfac.fine_subset hfac.fine_nonempty

#print axioms fine_field_of_counted_direct_endpoint_upstream_w50

end
end Kakeya.ml1Boot.W50AllCountedApplyUpstream
end
