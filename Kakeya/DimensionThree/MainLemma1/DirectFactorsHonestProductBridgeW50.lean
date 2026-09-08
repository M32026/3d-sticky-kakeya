module

public import Kakeya.DimensionThree.MainLemma1.ReorderedProductAssemblyW50

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50DirectFactorsHonestProductBridge

noncomputable section

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-!
This is the endpoint-facing spelling of the same-witness product bridge.  The
direct-factor record, the honest output, and all equality transports are kept in
one theorem so a caller cannot replace the coarse family after selecting `hfac`.
No analytic premise is hidden: `hprod1` and `hcellRaw` are the two estimates
that the caller has to supply, while the factor-family equalities are discharged
by the bridge itself.
-/
theorem apply_w50
    {ι : Type u} [DecidableEq ι]
    {delta tau theta : NNReal}
    {sPrime : Finset ι} {V : ι → ShadedTube delta E}
    {tTau tTheta : Finset ι}
    {TTau : ι → Tube tau E} {TTheta : ι → Tube theta E}
    {pTau pTheta : ι → ι}
    {M : Nat} {tm sf uCell tc sm : Finset ι}
    {ZTau : ι → ShadedTube tau E} {Zf : ι → ShadedTube delta E}
    {v0 : E} {Zc : ι → ShadedTube theta E} {Zm : ι → ShadedTube tau E}
    {kF lM : ι}
    (a b m : Nat)
    (hfac : W50Upstream.IsCaseTwoDirectFactorsUpstreamW50
      sPrime V tTau TTau pTau tTheta TTheta pTheta M tm sf ZTau Zf
      uCell v0 tc sm Zc Zm kF lM)
    {A B : ENNReal}
    {F : ShadedBody.FactorFamily E ι ι}
    {fineSet coarseSet : Finset ι}
    {fineShade : ι → ShadedTube delta E}
    {coarseShade : ι → ShadedTube theta E}
    {parent : ι → ι} {c : NNReal} {Tcoarse : ι → Tube theta E}
    {P : NNReal}
    (hprod1 :
      ShadedBody.multiplicity sPrime (fun i ↦ (V i).toShadedBody) ≤
        A * ShadedBody.multiplicity tm (fun k ↦ (ZTau k).toShadedBody) *
          ShadedBody.multiplicity (fibre sf pTau kF)
            (fun i ↦ (Zf i).toShadedBody))
    (hcellRaw :
      ShadedBody.multiplicity tm (fun k ↦ (ZTau k).toShadedBody) ≤
        B * ShadedBody.multiplicity uCell
          (fun k ↦ ((ZTau k).translate v0).toShadedBody))
    (hOut : Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput
      (c := c) F (fun i ↦ (V i)) Tcoarse
      fineSet coarseSet fineShade coarseShade parent P)
    (hinner : F.innerSet = uCell)
    (hinnerBody : ∀ k ∈ uCell,
      F.innerBody k = ((ZTau k).translate v0).toShadedBody)
    (hcoarseSet : coarseSet = tc)
    (hcoarseShade : ∀ k ∈ tc,
      (coarseShade k).toShadedBody = (Zc k).toShadedBody)
    (hactive :
      ShadedBody.multiplicity
          (Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent lM)
          (fun i ↦ (fineShade i).toShadedBody) =
        ShadedBody.multiplicity (fibre sm pTheta lM)
          (fun i ↦ (Zm i).toShadedBody)) :
    ShadedBody.multiplicity sPrime (fun i ↦ (V i).toShadedBody) ≤
      A * B * (P : ENNReal) *
        ShadedBody.multiplicity tc (fun j ↦ (Zc j).toShadedBody) *
        ShadedBody.multiplicity (fibre sm pTheta lM)
          (fun j ↦ (Zm j).toShadedBody) *
        ShadedBody.multiplicity (fibre sf pTau kF)
          (fun i ↦ (Zf i).toShadedBody) := by
  exact W50ReorderedProductAssembly.global_product_of_upstream_directFactors_w50
    a b m hfac hprod1 hcellRaw hOut hinner hinnerBody hcoarseSet
    hcoarseShade hactive

end
end Kakeya.ml1Boot.W50DirectFactorsHonestProductBridge

#print axioms Kakeya.ml1Boot.W50DirectFactorsHonestProductBridge.apply_w50
