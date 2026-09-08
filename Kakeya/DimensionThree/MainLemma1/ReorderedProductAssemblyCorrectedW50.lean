module

public import Kakeya.DimensionThree.MainLemma1.UpstreamCountedRawProducerW50Module
public import Kakeya.Factoring.DilatedTubePresentation

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50ReorderedProductAssemblyCorrected

noncomputable section

universe u v w z

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E]
  [BorelSpace E]

/-!
The honest coarse product is indexed by two different scale families.  The
source family `V` is at `delta`; the inner family consumed by the honest output
is at `tau` and is the translated cell family.  This spelling keeps the
indices and scales visible, so it can be called directly from the raw packet.
-/
theorem global_product_of_hprod1_hcell_honest_corrected_w50
    {ι : Type u} {κ : Type w} {lc : Type z}
    [DecidableEq ι] [DecidableEq κ] [DecidableEq lc]
    {delta tau theta : NNReal}
    {s : Finset ι} {tm : Finset κ} {sf : Finset ι}
    {V : ι → ShadedTube delta E}
    {ZTau : κ → ShadedTube tau E}
    {Zf : ι → ShadedTube delta E}
    {Tinner : κ → ShadedTube tau E}
    {tc : Finset lc} {sm : Finset κ}
    {Zc : lc → ShadedTube theta E} {Zm : κ → ShadedTube tau E}
    {pTau : ι → ι} {pTheta : κ → lc}
    {kF : ι} {lM : lc}
    {A B : ENNReal}
    {F : ShadedBody.FactorFamily E κ lc}
    {fineSet : Finset κ} {coarseSet : Finset lc}
    {fineShade : κ → ShadedTube tau E}
    {coarseShade : lc → ShadedTube theta E}
    {parent : κ → lc} {c : NNReal} {Tcoarse : lc → Tube theta E}
    {P : NNReal}
    (hprod1 :
      ShadedBody.multiplicity s (fun i ↦ (V i).toShadedBody) ≤
        A * ShadedBody.multiplicity tm (fun k ↦ (ZTau k).toShadedBody) *
          ShadedBody.multiplicity (fibre sf pTau kF)
            (fun i ↦ (Zf i).toShadedBody))
    (hcell :
      ShadedBody.multiplicity tm (fun k ↦ (ZTau k).toShadedBody) ≤
        B * ShadedBody.multiplicity F.innerSet F.innerBody)
    (hOut : Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput
      (c := c) F Tinner Tcoarse fineSet coarseSet fineShade coarseShade parent P)
    (hlM : lM ∈ coarseSet)
    (hcoarse :
      ShadedBody.multiplicity coarseSet
          (fun k ↦ (coarseShade k).toShadedBody) =
        ShadedBody.multiplicity tc (fun k ↦ (Zc k).toShadedBody))
    (hmiddle :
      ShadedBody.multiplicity
          (Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent lM)
          (fun i ↦ (fineShade i).toShadedBody) =
        ShadedBody.multiplicity (fibre sm pTheta lM)
          (fun i ↦ (Zm i).toShadedBody)) :
    ShadedBody.multiplicity s (fun i ↦ (V i).toShadedBody) ≤
      A * B * (P : ENNReal) *
        ShadedBody.multiplicity tc (fun j ↦ (Zc j).toShadedBody) *
        ShadedBody.multiplicity (fibre sm pTheta lM)
          (fun j ↦ (Zm j).toShadedBody) *
        ShadedBody.multiplicity (fibre sf pTau kF)
          (fun i ↦ (Zf i).toShadedBody) := by
  have hcoarseProduct := hOut.product lM hlM
  calc
    ShadedBody.multiplicity s (fun i ↦ (V i).toShadedBody) ≤
        A * ShadedBody.multiplicity tm (fun k ↦ (ZTau k).toShadedBody) *
          ShadedBody.multiplicity (fibre sf pTau kF)
            (fun i ↦ (Zf i).toShadedBody) := hprod1
    _ ≤ A * (B * ShadedBody.multiplicity F.innerSet F.innerBody) *
          ShadedBody.multiplicity (fibre sf pTau kF)
            (fun i ↦ (Zf i).toShadedBody) := by
      gcongr
    _ ≤ A * (B * ((P : ENNReal) *
          ShadedBody.multiplicity coarseSet
            (fun k ↦ (coarseShade k).toShadedBody) *
          ShadedBody.multiplicity
            (Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent lM)
            (fun i ↦ (fineShade i).toShadedBody))) *
          ShadedBody.multiplicity (fibre sf pTau kF)
            (fun i ↦ (Zf i).toShadedBody) := by
      gcongr
    _ = A * B * (P : ENNReal) *
          ShadedBody.multiplicity tc (fun j ↦ (Zc j).toShadedBody) *
          ShadedBody.multiplicity (fibre sm pTheta lM)
            (fun j ↦ (Zm j).toShadedBody) *
          ShadedBody.multiplicity (fibre sf pTau kF)
            (fun i ↦ (Zf i).toShadedBody) := by
      rw [hcoarse, hmiddle]
      ring

/-! Raw-producer specialization.  The two equalities identifying the honest
factor family with `uCell` and `tc` are explicit transport data, rather than
implicit coercions between the source and middle scales. -/
theorem global_product_of_upstream_directFactors_corrected_w50
    {ι : Type u} [DecidableEq ι]
    {delta tau theta : NNReal}
    {sPrime : Finset ι} {V : ι → ShadedTube delta E}
    {tTau tTheta : Finset ι}
    {TTau : ι → Tube tau E} {TTheta : ι → Tube theta E}
    {pTau pTheta : ι → ι}
    {M : Nat} {tm sf : Finset ι} {uCell tc sm : Finset ι}
    {ZTau : ι → ShadedTube tau E} {Zf : ι → ShadedTube delta E}
    {v0 : E} {Zc : ι → ShadedTube theta E} {Zm : ι → ShadedTube tau E}
    {kF lM : ι}
    (hfac : W50Upstream.IsCaseTwoDirectFactorsUpstreamW50
      sPrime V tTau TTau pTau tTheta TTheta pTheta M tm sf ZTau Zf
      uCell v0 tc sm Zc Zm kF lM)
    {A B : ENNReal}
    {F : ShadedBody.FactorFamily E ι ι}
    {fineSet coarseSet : Finset ι}
    {fineShade : ι → ShadedTube tau E}
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
      (c := c) F
      (fun k ↦ ((ZTau k).translate v0)) Tcoarse
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
  have hlM : lM ∈ coarseSet := by
    rw [hcoarseSet]
    exact hfac.middle_mem
  have hcoarse :
      ShadedBody.multiplicity coarseSet
          (fun k ↦ (coarseShade k).toShadedBody) =
        ShadedBody.multiplicity tc (fun k ↦ (Zc k).toShadedBody) := by
    rw [hcoarseSet]
    apply ShadedBody.multiplicity_congr
    intro k hk
    exact congrArg (fun W : ShadedBody E ↦ W.shade) (hcoarseShade k hk)
  have hcell :
      ShadedBody.multiplicity tm (fun k ↦ (ZTau k).toShadedBody) ≤
        B * ShadedBody.multiplicity F.innerSet F.innerBody := by
    calc
      ShadedBody.multiplicity tm (fun k ↦ (ZTau k).toShadedBody) ≤
          B * ShadedBody.multiplicity uCell
            (fun k ↦ ((ZTau k).translate v0).toShadedBody) := hcellRaw
      _ = B * ShadedBody.multiplicity F.innerSet F.innerBody := by
        congr 1
        rw [hinner]
        apply ShadedBody.multiplicity_congr
        intro k hk
        exact congrArg (fun W : ShadedBody E ↦ W.shade) (hinnerBody k hk).symm
  exact global_product_of_hprod1_hcell_honest_corrected_w50
    (hprod1 := hprod1) (hcell := hcell) (hOut := hOut)
    (hlM := hlM) (hcoarse := hcoarse) (hmiddle := hactive)

#print axioms global_product_of_hprod1_hcell_honest_corrected_w50
#print axioms global_product_of_upstream_directFactors_corrected_w50

end
end Kakeya.ml1Boot.W50ReorderedProductAssemblyCorrected
