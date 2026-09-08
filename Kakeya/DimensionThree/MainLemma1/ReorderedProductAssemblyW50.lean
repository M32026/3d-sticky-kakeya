module

public import Kakeya.DimensionThree.MainLemma1.UpstreamCountedRawProducerW50Module
public import Kakeya.Factoring.DilatedTubePresentation

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50ReorderedProductAssembly

noncomputable section

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E]
  [BorelSpace E]

/-!
The point of this lemma is only the algebraic part of the reordered coarse route.
`hprod1` is the first (fine/outer) product estimate, `hcell` is the ball-cell
estimate, and `hOut` is the honest dilated coarse output.  The three multiplicity
families are deliberately connected by equalities in the statement: this prevents
an independently selected coarse factor from being substituted for the one used by
the raw packet.
-/
theorem global_product_of_hprod1_hcell_honest_w50
    {ι : Type u} [DecidableEq ι]
    {δ τ θ : NNReal}
    {s tm sf tc sm : Finset ι}
    {V : ι → ShadedTube δ E}
    {ZTau : ι → ShadedTube τ E}
    {Zf : ι → ShadedTube δ E}
    {Zc : ι → ShadedTube θ E}
    {Zm : ι → ShadedTube τ E}
    {pTau pTheta : ι → ι}
    {kF lM : ι}
    {A B : ENNReal}
    {F : ShadedBody.FactorFamily E ι ι}
    {fineSet coarseSet : Finset ι}
    {fineShade : ι → ShadedTube δ E}
    {coarseShade : ι → ShadedTube θ E}
    {parent : ι → ι}
    {c : NNReal} {Tcoarse : ι → Tube θ E}
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
      (c := c) F
      (fun i ↦ (V i)) Tcoarse
      fineSet coarseSet fineShade coarseShade parent P)
    (hlM : lM ∈ coarseSet)
    (hcoarse :
      ShadedBody.multiplicity coarseSet
          (fun k ↦ (coarseShade k).toShadedBody) =
        ShadedBody.multiplicity tc (fun k ↦ (Zc k).toShadedBody))
    (hmiddle :
      ShadedBody.multiplicity (Kakeya.ml1CoarseHonestW45.activeFibre
          fineSet parent lM)
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

/-!
The raw-producer-facing spelling.  All packet data are present in the arguments,
including the two hierarchy scales and the direct-factor record.  The proof itself
uses only the three certified analytic inequalities above; the record is retained in
the interface so the selected `kF`/`lM` and all subset/cardinality fields cannot be
silently replaced by a different witness at the call site.
-/
theorem global_product_of_upstream_directFactors_w50
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
  apply global_product_of_hprod1_hcell_honest_w50
    (hprod1 := hprod1) (hcell := hcell) (hOut := hOut)
    (hlM := hlM) (hcoarse := hcoarse) (hmiddle := hactive)

end

end Kakeya.ml1Boot.W50ReorderedProductAssembly
