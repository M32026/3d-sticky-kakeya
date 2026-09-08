module

public import Kakeya.DimensionThree.MainLemma1.UpstreamCountedRawProducerW50Module
public import Kakeya.DimensionThree.MainLemma1.ScalarFactorization

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50UpstreamSameWitness

noncomputable section
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [MeasurableSpace E] [BorelSpace E]

/-- The upstream rich packet gives a two-scale factor on exactly the same selected
fine, middle, and coarse families.  Zero extension changes neither active
multiplicity nor the product inequality. -/
theorem W50Upstream.IsCaseTwoDirectFactorsUpstreamW50.toIsTwoScaleFactors_sameWitness_w50
    {delta tau theta : NNReal} {iota kappa : Type u}
    [DecidableEq iota] [DecidableEq kappa]
    {s : Finset iota} {T : iota -> ShadedTube delta E}
    {tTau : Finset kappa} {TTau : kappa -> Tube tau E} {pTau : iota -> kappa}
    {tTheta : Finset kappa} {TTheta : kappa -> Tube theta E}
    {pTheta : kappa -> kappa}
    {M : Nat} {tm : Finset kappa} {sf : Finset iota}
    {ZTau : kappa -> ShadedTube tau E} {Zf : iota -> ShadedTube delta E}
    {uCell : Finset kappa} {v0 : E} {tc sm : Finset kappa}
    {Zc : kappa -> ShadedTube theta E} {Zm : kappa -> ShadedTube tau E}
    {kF lM : kappa} {Lcard : ENNReal}
    (hfac : W50Upstream.IsCaseTwoDirectFactorsUpstreamW50 s T
      tTau TTau pTau tTheta TTheta pTheta M tm sf ZTau Zf
      uCell v0 tc sm Zc Zm kF lM)
    (hskFine : forall i, pTau i ∈ tTau)
    (hskMiddle : forall k, pTheta k ∈ tTheta)
    (hbranch : ((fibre s pTau kF).card : ENNReal) *
        ((fibre tTau pTheta lM).card : ENNReal) * (tc.card : ENNReal) <=
      Lcard * (s.card : ENNReal)) :
    IsTwoScaleFactors
      ((4 * (M : ENNReal)) *
        (factorTwoScales.C s.card delta uCell.card tau : ENNReal))
      Lcard s T tTau TTau pTau tTheta TTheta pTheta
      kF (zeroExtend sf (fun i => (T i).toTube) Zf) 0
      lM (zeroExtend sm TTau (fun k => (Zm k).translate (-v0))) 0
      tc Zc 0 := by
  classical
  have hsfSub : fibre sf pTau kF ⊆ fibre s pTau kF := by
    intro i hi
    exact Finset.mem_filter.mpr
      ⟨hfac.fine_subset (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
  have hsmSub : fibre sm pTheta lM ⊆ fibre tTau pTheta lM := by
    intro k hk
    have hksm : k ∈ sm := (Finset.mem_filter.mp hk).1
    exact Finset.mem_filter.mpr
      ⟨hfac.mid_subset (hfac.cell_subset (hfac.middle_subset hksm)),
        (Finset.mem_filter.mp hk).2⟩
  have hmiddleActiveTube : ∀ k ∈ sm,
      ((Zm k).translate (-v0)).toTube = TTau k := by
    intro k hk
    rw [StickyKakeya.shadedTube_translate_toTube, hfac.middle_tube k]
    exact StickyKakeya.tube_translate_neg_cancel (TTau k) v0
  have hfineMult :
      ShadedBody.multiplicity (fibre s pTau kF)
          (fun i => (zeroExtend sf (fun i => (T i).toTube) Zf i).toShadedBody) =
        ShadedBody.multiplicity (fibre sf pTau kF)
          (fun i => (Zf i).toShadedBody) := by
    rw [multiplicity_zeroExtend]
    rw [fibre_inter hfac.fine_subset pTau kF]
  have hmiddleMult :
      ShadedBody.multiplicity (fibre tTau pTheta lM)
          (fun k =>
            (zeroExtend sm TTau (fun j => (Zm j).translate (-v0)) k).toShadedBody) =
        ShadedBody.multiplicity (fibre sm pTheta lM)
          (fun k => (Zm k).toShadedBody) := by
    rw [multiplicity_zeroExtend]
    rw [fibre_inter
      (hfac.middle_subset.trans (hfac.cell_subset.trans hfac.mid_subset)) pTheta lM]
    simpa [shadedTube_translate_toShadedBody] using
      ShadedBody.multiplicity_translate_const (fibre sm pTheta lM)
        (fun k => (Zm k).toShadedBody) (-v0)
  refine
    { skeleton_fine := fun i _ => hskFine i
      skeleton_mid := fun k _ => hskMiddle k
      fine_mem := hfac.mid_subset hfac.fine_mem
      fine_nonempty := hfac.fine_nonempty.mono hsfSub
      fine_tube := ?_
      fine_fullness := bot_le
      mid_mem := hfac.coarse_subset hfac.middle_mem
      mid_nonempty := hfac.middle_nonempty.mono hsmSub
      mid_tube := ?_
      mid_fullness := bot_le
      coarse_subset := hfac.coarse_subset
      coarse_nonempty := hfac.coarse_nonempty
      coarse_tube := fun l _ => hfac.coarse_tube l
      coarse_fullness := bot_le
      branch_card := hbranch
      product := ?_ }
  · intro i hi
    exact zeroExtend_toTube (fun j _ => hfac.fine_tube j) i
  · intro k hk
    exact zeroExtend_toTube hmiddleActiveTube k
  · calc
      ShadedBody.multiplicity s (fun i => (T i).toShadedBody) <=
          (4 * (M : ENNReal)) *
              (factorTwoScales.C s.card delta uCell.card tau : ENNReal) *
            ShadedBody.multiplicity tc (fun j => (Zc j).toShadedBody) *
            ShadedBody.multiplicity (fibre sm pTheta lM)
              (fun j => (Zm j).toShadedBody) *
            ShadedBody.multiplicity (fibre sf pTau kF)
              (fun i => (Zf i).toShadedBody) := hfac.product
      _ = ((4 * (M : ENNReal)) *
              (factorTwoScales.C s.card delta uCell.card tau : ENNReal)) *
            ShadedBody.multiplicity (fibre s pTau kF)
              (fun i =>
                (zeroExtend sf (fun i => (T i).toTube) Zf i).toShadedBody) *
            ShadedBody.multiplicity (fibre tTau pTheta lM)
              (fun k =>
                (zeroExtend sm TTau (fun j => (Zm j).translate (-v0)) k).toShadedBody) *
            ShadedBody.multiplicity tc (fun l => (Zc l).toShadedBody) := by
          rw [hfineMult, hmiddleMult]
          ring

#print axioms W50Upstream.IsCaseTwoDirectFactorsUpstreamW50.toIsTwoScaleFactors_sameWitness_w50

end
end Kakeya.ml1Boot.W50UpstreamSameWitness
