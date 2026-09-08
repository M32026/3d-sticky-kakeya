module

public import Kakeya.DimensionThree.MainLemma1.CaseTwoUpstreamSameWitnessW50

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50UpstreamRawFactor

noncomputable section
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [MeasurableSpace E] [BorelSpace E]

/-- Raw CaseTwo inputs produce the counted direct packet and an `IsTwoScaleFactors`
certificate on the identical selected tuple. -/
theorem exists_caseTwo_counted_sameWitness_rawFactor_w50 [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {beta gamma0 : Real} {p : Params} (hspec : p.Spec beta gamma0)
    (Cd : NNReal) (Kd cd : Nat) :
    ∃ M : Nat, 0 < M ∧
      ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
        ∀ {iota : Type u} [DecidableEq iota]
          (s s2 sPrime : Finset iota) (V : iota -> ShadedTube delta E)
          (U : Tube.UniformTubeSet sPrime (fun i => (V i).toTube)
            (Tube.ssfGridLen delta) Cd)
          (a b m : Nat),
          (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) ->
          s2 ⊆ s -> sPrime ⊆ s2 -> sPrime.Nonempty ->
          (∀ t ⊆ s2, t.Nonempty ->
            (delta : ENNReal) ^ p.η 0 <=
              (ShadedBody.fullness t (fun i => (V i).toShadedBody) : ENNReal)) ->
          StickyKakeya.IsFrostmanDividingBlock U Cd Kd cd
            p.η p.ε a b m p.N ->
          ∃ (tTau tTheta : Finset iota)
            (pTau pTheta repTau repTheta pTheta0 : iota -> iota)
            (tm sf : Finset iota)
            (ZTau : iota -> ShadedTube
              (Tube.gridScale delta (Tube.ssfGridLen delta) b) E)
            (Zf : iota -> ShadedTube delta E)
            (uCell : Finset iota) (v0 : E) (tc sm : Finset iota)
            (Zc : iota -> ShadedTube
              (Tube.gridScale delta (Tube.ssfGridLen delta) a) E)
            (Zm : iota -> ShadedTube
              (Tube.gridScale delta (Tube.ssfGridLen delta) b) E)
            (kF lM : iota),
            tTau ⊆ U.cover.indexSet b ∧
            tTheta ⊆ U.cover.indexSet a ∧
            (∀ i, pTau i ∈ tTau) ∧
            (∀ k, pTheta k ∈ tTheta) ∧
            (∀ i ∈ sPrime,
              pTau i = repTau (U.cover.assign b i)) ∧
            (∀ j ∈ U.cover.indexSet b,
              repTau j ∈ tTau ∧
                (U.cover.tube b (repTau j)).toConvexSpaceBody =
                  (U.cover.tube b j).toConvexSpaceBody) ∧
            (∀ j' ∈ tTau,
              ∃ j ∈ U.cover.indexSet b, repTau j = j') ∧
            (∀ i ∈ sPrime,
              (U.cover.tube b (pTau i)).toConvexSpaceBody =
                (U.cover.tube b (U.cover.assign b i)).toConvexSpaceBody) ∧
            (∀ i ∈ sPrime,
              pTheta0 (U.cover.assign b i) = U.cover.assign a i) ∧
            (∀ k ∈ U.cover.indexSet b,
              pTheta0 k ∈ U.cover.indexSet a) ∧
            (∀ k ∈ U.cover.indexSet b,
              (U.cover.tube b k).toConvexSpaceBody <=
                (U.cover.tube a (pTheta0 k)).toConvexSpaceBody) ∧
            (∀ k ∈ tTau, pTheta k = repTheta (pTheta0 k)) ∧
            (∀ l ∈ U.cover.indexSet a,
              repTheta l ∈ tTheta ∧
                (U.cover.tube a (repTheta l)).toConvexSpaceBody =
                  (U.cover.tube a l).toConvexSpaceBody) ∧
            (∀ l' ∈ tTheta,
              ∃ l ∈ U.cover.indexSet a, repTheta l = l') ∧
            (∀ k ∈ tTau,
              (U.cover.tube a (pTheta k)).toConvexSpaceBody =
                (U.cover.tube a (pTheta0 k)).toConvexSpaceBody) ∧
            IsParentFamily sPrime (fun i => (V i).toTube)
              tTau (U.cover.tube b) pTau ∧
            IsParentFamily tTau (U.cover.tube b)
              tTheta (U.cover.tube a) pTheta ∧
            W50Upstream.IsCaseTwoDirectFactorsUpstreamW50 sPrime V
              tTau (U.cover.tube b) pTau
              tTheta (U.cover.tube a) pTheta
              M tm sf ZTau Zf uCell v0 tc sm Zc Zm kF lM ∧
            IsTwoScaleFactors
              ((4 * (M : ENNReal)) *
                (factorTwoScales.C sPrime.card delta uCell.card
                  (Tube.gridScale delta (Tube.ssfGridLen delta) b) : ENNReal))
              ((Cd : ENNReal) ^ 6) sPrime V
              tTau (U.cover.tube b) pTau
              tTheta (U.cover.tube a) pTheta
              kF (zeroExtend sf (fun i => (V i).toTube) Zf) 0
              lM (zeroExtend sm (U.cover.tube b)
                (fun k => (Zm k).translate (-v0))) 0
              tc Zc 0 := by
  obtain ⟨M, hM, hproduce⟩ :=
    W50Upstream.exists_caseTwoDirectFactors_counted_raw_block_upstream_w50
      (E := E) hdim hspec Cd Kd cd
  refine ⟨M, hM, ?_⟩
  filter_upwards [hproduce] with delta hdelta
  intro iota _ s s2 sPrime V U a b m hball hs2s hsPrimeSub hsPrimeNe hhered hblock
  obtain ⟨tTau, tTheta, pTau, pTheta, repTau, repTheta, pTheta0,
      tm, sf, ZTau, Zf, uCell, v0, tc, sm, Zc, Zm, kF, lM,
      htTau, htTheta, hpTau, hpTheta, hpTauRep, hrepTau, hontoTau,
      hpTauBody, hcompTheta, hpTheta0, hleTheta0, hpThetaRep,
      hrepTheta, hontoTheta, hpThetaBody, hparentFine, hparentTheta, hfac⟩ :=
    hdelta s s2 sPrime V U a b m hball hs2s hsPrimeSub hsPrimeNe hhered hblock
  have hbranch :
      ((fibre sPrime pTau kF).card : ENNReal) *
          ((fibre tTau pTheta lM).card : ENNReal) * (tc.card : ENNReal) <=
        (Cd : ENNReal) ^ 6 * (sPrime.card : ENNReal) := by
    exact W50Upstream.b3_branch_card_of_dedup_hierarchy_upstream_w50 U
      hblock.coarse_lt_fine.le hblock.fine_le htTau htTheta
      hparentFine hparentTheta
      (hfac.mid_subset hfac.fine_mem)
      (hfac.coarse_subset hfac.middle_mem) hfac.coarse_subset
  have hraw :=
    W50UpstreamSameWitness.W50Upstream.IsCaseTwoDirectFactorsUpstreamW50.toIsTwoScaleFactors_sameWitness_w50
      hfac hpTau hpTheta hbranch
  exact ⟨tTau, tTheta, pTau, pTheta, repTau, repTheta, pTheta0,
    tm, sf, ZTau, Zf, uCell, v0, tc, sm, Zc, Zm, kF, lM,
    htTau, htTheta, hpTau, hpTheta, hpTauRep, hrepTau, hontoTau,
    hpTauBody, hcompTheta, hpTheta0, hleTheta0, hpThetaRep,
    hrepTheta, hontoTheta, hpThetaBody, hparentFine, hparentTheta, hfac, hraw⟩

#print axioms exists_caseTwo_counted_sameWitness_rawFactor_w50

end
end Kakeya.ml1Boot.W50UpstreamRawFactor
