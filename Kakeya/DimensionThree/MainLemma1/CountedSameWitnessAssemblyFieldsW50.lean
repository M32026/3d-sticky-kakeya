module

public import Kakeya.DimensionThree.MainLemma1.CaseTwoUpstreamRawFactorW50
public import Kakeya.DimensionThree.MainLemma1.AnalyticEndgame

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50CountedSameWitnessFields

noncomputable section
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [MeasurableSpace E] [BorelSpace E]

/-- Cycle-safe final assembly for a named counted witness.  Every analytic and loss field is
an explicit argument, so callers cannot accidentally discharge a different witness. -/
theorem eventually_exact_payload_of_counted_sameWitness_fields_w50 [Nontrivial E]
    {beta gammaZero : Real} {p : Params} (hspec : p.Spec beta gammaZero)
    {c : Real} (hc0 : 0 < c) (hcEta : c <= p.η 0 / 4)
    (C0 Cu : NNReal) (hCu : 1 <= Cu) :
    ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      ∀ {tau theta : NNReal}, delta <= tau -> tau <= theta -> theta <= 1 ->
      ∀ {gamma : Real} {m : Nat}, 0 <= gamma -> c <= gamma -> gamma <= 1 ->
      m < p.N ->
      ∀ {iota : Type u} [DecidableEq iota]
        {s : Finset iota} {V : iota -> ShadedTube delta E}
        {tTau : Finset iota} {VTau : iota -> Tube tau E}
        {pTau : iota -> iota}
        {tTheta : Finset iota} {VTheta : iota -> Tube theta E}
        {pTheta : iota -> iota}
        {kF : iota} {Yf : iota -> ShadedTube delta E} {lamF : NNReal}
        {lM : iota} {Ym : iota -> ShadedTube tau E} {lamM : NNReal}
        {tThetaAct : Finset iota} {Yc : iota -> ShadedTube theta E}
        {lamC : NNReal} {Lfact : ENNReal} {Nmid : Nat},
        0 < s.card -> 0 < Nmid ->
        (s.card : Real) <= (delta : Real) ^ (-(7 : Real)) ->
        (Nmid : Real) <= (delta : Real) ^ (-(7 : Real)) ->
        IsTwoScaleFactors Lfact ((Cu : ENNReal) ^ 4) s V
          tTau VTau pTau tTheta VTheta pTheta
          kF Yf lamF lM Ym lamM tThetaAct Yc lamC ->
        Lfact <=
          (((C0 * factorTwoScales.C s.card delta Nmid tau : NNReal) : ENNReal)) *
            (delta : ENNReal) ^ (-p.ε') ->
        ShadedBody.multiplicity (fibre s pTau kF)
            (fun i => (Yf i).toShadedBody) <=
          (delta : ENNReal) ^ (-4 * (p.η m + 2 * p.ε')) *
            ((delta / tau : NNReal) : ENNReal) ^ (-2 * gamma) *
            (((fibre s pTau kF).card : ENNReal) *
              ((delta / tau : NNReal) : ENNReal) ^ (2 : Nat)) ^
                (1 - gamma / 2) ->
        ShadedBody.multiplicity (fibre tTau pTheta lM)
            (fun k => (Ym k).toShadedBody) <=
          (delta : ENNReal) ^ (10 * p.η m) *
            ((tau / theta : NNReal) : ENNReal) ^ (-2 * gamma) *
            (((fibre tTau pTheta lM).card : ENNReal) *
              ((tau / theta : NNReal) : ENNReal) ^ (2 : Nat)) ^
                (1 - gamma / 2) ->
        ShadedBody.multiplicity tThetaAct
            (fun l => (Yc l).toShadedBody) <=
          (delta : ENNReal) ^ (-4 * (p.η m + 2 * p.ε')) *
            (theta : ENNReal) ^ (-2 * gamma) *
            ((tThetaAct.card : ENNReal) *
              (theta : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2) ->
        ∃ (Cf CuOut c3 lamFOut lamMOut lamCOut : NNReal)
          (etaVol av avPrime : Real),
          delta <= tau ∧ tau <= theta ∧ theta <= 1 ∧
          0 <= av ∧ av <= avPrime ∧ 8 * avPrime <= 10 * av ∧
          0 <= etaVol ∧ 0 < c3 ∧ c3 <= 1 ∧ 1 <= CuOut ∧
          IsTwoScaleFactors Lfact ((CuOut : ENNReal) ^ 4) s V
            tTau VTau pTau tTheta VTheta pTheta
            kF Yf lamFOut lM Ym lamMOut tThetaAct Yc lamCOut ∧
          Lfact <= (Cf : ENNReal) * (delta : ENNReal) ^ (-p.ε') ∧
          ShadedBody.multiplicity (fibre s pTau kF)
              (fun i => (Yf i).toShadedBody) <=
            (delta : ENNReal) ^ (-4 * avPrime) *
              ((delta / tau : NNReal) : ENNReal) ^ (-2 * gamma) *
              (((fibre s pTau kF).card : ENNReal) *
                ((delta / tau : NNReal) : ENNReal) ^ (2 : Nat)) ^
                  (1 - gamma / 2) ∧
          ShadedBody.multiplicity (fibre tTau pTheta lM)
              (fun k => (Ym k).toShadedBody) <=
            (delta : ENNReal) ^ (10 * av) *
              ((tau / theta : NNReal) : ENNReal) ^ (-2 * gamma) *
              (((fibre tTau pTheta lM).card : ENNReal) *
                ((tau / theta : NNReal) : ENNReal) ^ (2 : Nat)) ^
                  (1 - gamma / 2) ∧
          ShadedBody.multiplicity tThetaAct
              (fun l => (Yc l).toShadedBody) <=
            (delta : ENNReal) ^ (-4 * avPrime) *
              (theta : ENNReal) ^ (-2 * gamma) *
              ((tThetaAct.card : ENNReal) *
                (theta : ENNReal) ^ (2 : Nat)) ^ (1 - gamma / 2) ∧
          (c3 : ENNReal) * (delta : ENNReal) ^ etaVol <=
            (s.card : ENNReal) * (delta : ENNReal) ^ (2 : Nat) ∧
          (Cf : ENNReal) * (CuOut : ENNReal) ^ 4 *
              (c3 : ENNReal) ^ (-c / 2) *
              (delta : ENNReal) ^ (-p.ε') *
              (delta : ENNReal) ^ (10 * av - 8 * avPrime) *
              (delta : ENNReal) ^ (-2 * c - etaVol * c / 2) <= 1 := by
  filter_upwards [
      AnalyticEndgameW27.eventually_exists_exact_tail_of_isTwoScaleFactors
        (E := E) hspec hc0 hcEta C0 Cu hCu] with delta htail
  intro tau theta hdeltaTau hTauTheta hThetaOne gamma m hgamma0 hcGamma
    hgamma1 hm iota _ s V tTau VTau pTau tTheta VTheta pTheta kF Yf lamF
    lM Ym lamM tThetaAct Yc lamC Lfact Nmid hs hNmid hcardS hcardMid
    hfactor hLfact hFine hMiddle hCoarse
  have hAnalytic : AnalyticEndgameW27.IsTwoScaleAnalyticBounds
      gamma (p.η m) (p.η m + 2 * p.ε')
      s pTau kF Yf tTau pTheta lM Ym tThetaAct Yc :=
    { fine := hFine, middle := hMiddle, coarse := hCoarse }
  obtain ⟨Cf, CuOut, c3, lamFOut, lamMOut, lamCOut,
      etaVol, av, avPrime, hOut⟩ :=
    htail (ι := iota) (κ := iota) (lc := iota)
      hdeltaTau hTauTheta hThetaOne hgamma0 hcGamma hgamma1 hm
      hs hNmid hcardS hcardMid hfactor hLfact hAnalytic
  refine ⟨Cf, CuOut, c3, lamFOut, lamMOut, lamCOut,
    etaVol, av, avPrime, ?_⟩
  rcases hOut with ⟨hdeltaTau', hTauTheta', hThetaOne', hav0, havLe,
    havGain, hetaVol, hc30, hc31, hCuOut, hfactorOut, hLfactOut,
    hFineOut, hMiddleOut, hCoarseOut, hVolume, hAbsorb, _hFinal⟩
  exact ⟨hdeltaTau', hTauTheta', hThetaOne', hav0, havLe, havGain,
    hetaVol, hc30, hc31, hCuOut, hfactorOut, hLfactOut,
    hFineOut, hMiddleOut, hCoarseOut, hVolume, hAbsorb⟩

#print axioms eventually_exact_payload_of_counted_sameWitness_fields_w50

end
end Kakeya.ml1Boot.W50CountedSameWitnessFields
