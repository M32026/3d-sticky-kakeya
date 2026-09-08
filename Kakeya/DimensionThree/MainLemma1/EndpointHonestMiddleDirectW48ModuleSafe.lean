module

public import Kakeya.DimensionThree.MainLemma1.Setup
public import Kakeya.DimensionThree.MainLemma1.W45H5Consumer
public import Kakeya.DimensionThree.MainLemma1.BallPort
public import Kakeya.Factoring.HonestFibreBridge

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W48EndpointHonestMiddleDirectModuleSafe

noncomputable section
set_option maxHeartbeats 12000000

universe u

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

/-!
This is the module-safe analytic endpoint boundary.  It takes the literal
  source/frostman/Q/fullness fields produced by an endpoint packet and applies
  the estimate no-ED consumer to that same source.  No packet type or downstream
  CaseTwo declaration is imported here, so this file can be imported upstream
  without introducing the CaseTwo import cycle.
-/
theorem eventually_middle_bound_of_honest_source_fields_w53
    [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {beta gammaZero gamma : Real} {p : Params}
    (hbeta0 : 0 <= beta) (hgammaZero : gammaZero ∈ Set.Ioc beta 1)
    (hp : p.Spec beta gammaZero) (hgamma : gamma ∈ Set.Icc gammaZero 1)
    (hKKT : KatzTaoEstimate.{u} E beta)
    {m : Nat} (hm : m <= p.N)
    {zFr zQ zD etaIn eM : Real}
    (hzFr : 0 <= zFr) (hzQ : 0 <= zQ) (hzD0 : 0 <= zD)
    (hzD : zFr + zQ <= zD) (heM : 0 < eM)
    (hloss : eM + (1 - betaPrime beta gamma) * zD + zQ <= 999 * p.η m)
    {CFr CQ CDelta : NNReal}
    (hCDelta1 : 1 <= CDelta) (hCQ1 : 1 <= CQ)
    (hCDelta : 4 * (W44NoED.C ^ 2 * CFr) * CQ <= CDelta) :
    ∃ etaM > (0 : Real),
      ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
        ∀ {tau rho : NNReal},
          0 < tau -> tau <= rho -> rho <= 1 ->
          delta <= tau / rho ->
          tau / rho <= delta ^ p.ε ->
          ∀ {iota : Type u} {source ambient : Finset iota}
            (Trho : Tube rho E) (Ttau : iota -> ShadedTube tau E),
            source.Nonempty -> source ⊆ ambient ->
            (∀ i ∈ ambient, (Ttau i).carrier ⊆ Trho.carrier) ->
            (0 < fullness source (fun i => (Ttau i).toShadedBody)) ->
            (delta : ENNReal) ^ etaIn <=
              (fullness source (fun i => (Ttau i).toShadedBody) : ENNReal) ->
            (delta : ENNReal) ^ etaM * (W44NoED.C : ENNReal) <=
              (delta : ENNReal) ^ etaIn ->
            frostmanConstIn source
                (fun i => (Ttau i).toConvexSpaceBody)
                Trho.toConvexSpaceBody <=
              (CFr : ENNReal) * (delta : ENNReal) ^ (-zFr) ->
            (CQ : ENNReal)⁻¹ * (delta : ENNReal) ^ zQ <=
              (((tau / rho : NNReal) : ENNReal) ^ (2 : Nat)) *
                (source.card : ENNReal) ->
            (((tau / rho : NNReal) : ENNReal) ^ (2 : Nat)) *
                (source.card : ENNReal) <=
              (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ) ->
            ShadedBody.multiplicity source
                (fun i => (Ttau i).toShadedBody) <=
              (delta : ENNReal) ^ (10 * p.η m) *
                ((tau / rho : NNReal) : ENNReal) ^ (-2 * gamma) *
                ((((tau / rho : NNReal) : ENNReal) ^ (2 : Nat)) *
                  (source.card : ENNReal)) ^ (1 - gamma / 2) := by
  obtain ⟨etaM, hetaM, hWZ⟩ :=
    Kakeya.ml1Boot.wzB_middle_factor_noED_ten_eta_w45
      (etaIn := etaIn) hdim hbeta0 hgammaZero hp hgamma hKKT hm
      hzFr hzQ hzD0 hzD heM hloss hCDelta1 hCQ1 hCDelta
  refine ⟨etaM, hetaM, ?_⟩
  exact hWZ

end
end Kakeya.ml1Boot.W48EndpointHonestMiddleDirectModuleSafe

end

#print axioms Kakeya.ml1Boot.W48EndpointHonestMiddleDirectModuleSafe.eventually_middle_bound_of_honest_source_fields_w53
