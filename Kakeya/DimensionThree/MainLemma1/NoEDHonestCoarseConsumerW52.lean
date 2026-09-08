module

public import Kakeya.DimensionThree.MainLemma1.CoarseBallUpstreamW50
public import Kakeya.DimensionThree.MainLemma1.Rescaling.KatzTao

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W52NoEDHonestCoarseConsumer

noncomputable section

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/- The input is intentionally independent of any producer.  A producer may fill
  these four fields on its literal coarse family, after which the theorem below
  is the ordinary no-ED Katz--Tao consumer. -/
structure HonestCoarseAnalyticInput
    {b deltaT R CDelta : NNReal} {kappa : Type v}
    (coarse : Finset kappa) (Zcoarse : kappa -> ShadedTube b E)
    (eps apKT etaCoarse : Real) : Prop where
  nonempty : coarse.Nonempty
  ball : forall l, l ∈ coarse ->
    (Zcoarse l).carrier ⊆ Metric.closedBall 0 (R : Real)
  fullness : (deltaT : ENNReal) ^ ((1 - 5 * eps) * etaCoarse) <=
    ShadedBody.fullness coarse (fun l => (Zcoarse l).toShadedBody)
  maxDensity : Kakeya.maxDensity coarse
      (fun l => (Zcoarse l).toConvexSpaceBody) <=
    (CDelta : ENNReal) * (deltaT : ENNReal) ^ (-30 * eps - apKT)
  frostman : frostmanConstIn coarse
      (fun l => (Zcoarse l).toConvexSpaceBody)
      (ConvexSpaceBody.closedBall (0 : E) (R : Real) R.coe_nonneg) <=
    (CDelta : ENNReal) * (deltaT : ENNReal) ^ (-apKT)

set_option maxHeartbeats 10000000 in
theorem eventually_multiplicity_of_honestCoarseAnalyticInput_w52
    (hdim : Module.finrank Real E = 3)
    {beta gamma : Real} (hbeta0 : 0 <= beta) (hbeta1 : beta < 1)
    (hgamma0 : 0 < gamma) (hgamma1 : gamma <= 1)
    (hKKT : KatzTaoEstimate.{v} E beta)
    {eps eps2 apKT : Real} (heps0 : 0 < eps) (heps1 : 5 * eps < 1)
    (hapKT : 0 < apKT) (heps2 : eps < eps2) (heps22 : eps2 <= 2 * eps)
    (hnum : gamma - ml1Boot.betaPrime beta gamma <=
      -72 * eps - 2 * apKT + 2 * (gamma - ml1Boot.betaPrime beta gamma))
    (hnum' : 10 * apKT <= (gamma - ml1Boot.betaPrime beta gamma) / 2)
    {CDelta R : NNReal} (hCDelta : 1 <= CDelta) (hR : 1 <= R) :
    exists etaCoarse, etaCoarse > (0 : Real) ∧
      ∀ᶠ (deltaT : NNReal) in 𝓝[>] 0,
        forall {b : NNReal}, deltaT <= b -> b <= deltaT ^ (1 - 5 * eps) ->
          (b : Real) <= 1 / 4 ->
          forall {kappa : Type v} (coarse : Finset kappa)
            (Zcoarse : kappa -> ShadedTube b E),
            HonestCoarseAnalyticInput (deltaT := deltaT) (R := R)
              (CDelta := CDelta) coarse Zcoarse eps apKT etaCoarse ->
            ShadedBody.multiplicity coarse
                (fun l => (Zcoarse l).toShadedBody) <=
              (deltaT : ENNReal) ^ (10 * apKT) * (b : ENNReal) ^ (-2 * gamma) *
                ((coarse.card : ENNReal) * (b : ENNReal) ^ (2 : Nat)) ^
                  (1 - gamma / 2) := by
  obtain ⟨etaCoarse, hetaCoarse, hcoarse⟩ :=
    ml1Boot.multiplicity_coarse_le_of_const_ball (E := E) hdim hbeta0 hbeta1
      hgamma0 hgamma1 hKKT heps0 heps1 hapKT heps2 heps22 hnum hnum'
      hCDelta R hR
  refine ⟨etaCoarse, hetaCoarse, ?_⟩
  filter_upwards [hcoarse] with deltaT hdeltaT
  intro b hdeltaB hbWindow hbQuarter kappa coarse Zcoarse hInput
  exact hdeltaT b hdeltaB hbWindow hbQuarter coarse Zcoarse hInput.nonempty
    hInput.ball hInput.fullness hInput.maxDensity hInput.frostman

end

end Kakeya.ml1Boot.W52NoEDHonestCoarseConsumer

#print axioms Kakeya.ml1Boot.W52NoEDHonestCoarseConsumer.eventually_multiplicity_of_honestCoarseAnalyticInput_w52

end
