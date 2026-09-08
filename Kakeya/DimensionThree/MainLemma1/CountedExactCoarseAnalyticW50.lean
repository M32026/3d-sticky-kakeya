module

public import Kakeya.DimensionThree.MainLemma1.CountedExactCoarseW50
public import Kakeya.DimensionThree.MainLemma1.CoarseBallUpstreamW50

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50CountedExactCoarseAnalytic

noncomputable section

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

set_option maxHeartbeats 6000000 in
/-- Radius-parametric actual-exponent coarse consumer, using only the two upstream coarse-ball
lemmas.  The fixed multiplicative loss is absorbed between exponents `-2 A` and `-4 A`. -/
theorem eventually_coarse_actualA_radius_upstream_w50
    (hdim : Module.finrank Real E = 3) {gamma : Real}
    (hgamma0 : 0 <= gamma) (hgamma1 : gamma <= 1)
    (hKF : FrostmanEstimate.{u} E gamma) (R : Real) (hR : 1 <= R) :
    forall A : Real, 0 < A -> forall Lf : NNReal, 1 <= Lf ->
      exists etaS : Real, 0 < etaS /\
      ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
        delta <= 1 ->
        forall rho : NNReal, delta <= rho -> rho <= 1 ->
        forall {kappa : Type u} [DecidableEq kappa]
          {t : Finset kappa} (Zrho : kappa -> ShadedTube rho E),
          t.Nonempty ->
          (∀ l ∈ t, (Zrho l).carrier ⊆ Metric.closedBall 0 R) ->
          (t : Set kappa).Pairwise
            (fun l l' => IsEssentiallyDistinct (Zrho l).carrier (Zrho l').carrier) ->
          frostmanConstIn t (fun l => (Zrho l).toConvexSpaceBody)
              (ConvexSpaceBody.closedBall (0 : E) R
                (le_of_lt (lt_of_lt_of_le zero_lt_one hR))) <=
            (Lf : ENNReal) * (delta : ENNReal) ^ (-A) ->
          (2 : ENNReal) * (delta : ENNReal) ^ etaS <=
            (ShadedBody.fullness t (fun l => (Zrho l).toShadedBody) : ENNReal) ->
          ShadedBody.multiplicity t (fun l => (Zrho l).toShadedBody) <=
            (delta : ENNReal) ^ (-4 * A) * (rho : ENNReal) ^ (-2 * gamma) *
              ((t.card : ENNReal) * (rho : ENNReal) ^ (2 : Nat)) ^
                (1 - gamma / 2) := by
  intro A hA Lf hLf
  obtain ⟨etaS, hetaS, M, hM, hsmall⟩ :=
    multiplicity_le_coarse_ball hdim hgamma0 hgamma1 hKF R hR A hA
  refine ⟨etaS, hetaS, ?_⟩
  let Cpay : NNReal := 2 * M * Lf
  have habsorb : ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      (Cpay : ENNReal) * (delta : ENNReal) ^ (-2 * A) <=
        (delta : ENNReal) ^ (-4 * A) := by
    simpa [Cpay] using
      (eventually_const_mul_rpow_le Cpay (x := -2 * A) (y := -4 * A)
        (by linarith))
  have hlarge := eventually_multiplicity_le_coarse_largeScale
    hdim hgamma0 hgamma1 R hR hA
  filter_upwards [hsmall Lf hLf A A hA.le hA.le, habsorb, hlarge,
      self_mem_nhdsWithin] with delta hsmallDelta habsorbDelta hlargeDelta hdelta0
  intro hdelta1 rho hdeltarho hrho1 kappa _ t Zrho htne hball hED hfrost hfull
  by_cases hrho4 : (rho : Real) <= 1 / 4
  · have hpay : (2 * (M : ENNReal) * (Lf : ENNReal)) *
        (delta : ENNReal) ^ (-A - A) <= (delta : ENNReal) ^ (-4 * A) := by
      simpa [Cpay, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        neg_mul, two_mul] using habsorbDelta
    exact hsmallDelta rho hdeltarho hrho4 Zrho htne hball hED hfrost hfull hpay
  · have hrhoLarge : (1 / 4 : Real) < (rho : Real) := lt_of_not_ge hrho4
    exact hlargeDelta rho hrhoLarge hrho1 Zrho htne hball hED

/-- The radius-eight specialization used by the honest undilation output. -/
theorem eventually_coarse_actualA_radius_eight_upstream_w50
    (hdim : Module.finrank Real E = 3) {gamma : Real}
    (hgamma0 : 0 <= gamma) (hgamma1 : gamma <= 1)
    (hKF : FrostmanEstimate.{u} E gamma) :
    forall A : Real, 0 < A -> forall Lf : NNReal, 1 <= Lf ->
      exists etaS : Real, 0 < etaS /\
      ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
        delta <= 1 ->
        forall rho : NNReal, delta <= rho -> rho <= 1 ->
        forall {kappa : Type u} [DecidableEq kappa]
          {t : Finset kappa} (Zrho : kappa -> ShadedTube rho E),
          t.Nonempty ->
          (∀ l ∈ t, (Zrho l).carrier ⊆ Metric.closedBall 0 8) ->
          (t : Set kappa).Pairwise
            (fun l l' => IsEssentiallyDistinct (Zrho l).carrier (Zrho l').carrier) ->
          frostmanConstIn t (fun l => (Zrho l).toConvexSpaceBody)
              (ConvexSpaceBody.closedBall (0 : E) 8 (by norm_num)) <=
            (Lf : ENNReal) * (delta : ENNReal) ^ (-A) ->
          (2 : ENNReal) * (delta : ENNReal) ^ etaS <=
            (ShadedBody.fullness t (fun l => (Zrho l).toShadedBody) : ENNReal) ->
          ShadedBody.multiplicity t (fun l => (Zrho l).toShadedBody) <=
            (delta : ENNReal) ^ (-4 * A) * (rho : ENNReal) ^ (-2 * gamma) *
              ((t.card : ENNReal) * (rho : ENNReal) ^ (2 : Nat)) ^
                (1 - gamma / 2) := by
  intro A hA Lf hLf
  simpa using eventually_coarse_actualA_radius_upstream_w50
    (E := E) hdim hgamma0 hgamma1 hKF 8 (by norm_num) A hA Lf hLf

end

end Kakeya.ml1Boot.W50CountedExactCoarseAnalytic

#print axioms Kakeya.ml1Boot.W50CountedExactCoarseAnalytic.eventually_coarse_actualA_radius_upstream_w50
#print axioms Kakeya.ml1Boot.W50CountedExactCoarseAnalytic.eventually_coarse_actualA_radius_eight_upstream_w50
