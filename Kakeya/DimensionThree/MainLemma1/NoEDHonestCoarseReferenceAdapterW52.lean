module

public import Kakeya.DimensionThree.MainLemma1.NoEDHonestCoarseAdapterW52
public import Kakeya.DimensionThree.MainLemma1.HonestNoEDPaymentsW52

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W52NoEDHonestCoarseConsumer

noncomputable section

universe u v w

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-! The source-side payment is made before invoking the literal no-ED
consumer.  Thus the output family and its coarse shade remain exactly those
of `hOut`; no post-product selection is hidden in this bridge. -/
set_option maxHeartbeats 8000000 in
theorem HonestDilateProductOutput.toAnalyticInput_of_referencePayment_w52
    {iota : Type u} {kappa : Type v} [DecidableEq iota] [DecidableEq kappa]
    {deltaT b c R Rbase CDelta productConstant branchN : NNReal}
    {eps apKT etaCoarse eRef aFull g : Real}
    {F : ShadedBody.FactorFamily E iota kappa}
    {T : iota -> ShadedTube deltaT E} {Tb : kappa -> Tube b E}
    {fineSet : Finset iota} {coarseSet : Finset kappa}
    {fineShade : iota -> ShadedTube deltaT E}
    {coarseShade : kappa -> ShadedTube b E} {parent : iota -> kappa}
    (hOut : Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput
      (c := c) F T Tb fineSet coarseSet fineShade coarseShade parent
        productConstant)
    {reference : Finset iota} {BRef kappaCard : ENNReal} {etaRef : Real}
    (hsourceSub : F.innerSet ⊆ reference)
    (hsourceNe : F.innerSet.Nonempty)
    (hrefBall : forall i, i ∈ reference ->
      (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hhered : forall t, t ⊆ reference -> t.Nonempty ->
      (deltaT : ENNReal) ^ etaRef <=
        (ShadedBody.fullness t
          (fun i => (T i).toShadedBody) : ENNReal))
    (hFrostRef : ConvexSpaceBody.frostmanConstant reference
      (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall <= BRef)
    (hkappaCard : kappaCard ≠ 0)
    (hcard : kappaCard * (reference.card : ENNReal) <=
      (F.innerSet.card : ENNReal))
    (hdeltaT0 : 0 < deltaT) (hdeltaT1 : deltaT <= 1)
    (hc : 1 < (c : Real)) (hbranchN : 0 < branchN)
    (heRef0 : 0 <= eRef) (heg : eRef + aFull <= g)
    (hetaRef_le : etaRef <= aFull)
    (hinner : forall i, i ∈ F.innerSet ->
      F.innerBody i = (T i).toShadedBody)
    (hrefAbsorb : (deltaT : ENNReal) ^ eRef <=
      (((productConstant⁻¹ : NNReal) : ENNReal)))
    (hparent : IsParentFamilyDilate (c : Real) F.innerSet
      (fun i => (T i).toTube) F.outerSet Tb F.parent)
    (hband : forall k, k ∈ F.outerSet ->
      (branchN : ENNReal) <= ((F.fiber k).card : ENNReal) /\
        ((F.fiber k).card : ENNReal) <= 2 * (branchN : ENNReal))
    (L : ConvexSpaceBody E)
    (hunitL : (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) <= L)
    (hrawL : forall k, k ∈ coarseSet ->
      Tube.dilate (Tb k) (c : Real) <= L)
    (hLhom : L.homothety 0 ((c : Real)⁻¹) =
      ConvexSpaceBody.closedBall (0 : E) (R : Real) R.coe_nonneg)
    (hbaseBall : forall k, k ∈ coarseSet ->
      (Tb k).carrier ⊆ Metric.closedBall 0 (Rbase : Real))
    (hRbase : 2 * (Rbase : Real) <= (R : Real))
    {Bmax : ENNReal}
    (hbaseMax : maxDensity coarseSet
      (fun k => (Tb k).toConvexSpaceBody) <= Bmax)
    (hfullAbsorb : (deltaT : ENNReal) ^ ((1 - 5 * eps) * etaCoarse) <=
      (((productConstant⁻¹ : NNReal) : ENNReal)) *
        (deltaT : ENNReal) ^ aFull)
    (hmaxAbsorb : ENNReal.ofReal ((c : Real) ^ Module.finrank Real E) * Bmax <=
      (CDelta : ENNReal) * (deltaT : ENNReal) ^ (-30 * eps - apKT))
    (hFrostAbsorb : 2 *
      (volume L.carrier /
        volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier *
          ((deltaT : ENNReal) ^ (-g) * (kappaCard⁻¹ * BRef))) <=
      (CDelta : ENNReal) * (deltaT : ENNReal) ^ (-apKT)) :
    HonestCoarseAnalyticInput (deltaT := deltaT) (R := R)
      (CDelta := CDelta) coarseSet coarseShade eps apKT etaCoarse := by
  have hpaid :=
    Kakeya.ml1Boot.W52HonestNoEDPayments.source_fullness_frostman_of_hereditary_w52
      (E := E) (delta := deltaT) (reference := reference)
      (source := F.innerSet) (V := T) hsourceSub hsourceNe hrefBall
      hhered hFrostRef hkappaCard hcard
  have hsourceBall : forall i, i ∈ F.innerSet ->
      (T i).carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro i hi
    exact hrefBall i (hsourceSub hi)
  have hfullPaid : (deltaT : ENNReal) ^ aFull <=
      (ShadedBody.fullness F.innerSet
        (fun i => (T i).toShadedBody) : ENNReal) := by
    exact (ENNReal.rpow_le_rpow_of_exponent_ge
      (by exact_mod_cast hdeltaT1) hetaRef_le).trans hpaid.1
  exact HonestDilateProductOutput.toAnalyticInput_of_powerPayments_w52
    (E := E) hOut hdeltaT0 hdeltaT1 hc hbranchN heRef0 heg hinner
    hsourceNe hsourceBall hfullPaid hrefAbsorb hparent hband L hunitL hrawL
    hLhom hpaid.2 hbaseBall hRbase hbaseMax hfullAbsorb hmaxAbsorb
    hFrostAbsorb

end
end Kakeya.ml1Boot.W52NoEDHonestCoarseConsumer

#print axioms Kakeya.ml1Boot.W52NoEDHonestCoarseConsumer.HonestDilateProductOutput.toAnalyticInput_of_referencePayment_w52

end
