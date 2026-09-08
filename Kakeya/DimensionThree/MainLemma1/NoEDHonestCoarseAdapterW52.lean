module

public import Kakeya.DimensionThree.MainLemma1.NoEDHonestCoarseConsumerW52
public import Kakeya.DimensionThree.MainLemma1.CountedHonestCoarseFieldW50
public import Kakeya.Factoring.DilatedTubePresentation

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

/- The producer-facing adapter.  It retains the literal `coarseSet/coarseShade`
  from `hOut`; the only numerical obligations are the three power payments.
  In particular, no post-product ED or callback witness is introduced. -/
set_option maxHeartbeats 6000000 in
theorem HonestDilateProductOutput.toAnalyticInput_of_powerPayments_w52
    {iota : Type w} {kappa : Type v} [DecidableEq kappa]
    {deltaT b c R Rbase CDelta productConstant branchN : NNReal}
    {eps apKT etaCoarse eRef aFull g : Real}
    {F : ShadedBody.FactorFamily E iota kappa}
    {T : iota -> ShadedTube deltaT E} {Tb : kappa -> Tube b E}
    {fineSet : Finset iota} {coarseSet : Finset kappa}
    {fineShade : iota -> ShadedTube deltaT E}
    {coarseShade : kappa -> ShadedTube b E} {parent : iota -> kappa}
    (hOut : Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput
      (c := c) F T Tb fineSet coarseSet fineShade coarseShade parent productConstant)
    (hdeltaT0 : 0 < deltaT) (hdeltaT1 : deltaT <= 1)
    (hc : 1 < (c : Real)) (hbranchN : 0 < branchN)
    (heRef0 : 0 <= eRef) (heg : eRef + aFull <= g)
    (hinner : forall i, i ∈ F.innerSet ->
      F.innerBody i = (T i).toShadedBody)
    (hsourceNe : F.innerSet.Nonempty)
    (hsourceBall : forall i, i ∈ F.innerSet ->
      (T i).carrier ⊆ Metric.closedBall 0 1)
    (hsourceFull : (deltaT : ENNReal) ^ aFull <=
      ShadedBody.fullness F.innerSet (fun i => (T i).toShadedBody))
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
    {Bsrc Bmax : ENNReal}
    (hsourceFrost : frostmanConstIn F.innerSet
      (fun i => (T i).toConvexSpaceBody)
      (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) <= Bsrc)
    (hbaseBall : forall k, k ∈ coarseSet ->
      (Tb k).carrier ⊆ Metric.closedBall 0 (Rbase : Real))
    (hRbase : 2 * (Rbase : Real) <= (R : Real))
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
          ((deltaT : ENNReal) ^ (-g) * Bsrc)) <=
      (CDelta : ENNReal) * (deltaT : ENNReal) ^ (-apKT)) :
    HonestCoarseAnalyticInput (deltaT := deltaT) (R := R) (CDelta := CDelta)
      coarseSet coarseShade eps apKT etaCoarse := by
  classical
  have hc0 : (0 : Real) < (c : Real) := zero_lt_one.trans hc
  have hFrost :=
    Kakeya.ml1Boot.W50CountedHonestCoarseField.HonestDilateProductOutput.coarse_frostman_from_retained_source_w50
      hOut hdeltaT0 hdeltaT1 hc hbranchN hparent hband hinner heRef0 heg
      hsourceNe hsourceBall hsourceFull hrefAbsorb hsourceFrost L hunitL hrawL
  have hfinalFrost : frostmanConstIn coarseSet
      (fun k => (coarseShade k).toConvexSpaceBody)
      (ConvexSpaceBody.closedBall (0 : E) (R : Real) R.coe_nonneg) <=
      (CDelta : ENNReal) * (deltaT : ENNReal) ^ (-apKT) := by
    rw [← hLhom] at *
    exact hFrost.trans hFrostAbsorb
  refine {
    nonempty := hOut.coarse_nonempty
    ball := ?_
    fullness := ?_
    maxDensity := ?_
    frostman := hfinalFrost }
  · intro k hk
    have hball2 := hOut.coarse_carrier_subset_closedBall hc.le hbaseBall k hk
    exact hball2.trans (Metric.closedBall_subset_closedBall (by linarith))
  · have houtFull :
        ((((productConstant⁻¹ : NNReal) *
          ShadedBody.fullness F.innerSet F.innerBody : NNReal) : ENNReal)) <=
        ((ShadedBody.fullness coarseSet
          (fun k => (coarseShade k).toShadedBody) : NNReal) : ENNReal) := by
      exact_mod_cast hOut.coarse_fullness
    have hfullEq : ShadedBody.fullness F.innerSet
        (fun i => (T i).toShadedBody) =
        ShadedBody.fullness F.innerSet F.innerBody := by
      unfold ShadedBody.fullness ShadedBody.fullness'
      congr 2
      · apply Finset.sum_congr rfl
        intro i hi
        exact congrArg (fun W : ShadedBody E => volume W.shade) (hinner i hi).symm
      · apply Finset.sum_congr rfl
        intro i hi
        exact congrArg (fun W : ShadedBody E => volume W.carrier) (hinner i hi).symm
    calc
      (deltaT : ENNReal) ^ ((1 - 5 * eps) * etaCoarse) <=
          (((productConstant⁻¹ : NNReal) : ENNReal)) *
            (deltaT : ENNReal) ^ aFull := hfullAbsorb
      _ <= (((productConstant⁻¹ : NNReal) : ENNReal)) *
          ((ShadedBody.fullness F.innerSet
            (fun i => (T i).toShadedBody) : NNReal) : ENNReal) := by gcongr
      _ = ((((productConstant⁻¹ : NNReal) *
            ShadedBody.fullness F.innerSet F.innerBody : NNReal) : ENNReal)) := by
        rw [hfullEq, ENNReal.coe_mul]
      _ <= ((ShadedBody.fullness coarseSet
          (fun k => (coarseShade k).toShadedBody) : NNReal) : ENNReal) := houtFull
  · exact (hOut.coarse_maxDensity_le hc).trans
      ((mul_le_mul_left' hbaseMax _).trans hmaxAbsorb)

end

end Kakeya.ml1Boot.W52NoEDHonestCoarseConsumer

#print axioms Kakeya.ml1Boot.W52NoEDHonestCoarseConsumer.HonestDilateProductOutput.toAnalyticInput_of_powerPayments_w52

end
