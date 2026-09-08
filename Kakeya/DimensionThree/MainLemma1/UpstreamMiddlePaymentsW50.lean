module

public import Kakeya.DimensionThree.MainLemma1.UpstreamCountedRawProducerW50Module
public import Kakeya.DimensionThree.MainLemma1.CanonicalMiddleUpstreamW50
public import Kakeya.DimensionThree.MainLemma1.W45H5Consumer

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50UpstreamMiddlePayments

noncomputable section
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

/-- The selected middle fibre of the module-safe counted packet retains both
one-scale average-fullness factors and the ball-cell half. -/
theorem middle_factor_fullness_upstream_w50
    {delta tau theta : NNReal} {iota kappa : Type u} [DecidableEq kappa]
    {s : Finset iota} {T : iota -> ShadedTube delta E}
    {tTau : Finset kappa} {TTau : kappa -> Tube tau E} {pTau : iota -> kappa}
    {tTheta : Finset kappa} {TTheta : kappa -> Tube theta E}
    {pTheta : kappa -> kappa}
    {M : Nat} {tm : Finset kappa} {sf : Finset iota}
    {ZTau : kappa -> ShadedTube tau E} {Zf : iota -> ShadedTube delta E}
    {uCell : Finset kappa} {v0 : E} {tc sm : Finset kappa}
    {Zc : kappa -> ShadedTube theta E} {Zm : kappa -> ShadedTube tau E}
    {kF lM : kappa}
    (hfac : W50Upstream.IsCaseTwoDirectFactorsUpstreamW50
      s T tTau TTau pTau tTheta TTheta pTheta
      M tm sf ZTau Zf uCell v0 tc sm Zc Zm kF lM) :
    (((factorOneScale.C uCell.card tau)⁻¹ : NNReal) : ENNReal) *
        (((1 / 2 : NNReal) : ENNReal) *
          ((((factorOneScale.C s.card delta)⁻¹ : NNReal) : ENNReal) *
            ShadedBody.fullness s (fun i => (T i).toShadedBody))) <=
      ShadedBody.fullness (fibre sm pTheta lM)
        (fun k => (Zm k).toShadedBody) := by
  have hout :
      (((factorOneScale.C s.card delta)⁻¹ : NNReal) : ENNReal) *
          ShadedBody.fullness s (fun i => (T i).toShadedBody) <=
        ShadedBody.fullness tm (fun k => (ZTau k).toShadedBody) := by
    exact_mod_cast hfac.outer_fullness
  have hcell :
      ((1 / 2 : NNReal) : ENNReal) *
          ((((factorOneScale.C s.card delta)⁻¹ : NNReal) : ENNReal) *
            ShadedBody.fullness s (fun i => (T i).toShadedBody)) <=
        ShadedBody.fullness uCell
          (fun k => ((ZTau k).translate v0).toShadedBody) := by
    apply le_trans _ hfac.cell_fullness
    gcongr
  calc
    (((factorOneScale.C uCell.card tau)⁻¹ : NNReal) : ENNReal) *
          (((1 / 2 : NNReal) : ENNReal) *
            ((((factorOneScale.C s.card delta)⁻¹ : NNReal) : ENNReal) *
              ShadedBody.fullness s (fun i => (T i).toShadedBody))) <=
        (((factorOneScale.C uCell.card tau)⁻¹ : NNReal) : ENNReal) *
          ShadedBody.fullness uCell
            (fun k => ((ZTau k).translate v0).toShadedBody) := by
      gcongr
    _ <= ShadedBody.fullness sm (fun k => (Zm k).toShadedBody) :=
      hfac.middle_refinement.coe_mul_fullness_le
    _ <= ShadedBody.fullness (fibre sm pTheta lM)
          (fun k => (Zm k).toShadedBody) := by
      exact_mod_cast hfac.middle_fullness

#print axioms middle_factor_fullness_upstream_w50

end
end Kakeya.ml1Boot.W50UpstreamMiddlePayments
