module

public import Kakeya.DimensionThree.MainLemma1.Setup
public import Kakeya.DimensionThree.MainLemma1.WZBalancedMiddle
public import Kakeya.DimensionThree.MainLemma1.W45H5Consumer

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology Tube
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W48EndpointMiddleSplitModuleSafeW53

noncomputable section
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]

/- A split-universe raw certificate.  This copy is kept upstream-safe: its
  proof only uses the module-safe balanced middle algebra, so it can be
  imported by CaseTwo without the legacy WZ packet files. -/
structure RawWZCertificate (betaPrimeValue zeta eM : Real) where
  etaM : Real
  etaM_pos : 0 < etaM
  bound :
    ∀ᶠ delta : NNReal in nhdsWithin 0 (Set.Ioi 0),
      ∀ q : NNReal, delta <= q -> q <= delta ^ (zeta / 5) ->
        ∀ {iota : Type u} {t : Finset iota}
          (Tq : iota -> ShadedTube q E),
          t.Nonempty -> (∀ l ∈ t, (Tq l).carrier ⊆ Metric.closedBall 0 1) ->
          (delta : ENNReal) ^ etaM <=
            (ShadedBody.fullness t (fun l => (Tq l).toShadedBody) : ENNReal) ->
          ShadedBody.multiplicity t (fun l => (Tq l).toShadedBody) <=
            (delta : ENNReal) ^ (-eM) *
              maxDensity t (fun l => (Tq l).toConvexSpaceBody) ^
                (1 - betaPrimeValue) * (t.card : ENNReal) ^ betaPrimeValue

theorem middle_raw_pointwise_split
    {beta' gamma zeta zFr zQ zD etaIn eM etaM : Real}
    (hbeta0 : 0 <= beta') (hbeta1 : beta' <= 1)
    (hgamma0 : 0 <= gamma) (hgamma1 : gamma <= 1)
    (hbetaGamma : beta' <= gamma)
    (hzeta : 0 < zeta) (hzFr : 0 <= zFr) (hzQ : 0 <= zQ)
    (hzD0 : 0 <= zD) (hzD : zFr + zQ <= zD)
    {CDelta CQ : NNReal}
    (hCDelta1 : 1 <= CDelta) (hCQ1 : 1 <= CQ)
    (hCDelta : 4 * (W44NoED.C ^ 2 * 1) * CQ <= CDelta)
    {delta : NNReal} (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    (hWZdelta :
      ∀ q : NNReal, delta <= q -> q <= delta ^ (zeta / 5) ->
        ∀ {iota : Type u} {t : Finset iota}
          (Tq : iota -> ShadedTube q E),
          t.Nonempty -> (∀ l ∈ t, (Tq l).carrier ⊆ Metric.closedBall 0 1) ->
          (delta : ENNReal) ^ etaM <=
            (ShadedBody.fullness t (fun l => (Tq l).toShadedBody) : ENNReal) ->
          ShadedBody.multiplicity t (fun l => (Tq l).toShadedBody) <=
            (delta : ENNReal) ^ (-eM) *
              maxDensity t (fun l => (Tq l).toConvexSpaceBody) ^
                (1 - beta') * (t.card : ENNReal) ^ beta')
    {tau rho : NNReal} (htau0 : 0 < tau) (htaurho : tau <= rho)
    (hrho1 : rho <= 1) (hdeltaq : delta <= fineScale tau rho)
    (hqsep : fineScale tau rho <= delta ^ (zeta / 5))
    {iota : Type u} {s : Finset iota}
    (Ttau : iota -> ShadedTube tau E)
    (V : iota -> ShadedTube (fineScale tau rho) E)
    (hs : s.Nonempty)
    (hVball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (hmult : ShadedBody.multiplicity s (fun i => (Ttau i).toShadedBody) =
      ShadedBody.multiplicity s (fun i => (V i).toShadedBody))
    (hVfull : (delta : ENNReal) ^ etaM <=
      (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal))
    (hVmax : maxDensity s (fun i => (V i).toConvexSpaceBody) <=
      (CDelta : ENNReal) * (delta : ENNReal) ^ (-zD))
    (hQlo : (CQ : ENNReal)⁻¹ * (delta : ENNReal) ^ zQ <=
      (fineScale tau rho : ENNReal) ^ (2 : Nat) * (s.card : ENNReal))
    (hQhi : (fineScale tau rho : ENNReal) ^ (2 : Nat) * (s.card : ENNReal) <=
      (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ)) :
    ShadedBody.multiplicity s (fun i => (Ttau i).toShadedBody) <=
      (CDelta : ENNReal) ^ (1 - beta') * (CQ : ENNReal) *
        (delta : ENNReal) ^
          (-eM - (1 - beta') * zD - zQ + 2 * zeta * (gamma - beta') / 5) *
        (fineScale tau rho : ENNReal) ^ (-2 * gamma) *
        ((fineScale tau rho : ENNReal) ^ (2 : Nat) * (s.card : ENNReal)) ^
          (1 - gamma / 2) := by
  have hfullRaw : (delta : ENNReal) ^ etaM <=
      (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) := hVfull
  have hraw := hWZdelta (fineScale tau rho) hdeltaq hqsep V hs hVball hfullRaw
  have hmiddle := wzB_middle_factor_of_raw hdelta0 hdelta1
    (by
      rw [fineScale]
      exact lt_min (div_pos htau0 (htau0.trans_le htaurho)) (by norm_num))
    hbeta0 hbeta1 hgamma0 hgamma1 hbetaGamma hzeta.le hzD0 hzQ
    hCDelta1 hCQ1 hraw hVmax
    (by simpa [ENNReal.rpow_neg] using hQlo) hQhi hqsep
  rwa [hmult]

end
end Kakeya.ml1Boot.W48EndpointMiddleSplitModuleSafeW53

end

#print axioms Kakeya.ml1Boot.W48EndpointMiddleSplitModuleSafeW53.middle_raw_pointwise_split
