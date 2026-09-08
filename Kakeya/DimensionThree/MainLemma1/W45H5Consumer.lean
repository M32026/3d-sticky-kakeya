/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.W44NoEDMiddleConsumer
public import Kakeya.DimensionThree.MainLemma1.WZBalancedNumerics
public import Kakeya.DimensionThree.MainLemma1.Rescaling.BallRadius

/-!
# Exact no-ED WZ middle consumer

This file consumes a Q-band on the same leaf family that is normalized.  It never identifies the
leaf index set of a uniform hierarchy with its full-level node set.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot

noncomputable section

universe u

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- The gain estimate for the middle-factor consumer, stated independently of the
full-level stopping construction. -/
theorem wz_middle_gain_funds_eta_w45
    {beta gammaZero gamma : Real} {p : Params}
    (hbeta0 : 0 <= beta) (hgammaZero : gammaZero ∈ Set.Ioc beta 1)
    (hp : p.Spec beta gammaZero) (hgamma : gamma ∈ Set.Icc gammaZero 1)
    {m : Nat} (hm : m <= p.N) :
    1010 * p.η m <=
      2 * p.ε * (gamma - betaPrime beta gamma) := by
  have heta0 : 0 <= p.η m := by
    exact hp.etaZeroPos.le.trans
      (hp.etaMono (Set.mem_Iic.mpr (Nat.zero_le _))
        (Set.mem_Iic.mpr hm) (Nat.zero_le _))
  have hetaTop : p.η m <= p.ε ^ 2 / 200 := by
    calc
      p.η m <= p.η p.N :=
        hp.etaMono (Set.mem_Iic.mpr hm) (Set.mem_Iic.mpr le_rfl) hm
      _ = p.κ := hp.etaTopEq
      _ <= p.ε ^ 2 / 200 := hp.kappaLeEpsSq
  have hgammaIoc : gamma ∈ Set.Ioc beta 1 :=
    ⟨lt_of_lt_of_le hgammaZero.1 hgamma.1, hgamma.2⟩
  have hgapMono : gap beta gammaZero <= gap beta gamma :=
    (gap_spec hbeta0).2.2 hgammaZero hgammaIoc hgamma.1
  have hgap : 96 * p.ε <= gamma - betaPrime beta gamma :=
    hp.ninetySixEpsLe.trans hgapMono
  have hmul := mul_le_mul_of_nonneg_left hgap hp.epsPos.le
  nlinarith [hetaTop, heta0]

/-- The no-ED WZ consumer in the exact middle-factor form.  The strict one-unit eta margin
between the `999 * eta_m` loss ledger and the WZ gain absorbs all fixed constants. -/
theorem wzB_middle_factor_noED_ten_eta_w45
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
        ∀ {tau rho : NNReal}, 0 < tau -> tau <= rho -> rho <= 1 ->
          delta <= tau / rho -> tau / rho <= delta ^ p.ε ->
          ∀ {iota : Type u} {s ambient : Finset iota} (Trho : Tube rho E)
            (Ttau : iota -> ShadedTube tau E),
            s.Nonempty -> s ⊆ ambient ->
            (∀ i ∈ ambient, (Ttau i).carrier ⊆ Trho.carrier) ->
            0 < ShadedBody.fullness s (fun i => (Ttau i).toShadedBody) ->
            (delta : ENNReal) ^ etaIn <=
              (ShadedBody.fullness s (fun i => (Ttau i).toShadedBody) : ENNReal) ->
            (delta : ENNReal) ^ etaM * (W44NoED.C : ENNReal) <=
              (delta : ENNReal) ^ etaIn ->
            frostmanConstIn s (fun i => (Ttau i).toConvexSpaceBody)
              Trho.toConvexSpaceBody <=
                (CFr : ENNReal) * (delta : ENNReal) ^ (-zFr) ->
            (CQ : ENNReal)⁻¹ * (delta : ENNReal) ^ zQ <=
              ((tau / rho : NNReal) : ENNReal) ^ (2 : Nat) * (s.card : ENNReal) ->
            ((tau / rho : NNReal) : ENNReal) ^ (2 : Nat) * (s.card : ENNReal) <=
              (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ) ->
            ShadedBody.multiplicity s (fun i => (Ttau i).toShadedBody) <=
              (delta : ENNReal) ^ (10 * p.η m)
                * ((tau / rho : NNReal) : ENNReal) ^ (-2 * gamma)
                * (((tau / rho : NNReal) : ENNReal) ^ (2 : Nat) *
                    (s.card : ENNReal)) ^ (1 - gamma / 2) := by
  have hgammaIoc : gamma ∈ Set.Ioc beta 1 :=
    ⟨lt_of_lt_of_le hgammaZero.1 hgamma.1, hgamma.2⟩
  have hbetaPrime := betaPrime_spec hbeta0 gamma hgammaIoc
  have hbetaPrime0 : 0 <= betaPrime beta gamma := hbetaPrime.1.le
  have hbetaPrime1 : betaPrime beta gamma <= 1 := hbetaPrime.2.le.trans hgamma.2
  have hbetaPrimeGamma : betaPrime beta gamma <= gamma := hbetaPrime.2.le
  have hgamma0 : 0 <= gamma := hbeta0.trans (le_of_lt hgammaIoc.1)
  have hKKTPrime : KatzTaoEstimate.{u} E (betaPrime beta gamma) :=
    katzTaoEstimate_betaPrime (E := E) gamma hgammaIoc hKKT
  have hzeta : 0 < 5 * p.ε := mul_pos (by norm_num) hp.epsPos
  obtain ⟨etaM, hetaM, hmiddle⟩ :=
    wzB_middle_factor_noED (etaIn := etaIn) hdim hbetaPrime0 hbetaPrime1 hgamma0 hgamma.2
      hbetaPrimeGamma hzeta hzFr hzQ hzD0 hzD hKKTPrime
      hCDelta1 hCQ1 hCDelta eM heM
  let eRaw : Real :=
    -eM - (1 - betaPrime beta gamma) * zD - zQ +
      2 * p.ε * (gamma - betaPrime beta gamma)
  have hetaPos : 0 < p.η m := by
    exact hp.etaZeroPos.trans_le
      (hp.etaMono (Set.mem_Iic.mpr (Nat.zero_le _)) (Set.mem_Iic.mpr hm) (Nat.zero_le _))
  have hgain := wz_middle_gain_funds_eta_w45 hbeta0 hgammaZero hp hgamma hm
  have heRaw : 10 * p.η m < eRaw := by
    dsimp [eRaw]
    linarith
  let K : ENNReal :=
    (CDelta : ENNReal) ^ (1 - betaPrime beta gamma) * (CQ : ENNReal)
  have hCDelta0 : (CDelta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (lt_of_lt_of_le zero_lt_one hCDelta1).ne'
  have hKtop : K ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero hCDelta0 ENNReal.coe_ne_top) ENNReal.coe_ne_top
  have habsorb : ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      K * (delta : ENNReal) ^ eRaw <= (delta : ENNReal) ^ (10 * p.η m) :=
    eventually_mul_rpow_le_rpow hKtop heRaw
  have hscale := eventually_fineScale_eq_ratio_of_wz_separation hzeta
  refine ⟨etaM, hetaM, ?_⟩
  filter_upwards [hmiddle, habsorb, hscale] with delta hmiddleDelta habsorbDelta hscaleDelta
  intro tau rho htau0 htaurho hrho1 hdeltaq hqsep iota s ambient Trho Ttau
    hs hsambient hcontain hfullPos hfullSource hfullFund hsourceFrost hQlo hQhi
  have hepsScale : (5 * p.ε) / 5 = p.ε := by ring
  have hqsepWZ : tau / rho <= delta ^ ((5 * p.ε) / 5) := by
    simpa only [hepsScale] using hqsep
  have hscaleEq : fineScale tau rho = tau / rho := hscaleDelta tau rho hqsepWZ
  have hraw := hmiddleDelta htau0 htaurho hrho1
    (by simpa only [hscaleEq] using hdeltaq)
    (by simpa only [hscaleEq] using hqsepWZ)
    Trho Ttau hs hsambient hcontain hfullPos hfullSource hfullFund hsourceFrost
    (by simpa only [hscaleEq] using hQlo) (by simpa only [hscaleEq] using hQhi)
  have hExp :
      -eM - (1 - betaPrime beta gamma) * zD - zQ +
          2 * (5 * p.ε) * (gamma - betaPrime beta gamma) / 5 = eRaw := by
    dsimp [eRaw]
    ring
  rw [hExp] at hraw
  change ShadedBody.multiplicity s (fun i => (Ttau i).toShadedBody) <=
      K * (delta : ENNReal) ^ eRaw
        * (fineScale tau rho : ENNReal) ^ (-2 * gamma)
        * ((fineScale tau rho : ENNReal) ^ (2 : Nat) *
            (s.card : ENNReal)) ^ (1 - gamma / 2) at hraw
  calc
    ShadedBody.multiplicity s (fun i => (Ttau i).toShadedBody) <=
        K * (delta : ENNReal) ^ eRaw
          * (fineScale tau rho : ENNReal) ^ (-2 * gamma)
          * ((fineScale tau rho : ENNReal) ^ (2 : Nat) *
              (s.card : ENNReal)) ^ (1 - gamma / 2) := hraw
    _ <= (delta : ENNReal) ^ (10 * p.η m)
          * (fineScale tau rho : ENNReal) ^ (-2 * gamma)
          * ((fineScale tau rho : ENNReal) ^ (2 : Nat) *
              (s.card : ENNReal)) ^ (1 - gamma / 2) := by gcongr
    _ = _ := by rw [hscaleEq]

#print axioms wz_middle_gain_funds_eta_w45
#print axioms wzB_middle_factor_noED_ten_eta_w45

end

end Kakeya.ml1Boot
