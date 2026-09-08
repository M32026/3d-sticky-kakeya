/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.W44NoEDNormalization
public import Kakeya.DimensionThree.MainLemma1.WZBalancedMiddle
public import Kakeya.DimensionThree.MainLemma1.WZBalancedNormalization

/-!
# the estimate no-ED WZ middle consumer

This module instantiates the analytic WZ middle theorem on the selection-free honest
normalization.  In particular, the source family and normalized family have identical index
sets and multiplicities, so no ED-selection exponent is charged.
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

/-- Construct the no-selection normalized family and discharge its fullness, Q-band and
absolute max-density obligations. -/
theorem exists_noED_normalizedMiddle_bounds
    (hdim : Module.finrank Real E = 3)
    {iota : Type u} {delta tau rho CFr CQ CDelta : NNReal}
    {etaIn etaM zFr zQ zD : Real}
    (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    (htau0 : 0 < tau) (htaurho : tau <= rho) (hrho1 : rho <= 1)
    {s ambient : Finset iota} (Trho : Tube rho E)
    (Ttau : iota -> ShadedTube tau E)
    (hs : s.Nonempty) (hsambient : s ⊆ ambient)
    (hcontain : ∀ i ∈ ambient, (Ttau i).carrier ⊆ Trho.carrier)
    (hfullPos : 0 < ShadedBody.fullness s (fun i => (Ttau i).toShadedBody))
    (hfullSource : (delta : ENNReal) ^ etaIn <=
      (ShadedBody.fullness s (fun i => (Ttau i).toShadedBody) : ENNReal))
    (hfullFund : (delta : ENNReal) ^ etaM *
      (W44NoED.C : ENNReal) <= (delta : ENNReal) ^ etaIn)
    (hsourceFrost : frostmanConstIn s (fun i => (Ttau i).toConvexSpaceBody)
      Trho.toConvexSpaceBody <= (CFr : ENNReal) * (delta : ENNReal) ^ (-zFr))
    (hQlo : (CQ : ENNReal)⁻¹ * (delta : ENNReal) ^ zQ <=
      (fineScale tau rho : ENNReal) ^ (2 : Nat) * (s.card : ENNReal))
    (hQhi : (fineScale tau rho : ENNReal) ^ (2 : Nat) * (s.card : ENNReal) <=
      (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ))
    (hCDelta : 4 * (W44NoED.C ^ 2 * CFr) * CQ <= CDelta)
    (hzD : zFr + zQ <= zD) :
    exists V : iota -> ShadedTube (fineScale tau rho) E,
      (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
      ShadedBody.multiplicity s (fun i => (Ttau i).toShadedBody) =
        ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ∧
      (delta : ENNReal) ^ etaM <=
        (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) ∧
      (CQ : ENNReal)⁻¹ * (delta : ENNReal) ^ zQ <=
        (fineScale tau rho : ENNReal) ^ (2 : Nat) * (s.card : ENNReal) ∧
      (fineScale tau rho : ENNReal) ^ (2 : Nat) * (s.card : ENNReal) <=
        (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ) ∧
      maxDensity s (fun i => (V i).toConvexSpaceBody) <=
        (CDelta : ENNReal) * (delta : ENNReal) ^ (-zD) := by
  classical
  obtain ⟨V, hball, hmult, hfullNorm, hFrostNorm⟩ :=
    W44NoED.exists_normalization_noED hdim htau0 htaurho hrho1 Trho Ttau
      hs hsambient hcontain hfullPos
  have hC1 : 1 <= W44NoED.C := W44NoED.one_le_C
  have hC0 : W44NoED.C ≠ 0 := (lt_of_lt_of_le zero_lt_one hC1).ne'
  have hcompareNN :
      ShadedBody.fullness s (fun i => (Ttau i).toShadedBody) <=
        W44NoED.C * ShadedBody.fullness s (fun i => (V i).toShadedBody) := by
    calc
      ShadedBody.fullness s (fun i => (Ttau i).toShadedBody) =
          W44NoED.C *
            (W44NoED.C⁻¹ * ShadedBody.fullness s (fun i => (Ttau i).toShadedBody)) := by
              rw [← mul_assoc, mul_inv_cancel₀ hC0, one_mul]
      _ <= W44NoED.C * ShadedBody.fullness s (fun i => (V i).toShadedBody) := by
        gcongr
  have hcompare :
      (ShadedBody.fullness s (fun i => (Ttau i).toShadedBody) : ENNReal) <=
        (W44NoED.C : ENNReal) *
          (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) := by
    exact_mod_cast hcompareNN
  have hfull : (delta : ENNReal) ^ etaM <=
      (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) :=
    fullness_lower_of_funded_comparison
      (ENNReal.coe_ne_zero.mpr hC0) ENNReal.coe_ne_top hfullFund hfullSource hcompare
  have hFrost : frostmanConstIn s (fun i => (V i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall <=
        ((W44NoED.C ^ 2 * CFr : NNReal) : ENNReal) *
          (delta : ENNReal) ^ (-zFr) := by
    calc
      frostmanConstIn s (fun i => (V i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall <=
          ((W44NoED.C ^ 2 : NNReal) : ENNReal) *
            frostmanConstIn s (fun i => (Ttau i).toConvexSpaceBody)
              Trho.toConvexSpaceBody := hFrostNorm
      _ <= ((W44NoED.C ^ 2 : NNReal) : ENNReal) *
          ((CFr : ENNReal) * (delta : ENNReal) ^ (-zFr)) := by gcongr
      _ = ((W44NoED.C ^ 2 * CFr : NNReal) : ENNReal) *
          (delta : ENNReal) ^ (-zFr) := by push_cast; ring
  have hrho0 : 0 < rho := htau0.trans_le htaurho
  have hq1 : fineScale tau rho <= 1 :=
    (fineScale_bounds htaurho hrho0).2.1.trans (by
      exact_mod_cast (by norm_num : (1 / 4 : Real) <= 1))
  have hmax : maxDensity s (fun i => (V i).toConvexSpaceBody) <=
      (CDelta : ENNReal) * (delta : ENNReal) ^ (-zD) := by
    have hraw := wz_maxDensity_le_of_frostman_qBand
      (CF := W44NoED.C ^ 2 * CFr) (CQ := CQ) (zF := zFr) (zQ := zQ)
      hdim hdelta0 hq1 V hball hFrost hQhi
    calc
      maxDensity s (fun i => (V i).toConvexSpaceBody) <=
          ((4 * (W44NoED.C ^ 2 * CFr) * CQ : NNReal) : ENNReal) *
            (delta : ENNReal) ^ (-(zFr + zQ)) := hraw
      _ <= (CDelta : ENNReal) * (delta : ENNReal) ^ (-zD) := by
        apply mul_le_mul'
        · exact_mod_cast hCDelta
        · exact ENNReal.rpow_le_rpow_of_exponent_ge
            (by exact_mod_cast hdelta1) (by linarith)
  exact ⟨V, hball, hmult, hfull, hQlo, hQhi, hmax⟩

/-- The analytic WZ middle estimate instantiated on the no-ED honest normalization.  This is an
actual call to `wzB_middle_factor`; the conclusion is already transported back to the source
family by exact multiplicity preservation. -/
theorem wzB_middle_factor_noED
    (hdim : Module.finrank Real E = 3)
    {beta' gamma zeta zFr zQ zD etaIn : Real}
    (hbeta0 : 0 <= beta') (hbeta1 : beta' <= 1)
    (hgamma0 : 0 <= gamma) (hgamma1 : gamma <= 1)
    (hbetaGamma : beta' <= gamma)
    (hzeta : 0 < zeta) (hzFr : 0 <= zFr) (hzQ : 0 <= zQ)
    (hzD0 : 0 <= zD) (hzD : zFr + zQ <= zD)
    (hKKT : KatzTaoEstimate.{u} E beta')
    {CFr CQ CDelta : NNReal}
    (hCDelta1 : 1 <= CDelta) (hCQ1 : 1 <= CQ)
    (hCDelta : 4 * (W44NoED.C ^ 2 * CFr) * CQ <= CDelta) :
    ∀ eM > (0 : Real), ∃ etaM > (0 : Real),
      ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
        ∀ {tau rho : NNReal}, 0 < tau -> tau <= rho -> rho <= 1 ->
          delta <= fineScale tau rho ->
          fineScale tau rho <= delta ^ (zeta / 5) ->
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
              (fineScale tau rho : ENNReal) ^ (2 : Nat) * (s.card : ENNReal) ->
            (fineScale tau rho : ENNReal) ^ (2 : Nat) * (s.card : ENNReal) <=
              (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ) ->
            ShadedBody.multiplicity s (fun i => (Ttau i).toShadedBody) <=
              (CDelta : ENNReal) ^ (1 - beta') * (CQ : ENNReal)
                * (delta : ENNReal) ^
                    (-eM - (1 - beta') * zD - zQ
                      + 2 * zeta * (gamma - beta') / 5)
                * (fineScale tau rho : ENNReal) ^ (-2 * gamma)
                * ((fineScale tau rho : ENNReal) ^ (2 : Nat) *
                    (s.card : ENNReal)) ^ (1 - gamma / 2) := by
  intro eM heM
  obtain ⟨etaM, hetaM, hWZ⟩ :=
    wzB_middle_factor hbeta0 hbeta1 hgamma0 hgamma1 hbetaGamma hzeta hzD0 hzQ
      hKKT hCDelta1 hCQ1 eM heM
  refine ⟨etaM, hetaM, ?_⟩
  filter_upwards [hWZ, Ioc_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)]
    with delta hWZdelta hdeltaRange
  have hdelta0 : 0 < delta := hdeltaRange.1
  have hdelta1 : delta <= 1 := hdeltaRange.2
  intro tau rho htau0 htaurho hrho1 hdeltaq hqsep iota s ambient Trho Ttau
    hs hsambient hcontain hfullPos hfullSource hfullFund hsourceFrost hQlo hQhi
  obtain ⟨V, hball, hmult, hfull, hQloV, hQhiV, hmax⟩ :=
    exists_noED_normalizedMiddle_bounds hdim hdelta0 hdelta1 htau0 htaurho hrho1
      Trho Ttau hs hsambient hcontain hfullPos hfullSource hfullFund hsourceFrost
      hQlo hQhi hCDelta hzD
  have hfullNN : delta ^ etaM <=
      ShadedBody.fullness s (fun i => (V i).toShadedBody) := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_rpow_of_ne_zero hdelta0.ne' etaM]
    exact hfull
  have hmiddle := hWZdelta (fineScale tau rho) hdeltaq hqsep V hs hball hfullNN hmax
    (by simpa [ENNReal.rpow_neg] using hQloV) hQhiV
  rwa [hmult]

#print axioms exists_noED_normalizedMiddle_bounds
#print axioms wzB_middle_factor_noED

end

end Kakeya.ml1Boot
