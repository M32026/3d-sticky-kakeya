/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.WZGlobalCrossing

/-!
# Transporting the global WZ ratio to canonical rho fibres

This module combines a two-sided global cardinality ratio with retained canonical-class balance.
All conclusions are cross-multiplied, so no scale division is needed.
-/

@[expose] public section

namespace Kakeya.WangZahl

noncomputable section

open Tube

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- Cross-multiplied upper bound for a global tau-to-rho cardinality ratio. -/
def GlobalRatioUpperBound (Xi tau rho tauCard rhoCard : NNReal) : Prop :=
  tau ^ 2 * tauCard <= Xi * rho ^ 2 * rhoCard

/-- Failure at the immediately finer scale gives an upper ratio at the current scale once the
producer supplies an adjacent parent-cardinality comparison. -/
theorem globalRatioUpperBound_of_nextFailure
    {thetaFail Kadj tau rho rhoNext tauCard rhoCard rhoNextCard : NNReal}
    (hrho : rhoNext <= rho) (hcard : rhoNextCard <= Kadj * rhoCard)
    (hfail : ¬ GlobalCrossing thetaFail tau rhoNext tauCard rhoNextCard) :
    GlobalRatioUpperBound (thetaFail * Kadj) tau rho tauCard rhoCard := by
  have hfail' : tau ^ 2 * tauCard < thetaFail * rhoNext ^ 2 * rhoNextCard :=
    lt_of_not_ge hfail
  calc
    tau ^ 2 * tauCard <= thetaFail * rhoNext ^ 2 * rhoNextCard := hfail'.le
    _ <= thetaFail * rho ^ 2 * rhoNextCard := by
      gcongr
    _ <= thetaFail * rho ^ 2 * (Kadj * rhoCard) :=
      mul_le_mul_right hcard (thetaFail * rho ^ 2)
    _ = (thetaFail * Kadj) * rho ^ 2 * rhoCard := by ring

/-- Hierarchy form of the predecessor-failure upper-ratio adapter. -/
theorem hierarchyGlobalRatioUpperBound_of_succFailure
    {ι : Type u} {delta : NNReal} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C thetaFail Kadj : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    {b a : Nat} (tauNodes : Finset ι)
    (hcard : ((activeRhoParents U b (a + 1) tauNodes).card : NNReal) <=
      Kadj * ((activeRhoParents U b a tauNodes).card : NNReal))
    (hfail : ¬ hierarchyGlobalCrossing U b tauNodes thetaFail (a + 1)) :
    GlobalRatioUpperBound (thetaFail * Kadj) (_root_.Tube.gridScale delta N b)
      (_root_.Tube.gridScale delta N a) tauNodes.card
      (activeRhoParents U b a tauNodes).card := by
  exact globalRatioUpperBound_of_nextFailure
    (_root_.Tube.gridScale_antitone hdelta hdeltaOne N (Nat.le_succ a)) hcard hfail

/-- Enlarge the coefficient in a global upper-ratio bound. -/
theorem GlobalRatioUpperBound.mono {Xi Xi' tau rho tauCard rhoCard : NNReal}
    (hXi : Xi <= Xi') (h : GlobalRatioUpperBound Xi tau rho tauCard rhoCard) :
    GlobalRatioUpperBound Xi' tau rho tauCard rhoCard := by
  calc
    tau ^ 2 * tauCard <= Xi * rho ^ 2 * rhoCard := h
    _ <= Xi' * rho ^ 2 * rhoCard := by gcongr

/-- Assemble the direct and predecessor-failure cases into one two-sided global ratio selection. -/
theorem exists_hierarchyGlobalRatioBand_of_cardLower
    {ι : Type u} {delta : NNReal} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C theta Kadj Xi : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hdelta : 0 < delta)
    (hdeltaOne : delta <= 1) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    {b sigma : Nat} (hb : b <= N) {tauNodes : Finset ι}
    (htau : tauNodes ⊆ U.cover.indexSet b)
    (hcardLower : theta * C <= (_root_.Tube.gridScale delta N b) ^ 2 * tauNodes.card)
    (hdirect : GlobalRatioUpperBound Xi (_root_.Tube.gridScale delta N b)
      (_root_.Tube.gridScale delta N sigma) tauNodes.card
      (activeRhoParents U b sigma tauNodes).card)
    (hadj : ∀ a, a < sigma ->
      ((activeRhoParents U b (a + 1) tauNodes).card : NNReal) <=
        Kadj * ((activeRhoParents U b a tauNodes).card : NNReal))
    (hcoeff : theta * Kadj <= Xi) :
    ∃ a, a <= sigma ∧ hierarchyGlobalCrossing U b tauNodes theta a ∧
      GlobalRatioUpperBound Xi (_root_.Tube.gridScale delta N b)
        (_root_.Tube.gridScale delta N a) tauNodes.card
        (activeRhoParents U b a tauNodes).card := by
  obtain ⟨a, ha, hcross, hcase⟩ :=
    exists_hierarchyGlobalCrossing_of_cardLower U hs hball hb htau hcardLower
  refine ⟨a, ha, hcross, ?_⟩
  rcases hcase with rfl | ⟨ha_lt, hfail⟩
  · exact hdirect
  · exact (hierarchyGlobalRatioUpperBound_of_succFailure
      U hdelta hdeltaOne tauNodes (hadj a ha_lt) hfail).mono hcoeff

/-- A global lower crossing and an upper average bound imply a local lower Q bound. -/
theorem localLowerQ_of_globalCrossing
    {theta kappa C tau rho tauCard rhoCard childCount : NNReal}
    (hrhoCard : 0 < rhoCard)
    (hcross : GlobalCrossing theta tau rho tauCard rhoCard)
    (haverage : kappa * tauCard <= C ^ 4 * rhoCard * childCount) :
    theta * kappa * rho ^ 2 <= C ^ 4 * tau ^ 2 * childCount := by
  apply le_of_mul_le_mul_right _ hrhoCard
  calc
    (theta * kappa * rho ^ 2) * rhoCard =
        kappa * (theta * rho ^ 2 * rhoCard) := by ring
    _ <= kappa * (tau ^ 2 * tauCard) := mul_le_mul_right hcross kappa
    _ = tau ^ 2 * (kappa * tauCard) := by ring
    _ <= tau ^ 2 * (C ^ 4 * rhoCard * childCount) :=
      mul_le_mul_right haverage (tau ^ 2)
    _ = (C ^ 4 * tau ^ 2 * childCount) * rhoCard := by ring

/-- A global upper ratio and a lower average bound imply a local upper Q bound. -/
theorem localUpperQ_of_globalRatioUpperBound
    {kappa C Xi tau rho tauCard rhoCard childCount : NNReal}
    (hrhoCard : 0 < rhoCard)
    (hupper : GlobalRatioUpperBound Xi tau rho tauCard rhoCard)
    (haverage : kappa * rhoCard * childCount <= C ^ 4 * tauCard) :
    kappa * tau ^ 2 * childCount <= C ^ 4 * Xi * rho ^ 2 := by
  apply le_of_mul_le_mul_right _ hrhoCard
  calc
    (kappa * tau ^ 2 * childCount) * rhoCard =
        tau ^ 2 * (kappa * rhoCard * childCount) := by ring
    _ <= tau ^ 2 * (C ^ 4 * tauCard) := mul_le_mul_right haverage (tau ^ 2)
    _ = C ^ 4 * (tau ^ 2 * tauCard) := by ring
    _ <= C ^ 4 * (Xi * rho ^ 2 * rhoCard) := mul_le_mul_right hupper (C ^ 4)
    _ = (C ^ 4 * Xi * rho ^ 2) * rhoCard := by ring

/-- Divide a cross-multiplied local band by the positive rho scale. -/
theorem normalizedQBand_of_crossMultiplied
    {theta kappa C Xi tau rho childCount : NNReal} (hrho : 0 < rho)
    (hlower : theta * kappa * rho ^ 2 <= C ^ 4 * tau ^ 2 * childCount)
    (hupper : kappa * tau ^ 2 * childCount <= C ^ 4 * Xi * rho ^ 2) :
    theta * kappa <= C ^ 4 * (tau / rho) ^ 2 * childCount ∧
      kappa * (tau / rho) ^ 2 * childCount <= C ^ 4 * Xi := by
  have hrho2 : 0 < rho ^ 2 := pow_pos hrho 2
  constructor
  · rw [show C ^ 4 * (tau / rho) ^ 2 * childCount =
        (C ^ 4 * tau ^ 2 * childCount) / rho ^ 2 by
      field_simp]
    exact (le_div_iff₀ hrho2).mpr hlower
  · rw [show kappa * (tau / rho) ^ 2 * childCount =
        (kappa * tau ^ 2 * childCount) / rho ^ 2 by
      field_simp]
    exact (div_le_iff₀ hrho2).mpr hupper

/-- If `delta <= tau` and `rho <= 1`, then `delta <= tau / rho`. -/
theorem scale_le_ratio_of_le_of_le_one {delta tau rho : NNReal} (hrho : 0 < rho)
    (hdeltaTau : delta <= tau) (hrhoOne : rho <= 1) :
    delta <= tau / rho := by
  apply (le_div_iff₀ hrho).mpr
  calc
    delta * rho <= delta * 1 := mul_le_mul_right hrhoOne delta
    _ = delta := mul_one delta
    _ <= tau := hdeltaTau

/-- An upper scale comparison passes to the corresponding ratio. -/
theorem ratio_le_of_le_mul {tau rho bound : NNReal} (hrho : 0 < rho)
    (htau : tau <= bound * rho) :
    tau / rho <= bound := by
  exact (div_le_iff₀ hrho).mpr htau

/-- The retained hierarchy balance transports a two-sided global ratio to every live rho fibre. -/
theorem canonicalQBand_of_globalRatioBand
    {ι : Type u} {delta : NNReal} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C kappa theta Xi : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hs : s.Nonempty)
    {b a : Nat} (hab : a <= b) (hb : b <= N) {tauNodes : Finset ι}
    (htau : tauNodes ⊆ U.cover.indexSet b)
    (hretain : ∀ p ∈ activeRhoParents U b a tauNodes,
      kappa * canonicalChildCount U b a p <=
        retainedCanonicalChildCount U b a tauNodes p)
    {p : ι} (hp : p ∈ activeRhoParents U b a tauNodes)
    (hcross : hierarchyGlobalCrossing U b tauNodes theta a)
    (hupper : GlobalRatioUpperBound Xi (_root_.Tube.gridScale delta N b)
      (_root_.Tube.gridScale delta N a) tauNodes.card
      (activeRhoParents U b a tauNodes).card) :
    theta * kappa * (_root_.Tube.gridScale delta N a) ^ 2 <=
        C ^ 4 * (_root_.Tube.gridScale delta N b) ^ 2 *
          retainedCanonicalChildCount U b a tauNodes p ∧
      kappa * (_root_.Tube.gridScale delta N b) ^ 2 *
          retainedCanonicalChildCount U b a tauNodes p <=
        C ^ 4 * Xi * (_root_.Tube.gridScale delta N a) ^ 2 := by
  have hrhoCard :
      0 < (((activeRhoParents U b a tauNodes).card : Nat) : NNReal) := by
    exact_mod_cast Finset.card_pos.mpr ⟨p, hp⟩
  constructor
  · exact localLowerQ_of_globalCrossing hrhoCard hcross
      (retainedFineCard_le_coarseCard_mul_childCount
        U hs hab hb htau hretain hp)
  · exact localUpperQ_of_globalRatioUpperBound hrhoCard hupper
      (retainedCoarseCard_mul_childCount_le U hs hab hb htau hretain hp)

/-- Normalized hierarchy Q band with `q = tau / rho`. -/
theorem canonicalNormalizedQBand_of_globalRatioBand
    {ι : Type u} {delta : NNReal} {s : Finset ι}
    {T : ι -> Tube delta E} {N : Nat} {C kappa theta Xi : NNReal}
    (U : _root_.Tube.UniformTubeSet s T N C) (hdelta : 0 < delta) (hs : s.Nonempty)
    {b a : Nat} (hab : a <= b) (hb : b <= N) {tauNodes : Finset ι}
    (htau : tauNodes ⊆ U.cover.indexSet b)
    (hretain : ∀ p ∈ activeRhoParents U b a tauNodes,
      kappa * canonicalChildCount U b a p <=
        retainedCanonicalChildCount U b a tauNodes p)
    {p : ι} (hp : p ∈ activeRhoParents U b a tauNodes)
    (hcross : hierarchyGlobalCrossing U b tauNodes theta a)
    (hupper : GlobalRatioUpperBound Xi (_root_.Tube.gridScale delta N b)
      (_root_.Tube.gridScale delta N a) tauNodes.card
      (activeRhoParents U b a tauNodes).card) :
    theta * kappa <=
        C ^ 4 * (_root_.Tube.gridScale delta N b / _root_.Tube.gridScale delta N a) ^ 2 *
          retainedCanonicalChildCount U b a tauNodes p ∧
      kappa * (_root_.Tube.gridScale delta N b / _root_.Tube.gridScale delta N a) ^ 2 *
          retainedCanonicalChildCount U b a tauNodes p <=
        C ^ 4 * Xi := by
  have hband := canonicalQBand_of_globalRatioBand
    U hs hab hb htau hretain hp hcross hupper
  exact normalizedQBand_of_crossMultiplied
    (_root_.Tube.gridScale_pos hdelta N a) hband.1 hband.2

end

end Kakeya.WangZahl
