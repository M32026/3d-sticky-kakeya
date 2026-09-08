/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Cases
public import Kakeya.DimensionThree.MainLemma1.ThreePass
public import Kakeya.DimensionThree.MainLemma1.W44NormalizationCardPort

/-!
# Honest normalization for the WZ middle scale

In the WZ separation window the truncated output scale `fineScale tau rho` is eventually the
exact ratio `tau / rho`. This module uses that identity to turn the existing fine-normalization
construction into an honest family of shaded `(tau / rho)`-tubes. The remaining ambient-density
factor in the maximal-density estimate stays explicit for the dynamic producer to bound.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody Filter Topology

namespace Kakeya.ml1Boot

universe u

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [MeasurableSpace E] [BorelSpace E]

/-- Transport a shaded tube across an equality of its scale index. -/
def castShadedTubeScale {a b : NNReal} (h : a = b) (T : ShadedTube a E) : ShadedTube b E :=
  h ▸ T

@[simp] theorem castScale_carrier {a b : NNReal} (h : a = b) (T : ShadedTube a E) :
    (castShadedTubeScale h T).carrier = T.carrier := by
  subst b
  rfl

@[simp] theorem castScale_shade {a b : NNReal} (h : a = b) (T : ShadedTube a E) :
    (castShadedTubeScale h T).shade = T.shade := by
  subst b
  rfl

@[simp] theorem castScale_toShadedBody {a b : NNReal} (h : a = b) (T : ShadedTube a E) :
    (castShadedTubeScale h T).toShadedBody = T.toShadedBody := by
  subst b
  rfl

@[simp] theorem castScale_toConvexSpaceBody {a b : NNReal} (h : a = b)
    (T : ShadedTube a E) :
    (castShadedTubeScale h T).toConvexSpaceBody = T.toConvexSpaceBody := by
  subst b
  rfl

/-- The truncation in `fineScale` is inactive when the scale ratio is at most `1 / 4`. -/
theorem fineScale_eq_div_of_div_le_quarter {tau rho : NNReal}
    (h : tau / rho <= 1 / 4) :
    fineScale tau rho = tau / rho := by
  exact min_eq_left h

/-- WZ separation eventually makes the honest replacement scale exactly `tau / rho`. -/
theorem eventually_fineScale_eq_ratio_of_wz_separation {zeta : Real} (hzeta : 0 < zeta) :
    ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      ∀ tau rho : NNReal, tau / rho <= delta ^ (zeta / 5) ->
        fineScale tau rho = tau / rho := by
  filter_upwards [eventually_rpow_le_quarter
      (show 0 < zeta / 5 by positivity)] with delta hquarter
  intro tau rho hsep
  have hquarterNN : delta ^ (zeta / 5) <= (1 / 4 : NNReal) := by
    exact_mod_cast hquarter.2
  exact fineScale_eq_div_of_div_le_quarter (hsep.trans hquarterNN)

/-- Transport a source Q-window through a selected normalization subfamily.

Only the selection constant is cancelled.  The scale factor remains in multiplicative form, so
this lemma does not require a separate positivity proof for `q`. -/
theorem qBand_transport_of_cardRetention {ι : Type*} {q C : NNReal} {L U : ENNReal}
    {s s' : Finset ι} (hC : 1 <= C) (hsub : s' ⊆ s)
    (hretain : (s.card : ENNReal) <= (C : ENNReal) * (s'.card : ENNReal))
    (hlower : L <= (q : ENNReal) ^ 2 * (s.card : ENNReal))
    (hupper : (q : ENNReal) ^ 2 * (s.card : ENNReal) <= U) :
    (C : ENNReal)⁻¹ * L <= (q : ENNReal) ^ 2 * (s'.card : ENNReal) ∧
      (q : ENNReal) ^ 2 * (s'.card : ENNReal) <= U := by
  have hC0 : (C : ENNReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hC))
  have hCtop : (C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  constructor
  · calc
      (C : ENNReal)⁻¹ * L
          <= (C : ENNReal)⁻¹ * ((C : ENNReal) * ((q : ENNReal) ^ 2 * (s'.card : ENNReal))) := by
            gcongr
            calc
              L <= (q : ENNReal) ^ 2 * (s.card : ENNReal) := hlower
              _ <= (q : ENNReal) ^ 2 * ((C : ENNReal) * (s'.card : ENNReal)) := by
                gcongr
              _ = (C : ENNReal) * ((q : ENNReal) ^ 2 * (s'.card : ENNReal)) := by ring
      _ = (q : ENNReal) ^ 2 * (s'.card : ENNReal) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hC0 hCtop, one_mul]
  · calc
      (q : ENNReal) ^ 2 * (s'.card : ENNReal)
          <= (q : ENNReal) ^ 2 * (s.card : ENNReal) := by
            gcongr
      _ <= U := hupper

noncomputable abbrev wzNormalizedTubeDensityC : NNReal :=
  _root_.Tube.volume_le.C 3 / (3 * _root_.Tube.le_volume.c 3)

/-- Density in the unit ball of honest three-dimensional `q`-tubes, before simplifying the
dimensional volume constant.  No packing or essential-distinctness assumption is used. -/
theorem wz_densityIn_unitBall_le_qsq_card [Nontrivial E]
    (hdim : Module.finrank Real E = 3) {ι : Type*} {s : Finset ι} {q : NNReal}
    (hq1 : q <= 1) (T : ι -> Tube q E)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) :
    densityIn s (fun i => (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
      (wzNormalizedTubeDensityC : ENNReal) *
        ((q : ENNReal) ^ (2 : Nat) * (s.card : ENNReal)) := by
  have hbody : ∀ i ∈ s, (T i).toConvexSpaceBody <=
      (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
    intro i hi
    exact SetLike.coe_subset_coe.mpr (hball i hi)
  have hsum : ∑ i ∈ s, volume (T i).carrier <=
      (s.card : ENNReal) *
        ((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal) * (q : ENNReal) ^ (2 : Nat) := by
    calc
      ∑ i ∈ s, volume (T i).carrier
          <= ∑ _i ∈ s, ((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal) *
              (q : ENNReal) ^ (2 : Nat) := by
            apply Finset.sum_le_sum
            intro i _hi
            simpa [hdim] using (_root_.Tube.volume_le hq1 (T i))
      _ = (s.card : ENNReal) *
          ((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal) *
            (q : ENNReal) ^ (2 : Nat) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  rw [densityIn_of_all_le hbody, volume_closedUnitBall_eq (E := E), hdim]
  calc
    (∑ i ∈ s, volume (T i).carrier) /
          (((3 * _root_.Tube.le_volume.c 3 : NNReal) : ENNReal))
        <= ((s.card : ENNReal) *
              ((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal) *
                (q : ENNReal) ^ (2 : Nat)) /
            (((3 * _root_.Tube.le_volume.c 3 : NNReal) : ENNReal)) :=
      ENNReal.div_le_div_right hsum _
    _ = (wzNormalizedTubeDensityC : ENNReal) *
        ((q : ENNReal) ^ (2 : Nat) * (s.card : ENNReal)) := by
      change _ =
        ((_root_.Tube.volume_le.C 3 /
            (3 * _root_.Tube.le_volume.c 3) : NNReal) : ENNReal) *
          ((q : ENNReal) ^ (2 : Nat) * (s.card : ENNReal))
      rw [ENNReal.coe_div (mul_ne_zero (by norm_num)
        (_root_.Tube.le_volume.c_pos 3).ne')]
      simp only [ENNReal.coe_mul, ENNReal.coe_ofNat]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring

theorem wzNormalizedTubeDensityC_le_four :
    wzNormalizedTubeDensityC <= 4 := by
  have hcR : (0 : Real) < (_root_.Tube.le_volume.c 3 : Real) := by
    exact_mod_cast _root_.Tube.le_volume.c_pos 3
  have hCReal : (_root_.Tube.volume_le.C 3 : Real) <=
      12 * (_root_.Tube.le_volume.c 3 : Real) :=
    (div_le_iff₀ hcR).mp _root_.Tube.volume_ratio_three_le_twelve
  have hCNN : _root_.Tube.volume_le.C 3 <= 12 * _root_.Tube.le_volume.c 3 := by
    exact_mod_cast hCReal
  change _root_.Tube.volume_le.C 3 / (3 * _root_.Tube.le_volume.c 3) <= 4
  rw [div_le_iff₀ (mul_pos (by norm_num) (_root_.Tube.le_volume.c_pos 3))]
  convert hCNN using 1 <;> ring

/-- The explicit unit-ball density bound used by the normalized WZ middle packet. -/
theorem wz_densityIn_unitBall_le_four_qsq_card [Nontrivial E]
    (hdim : Module.finrank Real E = 3) {ι : Type*} {s : Finset ι} {q : NNReal}
    (hq1 : q <= 1) (T : ι -> Tube q E)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) :
    densityIn s (fun i => (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
      4 * ((q : ENNReal) ^ (2 : Nat) * (s.card : ENNReal)) := by
  calc
    densityIn s (fun i => (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall
        <= (wzNormalizedTubeDensityC : ENNReal) *
          ((q : ENNReal) ^ (2 : Nat) * (s.card : ENNReal)) :=
      wz_densityIn_unitBall_le_qsq_card hdim hq1 T hball
    _ <= 4 * ((q : ENNReal) ^ (2 : Nat) * (s.card : ENNReal)) := by
      gcongr
      exact_mod_cast wzNormalizedTubeDensityC_le_four

/-- Combine a normalized Frostman bound with the upper Q-band to obtain an absolute max-density
bound.  The two source exponents are kept separate and add as `zF + zQ`. -/
theorem wz_maxDensity_le_of_frostman_qBand [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {ι : Type*} {s : Finset ι} {delta q CF CQ : NNReal} {zF zQ : Real}
    (hdelta0 : 0 < delta) (hq1 : q <= 1) (V : ι -> ShadedTube q E)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (hFrost : frostmanConstIn s (fun i => (V i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall <=
          (CF : ENNReal) * (delta : ENNReal) ^ (-zF))
    (hQhi : (q : ENNReal) ^ (2 : Nat) * (s.card : ENNReal) <=
      (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ)) :
    maxDensity s (fun i => (V i).toConvexSpaceBody) <=
      ((4 * CF * CQ : NNReal) : ENNReal) *
        (delta : ENNReal) ^ (-(zF + zQ)) := by
  have hbody : ∀ i ∈ s, (V i).toConvexSpaceBody <=
      (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
    intro i hi
    exact SetLike.coe_subset_coe.mpr (hball i hi)
  have hFr := isFrostmanIn_of_frostmanConstIn_le hFrost
  have hmax := hFr.maxDensity_le_of_carrier_subset hbody
  have hdens := wz_densityIn_unitBall_le_four_qsq_card hdim hq1
    (fun i => (V i).toTube) hball
  have hdeltaE0 : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta0.ne'
  have hdeltaEtop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  calc
    maxDensity s (fun i => (V i).toConvexSpaceBody)
        <= ((CF : ENNReal) * (delta : ENNReal) ^ (-zF)) *
          densityIn s (fun i => (V i).toConvexSpaceBody)
            ConvexSpaceBody.closedUnitBall := hmax
    _ <= ((CF : ENNReal) * (delta : ENNReal) ^ (-zF)) *
        (4 * ((q : ENNReal) ^ (2 : Nat) * (s.card : ENNReal))) := by gcongr
    _ <= ((CF : ENNReal) * (delta : ENNReal) ^ (-zF)) *
        (4 * ((CQ : ENNReal) * (delta : ENNReal) ^ (-zQ))) := by gcongr
    _ = ((4 * CF * CQ : NNReal) : ENNReal) *
        (delta : ENNReal) ^ (-(zF + zQ)) := by
      rw [show -(zF + zQ) = -zF + -zQ by ring,
        ENNReal.rpow_add (-zF) (-zQ) hdeltaE0 hdeltaEtop]
      push_cast
      ring

/-- FNL-facing form of the absolute max-density supplier, with the source Frostman loss visible. -/
theorem wz_maxDensity_le_of_fnl_relative_to_budget [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {ι : Type*} {s : Finset ι} {delta q CFN Csrc CQ CDelta : NNReal}
    {sourceFrost : ENNReal} {zF zQ zD : Real}
    (hdelta0 : 0 < delta) (hdelta1 : delta <= 1) (hq1 : q <= 1)
    (hC : 4 * (CFN * Csrc) * CQ <= CDelta) (hz : zF + zQ <= zD)
    (V : ι -> ShadedTube q E)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1)
    (hFNL : frostmanConstIn s (fun i => (V i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall <= (CFN : ENNReal) * sourceFrost)
    (hsource : sourceFrost <= (Csrc : ENNReal) * (delta : ENNReal) ^ (-zF))
    (hQhi : (q : ENNReal) ^ (2 : Nat) * (s.card : ENNReal) <=
      (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ)) :
    maxDensity s (fun i => (V i).toConvexSpaceBody) <=
      (CDelta : ENNReal) * (delta : ENNReal) ^ (-zD) := by
  have hFrost : frostmanConstIn s (fun i => (V i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall <=
        ((CFN * Csrc : NNReal) : ENNReal) * (delta : ENNReal) ^ (-zF) := by
    calc
      frostmanConstIn s (fun i => (V i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall <= (CFN : ENNReal) * sourceFrost := hFNL
      _ <= (CFN : ENNReal) *
          ((Csrc : ENNReal) * (delta : ENNReal) ^ (-zF)) := by gcongr
      _ = ((CFN * Csrc : NNReal) : ENNReal) *
          (delta : ENNReal) ^ (-zF) := by
            push_cast
            ring
  have hraw := wz_maxDensity_le_of_frostman_qBand (CF := CFN * Csrc) (CQ := CQ)
    (zF := zF) (zQ := zQ) hdim hdelta0 hq1 V hball hFrost hQhi
  calc
    maxDensity s (fun i => (V i).toConvexSpaceBody)
        <= ((4 * (CFN * Csrc) * CQ : NNReal) : ENNReal) *
          (delta : ENNReal) ^ (-(zF + zQ)) := hraw
    _ <= (CDelta : ENNReal) * (delta : ENNReal) ^ (-zD) := by
      apply mul_le_mul'
      · exact_mod_cast hC
      · exact ENNReal.rpow_le_rpow_of_exponent_ge
          (by exact_mod_cast hdelta1) (by linarith)

/-- Cancel a finite positive normalization loss after the producer has funded it. -/
theorem fullness_lower_of_funded_comparison {K source target : ENNReal}
    {delta : NNReal} {etaIn etaM : Real} (hK0 : K ≠ 0) (hKtop : K ≠ ⊤)
    (hfund : (delta : ENNReal) ^ etaM * K <= (delta : ENNReal) ^ etaIn)
    (hsource : (delta : ENNReal) ^ etaIn <= source)
    (hcompare : source <= K * target) :
    (delta : ENNReal) ^ etaM <= target := by
  apply (ENNReal.mul_le_mul_iff_left hK0 hKtop).mp
  calc
    (delta : ENNReal) ^ etaM * K <= (delta : ENNReal) ^ etaIn := hfund
    _ <= source := hsource
    _ <= target * K := by simpa [mul_comm] using hcompare

/-- Complete the quantitative normalization ledger on the same selected family.

The theorem performs no selection.  Its card, fullness and Frostman hypotheses are precisely the
three comparisons returned together by `exists_wzMiddleNormalization`; all remaining assumptions
are source-side producer data or explicit loss budgets. -/
theorem wz_normalizedMiddle_bounds [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {ι : Type*} {s s' : Finset ι} {delta q Lambda CFr CQ CDelta : NNReal}
    {etaIn etaM zFr zQ zD : Real} {sourceFrost : ENNReal}
    (hdelta0 : 0 < delta) (hdelta1 : delta <= 1) (hq1 : q <= 1)
    (hLambda : 1 <= Lambda)
    (V : ι -> ShadedTube q E) (hsub : s' ⊆ s)
    (hcard : (s.card : ENNReal) <=
      (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal) * (s'.card : ENNReal))
    (hball : ∀ i ∈ s', (V i).carrier ⊆ Metric.closedBall 0 1)
    (hfullCompare : (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) <=
      (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal) *
        (Lambda : ENNReal) ^ 2 *
          (ShadedBody.fullness s' (fun i => (V i).toShadedBody) : ENNReal))
    (hfullSource : (delta : ENNReal) ^ etaIn <=
      (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal))
    (hfullFund : (delta : ENNReal) ^ etaM *
      ((fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal) *
        (Lambda : ENNReal) ^ 2) <= (delta : ENNReal) ^ etaIn)
    (hFNL : frostmanConstIn s' (fun i => (V i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall <=
        (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal) * sourceFrost)
    (hsourceFrost : sourceFrost <= (CFr : ENNReal) * (delta : ENNReal) ^ (-zFr))
    (hQlo : (CQ : ENNReal)⁻¹ * (delta : ENNReal) ^ zQ <=
      (q : ENNReal) ^ (2 : Nat) * (s.card : ENNReal))
    (hQhi : (q : ENNReal) ^ (2 : Nat) * (s.card : ENNReal) <=
      (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ))
    (hCDelta : 4 * (fineNormalize.C (_root_.Tube.normalization.C 3) * CFr) * CQ <= CDelta)
    (hzD : zFr + zQ <= zD) :
    (delta : ENNReal) ^ etaM <=
        (ShadedBody.fullness s' (fun i => (V i).toShadedBody) : ENNReal) ∧
      (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal)⁻¹ *
          ((CQ : ENNReal)⁻¹ * (delta : ENNReal) ^ zQ) <=
        (q : ENNReal) ^ (2 : Nat) * (s'.card : ENNReal) ∧
      (q : ENNReal) ^ (2 : Nat) * (s'.card : ENNReal) <=
        (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ) ∧
      maxDensity s' (fun i => (V i).toConvexSpaceBody) <=
        (CDelta : ENNReal) * (delta : ENNReal) ^ (-zD) := by
  let Cfn : NNReal := fineNormalize.C (_root_.Tube.normalization.C 3)
  have hCfn : 1 <= Cfn :=
    one_le_fineNormalize_C (_root_.Tube.normalization.one_le_C 3)
  have hK0 : (Cfn : ENNReal) * (Lambda : ENNReal) ^ 2 ≠ 0 := by
    apply mul_ne_zero
    · exact ENNReal.coe_ne_zero.mpr (lt_of_lt_of_le zero_lt_one hCfn).ne'
    · exact pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr
        (lt_of_lt_of_le zero_lt_one hLambda).ne')
  have hKtop : (Cfn : ENNReal) * (Lambda : ENNReal) ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hfull : (delta : ENNReal) ^ etaM <=
      (ShadedBody.fullness s' (fun i => (V i).toShadedBody) : ENNReal) :=
    fullness_lower_of_funded_comparison hK0 hKtop (by simpa [Cfn] using hfullFund)
      hfullSource (by simpa [Cfn, mul_assoc] using hfullCompare)
  have hQ := qBand_transport_of_cardRetention hCfn hsub (by simpa [Cfn] using hcard)
    hQlo hQhi
  have hmax : maxDensity s' (fun i => (V i).toConvexSpaceBody) <=
      (CDelta : ENNReal) * (delta : ENNReal) ^ (-zD) :=
    wz_maxDensity_le_of_fnl_relative_to_budget hdim hdelta0 hdelta1 hq1
      (by simpa [Cfn] using hCDelta) hzD V hball (by simpa [Cfn] using hFNL)
      hsourceFrost hQ.2
  exact ⟨hfull, by simpa [Cfn] using hQ.1, hQ.2, hmax⟩

/-- Construct the honest normalized family used by the WZ middle estimate.

The maximal-density conclusion deliberately retains the ambient density in `B_1`. A later
balanced-block producer must bound that quantity absolutely; a Frostman constant alone does not.
-/
theorem exists_wzMiddleNormalization (hdim : Module.finrank Real E = 3)
    {zeta : Real} (hzeta : 0 < zeta) :
    ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
      ∀ {tau rho : NNReal}, 0 < tau -> tau <= rho -> rho <= 1 ->
        tau / rho <= delta ^ (zeta / 5) ->
      ∀ {Lambda : NNReal}, 1 <= Lambda -> {mu0 : ENNReal} -> 0 < mu0 ->
      ∀ {iota : Type u} {s ambient : Finset iota} (Trho : Tube rho E)
        (Ttau : iota -> ShadedTube tau E),
        s.Nonempty -> s ⊆ ambient ->
        (∀ i ∈ ambient, (Ttau i).carrier ⊆ Trho.carrier) ->
        (s : Set iota).Pairwise
          (fun i j => IsEssentiallyDistinct (Ttau i).carrier (Ttau j).carrier) ->
        (∀ i ∈ s, (Lambda : ENNReal)⁻¹ * mu0 * volume (Ttau i).carrier
            <= volume (Ttau i).shade ∧
          volume (Ttau i).shade <=
            (Lambda : ENNReal) * mu0 * volume (Ttau i).carrier) ->
        ∃ s' ⊆ s, s'.Nonempty ∧ ∃ V : iota -> ShadedTube (tau / rho) E,
          (s' : Set iota).Pairwise
              (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) ∧
          (s.card : ENNReal) <=
            (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal) *
              (s'.card : ENNReal) ∧
          (∀ i ∈ s', (V i).carrier ⊆ Metric.closedBall 0 1) ∧
          ShadedBody.multiplicity s (fun i => (Ttau i).toShadedBody)
            <= (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal)
              * (Lambda : ENNReal) ^ 2
              * ShadedBody.multiplicity s' (fun i => (V i).toShadedBody) ∧
          (ShadedBody.fullness s (fun i => (Ttau i).toShadedBody) : ENNReal)
            <= (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal)
              * (Lambda : ENNReal) ^ 2
              * (ShadedBody.fullness s' (fun i => (V i).toShadedBody) : ENNReal) ∧
          (s'.card : ENNReal) <= (s.card : ENNReal) ∧
          frostmanConstIn s' (fun i => (V i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall
            <= (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal)
              * frostmanConstIn s (fun i => (Ttau i).toConvexSpaceBody)
                  Trho.toConvexSpaceBody ∧
          maxDensity s' (fun i => (V i).toConvexSpaceBody)
            <= ((fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal)
                * frostmanConstIn s (fun i => (Ttau i).toConvexSpaceBody)
                    Trho.toConvexSpaceBody)
              * densityIn s' (fun i => (V i).toConvexSpaceBody)
                  ConvexSpaceBody.closedUnitBall := by
  filter_upwards [eventually_fineScale_eq_ratio_of_wz_separation hzeta]
    with delta hscale
  intro tau rho htau0 htaurho hrho1 hsep Lambda hLambda mu0 hmu0 iota s ambient
    Trho Ttau hs hsambient hcontain hED hdens
  have hscaleEq : fineScale tau rho = tau / rho :=
    hscale tau rho hsep
  obtain ⟨s', hs's, hs'ne, V0, hVED, hcard, hball, hmult, hfull, hfrost, -, -, -, -, -⟩ :=
    W44NormalizationPort.exists_fineNormalization_constructionVisible_withCard
      hdim htau0 htaurho hrho1 hLambda hmu0
      Trho Ttau hs hsambient hcontain hED hdens
  let V : iota -> ShadedTube (tau / rho) E := fun i => castShadedTubeScale hscaleEq (V0 i)
  have hVED' : (s' : Set iota).Pairwise
      (fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier) := by
    simpa [V] using hVED
  have hball' : ∀ i ∈ s', (V i).carrier ⊆ Metric.closedBall 0 1 := by
    simpa [V] using hball
  have hmult' :
      ShadedBody.multiplicity s (fun i => (Ttau i).toShadedBody)
        <= (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal)
          * (Lambda : ENNReal) ^ 2
          * ShadedBody.multiplicity s' (fun i => (V i).toShadedBody) := by
    simpa [V] using hmult
  have hfull' :
      (ShadedBody.fullness s (fun i => (Ttau i).toShadedBody) : ENNReal)
        <= (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal)
          * (Lambda : ENNReal) ^ 2
          * (ShadedBody.fullness s' (fun i => (V i).toShadedBody) : ENNReal) := by
    simpa [V] using hfull
  have hfrost' :
      frostmanConstIn s' (fun i => (V i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall
        <= (fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal)
          * frostmanConstIn s (fun i => (Ttau i).toConvexSpaceBody)
              Trho.toConvexSpaceBody := by
    simpa [V] using hfrost
  have hbody : ∀ i ∈ s', (V i).toConvexSpaceBody <=
      ConvexSpaceBody.closedUnitBall := by
    intro i hi
    change (V i).carrier ⊆ ConvexSpaceBody.closedUnitBall.carrier
    rw [ConvexSpaceBody.closedUnitBall_carrier]
    exact hball' i hi
  have hFr : IsFrostmanIn s' (fun i => (V i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall
      ((fineNormalize.C (_root_.Tube.normalization.C 3) : ENNReal)
        * frostmanConstIn s (fun i => (Ttau i).toConvexSpaceBody)
            Trho.toConvexSpaceBody) :=
    isFrostmanIn_of_frostmanConstIn_le hfrost'
  refine ⟨s', hs's, hs'ne, V, hVED', hcard, hball', hmult', hfull', ?_, hfrost', ?_⟩
  · exact_mod_cast Finset.card_le_card hs's
  · exact hFr.maxDensity_le_of_carrier_subset hbody

end Kakeya.ml1Boot
