/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceQAllRadius
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceFactorCeilings

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Kakeya.ML2Core Kakeya.ML2Reduction Kakeya.VeryNotSticky
open scoped NNReal ENNReal

namespace Kakeya.ML2Assembly

universe u

/-- The fixed-Q entrance allows the source delta^-5 cardinal bound.
This replaces the old SSF caller's delta^-4 calibration explicitly. -/
noncomputable def sourceQMiddleCardPower (e : Real) : Nat := Nat.ceil (10 / e) + 1

variable {iota : Type u}

/-- All R4 antecedents on the Q-selected F, without an SSF ambient identity. -/
theorem sourceQ_middle_original_bounds {delta : NNReal} {S : Finset iota}
    {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
    (Q : SourceThreadedTower S T M C) {a p b N J : Nat} {jp : iota} {F : Finset iota}
    (Z : iota -> ShadedTube (sourceTowerRadius delta M b) (EuclideanSpace Real (Fin 3)))
    {rho : NNReal} {e zeta etaC q gamma etaD R : Real} {A0 A1 : Nat}
    (hinput : SourceQCoverInput Q a p b jp F Z rho e zeta etaC)
    (eta : Nat -> Real)
    (hwindow : SourceTowerDividingWindow Q A0 A1 N eta e a b J)
    (hsit : Tube.IsRescalingSituation (sourceTowerRadius delta M p)
      (sourceTowerRadius delta M b) rho R 3) (hR : 0 < R)
    (he : 0 < e) (hrho : rho <= 1) (hS : (S.card : Real) <= (delta : Real) ^ (-(5 : Real)))
    (hfull : rho ^ gamma <= (outerLoss R)⁻¹ * ShadedBody.fullness F
      (fun i => (Z i).toShadedBody))
    (hnormalized : (outerLoss R : ENNReal) * ENNReal.ofReal
      (((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M b : Real)) ^ eta J) <=
        (rho : ENNReal) ^ (-q))
    (horiginal : ENNReal.ofReal
      (((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M b : Real)) ^ eta J) <=
        (rho : ENNReal) ^ (-(etaD - q))) :
    (forall i, i ∈ F -> (Z i).carrier <= (Q.tube p jp).carrier) /\
    0 < sourceQMiddleCardPower e /\
    (F.card : Real) <= (rho : Real) ^ (-(sourceQMiddleCardPower e : Real)) /\
    Kakeya.maxDensity F (fun i => (Z i).toConvexSpaceBody) <=
      (rho : ENNReal) ^ (-(etaD - q)) /\
    Kakeya.maxDensity F (fun i =>
      (outerFamily hsit.pos_ambient (Q.tube p jp) hR rho Z i).toConvexSpaceBody) <=
        (rho : ENNReal) ^ (-q) /\
    (rho : ENNReal) ^ gamma <= ShadedBody.fullness F (fun i =>
      (outerFamily hsit.pos_ambient (Q.tube p jp) hR rho Z i).toShadedBody) := by
  classical
  have hpM : p <= M := hinput.parent_lt_middle.le.trans hinput.middle_bound
  have hancestor := sourceQ_ancestor_fibre_identities Q hinput.coarse_le_parent hpM
  have hmiddle := sourceQ_ancestor_fibre_identities Q hinput.parent_lt_middle.le hinput.middle_bound
  let ja := sourceQAncestor Q a p jp
  have hja : ja ∈ Q.indexSet a := hancestor.2.1 jp hinput.parent_member
  have hsub : forall i, i ∈ F -> (Z i).carrier <= (Q.tube p jp).carrier := by
    intro i hi
    have hmem := hinput.family_subset hi
    rw [hmiddle.2.2.2 jp hinput.parent_member] at hmem
    obtain ⟨hib, hip⟩ := Finset.mem_filter.mp hmem
    have hh := hmiddle.2.2.1 i hib
    rw [hip] at hh
    change (Z i).toConvexSpaceBody <= (Q.tube p jp).toConvexSpaceBody
    rw [show (Z i).toConvexSpaceBody = (Q.tube b i).toConvexSpaceBody from
      congrArg Tube.toConvexSpaceBody (hinput.family_tubes i)]
    exact hh
  have hFab : F <= Q.fibre a b ja := by
    intro i hi
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp (hinput.family_subset hi)
    obtain ⟨hlS, hlp⟩ := Finset.mem_filter.mp hl
    apply Finset.mem_image.mpr
    refine ⟨l, Finset.mem_filter.mpr ⟨hlS, ?_⟩, rfl⟩
    change Q.place a l = sourceQAncestor Q a p jp
    rw [← hancestor.1 l hlS, hlp]
  have hcardS : F.card <= S.card :=
    (Finset.card_le_card hinput.family_subset).trans
      (Finset.card_image_le.trans (Finset.card_le_card (Finset.filter_subset _ _)))
  have hdelta1 : delta <= 1 := hinput.delta_small.le.trans
    (NNReal.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.mpr (Nat.cast_nonneg M)))
  have hdeltaR : (0 : Real) < delta := by exact_mod_cast hinput.delta_pos
  have hrhoR : (0 : Real) < rho := by exact_mod_cast hsit.pos_out
  have hpower : 5 <= e * (sourceQMiddleCardPower e : Real) / 2 := by
    have hh := (div_le_iff₀ he).mp (Nat.le_ceil (10 / e))
    simp only [sourceQMiddleCardPower, Nat.cast_add, Nat.cast_one]
    nlinarith
  have hcard : (F.card : Real) <= (rho : Real) ^ (-(sourceQMiddleCardPower e : Real)) := by
    have hrs : (rho : Real) <= (delta : Real) ^ (e / 2) :=
      hinput.rho_upper.trans (div_le_self (Real.rpow_nonneg delta.coe_nonneg _) (by norm_num))
    calc (F.card : Real) <= (S.card : Real) := by exact_mod_cast hcardS
      _ <= (delta : Real) ^ (-(5 : Real)) := hS
      _ <= (delta : Real) ^ ((e / 2) * (-(sourceQMiddleCardPower e : Real))) :=
        Real.rpow_le_rpow_of_exponent_ge hdeltaR hdelta1 (by nlinarith)
      _ = ((delta : Real) ^ (e / 2)) ^ (-(sourceQMiddleCardPower e : Real)) :=
        Real.rpow_mul delta.coe_nonneg _ _
      _ <= (rho : Real) ^ (-(sourceQMiddleCardPower e : Real)) :=
        Real.rpow_le_rpow_of_nonpos hrhoR hrs
          (neg_nonpos.mpr (Nat.cast_nonneg (sourceQMiddleCardPower e)))
  have hdensity : Kakeya.maxDensity F (fun i => (Z i).toConvexSpaceBody) <=
      ENNReal.ofReal (((sourceTowerRadius delta M a : Real) /
        (sourceTowerRadius delta M b : Real)) ^ eta J) := by
    have hbodies : (fun i => (Z i).toConvexSpaceBody) =
        (fun i => (Q.tube b i).toConvexSpaceBody) := by
      funext i
      exact congrArg Tube.toConvexSpaceBody (hinput.family_tubes i)
    rw [hbodies]
    exact (Kakeya.maxDensity_mono _ hFab).trans (hwindow.middle_density ja hja)
  have hR1 : 1 <= R := (by exact_mod_cast Tube.normalization.one_le_C 3 :
    (1 : Real) <= (Tube.normalization.C 3 : Real)).trans hsit.normalizationConst_le_radius
  have hratio : (sourceTowerRadius delta M b : Real) /
      (sourceTowerRadius delta M p : Real) <= 4 * (rho : Real) := by
    have heq : (rho : Real) = (sourceTowerRadius delta M b : Real) /
        (2 * (sourceTowerRadius delta M p : Real)) := by exact_mod_cast hinput.rho_eq
    rw [heq]
    have hpos : (0 : Real) < sourceTowerRadius delta M p := by exact_mod_cast hsit.pos_ambient
    field_simp
    nlinarith [NNReal.coe_nonneg (sourceTowerRadius delta M b)]
  refine ⟨hsub, by unfold sourceQMiddleCardPower; omega, hcard,
    hdensity.trans horiginal, ?_, ?_⟩
  · exact (outerFamily_maxDensity_le (by simp) hsit hR hR1 hratio hsub).trans
      ((mul_le_mul_right hdensity _).trans hnormalized)
  · have hh := hfull.trans (outerFamily_le_fullness (by simp) hsit hR hR1 hratio hsub)
    have hc : ((rho ^ gamma : NNReal) : ENNReal) <=
        (ShadedBody.fullness F (fun i =>
          (outerFamily hsit.pos_ambient (Q.tube p jp) hR rho Z i).toShadedBody) : ENNReal) := by
      exact_mod_cast hh
    simpa only [ENNReal.coe_rpow_of_ne_zero hsit.pos_out.ne'] using hc

/-- The exact generic R4 application; all returned rows refer to the same D,E,U0,U1.
The extra original density row is the verified Q-window output above. -/
theorem sourceQ_exists_actual_middle_retention
    (A q gamma alpha alphaPrime etaD : Real)
    (hA : 0 < A) (hq : 0 < q) (hgamma : 0 < gamma)
    (halpha : 0 < alpha) (halphaPrime : 0 < alphaPrime)
    (hgammaq : gamma <= q) (hcardgap : gamma + alpha < A)
    (hmassgap : gamma + alpha + alphaPrime < 3 * q) (hetaD : 3 * q <= etaD)
    (K0 : Nat) (hK0 : 0 < K0) :
    exists rho0 : NNReal, 0 < rho0 /\ rho0 <= 1 / 20 /\
      forall {iota : Type u} {b tau rho : NNReal} {R : Real}
        (hsit : Tube.IsRescalingSituation b tau rho R 3) (hR : 0 < R)
        (T0 : Tube b (EuclideanSpace Real (Fin 3))) (F : Finset iota)
        (Z : iota -> ShadedTube tau (EuclideanSpace Real (Fin 3))),
      1 <= R -> (tau : Real) / (b : Real) <= 4 * (rho : Real) ->
      0 < rho -> rho <= rho0 -> F.Nonempty ->
      (forall i, i ∈ F -> (Z i).carrier <= T0.carrier) ->
      (F.card : Real) <= (rho : Real) ^ (-(K0 : Real)) ->
      (rho : ENNReal) ^ gamma <= ShadedBody.fullness F
        (fun i => (outerFamily hsit.pos_ambient T0 hR rho Z i).toShadedBody) ->
      Kakeya.maxDensity F (fun i =>
        (outerFamily hsit.pos_ambient T0 hR rho Z i).toConvexSpaceBody) <=
          (rho : ENNReal) ^ (-q) ->
      Kakeya.maxDensity F (fun i => (Z i).toConvexSpaceBody) <=
        (rho : ENNReal) ^ (-(etaD - q)) ->
      forall varpi zeta : Real, 0 <= varpi -> 0 <= 2 + zeta -> rho ^ varpi <= 1 / 2 ->
      exists (D E : Finset iota) (U0 U1 : iota -> ShadedTube rho (EuclideanSpace Real (Fin 3))),
        SourceMiddleActualRetention hsit hR T0 A q gamma alpha alphaPrime etaD varpi zeta
          F D E Z U0 U1 := by
  obtain ⟨rho0, hrho0, hrho20, hret⟩ := sourceRetention_exists_normalizedRetention A q hA hq
    gamma alpha alphaPrime hgamma halpha halphaPrime hgammaq hcardgap hmassgap K0 hK0
  refine ⟨rho0, hrho0, hrho20, ?_⟩
  intro iota b tau rho R hsit hR T0 F Z hR1 hratio hrho hrhosmall hF hsub hcard
    hfull hdensity horiginal varpi zeta hvarpi hzeta hwindow
  obtain ⟨D, E, U0, U1, hp, hcount⟩ := hret hsit hR hratio hrho hrhosmall
    T0 F Z hF hsub hcard hdensity hfull varpi zeta hvarpi hzeta hwindow
  have hmultiplicity := outerFamily_multiplicity (by simp) hsit hR hratio hsub
  refine ⟨D, E, U0, U1, {
    paid := hp
    count := hcount
    subset := hp.handBack.subset
    nonempty := hp.prepared.nonempty
    cardinality_retained := ?_
    cardinality_upper := Finset.card_le_card hp.handBack.subset
    mass_retained := ?_
    original_fullness := hfull
    original_density := horiginal
    retained_fullness := hp.handBack.fullness_ge
    vns_fullness := ?_
    retained_density := hp.handBack.maxDensity_le
    uniform := hp.prepared.uniform
    normalized_multiplicity := hmultiplicity
    multiplicity_retained := ?_ }⟩
  · have hh := mul_le_mul_of_nonneg_left hp.card_paid (Real.rpow_nonneg rho.coe_nonneg A)
    have hr : (0 : Real) < rho := by exact_mod_cast hrho
    simpa [← mul_assoc, ← Real.rpow_add hr, Real.rpow_zero] using hh
  · simpa [ENNReal.div_eq_inv_mul, ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real) < 512)]
      using hp.mass_paid
  · have hr1 : (rho : ENNReal) <= 1 := by
      have hrReal : (rho : Real) <= 1 := hsit.out_le_quarter.trans (by norm_num)
      exact_mod_cast hrReal
    exact (ENNReal.rpow_le_rpow_of_exponent_ge hr1 hetaD).trans hp.handBack.fullness_ge
  · rw [← hmultiplicity]
    exact hp.handBack.multiplicity_le

/-- Call Lemma91At directly after producing its real downstairs antecedent.
The old upstairs hED supplier and universal shading hmid are not invoked. -/
theorem sourceMiddle_raw_of_downstairs {b tau rho : NNReal} {R : Real}
    (hsit : Tube.IsRescalingSituation b tau rho R 3) (hR : 0 < R)
    (T0 : Tube b (EuclideanSpace Real (Fin 3)))
    {beta varpi zeta v etaD A q gamma alpha alphaPrime : Real}
    {F D E : Finset iota}
    {Z : iota -> ShadedTube tau (EuclideanSpace Real (Fin 3))}
    {U0 U1 : iota -> ShadedTube rho (EuclideanSpace Real (Fin 3))}
    (hrho : 0 < rho) (hrho1 : rho <= 1) (hq : 0 < q) (h3q : 3 * q <= etaD)
    (hL : Lemma91At.{u} beta varpi zeta v etaD rho)
    (hret : SourceMiddleActualRetention hsit hR T0 A q gamma alpha alphaPrime etaD
      varpi zeta F D E Z U0 U1)
    (hdown : SourceMiddleDownstairsCount hsit hR T0 varpi zeta E Z)
    (huni : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) <=
      (rho : ENNReal) ^ (-etaD)) :
    ShadedBody.multiplicity E (fun i => (U1 i).toShadedBody) <=
      (rho : ENNReal) ^ v * (E.card : ENNReal) ^ beta := by
  have hretained := hret.paid.handBack
  refine hL E U1 ?_ ?_
    ⟨ShadedTube.ssfUniformConst 3, ShadedTube.one_le_ssfUniformConst 3, huni, hret.uniform⟩
    ?_ ?_ ?_
  · exact hretained.contained
  · exact hretained.centred
  · have hr : (rho : ENNReal) <= 1 := by exact_mod_cast hrho1
    exact hret.retained_density.trans
      (ENNReal.rpow_le_rpow_of_exponent_ge hr (by linarith))
  · have hh := hret.vns_fullness
    rw [← ENNReal.coe_rpow_of_ne_zero hrho.ne'] at hh
    exact_mod_cast hh
  · intro sigma hsigma
    exact hret.count sigma hsigma (hdown sigma hsigma)

/-- The same retained witness pays exactly 3q once, then the true raw v is
converted through rho<=delta^(e/2). In the chosen schedule nuMid=v/2. -/
theorem sourceMiddle_selected_handback_gain {delta b tau rho : NNReal} {R : Real}
    (hsit : Tube.IsRescalingSituation b tau rho R 3) (hR : 0 < R)
    (T0 : Tube b (EuclideanSpace Real (Fin 3)))
    {beta varpi zeta v etaD A q gamma alpha alphaPrime e nuMid : Real}
    {F D E : Finset iota}
    {Z : iota -> ShadedTube tau (EuclideanSpace Real (Fin 3))}
    {U0 U1 : iota -> ShadedTube rho (EuclideanSpace Real (Fin 3))}
    (hdelta : 0 < delta) (hdelta1 : delta <= 1) (hrho : 0 < rho) (hrho1 : rho <= 1)
    (hbeta : 0 <= beta) (hq : 0 < q) (h3q : 3 * q <= etaD)
    (hnu : 0 < nuMid) (hbudget : nuMid + 3 * q <= v)
    (he : 0 < e) (hscale : (rho : Real) <= (delta : Real) ^ (e / 2))
    (hL : Lemma91At.{u} beta varpi zeta v etaD rho)
    (hret : SourceMiddleActualRetention hsit hR T0 A q gamma alpha alphaPrime etaD
      varpi zeta F D E Z U0 U1)
    (hdown : SourceMiddleDownstairsCount hsit hR T0 varpi zeta E Z)
    (huni : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) <=
      (rho : ENNReal) ^ (-etaD)) :
    ShadedBody.multiplicity F (fun i => (Z i).toShadedBody) <=
      (rho : ENNReal) ^ (v - 3 * q) * (F.card : ENNReal) ^ beta /\
    ShadedBody.multiplicity F (fun i => (Z i).toShadedBody) <=
      (rho : ENNReal) ^ nuMid * (F.card : ENNReal) ^ beta /\
    ShadedBody.multiplicity F (fun i => (Z i).toShadedBody) <=
      (delta : ENNReal) ^ (e * nuMid / 2) * (F.card : ENNReal) ^ beta := by
  have hr0 : (rho : ENNReal) ≠ 0 := by exact_mod_cast hrho.ne'
  have hrt : (rho : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hr1 : (rho : ENNReal) <= 1 := by exact_mod_cast hrho1
  have hraw := sourceMiddle_raw_of_downstairs hsit hR T0 hrho hrho1 hq h3q hL hret hdown huni
  have hfirst : ShadedBody.multiplicity F (fun i => (Z i).toShadedBody) <=
      (rho : ENNReal) ^ (v - 3 * q) * (F.card : ENNReal) ^ beta := by
    calc
      _ <= (rho : ENNReal) ^ (-(3 * q)) *
          ((rho : ENNReal) ^ v * (E.card : ENNReal) ^ beta) :=
        hret.multiplicity_retained.trans (mul_le_mul' le_rfl hraw)
      _ <= (rho : ENNReal) ^ (-(3 * q)) *
          ((rho : ENNReal) ^ v * (F.card : ENNReal) ^ beta) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl
          (ENNReal.rpow_le_rpow (by exact_mod_cast hret.cardinality_upper) hbeta))
      _ = _ := by
        rw [← mul_assoc, ← ENNReal.rpow_add _ _ hr0 hrt]
        congr 2
        ring
  have hsecond := hfirst.trans (mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hr1
    (by linarith : nuMid <= v - 3 * q)) le_rfl)
  refine ⟨hfirst, hsecond, hsecond.trans (mul_le_mul' ?_ le_rfl)⟩
  have hreal : (rho : Real) ^ nuMid <= (delta : Real) ^ (e * nuMid / 2) := by
    calc (rho : Real) ^ nuMid <= ((delta : Real) ^ (e / 2)) ^ nuMid :=
        Real.rpow_le_rpow rho.coe_nonneg hscale hnu.le
      _ = _ := by rw [← Real.rpow_mul delta.coe_nonneg]; congr 1; ring
  have hn := ENNReal.ofReal_le_ofReal hreal
  simpa only [← ENNReal.ofReal_rpow_of_nonneg rho.coe_nonneg hnu.le,
    ← ENNReal.ofReal_rpow_of_nonneg delta.coe_nonneg (by positivity : 0 <= e * nuMid / 2),
    ENNReal.ofReal_coe_nnreal] using hn

/-- The complete C4-to-C5 pointwise producer. The threshold precedes Q,F,jp,
rho and the raw VNS call; R4 is run once and all outputs share its E/U1. -/
theorem sourceQ_exists_selected_middle_estimate
    (M A0 A1 C K0 : Nat) (e varpi zeta etaC R beta v etaD q gamma nuMid : Real)
    (hparameters : SourceQCoverParameters M A0 A1 C e varpi zeta etaC R)
    (hK0 : 0 < K0) (hbeta : 0 <= beta) (hq : 0 < q) (hgamma : 0 < gamma)
    (hgammaq : gamma <= q) (hcard : 2 * gamma < varpi * zeta / 16)
    (hmass : 3 * gamma < 3 * q) (h3q : 3 * q <= etaD)
    (hnu : 0 < nuMid) (hbudget : nuMid + 3 * q <= v) :
    ∀ᶠ delta : NNReal in 𝓝[>] 0,
      forall {iota : Type u} (S : Finset iota)
        (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
        (Q : SourceThreadedTower S T M C)
        (Y : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
      SourceTowerGeometry Q A0 A1 -> SourceTowerStatistics Q Y ->
      forall (a p b : Nat) (jp : iota) (F : Finset iota)
        (Z : iota -> ShadedTube (sourceTowerRadius delta M b) (EuclideanSpace Real (Fin 3)))
        (rho : NNReal), SourceQCoverInput Q a p b jp F Z rho e zeta etaC ->
      forall (hsit : Tube.IsRescalingSituation (sourceTowerRadius delta M p)
          (sourceTowerRadius delta M b) rho R 3) (hR : 0 < R),
      (F.card : Real) <= (rho : Real) ^ (-(K0 : Real)) ->
      (rho : ENNReal) ^ gamma <= ShadedBody.fullness F
        (fun i => (outerFamily hsit.pos_ambient (Q.tube p jp) hR rho Z i).toShadedBody) ->
      Kakeya.maxDensity F (fun i =>
        (outerFamily hsit.pos_ambient (Q.tube p jp) hR rho Z i).toConvexSpaceBody) <=
          (rho : ENNReal) ^ (-q) ->
      Kakeya.maxDensity F (fun i => (Z i).toConvexSpaceBody) <=
        (rho : ENNReal) ^ (-(etaD - q)) ->
      Lemma91At.{u} beta varpi zeta v etaD rho ->
      exists (D E : Finset iota) (U0 U1 : iota -> ShadedTube rho (EuclideanSpace Real (Fin 3))),
        SourceMiddleActualRetention hsit hR (Q.tube p jp)
          (varpi * zeta / 16) q gamma gamma gamma etaD varpi zeta F D E Z U0 U1 /\
        SourceMiddleDownstairsCount hsit hR (Q.tube p jp) varpi zeta E Z /\
        ShadedBody.multiplicity F (fun i => (Z i).toShadedBody) <=
          (delta : ENNReal) ^ (e * nuMid / 2) * (F.card : ENNReal) ^ beta := by
  classical
  have hA : 0 < varpi * zeta / 16 := by
    exact div_pos (mul_pos hparameters.vns_window_pos hparameters.excess_pos) (by norm_num)
  obtain ⟨rho0, hrho0, hrho20, hret⟩ := sourceQ_exists_actual_middle_retention
    (varpi * zeta / 16) q gamma gamma gamma etaD hA hq hgamma hgamma hgamma
    hgammaq (by linarith) (by linarith) h3q K0 hK0
  obtain ⟨ru, hru, hu⟩ := exists_threshold_const_le_rpow_neg
    (C := ShadedTube.ssfUniformConst 3) (ShadedTube.one_le_ssfUniformConst 3)
    (by linarith : 0 < etaD)
  let rv : NNReal := (1 / 2 : NNReal) ^ (1 / varpi)
  have hrv : 0 < rv := by unfold rv; positivity
  let r0 := min rho0 (min ru rv)
  have hr0 : 0 < r0 := lt_min hrho0 (lt_min hru hrv)
  have hd0 : 0 < r0 ^ (2 / e) := NNReal.rpow_pos hr0
  filter_upwards [sourceQ_exists_downstairs_count M A0 A1 C e varpi zeta etaC R hparameters,
    Ioo_mem_nhdsGT hd0, Ioo_mem_nhdsGT (by norm_num : (0 : NNReal) < 1)]
      with delta hdown hdelta hdelta1
  intro iota S T Q Y hgeometry hstats a p b jp F Z rho hinput hsit hR hcard
    hfull hdensity horiginal hL
  have hscale : (rho : Real) <= (delta : Real) ^ (e / 2) :=
    hinput.rho_upper.trans (div_le_self (Real.rpow_nonneg delta.coe_nonneg _) (by norm_num))
  have hsmall : rho <= r0 := by
    have hp : delta ^ (e / 2) <= r0 := by
      calc delta ^ (e / 2) <= (r0 ^ (2 / e)) ^ (e / 2) :=
          NNReal.rpow_le_rpow hdelta.2.le (by linarith [hparameters.window_pos])
        _ = r0 := by
          rw [← NNReal.rpow_mul, show (2 / e) * (e / 2) = 1 by
            field_simp [hparameters.window_pos.ne'], NNReal.rpow_one]
    have hscaleN : rho <= delta ^ (e / 2) := by exact_mod_cast hscale
    exact hscaleN.trans hp
  have hrhosmall : rho <= rho0 := hsmall.trans (min_le_left _ _)
  have hru' : rho <= ru := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrv' : rho <= rv := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hwindow : rho ^ varpi <= (1 / 2 : NNReal) := by
    calc rho ^ varpi <= rv ^ varpi := NNReal.rpow_le_rpow hrv' hparameters.vns_window_pos.le
      _ = 1 / 2 := by
        dsimp only [rv]
        rw [← NNReal.rpow_mul, one_div_mul_cancel hparameters.vns_window_pos.ne', NNReal.rpow_one]
  have hrho1 : rho <= 1 := by
    have hh : (rho : Real) <= 1 := hsit.out_le_quarter.trans (by norm_num)
    exact_mod_cast hh
  have hratio : (sourceTowerRadius delta M b : Real) /
      (sourceTowerRadius delta M p : Real) <= 4 * (rho : Real) := by
    have heq : (rho : Real) = (sourceTowerRadius delta M b : Real) /
        (2 * (sourceTowerRadius delta M p : Real)) := by exact_mod_cast hinput.rho_eq
    rw [heq]
    have hpos : (0 : Real) < sourceTowerRadius delta M p := by exact_mod_cast hsit.pos_ambient
    field_simp
    nlinarith [NNReal.coe_nonneg (sourceTowerRadius delta M b)]
  have hsub : forall i, i ∈ F -> (Z i).carrier <= (Q.tube p jp).carrier := by
    have ha := sourceQ_ancestor_fibre_identities Q hinput.parent_lt_middle.le hinput.middle_bound
    intro i hi
    have hmem := hinput.family_subset hi
    rw [ha.2.2.2 jp hinput.parent_member] at hmem
    obtain ⟨hib, hip⟩ := Finset.mem_filter.mp hmem
    have hh := ha.2.2.1 i hib
    rw [hip] at hh
    change (Z i).toConvexSpaceBody <= (Q.tube p jp).toConvexSpaceBody
    rw [show (Z i).toConvexSpaceBody = (Q.tube b i).toConvexSpaceBody from
      congrArg Tube.toConvexSpaceBody (hinput.family_tubes i)]
    exact hh
  obtain ⟨D, E, U0, U1, hretained⟩ := hret hsit hR (Q.tube p jp) F Z
    (by linarith [hparameters.radius_lower]) hratio hsit.pos_out hrhosmall hinput.family_nonempty
    hsub hcard hfull hdensity horiginal varpi zeta hparameters.vns_window_pos.le
    (by linarith [hparameters.excess_pos]) hwindow
  have hcounts := (hdown S T Q Y hgeometry hstats a p b jp F E Z rho hinput
    hretained.subset hretained.cardinality_retained hsit hR).2
  have huni : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) <=
      (rho : ENNReal) ^ (-etaD) := by
    have hh := ENNReal.coe_le_coe.mpr (hu rho hsit.pos_out hru')
    simpa only [ENNReal.coe_rpow_of_ne_zero hsit.pos_out.ne'] using hh
  exact ⟨D, E, U0, U1, hretained, hcounts,
    (sourceMiddle_selected_handback_gain hsit hR (Q.tube p jp) hdelta.1 hdelta1.2.le
      hsit.pos_out hrho1 hbeta hq h3q hnu hbudget hparameters.window_pos hscale
      hL hretained hcounts huni).2.2⟩

variable {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- The actual three zero-defect analytic rows on a previously chosen seam. -/
structure SourceQThreeFactorBounds (Q : SourceThreadedTower S T M C)
    {Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
    {a p b : Nat} {lambda : NNReal} {loss : ENNReal}
    (X : SourceQMiddleSeam Q Z a p b lambda loss)
    (beta fineCharge parentCharge outerCharge : Real) : Prop where
  fine : ShadedBody.multiplicity (Q.cell b X.jb) (fun i => (X.fineShade i).toShadedBody) <=
    (delta : ENNReal) ^ (-fineCharge) * ((Q.cell b X.jb).card : ENNReal) ^ beta
  parent : ShadedBody.multiplicity X.parents (fun i => (X.parentShade i).toShadedBody) <=
    (delta : ENNReal) ^ (-parentCharge) * (X.parents.card : ENNReal) ^ beta
  outer : ShadedBody.multiplicity X.coarse (fun i => (X.outerShade i).toShadedBody) <=
    (delta : ENNReal) ^ (-outerCharge) * (X.coarse.card : ENNReal) ^ beta

/-- Q-native fixed-M reading of A1-A8. The source B(0,3) level bound and
the actual top cell are retained; there is no identification with SSF nodesUnder. -/
theorem sourceQ_exists_three_factor_bounds {beta epsFine epsParent epsOuter : Real}
    (hbeta : 0 < beta) (hbeta1 : beta <= 1)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace Real (Fin 3)) beta)
    (hf : 0 < epsFine) (hp : 0 < epsParent) (hc : 0 < epsOuter)
    (M A0 A1 C : Nat) (hM : 2 <= M) :
    exists etaL : Real, 0 < etaL /\
    ∀ᶠ delta : NNReal in 𝓝[>] 0,
      forall {iota : Type u} (S : Finset iota)
        (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
        (Q : SourceThreadedTower S T M C)
        (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
      SourceTowerGeometry Q A0 A1 ->
      Kakeya.maxDensity S (fun i => (T i).toConvexSpaceBody) <= (delta : ENNReal) ^ (-etaL) ->
      forall (a p b : Nat), a <= p -> p < b -> b <= M ->
      forall (lambda : NNReal) (loss : ENNReal)
        (X : SourceQMiddleSeam Q Z a p b lambda loss)
        (kappaParent kappaOuter : Real), delta ^ etaL <= lambda ->
      0 <= kappaParent -> 0 <= kappaOuter ->
      Kakeya.maxDensity (Q.fibre a p X.ja) (fun i => (Q.tube p i).toConvexSpaceBody) <=
        (delta : ENNReal) ^ (-kappaParent) ->
      Kakeya.maxDensity X.coarse (fun i => (Q.tube a i).toConvexSpaceBody) <=
        (delta : ENNReal) ^ (-kappaOuter) ->
      SourceQThreeFactorBounds Q X beta epsFine (epsParent + kappaParent)
        (epsOuter + kappaOuter) := by
  classical
  obtain ⟨Hf, hHf, hfine⟩ := source_exists_fine_factor
    (EuclideanSpace Real (Fin 3)) hbeta.le hKT hf
  obtain ⟨Hp, hHp, tp, htp, htp1, hparent⟩ := source_exists_outer_factor
    (EuclideanSpace Real (Fin 3)) hbeta.le hbeta1 hKT hp
  obtain ⟨Hc, hHc, tc, htc, htc1, hcoarse⟩ := source_exists_outer_factor
    (EuclideanSpace Real (Fin 3)) hbeta.le hbeta1 hKT hc
  obtain ⟨dp, hdp, hdp1, hpayp⟩ := ML2Shaded.exists_threshold_const_le_rpow_neg'
    ((32 / (tp : Real)) ^ (6 : Nat)) hp
  obtain ⟨dc, hdc, hdc1, hpayc⟩ := ML2Shaded.exists_threshold_const_le_rpow_neg'
    ((32 / (tc : Real)) ^ (6 : Nat)) hc
  let etaL := min Hf (min Hp Hc)
  have hetaL : 0 < etaL := lt_min hHf (lt_min hHp hHc)
  refine ⟨etaL, hetaL, ?_⟩
  filter_upwards [hfine, source_eventually_fixed_tower_radius_conditions M hM hetaL,
    Ioo_mem_nhdsGT hdp, Ioo_mem_nhdsGT hdc] with delta hfine hradii hdeltaP hdeltaC
  intro iota S T Q Z hgeometry hmax a p b hap hpb hb lambda loss X kappaParent kappaOuter
    hfull hkappaP hkappaC hdensityP hdensityC
  have hd0 : 0 < delta := hradii.2.2.1
  have hd1 : delta <= 1 := hdeltaP.2.le.trans hdp1
  have hdE1 : (delta : ENNReal) <= 1 := by exact_mod_cast hd1
  have hpM : p < M := lt_of_lt_of_le hpb hb
  have haM : a < M := lt_of_le_of_lt hap hpM
  have hrpos (k : Nat) (hk : k < M) : 0 < sourceTowerRadius delta M k :=
    (by positivity : (0 : NNReal) < 4 * delta).trans_le (hradii.2.2.2.2.1 k hk)
  have hsmall (k : Nat) (hk : k < M) : sourceTowerRadius delta M k <= 1 / 40 := by
    rw [sourceTowerRadius, if_pos hk]
    have hh : delta ^ ((k : Real) / (M : Real)) <= 1 :=
      NNReal.rpow_le_one hd1 (by positivity)
    simpa using mul_le_mul_left' hh (1 / 40 : NNReal)
  have hball (k : Nat) (hk : k < M) (j : iota) (hj : j ∈ Q.indexSet k) :
      (Q.tube k j).carrier <= Metric.closedBall 0 1 := by
    obtain ⟨i, hi, rfl⟩ := Q.place_surjective k hk.le j hj
    have hh := Tube.le_rescale_of_subset (T i) (Q.tube k (Q.place k i))
      (Q.leaf_containment k hk.le i hi)
    intro x hx
    have hx' := hh hx
    change x ∈ ((T i).rescale (4 * sourceTowerRadius delta M k)).carrier at hx'
    rw [Tube.carrier_eq] at hx'
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hx'
    have hzT : z ∈ (T i).carrier := by
      rw [(T i).carrier_eq]
      exact Set.mem_iUnion₂.mpr ⟨z, hz, Metric.mem_closedBall_self delta.coe_nonneg⟩
    have hzB := Metric.mem_closedBall.mp (hgeometry.original_ball i hi hzT)
    have hxz' := Metric.mem_closedBall.mp hxz
    have hs : (sourceTowerRadius delta M k : Real) <= 1 / 40 := by exact_mod_cast hsmall k hk
    have hdist := dist_triangle x z 0
    apply Metric.mem_closedBall.mpr
    push_cast at hxz'
    linarith
  have hparentSub : X.parents <= Q.indexSet p := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (X.parents_subset hj)
    exact Q.place_mem p hpM.le i (Finset.mem_filter.mp hi).1
  have hbound (k : Nat) (hk : k < M) (F : Finset iota) (hF : F <= Q.indexSet k)
      (hne : F.Nonempty) (Y : iota -> ShadedTube (sourceTowerRadius delta M k)
        (EuclideanSpace Real (Fin 3)))
      (hY : forall i, (Y i).toTube = Q.tube k i)
      (eps H density : Real) (theta : NNReal) (htheta : 0 < theta)
      (hH : etaL <= H) (hdensity : 0 <= density)
      (hestimate : SourceOuterFactorAtBody (EuclideanSpace Real (Fin 3)) beta
        (eps + density) H theta density)
      (hpay : (32 / (theta : Real)) ^ (6 : Nat) <= (delta : Real) ^ (-eps))
      (hfullY : lambda <= ShadedBody.fullness F (fun i => (Y i).toShadedBody))
      (hmaxY : Kakeya.maxDensity F (fun i => (Y i).toConvexSpaceBody) <=
        (delta : ENNReal) ^ (-density)) :
      ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
        (delta : ENNReal) ^ (-(eps + density)) * (F.card : ENNReal) ^ beta := by
    by_cases hscale : sourceTowerRadius delta M k <= theta
    · apply hestimate (hrpos k hk) hscale delta hd0
        (le_trans (by nlinarith : delta <= 4 * delta) (hradii.2.2.2.2.1 k hk)) F Y
      · intro i hi
        change (Y i).toTube.carrier <= _
        rw [hY i]
        exact hball k hk i (hF hi)
      · exact (NNReal.rpow_le_rpow_of_exponent_ge hd0 hd1 hH).trans (hfull.trans hfullY)
      · exact hmaxY
    · have hthetaR : (0 : Real) < theta := by exact_mod_cast htheta
      have hrR : (0 : Real) < sourceTowerRadius delta M k := by exact_mod_cast hrpos k hk
      have hcard : (F.card : Real) <= (delta : Real) ^ (-eps) := by
        calc (F.card : Real) <= ((Q.indexSet k).card : Real) := by exact_mod_cast Finset.card_le_card hF
          _ <= (32 / (sourceTowerRadius delta M k : Real)) ^ (6 : Nat) := hgeometry.coarse_card k hk
          _ <= (32 / (theta : Real)) ^ (6 : Nat) := by
            gcongr
            exact_mod_cast (le_of_not_ge hscale)
          _ <= (delta : Real) ^ (-eps) := hpay
      have hcardE : (F.card : ENNReal) <= (delta : ENNReal) ^ (-eps) := by
        have hh := ENNReal.ofReal_le_ofReal hcard
        simpa only [← ENNReal.ofReal_rpow_of_pos (x := (delta : Real)) (p := -eps)
            (by exact_mod_cast hd0),
          ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_natCast] using hh
      have hcard1 : (1 : ENNReal) <= (F.card : ENNReal) := by exact_mod_cast hne.card_pos
      have hcardpow : (1 : ENNReal) <= (F.card : ENNReal) ^ beta := by
        simpa using ENNReal.rpow_le_rpow hcard1 hbeta.le
      calc ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <= (F.card : ENNReal) :=
          ShadedBody.multiplicity_le_card _ _
        _ <= (delta : ENNReal) ^ (-eps) := hcardE
        _ <= (delta : ENNReal) ^ (-(eps + density)) :=
          ENNReal.rpow_le_rpow_of_exponent_ge hdE1 (by linarith)
        _ <= (delta : ENNReal) ^ (-(eps + density)) * (F.card : ENNReal) ^ beta :=
          le_mul_of_one_le_right bot_le hcardpow
  refine ⟨?_, ?_, ?_⟩
  · apply hfine (Q.cell b X.jb) X.fineShade
    · intro i hi
      change (X.fineShade i).toTube.carrier <= _
      rw [X.fine_tubes i]
      exact (hgeometry.original_ball i (Finset.mem_filter.mp hi).1).trans
        (Metric.closedBall_subset_closedBall (by norm_num))
    · have hbody : (fun i => (X.fineShade i).toConvexSpaceBody) =
          (fun i => (T i).toConvexSpaceBody) := by
        funext i
        exact congrArg Tube.toConvexSpaceBody (X.fine_tubes i)
      rw [hbody]
      exact ((Kakeya.maxDensity_mono _ (Finset.filter_subset _ _)).trans hmax).trans
        (ENNReal.rpow_le_rpow_of_exponent_ge hdE1 (neg_le_neg (min_le_left _ _)))
    · exact (NNReal.rpow_le_rpow_of_exponent_ge hd0 hd1 (min_le_left _ _)).trans
        (hfull.trans X.fine_fullness)
  · apply hbound p hpM X.parents hparentSub ⟨X.jp, X.parent_member⟩ X.parentShade X.parent_tubes
      epsParent Hp kappaParent tp htp ((min_le_right _ _).trans (min_le_left _ _)) hkappaP
      (hparent kappaParent hkappaP) (hpayp hd0 hdeltaP.2.le) X.parent_fullness
    have hbody : (fun i => (X.parentShade i).toConvexSpaceBody) =
        (fun i => (Q.tube p i).toConvexSpaceBody) := by
      funext i
      exact congrArg Tube.toConvexSpaceBody (X.parent_tubes i)
    rw [hbody]
    exact (Kakeya.maxDensity_mono _ X.parents_subset).trans hdensityP
  · apply hbound a haM X.coarse X.coarse_subset ⟨X.ja, X.coarse_member⟩ X.outerShade X.outer_tubes
      epsOuter Hc kappaOuter tc htc ((min_le_right _ _).trans (min_le_right _ _)) hkappaC
      (hcoarse kappaOuter hkappaC) (hpayc hd0 hdeltaC.2.le) X.outer_fullness
    have hbody : (fun i => (X.outerShade i).toConvexSpaceBody) =
        (fun i => (Q.tube a i).toConvexSpaceBody) := by
      funext i
      exact congrArg Tube.toConvexSpaceBody (X.outer_tubes i)
    rwa [hbody]

/-- C5 on this exact X.jp, X.middleShade and R4's same E/U1. Fine, parent
and outer rows are instantiated at X; the middle estimate is constructed here. -/
theorem sourceQ_selected_fourFactor_caller
    (Q : SourceThreadedTower S T M C)
    {Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
    {a p b : Nat} {lambda : NNReal} {loss : ENNReal}
    (X : SourceQMiddleSeam Q Z a p b lambda loss)
    {rho : NNReal} {R beta varpi zeta v etaD A q gamma alpha alphaPrime e nuMid : Real}
    {fineCharge parentCharge outerCharge : Real}
    (hsit : Tube.IsRescalingSituation (sourceTowerRadius delta M p)
      (sourceTowerRadius delta M b) rho R 3) (hR : 0 < R)
    {D E : Finset iota}
    {U0 U1 : iota -> ShadedTube rho (EuclideanSpace Real (Fin 3))}
    (hdelta : 0 < delta) (hdelta1 : delta <= 1) (hrho : 0 < rho) (hrho1 : rho <= 1)
    (hbeta : 0 <= beta) (hq : 0 < q) (h3q : 3 * q <= etaD)
    (hnu : 0 < nuMid) (hbudget : nuMid + 3 * q <= v)
    (he : 0 < e) (hscale : (rho : Real) <= (delta : Real) ^ (e / 2))
    (hL : Lemma91At.{u} beta varpi zeta v etaD rho)
    (hret : SourceMiddleActualRetention hsit hR (Q.tube p X.jp)
      A q gamma alpha alphaPrime etaD varpi zeta X.middle D E X.middleShade U0 U1)
    (hdown : SourceMiddleDownstairsCount hsit hR (Q.tube p X.jp) varpi zeta E X.middleShade)
    (huni : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) <=
      (rho : ENNReal) ^ (-etaD))
    (hthree : SourceQThreeFactorBounds Q X beta fineCharge parentCharge outerCharge) :
    ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
      loss * (16 : ENNReal) ^ beta *
        (delta : ENNReal) ^ (e * nuMid / 2 - fineCharge - parentCharge - outerCharge) *
        (S.card : ENNReal) ^ beta := by
  have hm := (sourceMiddle_selected_handback_gain hsit hR (Q.tube p X.jp)
    hdelta hdelta1 hrho hrho1 hbeta hq h3q hnu hbudget he hscale hL hret hdown huni).2.2
  have hd0 : (delta : ENNReal) ≠ 0 := by exact_mod_cast hdelta.ne'
  have hdt : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  calc
    ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
        loss * ShadedBody.multiplicity (Q.cell b X.jb) (fun i => (X.fineShade i).toShadedBody) *
          ShadedBody.multiplicity X.middle (fun i => (X.middleShade i).toShadedBody) *
          ShadedBody.multiplicity X.parents (fun i => (X.parentShade i).toShadedBody) *
          ShadedBody.multiplicity X.coarse (fun i => (X.outerShade i).toShadedBody) := X.split
    _ <= loss * ((delta : ENNReal) ^ (-fineCharge) * ((Q.cell b X.jb).card : ENNReal) ^ beta) *
          ((delta : ENNReal) ^ (e * nuMid / 2) * (X.middle.card : ENNReal) ^ beta) *
          ((delta : ENNReal) ^ (-parentCharge) * (X.parents.card : ENNReal) ^ beta) *
          ((delta : ENNReal) ^ (-outerCharge) * (X.coarse.card : ENNReal) ^ beta) :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hthree.fine) hm)
        hthree.parent) hthree.outer
    _ = loss * (delta : ENNReal) ^ (e * nuMid / 2 - fineCharge - parentCharge - outerCharge) *
          (((Q.cell b X.jb).card : ENNReal) * X.middle.card * X.parents.card * X.coarse.card) ^ beta := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hbeta, ENNReal.mul_rpow_of_nonneg _ _ hbeta,
        ENNReal.mul_rpow_of_nonneg _ _ hbeta]
      rw [show e * nuMid / 2 - fineCharge - parentCharge - outerCharge =
        ((-fineCharge + e * nuMid / 2) + -parentCharge) + -outerCharge by ring]
      rw [ENNReal.rpow_add _ _ hd0 hdt, ENNReal.rpow_add _ _ hd0 hdt,
        ENNReal.rpow_add _ _ hd0 hdt]
      ring
    _ <= loss * (delta : ENNReal) ^ (e * nuMid / 2 - fineCharge - parentCharge - outerCharge) *
          (16 * (S.card : ENNReal)) ^ beta :=
      mul_le_mul' le_rfl (ENNReal.rpow_le_rpow X.card_product hbeta)
    _ = loss * (16 : ENNReal) ^ beta *
          (delta : ENNReal) ^ (e * nuMid / 2 - fineCharge - parentCharge - outerCharge) *
          (S.card : ENNReal) ^ beta := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hbeta]
      ring

end Kakeya.ML2Assembly
