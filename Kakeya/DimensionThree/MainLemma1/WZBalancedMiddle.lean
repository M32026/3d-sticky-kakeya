/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module


public import Kakeya.DimensionThree.MainLemma1.Rescaling.Numerics

/-!
# The middle factor in the WZ balanced-block endgame

This module turns the raw Katz--Tao multiplicity estimate into the middle factor needed by the
Wang--Zahl balanced branch.  The two-sided normalized branch-count band is essential because the
remaining power of that count can have either sign.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya.ml1Boot

universe u

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [MeasurableSpace E] [BorelSpace E]

/-- Convert a raw Katz--Tao middle estimate using a two-sided band for
`Q = q^2 * P2` and the WZ scale separation. -/
theorem wzB_middle_factor_of_raw
    {delta q : NNReal} {beta' gamma zeta zD zQ eM : Real}
    (hdelta0 : 0 < delta) (hdelta1 : delta <= 1) (hq0 : 0 < q)
    (hbeta0 : 0 <= beta') (hbeta1 : beta' <= 1)
    (hgamma0 : 0 <= gamma) (hgamma1 : gamma <= 1)
    (hbetaGamma : beta' <= gamma)
    (_hzeta : 0 <= zeta) (_hzD : 0 <= zD) (hzQ : 0 <= zQ)
    {M2 Delta P2 : ENNReal} {CDelta CQ : NNReal}
    (_hCDelta : 1 <= CDelta) (hCQ : 1 <= CQ)
    (hraw : M2 <= (delta : ENNReal) ^ (-eM) * Delta ^ (1 - beta') * P2 ^ beta')
    (hDelta : Delta <= (CDelta : ENNReal) * (delta : ENNReal) ^ (-zD))
    (hQlo : (CQ : ENNReal) ^ (-1 : Real) * (delta : ENNReal) ^ zQ <=
      (q : ENNReal) ^ (2 : Nat) * P2)
    (hQhi : (q : ENNReal) ^ (2 : Nat) * P2 <=
      (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ))
    (hsep : q <= delta ^ (zeta / 5)) :
    M2 <= (CDelta : ENNReal) ^ (1 - beta') * (CQ : ENNReal)
      * (delta : ENNReal) ^
          (-eM - (1 - beta') * zD - zQ + 2 * zeta * (gamma - beta') / 5)
      * (q : ENNReal) ^ (-2 * gamma)
      * ((q : ENNReal) ^ (2 : Nat) * P2) ^ (1 - gamma / 2) := by
  have hdeltaE0 : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta0.ne'
  have hdeltaEtop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hqE0 : (q : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hq0.ne'
  have hqEtop : (q : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCQ0 : (CQ : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (lt_of_lt_of_le zero_lt_one hCQ).ne'
  have hCQtop : (CQ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCDtop : (CDelta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hdeltaZ0 : (delta : ENNReal) ^ zQ ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, hdeltaE0, hdeltaEtop]
  have hdeltaNZtop : (delta : ENNReal) ^ (-zQ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hdeltaE0 hdeltaEtop
  have hdeltaNZDtop : (delta : ENNReal) ^ (-zD) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hdeltaE0 hdeltaEtop
  have hQleft0 : (CQ : ENNReal) ^ (-1 : Real) * (delta : ENNReal) ^ zQ ≠ 0 := by
    apply mul_ne_zero
    · simp [ENNReal.rpow_eq_zero_iff, hCQ0, hCQtop]
    · exact hdeltaZ0
  have hQ0 : (q : ENNReal) ^ (2 : Nat) * P2 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr hQleft0) hQlo)
  have hP20 : P2 ≠ 0 := by
    intro h
    simp [h] at hQ0
  have hQtop : (q : ENNReal) ^ (2 : Nat) * P2 ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hCQtop hdeltaNZtop) hQhi
  have hP2top : P2 ≠ ⊤ := by
    intro h
    simp [h, hqE0] at hQtop
  let Q : ENNReal := (q : ENNReal) ^ (2 : Nat) * P2
  let g : Real := gamma - beta'
  let h : Real := 1 - gamma / 2
  have hg0 : 0 <= g := by dsimp [g]; linarith
  have he0 : -1 <= gamma / 2 + beta' - 1 := by linarith
  have he1 : gamma / 2 + beta' - 1 <= 1 := by linarith
  have hcard : P2 ^ beta' <= (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ)
      * (q : ENNReal) ^ (-2 * beta') * Q ^ h := by
    have hQlo' : (CQ : ENNReal)⁻¹ * (delta : ENNReal) ^ zQ <=
        (q : ENNReal) ^ (2 : Nat) * P2 := by
      simpa [ENNReal.rpow_neg] using hQlo
    have h' := card_rpow_le_bracket (b := q) (δt := delta) hq0 hdelta1
      (β' := beta') (γ := gamma) he0 he1 (P := P2) hP20 hP2top
      (C := CQ) hCQ (h := zQ) hzQ hQlo' hQhi
    simpa [Q, h] using h'
  have hDeltaPow : Delta ^ (1 - beta') <=
      (CDelta : ENNReal) ^ (1 - beta')
        * (delta : ENNReal) ^ (-(1 - beta') * zD) := by
    calc
      Delta ^ (1 - beta') <=
          ((CDelta : ENNReal) * (delta : ENNReal) ^ (-zD)) ^ (1 - beta') :=
        ENNReal.rpow_le_rpow hDelta (by linarith)
      _ = (CDelta : ENNReal) ^ (1 - beta')
          * ((delta : ENNReal) ^ (-zD)) ^ (1 - beta') := by
        rw [ENNReal.mul_rpow_of_ne_top hCDtop hdeltaNZDtop]
      _ = (CDelta : ENNReal) ^ (1 - beta')
          * (delta : ENNReal) ^ (-(1 - beta') * zD) := by
        rw [← ENNReal.rpow_mul]
        congr 2
        ring
  have hsepE : (q : ENNReal) <= (delta : ENNReal) ^ (zeta / 5) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hdelta0.ne']
    exact_mod_cast hsep
  have hgain : (q : ENNReal) ^ (2 * g) <=
      (delta : ENNReal) ^ (2 * zeta * g / 5) := by
    calc
      (q : ENNReal) ^ (2 * g) <= ((delta : ENNReal) ^ (zeta / 5)) ^ (2 * g) :=
        ENNReal.rpow_le_rpow hsepE (by positivity)
      _ = (delta : ENNReal) ^ (2 * zeta * g / 5) := by
        rw [← ENNReal.rpow_mul]
        congr 1
        ring
  have hqfactor : (q : ENNReal) ^ (-2 * beta') =
      (q : ENNReal) ^ (-2 * gamma) * (q : ENNReal) ^ (2 * g) := by
    calc
      (q : ENNReal) ^ (-2 * beta') = (q : ENNReal) ^ (-2 * gamma + 2 * g) := by
        congr 1
        dsimp [g]
        ring
      _ = (q : ENNReal) ^ (-2 * gamma) * (q : ENNReal) ^ (2 * g) :=
        ENNReal.rpow_add (-2 * gamma) (2 * g) hqE0 hqEtop
  have hdeltaCombine :
      (delta : ENNReal) ^ (-eM) * (delta : ENNReal) ^ (-(1 - beta') * zD)
        * (delta : ENNReal) ^ (-zQ) * (delta : ENNReal) ^ (2 * zeta * g / 5) =
      (delta : ENNReal) ^ (-eM - (1 - beta') * zD - zQ + 2 * zeta * g / 5) := by
    rw [← ENNReal.rpow_add (-eM) (-(1 - beta') * zD) hdeltaE0 hdeltaEtop]
    rw [← ENNReal.rpow_add (-eM + -(1 - beta') * zD) (-zQ) hdeltaE0 hdeltaEtop]
    rw [← ENNReal.rpow_add
      (-eM + -(1 - beta') * zD + -zQ) (2 * zeta * g / 5) hdeltaE0 hdeltaEtop]
    congr 1
    ring
  calc
    M2 <= (delta : ENNReal) ^ (-eM) * Delta ^ (1 - beta') * P2 ^ beta' := hraw
    _ <= (delta : ENNReal) ^ (-eM)
        * ((CDelta : ENNReal) ^ (1 - beta')
          * (delta : ENNReal) ^ (-(1 - beta') * zD))
        * ((CQ : ENNReal) * (delta : ENNReal) ^ (-zQ)
          * (q : ENNReal) ^ (-2 * beta') * Q ^ h) := by gcongr
    _ = (CDelta : ENNReal) ^ (1 - beta') * (CQ : ENNReal)
        * ((delta : ENNReal) ^ (-eM)
          * (delta : ENNReal) ^ (-(1 - beta') * zD)
          * (delta : ENNReal) ^ (-zQ))
        * ((q : ENNReal) ^ (-2 * gamma) * (q : ENNReal) ^ (2 * g)) * Q ^ h := by
      rw [hqfactor]
      ac_rfl
    _ <= (CDelta : ENNReal) ^ (1 - beta') * (CQ : ENNReal)
        * ((delta : ENNReal) ^ (-eM)
          * (delta : ENNReal) ^ (-(1 - beta') * zD)
          * (delta : ENNReal) ^ (-zQ))
        * ((q : ENNReal) ^ (-2 * gamma)
          * (delta : ENNReal) ^ (2 * zeta * g / 5)) * Q ^ h := by gcongr
    _ = (CDelta : ENNReal) ^ (1 - beta') * (CQ : ENNReal)
        * (delta : ENNReal) ^
          (-eM - (1 - beta') * zD - zQ + 2 * zeta * (gamma - beta') / 5)
        * (q : ENNReal) ^ (-2 * gamma)
        * ((q : ENNReal) ^ (2 : Nat) * P2) ^ (1 - gamma / 2) := by
      dsimp [Q, h]
      rw [← hdeltaCombine]
      dsimp [g]
      ac_rfl

private theorem eventually_wz_rpow_le
    {c : NNReal} (hc : 0 < c) {e : Real} (he : 0 < e) :
    ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0), delta ^ e <= c := by
  have hc' : 0 < c ^ (1 / e) := NNReal.rpow_pos hc
  filter_upwards [eventually_le_nhdsGT hc'] with delta hdelta
  calc
    delta ^ e <= (c ^ (1 / e)) ^ e := NNReal.rpow_le_rpow hdelta he.le
    _ = c := by
      rw [← NNReal.rpow_mul, one_div_mul_cancel (ne_of_gt he), NNReal.rpow_one]

private theorem wzB_raw_family [Nontrivial E]
    {β' ζ : Real} (hβ'0 : 0 <= β') (hζ : 0 < ζ)
    (hKKT : KatzTaoEstimate.{u} E β') :
    ∀ eM > (0 : Real), ∃ etaM > (0 : Real),
      ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
        ∀ q : NNReal, delta <= q -> q <= delta ^ (ζ / 5) ->
        ∀ {κ : Type u} {t : Finset κ} (Tq : κ -> ShadedTube q E),
          t.Nonempty ->
          (∀ l ∈ t, (Tq l).carrier ⊆ Metric.closedBall 0 1) ->
          delta ^ etaM <= ShadedBody.fullness t (fun l => (Tq l).toShadedBody) ->
          ShadedBody.multiplicity t (fun l => (Tq l).toShadedBody) <=
            (delta : ENNReal) ^ (-eM) *
              maxDensity t (fun l => (Tq l).toConvexSpaceBody) ^ (1 - β') *
              (t.card : ENNReal) ^ β' := by
  classical
  intro eM heM
  obtain ⟨etaM, hetaM, hraw⟩ :=
    KatzTaoEstimate.multiplicity_bound_generalize (E := E) hβ'0 hKKT eM heM
  obtain ⟨q₀, hq₀, hrawIoc⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hraw
  refine ⟨etaM, hetaM, ?_⟩
  filter_upwards [eventually_wz_rpow_le hq₀
      (div_pos hζ (by norm_num : (0 : Real) < 5)),
      Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)]
    with delta hpow ⟨hdelta0, hdelta1⟩
  intro q hdeltaq hqsep κ t Tq ht hball hfull
  have hq0 : 0 < q := lt_of_lt_of_le hdelta0 hdeltaq
  have hqq₀ : q <= q₀ := hqsep.trans hpow
  rcases ht with ⟨l₀, hl₀⟩
  let T_ext : κ -> ShadedTube q E := fun i => if i ∈ t then Tq i else Tq l₀
  have hext_eq : ∀ i ∈ t, T_ext i = Tq i := by
    intro i hi
    simp [T_ext, hi]
  have hball_total : ∀ i, (T_ext i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i
    by_cases hi : i ∈ t
    · rw [hext_eq i hi]
      exact hball i hi
    · rw [show T_ext i = Tq l₀ by simp [T_ext, hi]]
      exact hball l₀ hl₀
  have hfull_eqENN :
      (ShadedBody.fullness t (fun i => (T_ext i).toShadedBody) : ENNReal) =
        (ShadedBody.fullness t (fun i => (Tq i).toShadedBody) : ENNReal) := by
    rw [ShadedBody.coe_fullness, ShadedBody.coe_fullness]
    unfold ShadedBody.fullness'
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      simp [hext_eq i hi]
    · apply Finset.sum_congr rfl
      intro i hi
      simp [hext_eq i hi]
  have hfull_eq :
      ShadedBody.fullness t (fun i => (T_ext i).toShadedBody) =
        ShadedBody.fullness t (fun i => (Tq i).toShadedBody) := by
    exact_mod_cast hfull_eqENN
  have hfull_ext :
      delta ^ etaM <= ShadedBody.fullness t (fun i => (T_ext i).toShadedBody) := by
    rw [hfull_eq]
    exact hfull
  have hraw_res := hrawIoc ⟨hq0, hqq₀⟩ delta hdelta0 hdeltaq t T_ext hball_total hfull_ext
  have hmu_eq :
      ShadedBody.multiplicity t (fun i => (T_ext i).toShadedBody) =
        ShadedBody.multiplicity t (fun i => (Tq i).toShadedBody) := by
    refine Kakeya.multiplicity_eq_of_eqOn (E := E) t ?_
    intro i hi
    rw [hext_eq i hi]
  have hext_convex :
      ∀ i ∈ t, (T_ext i).toConvexSpaceBody = (Tq i).toConvexSpaceBody := by
    intro i hi
    rw [hext_eq i hi]
  have hDelta_eq :
      maxDensity t (fun i => (T_ext i).toConvexSpaceBody) =
        maxDensity t (fun i => (Tq i).toConvexSpaceBody) := by
    apply le_antisymm
    · rw [maxDensity_le_iff]
      intro K
      rw [Kakeya.densityIn_eq_of_eqOn (E := E) t hext_convex K]
      exact le_maxDensity t (fun i => (Tq i).toConvexSpaceBody) K
    · rw [maxDensity_le_iff]
      intro K
      rw [← Kakeya.densityIn_eq_of_eqOn (E := E) t hext_convex K]
      exact le_maxDensity t (fun i => (T_ext i).toConvexSpaceBody) K
  rw [hmu_eq, hDelta_eq] at hraw_res
  exact hraw_res

/-- Public raw Katz--Tao family bound used when hierarchy losses must be cancelled before
rewriting the density and cardinality factors. -/
theorem wzB_raw_family_public [Nontrivial E]
    {beta' zeta : Real} (hbeta0 : 0 <= beta') (hzeta : 0 < zeta)
    (hKKT : KatzTaoEstimate.{u} E beta') :
    ∀ eM > (0 : Real), ∃ etaM > (0 : Real),
      ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
        ∀ q : NNReal, delta <= q -> q <= delta ^ (zeta / 5) ->
        ∀ {kappa : Type u} {t : Finset kappa} (Tq : kappa -> ShadedTube q E),
          t.Nonempty ->
          (∀ l ∈ t, (Tq l).carrier ⊆ Metric.closedBall 0 1) ->
          delta ^ etaM <= ShadedBody.fullness t (fun l => (Tq l).toShadedBody) ->
          ShadedBody.multiplicity t (fun l => (Tq l).toShadedBody) <=
            (delta : ENNReal) ^ (-eM) *
              maxDensity t (fun l => (Tq l).toConvexSpaceBody) ^ (1 - beta') *
              (t.card : ENNReal) ^ beta' := by
  exact wzB_raw_family hbeta0 hzeta hKKT

/-- The analytic middle-factor wrapper for the WZ balanced branch. -/
theorem wzB_middle_factor [Nontrivial E]
    {beta' gamma zeta zD zQ : Real}
    (hbeta0 : 0 <= beta') (hbeta1 : beta' <= 1)
    (hgamma0 : 0 <= gamma) (hgamma1 : gamma <= 1)
    (hbetaGamma : beta' <= gamma)
    (hzeta : 0 < zeta) (hzD : 0 <= zD) (hzQ : 0 <= zQ)
    (hKKT : KatzTaoEstimate.{u} E beta')
    {CDelta CQ : NNReal} (hCDelta : 1 <= CDelta) (hCQ : 1 <= CQ) :
    ∀ eM > (0 : Real), ∃ etaM > (0 : Real),
      ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
        ∀ q : NNReal, delta <= q -> q <= delta ^ (zeta / 5) ->
        ∀ {κ : Type u} {t : Finset κ} (Tq : κ -> ShadedTube q E),
          t.Nonempty ->
          (∀ l ∈ t, (Tq l).carrier ⊆ Metric.closedBall 0 1) ->
          delta ^ etaM <= ShadedBody.fullness t (fun l => (Tq l).toShadedBody) ->
          maxDensity t (fun l => (Tq l).toConvexSpaceBody) <=
            (CDelta : ENNReal) * (delta : ENNReal) ^ (-zD) ->
          (CQ : ENNReal) ^ (-1 : Real) * (delta : ENNReal) ^ zQ <=
            (q : ENNReal) ^ (2 : Nat) * (t.card : ENNReal) ->
          (q : ENNReal) ^ (2 : Nat) * (t.card : ENNReal) <=
            (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ) ->
          ShadedBody.multiplicity t (fun l => (Tq l).toShadedBody) <=
            (CDelta : ENNReal) ^ (1 - beta') * (CQ : ENNReal)
              * (delta : ENNReal) ^
                  (-eM - (1 - beta') * zD - zQ
                    + 2 * zeta * (gamma - beta') / 5)
              * (q : ENNReal) ^ (-2 * gamma)
              * ((q : ENNReal) ^ (2 : Nat) * (t.card : ENNReal)) ^
                  (1 - gamma / 2) := by
  intro eM heM
  obtain ⟨etaM, hetaM, hraw⟩ := wzB_raw_family (E := E) hbeta0 hzeta hKKT eM heM
  refine ⟨etaM, hetaM, ?_⟩
  filter_upwards [hraw, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)]
    with delta hraw_delta ⟨hdelta0, hdelta1⟩
  intro q hdeltaq hsep κ t Tq ht hball hfull hDelta hQlo hQhi
  have hq0 : 0 < q := lt_of_lt_of_le hdelta0 hdeltaq
  have hraw_bound := hraw_delta q hdeltaq hsep Tq ht hball hfull
  exact wzB_middle_factor_of_raw hdelta0 hdelta1.le hq0
    hbeta0 hbeta1 hgamma0 hgamma1 hbetaGamma hzeta.le hzD hzQ
    hCDelta hCQ hraw_bound hDelta hQlo hQhi hsep

end Kakeya.ml1Boot
