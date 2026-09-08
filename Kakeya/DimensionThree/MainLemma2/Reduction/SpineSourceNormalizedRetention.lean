/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCentredHandBackWire
public import Kakeya.DimensionThree.MainLemma2.ShadedDividingScales

/-!
# Actual normalized retention from one original fibre

The source/API plan fixes the cardinality budget and hand-back exponent
before the available fullness and uniformization losses. The four existence
obligations produce their retained data from the original family.
-/

@[expose] public section

open MeasureTheory Metric Kakeya.ML2Reduction Kakeya.VeryNotSticky
open scoped NNReal ENNReal

namespace Kakeya.ML2Assembly

universe u

/-- The explicit dimensional ratio used when passing between mass and card. -/
noncomputable def sourceRetentionVolumeRatio : NNReal :=
  Tube.volume_le.C 3 / Tube.le_volume.c 3

/-- Positive finite denominators and shaded mass for the actual finite family. -/
structure SourcePositiveFiniteFamily {rho : NNReal} {iota : Type u}
    (F : Finset iota) (O : iota -> ShadedTube rho (EuclideanSpace Real (Fin 3))) : Prop where
  carrier_pos : 0 < ∑ i ∈ F, volume (O i).carrier
  carrier_finite : (∑ i ∈ F, volume (O i).carrier) < (⊤ : ENNReal)
  mass_pos : 0 < ∑ i ∈ F, volume (O i).shade
  mass_finite : (∑ i ∈ F, volume (O i).shade) < (⊤ : ENNReal)
  union_pos : 0 < volume (⋃ i ∈ F, (O i).shade)
  union_finite : volume (⋃ i ∈ F, (O i).shade) < (⊤ : ENNReal)

/-- Dense preparation uses the original shades, with quantitative retention. -/
structure SourceDenseOriginalData (rho : NNReal) (gamma alpha : Real)
    {iota : Type u} (F D : Finset iota)
    (O : iota -> ShadedTube rho (EuclideanSpace Real (Fin 3))) : Prop where
  subset : D ⊆ F
  nonempty : D.Nonempty
  mass_half : (∑ i ∈ F, volume (O i).shade) <= 2 * ∑ i ∈ D, volume (O i).shade
  dense : ML2Shaded.HasDenseShading
    (ShadedBody.fullness F (fun i => (O i).toShadedBody) / 2)
    D (fun i => (O i).toShadedBody)
  card : (F.card : Real) <=
    2 * (sourceRetentionVolumeRatio : Real) * (rho : Real) ^ (-gamma) * (D.card : Real)
  original_cancellation : SourcePositiveFiniteFamily F O
  dense_cancellation : SourcePositiveFiniteFamily D O
  hereditary : forall t : Finset iota, t ⊆ D -> t.Nonempty ->
    ML2Shaded.HasDenseShading
        (ShadedBody.fullness F (fun i => (O i).toShadedBody) / 2)
        t (fun i => (O i).toShadedBody) ∧
      ShadedBody.fullness F (fun i => (O i).toShadedBody) / 2 <=
        ShadedBody.fullness t (fun i => (O i).toShadedBody) ∧
      Kakeya.maxDensity t (fun i => (O i).toConvexSpaceBody) <=
        Kakeya.maxDensity F (fun i => (O i).toConvexSpaceBody) ∧
      SourcePositiveFiniteFamily t O
  retained : forall t : Finset iota, t ⊆ D ->
    (D.card : Real) <= (rho : Real) ^ (-alpha) * (t.card : Real) ->
    t.Nonempty ∧
      (F.card : Real) <= 2 * (sourceRetentionVolumeRatio : Real) *
        (rho : Real) ^ (-(gamma + alpha)) * (t.card : Real) ∧
      (∑ i ∈ F, volume (O i).shade) <= 4 * (sourceRetentionVolumeRatio : ENNReal) *
        (rho : ENNReal) ^ (-(gamma + alpha)) * ∑ i ∈ t, volume (O i).shade ∧
      (rho : ENNReal) ^ gamma / 2 <=
        ShadedBody.fullness t (fun i => (O i).toShadedBody) ∧
      SourcePositiveFiniteFamily t O

/-- All seven actual centring rows are kept on the original index set. -/
structure SourceOriginalCentreData {rho : NNReal} {iota : Type u}
    (F : Finset iota) (O U0 : iota -> ShadedTube rho (EuclideanSpace Real (Fin 3))) : Prop where
  centred : forall i, i ∈ F -> (U0 i).toTube.IsCentred
  contained : forall i, i ∈ F -> (U0 i).carrier ⊆ Metric.closedBall 0 1
  covers : forall i, i ∈ F -> normalise 0 '' (O i).carrier ⊆ (U0 i).carrier
  shade_eq : forall i, i ∈ F -> (U0 i).shade = normalise 0 '' (O i).shade
  midpoint : forall i, i ∈ F -> ‖(O i).toTube.midpoint‖ <= 1
  foot : forall i, i ∈ F ->
    ‖Tube.lineFoot (centringDilate (O i).toTube.midpoint) (O i).toTube.direction -
      (U0 i).toTube.midpoint‖ <= (rho : Real) / 4
  direction : forall i, i ∈ F ->
    ‖(O i).toTube.direction - (U0 i).toTube.direction‖ <= (rho : Real) / 4

/-- Uniformize the prepared D and retain one common E, U1 for every paid row. -/
structure SourceUniformizedRetentionData (rho : NNReal) (gamma alpha alphaPrime : Real)
    {iota : Type u} (F D E : Finset iota)
    (O U0 U1 : iota -> ShadedTube rho (EuclideanSpace Real (Fin 3))) : Prop where
  dense : SourceDenseOriginalData rho gamma alpha F D O
  centre : SourceOriginalCentreData F O U0
  subset : E ⊆ D
  nonempty : E.Nonempty
  tube_eq : forall i, (U1 i).toTube = (U0 i).toTube
  shade_subset : forall i, (U1 i).shade ⊆ (U0 i).shade
  card_uniformizer : (D.card : Real) <= (rho : Real) ^ (-alpha) * (E.card : Real)
  fullness_uniformizer :
    ShadedBody.fullness' E (fun i => (U0 i).toShadedBody) <=
      ENNReal.ofReal ((rho : Real) ^ (-alphaPrime)) *
        ShadedBody.fullness' E (fun i => (U1 i).toShadedBody)
  mass_uniformizer : (∑ i ∈ E, volume (U0 i).shade) <=
    (rho : ENNReal) ^ (-alphaPrime) * ∑ i ∈ E, volume (U1 i).shade
  uniform : Nonempty (ShadedTube.ShadedUniformTubeSet E U1 (Tube.ssfGridLen rho)
    (ShadedTube.ssfUniformConst 3))
  fullness_retained : (rho : ENNReal) ^ (gamma + alphaPrime) / 1024 <=
    ShadedBody.fullness E (fun i => (U1 i).toShadedBody)
  card_retained : (F.card : Real) <= 2 * (sourceRetentionVolumeRatio : Real) *
    (rho : Real) ^ (-(gamma + alpha)) * (E.card : Real)
  mass_retained : ENNReal.ofReal (1 / 512) * (∑ i ∈ F, volume (O i).shade) <=
    4 * (sourceRetentionVolumeRatio : ENNReal) *
      (rho : ENNReal) ^ (-(gamma + alpha + alphaPrime)) * ∑ i ∈ E, volume (U1 i).shade
  multiplicity_retained : ShadedBody.multiplicity F (fun i => (O i).toShadedBody) <=
    4 * (sourceRetentionVolumeRatio : ENNReal) *
      (rho : ENNReal) ^ (-(gamma + alpha + alphaPrime)) *
        ShadedBody.multiplicity E (fun i => (U1 i).toShadedBody)
  union_subset : (⋃ i ∈ E, (U1 i).shade) ⊆ ⋃ i ∈ F, (U0 i).shade
  original_centred_cancellation : SourcePositiveFiniteFamily F U0
  retained_original_cancellation : SourcePositiveFiniteFamily E O
  retained_centred_cancellation : SourcePositiveFiniteFamily E U0
  retained_uniform_cancellation : SourcePositiveFiniteFamily E U1
  affine_mass : forall t : Finset iota, t ⊆ F ->
    (∑ i ∈ t, volume (U0 i).shade) =
      ENNReal.ofReal (1 / 512) * ∑ i ∈ t, volume (O i).shade
  affine_fullness : forall t : Finset iota, t ⊆ F ->
    (ShadedBody.fullness t (fun i => (U0 i).toShadedBody) : ENNReal) =
      ENNReal.ofReal (1 / 512) * ShadedBody.fullness t (fun i => (O i).toShadedBody)
  affine_multiplicity : forall t : Finset iota, t ⊆ F ->
    ShadedBody.multiplicity t (fun i => (U0 i).toShadedBody) =
      ShadedBody.multiplicity t (fun i => (O i).toShadedBody)

/-- Paid terminal losses retain the existing hand-back with original F on the left. -/
structure SourcePaidRetentionData {b deltaTube rho : NNReal} {R : Real}
    (hsit : Tube.IsRescalingSituation b deltaTube rho R 3) (hR : 0 < R)
    (T0 : Tube b (EuclideanSpace Real (Fin 3))) (A q gamma alpha alphaPrime : Real)
    {iota : Type u} (F D E : Finset iota)
    (Z : iota -> ShadedTube deltaTube (EuclideanSpace Real (Fin 3)))
    (U0 U1 : iota -> ShadedTube rho (EuclideanSpace Real (Fin 3))) : Prop where
  prepared : SourceUniformizedRetentionData rho gamma alpha alphaPrime F D E
    (outerFamily hsit.pos_ambient T0 hR rho Z) U0 U1
  card_paid : (F.card : Real) <= (rho : Real) ^ (-A) * (E.card : Real)
  mass_paid : ENNReal.ofReal (1 / 512) *
    (∑ i ∈ F, volume (outerFamily hsit.pos_ambient T0 hR rho Z i).shade) <=
      (rho : ENNReal) ^ (-(3 * q)) * ∑ i ∈ E, volume (U1 i).shade
  handBack : CentredHandBack hsit hR T0 0 q F E Z U1

/-- R1: produce dense original shades and their hereditary quantitative ledger. -/
theorem sourceRetention_exists_denseOriginal (gamma alpha : Real)
    (hgamma : 0 < gamma) (halpha : 0 < alpha)
    {rho : NNReal} (hrho : 0 < rho) (hrho1 : rho <= 1)
    {iota : Type u} (F : Finset iota) (hF : F.Nonempty)
    (O : iota -> ShadedTube rho (EuclideanSpace Real (Fin 3)))
    (hfull : (rho : ENNReal) ^ gamma <=
      ShadedBody.fullness F (fun i => (O i).toShadedBody)) :
    exists D : Finset iota, SourceDenseOriginalData rho gamma alpha F D O := by
  classical
  have hrhoR : 0 < (rho : Real) := hrho
  have hrhoE : (rho : ENNReal) ≠ 0 := by exact_mod_cast hrho.ne'
  have hdim : Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3 := by simp
  have hfinite : forall t : Finset iota, t.Nonempty ->
      0 < ShadedBody.fullness t (fun i => (O i).toShadedBody) ->
      SourcePositiveFiniteFamily t O := by
    intro t ht htf
    have hc : 0 < ∑ i ∈ t, volume (O i).carrier := by
      obtain ⟨i, hi⟩ := ht
      exact lt_of_lt_of_le (pos_iff_ne_zero.mpr (ML2Shaded.volume_carrier_ne_zero hrho (O i).toTube))
        (Finset.single_le_sum (f := fun i => volume (O i).carrier) (fun _ _ => bot_le) hi)
    have hct : (∑ i ∈ t, volume (O i).carrier) < (⊤ : ENNReal) :=
      ENNReal.sum_lt_top.mpr (fun i _ => (O i).isCompact.measure_lt_top)
    have hm : 0 < ∑ i ∈ t, volume (O i).shade := by
      rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul t (fun i => (O i).toShadedBody)]
      exact ENNReal.mul_pos (by exact_mod_cast htf.ne') hc.ne'
    have hmt : (∑ i ∈ t, volume (O i).shade) < (⊤ : ENNReal) :=
      lt_of_le_of_lt (Finset.sum_le_sum (fun i _ => measure_mono (O i).shade_subset)) hct
    refine ⟨hc, hct, hm, hmt, ?_, (measure_biUnion_finset_le t _).trans_lt hmt⟩
    obtain ⟨i, hi, hpos⟩ := Finset.sum_pos_iff.mp hm
    exact lt_of_lt_of_le hpos (measure_mono (fun x hx => Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩))
  have hpR : 0 < (rho : Real) ^ gamma := Real.rpow_pos_of_pos hrho _
  have hfR : (rho : Real) ^ gamma <=
      (ShadedBody.fullness F (fun i => (O i).toShadedBody) : Real) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hrho.ne'] at hfull
    exact_mod_cast hfull
  have hf0 : 0 < ShadedBody.fullness F (fun i => (O i).toShadedBody) := by
    exact_mod_cast hpR.trans_le hfR
  have hFc := hfinite F hF hf0
  obtain ⟨D, hDF, hmass, hdense⟩ :=
    ML2Shaded.exists_denseShading_refinement F (fun i => (O i).toShadedBody)
  have hD : D.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simpa [he] using hFc.mass_pos.trans_le hmass
  have hhered : forall t : Finset iota, t ⊆ D -> t.Nonempty ->
      ML2Shaded.HasDenseShading
          (ShadedBody.fullness F (fun i => (O i).toShadedBody) / 2)
          t (fun i => (O i).toShadedBody) ∧
        ShadedBody.fullness F (fun i => (O i).toShadedBody) / 2 <=
          ShadedBody.fullness t (fun i => (O i).toShadedBody) ∧
        Kakeya.maxDensity t (fun i => (O i).toConvexSpaceBody) <=
          Kakeya.maxDensity F (fun i => (O i).toConvexSpaceBody) ∧
        SourcePositiveFiniteFamily t O := by
    intro t ht htne
    have hden := hdense.subset ht
    have htf : ShadedBody.fullness F (fun i => (O i).toShadedBody) / 2 <=
        ShadedBody.fullness t (fun i => (O i).toShadedBody) := by
      have htfE := hden.le_fullness_tube hrho htne
      rw [← ShadedBody.coe_fullness t (fun i => (O i).toShadedBody)] at htfE
      exact ENNReal.coe_le_coe.mp htfE
    exact ⟨hden, htf, Kakeya.maxDensity_mono _ (ht.trans hDF),
      hfinite t htne ((div_pos hf0 (by norm_num)).trans_le htf)⟩
  have hDc := (hhered D (Finset.Subset.refl _) hD).2.2.2
  have hc0 : (0 : Real) < Tube.le_volume.c 3 := Tube.le_volume.c_pos 3
  have hpA : 0 < (rho : Real) ^ (-alpha) := Real.rpow_pos_of_pos hrho _
  have hratio : (sourceRetentionVolumeRatio : Real) =
      (Tube.volume_le.C 3 : Real) / (Tube.le_volume.c 3 : Real) := by
    simp [sourceRetentionVolumeRatio]
  have hcardRaw := ML2Shaded.card_le_of_sum_shade_le hrho hrho1 hmass
  have hcardR := ENNReal.toReal_mono (by finiteness) hcardRaw
  simp only [hdim,
    ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast] at hcardR
  have hcardD : (F.card : Real) <=
      2 * (sourceRetentionVolumeRatio : Real) * (rho : Real) ^ (-gamma) * (D.card : Real) := by
    calc
      (F.card : Real) <=
        (2 * (Tube.volume_le.C 3 : Real) * (D.card : Real)) /
          ((rho : Real) ^ gamma * (Tube.le_volume.c 3 : Real)) := by
        apply (le_div_iff₀ (mul_pos hpR hc0)).2
        have hf := mul_le_mul_of_nonneg_right hfR
          (show 0 <= (Tube.le_volume.c 3 : Real) * (F.card : Real) by positivity)
        nlinarith
      _ = _ := by rw [hratio, Real.rpow_neg hrhoR.le]; field_simp
  refine ⟨D, hDF, hD, hmass, hdense, hcardD, hFc, hDc, hhered, ?_⟩
  intro t ht hct
  have htne : t.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have hpD : (0 : Real) < D.card := by exact_mod_cast hD.card_pos
    simp [he] at hct
    exact hD.ne_empty hct
  obtain ⟨hdt, hft, hmt, htc⟩ := hhered t ht htne
  have hpadd : (rho : Real) ^ (-(gamma + alpha)) =
      (rho : Real) ^ (-gamma) * (rho : Real) ^ (-alpha) := by
    rw [neg_add, Real.rpow_add hrhoR]
  have hcardt : (F.card : Real) <= 2 * (sourceRetentionVolumeRatio : Real) *
      (rho : Real) ^ (-(gamma + alpha)) * (t.card : Real) := by
    rw [hpadd]
    have hc := mul_le_mul_of_nonneg_left hct
      (show 0 <= 2 * (sourceRetentionVolumeRatio : Real) * (rho : Real) ^ (-gamma) by positivity)
    nlinarith [hcardD]
  have hctE : (D.card : ENNReal) <= (rho : ENNReal) ^ (-alpha) * (t.card : ENNReal) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hrho.ne']
    exact_mod_cast hct
  have hsm := ML2Shaded.sum_shade_le_of_card_le hrho1 hdt hctE
  have hsmR := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero hrhoE ENNReal.coe_ne_top) ENNReal.coe_ne_top)
      htc.mass_finite.ne) hsm
  simp only [hdim,
    ENNReal.toReal_mul, ENNReal.coe_toReal, ← ENNReal.toReal_rpow,
    NNReal.coe_div, NNReal.coe_ofNat] at hsmR
  have hmassR := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by norm_num) hDc.mass_finite.ne) hmass
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hmassR
  have hpaid : (∑ i ∈ F, volume (O i).shade).toReal <=
      4 * (sourceRetentionVolumeRatio : Real) * (rho : Real) ^ (-(gamma + alpha)) *
        (∑ i ∈ t, volume (O i).shade).toReal := by
    have hlower := mul_le_mul_of_nonneg_right hfR
      (show 0 <= (Tube.le_volume.c 3 : Real) * (∑ i ∈ D, volume (O i).shade).toReal by positivity)
    have hDpaid : (∑ i ∈ D, volume (O i).shade).toReal <=
        (2 * (rho : Real) ^ (-alpha) * (Tube.volume_le.C 3 : Real) *
          (∑ i ∈ t, volume (O i).shade).toReal) /
          ((rho : Real) ^ gamma * (Tube.le_volume.c 3 : Real)) := by
      apply (le_div_iff₀ (mul_pos hpR hc0)).2
      linear_combination 2 * hsmR + hlower
    have heq : (2 * (rho : Real) ^ (-alpha) * (Tube.volume_le.C 3 : Real) *
          (∑ i ∈ t, volume (O i).shade).toReal) /
          ((rho : Real) ^ gamma * (Tube.le_volume.c 3 : Real)) =
        2 * (sourceRetentionVolumeRatio : Real) * (rho : Real) ^ (-(gamma + alpha)) *
          (∑ i ∈ t, volume (O i).shade).toReal := by
      rw [hratio, hpadd]
      simp only [Real.rpow_neg hrhoR.le]
      field_simp
    rw [heq] at hDpaid
    linarith
  refine ⟨htne, hcardt, ?_, ?_, htc⟩
  · apply (ENNReal.toReal_le_toReal hFc.mass_finite.ne
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top)
        (ENNReal.rpow_ne_top_of_ne_zero hrhoE ENNReal.coe_ne_top)) htc.mass_finite.ne)).mp
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofNat,
      ← ENNReal.toReal_rpow] using hpaid
  · calc (rho : ENNReal) ^ gamma / 2 <=
        (ShadedBody.fullness F (fun i => (O i).toShadedBody) : ENNReal) / 2 := by gcongr
      _ <= ShadedBody.fullness t (fun i => (O i).toShadedBody) := by
        simpa only [ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0),
          ENNReal.coe_ofNat] using (ENNReal.coe_le_coe.mpr hft)

/-- R2: choose a threshold, then actually centre and uniformize the selected D. -/
theorem sourceRetention_exists_uniformized (K0 : Nat) (hK0 : 0 < K0)
    (q gamma alpha alphaPrime : Real) (hq : 0 < q) (hgamma : 0 < gamma)
    (halpha : 0 < alpha) (halphaPrime : 0 < alphaPrime) :
    exists rho0 : NNReal, 0 < rho0 ∧ rho0 <= 1 / 20 ∧
      forall {b deltaTube rho : NNReal} {R : Real}
        (hsit : Tube.IsRescalingSituation b deltaTube rho R 3) (hR : 0 < R),
        (deltaTube : Real) / (b : Real) <= 4 * (rho : Real) ->
        0 < rho -> rho <= rho0 ->
        forall (T0 : Tube b (EuclideanSpace Real (Fin 3))) {iota : Type u}
          (F : Finset iota) (Z : iota -> ShadedTube deltaTube (EuclideanSpace Real (Fin 3))),
          F.Nonempty -> (forall i, i ∈ F -> (Z i).carrier ⊆ T0.carrier) ->
          (F.card : Real) <= (rho : Real) ^ (-(K0 : Real)) ->
          Kakeya.maxDensity F
            (fun i => (outerFamily hsit.pos_ambient T0 hR rho Z i).toConvexSpaceBody) <=
              (rho : ENNReal) ^ (-q) ->
          (rho : ENNReal) ^ gamma <= ShadedBody.fullness F
            (fun i => (outerFamily hsit.pos_ambient T0 hR rho Z i).toShadedBody) ->
          exists (D E : Finset iota)
            (U0 U1 : iota -> ShadedTube rho (EuclideanSpace Real (Fin 3))),
            SourceUniformizedRetentionData rho gamma alpha alphaPrime F D E
              (outerFamily hsit.pos_ambient T0 hR rho Z) U0 U1 := by
  classical
  obtain ⟨r0, hr00, hr01, huni⟩ :=
    ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf
      (E := EuclideanSpace Real (Fin 3)) K0 alpha alphaPrime halpha halphaPrime
  refine ⟨min r0 (1 / 20), lt_min hr00 (by norm_num), min_le_right _ _, ?_⟩
  intro b deltaTube rho R hsit hR hscale hrho hrho0 T0 iota F Z hF hsub hcard hdens hfull
  have hrhor0 : rho <= r0 := hrho0.trans (min_le_left _ _)
  have hrho20 : rho <= 1 / 20 := hrho0.trans (min_le_right _ _)
  have hrho1 : rho <= 1 := hrhor0.trans hr01
  have hrhoR : 0 < (rho : Real) := hrho
  have hrhoE : (rho : ENNReal) ≠ 0 := by exact_mod_cast hrho.ne'
  have hdim : Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3 := by simp
  let O := outerFamily hsit.pos_ambient T0 hR rho Z
  obtain ⟨D, hD⟩ := sourceRetention_exists_denseOriginal gamma alpha hgamma halpha
    hrho hrho1 F hF O hfull
  obtain ⟨U0, hcen, hball, hcover, hshade, hmid, hfoot, hdir⟩ :=
    exists_centredPushforward_of_outerFamily_data hsit hR hscale hrho
      (by exact_mod_cast hrho20) T0 F Z hsub
  have hcardD : (D.card : Real) <= (rho : Real) ^ (-(K0 : Real)) := by
    exact (show (D.card : Real) <= (F.card : Real) by
      exact_mod_cast Finset.card_le_card hD.subset).trans hcard
  obtain ⟨E, hED, U1, htube, hshrink, hcardE, hfullUni, huniform⟩ :=
    huni hrho hrhor0 D U0 (fun i hi => hball i (hD.subset hi)) hcardD
  obtain ⟨hE, hretcard, hretmass, hretfull, hEc⟩ := hD.retained E hED hcardE
  have hEF : E ⊆ F := hED.trans hD.subset
  have haffmass : forall t : Finset iota, t ⊆ F ->
      (∑ i ∈ t, volume (U0 i).shade) =
        ENNReal.ofReal (1 / 512) * ∑ i ∈ t, volume (O i).shade := by
    intro t ht
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => by
      rw [hshade i (ht hi), volume_normalise_image])
  have hafffull : forall t : Finset iota, t ⊆ F ->
      (ShadedBody.fullness t (fun i => (U0 i).toShadedBody) : ENNReal) =
        ENNReal.ofReal (1 / 512) * ShadedBody.fullness t (fun i => (O i).toShadedBody) :=
    fun t ht => fullness_pushforward t O U0 0 (fun i hi => hshade i (ht hi))
  have haffmult : forall t : Finset iota, t ⊆ F ->
      ShadedBody.multiplicity t (fun i => (U0 i).toShadedBody) =
        ShadedBody.multiplicity t (fun i => (O i).toShadedBody) :=
    fun t ht => multiplicity_pushforward t O U0 0 (fun i hi => hshade i (ht hi))
  have hfinite : forall (t : Finset iota)
      (V : iota -> ShadedTube rho (EuclideanSpace Real (Fin 3))), t.Nonempty ->
      0 < ∑ i ∈ t, volume (V i).shade -> SourcePositiveFiniteFamily t V := by
    intro t V ht hm
    have hc : 0 < ∑ i ∈ t, volume (V i).carrier := by
      obtain ⟨i, hi⟩ := ht
      exact lt_of_lt_of_le
        (pos_iff_ne_zero.mpr (ML2Shaded.volume_carrier_ne_zero hrho (V i).toTube))
        (Finset.single_le_sum (f := fun i => volume (V i).carrier) (fun _ _ => bot_le) hi)
    have hct : (∑ i ∈ t, volume (V i).carrier) < (⊤ : ENNReal) :=
      ENNReal.sum_lt_top.mpr (fun i _ => (V i).isCompact.measure_lt_top)
    have hmt : (∑ i ∈ t, volume (V i).shade) < (⊤ : ENNReal) :=
      lt_of_le_of_lt (Finset.sum_le_sum (fun i _ => measure_mono (V i).shade_subset)) hct
    refine ⟨hc, hct, hm, hmt, ?_, (measure_biUnion_finset_le t _).trans_lt hmt⟩
    obtain ⟨i, hi, hpos⟩ := Finset.sum_pos_iff.mp hm
    exact lt_of_lt_of_le hpos (measure_mono (fun x hx => Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩))
  have hF0 : SourcePositiveFiniteFamily F U0 := hfinite F U0 hF (by
    rw [haffmass F (Finset.Subset.refl _)]
    exact ENNReal.mul_pos (by norm_num) hD.original_cancellation.mass_pos.ne')
  have hE0 : SourcePositiveFiniteFamily E U0 := hfinite E U0 hE (by
    rw [haffmass E hEF]
    exact ENNReal.mul_pos (by norm_num) hEc.mass_pos.ne')
  have hrealpow : ENNReal.ofReal ((rho : Real) ^ (-alphaPrime)) =
      (rho : ENNReal) ^ (-alphaPrime) := by
    rw [← ENNReal.ofReal_rpow_of_pos hrhoR]
    simp
  have hmassUni := sum_shade_le_of_fullness'_le E U0 U1 htube hE0.carrier_pos.ne' hfullUni
  rw [hrealpow] at hmassUni
  have hE1 : SourcePositiveFiniteFamily E U1 := hfinite E U1 hE (by
    by_contra hn
    have hz : (∑ i ∈ E, volume (U1 i).shade) = 0 := le_antisymm (not_lt.mp hn) bot_le
    rw [hz, mul_zero] at hmassUni
    exact (not_le_of_gt hE0.mass_pos) hmassUni)
  have hfullUniE : (ShadedBody.fullness E (fun i => (U0 i).toShadedBody) : ENNReal) <=
      (rho : ENNReal) ^ (-alphaPrime) *
        ShadedBody.fullness E (fun i => (U1 i).toShadedBody) := by
    simpa only [ShadedBody.coe_fullness, hrealpow] using hfullUni
  have hpowcancel : (rho : ENNReal) ^ alphaPrime * (rho : ENNReal) ^ (-alphaPrime) = 1 := by
    rw [← ENNReal.rpow_add _ _ hrhoE ENNReal.coe_ne_top, add_neg_cancel, ENNReal.rpow_zero]
  have hfullRet : (rho : ENNReal) ^ (gamma + alphaPrime) / 1024 <=
      ShadedBody.fullness E (fun i => (U1 i).toShadedBody) := by
    have hlower : ENNReal.ofReal (1 / 512) * ((rho : ENNReal) ^ gamma / 2) <=
        (rho : ENNReal) ^ (-alphaPrime) *
          ShadedBody.fullness E (fun i => (U1 i).toShadedBody) := by
      exact (mul_le_mul' le_rfl hretfull).trans ((hafffull E hEF).symm ▸ hfullUniE)
    calc
      (rho : ENNReal) ^ (gamma + alphaPrime) / 1024 =
        (rho : ENNReal) ^ alphaPrime *
          (ENNReal.ofReal (1 / 512) * ((rho : ENNReal) ^ gamma / 2)) := by
        rw [ENNReal.rpow_add _ _ hrhoE ENNReal.coe_ne_top]
        have hj : ENNReal.ofReal (1 / 512) = (512 : ENNReal)⁻¹ := by
          rw [show (1 / 512 : Real) = (512 : Real)⁻¹ by norm_num,
            ENNReal.ofReal_inv_of_pos (by norm_num)]
          norm_num
        have hj2 : (1024 : ENNReal)⁻¹ = (512 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ := by
          rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inr (by norm_num))]
          norm_num
        rw [hj, div_eq_mul_inv, div_eq_mul_inv, hj2]
        ring
      _ <= (rho : ENNReal) ^ alphaPrime *
          ((rho : ENNReal) ^ (-alphaPrime) *
            ShadedBody.fullness E (fun i => (U1 i).toShadedBody)) := mul_le_mul' le_rfl hlower
      _ = _ := by rw [← mul_assoc, hpowcancel, one_mul]
  have hmassRet : ENNReal.ofReal (1 / 512) * (∑ i ∈ F, volume (O i).shade) <=
      4 * (sourceRetentionVolumeRatio : ENNReal) *
        (rho : ENNReal) ^ (-(gamma + alpha + alphaPrime)) * ∑ i ∈ E, volume (U1 i).shade := by
    calc
      ENNReal.ofReal (1 / 512) * (∑ i ∈ F, volume (O i).shade) <=
        ENNReal.ofReal (1 / 512) * (4 * (sourceRetentionVolumeRatio : ENNReal) *
          (rho : ENNReal) ^ (-(gamma + alpha)) * ∑ i ∈ E, volume (O i).shade) :=
        mul_le_mul' le_rfl hretmass
      _ = (4 * (sourceRetentionVolumeRatio : ENNReal) *
          (rho : ENNReal) ^ (-(gamma + alpha))) * ∑ i ∈ E, volume (U0 i).shade := by
        rw [haffmass E hEF]
        ring
      _ <= (4 * (sourceRetentionVolumeRatio : ENNReal) *
          (rho : ENNReal) ^ (-(gamma + alpha))) *
          ((rho : ENNReal) ^ (-alphaPrime) * ∑ i ∈ E, volume (U1 i).shade) :=
        mul_le_mul' le_rfl hmassUni
      _ = _ := by
        rw [neg_add (gamma + alpha), ENNReal.rpow_add _ _ hrhoE ENNReal.coe_ne_top]
        ring
  refine ⟨D, E, U0, U1, hD, ⟨hcen, hball, hcover, hshade, hmid, hfoot, hdir⟩,
    hED, hE, htube, hshrink, hcardE, hfullUni, hmassUni, ?_, hfullRet,
    hretcard, hmassRet, ?_, ?_, hF0, hEc, hE0, hE1, haffmass, hafffull, haffmult⟩
  · simpa only [hdim] using huniform
  · rw [← haffmult F (Finset.Subset.refl _)]
    exact multiplicity_le_of_shade_refinement hEF hshrink
      ((haffmass F (Finset.Subset.refl _)).symm ▸ hmassRet)
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, hEF hi, hshrink i hxi⟩

/-- R3: pay the four fixed constants and construct the original-family hand-back. -/
theorem sourceRetention_exists_paidHandBack (A q : Real) (hA : 0 < A) (hq : 0 < q)
    (gamma alpha alphaPrime : Real) (hgamma : 0 < gamma) (halpha : 0 < alpha)
    (halphaPrime : 0 < alphaPrime) (hgammaq : gamma <= q)
    (hcardgap : gamma + alpha < A) (hmassgap : gamma + alpha + alphaPrime < 3 * q)
    (K0 : Nat) (hK0 : 0 < K0) :
    exists rho0 : NNReal, 0 < rho0 ∧ rho0 <= 1 / 20 ∧
      forall {b deltaTube rho : NNReal} {R : Real}
        (hsit : Tube.IsRescalingSituation b deltaTube rho R 3) (hR : 0 < R),
        (deltaTube : Real) / (b : Real) <= 4 * (rho : Real) ->
        0 < rho -> rho <= rho0 ->
        forall (T0 : Tube b (EuclideanSpace Real (Fin 3))) {iota : Type u}
          (F : Finset iota) (Z : iota -> ShadedTube deltaTube (EuclideanSpace Real (Fin 3))),
          F.Nonempty -> (forall i, i ∈ F -> (Z i).carrier ⊆ T0.carrier) ->
          (F.card : Real) <= (rho : Real) ^ (-(K0 : Real)) ->
          Kakeya.maxDensity F
            (fun i => (outerFamily hsit.pos_ambient T0 hR rho Z i).toConvexSpaceBody) <=
              (rho : ENNReal) ^ (-q) ->
          (rho : ENNReal) ^ gamma <= ShadedBody.fullness F
            (fun i => (outerFamily hsit.pos_ambient T0 hR rho Z i).toShadedBody) ->
          exists (D E : Finset iota)
            (U0 U1 : iota -> ShadedTube rho (EuclideanSpace Real (Fin 3))),
            SourcePaidRetentionData hsit hR T0 A q gamma alpha alphaPrime F D E Z U0 U1 := by
  obtain ⟨r0, hr00, hr020, hprep⟩ := sourceRetention_exists_uniformized K0 hK0
    q gamma alpha alphaPrime hq hgamma halpha halphaPrime
  obtain ⟨r1, hr10, hC1⟩ := exists_threshold_coe_const_le_rpow_neg
    (C := max 1 (2 * sourceRetentionVolumeRatio)) (le_max_left _ _)
    (show 0 < A - gamma - alpha by linarith)
  obtain ⟨r2, hr20, hC2⟩ := exists_threshold_coe_const_le_rpow_neg
    (C := max 1 (4 * sourceRetentionVolumeRatio)) (le_max_left _ _)
    (show 0 < 3 * q - gamma - alpha - alphaPrime by linarith)
  obtain ⟨r3, hr30, hC3⟩ := exists_threshold_coe_const_le_rpow_neg
    (C := 1024) (by norm_num)
    (show 0 < 3 * q - gamma - alphaPrime by linarith)
  obtain ⟨r4, hr40, hC4⟩ := exists_threshold_coe_const_le_rpow_neg
    (C := 512) (by norm_num) hq
  refine ⟨min r0 (min r1 (min r2 (min r3 r4))),
    lt_min hr00 (lt_min hr10 (lt_min hr20 (lt_min hr30 hr40))),
    (min_le_left _ _).trans hr020, ?_⟩
  intro b deltaTube rho R hsit hR hscale hrho hrho0 T0 iota F Z hF hsub hcard hdens hfull
  have hrhor0 := hrho0.trans (min_le_left _ _)
  have hrhor1 := (hrho0.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrhor2 := ((hrho0.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
    (min_le_left _ _)
  have hrhor3 := (((hrho0.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_left _ _)
  have hrhor4 := (((hrho0.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_right _ _)
  have hrho20 : rho <= 1 / 20 := hrhor0.trans hr020
  have hrhoE : (rho : ENNReal) ≠ 0 := by exact_mod_cast hrho.ne'
  have hrhoE1 : (rho : ENNReal) <= 1 := by
    have h20R : (rho : Real) <= 1 / 20 := by exact_mod_cast hrho20
    have h1R : (rho : Real) <= 1 := by linarith
    exact_mod_cast h1R
  obtain ⟨D, E, U0, U1, hp⟩ :=
    hprep hsit hR hscale hrho hrhor0 T0 F Z hF hsub hcard hdens hfull
  have hconst1 : 2 * (sourceRetentionVolumeRatio : ENNReal) <=
      (rho : ENNReal) ^ (-(A - gamma - alpha)) := by
    apply le_trans ?_ (hC1 rho hrho hrhor1)
    exact_mod_cast (le_max_right 1 (2 * sourceRetentionVolumeRatio))
  have hconst2 : 4 * (sourceRetentionVolumeRatio : ENNReal) <=
      (rho : ENNReal) ^ (-(3 * q - gamma - alpha - alphaPrime)) := by
    apply le_trans ?_ (hC2 rho hrho hrhor2)
    exact_mod_cast (le_max_right 1 (4 * sourceRetentionVolumeRatio))
  have hcoef1 : 2 * (sourceRetentionVolumeRatio : ENNReal) *
      (rho : ENNReal) ^ (-(gamma + alpha)) <= (rho : ENNReal) ^ (-A) := by
    calc _ <= (rho : ENNReal) ^ (-(A - gamma - alpha)) *
        (rho : ENNReal) ^ (-(gamma + alpha)) := mul_le_mul' hconst1 le_rfl
      _ = _ := by rw [← ENNReal.rpow_add _ _ hrhoE ENNReal.coe_ne_top]; congr 1; ring
  have hcoef2 : 4 * (sourceRetentionVolumeRatio : ENNReal) *
      (rho : ENNReal) ^ (-(gamma + alpha + alphaPrime)) <=
        (rho : ENNReal) ^ (-(3 * q)) := by
    calc _ <= (rho : ENNReal) ^ (-(3 * q - gamma - alpha - alphaPrime)) *
        (rho : ENNReal) ^ (-(gamma + alpha + alphaPrime)) := mul_le_mul' hconst2 le_rfl
      _ = _ := by rw [← ENNReal.rpow_add _ _ hrhoE ENNReal.coe_ne_top]; congr 1; ring
  have hcoef1R := ENNReal.toReal_mono
    (ENNReal.rpow_ne_top_of_ne_zero hrhoE ENNReal.coe_ne_top) hcoef1
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.coe_toReal,
    ENNReal.toReal_ofNat] at hcoef1R
  have hcardPaid := hp.card_retained.trans
    (mul_le_mul_of_nonneg_right hcoef1R (by positivity : 0 <= (E.card : Real)))
  have hmassPaid := hp.mass_retained.trans (mul_le_mul' hcoef2 le_rfl)
  have hmultPaid := hp.multiplicity_retained.trans (mul_le_mul' hcoef2 le_rfl)
  have hfullPaid : (rho : ENNReal) ^ (3 * q) <=
      ShadedBody.fullness E (fun i => (U1 i).toShadedBody) := by
    apply le_trans ?_ hp.fullness_retained
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))).2
    calc
      (rho : ENNReal) ^ (3 * q) * 1024 <=
        (rho : ENNReal) ^ (3 * q) *
          (rho : ENNReal) ^ (-(3 * q - gamma - alphaPrime)) := by
        exact mul_le_mul' le_rfl (by simpa only [ENNReal.coe_ofNat] using hC3 rho hrho hrhor3)
      _ = _ := by rw [← ENNReal.rpow_add _ _ hrhoE ENNReal.coe_ne_top]; congr 1; ring
  have hEF := hp.subset.trans hp.dense.subset
  have hcar : forall i, (U1 i).carrier = (U0 i).carrier := by
    intro i
    exact congrArg (fun T : Tube rho (EuclideanSpace Real (Fin 3)) => T.carrier) (hp.tube_eq i)
  have hcov : forall i, i ∈ E -> normalise 0 ''
      (outerFamily hsit.pos_ambient T0 hR rho Z i).carrier ⊆ (U1 i).carrier := by
    intro i hi
    rw [hcar i]
    exact hp.centre.covers i (hEF hi)
  refine ⟨D, E, U0, U1, hp, hcardPaid, hmassPaid, ?_⟩
  refine {
    subset := hEF
    small := by exact_mod_cast hrho20
    dens := hdens
    full := (ENNReal.rpow_le_rpow_of_exponent_ge hrhoE1 hgammaq).trans hfull
    centred := fun i hi => by rw [hp.tube_eq i]; exact hp.centre.centred i (hEF hi)
    contained := fun i hi => by rw [hcar i]; exact hp.centre.contained i (hEF hi)
    covers := hcov
    maxDensity_le := ?_
    fullness_ge := hfullPaid
    card_le := by exact_mod_cast Finset.card_le_card hEF
    multiplicity_le := hmultPaid }
  apply (maxDensity_nodes_le E _ U1 hcov).trans
  have hden := (Kakeya.maxDensity_mono _ hEF).trans hdens
  calc
    (512 : ENNReal) * _ <= (rho : ENNReal) ^ (-q) * (rho : ENNReal) ^ (-q) :=
      mul_le_mul' (by simpa only [ENNReal.coe_ofNat] using hC4 rho hrho hrhor4) hden
    _ = _ := by rw [← ENNReal.rpow_add _ _ hrhoE ENNReal.coe_ne_top]; congr 1; ring

/-- R4: the same constructed E, U1 also carry the existing count transport. -/
theorem sourceRetention_exists_normalizedRetention (A q : Real) (hA : 0 < A) (hq : 0 < q)
    (gamma alpha alphaPrime : Real) (hgamma : 0 < gamma) (halpha : 0 < alpha)
    (halphaPrime : 0 < alphaPrime) (hgammaq : gamma <= q)
    (hcardgap : gamma + alpha < A) (hmassgap : gamma + alpha + alphaPrime < 3 * q)
    (K0 : Nat) (hK0 : 0 < K0) :
    exists rho0 : NNReal, 0 < rho0 ∧ rho0 <= 1 / 20 ∧
      forall {b deltaTube rho : NNReal} {R : Real}
        (hsit : Tube.IsRescalingSituation b deltaTube rho R 3) (hR : 0 < R),
        (deltaTube : Real) / (b : Real) <= 4 * (rho : Real) ->
        0 < rho -> rho <= rho0 ->
        forall (T0 : Tube b (EuclideanSpace Real (Fin 3))) {iota : Type u}
          (F : Finset iota) (Z : iota -> ShadedTube deltaTube (EuclideanSpace Real (Fin 3))),
          F.Nonempty -> (forall i, i ∈ F -> (Z i).carrier ⊆ T0.carrier) ->
          (F.card : Real) <= (rho : Real) ^ (-(K0 : Real)) ->
          Kakeya.maxDensity F
            (fun i => (outerFamily hsit.pos_ambient T0 hR rho Z i).toConvexSpaceBody) <=
              (rho : ENNReal) ^ (-q) ->
          (rho : ENNReal) ^ gamma <= ShadedBody.fullness F
            (fun i => (outerFamily hsit.pos_ambient T0 hR rho Z i).toShadedBody) ->
          forall varpi zeta : Real, 0 <= varpi -> 0 <= 2 + zeta -> rho ^ varpi <= 1 / 2 ->
          exists (D E : Finset iota)
            (U0 U1 : iota -> ShadedTube rho (EuclideanSpace Real (Fin 3))),
            SourcePaidRetentionData hsit hR T0 A q gamma alpha alphaPrime F D E Z U0 U1 ∧
              CountTransport hsit hR T0 0 varpi zeta E Z U1 := by
  obtain ⟨rho0, hrho00, hrho020, hpaid⟩ := sourceRetention_exists_paidHandBack A q hA hq
    gamma alpha alphaPrime hgamma halpha halphaPrime hgammaq hcardgap hmassgap K0 hK0
  refine ⟨rho0, hrho00, hrho020, ?_⟩
  intro b deltaTube rho R hsit hR hscale hrho hrho0 T0 iota F Z hF hsub hcard hdens hfull
    varpi zeta hvarpi hzeta hwindow
  obtain ⟨D, E, U0, U1, hret⟩ :=
    hpaid hsit hR hscale hrho hrho0 T0 F Z hF hsub hcard hdens hfull
  refine ⟨D, E, U0, U1, hret, countTransport_of_tubeEq hret.prepared.tube_eq ?_⟩
  have hEF := hret.prepared.subset.trans hret.prepared.dense.subset
  exact countTransport_of_contractedCover hsit hR hscale hrho hvarpi hzeta hwindow
    T0 E Z U0 (fun i hi => hsub i (hEF hi))
    (fun i hi => hret.prepared.centre.midpoint i (hEF hi))
    (fun i hi => hret.prepared.centre.foot i (hEF hi))
    (fun i hi => hret.prepared.centre.direction i (hEF hi))

end Kakeya.ML2Assembly
