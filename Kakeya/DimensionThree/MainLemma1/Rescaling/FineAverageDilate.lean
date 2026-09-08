/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Cases
public import Kakeya.DimensionThree.MainLemma1.Rescaling.MiddleAverage
public import Kakeya.DimensionThree.MainLemma1.Rescaling.FineDilate

/-!
# The fine factor at average fullness inside a dilated parent

This is the construction-facing analogue of `Kakeya.ml1Boot.multiplicity_le_fine_avg` for the
parent geometry produced by the dilated Proposition 5.1 pipeline.  The selected fine fibre is
density-pigeonholed internally; its producer therefore supplies only average fullness, the fixed
carrier geometry and a Frostman bound.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace fineAverageDilate

/-- Constant for the dilated fine estimate at the four-to-one density bracket produced by the
internal average-fullness normalization. -/
noncomputable abbrev C (c CF : NNReal) : NNReal :=
  16 * fineNormalizeDilate.C c ^ 2 * (2 * CF)

end fineAverageDilate

/-- The dilated fine estimate at the symmetric density bracket
`2⁻¹ μ₀ ≤ density ≤ 2 μ₀` produced by internal normalization. -/
theorem multiplicity_le_fine_bracketFour_dilate [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3) (c : NNReal) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hKF : FrostmanEstimate.{v} E γ) :
    ∀ ap' > (0 : ℝ), ∃ ηflat > (0 : ℝ),
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ b : NNReal, δ ≤ b → b ≤ 1 →
      ∀ {ι : Type v} {u : Finset ι} (Tb : Tube b E) (T : ι → ShadedTube δ E)
        (K : ConvexSpaceBody E) (M CF : NNReal) {R : ℝ} {μ₀ : ENNReal},
        1 ≤ M → 1 ≤ CF → 0 < μ₀ → u.Nonempty →
        Tb.carrier ⊆ Metric.closedBall 0 R →
        K ≤ Tube.dilate Tb (c : ℝ) →
        volume (Tube.dilate Tb (c : ℝ)).carrier ≤ (M : ENNReal) * volume K.carrier →
        (∀ i ∈ u, (T i).toConvexSpaceBody ≤ K) →
        (u : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (∀ i ∈ u,
          (2 : ENNReal)⁻¹ * μ₀ * volume (T i).carrier ≤ volume (T i).shade ∧
          volume (T i).shade ≤ 2 * μ₀ * volume (T i).carrier) →
        frostmanConstIn u (fun i => (T i).toConvexSpaceBody) K
          ≤ 2 * (CF : ENNReal) * (δ : ENNReal) ^ (-2 * ap') →
        16 * (fineNormalizeDilate.C c : ENNReal) * (δ : ENNReal) ^ ηflat
          ≤ ShadedBody.fullness u (fun i => (T i).toShadedBody) →
        ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          ≤ (M : ENNReal) * (fineAverageDilate.C c CF : ENNReal)
            * (δ : ENNReal) ^ (-3 * ap')
            * ((δ / b : NNReal) : ENNReal) ^ (-2 * γ)
            * ((u.card : ENNReal) * ((δ / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^
                (1 - γ / 2) := by
  intro ap' hap'
  obtain ⟨ηflat, hηflat, hgen⟩ := fine_genKF_dilate hdim c hγ0 hγ1 hKF ap' hap'
  refine ⟨ηflat, hηflat, ?_⟩
  let C : ENNReal := (fineNormalizeDilate.C c : ENNReal)
  have hC1 : 1 ≤ C := by
    change (1 : ENNReal) ≤ (fineNormalizeDilate.C c : ENNReal)
    exact_mod_cast one_le_fineNormalizeDilate_C c
  have hC0 : C ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hC1)
  have hCtop : C ≠ ⊤ := ENNReal.coe_ne_top
  filter_upwards [hgen 4 (by norm_num : (1 : NNReal) ≤ 4), self_mem_nhdsWithin]
    with δ hgenδ hδ0
  intro b hδb hb1 ι u Tb T K M CF R μ₀ hM hCF hμ₀ hu hTball hKle hKfat hsub hED hdens hF hFull
  have hCF1 : (1 : ENNReal) ≤ (CF : ENNReal) := by exact_mod_cast hCF
  have hCFtop : (CF : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ1 : δ ≤ 1 := hδb.trans hb1
  have hδle : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hδpos : 0 < (δ : ENNReal) := ENNReal.coe_pos.mpr hδ0
  have hδne : (δ : ENNReal) ≠ 0 := hδpos.ne'
  have hδtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hME : (1 : ENNReal) ≤ (M : ENNReal) := by exact_mod_cast hM
  have hM0 : (M : ENNReal) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hME)
  have hMC1 : (1 : ENNReal) ≤ (M : ENNReal) * C := one_le_mul hME hC1
  have hMC0 : (M : ENNReal) * C ≠ 0 := mul_ne_zero hM0 hC0
  have hMCtop : (M : ENNReal) * C ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hCtop
  let Cf : ENNReal :=
    2 * (CF : ENNReal) * (δ : ENNReal) ^ (-2 * ap') * ((M : ENNReal) * C)
  have hpow1 : (1 : ENNReal) ≤ (δ : ENNReal) ^ (-2 * ap') := by
    exact ENNReal.one_le_rpow_of_pos_of_le_one_of_neg hδpos hδle (by nlinarith)
  have hCf1 : 1 ≤ Cf := by
    dsimp [Cf]
    exact one_le_mul (one_le_mul (one_le_mul (by norm_num) hCF1) hpow1) hMC1
  have hCftop : Cf ≠ ⊤ := by
    dsimp [Cf]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hCFtop)
        (ENNReal.rpow_ne_top_of_ne_zero hδne hδtop)) hMCtop
  have hCfdiv : Cf / ((M : ENNReal) * C) =
      2 * (CF : ENNReal) * (δ : ENNReal) ^ (-2 * ap') := by
    dsimp [Cf]
    rw [ENNReal.mul_div_cancel_right hMC0 hMCtop]
  have hF' : frostmanConstIn u (fun i => (T i).toConvexSpaceBody) K
      ≤ Cf / ((M : ENNReal) * C) := by rw [hCfdiv]; exact hF
  have hFull' : C * (4 : ENNReal) ^ 2 * (δ : ENNReal) ^ ηflat
      ≤ ShadedBody.fullness u (fun i => (T i).toShadedBody) := by
    calc
      C * (4 : ENNReal) ^ 2 * (δ : ENNReal) ^ ηflat =
          16 * C * (δ : ENNReal) ^ ηflat := by ring
      _ ≤ ShadedBody.fullness u (fun i => (T i).toShadedBody) := hFull
  have hdens' : ∀ i ∈ u,
      (4 : ENNReal)⁻¹ * μ₀ * volume (T i).carrier ≤ volume (T i).shade ∧
      volume (T i).shade ≤ 4 * μ₀ * volume (T i).carrier := by
    intro i hi
    have hi' := hdens i hi
    constructor
    · calc
        (4 : ENNReal)⁻¹ * μ₀ * volume (T i).carrier
            ≤ (2 : ENNReal)⁻¹ * μ₀ * volume (T i).carrier := by
          gcongr
          norm_num
        _ ≤ volume (T i).shade := hi'.1
    · calc
        volume (T i).shade ≤ 2 * μ₀ * volume (T i).carrier := hi'.2
        _ ≤ 4 * μ₀ * volume (T i).carrier := by
          gcongr
          norm_num
  have hmult := hgenδ Cf hCf1 hCftop b hδb hb1 (ι := ι) (u := u) Tb T K M
    (μ₀ := μ₀) hM
    ⟨hμ₀, hu, hTball, hKle, hKfat, hsub, hED, hdens', hFull'⟩ hF'
  have hCfmono : Cf ^ (1 - γ / 2) ≤ Cf := by
    calc
      Cf ^ (1 - γ / 2) ≤ Cf ^ (1 : ℝ) := by
        exact ENNReal.rpow_le_rpow_of_exponent_le hCf1 (by nlinarith [hγ0])
      _ = Cf := ENNReal.rpow_one _
  have hrpow : (δ : ENNReal) ^ (-3 * ap') =
      (δ : ENNReal) ^ (-ap') * (δ : ENNReal) ^ (-2 * ap') := by
    rw [show -3 * ap' = -ap' + -2 * ap' by ring]
    exact ENNReal.rpow_add _ _ hδne hδtop
  have hconst : (fineAverageDilate.C c CF : ENNReal) =
      16 * C ^ 2 * (2 * (CF : ENNReal)) := by
    change (16 * fineNormalizeDilate.C c ^ 2 * (2 * CF) : ENNReal) = _
    dsimp [C]
  have hpref : C * (4 : ENNReal) ^ 2 * (δ : ENNReal) ^ (-ap') * Cf =
      (M : ENNReal) * (fineAverageDilate.C c CF : ENNReal) *
        (δ : ENNReal) ^ (-3 * ap') := by
    dsimp only [Cf]
    rw [hrpow, hconst]
    ring
  calc
    ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
        ≤ C * (4 : ENNReal) ^ 2 * (δ : ENNReal) ^ (-ap') * Cf ^ (1 - γ / 2)
          * ((δ / b : NNReal) : ENNReal) ^ (-2 * γ)
          * ((u.card : ENNReal) * ((δ / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^
              (1 - γ / 2) := hmult
    _ ≤ C * (4 : ENNReal) ^ 2 * (δ : ENNReal) ^ (-ap') * Cf
          * ((δ / b : NNReal) : ENNReal) ^ (-2 * γ)
          * ((u.card : ENNReal) * ((δ / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^
              (1 - γ / 2) := by gcongr
    _ = (M : ENNReal) * (fineAverageDilate.C c CF : ENNReal)
          * (δ : ENNReal) ^ (-3 * ap')
          * ((δ / b : NNReal) : ENNReal) ^ (-2 * γ)
          * ((u.card : ENNReal) * ((δ / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^
              (1 - γ / 2) := by rw [hpref]

/-- The fine factor over a fixed parent dilate, with density normalization performed after the
product-only fibre has been selected.

The three final hypotheses display the independent payments for normalized fullness, Frostman
subfamily transfer and the multiplicity loss of the density pigeonhole. -/
theorem multiplicity_le_fine_avg_dilate (hdim : Module.finrank ℝ E = 3)
    (c : NNReal) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hKF : FrostmanEstimate.{v} E γ) :
    ∀ ap' > (0 : ℝ), ∃ ηflat > (0 : ℝ),
    ∀ a A g : ℝ, 0 ≤ a →
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ b : NNReal, δ ≤ b → b ≤ 1 →
      ∀ {ι : Type v} {u : Finset ι} (Tb : Tube b E) (T : ι → ShadedTube δ E)
        (K : ConvexSpaceBody E) (M CF : NNReal) {R : ℝ},
        1 ≤ M →
        1 ≤ CF →
        u.Nonempty →
        Tb.carrier ⊆ Metric.closedBall 0 R →
        K ≤ Tube.dilate Tb (c : ℝ) →
        volume (Tube.dilate Tb (c : ℝ)).carrier ≤ (M : ENNReal) * volume K.carrier →
        (∀ i ∈ u, (T i).toConvexSpaceBody ≤ K) →
        (u : Set ι).Pairwise
          (fun i i' => IsEssentiallyDistinct (T i).carrier (T i').carrier) →
        frostmanConstIn u (fun i => (T i).toConvexSpaceBody) K
          ≤ (δ : ENNReal) ^ (-a) →
        (δ : ENNReal) ^ g
          ≤ ShadedBody.fullness u (fun i => (T i).toShadedBody) →
        16 * (fineNormalizeDilate.C c : ENNReal) * (δ : ENNReal) ^ ηflat
          ≤ (δ : ENNReal) ^ (2 * g) / 16 →
        ((δ : ENNReal) ^ (2 * g) / 16)⁻¹ * (δ : ENNReal) ^ (-a)
          ≤ 2 * (CF : ENNReal) * (δ : ENNReal) ^ (-2 * ap') →
        16 / (δ : ENNReal) ^ g *
            ((M : ENNReal) * (fineAverageDilate.C c CF : ENNReal)
              * (δ : ENNReal) ^ (-3 * ap'))
          ≤ (δ : ENNReal) ^ (-A) →
        ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
          ≤ (δ : ENNReal) ^ (-A)
            * ((δ / b : NNReal) : ENNReal) ^ (-2 * γ)
            * ((u.card : ENNReal) * ((δ / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^
                (1 - γ / 2) := by
  intro ap' hap'
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  obtain ⟨ηflat, hηflat, hraw⟩ :=
    multiplicity_le_fine_bracketFour_dilate hdim c hγ0 hγ1 hKF ap' hap'
  refine ⟨ηflat, hηflat, ?_⟩
  intro a A g ha
  filter_upwards [hraw, self_mem_nhdsWithin] with δ hrawδ hδ0
  intro b hδb hb1 ι u Tb T K M CF R hM hCF hu hTball hKle hKfat hsub hED hF hfull
    hfullPay hFrostPay hfinalPay
  have hδE0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδEtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  set lam : NNReal := δ ^ g with hlam
  have hlam0 : 0 < lam := by
    rw [hlam]
    exact NNReal.rpow_pos hδ0
  have hlamE : (lam : ENNReal) = (δ : ENNReal) ^ g := by
    rw [hlam, ENNReal.coe_rpow_of_ne_zero hδ0.ne']
  obtain ⟨u₂, hu₂u, hu₂ne, μ₀, hμ₀, hbracket, hmult, hfull₂, hcard₂⟩ :=
    exists_internalDensityNormalization (E := E) (ι := ι) (τ := δ) (u := u)
      (lam := lam) hδ0 T hu hlam0 (by simpa only [hlamE] using hfull)
  have hpow : (lam : ENNReal) ^ 2 = (δ : ENNReal) ^ (2 * g) := by
    rw [hlamE, sq, ← ENNReal.rpow_add _ _ hδE0 hδEtop]
    congr 1
    ring
  have hfullFine : 16 * (fineNormalizeDilate.C c : ENNReal) * (δ : ENNReal) ^ ηflat
      ≤ ShadedBody.fullness u₂ (fun i => (T i).toShadedBody) := by
    calc
      16 * (fineNormalizeDilate.C c : ENNReal) * (δ : ENNReal) ^ ηflat
          ≤ (δ : ENNReal) ^ (2 * g) / 16 := hfullPay
      _ = (lam : ENNReal) ^ 2 / 16 := by rw [hpow]
      _ ≤ ShadedBody.fullness u₂ (fun i => (T i).toShadedBody) := hfull₂
  obtain ⟨i₀, hi₀⟩ := hu
  set v : ENNReal := volume (T i₀).carrier with hv
  have hvol : ∀ i ∈ u, volume ((T i).toConvexSpaceBody).carrier = v := by
    intro i _
    simpa [hv] using
      _root_.Tube.volume_carrier_eq_volume_carrier (T i).toTube (T i₀).toTube
  have hparent : ∀ i ∈ u, (T i).toConvexSpaceBody ≤ K := hsub
  set κ : ENNReal := (δ : ENNReal) ^ (2 * g) / 16 with hκ
  have hpow0 : (δ : ENNReal) ^ (2 * g) ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ0) hδEtop).ne'
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    exact (ENNReal.div_pos hpow0 (by norm_num)).ne'
  have hcardκ : κ * (u.card : ENNReal) ≤ (u₂.card : ENNReal) := by
    rw [hκ, ← hpow]
    exact hcard₂
  have htransfer := frostmanConstIn_subfamily_le (v := v) (κ := κ)
    (s := u) (s' := u₂) (W := fun i => (T i).toConvexSpaceBody) (K := K)
    ⟨i₀, hi₀⟩ hvol hparent hu₂u hκ0 hcardκ
  have hF₂ : frostmanConstIn u₂ (fun i => (T i).toConvexSpaceBody) K
      ≤ 2 * (CF : ENNReal) * (δ : ENNReal) ^ (-2 * ap') := by
    calc
      frostmanConstIn u₂ (fun i => (T i).toConvexSpaceBody) K
          ≤ κ⁻¹ * frostmanConstIn u (fun i => (T i).toConvexSpaceBody) K := htransfer
      _ ≤ κ⁻¹ * (δ : ENNReal) ^ (-a) := by gcongr
      _ ≤ 2 * (CF : ENNReal) * (δ : ENNReal) ^ (-2 * ap') := by
        simpa only [hκ] using hFrostPay
  have hraw₂ := hrawδ b hδb hb1 Tb T K M CF hM hCF hμ₀ hu₂ne hTball hKle hKfat
    (fun i hi => hsub i (hu₂u hi)) (hED.mono (Finset.coe_subset.mpr hu₂u)) hbracket
    hF₂ hfullFine
  have hcardMono :
      ((u₂.card : ENNReal) * ((δ / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^ (1 - γ / 2)
        ≤ ((u.card : ENNReal) * ((δ / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^
          (1 - γ / 2) := by
    apply ENNReal.rpow_le_rpow
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hu₂u) bot_le
    · linarith
  calc
    ShadedBody.multiplicity u (fun i => (T i).toShadedBody)
        ≤ 16 / (lam : ENNReal) *
            ShadedBody.multiplicity u₂ (fun i => (T i).toShadedBody) := hmult
    _ ≤ 16 / (lam : ENNReal) *
          ((M : ENNReal) * (fineAverageDilate.C c CF : ENNReal)
            * (δ : ENNReal) ^ (-3 * ap')
            * ((δ / b : NNReal) : ENNReal) ^ (-2 * γ)
            * ((u₂.card : ENNReal) * ((δ / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^
                (1 - γ / 2)) := by gcongr
    _ = (16 / (δ : ENNReal) ^ g *
          ((M : ENNReal) * (fineAverageDilate.C c CF : ENNReal)
            * (δ : ENNReal) ^ (-3 * ap')))
          * ((δ / b : NNReal) : ENNReal) ^ (-2 * γ)
          * ((u₂.card : ENNReal) * ((δ / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^
              (1 - γ / 2) := by rw [hlamE]; ring
    _ ≤ (δ : ENNReal) ^ (-A) * ((δ / b : NNReal) : ENNReal) ^ (-2 * γ)
          * ((u.card : ENNReal) * ((δ / b : NNReal) : ENNReal) ^ (2 : ℕ)) ^
              (1 - γ / 2) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hfinalPay bot_le) hcardMono bot_le bot_le

end Kakeya.ml1Boot

end

#print axioms Kakeya.ml1Boot.multiplicity_le_fine_bracketFour_dilate
#print axioms Kakeya.ml1Boot.multiplicity_le_fine_avg_dilate
