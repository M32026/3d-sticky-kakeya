/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.FrostmanPlankEstimate
public import Kakeya.DimensionThree.Plank.KatzTaoPlankEstimate
public import Kakeya.DimensionThree.Plank.WindowPacking

/-!
# The auxiliary-scale form of the Frostman plank estimate

This file separates the analytic scale carrying fullness and the sub-polynomial loss from the
shortest width of the planks.  The result is the Frostman, rather than Katz--Tao, analogue of the
two-scale interfaces used elsewhere in Section 6.
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody Filter
open scoped NNReal Real ENNReal

noncomputable section

namespace Kakeya

namespace FrostmanEstimate

/-- The non-loss part of the Frostman plank bound is bounded below by an absolute constant.

The critical-angle concentration count gives `1 ≤ M(a/b)`.  Testing the Frostman hypothesis on
the working window gives `1 ≤ CF · |s| · 8ab`.  After raising the two inequalities to the
complementary powers `β/2` and `1-β/2`, all aspect-ratio powers cancel. -/
private theorem auxScale_extraFactor_lower {ι : Type*} {s : Finset ι} {a b : ℝ≥0}
    {hab : a ≤ b} {hb1 : b ≤ 1} (V : ι → ShadedPlank a b hab hb1)
    {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1) (ha : 0 < a) (hs : s.Nonempty)
    (hwin : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ))
    {C_NC M : ℝ≥0} (hC_NC : 1 ≤ C_NC) (hM : 1 ≤ M)
    (hNC : Plank.IsThickeningNonconcentrated s (fun i => (V i).toPrism3D) C_NC M)
    {CF : ENNReal} (hCF1 : 1 ≤ CF) (hCFtop : CF ≠ ⊤)
    (hFrost : IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) plankWindow CF) :
    (8 : ENNReal) ^ (-(1 - β / 2)) ≤
      CF ^ (1 - β / 2) * (M : ENNReal) ^ (β / 2)
        * ((a : ENNReal) / (b : ENNReal)) * (b : ENNReal) ^ (-2 * β)
        * ((b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (1 - β / 2) := by
  classical
  have hb : 0 < b := ha.trans_le hab
  let p : ℝ := 1 - β / 2
  have hp : 0 < p := by dsimp [p]; nlinarith
  have hp0 : 0 ≤ p := hp.le
  have hβ2 : 0 ≤ β / 2 := by nlinarith
  have hMth : ∀ i ∈ s, ∀ (θ : ℝ≥0), a / b ≤ θ → ∀ (hθ1 : θ ≤ 1),
      (({j ∈ s | (V j).carrier ⊆
          (Plank.thickened (V i).toPrism3D θ hθ1).carrier}.card : ℝ≥0)) ≤ M * θ :=
    fun i hi θ hθa hθ1 =>
      Plank.IsThickeningNonconcentrated.aligned_card_le hC_NC hNC i hi θ hθ1 hθa
  have hMinv : M⁻¹ ≤ a / b :=
    inv_le_div_of_plankConcentration ha hab hb1 V hs hM hMth
  have hM0 : M ≠ 0 := (zero_lt_one.trans_le hM).ne'
  have hMr : (1 : ℝ≥0) ≤ M * (a / b) := by
    calc
      (1 : ℝ≥0) = M * M⁻¹ := by simp [hM0]
      _ ≤ M * (a / b) := mul_le_mul_left' hMinv M
  have hMrpow : (1 : ℝ≥0) ≤ M ^ (β / 2) * (a / b) ^ (β / 2) := by
    calc
      (1 : ℝ≥0) = 1 ^ (β / 2) := by simp
      _ ≤ (M * (a / b)) ^ (β / 2) := NNReal.rpow_le_rpow hMr hβ2
      _ = M ^ (β / 2) * (a / b) ^ (β / 2) := by rw [NNReal.mul_rpow]
  have hab0 : a / b ≠ 0 := div_ne_zero ha.ne' hb.ne'
  have hratio : (a / b) ^ p ≤ M ^ (β / 2) * (a / b) := by
    calc
      (a / b) ^ p = 1 * (a / b) ^ p := by rw [one_mul]
      _ ≤ (M ^ (β / 2) * (a / b) ^ (β / 2)) * (a / b) ^ p :=
        mul_le_mul_of_nonneg_right hMrpow (by positivity)
      _ = M ^ (β / 2) * (a / b) := by
        rw [mul_assoc, ← NNReal.rpow_add hab0]
        simp only [show β / 2 + p = 1 by dsimp [p]; ring, NNReal.rpow_one]
  have hvol := volume_plankWindow_le_of_isFrostmanIn V ha hs hwin hFrost
  have hmass : (1 : ENNReal) ≤
      CF * ((s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))) :=
    one_le_volume_plankWindow.trans hvol
  have hmassNN : (1 : ℝ≥0) ≤
      CF.toNNReal * ((s.card : ℝ≥0) * (8 * a * b)) := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_mul,
      ENNReal.coe_mul, ENNReal.coe_toNNReal hCFtop]
    norm_num at hmass ⊢
    simpa [mul_assoc] using hmass
  have hscale : (8 : ℝ≥0)⁻¹ * (b / a) ≤
      CF.toNNReal * (b ^ 2 * (s.card : ℝ≥0)) := by
    have hmul := mul_le_mul_of_nonneg_right hmassNN
      (show (0 : ℝ≥0) ≤ b / (8 * a) by positivity)
    calc
      (8 : ℝ≥0)⁻¹ * (b / a) = 1 * (b / (8 * a)) := by
        field_simp [ha.ne']
      _ ≤ (CF.toNNReal * ((s.card : ℝ≥0) * (8 * a * b))) * (b / (8 * a)) := hmul
      _ = CF.toNNReal * (b ^ 2 * (s.card : ℝ≥0)) := by
        field_simp [ha.ne']
  have hscalePow : (8 : ℝ≥0) ^ (-p) * (b / a) ^ p ≤
      CF.toNNReal ^ p * (b ^ 2 * (s.card : ℝ≥0)) ^ p := by
    have hpw := NNReal.rpow_le_rpow hscale hp0
    rw [NNReal.mul_rpow, NNReal.mul_rpow] at hpw
    simpa [NNReal.inv_rpow, ← NNReal.rpow_neg] using hpw
  have hbpow : (1 : ENNReal) ≤ (b : ENNReal) ^ (-2 * β) := by
    rw [show -2 * β = -(2 * β) by ring, ENNReal.rpow_neg]
    exact ENNReal.one_le_inv.mpr (ENNReal.rpow_le_one (by exact_mod_cast hb1) (by nlinarith))
  have hratioE : (a : ENNReal) / (b : ENNReal) = ((a / b : ℝ≥0) : ENNReal) := by
    rw [ENNReal.coe_div hb.ne']
  have hmainNN : (8 : ℝ≥0) ^ (-p) ≤
      CF.toNNReal ^ p * M ^ (β / 2) * (a / b) *
        (b ^ 2 * (s.card : ℝ≥0)) ^ p := by
    calc
      (8 : ℝ≥0) ^ (-p) =
          ((8 : ℝ≥0) ^ (-p) * (b / a) ^ p) * (a / b) ^ p := by
        have hba0 : b / a ≠ 0 := div_ne_zero hb.ne' ha.ne'
        calc
          (8 : ℝ≥0) ^ (-p) = (8 : ℝ≥0) ^ (-p) * 1 := by rw [mul_one]
          _ = (8 : ℝ≥0) ^ (-p) * (((b / a) * (a / b)) ^ p) := by
            have hprod : (b / a) * (a / b) = 1 := by field_simp [ha.ne', hb.ne']
            rw [hprod, NNReal.one_rpow]
          _ = ((8 : ℝ≥0) ^ (-p) * (b / a) ^ p) * (a / b) ^ p := by
            rw [NNReal.mul_rpow]
            ring
      _ ≤ (CF.toNNReal ^ p * (b ^ 2 * (s.card : ℝ≥0)) ^ p) * (a / b) ^ p :=
        mul_le_mul_of_nonneg_right hscalePow (by positivity)
      _ ≤ (CF.toNNReal ^ p * (b ^ 2 * (s.card : ℝ≥0)) ^ p) *
          (M ^ (β / 2) * (a / b)) := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = CF.toNNReal ^ p * M ^ (β / 2) * (a / b) *
          (b ^ 2 * (s.card : ℝ≥0)) ^ p := by ring
  have hmainE : (8 : ENNReal) ^ (-p) ≤
      CF ^ p * (M : ENNReal) ^ (β / 2) * ((a : ENNReal) / (b : ENNReal)) *
        ((b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ p := by
    have hCFnn0 : CF.toNNReal ≠ 0 := by
      exact ENNReal.toNNReal_ne_zero.mpr ⟨(zero_lt_one.trans_le hCF1).ne', hCFtop⟩
    have hcard0 : (s.card : ℝ≥0) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hs
    have hbase0 : b ^ 2 * (s.card : ℝ≥0) ≠ 0 :=
      mul_ne_zero (pow_ne_zero 2 hb.ne') hcard0
    calc
      (8 : ENNReal) ^ (-p) = (((8 : ℝ≥0) ^ (-p) : ℝ≥0) : ENNReal) := by
        exact (ENNReal.coe_rpow_of_ne_zero (by norm_num : (8 : ℝ≥0) ≠ 0) (-p)).symm
      _ ≤ ((CF.toNNReal ^ p * M ^ (β / 2) * (a / b) *
          (b ^ 2 * (s.card : ℝ≥0)) ^ p : ℝ≥0) : ENNReal) :=
        ENNReal.coe_le_coe.mpr hmainNN
      _ = CF ^ p * (M : ENNReal) ^ (β / 2) * ((a : ENNReal) / (b : ENNReal)) *
          ((b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ p := by
        simp only [ENNReal.coe_mul]
        rw [ENNReal.coe_rpow_of_ne_zero hCFnn0,
          ENNReal.coe_rpow_of_ne_zero hM0, ENNReal.coe_rpow_of_ne_zero hbase0,
          ENNReal.coe_toNNReal hCFtop, ENNReal.coe_div hb.ne']
        simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_natCast]
  dsimp [p] at hmainE ⊢
  calc
    (8 : ENNReal) ^ (-(1 - β / 2)) ≤
        CF ^ (1 - β / 2) * (M : ENNReal) ^ (β / 2)
          * ((a : ENNReal) / (b : ENNReal))
          * ((b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (1 - β / 2) := hmainE
    _ = (CF ^ (1 - β / 2) * (M : ENNReal) ^ (β / 2)
          * ((a : ENNReal) / (b : ENNReal)) * 1
          * ((b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (1 - β / 2)) := by ring
    _ ≤ CF ^ (1 - β / 2) * (M : ENNReal) ^ (β / 2)
          * ((a : ENNReal) / (b : ENNReal)) * (b : ENNReal) ^ (-2 * β)
          * ((b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (1 - β / 2) := by gcongr

/-- **GWZ Lemma 6.4 with an auxiliary analytic scale.**

The planks have dimensions `a × b × 1`, while `τ ≤ a` carries both the fullness threshold and the
loss.  The proof is the standard Remark 3.6 dichotomy.  When `a ^ C ≤ τ`, the ordinary plank
estimate applies after rescaling its fullness exponent.  When `τ < a ^ C`, the loss alone pays for
the polynomial packing bound for essentially distinct windowed planks; the concentration and
Frostman hypotheses make the remaining factors bounded below up to an absolute constant. -/
theorem plankEstimate_auxScale.{u} {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKF : FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β) :
    ∃ C_NC : ℝ≥0, 1 ≤ C_NC ∧
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ b₀ > (0 : ℝ≥0),
      ∀ {ι : Type u} (s : Finset ι) {τ a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1)
        (V : ι → ShadedPlank a b hab hb1),
        0 < τ → τ ≤ a → b ≤ b₀ →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) →
        (s : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (V i).carrier (V j).carrier) →
        τ ^ η ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody) →
        ∀ (M : ℝ≥0), 1 ≤ M →
        Plank.IsThickeningNonconcentrated s (fun i => (V i).toPrism3D) C_NC M →
        ∀ (CF : ENNReal), 1 ≤ CF → CF ≠ ⊤ →
          IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) plankWindow CF →
          ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
            (τ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * (M : ENNReal) ^ (β / 2)
              * ((a : ENNReal) / (b : ENNReal)) * (b : ENNReal) ^ (-2 * β)
              * ((b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (1 - β / 2) := by
  classical
  obtain ⟨C_NC, hC_NC, hbaseAll⟩ :=
    FrostmanEstimate.plankEstimate.{u} hβpos hβle hKF
  refine ⟨C_NC, hC_NC, ?_⟩
  intro ε hε
  obtain ⟨η₁, hη₁, bbase, hbbase, hbase⟩ := hbaseAll (ε / 2) (by positivity)
  obtain ⟨Cwin, Dwin, hCwin, hDwin, hpackCard⟩ :=
    Plank.card_le_of_windowed_essentiallyDistinct_shaded
  let Cpack : ℝ≥0 := max 1 Cwin
  have hCpack : 1 ≤ Cpack := le_max_left _ _
  have hCwinpack : Cwin ≤ Cpack := le_max_right _ _
  let C : ℝ := 4 * (Dwin + 1) / ε
  have hC : 0 < C := by dsimp [C]; positivity
  have hDC : Dwin / C ≤ ε / 4 := by
    dsimp [C]
    have hD1 : 0 < Dwin + 1 := by linarith
    field_simp [hε.ne', hD1.ne']
    nlinarith [hDwin]
  let η : ℝ := η₁ / C
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨bpack, hbpack, hpackAbsorb⟩ :=
    plankKT_absorb Cpack hCpack (p := (1 : ℝ)) (e := ε / 4) (by norm_num) (by positivity)
  have hp0 : 0 ≤ 1 - β / 2 := by nlinarith
  obtain ⟨beight, hbeight, heightAbsorb⟩ :=
    plankKT_absorb 8 (by norm_num) (p := 1 - β / 2) (e := ε / 2) hp0 (by positivity)
  let b₀ : ℝ≥0 := min bbase (min bpack beight)
  have hb₀ : 0 < b₀ := by
    dsimp [b₀]
    exact lt_min hbbase (lt_min hbpack hbeight)
  refine ⟨η, hη, b₀, hb₀, ?_⟩
  intro ι s τ a b hab hb1 V hτ hτa hbb₀ hwin hed hfull M hM hNC CF hCF1 hCFtop hFrost
  have ha : 0 < a := hτ.trans_le hτa
  have hb : 0 < b := ha.trans_le hab
  have hτ1 : τ ≤ 1 := hτa.trans (hab.trans hb1)
  have hbbase' : b ≤ bbase := hbb₀.trans (min_le_left _ _)
  have hτpack : τ ≤ bpack :=
    (hτa.trans (hab.trans hbb₀)).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτeight : τ ≤ beight :=
    (hτa.trans (hab.trans hbb₀)).trans ((min_le_right _ _).trans (min_le_right _ _))
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [ShadedBody.multiplicity_empty]
  by_cases hcase : a ^ C ≤ τ
  · have hfund : a ^ η₁ ≤ τ ^ η := by
      calc
        a ^ η₁ = (a ^ C) ^ (η₁ / C) := by
          rw [← NNReal.rpow_mul]
          congr 1
          field_simp [hC.ne']
        _ ≤ τ ^ (η₁ / C) := NNReal.rpow_le_rpow hcase (by positivity)
        _ = τ ^ η := rfl
    have hfullBase : a ^ η₁ ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody) :=
      hfund.trans hfull
    have hordinary :=
      (hbase s hab hb1 V ha hbbase' hwin hed hfullBase M hM hNC CF hCF1 hCFtop hFrost).2
    have hloss₁ : (a : ENNReal) ^ (-(ε / 2)) ≤ (τ : ENNReal) ^ (-(ε / 2)) := by
      have hNN : a ^ (-(ε / 2)) ≤ τ ^ (-(ε / 2)) :=
        NNReal.rpow_le_rpow_of_nonpos hτ hτa (by linarith)
      rw [← ENNReal.coe_rpow_of_ne_zero ha.ne',
        ← ENNReal.coe_rpow_of_ne_zero hτ.ne']
      exact_mod_cast hNN
    have hloss₂ : (τ : ENNReal) ^ (-(ε / 2)) ≤ (τ : ENNReal) ^ (-ε) := by
      exact ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hτ1) (by linarith)
    exact hordinary.trans (by
      gcongr
      exact hloss₁.trans hloss₂)
  · push Not at hcase
    have hwindow : Plank.IsWindowedFamily s (ShadedPlank.planks V) :=
      isWindowedFamily_of_subset_plankWindow s V hwin
    have hcard := hpackCard s V ha hwindow hed
    have hpowDeep : a ^ (-Dwin) ≤ τ ^ (-(Dwin / C)) := by
      have hp := NNReal.rpow_le_rpow_of_nonpos hτ hcase.le
        (neg_nonpos.mpr (div_nonneg hDwin hC.le))
      calc
        a ^ (-Dwin) = (a ^ C) ^ (-(Dwin / C)) := by
          rw [← NNReal.rpow_mul]
          congr 1
          field_simp [hC.ne']
        _ ≤ τ ^ (-(Dwin / C)) := hp
    have hpowQuarter : τ ^ (-(Dwin / C)) ≤ τ ^ (-(ε / 4)) := by
      exact NNReal.rpow_le_rpow_of_exponent_ge hτ hτ1 (by linarith [hDC])
    have hcardQuarter : (s.card : ℝ≥0) ≤ Cpack * τ ^ (-(ε / 4)) := by
      calc
        (s.card : ℝ≥0) ≤ Cwin * a ^ (-Dwin) := hcard
        _ ≤ Cpack * τ ^ (-(ε / 4)) := by
          gcongr
          exact hpowDeep.trans hpowQuarter
    have hpackLoss : (Cpack : ENNReal) ≤ (τ : ENNReal) ^ (-(ε / 4)) :=
      by simpa [ENNReal.rpow_one] using hpackAbsorb τ hτ hτpack
    have hmuHalf : ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
        (τ : ENNReal) ^ (-(ε / 2)) := by
      calc
        ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤ (s.card : ENNReal) :=
          ShadedBody.multiplicity_le_card s (fun i => (V i).toShadedBody)
        _ ≤ (Cpack : ENNReal) * (τ : ENNReal) ^ (-(ε / 4)) := by
          have hcast := ENNReal.coe_le_coe.mpr hcardQuarter
          rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hτ.ne'] at hcast
          simpa using hcast
        _ ≤ (τ : ENNReal) ^ (-(ε / 4)) * (τ : ENNReal) ^ (-(ε / 4)) := by gcongr
        _ = (τ : ENNReal) ^ (-(ε / 2)) := by
          rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hτ.ne') ENNReal.coe_ne_top]
          congr 1
          ring
    let X : ENNReal := CF ^ (1 - β / 2) * (M : ENNReal) ^ (β / 2)
      * ((a : ENNReal) / (b : ENNReal)) * (b : ENNReal) ^ (-2 * β)
      * ((b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (1 - β / 2)
    have hX : (8 : ENNReal) ^ (-(1 - β / 2)) ≤ X :=
      auxScale_extraFactor_lower V hβpos hβle ha hs hwin hC_NC hM hNC hCF1 hCFtop hFrost
    have heightLoss : (8 : ENNReal) ^ (1 - β / 2) ≤
        (τ : ENNReal) ^ (-(ε / 2)) := heightAbsorb τ hτ hτeight
    have hXfund : 1 ≤ (τ : ENNReal) ^ (-(ε / 2)) * X := by
      have h8zero : (8 : ENNReal) ^ (1 - β / 2) ≠ 0 := by positivity
      have h8top : (8 : ENNReal) ^ (1 - β / 2) ≠ ⊤ := by finiteness
      calc
        (1 : ENNReal) = (8 : ENNReal) ^ (1 - β / 2) *
            (8 : ENNReal) ^ (-(1 - β / 2)) := by
          rw [ENNReal.rpow_neg, ENNReal.mul_inv_cancel h8zero h8top]
        _ ≤ (τ : ENNReal) ^ (-(ε / 2)) * X := mul_le_mul heightLoss hX (by positivity) (by positivity)
    calc
      ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
          (τ : ENNReal) ^ (-(ε / 2)) := hmuHalf
      _ = (τ : ENNReal) ^ (-(ε / 2)) * 1 := by rw [mul_one]
      _ ≤ (τ : ENNReal) ^ (-(ε / 2)) *
          ((τ : ENNReal) ^ (-(ε / 2)) * X) := mul_le_mul_left' hXfund _
      _ = (τ : ENNReal) ^ (-ε) * X := by
        rw [← mul_assoc, ← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hτ.ne') ENNReal.coe_ne_top]
        rw [show -(ε / 2) + -(ε / 2) = -ε by ring]
      _ = ( τ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * (M : ENNReal) ^ (β / 2)
          * ((a : ENNReal) / (b : ENNReal)) * (b : ENNReal) ^ (-2 * β)
          * ((b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (1 - β / 2) := by
        dsimp [X]
        ring

/-- **The deep branch of the auxiliary-scale Frostman plank estimate.**

If the analytic scale `τ` lies below a sufficiently large fixed power of the thin plank width,
window packing alone pays for the multiplicity.  Unlike `plankEstimate_auxScale`, this statement
has no smallness hypothesis on the middle width `b`: its only smallness threshold is placed on
`τ`, which is the scale that actually absorbs the two fixed packing constants.

This is the branch of Remark 3.6 used by Proposition 6.6(A) when the factor plank's thin width has
already been pigeonholed below a fixed power of the fine-tube scale. -/
theorem plankEstimate_auxScale_deep.{u} {β ε : ℝ}
    (hβpos : 0 < β) (hβle : β ≤ 1) (hε : 0 < ε) :
    ∃ Cdeep > (0 : ℝ), ∃ τ₀ > (0 : ℝ≥0),
      ∀ {ι : Type u} (s : Finset ι) {τ a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1)
        (V : ι → ShadedPlank a b hab hb1),
        0 < τ → τ ≤ a → τ ≤ τ₀ → τ < a ^ Cdeep →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) →
        (s : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (V i).carrier (V j).carrier) →
        ∀ (C_NC M : ℝ≥0), 1 ≤ C_NC → 1 ≤ M →
        Plank.IsThickeningNonconcentrated s (fun i => (V i).toPrism3D) C_NC M →
        ∀ (CF : ENNReal), 1 ≤ CF → CF ≠ ⊤ →
          IsFrostmanIn s (fun i => (V i).toConvexSpaceBody) plankWindow CF →
          ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
            (τ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * (M : ENNReal) ^ (β / 2)
              * ((a : ENNReal) / (b : ENNReal)) * (b : ENNReal) ^ (-2 * β)
              * ((b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (1 - β / 2) := by
  classical
  obtain ⟨Cwin, Dwin, hCwin, hDwin, hpackCard⟩ :=
    Plank.card_le_of_windowed_essentiallyDistinct_shaded
  let Cpack : ℝ≥0 := max 1 Cwin
  have hCpack : 1 ≤ Cpack := le_max_left _ _
  have hCwinpack : Cwin ≤ Cpack := le_max_right _ _
  let Cdeep : ℝ := 4 * (Dwin + 1) / ε
  have hCdeep : 0 < Cdeep := by dsimp [Cdeep]; positivity
  have hDC : Dwin / Cdeep ≤ ε / 4 := by
    dsimp [Cdeep]
    have hD1 : 0 < Dwin + 1 := by linarith
    field_simp [hε.ne', hD1.ne']
    nlinarith [hDwin]
  obtain ⟨τpack, hτpack, hpackAbsorb⟩ :=
    plankKT_absorb Cpack hCpack (p := (1 : ℝ)) (e := ε / 4)
      (by norm_num) (by positivity)
  have hp0 : 0 ≤ 1 - β / 2 := by nlinarith
  obtain ⟨τeight, hτeight, heightAbsorb⟩ :=
    plankKT_absorb 8 (by norm_num) (p := 1 - β / 2) (e := ε / 2)
      hp0 (by positivity)
  let τ₀ : ℝ≥0 := min τpack τeight
  have hτ₀ : 0 < τ₀ := by
    dsimp [τ₀]
    exact lt_min hτpack hτeight
  refine ⟨Cdeep, hCdeep, τ₀, hτ₀, ?_⟩
  intro ι s τ a b hab hb1 V hτ hτa hττ₀ hdeep hwin hed C_NC M hC_NC hM hNC CF
    hCF1 hCFtop hFrost
  have ha : 0 < a := hτ.trans_le hτa
  have hτ1 : τ ≤ 1 := hτa.trans (hab.trans hb1)
  have hτpack' : τ ≤ τpack := hττ₀.trans (min_le_left _ _)
  have hτeight' : τ ≤ τeight := hττ₀.trans (min_le_right _ _)
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [ShadedBody.multiplicity_empty]
  have hwindow : Plank.IsWindowedFamily s (ShadedPlank.planks V) :=
    isWindowedFamily_of_subset_plankWindow s V hwin
  have hcard := hpackCard s V ha hwindow hed
  have hpowDeep : a ^ (-Dwin) ≤ τ ^ (-(Dwin / Cdeep)) := by
    have hp := NNReal.rpow_le_rpow_of_nonpos hτ hdeep.le
      (neg_nonpos.mpr (div_nonneg hDwin hCdeep.le))
    calc
      a ^ (-Dwin) = (a ^ Cdeep) ^ (-(Dwin / Cdeep)) := by
        rw [← NNReal.rpow_mul]
        congr 1
        field_simp [hCdeep.ne']
      _ ≤ τ ^ (-(Dwin / Cdeep)) := hp
  have hpowQuarter : τ ^ (-(Dwin / Cdeep)) ≤ τ ^ (-(ε / 4)) := by
    exact NNReal.rpow_le_rpow_of_exponent_ge hτ hτ1 (by linarith [hDC])
  have hcardQuarter : (s.card : ℝ≥0) ≤ Cpack * τ ^ (-(ε / 4)) := by
    calc
      (s.card : ℝ≥0) ≤ Cwin * a ^ (-Dwin) := hcard
      _ ≤ Cpack * τ ^ (-(ε / 4)) := by
        gcongr
        exact hpowDeep.trans hpowQuarter
  have hpackLoss : (Cpack : ENNReal) ≤ (τ : ENNReal) ^ (-(ε / 4)) :=
    by simpa [ENNReal.rpow_one] using hpackAbsorb τ hτ hτpack'
  have hmuHalf : ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
      (τ : ENNReal) ^ (-(ε / 2)) := by
    calc
      ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤ (s.card : ENNReal) :=
        ShadedBody.multiplicity_le_card s (fun i => (V i).toShadedBody)
      _ ≤ (Cpack : ENNReal) * (τ : ENNReal) ^ (-(ε / 4)) := by
        have hcast := ENNReal.coe_le_coe.mpr hcardQuarter
        rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hτ.ne'] at hcast
        simpa using hcast
      _ ≤ (τ : ENNReal) ^ (-(ε / 4)) * (τ : ENNReal) ^ (-(ε / 4)) := by gcongr
      _ = (τ : ENNReal) ^ (-(ε / 2)) := by
        rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hτ.ne') ENNReal.coe_ne_top]
        congr 1
        ring
  let X : ENNReal := CF ^ (1 - β / 2) * (M : ENNReal) ^ (β / 2)
    * ((a : ENNReal) / (b : ENNReal)) * (b : ENNReal) ^ (-2 * β)
    * ((b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (1 - β / 2)
  have hX : (8 : ENNReal) ^ (-(1 - β / 2)) ≤ X :=
    auxScale_extraFactor_lower V hβpos hβle ha hs hwin hC_NC hM hNC hCF1 hCFtop hFrost
  have heightLoss : (8 : ENNReal) ^ (1 - β / 2) ≤
      (τ : ENNReal) ^ (-(ε / 2)) := heightAbsorb τ hτ hτeight'
  have hXfund : 1 ≤ (τ : ENNReal) ^ (-(ε / 2)) * X := by
    have h8zero : (8 : ENNReal) ^ (1 - β / 2) ≠ 0 := by positivity
    have h8top : (8 : ENNReal) ^ (1 - β / 2) ≠ ⊤ := by finiteness
    calc
      (1 : ENNReal) = (8 : ENNReal) ^ (1 - β / 2) *
          (8 : ENNReal) ^ (-(1 - β / 2)) := by
        rw [ENNReal.rpow_neg, ENNReal.mul_inv_cancel h8zero h8top]
      _ ≤ (τ : ENNReal) ^ (-(ε / 2)) * X :=
        mul_le_mul heightLoss hX (by positivity) (by positivity)
  calc
    ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
        (τ : ENNReal) ^ (-(ε / 2)) := hmuHalf
    _ = (τ : ENNReal) ^ (-(ε / 2)) * 1 := by rw [mul_one]
    _ ≤ (τ : ENNReal) ^ (-(ε / 2)) *
        ((τ : ENNReal) ^ (-(ε / 2)) * X) := mul_le_mul_left' hXfund _
    _ = (τ : ENNReal) ^ (-ε) * X := by
      rw [← mul_assoc,
        ← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hτ.ne') ENNReal.coe_ne_top]
      rw [show -(ε / 2) + -(ε / 2) = -ε by ring]
    _ = (τ : ENNReal) ^ (-ε) * CF ^ (1 - β / 2) * (M : ENNReal) ^ (β / 2)
        * ((a : ENNReal) / (b : ENNReal)) * (b : ENNReal) ^ (-2 * β)
        * ((b : ENNReal) ^ 2 * (s.card : ENNReal)) ^ (1 - β / 2) := by
      dsimp [X]
      ring

end FrostmanEstimate

namespace KatzTaoEstimate

/-- **GWZ Lemma 6.1 (Katz--Tao case) with an auxiliary analytic scale.**

The plank widths are `a × b × 1`, but the smaller scale `τ ≤ a` carries the fullness,
wide-slab and loss budgets.  This is the Katz--Tao companion of
`FrostmanEstimate.plankEstimate_auxScale`.  It is derived from the ordinary plank estimate by
the same Remark 3.6 dichotomy: if `a ^ C ≤ τ`, the hypotheses at `τ` fund the ordinary theorem
at `a`; otherwise pairwise essential distinctness in the fixed window gives a polynomial packing
bound, which the gap between `τ` and `a` absorbs. -/
theorem plankEstimate_auxScale {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∃ b₀ > (0 : ℝ≥0),
      ∀ {ι : Type*} (s : Finset ι) {τ a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1)
        (V : ι → ShadedPlank a b hab hb1),
        0 < τ → τ ≤ a → b ≤ b₀ →
        (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) →
        (s : Set ι).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct (V i).carrier (V j).carrier) →
        τ ^ η ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody) →
        ∀ (γ : ℝ), 0 ≤ γ → γ ≤ 1 →
        (∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a / b ≤ φ →
            ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
              ((Plank.inWideSlabFamily s (fun i => (V i).toPrism3D) S).card : ℝ≥0)
                ≤ τ ^ (-η) * φ ^ γ * (s.card : ℝ≥0)) →
          ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
            (τ : ENNReal) ^ (-ε)
              * (maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β)
              * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β := by
  classical
  intro ε hε
  obtain ⟨η₁, hη₁, bbase, hbbase, hbase⟩ :=
    KatzTaoEstimate.plankEstimate hβpos hβle hKKT (ε / 2) (by positivity)
  obtain ⟨Cwin, Dwin, hCwin, hDwin, hpackCard⟩ :=
    Plank.card_le_of_windowed_essentiallyDistinct_shaded
  let Cpack : ℝ≥0 := max 1 Cwin
  have hCpack : 1 ≤ Cpack := le_max_left _ _
  have hCwinpack : Cwin ≤ Cpack := le_max_right _ _
  let C : ℝ := 4 * (Dwin + 1) / ε
  have hC : 0 < C := by dsimp [C]; positivity
  have hDC : Dwin / C ≤ ε / 4 := by
    dsimp [C]
    have hD1 : 0 < Dwin + 1 := by linarith
    field_simp [hε.ne', hD1.ne']
    nlinarith [hDwin]
  let η : ℝ := min (η₁ / C) (ε / 4)
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min (by positivity) (by positivity)
  have hηC : C * η ≤ η₁ := by
    have hmin : η ≤ η₁ / C := min_le_left _ _
    have := mul_le_mul_of_nonneg_left hmin hC.le
    field_simp [hC.ne'] at this
    exact this
  have hηβ : η * β ≤ ε / 4 := by
    calc
      η * β ≤ (ε / 4) * β :=
        mul_le_mul_of_nonneg_right (min_le_right (η₁ / C) (ε / 4)) hβpos.le
      _ ≤ (ε / 4) * 1 := mul_le_mul_of_nonneg_left hβle (by positivity)
      _ = ε / 4 := by ring
  obtain ⟨bpack, hbpack, hpackAbsorb⟩ :=
    plankKT_absorb Cpack hCpack (p := (1 : ℝ)) (e := ε / 4)
      (by norm_num) (by positivity)
  let b₀ : ℝ≥0 := min bbase bpack
  have hb₀ : 0 < b₀ := lt_min hbbase hbpack
  refine ⟨η, hη, b₀, hb₀, ?_⟩
  intro ι s τ a b hab hb1 V hτ hτa hbb₀ hwin hed hfull γ hγ0 hγ1 hslab
  have ha : 0 < a := hτ.trans_le hτa
  have hb : 0 < b := ha.trans_le hab
  have hτ1 : τ ≤ 1 := hτa.trans (hab.trans hb1)
  have hbbase' : b ≤ bbase := hbb₀.trans (min_le_left _ _)
  have hτpack : τ ≤ bpack := hτa.trans (hab.trans (hbb₀.trans (min_le_right _ _)))
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [ShadedBody.multiplicity_empty]
  by_cases hcase : a ^ C ≤ τ
  · have hfund : a ^ η₁ ≤ τ ^ η := by
      calc
        a ^ η₁ ≤ a ^ (C * η) := by
          exact NNReal.rpow_le_rpow_of_exponent_ge ha (hab.trans hb1) hηC
        _ = (a ^ C) ^ η := by rw [NNReal.rpow_mul]
        _ ≤ τ ^ η := NNReal.rpow_le_rpow hcase hη.le
    have hfullBase : a ^ η₁ ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody) :=
      hfund.trans hfull
    have hslabBase : ∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a / b ≤ φ →
        ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
          ((Plank.inWideSlabFamily s (fun i => (V i).toPrism3D) S).card : ℝ≥0)
            ≤ a ^ (-η₁) * φ ^ γ * (s.card : ℝ≥0) := by
      intro φ hφR hφ S
      have hcoef : τ ^ (-η) ≤ a ^ (-η₁) := by
        calc
          τ ^ (-η) ≤ (a ^ C) ^ (-η) :=
            NNReal.rpow_le_rpow_of_nonpos (by positivity) hcase (by linarith)
          _ = a ^ (-(C * η)) := by
            rw [← NNReal.rpow_mul]
            congr 1
            ring
          _ ≤ a ^ (-η₁) :=
            NNReal.rpow_le_rpow_of_exponent_ge ha (hab.trans hb1) (by linarith)
      exact (hslab φ hφR hφ S).trans (by gcongr)
    have hordinary := hbase s hab hb1 V ha hbbase' hwin hed hfullBase γ hγ0 hγ1 hslabBase
    have hloss₁ : (a : ENNReal) ^ (-(ε / 2)) ≤ (τ : ENNReal) ^ (-(ε / 2)) := by
      have hNN : a ^ (-(ε / 2)) ≤ τ ^ (-(ε / 2)) :=
        NNReal.rpow_le_rpow_of_nonpos hτ hτa (by linarith)
      rw [← ENNReal.coe_rpow_of_ne_zero ha.ne',
        ← ENNReal.coe_rpow_of_ne_zero hτ.ne']
      exact_mod_cast hNN
    have hloss₂ : (τ : ENNReal) ^ (-(ε / 2)) ≤ (τ : ENNReal) ^ (-ε) :=
      ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hτ1) (by linarith)
    exact hordinary.trans (by gcongr; exact hloss₁.trans hloss₂)
  · push Not at hcase
    have hwindow : Plank.IsWindowedFamily s (ShadedPlank.planks V) :=
      isWindowedFamily_of_subset_plankWindow s V hwin
    have hcard := hpackCard s V ha hwindow hed
    have hpowDeep : a ^ (-Dwin) ≤ τ ^ (-(Dwin / C)) := by
      have hp := NNReal.rpow_le_rpow_of_nonpos hτ hcase.le
        (neg_nonpos.mpr (div_nonneg hDwin hC.le))
      calc
        a ^ (-Dwin) = (a ^ C) ^ (-(Dwin / C)) := by
          rw [← NNReal.rpow_mul]
          congr 1
          field_simp [hC.ne']
        _ ≤ τ ^ (-(Dwin / C)) := hp
    have hpowQuarter : τ ^ (-(Dwin / C)) ≤ τ ^ (-(ε / 4)) :=
      NNReal.rpow_le_rpow_of_exponent_ge hτ hτ1 (by linarith [hDC])
    have hcardQuarter : (s.card : ℝ≥0) ≤ Cpack * τ ^ (-(ε / 4)) := by
      calc
        (s.card : ℝ≥0) ≤ Cwin * a ^ (-Dwin) := hcard
        _ ≤ Cpack * τ ^ (-(ε / 4)) := by
          gcongr
          exact hpowDeep.trans hpowQuarter
    have hpackLoss : (Cpack : ENNReal) ≤ (τ : ENNReal) ^ (-(ε / 4)) := by
      simpa [ENNReal.rpow_one] using hpackAbsorb τ hτ hτpack
    have hmuHalf : ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤
        (τ : ENNReal) ^ (-(ε / 2)) := by
      calc
        ShadedBody.multiplicity s (fun i => (V i).toShadedBody) ≤ (s.card : ENNReal) :=
          ShadedBody.multiplicity_le_card s (fun i => (V i).toShadedBody)
        _ ≤ (Cpack : ENNReal) * (τ : ENNReal) ^ (-(ε / 4)) := by
          have hcast := ENNReal.coe_le_coe.mpr hcardQuarter
          rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hτ.ne'] at hcast
          exact hcast
        _ ≤ (τ : ENNReal) ^ (-(ε / 4)) * (τ : ENNReal) ^ (-(ε / 4)) := by
          gcongr
        _ = (τ : ENNReal) ^ (-(ε / 2)) := by
          rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hτ.ne') ENNReal.coe_ne_top]
          congr 1
          ring
    obtain ⟨i₀, hi₀⟩ := hs
    have hr : a / b ≤ Rslab :=
      (div_le_one hb |>.2 hab).trans one_le_Rslab
    have har : a ≤ a / b := by
      rw [le_div_iff₀ hb]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hb1 a.2
    let S : Prism3D (a / b) Rslab Rslab hr le_rfl :=
      Plank.toWideSlab ((V i₀).toPrism3D) (a / b) Rslab hr
    have hiS : i₀ ∈ Plank.inWideSlabFamily s (fun i => (V i).toPrism3D) S := by
      simpa [S] using (Plank.mem_inWideSlabFamily_toWideSlab
        (V := fun i => (V i).toPrism3D) hi₀ har one_le_Rslab hr)
    have hone : (1 : ℝ≥0) ≤
        (Plank.inWideSlabFamily s (fun i => (V i).toPrism3D) S).card := by
      exact_mod_cast Finset.one_le_card.mpr ⟨i₀, hiS⟩
    have hself := hone.trans (hslab (a / b) hr le_rfl S)
    have hτfundNN : τ ^ (η * β) ≤ (a / b) ^ (γ * β) * (s.card : ℝ≥0) ^ β := by
      have hmul : τ ^ η ≤ (a / b) ^ γ * (s.card : ℝ≥0) := by
        have hτcancel : τ ^ η * τ ^ (-η) = 1 := by
          rw [← NNReal.rpow_add hτ.ne']
          simp
        calc
          τ ^ η = τ ^ η * 1 := by rw [mul_one]
          _ ≤ τ ^ η * (τ ^ (-η) * (a / b) ^ γ * (s.card : ℝ≥0)) := by gcongr
          _ = (a / b) ^ γ * (s.card : ℝ≥0) := by
            rw [show τ ^ η * (τ ^ (-η) * (a / b) ^ γ * (s.card : ℝ≥0)) =
              (τ ^ η * τ ^ (-η)) * ((a / b) ^ γ * (s.card : ℝ≥0)) by ring,
              hτcancel, one_mul]
      have hp := NNReal.rpow_le_rpow hmul hβpos.le
      rw [NNReal.mul_rpow, ← NNReal.rpow_mul, ← NNReal.rpow_mul] at hp
      simpa [mul_assoc] using hp
    have hτfund : (τ : ENNReal) ^ (η * β) ≤
        ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β := by
      have hcast := ENNReal.coe_le_coe.mpr hτfundNN
      rw [ENNReal.coe_rpow_of_ne_zero hτ.ne', ENNReal.coe_mul,
        ENNReal.coe_rpow_of_ne_zero (div_ne_zero ha.ne' hb.ne'),
        ENNReal.coe_div hb.ne', ENNReal.coe_rpow_of_ne_zero (by
          exact_mod_cast Finset.card_ne_zero.mpr ⟨i₀, hi₀⟩)] at hcast
      simpa using hcast
    have hmax : (1 : ENNReal) ≤
        maxDensity s (fun i => (V i).toConvexSpaceBody) := by
      apply one_le_maxDensity
      refine ⟨i₀, hi₀, ?_⟩
      rw [show volume (V i₀).carrier =
          8 * (a : ENNReal) * (b : ENNReal) * 1 by
            exact Prism3D.volume_carrier (V i₀).toPrism3D]
      positivity
    have hmaxpow : (1 : ENNReal) ≤
        (maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β) := by
      simpa using ENNReal.rpow_le_rpow hmax (by linarith : 0 ≤ 1 - β)
    have hexp : (τ : ENNReal) ^ (-(ε / 2)) ≤
        (τ : ENNReal) ^ (-ε) * (τ : ENNReal) ^ (η * β) := by
      rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hτ.ne') ENNReal.coe_ne_top]
      exact ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hτ1) (by linarith [hηβ])
    exact hmuHalf.trans <| by
      calc
        (τ : ENNReal) ^ (-(ε / 2)) ≤
            (τ : ENNReal) ^ (-ε) * (τ : ENNReal) ^ (η * β) := hexp
        _ ≤ (τ : ENNReal) ^ (-ε) *
            ((maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β) *
              (((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β)) := by
          gcongr
          calc
            (τ : ENNReal) ^ (η * β) ≤
                ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β := hτfund
            _ = 1 * (((a : ENNReal) / (b : ENNReal)) ^ (γ * β) *
                (s.card : ENNReal) ^ β) := by rw [one_mul]
            _ ≤ (maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β) *
                (((a : ENNReal) / (b : ENNReal)) ^ (γ * β) *
                  (s.card : ENNReal) ^ β) := by gcongr
        _ = (τ : ENNReal) ^ (-ε)
              * (maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β)
              * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β := by
          ring

end KatzTaoEstimate

end Kakeya
