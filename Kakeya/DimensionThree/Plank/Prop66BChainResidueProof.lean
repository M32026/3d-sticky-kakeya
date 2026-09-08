/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Prop66BConstructedSplit
public import Kakeya.DimensionThree.Plank.Prop66BChainResidue

/-!
# GWZ Proposition 6.6(B): the residue of the fine-ED chain is proved

 `Kakeya.Prop66BPartBChainConstructed β` — the Part-(B) chain of GWZ Proposition 6.6(B) without the
unconstructible presentation contract `Kakeya.Section6PartBData.Remark53Prop51`
 — is proved here from `Kakeya.KatzTaoEstimate β` alone
(`Kakeya.prop66BPartBChainConstructed_of_katzTaoEstimate`).  Composed with the chain's assembly
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_parentWindow_of_chainConstructed`, this gives the
project statement of Proposition 6.6(B) with the parent-window binder condition by 
(`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_parentWindow_of_katzTaoEstimate`), which is
exactly the proof term of the re-pinned `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`
(`Kakeya/DimensionThree/Plank/Prop66BClose.lean`).

The route is the one  (T5) and /§7 lay
out: the constructed Proposition-5.1 output
(`Kakeya/DimensionThree/Plank/Prop66BConstructedOuter.lean`),
the essentially distinct extraction of the presented outer family, the tree's inner pipeline on the
constructed inner family, the two master-scale readings of GWZ Lemma 6.1 already in the tree, and
GWZ Lemma 3.7 for the large-`a` regime the construction does not cover.  GWZ Lemma 6.1 is not
modified, no density hypothesis is assumed, and no statement is changed.
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody
open scoped NNReal Real ENNReal

noncomputable section

universe u v w

namespace Kakeya

set_option maxHeartbeats 2000000 in
-- three regimes, each instantiating a long telescope
/-- **The residue of the fine-ED chain of GWZ Proposition 6.6(B) is a theorem of `K_KT(β)`.**

`Kakeya.Prop66BPartBChainConstructed β` (`Kakeya/DimensionThree/Plank/Prop66BChainResidue.lean`),
at any pair of index universes, from `Kakeya.KatzTaoEstimate β` at any universe.  Neither
`Kakeya.FrostmanEstimate` nor the residue's third datum clause (GWZ Lemma 4.1(ii) on the coarse
fibres) is used.

The proof follows `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_masterScaleLemma61`
(`Kakeya/DimensionThree/Plank/GlobalPlankFactorizationEstimate.lean`) with the constructed split
`Kakeya.factoringAndMultPropGlobal_constructed` in place of `Kakeya.factoringAndMultPropGlobal`,
and one more regime:

* **`δ + 2a ≤ 1`, `b ≤ b₀`** — the outer application of GWZ Lemma 6.1 (`γ = 0`,
  `Kakeya.exists_outerMultiplicityBoundAtMasterScale` at `ε/12`), the inner one (`γ = 1`,
  `Kakeya.PlankEstimateAtMasterScaleWithDensity` at `ε/6`), and
  `Kakeya.combineGlobalFactorWithInnerLoss` with `Csplit = 1`, `Ccard = 2`, the `δ ^ (-(ε/12))`
  split
  loss folded into the outer factor;
* **`δ + 2a ≤ 1`, `b₀ < b`** — GWZ Lemma 6.9 (`ShadedPlank.multiplicity_le_of_isKatzTao_of_large'`)
  replaces the outer Lemma 6.1, exactly as in `Kakeya.globalCoarsePlankFallback`, run at `ε/2` and
  combined by `Kakeya.combineGlobalFactorFallback`;
* **`1 < δ + 2a`** — the constructed route needs `δ + 2a ≤ 1`
  (`Kakeya.Section6PartBData.hasThickenedFrostmanFibers`), but then `a > 1/4`, so
  `(a/b) ^ β ≥ 1/4` and GWZ Lemma 3.7
  (`Kakeya.KatzTaoEstimate.exists_threshold_multiplicity_bound_univ`
  at `ε/2`) already gives the bound.

Both master-scale readings of GWZ Lemma 6.1 are theorems of `K_KT(β)`
(`Kakeya/DimensionThree/Plank/MasterScaleLemma61.lean`); Lemma 6.1 itself is untouched. -/
theorem prop66BPartBChainConstructed_of_katzTaoEstimate {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate.{w} (EuclideanSpace ℝ (Fin 3)) β) :
    Prop66BPartBChainConstructed.{u, v} β := by
  classical
  have h61δ : PlankEstimateAtMasterScale.{0} β :=
    KatzTaoEstimate.plankEstimateAtMasterScale hβpos hβle hKKT.toTypeZero
  have h61δΔ : PlankEstimateAtMasterScaleWithDensity.{0} β :=
    KatzTaoEstimate.plankEstimateAtMasterScaleWithDensity hβpos hβle hKKT.toTypeZero
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by positivity
  have hε6 : (0 : ℝ) < ε / 6 := by positivity
  have hε12 : (0 : ℝ) < ε / 12 := by positivity
  have hε36 : (0 : ℝ) < ε / 36 := by positivity
  -- the outer application of GWZ Lemma 6.1 (`γ = 0`), for the small-`b` branch
  obtain ⟨ηₒ, hηₒ, b₀ₒ, hb₀ₒ, hOuter⟩ :=
    exists_outerMultiplicityBoundAtMasterScale.{0} h61δ (ε' := ε / 12) hε12
  -- the inner application of GWZ Lemma 6.1 (`γ = 1`), shared by both branches
  obtain ⟨ηᵢ, hηᵢ, b₀ᵢ, hb₀ᵢ, h61⟩ := h61δΔ (ε / 6) hε6
  -- the angle windows of GWZ Lemma 6.9, for the large-`b` fallback
  obtain ⟨Kw, hKwin⟩ := ShadedSlab.exists_numAngleWindows_le (ε := ε / 36) hε36
  -- the constructed split, in both regimes
  obtain ⟨Cinner, hCi1, hSplitFun⟩ := factoringAndMultPropGlobal_constructed.{u, v}
  obtain ⟨ηA, hηA, δA, hδA, hcfgA⟩ := hSplitFun ηₒ ηᵢ (ε / 12) hηₒ hηᵢ hε12 b₀ᵢ hb₀ᵢ
  obtain ⟨ηB, hηB, δB, hδB, hcfgB⟩ := hSplitFun (ε / 36) ηᵢ (ε / 12) hε36 hηᵢ hε12 b₀ᵢ hb₀ᵢ
  -- GWZ Lemma 3.7, for the large-`a` regime
  obtain ⟨ηC, hηC, δC, hδC, hKT37⟩ :=
    KatzTaoEstimate.exists_threshold_multiplicity_bound_univ.{u, w} hβpos.le hKKT (ε / 2) hε2
  -- absolute-constant thresholds
  obtain ⟨δ2, hδ2, hfun2⟩ := exists_threshold_le_rpow_neg (2 : ℝ≥0) one_le_two hε6
  obtain ⟨δI, hδI, hIfun⟩ := rpowConstAbsorb Cinner hCi1 zero_le_one hε2
  set Cout : ℝ≥0 := 196520 * Kw * (8 * b₀ₒ ^ 2)⁻¹ with hCout
  set Comb : ℝ≥0 := max 1 (1 * Cout * (2 : ℝ≥0) ^ β * Cinner) with hComb
  obtain ⟨δco, hδco, hcofun⟩ := rpowConstAbsorb Comb (le_max_left _ _) zero_le_one hε2
  obtain ⟨δ4, hδ4, hfun4⟩ := exists_threshold_le_rpow_neg (4 : ℝ≥0) (by norm_num) hε2
  set η : ℝ := min (min ηA ηB) ηC with hη_def
  have hη : 0 < η := lt_min (lt_min hηA hηB) hηC
  have hηA' : η ≤ ηA := (min_le_left _ _).trans (min_le_left _ _)
  have hηB' : η ≤ ηB := (min_le_left _ _).trans (min_le_right _ _)
  have hηC' : η ≤ ηC := min_le_right _ _
  refine ⟨η, hη, min (min (min δA δB) (min δC δ2)) (min (min δI δco) (min δ4 (1 / 2))),
    lt_min (lt_min (lt_min hδA hδB) (lt_min hδC hδ2))
      (lt_min (lt_min hδI hδco) (lt_min hδ4 (by norm_num))), b₀ᵢ, hb₀ᵢ, ?_⟩
  intro ι q δ hδ0 T hδ hball hEDq hfull ρ a b hab hb1 κ r R m Cfib CF C₀ K hC₀ hCF hCfib hK
    hδρ hρa hδb₀ᵢa D hcfne hdimK _hdens
  -- unwind the threshold
  have hδδA : δ ≤ δA :=
    hδ.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hδδB : δ ≤ δB :=
    hδ.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hδδC : δ ≤ δC :=
    hδ.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
  have hδδ2 : δ ≤ δ2 :=
    hδ.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _))
  have hδδI : δ ≤ δI :=
    hδ.trans (((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hδδco : δ ≤ δco :=
    hδ.trans (((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hδδ4 : δ ≤ δ4 :=
    hδ.trans (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
  have hδhalf : δ ≤ 1 / 2 :=
    hδ.trans (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _))
  -- the scales
  have hδa : δ ≤ a := hδρ.trans hρa
  have ha0 : 0 < a := lt_of_lt_of_le hδ0 hδa
  have hδ1 : δ ≤ 1 := hδa.trans (hab.trans hb1)
  have hδne : δ ≠ 0 := hδ0.ne'
  have hδE0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδne
  have hδEtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hpow : ∀ {s t : ℝ}, s ≤ t → (δ : ℝ≥0) ^ (-s) ≤ δ ^ (-t) :=
    fun hst => NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (neg_le_neg hst)
  have hpow' : ∀ {s t : ℝ}, s ≤ t → (δ : ℝ≥0) ^ t ≤ δ ^ s :=
    fun hst => NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hst
  set Δ₀ : ENNReal := maxDensity q (fun i => (T i).toConvexSpaceBody) with hΔ₀
  have hthrI : (Cinner : ENNReal) ≤ (δ : ENNReal) ^ (-(ε / 2)) := by
    simpa using hIfun δ hδ0 hδδI
  have hcardcast : ∀ {nts nj nq : ℕ},
      (nts : ENNReal) * (nj : ENNReal) ≤ (2 : ENNReal) * (nq : ENNReal) →
      (nts : ENNReal) * (nj : ENNReal) ≤ ((2 : ℝ≥0) : ENNReal) * (nq : ENNReal) := by
    intro nts nj nq h
    rw [ENNReal.coe_ofNat]
    exact h
  by_cases hsmall : δ + 2 * a ≤ 1
  · by_cases hbcase : b ≤ b₀ₒ
    · -- ============ small `b`: both applications of GWZ Lemma 6.1 ============
      obtain ⟨ts, W, hts_ne, hts_sub, hWed, hWball, hWfull, hWKT, a', b', ha'b', hb'1, ιj, qj, Pj,
        ha'pos, hδa', hb'thr, hratio, hPjball, hPjed, hjfull, hmaxd, hslab1, hcardle, hsplitineq⟩ :=
        hcfgA q hδ0 T hδδA hball hEDq ((hpow' hηA').trans hfull) ρ a b hab hb1 hδρ hρa hsmall
          hδb₀ᵢa r R m Cfib CF C₀ K (hC₀.trans (hpow hηA')) (hCF.trans (hpow hηA'))
          (hCfib.trans (hpow hηA')) (hK.trans (hpow hηA')) D hcfne hdimK
      have hW : ShadedBody.multiplicity ts (fun j => (W j).toShadedBody) ≤
          (δ : ENNReal) ^ (-(ε / 12)) * (ts.card : ENNReal) ^ β :=
        hOuter ts hab hb1 W hδ0 hδa hbcase hWball hWed hWfull hWKT
      have hinner := h61 qj ha'b' hb'1 Pj hδ0 hδa' hb'thr hPjball hPjed hjfull
        1 zero_le_one le_rfl hslab1
      have hTj := innerBoundTransfer hβle hratio hmaxd hinner
      have hW' : (δ : ENNReal) ^ (-(ε / 12))
            * ShadedBody.multiplicity ts (fun j => (W j).toShadedBody)
          ≤ (δ : ENNReal) ^ (-(ε / 6)) * (ts.card : ENNReal) ^ β := by
        calc (δ : ENNReal) ^ (-(ε / 12)) * ShadedBody.multiplicity ts (fun j => (W j).toShadedBody)
            ≤ (δ : ENNReal) ^ (-(ε / 12))
                * ((δ : ENNReal) ^ (-(ε / 12)) * (ts.card : ENNReal) ^ β) :=
              mul_le_mul' le_rfl hW
          _ = (δ : ENNReal) ^ (-(ε / 6)) * (ts.card : ENNReal) ^ β := by
              rw [← mul_assoc, ← ENNReal.rpow_add _ _ hδE0 hδEtop]
              congr 2; ring
      have hsplit' : ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
          ((1 : ℝ≥0) : ENNReal)
            * ((δ : ENNReal) ^ (-(ε / 12))
              * ShadedBody.multiplicity ts (fun j => (W j).toShadedBody))
            * ShadedBody.multiplicity qj (fun i => (Pj i).toShadedBody) := by
        rw [ENNReal.coe_one, one_mul]
        exact hsplitineq
      have hthr : ((1 : ℝ≥0) : ENNReal) * ((2 : ℝ≥0) : ENNReal) ^ β
          ≤ (δ : ENNReal) ^ (-(ε / 6)) := by
        rw [ENNReal.coe_one, one_mul]
        calc ((2 : ℝ≥0) : ENNReal) ^ β ≤ ((2 : ℝ≥0) : ENNReal) ^ (1 : ℝ) :=
              ENNReal.rpow_le_rpow_of_exponent_le (by exact_mod_cast one_le_two) hβle
          _ = ((2 : ℝ≥0) : ENNReal) := ENNReal.rpow_one _
          _ ≤ (δ : ENNReal) ^ (-(ε / 6)) := by
              rw [← ENNReal.coe_rpow_of_ne_zero hδne]
              exact_mod_cast hfun2 δ hδ0 hδδ2
      exact combineGlobalFactorWithInnerLoss hβpos hβle hδ0 hδ1 (Csplit := 1) (Ccard := 2)
        le_rfl one_le_two hCi1 hW' hTj hsplit' (hcardcast hcardle) hthr hthrI
    · -- ============ large `b`: GWZ Lemma 6.9 replaces the outer Lemma 6.1 ============
      obtain ⟨ts, W, hts_ne, hts_sub, -, hWball, hWfull, hWKT, a', b', ha'b', hb'1, ιj, qj, Pj,
        ha'pos, hδa', hb'thr, hratio, hPjball, hPjed, hjfull, hmaxd, hslab1, hcardle, hsplitineq⟩ :=
        hcfgB q hδ0 T hδδB hball hEDq ((hpow' hηB').trans hfull) ρ a b hab hb1 hδρ hρa hsmall
          hδb₀ᵢa r R m Cfib CF C₀ K (hC₀.trans (hpow hηB')) (hCF.trans (hpow hηB'))
          (hCfib.trans (hpow hηB')) (hK.trans (hpow hηB')) D hcfne hdimK
      have hbb₀ : b₀ₒ ≤ b := (not_le.mp hbcase).le
      have hWbound := ShadedPlank.multiplicity_le_of_isKatzTao_of_large' (ε := ε / 36) (η := ε / 36)
        hb₀ₒ hKwin ts W ha0 hbb₀ hts_ne hδ0 hδa hε36.le hε36 hWKT hWfull
      have hexp : -(ε / 36 + 2 * (ε / 36)) = -(ε / 12) := by ring
      rw [hexp] at hWbound
      have hW' : (δ : ENNReal) ^ (-(ε / 12))
            * ShadedBody.multiplicity ts (fun j => (W j).toShadedBody)
          ≤ (Cout : ENNReal) * (δ : ENNReal) ^ (-((ε / 2) / 3)) := by
        calc (δ : ENNReal) ^ (-(ε / 12)) * ShadedBody.multiplicity ts (fun j => (W j).toShadedBody)
            ≤ (δ : ENNReal) ^ (-(ε / 12)) * ((Cout : ENNReal) * (δ : ENNReal) ^ (-(ε / 12))) :=
              mul_le_mul' le_rfl hWbound
          _ = (Cout : ENNReal) * ((δ : ENNReal) ^ (-(ε / 12)) * (δ : ENNReal) ^ (-(ε / 12))) := by
              ring
          _ = (Cout : ENNReal) * (δ : ENNReal) ^ (-((ε / 2) / 3)) := by
              rw [← ENNReal.rpow_add _ _ hδE0 hδEtop]
              congr 2; ring
      have hinner := h61 qj ha'b' hb'1 Pj hδ0 hδa' hb'thr hPjball hPjed hjfull
        1 zero_le_one le_rfl hslab1
      have hTj := innerBoundTransfer hβle hratio hmaxd hinner
      have hTj' : ShadedBody.multiplicity qj (fun i => (Pj i).toShadedBody) ≤
          (δ : ENNReal) ^ (-((ε / 2) / 3)) * ((Cinner : ENNReal) * Δ₀) ^ (1 - β)
            * ((a : ENNReal) / (b : ENNReal)) ^ β * (qj.card : ENNReal) ^ β := by
        rw [show -((ε / 2) / 3) = -(ε / 6) by ring]
        exact hTj
      have hsplit' : ShadedBody.multiplicity q (fun i => (T i).toShadedBody) ≤
          ((1 : ℝ≥0) : ENNReal)
            * ((δ : ENNReal) ^ (-(ε / 12))
              * ShadedBody.multiplicity ts (fun j => (W j).toShadedBody))
            * ShadedBody.multiplicity qj (fun i => (Pj i).toShadedBody) := by
        rw [ENNReal.coe_one, one_mul]
        exact hsplitineq
      have hcomb := combineGlobalFactorFallback hβpos hβle hε2 hδ0 hδ1 hδa
        (Csplit := 1) (Ccard := 2) (Cout := Cout) le_rfl one_le_two
        (Finset.card_ne_zero.mpr hts_ne) hW' hTj' hsplit' (hcardcast hcardle)
      -- absorb the inner density constant and the fixed constants
      have h_nonneg_1mβ : 0 ≤ 1 - β := by linarith
      have hCinner_rpow : (Cinner : ENNReal) ^ (1 - β) ≤ (Cinner : ENNReal) := by
        calc (Cinner : ENNReal) ^ (1 - β) ≤ (Cinner : ENNReal) ^ (1 : ℝ) :=
              ENNReal.rpow_le_rpow_of_exponent_le (by exact_mod_cast hCi1) (by linarith)
          _ = (Cinner : ENNReal) := ENNReal.rpow_one _
      have hCinner_mul : ((Cinner : ENNReal) * Δ₀) ^ (1 - β)
          ≤ (Cinner : ENNReal) * Δ₀ ^ (1 - β) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ h_nonneg_1mβ]
        exact mul_le_mul' hCinner_rpow le_rfl
      have hCombC : ((1 * Cout * (2 : ℝ≥0) ^ β : ℝ≥0) : ENNReal) * (Cinner : ENNReal)
          ≤ (δ : ENNReal) ^ (-(ε / 2)) := by
        calc ((1 * Cout * (2 : ℝ≥0) ^ β : ℝ≥0) : ENNReal) * (Cinner : ENNReal)
            = ((1 * Cout * (2 : ℝ≥0) ^ β * Cinner : ℝ≥0) : ENNReal) := (ENNReal.coe_mul _ _).symm
          _ ≤ (Comb : ENNReal) := by exact_mod_cast (le_max_right _ _ : _ ≤ Comb)
          _ = (Comb : ENNReal) ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
          _ ≤ (δ : ENNReal) ^ (-(ε / 2)) := hcofun δ hδ0 hδδco
      have hsplitδ : (δ : ENNReal) ^ (-ε)
          = (δ : ENNReal) ^ (-(ε / 2)) * (δ : ENNReal) ^ (-(ε / 2)) := by
        rw [← ENNReal.rpow_add _ _ hδE0 hδEtop]; congr 1; ring
      calc ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
          ≤ ((1 * Cout * (2 : ℝ≥0) ^ β : ℝ≥0) : ENNReal)
              * ((δ : ENNReal) ^ (-(ε / 2)) * ((Cinner : ENNReal) * Δ₀) ^ (1 - β)
                * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β) := hcomb
        _ ≤ ((1 * Cout * (2 : ℝ≥0) ^ β : ℝ≥0) : ENNReal)
              * ((δ : ENNReal) ^ (-(ε / 2)) * ((Cinner : ENNReal) * Δ₀ ^ (1 - β))
                * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β) := by
            gcongr
        _ = (((1 * Cout * (2 : ℝ≥0) ^ β : ℝ≥0) : ENNReal) * (Cinner : ENNReal))
              * (δ : ENNReal) ^ (-(ε / 2))
              * (Δ₀ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β) := by
            ring
        _ ≤ (δ : ENNReal) ^ (-(ε / 2)) * (δ : ENNReal) ^ (-(ε / 2))
              * (Δ₀ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β) := by
            gcongr
        _ = (δ : ENNReal) ^ (-ε) * Δ₀ ^ (1 - β)
              * ((a : ENNReal) / (b : ENNReal)) ^ β * (q.card : ENNReal) ^ β := by
            rw [hsplitδ]; ring
  · -- ============ large `a`: GWZ Lemma 3.7 directly, `(a/b)^β ≥ 1/4` ============
    have hlt : 1 < δ + 2 * a := not_le.mp hsmall
    set c4 : ℝ≥0 := (4 : ℝ≥0)⁻¹ with hc4
    have ha14 : c4 ≤ a := by
      have h1 := NNReal.coe_lt_coe.mpr hlt
      have h2 := NNReal.coe_le_coe.mpr hδhalf
      rw [← NNReal.coe_le_coe, hc4]
      push_cast at h1 h2 ⊢
      linarith
    have hab14 : (c4 : ENNReal) ≤ (a : ENNReal) / (b : ENNReal) := by
      calc (c4 : ENNReal) ≤ (a : ENNReal) := by exact_mod_cast ha14
        _ = (a : ENNReal) / 1 := (div_one _).symm
        _ ≤ (a : ENNReal) / (b : ENNReal) := ENNReal.div_le_div le_rfl (by exact_mod_cast hb1)
    have hc41 : (c4 : ENNReal) ≤ 1 := by
      rw [hc4]
      exact_mod_cast (inv_le_one_of_one_le₀ (by norm_num : (1 : ℝ≥0) ≤ 4))
    have hratioβ : (c4 : ENNReal) ≤ ((a : ENNReal) / (b : ENNReal)) ^ β := by
      calc (c4 : ENNReal) = (c4 : ENNReal) ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
        _ ≤ (c4 : ENNReal) ^ β := ENNReal.rpow_le_rpow_of_exponent_ge hc41 hβle
        _ ≤ ((a : ENNReal) / (b : ENNReal)) ^ β := ENNReal.rpow_le_rpow hab14 hβpos.le
    have h4 : (δ : ENNReal) ^ (ε / 2) ≤ (c4 : ENNReal) := by
      refine PartBLoss.rpow_le_inv_of_le_rpow_neg (L := 4) (by norm_num) ?_
      rw [← ENNReal.coe_rpow_of_ne_zero hδne]
      exact_mod_cast hfun4 δ hδ0 hδδ4
    have h37 := hKT37 δ hδ0 hδδC q T hball ((hpow' hηC').trans hfull)
    have hsplitδ : (δ : ENNReal) ^ (-(ε / 2))
        = (δ : ENNReal) ^ (-ε) * (δ : ENNReal) ^ (ε / 2) := by
      rw [← ENNReal.rpow_add _ _ hδE0 hδEtop]; congr 1; ring
    calc ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
        ≤ (δ : ENNReal) ^ (-(ε / 2)) * Δ₀ ^ (1 - β) * (q.card : ENNReal) ^ β := h37
      _ = (δ : ENNReal) ^ (-ε) * Δ₀ ^ (1 - β) * (δ : ENNReal) ^ (ε / 2)
            * (q.card : ENNReal) ^ β := by rw [hsplitδ]; ring
      _ ≤ (δ : ENNReal) ^ (-ε) * Δ₀ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ β
            * (q.card : ENNReal) ^ β := by
          gcongr
          exact h4.trans hratioβ


/-- **GWZ Proposition 6.6(B), in the parent-window form of, from `K_KT(β)`.**

The pinned statement `Kakeya.Prop66BScale.statement_of_universal_prop66B_essDistinct_parentWindow`,
i.e. the project statement `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` with the condition
binder `∀ k ∈ PS.parent, (PS.parentTube k).carrier ⊆ Metric.closedBall 0 1`, proved from exactly the
hypotheses of that theorem (`hKF` is not needed).  This is the proof of the target, in
`Kakeya/DimensionThree/Plank/Prop66BClose.lean`:
`fun ε hε => tubeMultiplicityOfGlobalPlankFactorisation_parentWindow_of_katzTaoEstimate hβpos hβle
hKKT hε₂0 hε₂1 ε hε`. -/
theorem tubeMultiplicityOfGlobalPlankFactorisation_parentWindow_of_katzTaoEstimate {β : ℝ}
    (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate.{w} (EuclideanSpace ℝ (Fin 3)) β)
    {ε₂ : ℝ} (hε₂0 : 0 < ε₂) (hε₂1 : ε₂ ≤ 1) :
    Prop66BScale.statement_of_universal_prop66B_essDistinct_parentWindow.{u} β ε₂ :=
  tubeMultiplicityOfGlobalPlankFactorisation_parentWindow_of_chainConstructed hβpos hβle hε₂0 hε₂1
    (prop66BPartBChainConstructed_of_katzTaoEstimate.{u, u, w} hβpos hβle hKKT)

end Kakeya

end
