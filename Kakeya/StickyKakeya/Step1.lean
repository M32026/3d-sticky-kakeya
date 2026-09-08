/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Sticky
public import Kakeya.StickyKakeya.CrossScale
public import Kakeya.StickyKakeya.Absorption
public import Kakeya.StickyKakeya.Constants
public import Kakeya.StickyKakeya.Counting
public import Kakeya.StickyKakeya.Fullness
public import Kakeya.StickyKakeya.Lemma75

/-!
# Theorem 7.3(A) ⇒ (B), Step 1: the translated Frostman family

`exists_frostman_translation_family` (paper `section7.tex` L188): apply GWZ Lemma 7.5 to the
Katz–Tao family `(𝕋, Y)`, producing a finite translation set and a refined family that is uniform,
fullness-preserving and Frostman at every scale with error `δ^{-η₁}`.  This is where the
Definition 2.1 data demanded by `Kakeya.StickyKakeya.subStickyFrostmanLemma` is assembled.
-/

@[expose] public section

open MeasureTheory
open Tube

namespace Kakeya

open MultiScaleFac

namespace StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

section stickyKatzTaoOfStickyFrostman

set_option maxHeartbeats 2000000 in
-- This lemma carries a large context (six E6/E7 threshold hypotheses, SSF bundle, and the
-- packing-algebra `hED` inequality), pushing several `nlinarith`/`ring`/`positivity` steps
-- past the default heartbeat budget.
lemma exists_frostman_translation_family
    (ε : ℝ)
    (η₁ : ℝ) (_hη₁_pos : 0 < η₁)
    (η_full : ℝ) (_hη_full_le : η_full ≤ η₁)
    (η_KT : ℝ) (hη_KT_pos : 0 < η_KT)
    {δ : NNReal} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hδ_le_quarter : (δ : ℝ) ≤
        (1 / 8 : ℝ) ^ (gridLen (Module.finrank ℝ E) η₁ ε))
    (_hη_KT_lt : η_KT <
        (1 / ((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ)) ^ 2)
    (hδ_le_inner : δ ≤ ssfδ₀ (E := E) η₁ ε)
    (_hδ_thresh : (δ : ℝ) ^ (sfBeta (E := E) η₁)
        * ((2 * (Tube.overlapConstBO (Module.finrank ℝ E) : NNReal)) : ℝ) ^ 3
        * (2 * ((2 * (Tube.overlapConstBO (Module.finrank ℝ E) : NNReal)) : ℝ) ^ 3)
            ^ (⌈Real.log (Real.log (1 / (δ : ℝ)))⌉₊) ≤ 1)
    (_hδ_ratio_thresh : (δ : ℝ) ^ (sfBeta (E := E) η₁ / 2)
        ≤ ((Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
              / (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)) ^ 2
            / ((2 * (Tube.overlapConstBO (Module.finrank ℝ E) : NNReal)) : ℝ)
                ^ (2 * (Module.finrank ℝ E - 1)))
    (_hMout_large : ((Module.finrank ℝ E : ℝ) - 1) / (⌈Real.log (Real.log (1 / (δ : ℝ)))⌉₊ : ℝ)
        ≤ sfBeta (E := E) η₁ / 4)
    (h_dmax_absorb :
        (↑(Tube.volume_le.C (Module.finrank ℝ E)) / ↑(Tube.le_volume.c (Module.finrank ℝ E))
            * ↑(2 * (Tube.overlapConstBOTight (Module.finrank ℝ E) : NNReal))
            * (2 : ENNReal) ^ Module.finrank ℝ E) * ENNReal.ofReal ((δ : ℝ) ^ (-η_KT))
          ≤ ENNReal.ofReal ((δ : ℝ) ^
              (-((1 / ((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ)) ^ 2))))
    (h_dmax_cross_absorb :
        (↑(crossScaleConst (Module.finrank ℝ E)
              * (2 * (Tube.overlapConstBOTight (Module.finrank ℝ E) : NNReal))) : ENNReal)
            * ENNReal.ofReal ((δ : ℝ) ^ (-(2 * η_KT)))
          ≤ ENNReal.ofReal ((δ : ℝ) ^
              (-((1 / ((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ)) ^ 2))))
    {ι : Type} (s : Finset ι) (hs_nonempty : s.Nonempty)
    (V : ι → ShadedTube δ E)
    (hT_in_unit : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (h_pertube : ∀ i ∈ s, ENNReal.ofReal ((δ : ℝ) ^ η_full / 2)
        * MeasureTheory.volume (V i).carrier ≤ MeasureTheory.volume (V i).shade)
    (h_kpoly : ∀ (B : ℕ),
        (B : ℝ) ≤ (((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 : ℕ) : ℝ)
            * (qCardConst (Module.finrank ℝ E) (gridLen (Module.finrank ℝ E) η₁ ε)
                  (cnEff (Module.finrank ℝ E))
                  (prodConst (Module.finrank ℝ E)
                    (gridLen (Module.finrank ℝ E) η₁ ε)) *
                (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
                  / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) + 1))
            * (δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1 + η_KT + 1)) →
        (δ : ℝ) ^ η₁ * ((Nat.log 2 B + 1 : ℕ) : ℝ)
              ^ (2 * ⌈Real.log (Real.log (1 / (δ : ℝ)))⌉₊)
          ≤ (δ : ℝ) ^ η_full / 2)
    (hKT : ConvexSpaceBody.IsKatzTao s (fun i => (V i).toConvexSpaceBody)
        (ENNReal.ofReal ((δ : ℝ) ^ (-η_KT))))
    (hKT_cover : ∀ k : ℕ, k ≤ gridLen (Module.finrank ℝ E) η₁ ε →
        HasNodeCoverAt s (fun i => (V i).toTube)
          (δ ^ ((k : ℝ) / ((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ)))
          ((δ : ℝ) ^ (-(η_KT / (3 * (Module.finrank ℝ E : ℝ)))))
          (ENNReal.ofReal ((δ : ℝ) ^ (-η_KT)))) :
      ∃ (R : Finset E) (s_ref : Finset (ι × E)) (V_ref : ι × E → ShadedTube δ E),
        R.Nonempty ∧ s_ref.Nonempty ∧ (∀ p ∈ s_ref, p.1 ∈ s ∧ p.2 ∈ R) ∧
        (R.card : ℝ) * (s.card : ℝ) *
              (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) *
            (δ : ℝ) ^ ((Module.finrank ℝ E : ℝ) - 1)
          ≤ (641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
              * edRefineC (E := E) * (δ : ℝ) ^ (-2 * η_KT)
              * (e2Const (Module.finrank ℝ E) η₁ ε δ * (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
                  * (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
                        / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
                      + (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
                        / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)))
              * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1)
                  ^ (gridLen (Module.finrank ℝ E) η₁ ε - 1) ∧
        (∀ p, (V_ref p).toTube = ((V p.1).toTube).translate p.2) ∧
        (∀ p, (V_ref p).shade ⊆ ((V p.1).translate p.2).shade) ∧
        (∀ p ∈ s_ref, (V_ref p).carrier ⊆ Metric.closedBall (0 : E)
            (((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ) + 1)) ∧
        (ENNReal.ofReal ((δ : ℝ) ^ η₁) ≤
            ShadedBody.fullness' s_ref (fun p => (V_ref p).toShadedBody)) ∧
        (ENNReal.ofReal ((δ : ℝ) ^ η_full / 2) ≤
            ShadedBody.fullness' s_ref (fun p => (V_ref p).toShadedBody)) ∧
        (∀ p ∈ s_ref, ENNReal.ofReal ((δ : ℝ) ^ η_full / 2)
            * MeasureTheory.volume (V_ref p).carrier
          ≤ MeasureTheory.volume (V_ref p).shade) ∧
        IsFrostmanAtEveryScale (E := E) s_ref
          (fun p => (V_ref p).toTube)
          (ENNReal.ofReal ((δ : ℝ) ^
            (-(2 * ((Module.finrank ℝ E : ℝ) + 3)
                * (1 / ((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ)))))) ∧
        Kakeya.maxDensity s_ref (fun p => ((V_ref p).toTube).toConvexSpaceBody)
          ≤ ENNReal.ofReal ((δ : ℝ) ^
            (-(((Module.finrank ℝ E : ℝ) + 3)
                * (1 / ((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ))))) := by
    classical
    set n : ℕ := Module.finrank ℝ E with hn_def
    have hn_pos : 0 < n := Module.finrank_pos (R := ℝ) (M := E)
    have hδ_pos_real : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
    have hδ_lt_one_real : (δ : ℝ) < 1 := by exact_mod_cast hδ_lt_one
    set M_inner : ℕ := gridLen n η₁ ε with hM_inner_def
    set ε_inner : ℝ := 1 / (M_inner : ℝ) with hε_inner_def
    set ρ_inner : Fin (M_inner + 1) → NNReal :=
      fun k => δ ^ ((k.val : ℝ) / (M_inner : ℝ)) with hρ_inner_def
    have hM_inner_pos : 1 ≤ M_inner := by
      rw [hM_inner_def]; exact one_le_gridLen _ _ _
    have hM_inner_pos_real : (0 : ℝ) < (M_inner : ℝ) := by
      have h1 : (1 : ℝ) ≤ (M_inner : ℝ) := by exact_mod_cast hM_inner_pos
      linarith
    have hM_inner_ne_zero : (M_inner : ℝ) ≠ 0 := hM_inner_pos_real.ne'
    have hε_inner_pos : 0 < ε_inner := by
      rw [hε_inner_def]; exact one_div_pos.mpr hM_inner_pos_real
    have hρ_inner_zero : ρ_inner 0 = 1 := by
      change (δ : NNReal) ^ (((0 : Fin (M_inner + 1)).val : ℝ) / (M_inner : ℝ)) = 1
      simp
    have hρ_inner_last : ρ_inner (Fin.last M_inner) = δ := by
      change (δ : NNReal) ^ (((Fin.last M_inner).val : ℝ) / (M_inner : ℝ)) = δ
      rw [Fin.val_last, div_self hM_inner_ne_zero, NNReal.rpow_one]
    have hρ_inner_anti : StrictAnti ρ_inner := by
      intro k₁ k₂ hk
      change (δ : NNReal) ^ ((k₂.val : ℝ) / (M_inner : ℝ))
          < (δ : NNReal) ^ ((k₁.val : ℝ) / (M_inner : ℝ))
      have h_exp : ((k₁.val : ℝ) / (M_inner : ℝ))
          < ((k₂.val : ℝ) / (M_inner : ℝ)) := by
        apply div_lt_div_of_pos_right _ hM_inner_pos_real
        exact_mod_cast hk
      exact NNReal.rpow_lt_rpow_of_exponent_gt hδ_pos hδ_lt_one h_exp
    have hM_inner_form : M_inner = gridLen (Module.finrank ℝ E) η₁ ε := by
      rw [hM_inner_def, hn_def]
    have hδ_le_quarter_M : (δ : ℝ) ≤ (1/8 : ℝ) ^ M_inner := hδ_le_quarter
    have hgap_Minner : (δ : ℝ) ^ ((1 : ℝ) / (M_inner : ℝ)) ≤ 1 / 2 := by
      have h_step : (δ : ℝ) ^ ((1 : ℝ) / (M_inner : ℝ))
          ≤ ((1/8 : ℝ) ^ M_inner) ^ ((1 : ℝ) / (M_inner : ℝ)) := by
        apply Real.rpow_le_rpow hδ_pos_real.le hδ_le_quarter_M; positivity
      have h_eq : ((1/8 : ℝ) ^ M_inner) ^ ((1 : ℝ) / (M_inner : ℝ)) = (1/8 : ℝ) := by
        rw [← Real.rpow_natCast ((1/8 : ℝ)) M_inner,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1/8),
            mul_one_div, div_self hM_inner_ne_zero, Real.rpow_one]
      linarith [h_eq ▸ h_step]
    obtain ⟨s₁, hs₁_sub, hs₁_inj, hs₁_ne_of, hs₁_cover⟩ :=
      exists_carrier_injOn_cover s (fun i => ((V i).toTube).carrier)
    have hs₁_ne : s₁.Nonempty := hs₁_ne_of hs_nonempty
    have hs₁_B1 : ∀ ⦃i⦄, i ∈ s₁ → ((V i).toTube).carrier ⊆ Metric.closedBall (0 : E) 1 :=
      fun i hi => hT_in_unit i (hs₁_sub hi)
    have hD_leaf : Kakeya.maxDensity s₁ (fun i => ((V i).toTube).toConvexSpaceBody)
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η_KT)) := by
      have hKT_at_δ : ConvexSpaceBody.IsKatzTao s
          (fun i => (Tube.rescale ((V i).toTube) (δ : NNReal)).toConvexSpaceBody)
          (ENNReal.ofReal ((δ : ℝ) ^ (-η_KT))) :=
        by
          simpa [Tube.toConvexSpaceBody_rescale_self] using hKT
      have hmax_s : Kakeya.maxDensity s
          (fun i => (Tube.rescale ((V i).toTube) (δ : NNReal)).toConvexSpaceBody)
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η_KT)) := hKT_at_δ
      have h_rescale_eq : (fun (i : ι) =>
            (Tube.rescale ((V i).toTube) (δ : NNReal)).toConvexSpaceBody)
          = (fun (i : ι) => ((V i).toTube).toConvexSpaceBody) :=
    by
        funext i
        apply ConvexSpaceBody.ext
        dsimp [Tube.rescale]
        calc
          (Tube.mk' (δ : NNReal) ((V i).toTube).dist_eq_one).carrier
              = ⋃ z ∈ segment ℝ ((V i).toTube).x ((V i).toTube).y,
              Metric.closedBall z (δ : ℝ) := rfl
          _ = ((V i).toTube).carrier := ((V i).toTube).carrier_eq.symm
      have hmax_s' : Kakeya.maxDensity s (fun i => ((V i).toTube).toConvexSpaceBody)
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η_KT)) := by
        simpa [h_rescale_eq] using hmax_s
      exact le_trans
          (Kakeya.maxDensity_mono (fun i => ((V i).toTube).toConvexSpaceBody) hs₁_sub) hmax_s'
    obtain ⟨s₂, hs₂_sub₁, hs₂_ED, _h_unif, hs₂_ne, h_card_s₂, h_hierarchy⟩ :=
      Tube.refineToEssDistinctUniform hδ_pos hδ_lt_one s₁ (fun i => (V i).toTube)
        M_inner hM_inner_pos hgap_Minner hs₁_B1 hs₁_ne
        (D := ENNReal.ofReal ((δ : ℝ) ^ (-η_KT))) (by simp) hD_leaf
    have hs₂_sub : s₂ ⊆ s := hs₂_sub₁.trans hs₁_sub
    have hT_s₂ : ∀ i ∈ s₂, ((V i).toTube).carrier ⊆ Metric.closedBall (0 : E) 1 :=
      fun i hi => hT_in_unit i (hs₂_sub hi)
    have hcover_s₂ : ∀ k : ℕ, k ≤ M_inner →
        HasNodeCoverAt s₂ (fun i => (V i).toTube) (δ ^ ((k : ℝ) / (M_inner : ℝ)))
          ((δ : ℝ) ^ (-(η_KT / (3 * (n : ℝ)))))
          (ENNReal.ofReal ((δ : ℝ) ^ (-η_KT))) := by
      intro k hk
      obtain ⟨r, Q, W, hρr, hr1, hratio, hQcov, hQdens⟩ := hKT_cover k hk
      exact ⟨r, Q, W, hρr, hr1, hratio, fun i hi => hQcov i (hs₂_sub hi), hQdens⟩
    have hD_leaf_s₂ : Kakeya.maxDensity s₂ (fun i => ((V i).toTube).toConvexSpaceBody)
        ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η_KT)) :=
      le_trans (Kakeya.maxDensity_mono (fun i => ((V i).toTube).toConvexSpaceBody) hs₂_sub₁)
        hD_leaf
    set C_uniform : NNReal := 2 * (Tube.overlapConstBOTight (Module.finrank ℝ E) : NNReal)
      with hC_uniform_def
    obtain ⟨h_uni, pmap, h_branching, h_count_bundle, h_pmap, h_scale_count,
      N₂_band, hN₂_band_pos, hN₂_band_child, hN₂_band_child_le, hN₂_band_prod⟩ := h_hierarchy
    have h_count : ∀ k : Fin M_inner,
        ((h_uni k.castSucc).parent.card : ℝ) ≤
          (641 : ℝ) ^ (2 * Module.finrank ℝ E)
            * ((4 : ℝ) / (ρ_inner k.castSucc : ℝ)) ^ (2 * Module.finrank ℝ E) := by
      intro k
      have htemp := h_count_bundle k.castSucc (by exact k.isLt)
      simpa [hρ_inner_def, Fin.val_castSucc, NNReal.coe_rpow] using htemp
    have h_ratio : ∀ k : Fin M_inner,
        (δ : ℝ) ^ ε_inner ≤ (ρ_inner k.succ : ℝ) / (ρ_inner k.castSucc : ℝ) := by
      intro k
      have hδ_pos' : (0 : ℝ) < (δ : ℝ) := hδ_pos_real
      have h_ratio_eq : (ρ_inner k.succ : ℝ) / (ρ_inner k.castSucc : ℝ)
          = (δ : ℝ) ^ ((1 : ℝ) / (M_inner : ℝ)) := by
        change ((δ : NNReal) ^ ((k.succ.val : ℝ) / (M_inner : ℝ)) : ℝ) /
              ((δ : NNReal) ^ ((k.castSucc.val : ℝ) / (M_inner : ℝ)) : ℝ)
            = (δ : ℝ) ^ ((1 : ℝ) / (M_inner : ℝ))
        simp only [Fin.val_succ, Fin.val_castSucc]
        rw [← Real.rpow_sub hδ_pos']
        congr 1
        push_cast
        field_simp
        ring
      rw [h_ratio_eq]
    have hN₂_bracket : ∀ k : Fin M_inner,
        ∀ j ∈ (h_uni k.castSucc).parent,
          ((N₂_band k.val : ℕ) : ℝ) ≤ 2 * ((Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
              / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)) *
            (((h_uni k.succ).parent.filter (fun i : ι =>
              ((h_uni k.succ).parentTube i).toConvexSpaceBody ≤
                ((h_uni k.castSucc).parentTube j).toConvexSpaceBody)).card : ℝ) := by
      intro k j hj
      refine le_trans (hN₂_band_child k j hj) ?_
      have hcard_nn : (0 : ℝ) ≤ (((h_uni k.succ).parent.filter (fun i : ι =>
          ((h_uni k.succ).parentTube i).toConvexSpaceBody ≤
            ((h_uni k.castSucc).parentTube j).toConvexSpaceBody)).card : ℝ) :=
        Nat.cast_nonneg _
      have h := mul_le_mul_of_nonneg_right (one_le_packConst (E := E)) hcard_nn
      rwa [one_mul] at h
    have hN₂_prod : (s₂.card : ℝ)
        ≤ prodConst (Module.finrank ℝ E) M_inner
            * ∏ k : Fin M_inner, ((N₂_band k.val : ℕ) : ℝ) := by
      have h := hN₂_band_prod
      rw [prodConst]
      rw [Fin.prod_univ_eq_prod_range (fun i => ((N₂_band i : ℕ) : ℝ)) M_inner]
      exact h
    have h_delta_max : ∀ k : Fin M_inner,
        Kakeya.maxDensity
            ((h_uni k.succ).parent.image
              (fun j => (h_uni k.succ).parentTube j))
            (fun u : Tube (ρ_inner k.succ) E => u.toConvexSpaceBody)
          ≤ ENNReal.ofReal (((ρ_inner k.castSucc : ℝ) / (ρ_inner k.succ : ℝ)) ^ ε_inner) := by
      intro k
      have hδρ_k : δ ≤ ρ_inner k.succ := by
        have := hρ_inner_anti.antitone (Fin.le_last k.succ); rwa [hρ_inner_last] at this
      have hρ1_k : ρ_inner k.succ ≤ 1 := by
        have := hρ_inner_anti.antitone (Fin.zero_le k.succ); rwa [hρ_inner_zero] at this
      have hratio : (ρ_inner k.castSucc : ℝ) / (ρ_inner k.succ : ℝ)
          = (δ : ℝ) ^ (-(1 / (M_inner : ℝ))) := by
        simp only [hρ_inner_def, NNReal.coe_rpow]
        rw [← Real.rpow_sub hδ_pos_real]
        congr 1
        rw [Fin.val_succ, Fin.val_castSucc]
        push_cast
        ring
      have hRHS : ((ρ_inner k.castSucc : ℝ) / (ρ_inner k.succ : ℝ)) ^ ε_inner
          = (δ : ℝ) ^ (-((1 / (M_inner : ℝ)) ^ 2)) := by
        rw [hratio, ← Real.rpow_mul hδ_pos_real.le, hε_inner_def]
        congr 1
        ring
      rw [hRHS]
      rcases eq_or_lt_of_le (Nat.succ_le_of_lt k.isLt) with hlast | hlt
      · have hρδ : ρ_inner k.succ = δ := by
          have : ρ_inner k.succ = ρ_inner (Fin.last M_inner) := by
            congr 1
            exact Fin.ext (by simpa [Fin.val_succ, Fin.val_last] using hlast)
          rw [this, hρ_inner_last]
        have hKTρ_k : ConvexSpaceBody.IsKatzTao s₂
            (fun i => (Tube.rescale ((V i).toTube) (ρ_inner k.succ)).toConvexSpaceBody)
            (ENNReal.ofReal ((δ : ℝ) ^ (-η_KT))) := by
          rw [hρδ]
          have hKT_s₂ : ConvexSpaceBody.IsKatzTao s₂
              (fun i => ((V i).toTube).toConvexSpaceBody)
              (ENNReal.ofReal ((δ : ℝ) ^ (-η_KT))) := hD_leaf_s₂
          simpa [Tube.toConvexSpaceBody_rescale_self] using hKT_s₂
        refine le_trans (uniform_parent_maxDensity_le hδ_pos hδρ_k hρ1_k (h_uni k.succ)
          (h_branching k.succ) hKTρ_k) ?_
        exact h_dmax_absorb
      · have h2δ : 2 * δ ≤ ρ_inner k.succ := by
          have hexp : ((k.succ.val : ℝ) / (M_inner : ℝ))
              ≤ ((M_inner : ℝ) - 1) / (M_inner : ℝ) := by
            have hnum : ((k.succ.val : ℝ)) ≤ (M_inner : ℝ) - 1 := by
              have hlt' : (k.val : ℝ) + 1 + 1 ≤ (M_inner : ℝ) := by exact_mod_cast hlt
              simp only [Fin.val_succ]
              push_cast
              linarith
            gcongr
          have hstep : (δ : ℝ) ^ (((M_inner : ℝ) - 1) / (M_inner : ℝ))
              ≤ (δ : ℝ) ^ ((k.succ.val : ℝ) / (M_inner : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_ge hδ_pos_real hδ_lt_one_real.le hexp
          have hA_pos : (0 : ℝ) < (δ : ℝ) ^ (((M_inner : ℝ) - 1) / (M_inner : ℝ)) :=
            Real.rpow_pos_of_pos hδ_pos_real _
          have hsum_exp : ((M_inner : ℝ) - 1) / (M_inner : ℝ) + 1 / (M_inner : ℝ) = 1 := by
            have hcollect : ((M_inner : ℝ) - 1) / (M_inner : ℝ) + 1 / (M_inner : ℝ)
                = (M_inner : ℝ) / (M_inner : ℝ) := by ring
            rw [hcollect, div_self hM_inner_ne_zero]
          have hfac : (δ : ℝ) ^ (((M_inner : ℝ) - 1) / (M_inner : ℝ))
              * (δ : ℝ) ^ ((1 : ℝ) / (M_inner : ℝ)) = (δ : ℝ) := by
            rw [← Real.rpow_add hδ_pos_real, hsum_exp]
            exact Real.rpow_one _
          have hhalf := mul_le_mul_of_nonneg_left hgap_Minner hA_pos.le
          have hreal : 2 * (δ : ℝ) ≤ (δ : ℝ) ^ ((k.succ.val : ℝ) / (M_inner : ℝ)) := by
            nlinarith [hstep, hfac, hhalf, hA_pos]
          have hcast : ((2 * δ : NNReal) : ℝ) ≤ ((ρ_inner k.succ : NNReal) : ℝ) := by
            simp only [hρ_inner_def, NNReal.coe_rpow, NNReal.coe_mul]
            push_cast
            exact hreal
          exact_mod_cast hcast
        obtain ⟨r, Q, W, hρr, hr1, hratio_le, hQcov, hQdens⟩ :=
          hcover_s₂ k.succ.val (Fin.is_le k.succ)
        have hρ_eq : (δ : NNReal) ^ ((k.succ.val : ℝ) / (M_inner : ℝ)) = ρ_inner k.succ := rfl
        rw [hρ_eq] at hρr hratio_le
        refine le_trans (uniform_parent_maxDensity_le_of_nodeCover hδ_pos h2δ hρr hr1
          (h_uni k.succ) (h_branching k.succ) hQcov hQdens) ?_
        have hpow_le : (((r : ℝ) / (ρ_inner k.succ : ℝ)) ^ (3 * n) : ℝ)
            ≤ (δ : ℝ) ^ (-η_KT) := by
          have hn_ne : ((n : ℕ) : ℝ) ≠ 0 := by
            have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
            exact this.ne'
          have hbase : (0 : ℝ) ≤ (r : ℝ) / (ρ_inner k.succ : ℝ) := by positivity
          calc (((r : ℝ) / (ρ_inner k.succ : ℝ)) ^ (3 * n) : ℝ)
              ≤ ((δ : ℝ) ^ (-(η_KT / (3 * (n : ℝ))))) ^ (3 * n) :=
                pow_le_pow_left₀ hbase hratio_le _
            _ = (δ : ℝ) ^ (-η_KT) := by
                rw [← Real.rpow_natCast ((δ : ℝ) ^ (-(η_KT / (3 * (n : ℝ))))) (3 * n),
                  ← Real.rpow_mul hδ_pos_real.le]
                congr 1
                push_cast
                field_simp
        calc (↑(crossScaleConst n * C_uniform) : ENNReal)
                * ENNReal.ofReal (((r : ℝ) / (ρ_inner k.succ : ℝ)) ^ (3 * n))
                * ENNReal.ofReal ((δ : ℝ) ^ (-η_KT))
            ≤ (↑(crossScaleConst n * C_uniform) : ENNReal)
                * ENNReal.ofReal ((δ : ℝ) ^ (-η_KT))
                * ENNReal.ofReal ((δ : ℝ) ^ (-η_KT)) := by
              gcongr
          _ = (↑(crossScaleConst n * C_uniform) : ENNReal)
                * ENNReal.ofReal ((δ : ℝ) ^ (-(2 * η_KT))) := by
              rw [mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ_pos_real.le _),
                ← Real.rpow_add hδ_pos_real]
              ring_nf
          _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-((1 / (M_inner : ℝ)) ^ 2))) := h_dmax_cross_absorb
    have hN₂_xm_LB : ∀ k : Fin M_inner,
        ((N₂_band k.val : ℕ) : ℝ)
          ≤ ((Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
                / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ))
            * ((ρ_inner k.castSucc : ℝ) / (ρ_inner k.succ : ℝ))
                ^ (((Module.finrank ℝ E : ℝ) - 1) + ε_inner) := by
      intro k
      obtain ⟨i, hi⟩ := hs₂_ne
      obtain ⟨j, hj, hle⟩ := (h_uni k.castSucc).exists_le_rescale hi
      have hρ_succ_pos : 0 < ρ_inner k.succ := by
        rw [hρ_inner_def]
        exact NNReal.rpow_pos hδ_pos
      have hρ_cs_pos : 0 < ρ_inner k.castSucc := by
        rw [hρ_inner_def]
        exact NNReal.rpow_pos hδ_pos
      have hρ_cs_le : ρ_inner k.castSucc ≤ 1 := by
        have := hρ_inner_anti.antitone (Fin.zero_le k.castSucc)
        rwa [hρ_inner_zero] at this
      exact N₂_le_ratio_rpow_of_parent_maxDensity hρ_succ_pos hρ_cs_pos hρ_cs_le
        (h_uni k.succ) ((h_uni k.castSucc).parentTube j) ε_inner (h_delta_max k) (N₂_band k.val)
        (hN₂_band_child k j hj)
    have h_SSF_at_δ :
        ∃ (K_dim : ℝ) (C_R : ℝ) (R_SSF : Finset E) (s'_SSF : Finset (ι × E)),
          0 < K_dim ∧
          R_SSF.Nonempty ∧ s'_SSF ⊆ s₂ ×ˢ R_SSF ∧
          (R_SSF.card : ℝ) * (s₂.card : ℝ) *
              (δ : ℝ) ^ ((Module.finrank ℝ E : ℝ) - 1) ≤ K_dim ∧
          0 < C_R ∧
          (R_SSF.card : ℝ) ≤ C_R *
            max 1 ((s₂.card : ℝ) * (δ : ℝ) ^ ((Module.finrank ℝ E : ℝ) - 1))⁻¹ ∧
          C_R ≤ qCardConst (Module.finrank ℝ E) M_inner (cnEff (Module.finrank ℝ E))
              (prodConst (Module.finrank ℝ E) M_inner) * (δ : ℝ) ^ (-ε_inner) ∧
          s'_SSF.Nonempty ∧
          (∀ p ∈ s'_SSF, ((V p.1).translate p.2).carrier
              ⊆ Metric.closedBall (0 : E) ((M_inner : ℝ) + 1)) ∧
          IsFrostmanAtEveryScale (E := E) s'_SSF
            (fun p : ι × E => ((V p.1).toTube).translate p.2)
            (ENNReal.ofReal
              ((δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) + 3) * ε_inner))) ∧
          (∃ K_cnt : ℝ, 1 ≤ K_cnt ∧
            ∀ ρ_anchor : NNReal, δ ≤ ρ_anchor → ρ_anchor ≤ 1 → ∀ p₀ ∈ s'_SSF,
              ENNReal.ofReal
                  (((Tube.le_volume.c (Module.finrank ℝ E) : ℝ) /
                      (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)) ^ 2 *
                    ((δ : ℝ) ^ ε_inner / K_cnt ^ M_inner) /
                    ((δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1) * ε_inner) *
                      (8 : ℝ) ^ (2 * (Module.finrank ℝ E - 1))))
                ≤ Kakeya.densityIn
                    (s'_SSF.filter (fun p : ι × E =>
                      (((V p.1).toTube).translate p.2).toConvexSpaceBody ≤
                        (Tube.rescale (((V p₀.1).toTube).translate p₀.2)
                          ρ_anchor).toConvexSpaceBody))
                    (fun p : ι × E => (((V p.1).toTube).translate p.2).toConvexSpaceBody)
                    (Tube.rescale (((V p₀.1).toTube).translate p₀.2)
                      ρ_anchor).toConvexSpaceBody) ∧
          Kakeya.maxDensity s'_SSF
              (fun p : ι × E => (((V p.1).toTube).translate p.2).toConvexSpaceBody)
            ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(((Module.finrank ℝ E : ℝ) + 3) * ε_inner))) := by
      have hSSF_body :=
        (exists_threshold_of_eventually_nhdsGT
          (subStickyFrostmanLemma (E := E) ε_inner hε_inner_pos M_inner hM_inner_pos
            (cnEff (Module.finrank ℝ E)) (cnEff_pos (E := E)) (one_le_cnEff (E := E))
            (prodConst (Module.finrank ℝ E) M_inner) (prodConst_pos _ _)
            ((641 : ℝ) ^ (2 * Module.finrank ℝ E)) (by positivity)
            (max 1 ⌈(C_uniform : ℝ)⌉₊)
            (Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)))).choose_spec.2
          hδ_pos hδ_le_inner (ι := ι) s₂ hs₂_ne
      have hM_inner_form : M_inner = gridLen (Module.finrank ℝ E) η₁ ε := by
        rw [hM_inner_def, hn_def]
      have hδ_le_quarter_M : (δ : ℝ) ≤ (1/8 : ℝ) ^ M_inner := by
        rw [hM_inner_form]; exact hδ_le_quarter
      have hδ_pow_one_M : (δ : ℝ) ^ ((1 : ℝ) / (M_inner : ℝ)) ≤ 1/8 := by
        have h_step :
            (δ : ℝ) ^ ((1 : ℝ) / (M_inner : ℝ))
              ≤ ((1/8 : ℝ) ^ M_inner) ^ ((1 : ℝ) / (M_inner : ℝ)) := by
          apply Real.rpow_le_rpow hδ_pos_real.le hδ_le_quarter_M
          positivity
        have h_eq :
            ((1/8 : ℝ) ^ M_inner) ^ ((1 : ℝ) / (M_inner : ℝ)) = (1/8 : ℝ) := by
          rw [← Real.rpow_natCast ((1/8 : ℝ)) M_inner,
              ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1/8),
              mul_one_div, div_self hM_inner_ne_zero, Real.rpow_one]
        linarith [h_eq ▸ h_step]
      have h_gap : ∀ k : Fin M_inner,
          8 * (ρ_inner k.succ : ℝ) ≤ (ρ_inner k.castSucc : ℝ) := by
        intro k
        change (8 : ℝ) * ((δ : ℝ) ^ ((k.succ.val : ℝ) / (M_inner : ℝ)))
            ≤ ((δ : ℝ) ^ ((k.castSucc.val : ℝ) / (M_inner : ℝ)))
        have h_succ_exp : ((k.succ.val : ℝ) / (M_inner : ℝ))
            = ((k.castSucc.val : ℝ) / (M_inner : ℝ)) + (1 : ℝ) / (M_inner : ℝ) := by
          have h_val : (k.succ.val : ℝ) = (k.castSucc.val : ℝ) + 1 := by
            rw [Fin.val_succ, Fin.val_castSucc]; push_cast; ring
          rw [h_val, add_div]
        rw [h_succ_exp, Real.rpow_add hδ_pos_real]
        have h_cs_nn : (0 : ℝ) ≤ (δ : ℝ) ^ ((k.castSucc.val : ℝ) / (M_inner : ℝ)) :=
          Real.rpow_nonneg hδ_pos_real.le _
        calc 8 * ((δ : ℝ) ^ ((k.castSucc.val : ℝ) / (M_inner : ℝ))
                * (δ : ℝ) ^ ((1 : ℝ) / (M_inner : ℝ)))
            = (8 * (δ : ℝ) ^ ((1 : ℝ) / (M_inner : ℝ)))
                * (δ : ℝ) ^ ((k.castSucc.val : ℝ) / (M_inner : ℝ)) := by ring
          _ ≤ 1 * (δ : ℝ) ^ ((k.castSucc.val : ℝ) / (M_inner : ℝ)) := by
              apply mul_le_mul_of_nonneg_right _ h_cs_nn
              linarith [hδ_pow_one_M]
          _ = (δ : ℝ) ^ ((k.castSucc.val : ℝ) / (M_inner : ℝ)) := one_mul _
      obtain ⟨C_SSF, C_s', R_SSF, _Rs, _R_partial, s'_SSF,
        hR_SSF_ne, hs'_SSF_sub, hR_card_raw, hC_SSF_le2,
        _hRp_0, _hRp_succ, _hRp_last, hs'_SSF_ne,
        h_frost_SSF, hC_s'_pos, hcount_SSF, hSSF_1net_raw, h_anchor_SSF, h_md_SSF⟩ :=
        hSSF_body (fun i => (V i).toTube)
          hT_s₂
          ρ_inner hρ_inner_zero hρ_inner_last hρ_inner_anti
          C_uniform h_uni h_branching
          h_count
          (by
            intro δ' W k hWleaf
            obtain ⟨i, hi_s, hi_W⟩ := hWleaf
            have hδ_le_ρ : δ ≤ ρ_inner k := by
              have hmono := hρ_inner_anti.antitone (Fin.le_last k)
              rwa [hρ_inner_last] at hmono
            have hcard := (h_uni k).parents_containing_tube_card_le hδ_le_ρ W hi_s hi_W
            have key : ∀ {m : ℕ}, (m : NNReal) ≤ C_uniform →
                m ≤ max 1 ⌈(C_uniform : ℝ)⌉₊ := by
              intro m hm
              refine le_trans ?_ (le_max_right 1 _)
              have hmr : (m : ℝ) ≤ (C_uniform : ℝ) := by exact_mod_cast hm
              exact_mod_cast hmr.trans (Nat.le_ceil _)
            exact key hcard)
          h_ratio h_gap
          (fun k => (h_uni k).parent) (fun _ => Finset.Subset.refl _)
          (fun i hi => (h_uni 0).exists_le_rescale hi)
          (fun k : Fin M_inner => N₂_band k.val)
          (fun k : Fin M_inner => hN₂_band_pos k.val)
          (fun k j hj => le_trans (hN₂_bracket k j hj) (by
            have hcard : (0 : ℝ) ≤ (((h_uni k.succ).parent.filter (fun i : ι =>
                ((h_uni k.succ).parentTube i).toConvexSpaceBody ≤
                  ((h_uni k.castSucc).parentTube j).toConvexSpaceBody)).card : ℝ) :=
              Nat.cast_nonneg _
            exact mul_le_mul_of_nonneg_right (packConst_le_cnEff _) hcard))
          (fun k j hj => le_trans (hN₂_band_child_le k j hj) (by
            have hN : (0 : ℝ) ≤ ((N₂_band k.val : ℕ) : ℝ) := Nat.cast_nonneg _
            exact mul_le_mul_of_nonneg_right (childUB_le_cnEff _) hN))
          (fun k => le_trans (hN₂_xm_LB k) (by
            have hr : (0 : ℝ) ≤ ((ρ_inner k.castSucc : ℝ) / (ρ_inner k.succ : ℝ))
                ^ (((Module.finrank ℝ E : ℝ) - 1) + ε_inner) :=
              Real.rpow_nonneg (by positivity) _
            refine mul_le_mul_of_nonneg_right ?_ hr
            refine le_trans ?_ (packConst_le_cnEff _)
            have hpc : (0 : ℝ) ≤ (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
                / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) := by
              have hc : (0 : ℝ) < (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) := by
                exact_mod_cast Tube.le_volume.c_pos (Module.finrank ℝ E)
              positivity
            linarith))
          hN₂_prod
          h_delta_max
      have hs'_card_ge : (δ : ℝ) ^ ε_inner * (s₂.card : ℝ) * (R_SSF.card : ℝ) / C_s'
          ≤ (s'_SSF.card : ℝ) := by
        rw [div_le_iff₀ hC_s'_pos]
        calc (δ : ℝ) ^ ε_inner * (s₂.card : ℝ) * (R_SSF.card : ℝ)
            ≤ C_s' * (s'_SSF.card : ℝ) := hcount_SSF
          _ = (s'_SSF.card : ℝ) * C_s' := mul_comm _ _
      set C_SSF' : ℝ := C_SSF * (δ : ℝ) ^ (-ε_inner) with hC_SSF'_def
      have hδ_negε_ge_one : (1 : ℝ) ≤ (δ : ℝ) ^ (-ε_inner) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ_pos_real hδ_lt_one.le
          (neg_nonpos_of_nonneg hε_inner_pos.le)
      have hδ_negε_nonneg : (0 : ℝ) ≤ (δ : ℝ) ^ (-ε_inner) :=
        le_trans zero_le_one hδ_negε_ge_one
      have hC_SSF'_le : max C_SSF' 1 ≤
          qCardConst (Module.finrank ℝ E) M_inner (cnEff (Module.finrank ℝ E))
            (prodConst (Module.finrank ℝ E) M_inner) * (δ : ℝ) ^ (-ε_inner) := by
        refine max_le ?_ ?_
        · rw [hC_SSF'_def]
          exact mul_le_mul_of_nonneg_right hC_SSF_le2 hδ_negε_nonneg
        · have hq : (1 : ℝ) ≤ qCardConst (Module.finrank ℝ E) M_inner
              (cnEff (Module.finrank ℝ E)) (prodConst (Module.finrank ℝ E) M_inner) :=
            one_le_qCardConst _ _ _ _
          nlinarith
      refine ⟨max C_SSF' 1 *
                max 1 ((s₂.card : ℝ) * (δ : ℝ) ^ ((Module.finrank ℝ E : ℝ) - 1)),
        max C_SSF' 1, R_SSF, s'_SSF,
        ?_, hR_SSF_ne, hs'_SSF_sub, ?_, ?_, ?_,
        hC_SSF'_le, hs'_SSF_ne, ?_, h_frost_SSF, h_anchor_SSF,
        h_md_SSF⟩
      · have h1 : (1 : ℝ) ≤ max C_SSF' 1 := le_max_right _ _
        have h2 : (1 : ℝ) ≤
            max 1 ((s₂.card : ℝ) * (δ : ℝ) ^ ((Module.finrank ℝ E : ℝ) - 1)) :=
          le_max_left _ _
        have h1pos : 0 < max C_SSF' 1 := lt_of_lt_of_le one_pos h1
        have h2pos : 0 <
            max 1 ((s₂.card : ℝ) * (δ : ℝ) ^ ((Module.finrank ℝ E : ℝ) - 1)) :=
          lt_of_lt_of_le one_pos h2
        exact mul_pos h1pos h2pos
      · set X : ℝ := (s₂.card : ℝ) * (δ : ℝ) ^ ((Module.finrank ℝ E : ℝ) - 1)
          with hX_def
        have hX_nn : 0 ≤ X := by
          apply mul_nonneg (Nat.cast_nonneg _)
          exact Real.rpow_nonneg (NNReal.coe_nonneg _) _
        have h_aux : max 1 X⁻¹ * X ≤ max 1 X := by
          by_cases hX1 : X ≤ 1
          · by_cases hX0 : X = 0
            · rw [hX0]; simp
            · have hXpos : 0 < X := lt_of_le_of_ne hX_nn (Ne.symm hX0)
              have hXinv_ge : (1 : ℝ) ≤ X⁻¹ := by
                rw [le_inv_comm₀ one_pos hXpos]; simpa using hX1
              rw [max_eq_right hXinv_ge, inv_mul_cancel₀ (ne_of_gt hXpos)]
              exact le_max_left _ _
          · have hX1' : 1 < X := lt_of_not_ge hX1
            have hXpos : 0 < X := lt_trans one_pos hX1'
            have hXinv_le : X⁻¹ ≤ 1 := by
              rw [inv_le_one_iff₀]; right; exact hX1'.le
            rw [max_eq_left hXinv_le, one_mul]
            exact le_max_right _ _
        have hmax_nn : 0 ≤ max (1 : ℝ) X⁻¹ * X := by
          apply mul_nonneg _ hX_nn
          exact le_trans zero_le_one (le_max_left _ _)
        have h_CSSF_le : C_SSF' ≤ max C_SSF' 1 := le_max_left _ _
        have h_max1X_nn : 0 ≤ max C_SSF' 1 := by
          exact le_trans zero_le_one (le_max_right _ _)
        calc (R_SSF.card : ℝ) * (s₂.card : ℝ) *
              (δ : ℝ) ^ ((Module.finrank ℝ E : ℝ) - 1)
            = (R_SSF.card : ℝ) * X := by rw [hX_def]; ring
          _ ≤ (C_SSF' * max 1 X⁻¹) * X :=
              mul_le_mul_of_nonneg_right hR_card_raw hX_nn
          _ = C_SSF' * (max 1 X⁻¹ * X) := by ring
          _ ≤ max C_SSF' 1 * (max 1 X⁻¹ * X) :=
              mul_le_mul_of_nonneg_right h_CSSF_le hmax_nn
          _ ≤ max C_SSF' 1 * max 1 X :=
              mul_le_mul_of_nonneg_left h_aux h_max1X_nn
      · exact lt_of_lt_of_le one_pos (le_max_right _ _)
      · refine le_trans hR_card_raw ?_
        exact mul_le_mul_of_nonneg_right (le_max_left _ _)
          (le_trans zero_le_one (le_max_left _ _))
      · exact hSSF_1net_raw
    obtain ⟨K_dim, _C_R, R_SSF, s'_SSF, hK_dim_pos, hR_SSF_ne, hs'_SSF_sub,
      hR_card_SSF, _hC_R_pos, hR_card_sharp, hC_R_le2, hs'_SSF_ne, hs'_1net, h_frost_SSF,
      h_anchor_SSF, h_md_SSF⟩ :=
      h_SSF_at_δ
    set W : ι × E → ShadedTube δ E := fun p => (V p.1).translate p.2 with hW_def
    have hM_pos : 0 < ⌈Real.log (Real.log (1 / (δ : ℝ)))⌉₊ := by
      rw [Nat.ceil_pos]
      apply Real.log_pos
      have hquarter : (δ : ℝ) ≤ 1 / 4 := by
        refine hδ_le_quarter.trans ?_
        obtain ⟨k, hk⟩ : ∃ k, M_inner = k + 1 := ⟨M_inner - 1, by omega⟩
        rw [hk, pow_succ]
        have hle1 : (1 / 8 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        calc (1 / 8 : ℝ) ^ k * (1 / 8) ≤ 1 * (1 / 8) := by
              apply mul_le_mul_of_nonneg_right hle1; norm_num
          _ ≤ 1 / 4 := by norm_num
      rw [Real.lt_log_iff_exp_lt (by positivity)]
      have he : Real.exp 1 < 4 := by
        have h9 := Real.exp_one_lt_d9; norm_num at h9 ⊢; linarith
      have h4 : (4 : ℝ) ≤ 1 / (δ : ℝ) := by
        rw [le_div_iff₀ hδ_pos_real]; nlinarith [hquarter, hδ_pos_real]
      linarith [he, h4]
    obtain ⟨s_inj, hs_inj_sub, hs_inj_carrierinj, hs_inj_ne_of, hs_inj_cover⟩ :=
      exists_carrier_injOn_cover s'_SSF (fun p => (W p).carrier)
    have hs_inj_ne : s_inj.Nonempty := hs_inj_ne_of hs'_SSF_ne
    have hs_inj_B1 : ∀ ⦃p : ι × E⦄, p ∈ s_inj →
        (W p).carrier ⊆ Metric.closedBall (0 : E) ((M_inner : ℝ) + 1) :=
      fun p hp => hs'_1net p (hs_inj_sub hp)
    have hsinj_mult := card_le_maxDensity_mul_card_injOn s'_SSF s_inj
      (fun p => (W p).toConvexSpaceBody)
      (fun p hp => hs_inj_cover p hp)
      (fun q hq => by
        exact lt_of_lt_of_le
          (ENNReal.coe_pos.mpr (mul_pos (Tube.le_volume.c_pos _) (pow_pos hδ_pos _)))
          (Tube.le_volume ((W q).toTube)))
      (fun q hq => ((W q).toConvexSpaceBody).isCompact.measure_lt_top.ne)
      _ h_md_SSF
    have hmult_real : (s'_SSF.card : ℝ)
        ≤ (δ : ℝ) ^ (-(((Module.finrank ℝ E : ℝ) + 3) * ε_inner)) * (s_inj.card : ℝ) := by
      have htop : ENNReal.ofReal ((δ : ℝ) ^ (-(((Module.finrank ℝ E : ℝ) + 3) * ε_inner)))
          * (s_inj.card : ENNReal) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)
      have h := ENNReal.toReal_mono htop hsinj_mult
      rwa [ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
        ENNReal.toReal_natCast] at h
    have hsinj_card_ge : (s'_SSF.card : ℝ)
        * (δ : ℝ) ^ (((Module.finrank ℝ E : ℝ) + 3) * ε_inner) ≤ (s_inj.card : ℝ) := by
      have hδp : (0 : ℝ) < (δ : ℝ) ^ (((Module.finrank ℝ E : ℝ) + 3) * ε_inner) := by positivity
      calc (s'_SSF.card : ℝ) * (δ : ℝ) ^ (((Module.finrank ℝ E : ℝ) + 3) * ε_inner)
          ≤ ((δ : ℝ) ^ (-(((Module.finrank ℝ E : ℝ) + 3) * ε_inner)) * (s_inj.card : ℝ))
              * (δ : ℝ) ^ (((Module.finrank ℝ E : ℝ) + 3) * ε_inner) :=
            mul_le_mul_of_nonneg_right hmult_real hδp.le
        _ = (s_inj.card : ℝ) := by
            rw [mul_right_comm, ← Real.rpow_add hδ_pos_real, neg_add_cancel,
              Real.rpow_zero, one_mul]
    have hs_inj_SSF : s_inj ⊆ s'_SSF := hs_inj_sub
    refine ⟨R_SSF, s_inj, W, hR_SSF_ne, hs_inj_ne, ?_, ?_, (fun p => rfl),
      (fun p => Set.Subset.refl _), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      have hp_prod : p ∈ s₂ ×ˢ R_SSF := hs'_SSF_sub (hs_inj_SSF hp)
      exact ⟨hs₂_sub (Finset.mem_product.mp hp_prod).1, (Finset.mem_product.mp hp_prod).2⟩
    · have hn_pos1 : 1 ≤ n := hn_pos
      have hexp : (δ : ℝ) ^ ((n : ℝ) - 1) = (δ : ℝ) ^ (n - 1) := by
        rw [← Real.rpow_natCast (δ : ℝ) (n - 1), Nat.cast_sub hn_pos1, Nat.cast_one]
      have hc_pos : (0 : ℝ) < (Tube.le_volume.c n : ℝ) := by exact_mod_cast Tube.le_volume.c_pos n
      have hCn_pos : (0 : ℝ) < (Tube.volume_le.C n : ℝ) := by
        have hval : Tube.volume_le.C n = 2 ^ (n + 1) := rfl
        rw [hval]; positivity
      have hδpow_pos : (0 : ℝ) < (δ : ℝ) ^ (n - 1) := pow_pos hδ_pos_real _
      have hδneg_pos : (0 : ℝ) < (δ : ℝ) ^ (-η_KT) := Real.rpow_pos_of_pos hδ_pos_real _
      have hvc_nn : (0 : ℝ) ≤ MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
          / (Tube.le_volume.c n : ℝ) := by positivity
      have hmc_nn : (0 : ℝ) ≤ (Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ) := by positivity
      have hktR : (s.card : ℝ) * (δ : ℝ) ^ (n - 1)
          ≤ (δ : ℝ) ^ (-η_KT) * (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
              / (Tube.le_volume.c n : ℝ)) := by
        have hkt := katzTao_card_volume_bound hδ_pos hδ_lt_one s (fun i => (V i).toTube)
          hT_in_unit η_KT hKT
        rw [← mul_div_assoc]; exact hkt
      have hmultR : (s.card : ℝ)
          ≤ (δ : ℝ) ^ (-η_KT) * ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ))
              * (s₁.card : ℝ) := by
        have hmult := katzTao_carrier_multiplicity_bound hδ_pos hδ_lt_one s
          (fun i => (V i).toTube) η_KT hKT s₁ hs₁_inj hs₁_cover
        rw [mul_div_assoc] at hmult; exact hmult
      have hs2_pos : (0 : ℝ) < (s₂.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs₂_ne
      set Cq : ℝ := qCardConst (Module.finrank ℝ E) M_inner (cnEff (Module.finrank ℝ E))
        (prodConst (Module.finrank ℝ E) M_inner) * (δ : ℝ) ^ (-ε_inner) with hCq_def
      have hCq_pos : 0 < Cq := by
        dsimp [Cq]
        have h1 : 0 < qCardConst (Module.finrank ℝ E) M_inner (cnEff (Module.finrank ℝ E))
            (prodConst (Module.finrank ℝ E) M_inner) :=
          qCardConst_pos (Module.finrank ℝ E) M_inner (cnEff (Module.finrank ℝ E))
            (prodConst (Module.finrank ℝ E) M_inner)
        have h2 : 0 < (δ : ℝ) ^ (-ε_inner) := Real.rpow_pos_of_pos hδ_pos_real _
        positivity
      have hR2 : (R_SSF.card : ℝ) ≤ Cq * max 1 ((s₂.card : ℝ) * (δ : ℝ) ^ (n - 1))⁻¹ := by
        have h0 : (0 : ℝ) ≤ max 1 ((s₂.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹ :=
          le_trans zero_le_one (le_max_left _ _)
        calc (R_SSF.card : ℝ)
            ≤ _C_R * max 1 ((s₂.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹ := hR_card_sharp
          _ ≤ Cq * max 1 ((s₂.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹ :=
              mul_le_mul_of_nonneg_right hC_R_le2 h0
          _ = Cq * max 1 ((s₂.card : ℝ) * (δ : ℝ) ^ (n - 1))⁻¹ := by rw [hexp]
      have hMe : M_inner - 1 = gridLen (Module.finrank ℝ E) η₁ ε - 1 := by
        rw [hM_inner_form]
      set P : ℝ := edRefineC (E := E) * (δ : ℝ) ^ (-η_KT)
        * ((641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
            * ((⌊Real.logb 2 (s₁.card : ℝ)⌋₊ : ℝ) + 1) ^ (M_inner - 1)) with hP_def
      have hP_ge1 : (1 : ℝ) ≤ P := by
        dsimp [P]
        have h1 : (1 : ℝ) ≤ edRefineC (E := E) := one_le_edRefineC (E := E)
        have h2 : (1 : ℝ) ≤ (δ : ℝ) ^ (-η_KT) :=
          Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ_pos_real hδ_lt_one_real.le (by linarith)
        have h3 : (1 : ℝ) ≤ (641 : ℝ) ^ (2 * Module.finrank ℝ E)
            * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
            * ((⌊Real.logb 2 (s₁.card : ℝ)⌋₊ : ℝ) + 1) ^ (M_inner - 1) := by
          have hpl : (1 : ℝ) ≤ ((⌊Real.logb 2 (s₁.card : ℝ)⌋₊ : ℝ) + 1) ^ (M_inner - 1) := by
            apply one_le_pow₀
            have h0 : (0 : ℝ) ≤ (⌊Real.logb 2 (s₁.card : ℝ)⌋₊ : ℝ) := Nat.cast_nonneg _
            linarith
          have hc1 : (1 : ℝ) ≤ (641 : ℝ) ^ (2 * Module.finrank ℝ E)
              * (4 : ℝ) ^ (2 * Module.finrank ℝ E) :=
            one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
              (one_le_pow₀ (by norm_num))
          nlinarith [hc1, hpl]
        have h_nonneg_ed : 0 ≤ edRefineC (E := E) := by linarith [one_le_edRefineC (E := E)]
        have h_nonneg_δ : 0 ≤ (δ : ℝ) ^ (-η_KT) := hδneg_pos.le
        have h12 : (1 : ℝ) ≤ edRefineC (E := E) * (δ : ℝ) ^ (-η_KT) :=
          calc
            (1 : ℝ) = 1 * 1 := by norm_num
            _ ≤ edRefineC (E := E) * (δ : ℝ) ^ (-η_KT) :=
              mul_le_mul h1 h2 (by norm_num : (0 : ℝ) ≤ 1) h_nonneg_ed
        calc
          (1 : ℝ) = 1 * 1 := by norm_num
          _ ≤ (edRefineC (E := E) * (δ : ℝ) ^ (-η_KT))
              * ((641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
                  * ((⌊Real.logb 2 (s₁.card : ℝ)⌋₊ : ℝ) + 1) ^ (M_inner - 1)) :=
            mul_le_mul h12 h3 (by norm_num : (0 : ℝ) ≤ 1) (mul_nonneg h_nonneg_ed h_nonneg_δ)
      have hP_pos : 0 < P := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hP_ge1
      have hs1s2 : (s₁.card : ℝ) ≤ (s₂.card : ℝ) * P := by
        have h_card_s₂' : (s₁.card : ENNReal) ≤ ENNReal.ofReal P * (s₂.card : ENNReal) := by
          calc
            (s₁.card : ENNReal) ≤
                Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) *
                ENNReal.ofReal ((δ : ℝ) ^ (-η_KT)) *
                ENNReal.ofReal ((641 : ℝ) ^ (2 * Module.finrank ℝ E)
                  * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
                  * ((⌊Real.logb 2 (s₁.card : ℝ)⌋₊ : ℝ) + 1) ^ (M_inner - 1)) *
                (s₂.card : ENNReal) := h_card_s₂
            _ = (ENNReal.ofReal (edRefineC (E := E))) *
                ENNReal.ofReal ((δ : ℝ) ^ (-η_KT)) *
                ENNReal.ofReal ((641 : ℝ) ^ (2 * Module.finrank ℝ E)
                  * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
                  * ((⌊Real.logb 2 (s₁.card : ℝ)⌋₊ : ℝ) + 1) ^ (M_inner - 1)) *
                (s₂.card : ENNReal) := by rw [ofReal_edRefineC]
            _ = ((ENNReal.ofReal (edRefineC (E := E)) * ENNReal.ofReal ((δ : ℝ) ^ (-η_KT))) *
                ENNReal.ofReal ((641 : ℝ) ^ (2 * Module.finrank ℝ E)
                  * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
                  * ((⌊Real.logb 2 (s₁.card : ℝ)⌋₊ : ℝ) + 1) ^ (M_inner - 1))) *
                (s₂.card : ENNReal) := by ring
            _ = (ENNReal.ofReal (edRefineC (E := E) * (δ : ℝ) ^ (-η_KT)) *
                ENNReal.ofReal ((641 : ℝ) ^ (2 * Module.finrank ℝ E)
                  * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
                  * ((⌊Real.logb 2 (s₁.card : ℝ)⌋₊ : ℝ) + 1) ^ (M_inner - 1))) *
                (s₂.card : ENNReal) := by
              rw [ENNReal.ofReal_mul (p := edRefineC (E := E)) (q := (δ : ℝ) ^ (-η_KT)) (by
                have h0 : (0 : ℝ) ≤ edRefineC (E := E) := by linarith [one_le_edRefineC (E := E)]
                exact h0)]
            _ = ENNReal.ofReal (edRefineC (E := E) * (δ : ℝ) ^ (-η_KT) *
                ((641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
                  * ((⌊Real.logb 2 (s₁.card : ℝ)⌋₊ : ℝ) + 1) ^ (M_inner - 1)))
                * (s₂.card : ENNReal) := by
              rw [ENNReal.ofReal_mul (p := edRefineC (E := E) * (δ : ℝ) ^ (-η_KT))
                (q := (641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
                  * ((⌊Real.logb 2 (s₁.card : ℝ)⌋₊ : ℝ) + 1) ^ (M_inner - 1))
                (mul_nonneg (by
                  have h0 : (0 : ℝ) ≤ edRefineC (E := E) := by
                    linarith [one_le_edRefineC (E := E)]
                  exact h0) (by positivity))]
            _ = ENNReal.ofReal P * (s₂.card : ENNReal) := by rfl
        have htop : ENNReal.ofReal P * (s₂.card : ENNReal) ≠ ⊤ :=
          ENNReal.mul_ne_top (ENNReal.ofReal_ne_top) (ENNReal.natCast_ne_top _)
        have h := ENNReal.toReal_mono htop h_card_s₂'
        rw [ENNReal.toReal_natCast, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal hP_pos.le, ENNReal.toReal_natCast] at h
        rw [mul_comm]
        exact h
      have hED := e2_regime_arith hCn_pos hCq_pos hδpow_pos hs2_pos hP_ge1 hδneg_pos hvc_nn hmc_nn
        (Nat.cast_nonneg _ : (0 : ℝ) ≤ (s.card : ℝ)) hR2 hktR hmultR hs1s2
      have hbase : (⌊Real.logb 2 (s₁.card : ℝ)⌋₊ : ℝ) + 1
          ≤ (⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1 := by
        have hcard_le : (s₁.card : ℝ) ≤ (s.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hs₁_sub
        have hs1pos : (0 : ℝ) < (s₁.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs₁_ne
        have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < (2 : ℝ)) hs1pos hcard_le
        have hfl : (⌊Real.logb 2 (s₁.card : ℝ)⌋₊ : ℝ) ≤ (⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) := by
          exact_mod_cast Nat.floor_le_floor hlog
        linarith
      rw [hn_def] at hED
      rw [show (δ : ℝ) ^ ((Module.finrank ℝ E : ℝ) - 1) = (δ : ℝ) ^ (n - 1) from hexp]
      refine le_trans hED ?_
      set Dconst : ℝ := Cq * (Tube.volume_le.C n : ℝ) *
        (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2) / (Tube.le_volume.c n : ℝ) +
         (Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ)) with hDconst
      have h_ed_nonneg : 0 ≤ edRefineC (E := E) := by linarith [one_le_edRefineC (E := E)]
      have h_nonneg_common : 0 ≤ (641 : ℝ) ^ (2 * Module.finrank ℝ E)
          * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
          * edRefineC (E := E) * (δ : ℝ) ^ (-2 * η_KT) * Dconst := by
        refine mul_nonneg (mul_nonneg (mul_nonneg (by positivity) h_ed_nonneg)
          (by positivity)) ?_
        unfold Dconst; positivity
      calc
        (δ : ℝ) ^ (-η_KT) * Dconst * P
            = (641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
              * edRefineC (E := E) * (δ : ℝ) ^ (-2 * η_KT) * Dconst
              * (((⌊Real.logb 2 (s₁.card : ℝ)⌋₊ : ℝ) + 1)
                  ^ (gridLen (Module.finrank ℝ E) η₁ ε - 1) : ℝ) := by
          dsimp [Dconst, P]
          calc
            (δ : ℝ) ^ (-η_KT) * Dconst * (edRefineC (E := E) * (δ : ℝ) ^ (-η_KT)
                * ((641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
                    * ((⌊Real.logb 2 (s₁.card : ℝ)⌋₊ : ℝ) + 1) ^ (M_inner - 1)))
                = (641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
                  * edRefineC (E := E) * ((δ : ℝ) ^ (-η_KT) * (δ : ℝ) ^ (-η_KT)) * Dconst
                  * ((⌊Real.logb 2 (s₁.card : ℝ)⌋₊ : ℝ) + 1) ^ (M_inner - 1) := by ring
            _ = (641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
                  * edRefineC (E := E) * ((δ : ℝ) ^ ((-η_KT) + (-η_KT))) * Dconst
                  * ((⌊Real.logb 2 (s₁.card : ℝ)⌋₊ : ℝ) + 1) ^ (M_inner - 1) := by
              rw [← Real.rpow_add hδ_pos_real]
            _ = (641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
                  * edRefineC (E := E) * (δ : ℝ) ^ (-2 * η_KT) * Dconst
                  * ((⌊Real.logb 2 (s₁.card : ℝ)⌋₊ : ℝ) + 1) ^ (M_inner - 1) := by ring_nf
            _ = (641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
                  * edRefineC (E := E) * (δ : ℝ) ^ (-2 * η_KT) * Dconst
                  * (((⌊Real.logb 2 (s₁.card : ℝ)⌋₊ : ℝ) + 1)
                  ^ (gridLen (Module.finrank ℝ E) η₁ ε - 1) : ℝ) := by
              rw [hMe]
        _ ≤ (641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
            * edRefineC (E := E) * (δ : ℝ) ^ (-2 * η_KT) * Dconst
            * (((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1)
                  ^ (gridLen (Module.finrank ℝ E) η₁ ε - 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ h_nonneg_common
          have h_exp : ((⌊Real.logb 2 (s₁.card : ℝ)⌋₊ : ℝ) + 1)
                  ^ (gridLen (Module.finrank ℝ E) η₁ ε - 1)
              ≤ ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1)
                  ^ (gridLen (Module.finrank ℝ E) η₁ ε - 1) := by
            refine pow_le_pow_left₀ (by positivity) hbase _
          exact h_exp
    · intro p hp
      exact hs_inj_B1 hp
    · set Kpoly : ENNReal :=
        ((Nat.log 2 ((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 * s_inj.card) + 1 : ℕ)
            : ENNReal) ^ (2 * ⌈Real.log (Real.log (1 / (δ : ℝ)))⌉₊) with hKpoly
      have hKpoly_ne0 : Kpoly ≠ 0 := by rw [hKpoly]; positivity
      have hKpoly_top : Kpoly ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
      have h_full_ge : ENNReal.ofReal ((δ : ℝ) ^ η_full / 2)
          ≤ ShadedBody.fullness' s_inj (fun p => (W p).toShadedBody) := by
        refine fullness'_ge_of_per_body s_inj (fun p => (W p).toShadedBody) _ ?_ ?_ ?_
        · obtain ⟨p₀, hp₀⟩ := hs_inj_ne
          have hp0 : (0 : ENNReal) < MeasureTheory.volume ((W p₀).toShadedBody).carrier := by
            refine lt_of_lt_of_le ?_ (W p₀).toTube.le_volume
            have := Tube.le_volume.c_pos (Module.finrank ℝ E)
            positivity
          exact lt_of_lt_of_le hp0 (Finset.single_le_sum
            (f := fun i => MeasureTheory.volume ((W i).toShadedBody).carrier)
            (fun i _ => bot_le) hp₀)
        · refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun p _ => ?_))
          exact (W p).toTube.isCompact.measure_lt_top
        · intro p hp
          have hp1 : p.1 ∈ s := by
            have hpp : p ∈ s₂ ×ˢ R_SSF := hs'_SSF_sub (hs_inj_SSF hp)
            exact hs₂_sub (Finset.mem_product.mp hpp).1
          have hc : MeasureTheory.volume ((W p).toShadedBody).carrier
              = MeasureTheory.volume (V p.1).carrier := by
            change MeasureTheory.volume (W p).carrier = _
            rw [hW_def]
            simp only [ShadedTube.translate, ShadedTube.vadd_carrier, MeasureTheory.measure_vadd]
          have hsh : MeasureTheory.volume ((W p).toShadedBody).shade
              = MeasureTheory.volume (V p.1).shade := by
            change MeasureTheory.volume (W p).shade = _
            rw [hW_def]
            exact MeasureTheory.measure_image_add _ p.2 (V p.1).shade
          rw [hc, hsh]; exact h_pertube p.1 hp1
      have h_comp : ENNReal.ofReal ((δ : ℝ) ^ η₁) * Kpoly
          ≤ ENNReal.ofReal ((δ : ℝ) ^ η_full / 2) := by
        have hB_bound :
            (((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 * s_inj.card : ℕ) : ℝ)
              ≤ (((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 : ℕ) : ℝ)
                  * ((qCardConst (Module.finrank ℝ E) M_inner (cnEff (Module.finrank ℝ E))
                        (prodConst (Module.finrank ℝ E) M_inner) * (δ : ℝ) ^ (-ε_inner)) *
                      (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
                        / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) + 1))
                  * (δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1 + η_KT)) :=
          sinj_B_bound (E := E) hδ_pos hδ_lt_one η_KT hη_KT_pos s s₂ s_inj s'_SSF R_SSF
            _C_R hs_inj_sub hs'_SSF_sub hs₂_ne hs₂_sub hR_card_sharp
            (qCardConst (Module.finrank ℝ E) M_inner (cnEff (Module.finrank ℝ E))
                (prodConst (Module.finrank ℝ E) M_inner) * (δ : ℝ) ^ (-ε_inner))
            (by
              have h1 : (0 : ℝ) < qCardConst (Module.finrank ℝ E) M_inner
                  (cnEff (Module.finrank ℝ E))
                  (prodConst (Module.finrank ℝ E) M_inner) := qCardConst_pos _ _ _ _
              have h2 : (0 : ℝ) < (δ : ℝ) ^ (-ε_inner) :=
                Real.rpow_pos_of_pos hδ_pos_real _
              positivity)
            hC_R_le2
            (fun i => (V i).toTube) hT_in_unit hKT
        have hB_bound' :
            (((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 * s_inj.card : ℕ) : ℝ)
              ≤ (((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 : ℕ) : ℝ)
                  * (qCardConst (Module.finrank ℝ E) M_inner (cnEff (Module.finrank ℝ E))
                        (prodConst (Module.finrank ℝ E) M_inner) *
                      (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
                        / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) + 1))
                  * (δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1 + η_KT + 1)) := by
          refine le_trans hB_bound ?_
          have hqpos : (0 : ℝ) < qCardConst (Module.finrank ℝ E) M_inner
              (cnEff (Module.finrank ℝ E))
              (prodConst (Module.finrank ℝ E) M_inner) := qCardConst_pos _ _ _ _
          have hvol : (0 : ℝ) < MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
              / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) + 1 := by
            have hc : (0 : ℝ) < (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) := by
              exact_mod_cast Tube.le_volume.c_pos (Module.finrank ℝ E)
            positivity
          have hov : (0 : ℝ) ≤ (((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 : ℕ) : ℝ) :=
            Nat.cast_nonneg _
          have hε_le_one : ε_inner ≤ 1 := by
            rw [hε_inner_def]
            rw [div_le_one hM_inner_pos_real]
            exact_mod_cast hM_inner_pos
          have hsplit : (δ : ℝ) ^ (-ε_inner) *
              (δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1 + η_KT))
                ≤ (δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1 + η_KT + 1)) := by
            rw [← Real.rpow_add hδ_pos_real]
            refine Real.rpow_le_rpow_of_exponent_ge hδ_pos_real hδ_lt_one.le ?_
            have hε_nonneg : 0 ≤ ε_inner := hε_inner_pos.le
            linarith
          calc
            (((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 : ℕ) : ℝ)
                * ((qCardConst (Module.finrank ℝ E) M_inner (cnEff (Module.finrank ℝ E))
                      (prodConst (Module.finrank ℝ E) M_inner) * (δ : ℝ) ^ (-ε_inner)) *
                    (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
                      / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) + 1))
                * (δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1 + η_KT))
              = (((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 : ℕ) : ℝ)
                  * (qCardConst (Module.finrank ℝ E) M_inner (cnEff (Module.finrank ℝ E))
                        (prodConst (Module.finrank ℝ E) M_inner) *
                      (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
                        / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) + 1))
                  * ((δ : ℝ) ^ (-ε_inner) *
                      (δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1 + η_KT))) := by ring
            _ ≤ (((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 : ℕ) : ℝ)
                  * (qCardConst (Module.finrank ℝ E) M_inner (cnEff (Module.finrank ℝ E))
                        (prodConst (Module.finrank ℝ E) M_inner) *
                      (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
                        / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) + 1))
                  * (δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1 + η_KT + 1)) := by
                have hfac : (0 : ℝ) ≤ (((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 : ℕ) : ℝ)
                    * (qCardConst (Module.finrank ℝ E) M_inner (cnEff (Module.finrank ℝ E))
                          (prodConst (Module.finrank ℝ E) M_inner) *
                        (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
                          / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) + 1)) := by
                  positivity
                exact mul_le_mul_of_nonneg_left hsplit hfac
        have hreal := h_kpoly ((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 * s_inj.card)
          hB_bound'
        rw [hKpoly, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity),
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ_pos_real.le _)]
        exact ENNReal.ofReal_le_ofReal hreal
      have h_heavy5 : ENNReal.ofReal ((δ : ℝ) ^ η₁) * Kpoly
          ≤ ShadedBody.fullness' s_inj (fun i => (W i).toShadedBody) :=
        le_trans h_comp h_full_ge
      have hKpoly_one : (1 : ENNReal) ≤ Kpoly := by
        rw [hKpoly]
        have hbase : (1 : ENNReal) ≤ ((Nat.log 2 ((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2
        * s_inj.card) + 1 : ℕ) : ENNReal) := by
          exact_mod_cast (by omega
            : 1 ≤ (Nat.log 2 ((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2
          * s_inj.card) + 1))
        exact one_le_pow₀ hbase
      calc
        ENNReal.ofReal ((δ : ℝ) ^ η₁)
            = ENNReal.ofReal ((δ : ℝ) ^ η₁) * (1 : ENNReal) := by simp
        _ ≤ ENNReal.ofReal ((δ : ℝ) ^ η₁) * Kpoly :=
          mul_le_mul (le_refl _) hKpoly_one (by simp) (by simp)
        _ ≤ ShadedBody.fullness' s_inj (fun i => (W i).toShadedBody) := h_heavy5
    · refine fullness'_ge_of_per_body s_inj (fun p => (W p).toShadedBody) _ ?_ ?_ ?_
      · obtain ⟨p₀, hp₀⟩ := hs_inj_ne
        have hp0 : (0 : ENNReal) < MeasureTheory.volume ((W p₀).toShadedBody).carrier := by
          refine lt_of_lt_of_le ?_ (W p₀).toTube.le_volume
          have := Tube.le_volume.c_pos (Module.finrank ℝ E)
          positivity
        exact lt_of_lt_of_le hp0 (Finset.single_le_sum
          (f := fun i => MeasureTheory.volume ((W i).toShadedBody).carrier)
          (fun i _ => bot_le) hp₀)
      · refine ne_of_lt (ENNReal.sum_lt_top.mpr (fun p _ => ?_))
        exact (W p).toTube.isCompact.measure_lt_top
      · intro p hp
        have hp1 : p.1 ∈ s := by
          have hpp : p ∈ s₂ ×ˢ R_SSF := hs'_SSF_sub (hs_inj_SSF hp)
          exact hs₂_sub (Finset.mem_product.mp hpp).1
        have hc : MeasureTheory.volume ((W p).toShadedBody).carrier
            = MeasureTheory.volume (V p.1).carrier := by
          change MeasureTheory.volume (W p).carrier = _
          rw [hW_def]
          simp only [ShadedTube.translate, ShadedTube.vadd_carrier, MeasureTheory.measure_vadd]
        have hsh : MeasureTheory.volume ((W p).toShadedBody).shade
            = MeasureTheory.volume (V p.1).shade := by
          change MeasureTheory.volume (W p).shade = _
          rw [hW_def]
          exact MeasureTheory.measure_image_add _ p.2 (V p.1).shade
        rw [hc, hsh]; exact h_pertube p.1 hp1
    · intro p hp
      have hp1 : p.1 ∈ s := by
        have hpp : p ∈ s₂ ×ˢ R_SSF := hs'_SSF_sub (hs_inj_SSF hp)
        exact hs₂_sub (Finset.mem_product.mp hpp).1
      have hc : MeasureTheory.volume (W p).carrier
          = MeasureTheory.volume (V p.1).carrier := by
        rw [hW_def]
        simp only [ShadedTube.translate, ShadedTube.vadd_carrier, MeasureTheory.measure_vadd]
      have hsh : MeasureTheory.volume (W p).shade
          = MeasureTheory.volume (V p.1).shade := by
        rw [hW_def]
        exact MeasureTheory.measure_image_add _ p.2 (V p.1).shade
      rw [hc, hsh]; exact h_pertube p.1 hp1
    · have hfd := isFrostmanAtEveryScale_of_carrier_dedup hδ_pos s'_SSF s_inj
        (fun p : ι × E => ((V p.1).toTube).translate p.2) hs_inj_sub
        (fun p hp => hs_inj_cover p hp) _ h_md_SSF _ h_frost_SSF
      have hC : ENNReal.ofReal ((δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) + 3) * ε_inner))
          * ENNReal.ofReal ((δ : ℝ) ^ (-(((Module.finrank ℝ E : ℝ) + 3) * ε_inner)))
        = ENNReal.ofReal ((δ : ℝ) ^ (-(2 * ((Module.finrank ℝ E : ℝ) + 3) * ε_inner))) := by
        calc
          ENNReal.ofReal ((δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) + 3) * ε_inner))
              * ENNReal.ofReal ((δ : ℝ) ^ (-(((Module.finrank ℝ E : ℝ) + 3) * ε_inner)))
          = ENNReal.ofReal (((δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) + 3) * ε_inner))
              * ((δ : ℝ) ^ (-(((Module.finrank ℝ E : ℝ) + 3) * ε_inner)))) := by
            rw [ENNReal.ofReal_mul (by positivity
              : 0 ≤ (δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) + 3) * ε_inner))]
          _ = ENNReal.ofReal ((δ : ℝ) ^ ((-((Module.finrank ℝ E : ℝ) + 3) * ε_inner)
              + (-(((Module.finrank ℝ E : ℝ) + 3) * ε_inner)))) := by rw [Real.rpow_add hδ_pos_real]
          _ = ENNReal.ofReal ((δ : ℝ) ^ (-(2 * ((Module.finrank ℝ E : ℝ) + 3) * ε_inner)))
              := by ring_nf
      rw [hC] at hfd
      rw [hW_def]
      exact hfd
    · let f : ι × E → ConvexSpaceBody E :=
        fun p => (((V p.1).toTube).translate p.2).toConvexSpaceBody
      have hW_eq : (fun p : ι × E => ((W p).toTube).toConvexSpaceBody) = f := by
        funext p
        change ((W p).toTube).toConvexSpaceBody =
            (((V p.1).toTube).translate p.2).toConvexSpaceBody
        rw [hW_def]; rfl
      rw [hW_eq]
      have hε_inner_grid : ε_inner = 1 / ((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ) := by
        rw [hε_inner_def]
      have hRHS : ENNReal.ofReal ((δ : ℝ) ^ (-(((Module.finrank ℝ E : ℝ) + 3) * ε_inner)))
          = ENNReal.ofReal ((δ : ℝ) ^ (-(((Module.finrank ℝ E : ℝ) + 3)
              * (1 / ((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ))))) := by
        rw [← hε_inner_grid]
      rw [← hRHS]
      exact le_trans (Kakeya.maxDensity_mono f hs_inj_sub) h_md_SSF
end stickyKatzTaoOfStickyFrostman

end StickyKakeya

end Kakeya
