/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Sticky
public import Kakeya.StickyKakeya.FibreCounts
public import Kakeya.StickyKakeya.CrossScale
public import Kakeya.StickyKakeya.Absorption
public import Kakeya.StickyKakeya.Step1

/-!
# Theorem 7.3(A) ⇒ (B): the fixed-`δ` assembly

`assembly_helper` runs the three steps of the paper at one fixed `δ`: Step 1 produces the
translated family, Step 2 applies Theorem 7.3(A) to it, and Step 3 averages back by translation
invariance.  The main theorem is this together with the choice of thresholds.
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

/-- **Assembly of GWZ Theorem 7.3(B)** for a fixed `δ` (paper section7.tex L188–L196), in three
steps: `exists_frostman_translation_family` (Lemma 7.5) translates `(𝕋, Y)` to a
Frostman-at-every-scale family, Theorem 7.3(A) applies to it giving `δ^ε ≤ |U(𝕋', Y')|`, and
Lebesgue translation invariance together with the packing bound averages back to
`∑ |Y| ≤ δ^{-ε} · |U(𝕋, Y)|`. -/
lemma assembly_helper
    (ε : ℝ) (_hε : 0 < ε)
    (ε_A : ℝ) (_hε_A_pos : 0 < ε_A)
    (η₁ : ℝ) (hη₁_pos : 0 < η₁)
    (η_full : ℝ) (hη_full_le : η_full ≤ η₁)
    (η_KT : ℝ) (hη_KT_pos : 0 < η_KT)
    {ι : Type}
    {δ : NNReal} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (h_bridge_apply :
      ∀ (s_idx : Finset (ι × E)) (V'' : ι × E → ShadedTube δ E), s_idx.Nonempty →
        (∀ p ∈ s_idx, (V'' p).carrier ⊆ Metric.closedBall (0 : E)
            (((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ) + 1)) →
        (s_idx.card : ℝ) ≤ (δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) + ε - ε_A)) →
        (∀ p ∈ s_idx, ENNReal.ofReal ((δ : ℝ) ^ η_full / 2)
            * volume (V'' p).carrier ≤ volume (V'' p).shade) →
        IsFrostmanAtGridScales s_idx (fun p => (V'' p).toTube) (ssfGridLen δ)
          (ENNReal.ofReal ((δ : ℝ) ^
            (-(2 * ((Module.finrank ℝ E : ℝ) + 3)
                * (1 / ((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ)))))) →
        Kakeya.maxDensity s_idx (fun p => ((V'' p).toTube).toConvexSpaceBody)
          ≤ ENNReal.ofReal ((δ : ℝ) ^
            (-(((Module.finrank ℝ E : ℝ) + 3)
                * (1 / ((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ))))) →
        ENNReal.ofReal ((δ : ℝ) ^ ε_A)
          ≤ volume (⋃ p ∈ s_idx, (V'' p).shade))
    (hδ_le_quarter : (δ : ℝ) ≤
        (1 / 8 : ℝ) ^ (gridLen (Module.finrank ℝ E) η₁ ε))
    (hη_KT_lt : η_KT <
        (1 / ((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ)) ^ 2)
    (hδ_le_inner : δ ≤ ssfδ₀ (E := E) η₁ ε)
    (hδ_thresh : (δ : ℝ) ^ (sfBeta (E := E) η₁)
        * ((2 * (Tube.overlapConstBO (Module.finrank ℝ E) : NNReal)) : ℝ) ^ 3
        * (2 * ((2 * (Tube.overlapConstBO (Module.finrank ℝ E) : NNReal)) : ℝ) ^ 3)
            ^ (⌈Real.log (Real.log (1 / (δ : ℝ)))⌉₊) ≤ 1)
    (hδ_ratio_thresh : (δ : ℝ) ^ (sfBeta (E := E) η₁ / 2)
        ≤ ((Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
              / (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)) ^ 2
            / ((2 * (Tube.overlapConstBO (Module.finrank ℝ E) : NNReal)) : ℝ)
                ^ (2 * (Module.finrank ℝ E - 1)))
    (hMout_large : ((Module.finrank ℝ E : ℝ) - 1) / (⌈Real.log (Real.log (1 / (δ : ℝ)))⌉₊ : ℝ)
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
    (hδ_le_Cvol : (δ : ℝ) ≤ (Tube.volume_le.C (Module.finrank ℝ E) : ℝ))
    (s : Finset ι) (V : ι → ShadedTube δ E)
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
          (ENNReal.ofReal ((δ : ℝ) ^ (-η_KT))))
    (habsorb : (δ : ℝ) ^ (-ε_A)
        * ((641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
            * edRefineC (E := E) * (δ : ℝ) ^ (-2 * η_KT)
            * (e2Const (Module.finrank ℝ E) η₁ ε δ *
              (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
                * (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
                      / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
                    + (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
                      / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)))
            * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1)
                ^ (gridLen (Module.finrank ℝ E) η₁ ε - 1))
      ≤ (δ : ℝ) ^ (-ε)) :
    ∑ i ∈ s, MeasureTheory.volume (V i).shade
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ε)) *
        MeasureTheory.volume (⋃ i ∈ s, (V i).shade) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn_pos : 0 < n := Module.finrank_pos (R := ℝ) (M := E)
  have hδ_pos_real : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
  have hδ_lt_one_real : (δ : ℝ) < 1 := by exact_mod_cast hδ_lt_one
  by_cases hs_empty : s = ∅
  · subst hs_empty; simp
  have hs_nonempty : s.Nonempty := Finset.nonempty_of_ne_empty hs_empty
  obtain ⟨R, s_ref, V_ref, hR_ne, hs_ref_ne, hσ_mem, hR_card_UB, h_tube_eq,
    h_shade_sub, hσ_carrier_unit, hσ_fullness, hσ_fullness_in, hσ_pertube,
    h_frostman_Fin, h_maxDensity_ref⟩ :=
    exists_frostman_translation_family (E := E) ε η₁ hη₁_pos η_full hη_full_le η_KT hη_KT_pos
      hδ_pos hδ_lt_one hδ_le_quarter hη_KT_lt hδ_le_inner hδ_thresh hδ_ratio_thresh hMout_large
      h_dmax_absorb h_dmax_cross_absorb s hs_nonempty V
      hT_in_unit h_pertube h_kpoly hKT hKT_cover
  have h_A_out :
      ENNReal.ofReal ((δ : ℝ) ^ ε_A)
        ≤ MeasureTheory.volume (⋃ p ∈ s_ref, (V_ref p).shade) := by
    have h_card_ref : (s_ref.card : ℝ)
        ≤ (δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) + ε - ε_A)) := by
      have h_sub : s_ref ⊆ s ×ˢ R := fun p hp => Finset.mem_product.mpr (hσ_mem p hp)
      have h_card_le : (s_ref.card : ℝ) ≤ (R.card : ℝ) * (s.card : ℝ) := by
        have hle := Finset.card_le_card h_sub
        rw [Finset.card_product] at hle
        have hle' : (s_ref.card : ℝ) ≤ (s.card : ℝ) * (R.card : ℝ) := by exact_mod_cast hle
        linarith [hle', mul_comm ((s.card : ℝ)) ((R.card : ℝ))]
      refine le_trans h_card_le ?_
      have hCv_pos : (0 : ℝ) < (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) := by
        unfold Tube.volume_le.C
        positivity
      have hkey := card_le_of_prod_bracket (δ := δ) hδ_pos _
        (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) ((Module.finrank ℝ E : ℝ) - 1) ε ε_A
        ((R.card : ℝ) * (s.card : ℝ)) hCv_pos hδ_le_Cvol (by positivity) hR_card_UB habsorb
      have hexp : (Module.finrank ℝ E : ℝ) - 1 + 1 + ε - ε_A
          = (Module.finrank ℝ E : ℝ) + ε - ε_A := by ring
      rwa [hexp] at hkey
    exact h_bridge_apply s_ref V_ref hs_ref_ne hσ_carrier_unit h_card_ref hσ_pertube
      (isFrostmanAtGridScales_of_isFrostmanAtEveryScale hδ_pos hδ_lt_one.le _ h_frostman_Fin)
      h_maxDensity_ref
  have h_avg :
      MeasureTheory.volume (⋃ p ∈ s_ref, (V_ref p).shade)
        ≤ (R.card : ENNReal) * MeasureTheory.volume (⋃ i ∈ s, (V i).shade) := by
    set S : Set E := ⋃ i ∈ s, (V i).shade with hS_def
    have h_each_subset :
        ∀ p ∈ s_ref, (V_ref p).shade ⊆ (p.2 + ·) '' S := by
      intro p hp
      have h1 : (V_ref p).shade ⊆ ((V p.1).translate p.2).shade := h_shade_sub p
      have h2 : ((V p.1).translate p.2).shade = (p.2 + ·) '' (V p.1).shade := rfl
      rw [h2] at h1
      refine h1.trans (Set.image_mono ?_)
      intro x hx
      exact Set.mem_biUnion (hσ_mem p hp).1 hx
    have h_union_subset :
        (⋃ p ∈ s_ref, (V_ref p).shade) ⊆ ⋃ v ∈ R, ((v + ·) '' S) := by
      intro x hx
      rw [Set.mem_iUnion₂] at hx
      obtain ⟨p, hp, hxp⟩ := hx
      exact Set.mem_iUnion₂.mpr
        ⟨p.2, (hσ_mem p hp).2, h_each_subset p hp hxp⟩
    calc MeasureTheory.volume (⋃ p ∈ s_ref, (V_ref p).shade)
        ≤ MeasureTheory.volume (⋃ v ∈ R, ((v + ·) '' S)) :=
          MeasureTheory.measure_mono h_union_subset
      _ ≤ ∑ v ∈ R, MeasureTheory.volume ((v + ·) '' S) :=
          MeasureTheory.measure_biUnion_finset_le R _
      _ = ∑ _v ∈ R, MeasureTheory.volume S := by
          refine Finset.sum_congr rfl ?_
          intro v _hv
          exact MeasureTheory.measure_image_add _ v S
      _ = (R.card : ENNReal) * MeasureTheory.volume S := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h_shade_vol :
      ∑ i ∈ s, MeasureTheory.volume (V i).shade
        ≤ ENNReal.ofReal ((s.card : ℝ) * (Tube.volume_le.C n : ℝ) *
            (δ : ℝ) ^ ((n : ℝ) - 1)) := by
    have hδ_le_one_nn : δ ≤ 1 := le_of_lt hδ_lt_one
    have hC_nonneg : (0 : ℝ) ≤ (Tube.volume_le.C n : ℝ) := NNReal.coe_nonneg _
    have h_pow_nonneg : (0 : ℝ) ≤ (δ : ℝ) ^ ((n : ℝ) - 1) :=
      (Real.rpow_pos_of_pos hδ_pos_real _).le
    have h_pow_eq : (δ : ℝ) ^ (n - 1 : ℕ) = (δ : ℝ) ^ ((n : ℝ) - 1) := by
      rw [show ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) by
            rw [Nat.cast_sub hn_pos]; push_cast; ring,
          Real.rpow_natCast]
    have h_each : ∀ i ∈ s,
        MeasureTheory.volume (V i).shade
          ≤ ENNReal.ofReal ((Tube.volume_le.C n : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1)) := by
      intro i _hi
      have h_subset : MeasureTheory.volume (V i).shade
          ≤ MeasureTheory.volume (V i).carrier := measure_mono (V i).shade_subset
      have h_tube : MeasureTheory.volume (V i).carrier
          ≤ ((Tube.volume_le.C n * δ ^ (n - 1) : NNReal) : ENNReal) :=
        Tube.volume_le hδ_le_one_nn (V i).toTube
      have h_eq :
          ((Tube.volume_le.C n * δ ^ (n - 1) : NNReal) : ENNReal)
            = ENNReal.ofReal ((Tube.volume_le.C n : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1)) := by
        rw [← ENNReal.ofReal_coe_nnreal]
        push_cast
        rw [h_pow_eq]
      exact (h_subset.trans h_tube).trans h_eq.le
    calc ∑ i ∈ s, MeasureTheory.volume (V i).shade
        ≤ ∑ _i ∈ s, ENNReal.ofReal
            ((Tube.volume_le.C n : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1)) :=
          Finset.sum_le_sum h_each
      _ = (s.card : ENNReal) * ENNReal.ofReal
            ((Tube.volume_le.C n : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal ((s.card : ℝ) *
            ((Tube.volume_le.C n : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))) := by
          rw [show ((s.card : ENNReal)) = ENNReal.ofReal ((s.card : ℝ)) from
                (ENNReal.ofReal_natCast s.card).symm,
              ← ENNReal.ofReal_mul (by exact_mod_cast Nat.zero_le _ : (0 : ℝ) ≤ (s.card : ℝ))]
      _ = ENNReal.ofReal ((s.card : ℝ) * (Tube.volume_le.C n : ℝ) *
            (δ : ℝ) ^ ((n : ℝ) - 1)) := by ring_nf
  set K : ℝ := (s.card : ℝ) * (Tube.volume_le.C n : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1)
    with hK_def
  have hK_nonneg : 0 ≤ K := by
    have h1 : (0 : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast Nat.zero_le _
    have hC : (0 : ℝ) ≤ (Tube.volume_le.C n : ℝ) := NNReal.coe_nonneg _
    have h2 : (0 : ℝ) ≤ (δ : ℝ) ^ ((n : ℝ) - 1) :=
      (Real.rpow_pos_of_pos hδ_pos_real _).le
    exact mul_nonneg (mul_nonneg h1 hC) h2
  set M_inner : ℕ := gridLen (Module.finrank ℝ E) η₁ ε with hM_inner_def
  set D : ℝ := (641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
      * edRefineC (E := E) * (δ : ℝ) ^ (-2 * η_KT)
      * (e2Const (Module.finrank ℝ E) η₁ ε δ *
          (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
          * (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
                / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
              + (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
                / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)))
      * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) + 1)
          ^ (gridLen (Module.finrank ℝ E) η₁ ε - 1) with hD_def
  have h_pow_εA_pos : 0 < (δ : ℝ) ^ ε_A := Real.rpow_pos_of_pos hδ_pos_real _
  have h_pow_εA_neg_pos : 0 < (δ : ℝ) ^ (-ε_A) := Real.rpow_pos_of_pos hδ_pos_real _
  have hR_K_le_D : (R.card : ENNReal) * ENNReal.ofReal K ≤ ENNReal.ofReal D := by
    have h_cast : ((R.card : ENNReal) : ENNReal) = ENNReal.ofReal (R.card : ℝ) :=
      (ENNReal.ofReal_natCast R.card).symm
    rw [h_cast, ← ENNReal.ofReal_mul (by exact_mod_cast Nat.zero_le _ : (0 : ℝ) ≤ (R.card : ℝ))]
    refine ENNReal.ofReal_le_ofReal ?_
    have hRK : (R.card : ℝ) * K =
        (R.card : ℝ) * (s.card : ℝ) * (Tube.volume_le.C n : ℝ) *
          (δ : ℝ) ^ ((n : ℝ) - 1) := by rw [hK_def]; ring
    rw [hRK]; exact hR_card_UB
  have h_combined :
      ENNReal.ofReal ((δ : ℝ) ^ ε_A) ≤
        (R.card : ENNReal) * MeasureTheory.volume (⋃ i ∈ s, (V i).shade) :=
    h_A_out.trans h_avg
  have h_with_K :
      ENNReal.ofReal ((δ : ℝ) ^ ε_A) * ENNReal.ofReal K ≤
        ((R.card : ENNReal) * MeasureTheory.volume (⋃ i ∈ s, (V i).shade)) *
          ENNReal.ofReal K := by gcongr
  have h_drop_R_K :
      ((R.card : ENNReal) * MeasureTheory.volume (⋃ i ∈ s, (V i).shade)) *
          ENNReal.ofReal K
        ≤ ENNReal.ofReal D * MeasureTheory.volume (⋃ i ∈ s, (V i).shade) := by
    have h_assoc :
        ((R.card : ENNReal) * MeasureTheory.volume (⋃ i ∈ s, (V i).shade)) *
            ENNReal.ofReal K
          = MeasureTheory.volume (⋃ i ∈ s, (V i).shade) *
              ((R.card : ENNReal) * ENNReal.ofReal K) := by
      rw [mul_comm (R.card : ENNReal) _, mul_assoc]
    rw [h_assoc, mul_comm (ENNReal.ofReal D) _]
    gcongr
  have h_pre :
      ENNReal.ofReal ((δ : ℝ) ^ ε_A * K) ≤
        ENNReal.ofReal D * MeasureTheory.volume (⋃ i ∈ s, (V i).shade) := by
    rw [ENNReal.ofReal_mul h_pow_εA_pos.le]
    exact h_with_K.trans h_drop_R_K
  have h_pow_inv_eq :
      (δ : ℝ) ^ (-ε_A) * ((δ : ℝ) ^ ε_A * K) = K := by
    have h1 : (δ : ℝ) ^ (-ε_A) * (δ : ℝ) ^ ε_A = 1 := by
      rw [← Real.rpow_add hδ_pos_real]; simp
    rw [← mul_assoc, h1, one_mul]
  have h_K_le :
      ENNReal.ofReal K ≤
        ENNReal.ofReal ((δ : ℝ) ^ (-ε_A) * D) *
          MeasureTheory.volume (⋃ i ∈ s, (V i).shade) := by
    have h_step :
        ENNReal.ofReal ((δ : ℝ) ^ (-ε_A)) * ENNReal.ofReal ((δ : ℝ) ^ ε_A * K) ≤
          ENNReal.ofReal ((δ : ℝ) ^ (-ε_A)) *
            (ENNReal.ofReal D * MeasureTheory.volume (⋃ i ∈ s, (V i).shade)) := by
      gcongr
    have h_simp :
        ENNReal.ofReal ((δ : ℝ) ^ (-ε_A)) * ENNReal.ofReal ((δ : ℝ) ^ ε_A * K) =
          ENNReal.ofReal K := by
      rw [← ENNReal.ofReal_mul h_pow_εA_neg_pos.le, h_pow_inv_eq]
    rw [h_simp] at h_step
    rw [ENNReal.ofReal_mul h_pow_εA_neg_pos.le, mul_assoc]
    exact h_step
  calc ∑ i ∈ s, MeasureTheory.volume (V i).shade
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ε_A) * D) *
          MeasureTheory.volume (⋃ i ∈ s, (V i).shade) := h_shade_vol.trans h_K_le
    _ ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ε)) *
          MeasureTheory.volume (⋃ i ∈ s, (V i).shade) :=
        by
          simpa [hD_def] using mul_le_mul_left (ENNReal.ofReal_le_ofReal habsorb)
            (MeasureTheory.volume (⋃ i ∈ s, (V i).shade))
end stickyKatzTaoOfStickyFrostman

end StickyKakeya

end Kakeya
