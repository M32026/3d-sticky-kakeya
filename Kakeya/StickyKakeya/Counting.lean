/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Sticky
public import Kakeya.StickyKakeya.CrossScale

/-!
# Theorem 7.3(A) ⇒ (B): counting and density bridges

The cardinality bounds the deduction reads off a density hypothesis: how many tubes fit inside a
coarser tube, how many children a parent has, the carrier-multiplicity of a Katz–Tao family, and
the leaf → parent `maxDensity` transfer of `:1466`.
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

open scoped Classical in
/-- **Tube-in-tube count upper bound via maxDensity** (blueprint Lemma 7.4 /
`lem:tubesInBodyCount`).  The number of `δ_fine`-tubes contained in a fixed `δ_coarse`-tube `K` is
at most `maxDensity(family) · (vol_le.C/le_vol.c) · (δ_coarse/δ_fine)^(n-1)`, by
`Kakeya.card_familyIn_le` together with the per-tube volume upper bound `Tube.volume_le`. -/
private lemma card_tubes_in_tube_le_of_maxDensity
    {ι : Type*} {δ_fine δ_coarse : NNReal}
    (hδ_fine_pos : 0 < δ_fine) (hδ_coarse_le : δ_coarse ≤ 1)
    (s : Finset ι) (T : ι → Tube δ_fine E) (K : Tube δ_coarse E)
    (M : ℝ) (hM : 0 ≤ M)
    (h_md : Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody)
        ≤ ENNReal.ofReal M) :
    ((Kakeya.familyIn s (fun i => (T i).toConvexSpaceBody)
        K.toConvexSpaceBody).card : ℝ)
      ≤ M * ((Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
            / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ))
        * ((δ_coarse : ℝ) / (δ_fine : ℝ)) ^ ((Module.finrank ℝ E : ℝ) - 1) := by
  classical
  set n := Module.finrank ℝ E with hn_def
  have hn_pos : 0 < n := Module.finrank_pos
  have hcpos : (0 : ℝ) < (Tube.le_volume.c n : ℝ) := by
    exact_mod_cast Tube.le_volume.c_pos n
  have hδf_pos : (0 : ℝ) < (δ_fine : ℝ) := by exact_mod_cast hδ_fine_pos
  have hδc_nonneg : (0 : ℝ) ≤ (δ_coarse : ℝ) := by exact_mod_cast NNReal.coe_nonneg _
  set cardSet := Kakeya.familyIn s (fun i => (T i).toConvexSpaceBody)
    K.toConvexSpaceBody with hcardSet_def
  have hcard_ennreal : (cardSet.card : ENNReal)
      * ((Tube.le_volume.c n : ENNReal) * (δ_fine : ENNReal) ^ (n - 1))
      ≤ (ENNReal.ofReal M) * ((Tube.volume_le.C n : ENNReal) * (δ_coarse : ENNReal) ^ (n - 1)) := by
    have hvol_le : volume K.toConvexSpaceBody.carrier
        ≤ (Tube.volume_le.C n : ENNReal) * (δ_coarse : ENNReal) ^ (n - 1) := by
      simpa [hn_def] using Tube.volume_le hδ_coarse_le K
    calc
      (cardSet.card : ENNReal) * ((Tube.le_volume.c n : ENNReal) * (δ_fine : ENNReal) ^ (n - 1))
          ≤ Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody)
      * volume K.toConvexSpaceBody.carrier :=
        Kakeya.card_familyIn_le s T K.toConvexSpaceBody
      _ ≤ (ENNReal.ofReal M) * volume K.toConvexSpaceBody.carrier :=
        mul_le_mul_of_nonneg_right h_md (by positivity)
      _ ≤ (ENNReal.ofReal M) * ((Tube.volume_le.C n : ENNReal) * (δ_coarse : ENNReal) ^ (n - 1)) :=
        mul_le_mul_of_nonneg_left hvol_le (by positivity)
  have hfinite_left : (cardSet.card : ENNReal)
    * ((Tube.le_volume.c n : ENNReal) * (δ_fine : ENNReal) ^ (n - 1)) ≠ (⊤ : ENNReal) := by
    have h1 : (cardSet.card : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.natCast_ne_top _
    have h2 : (Tube.le_volume.c n : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
    have h3 : (δ_fine : ENNReal) ^ (n - 1) ≠ (⊤ : ENNReal) :=
      ENNReal.pow_ne_top ENNReal.coe_ne_top
    have h4 : (Tube.le_volume.c n : ENNReal) * (δ_fine : ENNReal) ^ (n - 1) ≠ (⊤ : ENNReal) :=
      ENNReal.mul_ne_top h2 h3
    exact ENNReal.mul_ne_top h1 h4
  have hfinite_right : (ENNReal.ofReal M)
    * ((Tube.volume_le.C n : ENNReal) * (δ_coarse : ENNReal) ^ (n - 1)) ≠ (⊤ : ENNReal) := by
    have h1 : (ENNReal.ofReal M : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.ofReal_ne_top
    have h2 : (Tube.volume_le.C n : ENNReal) ≠ (⊤ : ENNReal) := ENNReal.coe_ne_top
    have h3 : (δ_coarse : ENNReal) ^ (n - 1) ≠ (⊤ : ENNReal) :=
      ENNReal.pow_ne_top ENNReal.coe_ne_top
    have h4 : (Tube.volume_le.C n : ENNReal) * (δ_coarse : ENNReal) ^ (n - 1) ≠ (⊤ : ENNReal) :=
      ENNReal.mul_ne_top h2 h3
    exact ENNReal.mul_ne_top h1 h4
  have hcard_real : (cardSet.card : ℝ) * ((Tube.le_volume.c n : ℝ) * (δ_fine : ℝ) ^ (n - 1))
      ≤ M * ((Tube.volume_le.C n : ℝ) * (δ_coarse : ℝ) ^ (n - 1)) := by
    have htemp := ENNReal.toReal_mono hfinite_right hcard_ennreal
    simpa [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal hM,
      ENNReal.toReal_pow] using htemp
  set denom : ℝ := (Tube.le_volume.c n : ℝ) * (δ_fine : ℝ) ^ (n - 1) with hdenom_def
  have hdenom_pos : 0 < denom := by
    rw [hdenom_def]
    have hpow_pos : (0 : ℝ) < (δ_fine : ℝ) ^ (n - 1) := by positivity
    positivity
  have hcard_div : (cardSet.card : ℝ) ≤
    M * ((Tube.volume_le.C n : ℝ) * (δ_coarse : ℝ) ^ (n - 1)) / denom :=
    (le_div_iff₀ hdenom_pos).mpr hcard_real
  have hdiv_eq : M * ((Tube.volume_le.C n : ℝ) * (δ_coarse : ℝ) ^ (n - 1)) / denom
      = M * ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ))
        * ((δ_coarse : ℝ) / (δ_fine : ℝ)) ^ (n - 1) := by
    calc
      M * ((Tube.volume_le.C n : ℝ) * (δ_coarse : ℝ) ^ (n - 1)) / denom
          = M * ((Tube.volume_le.C n : ℝ) * (δ_coarse : ℝ) ^ (n - 1)) /
            ((Tube.le_volume.c n : ℝ) * (δ_fine : ℝ) ^ (n - 1)) := rfl
      _ = M * ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ))
            * (((δ_coarse : ℝ) ^ (n - 1)) / ((δ_fine : ℝ) ^ (n - 1))) := by ring
      _ = M * ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ))
            * ((δ_coarse : ℝ) / (δ_fine : ℝ)) ^ (n - 1) := by rw [div_pow]
  have hcard_div' : (cardSet.card : ℝ) ≤ M * ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ))
      * ((δ_coarse : ℝ) / (δ_fine : ℝ)) ^ (n - 1) :=
    hcard_div.trans (by rw [hdiv_eq])
  have hpow : ((δ_coarse : ℝ) / (δ_fine : ℝ)) ^ (n - 1)
      = ((δ_coarse : ℝ) / (δ_fine : ℝ)) ^ ((n : ℝ) - 1) := by
    rw [← Real.rpow_natCast ((δ_coarse : ℝ) / (δ_fine : ℝ)) (n - 1),
      Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  rw [hpow] at hcard_div'
  exact hcard_div'

open scoped Classical in
/-- **Child-count upper bound at the parent scale.**  The number of `ρ_f`-parents contained in a
fixed `ρ_c`-tube `K` is at most `Δ_max · (vol_le.C/le_vol.c) · (ρ_c/ρ_f)^(n-1)`.  Index-shaped
restatement of `card_tubes_in_tube_le_of_maxDensity` for a uniformity's parent family. -/
private lemma card_children_le_of_parent_maxDensity
    {ι : Type*} {δ ρ_f ρ_c C D : NNReal}
    (hρ_f_pos : 0 < ρ_f) (hρ_c_le : ρ_c ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} (u : Tube.IsUniformAtScale s T ρ_f C D)
    (K : Tube ρ_c E) (Dm : ℝ) (hDm : 0 ≤ Dm)
    (h_md : Kakeya.maxDensity (u.parent.image (fun i => u.parentTube i))
        (fun w : Tube ρ_f E => w.toConvexSpaceBody) ≤ ENNReal.ofReal Dm) :
    ((u.parent.filter (fun i => (u.parentTube i).toConvexSpaceBody
        ≤ K.toConvexSpaceBody)).card : ℝ)
      ≤ Dm * ((Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
            / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ))
        * ((ρ_c : ℝ) / (ρ_f : ℝ)) ^ ((Module.finrank ℝ E : ℝ) - 1) := by
  classical
  have h_md_idx : Kakeya.maxDensity u.parent (fun i => (u.parentTube i).toConvexSpaceBody) ≤
    ENNReal.ofReal Dm := by
    rw [Kakeya.maxDensity_le_iff]
    intro K
    calc
      Kakeya.densityIn u.parent (fun i => (u.parentTube i).toConvexSpaceBody) K
          = Kakeya.densityIn (u.parent.image (fun i => u.parentTube i))
              (fun w : Tube ρ_f E => w.toConvexSpaceBody) K := by
        unfold Kakeya.densityIn
        congr 1
        rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_image u.parentTube_injOn]
      _ ≤ Kakeya.maxDensity (u.parent.image (fun i => u.parentTube i))
              (fun w : Tube ρ_f E => w.toConvexSpaceBody) := Kakeya.le_maxDensity _ _ _
      _ ≤ ENNReal.ofReal Dm := h_md
  have hcard := card_tubes_in_tube_le_of_maxDensity hρ_f_pos hρ_c_le u.parent u.parentTube K Dm
    hDm h_md_idx
  simpa [Kakeya.familyIn] using hcard

open scoped Classical in
/-- **The `x_m ≳ (ρ_succ/ρ_cs)^ε` input of GWZ Lemma 7.5** (blueprint `lem:x_m_lower_bound`).  Given
the per-scale density hypothesis `Δ_max(𝕋_{ρ_f}) ≤ (ρ_c/ρ_f)^ε`, every Definition 2.1(iii) child
count `N₂` obeys `N₂ ≤ (vol_le.C/le_vol.c) · (ρ_c/ρ_f)^((n-1)+ε)`.  This is the bound that makes
`∏_m max{1,x_m} ≲ δ^{-ε} ∏_m x_m`. -/
lemma N₂_le_ratio_rpow_of_parent_maxDensity
    {ι : Type*} {δ ρ_f ρ_c C D : NNReal}
    (hρ_f_pos : 0 < ρ_f) (hρ_c_pos : 0 < ρ_c) (hρ_c_le : ρ_c ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} (u : Tube.IsUniformAtScale s T ρ_f C D)
    (K : Tube ρ_c E) (ε : ℝ)
    (h_md : Kakeya.maxDensity (u.parent.image (fun i => u.parentTube i))
        (fun w : Tube ρ_f E => w.toConvexSpaceBody)
      ≤ ENNReal.ofReal (((ρ_c : ℝ) / (ρ_f : ℝ)) ^ ε))
    (N₂ : ℕ)
    (hN₂ : (N₂ : ℝ) ≤ ((u.parent.filter (fun i => (u.parentTube i).toConvexSpaceBody
        ≤ K.toConvexSpaceBody)).card : ℝ)) :
    (N₂ : ℝ) ≤ ((Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
          / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ))
      * ((ρ_c : ℝ) / (ρ_f : ℝ)) ^ (((Module.finrank ℝ E : ℝ) - 1) + ε) := by
  set n := Module.finrank ℝ E with hn_def
  have hn_pos : 0 < n := Module.finrank_pos (R := ℝ) (M := E)
  have hρ_f_pos' : (0 : ℝ) < (ρ_f : ℝ) := by exact_mod_cast hρ_f_pos
  have hρ_c_pos' : (0 : ℝ) < (ρ_c : ℝ) := by exact_mod_cast hρ_c_pos
  have hratio_nonneg : 0 ≤ (ρ_c : ℝ) / (ρ_f : ℝ) := by positivity
  have hratio_pos : 0 < (ρ_c : ℝ) / (ρ_f : ℝ) := div_pos hρ_c_pos' hρ_f_pos'
  set Dm := ((ρ_c : ℝ) / (ρ_f : ℝ)) ^ ε with hDm_def
  have hDm_nonneg : 0 ≤ Dm := Real.rpow_nonneg hratio_nonneg ε
  have h_card := card_children_le_of_parent_maxDensity hρ_f_pos hρ_c_le u K Dm hDm_nonneg h_md
  have hN₂_trans : (N₂ : ℝ) ≤ Dm * ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ))
      * ((ρ_c : ℝ) / (ρ_f : ℝ)) ^ ((n : ℝ) - 1) :=
    le_trans hN₂ h_card
  calc
    (N₂ : ℝ) ≤ Dm * ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ))
        * ((ρ_c : ℝ) / (ρ_f : ℝ)) ^ ((n : ℝ) - 1) := hN₂_trans
    _ = ((ρ_c : ℝ) / (ρ_f : ℝ)) ^ ε * ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ))
        * ((ρ_c : ℝ) / (ρ_f : ℝ)) ^ ((n : ℝ) - 1) := by rw [hDm_def]
    _ = ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ))
        * (((ρ_c : ℝ) / (ρ_f : ℝ)) ^ ε * ((ρ_c : ℝ) / (ρ_f : ℝ)) ^ ((n : ℝ) - 1)) := by ring
    _ = ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ))
        * ((ρ_c : ℝ) / (ρ_f : ℝ)) ^ (ε + ((n : ℝ) - 1)) := by
      rw [← Real.rpow_add hratio_pos ε ((n : ℝ) - 1)]
    _ = ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ))
        * ((ρ_c : ℝ) / (ρ_f : ℝ)) ^ (((n : ℝ) - 1) + ε) := by ring_nf
    _ = ((Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
          / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ))
        * ((ρ_c : ℝ) / (ρ_f : ℝ)) ^ (((Module.finrank ℝ E : ℝ) - 1) + ε) := by
      simp [hn_def]

/-- **Katz–Tao density ⇒ cardinality bound.**  A `δ^(-η)`-Katz–Tao family of `δ`-tubes
in `B_1` has `|s|·δ^(n-1) ≤ C_dim·δ^(-η)` (apply Katz–Tao at scale `ρ = δ`, where the
rescaled bodies are the tubes themselves with per-tube volume `≥ le_volume.c·δ^(n-1)`,
all contained in `B_2`).  This is the regime ingredient for E2. -/
lemma katzTao_card_volume_bound {δ : NNReal} (hδ : 0 < δ) (_hδ1 : δ < 1)
    {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (hT_B1 : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (η : ℝ)
    (hKT : ConvexSpaceBody.IsKatzTao s (fun i => (T i).toConvexSpaceBody)
      (ENNReal.ofReal ((δ : ℝ) ^ (-η)))) :
    (s.card : ℝ) * (δ : ℝ) ^ (Module.finrank ℝ E - 1)
      ≤ (δ : ℝ) ^ (-η) * MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
          / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) := by
  classical
  set n := Module.finrank ℝ E with hn
  have hc_pos : (0 : ℝ) < (Tube.le_volume.c n : ℝ) := by exact_mod_cast Tube.le_volume.c_pos n
  have hKTδ : ConvexSpaceBody.IsKatzTao s (fun i => ((T i).rescale δ).toConvexSpaceBody)
      (ENNReal.ofReal ((δ : ℝ) ^ (-η))) := by
    simpa [Tube.toConvexSpaceBody_rescale_self] using hKT
  have hcar : ∀ i, ((T i).rescale δ).carrier = (T i).carrier := fun i => by
    have hx : ((T i).rescale δ).x = (T i).x := rfl
    have hy : ((T i).rescale δ).y = (T i).y := rfl
    rw [((T i).rescale δ).carrier_eq_cthickening, (T i).carrier_eq_cthickening, hx, hy]
  set K : ConvexSpaceBody E := ConvexSpaceBody.closedBall (0 : E) 2 (by norm_num) with hK
  have hKcar : (K : Set E) = Metric.closedBall (0 : E) 2 := rfl
  have h_sub : ∀ i ∈ s, ((T i).rescale δ).toConvexSpaceBody ≤ K := by
    intro i hi
    rw [← SetLike.coe_subset_coe, hKcar]
    change ((T i).rescale δ).carrier ⊆ Metric.closedBall (0 : E) 2
    rw [hcar i]
    exact (hT_B1 i hi).trans (Metric.closedBall_subset_closedBall (by norm_num))
  have h_vol_lb : ∀ i ∈ s, (Tube.le_volume.c n : ℝ) * (δ : ℝ) ^ (n - 1)
      ≤ MeasureTheory.volume.real ((T i).rescale δ).carrier := by
    intro i _
    have hreal := ENNReal.toReal_mono ((T i).rescale δ).isCompact.measure_lt_top.ne
      (Tube.le_volume (δ := δ) ((T i).rescale δ))
    rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, ENNReal.coe_toReal] at hreal
  have hmain := ConvexSpaceBody.IsKatzTao.card_mul_le_real
    hKTδ ENNReal.ofReal_ne_top h_sub h_vol_lb
  rw [ENNReal.toReal_ofReal (by positivity)] at hmain
  rw [le_div_iff₀ hc_pos]
  calc (s.card : ℝ) * (δ : ℝ) ^ (n - 1) * (Tube.le_volume.c n : ℝ)
      = (s.card : ℝ) * ((Tube.le_volume.c n : ℝ) * (δ : ℝ) ^ (n - 1)) := by ring
    _ ≤ (δ : ℝ) ^ (-η) * MeasureTheory.volume.real (K : Set E) := hmain
    _ = (δ : ℝ) ^ (-η) * MeasureTheory.volume.real (Metric.closedBall (0 : E) 2) := by rw [hKcar]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Carrier-injective subfamily that additionally **covers** every carrier value of `t`
(strengthening `exists_carrier_injOn_subset` with the cover clause needed by
`katzTao_carrier_multiplicity_bound`). -/
lemma exists_carrier_injOn_cover {κ : Type*} (t : Finset κ) (f : κ → Set E) :
    ∃ t' : Finset κ, t' ⊆ t ∧ Set.InjOn f (t' : Set κ) ∧ (t.Nonempty → t'.Nonempty) ∧
      (∀ a ∈ t, ∃ a' ∈ t', f a = f a') := by
  classical
  choose g hg_mem hg_eq using
    (fun b : {b : Set E // b ∈ t.image f} => Finset.mem_image.mp b.2)
  refine ⟨Finset.image g Finset.univ, ?_, ?_, ?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha
    obtain ⟨b, rfl⟩ := ha
    exact hg_mem b
  · intro a ha a' ha' hfa
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at ha ha'
    obtain ⟨b, rfl⟩ := ha
    obtain ⟨b', rfl⟩ := ha'
    exact congrArg g (Subtype.ext (by rw [← hg_eq b, ← hg_eq b', hfa]))
  · intro ht
    obtain ⟨a, ha⟩ := ht
    exact ⟨g ⟨f a, Finset.mem_image_of_mem f ha⟩, Finset.mem_image_of_mem g (Finset.mem_univ _)⟩
  · intro a ha
    exact ⟨g ⟨f a, Finset.mem_image_of_mem f ha⟩, Finset.mem_image_of_mem g (Finset.mem_univ _),
      (hg_eq ⟨f a, Finset.mem_image_of_mem f ha⟩).symm⟩

/-- **Katz–Tao ⇒ carrier-multiplicity bound** (regime-B ingredient for E2).  In a `δ^(-η)`-Katz–Tao
family every carrier is shared by at most `δ^(-η)·volume_le.C/le_volume.c` tubes — apply Katz–Tao at
`ρ = δ` to the fibre of tubes with that carrier — so the total count is at most that times the
number `|s₁|` of distinct carriers, `s₁` being any carrier-injective subfamily covering them all. -/
lemma katzTao_carrier_multiplicity_bound {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ < 1)
    {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (η : ℝ)
    (hKT : ConvexSpaceBody.IsKatzTao s (fun i => (T i).toConvexSpaceBody)
      (ENNReal.ofReal ((δ : ℝ) ^ (-η))))
    (s₁ : Finset ι) (hs₁_inj : Set.InjOn (fun i => (T i).carrier) (s₁ : Set ι))
    (hs₁_cover : ∀ i ∈ s, ∃ j ∈ s₁, (T i).carrier = (T j).carrier) :
    (s.card : ℝ) ≤
      ((δ : ℝ) ^ (-η) * (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
          / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)) * (s₁.card : ℝ) := by
  classical
  set n := Module.finrank ℝ E with hn
  set B : ℝ := (δ : ℝ) ^ (-η) * (Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ) with hB
  have hc_pos : (0 : ℝ) < (Tube.le_volume.c n : ℝ) := by exact_mod_cast Tube.le_volume.c_pos n
  have hδ_pos_real : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδpow_pos : (0 : ℝ) < (δ : ℝ) ^ (-η) := Real.rpow_pos_of_pos hδ_pos_real _
  have hpow_pos : (0 : ℝ) < (δ : ℝ) ^ (n - 1) := pow_pos hδ_pos_real _
  have hcar : ∀ i, ((T i).rescale δ).carrier = (T i).carrier := fun i => by
    have hx : ((T i).rescale δ).x = (T i).x := rfl
    have hy : ((T i).rescale δ).y = (T i).y := rfl
    rw [((T i).rescale δ).carrier_eq_cthickening, (T i).carrier_eq_cthickening, hx, hy]
  have hbodycar : ∀ i, (((T i).rescale δ).toConvexSpaceBody : Set E) = (T i).carrier := by
    intro i; rw [← hcar i]; rfl
  have hbody_of_carrier : ∀ i j, (T i).carrier = (T j).carrier →
      ((T i).rescale δ).toConvexSpaceBody = ((T j).rescale δ).toConvexSpaceBody := by
    intro i j hij
    apply SetLike.coe_injective
    rw [hbodycar i, hbodycar j, hij]
  have hfiber : ∀ j ∈ s₁,
      ((s.filter (fun i => (T i).carrier = (T j).carrier)).card : ℝ) ≤ B := by
    intro j _
    set F : Finset ι := s.filter (fun i => (T i).carrier = (T j).carrier) with hF
    have hFsub : F ⊆ s := Finset.filter_subset _ _
    have hKT_F : ConvexSpaceBody.IsKatzTao F
        (fun i => ((T i).rescale δ).toConvexSpaceBody)
        (ENNReal.ofReal ((δ : ℝ) ^ (-η))) := by
      simpa [Tube.toConvexSpaceBody_rescale_self] using hKT.subset hFsub
    set Kj : ConvexSpaceBody E := ((T j).rescale δ).toConvexSpaceBody with hKj
    have h_sub : ∀ i ∈ F, ((T i).rescale δ).toConvexSpaceBody ≤ Kj := by
      intro i hi
      have hci : (T i).carrier = (T j).carrier := (Finset.mem_filter.mp hi).2
      rw [hKj]; exact le_of_eq (hbody_of_carrier i j hci)
    have h_vol_lb : ∀ i ∈ F, (Tube.le_volume.c n : ℝ) * (δ : ℝ) ^ (n - 1)
        ≤ MeasureTheory.volume.real ((T i).rescale δ).carrier := by
      intro i _
      have hreal := ENNReal.toReal_mono ((T i).rescale δ).isCompact.measure_lt_top.ne
        (Tube.le_volume (δ := δ) ((T i).rescale δ))
      rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, ENNReal.coe_toReal] at hreal
    have hmain := ConvexSpaceBody.IsKatzTao.card_mul_le_real
      hKT_F ENNReal.ofReal_ne_top h_sub h_vol_lb
    rw [ENNReal.toReal_ofReal hδpow_pos.le] at hmain
    have hcarKj : Kj.carrier = (T j).carrier := by rw [hKj]; exact hcar j
    have hKj_vol_ub : MeasureTheory.volume.real Kj.carrier
        ≤ (Tube.volume_le.C n : ℝ) * (δ : ℝ) ^ (n - 1) := by
      rw [hcarKj]
      have hle := Tube.volume_le hδ1.le (T j)
      have hmono := ENNReal.toReal_mono ENNReal.coe_ne_top hle
      rwa [ENNReal.coe_toReal] at hmono
    have hcancel : (F.card : ℝ) * (Tube.le_volume.c n : ℝ)
        ≤ (δ : ℝ) ^ (-η) * (Tube.volume_le.C n : ℝ) := by
      have hL : (F.card : ℝ) * (Tube.le_volume.c n : ℝ) * (δ : ℝ) ^ (n - 1)
          ≤ (δ : ℝ) ^ (-η) * (Tube.volume_le.C n : ℝ) * (δ : ℝ) ^ (n - 1) := by
        calc (F.card : ℝ) * (Tube.le_volume.c n : ℝ) * (δ : ℝ) ^ (n - 1)
            = (F.card : ℝ) * ((Tube.le_volume.c n : ℝ) * (δ : ℝ) ^ (n - 1)) := by ring
          _ ≤ (δ : ℝ) ^ (-η) * MeasureTheory.volume.real Kj.carrier := hmain
          _ ≤ (δ : ℝ) ^ (-η) * ((Tube.volume_le.C n : ℝ) * (δ : ℝ) ^ (n - 1)) :=
              mul_le_mul_of_nonneg_left hKj_vol_ub hδpow_pos.le
          _ = (δ : ℝ) ^ (-η) * (Tube.volume_le.C n : ℝ) * (δ : ℝ) ^ (n - 1) := by ring
      exact le_of_mul_le_mul_right hL hpow_pos
    rw [hB, le_div_iff₀ hc_pos]
    exact hcancel
  have hcover_img : ∀ i ∈ s, (T i).carrier ∈ s₁.image (fun j => (T j).carrier) := by
    intro i hi
    obtain ⟨j, hj, hij⟩ := hs₁_cover i hi
    rw [hij]; exact Finset.mem_image_of_mem _ hj
  calc (s.card : ℝ)
      = ∑ c ∈ s₁.image (fun j => (T j).carrier),
          ((s.filter (fun i => (T i).carrier = c)).card : ℝ) := by
        rw [Finset.card_eq_sum_card_fiberwise hcover_img, Nat.cast_sum]
    _ = ∑ j ∈ s₁, ((s.filter (fun i => (T i).carrier = (T j).carrier)).card : ℝ) := by
        rw [Finset.sum_image
          (fun x hx y hy hxy => hs₁_inj (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy)]
    _ ≤ ∑ _j ∈ s₁, B := Finset.sum_le_sum hfiber
    _ = (s₁.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = B * (s₁.card : ℝ) := by ring

open Classical in
omit [Nontrivial E] in
/-- **Carrier-multiplicity bound from maxDensity** (E6 / `h_match` multiplicity core).  If a
carrier-injective `s_inj ⊆ s_src` covers every carrier of `s_src`, then any class of
`s_src`-elements sharing one body `W q` has cardinality at most `maxDensity s_src W`, so summing
over the `≤ |s_inj|` carrier classes gives `|s_src| ≤ Cmax · |s_inj|`, with no pairwise-ED input. -/
lemma card_le_maxDensity_mul_card_injOn
    {ι : Type*} (s_src s_inj : Finset ι) (W : ι → ConvexSpaceBody E)
    (hcover : ∀ p ∈ s_src, ∃ q ∈ s_inj, (W p).carrier = (W q).carrier)
    (hpos : ∀ q ∈ s_inj, 0 < MeasureTheory.volume (W q).carrier)
    (hfin : ∀ q ∈ s_inj, MeasureTheory.volume (W q).carrier ≠ ⊤)
    (Cmax : ENNReal) (h_md : Kakeya.maxDensity s_src W ≤ Cmax) :
    (s_src.card : ENNReal) ≤ Cmax * (s_inj.card : ENNReal) := by
  classical
  have h_class : ∀ q ∈ s_inj,
      ((s_src.filter (fun p => (W p).carrier = (W q).carrier)).card : ENNReal) ≤ Cmax := by
    intro q hq
    have hcount := Kakeya.densityIn_ge_of_count_volume (s := s_src) (W := W)
        (K := W q) (t := s_src.filter (fun p => (W p).carrier = (W q).carrier))
        (vmin := MeasureTheory.volume (W q).carrier)
        (Finset.filter_subset _ _)
        (fun i hi => le_of_eq (SetLike.coe_injective (Finset.mem_filter.mp hi).2))
        (fun i hi => (congrArg MeasureTheory.volume (Finset.mem_filter.mp hi).2).symm.le)
    rw [mul_div_assoc, ENNReal.div_self (hpos q hq).ne' (hfin q hq), mul_one] at hcount
    exact le_trans hcount (le_trans (Kakeya.le_maxDensity s_src W (W q)) h_md)
  have hcov : s_src ⊆ s_inj.biUnion
      (fun q => s_src.filter (fun p => (W p).carrier = (W q).carrier)) := by
    intro p hp
    obtain ⟨q, hq, heq⟩ := hcover p hp
    exact Finset.mem_biUnion.mpr ⟨q, hq, Finset.mem_filter.mpr ⟨hp, heq⟩⟩
  have hcard_nat : s_src.card
      ≤ ∑ q ∈ s_inj, (s_src.filter (fun p => (W p).carrier = (W q).carrier)).card :=
    le_trans (Finset.card_le_card hcov) Finset.card_biUnion_le
  calc (s_src.card : ENNReal)
      ≤ ((∑ q ∈ s_inj,
            (s_src.filter (fun p => (W p).carrier = (W q).carrier)).card : ℕ) : ENNReal) := by
        exact_mod_cast hcard_nat
    _ = ∑ q ∈ s_inj,
          ((s_src.filter (fun p => (W p).carrier = (W q).carrier)).card : ENNReal) := by
        rw [Nat.cast_sum]
    _ ≤ ∑ _q ∈ s_inj, Cmax := Finset.sum_le_sum h_class
    _ = (s_inj.card : ENNReal) * Cmax := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = Cmax * (s_inj.card : ENNReal) := mul_comm _ _

open scoped Pointwise Classical in
/-- **Leaf→parent maxDensity transfer.**  A `C`-uniform structure at scale `ρ` (with
`1 ≤ branchingN`) transfers the leaf Katz–Tao maxDensity bound `δ^(-η)`, read at the matched scale
`ρ` for the rescaled leaves, to the parent `ρ`-tube family, up to a dimensional constant.  No
`(ρ/δ)` blowup appears, the parents being volume-comparable to the rescaled leaves. -/
lemma uniform_parent_maxDensity_le
    {δ : NNReal} (hδ : 0 < δ) {ι : Type*} {s : Finset ι} {T : ι → Tube δ E}
    {ρ : NNReal} (hδρ : δ ≤ ρ) (hρ1 : ρ ≤ 1) {C : NNReal}
    (h : Tube.IsUniformAtScale s T ρ C) (hbr : 1 ≤ h.branchingN) {η : ℝ}
    (hKTρ : Kakeya.maxDensity s (fun i => ((T i).rescale ρ).toConvexSpaceBody)
              ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η))) :
    Kakeya.maxDensity (h.parent.image h.parentTube) (fun u : Tube ρ E => u.toConvexSpaceBody)
      ≤ (↑(Tube.volume_le.C (Module.finrank ℝ E)) / ↑(Tube.le_volume.c (Module.finrank ℝ E))
          * ↑C * 2 ^ Module.finrank ℝ E) * ENNReal.ofReal ((δ : ℝ) ^ (-η)) := by
  classical
  set n := Module.finrank ℝ E with hn_def
  have hρ_pos : (0 : ℝ) < (ρ : ℝ) :=
    lt_of_lt_of_le (by exact_mod_cast hδ) (by exact_mod_cast hδρ)
  have hρ_ne : (ρ : NNReal) ≠ 0 := by exact_mod_cast hρ_pos.ne'
  have hcn_pos : (0 : NNReal) < Tube.le_volume.c n := Tube.le_volume.c_pos _
  have hcn_ne : (↑(Tube.le_volume.c n) : ENNReal) ≠ 0 := by exact_mod_cast hcn_pos.ne'
  have hcn_top : (↑(Tube.le_volume.c n) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  rw [Kakeya.maxDensity_le_iff]
  intro K
  rcases eq_or_ne (volume K.carrier) 0 with hK0 | hK0
  · rw [Kakeya.densityIn_eq_zero_of_volume_eq_zero hK0]; exact bot_le
  have hresc_in : ∀ i, (T i).toConvexSpaceBody ≤ K →
      ((T i).rescale ρ).toConvexSpaceBody ≤ K.cthickening (ρ : ℝ) := by
    intro i hi z hz
    have hz' : z ∈ ((T i).rescale ρ).carrier := hz
    rw [((T i).rescale ρ).carrier_eq_cthickening] at hz'
    have hseg : segment ℝ ((T i).rescale ρ).x ((T i).rescale ρ).y ⊆ K.carrier := by
      intro p hp
      have hpT : p ∈ (T i).carrier := by
        rw [(T i).carrier_eq_cthickening]; exact Metric.self_subset_cthickening _ hp
      exact hi hpT
    exact Metric.cthickening_subset_of_subset (ρ : ℝ) hseg hz'
  set PK : Finset ι := h.parent.filter (fun j => (h.parentTube j).toConvexSpaceBody ≤ K)
    with hPK_def
  set FK : Finset ι := s.filter (fun i =>
    ((T i).rescale ρ).toConvexSpaceBody ≤ K.cthickening (ρ : ℝ))
    with hFK_def
  have hnum : (∑ u ∈ (h.parent.image h.parentTube) with u.toConvexSpaceBody ≤ K, volume u.carrier)
      = ∑ j ∈ PK, volume (h.parentTube j).carrier := by
    simp only [hPK_def, Finset.sum_filter]
    exact Finset.sum_image (fun a ha b hb hab =>
      h.parentTube_injOn (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab)
  have hrep : ∀ j ∈ PK, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (h.parentTube j).toConvexSpaceBody := by
    intro j hj
    have hjP : j ∈ h.parent := Finset.mem_of_mem_filter j hj
    have hlb := h.le_mul_card_filter hjP
    have hpos : 0 < ({i ∈ s | (T i).toConvexSpaceBody ≤
            (h.parentTube j).toConvexSpaceBody}).card := by
      rcases Nat.eq_zero_or_pos
        ({i ∈ s | (T i).toConvexSpaceBody ≤ (h.parentTube j).toConvexSpaceBody}).card with h0 | hp
      · exfalso
        rw [h0, Nat.cast_zero, mul_zero, nonpos_iff_eq_zero] at hlb
        rw [hlb] at hbr; exact absurd hbr (by norm_num)
      · exact hp
    obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hi₀
    exact ⟨i₀, hi₀.1, hi₀.2⟩
  let i_rep : ι → ι := fun j => if hj : j ∈ PK then (hrep j hj).choose else j
  have hi_rep_mem : ∀ j ∈ PK, i_rep j ∈ s := by
    intro j hj; simp only [i_rep, dif_pos hj]; exact (hrep j hj).choose_spec.1
  have hi_rep_le : ∀ j ∈ PK,
      (T (i_rep j)).toConvexSpaceBody ≤ (h.parentTube j).toConvexSpaceBody := by
    intro j hj; simp only [i_rep, dif_pos hj]; exact (hrep j hj).choose_spec.2
  have hpar_le : ∀ j ∈ PK, volume (h.parentTube j).carrier
      ≤ (↑(Tube.volume_le.C n) / ↑(Tube.le_volume.c n)) *
          volume ((T (i_rep j)).rescale ρ).carrier := by
    intro j hj
    have hpar : volume (h.parentTube j).carrier
      ≤ ↑(Tube.volume_le.C n) * (↑ρ : ENNReal) ^ (n - 1) := by
      have := Tube.volume_le hρ1 (h.parentTube j)
      rw [hn_def]; exact this
    have hleaf : (↑(Tube.le_volume.c n) : ENNReal) * (↑ρ : ENNReal) ^ (n - 1)
        ≤ volume ((T (i_rep j)).rescale ρ).carrier := by
      have := Tube.le_volume ((T (i_rep j)).rescale ρ)
      rw [hn_def]; exact this
    calc volume (h.parentTube j).carrier
        ≤ ↑(Tube.volume_le.C n) * (↑ρ : ENNReal) ^ (n - 1) := hpar
      _ = (↑(Tube.volume_le.C n) / ↑(Tube.le_volume.c n))
        * (↑(Tube.le_volume.c n) * (↑ρ : ENNReal) ^ (n - 1)) := by
            rw [← mul_assoc, ENNReal.div_mul_cancel hcn_ne hcn_top]
      _ ≤ (↑(Tube.volume_le.C n) / ↑(Tube.le_volume.c n))
        * volume ((T (i_rep j)).rescale ρ).carrier :=
            mul_le_mul_right hleaf _
  have hcount : ∀ i ∈ s, ((PK.filter (fun j => i_rep j = i)).card : ENNReal)
      ≤ (if ((T i).rescale ρ).toConvexSpaceBody ≤ K.cthickening (ρ : ℝ)
              then (↑C : ENNReal) else 0) := by
    intro i hi
    by_cases hQ : ((T i).rescale ρ).toConvexSpaceBody ≤ K.cthickening (ρ : ℝ)
    · rw [if_pos hQ]
      have hsub : PK.filter (fun j => i_rep j = i)
          ⊆ h.parent.filter (fun j => (T i).toConvexSpaceBody ≤
              (h.parentTube j).toConvexSpaceBody) := by
        intro j hj
        rw [Finset.mem_filter] at hj ⊢
        refine ⟨Finset.mem_of_mem_filter j hj.1, ?_⟩
        have := hi_rep_le j hj.1
        rwa [hj.2] at this
      calc ((PK.filter (fun j => i_rep j = i)).card : ENNReal)
          ≤ ((h.parent.filter (fun j =>
              (T i).toConvexSpaceBody ≤ (h.parentTube j).toConvexSpaceBody)).card : ENNReal) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ (↑C : ENNReal) := by
            have := h.parents_containing_tube_card_le hδρ (T i) hi (le_refl _)
            exact_mod_cast this
    · rw [if_neg hQ]
      have hempty : PK.filter (fun j => i_rep j = i) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro j hj hji
        apply hQ
        have hjPK : j ∈ PK := hj
        have hle_parent : (h.parentTube j).toConvexSpaceBody ≤ K := (Finset.mem_filter.mp hjPK).2
        have hTiK : (T i).toConvexSpaceBody ≤ K := by
          have := hi_rep_le j hjPK
          rw [hji] at this
          exact this.trans hle_parent
        exact hresc_in i hTiK
      rw [hempty, Finset.card_empty, Nat.cast_zero]
  set D0 : ENNReal := ↑(Tube.volume_le.C n) / ↑(Tube.le_volume.c n) with hD0_def
  have hdc : ∑ j ∈ PK, volume ((T (i_rep j)).rescale ρ).carrier
      ≤ ↑C * ∑ i ∈ FK, volume ((T i).rescale ρ).carrier := by
    rw [← Finset.sum_fiberwise_of_maps_to hi_rep_mem
          (fun j => volume ((T (i_rep j)).rescale ρ).carrier)]
    calc ∑ i ∈ s, ∑ j ∈ PK with i_rep j = i, volume ((T (i_rep j)).rescale ρ).carrier
        = ∑ i ∈ s, ((PK.filter (fun j => i_rep j = i)).card : ENNReal)
            * volume ((T i).rescale ρ).carrier := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2]),
            Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s, (if ((T i).rescale ρ).toConvexSpaceBody ≤ K.cthickening (ρ : ℝ)
              then (↑C : ENNReal) else 0) * volume ((T i).rescale ρ).carrier :=
          Finset.sum_le_sum (fun i hi => mul_le_mul_left (hcount i hi) _)
      _ = ∑ i ∈ s, (if ((T i).rescale ρ).toConvexSpaceBody ≤ K.cthickening (ρ : ℝ)
              then (↑C : ENNReal) * volume ((T i).rescale ρ).carrier else 0) := by
          refine Finset.sum_congr rfl (fun i _ => ?_); rw [ite_mul, zero_mul]
      _ = ∑ i ∈ FK, (↑C : ENNReal) * volume ((T i).rescale ρ).carrier := by
          rw [hFK_def, Finset.sum_filter]
      _ = ↑C * ∑ i ∈ FK, volume ((T i).rescale ρ).carrier := by rw [Finset.mul_sum]
  have hKp_ne : volume (K.cthickening (ρ : ℝ)).carrier ≠ 0 := by
    have hsub : K.carrier ⊆ (K.cthickening (ρ : ℝ)).carrier := Metric.self_subset_cthickening _
    exact fun hz => hK0 (measure_mono_null hsub hz)
  have hKp_top : volume (K.cthickening (ρ : ℝ)).carrier ≠ ⊤ :=
    (K.cthickening (ρ : ℝ)).isCompact.measure_lt_top.ne
  have hKTplus : ∑ i ∈ FK, volume ((T i).rescale ρ).carrier
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η)) * volume (K.cthickening (ρ : ℝ)).carrier := by
    have hle : Kakeya.densityIn s (fun i => ((T i).rescale ρ).toConvexSpaceBody)
          (K.cthickening (ρ : ℝ)) ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η)) :=
      le_trans (Kakeya.le_maxDensity _ _ _) hKTρ
    exact (Kakeya.densityIn_le_iff _ _ _ _).mp hle
  rcases PK.eq_empty_or_nonempty with hPKe | hPKne
  · refine (Kakeya.densityIn_le_iff _ _ _ _).mpr ?_
    rw [hnum, hPKe, Finset.sum_empty]
    exact bot_le
  · obtain ⟨j₀, hj₀⟩ := hPKne
    have hball : Metric.closedBall ((h.parentTube j₀).x) (ρ : ℝ) ⊆ K.carrier := by
      have h1 : Metric.closedBall ((h.parentTube j₀).x) (ρ : ℝ) ⊆ (h.parentTube j₀).carrier := by
        rw [(h.parentTube j₀).carrier_eq]
        exact fun w hw => Set.mem_biUnion (left_mem_segment ℝ _ _) hw
      exact h1.trans (Finset.mem_filter.mp hj₀).2
    have hKplus : volume (K.cthickening (ρ : ℝ)).carrier ≤ 2 ^ n * volume K.carrier := by
      have hlem := volume_cthickening_le_of_closedBall_subset (K := K.carrier)
        K.isCompact K.convex hρ_pos hball (t := (ρ : ℝ)) hρ_pos
      have heq : ENNReal.ofReal (((ρ : ℝ) + (ρ : ℝ)) / (ρ : ℝ)) ^ Module.finrank ℝ E = 2 ^ n := by
        rw [show ((ρ : ℝ) + (ρ : ℝ)) / (ρ : ℝ) = 2 by rw [div_eq_iff hρ_pos.ne']; ring,
          ENNReal.ofReal_ofNat, hn_def]
      rw [heq] at hlem; exact hlem
    have hKt : volume K.carrier ≠ ⊤ := K.isCompact.measure_lt_top.ne
    have hmain : (∑ j ∈ PK, volume (h.parentTube j).carrier)
        ≤ (D0 * ↑C * 2 ^ n) * ENNReal.ofReal ((δ : ℝ) ^ (-η)) * volume K.carrier := by
      calc ∑ j ∈ PK, volume (h.parentTube j).carrier
          ≤ ∑ j ∈ PK, D0 * volume ((T (i_rep j)).rescale ρ).carrier := Finset.sum_le_sum hpar_le
        _ = D0 * ∑ j ∈ PK, volume ((T (i_rep j)).rescale ρ).carrier := by rw [Finset.mul_sum]
        _ ≤ D0 * (↑C * ∑ i ∈ FK, volume ((T i).rescale ρ).carrier) :=
          mul_le_mul_right hdc (D0 : ENNReal)
        _ ≤ D0 * (↑C * (ENNReal.ofReal ((δ : ℝ) ^ (-η))
              * volume (K.cthickening (ρ : ℝ)).carrier)) :=
            mul_le_mul_right (mul_le_mul_right hKTplus (↑C : ENNReal)) (D0 : ENNReal)
        _ ≤ D0 * (↑C * (ENNReal.ofReal ((δ : ℝ) ^ (-η)) * (2 ^ n * volume K.carrier))) :=
            mul_le_mul_right
            (mul_le_mul_right (mul_le_mul_right hKplus
              (ENNReal.ofReal ((δ : ℝ) ^ (-η)))) (↑C : ENNReal))
            (D0 : ENNReal)
        _ = (D0 * ↑C * 2 ^ n) * ENNReal.ofReal ((δ : ℝ) ^ (-η)) * volume K.carrier := by ring
    refine (Kakeya.densityIn_le_iff _ _ _ _).mpr ?_
    rw [hnum]
    exact hmain.trans (le_of_eq (by ring))

/-- The bounded-overlap per-scale constant for a `ρ / 4`-separated tube net: the multiplicity with
which the nodes of such a net can meet one common tube of the same radius.  Introduced here, above
its first consumer `sinj_B_bound`; `_root_` because this file sits inside `Kakeya.StickyKakeya`. -/
def _root_.Tube.overlapConstBO (n : ℕ) : ℕ := 2 * (385 * n + 1) ^ (2 * n)

/-- **E5 `|s_inj|` cardinality bound** (extracted for heartbeat reasons): the carrier-injective,
ED-refined index `s_inj ⊆ s'_SSF ⊆ s₂ ×ˢ R_SSF` has
`(2·overlapBO)²·|s_inj| ≤ C₀·δ^(-(n-1+η_KT))` with dimensional `C₀`.  Combines the SSF
`R_SSF`-count (`hR_card_sharp`) with the Katz–Tao `|s|`-bound (`katzTao_card_volume_bound`). -/
lemma sinj_B_bound {ι : Type*} {δ : NNReal} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (η_KT : ℝ) (hη_KT_pos : 0 < η_KT)
    (s s₂ : Finset ι) (s_inj s'_SSF : Finset (ι × E)) (R_SSF : Finset E) (_C_R : ℝ)
    (hs_inj_sub : s_inj ⊆ s'_SSF) (hs'_SSF_sub : s'_SSF ⊆ s₂ ×ˢ R_SSF)
    (hs₂_ne : s₂.Nonempty) (hs₂_sub : s₂ ⊆ s)
    (hR_card_sharp : (R_SSF.card : ℝ) ≤ _C_R
        * max 1 ((s₂.card : ℝ) * (δ : ℝ) ^ ((Module.finrank ℝ E : ℝ) - 1))⁻¹)
    (C_q : ℝ) (hC_q_nn : 0 ≤ C_q) (hC_R_le2 : _C_R ≤ C_q)
    (T : ι → Tube δ E) (hT_B1 : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hKT : ConvexSpaceBody.IsKatzTao s (fun i => (T i).toConvexSpaceBody)
      (ENNReal.ofReal ((δ : ℝ) ^ (-η_KT)))) :
    (((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 * s_inj.card : ℕ) : ℝ)
      ≤ (((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 : ℕ) : ℝ)
          * (C_q * (MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
                / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) + 1))
          * (δ : ℝ) ^ (-((Module.finrank ℝ E : ℝ) - 1 + η_KT)) := by
  classical
  set n := Module.finrank ℝ E with hn_def
  have hδ_pos_real : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
  have hδ1r : (δ : ℝ) < 1 := by exact_mod_cast hδ_lt_one
  have hn1 : 1 ≤ n := Module.finrank_pos
  have hexp : (δ : ℝ) ^ (n - 1) = (δ : ℝ) ^ ((n : ℝ) - 1) := by
    rw [← Real.rpow_natCast (δ : ℝ) (n - 1), Nat.cast_sub hn1, Nat.cast_one]
  have hδr1_pos : (0 : ℝ) < (δ : ℝ) ^ ((n : ℝ) - 1) := Real.rpow_pos_of_pos hδ_pos_real _
  have hs2_pos : (0 : ℝ) < (s₂.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs₂_ne
  set Ckt : ℝ := MeasureTheory.volume.real (Metric.closedBall (0 : E) 2)
    / (Tube.le_volume.c n : ℝ) with hCkt
  have hCkt_nn : (0 : ℝ) ≤ Ckt := by rw [hCkt]; positivity
  have hs_card : (s.card : ℝ) ≤ Ckt * (δ : ℝ) ^ (-((n : ℝ) - 1 + η_KT)) := by
    have hkt := katzTao_card_volume_bound hδ_pos hδ_lt_one s T hT_B1 η_KT hKT
    rw [hexp, mul_div_assoc, ← hCkt] at hkt
    have hmul : (s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1)
        ≤ Ckt * (δ : ℝ) ^ (-((n : ℝ) - 1 + η_KT)) * (δ : ℝ) ^ ((n : ℝ) - 1) := by
      refine hkt.trans (le_of_eq ?_)
      rw [mul_assoc, ← Real.rpow_add hδ_pos_real,
        show -((n : ℝ) - 1 + η_KT) + ((n : ℝ) - 1) = -η_KT by ring, mul_comm]
    exact le_of_mul_le_mul_right hmul hδr1_pos
  have hR2 : (R_SSF.card : ℝ) ≤ C_q * max 1 ((s₂.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹ := by
    refine le_trans hR_card_sharp ?_
    exact mul_le_mul_of_nonneg_right hC_R_le2 (le_trans zero_le_one (le_max_left _ _))
  have hcancel : (s₂.card : ℝ) * ((s₂.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹
      = (δ : ℝ) ^ (-((n : ℝ) - 1)) := by
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hs2_pos.ne', one_mul,
      ← Real.rpow_neg hδ_pos_real.le]
  have hsmax : (s₂.card : ℝ) * max 1 ((s₂.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹
      ≤ (s₂.card : ℝ) + (δ : ℝ) ^ (-((n : ℝ) - 1)) := by
    have hmaxle : max 1 ((s₂.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹
        ≤ 1 + ((s₂.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹ := by
      have hi : (0 : ℝ) ≤ ((s₂.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹ := by positivity
      rcases le_total 1 ((s₂.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹ with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    calc (s₂.card : ℝ) * max 1 ((s₂.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹
        ≤ (s₂.card : ℝ) * (1 + ((s₂.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹) :=
          mul_le_mul_of_nonneg_left hmaxle hs2_pos.le
      _ = (s₂.card : ℝ)
          + (s₂.card : ℝ) * ((s₂.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹ := by ring
      _ = (s₂.card : ℝ) + (δ : ℝ) ^ (-((n : ℝ) - 1)) := by rw [hcancel]
  have hmono : (δ : ℝ) ^ (-((n : ℝ) - 1)) ≤ (δ : ℝ) ^ (-((n : ℝ) - 1 + η_KT)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos_real hδ1r.le (by linarith [hη_KT_pos])
  have hsinj_le : (s_inj.card : ℝ)
      ≤ C_q * (Ckt + 1) * (δ : ℝ) ^ (-((n : ℝ) - 1 + η_KT)) := by
    have hsinj_nat : s_inj.card ≤ s₂.card * R_SSF.card :=
      le_trans (Finset.card_le_card hs_inj_sub)
        (le_trans (Finset.card_le_card hs'_SSF_sub) (le_of_eq (Finset.card_product _ _)))
    have hsinj_r : (s_inj.card : ℝ) ≤ (s₂.card : ℝ) * (R_SSF.card : ℝ) := by
      exact_mod_cast hsinj_nat
    have hs₂card_le : (s₂.card : ℝ) ≤ Ckt * (δ : ℝ) ^ (-((n : ℝ) - 1 + η_KT)) :=
      le_trans (by exact_mod_cast Finset.card_le_card hs₂_sub) hs_card
    calc (s_inj.card : ℝ) ≤ (s₂.card : ℝ) * (R_SSF.card : ℝ) := hsinj_r
      _ ≤ (s₂.card : ℝ) * (C_q * max 1 ((s₂.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹) :=
          mul_le_mul_of_nonneg_left hR2 hs2_pos.le
      _ = C_q * ((s₂.card : ℝ) * max 1 ((s₂.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹) := by ring
      _ ≤ C_q * ((s₂.card : ℝ) + (δ : ℝ) ^ (-((n : ℝ) - 1))) :=
          mul_le_mul_of_nonneg_left hsmax hC_q_nn
      _ ≤ C_q * (Ckt * (δ : ℝ) ^ (-((n : ℝ) - 1 + η_KT))
              + (δ : ℝ) ^ (-((n : ℝ) - 1 + η_KT))) :=
          mul_le_mul_of_nonneg_left (add_le_add hs₂card_le hmono) hC_q_nn
      _ = C_q * (Ckt + 1) * (δ : ℝ) ^ (-((n : ℝ) - 1 + η_KT)) := by ring
  have hX_nn : (0 : ℝ) ≤ (((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 : ℕ) : ℝ) := by
    positivity
  calc (((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 * s_inj.card : ℕ) : ℝ)
      = (((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 : ℕ) : ℝ) * (s_inj.card : ℝ) := by
        push_cast; ring
    _ ≤ (((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 : ℕ) : ℝ)
        * (C_q * (Ckt + 1) * (δ : ℝ) ^ (-((n : ℝ) - 1 + η_KT))) :=
        mul_le_mul_of_nonneg_left hsinj_le hX_nn
    _ = (((2 * Tube.overlapConstBO (Module.finrank ℝ E)) ^ 2 : ℕ) : ℝ)
        * (C_q * (Ckt + 1)) * (δ : ℝ) ^ (-((n : ℝ) - 1 + η_KT)) := by ring

/-- Twice the bounded-overlap constant `Tube.overlapConstBO n` dominates `4`. -/
lemma four_le_two_overlapConstBO (n : ℕ) :
    (4 : NNReal) ≤ 2 * (Tube.overlapConstBO n : NNReal) := by
  have h2 : (2 : ℕ) ≤ Tube.overlapConstBO n := by
    change 2 ≤ 2 * (385 * n + 1) ^ (2 * n)
    have hk : 1 ≤ (385 * n + 1) ^ (2 * n) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  calc (4 : NNReal) = 2 * 2 := by norm_num
    _ ≤ 2 * (Tube.overlapConstBO n : NNReal) := by gcongr; exact_mod_cast h2
end stickyKatzTaoOfStickyFrostman

end StickyKakeya

end Kakeya
