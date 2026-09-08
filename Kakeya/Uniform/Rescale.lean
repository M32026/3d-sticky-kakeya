/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Density
public import Kakeya.Frostman
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Rescaling bridges between a tube and its ancestor

Three geometric bridges relating a `δ`-tube to a coarser tube containing it: the ancestor's body
sits in a bounded rescale of the leaf, its carrier sits in a cthickening, and the leaf-anchored
fibre density is controlled after rescaling and translating.
-/

@[expose] public section


open MeasureTheory
open scoped ENNReal

namespace Tube

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

/-- If a `δ`-tube `T` sits inside a `ρ`-tube `A` (as convex bodies), then `A`'s
body sits inside the `(4ρ)`-rescale of `T`.  The constant `4` is dimension-independent
and, crucially, this holds with no relation between `δ` and `ρ`: the only geometric
input is that `T`'s axis segment lies within `ρ` of `A`'s axis segment (which follows
from `seg T ⊆ T.carrier ⊆ A.carrier = cthickening ρ (seg A)`). -/
theorem body_le_rescale_of_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {δ ρ : NNReal} (T : Tube δ E) (A : Tube ρ E)
    (hTA : T.toConvexSpaceBody ≤ A.toConvexSpaceBody) :
    A.toConvexSpaceBody ≤ (T.rescale (4 * ρ)).toConvexSpaceBody := by
  have hρ_nn : (0 : ℝ) ≤ (ρ : ℝ) := ρ.coe_nonneg
  have hT_carrier : T.carrier = Metric.cthickening (δ : ℝ) (segment ℝ T.x T.y) :=
    T.carrier_eq_cthickening
  have hA_carrier : A.carrier = Metric.cthickening (ρ : ℝ) (segment ℝ A.x A.y) :=
    A.carrier_eq_cthickening
  have h4_carrier : (T.rescale (4 * ρ)).carrier
      = Metric.cthickening ((4 : ℝ) * (ρ : ℝ)) (segment ℝ T.x T.y) := by
    rw [(T.rescale (4 * ρ)).carrier_eq_cthickening]
    norm_cast
  have hT_unit : ‖T.y - T.x‖ = 1 := T.norm_direction
  have hA_unit : ‖A.y - A.x‖ = 1 := A.norm_direction
  have hTA_carrier : T.carrier ⊆ A.carrier := hTA
  have hclose : ∀ p ∈ segment ℝ T.x T.y,
      ∃ q ∈ segment ℝ A.x A.y, dist p q ≤ (ρ : ℝ) := by
    intro p hp
    have hp_carrier : p ∈ T.carrier := by
      rw [hT_carrier]; exact Metric.self_subset_cthickening _ hp
    have hp_A : p ∈ A.carrier := hTA_carrier hp_carrier
    rw [hA_carrier, Metric.mem_cthickening_iff] at hp_A
    obtain ⟨q, hq_mem, hq_dist⟩ :=
      isCompact_segment.exists_infDist_eq_dist ⟨A.x, left_mem_segment ℝ _ _⟩ p
    refine ⟨q, hq_mem, ?_⟩
    rw [← hq_dist]
    have : Metric.infDist p (segment ℝ A.x A.y)
        = (Metric.infEDist p (segment ℝ A.x A.y)).toReal := rfl
    rw [this]
    calc (Metric.infEDist p (segment ℝ A.x A.y)).toReal
        ≤ (ENNReal.ofReal (ρ : ℝ)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hp_A
      _ = (ρ : ℝ) := ENNReal.toReal_ofReal hρ_nn
  have hsym := Tube.symm_hausdorff_segment hT_unit hA_unit hρ_nn hclose
  intro z hz
  have hz' : z ∈ A.carrier := hz
  rw [hA_carrier, Metric.mem_cthickening_iff] at hz'
  change z ∈ (T.rescale (4 * ρ)).carrier
  rw [h4_carrier, Metric.mem_cthickening_iff]
  obtain ⟨q, hq_mem, hq_dist⟩ :=
    isCompact_segment.exists_infDist_eq_dist ⟨A.x, left_mem_segment ℝ _ _⟩ z
  have hzq_le : dist z q ≤ (ρ : ℝ) := by
    rw [← hq_dist]
    have : Metric.infDist z (segment ℝ A.x A.y)
        = (Metric.infEDist z (segment ℝ A.x A.y)).toReal := rfl
    rw [this]
    calc (Metric.infEDist z (segment ℝ A.x A.y)).toReal
        ≤ (ENNReal.ofReal (ρ : ℝ)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hz'
      _ = (ρ : ℝ) := ENNReal.toReal_ofReal hρ_nn
  obtain ⟨wseg, hw_mem, hw_dist⟩ := hsym q hq_mem
  have hzw : dist z wseg ≤ (4 : ℝ) * (ρ : ℝ) := by
    have := dist_triangle z q wseg
    linarith [this, hzq_le, hw_dist]
  calc Metric.infEDist z (segment ℝ T.x T.y)
      ≤ edist z wseg := Metric.infEDist_le_edist_of_mem hw_mem
    _ = ENNReal.ofReal (dist z wseg) := by rw [edist_dist]
    _ ≤ ENNReal.ofReal ((4 : ℝ) * (ρ : ℝ)) := ENNReal.ofReal_le_ofReal hzw

theorem ancestor_body_subset_cthickening_of_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {δ ρ : NNReal} (T : Tube δ E) (A : Tube ρ E)
    (hTA : T.toConvexSpaceBody ≤ A.toConvexSpaceBody)
    (K : ConvexSpaceBody E) (hTK : T.toConvexSpaceBody ≤ K) :
    A.toConvexSpaceBody ≤ K.cthickening (4 * (ρ : ℝ)) := by
  refine (body_le_rescale_of_le T A hTA).trans ?_
  intro z hz
  have hz' : z ∈ (T.rescale (4 * ρ)).carrier := hz
  rw [(T.rescale (4 * ρ)).carrier_eq_cthickening] at hz'
  have hseg : segment ℝ (T.rescale (4 * ρ)).x (T.rescale (4 * ρ)).y = segment ℝ T.x T.y := rfl
  rw [hseg] at hz'
  have hsegT : segment ℝ T.x T.y ⊆ K.carrier := by
    intro p hp
    have hpT : p ∈ T.carrier := by
      rw [T.carrier_eq_cthickening]; exact Metric.self_subset_cthickening _ hp
    exact hTK hpT
  change z ∈ (K.cthickening (4 * (ρ : ℝ))).carrier
  change z ∈ Metric.cthickening (4 * (ρ : ℝ)) K.carrier
  have hmono : Metric.cthickening ((4 : ℝ) * (ρ : ℝ)) (segment ℝ T.x T.y)
      ⊆ Metric.cthickening ((4 : ℝ) * (ρ : ℝ)) K.carrier :=
    Metric.cthickening_subset_of_subset _ hsegT
  exact hmono hz'

open scoped Classical in
/-- **Katz–Tao transfer to a fattened, prefix-translated fibre.**  For a family `W` of `ρs`-tubes
and a fibre `F` of nodes obtained from the `S`-indexed one-step translates by a *common* prefix
offset `v`: if the `S`-indexed translated family has `maxDensity ≤ B`, then the fibre's fattened
tubes obey the same bound up to the factor `5 * volume_le.C n / le_volume.c n * 3 ^ (n - 1)`.
This turns eq. (53) of GWZ Lemma 7.5 into the Katz–Tao input of the Lemma 7.4 engine. -/
theorem maxDensity_fibre_rescale_translate_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} {ρs σs : NNReal} (hρs_pos : 0 < ρs)
    (hle : ρs ≤ σs) (hσs_le_four : σs ≤ 4) (hσs_ratio : (σs : ℝ) ≤ 3 * (ρs : ℝ))
    (W : ι → Tube ρs E) (v : E)
    (F S : Finset (ι × E)) (g : (ι × E) → (ι × E))
    (hg_mem : ∀ q ∈ F, g q ∈ S)
    (hg_eq : ∀ q ∈ F, q = ((g q).1, v + (g q).2))
    (B : ℝ) (hB : 0 ≤ B)
    (hmax : Kakeya.maxDensity S
              (fun pr : ι × E => ((W pr.1).translate pr.2).toConvexSpaceBody)
            ≤ ENNReal.ofReal B) :
    Kakeya.maxDensity F
        (fun q : ι × E => (((W q.1).rescale σs).translate q.2).toConvexSpaceBody)
      ≤ ENNReal.ofReal
        (5 * (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
            / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
          * 3 ^ (Module.finrank ℝ E - 1) * B) := by
  set n := Module.finrank ℝ E with hn_def
  set C_n := (Tube.volume_le.C n : ℝ) with hC_n_def
  set c_n := (Tube.le_volume.c n : ℝ) with hc_n_def
  have hc_n_pos : 0 < c_n := by exact_mod_cast Tube.le_volume.c_pos n
  have hρs_pos_r : (0 : ℝ) < (ρs : ℝ) := by exact_mod_cast hρs_pos
  have hσs_pos_r : (0 : ℝ) < (σs : ℝ) := by exact_mod_cast (hρs_pos.trans_le hle)
  have hρs_nn : (0 : ℝ) ≤ (ρs : ℝ) := NNReal.coe_nonneg _
  have hσs_nn : (0 : ℝ) ≤ (σs : ℝ) := NNReal.coe_nonneg _
  set V : (ι × E) → Tube ρs E := fun pr => (W pr.1).translate pr.2 with hV_def
  set U : (ι × E) → Tube σs E := fun pr => ((W pr.1).rescale σs).translate pr.2 with hU_def
  have hg_inj_on_F : ∀ a ∈ F, ∀ b ∈ F, g a = g b → a = b := by
    intro a ha b hb hgab
    have ha_eq := hg_eq a ha
    have hb_eq := hg_eq b hb
    rw [ha_eq, hb_eq, hgab]
  have hbody_eq (q : ι × E) (hq : q ∈ F) : (U q).toConvexSpaceBody
      = ((U (g q)).translate v).toConvexSpaceBody := by
    have hq1 : q.1 = (g q).1 := by
      simpa using congrArg Prod.fst (hg_eq q hq)
    have hq2 : q.2 = v + (g q).2 := by
      simpa using congrArg Prod.snd (hg_eq q hq)
    dsimp [U]
    rw [hq1, hq2]
    calc
      (((W (g q).1).rescale σs).translate (v + (g q).2)).toConvexSpaceBody
          = ConvexSpaceBody.translate
              ((W (g q).1).rescale σs).toConvexSpaceBody (v + (g q).2) := rfl
      _ = ConvexSpaceBody.translate
            (ConvexSpaceBody.translate ((W (g q).1).rescale σs).toConvexSpaceBody (g q).2) v := by
        rw [ConvexSpaceBody.translate_translate, add_comm]
      _ = ((((W (g q).1).rescale σs).translate (g q).2).translate v).toConvexSpaceBody := rfl
  have maxDensity_reindex_g (W' : (ι × E) → ConvexSpaceBody E) :
    Kakeya.maxDensity (F.image g) (fun pr : ι × E => W' pr)
      = Kakeya.maxDensity F (fun q : ι × E => W' (g q)) := by
    have key : ∀ K : ConvexSpaceBody E,
        Kakeya.densityIn (F.image g) (fun pr : ι × E => W' pr) K
          = Kakeya.densityIn F (fun q : ι × E => W' (g q)) K := by
      intro K
      unfold Kakeya.densityIn
      congr 1
      calc
        ∑ pr ∈ ((F.image g).filter fun pr : ι × E => W' pr ≤ K), volume ((W' pr).carrier)
            = ∑ pr ∈ F.image g, (if W' pr ≤ K then volume ((W' pr).carrier) else 0) := by
              rw [Finset.sum_filter]
        _ = ∑ q ∈ F, (if W' (g q) ≤ K then volume ((W' (g q)).carrier) else 0) := by
          rw [Finset.sum_image (fun a ha b hb h => hg_inj_on_F a ha b hb h)]
        _ = ∑ q ∈ (F.filter fun q : ι × E => W' (g q) ≤ K), volume ((W' (g q)).carrier) := by
          rw [Finset.sum_filter]
    apply le_antisymm
    · rw [Kakeya.maxDensity_le_iff]; intro K; rw [key]; exact Kakeya.le_maxDensity _ _ _
    · rw [Kakeya.maxDensity_le_iff]; intro K; rw [← key]; exact Kakeya.le_maxDensity _ _ _
  have h_peel :
    Kakeya.maxDensity F (fun q : ι × E => (U q).toConvexSpaceBody)
      ≤ Kakeya.maxDensity (F.image g) (fun pr : ι × E => (U pr).toConvexSpaceBody) :=
    (calc
      Kakeya.maxDensity F (fun q : ι × E => (U q).toConvexSpaceBody)
          = Kakeya.maxDensity F (fun q : ι × E => ((U (g q)).translate v).toConvexSpaceBody) :=
        Kakeya.maxDensity_congr (fun q hq => hbody_eq q hq)
      _ = Kakeya.maxDensity (F.image g)
          (fun pr : ι × E => ((U pr).translate v).toConvexSpaceBody) := by
        rw [maxDensity_reindex_g (fun pr : ι × E => ((U pr).translate v).toConvexSpaceBody)]
      _ = Kakeya.maxDensity (F.image g) (fun pr : ι × E => (U pr).toConvexSpaceBody) := by
        have h_body : (fun pr : ι × E => ((U pr).translate v).toConvexSpaceBody)
            = (fun pr : ι × E => ConvexSpaceBody.translate (U pr).toConvexSpaceBody v) := by
          ext pr; rfl
        rw [h_body, Kakeya.maxDensity_translate (F.image g)
      (fun pr : ι × E => (U pr).toConvexSpaceBody) v]
    ).le
  have h_commute (pr : ι × E) : (U pr).toConvexSpaceBody
      = ((V pr).rescale σs).toConvexSpaceBody := by
    calc
      (U pr).toConvexSpaceBody = (((W pr.1).rescale σs).translate pr.2).toConvexSpaceBody := rfl
      _ = (((W pr.1).translate pr.2).rescale σs).toConvexSpaceBody := by
        rw [Tube.translate_rescale_swap (W pr.1) pr.2 σs]
      _ = ((V pr).rescale σs).toConvexSpaceBody := rfl
  have h_commute_maxDensity :
    Kakeya.maxDensity (F.image g) (fun pr : ι × E => (U pr).toConvexSpaceBody)
      = Kakeya.maxDensity (F.image g) (fun pr : ι × E => ((V pr).rescale σs).toConvexSpaceBody) :=
    Kakeya.maxDensity_congr (fun pr _ => h_commute pr)
  have hFg_sub_S : F.image g ⊆ S := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨q, hq, rfl⟩
    exact hg_mem q hq
  have hstep : Kakeya.maxDensity (F.image g)
        (fun pr : ι × E => ((W pr.1).translate pr.2).toConvexSpaceBody)
      ≤ ENNReal.ofReal B :=
    le_trans ((Kakeya.maxDensity_mono
      (fun pr : ι × E => ((W pr.1).translate pr.2).toConvexSpaceBody)) hFg_sub_S) hmax
  have h_div_nonneg : 0 ≤ (σs : ℝ) / (ρs : ℝ) := div_nonneg hσs_nn hρs_nn
  have h_div : (σs : ℝ) / (ρs : ℝ) ≤ 3 := by
    calc
      (σs : ℝ) / (ρs : ℝ) = (σs : ℝ) * ((ρs : ℝ)⁻¹) := by rw [div_eq_mul_inv]
      _ ≤ (3 * (ρs : ℝ)) * ((ρs : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_right hσs_ratio (by positivity : 0 ≤ (ρs : ℝ)⁻¹)
      _ = 3 := by field_simp [hρs_pos_r.ne']
  have h_ratio_pow : ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1) ≤ 3 ^ (n - 1) := by
    have h_nonneg_base : 0 ≤ (σs : ℝ) / (ρs : ℝ) := div_nonneg hσs_nn hρs_nn
    exact pow_le_pow_left₀ h_nonneg_base h_div (n - 1 : ℕ)
  calc
    Kakeya.maxDensity F (fun q : ι × E => (((W q.1).rescale σs).translate q.2).toConvexSpaceBody)
        = Kakeya.maxDensity F (fun q : ι × E => (U q).toConvexSpaceBody) := rfl
    _ ≤ Kakeya.maxDensity (F.image g) (fun pr : ι × E => (U pr).toConvexSpaceBody) := h_peel
    _ = Kakeya.maxDensity (F.image g) (fun pr : ι × E => ((V pr).rescale σs).toConvexSpaceBody) :=
      h_commute_maxDensity
    _ ≤ ENNReal.ofReal
          (5 * (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
              / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
            * ((σs : ℝ) / (ρs : ℝ)) ^ (Module.finrank ℝ E - 1) * B) := by
      rw [Kakeya.maxDensity_le_iff]
      intro K
      rw [Kakeya.densityIn_le_iff]
      set t := (F.image g).filter (fun pr => ((V pr).rescale σs).toConvexSpaceBody ≤ K) with ht_def
      set t' := (F.image g).filter (fun pr => (V pr).toConvexSpaceBody ≤ K) with ht'_def
      have ht_sub_t' : t ⊆ t' := by
        intro i hi
        have hi' := Finset.mem_filter.mp hi
        rcases hi' with ⟨hi_s, hi_body⟩
        have h_main : (V i).toConvexSpaceBody ≤ K :=
          (Tube.le_rescale (V i) hle).trans hi_body
        exact Finset.mem_filter.mpr ⟨hi_s, h_main⟩
      have hvol_bound (i : ι × E) :
          volume (((V i).rescale σs).carrier) ≤
            (5 * ENNReal.ofReal (C_n / c_n * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1)))
            * volume ((V i).carrier) := by
        -- The `b = 4` instance of `Tube.volume_le_of_le`: the fattened scale `σs ≤ 3 * ρs`
        -- exceeds `1`, so the `δ ≤ 1` bound `Tube.volume_le` does not apply here.  Its constant
        -- `2 ^ n * (1 + 4)` is relaxed to `5 * volume_le.C n = 5 * 2 ^ (n + 1)`.
        have hvol_le : volume (((V i).rescale σs).carrier)
            ≤ (5 * Tube.volume_le.C n : ℝ≥0∞) * (σs : ℝ≥0∞) ^ (n - 1) := by
          refine (Tube.volume_le_of_le hσs_le_four ((V i).rescale σs)).trans ?_
          have hC : ((2 : NNReal) ^ n * (1 + 4) : NNReal) ≤ 5 * Tube.volume_le.C n := by
            unfold Tube.volume_le.C
            rw [pow_succ]
            calc (2 : NNReal) ^ n * (1 + 4)
                = 5 * 2 ^ n := by ring
              _ ≤ 5 * (2 ^ n * 2) := by
                  gcongr
                  exact le_mul_of_one_le_right zero_le one_le_two
          calc (((2 : NNReal) ^ n * (1 + 4) * σs ^ (n - 1) : NNReal) : ENNReal)
              ≤ ((5 * Tube.volume_le.C n * σs ^ (n - 1) : NNReal) : ENNReal) :=
                ENNReal.coe_le_coe.mpr (mul_le_mul_left hC (σs ^ (n - 1)))
            _ = 5 * (Tube.volume_le.C n : ℝ≥0∞) * (σs : ℝ≥0∞) ^ (n - 1) := by
                push_cast
                ring
        have h_vol_lb : (Tube.le_volume.c n : ℝ≥0∞) * (ρs : ℝ≥0∞) ^ (n - 1) ≤
          volume ((V i).carrier) :=
          Tube.le_volume (V i)
        have h_σs_div_ρs_enn_eq : (σs : ℝ≥0∞) / (ρs : ℝ≥0∞) =
          ENNReal.ofReal ((σs : ℝ) / (ρs : ℝ)) := by
          calc
            (σs : ℝ≥0∞) / (ρs : ℝ≥0∞) =
              (ENNReal.ofReal (σs : ℝ)) / (ENNReal.ofReal (ρs : ℝ)) := by simp
            _ = ENNReal.ofReal ((σs : ℝ) / (ρs : ℝ)) := by
              rw [(ENNReal.ofReal_div_of_pos hρs_pos_r).symm]
        have h_pow_eq : (σs : ℝ≥0∞) ^ (n - 1) = ((σs : ℝ≥0∞) / (ρs : ℝ≥0∞)) ^ (n - 1)
            * (ρs : ℝ≥0∞) ^ (n - 1) := by
          calc
            (σs : ℝ≥0∞) ^ (n - 1) = (((σs : ℝ≥0∞) / (ρs : ℝ≥0∞)) * (ρs : ℝ≥0∞)) ^ (n - 1) := by
              have hρs_coe_ne_zero : (ρs : ℝ≥0∞) ≠ 0 := by exact_mod_cast hρs_pos.ne'
              have hρs_coe_ne_top : (ρs : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
              rw [ENNReal.div_mul_cancel' (fun hzero => (hρs_coe_ne_zero hzero).elim)
                (fun hinf => (hρs_coe_ne_top hinf).elim)]
            _ = ((σs : ℝ≥0∞) / (ρs : ℝ≥0∞)) ^ (n - 1) * (ρs : ℝ≥0∞) ^ (n - 1) := by rw [mul_pow]
        have hσs_coe_ne_zero : (σs : ℝ≥0∞) ≠ 0 := by exact_mod_cast hρs_pos.trans_le hle |>.ne'
        have hσs_coe_ne_top : (σs : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
        have hc_n_enn_ne_zero : (Tube.le_volume.c n : ℝ≥0∞) ≠ 0 := by
          exact_mod_cast (Tube.le_volume.c_pos n).ne'
        have hc_n_enn_ne_top : (Tube.le_volume.c n : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
        have h_algebraic : (Tube.volume_le.C n : ℝ≥0∞) * (σs : ℝ≥0∞) ^ (n - 1) =
            (ENNReal.ofReal (C_n / c_n * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1)))
              * ((Tube.le_volume.c n : ℝ≥0∞) * (ρs : ℝ≥0∞) ^ (n - 1)) := by
          calc
            (Tube.volume_le.C n : ℝ≥0∞) * (σs : ℝ≥0∞) ^ (n - 1)
                = ((Tube.volume_le.C n : ℝ≥0∞) / (Tube.le_volume.c n : ℝ≥0∞))
                  * (Tube.le_volume.c n : ℝ≥0∞) * (σs : ℝ≥0∞) ^ (n - 1) := by
              rw [ENNReal.div_mul_cancel' (fun hzero => (hc_n_enn_ne_zero hzero).elim)
                (fun hinf => (hc_n_enn_ne_top hinf).elim)]
            _ = ((Tube.volume_le.C n : ℝ≥0∞) / (Tube.le_volume.c n : ℝ≥0∞))
                * (Tube.le_volume.c n : ℝ≥0∞)
                * (((σs : ℝ≥0∞) / (ρs : ℝ≥0∞)) ^ (n - 1) * (ρs : ℝ≥0∞) ^ (n - 1)) := by
              rw [h_pow_eq]
            _ = ((Tube.volume_le.C n : ℝ≥0∞) / (Tube.le_volume.c n : ℝ≥0∞))
                * ((σs : ℝ≥0∞) / (ρs : ℝ≥0∞)) ^ (n - 1)
                * ((Tube.le_volume.c n : ℝ≥0∞) * (ρs : ℝ≥0∞) ^ (n - 1)) := by ring
            _ = (ENNReal.ofReal (C_n / c_n * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1)))
                * ((Tube.le_volume.c n : ℝ≥0∞) * (ρs : ℝ≥0∞) ^ (n - 1)) := by
              calc
                ((Tube.volume_le.C n : ℝ≥0∞) / (Tube.le_volume.c n : ℝ≥0∞))
                    * ((σs : ℝ≥0∞) / (ρs : ℝ≥0∞)) ^ (n - 1)
                    * ((Tube.le_volume.c n : ℝ≥0∞) * (ρs : ℝ≥0∞) ^ (n - 1))
                  = ((ENNReal.ofReal C_n / ENNReal.ofReal c_n)
                      * ((ENNReal.ofReal ((σs : ℝ) / (ρs : ℝ))) ^ (n - 1)))
                      * ((Tube.le_volume.c n : ℝ≥0∞) * (ρs : ℝ≥0∞) ^ (n - 1)) := by
                    simp [hC_n_def, hc_n_def, h_σs_div_ρs_enn_eq]
                _ = (ENNReal.ofReal (C_n / c_n)
                    * ((ENNReal.ofReal ((σs : ℝ) / (ρs : ℝ))) ^ (n - 1)))
                    * ((Tube.le_volume.c n : ℝ≥0∞) * (ρs : ℝ≥0∞) ^ (n - 1)) := by
                  simp [ENNReal.ofReal_div_of_pos hc_n_pos]
                _ = (ENNReal.ofReal ((C_n / c_n) * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1)))
                    * ((Tube.le_volume.c n : ℝ≥0∞) * (ρs : ℝ≥0∞) ^ (n - 1)) := by
                  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ C_n / c_n),
                    ENNReal.ofReal_pow h_div_nonneg]
                _ = (ENNReal.ofReal (C_n / c_n * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1)))
                    * ((Tube.le_volume.c n : ℝ≥0∞) * (ρs : ℝ≥0∞) ^ (n - 1)) := rfl
        calc
          volume (((V i).rescale σs).carrier) ≤ (5 * Tube.volume_le.C n : ℝ≥0∞)
            * (σs : ℝ≥0∞) ^ (n - 1) := hvol_le
          _ = 5 * ((Tube.volume_le.C n : ℝ≥0∞) * (σs : ℝ≥0∞) ^ (n - 1)) := by ring
          _ = 5 * ((ENNReal.ofReal (C_n / c_n * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1)))
              * ((Tube.le_volume.c n : ℝ≥0∞) * (ρs : ℝ≥0∞) ^ (n - 1))) := by rw [h_algebraic]
          _ = (5 * ENNReal.ofReal (C_n / c_n * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1)))
              * ((Tube.le_volume.c n : ℝ≥0∞) * (ρs : ℝ≥0∞) ^ (n - 1)) := by ring
          _ ≤ (5 * ENNReal.ofReal (C_n / c_n * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1)))
              * volume ((V i).carrier) := by
            gcongr
      calc
        ∑ i ∈ t, volume (((V i).rescale σs).carrier)
            ≤ ∑ i ∈ t, ((5 * ENNReal.ofReal (C_n / c_n * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1)))
                * volume ((V i).carrier)) :=
          Finset.sum_le_sum fun i hi => hvol_bound i
        _ = (5 * ENNReal.ofReal (C_n / c_n * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1)))
            * (∑ i ∈ t, volume ((V i).carrier)) := by
          rw [Finset.mul_sum]
        _ ≤ (5 * ENNReal.ofReal (C_n / c_n * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1)))
            * (∑ i ∈ t', volume ((V i).carrier)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset ht_sub_t') ?_
          positivity
        _ ≤ (5 * ENNReal.ofReal (C_n / c_n * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1)))
            * (Kakeya.maxDensity (F.image g) (fun pr => (V pr).toConvexSpaceBody)
              * volume K.carrier) := by
          gcongr
          apply Kakeya.sum_volume_le_maxDensity_mul_volume
        _ ≤ (5 * ENNReal.ofReal (C_n / c_n * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1)))
            * (ENNReal.ofReal B * volume K.carrier) := by
          gcongr
        _ = ((5 * ENNReal.ofReal (C_n / c_n * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1)))
                * ENNReal.ofReal B) * volume K.carrier := by ring
        _ = ENNReal.ofReal ((5 * C_n / c_n) * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1) * B)
              * volume K.carrier := by
          calc
            ((5 * ENNReal.ofReal (C_n / c_n * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1)))
              * ENNReal.ofReal B) * volume K.carrier
                = (5 * (ENNReal.ofReal (C_n / c_n * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1))
                * ENNReal.ofReal B)) * volume K.carrier := by ring
            _ = (5 * ENNReal.ofReal ((C_n / c_n * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1)) * B))
                  * volume K.carrier := by
              rw [ENNReal.ofReal_mul
                (by positivity : 0 ≤ C_n / c_n * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1))]
            _ = ENNReal.ofReal (5 * ((C_n / c_n * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1)) * B))
                * volume K.carrier := by
              have : (5 : ℝ≥0∞) = ENNReal.ofReal (5 : ℝ) := by norm_num
              rw [this, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (5 : ℝ))]
            _ = ENNReal.ofReal ((5 * C_n / c_n) * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1) * B)
                * volume K.carrier := by
              congr 1
              field_simp [hc_n_pos.ne']
    _ ≤ ENNReal.ofReal
          (5 * (Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
              / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
            * 3 ^ (Module.finrank ℝ E - 1) * B) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have hC_n_nn : 0 ≤ C_n := by
        dsimp [C_n, Tube.volume_le.C]; positivity
      have h_factor : 5 * C_n / c_n * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1) * B
          ≤ 5 * C_n / c_n * 3 ^ (n - 1) * B := by
        calc
          5 * C_n / c_n * ((σs : ℝ) / (ρs : ℝ)) ^ (n - 1) * B
              = (5 * C_n / c_n) * (((σs : ℝ) / (ρs : ℝ)) ^ (n - 1) * B) := by ring
          _ ≤ (5 * C_n / c_n) * (3 ^ (n - 1) * B) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h_ratio_pow hB) (by positivity)
          _ = 5 * C_n / c_n * 3 ^ (n - 1) * B := by ring
      dsimp [C_n, c_n]
      exact h_factor

end Tube
