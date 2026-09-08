/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.GridScale
public import Kakeya.RandomTranslation.TranslationProb
public import Kakeya.Shading

/-!
# GWZ Lemma 7.5: the honest translation count

The scale-free arithmetic behind the per-scale translation set `R k` of GWZ Lemma 7.5: that the
count `J k = max {1, ⌈x_k⌉}` is admissible for the random-translation calibration, and that the
resulting product telescopes.  Nothing here mentions the hierarchy; the geometry enters only in
`Kakeya.StickyKakeya.subStickyFrostmanLemma.perScaleDeltaMax`, which consumes these.
-/

@[expose] public section

open MeasureTheory Real Metric ConvexSpaceBody
open scoped Topology
open Tube

namespace Kakeya


namespace StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-! ### Ingredients of the honest `J k = max {1, ⌈x_k⌉}` translation count

GWZ Lemma 7.5 builds, at each scale `k`, a translation set of size
`|R k| ∼ max {1, x_k}` with `x_k = (ρ_{k-1}/ρ_k)^{n-1} / N₂ k`
(blueprint `\eqref{cardRk}`).  The four lemmas below are the scale-free
arithmetic that makes that count admissible and that telescopes it:

* `le_volume_c_le_volume_le_C` — the two tube-volume constants are ordered;
* `jval_bracket` — `max {1, ⌈x⌉} ∼ max {1, x}`;
* `calibration_core` — with `J = max {1, ⌈x⌉}` the random-translation calibration
  still holds, at the price of a
  dimensional factor.  This is where the child-count *upper* bound and the
  `x_m` lower bound (blueprint `lem:x_m_lower_bound`) enter; they replace the
  collapse hypothesis `(ρ_{k-1}/ρ_k)^{n-1} ≤ N₂ k`, which is false as soon as
  `|s| ≪ δ^{-(n-1)}`;
* `prod_max_le` / `prod_x_le` — the blueprint's telescoping
  `∏_m max {1, x_m} ≤ δ^{-ε} · max {1, ∏_m x_m}` and
  `∏_m x_m ≲ (|s| · δ^{n-1})^{-1}` (blueprint `lem:composed_translation_family`).
  The `δ^{-ε}` is the price of the mixed regime and cannot be removed:
  `∏_m max {1, x_m} ≲ max {1, ∏_m x_m}` is false (`M = 2`, `x_1 = t`,
  `x_2 = 1/t`). -/

/-- The tube-volume lower constant never exceeds the upper one: both bounds apply to
one unit-scale tube. -/
lemma le_volume_c_le_volume_le_C :
    (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)
      ≤ (Tube.volume_le.C (Module.finrank ℝ E) : ℝ) := by
  let n := Module.finrank ℝ E
  have hδ1 : (1 : NNReal) ≤ 1 := le_rfl
  rcases exists_ne (0 : E) with ⟨v, hv⟩
  have hv_norm_pos : 0 < ‖v‖ := by
    rw [norm_pos_iff]
    exact hv
  let e : E := ‖v‖⁻¹ • v
  have h_e_norm : ‖e‖ = 1 := by
    dsimp [e]
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have h_dist : dist (0 : E) e = 1 := by
    simp [dist_eq_norm, h_e_norm]
  let T : Tube (1 : NNReal) E := Tube.mk' (1 : NNReal) h_dist
  have hle_vol : (Tube.le_volume.c n : ENNReal) * (1 : ENNReal) ^ (n - 1) ≤ volume T.carrier :=
    Tube.le_volume T
  have hvol_le : volume T.carrier ≤ (Tube.volume_le.C n : ENNReal) * (1 : ENNReal) ^ (n - 1) :=
    Tube.volume_le hδ1 T
  have h_ineq : (Tube.le_volume.c n : ENNReal) * (1 : ENNReal) ^ (n - 1) ≤
      (Tube.volume_le.C n : ENNReal) * (1 : ENNReal) ^ (n - 1) :=
    hle_vol.trans hvol_le
  have h_pow_ne_zero : (1 : ENNReal) ^ (n - 1) ≠ 0 := by simp
  have h_pow_ne_top : (1 : ENNReal) ^ (n - 1) ≠ ⊤ := by simp
  have h_vol_const_le : (Tube.le_volume.c n : ENNReal) ≤ (Tube.volume_le.C n : ENNReal) :=
    ((ENNReal.mul_le_mul_iff_left h_pow_ne_zero h_pow_ne_top).mp h_ineq)
  exact_mod_cast h_vol_const_le

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- `max {1, ⌈x⌉₊} ∼ max {1, x}` with the explicit constants `1` and `2`.  This is the
whole content of "`|q_m| ∼ max {1, x_m}`" once `q_m` is realised as `Fin (J k)`. -/
lemma jval_bracket {x : ℝ} (hx : 0 ≤ x) :
    max 1 x ≤ ((max 1 ⌈x⌉₊ : ℕ) : ℝ) ∧ ((max 1 ⌈x⌉₊ : ℕ) : ℝ) ≤ 2 * max 1 x := by
  have hmax_cast : ((max 1 ⌈x⌉₊ : ℕ) : ℝ) = max (1 : ℝ) ((Nat.ceil x : ℝ)) := by
    simp [Nat.cast_max]
  have hleft : max 1 x ≤ ((max 1 ⌈x⌉₊ : ℕ) : ℝ) := by
    calc
      max 1 x ≤ max (1 : ℝ) ((Nat.ceil x : ℝ)) :=
        max_le_max (le_refl 1) (Nat.le_ceil x)
      _ = ((max 1 ⌈x⌉₊ : ℕ) : ℝ) := by simp [Nat.cast_max]
  have hright : ((max 1 ⌈x⌉₊ : ℕ) : ℝ) ≤ 2 * max 1 x := by
    calc
      ((max 1 ⌈x⌉₊ : ℕ) : ℝ) = max (1 : ℝ) ((Nat.ceil x : ℝ)) := by simp [Nat.cast_max]
      _ ≤ max (2 * max 1 x) (2 * max 1 x) := by
        refine max_le_max ?_ ?_
        · have h1 : 1 ≤ max 1 x := le_max_left 1 x
          nlinarith
        · have hx_le_max : x ≤ max 1 x := le_max_right 1 x
          have h1_le_max : 1 ≤ max 1 x := le_max_left 1 x
          have hceil_lt_add_one : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
          nlinarith
      _ = 2 * max 1 x := by simp
  exact And.intro hleft hright

/-- **The random-translation calibration survives the honest translation count.**  With
`J = max {1, ⌈(ρ_c/ρ_f)^{n-1} / N₂⌉₊}` the calibration hypothesis of the joint random-translation
lemma still holds, with the scale-free constant inflated by `2 · Cn²`.  The two inputs replacing the
collapse hypothesis are `|children| ≤ Cn · N₂` and `N₂ ≤ Cn · (ρ_c/ρ_f)^{(n-1)+ε}`. -/
lemma calibration_core
    {ρ_f ρ_c : NNReal} (hρ_f_pos : 0 < (ρ_f : ℝ)) (hρ_c_pos : 0 < (ρ_c : ℝ))
    (hρ_le : (ρ_f : ℝ) ≤ (ρ_c : ℝ))
    {ε : ℝ} (hε : 0 < ε)
    {Cn : ℝ} (hCn : 1 ≤ Cn)
    {N₂ : ℕ} (hN₂ : 0 < N₂)
    {card : ℕ} (hcard : (card : ℝ) ≤ Cn * (N₂ : ℝ))
    (hN₂_xm : (N₂ : ℝ)
      ≤ Cn * ((ρ_c : ℝ) / (ρ_f : ℝ)) ^ (((Module.finrank ℝ E : ℝ) - 1) + ε))
    {K_pack : ℝ}
    (hK_pack : ((Tube.volume_le.C (Module.finrank ℝ E) : ℝ) *
        (ρ_c : ℝ) ^ (Module.finrank ℝ E - 1)) *
        Kakeya.probConst E (ρ_c : ℝ) + 1 ≤ K_pack) :
    ((max 1 ⌈((ρ_c : ℝ) / (ρ_f : ℝ)) ^ ((Module.finrank ℝ E : ℝ) - 1) / (N₂ : ℝ)⌉₊ : ℕ) : ℝ)
        * (card : ℝ) * Kakeya.probConst E (ρ_c : ℝ) *
          ((Tube.le_volume.c (Module.finrank ℝ E) : ℝ) *
            (ρ_f : ℝ) ^ (Module.finrank ℝ E - 1))
      < 2 * Cn ^ 2 * K_pack * ((ρ_c : ℝ) / (ρ_f : ℝ)) ^ ε := by
  set n := Module.finrank ℝ E with hn_def
  let V_lb := (Tube.le_volume.c n : ℝ) * (ρ_f : ℝ) ^ (n - 1)
  let V_ub := (Tube.volume_le.C n : ℝ) * (ρ_c : ℝ) ^ (n - 1)
  change V_ub * Kakeya.probConst E (ρ_c : ℝ) + 1 ≤ K_pack at hK_pack
  change ((max 1 ⌈((ρ_c : ℝ) / (ρ_f : ℝ)) ^ ((n : ℝ) - 1) / (N₂ : ℝ)⌉₊ : ℕ) : ℝ) *
      (card : ℝ) * Kakeya.probConst E (ρ_c : ℝ) * V_lb <
        2 * Cn ^ 2 * K_pack * ((ρ_c : ℝ) / (ρ_f : ℝ)) ^ ε
  have hn_pos : 0 < n := Module.finrank_pos
  have h_exp_nonneg : 0 ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
    linarith
  set t := (ρ_c : ℝ) / (ρ_f : ℝ) with ht_def
  have ht_pos : 0 < t := div_pos hρ_c_pos hρ_f_pos
  have ht_ge_one : 1 ≤ t := by
    rw [ht_def]
    exact (one_le_div hρ_f_pos (a := (ρ_c : ℝ))).mpr hρ_le
  have hΛ_nonneg : 0 ≤ t ^ ((n : ℝ) - 1) := Real.rpow_nonneg ht_pos.le _
  have hΛ_pos : 0 < t ^ ((n : ℝ) - 1) := Real.rpow_pos_of_pos ht_pos _
  have hx_nonneg : 0 ≤ t ^ ((n : ℝ) - 1) / (N₂ : ℝ) :=
    div_nonneg hΛ_nonneg (by exact_mod_cast hN₂.le)
  have ht_pow_eps_ge_one : 1 ≤ t ^ ε :=
    Real.one_le_rpow (by exact ht_ge_one) (by exact hε.le)
  have hΛ_ge_one : 1 ≤ t ^ ((n : ℝ) - 1) :=
    Real.one_le_rpow (by exact ht_ge_one) (by exact h_exp_nonneg)
  have hN₂_coe_pos : (0 : ℝ) < (N₂ : ℝ) := by exact_mod_cast hN₂
  have hN₂_coe_ne_zero : (N₂ : ℝ) ≠ 0 := by linarith
  have hN₂_card_nonneg : 0 ≤ (card : ℝ) := by exact_mod_cast Nat.zero_le _
  set J := ((max 1 ⌈t ^ ((n : ℝ) - 1) / (N₂ : ℝ)⌉₊ : ℕ) : ℝ) with hJ_def
  have hJ_nonneg : 0 ≤ J := by
    rw [hJ_def]; positivity
  have hJ_le_x_plus_one : J ≤ t ^ ((n : ℝ) - 1) / (N₂ : ℝ) + 1 := by
    rw [hJ_def]
    calc
      ((max 1 ⌈t ^ ((n : ℝ) - 1) / (N₂ : ℝ)⌉₊ : ℕ) : ℝ)
          = max (1 : ℝ) ((⌈t ^ ((n : ℝ) - 1) / (N₂ : ℝ)⌉₊ : ℕ) : ℝ) := by
            simp
      _ ≤ t ^ ((n : ℝ) - 1) / (N₂ : ℝ) + 1 := by
        refine max_le ?_ ?_
        · nlinarith [hΛ_nonneg, hN₂_coe_pos]
        · have hceil : (⌈t ^ ((n : ℝ) - 1) / (N₂ : ℝ)⌉₊ : ℝ) <
              t ^ ((n : ℝ) - 1) / (N₂ : ℝ) + 1 :=
            Nat.ceil_lt_add_one hx_nonneg
          nlinarith
  have hJ_card_le : J * (card : ℝ) ≤ Cn * (t ^ ((n : ℝ) - 1) + (N₂ : ℝ)) := by
    calc
      J * (card : ℝ) ≤ (t ^ ((n : ℝ) - 1) / (N₂ : ℝ) + 1) * (card : ℝ) :=
        mul_le_mul_of_nonneg_right hJ_le_x_plus_one hN₂_card_nonneg
      _ = (t ^ ((n : ℝ) - 1) / (N₂ : ℝ)) * (card : ℝ) + (card : ℝ) := by ring
      _ ≤ (t ^ ((n : ℝ) - 1) / (N₂ : ℝ)) * (Cn * (N₂ : ℝ)) + Cn * (N₂ : ℝ) := by
        nlinarith
      _ = Cn * (t ^ ((n : ℝ) - 1) + (N₂ : ℝ)) := by
        field_simp [hN₂_coe_ne_zero]
  have hN₂_le : (N₂ : ℝ) ≤ Cn * t ^ ((n : ℝ) - 1) * t ^ ε := by
    have hN₂_xm' : (N₂ : ℝ) ≤ Cn * t ^ (((n : ℝ) - 1) + ε) := by
      simpa [ht_def, hn_def] using hN₂_xm
    have h_rpow_add : t ^ (((n : ℝ) - 1) + ε) = t ^ ((n : ℝ) - 1) * t ^ ε :=
  Real.rpow_add ht_pos ((n : ℝ) - 1) ε
    rw [h_rpow_add] at hN₂_xm'
    calc
      (N₂ : ℝ) ≤ Cn * (t ^ ((n : ℝ) - 1) * t ^ ε) := hN₂_xm'
      _ = Cn * t ^ ((n : ℝ) - 1) * t ^ ε := by ring
  have h_sum_le : t ^ ((n : ℝ) - 1) + (N₂ : ℝ) ≤ 2 * Cn * t ^ ((n : ℝ) - 1) * t ^ ε := by
    have hN₂_le' : (N₂ : ℝ) ≤ Cn * t ^ ((n : ℝ) - 1) * t ^ ε := hN₂_le
    have hCn_pos : 0 < Cn := by linarith
    have hΛ_nonneg' : 0 ≤ t ^ ((n : ℝ) - 1) := hΛ_nonneg
    have h_mul : 1 + Cn * t ^ ε ≤ Cn * t ^ ε + Cn * t ^ ε := by
      have h1 : 1 ≤ Cn * t ^ ε := calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ Cn * t ^ ε := mul_le_mul hCn ht_pow_eps_ge_one (by norm_num) (by positivity)
      nlinarith
    calc
      t ^ ((n : ℝ) - 1) + (N₂ : ℝ)
          ≤ t ^ ((n : ℝ) - 1) + Cn * t ^ ((n : ℝ) - 1) * t ^ ε := by
            nlinarith
      _ = t ^ ((n : ℝ) - 1) * (1 + Cn * t ^ ε) := by ring
      _ ≤ t ^ ((n : ℝ) - 1) * (Cn * t ^ ε + Cn * t ^ ε) :=
        mul_le_mul_of_nonneg_left h_mul hΛ_nonneg'
      _ = 2 * Cn * t ^ ((n : ℝ) - 1) * t ^ ε := by ring
  have hJ_card_le' : J * (card : ℝ) ≤ 2 * Cn ^ 2 * t ^ ((n : ℝ) - 1) * t ^ ε := by
    calc
      J * (card : ℝ) ≤ Cn * (t ^ ((n : ℝ) - 1) + (N₂ : ℝ)) := hJ_card_le
      _ ≤ Cn * (2 * Cn * t ^ ((n : ℝ) - 1) * t ^ ε)
        := mul_le_mul_of_nonneg_left h_sum_le (by linarith)
      _ = 2 * Cn ^ 2 * t ^ ((n : ℝ) - 1) * t ^ ε := by ring
  have h_scale_free : t ^ ((n : ℝ) - 1) * V_lb ≤ V_ub := by
    dsimp [V_lb, V_ub]
    set m := n - 1 with hm_def
    have hm_sub : (n : ℝ) - 1 = ((m : ℕ) : ℝ) := by
      rw [hm_def, Nat.cast_sub hn_pos, Nat.cast_one]
    have h_rpow_to_pow : t ^ ((n : ℝ) - 1) = t ^ (m : ℕ) := by
      rw [hm_sub, Real.rpow_natCast]
    have h_pow_sub : (ρ_f : ℝ) ^ (n - 1) / (ρ_f : ℝ) ^ (m : ℕ) = 1 := by
      rw [hm_def, div_self (pow_ne_zero (n - 1) hρ_f_pos.ne.symm)]
    calc
      t ^ ((n : ℝ) - 1) * ((Tube.le_volume.c n : ℝ) * (ρ_f : ℝ) ^ (n - 1))
          = (Tube.le_volume.c n : ℝ) * (t ^ ((n : ℝ) - 1) * (ρ_f : ℝ) ^ (n - 1)) := by ring
      _ = (Tube.le_volume.c n : ℝ) * ((t ^ (m : ℕ)) * (ρ_f : ℝ) ^ (n - 1)) := by rw [h_rpow_to_pow]
      _ = (Tube.le_volume.c n : ℝ) * ((((ρ_c : ℝ) / (ρ_f : ℝ)) ^ (m : ℕ)) * (ρ_f : ℝ) ^ (n - 1))
        := rfl
      _ = (Tube.le_volume.c n : ℝ) *
          (((ρ_c : ℝ) ^ (m : ℕ) / (ρ_f : ℝ) ^ (m : ℕ)) * (ρ_f : ℝ) ^ (n - 1)) := by
        rw [div_pow]
      _ = (Tube.le_volume.c n : ℝ) * ((ρ_c : ℝ) ^ (m : ℕ)
          * ((ρ_f : ℝ) ^ (n - 1) / (ρ_f : ℝ) ^ (m : ℕ))) := by ring
      _ = (Tube.le_volume.c n : ℝ) * ((ρ_c : ℝ) ^ (m : ℕ)) := by
        rw [h_pow_sub, mul_one]
      _ = (Tube.le_volume.c n : ℝ) * ((ρ_c : ℝ) ^ (n - 1)) := rfl
      _ ≤ (Tube.volume_le.C n : ℝ) * ((ρ_c : ℝ) ^ (n - 1)) := by
        refine mul_le_mul_of_nonneg_right le_volume_c_le_volume_le_C (by positivity)
  have hprob_nonneg : 0 ≤ Kakeya.probConst E (ρ_c : ℝ) :=
    (Kakeya.probConst_pos (E := E) hρ_c_pos).le
  have hV_lb_nonneg : 0 ≤ V_lb := by
    dsimp [V_lb]
    positivity
  have hV_ub_nonneg : 0 ≤ V_ub := by
    dsimp [V_ub]
    positivity
  have hK_pack_nonneg : 0 ≤ K_pack := by
    have hprod_nonneg : 0 ≤ V_ub * Kakeya.probConst E (ρ_c : ℝ) :=
      mul_nonneg hV_ub_nonneg hprob_nonneg
    linarith
  have hCn_sq_nonneg : 0 ≤ Cn ^ 2 := by positivity
  have hCn_nonneg : 0 ≤ Cn := by linarith
  have ht_pow_eps_nonneg : 0 ≤ t ^ ε := Real.rpow_nonneg ht_pos.le _
  have hprod_lt : V_ub * Kakeya.probConst E (ρ_c : ℝ) < K_pack := by
    linarith
  have hpos_factor : 0 < 2 * Cn ^ 2 * t ^ ε := by
    positivity
  calc
    ((max 1 ⌈t ^ ((n : ℝ) - 1) / (N₂ : ℝ)⌉₊ : ℕ) : ℝ) * (card : ℝ) *
        Kakeya.probConst E (ρ_c : ℝ) * V_lb
        = J * (card : ℝ) * Kakeya.probConst E (ρ_c : ℝ) * V_lb := by
          rfl
    _ = (J * (card : ℝ)) * (Kakeya.probConst E (ρ_c : ℝ) * V_lb) := by ring
    _ ≤ (2 * Cn ^ 2 * t ^ ((n : ℝ) - 1) * t ^ ε) *
        (Kakeya.probConst E (ρ_c : ℝ) * V_lb) := by
      refine mul_le_mul_of_nonneg_right hJ_card_le' (mul_nonneg hprob_nonneg hV_lb_nonneg)
    _ = 2 * Cn ^ 2 * t ^ ε * (t ^ ((n : ℝ) - 1) * V_lb *
        Kakeya.probConst E (ρ_c : ℝ)) := by ring
    _ ≤ 2 * Cn ^ 2 * t ^ ε * (V_ub * Kakeya.probConst E (ρ_c : ℝ)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine mul_le_mul_of_nonneg_right h_scale_free hprob_nonneg
    _ < 2 * Cn ^ 2 * t ^ ε * K_pack := by
      nlinarith
    _ = 2 * Cn ^ 2 * K_pack * t ^ ε := by ring
    _ = 2 * Cn ^ 2 * K_pack * ((ρ_c : ℝ) / (ρ_f : ℝ)) ^ ε := by rfl

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The blueprint telescoping of `∏_m max {1, x_m}`** (`lem:composed_translation_family`,
upper bound).  Writing `max {1, x} = x / min {1, x}` and bounding each `min {1, x_m}`
below by `(ρ_m/ρ_{m-1})^ε / Cn` (blueprint `lem:x_m_lower_bound`), the scales
telescope to `δ^{-ε}`. -/
lemma prod_max_le
    (M : ℕ) {ε : ℝ} (hε : 0 < ε) {Cn : ℝ} (hCn : 1 ≤ Cn)
    {δ : NNReal} (hδ_pos : 0 < (δ : ℝ)) (_hδ_le_one : (δ : ℝ) ≤ 1)
    (ρ : Fin (M + 1) → NNReal)
    (hρ_pos : ∀ k, 0 < (ρ k : ℝ)) (hρ0 : (ρ 0 : ℝ) ≤ 1) (hρM : ρ (Fin.last M) = δ)
    (hρ_anti : ∀ k : Fin M, (ρ k.succ : ℝ) ≤ (ρ k.castSucc : ℝ))
    (N₂ : Fin M → ℕ) (hN₂_pos : ∀ k, 0 < N₂ k)
    (hxm : ∀ k : Fin M, (N₂ k : ℝ)
      ≤ Cn * ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ))
          ^ (((Module.finrank ℝ E : ℝ) - 1) + ε)) :
    ∏ k : Fin M, max 1 (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ))
          ^ ((Module.finrank ℝ E : ℝ) - 1) / (N₂ k : ℝ))
      ≤ Cn ^ M * (δ : ℝ) ^ (-ε)
        * max 1 (∏ k : Fin M, ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ))
            ^ ((Module.finrank ℝ E : ℝ) - 1) / (N₂ k : ℝ)) := by
  set n := Module.finrank ℝ E with hn_def
  have hn_pos : 0 < n := Module.finrank_pos
  have h_exp_nonneg : 0 ≤ (n : ℝ) - 1 := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
    linarith
  have hε_nonneg : 0 ≤ ε := by linarith
  set t := fun k : Fin M => (ρ k.castSucc : ℝ) / (ρ k.succ : ℝ) with ht_def
  have ht_pos : ∀ k : Fin M, 0 < t k := by
    intro k; dsimp [t]; exact div_pos (hρ_pos k.castSucc) (hρ_pos k.succ)
  have ht_nonneg : ∀ k : Fin M, 0 ≤ t k := fun k => (ht_pos k).le
  have ht_ge_one : ∀ k : Fin M, 1 ≤ t k := by
    intro k; dsimp [t]; exact (one_le_div (hρ_pos k.succ)).mpr (hρ_anti k)
  set Λ := fun k : Fin M => t k ^ ((n : ℝ) - 1) with hΛ_def
  have hΛ_nonneg : ∀ k : Fin M, 0 ≤ Λ k := fun k => Real.rpow_nonneg (ht_nonneg k) _
  have hΛ_pos : ∀ k : Fin M, 0 < Λ k := fun k => Real.rpow_pos_of_pos (ht_pos k) _
  set x := fun k : Fin M => Λ k / (N₂ k : ℝ) with hx_def
  have hx_nonneg : ∀ k : Fin M, 0 ≤ x k := fun k =>
    div_nonneg (hΛ_nonneg k) (by exact_mod_cast (hN₂_pos k).le)
  have hx_nonneg_prod : 0 ≤ ∏ k : Fin M, x k := Finset.prod_nonneg fun k _ => hx_nonneg k
  have h_max_nonneg : ∀ k : Fin M, 0 ≤ max 1 (x k) := by
    intro k; exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)
  have h_factor : ∀ k : Fin M, max 1 (x k) ≤ (Cn * t k ^ ε) * x k := by
    intro k
    have hN₂_pos_real : 0 < (N₂ k : ℝ) := by exact_mod_cast hN₂_pos k
    have hN₂_pos_real_ne : (N₂ k : ℝ) ≠ 0 := by linarith
    have hxm_k : (N₂ k : ℝ) ≤ Cn * t k ^ (((n : ℝ) - 1) + ε) := hxm k
    have h_rpow_add : t k ^ (((n : ℝ) - 1) + ε) = Λ k * t k ^ ε := by
      calc
        t k ^ (((n : ℝ) - 1) + ε) = t k ^ ((n : ℝ) - 1) * t k ^ ε :=
          Real.rpow_add (ht_pos k) ((n : ℝ) - 1) ε
        _ = Λ k * t k ^ ε := by rfl
    rw [h_rpow_add] at hxm_k
    have h_mul : (N₂ k : ℝ) ≤ (Cn * t k ^ ε) * Λ k := by
      calc
        (N₂ k : ℝ) ≤ Cn * (Λ k * t k ^ ε) := hxm_k
        _ = (Cn * t k ^ ε) * Λ k := by ring
    have h_one_le : 1 ≤ (Cn * t k ^ ε) * x k := by
      calc
        1 = (N₂ k : ℝ) / (N₂ k : ℝ) := by field_simp [hN₂_pos_real_ne]
        _ ≤ ((Cn * t k ^ ε) * Λ k) / (N₂ k : ℝ) := by
          simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right h_mul
            (by positivity : 0 ≤ (N₂ k : ℝ)⁻¹)
        _ = (Cn * t k ^ ε) * (Λ k / (N₂ k : ℝ)) := by ring
        _ = (Cn * t k ^ ε) * x k := by rfl
    have h_mul_ge_one : 1 ≤ Cn * t k ^ ε := by
      have h_t_pow_eps_ge_one : 1 ≤ t k ^ ε :=
        Real.one_le_rpow (ht_ge_one k) hε_nonneg
      nlinarith
    have h_x_le : x k ≤ (Cn * t k ^ ε) * x k := by
      nlinarith
    exact max_le h_one_le h_x_le
  have h_prod_factor : ∏ k : Fin M, max 1 (x k) ≤ ∏ k : Fin M, ((Cn * t k ^ ε) * x k) :=
    Finset.prod_le_prod (fun k _ => h_max_nonneg k) (fun k _ => h_factor k)
  have h_prod_simplify : ∏ k : Fin M, ((Cn * t k ^ ε) * x k) =
      Cn ^ M * (∏ k : Fin M, (t k ^ ε)) * (∏ k : Fin M, x k) := by
    calc
      ∏ k : Fin M, ((Cn * t k ^ ε) * x k)
          = (∏ k : Fin M, (Cn * t k ^ ε)) * (∏ k : Fin M, x k) := by
            rw [Finset.prod_mul_distrib]
      _ = ((∏ k : Fin M, Cn) * (∏ k : Fin M, (t k ^ ε))) * (∏ k : Fin M, x k) := by
        rw [Finset.prod_mul_distrib]
      _ = (∏ k : Fin M, Cn) * (∏ k : Fin M, (t k ^ ε)) * (∏ k : Fin M, x k) := by ring
      _ = Cn ^ M * (∏ k : Fin M, (t k ^ ε)) * (∏ k : Fin M, x k) := by
        simp [Finset.prod_const]
  rw [h_prod_simplify] at h_prod_factor
  have h_prod_t_pow_eps : ∏ k : Fin M, (t k ^ ε) = (∏ k : Fin M, t k) ^ ε := by
    calc
      ∏ k : Fin M, (t k ^ ε) = (∏ k : Fin M, t k) ^ ε := by
        rw [Real.finsetProd_rpow (Finset.univ : Finset (Fin M)) t (fun k _ => ht_nonneg k) ε]
      _ = (∏ k : Fin M, t k) ^ ε := rfl
  have h_prod_t : ∏ k : Fin M, t k = (ρ 0 : ℝ) / (δ : ℝ) := by
    calc
      ∏ k : Fin M, t k = ∏ k : Fin M, ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) := rfl
      _ = (ρ 0 : ℝ) / (ρ (Fin.last M) : ℝ) := prod_ratio_telescope M ρ hρ_pos
      _ = (ρ 0 : ℝ) / (δ : ℝ) := by rw [hρM]
  have h_telescope : (∏ k : Fin M, t k) ^ ε ≤ (δ : ℝ) ^ (-ε) := by
    calc
      (∏ k : Fin M, t k) ^ ε = ((ρ 0 : ℝ) / (δ : ℝ)) ^ ε := by rw [h_prod_t]
      _ ≤ (1 / (δ : ℝ)) ^ ε := by
        have h_div_le : (ρ 0 : ℝ) / (δ : ℝ) ≤ 1 / (δ : ℝ) := by
          simpa [div_eq_mul_inv] using
            mul_le_mul_of_nonneg_right hρ0 (by positivity : 0 ≤ (δ : ℝ)⁻¹)
        refine Real.rpow_le_rpow (by positivity) h_div_le hε_nonneg
      _ = (δ : ℝ) ^ (-ε) := by
        calc
          (1 / (δ : ℝ)) ^ ε = ((δ : ℝ)⁻¹) ^ ε := by simp
          _ = (δ : ℝ) ^ (-ε) := by rw [Real.rpow_neg_eq_inv_rpow]
  calc
    ∏ k : Fin M, max 1 (x k)
        ≤ Cn ^ M * (∏ k : Fin M, (t k ^ ε)) * (∏ k : Fin M, x k) := h_prod_factor
    _ = Cn ^ M * ((∏ k : Fin M, t k) ^ ε) * (∏ k : Fin M, x k) := by rw [h_prod_t_pow_eps]
    _ ≤ Cn ^ M * ((δ : ℝ) ^ (-ε)) * (∏ k : Fin M, x k) := by
      calc
        Cn ^ M * ((∏ k : Fin M, t k) ^ ε) * (∏ k : Fin M, x k)
            = (Cn ^ M * (∏ k : Fin M, x k)) * ((∏ k : Fin M, t k) ^ ε) := by ring
        _ ≤ (Cn ^ M * (∏ k : Fin M, x k)) * ((δ : ℝ) ^ (-ε)) :=
          mul_le_mul_of_nonneg_left h_telescope (mul_nonneg (by positivity) hx_nonneg_prod)
        _ = Cn ^ M * ((δ : ℝ) ^ (-ε)) * (∏ k : Fin M, x k) := by ring
    _ ≤ Cn ^ M * ((δ : ℝ) ^ (-ε)) * max 1 (∏ k : Fin M, x k) := by
      have h_nonneg : 0 ≤ Cn ^ M * ((δ : ℝ) ^ (-ε)) := by positivity
      refine mul_le_mul_of_nonneg_left (le_max_right _ _) h_nonneg
    _ = Cn ^ M * (δ : ℝ) ^ (-ε) * max 1 (∏ k : Fin M, x k) := by ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- **`∏_m x_m ≲ (|s| · δ^{n-1})^{-1}`** (`lem:composed_translation_family`).  The
numerators telescope to `(ρ_0/δ)^{n-1} ≤ δ^{-(n-1)}`, and the denominators are bounded
below by `|s| / C_prod` through the leaf-count product bound. -/
lemma prod_x_le
    (M : ℕ) {δ : NNReal} (hδ_pos : 0 < (δ : ℝ)) (_hδ_le_one : (δ : ℝ) ≤ 1)
    (ρ : Fin (M + 1) → NNReal)
    (hρ_pos : ∀ k, 0 < (ρ k : ℝ)) (hρ0 : (ρ 0 : ℝ) ≤ 1) (hρM : ρ (Fin.last M) = δ)
    (N₂ : Fin M → ℕ) (hN₂_pos : ∀ k, 0 < N₂ k)
    (s : Finset ι) (hs_ne : s.Nonempty)
    {C_prod : ℝ} (hC_prod_pos : 0 < C_prod)
    (hprod : (s.card : ℝ) ≤ C_prod * ∏ k : Fin M, (N₂ k : ℝ)) :
    ∏ k : Fin M, ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ))
        ^ ((Module.finrank ℝ E : ℝ) - 1) / (N₂ k : ℝ)
      ≤ C_prod * ((s.card : ℝ) * (δ : ℝ) ^ ((Module.finrank ℝ E : ℝ) - 1))⁻¹ := by
  set c := (Module.finrank ℝ E : ℝ) - 1 with hc_def
  have hc_nonneg : 0 ≤ c := by
    have h_finrank_pos : 0 < Module.finrank ℝ E := Module.finrank_pos
    have h_finrank_ge_one : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast h_finrank_pos
    linarith
  have hδ_c_pos : 0 < (δ : ℝ) ^ c := Real.rpow_pos_of_pos hδ_pos c
  have hδ_c_nonneg : 0 ≤ (δ : ℝ) ^ c := hδ_c_pos.le
  have hcard_pos : 0 < (s.card : ℝ) := by
    have hcard_nat_pos : 0 < s.card := Finset.card_pos.mpr hs_ne
    exact_mod_cast hcard_nat_pos
  set t := fun (k : Fin M) => (ρ k.castSucc : ℝ) / (ρ k.succ : ℝ) with ht_def
  have ht_nonneg : ∀ k : Fin M, 0 ≤ t k := by
    intro k; dsimp [t]
    exact div_nonneg (by positivity) (by positivity)
  have ht_pos : ∀ k : Fin M, 0 < t k := by
    intro k; dsimp [t]
    exact div_pos (by exact_mod_cast hρ_pos (k.castSucc)) (by exact_mod_cast hρ_pos (k.succ))
  have hprod_telescope : ∏ k : Fin M, t k = (ρ 0 : ℝ) / (δ : ℝ) := by
    calc
      ∏ k : Fin M, t k = ∏ k : Fin M, ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) := rfl
      _ = (ρ 0 : ℝ) / (ρ (Fin.last M) : ℝ) := prod_ratio_telescope M ρ hρ_pos
      _ = (ρ 0 : ℝ) / (δ : ℝ) := by rw [hρM]
  have hprod_telescope_nonneg : 0 ≤ ∏ k : Fin M, t k :=
    Finset.prod_nonneg (fun k _ => ht_nonneg k)
  have hprod_telescope_le : ∏ k : Fin M, t k ≤ 1 / (δ : ℝ) := by
    rw [hprod_telescope]
    refine div_le_div_of_nonneg_right hρ0 hδ_pos.le
  have hN₂_pos_real : ∀ k : Fin M, 0 < (N₂ k : ℝ) := by
    intro k; exact_mod_cast hN₂_pos k
  have hdenom_pos : 0 < ∏ k : Fin M, (N₂ k : ℝ) :=
    Finset.prod_pos (fun k _ => hN₂_pos_real k)
  have hdenom_nonneg : 0 ≤ ∏ k : Fin M, (N₂ k : ℝ) := hdenom_pos.le
  have hdiv : (s.card : ℝ) / C_prod ≤ ∏ k : Fin M, (N₂ k : ℝ) := by
    calc
      (s.card : ℝ) / C_prod ≤ (C_prod * ∏ k : Fin M, (N₂ k : ℝ)) / C_prod :=
        div_le_div_of_nonneg_right hprod hC_prod_pos.le
      _ = ∏ k : Fin M, (N₂ k : ℝ) := by field_simp [hC_prod_pos.ne']
  have hdenom_inv_le : (∏ k : Fin M, (N₂ k : ℝ))⁻¹ ≤ C_prod / (s.card : ℝ) := by
    field_simp [hcard_pos.ne', hdenom_pos.ne', hC_prod_pos.ne']
    rw [mul_comm]
    exact hprod
  calc
    ∏ k : Fin M, ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ c / (N₂ k : ℝ)
        = (∏ k : Fin M, ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ c) / (∏ k : Fin M, (N₂ k : ℝ)) := by
          rw [Finset.prod_div_distrib]
    _ = (∏ k : Fin M, t k ^ c) / (∏ k : Fin M, (N₂ k : ℝ)) := by rfl
    _ = ((∏ k : Fin M, t k) ^ c) / (∏ k : Fin M, (N₂ k : ℝ)) := by
      rw [Real.finsetProd_rpow (Finset.univ : Finset (Fin M)) t (fun k hk => ht_nonneg k) c]
    _ ≤ ((1 / (δ : ℝ)) ^ c) / (∏ k : Fin M, (N₂ k : ℝ)) := by
      refine div_le_div_of_nonneg_right ?_ hdenom_nonneg
      refine Real.rpow_le_rpow hprod_telescope_nonneg hprod_telescope_le hc_nonneg
    _ = (((δ : ℝ) ^ c)⁻¹) / (∏ k : Fin M, (N₂ k : ℝ)) := by
      rw [one_div, Real.inv_rpow hδ_pos.le c]
    _ = ((δ : ℝ) ^ c)⁻¹ * (1 / (∏ k : Fin M, (N₂ k : ℝ))) := by ring
    _ = ((δ : ℝ) ^ c)⁻¹ * (∏ k : Fin M, (N₂ k : ℝ))⁻¹ := by ring
    _ ≤ ((δ : ℝ) ^ c)⁻¹ * (C_prod / (s.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hdenom_inv_le (by positivity)
    _ = C_prod * ((s.card : ℝ) * (δ : ℝ) ^ c)⁻¹ := by ring
    _ = C_prod * ((s.card : ℝ) * (δ : ℝ) ^ ((Module.finrank ℝ E : ℝ) - 1))⁻¹ := by rfl
end StickyKakeya

end Kakeya
