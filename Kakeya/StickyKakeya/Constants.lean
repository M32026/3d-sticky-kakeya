/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.StickyKakeya.Lemma75

/-!
# Theorem 7.3(A) ⇒ (B): the constants and their thresholds

Every `δ`-independent constant the (A) ⇒ (B) deduction fixes before the `∀ᶠ δ` filter — the inner
grid length, the ED-refinement loss, the Definition 2.1(iii) bracket constant, the leaf-count
product constant — together with the elementary threshold facts about them.  Nothing here mentions
a tube family.
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


/-! ### Step-1 bridge lemmas (GWZ Definition 2.1 data for `subStickyFrostmanLemma`)

The (B) input `StickyKatzTaoEstimate` (`Kakeya/Sticky.lean:99-113`) gives
uniformity on the discrete scale grid `{δ^(k/M_paper) | k ≤ M_paper}` where
`M_paper := ⌈log log (1/δ)⌉₊` is δ-dependent.  But `subStickyFrostmanLemma`
(`Kakeya/Sticky.lean:1102+`) takes its scale chain length `M` as a *fixed*
parameter (chosen outside the `∀ᶠ δ` filter).  `exists_frostman_translation_family`
therefore works with the fixed chain `ρ_inner k = δ^(k/M_inner)`, built inline
there, and feeds `subStickyFrostmanLemma` the GWZ Definition 2.1 data.

The child-count bracket comes from the dyadic band of the pruning step
(`exists_child_count_of_band`, re-exported through
`Tube.refineToEssDistinctUniform`), which gives every coarse parent at least
`N₂ k` fine children with bracket constant `1` and no volume-fullness premise.
The earlier route through a tube-in-tube packing lower bound needed a
volume-fullness hypothesis on the coarse parents that is false for the
unrefined family, and has been removed. -/

open scoped Topology in
/-- Extract an explicit threshold from an eventually-statement on `𝓝[>] 0` (NNReal):
if `p` holds eventually as `δ → 0⁺`, there is `δ₀ > 0` with `p δ` for all `0 < δ ≤ δ₀`.
Used to convert `subStickyFrostmanLemma`'s `∀ᶠ` into a threaded `∃ δ₀` threshold. -/
lemma exists_threshold_of_eventually_nhdsGT {p : NNReal → Prop}
    (h : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal), p δ) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ ∀ ⦃δ : NNReal⦄, 0 < δ → δ ≤ δ₀ → p δ := by
  rw [Filter.eventually_iff, mem_nhdsWithin] at h
  obtain ⟨U, hU_open, hU_mem0, hU_sub⟩ := h
  obtain ⟨t, ht_pos, ht_sub⟩ := nhds_bot_basis.mem_iff.mp (hU_open.mem_nhds hU_mem0)
  refine ⟨t / 2, div_pos ht_pos (by norm_num), fun δ hδ_pos hδ_le => ?_⟩
  have hδ_lt : δ < t := lt_of_le_of_lt hδ_le (div_lt_self ht_pos (by norm_num))
  exact hU_sub ⟨ht_sub hδ_lt, hδ_pos⟩

/-- `1 ≤ packConst`, so the child-count bracket may be weakened from constant `1` to the packing
constant.  Both tube-volume bounds applied to a single unit-scale tube give
`le_volume.c n ≤ volume_le.C n`; the sandwich is already carried out inline in
`one_le_edRefineC`. -/
lemma one_le_packConst :
    (1 : ℝ) ≤ 2 * ((Tube.volume_le.C (Module.finrank ℝ E) : ℝ)
      / (Tube.le_volume.c (Module.finrank ℝ E) : ℝ)) := by
  let n := Module.finrank ℝ E
  have hc_pos : (0 : ℝ) < (Tube.le_volume.c n : ℝ) := by
    exact_mod_cast Tube.le_volume.c_pos n
  have hcC : (Tube.le_volume.c n : ℝ) ≤ (Tube.volume_le.C n : ℝ) := by
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
  have h1 : (1 : ℝ) ≤ (Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ) :=
      (le_div_iff₀ hc_pos).mpr (by simpa using hcC)
  linarith

/-- **The E6 `inSlack` exponent.**  Half of `β := η₁ - (n+3)·ε_inner`, where the inner SSF
parameters are `M_inner = ⌈(n+3)/η₁⌉₊ + 1` and `ε_inner = 1/M_inner`, both `δ`-independent.  The
choice `inSlack := δ^(sfBeta η₁)` is large enough to keep the Frostman error below the `δ^(-η₁)`
that Theorem 7.3(A) accepts, and small enough to absorb the per-scale telescoping loss. -/
@[irreducible] noncomputable def sfBeta (η₁ : ℝ) : ℝ :=
  (η₁ - ((Module.finrank ℝ E : ℝ) + 3)
    / ((⌈((Module.finrank ℝ E : ℝ) + 3) / η₁⌉₊ + 1 : ℕ) : ℝ)) / 2

omit [MeasurableSpace E] [BorelSpace E] in
/-- `sfBeta η₁ > 0`: since `M_inner = ⌈(n+3)/η₁⌉₊ + 1 > (n+3)/η₁`, we get
`(n+3)/M_inner < η₁`. -/
lemma sfBeta_pos (η₁ : ℝ) (hη₁ : 0 < η₁) : 0 < sfBeta (E := E) η₁ := by
  have hn_pos : 0 < (Module.finrank ℝ E : ℝ) := by
    exact mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hn3_pos : 0 < (Module.finrank ℝ E : ℝ) + 3 := by linarith
  have hx_pos : 0 < ((Module.finrank ℝ E : ℝ) + 3) / η₁ := div_pos hn3_pos hη₁
  set x := ((Module.finrank ℝ E : ℝ) + 3) / η₁ with hx_def
  have hx_lt_M : x < (Nat.ceil x : ℝ) + 1 := by
    have hx_le_ceil : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
    nlinarith
  have h_lt : ((Module.finrank ℝ E : ℝ) + 3) / ((Nat.ceil x : ℝ) + 1) < η₁ := by
    calc
      ((Module.finrank ℝ E : ℝ) + 3) / ((Nat.ceil x : ℝ) + 1) <
          ((Module.finrank ℝ E : ℝ) + 3) / x :=
        div_lt_div_of_pos_left hn3_pos hx_pos hx_lt_M
      _ = η₁ := by
        dsimp [x]
        field_simp [hη₁.ne.symm, hn3_pos.ne.symm]
  unfold sfBeta
  push_cast
  have h_num_pos : 0 < η₁ - ((Module.finrank ℝ E : ℝ) + 3) / ((Nat.ceil x : ℝ) + 1) := by linarith
  positivity

/-- The inner/outer grid length, chosen large enough to satisfy simultaneously the E7 requirement
`2·(n+3)·ε_inner ≤ η₁` and the E2 ε-budget slack `2·η_KT + ε_inner < ε/2`; the `max` with
`⌈4/ε⌉₊ + 1` guarantees `ε_inner = 1 / gridLen < ε/4`.  The first component carries the factor `16`
because the reduction to the unit ball charges its Frostman exponent twice more and adds the `Δ_max`
exponent on top, so that `5(n+3)·ε_inner < η₁` is what has to hold. -/
@[irreducible] noncomputable def gridLen (n : ℕ) (η₁ ε : ℝ) : ℕ :=
  max (⌈(16 * ((n : ℝ) + 3)) / η₁⌉₊ + 1) (⌈(4 : ℝ) / ε⌉₊ + 1)

lemma gridLen_eq (n : ℕ) (η₁ ε : ℝ) :
    gridLen n η₁ ε = max (⌈(16 * ((n : ℝ) + 3)) / η₁⌉₊ + 1) (⌈(4 : ℝ) / ε⌉₊ + 1) := by
  unfold gridLen; rfl

/-- **The exponent budget at any admissible multiplier.**  For `0 ≤ k ≤ 16` the grid length exceeds
`k(n+3)/η₁` strictly, so `k·(n+3)·ε_inner < η₁` with `ε_inner = 1 / gridLen n η₁ ε`.  The consumers
are `k = 2` (the leaf-anchored SSF Frostman exponent) and `k = 5` (the budget of the reduction to
the unit ball). -/
private lemma mul_np3_mul_one_div_gridLen_lt (k : ℝ) (_hk0 : 0 ≤ k) (hk16 : k ≤ 16)
    (n : ℕ) (η₁ ε : ℝ) (hη₁ : 0 < η₁) :
    k * ((n : ℝ) + 3) * (1 / ((gridLen n η₁ ε : ℕ) : ℝ)) < η₁ := by
  set A : ℝ := 16 * ((n : ℝ) + 3) with hA_def
  set M : ℕ := gridLen n η₁ ε with hM_def
  have hn3_nn : 0 ≤ (n : ℝ) + 3 := by positivity
  have hA_lt_M : A / η₁ < (M : ℝ) := by
    have hceil : A / η₁ < (⌈A / η₁⌉₊ : ℝ) + 1 := by
      have h := Nat.le_ceil (A / η₁)
      linarith
    have hM_ge : (⌈A / η₁⌉₊ : ℝ) + 1 ≤ (M : ℝ) := by
      exact_mod_cast (by
        rw [hM_def, gridLen_eq]
        change (⌈(16 * ((n : ℝ) + 3)) / η₁⌉₊ + 1 : ℕ) ≤
          max (⌈(16 * ((n : ℝ) + 3)) / η₁⌉₊ + 1) (⌈(4 : ℝ) / ε⌉₊ + 1)
        exact le_max_left _ _)
    linarith
  have hA_lt_ηM : A < η₁ * (M : ℝ) := by
    simpa [mul_comm] using (div_lt_iff₀ hη₁).mp hA_lt_M
  have hM_pos : 0 < (M : ℝ) := by
    have hM1 : 1 ≤ M := by
      rw [hM_def, gridLen_eq]
      exact le_trans (Nat.le_add_left 1 _) (le_max_left _ _)
    have hM1r : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
    linarith
  have hA_div_M : A * (1 / (M : ℝ)) < η₁ := by
    rw [← div_eq_mul_one_div]
    rw [div_lt_iff₀ hM_pos]
    exact hA_lt_ηM
  have hk_le_A : k * ((n : ℝ) + 3) ≤ A := by
    rw [hA_def]
    exact mul_le_mul_of_nonneg_right hk16 hn3_nn
  have hrec_nn : 0 ≤ 1 / (M : ℝ) :=
    div_nonneg zero_le_one (by exact_mod_cast (Nat.zero_le M))
  calc
    k * ((n : ℝ) + 3) * (1 / (M : ℝ))
        ≤ A * (1 / (M : ℝ)) := mul_le_mul_of_nonneg_right hk_le_A hrec_nn
    _ < η₁ := hA_div_M

/-- The budget of `StickyKakeya.exists_union_volume_ge_of_ball` at the SSF exponents
`η_F = 2(n+3)ε_inner`, `η_D = (n+3)ε_inner`: `2·η_F + η_D = 5(n+3)·ε_inner < η₁`. -/
lemma five_np3_mul_one_div_gridLen_lt (n : ℕ) (η₁ ε : ℝ) (hη₁ : 0 < η₁) :
    5 * ((n : ℝ) + 3) * (1 / ((gridLen n η₁ ε : ℕ) : ℝ)) < η₁ :=
  mul_np3_mul_one_div_gridLen_lt 5 (by norm_num) (by norm_num) n η₁ ε hη₁

/-- The repaired ball-reduction budget after the final essentially-distinct refinement:
`2·η_F + 2·η_D = 6(n+3)ε_inner < η₁`. -/
lemma six_np3_mul_one_div_gridLen_lt (n : ℕ) (η₁ ε : ℝ) (hη₁ : 0 < η₁) :
    6 * ((n : ℝ) + 3) * (1 / ((gridLen n η₁ ε : ℕ) : ℝ)) < η₁ :=
  mul_np3_mul_one_div_gridLen_lt 6 (by norm_num) (by norm_num) n η₁ ε hη₁

lemma one_le_gridLen (n : ℕ) (η₁ ε : ℝ) : 1 ≤ gridLen n η₁ ε := by
  rw [gridLen_eq]
  exact le_trans (Nat.le_add_left 1 _) (le_max_left _ _)

lemma gridLen_pos (n : ℕ) (η₁ ε : ℝ) : 0 < gridLen n η₁ ε :=
  one_le_gridLen n η₁ ε

/-- The grid is long enough that `ε_inner = 1 / gridLen` fits strictly inside a quarter of the
ε-budget; this is what pays for the blueprint's mixed-regime `δ^{-ε_inner}` loss. -/
lemma one_div_gridLen_lt (n : ℕ) (η₁ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    1 / ((gridLen n η₁ ε : ℕ) : ℝ) < ε / 4 := by
  have hceil_pos : (0 : ℝ) < ((⌈(4 : ℝ) / ε⌉₊ + 1 : ℕ) : ℝ) := by
    have : 0 < (⌈(4 : ℝ) / ε⌉₊ + 1 : ℕ) := by omega
    exact_mod_cast this
  have hge : ((⌈(4 : ℝ) / ε⌉₊ + 1 : ℕ) : ℝ) ≤ ((gridLen n η₁ ε : ℕ) : ℝ) := by
    have : (⌈(4 : ℝ) / ε⌉₊ + 1 : ℕ) ≤ gridLen n η₁ ε := by
      rw [gridLen_eq]; exact le_max_right _ _
    exact_mod_cast this
  have hgrid_pos : (0 : ℝ) < ((gridLen n η₁ ε : ℕ) : ℝ) := lt_of_lt_of_le hceil_pos hge
  have h4_lt : (4 : ℝ) < ε * ((⌈(4 : ℝ) / ε⌉₊ + 1 : ℕ) : ℝ) := by
    have hlt : (4 : ℝ) / ε < ((⌈(4 : ℝ) / ε⌉₊ + 1 : ℕ) : ℝ) := by
      have h := Nat.le_ceil ((4 : ℝ) / ε)
      push_cast
      linarith
    have := (div_lt_iff₀ hε).mp hlt
    linarith
  have h4_lt' : (4 : ℝ) < ε * ((gridLen n η₁ ε : ℕ) : ℝ) := by
    have := mul_le_mul_of_nonneg_left hge hε.le
    linarith
  rw [div_lt_div_iff₀ hgrid_pos (by norm_num : (0 : ℝ) < 4)]
  linarith

/-- Real form of the ED-refinement loss constant of `Tube.refineToEssDistinctLeaves`.  Refining a
family to be pairwise essentially distinct costs a factor `C · D`, where `D` bounds the maximal
density; the E2 packing bound is stated over `ℝ`, so the real form of `C` is carried here. -/
noncomputable def edRefineC : ℝ :=
  (Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E)).toReal

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- `Tube.refineToEssDistinctLeaves.C n ≠ ⊤`: it is
`overlapContainment.C n * vol_le.C n / le_volume.c n`, and `le_volume.c n > 0`. -/
private lemma refineToEssDistinctLeaves_C_ne_top :
    Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) ≠ ⊤ := by
  rw [Tube.refineToEssDistinctLeaves.C]
  refine ENNReal.div_ne_top ?_ ?_
  · refine ENNReal.mul_ne_top ?_ ?_
    · rw [Tube.overlapContainment.C]
      exact ENNReal.ofReal_ne_top
    · exact ENNReal.coe_ne_top
  · have hpos : 0 < Tube.le_volume.c (Module.finrank ℝ E) :=
      Tube.le_volume.c_pos (Module.finrank ℝ E)
    have hpos' : (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) ≠ 0 := by
      exact_mod_cast hpos.ne'
    exact hpos'

/-- `1 ≤ edRefineC`, so the ED-refinement loss only ever enlarges a bound. -/
lemma one_le_edRefineC : (1 : ℝ) ≤ edRefineC (E := E) := by
  have hC_ne_top : Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) ≠ ⊤ :=
    refineToEssDistinctLeaves_C_ne_top
  have h_one_ne_top : (1 : ENNReal) ≠ ⊤ := by simp
  have h_one_le_ENNReal : (1 : ENNReal) ≤
    Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) := by
    rw [Tube.refineToEssDistinctLeaves.C]
    have h_oc_ge_one : (1 : ENNReal) ≤ Tube.overlapContainment.C (Module.finrank ℝ E) := by
      rw [Tube.overlapContainment.C, ENNReal.one_le_ofReal]
      have h_one_lt_C : 1 < Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) :=
        Tube.tubeOverlapCoreClose.one_lt_C (Module.finrank ℝ E)
      have h_one_nonneg : 0 ≤ (1 : ℝ) := by norm_num
      have h_nonneg : 0 ≤ Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) := by linarith
      have h_one_le : (1 : ℝ) ≤ Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) := by linarith
      have h_pow : (1 : ℝ) ^ (Module.finrank ℝ E) ≤
          (Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)) ^ (Module.finrank ℝ E) :=
        pow_le_pow_left₀ h_one_nonneg h_one_le (Module.finrank ℝ E)
      simpa [Tube.tubeDilateVolume.C'] using h_pow
    have h_vol_le_div_ge_one : (1 : ENNReal) ≤ (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) /
      (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) := by
      have h_vol_const_le : (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) ≤
          (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) := by
        have hδ0 : (0 : NNReal) < 1 := by norm_num
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
        have hle_vol : (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) *
            (1 : ENNReal) ^ (Module.finrank ℝ E - 1) ≤ volume T.carrier :=
          Tube.le_volume T
        have hvol_le : volume T.carrier ≤ (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
            (1 : ENNReal) ^ (Module.finrank ℝ E - 1) :=
          Tube.volume_le hδ1 T
        have h_ineq : (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) *
            (1 : ENNReal) ^ (Module.finrank ℝ E - 1) ≤
            (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
            (1 : ENNReal) ^ (Module.finrank ℝ E - 1) :=
          hle_vol.trans hvol_le
        have h_pow_ne_zero : (1 : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ 0 := by simp
        have h_pow_ne_top : (1 : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ ⊤ := by simp
        exact ((ENNReal.mul_le_mul_iff_left h_pow_ne_zero h_pow_ne_top).mp h_ineq)
      have h_cpos : (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) ≠ 0 := by
        exact_mod_cast (Tube.le_volume.c_pos (Module.finrank ℝ E)).ne'
      rw [ENNReal.le_div_iff_mul_le (Or.inl h_cpos) (Or.inr (by exact ENNReal.coe_ne_top))]
      simpa [one_mul] using h_vol_const_le
    calc
      (1 : ENNReal) = (1 : ENNReal) * (1 : ENNReal) := by simp
      _ ≤ Tube.overlapContainment.C (Module.finrank ℝ E) *
        ((Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
        / (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)) := by
        exact mul_le_mul h_oc_ge_one h_vol_le_div_ge_one (by simp) (by positivity)
      _ = Tube.overlapContainment.C (Module.finrank ℝ E)
        * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) /
        (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) := by
        simp [div_eq_mul_inv, mul_assoc]
      _ = Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) := rfl
  have h := (ENNReal.toReal_le_toReal h_one_ne_top hC_ne_top).mpr h_one_le_ENNReal
  simpa [edRefineC, ENNReal.toReal_one] using h

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- `ENNReal.ofReal (edRefineC) = Tube.refineToEssDistinctLeaves.C n`, the bridge used to turn the
`ENNReal` cardinality conclusion of `refineToEssDistinctUniform` into a real inequality. -/
lemma ofReal_edRefineC :
    ENNReal.ofReal (edRefineC (E := E))
      = Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) := by
  rw [edRefineC, ENNReal.ofReal_toReal (refineToEssDistinctLeaves_C_ne_top (E := E))]

/-- For a positive exponent `p` and a positive constant `c`, `δ^p ≤ c` for all small `δ`.
Supplies the E6 `h_ratio` threshold `δ^(β/2) ≤ Kic²/Cuni^(2(n-1))`. -/
lemma rpow_le_const_eventually (p c : ℝ) (hp : 0 < p) (hc : 0 < c) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : NNReal, 0 < δ → (δ : ℝ) ≤ δ₀ → (δ : ℝ) ^ p ≤ c := by
  set δ₀ := c ^ (1 / p) with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := Real.rpow_pos_of_pos hc _
  have hcalc : (c ^ (1 / p)) ^ p = c := by
    rw [← Real.rpow_mul hc.le, show (1 / p) * p = 1 by field_simp [hp.ne'], Real.rpow_one]
  refine ⟨δ₀, hδ₀_pos, fun δ hδ_pos hδ_le => ?_⟩
  have hδ_nonneg : 0 ≤ (δ : ℝ) := by exact_mod_cast hδ_pos.le
  calc
    (δ : ℝ) ^ p ≤ (c ^ (1 / p)) ^ p := Real.rpow_le_rpow hδ_nonneg hδ_le (by positivity : 0 ≤ p)
    _ = c := hcalc

/-- `⌈loglog(1/δ)⌉₊ → ∞` as `δ → 0⁺`, so `a / ⌈loglog(1/δ)⌉₊ ≤ q` for all small `δ` whenever
`q > 0`.  Supplies the E6 `h_ratio` threshold `(n-1)/Mout ≤ β/4`. -/
lemma loglog_div_le_eventually (a q : ℝ) (hq : 0 < q) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : NNReal, 0 < δ → (δ : ℝ) ≤ δ₀ →
      a / ((⌈Real.log (Real.log (1 / (δ : ℝ)))⌉₊ : ℕ) : ℝ) ≤ q := by
  by_cases ha : a ≤ 0
  · refine ⟨1, by norm_num, fun δ hδpos hδle => ?_⟩
    have hden_nonneg : (0 : ℝ) ≤ ((⌈Real.log (Real.log (1 / (δ : ℝ)))⌉₊ : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    have hdiv : a / ((⌈Real.log (Real.log (1 / (δ : ℝ)))⌉₊ : ℕ) : ℝ) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg ha hden_nonneg
    linarith
  · have ha_pos : 0 < a := lt_of_not_ge ha
    have ha_q_pos : 0 < a / q := div_pos ha_pos hq
    set δ₀ := Real.exp (-Real.exp (a / q)) with hδ₀_def
    have hδ₀_pos : 0 < δ₀ := by
      rw [hδ₀_def]
      exact Real.exp_pos _
    refine ⟨δ₀, hδ₀_pos, fun δ hδpos hδle => ?_⟩
    have hδpos' : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδpos
    have hδle' : (δ : ℝ) ≤ δ₀ := hδle
    have hδ₀_lt_one : δ₀ < 1 := by
      calc
        δ₀ = Real.exp (-Real.exp (a / q)) := rfl
        _ < Real.exp 0 := by
          refine (Real.exp_lt_exp.mpr ?_)
          nlinarith [Real.exp_pos (a / q)]
        _ = 1 := Real.exp_zero
    have hδ_lt_one : (δ : ℝ) < 1 := lt_of_le_of_lt hδle' hδ₀_lt_one
    have h_one_div_gt_one : 1 < 1 / (δ : ℝ) :=
      one_lt_one_div hδpos' hδ_lt_one
    have h_log_one_div_pos : 0 < Real.log (1 / (δ : ℝ)) :=
      Real.log_pos h_one_div_gt_one
    have h_log_one_div_ge : Real.exp (a / q) ≤ Real.log (1 / (δ : ℝ)) := by
      calc
        Real.exp (a / q) = -Real.log (Real.exp (-Real.exp (a / q))) := by
          rw [Real.log_exp, neg_neg]
        _ = -Real.log δ₀ := by rw [hδ₀_def]
        _ ≤ -Real.log (δ : ℝ) := by
          refine neg_le_neg (Real.log_le_log (by exact_mod_cast hδpos) hδle')
        _ = Real.log (1 / (δ : ℝ)) := by
          rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hδpos'.ne', Real.log_one, zero_sub]
    have h_log_log_ge : a / q ≤ Real.log (Real.log (1 / (δ : ℝ))) := by
      calc
        a / q = Real.log (Real.exp (a / q)) := by rw [Real.log_exp (a / q)]
        _ ≤ Real.log (Real.log (1 / (δ : ℝ))) :=
          Real.log_le_log (Real.exp_pos (a / q)) h_log_one_div_ge
    let d := ((⌈Real.log (Real.log (1 / (δ : ℝ)))⌉₊ : ℕ) : ℝ)
    have hd_nonneg : 0 ≤ d := Nat.cast_nonneg _
    have hceil_ge : Real.log (Real.log (1 / (δ : ℝ))) ≤ d := by
      have := Nat.le_ceil (Real.log (Real.log (1 / (δ : ℝ))))
      simpa [d] using this
    have ha_q_le_d : a / q ≤ d := le_trans h_log_log_ge hceil_ge
    by_cases hd_pos : 0 < d
    · rw [div_le_iff₀ hd_pos]
      have ha_le_dq : a ≤ d * q := (div_le_iff₀ hq).mp ha_q_le_d
      calc
        a ≤ d * q := ha_le_dq
        _ = q * d := mul_comm _ _
    · have hd_zero : d = 0 := by linarith
      dsimp [d] at hd_zero
      rw [hd_zero, div_zero]
      exact hq.le

/-- The leaf-count product constant of `Tube.refineToEssDistinctUniform`
(`Kakeya/Uniform/Pruning.lean`): `|s| ≤ prodConst n M · ∏_k N₂ k`.  It is the `C_prod` parameter of
`subStickyFrostmanLemma`. -/
noncomputable def prodConst (n M : ℕ) : ℝ :=
  2 * ((641 : ℝ) ^ (2 * n) * (4 : ℝ) ^ (2 * n)) * (4 : ℝ) ^ M

lemma prodConst_pos (n M : ℕ) : 0 < prodConst n M := by
  unfold prodConst; positivity

/-- The Definition 2.1(iii) bracket constant handed to `subStickyFrostmanLemma`.  It must dominate
both directions of the bracket exported by `refineToEssDistinctUniform`: the packing constant
`2 · (vol_le.C / le_vol.c)` on the lower side and the bounded-overlap constant
`8 · overlapConstBOTight` on the upper side. -/
noncomputable def cnEff (n : ℕ) : ℝ :=
  max (2 * ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ)))
    (8 * (Tube.overlapConstBOTight n : ℝ))

lemma packConst_le_cnEff (n : ℕ) :
    2 * ((Tube.volume_le.C n : ℝ) / (Tube.le_volume.c n : ℝ)) ≤ cnEff n := le_max_left _ _

lemma childUB_le_cnEff (n : ℕ) :
    8 * (Tube.overlapConstBOTight n : ℝ) ≤ cnEff n := le_max_right _ _

lemma one_le_cnEff : (1 : ℝ) ≤ cnEff (Module.finrank ℝ E) :=
  le_trans (one_le_packConst (E := E)) (packConst_le_cnEff _)

lemma cnEff_pos : (0 : ℝ) < cnEff (Module.finrank ℝ E) :=
  lt_of_lt_of_le zero_lt_one (one_le_cnEff (E := E))

/-- The constant in the (E2) packing bound of Theorem 7.3(B)'s inner assembly: the
`subStickyFrostmanLemma` cardinality constant at the inner grid length
`M_inner = ⌈(n+3)/η₁⌉₊ + 1`, including the blueprint's mixed-regime `δ^{-ε_inner}` loss
(`lem:composed_translation_family`).  It replaces the literal `2` that the old
collapse-hypothesis route produced. -/
noncomputable def e2Const (n : ℕ) (η₁ ε : ℝ) (δ : NNReal) : ℝ :=
  qCardConst n (gridLen n η₁ ε) (cnEff n)
      (prodConst n (gridLen n η₁ ε))
    * (δ : ℝ) ^ (-(1 / ((gridLen n η₁ ε : ℕ) : ℝ)))

/-- The s-uniform `subStickyFrostmanLemma` threshold for the parameters determined by `η₁`, the
target exponent `ε`, and `n = finrank ℝ E` (now that the leaf index is `Type`, this is a clean
`NNReal`).  `δ ≤ ssfδ₀ η₁ ε` is what lets us invoke Lemma 7.5 (s-uniform form) at our specific
`δ`.  The `ε` enters only through the inner grid length `gridLen n η₁ ε`. -/
noncomputable def ssfδ₀ (η₁ ε : ℝ) : NNReal :=
  (exists_threshold_of_eventually_nhdsGT
    (subStickyFrostmanLemma (E := E)
      (1 / ((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ)) (by
        have := one_le_gridLen (Module.finrank ℝ E) η₁ ε
        have h : (0 : ℝ) < ((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ) := by
          exact_mod_cast gridLen_pos (Module.finrank ℝ E) η₁ ε
        positivity)
      (gridLen (Module.finrank ℝ E) η₁ ε) (one_le_gridLen _ _ _)
      (cnEff (Module.finrank ℝ E)) (cnEff_pos (E := E)) (one_le_cnEff (E := E))
      (prodConst (Module.finrank ℝ E) (gridLen (Module.finrank ℝ E) η₁ ε))
      (prodConst_pos _ _)
      ((641 : ℝ) ^ (2 * Module.finrank ℝ E)) (by positivity)
      (max 1 ⌈((2 * (Tube.overlapConstBOTight (Module.finrank ℝ E) : NNReal) : NNReal) : ℝ)⌉₊)
      (Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)))).choose

/-- `ssfδ₀ η₁ ε` is strictly positive (the threshold from `𝓝[>] 0`). -/
lemma ssfδ₀_pos (η₁ ε : ℝ) : 0 < ssfδ₀ (E := E) η₁ ε :=
  (exists_threshold_of_eventually_nhdsGT
    (subStickyFrostmanLemma (E := E)
      (1 / ((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ)) (by
        have := one_le_gridLen (Module.finrank ℝ E) η₁ ε
        have h : (0 : ℝ) < ((gridLen (Module.finrank ℝ E) η₁ ε : ℕ) : ℝ) := by
          exact_mod_cast gridLen_pos (Module.finrank ℝ E) η₁ ε
        positivity)
      (gridLen (Module.finrank ℝ E) η₁ ε) (one_le_gridLen _ _ _)
      (cnEff (Module.finrank ℝ E)) (cnEff_pos (E := E)) (one_le_cnEff (E := E))
      (prodConst (Module.finrank ℝ E) (gridLen (Module.finrank ℝ E) η₁ ε))
      (prodConst_pos _ _)
      ((641 : ℝ) ^ (2 * Module.finrank ℝ E)) (by positivity)
      (max 1 ⌈((2 * (Tube.overlapConstBOTight (Module.finrank ℝ E) : NNReal) : NNReal) : ℝ)⌉₊)
      (Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)))).choose_spec.1
end stickyKatzTaoOfStickyFrostman

end StickyKakeya

end Kakeya
