/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.Spread
public import Kakeya.MultiScaleFac.StoppingKT
public import Kakeya.MultiScaleFac.Transport
public import Kakeya.MultiScaleFac.Witness
public import Kakeya.MultiScaleFac.Bridge

/-!
# From the narrow window to GWZ's window, half (A)

The third bullet on the narrow window of exponent `e'`, and the clamp that widens it back to GWZ's
`ε`-window, together with the constants, the window arithmetic and the good node the two steps ask
for.

This module is the merge of the former `Bullet3GoodNodeA`, `Bullet3CoeffA`, `Bullet3ClampA`,
`Bullet3ConstMergeA`, `Bullet3NarrowSpread`, `Bullet3NarrowA`, `Bullet3AltAdapter`,
`Bullet3ClampInputs`, `Bullet3WindowInstA`.  Each keeps its own section, so its file-level
`open`s and `variable`s stay confined to it. -/

/-!
# Entering the half-(A) third bullet: a good node and the two standing smallness facts

The narrow-window witness package of the half-(A) third bullet,
`Kakeya.StickyKakeya.ssfA_narrow_witness_package`, is entered at a *prescribed* good node
`j ∈ goodNodes 𝒰 b G`, whereas the hypotheses available at the entry point
`Kakeya.StickyKakeya.ssf_bulletThree_of_alternativeTwo` speak only of a majority set: `G ⊆ s` and
`s.card ≤ 2 * G.card`.  The gap is one existence step, supplied here by
`Kakeya.MultiScaleFac.A.exists_goodNode`: the counting lemma
`Kakeya.MultiScaleFac.card_parent_le_mul_card_goodNodes` bounds the whole level `indexSet b` by a
multiple of the good nodes, and the level is nonempty because `s` is, so the good nodes are nonempty
too.

The two remaining small facts are the ones the same entry point leaves implicit: the standing
smallness `δ ≤ 16^{-M}` together with `16 ≤ M` forces `δ < 1`, and `16 ≤ M` forces `0 < M`.  Both
are demanded verbatim by `Kakeya.StickyKakeya.ssfA_narrow_witness_package` and by the clamping step
of the same bullet.
-/

@[expose] public section

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable {ι : Type u}
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### A good node out of a majority set -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **A majority set of leaves produces a good node.**  Since
`Kakeya.MultiScaleFac.card_parent_le_mul_card_goodNodes` bounds `indexSet b` by `4 C²` times
`goodNodes 𝒰 b G`, an empty set of good nodes would force the level to be empty, which it is not.
The membership `j ∈ 𝒰.cover.indexSet b` is returned alongside, as the consumers ask for both. -/
theorem A.exists_goodNode {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (hC : 1 ≤ C) (hs : s.Nonempty)
    (𝒰 : UniformTubeSet s T N C) {b : ℕ} (hb : b ≤ N)
    {G : Finset ι} (hG : G ⊆ s) (hGcard : s.card ≤ 2 * G.card) :
    ∃ j ∈ 𝒰.cover.indexSet b, j ∈ goodNodes 𝒰 b G := by
  classical
  have hIdx : (𝒰.cover.indexSet b).Nonempty := by
    rcases hs with ⟨i0, hi0⟩
    exact ⟨𝒰.cover.assign b i0, 𝒰.cover.assign_mem b hb i0 hi0⟩
  have hIdxPos : 0 < (𝒰.cover.indexSet b).card := Finset.card_pos.mpr hIdx
  have hgoodNe : (goodNodes 𝒰 b G).Nonempty := by
    by_contra hnot
    have hle : ((𝒰.cover.indexSet b).card : NNReal) ≤ 0 := by
      simpa [Finset.not_nonempty_iff_eq_empty.mp hnot] using
        card_parent_le_mul_card_goodNodes hC 𝒰 hb hG hGcard
    have hleNat : (𝒰.cover.indexSet b).card ≤ 0 := by exact_mod_cast hle
    omega
  obtain ⟨j, hj⟩ := hgoodNe
  exact ⟨j, (Finset.filter_subset _ _) hj, hj⟩

/-! ### The two standing smallness facts -/

/-- **The standing smallness of the sharp dichotomy forces `δ < 1`.**

`δ ≤ 16^{-M}` with `M` positive puts `δ` below a negative power of `16`. -/
theorem A.lt_one_of_sixteen_rpow_le {δ : NNReal}
    (hδ16 : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ))) (hM16 : 16 ≤ ssfGridLen δ) :
    δ < 1 := by
  have hM : (16 : ℝ) ≤ (ssfGridLen δ : ℝ) := by exact_mod_cast hM16
  exact hδ16.trans_lt (NNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))

/-- **The grid length of the sharp dichotomy is positive.** -/
theorem A.ssfGridLen_pos {δ : NNReal} (hM16 : 16 ≤ ssfGridLen δ) :
    0 < ssfGridLen δ := by
  omega

end MultiScaleFac

end Kakeya

end

/-!
# The transport level and the coefficient of a narrow window, half (A)

Two independent pieces of bookkeeping for the third bullet of half (A).

## The transport level

`Kakeya.MultiScaleFac.frostmanConstant_nodesIn_rescale_le_of_pairBand` compares the Frostman
constants of two concentric dilates of one level-`b` node, at radii `ρ` and `ρ'`, and it does so
*through a coarse level* `k`: the ancestor split, the band and the packing count all live at that
level.  The hypotheses it puts on `k` are `2δ ≤ σ_k` (the level is not finer than the tube radius),
`4 σ_k ≤ ρ` (the level is coarse enough that the `4ρ`-dilate contains the level-`k` ancestor) and
`σ_k ≤ 4 ρ'` (the level is fine enough that the packing count is bounded).

`Kakeya.MultiScaleFac.A.exists_transport_level` produces such a level from the window bounds
alone, and produces it *symmetrically* in the two radii: the conclusion asserts each of the three
demands for `ρ` and for `ρ'` separately, so the same witness serves whichever of the two radii is
the smaller.  Both ends of the window need it, and neither end knows in advance which of its two
radii is the smaller one, so an asymmetric form would have to be applied twice.

The level is the sharp rounding index of `Kakeya.MultiScaleFac.A.exists_round_index_sharp` taken
at the *smaller* radius; sharpness is retained in the last clause, which is what keeps the packing
count `(4ρ/σ_k)^{2n}` inside a single `Kakeya.MultiScaleFac.scaleGapLoss`.

## The coefficient of one narrow-window scale

The conclusion at a single scale of a narrow window carries a product of five unrelated factors:
the number `K_n` of coarse neighbours covering a dilated node, the band constant `C_b`, the two
node-density bounds `d_m` and `D_m` of
`Kakeya.MultiScaleFac.A.exists_density_pair`, two volume constants of the grid rounding, the
packing factor `Λ` with its own gap loss, and the stopping time's `δ^{-27/⌈\log\log 1/δ⌉}`.

Only the *ratio* `D_m / d_m` survives: it is bounded by the absolute
`Kakeya.MultiScaleFac.nodeDensityRatioConst`, and
`Kakeya.MultiScaleFac.A.density_ratio_le` performs that cancellation.  What is left is a product
of absolute constants against two gap losses, which
`Kakeya.MultiScaleFac.A.narrow_coefficient_le` absorbs into the single displayed
`Kakeya.MultiScaleFac.totalLoss` through `Kakeya.MultiScaleFac.A.const_scaleGapLoss_le`.  No
factor here is a power of `δ` beyond the two gap losses, which is exactly why the whole coefficient
is subpolynomial.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable {ι : Type u}
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The transport level -/

/-- **A transport level for a pair of window radii.**  Given radii `ρ`, `ρ'` bounded below by the
lower endpoint of the window `[a, b]`, there is a grid level `k ≤ b` meeting all three demands of
`Kakeya.MultiScaleFac.frostmanConstant_nodesIn_rescale_le_of_pairBand` *for both radii at once*.
The witness is the sharp rounding index at the smaller radius, and the statement is symmetric. -/
private theorem A.exists_transport_level {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδlt : δ < 1)
    (hδ16 : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ))) (hM : 0 < ssfGridLen δ)
    {ε : ℝ} {a b : ℕ} (hab : a < b) (hbM : b ≤ ssfGridLen δ)
    (hεba : 3 ≤ ε * ((b : ℝ) - (a : ℝ))) {ρ ρ' : NNReal} (hρ1 : ρ ≤ 1)
    (hlo : (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ε
      ≤ (ρ : ℝ))
    (hlo' : (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ε
      ≤ (ρ' : ℝ)) :
    ∃ k : ℕ, k ≤ b ∧ k ≤ ssfGridLen δ ∧
      2 * δ ≤ gridScale δ (ssfGridLen δ) k ∧
      4 * gridScale δ (ssfGridLen δ) k ≤ ρ ∧
      4 * gridScale δ (ssfGridLen δ) k ≤ ρ' ∧
      gridScale δ (ssfGridLen δ) k ≤ 4 * ρ ∧
      gridScale δ (ssfGridLen δ) k ≤ 4 * ρ' ∧
      ((min ρ ρ' : NNReal) : ℝ)
        ≤ 32 * scaleGapLoss 1 δ * (gridScale δ (ssfGridLen δ) k : ℝ) := by
  have hmin1 : min ρ ρ' ≤ 1 := (min_le_left ρ ρ').trans hρ1
  have hloMin : (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ε
      ≤ ((min ρ ρ' : NNReal) : ℝ) := by
    rw [NNReal.coe_min]
    exact le_min hlo hlo'
  obtain ⟨c, hcbb, hcM, hc2, hcspec, hsharp⟩ :=
    MultiScaleFac.A.exists_round_index_sharp hδ hδ1 hδlt hδ16 hM hab hbM hεba hmin1 hloMin
  set sig := gridScale δ (ssfGridLen δ) c
  have h4 : 4 * sig ≤ 32 * sig := mul_le_mul_left (by norm_num) sig
  have h1 : sig ≤ 32 * sig := by
    simpa using mul_le_mul_left (by norm_num : (1 : NNReal) ≤ 32) sig
  have hr4 : ∀ x : NNReal, x ≤ 4 * x := fun x => by
    simpa using mul_le_mul_left (by norm_num : (1 : NNReal) ≤ 4) x
  exact ⟨c, hcbb, hcM, hc2, h4.trans (hcspec.trans (min_le_left ρ ρ')),
    h4.trans (hcspec.trans (min_le_right ρ ρ')),
    h1.trans (hcspec.trans ((min_le_left ρ ρ').trans (hr4 ρ))),
    h1.trans (hcspec.trans ((min_le_right ρ ρ').trans (hr4 ρ'))), hsharp⟩

/-! ### The coefficient of one narrow-window scale -/

/-- **The two node-density bounds enter only through their ratio.**  The coefficient
`D · K_n / d_m · C_b · D_m` produced by `Kakeya.MultiScaleFac.A.hgrid_of_witness` collapses, under
`D_m ≤ R d_m`, to `D` times the absolute constant `K_n C_b R`. -/
private theorem A.density_ratio_le {D : ENNReal} {Kn : ℕ} {Cb R : NNReal} {dm Dm : ENNReal}
    (hdm0 : dm ≠ 0) (hdmtop : dm ≠ ⊤) (hDm : Dm ≤ (R : ENNReal) * dm) :
    D * (Kn : ENNReal) / dm * (Cb : ENNReal) * Dm
      ≤ D * (((Kn : NNReal) * Cb * R : NNReal) : ENNReal) := by
  calc
    D * (Kn : ENNReal) / dm * (Cb : ENNReal) * Dm
        ≤ D * (Kn : ENNReal) / dm * (Cb : ENNReal) * ((R : ENNReal) * dm) :=
          mul_le_mul_right hDm _
    _ = D * (Kn : ENNReal) / dm * dm * (Cb : ENNReal) * (R : ENNReal) := by ac_rfl
    _ = D * (Kn : ENNReal) * (Cb : ENNReal) * (R : ENNReal) := by
          rw [ENNReal.div_mul_cancel hdm0 hdmtop]
    _ = D * (((Kn : NNReal) * Cb * R : NNReal) : ENNReal) := by
          rw [ENNReal.coe_mul, ENNReal.coe_mul, ← ENNReal.coe_natCast]
          ac_rfl

/-- **The whole coefficient of one narrow-window scale is a displayed loss.**  Every factor is
either an absolute constant — the neighbour count `K_n`, the band constant `C_b`, the density ratio
`R`, the two volume constants of the grid rounding, the packing factor `Λ` — or one of the two gap
losses `c₁`, `c₂`, so the product collapses to `Kakeya.MultiScaleFac.totalLoss C K c δ`. -/
private theorem A.narrow_coefficient_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {Kn : ℕ} {Cb R V₁ V₂ Λ C : NNReal} (hC1 : 1 ≤ C)
    (hCle : (Kn : NNReal) * Cb * R * V₁ * V₂ * Λ ≤ C) {K c₁ c₂ c : ℕ} (hc : c₁ + c₂ ≤ c)
    {D X Y dm Dm : ENNReal} (hdm0 : dm ≠ 0) (hdmtop : dm ≠ ⊤)
    (hDm : Dm ≤ (R : ENNReal) * dm)
    (h : X ≤ D * (Kn : ENNReal) / dm * (Cb : ENNReal) * Dm * (V₁ : ENNReal) * (V₂ : ENNReal)
        * ((Λ : ENNReal) * ENNReal.ofReal (scaleGapLoss c₁ δ))
        * ENNReal.ofReal (scaleGapLoss c₂ δ) * Y) :
    X ≤ D * ((C : ENNReal) * totalLoss C K c δ) * Y := by
  set An : NNReal := (Kn : NNReal) * Cb * R * V₁ * V₂ * Λ with hAn
  set A0 : NNReal := max 1 An with hA0
  have hnn : (0 : ℝ) ≤ scaleGapLoss c₁ δ :=
    zero_le_one.trans (one_le_scaleGapLoss c₁ hδ hδ1)
  have hgap : ENNReal.ofReal (scaleGapLoss c₁ δ) * ENNReal.ofReal (scaleGapLoss c₂ δ) =
      ENNReal.ofReal (scaleGapLoss (c₁ + c₂) δ) := by
    rw [← ENNReal.ofReal_mul hnn, MultiScaleFac.A.scaleGapLoss_add hδ c₁ c₂]
  have hAnA0e : (An : ENNReal) ≤ (A0 : ENNReal) := ENNReal.coe_le_coe.mpr (le_max_right 1 An)
  have hcoerce :
      (((Kn : NNReal) * Cb * R : NNReal) : ENNReal) * (V₁ : ENNReal) * (V₂ : ENNReal) *
          (Λ : ENNReal)
        = (An : ENNReal) := by
    rw [hAn]; push_cast; ring
  have hdensity : D * (Kn : ENNReal) / dm * (Cb : ENNReal) * Dm
      ≤ D * (((Kn : NNReal) * Cb * R : NNReal) : ENNReal) :=
    MultiScaleFac.A.density_ratio_le hdm0 hdmtop hDm
  have hconstA : (A0 : ENNReal) * ENNReal.ofReal (scaleGapLoss (c₁ + c₂) δ)
      ≤ (C : ENNReal) * totalLoss C K c δ :=
    MultiScaleFac.A.const_scaleGapLoss_le hδ hδ1 (le_max_left 1 An) (max_le hC1 hCle) hc
  have hcoef :
      D * (Kn : ENNReal) / dm * (Cb : ENNReal) * Dm * (V₁ : ENNReal) * (V₂ : ENNReal) *
          ((Λ : ENNReal) * ENNReal.ofReal (scaleGapLoss c₁ δ)) *
          ENNReal.ofReal (scaleGapLoss c₂ δ)
        ≤ D * ((C : ENNReal) * totalLoss C K c δ) := by
    calc
      D * (Kn : ENNReal) / dm * (Cb : ENNReal) * Dm * (V₁ : ENNReal) * (V₂ : ENNReal) *
            ((Λ : ENNReal) * ENNReal.ofReal (scaleGapLoss c₁ δ)) *
            ENNReal.ofReal (scaleGapLoss c₂ δ)
        ≤ D * (((Kn : NNReal) * Cb * R : NNReal) : ENNReal) * (V₁ : ENNReal) * (V₂ : ENNReal) *
            ((Λ : ENNReal) * ENNReal.ofReal (scaleGapLoss c₁ δ)) *
            ENNReal.ofReal (scaleGapLoss c₂ δ) :=
          mul_le_mul_left (mul_le_mul_left (mul_le_mul_left
            (mul_le_mul_left hdensity _) _) _) _
      _ = D * (An : ENNReal) * ENNReal.ofReal (scaleGapLoss (c₁ + c₂) δ) := by
          rw [← hgap, ← hcoerce]; ring
      _ ≤ D * ((A0 : ENNReal) * ENNReal.ofReal (scaleGapLoss (c₁ + c₂) δ)) := by
          rw [mul_assoc]; exact mul_le_mul_right (mul_le_mul_left hAnA0e _) D
      _ ≤ D * ((C : ENNReal) * totalLoss C K c δ) := mul_le_mul_right hconstA D
  exact h.trans (mul_le_mul_left hcoef Y)

end MultiScaleFac

end Kakeya

end

/-!
# From the narrow window to the `ε`-window, half (A)

The third bullet of alternative (ii) of GWZ Lemma 7.7(A) is stated on the `ε`-window, while the
terminal alternative supplies its witness only on the narrower window of the larger exponent `e'`.
This file is the abstract step that closes that gap: the statement of the bullet *on the narrow
window* is taken as an explicit hypothesis, and the statement *on the `ε`-window* is produced from
it.  Nothing here knows how the narrow-window statement is obtained.

The mechanism is `Kakeya.MultiScaleFac.A.exists_window_clamp`: a scale `ρ` of the `ε`-window is
clamped to a scale `ρ'` of the narrow window that differs from it by at most one
`Kakeya.MultiScaleFac.scaleGapLoss` in either direction.  Whether the clamp moved `ρ` up or down is
decided by `le_total`, and the two cases are the two ends of the window:

* `ρ ≤ ρ'`: the bound descends from the coarser `ρ'` by the container transport, which is
  `Kakeya.MultiScaleFac.A.bulletThree_fineEnd_of_transport`;
* `ρ' ≤ ρ`: the bound ascends from the finer `ρ'` by the ancestor split, which is
  `Kakeya.MultiScaleFac.A.bulletThree_coarseEnd_of_ancestor`.

Both directions pay a transport coefficient built from absolute constants and from powers of the
two gap losses; no factor is a power of `δ` beyond those losses, so the whole coefficient is
absorbed into the displayed `Kakeya.MultiScaleFac.totalLoss`.
-/

@[expose] public section

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable {ι : Type u}
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The two endpoints of the two windows -/

/-- **The lower endpoint of the window grows with the exponent.**

The mirror image of `Kakeya.MultiScaleFac.window_upper_antitone`: on a block the ratio
`σ_a / σ_b` is at least `1`, so raising it to a larger exponent raises the lower endpoint.  Hence
the narrow window sits inside the wide one at the lower end as well. -/
private theorem A.clamp_window_lower_mono {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {M a b : ℕ}
    (hab : a ≤ b) {e e' : ℝ} (hee' : e ≤ e') :
    (gridScale δ M b : ℝ) * ((gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)) ^ e
      ≤ (gridScale δ M b : ℝ) * ((gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)) ^ e' := by
  have hsb : 0 < (gridScale δ M b : ℝ) := by exact_mod_cast gridScale_pos hδ M b
  have hone : 1 ≤ (gridScale δ M a : ℝ) / (gridScale δ M b : ℝ) :=
    (one_le_div hsb).mpr (by exact_mod_cast gridScale_antitone hδ hδ1 M hab)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hone hee') hsb.le

/-- **Every scale of the window is at least the finer grid scale of the block.**

The hypothesis `hbρ` of both ends of the window, read off the lower endpoint at exponent `0`. -/
private theorem A.clamp_gridScale_le_of_window_lower {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {M a b : ℕ} (hab : a ≤ b) {e : ℝ} (he : 0 ≤ e) {ρ : NNReal}
    (hlo : (gridScale δ M b : ℝ) * ((gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)) ^ e
      ≤ (ρ : ℝ)) :
    gridScale δ M b ≤ ρ := by
  have hσbpos : (0 : ℝ) < (gridScale δ M b : ℝ) := by exact_mod_cast gridScale_pos hδ M b
  have hdiv : (1 : ℝ) ≤ (gridScale δ M a : ℝ) / (gridScale δ M b : ℝ) :=
    (one_le_div hσbpos).mpr (by exact_mod_cast gridScale_antitone hδ hδ1 M hab)
  have hbase := mul_le_mul_of_nonneg_left (Real.one_le_rpow hdiv he) hσbpos.le
  rw [mul_one] at hbase
  exact_mod_cast hbase.trans hlo

/-! ### The two ratios that the clamp creates -/

/-- **The packing ratio of a sharply rounded level is a gap loss.**

The generalisation of `Kakeya.MultiScaleFac.A.lambda_le_scaleGapLoss` that the clamp needs: the
sharp rounding is available at the *smaller* of the two clamped radii, so the larger one is within
`32 · scaleGapLoss cA δ` of the rounded grid scale rather than within `32 · scaleGapLoss 1 δ`. -/
private theorem A.clamp_scaled_ratio_pow_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {cA : ℕ}
    {ρ : NNReal} {k : ℕ}
    (hρ : (ρ : ℝ) ≤ 32 * scaleGapLoss cA δ * (gridScale δ (ssfGridLen δ) k : ℝ)) (m : ℕ) :
    (((4 * ρ : NNReal) : ℝ) / (gridScale δ (ssfGridLen δ) k : ℝ)) ^ m
      ≤ (128 : ℝ) ^ m * scaleGapLoss (cA * m) δ := by
  have hsc_pos : (0 : ℝ) < (gridScale δ (ssfGridLen δ) k : ℝ) := by
    exact_mod_cast gridScale_pos hδ (ssfGridLen δ) k
  have hratio_le : ((4 * ρ : NNReal) : ℝ) / (gridScale δ (ssfGridLen δ) k : ℝ)
      ≤ 128 * scaleGapLoss cA δ := by
    have hS1 : (1 : ℝ) ≤ scaleGapLoss cA δ := one_le_scaleGapLoss cA hδ hδ1
    rw [div_le_iff₀ hsc_pos]
    push_cast
    linarith [hρ]
  calc
    (((4 * ρ : NNReal) : ℝ) / (gridScale δ (ssfGridLen δ) k : ℝ)) ^ m
        ≤ (128 * scaleGapLoss cA δ) ^ m :=
          pow_le_pow_left₀ (by positivity) hratio_le m
    _ = (128 : ℝ) ^ m * scaleGapLoss cA δ ^ m := mul_pow _ _ m
    _ = (128 : ℝ) ^ m * scaleGapLoss (cA * m) δ := by
          rw [MultiScaleFac.A.scaleGapLoss_pow hδ cA m]

/-- **A real power of the clamp ratio is a gap loss.**

The clamp keeps `x ≤ scaleGapLoss cB δ · y`, and the exponent `η (m + 1)` of the third bullet lies
in `[0, 1]`, so the residual factor `(x / y) ^ ζ` never exceeds the loss itself. -/
private theorem A.clamp_ratio_rpow_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {cB : ℕ}
    {x y : NNReal} (hy : 0 < (y : ℝ)) (hxy : (x : ℝ) ≤ scaleGapLoss cB δ * (y : ℝ))
    {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    ((x : ℝ) / (y : ℝ)) ^ ζ ≤ scaleGapLoss cB δ := by
  calc ((x : ℝ) / (y : ℝ)) ^ ζ ≤ scaleGapLoss cB δ ^ ζ :=
        Real.rpow_le_rpow (div_nonneg (by positivity) hy.le) ((div_le_iff₀ hy).mpr hxy) hζ0
    _ ≤ scaleGapLoss cB δ :=
        Real.rpow_le_self_of_one_le (one_le_scaleGapLoss cB hδ hδ1) hζ1

/-- **A natural power of the clamp ratio is a gap loss.**

The volume ratio of the container transport enters to the power `n - 1`. -/
private theorem A.clamp_ratio_pow_le {δ : NNReal} (hδ : 0 < δ) (_hδ1 : δ ≤ 1) {cB : ℕ}
    {x y : NNReal} (hy : 0 < (y : ℝ)) (hxy : (x : ℝ) ≤ scaleGapLoss cB δ * (y : ℝ)) (m : ℕ) :
    ((x : ℝ) / (y : ℝ)) ^ m ≤ scaleGapLoss (cB * m) δ := by
  calc ((x : ℝ) / (y : ℝ)) ^ m ≤ scaleGapLoss cB δ ^ m :=
        pow_le_pow_left₀ (div_nonneg (by positivity) hy.le) ((div_le_iff₀ hy).mpr hxy) m
    _ = scaleGapLoss (cB * m) δ := MultiScaleFac.A.scaleGapLoss_pow hδ cB m

/-! ### Merging the transport coefficient into the displayed loss -/

/-- **A narrow-window bound and one transport coefficient make one displayed loss.**  The shape in
which both ends of the window leave their conclusion: the coefficient inherited from the narrow
window times the coefficient of the transport, against the Frostman constant at the clamped radius,
collapsed by `Kakeya.MultiScaleFac.A.prod_le` into a single `Kakeya.MultiScaleFac.totalLoss`. -/
private theorem A.clamp_merge {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {C₀ B C : NNReal}
    (hC₀ : 1 ≤ C₀) (hB : 1 ≤ B) {K₀ K₂ K c₀ c₂ c : ℕ} (hC : C₀ * B ≤ C) (hK : K₀ + K₂ ≤ K)
    (hc : c₀ + c₂ ≤ c) {X F Y : ENNReal}
    (hF : F ≤ (B : ENNReal) * totalLoss B K₂ c₂ δ)
    (h : X ≤ (C₀ : ENNReal) * totalLoss C₀ K₀ c₀ δ * F * Y) :
    X ≤ (C : ENNReal) * totalLoss C K c δ * Y := by
  have hpre : X ≤ ((C₀ : ENNReal) * totalLoss C₀ K₀ c₀ δ) *
      ((B : ENNReal) * totalLoss B K₂ c₂ δ) * Y :=
    h.trans (mul_le_mul' (mul_le_mul' le_rfl hF) le_rfl)
  exact MultiScaleFac.A.prod_le hδ hδ1 (le_rfl : (1 : NNReal) ≤ (1 : NNReal)) hC₀ hB
    (by simpa using hC) hK hc (by simpa using hpre)

/-- **The packing count of the fine-end transport is a constant times a gap loss.**

The real-valued half of `Kakeya.MultiScaleFac.A.clamp_fine_factor_le`: the packing ratio is
bounded by `Kakeya.MultiScaleFac.A.clamp_scaled_ratio_pow_le` and the rest of the factor is
absolute. -/
private theorem A.clamp_fine_pack_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {n cA : ℕ}
    {Cu : NNReal} {ρ' : NNReal} {k : ℕ}
    (hσρ' : (ρ' : ℝ) ≤ 32 * scaleGapLoss cA δ * (gridScale δ (ssfGridLen δ) k : ℝ)) :
    2 * (25 : ℝ) ^ (2 * n)
        * (((4 * ρ' : NNReal) : ℝ) / (gridScale δ (ssfGridLen δ) k : ℝ)) ^ (2 * n) * (Cu : ℝ)
      ≤ 2 * (25 : ℝ) ^ (2 * n) * (128 : ℝ) ^ (2 * n) * (Cu : ℝ)
          * scaleGapLoss (cA * (2 * n)) δ := by
  have hratio := MultiScaleFac.A.clamp_scaled_ratio_pow_le hδ hδ1 hσρ' (2 * n)
  have := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hratio (by positivity : (0 : ℝ) ≤ 2 * (25 : ℝ) ^ (2 * n)))
    (NNReal.coe_nonneg Cu)
  linarith only [this]

/-- **The volume ratio of the fine-end transport is a gap loss.**

The other real-valued half of `Kakeya.MultiScaleFac.A.clamp_fine_factor_le`, from
`Kakeya.MultiScaleFac.A.clamp_ratio_pow_le`. -/
private theorem A.clamp_fine_vol_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {n cB : ℕ}
    {ρ ρ' : NNReal} (hρpos : 0 < (ρ : ℝ)) (hgap : (ρ' : ℝ) ≤ scaleGapLoss cB δ * (ρ : ℝ)) :
    (scaleGapVolConst n : ℝ) * ((ρ' : ℝ) / (ρ : ℝ)) ^ (n - 1)
      ≤ (scaleGapVolConst n : ℝ) * scaleGapLoss (cB * (n - 1)) δ :=
  mul_le_mul_of_nonneg_left
    (MultiScaleFac.A.clamp_ratio_pow_le hδ hδ1 hρpos hgap (n - 1)) (NNReal.coe_nonneg _)

/-- **The coefficient of the fine-end transport is a displayed loss.**  The container transport
contributes the packing count `(4ρ'/σ_k)^{2n}`, the neighbour count `K_n`, the band constant `C_b`
and the volume ratio `(ρ'/ρ)^{n-1}`; the two ratios are gap losses and what remains is absolute. -/
private theorem A.clamp_fine_factor_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {n Kn cA cB cF K₂ : ℕ} {Cu Cb B : NNReal} {ρ ρ' : NNReal} {k : ℕ} (hρpos : 0 < (ρ : ℝ))
    (hσρ' : (ρ' : ℝ) ≤ 32 * scaleGapLoss cA δ * (gridScale δ (ssfGridLen δ) k : ℝ))
    (hgap : (ρ' : ℝ) ≤ scaleGapLoss cB δ * (ρ : ℝ)) (hB : 1 ≤ B)
    (hBle : 2 * 25 ^ (2 * n) * 128 ^ (2 * n) * Cu * (Kn : NNReal) * Cb * scaleGapVolConst n ≤ B)
    (hcF : cA * (2 * n) + cB * (n - 1) ≤ cF) :
    ENNReal.ofReal (2 * (25 : ℝ) ^ (2 * n)
          * (((4 * ρ' : NNReal) : ℝ) / (gridScale δ (ssfGridLen δ) k : ℝ)) ^ (2 * n) * (Cu : ℝ))
        * ((Kn : ENNReal) * (Cb : ENNReal))
        * ENNReal.ofReal ((scaleGapVolConst n : ℝ) * ((ρ' : ℝ) / (ρ : ℝ)) ^ (n - 1))
      ≤ (B : ENNReal) * totalLoss B K₂ cF δ := by
  set A1 : ℝ := 2 * (25 : ℝ) ^ (2 * n)
          * (((4 * ρ' : NNReal) : ℝ) / (gridScale δ (ssfGridLen δ) k : ℝ)) ^ (2 * n) * (Cu : ℝ)
    with hA1def
  set A2 : ℝ := (scaleGapVolConst n : ℝ) * ((ρ' : ℝ) / (ρ : ℝ)) ^ (n - 1) with hA2def
  set A1c : ℝ := 2 * (25 : ℝ) ^ (2 * n) * (128 : ℝ) ^ (2 * n) * (Cu : ℝ) with hA1cdef
  set A2c : ℝ := (scaleGapVolConst n : ℝ) with hA2cdef
  set Ac : NNReal := 2 * 25 ^ (2 * n) * 128 ^ (2 * n) * Cu * (Kn : NNReal) * Cb * scaleGapVolConst n
    with hAcdef
  set A0 : NNReal := max 1 Ac with hA0def
  have hpack : A1 ≤ A1c * scaleGapLoss (cA * (2 * n)) δ :=
    MultiScaleFac.A.clamp_fine_pack_le hδ hδ1 hσρ'
  have hvol : A2 ≤ A2c * scaleGapLoss (cB * (n - 1)) δ :=
    MultiScaleFac.A.clamp_fine_vol_le hδ hδ1 hρpos hgap
  have hE1 : ENNReal.ofReal A1 ≤ ENNReal.ofReal (A1c * scaleGapLoss (cA * (2 * n)) δ) :=
    ENNReal.ofReal_le_ofReal hpack
  have hE2 : ENNReal.ofReal A2 ≤ ENNReal.ofReal (A2c * scaleGapLoss (cB * (n - 1)) δ) :=
    ENNReal.ofReal_le_ofReal hvol
  have hA1c_nonneg : 0 ≤ A1c := by
    dsimp only [A1c]
    positivity
  have hA2c_nonneg : 0 ≤ A2c := NNReal.coe_nonneg _
  have hs1nn : (0 : ℝ) ≤ scaleGapLoss (cA * (2 * n)) δ :=
    zero_le_one.trans (one_le_scaleGapLoss (cA * (2 * n)) hδ hδ1)
  have hE1c : ENNReal.ofReal (A1c * scaleGapLoss (cA * (2 * n)) δ) =
      ENNReal.ofReal A1c * ENNReal.ofReal (scaleGapLoss (cA * (2 * n)) δ) :=
    ENNReal.ofReal_mul hA1c_nonneg
  have hE2c : ENNReal.ofReal (A2c * scaleGapLoss (cB * (n - 1)) δ) =
      ENNReal.ofReal A2c * ENNReal.ofReal (scaleGapLoss (cB * (n - 1)) δ) :=
    ENNReal.ofReal_mul hA2c_nonneg
  have hgapprod : ENNReal.ofReal (scaleGapLoss (cA * (2 * n)) δ) *
        ENNReal.ofReal (scaleGapLoss (cB * (n - 1)) δ) =
      ENNReal.ofReal (scaleGapLoss (cA * (2 * n) + cB * (n - 1)) δ) := by
    rw [← ENNReal.ofReal_mul hs1nn,
        MultiScaleFac.A.scaleGapLoss_add hδ (cA * (2 * n)) (cB * (n - 1))]
  have hA1c_coe : A1c = ((2 * 25 ^ (2 * n) * 128 ^ (2 * n) * Cu : NNReal) : ℝ) := by
    rw [hA1cdef]; push_cast; ring
  have hA2c_coe : ENNReal.ofReal A2c = (scaleGapVolConst n : ENNReal) := by
    rw [hA2cdef]; exact ENNReal.ofReal_coe_nnreal
  have hconst_eq : ENNReal.ofReal A1c * (Kn : ENNReal) * (Cb : ENNReal) * ENNReal.ofReal A2c =
      (Ac : ENNReal) := by
    rw [hA1c_coe, hA2c_coe, ENNReal.ofReal_coe_nnreal, hAcdef]
    push_cast
    ring
  have hAcA0 : (Ac : ENNReal) ≤ (A0 : ENNReal) := ENNReal.coe_le_coe.mpr (le_max_right 1 Ac)
  have hconstloss : (A0 : ENNReal) * ENNReal.ofReal (scaleGapLoss (cA * (2 * n) + cB * (n - 1)) δ) ≤
      (B : ENNReal) * totalLoss B K₂ cF δ :=
    MultiScaleFac.A.const_scaleGapLoss_le hδ hδ1 (le_max_left 1 Ac) (max_le hB hBle) hcF
  calc
    ENNReal.ofReal A1 * ((Kn : ENNReal) * (Cb : ENNReal)) * ENNReal.ofReal A2
        ≤ ENNReal.ofReal (A1c * scaleGapLoss (cA * (2 * n)) δ) *
            ((Kn : ENNReal) * (Cb : ENNReal))
                * ENNReal.ofReal (A2c * scaleGapLoss (cB * (n - 1)) δ) := by
          exact mul_le_mul' (mul_le_mul_left hE1 _) hE2
      _ = (Ac : ENNReal) * (ENNReal.ofReal (scaleGapLoss (cA * (2 * n)) δ) *
            ENNReal.ofReal (scaleGapLoss (cB * (n - 1)) δ)) := by
          rw [hE1c, hE2c, ← hconst_eq]; ring
      _ = (Ac : ENNReal) * ENNReal.ofReal (scaleGapLoss (cA * (2 * n) + cB * (n - 1)) δ) := by
          rw [hgapprod]
      _ ≤ (A0 : ENNReal) * ENNReal.ofReal (scaleGapLoss (cA * (2 * n) + cB * (n - 1)) δ) := by
          exact mul_le_mul_left hAcA0 _
      _ ≤ (B : ENNReal) * totalLoss B K₂ cF δ := hconstloss

/-- **The coefficient of the coarse-end ascent is a displayed loss.**  The coefficient is the
reciprocal of the lower volume constant, the residual `(ρ/ρ')^{ζ'}` of the left-hand side, the
upper volume constant and the packing factor `Λ`; the first, third and fourth are absolute, and the
second and the gap loss inside `Λ` add their budgets. -/
private theorem A.clamp_coarse_factor_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {cB cΛ cF K₂ : ℕ}
    {V W Λ₀ B : NNReal} (hB : 1 ≤ B) (hBle : V * (W * Λ₀) ≤ B) (hcF : cB + cΛ ≤ cF) :
    (V : ENNReal) * (ENNReal.ofReal (scaleGapLoss cB δ)
        * ((W * (Λ₀ * Real.toNNReal (scaleGapLoss cΛ δ)) : NNReal) : ENNReal))
      ≤ (B : ENNReal) * totalLoss B K₂ cF δ := by
  have hnn : (0 : ℝ) ≤ scaleGapLoss cB δ :=
    zero_le_one.trans (one_le_scaleGapLoss cB hδ hδ1)
  calc
    (V : ENNReal) * (ENNReal.ofReal (scaleGapLoss cB δ)
          * ((W * (Λ₀ * Real.toNNReal (scaleGapLoss cΛ δ)) : NNReal) : ENNReal))
      = ((V * (W * Λ₀) : NNReal) : ENNReal) *
          (ENNReal.ofReal (scaleGapLoss cB δ) * ENNReal.ofReal (scaleGapLoss cΛ δ)) := by
          simp [ENNReal.ofReal, ENNReal.coe_mul, mul_assoc, mul_left_comm]
    _ = ((V * (W * Λ₀) : NNReal) : ENNReal) *
          ENNReal.ofReal (scaleGapLoss (cB + cΛ) δ) := by
          rw [← ENNReal.ofReal_mul hnn, MultiScaleFac.A.scaleGapLoss_add hδ cB cΛ]
    _ ≤ ((max 1 (V * (W * Λ₀)) : NNReal) : ENNReal)
          * ENNReal.ofReal (scaleGapLoss (cB + cΛ) δ) :=
          mul_le_mul_left (ENNReal.coe_le_coe.mpr (le_max_right 1 _)) _
    _ ≤ (B : ENNReal) * totalLoss B K₂ cF δ :=
          MultiScaleFac.A.const_scaleGapLoss_le hδ hδ1 (le_max_left 1 _) (max_le hB hBle) hcF

/-! ### The two ends of the clamp -/

open scoped Classical in
/-- **The clamped bound descends to a finer scale of the `ε`-window.**

The case `ρ ≤ ρ'` of the clamp: the narrow-window bound sits at the coarser radius `ρ'`, and
`Kakeya.MultiScaleFac.A.bulletThree_fineEnd_of_transport` moves it down to `ρ`.  The transport
coefficient is absorbed by `Kakeya.MultiScaleFac.A.clamp_fine_factor_le`. -/
private theorem A.clamp_bulletThree_fineEnd {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {Cu : NNReal} [DecidableEq ι]
    (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu) (hs : s.Nonempty)
    {k b Kn : ℕ} (hkb : k ≤ b) (hb : b ≤ ssfGridLen δ) (hk : k ≤ ssfGridLen δ)
    (h2δ : 2 * δ ≤ gridScale δ (ssfGridLen δ) k) {Φ : ENNReal} {Cb : NNReal}
    (hP : ∀ p ∈ 𝒰.cover.indexSet k, ∃ P ⊆ 𝒰.cover.indexSet k, P.card ≤ Kn ∧
      𝒰.nodesIn b (((𝒰.cover.tube k p).rescale
          (8 * gridScale δ (ssfGridLen δ) k)).toConvexSpaceBody)
        ⊆ P.biUnion (fun q =>
            (coverClass s (𝒰.cover.assign k) q).image (𝒰.cover.assign b)))
    (hbandLo : ∀ p ∈ 𝒰.cover.indexSet k,
      Φ ≤ Kakeya.maxDensity ((coverClass s (𝒰.cover.assign k) p).image (𝒰.cover.assign b))
          (fun w => (𝒰.cover.tube b w).toConvexSpaceBody))
    (hbandHi : ∀ p ∈ 𝒰.cover.indexSet k,
      Kakeya.maxDensity ((coverClass s (𝒰.cover.assign k) p).image (𝒰.cover.assign b))
          (fun w => (𝒰.cover.tube b w).toConvexSpaceBody) ≤ (Cb : ENNReal) * Φ)
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet b) {ρ ρ' : NNReal}
    (hbρ : gridScale δ (ssfGridLen δ) b ≤ ρ) (hρ : 4 * gridScale δ (ssfGridLen δ) k ≤ ρ)
    (hρρ' : ρ ≤ ρ') (hρ'4 : ρ' ≤ 4) (hr : gridScale δ (ssfGridLen δ) k ≤ 4 * ρ')
    {cA cB : ℕ}
    (hσρ' : (ρ' : ℝ) ≤ 32 * scaleGapLoss cA δ * (gridScale δ (ssfGridLen δ) k : ℝ))
    (hgap : (ρ' : ℝ) ≤ scaleGapLoss cB δ * (ρ : ℝ))
    {ζ' : ℝ} (hζ' : 0 ≤ ζ')
    {C₀ B C : NNReal} {K₀ K₂ K c₀ cF c : ℕ} (hC₀ : 1 ≤ C₀) (hB : 1 ≤ B)
    (hBle : 2 * 25 ^ (2 * Module.finrank ℝ E) * 128 ^ (2 * Module.finrank ℝ E) * Cu
        * (Kn : NNReal) * Cb * scaleGapVolConst (Module.finrank ℝ E) ≤ B)
    (hcF : cA * (2 * Module.finrank ℝ E) + cB * (Module.finrank ℝ E - 1) ≤ cF)
    (hC : C₀ * B ≤ C) (hK : K₀ + K₂ ≤ K) (hc : c₀ + cF ≤ c)
    (hbound : ENNReal.ofReal (((ρ' : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ζ')
      ≤ (C₀ : ENNReal) * totalLoss C₀ K₀ c₀ δ
          * ConvexSpaceBody.frostmanConstant
              (𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ').toConvexSpaceBody)
              (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
              ((𝒰.cover.tube b j).rescale ρ').toConvexSpaceBody) :
    ENNReal.ofReal (((ρ : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ζ')
      ≤ (C : ENNReal) * totalLoss C K c δ
          * ConvexSpaceBody.frostmanConstant
              (𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody)
              (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
              ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody := by
  classical
  have hρpos : (0 : ℝ) < (ρ : ℝ) := by
    have hskpos : (0 : ℝ) < (gridScale δ (ssfGridLen δ) k : ℝ) := by
      exact_mod_cast gridScale_pos hδ (ssfGridLen δ) k
    have hρR : 4 * (gridScale δ (ssfGridLen δ) k : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ
    linarith
  exact MultiScaleFac.A.clamp_merge hδ hδ1 hC₀ hB hC hK hc
    (MultiScaleFac.A.clamp_fine_factor_le (K₂ := K₂) hδ hδ1 hρpos hσρ' hgap hB hBle hcF)
    (MultiScaleFac.A.bulletThree_fineEnd_of_transport hδ hδ1 𝒰 hs hkb hb hk h2δ hP
      hbandLo hbandHi hj hbρ hρ hρρ' hρ'4 hr hζ' hbound)

open scoped Classical in
/-- **The clamped bound ascends to a coarser scale of the `ε`-window.**  The case `ρ' ≤ ρ` of the
clamp: the narrow-window bound sits at the finer radius `ρ'`, and
`Kakeya.MultiScaleFac.A.bulletThree_coarseEnd_of_ancestor` lifts it to `ρ`, the sharply rounded
ancestor count `Λ` being a gap loss. -/
private theorem A.clamp_bulletThree_coarseEnd {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {Cu : NNReal}
    (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu) (hCu : 1 ≤ Cu) (hs : s.Nonempty)
    {k b : ℕ} (hk : k ≤ ssfGridLen δ) (hb : b ≤ ssfGridLen δ) (hkb : k ≤ b)
    (h2δ : 2 * δ ≤ gridScale δ (ssfGridLen δ) k)
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet b) {ρ ρ' : NNReal}
    (hbρ' : gridScale δ (ssfGridLen δ) b ≤ ρ')
    (hkρ' : 4 * gridScale δ (ssfGridLen δ) k ≤ ρ') (hρ'ρ : ρ' ≤ ρ)
    {cA cB : ℕ}
    (hσρ : (ρ : ℝ) ≤ 32 * scaleGapLoss cA δ * (gridScale δ (ssfGridLen δ) k : ℝ))
    (hgap : (ρ : ℝ) ≤ scaleGapLoss cB δ * (ρ' : ℝ))
    {ζ' : ℝ} (hζ0 : 0 ≤ ζ') (hζ1 : ζ' ≤ 1)
    {C₀ B C : NNReal} {K₀ K₂ K c₀ cF c : ℕ} (hC₀ : 1 ≤ C₀) (hB : 1 ≤ B)
    (hBle : (Tube.le_volume.c (Module.finrank ℝ E))⁻¹
        * (Tube.volume_le.C (Module.finrank ℝ E)
            * (2 * 25 ^ (2 * Module.finrank ℝ E) * 128 ^ (2 * Module.finrank ℝ E) * Cu ^ 6)) ≤ B)
    (hcF : cB + cA * (2 * Module.finrank ℝ E) ≤ cF)
    (hC : C₀ * B ≤ C) (hK : K₀ + K₂ ≤ K) (hc : c₀ + cF ≤ c)
    (hbound : ENNReal.ofReal (((ρ' : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ζ')
      ≤ (C₀ : ENNReal) * totalLoss C₀ K₀ c₀ δ
          * ConvexSpaceBody.frostmanConstant
              (𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ').toConvexSpaceBody)
              (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
              ((𝒰.cover.tube b j).rescale ρ').toConvexSpaceBody) :
    ENNReal.ofReal (((ρ : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ζ')
      ≤ (C : ENNReal) * totalLoss C K c δ
          * ConvexSpaceBody.frostmanConstant
              (𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody)
              (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
              ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody := by
  classical
  set nn : ℕ := Module.finrank ℝ E with hnn
  set sk : ℝ := (gridScale δ (ssfGridLen δ) k : ℝ) with hsk
  set Dcoef : ENNReal := (C₀ : ENNReal) * totalLoss C₀ K₀ c₀ δ with hD
  set Lcoef : ENNReal := ENNReal.ofReal (scaleGapLoss cB δ) with hL
  set Lam0 : NNReal := 2 * 25 ^ (2 * nn) * 128 ^ (2 * nn) * Cu ^ 6 with hLam0
  set Lam : NNReal := Lam0 * Real.toNNReal (scaleGapLoss (cA * (2 * nn)) δ) with hLam
  set V : NNReal := (Tube.le_volume.c (Module.finrank ℝ E))⁻¹ with hV
  set W : NNReal := Tube.volume_le.C (Module.finrank ℝ E) with hW
  set Fcoef : ENNReal := (V : ENNReal) * Lcoef * ((W * Lam : NNReal) : ENNReal) with hFcoef
  set X : ENNReal := ENNReal.ofReal (((ρ : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ζ') with hX
  set CF : ENNReal := ConvexSpaceBody.frostmanConstant
      (𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody)
      (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
      ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody with hCF
  have hgrk : (0 : NNReal) < gridScale δ (ssfGridLen δ) k :=
    gridScale_pos hδ (ssfGridLen δ) k
  have h4k : (0 : NNReal) < 4 * gridScale δ (ssfGridLen δ) k :=
    mul_pos (by norm_num : (0 : NNReal) < 4) hgrk
  have hρ'pos_nn : (0 : NNReal) < ρ' := lt_of_lt_of_le h4k hkρ'
  have hρ'pos : (0 : ℝ) < (ρ' : ℝ) := by exact_mod_cast hρ'pos_nn
  have hLleReal : ((ρ : ℝ) / (ρ' : ℝ)) ^ ζ' ≤ scaleGapLoss cB δ :=
    MultiScaleFac.A.clamp_ratio_rpow_le hδ hδ1 hρ'pos hgap hζ0 hζ1
  have hLle : ENNReal.ofReal (((ρ : ℝ) / (ρ' : ℝ)) ^ ζ') ≤ Lcoef :=
    ENNReal.ofReal_le_ofReal hLleReal
  have hgl_nonneg : 0 ≤ (scaleGapLoss (cA * (2 * nn)) δ : ℝ) :=
    le_trans zero_le_one (one_le_scaleGapLoss (cA * (2 * nn)) hδ hδ1)
  have hLam0R : (Lam0 : ℝ) = 2 * (25 : ℝ) ^ (2 * nn) * (128 : ℝ) ^ (2 * nn) * (Cu : ℝ) ^ 6 := by
    dsimp [Lam0]
  have hLamR : (Lam : ℝ) = (Lam0 : ℝ) * (scaleGapLoss (cA * (2 * nn)) δ : ℝ) := by
    rw [hLam, NNReal.coe_mul, Real.coe_toNNReal _ hgl_nonneg]
  have hratio : ((((4 * ρ : NNReal) : ℝ) / sk) ^ (2 * nn)) ≤
      (128 : ℝ) ^ (2 * nn) * (scaleGapLoss (cA * (2 * nn)) δ : ℝ) :=
    MultiScaleFac.A.clamp_scaled_ratio_pow_le hδ hδ1 hσρ (2 * nn)
  have hLam_le :
      2 * (25 : ℝ) ^ (2 * nn) * (((4 * ρ : NNReal) : ℝ) / sk) ^ (2 * nn)
          * (Cu : ℝ) * ((Cu : ℝ) ^ 5) ≤ (Lam : ℝ) := by
    calc
      2 * (25 : ℝ) ^ (2 * nn) * (((4 * ρ : NNReal) : ℝ) / sk) ^ (2 * nn) * (Cu : ℝ) * ((Cu : ℝ) ^ 5)
          = (2 * (25 : ℝ) ^ (2 * nn) * (Cu : ℝ) * ((Cu : ℝ) ^ 5)) *
            ((((4 * ρ : NNReal) : ℝ) / sk) ^ (2 * nn)) := by
              ring
      _ ≤ (2 * (25 : ℝ) ^ (2 * nn) * (Cu : ℝ) * ((Cu : ℝ) ^ 5)) *
            ((128 : ℝ) ^ (2 * nn) * (scaleGapLoss (cA * (2 * nn)) δ : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (2 * (25 : ℝ) ^ (2 * nn) * (128 : ℝ) ^ (2 * nn) * (Cu : ℝ) ^ 6) *
            (scaleGapLoss (cA * (2 * nn)) δ : ℝ) := by
              ring
      _ = (Lam : ℝ) := by rw [hLamR, hLam0R]
  have hmain := MultiScaleFac.A.bulletThree_coarseEnd_of_ancestor hδ hδ1 𝒰 hCu hs hk hb hkb h2δ hj
      hbρ' hkρ' hρ'ρ (Λ := Lam) hLam_le (D := Dcoef) (L := Lcoef) hLle hbound
  have hcoarse : Fcoef ≤ (B : ENNReal) * totalLoss B K₂ cF δ := by
    dsimp only [Fcoef]
    rw [mul_assoc]
    exact MultiScaleFac.A.clamp_coarse_factor_le hδ hδ1 (cB := cB) (cΛ := cA * (2 * nn))
      (cF := cF) (K₂ := K₂) (V := V) (W := W) (Λ₀ := Lam0) (B := B) hB hBle hcF
  have hre : X ≤ Dcoef * Fcoef * CF := by
    dsimp only [Fcoef]
    calc
      X ≤ (V : ENNReal) * (Lcoef * Dcoef * ((W * Lam : NNReal) : ENNReal)) * CF := hmain
      _ = Dcoef * ((V : ENNReal) * Lcoef * ((W * Lam : NNReal) : ENNReal)) * CF := by ring
  exact MultiScaleFac.A.clamp_merge hδ hδ1 hC₀ hB (c₂ := cF) hC hK hc hcoarse hre

/-! ### The narrow window implies the `ε`-window -/

/-- **The sharp rounding of the smaller radius serves the larger one too.**  The level of
`Kakeya.MultiScaleFac.A.exists_transport_level` is obtained by rounding sharply at the smaller of
the two clamped radii, so the larger radius is within one further
`Kakeya.MultiScaleFac.scaleGapLoss` of the rounded grid scale. -/
private theorem A.clamp_sharp_transfer {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {cg k : ℕ}
    {x y : NNReal}
    (hx : (x : ℝ) ≤ 32 * scaleGapLoss 1 δ * (gridScale δ (ssfGridLen δ) k : ℝ))
    (hxy : (y : ℝ) ≤ scaleGapLoss cg δ * (x : ℝ)) :
    (y : ℝ) ≤ 32 * scaleGapLoss (cg + 1) δ * (gridScale δ (ssfGridLen δ) k : ℝ) := by
  have hSg : (0 : ℝ) ≤ scaleGapLoss cg δ :=
    zero_le_one.trans (one_le_scaleGapLoss cg hδ hδ1)
  calc
    (y : ℝ) ≤ scaleGapLoss cg δ * (x : ℝ) := hxy
    _ ≤ scaleGapLoss cg δ * (32 * scaleGapLoss 1 δ * (gridScale δ (ssfGridLen δ) k : ℝ)) :=
        mul_le_mul_of_nonneg_left hx hSg
    _ = 32 * (scaleGapLoss cg δ * scaleGapLoss 1 δ) * (gridScale δ (ssfGridLen δ) k : ℝ) := by
        ring
    _ = 32 * scaleGapLoss (cg + 1) δ * (gridScale δ (ssfGridLen δ) k : ℝ) := by
        rw [MultiScaleFac.A.scaleGapLoss_add hδ cg 1]

/-- **Every scale of the `ε`-window comes with a clamped partner and a transport level.**  The
scale-side preparation shared by the two ends of the window: the partner `ρ'` is the clamp of `ρ`
into the narrow window, `k` is the transport level of the pair, and
`Kakeya.MultiScaleFac.A.clamp_sharp_transfer` makes the packing bound available at both radii. -/
private theorem A.clamp_exists_window_data {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδlt : δ < 1)
    (hδ16 : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ))) (hM : 0 < ssfGridLen δ)
    {a b : ℕ} (hab : a < b) (hbM : b ≤ ssfGridLen δ)
    {ε e' : ℝ} (hε0 : 0 ≤ ε) (hεe' : ε ≤ e') (hεba : 3 ≤ ε * ((b : ℝ) - (a : ℝ)))
    {cg : ℕ} (hstep : (e' - ε) * ((b : ℝ) - (a : ℝ)) ≤ (cg : ℝ))
    (hnwne : (gridScale δ (ssfGridLen δ) b : ℝ)
          * ((gridScale δ (ssfGridLen δ) a : ℝ)
              / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e'
        ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
          * ((gridScale δ (ssfGridLen δ) b : ℝ)
              / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e')
    (hwin1 : (gridScale δ (ssfGridLen δ) a : ℝ)
          * ((gridScale δ (ssfGridLen δ) b : ℝ)
              / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ ε ≤ 1)
    {ρ : NNReal}
    (hlo : (gridScale δ (ssfGridLen δ) b : ℝ)
          * ((gridScale δ (ssfGridLen δ) a : ℝ)
              / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ε ≤ (ρ : ℝ))
    (hhi : (ρ : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
          * ((gridScale δ (ssfGridLen δ) b : ℝ)
              / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ ε) :
    ∃ (ρ' : NNReal) (k : ℕ),
      (gridScale δ (ssfGridLen δ) b : ℝ)
          * ((gridScale δ (ssfGridLen δ) a : ℝ)
              / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e' ≤ (ρ' : ℝ) ∧
      (ρ' : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
          * ((gridScale δ (ssfGridLen δ) b : ℝ)
              / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e' ∧
      k ≤ b ∧ k ≤ ssfGridLen δ ∧
      2 * δ ≤ gridScale δ (ssfGridLen δ) k ∧
      4 * gridScale δ (ssfGridLen δ) k ≤ ρ ∧
      4 * gridScale δ (ssfGridLen δ) k ≤ ρ' ∧
      gridScale δ (ssfGridLen δ) k ≤ 4 * ρ' ∧
      gridScale δ (ssfGridLen δ) b ≤ ρ ∧
      gridScale δ (ssfGridLen δ) b ≤ ρ' ∧
      ρ' ≤ 1 ∧
      (ρ' : ℝ) ≤ scaleGapLoss cg δ * (ρ : ℝ) ∧
      (ρ : ℝ) ≤ scaleGapLoss cg δ * (ρ' : ℝ) ∧
      (ρ' : ℝ) ≤ 32 * scaleGapLoss (cg + 1) δ * (gridScale δ (ssfGridLen δ) k : ℝ) ∧
      (ρ : ℝ) ≤ 32 * scaleGapLoss (cg + 1) δ * (gridScale δ (ssfGridLen δ) k : ℝ) := by
  classical
  have hdltR : (δ : ℝ) < 1 := by exact_mod_cast hδlt
  have hable : a ≤ b := le_of_lt hab
  have he0' : (0 : ℝ) ≤ e' := le_trans hε0 hεe'
  have hrho1 : ρ ≤ 1 := by exact_mod_cast hhi.trans hwin1
  obtain ⟨rhoN, hlon, hhin, hclampA, hclampB⟩ :=
    MultiScaleFac.A.exists_window_clamp hδ hdltR hM hstep hnwne hlo hhi
  have hupper := window_upper_antitone (M := ssfGridLen δ) hδ hδ1 hable hε0 hεe'
  have hrhoN1 : rhoN ≤ 1 := by exact_mod_cast (hhin.trans hupper).trans hwin1
  have hloe : (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ε
      ≤ (rhoN : ℝ) :=
    le_trans (MultiScaleFac.A.clamp_window_lower_mono hδ hδ1 hable hεe') hlon
  obtain ⟨k, hkb, hkM, h2d, h4krho, h4krhoN, hk4rho, hk4rhoN, hsharp⟩ :=
    MultiScaleFac.A.exists_transport_level hδ hδ1 hδlt hδ16 hM hab hbM hεba hrho1 hlo hloe
  have hbrho := MultiScaleFac.A.clamp_gridScale_le_of_window_lower (M := ssfGridLen δ) hδ hδ1 hable
    hε0 hlo
  have hbrhoN := MultiScaleFac.A.clamp_gridScale_le_of_window_lower (M := ssfGridLen δ) hδ hδ1 hable
    he0' hlon
  have hself : ∀ x : NNReal, (x : ℝ) ≤ scaleGapLoss cg δ * (x : ℝ) := fun x =>
    le_mul_of_one_le_left x.coe_nonneg (one_le_scaleGapLoss cg hδ hδ1)
  have hsharpBoth : (rhoN : ℝ) ≤ 32 * scaleGapLoss (cg + 1) δ * (gridScale δ (ssfGridLen δ) k : ℝ)
      ∧ (ρ : ℝ) ≤ 32 * scaleGapLoss (cg + 1) δ * (gridScale δ (ssfGridLen δ) k : ℝ) := by
    rcases le_total (ρ : ℝ) (rhoN : ℝ) with hcase | hcase
    · have hS : (ρ : ℝ) ≤ 32 * scaleGapLoss 1 δ * (gridScale δ (ssfGridLen δ) k : ℝ) := by
        simpa only [NNReal.coe_min, min_eq_left hcase] using hsharp
      exact ⟨MultiScaleFac.A.clamp_sharp_transfer hδ hδ1 hS hclampA,
        MultiScaleFac.A.clamp_sharp_transfer hδ hδ1 hS (hself ρ)⟩
    · have hS : (rhoN : ℝ) ≤ 32 * scaleGapLoss 1 δ * (gridScale δ (ssfGridLen δ) k : ℝ) := by
        simpa only [NNReal.coe_min, min_eq_right hcase] using hsharp
      exact ⟨MultiScaleFac.A.clamp_sharp_transfer hδ hδ1 hS (hself rhoN),
        MultiScaleFac.A.clamp_sharp_transfer hδ hδ1 hS hclampB⟩
  exact ⟨rhoN, k, hlon, hhin, hkb, hkM, h2d, h4krho, h4krhoN, hk4rhoN, hbrho, hbrhoN,
    hrhoN1, hclampA, hclampB, hsharpBoth.1, hsharpBoth.2⟩

open scoped Classical in
/-- **The third bullet on the narrow window implies the third bullet on the `ε`-window.**  The
abstract form of the last step of GWZ Lemma 7.7(A): the hypothesis `hnarrow` is the third bullet of
the terminal alternative stated on the window of the larger exponent `e'`, and the conclusion is
the same statement on the window of exponent `ε`, the two coefficients being added to the loss. -/
theorem A.clamp_bulletThree_window {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδlt : δ < 1)
    (hδ16 : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ))) (hM : 0 < ssfGridLen δ)
    {s : Finset ι} {T : ι → Tube δ E} {Cu : NNReal} [DecidableEq ι]
    (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu) (hCu : 1 ≤ Cu) (hs : s.Nonempty)
    {a b Kn : ℕ} (hab : a < b) (hbM : b ≤ ssfGridLen δ)
    {ε e' : ℝ} (hε0 : 0 ≤ ε) (hεe' : ε ≤ e') (hεba : 3 ≤ ε * ((b : ℝ) - (a : ℝ)))
    {cg : ℕ} (hstep : (e' - ε) * ((b : ℝ) - (a : ℝ)) ≤ (cg : ℝ))
    (hnwne : (gridScale δ (ssfGridLen δ) b : ℝ)
          * ((gridScale δ (ssfGridLen δ) a : ℝ)
              / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e'
        ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
          * ((gridScale δ (ssfGridLen δ) b : ℝ)
              / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e')
    (hwin1 : (gridScale δ (ssfGridLen δ) a : ℝ)
          * ((gridScale δ (ssfGridLen δ) b : ℝ)
              / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ ε ≤ 1)
    {Φ : ℕ → ENNReal} {Cb : NNReal}
    (hP : ∀ k : ℕ, k ≤ b → k < ssfGridLen δ → ∀ p ∈ 𝒰.cover.indexSet k,
      ∃ P ⊆ 𝒰.cover.indexSet k, P.card ≤ Kn ∧
      𝒰.nodesIn b (((𝒰.cover.tube k p).rescale
          (8 * gridScale δ (ssfGridLen δ) k)).toConvexSpaceBody)
        ⊆ P.biUnion (fun q =>
            (coverClass s (𝒰.cover.assign k) q).image (𝒰.cover.assign b)))
    (hbandLo : ∀ k ≤ ssfGridLen δ, ∀ p ∈ 𝒰.cover.indexSet k,
      Φ k ≤ Kakeya.maxDensity ((coverClass s (𝒰.cover.assign k) p).image (𝒰.cover.assign b))
          (fun w => (𝒰.cover.tube b w).toConvexSpaceBody))
    (hbandHi : ∀ k ≤ ssfGridLen δ, ∀ p ∈ 𝒰.cover.indexSet k,
      Kakeya.maxDensity ((coverClass s (𝒰.cover.assign k) p).image (𝒰.cover.assign b))
          (fun w => (𝒰.cover.tube b w).toConvexSpaceBody) ≤ (Cb : ENNReal) * Φ k)
    {ζ' : ℝ} (hζ0 : 0 ≤ ζ') (hζ1 : ζ' ≤ 1)
    {C₀ B C : NNReal} {K₀ K₂ K c₀ c : ℕ} (hC₀ : 1 ≤ C₀) (hB : 1 ≤ B)
    (hBfine : 2 * 25 ^ (2 * Module.finrank ℝ E) * 128 ^ (2 * Module.finrank ℝ E) * Cu
        * (Kn : NNReal) * Cb * scaleGapVolConst (Module.finrank ℝ E) ≤ B)
    (hBcoarse : (Tube.le_volume.c (Module.finrank ℝ E))⁻¹
        * (Tube.volume_le.C (Module.finrank ℝ E)
            * (2 * 25 ^ (2 * Module.finrank ℝ E) * 128 ^ (2 * Module.finrank ℝ E) * Cu ^ 6)) ≤ B)
    (hC : C₀ * B ≤ C) (hK : K₀ + K₂ ≤ K)
    (hc : c₀ + ((cg + 1) * (2 * Module.finrank ℝ E)
        + cg * (Module.finrank ℝ E - 1) + cg) ≤ c)
    (hnarrow : ∀ ρ : NNReal,
      (gridScale δ (ssfGridLen δ) b : ℝ)
          * ((gridScale δ (ssfGridLen δ) a : ℝ)
              / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e' ≤ (ρ : ℝ) →
      (ρ : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
          * ((gridScale δ (ssfGridLen δ) b : ℝ)
              / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e' →
      ∀ j ∈ 𝒰.cover.indexSet b,
        ENNReal.ofReal (((ρ : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ζ')
          ≤ (C₀ : ENNReal) * totalLoss C₀ K₀ c₀ δ *
              ConvexSpaceBody.frostmanConstant
                (𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody)
                (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
                ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody) :
    ∀ ρ : NNReal,
      (gridScale δ (ssfGridLen δ) b : ℝ)
          * ((gridScale δ (ssfGridLen δ) a : ℝ)
              / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ε ≤ (ρ : ℝ) →
      (ρ : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
          * ((gridScale δ (ssfGridLen δ) b : ℝ)
              / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ ε →
      ∀ j ∈ 𝒰.cover.indexSet b,
        ENNReal.ofReal (((ρ : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ζ')
          ≤ (C : ENNReal) * totalLoss C K c δ *
              ConvexSpaceBody.frostmanConstant
                (𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody)
                (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
                ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody := by
  classical
  intro ρ hlo hhi j hj
  obtain ⟨rhoN, k, hlon, hhin, hkb, hkM, h2d, h4kρ, h4kρN, hk4ρN, hbρ, hbρN, hρN1, hclampA,
      hclampB, hsharpN, hsharpRho⟩ :=
    MultiScaleFac.A.clamp_exists_window_data hδ hδ1 hδlt hδ16 hM hab hbM hε0 hεe' hεba hstep hnwne
      hwin1
      hlo hhi
  have hkne : k ≠ ssfGridLen δ := by
    intro hEq
    rw [hEq, gridScale_self δ hM] at h2d
    have h2dR : 2 * (δ : ℝ) ≤ (δ : ℝ) := by exact_mod_cast h2d
    have hdR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
    linarith
  have hkStrict : k < ssfGridLen δ := Nat.lt_of_le_of_ne hkM hkne
  have hbound := hnarrow rhoN hlon hhin j hj
  have hρN4 : rhoN ≤ 4 := le_trans hρN1 (by norm_num)
  rcases le_total ρ rhoN with hle | hge
  · exact MultiScaleFac.A.clamp_bulletThree_fineEnd (cA := cg + 1) (cB := cg)
      (cF := (cg + 1) * (2 * Module.finrank ℝ E) + cg * (Module.finrank ℝ E - 1) + cg)
      (K₂ := K₂) hδ hδ1 𝒰 hs hkb hbM hkM h2d (hP k hkb hkStrict) (hbandLo k hkM)
      (hbandHi k hkM) hj hbρ h4kρ hle hρN4 hk4ρN hsharpN hclampA hζ0 hC₀ hB hBfine
      (Nat.le_add_right _ _) hC hK hc hbound
  · exact MultiScaleFac.A.clamp_bulletThree_coarseEnd (cA := cg + 1) (cB := cg)
      (cF := (cg + 1) * (2 * Module.finrank ℝ E) + cg * (Module.finrank ℝ E - 1) + cg)
      (K₂ := K₂) hδ hδ1 𝒰 hCu hs hkM hbM hkb h2d hj hbρN h4kρN hge hsharpRho hclampB hζ0 hζ1 hC₀ hB
      hBcoarse (by omega) hC hK hc hbound

end MultiScaleFac

end Kakeya

end

/-!
# Merging the constants of the half-(A) third bullet

Every step of the half-(A) third bullet returns its own triple of parameters: a multiplicative
constant, a polylogarithmic degree, and a grid-gap budget.  The statement they must all feed,
`Kakeya.MultiScaleFac.dividingScalesFrostman`, displays a *single* group
`∃ (C δ₀ : NNReal) (K c : ℕ)`, so at assembly time the triples have to be replaced by one common
triple that dominates them all.

This file provides that replacement abstractly, with no numerical input:

* `Kakeya.MultiScaleFac.A.exists_common_const_pair` produces one constant dominating two, which
  is the shape in which the base of the window clamp is obtained.
* `Kakeya.MultiScaleFac.totalLoss_mono` is what makes such a replacement legitimate: the
  displayed loss only grows when its three parameters grow.  Without it, merging the parameters
  would not preserve any of the five bounds in which `Kakeya.MultiScaleFac.totalLoss` occurs.
* `Kakeya.MultiScaleFac.A.exists_clamp_bulletThree_window_const` produces a triple satisfying at
  once the three side conditions `hC`, `hK`, `hc` of
  `Kakeya.MultiScaleFac.A.clamp_bulletThree_window`.  Those three are of different shapes -- one
  multiplicative, two additive, and the last with a truncated subtraction in the ambient dimension
  -- so discharging them together is worth a lemma.

Nothing here depends on the value of any constant of the development: the base `B` dominating the
two absolute constants of the window clamp is an input, obtained from
`Kakeya.MultiScaleFac.A.exists_common_const_pair`.
-/

@[expose] public section
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable {ι : Type u}
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### Merging finitely many parameters -/

/-- **One constant dominating two constants.**  The shape in which the base of the window clamp is
produced: its two side conditions `hBfine` and `hBcoarse` are both of the form
`<explicit constant> ≤ B`. -/
theorem A.exists_common_const_pair (B₀ B₁ : NNReal) :
    ∃ C : NNReal, 1 ≤ C ∧ B₀ ≤ C ∧ B₁ ≤ C :=
  ⟨max 1 (max B₀ B₁), le_max_left _ _, (le_max_left B₀ B₁).trans (le_max_right _ _),
    (le_max_right B₀ B₁).trans (le_max_right _ _)⟩

/-! ### The side conditions of the window clamp -/

/-- **The three side conditions of the window clamp are satisfiable together.**  A triple `C K c`
meeting at once the multiplicative constraint `hC`, the additive constraint `hK` and the grid-gap
budget `hc` of `Kakeya.MultiScaleFac.A.clamp_bulletThree_window`, together with `1 ≤ C` and the
componentwise bounds `C₀ ≤ C`, `K₀ ≤ K`, `c₀ ≤ c` that `totalLoss_mono` consumes. -/
theorem A.exists_clamp_bulletThree_window_const {C₀ B : NNReal} (hC₀ : 1 ≤ C₀) (hB : 1 ≤ B)
    (K₀ K₂ c₀ cg n : ℕ) :
    ∃ (C : NNReal) (K c : ℕ), 1 ≤ C ∧ C₀ ≤ C ∧ B ≤ C ∧ K₀ ≤ K ∧ K₂ ≤ K ∧ c₀ ≤ c ∧
      C₀ * B ≤ C ∧ K₀ + K₂ ≤ K ∧ c₀ + ((cg + 1) * (2 * n) + cg * (n - 1) + cg) ≤ c := by
  set cF := (cg + 1) * (2 * n) + cg * (n - 1) + cg
  exact ⟨C₀ * B, K₀ + K₂, c₀ + cF, one_le_mul_of_one_le_of_one_le hC₀ hB,
    le_mul_of_le_of_one_le le_rfl hB, le_mul_of_one_le_of_le hC₀ le_rfl,
    Nat.le_add_right _ _, Nat.le_add_left _ _, Nat.le_add_right _ _, le_rfl, le_rfl, le_rfl⟩

end MultiScaleFac

end Kakeya

end

/-!
# Spreading one witness across a narrow window scale, half (A)

The terminal alternative of the half-(A) dichotomy speaks at a *single* level-`c` node, at the
reading scale `ρ_c` produced by the sharp window rounding.  This file carries that single lower
bound to the locked form of the third bullet at one scale `ρ` of the narrow window: a lower bound
at *every* level-`b` node, against the concentric `ρ`-rescale of that node, with a coefficient that
is one displayed `Kakeya.MultiScaleFac.totalLoss`.

Three steps, in this order.

* **Spreading.**  `Kakeya.MultiScaleFac.A.hgrid_of_witness` removes the majority set and moves the
  witness onto every level-`c` node, through the two-sided band.  The band is read off the
  `Kakeya.MultiScaleFac.PairBandOn` predicate carried by the banded stopping time at the pair of
  levels `(c, b)`; the transfer is free, the cover system of
  `Kakeya.MultiScaleFac.GridUniform.toUniformTubeSet` being definitionally the one of the
  grid-uniform system.  The price is the four coefficients `K_n`, `d_m`, `C_b = 2`, `D_m`.

* **Descent.**  `Kakeya.MultiScaleFac.le_frostmanConstant_nodesIn_rescale_of_grid_dilate` descends
  from the reading level `c` to the real scale `ρ`, which is admissible because the sharp rounding
  guarantees `32 ρ_c ≤ ρ`.  Its packing count is bounded by
  `Kakeya.MultiScaleFac.A.narrowLambdaConst` times a single
  `Kakeya.MultiScaleFac.scaleGapLoss (2n) δ`, again by sharpness, which is the content of
  `Kakeya.MultiScaleFac.A.lambda_le_scaleGapLoss`.  The price is the two volume constants of the
  rounding and that packing factor.

* **Accounting.**  `Kakeya.MultiScaleFac.A.narrow_coefficient_le` cancels the two node densities
  against their absolute ratio `R` and absorbs everything that is left -- absolute constants
  against the two gap losses, the packing count's `2n` and the witness budget `c₂` -- into the
  single displayed loss, as soon as `2n + c₂ ≤ c`.
-/

@[expose] public section

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable {ι : Type u}
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The packing factor of the sharply rounded descent -/

/-- **Constant in Lemma `A.narrow_descent`.**  The absolute part of the packing count of the
ancestor split at a sharply rounded reading level: the dimensional factor `2 · 25^{2n}` of the
split, the factor `128^{2n}` left by the sharpness of the rounding, and the sixth power of the
uniformity constant.  It depends on the ambient dimension and on `C_u` alone. -/
noncomputable def A.narrowLambdaConst (n : ℕ) (Cu : NNReal) : NNReal :=
  2 * 25 ^ (2 * n) * 128 ^ (2 * n) * Cu ^ 6

/-- The real value of `Kakeya.MultiScaleFac.A.narrowLambdaConst`. -/
private theorem A.narrowLambdaConst_coe (n : ℕ) (Cu : NNReal) :
    ((MultiScaleFac.A.narrowLambdaConst n Cu : NNReal) : ℝ)
      = 2 * (25 : ℝ) ^ (2 * n) * (128 : ℝ) ^ (2 * n) * ((Cu : ℝ) ^ 6) := by
  unfold MultiScaleFac.A.narrowLambdaConst
  push_cast
  ring

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The packing count of the sharply rounded descent, in the shape the rounding consumes.**
Verbatim the hypothesis `hΛ` of
`Kakeya.MultiScaleFac.le_frostmanConstant_nodesIn_rescale_of_grid_dilate` at the packing factor
`Λ = C · scaleGapLoss (2n) δ`, with `C` the absolute `Kakeya.MultiScaleFac.A.narrowLambdaConst`. -/
private theorem A.narrowLambda_spec {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {c : ℕ} {ρ : NNReal}
    (hsharp : (ρ : ℝ) ≤ 32 * scaleGapLoss 1 δ * (gridScale δ (ssfGridLen δ) c : ℝ))
    (Cu : NNReal) :
    2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
        * (((4 * ρ : NNReal) : ℝ) / (gridScale δ (ssfGridLen δ) c : ℝ))
            ^ (2 * Module.finrank ℝ E)
        * (Cu : ℝ) * ((Cu : ℝ) ^ 5)
      ≤ ((MultiScaleFac.A.narrowLambdaConst (Module.finrank ℝ E) Cu
            * Real.toNNReal (scaleGapLoss (2 * Module.finrank ℝ E) δ) : NNReal) : ℝ) := by
  have hnn : (0 : ℝ) ≤ scaleGapLoss (2 * Module.finrank ℝ E) δ :=
    zero_le_one.trans (one_le_scaleGapLoss (2 * Module.finrank ℝ E) hδ hδ1)
  rw [NNReal.coe_mul (MultiScaleFac.A.narrowLambdaConst (Module.finrank ℝ E) Cu),
    MultiScaleFac.A.narrowLambdaConst_coe, Real.coe_toNNReal _ hnn]
  exact MultiScaleFac.A.lambda_le_scaleGapLoss hδ hδ1 hsharp Cu (Module.finrank ℝ E)

/-! ### The band, in the shape the spreading lemma consumes -/

omit [Nontrivial E] in
open scoped Classical in
/-- **The paired band at one pair of levels, unbundled.**  `Kakeya.MultiScaleFac.PairBandOn` read at
the single pair of levels `(c, b)` and on the induced uniform set of tubes.  Nothing happens beyond
fixing the pair: the cover system of `Kakeya.MultiScaleFac.GridUniform.toUniformTubeSet` is
definitionally the one of the grid-uniform system. -/
theorem A.band_of_pairBandOn {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E}
    {Mgrid : ℕ} {Cv : NNReal} (𝒢 : GridUniform t T Mgrid Cv)
    {Φ : ℕ → ℕ → ENNReal} (hband : PairBandOn t 𝒢 2 Φ Mgrid)
    {c b : ℕ} (hc : c ≤ Mgrid) (hb : b ≤ Mgrid) :
    ∀ p ∈ 𝒢.toUniformTubeSet.cover.indexSet c,
      Φ c b ≤ Kakeya.maxDensity
            ((coverClass t (𝒢.toUniformTubeSet.cover.assign c) p).image
              (𝒢.toUniformTubeSet.cover.assign b))
            (fun j' => (𝒢.toUniformTubeSet.cover.tube b j').toConvexSpaceBody) ∧
        Kakeya.maxDensity
            ((coverClass t (𝒢.toUniformTubeSet.cover.assign c) p).image
              (𝒢.toUniformTubeSet.cover.assign b))
            (fun j' => (𝒢.toUniformTubeSet.cover.tube b j').toConvexSpaceBody)
          ≤ ((2 : NNReal) : ENNReal) * Φ c b := by
  intro p hp
  simpa [GridUniform.toUniformTubeSet_cover] using hband c hc b hb p
    (by simpa [GridUniform.toUniformTubeSet_cover] using hp)

/-! ### The descent from the reading level to the window scale -/

open scoped Classical in
/-- **The grid rounding at a sharply rounded reading level.**
`Kakeya.MultiScaleFac.le_frostmanConstant_nodesIn_rescale_of_grid_dilate` with its packing factor
already chosen: the sharpness of the rounding pins `Λ` to the absolute
`Kakeya.MultiScaleFac.A.narrowLambdaConst` times one `Kakeya.MultiScaleFac.scaleGapLoss (2n) δ`. -/
theorem A.narrow_descent {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {Cu : NNReal}
    (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu) (hCu : 1 ≤ Cu) (hs : s.Nonempty)
    {c b : ℕ} (hcM : c ≤ ssfGridLen δ) (hbM : b ≤ ssfGridLen δ) (hcb : c ≤ b)
    (h2d : 2 * δ ≤ gridScale δ (ssfGridLen δ) c)
    {ρ : NNReal} (h32 : 32 * gridScale δ (ssfGridLen δ) c ≤ ρ)
    (hsharp : (ρ : ℝ) ≤ 32 * scaleGapLoss 1 δ * (gridScale δ (ssfGridLen δ) c : ℝ))
    {X Dg : ENNReal}
    (hgrid : ∀ p ∈ 𝒰.cover.indexSet c, X ≤ Dg * ConvexSpaceBody.frostmanConstant
        (𝒰.nodesIn b (((𝒰.cover.tube c p).rescale
            (8 * gridScale δ (ssfGridLen δ) c)).toConvexSpaceBody))
        (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
        (((𝒰.cover.tube c p).rescale
            (8 * gridScale δ (ssfGridLen δ) c)).toConvexSpaceBody))
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet b) :
    X ≤ (((Tube.le_volume.c (Module.finrank ℝ E))⁻¹ : NNReal) : ENNReal)
        * (Dg * ((Tube.volume_le.C (Module.finrank ℝ E)
              * (MultiScaleFac.A.narrowLambdaConst (Module.finrank ℝ E) Cu
                  * Real.toNNReal (scaleGapLoss (2 * Module.finrank ℝ E) δ)) : NNReal) : ENNReal)
          * ConvexSpaceBody.frostmanConstant
              (𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody)
              (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
              ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody) :=
  le_frostmanConstant_nodesIn_rescale_of_grid_dilate hδ hδ1 𝒰 hCu hs hcM hbM hcb
    h2d h32 (MultiScaleFac.A.narrowLambda_spec hδ hδ1 hsharp Cu) hgrid hj

/-! ### The accounting of the whole coefficient -/

/-- **The coefficient produced by the spreading and the descent is one displayed loss.**  The chain
leaves the product `V₁ · (D · K_n / d_m · 2 · D_m · (V₂ · Λ))` in front of the Frostman constant;
the two node densities cancel through their absolute ratio `R`, the two gap losses add their
budgets, and what is left is a product of absolute constants. -/
theorem A.narrow_absorb {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {Kn : ℕ} {R V₁ V₂ Lam A B : NNReal} (hB1 : 1 ≤ B)
    (hBle : (Kn : NNReal) * (2 * A) * R * V₁ * V₂ * Lam ≤ B)
    {c₁ c₂ K cL : ℕ} (hcL : c₁ + c₂ ≤ cL)
    {X Y D dm Dm : ENNReal} (hdm0 : dm ≠ 0) (hdmtop : dm ≠ ⊤)
    (hDm : Dm ≤ (R : ENNReal) * dm)
    (hD : D ≤ (A : ENNReal) * ENNReal.ofReal (scaleGapLoss c₂ δ))
    (h : X ≤ (V₁ : ENNReal)
        * (D * (Kn : ENNReal) / dm * ((2 : NNReal) : ENNReal) * Dm
            * ((V₂ * (Lam * Real.toNNReal (scaleGapLoss c₁ δ)) : NNReal) : ENNReal) * Y)) :
    X ≤ (B : ENNReal) * totalLoss B K cL δ * Y := by
  have hcoe : ((V₂ * (Lam * Real.toNNReal (scaleGapLoss c₁ δ)) : NNReal) : ENNReal)
      = (V₂ : ENNReal) * ((Lam : ENNReal) * ENNReal.ofReal (scaleGapLoss c₁ δ)) := by
    rw [ENNReal.coe_mul, ENNReal.coe_mul]
    rfl
  have hcoe2 : (((2 * A : NNReal) : NNReal) : ENNReal) =
      ((2 : NNReal) : ENNReal) * (A : ENNReal) := by
    rw [ENNReal.coe_mul]
  have hmono : X ≤ (V₁ : ENNReal)
      * (((A : ENNReal) * ENNReal.ofReal (scaleGapLoss c₂ δ)) * (Kn : ENNReal) / dm
          * ((2 : NNReal) : ENNReal) * Dm
          * ((V₂ * (Lam * Real.toNNReal (scaleGapLoss c₁ δ)) : NNReal) : ENNReal) * Y) := by
    refine h.trans ?_
    gcongr
  have hshape : X ≤ 1 * (Kn : ENNReal) / dm * ((2 * A : NNReal) : ENNReal) * Dm
      * (V₁ : ENNReal) * (V₂ : ENNReal)
      * ((Lam : ENNReal) * ENNReal.ofReal (scaleGapLoss c₁ δ))
      * ENNReal.ofReal (scaleGapLoss c₂ δ) * Y := by
    refine hmono.trans_eq ?_
    rw [hcoe, hcoe2]
    simp only [div_eq_mul_inv, one_mul]
    ring
  simpa only [one_mul] using
    MultiScaleFac.A.narrow_coefficient_le hδ hδ1 hB1 hBle hcL hdm0 hdmtop hDm hshape

/-! ### The third bullet at one scale of the narrow window -/

end MultiScaleFac

end Kakeya

end

/-!
# The witness half of the third bullet of half (A), sharpened

`Kakeya.MultiScaleFac.A.narrow_witness_package` is the witness half of the third bullet of
half (A).  It is the package of `Kakeya.StickyKakeya.ssfA_narrow_witness_package` with the two scale
clauses of the sharp rounding kept in the conclusion.  The package itself exports only
`2 δ ≤ σ_c`, but the spreading half also consumes `32 σ_c ≤ ρ` and the sharpness `ρ ≤ 32 Λ₁ σ_c`
*at the same level `c`*, and the level is existentially bound, so those two clauses cannot be
recovered from the package after the fact.  They are not extra hypotheses of the narrow window
either: they come from the very call to `Kakeya.MultiScaleFac.A.exists_round_index_sharp` that
produces the level, so the sharpened package simply keeps them.

The sharpened witness is run into `Kakeya.StickyKakeya.ssfA_narrow_spread_package` on the banded
route, in `Kakeya.MultiScaleFac.A.bandedA_narrow_window`.
-/

@[expose] public section

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable {ι : Type u}
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The witness package with the two scale clauses kept -/

/-- **The narrow-window witness package of half (A), with the sharp scale clauses.**  Identical to
`Kakeya.StickyKakeya.ssfA_narrow_witness_package` except that the conclusion also carries the two
clauses `32 σ_c ≤ ρ` and `ρ ≤ 32 Λ₁ σ_c` of `Kakeya.MultiScaleFac.A.exists_round_index_sharp` at
the level `c` it produces, both of which the spreading step demands at that same level. -/
theorem A.narrow_witness_package {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδlt : δ < 1)
    (hδ16 : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ))) (hM : 0 < ssfGridLen δ)
    {s : Finset ι} {T : ι → Tube δ E} {Cv : NNReal} (hCv : 1 ≤ Cv) (hs : s.Nonempty)
    (𝒢 : GridUniform s T (ssfGridLen δ) Cv)
    {zeta : ℝ} (hz0 : 0 ≤ zeta) (hz1 : zeta ≤ 1)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ ssfGridLen δ)
    {e e' : ℝ} (he : 0 ≤ e) (hee' : e ≤ e')
    (hk : (6 : ℝ) ≤ (e' - e) * ((b : ℝ) - (a : ℝ)))
    {rho : NNReal}
    (hlo : (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e' ≤ (rho : ℝ))
    (hhi : (rho : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
        * ((gridScale δ (ssfGridLen δ) b : ℝ)
            / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e')
    {G : Finset ι} {j : ι} (hj : j ∈ goodNodes 𝒢.toUniformTubeSet b G)
    {D0 : ENNReal}
    (hAlt : ∀ i ∈ G, ∀ r : NNReal,
      (gridScale δ (ssfGridLen δ) b : ℝ)
          * ((gridScale δ (ssfGridLen δ) a : ℝ)
              / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e ≤ (r : ℝ) →
      (r : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
          * ((gridScale δ (ssfGridLen δ) b : ℝ)
              / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e →
      ENNReal.ofReal (((r : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ zeta)
        ≤ D0 * ConvexSpaceBody.frostmanConstant (fibreIndex s T δ r i)
            (fibreBodies T (gridScale δ (ssfGridLen δ) b))
            ((T i).rescale (2 * r)).toConvexSpaceBody) :
    ∃ c : ℕ, c ≤ b ∧ c ≤ ssfGridLen δ ∧ 2 * δ ≤ gridScale δ (ssfGridLen δ) c ∧
      32 * gridScale δ (ssfGridLen δ) c ≤ rho ∧
      (rho : ℝ) ≤ 32 * scaleGapLoss 1 δ * (gridScale δ (ssfGridLen δ) c : ℝ) ∧
      ∃ j' ∈ 𝒢.toUniformTubeSet.cover.indexSet c,
        ENNReal.ofReal (((rho : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ zeta)
          ≤ ENNReal.ofReal (32 * scaleGapLoss 1 δ)
              * (D0 * ((fibreFromNodeConst (E := E) : ENNReal)
                  * ((uniformTubeSetCuOf (E := E) Cv : NNReal) : ENNReal) ^ 5))
              * ConvexSpaceBody.frostmanConstant
                  (𝒢.toUniformTubeSet.nodesIn b ((𝒢.toUniformTubeSet.cover.tube c j').rescale
                      (8 * gridScale δ (ssfGridLen δ) c)).toConvexSpaceBody)
                  (fun w => (𝒢.toUniformTubeSet.cover.tube b w).toConvexSpaceBody)
                  ((𝒢.toUniformTubeSet.cover.tube c j').rescale
                      (8 * gridScale δ (ssfGridLen δ) c)).toConvexSpaceBody := by
  have hrho1 : rho ≤ 1 := MultiScaleFac.A.window_scale_le_one hδ hδ1 hab (he.trans hee') hhi
  have hablt : a < b := MultiScaleFac.A.lt_of_six_le_window_gap hee' hk
  have hthree : (3 : ℝ) ≤ e' * ((b : ℝ) - (a : ℝ)) :=
    MultiScaleFac.A.three_le_window_exp_mul he hab hk
  obtain ⟨c, hcb, hc, h2d, hcspec, hsharp⟩ :=
    MultiScaleFac.A.exists_round_index_sharp hδ hδ1 hδlt hδ16 hM hablt hb hthree hrho1 hlo
  have hdltR : (δ : ℝ) < 1 := by exact_mod_cast hδlt
  refine ⟨c, hcb, hc, h2d, hcspec, hsharp, ?_⟩
  exact MultiScaleFac.A.narrow_witness_hX_at_index hδ hδ1 hdltR hM hCv hs 𝒢 hz0 hz1 hab hb hc hcb
    h2d
    he hee' (k := 6) (by exact_mod_cast hk)
    (MultiScaleFac.A.one_le_thirtyTwo_mul_scaleGapLoss_one hδ hδ1)
    (MultiScaleFac.A.thirtyTwo_mul_scaleGapLoss_one_le hδ hδ16 hM)
    hlo hhi (MultiScaleFac.A.gridScale_le_of_thirtyTwo_mul_le hcspec) hsharp hj hAlt

end MultiScaleFac

end Kakeya

end

/-!
# Adapting the terminal alternative (ii) to the narrow-window witness package

`Kakeya.StickyKakeya.ssf_bulletThree_of_alternativeTwo` carries the terminal alternative (ii) in its
hypothesis list, in the shape the stopping time delivers it: one universally quantified real scale
`ρ` of a window, then a leaf `i₀` of a majority set `F ⊆ s`.  The entry point of the new chain,
`Kakeya.StickyKakeya.ssfA_narrow_witness_package`, asks for the same supply in the opposite
quantifier order — leaf first, scale second — on a set `G` that is the one indexing
`Kakeya.MultiScaleFac.goodNodes`, and with the whole coefficient collapsed into a single `D0`.

This file is the translation between the two, and nothing more.  It is deliberately confined to the
*supply* half of the correspondence: the new chain also demands a
`Kakeya.MultiScaleFac.GridUniform` and a second window exponent, neither of which the old hypothesis
list mentions, and those are hypotheses of the composed statement below rather than things derived
here.

Three points of the dictionary are worth recording.

* The window endpoints need no translation.  Both sides write the window of exponent `e` as
  `σ_b (σ_a/σ_b)^e ≤ r ≤ σ_a (σ_b/σ_a)^e`, character for character, so the identification is the
  substitution `e := (1 + 2N/M) ε` and no endpoint-equivalence lemma is needed.  Since
  `gridScale δ M k = δ^{k/M}` and `δ < 1`, one has `σ_a/σ_b > 1` for `a < b`, and the window of
  exponent `e` is `[σ_b R^e, σ_b R^{1-e}]` with `R = σ_a/σ_b`; it *shrinks* as `e` grows.

* The exponent `ζ'` of the alternative is the `zeta` of the package.  The package wants
  `0 ≤ zeta` and `zeta ≤ 1`, which the old hypothesis list gives only indirectly, through
  `0 ≤ ζ`, `ζ ≤ ε ζ'`, `ζ' ≤ ε` and `ε ≤ 1/64`; that derivation is
  `Kakeya.MultiScaleFac.A.Alt.zeta_nonneg_of_mul_le` and
  `Kakeya.MultiScaleFac.A.Alt.zeta_le_one_of_le`.

* The majority set `F` of the old list and the set `G` indexing the good nodes of the package are
  the same set.  The old list's `F ⊆ s` and `s.card ≤ 2 * F.card` are exactly the hypotheses of
  `Kakeya.MultiScaleFac.card_parent_le_mul_card_goodNodes`, which is what makes
  `goodNodes 𝒰 b F` a fixed proportion of the level; they are not needed to convert the supply
  itself, and so do not appear below.
-/

@[expose] public section

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable {ι : Type u}
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The exponent conditions, from the old hypothesis list -/

/-- **Nonnegativity of the outer exponent.**

The old hypothesis list bounds the inner exponent by `ζ ≤ ε ζ'` and asks `0 ≤ ζ`; with `ε` positive
this forces `0 ≤ ζ'`, which is what the package asks of its `zeta`. -/
theorem A.Alt.zeta_nonneg_of_mul_le {eps zeta zeta' : ℝ} (heps : 0 < eps)
    (hzeta : 0 ≤ zeta) (hle : zeta ≤ eps * zeta') : 0 ≤ zeta' :=
  le_of_mul_le_mul_left (by linarith) heps

/-- **The outer exponent is at most one.**

`ζ' ≤ ε ≤ 1/64 ≤ 1`. -/
theorem A.Alt.zeta_le_one_of_le {eps zeta' : ℝ} (heps : eps ≤ 1 / 64) (hle : zeta' ≤ eps) :
    zeta' ≤ 1 := by linarith

/-- **Nonnegativity of the supply-window exponent.**

The window the alternative speaks on has exponent `(1 + 2N/M) ε`, and the package asks its supply
exponent to be nonnegative. -/
theorem A.Alt.supplyExp_nonneg (N M : ℕ) {eps : ℝ} (heps : 0 ≤ eps) :
    0 ≤ (1 + 2 * ((N : ℝ) / (M : ℝ))) * eps := by
  exact mul_nonneg (by positivity) heps

/-! ### The supply, reordered -/

omit [Nontrivial E] in
/-- **The alternative (ii) supply of the old hypothesis list, as the `hAlt` of the package.**  The
alternative (ii) clause of `Kakeya.StickyKakeya.ssf_bulletThree_of_alternativeTwo`, restated as the
`hAlt` hypothesis of `Kakeya.StickyKakeya.ssfA_narrow_witness_package` at supply exponent
`e := (1 + 2N/M) ε`, at `zeta := ζ'`, at `G := F` and at `D0 := C₂ * ofReal (δ^{-27/M})`. -/
theorem A.Alt.hAlt_of_alternativeTwo {delta : NNReal} {s : Finset ι} {T : ι → Tube delta E}
    (N : ℕ) (C2 : NNReal) {eps zeta' : ℝ} {a b : ℕ} {F : Finset ι}
    (halt : ∀ r : NNReal,
      (gridScale delta (ssfGridLen delta) b : ℝ)
          * ((gridScale delta (ssfGridLen delta) a : ℝ)
              / (gridScale delta (ssfGridLen delta) b : ℝ))
            ^ ((1 + 2 * ((N : ℝ) / (ssfGridLen delta : ℝ))) * eps) ≤ (r : ℝ) →
      (r : ℝ) ≤ (gridScale delta (ssfGridLen delta) a : ℝ)
          * ((gridScale delta (ssfGridLen delta) b : ℝ)
              / (gridScale delta (ssfGridLen delta) a : ℝ))
            ^ ((1 + 2 * ((N : ℝ) / (ssfGridLen delta : ℝ))) * eps) →
      ∀ i0 ∈ F,
        ENNReal.ofReal (((r : ℝ) / (gridScale delta (ssfGridLen delta) b : ℝ)) ^ zeta')
          ≤ (C2 : ENNReal)
              * ENNReal.ofReal ((delta : ℝ) ^ (-(27 / (ssfGridLen delta : ℝ)))) *
              ConvexSpaceBody.frostmanConstant (fibreIndex s T delta r i0)
                (fibreBodies T (gridScale delta (ssfGridLen delta) b))
                ((T i0).rescale (2 * r)).toConvexSpaceBody) :
    ∀ i ∈ F, ∀ r : NNReal,
      (gridScale delta (ssfGridLen delta) b : ℝ)
          * ((gridScale delta (ssfGridLen delta) a : ℝ)
              / (gridScale delta (ssfGridLen delta) b : ℝ))
            ^ ((1 + 2 * ((N : ℝ) / (ssfGridLen delta : ℝ))) * eps) ≤ (r : ℝ) →
      (r : ℝ) ≤ (gridScale delta (ssfGridLen delta) a : ℝ)
          * ((gridScale delta (ssfGridLen delta) b : ℝ)
              / (gridScale delta (ssfGridLen delta) a : ℝ))
            ^ ((1 + 2 * ((N : ℝ) / (ssfGridLen delta : ℝ))) * eps) →
      ENNReal.ofReal (((r : ℝ) / (gridScale delta (ssfGridLen delta) b : ℝ)) ^ zeta')
        ≤ ((C2 : ENNReal)
              * ENNReal.ofReal ((delta : ℝ) ^ (-(27 / (ssfGridLen delta : ℝ)))))
            * ConvexSpaceBody.frostmanConstant (fibreIndex s T delta r i)
                (fibreBodies T (gridScale delta (ssfGridLen delta) b))
                ((T i).rescale (2 * r)).toConvexSpaceBody :=
  fun i hi r hlo hhi => halt r hlo hhi i hi

end MultiScaleFac

end Kakeya

end

/-!
# The inputs of the half-(A) window clamp

`Kakeya.MultiScaleFac.A.clamp_bulletThree_window` transports the third bullet from the wide
window of exponent `e'` to the narrow window of exponent `ε`.  Besides its terminal hypothesis
`hnarrow`, it asks for a window-arithmetic package (`hnwne`, `hstep`, `hwin1`) and for a
cover-and-band package read at a grid level (`hP`, `hbandLo`, `hbandHi`).  This file produces those
packages from the output of the banded stopping time
`Kakeya.MultiScaleFac.exists_maximal_cuts_banded_hoisted_selfBand` and from the long-block
condition.

The one point of adaptation is the arity of the band.  The stopping time carries
`Kakeya.MultiScaleFac.PairBandOn`, whose band `Φ : ℕ → ℕ → ENNReal` is indexed by a *pair* of grid
levels, while the clamp reads a band indexed by the coarse level alone.  Fixing the fine level `b`
resolves this: `Kakeya.MultiScaleFac.A.clampBandFun` is the unary band `k ↦ Φ k b`, and both
halves of `PairBandOn` specialise to it verbatim at `Cb = 2`.

The cover-and-band clauses are available only on part of the grid, and the clamp asks for them
exactly there.  `Kakeya.MultiScaleFac.PairBandOn` speaks at `k ≤ M`, while the coarse-neighbour
cover `Kakeya.MultiScaleFac.exists_coarseNeighbours` stops at `k < M`: the level `k = M` has
`gridScale δ M M = δ`, so the side condition `2δ ≤ σ_k` of the ancestor count fails there.  Above
the grid length nothing at all is known: no field of `Tube.GridCoverSystem`
constrains `indexSet k`, `assign k` or `tube k` for `k > M`, and the two-sided band admits no
padding there, since a band value of `0` breaks the upper bound and a band value of `⊤` breaks the
lower one.  The lemmas below are therefore stated on the ranges where they are true: `k ≤ M` for
the band, and `k ≤ b` together with `k < M` for the cover.  These are verbatim the binders of
`hbandLo`, `hbandHi` and `hP` in `Kakeya.MultiScaleFac.A.clamp_bulletThree_window`, so each
clause below can be handed to the clamp as it stands.  The transport level the clamp selects always
satisfies `2δ ≤ σ_k`, which already forces `k < M`, so nothing is lost by the restriction.

The handover itself is performed on the banded route, in
`Kakeya.MultiScaleFac.bulletThree_of_alternativeTwo_banded`.
-/

@[expose] public section

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable {ι : Type u} [DecidableEq ι]
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The grid levels at which an ancestor count is available -/

/-- **Every level strictly above the fine end of the grid is `2δ`-coarse.**

Consecutive grid scales are `16`-separated once `δ ≤ 16^{-M}`, and the fine end of the grid is the
leaf scale `δ`, so a level `k < M` has `16 δ ≤ σ_k`.  This is the side condition under which the
node-ancestor count, and with it the coarse-neighbour cover, is available. -/
theorem A.clamp_two_delta_le_gridScale {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hδ16 : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ))) (hM : 0 < ssfGridLen δ)
    {k : ℕ} (hk : k < ssfGridLen δ) :
    2 * δ ≤ gridScale δ (ssfGridLen δ) k := by
  have h16 : 16 * gridScale δ (ssfGridLen δ) (ssfGridLen δ) ≤ gridScale δ (ssfGridLen δ) k :=
    sixteen_mul_gridScale_le (N := ssfGridLen δ) (a := k) (b := ssfGridLen δ) hδ hδ1 hδ16 hk
      (le_rfl : ssfGridLen δ ≤ ssfGridLen δ)
  rw [gridScale_self δ hM] at h16
  exact le_trans (mul_le_mul_of_nonneg_right (by norm_num : (2 : NNReal) ≤ 16) hδ.le) h16

/-! ### The window arithmetic -/

/-- **The upper endpoint of the `ε`-window is at most one.**

The hypothesis `hwin1` of `Kakeya.MultiScaleFac.A.clamp_bulletThree_window`.  The endpoint is
`σ_a (σ_b/σ_a)^ε` with `σ_b ≤ σ_a ≤ 1`, so the displayed power is at most `1` and the endpoint is at
most `σ_a`. -/
private theorem A.clamp_window_upper_le_one {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {M a b : ℕ}
    (hab : a ≤ b) {ε : ℝ} (hε : 0 ≤ ε) :
    (gridScale δ M a : ℝ) * ((gridScale δ M b : ℝ) / (gridScale δ M a : ℝ)) ^ ε ≤ 1 := by
  have hga_pos : (0 : ℝ) < (gridScale δ M a : ℝ) := by exact_mod_cast gridScale_pos hδ M a
  have hbase : (gridScale δ M b : ℝ) / (gridScale δ M a : ℝ) ≤ 1 :=
    div_le_one_of_le₀ (by exact_mod_cast gridScale_antitone hδ hδ1 M hab) hga_pos.le
  have h := mul_le_mul_of_nonneg_left
    (Real.rpow_le_one (by positivity) hbase hε) hga_pos.le
  rw [mul_one] at h
  exact h.trans (by exact_mod_cast gridScale_le_one hδ1 M a)

/-- **The narrow window is nonempty on a long block.**

The hypothesis `hnwne` of `Kakeya.MultiScaleFac.A.clamp_bulletThree_window`, obtained from
`Kakeya.MultiScaleFac.A.narrow_window_nonempty` by reading the smallness of `δ` in `ℝ`. -/
private theorem A.clamp_narrow_window_nonempty {δ : NNReal} (hδ : 0 < δ) (hδlt : δ < 1)
    (hM : 0 < ssfGridLen δ) {ε : ℝ} {a b : ℕ}
    (hlong : IsLongBlock (ssfGridLen δ) ε a b) {e' : ℝ} (he' : 2 * e' ≤ 1) :
    (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e'
      ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
        * ((gridScale δ (ssfGridLen δ) b : ℝ)
            / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e' :=
  MultiScaleFac.A.narrow_window_nonempty hδ (by exact_mod_cast hδlt) hM hlong he'

/-! ### The band, read at a fixed fine level -/

/-- The unary band obtained from a paired band by fixing its fine level.  The clamp indexes its
band by the coarse level alone, while `Kakeya.MultiScaleFac.PairBandOn` indexes it by both levels of
the pair it brackets. -/
def A.clampBandFun (Φ : ℕ → ℕ → ENNReal) (b : ℕ) : ℕ → ENNReal := fun k => Φ k b

omit [Nontrivial E] in
/-- **The lower half of the paired band, at a fixed fine level.**

The hypothesis `hbandLo` of `Kakeya.MultiScaleFac.A.clamp_bulletThree_window`, on the range
`k ≤ M` where `Kakeya.MultiScaleFac.PairBandOn` speaks. -/
theorem A.clamp_band_lower {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E} {Cv : NNReal}
    (𝒢 : GridUniform t T (ssfGridLen δ) Cv) {Φ : ℕ → ℕ → ENNReal}
    (hband : PairBandOn t 𝒢 2 Φ (ssfGridLen δ)) {b : ℕ} (hb : b ≤ ssfGridLen δ) :
    ∀ k ≤ ssfGridLen δ, ∀ p ∈ 𝒢.toUniformTubeSet.cover.indexSet k,
      MultiScaleFac.A.clampBandFun Φ b k ≤ Kakeya.maxDensity
        ((coverClass t (𝒢.toUniformTubeSet.cover.assign k) p).image
          (𝒢.toUniformTubeSet.cover.assign b))
        (fun w => (𝒢.toUniformTubeSet.cover.tube b w).toConvexSpaceBody) := by
  intro k hk p hp
  convert (MultiScaleFac.A.band_of_pairBandOn 𝒢 hband hk hb p hp).1 using 2 <;>
    [rfl; (ext; simp [Finset.mem_image])]

omit [Nontrivial E] in
/-- **The upper half of the paired band, at a fixed fine level.**

The hypothesis `hbandHi` of `Kakeya.MultiScaleFac.A.clamp_bulletThree_window` at `Cb = 2`, on the
range `k ≤ M` where `Kakeya.MultiScaleFac.PairBandOn` speaks. -/
theorem A.clamp_band_upper {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E} {Cv : NNReal}
    (𝒢 : GridUniform t T (ssfGridLen δ) Cv) {Φ : ℕ → ℕ → ENNReal}
    (hband : PairBandOn t 𝒢 2 Φ (ssfGridLen δ)) {b : ℕ} (hb : b ≤ ssfGridLen δ) :
    ∀ k ≤ ssfGridLen δ, ∀ p ∈ 𝒢.toUniformTubeSet.cover.indexSet k,
      Kakeya.maxDensity
        ((coverClass t (𝒢.toUniformTubeSet.cover.assign k) p).image
          (𝒢.toUniformTubeSet.cover.assign b))
        (fun w => (𝒢.toUniformTubeSet.cover.tube b w).toConvexSpaceBody)
      ≤ ((2 : NNReal) : ENNReal) * MultiScaleFac.A.clampBandFun Φ b k := by
  intro k hk p hp
  convert (MultiScaleFac.A.band_of_pairBandOn 𝒢 hband hk hb p hp).2 using 2 <;>
    [(ext; simp); rfl]

end MultiScaleFac

end Kakeya

end

/-!
# The window arithmetic at the instance of the amended dichotomy, half (A)

`Kakeya.MultiScaleFac.A.clamp_bulletThree_window` and
`Kakeya.StickyKakeya.ssfA_narrow_witness_package` are stated for abstract window exponents.  This
file discharges their arithmetic hypotheses at the exponents the amended dichotomy
`Kakeya.MultiScaleFac.dividingScalesFrostman` actually runs at:

* `ε = 1/√N`, the window exponent the statement pins;
* `κ = N/M` with `M = ssfGridLen δ`, the ratio of the stopping-time budget to the grid length;
* `e = (1 + 2κ)ε`, the exponent at which the terminal alternative supplies its witness;
* `e' = e + 6/(b - a)`, the exponent of the *narrow* window on which
  `Kakeya.StickyKakeya.ssfA_narrow_witness_package` reads that witness.

Windows narrow as the exponent grows, so the three exponents sit in the order `ε ≤ e ≤ e'` and the
transport runs from the narrow end back to the wide one: alternative (ii) supplies the bullet at
`e`, the witness package converts it to the narrow window at `e'`, and
`Kakeya.MultiScaleFac.A.clamp_bulletThree_window` pushes that narrow conclusion back out to the
`ε`-window.

Two of the hypotheses the clamp asks for are already available in the development and are not
restated here: `hwin1` is `Kakeya.MultiScaleFac.A.clamp_window_upper_le_one` and `hεba` is
`Kakeya.MultiScaleFac.A.three_le_eps_mul_block`.  The `ℝ`-to-`ℕ` conversion of the gap budget is
`Kakeya.MultiScaleFac.A.le_cast_ceil`.

The one parameter bound that is not free is the block length: every statement below reads it
through `3 ≤ ε (b - a)`, which on a long block with `3N ≤ M` and `ε = 1/√N` is
`Kakeya.MultiScaleFac.A.three_le_eps_mul_block`, and which at `ε ≤ 1/64` forces `b - a ≥ 192`.
That is what makes the residual term `6/(b - a)` of `e'` small enough for `2e' ≤ 1`.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable {ι : Type u} [DecidableEq ι]
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The block length -/

/-- **A block carrying three window steps has positive length.**

Every statement of this file reads the block length through `3 ≤ ε (b - a)`; since `ε > 0` this
already forces `b - a > 0`, which is what makes the residual `6/(b - a)` of the narrow exponent
meaningful. -/
private theorem A.inst_block_len_pos {eps : ℝ} (hepspos : 0 < eps) {a b : ℕ}
    (hepsba : 3 ≤ eps * ((b : ℝ) - (a : ℝ))) :
    0 < (b : ℝ) - (a : ℝ) := by
  nlinarith [hepspos, hepsba]

/-! ### The three exponents are ordered -/

/-- **The narrow exponent is at least the supply exponent.**

The hypothesis `hee'` of `Kakeya.StickyKakeya.ssfA_narrow_witness_package`: the narrow exponent
`e' = e + 6/(b - a)` exceeds `e` by a nonnegative residual. -/
private theorem A.inst_e_le_ePrime {eps e ePrime : ℝ} (hepspos : 0 < eps) {a b : ℕ}
    (hepsba : 3 ≤ eps * ((b : ℝ) - (a : ℝ)))
    (heP : ePrime = e + 6 / ((b : ℝ) - (a : ℝ))) :
    e ≤ ePrime := by
  rw [heP]
  exact le_add_of_nonneg_right (div_nonneg (by norm_num)
    (MultiScaleFac.A.inst_block_len_pos hepspos hepsba).le)

/-- **The two exponents are exactly six grid steps apart.**  The hypothesis `hk` of
`Kakeya.StickyKakeya.ssfA_narrow_witness_package`: the residual of `e'` is chosen to make
`(e' - e)(b - a) = 6`, which is what the witness package needs — three steps to round the reading
scale and three to keep the rounded scale inside the wide window. -/
private theorem A.inst_six_le_window_gap {eps e ePrime : ℝ} (hepspos : 0 < eps) {a b : ℕ}
    (hepsba : 3 ≤ eps * ((b : ℝ) - (a : ℝ)))
    (heP : ePrime = e + 6 / ((b : ℝ) - (a : ℝ))) :
    (6 : ℝ) ≤ (ePrime - e) * ((b : ℝ) - (a : ℝ)) := by
  have hne : (b : ℝ) - (a : ℝ) ≠ 0 :=
    (MultiScaleFac.A.inst_block_len_pos hepspos hepsba).ne'
  rw [heP, add_sub_cancel_left, div_mul_cancel₀ _ hne]

/-- **The narrow exponent is at least the window exponent.**

The hypothesis `hεe'` of `Kakeya.MultiScaleFac.A.clamp_bulletThree_window`.  Both steps are
nonnegative: `ε ≤ (1 + 2κ)ε = e` because `κ ≥ 0`, and `e ≤ e'` because the residual is
nonnegative. -/
private theorem A.inst_eps_le_ePrime {N : ℕ} {δ : NNReal} {eps e ePrime : ℝ} (hepspos : 0 < eps)
    (he : e = (1 + 2 * ((N : ℝ) / (ssfGridLen δ : ℝ))) * eps) {a b : ℕ}
    (hepsba : 3 ≤ eps * ((b : ℝ) - (a : ℝ)))
    (heP : ePrime = e + 6 / ((b : ℝ) - (a : ℝ))) :
    eps ≤ ePrime := by
  have hkappa : 0 ≤ (N : ℝ) / (ssfGridLen δ : ℝ) :=
    div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg (ssfGridLen δ))
  have hepse : eps ≤ e := he ▸ le_mul_of_one_le_left hepspos.le (by linarith)
  exact hepse.trans (MultiScaleFac.A.inst_e_le_ePrime hepspos hepsba heP)

/-! ### The gap budget, read against a ceiling -/

/-- **The gap budget absorbs the residual.**

The `ℝ`-to-`ℕ` step of the window accounting, isolated: the total gap `2√N + 6` produced below is
at most `8√N` once `N ≥ 1`, hence at most its ceiling.  Splitting this off keeps the cast out of
the estimate proper. -/
private theorem A.inst_two_sqrt_add_six_le_ceil {N : ℕ} (hN : 1 ≤ N) :
    2 * Real.sqrt (N : ℝ) + 6 ≤ ((⌈8 * Real.sqrt (N : ℝ)⌉₊ : ℕ) : ℝ) := by
  have hroot : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    simpa using Real.sqrt_le_sqrt (by exact_mod_cast hN : (1 : ℝ) ≤ (N : ℝ))
  exact MultiScaleFac.A.le_cast_ceil (by linarith)

/-- **The narrow and the `ε`-window are `⌈8√N⌉` grid steps apart.**  The hypothesis `hstep` of
`Kakeya.MultiScaleFac.A.clamp_bulletThree_window` at the gap budget `cg = ⌈8√N⌉`, measured against
the narrow exponent `e' = e + 6/(b - a)` and hence carrying the extra six steps:
`(e' - ε)(b - a) = 2κε(b - a) + 6 ≤ 2Nε + 6 = 2√N + 6 ≤ 8√N`. -/
theorem A.inst_window_steps {N : ℕ} (hN : 1 ≤ N) {δ : NNReal} {eps e ePrime : ℝ}
    (hepspos : 0 < eps) (heps : eps = 1 / Real.sqrt (N : ℝ)) (hM : 0 < ssfGridLen δ) {a b : ℕ}
    (hbM : b ≤ ssfGridLen δ) (hepsba : 3 ≤ eps * ((b : ℝ) - (a : ℝ)))
    (he : e = (1 + 2 * ((N : ℝ) / (ssfGridLen δ : ℝ))) * eps)
    (heP : ePrime = e + 6 / ((b : ℝ) - (a : ℝ))) :
    (ePrime - eps) * ((b : ℝ) - (a : ℝ)) ≤ ((⌈8 * Real.sqrt (N : ℝ)⌉₊ : ℕ) : ℝ) := by
  have hMR : (0 : ℝ) < (ssfGridLen δ : ℝ) := by exact_mod_cast hM
  have hNR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  have hlen : 0 < (b : ℝ) - (a : ℝ) := MultiScaleFac.A.inst_block_len_pos hepspos hepsba
  have hlenne : (b : ℝ) - (a : ℝ) ≠ 0 := ne_of_gt hlen
  have hbR : (b : ℝ) ≤ (ssfGridLen δ : ℝ) := by exact_mod_cast hbM
  have hlenM : (b : ℝ) - (a : ℝ) ≤ (ssfGridLen δ : ℝ) := by
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    linarith
  have hfac : (0 : ℝ) ≤ 2 * ((N : ℝ) / (ssfGridLen δ : ℝ)) * eps :=
    mul_nonneg (mul_nonneg (by norm_num) (div_nonneg hNR.le hMR.le)) hepspos.le
  have hsplit : (ePrime - eps) * ((b : ℝ) - (a : ℝ))
      = (e - eps) * ((b : ℝ) - (a : ℝ)) + 6 := by
    rw [heP]; linear_combination div_mul_cancel₀ (6 : ℝ) hlenne
  have hle1 : (e - eps) * ((b : ℝ) - (a : ℝ))
      ≤ 2 * ((N : ℝ) / (ssfGridLen δ : ℝ)) * eps * (ssfGridLen δ : ℝ) := by
    rw [show e - eps = 2 * ((N : ℝ) / (ssfGridLen δ : ℝ)) * eps by rw [he]; ring]
    exact mul_le_mul_of_nonneg_left hlenM hfac
  have hcancel : 2 * ((N : ℝ) / (ssfGridLen δ : ℝ)) * eps * (ssfGridLen δ : ℝ)
      = 2 * (N : ℝ) * eps := by
    linear_combination 2 * eps * div_mul_cancel₀ (N : ℝ) (ne_of_gt hMR)
  have hroot : 2 * (N : ℝ) * eps = 2 * Real.sqrt (N : ℝ) := by
    rw [heps, mul_one_div, mul_div_assoc, Real.div_sqrt]
  linarith [MultiScaleFac.A.inst_two_sqrt_add_six_le_ceil hN]

/-! ### The narrow window is nonempty -/

/-- **Twice the narrow exponent is at most one.**

The side condition of `Kakeya.MultiScaleFac.A.narrow_window_nonempty`.  Three bounds enter:
`κ = N/M ≤ 1/3` from `3N ≤ M`; `ε ≤ 1/64`; and `6/(b - a) ≤ 2ε` from `3 ≤ ε(b - a)`.  Together
`2e' = 2(1 + 2κ)ε + 12/(b - a) ≤ (10/3)ε + 4ε = (22/3)ε ≤ 22/192 < 1`. -/
private theorem A.inst_two_mul_ePrime_le_one {N : ℕ} {δ : NNReal} {eps e ePrime : ℝ}
    (hepspos : 0 < eps) (heps64 : eps ≤ 1 / 64) (hM : 0 < ssfGridLen δ)
    (hNM : 3 * N ≤ ssfGridLen δ) {a b : ℕ} (hepsba : 3 ≤ eps * ((b : ℝ) - (a : ℝ)))
    (he : e = (1 + 2 * ((N : ℝ) / (ssfGridLen δ : ℝ))) * eps)
    (heP : ePrime = e + 6 / ((b : ℝ) - (a : ℝ))) :
    2 * ePrime ≤ 1 := by
  have hMR : (0 : ℝ) < (ssfGridLen δ : ℝ) := by exact_mod_cast hM
  have hNMR : (3 : ℝ) * (N : ℝ) ≤ (ssfGridLen δ : ℝ) := by exact_mod_cast hNM
  have hkap : (N : ℝ) / (ssfGridLen δ : ℝ) ≤ 1 / 3 := by
    rw [div_le_iff₀ hMR]; linarith only [hNMR]
  have hlen : 0 < (b : ℝ) - (a : ℝ) := MultiScaleFac.A.inst_block_len_pos hepspos hepsba
  have hsix : 6 / ((b : ℝ) - (a : ℝ)) ≤ 2 * eps := by
    rw [div_le_iff₀ hlen, mul_assoc]; linarith only [hepsba]
  have hkeps := mul_le_mul_of_nonneg_right hkap hepspos.le
  rw [heP, he]
  linarith only [hkeps, hsix, heps64]

/-- **The narrow window is nonempty at the instantiated exponent.**

The hypothesis `hnwne` of `Kakeya.MultiScaleFac.A.clamp_bulletThree_window`, obtained from
`Kakeya.MultiScaleFac.A.clamp_narrow_window_nonempty` once `2e' ≤ 1` is known. -/
private theorem A.inst_narrow_window_nonempty {N : ℕ} {δ : NNReal} (hδ : 0 < δ) (hδlt : δ < 1)
    (hM : 0 < ssfGridLen δ) (hNM : 3 * N ≤ ssfGridLen δ) {eps e ePrime : ℝ}
    (hepspos : 0 < eps) (heps64 : eps ≤ 1 / 64) {a b : ℕ}
    (hlong : IsLongBlock (ssfGridLen δ) eps a b)
    (hepsba : 3 ≤ eps * ((b : ℝ) - (a : ℝ)))
    (he : e = (1 + 2 * ((N : ℝ) / (ssfGridLen δ : ℝ))) * eps)
    (heP : ePrime = e + 6 / ((b : ℝ) - (a : ℝ))) :
    (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ePrime
      ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
        * ((gridScale δ (ssfGridLen δ) b : ℝ)
            / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ ePrime := by
  exact MultiScaleFac.A.clamp_narrow_window_nonempty hδ hδlt hM hlong
    (MultiScaleFac.A.inst_two_mul_ePrime_le_one hepspos heps64 hM hNM hepsba he heP)

/-! ### The whole package -/

/-- **The window arithmetic of the amended dichotomy, in one statement.**  Every arithmetic
hypothesis that `Kakeya.StickyKakeya.ssfA_narrow_witness_package` and
`Kakeya.MultiScaleFac.A.clamp_bulletThree_window` ask of the three exponents `ε = 1/√N`,
`e = (1 + 2N/M)ε` and `e' = e + 6/(b - a)`, produced at once from the long-block condition. -/
theorem A.window_instance {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδlt : δ < 1)
    (hM : 0 < ssfGridLen δ) {N : ℕ} (hN : 4096 ≤ N) (hNM : 3 * N ≤ ssfGridLen δ)
    {eps : ℝ} (heps : eps = 1 / Real.sqrt (N : ℝ)) {a b : ℕ} (hbM : b ≤ ssfGridLen δ)
    (hlong : IsLongBlock (ssfGridLen δ) eps a b) {e ePrime : ℝ}
    (he : e = (1 + 2 * ((N : ℝ) / (ssfGridLen δ : ℝ))) * eps)
    (heP : ePrime = e + 6 / ((b : ℝ) - (a : ℝ))) :
    a < b ∧ 0 ≤ e ∧ e ≤ ePrime ∧ eps ≤ ePrime ∧
      3 ≤ eps * ((b : ℝ) - (a : ℝ)) ∧
      (6 : ℝ) ≤ (ePrime - e) * ((b : ℝ) - (a : ℝ)) ∧
      (ePrime - eps) * ((b : ℝ) - (a : ℝ)) ≤ ((⌈8 * Real.sqrt (N : ℝ)⌉₊ : ℕ) : ℝ) ∧
      ((gridScale δ (ssfGridLen δ) b : ℝ)
          * ((gridScale δ (ssfGridLen δ) a : ℝ)
              / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ePrime
        ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
          * ((gridScale δ (ssfGridLen δ) b : ℝ)
              / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ ePrime) ∧
      ((gridScale δ (ssfGridLen δ) a : ℝ)
          * ((gridScale δ (ssfGridLen δ) b : ℝ)
              / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ eps ≤ 1) := by
  have hab : a < b := by
    have hlongN : ((⌈eps * (ssfGridLen δ : ℝ)⌉₊ : ℕ) + a) < b := by
      simpa [IsLongBlock] using hlong
    omega
  have hepspos : 0 < eps := eps_pos_of_eq_one_div_sqrt (by omega : 16 ≤ N) heps
  have heps64 : eps ≤ 1 / 64 := eps_le_one_div_64_of_eq_one_div_sqrt hN heps
  have hepsN : (1 : ℝ) ≤ eps ^ 2 * (N : ℝ) :=
    (eps_sq_mul_eq_one_of_eq_one_div_sqrt (by omega : 0 < N) heps).ge
  have hepsba : 3 ≤ eps * ((b : ℝ) - (a : ℝ)) :=
    MultiScaleFac.A.three_le_eps_mul_block hepspos hNM hepsN hlong
  have he0 : (0 : ℝ) ≤ e := by
    have hkappa : (0 : ℝ) ≤ (N : ℝ) / (ssfGridLen δ : ℝ) :=
      div_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg (ssfGridLen δ))
    rw [he]
    exact mul_nonneg (by linarith) hepspos.le
  exact ⟨hab, he0, MultiScaleFac.A.inst_e_le_ePrime hepspos hepsba heP,
    MultiScaleFac.A.inst_eps_le_ePrime hepspos he hepsba heP, hepsba,
    MultiScaleFac.A.inst_six_le_window_gap hepspos hepsba heP,
    MultiScaleFac.A.inst_window_steps (by omega : 1 ≤ N) hepspos heps hM hbM hepsba he heP,
    MultiScaleFac.A.inst_narrow_window_nonempty hδ hδlt hM hNM hepspos heps64 hlong hepsba he heP,
    MultiScaleFac.A.clamp_window_upper_le_one hδ hδ1 hab.le hepspos.le⟩

end MultiScaleFac

end Kakeya

end
