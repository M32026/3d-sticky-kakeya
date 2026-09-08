/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.NodeAncestorSplit
public import Kakeya.MultiScaleFac.Loss

/-!
# Transporting the third bullet between radii and window ends

Comparing the Frostman constants of two concentric dilates of one node through a coarse level, the
two ends of the window, and the arithmetic of the window exponents.

This module is the merge of the former `Bullet3TransportA`, `Bullet3WindowA`, `Bullet3WindowArith`.
Each keeps its own section, so its file-level `open`s and `variable`s stay confined to it.

## Container transport across concentric dilates, half (A)

The third bullet of alternative (ii) of GWZ Lemma 7.7(A) asserts a *lower* bound on the Frostman
constant of the level-`b` nodes inside the real container `T_j^{(ρ)}`, for every `ρ` of the
`ε`-window.  The terminal alternative supplies such a bound only at grid scales lying at relative
depth at least `ε` inside the block, and reading it up to a real container costs an ancestor split,
which needs the reading level to be *finer* than `ρ` by a bounded number of grid steps.  At the fine
end of the window the required reading level therefore leaves the range on which the split test
speaks, by a bounded number of grid steps.

This section supplies the missing move: a transport in the opposite direction,

  `C_F(𝕋_b[T_j^{(ρ')}], T_j^{(ρ')}) ≤ L · C_F(𝕋_b[T_j^{(ρ)}], T_j^{(ρ)})`

for two concentric dilates of the same level-`b` node whose radii differ by a bounded number of grid
steps.  Half (B) gets the corresponding step for free, its quantity `Δ_max` being monotone in the
container; here both the index set and the container move and the Frostman constant is monotone in
neither.  The transport is *false* without extra structure — an isolated fine node inside the small
container makes the left side large and the right side `O(1)` — and what makes it true is the
two-sided band `Kakeya.MultiScaleFac.PairBandOn` carried by the family the banded stopping time
returns: it brackets the class-image maximal density of every pair of levels at every node of the
coarser level, and so replaces half (B)'s free monotonicity.

## The two ends of the window, half (A)

The third bullet of alternative (ii) of GWZ Lemma 7.7(A) is stated on the `ε`-window, while the
witness reading of the terminal alternative is available only on the narrower window of exponent
`e' ≥ ε`: the reading grid scale has to sit inside the range on which the split test speaks, and it
is a bounded number of grid steps finer than `ρ`.  The two windows differ by `(e' - ε)(b - a)` grid
steps at each end, which is a `Kakeya.MultiScaleFac.scaleGapLoss` and not a fixed power of `δ`.

This section closes both ends.  At the fine end the bound descends from a coarser radius by the
container transport of `Kakeya.MultiScaleFac.frostmanConstant_nodesIn_rescale_le_of_pairBand`.  At
the coarse end it ascends from a finer radius, and no band is needed: the ascent is the free
direction of `Kakeya.MultiScaleFac.card_mul_frostmanConstant_nodesIn_le`, whose only input is the
ancestor-split count of the nodes of the larger container against the nodes of the smaller one.

## The arithmetic of the two window exponents, half (A)

The third bullet of alternative (ii) of GWZ Lemma 7.7(A) is stated on the `ε`-window, while the
terminal alternative supplies its witness only on the wider window of exponent `e' = (1 + 2κ)ε`
with `κ = N/⌈\log\log 1/δ⌉`.  `Kakeya.MultiScaleFac.A.exists_window_clamp` clamps a scale of the
wide window into the narrow one at the price of one `Kakeya.MultiScaleFac.scaleGapLoss` at each end,
provided its two side conditions are met: the narrow window must be nonempty, and the two exponents
must differ by a bounded number of grid steps.

This section collects the purely arithmetic facts the clamp is missing.

* `Kakeya.MultiScaleFac.A.lambda_le_scaleGapLoss` turns the packing count `(4ρ/σ_c)^{2n}` of the
  ancestor split into a single `Kakeya.MultiScaleFac.scaleGapLoss` with an explicit exponent.  This
  is what keeps the coarse-end factor `Λ` of
  `Kakeya.MultiScaleFac.A.bulletThree_coarseEnd_of_ancestor` subpolynomial: without the sharp
  rounding of `Kakeya.MultiScaleFac.A.exists_round_index_sharp` the ratio `ρ/σ_c` could be a whole
  block of grid steps, and the count would be a fixed power of `δ`.
* `Kakeya.MultiScaleFac.A.narrow_window_nonempty` is the hypothesis `hnarrow` of the clamp: on a
  long block the narrow window has a nonempty interior as soon as `2e' ≤ 1`.

The hypothesis `hc` of the clamp, that the two window exponents differ by at most `⌈8√N⌉` grid
steps, is supplied on the live route by `Kakeya.MultiScaleFac.A.inst_window_steps`.
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

/-! ### The two halves of the band -/

/-! ### The transport of the maximal density -/

open scoped Classical in
/-- **Transport of `Kakeya.maxDensity` across concentric dilates.**  The nodes of the larger
container are split along their level-`k` ancestors, of which there are at most
`2 · 25^{2n} (4ρ'/ρ_k)^{2n} C_u`; each summand is bounded by the upper half of the band, and the
lower half turns the band value back into the maximal density of the smaller container. -/
theorem maxDensity_nodesIn_rescale_le_of_pairBand {δ : NNReal} (hδ : 0 < δ) {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} [DecidableEq ι]
    (𝒰 : UniformTubeSet s T N Cu) (hs : s.Nonempty)
    {k b Kn : ℕ} (hkb : k ≤ b) (hb : b ≤ N) (hk : k ≤ N)
    (h2δ : 2 * δ ≤ gridScale δ N k) {Φ : ENNReal} {Cb : NNReal}
    (hP : ∀ p ∈ 𝒰.cover.indexSet k, ∃ P ⊆ 𝒰.cover.indexSet k, P.card ≤ Kn ∧
      𝒰.nodesIn b (((𝒰.cover.tube k p).rescale
          (8 * gridScale δ N k)).toConvexSpaceBody)
        ⊆ P.biUnion (fun q =>
            (coverClass s (𝒰.cover.assign k) q).image (𝒰.cover.assign b)))
    (hbandLo : ∀ p ∈ 𝒰.cover.indexSet k,
      Φ ≤ Kakeya.maxDensity ((coverClass s (𝒰.cover.assign k) p).image (𝒰.cover.assign b))
          (fun w => (𝒰.cover.tube b w).toConvexSpaceBody))
    (hbandHi : ∀ p ∈ 𝒰.cover.indexSet k,
      Kakeya.maxDensity ((coverClass s (𝒰.cover.assign k) p).image (𝒰.cover.assign b))
          (fun w => (𝒰.cover.tube b w).toConvexSpaceBody) ≤ (Cb : ENNReal) * Φ)
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet b) {ρ ρ' : NNReal}
    (hρ : 4 * gridScale δ N k ≤ ρ) (_hρρ' : ρ ≤ ρ')
    (hr : gridScale δ N k ≤ 4 * ρ') :
    Kakeya.maxDensity (𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ').toConvexSpaceBody)
        (fun w => (𝒰.cover.tube b w).toConvexSpaceBody)
      ≤ ENNReal.ofReal (2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
            * (((4 * ρ' : NNReal) : ℝ) / (gridScale δ N k : ℝ)) ^ (2 * Module.finrank ℝ E)
            * (Cu : ℝ))
          * ((Kn : ENNReal) * (Cb : ENNReal))
          * Kakeya.maxDensity (𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody)
              (fun w => (𝒰.cover.tube b w).toConvexSpaceBody) := by
  let K' : ConvexSpaceBody E := ((𝒰.cover.tube b j).rescale ρ').toConvexSpaceBody
  let Na : Finset ι := (𝒰.nodesIn b K').image (𝒰.nodeAncestor b k)
  let P : ℝ := 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
      * (((4 * ρ' : NNReal) : ℝ) / (gridScale δ N k : ℝ)) ^ (2 * Module.finrank ℝ E) * (Cu : ℝ)
  let η : ENNReal := (Kn : ENNReal) * ((Cb : ENNReal) * Φ)
  let W : ι → ConvexSpaceBody E := fun w => (𝒰.cover.tube b w).toConvexSpaceBody
  let M : ENNReal := Kakeya.maxDensity
    (𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody) W
  have hsummand : ∀ q ∈ Na, Kakeya.maxDensity (𝒰.nodesUnder b k q) W ≤ η := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨w, hw, rfl⟩
    obtain ⟨P, hPsub, hPcard, hPcover⟩ := hP (𝒰.nodeAncestor b k w)
      (UniformTubeSet.nodeAncestor_mem (𝒰 := 𝒰) (a := k) (b := b) (ha := hk) (hb := hb)
        (hs := hs) ((𝒰.mem_nodesIn_iff b K' w).mp hw).1)
    have hsub : 𝒰.nodesUnder b k (𝒰.nodeAncestor b k w) ⊆
        P.biUnion (fun a => (coverClass s (𝒰.cover.assign k) a).image (𝒰.cover.assign b)) :=
      (nodesUnder_subset_nodesIn_rescale 𝒰 (𝒰.nodeAncestor b k w)
        (le_mul_of_one_le_left zero_le (by norm_num))).trans hPcover
    refine (maxDensity_le_sum_of_subset_biUnion W hsub).trans
      ((Finset.sum_le_sum fun a ha => hbandHi a (hPsub ha)).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_left (Nat.cast_le.2 hPcard) _
  have hcard : (Na.card : ENNReal) ≤ ENNReal.ofReal P :=
    (ENNReal.ofReal_natCast Na.card).ge.trans (ENNReal.ofReal_le_ofReal
      (card_image_nodeAncestor_le_ratio (hδ := hδ) (𝒰 := 𝒰) (a := k) (b := b) (ha := hk)
        (hb := hb) (hs := hs) (h2δ := h2δ) (r := ρ') (hr := hr) ((𝒰.cover.tube b j).rescale ρ')))
  have hPhiM : Φ ≤ M := by
    have hch : (𝒰.cover.tube k (𝒰.nodeAncestor b k j)).toConvexSpaceBody
        ≤ ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody :=
      (Tube.rescale_le_of_le (𝒰.cover.tube b j) _
        (UniformTubeSet.tube_le_tube_nodeAncestor (𝒰 := 𝒰) (a := k) (b := b)
          (hab := hkb) (hb := hb) (hs := hs) (hw := hj))).trans
        (Tube.rescale_le_rescale_of_radius_le (𝒰.cover.tube b j) hρ)
    refine (hbandLo _ (UniformTubeSet.nodeAncestor_mem (𝒰 := 𝒰) (a := k) (b := b)
      (ha := hk) (hb := hb) (hs := hs) (hw := hj))).trans (maxDensity_mono W ?_)
    exact Finset.image_subset_iff.mpr fun i hi =>
      nodesIn_subset_of_le 𝒰 b hch (assign_mem_nodesUnder 𝒰 hkb hb hi)
  calc
    Kakeya.maxDensity (𝒰.nodesIn b K') W ≤
        ∑ q ∈ Na, Kakeya.maxDensity (𝒰.nodesUnder b k q) W :=
      maxDensity_nodesIn_le_sum_nodesUnder (𝒰 := 𝒰) (c := k) (b := b) (hcb := hkb)
        (hb := hb) (hs := hs) (K := K')
    _ ≤ (Na.card : ENNReal) * η :=
      (Finset.sum_le_sum hsummand).trans_eq (by rw [Finset.sum_const, nsmul_eq_mul])
    _ ≤ ENNReal.ofReal P * ((Kn : ENNReal) * (Cb : ENNReal)) * M := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul' hcard (mul_le_mul_right (mul_le_mul_right hPhiM _) _)

/-! ### From maximal densities to Frostman constants -/

/-- **The volume of a dilate against the volume of a smaller concentric dilate.**

`Kakeya.MultiScaleFac.scaleGapVolConst` is `5 C_n / c_n`, so this is the `b = 4` instance of
`Tube.volume_le_of_le` against `Tube.le_volume`; the ratio of radii appears to the power `n - 1`
and carries no power of `δ`. -/
theorem volume_rescale_le_scaleGapVolConst_mul_volume_rescale {σ : NNReal} (T : Tube σ E)
    {ρ ρ' : NNReal}
    (hρ : 0 < ρ) (hρ' : ρ' ≤ 4) :
    volume ((T.rescale ρ').carrier)
      ≤ ENNReal.ofReal ((scaleGapVolConst (Module.finrank ℝ E) : ℝ)
            * ((ρ' : ℝ) / (ρ : ℝ)) ^ (Module.finrank ℝ E - 1))
        * volume ((T.rescale ρ).carrier) := by
  set n := Module.finrank ℝ E
  set m := n - 1
  set A : NNReal := scaleGapVolConst n * (ρ' / ρ) ^ m with hAdef
  have hratio : A * (Tube.le_volume.c n * ρ ^ m) = 5 * Tube.volume_le.C n * ρ' ^ m := by
    rw [hAdef, scaleGapVolConst, div_pow, mul_mul_mul_comm,
      div_mul_cancel₀ _ (Tube.le_volume.c_pos n).ne', div_mul_cancel₀ _ (pow_ne_zero m hρ.ne')]
  have hA : (A : ℝ) = (scaleGapVolConst n : ℝ) * ((ρ' : ℝ) / (ρ : ℝ)) ^ m := by
    simp only [hAdef, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_div]
  rw [← hA, ENNReal.ofReal_coe_nnreal]
  calc
    volume ((T.rescale ρ').carrier) ≤ ((5 * Tube.volume_le.C n * ρ' ^ m : NNReal) : ENNReal) := by
      -- The `b = 4` instance of `Tube.volume_le_of_le`: the fattened scale `ρ'` exceeds `1`, so
      -- the `δ ≤ 1` bound `Tube.volume_le` does not apply.  Its constant `2 ^ n * (1 + 4)` is
      -- relaxed to the `5 * volume_le.C n` that `scaleGapVolConst` is defined against.
      refine (Tube.volume_le_of_le hρ' (T.rescale ρ')).trans (ENNReal.coe_le_coe.mpr ?_)
      have hC : ((2 : NNReal) ^ n * (1 + 4) : NNReal) ≤ 5 * Tube.volume_le.C n := by
        unfold Tube.volume_le.C
        rw [pow_succ]
        calc (2 : NNReal) ^ n * (1 + 4)
            = 5 * 2 ^ n := by ring
          _ ≤ 5 * (2 ^ n * 2) := by
              gcongr
              exact le_mul_of_one_le_right zero_le one_le_two
      exact mul_le_mul_right' hC _
    _ = (A : ENNReal) * ((Tube.le_volume.c n * ρ ^ m : NNReal) : ENNReal) := by
      rw [← ENNReal.coe_mul, hratio]
    _ ≤ (A : ENNReal) * volume ((T.rescale ρ).carrier) :=
      mul_le_mul_right (Tube.le_volume (T.rescale ρ)) _

omit [Nontrivial E] in
/-- **The density in the smaller container against the density in the larger one.**

The nodes of the smaller container are among those of the larger one and each of them lies in its
container, so the two numerators compare directly; the only loss is the ratio of the two container
volumes. -/
theorem densityIn_nodesIn_le_mul_densityIn_nodesIn {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T N Cu) {b : ℕ}
    {K₁ K₂ : ConvexSpaceBody E} (hK : K₁ ≤ K₂) {Vr : ENNReal} (_hVr : Vr ≠ ⊤)
    (hvol : volume K₂.carrier ≤ Vr * volume K₁.carrier)
    (h1 : volume K₁.carrier ≠ 0) (_h2 : volume K₂.carrier ≠ 0) :
    Kakeya.densityIn (𝒰.nodesIn b K₁) (fun w => (𝒰.cover.tube b w).toConvexSpaceBody) K₁
      ≤ Vr * Kakeya.densityIn (𝒰.nodesIn b K₂)
          (fun w => (𝒰.cover.tube b w).toConvexSpaceBody) K₂ := by
  set W : ι → ConvexSpaceBody E := fun w => (𝒰.cover.tube b w).toConvexSpaceBody
  have hW1 : ∀ i ∈ 𝒰.nodesIn b K₁, W i ≤ K₁ := fun i hi => ((𝒰.mem_nodesIn_iff b K₁ i).mp hi).2
  have hW2 : ∀ i ∈ 𝒰.nodesIn b K₂, W i ≤ K₂ := fun i hi => ((𝒰.mem_nodesIn_iff b K₂ i).mp hi).2
  rw [← ENNReal.mul_le_mul_iff_right (a := volume K₁.carrier) h1 K₁.isCompact'.measure_ne_top]
  calc
    volume K₁.carrier * Kakeya.densityIn (𝒰.nodesIn b K₁) W K₁
        = ∑ i ∈ 𝒰.nodesIn b K₁, volume (W i).carrier :=
      (mul_comm _ _).trans (Kakeya.sum_volume_eq_densityIn_mul_volume' hW1).symm
    _ ≤ ∑ i ∈ 𝒰.nodesIn b K₂, volume (W i).carrier :=
      Finset.sum_le_sum_of_subset (nodesIn_subset_of_le 𝒰 b hK)
    _ = Kakeya.densityIn (𝒰.nodesIn b K₂) W K₂ * volume K₂.carrier :=
      Kakeya.sum_volume_eq_densityIn_mul_volume' hW2
    _ ≤ Kakeya.densityIn (𝒰.nodesIn b K₂) W K₂ * (Vr * volume K₁.carrier) := by gcongr
    _ = volume K₁.carrier * (Vr * Kakeya.densityIn (𝒰.nodesIn b K₂) W K₂) := by ring

omit [Nontrivial E] in
/-- **A Frostman constant is transported by a maximal-density bound and a density bound.**

Both Frostman constants are `Δ_max / Δ` by
`ConvexSpaceBody.frostmanConstant_eq_maxDensity_div`; the numerator is moved by `hmax` and the
denominator by `hdens`. -/
theorem frostmanConstant_le_mul_of_maxDensity_le_of_densityIn_le {t₁ t₂ : Finset ι}
    {W : ι → ConvexSpaceBody E} {K₁ K₂ : ConvexSpaceBody E}
    (hW1 : ∀ i ∈ t₁, W i ≤ K₁) (_hW2 : ∀ i ∈ t₂, W i ≤ K₂)
    (_hd1 : 0 < Kakeya.densityIn t₁ W K₁) (_hd2 : 0 < Kakeya.densityIn t₂ W K₂)
    {A Vr : ENNReal} (_hA : A ≠ ⊤) (_hVr : Vr ≠ ⊤)
    (hmax : Kakeya.maxDensity t₂ W ≤ A * Kakeya.maxDensity t₁ W)
    (hdens : Kakeya.densityIn t₁ W K₁ ≤ Vr * Kakeya.densityIn t₂ W K₂) :
    ConvexSpaceBody.frostmanConstant t₂ W K₂
      ≤ A * Vr * ConvexSpaceBody.frostmanConstant t₁ W K₁ := by
  set m1 : ENNReal := Kakeya.maxDensity t₁ W
  set m2 : ENNReal := Kakeya.maxDensity t₂ W
  set d1 : ENNReal := Kakeya.densityIn t₁ W K₁
  set d2 : ENNReal := Kakeya.densityIn t₂ W K₂
  set C1 : ENNReal := ConvexSpaceBody.frostmanConstant t₁ W K₁
  rw [ConvexSpaceBody.frostmanConstant_le_iff]
  intro K' hK'
  have hm1 : m1 ≤ C1 * d1 :=
    ConvexSpaceBody.IsFrostmanIn.maxDensity_le_of_carrier_subset
      (ConvexSpaceBody.isFrostmanIn_frostmanConstant (s := t₁) (W := W) (K := K₁)) hW1
  calc
    Kakeya.densityIn t₂ W K' ≤ m2 := Kakeya.le_maxDensity t₂ W K'
    _ ≤ A * m1 := hmax
    _ ≤ A * (C1 * d1) := by gcongr
    _ ≤ A * (C1 * (Vr * d2)) := by gcongr
    _ = (A * Vr * C1) * d2 := by ring

/-- **The nodes of a dilate of a level-`b` node have positive density in it.**

The node `j` itself is one of them, and a tube of positive radius has positive volume. -/
theorem densityIn_nodesIn_rescale_pos {δ : NNReal} (hδ : 0 < δ) {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T N Cu) {b : ℕ} {j : ι}
    (hj : j ∈ 𝒰.cover.indexSet b) {ρ : NNReal} (hρ : gridScale δ N b ≤ ρ) :
    0 < Kakeya.densityIn (𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody)
        (fun w => (𝒰.cover.tube b w).toConvexSpaceBody)
        ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody := by
  rw [Kakeya.densityIn_pos_iff]
  have hleNode : (𝒰.cover.tube b j).toConvexSpaceBody ≤
      ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody :=
    Tube.le_rescale (𝒰.cover.tube b j) hρ
  refine ⟨j, (𝒰.mem_nodesIn_iff _ _ j).mpr ⟨hj, hleNode⟩, ?_, hleNode⟩
  refine lt_of_lt_of_le ?_ (Tube.le_volume (𝒰.cover.tube b j))
  exact_mod_cast mul_pos (Tube.le_volume.c_pos (Module.finrank ℝ E))
    (pow_pos (gridScale_pos hδ N b) (Module.finrank ℝ E - 1))

/-! ### The container transport -/

/-- A dilate of a tube by a positive radius has a carrier of nonzero volume. -/
private lemma volume_rescale_toConvexSpaceBody_ne_zero -- (extracted by Fuse golfer)
    {r : NNReal} (T : Tube r E) {ρ : NNReal} (hρ : 0 < ρ) :
    volume (T.rescale ρ).toConvexSpaceBody.carrier ≠ 0 :=
  ((ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos (Module.finrank ℝ E)).ne')
    (pow_ne_zero _ (ENNReal.coe_ne_zero.mpr hρ.ne'))).trans_le
      (le_volume_rescale_toConvexSpaceBody T ρ)).ne'

open scoped Classical in
/-- **The container transport of the half-(A) third bullet.**  For two concentric dilates of the
same level-`b` node whose radii differ by a bounded number of grid steps, the Frostman constant of
the larger is at most a loss times that of the smaller.  The loss is a packing count, the band
constant and the ratio of the container volumes; none is a power of `δ` beyond a `scaleGapLoss`. -/
theorem frostmanConstant_nodesIn_rescale_le_of_pairBand {δ : NNReal} (hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} [DecidableEq ι]
    (𝒰 : UniformTubeSet s T N Cu) (hs : s.Nonempty)
    {k b Kn : ℕ} (hkb : k ≤ b) (hb : b ≤ N) (hk : k ≤ N)
    (h2δ : 2 * δ ≤ gridScale δ N k) {Φ : ENNReal} {Cb : NNReal}
    (hP : ∀ p ∈ 𝒰.cover.indexSet k, ∃ P ⊆ 𝒰.cover.indexSet k, P.card ≤ Kn ∧
      𝒰.nodesIn b (((𝒰.cover.tube k p).rescale
          (8 * gridScale δ N k)).toConvexSpaceBody)
        ⊆ P.biUnion (fun q =>
            (coverClass s (𝒰.cover.assign k) q).image (𝒰.cover.assign b)))
    (hbandLo : ∀ p ∈ 𝒰.cover.indexSet k,
      Φ ≤ Kakeya.maxDensity ((coverClass s (𝒰.cover.assign k) p).image (𝒰.cover.assign b))
          (fun w => (𝒰.cover.tube b w).toConvexSpaceBody))
    (hbandHi : ∀ p ∈ 𝒰.cover.indexSet k,
      Kakeya.maxDensity ((coverClass s (𝒰.cover.assign k) p).image (𝒰.cover.assign b))
          (fun w => (𝒰.cover.tube b w).toConvexSpaceBody) ≤ (Cb : ENNReal) * Φ)
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet b) {ρ ρ' : NNReal}
    (hbρ : gridScale δ N b ≤ ρ) (hρ : 4 * gridScale δ N k ≤ ρ) (hρρ' : ρ ≤ ρ')
    (hρ'4 : ρ' ≤ 4) (hr : gridScale δ N k ≤ 4 * ρ') :
    ConvexSpaceBody.frostmanConstant
        (𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ').toConvexSpaceBody)
        (fun w => (𝒰.cover.tube b w).toConvexSpaceBody)
        ((𝒰.cover.tube b j).rescale ρ').toConvexSpaceBody
      ≤ ENNReal.ofReal (2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
            * (((4 * ρ' : NNReal) : ℝ) / (gridScale δ N k : ℝ)) ^ (2 * Module.finrank ℝ E)
            * (Cu : ℝ))
          * ((Kn : ENNReal) * (Cb : ENNReal))
          * ENNReal.ofReal ((scaleGapVolConst (Module.finrank ℝ E) : ℝ)
              * ((ρ' : ℝ) / (ρ : ℝ)) ^ (Module.finrank ℝ E - 1))
          * ConvexSpaceBody.frostmanConstant
              (𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody)
              (fun w => (𝒰.cover.tube b w).toConvexSpaceBody)
              ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody := by
  have hρpos : 0 < ρ := lt_of_lt_of_le (mul_pos (by norm_num) (gridScale_pos hδ N k)) hρ
  exact frostmanConstant_le_mul_of_maxDensity_le_of_densityIn_le
    (fun i hi => ((𝒰.mem_nodesIn_iff _ _ i).mp hi).2)
    (fun i hi => ((𝒰.mem_nodesIn_iff _ _ i).mp hi).2)
    (densityIn_nodesIn_rescale_pos hδ 𝒰 hj hbρ)
    (densityIn_nodesIn_rescale_pos hδ 𝒰 hj (hbρ.trans hρρ'))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top Kn) ENNReal.coe_ne_top))
    ENNReal.ofReal_ne_top
    (maxDensity_nodesIn_rescale_le_of_pairBand hδ 𝒰 hs hkb hb hk h2δ hP hbandLo hbandHi hj
      hρ hρρ' hr)
    (densityIn_nodesIn_le_mul_densityIn_nodesIn (𝒰 := 𝒰) (b := b)
      (hK := Tube.rescale_le_rescale_of_radius_le (𝒰.cover.tube b j) hρρ')
      (_hVr := ENNReal.ofReal_ne_top)
      (hvol := volume_rescale_le_scaleGapVolConst_mul_volume_rescale (𝒰.cover.tube b j) hρpos hρ'4)
      (h1 := volume_rescale_toConvexSpaceBody_ne_zero (𝒰.cover.tube b j) hρpos)
      (_h2 := volume_rescale_toConvexSpaceBody_ne_zero (𝒰.cover.tube b j) (hρpos.trans_le hρρ')))

/-! ### The third bullet below the reading range -/

open scoped Classical in
/-- **The third bullet at a scale below the reading range.**  At the fine end of the `ε`-window the
bullet is only available at a radius `ρ'` a bounded number of grid steps coarser.  The left-hand
side is monotone in the radius and the right-hand side is moved by the container transport, so the
bound descends to `ρ` at the price of the transport loss. -/
theorem A.bulletThree_fineEnd_of_transport {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} [DecidableEq ι]
    (𝒰 : UniformTubeSet s T N Cu) (hs : s.Nonempty)
    {k b Kn : ℕ} (hkb : k ≤ b) (hb : b ≤ N) (hk : k ≤ N)
    (h2δ : 2 * δ ≤ gridScale δ N k) {Φ : ENNReal} {Cb : NNReal}
    (hP : ∀ p ∈ 𝒰.cover.indexSet k, ∃ P ⊆ 𝒰.cover.indexSet k, P.card ≤ Kn ∧
      𝒰.nodesIn b (((𝒰.cover.tube k p).rescale
          (8 * gridScale δ N k)).toConvexSpaceBody)
        ⊆ P.biUnion (fun q =>
            (coverClass s (𝒰.cover.assign k) q).image (𝒰.cover.assign b)))
    (hbandLo : ∀ p ∈ 𝒰.cover.indexSet k,
      Φ ≤ Kakeya.maxDensity ((coverClass s (𝒰.cover.assign k) p).image (𝒰.cover.assign b))
          (fun w => (𝒰.cover.tube b w).toConvexSpaceBody))
    (hbandHi : ∀ p ∈ 𝒰.cover.indexSet k,
      Kakeya.maxDensity ((coverClass s (𝒰.cover.assign k) p).image (𝒰.cover.assign b))
          (fun w => (𝒰.cover.tube b w).toConvexSpaceBody) ≤ (Cb : ENNReal) * Φ)
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet b) {ρ ρ' : NNReal}
    (hbρ : gridScale δ N b ≤ ρ) (hρ : 4 * gridScale δ N k ≤ ρ) (hρρ' : ρ ≤ ρ')
    (hρ'4 : ρ' ≤ 4) (hr : gridScale δ N k ≤ 4 * ρ')
    {ζ' : ℝ} (hζ' : 0 ≤ ζ') {D : ENNReal}
    (hbound : ENNReal.ofReal (((ρ' : ℝ) / (gridScale δ N b : ℝ)) ^ ζ')
      ≤ D * ConvexSpaceBody.frostmanConstant
          (𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ').toConvexSpaceBody)
          (fun w => (𝒰.cover.tube b w).toConvexSpaceBody)
          ((𝒰.cover.tube b j).rescale ρ').toConvexSpaceBody) :
    ENNReal.ofReal (((ρ : ℝ) / (gridScale δ N b : ℝ)) ^ ζ')
      ≤ D * (ENNReal.ofReal (2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
              * (((4 * ρ' : NNReal) : ℝ) / (gridScale δ N k : ℝ)) ^ (2 * Module.finrank ℝ E)
              * (Cu : ℝ))
            * ((Kn : ENNReal) * (Cb : ENNReal))
            * ENNReal.ofReal ((scaleGapVolConst (Module.finrank ℝ E) : ℝ)
                * ((ρ' : ℝ) / (ρ : ℝ)) ^ (Module.finrank ℝ E - 1)))
          * ConvexSpaceBody.frostmanConstant
              (𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody)
              (fun w => (𝒰.cover.tube b w).toConvexSpaceBody)
              ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody := by
  have hmono : ENNReal.ofReal (((ρ : ℝ) / (gridScale δ N b : ℝ)) ^ ζ') ≤
      ENNReal.ofReal (((ρ' : ℝ) / (gridScale δ N b : ℝ)) ^ ζ') :=
    ENNReal.ofReal_le_ofReal <| Real.rpow_le_rpow (by positivity)
      (div_le_div_of_nonneg_right (by exact_mod_cast hρρ')
        (le_of_lt (gridScale_pos hδ N b))) hζ'
  refine hmono.trans (hbound.trans ?_)
  rw [mul_assoc]
  exact mul_le_mul_right (frostmanConstant_nodesIn_rescale_le_of_pairBand hδ hδ1 𝒰 hs hkb hb hk
    h2δ hP hbandLo hbandHi hj hbρ hρ hρρ' hρ'4 hr) D

/-! ### The ancestor of a node inside a dilate -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
open scoped Classical in
/-- **The nodes under the level-`k` ancestor of `j` lie inside every `ρ`-dilate of `j` with
`4 ρ_k ≤ ρ`.**

The ancestor node contains `T_j`, hence lies in its `4ρ_k`-dilate, hence in its `ρ`-dilate. -/
theorem nodesUnder_nodeAncestor_subset_nodesIn_rescale {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T N Cu) (hs : s.Nonempty)
    {k b : ℕ} (hkb : k ≤ b) (hb : b ≤ N) {j : ι} (hj : j ∈ 𝒰.cover.indexSet b) {ρ : NNReal}
    (hρ : 4 * gridScale δ N k ≤ ρ) :
    𝒰.nodesUnder b k (𝒰.nodeAncestor b k j)
      ⊆ 𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody := by
  classical
  have hch : (𝒰.cover.tube k (𝒰.nodeAncestor b k j)).toConvexSpaceBody
      ≤ ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody :=
    (Tube.rescale_le_of_le (𝒰.cover.tube b j) _
        (𝒰.tube_le_tube_nodeAncestor hkb hb hs hj)).trans
      (Tube.rescale_le_rescale_of_radius_le (𝒰.cover.tube b j) hρ)
  simpa [UniformTubeSet.nodesUnder_eq_nodesIn] using nodesIn_subset_of_le 𝒰 b hch

/-! ### Splitting the left-hand side across two radii -/

/-- **The left-hand side of the third bullet factors across an intermediate radius.** -/
theorem A.div_rpow_split {r r' t : ℝ} (hr : 0 ≤ r) (hr' : 0 < r') (ht : 0 < t) {ζ : ℝ} :
    (r / t) ^ ζ = (r / r') ^ ζ * (r' / t) ^ ζ := by
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  field_simp

/-! ### The coarse end -/

open scoped Classical in
/-- **The third bullet at a scale above the reading range.**  At the coarse end of the `ε`-window
the bound is available only at a radius `ρ'` a bounded number of grid steps finer.  Ascending to `ρ`
is free: the nodes of the `ρ`-dilate are at most `Λ` times as many as those of the `ρ'`-dilate by
the ancestor split, and `leVolumeConst_mul_le_of_frostmanConstant_nodesIn` turns that into `C_F`. -/
theorem A.bulletThree_coarseEnd_of_ancestor {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {Cu : NNReal}
    (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cu) (hCu : 1 ≤ Cu) (hs : s.Nonempty)
    {k b : ℕ} (hk : k ≤ ssfGridLen δ) (hb : b ≤ ssfGridLen δ) (hkb : k ≤ b)
    (h2δ : 2 * δ ≤ gridScale δ (ssfGridLen δ) k)
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet b) {ρ ρ' : NNReal}
    (hbρ' : gridScale δ (ssfGridLen δ) b ≤ ρ')
    (hkρ' : 4 * gridScale δ (ssfGridLen δ) k ≤ ρ') (hρ'ρ : ρ' ≤ ρ)
    {Λ : NNReal}
    (hΛ : 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
        * (((4 * ρ : NNReal) : ℝ)
            / (gridScale δ (ssfGridLen δ) k : ℝ)) ^ (2 * Module.finrank ℝ E)
        * (Cu : ℝ) * ((Cu : ℝ) ^ 5) ≤ (Λ : ℝ))
    {ζ' : ℝ} {D L : ENNReal}
    (hL : ENNReal.ofReal (((ρ : ℝ) / (ρ' : ℝ)) ^ ζ') ≤ L)
    (hbound : ENNReal.ofReal (((ρ' : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ζ')
      ≤ D * ConvexSpaceBody.frostmanConstant
          (𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ').toConvexSpaceBody)
          (fun w => (𝒰.cover.tube b w).toConvexSpaceBody)
          ((𝒰.cover.tube b j).rescale ρ').toConvexSpaceBody) :
    ENNReal.ofReal (((ρ : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ζ')
      ≤ (((Tube.le_volume.c (Module.finrank ℝ E))⁻¹ : NNReal) : ENNReal)
          * (L * D * ((Tube.volume_le.C (Module.finrank ℝ E) * Λ : NNReal) : ENNReal))
          * ConvexSpaceBody.frostmanConstant
              (𝒰.nodesIn b ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody)
              (fun w => (𝒰.cover.tube b w).toConvexSpaceBody)
              ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody := by
  let K1 : ConvexSpaceBody E := ((𝒰.cover.tube b j).rescale ρ').toConvexSpaceBody
  let K2 : ConvexSpaceBody E := ((𝒰.cover.tube b j).rescale ρ).toConvexSpaceBody
  let CF1 : ENNReal := ConvexSpaceBody.frostmanConstant (𝒰.nodesIn b K1)
    (fun w => (𝒰.cover.tube b w).toConvexSpaceBody) K1
  have hρ'0 : 0 < ρ' :=
    lt_of_lt_of_le (mul_pos (by norm_num) (gridScale_pos hδ (ssfGridLen δ) k)) hkρ'
  have hρ'pos : (0 : ℝ) < (ρ' : ℝ) := NNReal.coe_pos.2 hρ'0
  have hρpos : (0 : ℝ) < (ρ : ℝ) := NNReal.coe_pos.2 (hρ'0.trans_le hρ'ρ)
  have hgb : (0 : ℝ) < (gridScale δ (ssfGridLen δ) b : ℝ) :=
    NNReal.coe_pos.2 (gridScale_pos hδ (ssfGridLen δ) b)
  have hX : ENNReal.ofReal (((ρ : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ζ')
      ≤ (L * D) * CF1 := by
    rw [MultiScaleFac.A.div_rpow_split (r := (ρ : ℝ)) (r' := (ρ' : ℝ))
        (t := (gridScale δ (ssfGridLen δ) b : ℝ)) hρpos.le hρ'pos hgb,
      ENNReal.ofReal_mul (Real.rpow_nonneg (div_pos hρpos hρ'pos).le ζ'), mul_assoc]
    exact mul_le_mul' hL hbound
  have hK : K1 ≤ K2 := Tube.rescale_le_rescale_of_radius_le (𝒰.cover.tube b j) hρ'ρ
  have hcard : ((𝒰.nodesIn b K2).card : ENNReal) ≤
      (Λ : ENNReal) * ((𝒰.nodesIn b K1).card : ENNReal) :=
    (card_nodesIn_rescale_le_of_ancestor hδ 𝒰 hCu hs hk hb hkb h2δ (hkρ'.trans hρ'ρ) hΛ
          (𝒰.nodeAncestor_mem hk hb hs hj)).trans
      (mul_le_mul' le_rfl (Nat.cast_le.2 (Finset.card_le_card
        (nodesUnder_nodeAncestor_subset_nodesIn_rescale 𝒰 hs hkb hb hj hkρ'))))
  have hne : (𝒰.nodesIn b K1).Nonempty :=
    ⟨j, (𝒰.mem_nodesIn_iff b K1 j).2 ⟨hj, Tube.le_rescale (𝒰.cover.tube b j) hbρ'⟩⟩
  rw [mul_assoc]
  exact le_of_leVolumeConst_mul_le
    (leVolumeConst_mul_le_of_frostmanConstant_nodesIn hδ hδ1 𝒰 (b := b) (K₁ := K1) (K₂ := K2)
      (hK := hK) (Λ := Λ) (hcard := hcard) (hne := hne) (D := L * D) (hX := hX))

/-! ### Clamping a scale of the wide window into the narrow one -/

/-- **Raising the window exponent shrinks the upper endpoint by at most one gap loss.**

The quantitative companion of `Kakeya.MultiScaleFac.window_upper_antitone`, and the mirror image of
`Kakeya.MultiScaleFac.window_endpoint_le_scaleGapLoss_mul`. -/
theorem window_upper_le_scaleGapLoss_mul {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1)
    (hM : 0 < ssfGridLen δ) {a b c : ℕ} {e e' : ℝ}
    (hc : (e' - e) * ((b : ℝ) - (a : ℝ)) ≤ (c : ℝ)) :
    (gridScale δ (ssfGridLen δ) a : ℝ)
        * ((gridScale δ (ssfGridLen δ) b : ℝ) / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e
      ≤ scaleGapLoss c δ
          * ((gridScale δ (ssfGridLen δ) a : ℝ)
              * ((gridScale δ (ssfGridLen δ) b : ℝ)
                  / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e') := by
  have hδ0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hM0 : (0 : ℝ) < (ssfGridLen δ : ℝ) := by exact_mod_cast hM
  rw [scaleGapLoss, gridScale_mul_ratio_rpow hδ (ssfGridLen δ) b a e,
    gridScale_mul_ratio_rpow hδ (ssfGridLen δ) b a e', ← Real.rpow_add hδ0,
    show -((c : ℝ) / (ssfGridLen δ : ℝ))
          + ((a : ℝ) - e' * ((a : ℝ) - (b : ℝ))) / (ssfGridLen δ : ℝ)
        = (((a : ℝ) - e' * ((a : ℝ) - (b : ℝ))) - (c : ℝ)) / (ssfGridLen δ : ℝ) by
      field_simp; ring]
  exact (rpow_div_le_rpow_div_iff hδ hδ1 hM _ _).2 (by linarith)

/-- **Every scale of the wide window is a bounded number of grid steps from the narrow window.**
The clamp `ρ' = min (max ρ L') U'` of `ρ` into the window of the larger exponent `e'` stays within a
single `Kakeya.MultiScaleFac.scaleGapLoss` of `ρ` in both directions, the two endpoint residuals
being `window_endpoint_le_scaleGapLoss_mul` and `window_upper_le_scaleGapLoss_mul`. -/
theorem A.exists_window_clamp {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1)
    (hM : 0 < ssfGridLen δ) {a b : ℕ} {e e' : ℝ} {c : ℕ}
    (hc : (e' - e) * ((b : ℝ) - (a : ℝ)) ≤ (c : ℝ))
    (hnarrow : (gridScale δ (ssfGridLen δ) b : ℝ)
          * ((gridScale δ (ssfGridLen δ) a : ℝ)
              / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e'
        ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
          * ((gridScale δ (ssfGridLen δ) b : ℝ)
              / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e')
    {ρ : NNReal}
    (hlo : (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e ≤ (ρ : ℝ))
    (hhi : (ρ : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
        * ((gridScale δ (ssfGridLen δ) b : ℝ)
            / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e) :
    ∃ ρ' : NNReal,
      (gridScale δ (ssfGridLen δ) b : ℝ)
          * ((gridScale δ (ssfGridLen δ) a : ℝ)
              / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e' ≤ (ρ' : ℝ) ∧
      (ρ' : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
          * ((gridScale δ (ssfGridLen δ) b : ℝ)
              / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e' ∧
      (ρ' : ℝ) ≤ scaleGapLoss c δ * (ρ : ℝ) ∧
      (ρ : ℝ) ≤ scaleGapLoss c δ * (ρ' : ℝ) := by
  set Lw : ℝ := (gridScale δ (ssfGridLen δ) b : ℝ)
      * ((gridScale δ (ssfGridLen δ) a : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e
  set Uw : ℝ := (gridScale δ (ssfGridLen δ) a : ℝ)
      * ((gridScale δ (ssfGridLen δ) b : ℝ) / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e
  set Ln : ℝ := (gridScale δ (ssfGridLen δ) b : ℝ)
      * ((gridScale δ (ssfGridLen δ) a : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e'
  set Un : ℝ := (gridScale δ (ssfGridLen δ) a : ℝ)
      * ((gridScale δ (ssfGridLen δ) b : ℝ) / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e'
  have hδnn : δ ≤ 1 := by exact_mod_cast hδ1.le
  have h1S : (1 : ℝ) ≤ scaleGapLoss c δ := one_le_scaleGapLoss c hδ hδnn
  have hS : (0 : ℝ) ≤ scaleGapLoss c δ := zero_le_one.trans h1S
  have hρ0 : (0 : ℝ) ≤ (ρ : ℝ) := ρ.coe_nonneg
  have hga : (0 : ℝ) < (gridScale δ (ssfGridLen δ) a : ℝ) := by
    exact_mod_cast gridScale_pos hδ (ssfGridLen δ) a
  have hgb : (0 : ℝ) < (gridScale δ (ssfGridLen δ) b : ℝ) := by
    exact_mod_cast gridScale_pos hδ (ssfGridLen δ) b
  have hUn0 : (0 : ℝ) ≤ Un :=
    (mul_pos hga (Real.rpow_pos_of_pos (div_pos hgb hga) e')).le
  have hmin0 : (0 : ℝ) ≤ min (max (ρ : ℝ) Ln) Un :=
    le_min (hρ0.trans (le_max_left _ _)) hUn0
  refine ⟨Real.toNNReal (min (max (ρ : ℝ) Ln) Un), ?_, ?_, ?_, ?_⟩ <;>
    rw [Real.coe_toNNReal _ hmin0]
  · exact le_min (le_max_right _ _) hnarrow
  · exact min_le_right _ _
  · refine (min_le_left _ _).trans (max_le (le_mul_of_one_le_left hρ0 h1S) ?_)
    exact (window_endpoint_le_scaleGapLoss_mul hδ hδ1 hM hc).trans
      (mul_le_mul_of_nonneg_left hlo hS)
  · rcases le_total (ρ : ℝ) Un with h | h
    · exact (le_min (le_max_left _ _) h).trans (le_mul_of_one_le_left hmin0 h1S)
    · rw [min_eq_right (h.trans (le_max_left _ _))]
      exact hhi.trans (window_upper_le_scaleGapLoss_mul hδ hδ1 hM hc)

/-! ### Real bounds read against a ceiling -/

/-- **A real upper bound may be read against the ceiling of the bounding value.**

The one place where the window arithmetic leaves `ℝ` for `ℕ`: the gap budget `c` of
`Kakeya.MultiScaleFac.A.exists_window_clamp` is a natural number, while the estimate that produces
it is an inequality between reals. -/
theorem A.le_cast_ceil {x y : ℝ} (h : x ≤ y) : x ≤ (⌈y⌉₊ : ℝ) := h.trans (Nat.le_ceil y)

/-! ### The packing count of the sharply rounded ancestor split -/

/-- **The packing count of the ancestor split at a sharply rounded index is a gap loss.**
`Kakeya.MultiScaleFac.A.exists_round_index_sharp` keeps the rounded scale `σ_c` within a single grid
step of `ρ/32`, so `4ρ/σ_c ≤ 128 · scaleGapLoss 1 δ`; raising this to the dimensional power `2n`
gives `Kakeya.MultiScaleFac.scaleGapLoss (2n) δ` up to the absolute constant `128^{2n}`. -/
theorem A.lambda_le_scaleGapLoss {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {c : ℕ} {ρ : NNReal}
    (hρ : (ρ : ℝ) ≤ 32 * scaleGapLoss 1 δ * (gridScale δ (ssfGridLen δ) c : ℝ))
    (Cu : NNReal) (n : ℕ) :
    2 * (25 : ℝ) ^ (2 * n)
        * (((4 * ρ : NNReal) : ℝ) / (gridScale δ (ssfGridLen δ) c : ℝ)) ^ (2 * n)
        * (Cu : ℝ) * ((Cu : ℝ) ^ 5)
      ≤ 2 * (25 : ℝ) ^ (2 * n) * (128 : ℝ) ^ (2 * n) * ((Cu : ℝ) ^ 6)
          * scaleGapLoss (2 * n) δ := by
  have hsc : (0 : ℝ) < (gridScale δ (ssfGridLen δ) c : ℝ) := by
    exact_mod_cast gridScale_pos hδ (ssfGridLen δ) c
  have hS1 : (1 : ℝ) ≤ (scaleGapLoss 1 δ : ℝ) := by
    exact_mod_cast one_le_scaleGapLoss 1 hδ hδ1
  have hSpow : ((scaleGapLoss 1 δ : ℝ)) ^ (2 * n) = (scaleGapLoss (2 * n) δ : ℝ) := by
    have hp := MultiScaleFac.A.scaleGapLoss_pow hδ 1 (2 * n)
    rw [one_mul] at hp
    exact_mod_cast hp
  have hpow : (((4 * ρ : NNReal) : ℝ) / (gridScale δ (ssfGridLen δ) c : ℝ)) ^ (2 * n)
      ≤ (128 : ℝ) ^ (2 * n) * (scaleGapLoss (2 * n) δ : ℝ) := by
    rw [← hSpow, ← mul_pow]
    refine pow_le_pow_left₀ (div_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)) ?_ (2 * n)
    rw [div_le_iff₀ hsc]
    push_cast
    linarith [hS1]
  calc
    2 * (25 : ℝ) ^ (2 * n)
          * (((4 * ρ : NNReal) : ℝ) / (gridScale δ (ssfGridLen δ) c : ℝ)) ^ (2 * n)
          * (Cu : ℝ) * ((Cu : ℝ) ^ 5)
        = (((4 * ρ : NNReal) : ℝ) / (gridScale δ (ssfGridLen δ) c : ℝ)) ^ (2 * n)
          * (2 * (25 : ℝ) ^ (2 * n) * (Cu : ℝ) ^ 6) := by ring
    _ ≤ ((128 : ℝ) ^ (2 * n) * (scaleGapLoss (2 * n) δ : ℝ))
          * (2 * (25 : ℝ) ^ (2 * n) * (Cu : ℝ) ^ 6) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = 2 * (25 : ℝ) ^ (2 * n) * (128 : ℝ) ^ (2 * n) * ((Cu : ℝ) ^ 6)
          * scaleGapLoss (2 * n) δ := by ring

/-! ### Nonemptiness of the narrow window -/

/-- **On a long block the narrow window is nonempty.**  The hypothesis `hnarrow` of
`Kakeya.MultiScaleFac.A.exists_window_clamp`.  Both endpoints are powers of `δ`, and the lower one
is the smaller exactly when `2e'(b - a) ≤ b - a`; a long block has `a < b`, so the condition reduces
to `2e' ≤ 1`, which the window exponent `e' = (1 + 2κ)ε` meets with room to spare. -/
theorem A.narrow_window_nonempty {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) < 1)
    (hM : 0 < ssfGridLen δ) {ε : ℝ} {a b : ℕ}
    (hlong : IsLongBlock (ssfGridLen δ) ε a b) {e' : ℝ} (he' : 2 * e' ≤ 1) :
    (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ e'
      ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
        * ((gridScale δ (ssfGridLen δ) b : ℝ)
            / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ e' := by
  have hab : (a : ℝ) ≤ (b : ℝ) := by
    have hl : ⌈ε * (ssfGridLen δ : ℝ)⌉₊ + a < b := by simpa [IsLongBlock] using hlong
    exact_mod_cast (by omega : a ≤ b)
  rw [gridScale_mul_ratio_rpow hδ (ssfGridLen δ) b a e',
    gridScale_mul_ratio_rpow hδ (ssfGridLen δ) a b e']
  exact (rpow_div_le_rpow_div_iff hδ hδ1 hM _ _).2
    (by linarith [mul_nonneg (sub_nonneg.2 hab) (by linarith : (0 : ℝ) ≤ 1 - 2 * e')])

end MultiScaleFac
end Kakeya

end
