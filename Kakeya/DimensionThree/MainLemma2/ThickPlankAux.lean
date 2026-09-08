/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThinConfig
public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.Thickness.Volume

/-!
# Auxiliary lemmas for the Section 6 plank interface of the thick case

The reusable pieces of `Kakeya/DimensionThree/MainLemma2/ThickPlankInterface.lean`, kept here so
that the interface file carries only the four Section 6 statements and their assembly. Nothing
in this file is specific to the thick case except `Kakeya.VeryNotSticky.volume_segs_carrier_pos`,
which reads the thickness data (C3) of `Kakeya.VeryNotSticky.BallData`.

Three groups:

* **scale facts of the configuration** — `Kakeya.VeryNotSticky.cfg_a_pos`,
  `Kakeya.VeryNotSticky.cfg_b_pos`, `Kakeya.VeryNotSticky.cfg_b_le_one` and
  `Kakeya.VeryNotSticky.cfg_a_le_one`, the positivity and the unit bounds of the working
  factoring dimensions, read off the field `Kakeya.VeryNotSticky.hdims`;
* **the non-concentration parameter** of blueprint `lem:ml2thickMbound` — that
  `M = Θ C_bias (δ/a)^{2+ϱ}|𝒫|` is at least `1` and finite
  (`Kakeya.VeryNotSticky.one_le_thickM`, `Kakeya.VeryNotSticky.thickM_ne_top`), which is what
  blueprint `plankF` requires of it, together with the lower bound on `M⁻¹(b')²|𝒫|` that the
  assembly uses (`Kakeya.VeryNotSticky.thickM_lower`,
  `Kakeya.VeryNotSticky.rpow_thickM_lower`) and the `ℝ≥0` form of the fibre bound that the
  Section 6 signature wants (`Kakeya.VeryNotSticky.card_le_toNNReal_mul`);
* **the factor bounds of blueprint `lem:ml2thickPlankF`** — the `[0, ∞]` arithmetic that turns
  the conclusion of `plankF` at the plank scales into
  `Kakeya.VeryNotSticky.DenseInBodyRaw` at the block, and which
  `Kakeya.VeryNotSticky.denseInBodyRaw_of_thickPlankPresentation` is assembled from. Its
  terminal statements are `Kakeya.VeryNotSticky.thickPlankF_product_lower`,
  `Kakeya.VeryNotSticky.thickPlankF_conclude` and
  `Kakeya.VeryNotSticky.exists_denseConst_of_plankF`, the last of which splits the produced
  constant into the two `ℝ≥0` factors the interface returns
  (`Kakeya.VeryNotSticky.exists_nnreal_const_of_le`).

There is no Frostman-window group. An earlier version carried one, converting an
`ConvexSpaceBody.IsFrostmanIn` estimate from `ConvexSpaceBody.closedUnitBall` to
`Kakeya.plankWindow = B̄(0, 4)` at the cost of the volume ratio `4³ = 64`. It is gone:
`Kakeya.VeryNotSticky.PlankFrostmanVolumeAt` is now stated in the plank window directly, so no
`ConvexSpaceBody.IsFrostmanIn.change_ambient` step arises and the conversion had no call site.
The factor `64` it used to pay for survives in that predicate as pure slack; see the docstring
of `Kakeya.VeryNotSticky.plankFrostmanVolume`.

`Kakeya.VeryNotSticky.volume_segs_carrier_pos`, the positivity of the carrier volume of a
segment of (C3), sits with the first group and is the one declaration here that reads
`Kakeya.VeryNotSticky.BallData`.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric ShadedBody

universe u

/-! ### Positivity of the carrier volume of a segment -/

/-- **A tube segment of (C3) has positive carrier volume.**

The thickness data `Kakeya.VeryNotSticky.BallData.segs_thickness` bounds each of the three affine
thicknesses of `T_B` below by `C₀⁻¹` times an entry of `(r₁, δ, δ)`, all three of which are
positive; `Convex.volume_pos_of_ethickness_ne_zero` turns that into `0 < |T_B|`.

This is `Kakeya.VeryNotSticky.thickSegVolRatio` shorn of its quantitative content. It is stated
separately because that lemma lives in `Kakeya/DimensionThree/MainLemma2/ThickCase.lean`, which
is downstream of the plank interface. -/
theorem volume_segs_carrier_pos {cfg : VeryNotSticky.{u}} (bd : BallData cfg) {B : bd.bι}
    (hB : B ∈ bd.bs) {p : bd.σ} (hp : p ∈ bd.segs B) :
    0 < volume (bd.Y p).carrier := by
  have hthickp : HasThicknesses (bd.Y p).carrier bd.C₀
      ![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] :=
    bd.segs_thickness B hB p hp
  have hconv : Convex ℝ (bd.Y p).carrier := (bd.Y p).convex
  have hbdd : Bornology.IsBounded (bd.Y p).carrier := (bd.Y p).isCompact.isBounded
  have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hδpos : (0 : ℝ) < (cfg.δ : ℝ) := by exact_mod_cast cfg.hδ
  have hr₁pos : 0 < (cfg.r₁ : ℝ) := by
    have hδrpow : 0 < (cfg.δ : ℝ) ^ cfg.exscal :=
      Real.rpow_pos_of_pos (by exact_mod_cast cfg.hδ) cfg.exscal
    simpa [r₁] using hδrpow
  have hC₀pos : 0 < (bd.C₀ : ℝ) := by
    have hC₀_one : (1 : ℝ) ≤ (bd.C₀ : ℝ) := by exact_mod_cast bd.hC₀
    linarith
  have hthick_ne_zero : ∀ i ∈ Finset.range (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))),
      Metric.ethickness ℝ (bd.Y p).carrier i ≠ 0 := by
    intro i hi
    rw [Finset.mem_range, hfinrank] at hi
    let k : Fin 3 := ⟨i, hi⟩
    rcases hthickp k with ⟨hle, _⟩
    have h_val_pos : 0 < (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] k) := by
      match k with
      | 0 => simp [hr₁pos]
      | 1 => simp [hδpos]
      | 2 => simp [hδpos]
    have hle' : ((bd.C₀ : ℝ)⁻¹ * (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] k : ℝ)) ≤
        Metric.thickness ℝ (bd.Y p).carrier (k : ℕ) := by
      simpa using hle
    have hprodpos : 0 < (bd.C₀ : ℝ)⁻¹ * (![(cfg.r₁ : ℝ), (cfg.δ : ℝ), (cfg.δ : ℝ)] k) :=
      mul_pos (inv_pos.mpr hC₀pos) h_val_pos
    have hpos : 0 < Metric.thickness ℝ (bd.Y p).carrier (k : ℕ) := by linarith
    rw [Metric.ethickness_thickness' hbdd k.val]
    rw [ENNReal.ofReal_ne_zero_iff]
    simpa [k] using hpos
  exact hconv.volume_pos_of_ethickness_ne_zero hthick_ne_zero

/-! ### Scale facts of the configuration

The three inequalities between the working scales that the thick-case plank assembly needs and
that Configuration `hyp:ml2setup` gives immediately, through the field
`Kakeya.VeryNotSticky.hdims`, `δ ≤ a ≤ b ≤ r₁ = δ^{exscal}`. -/

/-- `0 < a`: the smallest working factoring dimension is at least `δ > 0`. -/
theorem cfg_a_pos (cfg : VeryNotSticky.{u}) : 0 < cfg.a := by
  exact lt_of_lt_of_le cfg.hδ cfg.hdims.1

/-- `0 < b`: the middle working factoring dimension is at least `a > 0`. -/
theorem cfg_b_pos (cfg : VeryNotSticky.{u}) : 0 < cfg.b := by
  exact lt_of_lt_of_le (lt_of_lt_of_le cfg.hδ cfg.hdims.1) cfg.hdims.2.1

/-- `b ≤ 1`: the middle working factoring dimension is at most `r₁ = δ^{exscal} ≤ 1`, since
`δ ≤ 1` and `exscal > 0`. This is what makes the step `δ/b ≥ δ` of blueprint
`lem:ml2thickPlankF` — `Kakeya.VeryNotSticky.self_le_div_of_le_one` — available. -/
theorem cfg_b_le_one (cfg : VeryNotSticky.{u}) : cfg.b ≤ 1 := by
  exact le_trans cfg.hdims.2.2 (NNReal.rpow_le_one cfg.hδ1 cfg.hexscal.le)

/-- `a ≤ 1`: the short working factoring dimension is at most `b ≤ 1`.

This is the upper half of the radius hypothesis `a ≤ r ≤ 1` of blueprint `lem:ml2aScaleData`
at the radius `r = cfg.a`, which is where the thick branch invokes the scale-`r` interface
`Kakeya.VeryNotSticky.exists_aScaleData`; without it that interface is refutable, so this is
not decoration. -/
theorem cfg_a_le_one (cfg : VeryNotSticky.{u}) : cfg.a ≤ 1 := by
  exact le_trans cfg.hdims.2.1 (cfg_b_le_one cfg)

/-! ### The non-concentration parameter of blueprint `lem:ml2thickMbound`

Blueprint `plankF` demands `1 ≤ M < ∞` of the parameter it is applied at, and the thick case
supplies `M = Θ C_bias (δ/a)^{2+ϱ}|𝒫|`. Both conditions are `[0, ∞]`-arithmetic; no geometry
enters. -/

/-- **The non-concentration parameter is at least `1`** (blueprint `lem:ml2thickPcard`, in the
form blueprint `plankF` consumes).

The cardinality bound `(a/δ)^{2+ϱ} ≤ |𝒫|` of blueprint `lem:ml2thickPcard` is exactly what
cancels the factor `(δ/a)^{2+ϱ}`, the two being mutually inverse; the remaining factors
`Θ` and `C_bias` are at least `1`. -/
theorem one_le_thickM {Θ Cb d na N : ENNReal} (hΘ1 : 1 ≤ Θ) (hCb1 : 1 ≤ Cb)
    (hd0 : d ≠ 0) (hdtop : d ≠ ⊤) (hna0 : na ≠ 0) (hnatop : na ≠ ⊤) {ϱ : ℝ}
    (hN : (na / d) ^ (2 + ϱ) ≤ N) :
    1 ≤ Θ * Cb * (d / na) ^ (2 + ϱ) * N := by
  have hq0 : d / na ≠ 0 := ENNReal.div_ne_zero.2 ⟨hd0, hnatop⟩
  have hqtop : d / na ≠ ⊤ := ENNReal.div_ne_top hdtop hna0
  have hqinv : (d / na)⁻¹ = na / d :=
    ENNReal.inv_div (Or.inl hnatop) (Or.inl hna0)
  have hpow0 : (d / na) ^ (2 + ϱ) ≠ 0 := by
    intro h
    rw [ENNReal.rpow_eq_zero_iff] at h
    simp [hq0, hqtop] at h
  have hpowtop : (d / na) ^ (2 + ϱ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hq0 hqtop
  have hprod : (d / na) ^ (2 + ϱ) * (na / d) ^ (2 + ϱ) = 1 := by
    calc
      (d / na) ^ (2 + ϱ) * (na / d) ^ (2 + ϱ)
          = (d / na) ^ (2 + ϱ) * ((d / na) ^ (2 + ϱ))⁻¹ := by
            rw [← hqinv, ENNReal.inv_rpow]
      _ = 1 := by
            exact ENNReal.mul_inv_cancel hpow0 hpowtop
  have h1 : (1 : ENNReal) ≤ (d / na) ^ (2 + ϱ) * N := by
    calc
      (1 : ENNReal) = (d / na) ^ (2 + ϱ) * (na / d) ^ (2 + ϱ) := by rw [hprod]
      _ ≤ (d / na) ^ (2 + ϱ) * N := by
        gcongr
  have hΘCb : (1 : ENNReal) ≤ Θ * Cb := one_le_mul hΘ1 hCb1
  calc
    (1 : ENNReal) ≤ (Θ * Cb) * ((d / na) ^ (2 + ϱ) * N) := one_le_mul hΘCb h1
    _ = Θ * Cb * (d / na) ^ (2 + ϱ) * N := by
      ring

/-- **The non-concentration parameter is finite**, which blueprint `plankF` also demands: each
of its four factors is, the middle one because `d / na` lies in `(0, ∞)`. -/
theorem thickM_ne_top {Θ Cb d na N : ENNReal} (hΘtop : Θ ≠ ⊤) (hCbtop : Cb ≠ ⊤)
    (hd0 : d ≠ 0) (hdtop : d ≠ ⊤) (hna0 : na ≠ 0) (hnatop : na ≠ ⊤) (hNtop : N ≠ ⊤) {ϱ : ℝ} :
    Θ * Cb * (d / na) ^ (2 + ϱ) * N ≠ ⊤ := by
  have hq0 : d / na ≠ 0 := ENNReal.div_ne_zero.2 ⟨hd0, hnatop⟩
  have hqtop : d / na ≠ ⊤ := ENNReal.div_ne_top hdtop hna0
  have hpow : (d / na) ^ (2 + ϱ) ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hq0 hqtop
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hΘtop hCbtop) hpow) hNtop

/-- **Splitting the constant of `Kakeya.VeryNotSticky.thickPlankF_conclude` into two `ℝ≥0`
factors, each at least `1`.**

`Kakeya.VeryNotSticky.DenseInBodyRaw` carries its constant as a product `Θ' C₁'` of two `ℝ≥0`
numbers bounded below by `1`, whereas `thickPlankF_conclude` delivers the `[0, ∞]`-valued
constant `64 |B₁| CP^{ν+3β} (Θ C_bias)(CP C_bias)`. The split used is
`Θ' = Θ C_bias²` — the whole bias contribution, which is the one `δ`-dependent factor — and
`C₁' = max 1 (64 |B₁| CP^{ν+3β} CP)` — the `δ`-free geometric contribution. The `max` is what
supplies `1 ≤ C₁'` without a numerical lower bound for `|B₁|`; it costs nothing, the
hypothesis being an upper bound on `X`. -/
theorem exists_nnreal_const_of_le {CP Θ Cb : NNReal} (hCP : 1 ≤ CP) (hΘ : 1 ≤ Θ) (hCb : 1 ≤ Cb)
    {ν β : ℝ} {X Y B1 : ENNReal} (hB1 : B1 ≠ ⊤)
    (h : X ≤ 64 * B1 * (CP : ENNReal) ^ (ν + 3 * β) * ((Θ : ENNReal) * (Cb : ENNReal)) *
        ((CP : ENNReal) * (Cb : ENNReal)) * Y) :
    ∃ Θ' C₁' : NNReal, 1 ≤ Θ' ∧ 1 ≤ C₁' ∧ X ≤ (Θ' : ENNReal) * (C₁' : ENNReal) * Y := by
  have hCP0 : CP ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hCP)
  have hC : (64 : ENNReal) * B1 * (CP : ENNReal) ^ (ν + 3 * β) * (CP : ENNReal) ≤
      ((max 1 (64 * B1.toNNReal * CP ^ (ν + 3 * β) * CP) : NNReal) : ENNReal) := by
    calc
      (64 : ENNReal) * B1 * (CP : ENNReal) ^ (ν + 3 * β) * (CP : ENNReal)
          = ((64 * B1.toNNReal * CP ^ (ν + 3 * β) * CP : NNReal) : ENNReal) := by
            simp [ENNReal.coe_rpow_of_ne_zero hCP0, hB1]
      _ ≤ ((max 1 (64 * B1.toNNReal * CP ^ (ν + 3 * β) * CP) : NNReal) : ENNReal) := by
            exact ENNReal.coe_le_coe.2 (le_max_right _ _)
  refine ⟨Θ * Cb * Cb, max 1 (64 * B1.toNNReal * CP ^ (ν + 3 * β) * CP),
    one_le_mul (one_le_mul hΘ hCb) hCb,
    le_max_left _ _, h.trans ?_⟩
  calc
    64 * B1 * (CP : ENNReal) ^ (ν + 3 * β) * ((Θ : ENNReal) * (Cb : ENNReal)) *
        ((CP : ENNReal) * (Cb : ENNReal)) * Y
        = (Θ : ENNReal) * (Cb : ENNReal) * (Cb : ENNReal) *
            ((64 : ENNReal) * B1 * (CP : ENNReal) ^ (ν + 3 * β) * (CP : ENNReal)) * Y := by
          ring
    _ ≤ (Θ : ENNReal) * (Cb : ENNReal) * (Cb : ENNReal) *
        (((max 1 (64 * B1.toNNReal * CP ^ (ν + 3 * β) * CP) : NNReal) : ENNReal)) * Y := by
          gcongr
    _ = ((Θ * Cb * Cb : NNReal) : ENNReal) *
        (((max 1 (64 * B1.toNNReal * CP ^ (ν + 3 * β) * CP) : NNReal) : ENNReal)) * Y := by
          rw [← ENNReal.coe_mul, ← ENNReal.coe_mul]

/-! ### Transporting the non-concentration parameter -/

/-- **The non-concentration bound, transported from `[0, ∞]` to `ℝ≥0`.**

`Kakeya.VeryNotSticky.PlankFrostmanVolumeAt` states the fibre bound
`|{j : P_j ⊆ (P_i)_θ}| ≤ M θ` with `M : ENNReal`, because that is the shape the thick case
produces it in — the parameter is `Θ (δ/a)^{2+ϱ}|𝒫|`, a product of `[0, ∞]`-valued quantities.
The Section 6 statement `Kakeya.FrostmanEstimate.plankEstimate` states it with `M : ℝ≥0`. Under
`M ≠ ⊤` the two agree. -/
theorem card_le_toNNReal_mul {n : ℕ} {M : ENNReal} (hMtop : M ≠ ⊤) {θ : NNReal}
    (h : (n : ENNReal) ≤ M * (θ : ENNReal)) : (n : NNReal) ≤ M.toNNReal * θ := by
  rw [← ENNReal.coe_le_coe]
  simpa [ENNReal.coe_toNNReal hMtop] using h

/-! ### The factor bounds of blueprint `lem:ml2thickPlankF`

Blueprint `lem:ml2thickPlankF` reads the conclusion of `plankF` at the plank scales
`a' ∼ δ/b`, `b' ∼ δ/a` and at `M = Θ (δ/a)^{2+ϱ}|𝒫|`, and bounds each of its four factors
below by a `δ`-free constant times a power of the working scales. The four bounds are
`rpow_mul_le_rpow_of_inv_mul_le` (twice, for `a'^ν` and for `(b')^{2β}`),
`inv_le_rpow_of_neg_one_le` (for `C_F^{β/2-1}` and for `Θ^{-β/2}`) and `thickM_lower`
together with `rpow_thickM_lower` (for `(M^{-1}(b')²|𝒫|)^{β/2}`).

All of them are statements about `[0, ∞]` alone; no geometry enters. -/

/-- **`C⁻¹ ≤ C^e` for `C ≥ 1` and `e ≥ -1`.**

Used three times in blueprint `lem:ml2thickPlankF`: for `C_F^{β/2-1} ≥ C_F⁻¹` (the exponent is
`≥ -1` because `β > 0`), for `Θ^{-β/2} ≥ Θ⁻¹` (because `β ≤ 2`), and for the analogous step on
the comparison constant `C_{lem:ml2thickPlank}`. -/
theorem inv_le_rpow_of_neg_one_le {C : ENNReal} (hC : 1 ≤ C) {e : ℝ} (he : -1 ≤ e) :
    C⁻¹ ≤ C ^ e := by
  rw [← ENNReal.rpow_neg_one]
  exact ENNReal.rpow_le_rpow_of_exponent_le hC he

/-- **Raising a division-free lower bound to a nonnegative power.**

The form in which the comparabilities `a' ≥ CP⁻¹ δ/b` and `b' ≥ CP⁻¹ δ/a` of
`Kakeya.VeryNotSticky.ThickPlankPresentation` are used: the constant comes out as an explicit
negative power of `CP`, which blueprint `lem:ml2thickPlankF` absorbs into the constant it
produces. -/
theorem rpow_mul_le_rpow_of_inv_mul_le {CP x y : ENNReal} (_hCP0 : CP ≠ 0) (_hCPtop : CP ≠ ⊤)
    (h : CP⁻¹ * x ≤ y) {r : ℝ} (hr : 0 ≤ r) :
    CP ^ (-r) * x ^ r ≤ y ^ r := by
  calc
    CP ^ (-r) * x ^ r
        = (CP⁻¹) ^ r * x ^ r := by rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg]
    _ = (CP⁻¹ * x) ^ r := (ENNReal.mul_rpow_of_nonneg _ _ hr).symm
    _ ≤ y ^ r := ENNReal.rpow_le_rpow h hr

/-- **Dividing by something at most `1` only increases.**

The step `δ/b ≥ δ` behind the first comparability of blueprint `lem:ml2thickPlank`(i): the
middle working scale satisfies `b ≤ r₁ ≤ 1`, so the short plank dimension `a' ∼ δ/b` is at
least `CP⁻¹ δ`. -/
theorem self_le_div_of_le_one {d nb : ENNReal} (hnb0 : nb ≠ 0) (hnb1 : nb ≤ 1) :
    d ≤ d / nb := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl hnb0)
    (Or.inl (ne_top_of_le_ne_top ENNReal.one_ne_top hnb1))]
  exact mul_le_of_le_one_right' hnb1

/-- **The non-concentration factor of blueprint `lem:ml2thickMbound`, bounded below.**

At `M = Θ (δ/a)^{2+ϱ}|𝒫|` and `b' ≥ CP⁻¹ δ/a`, the quantity `M^{-1}(b')²|𝒫|` that blueprint
`plankF` raises to the power `β/2` is at least `CP^{-2} Θ^{-1} (a/δ)^{ϱ}`: the cardinality
cancels, two of the `2 + ϱ` powers of `δ/a` are eaten by `(b')²`, and the surviving `(δ/a)^{-ϱ}`
is the thick-case surplus. -/
theorem thickM_lower {CP d na Θ N b' : ENNReal} (hCP0 : CP ≠ 0) (hCPtop : CP ≠ ⊤)
    (hΘ0 : Θ ≠ 0) (hΘtop : Θ ≠ ⊤) (hN0 : N ≠ 0) (hNtop : N ≠ ⊤)
    (hd0 : d ≠ 0) (hdtop : d ≠ ⊤) (hna0 : na ≠ 0) (hnatop : na ≠ ⊤)
    (hb' : CP⁻¹ * (d / na) ≤ b') {ϱ : ℝ} :
    CP ^ (-2 : ℝ) * Θ⁻¹ * (na / d) ^ ϱ ≤
      (Θ * (d / na) ^ (2 + ϱ) * N)⁻¹ * b' ^ (2 : ℝ) * N := by
  let q : ENNReal := d / na
  have hq : q = d / na := rfl
  have hq0 : q ≠ 0 := by
    rw [hq]
    exact ENNReal.div_ne_zero.2 ⟨hd0, hnatop⟩
  have hqtop : q ≠ ⊤ := by
    rw [hq]
    exact ENNReal.div_ne_top hdtop hna0
  have hbpow : CP ^ (-2 : ℝ) * q ^ (2 : ℝ) ≤ b' ^ (2 : ℝ) :=
    rpow_mul_le_rpow_of_inv_mul_le (CP := CP) (x := q) (y := b') hCP0 hCPtop
      (by simpa [q] using hb') (r := (2 : ℝ)) (by norm_num)
  have hqinv : q⁻¹ = na / d := by
    rw [hq]
    exact ENNReal.inv_div (Or.inl hnatop) (Or.inl hna0)
  have hqneg : q ^ (-ϱ) = (na / d) ^ ϱ := by
    calc
      q ^ (-ϱ) = (q ^ ϱ)⁻¹ := by rw [ENNReal.rpow_neg]
      _ = (q⁻¹) ^ ϱ := by rw [ENNReal.inv_rpow]
      _ = (na / d) ^ ϱ := by rw [hqinv]
  have hqcomb : q ^ (-(2 + ϱ)) * q ^ (2 : ℝ) = q ^ (-ϱ) := by
    rw [← ENNReal.rpow_add (-(2 + ϱ)) (2 : ℝ) hq0 hqtop]
    congr 1
    ring
  calc
    (Θ * (d / na) ^ (2 + ϱ) * N)⁻¹ * b' ^ (2 : ℝ) * N
        = (Θ * q ^ (2 + ϱ) * N)⁻¹ * b' ^ (2 : ℝ) * N := by rw [← hq]
    _ = Θ⁻¹ * q ^ (-(2 + ϱ)) * N⁻¹ * b' ^ (2 : ℝ) * N := by
        rw [ENNReal.mul_inv (Or.inr hNtop) (Or.inr hN0)]
        rw [ENNReal.mul_inv (Or.inl hΘ0) (Or.inl hΘtop)]
        rw [← ENNReal.rpow_neg]
    _ ≥ Θ⁻¹ * q ^ (-(2 + ϱ)) * N⁻¹ * (CP ^ (-2 : ℝ) * q ^ (2 : ℝ)) * N := by
        gcongr
    _ = CP ^ (-2 : ℝ) * Θ⁻¹ * q ^ (-ϱ) := by
        calc
          Θ⁻¹ * q ^ (-(2 + ϱ)) * N⁻¹ * (CP ^ (-2 : ℝ) * q ^ (2 : ℝ)) * N
              = CP ^ (-2 : ℝ) * Θ⁻¹ * (q ^ (-(2 + ϱ)) * q ^ (2 : ℝ)) * (N⁻¹ * N) := by
                ring
          _ = CP ^ (-2 : ℝ) * Θ⁻¹ * q ^ (-ϱ) * (N⁻¹ * N) := by
                rw [hqcomb]
          _ = CP ^ (-2 : ℝ) * Θ⁻¹ * q ^ (-ϱ) * 1 := by
                rw [ENNReal.inv_mul_cancel hN0 hNtop]
          _ = CP ^ (-2 : ℝ) * Θ⁻¹ * q ^ (-ϱ) := by
                rw [mul_one]
    _ = CP ^ (-2 : ℝ) * Θ⁻¹ * (na / d) ^ ϱ := by
        rw [hqneg]

/-- **The `β/2`-th power of `Kakeya.VeryNotSticky.thickM_lower`, with the constants split off.**

`(CP^{-2} Θ^{-1} (a/δ)^{ϱ})^{β/2} = CP^{-β} Θ^{-β/2} (a/δ)^{ϱβ/2}`, and `Θ^{-β/2} ≥ Θ^{-1}`
since `Θ ≥ 1` and `β ≤ 2`. This is the step that produces the whole thick-case surplus
`(a/δ)^{ϱβ/2}` of `Kakeya.VeryNotSticky.DenseInBodyRaw`. -/
theorem rpow_thickM_lower {CP Θ d na : ENNReal} (_hCP0 : CP ≠ 0) (_hCPtop : CP ≠ ⊤)
    (hΘ1 : 1 ≤ Θ) (_hΘtop : Θ ≠ ⊤) {β ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    CP ^ (-β) * Θ⁻¹ * (na / d) ^ (ϱ * β / 2) ≤
      (CP ^ (-2 : ℝ) * Θ⁻¹ * (na / d) ^ ϱ) ^ (β / 2) := by
  have hb2 : 0 ≤ β / 2 := div_nonneg (le_of_lt hβ0) (by norm_num)
  have he : -1 ≤ -(β / 2) := by nlinarith
  have hRHS : (CP ^ (-2 : ℝ) * Θ⁻¹ * (na / d) ^ ϱ) ^ (β / 2) =
      CP ^ (-β : ℝ) * Θ ^ (-(β / 2)) * (na / d) ^ (ϱ * β / 2) := by
    have hexp1 : (-2 : ℝ) * (β / 2) = -β := by ring
    have hexp2 : ϱ * (β / 2) = ϱ * β / 2 := by ring
    calc
      (CP ^ (-2 : ℝ) * Θ⁻¹ * (na / d) ^ ϱ) ^ (β / 2)
          = (CP ^ (-2 : ℝ) * Θ⁻¹) ^ (β / 2) * ((na / d) ^ ϱ) ^ (β / 2) := by
            rw [ENNReal.mul_rpow_of_nonneg (CP ^ (-2 : ℝ) * Θ⁻¹) ((na / d) ^ ϱ) hb2]
      _ = (CP ^ (-2 : ℝ)) ^ (β / 2) * (Θ⁻¹) ^ (β / 2) * ((na / d) ^ ϱ) ^ (β / 2) := by
            rw [ENNReal.mul_rpow_of_nonneg (CP ^ (-2 : ℝ)) (Θ⁻¹) hb2]
      _ = CP ^ (-β) * (Θ⁻¹) ^ (β / 2) * ((na / d) ^ ϱ) ^ (β / 2) := by
            rw [← ENNReal.rpow_mul CP (-2) (β / 2), hexp1]
      _ = CP ^ (-β) * (Θ ^ (β / 2))⁻¹ * ((na / d) ^ ϱ) ^ (β / 2) := by
            rw [ENNReal.inv_rpow]
      _ = CP ^ (-β) * Θ ^ (-(β / 2)) * ((na / d) ^ ϱ) ^ (β / 2) := by
            rw [← ENNReal.rpow_neg Θ (β / 2)]
      _ = CP ^ (-β) * Θ ^ (-(β / 2)) * (na / d) ^ (ϱ * β / 2) := by
            rw [← ENNReal.rpow_mul (na / d) ϱ (β / 2), hexp2]
  calc
    CP ^ (-β) * Θ⁻¹ * (na / d) ^ (ϱ * β / 2)
        ≤ CP ^ (-β) * Θ ^ (-(β / 2)) * (na / d) ^ (ϱ * β / 2) := by
          gcongr
          exact inv_le_rpow_of_neg_one_le hΘ1 he
    _ = (CP ^ (-2 : ℝ) * Θ⁻¹ * (na / d) ^ ϱ) ^ (β / 2) := by
          rw [← hRHS]

/-- **The four factor bounds of blueprint `lem:ml2thickPlankF`, multiplied together.**

The left-hand side of the `plankF` conclusion, read at the plank scales `a' ∼ d/nb`,
`b' ∼ d/na` and at `M = Θ (d/na)^{2+ϱ} N`, is bounded below by a product in which every
occurrence of the plank data has been replaced by the working scales and an explicit negative
power of the comparison constant `CP`. The four factors are bounded by
`Kakeya.VeryNotSticky.rpow_mul_le_rpow_of_inv_mul_le` (for `a'^ν`, after
`Kakeya.VeryNotSticky.self_le_div_of_le_one` turns `d/nb` into `d`, and for `(b')^{2β}`),
`Kakeya.VeryNotSticky.inv_le_rpow_of_neg_one_le` (for `C_F^{β/2-1}`) and
`Kakeya.VeryNotSticky.thickM_lower` followed by `Kakeya.VeryNotSticky.rpow_thickM_lower` (for
the non-concentration factor).

Here `d`, `na`, `nb` are the working scales `δ`, `a`, `b`, and `Cb` is the bias constant
`C_bias`. -/
theorem thickPlankF_product_lower {CP Cb Θ d na nb a' b' N : ENNReal} {ν β ϱ : ℝ}
    (hCP0 : CP ≠ 0) (hCPtop : CP ≠ ⊤) (hCP1 : 1 ≤ CP)
    (hCb1 : 1 ≤ Cb) (hΘ1 : 1 ≤ Θ) (hΘtop : Θ ≠ ⊤)
    (hN0 : N ≠ 0) (hNtop : N ≠ ⊤)
    (hd0 : d ≠ 0) (hdtop : d ≠ ⊤) (hna0 : na ≠ 0) (hnatop : na ≠ ⊤)
    (hnb0 : nb ≠ 0) (hnb1 : nb ≤ 1)
    (hν : 0 ≤ ν) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (ha' : CP⁻¹ * (d / nb) ≤ a') (hb' : CP⁻¹ * (d / na) ≤ b') :
    CP ^ (-ν) * d ^ ν * (CP * Cb)⁻¹ * (CP ^ (-(2 * β)) * (d / na) ^ (2 * β)) *
        (CP ^ (-β) * Θ⁻¹ * (na / d) ^ (ϱ * β / 2)) ≤
      a' ^ ν * (CP * Cb) ^ (β / 2 - 1) * b' ^ (2 * β) *
        ((Θ * (d / na) ^ (2 + ϱ) * N)⁻¹ * b' ^ (2 : ℝ) * N) ^ (β / 2) := by
  have h1 : CP ^ (-ν) * d ^ ν ≤ a' ^ ν := by
    have hsum : CP⁻¹ * d ≤ a' := by
      calc
        CP⁻¹ * d ≤ CP⁻¹ * (d / nb) := by
          gcongr
          exact self_le_div_of_le_one hnb0 hnb1
        _ ≤ a' := ha'
    exact rpow_mul_le_rpow_of_inv_mul_le hCP0 hCPtop hsum hν
  have h2 : (CP * Cb)⁻¹ ≤ (CP * Cb) ^ (β / 2 - 1) := by
    have hCPCb1 : 1 ≤ CP * Cb := by
      exact one_le_mul hCP1 hCb1
    have he : -1 ≤ β / 2 - 1 := by linarith
    exact inv_le_rpow_of_neg_one_le (C := CP * Cb) hCPCb1 he
  have h3 : CP ^ (-(2 * β)) * (d / na) ^ (2 * β) ≤ b' ^ (2 * β) := by
    have hnonneg : (0 : ℝ) ≤ 2 * β := by nlinarith
    exact rpow_mul_le_rpow_of_inv_mul_le hCP0 hCPtop hb' (r := 2 * β) hnonneg
  have h4 : CP ^ (-β) * Θ⁻¹ * (na / d) ^ (ϱ * β / 2) ≤
      ((Θ * (d / na) ^ (2 + ϱ) * N)⁻¹ * b' ^ (2 : ℝ) * N) ^ (β / 2) := by
    have hΘ0 : Θ ≠ 0 := (zero_lt_one.trans_le hΘ1).ne'
    have hβ2 : (0 : ℝ) ≤ β / 2 := by nlinarith
    exact (rpow_thickM_lower hCP0 hCPtop hΘ1 hΘtop hβ0 hβ1).trans
      (ENNReal.rpow_le_rpow
        (thickM_lower hCP0 hCPtop hΘ0 hΘtop hN0 hNtop hd0 hdtop hna0 hnatop hb') hβ2)
  exact mul_le_mul' (mul_le_mul' (mul_le_mul' h1 h2) h3) h4

/-- **Transporting the `plankF` conclusion back to the body, and collecting the constants**
(blueprint `lem:ml2thickPlankF`, final step).

The product bound of `Kakeya.VeryNotSticky.thickPlankF_product_lower` is
`A⁻¹ · d^ν (na/d)^{ϱβ/2} (d/na)^{2β}` with `A = CP^{ν+3β} (CP C_bias) Θ`. Multiplying by the
volume `W` of the body, feeding in `Kakeya.VeryNotSticky.ThickPlankPresentation.volume_le` in
the form `|U(𝒫)| |W| ≤ |B₁| |U ∩ W|`, and clearing `A` and `na^{2β}` — both in `(0, ∞)` —
gives exactly `Kakeya.VeryNotSticky.DenseInBodyRaw` at the constant `64 |B₁| CP^{ν+3β} Θ`, the
identity `(d/na)^{2β} · na^{2β} = d^{2β}` being what turns the plank scale back into the
working scale. -/
theorem thickPlankF_conclude {CP Cb Θ d na UP W UW B1 : ENNReal} {ν β ϱ : ℝ}
    (hCP0 : CP ≠ 0) (hCPtop : CP ≠ ⊤) (hCb0 : Cb ≠ 0) (hCbtop : Cb ≠ ⊤)
    (hΘ0 : Θ ≠ 0) (hΘtop : Θ ≠ ⊤)
    (_hd0 : d ≠ 0) (_hdtop : d ≠ ⊤) (hna0 : na ≠ 0) (hnatop : na ≠ ⊤)
    (hβ0 : 0 < β) (_hν : 0 ≤ ν)
    (hP : CP ^ (-ν) * d ^ ν * (CP * Cb)⁻¹ * (CP ^ (-(2 * β)) * (d / na) ^ (2 * β)) *
        (CP ^ (-β) * Θ⁻¹ * (na / d) ^ (ϱ * β / 2)) ≤ 64 * UP)
    (hvol : UP * W ≤ B1 * UW) :
    d ^ ν * (na / d) ^ (ϱ * β / 2) * (d ^ (2 * β) * W) ≤
      64 * B1 * CP ^ (ν + 3 * β) * Θ * (CP * Cb) * (na ^ (2 * β) * UW) := by
  -- STEP 1: name the constant
  let A : ENNReal := CP ^ (ν + 3 * β) * (CP * Cb) * Θ
  let G : ENNReal := d ^ ν * (na / d) ^ (ϱ * β / 2) * (d / na) ^ (2 * β)
  let X : ENNReal := d ^ ν * (na / d) ^ (ϱ * β / 2) * (d ^ (2 * β) * W)
  let n2 : ENNReal := na ^ (2 * β)
  have hCPpow0 : CP ^ (ν + 3 * β) ≠ 0 := by
    simp [hCP0, hCPtop]
  have hCPpowTop : CP ^ (ν + 3 * β) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hCP0 hCPtop
  have hCPCb0 : CP * Cb ≠ 0 := mul_ne_zero hCP0 hCb0
  have hCPCbTop : CP * Cb ≠ ⊤ := ENNReal.mul_ne_top hCPtop hCbtop
  have hA0 : A ≠ 0 := by
    dsimp [A]
    exact mul_ne_zero (mul_ne_zero hCPpow0 hCPCb0) hΘ0
  have hAtop : A ≠ ⊤ := by
    dsimp [A]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hCPpowTop hCPCbTop) hΘtop
  have hn20 : n2 ≠ 0 := by
    dsimp [n2]
    simp [hna0, hnatop]
  have hn2top : n2 ≠ ⊤ := by
    dsimp [n2]
    exact ENNReal.rpow_ne_top_of_ne_zero hna0 hnatop
  have hAdef : A = CP ^ (ν + 3 * β) * (CP * Cb) * Θ := rfl
  have hGdef : G = d ^ ν * (na / d) ^ (ϱ * β / 2) * (d / na) ^ (2 * β) := rfl
  have hXdef : X = d ^ ν * (na / d) ^ (ϱ * β / 2) * (d ^ (2 * β) * W) := rfl
  have hn2def : n2 = na ^ (2 * β) := rfl
  -- STEP 2: the left side of `hP` is `A⁻¹ * G`
  have hCPsum : CP ^ (-ν) * CP ^ (-(2 * β)) * CP ^ (-β) = (CP ^ (ν + 3 * β))⁻¹ := by
    calc
      CP ^ (-ν) * CP ^ (-(2 * β)) * CP ^ (-β)
          = CP ^ (-ν + -(2 * β)) * CP ^ (-β) := by
            rw [← ENNReal.rpow_add (-ν) (-(2 * β)) hCP0 hCPtop]
      _ = CP ^ ((-ν + -(2 * β)) + -β) := by
            rw [← ENNReal.rpow_add (-ν + -(2 * β)) (-β) hCP0 hCPtop]
      _ = (CP ^ (ν + 3 * β))⁻¹ := by
            rw [← ENNReal.rpow_neg]
            congr 1
            ring
  have hAinv : A⁻¹ = (CP ^ (ν + 3 * β))⁻¹ * (CP * Cb)⁻¹ * Θ⁻¹ := by
    dsimp [A]
    rw [ENNReal.mul_inv (Or.inl (mul_ne_zero hCPpow0 hCPCb0))
      (Or.inl (ENNReal.mul_ne_top hCPpowTop hCPCbTop))]
    rw [ENNReal.mul_inv (Or.inl hCPpow0) (Or.inl hCPpowTop)]
  have hrw : CP ^ (-ν) * d ^ ν * (CP * Cb)⁻¹ * (CP ^ (-(2 * β)) * (d / na) ^ (2 * β)) *
        (CP ^ (-β) * Θ⁻¹ * (na / d) ^ (ϱ * β / 2)) = A⁻¹ * G := by
    calc
      (CP ^ (-ν) * d ^ ν * (CP * Cb)⁻¹ * (CP ^ (-(2 * β)) * (d / na) ^ (2 * β)) *
          (CP ^ (-β) * Θ⁻¹ * (na / d) ^ (ϱ * β / 2)))
        = (CP ^ (-ν) * CP ^ (-(2 * β)) * CP ^ (-β)) * d ^ ν * (CP * Cb)⁻¹ * Θ⁻¹ *
            (d / na) ^ (2 * β) * (na / d) ^ (ϱ * β / 2) := by
          ring
      _ = (CP ^ (ν + 3 * β))⁻¹ * d ^ ν * (CP * Cb)⁻¹ * Θ⁻¹ * (d / na) ^ (2 * β) *
            (na / d) ^ (ϱ * β / 2) := by
          rw [hCPsum]
      _ = A⁻¹ * G := by
          rw [hAinv, hGdef]
          ring
  -- STEP 3: the scale identity `G * W = X * (na^(2*β))⁻¹`
  have h2b : (0 : ℝ) ≤ 2 * β := by nlinarith
  have hdiv : (d / na) ^ (2 * β) = d ^ (2 * β) * (na ^ (2 * β))⁻¹ := by
    rw [ENNReal.div_rpow_of_nonneg d na h2b]
    rw [div_eq_mul_inv]
  have hGscale : G * W = X * n2⁻¹ := by
    rw [hGdef, hXdef, hn2def]
    rw [hdiv]
    ring
  -- STEP 4: put it together
  have h1 : A⁻¹ * G ≤ 64 * UP := by
    rw [← hrw]
    exact hP
  have h3 : A⁻¹ * G * W ≤ 64 * UP * W := by
    gcongr
  have hGA : A⁻¹ * G * W = A⁻¹ * (X * n2⁻¹) := by
    rw [mul_assoc, hGscale]
  have h4 : A⁻¹ * (X * n2⁻¹) ≤ 64 * UP * W := by
    rwa [hGA] at h3
  have h5 : 64 * UP * W ≤ 64 * (B1 * UW) := by
    rw [mul_assoc]
    gcongr
  have hstep4 : A⁻¹ * (X * n2⁻¹) ≤ 64 * (B1 * UW) := le_trans h4 h5
  -- STEP 5: clear `A⁻¹` and `n2⁻¹`
  have hAA : A * A⁻¹ = 1 := ENNReal.mul_inv_cancel hA0 hAtop
  have hn2n2 : n2 * n2⁻¹ = 1 := ENNReal.mul_inv_cancel hn20 hn2top
  have hXeq : X = A * (n2 * (A⁻¹ * (X * n2⁻¹))) := by
    calc
      X = (A * A⁻¹) * (n2 * n2⁻¹) * X := by
          rw [hAA, hn2n2]
          simp
      _ = A * (n2 * (A⁻¹ * (X * n2⁻¹))) := by
          ring
  have hXle : X ≤ A * (n2 * (64 * (B1 * UW))) := by
    calc
      X = A * (n2 * (A⁻¹ * (X * n2⁻¹))) := hXeq
      _ ≤ A * (n2 * (64 * (B1 * UW))) := by
          gcongr
  calc
    d ^ ν * (na / d) ^ (ϱ * β / 2) * (d ^ (2 * β) * W) = X := rfl
    _ ≤ A * (n2 * (64 * (B1 * UW))) := hXle
    _ = 64 * B1 * CP ^ (ν + 3 * β) * Θ * (CP * Cb) * (na ^ (2 * β) * UW) := by
        dsimp [A, n2]
        ring

/-- **The whole `[0, ∞]` half of blueprint `lem:ml2thickPlankF`, in one step.**

From the `plankF` conclusion at the plank scales (`hplank`) and the volume comparison of
blueprint `lem:ml2thickPlank`(ii) (`hvol`), the density inside the body follows with two `ℝ≥0`
constants bounded below by `1`. It is exactly
`Kakeya.VeryNotSticky.thickPlankF_product_lower`, then transitivity, then
`Kakeya.VeryNotSticky.thickPlankF_conclude`, then
`Kakeya.VeryNotSticky.exists_nnreal_const_of_le`; it is packaged as one lemma so that the
consumer `Kakeya.VeryNotSticky.denseInBodyRaw_of_thickPlankPresentation` carries only the
geometry and not the arithmetic.

`d`, `na`, `nb` are the working scales `δ`, `a`, `b`, `a'`, `b'` the plank dimensions, `N` the
cardinality of the block, `Ns` the cardinality of the selected subfamily the estimate was
actually applied to, `UP` the shaded volume of the plank family, `W` and `UW` the volume of the
body and of the shaded union inside it, `B1` the volume of the localizing ball, and `Cb` the
bias constant of blueprint `lemmafactmaxbias`.

**Why `N` and `Ns` are separate.** `Kakeya.VeryNotSticky.ThickPlankPresentation` carries an
*enclosing* plank family whose essential distinctness holds only on a selected subfamily, so
blueprint `plankF` is applied to `Ns = |sel|` planks while the non-concentration parameter `M`
is still stated with the block cardinality `N` — that is what keeps
`Kakeya.VeryNotSticky.one_le_thickM` fed by blueprint `lem:ml2thickPcard` unchanged. The
hypothesis `hNs : CP⁻¹ N ≤ Ns` is the presentation's `sel_card`, and the whole effect of the
gap is to run `Kakeya.VeryNotSticky.thickPlankF_product_lower` and
`Kakeya.VeryNotSticky.thickPlankF_conclude` at `CP Θ C_bias` in place of `Θ C_bias`, i.e. one
further power of `CP` in the produced constant. No exponent moves. -/
theorem exists_denseConst_of_plankF {CP Θ Cb : NNReal} (hCP : 1 ≤ CP) (hΘ : 1 ≤ Θ)
    (hCb : 1 ≤ Cb) {d na nb a' b' N Ns UP W UW B1 : ENNReal} {ν β ϱ : ℝ}
    (hN0 : N ≠ 0) (hNtop : N ≠ ⊤)
    (hd0 : d ≠ 0) (hdtop : d ≠ ⊤) (hna0 : na ≠ 0) (hnatop : na ≠ ⊤)
    (hnb0 : nb ≠ 0) (hnb1 : nb ≤ 1) (hB1 : B1 ≠ ⊤)
    (hν : 0 ≤ ν) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (ha' : (CP : ENNReal)⁻¹ * (d / nb) ≤ a') (hb' : (CP : ENNReal)⁻¹ * (d / na) ≤ b')
    (hNs : (CP : ENNReal)⁻¹ * N ≤ Ns)
    (hplank : a' ^ ν * ((CP : ENNReal) * (Cb : ENNReal)) ^ (β / 2 - 1) * b' ^ (2 * β) *
        (((Θ : ENNReal) * (Cb : ENNReal) * (d / na) ^ (2 + ϱ) * N)⁻¹ * b' ^ (2 : ℝ) * Ns) ^
          (β / 2) ≤ 64 * UP)
    (hvol : UP * W ≤ B1 * UW) :
    ∃ Θ' C₁' : NNReal, 1 ≤ Θ' ∧ 1 ≤ C₁' ∧
      d ^ ν * (na / d) ^ (ϱ * β / 2) * (d ^ (2 * β) * W) ≤
        (Θ' : ENNReal) * (C₁' : ENNReal) * (na ^ (2 * β) * UW) := by
  let CPe : ENNReal := (CP : ENNReal)
  let Θe : ENNReal := (Θ : ENNReal)
  let Cbe : ENNReal := (Cb : ENNReal)
  let Y : ENNReal := (d / na) ^ (2 + ϱ)
  let X : ENNReal := (Θe * Cbe) * Y * N
  let M : ENNReal := (((CPe * Θe * Cbe) * Y * N)⁻¹ * b' ^ (2 : ℝ) * N) ^ (β / 2)
  let M' : ENNReal := (((Θe * Cbe) * Y * N)⁻¹ * b' ^ (2 : ℝ) * Ns) ^ (β / 2)
  have hCP1 : (1 : ENNReal) ≤ CPe := by
    dsimp [CPe]
    exact_mod_cast hCP
  have hCP0 : CPe ≠ 0 := by
    dsimp [CPe]
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hCP))
  have hCPtop : CPe ≠ ⊤ := by
    dsimp [CPe]
    exact ENNReal.coe_ne_top
  have hΘ1 : (1 : ENNReal) ≤ Θe := by
    dsimp [Θe]
    exact_mod_cast hΘ
  have hΘ0 : Θe ≠ 0 := by
    dsimp [Θe]
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hΘ))
  have hΘtop : Θe ≠ ⊤ := by
    dsimp [Θe]
    exact ENNReal.coe_ne_top
  have hCb1 : (1 : ENNReal) ≤ Cbe := by
    dsimp [Cbe]
    exact_mod_cast hCb
  have hCb0 : Cbe ≠ 0 := by
    dsimp [Cbe]
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hCb))
  have hCbtop : Cbe ≠ ⊤ := by
    dsimp [Cbe]
    exact ENNReal.coe_ne_top
  have hΘF1 : (1 : ENNReal) ≤ CPe * Θe * Cbe := by
    exact one_le_mul (one_le_mul hCP1 hΘ1) hCb1
  have hΘFtop : CPe * Θe * Cbe ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hCPtop hΘtop) hCbtop
  have hΘF0 : CPe * Θe * Cbe ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hCP0 hΘ0) hCb0
  have hNs' : CPe⁻¹ * N ≤ Ns := by
    simpa [CPe] using hNs
  have hXdef : X = (Θe * Cbe) * Y * N := rfl
  have hCPeX : (CPe * Θe * Cbe) * Y * N = CPe * X := by
    dsimp [X]
    ring
  have hmono : ((CPe * Θe * Cbe) * Y * N)⁻¹ * b' ^ (2 : ℝ) * N ≤
      ((Θe * Cbe) * Y * N)⁻¹ * b' ^ (2 : ℝ) * Ns := by
    calc
      ((CPe * Θe * Cbe) * Y * N)⁻¹ * b' ^ (2 : ℝ) * N
          = (CPe * X)⁻¹ * b' ^ (2 : ℝ) * N := by
              rw [hCPeX]
      _ = (CPe⁻¹ * X⁻¹) * b' ^ (2 : ℝ) * N := by
              rw [ENNReal.mul_inv (Or.inl hCP0) (Or.inl hCPtop)]
      _ = X⁻¹ * b' ^ (2 : ℝ) * (CPe⁻¹ * N) := by
              ring
      _ ≤ X⁻¹ * b' ^ (2 : ℝ) * Ns := by
              gcongr
      _ = ((Θe * Cbe) * Y * N)⁻¹ * b' ^ (2 : ℝ) * Ns := by
              rw [← hXdef]
  have hβ2 : (0 : ℝ) ≤ β / 2 := by nlinarith
  have hmonopow : M ≤ M' := by
    dsimp [M, M']
    exact ENNReal.rpow_le_rpow hmono hβ2
  have hprod := thickPlankF_product_lower (CP := CPe) (Cb := Cbe) (Θ := CPe * Θe * Cbe)
    (d := d) (na := na) (nb := nb) (a' := a') (b' := b') (N := N) (ν := ν) (β := β) (ϱ := ϱ)
    hCP0 hCPtop hCP1 hCb1 hΘF1 hΘFtop hN0 hNtop hd0 hdtop hna0 hnatop hnb0 hnb1 hν hβ0 hβ1
    (by simpa [CPe] using ha') (by simpa [CPe] using hb')
  have hMle : a' ^ ν * (CPe * Cbe) ^ (β / 2 - 1) * b' ^ (2 * β) * M ≤
      a' ^ ν * (CPe * Cbe) ^ (β / 2 - 1) * b' ^ (2 * β) * M' := by
    gcongr
  have hP : CPe ^ (-ν) * d ^ ν * (CPe * Cbe)⁻¹ * (CPe ^ (-(2 * β)) * (d / na) ^ (2 * β)) *
      (CPe ^ (-β) * (CPe * Θe * Cbe)⁻¹ * (na / d) ^ (ϱ * β / 2)) ≤ 64 * UP := by
    calc
      CPe ^ (-ν) * d ^ ν * (CPe * Cbe)⁻¹ * (CPe ^ (-(2 * β)) * (d / na) ^ (2 * β)) *
          (CPe ^ (-β) * (CPe * Θe * Cbe)⁻¹ * (na / d) ^ (ϱ * β / 2))
          ≤ a' ^ ν * (CPe * Cbe) ^ (β / 2 - 1) * b' ^ (2 * β) * M := by
              simpa [M] using hprod
      _ ≤ a' ^ ν * (CPe * Cbe) ^ (β / 2 - 1) * b' ^ (2 * β) * M' := hMle
      _ ≤ 64 * UP := by
              simpa [CPe, Θe, Cbe, Y, M'] using hplank
  have hcon := thickPlankF_conclude (CP := CPe) (Cb := Cbe) (Θ := CPe * Θe * Cbe)
    (d := d) (na := na) (UP := UP) (W := W) (UW := UW) (B1 := B1)
    (ν := ν) (β := β) (ϱ := ϱ)
    hCP0 hCPtop hCb0 hCbtop hΘF0 hΘFtop hd0 hdtop hna0 hnatop hβ0 hν hP hvol
  exact exists_nnreal_const_of_le (CP := CP) (Θ := CP * Θ) (Cb := Cb) hCP
    (one_le_mul hCP hΘ) hCb hB1 (by
      simpa [CPe, Θe, Cbe, Y, ENNReal.coe_mul] using hcon)

end Kakeya.VeryNotSticky
