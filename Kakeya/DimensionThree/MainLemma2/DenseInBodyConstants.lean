/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThickCase
public import Kakeya.DimensionThree.MainLemma2.DenseInBodyNamed

/-!
# Named constants for density inside a body

`Kakeya.VeryNotSticky.exists_denseInBody` and its auxiliary lemmas return
`∃ Θ C₁ : ℝ≥0, 1 ≤ Θ ∧ 1 ≤ C₁ ∧ …`. Quantitative thresholds must use a
suitable pair of witnesses: requiring `Λ C₁ Θ ≤ δ^{-ν}` for every pair
`(Θ, C₁)` would allow arbitrarily large constants to defeat the threshold.

The proof supplies an explicit pair.
`Kakeya.VeryNotSticky.exists_denseConst_of_plankF` calls
`Kakeya.VeryNotSticky.exists_nnreal_const_of_le` at `Θ := CP * Θ`; the latter
returns `⟨Θ * Cb * Cb, max 1 (64 * B1.toNNReal * CP ^ (ν + 3β) * CP)⟩`.
The subsequent lemmas preserve this pair:

* `Kakeya.VeryNotSticky.denseInBodyΘ CP Θ₀ C_bias = CP Θ₀ C_bias²`.
  Its scale dependence occurs through `C_bias` (the maximal-density
  factorization estimate).
* `Kakeya.VeryNotSticky.denseInBodyC₁ CP ν β =
  max 1 (64 |B̄(0,4)| CP^{ν+3β} CP)`. This constant is independent of
  `δ` and depends on `CP`, the two exponents, and the ambient dimension.

The chain
`thickPlankF_conclude_of_plankF → denseConst_at_of_plankF →
denseInBodyRaw_at_of_thickPlankPresentation → exists_denseInBodyRaw_at →
exists_denseInBody_at` establishes the estimates at these named constants.
Each `_at` form implies its existential companion, as recorded by
`exists_denseInBody_at_imp` and the analogous lemmas.

`thickPlankF_conclude_of_plankF` separates the quantitative estimate from
choosing its witnesses, so both the named and existential forms follow from
the same estimate. The definitions `denseInBodyΘ` and `denseInBodyC₁` are
provided by `DenseInBodyNamed.lean`.
-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace Kakeya.VeryNotSticky

open Kakeya

universe u

/-! ### The arithmetic step, at the named constants -/

/-- **`Kakeya.VeryNotSticky.exists_nnreal_const_of_le`, with its witnesses named.**

The existing lemma is applied at `Θ := CP * Θ`; its two witnesses are then exactly
`denseInBodyΘ CP Θ Cb` and `denseInBodyC₁ CP ν β`, the second because
`Kakeya.VeryNotSticky.denseInBodyRaw_of_thickPlankPresentation` instantiates its `B1` at the
volume of the window ball. -/
theorem le_denseInBodyConst_of_le {CP Θ Cb : NNReal} (hCP : 1 ≤ CP) (_hCb : 1 ≤ Cb)
    {ν β : ℝ} {X Y : ENNReal}
    (h : X ≤ 64 * volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) Plank.windowRadius) *
        (CP : ENNReal) ^ (ν + 3 * β) *
        ((CP : ENNReal) * (Θ : ENNReal) * (Cb : ENNReal)) *
        ((CP : ENNReal) * (Cb : ENNReal)) * Y) :
    X ≤ (denseInBodyΘ CP Θ Cb : ENNReal) * (denseInBodyC₁ CP ν β : ENNReal) * Y := by
  set B1 : ENNReal :=
    volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) Plank.windowRadius) with hB1def
  have hB1 : B1 ≠ ⊤ := by
    rw [hB1def]; exact (MeasureTheory.measure_closedBall_lt_top).ne
  have hCP0 : CP ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hCP)
  have hC : (64 : ENNReal) * B1 * (CP : ENNReal) ^ (ν + 3 * β) * (CP : ENNReal) ≤
      ((denseInBodyC₁ CP ν β : NNReal) : ENNReal) := by
    calc
      (64 : ENNReal) * B1 * (CP : ENNReal) ^ (ν + 3 * β) * (CP : ENNReal)
          = ((64 * B1.toNNReal * CP ^ (ν + 3 * β) * CP : NNReal) : ENNReal) := by
            simp [ENNReal.coe_rpow_of_ne_zero hCP0, hB1]
      _ ≤ ((denseInBodyC₁ CP ν β : NNReal) : ENNReal) := by
            exact ENNReal.coe_le_coe.2 (le_max_right _ _)
  refine h.trans ?_
  calc
    64 * B1 * (CP : ENNReal) ^ (ν + 3 * β) *
          ((CP : ENNReal) * (Θ : ENNReal) * (Cb : ENNReal)) *
          ((CP : ENNReal) * (Cb : ENNReal)) * Y
        = (CP : ENNReal) * (Θ : ENNReal) * (Cb : ENNReal) * (Cb : ENNReal) *
            ((64 : ENNReal) * B1 * (CP : ENNReal) ^ (ν + 3 * β) * (CP : ENNReal)) * Y := by
          ring
    _ ≤ (CP : ENNReal) * (Θ : ENNReal) * (Cb : ENNReal) * (Cb : ENNReal) *
        ((denseInBodyC₁ CP ν β : NNReal) : ENNReal) * Y := by
          gcongr
    _ = (denseInBodyΘ CP Θ Cb : ENNReal) * ((denseInBodyC₁ CP ν β : NNReal) : ENNReal) * Y := by
          rw [denseInBodyΘ]
          push_cast
          ring

/-! ### The plank half, factored -/

/-- **The whole of `Kakeya.VeryNotSticky.exists_denseConst_of_plankF` except its last line.**

Hypotheses and proof are those of the existing lemma; what is different is that the conclusion
is the *bound at the explicit product* that `Kakeya.VeryNotSticky.thickPlankF_conclude`
delivers, before it is split into two `ℝ≥0` factors. Both the existing existential and the named
form of this file follow from it, the first by
`Kakeya.VeryNotSticky.exists_nnreal_const_of_le` and the second by
`Kakeya.VeryNotSticky.le_denseInBodyConst_of_le`.

It is stated separately, rather than obtained by editing the existing lemma, so that no existing
proof term changes. -/
theorem thickPlankF_conclude_of_plankF {CP Θ Cb : NNReal} (hCP : 1 ≤ CP) (hΘ : 1 ≤ Θ)
    (hCb : 1 ≤ Cb) {d na nb a' b' N Ns UP W UW B1 : ENNReal} {ν β ϱ : ℝ}
    (hN0 : N ≠ 0) (hNtop : N ≠ ⊤)
    (hd0 : d ≠ 0) (hdtop : d ≠ ⊤) (hna0 : na ≠ 0) (hnatop : na ≠ ⊤)
    (hnb0 : nb ≠ 0) (hnb1 : nb ≤ 1)
    (hν : 0 ≤ ν) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (ha' : (CP : ENNReal)⁻¹ * (d / nb) ≤ a') (hb' : (CP : ENNReal)⁻¹ * (d / na) ≤ b')
    (hNs : (CP : ENNReal)⁻¹ * N ≤ Ns)
    (hplank : a' ^ ν * ((CP : ENNReal) * (Cb : ENNReal)) ^ (β / 2 - 1) * b' ^ (2 * β) *
        (((Θ : ENNReal) * (Cb : ENNReal) * (d / na) ^ (2 + ϱ) * N)⁻¹ * b' ^ (2 : ℝ) * Ns) ^
          (β / 2) ≤ 64 * UP)
    (hvol : UP * W ≤ B1 * UW) :
    d ^ ν * (na / d) ^ (ϱ * β / 2) * (d ^ (2 * β) * W) ≤
      64 * B1 * (CP : ENNReal) ^ (ν + 3 * β) *
        ((CP : ENNReal) * (Θ : ENNReal) * (Cb : ENNReal)) *
        ((CP : ENNReal) * (Cb : ENNReal)) * (na ^ (2 * β) * UW) := by
  let CPe : ENNReal := (CP : ENNReal)
  let Θe : ENNReal := (Θ : ENNReal)
  let Cbe : ENNReal := (Cb : ENNReal)
  let Y : ENNReal := (d / na) ^ (2 + ϱ)
  let X : ENNReal := (Θe * Cbe) * Y * N
  let M : ENNReal := (((CPe * Θe * Cbe) * Y * N)⁻¹ * b' ^ (2 : ℝ) * N) ^ (β / 2)
  let M' : ENNReal := (((Θe * Cbe) * Y * N)⁻¹ * b' ^ (2 : ℝ) * Ns) ^ (β / 2)
  have hCP1 : (1 : ENNReal) ≤ CPe := by
    dsimp [CPe]; exact_mod_cast hCP
  have hCP0 : CPe ≠ 0 := by
    dsimp [CPe]; exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hCP))
  have hCPtop : CPe ≠ ⊤ := by
    dsimp [CPe]; exact ENNReal.coe_ne_top
  have hΘ1 : (1 : ENNReal) ≤ Θe := by
    dsimp [Θe]; exact_mod_cast hΘ
  have hΘ0 : Θe ≠ 0 := by
    dsimp [Θe]; exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hΘ))
  have hΘtop : Θe ≠ ⊤ := by
    dsimp [Θe]; exact ENNReal.coe_ne_top
  have hCb1 : (1 : ENNReal) ≤ Cbe := by
    dsimp [Cbe]; exact_mod_cast hCb
  have hCb0 : Cbe ≠ 0 := by
    dsimp [Cbe]; exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hCb))
  have hCbtop : Cbe ≠ ⊤ := by
    dsimp [Cbe]; exact ENNReal.coe_ne_top
  have hΘF1 : (1 : ENNReal) ≤ CPe * Θe * Cbe := one_le_mul (one_le_mul hCP1 hΘ1) hCb1
  have hΘFtop : CPe * Θe * Cbe ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hCPtop hΘtop) hCbtop
  have hΘF0 : CPe * Θe * Cbe ≠ 0 := mul_ne_zero (mul_ne_zero hCP0 hΘ0) hCb0
  have hNs' : CPe⁻¹ * N ≤ Ns := by simpa [CPe] using hNs
  have hXdef : X = (Θe * Cbe) * Y * N := rfl
  have hCPeX : (CPe * Θe * Cbe) * Y * N = CPe * X := by
    dsimp [X]; ring
  have hmono : ((CPe * Θe * Cbe) * Y * N)⁻¹ * b' ^ (2 : ℝ) * N ≤
      ((Θe * Cbe) * Y * N)⁻¹ * b' ^ (2 : ℝ) * Ns := by
    calc
      ((CPe * Θe * Cbe) * Y * N)⁻¹ * b' ^ (2 : ℝ) * N
          = (CPe * X)⁻¹ * b' ^ (2 : ℝ) * N := by rw [hCPeX]
      _ = (CPe⁻¹ * X⁻¹) * b' ^ (2 : ℝ) * N := by
              rw [ENNReal.mul_inv (Or.inl hCP0) (Or.inl hCPtop)]
      _ = X⁻¹ * b' ^ (2 : ℝ) * (CPe⁻¹ * N) := by ring
      _ ≤ X⁻¹ * b' ^ (2 : ℝ) * Ns := by gcongr
      _ = ((Θe * Cbe) * Y * N)⁻¹ * b' ^ (2 : ℝ) * Ns := by rw [← hXdef]
  have hβ2 : (0 : ℝ) ≤ β / 2 := by nlinarith
  have hmonopow : M ≤ M' := by
    dsimp [M, M']; exact ENNReal.rpow_le_rpow hmono hβ2
  have hprod := thickPlankF_product_lower (CP := CPe) (Cb := Cbe) (Θ := CPe * Θe * Cbe)
    (d := d) (na := na) (nb := nb) (a' := a') (b' := b') (N := N) (ν := ν) (β := β) (ϱ := ϱ)
    hCP0 hCPtop hCP1 hCb1 hΘF1 hΘFtop hN0 hNtop hd0 hdtop hna0 hnatop hnb0 hnb1 hν hβ0 hβ1
    (by simpa [CPe] using ha') (by simpa [CPe] using hb')
  have hMle : a' ^ ν * (CPe * Cbe) ^ (β / 2 - 1) * b' ^ (2 * β) * M ≤
      a' ^ ν * (CPe * Cbe) ^ (β / 2 - 1) * b' ^ (2 * β) * M' := by gcongr
  have hP : CPe ^ (-ν) * d ^ ν * (CPe * Cbe)⁻¹ * (CPe ^ (-(2 * β)) * (d / na) ^ (2 * β)) *
      (CPe ^ (-β) * (CPe * Θe * Cbe)⁻¹ * (na / d) ^ (ϱ * β / 2)) ≤ 64 * UP := by
    calc
      CPe ^ (-ν) * d ^ ν * (CPe * Cbe)⁻¹ * (CPe ^ (-(2 * β)) * (d / na) ^ (2 * β)) *
          (CPe ^ (-β) * (CPe * Θe * Cbe)⁻¹ * (na / d) ^ (ϱ * β / 2))
          ≤ a' ^ ν * (CPe * Cbe) ^ (β / 2 - 1) * b' ^ (2 * β) * M := by
              simpa [M] using hprod
      _ ≤ a' ^ ν * (CPe * Cbe) ^ (β / 2 - 1) * b' ^ (2 * β) * M' := hMle
      _ ≤ 64 * UP := by simpa [CPe, Θe, Cbe, Y, M'] using hplank
  have hcon := thickPlankF_conclude (CP := CPe) (Cb := Cbe) (Θ := CPe * Θe * Cbe)
    (d := d) (na := na) (UP := UP) (W := W) (UW := UW) (B1 := B1)
    (ν := ν) (β := β) (ϱ := ϱ)
    hCP0 hCPtop hCb0 hCbtop hΘF0 hΘFtop hd0 hdtop hna0 hnatop hβ0 hν hP hvol
  simpa [CPe, Θe, Cbe] using hcon

/-- **`Kakeya.VeryNotSticky.exists_denseConst_of_plankF`, at the named constants.**

Same hypotheses; the two produced constants are `Kakeya.VeryNotSticky.denseInBodyΘ CP Θ Cb`
and `Kakeya.VeryNotSticky.denseInBodyC₁ CP ν β`, the localizing ball being the window ball. -/
theorem denseConst_at_of_plankF {CP Θ Cb : NNReal} (hCP : 1 ≤ CP) (hΘ : 1 ≤ Θ)
    (hCb : 1 ≤ Cb) {d na nb a' b' N Ns UP W UW : ENNReal} {ν β ϱ : ℝ}
    (hN0 : N ≠ 0) (hNtop : N ≠ ⊤)
    (hd0 : d ≠ 0) (hdtop : d ≠ ⊤) (hna0 : na ≠ 0) (hnatop : na ≠ ⊤)
    (hnb0 : nb ≠ 0) (hnb1 : nb ≤ 1)
    (hν : 0 ≤ ν) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (ha' : (CP : ENNReal)⁻¹ * (d / nb) ≤ a') (hb' : (CP : ENNReal)⁻¹ * (d / na) ≤ b')
    (hNs : (CP : ENNReal)⁻¹ * N ≤ Ns)
    (hplank : a' ^ ν * ((CP : ENNReal) * (Cb : ENNReal)) ^ (β / 2 - 1) * b' ^ (2 * β) *
        (((Θ : ENNReal) * (Cb : ENNReal) * (d / na) ^ (2 + ϱ) * N)⁻¹ * b' ^ (2 : ℝ) * Ns) ^
          (β / 2) ≤ 64 * UP)
    (hvol : UP * W ≤
      volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) Plank.windowRadius) * UW) :
    d ^ ν * (na / d) ^ (ϱ * β / 2) * (d ^ (2 * β) * W) ≤
      (denseInBodyΘ CP Θ Cb : ENNReal) * (denseInBodyC₁ CP ν β : ENNReal) *
        (na ^ (2 * β) * UW) :=
  le_denseInBodyConst_of_le hCP hCb
    (thickPlankF_conclude_of_plankF hCP hΘ hCb hN0 hNtop hd0 hdtop hna0 hnatop hnb0 hnb1
      hν hβ0 hβ1 ha' hb' hNs hplank hvol)

/-! ### The three interface twins -/

/-- **`Kakeya.VeryNotSticky.denseInBodyRaw_of_thickPlankPresentation`, at the named
constants.** -/
theorem denseInBodyRaw_at_of_thickPlankPresentation {cfg : VeryNotSticky.{u}}
    (bd : BallData cfg) {τ : ℝ} (hτ : 0 < τ) (hβ1 : cfg.β ≤ 1)
    {CP Θ C_NC : NNReal} (hCP : 1 ≤ CP) (hΘ : 1 ≤ Θ) {ηF : ℝ} (hηF : 0 < ηF)
    (hbudget : PlankFrostmanUsable bd τ CP C_NC ηF)
    {B : bd.bι} {p₀ : bd.σ} (hp₀ : p₀ ∈ bd.segs B)
    (hpres : ThickPlankPresentation bd B (bd.blk p₀) CP Θ C_NC)
    (hfull : bd.c₁ * cfg.δ ^ (2 * cfg.η) ≤
      ShadedBody.fullness ((bd.segs B).filter fun p => bd.blk p = bd.blk p₀) bd.Y)
    (hPcard : ((cfg.a : ENNReal) / (cfg.δ : ENNReal)) ^ (2 + cfg.ϱ) ≤
      ((((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card : ℕ) : ENNReal)) :
    DenseInBodyRaw bd (cfg.ϱ * cfg.β * τ / 8)
      (denseInBodyΘ CP Θ bd.Cbias)
      (denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β) B (bd.blk p₀) := by
  have hp₀s : p₀ ∈ (bd.segs B).filter fun p => bd.blk p = bd.blk p₀ :=
    Finset.mem_filter.mpr ⟨hp₀, rfl⟩
  have hcard : ((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card ≠ 0 :=
    Finset.card_ne_zero_of_mem hp₀s
  have hN0 : ((((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card : ℕ) : ENNReal) ≠ 0 := by
    exact_mod_cast hcard
  have hd0 : (cfg.δ : ENNReal) ≠ 0 := by simpa using (ne_of_gt cfg.hδ)
  have hna0 : (cfg.a : ENNReal) ≠ 0 := by simpa using (ne_of_gt (cfg_a_pos cfg))
  have hnb0 : (cfg.b : ENNReal) ≠ 0 := by simpa using (ne_of_gt (cfg_b_pos cfg))
  have hnb1 : (cfg.b : ENNReal) ≤ 1 := by exact_mod_cast (cfg_b_le_one cfg)
  have hν : (0 : ℝ) ≤ cfg.ϱ * cfg.β * τ / 8 := by
    have h1 : 0 < cfg.ϱ := cfg.hϱ
    have h2 : 0 < cfg.β := cfg.hβ
    positivity
  exact denseConst_at_of_plankF hCP hΘ bd.hCbias hN0 (ENNReal.natCast_ne_top _)
    hd0 ENNReal.coe_ne_top hna0 ENNReal.coe_ne_top hnb0 hnb1 hν cfg.hβ hβ1
    (thickPres_inv_le_a' hpres hCP) (thickPres_inv_le_b' hpres hCP)
    hpres.sel_card
    (thickPlankF_apply bd hCP hΘ hηF hbudget hpres hfull hPcard)
    hpres.volume_le

/-- **`Kakeya.VeryNotSticky.exists_denseInBodyRaw`, at the named constants.** -/
theorem exists_denseInBodyRaw_at {cfg : VeryNotSticky.{u}} (bd : BallData cfg) {τ : ℝ}
    (hτ : 0 < τ) (hβ1 : cfg.β ≤ 1) {CP Θ₀ C_NC : NNReal} (hCP : 1 ≤ CP) (hΘ₀ : 1 ≤ Θ₀)
    {ηF : ℝ} (hηF : 0 < ηF)
    (hbudget : PlankFrostmanUsable bd τ CP C_NC ηF)
    (hpres : ThickPlankPresentable bd CP Θ₀ C_NC)
    (hPcard : ∀ B ∈ bd.bs, ∀ p₀ ∈ bd.segs B,
      ((cfg.a : ENNReal) / (cfg.δ : ENNReal)) ^ (2 + cfg.ϱ) ≤
        ((((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card : ℕ) : ENNReal)) :
    ∃ B ∈ bd.bs, ∃ j ∈ bd.bodies B,
      DenseInBodyRaw bd (cfg.ϱ * cfg.β * τ / 8)
        (denseInBodyΘ CP Θ₀ bd.Cbias)
        (denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β) B j := by
  obtain ⟨B, hB, p₀, hp₀, hfull⟩ := exists_thickFullBlock bd
  obtain ⟨pres⟩ := hpres B hB p₀ hp₀
  exact ⟨B, hB, bd.blk p₀, bd.blk_mem B hB p₀ hp₀,
    denseInBodyRaw_at_of_thickPlankPresentation bd hτ hβ1 hCP hΘ₀ hηF hbudget hp₀ pres hfull
      (hPcard B hB p₀ hp₀)⟩

/-- `Kakeya.VeryNotSticky.exists_denseInBody` at the named constants.
Fixing `Θ` and `C₁` makes the threshold a direct inequality in the
configuration constants. It does not require the inequality to hold
for every pair of density witnesses. -/
theorem exists_denseInBody_at (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (bd : BallData cfg) (hβ1 : cfg.β ≤ 1) (hthick : cfg.δ ^ (1 - τ) ≤ cfg.a)
    (hδ₂ : (bd.Cbias : ENNReal) * (((48 * bd.C₀ ^ 6) ^ 3 : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(τ * cfg.ϱ)))
    {CP Θ₀ C_NC : NNReal} (hCP : 1 ≤ CP) (hΘ₀ : 1 ≤ Θ₀) {ηF : ℝ} (hηF : 0 < ηF)
    (hbudget : PlankFrostmanUsable bd τ CP C_NC ηF)
    (hpres : ThickPlankPresentable bd CP Θ₀ C_NC) :
    ∀ Λ : ENNReal, 1 ≤ Λ → Λ ≠ ⊤ →
      Λ * (denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β : ENNReal) *
          (denseInBodyΘ CP Θ₀ bd.Cbias : ENNReal) ≤
        (cfg.δ : ENNReal) ^ (-(cfg.ϱ * cfg.β * τ / 8)) →
      ∃ B ∈ bd.bs, ∃ j ∈ bd.bodies B,
        Λ * (cfg.δ : ENNReal) ^ (2 * cfg.β) * volume (bd.Wb j).carrier ≤
          (cfg.δ : ENNReal) ^ (2 * (cfg.ϱ * cfg.β * τ / 8)) *
            volume ((⋃ p ∈ (bd.segs B).filter fun p => bd.blk p = j, (bd.Y p).shade) ∩
              (bd.Wb j).carrier) *
            (cfg.a : ENNReal) ^ (2 * cfg.β) := by
  let ν : ℝ := cfg.ϱ * cfg.β * τ / 8
  let d : ENNReal := (cfg.δ : ENNReal)
  let na : ENNReal := (cfg.a : ENNReal)
  let A : ENNReal := na / d
  have hδe_pos : (0 : ENNReal) < (cfg.δ : ENNReal) := by exact_mod_cast cfg.hδ
  have hd0 : d ≠ 0 := by dsimp [d]; exact hδe_pos.ne.symm
  have hdtop : d ≠ ⊤ := by dsimp [d]; exact ENNReal.coe_ne_top
  have hδ0 : (cfg.δ : NNReal) ≠ 0 := ne_of_gt cfg.hδ
  have hϱp : 0 < cfg.ϱ := cfg.hϱ
  have hβp : 0 < cfg.β := cfg.hβ
  have hτp : 0 < τ := params.hτ
  have hνpos : 0 < ν := by dsimp [ν]; positivity
  have h_rhs_nonneg : 0 ≤ cfg.ϱ * cfg.β / 2 := by positivity
  have hthickE : d ^ (1 - τ) ≤ na := by
    dsimp [d, na]
    rw [← ENNReal.coe_rpow_of_ne_zero hδ0 (1 - τ)]
    exact_mod_cast hthick
  have h_pow_split : d ^ (1 - τ) = d ^ (-τ) * d := by
    rw [show (1 : ℝ) - τ = (-τ) + (1 : ℝ) by ring]
    rw [ENNReal.rpow_add (-τ) (1 : ℝ) hd0 hdtop, ENNReal.rpow_one]
  have hthickE' : d ^ (-τ) * d ≤ na := by rw [h_pow_split] at hthickE; exact hthickE
  have hdiv : d ^ (-τ) ≤ A := by
    dsimp [A]
    rw [ENNReal.le_div_iff_mul_le (Or.inl hd0) (Or.inl hdtop)]
    exact hthickE'
  have hsurplus : d ^ (-(4 * ν)) ≤ A ^ (cfg.ϱ * cfg.β / 2) := by
    have h := ENNReal.rpow_le_rpow hdiv h_rhs_nonneg
    rwa [show (-(4 * ν)) = (-τ) * (cfg.ϱ * cfg.β / 2) by dsimp [ν]; ring,
      ENNReal.rpow_mul d (-τ) (cfg.ϱ * cfg.β / 2)]
  obtain ⟨B, hB, j, hj, hraw⟩ :=
    exists_denseInBodyRaw_at bd params.hτ hβ1 hCP hΘ₀ hηF hbudget hpres
      (fun B' hB' => fun p₀ hp₀ => thickPcard_ge cfg params bd hthick hδ₂ hB' hp₀)
  set Θ : NNReal := denseInBodyΘ CP Θ₀ bd.Cbias with hΘdef
  set C₁ : NNReal := denseInBodyC₁ CP ν cfg.β with hC₁def
  let X : ENNReal := d ^ (2 * cfg.β) * volume (bd.Wb j).carrier
  let Y : ENNReal :=
    na ^ (2 * cfg.β) *
      volume ((⋃ p ∈ (bd.segs B).filter fun p => bd.blk p = j, (bd.Y p).shade) ∩
        (bd.Wb j).carrier)
  have hraw' : d ^ ν * A ^ (cfg.ϱ * cfg.β / 2) * X ≤ (Θ : ENNReal) * (C₁ : ENNReal) * Y := by
    simpa [DenseInBodyRaw, X, Y, ν, d, na, A, hΘdef, hC₁def] using hraw
  have hidem : d ^ (-(3 * ν)) * X ≤ (Θ : ENNReal) * (C₁ : ENNReal) * Y := by
    have hsum : d ^ (-(4 * ν)) * X ≤ A ^ (cfg.ϱ * cfg.β / 2) * X :=
      mul_le_mul_of_nonneg_right hsurplus (by positivity : 0 ≤ X)
    have hud : d ^ ν * (d ^ (-(4 * ν)) * X) ≤ d ^ ν * (A ^ (cfg.ϱ * cfg.β / 2) * X) :=
      mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ d ^ ν)
    have hle : d ^ ν * d ^ (-(4 * ν)) * X ≤ (Θ : ENNReal) * (C₁ : ENNReal) * Y := by
      calc
        d ^ ν * d ^ (-(4 * ν)) * X = d ^ ν * (d ^ (-(4 * ν)) * X) := by simp [mul_assoc]
        _ ≤ d ^ ν * (A ^ (cfg.ϱ * cfg.β / 2) * X) := hud
        _ = d ^ ν * A ^ (cfg.ϱ * cfg.β / 2) * X := by simp [mul_assoc]
        _ ≤ (Θ : ENNReal) * (C₁ : ENNReal) * Y := hraw'
    have hp : d ^ ν * d ^ (-(4 * ν)) = d ^ (-(3 * ν)) := by
      rw [← ENNReal.rpow_add ν (-(4 * ν)) hd0 hdtop]
      congr 1
      ring
    rwa [← hp]
  intro Λ hΛ1 hΛtop hthr
  refine ⟨B, hB, j, hj, ?_⟩
  have hΛstep : Λ * (d ^ (-(3 * ν)) * X) ≤ d ^ (-ν) * Y := by
    calc
      Λ * (d ^ (-(3 * ν)) * X) ≤ Λ * ((Θ : ENNReal) * (C₁ : ENNReal) * Y) :=
        mul_le_mul_of_nonneg_left hidem (by positivity : 0 ≤ Λ)
      _ = (Λ * (C₁ : ENNReal) * (Θ : ENNReal)) * Y := by
        simp [mul_assoc, mul_comm]
      _ ≤ d ^ (-ν) * Y := mul_le_mul_of_nonneg_right hthr (by positivity : 0 ≤ Y)
  have hcancel : d ^ (3 * ν) * d ^ (-(3 * ν)) = 1 := by
    rw [← ENNReal.rpow_add (3 * ν) (-(3 * ν)) hd0 hdtop]
    rw [show ((3 : ℝ) * ν + (-(3 * ν)) = 0) by ring, ENNReal.rpow_zero]
  have hpow : d ^ (3 * ν) * d ^ (-ν) = d ^ (2 * ν) := by
    rw [← ENNReal.rpow_add (3 * ν) (-ν) hd0 hdtop]
    congr 1
    ring
  have hΛX : Λ * X ≤ d ^ (2 * ν) * Y := by
    calc
      Λ * X = d ^ (3 * ν) * (Λ * (d ^ (-(3 * ν)) * X)) := by
        rw [show d ^ (3 * ν) * (Λ * (d ^ (-(3 * ν)) * X))
            = (d ^ (3 * ν) * d ^ (-(3 * ν))) * (Λ * X) by ring, hcancel, one_mul]
      _ ≤ d ^ (3 * ν) * (d ^ (-ν) * Y) :=
        mul_le_mul_of_nonneg_left hΛstep (by positivity : 0 ≤ d ^ (3 * ν))
      _ = d ^ (2 * ν) * Y := by rw [← mul_assoc, hpow]
  calc
    Λ * (cfg.δ : ENNReal) ^ (2 * cfg.β) * volume (bd.Wb j).carrier = Λ * X := by
      dsimp [X, d]; ring
    _ ≤ d ^ (2 * ν) * Y := hΛX
    _ = (cfg.δ : ENNReal) ^ (2 * (cfg.ϱ * cfg.β * τ / 8)) *
          volume ((⋃ p ∈ (bd.segs B).filter fun p => bd.blk p = j, (bd.Y p).shade) ∩
            (bd.Wb j).carrier) *
          (cfg.a : ENNReal) ^ (2 * cfg.β) := by
      dsimp [Y, d, na, ν]; ring

/-! ### Sufficiency of the threshold at named constants -/

/-- The thick-case multiplicity bound from a threshold at named constants.
A threshold quantified over every pair `(Θ, C₁)` allows arbitrarily
large witnesses to defeat the required bound, as shown by
`no_thickDensityThresholds_of_thick`. Here the hypothesis is instead
the direct inequality `C² * K(C₀) * C₁' * Θ' ≤ δ^(-ν)` at the
two named witnesses. `Kakeya.VeryNotSticky.exists_denseInBody_at`
then yields the multiplicity conclusion.

The side condition `1 ≤ Λ` is derived from `1 ≤ C` and
`8π(2√3 + C₀)^3 ≥ 1` for `C₀ ≥ 1`, rather than assumed
separately. -/
theorem goalMult_of_a_ge_of_thresholds_at (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    {thr : ScaleThresholds} (hthr : cfg.δ ≤ thr.aScale (cfg.ϱ * cfg.β * τ / 8))
    (bd : BallData cfg) (hβ1 : cfg.β ≤ 1) (hthick : cfg.δ ^ (1 - τ) ≤ cfg.a)
    (hδ₂ : (bd.Cbias : ENNReal) * (((48 * bd.C₀ ^ 6) ^ 3 : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(τ * cfg.ϱ)))
    {CP Θ₀ C_NC : NNReal} (hCP : 1 ≤ CP) (hΘ₀ : 1 ≤ Θ₀) {ηF : ℝ} (hηF : 0 < ηF)
    (hbudget : PlankFrostmanUsable bd τ CP C_NC ηF)
    (hpres : ThickPlankPresentable bd CP Θ₀ C_NC)
    (hdens : ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
      cfg.AScaleData C cfg.a (cfg.ϱ * cfg.β * τ / 8) →
      C ^ 2 * ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) *
          (denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β : ENNReal) *
          (denseInBodyΘ CP Θ₀ bd.Cbias : ENNReal) ≤
        (cfg.δ : ENNReal) ^ (-(cfg.ϱ * cfg.β * τ / 8))) :
    cfg.goalMult (cfg.ϱ * cfg.β * τ / 8) := by
  obtain ⟨C, hC1, hCtop, -, hdata, himp⟩ := goalMult_of_a_ge_of_goalDensity cfg params hthr
  have hK1 : (1 : ℝ) ≤ 8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hs : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    have hC₀ : (1 : ℝ) ≤ (bd.C₀ : ℝ) := by exact_mod_cast bd.hC₀
    have hbase : (1 : ℝ) ≤ 2 * Real.sqrt 3 + (bd.C₀ : ℝ) := by linarith
    have hcube : (1 : ℝ) ≤ (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3 := one_le_pow₀ hbase
    have h8pi : (24 : ℝ) ≤ 8 * Real.pi := by linarith
    calc
      (1 : ℝ) ≤ 24 * 1 := by norm_num
      _ ≤ (8 * Real.pi) * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3 :=
          mul_le_mul h8pi hcube (by norm_num) (by linarith)
      _ = 8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3 := by ring
  have hKe : (1 : ENNReal) ≤
      ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hK1
  have hCsq : (1 : ENNReal) ≤ C ^ 2 := one_le_pow₀ hC1
  have hΛ1 : (1 : ENNReal) ≤
      C ^ 2 * ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) :=
    one_le_mul hCsq hKe
  have hΛtop : C ^ 2 * ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3)
      ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.pow_ne_top hCtop) ENNReal.ofReal_ne_top
  have h := exists_denseInBody_at cfg params bd hβ1 hthick hδ₂ hCP hΘ₀ hηF hbudget hpres
    (C ^ 2 * ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3))
    hΛ1 hΛtop (hdens C hC1 hCtop hdata)
  exact himp (goalDensity_of_denseInBody cfg bd (K := C ^ 2)
    (ν := cfg.ϱ * cfg.β * τ / 8) h)

/-! ### A universal comparison-constant threshold is impossible

Consider a condition beginning with
`∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ → cfg.AScaleData C cfg.a ν →`
and requiring `C² * K(C₀) * C₁' * Θ' ≤ δ^(-ν)` at fixed positive
factors. Since `AScaleData` is upward closed in `C`, this condition is
false whenever an admissible `C` exists.
`goalMult_of_a_ge_of_goalDensity` supplies such a constant under the
scale threshold. The two theorems below establish the obstruction first
abstractly and then for this density-threshold expression.

The applicable estimate is a threshold at the particular comparison
constant supplied by the scale argument, as used in
`Kakeya.VeryNotSticky.goalMult_of_denseInBody_at`. Its bound must be
controlled explicitly, rather than quantified over all admissible constants.
-/

/-- **A `δ`-free bound cannot be asked of every admissible comparison constant.**

`Kakeya.VeryNotSticky.AScaleData` is upward-closed in `C`
(`Kakeya.VeryNotSticky.AScaleData.mono`), so if it holds at one finite `C ≥ 1` it holds at every
larger one; a demand `C² X ≤ Y` with `X ≠ 0` and `Y ≠ ⊤` then fails at `C` large. -/
theorem no_forall_aScaleData_le {cfg : VeryNotSticky.{u}} {r : NNReal} {ν : ℝ}
    {X Y : ENNReal} (hX0 : X ≠ 0) (hXtop : X ≠ ⊤) (hYtop : Y ≠ ⊤)
    (hsome : ∃ C : ENNReal, 1 ≤ C ∧ C ≠ ⊤ ∧ cfg.AScaleData C r ν)
    (h : ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ → cfg.AScaleData C r ν → C ^ 2 * X ≤ Y) : False := by
  obtain ⟨C₁, hC₁, hC₁top, hdata⟩ := hsome
  set C : ENNReal := max C₁ (Y * X⁻¹ + 1) with hCdef
  have hXinv_top : X⁻¹ ≠ ⊤ := by simpa using hX0
  have hCtop : C ≠ ⊤ := by
    rw [hCdef]
    exact (max_lt hC₁top.lt_top
      (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top hYtop.lt_top hXinv_top.lt_top,
        ENNReal.one_lt_top⟩)).ne
  have hC1 : 1 ≤ C := le_max_of_le_left hC₁
  have hCdata : cfg.AScaleData C r ν := AScaleData.mono cfg (le_max_left _ _) hdata
  have hle := h C hC1 hCtop hCdata
  have hCC : C ≤ C ^ 2 := by
    calc C = C ^ 1 := (pow_one C).symm
      _ ≤ C ^ 2 := pow_le_pow_right₀ hC1 (by norm_num)
  have hbig : Y < C * X := by
    calc Y = Y * X⁻¹ * X := by
          rw [mul_assoc, ENNReal.inv_mul_cancel hX0 hXtop, mul_one]
      _ < (Y * X⁻¹ + 1) * X := by
          rw [mul_comm (Y * X⁻¹) X, mul_comm (Y * X⁻¹ + 1) X]
          exact ENNReal.mul_lt_mul_right hX0 hXtop
            (ENNReal.lt_add_right (ENNReal.mul_ne_top hYtop hXinv_top) one_ne_zero)
      _ ≤ C * X := by
          gcongr
          exact le_max_right _ _
  have : C * X ≤ Y := le_trans (by gcongr) hle
  exact absurd (lt_of_lt_of_le hbig this) (lt_irrefl Y)

/-- A density threshold universal in the comparison constant is false.
`goalMult_of_a_ge_of_goalDensity` supplies the admissible `C` needed by
`no_forall_aScaleData_le` from the scale threshold of the thick case.
Thus `hthr` is the only additional input to this contradiction. -/
theorem no_densityAfter_forall_C (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    {thr : ScaleThresholds} (hthr : cfg.δ ≤ thr.aScale (cfg.ϱ * cfg.β * τ / 8))
    (bd : BallData cfg) {CP Θ : NNReal} (hCP : 1 ≤ CP) (hΘ : 1 ≤ Θ)
    (h : ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
        cfg.AScaleData C cfg.a (cfg.ϱ * cfg.β * τ / 8) →
      C ^ 2 * ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) *
          (denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β : ENNReal) *
          (denseInBodyΘ CP Θ bd.Cbias : ENNReal) ≤
        (cfg.δ : ENNReal) ^ (-(cfg.ϱ * cfg.β * τ / 8))) : False := by
  obtain ⟨C, hC1, hCtop, -, hdata, _himp⟩ := goalMult_of_a_ge_of_goalDensity cfg params hthr
  set K : ENNReal := ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) with hK
  set X : ENNReal := K * (denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β : ENNReal) *
    (denseInBodyΘ CP Θ bd.Cbias : ENNReal) with hX
  have hKpos : (0 : ℝ) < 8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3 := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have hs : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    have hC₀ : (1 : ℝ) ≤ (bd.C₀ : ℝ) := by exact_mod_cast bd.hC₀
    have hbase : (0 : ℝ) < 2 * Real.sqrt 3 + (bd.C₀ : ℝ) := by linarith
    positivity
  have hK0 : K ≠ 0 := by
    rw [hK]
    simpa using hKpos
  have hKtop : K ≠ ⊤ := by rw [hK]; exact ENNReal.ofReal_ne_top
  have hC₁0 : ((denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β : NNReal) : ENNReal) ≠ 0 := by
    have h1 : (1 : NNReal) ≤ denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β :=
      one_le_denseInBodyC₁ _ _ _
    simpa using (ne_of_gt (lt_of_lt_of_le zero_lt_one h1))
  have hΘ0 : ((denseInBodyΘ CP Θ bd.Cbias : NNReal) : ENNReal) ≠ 0 := by
    have h1 : (1 : NNReal) ≤ denseInBodyΘ CP Θ bd.Cbias :=
      one_le_denseInBodyΘ hCP hΘ bd.hCbias
    simpa using (ne_of_gt (lt_of_lt_of_le zero_lt_one h1))
  have hX0 : X ≠ 0 := by
    rw [hX]
    exact mul_ne_zero (mul_ne_zero hK0 hC₁0) hΘ0
  have hXtop : X ≠ ⊤ := by
    rw [hX]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hKtop ENNReal.coe_ne_top) ENNReal.coe_ne_top
  have hδ0 : (cfg.δ : ENNReal) ≠ 0 := by simpa using (ne_of_gt cfg.hδ)
  have hYtop : (cfg.δ : ENNReal) ^ (-(cfg.ϱ * cfg.β * τ / 8)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hδ0 ENNReal.coe_ne_top
  refine no_forall_aScaleData_le (cfg := cfg) (r := cfg.a) (ν := cfg.ϱ * cfg.β * τ / 8)
    hX0 hXtop hYtop ⟨C, hC1, hCtop, hdata⟩ ?_
  intro C' hC'1 hC'top hC'data
  have := h C' hC'1 hC'top hC'data
  rw [hX, hK]
  calc C' ^ 2 * (ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) *
          (denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β : ENNReal) *
          (denseInBodyΘ CP Θ bd.Cbias : ENNReal))
      = C' ^ 2 * ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) *
          (denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β : ENNReal) *
          (denseInBodyΘ CP Θ bd.Cbias : ENNReal) := by ring
    _ ≤ _ := this

/-- **The honest per-`C` consumer step**, the one thing the thick case actually needs from a
repaired `density` field.

No quantifier over `C`: the caller hands over the comparison constant the scale layer produced,
its `AScaleData`, the implication `goalDensity (C²) → goalMult` that came with it, and the
threshold **at that `C`**. This is satisfiable — unlike its `∀ C` wrapper
`Kakeya.VeryNotSticky.goalMult_of_a_ge_of_thresholds_at`, whose hypothesis
`Kakeya.VeryNotSticky.no_densityAfter_forall_C` refutes. -/
theorem goalMult_of_denseInBody_at (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (bd : BallData cfg) (hβ1 : cfg.β ≤ 1) (hthick : cfg.δ ^ (1 - τ) ≤ cfg.a)
    (hδ₂ : (bd.Cbias : ENNReal) * (((48 * bd.C₀ ^ 6) ^ 3 : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(τ * cfg.ϱ)))
    {CP Θ₀ C_NC : NNReal} (hCP : 1 ≤ CP) (hΘ₀ : 1 ≤ Θ₀) {ηF : ℝ} (hηF : 0 < ηF)
    (hbudget : PlankFrostmanUsable bd τ CP C_NC ηF)
    (hpres : ThickPlankPresentable bd CP Θ₀ C_NC)
    {C : ENNReal} (hC1 : 1 ≤ C) (hCtop : C ≠ ⊤)
    (himp : cfg.goalDensity (C ^ 2) cfg.a (cfg.ϱ * cfg.β * τ / 8) →
      cfg.goalMult (cfg.ϱ * cfg.β * τ / 8))
    (hthrC : C ^ 2 * ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) *
        (denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β : ENNReal) *
        (denseInBodyΘ CP Θ₀ bd.Cbias : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(cfg.ϱ * cfg.β * τ / 8))) :
    cfg.goalMult (cfg.ϱ * cfg.β * τ / 8) := by
  have hK1 : (1 : ℝ) ≤ 8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3 := by
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hs : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    have hC₀ : (1 : ℝ) ≤ (bd.C₀ : ℝ) := by exact_mod_cast bd.hC₀
    have hbase : (1 : ℝ) ≤ 2 * Real.sqrt 3 + (bd.C₀ : ℝ) := by linarith
    have hcube : (1 : ℝ) ≤ (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3 := one_le_pow₀ hbase
    have h8pi : (24 : ℝ) ≤ 8 * Real.pi := by linarith
    calc
      (1 : ℝ) ≤ 24 * 1 := by norm_num
      _ ≤ (8 * Real.pi) * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3 :=
          mul_le_mul h8pi hcube (by norm_num) (by linarith)
      _ = 8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3 := by ring
  have hKe : (1 : ENNReal) ≤
      ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hK1
  have hCsq : (1 : ENNReal) ≤ C ^ 2 := one_le_pow₀ hC1
  have hΛ1 : (1 : ENNReal) ≤
      C ^ 2 * ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) :=
    one_le_mul hCsq hKe
  have hΛtop : C ^ 2 * ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3)
      ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.pow_ne_top hCtop) ENNReal.ofReal_ne_top
  have h := exists_denseInBody_at cfg params bd hβ1 hthick hδ₂ hCP hΘ₀ hηF hbudget hpres
    (C ^ 2 * ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3))
    hΛ1 hΛtop hthrC
  exact himp (goalDensity_of_denseInBody cfg bd (K := C ^ 2)
    (ν := cfg.ϱ * cfg.β * τ / 8) h)

/-! ### The named pair is a legal pair of witnesses -/

/-- The named form implies the existing existential form of
`Kakeya.VeryNotSticky.exists_denseInBodyRaw`; the firing control that
`Kakeya.VeryNotSticky.denseInBodyΘ` and `Kakeya.VeryNotSticky.denseInBodyC₁` really are
witnesses for it. -/
theorem exists_denseInBodyRaw_of_at {cfg : VeryNotSticky.{u}} (bd : BallData cfg) {τ : ℝ}
    (hτ : 0 < τ) (hβ1 : cfg.β ≤ 1) {CP Θ₀ C_NC : NNReal} (hCP : 1 ≤ CP) (hΘ₀ : 1 ≤ Θ₀)
    {ηF : ℝ} (hηF : 0 < ηF)
    (hbudget : PlankFrostmanUsable bd τ CP C_NC ηF)
    (hpres : ThickPlankPresentable bd CP Θ₀ C_NC)
    (hPcard : ∀ B ∈ bd.bs, ∀ p₀ ∈ bd.segs B,
      ((cfg.a : ENNReal) / (cfg.δ : ENNReal)) ^ (2 + cfg.ϱ) ≤
        ((((bd.segs B).filter fun p => bd.blk p = bd.blk p₀).card : ℕ) : ENNReal)) :
    ∃ Θ C₁ : NNReal, 1 ≤ Θ ∧ 1 ≤ C₁ ∧
      ∃ B ∈ bd.bs, ∃ j ∈ bd.bodies B,
        DenseInBodyRaw bd (cfg.ϱ * cfg.β * τ / 8) Θ C₁ B j :=
  ⟨_, _, one_le_denseInBodyΘ hCP hΘ₀ bd.hCbias,
    one_le_denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β,
    exists_denseInBodyRaw_at bd hτ hβ1 hCP hΘ₀ hηF hbudget hpres hPcard⟩

/-- The named form implies the existing existential form of
`Kakeya.VeryNotSticky.exists_denseInBody`. -/
theorem exists_denseInBody_of_at (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (bd : BallData cfg) (hβ1 : cfg.β ≤ 1) (hthick : cfg.δ ^ (1 - τ) ≤ cfg.a)
    (hδ₂ : (bd.Cbias : ENNReal) * (((48 * bd.C₀ ^ 6) ^ 3 : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(τ * cfg.ϱ)))
    {CP Θ₀ C_NC : NNReal} (hCP : 1 ≤ CP) (hΘ₀ : 1 ≤ Θ₀) {ηF : ℝ} (hηF : 0 < ηF)
    (hbudget : PlankFrostmanUsable bd τ CP C_NC ηF)
    (hpres : ThickPlankPresentable bd CP Θ₀ C_NC) :
    ∃ Θ C₁ : NNReal, 1 ≤ Θ ∧ 1 ≤ C₁ ∧
      ∀ Λ : ENNReal, 1 ≤ Λ → Λ ≠ ⊤ →
        Λ * (C₁ : ENNReal) * (Θ : ENNReal) ≤
          (cfg.δ : ENNReal) ^ (-(cfg.ϱ * cfg.β * τ / 8)) →
        ∃ B ∈ bd.bs, ∃ j ∈ bd.bodies B,
          Λ * (cfg.δ : ENNReal) ^ (2 * cfg.β) * volume (bd.Wb j).carrier ≤
            (cfg.δ : ENNReal) ^ (2 * (cfg.ϱ * cfg.β * τ / 8)) *
              volume ((⋃ p ∈ (bd.segs B).filter fun p => bd.blk p = j, (bd.Y p).shade) ∩
                (bd.Wb j).carrier) *
              (cfg.a : ENNReal) ^ (2 * cfg.β) :=
  ⟨_, _, one_le_denseInBodyΘ hCP hΘ₀ bd.hCbias,
    one_le_denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β,
    exists_denseInBody_at cfg params bd hβ1 hthick hδ₂ hCP hΘ₀ hηF hbudget hpres⟩

/-! ### F33 — the re-cut of `Kakeya.VeryNotSticky.ThickDensityThresholds.density`

The bare, `C`-free threshold and the thick-case entry point that reads it. Both live here,
downstream of `goalMult_of_denseInBody_at`, because that is the first module in which the
named-constant density estimate is available; `MainLemma2/ThickCase.lean`, where the field
is declared, is upstream of it. -/

/-- **The bare, `C`-free threshold suffices**: with it the thick branch reaches
`cfg.goalMult (ϱβτ/8)` and `Kakeya.VeryNotSticky.ThickDensityThresholds.density` is never read. -/
theorem goalMult_of_a_ge_of_bareThreshold (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (bd : BallData cfg) (hβ1 : cfg.β ≤ 1) (hthick : cfg.δ ^ (1 - τ) ≤ cfg.a)
    {thr : ScaleThresholds} (hthr : cfg.δ ≤ thr.aScale (cfg.ϱ * cfg.β * τ / 8))
    (hδ₂ : (bd.Cbias : ENNReal) * (((48 * bd.C₀ ^ 6) ^ 3 : NNReal) : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(τ * cfg.ϱ)))
    {CP Θ₀ C_NC : NNReal} (hCP : 1 ≤ CP) (hΘ₀ : 1 ≤ Θ₀) {ηF : ℝ} (hηF : 0 < ηF)
    (hbudget : PlankFrostmanUsable bd τ CP C_NC ηF)
    (hpres : ThickPlankPresentable bd CP Θ₀ C_NC)
    (hbare : ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) *
        (denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β : ENNReal) *
        (denseInBodyΘ CP Θ₀ bd.Cbias : ENNReal) ≤
      (cfg.δ : ENNReal) ^ (-(cfg.ϱ * cfg.β * τ / 8 - cfg.η))) :
    cfg.goalMult (cfg.ϱ * cfg.β * τ / 8) := by
  obtain ⟨C, hC1, hCtop, hCsq, hdata, himp⟩ := goalMult_of_a_ge_of_goalDensity cfg params hthr
  refine goalMult_of_denseInBody_at cfg params bd hβ1 hthick hδ₂ hCP hΘ₀ hηF hbudget hpres
    hC1 hCtop himp ?_
  have hδ0 : (cfg.δ : ENNReal) ≠ 0 := by
    simpa using (ENNReal.coe_pos.mpr cfg.hδ).ne'
  have hδtop : (cfg.δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsplit : (cfg.δ : ENNReal) ^ (-cfg.η) *
      (cfg.δ : ENNReal) ^ (-(cfg.ϱ * cfg.β * τ / 8 - cfg.η)) =
      (cfg.δ : ENNReal) ^ (-(cfg.ϱ * cfg.β * τ / 8)) := by
    rw [← ENNReal.rpow_add _ _ hδ0 hδtop]
    congr 1
    ring
  calc C ^ 2 * ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) *
        (denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β : ENNReal) *
        (denseInBodyΘ CP Θ₀ bd.Cbias : ENNReal)
      = C ^ 2 * (ENNReal.ofReal (8 * Real.pi * (2 * Real.sqrt 3 + (bd.C₀ : ℝ)) ^ 3) *
          (denseInBodyC₁ CP (cfg.ϱ * cfg.β * τ / 8) cfg.β : ENNReal) *
          (denseInBodyΘ CP Θ₀ bd.Cbias : ENNReal)) := by ring
    _ ≤ (cfg.δ : ENNReal) ^ (-cfg.η) *
          (cfg.δ : ENNReal) ^ (-(cfg.ϱ * cfg.β * τ / 8 - cfg.η)) := by
        exact mul_le_mul' hCsq hbare
    _ = (cfg.δ : ENNReal) ^ (-(cfg.ϱ * cfg.β * τ / 8)) := hsplit

/-- [Main Lemma 2, thick case] (blueprint `lem:ml2thick`).
In the configuration `cfg` of Subsection `subsecproofoverview`, suppose we are in the
*thick case*, i.e. the biased factoring dimension satisfies `a ≥ δ^{1-τ}`. Then, under the
parameter budgets of Definition `hyp:ml2params` and the thick-case scale thresholds, the
density estimate `eqgoaldens` holds and hence the goal `μ(T, Y) ≤ δ^ν |T|^β` follows with a
positive gain (the blueprint value is `ν = ϱ β τ / 8`, which is what the proof produces).

**Why the binders are here.** An earlier version of this statement took only `cfg`, `0 < τ`
and the thickness hypothesis, and produced the gain existentially. That version is **not
provable**, and the obstruction is not a missing proof but a missing hypothesis:
`Kakeya.VeryNotSticky` constrains its exponents `η`, `ϱ`, `exscal` **only by positivity** —
its fields `hη`, `hϱ`, `hexscal` say `0 < ·` and nothing more — so
`Kakeya.VeryNotSticky.CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ'` is not derivable
from `cfg` for any choice of `τ'`. The cleanest witness is the field
`Kakeya.VeryNotSticky.CaseParams.densityBias`, `2^20 η < ϱ`, which mentions neither `τ` nor
`τ'`, so no choice of exponent by the prover can rescue it: at `cfg.η = 1`, `cfg.ϱ = 1/1000`
it is false, and `slabDensity` (`2η < exscal`), `slabBias` (`2^20 ϱ < exscal`) and `scale`
(`exscal < 1/2`) fail in exactly the same way. Nor is `bd` derivable: Configuration
`hyp:ml2setup`(C2)–(C5) — the `r₁`-ball cover with its subordinate partition, the per-ball
tube segments and the factoring blocks with their Frostman and biased-density bounds — is
constructed *alongside* `cfg` by blueprint `lem:ml2setupexists`, not from it, and the fields
`Kakeya.VeryNotSticky.BallData.segs_nonempty` and `blk_mem` forbid a vacuous witness.

So the budgets travel *beside* the configuration and never inside it. That is the section's
own design, and it is visible in the signature of
`Kakeya.VeryNotSticky.exists_setup_caseSideData`, which takes `params` as an external binder
and returns a configuration satisfying `cfg.exscal = exscal ∧ cfg.ϱ = ϱ ∧ cfg.η = η`. Every
other statement of the case split follows it — `Kakeya.VeryNotSticky.exists_goalMult` carries
exactly `params`, `bd` and `hdens` — and the old binder list of this declaration was the one
statement in the section that forgot to carry its budgets. It now carries the same three, so
that it is a *theorem* about the thick case rather than an unprovable homonym of one.

The separate hypothesis `0 < τ` of the old signature is dropped as redundant: it is the field
`Kakeya.VeryNotSticky.CaseParams.hτ` of `params`.

The proof is `Kakeya.VeryNotSticky.goalMult_of_a_ge_of_thickData` at the fields of `hdens`,
the thick-case guard being what unlocks its two guarded fields `plankF` and `density`. -/
theorem goalMult_of_a_ge (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ')
    (bd : BallData cfg) {CP Θ C_NC : NNReal} {ηF : ℝ}
    (hdens : ThickDensityThresholds cfg bd τ CP Θ C_NC ηF)
    (hthick : cfg.δ ^ (1 - τ) ≤ cfg.a) :
    ∃ ν > (0 : ℝ), cfg.goalMult ν := by
  obtain ⟨thr, hthr⟩ := exists_scaleThresholds_of_le_one cfg.hδ1
  have hτ : 0 < τ := params.hτ
  have hϱ : 0 < cfg.ϱ := cfg.hϱ
  have hβ : 0 < cfg.β := cfg.hβ
  refine ⟨cfg.ϱ * cfg.β * τ / 8, by positivity, ?_⟩
  exact goalMult_of_a_ge_of_bareThreshold cfg params bd cfg.hβ1 hthick (hthr _) hdens.bias
    hdens.hCP hdens.hΘ hdens.hηF (hdens.plankF hthick) (hdens.plankPres hthick)
    (hdens.density hthick)

end Kakeya.VeryNotSticky

end

end
