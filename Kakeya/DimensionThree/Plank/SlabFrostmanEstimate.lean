/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabFibreFrostman
public import Kakeya.DimensionThree.Plank.SlabFrostmanInput

/-!
# The per-slab Frostman volume lower bound of GWZ Lemma 6.4

This module proves `Plank.frostmanSlabUnionVolumeLowerBound` (stated in
`Kakeya.DimensionThree.Plank.FrostmanPlankGeometry`), the per-slab analysis step of GWZ Lemma 6.4. Every
geometric input is already available:

* `Plank.exists_pairwiseED_subfibre_package` extracts the genuinely pairwise essentially distinct
  sub-fibre together with its two retention losses, both governed by the single absolute `MED`;
* `Plank.isFrostmanIn_slabFibreTubes_sub` produces the Frostman hypothesis for that sub-fibre;
* `Plank.sum_shade_le_of_multiplicity_le` converts the resulting multiplicity bound into the
  union-volume lower bound, with the affine Jacobian of the slab normalisation cancelling exactly;
* `Plank.sum_volume_carrier_shadeBody` supplies the exact total carrier volume
  `Cfib³ · |fibre| · 8 θ b²`, so the fullness hypothesis becomes a shade-*mass* lower bound.

Nothing here re-derives geometry, and **no cardinality comparison between the sub-fibre and the
fibre is used**: the extraction loss enters only through the weighted shade mass.

## The scales

Writing `𝒯` for the ambient representative ensemble, `fibre ⊆ 𝒯` for the slab fibre and
`sub ⊆ fibre` for the extracted pairwise essentially distinct sub-fibre, the tube estimate
`Kakeya.FrostmanEstimate.multiplicity_bound_tau_isFrostmanIn` is run with

* `δ_KF` is `b / 8`: the *physical* tube radius, since `Plank.slabFibreTubes` lands in
  `ShadedTube (b/8)`;
* `τ_KF` is `a / 8`: the *analytic* scale, carrying both the `τ^(-ε/2)` loss and the fullness
  threshold;
* `CFtube` is `Plank.perSlabCFtube`: the induced tube Frostman constant;
* the family is `sub`, of cardinality `|sub|`, which is never compared with `|fibre|`.

`0 < τ_KF` holds because `0 < a`, and `τ_KF ≤ δ_KF` because `a ≤ b`. The physical and the analytic
scale are genuinely different — `a` may be far smaller than `b` — and that is exactly why the
single-scale form of GWZ Lemma 3.9 is unusable here.

## The `|sub|` cancellation

`Plank.perSlabCFtube` carries `|sub|` in its denominator, and the tube estimate contributes the
factor `CFtube^(1-β/2) · (|sub| · δ_KF²)^(1-β/2) = (CFtube · |sub| · δ_KF²)^(1-β/2)`. The product
`CFtube · |sub| · δ_KF²` is `|sub|`-free by `Plank.perSlabCFtube_mul_card_mul_sq`; that lemma is the
whole of the cancellation and is stated as an *equality*, not buried in an `nlinarith` block.

## Bookkeeping of the exponents

`Plank.perSlabScalar` is the single scalar inequality of the per-slab step. Its two sides are
literally the target and the shade mass, and the cancellations it performs are

* `CF^(β/2-1) · CF^(1-β/2) = 1` and `|𝒯|^(β/2-1) · |𝒯|^(1-β/2) = 1` — this is why the tube Frostman
  constant had to keep `CF` and `|𝒯|` free;
* `θ^(β/2) · θ^(1-β/2) = θ`, matching the single `θ` in the carrier volume `8 θ b²`;
* `b^(2β) · (b²)^(β/2) · b^(-2β) · (b²)^(1-β/2) = b²`, matching the `b²` in the carrier volume;
* `a^ε · a^(-ε/2) = a^(ε/2) ≤ a^(4η)`, which is where `4η ≤ ε/2` is used.

Only fixed constants survive, and they are absorbed into `Plank.perSlabLoss`, the lemma's `K`.
-/

@[expose] public section

open MeasureTheory Kakeya Filter Topology
open scoped NNReal ENNReal Real

noncomputable section

namespace Plank

variable {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1}

/-! ### Fixed constants -/

/-- The volume of the closed unit ball of `ℝ³`, as an `ℝ≥0`. It is a fixed positive finite
constant; no closed form is needed. -/
def unitBallVol : ℝ≥0 :=
  (volume (ConvexSpaceBody.closedUnitBall :
    ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))).carrier).toNNReal

theorem unitBallVol_pos : 0 < unitBallVol := by
  rw [unitBallVol]
  exact ENNReal.toNNReal_pos
    (ne_of_gt (ConvexSpaceBody.closedUnitBall_volume_pos (E := EuclideanSpace ℝ (Fin 3))))
    (ConvexSpaceBody.closedUnitBall.isCompact.measure_ne_top)

theorem coe_unitBallVol :
    ((unitBallVol : ℝ≥0) : ENNReal)
      = volume (ConvexSpaceBody.closedUnitBall :
          ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))).carrier := by
  rw [unitBallVol]
  exact ENNReal.coe_toNNReal (ConvexSpaceBody.closedUnitBall.isCompact.measure_ne_top)

/-- **The fixed part of the induced tube Frostman constant.**

`Plank.isFrostmanIn_slabFibreTubes_sub` needs
`fibreTubeLoss Cfib · Cfib³ · (Cloc · CF · |𝒯| · 8θb²) · |B₁| ≤ CFtube · ∑_{sub} |T Q|`, and
`Tube.le_volume` gives `∑_{sub} |T Q| ≥ |sub| · c₃ · (b/8)²` with `c₃ = Tube.le_volume.c 3`. The
two `b²` cancel and the numerical factor is `8 · 64 = 512`. -/
def perSlabTubeConst (Cfib Cloc : ℝ≥0) : ℝ≥0 :=
  512 * fibreTubeLoss Cfib * Cfib ^ 3 * Cloc * unitBallVol / Tube.le_volume.c 3

theorem perSlabTubeConst_pos (Cfib Cloc : ℝ≥0) (hCfib : 1 ≤ Cfib) (hCloc : 1 ≤ Cloc) :
    0 < perSlabTubeConst Cfib Cloc := by
  unfold perSlabTubeConst
  rw [div_eq_mul_inv]
  have hfib : 0 < fibreTubeLoss Cfib := lt_of_lt_of_le zero_lt_one (one_le_fibreTubeLoss Cfib)
  have hcf1 : 0 < Cfib := lt_of_lt_of_le zero_lt_one hCfib
  have hcl1 : 0 < Cloc := lt_of_lt_of_le zero_lt_one hCloc
  have hunit : 0 < unitBallVol := unitBallVol_pos
  have hc : 0 < Tube.le_volume.c 3 := Tube.le_volume.c_pos 3
  positivity

/-- **The induced tube Frostman constant of one slab fibre.**

The `|sub|` denominator is what the tube estimate's factor
`CFtube^(1-β/2) · (|sub| · (b/8)²)^(1-β/2)` cancels; see
`Plank.perSlabCFtube_mul_card_mul_sq`. -/
def perSlabCFtube (Cfib Cloc : ℝ≥0) (CF : ENNReal) (mT nsub : ℕ) (θ : ℝ≥0) : ENNReal :=
  ((perSlabTubeConst Cfib Cloc : ℝ≥0) : ENNReal) * CF * (mT : ENNReal) * (θ : ENNReal)
    * ((nsub : ENNReal))⁻¹

/-- **The `|sub|` cancellation, in isolation.**

`CFtube · |sub| · (b/8)² = (perSlabTubeConst / 64) · CF · |𝒯| · θ · b²`: the sub-fibre cardinality
disappears exactly, leaving a quantity in which only `CF`, `|𝒯|`, `θ` and `b` occur. This is the
identity that makes the tube estimate's `(|sub| · δ²)^(1-β/2)` factor harmless. -/
theorem perSlabCFtube_mul_card_mul_sq (Cfib Cloc : ℝ≥0) (CF : ENNReal) (hCFtop : CF ≠ ⊤)
    (mT nsub : ℕ) (hnsub : nsub ≠ 0) (θ b : ℝ≥0) :
    perSlabCFtube Cfib Cloc CF mT nsub θ * ((nsub : ENNReal) * ((b / 8 : ℝ≥0) : ENNReal) ^ 2)
      = ((perSlabTubeConst Cfib Cloc / 64 : ℝ≥0) : ENNReal) * CF * (mT : ENNReal)
          * (θ : ENNReal) * ((b : ℝ≥0) : ENNReal) ^ 2 := by
  unfold perSlabCFtube
  have hN0 : (nsub : ENNReal) ≠ 0 := by
    exact_mod_cast hnsub
  have hNtop : (nsub : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top nsub
  have hNinv : ((nsub : ENNReal))⁻¹ * (nsub : ENNReal) = 1 :=
    ENNReal.inv_mul_cancel hN0 hNtop
  have hbd : ((b / 8 : ℝ≥0) : ENNReal) ^ 2 = ((b : ℝ≥0) : ENNReal) ^ 2 / (64 : ENNReal) := by
    rw [ENNReal.coe_div (by norm_num : (8 : ℝ≥0) ≠ 0)]
    rw [ENNReal.div_eq_inv_mul]
    calc
      ((8 : ENNReal)⁻¹ * ((b : ℝ≥0) : ENNReal)) ^ 2
          = (8 : ENNReal)⁻¹ ^ 2 * ((b : ℝ≥0) : ENNReal) ^ 2 := by
            exact mul_pow _ _ _
      _ = ((8 : ENNReal) ^ 2)⁻¹ * ((b : ℝ≥0) : ENNReal) ^ 2 := by
            rw [← ENNReal.inv_pow]
      _ = (64 : ENNReal)⁻¹ * ((b : ℝ≥0) : ENNReal) ^ 2 := by
            norm_num
      _ = ((b : ℝ≥0) : ENNReal) ^ 2 / (64 : ENNReal) := by
            rw [ENNReal.div_eq_inv_mul]
  rw [hbd]
  rw [ENNReal.coe_div (by norm_num : (64 : ℝ≥0) ≠ 0)]
  calc
    ((perSlabTubeConst Cfib Cloc : ENNReal) * CF * (mT : ENNReal) * (θ : ENNReal)
        * ((nsub : ENNReal))⁻¹ * ((nsub : ENNReal) * (((b : ℝ≥0) : ENNReal) ^ 2 / (64 : ENNReal))))
      = ((perSlabTubeConst Cfib Cloc : ENNReal) * CF * (mT : ENNReal) * (θ : ENNReal))
          * ((((nsub : ENNReal))⁻¹ * (nsub : ENNReal))
            * (((b : ℝ≥0) : ENNReal) ^ 2 / (64 : ENNReal))) := by
        ac_rfl
    _ = ((perSlabTubeConst Cfib Cloc : ENNReal) * CF * (mT : ENNReal) * (θ : ENNReal))
          * (((b : ℝ≥0) : ENNReal) ^ 2 / (64 : ENNReal)) := by
        rw [hNinv]
        simp
    _ = (perSlabTubeConst Cfib Cloc : ENNReal) * CF * (mT : ENNReal) * (θ : ENNReal)
          * ((b : ℝ≥0) : ENNReal) ^ 2 * (64 : ENNReal)⁻¹ := by
        rw [ENNReal.div_eq_inv_mul]
        ac_rfl
    _ = ((perSlabTubeConst Cfib Cloc : ENNReal) / (64 : ENNReal)) * CF * (mT : ENNReal)
          * (θ : ENNReal) * ((b : ℝ≥0) : ENNReal) ^ 2 := by
        rw [ENNReal.div_eq_inv_mul]
        ac_rfl

/-- Relates the fixed tube constant to the physical coefficient (the `b`-less part) of the
Frostman side condition: multiplying `perSlabTubeConst/64` by the fullness radius `c₃ =
Tube.le_volume.c 3` and cancelling the `64`, one gets `8 · fibreTubeLoss · Cfib³ · Cloc · |B₁|`. -/
private lemma frostman_coeff_const (Cfib Cloc : ℝ≥0) :
    Tube.le_volume.c 3 * (perSlabTubeConst Cfib Cloc / 64 : ℝ≥0)
      = 8 * fibreTubeLoss Cfib * Cfib ^ 3 * Cloc * unitBallVol := by
  unfold perSlabTubeConst
  have hc : Tube.le_volume.c 3 ≠ 0 := (Tube.le_volume.c_pos 3).ne'
  field_simp [hc]
  ring

/-- The coefficient cancellation behind `perSlabCFtube_frostman_side`: after multiplying by
`θ · b²`, the left-hand physical volume equals the right-hand carrier. -/
private lemma frostman_coeff (Cfib Cloc : ℝ≥0) (θ b : ℝ≥0) :
    (Tube.le_volume.c 3 * (perSlabTubeConst Cfib Cloc / 64 : ℝ≥0)) * θ * b ^ 2
      = fibreTubeLoss Cfib * Cfib ^ 3 * Cloc * (8 * (θ * b) * b) * unitBallVol := by
  rw [show 8 * (θ * b) * b = 8 * θ * b ^ 2 by ring]
  rw [frostman_coeff_const]
  ring

/-- The side condition of `Plank.isFrostmanIn_slabFibreTubes_sub`, with the tube-volume lower bound
`Tube.le_volume` already substituted. -/
theorem perSlabCFtube_frostman_side (Cfib Cloc : ℝ≥0)
    (CF : ENNReal) (hCFtop : CF ≠ ⊤) (mT nsub : ℕ) (hnsub : nsub ≠ 0) (θ b : ℝ≥0) :
    ((fibreTubeLoss Cfib : ℝ≥0) : ENNReal) * ((Cfib : ℝ≥0) : ENNReal) ^ 3
        * ((Cloc : ENNReal) * CF * (mT : ENNReal) * ((8 * (θ * b) * b : ℝ≥0) : ENNReal))
        * volume (ConvexSpaceBody.closedUnitBall :
            ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))).carrier
      ≤ perSlabCFtube Cfib Cloc CF mT nsub θ
          * ((nsub : ENNReal) * (((Tube.le_volume.c 3 : ℝ≥0) : ENNReal)
              * ((b / 8 : ℝ≥0) : ENNReal) ^ 2)) := by
  apply le_of_eq
  rw [← coe_unitBallVol]
  have hR : perSlabCFtube Cfib Cloc CF mT nsub θ
      * ((nsub : ENNReal) * (((Tube.le_volume.c 3 : ℝ≥0) : ENNReal)
          * ((b / 8 : ℝ≥0) : ENNReal) ^ 2))
      = ((Tube.le_volume.c 3 : ℝ≥0) : ENNReal)
        * (perSlabCFtube Cfib Cloc CF mT nsub θ
            * ((nsub : ENNReal) * ((b / 8 : ℝ≥0) : ENNReal) ^ 2)) := by
    ac_rfl
  rw [hR, perSlabCFtube_mul_card_mul_sq Cfib Cloc CF hCFtop mT nsub hnsub θ b]
  have hkey : (fibreTubeLoss Cfib * Cfib ^ 3 * Cloc * (8 * (θ * b) * b) * unitBallVol : ℝ≥0)
      = Tube.le_volume.c 3 * (perSlabTubeConst Cfib Cloc / 64 : ℝ≥0) * θ * b ^ 2 :=
    (frostman_coeff Cfib Cloc θ b).symm
  calc
    ((fibreTubeLoss Cfib : ℝ≥0) : ENNReal) * ((Cfib : ℝ≥0) : ENNReal) ^ 3
        * ((Cloc : ENNReal) * CF * (mT : ENNReal) * ((8 * (θ * b) * b : ℝ≥0) : ENNReal))
        * ((unitBallVol : ℝ≥0) : ENNReal)
        = ((fibreTubeLoss Cfib * Cfib ^ 3 * Cloc * (8 * (θ * b) * b) * unitBallVol : ℝ≥0) : ENNReal)
            * CF * (mT : ENNReal) := by
          push_cast
          ring
    _ = ((Tube.le_volume.c 3 * (perSlabTubeConst Cfib Cloc / 64 : ℝ≥0) * θ * b ^ 2 : ℝ≥0) : ENNReal)
            * CF * (mT : ENNReal) := by rw [hkey]
    _ = ((Tube.le_volume.c 3 : ℝ≥0) : ENNReal)
          * (((perSlabTubeConst Cfib Cloc / 64 : ℝ≥0) : ENNReal) * CF * (mT : ENNReal)
            * (θ : ENNReal) * ((b : ℝ≥0) : ENNReal) ^ 2) := by
          push_cast
          ring

/-- **The fixed loss of the per-slab estimate.** It absorbs the extraction loss `MED + 1`, the
numerical factors `8^(ε/2)` and `8^(2β) ≤ 64` produced by the tube radius `b/8` and the analytic
scale `a/8`, the tube Frostman constant's fixed part, and the fullness constant `c₂`. -/
def perSlabLoss (ε : ℝ) (c2 Cfib Mret Kc : ℝ≥0) : ℝ≥0 :=
  Mret * (8 : ℝ≥0) ^ (ε / 2) * 64 * (1 + Kc) * (c2 * Cfib ^ 3 * 8)⁻¹

theorem perSlabLoss_pos {ε : ℝ} {c2 Cfib Mret Kc : ℝ≥0} (hc2 : 0 < c2) (hCfib : 1 ≤ Cfib)
    (hMret : 1 ≤ Mret) : 0 < perSlabLoss ε c2 Cfib Mret Kc := by
  unfold perSlabLoss
  positivity

/-! ### The scalar cancellation -/

/-- Combining two `rpow`s of the same nonzero finite base. -/
private theorem enn_rpow_add' {x : ENNReal} (h0 : x ≠ 0) (ht : x ≠ ⊤) (p q : ℝ) :
    x ^ p * x ^ q = x ^ (p + q) := (ENNReal.rpow_add p q h0 ht).symm

/-- A natural square raised to a real power. -/
private theorem enn_sq_rpow (x : ENNReal) (p : ℝ) : (x ^ (2 : ℕ)) ^ p = x ^ ((2 : ℝ) * p) := by
  rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
  norm_num

/-- Splitting off the fixed factor `8` from a `rpow` of `x / 8`. -/
private theorem coe_div_eight_rpow (x : ℝ≥0) (p : ℝ) :
    (((x / 8 : ℝ≥0)) : ENNReal) ^ p = (x : ENNReal) ^ p * (8 : ENNReal) ^ (-p) := by
  rw [ENNReal.coe_div (by norm_num : (8 : ℝ≥0) ≠ 0), ENNReal.div_eq_inv_mul,
    ENNReal.mul_rpow_of_ne_top (by simp) ENNReal.coe_ne_top, ENNReal.inv_rpow,
    ← ENNReal.rpow_neg, mul_comm]
  norm_num

/-- **Closed form of the per-slab left-hand side** — the exponent bookkeeping of GWZ Lemma 6.4, as
an exact identity.

Writing `p = 1 - β/2`, the four groups of powers collapse as follows.

* `CF ^ (β/2 - 1) · CF ^ p = 1` and `|𝒯| ^ (β/2 - 1) · |𝒯| ^ p = 1`. This is why the induced tube
  Frostman constant `Plank.perSlabCFtube` had to keep `CF` and `|𝒯|` free and unmodified.
* `θ ^ (β/2) · θ ^ p = θ`, matching the single `θ` of the carrier volume `8 θ b²`.
* `b ^ (2β) · (b²) ^ (β/2) · (b/8) ^ (-2β) · (b²) ^ p = 8 ^ (2β) · b²`, i.e. the `b`-exponents
  `2β + β - 2β + (2 - β)` sum to `2`, and the tube radius `b/8` contributes only the fixed
  factor `8 ^ (2β)`.
* `a ^ ε · (a/8) ^ (-(ε/2)) = 8 ^ (ε/2) · a ^ (ε/2)`, the residual gain that must dominate the
  fullness exponent `a ^ (4η)`.

Nothing is discarded: the identity is exact, and the only surviving constants are `8 ^ (ε/2)`,
`8 ^ (2β)` and `Kc ^ p`. -/
theorem perSlabScalarLHS {β ε : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    {a b θ : ℝ≥0} (ha : 0 < a) (hb0 : 0 < b) (hθ0 : 0 < θ)
    {Mret Kc : ℝ≥0} {CF : ENNReal} (hCF1 : 1 ≤ CF) (hCFtop : CF ≠ ⊤) {mT nf : ℕ} (hmT : mT ≠ 0) :
    ((a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
        * ((b : ENNReal) ^ 2) ^ (β / 2) * (θ : ENNReal) ^ (β / 2)
        * (mT : ENNReal) ^ (β / 2 - 1) * (nf : ENNReal))
      * ((Mret : ENNReal) * (((a / 8 : ℝ≥0)) : ENNReal) ^ (-(ε / 2))
          * (((b / 8 : ℝ≥0)) : ENNReal) ^ (-2 * β)
          * ((Kc : ENNReal) * CF * (mT : ENNReal) * (θ : ENNReal)
              * ((b : ℝ≥0) : ENNReal) ^ 2) ^ (1 - β / 2))
      = (Mret : ENNReal) * (8 : ENNReal) ^ (ε / 2) * (8 : ENNReal) ^ (2 * β)
          * ((Kc : ℝ≥0) : ENNReal) ^ (1 - β / 2) * (a : ENNReal) ^ (ε / 2)
          * ((b : ℝ≥0) : ENNReal) ^ 2 * (θ : ENNReal) * (nf : ENNReal) := by
  have hp : (0 : ℝ) ≤ 1 - β / 2 := by linarith
  have ha_ne : (a : ENNReal) ≠ 0 := (ENNReal.coe_ne_zero).2 (ne_of_gt ha)
  have ha_top : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hb_ne : (b : ENNReal) ≠ 0 := (ENNReal.coe_ne_zero).2 (ne_of_gt hb0)
  have hb_top : (b : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hθ_ne : (θ : ENNReal) ≠ 0 := (ENNReal.coe_ne_zero).2 (ne_of_gt hθ0)
  have hθ_top : (θ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCF_ne : CF ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hCF1)
  have hmT_ne : (mT : ENNReal) ≠ 0 := by exact_mod_cast hmT
  have hmT_top : (mT : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top mT
  have hbig :
      ((Kc : ENNReal) * CF * (mT : ENNReal) * (θ : ENNReal) * ((b : ℝ≥0) : ENNReal) ^ 2) ^
          (1 - β / 2)
        = (Kc : ENNReal) ^ (1 - β / 2) * CF ^ (1 - β / 2) * (mT : ENNReal) ^ (1 - β / 2)
            * (θ : ENNReal) ^ (1 - β / 2) * (((b : ℝ≥0) : ENNReal) ^ 2) ^ (1 - β / 2) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp, ENNReal.mul_rpow_of_nonneg _ _ hp,
      ENNReal.mul_rpow_of_nonneg _ _ hp, ENNReal.mul_rpow_of_nonneg _ _ hp]
  have hsqa : (((a : ℝ≥0) : ENNReal) ^ (-(ε / 2)) *
      (8 : ENNReal) ^ (ε / 2)) = (((a / 8 : ℝ≥0)) : ENNReal) ^ (-(ε / 2)) := by
    rw [coe_div_eight_rpow a (-(ε / 2))]
    rw [neg_neg]
  have hsqb : (((b : ℝ≥0) : ENNReal) ^ (-2 * β) *
      (8 : ENNReal) ^ (2 * β)) = (((b / 8 : ℝ≥0)) : ENNReal) ^ (-2 * β) := by
    rw [coe_div_eight_rpow b (-2 * β)]
    rw [show -(-2 * β) = 2 * β by ring]
  calc
    ((a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
        * ((b : ENNReal) ^ 2) ^ (β / 2) * (θ : ENNReal) ^ (β / 2)
        * (mT : ENNReal) ^ (β / 2 - 1) * (nf : ENNReal))
      * ((Mret : ENNReal) * (((a / 8 : ℝ≥0)) : ENNReal) ^ (-(ε / 2))
          * (((b / 8 : ℝ≥0)) : ENNReal) ^ (-2 * β)
          * ((Kc : ENNReal) * CF * (mT : ENNReal) * (θ : ENNReal)
              * ((b : ℝ≥0) : ENNReal) ^ 2) ^ (1 - β / 2))
    = (Mret : ENNReal) * (8 : ENNReal) ^ (ε / 2) * (8 : ENNReal) ^ (2 * β)
          * ((Kc : ℝ≥0) : ENNReal) ^ (1 - β / 2) * (a : ENNReal) ^ (ε / 2)
          * ((b : ℝ≥0) : ENNReal) ^ 2 * (θ : ENNReal) * (nf : ENNReal) := by
      rw [hbig, ← hsqa, ← hsqb, enn_sq_rpow (b : ENNReal) (β / 2),
        enn_sq_rpow (b : ENNReal) (1 - β / 2)]
      ring_nf
      -- reassociate so that same-base powers are contiguous
      rw [show
          (↑a : ENNReal) ^ ε * CF ^ (-1 + β * (1 / 2)) * (↑b : ENNReal) ^ (β * 2) *
              (↑b : ENNReal) ^ β * (↑θ : ENNReal) ^ (β * (1 / 2)) *
              (↑mT : ENNReal) ^ (-1 + β * (1 / 2)) *
              (↑nf : ENNReal) * (↑Mret : ENNReal) * (↑a : ENNReal) ^ (ε * (-1 / 2)) *
              8 ^ (ε * (1 / 2)) *
              (↑b : ENNReal) ^ (-(β * 2)) * 8 ^ (β * 2) * (↑Kc : ENNReal) ^ (1 + β * (-1 / 2)) *
              CF ^ (1 + β * (-1 / 2)) * (↑mT : ENNReal) ^ (1 + β * (-1 / 2)) *
              (↑θ : ENNReal) ^ (1 + β * (-1 / 2)) *
              (↑b : ENNReal) ^ (2 - β)
          = ((↑b : ENNReal) ^ (β * 2) * (↑b : ENNReal) ^ β * (↑b : ENNReal) ^ (-(β * 2)) *
                (↑b : ENNReal) ^ (2 - β)) *
              (CF ^ (-1 + β * (1 / 2)) * CF ^ (1 + β * (-1 / 2))) *
              ((↑mT : ENNReal) ^ (-1 + β * (1 / 2)) * (↑mT : ENNReal) ^ (1 + β * (-1 / 2))) *
              ((↑a : ENNReal) ^ ε * (↑a : ENNReal) ^ (ε * (-1 / 2))) *
              ((↑θ : ENNReal) ^ (β * (1 / 2)) * (↑θ : ENNReal) ^ (1 + β * (-1 / 2))) *
              (8 ^ (ε * (1 / 2)) * 8 ^ (β * 2)) * (↑nf : ENNReal) * (↑Mret : ENNReal) *
              (↑Kc : ENNReal) ^ (1 + β * (-1 / 2)) by ac_rfl]
      -- combine the b powers
      rw [enn_rpow_add' hb_ne hb_top (β * 2) β]
      rw [enn_rpow_add' hb_ne hb_top (β * 2 + β) (-(β * 2))]
      rw [enn_rpow_add' hb_ne hb_top (β * 2 + β + (-(β * 2))) (2 - β)]
      -- CF and mT powers cancel
      rw [enn_rpow_add' hCF_ne hCFtop (-1 + β * (1 / 2)) (1 + β * (-1 / 2))]
      rw [enn_rpow_add' hmT_ne hmT_top (-1 + β * (1 / 2)) (1 + β * (-1 / 2))]
      -- θ and a combine
      rw [enn_rpow_add' hθ_ne hθ_top (β * (1 / 2)) (1 + β * (-1 / 2))]
      rw [enn_rpow_add' ha_ne ha_top ε (ε * (-1 / 2))]
      -- ring-normalize the summed exponents, then strip the surviving 0/1 powers
      ring_nf
      simp [ENNReal.rpow_zero, ENNReal.rpow_one]
      ac_rfl

/-- **The constant comparison of the per-slab step.** After
`Plank.perSlabScalarLHS` has cancelled every `CF`, `|𝒯|`, `θ` and `b` power, the per-slab estimate
reduces to three elementary facts: `8 ^ (2β) ≤ 64` (as `0 < 2β ≤ 2`), `Kc ^ (1 - β/2) ≤ 1 + Kc`
(as `0 < 1 - β/2 ≤ 1`), and `a ^ (ε/2) ≤ a ^ (4η)` (as `a ≤ 1` and `4η ≤ ε/2`). The constant
`Plank.perSlabLoss` is exactly what absorbs the first two together with the fullness constant `c₂`
and the dilation loss `Cfib³`. -/
theorem perSlabScalarCompare {β ε η : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1) (hεpos : 0 < ε)
    (hηpos : 0 < η) (hηε : 4 * η ≤ ε / 2)
    {a b θ : ℝ≥0} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    {c2 Cfib Mret Kc : ℝ≥0} (hc2 : 0 < c2) (hCfib : 1 ≤ Cfib) (hMret : 1 ≤ Mret) {nf : ℕ} :
    (Mret : ENNReal) * (8 : ENNReal) ^ (ε / 2) * (8 : ENNReal) ^ (2 * β)
        * ((Kc : ℝ≥0) : ENNReal) ^ (1 - β / 2) * (a : ENNReal) ^ (ε / 2)
        * ((b : ℝ≥0) : ENNReal) ^ 2 * (θ : ENNReal) * (nf : ENNReal)
      ≤ ((perSlabLoss ε c2 Cfib Mret Kc : ℝ≥0) : ENNReal)
          * (((c2 * a ^ (4 * η) : ℝ≥0)) : ENNReal)
            * ((nf : ENNReal)
              * (((Cfib : ℝ≥0) : ENNReal) ^ 3 * ((8 * (θ * b) * b : ℝ≥0) : ENNReal))) := by
  -- STEP A: the ℝ≥0 coefficient identity behind `perSlabLoss`
  have hA : (perSlabLoss ε c2 Cfib Mret Kc * (c2 * (Cfib ^ 3 * (8 * (θ * b) * b))) : ℝ≥0)
      = (Mret * (8 : ℝ≥0) ^ (ε / 2) * 64 * (1 + Kc) * (θ * b ^ 2) : ℝ≥0) := by
    unfold perSlabLoss
    have hne : c2 * Cfib ^ 3 * 8 ≠ (0 : ℝ≥0) := by positivity
    field_simp [hne]
  -- coercions of the two rpow bases into ENNReal
  have h8co : (((8 : ℝ≥0) ^ (ε / 2) : ℝ≥0) : ENNReal) = (8 : ENNReal) ^ (ε / 2) :=
    ENNReal.coe_rpow_of_ne_zero (by norm_num : (8 : ℝ≥0) ≠ 0) (ε / 2)
  have haco : (((a ^ (4 * η) : ℝ≥0)) : ENNReal) = (a : ENNReal) ^ (4 * η) :=
    ENNReal.coe_rpow_of_ne_zero (ne_of_gt ha) (4 * η)
  -- STEP B: right-hand side → matching coefficient form
  have hR : ((perSlabLoss ε c2 Cfib Mret Kc : ℝ≥0) : ENNReal)
          * (((c2 * a ^ (4 * η) : ℝ≥0)) : ENNReal)
            * ((nf : ENNReal)
              * (((Cfib : ℝ≥0) : ENNReal) ^ 3 * ((8 * (θ * b) * b : ℝ≥0) : ENNReal)))
      = (Mret : ENNReal) * (8 : ENNReal) ^ (ε / 2) * (64 : ENNReal)
          * ((1 + Kc : ℝ≥0) : ENNReal) * ((θ * b ^ 2 : ℝ≥0) : ENNReal)
          * (a : ENNReal) ^ (4 * η) * (nf : ENNReal) := by
    calc
      ((perSlabLoss ε c2 Cfib Mret Kc : ℝ≥0) : ENNReal)
          * (((c2 * a ^ (4 * η) : ℝ≥0)) : ENNReal)
            * ((nf : ENNReal)
              * (((Cfib : ℝ≥0) : ENNReal) ^ 3 * ((8 * (θ * b) * b : ℝ≥0) : ENNReal)))
        = ((perSlabLoss ε c2 Cfib Mret Kc * (c2 * (Cfib ^ 3 * (8 * (θ * b) * b)))
              * a ^ (4 * η) : ℝ≥0) : ENNReal) * (nf : ENNReal) := by
          push_cast
          ring
      _ = ((Mret * (8 : ℝ≥0) ^ (ε / 2) * 64 * (1 + Kc) * (θ * b ^ 2) * a ^ (4 * η) : ℝ≥0)
              : ENNReal) * (nf : ENNReal) := by
          rw [hA]
      _ = (Mret : ENNReal) * (8 : ENNReal) ^ (ε / 2) * (64 : ENNReal)
          * ((1 + Kc : ℝ≥0) : ENNReal) * ((θ * b ^ 2 : ℝ≥0) : ENNReal)
          * (a : ENNReal) ^ (4 * η) * (nf : ENNReal) := by
          push_cast
          rw [haco, h8co]
  -- STEP C: left-hand side → matching coefficient form
  have hL : (Mret : ENNReal) * (8 : ENNReal) ^ (ε / 2) * (8 : ENNReal) ^ (2 * β)
        * ((Kc : ℝ≥0) : ENNReal) ^ (1 - β / 2) * (a : ENNReal) ^ (ε / 2)
        * ((b : ℝ≥0) : ENNReal) ^ 2 * (θ : ENNReal) * (nf : ENNReal)
      = (Mret : ENNReal) * (8 : ENNReal) ^ (ε / 2) * (8 : ENNReal) ^ (2 * β)
          * ((Kc : ℝ≥0) : ENNReal) ^ (1 - β / 2) * ((θ * b ^ 2 : ℝ≥0) : ENNReal)
          * (a : ENNReal) ^ (ε / 2) * (nf : ENNReal) := by
    push_cast
    ring
  -- the three comparison facts
  have h8le : (8 : ENNReal) ^ (2 * β) ≤ ((64 : ℝ≥0) : ENNReal) := by
    calc
      (8 : ENNReal) ^ (2 * β) ≤ (8 : ENNReal) ^ (2 : ℝ) := by
        exact ENNReal.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ENNReal) ≤ (8 : ENNReal))
          (by linarith : (2 * β : ℝ) ≤ 2)
      _ = ((64 : ℝ≥0) : ENNReal) := by
        norm_num
  have hKcle : ((Kc : ℝ≥0) : ENNReal) ^ (1 - β / 2) ≤ ((1 + Kc : ℝ≥0) : ENNReal) := by
    rcases le_total Kc 1 with hKle | hKge
    · calc
        ((Kc : ℝ≥0) : ENNReal) ^ (1 - β / 2) ≤ (1 : ENNReal) := by
          exact ENNReal.rpow_le_one (by exact_mod_cast hKle) (by linarith : (0 : ℝ) ≤ 1 - β / 2)
        _ ≤ ((1 + Kc : ℝ≥0) : ENNReal) := by
          exact_mod_cast (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ Kc by positivity)
            : (1 : ℝ≥0) ≤ 1 + Kc)
    · calc
        ((Kc : ℝ≥0) : ENNReal) ^ (1 - β / 2) ≤ ((Kc : ℝ≥0) : ENNReal) ^ (1 : ℝ) := by
          exact ENNReal.rpow_le_rpow_of_exponent_le (by exact_mod_cast hKge)
            (by linarith : (1 - β / 2 : ℝ) ≤ 1)
        _ = (Kc : ENNReal) := by rw [ENNReal.rpow_one]
        _ ≤ ((1 + Kc : ℝ≥0) : ENNReal) := by
          have hk1 : (Kc : ℝ≥0) ≤ 1 + Kc := by
            rw [add_comm]
            exact le_add_of_nonneg_right (by norm_num : (0 : ℝ≥0) ≤ (1 : ℝ≥0))
          exact_mod_cast hk1
  have hae2le : (a : ENNReal) ^ (ε / 2) ≤ (a : ENNReal) ^ (4 * η) := by
    have ha1 : (a : ENNReal) ≤ 1 := by exact_mod_cast (le_trans hab hb1)
    exact ENNReal.rpow_le_rpow_of_exponent_ge ha1 hηε
  -- assemble
  calc
    (Mret : ENNReal) * (8 : ENNReal) ^ (ε / 2) * (8 : ENNReal) ^ (2 * β)
        * ((Kc : ℝ≥0) : ENNReal) ^ (1 - β / 2) * (a : ENNReal) ^ (ε / 2)
        * ((b : ℝ≥0) : ENNReal) ^ 2 * (θ : ENNReal) * (nf : ENNReal)
    = (Mret : ENNReal) * (8 : ENNReal) ^ (ε / 2) * (8 : ENNReal) ^ (2 * β)
          * ((Kc : ℝ≥0) : ENNReal) ^ (1 - β / 2) * ((θ * b ^ 2 : ℝ≥0) : ENNReal)
          * (a : ENNReal) ^ (ε / 2) * (nf : ENNReal) := hL
    _ ≤ (Mret : ENNReal) * (8 : ENNReal) ^ (ε / 2) * (64 : ENNReal)
        * ((1 + Kc : ℝ≥0) : ENNReal) * ((θ * b ^ 2 : ℝ≥0) : ENNReal)
        * (a : ENNReal) ^ (4 * η) * (nf : ENNReal) := by
      gcongr
      · exact h8le
    _ = ((perSlabLoss ε c2 Cfib Mret Kc : ℝ≥0) : ENNReal)
        * (((c2 * a ^ (4 * η) : ℝ≥0)) : ENNReal)
          * ((nf : ENNReal)
            * (((Cfib : ℝ≥0) : ENNReal) ^ 3 * ((8 * (θ * b) * b : ℝ≥0) : ENNReal))) := hR.symm

/-- **The per-slab scalar inequality.**

The left-hand side is the per-slab target multiplied by the two losses that the analytic step
introduces — the shade-mass extraction loss `Mret = MED + 1` and the tube multiplicity bound `B`
returned by the two-scale Frostman estimate at `τ = a/8`, `δ = b/8`. The right-hand side is
`perSlabLoss` times the shade mass supplied by the fullness hypothesis. Every occurrence of `CF`,
of `|𝒯|` and of `|sub|` has already cancelled; what remains is
`a^(ε/2) ≤ a^(4η)` together with fixed constants.

This is the *only* place where the exponents of GWZ Lemma 6.4 are balanced, and it is stated as a
single inequality between explicit products so that the bookkeeping is auditable. -/
theorem perSlabScalar {β ε η : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1) (hεpos : 0 < ε)
    (hηpos : 0 < η) (hηε : 4 * η ≤ ε / 2)
    {a b θ : ℝ≥0} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    {c2 Cfib Mret Kc : ℝ≥0} (hc2 : 0 < c2) (hCfib : 1 ≤ Cfib) (hMret : 1 ≤ Mret)
    {CF : ENNReal} (hCF1 : 1 ≤ CF) (hCFtop : CF ≠ ⊤) {mT nf : ℕ} (hmT : mT ≠ 0) :
    ((a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
        * ((b : ENNReal) ^ 2) ^ (β / 2) * (θ : ENNReal) ^ (β / 2)
        * (mT : ENNReal) ^ (β / 2 - 1) * (nf : ENNReal))
      * ((Mret : ENNReal) * (((a / 8 : ℝ≥0)) : ENNReal) ^ (-(ε / 2))
          * (((b / 8 : ℝ≥0)) : ENNReal) ^ (-2 * β)
          * ((Kc : ENNReal) * CF * (mT : ENNReal) * (θ : ENNReal)
              * ((b : ℝ≥0) : ENNReal) ^ 2) ^ (1 - β / 2))
      ≤ ((perSlabLoss ε c2 Cfib Mret Kc : ℝ≥0) : ENNReal)
          * (((c2 * a ^ (4 * η) : ℝ≥0)) : ENNReal)
            * ((nf : ENNReal)
              * (((Cfib : ℝ≥0) : ENNReal) ^ 3 * ((8 * (θ * b) * b : ℝ≥0) : ENNReal))) := by
  rw [perSlabScalarLHS (β := β) (ε := ε) hβpos hβle ha (lt_of_lt_of_le ha hab) hθ0
    hCF1 hCFtop hmT]
  exact perSlabScalarCompare hβpos hβle hεpos hηpos hηε ha hab hb1 hθ0 hθ1 hc2 hCfib hMret

/-! ### Auxiliary geometric facts -/

/-- The exact carrier volume of a fibre's shading body: the `Cfib`-dilation of a
`θ`-thickened `b`-plank. -/
theorem volume_carrier_shadeBody {fibre : Finset (ThickenedPlank θ b hθ1 hb1)}
    {Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {S : Slab θ hθ1} {Cfib : ℝ≥0} (h : SlabFibreGeometry fibre Yθ S Cfib)
    {Q : ThickenedPlank θ b hθ1 hb1} (hQ : Q ∈ fibre) :
    volume ((Yθ Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = ((Cfib : ℝ≥0) : ENNReal) ^ 3 * ((8 * (θ * b) * b : ℝ≥0) : ENNReal) := by
  rw [h.shade_body Q hQ, PrismNDim.volume_dilation]
  rw [Prism3D.volume_carrier Q, ENNReal.coe_one, mul_one]
  rw [← ENNReal.coe_ofNat, ← ENNReal.coe_mul, ← ENNReal.coe_mul]

/-- The tube-volume lower bound of `Tube.le_volume`, summed over the extracted sub-fibre. -/
theorem card_mul_le_sum_volume_carrier_slabFibreTubes
    {fibre : Finset (ThickenedPlank θ b hθ1 hb1)}
    {Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {S : Slab θ hθ1} {Cfib : ℝ≥0} (hθ0 : 0 < θ)
    (sub : Finset (ThickenedPlank θ b hθ1 hb1)) :
    (sub.card : ENNReal) * (((Tube.le_volume.c 3 : ℝ≥0) : ENNReal)
        * ((b / 8 : ℝ≥0) : ENNReal) ^ 2)
      ≤ ∑ Q ∈ sub, volume ((slabFibreTubes Cfib fibre Yθ S hθ0 Q).carrier :
          Set (EuclideanSpace ℝ (Fin 3))) := by
  have hpoint : ∀ Q ∈ sub, ((Tube.le_volume.c 3 : ℝ≥0) : ENNReal)
      * ((b / 8 : ℝ≥0) : ENNReal) ^ 2
      ≤ volume ((slabFibreTubes Cfib fibre Yθ S hθ0 Q).carrier :
          Set (EuclideanSpace ℝ (Fin 3))) := by
    intro Q hQ
    have hle := Tube.le_volume (T := (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toTube)
    simpa [finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)] using hle
  calc
    (sub.card : ENNReal) * (((Tube.le_volume.c 3 : ℝ≥0) : ENNReal)
        * ((b / 8 : ℝ≥0) : ENNReal) ^ 2)
        = sub.card • (((Tube.le_volume.c 3 : ℝ≥0) : ENNReal)
            * ((b / 8 : ℝ≥0) : ENNReal) ^ 2) := by
          rw [← nsmul_eq_mul]
    _ ≤ ∑ Q ∈ sub, volume ((slabFibreTubes Cfib fibre Yθ S hθ0 Q).carrier :
          Set (EuclideanSpace ℝ (Fin 3))) := by
          exact Finset.card_nsmul_le_sum sub
            (fun Q => volume ((slabFibreTubes Cfib fibre Yθ S hθ0 Q).carrier :
              Set (EuclideanSpace ℝ (Fin 3))))
            (((Tube.le_volume.c 3 : ℝ≥0) : ENNReal) * ((b / 8 : ℝ≥0) : ENNReal) ^ 2)
            hpoint

/-- **The fullness threshold at the analytic scale.** With `4η ≤ ηKF/2` and `b ≤ b₀` small enough
that `b₀^(ηKF - 4η) ≤ G`, the plank-scale fullness `G · a^(4η)` dominates `(a/8)^ηKF`. -/
theorem perSlabFullnessThreshold {ηKF η : ℝ} (hηKF : 0 < ηKF) (hηpos : 0 < η)
    (hη4 : 4 * η ≤ ηKF / 2) {G a b b₀ : ℝ≥0} (hG : 0 < G) (ha : 0 < a) (hab : a ≤ b)
    (hbb₀ : b ≤ b₀) (hb₀1 : b₀ ≤ 1) (hb₀ : b₀ ^ (ηKF - 4 * η) ≤ G) :
    ((a / 8 : ℝ≥0)) ^ ηKF ≤ G * a ^ (4 * η) := by
  have ha_div : (a / 8 : ℝ≥0) ≤ a := by
    exact div_le_self ha.le (by norm_num : (1 : ℝ≥0) ≤ 8)
  have hη4lt : 4 * η < ηKF := lt_of_le_of_lt hη4 (half_lt_self hηKF)
  have hpos : 0 < ηKF - 4 * η := sub_pos.mpr hη4lt
  have hη_decomp : 4 * η + (ηKF - 4 * η) = ηKF := by ring
  have ha_b0 : a ≤ b₀ := le_trans hab hbb₀
  calc
    ((a / 8 : ℝ≥0)) ^ ηKF ≤ a ^ ηKF := NNReal.rpow_le_rpow ha_div hηKF.le
    _ = a ^ (4 * η) * a ^ (ηKF - 4 * η) := by
        conv_lhs => rw [← hη_decomp]
        exact NNReal.rpow_add (ne_of_gt ha) (4 * η) (ηKF - 4 * η)
    _ ≤ a ^ (4 * η) * G := by
        gcongr
        exact le_trans (NNReal.rpow_le_rpow ha_b0 hpos.le) hb₀
    _ = G * a ^ (4 * η) := by rw [mul_comm]

/-- A positive threshold making a fixed positive power small: used to pick `b₀`. -/
theorem exists_nnreal_rpow_le {p : ℝ} (hp : 0 < p) {G : ℝ≥0} (hG : 0 < G) :
    ∃ b₀ : ℝ≥0, 0 < b₀ ∧ b₀ ≤ 1 ∧ b₀ ^ p ≤ G := by
  let b₀ : ℝ≥0 := min 1 (G ^ (1 / p))
  refine ⟨b₀, ?_, ?_, ?_⟩
  · exact lt_min (by norm_num : (0 : ℝ≥0) < 1) (NNReal.rpow_pos hG)
  · exact min_le_left _ _
  · calc
      b₀ ^ p ≤ (G ^ (1 / p)) ^ p := NNReal.rpow_le_rpow (min_le_right _ _) hp.le
      _ = G ^ ((1 / p) * p) := by rw [← NNReal.rpow_mul]
      _ = G ^ (1 : ℝ) := by rw [one_div_mul_cancel hp.ne']
      _ = G := by rw [NNReal.rpow_one]

/-- `ℝ³` has dimension `3`, so the exponent `Module.finrank ℝ E - 1` of GWZ Lemma 3.9 is `2`. -/
private theorem finrank_three : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 :=
  finrank_euclideanSpace_fin

/-- **The shade mass of a fibre from its fullness.** The carrier volumes of the shading bodies are
all equal to `Cfib³ · 8 θ b²` (`Plank.volume_carrier_shadeBody`), so a lower bound on the fullness
is literally a lower bound on the total shade mass. No cardinality pigeonhole is involved. -/
theorem perSlabMassBound {fibre : Finset (ThickenedPlank θ b hθ1 hb1)}
    {Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {S : Slab θ hθ1} {Cfib : ℝ≥0} (h : SlabFibreGeometry fibre Yθ S Cfib)
    {G : ℝ≥0} (hfull : G ≤ ShadedBody.fullness fibre Yθ) :
    (G : ENNReal) * ((fibre.card : ENNReal)
        * (((Cfib : ℝ≥0) : ENNReal) ^ 3 * ((8 * (θ * b) * b : ℝ≥0) : ENNReal)))
      ≤ ∑ Q ∈ fibre, volume (Yθ Q).shade :=
  ShadedBody.coe_fullness_mul_le_sum_volume_shade fibre Yθ hfull
    (fun Q hQ => le_of_eq (volume_carrier_shadeBody h hQ).symm)

/-- Cancelling a common nonzero finite factor: from `X ≤ W · U` and `G · W ≤ K · X` conclude
`G ≤ K · U`. This is how the per-slab target is released from the two multiplicative losses. -/
private theorem le_of_mul_le_of_le_mul {G K X U W : ENNReal} (hW0 : W ≠ 0) (hWtop : W ≠ ⊤)
    (h1 : X ≤ W * U) (h2 : G * W ≤ K * X) : G ≤ K * U := by
  have h3 : G * W ≤ K * U * W := by
    calc
      G * W ≤ K * X := h2
      _ ≤ K * (W * U) := by gcongr
      _ = K * U * W := by ring
  exact (ENNReal.mul_le_mul_iff_left hW0 hWtop).mp h3

/-! ### The per-slab estimate -/

/-- **The multiplicity of the extracted tube sub-fibre.**

This is the single call to the analytic input. The scales are
`δ_KF = b/8` (the physical radius of `Plank.slabFibreTubes`) and `τ_KF = a/8` (the analytic scale),
and the Frostman constant is `Plank.perSlabCFtube`, whose `|sub|` denominator is cancelled by the
estimate's own `(|sub| · δ_KF²)^(1-β/2)` factor. The conclusion is therefore free of `|sub|`. -/
theorem perSlabMultiplicityBound {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    {ε : ℝ} (hε : 0 < ε) {ηKF : ℝ} {δ₀ : ℝ≥0}
    (hTS : ∀ δ : ℝ≥0, 0 < δ → δ ≤ δ₀ → ∀ τ : ℝ≥0, 0 < τ → τ ≤ δ →
      ∀ {κ : Type} (t : Finset κ) (T : κ → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (t : Set κ).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
        τ ^ ηKF ≤ ShadedBody.fullness t (fun i => (T i).toShadedBody) →
        ∀ CFt : ENNReal, 1 ≤ CFt → CFt ≠ ⊤ →
        ConvexSpaceBody.IsFrostmanIn t (fun i => (T i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall CFt →
        ShadedBody.multiplicity t (fun i => (T i).toShadedBody) ≤
          (τ : ENNReal) ^ (-(ε / 2)) * CFt ^ (1 - β / 2) * (δ : ENNReal) ^ (-2 * β) *
          ((t.card : ENNReal) * (δ : ENNReal) ^ 2) ^ (1 - β / 2))
    {Cfib Cloc : ℝ≥0} (hCfib : 1 ≤ Cfib) (hCloc : 1 ≤ Cloc)
    {a : ℝ≥0} (ha : 0 < a) (hab : a ≤ b) (hbδ₀ : b ≤ δ₀)
    (hθ0 : 0 < θ)
    {Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {𝒯 fibre sub : Finset (ThickenedPlank θ b hθ1 hb1)} {S : Slab θ hθ1}
    {CF : ENNReal} (hCF1 : 1 ≤ CF) (hCFtop : CF ≠ ⊤)
    (hgeom : SlabFibreGeometry fibre Yθ S Cfib) (hfne : fibre.Nonempty)
    (hsub : sub ⊆ fibre) (hsub_ne : sub.Nonempty)
    (hpair : (↑sub : Set (ThickenedPlank θ b hθ1 hb1)).Pairwise
      (fun Q Q' => _root_.IsEssentiallyDistinct
        ((slabFibreTubes Cfib fibre Yθ S hθ0 Q).carrier :
          Set (EuclideanSpace ℝ (Fin 3)))
        ((slabFibreTubes Cfib fibre Yθ S hθ0 Q').carrier :
          Set (EuclideanSpace ℝ (Fin 3)))))
    (hfullsub : (a / 8 : ℝ≥0) ^ ηKF ≤ ShadedBody.fullness sub
      (fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toShadedBody))
    (hfrost : Kakeya.frostmanConstant fibre (fun Q => Q.toConvexSpaceBody) S.toConvexSpaceBody
      ≤ (Cloc : ENNReal) * CF * ((𝒯.card : ENNReal) / (fibre.card : ENNReal))
          * volume S.carrier) :
    ShadedBody.multiplicity sub
        (fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toShadedBody)
      ≤ ((a / 8 : ℝ≥0) : ENNReal) ^ (-(ε / 2))
        * ((b / 8 : ℝ≥0) : ENNReal) ^ (-2 * β)
        * (((perSlabTubeConst Cfib Cloc / 64 : ℝ≥0) : ENNReal) * CF * (𝒯.card : ENNReal)
            * (θ : ENNReal) * ((b : ℝ≥0) : ENNReal) ^ 2) ^ (1 - β / 2) := by
  set T : ThickenedPlank θ b hθ1 hb1 → ShadedTube (b / 8) (EuclideanSpace ℝ (Fin 3)) :=
    fun Q => slabFibreTubes Cfib fibre Yθ S hθ0 Q with hT_def
  set CFt : ENNReal := perSlabCFtube Cfib Cloc CF 𝒯.card sub.card θ with hCFt_def
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hnsub : sub.card ≠ 0 := Finset.card_ne_zero.mpr hsub_ne
  have hS0 : volume S.carrier ≠ 0 := by
    have hθE : (0 : ENNReal) < (θ : ENNReal) := by exact_mod_cast hθ0
    exact ne_of_gt (lt_of_lt_of_le hθE (Slab.delta_le_volume S))
  have hsum :
      (sub.card : ENNReal) * (((Tube.le_volume.c 3 : ℝ≥0) : ENNReal)
        * ((b / 8 : ℝ≥0) : ENNReal) ^ 2)
      ≤ ∑ Q ∈ sub, volume ((T Q).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    simpa [hT_def] using
      card_mul_le_sum_volume_carrier_slabFibreTubes (Cfib := Cfib) (fibre := fibre) (Yθ := Yθ)
        (S := S) hθ0 sub
  have hCFtube :
      ((fibreTubeLoss Cfib : ℝ≥0) : ENNReal) * ((Cfib : ℝ≥0) : ENNReal) ^ 3
        * ((Cloc : ENNReal) * CF * (𝒯.card : ENNReal) * ((8 * (θ * b) * b : ℝ≥0) : ENNReal))
        * volume (ConvexSpaceBody.closedUnitBall :
            ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))).carrier
      ≤ CFt * ∑ Q ∈ sub, volume ((T Q).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    refine le_trans (perSlabCFtube_frostman_side Cfib Cloc CF hCFtop 𝒯.card sub.card hnsub θ b) ?_
    gcongr
  have hFrostT := isFrostmanIn_slabFibreTubes_sub (𝒯 := 𝒯) (CFtube := CFt)
    hgeom hCfib hθ0 hb0 hfne hS0 hsub hfrost hCFtube
  have hballT : ∀ Q, ((T Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 1 :=
    fun Q => slabFibreTubes_carrier_subset_closedBall hgeom hCfib hθ0 Q
  -- the induced tube Frostman constant is at least one, because the sub-fibre has positive mass
  have hsumpos : 0 < ∑ Q ∈ sub, volume ((T Q).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    refine lt_of_lt_of_le ?_ hsum
    have hcard : (0 : ENNReal) < (sub.card : ENNReal) := by
      exact_mod_cast Nat.pos_of_ne_zero hnsub
    have hc3 : (0 : ENNReal) < ((Tube.le_volume.c 3 : ℝ≥0) : ENNReal) := by
      exact_mod_cast Tube.le_volume.c_pos 3
    have hb8 : (0 : ENNReal) < ((b / 8 : ℝ≥0) : ENNReal) := by
      exact_mod_cast (by positivity : (0 : ℝ≥0) < b / 8)
    positivity
  have hdens : 0 < Kakeya.densityIn sub (fun Q => (T Q).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall := by
    rw [Kakeya.densityIn_of_all_le
      (fun Q _ => SetLike.coe_subset_coe.mp (hballT Q))]
    exact ENNReal.div_pos hsumpos.ne'
      (ConvexSpaceBody.closedUnitBall (E := EuclideanSpace ℝ (Fin 3))).isCompact.measure_ne_top
  have hCFt1 : 1 ≤ CFt := hFrostT.one_le hdens
  have hCFttop : CFt ≠ ⊤ := by
    rw [hCFt_def, perSlabCFtube]
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hCFtop) (ENNReal.natCast_ne_top _))
      ENNReal.coe_ne_top) ?_
    exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hnsub)
  have hδδ₀ : b / 8 ≤ δ₀ := le_trans (div_le_self hb0.le (by norm_num)) hbδ₀
  have hτδ : a / 8 ≤ b / 8 := by gcongr
  have hres := hTS (b / 8) (by positivity) hδδ₀ (a / 8) (by positivity) hτδ sub T
    hballT hpair hfullsub CFt hCFt1 hCFttop hFrostT
  have hp : (0 : ℝ) ≤ 1 - β / 2 := by linarith
  refine hres.trans (le_of_eq ?_)
  calc
    ((a / 8 : ℝ≥0) : ENNReal) ^ (-(ε / 2)) * CFt ^ (1 - β / 2)
        * ((b / 8 : ℝ≥0) : ENNReal) ^ (-2 * β)
        * ((sub.card : ENNReal) * ((b / 8 : ℝ≥0) : ENNReal) ^ 2) ^ (1 - β / 2)
        = ((a / 8 : ℝ≥0) : ENNReal) ^ (-(ε / 2)) * ((b / 8 : ℝ≥0) : ENNReal) ^ (-2 * β)
          * (CFt ^ (1 - β / 2)
            * ((sub.card : ENNReal) * ((b / 8 : ℝ≥0) : ENNReal) ^ 2) ^ (1 - β / 2)) := by
          ring
    _ = ((a / 8 : ℝ≥0) : ENNReal) ^ (-(ε / 2)) * ((b / 8 : ℝ≥0) : ENNReal) ^ (-2 * β)
          * ((CFt * ((sub.card : ENNReal) * ((b / 8 : ℝ≥0) : ENNReal) ^ 2)) ^ (1 - β / 2)) := by
          congr 1
          exact (ENNReal.mul_rpow_of_nonneg _ _ hp).symm
    _ = ((a / 8 : ℝ≥0) : ENNReal) ^ (-(ε / 2)) * ((b / 8 : ℝ≥0) : ENNReal) ^ (-2 * β)
          * (((perSlabTubeConst Cfib Cloc / 64 : ℝ≥0) : ENNReal) * CF * (𝒯.card : ENNReal)
              * (θ : ENNReal) * ((b : ℝ≥0) : ENNReal) ^ 2) ^ (1 - β / 2) := by
          rw [hCFt_def,
            perSlabCFtube_mul_card_mul_sq Cfib Cloc CF hCFtop 𝒯.card sub.card hnsub θ b]

/-- A positive `ℝ≥0` is nonzero when coerced to `ENNReal`. -/
private lemma coe_nn_ne_zero_of_pos {x : ℝ≥0} (hx : 0 < x) : (x : ENNReal) ≠ 0 := by
  exact_mod_cast (ne_of_gt hx)

/-- A real power of a nonzero finite `ENNReal` is nonzero. -/
private lemma enn_rpow_ne_zero {x : ENNReal} (h0 : x ≠ 0) (ht : x ≠ ⊤) (y : ℝ) :
    x ^ y ≠ 0 := by
  simp [ENNReal.rpow_eq_zero_iff, h0, ht]

/-- A real power of a nonzero finite `ENNReal` is finite. -/
private lemma enn_rpow_ne_top {x : ENNReal} (h0 : x ≠ 0) (ht : x ≠ ⊤) (y : ℝ) :
    x ^ y ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero h0 ht

/-- **Per-slab Frostman volume lower bound, from the two-scale tube estimate in threshold form.**

Everything before the analytic call is proved here; the analytic input enters only through the
explicit hypothesis `hTS`, which is exactly
`Kakeya.FrostmanEstimate.multiplicity_bound_tau_isFrostmanIn` after
`mem_nhdsGT_iff_exists_Ioc_subset`. Keeping it as a hypothesis makes the dependency of GWZ Lemma
6.4 on GWZ Lemma 3.9 a single, visible edge. -/
theorem frostmanSlabUnionVolumeLowerBound_of_twoScaleKF {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    {ε : ℝ} (hε : 0 < ε) {ηKF : ℝ} (hηKF : 0 < ηKF) {δ₀ : ℝ≥0} (hδ₀ : 0 < δ₀)
    (hTS : ∀ δ : ℝ≥0, 0 < δ → δ ≤ δ₀ → ∀ τ : ℝ≥0, 0 < τ → τ ≤ δ →
      ∀ {κ : Type} (t : Finset κ) (T : κ → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (t : Set κ).Pairwise
          (fun i j => _root_.IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
        τ ^ ηKF ≤ ShadedBody.fullness t (fun i => (T i).toShadedBody) →
        ∀ CFt : ENNReal, 1 ≤ CFt → CFt ≠ ⊤ →
        ConvexSpaceBody.IsFrostmanIn t (fun i => (T i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall CFt →
        ShadedBody.multiplicity t (fun i => (T i).toShadedBody) ≤
          (τ : ENNReal) ^ (-(ε / 2)) * CFt ^ (1 - β / 2) * (δ : ENNReal) ^ (-2 * β) *
          ((t.card : ENNReal) * (δ : ENNReal) ^ 2) ^ (1 - β / 2)) :
    ∀ c2 > (0 : ℝ≥0), ∀ Cfib : ℝ≥0, 1 ≤ Cfib → ∀ Cloc : ℝ≥0, 1 ≤ Cloc →
      ∃ η > (0 : ℝ), ∃ b₀ > (0 : ℝ≥0), ∃ K : ℝ≥0, 0 < K ∧
      ∀ {a b : ℝ≥0} (ha : 0 < a) (hab : a ≤ b) (hb0 : b ≤ b₀) (hb1 : b ≤ 1)
        {θ : ℝ≥0} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθa : a / b ≤ θ)
        (Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (𝒯 fibre : Finset (ThickenedPlank θ b hθ1 hb1)) (S : Slab θ hθ1) (CF : ENNReal),
        fibre ⊆ 𝒯 → fibre.Nonempty → 1 ≤ CF → CF ≠ ⊤ →
        SlabFibreGeometry fibre Yθ S Cfib →
        (c2 : ℝ≥0) * a ^ (4 * η) ≤ ShadedBody.fullness fibre Yθ →
        Kakeya.frostmanConstant fibre (fun Q => Q.toConvexSpaceBody) S.toConvexSpaceBody
            ≤ (Cloc : ENNReal) * CF
              * ((𝒯.card : ENNReal) / (fibre.card : ENNReal)) * volume S.carrier →
        (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
              * ((b : ENNReal) ^ 2) ^ (β / 2) * (θ : ENNReal) ^ (β / 2)
              * (𝒯.card : ENNReal) ^ (β / 2 - 1) * (fibre.card : ENNReal)
            ≤ (K : ENNReal) * volume (⋃ Q ∈ fibre, (Yθ Q).shade) := by
  intro c2 hc2 Cfib hCfib Cloc hCloc
  obtain ⟨MED, hMED⟩ := exists_pairwiseED_subfibre_package Cfib hCfib
  set Mret : ℝ≥0 := (MED : ℝ≥0) + 1 with hMret_def
  have hmed_nonneg : (0 : ℝ≥0) ≤ (MED : ℝ≥0) := Nat.cast_nonneg MED
  have hMret1 : 1 ≤ Mret := by
    rw [hMret_def]
    simp
  have hMret_pos : 0 < Mret := lt_of_lt_of_le zero_lt_one hMret1
  have hMret_coe : (Mret : ENNReal) = (MED : ENNReal) + 1 := by
    rw [hMret_def]
    norm_num
  set η : ℝ := min (ηKF / 8) (ε / 8) with hη_def
  have hηpos : 0 < η := by
    rw [hη_def]
    exact lt_min (by positivity) (by positivity)
  have hη4KF : 4 * η ≤ ηKF / 2 := by
    rw [hη_def]
    have hle : min (ηKF / 8) (ε / 8) ≤ ηKF / 8 := min_le_left (ηKF / 8) (ε / 8)
    linarith
  have hη4ε : 4 * η ≤ ε / 2 := by
    rw [hη_def]
    have hle : min (ηKF / 8) (ε / 8) ≤ ε / 8 := min_le_right (ηKF / 8) (ε / 8)
    linarith
  set G : ℝ≥0 := Mret⁻¹ * (fibreTubeLoss Cfib)⁻¹ * c2 with hG_def
  have hG : 0 < G := by
    rw [hG_def]
    have hft : 0 < fibreTubeLoss Cfib := lt_of_lt_of_le zero_lt_one (one_le_fibreTubeLoss Cfib)
    positivity
  obtain ⟨b₁, hb₁0, hb₁1le1, hb₁le⟩ :=
    exists_nnreal_rpow_le (p := ηKF - 4 * η) (by linarith : 0 < ηKF - 4 * η) hG
  set Kc : ℝ≥0 := perSlabTubeConst Cfib Cloc / 64 with hKc_def
  refine ⟨η, hηpos, min b₁ δ₀, lt_min hb₁0 hδ₀, perSlabLoss ε c2 Cfib Mret Kc,
    perSlabLoss_pos hc2 hCfib hMret1, ?_⟩
  intro a b ha hab hb₀ hb1 θ hθ0 hθ1 hθa Yθ 𝒯 fibre S CF hf𝒢 hfne hCF1 hCFtop
    hgeom hfull hfrost
  have hbnz : 0 < b := lt_of_lt_of_le ha hab
  have hbb₁ : b ≤ b₁ := le_trans hb₀ (min_le_left b₁ δ₀)
  have hbδ₀ : b ≤ δ₀ := le_trans hb₀ (min_le_right b₁ δ₀)
  obtain ⟨sub, hsub, hpair, hmassret, hfullret⟩ := hMED fibre Yθ S hbnz hθ0 hgeom
  have hsub_ne : sub.Nonempty := by
    by_contra hempty
    have hsub0 : sub = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hsum0 : (∑ Q ∈ sub, volume (Yθ Q).shade) = 0 := by simp [hsub0]
    have hle : (∑ Q ∈ fibre, volume (Yθ Q).shade) ≤ 0 := by
      calc
        (∑ Q ∈ fibre, volume (Yθ Q).shade)
            ≤ ((MED : ENNReal) + 1) * ∑ Q ∈ sub, volume (Yθ Q).shade := hmassret
        _ = 0 := by rw [hsum0]; simp
    exact (not_lt_of_ge hle) hgeom.mass_pos
  let T : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)) :=
    fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toShadedBody
  have hft : (fibreTubeLoss Cfib)⁻¹ * ShadedBody.fullness fibre Yθ
      ≤ ShadedBody.fullness fibre T := by
    simpa [T] using slabFibreTubes_fullness hgeom hCfib hθ0 hbnz
  have hfret_nn : ShadedBody.fullness fibre T ≤ Mret * ShadedBody.fullness sub T := by
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_mul]
    rw [ShadedBody.coe_fullness fibre T, ShadedBody.coe_fullness sub T]
    rw [hMret_coe]
    exact hfullret
  have hGfull : G * a ^ (4 * η) ≤ ShadedBody.fullness sub T := by
    rw [hG_def]
    calc
      (Mret⁻¹ * (fibreTubeLoss Cfib)⁻¹ * c2 * a ^ (4 * η))
          = Mret⁻¹ * ((fibreTubeLoss Cfib)⁻¹ * (c2 * a ^ (4 * η))) := by
            ring
      _ ≤ Mret⁻¹ * ShadedBody.fullness fibre T := by
            gcongr
            have hinv : (0 : ℝ≥0) ≤ (fibreTubeLoss Cfib)⁻¹ := zero_le
            exact le_trans (mul_le_mul_of_nonneg_left hfull hinv) hft
      _ ≤ ShadedBody.fullness sub T := by
            calc
              Mret⁻¹ * ShadedBody.fullness fibre T
                  ≤ Mret⁻¹ * (Mret * ShadedBody.fullness sub T) := by
                    exact mul_le_mul_of_nonneg_left hfret_nn (inv_nonneg.mpr (le_of_lt hMret_pos))
              _ = ShadedBody.fullness sub T := by
                    rw [← mul_assoc, inv_mul_cancel₀ hMret_pos.ne', one_mul]
  have hη4lt : 0 < ηKF - 4 * η := by linarith
  have hb₀pow : (min b₁ δ₀) ^ (ηKF - 4 * η) ≤ G := by
    exact le_trans (NNReal.rpow_le_rpow (min_le_left b₁ δ₀) hη4lt.le) hb₁le
  have hb₀1 : min b₁ δ₀ ≤ 1 := le_trans (min_le_left b₁ δ₀) hb₁1le1
  have hthr : (a / 8 : ℝ≥0) ^ ηKF ≤ ShadedBody.fullness sub T := by
    exact le_trans
      (perSlabFullnessThreshold (ηKF := ηKF) hηKF hηpos hη4KF hG ha hab hb₀ hb₀1 hb₀pow)
      hGfull
  have hmT : 𝒯.card ≠ 0 := by
    have hfbne : 0 < fibre.card := Finset.card_pos.mpr hfne
    have hle : fibre.card ≤ 𝒯.card := Finset.card_le_card hf𝒢
    exact ne_of_gt (lt_of_lt_of_le hfbne hle)
  have hmult := Plank.perSlabMultiplicityBound (β := β) (ε := ε) (ηKF := ηKF) (δ₀ := δ₀)
    hβpos hβle hε hTS hCfib hCloc ha hab hbδ₀ hθ0
    hCF1 hCFtop hgeom hfne hsub hsub_ne hpair hthr hfrost
  let B : ENNReal :=
    (((a / 8 : ℝ≥0)) : ENNReal) ^ (-(ε / 2)) * (((b / 8 : ℝ≥0)) : ENNReal) ^ (-2 * β)
      * ((Kc : ENNReal) * CF * (𝒯.card : ENNReal) * (θ : ENNReal)
          * ((b : ℝ≥0) : ENNReal) ^ 2) ^ (1 - β / 2)
  have hmult' : ShadedBody.multiplicity sub T ≤ B := by
    simpa [T, B, hKc_def] using hmult
  have hshade : (∑ Q ∈ fibre, volume (Yθ Q).shade)
      ≤ ((MED : ENNReal) + 1) * B * volume (⋃ Q ∈ fibre, (Yθ Q).shade) :=
    Plank.sum_shade_le_of_multiplicity_le (M := (MED : ENNReal) + 1) (B := B)
      hgeom hCfib hθ0 hsub hmassret hmult'
  have hmassLB := Plank.perSlabMassBound (G := c2 * a ^ (4 * η)) hgeom hfull
  have hscal := Plank.perSlabScalar (η := η) (Kc := Kc) (nf := fibre.card)
    hβpos hβle hε hηpos hη4ε
    ha hab hb1 hθ0 hθ1 hc2 hCfib hMret1 hCF1 hCFtop hmT
  let X : ENNReal :=
    ((c2 * a ^ (4 * η) : ℝ≥0) : ENNReal)
      * ((fibre.card : ENNReal)
        * (((Cfib : ℝ≥0) : ENNReal) ^ 3 * ((8 * (θ * b) * b : ℝ≥0) : ENNReal)))
  let U : ENNReal := volume (⋃ Q ∈ fibre, (Yθ Q).shade)
  let W : ENNReal := (Mret : ENNReal) * B
  let K : ENNReal := (perSlabLoss ε c2 Cfib Mret Kc : ENNReal)
  let targetLHS : ENNReal :=
    (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
      * ((b : ENNReal) ^ 2) ^ (β / 2) * (θ : ENNReal) ^ (β / 2)
      * (𝒯.card : ENNReal) ^ (β / 2 - 1) * (fibre.card : ENNReal)
  have h1 : X ≤ W * U := by
    refine le_trans hmassLB ?_
    change (∑ Q ∈ fibre, volume (Yθ Q).shade)
      ≤ (Mret : ENNReal) * B * volume (⋃ Q ∈ fibre, (Yθ Q).shade)
    rw [hMret_coe]
    exact hshade
  have h2 : targetLHS * W ≤ K * X := by
    convert hscal using 1 <;> ring
  have h_a8 : (0 : ℝ≥0) < a / 8 := by positivity
  have h_b8 : (0 : ℝ≥0) < b / 8 := by positivity
  have h_Kc_pos : 0 < Kc := by
    rw [hKc_def]
    have hc : 0 < perSlabTubeConst Cfib Cloc := perSlabTubeConst_pos Cfib Cloc hCfib hCloc
    positivity
  have h_Kc0 : (Kc : ENNReal) ≠ 0 := coe_nn_ne_zero_of_pos h_Kc_pos
  have h_MretE : (Mret : ENNReal) ≠ 0 := coe_nn_ne_zero_of_pos hMret_pos
  have h_Mret_top : (Mret : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have h_CF0 : CF ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hCF1)
  have h_mT0 : (𝒯.card : ENNReal) ≠ 0 := by exact_mod_cast hmT
  have h_mT_top : (𝒯.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h_b0e : (b : ENNReal) ≠ 0 := coe_nn_ne_zero_of_pos hbnz
  have h_θ0e : (θ : ENNReal) ≠ 0 := coe_nn_ne_zero_of_pos hθ0
  have h_bpow0 : ((b : ℝ≥0) : ENNReal) ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_ne_zero h_b0e h_b0e
  have h_bpow_top : ((b : ℝ≥0) : ENNReal) ^ 2 ≠ ⊤ := by
    rw [pow_two]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hbig0 :
      ((Kc : ENNReal) * CF * (𝒯.card : ENNReal) * (θ : ENNReal)
          * ((b : ℝ≥0) : ENNReal) ^ 2) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero h_Kc0 h_CF0) h_mT0) h_θ0e)
      h_bpow0
  have hbig_top :
      ((Kc : ENNReal) * CF * (𝒯.card : ENNReal) * (θ : ENNReal)
          * ((b : ℝ≥0) : ENNReal) ^ 2) ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hCFtop) h_mT_top)
        ENNReal.coe_ne_top)
      h_bpow_top
  have hW0 : W ≠ 0 := by
    have hB0 : B ≠ 0 := by
      change ((((a / 8 : ℝ≥0)) : ENNReal) ^ (-(ε / 2)))
          * ((((b / 8 : ℝ≥0)) : ENNReal) ^ (-2 * β))
          * (((Kc : ENNReal) * CF * (𝒯.card : ENNReal) * (θ : ENNReal)
              * ((b : ℝ≥0) : ENNReal) ^ 2) ^ (1 - β / 2)) ≠ 0
      have h1f : (((a / 8 : ℝ≥0)) : ENNReal) ^ (-(ε / 2)) ≠ 0 :=
        enn_rpow_ne_zero (coe_nn_ne_zero_of_pos h_a8) ENNReal.coe_ne_top (-(ε / 2))
      have h2f : (((b / 8 : ℝ≥0)) : ENNReal) ^ (-2 * β) ≠ 0 :=
        enn_rpow_ne_zero (coe_nn_ne_zero_of_pos h_b8) ENNReal.coe_ne_top (-2 * β)
      have h3f : ((((Kc : ENNReal) * CF * (𝒯.card : ENNReal) * (θ : ENNReal)
          * ((b : ℝ≥0) : ENNReal) ^ 2)) ^ (1 - β / 2)) ≠ 0 :=
        enn_rpow_ne_zero hbig0 hbig_top (1 - β / 2)
      exact mul_ne_zero (mul_ne_zero h1f h2f) h3f
    change (Mret : ENNReal) * B ≠ 0
    exact mul_ne_zero h_MretE hB0
  have hWtop : W ≠ ⊤ := by
    have hB_top : B ≠ ⊤ := by
      change ((((a / 8 : ℝ≥0)) : ENNReal) ^ (-(ε / 2)))
          * ((((b / 8 : ℝ≥0)) : ENNReal) ^ (-2 * β))
          * (((Kc : ENNReal) * CF * (𝒯.card : ENNReal) * (θ : ENNReal)
              * ((b : ℝ≥0) : ENNReal) ^ 2) ^ (1 - β / 2)) ≠ ⊤
      have h1f : (((a / 8 : ℝ≥0)) : ENNReal) ^ (-(ε / 2)) ≠ ⊤ :=
        enn_rpow_ne_top (coe_nn_ne_zero_of_pos h_a8) ENNReal.coe_ne_top (-(ε / 2))
      have h2f : (((b / 8 : ℝ≥0)) : ENNReal) ^ (-2 * β) ≠ ⊤ :=
        enn_rpow_ne_top (coe_nn_ne_zero_of_pos h_b8) ENNReal.coe_ne_top (-2 * β)
      have h3f : ((((Kc : ENNReal) * CF * (𝒯.card : ENNReal) * (θ : ENNReal)
          * ((b : ℝ≥0) : ENNReal) ^ 2)) ^ (1 - β / 2)) ≠ ⊤ :=
        enn_rpow_ne_top hbig0 hbig_top (1 - β / 2)
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top h1f h2f) h3f
    change (Mret : ENNReal) * B ≠ ⊤
    exact ENNReal.mul_ne_top h_Mret_top hB_top
  exact le_of_mul_le_of_le_mul (G := targetLHS) (K := K) (X := X) (U := U) (W := W)
    hW0 hWtop h1 h2

/-- **Per-slab Frostman volume lower bound** (the analysis leaf of GWZ Lemma 6.4).

This is `Plank.frostmanSlabUnionVolumeLowerBound_of_twoScaleKF` with the analytic input supplied by
`Kakeya.FrostmanEstimate.multiplicity_bound_tau_isFrostmanIn`, converted from its `∀ᶠ δ in 𝓝[>] 0`
form to the threshold form by `mem_nhdsGT_iff_exists_Ioc_subset`. The universe of the tube families
is descended to `Type 0` by `Kakeya.FrostmanEstimate.toTypeZero`, so the hypothesis `hKF` stays fully
universe-polymorphic and no Section 6 statement needs a universe annotation. -/
theorem frostmanSlabUnionVolumeLowerBound_proof {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKF : Kakeya.FrostmanEstimate (EuclideanSpace ℝ (Fin 3)) β) :
    ∀ ε > (0 : ℝ), ∀ c2 > (0 : ℝ≥0), ∀ Cfib : ℝ≥0, 1 ≤ Cfib → ∀ Cloc : ℝ≥0, 1 ≤ Cloc →
      ∃ η > (0 : ℝ), ∃ b₀ > (0 : ℝ≥0), ∃ K : ℝ≥0, 0 < K ∧
      ∀ {a b : ℝ≥0} (ha : 0 < a) (hab : a ≤ b) (hb0 : b ≤ b₀) (hb1 : b ≤ 1)
        {θ : ℝ≥0} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθa : a / b ≤ θ)
        (Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (𝒯 fibre : Finset (ThickenedPlank θ b hθ1 hb1)) (S : Slab θ hθ1) (CF : ENNReal),
        fibre ⊆ 𝒯 → fibre.Nonempty → 1 ≤ CF → CF ≠ ⊤ →
        SlabFibreGeometry fibre Yθ S Cfib →
        (c2 : ℝ≥0) * a ^ (4 * η) ≤ ShadedBody.fullness fibre Yθ →
        Kakeya.frostmanConstant fibre (fun Q => Q.toConvexSpaceBody) S.toConvexSpaceBody
            ≤ (Cloc : ENNReal) * CF
              * ((𝒯.card : ENNReal) / (fibre.card : ENNReal)) * volume S.carrier →
        (a : ENNReal) ^ ε * CF ^ (β / 2 - 1) * (b : ENNReal) ^ (2 * β)
              * ((b : ENNReal) ^ 2) ^ (β / 2) * (θ : ENNReal) ^ (β / 2)
              * (𝒯.card : ENNReal) ^ (β / 2 - 1) * (fibre.card : ENNReal)
            ≤ (K : ENNReal) * volume (⋃ Q ∈ fibre, (Yθ Q).shade) := by
  intro ε hε
  obtain ⟨ηKF, hηKF, hev⟩ :=
    Kakeya.FrostmanEstimate.multiplicity_bound_tau_isFrostmanIn
      (EuclideanSpace ℝ (Fin 3)) hβpos.le hβle (by rw [finrank_three]; norm_num)
      (Kakeya.FrostmanEstimate.toTypeZero _ hKF) (ε / 2) (by linarith)
  obtain ⟨δ₀, hδ₀, hIoc⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  refine frostmanSlabUnionVolumeLowerBound_of_twoScaleKF hβpos hβle hε hηKF hδ₀ ?_
  intro δ hδ0 hδδ₀ τ hτ0 hτδ κ t T hball hpair hfull CFt hCFt1 hCFttop hFrost
  have hres := hIoc ⟨hδ0, hδδ₀⟩ τ hτ0 hτδ t T hball hpair hfull CFt hCFt1 hCFttop hFrost
  simpa [finrank_three] using hres

end Plank

end

end
