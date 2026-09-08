/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.DimensionThree.Plank.SlabFamilyControl
public import Kakeya.DimensionThree.Plank.RepresentativeDensity
public import Kakeya.DimensionThree.Plank.DilatedSlabTube
public import Kakeya.DimensionThree.Plank.Reduction
public import Kakeya.DimensionThree.Plank.SlabwiseReduction
public import Kakeya.PartialEstimates
public import Kakeya.Factorization
public import Kakeya.Uniform
public import Kakeya.ShadedUniform
public import Kakeya.FrostmanConstant

/-!
# Inputs for the GWZ Katz-Tao plank estimate

This module contains the geometric and scalar helper layer used by GWZ Lemma 6.1.
The final public estimates live in `KatzTaoPlankEstimate.lean`.
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody
open scoped NNReal Real ENNReal Classical

noncomputable section

namespace Kakeya

/-- **The long half-width of the slabs of GWZ Lemma 6.1**: twice the plank window radius.

A GWZ slab is the `θ`-neighbourhood of a *plane* intersected with the working window, so its long
extent is that of the window.  `Slab θ = Prism3D θ 1 1` has long half-widths `1` — exactly a plank's
own length — and exact containment in such a box is a strictly weaker requirement: for `b` close to
`1` a plank fits only when its in-plane pose matches the box's exactly.  Stating the slab
non-concentration hypothesis over `Prism3D φ Rslab Rslab` is the faithful reading, and it is the one
that controls a family which is merely contained in a fixed dilation of a slab
(`Plank.card_le_of_wideSlabNonconcentration`): the two long coordinates of a windowed plank relative
to any slab centred in the window are bounded by `2 * plankWindowRadius` for free. -/
def Rslab : ℝ≥0 := 2 * plankWindowRadius

theorem one_le_Rslab : 1 ≤ Rslab := by
  rw [Rslab, plankWindowRadius]
  norm_num

/-- **GWZ Remark 6.3: the low-multiplicity branch of Lemma 6.1 is automatic.**

The right-hand side of Lemma 6.1 is at least `a ^ (-η)` as soon as `η + η * β ≤ ε`.  Two inputs: the
slab hypothesis applied at the smallest legal scale `φ = a / b` to the wide slab of a plank's own
frame (`Plank.mem_inWideSlabFamily_toWideSlab`) gives `1 ≤ a ^ (-η) * (a/b) ^ γ * |s|`, and a
nonempty family of planks of positive volume has `1 ≤ Δ_max` (`Kakeya.one_le_maxDensity`).  Hence in
the branch `μ ≤ a ^ (-η)` the conclusion of Lemma 6.1 holds with no geometry at all. -/
theorem RHSplankKT_ge_smallMultiplicityThreshold {ι : Type*} {a b : ℝ≥0} {hab : a ≤ b}
    {hb1 : b ≤ 1} (s : Finset ι) (V : ι → ShadedPlank a b hab hb1) {β γ η ε : ℝ}
    (ha : 0 < a) (hβpos : 0 < β) (hβle : β ≤ 1) (hγ0 : 0 ≤ γ) (hη : 0 ≤ η)
    (hηε : η + η * β ≤ ε) (hs : s.Nonempty)
    (hslab : ∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a / b ≤ φ →
      ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
        ((Plank.inWideSlabFamily s (fun i => (V i).toPrism3D) S).card : ℝ≥0)
          ≤ a ^ (-η) * φ ^ γ * (s.card : ℝ≥0)) :
    (a : ENNReal) ^ (-η) ≤
      (a : ENNReal) ^ (-ε)
        * (maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β)
        * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β := by
  obtain ⟨i₀, hi₀⟩ := hs
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have ha1 : a ≤ 1 := hab.trans hb1
  have hdb1 : a / b ≤ 1 := div_le_one_of_le₀ hab hb0.le
  have hdbR : a / b ≤ Rslab := hdb1.trans one_le_Rslab
  have hadb : a ≤ a / b := by
    rw [le_div_iff₀ hb0]
    calc
      a * b ≤ a * 1 := by gcongr
      _ = a := mul_one a
  -- (i) The slab hypothesis at the smallest legal scale `φ = a / b`.
  let S : Prism3D (a / b) Rslab Rslab hdbR le_rfl :=
    Plank.toWideSlab ((V i₀).toPrism3D) (a / b) Rslab hdbR
  have hmem : i₀ ∈ Plank.inWideSlabFamily s (fun i => (V i).toPrism3D) S := by
    simpa [S] using (Plank.mem_inWideSlabFamily_toWideSlab (V := fun i => (V i).toPrism3D)
      hi₀ hadb one_le_Rslab hdbR)
  have hpos : 0 < (Plank.inWideSlabFamily s (fun i => (V i).toPrism3D) S).card :=
    Finset.card_pos.mpr ⟨i₀, hmem⟩
  have hone : (1 : ℝ≥0) ≤ (Plank.inWideSlabFamily s (fun i => (V i).toPrism3D) S).card := by
    exact_mod_cast (Nat.succ_le_of_lt hpos)
  have hcard := hslab (a / b) hdbR le_rfl S
  have h1 : (1 : ℝ≥0) ≤ a ^ (-η) * (a / b) ^ γ * (s.card : ℝ≥0) := hone.trans hcard
  -- (ii) Cast to `ENNReal` and raise to the power `β`.
  have hab0 : a / b ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hadb)
  have h1e : (1 : ENNReal) ≤
      (a : ENNReal) ^ (-η) * ((a : ENNReal) / (b : ENNReal)) ^ γ * (s.card : ENNReal) := by
    have hcast := ENNReal.coe_le_coe.mpr h1
    rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero ha.ne',
        ENNReal.coe_rpow_of_ne_zero hab0, ENNReal.coe_div hb0.ne'] at hcast
    simpa using hcast
  have h1eβ : (1 : ENNReal) ≤
      (a : ENNReal) ^ (-η * β) * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β)
        * (s.card : ENNReal) ^ β := by
    have hpow := ENNReal.rpow_le_rpow h1e hβpos.le
    rw [ENNReal.one_rpow] at hpow
    rw [ENNReal.mul_rpow_of_nonneg _ _ hβpos.le, ENNReal.mul_rpow_of_nonneg _ _ hβpos.le] at hpow
    rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hpow
    exact hpow
  -- (iii) Clear the negative power by multiplying by `a ^ (η * β)`.
  have hA0 : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr ha.ne'
  have hAtop : (a : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hcancel : (a : ENNReal) ^ (-η * β) * (a : ENNReal) ^ (η * β) = 1 := by
    rw [← ENNReal.rpow_add (-η * β) (η * β) hA0 hAtop]
    rw [show (-η * β) + η * β = 0 by ring]
    rw [ENNReal.rpow_zero]
  have hclear : (a : ENNReal) ^ (η * β) ≤
      ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β := by
    calc
      (a : ENNReal) ^ (η * β) = 1 * (a : ENNReal) ^ (η * β) := by rw [one_mul]
      _ ≤ ((a : ENNReal) ^ (-η * β) * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β)
            * (s.card : ENNReal) ^ β) * (a : ENNReal) ^ (η * β) :=
        mul_le_mul' h1eβ le_rfl
      _ = ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β := by
        calc
          (((a : ENNReal) ^ (-η * β) * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β)
              * (s.card : ENNReal) ^ β) * (a : ENNReal) ^ (η * β))
              = (((a : ENNReal) ^ (-η * β) * (a : ENNReal) ^ (η * β))
                  * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β) := by
                ac_rfl
          _ = ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β := by
                rw [hcancel]
                rw [one_mul]
  -- (iv) Insert the `≥ 1` density factor and chain.
  have hβ1m : 0 ≤ 1 - β := by linarith
  have hA1 : (a : ENNReal) ≤ 1 := ENNReal.coe_le_coe.mpr ha1
  have hvol_pos : 0 < volume ((V i₀).toConvexSpaceBody).carrier := by
    change 0 < volume (((V i₀).toConvexSpaceBody) : Set (EuclideanSpace ℝ (Fin 3)))
    rw [show ((V i₀).toConvexSpaceBody : Set (EuclideanSpace ℝ (Fin 3))) =
        (V i₀).toPrism3D.carrier from rfl]
    rw [Prism3D.volume_carrier]
    have haE : (0 : ENNReal) < (a : ENNReal) := by exact_mod_cast ha
    have hbE : (0 : ENNReal) < (b : ENNReal) := by exact_mod_cast hb0
    positivity
  have hΔ1 : 1 ≤ maxDensity s (fun i => (V i).toConvexSpaceBody) :=
    one_le_maxDensity (s := s) (W := fun i => (V i).toConvexSpaceBody) ⟨i₀, hi₀, hvol_pos⟩
  have hΔ1pow : 1 ≤ (maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β) := by
    calc
      1 = (1 : ENNReal) ^ (1 - β) := by rw [ENNReal.one_rpow]
      _ ≤ (maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β) :=
        ENNReal.rpow_le_rpow hΔ1 hβ1m
  calc
    (a : ENNReal) ^ (-η) ≤ (a : ENNReal) ^ (-ε + η * β) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hA1 (by linarith)
    _ = (a : ENNReal) ^ (-ε) * (a : ENNReal) ^ (η * β) := by
      rw [ENNReal.rpow_add (-ε) (η * β) hA0 hAtop]
    _ ≤ (a : ENNReal) ^ (-ε) *
          (((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β) :=
      mul_le_mul_of_nonneg_left hclear bot_le
    _ = (a : ENNReal) ^ (-ε) * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β)
          * (s.card : ENNReal) ^ β := by
      rw [mul_assoc]
    _ ≤ (a : ENNReal) ^ (-ε) * (maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β)
          * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β := by
      have hmiddle : ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β ≤
          (maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β)
            * (((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β) := by
        simpa [one_mul] using (mul_le_mul' hΔ1pow le_rfl)
      have hle : (a : ENNReal) ^ (-ε) *
            (((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β) ≤
          (a : ENNReal) ^ (-ε) *
            ((maxDensity s (fun i => (V i).toConvexSpaceBody)) ^ (1 - β)
              * (((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (s.card : ENNReal) ^ β)) :=
        mul_le_mul_of_nonneg_left hmiddle bot_le
      simpa [mul_assoc] using hle

/-! ### Algebraic and structural inputs to GWZ Lemma 6.1 -/

/-- **The `N`-cancellation of GWZ Lemma 6.1.**  Item 4 of Lemma 6.13 contributes the factor
`u · N = a·N/(b·θ)`, the representative density transfer contributes `(u · N)⁻¹ ^ (1 - β)`, and the
assigned-representative cardinality bound contributes `N ^ (-β)`.  Their product is `u ^ β`: the
fibre scale `N` disappears completely. -/
theorem plankKT_scale_cancel {β : ℝ} {u N : ENNReal}
    (hu0 : u ≠ 0) (hutop : u ≠ ⊤) (hN0 : N ≠ 0) (hNtop : N ≠ ⊤) :
    (u * N) * ((u * N)⁻¹) ^ (1 - β) * N ^ (-β) = u ^ β := by
  have hw0 : u * N ≠ 0 := mul_ne_zero hu0 hN0
  have hwtop : u * N ≠ ⊤ := ENNReal.mul_ne_top hutop hNtop
  have hwβ : (u * N) ^ β = u ^ β * N ^ β :=
    ENNReal.mul_rpow_of_ne_zero hu0 hN0 β
  have hcancel : N ^ β * N ^ (-β) = 1 := by
    rw [← ENNReal.rpow_add β (-β) hN0 hNtop]
    rw [show β + (-β) = (0 : ℝ) by ring, ENNReal.rpow_zero]
  calc
    (u * N) * ((u * N)⁻¹) ^ (1 - β) * N ^ (-β)
        = ((u * N) * ((u * N)⁻¹) ^ (1 - β)) * N ^ (-β) := by rw [mul_assoc]
    _ = (u * N) ^ β * N ^ (-β) := by
      congr 1
      calc
        (u * N) * ((u * N)⁻¹) ^ (1 - β)
            = (u * N) ^ (1 : ℝ) * ((u * N)⁻¹) ^ (1 - β) := by rw [ENNReal.rpow_one]
        _ = (u * N) ^ (1 : ℝ) * (u * N) ^ (-(1 - β)) := by
          rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg]
        _ = (u * N) ^ ((1 : ℝ) + (-(1 - β))) := by
          rw [ENNReal.rpow_add (1 : ℝ) (-(1 - β)) hw0 hwtop]
        _ = (u * N) ^ β := by
          congr 1
          ring
    _ = (u ^ β * N ^ β) * N ^ (-β) := by rw [hwβ]
    _ = u ^ β * (N ^ β * N ^ (-β)) := by rw [mul_assoc]
    _ = u ^ β * (1 : ENNReal) := by rw [hcancel]
    _ = u ^ β := by rw [mul_one]

/-- **From the slab scale to the eccentricity.**  With `a / b ≤ θ ≤ 1`, `0 ≤ γ ≤ 1` and `0 < β`,
the surviving scale factor `(a / (b θ)) ^ β` together with the slab gain `θ ^ (γ β)` is at most the
eccentricity factor `(a / b) ^ (γ β)` of the conclusion: writing the left side as
`(a/b) ^ β · θ ^ ((γ - 1) β)` and using `θ ≥ a / b` with the nonpositive exponent `(γ - 1) β`. -/
theorem theta_factor_le_eccentricity_factor {a b θ : ℝ≥0} {β γ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hθ0 : 0 < θ) (hθ : a / b ≤ θ) (hβ : 0 < β)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ((a : ENNReal) / ((b : ENNReal) * (θ : ENNReal))) ^ β * (θ : ENNReal) ^ (γ * β)
      ≤ ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hθnz : θ ≠ 0 := ne_of_gt hθ0
  have hβ0 : 0 ≤ β := hβ.le
  -- r := a / b in ℝ≥0
  let r : ℝ≥0 := a / b
  have hrr : (r : ENNReal) = (a : ENNReal) / (b : ENNReal) := by
    dsimp [r]
    exact ENNReal.coe_div hb0
  have hr0 : r ≠ 0 := ne_of_gt (div_pos ha hb)
  have hr_ne : (r : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hr0
  have hr_top : (r : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hrle : (r : ENNReal) ≤ (θ : ENNReal) := by
    dsimp [r]
    exact ENNReal.coe_le_coe.mpr hθ
  have hθnzE : (θ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hθnz
  have hθtop : (θ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- exponent e0 = -((γ - 1) * β) ≥ 0, so (γ - 1) * β = -e0
  let e0 : ℝ := -((γ - 1) * β)
  have hen_le : (γ - 1) * β ≤ 0 := by
    have hgm : γ - 1 ≤ 0 := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg hgm hβ0
  have he0 : 0 ≤ e0 := by dsimp [e0]; exact neg_nonneg.mpr hen_le
  -- Step 1: factor the left-hand side
  have hfactor :
      ((a : ENNReal) / ((b : ENNReal) * (θ : ENNReal))) ^ β * (θ : ENNReal) ^ (γ * β)
        = (r : ENNReal) ^ β * (θ : ENNReal) ^ ((γ - 1) * β) := by
    have hquot :
        (a : ENNReal) / ((b : ENNReal) * (θ : ENNReal)) = (r : ENNReal) / (θ : ENNReal) := by
      have hbθ0 : (b * θ : ℝ≥0) ≠ 0 := mul_ne_zero hb0 hθnz
      have hmid : (a / (b * θ) : ℝ≥0) = (a / b) / θ := by
        apply NNReal.coe_injective
        rw [NNReal.coe_div (a : ℝ≥0) (b * θ : ℝ≥0)]
        rw [NNReal.coe_div (a / b : ℝ≥0) θ, NNReal.coe_div a b]
        rw [NNReal.coe_mul]
        ring
      calc
        (a : ENNReal) / ((b : ENNReal) * (θ : ENNReal))
          = (a : ENNReal) / (((b * θ : ℝ≥0) : ENNReal)) := by
              rw [← ENNReal.coe_mul]
        _ = ((a / (b * θ) : ℝ≥0) : ENNReal) := (ENNReal.coe_div hbθ0).symm
        _ = (((a / b : ℝ≥0) / θ : ℝ≥0) : ENNReal) := by
              rw [hmid]
        _ = (r : ENNReal) / (θ : ENNReal) := by
              dsimp [r]
              exact ENNReal.coe_div hθnz
    -- (r / θ) ^ β = (r) ^ β * (θ) ^ (-β)
    have hfactor1 : ((r : ENNReal) / (θ : ENNReal)) ^ β =
        (r : ENNReal) ^ β * (θ : ENNReal) ^ (-β) := by
      rw [ENNReal.div_rpow_of_nonneg (r : ENNReal) (θ : ENNReal) hβ0]
      rw [ENNReal.div_eq_inv_mul]
      rw [ENNReal.rpow_neg (θ : ENNReal) β]
      rw [mul_comm]
    calc
      ((a : ENNReal) / ((b : ENNReal) * (θ : ENNReal))) ^ β * (θ : ENNReal) ^ (γ * β)
        = (r : ENNReal) ^ β * (θ : ENNReal) ^ (-β) * (θ : ENNReal) ^ (γ * β) := by
          rw [hquot, hfactor1]
      _ = (r : ENNReal) ^ β * (θ : ENNReal) ^ (γ * β - β) := by
          rw [mul_assoc]
          rw [← ENNReal.rpow_add (-β) (γ * β) hθnzE hθtop]
          rw [show (-β) + (γ * β) = γ * β - β by ring]
      _ = (r : ENNReal) ^ β * (θ : ENNReal) ^ ((γ - 1) * β) := by
          rw [show γ * β - β = (γ - 1) * β by ring]
  -- Step 2: antitonicity of x ↦ x^en (en ≤ 0) gives θ^en ≤ r^en
  have hanti : (θ : ENNReal) ^ (-e0) ≤ (r : ENNReal) ^ (-e0) := by
    have hpow : (r : ENNReal) ^ e0 ≤ (θ : ENNReal) ^ e0 :=
      ENNReal.monotone_rpow_of_nonneg he0 hrle
    rw [ENNReal.rpow_neg (θ : ENNReal) e0, ENNReal.rpow_neg (r : ENNReal) e0]
    exact (ENNReal.inv_le_inv).mpr hpow
  have hle2 : (r : ENNReal) ^ β * (θ : ENNReal) ^ ((γ - 1) * β) ≤ (r : ENNReal) ^ (γ * β) := by
    calc
      (r : ENNReal) ^ β * (θ : ENNReal) ^ ((γ - 1) * β)
        = (r : ENNReal) ^ β * (θ : ENNReal) ^ (-e0) := by
          rw [show (γ - 1) * β = -e0 by dsimp [e0]; ring]
      _ ≤ (r : ENNReal) ^ β * (r : ENNReal) ^ (-e0) :=
          mul_le_mul_of_nonneg_left hanti bot_le
      _ = (r : ENNReal) ^ (β + (-e0)) := by
          rw [← ENNReal.rpow_add β (-e0) hr_ne hr_top]
      _ = (r : ENNReal) ^ (γ * β) := by
          rw [show β + (-e0) = γ * β by dsimp [e0]; ring]
  calc
    ((a : ENNReal) / ((b : ENNReal) * (θ : ENNReal))) ^ β * (θ : ENNReal) ^ (γ * β)
      = (r : ENNReal) ^ β * (θ : ENNReal) ^ ((γ - 1) * β) := hfactor
    _ ≤ (r : ENNReal) ^ (γ * β) := hle2
    _ = ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) := by
        rw [← hrr]

/-- **Absorbing a fixed constant into a negative power of a small scale.**  (Local copy of
`Kakeya.rpowConstAbsorb` of `PlankFactorizationEstimate.lean`, which is downstream of this file.) -/
theorem plankKT_absorb (C : ℝ≥0) (hC : 1 ≤ C) {p e : ℝ} (hp : 0 ≤ p) (he : 0 < e) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ δ : ℝ≥0, 0 < δ → δ ≤ δ₀ →
      (C : ENNReal) ^ p ≤ (δ : ENNReal) ^ (-e) := by
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hC
  have hC0_ne : C ≠ 0 := hC0.ne'
  have he_ne : e ≠ 0 := by linarith
  set δ₀ : ℝ≥0 := C ^ (-p / e) with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := NNReal.rpow_pos hC0
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro δ hδ hδle
  -- lift δ ≤ δ₀ to ENNReal
  have hδle_coe : (δ : ENNReal) ≤ (δ₀ : ENNReal) := by exact mod_cast hδle
  have hδ0_ne : (δ : ENNReal) ≠ 0 := by exact mod_cast hδ.ne'
  have hδ_top_ne : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ₀_top_ne : (δ₀ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ₀_0_ne : (δ₀ : ENNReal) ≠ 0 := by exact mod_cast hδ₀_pos.ne'
  have hC_enn_ne0 : (C : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hC0_ne
  have hC_enn_ne_top : (C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- Step 1: show that (δ₀ : ENNReal)^(-e) = (C : ENNReal)^p
  have h_eq : (δ₀ : ENNReal) ^ (-e) = (C : ENNReal) ^ p := by
    calc
      (δ₀ : ENNReal) ^ (-e) = ((C : ENNReal) ^ (-p / e)) ^ (-e) := by
        rw [← ENNReal.coe_rpow_of_ne_zero hC0_ne (-p / e)]
      _ = (C : ENNReal) ^ ((-p / e) * (-e)) := by rw [ENNReal.rpow_mul]
      _ = (C : ENNReal) ^ p := by
        field_simp [he_ne]
  -- Step 2: use monotonicity of x ↦ x^e for e > 0, then invert
  have h_e_nonneg : 0 ≤ e := by linarith
  have h_pow_e : (δ : ENNReal) ^ e ≤ (δ₀ : ENNReal) ^ e :=
    ENNReal.rpow_le_rpow hδle_coe h_e_nonneg
  calc
    (C : ENNReal) ^ p = (δ₀ : ENNReal) ^ (-e) := by rw [h_eq]
    _ = ((δ₀ : ENNReal) ^ e)⁻¹ := by rw [ENNReal.rpow_neg]
    _ ≤ ((δ : ENNReal) ^ e)⁻¹ := ENNReal.inv_le_inv.mpr h_pow_e
    _ = (δ : ENNReal) ^ (-e) := by rw [ENNReal.rpow_neg]

/-- **The generalized Lemma 3.7 in threshold form.**
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize` is stated with an `∀ᶠ δ in 𝓝[>] 0`; GWZ
Lemma 6.1 needs the equivalent explicit threshold `δ₀`, since its own `b₀` is built from it.

The index universe is shared: `Kakeya.KatzTaoEstimate.{u}` quantifies its tube families over
`Type u`, so the family binder below has to be `Type u` as well. Writing `Type` here instead would
pin the conclusion to `Type 0` while leaving the hypothesis at an unrelated universe, and the
resulting mismatch is not visible in the statement — it surfaces only when the two are unified. -/
theorem exists_b0_multiplicity_bound.{u} {β : ℝ} (hβ0 : 0 ≤ β)
    (hKKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) (ε : ℝ) (hε : 0 < ε) :
    ∃ ηKT : ℝ, 0 < ηKT ∧ ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧
      ∀ δ : ℝ≥0, 0 < δ → δ ≤ δ₀ → ∀ τ : ℝ≥0, 0 < τ → τ ≤ δ →
        ∀ {κ : Type u} (t : Finset κ) (T : κ → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
          (∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) →
          τ ^ ηKT ≤ ShadedBody.fullness t (fun i => (T i).toShadedBody) →
          ShadedBody.multiplicity t (fun i => (T i).toShadedBody) ≤
            (τ : ENNReal) ^ (-ε)
              * (maxDensity t (fun i => (T i).toConvexSpaceBody)) ^ (1 - β)
              * (t.card : ENNReal) ^ β := by
  obtain ⟨ηKT, hηKT, hev⟩ :=
    KatzTaoEstimate.multiplicity_bound_generalize (E := EuclideanSpace ℝ (Fin 3)) hβ0 hKKT ε hε
  obtain ⟨u, hu0, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  use ηKT, hηKT, u, hu0
  intro δ hδ0 hδu τ hτ0 hτδ κ t T hball hfull
  exact (hsub ⟨hδ0, hδu⟩) τ hτ0 hτδ t T hball hfull

/-- **The scale bookkeeping of GWZ Lemma 6.1.**  The three high-multiplicity factors — Item 4's
`a·N/(b·θ)`, the representative density transfer's `θ·b/(a·N)` (to the power `1 - β`) and the
assigned-representative cardinality's `N⁻¹` (to the power `β`) — cancel the fibre scale `N`
completely, leaving `(a/(b·θ)) ^ β`, which `Kakeya.theta_factor_le_eccentricity_factor` converts
into the eccentricity factor `(a/b) ^ (γ β)` of the conclusion. -/
theorem plankKT_final_algebra {a b θ : ℝ≥0} {β γ : ℝ} {N : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hθ0 : 0 < θ) (hθ : a / b ≤ θ) (hN : 1 ≤ N)
    (hβ : 0 < β) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) {Δ K : ENNReal} :
    (((a * (N : ℝ≥0)) / (b * θ) : ℝ≥0) : ENNReal)
        * ((((θ * b / (a * (N : ℝ≥0))) : ℝ≥0) : ENNReal) * Δ) ^ (1 - β)
        * ((N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ * K) ^ β
      ≤ Δ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * K ^ β := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hθnz : θ ≠ 0 := ne_of_gt hθ0
  have hNnz : N ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le zero_lt_one hN)
  have hβ0 : 0 ≤ β := hβ.le
  let u : ENNReal := (a : ENNReal) / ((b : ENNReal) * (θ : ENNReal))
  let n : ENNReal := (N : ENNReal)
  have hden0 : (b : ENNReal) * (θ : ENNReal) ≠ 0 :=
    mul_ne_zero (ENNReal.coe_ne_zero.mpr hb0) (ENNReal.coe_ne_zero.mpr hθnz)
  have hden_top : (b : ENNReal) * (θ : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hu0 : u ≠ 0 := by
    dsimp [u]
    exact ENNReal.div_ne_zero.mpr ⟨ENNReal.coe_ne_zero.mpr ha0, hden_top⟩
  have hutop : u ≠ ⊤ := by
    dsimp [u]
    exact ENNReal.div_ne_top (by exact ENNReal.coe_ne_top) hden0
  have hn0 : n ≠ 0 := by
    dsimp [n]
    simpa using (ENNReal.coe_ne_zero.mpr (show (N : ℝ≥0) ≠ 0 by exact_mod_cast hNnz))
  have hntop : n ≠ ⊤ := by
    dsimp [n]
    exact ENNReal.natCast_ne_top N
  have hq : (a : ENNReal) * (N : ENNReal) / ((b : ENNReal) * (θ : ENNReal)) = u * n := by
    dsimp [u, n]
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
    ac_rfl
  have hP1 : (((a * (N : ℝ≥0)) / (b * θ) : ℝ≥0) : ENNReal) = u * n := by
    have hbθnz : (b * θ : ℝ≥0) ≠ 0 := mul_ne_zero hb0 hθnz
    calc
      (((a * (N : ℝ≥0)) / (b * θ) : ℝ≥0) : ENNReal)
        = (((a * (N : ℝ≥0)) : ℝ≥0) : ENNReal) / (((b * θ : ℝ≥0) : ENNReal)) :=
          ENNReal.coe_div hbθnz
      _ = ((a : ENNReal) * ((N : ℝ≥0) : ENNReal)) / ((b : ENNReal) * (θ : ENNReal)) := by
          rw [ENNReal.coe_mul]
          rw [ENNReal.coe_mul]
      _ = (a : ENNReal) * (N : ENNReal) / ((b : ENNReal) * (θ : ENNReal)) := by
          rw [ENNReal.coe_natCast]
      _ = u * n := hq
  have hP2 : (((θ * b / (a * (N : ℝ≥0))) : ℝ≥0) : ENNReal) = (u * n)⁻¹ := by
    have hanNnz : (a * (N : ℝ≥0) : ℝ≥0) ≠ 0 :=
      mul_ne_zero ha0 (show (N : ℝ≥0) ≠ 0 by exact_mod_cast hNnz)
    calc
      (((θ * b / (a * (N : ℝ≥0))) : ℝ≥0) : ENNReal)
        = (((θ * b : ℝ≥0)) : ENNReal) / (((a * (N : ℝ≥0)) : ℝ≥0) : ENNReal) :=
          ENNReal.coe_div hanNnz
      _ = (θ : ENNReal) * (b : ENNReal) / ((a : ENNReal) * (N : ENNReal)) := by
          rw [ENNReal.coe_mul]
          rw [ENNReal.coe_mul]
          rw [ENNReal.coe_natCast]
      _ = ((b : ENNReal) * (θ : ENNReal)) / ((a : ENNReal) * (N : ENNReal)) := by
          rw [mul_comm (θ : ENNReal) (b : ENNReal)]
      _ = ((a : ENNReal) * (N : ENNReal) / ((b : ENNReal) * (θ : ENNReal)))⁻¹ := by
          rw [← ENNReal.inv_div (Or.inl hden_top) (Or.inl hden0)]
      _ = (u * n)⁻¹ := by rw [hq]
  have hun0 : u * n ≠ 0 := mul_ne_zero hu0 hn0
  have huntop : u * n ≠ ⊤ := ENNReal.mul_ne_top hutop hntop
  have hsplit_β : ((N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ * K) ^ β =
        (N : ENNReal) ^ (-β) * (θ : ENNReal) ^ (γ * β) * K ^ β := by
    calc
      ((N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ * K) ^ β
        = ((N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ) ^ β * K ^ β :=
            ENNReal.mul_rpow_of_nonneg ((N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ) K hβ0
      _ = (N : ENNReal)⁻¹ ^ β * (θ : ENNReal) ^ (γ * β) * K ^ β := by
            rw [ENNReal.mul_rpow_of_nonneg ((N : ENNReal)⁻¹) ((θ : ENNReal) ^ γ) hβ0]
            rw [← ENNReal.rpow_mul (θ : ENNReal) γ β]
      _ = (N : ENNReal) ^ (-β) * (θ : ENNReal) ^ (γ * β) * K ^ β := by
            rw [ENNReal.inv_rpow]
            rw [← ENNReal.rpow_neg (N : ENNReal) β]
  have hsplit_δ : ((((θ * b / (a * (N : ℝ≥0))) : ℝ≥0) : ENNReal) * Δ) ^ (1 - β) =
        (((θ * b / (a * (N : ℝ≥0))) : ℝ≥0) : ENNReal) ^ (1 - β) * Δ ^ (1 - β) := by
    rw [hP2]
    by_cases hΔ0 : Δ = 0
    · rw [hΔ0]
      exact ENNReal.mul_rpow_of_ne_top (ENNReal.inv_ne_top.mpr hun0) (by simp) (1 - β)
    · exact ENNReal.mul_rpow_of_ne_zero (ENNReal.inv_ne_zero.mpr huntop) hΔ0 (1 - β)
  have hscale :
      (((a * (N : ℝ≥0)) / (b * θ) : ℝ≥0) : ENNReal)
        * (((θ * b / (a * (N : ℝ≥0))) : ℝ≥0) : ENNReal) ^ (1 - β)
        * (N : ENNReal) ^ (-β) = u ^ β := by
    calc
      (((a * (N : ℝ≥0)) / (b * θ) : ℝ≥0) : ENNReal)
        * (((θ * b / (a * (N : ℝ≥0))) : ℝ≥0) : ENNReal) ^ (1 - β)
        * (N : ENNReal) ^ (-β)
        = (u * n) * ((u * n)⁻¹) ^ (1 - β) * n ^ (-β) := by
            rw [hP1, hP2]
      _ = u ^ β := plankKT_scale_cancel hu0 hutop hn0 hntop
  have hcore :
      (((a * (N : ℝ≥0)) / (b * θ) : ℝ≥0) : ENNReal)
        * ((((θ * b / (a * (N : ℝ≥0))) : ℝ≥0) : ENNReal) * Δ) ^ (1 - β)
        * ((N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ * K) ^ β
      = u ^ β * (θ : ENNReal) ^ (γ * β) * Δ ^ (1 - β) * K ^ β := by
    calc
      (((a * (N : ℝ≥0)) / (b * θ) : ℝ≥0) : ENNReal)
        * ((((θ * b / (a * (N : ℝ≥0))) : ℝ≥0) : ENNReal) * Δ) ^ (1 - β)
        * ((N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ * K) ^ β
        = (((a * (N : ℝ≥0)) / (b * θ) : ℝ≥0) : ENNReal)
          * ((((θ * b / (a * (N : ℝ≥0))) : ℝ≥0) : ENNReal) * Δ) ^ (1 - β)
          * ((N : ENNReal) ^ (-β) * (θ : ENNReal) ^ (γ * β) * K ^ β) := by
            rw [hsplit_β]
      _ = (((a * (N : ℝ≥0)) / (b * θ) : ℝ≥0) : ENNReal)
          * ((((θ * b / (a * (N : ℝ≥0))) : ℝ≥0) : ENNReal) ^ (1 - β) * Δ ^ (1 - β))
          * ((N : ENNReal) ^ (-β) * (θ : ENNReal) ^ (γ * β) * K ^ β) := by
            rw [hsplit_δ]
      _ = (((a * (N : ℝ≥0)) / (b * θ) : ℝ≥0) : ENNReal)
          * (((θ * b / (a * (N : ℝ≥0))) : ℝ≥0) : ENNReal) ^ (1 - β)
          * (N : ENNReal) ^ (-β)
          * Δ ^ (1 - β) * (θ : ENNReal) ^ (γ * β) * K ^ β := by
            ac_rfl
      _ = u ^ β * Δ ^ (1 - β) * (θ : ENNReal) ^ (γ * β) * K ^ β := by
            rw [hscale]
      _ = u ^ β * (θ : ENNReal) ^ (γ * β) * Δ ^ (1 - β) * K ^ β := by ac_rfl
  have hfin : u ^ β * (θ : ENNReal) ^ (γ * β) * Δ ^ (1 - β) * K ^ β
        ≤ Δ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * K ^ β := by
    have htheta : ((a : ENNReal) / ((b : ENNReal) * (θ : ENNReal))) ^ β *
          (θ : ENNReal) ^ (γ * β) ≤ ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) :=
      theta_factor_le_eccentricity_factor ha hb hθ0 hθ hβ hγ0 hγ1
    have htheta' : u ^ β * (θ : ENNReal) ^ (γ * β) ≤
        ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) := by
      simpa [u] using htheta
    calc
      u ^ β * (θ : ENNReal) ^ (γ * β) * Δ ^ (1 - β) * K ^ β
        = (u ^ β * (θ : ENNReal) ^ (γ * β)) * (Δ ^ (1 - β) * K ^ β) := by ac_rfl
      _ ≤ ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * (Δ ^ (1 - β) * K ^ β) :=
          mul_le_mul' htheta' le_rfl
      _ = Δ ^ (1 - β) * ((a : ENNReal) / (b : ENNReal)) ^ (γ * β) * K ^ β := by ac_rfl
  rw [hcore]
  exact hfin

open scoped Classical in
/-- **The shading of a representative lies in a fixed dilation of its anchor plank's thickening.**
Lemma 6.13 gives `(Yθ Q).carrier = (Q.dilation Cbox).carrier`, and the representative `Q` lies in the
`cThk`-dilation of the anchor's thickening (`ThickenedRepr.repr_subset_thickened`); composing the two
dilations (`PrismNDim.dilation_carrier_subset_dilation_of_carrier_subset`) gives the fixed constant
`(2 Cbox + 1) cThk`, which is what the Katz–Tao tube family consumes. -/
theorem Plank.carrier_subset_dilated_thickened_anchor {ι : Type*} {a b : ℝ≥0} {hab : a ≤ b}
    {hb1 : b ≤ 1} {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk Cbox : ℝ≥0} (hCbox : 0 < Cbox)
    {s' : Finset ι} {V : ι → Plank a b hab hb1}
    (R : Plank.ThickenedRepr s' V θ hθ1 cThk)
    (Yθ : Plank.ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (rep : Plank.ThickenedPlank θ b hθ1 hb1 → ι)
    (hrep : ∀ Q ∈ R.indexSet, rep Q ∈ s' ∧ R.repr (rep Q) = Q)
    (hYθ : ∀ Q ∈ R.indexSet, ((Yθ Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = ((Q.toPrismNDim.dilation Cbox).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    {Q : Plank.ThickenedPlank θ b hθ1 hb1} (hQ : Q ∈ R.indexSet) :
    ((Yθ Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ ((((V (rep Q)).thickened θ hθ1).toPrismNDim.dilation
          ((2 * Cbox + 1) * cThk)).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  obtain ⟨hrepmem, hreprep⟩ := hrep Q hQ
  have hsub : ((Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) ⊆
      ((((V (rep Q)).thickened θ hθ1).toPrismNDim.dilation cThk).carrier) := by
    have := R.repr_subset_thickened (rep Q) hrepmem
    rwa [hreprep] at this
  have hdil := PrismNDim.dilation_carrier_subset_dilation_of_carrier_subset
    (P := ((V (rep Q)).thickened θ hθ1).toPrismNDim)
    (Q := Q.toPrismNDim) (c := cThk) (C := Cbox) hCbox hsub
  rw [hYθ Q hQ]
  exact hdil

/-- **Re-carrying a shading costs only the carrier-volume ratio in fullness.**  If `Y'` has the same
shades as `Y` on `A` but carriers larger by at most the factor `C`, then `λ'(A, Y) ≤ C · λ'(A, Y')`:
the numerators agree and the denominator grows by at most `C`.

This is what lets GWZ Lemma 6.1 replace the shading of 6.13 (carried by `Q.dilation Cbox`) by the
one the Katz–Tao tube layer needs (carried by the *anchor* plank's dilated thickening, see
`Kakeya.exists_anchorShading`) at the price of a fixed constant. The degenerate case is fine: if the
carriers have total volume zero then so do the shades, and both sides are `0`. -/
private theorem fullness'_le_of_volume_carrier_le {ι : Type*} (A : Finset ι)
    (Y Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) {C : ENNReal}
    (hshade : ∀ Q ∈ A, (Y' Q).shade = (Y Q).shade)
    (hvol : ∀ Q ∈ A, volume (Y' Q).carrier ≤ C * volume (Y Q).carrier) :
    ShadedBody.fullness' A Y ≤ C * ShadedBody.fullness' A Y' := by
  let S := ∑ Q ∈ A, volume (Y Q).shade
  let D := ∑ Q ∈ A, volume (Y Q).carrier
  let D' := ∑ Q ∈ A, volume (Y' Q).carrier
  have hSum_congr : (∑ Q ∈ A, volume (Y Q).shade) = ∑ Q ∈ A, volume (Y' Q).shade :=
    Finset.sum_congr rfl (fun Q hQ => by rw [hshade Q hQ])
  have hvolSum : D' ≤ C * D := by
    dsimp [D', D]
    calc
      (∑ Q ∈ A, volume (Y' Q).carrier) ≤ ∑ Q ∈ A, C * volume (Y Q).carrier :=
        Finset.sum_le_sum hvol
      _ = C * ∑ Q ∈ A, volume (Y Q).carrier := by rw [Finset.mul_sum]
  have hDneTop : D ≠ ⊤ := by
    simpa [D] using (ENNReal.sum_ne_top).2 (fun Q _ => (Y Q).isCompact'.measure_ne_top)
  have hD'neTop : D' ≠ ⊤ := by
    simpa [D'] using (ENNReal.sum_ne_top).2 (fun Q _ => (Y' Q).isCompact'.measure_ne_top)
  change (∑ Q ∈ A, volume (Y Q).shade) / (∑ Q ∈ A, volume (Y Q).carrier) ≤
    C * ((∑ Q ∈ A, volume (Y' Q).shade) / (∑ Q ∈ A, volume (Y' Q).carrier))
  rw [hSum_congr.symm]
  change S / D ≤ C * (S / D')
  by_cases hS : S = 0
  · simp [hS, ENNReal.zero_div]
  · by_cases hD' : D' = 0
    · have hcar0 : ∀ Q ∈ A, volume (Y' Q).carrier = 0 :=
        (Finset.sum_eq_zero_iff.mp (by simpa [D'] using hD'))
      have hshade0 : ∀ Q ∈ A, volume (Y' Q).shade = 0 := fun Q hQ =>
        measure_mono_null (Y' Q).shade_subset (hcar0 Q hQ)
      have hS0 : S = 0 := by
        dsimp [S]
        calc
          (∑ Q ∈ A, volume (Y Q).shade) = ∑ Q ∈ A, volume (Y' Q).shade :=
            Finset.sum_congr rfl (fun Q hQ => by rw [hshade Q hQ])
          _ = 0 := Finset.sum_eq_zero hshade0
      simp [hS0, ENNReal.zero_div]
    · have hDne0 : D ≠ 0 := by
        intro hDzero
        exact hD' (le_antisymm (by simpa [hDzero] using hvolSum) zero_le)
      have hSD'mul : S * D' ≤ C * S * D := by
        calc
          S * D' ≤ S * (C * D) := mul_le_mul_right hvolSum S
          _ = C * S * D := by ac_rfl
      have hSle : S ≤ C * (S / D') * D := by
        calc
          S ≤ (C * S * D) / D' :=
            (ENNReal.le_div_iff_mul_le (Or.inl hD') (Or.inl hD'neTop)).2 hSD'mul
          _ = C * (S / D') * D := by
            rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
            ac_rfl
      exact (ENNReal.div_le_iff_le_mul (Or.inl hDne0) (Or.inl hDneTop)).2 hSle

/-- **The assigned-representative count in the shape `Kakeya.plankKT_final_algebra` consumes.**

`Plank.card_assignedRepr_mul_le_of_wideSlabNonconcentration` delivers the wide-slab bound in the
multiplicative real form `(N / cN) · |A| ≤ C · θ ^ γ · K₀`, which is where the `1 / N` of GWZ (42)
is paid back. This converts it, without ever dividing, into the `ENNReal` factorisation
`|A| ≤ N⁻¹ · θ ^ γ · (cN · C · K₀)`, which is the `N⁻¹ · θ^γ · K` of
`Kakeya.plankKT_final_algebra`.

The absolute constants `cN` and `C` are separated from the dynamic part `K₀` (which carries
`a ^ (-η) · |s|`), so that the final absorption sees them as fixed. -/
theorem plankKT_card_enn_of_mul_le {N Acard : ℕ} {cN C K₀ θ : ℝ≥0} {γ : ℝ}
    (hcN : 0 < cN) (hN : 1 ≤ N) (hθ : 0 < θ)
    (h : ((N : ℝ) / (cN : ℝ)) * (Acard : ℝ) ≤ ((C * θ ^ γ * K₀ : ℝ≥0) : ℝ)) :
    (Acard : ENNReal) ≤ (N : ENNReal)⁻¹ * (θ : ENNReal) ^ γ * ((cN * C * K₀ : ℝ≥0) : ENNReal) := by
  have hcNreal : (0 : ℝ) < (cN : ℝ) := by exact_mod_cast hcN
  have hdiv : (N : ℝ) * (Acard : ℝ) / (cN : ℝ) ≤ ((C * θ ^ γ * K₀ : ℝ≥0) : ℝ) := by
    rwa [div_mul_eq_mul_div] at h
  have hreal : (N : ℝ) * (Acard : ℝ) ≤ (cN : ℝ) * ((C * θ ^ γ * K₀ : ℝ≥0) : ℝ) := by
    rw [mul_comm (cN : ℝ)]
    exact (div_le_iff₀ hcNreal).mp hdiv
  have hnn : (N : ℝ≥0) * (Acard : ℝ≥0) ≤ cN * (C * θ ^ γ * K₀) := by
    exact_mod_cast hreal
  have hnn' : (N : ℝ≥0) * (Acard : ℝ≥0) ≤ θ ^ γ * (cN * C * K₀) := by
    calc
      (N : ℝ≥0) * (Acard : ℝ≥0) ≤ cN * (C * θ ^ γ * K₀) := hnn
      _ = θ ^ γ * (cN * C * K₀) := by ring
  have hen : (N : ENNReal) * (Acard : ENNReal) ≤
      (θ : ENNReal) ^ γ * ((cN * C * K₀ : ℝ≥0) : ENNReal) := by
    rw [← ENNReal.coe_natCast, ← ENNReal.coe_natCast, ← ENNReal.coe_mul,
      ← ENNReal.coe_rpow_of_ne_zero hθ.ne' γ, ← ENNReal.coe_mul]
    exact ENNReal.coe_le_coe.mpr hnn'
  have hN0 : (N : ENNReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hN))
  have hNtop : (N : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top N
  rw [mul_assoc]
  exact (ENNReal.mul_le_iff_le_inv hN0 hNtop).mp hen

/-- **Re-carrying the thickened shading on the anchor plank's dilated thickening.**

GWZ 6.13 hands back a shading whose carrier is `Q.dilation Cbox`, and
`Plank.carrier_subset_dilated_thickened_anchor` places that inside the `Cdil`-dilation of the
*anchor* plank's thickening — but only as an inclusion. The Katz–Tao tube layer
(`Plank.fullness'_le_ktTubeFamily`, `Plank.maxDensity_ktTubeFamily_le`) needs the carrier to be that
dilation *exactly*. Intersecting the shade with the larger body supplies a shading that has the
required carrier identity and, on `A`, the very same shade — so multiplicity is untouched and the
fullness and max-density comparisons only cost the fixed ratio of the two carrier volumes. -/
theorem exists_anchorShading {ι : Type*} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (W : Plank.ThickenedPlank θ b hθ1 hb1 → Plank a b hab hb1)
    (Yθ : Plank.ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (Cdil : ℝ≥0) (A : Finset (Plank.ThickenedPlank θ b hθ1 hb1))
    (hsub : ∀ Q ∈ A, ((Yθ Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (((W Q).thickened θ hθ1).toPrismNDim.dilation Cdil).carrier) :
    ∃ Y' : Plank.ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)),
      (∀ Q, ((Y' Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          = (((W Q).thickened θ hθ1).toPrismNDim.dilation Cdil).carrier) ∧
      (∀ Q ∈ A, (Y' Q).shade = (Yθ Q).shade) := by
  let _ := ι
  refine ⟨fun Q =>
    ({ toConvexSpaceBody := (((W Q).thickened θ hθ1).toPrismNDim.dilation Cdil).toConvexSpaceBody,
       shade := (Yθ Q).shade ∩ ((((W Q).thickened θ hθ1).toPrismNDim.dilation Cdil).carrier :
         Set (EuclideanSpace ℝ (Fin 3))),
       measurableSet_shade := (Yθ Q).measurableSet_shade.inter
         (PrismNDim.measurableSet_carrier (((W Q).thickened θ hθ1).toPrismNDim.dilation Cdil)),
       shade_subset := Set.inter_subset_right } : ShadedBody (EuclideanSpace ℝ (Fin 3))), ?_, ?_⟩
  · intro Q
    rfl
  · intro Q hQ
    change (Yθ Q).shade ∩ ((((W Q).thickened θ hθ1).toPrismNDim.dilation Cdil).carrier :
        Set (EuclideanSpace ℝ (Fin 3))) = (Yθ Q).shade
    exact Set.inter_eq_self_of_subset_left (((Yθ Q).shade_subset).trans (hsub Q hQ))

/-- **Second link of the max-density chain: re-carried anchor shadings versus representatives.**

The shading produced by `Kakeya.exists_anchorShading` is carried by the `Cdil`-dilation of the
anchor plank's thickening, which contains the representative `Q` and has exactly `Cdil³` times its
volume (`Plank.anchorDilation_facts`). So `Kakeya.maxDensity_le_of_subset_of_volume_le` applies with
the constant `Cdil³`, and no affine transport is involved. -/
private theorem maxDensity_anchorShading_le {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk Cdil : ℝ≥0} (hcd : cThk ≤ Cdil)
    (A : Finset (Plank.ThickenedPlank θ b hθ1 hb1))
    (W : Plank.ThickenedPlank θ b hθ1 hb1 → Plank a b hab hb1)
    (Yanc : Plank.ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hcarEq : ∀ Q ∈ A, ((Yanc Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (((W Q).thickened θ hθ1).toPrismNDim.dilation Cdil).carrier)
    (hQthick : ∀ Q ∈ A, (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (((W Q).thickened θ hθ1).toPrismNDim.dilation cThk).carrier) :
    Kakeya.maxDensity A (fun Q => (Yanc Q).toConvexSpaceBody)
      ≤ (Cdil : ENNReal) ^ 3 * Kakeya.maxDensity A (fun Q => Q.toConvexSpaceBody) := by
  refine Kakeya.maxDensity_le_of_subset_of_volume_le A
    (fun Q => Q.toConvexSpaceBody) (fun Q => (Yanc Q).toConvexSpaceBody)
    (C := (Cdil : ENNReal) ^ 3) ?_ ?_
  · intro Q hQ
    rw [hcarEq Q hQ]
    exact (Plank.anchorDilation_facts hcd (W Q) Q (hQthick Q hQ)).1
  · intro Q hQ
    rw [hcarEq Q hQ]
    exact le_of_eq (Plank.anchorDilation_facts hcd (W Q) Q (hQthick Q hQ)).2

/-- **The max-density chain of GWZ (42): the Katz–Tao tubes inherit the factor `θb/(aN)`.**

This is where the fibre scale `N` enters the density side, and the surviving `N⁻¹` is exactly what
cancels the `aN/(bθ)` of Lemma 6.13 Item 4 inside `Kakeya.plankKT_final_algebra`. Four links:

* `Plank.maxDensity_ktTubeFamily_le` replaces the tubes by the normalised shading bodies, at the
  absolute cost `40 (1 + Cang)³ (1 + Cset)³`;
* `Kakeya.maxDensity_mapAffine` deletes the normalising map outright — maximal density is an affine
  invariant, so nothing downstream needs transport;
* `Kakeya.maxDensity_anchorShading_le` replaces the re-carried shadings by the representatives, at
  the exact cost `Cdil³`;
* `Plank.ThickenedRepr.maxDensity_repr_le` (the un-mapped form), with the fibre lower bound,
  converts the representatives into the original planks at the cost
  `enlargementConst cThk · cN · θb/(aN)`.

Every factor except `θb/(aN)` is absolute: independent of `a`, `b`, `θ`, `N`, `s'` and `V`. -/
theorem plankKT_maxDensity_tube_le {ι : Type*} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} {s' : Finset ι} {V : ι → Plank a b hab hb1}
    {cThk Cset Cang Cdil : ℝ≥0} (hθ0 : 0 < θ) (ha : 0 < a) (hCdil : 1 ≤ Cdil)
    (hcd : cThk ≤ Cdil)
    (R : Plank.ThickenedRepr s' V θ hθ1 cThk)
    (W : Plank.ThickenedPlank θ b hθ1 hb1 → Plank a b hab hb1)
    (Yanc : Plank.ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (S : Slab θ hθ1) {A : Finset (Plank.ThickenedPlank θ b hθ1 hb1)}
    (hAsub : A ⊆ R.indexSet)
    (hmem : ∀ Q ∈ A, Q ∈ Plank.inSlabFamilyC Cset Cang A W S)
    (hcarEq : ∀ Q ∈ A, ((Yanc Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (((W Q).thickened θ hθ1).toPrismNDim.dilation Cdil).carrier)
    (hQthick : ∀ Q ∈ A, (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (((W Q).thickened θ hθ1).toPrismNDim.dilation cThk).carrier)
    {N : ℕ} {cN : ℝ≥0} (hcN : 0 < cN) (hN : 0 < N)
    (hfib : ∀ Q ∈ A, (N : ℝ) / (cN : ℝ) ≤ ((s'.filter fun i => R.repr i = Q).card : ℝ)) :
    Kakeya.maxDensity A (fun Q => (Plank.slabTubeFamily A W Yanc S
        (Plank.slabTubeConst (Plank.dilatedSetConst Cset Cdil) Cang) hθ0
        (Plank.slabTubeConst_pos _ _) Q).toConvexSpaceBody)
      ≤ (40 * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset : ENNReal)) ^ 3) * (Cdil : ENNReal) ^ 3
          * ((Plank.enlargementConst cThk * cN : ℝ≥0) : ENNReal)
          * ((θ * b / (a * (N : ℝ≥0)) : ℝ≥0) : ENNReal)
          * Kakeya.maxDensity s' (fun i => (V i).toConvexSpaceBody) := by
  let c₁ : ENNReal := 40 * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset : ENNReal)) ^ 3
  let EnC : ENNReal := ((Plank.enlargementConst cThk * cN : ℝ≥0) : ENNReal)
  let θb : ENNReal := ((θ * b / (a * (N : ℝ≥0)) : ℝ≥0) : ENNReal)
  calc
    Kakeya.maxDensity A (fun Q => (Plank.slabTubeFamily A W Yanc S
          (Plank.slabTubeConst (Plank.dilatedSetConst Cset Cdil) Cang) hθ0
          (Plank.slabTubeConst_pos _ _) Q).toConvexSpaceBody)
        ≤ c₁ * Kakeya.maxDensity A (fun Q => ((Yanc Q).toConvexSpaceBody).mapAffine
            (Slab.normalizeScaled S (Plank.slabTubeConst (Plank.dilatedSetConst Cset Cdil) Cang) hθ0
              (Plank.slabTubeConst_pos _ _))) := by
          simpa [c₁] using
            (Plank.maxDensity_ktTubeFamily_le (s := A) (V := W) (Y := Yanc) hθ0 hCdil hmem hcarEq)
    _ = c₁ * Kakeya.maxDensity A (fun Q => (Yanc Q).toConvexSpaceBody) := by
          rw [Kakeya.maxDensity_mapAffine A (fun Q => (Yanc Q).toConvexSpaceBody)
            (Slab.normalizeScaled S (Plank.slabTubeConst (Plank.dilatedSetConst Cset Cdil) Cang) hθ0
              (Plank.slabTubeConst_pos _ _))]
    _ ≤ c₁ * ((Cdil : ENNReal) ^ 3 * Kakeya.maxDensity A (fun Q => Q.toConvexSpaceBody)) :=
          mul_le_mul_right (Kakeya.maxDensity_anchorShading_le hcd A W Yanc hcarEq hQthick) c₁
    _ = c₁ * (Cdil : ENNReal) ^ 3 * Kakeya.maxDensity A (fun Q => Q.toConvexSpaceBody) := by
          ring
    _ ≤ (c₁ * (Cdil : ENNReal) ^ 3) *
            (EnC * θb * Kakeya.maxDensity s' (fun i => (V i).toConvexSpaceBody)) :=
          mul_le_mul_right (Plank.ThickenedRepr.maxDensity_repr_le R hAsub hcN ha hN hfib)
            (c₁ * (Cdil : ENNReal) ^ 3)
    _ ≤ c₁ * (Cdil : ENNReal) ^ 3 * EnC * θb *
            Kakeya.maxDensity s' (fun i => (V i).toConvexSpaceBody) := by
          exact le_of_eq (by ring)

/-- **The fullness side of GWZ Lemma 6.1, as a pure fixed-constant comparison.**

No exponent hierarchy appears here: this only says that passing from the shading `Yθ` delivered by
Lemma 6.13 to the Katz–Tao tubes costs the absolute factor
`CFull = Cdil³ · 40 (1 + Cang)³ (1 + Cset)³`. The caller combines it with Item 2 of 6.13
(`c2 · a^(4η) · a^εred ≤ λ(A, Yθ)`) and only then compares exponents.

Two links:

* `Kakeya.fullness'_le_of_volume_carrier_le` moves `Yθ` to the re-carried anchor shading `Yanc`.
  Their shades agree on `A`, and the carrier volumes are `Cdil³ · |Q|` and `Cbox³ · |Q|`
  respectively (`Plank.anchorDilation_facts` and `PrismNDim.volume_dilation`), so with `1 ≤ Cbox`
  the ratio is at most `Cdil³` — no division is needed;
* `Plank.fullness'_le_ktTubeFamily` moves `Yanc` to the tubes at the cost
  `40 (1 + Cang)³ (1 + Cset)³`.

`CFull` is independent of `a`, `b`, `θ`, `N`, `s` and `V`. -/
theorem plankKT_fullness_tube_le {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} {cThk Cset Cang Cbox Cdil : ℝ≥0}
    (hθ0 : 0 < θ) (hb0 : 0 < b) (hCdil : 1 ≤ Cdil) (hCbox : 1 ≤ Cbox) (hcd : cThk ≤ Cdil)
    (W : Plank.ThickenedPlank θ b hθ1 hb1 → Plank a b hab hb1)
    (Yθ Yanc : Plank.ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (S : Slab θ hθ1) (A : Finset (Plank.ThickenedPlank θ b hθ1 hb1))
    (hmem : ∀ Q ∈ A, Q ∈ Plank.inSlabFamilyC Cset Cang A W S)
    (hYθcar : ∀ Q ∈ A, ((Yθ Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (Q.toPrismNDim.dilation Cbox).carrier)
    (hcarEq : ∀ Q ∈ A, ((Yanc Q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (((W Q).thickened θ hθ1).toPrismNDim.dilation Cdil).carrier)
    (hQthick : ∀ Q ∈ A, (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (((W Q).thickened θ hθ1).toPrismNDim.dilation cThk).carrier)
    (hshade : ∀ Q ∈ A, (Yanc Q).shade = (Yθ Q).shade) :
    ShadedBody.fullness' A Yθ
      ≤ ((Cdil : ENNReal) ^ 3 * (40 * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset : ENNReal)) ^ 3))
          * ShadedBody.fullness' A (fun Q => (Plank.slabTubeFamily A W Yanc S
              (Plank.slabTubeConst (Plank.dilatedSetConst Cset Cdil) Cang) hθ0
              (Plank.slabTubeConst_pos _ _) Q).toShadedBody) := by
  let κ : ENNReal := 40 * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset : ENNReal)) ^ 3
  have hvol : ∀ Q ∈ A, volume (Yanc Q).carrier ≤ (Cdil : ENNReal) ^ 3 * volume (Yθ Q).carrier := by
    intro Q hQ
    rw [hcarEq Q hQ, (Plank.anchorDilation_facts hcd (W Q) Q (hQthick Q hQ)).2]
    rw [hYθcar Q hQ, PrismNDim.volume_dilation]
    have hCbox3 : (1 : ENNReal) ≤ (Cbox : ENNReal) ^ 3 := by
      have : (1 : ENNReal) ≤ (Cbox : ENNReal) := by exact_mod_cast hCbox
      calc
        (1 : ENNReal) = (1 : ENNReal) ^ 3 := by simp
        _ ≤ (Cbox : ENNReal) ^ 3 := by
          gcongr
    have hvol' : (1 : ENNReal) * volume (Q.carrier) ≤ (Cbox : ENNReal) ^ 3 * volume (Q.carrier) := by
      gcongr
    calc
      (Cdil : ENNReal) ^ 3 * volume (Q.carrier)
          = (Cdil : ENNReal) ^ 3 * (1 * volume (Q.carrier)) := by ring
      _ ≤ (Cdil : ENNReal) ^ 3 * ((Cbox : ENNReal) ^ 3 * volume (Q.carrier)) := by
        gcongr
  calc
    ShadedBody.fullness' A Yθ
        ≤ (Cdil : ENNReal) ^ 3 * ShadedBody.fullness' A Yanc :=
      Kakeya.fullness'_le_of_volume_carrier_le A Yθ Yanc hshade hvol
    _ ≤ (Cdil : ENNReal) ^ 3 *
          (κ * ShadedBody.fullness' A (fun Q => (Plank.slabTubeFamily A W Yanc S
              (Plank.slabTubeConst (Plank.dilatedSetConst Cset Cdil) Cang) hθ0
              (Plank.slabTubeConst_pos _ _) Q).toShadedBody)) := by
      gcongr
      exact Plank.fullness'_le_ktTubeFamily hθ0 hb0 hCdil hmem hcarEq
    _ = ((Cdil : ENNReal) ^ 3 *
          (40 * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset : ENNReal)) ^ 3)) *
          ShadedBody.fullness' A (fun Q => (Plank.slabTubeFamily A W Yanc S
              (Plank.slabTubeConst (Plank.dilatedSetConst Cset Cdil) Cang) hθ0
              (Plank.slabTubeConst_pos _ _) Q).toShadedBody) := by
      simp [κ, mul_assoc]

/-- **The `(a/8) ^ ηKT` fullness threshold of generalized Lemma 3.7, as pure scalar algebra.**

`Kakeya.plankKT_fullness_tube_le` gives the geometry with a fixed constant, and Item 2 of Lemma 6.13
gives `a ^ (4η)` up to another fixed constant; this converts that into the exact hypothesis
`(a/8) ^ ηKT ≤ λ` that `Kakeya.exists_b0_multiplicity_bound` consumes at the analytic scale
`τ = a/8`.

The only thing that makes it work is the *strict* inequality `4η < ηKT`: writing `d = ηKT - 4η > 0`,
the claim reduces to `CFull · 8 ^ (-ηKT) ≤ a ^ (-d)`, and since `a ≤ b ≤ b₀ < 1` the right-hand side
blows up as `b₀` shrinks. No geometry appears here, and no geometric helper has to know about the
exponent hierarchy. -/
theorem exists_b₀_tube_fullness_threshold {η ηKT : ℝ} (hη : 0 < η) (hηKT : 0 < ηKT)
    (h4η : 4 * η < ηKT) (CFull : ℝ≥0) (hCFull : 0 < CFull) :
    ∃ b₀ : ℝ≥0, 0 < b₀ ∧ ∀ a b : ℝ≥0, 0 < a → a ≤ b → b ≤ b₀ →
      ∀ lam : ℝ≥0, a ^ (4 * η) ≤ CFull * lam → (a / 8) ^ ηKT ≤ lam := by
  have hd : 0 < ηKT - 4 * η := by exact sub_pos.mpr h4η
  -- The estimates below use only the strict gap `4*η < ηKT`; the hypothesis `0 < η` is what
  -- makes the exponent `4*η` positive (the origin of the `a^(4*η)` term in the threshold).
  have h_4η_pos : 0 < 4 * η := mul_pos (by norm_num : (0 : ℝ) < 4) hη
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := plankKT_absorb (max CFull 1) (le_max_right CFull 1)
    (p := (1 : ℝ)) (e := ηKT - 4 * η) (by norm_num) hd
  refine ⟨min (1 / 2 : ℝ≥0) δ₀, lt_min (by norm_num : (0 : ℝ≥0) < 1 / 2) hδ₀pos, ?_⟩
  intro a b ha hab hb lam hlam
  have ha_b₀ : a ≤ min (1 / 2 : ℝ≥0) δ₀ := le_trans hab hb
  have ha_le_δ₀ : a ≤ δ₀ := le_trans ha_b₀ (min_le_right (1 / 2 : ℝ≥0) δ₀)
  have ha_ne : a ≠ 0 := ne_of_gt ha
  -- absorption gives CFull ≤ a^(4η - ηKT)
  have hAbs : (max CFull 1 : ENNReal) ^ (1 : ℝ) ≤ (a : ENNReal) ^ (-(ηKT - 4 * η)) :=
    hδ₀ a ha ha_le_δ₀
  have hAbs_nn : max CFull 1 ≤ a ^ (-(ηKT - 4 * η)) := by
    rw [ENNReal.rpow_one] at hAbs
    rw [← ENNReal.coe_rpow_of_ne_zero ha_ne (-(ηKT - 4 * η))] at hAbs
    exact ENNReal.coe_le_coe.mp hAbs
  have hCFull_le : CFull ≤ a ^ (4 * η - ηKT) := by
    have h₀ : CFull ≤ a ^ (-(ηKT - 4 * η)) := le_trans (le_max_left CFull 1) hAbs_nn
    simpa [neg_sub] using h₀
  -- (a/8)^ηKT ≤ a^ηKT by base monotonicity (a/8 ≤ a, ηKT ≥ 0)
  have hdiv : a / 8 ≤ a := by
    exact_mod_cast (show (a : ℝ) / 8 ≤ (a : ℝ) by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 8)]
      calc
        (a : ℝ) = (a : ℝ) * 1 := by simp
        _ ≤ (a : ℝ) * 8 := by
          exact mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) ≤ 8) (NNReal.coe_nonneg a))
  have h_step1 : (a / 8) ^ ηKT ≤ a ^ ηKT := NNReal.rpow_le_rpow hdiv (le_of_lt hηKT)
  -- a^ηKT * CFull ≤ a^(4η), then divide by CFull
  have htmp : a ^ ηKT * CFull ≤ a ^ (4 * η) := by
    calc
      a ^ ηKT * CFull ≤ a ^ ηKT * a ^ (4 * η - ηKT) :=
        mul_le_mul_of_nonneg_left hCFull_le (bot_le : (0 : ℝ≥0) ≤ a ^ ηKT)
      _ = a ^ (ηKT + (4 * η - ηKT)) := by rw [← NNReal.rpow_add ha_ne]
      _ = a ^ (4 * η) := by rw [show ηKT + (4 * η - ηKT) = 4 * η by linarith]
  have h_step2 : a ^ ηKT ≤ a ^ (4 * η) * CFull⁻¹ := by
    calc
      a ^ ηKT = (a ^ ηKT * CFull) * CFull⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hCFull.ne', mul_one]
      _ ≤ a ^ (4 * η) * CFull⁻¹ :=
        mul_le_mul_of_nonneg_right htmp (bot_le : (0 : ℝ≥0) ≤ CFull⁻¹)
  -- divide the hypothesis by CFull
  have h_step3 : a ^ (4 * η) * CFull⁻¹ ≤ lam := by
    calc
      a ^ (4 * η) * CFull⁻¹ ≤ (CFull * lam) * CFull⁻¹ :=
        mul_le_mul_of_nonneg_right hlam (bot_le : (0 : ℝ≥0) ≤ CFull⁻¹)
      _ = lam := by rw [mul_comm CFull lam, mul_assoc, mul_inv_cancel₀ hCFull.ne', mul_one]
  calc
    (a / 8) ^ ηKT ≤ a ^ ηKT := h_step1
    _ ≤ a ^ (4 * η) * CFull⁻¹ := h_step2
    _ ≤ lam := h_step3


end Kakeya

end
