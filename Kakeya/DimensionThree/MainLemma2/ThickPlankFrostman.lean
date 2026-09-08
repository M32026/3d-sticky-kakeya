/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThickCase

/-!
# The Frostman field of the thick-case plank presentation (row G10d)

This file proves field **16** (`frostman`) of
`Kakeya.VeryNotSticky.ThickPlankPresentation` — blueprint `lem:ml2thickPlank`(iii), GWZ
`gwz.txt` l.2121 "by (82)" — from the normalisation and selection data and from nothing else.
It imports only `Kakeya.DimensionThree.MainLemma2.ThickCase`.

## The statement

`C_F(𝒫_sel) ≤ CP C_bias` **in the plank window** `Kakeya.plankWindow = B̄(0,4)`, i.e.

`∀ K' ≤ B̄(0,4), Δ(𝒫_sel, K') ≤ CP C_bias Δ(𝒫_sel, B̄(0,4))`.

## The proof, in two halves

**Half A — the numerator.** Fix `K' ≤ B̄(0,4)`. A selected plank `P_q ⊆ K'` carries its segment
image with it, `L(Y_q) ⊆ P_q ⊆ K'`, so `Y_q` lies in `K'' := L⁻¹(K') ∩ W_j`, a convex body with
`K'' ≤ W_j` — the only shape in which `Kakeya.VeryNotSticky.BallData.biasedDensity` of (C4) may
be read. Every plank has carrier volume exactly `8 a' b'` (`Prism3D.volume_carrier`), and
`8 a' b' ≤ C_e |L(Y_q)|` is `hKvol`, so

`∑_{P_q ⊆ K'} |P_q| ≤ C_e |det L| ∑_{Y_q ≤ K''} |Y_q| = C_e |det L| Δ(𝕋_{B,W}, K'') |K''|`,

`biasedDensity` bounds `Δ(𝕋_{B,W}, K'')` by `C_bias (|K''|/|W|)^ϱ Δ(𝕋_{B,W}, W)` and the ratio
is `≤ 1` because `K'' ⊆ W`; and `|det L| |K''| = |L(K'')| ≤ |K'|`. Dividing by `|K'|`
(`Kakeya.densityIn_le_iff`, so no division is ever performed) gives
`Δ(𝒫_sel, K') ≤ C_e C_bias Δ(𝕋_{B,W}, W)`. **The `ϱ`-gain is discarded here**: unlike field 18,
field 16 needs only `(|K''|/|W|)^ϱ ≤ 1`.

**Half B — the denominator.** `Δ(𝕋_{B,W}, W)` must be paid back in terms of
`Δ(𝒫_sel, B̄(0,4)) = |sel| 8a'b' / |B̄(0,4)|` (the window clause makes the filter all of `sel`).
Two-sided segment volumes (`Kakeya.VeryNotSticky.thickSegVol`), the body volume
(`Kakeya.VeryNotSticky.thickBodyVol`), the **cardinality** retention `sel_card` and the *lower*
comparabilities `δ/b ≤ a'`, `δ/a ≤ b'` give it at the `δ`-free `6 C₀⁶ C_sel |B̄(0,4)|`: the
`δ²/(ab)` of `8a'b'` cancels against the `r₁ b a` of `|W|`, leaving `r₁ δ²`, which cancels
against the segment volume. Only the *lower* halves of the capped comparabilities are used, so
the caps  cost nothing here.

**Field 16 consumes R31 twice over**: through `hKvol` and the ED planks it presupposes, and
through the cardinality retention `hcard`, which is the field `sel_card` — the same clause
`Kakeya.VeryNotSticky.denseInBodyRaw_of_thickPlankPresentation` consumes downstream. Unlike
field 15 it does **not** need the shaded-mass retention.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric ShadedBody

universe u

/-- Cross-multiplication in `[0,∞]`: from `a c ≤ b d` with `c`, `d` positive and finite,
`a / d ≤ b / c`. This is the one place field 16 turns a product bound into a bound between two
`Kakeya.densityIn`s. -/
theorem div_le_div_of_mul_le {a b c d : ENNReal} (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hd0 : d ≠ 0) (hdt : d ≠ ⊤) (h : a * c ≤ b * d) : a / d ≤ b / c := by
  have h2 : a * c * (c⁻¹ * d⁻¹) ≤ b * d * (c⁻¹ * d⁻¹) := by gcongr
  calc a / d = a * d⁻¹ := by rw [div_eq_mul_inv]
    _ = a * c * (c⁻¹ * d⁻¹) := by
        rw [show a * c * (c⁻¹ * d⁻¹) = a * d⁻¹ * (c * c⁻¹) by ring,
          ENNReal.mul_inv_cancel hc0 hct, mul_one]
    _ ≤ b * d * (c⁻¹ * d⁻¹) := h2
    _ = b * c⁻¹ := by
        rw [show b * d * (c⁻¹ * d⁻¹) = b * c⁻¹ * (d * d⁻¹) by ring,
          ENNReal.mul_inv_cancel hd0 hdt, mul_one]
    _ = b / c := by rw [div_eq_mul_inv]
/-- the scalar core of field 16's second half, in `ℝ≥0`. -/
theorem thickFrostman_arith {C₀ Csel Vwin Cw r₁ dl a b : NNReal}
    (ha : 0 < a) (hb : 0 < b) (hC₀ : 0 < C₀)
    (hCw : 6 * C₀ ^ (6 : ℕ) * Csel * Vwin ≤ Cw) :
    Csel * (8 * C₀ ^ (3 : ℕ) * r₁ * dl ^ (2 : ℕ)) * Vwin
      ≤ Cw * (8 * (dl / b) * (dl / a)) * ((6 * C₀ ^ (3 : ℕ))⁻¹ * (r₁ * b * a)) := by
  have hrhs : Cw * (8 * (dl / b) * (dl / a)) * ((6 * C₀ ^ (3 : ℕ))⁻¹ * (r₁ * b * a))
      = Cw * (8 * r₁ * dl ^ (2 : ℕ)) * (6 * C₀ ^ (3 : ℕ))⁻¹ := by
    field_simp
  rw [hrhs]
  have hC₀' : (6 : NNReal) * C₀ ^ (3 : ℕ) ≠ 0 := by positivity
  rw [show Cw * (8 * r₁ * dl ^ (2 : ℕ)) * (6 * C₀ ^ (3 : ℕ))⁻¹
        = Cw * (8 * r₁ * dl ^ (2 : ℕ)) / (6 * C₀ ^ (3 : ℕ)) from (div_eq_mul_inv _ _).symm,
    le_div_iff₀ (show (0:NNReal) < 6 * C₀ ^ (3 : ℕ) by positivity)]
  calc Csel * (8 * C₀ ^ (3 : ℕ) * r₁ * dl ^ (2 : ℕ)) * Vwin * (6 * C₀ ^ (3 : ℕ))
      = (6 * C₀ ^ (6 : ℕ) * Csel * Vwin) * (8 * r₁ * dl ^ (2 : ℕ)) := by ring
    _ ≤ Cw * (8 * r₁ * dl ^ (2 : ℕ)) := by gcongr

open scoped Classical in
/-- **Field 16 of `Kakeya.VeryNotSticky.ThickPlankPresentation`** (blueprint
`lem:ml2thickPlank`(iii)), from the normalisation and selection data.

`hPY`, `hwin` are fields 9 and 13; `hsel` is field 11; `hcard` is field 12 (`sel_card`);
`hKvol` is `Kakeya.VeryNotSticky.thickPlank_hKvol`; `hlow_a`, `hlow_b` are the lower halves of
the comparabilities (`Kakeya.VeryNotSticky.delta_div_b_le_thickPlankShort` and its companion).
`Vwin` is any `δ`-free upper bound for `|B̄(0,4)|`, e.g.
`(volume Kakeya.plankWindow.carrier).toNNReal`. The field holds at any
`CP ≥ C_e · 6 C₀⁶ C_sel Vwin`. -/
theorem thickPlank_frostman
    (cfg : VeryNotSticky.{u}) (bd : BallData cfg) {B : bd.bι} (hB : B ∈ bd.bs)
    {j : bd.ω} (hj : j ∈ bd.bodies B)
    {a' b' : NNReal} {hab' : a' ≤ b'} {hb1' : b' ≤ 1}
    (P : bd.σ → ShadedPlank a' b' hab' hb1')
    (sel : Finset bd.σ) (hsel : sel ⊆ (bd.segs B).filter fun p => bd.blk p = j)
    (L : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
    (hPY : ∀ p ∈ (bd.segs B).filter (fun q => bd.blk q = j),
      ⇑L '' ((bd.Y p).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ ((P p).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hwin : ∀ p ∈ sel, ((P p).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (Kakeya.plankWindow.carrier : Set (EuclideanSpace ℝ (Fin 3))))
    {Ce : NNReal}
    (hKvol : ∀ p ∈ (bd.segs B).filter (fun q => bd.blk q = j),
      8 * (a' : ENNReal) * (b' : ENNReal)
        ≤ (Ce : ENNReal) * volume (⇑L '' ((bd.Y p).carrier : Set (EuclideanSpace ℝ (Fin 3)))))
    {Csel : NNReal} (hCsel : 0 < Csel)
    (hcard : (Csel : ENNReal)⁻¹ *
        ((((bd.segs B).filter fun p => bd.blk p = j).card : ℕ) : ENNReal)
      ≤ ((sel.card : ℕ) : ENNReal))
    (hlow_a : cfg.δ / cfg.b ≤ a') (hlow_b : cfg.δ / cfg.a ≤ b')
    {Vwin : NNReal}
    (hVwin : volume (Kakeya.plankWindow.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ (Vwin : ENNReal))
    {CP : NNReal} (hCP : Ce * (6 * bd.C₀ ^ (6 : ℕ) * Csel * Vwin) ≤ CP) :
    ConvexSpaceBody.IsFrostmanIn sel (fun p => (P p).toConvexSpaceBody) Kakeya.plankWindow
      ((CP * bd.Cbias : NNReal) : ENNReal) := by
  classical
  set blk : Finset bd.σ := (bd.segs B).filter (fun q => bd.blk q = j) with hblk
  set Yb : bd.σ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun q => (bd.Y q).toConvexSpaceBody with hYb
  set Pb : bd.σ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun q => (P q).toConvexSpaceBody with hPb
  set J : ENNReal := ENNReal.ofReal
    |LinearMap.det ((L.linear : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) :
      EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))| with hJdef
  have hJvol : ∀ S : Set (EuclideanSpace ℝ (Fin 3)), volume (⇑L '' S) = J * volume S := by
    intro S
    simpa [hJdef] using Kakeya.volume_affineImage L S
  have hcont' : Continuous (L.symm : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) :=
    L.symm.continuous_of_finiteDimensional
  have hC₀pos : (0 : NNReal) < bd.C₀ := lt_of_lt_of_le zero_lt_one bd.hC₀
  have hapos : (0 : NNReal) < cfg.a := cfg_a_pos cfg
  have hbpos : (0 : NNReal) < cfg.b := cfg_b_pos cfg
  have hr₁pos : (0 : NNReal) < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  obtain ⟨hWlo, hWhi⟩ := thickBodyVol cfg bd hB hj
  have hW0 : volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ 0 := by
    have h1 : (0 : ENNReal) < (((6 * bd.C₀ ^ 3 : NNReal) : ENNReal))⁻¹ :=
      ENNReal.inv_pos.mpr ENNReal.coe_ne_top
    have h2 : (0 : ENNReal) < ((cfg.r₁ * cfg.b * cfg.a : NNReal) : ENNReal) := by
      have hprod : (0 : NNReal) < cfg.r₁ * cfg.b * cfg.a := by positivity
      exact_mod_cast hprod
    exact (lt_of_lt_of_le (ENNReal.mul_pos h1.ne' h2.ne') hWlo).ne'
  have hWt : volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ ⊤ :=
    (bd.Wb j).isCompact.measure_ne_top
  have hwin0 : volume (Kakeya.plankWindow.carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ 0 := by
    have := Kakeya.one_le_volume_plankWindow
    intro h
    rw [h] at this
    simp at this
  have hwint : volume (Kakeya.plankWindow.carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ ⊤ :=
    Kakeya.plankWindow.isCompact.measure_ne_top
  -- ### Step B: the block density is controlled by the plank density in the window
  have hSsel : ∑ q ∈ sel with Pb q ≤ Kakeya.plankWindow, volume (Pb q).carrier
      = ((sel.card : ℕ) : ENNReal) * (8 * (a' : ENNReal) * (b' : ENNReal)) := by
    have hfil : (sel.filter fun q => Pb q ≤ Kakeya.plankWindow) = sel := by
      refine Finset.filter_true_of_mem ?_
      intro q hq
      exact hwin q hq
    rw [hfil]
    have hvq : ∀ q : bd.σ, volume (Pb q).carrier = 8 * (a' : ENNReal) * (b' : ENNReal) := by
      intro q
      simpa using Prism3D.volume_carrier ((P q).toPrism3D)
    rw [Finset.sum_congr rfl (fun q _ => hvq q), Finset.sum_const, nsmul_eq_mul]
  have hSblk : ∑ q ∈ blk with Yb q ≤ bd.Wb j, volume (Yb q).carrier
      ≤ ((blk.card : ℕ) : ENNReal) * ((8 * bd.C₀ ^ 3 * cfg.r₁ * cfg.δ ^ 2 : NNReal) : ENNReal) := by
    calc ∑ q ∈ blk with Yb q ≤ bd.Wb j, volume (Yb q).carrier
        ≤ ∑ q ∈ blk, volume (Yb q).carrier :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ ∑ _q ∈ blk, ((8 * bd.C₀ ^ 3 * cfg.r₁ * cfg.δ ^ 2 : NNReal) : ENNReal) :=
          Finset.sum_le_sum (fun q hq =>
            (thickSegVol cfg bd hB (Finset.mem_filter.mp hq).1).2)
      _ = ((blk.card : ℕ) : ENNReal) * _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hblkcard : ((blk.card : ℕ) : ENNReal) ≤ (Csel : ENNReal) * ((sel.card : ℕ) : ENNReal) := by
    have hC0 : (Csel : ENNReal) ≠ 0 := by simpa using hCsel.ne'
    have hCt : (Csel : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    calc ((blk.card : ℕ) : ENNReal)
        = (Csel : ENNReal) * ((Csel : ENNReal)⁻¹ * ((blk.card : ℕ) : ENNReal)) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hC0 hCt, one_mul]
      _ ≤ (Csel : ENNReal) * ((sel.card : ℕ) : ENNReal) := by gcongr
  have hWlo' : (((6 * bd.C₀ ^ 3 : NNReal))⁻¹ * (cfg.r₁ * cfg.b * cfg.a) : NNReal)
      ≤ volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    refine le_trans (le_of_eq ?_) hWlo
    rw [ENNReal.coe_mul, ENNReal.coe_inv (by positivity)]
  have harith := thickFrostman_arith (C₀ := bd.C₀) (Csel := Csel) (Vwin := Vwin)
    (Cw := 6 * bd.C₀ ^ (6 : ℕ) * Csel * Vwin) (r₁ := cfg.r₁) (dl := cfg.δ)
    (a := cfg.a) (b := cfg.b) hapos hbpos hC₀pos le_rfl
  have hlow8 : ((8 * (cfg.δ / cfg.b) * (cfg.δ / cfg.a) : NNReal) : ENNReal)
      ≤ 8 * (a' : ENNReal) * (b' : ENNReal) := by
    calc ((8 * (cfg.δ / cfg.b) * (cfg.δ / cfg.a) : NNReal) : ENNReal)
        = 8 * ((cfg.δ / cfg.b : NNReal) : ENNReal) * ((cfg.δ / cfg.a : NNReal) : ENNReal) := by
          rw [ENNReal.coe_mul, ENNReal.coe_mul]; norm_num
      _ ≤ 8 * (a' : ENNReal) * (b' : ENNReal) := by
          gcongr
  have hZcoe : ((Csel * (8 * bd.C₀ ^ (3 : ℕ) * cfg.r₁ * cfg.δ ^ (2 : ℕ)) * Vwin : NNReal)
        : ENNReal)
      = (Csel : ENNReal) * ((8 * bd.C₀ ^ (3 : ℕ) * cfg.r₁ * cfg.δ ^ (2 : ℕ) : NNReal) : ENNReal)
        * (Vwin : ENNReal) := by
    rw [ENNReal.coe_mul, ENNReal.coe_mul]
  have hCXY : ((Csel * (8 * bd.C₀ ^ (3 : ℕ) * cfg.r₁ * cfg.δ ^ (2 : ℕ)) * Vwin : NNReal) : ENNReal)
      ≤ ((6 * bd.C₀ ^ (6 : ℕ) * Csel * Vwin : NNReal) : ENNReal)
        * ((8 * (cfg.δ / cfg.b) * (cfg.δ / cfg.a) : NNReal) : ENNReal)
        * (((6 * bd.C₀ ^ (3 : ℕ))⁻¹ * (cfg.r₁ * cfg.b * cfg.a) : NNReal) : ENNReal) := by
    rw [← ENNReal.coe_mul, ← ENNReal.coe_mul]
    exact_mod_cast harith
  have hmul : (∑ q ∈ blk with Yb q ≤ bd.Wb j, volume (Yb q).carrier)
        * volume (Kakeya.plankWindow.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ (((6 * bd.C₀ ^ (6 : ℕ) * Csel * Vwin : NNReal) : ENNReal)
          * ∑ q ∈ sel with Pb q ≤ Kakeya.plankWindow, volume (Pb q).carrier)
        * volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    calc (∑ q ∈ blk with Yb q ≤ bd.Wb j, volume (Yb q).carrier)
          * volume (Kakeya.plankWindow.carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ≤ ((Csel : ENNReal) * ((sel.card : ℕ) : ENNReal))
            * ((8 * bd.C₀ ^ (3 : ℕ) * cfg.r₁ * cfg.δ ^ (2 : ℕ) : NNReal) : ENNReal)
            * (Vwin : ENNReal) := by
          gcongr
          exact hSblk.trans (by gcongr)
      _ = ((sel.card : ℕ) : ENNReal)
            * ((Csel * (8 * bd.C₀ ^ (3 : ℕ) * cfg.r₁ * cfg.δ ^ (2 : ℕ)) * Vwin : NNReal)
              : ENNReal) := by
          rw [hZcoe]; ring
      _ ≤ ((sel.card : ℕ) : ENNReal)
            * (((6 * bd.C₀ ^ (6 : ℕ) * Csel * Vwin : NNReal) : ENNReal)
              * ((8 * (cfg.δ / cfg.b) * (cfg.δ / cfg.a) : NNReal) : ENNReal)
              * (((6 * bd.C₀ ^ (3 : ℕ))⁻¹ * (cfg.r₁ * cfg.b * cfg.a) : NNReal) : ENNReal)) := by
          gcongr
      _ = ((6 * bd.C₀ ^ (6 : ℕ) * Csel * Vwin : NNReal) : ENNReal)
            * (((sel.card : ℕ) : ENNReal)
              * ((8 * (cfg.δ / cfg.b) * (cfg.δ / cfg.a) : NNReal) : ENNReal))
            * (((6 * bd.C₀ ^ (3 : ℕ))⁻¹ * (cfg.r₁ * cfg.b * cfg.a) : NNReal) : ENNReal) := by
          ring
      _ ≤ ((6 * bd.C₀ ^ (6 : ℕ) * Csel * Vwin : NNReal) : ENNReal)
            * (((sel.card : ℕ) : ENNReal) * (8 * (a' : ENNReal) * (b' : ENNReal)))
            * volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
          gcongr
      _ = _ := by rw [hSsel]
  have hstepB : Kakeya.densityIn blk Yb (bd.Wb j)
      ≤ ((6 * bd.C₀ ^ (6 : ℕ) * Csel * Vwin : NNReal) : ENNReal)
        * Kakeya.densityIn sel Pb Kakeya.plankWindow := by
    have := div_le_div_of_mul_le (a := ∑ q ∈ blk with Yb q ≤ bd.Wb j, volume (Yb q).carrier)
      (b := ((6 * bd.C₀ ^ (6 : ℕ) * Csel * Vwin : NNReal) : ENNReal)
        * ∑ q ∈ sel with Pb q ≤ Kakeya.plankWindow, volume (Pb q).carrier)
      (c := volume (Kakeya.plankWindow.carrier : Set (EuclideanSpace ℝ (Fin 3))))
      (d := volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3))))
      hwin0 hwint hW0 hWt hmul
    simpa [Kakeya.densityIn, mul_div_assoc] using this
  -- ### Step A: the Frostman inequality itself
  intro K' hK'
  have hA : Kakeya.densityIn sel Pb K'
      ≤ (Ce : ENNReal) * (bd.Cbias : ENNReal) * Kakeya.densityIn blk Yb (bd.Wb j) := by
    rw [Kakeya.densityIn_le_iff]
    rcases Finset.eq_empty_or_nonempty (sel.filter fun q => Pb q ≤ K') with hE | ⟨q₀, hq₀⟩
    · rw [show (∑ q ∈ sel with Pb q ≤ K', volume (Pb q).carrier)
            = ∑ q ∈ (sel.filter fun q => Pb q ≤ K'), volume (Pb q).carrier from rfl, hE]
      simp
    · set Kpre : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
        K'.affineImage L.symm.toAffineMap hcont' with hKpre
      have hKpre_carrier : (Kpre.carrier : Set (EuclideanSpace ℝ (Fin 3)))
          = ⇑L.symm '' (K'.carrier : Set (EuclideanSpace ℝ (Fin 3))) := rfl
      have hmemF : ∀ q ∈ sel.filter (fun q => Pb q ≤ K'),
          ((bd.Y q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            ⊆ Kpre.carrier ∩ (bd.Wb j).carrier := by
        intro q hq x hx
        rw [Finset.mem_filter] at hq
        have hqblk := Finset.mem_filter.mp (hsel hq.1)
        constructor
        · rw [hKpre_carrier]
          refine ⟨L x, ?_, by simp⟩
          exact hq.2 (hPY q (hsel hq.1) ⟨x, hx, rfl⟩)
        · have h2 := bd.segs_le B hB q hqblk.1
          rw [hqblk.2] at h2
          exact h2 hx
      have hne : ((Kpre.carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ∩ ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3)))).Nonempty := by
        obtain ⟨x, hx⟩ := (bd.Y q₀).nonempty
        exact ⟨x, hmemF q₀ hq₀ hx⟩
      set K'' : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
        Kpre.inter (bd.Wb j) hne with hK''
      have hK''W : K'' ≤ bd.Wb j := fun x hx => hx.2
      have hsub : (sel.filter fun q => Pb q ≤ K') ⊆ Kakeya.familyIn blk Yb K'' := by
        intro q hq
        refine Finset.mem_filter.mpr ⟨hsel (Finset.mem_filter.mp hq).1, ?_⟩
        intro x hx
        exact hmemF q hq hx
      have hLK'' : ⇑L '' (K''.carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ (K'.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
        rintro _ ⟨x, hx, rfl⟩
        have hx1 : x ∈ (Kpre.carrier : Set (EuclideanSpace ℝ (Fin 3))) := hx.1
        rw [hKpre_carrier] at hx1
        obtain ⟨y, hy, rfl⟩ := hx1
        simpa using hy
      have hJK'' : J * volume (K''.carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ≤ volume (K'.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
        rw [← hJvol]
        exact measure_mono hLK''
      have hdens : Kakeya.densityIn blk Yb K''
          ≤ (bd.Cbias : ENNReal) * Kakeya.densityIn blk Yb (bd.Wb j) := by
        have hbd := bd.biasedDensity B hB j hj K'' hK''W
        rw [← hYb, ← hblk] at hbd
        refine hbd.trans ?_
        have h1 : (volume (K''.carrier : Set (EuclideanSpace ℝ (Fin 3)))
            / volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ^ cfg.ϱ ≤ 1 := by
          refine ENNReal.rpow_le_one ?_ cfg.hϱ.le
          refine ENNReal.div_le_of_le_mul ?_
          rw [one_mul]
          exact measure_mono hK''W
        calc (bd.Cbias : ENNReal) * (volume (K''.carrier : Set (EuclideanSpace ℝ (Fin 3)))
              / volume ((bd.Wb j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ^ cfg.ϱ
              * Kakeya.densityIn blk Yb (bd.Wb j)
            ≤ (bd.Cbias : ENNReal) * 1 * Kakeya.densityIn blk Yb (bd.Wb j) := by gcongr
          _ = (bd.Cbias : ENNReal) * Kakeya.densityIn blk Yb (bd.Wb j) := by ring
      have hstep : ∀ q ∈ sel.filter (fun q => Pb q ≤ K'),
          volume (Pb q).carrier ≤ (Ce : ENNReal) * (J * volume (bd.Y q).carrier) := by
        intro q hq
        have hv : volume ((Pb q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            = 8 * (a' : ENNReal) * (b' : ENNReal) := by
          simpa using Prism3D.volume_carrier ((P q).toPrism3D)
        rw [hv, ← hJvol]
        exact hKvol q (hsel (Finset.mem_filter.mp hq).1)
      calc ∑ q ∈ sel with Pb q ≤ K', volume (Pb q).carrier
          ≤ ∑ q ∈ sel with Pb q ≤ K', (Ce : ENNReal) * (J * volume (bd.Y q).carrier) :=
            Finset.sum_le_sum hstep
        _ = (Ce : ENNReal) * (J * ∑ q ∈ sel with Pb q ≤ K', volume (Yb q).carrier) := by
            rw [Finset.mul_sum, Finset.mul_sum]
        _ ≤ (Ce : ENNReal) * (J * ∑ q ∈ Kakeya.familyIn blk Yb K'', volume (Yb q).carrier) := by
            gcongr
        _ = (Ce : ENNReal) * (J * (Kakeya.densityIn blk Yb K''
              * volume (K''.carrier : Set (EuclideanSpace ℝ (Fin 3))))) := by
            rw [show (∑ q ∈ Kakeya.familyIn blk Yb K'', volume (Yb q).carrier)
                = ∑ q ∈ blk with Yb q ≤ K'', volume (Yb q).carrier from rfl,
              Kakeya.sum_volume_eq_densityIn_mul_volume]
        _ = (Ce : ENNReal) * Kakeya.densityIn blk Yb K''
              * (J * volume (K''.carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by ring
        _ ≤ (Ce : ENNReal) * ((bd.Cbias : ENNReal) * Kakeya.densityIn blk Yb (bd.Wb j))
              * volume (K'.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by gcongr
        _ = (Ce : ENNReal) * (bd.Cbias : ENNReal) * Kakeya.densityIn blk Yb (bd.Wb j)
              * volume (K'.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by ring
  calc Kakeya.densityIn sel Pb K'
      ≤ (Ce : ENNReal) * (bd.Cbias : ENNReal) * Kakeya.densityIn blk Yb (bd.Wb j) := hA
    _ ≤ (Ce : ENNReal) * (bd.Cbias : ENNReal) *
          (((6 * bd.C₀ ^ (6 : ℕ) * Csel * Vwin : NNReal) : ENNReal)
            * Kakeya.densityIn sel Pb Kakeya.plankWindow) := by gcongr
    _ = (((Ce * (6 * bd.C₀ ^ (6 : ℕ) * Csel * Vwin)) * bd.Cbias : NNReal) : ENNReal)
          * Kakeya.densityIn sel Pb Kakeya.plankWindow := by
        push_cast
        ring
    _ ≤ ((CP * bd.Cbias : NNReal) : ENNReal) * Kakeya.densityIn sel Pb Kakeya.plankWindow := by
        have hle : (Ce * (6 * bd.C₀ ^ (6 : ℕ) * Csel * Vwin)) * bd.Cbias ≤ CP * bd.Cbias := by
          gcongr
        gcongr

/-- **Fidelity tripwire for field 16.** The conclusion of
`Kakeya.VeryNotSticky.thickPlank_frostman` is, verbatim, the field `frostman` of
`Kakeya.VeryNotSticky.ThickPlankPresentation` — in the plank window and at `CP * bd.Cbias`,
with the bias constant explicit and not absorbed. If the field's text drifts this stops
compiling. -/
example {cfg : VeryNotSticky.{u}} {bd : BallData cfg} {B : bd.bι} {j : bd.ω}
    {CP Θ C_NC : NNReal} (h : ThickPlankPresentation bd B j CP Θ C_NC) :
    ConvexSpaceBody.IsFrostmanIn h.sel
      (fun p => (h.P p).toConvexSpaceBody) Kakeya.plankWindow
      ((CP * bd.Cbias : NNReal) : ENNReal) :=
  h.frostman

end Kakeya.VeryNotSticky
