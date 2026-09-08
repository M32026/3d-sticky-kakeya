/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThickPlankNormalise
public import Kakeya.DimensionThree.MainLemma2.ThickPlankSelect
public import Kakeya.DimensionThree.MainLemma2.LineEssDistinct
public import Kakeya.DimensionThree.MainLemma2.ThickPlankNonconc
public import Kakeya.DimensionThree.MainLemma2.ThickPlankFullness
public import Kakeya.DimensionThree.MainLemma2.ThickPlankFrostman

/-!
# Constructing `ThickPlankPresentable`

This file defines the two comparison constants, proves their lower
bounds by `1`, and assembles all eighteen fields of
`Kakeya.VeryNotSticky.ThickPlankPresentation`.

| Fields | Estimates used |
|---|---|
| 1-9, 13 | `exists_thickPlankNormalisation` and the four comparabilities |
| 10-12, 14 | `plankSubfamilySelection_card`, `edImages_of_edSegments` |
| 15 | `thickPlank_fullness_ge` |
| 16 | `thickPlank_frostman` |
| 17 | `thickPlank_volume_le` |
| 18 | `thickPlank_nonconcentration` |

The geometric input `hEDdeg` bounds the non-ED degree of the segments
in each ball by `edMultiplicityConstant`. A line-based bound on the
canonical capsule family supplies this degree condition; pairwise
essential distinctness of the entire family is not required.

## Choice of constants

`thickPlank_hKvol` requires `6144 C₀^8 ≤ C_e * c_W`, where
`c_W = thickPlankBodyFloor C₀ = κ³ / (6 C₀^5)`. Using
`C_e = plankEnclosureConstant C₀ = max 1 (2^20 C₀^6)` would require
`κ³ ≥ (6144 * 6 / 2^20) C₀^7`, which fails for large `C₀`.
The selection therefore uses `thickPlankEnclC₀ C₀`, chosen so that
its enclosure constant meets the required bound. The comparison
parameter of `plankSubfamilySelection_card` is independent of `bd.C₀`.

The Frostman field also costs `C_e * 6 C₀^6 * C_sel * V_win`,
where `V_win` is the volume of `Kakeya.plankWindow`; this window
factor is included in `thickPlankCP`. Finally, `thickPlankΘ` is
`thickNonconcΘ` evaluated at this `CP` and the body-volume floor,
so the nonconcentration field follows directly.
-/

@[expose] public section

open Finset MeasureTheory Metric Set ShadedBody
open scoped ENNReal NNReal

noncomputable section

namespace Kakeya.VeryNotSticky

open Kakeya

/-- Shorthand for the ambient space of the thick case. -/
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

universe u

/-! ### The constants -/

/-- The volume of the Section 6 window `B̄(0, 4)`, capped below at `1`. -/
def thickPlankWindowVol : NNReal :=
  max 1 (volume (Kakeya.plankWindow.carrier : Set E₃)).toNNReal

theorem one_le_thickPlankWindowVol : 1 ≤ thickPlankWindowVol := le_max_left _ _

theorem volume_plankWindow_le_thickPlankWindowVol :
    volume (Kakeya.plankWindow.carrier : Set E₃) ≤ (thickPlankWindowVol : ENNReal) := by
  have hne : volume (Kakeya.plankWindow.carrier : Set E₃) ≠ ⊤ :=
    Kakeya.plankWindow.isCompact.measure_ne_top
  calc volume (Kakeya.plankWindow.carrier : Set E₃)
      = (((volume (Kakeya.plankWindow.carrier : Set E₃)).toNNReal : NNReal) : ENNReal) := by
        rw [ENNReal.coe_toNNReal hne]
    _ ≤ (thickPlankWindowVol : ENNReal) := by
        exact ENNReal.coe_le_coe.2 (le_max_right _ _)

/-- **The enlarged comparison constant at which the subfamily selection is run.**

`Kakeya.VeryNotSticky.thickPlank_hKvol` asks for `6144 C₀⁸ ≤ C_e c_W`, and the volume floor
`c_W` carries no lower bound on the pinned contraction. Adding `6144 C₀⁸ / c_W` to `C₀` makes
`plankEnclosureConstant` of the result clear the bar by itself, because
`plankEnclosureConstant x = max 1 (2²⁰ x⁶) ≥ x` for `x ≥ 1`. -/
def thickPlankEnclC₀ (C₀ : NNReal) : NNReal :=
  C₀ + 6144 * C₀ ^ (8 : ℕ) / thickPlankBodyFloor C₀

theorem one_le_thickPlankEnclC₀ {C₀ : NNReal} (hC₀ : 1 ≤ C₀) : 1 ≤ thickPlankEnclC₀ C₀ :=
  hC₀.trans le_self_add

/-- The enclosure constant of the selection, at the enlarged comparison constant. -/
def thickPlankCe (C₀ : NNReal) : NNReal := plankEnclosureConstant (thickPlankEnclC₀ C₀)

/-- The selection constant, at the enlarged comparison constant **and at the non-ED degree bound
`edMultiplicityConstant`**: the cluster degree of a
family whose inner bodies have non-ED degree `≤ D_K` is `(D_K + 1) · C^{sel} − 1`
(`Kakeya.VeryNotSticky.plankClusterBound_of_degree`), so the selection loses
`(D_K + 1) · C^{sel}(thickPlankEnclC₀ C₀)`.  `δ`-free, a function of `C₀` alone. -/
def thickPlankCsel (C₀ : NNReal) : NNReal :=
  ((edMultiplicityConstant : NNReal) + 1) * plankSelectionConstant (thickPlankEnclC₀ C₀)

theorem one_le_thickPlankCe (C₀ : NNReal) : 1 ≤ thickPlankCe C₀ :=
  one_le_plankEnclosureConstant _

theorem one_le_thickPlankCsel (C₀ : NNReal) : 1 ≤ thickPlankCsel C₀ :=
  one_le_mul_of_one_le_of_one_le le_add_self (one_le_plankSelectionConstant _)

/-- `6144 C₀⁸ ≤ C_e c_W`, the hypothesis of `Kakeya.VeryNotSticky.thickPlank_hKvol`. -/
theorem thickPlank_hKvol_const {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    6144 * C₀ ^ (8 : ℕ) ≤ thickPlankCe C₀ * thickPlankBodyFloor C₀ := by
  have hfl : 0 < thickPlankBodyFloor C₀ := thickPlankBodyFloor_pos hC₀
  have hE : 1 ≤ thickPlankEnclC₀ C₀ := one_le_thickPlankEnclC₀ hC₀
  have hEe : thickPlankEnclC₀ C₀ ≤ thickPlankCe C₀ := by
    rw [thickPlankCe, plankEnclosureConstant]
    refine le_max_of_le_right ?_
    have hpow : (thickPlankEnclC₀ C₀) ^ (1 : ℕ) ≤ (thickPlankEnclC₀ C₀) ^ (6 : ℕ) :=
      pow_le_pow_right₀ hE (by norm_num)
    have h2 : (1 : NNReal) ≤ 2 ^ (20 : ℕ) := one_le_pow₀ (by norm_num)
    calc thickPlankEnclC₀ C₀ = 1 * (thickPlankEnclC₀ C₀) ^ (1 : ℕ) := by norm_num
      _ ≤ 2 ^ (20 : ℕ) * (thickPlankEnclC₀ C₀) ^ (6 : ℕ) := by gcongr
  have hdiv : 6144 * C₀ ^ (8 : ℕ) / thickPlankBodyFloor C₀ ≤ thickPlankEnclC₀ C₀ := by
    rw [thickPlankEnclC₀]
    exact le_add_self
  calc 6144 * C₀ ^ (8 : ℕ)
      = 6144 * C₀ ^ (8 : ℕ) / thickPlankBodyFloor C₀ * thickPlankBodyFloor C₀ := by
        rw [div_mul_cancel₀ _ (ne_of_gt hfl)]
    _ ≤ thickPlankCe C₀ * thickPlankBodyFloor C₀ := by
        gcongr
        exact hdiv.trans hEe

/-- **The plank comparison constant `C_{lem:ml2thickPlank}(C₀)`**, `δ`-free.

Five factors, one per obligation: `4 C₀` for the comparabilities of G10a, `C_sel` for
`sel_card`, `C_e` for the enclosure, `6 C₀⁶` and `V_win` for field 16. -/
def thickPlankCP (C₀ : NNReal) : NNReal :=
  4 * C₀ * thickPlankCsel C₀ * thickPlankCe C₀ * (6 * C₀ ^ (6 : ℕ)) * thickPlankWindowVol

/-- **The non-concentration constant `Θ`**, `δ`-free, a function of `(C₀, C_NC, ϱ)`. -/
def thickPlankΘ (C₀ C_NC : NNReal) (ϱ : ℝ) : NNReal :=
  thickNonconcΘ C₀ C_NC (thickPlankCP C₀) (thickPlankBodyFloor C₀) ϱ

section CPFacts

variable {C₀ : NNReal}

private theorem four_C₀_ge (hC₀ : 1 ≤ C₀) : (1 : NNReal) ≤ 4 * C₀ := by
  calc (1 : NNReal) = 1 * 1 := by norm_num
    _ ≤ 4 * C₀ := by gcongr; norm_num

private theorem six_C₀_ge (hC₀ : 1 ≤ C₀) : (1 : NNReal) ≤ 6 * C₀ ^ (6 : ℕ) := by
  have h : (1 : NNReal) ≤ C₀ ^ (6 : ℕ) := one_le_pow₀ hC₀
  calc (1 : NNReal) = 1 * 1 := by norm_num
    _ ≤ 6 * C₀ ^ (6 : ℕ) := by gcongr; norm_num

/-- `4 C₀ ≤ CP`: the four comparabilities of G10a. -/
theorem four_mul_le_thickPlankCP (hC₀ : 1 ≤ C₀) : 4 * C₀ ≤ thickPlankCP C₀ := by
  have h4 := four_C₀_ge hC₀
  have hs := one_le_thickPlankCsel C₀
  have he := one_le_thickPlankCe C₀
  have h6 := six_C₀_ge hC₀
  have hv := one_le_thickPlankWindowVol
  rw [thickPlankCP]
  calc 4 * C₀ = 4 * C₀ * 1 * 1 * 1 * 1 := by ring
    _ ≤ 4 * C₀ * thickPlankCsel C₀ * thickPlankCe C₀ * (6 * C₀ ^ (6 : ℕ)) *
        thickPlankWindowVol := by gcongr

/-- `C_sel ≤ CP`: field 12 `sel_card`. -/
theorem thickPlankCsel_le_thickPlankCP (hC₀ : 1 ≤ C₀) :
    thickPlankCsel C₀ ≤ thickPlankCP C₀ := by
  have h4 := four_C₀_ge hC₀
  have he := one_le_thickPlankCe C₀
  have h6 := six_C₀_ge hC₀
  have hv := one_le_thickPlankWindowVol
  rw [thickPlankCP]
  calc thickPlankCsel C₀ = 1 * thickPlankCsel C₀ * 1 * 1 * 1 := by ring
    _ ≤ 4 * C₀ * thickPlankCsel C₀ * thickPlankCe C₀ * (6 * C₀ ^ (6 : ℕ)) *
        thickPlankWindowVol := by gcongr

/-- `C_sel C_e ≤ CP`: field 15 `fullness_ge`. -/
theorem thickPlankCsel_mul_thickPlankCe_le_thickPlankCP (hC₀ : 1 ≤ C₀) :
    thickPlankCsel C₀ * thickPlankCe C₀ ≤ thickPlankCP C₀ := by
  have h4 := four_C₀_ge hC₀
  have h6 := six_C₀_ge hC₀
  have hv := one_le_thickPlankWindowVol
  rw [thickPlankCP]
  calc thickPlankCsel C₀ * thickPlankCe C₀
      = 1 * thickPlankCsel C₀ * thickPlankCe C₀ * 1 * 1 := by ring
    _ ≤ 4 * C₀ * thickPlankCsel C₀ * thickPlankCe C₀ * (6 * C₀ ^ (6 : ℕ)) *
        thickPlankWindowVol := by gcongr

/-- `C_e (6 C₀⁶ C_sel V_win) ≤ CP`: field 16 `frostman`. -/
theorem thickPlankCe_mul_le_thickPlankCP (hC₀ : 1 ≤ C₀) :
    thickPlankCe C₀ * (6 * C₀ ^ (6 : ℕ) * thickPlankCsel C₀ * thickPlankWindowVol)
      ≤ thickPlankCP C₀ := by
  have h4 := four_C₀_ge hC₀
  rw [thickPlankCP]
  calc thickPlankCe C₀ * (6 * C₀ ^ (6 : ℕ) * thickPlankCsel C₀ * thickPlankWindowVol)
      = 1 * thickPlankCsel C₀ * thickPlankCe C₀ * (6 * C₀ ^ (6 : ℕ)) *
        thickPlankWindowVol := by ring
    _ ≤ 4 * C₀ * thickPlankCsel C₀ * thickPlankCe C₀ * (6 * C₀ ^ (6 : ℕ)) *
        thickPlankWindowVol := by gcongr

theorem one_le_thickPlankCP (hC₀ : 1 ≤ C₀) : 1 ≤ thickPlankCP C₀ :=
  (four_C₀_ge hC₀).trans (four_mul_le_thickPlankCP hC₀)

end CPFacts

theorem one_le_thickPlankΘ {C₀ C_NC : NNReal} (hC₀ : 1 ≤ C₀) (hC_NC : 1 ≤ C_NC) {ϱ : ℝ}
    (hϱ : 0 ≤ ϱ) : 1 ≤ thickPlankΘ C₀ C_NC ϱ := by
  refine one_le_thickNonconcΘ hC₀ hϱ (thickPlankBodyFloor_pos hC₀) ?_
  have hκ : Real.toNNReal thickNormKappa ^ (3 : ℕ) ≤ 1 := by
    calc Real.toNNReal thickNormKappa ^ (3 : ℕ) ≤ 1 ^ (3 : ℕ) :=
          pow_le_pow_left' toNNReal_thickNormKappa_le_one 3
      _ = 1 := one_pow 3
  have hfloor : thickPlankBodyFloor C₀ ≤ 1 := by
    rw [thickPlankBodyFloor]
    refine div_le_one_of_le₀ (hκ.trans ?_) bot_le
    have h1 : (1 : NNReal) ≤ C₀ ^ (5 : ℕ) := one_le_pow₀ hC₀
    calc (1 : NNReal) = 1 * 1 := by norm_num
      _ ≤ 6 * C₀ ^ (5 : ℕ) := by gcongr; norm_num
  refine hfloor.trans ?_
  have h1 : (1 : NNReal) ≤ C_NC ^ (3 : ℕ) := one_le_pow₀ hC_NC
  have h2 : (1 : NNReal) ≤ thickPlankCP C₀ ^ (2 : ℕ) := one_le_pow₀ (one_le_thickPlankCP hC₀)
  calc (1 : NNReal) = 1 * 1 * 1 := by norm_num
    _ ≤ 8 * C_NC ^ (3 : ℕ) * thickPlankCP C₀ ^ (2 : ℕ) := by gcongr; norm_num

/-! ### The assembly -/

/-- Construct the eighteen fields of `ThickPlankPresentation` at
`CP = thickPlankCP bd.C₀` and `Θ = thickPlankΘ bd.C₀ C_NC cfg.ϱ`,
which are independent of `δ`. The geometric hypothesis `hEDdeg` is
the non-ED degree bound on the segments in each ball.

The selection uses the enlarged parameter `thickPlankEnclC₀ bd.C₀`
in `plankSubfamilySelection_card_of_degree`. The pairwise theorem
`thickPlankSelection_of_edImages` specializes to degree zero and
comparison parameter `bd.C₀`, so it does not provide this enlargement.
Neither `params` nor `hthick` is needed for the construction;
`thickPlankPresentable_of_ballData_params` retains those arguments
for callers that already carry them. -/
theorem thickPlankPresentable_of_ballData (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (hEDdeg : ∀ B ∈ bd.bs, ∀ p ∈ bd.segs B,
      {q ∈ (bd.segs B : Set bd.σ) | q ≠ p ∧
        ¬ _root_.IsEssentiallyDistinct (bd.Y p).carrier (bd.Y q).carrier}.ncard ≤
          edMultiplicityConstant)
    (C_NC : NNReal) (hC_NC : 1 ≤ C_NC) :
    ThickPlankPresentable bd (thickPlankCP bd.C₀) (thickPlankΘ bd.C₀ C_NC cfg.ϱ) C_NC := by
  classical
  intro B hB p₀ hp₀
  have hj : bd.blk p₀ ∈ bd.bodies B := bd.blk_mem B hB p₀ hp₀
  obtain ⟨L, P, hshade, hwin, hencl, hfloor, hLwin⟩ := exists_thickPlankNormalisation bd hB hj
  -- the enclosure volume comparison at the segment level (row G10c)
  have hup_a : thickPlankShort cfg bd.C₀ ≤ 4 * bd.C₀ * (cfg.δ / cfg.b) := by
    rw [← mul_div_assoc]
    exact thickPlankShort_le_const cfg bd.hC₀
  have hup_b : thickPlankLong cfg bd.C₀ ≤ 4 * bd.C₀ * (cfg.δ / cfg.a) := by
    rw [← mul_div_assoc]
    exact thickPlankLong_le_const cfg bd.hC₀
  have hKvolL := thickPlank_hKvol cfg bd hB hj hup_a hup_b L hfloor
    (thickPlank_hKvol_const bd.hC₀)
  -- the image bodies, and the subfamily selection at the enlarged comparison constant
  set K : bd.σ → ConvexSpaceBody E₃ :=
    fun p => ConvexSpaceBody.affineImage L.toAffineMap L.continuous_of_finiteDimensional
      (bd.Y p).toConvexSpaceBody with hKdef
  have hKcar : ∀ p, ((K p).carrier : Set E₃) = L '' ((bd.Y p).carrier : Set E₃) := by
    intro p
    rw [hKdef]
    simp
  have hKP : ∀ p ∈ (bd.segs B).filter (fun q => bd.blk q = bd.blk p₀),
      ((K p).carrier : Set E₃) ⊆ (((fun p => (P p).toPrism3D) p).carrier : Set E₃) := by
    intro p hp
    rw [hKcar p]
    exact hencl p hp
  have hKvol : ∀ p ∈ (bd.segs B).filter (fun q => bd.blk q = bd.blk p₀),
      8 * ((thickPlankShort cfg bd.C₀ : NNReal) : ENNReal) *
          ((thickPlankLong cfg bd.C₀ : NNReal) : ENNReal)
        ≤ (plankEnclosureConstant (thickPlankEnclC₀ bd.C₀) : ENNReal) *
          volume ((K p).carrier : Set E₃) := by
    intro p hp
    rw [hKcar p]
    exact hKvolL p hp
  have hKdeg : ∀ p ∈ (bd.segs B).filter (fun q => bd.blk q = bd.blk p₀),
      {q ∈ (((bd.segs B).filter (fun q => bd.blk q = bd.blk p₀)) : Set bd.σ) | q ≠ p ∧
        ¬ _root_.IsEssentiallyDistinct ((K p).carrier : Set E₃)
          ((K q).carrier : Set E₃)}.ncard ≤ edMultiplicityConstant := by
    have h := edImages_of_edSegments_degree bd
      ((bd.segs B).filter (fun q => bd.blk q = bd.blk p₀)) (Finset.filter_subset _ _)
      (hEDdeg B hB) L
    intro p hp
    refine le_trans (le_of_eq ?_) (h p hp)
    simp only [hKcar]
  obtain ⟨sel, hsub, hed, hy, hcard⟩ :=
    plankSubfamilySelection_card_of_degree (C₀ := thickPlankEnclC₀ bd.C₀)
      (Csel := thickPlankCsel bd.C₀) (D_K := edMultiplicityConstant)
      (one_le_thickPlankEnclC₀ bd.hC₀) le_rfl (thickPlankShort_pos cfg bd.hC₀)
      (thickPlankShort_le_long cfg bd.hC₀) (thickPlankLong_le_one cfg bd.C₀)
      ((bd.segs B).filter (fun q => bd.blk q = bd.blk p₀))
      (fun p => (P p).toPrism3D) K hKP hKvol hKdeg (fun p => volume (bd.Y p).shade)
  -- the window, in the two shapes the two rows want
  have hwinBody : ∀ p ∈ sel, ((P p).carrier : Set E₃)
      ⊆ (Kakeya.plankWindow.carrier : Set E₃) := by
    intro p _
    refine (hwin p).trans ?_
    rw [Kakeya.plankWindow_carrier]
    refine closedBall_subset_closedBall ?_
    rw [Plank.windowRadius, Kakeya.plankWindowRadius]
    norm_num
  have hshadeSel : ∀ q ∈ sel, ((P q).shade : Set E₃) ⊆ L '' ((bd.Y q).shade) := by
    intro q hq
    exact le_of_eq (hshade q (hsub hq))
  refine ⟨{
    a' := thickPlankShort cfg bd.C₀
    b' := thickPlankLong cfg bd.C₀
    hab' := thickPlankShort_le_long cfg bd.hC₀
    hb1' := thickPlankLong_le_one cfg bd.C₀
    short_lower := thickPlank_short_lower cfg bd.hC₀ (one_le_thickPlankCP bd.hC₀)
    short_upper := thickPlank_short_upper cfg bd.hC₀ (four_mul_le_thickPlankCP bd.hC₀)
    long_lower := thickPlank_long_lower cfg bd.hC₀ (one_le_thickPlankCP bd.hC₀)
    long_upper := thickPlank_long_upper cfg bd.hC₀ (four_mul_le_thickPlankCP bd.hC₀)
    P := P
    sel := sel
    sel_subset := hsub
    sel_card := ?_
    windowed := isWindowedFamily_of_carrier_subset sel P hwin
    essDistinct := hed
    fullness_ge := thickPlank_fullness_ge cfg bd P sel hsub L hshade
      (lt_of_lt_of_le zero_lt_one (one_le_thickPlankCe bd.C₀)) hKvolL
      (lt_of_lt_of_le zero_lt_one (one_le_thickPlankCsel bd.C₀)) hy
      (thickPlankCsel_mul_thickPlankCe_le_thickPlankCP bd.hC₀)
    frostman := thickPlank_frostman cfg bd hB hj P sel hsub L hencl hwinBody hKvolL
      (lt_of_lt_of_le zero_lt_one (one_le_thickPlankCsel bd.C₀)) hcard
      (delta_div_b_le_thickPlankShort cfg bd.hC₀) (delta_div_a_le_thickPlankLong cfg bd.hC₀)
      volume_plankWindow_le_thickPlankWindowVol (thickPlankCe_mul_le_thickPlankCP bd.hC₀)
    volume_le := thickPlank_volume_le cfg bd hB P sel hsub L hshadeSel hLwin
    nonconcentration := ?_ }⟩
  · refine le_trans ?_ hcard
    have hle : ((thickPlankCsel bd.C₀ : NNReal) : ENNReal)
        ≤ ((thickPlankCP bd.C₀ : NNReal) : ENNReal) := by
      exact_mod_cast thickPlankCsel_le_thickPlankCP bd.hC₀
    gcongr
  · exact thickPlank_nonconcentration cfg bd hB hj P sel hsub (one_le_thickPlankCP bd.hC₀)
      (thickPlank_long_upper cfg bd.hC₀ (four_mul_le_thickPlankCP bd.hC₀)) L
      (fun q hq => hencl q (hsub hq)) (thickPlankBodyFloor_pos bd.hC₀) hfloor hC_NC

/-- Compatibility form carrying `params` and `hthick`. These arguments
are unused: the conclusion follows directly from
`Kakeya.VeryNotSticky.thickPlankPresentable_of_ballData`. -/
theorem thickPlankPresentable_of_ballData_params (cfg : VeryNotSticky.{u}) {τ τ' : ℝ}
    (_params : CaseParams cfg.β cfg.ζ cfg.exscal cfg.ϱ cfg.η τ τ') (bd : BallData cfg)
    (_hthick : cfg.δ ^ (1 - τ) ≤ cfg.a)
    (hEDdeg : ∀ B ∈ bd.bs, ∀ p ∈ bd.segs B,
      {q ∈ (bd.segs B : Set bd.σ) | q ≠ p ∧
        ¬ _root_.IsEssentiallyDistinct (bd.Y p).carrier (bd.Y q).carrier}.ncard ≤
          edMultiplicityConstant)
    (C_NC : NNReal) (hC_NC : 1 ≤ C_NC) :
    ThickPlankPresentable bd (thickPlankCP bd.C₀) (thickPlankΘ bd.C₀ C_NC cfg.ϱ) C_NC :=
  thickPlankPresentable_of_ballData cfg bd hEDdeg C_NC hC_NC

end Kakeya.VeryNotSticky

end

end
