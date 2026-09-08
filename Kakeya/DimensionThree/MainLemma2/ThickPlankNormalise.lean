/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.PlankPresentation
public import Kakeya.DimensionThree.MainLemma2.PlankRescaling
public import Kakeya.DimensionThree.MainLemma2.ThickPlankInterface
public import Kakeya.DimensionThree.MainLemma2.ThickCase
public import Kakeya.DimensionThree.Plank.TubePlankNormalisation

/-!
# The plank model of a thick block, from the thickness data alone

Row G10a : fields `a'`, `b'`, `hab'`, `hb1'`,
`short_lower`–`long_upper`, `P` and `windowed` of
`Kakeya.VeryNotSticky.ThickPlankPresentation`.
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

/-! ### The axis decomposition of a body with a thickness profile -/

/-- **A body with profile `(t₀, t₁, t₁)` is a capsule around its own long axis**: every chord
splits into a multiple of the frame's long vector `bodyFrame K 2` and a residue of norm at most
`4 C t₁`.

This is what replaces the `Tube` structure in
`Kakeya.Plank.exists_axis_decomposition_of_mem_tube`. A `Tube` is the `δ`-neighbourhood of a
**unit** segment, and no rescaling of a `BallData` segment is one: after `L_B` the segments have
axial extent up to `2` and there is no unit-length axis to hang the neighbourhood on. What the
normalisation estimates actually consume is only the splitting below — the two existing bounds
`Kakeya.Plank.abs_inner_le_thin` and `Kakeya.Plank.abs_inner_le_mid` are stated for an arbitrary
residue `e` with `‖e‖ ≤ δ`, not for a tube — so the profile is enough.

The constant is `4` and not `2√2` only because the residue is bounded by the triangle inequality
on its two coordinates rather than by Pythagoras; nothing downstream is sensitive to it. -/
theorem norm_sub_axis_le_of_hasThicknesses (K : ConvexSpaceBody E₃) {C : NNReal} {t₀ t₁ : ℝ}
    (hthick : HasThicknesses (K.carrier : Set E₃) C ![t₀, t₁, t₁])
    {x u : E₃} (hx : x ∈ (K.carrier : Set E₃)) (hu : u ∈ (K.carrier : Set E₃)) :
    ‖(x - u) - ((bodyFrame K).repr (x - u) 2) • (bodyFrame K 2)‖ ≤ 4 * (C : ℝ) * t₁ := by
  classical
  set q : OrthonormalBasis (Fin 3) ℝ E₃ := bodyFrame K with hq
  set z : E₃ := x - u with hz
  have hsplit : z - (q.repr z 2) • q 2 = (q.repr z 0) • q 0 + (q.repr z 1) • q 1 := by
    have hsum : ∑ i : Fin 3, (q.repr z i) • q i = z := q.sum_repr z
    rw [Fin.sum_univ_three] at hsum
    exact sub_eq_iff_eq_add.mpr hsum.symm
  have hcoord : ∀ i : Fin 3, |q.repr z i| ≤ 2 * Metric.thickness ℝ (K.carrier : Set E₃)
      (Fin.rev i) := by
    intro i
    exact abs_bodyFrame_repr_sub_le K hx hu i
  have hth : ∀ k : Fin 3, Metric.thickness ℝ (K.carrier : Set E₃) (k : ℕ)
      ≤ (C : ℝ) * ![t₀, t₁, t₁] k := fun k => (hthick k).2
  have h0 : |q.repr z 0| ≤ 2 * ((C : ℝ) * t₁) := by
    refine (hcoord 0).trans ?_
    have := hth 2
    simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at this
    have hrev : ((Fin.rev (0 : Fin 3)) : ℕ) = ((2 : Fin 3) : ℕ) := by decide
    rw [hrev]
    exact mul_le_mul_of_nonneg_left this (by norm_num)
  have h1 : |q.repr z 1| ≤ 2 * ((C : ℝ) * t₁) := by
    refine (hcoord 1).trans ?_
    have := hth 1
    simp only [Matrix.cons_val_one] at this
    have hrev : ((Fin.rev (1 : Fin 3)) : ℕ) = ((1 : Fin 3) : ℕ) := by decide
    rw [hrev]
    exact mul_le_mul_of_nonneg_left this (by norm_num)
  calc
    ‖z - (q.repr z 2) • q 2‖ = ‖(q.repr z 0) • q 0 + (q.repr z 1) • q 1‖ := by rw [hsplit]
    _ ≤ ‖(q.repr z 0) • q 0‖ + ‖(q.repr z 1) • q 1‖ := norm_add_le _ _
    _ = |q.repr z 0| + |q.repr z 1| := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, q.norm_eq_one,
          q.norm_eq_one, mul_one, mul_one]
    _ ≤ 2 * ((C : ℝ) * t₁) + 2 * ((C : ℝ) * t₁) := add_le_add h0 h1
    _ = 4 * (C : ℝ) * t₁ := by ring

/-! ### The fixed contraction in plank normalization

`Kakeya.Plank.factorNormalisingAffineEquiv` supplies one positive
contraction `κ`, chosen before the plank. The volume lower bound
`cW ≤ |L(W_j)|` uses `cW = κ³ / (6 C₀^5)`. Naming `κ` with
`Exists.choose` makes this bound, and hence the resulting
nonconcentration constant `Θ`, a fixed function of `(C₀, C_NC, ϱ)`.
Only positivity and independence from the plank and scale are needed;
an explicit numerical value of `κ` is unnecessary.
-/

/-- **The pinned contraction of the plank normalisation.** `Exists.choose` of
`Kakeya.Plank.factorNormalisingAffineEquiv`, whose `κ` is chosen before the plank and is
therefore a single constant of the development. -/
noncomputable def thickNormKappa : ℝ := Plank.factorNormalisingAffineEquiv.choose

theorem thickNormKappa_pos : 0 < thickNormKappa := by
  obtain ⟨_cfac, _Cfac, hκ, _, _, _⟩ := Plank.factorNormalisingAffineEquiv.choose_spec
  exact hκ

/-- `Kakeya.Plank.factorNormalisingAffineEquiv` at the pinned contraction, with the three
clauses this file uses. -/
theorem exists_thickNormalisation {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1} (ha : 0 < a)
    (W : Plank a b hab hb1) :
    ∃ (f : E₃ →ᵃ[ℝ] E₃) (J : NNReal) (g : OrthonormalBasis (Fin 3) ℝ E₃),
      0 < J ∧ Plank.IsPlankNormalisation W f thickNormKappa g ∧
      (∀ E : Set E₃, volume (f '' E) = (J : ENNReal) * volume E) ∧
      f '' (W.carrier : Set E₃) ⊆ closedBall (0 : E₃) 1 := by
  obtain ⟨_cfac, _Cfac, _hκ, _, _, hall⟩ := Plank.factorNormalisingAffineEquiv.choose_spec
  obtain ⟨f, J, g, hJ0, hnorm, hvol, himg, _, _, _⟩ := hall ha W
  exact ⟨f, J, g, hJ0, hnorm, hvol, himg⟩

/-- `3 κ² ≤ 1` for the pinned contraction, hence `κ ≤ 1`.

`Kakeya.Plank.three_mul_sq_le_one_of_image_subset_closedBall` is stated for one plank; since the
contraction is the *same* for all of them, running it once on the unit plank
`Prism3D.std 1 1 1` fixes it globally. -/
theorem three_mul_thickNormKappa_sq_le_one : 3 * thickNormKappa ^ 2 ≤ 1 := by
  obtain ⟨f, J, g, _hJ0, hnorm, _hvolf, himg⟩ :=
    exists_thickNormalisation (a := (1 : NNReal)) (b := (1 : NNReal)) (hab := le_rfl)
      (hb1 := le_rfl) zero_lt_one (Prism3D.std (1 : NNReal) 1 1 le_rfl le_rfl)
  exact Plank.three_mul_sq_le_one_of_image_subset_closedBall zero_lt_one _ thickNormKappa_pos
    hnorm himg

theorem thickNormKappa_le_one : thickNormKappa ≤ 1 := by
  have h := three_mul_thickNormKappa_sq_le_one
  nlinarith [thickNormKappa_pos]

theorem toNNReal_thickNormKappa_le_one : Real.toNNReal thickNormKappa ≤ 1 := by
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ thickNormKappa_pos.le]
  simpa using thickNormKappa_le_one

/-- **The `δ`-free volume floor of a normalised factoring body**, `κ³ / (6 C₀⁵)`.

This is the constant `cW` of row G10e's `Kakeya.VeryNotSticky.thickPlank_nonconcentration`. It
is a function of `bd.C₀` and the pinned contraction alone — in particular `δ`-free — and it is
what makes `Kakeya.VeryNotSticky.thickPlankΘ` a `def` of `(C₀, C_NC, ϱ)`.

The `6 C₀³` is `Kakeya.VeryNotSticky.thickBodyVol`'s lower half and the `C₀²` is the product of
the two enclosing half-widths `Kakeya.VeryNotSticky.thickBodyShort`,
`Kakeya.VeryNotSticky.thickBodyLong` against `(C₀ a/r₁, C₀ b/r₁)`; the three powers of `r₁`
from the rescaling cancel exactly. -/
noncomputable def thickPlankBodyFloor (C₀ : NNReal) : NNReal :=
  (Real.toNNReal thickNormKappa) ^ (3 : ℕ) / (6 * C₀ ^ (5 : ℕ))

theorem thickPlankBodyFloor_pos {C₀ : NNReal} (hC₀ : 1 ≤ C₀) : 0 < thickPlankBodyFloor C₀ := by
  have hC : (0 : NNReal) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hκ : (0 : NNReal) < Real.toNNReal thickNormKappa := by
    rw [← NNReal.coe_pos, Real.coe_toNNReal _ thickNormKappa_pos.le]
    exact thickNormKappa_pos
  exact div_pos (by positivity) (by positivity)

/-! ### The enclosing plank of a rescaled factoring body -/

/-- `0 < r₁ = δ^{exscal}` as a real. -/
theorem thickPlank_r₁_pos (cfg : VeryNotSticky.{u}) : (0 : ℝ) < cfg.r₁ := by
  have h : (0 : NNReal) < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  exact_mod_cast h

/-- `0 < r₁` in `ℝ≥0`. -/
theorem thickPlank_r₁_pos' (cfg : VeryNotSticky.{u}) : (0 : NNReal) < cfg.r₁ :=
  NNReal.rpow_pos cfg.hδ

/-- **The short half-width of the plank enclosing a rescaled factoring body**, `min (C₀ a/r₁) 1`.

The cap at `1` is not cosmetic: `Plank` demands the middle half-width to be at most `1`, and
nothing in the configuration bounds `C₀ b` by `r₁` — `cfg.hdims` gives only `b ≤ r₁`. Capping
costs nothing, the enclosure being read inside `B̄(0,1)`, where a half-width of `1` already
dominates every spread. -/
def thickBodyShort (cfg : VeryNotSticky.{u}) (C₀ : NNReal) : NNReal :=
  min (C₀ * cfg.a / cfg.r₁) 1

/-- **The middle half-width of the plank enclosing a rescaled factoring body**,
`min (C₀ b/r₁) 1`; see `Kakeya.VeryNotSticky.thickBodyShort`. -/
def thickBodyLong (cfg : VeryNotSticky.{u}) (C₀ : NNReal) : NNReal :=
  min (C₀ * cfg.b / cfg.r₁) 1

theorem thickBodyShort_pos (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    0 < thickBodyShort cfg C₀ := by
  have hC : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have ha : 0 < cfg.a := cfg_a_pos cfg
  have hr : 0 < cfg.r₁ := thickPlank_r₁_pos' cfg
  refine lt_min ?_ zero_lt_one
  exact div_pos (mul_pos hC ha) hr

theorem thickBodyShort_le_long (cfg : VeryNotSticky.{u}) (C₀ : NNReal) :
    thickBodyShort cfg C₀ ≤ thickBodyLong cfg C₀ := by
  refine min_le_min ?_ le_rfl
  gcongr
  exact cfg.hdims.2.1

theorem thickBodyLong_le_one (cfg : VeryNotSticky.{u}) (C₀ : NNReal) :
    thickBodyLong cfg C₀ ≤ 1 := min_le_right _ _

theorem thickBodyShort_le (cfg : VeryNotSticky.{u}) (C₀ : NNReal) :
    thickBodyShort cfg C₀ ≤ C₀ * cfg.a / cfg.r₁ := min_le_left _ _

theorem thickBodyLong_le (cfg : VeryNotSticky.{u}) (C₀ : NNReal) :
    thickBodyLong cfg C₀ ≤ C₀ * cfg.b / cfg.r₁ := min_le_left _ _

/-- **Admissible dimensions are self-certifying.** `Kakeya.VeryNotSticky.plankWindowEnclosure`
uses the four scales `C₀, a, b, r₁` of `Kakeya.VeryNotSticky.IsAdmissiblePlankDimensions` only
through the record; at `C₀ = r₁ = 1` and `(a, b) = (a', b')` the two domination clauses are
reflexive, so any legal pair of plank dimensions is admissible and the enclosure may be run at
dimensions the configuration does not dominate — which is what the cap of
`Kakeya.VeryNotSticky.thickBodyShort` needs. -/
theorem isAdmissiblePlankDimensions_self {a' b' : NNReal} (ha' : 0 < a') (hab' : a' ≤ b')
    (hb1' : b' ≤ 1) : IsAdmissiblePlankDimensions 1 a' b' 1 a' b' :=
  { short_pos := ha'
    short_le_long := hab'
    long_le_one := hb1'
    le_short := by simp
    le_long := by simp }

/-- **The plank model of a factoring body** (fields `a'`–`hb1'` of the *outer* plank).

`L_B(W)` is enclosed in a plank of half-widths `(min (C₀ a/r₁) 1, min (C₀ b/r₁) 1, 1)` on the
body's own ascending frame, inside the window `B̄(0, 4)`. Everything is existing:
`Kakeya.VeryNotSticky.plankRescaledFamily_spread` for the two short spreads,
`Kakeya.VeryNotSticky.plankRescale_image_closedBall` for the containment in `B̄(0,1)` — which is
also what supplies the spread bound `2` in the capped branch — and
`Kakeya.VeryNotSticky.plankWindowEnclosure` for the enclosure itself. -/
theorem exists_thickBodyPlank {cfg : VeryNotSticky.{u}} (bd : BallData cfg) {B : bd.bι}
    (hB : B ∈ bd.bs) {j : bd.ω} (hj : j ∈ bd.bodies B) :
    ∃ W : Plank (thickBodyShort cfg bd.C₀) (thickBodyLong cfg bd.C₀)
        (thickBodyShort_le_long cfg bd.C₀) (thickBodyLong_le_one cfg bd.C₀),
      (plankRescale (bd.ctr B) (thickPlank_r₁_pos cfg).ne' ''
          ((bd.Wb j).carrier : Set E₃)) ⊆ (W.carrier : Set E₃) ∧
      (W.carrier : Set E₃) ⊆ closedBall (0 : E₃) (plankBallRadius : ℝ) := by
  classical
  set hr₁ : (0 : ℝ) < (cfg.r₁ : ℝ) := thickPlank_r₁_pos cfg with hr₁def
  set L := plankRescale (bd.ctr B) hr₁.ne' with hL
  set K : Set E₃ := L '' ((bd.Wb j).carrier : Set E₃) with hK
  have hball : L '' closedBall (bd.ctr B) (cfg.r₁ : ℝ) = closedBall (0 : E₃) 1 := by
    rw [hL, plankRescale_image_closedBall (bd.ctr B) hr₁, plankRescale_apply, sub_self,
      smul_zero, div_self hr₁.ne']
  have hK1 : K ⊆ closedBall (0 : E₃) 1 := by
    rw [hK, ← hball]
    exact Set.image_mono (bd.bodies_subset_ball B hB j hj)
  have hKcpt : IsCompact K := by
    rw [hK]
    exact (bd.Wb j).isCompact'.image (plankRescale_continuous (bd.ctr B) hr₁.ne')
  have hKne : K.Nonempty := by
    rw [hK]
    exact (bd.Wb j).nonempty'.image _
  -- the two spreads
  have hspreadRaw := plankRescaledFamily_spread ({j} : Finset bd.ω) bd.Wb bd.hC₀
    (thickPlank_r₁_pos' cfg) (bd.ctr B)
    (by
      intro j' hj'
      rw [Finset.mem_singleton] at hj'
      rw [hj']
      exact bd.bodies_thickness B hB j hj) j (Finset.mem_singleton_self j)
  have hcarrier : (((bd.Wb j).plankRescale (bd.ctr B)
      (NNReal.coe_ne_zero.mpr (thickPlank_r₁_pos' cfg).ne')).carrier : Set E₃) = K := by
    rw [hK, hL]
    simp [ConvexSpaceBody.plankRescale]
  rw [hcarrier] at hspreadRaw
  have hballspread : ∀ x ∈ K, ∀ u ∈ K, ∀ i : Fin 3,
      |(bodyFrame (bd.Wb j)).repr (x - u) i| ≤ 2 := by
    intro x hx u hu i
    have hxn : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp (hK1 hx)
    have hun : ‖u‖ ≤ 1 := mem_closedBall_zero_iff.mp (hK1 hu)
    have hnorm : ‖x - u‖ ≤ 2 := by
      have := norm_sub_le x u
      linarith
    calc
      |(bodyFrame (bd.Wb j)).repr (x - u) i|
          ≤ ‖(bodyFrame (bd.Wb j)) i‖ * ‖x - u‖ := by
            rw [OrthonormalBasis.repr_apply_apply]
            exact abs_real_inner_le_norm _ _
      _ = ‖x - u‖ := by rw [(bodyFrame (bd.Wb j)).norm_eq_one, one_mul]
      _ ≤ 2 := hnorm
  have hspread : ∀ x ∈ K, ∀ u ∈ K,
      |(bodyFrame (bd.Wb j)).repr (x - u) 0| ≤ 2 * ((thickBodyShort cfg bd.C₀ : NNReal) : ℝ) ∧
      |(bodyFrame (bd.Wb j)).repr (x - u) 1| ≤ 2 * ((thickBodyLong cfg bd.C₀ : NNReal) : ℝ) := by
    intro x hx u hu
    obtain ⟨h0, h1⟩ := hspreadRaw x hx u hu
    constructor
    · rw [thickBodyShort]
      rcases le_total (bd.C₀ * cfg.a / cfg.r₁) (1 : NNReal) with hle | hle
      · rw [min_eq_left hle]; exact h0
      · rw [min_eq_right hle]
        simpa using hballspread x hx u hu 0
    · rw [thickBodyLong]
      rcases le_total (bd.C₀ * cfg.b / cfg.r₁) (1 : NNReal) with hle | hle
      · rw [min_eq_left hle]; exact h1
      · rw [min_eq_right hle]
        simpa using hballspread x hx u hu 1
  obtain ⟨P, hKP, hwin, _hbasis⟩ :=
    plankWindowEnclosure (C₀ := 1) (a := thickBodyShort cfg bd.C₀)
      (b := thickBodyLong cfg bd.C₀) (r₁ := 1) le_rfl zero_lt_one
      (thickBodyShort_le_long cfg bd.C₀)
      (isAdmissiblePlankDimensions_self (thickBodyShort_pos cfg bd.hC₀)
        (thickBodyShort_le_long cfg bd.C₀) (thickBodyLong_le_one cfg bd.C₀))
      hKcpt hKne hK1 (bodyFrame (bd.Wb j)) hspread
  exact ⟨P, hKP, hwin⟩

/-! ### The normalised plank model of one segment -/

theorem thickSegShort_le_long {aW bW : NNReal} (haW : 0 < aW) (h : aW ≤ bW) (δe : NNReal) :
    min (δe / bW) 1 ≤ min (δe / aW) 1 := by
  refine min_le_min ?_ le_rfl
  gcongr

theorem thickSegShort_pos {aW bW δe : NNReal} (haW : 0 < aW) (h : aW ≤ bW) (hδe : 0 < δe) :
    0 < min (δe / bW) 1 :=
  lt_min (div_pos hδe (lt_of_lt_of_le haW h)) zero_lt_one

/-- **The normalised plank model of a capsule-shaped body inside a factor plank.**

This is `Kakeya.Plank.exists_normalisedTubePlank` with the `Tube` hypothesis replaced by the
axis splitting `Kakeya.VeryNotSticky.norm_sub_axis_le_of_hasThicknesses` supplies. The proof is
the same three estimates:

* along the thin normal `n` — chosen orthogonal to both the image axis `ŵ` and to `g 0` — the
  axial part of the chord contributes nothing and the residue contributes at most `δe / bW`
  (`Kakeya.Plank.abs_inner_le_thin`);
* along the middle axis `m` — orthogonal to `ŵ` — the axial part again contributes nothing and
  the residue at most `δe / aW` (`Kakeya.Plank.abs_inner_le_mid`);
* along every direction, the window gives the crude bound `2`, which is what lets the two plank
  dimensions be capped at `1` (the ratios `δe / bW`, `δe / aW` are not bounded by `1` in general).

The plank is produced by `Kakeya.VeryNotSticky.plankWindowEnclosure` on the frame
`(n, m, ŵ)`, which also delivers the window containment. -/
theorem exists_thickSegmentPlank {aW bW : NNReal} {habW : aW ≤ bW} {hbW1 : bW ≤ 1}
    (haW : 0 < aW) (W : Plank aW bW habW hbW1)
    {f : E₃ →ᵃ[ℝ] E₃} {κ : ℝ} (hκ : 0 < κ)
    {g : OrthonormalBasis (Fin 3) ℝ E₃}
    (hnorm : Plank.IsPlankNormalisation W f κ g)
    (himg : f '' (W.carrier : Set E₃) ⊆ closedBall (0 : E₃) 1)
    (K : ConvexSpaceBody E₃) (hKW : (K.carrier : Set E₃) ⊆ (W.carrier : Set E₃))
    {δe : NNReal} (hδe : 0 < δe)
    (hcap : ∀ x ∈ (K.carrier : Set E₃), ∀ u ∈ (K.carrier : Set E₃),
      ‖(x - u) - ((bodyFrame K).repr (x - u) 2) • (bodyFrame K 2)‖ ≤ (δe : ℝ)) :
    ∃ P : Plank (min (δe / bW) 1) (min (δe / aW) 1)
        (thickSegShort_le_long haW habW δe) (min_le_right _ _),
      f '' (K.carrier : Set E₃) ⊆ (P.carrier : Set E₃) ∧
      (P.carrier : Set E₃) ⊆ closedBall (0 : E₃) (plankBallRadius : ℝ) := by
  classical
  have hκ3 : 3 * κ ^ 2 ≤ 1 :=
    Plank.three_mul_sq_le_one_of_image_subset_closedBall haW W hκ hnorm himg
  have hthick_pos : ∀ i : Fin 3, (0 : ℝ) < (W.thicknesses i : ℝ) := by
    intro i
    rw [W.thicknesses_eq]
    fin_cases i
    · exact_mod_cast haW
    · exact_mod_cast (lt_of_lt_of_le haW habW)
    · norm_num
  -- the long axis of `K` and its image direction
  set v : E₃ := bodyFrame K 2 with hv
  have hv1 : ‖v‖ = 1 := (bodyFrame K).norm_eq_one 2
  set D : E₃ := f (W.center + v) - f W.center with hD
  have hDg : ∀ i : Fin 3, inner ℝ D (g i)
      = κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ v (W.basis i) := by
    intro i
    have h := Plank.inner_image_sub_basis W hnorm (W.center + v) W.center i
    rw [hD]
    simpa using h
  have hD0 : D ≠ 0 := by
    intro h0
    have hzero : ∀ i : Fin 3, inner ℝ v (W.basis i) = 0 := by
      intro i
      have h := hDg i
      rw [h0] at h
      simp only [inner_zero_left] at h
      have hne : κ * ((W.thicknesses i : ℝ))⁻¹ ≠ 0 :=
        mul_ne_zero (ne_of_gt hκ) (inv_ne_zero (ne_of_gt (hthick_pos i)))
      exact (mul_eq_zero.mp h.symm).resolve_left hne
    have hv0 : v = 0 := by
      have hsum : ∑ i : Fin 3, (W.basis.repr v i) • W.basis i = v := W.basis.sum_repr v
      rw [← hsum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [W.basis.repr_apply_apply, real_inner_comm, hzero i, zero_smul]
    rw [hv0] at hv1
    simp at hv1
  have hDnorm : (0 : ℝ) < ‖D‖ := norm_pos_iff.mpr hD0
  set ŵ : E₃ := (‖D‖⁻¹ : ℝ) • D with hŵ
  have hŵ1 : ‖ŵ‖ = 1 := by
    rw [hŵ, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg D)),
      inv_mul_cancel₀ (ne_of_gt hDnorm)]
  have hDeq : D = ‖D‖ • ŵ := by
    rw [hŵ, smul_smul, mul_inv_cancel₀ (ne_of_gt hDnorm), one_smul]
  -- the adapted frame
  obtain ⟨n, hn1, hnŵ, hng0⟩ := Plank.exists_unit_orthogonal_pair ŵ (g 0)
  obtain ⟨Bs, hB0, hB2⟩ := Plank.exists_orthonormalBasis_fst_thd_eq hn1 hŵ1 hnŵ
  set m : E₃ := Bs 1 with hm
  have hm1 : ‖m‖ = 1 := Bs.norm_eq_one 1
  have hmŵ : inner ℝ m ŵ = 0 := by
    rw [hm, ← hB2]
    exact Bs.inner_eq_zero (by decide)
  -- the two axial vanishings
  have hDn : inner ℝ D n = 0 := by
    rw [hDeq, real_inner_smul_left, real_inner_comm, hnŵ, mul_zero]
  have hDm : inner ℝ D m = 0 := by
    rw [hDeq, real_inner_smul_left, real_inner_comm, hmŵ, mul_zero]
  -- the chord estimates
  have hchord : ∀ (w : E₃), inner ℝ D w = 0 → ‖w‖ = 1 →
      ∀ x ∈ (K.carrier : Set E₃), ∀ u ∈ (K.carrier : Set E₃),
        inner ℝ (f x - f u) w
          = ∑ i, inner ℝ w (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹ *
              inner ℝ ((x - u) - ((bodyFrame K).repr (x - u) 2) • v) (W.basis i)) := by
    intro w hw _hw1 x hx u hu
    set t : ℝ := (bodyFrame K).repr (x - u) 2 with ht
    set e : E₃ := (x - u) - t • v with he
    have hsplit : x - u = t • v + e := by rw [he]; abel
    have hexp := Plank.inner_image_sub_expand W hnorm x u w
    have hexpv := Plank.inner_image_sub_expand W hnorm (W.center + v) W.center w
    have hDw : inner ℝ D w
        = ∑ i, inner ℝ w (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ v (W.basis i)) := by
      rw [hD]
      simpa using hexpv
    rw [hexp]
    have hterm : ∀ i : Fin 3, inner ℝ w (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹ *
          inner ℝ (x - u) (W.basis i))
        = t * (inner ℝ w (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ v (W.basis i)))
          + inner ℝ w (g i) * (κ * ((W.thicknesses i : ℝ))⁻¹ * inner ℝ e (W.basis i)) := by
      intro i
      rw [hsplit, inner_add_left, real_inner_smul_left]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, ← Finset.mul_sum,
      ← hDw, hw, mul_zero, zero_add]
  -- spread bounds
  have hKimg : f '' (K.carrier : Set E₃) ⊆ closedBall (0 : E₃) 1 :=
    Set.Subset.trans (Set.image_mono hKW) himg
  have hballspread : ∀ X ∈ f '' (K.carrier : Set E₃), ∀ U ∈ f '' (K.carrier : Set E₃),
      ∀ i : Fin 3, |Bs.repr (X - U) i| ≤ 2 := by
    intro X hX U hU i
    have hXn : ‖X‖ ≤ 1 := mem_closedBall_zero_iff.mp (hKimg hX)
    have hUn : ‖U‖ ≤ 1 := mem_closedBall_zero_iff.mp (hKimg hU)
    have hnormXU : ‖X - U‖ ≤ 2 := by
      have := norm_sub_le X U
      linarith
    calc
      |Bs.repr (X - U) i| ≤ ‖Bs i‖ * ‖X - U‖ := by
        rw [OrthonormalBasis.repr_apply_apply]
        exact abs_real_inner_le_norm _ _
      _ = ‖X - U‖ := by rw [Bs.norm_eq_one, one_mul]
      _ ≤ 2 := hnormXU
  have hspread : ∀ X ∈ f '' (K.carrier : Set E₃), ∀ U ∈ f '' (K.carrier : Set E₃),
      |Bs.repr (X - U) 0| ≤ 2 * ((min (δe / bW) 1 : NNReal) : ℝ) ∧
      |Bs.repr (X - U) 1| ≤ 2 * ((min (δe / aW) 1 : NNReal) : ℝ) := by
    rintro X ⟨x, hx, rfl⟩ U ⟨u, hu, rfl⟩
    have hres : ‖(x - u) - ((bodyFrame K).repr (x - u) 2) • v‖ ≤ (δe : ℝ) := hcap x hx u hu
    have h0 : |Bs.repr (f x - f u) 0| ≤ ((δe / bW : NNReal) : ℝ) := by
      rw [OrthonormalBasis.repr_apply_apply, hB0, real_inner_comm]
      rw [hchord n hDn hn1 x hx u hu]
      exact Plank.abs_inner_le_thin haW hκ hκ3 W hn1 hng0 hres
    have h1 : |Bs.repr (f x - f u) 1| ≤ ((δe / aW : NNReal) : ℝ) := by
      rw [OrthonormalBasis.repr_apply_apply, ← hm, real_inner_comm]
      rw [hchord m hDm hm1 x hx u hu]
      exact Plank.abs_inner_le_mid haW hκ hκ3 W hm1 hres
    have hb0 := hballspread (f x) ⟨x, hx, rfl⟩ (f u) ⟨u, hu, rfl⟩ 0
    have hb1 := hballspread (f x) ⟨x, hx, rfl⟩ (f u) ⟨u, hu, rfl⟩ 1
    constructor
    · rcases le_total (δe / bW) (1 : NNReal) with hle | hle
      · rw [min_eq_left hle]
        refine h0.trans ?_
        have : ((δe / bW : NNReal) : ℝ) ≤ 2 * ((δe / bW : NNReal) : ℝ) := by
          nlinarith [(δe / bW : NNReal).coe_nonneg]
        exact this
      · rw [min_eq_right hle]
        simpa using hb0
    · rcases le_total (δe / aW) (1 : NNReal) with hle | hle
      · rw [min_eq_left hle]
        refine h1.trans ?_
        have : ((δe / aW : NNReal) : ℝ) ≤ 2 * ((δe / aW : NNReal) : ℝ) := by
          nlinarith [(δe / aW : NNReal).coe_nonneg]
        exact this
      · rw [min_eq_right hle]
        simpa using hb1
  have hKcpt : IsCompact (f '' (K.carrier : Set E₃)) :=
    K.isCompact'.image f.continuous_of_finiteDimensional
  have hKne : (f '' (K.carrier : Set E₃)).Nonempty := K.nonempty'.image _
  obtain ⟨P, hKP, hwin, _hbasis⟩ :=
    plankWindowEnclosure (C₀ := 1) (a := min (δe / bW) 1) (b := min (δe / aW) 1) (r₁ := 1)
      le_rfl zero_lt_one (thickSegShort_le_long haW habW δe)
      (isAdmissiblePlankDimensions_self (thickSegShort_pos haW habW hδe)
        (thickSegShort_le_long haW habW δe) (min_le_right _ _))
      hKcpt hKne hKimg Bs hspread
  exact ⟨P, hKP, hwin⟩

/-! ### The plank dimensions of the thick presentation, and their comparabilities -/

/-- **The residue scale of a rescaled segment**, `4 C₀ δ / r₁`: the radius of the capsule that
`Kakeya.VeryNotSticky.norm_sub_axis_le_of_hasThicknesses` puts around the long axis of
`L_B(Y_p)`. -/
def thickSegScale (cfg : VeryNotSticky.{u}) (C₀ : NNReal) : NNReal :=
  4 * C₀ * cfg.δ / cfg.r₁

/-- **The short dimension `a'` of the thick presentation**, `min (δe / bW) 1`. -/
def thickPlankShort (cfg : VeryNotSticky.{u}) (C₀ : NNReal) : NNReal :=
  min (thickSegScale cfg C₀ / thickBodyLong cfg C₀) 1

/-- **The middle dimension `b'` of the thick presentation**, `min (δe / aW) 1`. -/
def thickPlankLong (cfg : VeryNotSticky.{u}) (C₀ : NNReal) : NNReal :=
  min (thickSegScale cfg C₀ / thickBodyShort cfg C₀) 1

theorem thickSegScale_pos (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    0 < thickSegScale cfg C₀ := by
  have hC : (0 : NNReal) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  exact div_pos (mul_pos (mul_pos (by norm_num) hC) cfg.hδ) (thickPlank_r₁_pos' cfg)

theorem thickBodyLong_pos (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    0 < thickBodyLong cfg C₀ :=
  lt_of_lt_of_le (thickBodyShort_pos cfg hC₀) (thickBodyShort_le_long cfg C₀)

theorem thickPlankShort_le_long (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    thickPlankShort cfg C₀ ≤ thickPlankLong cfg C₀ :=
  thickSegShort_le_long (thickBodyShort_pos cfg hC₀) (thickBodyShort_le_long cfg C₀)
    (thickSegScale cfg C₀)

theorem thickPlankLong_le_one (cfg : VeryNotSticky.{u}) (C₀ : NNReal) :
    thickPlankLong cfg C₀ ≤ 1 := min_le_right _ _

theorem thickPlankShort_pos (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    0 < thickPlankShort cfg C₀ :=
  thickSegShort_pos (thickBodyShort_pos cfg hC₀) (thickBodyShort_le_long cfg C₀)
    (thickSegScale_pos cfg hC₀)

/-! The four comparabilities. `cfg.hdims` gives `δ ≤ a ≤ b ≤ r₁`, and these are the only facts
about the configuration that enter. -/

theorem thickPlank_delta_le_b (cfg : VeryNotSticky.{u}) : cfg.δ ≤ cfg.b :=
  cfg.hdims.1.trans cfg.hdims.2.1

theorem thickPlank_b_le_r₁ (cfg : VeryNotSticky.{u}) : cfg.b ≤ cfg.r₁ := cfg.hdims.2.2

theorem thickPlank_a_le_r₁ (cfg : VeryNotSticky.{u}) : cfg.a ≤ cfg.r₁ :=
  cfg.hdims.2.1.trans cfg.hdims.2.2

/-- `δe / (C₀ x / r₁) = 4 δ / x` for `x ∈ {a, b}`. -/
theorem thickSegScale_div_eq (cfg : VeryNotSticky.{u}) {C₀ x : NNReal} (hC₀ : 1 ≤ C₀)
    (hx : 0 < x) : thickSegScale cfg C₀ / (C₀ * x / cfg.r₁) = 4 * cfg.δ / x := by
  have hC : (0 : NNReal) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hr : (0 : NNReal) < cfg.r₁ := thickPlank_r₁_pos' cfg
  rw [thickSegScale, ← NNReal.coe_inj]
  push_cast
  have hC' : ((C₀ : ℝ)) ≠ 0 := by positivity
  have hx' : ((x : ℝ)) ≠ 0 := by positivity
  have hr' : ((cfg.r₁ : ℝ)) ≠ 0 := by positivity
  field_simp

theorem four_mul_delta_le (cfg : VeryNotSticky.{u}) : cfg.δ ≤ 4 * cfg.δ :=
  le_mul_of_one_le_left bot_le (by norm_num)

theorem four_mul_le_four_mul_C₀ (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    (4 : NNReal) * cfg.δ ≤ 4 * C₀ * cfg.δ := by
  rw [mul_assoc]
  have h : cfg.δ ≤ C₀ * cfg.δ := le_mul_of_one_le_left bot_le hC₀
  gcongr

/-- The lower half of the short comparability, before the constant: `δ/b ≤ a'`. -/
theorem delta_div_b_le_thickPlankShort (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    cfg.δ / cfg.b ≤ thickPlankShort cfg C₀ := by
  have hb : (0 : NNReal) < cfg.b := cfg_b_pos cfg
  have hstep : 4 * cfg.δ / cfg.b ≤ thickSegScale cfg C₀ / thickBodyLong cfg C₀ := by
    rw [← thickSegScale_div_eq cfg hC₀ hb]
    have h1 : (0 : NNReal) < thickBodyLong cfg C₀ := thickBodyLong_pos cfg hC₀
    have h2 : thickBodyLong cfg C₀ ≤ C₀ * cfg.b / cfg.r₁ := thickBodyLong_le cfg C₀
    gcongr
  have hδb : cfg.δ / cfg.b ≤ 4 * cfg.δ / cfg.b := by
    have h : cfg.δ ≤ 4 * cfg.δ := four_mul_delta_le cfg
    gcongr
  rw [thickPlankShort]
  exact le_min (hδb.trans hstep) (div_le_one_of_le₀ (thickPlank_delta_le_b cfg) bot_le)

/-- The lower half of the middle comparability: `δ/a ≤ b'`. -/
theorem delta_div_a_le_thickPlankLong (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    cfg.δ / cfg.a ≤ thickPlankLong cfg C₀ := by
  have ha : (0 : NNReal) < cfg.a := cfg_a_pos cfg
  have hstep : 4 * cfg.δ / cfg.a ≤ thickSegScale cfg C₀ / thickBodyShort cfg C₀ := by
    rw [← thickSegScale_div_eq cfg hC₀ ha]
    have h1 : (0 : NNReal) < thickBodyShort cfg C₀ := thickBodyShort_pos cfg hC₀
    have h2 : thickBodyShort cfg C₀ ≤ C₀ * cfg.a / cfg.r₁ := thickBodyShort_le cfg C₀
    gcongr
  have hδa : cfg.δ / cfg.a ≤ 4 * cfg.δ / cfg.a := by
    have h : cfg.δ ≤ 4 * cfg.δ := four_mul_delta_le cfg
    gcongr
  rw [thickPlankLong]
  exact le_min (hδa.trans hstep) (div_le_one_of_le₀ cfg.hdims.1 bot_le)

/-- The upper half of the short comparability: `a' ≤ 4 C₀ δ / b`. -/
theorem thickPlankShort_le_const (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    thickPlankShort cfg C₀ ≤ 4 * C₀ * cfg.δ / cfg.b := by
  have hb : (0 : NNReal) < cfg.b := cfg_b_pos cfg
  rw [thickPlankShort]
  refine (min_le_left _ _).trans ?_
  rcases le_total (C₀ * cfg.b / cfg.r₁) (1 : NNReal) with hle | hle
  · rw [thickBodyLong, min_eq_left hle, thickSegScale_div_eq cfg hC₀ hb]
    have h : (4 : NNReal) * cfg.δ ≤ 4 * C₀ * cfg.δ := four_mul_le_four_mul_C₀ cfg hC₀
    gcongr
  · rw [thickBodyLong, min_eq_right hle, div_one, thickSegScale]
    have h : cfg.b ≤ cfg.r₁ := thickPlank_b_le_r₁ cfg
    gcongr

/-- The upper half of the middle comparability: `b' ≤ 4 C₀ δ / a`. -/
theorem thickPlankLong_le_const (cfg : VeryNotSticky.{u}) {C₀ : NNReal} (hC₀ : 1 ≤ C₀) :
    thickPlankLong cfg C₀ ≤ 4 * C₀ * cfg.δ / cfg.a := by
  have ha : (0 : NNReal) < cfg.a := cfg_a_pos cfg
  rw [thickPlankLong]
  refine (min_le_left _ _).trans ?_
  rcases le_total (C₀ * cfg.a / cfg.r₁) (1 : NNReal) with hle | hle
  · rw [thickBodyShort, min_eq_left hle, thickSegScale_div_eq cfg hC₀ ha]
    have h : (4 : NNReal) * cfg.δ ≤ 4 * C₀ * cfg.δ := four_mul_le_four_mul_C₀ cfg hC₀
    gcongr
  · rw [thickBodyShort, min_eq_right hle, div_one, thickSegScale]
    have h : cfg.a ≤ cfg.r₁ := thickPlank_a_le_r₁ cfg
    gcongr

/-! ### The four comparabilities in the shape `ThickPlankPresentation` states them

The structure states `short_lower`–`long_upper` in `ℝ`, at a constant `CP`; these are the
`ℝ≥0` bounds above, cast, at any `CP ≥ 4 C₀`. The constant is `δ`-free: it depends on the
comparison constant of (C4) and on nothing else. -/

theorem thickPlank_short_lower (cfg : VeryNotSticky.{u}) {C₀ CP : NNReal} (hC₀ : 1 ≤ C₀)
    (hCP : 1 ≤ CP) :
    (CP : ℝ)⁻¹ * ((cfg.δ : ℝ) / (cfg.b : ℝ)) ≤ ((thickPlankShort cfg C₀ : NNReal) : ℝ) := by
  have hmain : ((cfg.δ / cfg.b : NNReal) : ℝ) ≤ ((thickPlankShort cfg C₀ : NNReal) : ℝ) := by
    exact_mod_cast delta_div_b_le_thickPlankShort cfg hC₀
  rw [NNReal.coe_div] at hmain
  refine le_trans ?_ hmain
  have hCP1 : (1 : ℝ) ≤ (CP : ℝ) := by exact_mod_cast hCP
  have hinv : (CP : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hCP1
  have hnn : (0 : ℝ) ≤ (cfg.δ : ℝ) / (cfg.b : ℝ) := by positivity
  nlinarith

theorem thickPlank_long_lower (cfg : VeryNotSticky.{u}) {C₀ CP : NNReal} (hC₀ : 1 ≤ C₀)
    (hCP : 1 ≤ CP) :
    (CP : ℝ)⁻¹ * ((cfg.δ : ℝ) / (cfg.a : ℝ)) ≤ ((thickPlankLong cfg C₀ : NNReal) : ℝ) := by
  have hmain : ((cfg.δ / cfg.a : NNReal) : ℝ) ≤ ((thickPlankLong cfg C₀ : NNReal) : ℝ) := by
    exact_mod_cast delta_div_a_le_thickPlankLong cfg hC₀
  rw [NNReal.coe_div] at hmain
  refine le_trans ?_ hmain
  have hCP1 : (1 : ℝ) ≤ (CP : ℝ) := by exact_mod_cast hCP
  have hinv : (CP : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hCP1
  have hnn : (0 : ℝ) ≤ (cfg.δ : ℝ) / (cfg.a : ℝ) := by positivity
  nlinarith

theorem thickPlank_short_upper (cfg : VeryNotSticky.{u}) {C₀ CP : NNReal} (hC₀ : 1 ≤ C₀)
    (hCP : 4 * C₀ ≤ CP) :
    ((thickPlankShort cfg C₀ : NNReal) : ℝ) ≤ (CP : ℝ) * ((cfg.δ : ℝ) / (cfg.b : ℝ)) := by
  have hmain : ((thickPlankShort cfg C₀ : NNReal) : ℝ)
      ≤ ((4 * C₀ * cfg.δ / cfg.b : NNReal) : ℝ) := by
    exact_mod_cast thickPlankShort_le_const cfg hC₀
  refine hmain.trans ?_
  push_cast
  have hCP' : 4 * (C₀ : ℝ) ≤ (CP : ℝ) := by exact_mod_cast hCP
  have hnn : (0 : ℝ) ≤ (cfg.δ : ℝ) / (cfg.b : ℝ) := by positivity
  have : 4 * (C₀ : ℝ) * (cfg.δ : ℝ) / (cfg.b : ℝ)
      = (4 * (C₀ : ℝ)) * ((cfg.δ : ℝ) / (cfg.b : ℝ)) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_right hCP' hnn

theorem thickPlank_long_upper (cfg : VeryNotSticky.{u}) {C₀ CP : NNReal} (hC₀ : 1 ≤ C₀)
    (hCP : 4 * C₀ ≤ CP) :
    ((thickPlankLong cfg C₀ : NNReal) : ℝ) ≤ (CP : ℝ) * ((cfg.δ : ℝ) / (cfg.a : ℝ)) := by
  have hmain : ((thickPlankLong cfg C₀ : NNReal) : ℝ)
      ≤ ((4 * C₀ * cfg.δ / cfg.a : NNReal) : ℝ) := by
    exact_mod_cast thickPlankLong_le_const cfg hC₀
  refine hmain.trans ?_
  push_cast
  have hCP' : 4 * (C₀ : ℝ) ≤ (CP : ℝ) := by exact_mod_cast hCP
  have hnn : (0 : ℝ) ≤ (cfg.δ : ℝ) / (cfg.a : ℝ) := by positivity
  have : 4 * (C₀ : ℝ) * (cfg.δ : ℝ) / (cfg.a : ℝ)
      = (4 * (C₀ : ℝ)) * ((cfg.δ : ℝ) / (cfg.a : ℝ)) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_right hCP' hnn

/-! ### The assembly: fields 1–9 and 13 of `ThickPlankPresentation` -/

/-- The enclosure radius of `Kakeya.VeryNotSticky.plankWindowEnclosure` is the Section 6
window radius. -/
theorem coe_plankBallRadius : ((plankBallRadius : NNReal) : ℝ) = Plank.windowRadius := by
  rfl

/-- A plank of prescribed dimensions inside the window, for the indices off the block. The
structure field `Kakeya.VeryNotSticky.ThickPlankPresentation.P` is a total function on `bd.σ`,
while only the block carries geometry. -/
theorem exists_defaultWindowedPlank {a' b' : NNReal} (ha' : 0 < a') (hab' : a' ≤ b')
    (hb1' : b' ≤ 1) :
    ∃ P : Plank a' b' hab' hb1',
      (P.carrier : Set E₃) ⊆ closedBall (0 : E₃) (plankBallRadius : ℝ) := by
  obtain ⟨P, _hsub, hwin, _hbasis⟩ :=
    plankWindowEnclosure (C₀ := 1) (a := a') (b := b') (r₁ := 1) le_rfl zero_lt_one hab'
      (isAdmissiblePlankDimensions_self ha' hab' hb1')
      (isCompact_singleton (x := (0 : E₃))) (Set.singleton_nonempty (0 : E₃))
      (by simp) (EuclideanSpace.basisFun (Fin 3) ℝ)
      (by
        rintro x hx u hu
        rw [Set.mem_singleton_iff] at hx hu
        subst hx; subst hu
        simp)
  exact ⟨P, hwin⟩

/-- **G10a: the normalised plank model of a thick block.**

For a ball `B` and a body `W = Wb j`, there is one affine change of variables `L` — the
rescaling `L_B` of `Kakeya.VeryNotSticky.plankRescale` followed by the plank normalisation of
the enclosing plank of `L_B(W)` — and one family of shaded planks `P` of the *fixed* dimensions
`a' = Kakeya.VeryNotSticky.thickPlankShort`, `b' = Kakeya.VeryNotSticky.thickPlankLong`,
comparable to `δ/b` and `δ/a` at the `δ`-free constant `4 C₀`, such that

* every segment of the block has `L(Y_p) ⊆ P_p` (the enclosure, field `P`);
* every `P_p` lies in the window `B̄(0, 4)` (field `windowed`);
* the shading of `P_p` is the transported shading `L(Y_p^{shade})`.

This is fields 1–4 (through the two `def`s and the two order lemmas), 5–8 (the four
comparabilities, proved separately as
`Kakeya.VeryNotSticky.delta_div_b_le_thickPlankShort` and its three companions), 9 and 13.

**The route is not the one the docstrings advertise.** `Kakeya/DimensionThree/Plank/
NormalisedThickness.lean` and `…/Alignment.lean`, cited at `ThickCase.lean:2280` and
`ThickPlankInterface.lean:592`, do not exist. The machinery is
`Kakeya/DimensionThree/Plank/TubePlankNormalisation.lean`, and its packaged entry point
`Kakeya.Plank.exists_normalisedTubePlank` is *not* applicable here: it wants a `Tube`, the
`δ`-neighbourhood of a **unit** segment, and a rescaled `BallData` segment is not one — after
`L_B` it has axial extent up to `2`, so no tube of radius `∼ δ/r₁` contains it. What is
applicable, and is used here, are that file's two estimates
`Kakeya.Plank.abs_inner_le_thin` and `Kakeya.Plank.abs_inner_le_mid`, which are stated for an
arbitrary residue and need only the axis splitting of
`Kakeya.VeryNotSticky.norm_sub_axis_le_of_hasThicknesses`. -/
theorem exists_thickPlankNormalisation {cfg : VeryNotSticky.{u}} (bd : BallData cfg)
    {B : bd.bι} (hB : B ∈ bd.bs) {j : bd.ω} (hj : j ∈ bd.bodies B) :
    ∃ (L : E₃ ≃ᵃ[ℝ] E₃)
      (P : bd.σ → ShadedPlank (thickPlankShort cfg bd.C₀) (thickPlankLong cfg bd.C₀)
        (thickPlankShort_le_long cfg bd.hC₀) (thickPlankLong_le_one cfg bd.C₀)),
      (∀ p ∈ (bd.segs B).filter (fun q => bd.blk q = j),
        (P p).shade = L '' (bd.Y p).shade) ∧
      (∀ p, ((P p).carrier : Set E₃) ⊆ closedBall (0 : E₃) (Plank.windowRadius : ℝ)) ∧
      (∀ p ∈ (bd.segs B).filter (fun q => bd.blk q = j),
        L '' ((bd.Y p).carrier : Set E₃) ⊆ ((P p).carrier : Set E₃)) ∧
      ((thickPlankBodyFloor bd.C₀ : NNReal) : ENNReal) ≤
        volume (L '' ((bd.Wb j).carrier : Set E₃)) ∧
      L '' ((bd.Wb j).carrier : Set E₃) ⊆
        closedBall (0 : E₃) (Plank.windowRadius : ℝ) := by
  classical
  have hr₁ : (0 : ℝ) < (cfg.r₁ : ℝ) := thickPlank_r₁_pos cfg
  have haWpos : 0 < thickBodyShort cfg bd.C₀ := thickBodyShort_pos cfg bd.hC₀
  set L₁ : E₃ ≃ᵃ[ℝ] E₃ := plankRescale (bd.ctr B) hr₁.ne' with hL₁
  obtain ⟨W, hWsub, _hWwin⟩ := exists_thickBodyPlank bd hB hj
  have hκ : 0 < thickNormKappa := thickNormKappa_pos
  obtain ⟨f, J, g, hJ0, hnorm, hvolf, himg⟩ := exists_thickNormalisation haWpos W
  obtain ⟨F, hF⟩ := Plank.exists_affineEquiv_of_isPlankNormalisation haWpos W hκ hnorm
  set L : E₃ ≃ᵃ[ℝ] E₃ := L₁.trans F with hL
  have hLapp : ∀ x : E₃, L x = f (L₁ x) := by
    intro x
    rw [hL]
    simpa using hF (L₁ x)
  have hLimage : ∀ S : Set E₃, L '' S = f '' (L₁ '' S) := by
    intro S
    rw [Set.image_image]
    exact Set.image_congr' hLapp
  -- the rescaled segment bodies
  set Kp : bd.σ → ConvexSpaceBody E₃ :=
    fun p => ((bd.Y p).toConvexSpaceBody).plankRescale (bd.ctr B) hr₁.ne' with hKp
  have hKpcar : ∀ p, ((Kp p).carrier : Set E₃) = L₁ '' ((bd.Y p).carrier : Set E₃) := by
    intro p
    rw [hKp, hL₁]
    simp [ConvexSpaceBody.plankRescale]
  -- the per-index plank
  have hchoice : ∀ p : bd.σ, ∃ Q : Plank (thickPlankShort cfg bd.C₀) (thickPlankLong cfg bd.C₀)
      (thickPlankShort_le_long cfg bd.hC₀) (thickPlankLong_le_one cfg bd.C₀),
      ((Q.carrier : Set E₃) ⊆ closedBall (0 : E₃) (plankBallRadius : ℝ)) ∧
      (p ∈ (bd.segs B).filter (fun q => bd.blk q = j) →
        f '' ((Kp p).carrier : Set E₃) ⊆ (Q.carrier : Set E₃)) := by
    intro p
    by_cases hp : p ∈ (bd.segs B).filter (fun q => bd.blk q = j)
    · rw [Finset.mem_filter] at hp
      obtain ⟨hpB, hpj⟩ := hp
      -- the segment sits inside the body, hence inside the enclosing plank
      have hYW : ((bd.Y p).carrier : Set E₃) ⊆ ((bd.Wb j).carrier : Set E₃) := by
        have h := bd.segs_le B hB p hpB
        rw [hpj] at h
        exact h
      have hKW : ((Kp p).carrier : Set E₃) ⊆ (W.carrier : Set E₃) := by
        rw [hKpcar p]
        exact Set.Subset.trans (Set.image_mono hYW) hWsub
      -- the capsule bound
      have hthick' : HasThicknesses ((Kp p).carrier : Set E₃) bd.C₀
          ![(1 : ℝ), (cfg.δ : ℝ) / (cfg.r₁ : ℝ), (cfg.δ : ℝ) / (cfg.r₁ : ℝ)] := by
        rw [hKpcar p, hL₁]
        exact hasThicknesses_plankRescale_image (bd.ctr B) bd.hC₀ hr₁
          (bd.Y p).isCompact'.isBounded (bd.segs_thickness B hB p hpB)
      have hcap : ∀ x ∈ ((Kp p).carrier : Set E₃), ∀ u ∈ ((Kp p).carrier : Set E₃),
          ‖(x - u) - ((bodyFrame (Kp p)).repr (x - u) 2) • (bodyFrame (Kp p) 2)‖
            ≤ ((thickSegScale cfg bd.C₀ : NNReal) : ℝ) := by
        intro x hx u hu
        refine (norm_sub_axis_le_of_hasThicknesses (Kp p) hthick' hx hu).trans ?_
        rw [thickSegScale]
        push_cast
        rw [mul_div_assoc]
      obtain ⟨Q, hQsub, hQwin⟩ :=
        exists_thickSegmentPlank haWpos W hκ hnorm himg (Kp p) hKW
          (thickSegScale_pos cfg bd.hC₀) hcap
      exact ⟨Q, hQwin, fun _ => hQsub⟩
    · obtain ⟨Q, hQ⟩ := exists_defaultWindowedPlank (thickPlankShort_pos cfg bd.hC₀)
        (thickPlankShort_le_long cfg bd.hC₀) (thickPlankLong_le_one cfg bd.C₀)
      exact ⟨Q, hQ, fun h => absurd h hp⟩
  choose Q hQwin hQsub using hchoice
  -- the shaded planks
  have hLemb : MeasurableEmbedding L :=
    L.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding
  have hshade : ∀ p, L '' ((bd.Y p).shade) ⊆ (Q p).carrier ∨
      p ∉ (bd.segs B).filter (fun q => bd.blk q = j) := by
    intro p
    by_cases hp : p ∈ (bd.segs B).filter (fun q => bd.blk q = j)
    · left
      have h1 : L '' ((bd.Y p).shade) ⊆ L '' ((bd.Y p).carrier : Set E₃) :=
        Set.image_mono (bd.Y p).shade_subset
      refine h1.trans ?_
      rw [hLimage, ← hKpcar p]
      exact hQsub p hp
    · right; exact hp
  set Psh : bd.σ → ShadedPlank (thickPlankShort cfg bd.C₀) (thickPlankLong cfg bd.C₀)
      (thickPlankShort_le_long cfg bd.hC₀) (thickPlankLong_le_one cfg bd.C₀) :=
    fun p =>
      { toPrism3D := Q p
        shade := if p ∈ (bd.segs B).filter (fun q => bd.blk q = j)
          then L '' ((bd.Y p).shade) else ∅
        measurableSet_shade := by
          by_cases hp : p ∈ (bd.segs B).filter (fun q => bd.blk q = j)
          · rw [if_pos hp]
            exact hLemb.measurableSet_image' (bd.Y p).measurableSet_shade
          · rw [if_neg hp]; exact MeasurableSet.empty
        shade_subset := by
          by_cases hp : p ∈ (bd.segs B).filter (fun q => bd.blk q = j)
          · rw [if_pos hp]
            rcases hshade p with h | h
            · exact h
            · exact absurd hp h
          · rw [if_neg hp]; exact Set.empty_subset _ } with hPsh
  refine ⟨L, Psh, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hPsh]
    exact if_pos hp
  · intro p
    refine (hQwin p).trans ?_
    rw [coe_plankBallRadius]
  · intro p hp
    rw [hLimage, ← hKpcar p]
    exact hQsub p hp
  · -- the `δ`-free volume floor of the normalised body, row G10e's `hLW`
    have hWpos : (0 : NNReal) < cfg.r₁ := thickPlank_r₁_pos' cfg
    have hapos : (0 : NNReal) < cfg.a := cfg_a_pos cfg
    have hbpos : (0 : NNReal) < cfg.b := cfg_b_pos cfg
    have hCpos : (0 : NNReal) < bd.C₀ := lt_of_lt_of_le zero_lt_one bd.hC₀
    have hJeq : J * (thickBodyShort cfg bd.C₀ * thickBodyLong cfg bd.C₀)
        = Real.toNNReal thickNormKappa ^ (3 : ℕ) :=
      Plank.jacobian_eq haWpos W hκ hnorm hvolf
    have hY0 : (0 : NNReal) < bd.C₀ ^ (2 : ℕ) * cfg.a * cfg.b / cfg.r₁ ^ (2 : ℕ) := by
      apply div_pos _ (by positivity)
      positivity
    have hXY : thickBodyShort cfg bd.C₀ * thickBodyLong cfg bd.C₀
        ≤ bd.C₀ ^ (2 : ℕ) * cfg.a * cfg.b / cfg.r₁ ^ (2 : ℕ) := by
      have h1 : thickBodyShort cfg bd.C₀ ≤ bd.C₀ * cfg.a / cfg.r₁ := thickBodyShort_le cfg bd.C₀
      have h2 : thickBodyLong cfg bd.C₀ ≤ bd.C₀ * cfg.b / cfg.r₁ := thickBodyLong_le cfg bd.C₀
      calc thickBodyShort cfg bd.C₀ * thickBodyLong cfg bd.C₀
          ≤ (bd.C₀ * cfg.a / cfg.r₁) * (bd.C₀ * cfg.b / cfg.r₁) := mul_le_mul' h1 h2
        _ = bd.C₀ ^ (2 : ℕ) * cfg.a * cfg.b / cfg.r₁ ^ (2 : ℕ) := by
            rw [← NNReal.coe_inj]
            push_cast
            field_simp
    have hJlow : Real.toNNReal thickNormKappa ^ (3 : ℕ)
        / (bd.C₀ ^ (2 : ℕ) * cfg.a * cfg.b / cfg.r₁ ^ (2 : ℕ)) ≤ J := by
      rw [div_le_iff₀ hY0, ← hJeq]
      gcongr
    have hstep : (Real.toNNReal thickNormKappa ^ (3 : ℕ)
          / (bd.C₀ ^ (2 : ℕ) * cfg.a * cfg.b / cfg.r₁ ^ (2 : ℕ)))
        * cfg.r₁⁻¹ ^ (3 : ℕ) * ((6 * bd.C₀ ^ (3 : ℕ))⁻¹ * (cfg.r₁ * cfg.b * cfg.a))
        = thickPlankBodyFloor bd.C₀ := by
      rw [thickPlankBodyFloor, ← NNReal.coe_inj]
      push_cast
      field_simp
    have hfinalN : thickPlankBodyFloor bd.C₀
        ≤ J * cfg.r₁⁻¹ ^ (3 : ℕ) * ((6 * bd.C₀ ^ (3 : ℕ))⁻¹ * (cfg.r₁ * cfg.b * cfg.a)) := by
      rw [← hstep]
      gcongr
    -- transfer to `[0, ∞]`
    have hofReal : ENNReal.ofReal (((cfg.r₁ : ℝ))⁻¹ ^ 3)
        = (((cfg.r₁⁻¹ ^ (3 : ℕ) : NNReal)) : ENNReal) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
    have hWlow : (((6 * bd.C₀ ^ (3 : ℕ))⁻¹ * (cfg.r₁ * cfg.b * cfg.a) : NNReal) : ENNReal)
        ≤ volume ((bd.Wb j).carrier : Set E₃) := by
      have h := (thickBodyVol cfg bd hB hj).1
      have hne : (6 * bd.C₀ ^ (3 : ℕ) : NNReal) ≠ 0 := by positivity
      rw [ENNReal.coe_mul, ENNReal.coe_inv hne]
      simpa using h
    calc ((thickPlankBodyFloor bd.C₀ : NNReal) : ENNReal)
        ≤ (((J * cfg.r₁⁻¹ ^ (3 : ℕ)
              * ((6 * bd.C₀ ^ (3 : ℕ))⁻¹ * (cfg.r₁ * cfg.b * cfg.a)) : NNReal)) : ENNReal) := by
          exact_mod_cast hfinalN
      _ = (J : ENNReal) * (((cfg.r₁⁻¹ ^ (3 : ℕ) : NNReal)) : ENNReal)
            * (((6 * bd.C₀ ^ (3 : ℕ))⁻¹ * (cfg.r₁ * cfg.b * cfg.a) : NNReal) : ENNReal) := by
          push_cast
          ring
      _ ≤ (J : ENNReal) * (((cfg.r₁⁻¹ ^ (3 : ℕ) : NNReal)) : ENNReal)
            * volume ((bd.Wb j).carrier : Set E₃) := by gcongr
      _ = (J : ENNReal) * (ENNReal.ofReal (((cfg.r₁ : ℝ))⁻¹ ^ 3)
            * volume ((bd.Wb j).carrier : Set E₃)) := by
          rw [hofReal]; ring
      _ = (J : ENNReal) * volume (L₁ '' ((bd.Wb j).carrier : Set E₃)) := by
          rw [hL₁, volume_plankRescale_image (bd.ctr B) hr₁]
      _ = volume (f '' (L₁ '' ((bd.Wb j).carrier : Set E₃))) := (hvolf _).symm
      _ = volume (L '' ((bd.Wb j).carrier : Set E₃)) := by rw [hLimage]
  · -- `L(W_j)` lies in the Section 6 window: row G10c's `hLwin`
    rw [hLimage]
    refine Set.Subset.trans (Set.image_mono hWsub) ?_
    refine himg.trans ?_
    refine closedBall_subset_closedBall ?_
    rw [Plank.windowRadius]
    norm_num

/-- Field `windowed`: a family of shaded planks all of whose carriers lie in the window is a
`Kakeya.Plank.IsWindowedFamily` over every index set, in particular over the selected
subfamily of `Kakeya.VeryNotSticky.ThickPlankPresentation.sel`. -/
theorem isWindowedFamily_of_carrier_subset {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    {ι : Type*} (t : Finset ι) (P : ι → ShadedPlank a b hab hb1)
    (h : ∀ p, ((P p).carrier : Set E₃) ⊆ closedBall (0 : E₃) (Plank.windowRadius : ℝ)) :
    Plank.IsWindowedFamily t (fun p => (P p).toPrism3D) := fun i _ => h i

end Kakeya.VeryNotSticky

end

end
