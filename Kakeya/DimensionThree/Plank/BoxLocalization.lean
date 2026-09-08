/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabIntersection
public import Kakeya.DimensionThree.Plank.RepresentativeFibres
public import Kakeya.Mathlib.MeasureTheory.BoundedOverlap

/-!
# Tangential slab-box grids for GWZ Lemma 6.13

This module contains the shift-parametric slab-box grid and the tangentiality estimate it supports:
a plank meeting the *middle half* of a grid box is tangential to that box
(`Plank.comparableScalars_of_mem_halfBox`).  The middle-half mass capture built on top of it lives
in `Kakeya.DimensionThree.Plank.BoxMassCapture`, and the representative selection and slab-mass
packing layer lives in `Kakeya.DimensionThree.Plank.SlabAssignment`.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}
/-! ## The slab-box grid (`def:boxLayerAPI`, `lem:plankBoxIntersectionIsSlabAPI`,
`lem:plankSlabAngleComparableAPI`)

The grid consists of `θb' × b' × b'` boxes aligned with the orthonormal frame of the slab `S`,
in the shift-parametric form `Plank.shiftedSlabBox S b' t k`.  There is a single implementation:
the zero shift `t = 0` is one of the eight shifts of `Plank.gridShiftSet` and needs no separate
grid, and the Lemma 6.13 route never uses exact tiling of `S` by an unshifted grid. -/

open Classical in
/-- The index window **scaled by `M`**: multi-indices in `[-M⌈1/b'⌉, M⌈1/b'⌉]³`, large enough that
every point of the `M`-dilation of the slab `S` rounds to a box in the family.

The scaling is what reconciles the tangential-box layer with the slab layer.  The slab
decomposition delivers planks in `Plank.inSlabFamilyC Cset Cang`, i.e. inside the
`Cset`-*dilation* of `S`, not inside `S` itself, so `M = ⌈Cset⌉` is what restores coverage; `M` is
fixed before the finite configuration, exactly as `Cset` is. -/
noncomputable def slabBoxIndexFor (b' : ℝ≥0) (M : ℕ) : Finset (Fin 3 → ℤ) :=
  Finset.Icc (fun _ => -((M * ⌈(1 : ℝ) / (b' : ℝ)⌉₊ : ℕ) : ℤ))
    (fun _ => ((M * ⌈(1 : ℝ) / (b' : ℝ)⌉₊ : ℕ) : ℤ))

/-- Per-coordinate rounding bound: for `w > 0`, rounding `c/(2w)` places `c` within `w`
of the nearest grid point `2·w·round(c/(2w))`. -/
private theorem round_mul_bound (c : ℝ) {w : ℝ} (hw : 0 < w) :
    |c - 2 * w * (round (c / (2 * w)) : ℝ)| ≤ w := by
  set t := c / (2 * w) with ht
  have hc_eq : c = 2 * w * t := by
    dsimp [t]; field_simp [hw.ne.symm]
  have hpos2w : 0 < 2 * w := by nlinarith
  calc
    |c - 2 * w * (round (c / (2 * w)) : ℝ)| = |c - 2 * w * (round t : ℝ)| := by simp [ht]
    _ = |2 * w * t - 2 * w * (round t : ℝ)| := by rw [hc_eq]
    _ = |2 * w * (t - (round t : ℝ))| := by ring_nf
    _ = |2 * w| * |t - (round t : ℝ)| := by rw [abs_mul]
    _ = (2 * w) * |t - (round t : ℝ)| := by rw [abs_of_pos hpos2w]
    _ ≤ (2 * w) * (1 / 2) := by
      gcongr
      exact abs_sub_round t
    _ = w := by ring

/-- The box half-widths `(θb', b', b')` are `b'` times the slab half-widths `(θ, 1, 1)`. -/
private lemma boxWidth_eq_mul_slabWidth (θ b' : ℝ≥0) (j : Fin 3) : -- (extracted by Fuse golfer)
    ((![θ * b', b', b'] j : ℝ≥0) : ℝ) = (b' : ℝ) * ((![θ, 1, 1] j : ℝ≥0) : ℝ) := by
  fin_cases j <;> simp [mul_comm]

/-- A real bound `|n| < k + 1` on an integer `n` is an integer bound `|n| ≤ k`. -/
private lemma int_abs_le_of_real_abs_lt_succ {n : ℤ} {k : ℕ} (h : |(n : ℝ)| < (k : ℝ) + 1) :
    |n| ≤ (k : ℤ) := by
  have h_abs_eq : |(n : ℝ)| = (|n| : ℝ) := by simp
  rw [h_abs_eq] at h
  have h' : (|n| : ℤ) ≤ (k : ℤ) := by
    by_contra! hc
    have : (k : ℤ) < |n| := hc
    have h' : (k : ℝ) < (|n| : ℝ) := by exact_mod_cast this
    have : (|n| : ℝ) ≥ (k : ℝ) + 1 := by
      have : (|n| : ℤ) ≥ (k : ℤ) + 1 := by omega
      exact_mod_cast this
    linarith
  exact h'

/-! ## Shifted slab-box grids and box tangentiality (`lem:tangBox*`)

The grid is parametrised by a shift `t ∈ gridShiftSet = {0, ½}³`, chosen independently in each of
the three slab-frame directions.  Eight shifts are what the argument needs: the three box
half-widths `(θb, b, b)` are matched against the three plank half-widths `(a, b, 1)` direction by
direction, and only the middle direction is at risk, where plank and box have the same half-width
`b`.  There the two candidate cells containing a point are offset by half a cell, so one of them
always meets the plank's extent in at least half a cell.  The choice is per-coordinate, so the
shift set is the full product `{0, ½}³` and cannot be reduced.

A pair `(i, k)` is *tangential* (with constant `cTan`) when `|Pᵢ ∩ Q_k| ∼_{cTan} a b²`. -/

open Classical in
/-- The absolute finite set of grid shifts `K_sh = {0, ½}³` (as maps `Fin 3 → ℝ`). -/
noncomputable def gridShiftSet : Finset (Fin 3 → ℝ) :=
  Fintype.piFinset (fun _ : Fin 3 => ({0, 1 / 2} : Finset ℝ))

/-- The center of the shifted grid box: the base grid center translated by `t` (in units of one
box cell) along the slab frame. -/
noncomputable def shiftedSlabBoxCenter {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (b' : ℝ≥0)
    (t : Fin 3 → ℝ) (k : Fin 3 → ℤ) : EuclideanSpace ℝ (Fin 3) :=
  S.center + ∑ i : Fin 3,
    ((2 : ℝ) * ((![θ * b', b', b'] i : ℝ≥0) : ℝ) * ((k i : ℝ) + t i)) • S.basis i

/-- The shifted `θb' × b' × b'` grid box at lattice index `k` and shift `t`, aligned with `S`. -/
noncomputable def shiftedSlabBox {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (b' : ℝ≥0)
    (t : Fin 3 → ℝ) (k : Fin 3 → ℤ) : ThetaBox θ b' hθ1 where
  toPrismNDim := PrismNDim.mk' (shiftedSlabBoxCenter S b' t k) S.basis ![θ * b', b', b']
  thicknesses_eq := PrismNDim.thicknesses_mk' _ _ _

open Classical in
/-- The shifted round index: for each coordinate, round (c/(2w) - t_j) instead of c/(2w). -/
noncomputable def shiftedSlabRoundIndex {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (b' : ℝ≥0)
    (t : Fin 3 → ℝ) (x : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℤ :=
  fun j => round (S.basis.repr (x -ᵥ S.center) j / (2 * ((![θ * b', b', b'] j : ℝ≥0) : ℝ)) - t j)

/-- Helper: `|t_j| ≤ 1/2` when `t ∈ gridShiftSet`. -/
private lemma abs_t_j_le_half {t : Fin 3 → ℝ} (ht : t ∈ gridShiftSet) (j : Fin 3) :
    |t j| ≤ 1/2 := by
  have hmem : ∀ a : Fin 3, t a ∈ ({0, 1/2} : Finset ℝ) := by
    simpa [gridShiftSet, Fintype.mem_piFinset] using ht
  have hmem' : t j = 0 ∨ t j = 1/2 := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hmem j
  rcases hmem' with (h | h)
  · simp [h]
  · rw [h]; norm_num

/-- Coordinate of the shifted slab box center (analogous to `slabBoxCenter_coord`). -/
private lemma shiftedSlabBoxCenter_coord {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (b' : ℝ≥0)
    (t : Fin 3 → ℝ) (k : Fin 3 → ℤ) (j : Fin 3) :
    S.basis.repr (shiftedSlabBoxCenter S b' t k -ᵥ S.center) j
      = 2 * ((![θ * b', b', b'] j : ℝ≥0) : ℝ) * ((k j : ℝ) + t j) := by
  have hv : shiftedSlabBoxCenter S b' t k -ᵥ S.center
      = ∑ i : Fin 3, ((2 : ℝ) * ((![θ * b', b', b'] i : ℝ≥0) : ℝ) * ((k i : ℝ) + t i)) • S.basis
          i := by
    simp [shiftedSlabBoxCenter, vsub_eq_sub, add_sub_cancel_left]
  have hortho : ∀ i : Fin 3,
      inner ℝ (S.basis j) (S.basis i) = (if j = i then (1 : ℝ) else 0) :=
    fun i => orthonormal_iff_ite.mp S.basis.orthonormal j i
  rw [S.basis.repr_apply_apply, hv, inner_sum]
  simp [real_inner_smul_right, hortho, mul_ite, mul_one, mul_zero]

/-- Frame coordinate of a point measured from a shifted slab-box center, in terms of the
coordinate measured from the slab center. -/
private lemma repr_vsub_shiftedSlabBoxCenter {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (b' : ℝ≥0)
    (t : Fin 3 → ℝ) (k : Fin 3 → ℤ) (x : EuclideanSpace ℝ (Fin 3)) -- (extracted by Fuse golfer)
    (j : Fin 3) :
    S.basis.repr (x -ᵥ shiftedSlabBoxCenter S b' t k) j
      = S.basis.repr (x -ᵥ S.center) j
        - 2 * ((![θ * b', b', b'] j : ℝ≥0) : ℝ) * ((k j : ℝ) + t j) := by
  rw [← vsub_sub_vsub_cancel_right x (shiftedSlabBoxCenter S b' t k) S.center, map_sub]
  change S.basis.repr (x -ᵥ S.center) j
      - S.basis.repr (shiftedSlabBoxCenter S b' t k -ᵥ S.center) j = _
  rw [shiftedSlabBoxCenter_coord]

/-- Coordinatewise bound for a point of the `Cset`-dilation of a slab: each frame coordinate is
at most `Cset` times the corresponding slab half-width. -/
private lemma abs_repr_le_of_mem_dilation {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) {Cset : ℝ≥0}
    {x : EuclideanSpace ℝ (Fin 3)} -- (extracted by Fuse golfer)
    (hx : x ∈ ((S.toPrismNDim.dilation Cset).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (j : Fin 3) :
    |S.basis.repr (x -ᵥ S.center) j| ≤ (Cset : ℝ) * ((![θ, 1, 1] j : ℝ≥0) : ℝ) := by
  have hmem := (PrismNDim.mem_carrier_iff (S.toPrismNDim.dilation Cset) (x := x)).mp hx j
  simpa only [PrismNDim.dilation_center, PrismNDim.dilation_basis,
    PrismNDim.dilation_thicknesses, Prism3D.thicknesses_eq S, NNReal.coe_mul] using hmem

/-- Index membership for a point of the `Cset`-dilated slab, in the `M`-scaled window.

Public because `Plank.exists_shift_mem_halfSlabBox` places the round index in the window. -/
lemma shiftedSlabRoundIndex_mem_dilation {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1)
    {b' : ℝ≥0} (hb' : 0 < b') (_hb'1 : b' ≤ 1) {t : Fin 3 → ℝ} (ht : t ∈ gridShiftSet)
    {Cset : ℝ≥0} (hCset : 1 ≤ Cset) {M : ℕ} (hM : (Cset : ℝ) ≤ (M : ℝ))
    {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ((S.toPrismNDim.dilation Cset).carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    shiftedSlabRoundIndex S b' t x ∈ slabBoxIndexFor b' M := by
  rw [slabBoxIndexFor, Finset.mem_Icc]
  set K : ℕ := ⌈(1 : ℝ) / (b' : ℝ)⌉₊ with hK
  have hb'pos : (0 : ℝ) < (b' : ℝ) := by exact_mod_cast hb'
  have hKb : (1 : ℝ) ≤ (K : ℝ) * (b' : ℝ) := (div_le_iff₀ hb'pos).mp (Nat.le_ceil _)
  clear_value K
  clear hK
  have key : (Cset : ℝ) < 2 * ((M : ℝ) * ((K : ℝ) * (b' : ℝ))) := by
    have hCpos : (0 : ℝ) < (Cset : ℝ) := lt_of_lt_of_le one_pos (by exact_mod_cast hCset)
    linarith only [hCpos, mul_le_mul hM hKb zero_le_one (Nat.cast_nonneg M)]
  -- For each coordinate j, show |shiftedSlabRoundIndex S b' t x j| ≤ ((M * K : ℕ) : ℤ)
  have h_bound : ∀ j : Fin 3, |shiftedSlabRoundIndex S b' t x j| ≤ ((M * K : ℕ) : ℤ) := by
    intro j
    have habs : |t j| ≤ 1 / 2 := abs_t_j_le_half ht j
    have htj : t j = 0 ∨ t j = 1 / 2 := by
      simp only [gridShiftSet, Fintype.mem_piFinset, Finset.mem_insert,
        Finset.mem_singleton] at ht
      exact ht j
    set c := S.basis.repr (x -ᵥ S.center) j with hc
    set w := ((![θ * b', b', b'] j : ℝ≥0) : ℝ) with hw
    set thk := ((![θ, 1, 1] j : ℝ≥0) : ℝ) with hthk
    have hc_bound : |c| ≤ (Cset : ℝ) * thk := abs_repr_le_of_mem_dilation S hx j
    have h_w_eq : w = (b' : ℝ) * thk := boxWidth_eq_mul_slabWidth θ b' j
    have hwnn : (0 : ℝ) ≤ w := by rw [hw]; exact NNReal.coe_nonneg _
    rw [show shiftedSlabRoundIndex S b' t x j = round (c / (2 * w) - t j) from rfl]
    -- from here on the argument is pure real arithmetic in `c`, `w`, `thk`
    clear_value c w thk
    clear hc hw hthk hx
    rcases eq_or_lt_of_le hwnn with hw0 | hwpos
    · -- `w = 0`, so `c / (2 * w) = 0` and the index is `round (-t j) = 0`
      have hzero : round (c / (2 * w) - t j) = 0 := by
        rcases htj with h | h <;> rw [← hw0, h] <;> simp [round_neg_two_inv]
      rw [hzero, abs_zero]
      exact Int.natCast_nonneg _
    · have hthk_pos : 0 < thk := by
        rw [h_w_eq] at hwpos
        exact pos_of_mul_pos_right hwpos hb'pos.le
      have h2w : (0 : ℝ) < 2 * w := by linarith only [hwpos]
      refine int_abs_le_of_real_abs_lt_succ ?_
      have h_real_bound : |(round (c / (2 * w) - t j) : ℝ)| ≤ |c| / (2 * w) + 1 := by
        have h5 : |c / (2 * w)| = |c| / (2 * w) := by rw [abs_div, abs_of_pos h2w]
        linarith only [habs, h5, abs_sub_round (c / (2 * w) - t j),
          abs_sub_abs_le_abs_sub ((round (c / (2 * w) - t j) : ℝ)) (c / (2 * w) - t j),
          abs_sub_comm ((round (c / (2 * w) - t j) : ℝ)) (c / (2 * w) - t j),
          abs_sub (c / (2 * w)) (t j)]
      have h_ineq : |c| / (2 * w) < ((M * K : ℕ) : ℝ) := by
        rw [div_lt_iff₀ h2w, h_w_eq, Nat.cast_mul]
        linarith only [hc_bound, mul_lt_mul_of_pos_right key hthk_pos]
      linarith only [h_real_bound, h_ineq]
  exact ⟨fun j => (abs_le.mp (h_bound j)).1, fun j => (abs_le.mp (h_bound j)).2⟩

/-- Each grid box has volume `8 θ b'³` (a `θb' × b' × b'` prism); the shift does not change it. -/
theorem shiftedSlabBox_volume {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (b' : ℝ≥0)
    (t : Fin 3 → ℝ) (k : Fin 3 → ℤ) :
    volume (shiftedSlabBox S b' t k).carrier = 8 * (θ : ENNReal) * b' * b' * b' := by
  rw [Prism3D.volume_carrier (shiftedSlabBox S b' t k)]
  simp [ENNReal.coe_mul, mul_assoc]

/-- Coordinate characterisation of membership in a shifted grid box, at an *arbitrary* lattice
index `k` (as opposed to the rounded index used by the coverage lemmas). -/
theorem mem_shiftedSlabBox_iff {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (b' : ℝ≥0)
    (t : Fin 3 → ℝ) (k : Fin 3 → ℤ) (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ ((shiftedSlabBox S b' t k).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ↔ ∀ j : Fin 3,
          |S.basis.repr (x -ᵥ S.center) j
              - 2 * ((![θ * b', b', b'] j : ℝ≥0) : ℝ) * ((k j : ℝ) + t j)|
            ≤ ((![θ * b', b', b'] j : ℝ≥0) : ℝ) := by
  rw [PrismNDim.mem_carrier_iff]
  refine forall_congr' fun j => ?_
  change |S.basis.repr (x -ᵥ shiftedSlabBoxCenter S b' t k) j|
      ≤ ((![θ * b', b', b'] j : ℝ≥0) : ℝ) ↔ _
  rw [repr_vsub_shiftedSlabBoxCenter]

/-- Every half-width of a `θb' × b' × b'` box is strictly positive. -/
private lemma coe_boxWidth_pos {θ b' : ℝ≥0} (hθ : 0 < θ) (hb' : 0 < b') (j : Fin 3) :
    (0 : ℝ) < ((![θ * b', b', b'] j : ℝ≥0) : ℝ) := by -- (extracted by Fuse golfer)
  have hb'R : (0 : ℝ) < (b' : ℝ) := by exact_mod_cast hb'
  have hθR : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ
  fin_cases j <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Fin.reduceFinMk, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, NNReal.coe_mul,
      NNReal.coe_pos, gt_iff_lt] <;>
    positivity

/-- **Unconditional nearest-box membership.**  When all three half-widths are positive
(`0 < θ`, `0 < b'`), *every* point of `ℝ³` lies in the shifted grid box at its own rounded index —
the point need not lie in `S` or in any dilation of it.  This is what the covering-fraction
construction consumes, where the sampled points sit on the long axis of a representative prism and
are not confined to `S`. -/
theorem mem_shiftedSlabBox_shiftedSlabRoundIndex {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1)
    {b' : ℝ≥0} (hb' : 0 < b') (hθ : 0 < θ) (t : Fin 3 → ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ ((shiftedSlabBox S b' t (shiftedSlabRoundIndex S b' t x)).carrier :
      Set (EuclideanSpace ℝ (Fin 3))) := by
  rw [mem_shiftedSlabBox_iff]
  intro j
  set w := ((![θ * b', b', b'] j : ℝ≥0) : ℝ) with hw
  set c := S.basis.repr (x -ᵥ S.center) j with hc
  have hwpos : 0 < w := coe_boxWidth_pos hθ hb' j
  rw [show ((shiftedSlabRoundIndex S b' t x j : ℤ) : ℝ) = round (c / (2 * w) - t j) from rfl,
    show c - 2 * w * ((round (c / (2 * w) - t j) : ℝ) + t j)
        = (c - 2 * w * t j) - 2 * w * (round ((c - 2 * w * t j) / (2 * w)) : ℝ) from by
      rw [sub_div, mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero hwpos.ne')]
      ring]
  exact round_mul_bound (c - 2 * w * t j) hwpos

open Classical in
/-- **Pointwise overlap of one fixed shift is at most `8`.** For a single fixed shift `t`, each
point lies in at most `2³ = 8` of the grid boxes `shiftedSlabBox S b' t k`.

In each coordinate `j`, membership forces `k j` into the closed interval `[u j - 1/2, u j + 1/2]`
of length `1`, which contains at most two integers.  The bound is uniform in `x`, `t`, `D` and the
scale — the exact property the fixed-shift additivity estimate needs. -/
private lemma card_filter_mem_shiftedSlabBox_le {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) {b' : ℝ≥0}
    (hb' : 0 < b') (hθ : 0 < θ) (t : Fin 3 → ℝ) (D : Finset (Fin 3 → ℤ))
    (x : EuclideanSpace ℝ (Fin 3)) :
    {k ∈ D | x ∈ ((shiftedSlabBox S b' t k).carrier : Set (EuclideanSpace ℝ (Fin 3)))}.card
      ≤ 8 := by
  -- Abbreviate the half-widths `w j` (all positive) and the shifted ratios `r j`.
  obtain ⟨w, hw, hwpos⟩ : ∃ w : Fin 3 → ℝ,
      (∀ j, ((![θ * b', b', b'] j : ℝ≥0) : ℝ) = w j) ∧ ∀ j, 0 < w j :=
    ⟨_, fun _ => rfl, coe_boxWidth_pos hθ hb'⟩
  obtain ⟨r, hr⟩ : ∃ r : Fin 3 → ℝ,
      ∀ j, r j = S.basis.repr (x -ᵥ S.center) j / (2 * w j) - t j := ⟨_, fun _ => rfl⟩
  -- Containment in a product of intervals of integer length at most 1.
  have hsub : {k ∈ D | x ∈ ((shiftedSlabBox S b' t k).carrier :
      Set (EuclideanSpace ℝ (Fin 3)))}
      ⊆ Fintype.piFinset fun j => Finset.Icc ⌈r j - 1/2⌉ ⌊r j + 1/2⌋ := by
    intro k hk
    have hmem := (mem_shiftedSlabBox_iff S b' t k x).mp (Finset.mem_filter.mp hk).2
    simp only [hw] at hmem
    rw [Fintype.mem_piFinset]
    intro j
    have hd : (0 : ℝ) < 2 * w j := by linarith [hwpos j]
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hmem j)
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.ceil_le, hr, sub_le_iff_le_add, sub_le_iff_le_add, div_le_iff₀ hd]
      linarith
    · rw [Int.le_floor, hr, ← sub_le_iff_le_add, le_sub_iff_add_le, le_div_iff₀ hd]
      linarith
  -- Each factor is an integer interval of length ≤ 1, so contains at most two integers.
  have hcard : ∀ j : Fin 3, (Finset.Icc ⌈r j - 1/2⌉ ⌊r j + 1/2⌋).card ≤ 2 := by
    intro j
    have hrw : r j - 1/2 + 1 = r j + 1/2 := by ring
    have h : ⌊r j + 1/2⌋ ≤ ⌈r j - 1/2⌉ + 1 := by
      rw [← Int.ceil_add_one, hrw]
      exact Int.floor_le_ceil _
    rw [Int.card_Icc]
    omega
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [Fintype.card_piFinset, Fin.prod_univ_three]
  exact Nat.mul_le_mul (Nat.mul_le_mul (hcard 0) (hcard 1)) (hcard 2)

open Classical in
/-- **Fixed-shift additivity for the box grid.**  For one fixed shift `t`, the boxes of the grid
overlap boundedly, so their intersections with any measurable set `U` add up to at most `8 |U|`:

`∑_{q ∈ D} |U ∩ B_q| ≤ 8 |U|`.

Exact disjointness is *not* claimed (closed boxes share faces), and is not needed: a fixed finite
overlap constant is what the aggregate density argument consumes, and it matches the repository's
`Tube`/`outerPrism` convention of bounded overlap rather than exact tilings. -/
theorem shiftedSlabBox_sum_inter_volume_le {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) {b' : ℝ≥0}
    (hb' : 0 < b') (hθ : 0 < θ) (t : Fin 3 → ℝ) (D : Finset (Fin 3 → ℤ))
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : MeasurableSet U) :
    ∑ q ∈ D, volume (U ∩ ((shiftedSlabBox S b' t q).carrier :
        Set (EuclideanSpace ℝ (Fin 3))))
      ≤ (8 : ENNReal) * volume U := by
  have hAmeas : ∀ q ∈ D, MeasurableSet (U ∩ ((shiftedSlabBox S b' t q).carrier :
      Set (EuclideanSpace ℝ (Fin 3)))) :=
    fun q _ => hU.inter (shiftedSlabBox S b' t q).measurableSet_carrier
  refine le_trans (MeasureTheory.sum_measure_le_mul_measure_biUnion_of_card_filter_le
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3)))) (C := 8) D hAmeas fun y => ?_) ?_
  · refine le_trans (Finset.card_le_card ?_) (card_filter_mem_shiftedSlabBox_le S hb' hθ t D y)
    intro q hq
    simp only [Finset.mem_filter, Set.mem_inter_iff] at hq ⊢
    exact ⟨hq.1, hq.2.2⟩
  · rw [Nat.cast_ofNat]
    exact mul_le_mul_right
      (measure_mono (Set.iUnion₂_subset fun _ _ => Set.inter_subset_left)) _

/-- **One-sided outer slab model of a plank–box intersection** (`lem:tangBoxOuterSlabModel`). There
are absolute constants `Cset = 6`, `Cvol = 1728` such that, for *any* plank `P`, box `Q` and shading
`Y ⊆ P`, there is an `a × b × b` outer slab model `σ` with `Y ∩ Q ⊆ (σ.dilation Cset)` and
`|σ.dilation Cset| ∼_{Cvol} a b²`. This is unconditional: no tangentiality hypothesis is needed,
because the dilated model has the exact volume `1728·a·b²`. -/
private theorem plankBox_outer_slab_model :
    ∃ Cset Cvol : ℝ≥0, 1 ≤ Cset ∧ 1 ≤ Cvol ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {θ : ℝ≥0} (hθ1 : θ ≤ 1)
        (P : Plank a b hab hb1) (Q : ThetaBox θ b hθ1)
        (Y : Set (EuclideanSpace ℝ (Fin 3))),
        Y ⊆ (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) →
        ∃ σ : Prism3D a b b hab le_rfl,
          (Y ∩ Q.carrier) ⊆ (σ.toPrismNDim.dilation Cset).carrier ∧
          Kakeya.ComparableScalars Cvol
            (volume (σ.toPrismNDim.dilation Cset).carrier).toNNReal (a * b ^ 2) := by
  refine ⟨6, 1728, by norm_num, by norm_num, ?_⟩
  intro a b hab hb1 θ hθ1 P Q Y hY
  have hYQ : Y ∩ Q.carrier ⊆ (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ Q.carrier :=
    Set.inter_subset_inter hY (Set.Subset.refl _)
  -- One model serves both cases: centred at a point of `P ∩ Q` if there is one, arbitrarily
  -- otherwise (the intersection being empty, containment is vacuous).
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : EuclideanSpace ℝ (Fin 3),
      (Y ∩ Q.carrier) ⊆ ((plankSlabModel P x₀).dilation 6).carrier := by
    rcases Set.eq_empty_or_nonempty ((P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ Q.carrier)
      with he | ⟨x₀, hx₀P, hx₀Q⟩
    · exact ⟨P.center, (he ▸ hYQ).trans (Set.empty_subset _)⟩
    · exact ⟨x₀, hYQ.trans (plankSlabModel_inter_subset P θ hθ1 Q hx₀P hx₀Q)⟩
  refine ⟨plankSlabModel P x₀, hx₀, ?_⟩
  have hvol : (volume ((plankSlabModel P x₀).dilation 6).carrier).toNNReal
      = 1728 * (a * b ^ 2) := by
    rw [plankSlabModel_dilation_volume P x₀ 6, ← ENNReal.coe_ofNat]
    simp only [← ENNReal.coe_mul, ENNReal.toNNReal_coe]
    ring
  rw [hvol]
  refine ⟨le_rfl, ?_⟩
  rw [← mul_assoc]
  exact le_mul_of_one_le_left' (by norm_num)

/-- `gridShiftSet` is nonempty: the zero shift belongs to it. -/
theorem gridShiftSet_nonempty : gridShiftSet.Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  simp [gridShiftSet, Fintype.mem_piFinset]

/-- **Nearest shifted-lattice cell.**  The two shifted lattices of cell centres, `2wℤ` and
`2wℤ + w`, together form `wℤ`, so for *any* real `x` one of the two shifts `t ∈ {0, ½}` provides a
cell whose centre is within `w/2` of `x` — i.e. `x` lies in the *middle half* of that cell.

This is the form the inscribed-prism construction needs: being merely inside a cell is not enough,
because a point on the cell boundary leaves no room, whereas a point in the middle half leaves a
full `w/2` of clearance on every side. -/
private theorem exists_shift_index_near {w : ℝ} (hw : 0 < w) (x : ℝ) :
    ∃ t : ℝ, (t = 0 ∨ t = 1 / 2) ∧ ∃ k : ℤ,
      |x - 2 * w * ((k : ℝ) + t)| ≤ w / 2 := by
  set m : ℤ := round (x / w) with hm_def
  have hnear : |x - w * (m : ℝ)| ≤ w / 2 := by
    have habs : |x / w - (m : ℝ)| ≤ 1 / 2 := by
      rw [hm_def]; exact abs_sub_round (x / w)
    have hx : x - w * (m : ℝ) = w * (x / w - (m : ℝ)) := by field_simp
    rw [hx, abs_mul, abs_of_pos hw]
    calc w * |x / w - (m : ℝ)| ≤ w * (1 / 2) :=
          mul_le_mul_of_nonneg_left habs hw.le
      _ = w / 2 := by ring
  rcases Int.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · refine ⟨0, Or.inl rfl, k, ?_⟩
    have hrw : 2 * w * ((k : ℝ) + 0) = w * (m : ℝ) := by rw [hk]; push_cast; ring
    rw [hrw]; exact hnear
  · refine ⟨1 / 2, Or.inr rfl, k, ?_⟩
    have hrw : 2 * w * ((k : ℝ) + 1 / 2) = w * (m : ℝ) := by rw [hk]; push_cast; ring
    rw [hrw]; exact hnear

/-- **The shifted index is the rounded one.**  Companion to `exists_shift_index_near`: an integer
`n` whose lattice point `2w(n + a)` is within `w/2` of `y` *is* the nearest integer to
`y/(2w) - a`. -/
private lemma round_eq_of_abs_sub_le {w y a : ℝ} {n : ℤ} (hw : 0 < w)
    (h : |y - 2 * w * ((n : ℝ) + a)| ≤ w / 2) :
    round (y / (2 * w) - a) = n := by -- (extracted by Fuse golfer)
  have hd : (0 : ℝ) < 2 * w := by linarith
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  refine round_eq_iff.mpr ⟨?_, ?_⟩
  · rw [le_sub_iff_add_le, le_div_iff₀ hd]; linarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hd]; linarith

/-- **Upper half of tangentiality, unconditionally.**  For *every* plank `V` and *every*
`θb × b × b` box `Q`, the intersection has volume `≲ a b²`.  This is a direct corollary of the
one-sided outer slab model: `V ∩ Q` sits inside a dilated `a × b × b` model prism whose volume is
exactly `1728 a b²`.  No tangentiality and no angle hypothesis are involved. -/
private theorem exists_plank_box_volume_upper :
    ∃ Cvol : ℝ≥0, 1 ≤ Cvol ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {θ : ℝ≥0} (hθ1 : θ ≤ 1)
        (V : Plank a b hab hb1) (Q : ThetaBox θ b hθ1),
        (volume ((V.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ Q.carrier)).toNNReal
          ≤ Cvol * (a * b ^ 2) := by
  obtain ⟨Cset, Cvol, hCset, hCvol, hmodel⟩ := plankBox_outer_slab_model
  refine ⟨Cvol, hCvol, ?_⟩
  intro a b hab hb1 θ hθ1 V Q
  obtain ⟨σ, hsub, hvol⟩ := hmodel hθ1 V Q (V.carrier : Set (EuclideanSpace ℝ (Fin 3)))
    (Set.Subset.refl _)
  refine (ENNReal.toNNReal_mono ?_ (measure_mono hsub)).trans hvol.1
  rw [PrismNDim.volume_carrier]
  exact ENNReal.mul_ne_top (by simp) (ENNReal.prod_ne_top fun i _ => ENNReal.coe_ne_top)

/-- **Nearest shifted cell, in all three slab coordinates at once.**  For any point `x` there is a
grid shift `t ∈ gridShiftSet` such that the round-index box of that shift puts `x` in its *middle
half*: every slab-frame coordinate of `x` relative to the box centre is at most half the
corresponding box half-width.

This is `exists_shift_index_near` applied in each coordinate separately (the choices are
independent, which is why the product shift set `{0,½}³` is the right one), followed by the
observation that the index produced there *is* the round index `shiftedSlabRoundIndex`: it sits
within `¼` of `S.basis.repr (x -ᵥ S.center) j / (2 w j) - t j`, hence is its nearest integer.

Being merely inside the box is not enough for the inscribed-prism construction — a boundary point
leaves no room — whereas the middle half leaves a full `w j / 2` of clearance on every side. -/
theorem exists_shift_middle_half {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) {b' : ℝ≥0}
    (hθ0 : 0 < θ) (hb' : 0 < b') (x : EuclideanSpace ℝ (Fin 3)) :
    ∃ t ∈ gridShiftSet, ∀ j : Fin 3,
      |S.basis.repr (x -ᵥ (shiftedSlabBox S b' t (shiftedSlabRoundIndex S b' t x)).center) j|
        ≤ ((![θ * b', b', b'] j : ℝ≥0) : ℝ) / 2 := by
  set w := fun (j : Fin 3) => ((![θ * b', b', b'] j : ℝ≥0) : ℝ)
  set u := fun (j : Fin 3) => S.basis.repr (x -ᵥ S.center) j
  have hw_pos : ∀ j : Fin 3, 0 < w j := coe_boxWidth_pos hθ0 hb'
  choose t ht_or k hk using fun j : Fin 3 => exists_shift_index_near (hw_pos j) (u j)
  have ht_mem : t ∈ gridShiftSet := Fintype.mem_piFinset.mpr fun j =>
    Finset.mem_insert.mpr ((ht_or j).imp id Finset.mem_singleton.mpr)
  -- The index produced coordinatewise *is* the round index: it sits within `¼` of the ratio.
  have h_round_eq : ∀ j : Fin 3, shiftedSlabRoundIndex S b' t x j = k j :=
    fun j => round_eq_of_abs_sub_le (hw_pos j) (hk j)
  have h_coord : ∀ j : Fin 3,
      S.basis.repr (x -ᵥ (shiftedSlabBox S b' t (shiftedSlabRoundIndex S b' t x)).center) j
        = u j - 2 * w j * ((k j : ℝ) + t j) := by
    intro j
    change S.basis.repr (x -ᵥ shiftedSlabBoxCenter S b' t (shiftedSlabRoundIndex S b' t x)) j = _
    rw [funext h_round_eq, ← vsub_sub_vsub_cancel_right x (shiftedSlabBoxCenter S b' t k) S.center,
      map_sub, PiLp.sub_apply, shiftedSlabBoxCenter_coord]
  refine ⟨t, ht_mem, fun j => ?_⟩
  rw [h_coord j]
  exact hk j

/-- **Clamping into a symmetric interval stays inside it.** -/
private theorem abs_clamp_le {T h u : ℝ} (_hh0 : 0 ≤ h) (hhT : h ≤ T) :
    |max (-(T - h)) (min u (T - h))| ≤ T - h := by
  have h_nonneg : 0 ≤ T - h := by linarith
  have h_nonpos : -(T - h) ≤ T - h := by linarith
  have h_min_le : min u (T - h) ≤ T - h := min_le_right _ _
  have h_clamped_le : max (-(T - h)) (min u (T - h)) ≤ T - h := max_le h_nonpos h_min_le
  have h_clamped_ge : -(T - h) ≤ max (-(T - h)) (min u (T - h)) := le_max_left _ _
  exact abs_le.mpr ⟨h_clamped_ge, h_clamped_le⟩

/-- **Clamping moves a point of `[-T, T]` by at most `h`.** -/
private theorem abs_clamp_sub_le {T h u : ℝ} (hh0 : 0 ≤ h) (hhT : h ≤ T) (hu : |u| ≤ T) :
    |max (-(T - h)) (min u (T - h)) - u| ≤ h := by
  have h_nonneg : 0 ≤ T - h := by linarith
  have hul : -T ≤ u := (abs_le.mp hu).1
  have hur : u ≤ T := (abs_le.mp hu).2
  by_cases hu_lt_low : u < -(T - h)
  · -- u < -(T - h), so clamped = -(T - h)
    have h_min : min u (T - h) = u := min_eq_left (by nlinarith)
    have h_max : max (-(T - h)) u = -(T - h) := max_eq_left (by nlinarith)
    rw [h_min, h_max]
    have h_nonneg_diff : 0 ≤ -(T - h) - u := by nlinarith
    rw [abs_of_nonneg h_nonneg_diff]
    nlinarith
  · -- u ≥ -(T - h)
    by_cases hu_gt_high : (T - h) < u
    · -- u > T - h, so clamped = T - h
      have h_min : min u (T - h) = T - h := min_eq_right (by nlinarith)
      have h_max : max (-(T - h)) (T - h) = T - h := max_eq_right (by nlinarith)
      rw [h_min, h_max]
      have h_nonpos_diff : (T - h) - u ≤ 0 := by nlinarith
      rw [abs_of_nonpos h_nonpos_diff]
      nlinarith
    · -- u ∈ [-(T - h), T - h], so clamped = u
      have h_min : min u (T - h) = u := min_eq_left (by nlinarith)
      have h_max : max (-(T - h)) u = u := max_eq_right (by nlinarith)
      rw [h_min, h_max, sub_self, abs_zero]
      exact hh0

/-- **Cross-frame expansion bound.**  If the `B`-coordinates of `v` are bounded by `c`, then the
inner product of `v` with any vector `e` is bounded by `∑ j, c j · |⟪e, B j⟫|`.  This is
`inner_eq_sum_frame` followed by the triangle inequality. -/
theorem abs_inner_le_sum_frame_bound
    (B : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
    (e v : EuclideanSpace ℝ (Fin 3)) (c : Fin 3 → ℝ)
    (hv : ∀ j, |B.repr v j| ≤ c j) :
    |(inner ℝ e v : ℝ)| ≤ ∑ j, c j * |(inner ℝ e (B j) : ℝ)| := by
  rw [inner_eq_sum_frame B e v]
  calc
    |∑ j : Fin 3, inner ℝ (B j) v * inner ℝ e (B j)|
        ≤ ∑ j : Fin 3, |inner ℝ (B j) v * inner ℝ e (B j)| :=
      Finset.abs_sum_le_sum_abs (fun j => inner ℝ (B j) v * inner ℝ e (B j)) Finset.univ
    _ = ∑ j : Fin 3, |inner ℝ (B j) v| * |inner ℝ e (B j)| := by
      simp_rw [abs_mul]
    _ = ∑ j : Fin 3, |B.repr v j| * |inner ℝ e (B j)| := by
      simp_rw [B.repr_apply_apply v]
    _ ≤ ∑ j : Fin 3, c j * |inner ℝ e (B j)| := by
      refine Finset.sum_le_sum fun j _ => ?_
      have h_nonneg : 0 ≤ |inner ℝ e (B j)| := abs_nonneg _
      have h_bound : |B.repr v j| ≤ c j := hv j
      nlinarith

/-- **The inscribed-prism principle.**  Let `P` and `Q` be prisms and let `x ∈ P` lie in the
*middle half* of `Q`.  Suppose the half-widths `hh` fit inside `P` (`hh j ≤ P.thicknesses j`) and
are small enough in the `Q`-frame that the cross-frame spread `∑ j, hh j · |⟪Q.basis i, P.basis j⟫|`
is at most a quarter of each `Q` half-width.  Then `P ∩ Q` contains a full `hh`-prism, so
`8 · ∏ hh ≤ |P ∩ Q|`.

The prism is `R = mk' z P.basis hh` where `z` is obtained from `x` by clamping each `P`-coordinate
into `[-(T j - hh j), T j - hh j]`.  Clamping puts `R` inside `P` and moves `x` by at most `hh j` in
coordinate `j`, so in the `Q`-frame `R` stays within `Q.thicknesses i / 2` (middle half) plus twice
the cross-frame spread `Q.thicknesses i / 4`, i.e. exactly `Q.thicknesses i`.

Being in the middle half, rather than merely inside `Q`, is what makes this work: a point on the
boundary of `Q` leaves no room at all. -/
private theorem volume_inter_ge_of_middle_half
    (P Q : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)))
    (hh : Fin 3 → ℝ≥0) (hhP : ∀ j, hh j ≤ P.thicknesses j)
    {x : EuclideanSpace ℝ (Fin 3)} (hxP : x ∈ (P.carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hxQ : ∀ i, |Q.basis.repr (x -ᵥ Q.center) i| ≤ ((Q.thicknesses i : ℝ≥0) : ℝ) / 2)
    (hcross : ∀ i, ∑ j, ((hh j : ℝ≥0) : ℝ) * |(inner ℝ (Q.basis i) (P.basis j) : ℝ)|
      ≤ ((Q.thicknesses i : ℝ≥0) : ℝ) / 4) :
    8 * ∏ j, (hh j : ENNReal) ≤
      volume ((P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ Q.carrier) := by
  -- STEP 1: `s` clamps the `P`-coordinates `u` of `x` into `[-(T - hh), T - hh]`; `z` is the
  -- clamped point.
  set T : Fin 3 → ℝ := fun j => (P.thicknesses j : ℝ) with hT
  set u : Fin 3 → ℝ := fun j => P.basis.repr (x -ᵥ P.center) j with hu
  have hhT : ∀ j, (hh j : ℝ) ≤ T j := fun j => by exact_mod_cast hhP j
  have hu_bound : ∀ j, |u j| ≤ T j := fun j => (P.mem_carrier_iff (x := x)).mp hxP j
  set s : Fin 3 → ℝ := fun j =>
    max (-(T j - (hh j : ℝ))) (min (u j) (T j - (hh j : ℝ))) with hs
  have hs_clamp : ∀ j, |s j| ≤ T j - (hh j : ℝ) := fun j =>
    abs_clamp_le (hh j).coe_nonneg (hhT j)
  have hs_sub : ∀ j, |s j - u j| ≤ (hh j : ℝ) := fun j =>
    abs_clamp_sub_le (hh j).coe_nonneg (hhT j) (hu_bound j)
  set z : EuclideanSpace ℝ (Fin 3) := x + ∑ j, ((s j - u j) : ℝ) • P.basis j with hz
  -- STEP 2: Coordinate properties of `z`.
  have hz_coord : ∀ j, P.basis.repr (z -ᵥ P.center) j = s j := fun j => by
    have hzc : z -ᵥ P.center = (x -ᵥ P.center) + ∑ i, ((s i - u i) : ℝ) • P.basis i := by
      simp only [hz, vsub_eq_sub, add_sub_right_comm]
    rw [P.basis.repr_apply_apply, hzc, inner_add_right, inner_sum,
      ← P.basis.repr_apply_apply]
    simp only [real_inner_smul_right, orthonormal_iff_ite.mp P.basis.orthonormal j, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, hu]
    ring
  have hz_coord_shift : ∀ (y : EuclideanSpace ℝ (Fin 3)) j,
      P.basis.repr (y -ᵥ z) j = P.basis.repr (y -ᵥ P.center) j - s j := fun y j => by
    rw [← vsub_sub_vsub_cancel_right y z P.center, map_sub, PiLp.sub_apply, hz_coord]
  -- STEP 3: The inscribed prism `R`, which sits inside both `P` and `Q`.
  set R : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) :=
    PrismNDim.mk' z P.basis hh with hR
  have hR_mem : ∀ y, y ∈ R.carrier ↔ ∀ j, |P.basis.repr (y -ᵥ z) j| ≤ (hh j : ℝ) := fun y => by
    rw [R.mem_carrier_iff]
    simp only [hR, PrismNDim.center_mk', PrismNDim.basis_mk', PrismNDim.thicknesses_mk']
  have hR_sub_P : (R.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ P.carrier := fun y hy => by
    rw [P.mem_carrier_iff]
    intro j
    change |P.basis.repr (y -ᵥ P.center) j| ≤ T j
    have h1 := abs_le.mp ((hR_mem y).mp hy j)
    have h2 := abs_le.mp (hs_clamp j)
    have h3 := hz_coord_shift y j
    rw [abs_le]
    constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, h3]
  have hR_sub_Q : (R.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Q.carrier := fun y hy => by
    rw [Q.mem_carrier_iff]
    intro i
    have hyR := (hR_mem y).mp hy
    have h_decomp : Q.basis.repr (y -ᵥ Q.center) i = Q.basis.repr (x -ᵥ Q.center) i
        + inner ℝ (Q.basis i) (z - x) + inner ℝ (Q.basis i) (y - z) := by
      rw [Q.basis.repr_apply_apply, Q.basis.repr_apply_apply,
        show y -ᵥ Q.center = (x -ᵥ Q.center) + (z - x) + (y - z) by
          simp only [vsub_eq_sub, sub_add_sub_cancel'],
        inner_add_right, inner_add_right]
    have hzx_bound : |inner ℝ (Q.basis i) (z - x)|
        ≤ ∑ j, ((hh j : ℝ≥0) : ℝ) * |(inner ℝ (Q.basis i) (P.basis j) : ℝ)| := by
      refine abs_inner_le_sum_frame_bound P.basis (Q.basis i) (z - x)
        (fun j => ((hh j : ℝ≥0) : ℝ)) fun j => ?_
      rw [show z - x = (z -ᵥ P.center) - (x -ᵥ P.center) by
          simp only [vsub_eq_sub, sub_sub_sub_cancel_right], map_sub, PiLp.sub_apply, hz_coord]
      exact hs_sub j
    have hyz_bound : |inner ℝ (Q.basis i) (y - z)|
        ≤ ∑ j, ((hh j : ℝ≥0) : ℝ) * |(inner ℝ (Q.basis i) (P.basis j) : ℝ)| := by
      refine abs_inner_le_sum_frame_bound P.basis (Q.basis i) (y - z)
        (fun j => ((hh j : ℝ≥0) : ℝ)) fun j => ?_
      simpa only [vsub_eq_sub] using hyR j
    have hx_bound := hxQ i
    have hc := hcross i
    rw [h_decomp]
    refine (abs_add_three _ _ _).trans ?_
    linarith only [hx_bound, hzx_bound, hyz_bound, hc]
  -- STEP 4: `|R| = 8 ∏ hh`, and `R ⊆ P ∩ Q`.
  have h_vol_R : volume (R.carrier : Set (EuclideanSpace ℝ (Fin 3))) =
      8 * ∏ j, (hh j : ENNReal) := by
    rw [R.volume_carrier]
    simp only [hR, PrismNDim.thicknesses_mk', finrank_euclideanSpace_fin]
    norm_num
  calc
    8 * ∏ j, (hh j : ENNReal) = volume (R.carrier : Set (EuclideanSpace ℝ (Fin 3))) := h_vol_R.symm
    _ ≤ volume ((P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ Q.carrier) :=
      measure_mono (Set.subset_inter hR_sub_P hR_sub_Q)

/-- Arithmetic core of the cross-frame spread bound: if the leading weight `h₀` is at most `T/16`
and the two remaining weights `ρ` pair with coefficients of size at most `m` where `ρ * m ≤ T/64`,
then the weighted sum of the three coefficients is at most `T/4`. -/
private lemma weighted_abs_sum_le_quarter {h₀ ρ m T c₀ c₁ c₂ : ℝ} (hh₀ : 0 ≤ h₀) (hρ : 0 ≤ ρ)
    (hT : 0 ≤ T) (hh₀T : h₀ ≤ T / 16) (hρm : ρ * m ≤ T / 64) (hc₀ : |c₀| ≤ 1) (hc₁ : |c₁| ≤ m)
    (hc₂ : |c₂| ≤ m) : h₀ * |c₀| + ρ * |c₁| + ρ * |c₂| ≤ T / 4 := by
  -- (extracted by Fuse golfer)
  have e0 := mul_le_mul_of_nonneg_left hc₀ hh₀
  have e1 := mul_le_mul_of_nonneg_left hc₁ hρ
  have e2 := mul_le_mul_of_nonneg_left hc₂ hρ
  rw [mul_one] at e0
  linarith only [e0, e1, e2, hh₀T, hρm, hT]

/-- **The cross-frame spread of the inscribed half-widths is a quarter of the box.**  With
`h₀ = min a (θb/16)` and `ρ = b/(64 Cang)`, the plank-frame prism `![h₀, ρ, ρ]` spreads over at
most a quarter of each half-width of a `θb × b × b` box whose frame makes angle `≤ Cang·θ` with the
plank.  In the thin direction the two off-diagonal inner products are `≤ Cang·θ`
(`abs_inner_basis_ne_zero_le_angle`), giving `h₀ + 2ρ·Cang·θ ≤ θb/16 + θb/32 ≤ θb/4`; in the two
wide directions the crude bound `1` gives `h₀ + 2ρ ≤ b/16 + b/32 ≤ b/4`. -/
private theorem inscribed_cross_spread_le
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (V : Plank a b hab hb1)
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (t : Fin 3 → ℝ) (k : Fin 3 → ℤ)
    {Cang : ℝ≥0} (hCang : 1 ≤ Cang) (hb0 : 0 < b) (hθ0 : 0 < θ)
    (haθb : (a : ℝ) ≤ (θ : ℝ) * (b : ℝ))
    (hang : Prism3D.angle V S ≤ (Cang : ℝ) * (θ : ℝ)) (i : Fin 3) :
    ∑ j, ((![min a (θ * b / 16), b / (64 * Cang), b / (64 * Cang)] j : ℝ≥0) : ℝ) *
        |(inner ℝ ((shiftedSlabBox S b t k).basis i) (V.basis j) : ℝ)|
      ≤ (((shiftedSlabBox S b t k).thicknesses i : ℝ≥0) : ℝ) / 4 := by
  have h3 : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2 := by decide
  rw [show (shiftedSlabBox S b t k).basis = S.basis from PrismNDim.basis_mk' _ _ _,
    show (shiftedSlabBox S b t k).thicknesses = ![θ * b, b, b] from PrismNDim.thicknesses_mk' _ _ _,
    Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_min]
  -- coefficients in ℝ
  have hb0' : (0 : ℝ) < b := NNReal.coe_pos.mpr hb0
  have hθ0' : (0 : ℝ) < θ := NNReal.coe_pos.mpr hθ0
  have hθ1' : (θ : ℝ) ≤ 1 := NNReal.coe_le_one.mpr hθ1
  have hC1 : (1 : ℝ) ≤ Cang := NNReal.one_le_coe.mpr hCang
  have hCpos : (0 : ℝ) < Cang := one_pos.trans_le hC1
  have hb64 : (0 : ℝ) ≤ (b : ℝ) / 64 := div_nonneg b.coe_nonneg (Nat.ofNat_nonneg _)
  have hθb0 : (0 : ℝ) ≤ (θ : ℝ) * b := a.coe_nonneg.trans haθb
  have hh₀0 : (0 : ℝ) ≤ min (a : ℝ) ((θ : ℝ) * b / 16) :=
    le_min a.coe_nonneg (div_nonneg hθb0 (Nat.ofNat_nonneg _))
  have hρ0 : (0 : ℝ) ≤ (b : ℝ) / (64 * (Cang : ℝ)) :=
    div_nonneg b.coe_nonneg (mul_nonneg (Nat.ofNat_nonneg _) hCpos.le)
  have hh₀θ : min (a : ℝ) ((θ : ℝ) * b / 16) ≤ (θ : ℝ) * b / 16 := min_le_right _ _
  have hρC : (b : ℝ) / (64 * (Cang : ℝ)) * (Cang : ℝ) = (b : ℝ) / 64 := by
    rw [← div_div, div_mul_cancel₀ _ hCpos.ne']
  have hh₀b : min (a : ℝ) ((θ : ℝ) * b / 16) ≤ (b : ℝ) / 16 :=
    hh₀θ.trans (by linarith only [mul_le_of_le_one_left hb0'.le hθ1', hθ0'])
  have hρ64 : (b : ℝ) / (64 * (Cang : ℝ)) ≤ (b : ℝ) / 64 := by
    rw [← div_div]; exact div_le_self hb64 hC1
  -- crude bound for any inner product of unit basis vectors: |⟨S.basis i, V.basis j⟩| ≤ 1
  have hc (j : Fin 3) : |(inner ℝ (S.basis i) (V.basis j) : ℝ)| ≤ 1 := by
    have h := abs_real_inner_le_norm (S.basis i) (V.basis j)
    rwa [S.basis.norm_eq_one i, V.basis.norm_eq_one j, mul_one] at h
  -- the two wide directions: the crude bound `1` gives `h₀ + 2ρ ≤ b/16 + b/32 ≤ b/4`
  have hwide := weighted_abs_sum_le_quarter hh₀0 hρ0 hb0'.le hh₀b
    ((mul_one _).trans_le hρ64) (hc 0) (hc 1) (hc 2)
  rcases h3 i with rfl | rfl | rfl
  · -- thin direction: the two off-diagonal inner products are `≤ Cang·θ`
    have hs (j : Fin 3) (hj : j ≠ 0) :
        |(inner ℝ (S.basis 0) (V.basis j) : ℝ)| ≤ (Cang : ℝ) * θ := by
      rw [real_inner_comm]
      exact (abs_inner_basis_ne_zero_le_angle V S hj).trans hang
    exact weighted_abs_sum_le_quarter (T := (θ : ℝ) * b) hh₀0 hρ0 hθb0 hh₀θ
      (le_of_eq (by rw [← mul_assoc, hρC]; ring)) (hc 0) (hs 1 (by decide)) (hs 2 (by decide))
  · exact hwide
  · exact hwide

/-- Arithmetic core of the inscribed-prism bound: the half-widths
`(min a (θb/16), b/(64 Cang), b/(64 Cang))` have product at least `a b² / (8 · 8192 Cang²)`.
The hypothesis `a ≤ θb` is what turns the `min` into `a / 16`. -/
private lemma mul_sq_le_halfwidth_prod {a b θ Cang : ℝ≥0} (hCang : 1 ≤ Cang)
    (haθb : a ≤ θ * b) :
    (a : ENNReal) * (b : ENNReal) ^ 2 ≤ 8192 * (Cang : ENNReal) ^ 2 *
      (8 * ∏ j : Fin 3,
        (((![min a (θ * b / 16), b / (64 * Cang), b / (64 * Cang)] : Fin 3 → ℝ≥0) j : ℝ≥0)
          : ENNReal)) := by
  -- (extracted by Fuse golfer)
  have hCne : Cang ≠ 0 := by
    rintro rfl
    simp at hCang
  have keyN : a * b ^ 2 ≤ 8192 * Cang ^ 2 *
      (8 * (min a (θ * b / 16) * (b / (64 * Cang)) * (b / (64 * Cang)))) := by
    calc a * b ^ 2
        = 8192 * Cang ^ 2 * (8 * (a / 16 * (b / (64 * Cang)) * (b / (64 * Cang)))) := by
          field_simp
          ring
      _ ≤ _ := by
          gcongr
          exact le_min (div_le_self zero_le (by norm_num)) (by gcongr)
  rw [Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  exact_mod_cast keyN

/-- The `ENNReal` form of `inscribed_prism_volume_lower`, before the `toNNReal` transfer.  This is
where all the geometry happens: instantiate `volume_inter_ge_of_middle_half` with the plank, the
shifted box and the half-widths `![min a (θb/16), b/(64 Cang), b/(64 Cang)]`, discharge its
cross-frame hypothesis by `inscribed_cross_spread_le`, and simplify the resulting product of
half-widths using `min a (θb/16) ≥ a/16` (which is where `a ≤ θb` is used). -/
private theorem inscribed_prism_volume_lower_ennreal
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (V : Plank a b hab hb1)
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (t : Fin 3 → ℝ) (k : Fin 3 → ℤ)
    {Cang : ℝ≥0} (hCang : 1 ≤ Cang)
    (_ha : 0 < a) (hb0 : 0 < b) (hθ0 : 0 < θ) (haθb : (a : ℝ) ≤ (θ : ℝ) * (b : ℝ))
    (hang : Prism3D.angle V S ≤ (Cang : ℝ) * (θ : ℝ))
    {x : EuclideanSpace ℝ (Fin 3)} (hxV : x ∈ (V.carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hxQ : ∀ j : Fin 3,
      |S.basis.repr (x -ᵥ (shiftedSlabBox S b t k).center) j|
        ≤ ((![θ * b, b, b] j : ℝ≥0) : ℝ) / 2) :
    (a : ENNReal) * (b : ENNReal) ^ 2 ≤ 8192 * (Cang : ENNReal) ^ 2 *
      volume ((V.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        (shiftedSlabBox S b t k).carrier) := by
  have hρb : b / (64 * Cang) ≤ b :=
    div_le_self zero_le (hCang.trans (le_mul_of_one_le_left zero_le (by norm_num)))
  have hhP : ∀ j : Fin 3,
      (![min a (θ * b / 16), b / (64 * Cang), b / (64 * Cang)] : Fin 3 → ℝ≥0) j
        ≤ V.thicknesses j := by
    rw [Prism3D.thicknesses_eq V]
    intro j
    fin_cases j
    · exact min_le_left _ _
    · exact hρb
    · exact hρb.trans hb1
  have hvol := volume_inter_ge_of_middle_half V.toPrismNDim
    (shiftedSlabBox S b t k).toPrismNDim
    ![min a (θ * b / 16), b / (64 * Cang), b / (64 * Cang)] hhP hxV hxQ
    (inscribed_cross_spread_le V S t k hCang hb0 hθ0 haθb hang)
  exact (mul_sq_le_halfwidth_prod hCang (mod_cast haθb)).trans
    (mul_le_mul_right hvol (8192 * (Cang : ENNReal) ^ 2))

/-- **Lower half of tangentiality: the inscribed prism.**  If `x` lies in the middle half of the
box `Q = shiftedSlabBox S b t k` and also in the plank `V`, then `V ∩ Q` contains a whole prism of
dimensions comparable to `a × b × b`, so `a b² ≲ |V ∩ Q|` with a constant depending only on the
angle constant `Cang`.

The prism is built in the *plank* frame with half-widths `(h₀, ρ, ρ)`, where
`h₀ = min a (θb/16)` and `ρ = b / (64 Cang)`, centred at the point `z` obtained from `x` by
clamping each plank coordinate into the shrunken box `[-(T j - h j), T j - h j]`, `T = (a, b, 1)`.
Clamping moves `x` by at most `h j` in coordinate `j`, so:

* `R ⊆ V` holds by construction (each clamped coordinate has `|z j| + h j ≤ T j`), using
  `h₀ ≤ a`, `ρ ≤ b` and `ρ ≤ 1`;
* `R ⊆ Q` is a cross-frame estimate.  In the thin slab direction the off-diagonal inner products
  `|⟪V.basis j, S.basis 0⟫|`, `j ≠ 0`, are at most the angle `Cang·θ`
  (`abs_inner_basis_ne_zero_le_angle`), so the coordinate-`0` budget spent is
  `θb/2` (the middle-half clearance) plus `2·(h₀ + 2ρ·Cang·θ) ≤ 2·(θb/16 + θb/32) ≤ θb/4`; in the
  two wide directions the budget spent is `b/2 + 2·(h₀ + 2ρ) ≤ b/2 + b/4`.  Both stay under the
  box half-widths with room to spare.

Finally `|R| = 8 h₀ ρ² ≥ 8 (a/16)(b/(64 Cang))² = a b² / (8192 Cang²)`, using `a ≤ θb` to convert
the `min` into `h₀ ≥ a/16`.  Every constant here is strictly positive and depends only on `Cang`. -/
private theorem inscribed_prism_volume_lower
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (V : Plank a b hab hb1)
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (t : Fin 3 → ℝ) (k : Fin 3 → ℤ)
    {Cang : ℝ≥0} (hCang : 1 ≤ Cang)
    (ha : 0 < a) (hb0 : 0 < b) (hθ0 : 0 < θ) (haθb : (a : ℝ) ≤ (θ : ℝ) * (b : ℝ))
    (hang : Prism3D.angle V S ≤ (Cang : ℝ) * (θ : ℝ))
    {x : EuclideanSpace ℝ (Fin 3)} (hxV : x ∈ (V.carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hxQ : ∀ j : Fin 3,
      |S.basis.repr (x -ᵥ (shiftedSlabBox S b t k).center) j|
        ≤ ((![θ * b, b, b] j : ℝ≥0) : ℝ) / 2) :
    (a : ℝ≥0) * b ^ 2 ≤ 8192 * Cang ^ 2 *
      (volume ((V.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        (shiftedSlabBox S b t k).carrier)).toNNReal := by
  have hfin : volume ((V.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
      (shiftedSlabBox S b t k).carrier) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_left).trans_lt
      (by rw [Prism3D.volume_carrier V]; finiteness)).ne
  refine ENNReal.coe_le_coe.mp ?_
  push_cast [ENNReal.coe_toNNReal hfin]
  exact inscribed_prism_volume_lower_ennreal V S t k hCang ha hb0 hθ0 haθb hang hxV hxQ

/-- **Tangentiality from meeting the middle half of a box, at a prescribed shift.**  There is a
`cTan ≥ 1` depending only on `Cang` such that a plank `V` of the controlled slab family of `S` is
tangential to *any* grid box `Q = shiftedSlabBox S b t k` of *any* shift `t` that it meets in the
concentric half-dilation of `Q`: `|V ∩ Q| ∼_{cTan} a b²`.

The statement is shift-free: choosing a shift serves only to place a point in the middle half of
*some* box (`Plank.exists_shift_middle_half`), and once a point of the plank is known to lie in the
middle half of the box at hand, no choice is left to make.  The upper half of the comparability is
unconditional (`exists_plank_box_volume_upper`) and the lower half is the inscribed-prism estimate,
whose hypothesis is exactly membership in the middle half, i.e. in `Q.dilation 2⁻¹`.

The lower half is the real content, and it is what the eight shifts buy.  Direction by direction,
with box half-widths `(θb, b, b)` and plank half-widths `(a, b, 1)`: in the long direction the plank
spans the box; in the thin direction the plank is thinner than the box (`a ≤ θb`); in the middle
direction plank and box have the same half-width `b`, so the plank can be split between two boxes —
but the two cells containing a point for the shifts `0` and `½` of that coordinate are offset by
half a cell, so one of them always meets the plank's middle extent in at least half a cell.  Hence
two shifts per coordinate suffice and `gridShiftSet = {0,½}³` need not be enlarged.

`cTan` depends only on `Cang`: a plank tilted by `Cang·θ` crosses about `Cang` of the thin box slots
rather than one, so the inscribed prism shrinks by that *fixed* factor.

The middle-half hypothesis cannot be weakened to `V ∩ Q ≠ ∅`.  With box half-widths `(θb, b, b)`
in the frame of `S` and plank half-widths `(a, b, 1)`, a plank whose middle extent overlaps the
box's middle extent in a sliver of width `ε` meets `Q` in volume `≍ min (a) (θb) · ε · b`, which
tends to `0` while `a b²` is fixed; so the lower half fails for every constant.  Corner and edge
clipping is why this layer is pointwise rather than "meets the box". -/
theorem comparableScalars_of_mem_halfBox (Cang : ℝ≥0) (hCang : 1 ≤ Cang) :
    ∃ cTan : ℝ≥0, 1 ≤ cTan ∧
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
        (V : Plank a b hab hb1) {θ : ℝ≥0} (hθ1 : θ ≤ 1) (S : Slab θ hθ1)
        (t : Fin 3 → ℝ) (k : Fin 3 → ℤ),
        0 < a → 0 < b → a ≤ θ * b →
        Prism3D.angle V S ≤ (Cang : ℝ) * (θ : ℝ) →
        (∃ x ∈ (V.carrier : Set (EuclideanSpace ℝ (Fin 3))),
          x ∈ (((shiftedSlabBox S b t k).toPrismNDim.dilation 2⁻¹).carrier :
            Set (EuclideanSpace ℝ (Fin 3)))) →
        Kakeya.ComparableScalars cTan
          (volume ((V.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
            (shiftedSlabBox S b t k).carrier)).toNNReal (a * b ^ 2) := by
  obtain ⟨Cvol, hCvol, hupper⟩ := exists_plank_box_volume_upper
  refine ⟨max Cvol (8192 * Cang ^ 2), le_max_of_le_left hCvol, ?_⟩
  rintro a b hab hb1 V θ hθ1 S t k ha hb0 haθb hang ⟨x, hxV, hxMid⟩
  have hθ0 : 0 < θ := pos_of_ne_zero fun h => ha.ne' (by simpa [h] using haθb)
  have hxQ : ∀ j : Fin 3,
      |S.basis.repr (x -ᵥ (shiftedSlabBox S b t k).center) j|
        ≤ ((![θ * b, b, b] j : ℝ≥0) : ℝ) / 2 := fun j => by
    simpa only [PrismNDim.dilation_center, PrismNDim.dilation_basis,
      PrismNDim.dilation_thicknesses, Prism3D.thicknesses_eq (shiftedSlabBox S b t k),
      show (shiftedSlabBox S b t k).basis = S.basis from PrismNDim.basis_mk' _ _ _,
      inv_mul_eq_div, NNReal.coe_div, NNReal.coe_ofNat] using
      ((shiftedSlabBox S b t k).toPrismNDim.dilation 2⁻¹).mem_carrier_iff (x := x) |>.mp hxMid j
  exact ⟨(hupper hθ1 V (shiftedSlabBox S b t k)).trans (mul_le_mul_left (le_max_left _ _) _),
    (inscribed_prism_volume_lower V S t k hCang ha hb0 hθ0 (mod_cast haθb) hang hxV hxQ).trans
      (mul_le_mul_left (le_max_right _ _) _)⟩

end Plank

end
