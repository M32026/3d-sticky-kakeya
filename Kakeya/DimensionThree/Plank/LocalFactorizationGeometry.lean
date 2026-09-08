/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.PrismGeometry
public import Kakeya.DimensionThree.Plank.FrostmanPlankEstimate
public import Kakeya.DimensionThree.Plank.ComparableBodyFactorization

/-!
# GWZ Proposition 6.6(A): the cross-parent repair

The printed proof of GWZ Proposition 6.6(A) forms the outer plank family

`𝒲 = ⨆_{T_ρ ∈ 𝕋_ρ} 𝒲_{T_ρ}`

from one plank factorization per coarse fibre `𝕋[T_ρ]`, fixes `W ∈ 𝒲_{T_ρ}` with thickening
`W_θ`, and then asserts that every `W' ∈ 𝒲` with `W' ⊆ W_θ` already lies in the *same* parent
family `𝒲_{T_ρ}`, i.e. `𝒲[W_θ] = 𝒲_{T_ρ}[W_θ]`.

**That inference is false.**  If `W'` comes from a different coarse parent `T_ρ'`, a fine tube `T'`
in the fibre of `W'` satisfies `T' ⊆ T_ρ'` and `T' ⊆ W' ⊆ W_θ`, but nothing forces `T' ⊆ T_ρ`, so
uniqueness of the parent of `T'` does not give `T_ρ' = T_ρ`.  Nothing in this file states or uses
any such same-parent equality.

The corrected argument keeps the parent label of every outer plank and splits the count:

* `Tube.UniformTubeSet.card_contributingNodes_le` bounds the number of coarse parents that
  can contribute a plank inside `W_θ`, using `UniformTubeSet.boundedOverlap`;
* `Kakeya.card_filter_le_of_parentwise` sums a parentwise bound over a controlled parent set;
* `Kakeya.card_le_of_parentwise_of_boundedOverlap` combines the two, and
  `Kakeya.plankConcentration_of_parentwise` lands the result in the exact `≤ M * θ` shape that GWZ
  Lemma 6.4 (`Kakeya.FrostmanEstimate.plankEstimate`) consumes, with

  `M = C_geom * C_uniform * C_local * (b / a)`

  in place of the printed argument's unsupported `M ≲ b / a`.

## The Scale comparison

`PlankFactorizationEstimate.lean`'s Proposition 6.6(A) currently assumes `δ ≤ ρ` and `ρ ≤ a`, on top of
`a ≤ b ≤ 1`.  The second of these is reversed.  The outer bodies of a
`Kakeya.PlankFactorization` are convex hulls of subfamilies of the fine tubes assigned to one
coarse `ρ`-tube `R`, so every outer plank is *contained in* `R`; a plank inside a `ρ`-tube has
`b ≤ ρ`.  This is `Kakeya.PlankFactorization.b_le_of_le_tube` below, and it needs no new
hypothesis — it is a consequence of the data Proposition 6.6(A) already carries.  Together with
`ρ ≤ a ≤ b` the current signature therefore forces `a ≍ b ≍ ρ`, a degenerate regime in which the
conclusion's `(a/b) ^ (3β/2)` gain is vacuous.  The honest chain is `δ ≲ a ≤ b ≤ ρ`, matching the
Section 8 consumer's `b ≤ ρ`.

`b ≤ ρ` is what makes the covering datum `hF` below suppliable at all: only when the two short
axes of `W_θ` are at most the coarse radius can a `θb × b × 1` prism be swept by boundedly many
`ρ`-tubes.

## Leaf essential distinctness is a separate matter

`UniformTubeSet.boundedOverlap` controls *coarse parent* overlap only.  It says nothing about the
leaf `δ`-tubes being pairwise essentially distinct, and the anisotropic packing step that supplies
the parentwise Katz--Tao bound `hlocal` does use leaf ED.  That bound is therefore taken as a
hypothesis here rather than derived, and `UniformTubeSet` is left unstrengthened.
-/

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody
open scoped NNReal Real ENNReal Classical

noncomputable section

namespace Kakeya

/-! ### The Scale comparison: a plank inside a coarse tube is thin -/

/-- **Scale comparison, in the form the factorization supplies it.**

If a `Kakeya.PlankFactorization` factors a nonempty family all of whose members lie in a single
coarse `ρ`-tube `R`, then `b ≤ ρ`.  Each part of the underlying `Finpartition` is nonempty, so its
outer body is the convex hull of a nonempty subfamily of bodies contained in the convex set `R`,
hence is itself contained in `R`; that outer body is an `a × b × 1` plank.

Consequently the hypothesis `ρ ≤ a` of the current Proposition 6.6(A) signature is not merely
unnecessary — combined with this lemma it collapses `a`, `b` and `ρ` to a single scale. -/
theorem PlankFactorization.b_le_of_le_tube {ι : Type*} [DecidableEq ι]
    {a b ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {s : Finset ι}
    {V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {C₀ : ℝ≥0}
    (Fz : PlankFactorization a b hab hb1 s V C₀) (hs : s.Nonempty)
    (R : Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (hV : ∀ i ∈ s, V i ≤ R.toConvexSpaceBody) : b ≤ ρ := by
  obtain ⟨t, ht⟩ := Fz.parts_nonempty (Finset.nonempty_iff_ne_empty.mp hs)
  have htne : t.Nonempty := Fz.nonempty_of_mem_parts ht
  have hts : t ⊆ s := fun i hi ↦ Fz.subset ht hi
  have hle : t.convexHull_biUnion V ≤ R.toConvexSpaceBody :=
    (htne.convexHull_biUnion_le_iff V R.toConvexSpaceBody).2 (fun i hi ↦ hV i (hts hi))
  rcases Fz.parts_are_planks t ht with ⟨Q, hQ⟩
  exact Plank.b_le_of_le_tube Q R (by rw [← hQ]; exact hle)

/-- **The scale relation of GWZ Proposition 6.6(A), derived from its own data.**

Given a coarse family `(R k)_{k ∈ r}` of `ρ`-tubes, an assignment putting every fine tube inside its
coarse tube, and one `a × b × 1` plank factorisation `Fz k` of each coarse fibre, the outer plank
width satisfies `b ≤ ρ`.

Take any `i₀ ∈ q` and let `k := assign i₀`.  The fibre `{i ∈ q | assign i = k}` contains `i₀`, so it
is nonempty, and every one of its members lies in `R k`; now apply
`Kakeya.PlankFactorization.b_le_of_le_tube`.

This is what replaces the deleted (and false) hypothesis `ρ ≤ a` of Proposition 6.6(A): the correct
relation is not an extra assumption but a consequence, so the public statement loses a hypothesis
rather than gaining one.  Nonemptiness of `q` is genuinely needed — with `q = ∅` there is no plank
at all and nothing constrains `b` — and it is exactly the case in which the multiplicity bound is
trivial. -/
theorem b_le_of_localPlankFactorisation {ι κ : Type*}
    {δ ρ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {q : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} (hq : q.Nonempty)
    {r : Finset κ} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))} {assign : ι → κ}
    (hassign : ∀ i ∈ q, assign i ∈ r ∧
      (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody)
    {C₀ : ℝ≥0}
    (Fz : ∀ k ∈ r, PlankFactorization a b hab hb1
      {i ∈ q | assign i = k} (fun i => (T i).toConvexSpaceBody) C₀) :
    b ≤ ρ := by
  obtain ⟨i₀, hi₀⟩ := hq
  refine PlankFactorization.b_le_of_le_tube (Fz (assign i₀) (hassign i₀ hi₀).1)
    ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, rfl⟩⟩ (R (assign i₀)) ?_
  intro i hi
  obtain ⟨hiq, hik⟩ := Finset.mem_filter.mp hi
  exact hik ▸ (hassign i hiq).2

/-! ### The *longitudinal* scale relation, and why it is decisive

`Kakeya.Plank.b_le_of_le_tube` compares the transverse extents of a plank and a coarse tube.  The
longitudinal extents must also be compared, and doing so is much more restrictive.

In this development a `Plank a b` is `Prism3D a b 1`, whose `thicknesses` are *half*-widths
(`Kakeya.Prism3D.volume_carrier` is `8 * a * b * c`).  So a plank has longitudinal **extent 2**: it
contains the two points `centre ± e` for a unit `e` on its long axis, at distance `2`
(`Kakeya.Prism3D.mem_add_mem_longAxis`, `mem_sub_mem_longAxis`).

A `Tube ρ`, by contrast, is the `ρ`-neighbourhood of a *unit* segment, so it sits in a ball of
radius `1/2 + ρ` about its midpoint (`Kakeya.Tube.carrier_subset_closedBall_midpoint`) and therefore
has diameter at most `1 + 2ρ`.

Consequently a plank inside a `ρ`-tube forces `2 ≤ 1 + 2ρ`, i.e. `1/2 ≤ ρ`.  The two normalisations
disagree by a factor of two in the long direction, and the consequence is not cosmetic: the
`PlankFactorization` hypothesis of Proposition 6.6(A) is only satisfiable for `ρ ∈ [1/2, 1]`. -/

/-- `1/2 ≤ ρ`, in the form the factorization supplies it (companion of
`Kakeya.PlankFactorization.b_le_of_le_tube`). -/
theorem PlankFactorization.half_le_of_le_tube {ι : Type*} [DecidableEq ι]
    {a b ρ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {s : Finset ι}
    {V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {C₀ : ℝ≥0}
    (Fz : PlankFactorization a b hab hb1 s V C₀) (hs : s.Nonempty)
    (R : Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (hV : ∀ i ∈ s, V i ≤ R.toConvexSpaceBody) : 1 / 2 ≤ ρ := by
  obtain ⟨t, ht⟩ := Fz.parts_nonempty (Finset.nonempty_iff_ne_empty.mp hs)
  have htne : t.Nonempty := Fz.nonempty_of_mem_parts ht
  have hts : t ⊆ s := fun i hi ↦ Fz.subset ht hi
  have hle : t.convexHull_biUnion V ≤ R.toConvexSpaceBody :=
    (htne.convexHull_biUnion_le_iff V R.toConvexSpaceBody).2 (fun i hi ↦ hV i (hts hi))
  rcases Fz.parts_are_planks t ht with ⟨Q, hQ⟩
  exact Plank.half_le_of_le_tube Q R (by rw [← hQ]; exact hle)

/-- **`1/2 ≤ ρ` from Proposition 6.6(A)'s own data.**

Companion of `Kakeya.b_le_of_localPlankFactorisation`.  Together they pin the coarse scale of the
local plank factorisation to `ρ ∈ [1/2, 1]`, so the intended regime `ρ ≪ 1` of GWZ
Proposition 6.6(A) is *not* expressible against the current `Plank`/`Tube` normalisation. -/
theorem half_le_of_localPlankFactorisation {ι κ : Type*}
    {δ ρ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {q : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} (hq : q.Nonempty)
    {r : Finset κ} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))} {assign : ι → κ}
    (hassign : ∀ i ∈ q, assign i ∈ r ∧
      (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody)
    {C₀ : ℝ≥0}
    (Fz : ∀ k ∈ r, PlankFactorization a b hab hb1
      {i ∈ q | assign i = k} (fun i => (T i).toConvexSpaceBody) C₀) :
    1 / 2 ≤ ρ := by
  obtain ⟨i₀, hi₀⟩ := hq
  refine PlankFactorization.half_le_of_le_tube (Fz (assign i₀) (hassign i₀ hi₀).1)
    ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, rfl⟩⟩ (R (assign i₀)) ?_
  intro i hi
  obtain ⟨hiq, hik⟩ := Finset.mem_filter.mp hi
  exact hik ▸ (hassign i hiq).2

/-! ### The leafwise `ρ`-tube cover from a position × direction net

This is the covering datum at the *external* radius `ρ`, built as GWZ intends: an `O(1)` net of
positions crossed with an `O(1)` net of directions, each pair giving one `ρ`-tube, and whole-leaf
containment proved from closeness of the two endpoints.

Two scale inputs make the nets `O(1)`, and both are *derived* in the 6.6(A) context rather than
assumed:

* `1/2 ≤ ρ` — `Kakeya.half_le_of_localPlankFactorisation`;
* `δ ≤ 1/4` — from the consumer's freedom to shrink `δ₀`.

Together they give the net budget `δ + 1/8 ≤ ρ`, so a single net at scale `1/16` in `B₁` serves
*both* the position and the direction coordinate (a unit direction lies in `B₁` too), and the
covering tubes have radius exactly `ρ` — no dilation constant is needed. -/

/-- `d` normalised to a unit vector, with a fixed fallback when `d = 0`.  Making this a *total*
function is what lets the covering family be a plain `Finset.image` over a product of nets, with no
dependent-membership plumbing. -/
noncomputable def unitDir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e₀ d : E) : E :=
  if d = 0 then e₀ else ‖d‖⁻¹ • d

theorem norm_unitDir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {e₀ : E} (he₀ : ‖e₀‖ = 1) (d : E) : ‖unitDir e₀ d‖ = 1 := by
  unfold unitDir
  split_ifs with h
  · exact he₀
  · rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg d),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

/-- Normalising a net point costs at most as much again: if `d` is a unit vector and `d'` is within
`r < 1` of it, then the *normalisation* of `d'` is within `2r` of `d`.

Indeed `d' ≠ 0` since `‖d'‖ ≥ 1 - r > 0`, and
`‖d' - ‖d'‖⁻¹ • d'‖ = |‖d'‖ - 1| = |‖d'‖ - ‖d‖| ≤ ‖d' - d‖ ≤ r`. -/
theorem norm_sub_unitDir_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {e₀ : E} (he₀ : ‖e₀‖ = 1) {d d' : E} (hd : ‖d‖ = 1) {r : ℝ}
    (hr : dist d d' ≤ r) (hr1 : r < 1) :
    ‖d - unitDir e₀ d'‖ ≤ 2 * r := by
  have hrd : ‖d - d'‖ ≤ r := by rwa [← dist_eq_norm]
  have hnorm : |‖d'‖ - 1| ≤ r := by
    have h1 : |‖d'‖ - ‖d‖| ≤ ‖d' - d‖ := abs_norm_sub_norm_le d' d
    have h1' : |‖d'‖ - 1| ≤ ‖d' - d‖ := by simpa [hd] using h1
    exact h1'.trans (by rwa [norm_sub_rev d' d])
  have hr_nonneg : 0 ≤ r := le_trans dist_nonneg hr
  have hd'0 : d' ≠ 0 := by
    intro h0
    have h0n : ‖d'‖ = 0 := by simp [h0]
    have h1 : |(0 : ℝ) - 1| ≤ r := by rwa [h0n] at hnorm
    norm_num at h1
    linarith
  rw [unitDir, if_neg hd'0]
  have hpos : 0 < ‖d'‖ := norm_pos_iff.mpr hd'0
  have hnorm_eq : ‖d' - ‖d'‖⁻¹ • d'‖ = |‖d'‖ - 1| := by
    rw [show d' - ‖d'‖⁻¹ • d' = (1 - ‖d'‖⁻¹) • d' from by module,
      norm_smul, Real.norm_eq_abs, ← abs_of_nonneg (norm_nonneg d'), ← abs_mul]
    congr 1
    field_simp [hpos.ne', abs_ne_zero.mpr (norm_ne_zero_iff.mpr hd'0)]
    rw [abs_of_nonneg (norm_nonneg d')]
    ring
  have htri : ‖d - ‖d'‖⁻¹ • d'‖ ≤ ‖d - d'‖ + ‖d' - ‖d'‖⁻¹ • d'‖ := by
    simpa [dist_eq_norm] using dist_triangle d d' (‖d'‖⁻¹ • d')
  calc
    ‖d - ‖d'‖⁻¹ • d'‖ ≤ ‖d - d'‖ + ‖d' - ‖d'‖⁻¹ • d'‖ := htri
    _ ≤ r + r := by
      exact add_le_add hrd (by rw [hnorm_eq]; exact hnorm)
    _ = 2 * r := by ring

/-- The `ρ`-tube with midpoint `c` and unit direction `unitDir e₀ d`.

A thin *total* wrapper around the repository's own `Tube.ofMidpointDirection`: the only thing
added is that the direction argument need not already be a unit vector, which is what lets the
covering family be a plain `Finset.image` over a product of nets with no dependent-membership
plumbing. -/
noncomputable def tubeOfCenterDir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] (ρ : NNReal) {e₀ : E} (he₀ : ‖e₀‖ = 1) (c d : E) : Tube ρ E :=
  Tube.ofMidpointDirection ρ c (unitDir e₀ d) (norm_unitDir he₀ d)

@[simp] theorem tubeOfCenterDir_x {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] (ρ : NNReal) {e₀ : E} (he₀ : ‖e₀‖ = 1) (c d : E) :
    (tubeOfCenterDir ρ he₀ c d).x = c - (1 / 2 : ℝ) • unitDir e₀ d := rfl

@[simp] theorem tubeOfCenterDir_y {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] (ρ : NNReal) {e₀ : E} (he₀ : ‖e₀‖ = 1) (c d : E) :
    (tubeOfCenterDir ρ he₀ c d).y = c + (1 / 2 : ℝ) • unitDir e₀ d := rfl

/-- **Whole-leaf containment from closeness of midpoint and direction.**

If the midpoint of a `δ`-tube is within `r` of `c` and its direction is within `2r` of
`unitDir e₀ d`, then the whole `δ`-tube lies inside `tubeOfCenterDir ρ he₀ c d`, provided
`δ + 2r ≤ ρ`.

The endpoints of a tube are `midpoint ∓ (1/2) • direction`, so each endpoint moves by at most
`r + (1/2)(2r) = 2r`, and `Kakeya.Tube.carrier_subset_of_endpoints_close` applies with that budget.
This is the step that makes the cover *leafwise* rather than a mere set cover. -/
theorem Tube.carrier_subset_tubeOfCenterDir
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {δ ρ : NNReal} (T : Tube δ E) {e₀ : E} (he₀ : ‖e₀‖ = 1) (c d : E) {r : ℝ}
    (hc : dist T.midpoint c ≤ r)
    (hdu : ‖T.direction - unitDir e₀ d‖ ≤ 2 * r)
    (hr : (δ : ℝ) + 2 * r ≤ (ρ : ℝ)) :
    T.carrier ⊆ (tubeOfCenterDir ρ he₀ c d).carrier := by
  have hxid : T.midpoint - (1 / 2 : ℝ) • T.direction = T.x := by
    simp only [Tube.midpoint, Tube.direction]
    module
  have hyid : T.midpoint + (1 / 2 : ℝ) • T.direction = T.y := by
    simp only [Tube.midpoint, Tube.direction]
    module
  have hx : dist T.x (tubeOfCenterDir ρ he₀ c d).x ≤ 2 * r := by
    rw [tubeOfCenterDir_x, ← hxid, dist_eq_norm,
      show (T.midpoint - (1 / 2 : ℝ) • T.direction) - (c - (1 / 2 : ℝ) • unitDir e₀ d)
          = (T.midpoint - c) - (1 / 2 : ℝ) • (T.direction - unitDir e₀ d) from by module]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [← dist_eq_norm]
    linarith [hc, hdu]
  have hy : dist T.y (tubeOfCenterDir ρ he₀ c d).y ≤ 2 * r := by
    rw [tubeOfCenterDir_y, ← hyid, dist_eq_norm,
      show (T.midpoint + (1 / 2 : ℝ) • T.direction) - (c + (1 / 2 : ℝ) • unitDir e₀ d)
          = (T.midpoint - c) + (1 / 2 : ℝ) • (T.direction - unitDir e₀ d) from by module]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [← dist_eq_norm]
    linarith [hc, hdu]
  exact Tube.carrier_subset_of_endpoints_close T (tubeOfCenterDir ρ he₀ c d) hx hy hr

/-- The cardinality of the leafwise cover: the square of the size of a `1/16`-net of `B₁`, since one
net serves both the position and the direction coordinate.  Depends only on the ambient
dimension. -/
noncomputable abbrev leafwiseCoverConst (n : ℕ) : NNReal :=
  (FiniteDimensional.discretizeBallAt.C n * 16 ^ n) ^ 2

/-- **Milestone 1/2: the leafwise `O(1)` cover by `ρ`-tubes.**

Every `δ`-tube of the family lies *entirely* inside one of at most
`leafwiseCoverConst (finrank ℝ E)` tubes of radius exactly `ρ`.  The constant is absolute — it
depends only on the ambient dimension, and on neither `δ`, `ρ`, `a`, `b` nor `θ`.

Construction: let `P` be a `1/16`-net of `B₁` (`FiniteDimensional.discretizeBallAt`).  A leaf `T`
has midpoint in `B₁` and unit direction, so *both* lie in `B₁`; pick `c'` and `d'` in `P` within
`1/16` of them.  The covering tube is `tubeOfCenterDir ρ he₀ c' d'`.  Normalising `d'` moves it by
at most a further `1/16`, so the directions differ by at most `1/8` and the endpoints by at most
`1/16 + (1/2)(1/8) = 1/8`; with `δ ≤ 1/4 ≤ ρ - 1/8` this is exactly the budget of
`Tube.carrier_subset_of_endpoints_close`. -/
theorem exists_leafwise_tube_cover
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} {δ ρ : NNReal} (hδ0 : 0 < δ) (hδ : (δ : ℝ) ≤ 1 / 4) (hρ : (1 : ℝ) / 2 ≤ (ρ : ℝ))
    (q : Finset ι) (T : ι → Tube δ E)
    (hball : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) :
    ∃ F : Finset (Tube ρ E),
      (F.card : NNReal) ≤ leafwiseCoverConst (Module.finrank ℝ E) ∧
      ∀ i ∈ q, ∃ V ∈ F, (T i).carrier ⊆ V.carrier := by
  classical
  -- A fixed unit vector: the fallback direction when a net point is zero.
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  set e₀ : E := ‖v‖⁻¹ • v with he₀def
  have he₀ : ‖e₀‖ = 1 := by
    rw [he₀def, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  -- A `1/16`-net of the closed unit ball, serving both position and direction.
  obtain ⟨P, hPcard, hPmem, hPnet⟩ :=
    FiniteDimensional.discretizeBallAt (E := E) (r := (1 / 16 : NNReal)) (R := (1 : NNReal))
      (by norm_num) (by exact_mod_cast (by norm_num : (1 / 16 : ℝ) ≤ (1 : ℝ)))
  let f : E × E → Tube ρ E := fun p => tubeOfCenterDir ρ he₀ p.1 p.2
  refine ⟨(P ×ˢ P).image f, ?_, ?_⟩
  · -- Cardinality: the image is no larger than the product of the two nets.
    have hPcard' : (P.card : NNReal) ≤
        FiniteDimensional.discretizeBallAt.C (Module.finrank ℝ E) * 16 ^ Module.finrank ℝ E := by
      have hratio : ((1 : NNReal) / (1 / 16 : NNReal)) = 16 := by norm_num
      simpa [hratio] using hPcard
    have hPcardSq : ((P.card : NNReal) * (P.card : NNReal)) ≤
        (FiniteDimensional.discretizeBallAt.C (Module.finrank ℝ E) *
          16 ^ Module.finrank ℝ E) ^ 2 := by
      rw [pow_two]
      exact mul_le_mul hPcard' hPcard' (by positivity) (by positivity)
    calc
      (((P ×ˢ P).image f).card : NNReal)
          ≤ ((P ×ˢ P).card : NNReal) := by
            exact_mod_cast Finset.card_image_le
      _ = (P.card : NNReal) * (P.card : NNReal) := by
        rw [Finset.card_product, Nat.cast_mul]
      _ ≤ (FiniteDimensional.discretizeBallAt.C (Module.finrank ℝ E) *
            16 ^ Module.finrank ℝ E) ^ 2 := hPcardSq
      _ = leafwiseCoverConst (Module.finrank ℝ E) := by
        rw [leafwiseCoverConst]
  · -- Covering: midpoint and direction of `T i` both lie in the unit ball, near a net point each.
    intro i hi
    have hmid : (T i).midpoint ∈ Metric.closedBall (0 : E) ((1 : NNReal) : ℝ) :=
      Tube.midpoint_mem_closedBall_of_subset hδ0 (T i) (hball i hi)
    have hdirnorm : ‖(T i).direction‖ = 1 := Tube.norm_direction (T i)
    have hdirmem : (T i).direction ∈ Metric.closedBall (0 : E) ((1 : NNReal) : ℝ) := by
      simp [Metric.mem_closedBall, dist_zero_right, hdirnorm]
    obtain ⟨c', hc'P, hc'⟩ := hPnet _ hmid
    obtain ⟨d', hd'P, hd'⟩ := hPnet _ hdirmem
    refine ⟨tubeOfCenterDir ρ he₀ c' d',
      Finset.mem_image_of_mem (f := f) (a := (c', d')) (Finset.mem_product.mpr ⟨hc'P, hd'P⟩), ?_⟩
    refine Tube.carrier_subset_tubeOfCenterDir (T i) he₀ c' d' (r := 1 / 16) ?_ ?_ ?_
    · exact_mod_cast hc'
    · exact norm_sub_unitDir_le he₀ hdirnorm (by exact_mod_cast hd') (by norm_num)
    · linarith

/-- **Milestone 3: the cover, in the shape the cross-parent counting consumes.**

Exactly the `hF` hypothesis of `Tube.UniformTubeSet.card_contributingNodes_le_of_cover` and
the `hcov` datum of `Kakeya.factoringAndMultPropCombined`, at the external radius `ρ` and with the
explicit constant `leafwiseCoverConst`.  The container `K` plays no role: the cover catches every
leaf of the family, a fortiori every leaf inside `K`. -/
theorem exists_leafwise_cover_of_localScales
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} {δ ρ : NNReal} (hδ0 : 0 < δ) (hδ : (δ : ℝ) ≤ 1 / 4) (hρ : (1 : ℝ) / 2 ≤ (ρ : ℝ))
    (q : Finset ι) (T : ι → Tube δ E)
    (hball : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (K : ConvexSpaceBody E) :
    ∃ F : Finset (Tube ρ E),
      (F.card : NNReal) ≤ leafwiseCoverConst (Module.finrank ℝ E) ∧
      ∀ i ∈ q, (T i).toConvexSpaceBody ≤ K →
        ∃ V ∈ F, (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody := by
  obtain ⟨F, hFcard, hF⟩ := exists_leafwise_tube_cover hδ0 hδ hρ q T hball
  refine ⟨F, hFcard, ?_⟩
  intro i hi _
  obtain ⟨V, hV, hsub⟩ := hF i hi
  exact ⟨V, hV, (SetLike.coe_subset_coe (S := (T i).toConvexSpaceBody)
    (T := V.toConvexSpaceBody)).mpr hsub⟩

/-! ### Milestone 4: external parents versus hierarchy nodes

The cross-parent count is carried out on *hierarchy nodes*, but the Katz--Tao property lives on the
*external* factorization classes: `Kakeya.PlankFactorization` makes the outer bodies of each single
`Fz k` a Katz--Tao family (`ConvexSpaceBody.Factorization.isKatzTao`), and says nothing whatever
about a union over several `k`.

Neither of the two candidate reconciliations survives contact with the definitions.

* *Each external class maps to one hierarchy node, so the estimate stays external.*  The map
  `par` is not injective on external classes: the chosen node has radius
  `gridScale δ N kLev ≥ ρ`, possibly much larger than `ρ`, so many external `ρ`-tubes can share a
  node.  Bounding the number of contributing *nodes* therefore does not bound the number of
  contributing *external parents*.
* *Union the external classes sitting inside one node.*  This needs `IsKatzTao` for a union of
  Katz--Tao families.  Katz--Tao is inherited by *subsets*, not by unions, and invoking downward
  inheritance here would be using it in the wrong direction.  This is the same failure mode as the
  original GWZ gap.

The resolution is not to regroup at all: group by the external parent, where the hypothesis
actually holds, and bound the number of contributing external parents separately.  The summation
step is `Kakeya.card_filter_le_of_parentwise`, which is already generic in the label type; the
instance below records the external-parent grouping under its own name so that no call site has to
choose between the two families by accident.  See
`Kakeya.card_planks_le_of_externalParentwise`, stated below next to the summation lemma it uses. -/

/-! ### The unit-radius fallback cover

The covering datum that `Tube.UniformTubeSet.card_contributingNodes_le_of_cover` consumes
asks for *leafwise* containment: every leaf lying in the container must lie in a single member of
the family.  A mere set cover is not enough, because a leaf can straddle two members.

Two facts make the honest answer short.

* The covering radius must strictly exceed the leaf radius.  A `Tube δ` contains balls of radius
  `δ`, so it can only sit inside a `Tube ρ` when the axes nearly coincide; with `δ = ρ` allowed by
  the hypotheses of Proposition 6.6(A), no *finite* family of `ρ`-tubes can catch every leaf
  leafwise.  Some fixed enlargement of the radius is therefore unavoidable, exactly as anticipated.
* Once the radius is enlarged to `1`, the family collapses to a single tube: every leaf lies in
  `B_1` by hypothesis, and a `1`-tube whose axis passes through the origin contains `B_1`.

So the honest covering constant is `Ccover = 1` at covering radius `1`. No net, no discretisation
of position or direction, and no `δ ^ (-η)` loss. -/

/-- A `1`-tube through the origin contains the closed unit ball, hence every leaf of a family
contained in `B_1`.  This is the leafwise covering datum with a single member. -/
theorem exists_tube_one_superset_of_subset_unitBall
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} {δ : NNReal} (q : Finset ι) (T : ι → Tube δ E)
    (hball : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) :
    ∃ V : Tube (1 : NNReal) E,
      ∀ i ∈ q, (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody := by
  classical
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  let e : E := (‖x‖⁻¹ : ℝ) • x
  have he : ‖e‖ = 1 := by
    dsimp [e]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)
  let x₀ : E := -((1 / 2 : ℝ) • e)
  let y₀ : E := (1 / 2 : ℝ) • e
  have hdist : dist x₀ y₀ = 1 := by
    rw [dist_eq_norm]
    calc
      ‖x₀ - y₀‖ = ‖(-1 : ℝ) • e‖ := by
        congr 1
        dsimp [x₀, y₀]
        module
      _ = 1 := by simp [he]
  let V : Tube (1 : NNReal) E := Tube.mk' (1 : NNReal) hdist
  have hc : (0 : E) ∈ segment ℝ V.x V.y := by
    change (0 : E) ∈ segment ℝ x₀ y₀
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    dsimp [x₀, y₀]
    module
  have hball_in : Metric.closedBall (0 : E) ((1 : NNReal) : ℝ) ⊆ V.carrier :=
    Tube.closedBall_subset_carrier_of_mem_segment V hc
  have hball_in' : Metric.closedBall (0 : E) (1 : ℝ) ⊆ V.carrier := by
    simpa using hball_in
  refine ⟨V, ?_⟩
  intro i hi
  exact (SetLike.coe_subset_coe (S := (T i).toConvexSpaceBody)
    (T := V.toConvexSpaceBody)).mpr ((hball i hi).trans hball_in')

/-- **The bounded leafwise cover, packaged for the cross-parent adapter.**

Exactly the shape of the `hcov` datum of `Kakeya.factoringAndMultPropCombined` and of the covering
hypothesis of `Tube.UniformTubeSet.card_contributingNodes_le_of_cover`, with covering radius
`1` and `Ccover = 1`, an absolute constant.  The container `K` is irrelevant: the bound holds for
every leaf of the family, whether or not it lies in `K`. -/
theorem exists_leafwise_cover_unitRadius
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} {δ : NNReal} (q : Finset ι) (T : ι → Tube δ E)
    (hball : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (K : ConvexSpaceBody E) :
    ∃ F : Finset (Tube (1 : NNReal) E), (F.card : ℝ≥0) ≤ 1 ∧
      ∀ i ∈ q, (T i).toConvexSpaceBody ≤ K →
        ∃ V ∈ F, (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody := by
  obtain ⟨V, hV⟩ := exists_tube_one_superset_of_subset_unitBall q T hball
  refine ⟨{V}, ?_, ?_⟩
  · simp
  · intro i hi _
    exact ⟨V, Finset.mem_singleton_self V, hV i hi⟩

end Kakeya

namespace Tube

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-! ### Counting the coarse parents that contribute to a container -/

/-- **The hierarchy nodes at grid index `k` that contribute to a container `K`.**

A node `j` contributes when some leaf of `s` lies in both the node and `K`.  This is exactly the
filter that `UniformTubeSet.boundedOverlap` bounds, with the grid-radius test tube `V` replaced by
an arbitrary convex body, so that the container may be a thickened plank.

Contribution is stated through an *occupied* leaf, never through the mere formal existence of an
outer cell: a factorization part is nonempty, and it is the leaf inside it that certifies the
parent. -/
def UniformTubeSet.contributingNodes {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C) (k : ℕ) (K : ConvexSpaceBody E) :
    Finset ι :=
  (𝒰.cover.indexSet k).filter (fun j => ∃ i ∈ s,
    (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
    (T i).toConvexSpaceBody ≤ K)

/-- **Cross-parent counting lemma.**

If every leaf of `s` that lies in the container `K` already lies in one of the `F.card` many
grid-radius tubes `F`, then at most `F.card * C` hierarchy nodes at level `k` contribute to `K`.

Each contributing node is certified by a leaf `i ∈ s` inside both the node and `K`; that leaf lies
in some `V ∈ F`, so the node is counted by `UniformTubeSet.boundedOverlap` at `V`, which admits at
most `C` nodes.  Summing over `F` gives the bound.

The covering hypothesis is deliberately stated leafwise (`each leaf in K lies in some member of
F`) and not as a set cover `K ⊆ ⋃ V ∈ F, V`.  A set cover is *not* enough: a leaf could straddle
two members of the cover and lie in neither.  The leafwise form is what a cover at a radius
comparable to the container's short axes actually supplies, and it is the honest hypothesis. -/
theorem UniformTubeSet.card_contributingNodes_le {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C) {k : ℕ} (hk : k ≤ N)
    (K : ConvexSpaceBody E) (F : Finset (Tube (gridScale δ N k) E))
    (hF : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ K →
      ∃ V ∈ F, (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) :
    ((𝒰.contributingNodes k K).card : NNReal) ≤ (F.card : NNReal) * C := by
  classical
  let g : Tube (gridScale δ N k) E → Finset ι := fun V =>
    (𝒰.cover.indexSet k).filter (fun j => ∃ i ∈ s,
      (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
      (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)
  have hsub : 𝒰.contributingNodes k K ⊆ F.biUnion g := by
    intro j hj
    simp only [UniformTubeSet.contributingNodes, Finset.mem_filter] at hj
    rcases hj with ⟨hjind, ⟨i, hi, hTij, hTiK⟩⟩
    rcases hF i hi hTiK with ⟨V, hV, hTiV⟩
    exact Finset.mem_biUnion.mpr ⟨V, hV, by
      simp only [g, Finset.mem_filter]
      exact ⟨hjind, ⟨i, hi, hTij, hTiV⟩⟩⟩
  have hcard : (𝒰.contributingNodes k K).card ≤ ∑ V ∈ F, (g V).card := by
    exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hg : ∀ V ∈ F, ((g V).card : NNReal) ≤ C := by
    intro V hV
    simpa [g] using 𝒰.boundedOverlap k hk V
  calc
    ((𝒰.contributingNodes k K).card : NNReal)
        ≤ ((∑ V ∈ F, (g V).card : ℕ) : NNReal) := by
      exact Nat.cast_le.mpr hcard
    _ = ∑ V ∈ F, ((g V).card : NNReal) := by
      exact Nat.cast_sum (s := F) (f := fun V => (g V).card)
    _ ≤ ∑ V ∈ F, C := by
      exact Finset.sum_le_sum hg
    _ = (F.card : NNReal) * C := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-! ### From exact grid radii to arbitrary scales

`UniformTubeSet.boundedOverlap` is stated only for test tubes of the *exact* grid radius
`gridScale δ N k`, while Proposition 6.6(A) is quantified over an arbitrary coarse scale
`ρ ∈ [δ, 1]`.  The grid has only `N = ⌈log log (1/δ)⌉` levels, so consecutive radii differ by the
factor `δ ^ (1/N)`, which is *not* `O(1)`: an arbitrary `ρ` is in general nowhere near a grid
radius, and no rounding argument can identify the two.

The resolution below does not round `ρ` to a grid radius and does not lose any constant.  A tube of
radius `ρ` is *contained* in the tube with the same axis and the larger radius `gridScale δ N k`
whenever `ρ ≤ gridScale δ N k` (`Tube.le_rescale`), and `contributingNodes` only ever tests
leaves for containment in the container.  So the exact-grid bound applies verbatim, with the same
constant `C`.

What the sparse grid does cost is the *level*: the finest grid level whose radius still dominates
`ρ` is `gridLevelOf δ N ρ`, and its radius can exceed `ρ` by as much as `δ ^ (-1/N)`
(`gridScale_gridLevelOf_lt_mul`).  That is where the `log log` sparsity of the grid shows up — as a
coarsening of the parent scale, not as a multiplicative loss in the overlap count.  Downstream it is
the within-parent Katz--Tao input, not this lemma, that has to be supplied at the coarser level.

No
essential distinctness of coarse parents is used anywhere below. -/

/-- Grid radii are antitone in the level. -/
theorem gridScale_le_gridScale_of_le {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (N : ℕ)
    {j k : ℕ} (hjk : j ≤ k) : gridScale δ N k ≤ gridScale δ N j := by
  unfold gridScale
  exact NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1
    (div_le_div_of_nonneg_right (by exact_mod_cast hjk) (Nat.cast_nonneg N))

/-- One step of the grid multiplies the radius by `δ ^ (1/N)`. -/
theorem gridScale_succ {δ : NNReal} (hδ0 : 0 < δ) (N k : ℕ) :
    gridScale δ N (k + 1) = gridScale δ N k * δ ^ ((1 : ℝ) / (N : ℝ)) := by
  simp only [gridScale]
  rw [← NNReal.rpow_add hδ0.ne']
  congr 1
  push_cast
  rw [add_div]

/-- **The canonical level for an arbitrary scale**: the finest grid level whose radius still
dominates `ρ`.  Level `0` always qualifies, since `gridScale δ N 0 = 1`. -/
noncomputable def gridLevelOf (δ : NNReal) (N : ℕ) (ρ : NNReal) : ℕ :=
  Nat.findGreatest (fun k => ρ ≤ gridScale δ N k) N

theorem gridLevelOf_le (δ : NNReal) (N : ℕ) (ρ : NNReal) : gridLevelOf δ N ρ ≤ N :=
  Nat.findGreatest_le N

/-- The defining property of `gridLevelOf`: its radius dominates `ρ`. -/
theorem le_gridScale_gridLevelOf {δ : NNReal} (N : ℕ) {ρ : NNReal} (hρ1 : ρ ≤ 1) :
    ρ ≤ gridScale δ N (gridLevelOf δ N ρ) := by
  unfold gridLevelOf
  exact Nat.findGreatest_spec (P := fun k => ρ ≤ gridScale δ N k) (Nat.zero_le N) (by
    simpa [gridScale] using hρ1)

/-- Maximality of `gridLevelOf`: unless it is already the finest level `N`, the next finer grid
radius undershoots `ρ`. -/
theorem gridScale_gridLevelOf_succ_lt {δ : NNReal} {N : ℕ} {ρ : NNReal}
    (h : gridLevelOf δ N ρ < N) : gridScale δ N (gridLevelOf δ N ρ + 1) < ρ := by
  have hnlt : ¬ ρ ≤ gridScale δ N (gridLevelOf δ N ρ + 1) := by
    exact Nat.findGreatest_is_greatest (P := fun k : ℕ => ρ ≤ gridScale δ N k) (n := N)
      (Nat.lt_succ_self _) (Nat.succ_le_of_lt h)
  exact not_le.mp hnlt

/-- **The sparse-grid loss, made explicit.**  The canonical level's radius exceeds `ρ` by strictly
less than the factor `δ ^ (-1/N)`.  With `N = ⌈log log (1/δ)⌉` this factor is
`exp (log (1/δ) / ⌈log log (1/δ)⌉)`, which is superpolynomial in `1/δ` — the coarsening is real and
is not absorbable as a constant.  It is recorded here so that consumers choosing the level through
`gridLevelOf` can see exactly how much coarser their parents may be than `ρ`. -/
theorem gridScale_gridLevelOf_lt_mul {δ : NNReal} (hδ0 : 0 < δ) {N : ℕ} {ρ : NNReal}
    (h : gridLevelOf δ N ρ < N) :
    gridScale δ N (gridLevelOf δ N ρ) < ρ * δ ^ (-(1 : ℝ) / (N : ℝ)) := by
  let k : ℕ := gridLevelOf δ N ρ
  let t : NNReal := δ ^ ((1 : ℝ) / (N : ℝ))
  have ht_pos : 0 < t := by
    dsimp [t]
    exact NNReal.rpow_pos hδ0
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have h1 : gridScale δ N k * t < ρ := by
    dsimp [t]
    rw [← gridScale_succ hδ0 N k]
    dsimp [k]
    exact gridScale_gridLevelOf_succ_lt h
  have h2 : gridScale δ N k < ρ * t⁻¹ := by
    rw [← mul_lt_mul_iff_right₀ ht_pos]
    rw [← mul_assoc, mul_comm t ρ, mul_assoc, mul_inv_cancel₀ ht_ne, mul_one]
    simpa [mul_comm] using h1
  have ht_inv : δ ^ (-(1 : ℝ) / (N : ℝ)) = t⁻¹ := by
    dsimp [t]
    rw [neg_div]
    exact NNReal.rpow_neg δ ((1 : ℝ) / (N : ℝ))
  rw [ht_inv]
  simpa [k] using h2

/-- **Pushing a covering family up to a larger radius.**

Replacing each covering tube by the tube with the same axis and the larger radius `ρ'` preserves
both the cardinality bound and the leafwise covering property, since `Tube.le_rescale` puts
each tube inside its own rescale.  This is the whole content of the arbitrary-scale bridge: a
covering datum produced at an external coarse scale `ρ` is usable at any grid radius `ρ' ≥ ρ`, with
no loss of constant.

Stated for an abstract family of bodies `B` and an abstract selection predicate `P` so that it
serves both the plain and the shaded/thickened-plank consumers. -/
theorem exists_cover_rescale {ρ ρ' : NNReal} (hρ : ρ ≤ ρ')
    {α : Type*} (q : Finset α) (B : α → ConvexSpaceBody E) (P : α → Prop)
    {Cgeom : NNReal} (F : Finset (Tube ρ E)) (hFcard : (F.card : NNReal) ≤ Cgeom)
    (hF : ∀ i ∈ q, P i → ∃ V ∈ F, B i ≤ V.toConvexSpaceBody) :
    ∃ F' : Finset (Tube ρ' E), (F'.card : NNReal) ≤ Cgeom ∧
      ∀ i ∈ q, P i → ∃ V ∈ F', B i ≤ V.toConvexSpaceBody := by
  classical
  refine ⟨F.image (fun V => V.rescale ρ'), ?_, ?_⟩
  · refine le_trans ?_ hFcard
    exact Nat.cast_le.mpr Finset.card_image_le
  · intro i hi hPi
    obtain ⟨V, hV, hBV⟩ := hF i hi hPi
    exact ⟨V.rescale ρ', Finset.mem_image_of_mem _ hV, hBV.trans (V.le_rescale hρ)⟩

/-- **A qualifying grid level always exists.**

The side condition `ρ ≤ gridScale δ N kLev` that `Kakeya.factoringAndMultPropCombined` carries is
never vacuous: `gridLevelOf δ N ρ` witnesses it for every `ρ ≤ 1`, and by
`gridScale_gridLevelOf_lt_mul` it is the *best* witness, overshooting `ρ` by less than
`δ ^ (-1/N)`. -/
theorem exists_gridLevel_le_of_le_one {δ : NNReal} (N : ℕ) {ρ : NNReal} (hρ1 : ρ ≤ 1) :
    ∃ k, k ≤ N ∧ ρ ≤ gridScale δ N k :=
  ⟨gridLevelOf δ N ρ, gridLevelOf_le δ N ρ, le_gridScale_gridLevelOf N hρ1⟩

/-- `contributingNodes` is monotone in the container. -/
theorem UniformTubeSet.contributingNodes_mono {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C) (k : ℕ) {K K' : ConvexSpaceBody E}
    (hKK' : K ≤ K') : 𝒰.contributingNodes k K ⊆ 𝒰.contributingNodes k K' := by
  intro j hj
  simp only [UniformTubeSet.contributingNodes, Finset.mem_filter] at hj ⊢
  rcases hj with ⟨hjind, i, hi, hTij, hTiK⟩
  exact ⟨hjind, i, hi, hTij, hTiK.trans hKK'⟩

/-- **Arbitrary-scale cross-parent counting, covering family at an arbitrary radius.**

The generalisation of `UniformTubeSet.card_contributingNodes_le` in which the covering tubes have an
arbitrary radius `ρ ≤ gridScale δ N k` rather than the exact grid radius.  This is what lets
Proposition 6.6(A) state its covering datum at the external coarse scale `ρ` and still consume
`boundedOverlap`, which lives at grid radii only.

No constant is lost: each covering tube is replaced by the tube with the same axis and the grid
radius, which contains it. -/
theorem UniformTubeSet.card_contributingNodes_le_of_cover {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C)
    {k : ℕ} (hk : k ≤ N) (K : ConvexSpaceBody E)
    {ρ : NNReal} (hρ : ρ ≤ gridScale δ N k) (F : Finset (Tube ρ E))
    (hF : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ K →
      ∃ V ∈ F, (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) :
    ((𝒰.contributingNodes k K).card : NNReal) ≤ (F.card : NNReal) * C := by
  classical
  set F' : Finset (Tube (gridScale δ N k) E) := F.image (fun V => V.rescale (gridScale δ N k))
  have hcard' : F'.card ≤ F.card := Finset.card_image_le
  have hF' : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ K →
      ∃ V' ∈ F', (T i).toConvexSpaceBody ≤ V'.toConvexSpaceBody := by
    intro i hi hiK
    obtain ⟨V, hV, hTiV⟩ := hF i hi hiK
    exact ⟨V.rescale (gridScale δ N k), Finset.mem_image_of_mem _ hV,
      hTiV.trans (V.le_rescale hρ)⟩
  calc ((𝒰.contributingNodes k K).card : NNReal)
      ≤ (F'.card : NNReal) * C := 𝒰.card_contributingNodes_le hk K F' hF'
    _ ≤ (F.card : NNReal) * C := by gcongr

/-- **Arbitrary-scale cross-parent counting against a single `ρ`-tube.**

For every `ρ ≤ gridScale δ N k` and every `ρ`-tube `V`, at most `C` level-`k` nodes contribute a
leaf lying inside `V`.  Contribution is leaf-mediated throughout: no geometric overlap of the parent
tubes themselves is asserted, and the parents are not assumed essentially distinct. -/
theorem UniformTubeSet.card_contributingNodes_tube_le {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C)
    {k : ℕ} (hk : k ≤ N) {ρ : NNReal} (hρ : ρ ≤ gridScale δ N k) (V : Tube ρ E) :
    ((𝒰.contributingNodes k V.toConvexSpaceBody).card : NNReal) ≤ C := by
  have hF : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody →
      ∃ V' ∈ ({V} : Finset (Tube ρ E)), (T i).toConvexSpaceBody ≤ V'.toConvexSpaceBody :=
    fun i _ hiV => ⟨V, Finset.mem_singleton_self V, hiV⟩
  have h := 𝒰.card_contributingNodes_le_of_cover hk V.toConvexSpaceBody hρ {V} hF
  simpa using h

/-- **The arbitrary-scale theorem at the canonical level.**

Instantiation of `UniformTubeSet.card_contributingNodes_le_of_cover` at `k = gridLevelOf δ N ρ`,
which requires nothing of `ρ` beyond `ρ ≤ 1`.  This is the form Proposition 6.6(A) uses: the coarse
scale `ρ` is arbitrary, the level is determined by it, and the count is `F.card * C` with no
grid-sparsity factor. -/
theorem UniformTubeSet.card_contributingNodes_gridLevelOf_le {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C)
    {ρ : NNReal} (hρ1 : ρ ≤ 1) (K : ConvexSpaceBody E) (F : Finset (Tube ρ E))
    (hF : ∀ i ∈ s, (T i).toConvexSpaceBody ≤ K →
      ∃ V ∈ F, (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) :
    ((𝒰.contributingNodes (gridLevelOf δ N ρ) K).card : NNReal) ≤ (F.card : NNReal) * C :=
  𝒰.card_contributingNodes_le_of_cover (gridLevelOf_le δ N ρ) K
    (le_gridScale_gridLevelOf N hρ1) F hF

/-! ### Where the external parent package comes from

Proposition 6.6(A) consumes leaf-mediated bounded overlap of its *external* coarse family
`(R k)_{k ∈ r}`, and that is not a consequence of the hierarchy: hierarchy `boundedOverlap` counts
nodes at *exact* grid radii, and consecutive grid radii `δ ^ (k/N)` with `N = ssfGridLen δ` differ
superpolynomially, so a node at the level above an arbitrary `ρ` is not comparable to `ρ`.

What *is* provable — and is the honest reference point for the missing construction — is the exact
grid case: when the coarse family is taken to be the hierarchy's own nodes at a grid level, the
external hypothesis is literally Definition 2.1(ii).  The lemma below is that instance.  The
genuinely missing ingredient for arbitrary `ρ` is therefore not a rounding argument but the
*construction* of a coarse family at a non-grid scale together with its bounded overlap; this is the
correct replacement for the sorried `Kakeya.Tube.IsUniform.spread`, whose own condition demands
pairwise essential distinctness of the coarse family and is not used anywhere here. -/

/-- **The external bounded-overlap hypothesis, at an exact grid level.**

Taking the coarse family to be `𝒰.cover.tube k` with assignment `𝒰.cover.assign k` and index set
`𝒰.cover.indexSet k`, the leaf-mediated external overlap bound required by Proposition 6.6(A) is
exactly `UniformTubeSet.boundedOverlap`: an assigned leaf lies in its own node by
`GridCoverSystem.le_tube_assign`, so the external filter is a subset of the hierarchy one. -/
theorem UniformTubeSet.extOverlap_of_gridLevel {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C)
    {k : ℕ} (hk : k ≤ N) (V : Tube (gridScale δ N k) E) :
    ((({j ∈ 𝒰.cover.indexSet k | ∃ i ∈ s, 𝒰.cover.assign k i = j ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody}).card : NNReal)) ≤ C := by
  classical
  have hsub : ({j ∈ 𝒰.cover.indexSet k | ∃ i ∈ s, 𝒰.cover.assign k i = j ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody} : Finset ι) ⊆
      (𝒰.cover.indexSet k).filter (fun j => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    rcases hj with ⟨hjIn, i, hi, hassign, hle⟩
    refine ⟨hjIn, i, hi, ?_, hle⟩
    rw [← hassign]
    exact 𝒰.cover.le_tube_assign k hk i hi
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (𝒰.boundedOverlap k hk V)

end Tube

namespace Kakeya

open _root_.Tube

/-! ### Summing a parentwise bound over a controlled parent set -/

/-- **Parentwise summation.**  If every counted element carries a label in the finite set `P` and
each label class contributes at most `m`, the total is at most `P.card * m`.

This is the combinatorial half of the repair: the global count over all outer planks is the sum of
the within-parent counts over the contributing parents, never a single within-parent count. -/
theorem card_filter_le_of_parentwise {α : Type*} {ι : Type*}
    {ts : Finset α} {p : α → Prop} {par : α → ι} {P : Finset ι}
    (hpar : ∀ x ∈ ts, p x → par x ∈ P) {m : ℝ≥0}
    (hlocal : ∀ j ∈ P, (({x ∈ ts | p x ∧ par x = j}).card : ℝ≥0) ≤ m) :
    (({x ∈ ts | p x}).card : ℝ≥0) ≤ (P.card : ℝ≥0) * m := by
  classical
  let f : ι → Finset α := fun j => {x ∈ ts | p x ∧ par x = j}
  have hsub : ({x ∈ ts | p x} : Finset α) ⊆ P.biUnion f := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxts, hpx⟩
    exact Finset.mem_biUnion.mpr ⟨par x, hpar x hxts hpx, by simp [f, hxts, hpx]⟩
  have hcard : ({x ∈ ts | p x}).card ≤ ∑ j ∈ P, (f j).card := by
    calc
      ({x ∈ ts | p x}).card ≤ (P.biUnion f).card := Finset.card_le_card hsub
      _ ≤ ∑ j ∈ P, (f j).card := Finset.card_biUnion_le
  have hsum : (∑ j ∈ P, ((f j).card : ℝ≥0)) ≤ (P.card : ℝ≥0) * m := by
    calc
      (∑ j ∈ P, ((f j).card : ℝ≥0)) ≤ ∑ j ∈ P, m :=
        Finset.sum_le_sum (fun j hj => hlocal j hj)
      _ = (P.card : ℝ≥0) * m := by
        simp [Finset.sum_const, nsmul_eq_mul]
  calc
    (({x ∈ ts | p x}).card : ℝ≥0) ≤ (∑ j ∈ P, ((f j).card : ℝ≥0)) := by
      exact_mod_cast hcard
    _ ≤ (P.card : ℝ≥0) * m := hsum

/-- **Milestone 4: the global plank count, grouped by the EXTERNAL factorization parent.**

`ext x` is the external parent label of the outer plank `x` (the `k` with `x` produced by `Fz k`),
`r` the external index set, and `m` the within-class Katz--Tao bound — which for the
`Kakeya.PlankFactorization` of a single `k` is exactly the available hypothesis, since
`ConvexSpaceBody.Factorization.isKatzTao` is a property of each `Fz k` separately.  The conclusion
is the global count, with the number of contributing external parents as the only extra factor.

Contrast `Kakeya.card_le_of_parentwise_of_boundedOverlap`, which groups by hierarchy node: that
version obtains its parent count from `boundedOverlap`, but then needs the within-class estimate on
a *node* class, i.e. on a union of several external classes — and Katz--Tao is inherited by subsets,
not by unions.  See the discussion above `Kakeya.exists_leafwise_cover_of_localScales`. -/
theorem card_planks_le_of_externalParentwise
    {κ' κ : Type*} {ts : Finset κ'} {p : κ' → Prop} {ext : κ' → κ} {r : Finset κ}
    (hext : ∀ x ∈ ts, p x → ext x ∈ r) {m : ℝ≥0}
    (hKT : ∀ k ∈ r, (({x ∈ ts | p x ∧ ext x = k}).card : ℝ≥0) ≤ m) :
    (({x ∈ ts | p x}).card : ℝ≥0) ≤ (r.card : ℝ≥0) * m :=
  card_filter_le_of_parentwise hext hKT

/-! ### The global concentration estimate -/

/-- **Global concentration from a parentwise bound plus bounded coarse overlap.**

This is the corrected replacement for the printed proof's `𝒲[W_θ] = 𝒲_{T_ρ}[W_θ]`.

* `hpar_mem` and `hocc` retain the parent label of each outer body and certify it by an actual
  occupied leaf of that parent's fibre — the leaf `i` lies in the parent node `𝒰.cover.tube k
  (par x)` *and* in the outer body `Wc x`.  Several distinct parents are allowed to contribute.
* `hF` is the covering datum for the container.
* `hlocal` is the within-parent estimate, supplied by the local Katz--Tao packing bound inside a
  single parent.  It is a hypothesis, not a consequence: it is where leaf essential distinctness
  enters, and `UniformTubeSet` does not provide that.

The conclusion multiplies the two controlled factors instead of discarding one of them. -/
theorem card_le_of_parentwise_of_boundedOverlap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} {κ' : Type*} {δ : NNReal} {q : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet q T N C) {k : ℕ} (hk : k ≤ N)
    {ts : Finset κ'} {Wc : κ' → ConvexSpaceBody E} {par : κ' → ι} {K : ConvexSpaceBody E}
    (hpar_mem : ∀ x ∈ ts, par x ∈ 𝒰.cover.indexSet k)
    (hocc : ∀ x ∈ ts, Wc x ≤ K → ∃ i ∈ q,
      (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k (par x)).toConvexSpaceBody ∧
      (T i).toConvexSpaceBody ≤ Wc x)
    (F : Finset (Tube (gridScale δ N k) E))
    (hF : ∀ i ∈ q, (T i).toConvexSpaceBody ≤ K →
      ∃ V ∈ F, (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)
    {m : ℝ≥0}
    (hlocal : ∀ j ∈ 𝒰.cover.indexSet k,
      (({x ∈ ts | Wc x ≤ K ∧ par x = j}).card : ℝ≥0) ≤ m) :
    (({x ∈ ts | Wc x ≤ K}).card : ℝ≥0) ≤ ((F.card : ℝ≥0) * C) * m := by
  let P : Finset ι := 𝒰.contributingNodes k K
  have hpar' : ∀ x ∈ ts, Wc x ≤ K → par x ∈ P := by
    intro x hx hKx
    unfold P UniformTubeSet.contributingNodes
    refine Finset.mem_filter.mpr ⟨hpar_mem x hx, ?_⟩
    rcases hocc x hx hKx with ⟨i, hi, hTi, hTiWc⟩
    exact ⟨i, hi, hTi, le_trans hTiWc hKx⟩
  have hlocal' : ∀ j ∈ P, (({x ∈ ts | Wc x ≤ K ∧ par x = j}).card : ℝ≥0) ≤ m := by
    intro j hj
    unfold P UniformTubeSet.contributingNodes at hj
    exact hlocal j ((Finset.mem_filter.mp hj).1)
  have hPA : (({x ∈ ts | Wc x ≤ K}).card : ℝ≥0) ≤ (P.card : ℝ≥0) * m := by
    exact card_filter_le_of_parentwise (p := fun x : κ' => Wc x ≤ K) (par := par) (P := P)
      hpar' hlocal'
  have hPC : (P.card : ℝ≥0) ≤ (F.card : ℝ≥0) * C := by
    unfold P
    exact UniformTubeSet.card_contributingNodes_le 𝒰 hk K F hF
  have hstep : (P.card : ℝ≥0) * m ≤ ((F.card : ℝ≥0) * C) * m := by
    exact mul_le_mul_left hPC m
  exact le_trans hPA hstep

/-- **The thick-plank concentration hypothesis of GWZ Lemma 6.4, proved cross-parent.**

Specialization of `Kakeya.card_le_of_parentwise_of_boundedOverlap` to the container
`K = W_j` thickened by `θ`, with the within-parent Katz--Tao bound in its usual form
`C_local * (b / a) * θ`.  The conclusion is literally the non-concentration hypothesis that
`Kakeya.FrostmanEstimate.plankEstimate` consumes, with concentration parameter

`M = C_geom * C_uniform * C_local * (b / a)`.

The `C_geom * C_uniform` prefactor is the price of the repair and must be carried honestly: with
`C_uniform ≤ δ ^ (-ηFine)` it is a `δ ^ (-O(ηFine))` loss, absorbed downstream into `δ ^ (-ε)` by
choosing `ηFine` small relative to the consumer's `ε`.  It is *not* an absolute constant, and the
printed `M ≲ b / a` is not recovered. -/
theorem plankConcentration_of_parentwise
    {ι : Type*} {κ' : Type*} {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {q : Finset ι} {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} {N : ℕ} {C : NNReal}
    (𝒰 : UniformTubeSet q T N C) {k : ℕ} (hk : k ≤ N)
    {ts : Finset κ'} {W : κ' → Plank a b hab hb1} {par : κ' → ι}
    {j : κ'} {θ : ℝ≥0} (hθ1 : θ ≤ 1) {Cgeom Clocal : ℝ≥0}
    (hpar_mem : ∀ x ∈ ts, par x ∈ 𝒰.cover.indexSet k)
    (hocc : ∀ x ∈ ts,
      (W x).carrier ⊆ (Plank.thickened (W j) θ hθ1).carrier → ∃ i ∈ q,
      (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k (par x)).toConvexSpaceBody ∧
      (T i).carrier ⊆ (W x).carrier)
    (F : Finset (Tube (gridScale δ N k) (EuclideanSpace ℝ (Fin 3))))
    (hFcard : (F.card : ℝ≥0) ≤ Cgeom)
    (hF : ∀ i ∈ q, (T i).carrier ⊆ (Plank.thickened (W j) θ hθ1).carrier →
      ∃ V ∈ F, (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)
    (hlocal : ∀ jn ∈ 𝒰.cover.indexSet k,
      (({x ∈ ts | (W x).carrier ⊆ (Plank.thickened (W j) θ hθ1).carrier ∧
        par x = jn}).card : ℝ≥0) ≤ Clocal * (b / a) * θ) :
    (({x ∈ ts | (W x).carrier ⊆
        (Plank.thickened (W j) θ hθ1).carrier}).card : ℝ≥0)
      ≤ (Cgeom * C * Clocal * (b / a)) * θ := by
  classical
  -- Bridge between the `ConvexSpaceBody` order and carrier inclusion.
  have hbridge : ∀ (X Y : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))),
      X ≤ Y ↔ (X.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Y.carrier := by
    intro X Y
    rfl
  let Kthick : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    (Plank.thickened (W j) θ hθ1).toConvexSpaceBody
  let Wc : κ' → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun x => (W x).toConvexSpaceBody
  have hcar : ∀ x : κ', (W x).carrier ⊆ (Plank.thickened (W j) θ hθ1).carrier ↔
      Wc x ≤ Kthick := by
    intro x
    change (Wc x).carrier ⊆ Kthick.carrier ↔ Wc x ≤ Kthick
    exact (hbridge (Wc x) Kthick).symm
  have hfilter_top : ts.filter (fun x : κ' => (W x).carrier ⊆
        (Plank.thickened (W j) θ hθ1).carrier) = ts.filter (fun x : κ' => Wc x ≤ Kthick) := by
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, hcar x]
  have hfilter_j : ∀ jn : ι, ts.filter (fun x : κ' => (W x).carrier ⊆
      (Plank.thickened (W j) θ hθ1).carrier ∧ par x = jn) =
      ts.filter (fun x : κ' => Wc x ≤ Kthick ∧ par x = jn) := by
    intro jn
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, hcar x]
  have hocc' : ∀ x ∈ ts, Wc x ≤ Kthick → ∃ i ∈ q,
      (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k (par x)).toConvexSpaceBody ∧
      (T i).toConvexSpaceBody ≤ Wc x := by
    intro x hx hxK
    rcases hocc x hx ((hcar x).mpr hxK) with ⟨i, hiq, hTi, hTiWc⟩
    exact ⟨i, hiq, hTi, (hbridge (T i).toConvexSpaceBody (Wc x)).mpr (by simpa using hTiWc)⟩
  have hF' : ∀ i ∈ q, (T i).toConvexSpaceBody ≤ Kthick →
      ∃ V ∈ F, (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody := by
    intro i hi hiK
    exact hF i hi ((hbridge (T i).toConvexSpaceBody Kthick).mp (by simpa [Kthick] using hiK))
  have hlocal' : ∀ jn ∈ 𝒰.cover.indexSet k,
      (({x ∈ ts | Wc x ≤ Kthick ∧ par x = jn}).card : ℝ≥0) ≤ Clocal * (b / a) * θ := by
    intro jn hjn
    rw [← hfilter_j jn]
    exact hlocal jn hjn
  have hmain : (({x ∈ ts | Wc x ≤ Kthick}).card : ℝ≥0) ≤
      ((F.card : ℝ≥0) * C) * (Clocal * (b / a) * θ) := by
    rw [← hfilter_top]
    exact card_le_of_parentwise_of_boundedOverlap (E := EuclideanSpace ℝ (Fin 3)) 𝒰 hk
      (Wc := Wc) (par := par) (K := Kthick) (m := Clocal * (b / a) * θ)
      hpar_mem hocc' F hF' hlocal'
  rw [hfilter_top]
  have hstep0 : ((F.card : ℝ≥0) * C) * (Clocal * (b / a) * θ) ≤
      (Cgeom * C) * (Clocal * (b / a) * θ) := by
    gcongr
  have hstep1 : (Cgeom * C) * (Clocal * (b / a) * θ) = (Cgeom * C * Clocal * (b / a)) * θ := by
    ring
  exact le_trans hmain (le_trans hstep0 (le_of_eq hstep1))

/-! ### The two adapters consumed by GWZ Proposition 6.6(A) -/

/-- **The parentwise package of GWZ Proposition 5.1, converted into the non-concentration
hypothesis of GWZ Lemma 6.4.**

This is `Kakeya.plankConcentration_of_parentwise` phrased for a shaded plank family and a
`Tube.ShadedUniformTubeSet`, i.e. exactly the shapes that
`Kakeya.factoringAndMultPropCombined` produces and `Kakeya.FrostmanEstimate.plankEstimate`
consumes.  The concentration parameter that comes out is

`M = (Cgeom * Cu * Csplit) * (b / a)`,

not the printed `Csplit * (b / a)`.

**The covering datum is stated at an arbitrary radius `ρ`**, subject only to
`ρ ≤ gridScale δ N kLev`.  This is the hierarchy/external-parent bridge: Proposition 5.1 builds its
covering family out of the *external* coarse tubes, at the external scale `ρ`, where the derived
relation `b ≤ ρ` makes a bounded family possible; `boundedOverlap` then consumes it at the grid
radius, because a `ρ`-tube is contained in the tube with the same axis and the larger grid radius
(`Tube.le_rescale`).  Nothing here identifies `ρ` with a grid radius and nothing here
requires the external parent labels to be hierarchy nodes. -/
theorem shadedPlankConcentration_of_parentwise
    {ι : Type*} {κ' : Type*} {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {q : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {N : ℕ} {Cu : ℝ≥0}
    (𝒱 : ShadedTube.ShadedUniformTubeSet q T N Cu) {kLev : ℕ} (hk : kLev ≤ N)
    {ts : Finset κ'} {W : κ' → ShadedPlank a b hab hb1} {par : κ' → ι}
    {Cgeom Csplit : ℝ≥0}
    {ρ : ℝ≥0} (hρ : ρ ≤ gridScale δ N kLev)
    (hpar_mem : ∀ x ∈ ts, par x ∈ 𝒱.tubeUniform.cover.indexSet kLev)
    (hocc : ∀ x ∈ ts, ∀ (j : κ') (θ : ℝ≥0) (hθ1 : θ ≤ 1),
      (W x).carrier ⊆ (Plank.thickened (W j).toPrism3D θ hθ1).carrier →
      ∃ i ∈ q, ((T i).toTube).toConvexSpaceBody ≤
          (𝒱.tubeUniform.cover.tube kLev (par x)).toConvexSpaceBody ∧
        (T i).carrier ⊆ (W x).carrier)
    (hcov : ∀ j ∈ ts, ∀ (θ : ℝ≥0), a / b ≤ θ → ∀ (hθ1 : θ ≤ 1),
      ∃ F : Finset (Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (F.card : ℝ≥0) ≤ Cgeom ∧
        ∀ i ∈ q, (T i).carrier ⊆ (Plank.thickened (W j).toPrism3D θ hθ1).carrier →
          ∃ V ∈ F, ((T i).toTube).toConvexSpaceBody ≤ V.toConvexSpaceBody)
    (hloc : ∀ j ∈ ts, ∀ (θ : ℝ≥0), a / b ≤ θ → ∀ (hθ1 : θ ≤ 1),
      ∀ jn ∈ 𝒱.tubeUniform.cover.indexSet kLev,
        (({k ∈ ts | (W k).carrier ⊆ (Plank.thickened (W j).toPrism3D θ hθ1).carrier ∧
            par k = jn}.card : ℝ≥0)) ≤ (Csplit * (b / a)) * θ) :
    ∀ j ∈ ts, ∀ (θ : ℝ≥0), a / b ≤ θ → ∀ (hθ1 : θ ≤ 1),
      (({k ∈ ts | (W k).carrier ⊆
          (Plank.thickened (W j).toPrism3D θ hθ1).carrier}.card : ℝ≥0))
        ≤ ((Cgeom * Cu * Csplit) * (b / a)) * θ := by
  intro j hj θ hθab hθ1
  obtain ⟨F, hFcard, hF⟩ := hcov j hj θ hθab hθ1
  set F' : Finset (Tube (gridScale δ N kLev) (EuclideanSpace ℝ (Fin 3))) :=
    F.image (fun V => V.rescale (gridScale δ N kLev))
  have hF'card : (F'.card : ℝ≥0) ≤ Cgeom := by
    exact le_trans (Nat.cast_le.mpr Finset.card_image_le) hFcard
  have hF' : ∀ i ∈ q, (T i).carrier ⊆
        (Plank.thickened (W j).toPrism3D θ hθ1).carrier →
      ∃ V' ∈ F', ((T i).toTube).toConvexSpaceBody ≤ V'.toConvexSpaceBody := by
    intro i hi hisub
    obtain ⟨V, hV, hTiV⟩ := hF i hi hisub
    exact ⟨V.rescale (gridScale δ N kLev), Finset.mem_image_of_mem _ hV,
      hTiV.trans (V.le_rescale hρ)⟩
  exact plankConcentration_of_parentwise (𝒰 := 𝒱.tubeUniform) hk
    (W := fun x => (W x).toPrism3D) (par := par) (j := j) hθ1
    (Cgeom := Cgeom) (Clocal := Csplit) hpar_mem
    (fun x hx hxsub => hocc x hx j θ hθ1 hxsub) F' hF'card hF'
    (hloc j hj θ hθab hθ1)

/-- **Absorbing the cross-parent loss into `δ ^ (-ε)`.**

The repair multiplies the concentration parameter by `Cgeom * Cu`, where `Cgeom` is a dimensional
covering constant but `Cu` is only bounded by `δ ^ (-η)`.  GWZ Lemma 6.4 pays `M ^ (β/2)` and the
`μ`-split pays another factor of the same constant, so the consumer needs
`(Cgeom * Cu * Csplit) ^ (1 + β/2) ≤ δ ^ (-ε/4)`.

This holds below a threshold depending only on `ε`, `Cgeom` and `Csplit`, provided the fine
exponent satisfies `η ≤ ε/12`: since `β ≤ 1` we have `1 + β/2 ≤ 3/2`, so the `Cu` part costs
`δ ^ (-η(1+β/2)) ≤ δ ^ (-ε/8)`, and the constant part is absorbed by
`Kakeya.rpowConstAbsorb`.  Shrinking `η` is free for the consumer: every `η`-hypothesis of
Proposition 6.6(A) only gets stronger. -/
theorem crossParentThreshold {β : ℝ} (hβpos : 0 < β) (hβle : β ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (Cgeom Csplit : ℝ≥0) (hCg : 1 ≤ Cgeom) (hCs : 1 ≤ Csplit) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧
      ∀ {η : ℝ}, 0 < η → η ≤ ε / 12 →
      ∀ (δ Cu : ℝ≥0), 0 < δ → δ ≤ δ₀ → δ ≤ 1 → Cu ≤ δ ^ (-η) →
        ((Cgeom * Cu * Csplit : ℝ≥0) : ENNReal) ^ ((1 : ℝ) + β / 2)
          ≤ (δ : ENNReal) ^ (-(ε / 4)) := by
  let Cc : ℝ≥0 := Cgeom * Csplit
  let p : ℝ := 1 + β / 2
  have hCc : 1 ≤ Cc := by
    dsimp [Cc]
    exact one_le_mul hCg hCs
  have hCpos : 0 < Cc := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hCc
  have hCne0 : Cc ≠ 0 := ne_of_gt hCpos
  have hp_nonneg : 0 ≤ p := by dsimp [p]; nlinarith [hβpos]
  have hp_le32 : p ≤ 3 / 2 := by dsimp [p]; nlinarith [hβle]
  have hε8 : 0 < ε / 8 := div_pos hε (by norm_num)
  have hε8_ne : ε / 8 ≠ 0 := ne_of_gt hε8
  set δ₀ : ℝ≥0 := Cc ^ (-p / (ε / 8)) with hδ₀_def
  have hδ₀_pos : 0 < δ₀ := by
    rw [hδ₀_def]
    exact NNReal.rpow_pos hCpos
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro η hηpos hηle δ Cu hδpos hδle hδ1 hCu
  have hC_enn : (Cc : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hCne0
  have hδ_enn0 : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδpos.ne'
  have hδ_top : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hbase_le1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  -- Absorb the constant part: (Cc : ENNReal) ^ p ≤ δ ^ (-(ε / 8)), via δ ≤ δ₀.
  have hδle₀ : (δ : ENNReal) ≤ (δ₀ : ENNReal) := by exact_mod_cast hδle
  have h_eq : (δ₀ : ENNReal) ^ (-(ε / 8)) = (Cc : ENNReal) ^ p := by
    rw [hδ₀_def]
    calc
      ((Cc ^ (-p / (ε / 8)) : ℝ≥0) : ENNReal) ^ (-(ε / 8))
          = ((Cc : ENNReal) ^ (-p / (ε / 8))) ^ (-(ε / 8)) := by
            rw [ENNReal.coe_rpow_of_ne_zero hCne0]
      _ = (Cc : ENNReal) ^ ((-p / (ε / 8)) * (-(ε / 8))) := by
            rw [ENNReal.rpow_mul]
      _ = (Cc : ENNReal) ^ p := by
            congr 1
            field_simp [hε8_ne]
  have h_e_nonneg : 0 ≤ ε / 8 := le_of_lt hε8
  have h_pow_e : (δ : ENNReal) ^ (ε / 8) ≤ (δ₀ : ENNReal) ^ (ε / 8) :=
    ENNReal.rpow_le_rpow hδle₀ h_e_nonneg
  have h_inv : ((δ₀ : ENNReal) ^ (ε / 8))⁻¹ ≤ ((δ : ENNReal) ^ (ε / 8))⁻¹ :=
    (ENNReal.inv_le_inv.mpr h_pow_e)
  have hconst : (Cc : ENNReal) ^ p ≤ (δ : ENNReal) ^ (-(ε / 8)) := by
    calc
      (Cc : ENNReal) ^ p = (δ₀ : ENNReal) ^ (-(ε / 8)) := by rw [h_eq]
      _ = ((δ₀ : ENNReal) ^ (ε / 8))⁻¹ := by rw [ENNReal.rpow_neg]
      _ ≤ ((δ : ENNReal) ^ (ε / 8))⁻¹ := h_inv
      _ = (δ : ENNReal) ^ (-(ε / 8)) := by rw [ENNReal.rpow_neg]
  -- The `Cu` factor: `Cgeom * Cu * Csplit ≤ Cc * δ ^ (-η)` in ℝ≥0.
  have hle_nn : Cgeom * Cu * Csplit ≤ Cc * δ ^ (-η) := by
    calc
      Cgeom * Cu * Csplit = Cc * Cu := by
        dsimp [Cc]
        ac_rfl
      _ ≤ Cc * δ ^ (-η) := by
        gcongr
  have hle_enn : ((Cgeom * Cu * Csplit : ℝ≥0) : ENNReal) ≤
      ((Cc * δ ^ (-η) : ℝ≥0) : ENNReal) := by
    exact_mod_cast hle_nn
  have hpow0 : ((Cgeom * Cu * Csplit : ℝ≥0) : ENNReal) ^ p ≤
      ((Cc * δ ^ (-η) : ℝ≥0) : ENNReal) ^ p := by
    exact ENNReal.rpow_le_rpow hle_enn hp_nonneg
  have hsplit : ((Cc * δ ^ (-η) : ℝ≥0) : ENNReal) ^ p
      = (Cc : ENNReal) ^ p * (δ : ENNReal) ^ ((-η) * p) := by
    calc
      ((Cc * δ ^ (-η) : ℝ≥0) : ENNReal) ^ p
          = ((Cc : ENNReal) * ((δ ^ (-η) : ℝ≥0) : ENNReal)) ^ p := by
            rw [ENNReal.coe_mul]
      _ = (Cc : ENNReal) ^ p * ((δ ^ (-η) : ℝ≥0) : ENNReal) ^ p := by
            exact ENNReal.mul_rpow_of_nonneg _ _ hp_nonneg
      _ = (Cc : ENNReal) ^ p * ((δ : ENNReal) ^ (-η)) ^ p := by
            rw [ENNReal.coe_rpow_of_ne_zero hδpos.ne']
      _ = (Cc : ENNReal) ^ p * (δ : ENNReal) ^ ((-η) * p) := by
            rw [ENNReal.rpow_mul]
  -- Exponent comparison: η * p ≤ ε / 8.
  have hηp : η * p ≤ ε / 8 := by
    have hstep : η * p ≤ (ε / 12) * (3 / 2 : ℝ) := by
      exact mul_le_mul hηle hp_le32 hp_nonneg (by positivity)
    nlinarith
  have hneg : -(ε / 8) ≤ -(η * p) := by linarith
  have hdelta : (δ : ENNReal) ^ ((-η) * p) ≤ (δ : ENNReal) ^ (-(ε / 8)) := by
    have hneg' : -(ε / 8) ≤ (-η) * p := by simpa [neg_mul] using hneg
    exact ENNReal.rpow_le_rpow_of_exponent_ge hbase_le1 hneg'
  -- Assemble.
  calc
    ((Cgeom * Cu * Csplit : ℝ≥0) : ENNReal) ^ p
        ≤ ((Cc * δ ^ (-η) : ℝ≥0) : ENNReal) ^ p := hpow0
    _ = (Cc : ENNReal) ^ p * (δ : ENNReal) ^ ((-η) * p) := hsplit
    _ ≤ (δ : ENNReal) ^ (-(ε / 8)) * (δ : ENNReal) ^ ((-η) * p) := by
        exact mul_le_mul' hconst le_rfl
    _ ≤ (δ : ENNReal) ^ (-(ε / 8)) * (δ : ENNReal) ^ (-(ε / 8)) := by
        exact mul_le_mul' le_rfl hdelta
    _ = (δ : ENNReal) ^ (-(ε / 8) + -(ε / 8)) := by
        rw [← ENNReal.rpow_add (-(ε / 8)) (-(ε / 8)) hδ_enn0 hδ_top]
    _ = (δ : ENNReal) ^ (-(ε / 4)) := by
        congr 1
        ring

/-! ### The local leafwise cover, valid at arbitrarily small `ρ`

`Kakeya.exists_leafwise_tube_cover` above covers *every* leaf of `B₁` and therefore needs
`1/2 ≤ ρ`.  The local statement needed by Proposition 6.6(A) is different: the leaves to be covered
are only those inside a container `K`, and the covering radius may be arbitrarily small.

The honest criterion is remarkably simple, and it is not a net: **a container that is itself
tube-shaped needs exactly one covering tube.**  If `K ≤ V₀` for some `V₀ : Tube r E`, then every
leaf inside `K` lies in `V₀.rescale ρ` as soon as `δ + r ≤ ρ`.  Convexity does all the work: the
leaf's core segment lies in the convex set `V₀.carrier`, so the leaf, being the `δ`-thickening of
its core, lies in the `(δ + r)`-thickening of `V₀`'s core.

No position net and no direction net appear, the constant is `1`, and there is no constraint on `ρ`
beyond `δ + r ≤ ρ` — in particular the statement is available for arbitrarily small `ρ`.  What it
*needs* is the tube-shaped container, i.e. the datum `K ≤ V₀` with `r` comparable to `b`.  This is
precisely the paper's "the `θb × b × 1` plank sits inside a `b`-tube", and it is exactly what the
current `Plank` normalisation fails to provide: a `Plank a b` has longitudinal extent `2` while a
`Tube r` has diameter at most `1 + 2r`, so `K ≤ V₀` forces `1/2 ≤ r`
(`Kakeya.Plank.half_le_of_le_tube`).  A *fixed dilation* of the covering radius does not repair
this, because the deficiency is longitudinal and the core length of a `Tube` is pinned to `1` by its
definition. -/

/-- Rescaling is idempotent in its radius argument: only the endpoints of the tube are retained. -/
theorem Tube.rescale_rescale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ : NNReal} (T : Tube δ E) (r ρ : NNReal) : (T.rescale r).rescale ρ = T.rescale ρ := rfl

/-- **Whole-leaf containment from a tube-shaped container.**

A `δ`-tube contained in an `r`-tube `V` lies in the `ρ`-rescale of `V` whenever `δ + r ≤ ρ`.  The
leaf's core segment lies in the convex set `V.carrier`, and the leaf is the `δ`-thickening of its
core, hence lies in the `δ`-thickening of `V.carrier`, which is the `(r + δ)`-rescale of `V`. -/
theorem Tube.carrier_subset_rescale_of_subset_tube
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ r ρ : NNReal} (T : Tube δ E) (V : Tube r E)
    (h : (T.carrier : Set E) ⊆ (V.carrier : Set E)) (hδr : δ + r ≤ ρ) :
    (T.carrier : Set E) ⊆ ((V.rescale ρ).carrier : Set E) := by
  -- `T.x` and `T.y` lie in `T.carrier`, hence in the convex set `V.carrier`.
  have hxV : T.x ∈ (V.carrier : Set E) := by
    apply h
    rw [T.carrier_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨T.x, left_mem_segment ℝ T.x T.y, Metric.mem_closedBall_self δ.coe_nonneg⟩
  have hyV : T.y ∈ (V.carrier : Set E) := by
    apply h
    rw [T.carrier_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨T.y, right_mem_segment ℝ T.x T.y, Metric.mem_closedBall_self δ.coe_nonneg⟩
  -- The core segment of `T` lies in the convex set `V.carrier`, so the `δ`-thickening of `T`'s
  -- core lies in `(V.rescale (r+δ))`.
  have hTc : (T.carrier : Set E) ⊆ ((V.rescale (r + δ)).carrier : Set E) := by
    calc
      (T.carrier : Set E) = Metric.cthickening (δ : ℝ) (segment ℝ T.x T.y) :=
        T.carrier_eq_cthickening
      _ ⊆ Metric.cthickening (δ : ℝ) (V.carrier : Set E) := by
        exact Metric.cthickening_subset_of_subset (δ : ℝ)
          (Convex.segment_subset V.convex hxV hyV)
      _ = (V.rescale (r + δ)).carrier := V.cthickening_carrier δ
  -- `V.rescale (r+δ) ⊆ V.rescale ρ` since `r+δ ≤ ρ`, and `(r+δ)`-rescale composed with `ρ`
  -- equals the `ρ`-rescale.
  have hrd : r + δ ≤ ρ := by simpa [add_comm] using hδr
  have hle : ((V.rescale (r + δ)).carrier : Set E) ⊆ ((V.rescale ρ).carrier : Set E) := by
    have hle0 : (V.rescale (r + δ)).toConvexSpaceBody ≤ (V.rescale ρ).toConvexSpaceBody := by
      rw [← Tube.rescale_rescale V (r + δ) ρ]
      exact (V.rescale (r + δ)).le_rescale hrd
    exact (SetLike.coe_subset_coe
      (S := (V.rescale (r + δ)).toConvexSpaceBody) (T := (V.rescale ρ).toConvexSpaceBody)).mp hle0
  exact hTc.trans hle

/-- **The local leafwise cover: one tube suffices for a tube-shaped container.**

Exactly the covering datum consumed by `Kakeya.card_extParents_le_of_cover` (and by
`Tube.UniformTubeSet.card_contributingNodes_le_of_cover`), with covering constant `1`,
covering radius exactly `ρ`, and no lower bound on `ρ` beyond `δ + r ≤ ρ`. -/
theorem exists_leafwise_cover_of_tube_container
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {ι : Type*} {δ r ρ : NNReal} (hδr : δ + r ≤ ρ)
    (q : Finset ι) (T : ι → Tube δ E) (K : ConvexSpaceBody E)
    (V₀ : Tube r E) (hK : K ≤ V₀.toConvexSpaceBody) :
    ∃ F : Finset (Tube ρ E), (F.card : ℝ≥0) ≤ 1 ∧
      ∀ i ∈ q, (T i).toConvexSpaceBody ≤ K →
        ∃ V ∈ F, (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody := by
  refine ⟨{V₀.rescale ρ}, ?_, ?_⟩
  · simp
  · intro i hi hiK
    refine ⟨V₀.rescale ρ, Finset.mem_singleton_self (V₀.rescale ρ), ?_⟩
    have hT : (T i).toConvexSpaceBody ≤ V₀.toConvexSpaceBody := le_trans hiK hK
    have hsub : (T i).carrier ⊆ (V₀.rescale ρ).carrier :=
      Tube.carrier_subset_rescale_of_subset_tube (T i) V₀
        ((SetLike.coe_subset_coe (S := (T i).toConvexSpaceBody)
          (T := V₀.toConvexSpaceBody)).mp hT) hδr
    exact (SetLike.coe_subset_coe (S := (T i).toConvexSpaceBody)
      (T := (V₀.rescale ρ).toConvexSpaceBody)).mpr hsub

/-! ### Cross-parent counting, entirely external-parentwise

The counting below never mentions the coarse hierarchy.  The reason is a structural mismatch that
the hierarchy route cannot repair: the Katz--Tao property lives on each *external* factorization
class `Fz k` separately (`ConvexSpaceBody.Factorization.isKatzTao`), many external `ρ`-parents can
share one hierarchy node (whose radius `gridScale δ N kLev` may be far larger than `ρ`), and
Katz--Tao is inherited by subsets but not by unions.  So the within-class estimate must be used on
the class where it holds, and the *external* parents must be counted directly.

The input that does the counting is leaf-mediated bounded overlap of the external system itself:
for every `ρ`-tube `V`, at most `Cu` external parents own a leaf lying inside `V`.  This is the
external analogue of `Tube.UniformTubeSet.boundedOverlap` and the honest replacement for
the sorried `Kakeya.Tube.IsUniform.spread`; it is *not* pairwise essential distinctness of the
coarse family, and it is not automatic for an arbitrary external family. -/

/-- **The number of contributing external parents, from a leafwise cover.**

`hover` is leaf-mediated bounded overlap of the external parent system at radius `ρ`.  If the leaves
inside the container `K` are caught leafwise by the family `F` of `ρ`-tubes, then every external
parent contributing a leaf inside `K` contributes a leaf inside some member of `F`, so the parents
are covered by `F.card` many applications of `hover`. -/
theorem card_extParents_le_of_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {ι κ : Type*} {ρ : NNReal} {q : Finset ι} {Tb : ι → ConvexSpaceBody E}
    {r : Finset κ} {assign : ι → κ} {Cu : ℝ≥0}
    (hover : ∀ V : Tube ρ E,
      ((({k ∈ r | ∃ i ∈ q, assign i = k ∧ Tb i ≤ V.toConvexSpaceBody}).card : ℝ≥0)) ≤ Cu)
    {K : ConvexSpaceBody E} (F : Finset (Tube ρ E))
    (hF : ∀ i ∈ q, Tb i ≤ K → ∃ V ∈ F, Tb i ≤ V.toConvexSpaceBody) :
    ((({k ∈ r | ∃ i ∈ q, assign i = k ∧ Tb i ≤ K}).card : ℝ≥0)) ≤ (F.card : ℝ≥0) * Cu := by
  classical
  let g : Tube ρ E → Finset κ := fun V =>
    {k ∈ r | ∃ i ∈ q, assign i = k ∧ Tb i ≤ V.toConvexSpaceBody}
  have hsub : ({k ∈ r | ∃ i ∈ q, assign i = k ∧ Tb i ≤ K} : Finset κ) ⊆ F.biUnion g := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkr, ⟨i, hiq, hassign, hTbK⟩⟩
    rcases hF i hiq hTbK with ⟨V, hV, hTbV⟩
    exact Finset.mem_biUnion.mpr ⟨V, hV, by
      simp only [g, Finset.mem_filter]
      exact ⟨hkr, i, hiq, hassign, hTbV⟩⟩
  have hcard : ({k ∈ r | ∃ i ∈ q, assign i = k ∧ Tb i ≤ K}).card ≤
      ∑ V ∈ F, (g V).card := by
    exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hg : ∀ V ∈ F, ((g V).card : ℝ≥0) ≤ Cu := by
    intro V hV
    simpa [g] using hover V
  calc
    (({k ∈ r | ∃ i ∈ q, assign i = k ∧ Tb i ≤ K}).card : ℝ≥0)
        ≤ ((∑ j ∈ F, (g j).card : ℕ) : ℝ≥0) := by
      exact Nat.cast_le.mpr hcard
    _ = ∑ j ∈ F, ((g j).card : ℝ≥0) := by
      exact Nat.cast_sum (s := F) (f := fun j => (g j).card)
    _ ≤ ∑ j ∈ F, Cu := by
      exact Finset.sum_le_sum hg
    _ = (F.card : ℝ≥0) * Cu := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- **The definitive corrected cross-parent count.**

`#{outer bodies inside K} ≤ (#F · Cu) · m`, where

* `#F · Cu` bounds the number of contributing *external* parents
  (`Kakeya.card_extParents_le_of_cover`), and
* `m` is the within-*external*-class bound, i.e. the local Katz--Tao estimate on a single `Fz k`.

There is no same-parent equality, no regrouping of external classes by hierarchy node, and no
Katz--Tao estimate on a union of classes.  `hocc` is the occupancy certificate: an outer body inside
`K` is witnessed by a genuine leaf of its own external class lying inside it. -/
theorem card_le_of_externalParentwise
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {ι κ κ' : Type*} {ρ : NNReal} {q : Finset ι} {Tb : ι → ConvexSpaceBody E}
    {r : Finset κ} {assign : ι → κ} {Cu : ℝ≥0}
    (hover : ∀ V : Tube ρ E,
      ((({k ∈ r | ∃ i ∈ q, assign i = k ∧ Tb i ≤ V.toConvexSpaceBody}).card : ℝ≥0)) ≤ Cu)
    {ts : Finset κ'} {Wc : κ' → ConvexSpaceBody E} {par : κ' → κ} {K : ConvexSpaceBody E}
    (hpar_mem : ∀ x ∈ ts, par x ∈ r)
    (hocc : ∀ x ∈ ts, Wc x ≤ K → ∃ i ∈ q, assign i = par x ∧ Tb i ≤ Wc x)
    (F : Finset (Tube ρ E))
    (hF : ∀ i ∈ q, Tb i ≤ K → ∃ V ∈ F, Tb i ≤ V.toConvexSpaceBody)
    {m : ℝ≥0}
    (hlocal : ∀ k ∈ r, (({x ∈ ts | Wc x ≤ K ∧ par x = k}).card : ℝ≥0) ≤ m) :
    (({x ∈ ts | Wc x ≤ K}).card : ℝ≥0) ≤ ((F.card : ℝ≥0) * Cu) * m := by
  classical
  let P : Finset κ := {k ∈ r | ∃ i ∈ q, assign i = k ∧ Tb i ≤ K}
  have hpar' : ∀ x ∈ ts, Wc x ≤ K → par x ∈ P := by
    intro x hx hKx
    refine Finset.mem_filter.mpr ⟨hpar_mem x hx, ?_⟩
    rcases hocc x hx hKx with ⟨i, hi, hassign, hTiWc⟩
    exact ⟨i, hi, hassign, le_trans hTiWc hKx⟩
  have hlocal' : ∀ j ∈ P, (({x ∈ ts | Wc x ≤ K ∧ par x = j}).card : ℝ≥0) ≤ m := by
    intro j hj
    exact hlocal j ((Finset.mem_filter.mp hj).1)
  have hPA : (({x ∈ ts | Wc x ≤ K}).card : ℝ≥0) ≤ (P.card : ℝ≥0) * m := by
    exact card_filter_le_of_parentwise (p := fun x : κ' => Wc x ≤ K) (par := par) (P := P)
      hpar' hlocal'
  have hPC : (P.card : ℝ≥0) ≤ (F.card : ℝ≥0) * Cu := by
    unfold P
    exact card_extParents_le_of_cover hover F hF
  have hstep : (P.card : ℝ≥0) * m ≤ ((F.card : ℝ≥0) * Cu) * m := by
    exact mul_le_mul_of_nonneg_right hPC (by positivity)
  exact le_trans hPA hstep

/-- **The thick-plank concentration hypothesis of GWZ Lemma 6.4, proved external-parentwise.**

The shaded-family adapter: exactly the shapes that `Kakeya.factoringAndMultPropCombined` produces
and `Kakeya.FrostmanEstimate.plankEstimate` consumes, with concentration parameter

`M = (Cgeom * Cu * Csplit) * (b / a)`.

Compared with `Kakeya.shadedPlankConcentration_of_parentwise` this version is hierarchy-free: the
parent labels are the external factorization labels `κ`, so the within-parent bound `hloc` is
indexed by `k ∈ r` and is the Katz--Tao estimate on the single class `Fz k`, where it actually
holds.  There is consequently no grid level, and no side condition relating `ρ` to a grid radius. -/
theorem shadedPlankConcentration_of_externalParentwise
    {ι κ κ' : Type*} {δ ρ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {q : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {r : Finset κ} {assign : ι → κ} {Cu Cgeom Csplit : ℝ≥0}
    {ts : Finset κ'} {W : κ' → ShadedPlank a b hab hb1} {par : κ' → κ}
    (hover : ∀ V : Tube ρ (EuclideanSpace ℝ (Fin 3)),
      ((({k ∈ r | ∃ i ∈ q, assign i = k ∧
        ((T i).toTube).toConvexSpaceBody ≤ V.toConvexSpaceBody}).card : ℝ≥0)) ≤ Cu)
    (hpar_mem : ∀ x ∈ ts, par x ∈ r)
    (hocc : ∀ x ∈ ts, ∀ (j : κ') (θ : ℝ≥0) (hθ1 : θ ≤ 1),
      (W x).carrier ⊆ (Plank.thickened (W j).toPrism3D θ hθ1).carrier →
      ∃ i ∈ q, assign i = par x ∧ (T i).carrier ⊆ (W x).carrier)
    (hcov : ∀ j ∈ ts, ∀ (θ : ℝ≥0), a / b ≤ θ → ∀ (hθ1 : θ ≤ 1),
      ∃ F : Finset (Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (F.card : ℝ≥0) ≤ Cgeom ∧
        ∀ i ∈ q, (T i).carrier ⊆ (Plank.thickened (W j).toPrism3D θ hθ1).carrier →
          ∃ V ∈ F, ((T i).toTube).toConvexSpaceBody ≤ V.toConvexSpaceBody)
    (hloc : ∀ j ∈ ts, ∀ (θ : ℝ≥0), a / b ≤ θ → ∀ (hθ1 : θ ≤ 1),
      ∀ k ∈ r,
        (({x ∈ ts | (W x).carrier ⊆ (Plank.thickened (W j).toPrism3D θ hθ1).carrier ∧
            par x = k}.card : ℝ≥0)) ≤ (Csplit * (b / a)) * θ) :
    ∀ j ∈ ts, ∀ (θ : ℝ≥0), a / b ≤ θ → ∀ (hθ1 : θ ≤ 1),
      (({x ∈ ts | (W x).carrier ⊆
          (Plank.thickened (W j).toPrism3D θ hθ1).carrier}.card : ℝ≥0))
        ≤ ((Cgeom * Cu * Csplit) * (b / a)) * θ := by
  intro j hj θ hθab hθ1
  obtain ⟨F, hFcard, hF⟩ := hcov j hj θ hθab hθ1
  -- Bridge between the `ConvexSpaceBody` order and carrier inclusion.
  have hbridge : ∀ (X Y : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))),
      X ≤ Y ↔ (X.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Y.carrier := by
    intro X Y
    rfl
  let Tb : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun i => ((T i).toTube).toConvexSpaceBody
  let Kthick : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    (Plank.thickened (W j).toPrism3D θ hθ1).toConvexSpaceBody
  let Wc : κ' → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun x => (W x).toConvexSpaceBody
  have hcar : ∀ x : κ', (W x).carrier ⊆ (Plank.thickened (W j).toPrism3D θ hθ1).carrier ↔
      Wc x ≤ Kthick := by
    intro x
    change (Wc x).carrier ⊆ Kthick.carrier ↔ Wc x ≤ Kthick
    exact (hbridge (Wc x) Kthick).symm
  have hfilter_top : ts.filter (fun x : κ' => (W x).carrier ⊆
        (Plank.thickened (W j).toPrism3D θ hθ1).carrier) =
      ts.filter (fun x : κ' => Wc x ≤ Kthick) := by
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, hcar x]
  have hfilter_j : ∀ k : κ, ts.filter (fun x : κ' => (W x).carrier ⊆
      (Plank.thickened (W j).toPrism3D θ hθ1).carrier ∧ par x = k) =
      ts.filter (fun x : κ' => Wc x ≤ Kthick ∧ par x = k) := by
    intro k
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, hcar x]
  have hocc' : ∀ x ∈ ts, Wc x ≤ Kthick → ∃ i ∈ q, assign i = par x ∧ Tb i ≤ Wc x := by
    intro x hx hxK
    rcases hocc x hx j θ hθ1 ((hcar x).mpr hxK) with ⟨i, hiq, hassign, hTiWc⟩
    exact ⟨i, hiq, hassign, (hbridge (Tb i) (Wc x)).mpr (by simpa [Tb] using hTiWc)⟩
  have hF' : ∀ i ∈ q, Tb i ≤ Kthick → ∃ V ∈ F, Tb i ≤ V.toConvexSpaceBody := by
    intro i hi hiK
    exact hF i hi ((hbridge (Tb i) Kthick).mp (by simpa [Tb] using hiK))
  have hlocal' : ∀ k ∈ r,
      (({x ∈ ts | Wc x ≤ Kthick ∧ par x = k}.card : ℝ≥0)) ≤ Csplit * (b / a) * θ := by
    intro k hk
    rw [← hfilter_j k]
    exact hloc j hj θ hθab hθ1 k hk
  have hmain : (({x ∈ ts | Wc x ≤ Kthick}.card : ℝ≥0)) ≤
      ((F.card : ℝ≥0) * Cu) * (Csplit * (b / a) * θ) := by
    rw [← hfilter_top]
    exact card_le_of_externalParentwise (E := EuclideanSpace ℝ (Fin 3))
      (Tb := Tb) hover (Wc := Wc) (par := par) (K := Kthick)
      hpar_mem hocc' F hF' (m := Csplit * (b / a) * θ) hlocal'
  rw [hfilter_top]
  have hstep0 : ((F.card : ℝ≥0) * Cu) * (Csplit * (b / a) * θ) ≤
      (Cgeom * Cu) * (Csplit * (b / a) * θ) := by
    gcongr
  have hstep1 : (Cgeom * Cu) * (Csplit * (b / a) * θ) =
      ((Cgeom * Cu * Csplit) * (b / a)) * θ := by
    ring
  exact le_trans hmain (le_trans hstep0 (le_of_eq hstep1))

/-! ### The comparable-plank normalisation, and the local cover it unlocks

The covering datum above is still an *assumed* counting statement.  This section reduces it to a
single *containment*, which is both weaker and manifestly true in the paper's normalisation, and
proves the counting.

**The normalisation defect.**  `Plank a b` is `Prism3D a b 1`, and `Prism3D` records half-widths, so
a Lean plank has longitudinal *extent* `2`.  A `Tube r` is the `r`-neighbourhood of a segment of
length exactly `1` (`Tube.dist_eq_one`), hence has diameter at most `1 + 2r`.  A plank inside
a tube therefore forces `2 ≤ 1 + 2r`, i.e. `1/2 ≤ r` (`Kakeya.Plank.half_le_of_le_tube`).  This is a
fixed-constant mismatch between two normalisations, not a statement about the mathematics: the paper
asks only for dimensions *comparable* to `a × b × 1`, and its `θb × b × 1` plank does sit inside a
tube of radius comparable to `b`.  Because the deficiency is longitudinal and `Tube`'s core length
is pinned to `1`, no dilation of the covering radius repairs it, and neither does a position or a
direction net: a leaf has core length `1` and so does a covering tube, so covering a container of
extent `2` leafwise needs `⌈1/ρ⌉` tubes, not `O(1)`.

**The minimal comparable-plank interface.**  What the argument consumes is exactly
`IsTubeShaped r K` — the container lies in *some* tube of radius `r` — with `r` comparable to `b`.
`Kakeya.Prism3D.isTubeShaped` proves that this holds, with `r = a + b ≤ 2 * b`, for any prism whose
long half-width is at most `1/2`, i.e. for the paper's normalisation.  Nothing about
`PlankFactorization`, `Prism3D` or `Tube` is changed; the datum is simply requested where the paper
supplies it.

**What it buys.**  With a tube-shaped container the cover is a *singleton* and no `δ` enters at all:
a body inside `K` is inside `V₀`, hence inside `V₀.rescale ρ` as soon as `r ≤ ρ`.  So
`Ccover = 1`, the covering radius is exactly `ρ`, and the statement is available for arbitrarily
small `ρ` — the local theorem that `Kakeya.exists_leafwise_tube_cover` (which discretises all of
`B₁` and therefore needs `1/2 ≤ ρ`) is not. -/

/-- **Superseded — do not use in new code.**  Its hypothesis `hshape` demands that the *exact* Lean
thickened plank be contained in a tube of radius `2 * b`, and that is **false** for `b < 1/2`: a
`Plank a b = Prism3D a b 1` has longitudinal extent `2` while a `Tube r` has diameter at most
`1 + 2r` (`Kakeya.Plank.half_le_of_le_tube`).  The lemma itself is true — it is simply
unusable at small scales, because its hypothesis cannot be met.  The live replacement is
`Kakeya.shadedPlankConcentration_of_confinedWitness`, whose geometric input is about the *actual*
factor bodies rather than the representative planks.

**The corrected cross-parent concentration, from the comparable-plank datum.**

The covering family has disappeared from the hypotheses: `hshape` is the single containment of
`W_θ` in a `2b`-tube, and `h2b : 2 * b ≤ ρ'` is the fixed-dilation scale relation, available from
the derived `b ≤ ρ` by taking the test radius `ρ' = 2 * ρ`.  The conclusion is the concentration
hypothesis of GWZ Lemma 6.4 with

`M = (Cu * Csplit) * (b / a)`,

so the only cross-parent loss is the external overlap constant `Cu`. -/
theorem shadedPlankConcentration_of_tubeShaped
    {ι κ κ' : Type*} {δ ρ' a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {q : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {r : Finset κ} {assign : ι → κ} {Cu Csplit : ℝ≥0}
    {ts : Finset κ'} {W : κ' → ShadedPlank a b hab hb1} {par : κ' → κ}
    (h2b : 2 * b ≤ ρ')
    (hover : ∀ V : Tube ρ' (EuclideanSpace ℝ (Fin 3)),
      ((({k ∈ r | ∃ i ∈ q, assign i = k ∧
        ((T i).toTube).toConvexSpaceBody ≤ V.toConvexSpaceBody}).card : ℝ≥0)) ≤ Cu)
    (hpar_mem : ∀ x ∈ ts, par x ∈ r)
    (hocc : ∀ x ∈ ts, ∀ (j : κ') (θ : ℝ≥0) (hθ1 : θ ≤ 1),
      (W x).carrier ⊆ (Plank.thickened (W j).toPrism3D θ hθ1).carrier →
      ∃ i ∈ q, assign i = par x ∧ (T i).carrier ⊆ (W x).carrier)
    (hshape : ∀ j ∈ ts, ∀ (θ : ℝ≥0), a / b ≤ θ → ∀ (hθ1 : θ ≤ 1),
      IsTubeShaped (2 * b) (Plank.thickened (W j).toPrism3D θ hθ1).toConvexSpaceBody)
    (hloc : ∀ j ∈ ts, ∀ (θ : ℝ≥0), a / b ≤ θ → ∀ (hθ1 : θ ≤ 1),
      ∀ k ∈ r,
        (({x ∈ ts | (W x).carrier ⊆ (Plank.thickened (W j).toPrism3D θ hθ1).carrier ∧
            par x = k}.card : ℝ≥0)) ≤ (Csplit * (b / a)) * θ) :
    ∀ j ∈ ts, ∀ (θ : ℝ≥0), a / b ≤ θ → ∀ (hθ1 : θ ≤ 1),
      (({x ∈ ts | (W x).carrier ⊆
          (Plank.thickened (W j).toPrism3D θ hθ1).carrier}.card : ℝ≥0))
        ≤ ((1 * Cu * Csplit) * (b / a)) * θ := by
  have hbridge : ∀ (X Y : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))),
      X ≤ Y ↔ (X.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Y.carrier := by
    intro X Y
    rfl
  have hcov :
      ∀ j ∈ ts, ∀ (θ : ℝ≥0), a / b ≤ θ → ∀ (hθ1 : θ ≤ 1),
      ∃ F : Finset (Tube ρ' (EuclideanSpace ℝ (Fin 3))),
        (F.card : ℝ≥0) ≤ 1 ∧
        ∀ i ∈ q, (T i).carrier ⊆ (Plank.thickened (W j).toPrism3D θ hθ1).carrier →
          ∃ V ∈ F, ((T i).toTube).toConvexSpaceBody ≤ V.toConvexSpaceBody := by
    intro j hj θ hθab hθ1
    obtain ⟨V, hV⟩ := hshape j hj θ hθab hθ1
    refine ⟨{V.rescale ρ'}, ?_, ?_⟩
    · simp
    · intro i hi hc
      have hTiK : ((T i).toTube).toConvexSpaceBody ≤
          (Plank.thickened (W j).toPrism3D θ hθ1).toConvexSpaceBody := by
        exact (hbridge ((T i).toTube).toConvexSpaceBody
          (Plank.thickened (W j).toPrism3D θ hθ1).toConvexSpaceBody).mpr (by simpa using hc)
      exact ⟨V.rescale ρ', Finset.mem_singleton_self (V.rescale ρ'),
        le_trans (le_trans hTiK hV) (V.le_rescale h2b)⟩
  exact shadedPlankConcentration_of_externalParentwise (Cgeom := 1) hover hpar_mem hocc hcov hloc

/-! ### The actual factor body, and the confinement datum that replaces the false shape output

The shape datum of the previous iteration,

`∃ V₀ : Tube (2 * b) E, (Plank.thickened (W j).toPrism3D θ hθ1).toConvexSpaceBody ≤ V₀`,

is **false** for small `b`, and this section removes it.  Two facts explain both the failure and the
repair.

*Why it is false.*  `Plank a b = Prism3D a b 1` and `Prism3D` records half-widths, so a thickened
plank has longitudinal extent `2`, while a `Tube r` has diameter at most `1 + 2r`; containment
forces `1/2 ≤ r` (`Kakeya.Plank.half_le_of_le_tube`).  Nothing can be attached to the *exact* Lean
thickened plank at radius comparable to `b`.

*Why the count is nevertheless available.*  What the parent count consumes is not a shape statement
about the container at all.  It needs only: **one** test tube of radius `Cparent * ρ` catching an
occupying leaf of every contributing outer body.  That is the datum `hconf` below, and it is
satisfiable for arbitrarily small `ρ`, because `W x ⊆ W_θ(j)` is longitudinally *rigid*: applying
transverse bounds of `W_θ(j)` to `centre x ± u x` gives `|⟪u x, e₁ʲ⟫| ≤ b` and
`|⟪u x, e₀ʲ⟫| ≤ θb`, hence `|⟪u x, e₂ʲ⟫| ≥ 1 - b²`, and then the longitudinal bound gives
`|⟪centre x - centre j, e₂ʲ⟫| ≤ b²`.  So all contributing bodies — and with them their occupying
leaves, which lie in the *actual* factor bodies of longitudinal extent `≈ 1` rather than in the
representative planks of extent `2` — are confined to a single tube of radius `O(b) ⊆ O(ρ)` on
`W_θ(j)`'s own long axis.

This is exactly the distinction steps 3 asks for: the body on which Proposition 5.1 factors the fine
tubes (`body`, longitudinal extent `≈ 1`, contained in its coarse parent) is **not** the exact Lean
plank handed to GWZ Lemma 6.4 (`W`, longitudinal extent `2`).  The old interface made them
definitionally equal; that identification is the normalisation bug.  Here they are separate, related
only by fixed-constant comparability, of which only the transverse half — `ContainsFlatDisc` — is
consumed by the proved layer. -/

/-- One outer body of a `Kakeya.ComparableBodyFactorization` of a nonempty fibre lies inside the coarse
tube containing that fibre.  This is the minimality field `body_le` applied to the coarse tube. -/
theorem ComparableBodyFactorization.exists_body_le {ι : Type*} {b ρ C₀ : ℝ≥0} {s : Finset ι}
    {Tb : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} (hs : s.Nonempty)
    (F : ComparableBodyFactorization b s Tb C₀) (R : Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (hTb : ∀ i ∈ s, Tb i ≤ R.toConvexSpaceBody) :
    ∃ x ∈ F.cells, F.body x ≤ R.toConvexSpaceBody := by
  obtain ⟨i₀, hi₀⟩ := hs
  refine ⟨F.cellOf i₀, F.cellOf_mem i₀ hi₀, ?_⟩
  exact F.body_le (F.cellOf i₀) (F.cellOf_mem i₀ hi₀) R.toConvexSpaceBody
    (fun i hi _ => hTb i hi)

/-- **The corrected scale relation.**

`b ≤ 2 * ρ`, derived from Proposition 6.6(A)'s own data through the comparable-body interface.  Take
any `i₀ ∈ q`, let `k := assign i₀` and `x := (Fz k).cellOf i₀`; minimality puts `body x` inside
`R k`, and `wide` then gives `min b (1/2) ≤ ρ`, whence `b ≤ 2 * ρ`: either `min b (1/2) = b` and
`b ≤ ρ ≤ 2ρ`, or `1/2 ≤ ρ` and `b ≤ 1 = 2 * (1/2) ≤ 2ρ`.  The hypothesis `b ≤ 1` is used only in the
second case, and Proposition 6.6(A) carries it already.

This replaces `Kakeya.b_le_of_localPlankFactorisation`, which obtained the sharper `b ≤ ρ` but only
from the exact normalisation that simultaneously forced `1/2 ≤ ρ`.  Per the Scale comparison the weaker
statement with an absolute constant is the correct one: chasing the constant `1` here relies on the
bad normalisation. -/
theorem b_le_two_mul_of_comparableBodyFactorization {ι κ : Type*}
    {δ ρ b : ℝ≥0} (hb1 : b ≤ 1)
    {q : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} (hq : q.Nonempty)
    {r : Finset κ} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))} {assign : ι → κ}
    (hassign : ∀ i ∈ q, assign i ∈ r ∧
      (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody)
    {C₀ : ℝ≥0}
    (Fz : ∀ k ∈ r, ComparableBodyFactorization b
      {i ∈ q | assign i = k} (fun i => (T i).toConvexSpaceBody) C₀) :
    b ≤ 2 * ρ := by
  classical
  obtain ⟨i₀, hi₀⟩ := hq
  set k := assign i₀ with hk_def
  have hk : k ∈ r := (hassign i₀ hi₀).1
  have hfib : ({i ∈ q | assign i = k} : Finset ι).Nonempty :=
    ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, rfl⟩⟩
  have hTb : ∀ i ∈ ({i ∈ q | assign i = k} : Finset ι),
      (T i).toConvexSpaceBody ≤ (R k).toConvexSpaceBody := by
    intro i hi
    obtain ⟨hiq, hik⟩ := Finset.mem_filter.mp hi
    exact hik ▸ (hassign i hiq).2
  obtain ⟨x, hx, hbodyle⟩ :=
    ComparableBodyFactorization.exists_body_le hfib (Fz k hk) (R k) hTb
  have hmin : min b (1 / 2 : ℝ≥0) ≤ ρ := by
    have hsub : ((Fz k hk).body x).carrier ⊆
        ((R k).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
      (SetLike.coe_subset_coe (S := (Fz k hk).body x)
        (T := (R k).toConvexSpaceBody)).mp hbodyle
    exact ContainsFlatDisc.le_of_subset_tube ((Fz k hk).wide x hx) (R k) hsub
  exact le_two_mul_of_min_le hb1 hmin

/-- **The cross-parent count from a single confining test tube.**

The definitive form of the corrected count.  `hconf` supplies *one* test tube `V` such that every
outer body inside the container `K` is witnessed by an occupied leaf of its own external parent
lying in `V`.  Then `hover V` bounds the contributing external parents by `Cu` outright — there
is no covering family and no covering constant — and the within-parent bound `hlocal`, indexed by
`k ∈ r` where the Katz--Tao property actually lives, finishes.

No same-parent equality, no hierarchy node, no Katz--Tao estimate on a union of classes, and no
essential distinctness of the external labels. -/
theorem card_le_of_confinedWitness
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {ι κ κ' : Type*} {ρ : NNReal} {q : Finset ι} {Tb : ι → ConvexSpaceBody E}
    {r : Finset κ} {assign : ι → κ} {Cu : ℝ≥0}
    (hover : ∀ V : Tube ρ E,
      ((({k ∈ r | ∃ i ∈ q, assign i = k ∧ Tb i ≤ V.toConvexSpaceBody}).card : ℝ≥0)) ≤ Cu)
    {ts : Finset κ'} {Wc : κ' → ConvexSpaceBody E} {par : κ' → κ} {K : ConvexSpaceBody E}
    (hpar_mem : ∀ x ∈ ts, par x ∈ r)
    (hconf : ∃ V : Tube ρ E, ∀ x ∈ ts, Wc x ≤ K →
      ∃ i ∈ q, assign i = par x ∧ Tb i ≤ V.toConvexSpaceBody)
    {m : ℝ≥0}
    (hlocal : ∀ k ∈ r, (({x ∈ ts | Wc x ≤ K ∧ par x = k}).card : ℝ≥0) ≤ m) :
    (({x ∈ ts | Wc x ≤ K}).card : ℝ≥0) ≤ Cu * m := by
  classical
  obtain ⟨V, hV⟩ := hconf
  let P : Finset κ := {k ∈ r | ∃ i ∈ q, assign i = k ∧ Tb i ≤ V.toConvexSpaceBody}
  have hpar' : ∀ x ∈ ts, Wc x ≤ K → par x ∈ P := by
    intro x hx hKx
    unfold P
    refine Finset.mem_filter.mpr ⟨hpar_mem x hx, ?_⟩
    rcases hV x hx hKx with ⟨i, hi, hassign, hTiV⟩
    exact ⟨i, hi, hassign, hTiV⟩
  have hlocal' : ∀ j ∈ P, (({x ∈ ts | Wc x ≤ K ∧ par x = j}).card : ℝ≥0) ≤ m := by
    intro j hj
    exact hlocal j ((Finset.mem_filter.mp hj).1)
  have hPA : (({x ∈ ts | Wc x ≤ K}).card : ℝ≥0) ≤ (P.card : ℝ≥0) * m := by
    exact card_filter_le_of_parentwise (p := fun x : κ' => Wc x ≤ K) (par := par) (P := P)
      hpar' hlocal'
  have hPC : (P.card : ℝ≥0) ≤ Cu := by
    unfold P
    exact hover V
  have hstep : (P.card : ℝ≥0) * m ≤ Cu * m := by
    exact mul_le_mul_of_nonneg_right hPC (by positivity)
  exact le_trans hPA hstep

/-- **The confinement datum, from occupancy into the actual bodies plus tube-shapedness.**

This is the decomposition that makes `hconf` of `Kakeya.card_le_of_confinedWitness` an honest
geometric statement rather than a black box, and it is where the actual body `Hb` and the
representative plank `Wc` are kept apart:

* `hocc` is occupancy *into the actual body* — the leaf lies in `Hb x`, of longitudinal extent
  `≈ 1`, not merely in the representative plank `Wc x` of extent `2`;
* `hbody` is the rigidity of `Wc x ≤ K`: the actual bodies of the contributing cells are confined to
  a single region `Kh`;
* `hshape` says `Kh` is tube-shaped at a radius comparable to `b`, hence to `ρ`.

No dilation of the leaf radius and no covering family appear. -/
theorem confinedWitness_of_isTubeShaped
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {ι κ κ' : Type*} {rad ρ : NNReal} {q : Finset ι} {Tb : ι → ConvexSpaceBody E}
    {assign : ι → κ} {ts : Finset κ'} {Wc Hb : κ' → ConvexSpaceBody E} {par : κ' → κ}
    {K Kh : ConvexSpaceBody E}
    (hocc : ∀ x ∈ ts, Wc x ≤ K → ∃ i ∈ q, assign i = par x ∧ Tb i ≤ Hb x)
    (hbody : ∀ x ∈ ts, Wc x ≤ K → Hb x ≤ Kh)
    (hshape : IsTubeShaped rad Kh) (hrρ : rad ≤ ρ) :
    ∃ V : Tube ρ E, ∀ x ∈ ts, Wc x ≤ K →
      ∃ i ∈ q, assign i = par x ∧ Tb i ≤ V.toConvexSpaceBody := by
  rcases hshape with ⟨V₀, hV₀⟩
  refine ⟨V₀.rescale ρ, ?_⟩
  intro x hx hxK
  rcases hocc x hx hxK with ⟨i, hi, hassigni, hTiHb⟩
  exact ⟨i, hi, hassigni,
    le_trans hTiHb (le_trans (hbody x hx hxK) (le_trans hV₀ (V₀.le_rescale hrρ)))⟩

/-- **The thick-plank concentration hypothesis of GWZ Lemma 6.4, from the confinement datum.**

The shaded-family adapter, in the shape `Kakeya.factoringAndMultPropCombined` now produces and
`Kakeya.FrostmanEstimate.plankEstimate` consumes.  The container is the exact Lean thickened plank,
as Lemma 6.4 requires; the confinement datum is about the *actual* factor bodies, so no false
statement about the thickened plank's shape is needed.  Concentration parameter

`M = (Cu * Csplit) * (b / a)`,

with `Cu` the external leaf-mediated overlap constant and no covering constant at all. -/
theorem shadedPlankConcentration_of_confinedWitness
    {ι κ κ' : Type*} {δ ρ' a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {q : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {r : Finset κ} {assign : ι → κ} {Cu Csplit : ℝ≥0}
    {ts : Finset κ'} {W : κ' → ShadedPlank a b hab hb1} {par : κ' → κ}
    (hover : ∀ V : Tube ρ' (EuclideanSpace ℝ (Fin 3)),
      ((({k ∈ r | ∃ i ∈ q, assign i = k ∧
        ((T i).toTube).toConvexSpaceBody ≤ V.toConvexSpaceBody}).card : ℝ≥0)) ≤ Cu)
    (hpar_mem : ∀ x ∈ ts, par x ∈ r)
    (hconf : ∀ j ∈ ts, ∀ (θ : ℝ≥0), a / b ≤ θ → ∀ (hθ1 : θ ≤ 1),
      ∃ V : Tube ρ' (EuclideanSpace ℝ (Fin 3)), ∀ x ∈ ts,
        (W x).carrier ⊆ (Plank.thickened (W j).toPrism3D θ hθ1).carrier →
        ∃ i ∈ q, assign i = par x ∧
          ((T i).toTube).toConvexSpaceBody ≤ V.toConvexSpaceBody)
    (hloc : ∀ j ∈ ts, ∀ (θ : ℝ≥0), a / b ≤ θ → ∀ (hθ1 : θ ≤ 1),
      ∀ k ∈ r,
        (({x ∈ ts | (W x).carrier ⊆ (Plank.thickened (W j).toPrism3D θ hθ1).carrier ∧
            par x = k}.card : ℝ≥0)) ≤ (Csplit * (b / a)) * θ) :
    ∀ j ∈ ts, ∀ (θ : ℝ≥0), a / b ≤ θ → ∀ (hθ1 : θ ≤ 1),
      (({x ∈ ts | (W x).carrier ⊆
          (Plank.thickened (W j).toPrism3D θ hθ1).carrier}.card : ℝ≥0))
        ≤ ((Cu * Csplit) * (b / a)) * θ := by
  intro j hj θ hθab hθ1
  have hbridge : ∀ (X Y : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))),
      X ≤ Y ↔ (X.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ Y.carrier := by
    intro X Y
    rfl
  let Tb : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun i => ((T i).toTube).toConvexSpaceBody
  let Kthick : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    (Plank.thickened (W j).toPrism3D θ hθ1).toConvexSpaceBody
  let Wc : κ' → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun x => (W x).toConvexSpaceBody
  have hcar : ∀ x : κ', (W x).carrier ⊆ (Plank.thickened (W j).toPrism3D θ hθ1).carrier ↔
      Wc x ≤ Kthick := by
    intro x
    change (Wc x).carrier ⊆ Kthick.carrier ↔ Wc x ≤ Kthick
    exact (hbridge (Wc x) Kthick).symm
  have hfilter_top : ts.filter (fun x : κ' => (W x).carrier ⊆
        (Plank.thickened (W j).toPrism3D θ hθ1).carrier) =
      ts.filter (fun x : κ' => Wc x ≤ Kthick) := by
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, hcar x]
  have hfilter_j : ∀ k : κ, ts.filter (fun x : κ' => (W x).carrier ⊆
      (Plank.thickened (W j).toPrism3D θ hθ1).carrier ∧ par x = k) =
      ts.filter (fun x : κ' => Wc x ≤ Kthick ∧ par x = k) := by
    intro k
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, hcar x]
  have hconf' : ∃ V : Tube ρ' (EuclideanSpace ℝ (Fin 3)), ∀ x ∈ ts, Wc x ≤ Kthick →
      ∃ i ∈ q, assign i = par x ∧ Tb i ≤ V.toConvexSpaceBody := by
    obtain ⟨V, hV⟩ := hconf j hj θ hθab hθ1
    refine ⟨V, ?_⟩
    intro x hx hxK
    rcases hV x hx ((hcar x).mpr hxK) with ⟨i, hiq, hassign, hTi⟩
    exact ⟨i, hiq, hassign, by simpa [Tb] using hTi⟩
  have hlocal' : ∀ k ∈ r, (({x ∈ ts | Wc x ≤ Kthick ∧ par x = k}.card : ℝ≥0)) ≤
      Csplit * (b / a) * θ := by
    intro k hk
    rw [← hfilter_j k]
    exact hloc j hj θ hθab hθ1 k hk
  have hmain : (({x ∈ ts | Wc x ≤ Kthick}.card : ℝ≥0)) ≤
      Cu * (Csplit * (b / a) * θ) := by
    rw [← hfilter_top]
    exact card_le_of_confinedWitness (E := EuclideanSpace ℝ (Fin 3)) hover hpar_mem
      hconf' (m := Csplit * (b / a) * θ) hlocal'
  rw [hfilter_top]
  have hstep : ((Cu * Csplit) * (b / a)) * θ = Cu * (Csplit * (b / a) * θ) := by
    ring
  exact le_trans hmain (le_of_eq hstep.symm)

/-! ### The cross-parent test dilation

GWZ Lemma 6.4 tests non-concentration against the `C_NC`-dilation of a `θ`-thickened plank, whose
transversal half-widths are `C_NC · θ b` and `C_NC · b`. The confinement datum is therefore *stated*
at the radius `(2 C_NC + 2) · ρ`, not `8 ρ`: the aligned container's `8 ρ` budget is *not* enough once
`C_NC > 3`. `(2 C_NC + 2) · ρ` is a chosen radius, not a derived transversal bound — a `Tube` has a
disc cross-section, so the transversal requirement is `C_NC · b · sqrt (1 + θ ^ 2)`, up to
`2 * sqrt 2 * C_NC * ρ` under `b ≤ 2ρ`, and that exceeds `(2 C_NC + 2) ρ` for `C_NC > 2.414…`. The constant is fixed by what the leafwise cover below can
absorb, not by a transversal match.

`Kakeya.ExternalParentSystem` is **not** generalized for this.  Its overlap field is already stated
for test tubes of radius `8 ·` (its own scale), and its construction
(`Kakeya.exists_externalParentSystem_of_four_mul_le`) puts no upper bound on that scale.  So the
parent system is simply instantiated at the enlarged scale `crossParentTestConst C_NC * ρ`, and its
own overlap radius `8 * (crossParentTestConst C_NC * ρ)` then dominates the confinement radius with
room to spare.  Nothing in the packing argument changes, and the overlap constant stays the
absolute `Kakeya.parentOverlapConst`.

The constant itself is `Kakeya.crossParentTestConst`, defined in `FrostmanPlankReduction.lean` so that
the Proposition-5.1 interface in `FrostmanPlankEstimate.lean` can state its confinement clause at that
radius. -/

/-- **The `C_NC`-dilated thick-plank non-concentration hypothesis of GWZ Lemma 6.4, from the
confinement datum.**

This is the theorem the corrected `Kakeya.FrostmanEstimate.plankEstimate` consumes.  Its conclusion
is literally `Plank.IsThickeningNonconcentrated`, so no aligned/dilated conversion happens anywhere:
the whole cross-parent count is run against the *dilated* test body

`((W j).toPrism3D.thickened φ hφ1).toPrismNDim.dilation C_NC`

from the outset.  `Kakeya.shadedPlankConcentration_of_confinedWitness` is the `C_NC = 1` shadow of
this statement and is retained only for reference; it is **not** used to derive this one, and it
cannot be — see the counterexample recorded with `Kakeya.plankReductionForFrostmanEstimate`.

The proof is the container-generic count `Kakeya.card_le_of_confinedWitness` instantiated at the
dilated body, so the argument is unchanged:

* `hconf` gives *one* test tube of radius `ρ'` catching an occupied leaf of every contributing
  cell's own external parent;
* `hover` bounds the contributing external parents by `Cu`;
* `hloc` is the within-parent count *at the dilated body*, and is summed over parents.

No hierarchy regrouping, no same-parent equality, no Katz--Tao estimate on a union of classes, and
no essential distinctness of the external labels.  The concentration parameter is

`M = (Cu * Csplit) * (b / a)`,

exactly as in the aligned version; the dilation is paid for inside `hconf` (a larger confinement
radius `ρ'`) and inside `hloc` (a larger within-parent constant), never in `M`. -/
theorem isThickeningNonconcentrated_of_externalParents
    {ι κ κ' : Type*} {δ ρ' a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {q : Finset ι} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {r : Finset κ} {assign : ι → κ} {Cu Csplit C_NC : ℝ≥0}
    {ts : Finset κ'} {W : κ' → ShadedPlank a b hab hb1} {par : κ' → κ}
    (hover : ∀ V : Tube ρ' (EuclideanSpace ℝ (Fin 3)),
      ((({k ∈ r | ∃ i ∈ q, assign i = k ∧
        ((T i).toTube).toConvexSpaceBody ≤ V.toConvexSpaceBody}).card : ℝ≥0)) ≤ Cu)
    (hpar_mem : ∀ x ∈ ts, par x ∈ r)
    (hconf : ∀ j ∈ ts, ∀ (θ : ℝ≥0) (hθ1 : θ ≤ 1), a / b ≤ θ →
      ∃ V : Tube ρ' (EuclideanSpace ℝ (Fin 3)), ∀ x ∈ ts,
        ((W x).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
            (((Plank.thickened (W j).toPrism3D θ hθ1).toPrismNDim.dilation C_NC).carrier :
              Set (EuclideanSpace ℝ (Fin 3))) →
        ∃ i ∈ q, assign i = par x ∧
          ((T i).toTube).toConvexSpaceBody ≤ V.toConvexSpaceBody)
    (hloc : ∀ j ∈ ts, ∀ (θ : ℝ≥0) (hθ1 : θ ≤ 1), a / b ≤ θ → ∀ k ∈ r,
      (({x ∈ ts | ((W x).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
          (((Plank.thickened (W j).toPrism3D θ hθ1).toPrismNDim.dilation C_NC).carrier :
            Set (EuclideanSpace ℝ (Fin 3))) ∧
          par x = k}.card : ℝ≥0)) ≤ (Csplit * (b / a)) * θ) :
    Plank.IsThickeningNonconcentrated ts (fun x => (W x).toPrism3D) C_NC
      ((Cu * Csplit) * (b / a)) := by
  classical
  intro j hj θ hθ1 hθab
  let Tb : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun i => ((T i).toTube).toConvexSpaceBody
  let Kdil : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    ((Plank.thickened (W j).toPrism3D θ hθ1).toPrismNDim.dilation C_NC).toConvexSpaceBody
  let Wc : κ' → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun x => (W x).toConvexSpaceBody
  have hcar : ∀ x : κ', (((W x).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (((Plank.thickened (W j).toPrism3D θ hθ1).toPrismNDim.dilation C_NC).carrier :
        Set (EuclideanSpace ℝ (Fin 3)))) ↔ Wc x ≤ Kdil := fun x => Iff.rfl
  have hfilter_top : ts.filter (fun x : κ' =>
        ((W x).toPrism3D.carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
          (((Plank.thickened (W j).toPrism3D θ hθ1).toPrismNDim.dilation C_NC).carrier :
            Set (EuclideanSpace ℝ (Fin 3))))
      = ts.filter (fun x : κ' => Wc x ≤ Kdil) := by
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, ← hcar x]
  have hfilter_j : ∀ k : κ, ts.filter (fun x : κ' =>
      ((W x).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
        (((Plank.thickened (W j).toPrism3D θ hθ1).toPrismNDim.dilation C_NC).carrier :
          Set (EuclideanSpace ℝ (Fin 3))) ∧ par x = k)
      = ts.filter (fun x : κ' => Wc x ≤ Kdil ∧ par x = k) := by
    intro k
    ext x
    rw [Finset.mem_filter, Finset.mem_filter, hcar x]
  have hconf' : ∃ V : Tube ρ' (EuclideanSpace ℝ (Fin 3)), ∀ x ∈ ts, Wc x ≤ Kdil →
      ∃ i ∈ q, assign i = par x ∧ Tb i ≤ V.toConvexSpaceBody := by
    obtain ⟨V, hV⟩ := hconf j hj θ hθ1 hθab
    refine ⟨V, ?_⟩
    intro x hx hxK
    rcases hV x hx ((hcar x).mpr hxK) with ⟨i, hiq, hassign, hTi⟩
    exact ⟨i, hiq, hassign, by simpa [Tb] using hTi⟩
  have hlocal' : ∀ k ∈ r, (({x ∈ ts | Wc x ≤ Kdil ∧ par x = k}.card : ℝ≥0)) ≤
      Csplit * (b / a) * θ := by
    intro k hk
    rw [← hfilter_j k]
    exact hloc j hj θ hθ1 hθab k hk
  have hmain : (({x ∈ ts | Wc x ≤ Kdil}.card : ℝ≥0)) ≤ Cu * (Csplit * (b / a) * θ) :=
    card_le_of_confinedWitness (E := EuclideanSpace ℝ (Fin 3)) hover hpar_mem hconf'
      (m := Csplit * (b / a) * θ) hlocal'
  rw [hfilter_top]
  exact le_trans hmain (le_of_eq (by ring : ((Cu * Csplit) * (b / a)) * θ
    = Cu * (Csplit * (b / a) * θ)).symm)

end Kakeya

end

end
