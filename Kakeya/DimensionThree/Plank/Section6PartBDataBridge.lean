/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Section6HallDecomposition
public import Kakeya.DimensionThree.Plank.GlobalPlankPartBBridge

/-!
# From `(PS, Fz)` to `Section6PartBData`

`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` (GWZ Proposition 6.6(B),
`Kakeya/DimensionThree/Plank/Factorization.lean`) quantifies over a pair

* `PS : Tube.IsUniformAtScale q (fun i => (T i).toTube) ρ Cpar`, and
* `Fz : GlobalPlankFactorization Cw a b hab hb1 PS.parent
    (fun k => (PS.parentTube k).toConvexSpaceBody) C₀`,

whereas the whole proved Part-(B) development downstream — beginning with
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData` — is stated over
`Kakeya.Section6PartBData`.  This file converts the first into the second.

`Section6PartBData` has exactly two fields, and each already has an owner:

* `factor` is `Kakeya.GlobalPlankFactorization.toSection6PartBFactorisation`
  (`Kakeya/DimensionThree/Plank/GlobalPlankPartBBridge.lean`), over the **same** coarse index set
  `PS.parent` and the **same** coarse family `PS.parentTube` that `Fz` is stated over;
* `decomp` is `Kakeya.Section6CoarseTubeDecomposition.ofUniformAtScaleHall`
  (`Kakeya/DimensionThree/Plank/Section6HallDecomposition.lean`), likewise over the full parent set.

The coarse index sets therefore agree on the nose and the two halves compose.  What the conversion
needs beyond the hypotheses Proposition 6.6(B) already carries is recorded below, field by field.

## What Proposition 6.6(B) already supplies

All of the following are derivable inside the statement of
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`, at any threshold `δ₀ ≤ 1`:

* `δ ≤ ρ`, by `Kakeya.Prop66BScale.le_of_plankScale_le` from `δ ^ (1 - ε₂) ≤ ρ`;
* `0 < ρ`, `0 < a`, `0 < b`, from `δ ≤ ρ ≤ a ≤ b` and `0 < δ`;
* `q.Nonempty`, from the fullness hypothesis `δ ^ η ≤ fullness q 𝕋` — the empty family has
  fullness `0`;
* `PS.parent.Nonempty` (`Kakeya.parent_nonempty_of_nonempty`) and `0 < PS.branchingN`
  (`Kakeya.branchingN_pos_of_nonempty`), from `q.Nonempty`;
* `Fz.parts.Nonempty`, from `PS.parent.Nonempty` through the underlying `Finpartition`;
* `1 ≤ Cw`, which is the field `Kakeya.GlobalPlankFactorization.one_le_Cw`;
* `1 ≤ Cpar`, after replacing `PS` by `PS.mono` at `max 1 Cpar` — a *weakening* of the uniformity
  datum that leaves `parent`, `parentTube` and `branchingN` untouched, so `Fz` still typechecks
  against it, and which keeps the budget since `Cpar ≤ δ ^ (-η)` and `1 ≤ δ ^ (-η)`.

## What it does **not** supply, and who does

Two hypotheses of `Kakeya.Section6PartBData.ofUniformAtScaleOfGlobalPlank` are **not** available
from Proposition 6.6(B) as it currently stands.

**(1) The parent window `hballs`: the coarse `ρ`-tubes lie in the closed unit ball.  NOT owed —
6.6(B)'s leaf window is at the wrong radius, not missing.**  Proposition 6.6(B) normalises only the
*leaves*, and at radius exactly `1`; neither its remaining hypotheses nor any field of
`Tube.IsUniformAtScale` says where the parent tubes lie, since the parent family is explicitly a
family of *free* `ρ`-tubes with cores anywhere.

The tree already measures the gap exactly:
`Kakeya.ML2Reduction.parentTube_carrier_subset_closedBall` proves that leaves inside `B̄(0, r)`
force parents inside `B̄(0, r + 4 ρ)`.  At `r = 1` that is `B̄(0, 1 + 4 ρ)`, which is why the window
does not come for free; at `r + 4 ρ ≤ 1` it *is* the parent window, and that inequality is already a
hypothesis of `Kakeya.ML2Reduction.eccentric_of_maxDensityFactoring_of_leafBall`.  The discharge is
`Kakeya.parentWindow_of_leafWindow`, and
`Kakeya.Section6PartBData.ofUniformAtScaleOfGlobalPlankOfLeafBall` is this file's constructor with
`hballs` replaced by the leaf window (both in
`Kakeya/DimensionThree/MainLemma2/Reduction/PartBDatumAtCallSite.lean`, which may cite
`Kakeya.ML2Reduction`; this file may not).  Independently,
`Kakeya.ML2Reduction.PlankFactoringData.ball` is character-for-character `hballs`, so the one
application site supplies it twice over.

The window is consumed at exactly one place, the `repr_window` field, through
`Kakeya.framedPlank_subset_closedBall`, whose numerical margin is *tight*: the framed plank of a
body inside `closedBall 0 1` lies in `closedBall 0 4` (`Kakeya.plankWindowRadius`) with the
squared-norm budget `1 + 8 + 4·(3/2) + 1 = 16` exactly saturated, so no slack is available to
absorb a larger window on the body.  That is why the repair is to tighten `r`, not to widen the
window.

**(2) The branching floor `(max 1 Cpar) ^ 2 ≤ PS.branchingN`.  Now a HYPOTHESIS of Proposition
6.6(B), because it is a missing datum.**

Since steps  the floor is carried by
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` itself, beside `Cpar ≤ δ ^ (-η)`, and threaded
to the one application site; the old branching-free form is pinned as
`Kakeya.Prop66BScale.statement_of_universal_prop66B_plankScale` and the new one as
`Kakeya.Prop66BScale.statement_of_universal_prop66B_branchingFloor`.  Four facts fix its
status.

*It is a statement about the configuration, not a choice of parameter.*
`Kakeya.branchingN_le_mul_card_parentContainment` is `N ≤ C · |F_j|`, so `branchingN` cannot be
inflated: it is pinned to within `C` of the containment counts, in `Tube.IsUniformAtScale` and
equally in `Tube.UniformTubeSet` and `Tube.ChainUniformTubeSet`, whose `branchingN` fields are
bracketed by `card_class_le` and `le_card_class`.  Read on the configuration the floor says *every
coarse `ρ`-tube carries at least `Cpar` fine tubes*
(`Kakeya.le_card_parentContainment_of_sq_le_branchingN`), and one parent carrying `Cpar ^ 3` of them
already gives it back (`Kakeya.sq_le_branchingN_of_cube_le_card_parentContainment`).

*It is necessary for this route.*  `Kakeya.Section6CoarseTubeDecomposition.card_coarseSet_le_card`
shows that any decomposition forces `|coarseSet| ≤ |q|`, a genuine cardinality constraint that the
uniformity datum does not carry; `Kakeya.card_parent_le_card_of_sq_le_branchingN` shows the floor
restores it.

*It is not implied by the numbers the datum exports.*
`Kakeya.not_exists_sdr_of_uniform_numeric_fields` exhibits a bipartite system meeting **all seven**
numeric facts available — including the two the producers add, `1 ≤ N` and
`|𝕋_ρ| · N ≤ |𝕋| ≤ 2 |𝕋_ρ| · N` from `Tube.refineToEssDistinctUniform` — with no system of distinct
representatives.  There, no assignment whatever gives every parent a nonempty fibre.

*And the cardinality band does not reach it either.*
`Kakeya.band_consistent_with_unit_branching` shows that Main Lemma 2's `|𝕋| > δ^{-1}`, together with
that same two-sided count and any covering bound `|𝕋_ρ| ≤ ρ^{-4}`, is satisfiable at branching
exactly `1` when `ρ = δ ^ (1 - ε₂)`.

A tree-wide scan finds the strongest lower bound on any `branchingN` anywhere to be `1 ≤ branchingN`
(`Tube.refineToEssDistinctUniform`, `Tube.exists_uniform_subset_tight_injLeaves`).  So the floor has
no producer today; it is owed by whoever eventually builds the `PS` that Main Lemma 2 hands to
Proposition 6.6(B), and the branching numbers are known there, at the point where the class sizes
are.  It survives the one refinement the chain performs
(`Kakeya.ML2Reduction.branchingN_restrictParents`, `rfl`).

## The re-declared half-widths

The datum produced below is at the half-widths `(Fz.uniformThin, Fz.uniformMid)`, not at the
declared `(a, b)`; that is the re-declaration forced by
`Kakeya.GlobalPlankFactorization.toSection6PartBFactorisation`, and the bookkeeping back to `(a, b)`
is `Kakeya.GlobalPlankFactorization.uniformThin_le` (`A ≤ a`) together with
`Kakeya.GlobalPlankFactorization.le_mul_uniformMid` (`b ≤ K * B`), both already proved.  The fibre
comparability constant is `2 * Cpar ^ 2`, inside the sub-polynomial budget whenever
`Cpar ≤ δ ^ (-η)`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace Kakeya

/-! ### Nondegeneracy facts that Proposition 6.6(B) already implies -/

variable {ι : Type*} {δ : ℝ≥0} {q : Finset ι}
  {Tt : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} {ρ C : ℝ≥0}

/-- A nonempty leaf family has a nonempty parent family. -/
theorem parent_nonempty_of_nonempty (U : Tube.IsUniformAtScale q Tt ρ C) (hq : q.Nonempty) :
    U.parent.Nonempty := by
  obtain ⟨i, hi⟩ := hq
  obtain ⟨j, hj, _⟩ := U.exists_le_rescale hi
  exact ⟨j, hj⟩

open Classical in
/-- **The branching number of a nonempty uniform family is positive.**  A leaf lies in some parent,
so that parent's containment set is nonempty, and `card_filter_le` then forbids `N = 0`. -/
theorem branchingN_pos_of_nonempty (U : Tube.IsUniformAtScale q Tt ρ C) (hq : q.Nonempty) :
    0 < U.branchingN := by
  classical
  obtain ⟨i, hi⟩ := hq
  obtain ⟨j, hj, hij⟩ := U.exists_le_rescale hi
  have h1 : (1 : ℝ≥0) ≤ ((parentContainment U j).card : ℝ≥0) := by
    have hne : (parentContainment U j).Nonempty := ⟨i, mem_parentContainment.mpr ⟨hi, hij⟩⟩
    exact_mod_cast Finset.card_pos.mpr hne
  have h3 : (1 : ℝ≥0) ≤ C * U.branchingN := h1.trans (card_parentContainment_le U hj)
  rcases eq_zero_or_pos U.branchingN with h0 | h0
  · exfalso
    rw [h0, mul_zero] at h3
    exact absurd h3 (by norm_num)
  · exact h0

open Classical in
/-- **The branching floor forces the parent family to be no larger than the leaf family.**

Each parent sees at least `N / C` leaves, each leaf is seen by at most `C` parents, so
`|𝕋_ρ| · N ≤ C² · |𝕋|`; with `C² ≤ N` this is `|𝕋_ρ| ≤ |𝕋|`.  Compare
`Kakeya.Section6CoarseTubeDecomposition.card_coarseSet_le_card`: that inequality is *forced* by the
existence of a decomposition over the full parent family, and `Tube.IsUniformAtScale` alone
does not imply it. -/
theorem card_parent_le_card_of_sq_le_branchingN (U : Tube.IsUniformAtScale q Tt ρ C)
    (hδρ : δ ≤ ρ) (hC : 1 ≤ C) (hNC : C ^ 2 ≤ U.branchingN) :
    U.parent.card ≤ q.card := by
  classical
  have hC2 : (0 : ℝ≥0) < C ^ 2 := by positivity
  have hmain := card_mul_branchingN_le U hδρ (subset_refl U.parent)
  have hsub : U.parent.biUnion (parentContainment U) ⊆ q := by
    intro i hi
    rw [Finset.mem_biUnion] at hi
    obtain ⟨j, _, hij⟩ := hi
    exact (mem_parentContainment.mp hij).1
  have hcard : ((U.parent.biUnion (parentContainment U)).card : ℝ≥0) ≤ (q.card : ℝ≥0) := by
    exact_mod_cast Finset.card_le_card hsub
  have hstep : (U.parent.card : ℝ≥0) * C ^ 2 ≤ C ^ 2 * (q.card : ℝ≥0) := by
    calc (U.parent.card : ℝ≥0) * C ^ 2 ≤ (U.parent.card : ℝ≥0) * U.branchingN := by gcongr
      _ ≤ C ^ 2 * (((U.parent.biUnion (parentContainment U)).card : ℝ≥0)) := hmain
      _ ≤ C ^ 2 * (q.card : ℝ≥0) := by gcongr
  have hstep' : (U.parent.card : ℝ≥0) * C ^ 2 ≤ (q.card : ℝ≥0) * C ^ 2 := by
    rw [mul_comm ((q.card : ℝ≥0)) (C ^ 2)]
    exact hstep
  have hfin : (U.parent.card : ℝ≥0) ≤ (q.card : ℝ≥0) := le_of_mul_le_mul_right hstep' hC2
  exact_mod_cast hfin

namespace Section6CoarseTubeDecomposition

open Classical in
/-- **A coarse decomposition forces `|𝕋_ρ| ≤ |𝕋|`.**  Every coarse index in use carries a nonempty
fibre of the *function* `assign`, so the coarse index set is contained in the image of `assign`.

This is the cardinality content of the `fibre_nonempty` clause, and it is what
`Tube.IsUniformAtScale` does not supply on its own. -/
theorem card_coarseSet_le_card {ι κ : Type*} {q : Finset ι} {δ : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {coarseSet : Finset κ} {ρ : ℝ≥0}
    {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))} {m Cfib : ℝ≥0}
    (D : Section6CoarseTubeDecomposition q T coarseSet R m Cfib) :
    coarseSet.card ≤ q.card := by
  classical
  have hsub : coarseSet ⊆ q.image D.assign := by
    intro k hk
    obtain ⟨i, hi⟩ := D.fibre_nonempty k hk
    have hi' : i ∈ q ∧ D.assign i = k := by simpa [Finset.mem_filter] using hi
    exact Finset.mem_image.mpr ⟨i, hi'.1, hi'.2⟩
  exact le_trans (Finset.card_le_card hsub) (Finset.card_image_le)

end Section6CoarseTubeDecomposition

/-! ### The `|𝕋| > δ^{-1}` band does not reach the floor -/

/-- **Prof. Wang's cardinality band does not supply the branching floor.**

Main Lemma 2 needs `|𝕋| > δ^{-1}`, an *output* of bilinearity rather than a case split.  It is natural to hope the floor follows: the branching is `≈ |𝕋| / |𝕋_ρ|`, so a
lower bound on `|𝕋|` plus an upper bound on `|𝕋_ρ|` would give one.  It does not, and the reason is
that the coarse scale is *close to* `δ`, so the covering bound on `|𝕋_ρ|` is far larger than the
band.

This is that obstruction, in pure arithmetic and with no tube geometry: at `ρ = δ ^ (1 - ε₂)`, the
band `δ^{-1} ≤ |𝕋|`, the producers' own two-sided count `|𝕋| ≤ 2 · |𝕋_ρ| · N`
(`Tube.refineToEssDistinctUniform`) and **any** covering bound `|𝕋_ρ| ≤ ρ^{-4}` — the sharp count of
essentially distinct `ρ`-tubes in the unit ball in `ℝ³`, and a fortiori the tree's own cruder
`ρ^{-2n}` at `n = 3` — are simultaneously satisfiable with `N = 1`, hence with `N` below every floor
`δ ^ (-2η)`.  The witness is `|𝕋| = |𝕋_ρ| = δ^{-1}`, `N = 1`.

So the band route is closed, and the floor remains a hypothesis of
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` rather than a consequence of it. -/
theorem band_consistent_with_unit_branching {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {ε₂ : ℝ} (hε₂ : ε₂ ≤ 1 / 2) {η : ℝ} (hη : 0 < η) :
    ∃ card parents branch : ℝ≥0,
      δ ^ (-1 : ℝ) ≤ card ∧
      card ≤ 2 * parents * branch ∧
      parents ≤ (δ ^ (1 - ε₂)) ^ (-(4 : ℝ)) ∧
      branch < δ ^ (-2 * η) := by
  refine ⟨δ ^ (-1 : ℝ), δ ^ (-1 : ℝ), 1, le_rfl, ?_, ?_, ?_⟩
  · rw [mul_one]
    calc δ ^ (-1 : ℝ) = 1 * δ ^ (-1 : ℝ) := (one_mul _).symm
      _ ≤ 2 * δ ^ (-1 : ℝ) := by gcongr; norm_num
  · rw [← NNReal.rpow_mul]
    refine NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le ?_
    nlinarith
  · have := NNReal.rpow_lt_rpow_of_exponent_gt hδ0 hδ1 (show (-2 * η) < 0 by nlinarith)
    simpa using this


/-! ### The assembly -/

open Classical in
/-- **The Part-(B) datum, built from the pair `(PS, Fz)` that GWZ Proposition 6.6(B) quantifies
over.**

Both halves live over the **same** coarse index set `PS.parent` and the **same** coarse family
`PS.parentTube`, so they compose with no reindexing:

* `factor := Fz.toSection6PartBFactorisation`, which supplies the representative planks as data,
  the working-window containment and the Remark-5.3 coarse-fibre Frostman clause, at the
  re-declared half-widths `(Fz.uniformThin, Fz.uniformMid)`;
* `decomp := Section6CoarseTubeDecomposition.ofUniformAtScaleHall`, whose fibre lower bound is
  produced by Hall's marriage theorem rather than assumed.

Of the nine hypotheses, seven are derivable inside the statement of
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` (see the module docstring).  The two that are
not are `hNC` — the branching floor, whose cardinality content is
`Kakeya.card_parent_le_card_of_sq_le_branchingN` and which no `Tube.IsUniformAtScale`
implies on its own — and `hballs`, the parent window, which is exactly the field
`Kakeya.ML2Reduction.PlankFactoringData.ball` at the single application site.

The universe restriction `ι : Type` is inherited from
`Kakeya.GlobalPlankFactorization.toSection6PartBFactorisation`, whose cell type is `Finset κ` and
whose target field `Kakeya.Section6PartBFactorisation.Cell` lives in `Type`; the same restriction
already appears as `{κ : Type}` in
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData`. -/
def Section6PartBData.ofUniformAtScaleOfGlobalPlank
    {ι : Type} {q : Finset ι} {δ : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {ρ Cpar : ℝ≥0}
    {Cw a b C₀ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (PS : Tube.IsUniformAtScale q (fun i => (T i).toTube) ρ Cpar)
    (Fz : GlobalPlankFactorization Cw a b hab hb1 PS.parent
      (fun k => (PS.parentTube k).toConvexSpaceBody) C₀)
    (hCpar : 1 ≤ Cpar) (hδρ : δ ≤ ρ) (hNC : Cpar ^ 2 ≤ PS.branchingN)
    (hb0 : 0 < b) (hρ : 0 < ρ) (hq : q.Nonempty)
    (hballs : ∀ k ∈ PS.parent,
      (PS.parentTube k).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Section6PartBData Fz.uniformThin Fz.uniformMid Fz.uniformThin_le_uniformMid
      (Fz.uniformMid_le_one hballs) q T PS.parent PS.parentTube
      PS.branchingN (2 * Cpar ^ 2)
      (GlobalPlankFactorization.partBFrostmanConst Cw C₀) C₀ where
  decomp := Section6CoarseTubeDecomposition.ofUniformAtScaleHall PS hCpar hδρ
    (branchingN_pos_of_nonempty PS hq) hNC
  factor := Fz.toSection6PartBFactorisation Fz.one_le_Cw hb1 hb0 hρ
    (by
      obtain ⟨j, hj⟩ := parent_nonempty_of_nonempty PS hq
      obtain ⟨t, ht, _⟩ := Fz.toFinpartition.exists_mem hj
      exact ⟨t, ht⟩)
    hballs


open Classical in
/-- **`1 ≤ Cpar` is free**, so the assembly above needs it only for bookkeeping.

`Tube.IsUniformAtScale.mono` leaves `parent`, `parentTube` and `branchingN` untouched — the two
`rfl`s below are the pin — so the very same `Fz` typechecks against the weakened uniformity datum,
and the only visible change is the fibre comparability constant, which becomes
`2 * max 1 Cpar ^ 2` and therefore still sits inside the budget `Cpar ≤ δ ^ (-η)` because
`1 ≤ δ ^ (-η)` for `δ ≤ 1`.

Two hypotheses remain that GWZ Proposition 6.6(B) does not carry: `hNC` and `hballs`. -/
def Section6PartBData.ofUniformAtScaleOfGlobalPlank'
    {ι : Type} {q : Finset ι} {δ : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {ρ Cpar : ℝ≥0}
    {Cw a b C₀ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (PS : Tube.IsUniformAtScale q (fun i => (T i).toTube) ρ Cpar)
    (Fz : GlobalPlankFactorization Cw a b hab hb1 PS.parent
      (fun k => (PS.parentTube k).toConvexSpaceBody) C₀)
    (hδρ : δ ≤ ρ) (hNC : max 1 Cpar ^ 2 ≤ PS.branchingN)
    (hb0 : 0 < b) (hρ : 0 < ρ) (hq : q.Nonempty)
    (hballs : ∀ k ∈ PS.parent,
      (PS.parentTube k).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Section6PartBData Fz.uniformThin Fz.uniformMid Fz.uniformThin_le_uniformMid
      (Fz.uniformMid_le_one hballs) q T PS.parent PS.parentTube
      PS.branchingN (2 * max 1 Cpar ^ 2)
      (GlobalPlankFactorization.partBFrostmanConst Cw C₀) C₀ :=
  Section6PartBData.ofUniformAtScaleOfGlobalPlank
    (PS.mono (le_max_right 1 Cpar) (le_max_right 1 Cpar)) Fz
    (le_max_left 1 Cpar) hδρ hNC hb0 hρ hq hballs

/-- `Tube.IsUniformAtScale.mono` does not move the parent family. -/
theorem mono_parent_eq {ι : Type*} {δ : ℝ≥0} {q : Finset ι}
    {Tt : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} {ρ C C' : ℝ≥0} (hC : C ≤ C')
    (U : Tube.IsUniformAtScale q Tt ρ C) : (U.mono hC hC).parent = U.parent := rfl

/-- `Tube.IsUniformAtScale.mono` does not move the branching number. -/
theorem mono_branchingN_eq {ι : Type*} {δ : ℝ≥0} {q : Finset ι}
    {Tt : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} {ρ C C' : ℝ≥0} (hC : C ≤ C')
    (U : Tube.IsUniformAtScale q Tt ρ C) : (U.mono hC hC).branchingN = U.branchingN := rfl


end Kakeya

end

end
