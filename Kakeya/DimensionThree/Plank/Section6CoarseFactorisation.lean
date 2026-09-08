/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.GlobalPlankFactorization

/-!
# Section 6: the coarse-parent input layer of GWZ Proposition 6.6(B)

Proposition 6.6(B) is currently stated with the hypothesis

`∀ i ∈ q, ∃ k ∈ r, (T i).toConvexSpaceBody ≤ (R k).toConvexSpaceBody`,

i.e. "every fine tube lies in *some* coarse tube".  That is strictly weaker than the datum the
paper uses, and the gap is not cosmetic: the proof of 6.6(B) needs a *function* `𝒯 → 𝒯_ρ` whose
fibres have comparable cardinality, and it needs the coarse family sitting over an outer plank `W`
to be Frostman **in `W`**.  Neither is a consequence of a bare existential cover.  This file
supplies the missing data.

## What the check found

The uniformity API (`Tube.IsUniformAtScale`) genuinely provides, at a scale `ρ`:

* a parent family, indexed by `parent`, of `ρ`-tubes `(T j).rescale ρ` (field `exists_le_rescale`);
* an *existential* assignment of each fine tube to a parent containing it (same field);
* a common branching number `branchingN`, and two-sided comparability of the cardinality of each
  **containment** set `{i ∈ s | T i ≤ (T j).rescale ρ}` with it (fields `card_filter_le` and
  `le_mul_card_filter`);
* pairwise essential distinctness of the parents.

It does **not** provide:

1. an assignment *function* — only the existential.  Choosing one is harmless
   (`Kakeya.uniformCoarseAssign`), but a chosen function has *smaller* fibres than the containment
   sets, because a fine tube may lie in several parents at once;
2. consequently, the **lower** bound for the fibres of a chosen assignment.  The upper bound
   transfers (a fibre is contained in a containment set,
   `Kakeya.Section6CoarseTubeDecomposition.card_fibre_le_of_uniformAtScale`),
   the lower bound does not: `le_mul_card_filter` bounds the containment set, and the assignment may
   have routed all of its members elsewhere.  Repairing this needs a bounded-overlap count for the
   parent family, which is a separate (available, but distinct) input;
3. any Frostman datum whatsoever, at either scale.

`Kakeya.Section6CoarseTubeDecomposition` therefore records exactly the four genuine items — a
function, its membership, leafwise containment, and two-sided fibre comparability — and the
constructor `Kakeya.Section6CoarseTubeDecomposition.ofUniformAtScale` discharges every clause that
uniformity does give, leaving item 2 as a single named hypothesis rather than fabricating it.
Nonemptiness of the fibres is *not* a hypothesis there: the coarse index set is taken to be the set
of parents actually used, `q.image assign`, for which nonemptiness is automatic.

## The Part-(B) factorisation datum

`Kakeya.GlobalComparableBodyFactorization` already carries the outer Katz--Tao property, cellwise
containment of the coarse tubes, and containment of each cell body in an `a × b × 1` plank.  What it
does not carry is the **coarse-fibre Frostman** datum, and it presents the representative plank as
an existential (`le_plank`) rather than as data.  `Kakeya.Section6PartBFactorisation` adds both:

* `repr` and `body_le_repr` — the representative `a × b × 1` plank of each cell, as data.  The
  actual cell body and its representative plank stay strictly separate; no actual body is ever
  assumed to *be* a plank (that hypothesis is unsatisfiable, see
  `Kakeya.not_plankFactorization_tubes_of_pos`);
* `coarse_fibre_frostman` — the coarse fibre `𝒯_{ρ,W}` is `C_F`-Frostman **in the representative
  plank**, which is where the paper's `W` lives and where the consumer needs it.

There is deliberately **no** fine-fibre Frostman clause.  That is the whole content of GWZ
Remark 5.3: the fine family need not be Frostman, and every estimate that looks like it needs a fine
Frostman datum is obtained instead from the coarse one plus fibre comparability.  The two theorems
that make this precise here are

* `Kakeya.Section6PartBData.remark53FibreFrostman` — the coarse (and only the coarse) Frostman
  hypothesis, in the exact shape a Proposition-5.1 black box consumes; and
* `Kakeya.Section6PartBData.remark53_card_fine_le` — the *fine* slab count
  `|{i : R (assign i) ⊆ K}| ≤ C_fib² · C_vol · C_F · θ · |𝒯_W|` for any `K ⊆ W` of relative volume
  `θ`, derived with no fine Frostman input at all.  This is the `γ = 1` non-concentration datum of
  GWZ Lemma 6.1 that Proposition 6.6(B) actually uses.

## The scale relation

`ρ ≤ a` is a consequence of the datum, not an assumption: a `ρ`-tube contains a ball of radius `ρ`,
it lies in its cell body, and the cell body lies in the representative `a × b × 1` plank, whose
least width is `a` (`Kakeya.Section6PartBFactorisation.rho_le`).  This uses only the honest
representative geometry — containment in the plank — and never an equality of actual body and plank.

## What is still expected from the merged Proposition 5.1

`Kakeya.Section6PartBData.transverseFactorInput` produces, cell by cell, *exactly* the hypothesis
list of `Kakeya.katzTaoTransverseFactorBound` (which is what the `γ = 1` affine-normalisation layer
consumes).  Nothing in this file normalises anything.  Beyond that, Proposition 6.6(B) still needs
from the merged Proposition 5.1, and from nowhere else:

1. the multiplicity split `μ(𝒯, Y) ≤ C · μ(𝒲) · μ(𝒯_W)` for the **fine** family, granted the
   coarse-fibre Frostman datum `Kakeya.Section6PartBData.remark53FibreFrostman` — this is the
   Remark-5.3 upgrade of Proposition 5.1 and is *not* derivable from the present interface;
2. the cardinality bound `|𝒲| · |𝒯_W| ≤ C · |𝒯|`;
3. the outer fullness lower bound for the selected cells.

Items 1--3 are the only facts `Kakeya.factoringAndMultPropGlobal` needs that this file does not
provide; everything else in its statement is either produced here or already available.  The
migration of `Kakeya.factoringAndMultPropGlobal` itself is a one-line hypothesis swap: the present
weak cover is recovered from the new datum by
`Kakeya.Section6CoarseTubeDecomposition.exists_parent`.
-/

@[expose] public section

open MeasureTheory Convexity
-- Every fibre in this file is a `Finset.filter` over an arbitrary index type, so the classical
-- instance is needed both in the statements and inside the proofs;
-- `Kakeya.GlobalComparableBodyFactorization` opens it file-wide for the same reason.
set_option linter.style.openClassical false
open scoped NNReal ENNReal Classical

noncomputable section

namespace Kakeya

/-! ## The coarse tube decomposition -/

open Classical in
/-- **The Section-6 coarse tube decomposition** (the honest form of "the fine tubes lie over the
coarse tubes").

A *function* `assign` from fine to coarse indices, with leafwise containment and two-sided fibre
comparability around a common size `m`.  This is the `T_ρ` datum of GWZ Section 6, and it is what
`Kakeya.katzTaoTransverseFactorBound` consumes.

Every field is genuine data supplied by the uniformity of the fine family at scale `ρ`, except the
fibre lower bound `le_card_fibre`; see the module docstring and
`Kakeya.Section6CoarseTubeDecomposition.ofUniformAtScale`. -/
structure Section6CoarseTubeDecomposition
    {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    {κ : Type*} (coarseSet : Finset κ) {ρ : ℝ≥0}
    (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (m Cfib : ℝ≥0) where
  /-- The coarse index carrying each fine index. -/
  assign : ι → κ
  /-- The coarse index of a fine index in use is in use. -/
  assign_mem : ∀ i ∈ q, assign i ∈ coarseSet
  /-- Each fine tube lies in its own coarse tube. -/
  leaf_le_parent : ∀ i ∈ q, (T i).toConvexSpaceBody ≤ (R (assign i)).toConvexSpaceBody
  /-- The comparability constant is at least `1`. -/
  one_le_Cfib : 1 ≤ Cfib
  /-- The common fibre size is positive. -/
  m_pos : 0 < m
  /-- Every coarse index in use carries at least one fine index. -/
  fibre_nonempty : ∀ k ∈ coarseSet, ({i ∈ q | assign i = k} : Finset ι).Nonempty
  /-- Fibre comparability, lower half. -/
  le_card_fibre : ∀ k ∈ coarseSet,
    m / Cfib ≤ (({i ∈ q | assign i = k} : Finset ι).card : ℝ≥0)
  /-- Fibre comparability, upper half. -/
  card_fibre_le : ∀ k ∈ coarseSet,
    (({i ∈ q | assign i = k} : Finset ι).card : ℝ≥0) ≤ Cfib * m

namespace Section6CoarseTubeDecomposition

variable {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
  {m Cfib : ℝ≥0}

open Classical in
/-- The fibre of a coarse index: the fine indices assigned to it. -/
def fibre (D : Section6CoarseTubeDecomposition q T coarseSet R m Cfib) (k : κ) : Finset ι :=
  {i ∈ q | D.assign i = k}

variable (D : Section6CoarseTubeDecomposition q T coarseSet R m Cfib)

theorem mem_fibre_iff {k : κ} {i : ι} : i ∈ D.fibre k ↔ i ∈ q ∧ D.assign i = k := by
  simp [fibre, Finset.mem_filter]

theorem fibre_subset (k : κ) : D.fibre k ⊆ q := by
  intro i hi
  exact ((mem_fibre_iff D).mp hi).1

/-- **The current weak Part-(B) hypothesis is a consequence of the decomposition.**  This is the
one-line bridge that lets `Kakeya.factoringAndMultPropGlobal` swap its existential cover for the
honest datum without any other change. -/
theorem exists_parent (D' : Section6CoarseTubeDecomposition q T coarseSet R m Cfib) :
    ∀ i ∈ q, ∃ k ∈ coarseSet, (T i).toConvexSpaceBody ≤ (R k).toConvexSpaceBody := by
  intro i hi
  refine ⟨D'.assign i, D'.assign_mem i hi, D'.leaf_le_parent i hi⟩

/-- Fibre comparability in the two-sided guarded form consumed by
`Kakeya.katzTaoTransverseFactorBound`. -/
theorem comparable_fibres :
    ∀ k ∈ coarseSet, (D.fibre k).Nonempty →
      m / Cfib ≤ ((D.fibre k).card : ℝ≥0) ∧ ((D.fibre k).card : ℝ≥0) ≤ Cfib * m := by
  intro k hk _
  constructor
  · simpa [fibre] using D.le_card_fibre k hk
  · simpa [fibre] using D.card_fibre_le k hk

/-! ### Selected subfamilies -/

open Classical in
/-- **A selected fine fibre is contained in the full fibre**, hence inherits the upper bound. -/
theorem card_selected_fibre_le {q' : Finset ι} (hq' : q' ⊆ q) (k : κ) :
    (({i ∈ q' | D.assign i = k} : Finset ι).card : ℝ≥0) ≤ ((D.fibre k).card : ℝ≥0) := by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi
  simpa [Section6CoarseTubeDecomposition.fibre, Finset.mem_filter] using ⟨hq' hi.1, hi.2⟩

open Classical in
/-- **Restriction to a selected fine subfamily.**  The upper fibre bound is inherited; the lower one
is not (selection can empty a fibre), so it is an explicit hypothesis, exactly as for
`Kakeya.Section6CoarseTubeDecomposition.ofUniformAtScale`. -/
def restrict {q' : Finset ι} (hq' : q' ⊆ q) {Cfib' : ℝ≥0} (hCfib : Cfib ≤ Cfib')
    (hne : ∀ k ∈ coarseSet, ({i ∈ q' | D.assign i = k} : Finset ι).Nonempty)
    (hlb : ∀ k ∈ coarseSet,
      m / Cfib' ≤ (({i ∈ q' | D.assign i = k} : Finset ι).card : ℝ≥0)) :
    Section6CoarseTubeDecomposition q' T coarseSet R m Cfib' where
  assign := D.assign
  assign_mem := fun i hi => D.assign_mem i (hq' hi)
  leaf_le_parent := fun i hi => D.leaf_le_parent i (hq' hi)
  one_le_Cfib := le_trans D.one_le_Cfib hCfib
  m_pos := D.m_pos
  fibre_nonempty := hne
  le_card_fibre := hlb
  card_fibre_le := by
    intro k hk
    calc
      (({i ∈ q' | D.assign i = k} : Finset ι).card : ℝ≥0)
          ≤ ((D.fibre k).card : ℝ≥0) := card_selected_fibre_le D hq' k
      _ ≤ Cfib * m := D.card_fibre_le k hk
      _ ≤ Cfib' * m := by
        gcongr

/-! ### Counting transport -/

open Classical in
/-- **Fine counting from a selected coarse subfamily, fraction form.**  If the selected coarse
indices are a `Cθ`-fraction of the coarse family, the fine indices lying over them are a
`Cfib ^ 2 · Cθ`-fraction of the fine family.  No Frostman datum for the *fine* family is used. -/
theorem card_le_of_selected (hne : coarseSet.Nonempty)
    {Cθ : ℝ≥0} {sel : Finset κ} (hsel : sel ⊆ coarseSet)
    (hselcard : (sel.card : ℝ≥0) ≤ Cθ * (coarseSet.card : ℝ≥0))
    {qS : Finset ι} (hqS : qS ⊆ q) (hmem : ∀ i ∈ qS, D.assign i ∈ sel) :
    (qS.card : ℝ≥0) ≤ Cfib ^ 2 * Cθ * (q.card : ℝ≥0) := by
  classical
  have hlb : ∀ k ∈ coarseSet,
      Cfib⁻¹ * m ≤ (({i ∈ q | D.assign i = k} : Finset ι).card : ℝ≥0) := by
    intro k hk
    calc
      Cfib⁻¹ * m = m * Cfib⁻¹ := by rw [mul_comm]
      _ = m / Cfib := by rw [div_eq_mul_inv]
      _ ≤ (({i ∈ q | D.assign i = k} : Finset ι).card : ℝ≥0) := D.le_card_fibre k hk
  exact card_le_of_comparable_fibres_of_selected_le D.one_le_Cfib hne D.assign_mem hlb
    D.card_fibre_le hsel hselcard hqS hmem

end Section6CoarseTubeDecomposition

/-! ## Building a decomposition from uniformity -/

open Classical in
/-- **The assignment function chosen from single-scale uniformity.**

`Tube.IsUniformAtScale` supplies only the *existential* statement that each fine tube lies in
some parent; this is a choice of witness.  Choosing is harmless, but see
`Kakeya.Section6CoarseTubeDecomposition.ofUniformAtScale`: a chosen function has smaller fibres than
the containment sets that uniformity controls, so the fibre *lower* bound does not survive the
choice. -/
def uniformCoarseAssign {ι : Type*} {q : Finset ι} {δ : ℝ≥0}
    {Tt : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} {ρ C : ℝ≥0}
    (U : Tube.IsUniformAtScale q Tt ρ C) (i : ι) : ι :=
  if h : i ∈ q then Classical.choose (U.exists_le_rescale h) else i

namespace uniformCoarseAssign

variable {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {Tt : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}
  {ρ C : ℝ≥0} (U : Tube.IsUniformAtScale q Tt ρ C)

theorem mem_parent {i : ι} (hi : i ∈ q) : uniformCoarseAssign U i ∈ U.parent := by
  rw [uniformCoarseAssign, dif_pos hi]
  exact (Classical.choose_spec (U.exists_le_rescale hi)).1

theorem le_rescale {i : ι} (hi : i ∈ q) :
    (Tt i).toConvexSpaceBody ≤ (U.parentTube (uniformCoarseAssign U i)).toConvexSpaceBody := by
  rw [uniformCoarseAssign, dif_pos hi]
  exact (Classical.choose_spec (U.exists_le_rescale hi)).2

end uniformCoarseAssign

namespace Section6CoarseTubeDecomposition

open Classical in
/-- **The fibres of the chosen assignment are contained in the containment sets.**  This is the
precise reason the fibre upper bound transfers from uniformity while the lower bound does not. -/
theorem fibre_subset_filter_of_uniformAtScale {ι : Type*} {q : Finset ι} {δ : ℝ≥0}
    {Tt : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} {ρ C : ℝ≥0}
    (U : Tube.IsUniformAtScale q Tt ρ C) (k : ι) :
    ({i ∈ q | uniformCoarseAssign U i = k} : Finset ι)
      ⊆ {i ∈ q | (Tt i).toConvexSpaceBody ≤ (U.parentTube k).toConvexSpaceBody} := by
  intro i hi
  rw [Finset.mem_filter] at hi
  rw [Finset.mem_filter]
  constructor
  · exact hi.1
  · rw [← hi.2]
    rw [uniformCoarseAssign, dif_pos hi.1]
    exact (Classical.choose_spec (U.exists_le_rescale hi.1)).2

open Classical in
/-- **The fibre upper bound supplied by uniformity.** -/
theorem card_fibre_le_of_uniformAtScale {ι : Type*} {q : Finset ι} {δ : ℝ≥0}
    {Tt : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} {ρ C : ℝ≥0}
    (U : Tube.IsUniformAtScale q Tt ρ C) {k : ι} (hk : k ∈ U.parent) :
    (({i ∈ q | uniformCoarseAssign U i = k} : Finset ι).card : ℝ≥0) ≤ C * U.branchingN := by
  let F : Finset ι := {i ∈ q | (Tt i).toConvexSpaceBody ≤ (U.parentTube k).toConvexSpaceBody}
  have hle : ((({i ∈ q | uniformCoarseAssign U i = k} : Finset ι).card : ℝ≥0)) ≤
      (F.card : ℝ≥0) := by
    exact_mod_cast Finset.card_le_card (fibre_subset_filter_of_uniformAtScale U k)
  calc
    (({i ∈ q | uniformCoarseAssign U i = k} : Finset ι).card : ℝ≥0) ≤ (F.card : ℝ≥0) := hle
    _ ≤ C * U.branchingN := by exact_mod_cast U.card_filter_le hk

open Classical in
/-- **The coarse decomposition supplied by single-scale uniformity.**

The coarse index set is the set of parents *actually used*, `q.image assign`, so that fibre
nonemptiness is automatic rather than assumed.  Everything else is discharged from the uniformity
data, except the single hypothesis `hlb`: uniformity's own lower bound
(`Tube.IsUniformAtScale.le_mul_card_filter`) is a statement about the *containment* set
`{i ∈ q | T i ≤ U.parentTube k}`, which can be strictly larger than the fibre of a chosen
assignment, so it does not imply `hlb`.  Supplying `hlb` requires a bounded-overlap count for the
parent family; it is *not* invented here. -/
def ofUniformAtScale {ι : Type*} {q : Finset ι} {δ : ℝ≥0}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {ρ C : ℝ≥0}
    (U : Tube.IsUniformAtScale q (fun i => (T i).toTube) ρ C) (hC : 1 ≤ C)
    (hN : 0 < U.branchingN)
    (hlb : ∀ k ∈ q.image (uniformCoarseAssign U),
      U.branchingN / C
        ≤ (({i ∈ q | uniformCoarseAssign U i = k} : Finset ι).card : ℝ≥0)) :
    Section6CoarseTubeDecomposition q T (q.image (uniformCoarseAssign U))
      (fun k => U.parentTube k) U.branchingN C where
  assign := uniformCoarseAssign U
  assign_mem := by
    intro i hi
    exact Finset.mem_image_of_mem (uniformCoarseAssign U) hi
  leaf_le_parent := by
    intro i hi
    simpa using uniformCoarseAssign.le_rescale U hi
  one_le_Cfib := hC
  m_pos := hN
  fibre_nonempty := by
    intro k hk
    rw [Finset.mem_image] at hk
    rcases hk with ⟨i, hi, hik⟩
    exact ⟨i, by simpa [Finset.mem_filter] using ⟨hi, hik⟩⟩
  le_card_fibre := by
    intro k hk
    exact hlb k hk
  card_fibre_le := by
    intro k hk
    apply card_fibre_le_of_uniformAtScale
    rw [Finset.mem_image] at hk
    rcases hk with ⟨i, hi, hik⟩
    rw [← hik]
    exact uniformCoarseAssign.mem_parent U hi

end Section6CoarseTubeDecomposition

/-! ## The Part-(B) factorisation datum -/

open Classical in
/-- **The honest Part-(B) factorisation datum: "`𝒲` factors `𝒯_ρ`".**

A wrapper around the geometry of `Kakeya.GlobalComparableBodyFactorization` carrying, in addition, the two
things Proposition 6.6(B) genuinely uses and that structure lacks:

* the representative `a × b × 1` plank of each cell as **data** (`repr`, `body_le_repr`) rather than
  as the existential `Kakeya.GlobalComparableBodyFactorization.le_plank`;
* the **coarse-fibre Frostman** datum `coarse_fibre_frostman`: the coarse tubes collected by a cell
  are `CF`-Frostman inside that cell's representative plank.

The actual cell body `body x` and the representative plank `repr x` are kept strictly separate: no
actual body is assumed to be a plank, and no exact plank is required to lie in a `ρ`-tube.  There is
deliberately no fine-fibre Frostman clause; see the module docstring. -/
structure Section6PartBFactorisation (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
    {κ : Type*} (coarseSet : Finset κ) {ρ : ℝ≥0}
    (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (CF C₀ : ℝ≥0) where
  /-- Index type of the outer cells. -/
  Cell : Type
  /-- The outer cells actually used. -/
  cells : Finset Cell
  /-- The *actual* outer body of a cell.  Never assumed to be a plank. -/
  body : Cell → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))
  /-- The cell collecting each coarse tube. -/
  cellOf : κ → Cell
  /-- Every coarse index in use is collected by a cell in use. -/
  cellOf_mem : ∀ k ∈ coarseSet, cellOf k ∈ cells
  /-- Every coarse tube lies in the body of its cell. -/
  le_body : ∀ k ∈ coarseSet, (R k).toConvexSpaceBody ≤ body (cellOf k)
  /-- The representative `a × b × 1` plank of a cell. -/
  repr : Cell → Plank a b hab hb1
  /-- The actual body is contained in its representative plank. -/
  body_le_repr : ∀ x ∈ cells, body x ≤ (repr x).toConvexSpaceBody
  /-- **The representative planks lie in the working window.**

  This is *not* derivable from the rest of the datum.  The only spatial anchor available downstream
  is that the fine tubes lie in the unit ball, which puts one point of `repr x` in
  `closedBall 0 1`; an `a × b × 1` plank through that point reaches out to
  `1 + 2√(a² + b² + 1)`, which at `a = b = 1` is `1 + 2√3 ≈ 4.47 > 4 = plankWindowRadius`.  So the
  containment genuinely has to be part of the datum, supplied by whoever builds the
  factorisation from a concrete configuration.  It is what
  `Kakeya.factoringAndMultPropGlobal` exports as the outer window clause. -/
  repr_window : ∀ x ∈ cells,
    ((repr x).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)
  /-- The Frostman constant is at least `1`. -/
  one_le_CF : 1 ≤ CF
  /-- **Coarse-fibre Frostman.**  The coarse tubes collected by a cell are `CF`-Frostman in the
  cell's representative plank. -/
  coarse_fibre_frostman : ∀ x ∈ cells,
    ConvexSpaceBody.IsFrostmanIn ({k ∈ coarseSet | cellOf k = x} : Finset κ)
      (fun k => (R k).toConvexSpaceBody) (repr x).toConvexSpaceBody (CF : ENNReal)
  /-- The outer family is Katz--Tao with constant `C₀`. -/
  isKatzTao : ConvexSpaceBody.IsKatzTao cells body (C₀ : ENNReal)

namespace Section6PartBFactorisation

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
  {CF C₀ : ℝ≥0}

open Classical in
/-- The coarse tubes collected by a cell. -/
def coarseFibre (F : Section6PartBFactorisation a b hab hb1 coarseSet R CF C₀) (x : F.Cell) :
    Finset κ :=
  {k ∈ coarseSet | F.cellOf k = x}

variable (F : Section6PartBFactorisation a b hab hb1 coarseSet R CF C₀)

theorem mem_coarseFibre_iff {x : F.Cell} {k : κ} :
    k ∈ F.coarseFibre x ↔ k ∈ coarseSet ∧ F.cellOf k = x := by
  simp [coarseFibre, Finset.mem_filter]

theorem coarseFibre_subset (x : F.Cell) : F.coarseFibre x ⊆ coarseSet := by
  rw [coarseFibre]
  exact Finset.filter_subset (fun k => F.cellOf k = x) coarseSet

/-- Each coarse tube lies in the representative plank of its cell. -/
theorem le_repr {k : κ} (hk : k ∈ coarseSet) :
    (R k).toConvexSpaceBody ≤ (F.repr (F.cellOf k)).toConvexSpaceBody := by
  exact le_trans (F.le_body k hk) (F.body_le_repr (F.cellOf k) (F.cellOf_mem k hk))

theorem carrier_subset_repr {k : κ} (hk : k ∈ coarseSet) :
    (R k).carrier ⊆ ((F.repr (F.cellOf k)).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  exact (SetLike.coe_subset_coe (S := (R k).toConvexSpaceBody)
    (T := (F.repr (F.cellOf k)).toConvexSpaceBody)).mp (F.le_repr hk)

/-- Every coarse tube of a cell's fibre lies in that cell's representative plank. -/
theorem carrier_subset_repr_of_mem_coarseFibre {x : F.Cell} {k : κ} (hk : k ∈ F.coarseFibre x) :
    (R k).carrier ⊆ ((F.repr x).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  rw [mem_coarseFibre_iff] at hk
  rcases hk with ⟨hk_coarse, hkcell⟩
  rw [← hkcell]
  exact
    (SetLike.coe_subset_coe (S := (R k).toConvexSpaceBody)
      (T := (F.repr (F.cellOf k)).toConvexSpaceBody)).mp (le_repr F hk_coarse)

/-- The `ENNReal` cancellation behind
`Kakeya.Section6PartBFactorisation.volume_repr_le_of_coarseFibre_nonempty`: two densities with a
common, positive and finite numerator `S` compare exactly as their denominators do, in reverse. -/
private theorem le_mul_of_div_le_mul_div {S vB vP C : ENNReal}
    (hS0 : S ≠ 0) (hStop : S ≠ ⊤) (hvB0 : vB ≠ 0) (hvBtop : vB ≠ ⊤) (hvPtop : vP ≠ ⊤)
    (h : S / vB ≤ C * (S / vP)) : vP ≤ C * vB := by
  rcases eq_or_ne vP 0 with hvP0 | hvP0
  · simp [hvP0]
  rcases eq_or_ne C ⊤ with hCtop | hCtop
  · rw [hCtop, mul_comm, ENNReal.mul_top hvB0]
    exact le_top
  have h1 : S ≤ C * (S / vP) * vB := (ENNReal.div_le_iff hvB0 hvBtop).mp h
  have h1' : S ≤ (C * vB * S) / vP := by
    calc
      S ≤ C * (S / vP) * vB := h1
      _ = (C * vB * S) / vP := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
  have h2 : S * vP ≤ C * vB * S :=
    (ENNReal.le_div_iff_mul_le (Or.inl hvP0) (Or.inl hvPtop)).mp h1'
  have h2' : S * vP ≤ S * (C * vB) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using h2
  exact (ENNReal.mul_le_mul_iff_right hS0 hStop).mp h2'

/-- **The reverse volume comparison is already in the datum: it is the Frostman clause.**

`Kakeya.Section6PartBFactorisation` carries no field of the form
`volume (repr x) ≤ C · volume (body x)`, and at first sight the Katz--Tao property of the cell
bodies therefore says nothing about the representative planks: enlarging each body to its
representative can inflate the density arbitrarily.

It does not, because the datum already pins the two volumes together.  Apply the coarse-fibre
Frostman clause `coarse_fibre_frostman` — which is Frostman *in the representative plank* — at the
test body `K' := body x`, legitimate by `body_le_repr`.  Every tube of the fibre lies in `body x`
(`le_body`), so the containment filter is vacuous on both sides and the two densities share the
same numerator `S = ∑_{k ∈ fibre x} |R k|`:

`S / |body x| = Δ(𝒯_x, body x) ≤ CF · Δ(𝒯_x, repr x) = CF · S / |repr x|`.

With `0 < S < ∞` — positivity is `0 < ρ` through `Tube.le_volume`, together with a nonempty
fibre — the common factor cancels and leaves exactly

`|repr x| ≤ CF · |body x|`.

So the comparison constant is the Frostman constant, not a new assumption.  This is the sharp
statement: a cell whose representative is much larger than its actual body has a fibre that
concentrates inside the body, which is precisely what a Frostman hypothesis in the representative
forbids. -/
theorem volume_repr_le_of_coarseFibre_nonempty
    (F' : Section6PartBFactorisation a b hab hb1 coarseSet R CF C₀) (hρ0 : 0 < ρ)
    {x : F'.Cell} (hx : x ∈ F'.cells) (hne : (F'.coarseFibre x).Nonempty) :
    volume ((F'.repr x).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ (CF : ENNReal) * volume (F'.body x).carrier := by
  classical
  let s : Finset κ := F'.coarseFibre x
  let V : κ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) := fun k => (R k).toConvexSpaceBody
  let B : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) := F'.body x
  let P : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) := (F'.repr x).toConvexSpaceBody
  let S : ENNReal := ∑ k ∈ s, volume (R k).carrier
  let vB : ENNReal := volume B.carrier
  let vP : ENNReal := volume P.carrier
  -- (1) every fibre member lies in the cell's actual body.
  have hVB : ∀ k ∈ s, V k ≤ B := by
    intro k hk
    rw [mem_coarseFibre_iff] at hk
    rcases hk with ⟨hkcoarse, hkeq⟩
    dsimp [V, B]
    rw [← hkeq]
    exact F'.le_body k hkcoarse
  -- (2) every fibre member lies in the representative plank.
  have hVP : ∀ k ∈ s, V k ≤ P := by
    intro k hk
    exact le_trans (hVB k hk) (by simpa [B, P] using F'.body_le_repr x hx)
  -- (3) both densities share the numerator S = ∑_{k ∈ s} |R k|, by the containment filters.
  have hdB : densityIn s V B = S / vB := by
    simpa [V, B, S, vB] using densityIn_of_all_le hVB
  have hdP : densityIn s V P = S / vP := by
    simpa [V, P, S, vP] using densityIn_of_all_le hVP
  -- the coarse-fibre Frostman clause at the test body B.
  have hBP : B ≤ P := by simpa [B, P] using F'.body_le_repr x hx
  have hfrost : ConvexSpaceBody.IsFrostmanIn s V P (CF : ENNReal) := by
    dsimp [s, V, P]
    exact F'.coarse_fibre_frostman x hx
  have hmain : S / vB ≤ (CF : ENNReal) * (S / vP) := by
    calc
      S / vB = densityIn s V B := hdB.symm
      _ ≤ (CF : ENNReal) * densityIn s V P := hfrost B hBP
      _ = (CF : ENNReal) * (S / vP) := by rw [hdP]
  -- (4) S ≠ 0: a nonempty fibre and the tube volume lower bound.
  obtain ⟨k₀, k₀mem⟩ := hne
  have hvolR : 0 < volume (R k₀).carrier := by
    have hle : ((Tube.le_volume.c 3 : ℝ≥0) : ENNReal) * (ρ : ENNReal) ^ 2
        ≤ volume (R k₀).carrier := by
      simpa [finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)] using
        (Tube.le_volume (E := EuclideanSpace ℝ (Fin 3)) (R k₀))
    have hnb : ((Tube.le_volume.c 3 : ℝ≥0) : ENNReal) * (ρ : ENNReal) ^ 2 ≠ 0 := by
      exact mul_ne_zero (ENNReal.coe_ne_zero.mpr (ne_of_gt (Tube.le_volume.c_pos 3)))
        (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr (ne_of_gt hρ0)))
    exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hnb) hle
  have hS0 : S ≠ 0 := by
    have hle : volume (R k₀).carrier ≤ S := by
      simpa [S] using
        (Finset.single_le_sum_of_canonicallyOrdered
          (f := fun k => volume (R k).carrier) k₀mem)
    exact ne_of_gt (lt_of_lt_of_le hvolR hle)
  -- (5) S ≠ ⊤: each tube's carrier is compact.
  have hStop : S ≠ ⊤ := by
    change (∑ k ∈ s, volume (R k).carrier) ≠ (⊤ : ENNReal)
    exact ENNReal.sum_ne_top.2 (fun k hk => (R k).isCompact.measure_lt_top.ne)
  -- (6) vB ≠ 0: containment from (1) plus the tube lower bound.
  have hBRk : (R k₀).toConvexSpaceBody ≤ B := by simpa [V] using hVB k₀ k₀mem
  have hvB0 : vB ≠ 0 := by
    have hle : volume (R k₀).carrier ≤ vB := by
      exact measure_mono ((SetLike.coe_subset_coe
        (S := (R k₀).toConvexSpaceBody) (T := B)).mp hBRk)
    exact ne_of_gt (lt_of_lt_of_le hvolR hle)
  -- (7) the compact carriers are finite.
  have hvBtop : vB ≠ ⊤ := B.isCompact.measure_lt_top.ne
  have hvPtop : vP ≠ ⊤ := P.isCompact.measure_lt_top.ne
  -- the pure arithmetic endgame.
  exact le_mul_of_div_le_mul_div (C := (CF : ENNReal)) hS0 hStop hvB0 hvBtop hvPtop hmain

/-- **Katz--Tao transfers from the cell bodies to the representative planks, at the cost `CF`.**

This is the input the Section-6(B) consumer needs and the factorisation datum did not visibly
supply.  It is a two-line consequence of `Kakeya.maxDensity_le_of_subset_of_volume_le` — the
generic "enlarge each body by a bounded volume factor" transfer — fed with `body_le_repr` for the
containment and `Kakeya.Section6PartBFactorisation.volume_repr_le_of_coarseFibre_nonempty` for the
volume factor.

The constant is `CF * C₀`, both factors already present in the datum and both required by
Proposition 6.6(B) to be at most `δ ^ (-η)`; a consumer needing `Δ_max(𝒲) ≤ δ ^ (-ηₒ)` therefore
only has to choose its fine exponent with `2η ≤ ηₒ`.  It is deliberately not `C₀`: the enlargement
from body to representative is a genuine loss, bounded by the Frostman constant and no better. -/
theorem isKatzTao_repr
    (F' : Section6PartBFactorisation a b hab hb1 coarseSet R CF C₀) (hρ0 : 0 < ρ)
    (hne : ∀ x ∈ F'.cells, (F'.coarseFibre x).Nonempty) :
    ConvexSpaceBody.IsKatzTao F'.cells (fun x => (F'.repr x).toConvexSpaceBody)
      ((CF * C₀ : ℝ≥0) : ENNReal) := by
  rw [ConvexSpaceBody.IsKatzTao_def]
  calc
    Kakeya.maxDensity F'.cells (fun x => (F'.repr x).toConvexSpaceBody)
        ≤ (CF : ENNReal) * Kakeya.maxDensity F'.cells F'.body := by
      exact Kakeya.maxDensity_le_of_subset_of_volume_le F'.cells F'.body
        (fun x => (F'.repr x).toConvexSpaceBody)
        (by
          intro x hx
          exact (SetLike.coe_subset_coe (S := F'.body x)
            (T := (F'.repr x).toConvexSpaceBody)).mp (F'.body_le_repr x hx))
        (fun x hx => F'.volume_repr_le_of_coarseFibre_nonempty hρ0 hx (hne x hx))
    _ ≤ (CF : ENNReal) * (C₀ : ENNReal) := by
      gcongr
      exact F'.isKatzTao
    _ = ((CF * C₀ : ℝ≥0) : ENNReal) := by
      simp

/-- **Katz--Tao on the representative planks, over a subfamily of cells.**

Section 6(B) applies the transfer to the cells *selected by Proposition 5.1*, not to every cell of
the datum, and only a selected cell is known to carry a coarse tube — nothing in
`Kakeya.Section6PartBFactorisation` forces `cellOf` to be surjective onto `cells`.  This is
`Kakeya.Section6PartBFactorisation.isKatzTao_repr` restricted to a subfamily: the volume comparison
is needed only on `s`, and the ambient Katz--Tao bound descends to `s` by `Kakeya.maxDensity_mono`.

The constant is unchanged at `CF * C₀`; restricting the index set never increases the density. -/
theorem isKatzTao_repr_of_subset
    (F' : Section6PartBFactorisation a b hab hb1 coarseSet R CF C₀) (hρ0 : 0 < ρ)
    {s : Finset F'.Cell} (hs : s ⊆ F'.cells)
    (hne : ∀ x ∈ s, (F'.coarseFibre x).Nonempty) :
    ConvexSpaceBody.IsKatzTao s (fun x => (F'.repr x).toConvexSpaceBody)
      ((CF * C₀ : ℝ≥0) : ENNReal) := by
  rw [ConvexSpaceBody.IsKatzTao_def]
  calc
    Kakeya.maxDensity s (fun x => (F'.repr x).toConvexSpaceBody)
        ≤ (CF : ENNReal) * Kakeya.maxDensity s F'.body := by
      exact Kakeya.maxDensity_le_of_subset_of_volume_le s F'.body
        (fun x => (F'.repr x).toConvexSpaceBody)
        (by
          intro x hx
          exact (SetLike.coe_subset_coe (S := F'.body x)
            (T := (F'.repr x).toConvexSpaceBody)).mp (F'.body_le_repr x (hs hx)))
        (fun x hx => F'.volume_repr_le_of_coarseFibre_nonempty hρ0 (hs hx) (hne x hx))
    _ ≤ (CF : ENNReal) * Kakeya.maxDensity F'.cells F'.body := by
      gcongr
      exact Kakeya.maxDensity_mono F'.body hs
    _ ≤ (CF : ENNReal) * (C₀ : ENNReal) := by
      gcongr
      exact F'.isKatzTao
    _ = ((CF * C₀ : ℝ≥0) : ENNReal) := by
      simp

/-- **The Part-(B) scale relation, from the honest representative geometry.**

A `ρ`-tube contains a ball of radius `ρ`; it lies in its cell body, which lies in the cell's
representative `a × b × 1` plank, whose least width is `a`.  Hence `ρ ≤ a`
(`Kakeya.Tube.rho_le_of_le_prism3D`).  No equality between an actual body and a plank is used. -/
theorem rho_le_of_mem (F' : Section6PartBFactorisation a b hab hb1 coarseSet R CF C₀)
    {k : κ} (hk : k ∈ coarseSet) : ρ ≤ a := by
  exact Tube.rho_le_of_le_prism3D (R k) (F'.repr (F'.cellOf k)) (F'.le_repr hk)

/-- **The Part-(B) scale relation.** -/
theorem rho_le (F' : Section6PartBFactorisation a b hab hb1 coarseSet R CF C₀)
    (hne : coarseSet.Nonempty) : ρ ≤ a := by
  obtain ⟨k, hk⟩ := hne
  exact rho_le_of_mem F' hk

open Classical in
/-- **Wrapping a `Kakeya.GlobalComparableBodyFactorization`.**  The outer geometry is taken over verbatim;
the representative planks and the coarse-fibre Frostman datum are the new inputs. -/
def ofGlobalPlankFactorization
    (Fz : GlobalComparableBodyFactorization a b hab hb1 coarseSet (fun k => (R k).toConvexSpaceBody) C₀)
    (repr : Fz.Cell → Plank a b hab hb1)
    (hrepr : ∀ x ∈ Fz.cells, Fz.body x ≤ (repr x).toConvexSpaceBody)
    (hwin : ∀ x ∈ Fz.cells, ((repr x).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ))
    (hCF : 1 ≤ CF)
    (hfrost : ∀ x ∈ Fz.cells,
      ConvexSpaceBody.IsFrostmanIn ({k ∈ coarseSet | Fz.cellOf k = x} : Finset κ)
        (fun k => (R k).toConvexSpaceBody) (repr x).toConvexSpaceBody (CF : ENNReal)) :
    Section6PartBFactorisation a b hab hb1 coarseSet R CF C₀ where
  Cell := Fz.Cell
  cells := Fz.cells
  body := Fz.body
  cellOf := Fz.cellOf
  cellOf_mem := Fz.cellOf_mem
  le_body := Fz.le_body
  repr := repr
  body_le_repr := hrepr
  repr_window := hwin
  one_le_CF := hCF
  coarse_fibre_frostman := hfrost
  isKatzTao := Fz.isKatzTao

end Section6PartBFactorisation

/-! ## Coarse counting: the volume-comparable Frostman count -/

/-- **A Frostman family of volume-comparable bodies cannot concentrate.**

If the bodies `V k`, `k ∈ r`, all have volume in `[v, Cv · v]`, are `CF`-Frostman in `W`, and
`K ⊆ W` has volume at most `θ · |W|`, then at most a `Cv · CF · θ`-fraction of them lie in `K`.

This is `Kakeya.card_le_of_frostmanIn` with the volume ratio made explicit and the common volume
cancelled, which is the form the fine-family transport below needs. -/
theorem card_le_of_frostmanIn_of_volume_comparable {κ : Type*} {r : Finset κ}
    {V : κ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {W K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {CF θ Cv : ℝ≥0} {v : ENNReal}
    (hv0 : v ≠ 0) (hvtop : v ≠ ⊤)
    (hFrost : ConvexSpaceBody.IsFrostmanIn r V W (CF : ENNReal))
    (hVW : ∀ k ∈ r, V k ≤ W) (hKW : K ≤ W)
    (hmin : ∀ k ∈ r, v ≤ volume (V k).carrier)
    (hmax : ∀ k ∈ r, volume (V k).carrier ≤ (Cv : ENNReal) * v)
    (hW0 : volume W.carrier ≠ 0) (hWtop : volume W.carrier ≠ ⊤)
    (hvolK : volume K.carrier ≤ (θ : ENNReal) * volume W.carrier) :
    (({k ∈ r | V k ≤ K}).card : ENNReal)
      ≤ ((Cv * CF * θ : ℝ≥0) : ENNReal) * (r.card : ENNReal) := by
  have hvolb : volume K.carrier / volume W.carrier ≤ (θ : ENNReal) := by
    rw [ENNReal.div_le_iff_le_mul (.inl hW0) (.inl hWtop)]
    exact hvolK
  have hmain : (({k ∈ r | V k ≤ K}).card : ENNReal) * v
      ≤ (CF : ENNReal) * ((r.card : ENNReal) * ((Cv : ENNReal) * v))
        * (volume K.carrier / volume W.carrier) := by
    exact card_le_of_frostmanIn hFrost hVW hKW hv0 hmin hmax hW0 hWtop
  have hstep : (CF : ENNReal) * ((r.card : ENNReal) * ((Cv : ENNReal) * v))
        * (volume K.carrier / volume W.carrier)
      ≤ ((Cv * CF * θ : ℝ≥0) : ENNReal) * (r.card : ENNReal) * v := by
    calc
      (CF : ENNReal) * ((r.card : ENNReal) * ((Cv : ENNReal) * v))
          * (volume K.carrier / volume W.carrier)
          ≤ (CF : ENNReal) * ((r.card : ENNReal) * ((Cv : ENNReal) * v)) * (θ : ENNReal) := by
            gcongr
      _ = ((Cv * CF * θ : ℝ≥0) : ENNReal) * (r.card : ENNReal) * v := by
            simp [ENNReal.coe_mul, mul_assoc, mul_left_comm, mul_comm]
  have hleft : v * (({k ∈ r | V k ≤ K}).card : ENNReal)
      ≤ v * (((Cv * CF * θ : ℝ≥0) : ENNReal) * (r.card : ENNReal)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (le_trans hmain hstep)
  exact (ENNReal.mul_le_mul_iff_right hv0 hvtop).mp hleft

/-- The ratio of the two dimensional constants bounding the volume of a `ρ`-tube in `ℝ³`. -/
def coarseTubeVolumeRatio : ℝ≥0 :=
  Tube.volume_le.C 3 / Tube.le_volume.c 3

theorem one_le_coarseTubeVolumeRatio : 1 ≤ coarseTubeVolumeRatio := by
  rw [coarseTubeVolumeRatio, Tube.volume_le.C]
  norm_num
  have h32 : Real.Gamma ((3 : ℝ) / 2) = (1 / 2 : ℝ) * Real.sqrt Real.pi := by
    rw [show (3 : ℝ) / 2 = 1 / 2 + (1 : ℝ) by norm_num]
    rw [Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    rw [Real.Gamma_one_half_eq]
  have hg : Real.Gamma ((3 : ℝ) / 2 + 1) = (3 / 4 : ℝ) * Real.sqrt Real.pi := by
    rw [Real.Gamma_add_one (by norm_num : (3 : ℝ) / 2 ≠ 0), h32]
    ring
  have hc : (Tube.le_volume.c 3 : ℝ) ≤ 16 := by
    change Real.sqrt Real.pi ^ 3 / Real.Gamma (3 / 2 + 1) / 3 ≤ 16
    rw [hg]
    have hpos : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hsqrt : Real.sqrt Real.pi ≠ 0 := ne_of_gt hpos
    field_simp [hsqrt]
    rw [Real.sq_sqrt Real.pi_nonneg]
    nlinarith [Real.pi_le_four, Real.pi_pos]
  rw [← NNReal.coe_le_coe]
  rw [NNReal.coe_div]
  norm_num
  rw [le_div_iff₀ (NNReal.coe_pos.mpr (Tube.le_volume.c_pos 3))]
  simpa using hc

/-- The volume of a `ρ`-tube in `ℝ³`, two-sided, in the form
`v ≤ volume ≤ coarseTubeVolumeRatio · v` with `v = c · ρ²`. -/
theorem Tube.volume_comparable_three {ρ : ℝ≥0} (hρ1 : ρ ≤ 1)
    (R : Tube ρ (EuclideanSpace ℝ (Fin 3))) :
    ((Tube.le_volume.c 3 : ℝ≥0) : ENNReal) * (ρ : ENNReal) ^ 2 ≤ volume R.carrier ∧
      volume R.carrier ≤ (coarseTubeVolumeRatio : ENNReal)
        * (((Tube.le_volume.c 3 : ℝ≥0) : ENNReal) * (ρ : ENNReal) ^ 2) := by
  constructor
  · simpa [finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)] using
      (Tube.le_volume (E := EuclideanSpace ℝ (Fin 3)) R)
  · have hc : Tube.le_volume.c (3 : ℕ) ≠ (0 : ℝ≥0) := ne_of_gt (Tube.le_volume.c_pos 3)
    have hle : volume R.carrier ≤
        ((Tube.volume_le.C 3 * ρ ^ 2 : ℝ≥0) : ENNReal) := by
      simpa [finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)] using
        (Tube.volume_le (E := EuclideanSpace ℝ (Fin 3)) hρ1 R)
    have hul : coarseTubeVolumeRatio * (Tube.le_volume.c 3 * ρ ^ 2) =
        Tube.volume_le.C 3 * ρ ^ 2 := by
      rw [coarseTubeVolumeRatio, ← mul_assoc]
      rw [div_mul_cancel₀ (Tube.volume_le.C 3) hc]
    have hcoef : (coarseTubeVolumeRatio : ENNReal) *
        (((Tube.le_volume.c 3 : ℝ≥0) : ENNReal) * (ρ : ENNReal) ^ 2) =
        ((Tube.volume_le.C 3 * ρ ^ 2 : ℝ≥0) : ENNReal) := by
      rw [← ENNReal.coe_pow, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
      exact congrArg (fun x : ℝ≥0 => (x : ENNReal)) hul
    calc
      volume R.carrier ≤ ((Tube.volume_le.C 3 * ρ ^ 2 : ℝ≥0) : ENNReal) := hle
      _ = (coarseTubeVolumeRatio : ENNReal) *
          (((Tube.le_volume.c 3 : ℝ≥0) : ENNReal) * (ρ : ENNReal) ^ 2) := hcoef.symm

/-- **The coarse Frostman count for `ρ`-tubes** (the first step of GWZ's `γ = 1` non-concentration
bound): a `CF`-Frostman family of `ρ`-tubes in `W` puts at most a
`coarseTubeVolumeRatio · CF · θ`-fraction of its members inside a subset of relative volume `θ`. -/
theorem card_coarse_le_of_frostmanIn {κ : Type*} {r : Finset κ} {ρ : ℝ≥0}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
    {W K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {CF θ : ℝ≥0}
    (hFrost : ConvexSpaceBody.IsFrostmanIn r (fun k => (R k).toConvexSpaceBody) W (CF : ENNReal))
    (hRW : ∀ k ∈ r, (R k).toConvexSpaceBody ≤ W) (hKW : K ≤ W)
    (hW0 : volume W.carrier ≠ 0) (hWtop : volume W.carrier ≠ ⊤)
    (hvolK : volume K.carrier ≤ (θ : ENNReal) * volume W.carrier) :
    ((({k ∈ r | (R k).toConvexSpaceBody ≤ K}).card : ℝ≥0))
      ≤ coarseTubeVolumeRatio * CF * θ * (r.card : ℝ≥0) := by
  let v : ENNReal := ((Tube.le_volume.c 3 : ℝ≥0) : ENNReal) * (ρ : ENNReal) ^ 2
  have hv0 : v ≠ 0 := by
    dsimp [v]
    refine mul_ne_zero ?_ ?_
    · exact ENNReal.coe_ne_zero.mpr (ne_of_gt (Tube.le_volume.c_pos 3))
    · exact pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr (ne_of_gt hρ0))
  have hvtop : v ≠ ⊤ := by
    dsimp [v]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hmin : ∀ k ∈ r, v ≤ volume ((R k).toConvexSpaceBody).carrier := by
    intro k hk
    simpa using (Tube.volume_comparable_three hρ1 (R k)).1
  have hmax : ∀ k ∈ r,
      volume ((R k).toConvexSpaceBody).carrier ≤ (coarseTubeVolumeRatio : ENNReal) * v := by
    intro k hk
    simpa using (Tube.volume_comparable_three hρ1 (R k)).2
  have hmain : (({k ∈ r | (R k).toConvexSpaceBody ≤ K}).card : ENNReal)
      ≤ ((coarseTubeVolumeRatio * CF * θ : ℝ≥0) : ENNReal) * (r.card : ENNReal) := by
    refine card_le_of_frostmanIn_of_volume_comparable (V := fun k => (R k).toConvexSpaceBody)
      (W := W) (K := K) (CF := CF) (θ := θ) (Cv := coarseTubeVolumeRatio) (v := v)
      hv0 hvtop hFrost hRW hKW hmin hmax hW0 hWtop hvolK
  exact ENNReal.coe_le_coe.mp hmain

/-! ## The combined Part-(B) input datum -/

/-- **The complete Part-(B) input.**  A coarse tube decomposition of the fine family together with a
factorisation of the coarse family.  This is the exact replacement for the weak hypothesis
`∀ i ∈ q, ∃ k ∈ r, T i ≤ R k` of `Kakeya.factoringAndMultPropGlobal`. -/
structure Section6PartBData (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
    {ι : Type*} (q : Finset ι) {δ : ℝ≥0} (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    {κ : Type*} (coarseSet : Finset κ) {ρ : ℝ≥0}
    (R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))) (m Cfib CF C₀ : ℝ≥0) where
  /-- The fine-to-coarse decomposition. -/
  decomp : Section6CoarseTubeDecomposition q T coarseSet R m Cfib
  /-- The factorisation of the coarse family by outer cells. -/
  factor : Section6PartBFactorisation a b hab hb1 coarseSet R CF C₀

namespace Section6PartBData

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
  {m Cfib CF C₀ : ℝ≥0}

/-- The cell of a fine index: the cell of its coarse parent. -/
def cellOfFine (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀) (i : ι) :
    D.factor.Cell :=
  D.factor.cellOf (D.decomp.assign i)

open Classical in
/-- The fine tubes lying over a cell. -/
def fineFibre (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)
    (x : D.factor.Cell) : Finset ι :=
  {i ∈ q | D.cellOfFine i = x}

variable (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)

theorem mem_fineFibre_iff {x : D.factor.Cell} {i : ι} :
    i ∈ D.fineFibre x ↔ i ∈ q ∧ D.cellOfFine i = x := by
  simp [fineFibre, Finset.mem_filter]

theorem fineFibre_subset (x : D.factor.Cell) : D.fineFibre x ⊆ q := by
  rw [fineFibre]
  exact Finset.filter_subset (fun i => D.cellOfFine i = x) q

/-- The coarse parent of a fine tube of a cell belongs to that cell's coarse fibre. -/
theorem assign_mem_coarseFibre {x : D.factor.Cell} {i : ι} (hi : i ∈ D.fineFibre x) :
    D.decomp.assign i ∈ D.factor.coarseFibre x := by
  rw [Section6PartBFactorisation.mem_coarseFibre_iff]
  rw [mem_fineFibre_iff] at hi
  rcases hi with ⟨hiq, hxi⟩
  constructor
  · exact D.decomp.assign_mem i hiq
  · exact hxi

/-- Every fine tube of a cell lies in that cell's representative plank. -/
theorem carrier_subset_repr {x : D.factor.Cell} {i : ι} (hi : i ∈ D.fineFibre x) :
    (T i).carrier ⊆ ((D.factor.repr x).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  have hq : i ∈ q := (D.mem_fineFibre_iff.mp hi).1
  have hcf : D.cellOfFine i = x := (D.mem_fineFibre_iff.mp hi).2
  have hcell : D.factor.cellOf (D.decomp.assign i) = x := by
    simpa [cellOfFine] using hcf
  have hle : (T i).toConvexSpaceBody ≤ (D.factor.repr x).toConvexSpaceBody := by
    rw [← hcell]
    exact le_trans (D.decomp.leaf_le_parent i hq) (D.factor.le_repr (D.decomp.assign_mem i hq))
  exact (SetLike.coe_subset_coe (S := (T i).toConvexSpaceBody)
    (T := (D.factor.repr x).toConvexSpaceBody)).mp hle

/-! ### Cardinality transport between the global and the cellwise fibres -/

open Classical in
/-- **The key cardinality transport.**  For a coarse index belonging to the cell `x`, the fine
indices assigned to it *within the cell* are exactly all the fine indices assigned to it.  Hence
every cardinality bound for the global fibres holds verbatim for the cellwise ones, with no loss.

This is what lets the two-sided fibre comparability of the decomposition be handed, unchanged, to
the cellwise consumer `Kakeya.katzTaoTransverseFactorBound`. -/
theorem filter_fineFibre_eq {x : D.factor.Cell} {k : κ} (hk : k ∈ D.factor.coarseFibre x) :
    ({i ∈ D.fineFibre x | D.decomp.assign i = k} : Finset ι) = D.decomp.fibre k := by
  ext i
  constructor
  · intro hi
    rw [Finset.mem_filter] at hi
    rw [D.decomp.mem_fibre_iff]
    exact ⟨D.fineFibre_subset x hi.1, hi.2⟩
  · intro hi
    rw [D.decomp.mem_fibre_iff] at hi
    rw [Finset.mem_filter]
    constructor
    · rw [D.mem_fineFibre_iff]
      refine ⟨hi.1, ?_⟩
      have hcell : D.factor.cellOf k = x := (D.factor.mem_coarseFibre_iff.mp hk).2
      calc
        D.cellOfFine i = D.factor.cellOf (D.decomp.assign i) := rfl
        _ = D.factor.cellOf k := by rw [hi.2]
        _ = x := hcell
    · exact hi.2

open Classical in
/-- The cellwise decomposition: the restriction of the global decomposition to a cell.  Its fibre
bounds are the global ones, by `Kakeya.Section6PartBData.filter_fineFibre_eq`. -/
def cellDecomposition (x : D.factor.Cell) :
    Section6CoarseTubeDecomposition (D.fineFibre x) T (D.factor.coarseFibre x) R m Cfib where
  assign := D.decomp.assign
  assign_mem := by
    intro i hi
    exact D.assign_mem_coarseFibre hi
  leaf_le_parent := by
    intro i hi
    exact D.decomp.leaf_le_parent i (D.fineFibre_subset x hi)
  one_le_Cfib := D.decomp.one_le_Cfib
  m_pos := D.decomp.m_pos
  fibre_nonempty := by
    intro k hk
    have hkc : k ∈ coarseSet := D.factor.coarseFibre_subset x hk
    rw [D.filter_fineFibre_eq hk]
    exact D.decomp.fibre_nonempty k hkc
  le_card_fibre := by
    intro k hk
    have hkc : k ∈ coarseSet := D.factor.coarseFibre_subset x hk
    rw [D.filter_fineFibre_eq hk]
    exact D.decomp.le_card_fibre k hkc
  card_fibre_le := by
    intro k hk
    have hkc : k ∈ coarseSet := D.factor.coarseFibre_subset x hk
    rw [D.filter_fineFibre_eq hk]
    exact D.decomp.card_fibre_le k hkc

/-! ### GWZ Remark 5.3 for Part (B) -/

/-- **The Part-(B) Frostman hypothesis, in the shape a Proposition-5.1 black box consumes.**

Only the *coarse* fibres are claimed to be Frostman.  The fine fibres are not, and must not be:
that is the content of GWZ Remark 5.3, and it is why Proposition 6.6(B) may be applied at all. -/
def Remark53FibreFrostman (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀) : Prop :=
  ∀ x ∈ D.factor.cells,
    ConvexSpaceBody.IsFrostmanIn (D.factor.coarseFibre x) (fun k => (R k).toConvexSpaceBody)
      (D.factor.repr x).toConvexSpaceBody (CF : ENNReal)

/-- The Part-(B) datum supplies its own Remark-5.3 Frostman hypothesis. -/
theorem remark53FibreFrostman : D.Remark53FibreFrostman := by
  intro x hx
  exact D.factor.coarse_fibre_frostman x hx

open Classical in
/-- **GWZ Remark 5.3 for Part (B): fine non-concentration with no fine Frostman datum.**

Let `x` be a cell, `W = repr x` its representative plank, and `K ⊆ W` a convex body of relative
volume at most `θ`.  Then the fine tubes of the cell whose *coarse parents* lie in `K` number at
most `Cfib² · coarseTubeVolumeRatio · CF · θ · |𝒯_W|`.

The only Frostman input is the coarse-fibre datum; the fine family is controlled purely by fibre
comparability.  This is the `γ = 1` slab non-concentration hypothesis that Proposition 6.6(B) feeds
to GWZ Lemma 6.1. -/
theorem remark53_card_fine_le
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {x : D.factor.Cell} (hx : x ∈ D.factor.cells)
    (hne : (D.factor.coarseFibre x).Nonempty)
    {K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))} {θ : ℝ≥0}
    (hKW : K ≤ (D.factor.repr x).toConvexSpaceBody)
    (hW0 : volume ((D.factor.repr x).carrier : Set (EuclideanSpace ℝ (Fin 3))) ≠ 0)
    (hvolK : volume K.carrier
      ≤ (θ : ENNReal) * volume ((D.factor.repr x).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    {qS : Finset ι} (hqS : qS ⊆ D.fineFibre x)
    (hmem : ∀ i ∈ qS, (R (D.decomp.assign i)).toConvexSpaceBody ≤ K) :
    (qS.card : ℝ≥0)
      ≤ Cfib ^ 2 * (coarseTubeVolumeRatio * CF * θ) * ((D.fineFibre x).card : ℝ≥0) := by
  let sel : Finset κ := {k ∈ D.factor.coarseFibre x | (R k).toConvexSpaceBody ≤ K}
  have hsel : sel ⊆ D.factor.coarseFibre x := by
    rw [show sel = (D.factor.coarseFibre x).filter (fun k => (R k).toConvexSpaceBody ≤ K) by rfl]
    exact Finset.filter_subset _ _
  have hRW : ∀ k ∈ D.factor.coarseFibre x,
      (R k).toConvexSpaceBody ≤ (D.factor.repr x).toConvexSpaceBody := by
    intro k hk
    rw [D.factor.mem_coarseFibre_iff] at hk
    rcases hk with ⟨hkcoarse, hkcell⟩
    rw [← hkcell]
    exact Section6PartBFactorisation.le_repr (F := D.factor) hkcoarse
  have hselcard : (sel.card : ℝ≥0) ≤
      (coarseTubeVolumeRatio * CF * θ) * ((D.factor.coarseFibre x).card : ℝ≥0) := by
    rw [show sel = (D.factor.coarseFibre x).filter (fun k => (R k).toConvexSpaceBody ≤ K) by rfl]
    have hWtop : volume ((D.factor.repr x).toConvexSpaceBody).carrier ≠ ⊤ :=
      (D.factor.repr x).isCompact.measure_lt_top.ne
    exact card_coarse_le_of_frostmanIn hρ0 hρ1 (r := D.factor.coarseFibre x)
      (W := (D.factor.repr x).toConvexSpaceBody) (K := K) (CF := CF) (θ := θ)
      (hFrost := D.remark53FibreFrostman x hx) (hRW := hRW) (hKW := hKW)
      (hW0 := hW0) (hWtop := hWtop) (hvolK := hvolK)
  have hmem_sel : ∀ i ∈ qS, D.decomp.assign i ∈ sel := by
    intro i hi
    rw [show sel = (D.factor.coarseFibre x).filter (fun k => (R k).toConvexSpaceBody ≤ K) by rfl]
    rw [Finset.mem_filter]
    exact ⟨D.assign_mem_coarseFibre (hqS hi), hmem i hi⟩
  exact (D.cellDecomposition x).card_le_of_selected hne
    (Cθ := coarseTubeVolumeRatio * CF * θ) (sel := sel) (hsel := hsel)
    (hselcard := hselcard) (qS := qS) (hqS := hqS) (hmem := hmem_sel)

/-! ### The output handed to the affine-normalisation layer -/

open Classical in
/-- **The Part-(B) input of the affine-normalisation layer.**

Cell by cell, this is *literally* the hypothesis list of `Kakeya.katzTaoTransverseFactorBound`, with
`qW := D.fineFibre x`, `rW := D.factor.coarseFibre x`, `W := D.factor.repr x`, `assign` the
decomposition's assignment and `C₀ := CF`:

1. the fine tubes of the cell lie in `W`;
2. their coarse parents lie in `rW` and contain them;
3. the coarse family is `CF`-Frostman in `W` — the coarse-fibre datum of GWZ Remark 5.3, *not* a
   fine Frostman claim;
4. every coarse fibre of the cell is nonempty and has cardinality comparable to `m`;
5. the coarse tubes of the cell lie in `W`.

The fibre estimate is claimed for *all* coarse fibres of the cell, empty ones included: a guarded
"nonempty fibres" form would be unusable, since padding `rW` with empty-fibre coarse tubes would
lower the admissible Frostman constant without changing `|qW|` or the selected set, so the target
bound `|(qW)_S| ≤ Ccount · Cvol · C₀ · Cfib² · θ · |qW|` would fail by an arbitrarily large
factor.  Nothing extra is needed for the unguarded form: the decomposition's fibre bounds
`le_card_fibre`/`card_fibre_le` are already unguarded over its whole `coarseSet`, and
`Kakeya.Section6PartBData.cellDecomposition` carries them to the cell verbatim.

Nothing here normalises anything: the affine map, the model planks and the slab counting all remain
the business of the normalisation layer. -/
theorem transverseFactorInput {x : D.factor.Cell} (hx : x ∈ D.factor.cells) :
    (∀ i ∈ D.fineFibre x,
        (T i).carrier ⊆ ((D.factor.repr x).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∧
      (∀ i ∈ D.fineFibre x, D.decomp.assign i ∈ D.factor.coarseFibre x ∧
        (T i).toConvexSpaceBody ≤ (R (D.decomp.assign i)).toConvexSpaceBody) ∧
      ConvexSpaceBody.IsFrostmanIn (D.factor.coarseFibre x) (fun k => (R k).toConvexSpaceBody)
        (D.factor.repr x).toConvexSpaceBody (CF : ENNReal) ∧
      (∀ k ∈ D.factor.coarseFibre x,
        m / Cfib ≤ (({i ∈ D.fineFibre x | D.decomp.assign i = k} : Finset ι).card : ℝ≥0) ∧
          (({i ∈ D.fineFibre x | D.decomp.assign i = k} : Finset ι).card : ℝ≥0) ≤ Cfib * m) ∧
      (∀ k ∈ D.factor.coarseFibre x,
        (R k).carrier ⊆ ((D.factor.repr x).carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact D.carrier_subset_repr hi
  · intro i hi
    exact ⟨D.assign_mem_coarseFibre hi,
      D.decomp.leaf_le_parent i (D.fineFibre_subset x hi)⟩
  · exact D.remark53FibreFrostman x hx
  · intro k hk
    constructor
    · exact (D.cellDecomposition x).le_card_fibre k hk
    · exact (D.cellDecomposition x).card_fibre_le k hk
  · intro k hk
    exact Section6PartBFactorisation.carrier_subset_repr_of_mem_coarseFibre (F := D.factor) hk

/-- **The scale relation, from the Part-(B) datum.** -/
theorem rho_le (D' : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)
    (hne : coarseSet.Nonempty) : ρ ≤ a :=
  Section6PartBFactorisation.rho_le D'.factor hne

/-- **The weak Part-(B) hypothesis of `Kakeya.factoringAndMultPropGlobal`**, recovered from the
honest datum.  This is the whole cost of migrating that theorem's signature. -/
theorem exists_parent (D' : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀) :
    ∀ i ∈ q, ∃ k ∈ coarseSet, (T i).toConvexSpaceBody ≤ (R k).toConvexSpaceBody :=
  Section6CoarseTubeDecomposition.exists_parent D'.decomp

end Section6PartBData

end Kakeya

end

end
