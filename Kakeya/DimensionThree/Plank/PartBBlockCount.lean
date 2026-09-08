/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Pigeonhole
public import Kakeya.DimensionThree.Plank.Section6PartBProp51

/-!
# The block-size pigeonhole of GWZ Proposition 6.6(B)

`Kakeya.factoringAndMultPropGlobal` exports the cardinality clause

`|𝒲'| · |𝒯_W| ≤ Ccard · |𝒯|`,

with `Ccard` bound in the **outermost** existential — before the exponents, before `δ`, before
the family and before `Cfib`, `CF`, `C₀`.  `Ccard` is therefore absolute.  This file is about
where that clause comes from.

## What GWZ does, and does not, do

`Ccard` is **not** one of the seven items of Proposition 5.1
(`blueprint/src/GWZAdapted/section5_multiplicity.tex`).  GWZ obtains it from a *uniformization
step performed by hand*, and performs it only in **Part (A)**:

> After pigeonholing and refining `𝕋` and `𝕎`, we may suppose that `|Y(T)|` is approximately the
> same for each `T ∈ 𝕋`, and `|𝕋_W|` is approximately the same for each `W ∈ 𝕎`.
> (GWZ, proof of Proposition 6.6, Part (A))

**Part (B) never repeats it.**  Part (B) selects its outer plank only by shading density
("Select a set `W ∈ 𝕎` so that `λ(𝒯_W, Y') ⪆ δ^{-η}`"), and then closes with
"Since `|𝕋| ≈ |𝕎||𝕋_j| after the uniformization step" — a step that, in Part (B), does not exist.

## What that costs, and what this file supplies

Part (A)'s sentence is a dyadic pigeonhole on the sizes of the parts of the partition
`𝒯 = ⨆_{W ∈ 𝒲} 𝒯_W`, and it uses nothing specific to Part (A): not the Frostman hypothesis, not
`plankF`, not the per-coarse-tube factorization.  It therefore **transfers verbatim**.  The reason
it transfers is that the pigeonhole discards *whole cells*, so every per-cell hypothesis of the
Part-(B) datum (coarse-fibre Frostman, `body_le_repr`, `repr_window`, the fibre bounds of the
fine-to-coarse decomposition) is inherited unchanged on the surviving cells, and the two global
ratio-type hypotheses — the fullness `λ(𝒯, Y)` and the multiplicity `μ(𝒯, Y)` — pay exactly one
factor `Kakeya.dyadicPigeonholeNatConstant |𝒯| = Nat.log 2 |𝒯| + 1`, which is logarithmic in
`1/δ` and is absorbed by shrinking `η`.

`Kakeya.BlockCount.exists_dyadicCells` is that pigeonhole:

* `Kakeya.BlockCount.card_le_two_mul_card_of_mem_dyadicCells` — block comparability with the
  **absolute constant `2`**, which is the shape of
  `Kakeya.Section6PartBData.Remark53Prop51.fiber_card_comparable`;
* `Kakeya.BlockCount.card_mul_card_block_le` — `|𝒲'| · |𝒯_W| ≤ 2 · |𝒯|`, which is the `Ccard`
  clause with **`Ccard = 2`**;
* the mass clause, which is the only cost.

## The constant is `2`, not `1`

`Ccard = 1` *is* available, and is useless: `Kakeya.BlockCount.exists_min_block` shows that the
cell of **minimal** block size satisfies `|cells| · blk x ≤ |q|` with no pigeonhole at all.  But
Proposition 6.6(B) does not get to choose the cell.  The cell is handed to it by the *fullness*
selection `Kakeya.exists_fibre_fullness_le`, a mediant maximisation, and the fullest fibre is in
general the largest one.  Reading the aggregate identity `∑_x blk x = |q|` as a pointwise bound at
the fullness-selected cell is precisely the "aggregate bound consumed as pointwise" defect.  After
the dyadic restriction the correct pointwise constant is `2`, and `2` is sharp for the dyadic
class (a class may contain a cell of size `2^k` and a cell of size `2^{k+1} - 1`).

## Why the pigeonhole cannot be skipped

`Kakeya.BlockCount.not_absoluteBlockCount` and
`Kakeya.BlockCount.not_absoluteBlockComparability` refute the two clauses as stated for a general
block system: the counterexample is `q = range (2n)`, `cell i = min i n`, which has `n` singleton
blocks and one block of size `n`.  The ratio `|cells| · max blk / |q|` is then `(n+1)/2`, so the
failure is **polynomial in the number of cells** — `|cells| ≲ δ^{-4}` — not logarithmic.  No choice
of `δ₀` absorbs it.  The pigeonhole is genuinely necessary, and the constant it produces is
genuinely absolute.

## Effect on the tree

In this development the Part-(B) fine factor family is *unrefined*:
`Kakeya.Section6PartBData.fineOutput.outerSet = D.factor.cells` and
`Kakeya.Section6PartBData.fineOutput.fiber x = D.fineFibre x`, both by `rfl`
(`Kakeya.BlockCount.fineOutput_outerSet_eq`, `Kakeya.BlockCount.fineOutput_fiber_eq`).  So
`Remark53Prop51.fiber_card_comparable` is not a statement about Proposition 5.1's construction at
all — it is a bare assertion that the *input datum's* cell block sizes are comparable within an
absolute constant, i.e. exactly the Part (A) uniformization, assumed rather than performed.
`Kakeya.BlockCount.fiber_card_comparable_iff_block_comparable` pins that reading down, and
`Kakeya.BlockCount.not_absoluteBlockComparability` shows the assertion is false in general.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal Classical

noncomputable section

namespace Kakeya

namespace BlockCount

variable {ι κ : Type*}

/-! ## The blocks of a classification map -/

open Classical in
/-- The block of `q` over the cell `x`: the fibre of the classification map `cell`.

This is deliberately the same shape as `Kakeya.Section6PartBData.fineFibre` and
`ShadedBody.ShadedFactorFamily.fiber`, so that the Part-(B) instances are `rfl`. -/
def block (q : Finset ι) (cell : ι → κ) (x : κ) : Finset ι := {i ∈ q | cell i = x}

theorem mem_block_iff {q : Finset ι} {cell : ι → κ} {x : κ} {i : ι} :
    i ∈ block q cell x ↔ i ∈ q ∧ cell i = x := by
  classical
  simp [block, Finset.mem_filter]

theorem block_subset (q : Finset ι) (cell : ι → κ) (x : κ) : block q cell x ⊆ q := by
  intro i hi
  exact (mem_block_iff.mp hi).1

theorem card_block_le (q : Finset ι) (cell : ι → κ) (x : κ) : (block q cell x).card ≤ q.card :=
  Finset.card_le_card (block_subset q cell x)

theorem one_le_card_block {q : Finset ι} {cell : ι → κ} {i : ι} (hi : i ∈ q) :
    1 ≤ (block q cell (cell i)).card :=
  Finset.card_pos.mpr ⟨i, mem_block_iff.mpr ⟨hi, rfl⟩⟩

/-- **The blocks partition `q`.**  The total block size is the size of `q`; there is no constant
and no loss.  This is `Finset.card_eq_sum_card_fiberwise`, and it is the only global fact the
pigeonhole below uses. -/
theorem sum_card_block (q : Finset ι) (cell : ι → κ) (cells : Finset κ)
    (hmaps : ∀ i ∈ q, cell i ∈ cells) :
    (∑ x ∈ cells, (block q cell x).card) = q.card := by
  classical
  exact (Finset.card_eq_sum_card_fiberwise hmaps).symm

/-- **The `Ccard = 1` statement, and why it is useless.**

The cell of *minimal* block size satisfies `|cells| · blk x ≤ |q|` with no pigeonhole and no
constant.  Proposition 6.6(B) cannot use it: its cell is produced by the fullness maximisation
`Kakeya.exists_fibre_fullness_le`, not by a cardinality minimisation, and there is no reason for
the two to agree.  See `Kakeya.BlockCount.not_absoluteBlockCount` for what happens if one pretends
they do. -/
theorem exists_min_block (q : Finset ι) (cell : ι → κ) (cells : Finset κ)
    (hcells : cells.Nonempty) (hmaps : ∀ i ∈ q, cell i ∈ cells) :
    ∃ x ∈ cells, cells.card * (block q cell x).card ≤ q.card := by
  classical
  obtain ⟨x₀, hx₀, hmin⟩ :=
    Finset.exists_min_image cells (fun x => (block q cell x).card) hcells
  refine ⟨x₀, hx₀, ?_⟩
  calc
    cells.card * (block q cell x₀).card
        = ∑ _y ∈ cells, (block q cell x₀).card := by
          rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ y ∈ cells, (block q cell y).card := Finset.sum_le_sum hmin
    _ = q.card := sum_card_block q cell cells hmaps

/-! ## The dyadic block class -/

open Classical in
/-- The `k`-th **dyadic block class**: the cells whose block size lies in `[2 ^ k, 2 ^ (k + 1))`.

This is Part (A)'s "`|𝕋_W|` is approximately the same for each `W ∈ 𝕎`", made a definition. -/
def dyadicCells (q : Finset ι) (cell : ι → κ) (cells : Finset κ) (k : ℕ) : Finset κ :=
  {x ∈ cells | 2 ^ k ≤ (block q cell x).card ∧ (block q cell x).card < 2 ^ (k + 1)}

theorem mem_dyadicCells_iff {q : Finset ι} {cell : ι → κ} {cells : Finset κ} {k : ℕ} {x : κ} :
    x ∈ dyadicCells q cell cells k ↔
      x ∈ cells ∧ 2 ^ k ≤ (block q cell x).card ∧ (block q cell x).card < 2 ^ (k + 1) := by
  classical
  simp [dyadicCells, Finset.mem_filter]

theorem dyadicCells_subset (q : Finset ι) (cell : ι → κ) (cells : Finset κ) (k : ℕ) :
    dyadicCells q cell cells k ⊆ cells := by
  intro x hx
  exact (mem_dyadicCells_iff.mp hx).1

/-- Every cell of a dyadic class has a nonempty block. -/
theorem block_nonempty_of_mem_dyadicCells {q : Finset ι} {cell : ι → κ} {cells : Finset κ}
    {k : ℕ} {x : κ} (hx : x ∈ dyadicCells q cell cells k) : (block q cell x).Nonempty := by
  rcases mem_dyadicCells_iff.mp hx with ⟨-, hlow, -⟩
  have h1 : 1 ≤ (block q cell x).card := le_trans Nat.one_le_two_pow hlow
  exact Finset.card_pos.mp h1

/-- **Block comparability on a dyadic class, with the absolute constant `2`.**

This is the shape of `Kakeya.Section6PartBData.Remark53Prop51.fiber_card_comparable`, and the
constant is `2` because a dyadic class is a half-open interval `[2 ^ k, 2 ^ (k + 1))`. -/
theorem card_le_two_mul_card_of_mem_dyadicCells {q : Finset ι} {cell : ι → κ} {cells : Finset κ}
    {k : ℕ} {x y : κ} (hx : x ∈ dyadicCells q cell cells k)
    (hy : y ∈ dyadicCells q cell cells k) :
    (block q cell x).card ≤ 2 * (block q cell y).card := by
  rcases mem_dyadicCells_iff.mp hx with ⟨-, -, hxhigh⟩
  rcases mem_dyadicCells_iff.mp hy with ⟨-, hylow, -⟩
  have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
  omega

/-- **The cardinality clause of GWZ 6.6(B), on a dyadic class, with `Ccard = 2`.**

`|𝒲'| · |𝒯_W| ≤ 2 · |𝒯|` for **every** `W ∈ 𝒲'`, not merely for a well-chosen one.  That
`∀` is the whole point: the consumer's cell is chosen by the fullness selection. -/
theorem card_mul_card_block_le {q : Finset ι} {cell : ι → κ} {cells : Finset κ} {k : ℕ}
    (hmaps : ∀ i ∈ q, cell i ∈ cells) {x : κ} (hx : x ∈ dyadicCells q cell cells k) :
    (dyadicCells q cell cells k).card * (block q cell x).card ≤ 2 * q.card := by
  classical
  calc
    (dyadicCells q cell cells k).card * (block q cell x).card
        = ∑ _y ∈ dyadicCells q cell cells k, (block q cell x).card := by
          rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ y ∈ dyadicCells q cell cells k, 2 * (block q cell y).card :=
          Finset.sum_le_sum fun y hy => card_le_two_mul_card_of_mem_dyadicCells hx hy
    _ = 2 * ∑ y ∈ dyadicCells q cell cells k, (block q cell y).card := by
          rw [Finset.mul_sum]
    _ ≤ 2 * ∑ y ∈ cells, (block q cell y).card := by
          have := Finset.sum_le_sum_of_subset
            (f := fun y => (block q cell y).card) (dyadicCells_subset q cell cells k)
          omega
    _ = 2 * q.card := by rw [sum_card_block q cell cells hmaps]

/-! ## The pigeonhole -/

open Classical in
/-- **The block-size pigeonhole: GWZ Part (A)'s uniformization step, for Part (B).**

Given any weight `w` on the fine indices — in the application, the shade volume — there is a
dyadic block class `cells'` on which

* all block sizes are comparable with the absolute constant `2`;
* `|cells'| · blk x ≤ 2 · |q|` for **every** `x ∈ cells'`;
* every block is nonempty;

and which retains at least a `1 / (Nat.log 2 |q| + 1)` share of the total weight.  The last clause
is the only cost, and it is logarithmic: it is what GWZ's `⪅` hides, and it is absorbed by
shrinking the fullness exponent `η`.

`cells'` is obtained by *discarding whole cells*, which is why every per-cell hypothesis of a
Part-(B) datum survives it unchanged. -/
theorem exists_dyadicCells (q : Finset ι) (cell : ι → κ) (cells : Finset κ)
    (hmaps : ∀ i ∈ q, cell i ∈ cells) (w : ι → ENNReal) :
    ∃ cells' : Finset κ, cells' ⊆ cells ∧
      (∀ x ∈ cells', (block q cell x).Nonempty) ∧
      (∀ x ∈ cells', ∀ y ∈ cells', (block q cell x).card ≤ 2 * (block q cell y).card) ∧
      (∀ x ∈ cells', cells'.card * (block q cell x).card ≤ 2 * q.card) ∧
      (∑ i ∈ q, w i
        ≤ (Kakeya.dyadicPigeonholeNatConstant q.card : ENNReal)
            * ∑ i ∈ {i ∈ q | cell i ∈ cells'}, w i) := by
  classical
  obtain ⟨k, -, hmass⟩ :=
    Nat.dyadic_pigeonhole_ennreal (N := q.card) q w
      (fun i => (block q cell (cell i)).card)
      (fun i hi => ⟨one_le_card_block hi, card_block_le q cell (cell i)⟩)
  refine ⟨dyadicCells q cell cells k, dyadicCells_subset q cell cells k,
    fun x hx => block_nonempty_of_mem_dyadicCells hx,
    fun x hx y hy => card_le_two_mul_card_of_mem_dyadicCells hx hy,
    fun x hx => card_mul_card_block_le hmaps hx, ?_⟩
  refine le_trans hmass (le_of_eq ?_)
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_filter, mem_dyadicCells_iff]
  constructor
  · rintro ⟨hi, hlow, hhigh⟩
    exact ⟨hi, hmaps i hi, hlow, hhigh⟩
  · rintro ⟨hi, -, hlow, hhigh⟩
    exact ⟨hi, hlow, hhigh⟩


/-! ## What the logarithmic factor costs

Two transports, both with the same constant `L = Kakeya.dyadicPigeonholeNatConstant |q|`.  They
are the whole price of the pigeonhole: everything else in a Part-(B) datum is a per-cell
hypothesis, and the class is obtained by discarding whole cells. -/

section Analytic

variable {ι : Type*} {q' q : Finset ι} {V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}

/-- **A sub-family that keeps a `1/L` share of the shade mass is an `L⁻¹`-refinement.**

The carriers are literally the same bodies, so the `ShadedBody.IsRefinement` clause is trivial and
the content is entirely the mass inequality — which is exactly the last clause of
`Kakeya.BlockCount.exists_dyadicCells`.  Composing with
`ShadedBody.IsCRefinement.mul_fullness_le` gives `L⁻¹ · λ(𝒯, Y) ≤ λ(𝒯'', Y)`, i.e. the fullness
budget pays one logarithm and nothing else. -/
theorem isCRefinement_of_subset_of_sum_le {L : ℝ≥0} (hsub : q' ⊆ q)
    (hmass : ∑ i ∈ q, volume (V i).shade ≤ (L : ENNReal) * ∑ i ∈ q', volume (V i).shade) :
    ShadedBody.IsCRefinement q' V q V L⁻¹ :=
  ShadedBody.isCRefinement_of_isRefinement_of_sum_le q' V q V
    ⟨hsub, fun _ _ => ⟨rfl, subset_rfl⟩⟩ hmass

/-- **The same sub-family loses at most `L` in multiplicity.**

`ShadedBody.multiplicity` is `(∑ |Y|) / |U(Y)|`.  Passing to a sub-family multiplies the numerator
by at least `1/L` (hypothesis) and can only *shrink* the denominator, so the ratio drops by at most
`L`.  This is the clause that lets `μ(𝒯, Y)` on the left of GWZ's split
`boundMuByWandTTW` be replaced by `μ` of the pigeonholed family. -/
theorem multiplicity_le_mul_of_subset {L : ENNReal} (hsub : q' ⊆ q)
    (hmass : ∑ i ∈ q, volume (V i).shade ≤ L * ∑ i ∈ q', volume (V i).shade) :
    ShadedBody.multiplicity q V ≤ L * ShadedBody.multiplicity q' V := by
  have hU : volume (⋃ i ∈ q', (V i).shade) ≤ volume (⋃ i ∈ q, (V i).shade) :=
    measure_mono (Set.biUnion_subset_biUnion_left hsub)
  calc
    ShadedBody.multiplicity q V
        = (∑ i ∈ q, volume (V i).shade) / volume (⋃ i ∈ q, (V i).shade) :=
          ShadedBody.multiplicity_eq_div q V
    _ ≤ (L * ∑ i ∈ q', volume (V i).shade) / volume (⋃ i ∈ q', (V i).shade) :=
          ENNReal.div_le_div hmass hU
    _ = L * ((∑ i ∈ q', volume (V i).shade) / volume (⋃ i ∈ q', (V i).shade)) :=
          mul_div_assoc _ _ _
    _ = L * ShadedBody.multiplicity q' V := by rw [ShadedBody.multiplicity_eq_div]

end Analytic


/-! ## The Part-(B) reading

In this development the Part-(B) fine factor family produced by
`Kakeya.Section6PartBData.fineOutput` is **unrefined**: its outer set is *all* the cells and its
fibres are *exactly* the datum's own `Kakeya.Section6PartBData.fineFibre`.  Both facts hold by
`rfl`.  Consequently
`Kakeya.Section6PartBData.Remark53Prop51.fiber_card_comparable` — whose docstring attributes it to
"the pigeonholing inside the [Proposition 5.1] construction" — makes no reference to Proposition
5.1 whatsoever.  It is the bare assertion that the *input datum's* cell block sizes are comparable
within an absolute constant: precisely GWZ Part (A)'s uniformization sentence, assumed rather than
performed.  `Kakeya.BlockCount.not_absoluteBlockComparability` shows that assumption is false in
general. -/

section PartB

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
  {m Cfib CF C₀ : ℝ≥0}
  (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)

/-- **The Proposition-5.1 output selects nothing**: its outer set is all the cells of the datum. -/
theorem fineOutput_outerSet_eq : D.fineOutput.outerSet = D.factor.cells := rfl

/-- **The Proposition-5.1 fibres are the datum's own blocks.**  Nothing has been refined. -/
theorem fineOutput_fiber_eq (x : D.factor.Cell) :
    D.fineOutput.fiber x = block q D.cellOfFine x := rfl

/-- The cell map sends the fine family into the cells of the datum. -/
theorem cellOfFine_maps : ∀ i ∈ q, D.cellOfFine i ∈ D.factor.cells :=
  fun i hi => D.factor.cellOf_mem _ (D.decomp.assign_mem i hi)

/-- **compatibility.**  `Kakeya.Section6PartBData.Remark53Prop51.fiber_card_comparable` *is* the
statement that the input datum's block sizes are comparable — no Proposition 5.1 anywhere. -/
theorem fiber_card_comparable_iff_block_comparable (Cprop : ℝ≥0) :
    (∀ x ∈ D.fineOutput.outerSet, ∀ y ∈ D.fineOutput.outerSet,
        ((D.fineOutput.fiber x).card : ℝ≥0) ≤ Cprop * ((D.fineOutput.fiber y).card : ℝ≥0))
      ↔ (∀ x ∈ D.factor.cells, ∀ y ∈ D.factor.cells,
        ((block q D.cellOfFine x).card : ℝ≥0)
          ≤ Cprop * ((block q D.cellOfFine y).card : ℝ≥0)) :=
  Iff.rfl

/-- **compatibility, pinned to the real field.**  If the shape of
`Kakeya.Section6PartBData.Remark53Prop51.fiber_card_comparable` ever changes, this breaks. -/
example {Cprop : ℝ≥0} (hR : D.Remark53Prop51 Cprop) :
    ∀ x ∈ D.factor.cells, ∀ y ∈ D.factor.cells,
      ((block q D.cellOfFine x).card : ℝ≥0)
        ≤ Cprop * ((block q D.cellOfFine y).card : ℝ≥0) :=
  hR.fiber_card_comparable

/-- **compatibility, pinned to the consumer.**  The hypothesis of
`Kakeya.Section6PartBData.card_mul_card_fiber_le` — the lemma that discharges the `Ccard` clause of
`Kakeya.factoringAndMultPropGlobal` — asks for the *fullness-selected* cell `x₀` to be within
`Ccard` of the **minimum** block size over **all** cells.  That is the quantifier order the
pigeonhole below repairs. -/
example {Cprop Ccard : ℝ≥0} (hR : D.Remark53Prop51 Cprop) {x₀ : D.factor.Cell}
    (hcomp : ∀ y ∈ D.factor.cells,
      ((block q D.cellOfFine x₀).card : ℝ≥0) ≤ Ccard * ((block q D.cellOfFine y).card : ℝ≥0)) :
    ((D.factor.cells.card : ℝ≥0)) * ((block q D.cellOfFine x₀).card : ℝ≥0)
      ≤ Ccard * (q.card : ℝ≥0) :=
  D.card_mul_card_fiber_le hR hcomp

/-! ### What the block sizes actually are

A block is the union of the fine fibres of the coarse tubes the cell collects, and those fibres are
two-sidedly comparable to `m` by `Kakeya.Section6CoarseTubeDecomposition`.  So, up to `Cfib²`,

`|𝒯_x| ≍ m · |{coarse tubes collected by x}|`,

and **block comparability across cells is exactly comparability of the number of `ρ`-tubes each
`a × b × 1` plank collects.**  Nothing in `Kakeya.Section6PartBFactorisation` constrains that: the
coarse-fibre Frostman clause is a statement *inside one cell*, and the Katz--Tao clause bounds the
density of the cell *bodies*, not the count of tubes inside them.  This is why the uniformization
has to be performed and cannot be read off the datum. -/

/-- **A block is the disjoint union of the coarse fibres the cell collects.** -/
theorem card_block_eq_sum_card_fibre {x : D.factor.Cell} :
    (block q D.cellOfFine x).card
      = ∑ k ∈ D.factor.coarseFibre x, (D.decomp.fibre k).card := by
  classical
  have hmaps : ∀ i ∈ D.fineFibre x, D.decomp.assign i ∈ D.factor.coarseFibre x :=
    fun i hi => D.assign_mem_coarseFibre hi
  have h := Finset.card_eq_sum_card_fiberwise hmaps
  rw [show block q D.cellOfFine x = D.fineFibre x from rfl, h]
  exact Finset.sum_congr rfl fun k hk => by rw [D.filter_fineFibre_eq hk]

/-- **Upper half**: `|𝒯_x| ≤ Cfib · m · |coarse fibre of x|`. -/
theorem card_block_le_mul_card_coarseFibre {x : D.factor.Cell} :
    ((block q D.cellOfFine x).card : ℝ≥0)
      ≤ Cfib * m * ((D.factor.coarseFibre x).card : ℝ≥0) := by
  classical
  rw [card_block_eq_sum_card_fibre D]
  push_cast
  calc
    (∑ k ∈ D.factor.coarseFibre x, ((D.decomp.fibre k).card : ℝ≥0))
        ≤ ∑ _k ∈ D.factor.coarseFibre x, Cfib * m :=
          Finset.sum_le_sum fun k hk =>
            D.decomp.card_fibre_le k (D.factor.coarseFibre_subset x hk)
    _ = Cfib * m * ((D.factor.coarseFibre x).card : ℝ≥0) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring

/-- **Lower half**: `(m / Cfib) · |coarse fibre of x| ≤ |𝒯_x|`. -/
theorem mul_card_coarseFibre_le_card_block {x : D.factor.Cell} :
    m / Cfib * ((D.factor.coarseFibre x).card : ℝ≥0)
      ≤ ((block q D.cellOfFine x).card : ℝ≥0) := by
  classical
  rw [card_block_eq_sum_card_fibre D]
  push_cast
  calc
    m / Cfib * ((D.factor.coarseFibre x).card : ℝ≥0)
        = ∑ _k ∈ D.factor.coarseFibre x, m / Cfib := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
    _ ≤ ∑ k ∈ D.factor.coarseFibre x, ((D.decomp.fibre k).card : ℝ≥0) :=
          Finset.sum_le_sum fun k hk =>
            D.decomp.le_card_fibre k (D.factor.coarseFibre_subset x hk)

open Classical in
/-- **GWZ Part (A)'s uniformization step, executed for the Part-(B) datum.**

There is a class of cells `cells' ⊆ D.factor.cells` on which

* every block is nonempty;
* the block sizes are comparable with the **absolute constant `2`** — the shape of
  `Remark53Prop51.fiber_card_comparable`, now a theorem rather than a hypothesis;
* `|cells'| · |𝒯_x| ≤ 2 · |𝒯|` for **every** `x ∈ cells'` — the `Ccard` clause of
  `Kakeya.factoringAndMultPropGlobal` with `Ccard = 2`, and with the `∀` that the fullness
  selection needs;

and the fine family restricted to those cells is an `L⁻¹`-refinement of the whole fine family,
with `L = Kakeya.dyadicPigeonholeNatConstant |𝒯| = Nat.log 2 |𝒯| + 1`, whence its fullness is at
least `L⁻¹ λ(𝒯, Y)` (`ShadedBody.IsCRefinement.mul_fullness_le`) and
`μ(𝒯, Y) ≤ L · μ(𝒯'', Y)`.

`cells'` is obtained by discarding whole cells, so every per-cell field of
`Kakeya.Section6PartBFactorisation` and every fibre bound of
`Kakeya.Section6CoarseTubeDecomposition` restricts to it unchanged.  `L` is the entire price. -/
theorem exists_partB_dyadicCells :
    ∃ cells' : Finset D.factor.Cell, cells' ⊆ D.factor.cells ∧
      (∀ x ∈ cells', (D.fineOutput.fiber x).Nonempty) ∧
      (∀ x ∈ cells', ∀ y ∈ cells',
        ((D.fineOutput.fiber x).card : ℝ≥0) ≤ 2 * ((D.fineOutput.fiber y).card : ℝ≥0)) ∧
      (∀ x ∈ cells', (cells'.card : ENNReal) * ((D.fineOutput.fiber x).card : ENNReal)
        ≤ (2 : ℝ≥0) * (q.card : ENNReal)) ∧
      ShadedBody.IsCRefinement ({i ∈ q | D.cellOfFine i ∈ cells'})
          (fun i => (T i).toShadedBody) q (fun i => (T i).toShadedBody)
          ((Kakeya.dyadicPigeonholeNatConstant q.card : ℝ≥0))⁻¹ ∧
      ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
        ≤ (Kakeya.dyadicPigeonholeNatConstant q.card : ENNReal)
            * ShadedBody.multiplicity ({i ∈ q | D.cellOfFine i ∈ cells'})
                (fun i => (T i).toShadedBody) := by
  classical
  obtain ⟨cells', hsub, hne, hcomp, hcount, hmass⟩ :=
    exists_dyadicCells q D.cellOfFine D.factor.cells (cellOfFine_maps D)
      (fun i => volume ((T i).toShadedBody).shade)
  refine ⟨cells', hsub, hne, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    have := hcomp x hx y hy
    rw [fineOutput_fiber_eq, fineOutput_fiber_eq]
    exact_mod_cast this
  · intro x hx
    have := hcount x hx
    rw [fineOutput_fiber_eq]
    exact_mod_cast this
  · exact isCRefinement_of_subset_of_sum_le (Finset.filter_subset _ _) (by simpa using hmass)
  · exact multiplicity_le_mul_of_subset (Finset.filter_subset _ _) hmass

end PartB

/-! ### The restricted datum: why the Part (A) argument transfers

The pigeonhole discards **whole cells**, and that is the entire reason Part (A)'s sentence works in
Part (B).  Every field of `Kakeya.Section6PartBFactorisation` and of
`Kakeya.Section6CoarseTubeDecomposition` is either per cell, per coarse tube, or a constant, so all
of them restrict *verbatim* — the coarse-fibre Frostman clause and the two-sided fine-fibre
comparability are literally the same `Finset`s, not merely comparable ones.  The following
construction makes that a theorem instead of a table. -/

section Restrict

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
  {m Cfib CF C₀ : ℝ≥0}
  (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)

open Classical in
/-- The fine indices surviving a restriction to `cells'`. -/
def restrictFine (cells' : Finset D.factor.Cell) : Finset ι :=
  {i ∈ q | D.cellOfFine i ∈ cells'}

open Classical in
/-- The coarse indices surviving a restriction to `cells'`. -/
def restrictCoarse (cells' : Finset D.factor.Cell) : Finset κ :=
  {k ∈ coarseSet | D.factor.cellOf k ∈ cells'}

variable {D}

theorem mem_restrictFine_iff {cells' : Finset D.factor.Cell} {i : ι} :
    i ∈ restrictFine D cells' ↔ i ∈ q ∧ D.cellOfFine i ∈ cells' := by
  classical
  simp [restrictFine, Finset.mem_filter]

theorem mem_restrictCoarse_iff {cells' : Finset D.factor.Cell} {k : κ} :
    k ∈ restrictCoarse D cells' ↔ k ∈ coarseSet ∧ D.factor.cellOf k ∈ cells' := by
  classical
  simp [restrictCoarse, Finset.mem_filter]

/-- **A surviving coarse tube keeps its whole fine fibre.**  This is why the two-sided fibre
comparability of `Kakeya.Section6CoarseTubeDecomposition` restricts with no loss. -/
theorem filter_restrictFine_assign_eq {cells' : Finset D.factor.Cell} {k : κ}
    (hk : D.factor.cellOf k ∈ cells') :
    ({i ∈ restrictFine D cells' | D.decomp.assign i = k} : Finset ι)
      = ({i ∈ q | D.decomp.assign i = k} : Finset ι) := by
  classical
  ext i
  simp only [Finset.mem_filter, mem_restrictFine_iff]
  constructor
  · rintro ⟨⟨hi, -⟩, hass⟩
    exact ⟨hi, hass⟩
  · rintro ⟨hi, hass⟩
    refine ⟨⟨hi, ?_⟩, hass⟩
    change D.factor.cellOf (D.decomp.assign i) ∈ cells'
    rw [hass]
    exact hk

/-- **A surviving cell keeps its whole coarse fibre.**  This is why the coarse-fibre Frostman
clause restricts verbatim. -/
theorem filter_restrictCoarse_cellOf_eq {cells' : Finset D.factor.Cell}
    {x : D.factor.Cell} (hx : x ∈ cells') :
    ({k ∈ restrictCoarse D cells' | D.factor.cellOf k = x} : Finset κ)
      = ({k ∈ coarseSet | D.factor.cellOf k = x} : Finset κ) := by
  classical
  ext k
  simp only [Finset.mem_filter, mem_restrictCoarse_iff]
  constructor
  · rintro ⟨⟨hk, -⟩, hcell⟩
    exact ⟨hk, hcell⟩
  · rintro ⟨hk, hcell⟩
    exact ⟨⟨hk, hcell ▸ hx⟩, hcell⟩

/-- **A surviving cell keeps its whole fine block.** -/
theorem block_restrictFine_eq {cells' : Finset D.factor.Cell} {x : D.factor.Cell}
    (hx : x ∈ cells') :
    block (restrictFine D cells') D.cellOfFine x = block q D.cellOfFine x := by
  classical
  ext i
  simp only [mem_block_iff, mem_restrictFine_iff]
  constructor
  · rintro ⟨⟨hi, -⟩, hcell⟩
    exact ⟨hi, hcell⟩
  · rintro ⟨hi, hcell⟩
    exact ⟨⟨hi, hcell ▸ hx⟩, hcell⟩

variable (D)

open Classical in
/-- **The Part-(B) datum restricted to a subset of cells.**

Every field is the original one, read on the surviving indices.  The only field that is not a
literal restriction is `isKatzTao`, and it is `ConvexSpaceBody.IsKatzTao.subset`. -/
def restrictCells (cells' : Finset D.factor.Cell) (hsub : cells' ⊆ D.factor.cells) :
    Section6PartBData a b hab hb1 (restrictFine D cells') T (restrictCoarse D cells') R
      m Cfib CF C₀ where
  decomp :=
    { assign := D.decomp.assign
      assign_mem := by
        intro i hi
        rcases mem_restrictFine_iff.mp hi with ⟨hiq, hcell⟩
        exact mem_restrictCoarse_iff.mpr ⟨D.decomp.assign_mem i hiq, hcell⟩
      leaf_le_parent := fun i hi => D.decomp.leaf_le_parent i (mem_restrictFine_iff.mp hi).1
      one_le_Cfib := D.decomp.one_le_Cfib
      m_pos := D.decomp.m_pos
      fibre_nonempty := by
        intro k hk
        rw [filter_restrictFine_assign_eq (mem_restrictCoarse_iff.mp hk).2]
        exact D.decomp.fibre_nonempty k (mem_restrictCoarse_iff.mp hk).1
      le_card_fibre := by
        intro k hk
        rw [filter_restrictFine_assign_eq (mem_restrictCoarse_iff.mp hk).2]
        exact D.decomp.le_card_fibre k (mem_restrictCoarse_iff.mp hk).1
      card_fibre_le := by
        intro k hk
        rw [filter_restrictFine_assign_eq (mem_restrictCoarse_iff.mp hk).2]
        exact D.decomp.card_fibre_le k (mem_restrictCoarse_iff.mp hk).1 }
  factor :=
    { Cell := D.factor.Cell
      cells := cells'
      body := D.factor.body
      cellOf := D.factor.cellOf
      cellOf_mem := fun k hk => (mem_restrictCoarse_iff.mp hk).2
      le_body := fun k hk => D.factor.le_body k (mem_restrictCoarse_iff.mp hk).1
      repr := D.factor.repr
      body_le_repr := fun x hx => D.factor.body_le_repr x (hsub hx)
      repr_window := fun x hx => D.factor.repr_window x (hsub hx)
      one_le_CF := D.factor.one_le_CF
      coarse_fibre_frostman := by
        intro x hx
        rw [filter_restrictCoarse_cellOf_eq hx]
        exact D.factor.coarse_fibre_frostman x (hsub hx)
      isKatzTao := D.factor.isKatzTao.subset hsub }

@[simp] theorem restrictCells_cells (cells' : Finset D.factor.Cell)
    (hsub : cells' ⊆ D.factor.cells) :
    (restrictCells D cells' hsub).factor.cells = cells' := rfl

@[simp] theorem restrictCells_cellOfFine (cells' : Finset D.factor.Cell)
    (hsub : cells' ⊆ D.factor.cells) (i : ι) :
    (restrictCells D cells' hsub).cellOfFine i = D.cellOfFine i := rfl

/-- **The restricted datum's Proposition-5.1 fibres are the surviving original blocks.** -/
theorem restrictCells_fineOutput_fiber (cells' : Finset D.factor.Cell)
    (hsub : cells' ⊆ D.factor.cells) {x : D.factor.Cell} (hx : x ∈ cells') :
    (restrictCells D cells' hsub).fineOutput.fiber x = block q D.cellOfFine x :=
  block_restrictFine_eq hx

open Classical in
/-- **GWZ Part (A)'s uniformization step, performed on a Part-(B) datum.**

There is a sub-datum `D''` of `D`, obtained by discarding whole cells — so with every per-cell
field of `D` inherited verbatim — for which

* the `fiber_card_comparable` clause of `Kakeya.Section6PartBData.Remark53Prop51` holds **as a
  theorem, with the absolute constant `2`**;
* the `Ccard` clause of `Kakeya.factoringAndMultPropGlobal` holds **for every cell**, with
  `Ccard = 2`;

at the single cost that the fine family of `D''` is an `L⁻¹`-refinement of that of `D`,
`L = Kakeya.dyadicPigeonholeNatConstant |𝒯| = Nat.log 2 |𝒯| + 1`, hence

* `L⁻¹ · λ(𝒯, Y) ≤ λ(𝒯'', Y)`, by `ShadedBody.IsCRefinement.mul_fullness_le`;
* `μ(𝒯, Y) ≤ L · μ(𝒯'', Y)`.

`L` is logarithmic in `1/δ` once `|𝒯| ≲ δ^{-4}`, so it is absorbed by shrinking the fullness
exponent `η`; it never touches `Ccard`, which stays absolute.  **This is the missing step of GWZ's
Part (B), and it is Part (A)'s step unchanged.** -/
theorem exists_restrictCells_block_equalised :
    ∃ (cells' : Finset D.factor.Cell) (hsub : cells' ⊆ D.factor.cells),
      (∀ x ∈ cells', ((restrictCells D cells' hsub).fineOutput.fiber x).Nonempty) ∧
      (∀ x ∈ cells', ∀ y ∈ cells',
        (((restrictCells D cells' hsub).fineOutput.fiber x).card : ℝ≥0)
          ≤ 2 * (((restrictCells D cells' hsub).fineOutput.fiber y).card : ℝ≥0)) ∧
      (∀ x ∈ cells',
        (((restrictCells D cells' hsub).factor.cells.card : ENNReal))
            * (((restrictCells D cells' hsub).fineOutput.fiber x).card : ENNReal)
          ≤ (2 : ℝ≥0) * ((restrictFine D cells').card : ENNReal)) ∧
      ShadedBody.IsCRefinement (restrictFine D cells') (fun i => (T i).toShadedBody)
          q (fun i => (T i).toShadedBody)
          ((Kakeya.dyadicPigeonholeNatConstant q.card : ℝ≥0))⁻¹ ∧
      ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
        ≤ (Kakeya.dyadicPigeonholeNatConstant q.card : ENNReal)
            * ShadedBody.multiplicity (restrictFine D cells') (fun i => (T i).toShadedBody) := by
  classical
  obtain ⟨cells', hsub, hne, hcomp, -, hmass⟩ :=
    exists_dyadicCells q D.cellOfFine D.factor.cells (cellOfFine_maps D)
      (fun i => volume ((T i).toShadedBody).shade)
  refine ⟨cells', hsub, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [restrictCells_fineOutput_fiber D cells' hsub hx]
    exact hne x hx
  · intro x hx y hy
    rw [restrictCells_fineOutput_fiber D cells' hsub hx,
      restrictCells_fineOutput_fiber D cells' hsub hy]
    exact_mod_cast hcomp x hx y hy
  · intro x hx
    rw [restrictCells_cells, restrictCells_fineOutput_fiber D cells' hsub hx]
    -- On the restricted datum the count clause is the *exact* pigeonhole inequality, with the
    -- restricted fine family in the denominator: `|cells'| · blk x ≤ 2 · |𝒯''|`.
    have hkey : cells'.card * (block q D.cellOfFine x).card
        ≤ 2 * (restrictFine D cells').card := by
      have hmaps'' : ∀ i ∈ restrictFine D cells', D.cellOfFine i ∈ cells' :=
        fun i hi => (mem_restrictFine_iff.mp hi).2
      calc
        cells'.card * (block q D.cellOfFine x).card
            = cells'.card * (block (restrictFine D cells') D.cellOfFine x).card := by
              rw [block_restrictFine_eq hx]
        _ = ∑ _y ∈ cells', (block (restrictFine D cells') D.cellOfFine x).card := by
              rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ y ∈ cells', 2 * (block (restrictFine D cells') D.cellOfFine y).card := by
              refine Finset.sum_le_sum fun y hy => ?_
              rw [block_restrictFine_eq hx, block_restrictFine_eq hy]
              exact hcomp x hx y hy
        _ = 2 * ∑ y ∈ cells', (block (restrictFine D cells') D.cellOfFine y).card := by
              rw [Finset.mul_sum]
        _ = 2 * (restrictFine D cells').card := by
              rw [sum_card_block (restrictFine D cells') D.cellOfFine cells' hmaps'']
    exact_mod_cast hkey
  · exact isCRefinement_of_subset_of_sum_le
      (fun i hi => (mem_restrictFine_iff.mp hi).1) (by simpa [restrictFine] using hmass)
  · exact multiplicity_le_mul_of_subset
      (fun i hi => (mem_restrictFine_iff.mp hi).1) (by simpa [restrictFine] using hmass)

end Restrict


/-! ## Refutation: the clause is false without the pigeonhole

The two `Prop`s below are the two clauses `Kakeya.Section6PartBData.Remark53Prop51` asserts, read
for a general block system with the constant quantified **first** — which is what
`Kakeya.factoringAndMultPropGlobal` requires of `Ccard`, and what the docstring of
`Remark53Prop51.fiber_card_comparable` claims ("it carries the absolute constant, so it is
legitimate input for a constant that Proposition 6.6(B) must fix before the configuration").

Both are false.  They are restricted to `ι = κ = ℕ`, which makes the refutations *stronger*: a
counterexample over `ℕ` refutes every more general form. -/

/-- **The fibre-comparability clause, with the constant fixed before the block system.**

This is `Kakeya.Section6PartBData.Remark53Prop51.fiber_card_comparable` read through
`Kakeya.BlockCount.fiber_card_comparable_iff_block_comparable`. -/
def AbsoluteBlockComparability : Prop :=
  ∃ C : ℝ≥0, ∀ (q : Finset ℕ) (cell : ℕ → ℕ) (cells : Finset ℕ),
    (∀ i ∈ q, cell i ∈ cells) →
    (∀ x ∈ cells, (block q cell x).Nonempty) →
    ∀ x ∈ cells, ∀ y ∈ cells,
      ((block q cell x).card : ℝ≥0) ≤ C * ((block q cell y).card : ℝ≥0)

/-- **The `Ccard` clause of `Kakeya.factoringAndMultPropGlobal`, with the constant fixed before the
block system**: `|𝒲'| · |𝒯_W| ≤ Ccard · |𝒯|` for every `W`, not for a well-chosen one. -/
def AbsoluteBlockCount : Prop :=
  ∃ C : ℝ≥0, ∀ (q : Finset ℕ) (cell : ℕ → ℕ) (cells : Finset ℕ),
    (∀ i ∈ q, cell i ∈ cells) →
    (∀ x ∈ cells, (block q cell x).Nonempty) →
    ∀ x ∈ cells,
      (cells.card : ℝ≥0) * ((block q cell x).card : ℝ≥0) ≤ C * (q.card : ℝ≥0)

/-! ### The witness: `n` singleton blocks and one block of size `n` -/

/-- The witness classification map: `q = {0, …, 2n-1}` is split into the singletons
`{0}, …, {n-1}` and the single block `{n, …, 2n-1}`. -/
theorem block_skew_top (n : ℕ) :
    block (Finset.range (2 * n)) (fun i => min i n) n = Finset.Ico n (2 * n) := by
  ext i
  simp only [mem_block_iff, Finset.mem_range, Finset.mem_Ico]
  omega

theorem block_skew_low (n : ℕ) {x : ℕ} (hx : x < n) :
    block (Finset.range (2 * n)) (fun i => min i n) x = {x} := by
  ext i
  simp only [mem_block_iff, Finset.mem_range, Finset.mem_singleton]
  omega

theorem block_skew_maps (n : ℕ) :
    ∀ i ∈ Finset.range (2 * n), (fun i => min i n) i ∈ Finset.range (n + 1) := by
  intro i _
  simp only [Finset.mem_range]
  omega

theorem block_skew_nonempty (n : ℕ) (hn : 1 ≤ n) :
    ∀ x ∈ Finset.range (n + 1), (block (Finset.range (2 * n)) (fun i => min i n) x).Nonempty := by
  intro x hx
  simp only [Finset.mem_range] at hx
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hx) with h | h
  · rw [block_skew_low n h]
    exact Finset.singleton_nonempty x
  · subst h
    rw [block_skew_top]
    exact Finset.nonempty_Ico.mpr (by omega)

theorem card_block_skew_top (n : ℕ) :
    (block (Finset.range (2 * n)) (fun i => min i n) n).card = n := by
  rw [block_skew_top, Nat.card_Ico]
  omega

/-! ### The refutations -/

/-- **The fibre-comparability clause of `Remark53Prop51` is false with an absolute constant.**

The big block has `n` elements and the singleton blocks have one, so the ratio is `n`, which is
unbounded.  In the application `n` is the number of fine tubes over one outer cell, so the ratio
can be as large as `|𝒯|` itself. -/
theorem not_absoluteBlockComparability : ¬ AbsoluteBlockComparability := by
  rintro ⟨C, hC⟩
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt ((C : ℝ) + 1)
  set n : ℕ := max 1 n₀ with hn_def
  have hn1 : 1 ≤ n := le_max_left _ _
  have hnC : (C : ℝ) + 1 < (n : ℝ) :=
    lt_of_lt_of_le hn₀ (by exact_mod_cast le_max_right 1 n₀)
  have hmem_n : n ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hmem_0 : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have h := hC (Finset.range (2 * n)) (fun i => min i n) (Finset.range (n + 1))
    (block_skew_maps n) (block_skew_nonempty n hn1) n hmem_n 0 hmem_0
  rw [card_block_skew_top n, block_skew_low n (by omega : 0 < n), Finset.card_singleton] at h
  have hR : (n : ℝ) ≤ (C : ℝ) * 1 := by exact_mod_cast NNReal.coe_le_coe.mpr h
  nlinarith [hnC, hR]

/-- **The `Ccard` clause is false with an absolute constant.**

`|cells| · blk x = (n+1)·n` while `|q| = 2n`, so the clause forces `C ≥ (n+1)/2`.  The failure is
**polynomial in the number of cells**, not logarithmic: no choice of `δ₀` absorbs it, and this is
why the dyadic pigeonhole of `Kakeya.BlockCount.exists_dyadicCells` cannot be skipped. -/
theorem not_absoluteBlockCount : ¬ AbsoluteBlockCount := by
  rintro ⟨C, hC⟩
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (2 * (C : ℝ) + 1)
  set n : ℕ := max 1 n₀ with hn_def
  have hn1 : 1 ≤ n := le_max_left _ _
  have hnC : 2 * (C : ℝ) + 1 < (n : ℝ) :=
    lt_of_lt_of_le hn₀ (by exact_mod_cast le_max_right 1 n₀)
  have hmem_n : n ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have h := hC (Finset.range (2 * n)) (fun i => min i n) (Finset.range (n + 1))
    (block_skew_maps n) (block_skew_nonempty n hn1) n hmem_n
  rw [card_block_skew_top n, Finset.card_range, Finset.card_range] at h
  have hR : ((n : ℝ) + 1) * (n : ℝ) ≤ (C : ℝ) * (2 * (n : ℝ)) := by
    have := NNReal.coe_le_coe.mpr h
    push_cast at this
    linarith [this]
  have hnpos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  nlinarith [hnC, hR, hnpos]

end BlockCount

end Kakeya
