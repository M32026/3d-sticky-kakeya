/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ConvexBody
public import Kakeya.Pigeonhole

/-!
# Extracting an essentially distinct subfamily

GWZ Proposition 6.6(B) needs its *inner* normalised plank family to be pairwise essentially
distinct.  That property is **not** produced by the normalisation:
`Kakeya.innerShadedPlankFamily` only places the image `f(T i)` of each fine tube *inside* a model
plank `P i` of the exact dimensions `(δ/b) × (δ/a) × 1`, and essential distinctness is destroyed by
enlarging bodies — two barely-overlapping tubes can sit in two nearly coincident planks.  The
normalisation file records this explicitly.

The repair is an *extraction*: pass to a subfamily on which essential distinctness does hold, paying
a bounded factor in cardinality.  This file contains the combinatorial half of that argument, in a
form that is independent of all Section-6 data.

## What is here

`Kakeya.exists_conflictFree_subset` is the greedy independent-set bound: a symmetric conflict
relation whose degree on `s` is at most `d` admits a conflict-free `t ⊆ s` with
`s.card ≤ (d + 1) * t.card`.  `Kakeya.exists_essentiallyDistinct_subset` is its specialisation to
the conflict relation "fails to be essentially distinct".

Both are stated for an arbitrary family of sets, so they apply verbatim to the inner planks, to the
outer planks, or to any other family for which a degree bound is available.

## What is *not* here, and why

The geometric input — a bound on the conflict degree of the inner plank family — is deliberately
left to the caller.  It is a genuinely separate statement, and the honest route to it is:

1. two congruent planks overlapping in more than half their volume lie in a bounded dilate of one
   another;
2. hence every conflicting `f(T j)` lies in a bounded dilate `K` of the container of `f(T i)`, so
   after pulling back by the (affine, constant-Jacobian) normalisation every conflicting `T j` is a
   `δ`-tube inside a bounded dilate of the `δ`-tube `T i`;
3. a `δ`-tube inside a bounded dilate of a `δ`-tube has direction within `O(δ)` of it, so all
   conflicting tubes lie in a *single* direction cap;
4. `Kakeya.position_count_le_of_bad_directionClass'` bounds the number of pairwise-ED `δ`-tubes in
   one direction cap contained in `K` by `C · M` with `volume K ≤ M · δ ^ (n - 1)`; for a
   tube-shaped `K` the normalising factor `M` is absolute, so the degree is `O(1)`.

Step 4 is the reason the loss is an absolute constant rather than a power of `δ`: the generic count
`Kakeya.card_le_of_ED_subset` multiplies the position count by a factor `δ ^ (-(n-1))` of direction
caps, which is exactly what is *not* needed here, all conflicting tubes being nearly parallel.
Steps 1--3 are new geometry and are not attempted in this file.
-/

@[expose] public section

open MeasureTheory
-- Both conflict relations below are `Finset.filter`s over an arbitrary index type.
set_option linter.style.openClassical false
open scoped Classical

noncomputable section

namespace Kakeya

/-- **Greedy independent set for a bounded-degree conflict relation.**

If a symmetric relation `Adj` has degree at most `d` on `s`, then `s` contains a conflict-free
subfamily of at least `s.card / (d + 1)` elements.

The proof is the standard greedy argument: repeatedly take a surviving index, keep it, and delete
it together with its at most `d` neighbours.  No structure on `ι` is used, so the lemma applies to
any family — tubes, planks, or abstract indices. -/
theorem exists_conflictFree_subset {ι : Type*} (s : Finset ι)
    (Adj : ι → ι → Prop) (hsymm : ∀ i j, Adj i j → Adj j i)
    {d : ℕ} (hdeg : ∀ i ∈ s, ({j ∈ s | Adj i j} : Finset ι).card ≤ d) :
    ∃ t ⊆ s, (t : Set ι).Pairwise (fun i j => ¬ Adj i j) ∧ s.card ≤ (d + 1) * t.card := by
  -- The degree bound is threaded through the induction explicitly: every strict subset inherits it.
  let deg : Finset ι → Prop := fun u => ∀ j ∈ u, ({k ∈ u | Adj j k} : Finset ι).card ≤ d
  let p : Finset ι → Prop := fun u =>
    ∃ t ⊆ u, (t : Set ι).Pairwise (fun i j => ¬ Adj i j) ∧ u.card ≤ (d + 1) * t.card
  have main : ∀ u : Finset ι, deg u → p u := by
    intro u
    refine Finset.strongInductionOn u ?_
    intro s ih hdeg_s
    by_cases hs : s = ∅
    · subst hs
      exact ⟨∅, by simp, by simp [Set.Pairwise], by simp⟩
    · rcases (Finset.nonempty_iff_ne_empty.mpr hs) with ⟨i, his⟩
      let N : Finset ι := s.filter fun j => Adj i j
      let s' : Finset ι := s \ (insert i N)
      have hss' : s' ⊆ s := by
        intro x hx
        exact (Finset.mem_sdiff.mp hx).1
      have hi_notin_s' : i ∉ s' := by
        intro hi'
        exact Finset.notMem_sdiff_of_mem_right (Finset.mem_insert_self i N) hi'
      have hs'_ne_s : s' ≠ s := by
        intro h
        exact hi_notin_s' (h ▸ his)
      have hss'p : s' ⊂ s :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hss', hs'_ne_s⟩
      have hdeg' : deg s' := by
        intro j hjs'
        have hju : j ∈ s := hss' hjs'
        have hsub : ({k ∈ s' | Adj j k} : Finset ι) ⊆ {k ∈ s | Adj j k} := by
          intro k hk
          rw [Finset.mem_filter] at hk ⊢
          exact ⟨hss' hk.1, hk.2⟩
        exact (Finset.card_le_card hsub).trans (hdeg_s j hju)
      rcases ih s' hss'p hdeg' with ⟨t', ht's', hp', hc'⟩
      let t : Finset ι := insert i t'
      refine ⟨t, ?_, ?_, ?_⟩
      · intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hxt'
        · exact his
        · exact hss' (ht's' hxt')
      · -- (t : Set ι).Pairwise (fun i j => ¬ Adj i j)
        rw [Finset.coe_insert]
        refine Set.Pairwise.insert hp' ?_
        intro j hj _hij
        have hjs' : j ∈ s' := ht's' hj
        have hjs : j ∈ s := hss' hjs'
        have hj_notin_N : j ∉ N := by
          exact fun hjN => Finset.notMem_sdiff_of_mem_right (Finset.mem_insert_of_mem hjN) hjs'
        have hAdj_ij : ¬ Adj i j := by
          intro hAdjij
          exact hj_notin_N (Finset.mem_filter.mpr ⟨hjs, hAdjij⟩)
        exact ⟨hAdj_ij, fun hji => hAdj_ij (hsymm j i hji)⟩
      · -- s.card ≤ (d + 1) * t.card
        have hNcard : N.card ≤ d := hdeg_s i his
        have hNi : (insert i N).card ≤ d + 1 :=
          (Finset.card_insert_le i N).trans (Nat.add_le_add_right hNcard 1)
        have hi_notin_t' : i ∉ t' := fun hi't' => hi_notin_s' (ht's' hi't')
        have htcard : t.card = t'.card + 1 := Finset.card_insert_of_notMem hi_notin_t'
        rw [htcard]
        calc
          s.card ≤ s'.card + (insert i N).card :=
            Finset.card_le_card_sdiff_add_card (s := s) (t := insert i N)
          _ ≤ (d + 1) * t'.card + (d + 1) := Nat.add_le_add hc' hNi
          _ = (d + 1) * (t'.card + 1) := by rw [Nat.mul_succ]
  exact main s hdeg

/-- **The ED conflict degree.**

The number of members of `s` whose body fails to be essentially distinct from `U i`.  This is the
single numerical quantity the geometric half of the argument has to bound; naming it lets a
downstream module state its bound without repeating the `Finset.filter` expression.

Note that `i` itself is counted whenever `i ∈ s` and `U i` has positive finite measure, so a bound
`edConflictDegree s U i ≤ d` implicitly allows `d ≥ 1`. -/
def edConflictDegree {ι : Type*} {E : Type*} [MeasureSpace E]
    (s : Finset ι) (U : ι → Set E) (i : ι) : ℕ :=
  ({j ∈ s | ¬ _root_.IsEssentiallyDistinct (U i) (U j)} : Finset ι).card

/-- **Extraction of an essentially distinct subfamily.**

The specialisation of `Kakeya.exists_conflictFree_subset` to the conflict relation
"`U i` and `U j` are *not* essentially distinct".  The hypothesis `hdeg` is the geometric input:
each member conflicts with at most `d` others.

This is the statement GWZ Proposition 6.6(B) consumes for its inner normalised plank family, with
`U i := (P i).carrier`.  Nothing here assumes essential distinctness of the enlarged bodies; it is
*produced*, on a subfamily, at the cost of the factor `d + 1`. -/
theorem exists_essentiallyDistinct_subset {ι : Type*}
    {E : Type*} [MeasureSpace E] (s : Finset ι) (U : ι → Set E)
    {d : ℕ}
    (hdeg : ∀ i ∈ s,
      ({j ∈ s | ¬ _root_.IsEssentiallyDistinct (U i) (U j)} : Finset ι).card ≤ d) :
    ∃ t ⊆ s, (t : Set ι).Pairwise (fun i j => _root_.IsEssentiallyDistinct (U i) (U j)) ∧
      s.card ≤ (d + 1) * t.card := by
  rcases Kakeya.exists_conflictFree_subset s
      (fun i j => ¬ _root_.IsEssentiallyDistinct (U i) (U j))
      (by intro i j hij h; exact hij (_root_.isEssentiallyDistinct_symm h)) (d := d)
      (by
        intro i hi
        convert hdeg i hi using 1
        congr 1
        apply Finset.ext
        intro j
        simp) with
    ⟨t, ht_sub, hpair, hcard⟩
  refine ⟨t, ht_sub, ?_, hcard⟩
  intro i hi j hj hij
  exact not_not.mp (hpair hi hj hij)

end Kakeya

end

end
