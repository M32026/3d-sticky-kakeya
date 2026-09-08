/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.EDDegree
public import Kakeya.Tube.EDUpToMult

/-!
# Weighted essentially distinct extraction for the inner plank family

The cardinality-only extraction `Kakeya.exists_inner_plank_ED_subfamily_of_bounded_conflict_degree`
is too weak for GWZ 6.6(B): fullness is *not* monotone under restriction, so a subfamily with good
cardinality can discard almost all of the shade mass, and then no fullness lower bound survives.

This module replaces it by the weighted extraction.  From a bound `d` on
`Kakeya.edConflictDegree` it produces a single subfamily that retains, both up to the factor
`d + 1`,

* the shade mass `∑ volume (P i).shade`, which is exactly the hypothesis of
  `ShadedBody.fullness'_le_of_subset_of_sum_shade_le` (fullness transfer) and of
  `Kakeya.multiplicity_pigeon_transfer` (multiplicity split);
* the cardinality, which the slab and cardinality clauses of 6.6(B) need.

The `d + 1` loss is *not* free: it is a genuine constant that the consumer must absorb into its
sub-polynomial budget, which is why the small-`δ` threshold of the caller carries a
`d + 1 ≤ δ ^ (-(ηᵢ - η))` clause.

The engine is `Kakeya.IsEDUpToMult.exists_pairwise_subset_with_measure_and_card`; the only work here
is the dictionary between `Kakeya.edConflictDegree` (fixed index first in the essential-distinctness
relation) and `Kakeya.IsEDUpToMult` (fixed index second), which is symmetry of
`IsEssentiallyDistinct`.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace Kakeya

/-- **A bound on the ED conflict degree is exactly `IsEDUpToMult`.**

The two notions filter the same index set; they differ only in the order of the arguments of
`IsEssentiallyDistinct`, which is symmetric. -/
theorem isEDUpToMult_of_edConflictDegree_le
    {ι : Type*} {E : Type*} [MeasureSpace E] (s : Finset ι) (U : ι → Set E) {M : ℕ}
    (hdeg : ∀ i ∈ s, edConflictDegree s U i ≤ M) :
    IsEDUpToMult s U M := by
  classical
  rw [IsEDUpToMult]
  intro i hi
  have hset : (notEssDistinctSet s U (U i)).card = edConflictDegree s U i := by
    unfold notEssDistinctSet edConflictDegree
    congr 1
    exact Finset.filter_congr (fun j _ => by
      constructor
      · intro h
        exact fun h' => h (isEssentiallyDistinct_symm h')
      · intro h
        exact fun h' => h (isEssentiallyDistinct_symm h'))
  calc
    (notEssDistinctSet s U (U i)).card = edConflictDegree s U i := hset
    _ ≤ M := hdeg i hi

/-- **Weighted essentially distinct extraction for a shaded plank family.**

Given a finite family of `a × b × 1` shaded planks whose ED conflict degree is at most `d`, there is
a subfamily that is pairwise essentially distinct and retains both the cardinality and the shade
mass up to the factor `d + 1`.

This is the package GWZ 6.6(B) consumes for its inner normalised plank family.  Nothing is assumed
about essential distinctness of enlarged planks; it is *produced*, on a subfamily, at the stated
cost. -/
theorem exists_inner_plank_ED_subfamily_weighted
    {ι : Type*} {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    (q : Finset ι) (P : ι → ShadedPlank a b hab hb1) {d : ℕ}
    (hdeg : ∀ i ∈ q, edConflictDegree q (fun j => (P j).carrier) i ≤ d) :
    ∃ s ⊆ q,
      (s : Set ι).Pairwise
        (fun i j => _root_.IsEssentiallyDistinct (P i).carrier (P j).carrier) ∧
      q.card ≤ (d + 1) * s.card ∧
      (∑ i ∈ q, volume (P i).shade)
        ≤ ((d : ENNReal) + 1) * ∑ i ∈ s, volume (P i).shade := by
  have hfin : ∀ i : ι, i ∈ q → volume (P i).shade ≠ ⊤ := fun i _ =>
    ne_top_of_le_ne_top (P i).isCompact'.measure_ne_top (measure_mono (P i).shade_subset)
  have hED : IsEDUpToMult q (fun j => (P j).carrier) d :=
    isEDUpToMult_of_edConflictDegree_le q (fun j => (P j).carrier) (M := d) hdeg
  obtain ⟨s, hs, hpair, hmass, hcard⟩ :=
    IsEDUpToMult.exists_pairwise_subset_with_measure_and_card (s := q)
      (V := fun j => (P j).carrier) (M := d) hED (fun i => volume (P i).shade) hfin
  exact ⟨s, hs, hpair, hcard, hmass⟩

end Kakeya

end

end
