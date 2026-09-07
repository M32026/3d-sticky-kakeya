module

public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.Pigeonhole
public import MyLeanRepo.InductionOnScales.IncidenceLemma
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Uniform Fiber Selection (OS form70)

Selects a subset of coarse tubes whose fiber sizes (number of contained
fine tubes) lie in a dyadic band `[NΔ, 2*NΔ)`.

This is the missing form70 construction from OS Proposition 5.1:
- Partition coarse tubes by fiber size into dyadic bands
- Select one band containing at least `1 / (log N + 2)` fraction
- Output uniform fibers and cardinality bound

## Main results

- `select_uniform_fibers`: select coarse tubes with uniform fiber sizes
- `fibers_disjoint`: geometric fibers are pairwise disjoint
- `fiber_sum_le_total`: sum of fiber sizes ≤ total fine tubes
- `form80_bound`: |fineTubes| ≥ |coarseTubes'| * NΔ
- `form71_bound`: |TQ_local| ≤ MΔ * 2 * NΔ

## Whiteprint node
`uniform_fibers` under `InductionOnScales/CoarsePhase/`.
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace InductionOnScales

/-- Number of fine tubes geometrically contained in a coarse tube. -/
def fiberSize {n m : ℕ} (hnm : m ≤ n)
    (fineTubes : Finset (DyadicTube n)) (U : DyadicTube m) : ℕ :=
  (fineTubes.filter (fun T => T.toSet ⊆ U.toSet)).card

/-- Geometric fibers are pairwise disjoint: a fine tube can be contained in
at most one coarse tube. -/
lemma fibers_disjoint {n m : ℕ} (hnm : m ≤ n)
    (fineTubes : Finset (DyadicTube n))
    {U1 U2 : DyadicTube m} (h_ne : U1 ≠ U2) :
    Disjoint (fineTubes.filter (fun T => T.toSet ⊆ U1.toSet))
      (fineTubes.filter (fun T => T.toSet ⊆ U2.toSet)) := by
  rw [Finset.disjoint_left]
  intro T hT1 hT2
  have h1 : T.toSet ⊆ U1.toSet := (Finset.mem_filter.mp hT1).2
  have h2 : T.toSet ⊆ U2.toSet := (Finset.mem_filter.mp hT2).2
  have h_eq : U1 = U2 := unique_containing_coarse_tube hnm T U1 U2 h1 h2
  exact h_ne h_eq

/-- Sum of fiber sizes over any subset of coarse tubes is at most the
total number of fine tubes, because fibers are pairwise disjoint. -/
lemma fiber_sum_le_total {n m : ℕ} (hnm : m ≤ n)
    (fineTubes : Finset (DyadicTube n))
    (coarseSubset : Finset (DyadicTube m)) :
    ∑ U ∈ coarseSubset, (fiberSize hnm fineTubes U) ≤ fineTubes.card := by
  let fiber := fun U : DyadicTube m => fineTubes.filter (fun T => T.toSet ⊆ U.toSet)
  have h_disj : (coarseSubset : Set (DyadicTube m)).PairwiseDisjoint fiber := by
    intro U1 _ U2 _ h_ne
    exact fibers_disjoint hnm fineTubes h_ne
  have h_union : (coarseSubset.biUnion fiber) ⊆ fineTubes := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨U, _, hxU⟩
    exact (Finset.mem_filter.mp hxU).1
  have h_sum : ∑ U ∈ coarseSubset, (fiber U).card = (coarseSubset.biUnion fiber).card := by
    rw [Finset.card_biUnion h_disj]
  have h_main : ∑ U ∈ coarseSubset, (fiber U).card ≤ fineTubes.card := by
    rw [h_sum]
    exact Finset.card_le_card h_union
  have h_eq : ∑ U ∈ coarseSubset, (fiberSize hnm fineTubes U) = ∑ U ∈ coarseSubset, (fiber U).card := by
    apply Finset.sum_congr rfl
    intro U _
    rfl
  rw [h_eq]
  exact h_main

/-- Select a subset of coarse tubes with uniform fiber sizes in [NΔ, 2*NΔ).

This is OS form70: dyadic band selection on fiber sizes.

Given `h_pos` that every coarse tube contains at least one fine tube,
applies `exists_dyadic_size_subfamily` to find a band `[NΔ, 2*NΔ)`
containing at least `1 / (log |fineTubes| + 2)` fraction of coarse tubes.

The cardinality bound includes a factor of 2 from integer division:
`|coarseTubes| ≤ 2 * (log |fineTubes| + 2) * |coarseTubes'|`.
This polylog factor is absorbed by K. -/
lemma select_uniform_fibers {n m : ℕ} (hnm : m ≤ n)
    (fineTubes : Finset (DyadicTube n))
    (coarseTubes : Finset (DyadicTube m))
    (h_coarse_nonempty : coarseTubes.Nonempty)
    (h_pos : ∀ U ∈ coarseTubes, 0 < fiberSize hnm fineTubes U) :
    ∃ (NΔ : ℕ) (coarseTubes' : Finset (DyadicTube m)),
      coarseTubes' ⊆ coarseTubes ∧
      coarseTubes'.Nonempty ∧
      (∀ U ∈ coarseTubes', NΔ ≤ fiberSize hnm fineTubes U) ∧
      (∀ U ∈ coarseTubes', fiberSize hnm fineTubes U < 2 * NΔ) ∧
      (coarseTubes.card : ℝ) ≤
        2 * ((Nat.log 2 fineTubes.card + 2 : ℕ) : ℝ) * (coarseTubes'.card : ℝ) := by
  let pop : DyadicTube m → ℕ := fun U => fiberSize hnm fineTubes U
  have h_bound : ∀ U ∈ coarseTubes, pop U ≤ fineTubes.card := by
    intro U _
    simpa [pop, fiberSize] using Finset.card_filter_le fineTubes _
  have hN : 0 < fineTubes.card := by
    rcases h_coarse_nonempty with ⟨U, hU⟩
    have h : 0 < pop U := h_pos U hU
    have h2 : pop U ≤ fineTubes.card := h_bound U hU
    exact lt_of_lt_of_le h h2
  rcases exists_dyadic_size_subfamily coarseTubes pop hN h_bound h_pos
    with ⟨NΔ, coarseTubes', h_sub, h_band, h_card⟩
  let L : ℕ := numDyadicLevels fineTubes.card
  have hL_pos : 0 < L := by
    simp [L, numDyadicLevels]
    <;> omega
  by_cases h_ne : coarseTubes'.Nonempty
  · -- Standard case: selected subset is nonempty
    have h1 : coarseTubes.card / L ≤ coarseTubes'.card := h_card
    have h2 : coarseTubes.card < L * (coarseTubes'.card + 1) := by
      have h3 : coarseTubes.card = L * (coarseTubes.card / L) + coarseTubes.card % L :=
        Eq.symm (Nat.div_add_mod coarseTubes.card L)
      have h4 : coarseTubes.card % L < L := Nat.mod_lt _ hL_pos
      have h5 : L * (coarseTubes.card / L) ≤ L * coarseTubes'.card := by
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have h6 : L * (coarseTubes.card / L) + coarseTubes.card % L < L * (coarseTubes'.card + 1) := by
        calc
          L * (coarseTubes.card / L) + coarseTubes.card % L
            ≤ L * (coarseTubes.card / L) + (L - 1) := by
              have h7 : coarseTubes.card % L ≤ L - 1 := by
                omega
              omega
          _ < L * (coarseTubes'.card + 1) := by
            have h8 : L * (coarseTubes.card / L) + (L - 1) < L * (coarseTubes'.card + 1) := by
              rw [mul_add, mul_one]
              omega
            exact h8
      rw [h3]
      exact h6
    have h6 : coarseTubes'.card + 1 ≤ 2 * coarseTubes'.card := by
      have h7 : 0 < coarseTubes'.card := h_ne.card_pos
      omega
    have h_card_bound : (coarseTubes.card : ℝ) ≤
        2 * (L : ℝ) * (coarseTubes'.card : ℝ) := by
      have h8 : (coarseTubes.card : ℝ) < (L : ℝ) * ((coarseTubes'.card : ℝ) + 1) := by
        exact_mod_cast h2
      have h9 : (L : ℝ) * ((coarseTubes'.card : ℝ) + 1) ≤
          2 * (L : ℝ) * (coarseTubes'.card : ℝ) := by
        have h10 : (coarseTubes'.card : ℝ) + 1 ≤ 2 * (coarseTubes'.card : ℝ) := by exact_mod_cast h6
        calc
          (L : ℝ) * ((coarseTubes'.card : ℝ) + 1)
            ≤ (L : ℝ) * (2 * (coarseTubes'.card : ℝ)) := by gcongr
          _ = 2 * (L : ℝ) * (coarseTubes'.card : ℝ) := by ring
      linarith
    exact ⟨NΔ, coarseTubes', h_sub, h_ne,
      (fun U hU => (h_band U hU).1),
      (fun U hU => (h_band U hU).2),
      h_card_bound⟩
  · -- Degenerate case: selected subset is empty
    -- This means coarseTubes.card < L. Pick any single coarse tube.
    have h_empty' : coarseTubes' = ∅ := by simpa using h_ne
    have h_small : coarseTubes.card < L := by
      by_contra h
      have h' : L ≤ coarseTubes.card := by linarith
      have h_div_pos : 0 < coarseTubes.card / L := Nat.div_pos h' hL_pos
      have h10 : coarseTubes'.card = 0 := by
        rw [h_empty'] <;> simp
      have h11 : coarseTubes'.card ≥ coarseTubes.card / L := h_card
      rw [h10] at h11
      linarith
    rcases h_coarse_nonempty with ⟨U0, hU0⟩
    let NΔ' := fiberSize hnm fineTubes U0
    let coarseTubes'' : Finset (DyadicTube m) := {U0}
    have h_card1 : coarseTubes''.card = 1 := by simp [coarseTubes'']
    have h_card_bound' : (coarseTubes.card : ℝ) ≤
        2 * (L : ℝ) * (coarseTubes''.card : ℝ) := by
      rw [h_card1]
      have h : (coarseTubes.card : ℝ) < (L : ℝ) := by exact_mod_cast h_small
      have h2 : (coarseTubes.card : ℝ) ≤ 2 * (L : ℝ) := by linarith
      simpa using h2
    exact ⟨NΔ', coarseTubes'',
      by simp [coarseTubes''] <;> exact hU0,
      by simp [coarseTubes''] <;> exact hU0,
      (fun U hU => by
        have h_eq : U = U0 := by simpa [coarseTubes''] using hU
        rw [h_eq] <;> rfl),
      (fun U hU => by
        have h_eq : U = U0 := by simpa [coarseTubes''] using hU
        rw [h_eq]
        have hNpos : 0 < NΔ' := h_pos U0 hU0
        linarith),
      h_card_bound'⟩

/-- form80: total fine tubes ≥ selected coarse tubes × NΔ.

Follows from disjoint fibers each of size ≥ NΔ. -/
lemma form80_bound {n m : ℕ} (hnm : m ≤ n)
    (fineTubes : Finset (DyadicTube n))
    (coarseTubes' : Finset (DyadicTube m))
    (NΔ : ℕ)
    (h_lower : ∀ U ∈ coarseTubes', NΔ ≤ fiberSize hnm fineTubes U) :
    (fineTubes.card : ℝ) ≥ (coarseTubes'.card : ℝ) * (NΔ : ℝ) := by
  have h_sum : ∑ U ∈ coarseTubes', (fiberSize hnm fineTubes U) ≤ fineTubes.card :=
    fiber_sum_le_total hnm fineTubes coarseTubes'
  have h_lower_sum : (coarseTubes'.card : ℝ) * (NΔ : ℝ) ≤
      ∑ U ∈ coarseTubes', (fiberSize hnm fineTubes U : ℝ) := by
    have h : ∑ U ∈ coarseTubes', (NΔ : ℝ) ≤ ∑ U ∈ coarseTubes', (fiberSize hnm fineTubes U : ℝ) := by
      apply Finset.sum_le_sum
      intro U hU
      exact_mod_cast h_lower U hU
    simpa [Finset.sum_const] using h
  have h_main : (coarseTubes'.card : ℝ) * (NΔ : ℝ) ≤ (fineTubes.card : ℝ) := by
    calc
      (coarseTubes'.card : ℝ) * (NΔ : ℝ)
        ≤ ∑ U ∈ coarseTubes', (fiberSize hnm fineTubes U : ℝ) := h_lower_sum
      _ ≤ (fineTubes.card : ℝ) := by exact_mod_cast h_sum
  exact h_main

/-- form71: local tubes ≤ MΔ × 2 × NΔ.

For each coarse square Q, TQ_local is the union of fibers over coarse tubes
in the local family. Since fibers are disjoint and each has size < 2*NΔ,
the total is ≤ MΔ * 2 * NΔ. -/
lemma form71_bound {n m : ℕ} (hnm : m ≤ n)
    (fineTubes : Finset (DyadicTube n))
    (localCoarseTubes : Finset (DyadicTube m))
    (MΔ : ℕ) (hMΔ : localCoarseTubes.card ≤ MΔ)
    (NΔ : ℕ)
    (h_upper : ∀ U ∈ localCoarseTubes, fiberSize hnm fineTubes U < 2 * NΔ) :
    (localCoarseTubes.biUnion
      (fun U => fineTubes.filter (fun T => T.toSet ⊆ U.toSet))).card
      ≤ MΔ * 2 * NΔ := by
  let fiber := fun U : DyadicTube m => fineTubes.filter (fun T => T.toSet ⊆ U.toSet)
  let TQ_local := localCoarseTubes.biUnion fiber
  have h_disj : (localCoarseTubes : Set (DyadicTube m)).PairwiseDisjoint fiber := by
    intro U1 _ U2 _ h_ne
    exact fibers_disjoint hnm fineTubes h_ne
  have h_card : TQ_local.card = ∑ U ∈ localCoarseTubes, (fiber U).card := by
    rw [Finset.card_biUnion h_disj]
  rw [h_card]
  by_cases h_nonempty : localCoarseTubes.Nonempty
  · have h_sum_lt : ∑ U ∈ localCoarseTubes, (fiber U).card <
        localCoarseTubes.card * (2 * NΔ) := by
      have h1 : ∀ U ∈ localCoarseTubes, (fiber U).card < 2 * NΔ := by
        intro U hU
        simpa [fiber, fiberSize] using h_upper U hU
      have h2 : ∑ U ∈ localCoarseTubes, (fiber U).card <
          ∑ U ∈ localCoarseTubes, (2 * NΔ) := by
        apply Finset.sum_lt_sum_of_nonempty h_nonempty
        intro U hU
        exact h1 U hU
      simpa [Finset.sum_const] using h2
    have h3 : ∑ U ∈ localCoarseTubes, (fiber U).card ≤ MΔ * 2 * NΔ := by
      have h4 : ∑ U ∈ localCoarseTubes, (fiber U).card < localCoarseTubes.card * (2 * NΔ) := h_sum_lt
      have h5 : localCoarseTubes.card * (2 * NΔ) ≤ MΔ * (2 * NΔ) :=
        mul_le_mul_of_nonneg_right hMΔ (by positivity)
      have h6 : ∑ U ∈ localCoarseTubes, (fiber U).card < MΔ * (2 * NΔ) := lt_of_lt_of_le h4 h5
      have h7 : MΔ * (2 * NΔ) = MΔ * 2 * NΔ := by ring
      rw [h7] at h6
      exact le_of_lt h6
    exact h3
  · have h_empty : localCoarseTubes = ∅ := by simpa using h_nonempty
    rw [h_empty]
    <;> simp

end InductionOnScales
