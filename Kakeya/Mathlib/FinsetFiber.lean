/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Card

/-!
# Fibrewise cardinality bounds

Cardinality bounds obtained by classifying the elements of a `Finset` and bounding each fibre
of the classification separately. This is the counting step of the bush bound
`Kakeya.bushCount_exists`, where the classes are the cells of a `δ`-net of the unit sphere.
-/

@[expose] public section

namespace Finset

/-- If every element of `s` is assigned a class in `Θ` and every fibre has at most `N`
elements, then `s` has at most `Θ.card * N` elements. -/
lemma card_le_mul_of_fiber_card_le {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (Θ : Finset κ)
    (cls : ι → κ) (hcls : ∀ i ∈ s, cls i ∈ Θ) (N : ℕ)
    (hN : ∀ w ∈ Θ, (s.filter fun i ↦ cls i = w).card ≤ N) :
    s.card ≤ Θ.card * N := by
  have hMapsTo : (s : Set ι).MapsTo cls (Θ : Set κ) := by
    intro i hi
    simpa using hcls i hi
  have hcard_eq : s.card = ∑ w ∈ Θ, (s.filter fun i ↦ cls i = w).card := by
    simpa using Finset.card_eq_sum_card_fiberwise hMapsTo
  have hsum : ∑ w ∈ Θ, (s.filter fun i ↦ cls i = w).card ≤ Θ.card • N :=
    Finset.sum_le_card_nsmul Θ (fun w => (s.filter fun i ↦ cls i = w).card) N hN
  calc
    s.card = ∑ w ∈ Θ, (s.filter fun i ↦ cls i = w).card := hcard_eq
    _ ≤ Θ.card • N := hsum
    _ = Θ.card * N := by simp

end Finset
