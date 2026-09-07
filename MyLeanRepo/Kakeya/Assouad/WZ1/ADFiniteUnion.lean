import MyLeanRepo.Kakeya.Assouad.WZ1.IntervalADHelpers
import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Finite union closure for one-dimensional AD control

A finite union of `IsADSet1` sets is itself `IsADSet1` with a constant
multiplied by the number of pieces. This is the elementary covering-number
union bound used to patch local grain estimates into slab-wide control.
-/

namespace Kakeya.Assouad

open Metric Set

/-- A finite union of `IsADSet1` sets is `IsADSet1` with constant `card * C`.

Requires `s.Nonempty` so that `card * C ≥ 1`. -/
lemma IsADSet1_finite_union
    {ι : Type*} {s : Finset ι} {E : ι → Set ℝ}
    {δ α : ℝ} {C : ENNReal}
    (hs_nonempty : s.Nonempty)
    (h : ∀ i ∈ s, IsADSet1 (E i) δ α C)
    (hbounded : (⋃ i ∈ s, E i) ⊆ Set.Icc (-4 : ℝ) 4) :
    IsADSet1 (⋃ i ∈ s, E i) δ α ((s.card : ENNReal) * C) := by
  classical
  have hcard_pos : 0 < s.card := Finset.Nonempty.card_pos hs_nonempty
  rcases hs_nonempty with ⟨i0, hi0⟩
  rcases h i0 hi0 with ⟨hδ, hα, hα_one, hC_one, _, _⟩
  have hcard_one : (1 : ENNReal) ≤ (s.card : ENNReal) := by
    exact_mod_cast
      (show 1 ≤ s.card from Nat.one_le_iff_ne_zero.mpr hcard_pos.ne')
  have hC_target : (1 : ENNReal) ≤ (s.card : ENNReal) * C := by
    calc
      (1 : ENNReal) ≤ (s.card : ENNReal) := hcard_one
      _ ≤ (s.card : ENNReal) * C := by
        exact le_mul_of_one_le_right' hC_one
  refine ⟨hδ, hα, hα_one, hC_target, hbounded, ?_⟩
  intro rho hrho hdelta_rho hrho_one x r hrho_r hr_one
  let epsilon : NNReal := ⟨rho, hrho⟩
  let pieces : ι → Set ℝ := fun i => E i ∩ closedBall x r
  have h_union_inter :
      (⋃ i ∈ s, E i) ∩ closedBall x r =
        ⋃ i ∈ s, pieces i := by
    ext y
    simp [pieces, Set.mem_inter_iff]
    <;> tauto
  rw [h_union_inter]
  have h_pieces : ∀ i ∈ s,
      (externalCoveringNumber epsilon (pieces i) : ENNReal) ≤
        C * Kakeya.realRpowENN (r / rho) α := by
    intro i hi
    rcases h i hi with ⟨_, _, _, _, _, hcover⟩
    exact
      hcover rho hrho hdelta_rho hrho_one
        x r hrho_r hr_one
  have h_main :
      (externalCoveringNumber epsilon
          (⋃ i ∈ s, pieces i) : ENNReal) ≤
        (s.card : ENNReal) *
          (C * Kakeya.realRpowENN (r / rho) α) :=
    externalCoveringNumber_biUnion_le_card h_pieces
  simpa [mul_assoc] using h_main

/-- Union of two `IsADSet1` sets with the same constant. -/
lemma IsADSet1_union
    {E1 E2 : Set ℝ} {δ α : ℝ} {C : ENNReal}
    (h1 : IsADSet1 E1 δ α C)
    (h2 : IsADSet1 E2 δ α C)
    (hbounded : E1 ∪ E2 ⊆ Set.Icc (-4 : ℝ) 4) :
    IsADSet1 (E1 ∪ E2) δ α (2 * C) := by
  classical
  let indices : Finset Bool := {true, false}
  let pieces : Bool → Set ℝ := fun b => if b then E1 else E2
  have hindices : indices.Nonempty := ⟨true, by simp [indices]⟩
  have h_union : (⋃ i ∈ indices, pieces i) = E1 ∪ E2 := by
    ext y
    simp [indices, pieces, Finset.mem_insert, Finset.mem_singleton]
    <;> tauto
  have hpieces :
      ∀ i ∈ indices, IsADSet1 (pieces i) δ α C := by
    intro i hi
    fin_cases i <;> simp [pieces, h1, h2] <;> tauto
  have hbounded' :
      (⋃ i ∈ indices, pieces i) ⊆
        Set.Icc (-4 : ℝ) 4 := by
    rw [h_union]
    exact hbounded
  have h_main :=
    IsADSet1_finite_union hindices hpieces hbounded'
  have hcard : (indices.card : ENNReal) = 2 := by
    simp [indices]
  simpa [h_union, hcard] using h_main

end Kakeya.Assouad
