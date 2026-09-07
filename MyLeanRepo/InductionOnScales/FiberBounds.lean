module

public import MyLeanRepo.InductionOnScales.UniformFibers
public import MyLeanRepo.InductionOnScales.Proposition2Optimized
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Fiber Bounds for Coarse Tubes

Helper lemmas about fiber sizes (number of fine tubes geometrically
contained in a coarse tube).

## Main result

- `coarse_tubes_positive_fibers`: every coarse tube selected by the coarse
  phase contains at least one fine tube, using the popularity lower bound.

This is the prerequisite for `select_uniform_fibers`.

## Whiteprint node
Helper for CoarsePhase uniform-fiber step.
-/

attribute [local instance] Classical.propDecidable

noncomputable section

namespace InductionOnScales

/-- Every coarse tube selected by coarse_phase_data contains at least one fine
tube from config.tubes.

Proof: `h_popularity` gives `H ≤ ∑_{p ∈ P} countInCoarse(tfOpt p, U)`.
Since `H ≥ 1`, some `p` has `countInCoarse > 0`, meaning some `T ∈ tfOpt p`
has `coarseAnc hnm T = U`. By `coarseAnc_contains`, `T.toSet ⊆ U.toSet`.
Since `tfOpt p ⊆ config.tubes`, `T ∈ config.tubes`, so `fiberSize ≥ 1`. -/
lemma coarse_tubes_positive_fibers
    {n m : ℕ} (hnm : m ≤ n)
    {s C₁ : ℝ} {M : ℕ}
    (config : NiceConfiguration n s C₁ M)
    (P : Finset (DyadicSquare n))
    (tfOpt : DyadicSquare n → Finset (DyadicTube n))
    (H : ℝ) (hH : 1 ≤ H)
    (coarseTubes : Finset (DyadicTube m))
    (h_popularity : ∀ U ∈ coarseTubes,
      H ≤ ∑ p ∈ P, (countInCoarse hnm (tfOpt p) U : ℝ))
    (h_tfOpt_sub : ∀ p ∈ P, tfOpt p ⊆ config.tubes) :
    ∀ U ∈ coarseTubes, 0 < fiberSize hnm config.tubes U := by
  intro U hU
  have h_sum_pos : (0 : ℝ) < ∑ p ∈ P, (countInCoarse hnm (tfOpt p) U : ℝ) := by
    have h : H ≤ ∑ p ∈ P, (countInCoarse hnm (tfOpt p) U : ℝ) := h_popularity U hU
    have h' : (0 : ℝ) < H := by linarith
    exact lt_of_lt_of_le h' h
  have h_exists : ∃ (p : DyadicSquare n), p ∈ P ∧ 0 < countInCoarse hnm (tfOpt p) U := by
    by_contra h
    push Not at h
    have h_all_zero : ∀ p ∈ P, (countInCoarse hnm (tfOpt p) U : ℝ) = 0 := by
      intro p hp
      have h' : countInCoarse hnm (tfOpt p) U ≤ 0 := h p hp
      have h'' : countInCoarse hnm (tfOpt p) U = 0 := by omega
      exact_mod_cast h''
    have h_sum_zero : (∑ p ∈ P, (countInCoarse hnm (tfOpt p) U : ℝ)) = 0 := by
      rw [Finset.sum_congr rfl h_all_zero] <;> simp
    rw [h_sum_zero] at h_sum_pos
    <;> linarith
  rcases h_exists with ⟨p, hp, h_count_pos⟩
  have h_fiber_nonempty : ((tfOpt p).filter (fun T => coarseAnc hnm T = U)).Nonempty := by
    simpa [countInCoarse, Finset.card_pos] using h_count_pos
  rcases h_fiber_nonempty with ⟨T, hT_in_filter⟩
  have hT_in : T ∈ tfOpt p := (Finset.mem_filter.mp hT_in_filter).1
  have hAnc_eq : coarseAnc hnm T = U := (Finset.mem_filter.mp hT_in_filter).2
  have h_contain : T.toSet ⊆ U.toSet := by
    have h1 : T.toSet ⊆ (coarseAnc hnm T).toSet := coarseAnc_contains hnm T
    rw [hAnc_eq] at h1
    exact h1
  have hT_in_config : T ∈ config.tubes := h_tfOpt_sub p hp hT_in
  have h_in_fiber : T ∈ (config.tubes.filter (fun T' => T'.toSet ⊆ U.toSet)) := by
    rw [Finset.mem_filter]
    exact ⟨hT_in_config, h_contain⟩
  have h_card_pos : 0 < (config.tubes.filter (fun T' => T'.toSet ⊆ U.toSet)).card :=
    Finset.card_pos.mpr ⟨T, h_in_fiber⟩
  simpa [fiberSize] using h_card_pos

end InductionOnScales
