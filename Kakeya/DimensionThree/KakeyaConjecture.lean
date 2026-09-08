/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.IsBesicovitch
public import Kakeya.DimensionThree.KakeyaEstimate
public import Kakeya.IsBesicovitch.Assembly
public import Kakeya.IsBesicovitch.HausdorffDim
public import Kakeya.IsBesicovitch.PartsAB
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
In ℝ^3, every Besicovitch set has Hausdorff dimension 3.
-/

@[expose] public section

open scoped ENNReal NNReal MeasureTheory Topology Pointwise

/--
The Katz-Tao reduction `KX(3,3) ⇒ KH(3,3)`, specialised to `n = p = 3`: the shaded Kakeya estimate
`KakeyaEstimate 3 β η` implies `dimH S ≥ 3` for every Besicovitch set `S ⊂ ℝ³`.
-/
theorem dimH_ge_three_of_kakeyaEstimate
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3)))
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : IsBesicovitch S) :
    (3 : ℝ≥0∞) ≤ dimH S := by
  by_contra h_lt
  obtain ⟨q, hq_pos, hq_lt_three, hq_dimS⟩ :=
    Kakeya.IsBesicovitch.exists_real_between_dimH_and_three S (not_le.mp h_lt)
  have hτ_pos : 0 < (3 - q) / 2 := by linarith
  obtain ⟨η, hη_pos, hKE⟩ := KakeyaEstimateDimensionThree_pos hSFE _ hτ_pos
  have h_cover : ∀ K₀ : ℕ,
      ∃ (ι : Type) (x : ι → EuclideanSpace ℝ (Fin 3)) (r : ι → ℝ),
        (∀ i, 0 < r i ∧ r i ≤ (1 / 2 : ℝ) ^ K₀) ∧
        S ⊆ ⋃ i, Metric.closedBall (x i) (r i) ∧
        ∑' i, (r i) ^ q ≤ 1 ∧
        Summable (fun i => (r i) ^ q) :=
    fun K₀ => Kakeya.IsBesicovitch.exists_qcover_of_dimH_lt S hq_pos hq_dimS K₀
  exact Kakeya.IsBesicovitch.false_of_qcover_kakeyaEstimate S hS hq_pos hq_lt_three hη_pos hKE
    h_cover

theorem KakeyaDimensionThree_of_stickyFrostmanEstimate
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3))) : KakeyaSetConjecture 3 := by
  intro S hS
  have h_le : dimH S ≤ (3 : ℝ≥0∞) := by
    calc dimH S
        ≤ dimH (Set.univ : Set (EuclideanSpace ℝ (Fin 3))) := dimH_mono (Set.subset_univ _)
      _ = (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ≥0∞) :=
          Real.dimH_univ_eq_finrank _
      _ = (3 : ℝ≥0∞) := by simp
  have h_ge : (3 : ℝ≥0∞) ≤ dimH S := dimH_ge_three_of_kakeyaEstimate hSFE S hS
  exact le_antisymm h_le h_ge
