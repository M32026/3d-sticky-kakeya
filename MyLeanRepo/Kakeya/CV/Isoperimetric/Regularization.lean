import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Regularization Lemma

Given a bounded measurable set `B` with finite `(n-1)`-Hausdorff measure
of its frontier, construct a regular open set `U = interior(closure B)` such that:
1. `U` is open and bounded
2. `volume U = volume B`
3. `μHE[n-1](frontier U) ≤ μHE[n-1](frontier B)`

This removes "slits" and "hairs" that cause Minkowski content bounds to fail.
-/

namespace Geometry

open MeasureTheory ENNReal Metric Set
open scoped MeasureTheory

/-- If `μHE[n-1] s < ⊤` for `n ≥ 1`, then `volume s = 0`.
By the zero-or-top dichotomy for Euclidean Hausdorff measures. -/
lemma volume_eq_zero_of_ehausdorff_lt_top {n : ℕ} (hn : 1 ≤ n)
    {s : Set (E n)} (h : μHE[n - 1] s < ⊤) :
    volume s = 0 := by
  have h1 : n - 1 < n := by omega
  have h2 := MeasureTheory.Measure.euclideanHausdorffMeasure_zero_or_top h1 s
  rcases h2 with (h2 | h2)
  · -- μHE[n] s = 0
    have h3 : (μHE[n] : Measure (E n)) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
    rw [h3] at h2
    exact h2
  · -- μHE[n-1] s = ⊤, contradicts h
    exfalso
    exact h.ne h2

/-- `closure B = B ∪ frontier B`. -/
lemma closure_eq_union_frontier {α : Type*} [TopologicalSpace α] {B : Set α} :
    closure B = B ∪ frontier B := by
  apply Set.Subset.antisymm
  · intro x hx
    by_cases h : x ∈ B
    · exact Or.inl h
    · have h' : x ∈ frontier B := by
        have h1 : x ∈ closure B := hx
        have h2 : x ∉ interior B := by
          intro h3; exact h (interior_subset h3)
        exact ⟨h1, h2⟩
      exact Or.inr h'
  · rintro x (h | h)
    · exact subset_closure h
    · exact h.1

/-- `frontier (closure B) ⊆ frontier B`. -/
lemma frontier_closure_subset {α : Type*} [TopologicalSpace α] {B : Set α} :
    frontier (closure B) ⊆ frontier B := by
  have h1 : frontier (closure B) = closure (closure B) \ interior (closure B) := by rfl
  rw [h1]
  have h2 : closure (closure B) = closure B := by simp
  rw [h2]
  have h3 : interior B ⊆ interior (closure B) := interior_mono subset_closure
  have h4 : closure B \ interior (closure B) ⊆ closure B \ interior B :=
    diff_subset_diff_right h3
  exact h4

/-- `interior (closure B)` is a regular open set:
`interior (closure (interior (closure B))) = interior (closure B)`. -/
lemma interior_closure_regular {α : Type*} [TopologicalSpace α] {B : Set α} :
    interior (closure (interior (closure B))) = interior (closure B) := by
  let U := interior (closure B)
  have h1 : U ⊆ interior (closure U) := by
    have hU_open : IsOpen U := isOpen_interior
    have h_eq : U = interior U := hU_open.interior_eq.symm
    have h_sub : U ⊆ closure U := subset_closure
    have h : interior U ⊆ interior (closure U) := interior_mono h_sub
    rw [←h_eq] at h
    exact h
  have h2 : closure U ⊆ closure B := by
    have h21 : closure U ⊆ closure (closure B) := closure_mono interior_subset
    have h22 : closure (closure B) = closure B := by simp
    rw [h22] at h21
    exact h21
  have h4 : interior (closure U) ⊆ interior (closure B) := interior_mono h2
  exact Set.Subset.antisymm h4 h1

/-- `frontier (interior (closure B)) ⊆ frontier (closure B)`. -/
lemma frontier_interior_closure_subset {α : Type*} [TopologicalSpace α] {B : Set α} :
    frontier (interior (closure B)) ⊆ frontier (closure B) := by
  let U := interior (closure B)
  have hU : interior U = U := by
    simp [U, interior_interior]
  have h1 : closure U ⊆ closure (closure B) := closure_mono interior_subset
  have h2 : closure (closure B) = closure B := by simp
  intro x hx
  have h3 : x ∈ closure U := hx.1
  have h4 : x ∉ interior U := hx.2
  have h5 : x ∉ U := by
    rw [←hU]; exact h4
  have h6 : x ∈ closure (closure B) := h1 h3
  exact ⟨h6, h5⟩

/-- **Regularization lemma.** Given a bounded measurable set `B` with finite
`(n-1)`-Hausdorff measure of its frontier, let `U := interior (closure B)`. Then:
1. `U` is open
2. `U` is bounded
3. `volume U = volume B`
4. `μHE[n-1](frontier U) ≤ μHE[n-1](frontier B)` -/
theorem regularize_open (n : ℕ) (hn : 2 ≤ n)
    (B : Set (E n)) (hB : MeasurableSet B)
    (hBdd : Bornology.IsBounded B)
    (hfin : μHE[n - 1] (frontier B) < ⊤) :
    let U := interior (closure B)
    IsOpen U ∧ Bornology.IsBounded U ∧
    U = interior (closure U) ∧
    volume U = volume B ∧
    μHE[n - 1] (frontier U) ≤ μHE[n - 1] (frontier B) := by
  let U := interior (closure B)
  have hU_open : IsOpen U := isOpen_interior
  have h_closure_bdd : Bornology.IsBounded (closure B) :=
    isBounded_closure_iff.mpr hBdd
  have hU_bdd : Bornology.IsBounded U := by
    have hsub : U ⊆ closure B := interior_subset
    exact Bornology.IsBounded.subset h_closure_bdd hsub
  have h_frontier_B_vol : volume (frontier B) = 0 :=
    volume_eq_zero_of_ehausdorff_lt_top (by linarith) hfin
  have h_frontier_closure_subset : frontier (closure B) ⊆ frontier B :=
    frontier_closure_subset
  have h_frontier_closure_vol : volume (frontier (closure B)) = 0 := by
    have h : volume (frontier (closure B)) ≤ volume (frontier B) :=
      measure_mono h_frontier_closure_subset
    have h' : volume (frontier B) = 0 := h_frontier_B_vol
    rw [h'] at h
    simpa using h
  have h_frontier_U_subset : frontier U ⊆ frontier (closure B) :=
    frontier_interior_closure_subset
  have h_frontier_U_subset_B : frontier U ⊆ frontier B :=
    h_frontier_U_subset.trans h_frontier_closure_subset
  have h_hausdorff_U_le : μHE[n - 1] (frontier U) ≤ μHE[n - 1] (frontier B) :=
    measure_mono h_frontier_U_subset_B
  -- volume (closure B) = volume B
  have h_eq1 : closure B = B ∪ frontier B := closure_eq_union_frontier
  have h_vol_closure_le : volume (closure B) ≤ volume B + volume (frontier B) := by
    rw [h_eq1]
    exact measure_union_le _ _
  have h_vol_closure_eq : volume (closure B) = volume B := by
    have h1 : volume (closure B) ≤ volume B := by
      calc volume (closure B) ≤ volume B + volume (frontier B) := h_vol_closure_le
           _ = volume B + 0 := by rw [h_frontier_B_vol]
           _ = volume B := by simp
    have h2 : volume B ≤ volume (closure B) := measure_mono subset_closure
    exact le_antisymm h1 h2
  -- volume U = volume (closure B)
  have h_eq2 : closure B = U ∪ frontier (closure B) := by
    apply Set.Subset.antisymm
    · intro x hx
      by_cases h : x ∈ U
      · exact Or.inl h
      · have h' : x ∈ frontier (closure B) := by
          have h1 : x ∈ closure B := hx
          have h2 : x ∉ interior (closure B) := h
          exact ⟨by simpa using h1, h2⟩
        exact Or.inr h'
    · rintro x (h | h)
      · exact interior_subset h
      · have h1 : x ∈ closure B := by simpa [closure_closure] using h.1
        exact h1
  have h_vol_U_le : volume (closure B) ≤ volume U + volume (frontier (closure B)) := by
    have h_eq3 : volume (closure B) = volume (U ∪ frontier (closure B)) := by
      congr
      <;> exact h_eq2
    rw [h_eq3]
    simpa using measure_union_le (μ := volume) (s := U) (t := frontier (closure B))
  have h_vol_U_eq_closure : volume U = volume (closure B) := by
    have h1 : volume (closure B) ≤ volume U := by
      calc volume (closure B) ≤ volume U + volume (frontier (closure B)) := h_vol_U_le
           _ = volume U + 0 := by rw [h_frontier_closure_vol]
           _ = volume U := by simp
    have h2 : volume U ≤ volume (closure B) := measure_mono interior_subset
    exact le_antisymm h2 h1
  have h_vol_U_eq_B : volume U = volume B := by
    rw [h_vol_U_eq_closure, h_vol_closure_eq]
  have hU_reg : U = interior (closure U) := by
    have h : interior (closure U) = U := by
      simpa [U] using interior_closure_regular (B := B)
    exact h.symm
  exact ⟨hU_open, hU_bdd, hU_reg, h_vol_U_eq_B, h_hausdorff_U_le⟩

end Geometry
