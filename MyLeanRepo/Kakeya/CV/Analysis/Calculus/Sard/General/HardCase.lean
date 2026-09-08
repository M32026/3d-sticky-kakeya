/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.Defs
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.DerivativeStratification
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.StratumImage
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Int.Star
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard.General

open MeasureTheory Module
open scoped ContDiff

lemma hC {m n : ℕ} (f : E m → E n) :
    ∀ j : ℕ, flatStratum f (j + 1) ⊆ flatStratum f j := by
  intro j x hx
  simp only [flatStratum, Set.mem_setOf_eq] at *
  intro ℓ hℓ
  have hℓ' : 1 ≤ ℓ ∧ ℓ ≤ j + 1 := ⟨hℓ.1, by linarith⟩
  exact hx ℓ hℓ'

lemma h3_main {m n : ℕ} (f : E m → E n) (k : ℕ) :
    flatStratum f 1 ⊆ (⋃ j : ℕ, (flatStratum f j \ flatStratum f (j + 1))) ∪ flatStratum f k := by
  intro x hx
  by_cases h : (∃ j : ℕ, x ∈ flatStratum f j ∧ x ∉ flatStratum f (j + 1))
  ·
    have h4 : x ∈ (⋃ j : ℕ, (flatStratum f j \ flatStratum f (j + 1))) := by
      rcases h with ⟨j, hj1, hj2⟩
      exact Set.mem_iUnion.mpr ⟨j, ⟨hj1, hj2⟩⟩
    exact Set.mem_union_left _ h4
  ·
    have h' : ∀ j : ℕ, x ∈ flatStratum f j → x ∈ flatStratum f (j + 1) := by
      simpa [not_exists] using h
    have h_all : ∀ j : ℕ, x ∈ flatStratum f j := by
      intro j
      induction j with
      | zero =>
        simp only [flatStratum, Set.mem_setOf_eq]
        intro ℓ hℓ
        linarith
      | succ j ih =>
        exact h' j ih
    have h5 : x ∈ flatStratum f k := h_all k
    exact Set.mem_union_right _ h5

/-- Lemma 17 (Hard case step: 0 < n < m).
    Given the induction hypothesis (Sard holds in all dimensions < m),
    prove Sard for dimension m with 0 < n < m.

    Decompose the critical set:
    Crit = C⁺ ∪ C₁ where C⁺ has 0 < rank, C₁ has Df = 0
    C₁ = ⋃_j (C_j \ C_{j+1}) ∪ C_k  (k = m-n+1)
    Each piece has null image, so countable union of null is null. -/
theorem hard_case_sard {m n : ℕ} (hnm : 0 < n ∧ n < m)
    (f : E m → E n)
    (h_pos_rank : volume (f '' {x | 0 < fderivRank f x ∧ fderivRank f x < n}) = 0)
    (h_strata : ∀ j : ℕ, j ≥ 1 →
      volume (f '' (((flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x}))) = 0)
    (h_flat : let k := m - n + 2; volume (f '' flatStratum f k) = 0) :
    volume (f '' {x | IsCriticalPoint f x}) = 0 := by
  set A : Set (E m) := {x | 0 < fderivRank f x ∧ fderivRank f x < n} with hA_def
  set B : Set (E m) := {x | fderivRank f x = 0} with hB_def
  set k : ℕ := m - n + 2 with hk_def
  have h1 : {x | IsCriticalPoint f x} = A ∪ B := by
    ext x
    simp only [hA_def, hB_def, Set.mem_setOf_eq, Set.mem_union]
    constructor
    ·
      intro hx
      have h11 : fderivRank f x < m := hx.1
      have h12 : fderivRank f x < n := hx.2
      by_cases h : 0 < fderivRank f x
      · left
        exact ⟨h, h12⟩
      · right
        omega
    ·
      rintro (h | h)
      ·
        have h21 : 0 < fderivRank f x := h.1
        have h22 : fderivRank f x < n := h.2
        have h23 : fderivRank f x < m := by linarith [hnm.2]
        exact ⟨h23, h22⟩
      ·
        have h21 : fderivRank f x = 0 := h
        have h22 : fderivRank f x < m := by
          omega
        have h23 : fderivRank f x < n := by
          omega
        exact ⟨h22, h23⟩
  have h_image_union : f '' {x | IsCriticalPoint f x} = (f '' A) ∪ (f '' B) := by
    rw [h1]
    rw [Set.image_union]
  rw [h_image_union]
  have hB_eq_flat1 : B = flatStratum f 1 := by
    ext x
    simp only [hB_def, Set.mem_setOf_eq]
    exact h5_aux f x
  have h_flat1_subset_crit : flatStratum f 1 ⊆ {x | IsCriticalPoint f x} := by
    intro x hx
    have h_rank0 : fderivRank f x = 0 := (h5_aux f x).mpr hx
    exact ⟨by linarith [hnm.2], by linarith [hnm.1]⟩
  have h_j_ge_1_eq : ∀ j : ℕ, j ≥ 1 →
    (flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x} = flatStratum f j \ flatStratum f (j + 1) := by
    intro j hj
    have h_sub : flatStratum f j ⊆ flatStratum f 1 := by
      have h_chain : ∀ i, flatStratum f (i + 1) ⊆ flatStratum f i := hC f
      induction' hj with j hj ih
      · simp
      · exact Set.Subset.trans (h_chain j) ih
    have h_sub2 : flatStratum f j ⊆ {x | IsCriticalPoint f x} :=
      Set.Subset.trans h_sub h_flat1_subset_crit
    apply Set.inter_eq_left.mpr
    exact Set.Subset.trans (show flatStratum f j \ flatStratum f (j + 1) ⊆ flatStratum f j from by simp) h_sub2
  have h3 : B ⊆ (⋃ j : ℕ, ((flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x})) ∪ flatStratum f k := by
    rw [hB_eq_flat1]
    have h_main : flatStratum f 1 ⊆ (⋃ j : ℕ, (flatStratum f j \ flatStratum f (j + 1))) ∪ flatStratum f k := h3_main f k
    intro x hx
    rcases h_main hx with (h4 | h5)
    · left
      rcases Set.mem_iUnion.mp h4 with ⟨j, hj1, hj2⟩
      -- Note: j must be ≥ 1 since x ∈ flatStratum f 1
      have hj_ge1 : j ≥ 1 := by
        by_contra h_j0
        have h_j0' : j = 0 := by omega
        subst h_j0'
        exact hj2 (by simpa using hx)
      have h_eq : (flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x} = flatStratum f j \ flatStratum f (j + 1) := h_j_ge_1_eq j hj_ge1
      exact Set.mem_iUnion.mpr ⟨j, h_eq.symm ▸ ⟨hj1, hj2⟩⟩
    · right
      exact h5
  have h3' : (⋃ j : ℕ, (flatStratum f j \ flatStratum f (j + 1))) ∩ B ⊆ (⋃ j : ℕ, ((flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x})) := by
    simp only [Set.iUnion_inter]
    apply Set.iUnion_mono
    intro j
    by_cases h_j0 : j = 0
    · subst h_j0
      simp [hB_eq_flat1]
    · have hj_pos : j ≥ 1 := by omega
      have h_eq : (flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x} = flatStratum f j \ flatStratum f (j + 1) := h_j_ge_1_eq j hj_pos
      rw [h_eq]
      simp
  have h4 : f '' B ⊆ (⋃ j : ℕ, f '' (((flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x}))) ∪ f '' flatStratum f k := by
    have h41 : B ⊆ (⋃ j : ℕ, ((flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x})) ∪ flatStratum f k := h3
    have h : f '' B ⊆ f '' ((⋃ j : ℕ, ((flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x})) ∪ flatStratum f k) := by
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      exact ⟨y, h41 hy, rfl⟩
    rw [Set.image_union] at h
    have h' : f '' (⋃ j : ℕ, ((flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x})) = (⋃ j : ℕ, f '' (((flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x}))) := by
      rw [Set.image_iUnion]
    rw [h'] at h
    exact h
  have h_strata' : ∀ j : ℕ, volume (f '' (((flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x}))) = 0 := by
    intro j
    by_cases hj : j ≥ 1
    · exact h_strata j hj
    · -- j = 0: the set is (flatStratum f 0 \ flatStratum f 1) ∩ {x | IsCriticalPoint f x}
      -- But flatStratum f 0 = univ, so this is {x | x ∉ flatStratum f 1} ∩ {x | IsCriticalPoint f x}
      -- = {x | 0 < fderivRank f x ∧ fderivRank f x < n} = A
      -- And we already have volume (f '' A) = 0 by h_pos_rank
      have h_j0 : j = 0 := by omega
      subst h_j0
      have h_eq : (flatStratum f 0 \ flatStratum f 1) ∩ {x | IsCriticalPoint f x} = A := by
        ext x
        simp only [A, flatStratum, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_inter_iff]
        constructor
        · rintro ⟨h_left, h_right⟩
          have h2 : x ∉ flatStratum f 1 := h_left.2
          have h3 : IsCriticalPoint f x := h_right
          have h4 : 0 < fderivRank f x := by
            by_contra h5
            have h6 : fderivRank f x = 0 := by omega
            have h7 : x ∈ flatStratum f 1 := (h5_aux f x).mp h6
            exact h2 h7
          exact ⟨h4, h3.2⟩
        · rintro ⟨h1, h2⟩
          have h3 : x ∉ flatStratum f 1 := by
            intro h4
            have h5 : fderivRank f x = 0 := (h5_aux f x).mpr h4
            linarith
          have h4 : x ∈ flatStratum f 0 := by
            simp [flatStratum]
            intro ℓ hℓ hℓ0
            omega
          have h5 : IsCriticalPoint f x := ⟨by linarith [hnm.2], h2⟩
          exact ⟨⟨h4, h3⟩, h5⟩
      rw [h_eq]
      exact h_pos_rank
  have h_null1 : volume (⋃ j : ℕ, f '' (((flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x}))) = 0 := by
    exact measure_iUnion_null_iff.mpr h_strata'
  have h_null2 : volume (f '' flatStratum f k) = 0 := h_flat
  have h_null3 : volume ((⋃ j : ℕ, f '' (((flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x}))) ∪ f '' flatStratum f k) = 0 := by
    exact MeasureTheory.measure_union_null h_null1 h_null2
  have h_null4 : volume (f '' B) = 0 := by
    have h : volume (f '' B) ≤ volume ((⋃ j : ℕ, f '' (((flatStratum f j \ flatStratum f (j + 1)) ∩ {x | IsCriticalPoint f x}))) ∪ f '' flatStratum f k) := by
      exact measure_mono h4
    rw [h_null3] at h
    have h' : volume (f '' B) ≤ 0 := h
    have h'' : 0 ≤ volume (f '' B) := zero_le
    exact le_antisymm h' h''
  have h_final : volume ((f '' A) ∪ (f '' B)) = 0 := by
    exact MeasureTheory.measure_union_null h_pos_rank h_null4
  exact h_final

end ForMathlib.Analysis.Calculus.Sard.General
