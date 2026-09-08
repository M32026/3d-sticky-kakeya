/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.Defs
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.PositiveRankLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard.General

open MeasureTheory Module
open scoped ContDiff

lemma h_local_implies_main_goal {m n : ℕ}
    (f : E m → E n)
    (h_local : ∀ (x : E m), x ∈ {x : E m | 0 < fderivRank f x ∧ fderivRank f x < n} →
      ∃ (U : Set (E m)), IsOpen U ∧ x ∈ U ∧ volume (f '' ({x : E m | 0 < fderivRank f x ∧ fderivRank f x < n} ∩ U)) = 0) :
    volume (f '' {x | 0 < fderivRank f x ∧ fderivRank f x < n}) = 0 := by
  let S : Set (E m) := {x | 0 < fderivRank f x ∧ fderivRank f x < n}
  let ι := {x : E m // x ∈ S}
  let U : ι → Set (E m) := fun i : ι => (Classical.choose (h_local i.val i.property))
  let hU_spec : ∀ (i : ι), IsOpen (U i) ∧ i.val ∈ U i ∧ volume (f '' (S ∩ U i)) = 0 :=
    fun i : ι => Classical.choose_spec (h_local i.val i.property)
  have hU_open : ∀ (i : ι), IsOpen (U i) := fun i => (hU_spec i).1
  have hS_lindelof : IsLindelof S := by
    exact IsLindelof.of_coe
  have h_cover : S ⊆ ⋃ (i : ι), U i := by
    intro x hx
    let i : ι := ⟨x, hx⟩
    have h1 : x ∈ U i := (hU_spec i).2.1
    exact Set.mem_iUnion.mpr ⟨i, h1⟩
  rcases IsLindelof.elim_countable_subcover hS_lindelof U hU_open h_cover with ⟨r, hr_count, hr_cover⟩
  have h4 : ∀ (i : ι), i ∈ r → volume (f '' (S ∩ U i)) = 0 := by
    intro i _
    exact (hU_spec i).2.2
  have h6 : volume (⋃ i ∈ r, f '' (S ∩ U i)) = 0 := by
    exact (MeasureTheory.measure_biUnion_null_iff hr_count).mpr h4
  have h7 : f '' S ⊆ ⋃ i ∈ r, f '' (S ∩ U i) := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h_x_in_S : x ∈ S := hx
    have h_x_in_union : x ∈ ⋃ i ∈ r, U i := hr_cover h_x_in_S
    have h_unfold1 : ∃ (i : ι), i ∈ r ∧ x ∈ U i := by
      simpa [Set.mem_iUnion] using h_x_in_union
    rcases h_unfold1 with ⟨i, hi_mem_r, hx_in_Ui⟩
    have h_goal : f x ∈ f '' (S ∩ U i) := by
      exact ⟨x, ⟨hx, hx_in_Ui⟩, rfl⟩
    have h_final : f x ∈ ⋃ i ∈ r, f '' (S ∩ U i) := by
      simpa [Set.mem_iUnion] using ⟨i, hi_mem_r, h_goal⟩
    exact h_final
  exact measure_mono_null h7 h6

/-- Lemma 9 (Positive-rank critical image is null).
    Let C⁺ = {x | 0 < fderivRank f x < n}.
    Then vol_n(f(C⁺)) = 0, assuming the induction hypothesis that
    Sard holds in all smaller source dimensions.

    Proof sketch:
    1. For each p ∈ C⁺ with rank r, use local straightening (Lemma 6).
    2. In straightened coordinates, critical condition rank < n
       becomes rank(D_b G) < n-r in the b-slice.
    3. By induction on m-r, for each fixed a, the b-slice critical image
       has (n-r)-dimensional volume zero.
    4. By Fubini (Lemma 8), the full image has n-dimensional volume zero.
    5. Use Lindelöf property / second countability to cover C⁺ with
       countably many such neighborhoods, then countable union of null is null. -/
theorem positive_rank_critical_null {m n : ℕ} (f : E m → E n)
    (h_local_fact : ∀ (x : E m), x ∈ {x : E m | 0 < fderivRank f x ∧ fderivRank f x < n} →
      ∃ (U : Set (E m)), IsOpen U ∧ x ∈ U ∧
        volume (f '' ({x : E m | 0 < fderivRank f x ∧ fderivRank f x < n} ∩ U)) = 0) :
    volume (f '' {x | 0 < fderivRank f x ∧ fderivRank f x < n}) = 0 :=
  h_local_implies_main_goal f h_local_fact

end ForMathlib.Analysis.Calculus.Sard.General
