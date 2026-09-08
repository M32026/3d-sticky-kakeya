/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.Defs
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

lemma round1_h_main {m n : ℕ} (f : E m → E n) (x : E m) :
    fderivRank f x ≤ m ∧ fderivRank f x ≤ n := by
  let g : (E m) →ₗ[ℝ] (E n) := (fderiv ℝ f x).toLinearMap
  let p : Submodule ℝ (E n) := LinearMap.range g
  have h1 : fderivRank f x = finrank ℝ p := by
    rfl
  have h2 : finrank ℝ p ≤ finrank ℝ (E m) := by
    exact LinearMap.finrank_range_le g
  have h3 : finrank ℝ (E m) = m := by
    simp [E]
  have h4 : finrank ℝ p ≤ finrank ℝ (E n) := by
    exact Submodule.finrank_le (p)
  have h5 : finrank ℝ (E n) = n := by
    simp [E]
  constructor
  ·
    rw [h1]
    linarith
  ·
    rw [h1]
    linarith

/-- Lemma 1: The rank of the fderiv is always at most min(m, n).
    In particular, if n < m then rank < m is automatic. -/
theorem fderivRank_le_min {m n : ℕ} (f : E m → E n) (x : E m) :
    fderivRank f x ≤ min m n := by
  have h_main : fderivRank f x ≤ m ∧ fderivRank f x ≤ n := round1_h_main f x
  have h1 : fderivRank f x ≤ m := h_main.1
  have h2 : fderivRank f x ≤ n := h_main.2
  exact le_min h1 h2

/-- Lemma 2: For n < m, the critical point condition simplifies to
    `fderivRank f x < n` (since rank < m is automatic). -/
theorem isCriticalPoint_iff_rank_lt_n {m n : ℕ} (hnm : n < m)
    (f : E m → E n) (x : E m) :
    IsCriticalPoint f x ↔ fderivRank f x < n := by
  constructor
  ·
    intro h
    exact h.2
  ·
    intro h
    have h1 : fderivRank f x < n := h
    have h2 : fderivRank f x < m := by
      linarith
    exact ⟨h2, h1⟩

end ForMathlib.Analysis.Calculus.Sard.General
