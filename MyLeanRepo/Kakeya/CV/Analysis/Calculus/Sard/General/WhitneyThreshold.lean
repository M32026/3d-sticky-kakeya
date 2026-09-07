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
import Mathlib.RingTheory.WittVector.IsPoly
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

/-- Lemma 15 (Numerical inequality).
    If k = m - n + 1 and 0 < n < m, then k * n ≥ m.
    This is the Whitney smoothness threshold. -/
theorem whiteny_smoothness_threshold (m n : ℕ) (hn_pos : 0 < n) (hnm : n < m) :
    (m - n + 1) * n ≥ m := by
  have h1 : m ≥ n + 1 := by omega
  have h2 : (m - n + 1) * n = (m - n) * n + n := by
    have h3 : m ≥ n := by omega
    zify [h3]
    ring_nf
  rw [h2]
  have h4 : (m - n) * n ≥ m - n := by
    have h5 : n ≥ 1 := by omega
    have h6 : m - n ≥ 0 := by omega
    nlinarith
  omega

end ForMathlib.Analysis.Calculus.Sard.General
