/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
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
import Mathlib.Geometry.Euclidean.Volume.Measure
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
import Mathlib.Tactic.SetNotationForOrder
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard.General

open MeasureTheory Module
open scoped ContDiff

/-- Lemma 3 (Easy case: m < n). If m < n, then for any C¹ map f : E m → E n,
    the image of any set has Hausdorff dimension ≤ m < n, hence n-dimensional
    volume zero. In particular, the critical set has volume zero. -/
theorem sard_m_lt_n {m n : ℕ} (hmn : m < n) (f : E m → E n)
    (hf : ContDiff ℝ 1 f) :
    volume (f '' {x | IsCriticalPoint f x}) = 0 := by
  let s : Set (E n) := f '' {x | IsCriticalPoint f x}
  have h1 : s ⊆ Set.range f := by
    intro y hy
    rcases hy with ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have h2 : dimH (Set.range f) ≤ (m : ENNReal) := by
    have h21 : Module.finrank ℝ (E m) = m := by simp [E]
    have h22 := hf.dimH_range_le
    rw [h21] at h22
    exact h22
  have h3 : dimH s ≤ dimH (Set.range f) := dimH_mono h1
  have h4 : dimH s ≤ (m : ENNReal) := by exact h3.trans h2
  have h51 : (m : ENNReal) < (n : ENNReal) := by exact_mod_cast hmn
  have h5 : dimH s < (n : ENNReal) := by
    calc
      dimH s ≤ (m : ENNReal) := h4
      _ < (n : ENNReal) := h51
  have h6 : (MeasureTheory.Measure.hausdorffMeasure (n : ℝ)) s = 0 :=
    hausdorffMeasure_of_dimH_lt (d := n) h5
  have h71 : (MeasureTheory.Measure.euclideanHausdorffMeasure n : Measure (E n)) s = 0 := by
    rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def n]
    simp [h6]
  have h_eq : (MeasureTheory.Measure.euclideanHausdorffMeasure n : Measure (E n)) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
  have h_final : volume s = 0 := by
    calc
      volume s = (MeasureTheory.Measure.euclideanHausdorffMeasure n : Measure (E n)) s := by rw [h_eq]
      _ = 0 := h71
  exact h_final

end ForMathlib.Analysis.Calculus.Sard.General
