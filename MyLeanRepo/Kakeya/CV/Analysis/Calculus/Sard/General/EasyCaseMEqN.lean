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

lemma rank_lt_iff_det_eq_zero {n : ℕ} (L : (E n) →ₗ[ℝ] (E n)) :
    finrank ℝ (LinearMap.range L) < n ↔ LinearMap.det L = 0 := by
  have h1 : Module.finrank ℝ (E n) = n := by simp [E]
  constructor
  ·
    intro h
    by_contra h2
    have h3 : LinearMap.det L ≠ 0 := h2
    have h4 : Function.Surjective L := (LinearMap.equivOfDetNeZero L h3).surjective
    have h5 : LinearMap.range L = ⊤ := by
      simpa [LinearMap.range_eq_top] using h4
    have h6 : finrank ℝ (LinearMap.range L) = Module.finrank ℝ (E n) := by
      rw [h5]
      simp
    have h7 : finrank ℝ (LinearMap.range L) = n := by
      rw [h6, h1]
    linarith
  ·
    intro h
    have h2 : LinearMap.range L < ⊤ := LinearMap.range_lt_top_of_det_eq_zero h
    have h3 : LinearMap.range L ≠ ⊤ := h2.ne
    have h_le : finrank ℝ (LinearMap.range L) ≤ Module.finrank ℝ (E n) := Submodule.finrank_le _
    have h_le2 : finrank ℝ (LinearMap.range L) ≤ n := by
      rw [h1] at h_le
      exact h_le
    by_contra h4
    have h5 : ¬ (finrank ℝ (LinearMap.range L) < n) := h4
    have h6 : finrank ℝ (LinearMap.range L) = n := by omega
    have h7 : finrank ℝ (LinearMap.range L) = Module.finrank ℝ (E n) := by
      rw [h1]
      exact h6
    have h8 : LinearMap.range L = ⊤ := Submodule.eq_top_of_finrank_eq h7
    exact h3 h8

/-- Lemma 4 (Equal dimension case: m = n). Use Mathlib's
    `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`.
    When m = n, det(f' x) = 0 iff rank < m, which is the critical condition. -/
theorem sard_m_eq_n {n : ℕ} (f : E n → E n)
    (hf : ContDiff ℝ 1 f) :
    volume (f '' {x | IsCriticalPoint f x}) = 0 := by
  let s : Set (E n) := {x | IsCriticalPoint f x}
  have h_differentiable : Differentiable ℝ f := hf.differentiable (by norm_num)
  have h_diff : ∀ (x : E n), HasFDerivAt f (fderiv ℝ f x) x := by
    intro x
    exact h_differentiable.differentiableAt.hasFDerivAt
  have h1 : ∀ x ∈ s, HasFDerivWithinAt f (fderiv ℝ f x) s x := by
    intro x hx
    exact (h_diff x).hasFDerivWithinAt
  have h2 : ∀ x ∈ s, (fderiv ℝ f x).det = 0 := by
    intro x hx
    have h_crit : IsCriticalPoint f x := hx
    have h_rank_lt : fderivRank f x < n := h_crit.1
    let L : (E n) →ₗ[ℝ] (E n) := (fderiv ℝ f x).toLinearMap
    have h3 : fderivRank f x = finrank ℝ (LinearMap.range L) := by
      rfl
    have h4 : finrank ℝ (LinearMap.range L) < n := by
      rw [←h3]
      exact h_rank_lt
    have h5 : LinearMap.det L = 0 := (rank_lt_iff_det_eq_zero L).mp h4
    exact h5
  exact MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (volume : MeasureTheory.Measure (E n)) h1 h2

end ForMathlib.Analysis.Calculus.Sard.General
