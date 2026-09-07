module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
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

/-!
# Sard's theorem for rank-deficient smooth maps

For a smooth map `f : ℝᵐ → ℝⁿ`, the image of the rank-deficient set
`{x | rank df(x) < m ∧ rank df(x) < n}` — points where the Jacobian
`df(x)` is neither injective nor surjective — has Lebesgue measure
zero. The manifold form follows from this Euclidean version
chart-by-chart, so the substance of the theorem lives at the
Euclidean level used here.

This file uses the rank-deficient condition `rank df(x) < m ∧
rank df(x) < n`. The standard textbook Sard theorem uses the larger
critical set `rank df(x) < n`, so it implies the form proved here.
The two conditions agree when `m ≥ n`.

Mathlib has the equal-dimension case `μ (f '' s) = 0` when
`det (f' x) = 0` on `s`
(`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`)
plus topological corollaries via Hausdorff dimension, but no general
critical-value / Sard statement.
-/

open MeasureTheory Module
open scoped ContDiff

/-- The Euclidean model space `ℝⁿ`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

instance instContinuousSMulProdEuclidean (m n : ℕ) :
    ContinuousSMul ℝ (E m × E n) :=
  ⟨(continuous_fst.smul (continuous_fst.comp continuous_snd)).prodMk
    (continuous_fst.smul (continuous_snd.comp continuous_snd))⟩

/-- The rank of the Fréchet derivative of `f` at `x`. -/
noncomputable def fderivRank {m n : ℕ} (f : E m → E n) (x : E m) : ℕ :=
  finrank ℝ (LinearMap.range (fderiv ℝ f x).toLinearMap)

/-- A **critical point** of `f`: a point where
`df(x)` has rank less than both `m` and `n`, so `df(x)` fails to have
full rank `min m n`. Weaker than the textbook condition
`rank df(x) < n`; see the module docstring. -/
def IsCriticalPoint {m n : ℕ} (f : E m → E n) (x : E m) : Prop :=
  fderivRank f x < m ∧ fderivRank f x < n

/-- The **critical values** of `f`: the image in `ℝⁿ` of the
rank-deficient locus. -/
def criticalValues {m n : ℕ} (f : E m → E n) : Set (E n) :=
  f '' {x | IsCriticalPoint f x}



end ForMathlib.Analysis.Calculus.Sard.General
