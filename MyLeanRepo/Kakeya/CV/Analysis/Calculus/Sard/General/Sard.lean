module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.Defs
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.RankBounds
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.EasyCaseMLtN
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.EasyCaseMEqN
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.LinearSplitting
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.LocalStraightening
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.RankFormulaFubini
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.PositiveRank
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.DerivativeStratification
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.StratumImage
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.FlatTaylorEstimate
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.HardCase
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.General.Induction
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
# Sard's theorem (Morse 1939 / Sard 1942)

For a smooth map `f : ℝᵐ → ℝⁿ`, the image of the set where the Jacobian
`df(x)` does not have full rank has Lebesgue measure zero.

## Proof Structure (DAG)

```
[Basic definitions]
    Basic.lean
        │
        ├──→ RankBounds.lean
        │       ├──→ EasyCaseMLtN.lean
        │       └──→ EasyCaseMEqN.lean
        │
        ├──→ LinearSplitting.lean
        │       └──→ LocalStraightening.lean
        │               └──→ RankFormulaFubini.lean
        │                       └──→ PositiveRank.lean
        │
        ├──→ DerivativeStratification.lean
        │       └──→ StratumImage.lean
        │
        └──→ FlatTaylorEstimate.lean
                │
PositiveRank.lean ──┬──→ HardCase.lean
StratumImage.lean ──┤
FlatTaylorEstimate.lean ──→ HardCase.lean ──→ Induction.lean ──→ sard
```
-/

open MeasureTheory Module
open scoped ContDiff

/-- **Sard's theorem** (Morse 1939 / Sard 1942). The critical set of a
    smooth map `f : ℝᵐ → ℝⁿ` has zero Lebesgue measure in `ℝⁿ`. -/
theorem criticalValues_null {m n : ℕ} (f : E m → E n) (hf : ContDiff ℝ ∞ f) :
    volume (criticalValues f) = 0 := by
  exact sard_induction m n f hf


end ForMathlib.Analysis.Calculus.Sard.General
