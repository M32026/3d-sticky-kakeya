import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic

/-!
# Perimeter Definition

Defines the local De Giorgi perimeter, shared between
`SharpGradientBound` and `RelativeIsoperimetric`.

Reuses `TestVectorField` and `divergence` from `Perimeter.Basic`.
-/

open MeasureTheory Metric Set ENNReal
open scoped ContDiff

namespace Geometry.Perimeter

variable {n : ℕ}

/-- **Local De Giorgi perimeter** of `S` in `Ω`.

`P(S; Ω) = sup { |∫_S div Φ| : Φ ∈ C_c^∞(Ω; ℝ^n), ‖Φ‖ ≤ 1 }`. -/
noncomputable def perimeterIn (S : Set (E n)) (Ω : Set (E n)) : ENNReal :=
  iSup fun (Φ : {Φ : TestVectorField // Function.support Φ.toFun ⊆ Ω}) =>
    ENNReal.ofReal |∫ x in S, divergence Φ.val.toFun x|

end Geometry.Perimeter
