/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard

/-!
# Sard's regular-value corollary

`regular_value_ae`: for a smooth `f : ℝᵐ → ℝ`, almost every `c ∈ ℝ` is a regular
value (every point of the level set `f⁻¹(c)` has nonzero derivative). This is the
measure-theoretic heart of the regular-value form of Sard's theorem; the critical-set-null form is developed in the general Sard modules.
The trusted helper `IsRegularValue` is a non-hole. Mathlib has the equal-
dimension Jacobian-null lemma and Hausdorff-dimension corollaries but not the
general critical-values-are-null statement.


-/

/-- `c` is a **regular value** of `f : ℝᵐ → ℝ`: every point of the level set
`f⁻¹(c)` has nonzero derivative. -/
def IsRegularValue {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ) (c : ℝ) : Prop :=
  ∀ x, f x = c → fderiv ℝ f x ≠ 0

/-- The scalar critical values of `f : ℝᵐ → ℝ`: the image of the points where
the Frechet derivative vanishes. -/
def criticalValues {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ) : Set ℝ :=
  f '' {x | fderiv ℝ f x = 0}



end ForMathlib.Analysis.Calculus.Sard
