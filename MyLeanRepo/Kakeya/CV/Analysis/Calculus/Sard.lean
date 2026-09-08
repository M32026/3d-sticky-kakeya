/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.CriticalImageNull

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

open MeasureTheory
open scoped ContDiff

/-- **Regular value corollary (Sard).** For a smooth `f : ℝᵐ → ℝ`, almost every
`c ∈ ℝ` is a regular value. -/
theorem regular_value_ae {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    ∀ᵐ c ∂(volume : Measure ℝ), IsRegularValue f c := by
  exact regular_value_ae_of_critical_image_null (sard_criticalValues_null f hf)

end ForMathlib.Analysis.Calculus.Sard
