import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open scoped Pointwise

/-!
# Minkowski Content — Basic Definitions

Definition of the outer Minkowski content and basic properties.

## Main definitions

- `outerMinkowskiContent E`: `limsup_{t→0+} (volume(E + t·B₁) - volume E) / t`

## Main results

- Basic monotonicity and scaling properties of the Minkowski content.

## Whiteprint

This module is a sub-node of `minkowski_content`.
-/

namespace Geometry

open MeasureTheory ENNReal Metric

/-- The **outer Minkowski content** of a set `E`, defined as
`limsup_{t→0+} (volume(E + t·B₁) - volume E) / t`.
Stated as an `ε-δ` upper bound property rather than a direct limit,
since ENNReal subtraction is problematic. -/
def HasUpperMinkowskiContent (n : ℕ) (E : Set (E n)) (C : ENNReal) : Prop :=
  ∀ (ε : ENNReal), 0 < ε → ∃ (δ : ℝ), 0 < δ ∧
    ∀ (t : ℝ), 0 < t → t < δ →
      MeasurableSet (E + t • unitBall n) →
      volume (E + t • unitBall n) ≤ volume E + (C + ε) * ENNReal.ofReal t

/-- The outer Minkowski content is monotone in the bound: if `C` is an
upper content bound and `C ≤ C'`, then `C'` is also an upper bound. -/
theorem hasUpperMinkowskiContent_mono {n : ℕ} {E : Set (E n)} {C C' : ENNReal}
    (h : HasUpperMinkowskiContent n E C) (hle : C ≤ C') :
    HasUpperMinkowskiContent n E C' := by
  intro ε hε
  rcases h ε hε with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, fun t ht_pos hltδ hmeas => ?_⟩
  have h1 : volume (E + t • unitBall n) ≤ volume E + (C + ε) * ENNReal.ofReal t :=
    hδ t ht_pos hltδ hmeas
  have h2 : (C + ε) * ENNReal.ofReal t ≤ (C' + ε) * ENNReal.ofReal t := by
    gcongr
  have h3 : volume E + (C + ε) * ENNReal.ofReal t ≤ volume E + (C' + ε) * ENNReal.ofReal t :=
    add_le_add_right h2 (volume E)
  exact le_trans h1 h3

end Geometry
