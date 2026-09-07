import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Selected-layer mass cancellation

PYZ Lemma 43 gives every selected shading mass in one dyadic interval
`[Lambda, 2 * Lambda)`.  The coarse-parent measure bound contributes
`Lambda⁻¹`, and the `1/4`--`3/4` interpolation therefore contributes
`Lambda⁻¹/4`.  Multiplying the selected-cardinality estimate by the retained
layer mass restores one copy of `Lambda`; the remaining `Lambda^(3/4)` is
bounded by the geometric fine-rectangle area.
-/

namespace Kakeya.Cinematic

def SelectedLayerMassCancellationStatement : Prop :=
  ∀ coefficient parentArea fineArea layerMass : ℝ,
    0 ≤ coefficient →
    0 ≤ parentArea →
    0 ≤ fineArea →
    0 < layerMass →
    layerMass ≤ fineArea →
    coefficient *
        Real.rpow (parentArea / layerMass) (1 / 4 : ℝ) *
        layerMass ≤
      coefficient *
        Real.rpow parentArea (1 / 4 : ℝ) *
        Real.rpow fineArea (3 / 4 : ℝ)

end Kakeya.Cinematic
