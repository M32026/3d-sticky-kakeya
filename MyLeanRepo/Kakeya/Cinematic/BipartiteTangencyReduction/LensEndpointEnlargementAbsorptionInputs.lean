import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.LensEndpointLocalization

/-!
# Polynomial absorption of the lens endpoint enlargement

The directional lens leaf localizes endpoints in an `E * sqrt(delta / t)`
enlargement. The robust unit core chooses a polynomial comparability constant
large enough that this enlargement still forces two overlapping lenses to
come from comparable rectangles.
-/

namespace Kakeya.Cinematic

def LensEndpointEnlargementAbsorptionStatement : Prop :=
  ∀ {K tangency C : ℝ},
    1 ≤ K →
    5 ≤ tangency →
    100 ≤ C →
    100000 * K ^ 2 ≤ C →
    let V := 25 * tangency ^ 10 + 2 * tangency + 2
    let E := 12 * K * (V + 1) + Real.sqrt (6 * K * V)
    (2 + 2 * E) ^ 2 ≤ C * Real.rpow tangency C

end Kakeya.Cinematic
