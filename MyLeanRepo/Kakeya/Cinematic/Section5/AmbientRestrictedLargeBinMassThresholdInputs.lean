import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedLargeBinRefinementInputs

/-!
# Cubic mass threshold for a large fixed ambient bin

The global Katz--Tao bound gives `mu ≤ C_KT / delta`.  After reserving one
linear ambient-cardinality factor for bounded-overlap summation, the explicit
local target therefore dominates a cubic power of the transported vertical
scale once one fully displayed small-scale inequality holds.
-/

namespace Kakeya.Cinematic

def AmbientRestrictedLargeBinMassThresholdStatement : Prop :=
  ∀ (delta deltaVert epsilon mu logLoss D C_KT scale : ℝ)
    (total : ENNReal),
    0 < delta →
    0 < deltaVert →
    0 < mu →
    0 < logLoss →
    0 < D →
    0 < C_KT →
    0 < scale →
    deltaVert = scale * delta →
    mu ≤ C_KT / delta →
    logLoss * D ^ 3 *
          Real.rpow C_KT (5 / 2 : ℝ) *
          scale ^ 3 *
          Real.rpow delta (1 / 2 + epsilon) ≤
      1 →
    ENNReal.ofReal
          ((Real.rpow delta (-epsilon) *
              Real.rpow mu (-3 / 2 : ℝ)) /
            (logLoss * (D ^ 3 * (C_KT / delta)))) <
        total →
    ENNReal.ofReal (Real.rpow deltaVert 3) < total

end Kakeya.Cinematic
