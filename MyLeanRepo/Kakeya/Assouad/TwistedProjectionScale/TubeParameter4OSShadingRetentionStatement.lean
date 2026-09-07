import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameter4OSFiberLiftStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameter4FiberMassBoundsStatement

/-!
# Shaded-mass retention under complete-fiber and OS parameter pruning

Once every active tube carries a common shaded-mass floor, cardinality
retention converts directly to shaded-mass retention.  This is the paper's
reason for performing per-tube pruning before the Orponen--Shmerkin
uniformization.

The two finite losses are:

* dyadic regularization of exact four-parameter fibers;
* the local OS branching loss on the distinct parameter image.

No weighted tree theorem and no division by an `ENNReal` mass is needed.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The total natural-number loss in the two cardinality refinements. -/
def tubeParameter4OSCardinalityLoss
    (activeCard base levels : ℕ) : ℕ :=
  (Nat.log 2 activeCard + 1) *
    (2 * (2 * (Nat.log 2 ((base + 1) ^ 4) + 1)) ^ levels)

/--
Complete-fiber regularization followed by OS branching retains shaded mass
once every active tube has a common positive mass floor.

The output is cancellation-free:

`threshold * originalMass ≤ loss * tubeVolume * selectedMass`.
-/
def TubeParameter4OSShadingRetentionStatement : Prop :=
  TubeVolumeScalingStatement →
    ∀ {delta : ℝ},
      0 < delta →
      delta ≤ 1 →
      ∀ family : Kakeya.Streamlined.TubeFamily delta,
        ∀ shading : Kakeya.Streamlined.TubeShading family,
          ∀ threshold : ENNReal,
            HasPerTubeMass shading threshold →
            let active := positiveMassIndices shading
            ∀ regularized :
                TubeParameter4FiberRegularizationData family active,
              ∀ base levels : ℕ,
                ∀ uniform :
                    TubeParameter4OSFiberLiftData
                      regularized base levels,
                  threshold * shading.mass ≤
                    (tubeParameter4OSCardinalityLoss
                        active.card base levels : ENNReal) *
                      Kakeya.deltaTubeVolume delta *
                        (selectedTubeShading
                          shading uniform.selected).mass

end Kakeya.Assouad
