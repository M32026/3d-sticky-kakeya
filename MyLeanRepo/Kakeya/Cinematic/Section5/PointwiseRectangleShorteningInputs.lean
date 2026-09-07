import MyLeanRepo.Kakeya.Cinematic.Section5.FineShadings
import MyLeanRepo.Kakeya.Cinematic.Section5.RectangleShorteningInputs

/-!
# Pointwise rectangle shortening input

This proposition packages midpoint-preserving shortening for a point-indexed
family of fine rectangles. It changes only the common rectangle scale and
retains the point, center, tangent fiber, central containment, and tangency
certificates needed by the Section 5 shading argument.
-/

namespace Kakeya.Cinematic

def PointwiseRectangleShorteningStatement : Prop :=
  RectangleShorteningStatement →
    ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
      {K delta t Delta C_R : ℝ},
      ∀ I : ParameterInterval,
        I.IsControlled K →
        ∀ point : E → UnitPoint × ℝ,
          (∀ p : E, (((point p).1 : ℝ), (point p).2) = p) →
          ∀ center : E → C2Function,
            (∀ p : E, center p ∈ family) →
            ∀ fiber : E → FiniteFunctionFamily,
              (∀ p : E, (fiber p).carrier ⊆ family) →
              ∀ exactScale : E → ℝ,
                0 < delta →
                0 < C_R * t * Delta / delta →
                (∀ p : E, 0 < exactScale p) →
                (∀ p : E,
                  exactScale p ≤ C_R * t * Delta / delta) →
                ∀ rectangle :
                    ∀ p : E,
                      CurvilinearRectangle delta (exactScale p),
                  (∀ p : E,
                    (rectangle p).function = center p) →
                  (∀ p : E,
                    (rectangle p).interval.midpoint = p.1.1) →
                  (∀ p : E,
                    |(rectangle p).interval.midpoint - I.midpoint| ≤
                      I.length / 16) →
                  (∀ p : E, point p ∈ (rectangle p).carrier) →
                  (∀ p : E,
                    (rectangle p).IsOverCentralQuarterOf I) →
                  (∀ p : E, ∀ f ∈ (fiber p).carrier,
                    (rectangle p).IsLambdaTangent f 5) →
                  ∃ data :
                      FineRectangleAssignmentData
                        family E K delta t Delta C_R,
                    data.interval = I ∧
                    (∀ p : E, data.center p = center p) ∧
                    ∀ p : E, data.fiber p = fiber p

end Kakeya.Cinematic
