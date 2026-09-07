import MyLeanRepo.Kakeya.Cinematic.Section5.ShadingVolume
import MyLeanRepo.Kakeya.Cinematic.Statements

/-!
# Fine carriers inside one coarse-parent neighborhood

An enlarged fine real carrier has the same defining function and midpoint as
its centered coarse enlargement.  If that coarse enlargement is equal or
100-comparable to one fixed coarse parent, then the fine carrier lies in one
fixed real-coordinate neighborhood of the parent.  The neighborhood has
horizontal half-width `C_out` times the coarse interval length and vertical
radius `C_out * Delta`.
-/

open MeasureTheory

namespace Kakeya.Cinematic

def coarseFiberRealNeighborhood
    {Delta T : ℝ} (R : CurvilinearRectangle Delta T)
    (C_out : ℝ) : Set (ℝ × ℝ) :=
  {p |
    |p.1 - R.interval.midpoint| ≤ C_out * R.interval.length ∧
    |p.2 - R.function.extension p.1| ≤ C_out * Delta}

def CoarseFiberCarrierContainmentStatement : Prop :=
  CommonTangentRectangleStatement →
    ComparableRectanglesStatement →
    ∀ K D C_shading : ℝ,
      1 ≤ K →
      1 ≤ D →
      1 ≤ C_shading →
      ∃ C_out : ℝ,
        1 ≤ C_out ∧
        ∀ {family : Set C2Function}
          {I : ParameterInterval}
          {delta t Delta C_R : ℝ},
          IsCinematicFamily family K D →
          I.IsControlled K →
          0 < delta →
          delta ≤ Delta →
          Delta ≤ t →
          1 ≤ C_R →
          ∀
            (U : CurvilinearRectangle
              (C_shading * delta)
              (C_R * t * Delta / delta))
            (enlarged parent :
              CurvilinearRectangle Delta (C_R * t)),
            U.function = enlarged.function →
            U.interval.midpoint = enlarged.interval.midpoint →
            enlarged.function ∈ family →
            parent.function ∈ family →
            enlarged.IsOverCentralQuarterOf I →
            parent.IsOverCentralQuarterOf I →
            (enlarged = parent ∨
              enlarged.AreLambdaComparable parent family 100) →
            U.realCarrier ⊆
                coarseFiberRealNeighborhood parent C_out ∧
              volume (coarseFiberRealNeighborhood parent C_out) =
                ENNReal.ofReal
                  (4 * C_out ^ 2 * Delta * parent.interval.length)

end Kakeya.Cinematic
