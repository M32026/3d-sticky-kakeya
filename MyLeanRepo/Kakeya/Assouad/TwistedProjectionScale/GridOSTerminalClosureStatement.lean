import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSTelescopingStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SelectedScaleStatements

/-!
# Close a finite corrected grid OS run at the terminal scale

The nonterminal transitions telescope the projection volumes with one factor
`6889` per step.  The final application of the one-scale theorem contributes
the last ratio and a thickened nonempty planar set.  Once its selected radius
reaches `delta ^ (epsilon ^ 2)`, the closed terminal projection theorem gives
the paper exponent before fixed-constant absorption.
-/

namespace Kakeya.Assouad

/--
Combine finite transition telescoping with the terminal one-scale inequality.
-/
def GridOSTerminalClosureInput : Prop :=
  ∀ {delta epsilon : ℝ},
        0 < delta →
        delta < 1 →
        0 < epsilon →
        epsilon < 1 →
        ∀ steps : ℕ,
          ∀ scale : ℕ → ℝ,
            ∀ projectedVolume : ℕ → ENNReal,
              scale 0 = delta →
              (∀ index : ℕ, index ≤ steps → 0 < scale index) →
              (∀ index : ℕ, index < steps →
                Kakeya.realRpowENN
                    (scale index / scale (index + 1)) epsilon *
                  projectedVolume (index + 1) ≤
                    (6889 : ENNReal) * projectedVolume index) →
                ∀ rho : ℝ,
                  0 < rho →
                  Real.rpow delta (epsilon ^ 2) ≤ rho →
                  ∀ X : Set Point2,
                    X.Nonempty →
                    Kakeya.realRpowENN
                        (scale steps / rho) epsilon *
                      MeasureTheory.volume
                        (Metric.cthickening rho X) ≤
                      projectedVolume steps →
                        Kakeya.realRpowENN
                            delta
                            (epsilon +
                              epsilon ^ 2 * (2 - epsilon)) ≤
                          (6889 : ENNReal) ^ steps *
                            projectedVolume 0

/-- Assemble the direct terminal closure from finite telescoping and the terminal theorem. -/
def GridOSTerminalClosureStatement : Prop :=
  GridOSTelescopingStatement →
    SelectedScaleTerminalProjectionStatement →
      GridOSTerminalClosureInput

end Kakeya.Assouad
