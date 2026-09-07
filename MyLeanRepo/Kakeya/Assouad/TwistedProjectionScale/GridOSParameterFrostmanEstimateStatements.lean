import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSFiniteRunStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSFinalConstantAbsorptionStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSReadyStateStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSTerminalClosureStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSTerminationStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridOSInitialStateStatements

/-!
# Final corrected parameter-Frostman Section 7 estimate

This is the direct finite-iteration boundary used by WZ2 Theorem 5.2.
Every input is callable: no conditional theorem is nested without the leaves
needed to instantiate it.

The route proves the explicit indexed parameter-Frostman specialization
actually supplied by WZ Lemma 8.  It does not assert the legacy
TubeWolff-only implication for freely translated unit segments.
-/

namespace Kakeya.Assouad

/--
Assemble the final parameter-Frostman twisted-projection lower bound from the
corrected terminal-grid initial state, finite scheduled iteration, and
terminal arithmetic.
-/
def GridOSParameterFrostmanEstimateStatement : Prop :=
  GridOSBoundedOneScaleInput →
    TubeParameterGridOSInitialStateInput →
      GridOSEffectiveLossScheduleStatement →
        GridOSInitialReadyStateInput →
          GridOSStateDichotomyInput →
            GridOSTransitionReadyStateStatement →
              GridOSFiniteStepScheduleInput →
                GridOSFiniteRunStatement →
                  GridOSTerminationStatement →
                    GridOSTerminalClosureInput →
                      GridOSFinalConstantAbsorptionStatement →
                        TwistedProjectionParameterFrostmanEstimateStatement

end Kakeya.Assouad
