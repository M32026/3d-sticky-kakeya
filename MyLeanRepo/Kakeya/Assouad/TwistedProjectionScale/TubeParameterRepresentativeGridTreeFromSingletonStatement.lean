import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterRepresentativeGridTreeStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterRepresentativeTerminalSingletonStatement

/-!
# Assemble the representative parameter grid tree from terminal singletons

All nonterminal tree properties are the public floor-grid lemmas already
proved for arbitrary finite parameter sets.  The only additional input is
terminal singleton cardinality for the representative set.
-/

namespace Kakeya.Assouad

/-- Assemble the full representative grid tree from terminal singleton cells. -/
def TubeParameterRepresentativeGridTreeFromSingletonStatement : Prop :=
  TubeParameterRepresentativeTerminalSingletonStatement →
    TubeParameterRepresentativeGridTreeStatement

end Kakeya.Assouad
