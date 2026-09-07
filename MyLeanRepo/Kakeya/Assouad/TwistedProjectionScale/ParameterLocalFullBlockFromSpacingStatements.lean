import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalSpacingCandidateStatement

/-!
# Assemble the full local block from spacing and pruning

The hard spacing producer and local Frostman pruning are independent.  This
boundary only synchronizes their thresholds and recovers the historical
`ParameterLocalFullBlockSelectionStatement` consumed downstream.
-/

namespace Kakeya.Assouad

def ParameterLocalFullBlockFromSpacingStatement : Prop :=
  ParameterLocalSpacingCandidateStatement →
    ParameterLocalFrostmanBlockPruningStatement →
      ParameterLocalFullBlockSelectionStatement

end Kakeya.Assouad
