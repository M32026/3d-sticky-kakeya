import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalFinalAssembly

/-!
# Pure WZ2 Node 6: large slope

The actual fixed-lambda half-offset terminal construction proves the frozen
paper-facing statement using the certified fixed-scale Proposition 6.2
construction.
-/

namespace Kakeya.Assouad

theorem pure_wz2_node06_large_slope :
    PureWZ2LargeSlopeStatement :=
  pureWZ2_direct_halfOffset_large_slope

end Kakeya.Assouad
