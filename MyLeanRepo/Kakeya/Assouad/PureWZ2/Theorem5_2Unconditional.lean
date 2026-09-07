import MyLeanRepo.Kakeya.Assouad.PureWZ2.SubunitPackage
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node02CriticalExtraction
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node03PropSticky
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node04Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichFinalAssembly
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node06LargeSlope
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node07SmallTwistedProjection
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node08Theorem5_2

/-!
# Unconditional pure WZ2 Theorem 5.2

This is the serial paper-level assembly of the already closed Nodes 1--8.
Node 2 performs the contradiction extraction from failure of Theorem 5.2;
Nodes 3--7 produce the critical structural packages; Node 8 contradicts the
small twisted-projection upper bound with the parameter-Frostman lower bound.

The Node-5 input is the direct-rich Proposition 6.4 theorem
`pure_wz2_node05_c2_grains`, so its final family, shading, nearby CWA,
density, volume upper, and grains remain on the same combined-selection
witness.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The normalized pure WZ2 Theorem 5.2 with no external proof inputs. -/
theorem PureWZ2Theorem5_2Unconditional :
    PureWZ2Theorem5_2Statement :=
  pure_wz2_node08_theorem5_2
    pure_wz2_node01_subunit_package
    pure_wz2_node02_critical_extraction
    pure_wz2_node03_prop_sticky
    pure_wz2_node04_grains
    pure_wz2_node05_c2_grains
    pure_wz2_node06_large_slope
    pure_wz2_node07_small_twisted_projection

/-- Snake-case compatibility name for the unconditional endpoint. -/
theorem pure_wz2_theorem5_2_unconditional :
    PureWZ2Theorem5_2Statement :=
  PureWZ2Theorem5_2Unconditional

end Kakeya.Assouad

end
