import MyLeanRepo.Kakeya.Assouad.Inputs
import MyLeanRepo.Kakeya.Cinematic.Section5.UniformC2ConcreteAssembly

/-!
# Closed PYZ input for WZ2

The PYZ workstream exports the absolute-two-jet-uniform cinematic maximal
estimate.  This module identifies that theorem with WZ2's frozen local
interface without changing quantifier order or constants.
-/

namespace Kakeya.Assouad

theorem pyz_input : PYZInput := by
  simpa only [PYZInput, IsCinematicDeltaSeparated,
    HasCinematicKatzTaoBound,
    Kakeya.Cinematic.WZ2UniformC2Input,
    Kakeya.Cinematic.HasUniformC2Bound,
    Kakeya.Cinematic.FiniteFunctionFamily.IsDeltaSeparated,
    Kakeya.Cinematic.FiniteFunctionFamily.HasKatzTaoBound] using
      Kakeya.Cinematic.wz2_uniformC2_input

end Kakeya.Assouad
