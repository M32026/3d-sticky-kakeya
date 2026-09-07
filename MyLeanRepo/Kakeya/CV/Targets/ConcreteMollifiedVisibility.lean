import MyLeanRepo.Kakeya.CV.Targets.ConcreteMollifiedVisibility.MassProperties

/-!
# Concrete mollified visibility body

Instantiates the generic averaged-seminorm package for bounded-degree
polynomial surface area and proves the resulting body is eligible for the
John ellipsoid machinery.

## Whiteprint node: concrete-mollified-visibility
-/

namespace Kakeya.CV

theorem concrete_mollified_visibility
    (hSurface : ConcreteMollifiedSurfaceStatement) :
    ConcreteMollifiedVisibilityStatement :=
  concrete_mollified_visibility_of_mass hSurface

end Kakeya.CV
