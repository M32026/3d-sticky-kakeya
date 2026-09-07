import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.Targets.ConcreteVisibilityHomotheticContinuity.MainAssembly

/-!
# Homothetic continuity of concrete visibility bodies

Connects coefficient convergence to the Banach--Mazur style convergence needed
by the stable same-colour ellipsoid selection.
-/

namespace Kakeya.CV

theorem concrete_visibility_homothetic_continuity
    (hSurface : ConcreteMollifiedSurfaceStatement)
    (hBody : ConcreteMollifiedVisibilityStatement) :
    ConcreteVisibilityHomotheticContinuityStatement :=
  concrete_visibility_homothetic_continuity_main hSurface hBody

end Kakeya.CV
