import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.CoefficientSurfaceMeasurability

/-!
# Coefficient-space measurability of directional surface area

This is the remaining analytic leaf for concrete mollification.  The target is
almost-everywhere measurability in coefficient space; it must not be replaced
by a pointwise slab-limit identity for every fixed polynomial.
-/

namespace Kakeya.CV

theorem coefficientSurfaceFunctional_aeMeasurable :
    CoefficientSurfaceFunctionalAEMeasurabilityStatement := by
  exact coefficientSurfaceFunctional_aeMeasurable_proof

end Kakeya.CV
