import MyLeanRepo.Kakeya.CV.ConcreteMollifiedSurface.LocalIntegrability

/-!
# Concrete mollified polynomial surface area

Combines coefficient-space regularity, the cylinder estimate, and convolution
continuity to instantiate the paper's mollified directional surface area.
-/

namespace Kakeya.CV

open MeasureTheory

theorem concrete_mollified_surface
    (hGeneric : GenericPolynomialRegularityStatement)
    (hCylinder : PolynomialCylinderEstimateStatement)
    (hSingular : SquarefreeSingularSetNullStatement)
    (hMeasurable : CoefficientSurfaceFunctionalAEMeasurabilityStatement)
    (hContinuity : MollifiedSurfaceContinuityStatement) :
    ConcreteMollifiedSurfaceStatement := by
  intro k P U c ε hU_meas hU hε
  have h_local : ∀ u : Point 3,
      LocallyIntegrable (coefficientSurfaceFunctional P u U) volume := by
    intro u
    exact coefficientSurfaceFunctional_locallyIntegrable hU hGeneric hCylinder hSingular
      (hMeasurable k P U c hU_meas hU u)
  refine ⟨h_local, ?_⟩
  intro u
  exact hContinuity P.dim ε (coefficientSurfaceFunctional P u U) hε (h_local u)

end Kakeya.CV
