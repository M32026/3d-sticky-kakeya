import MyLeanRepo.Kakeya.CV.MultilinearKakeya.DeltaTubeScaling
import MyLeanRepo.Kakeya.CV.MultilinearKakeya.ShadingRestriction
import MyLeanRepo.Kakeya.CV.PolynomialVisibilityComplete
import MyLeanRepo.Kakeya.CV.Targets.PreliminaryReduction
import MyLeanRepo.Kakeya.CV.Targets.VisibilityDegreeBound
import MyLeanRepo.Kakeya.CV.Targets.VisibilityDirectionalBound

/-!
# Conditional assembly of the WZ1 multilinear Kakeya input

This module records that the two explicit open bridges are the only remaining
CV obligations before the exact shaded theorem consumed by WZ1 is available.
-/

namespace Kakeya.CV

/--
The completed CV infrastructure, together with the Sections 2--4 assembly and
the geometric scaling bridge, yields the exact shaded delta-tube inequality.
-/
theorem multilinear_kakeya_three_of_bridges
    (hApplication :
      PolynomialVisibilityToUnitScaleMultilinearKakeyaStatement)
    (hScaling : DeltaTubeMultilinearKakeyaScalingStatement) :
    MultilinearKakeyaThreeStatement := by
  have hUnitScale : UnitScaleMultilinearKakeyaStatement :=
    hApplication polynomial_visibility_complete
      (by
        exact concrete_mollified_surface generic_polynomial_regularity
          polynomial_cylinder_estimate squarefree_singularSet_null
          coefficientSurfaceFunctional_aeMeasurable
          mollified_surface_continuity)
      (by
        exact concrete_mollified_visibility
          (concrete_mollified_surface generic_polynomial_regularity
            polynomial_cylinder_estimate squarefree_singularSet_null
            coefficientSurfaceFunctional_aeMeasurable
            mollified_surface_continuity))
      polynomial_cylinder_estimate
      visibility_directional_surface_bound
      (visibility_degree_bound polynomial_cylinder_estimate
        visibility_directional_surface_bound)
      multilinear_kakeya_preliminary_reduction
  exact multilinear_kakeya_shading_restriction
    (hScaling hUnitScale)

/--
After the geometric scaling bridge is closed, the CV Sections 2--4
application is the sole remaining input for the exact WZ1 theorem.
-/
theorem multilinear_kakeya_three_of_application
    (hApplication :
      PolynomialVisibilityToUnitScaleMultilinearKakeyaStatement) :
    MultilinearKakeyaThreeStatement :=
  multilinear_kakeya_three_of_bridges hApplication
    deltaTube_multilinear_kakeya_scaling

end Kakeya.CV
