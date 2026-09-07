import MyLeanRepo.Kakeya.CV.AntipodalSignSeparation
import MyLeanRepo.Kakeya.CV.BadSetAtomCardinality
import MyLeanRepo.Kakeya.CV.CenteredHomotheticVolumeComparison
import MyLeanRepo.Kakeya.CV.DyadicPolynomialBadSetDecomposition
import MyLeanRepo.Kakeya.CV.EllipsoidTranslatePacking
import MyLeanRepo.Kakeya.CV.FiniteDyadicPolynomialBadSetDecomposition
import MyLeanRepo.Kakeya.CV.FinitePaletteTranslatePacking
import MyLeanRepo.Kakeya.CV.NormalizedPolynomialSphere
import MyLeanRepo.Kakeya.CV.PolynomialBadSetCover
import MyLeanRepo.Kakeya.CV.PolynomialVisibility
import MyLeanRepo.Kakeya.CV.PrincipalAxesMollifiedDirectionalBudget
import MyLeanRepo.Kakeya.CV.PrincipalAxesMollifiedManyBisections
import MyLeanRepo.Kakeya.CV.PrincipalAxesRepresentation
import MyLeanRepo.Kakeya.CV.SquarefreeSingularSetNull
import MyLeanRepo.Kakeya.CV.StableEllipsoidColouring
import MyLeanRepo.Kakeya.CV.StableEllipsoidPaletteBandFiniteness
import MyLeanRepo.Kakeya.CV.Targets.CoefficientSurfaceFunctionalAEMeasurability
import MyLeanRepo.Kakeya.CV.Targets.ConcreteMollifiedSurface
import MyLeanRepo.Kakeya.CV.Targets.ConcreteMollifiedVisibility
import MyLeanRepo.Kakeya.CV.Targets.ConcreteVisibilityHomotheticContinuity
import MyLeanRepo.Kakeya.CV.Targets.EllipsoidSelectionStability
import MyLeanRepo.Kakeya.CV.Targets.GenericPolynomialRegularity
import MyLeanRepo.Kakeya.CV.Targets.MollifiedSurfaceContinuity
import MyLeanRepo.Kakeya.CV.Targets.PolynomialBadSetAvoidance
import MyLeanRepo.Kakeya.CV.Targets.PolynomialCylinderEstimate
import MyLeanRepo.Kakeya.CV.Targets.PolynomialParameterSpace
import MyLeanRepo.Kakeya.CV.Targets.PolynomialRegionIsoperimetric
import MyLeanRepo.Kakeya.CV.Targets.PrincipalAxesManyBisections
import MyLeanRepo.Kakeya.CV.UniformFiniteBisectionStability
import MyLeanRepo.Kakeya.CV.UnitCubeEllipsoidPacking

/-!
# Complete polynomial visibility theorem

Closes the Carbery--Valdimarsson polynomial visibility statement by assembling
the completed geometric, analytic, topological, and isoperimetric inputs.
-/

namespace Kakeya.CV

theorem polynomial_visibility_complete.{u} :
    PolynomialVisibilityStatement.{u} := by
  have hSurface : ConcreteMollifiedSurfaceStatement :=
    concrete_mollified_surface generic_polynomial_regularity
      polynomial_cylinder_estimate squarefree_singularSet_null
      coefficientSurfaceFunctional_aeMeasurable mollified_surface_continuity
  have hBody : ConcreteMollifiedVisibilityStatement :=
    concrete_mollified_visibility hSurface
  have hContinuity : ConcreteVisibilityHomotheticContinuityStatement :=
    concrete_visibility_homothetic_continuity hSurface hBody
  have hDyadic : DyadicPolynomialBadSetDecompositionStatement :=
    dyadic_polynomial_badSet_decomposition hBody
      stable_finite_colour_ellipsoid_net
  have hFiniteDyadic : FiniteDyadicPolynomialBadSetDecompositionStatement :=
    finite_dyadic_polynomial_badSet_decomposition hBody hDyadic
  have hUnitCubePacking : UnitCubeEllipsoidPackingStatement :=
    unitCube_ellipsoid_translate_packing ellipsoid_translate_packing
  have hPalettePacking : FinitePaletteTranslatePackingStatement :=
    finite_palette_translate_packing hUnitCubePacking
  have hManyBisections : PrincipalAxesManyBisectionsStatement.{0} :=
    principalAxes_many_bisections.{0} polynomial_region_isoperimetric
  have hMollifiedManyBisections :
      PrincipalAxesMollifiedManyBisectionsStatement.{0} :=
    principalAxes_mollified_many_bisections.{0}
  have hAvoidance : PolynomialBadSetAvoidanceConclusion.{u} :=
    polynomial_badSet_avoidance.{u}
      normalized_polynomial_sphere hSurface hBody hContinuity hFiniteDyadic
      stable_ellipsoid_palette_band_finiteness hPalettePacking
      principalAxes_representation uniform_finite_bisections_stable
      hMollifiedManyBisections hManyBisections
      generic_polynomial_regularity squarefree_singularSet_null
      polynomial_cylinder_estimate principalAxes_mollified_directional_budget
      centered_homothetic_volume_comparison ellipsoid_selection_stability
      antipodal_sign_separation badSet_atom_cardinality_bound
      polynomial_bad_set_cover
  exact polynomial_visibility polynomial_parameter_space hAvoidance

end Kakeya.CV
