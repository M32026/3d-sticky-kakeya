import MyLeanRepo.Kakeya.CV.MultilinearKakeya.LatticeAssembly

/-!
# Apply polynomial visibility to unit-scale multilinear Kakeya

Conditional assembly of CV Sections 2--4 from the finite lattice-cube
factorization leaf.
-/

namespace Kakeya.CV

theorem polynomial_visibility_to_unitScale_multilinear_kakeya_of_factorization
    (hFactorization : PolynomialVisibilityToLatticeFactorizationStatement) :
    PolynomialVisibilityToUnitScaleMultilinearKakeyaStatement := by
  intro hVisibility hSurface hBody hCylinder hDirectional hDegree hPreliminary
  exact unitScale_multilinear_kakeya_of_lattice_factorization hPreliminary
    (hFactorization hVisibility hSurface hBody hCylinder hDirectional hDegree)

end Kakeya.CV
