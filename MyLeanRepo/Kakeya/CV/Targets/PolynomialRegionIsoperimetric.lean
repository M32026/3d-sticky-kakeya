import MyLeanRepo.Kakeya.CV.PolynomialRegionIsoperimetricFromGeneral

/-!
# Polynomial-region isoperimetric inequality

CV Appendix, specialized to the three-dimensional polynomial sign regions
used in the bisecting-ball argument.
-/

namespace Kakeya.CV

theorem polynomial_region_isoperimetric :
    PolynomialRegionIsoperimetricStatement :=
  polynomial_region_isoperimetric_from_general

end Kakeya.CV
