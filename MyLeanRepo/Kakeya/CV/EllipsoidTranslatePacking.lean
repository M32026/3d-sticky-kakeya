import MyLeanRepo.Kakeya.CV.Targets.EllipsoidTranslatePacking.Assembly

/-!
# Volume-efficient packing by ellipsoid translates

Constructs the finite translate index sets used before applying the
many-bisections estimate.
-/

namespace Kakeya.CV

theorem ellipsoid_translate_packing :
    EllipsoidTranslatePackingStatement := by
  refine' ⟨64, by norm_num, _⟩
  intro A η hη hcontain
  rcases ellipsoid_translate_packing_main A η hη hcontain with ⟨n, z, h1, h2, h3, h4⟩
  refine' ⟨n, z, h1, h2, _⟩
  constructor
  · simpa [mul_comm] using h3
  · simpa [mul_comm] using h4

end Kakeya.CV
