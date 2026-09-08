import MyLeanRepo.Kakeya.Streamlined.FactoringShadingUnionCompatibility

/-!
# Union compatibility for a factoring shading
-/

namespace Kakeya.Streamlined

theorem factoring_shading_union_compatibility_main :
    FactoringShadingUnionCompatibilityStatement := by
  intro fine coarse P Y Z h x hx
  have hux : x ∈ Y.union := hx
  rcases hx with ⟨i, hi⟩
  exact ⟨P.parent i, h x hux i hi⟩

end Kakeya.Streamlined
