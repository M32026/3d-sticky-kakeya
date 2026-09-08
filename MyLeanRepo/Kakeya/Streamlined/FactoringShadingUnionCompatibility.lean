import MyLeanRepo.Kakeya.Streamlined.Statements

/-!
# Union compatibility for a factoring shading

This isolates the point-set containment used by the Section 5 factoring
multiplicity product.
-/

noncomputable section

namespace Kakeya.Streamlined

def FactoringShadingUnionCompatibilityStatement : Prop :=
  ∀ {fine coarse : BodyFamily},
    ∀ (P : Factoring fine coarse),
    ∀ (Y : Shading fine) (Z : Shading coarse),
      (∀ x ∈ Y.union,
        ∀ i, x ∈ Y.carrier i →
          x ∈ Z.carrier (P.parent i)) →
      Y.union ⊆ Z.union

end Kakeya.Streamlined
