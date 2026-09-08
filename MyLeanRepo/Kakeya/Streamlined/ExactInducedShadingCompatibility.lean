import MyLeanRepo.Kakeya.Streamlined.FactoringShadingUnionCompatibility.Proof

/-!
# Compatibility of the exact induced shading

The paper's induced coarse shading contains every fine shaded point in its
assigned parent.  This is the pointwise compatibility item used by the
factoring multiplicity argument.
-/

noncomputable section

namespace Kakeya.Streamlined

def ExactInducedShadingCompatibilityStatement : Prop :=
  ∀ {fine coarse : BodyFamily},
    ∀ (P : Factoring fine coarse),
    ∀ (Y : Shading fine) (Z : Shading coarse),
    ∀ r : ℝ,
      P.IsExactInducedShading Y Z r →
      (∀ x ∈ Y.union,
        ∀ i, x ∈ Y.carrier i →
          x ∈ Z.carrier (P.parent i)) ∧
      Y.union ⊆ Z.union

end Kakeya.Streamlined
