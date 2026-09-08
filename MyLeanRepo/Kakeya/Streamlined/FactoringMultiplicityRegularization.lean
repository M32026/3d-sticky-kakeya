import MyLeanRepo.Kakeya.Streamlined.MultiplicityPigeonhole
import MyLeanRepo.Kakeya.Streamlined.Statements

/-!
# Simultaneous coarse and fiber multiplicity regularization

This is the combinatorial selection core of the Section 5 factoring
proposition.  Fiber multiplicities are regularized first, their dyadic level
is made common across selected parents, and the coarse multiplicity is then
regularized without changing the surviving fiber multiplicities.
-/

noncomputable section

namespace Kakeya.Streamlined

def FactoringMultiplicityRegularizationStatement : Prop :=
  ∀ {fine coarse : BodyFamily},
    ∀ (P : Factoring fine coarse),
    ∀ (Y : Shading fine) (Z : Shading coarse),
      0 < Y.mass →
      (∀ x ∈ Y.union,
        ∀ i, x ∈ Y.carrier i →
          x ∈ Z.carrier (P.parent i)) →
      ∃ R : FactoringRefinement P Y,
        ∃ mcoarse Mcoarse mfiber Mfiber : ℕ,
          R.fineRefinement.RetainsMass
            (((Nat.log 2 fine.card + 1 : ℕ) : ENNReal) ^ 3)⁻¹ ∧
          (∀ j,
            R.coarseShading.carrier j ⊆
              Z.carrier (R.coarseSubfamily.embedding j)) ∧
          1 ≤ mcoarse ∧
          (Mcoarse : ENNReal) ≤ 2 * (mcoarse : ENNReal) ∧
          R.coarseShading.HasConstantMultiplicity mcoarse Mcoarse ∧
          1 ≤ mfiber ∧
          (Mfiber : ENNReal) ≤ 2 * (mfiber : ENNReal) ∧
          (∀ j, R.factoring.FiberHasConstantMultiplicity
            R.fineRefinement.shading j mfiber Mfiber) ∧
          (∀ x ∈ R.fineRefinement.shading.union,
            ∀ i, x ∈ R.fineRefinement.shading.carrier i →
              x ∈ R.coarseShading.carrier (R.factoring.parent i))

end Kakeya.Streamlined
