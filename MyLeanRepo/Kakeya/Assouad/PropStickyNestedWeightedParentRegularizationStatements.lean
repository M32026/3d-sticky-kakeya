import MyLeanRepo.Kakeya.Assouad.PropStickyNestedWeightedLowerRegularizationStatements

/-!
# Weighted regularization for nested parent maps

This is the finite combinatorial form used by the corrected Section 6
preparation.  Unlike simultaneous dyadic degree regularization, it uses the
nesting of the parent fibers.  The total loss is therefore `2 ^ scaleCount`,
with no logarithmic factor per scale.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperNestedWeightedParentRegularizationData
    (indexType : Type)
    [Fintype indexType] [DecidableEq indexType]
    (weight : indexType → ENNReal)
    (scaleCount : ℕ)
    (Parent : Fin scaleCount → Type)
    [∀ coordinate, Fintype (Parent coordinate)]
    [∀ coordinate, DecidableEq (Parent coordinate)]
    (parent : ∀ coordinate, indexType → Parent coordinate) where
  selected : Finset indexType
  retained_weight :
    (∑ index : indexType, weight index) ≤
      (2 : ENNReal) ^ scaleCount *
        ∑ index ∈ selected, weight index
  parent_weight_floor :
    ∀ coordinate,
      ∀ value : Parent coordinate,
        (selected.filter fun index =>
            parent coordinate index = value).Nonempty →
          (1 / 2 : ENNReal) *
                (∑ index ∈ selected, weight index) ≤
            (Fintype.card (Parent coordinate) : ENNReal) *
              ∑ index ∈
                  selected.filter fun index =>
                    parent coordinate index = value,
                weight index

def WZ2PropStickyNestedWeightedParentRegularizationStatement : Prop :=
  ∀ (indexType : Type)
    [Fintype indexType] [DecidableEq indexType],
    ∀ (weight : indexType → ENNReal),
      (∑ index : indexType, weight index) ≠ ⊤ →
      ∀ (scaleCount : ℕ),
        ∀ (Parent : Fin scaleCount → Type),
          ∀ [∀ coordinate, Fintype (Parent coordinate)],
            ∀ [∀ coordinate, DecidableEq (Parent coordinate)],
              ∀ (parent :
                  ∀ coordinate, indexType → Parent coordinate),
                (∀ level,
                  ∀ hnext : level + 1 < scaleCount,
                    ∀ first second,
                      parent ⟨level + 1, hnext⟩
                          first =
                        parent ⟨level + 1, hnext⟩
                          second →
                      parent
                          ⟨level, Nat.lt_of_succ_lt hnext⟩
                          first =
                        parent
                          ⟨level, Nat.lt_of_succ_lt hnext⟩
                          second) →
                  Nonempty
                    (WZ2PaperNestedWeightedParentRegularizationData
                      indexType weight scaleCount Parent parent)

end Kakeya.Assouad

end
