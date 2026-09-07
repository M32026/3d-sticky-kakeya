import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12

/-!
# Uniform weighted sums over selected parent classes

Suppose all ambient parent weights are mutually `C`-comparable and a selected
set has `D`-comparable occupied class cardinalities under a quotient map.
Then the selected weighted class sums are `C * D`-comparable.

This is the counting core for unions of complete actual Definition 2.12
fibers: the ambient weight is one actual full-fiber cardinality, while the
selected class records the actual parents grouped into one coarser parent.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Uniform ambient weights and uniform occupied selected class sizes imply
uniform selected class-weight sums. -/
theorem wz2_uniform_selected_class_weight
    {Middle Coarse : Type*}
    [Fintype Middle] [DecidableEq Middle]
    [Fintype Coarse] [DecidableEq Coarse]
    (weight : Middle → ENNReal)
    (ambientConstant : ENNReal)
    (weightUniform :
      ∀ first second,
        weight first ≤ ambientConstant * weight second)
    (selected : Finset Middle)
    (parent : Middle → Coarse)
    (degreeConstant : ENNReal)
    (degreeUniform :
      ∀ first second,
        0 <
            (selected.filter fun middle =>
              parent middle = first).card →
        0 <
            (selected.filter fun middle =>
              parent middle = second).card →
        ((selected.filter fun middle =>
          parent middle = first).card : ENNReal) ≤
          degreeConstant *
            ((selected.filter fun middle =>
              parent middle = second).card : ENNReal)) :
    ∀ first second,
      0 <
          (selected.filter fun middle =>
            parent middle = first).card →
      0 <
          (selected.filter fun middle =>
            parent middle = second).card →
      (∑ middle ∈ selected.filter
          (fun current => parent current = first),
          weight middle) ≤
        (ambientConstant * degreeConstant) *
          ∑ middle ∈ selected.filter
            (fun current => parent current = second),
            weight middle := by
  intro first second firstPos secondPos
  let firstClass :=
    selected.filter fun middle =>
      parent middle = first
  let secondClass :=
    selected.filter fun middle =>
      parent middle = second
  have secondNonempty : secondClass.Nonempty :=
    Finset.card_pos.mp secondPos
  obtain ⟨reference, referenceMem, referenceMin⟩ :=
    Finset.exists_min_image
      secondClass weight secondNonempty
  have firstWeightUpper :
      ∀ middle ∈ firstClass,
        weight middle ≤
          ambientConstant * weight reference := by
    intro middle _
    exact weightUniform middle reference
  have firstSumUpper :
      (∑ middle ∈ firstClass, weight middle) ≤
        (firstClass.card : ENNReal) *
          (ambientConstant * weight reference) := by
    calc
      (∑ middle ∈ firstClass, weight middle) ≤
          ∑ _middle ∈ firstClass,
            ambientConstant * weight reference := by
        exact
          Finset.sum_le_sum fun middle hmiddle =>
            firstWeightUpper middle hmiddle
      _ =
          (firstClass.card : ENNReal) *
            (ambientConstant * weight reference) := by
        simp [Finset.sum_const]
  have degree :=
    degreeUniform first second firstPos secondPos
  have referenceSumLower :
      (secondClass.card : ENNReal) * weight reference ≤
        ∑ middle ∈ secondClass, weight middle := by
    calc
      (secondClass.card : ENNReal) * weight reference =
          ∑ _middle ∈ secondClass,
            weight reference := by
        simp [Finset.sum_const]
      _ ≤
          ∑ middle ∈ secondClass, weight middle := by
        exact
          Finset.sum_le_sum fun middle hmiddle =>
            referenceMin middle hmiddle
  calc
    (∑ middle ∈ firstClass, weight middle) ≤
        (firstClass.card : ENNReal) *
          (ambientConstant * weight reference) :=
      firstSumUpper
    _ ≤
        (degreeConstant * (secondClass.card : ENNReal)) *
          (ambientConstant * weight reference) := by
      gcongr
    _ =
        (ambientConstant * degreeConstant) *
          ((secondClass.card : ENNReal) *
            weight reference) := by
      ring
    _ ≤
        (ambientConstant * degreeConstant) *
          ∑ middle ∈ secondClass, weight middle := by
      gcongr

end Kakeya.Assouad

end
