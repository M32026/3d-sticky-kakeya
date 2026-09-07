import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteFiberRatio

/-!
# Selected fiber uniformity from nested weighted lower pruning

The number of occupied parents cancels.  Ambient fibers are `ambientConstant`
uniform, the source shading has a common per-tube lower bound, and nested
pruning gives every surviving parent a fixed share of the selected total
mass.  A common per-tube upper bound then converts that mass share back to a
selected fiber-cardinality lower bound.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped BigOperators ENNReal

theorem finite_nested_weighted_selected_fiber_uniform
    {Parent : Type}
    [Fintype Parent] [Nonempty Parent]
    (ambientCount selectedCount selectedMass : Parent → ENNReal)
    (sourceMass selectedTotalMass : ENNReal)
    (tubeLower tubeUpper ambientConstant retentionConstant : ENNReal)
    (htubeLowerZero : tubeLower ≠ 0)
    (htubeLowerTop : tubeLower ≠ ⊤)
    (hambientUniform :
      ∀ first second,
        ambientCount first ≤
          ambientConstant * ambientCount second)
    (hselectedAmbient :
      ∀ parent, selectedCount parent ≤ ambientCount parent)
    (hsourceLower :
      tubeLower * (∑ parent, ambientCount parent) ≤ sourceMass)
    (hretained :
      sourceMass ≤ retentionConstant * selectedTotalMass)
    (hselectedMassUpper :
      ∀ parent,
        selectedMass parent ≤ tubeUpper * selectedCount parent)
    (hselectedMassFloor :
      ∀ parent,
        selectedCount parent ≠ 0 →
          (1 / 2 : ENNReal) * selectedTotalMass ≤
            (Fintype.card Parent : ENNReal) *
              selectedMass parent) :
    ∀ first second,
      selectedCount second ≠ 0 →
      selectedCount first ≤
        (tubeLower⁻¹ *
          (2 * ambientConstant * retentionConstant * tubeUpper)) *
          selectedCount second := by
  intro first second hsecond
  let parentCount : ENNReal := Fintype.card Parent
  have hparentCountPos : 0 < parentCount := by
    dsimp only [parentCount]
    change
      (0 : ENNReal) <
        (Fintype.card Parent : ENNReal)
    exact_mod_cast
      (Fintype.card_pos : 0 < Fintype.card Parent)
  have hparentCountTop : parentCount ≠ ⊤ := by
    exact ENNReal.natCast_ne_top _
  have hambientFirst :
      parentCount * ambientCount first ≤
        ambientConstant * ∑ parent, ambientCount parent := by
    calc
      parentCount * ambientCount first =
          ∑ _parent : Parent, ambientCount first := by
        simp [parentCount]
      _ ≤
          ∑ parent : Parent,
            ambientConstant * ambientCount parent := by
        exact Finset.sum_le_sum fun parent _ =>
          hambientUniform first parent
      _ =
          ambientConstant * ∑ parent, ambientCount parent := by
        rw [Finset.mul_sum]
  have hselectedFirst :
      parentCount * (tubeLower * selectedCount first) ≤
        ambientConstant * sourceMass := by
    calc
      parentCount * (tubeLower * selectedCount first) =
          tubeLower * (parentCount * selectedCount first) := by
        ring
      _ ≤ tubeLower * (parentCount * ambientCount first) := by
        exact mul_le_mul_left'
          (mul_le_mul_left' (hselectedAmbient first) parentCount)
          tubeLower
      _ ≤ tubeLower *
          (ambientConstant * ∑ parent, ambientCount parent) := by
        gcongr
      _ =
          ambientConstant *
            (tubeLower * ∑ parent, ambientCount parent) := by
        ring
      _ ≤ ambientConstant * sourceMass := by
        gcongr
  have htotalFromSecond :
      selectedTotalMass ≤
        2 * parentCount * selectedMass second := by
    have hfloor := hselectedMassFloor second hsecond
    have hhalfFinite :
        (1 / 2 : ENNReal) ≠ ⊤ := by norm_num
    calc
      selectedTotalMass =
          2 * ((1 / 2 : ENNReal) * selectedTotalMass) := by
        have hcancel :
            (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
          simpa [div_eq_mul_inv] using
            ENNReal.mul_inv_cancel
              (show (2 : ENNReal) ≠ 0 by norm_num)
              (show (2 : ENNReal) ≠ ⊤ by norm_num)
        rw [← mul_assoc, hcancel, one_mul]
      _ ≤ 2 * (parentCount * selectedMass second) := by
        gcongr
      _ = 2 * parentCount * selectedMass second := by ring
  have hwithParentCount :
      parentCount * (tubeLower * selectedCount first) ≤
        parentCount *
          ((2 * ambientConstant * retentionConstant * tubeUpper) *
            selectedCount second) := by
    calc
      parentCount * (tubeLower * selectedCount first) ≤
          ambientConstant * sourceMass := hselectedFirst
      _ ≤
          ambientConstant *
            (retentionConstant * selectedTotalMass) := by
        gcongr
      _ ≤
          ambientConstant *
            (retentionConstant *
              (2 * parentCount * selectedMass second)) := by
        gcongr
      _ ≤
          ambientConstant *
            (retentionConstant *
              (2 * parentCount *
                (tubeUpper * selectedCount second))) := by
        exact mul_le_mul_left'
          (mul_le_mul_left'
            (mul_le_mul_left'
              (hselectedMassUpper second)
              (2 * parentCount))
            retentionConstant)
          ambientConstant
      _ =
          parentCount *
            ((2 * ambientConstant * retentionConstant * tubeUpper) *
              selectedCount second) := by
        ring
  have hwithoutParentCount :
      tubeLower * selectedCount first ≤
        (2 * ambientConstant * retentionConstant * tubeUpper) *
          selectedCount second := by
    have hcomm :
        (tubeLower * selectedCount first) * parentCount ≤
          ((2 * ambientConstant * retentionConstant * tubeUpper) *
            selectedCount second) * parentCount := by
      simpa [mul_comm] using hwithParentCount
    exact
      (ENNReal.mul_le_mul_iff_left
        hparentCountPos.ne' hparentCountTop).mp hcomm
  have hinverse :
      selectedCount first ≤
        tubeLower⁻¹ *
          ((2 * ambientConstant * retentionConstant * tubeUpper) *
            selectedCount second) := by
    have hmul :
        tubeLower⁻¹ * (tubeLower * selectedCount first) ≤
          tubeLower⁻¹ *
            ((2 * ambientConstant * retentionConstant * tubeUpper) *
              selectedCount second) := by
      gcongr
    have hcancel :
        tubeLower⁻¹ * tubeLower = 1 :=
      ENNReal.inv_mul_cancel htubeLowerZero htubeLowerTop
    calc
      selectedCount first =
          (tubeLower⁻¹ * tubeLower) * selectedCount first := by
        rw [hcancel, one_mul]
      _ = tubeLower⁻¹ *
          (tubeLower * selectedCount first) := by ring
      _ ≤ tubeLower⁻¹ *
          ((2 * ambientConstant * retentionConstant * tubeUpper) *
            selectedCount second) := hmul
  simpa [mul_assoc] using hinverse

end Kakeya.Assouad

end
