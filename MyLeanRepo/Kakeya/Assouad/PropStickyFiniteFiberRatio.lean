import MyLeanRepo.Kakeya.Assouad.PropStickyConvexWolffSubfamilyTransfer

/-!
# Fiberwise cardinality ratios after finite regularization

This module turns global cardinality retention plus ambient and selected
fiber uniformity into a pointwise ambient-to-selected fiber ratio.  The
ratio is then transported through the exact source/target index equivalence
of one unit-rescaled full fiber.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal

theorem finite_uniform_fiber_ratio
    {Parent : Type*}
    [Fintype Parent] [Nonempty Parent]
    (ambient selected : Parent → ENNReal)
    (ambientConstant selectedConstant retentionConstant : ENNReal)
    (hambient :
      ∀ first second,
        ambient first ≤ ambientConstant * ambient second)
    (hselected :
      ∀ first second,
        selected first ≤ selectedConstant * selected second)
    (hretained :
      (∑ parent, ambient parent) ≤
        retentionConstant * ∑ parent, selected parent)
    (parent : Parent) :
    ambient parent ≤
      ambientConstant * retentionConstant * selectedConstant *
        selected parent := by
  let parentCount : ENNReal := Fintype.card Parent
  have hparentCountPos : 0 < parentCount := by
    have hcardPos : 0 < Fintype.card Parent :=
      Fintype.card_pos
    have hcastPos :
        (0 : ENNReal) < (Fintype.card Parent : ENNReal) :=
      Nat.cast_pos.mpr hcardPos
    simpa [parentCount] using hcastPos
  have hparentCountTop : parentCount ≠ ⊤ := by
    simp [parentCount]
  have hambientSum :
      parentCount * ambient parent ≤
        ambientConstant * ∑ other, ambient other := by
    calc
      parentCount * ambient parent =
          ∑ _other : Parent, ambient parent := by
        simp [parentCount]
      _ ≤ ∑ other : Parent,
            ambientConstant * ambient other := by
        exact Finset.sum_le_sum fun other _ =>
          hambient parent other
      _ = ambientConstant * ∑ other, ambient other := by
        rw [Finset.mul_sum]
  have hselectedSum :
      (∑ other, selected other) ≤
        parentCount * (selectedConstant * selected parent) := by
    calc
      (∑ other, selected other) ≤
          ∑ _other : Parent,
            selectedConstant * selected parent := by
        exact Finset.sum_le_sum fun other _ =>
          hselected other parent
      _ = parentCount *
          (selectedConstant * selected parent) := by
        simp [parentCount]
  have hwithCount :
      parentCount * ambient parent ≤
        parentCount *
          (ambientConstant * retentionConstant *
            selectedConstant * selected parent) := by
    calc
      parentCount * ambient parent ≤
          ambientConstant * ∑ other, ambient other :=
        hambientSum
      _ ≤ ambientConstant *
          (retentionConstant * ∑ other, selected other) := by
        gcongr
      _ ≤ ambientConstant *
          (retentionConstant *
            (parentCount *
              (selectedConstant * selected parent))) := by
        gcongr
      _ = parentCount *
          (ambientConstant * retentionConstant *
            selectedConstant * selected parent) := by
        ring
  have hwithCount' :
      ambient parent * parentCount ≤
        (ambientConstant * retentionConstant *
          selectedConstant * selected parent) * parentCount := by
    simpa [mul_comm] using hwithCount
  exact
    (ENNReal.mul_le_mul_iff_left
      hparentCountPos.ne' hparentCountTop).mp hwithCount'

theorem finite_uniform_weighted_fiber_ratio
    {Parent : Type*}
    [Fintype Parent] [Nonempty Parent]
    (ambient selected : Parent → ENNReal)
    (weight ambientConstant selectedConstant retentionConstant : ENNReal)
    (hambient :
      ∀ first second,
        ambient first ≤ ambientConstant * ambient second)
    (hselected :
      ∀ first second,
        selected first ≤ selectedConstant * selected second)
    (hretained :
      weight * (∑ parent, ambient parent) ≤
        retentionConstant * ∑ parent, selected parent)
    (parent : Parent) :
    weight * ambient parent ≤
      ambientConstant * retentionConstant * selectedConstant *
        selected parent := by
  let parentCount : ENNReal := Fintype.card Parent
  have hparentCountPos : 0 < parentCount := by
    have hcardPos : 0 < Fintype.card Parent :=
      Fintype.card_pos
    have hcastPos :
        (0 : ENNReal) < (Fintype.card Parent : ENNReal) :=
      Nat.cast_pos.mpr hcardPos
    simpa [parentCount] using hcastPos
  have hparentCountTop : parentCount ≠ ⊤ := by
    simp [parentCount]
  have hambientSum :
      parentCount * ambient parent ≤
        ambientConstant * ∑ other, ambient other := by
    calc
      parentCount * ambient parent =
          ∑ _other : Parent, ambient parent := by
        simp [parentCount]
      _ ≤ ∑ other : Parent,
            ambientConstant * ambient other := by
        exact Finset.sum_le_sum fun other _ =>
          hambient parent other
      _ = ambientConstant * ∑ other, ambient other := by
        rw [Finset.mul_sum]
  have hselectedSum :
      (∑ other, selected other) ≤
        parentCount * (selectedConstant * selected parent) := by
    calc
      (∑ other, selected other) ≤
          ∑ _other : Parent,
            selectedConstant * selected parent := by
        exact Finset.sum_le_sum fun other _ =>
          hselected other parent
      _ = parentCount *
          (selectedConstant * selected parent) := by
        simp [parentCount]
  have hwithCount :
      parentCount * (weight * ambient parent) ≤
        parentCount *
          (ambientConstant * retentionConstant *
            selectedConstant * selected parent) := by
    calc
      parentCount * (weight * ambient parent) =
          weight * (parentCount * ambient parent) := by ring
      _ ≤ weight *
          (ambientConstant * ∑ other, ambient other) := by
        gcongr
      _ = ambientConstant *
          (weight * ∑ other, ambient other) := by ring
      _ ≤ ambientConstant *
          (retentionConstant * ∑ other, selected other) := by
        gcongr
      _ ≤ ambientConstant *
          (retentionConstant *
            (parentCount *
              (selectedConstant * selected parent))) := by
        gcongr
      _ = parentCount *
          (ambientConstant * retentionConstant *
            selectedConstant * selected parent) := by
        ring
  have hwithCount' :
      (weight * ambient parent) * parentCount ≤
        (ambientConstant * retentionConstant *
          selectedConstant * selected parent) * parentCount := by
    simpa [mul_comm] using hwithCount
  exact
    (ENNReal.mul_le_mul_iff_left
      hparentCountPos.ne' hparentCountTop).mp hwithCount'

theorem
    WZ2PaperUnitRescaledFamilyData.targetFamily_enncard_eq_fullFiber
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C : ENNReal}
    (data :
      WZ2PaperUnitRescaledFamilyData
        cover parent hrho C) :
    data.targetFamily.enncard =
      (cover.fullFiberSubfamily parent).family.enncard := by
  change (data.targetFamily.card : ENNReal) =
    ((cover.fullFiberSubfamily parent).family.card : ENNReal)
  have hcard :
      data.targetFamily.card =
        (cover.fullFiberSubfamily parent).family.card := by
    simpa using Fintype.card_congr data.targetEquivFullFiber
  exact congrArg (fun cardinality : ℕ => (cardinality : ENNReal)) hcard

theorem
    WZ2PaperUnitRescaledFamilyData.targetSubfamily_convex_wolff_of_source_ratio
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C K : ENNReal}
    (data :
      WZ2PaperUnitRescaledFamilyData
        cover parent hrho C)
    (sourceSelected :
      Kakeya.Streamlined.TubeSubfamily
        (cover.fullFiberSubfamily parent).family)
    (hsourceRatio :
      (cover.fullFiberSubfamily parent).family.enncard ≤
        K * sourceSelected.family.enncard) :
    WZ2PaperConvexWolffBound
      (data.targetSubfamilyForSource sourceSelected).family
      (K * C) := by
  apply
    data.convex_wolff.subfamily_of_cardinality
      (data.targetSubfamilyForSource sourceSelected)
  rw [data.targetFamily_enncard_eq_fullFiber]
  exact hsourceRatio

theorem
    WZ2PaperUnitRescaledFamilyData.targetSubfamily_convex_wolff_of_weighted_source_ratio
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C weight K : ENNReal}
    (data :
      WZ2PaperUnitRescaledFamilyData
        cover parent hrho C)
    (sourceSelected :
      Kakeya.Streamlined.TubeSubfamily
        (cover.fullFiberSubfamily parent).family)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hsourceRatio :
      weight *
          (cover.fullFiberSubfamily parent).family.enncard ≤
        K * sourceSelected.family.enncard) :
    WZ2PaperConvexWolffBound
      (data.targetSubfamilyForSource sourceSelected).family
      ((weight⁻¹ * K) * C) := by
  apply
    data.convex_wolff.subfamily_of_weighted_cardinality
      (data.targetSubfamilyForSource sourceSelected)
      hweightZero hweightTop
  rw [data.targetFamily_enncard_eq_fullFiber]
  simpa only [
    WZ2PaperUnitRescaledFamilyData.targetSubfamilyForSource,
    Kakeya.Streamlined.TubeFamily.enncard] using hsourceRatio

end Kakeya.Assouad

end
