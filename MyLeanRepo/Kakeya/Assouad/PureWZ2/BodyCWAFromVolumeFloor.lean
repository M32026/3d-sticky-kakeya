import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12

/-!
# Convex-Wolff counting from a uniform body-volume floor

If every member of a finite body family has volume at least `floor`, then a
body contained in a convex test set forces that test set to have volume at
least `floor`.  Summing this elementary observation gives normalized
Convex-Wolff counting with constant `floor⁻¹`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem wz2PaperBodyConvexWolffBound_of_volume_floor
    (family : Kakeya.Streamlined.BodyFamily)
    (floor : ENNReal)
    (floor_ne_zero : floor ≠ 0)
    (floor_ne_top : floor ≠ ⊤)
    (volumeFloor :
      ∀ index, floor ≤ (family.body index).volume) :
    WZ2PaperBodyConvexWolffBound family floor⁻¹ := by
  intro convexSet _hconvex
  let contained := family.containedIndices convexSet
  have eachUpper :
      ∀ index ∈ contained,
        floor ≤ volume convexSet := by
    intro index hindex
    exact
      (volumeFloor index).trans
        (measure_mono
          ((Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mp
            hindex))
  have weightedCount :
      family.containedCount convexSet * floor ≤
        family.enncard * volume convexSet := by
    calc
      family.containedCount convexSet * floor =
          ∑ _index ∈ contained, floor := by
        simp [Kakeya.Streamlined.BodyFamily.containedCount,
          contained, Finset.sum_const, nsmul_eq_mul]
      _ ≤
          ∑ _index ∈ contained, volume convexSet := by
        exact Finset.sum_le_sum eachUpper
      _ =
          (contained.card : ENNReal) * volume convexSet := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ family.enncard * volume convexSet := by
        gcongr
        change (contained.card : ENNReal) ≤
          (family.card : ENNReal)
        exact_mod_cast
          (show contained.card ≤ family.card by
            simpa using Finset.card_le_univ contained)
  calc
    family.containedCount convexSet =
        floor⁻¹ *
          (family.containedCount convexSet * floor) := by
      rw [show
        floor⁻¹ *
            (family.containedCount convexSet * floor) =
          family.containedCount convexSet *
            (floor⁻¹ * floor) by ring,
        ENNReal.inv_mul_cancel floor_ne_zero floor_ne_top,
        mul_one]
    _ ≤ floor⁻¹ *
        (family.enncard * volume convexSet) := by
      gcongr
    _ =
        floor⁻¹ * volume convexSet * family.enncard := by
      ring

/--
Equivalent denominator-free form: if `1 ≤ C * |body|` for every member, the
family satisfies normalized CWA with constant `C`.
-/
theorem wz2PaperBodyConvexWolffBound_of_volume_ratio
    (family : Kakeya.Streamlined.BodyFamily)
    (C : ENNReal)
    (volumeRatio :
      ∀ index, 1 ≤ C * (family.body index).volume) :
    WZ2PaperBodyConvexWolffBound family C := by
  intro convexSet _hconvex
  let contained := family.containedIndices convexSet
  have eachUpper :
      ∀ index ∈ contained,
        1 ≤ C * volume convexSet := by
    intro index hindex
    calc
      (1 : ENNReal) ≤
          C * (family.body index).volume :=
        volumeRatio index
      _ ≤ C * volume convexSet := by
        gcongr
        exact measure_mono
          ((Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mp
            hindex)
  calc
    family.containedCount convexSet =
        ∑ _index ∈ contained, (1 : ENNReal) := by
      simp [Kakeya.Streamlined.BodyFamily.containedCount,
        contained]
    _ ≤
        ∑ _index ∈ contained,
          C * volume convexSet := by
      exact Finset.sum_le_sum eachUpper
    _ =
        (contained.card : ENNReal) *
          (C * volume convexSet) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤
        family.enncard * (C * volume convexSet) := by
      gcongr
      change (contained.card : ENNReal) ≤
        (family.card : ENNReal)
      exact_mod_cast
        (show contained.card ≤ family.card by
          simpa using Finset.card_le_univ contained)
    _ = C * volume convexSet * family.enncard := by
      ring

end Kakeya.Assouad

end
