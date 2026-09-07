import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Unit-circle Frostman normalization for WZ1 Lemma 49

A separated direction set on the unit circle becomes one-dimensional
Frostman once its global cardinality is bounded below at the reciprocal
separation scale.
-/

namespace Kakeya.Assouad

/--
Normalize unit-circle cap packing by a global cardinality lower bound.

The term `4 / sqrt 3 + 1` is the local cap-packing constant.  The additional
constant `2` handles radii between `1 / 2` and `1`.
-/
def WZ1Lemma49UnitCircleFrostmanStatement : Prop :=
  ∀ {directions : DiscreteSet 2} {tau kappa : ℝ},
    0 < tau →
    tau ≤ 1 / 2 →
    0 < kappa →
    (∀ direction ∈ directions, ‖direction‖ = 1) →
    directions.IsDeltaSeparated tau →
    kappa / tau ≤ (directions.card : ℝ) →
    directions.IsFrostman tau 1
      (ENNReal.ofReal
        (2 + (4 / Real.sqrt 3 + 1) / kappa))

end Kakeya.Assouad
