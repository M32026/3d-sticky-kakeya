import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Log

/-!
# Joint dyadic regularization of two fiber cardinalities

The paper first freezes the metric-fiber scale `mu₁` and then the retained
tangency-fiber scale `mu₂`.  This pure finite interface performs both
pigeonholes at once, retaining a squared logarithmic fraction while exposing
the two independent dyadic ranges.
-/

namespace Kakeya.Cinematic

def JointFiberCardinalityRegularizationStatement : Prop :=
  ∀ {α : Type*} [DecidableEq α],
    ∀ (items : Finset α) (metricCard retainedCard : α → ℕ)
      (upper : ℕ),
      items.Nonempty →
      (∀ item ∈ items,
        0 < metricCard item ∧
          metricCard item ≤ upper ∧
          0 < retainedCard item ∧
          retainedCard item ≤ upper) →
      ∃ metricLevel retainedLevel : ℕ,
        ∃ selected : Finset α,
          metricLevel ≤ Nat.log2 upper ∧
          retainedLevel ≤ Nat.log2 upper ∧
          selected.Nonempty ∧
          selected =
            items.filter (fun item =>
              2 ^ metricLevel ≤ metricCard item ∧
                metricCard item < 2 ^ (metricLevel + 1) ∧
                2 ^ retainedLevel ≤ retainedCard item ∧
                retainedCard item < 2 ^ (retainedLevel + 1)) ∧
          items.card ≤
            (Nat.log2 upper + 1) ^ 2 * selected.card ∧
          ∀ item ∈ selected,
            2 ^ metricLevel ≤ metricCard item ∧
              metricCard item < 2 ^ (metricLevel + 1) ∧
              2 ^ retainedLevel ≤ retainedCard item ∧
              retainedCard item < 2 ^ (retainedLevel + 1)

end Kakeya.Cinematic
