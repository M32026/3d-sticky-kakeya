import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Log

/-!
# Dyadic regularization of coarse support cardinalities

After the function--parent incidence graph has been regularized and its
supports have been constructed, one further dyadic pigeonhole selects coarse
parents whose support cardinalities have one common positive lower scale.
This scale is distinct from the preceding incidence degree.
-/

namespace Kakeya.Cinematic

def CoarseSupportCardinalityRegularizationStatement : Prop :=
  ∀ {α γ : Type*} [DecidableEq α] [DecidableEq γ],
    ∀ (ambient : Finset α) (active : Finset γ)
      (support : γ → Finset α),
      active.Nonempty →
      (∀ coarse ∈ active, (support coarse).Nonempty) →
      (∀ coarse ∈ active, support coarse ⊆ ambient) →
      ∃ (level : ℕ) (selected : Finset γ),
        level ≤ Nat.log2 ambient.card ∧
        selected.Nonempty ∧
        selected =
          active.filter (fun coarse =>
            2 ^ level ≤ (support coarse).card ∧
              (support coarse).card < 2 ^ (level + 1)) ∧
        active.card ≤
          (Nat.log2 ambient.card + 1) * selected.card ∧
        ∀ coarse ∈ selected,
          2 ^ level ≤ (support coarse).card ∧
            (support coarse).card < 2 ^ (level + 1)

end Kakeya.Cinematic
