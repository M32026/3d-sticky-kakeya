import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Fiber cardinality bound for finite product sets

If every fiber of a finset over its first projection has bounded size,
and the projection itself has bounded size, then the total cardinality
is bounded by the product.
-/

namespace Kakeya.Assouad

/--
Cardinality bound for a finset of pairs: if the first-projection image
has at most `M` elements and every fiber over the first component has
at most `K` elements, then the total set has at most `M * K` elements.
-/
lemma fiber_card_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset (α × β)) (M K : ℕ)
    (hM : (s.image Prod.fst).card ≤ M)
    (hK : ∀ (a : α), (s.filter (fun p : α × β => p.1 = a)).card ≤ K) :
    s.card ≤ M * K := by
  let t := s.image Prod.fst
  let f : α → ℕ := fun a => (s.filter (fun p : α × β => p.1 = a)).card
  have h_main : s.card = ∑ a ∈ t, f a := by
    exact Finset.card_eq_sum_card_fiberwise (H := fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  rw [h_main]
  have h1 : ∀ a ∈ t, f a ≤ K := by
    intro a _
    exact hK a
  have h_sum : ∑ a ∈ t, f a ≤ t.card * K := by
    have h2 : ∑ a ∈ t, f a ≤ t.card • K := Finset.sum_le_card_nsmul t f K h1
    have h3 : t.card • K = t.card * K := by
      simp
    rw [h3] at h2
    exact h2
  have h3 : t.card ≤ M := hM
  have h4 : t.card * K ≤ M * K := by
    have h5 : t.card * K ≤ M * K := by
      rw [mul_comm t.card K, mul_comm M K]
      exact Nat.mul_le_mul_left K h3
    exact h5
  exact le_trans h_sum h4

end Kakeya.Assouad
