import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log

/-!
# Dyadic regularization of parent--function incidence degrees

This is the finite pigeonholing step preceding PYZ Lemma 47.  Edges join
functions to fine rectangles, and every fine rectangle has a coarse parent.
One dyadic degree class retains a logarithmic fraction of all edges.
-/

namespace Kakeya.Cinematic

def incidenceDegree
    {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (edges : Finset (α × β)) (parent : β → γ)
    (function : α) (coarse : γ) : ℕ :=
  (edges.filter fun edge =>
    edge.1 = function ∧ parent edge.2 = coarse).card

def IncidenceDegreeRegularizationStatement : Prop :=
  ∀ {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    [Fintype β],
    ∀ (edges : Finset (α × β)) (parent : β → γ),
      edges.Nonempty →
      ∃ (level : ℕ) (selected : Finset (α × β)),
        level ≤ Nat.log2 (Fintype.card β) ∧
        selected =
          edges.filter (fun edge =>
            2 ^ level ≤
                incidenceDegree edges parent edge.1 (parent edge.2) ∧
              incidenceDegree edges parent edge.1 (parent edge.2) <
                2 ^ (level + 1)) ∧
        edges.card ≤
          (Nat.log2 (Fintype.card β) + 1) * selected.card ∧
        ∀ function coarse,
          incidenceDegree selected parent function coarse = 0 ∨
            (2 ^ level ≤
                incidenceDegree selected parent function coarse ∧
              incidenceDegree selected parent function coarse <
                2 ^ (level + 1))

end Kakeya.Cinematic
