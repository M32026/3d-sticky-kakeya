import MyLeanRepo.Kakeya.Cinematic.Definitions
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Statements

/-!
# Graph lenses for the PYZ application of Marcus--Tardos

This file records only the first-generation lenses lying in the graph strip.
The closing arcs used to turn the graphs into pseudo-circles are deliberately
absent from the data: the bridge theorem below is responsible for constructing
the cyclic intersection-reverse lists justified by that closing construction.
-/

noncomputable section

namespace Kakeya.Cinematic

/--
A finite graph family has the two pseudo-circle properties used by PYZ:
distinct graphs meet at most twice, and every meeting is proper.
-/
def IsGraphPseudoCircleFamily (curves : Finset C2Function) : Prop :=
  (∀ f ∈ curves, ∀ g ∈ curves, f ≠ g →
    ∀ x₁ x₂ x₃ : UnitPoint,
      (x₁ : ℝ) < x₂ → (x₂ : ℝ) < x₃ →
      f x₁ = g x₁ → f x₂ = g x₂ → f x₃ = g x₃ → False) ∧
  (∀ f ∈ curves, ∀ g ∈ curves, f ≠ g →
    ∀ x : UnitPoint, f x = g x →
      f.firstDeriv x ≠ g.firstDeriv x)

/-- A first-generation lens between two distinct graph curves. -/
structure GraphLens where
  f : C2Function
  g : C2Function
  f_ne_g : f ≠ g
  left : UnitPoint
  right : UnitPoint
  left_lt_right : (left : ℝ) < right
  eq_left : f left = g left
  eq_right : f right = g right
  no_interior_intersection :
    ∀ x : UnitPoint,
      (left : ℝ) < x → (x : ℝ) < right → f x ≠ g x

namespace GraphLens

/--
Two graph lenses overlap exactly when they share a graph side over a
positive-length parameter interval.
-/
def Overlap (L₁ L₂ : GraphLens) : Prop :=
  (L₁.f = L₂.f ∨ L₁.f = L₂.g ∨
    L₁.g = L₂.f ∨ L₁.g = L₂.g) ∧
  max (L₁.left : ℝ) L₂.left < min (L₁.right : ℝ) L₂.right

def Nonoverlap (L₁ L₂ : GraphLens) : Prop :=
  ¬L₁.Overlap L₂

end GraphLens

/-- Marcus--Tardos Lemma 10 in the graph-lens form needed by PYZ. -/
def GraphLensBoundStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ curves : Finset C2Function,
      IsGraphPseudoCircleFamily curves →
      ∀ lenses : Finset GraphLens,
        (∀ L ∈ lenses, L.f ∈ curves ∧ L.g ∈ curves) →
        (∀ L₁ ∈ lenses, ∀ L₂ ∈ lenses,
          L₁ ≠ L₂ → L₁.Nonoverlap L₂) →
        (lenses.card : ℝ) ≤
          C * Real.rpow curves.card (3 / 2 : ℝ) *
            Real.log (curves.card + 1)

/--
The topological/list-encoding bridge from Marcus--Tardos Corollary 6 to its
non-overlapping graph-lens consequence.
-/
def GraphLensBoundFromSequencesStatement : Prop :=
  MarcusTardos.TotalLengthSequenceBoundStatement →
    GraphLensBoundStatement

end Kakeya.Cinematic
