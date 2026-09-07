import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Lenses
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

/-!
# Sequence data attached to graph lenses

The closure used by Pramanik--Yang--Zahl places the interior of every closed
curve below its graph.  Consequently a graph lens is a Marcus--Tardos
moon-face: its upper graph is the positive side and its lower graph is the
negative side.  The lens-face and inverse-face sequence families are empty.
-/

noncomputable section

namespace Kakeya.Cinematic.GraphLensBridge

open Kakeya.Cinematic

/-- The midpoint of the parameter interval supporting a graph lens. -/
def midpoint (lens : GraphLens) : UnitPoint :=
  ⟨((lens.left : ℝ) + lens.right) / 2, by
    constructor
    · have hleft : 0 ≤ (lens.left : ℝ) := lens.left.property.1
      have hright : 0 ≤ (lens.right : ℝ) := lens.right.property.1
      linarith
    · have hleft : (lens.left : ℝ) ≤ 1 := lens.left.property.2
      have hright : (lens.right : ℝ) ≤ 1 := lens.right.property.2
      linarith⟩

theorem left_lt_midpoint (lens : GraphLens) :
    (lens.left : ℝ) < midpoint lens := by
  simp only [midpoint]
  linarith [lens.left_lt_right]

theorem midpoint_lt_right (lens : GraphLens) :
    (midpoint lens : ℝ) < lens.right := by
  simp only [midpoint]
  linarith [lens.left_lt_right]

theorem value_ne_at_midpoint (lens : GraphLens) :
    lens.f (midpoint lens) ≠ lens.g (midpoint lens) :=
  lens.no_interior_intersection (midpoint lens)
    (left_lt_midpoint lens) (midpoint_lt_right lens)

/-- The positive side of the moon-face obtained after closing the graphs. -/
def upper (lens : GraphLens) : C2Function :=
  if lens.g (midpoint lens) < lens.f (midpoint lens) then lens.f else lens.g

/-- The negative side of the moon-face obtained after closing the graphs. -/
def lower (lens : GraphLens) : C2Function :=
  if lens.g (midpoint lens) < lens.f (midpoint lens) then lens.g else lens.f

theorem upper_eq_f_or_g (lens : GraphLens) :
    upper lens = lens.f ∨ upper lens = lens.g := by
  simp only [upper]
  split_ifs <;> simp

theorem lower_eq_f_or_g (lens : GraphLens) :
    lower lens = lens.f ∨ lower lens = lens.g := by
  simp only [lower]
  split_ifs <;> simp

theorem upper_ne_lower (lens : GraphLens) :
    upper lens ≠ lower lens := by
  simp only [upper, lower]
  split_ifs with h
  · exact lens.f_ne_g
  · exact lens.f_ne_g.symm

theorem lower_lt_upper_at_midpoint (lens : GraphLens) :
    lower lens (midpoint lens) < upper lens (midpoint lens) := by
  simp only [upper, lower]
  split_ifs with h
  · exact h
  · exact lt_of_le_of_ne (le_of_not_gt h)
      (value_ne_at_midpoint lens)

/-- The lenses whose positive side is a fixed host curve. -/
def hostedLenses (lenses : Finset GraphLens) (host : C2Function) :
    Finset GraphLens :=
  by
    classical
    exact lenses.filter fun lens => upper lens = host

@[implicit_reducible]
private noncomputable def tieOrder : LinearOrder GraphLens := by
  classical
  exact linearOrderOfSTO WellOrderingRel

/--
An auxiliary total order which first compares lens midpoints.  The arbitrary
well-order is consulted only to break midpoint ties.
-/
@[implicit_reducible]
noncomputable def graphLensOrder : LinearOrder GraphLens := by
  letI := tieOrder
  exact LinearOrder.lift'
    (fun lens => toLex ((midpoint lens : ℝ), lens))
    (fun _ _ h => congrArg (fun value => (ofLex value).2) h)

theorem midpoint_le_of_graphLensOrder_lt {first second : GraphLens}
    (h : @LT.lt GraphLens graphLensOrder.toLT first second) :
    (midpoint first : ℝ) ≤ midpoint second := by
  letI := tieOrder
  change toLex ((midpoint first : ℝ), first) <
    toLex ((midpoint second : ℝ), second) at h
  rcases (Prod.Lex.lt_iff.mp h) with hmid | htie
  · exact hmid.le
  · exact htie.1.le

/-- The host fiber in increasing midpoint order. -/
def hostedList (lenses : Finset GraphLens) (host : C2Function) :
    List GraphLens :=
  letI := graphLensOrder
  (hostedLenses lenses host).sort

/--
The moon-face sequence at a host curve, ordered from left to right along its
graph side.  This is a cyclic order after the graph is closed.
-/
def moonSequence (lenses : Finset GraphLens) (host : C2Function) :
    List C2Function :=
  (hostedList lenses host).map lower

/-- Graph lenses contribute no lens-face sequence in the PYZ closure. -/
def lensSequence (_lenses : Finset GraphLens) (_host : C2Function) :
    List C2Function :=
  []

/-- Graph lenses contribute no inverse-face sequence in the PYZ closure. -/
def inverseSequence (_lenses : Finset GraphLens) (_host : C2Function) :
    List C2Function :=
  []

end Kakeya.Cinematic.GraphLensBridge
