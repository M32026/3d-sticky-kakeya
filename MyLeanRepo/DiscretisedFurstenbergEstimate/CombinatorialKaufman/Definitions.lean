module

public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Definitions for the Combinatorial Kaufman Decomposition

This module contains the shared definitions used throughout the proof:
`chordSlope`, `chordValue`, `EpsilonLinear`, `EpsilonSuperlinear`, and
`PairwiseInteriorDisjoint`.
-/

noncomputable section

def chordSlope (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (f b - f a) / (b - a)

def chordValue (f : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  f a + chordSlope f a b * (x - a)

def EpsilonLinear (f : ℝ → ℝ) (ε a b : ℝ) : Prop :=
  ∀ x ∈ Set.Icc a b,
    |f x - chordValue f a b x| ≤ ε * (b - a)

def EpsilonSuperlinear (f : ℝ → ℝ) (ε a b : ℝ) : Prop :=
  ∀ x ∈ Set.Icc a b,
    chordValue f a b x - ε * (b - a) ≤ f x

def PairwiseInteriorDisjoint {n : ℕ} (I : Fin n → ℝ × ℝ) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    Disjoint (Set.Ioo (I i).1 (I i).2) (Set.Ioo (I j).1 (I j).2)

/-- Sum of lengths of intervals in a list. -/
def totalLength (L : List (ℝ × ℝ)) : ℝ :=
  (L.map (fun I : ℝ × ℝ => I.2 - I.1)).sum

/-- Sorted left-to-right, disjoint interiors: for I before J, I.2 ≤ J.1. -/
def SortedDisjoint (L : List (ℝ × ℝ)) : Prop :=
  L.Pairwise (fun I J => I.2 ≤ J.1) ∧ ∀ I ∈ L, I.1 < I.2

/-- All intervals are ε-linear. -/
def AllEpsilonLinear (f : ℝ → ℝ) (ε : ℝ) (L : List (ℝ × ℝ)) : Prop :=
  ∀ I ∈ L, EpsilonLinear f ε I.1 I.2

/-- Each interval is either 2δ-linear (slope ≥ s, ≤ 2) or 2δ-superlinear (slope = s). -/
def GoodIntervals (f : ℝ → ℝ) (s δ : ℝ) (L : List (ℝ × ℝ)) : Prop :=
  ∀ I ∈ L,
    (EpsilonLinear f (2 * δ) I.1 I.2 ∧ s ≤ chordSlope f I.1 I.2 ∧ chordSlope f I.1 I.2 ≤ 2) ∨
    (EpsilonSuperlinear f (2 * δ) I.1 I.2 ∧ chordSlope f I.1 I.2 = s)

end
