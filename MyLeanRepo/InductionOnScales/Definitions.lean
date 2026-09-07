module

public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Definitions for induction on scales

Core definitions: dyadic squares/tubes, NiceConfiguration, and related
geometric and combinatorial structures. Extracted from the target theorem
file to break a circular import dependency.
-/

open scoped BigOperators

noncomputable section

abbrev InductionPlane := ℝ × ℝ

def dyadicDelta (n : ℕ) : ℝ := Real.rpow 2 (-(n : ℝ))

def unitSquare : Set InductionPlane :=
  Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1

structure DyadicSquare (n : ℕ) where
  i : ℤ
  j : ℤ
deriving DecidableEq

structure DyadicTube (n : ℕ) where
  a : ℤ
  b : ℤ
deriving DecidableEq

def DyadicTube.IsInAllowedParameterStrip {n : ℕ}
    (T : DyadicTube n) : Prop :=
  -((2 ^ n : ℕ) : ℤ) ≤ T.a ∧ T.a < ((2 ^ n : ℕ) : ℤ)

def DyadicSquare.toSet {n : ℕ}
    (Q : DyadicSquare n) : Set InductionPlane :=
  let δ := dyadicDelta n
  Set.Ico ((Q.i : ℝ) * δ) ((Q.i + 1 : ℝ) * δ) ×ˢ
    Set.Ico ((Q.j : ℝ) * δ) ((Q.j + 1 : ℝ) * δ)

def DyadicTube.slope {n : ℕ} (T : DyadicTube n) : ℝ :=
  (T.a : ℝ) * dyadicDelta n

def DyadicTube.intercept {n : ℕ} (T : DyadicTube n) : ℝ :=
  (T.b : ℝ) * dyadicDelta n

def DyadicTube.toSet {n : ℕ}
    (T : DyadicTube n) : Set InductionPlane :=
  let δ := dyadicDelta n
  {p | ∃ slope ∈ Set.Ico ((T.a : ℝ) * δ) ((T.a + 1 : ℝ) * δ),
    ∃ intercept ∈ Set.Ico ((T.b : ℝ) * δ) ((T.b + 1 : ℝ) * δ),
      p.2 = slope * p.1 + intercept}

def tubeParamDist {n : ℕ} (T U : DyadicTube n) : ℝ :=
  max |T.slope - U.slope| |T.intercept - U.intercept|

/-- Finite cardinal Frostman condition in the dyadic tube-parameter chart. -/
def IsFiniteTubeSSet
    {n : ℕ} (s C : ℝ) (F : Finset (DyadicTube n)) : Prop :=
  F.Nonempty ∧ 1 ≤ C ∧ 0 ≤ s ∧
  (∀ T ∈ F, ∀ U ∈ F, T ≠ U →
    dyadicDelta n ≤ tubeParamDist T U) ∧
  ∀ center : DyadicTube n, ∀ r : ℝ, dyadicDelta n ≤ r →
    ((F.filter fun T => tubeParamDist T center ≤ r).card : ℝ) ≤
      C * Real.rpow r s * (F.card : ℝ)

structure NiceConfiguration
    (n : ℕ) (s C : ℝ) (M : ℕ) where
  points : Finset (DyadicSquare n)
  tubes : Finset (DyadicTube n)
  tubeFamily :
    (p : DyadicSquare n) → p ∈ points → Finset (DyadicTube n)
  h_subset : ∀ p hp, tubeFamily p hp ⊆ tubes
  h_size : ∀ p hp, (tubeFamily p hp).card = M
  h_sset : ∀ p hp, IsFiniteTubeSSet s C (tubeFamily p hp)
  h_incidence : ∀ p hp T, T ∈ tubeFamily p hp →
    (T.toSet ∩ p.toSet).Nonempty
  h_bounded : ∀ p ∈ points, p.toSet ⊆ unitSquare
  h_tube_parameters : ∀ T ∈ tubes, T.IsInAllowedParameterStrip

def NiceConfiguration.tubeFamilyOpt
    {n : ℕ} {s C : ℝ} {M : ℕ}
    (config : NiceConfiguration n s C M)
    (p : DyadicSquare n) : Finset (DyadicTube n) :=
  if hp : p ∈ config.points then config.tubeFamily p hp else ∅

def coarseRefinementFactor (n m : ℕ) : ℕ := 2 ^ (n - m)

/-- Index of the dyadic parent cell. Using a real floor is essential for
negative slope indices: truncation toward zero gives the wrong parent. -/
def coarseParentIndex (n m : ℕ) (a : ℤ) : ℤ :=
  ⌊(a : ℝ) / (coarseRefinementFactor n m : ℝ)⌋

/-- The occupied slope cell at the local scale `δ / Δ`. If
`δ = 2⁻ⁿ` and `Δ = 2⁻ᵐ`, a `δ`-slope index must be divided by `2ᵐ`,
not by the coarse-parent factor `2ⁿ⁻ᵐ`. -/
def localSlopeCellIndex (m : ℕ) (a : ℤ) : ℤ :=
  ⌊(a : ℝ) / ((2 ^ m : ℕ) : ℝ)⌋

def squareContained {n m : ℕ} (hnm : m ≤ n)
    (p : DyadicSquare n) (Q : DyadicSquare m) : Prop :=
  (Q.i : ℤ) * coarseRefinementFactor n m ≤ p.i ∧
  p.i < (Q.i + 1) * coarseRefinementFactor n m ∧
  (Q.j : ℤ) * coarseRefinementFactor n m ≤ p.j ∧
  p.j < (Q.j + 1) * coarseRefinementFactor n m

def containingSquare {n m : ℕ} (hnm : m ≤ n)
    (p : DyadicSquare n) : DyadicSquare m :=
  ⟨coarseParentIndex n m p.i, coarseParentIndex n m p.j⟩

/-- Coordinatewise parameter truncation. This map is retained only to state
what must *not* be used as an incidence-preserving map; the theorem below does
not mention it. -/
def deprecatedCoordinatewiseAncestor {n m : ℕ} (hnm : m ≤ n)
    (T : DyadicTube n) : DyadicTube m :=
  ⟨coarseParentIndex n m T.a, coarseParentIndex n m T.b⟩

def squareHomothety {n m : ℕ} (hnm : m ≤ n)
    (Q : DyadicSquare m) (p : DyadicSquare n) :
    DyadicSquare (n - m) :=
  ⟨p.i - Q.i * coarseRefinementFactor n m,
   p.j - Q.j * coarseRefinementFactor n m⟩

attribute [local instance] Classical.propDecidable

end
