import MyLeanRepo.Kakeya.Streamlined.DividingScales.AdjacentParentMapHierarchy
import MyLeanRepo.Kakeya.Streamlined.DividingScales.PeriodicIntegerGridColoring
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Occupied nested integer-grid hierarchies

This module converts any finite family of Euclidean coordinate points into a
nested hierarchy of occupied floor-grid labels.

At level `k`, the label is

`coordinate ↦ floor (point coordinate * base^k)`.

Only labels hit by an actual leaf are retained.  Consequently every parent
map is surjective.  Division of a level-`k+1` label by `base` recovers the
level-`k` label, so the occupied parent maps satisfy the project's existing
`AdjacentFiniteParentMapRefinement` interface.

The construction is independent of tubes.  A strict full-midpoint producer
may use more coordinates than a supporting-line window producer, while both
reuse the same hierarchy and periodic-coloring infrastructure.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- Integer floor-grid label of one coordinate point at one level. -/
def integerGridLabel
    {dimension : ℕ}
    (base level : ℕ)
    (point : Fin dimension → ℝ) :
    Fin dimension → ℤ :=
  fun coordinate =>
    ⌊point coordinate * (base ^ level : ℝ)⌋

/--
Two points with the same floor-grid label differ by less than one cell width
in every coordinate.
-/
theorem abs_sub_lt_inv_pow_of_integerGridLabel_eq
    {dimension : ℕ}
    {base level : ℕ}
    (hbase : 1 ≤ base)
    {first second : Fin dimension → ℝ}
    (hlabel :
      integerGridLabel base level first =
        integerGridLabel base level second)
    (coordinate : Fin dimension) :
    |first coordinate - second coordinate| <
      (base ^ level : ℝ)⁻¹ := by
  have hbasePos : 0 < (base : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hbase)
  have hscalePos : 0 < (base ^ level : ℝ) := pow_pos hbasePos level
  have hfloor :
      ⌊first coordinate * (base ^ level : ℝ)⌋ =
        ⌊second coordinate * (base ^ level : ℝ)⌋ := by
    exact congrFun hlabel coordinate
  have hscaled :=
    Int.abs_sub_lt_one_of_floor_eq_floor hfloor
  have hscaledDifference :
      first coordinate * (base ^ level : ℝ) -
          second coordinate * (base ^ level : ℝ) =
        (first coordinate - second coordinate) *
          (base ^ level : ℝ) := by
    ring
  have hproduct :
      |first coordinate - second coordinate| *
          (base ^ level : ℝ) < 1 := by
    rw [← abs_of_pos hscalePos, ← abs_mul, ← hscaledDifference]
    exact hscaled
  calc
    |first coordinate - second coordinate|
        < 1 / (base ^ level : ℝ) := (lt_div_iff₀ hscalePos).2 hproduct
    _ = (base ^ level : ℝ)⁻¹ := one_div _

/--
A coordinatewise real bound gives a coordinatewise integer-label bound after
scaling, with the single extra unit coming from the two floor errors.
-/
theorem integerGridLabel_abs_sub_lt_of_coordinate_abs_sub_le
    {dimension : ℕ}
    {base level modulus : ℕ}
    {bound : ℝ}
    {first second : Fin dimension → ℝ}
    (hcoordinate :
      ∀ coordinate,
        |first coordinate - second coordinate| ≤ bound)
    (hmodulus :
      bound * (base ^ level : ℝ) + 1 <
        (modulus : ℝ))
    (coordinate : Fin dimension) :
    |integerGridLabel base level first coordinate -
        integerGridLabel base level second coordinate| <
      (modulus : ℤ) := by
  let scale : ℝ := (base ^ level : ℝ)
  let firstScaled : ℝ := first coordinate * scale
  let secondScaled : ℝ := second coordinate * scale
  have hscale : 0 ≤ scale := by
    positivity
  have hscaled :
      |firstScaled - secondScaled| ≤ bound * scale := by
    have hmul :=
      mul_le_mul_of_nonneg_right
        (hcoordinate coordinate) hscale
    have hdifference :
        firstScaled - secondScaled =
          (first coordinate - second coordinate) * scale := by
      dsimp only [firstScaled, secondScaled]
      ring
    rw [hdifference, abs_mul, abs_of_nonneg hscale]
    exact hmul
  have hfirstFloor :
      ((⌊firstScaled⌋ : ℤ) : ℝ) ≤ firstScaled :=
    Int.floor_le firstScaled
  have hsecondFloor :
      ((⌊secondScaled⌋ : ℤ) : ℝ) ≤ secondScaled :=
    Int.floor_le secondScaled
  have hfirstUpper :
      firstScaled < ((⌊firstScaled⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one firstScaled
  have hsecondUpper :
      secondScaled < ((⌊secondScaled⌋ : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one secondScaled
  have hupperReal :
      (((⌊firstScaled⌋ : ℤ) -
          (⌊secondScaled⌋ : ℤ) : ℤ) : ℝ) <
        (modulus : ℝ) := by
    have hdiff :
        firstScaled - secondScaled ≤
          |firstScaled - secondScaled| :=
      le_abs_self _
    push_cast
    linarith
  have hlowerReal :
      (-(modulus : ℝ)) <
        (((⌊firstScaled⌋ : ℤ) -
          (⌊secondScaled⌋ : ℤ) : ℤ) : ℝ) := by
    have hdiff :
        secondScaled - firstScaled ≤
          |firstScaled - secondScaled| := by
      simpa [abs_sub_comm] using
        (le_abs_self (secondScaled - firstScaled))
    push_cast
    linarith
  have hupperInt :
      (⌊firstScaled⌋ : ℤ) - (⌊secondScaled⌋ : ℤ) <
        (modulus : ℤ) := by
    exact_mod_cast hupperReal
  have hlowerInt :
      -(modulus : ℤ) <
        (⌊firstScaled⌋ : ℤ) - (⌊secondScaled⌋ : ℤ) := by
    exact_mod_cast hlowerReal
  rw [abs_lt]
  simpa only [integerGridLabel, firstScaled, secondScaled, scale] using
    And.intro hlowerInt hupperInt

/-- Labels occupied by a finite leaf family at one level. -/
def occupiedIntegerGridLabels
    {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf]
    {dimension : ℕ}
    (point : Leaf → Fin dimension → ℝ)
    (base level : ℕ) :
    Finset (Fin dimension → ℤ) := by
  classical
  exact Finset.univ.image fun leaf =>
    integerGridLabel base level (point leaf)

/-- One occupied label, carrying its certificate of occupancy. -/
abbrev OccupiedIntegerGridLabel
    {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf]
    {dimension : ℕ}
    (point : Leaf → Fin dimension → ℝ)
    (base level : ℕ) :=
  { label : Fin dimension → ℤ //
    label ∈ occupiedIntegerGridLabels point base level }

/-- Parent label of one leaf at one grid level. -/
def occupiedIntegerGridParent
    {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf]
    {dimension : ℕ}
    (point : Leaf → Fin dimension → ℝ)
    (base level : ℕ)
    (leaf : Leaf) :
    OccupiedIntegerGridLabel point base level :=
  ⟨integerGridLabel base level (point leaf), by
    classical
    exact Finset.mem_image.mpr
      ⟨leaf, Finset.mem_univ leaf, rfl⟩⟩

/-- Every occupied label is represented by a leaf. -/
theorem occupiedIntegerGridParent_surjective
    {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf]
    {dimension : ℕ}
    (point : Leaf → Fin dimension → ℝ)
    (base level : ℕ) :
    Function.Surjective
      (occupiedIntegerGridParent point base level) := by
  intro parent
  rcases Finset.mem_image.mp parent.property with
    ⟨leaf, _hleaf, hleaf⟩
  refine ⟨leaf, ?_⟩
  apply Subtype.ext
  exact hleaf

/--
Choose one actual leaf occupying a given grid label.
-/
def occupiedIntegerGridRepresentative
    {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf]
    {dimension : ℕ}
    (point : Leaf → Fin dimension → ℝ)
    (base level : ℕ)
    (parent : OccupiedIntegerGridLabel point base level) :
    Leaf :=
  Classical.choose (Finset.mem_image.mp parent.property)

/-- The chosen representative occupies exactly its prescribed label. -/
theorem occupiedIntegerGridParent_representative
    {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf]
    {dimension : ℕ}
    (point : Leaf → Fin dimension → ℝ)
    (base level : ℕ)
    (parent : OccupiedIntegerGridLabel point base level) :
    occupiedIntegerGridParent point base level
        (occupiedIntegerGridRepresentative point base level parent) =
      parent := by
  apply Subtype.ext
  exact
    (Classical.choose_spec
      (Finset.mem_image.mp parent.property)).2

/-- Parent equality is exactly equality of the underlying integer labels. -/
@[simp] theorem occupiedIntegerGridParent_eq_iff
    {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf]
    {dimension : ℕ}
    (point : Leaf → Fin dimension → ℝ)
    (base level : ℕ)
    (first second : Leaf) :
    occupiedIntegerGridParent point base level first =
        occupiedIntegerGridParent point base level second ↔
      integerGridLabel base level (point first) =
        integerGridLabel base level (point second) := by
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- Dividing one child coordinate by `base` recovers its parent coordinate. -/
lemma integerGridLabel_child_ediv_eq_parent
    {dimension : ℕ}
    {base level : ℕ}
    (hbase : 1 ≤ base)
    (point : Fin dimension → ℝ)
    (coordinate : Fin dimension) :
    integerGridLabel base (level + 1) point coordinate /
          (base : ℤ) =
        integerGridLabel base level point coordinate := by
  have hbase_ne : base ≠ 0 := by omega
  unfold integerGridLabel
  rw [show
    point coordinate * (base ^ (level + 1) : ℝ) =
      (point coordinate * (base ^ level : ℝ)) * (base : ℝ) by
        simp [pow_succ]
        ring]
  exact
    Int.mul_natCast_floor_div_cancel hbase_ne
      (point coordinate * (base ^ level : ℝ))

/-- Equality of adjacent fine labels implies equality of coarse labels. -/
theorem integerGridLabel_adjacent_refines
    {dimension : ℕ}
    {base level : ℕ}
    (hbase : 1 ≤ base)
    (first second : Fin dimension → ℝ)
    (hfine :
      integerGridLabel base (level + 1) first =
        integerGridLabel base (level + 1) second) :
    integerGridLabel base level first =
      integerGridLabel base level second := by
  funext coordinate
  have hfineCoordinate :=
    congrFun hfine coordinate
  have hfirst :=
    integerGridLabel_child_ediv_eq_parent
      (level := level) hbase first coordinate
  have hsecond :=
    integerGridLabel_child_ediv_eq_parent
      (level := level) hbase second coordinate
  rw [← hfirst, ← hsecond, hfineCoordinate]

/-- Equality at any finer grid level implies equality at every coarser level. -/
theorem integerGridLabel_refines_of_le
    {dimension : ℕ}
    {base coarse fine : ℕ}
    (hbase : 1 ≤ base)
    (hcoarseFine : coarse ≤ fine)
    (first second : Fin dimension → ℝ)
    (hfine :
      integerGridLabel base fine first =
        integerGridLabel base fine second) :
    integerGridLabel base coarse first =
      integerGridLabel base coarse second := by
  induction hcoarseFine with
  | refl =>
      exact hfine
  | @step fine hcoarseFine inductionHypothesis =>
      apply inductionHypothesis
      exact integerGridLabel_adjacent_refines
        hbase first second hfine

/--
Occupied floor-grid parents form an adjacent-refining hierarchy on every
finite level interval.
-/
def occupiedIntegerGridAdjacentRefinement
    {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf]
    {dimension levels : ℕ}
    (point : Leaf → Fin dimension → ℝ)
    (base : ℕ) (hbase : 1 ≤ base) :
    AdjacentFiniteParentMapRefinement
      Leaf
      (fun level : Fin (levels + 1) =>
        OccupiedIntegerGridLabel point base level.val)
      (fun level leaf =>
        occupiedIntegerGridParent point base level.val leaf) where
  adjacent_refines interval first second hfine := by
    apply Subtype.ext
    apply integerGridLabel_adjacent_refines hbase
    have hfineValue := congrArg Subtype.val hfine
    simpa using hfineValue

/-- The induced transition between any two occupied grid levels. -/
def occupiedIntegerGridTransition
    {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf]
    {dimension levels : ℕ}
    (point : Leaf → Fin dimension → ℝ)
    (base : ℕ) (hbase : 1 ≤ base)
    (coarse fine : Fin (levels + 1))
    (hcoarseFine : coarse ≤ fine) :
    OccupiedIntegerGridLabel point base fine.val →
      OccupiedIntegerGridLabel point base coarse.val :=
  (occupiedIntegerGridAdjacentRefinement point base hbase).transition
    (fun level =>
      occupiedIntegerGridParent_surjective
        point base level.val)
    coarse fine hcoarseFine

/-- Long-range occupied-grid transitions commute with every leaf parent. -/
theorem occupiedIntegerGridTransition_parent_compatible
    {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf]
    {dimension levels : ℕ}
    (point : Leaf → Fin dimension → ℝ)
    (base : ℕ) (hbase : 1 ≤ base)
    (coarse fine : Fin (levels + 1))
    (hcoarseFine : coarse ≤ fine)
    (leaf : Leaf) :
    occupiedIntegerGridTransition
        point base hbase coarse fine hcoarseFine
        (occupiedIntegerGridParent point base fine.val leaf) =
      occupiedIntegerGridParent point base coarse.val leaf := by
  exact
    (occupiedIntegerGridAdjacentRefinement point base hbase)
      |>.transition_parent_compatible
        (fun level =>
          occupiedIntegerGridParent_surjective
            point base level.val)
        coarse fine hcoarseFine leaf

/-- A terminal grid label is injective whenever the underlying label is. -/
theorem occupiedIntegerGridParent_injective
    {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf]
    {dimension : ℕ}
    (point : Leaf → Fin dimension → ℝ)
    (base level : ℕ)
    (hlabel :
      Function.Injective fun leaf =>
        integerGridLabel base level (point leaf)) :
    Function.Injective
      (occupiedIntegerGridParent point base level) := by
  intro first second hparent
  apply hlabel
  exact congrArg Subtype.val hparent

/-- All level labels of one leaf, ready for periodic residue coloring. -/
def multilevelIntegerGridLabel
    {Leaf : Type*}
    {dimension levels : ℕ}
    (point : Leaf → Fin dimension → ℝ)
    (base : ℕ)
    (leaf : Leaf) :
    Fin levels → Fin dimension → ℤ :=
  fun level =>
    integerGridLabel base level.val (point leaf)

end Kakeya.Streamlined
