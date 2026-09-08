import MyLeanRepo.Kakeya.Streamlined.DividingScales.CoherentRelationCardinalityTelescope

/-!
# Building a coherent hierarchy from adjacent parent-map refinement

The geometric producer does not need to construct every long-range
transition separately.  It is enough to prove the adjacent partition
refinement property:

```text
same parent at level k+1  ->  same parent at level k.
```

For surjective parent maps on a finite level chain, this condition makes the
level-`k` parent map factor through every finer parent map.  Choosing one
preimage of a finer parent then defines all long-range transitions.  The
result is independent of that preimage precisely because of the refinement
property.

This module is purely combinatorial.  It isolates the first reusable output
that a nested phase-space net construction must provide.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- A finite family of parent maps in which every adjacent finer partition
refines the preceding coarser partition. -/
structure AdjacentFiniteParentMapRefinement
    (Leaf : Type*)
    {levelCount : ℕ}
    (Parent : Fin (levelCount + 1) → Type*)
    (parent : (level : Fin (levelCount + 1)) → Leaf → Parent level) where
  adjacent_refines :
    ∀ interval : Fin levelCount,
      ∀ first second : Leaf,
        parent interval.succ first = parent interval.succ second →
          parent interval.castSucc first = parent interval.castSucc second

/--
Adjacent refinement data only on intervals away from the formal root and
identity bottom.

The endpoint intervals can be recovered whenever the root parent type is
subsingleton and the bottom parent map is injective.
-/
structure InteriorFiniteParentMapRefinement
    (Leaf : Type*)
    {levelCount : ℕ}
    (Parent : Fin (levelCount + 1) → Type*)
    (parent : (level : Fin (levelCount + 1)) → Leaf → Parent level) where
  interior_refines :
    ∀ interval : Fin levelCount,
      interval.castSucc ≠ 0 →
      interval.succ ≠ Fin.last levelCount →
      ∀ first second : Leaf,
        parent interval.succ first = parent interval.succ second →
          parent interval.castSucc first = parent interval.castSucc second

namespace AdjacentFiniteParentMapRefinement

variable {Leaf : Type*} {levelCount : ℕ}
variable {Parent : Fin (levelCount + 1) → Type*}
variable {parent : (level : Fin (levelCount + 1)) → Leaf → Parent level}

/-- Equality of fine parent labels propagates to every coarser level. -/
lemma parent_eq_of_le
    (H : AdjacentFiniteParentMapRefinement Leaf Parent parent)
    (coarse fine : Fin (levelCount + 1))
    (hcoarseFine : coarse ≤ fine)
    (first second : Leaf)
    (hfine : parent fine first = parent fine second) :
    parent coarse first = parent coarse second := by
  have haux :
      ∀ distance : ℕ,
      ∀ hbound : coarse.val + distance ≤ levelCount,
        parent
            ⟨coarse.val + distance,
              Nat.lt_succ_of_le hbound⟩ first =
          parent
            ⟨coarse.val + distance,
              Nat.lt_succ_of_le hbound⟩ second →
        parent coarse first = parent coarse second := by
    intro distance
    induction distance with
    | zero =>
        intro hbound heq
        simpa using heq
    | succ distance inductionHypothesis =>
        intro hbound heq
        have hpreviousBound :
            coarse.val + distance ≤ levelCount := by
          omega
        let interval : Fin levelCount :=
          ⟨coarse.val + distance, by omega⟩
        have hsuccessor :
            interval.succ =
              (⟨coarse.val + (distance + 1),
                Nat.lt_succ_of_le hbound⟩ :
                Fin (levelCount + 1)) := by
          apply Fin.ext
          simp [interval]
          omega
        have hstep :
            parent interval.castSucc first =
              parent interval.castSucc second := by
          apply H.adjacent_refines interval first second
          rw [hsuccessor]
          exact heq
        apply inductionHypothesis hpreviousBound
        simpa [interval] using hstep
  let distance := fine.val - coarse.val
  have hposition : coarse.val + distance = fine.val := by
    dsimp only [distance]
    omega
  have hbound : coarse.val + distance ≤ levelCount := by
    rw [hposition]
    omega
  apply haux distance hbound
  have hindex :
      (⟨coarse.val + distance,
          Nat.lt_succ_of_le hbound⟩ :
        Fin (levelCount + 1)) = fine := by
    apply Fin.ext
    exact hposition
  rw [hindex]
  exact hfine

/-- The long-range transition induced by a representative leaf of the finer
parent. -/
def transition
    (H : AdjacentFiniteParentMapRefinement Leaf Parent parent)
    (parent_surjective :
      ∀ level, Function.Surjective (parent level))
    (coarse fine : Fin (levelCount + 1))
    (_hcoarseFine : coarse ≤ fine) :
    Parent fine → Parent coarse :=
  fun fineParent =>
    parent coarse
      (Function.surjInv (parent_surjective fine) fineParent)

/-- The induced transition is compatible with every leaf parent assignment. -/
lemma transition_parent_compatible
    (H : AdjacentFiniteParentMapRefinement Leaf Parent parent)
    (parent_surjective :
      ∀ level, Function.Surjective (parent level))
    (coarse fine : Fin (levelCount + 1))
    (hcoarseFine : coarse ≤ fine)
    (leaf : Leaf) :
    H.transition parent_surjective coarse fine hcoarseFine
        (parent fine leaf) =
      parent coarse leaf := by
  let representative :=
    Function.surjInv (parent_surjective fine) (parent fine leaf)
  have hfine :
      parent fine representative = parent fine leaf :=
    Function.surjInv_eq (parent_surjective fine) (parent fine leaf)
  exact H.parent_eq_of_le coarse fine hcoarseFine representative leaf hfine

end AdjacentFiniteParentMapRefinement

namespace InteriorFiniteParentMapRefinement

variable {Leaf : Type*} {levelCount : ℕ}
variable {Parent : Fin (levelCount + 1) → Type*}
variable {parent : (level : Fin (levelCount + 1)) → Leaf → Parent level}

/--
Root uniqueness and bottom injectivity complete interior refinement to every
adjacent interval.
-/
def toAdjacent
    (H : InteriorFiniteParentMapRefinement Leaf Parent parent)
    (root_unique :
      ∀ first second : Parent (0 : Fin (levelCount + 1)),
        first = second)
    (bottom_injective :
      Function.Injective (parent (Fin.last levelCount))) :
    AdjacentFiniteParentMapRefinement Leaf Parent parent where
  adjacent_refines interval first second hfine := by
    by_cases hroot : interval.castSucc = 0
    · rw [hroot]
      exact root_unique _ _
    · by_cases hbottom : interval.succ = Fin.last levelCount
      · have hleaf : first = second := by
          rw [hbottom] at hfine
          apply bottom_injective
          exact hfine
        rw [hleaf]
      · exact
          H.interior_refines interval hroot hbottom
            first second hfine

end InteriorFiniteParentMapRefinement

/-- Adjacent partition refinement for the parent maps of one conditional grid
structure. -/
abbrev AdjacentGridParentRefinement
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one) :=
  AdjacentFiniteParentMapRefinement
    (Fin F.card)
    (fun level : UniformScaleIndex delta =>
      Fin (U.coarse level).card)
    (fun level => (U.cover level).parent)

/--
The minimal transition data expected from the geometric fixed-tree producer.

Only adjacent fine-to-coarse transitions are stored.  Compatibility with the
bottom parent assignments automatically implies adjacent partition
refinement and hence all long-range transitions.
-/
structure AdjacentGridParentTransitionSystem
    {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := localC) F hdelta_le_one) where
  transition :
    ∀ interval : Fin (uniformScaleSteps delta),
      Fin (U.coarse interval.succ).card →
        Fin (U.coarse interval.castSucc).card
  parent_compatible :
    ∀ (interval : Fin (uniformScaleSteps delta))
      (original : Fin F.card),
      transition interval
          ((U.cover interval.succ).parent original) =
        (U.cover interval.castSucc).parent original

namespace AdjacentGridParentRefinement

variable {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
  depth (A := A) (C := localC) F hdelta_le_one}

/-- Adjacent partition refinement supplies the exact fixed grid hierarchy
consumed by coherent localized composition. -/
def toCoherentGridParentHierarchy
    (H : AdjacentGridParentRefinement U) :
    CoherentGridParentHierarchy U where
  transition coarse fine hcoarseFine :=
    H.transition
      (fun level => (U.cover level).parent_surjective)
      coarse fine hcoarseFine
  parent_compatible coarse fine hcoarseFine original :=
    H.transition_parent_compatible
      (fun level => (U.cover level).parent_surjective)
      coarse fine hcoarseFine original

end AdjacentGridParentRefinement

namespace AdjacentGridParentTransitionSystem

variable {depth : ℕ} {delta A localC : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
  depth (A := A) (C := localC) F hdelta_le_one}

/-- Adjacent transition compatibility implies adjacent fiber refinement. -/
def toAdjacentGridParentRefinement
    (H : AdjacentGridParentTransitionSystem U) :
    AdjacentGridParentRefinement U where
  adjacent_refines interval first second hfine := by
    calc
      (U.cover interval.castSucc).parent first
          =
        H.transition interval
          ((U.cover interval.succ).parent first) :=
            (H.parent_compatible interval first).symm
      _ =
        H.transition interval
          ((U.cover interval.succ).parent second) :=
            congrArg (H.transition interval) hfine
      _ = (U.cover interval.castSucc).parent second :=
        H.parent_compatible interval second

/-- Adjacent transition data generates the complete coherent grid hierarchy. -/
def toCoherentGridParentHierarchy
    (H : AdjacentGridParentTransitionSystem U) :
    CoherentGridParentHierarchy U :=
  H.toAdjacentGridParentRefinement.toCoherentGridParentHierarchy

end AdjacentGridParentTransitionSystem

end Kakeya.Streamlined
