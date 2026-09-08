import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConditionalBranchSystem
import MyLeanRepo.Kakeya.Streamlined.DividingScales.FrostmanProfiles

/-!
# Conditional factor addresses for the dividing-scales recursion

The recursive state in Section 7 is a finite family of branch-local factors,
not one global partition of the paper grid.  A branch is cut out directly by
ambient parent coordinates from the independent covers.  Splitting a factor
appends the selected middle parent only to the inner child.  The outer child
keeps the old branch context and raises its fine endpoint to the middle scale.

The objects below are addresses into the ambient independent cover system.
They deliberately do not claim that the original `delta`-tube cell is already
the rescaled relative-scale tube family from the paper.  Local Frostman
profiles are read from the selected endpoint families instead.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- Append one ambient paper-grid scale to a conditional coordinate list. -/
def appendConditionalScale
    {delta : ℝ} {m : ℕ}
    (scale : Fin m → UniformScaleIndex delta)
    (r : UniformScaleIndex delta) :
    Fin (m + 1) → UniformScaleIndex delta :=
  Fin.snoc scale r

/-- Append one ambient parent value to a conditional coordinate list. -/
def appendConditionalParent
    {m : ℕ} (parent : Fin m → ℕ) (p : ℕ) :
    Fin (m + 1) → ℕ :=
  Fin.snoc parent p

@[simp] lemma appendConditionalScale_castSucc
    {delta : ℝ} {m : ℕ}
    (scale : Fin m → UniformScaleIndex delta)
    (r : UniformScaleIndex delta) (t : Fin m) :
    appendConditionalScale scale r t.castSucc = scale t := by
  simp [appendConditionalScale]

@[simp] lemma appendConditionalScale_last
    {delta : ℝ} {m : ℕ}
    (scale : Fin m → UniformScaleIndex delta)
    (r : UniformScaleIndex delta) :
    appendConditionalScale scale r (Fin.last m) = r := by
  simp [appendConditionalScale]

@[simp] lemma appendConditionalParent_castSucc
    {m : ℕ} (parent : Fin m → ℕ) (p : ℕ) (t : Fin m) :
    appendConditionalParent parent p t.castSucc = parent t := by
  simp [appendConditionalParent]

@[simp] lemma appendConditionalParent_last
    {m : ℕ} (parent : Fin m → ℕ) (p : ℕ) :
    appendConditionalParent parent p (Fin.last m) = p := by
  simp [appendConditionalParent]

/--
Membership after appending one coordinate is exactly old-cell membership
together with the new ambient parent identity.
-/
lemma mem_conditionalParentCell_append_iff
    {delta A C : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (coarse :
      ∀ k : UniformScaleIndex delta,
        TubeFamily (uniformScale delta hdelta_le_one k).1)
    (cover :
      ∀ k, LocalDilatedTubeCover A C F (coarse k))
    {m : ℕ}
    (scale : Fin m → UniformScaleIndex delta)
    (parent : Fin m → ℕ)
    (r : UniformScaleIndex delta) (p : ℕ)
    (i : Fin F.card) :
    i ∈ conditionalParentCell coarse cover
        (appendConditionalScale scale r)
        (appendConditionalParent parent p) ↔
      i ∈ conditionalParentCell coarse cover scale parent ∧
        ((cover r).parent i).val = p := by
  rw [mem_conditionalParentCell_iff]
  rw [mem_conditionalParentCell_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro t
      have ht := h t.castSucc
      rw [appendConditionalScale_castSucc,
        appendConditionalParent_castSucc] at ht
      exact ht
    · have hlast := h (Fin.last m)
      rw [appendConditionalScale_last,
        appendConditionalParent_last] at hlast
      exact hlast
  · rintro ⟨hold, hnew⟩ t
    refine Fin.lastCases ?_ (fun old => ?_) t
    · rw [appendConditionalScale_last,
        appendConditionalParent_last]
      exact hnew
    · rw [appendConditionalScale_castSucc,
        appendConditionalParent_castSucc]
      exact hold old

/--
One branch-local factor address in the Section 7 recursion.

The address records its exact conditional cell, a complete restricted cover
system on that cell, and one ordered interval of absolute paper-grid scales.
Its paper relative scale is `fineScale / coarseScale`.  No transition map
between the independent covers is added.
-/
structure FrostmanConditionalFactor
    {depth : ℕ} {delta A C : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := C) F hdelta_le_one) where
  coordinateCount : ℕ
  coordinateCount_le : coordinateCount ≤ depth
  scale : Fin coordinateCount → UniformScaleIndex delta
  parent : Fin coordinateCount → ℕ
  cell_nonempty :
    (conditionalParentCell U.coarse U.cover scale parent).Nonempty
  branchSystem : ConditionalBranchSystem U scale parent
  fine : UniformScaleIndex delta
  coarse : UniformScaleIndex delta
  fineScale_le_coarseScale :
    (uniformScale delta hdelta_le_one fine).1 ≤
      (uniformScale delta hdelta_le_one coarse).1

namespace FrostmanConditionalFactor

variable {depth : ℕ} {delta A C : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
  depth (A := A) (C := C) F hdelta_le_one}

/-- The original fine-tube subfamily represented by a factor. -/
abbrev family (P : FrostmanConditionalFactor U) : TubeFamily delta :=
  (TubeSubfamily.fromFinset F
    (conditionalParentCell U.coarse U.cover P.scale P.parent)).family

/-- The complete branch-local paper-grid structure carried by a factor. -/
abbrev branchLocal
    (P : FrostmanConditionalFactor U) :
    LocalDilatedDiscreteUniformTubeStructure
      (A := A) (C := C) P.family hdelta_le_one :=
  P.branchSystem.toLocal

/-- Forget local coaxial data while retaining the branch cover system. -/
abbrev dilated
    (P : FrostmanConditionalFactor U) :
    DilatedDiscreteUniformTubeStructure
      (A := A) P.family hdelta_le_one :=
  P.branchLocal.toDilated

/-- Every factor family is nonempty by its stored cell witness. -/
lemma family_nonempty (P : FrostmanConditionalFactor U) :
    P.family.Nonempty := by
  exact Finset.card_pos.mpr P.cell_nonempty

/-- Every branch-local structure has the ambient conditional uniformity. -/
@[simp] lemma branchLocal_uniformity (P : FrostmanConditionalFactor U) :
    P.branchLocal.uniformity = U.uniformity :=
  U.assigned_to_full.symm

/--
The conditional cell obtained by appending a selected local parent is
nonempty.  Surjectivity of the branch-local cover supplies a fine witness,
and parent compatibility identifies its ambient parent coordinate.
-/
lemma extendedCell_nonempty
    (P : FrostmanConditionalFactor U)
    (r : UniformScaleIndex delta)
    (j : Fin (P.branchLocal.coarse r).card) :
    (conditionalParentCell U.coarse U.cover
      (appendConditionalScale P.scale r)
      (appendConditionalParent P.parent
        ((P.branchSystem.selectedCoarse r).embedding j).val)).Nonempty := by
  classical
  let S := TubeSubfamily.fromFinset F
    (conditionalParentCell U.coarse U.cover P.scale P.parent)
  let Q := P.branchSystem.restrictedCover r
  rcases Q.parent_surjective j with ⟨i, hi⟩
  let original : Fin F.card := S.embedding i
  refine ⟨original, ?_⟩
  rw [mem_conditionalParentCell_append_iff]
  constructor
  · exact Finset.orderEmbOfFin_mem
      (conditionalParentCell U.coarse U.cover P.scale P.parent) rfl i
  · have hcompat := P.branchSystem.parent_compatible r i
    rw [show Q.parent i = j by exact hi] at hcompat
    exact congrArg Fin.val hcompat.symm

/--
Append one selected parent coordinate and build the complete restricted cover
system on the resulting child branch.
-/
def extend
    (P : FrostmanConditionalFactor U)
    (hroom : P.coordinateCount < depth)
    (r : UniformScaleIndex delta)
    (j : Fin (P.branchLocal.coarse r).card)
    (fine coarse : UniformScaleIndex delta)
    (hscales :
      (uniformScale delta hdelta_le_one fine).1 ≤
        (uniformScale delta hdelta_le_one coarse).1) :
    FrostmanConditionalFactor U where
  coordinateCount := P.coordinateCount + 1
  coordinateCount_le := by omega
  scale := appendConditionalScale P.scale r
  parent := appendConditionalParent P.parent
    ((P.branchSystem.selectedCoarse r).embedding j).val
  cell_nonempty := P.extendedCell_nonempty r j
  branchSystem :=
    Classical.choice <|
      U.exists_conditionalBranchSystem
        (show P.coordinateCount + 1 ≤ depth by omega)
        (appendConditionalScale P.scale r)
        (appendConditionalParent P.parent
          ((P.branchSystem.selectedCoarse r).embedding j).val)
  fine := fine
  coarse := coarse
  fineScale_le_coarseScale := hscales

/-- The inner child appends a middle-scale parent and keeps the fine endpoint. -/
def innerChild
    (P : FrostmanConditionalFactor U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (j : Fin (P.branchLocal.coarse middle).card)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1) :
    FrostmanConditionalFactor U :=
  P.extend hroom middle j P.fine middle hfine_middle

/--
The outer child keeps the old branch context and starts at the middle scale.

Only the inner child fixes a representative middle parent.  Appending a
coarse parent here would incorrectly replace the entire outer factor by one
of its fibers.
-/
def outerChild
    (P : FrostmanConditionalFactor U)
    (middle : UniformScaleIndex delta)
    (hmiddle_coarse :
      (uniformScale delta hdelta_le_one middle).1 ≤
        (uniformScale delta hdelta_le_one P.coarse).1) :
    FrostmanConditionalFactor U where
  coordinateCount := P.coordinateCount
  coordinateCount_le := P.coordinateCount_le
  scale := P.scale
  parent := P.parent
  cell_nonempty := P.cell_nonempty
  branchSystem := P.branchSystem
  fine := middle
  coarse := P.coarse
  fineScale_le_coarseScale := hmiddle_coarse

@[simp] lemma innerChild_coordinateCount
    (P : FrostmanConditionalFactor U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (j : Fin (P.branchLocal.coarse middle).card)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1) :
    (P.innerChild hroom middle j hfine_middle).coordinateCount =
      P.coordinateCount + 1 :=
  rfl

@[simp] lemma outerChild_coordinateCount
    (P : FrostmanConditionalFactor U)
    (middle : UniformScaleIndex delta)
    (hmiddle_coarse :
      (uniformScale delta hdelta_le_one middle).1 ≤
        (uniformScale delta hdelta_le_one P.coarse).1) :
    (P.outerChild middle hmiddle_coarse).coordinateCount =
      P.coordinateCount :=
  rfl

@[simp] lemma innerChild_fine
    (P : FrostmanConditionalFactor U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (j : Fin (P.branchLocal.coarse middle).card)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1) :
    (P.innerChild hroom middle j hfine_middle).fine = P.fine :=
  rfl

@[simp] lemma innerChild_coarse
    (P : FrostmanConditionalFactor U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (j : Fin (P.branchLocal.coarse middle).card)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1) :
    (P.innerChild hroom middle j hfine_middle).coarse = middle :=
  rfl

@[simp] lemma outerChild_fine
    (P : FrostmanConditionalFactor U)
    (middle : UniformScaleIndex delta)
    (hmiddle_coarse :
      (uniformScale delta hdelta_le_one middle).1 ≤
        (uniformScale delta hdelta_le_one P.coarse).1) :
    (P.outerChild middle hmiddle_coarse).fine = middle :=
  rfl

@[simp] lemma outerChild_coarse
    (P : FrostmanConditionalFactor U)
    (middle : UniformScaleIndex delta)
    (hmiddle_coarse :
      (uniformScale delta hdelta_le_one middle).1 ≤
        (uniformScale delta hdelta_le_one P.coarse).1) :
    (P.outerChild middle hmiddle_coarse).coarse = P.coarse :=
  rfl

/-- Fine absolute scale of one factor address. -/
def fineScale (P : FrostmanConditionalFactor U) : ℝ :=
  (uniformScale delta hdelta_le_one P.fine).1

/-- Coarse absolute scale of one factor address. -/
def coarseScale (P : FrostmanConditionalFactor U) : ℝ :=
  (uniformScale delta hdelta_le_one P.coarse).1

/-- The paper relative scale represented by this factor interval. -/
def relativeScale (P : FrostmanConditionalFactor U) : ℝ :=
  P.fineScale / P.coarseScale

lemma fineScale_pos
    (hdelta : 0 < delta) (P : FrostmanConditionalFactor U) :
    0 < P.fineScale :=
  lt_of_lt_of_le hdelta
    (uniformScale delta hdelta_le_one P.fine).property.1

lemma coarseScale_pos
    (hdelta : 0 < delta) (P : FrostmanConditionalFactor U) :
    0 < P.coarseScale :=
  lt_of_lt_of_le hdelta
    (uniformScale delta hdelta_le_one P.coarse).property.1

lemma relativeScale_pos
    (hdelta : 0 < delta) (P : FrostmanConditionalFactor U) :
    0 < P.relativeScale :=
  div_pos (P.fineScale_pos hdelta) (P.coarseScale_pos hdelta)

lemma relativeScale_le_one
    (hdelta : 0 < delta) (P : FrostmanConditionalFactor U) :
    P.relativeScale ≤ 1 := by
  exact (div_le_one (P.coarseScale_pos hdelta)).2
    P.fineScale_le_coarseScale

@[simp] lemma innerChild_fineScale
    (P : FrostmanConditionalFactor U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (j : Fin (P.branchLocal.coarse middle).card)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1) :
    (P.innerChild hroom middle j hfine_middle).fineScale =
      P.fineScale :=
  rfl

@[simp] lemma innerChild_coarseScale
    (P : FrostmanConditionalFactor U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (j : Fin (P.branchLocal.coarse middle).card)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1) :
    (P.innerChild hroom middle j hfine_middle).coarseScale =
      (uniformScale delta hdelta_le_one middle).1 :=
  rfl

@[simp] lemma outerChild_fineScale
    (P : FrostmanConditionalFactor U)
    (middle : UniformScaleIndex delta)
    (hmiddle_coarse :
      (uniformScale delta hdelta_le_one middle).1 ≤
        (uniformScale delta hdelta_le_one P.coarse).1) :
    (P.outerChild middle hmiddle_coarse).fineScale =
      (uniformScale delta hdelta_le_one middle).1 :=
  rfl

@[simp] lemma outerChild_coarseScale
    (P : FrostmanConditionalFactor U)
    (middle : UniformScaleIndex delta)
    (hmiddle_coarse :
      (uniformScale delta hdelta_le_one middle).1 ≤
        (uniformScale delta hdelta_le_one P.coarse).1) :
    (P.outerChild middle hmiddle_coarse).coarseScale =
      P.coarseScale :=
  rfl

/--
The two relative scales created by a split multiply exactly to the parent
relative scale.
-/
lemma innerChild_relativeScale_mul_outerChild_relativeScale
    (hdelta : 0 < delta)
    (P : FrostmanConditionalFactor U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (j : Fin (P.branchLocal.coarse middle).card)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1)
    (hmiddle_coarse :
      (uniformScale delta hdelta_le_one middle).1 ≤
        (uniformScale delta hdelta_le_one P.coarse).1) :
    (P.innerChild hroom middle j hfine_middle).relativeScale *
        (P.outerChild middle hmiddle_coarse).relativeScale =
      P.relativeScale := by
  have hmiddle :
      0 < (uniformScale delta hdelta_le_one middle).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one middle).property.1
  have hcoarse := P.coarseScale_pos hdelta
  dsimp only [relativeScale]
  rw [innerChild_fineScale, innerChild_coarseScale,
    outerChild_fineScale, outerChild_coarseScale]
  field_simp [hmiddle.ne', hcoarse.ne']

/-- Largest assigned relation-fiber Frostman profile on this factor interval. -/
def relationProfile (P : FrostmanConditionalFactor U) : ENNReal :=
  P.dilated.relationFrostmanMax
    P.family_nonempty P.fine P.coarse

/-- Local endpoint control for one relative-scale factor. -/
def IsRelationControlled
    (P : FrostmanConditionalFactor U)
    (exponent : ℝ) (bound : ENNReal) : Prop :=
  P.relationProfile ≤
    bound *
      Kakeya.realRpowENN
        (P.coarseScale / P.fineScale) exponent

end FrostmanConditionalFactor

end Kakeya.Streamlined
