import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConditionalFactors
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConditionalBranchJointUniformity

/-!
# All-branch conditional factor scopes

A Section 7 factor fixes a list of previously selected scales, but its
endpoint estimates quantify over every nonempty parent cell for those scales.
Thus the global recursive object must not fix one parent assignment.

Every nonempty cell is represented by any original fine index in that cell.
This finite parametrization may repeat the same cell, which is harmless for
maxima and universal bounds.  Appending a middle scale therefore represents
all nonempty child cells without introducing a transition map.
-/

noncomputable section

namespace Kakeya.Streamlined

/--
One all-branch factor scope.

`scale` records only the historical conditional coordinates.  Parent values
remain universally quantified through `parentOf`.
-/
structure FrostmanConditionalFactorScope
    {depth : ℕ} {delta A C : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := C) F hdelta_le_one) where
  coordinateCount : ℕ
  coordinateCount_le : coordinateCount ≤ depth
  scale : Fin coordinateCount → UniformScaleIndex delta
  fine : UniformScaleIndex delta
  coarse : UniformScaleIndex delta
  fineScale_le_coarseScale :
    (uniformScale delta hdelta_le_one fine).1 ≤
      (uniformScale delta hdelta_le_one coarse).1

namespace FrostmanConditionalFactorScope

variable {depth : ℕ} {delta A C : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
  depth (A := A) (C := C) F hdelta_le_one}

/-- Parent values of one represented cell. -/
def parentOf
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card) :
    Fin P.coordinateCount → ℕ :=
  fun t => ((U.cover (P.scale t)).parent i).val

/-- Every represented conditional cell contains its representing fine index. -/
lemma mem_cell_parentOf
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card) :
    i ∈ conditionalParentCell U.coarse U.cover P.scale (P.parentOf i) := by
  rw [mem_conditionalParentCell_iff]
  intro t
  rfl

/-- Every represented conditional cell is nonempty. -/
lemma cell_parentOf_nonempty
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card) :
    (conditionalParentCell U.coarse U.cover
      P.scale (P.parentOf i)).Nonempty :=
  ⟨i, P.mem_cell_parentOf i⟩

/-- Build the branch address represented by one original fine index. -/
def address
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card) :
    FrostmanConditionalFactor U where
  coordinateCount := P.coordinateCount
  coordinateCount_le := P.coordinateCount_le
  scale := P.scale
  parent := P.parentOf i
  cell_nonempty := P.cell_parentOf_nonempty i
  branchSystem :=
    Classical.choice <|
      U.exists_conditionalBranchSystem
        P.coordinateCount_le P.scale (P.parentOf i)
  fine := P.fine
  coarse := P.coarse
  fineScale_le_coarseScale := P.fineScale_le_coarseScale

/-- Every represented branch family inherits ambient unit-ball containment. -/
lemma address_family_isInUnitBall
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (hF_ball : F.IsInUnitBall) :
    (P.address i).family.IsInUnitBall := by
  intro localIndex
  change
    ((TubeSubfamily.fromFinset F
      (conditionalParentCell U.coarse U.cover
        P.scale (P.parentOf i))).family.tube localIndex).IsInUnitBall
  rw [(TubeSubfamily.fromFinset F
    (conditionalParentCell U.coarse U.cover
      P.scale (P.parentOf i))).tube_eq localIndex]
  exact hF_ball _

/-- The canonical local index of the representing fine tube. -/
def addressIndex
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card) :
    Fin (P.address i).family.card := by
  let I :=
    conditionalParentCell U.coarse U.cover P.scale (P.parentOf i)
  exact (I.orderIsoOfFin rfl).symm ⟨i, P.mem_cell_parentOf i⟩

/-- The canonical local index embeds back to its representing fine index. -/
@[simp] lemma address_embedding_addressIndex
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card) :
    (TubeSubfamily.fromFinset F
      (conditionalParentCell U.coarse U.cover
        P.scale (P.parentOf i))).embedding (P.addressIndex i) = i := by
  let I :=
    conditionalParentCell U.coarse U.cover P.scale (P.parentOf i)
  change I.orderEmbOfFin rfl
      ((I.orderIsoOfFin rfl).symm ⟨i, P.mem_cell_parentOf i⟩) = i
  exact congrArg Subtype.val
    ((I.orderIsoOfFin rfl).apply_symm_apply
      ⟨i, P.mem_cell_parentOf i⟩)

/-- Local endpoint parent containing the representing fine tube. -/
def addressEndpointParent
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (s : UniformScaleIndex delta) :
    Fin ((P.address i).dilated.coarse s).card :=
  ((P.address i).dilated.cover s).parent
    (P.addressIndex i)

/-- The local endpoint parent has the expected ambient parent identity. -/
lemma addressEndpointParent_ambient
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (s : UniformScaleIndex delta) :
    ((P.address i).branchSystem.selectedCoarse s).embedding
        (P.addressEndpointParent i s) =
      (U.cover s).parent i := by
  rw [addressEndpointParent]
  change
    ((P.address i).branchSystem.selectedCoarse s).embedding
        (((P.address i).branchSystem.restrictedCover s).parent
          (P.addressIndex i)) =
      (U.cover s).parent i
  rw [(P.address i).branchSystem.parent_compatible s (P.addressIndex i)]
  change
    (U.cover s).parent
      ((TubeSubfamily.fromFinset F
        (conditionalParentCell U.coarse U.cover
          P.scale (P.parentOf i))).embedding (P.addressIndex i)) =
      (U.cover s).parent i
  rw [P.address_embedding_addressIndex i]

/--
Every represented parent cell has a complete branch-local joint-uniform
paper-grid structure while one further split remains available.
-/
def jointAddress
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount + 1 ≤ depth)
    (i : Fin F.card) :
    JointUniformLocalDilatedDiscreteUniformTubeStructure
      (A := A) (C := C)
      (P.address i).family hdelta_le_one :=
  (P.address i).branchSystem.toJoint hroom

@[simp] lemma jointAddress_uniformity
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount + 1 ≤ depth)
    (i : Fin F.card) :
    (P.jointAddress hroom i).uniformity = U.uniformity :=
  U.assigned_to_full.symm

/-- The joint view forgets to the same branch-local dilated structure. -/
lemma jointAddress_assignedRelationFrostmanConstant
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount + 1 ≤ depth)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta)
    (k : Fin ((P.address i).dilated.coarse s).card) :
    (P.jointAddress hroom i).toDilated.assignedRelationFrostmanConstant
        r s k =
      (P.address i).dilated.assignedRelationFrostmanConstant r s k :=
  rfl

/-- Fine absolute scale of a scope. -/
def fineScale (P : FrostmanConditionalFactorScope U) : ℝ :=
  (uniformScale delta hdelta_le_one P.fine).1

/-- Coarse absolute scale of a scope. -/
def coarseScale (P : FrostmanConditionalFactorScope U) : ℝ :=
  (uniformScale delta hdelta_le_one P.coarse).1

/-- Relative paper scale of a scope. -/
def relativeScale (P : FrostmanConditionalFactorScope U) : ℝ :=
  P.fineScale / P.coarseScale

lemma fineScale_pos
    (hdelta : 0 < delta) (P : FrostmanConditionalFactorScope U) :
    0 < P.fineScale :=
  lt_of_lt_of_le hdelta
    (uniformScale delta hdelta_le_one P.fine).property.1

lemma coarseScale_pos
    (hdelta : 0 < delta) (P : FrostmanConditionalFactorScope U) :
    0 < P.coarseScale :=
  lt_of_lt_of_le hdelta
    (uniformScale delta hdelta_le_one P.coarse).property.1

lemma relativeScale_pos
    (hdelta : 0 < delta) (P : FrostmanConditionalFactorScope U) :
    0 < P.relativeScale :=
  div_pos (P.fineScale_pos hdelta) (P.coarseScale_pos hdelta)

lemma relativeScale_le_one
    (hdelta : 0 < delta) (P : FrostmanConditionalFactorScope U) :
    P.relativeScale ≤ 1 := by
  exact (div_le_one (P.coarseScale_pos hdelta)).2
    P.fineScale_le_coarseScale

/-- Replace only the displayed endpoints while retaining the same historical
conditional coordinates. -/
def withEndpoints
    (P : FrostmanConditionalFactorScope U)
    (fine coarse : UniformScaleIndex delta)
    (hfineCoarse :
      (uniformScale delta hdelta_le_one fine).1 ≤
        (uniformScale delta hdelta_le_one coarse).1) :
    FrostmanConditionalFactorScope U where
  coordinateCount := P.coordinateCount
  coordinateCount_le := P.coordinateCount_le
  scale := P.scale
  fine := fine
  coarse := coarse
  fineScale_le_coarseScale := hfineCoarse

/-- The all-branch inner child appends the selected middle scale. -/
def innerChild
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1) :
    FrostmanConditionalFactorScope U where
  coordinateCount := P.coordinateCount + 1
  coordinateCount_le := by omega
  scale := appendConditionalScale P.scale middle
  fine := P.fine
  coarse := middle
  fineScale_le_coarseScale := hfine_middle

/-- Historical scales are unchanged in the inner child. -/
@[simp] lemma innerChild_scale_castSucc
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1)
    (t : Fin P.coordinateCount) :
    (P.innerChild hroom middle hfine_middle).scale t.castSucc =
      P.scale t := by
  change appendConditionalScale P.scale middle t.castSucc = P.scale t
  rw [appendConditionalScale_castSucc]

/-- The new inner-child scale coordinate is the middle scale. -/
@[simp] lemma innerChild_scale_last
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1) :
    (P.innerChild hroom middle hfine_middle).scale
        (Fin.last P.coordinateCount) = middle := by
  change appendConditionalScale P.scale middle
      (Fin.last P.coordinateCount) = middle
  rw [appendConditionalScale_last]

/-- Historical parent values are unchanged in the inner child. -/
@[simp] lemma innerChild_parentOf_castSucc
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1)
    (i : Fin F.card)
    (t : Fin P.coordinateCount) :
    (P.innerChild hroom middle hfine_middle).parentOf i t.castSucc =
      P.parentOf i t := by
  unfold parentOf
  rw [show (P.innerChild hroom middle hfine_middle).scale =
      appendConditionalScale P.scale middle by rfl]
  rw [appendConditionalScale_castSucc]

/-- The new inner-child parent coordinate is the middle-scale parent. -/
@[simp] lemma innerChild_parentOf_last
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1)
    (i : Fin F.card) :
    (P.innerChild hroom middle hfine_middle).parentOf i
        (Fin.last P.coordinateCount) =
      ((U.cover middle).parent i).val := by
  unfold parentOf
  rw [show (P.innerChild hroom middle hfine_middle).scale =
      appendConditionalScale P.scale middle by rfl]
  rw [appendConditionalScale_last]

/-- Full parent-assignment form for an inner-child represented cell. -/
lemma innerChild_parentOf
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1)
    (i : Fin F.card) :
    (P.innerChild hroom middle hfine_middle).parentOf i =
      appendConditionalParent (P.parentOf i)
        ((U.cover middle).parent i).val := by
  funext t
  refine Fin.lastCases ?_ (fun old => ?_) t
  · rw [innerChild_parentOf_last, appendConditionalParent_last]
  · rw [innerChild_parentOf_castSucc,
      appendConditionalParent_castSucc]

/-- The all-branch outer child retains the historical coordinates. -/
def outerChild
    (P : FrostmanConditionalFactorScope U)
    (middle : UniformScaleIndex delta)
    (hmiddle_coarse :
      (uniformScale delta hdelta_le_one middle).1 ≤
        (uniformScale delta hdelta_le_one P.coarse).1) :
    FrostmanConditionalFactorScope U where
  coordinateCount := P.coordinateCount
  coordinateCount_le := P.coordinateCount_le
  scale := P.scale
  fine := middle
  coarse := P.coarse
  fineScale_le_coarseScale := hmiddle_coarse

@[simp] lemma innerChild_coordinateCount
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1) :
    (P.innerChild hroom middle hfine_middle).coordinateCount =
      P.coordinateCount + 1 :=
  rfl

@[simp] lemma outerChild_coordinateCount
    (P : FrostmanConditionalFactorScope U)
    (middle : UniformScaleIndex delta)
    (hmiddle_coarse :
      (uniformScale delta hdelta_le_one middle).1 ≤
        (uniformScale delta hdelta_le_one P.coarse).1) :
    (P.outerChild middle hmiddle_coarse).coordinateCount =
      P.coordinateCount :=
  rfl

@[simp] lemma innerChild_fineScale
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1) :
    (P.innerChild hroom middle hfine_middle).fineScale =
      P.fineScale :=
  rfl

@[simp] lemma innerChild_coarseScale
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1) :
    (P.innerChild hroom middle hfine_middle).coarseScale =
      (uniformScale delta hdelta_le_one middle).1 :=
  rfl

@[simp] lemma outerChild_fineScale
    (P : FrostmanConditionalFactorScope U)
    (middle : UniformScaleIndex delta)
    (hmiddle_coarse :
      (uniformScale delta hdelta_le_one middle).1 ≤
        (uniformScale delta hdelta_le_one P.coarse).1) :
    (P.outerChild middle hmiddle_coarse).fineScale =
      (uniformScale delta hdelta_le_one middle).1 :=
  rfl

@[simp] lemma outerChild_coarseScale
    (P : FrostmanConditionalFactorScope U)
    (middle : UniformScaleIndex delta)
    (hmiddle_coarse :
      (uniformScale delta hdelta_le_one middle).1 ≤
        (uniformScale delta hdelta_le_one P.coarse).1) :
    (P.outerChild middle hmiddle_coarse).coarseScale =
      P.coarseScale :=
  rfl

/-- A scope split preserves the represented relative scale exactly. -/
lemma innerChild_relativeScale_mul_outerChild_relativeScale
    (hdelta : 0 < delta)
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1)
    (hmiddle_coarse :
      (uniformScale delta hdelta_le_one middle).1 ≤
        (uniformScale delta hdelta_le_one P.coarse).1) :
    (P.innerChild hroom middle hfine_middle).relativeScale *
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

end FrostmanConditionalFactorScope

end Kakeya.Streamlined
