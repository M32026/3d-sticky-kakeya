import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PacketCellExactification

/-!
# Proposition 6.2: the reference parent-degree scale

For a surviving reference parent `P`, let `K(P)` be the number of selected
packet-cells incident to `P`.  The multiplicity class gives

`muFine * K(P) ≤ w(P) < 2 * muFine * K(P)`,

while the parent-weight class makes all `w(P)` comparable within a factor
two.  Hence any two positive reference parent degrees differ by a strict
factor less than four.

The common paper scale `K` is the minimum reference parent degree.  This
module performs no new selection.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62PacketCellInput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput cover shading)
    (multiplicity : input.FineMultiplicityClassData)
    (parentClass : input.ParentClassData multiplicity)
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        coarse ambientConstant scaleWindow}
    (treeCleanup :
      input.ParentTreeCleanupData
        multiplicity parentClass schedule)
    (exactification :
      input.PacketCellExactificationData
        multiplicity parentClass treeCleanup)

/-- `K(P)` on the literal pair set underlying the incidence graph. -/
def referenceParentDegree
    (parent : Fin coarse.card) : ℕ :=
  ((input.referencePairs multiplicity parentClass treeCleanup).filter
    fun pair => pair.1 = parent).card

theorem referencePairsAt_eq_selectedPairsAt
    {parent : Fin coarse.card}
    (parentMem : parent ∈ treeCleanup.referenceParents) :
    (input.referencePairs multiplicity parentClass treeCleanup).filter
        (fun pair => pair.1 = parent) =
      input.selectedPairsAt multiplicity parent := by
  ext pair
  simp only [
    Finset.mem_filter,
    input.mem_referencePairs_iff,
    selectedPairsAt
  ]
  constructor
  · rintro ⟨⟨pairSelected, _pairParentMem⟩, pairParent⟩
    exact ⟨pairSelected, pairParent⟩
  · rintro ⟨pairSelected, pairParent⟩
    exact
      ⟨⟨pairSelected, by simpa [pairParent] using parentMem⟩,
        pairParent⟩

theorem incidence_parentDegree_eq
    (parent : Fin coarse.card) :
    exactification.incidence.parentDegree
        exactification.incidence.allEdges parent =
      input.referenceParentDegree
        multiplicity parentClass treeCleanup parent := by
  let edges := exactification.incidence.edgePool
  have univ_eq_attach :
      (Finset.univ : Finset exactification.incidence.Edge) =
        edges.attach := by
    ext edge
    simp [edges]
  unfold PureWZ2Prop62FourDegreeIncidenceData.parentDegree
  unfold PureWZ2Prop62FourDegreeIncidenceData.allEdges
  rw [univ_eq_attach]
  change
    ((edges.attach.filter fun edge =>
      edge.1.1 = parent).card) =
      ((input.referencePairs
        multiplicity parentClass treeCleanup).filter
          fun pair => pair.1 = parent).card
  have filterCard :
      (edges.attach.filter fun edge =>
          edge.1.1 = parent).card =
        (edges.filter fun pair =>
          pair.1 = parent).card := by
    have filterEquality :=
      Finset.filter_attach
        (fun pair :
          Fin coarse.card × WZ2PaperCellIndex =>
            pair.1 = parent)
        edges
    have cardEquality :=
      congrArg Finset.card filterEquality
    simpa only [Finset.card_map, Finset.card_attach] using
      cardEquality
  rw [filterCard]
  change
    (edges.filter fun pair => pair.1 = parent).card =
      ((input.referencePairs
        multiplicity parentClass treeCleanup).filter
          fun pair => pair.1 = parent).card
  rw [show edges =
      input.referencePairs
        multiplicity parentClass treeCleanup from
    exactification.incidence_edgePool_eq]

theorem referenceParentDegree_pos
    {parent : Fin coarse.card}
    (parentMem : parent ∈ treeCleanup.referenceParents) :
    0 <
      input.referenceParentDegree
        multiplicity parentClass treeCleanup parent := by
  rw [referenceParentDegree,
    input.referencePairsAt_eq_selectedPairsAt
      multiplicity parentClass treeCleanup parentMem]
  exact
    (ParentTreeCleanupData.reference_parent_has_selected_pair
      input multiplicity parentClass schedule
      treeCleanup parentMem).card_pos

theorem muFine_mul_referenceParentDegree_le_weight
    {parent : Fin coarse.card}
    (parentMem : parent ∈ treeCleanup.referenceParents) :
    multiplicity.muFine *
        input.referenceParentDegree
          multiplicity parentClass treeCleanup parent ≤
      input.parentIncidenceWeight multiplicity parent := by
  rw [referenceParentDegree,
    input.referencePairsAt_eq_selectedPairsAt
      multiplicity parentClass treeCleanup parentMem]
  unfold parentIncidenceWeight
  have lower :
      ∀ pair ∈ input.selectedPairsAt multiplicity parent,
        multiplicity.muFine ≤
          input.packetCellMultiplicity pair := by
    intro pair pairMem
    exact
      (multiplicity.multiplicity_band pair
        (Finset.mem_filter.mp pairMem).1).1
  simpa [Nat.mul_comm] using
    Finset.card_nsmul_le_sum
      (input.selectedPairsAt multiplicity parent)
      input.packetCellMultiplicity multiplicity.muFine lower

theorem weight_lt_two_muFine_mul_referenceParentDegree
    {parent : Fin coarse.card}
    (parentMem : parent ∈ treeCleanup.referenceParents) :
    input.parentIncidenceWeight multiplicity parent <
      2 * multiplicity.muFine *
        input.referenceParentDegree
          multiplicity parentClass treeCleanup parent := by
  rw [referenceParentDegree,
    input.referencePairsAt_eq_selectedPairsAt
      multiplicity parentClass treeCleanup parentMem]
  unfold parentIncidenceWeight
  let pairs := input.selectedPairsAt multiplicity parent
  have pairsNonempty : pairs.Nonempty :=
    ParentTreeCleanupData.reference_parent_has_selected_pair
      input multiplicity parentClass schedule treeCleanup parentMem
  have pointwiseLe :
      ∀ pair ∈ pairs,
        input.packetCellMultiplicity pair ≤
          2 * multiplicity.muFine := by
    intro pair pairMem
    exact
      (multiplicity.multiplicity_band pair
        (Finset.mem_filter.mp pairMem).1).2.le
  have pointwiseStrict :
      ∃ pair ∈ pairs,
        input.packetCellMultiplicity pair <
          2 * multiplicity.muFine := by
    rcases pairsNonempty with ⟨pair, pairMem⟩
    exact
      ⟨pair, pairMem,
        (multiplicity.multiplicity_band pair
          (Finset.mem_filter.mp pairMem).1).2⟩
  have strictSum :
      (∑ pair ∈ pairs,
          input.packetCellMultiplicity pair) <
        ∑ _pair ∈ pairs,
          2 * multiplicity.muFine := by
    exact Finset.sum_lt_sum pointwiseLe pointwiseStrict
  simpa [pairs, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using strictSum

theorem referenceParentDegree_lt_four_mul
    {first second : Fin coarse.card}
    (firstMem : first ∈ treeCleanup.referenceParents)
    (secondMem : second ∈ treeCleanup.referenceParents) :
    input.referenceParentDegree
        multiplicity parentClass treeCleanup first <
      4 *
        input.referenceParentDegree
          multiplicity parentClass treeCleanup second := by
  have firstLower :=
    input.muFine_mul_referenceParentDegree_le_weight
      multiplicity parentClass treeCleanup firstMem
  have firstWeightUpper :
      input.parentIncidenceWeight multiplicity first <
        2 * parentClass.weightFloor :=
    (treeCleanup.reference_weight_band first firstMem).2
  have secondWeightLower :
      parentClass.weightFloor ≤
        input.parentIncidenceWeight multiplicity second :=
    (treeCleanup.reference_weight_band second secondMem).1
  have secondUpper :=
    input.weight_lt_two_muFine_mul_referenceParentDegree
      multiplicity parentClass treeCleanup secondMem
  have multiplied :
      multiplicity.muFine *
          input.referenceParentDegree
            multiplicity parentClass treeCleanup first <
        multiplicity.muFine *
          (4 *
            input.referenceParentDegree
              multiplicity parentClass treeCleanup second) := by
    calc
      multiplicity.muFine *
          input.referenceParentDegree
            multiplicity parentClass treeCleanup first ≤
          input.parentIncidenceWeight multiplicity first :=
        firstLower
      _ < 2 * parentClass.weightFloor :=
        firstWeightUpper
      _ ≤
          2 *
            input.parentIncidenceWeight multiplicity second := by
        exact Nat.mul_le_mul_left 2 secondWeightLower
      _ <
          2 *
            (2 * multiplicity.muFine *
              input.referenceParentDegree
                multiplicity parentClass treeCleanup second) := by
        exact Nat.mul_lt_mul_of_pos_left secondUpper (by norm_num)
      _ =
          multiplicity.muFine *
            (4 *
              input.referenceParentDegree
                multiplicity parentClass treeCleanup second) := by
        ring
  exact Nat.lt_of_mul_lt_mul_left multiplied

structure ReferenceParentDegreeData where
  degreeValues : Finset ℕ
  degreeValues_eq :
    degreeValues =
      treeCleanup.referenceParents.image fun parent =>
        input.referenceParentDegree
          multiplicity parentClass treeCleanup parent
  degreeValues_nonempty : degreeValues.Nonempty
  K : ℕ
  K_eq : K = degreeValues.min' degreeValues_nonempty
  K_pos : 0 < K
  degree_band :
    ∀ parent ∈ treeCleanup.referenceParents,
      K ≤
          input.referenceParentDegree
            multiplicity parentClass treeCleanup parent ∧
        input.referenceParentDegree
            multiplicity parentClass treeCleanup parent <
          4 * K
  incidence_degree_band :
    ∀ parent ∈
        exactification.incidence.activeParents
          exactification.incidence.allEdges,
      K ≤
          exactification.incidence.parentDegree
            exactification.incidence.allEdges parent ∧
        exactification.incidence.parentDegree
            exactification.incidence.allEdges parent <
          4 * K

theorem pureWZ2_prop62_reference_parent_degree :
    Nonempty
      (input.ReferenceParentDegreeData
        multiplicity parentClass treeCleanup exactification) := by
  let degreeValues : Finset ℕ :=
    treeCleanup.referenceParents.image fun parent =>
      input.referenceParentDegree
        multiplicity parentClass treeCleanup parent
  have degreeValuesNonempty : degreeValues.Nonempty :=
    treeCleanup.referenceParents_nonempty.image _
  let K := degreeValues.min' degreeValuesNonempty
  have KMem : K ∈ degreeValues :=
    Finset.min'_mem degreeValues degreeValuesNonempty
  rcases Finset.mem_image.mp KMem with
    ⟨minParent, minParentMem, minParentDegree⟩
  have KPos : 0 < K := by
    rw [← minParentDegree]
    exact
      input.referenceParentDegree_pos
        multiplicity parentClass treeCleanup minParentMem
  have degreeBand :
      ∀ parent ∈ treeCleanup.referenceParents,
        K ≤
            input.referenceParentDegree
              multiplicity parentClass treeCleanup parent ∧
          input.referenceParentDegree
              multiplicity parentClass treeCleanup parent <
            4 * K := by
    intro parent parentMem
    constructor
    · apply Finset.min'_le degreeValues
      exact
        Finset.mem_image.mpr
          ⟨parent, parentMem, rfl⟩
    · rw [← minParentDegree]
      exact
        input.referenceParentDegree_lt_four_mul
          multiplicity parentClass treeCleanup parentMem minParentMem
  exact
    ⟨{
      degreeValues := degreeValues
      degreeValues_eq := rfl
      degreeValues_nonempty := degreeValuesNonempty
      K := K
      K_eq := rfl
      K_pos := KPos
      degree_band := degreeBand
      incidence_degree_band := by
        intro parent parentActive
        have parentMem :
            parent ∈ treeCleanup.referenceParents :=
          (exactification.active_parent_iff parent).mp parentActive
        rw [
          incidence_parentDegree_eq
            input multiplicity parentClass treeCleanup
              exactification parent
        ]
        exact degreeBand parent parentMem
    }⟩

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
