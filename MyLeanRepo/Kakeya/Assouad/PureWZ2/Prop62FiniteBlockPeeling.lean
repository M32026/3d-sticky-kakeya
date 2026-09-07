import MyLeanRepo.Kakeya.Streamlined.Basic

/-!
# Proposition 6.2: finite block peeling with one-time charges

The simultaneous packet core repeatedly deletes one currently bad block.
Each block label can be charged only once, because the whole block is removed
when that label is used.  This finite lemma isolates that termination and
accounting argument.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem pureWZ2_prop62_finite_block_peeling
    {Edge Label : Type*}
    [DecidableEq Edge] [DecidableEq Label]
    (block : Label → Finset Edge)
    (bad : Finset Edge → Label → Prop)
    (charge : Label → ℕ)
    (bad_nonempty :
      ∀ edges label,
        bad edges label →
          (edges ∩ block label).Nonempty)
    (bad_card_le :
      ∀ edges label,
        bad edges label →
          (edges ∩ block label).card ≤ charge label)
    (initialEdges : Finset Edge)
    (labels : Finset Label) :
    ∃ core : Finset Edge,
      core ⊆ initialEdges ∧
      (∀ label ∈ labels, ¬bad core label) ∧
      (initialEdges \ core).card ≤
        ∑ label ∈ labels, charge label := by
  let P : ℕ → Prop := fun labelCount =>
    ∀ (currentLabels : Finset Label)
      (currentEdges : Finset Edge),
      currentLabels.card ≤ labelCount →
        ∃ core : Finset Edge,
          core ⊆ currentEdges ∧
          (∀ label ∈ currentLabels, ¬bad core label) ∧
          (currentEdges \ core).card ≤
            ∑ label ∈ currentLabels, charge label
  have main :
      ∀ labelCount,
        (∀ smaller, smaller < labelCount → P smaller) →
          P labelCount := by
    intro labelCount inductionHypothesis
      currentLabels currentEdges labelCard
    by_cases existsBad :
        ∃ label ∈ currentLabels, bad currentEdges label
    · rcases existsBad with ⟨label, labelMem, labelBad⟩
      let removedBlock : Finset Edge :=
        currentEdges ∩ block label
      let remainingEdges : Finset Edge :=
        currentEdges \ removedBlock
      let remainingLabels : Finset Label :=
        currentLabels.erase label
      have remainingLabelCard :
          remainingLabels.card < labelCount := by
        have eraseCard :
            remainingLabels.card < currentLabels.card := by
          simpa [remainingLabels] using
            Finset.card_erase_lt_of_mem labelMem
        exact eraseCard.trans_le labelCard
      rcases
          inductionHypothesis
            remainingLabels.card remainingLabelCard
            remainingLabels remainingEdges le_rfl
        with
        ⟨core, coreSubsetRemaining, noRemainingBad,
          remainingCharge⟩
      have remainingSubsetCurrent :
          remainingEdges ⊆ currentEdges := by
        exact Finset.sdiff_subset
      have coreSubsetCurrent :
          core ⊆ currentEdges :=
        coreSubsetRemaining.trans remainingSubsetCurrent
      have removedSubsetCurrent :
          removedBlock ⊆ currentEdges := by
        exact Finset.inter_subset_left
      have coreDisjointRemoved :
          Disjoint core removedBlock := by
        rw [Finset.disjoint_left]
        intro edge edgeCore edgeRemoved
        have edgeRemaining :=
          coreSubsetRemaining edgeCore
        exact
          (Finset.mem_sdiff.mp edgeRemaining).2 edgeRemoved
      have selectedLabelNotBad :
          ¬bad core label := by
        intro coreBad
        rcases bad_nonempty core label coreBad with
          ⟨edge, edgeMem⟩
        have edgeCore := (Finset.mem_inter.mp edgeMem).1
        have edgeBlock := (Finset.mem_inter.mp edgeMem).2
        have edgeCurrent := coreSubsetCurrent edgeCore
        have edgeRemoved : edge ∈ removedBlock :=
          Finset.mem_inter.mpr ⟨edgeCurrent, edgeBlock⟩
        exact
          (Finset.disjoint_left.mp coreDisjointRemoved
            edgeCore edgeRemoved)
      have noBad :
          ∀ candidate ∈ currentLabels,
            ¬bad core candidate := by
        intro candidate candidateMem
        by_cases candidateEq : candidate = label
        · subst candidate
          exact selectedLabelNotBad
        · exact
            noRemainingBad candidate
              (Finset.mem_erase.mpr
                ⟨candidateEq, candidateMem⟩)
      have removedDecomposition :
          currentEdges \ core =
            removedBlock ∪ (remainingEdges \ core) := by
        ext edge
        simp only [
          remainingEdges, Finset.mem_sdiff,
          Finset.mem_union
        ]
        constructor
        · intro edgeData
          by_cases edgeRemoved : edge ∈ removedBlock
          · exact Or.inl edgeRemoved
          · exact Or.inr
              ⟨⟨edgeData.1, edgeRemoved⟩, edgeData.2⟩
        · rintro (edgeRemoved | edgeRemaining)
          · exact
              ⟨removedSubsetCurrent edgeRemoved,
                fun edgeCore =>
                  (Finset.disjoint_left.mp coreDisjointRemoved
                    edgeCore edgeRemoved)⟩
          · exact
              ⟨edgeRemaining.1.1, edgeRemaining.2⟩
      have removedDisjoint :
          Disjoint removedBlock (remainingEdges \ core) := by
        rw [Finset.disjoint_left]
        intro edge edgeRemoved edgeRemaining
        have edgeRemainingData :
            edge ∈ remainingEdges ∧ edge ∉ core :=
          Finset.mem_sdiff.mp edgeRemaining
        have edgeNotRemoved :
            edge ∉ removedBlock := by
          have edgeInDifference :
              edge ∈ currentEdges \ removedBlock :=
            edgeRemainingData.1
          exact (Finset.mem_sdiff.mp edgeInDifference).2
        exact edgeNotRemoved edgeRemoved
      have removedCard :
          (currentEdges \ core).card =
            removedBlock.card +
              (remainingEdges \ core).card := by
        rw [
          removedDecomposition,
          Finset.card_union_of_disjoint removedDisjoint
        ]
      have selectedCharge :
          removedBlock.card ≤ charge label := by
        simpa [removedBlock] using
          bad_card_le currentEdges label labelBad
      have chargeDecomposition :
          (∑ candidate ∈ currentLabels, charge candidate) =
            charge label +
              ∑ candidate ∈ remainingLabels,
                charge candidate := by
        rw [
          show currentLabels =
              insert label remainingLabels by
            ext candidate
            simp [remainingLabels, labelMem],
          Finset.sum_insert
        ]
        simp [remainingLabels]
      refine
        ⟨core, coreSubsetCurrent, noBad, ?_⟩
      rw [removedCard, chargeDecomposition]
      exact Nat.add_le_add selectedCharge remainingCharge
    · exact
        ⟨currentEdges, Finset.Subset.rfl, by
          intro label labelMem
          exact fun labelBad =>
            existsBad ⟨label, labelMem, labelBad⟩,
          by simp⟩
  have allCounts : ∀ labelCount, P labelCount :=
    fun labelCount =>
      Nat.strong_induction_on labelCount main
  exact allCounts labels.card labels initialEdges le_rfl

end Kakeya.Assouad

end
