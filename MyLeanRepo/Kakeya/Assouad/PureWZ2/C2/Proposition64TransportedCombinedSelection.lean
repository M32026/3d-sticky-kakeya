import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64TransportedSourceParentQuotient

/-!
# One combined selection for Proposition 6.4 transported parents

At every requested coordinate, one selector slot records the proper conflict
color of the transported quotient parent and a second selector slot records
the joint quotient-parent/source-parent owner.  A single call to
`wz2_finite_colored_degree_selection` therefore produces one common final
subfamily with both the separation and owner-pair regularity needed for the
literal Definition 2.12 cover.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

variable
    {sigma workLoss sourceDelta targetDelta₀ outputLoss : ℝ}
    {Grid : Type*} [PureWZ2Proposition64TargetGrid Grid]
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀}
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    (frostman : SelectedSourceFrostmanReceipt geometry)
    (floor : Grid)

private noncomputable abbrev initialED :=
  quantitativeVerticalPaperED quantitativeOutput geometry frostman

private noncomputable abbrev schedule :=
  quantitativeVerticalRequestedScaleScheduleFor quantitativeOutput geometry floor

namespace QuantitativeVerticalTransportedSourceParentQuotientData

private theorem combinedSelection_selected_nonempty
    {indexType : Type*}
    [Fintype indexType] [DecidableEq indexType] [LinearOrder indexType]
    {coordinateCount : ℕ}
    {Color Vertex : Fin coordinateCount → Type}
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    [∀ coordinate, Fintype (Vertex coordinate)]
    [∀ coordinate, DecidableEq (Vertex coordinate)]
    {color : ∀ coordinate, indexType → Color coordinate}
    {parent : ∀ coordinate, indexType → Vertex coordinate}
    {weight : indexType → ENNReal}
    (data : WZ2FiniteColoredDegreeSelectionData
      coordinateCount Color Vertex color parent weight)
    (htotal : 0 < ∑ index, weight index) :
    data.regularized.selected.Nonempty := by
  by_contra hempty
  have hselectedEmpty : data.regularized.selected = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hselectedSum :
      (∑ index ∈ data.regularized.selected, weight index) = 0 := by
    rw [hselectedEmpty]
    simp
  have hcolorSum : (∑ index ∈ data.colorClass, weight index) ≤ 0 := by
    have hdegree := data.regularized.retained_weight
    have hleft :
        (∑ index, if index ∈ data.colorClass then weight index else 0) =
          ∑ index ∈ data.colorClass, weight index := by
      rw [Finset.sum_ite]
      simp
    have hright :
        (∑ index ∈ data.regularized.selected,
          if index ∈ data.colorClass then weight index else 0) =
          ∑ index ∈ data.regularized.selected, weight index := by
      apply Finset.sum_congr rfl
      intro index hindex
      rw [if_pos (data.selected_subset_colorClass hindex)]
    rw [hleft, hright, hselectedSum, mul_zero] at hdegree
    exact hdegree
  have htotalZero : (∑ index, weight index) ≤ 0 :=
    data.color_retained.trans <| by
      simpa using mul_le_mul_left' hcolorSum
        (Fintype.card (∀ coordinate, Color coordinate) : ENNReal)
  exact (not_le_of_gt htotal) htotalZero

private abbrev selectorCount :=
  (schedule quantitativeOutput geometry floor).levelCount * 2

private noncomputable def selectorDecoded :
    Fin (selectorCount quantitativeOutput geometry floor) →
      Fin (schedule quantitativeOutput geometry floor).levelCount × Fin 2 :=
  finProdFinEquiv.symm

private abbrev SelectorColor
    (slot : Fin (selectorCount quantitativeOutput geometry floor)) :=
  Fin (if (selectorDecoded quantitativeOutput geometry floor slot).2 = 0 then
    quantitativeVerticalTransportedQuotientConflictDegree + 1 else 1)

private abbrev DirectVertex
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw) :=
  Σ coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount,
    Fin (data.quotientParents quantitativeOutput geometry frostman floor
      coordinate).card

private abbrev PairVertex
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw) :=
  Σ coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount,
    Fin (data.quotientParents quantitativeOutput geometry frostman floor
      coordinate).card ×
      Fin (quantitativeVerticalMatchedSourceNearby
        quantitativeOutput geometry floor coordinate).scaleData.coarse.card

private abbrev SelectorVertex
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw)
    (_slot : Fin (selectorCount quantitativeOutput geometry floor)) :=
  DirectVertex quantitativeOutput geometry frostman floor data ⊕
    PairVertex quantitativeOutput geometry frostman floor data

private noncomputable def selectorColorMap
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw)
    (coloring : QuantitativeVerticalTransportedQuotientColoringData
      quantitativeOutput geometry frostman floor data) :
    ∀ slot, Fin (initialED quantitativeOutput geometry frostman).subfamily.family.card →
      SelectorColor quantitativeOutput geometry floor slot :=
  fun slot source =>
    if hdirect :
        (selectorDecoded quantitativeOutput geometry floor slot).2 = 0 then
      Fin.cast (by rw [if_pos hdirect])
        (coloring.color
          (selectorDecoded quantitativeOutput geometry floor slot).1
          (data.assignedParent quantitativeOutput geometry frostman floor
            (selectorDecoded quantitativeOutput geometry floor slot).1 source))
    else Fin.cast (by rw [if_neg hdirect]) 0

private def selectorOwnerMap
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw) :
    ∀ slot, Fin (initialED quantitativeOutput geometry frostman).subfamily.family.card →
      SelectorVertex quantitativeOutput geometry frostman floor data slot :=
  fun slot source =>
    if (selectorDecoded quantitativeOutput geometry floor slot).2 = 0 then
      Sum.inl ⟨
        (selectorDecoded quantitativeOutput geometry floor slot).1,
        data.assignedParent quantitativeOutput geometry frostman floor
          (selectorDecoded quantitativeOutput geometry floor slot).1 source⟩
    else
      Sum.inr ⟨
        (selectorDecoded quantitativeOutput geometry floor slot).1,
        (data.assignedParent quantitativeOutput geometry frostman floor
            (selectorDecoded quantitativeOutput geometry floor slot).1 source,
          data.sourceOwner quantitativeOutput geometry frostman floor
            (selectorDecoded quantitativeOutput geometry floor slot).1 source)⟩

private noncomputable def selectorWeight
    (source : Fin
      (initialED quantitativeOutput geometry frostman).subfamily.family.card) :
    ENNReal :=
  volume ((initialED quantitativeOutput geometry frostman).finalShading.carrier
    source)

/-- Opaque result of exactly one combined color-vector and degree selection. -/
structure QuantitativeVerticalTransportedCombinedSelectionCoreData
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw) where
  coloring : QuantitativeVerticalTransportedQuotientColoringData
    quantitativeOutput geometry frostman floor data
  selection : WZ2FiniteColoredDegreeSelectionData
    (selectorCount quantitativeOutput geometry floor)
    (SelectorColor quantitativeOutput geometry floor)
    (SelectorVertex quantitativeOutput geometry frostman floor data)
    (selectorColorMap quantitativeOutput geometry frostman floor data coloring)
    (selectorOwnerMap quantitativeOutput geometry frostman floor data)
    (selectorWeight quantitativeOutput geometry frostman)

theorem exists_quantitativeVerticalTransportedCombinedSelectionCore
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    (data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw) :
    Nonempty (QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data) := by
  let coloring := Classical.choice
    (data.exists_coloring quantitativeOutput geometry frostman floor)
  letI colorNonempty : ∀ slot, Nonempty
      (SelectorColor quantitativeOutput geometry floor slot) := by
    intro slot
    unfold SelectorColor
    by_cases hdirect :
        (selectorDecoded quantitativeOutput geometry floor slot).2 = 0
    · rw [if_pos hdirect]
      exact Fin.pos_iff_nonempty.mp (Nat.succ_pos _)
    · rw [if_neg hdirect]
      infer_instance
  refine ⟨{ coloring := coloring, selection := Classical.choice ?_ }⟩
  exact wz2_finite_colored_degree_selection
    (selectorCount quantitativeOutput geometry floor)
    (SelectorColor quantitativeOutput geometry floor)
    (SelectorVertex quantitativeOutput geometry frostman floor data)
    (selectorColorMap quantitativeOutput geometry frostman floor data coloring)
    (selectorOwnerMap quantitativeOutput geometry frostman floor data)
    (selectorWeight quantitativeOutput geometry frostman)
    (Nat.mul_pos
      (schedule quantitativeOutput geometry floor).levelCount_pos (by norm_num))

namespace QuantitativeVerticalTransportedCombinedSelectionCoreData

noncomputable def selectedIndices
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data) :=
  core.selection.regularized.selected

noncomputable def selected
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data) :
    WZ2PaperPureTubeSubfamily
      (initialED quantitativeOutput geometry frostman).subfamily.family :=
  WZ2PaperPureTubeSubfamily.fromFinset
    (initialED quantitativeOutput geometry frostman).subfamily.family
    (core.selectedIndices quantitativeOutput geometry frostman floor)

theorem selected_nonempty
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data) :
    (core.selected quantitativeOutput geometry frostman floor).family.Nonempty := by
  apply (combinedSelection_selected_nonempty core.selection ?_).card_pos
  change 0 < (initialED quantitativeOutput geometry frostman).finalShading.mass
  have hright : 0 <
      (quantitativeVerticalPaperEDLoss quantitativeOutput geometry + 1) *
        (initialED quantitativeOutput geometry frostman).finalShading.mass :=
    geometry.cleanup_finalShading_mass_pos.trans_le
      (initialED quantitativeOutput geometry frostman).mass_retention
  by_contra hzero
  rw [not_lt, nonpos_iff_eq_zero] at hzero
  simp [hzero] at hright

private noncomputable def directSlot
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (_core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    Fin (selectorCount quantitativeOutput geometry floor) :=
  finProdFinEquiv (coordinate, (0 : Fin 2))

private noncomputable def pairSlot
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (_core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    Fin (selectorCount quantitativeOutput geometry floor) :=
  finProdFinEquiv (coordinate, (1 : Fin 2))

private theorem decoded_directSlot
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    selectorDecoded quantitativeOutput geometry floor
        (core.directSlot quantitativeOutput geometry frostman floor coordinate) =
      (coordinate, (0 : Fin 2)) :=
  Equiv.symm_apply_apply finProdFinEquiv _

private theorem decoded_pairSlot
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount) :
    selectorDecoded quantitativeOutput geometry floor
        (core.pairSlot quantitativeOutput geometry frostman floor coordinate) =
      (coordinate, (1 : Fin 2)) :=
  Equiv.symm_apply_apply finProdFinEquiv _

theorem selected_mem
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (source : Fin
      (core.selected quantitativeOutput geometry frostman floor).family.card) :
    (core.selected quantitativeOutput geometry frostman floor).embedding source ∈
      core.selectedIndices quantitativeOutput geometry frostman floor :=
  Finset.orderEmbOfFin_mem _ rfl source

private theorem selectorOwner_direct
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (source : Fin
      (initialED quantitativeOutput geometry frostman).subfamily.family.card) :
    selectorOwnerMap quantitativeOutput geometry frostman floor data
        (core.directSlot quantitativeOutput geometry frostman floor coordinate)
        source =
      Sum.inl ⟨coordinate,
        data.assignedParent quantitativeOutput geometry frostman floor coordinate
          source⟩ := by
  unfold selectorOwnerMap
  rw [core.decoded_directSlot quantitativeOutput geometry frostman floor
    coordinate]
  simp

private theorem selectorOwner_pair
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (source : Fin
      (initialED quantitativeOutput geometry frostman).subfamily.family.card) :
    selectorOwnerMap quantitativeOutput geometry frostman floor data
        (core.pairSlot quantitativeOutput geometry frostman floor coordinate)
        source =
      Sum.inr ⟨coordinate,
        (data.assignedParent quantitativeOutput geometry frostman floor coordinate
            source,
          data.sourceOwner quantitativeOutput geometry frostman floor coordinate
            source)⟩ := by
  unfold selectorOwnerMap
  rw [core.decoded_pairSlot quantitativeOutput geometry frostman floor coordinate]
  simp

private theorem selected_filter_card
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (slot : Fin (selectorCount quantitativeOutput geometry floor))
    (vertex : SelectorVertex quantitativeOutput geometry frostman floor data slot) :
    ((core.selectedIndices quantitativeOutput geometry frostman floor).filter
      fun source => selectorOwnerMap quantitativeOutput geometry frostman floor
        data slot source = vertex).card =
      ((Finset.univ : Finset (Fin
        (core.selected quantitativeOutput geometry frostman floor).family.card)
        ).filter fun source =>
          selectorOwnerMap quantitativeOutput geometry frostman floor data slot
            ((core.selected quantitativeOutput geometry frostman floor).embedding
              source) = vertex).card := by
  let selected := core.selected quantitativeOutput geometry frostman floor
  let selectedIndices := core.selectedIndices quantitativeOutput geometry
    frostman floor
  let localIndices := (Finset.univ : Finset (Fin selected.family.card)).filter
    fun source => selectorOwnerMap quantitativeOutput geometry frostman floor data
      slot (selected.embedding source) = vertex
  have imageEq : Finset.image selected.embedding localIndices =
      selectedIndices.filter fun source =>
        selectorOwnerMap quantitativeOutput geometry frostman floor data slot
          source = vertex := by
    ext source
    simp only [Finset.mem_image, localIndices, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨selectedSource, howner, rfl⟩
      exact ⟨core.selected_mem quantitativeOutput geometry frostman floor
        selectedSource, howner⟩
    · rintro ⟨hselected, howner⟩
      let selectedSource : Fin selected.family.card :=
        (selectedIndices.orderIsoOfFin rfl).symm ⟨source, hselected⟩
      have hembedding : selected.embedding selectedSource = source :=
        congrArg Subtype.val
          ((selectedIndices.orderIsoOfFin rfl).apply_symm_apply
            ⟨source, hselected⟩)
      exact ⟨selectedSource, by rwa [hembedding], hembedding⟩
  rw [← imageEq, Finset.card_image_of_injective _ selected.embedding.injective]

private theorem slot_degree_uniform
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (slot : Fin (selectorCount quantitativeOutput geometry floor))
    (first second : SelectorVertex quantitativeOutput geometry frostman floor
      data slot)
    (hfirst : 0 < ((Finset.univ : Finset (Fin
      (core.selected quantitativeOutput geometry frostman floor).family.card)
      ).filter fun source =>
        selectorOwnerMap quantitativeOutput geometry frostman floor data slot
          ((core.selected quantitativeOutput geometry frostman floor).embedding
            source) = first).card)
    (hsecond : 0 < ((Finset.univ : Finset (Fin
      (core.selected quantitativeOutput geometry frostman floor).family.card)
      ).filter fun source =>
        selectorOwnerMap quantitativeOutput geometry frostman floor data slot
          ((core.selected quantitativeOutput geometry frostman floor).embedding
            source) = second).card) :
    (((Finset.univ : Finset (Fin
      (core.selected quantitativeOutput geometry frostman floor).family.card)
      ).filter fun source =>
        selectorOwnerMap quantitativeOutput geometry frostman floor data slot
          ((core.selected quantitativeOutput geometry frostman floor).embedding
            source) = first).card : ENNReal) ≤
      quantitativeVerticalTransportedPairDegreeConstant
          quantitativeOutput geometry frostman floor *
        (((Finset.univ : Finset (Fin
          (core.selected quantitativeOutput geometry frostman floor).family.card)
          ).filter fun source =>
            selectorOwnerMap quantitativeOutput geometry frostman floor data slot
              ((core.selected quantitativeOutput geometry frostman floor).embedding
                source) = second).card : ENNReal) := by
  have huniform := core.selection.regularized.degree_uniform slot first second
    (by
      change 0 < ((core.selectedIndices quantitativeOutput geometry frostman
        floor).filter fun source =>
          selectorOwnerMap quantitativeOutput geometry frostman floor data slot
            source = first).card
      rw [core.selected_filter_card quantitativeOutput geometry frostman floor
        slot first]
      exact hfirst)
    (by
      change 0 < ((core.selectedIndices quantitativeOutput geometry frostman
        floor).filter fun source =>
          selectorOwnerMap quantitativeOutput geometry frostman floor data slot
            source = second).card
      rw [core.selected_filter_card quantitativeOutput geometry frostman floor
        slot second]
      exact hsecond)
  calc
    _ = (((core.selectedIndices quantitativeOutput geometry frostman floor).filter
          fun source => selectorOwnerMap quantitativeOutput geometry frostman
            floor data slot source = first).card : ENNReal) := by
      exact congrArg (fun cardinality : ℕ => (cardinality : ENNReal))
        (core.selected_filter_card quantitativeOutput geometry frostman floor
          slot first).symm
    _ ≤ quantitativeVerticalTransportedPairDegreeConstant
            quantitativeOutput geometry frostman floor *
          (((core.selectedIndices quantitativeOutput geometry frostman floor).filter
            fun source => selectorOwnerMap quantitativeOutput geometry frostman
              floor data slot source = second).card : ENNReal) := by
      change
        (((core.selection.regularized.selected).filter fun source =>
          selectorOwnerMap quantitativeOutput geometry frostman floor data slot
            source = first).card : ENNReal) ≤
          (16 *
              (selectorCount quantitativeOutput geometry floor : ENNReal) *
            (Nat.log 2
                (2 * (initialED quantitativeOutput geometry frostman
                  ).subfamily.family.card) + 1 : ENNReal) ^
              selectorCount quantitativeOutput geometry floor) *
            (((core.selection.regularized.selected).filter fun source =>
              selectorOwnerMap quantitativeOutput geometry frostman floor data
                slot source = second).card : ENNReal)
      simpa only [Fintype.card_fin] using huniform
    _ = _ := by
      apply congrArg
      exact congrArg (fun cardinality : ℕ => (cardinality : ENNReal))
        (core.selected_filter_card quantitativeOutput geometry frostman floor
          slot second)

theorem direct_degree_uniform
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (first second : Fin (data.quotientParents quantitativeOutput geometry
      frostman floor coordinate).card)
    (hfirst : 0 < ((Finset.univ : Finset (Fin
      (core.selected quantitativeOutput geometry frostman floor).family.card)
      ).filter fun source =>
        data.assignedParent quantitativeOutput geometry frostman floor coordinate
          ((core.selected quantitativeOutput geometry frostman floor).embedding
            source) = first).card)
    (hsecond : 0 < ((Finset.univ : Finset (Fin
      (core.selected quantitativeOutput geometry frostman floor).family.card)
      ).filter fun source =>
        data.assignedParent quantitativeOutput geometry frostman floor coordinate
          ((core.selected quantitativeOutput geometry frostman floor).embedding
            source) = second).card) :
    (((Finset.univ : Finset (Fin
      (core.selected quantitativeOutput geometry frostman floor).family.card)
      ).filter fun source =>
        data.assignedParent quantitativeOutput geometry frostman floor coordinate
          ((core.selected quantitativeOutput geometry frostman floor).embedding
            source) = first).card : ENNReal) ≤
      quantitativeVerticalTransportedPairDegreeConstant
          quantitativeOutput geometry frostman floor *
        (((Finset.univ : Finset (Fin
          (core.selected quantitativeOutput geometry frostman floor).family.card)
          ).filter fun source =>
            data.assignedParent quantitativeOutput geometry frostman floor
              coordinate
              ((core.selected quantitativeOutput geometry frostman floor
                ).embedding source) = second).card : ENNReal) := by
  have hraw := core.slot_degree_uniform quantitativeOutput geometry frostman floor
    (core.directSlot quantitativeOutput geometry frostman floor coordinate)
    (Sum.inl ⟨coordinate, first⟩) (Sum.inl ⟨coordinate, second⟩)
    (by
      simp_rw [core.selectorOwner_direct quantitativeOutput geometry
        frostman floor]
      simpa using hfirst)
    (by
      simp_rw [core.selectorOwner_direct quantitativeOutput geometry
        frostman floor]
      simpa using hsecond)
  simp_rw [core.selectorOwner_direct quantitativeOutput geometry frostman floor]
    at hraw
  simpa using hraw

theorem pair_degree_uniform
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (first second : Fin (data.quotientParents quantitativeOutput geometry
        frostman floor coordinate).card ×
      Fin (quantitativeVerticalMatchedSourceNearby quantitativeOutput geometry
        floor coordinate).scaleData.coarse.card)
    (hfirst : 0 < ((Finset.univ : Finset (Fin
      (core.selected quantitativeOutput geometry frostman floor).family.card)
      ).filter fun source =>
        (data.assignedParent quantitativeOutput geometry frostman floor coordinate
            ((core.selected quantitativeOutput geometry frostman floor).embedding
              source),
          data.sourceOwner quantitativeOutput geometry frostman floor coordinate
            ((core.selected quantitativeOutput geometry frostman floor).embedding
              source)) = first).card)
    (hsecond : 0 < ((Finset.univ : Finset (Fin
      (core.selected quantitativeOutput geometry frostman floor).family.card)
      ).filter fun source =>
        (data.assignedParent quantitativeOutput geometry frostman floor coordinate
            ((core.selected quantitativeOutput geometry frostman floor).embedding
              source),
          data.sourceOwner quantitativeOutput geometry frostman floor coordinate
            ((core.selected quantitativeOutput geometry frostman floor).embedding
              source)) = second).card) :
    (((Finset.univ : Finset (Fin
      (core.selected quantitativeOutput geometry frostman floor).family.card)
      ).filter fun source =>
        (data.assignedParent quantitativeOutput geometry frostman floor coordinate
            ((core.selected quantitativeOutput geometry frostman floor).embedding
              source),
          data.sourceOwner quantitativeOutput geometry frostman floor coordinate
            ((core.selected quantitativeOutput geometry frostman floor).embedding
              source)) = first).card : ENNReal) ≤
      quantitativeVerticalTransportedPairDegreeConstant
          quantitativeOutput geometry frostman floor *
        (((Finset.univ : Finset (Fin
          (core.selected quantitativeOutput geometry frostman floor).family.card)
          ).filter fun source =>
            (data.assignedParent quantitativeOutput geometry frostman floor
                coordinate
                ((core.selected quantitativeOutput geometry frostman floor
                  ).embedding source),
              data.sourceOwner quantitativeOutput geometry frostman floor
                coordinate
                ((core.selected quantitativeOutput geometry frostman floor
                  ).embedding source)) = second).card : ENNReal) := by
  have hraw := core.slot_degree_uniform quantitativeOutput geometry frostman floor
    (core.pairSlot quantitativeOutput geometry frostman floor coordinate)
    (Sum.inr ⟨coordinate, first⟩) (Sum.inr ⟨coordinate, second⟩)
    (by
      simp_rw [core.selectorOwner_pair quantitativeOutput geometry
        frostman floor]
      simpa using hfirst)
    (by
      simp_rw [core.selectorOwner_pair quantitativeOutput geometry
        frostman floor]
      simpa using hsecond)
  simp_rw [core.selectorOwner_pair quantitativeOutput geometry frostman floor]
    at hraw
  simpa using hraw

theorem monochromatic
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data)
    (coordinate : Fin (schedule quantitativeOutput geometry floor).levelCount)
    (first second : Fin
      (core.selected quantitativeOutput geometry frostman floor).family.card) :
    core.coloring.color coordinate
        (data.assignedParent quantitativeOutput geometry frostman floor coordinate
          ((core.selected quantitativeOutput geometry frostman floor).embedding
            first)) =
      core.coloring.color coordinate
        (data.assignedParent quantitativeOutput geometry frostman floor coordinate
          ((core.selected quantitativeOutput geometry frostman floor).embedding
            second)) := by
  let slot := core.directSlot quantitativeOutput geometry frostman floor coordinate
  have hfirstMem := core.selected_mem quantitativeOutput geometry frostman floor first
  have hsecondMem := core.selected_mem quantitativeOutput geometry frostman floor second
  have hfirstClass := core.selection.selected_subset_colorClass hfirstMem
  have hsecondClass := core.selection.selected_subset_colorClass hsecondMem
  have hfirstMono := core.selection.monochromatic
    ((core.selected quantitativeOutput geometry frostman floor).embedding first)
    hfirstClass slot
  have hsecondMono := core.selection.monochromatic
    ((core.selected quantitativeOutput geometry frostman floor).embedding second)
    hsecondClass slot
  have hcolorCard :
      (if (selectorDecoded quantitativeOutput geometry floor slot).2 = 0 then
        quantitativeVerticalTransportedQuotientConflictDegree + 1 else 1) =
          quantitativeVerticalTransportedQuotientConflictDegree + 1 := by
    dsimp only [slot]
    rw [core.decoded_directSlot quantitativeOutput geometry frostman floor
      coordinate]
    simp
  have hfirstMono' := congrArg (Fin.cast hcolorCard) hfirstMono
  have hsecondMono' := congrArg (Fin.cast hcolorCard) hsecondMono
  have hmap : ∀ source,
      Fin.cast hcolorCard
          (selectorColorMap quantitativeOutput geometry frostman floor data
            core.coloring slot source) =
        core.coloring.color coordinate
          (data.assignedParent quantitativeOutput geometry frostman floor
            coordinate source) := by
    intro source
    apply Fin.ext
    unfold selectorColorMap
    have hdecoded := core.decoded_directSlot quantitativeOutput geometry
      frostman floor coordinate
    have hsecond := congrArg Prod.snd hdecoded
    rw [dif_pos (by simpa [slot] using hsecond)]
    simp only [Fin.coe_cast]
    rw [congrArg Prod.fst hdecoded]
  rw [hmap] at hfirstMono' hsecondMono'
  exact hfirstMono'.trans hsecondMono'.symm

noncomputable def retentionConstant
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (_core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data) : ENNReal :=
  quantitativeVerticalTransportedSelectionRetention
    quantitativeOutput geometry frostman floor

theorem retentionConstant_ne_top
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data) :
    core.retentionConstant quantitativeOutput geometry frostman floor ≠ ⊤ := by
  unfold retentionConstant quantitativeVerticalTransportedSelectionRetention
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · exact ENNReal.natCast_ne_top _
    · norm_num
  · exact ENNReal.pow_ne_top (by simp)

theorem retained_mass
    {raw : QuantitativeVerticalTransportedSourceParentScheduleData
      quantitativeOutput geometry frostman floor}
    {data : QuantitativeVerticalTransportedSourceParentQuotientData
      quantitativeOutput geometry frostman floor raw}
    (core : QuantitativeVerticalTransportedCombinedSelectionCoreData
      quantitativeOutput geometry frostman floor data) :
    (initialED quantitativeOutput geometry frostman).finalShading.mass ≤
      core.retentionConstant quantitativeOutput geometry frostman floor *
        (restrictPaperShading
          (core.selected quantitativeOutput geometry frostman floor
            ).toTubeSubfamily
          (initialED quantitativeOutput geometry frostman).finalShading).mass := by
  let selected := core.selected quantitativeOutput geometry frostman floor
  let selectedIndices := core.selectedIndices quantitativeOutput geometry
    frostman floor
  have selectedSum :
      (∑ source : Fin selected.family.card,
        selectorWeight quantitativeOutput geometry frostman
          (selected.embedding source)) =
        ∑ source ∈ selectedIndices,
          selectorWeight quantitativeOutput geometry frostman source := by
    let equivalence := selectedIndices.orderIsoOfFin rfl
    exact (Fintype.sum_equiv equivalence.toEquiv
      (fun source : Fin selected.family.card =>
        selectorWeight quantitativeOutput geometry frostman
          (selected.embedding source))
      (fun source : selectedIndices =>
        selectorWeight quantitativeOutput geometry frostman source.1)
      (fun _ => rfl)).trans (Finset.sum_coe_sort selectedIndices
        (selectorWeight quantitativeOutput geometry frostman))
  have colorCard : Fintype.card
      (∀ slot, SelectorColor quantitativeOutput geometry floor slot) =
      (quantitativeVerticalTransportedQuotientConflictDegree + 1) ^
        (schedule quantitativeOutput geometry floor).levelCount := by
    rw [Fintype.card_pi]
    calc
      (∏ slot : Fin (selectorCount quantitativeOutput geometry floor),
          Fintype.card (SelectorColor quantitativeOutput geometry floor slot)) =
          ∏ pair : Fin (schedule quantitativeOutput geometry floor).levelCount ×
              Fin 2,
            Fintype.card (SelectorColor quantitativeOutput geometry floor
              (finProdFinEquiv pair)) := by
        apply Fintype.prod_equiv finProdFinEquiv.symm
        intro slot
        rw [Equiv.apply_symm_apply]
      _ = ∏ coordinate : Fin (schedule quantitativeOutput geometry floor
              ).levelCount,
            ∏ slot : Fin 2,
              Fintype.card (SelectorColor quantitativeOutput geometry floor
                (finProdFinEquiv (coordinate, slot))) := by
        rw [Fintype.prod_prod_type]
      _ = ∏ _coordinate : Fin (schedule quantitativeOutput geometry floor
              ).levelCount,
          (quantitativeVerticalTransportedQuotientConflictDegree + 1) := by
        apply Finset.prod_congr rfl
        intro coordinate _
        rw [Fin.prod_univ_two]
        have hzero : selectorDecoded quantitativeOutput geometry floor
              (finProdFinEquiv (coordinate, (0 : Fin 2))) =
            (coordinate, (0 : Fin 2)) :=
          Equiv.symm_apply_apply finProdFinEquiv _
        have hone : selectorDecoded quantitativeOutput geometry floor
              (finProdFinEquiv (coordinate, (1 : Fin 2))) =
            (coordinate, (1 : Fin 2)) :=
          Equiv.symm_apply_apply finProdFinEquiv _
        simp only [SelectorColor, Fintype.card_fin]
        rw [hzero, hone]
        norm_num
      _ = _ := by simp
  have hdegree := core.selection.regularized.retained_weight
  have hleft :
      (∑ source, if source ∈ core.selection.colorClass then
          selectorWeight quantitativeOutput geometry frostman source else 0) =
        ∑ source ∈ core.selection.colorClass,
          selectorWeight quantitativeOutput geometry frostman source := by
    rw [Finset.sum_ite]
    simp
  have hright :
      (∑ source ∈ selectedIndices,
        if source ∈ core.selection.colorClass then
          selectorWeight quantitativeOutput geometry frostman source else 0) =
        ∑ source ∈ selectedIndices,
          selectorWeight quantitativeOutput geometry frostman source := by
    apply Finset.sum_congr rfl
    intro source hsource
    rw [if_pos (core.selection.selected_subset_colorClass hsource)]
  have retainedWeight :
      (∑ source, selectorWeight quantitativeOutput geometry frostman source) ≤
      core.retentionConstant quantitativeOutput geometry frostman floor *
        ∑ source ∈ selectedIndices,
          selectorWeight quantitativeOutput geometry frostman source := by
    calc
      (∑ source, selectorWeight quantitativeOutput geometry frostman source) ≤
          (Fintype.card
            (∀ slot, SelectorColor quantitativeOutput geometry floor slot) :
              ENNReal) *
            ∑ source ∈ core.selection.colorClass,
              selectorWeight quantitativeOutput geometry frostman source :=
        core.selection.color_retained
      _ = (Fintype.card
            (∀ slot, SelectorColor quantitativeOutput geometry floor slot) :
              ENNReal) *
          (∑ source,
            if source ∈ core.selection.colorClass then
              selectorWeight quantitativeOutput geometry frostman source else 0) := by
        rw [hleft]
      _ ≤ (Fintype.card
            (∀ slot, SelectorColor quantitativeOutput geometry floor slot) :
              ENNReal) *
          ((8 : ENNReal) *
            (Nat.log 2
                (2 * (initialED quantitativeOutput geometry frostman
                  ).subfamily.family.card) + 1 : ENNReal) ^
              (selectorCount quantitativeOutput geometry floor + 1) *
            ∑ source ∈ selectedIndices,
              selectorWeight quantitativeOutput geometry frostman source) := by
        gcongr
        calc
          (∑ source, if source ∈ core.selection.colorClass then
              selectorWeight quantitativeOutput geometry frostman source else 0) ≤
              (8 : ENNReal) *
                (Nat.log 2
                    (2 * (initialED quantitativeOutput geometry frostman
                      ).subfamily.family.card) + 1 : ENNReal) ^
                  (selectorCount quantitativeOutput geometry floor + 1) *
                ∑ source ∈ core.selection.regularized.selected,
                  if source ∈ core.selection.colorClass then
                    selectorWeight quantitativeOutput geometry frostman source
                  else 0 := by
            simpa only [Fintype.card_fin] using hdegree
          _ = _ := by
            apply congrArg
            exact hright
      _ = core.retentionConstant quantitativeOutput geometry frostman floor *
          ∑ source ∈ selectedIndices,
            selectorWeight quantitativeOutput geometry frostman source := by
        rw [colorCard]
        unfold retentionConstant
        unfold quantitativeVerticalTransportedSelectionRetention
        simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one,
          quantitativeVerticalTransportedSelectorCoordinateCount, selectorCount]
        ring
  calc
    (initialED quantitativeOutput geometry frostman).finalShading.mass =
        ∑ source, selectorWeight quantitativeOutput geometry frostman source := rfl
    _ ≤ core.retentionConstant quantitativeOutput geometry frostman floor *
        ∑ source ∈ selectedIndices,
          selectorWeight quantitativeOutput geometry frostman source := retainedWeight
    _ = core.retentionConstant quantitativeOutput geometry frostman floor *
        (restrictPaperShading selected.toTubeSubfamily
          (initialED quantitativeOutput geometry frostman).finalShading).mass := by
      apply congrArg
      exact selectedSum.symm.trans
        (restrictPaperShading_mass selected.toTubeSubfamily
          (initialED quantitativeOutput geometry frostman).finalShading).symm

end QuantitativeVerticalTransportedCombinedSelectionCoreData

end QuantitativeVerticalTransportedSourceParentQuotientData

end PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

end Kakeya.Assouad

end
