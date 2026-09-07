import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64QuantitativeVerticalJointSelection

/-!
# Raw colored parents for quantitative vertical selection

Literal partitioning is produced only after the simultaneous color selection.
This is the correct replacement for attempting to reflect doubled-fiber
membership backwards through the non-invertible retubing.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private theorem finiteColored_selected_nonempty
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

private theorem finiteColored_retained_weight
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
      coordinateCount Color Vertex color parent weight) :
    (∑ index, weight index) ≤
      ((Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
        8 * (Nat.log 2 (2 * Fintype.card indexType) + 1 : ENNReal) ^
          (coordinateCount + 1)) *
        ∑ index ∈ data.regularized.selected, weight index := by
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
  rw [hleft, hright] at hdegree
  calc
    _ ≤ (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
        ∑ index ∈ data.colorClass, weight index := data.color_retained
    _ ≤ (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
        ((8 * (Nat.log 2 (2 * Fintype.card indexType) + 1 : ENNReal) ^
          (coordinateCount + 1)) *
          ∑ index ∈ data.regularized.selected, weight index) :=
      mul_le_mul_left' hdegree _
    _ = _ := by ring

namespace PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

variable
    {sigma workLoss sourceDelta targetDelta₀ outputLoss : ℝ}
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀}
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    (frostman : SelectedSourceFrostmanReceipt geometry)
    (floor : PureWZ2CroppedCriticalFloorSelectionData
      sigma outputLoss outputLoss)

private noncomputable abbrev initialED :=
  quantitativeVerticalPaperED quantitativeOutput geometry frostman

/-- Pre-selection geometry at the fixed scale grid.  It stores parent owners
and a proper coloring of the doubled-fiber conflict graph, not a target cover
or a selected family. -/
structure QuantitativeVerticalRawColoredParentReceipt where
  actualScale :
    Fin (quantitativeVerticalRequestedScaleSchedule
      quantitativeOutput geometry floor).levelCount → ℝ
  actualScale_pos : ∀ coordinate, 0 < actualScale coordinate
  colorCount :
    Fin (quantitativeVerticalRequestedScaleSchedule
      quantitativeOutput geometry floor).levelCount → ℕ
  colorCount_pos : ∀ coordinate, 0 < colorCount coordinate
  coarse :
    ∀ coordinate :
        Fin (quantitativeVerticalRequestedScaleSchedule
          quantitativeOutput geometry floor).levelCount,
      Kakeya.Streamlined.TubeFamily
        (actualScale coordinate)
  parent :
    ∀ coordinate,
      Fin (initialED quantitativeOutput geometry frostman).subfamily.family.card →
        Fin (coarse coordinate).card
  parent_covers :
    ∀ coordinate source,
      source ∈ wz2PaperOrdinaryFullFiberIndices
        (initialED quantitativeOutput geometry frostman).subfamily.family
        (coarse coordinate) (parent coordinate source)
  color :
    ∀ coordinate, Fin (coarse coordinate).card → Fin (colorCount coordinate)
  proper :
    ∀ coordinate first second, first ≠ second →
      (wz2PaperOrdinaryDilatedFiberIndices 2
          (initialED quantitativeOutput geometry frostman).subfamily.family
          (coarse coordinate) first ∩
        wz2PaperOrdinaryDilatedFiberIndices 2
          (initialED quantitativeOutput geometry frostman).subfamily.family
          (coarse coordinate) second).Nonempty →
        color coordinate first ≠ color coordinate second
  parentCountConstant :
    Fin (quantitativeVerticalRequestedScaleSchedule
      quantitativeOutput geometry floor).levelCount → ENNReal
  parentCount :
    ∀ coordinate,
      (coarse coordinate).enncard ≤
        parentCountConstant coordinate *
          (Kakeya.realRpowENN
            (actualScale coordinate) 2)⁻¹
  rounding :
    ∀ requested : WZ2PaperRequestedScale
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta),
      ∃ coordinate : Fin (quantitativeVerticalRequestedScaleSchedule
          quantitativeOutput geometry floor).levelCount,
        requested.1 ≤ actualScale coordinate ∧
          ENNReal.ofReal (actualScale coordinate) <
            Kakeya.realRpowENN
                (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
                (-floor.structuralLoss) *
              ENNReal.ofReal requested.1

/-- Minimal non-conclusion geometric leaf: target-scale parent nets with literal
owner containment and packing.  Coloring, selection, covers, and uniformity are
not fields; they are constructed below. -/
structure QuantitativeVerticalRawParentNetReceipt where
  actualScale :
    Fin (quantitativeVerticalRequestedScaleSchedule
      quantitativeOutput geometry floor).levelCount → ℝ
  actualScale_pos : ∀ coordinate, 0 < actualScale coordinate
  coarse :
    ∀ coordinate :
        Fin (quantitativeVerticalRequestedScaleSchedule
          quantitativeOutput geometry floor).levelCount,
      Kakeya.Streamlined.TubeFamily
        (actualScale coordinate)
  parent :
    ∀ coordinate,
      Fin (initialED quantitativeOutput geometry frostman).subfamily.family.card →
        Fin (coarse coordinate).card
  parent_covers :
    ∀ coordinate source,
      source ∈ wz2PaperOrdinaryFullFiberIndices
        (initialED quantitativeOutput geometry frostman).subfamily.family
        (coarse coordinate) (parent coordinate source)
  parentCountConstant :
    Fin (quantitativeVerticalRequestedScaleSchedule
      quantitativeOutput geometry floor).levelCount → ENNReal
  parentCount :
    ∀ coordinate,
      (coarse coordinate).enncard ≤
        parentCountConstant coordinate *
          (Kakeya.realRpowENN
            (actualScale coordinate) 2)⁻¹
  rounding :
    ∀ requested : WZ2PaperRequestedScale
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta),
      ∃ coordinate : Fin (quantitativeVerticalRequestedScaleSchedule
          quantitativeOutput geometry floor).levelCount,
        requested.1 ≤ actualScale coordinate ∧
          ENNReal.ofReal (actualScale coordinate) <
            Kakeya.realRpowENN
                (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
                (-floor.structuralLoss) *
              ENNReal.ofReal requested.1

namespace QuantitativeVerticalRawParentNetReceipt

/-- The identity coloring into one extra color is automatically proper for the
raw doubled-fiber conflict graph. -/
noncomputable def toColored
    (net : QuantitativeVerticalRawParentNetReceipt
      quantitativeOutput geometry frostman floor) :
    QuantitativeVerticalRawColoredParentReceipt
      quantitativeOutput geometry frostman floor where
  actualScale := net.actualScale
  actualScale_pos := net.actualScale_pos
  colorCount := fun coordinate => (net.coarse coordinate).card + 1
  colorCount_pos := fun _ => Nat.zero_lt_succ _
  coarse := net.coarse
  parent := net.parent
  parent_covers := net.parent_covers
  color := fun coordinate parent =>
    ⟨parent, Nat.lt.step parent.isLt⟩
  proper := by
    intro coordinate first second hne _ hover
    apply hne
    apply Fin.ext
    exact congrArg
      (fun value : Fin ((net.coarse coordinate).card + 1) => value.val) hover
  parentCountConstant := net.parentCountConstant
  parentCount := net.parentCount
  rounding := net.rounding

end QuantitativeVerticalRawParentNetReceipt

namespace QuantitativeVerticalRawColoredParentReceipt

/-- Joint selected output together with the occupied-parent equivalence back
to the raw target parents used by the same selection. -/
structure SelectionWithParentProvenance
    (raw : QuantitativeVerticalRawColoredParentReceipt
      quantitativeOutput geometry frostman floor) where
  joint : QuantitativeVerticalJointFiniteSelectionReceipt
    quantitativeOutput geometry frostman floor
  coordinateCount_eq :
    joint.coordinateCount =
      (quantitativeVerticalRequestedScaleSchedule
        quantitativeOutput geometry floor).levelCount
  actualScale_eq :
    ∀ coordinate,
      joint.actualScale coordinate =
        raw.actualScale (Fin.cast coordinateCount_eq coordinate)
  ambientParent :
    ∀ coordinate : Fin joint.coordinateCount,
      Fin (joint.coarse coordinate).card ↪
        Fin (raw.coarse (Fin.cast coordinateCount_eq coordinate)).card
  parent_eq :
    ∀ coordinate source,
      ambientParent coordinate ((joint.cover coordinate).parent source) =
        raw.parent (Fin.cast coordinateCount_eq coordinate)
          (joint.selected.embedding source)
  parent_occupied :
    ∀ coordinate parent,
      ∃ source,
        raw.parent (Fin.cast coordinateCount_eq coordinate)
            (joint.selected.embedding source) =
          ambientParent coordinate parent

/-- Occupied parents and their post-color-selection literal cover. -/
structure MonochromaticCoverData
    (raw : QuantitativeVerticalRawColoredParentReceipt
      quantitativeOutput geometry frostman floor)
    (coordinate : Fin (quantitativeVerticalRequestedScaleSchedule
      quantitativeOutput geometry floor).levelCount)
    (selected : Kakeya.Streamlined.TubeSubfamily
      (initialED quantitativeOutput geometry frostman).subfamily.family) where
  selectedParents : Kakeya.Streamlined.TubeSubfamily (raw.coarse coordinate)
  cover : WZ2PaperPurePartitioningCover selected.family selectedParents.family
  parent_embedding_eq :
    ∀ source,
      selectedParents.embedding (cover.parent source) =
        raw.parent coordinate (selected.embedding source)
  parent_occupied :
    ∀ parentIndex,
      ∃ source,
        raw.parent coordinate (selected.embedding source) =
          selectedParents.embedding parentIndex

/-- A monochromatic subfamily has a literal cover by exactly its occupied
parents. -/
noncomputable def monochromaticCover
    (raw : QuantitativeVerticalRawColoredParentReceipt
      quantitativeOutput geometry frostman floor)
    (coordinate : Fin (quantitativeVerticalRequestedScaleSchedule
      quantitativeOutput geometry floor).levelCount)
    (selected : Kakeya.Streamlined.TubeSubfamily
      (initialED quantitativeOutput geometry frostman).subfamily.family)
    (selectedColor : Fin (raw.colorCount coordinate))
    (monochromatic :
      ∀ source,
        raw.color coordinate (raw.parent coordinate
          (selected.embedding source)) = selectedColor) :
    MonochromaticCoverData quantitativeOutput geometry frostman floor
      raw coordinate selected := by
  let owner : Fin selected.family.card → Fin (raw.coarse coordinate).card :=
    fun source => raw.parent coordinate (selected.embedding source)
  let parentIndices : Finset (Fin (raw.coarse coordinate).card) :=
    Finset.univ.image owner
  let selectedParents :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      (raw.coarse coordinate) parentIndices
  let parentEquiv : Fin selectedParents.family.card ≃ parentIndices :=
    (parentIndices.orderIsoOfFin rfl).toEquiv
  have ownerMem : ∀ source, owner source ∈ parentIndices := by
    intro source
    exact Finset.mem_image.mpr ⟨source, Finset.mem_univ source, rfl⟩
  let targetParent : Fin selected.family.card →
      Fin selectedParents.family.card :=
    fun source => parentEquiv.symm ⟨owner source, ownerMem source⟩
  have targetParent_eq :
      ∀ source,
        selectedParents.embedding (targetParent source) = owner source := by
    intro source
    exact congrArg Subtype.val
      (parentEquiv.apply_symm_apply ⟨owner source, ownerMem source⟩)
  have targetParent_mem :
      ∀ source,
        source ∈ wz2PaperOrdinaryFullFiberIndices
          selected.family selectedParents.family (targetParent source) := by
    intro source
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff,
      selected.tube_eq, selectedParents.tube_eq, targetParent_eq]
    exact (mem_wz2PaperOrdinaryFullFiberIndices_iff
      (raw.parent coordinate (selected.embedding source))
      (selected.embedding source)).mp
        (raw.parent_covers coordinate (selected.embedding source))
  let cover : WZ2PaperPurePartitioningCover
      selected.family selectedParents.family := {
    covers := fun source => ⟨targetParent source, targetParent_mem source⟩
    doubled_fibers_disjoint := by
      intro first second hne
      rw [Finset.disjoint_left]
      intro source hfirst hsecond
      have hfirstAmbient :
          selected.embedding source ∈
            wz2PaperOrdinaryDilatedFiberIndices 2
              (initialED quantitativeOutput geometry frostman).subfamily.family
              (raw.coarse coordinate) (selectedParents.embedding first) := by
        simpa only [mem_wz2PaperOrdinaryDilatedFiberIndices_iff,
          selected.tube_eq, selectedParents.tube_eq] using hfirst
      have hsecondAmbient :
          selected.embedding source ∈
            wz2PaperOrdinaryDilatedFiberIndices 2
              (initialED quantitativeOutput geometry frostman).subfamily.family
              (raw.coarse coordinate) (selectedParents.embedding second) := by
        simpa only [mem_wz2PaperOrdinaryDilatedFiberIndices_iff,
          selected.tube_eq, selectedParents.tube_eq] using hsecond
      have hparentNe : selectedParents.embedding first ≠
          selectedParents.embedding second :=
        selectedParents.embedding.injective.ne hne
      have hcolorNe := raw.proper coordinate
        (selectedParents.embedding first) (selectedParents.embedding second)
        hparentNe
        ⟨selected.embedding source,
          Finset.mem_inter.mpr ⟨hfirstAmbient, hsecondAmbient⟩⟩
      have firstMem :=
        Finset.orderEmbOfFin_mem parentIndices rfl first
      have secondMem :=
        Finset.orderEmbOfFin_mem parentIndices rfl second
      rcases Finset.mem_image.mp firstMem with ⟨firstSource, _, hfirstOwner⟩
      rcases Finset.mem_image.mp secondMem with ⟨secondSource, _, hsecondOwner⟩
      apply hcolorNe
      change raw.color coordinate
          (parentIndices.orderEmbOfFin rfl first) =
        raw.color coordinate (parentIndices.orderEmbOfFin rfl second)
      rw [← hfirstOwner, ← hsecondOwner]
      simpa only [owner] using
        (monochromatic firstSource).trans (monochromatic secondSource).symm
  }
  refine {
    selectedParents := selectedParents
    cover := cover
    parent_embedding_eq := ?_
    parent_occupied := ?_
  }
  · intro source
    have hparent :
        cover.parent source = targetParent source :=
      cover.fullFiber_parent_unique
        (raw.actualScale_pos coordinate).le
        (cover.parent_mem_fullFiber source) (targetParent_mem source)
    rw [hparent, targetParent_eq]
  · intro parentIndex
    have hmem := Finset.orderEmbOfFin_mem parentIndices rfl parentIndex
    rcases Finset.mem_image.mp hmem with ⟨source, _, hsource⟩
    refine ⟨source, ?_⟩
    change raw.parent coordinate (selected.embedding source) =
      parentIndices.orderEmbOfFin rfl parentIndex
    simpa only [owner] using hsource

/-- One simultaneous color-vector pigeonhole and carrier-volume weighted
degree regularization produces the joint selection receipt. -/
theorem selectWithParentProvenance
    (raw : QuantitativeVerticalRawColoredParentReceipt
      quantitativeOutput geometry frostman floor) :
    Nonempty (SelectionWithParentProvenance
      quantitativeOutput geometry frostman floor raw) := by
  let ed := initialED quantitativeOutput geometry frostman
  let count := (quantitativeVerticalRequestedScaleSchedule
    quantitativeOutput geometry floor).levelCount
  let Color : Fin count → Type := fun coordinate => Fin (raw.colorCount coordinate)
  let Vertex : Fin count → Type := fun coordinate => Fin (raw.coarse coordinate).card
  let color : ∀ coordinate, Fin ed.subfamily.family.card → Color coordinate :=
    fun coordinate source => raw.color coordinate (raw.parent coordinate source)
  let parent : ∀ coordinate, Fin ed.subfamily.family.card → Vertex coordinate :=
    raw.parent
  let weight : Fin ed.subfamily.family.card → ENNReal :=
    fun index => MeasureTheory.volume (ed.finalShading.carrier index)
  letI colorNonempty : ∀ coordinate, Nonempty (Color coordinate) :=
    fun coordinate => ⟨⟨0, raw.colorCount_pos coordinate⟩⟩
  let regularized := Classical.choice <|
    wz2_finite_colored_degree_selection count Color Vertex color parent weight
      (quantitativeVerticalRequestedScaleSchedule
        quantitativeOutput geometry floor).levelCount_pos
  let selectedIndices := regularized.regularized.selected
  let selected := Kakeya.Streamlined.TubeSubfamily.fromFinset
    ed.subfamily.family selectedIndices
  have selectedMem : ∀ index : Fin selected.family.card,
      selected.embedding index ∈ selectedIndices := by
    intro index
    exact Finset.orderEmbOfFin_mem selectedIndices rfl index
  have totalWeightPos : 0 < ∑ index, weight index := by
    change 0 < ed.finalShading.mass
    have hright : 0 <
        (quantitativeVerticalPaperEDLoss quantitativeOutput geometry + 1) *
          ed.finalShading.mass :=
      geometry.cleanup_finalShading_mass_pos.trans_le ed.mass_retention
    by_contra hzero
    rw [not_lt, nonpos_iff_eq_zero] at hzero
    simp [hzero] at hright
  have selectedNonempty : selected.family.Nonempty := by
    exact (finiteColored_selected_nonempty regularized totalWeightPos).card_pos
  let mono : ∀ coordinate,
      MonochromaticCoverData quantitativeOutput geometry frostman floor
        raw coordinate selected :=
    fun coordinate => monochromaticCover
      quantitativeOutput geometry frostman floor raw coordinate selected
      (regularized.colorVector coordinate) (fun source => by
        have hclass := regularized.selected_subset_colorClass (selectedMem source)
        have hmono := regularized.monochromatic
          (selected.embedding source) hclass coordinate
        simpa only [color] using hmono)
  have selectedFilterCard :
      ∀ (coordinate : Fin count) (vertex : Vertex coordinate),
        (selectedIndices.filter fun index =>
          parent coordinate index = vertex).card =
        ((Finset.univ : Finset (Fin selected.family.card)).filter fun index =>
          parent coordinate (selected.embedding index) = vertex).card := by
    intro coordinate vertex
    let localIndices := (Finset.univ : Finset (Fin selected.family.card)).filter
      fun index => parent coordinate (selected.embedding index) = vertex
    have himage :
        Finset.image selected.embedding localIndices =
          selectedIndices.filter fun index => parent coordinate index = vertex := by
      ext index
      simp only [Finset.mem_image, localIndices, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨source, hparent, rfl⟩
        exact ⟨selectedMem source, hparent⟩
      · rintro ⟨hselected, hparent⟩
        let source : Fin selected.family.card :=
          (selectedIndices.orderIsoOfFin rfl).symm ⟨index, hselected⟩
        have hembedding : selected.embedding source = index :=
          congrArg Subtype.val
            ((selectedIndices.orderIsoOfFin rfl).apply_symm_apply
              ⟨index, hselected⟩)
        exact ⟨source, by rwa [hembedding], hembedding⟩
    calc
      _ = (Finset.image selected.embedding localIndices).card :=
        congrArg Finset.card himage.symm
      _ = localIndices.card :=
        Finset.card_image_of_injective _ selected.embedding.injective
  have fiberEq :
      ∀ coordinate parentIndex,
        wz2PaperOrdinaryFullFiberIndices selected.family
            (mono coordinate).selectedParents.family parentIndex =
          (Finset.univ : Finset (Fin selected.family.card)).filter fun source =>
            parent coordinate (selected.embedding source) =
              (mono coordinate).selectedParents.embedding parentIndex := by
    intro coordinate parentIndex
    ext source
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [(mono coordinate).cover.mem_fullFiber_iff_parent_eq
      (raw.actualScale_pos coordinate).le]
    constructor
    · intro h
      rw [← h]
      exact (mono coordinate).parent_embedding_eq source |>.symm
    · intro h
      apply (mono coordinate).selectedParents.embedding.injective
      rw [(mono coordinate).parent_embedding_eq source]
      exact h
  have selectedUniform :
      ∀ coordinate,
        WZ2PaperPureFullFibersAreCUniform selected.family
          (mono coordinate).selectedParents.family
          (16 * (count : ENNReal) *
            (Nat.log 2 (2 * ed.subfamily.family.card) + 1 : ENNReal) ^ count) := by
    intro coordinate first second
    change
      ((wz2PaperOrdinaryFullFiberIndices selected.family
          (mono coordinate).selectedParents.family first).card : ENNReal) ≤
        (16 * (count : ENNReal) *
          (Nat.log 2 (2 * ed.subfamily.family.card) + 1 : ENNReal) ^ count) *
        ((wz2PaperOrdinaryFullFiberIndices selected.family
          (mono coordinate).selectedParents.family second).card : ENNReal)
    rw [fiberEq coordinate first, fiberEq coordinate second]
    have hpositive :
        ∀ parentIndex : Fin (mono coordinate).selectedParents.family.card,
          0 < (selectedIndices.filter fun index =>
            parent coordinate index =
              (mono coordinate).selectedParents.embedding parentIndex).card := by
      intro parentIndex
      apply Finset.card_pos.mpr
      rcases (mono coordinate).parent_occupied parentIndex with
        ⟨source, hsource⟩
      refine ⟨selected.embedding source,
        Finset.mem_filter.mpr ⟨selectedMem source, ?_⟩⟩
      simpa only [parent] using hsource
    have hdegree := regularized.regularized.degree_uniform coordinate
      ((mono coordinate).selectedParents.embedding first)
      ((mono coordinate).selectedParents.embedding second)
      (hpositive first) (hpositive second)
    calc
      _ = ((selectedIndices.filter fun index =>
          parent coordinate index =
            (mono coordinate).selectedParents.embedding first).card : ENNReal) := by
        exact congrArg (fun cardinality : ℕ => (cardinality : ENNReal))
          (selectedFilterCard coordinate
            ((mono coordinate).selectedParents.embedding first)).symm
      _ ≤ (16 * (count : ENNReal) *
            (Nat.log 2 (2 * ed.subfamily.family.card) + 1 : ENNReal) ^ count) *
          ((selectedIndices.filter fun index =>
            parent coordinate index =
              (mono coordinate).selectedParents.embedding second).card : ENNReal) := by
        simpa only [selectedIndices, parent, Fintype.card_fin] using hdegree
      _ = _ := by
        apply congrArg (fun degree : ENNReal =>
          (16 * (count : ENNReal) *
            (Nat.log 2 (2 * ed.subfamily.family.card) + 1 : ENNReal) ^ count) *
              degree)
        exact congrArg (fun cardinality : ℕ => (cardinality : ENNReal))
          (selectedFilterCard coordinate
            ((mono coordinate).selectedParents.embedding second))
  let retentionConstant :=
    (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
      8 * (Nat.log 2 (2 * ed.subfamily.family.card) + 1 : ENNReal) ^ (count + 1)
  have retainedWeight :
      (∑ index, weight index) ≤
        retentionConstant * ∑ index ∈ selectedIndices, weight index := by
    simpa only [retentionConstant, selectedIndices, Fintype.card_fin] using
      finiteColored_retained_weight regularized
  have retainedMass :
      ed.finalShading.mass ≤ retentionConstant *
        (restrictPaperShading selected ed.finalShading).mass := by
    let equivalence := selectedIndices.orderIsoOfFin rfl
    have hsum :
        (∑ index : Fin selected.family.card,
          weight (selected.embedding index)) =
          ∑ index ∈ selectedIndices, weight index :=
      (Fintype.sum_equiv equivalence.toEquiv
        (fun index : Fin selected.family.card => weight (selected.embedding index))
        (fun index : selectedIndices => weight index.1) (fun _ => rfl)).trans
        (Finset.sum_coe_sort selectedIndices weight)
    calc
      ed.finalShading.mass = ∑ index, weight index := rfl
      _ ≤ retentionConstant * ∑ index ∈ selectedIndices, weight index :=
        retainedWeight
      _ = retentionConstant *
          (restrictPaperShading selected ed.finalShading).mass := by
        apply congrArg (fun mass => retentionConstant * mass)
        exact hsum.symm.trans
          (restrictPaperShading_mass selected ed.finalShading).symm
  have selectedParentCount :
      ∀ coordinate,
        ((mono coordinate).selectedParents.family).enncard ≤
          raw.parentCountConstant coordinate *
            (Kakeya.realRpowENN (raw.actualScale coordinate) 2)⁻¹ := by
    intro coordinate
    calc
      (mono coordinate).selectedParents.family.enncard ≤
          (raw.coarse coordinate).enncard := by
        simp only [Kakeya.Streamlined.TubeFamily.enncard]
        exact_mod_cast (by
          simpa only [Fintype.card_fin] using
            Fintype.card_le_of_injective
              (mono coordinate).selectedParents.embedding
              (mono coordinate).selectedParents.embedding.injective)
      _ ≤ _ := raw.parentCount coordinate
  let joint : QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor := {
    selected := selected
    selected_nonempty := selectedNonempty
    retentionConstant := retentionConstant
    retentionConstant_ne_top := by
      unfold retentionConstant
      apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · exact ENNReal.coe_ne_top
        · norm_num
      · simp
    retained_mass := retainedMass
    coordinateCount := count
    coordinateCount_pos :=
      (quantitativeVerticalRequestedScaleSchedule
        quantitativeOutput geometry floor).levelCount_pos
    actualScale := fun coordinate =>
      raw.actualScale coordinate
    actualScale_pos := raw.actualScale_pos
    coarse := fun coordinate => (mono coordinate).selectedParents.family
    cover := fun coordinate => (mono coordinate).cover
    degreeConstant := fun _ =>
      16 * (count : ENNReal) *
        (Nat.log 2 (2 * ed.subfamily.family.card) + 1 : ENNReal) ^ count
    fullFiberUniform := selectedUniform
    parentCountConstant := raw.parentCountConstant
    parentCount := selectedParentCount
    rounding := raw.rounding
  }
  refine ⟨{
    joint := joint
    coordinateCount_eq := rfl
    actualScale_eq := fun _ => rfl
    ambientParent := fun coordinate =>
      (mono coordinate).selectedParents.embedding
    parent_eq := ?_
    parent_occupied := ?_
  }⟩
  · intro coordinate source
    exact (mono coordinate).parent_embedding_eq source
  · intro coordinate parentIndex
    exact (mono coordinate).parent_occupied parentIndex

/-- Compatibility projection for callers that only need the joint receipt. -/
theorem select
    (raw : QuantitativeVerticalRawColoredParentReceipt
      quantitativeOutput geometry frostman floor) :
    Nonempty (QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor) := by
  rcases selectWithParentProvenance
      quantitativeOutput geometry frostman floor raw with ⟨output⟩
  exact ⟨output.joint⟩

/-- Closed adapter from the minimal target parent-net geometry to one
simultaneous colored, carrier-volume weighted joint selection. -/
theorem selectOfParentNet
    (net : QuantitativeVerticalRawParentNetReceipt
      quantitativeOutput geometry frostman floor) :
    Nonempty (QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor) :=
  select quantitativeOutput geometry frostman floor
    (net.toColored quantitativeOutput geometry frostman floor)

end QuantitativeVerticalRawColoredParentReceipt

end PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

end Kakeya.Assouad

end
