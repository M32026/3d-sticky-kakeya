import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.FiniteColoredDegreeSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.OneScaleAnchoredColoring

/-!
# Finite simultaneous selection for anchored covers

Specialize the generic dependent-color/degree regularizer to finitely many
anchored owner covers of one reanchored fine family.

The output is one indexed fine subfamily.  It is simultaneously
monochromatic for every reference-scale coarse coloring and has uniformly
comparable nonempty owner degrees at every reference scale.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private theorem pureWZ2_sum_orderEmbOfFin
    {n : ℕ}
    (selected : Finset (Fin n))
    (weight : Fin n → ENNReal) :
    (∑ index : Fin selected.card,
      weight (selected.orderEmbOfFin rfl index)) =
        ∑ index ∈ selected, weight index := by
  let equivalence : Fin selected.card ≃ selected :=
    (selected.orderIsoOfFin rfl).toEquiv
  calc
    (∑ index : Fin selected.card,
      weight (selected.orderEmbOfFin rfl index)) =
        ∑ index : selected, weight index.1 := by
      exact
        Fintype.sum_equiv equivalence
          (fun index : Fin selected.card =>
            weight (selected.orderEmbOfFin rfl index))
          (fun index : selected => weight index.1)
          (fun _ => rfl)
    _ = ∑ index ∈ selected, weight index :=
      Finset.sum_coe_sort selected weight

private theorem pureWZ2_filter_card_orderEmbOfFin
    {n : ℕ}
    (selected : Finset (Fin n))
    {Vertex : Type} [DecidableEq Vertex]
    (parent : Fin n → Vertex)
    (vertex : Vertex) :
    ((Finset.univ : Finset (Fin selected.card)).filter fun index =>
        parent (selected.orderEmbOfFin rfl index) = vertex).card =
      (selected.filter fun index =>
        parent index = vertex).card := by
  let embedding := (selected.orderEmbOfFin rfl).toEmbedding
  let source :=
    (Finset.univ : Finset (Fin selected.card)).filter fun index =>
      parent (embedding index) = vertex
  have himage :
      Finset.image embedding source =
        selected.filter fun index =>
          parent index = vertex := by
    ext index
    constructor
    · intro hindex
      rcases Finset.mem_image.mp hindex with
        ⟨sourceIndex, hsourceIndex, rfl⟩
      exact
        Finset.mem_filter.mpr
          ⟨Finset.orderEmbOfFin_mem selected rfl sourceIndex,
            (Finset.mem_filter.mp hsourceIndex).2⟩
    · intro hindex
      rcases Finset.mem_filter.mp hindex with
        ⟨hselected, hparent⟩
      let equivalence := selected.orderIsoOfFin rfl
      let sourceIndex : Fin selected.card :=
        equivalence.symm ⟨index, hselected⟩
      have hembedding :
          embedding sourceIndex = index := by
        exact congrArg Subtype.val
          (equivalence.apply_symm_apply
            ⟨index, hselected⟩)
      exact
        Finset.mem_image.mpr
          ⟨sourceIndex,
            Finset.mem_filter.mpr
              ⟨Finset.mem_univ sourceIndex, by
                rw [hembedding]
                exact hparent⟩,
            hembedding⟩
  calc
    source.card = (Finset.image embedding source).card :=
      (Finset.card_image_of_injective
        source embedding.injective).symm
    _ = _ := congrArg Finset.card himage

/-- Explicit simultaneous owner-degree regularization constant. -/
def pureWZ2FiniteAnchoredDegreeConstant
    (coordinateCount familyCard : ℕ) : ENNReal :=
  16 * (coordinateCount : ENNReal) *
    (Nat.log 2 (2 * familyCard) + 1 : ENNReal) ^
      coordinateCount

/-- Explicit color-vector and weighted regularization loss. -/
def pureWZ2FiniteAnchoredRetentionConstant
    (A : ℝ) (coordinateCount familyCard : ℕ) : ENNReal :=
  (Fintype.card
    (Fin coordinateCount →
      Fin (pureWZ2AnchoredCoarseConflictDegree A + 1)) :
      ENNReal) *
    (8 : ENNReal) *
      (Nat.log 2 (2 * familyCard) + 1 : ENNReal) ^
        (coordinateCount + 1)

/-- One final simultaneous anchored selection. -/
structure PureWZ2FiniteAnchoredSelectionData
    {delta A : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : Kakeya.Streamlined.TubeShading source}
    (fine : PureWZ2LocalizedDistinctReanchoringData sourceShading)
    (coordinateCount : ℕ)
    {constant : ENNReal}
    (scale :
      Fin coordinateCount →
        Kakeya.Streamlined.AdmissibleScale delta)
    (scaleData :
      ∀ coordinate,
        PureWZ2GWZScaleData
          (A := A) source (scale coordinate) constant)
    (oneScale :
      ∀ coordinate,
        PureWZ2OneScaleAnchoredOwnerCoverData
          fine (scaleData coordinate))
    (coloring :
      ∀ coordinate,
        PureWZ2OneScaleAnchoredColoringData
          fine (scaleData coordinate) (oneScale coordinate))
    (weight : Fin fine.family.card → ENNReal) where
  selected :
    WZ2PaperPureTubeSubfamily fine.family
  colorVector :
    Fin coordinateCount →
      Fin (pureWZ2AnchoredCoarseConflictDegree A + 1)
  monochromatic :
    ∀ coordinate selectedIndex,
      (coloring coordinate).fineColor
          (selected.embedding selectedIndex) =
        colorVector coordinate
  degreeConstant : ENNReal
  degreeConstant_eq :
    degreeConstant =
      pureWZ2FiniteAnchoredDegreeConstant
        coordinateCount fine.family.card
  degree_uniform :
    ∀ coordinate,
      ∀ first second :
        Fin (oneScale coordinate).coarse.card,
        0 <
            ((Finset.univ :
              Finset (Fin selected.family.card)).filter fun index =>
                (oneScale coordinate).cover.parent
                    (selected.embedding index) =
                  first).card →
        0 <
            ((Finset.univ :
              Finset (Fin selected.family.card)).filter fun index =>
                (oneScale coordinate).cover.parent
                    (selected.embedding index) =
                  second).card →
        (((Finset.univ :
          Finset (Fin selected.family.card)).filter fun index =>
            (oneScale coordinate).cover.parent
                (selected.embedding index) =
              first).card : ENNReal) ≤
          degreeConstant *
            (((Finset.univ :
              Finset (Fin selected.family.card)).filter fun index =>
                (oneScale coordinate).cover.parent
                    (selected.embedding index) =
                  second).card : ENNReal)
  retentionConstant : ENNReal
  retentionConstant_eq :
    retentionConstant =
      pureWZ2FiniteAnchoredRetentionConstant
        A coordinateCount fine.family.card
  retained_weight :
    (∑ index : Fin fine.family.card, weight index) ≤
      retentionConstant *
        ∑ index : Fin selected.family.card,
          weight (selected.embedding index)
  selected_weight_pos :
    ∀ index : Fin selected.family.card,
      0 < weight (selected.embedding index)
  weightLevel : ENNReal
  weightLevel_pos : 0 < weightLevel
  weight_band :
    ∀ index : Fin selected.family.card,
      weightLevel ≤ weight (selected.embedding index) ∧
        weight (selected.embedding index) ≤ 2 * weightLevel

/-- Build the one-shot simultaneous anchored selection. -/
theorem pureWZ2_finite_anchored_selection
    {delta A : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : Kakeya.Streamlined.TubeShading source}
    (fine : PureWZ2LocalizedDistinctReanchoringData sourceShading)
    (coordinateCount : ℕ)
    (coordinateCountPos : 0 < coordinateCount)
    {constant : ENNReal}
    (scale :
      Fin coordinateCount →
        Kakeya.Streamlined.AdmissibleScale delta)
    (scaleData :
      ∀ coordinate,
        PureWZ2GWZScaleData
          (A := A) source (scale coordinate) constant)
    (oneScale :
      ∀ coordinate,
        PureWZ2OneScaleAnchoredOwnerCoverData
          fine (scaleData coordinate))
    (coloring :
      ∀ coordinate,
        PureWZ2OneScaleAnchoredColoringData
          fine (scaleData coordinate) (oneScale coordinate))
    (weight : Fin fine.family.card → ENNReal) :
    Nonempty
      (PureWZ2FiniteAnchoredSelectionData
        fine coordinateCount scale scaleData oneScale coloring weight) := by
  let Color : Fin coordinateCount → Type :=
    fun _ =>
      Fin (pureWZ2AnchoredCoarseConflictDegree A + 1)
  let Vertex : Fin coordinateCount → Type :=
    fun coordinate => Fin (oneScale coordinate).coarse.card
  let color : ∀ coordinate,
      Fin fine.family.card → Color coordinate :=
    fun coordinate => (coloring coordinate).fineColor
  let parent : ∀ coordinate,
      Fin fine.family.card → Vertex coordinate :=
    fun coordinate => (oneScale coordinate).cover.parent
  rcases
      wz2_finite_colored_degree_selection
        coordinateCount Color Vertex color parent weight
        coordinateCountPos with
    ⟨regularized⟩
  let colorClass := regularized.colorClass
  let finalIndices := regularized.regularized.selected
  let finalEmbedding :=
    (finalIndices.orderEmbOfFin rfl).toEmbedding
  let selected :
      WZ2PaperPureTubeSubfamily fine.family :=
    WZ2PaperPureTubeSubfamily.fromFinset
      fine.family finalIndices
  have hselectedEmbedding :
      ∀ index : Fin selected.family.card,
        selected.embedding index = finalEmbedding index := by
    intro index
    rfl
  have hmonochromatic :
      ∀ coordinate selectedIndex,
        (coloring coordinate).fineColor
            (selected.embedding selectedIndex) =
          regularized.colorVector coordinate := by
    intro coordinate selectedIndex
    have hfinal :
        selected.embedding selectedIndex ∈ finalIndices :=
      Finset.orderEmbOfFin_mem finalIndices rfl selectedIndex
    have hcolorClass :
        selected.embedding selectedIndex ∈
          colorClass :=
      regularized.selected_subset_colorClass hfinal
    have hmono :=
      regularized.monochromatic
        (selected.embedding selectedIndex)
        hcolorClass coordinate
    simpa [color, Color] using hmono
  let degreeConstant : ENNReal :=
    pureWZ2FiniteAnchoredDegreeConstant
      coordinateCount fine.family.card
  have hdegreeUniform :
      ∀ coordinate,
        ∀ first second :
          Fin (oneScale coordinate).coarse.card,
          0 <
              ((Finset.univ :
                Finset (Fin selected.family.card)).filter fun index =>
                  (oneScale coordinate).cover.parent
                      (selected.embedding index) =
                    first).card →
          0 <
              ((Finset.univ :
                Finset (Fin selected.family.card)).filter fun index =>
                  (oneScale coordinate).cover.parent
                      (selected.embedding index) =
                    second).card →
          (((Finset.univ :
            Finset (Fin selected.family.card)).filter fun index =>
              (oneScale coordinate).cover.parent
                  (selected.embedding index) =
                first).card : ENNReal) ≤
            degreeConstant *
              (((Finset.univ :
                Finset (Fin selected.family.card)).filter fun index =>
                  (oneScale coordinate).cover.parent
                      (selected.embedding index) =
                    second).card : ENNReal) := by
    intro coordinate first second hfirst hsecond
    let coordinateParent :
        Fin fine.family.card →
          Fin (oneScale coordinate).coarse.card :=
      (oneScale coordinate).cover.parent
    have hfirstCard :
        ((Finset.univ :
          Finset (Fin selected.family.card)).filter fun index =>
            (oneScale coordinate).cover.parent
                (selected.embedding index) =
              first).card =
          (finalIndices.filter fun index =>
            coordinateParent index = first).card := by
      have hcard :=
        pureWZ2_filter_card_orderEmbOfFin
          finalIndices coordinateParent first
      change
        ((Finset.univ : Finset (Fin finalIndices.card)).filter
          fun index =>
            coordinateParent
                (finalIndices.orderEmbOfFin rfl index) =
              first).card =
          (finalIndices.filter fun index =>
            coordinateParent index = first).card
      exact hcard
    have hsecondCard :
        ((Finset.univ :
          Finset (Fin selected.family.card)).filter fun index =>
            (oneScale coordinate).cover.parent
                (selected.embedding index) =
              second).card =
          (finalIndices.filter fun index =>
            coordinateParent index = second).card := by
      have hcard :=
        pureWZ2_filter_card_orderEmbOfFin
          finalIndices coordinateParent second
      change
        ((Finset.univ : Finset (Fin finalIndices.card)).filter
          fun index =>
            coordinateParent
                (finalIndices.orderEmbOfFin rfl index) =
              second).card =
          (finalIndices.filter fun index =>
            coordinateParent index = second).card
      exact hcard
    have hregular :=
      regularized.regularized.degree_uniform
        coordinate first second
        (by
          simpa [parent, Vertex, coordinateParent] using
            (show 0 <
              (finalIndices.filter fun index =>
                coordinateParent index = first).card by
              rwa [← hfirstCard]))
        (by
          simpa [parent, Vertex, coordinateParent] using
            (show 0 <
              (finalIndices.filter fun index =>
                coordinateParent index = second).card by
              rwa [← hsecondCard]))
    rw [hfirstCard, hsecondCard]
    simpa [degreeConstant, pureWZ2FiniteAnchoredDegreeConstant,
      parent, Vertex, coordinateParent] using
      hregular
  let retentionConstant : ENNReal :=
    pureWZ2FiniteAnchoredRetentionConstant
      A coordinateCount fine.family.card
  have hselectedSum :
      (∑ index : Fin selected.family.card,
        weight (selected.embedding index)) =
        ∑ index ∈ finalIndices, weight index := by
    change
      (∑ index : Fin finalIndices.card,
        weight (finalIndices.orderEmbOfFin rfl index)) = _
    exact
      pureWZ2_sum_orderEmbOfFin finalIndices weight
  have hregularizedWeight :
      (∑ index : Fin fine.family.card,
        if index ∈ colorClass then weight index else 0) ≤
        (8 : ENNReal) *
          (Nat.log 2 (2 * fine.family.card) + 1 : ENNReal) ^
            (coordinateCount + 1) *
          ∑ index ∈ finalIndices, weight index := by
    have hraw := regularized.regularized.retained_weight
    have hright :
        (∑ index ∈ finalIndices,
          if index ∈ colorClass then weight index else 0) =
          ∑ index ∈ finalIndices, weight index := by
      apply Finset.sum_congr rfl
      intro index hindex
      rw [if_pos
        (regularized.selected_subset_colorClass hindex)]
    have hraw' :
        (∑ index : Fin fine.family.card,
          if index ∈ colorClass then weight index else 0) ≤
          (8 : ENNReal) *
            (Nat.log 2 (2 * fine.family.card) + 1 : ENNReal) ^
              (coordinateCount + 1) *
            ∑ index ∈ finalIndices,
              (if index ∈ colorClass then weight index else 0) := by
      simpa [colorClass, finalIndices, Fintype.card_fin] using hraw
    rwa [hright] at hraw'
  have hcolorClassSum :
      (∑ index : Fin fine.family.card,
        if index ∈ colorClass then weight index else 0) =
        ∑ index ∈ colorClass, weight index := by
    rw [Finset.sum_ite]
    simp
  have hretained :
      (∑ index : Fin fine.family.card, weight index) ≤
        retentionConstant *
          ∑ index : Fin selected.family.card,
            weight (selected.embedding index) := by
    calc
      (∑ index : Fin fine.family.card, weight index) ≤
          (Fintype.card
            (Fin coordinateCount →
              Fin (pureWZ2AnchoredCoarseConflictDegree A + 1)) :
              ENNReal) *
            ∑ index ∈ colorClass, weight index := by
        simpa [Color, colorClass] using regularized.color_retained
      _ =
          (Fintype.card
            (Fin coordinateCount →
              Fin (pureWZ2AnchoredCoarseConflictDegree A + 1)) :
              ENNReal) *
            (∑ index : Fin fine.family.card,
              if index ∈ colorClass then weight index else 0) := by
        rw [hcolorClassSum]
      _ ≤
          (Fintype.card
            (Fin coordinateCount →
              Fin (pureWZ2AnchoredCoarseConflictDegree A + 1)) :
              ENNReal) *
            ((8 : ENNReal) *
              (Nat.log 2 (2 * fine.family.card) + 1 : ENNReal) ^
                (coordinateCount + 1) *
              ∑ index ∈ finalIndices, weight index) := by
        exact mul_le_mul_left'
          hregularizedWeight
          (Fintype.card
            (Fin coordinateCount →
              Fin (pureWZ2AnchoredCoarseConflictDegree A + 1)) :
              ENNReal)
      _ =
          retentionConstant *
            ∑ index : Fin selected.family.card,
              weight (selected.embedding index) := by
        rw [hselectedSum]
        dsimp only [retentionConstant]
        dsimp only [pureWZ2FiniteAnchoredRetentionConstant]
        ring
  have hselectedWeightPos :
      ∀ index : Fin selected.family.card,
        0 < weight (selected.embedding index) := by
    intro index
    have hraw :=
      regularized.regularized.selected_weight_pos
        (finalEmbedding index)
        (Finset.orderEmbOfFin_mem finalIndices rfl index)
    have hinside :
        finalEmbedding index ∈ colorClass :=
      regularized.selected_subset_colorClass
        (Finset.orderEmbOfFin_mem finalIndices rfl index)
    rw [if_pos hinside] at hraw
    simpa only [hselectedEmbedding] using hraw
  have hweightBand :
      ∀ index : Fin selected.family.card,
        regularized.regularized.weightLevel ≤
            weight (selected.embedding index) ∧
          weight (selected.embedding index) ≤
            2 * regularized.regularized.weightLevel := by
    intro index
    have hraw :=
      regularized.regularized.weight_band
        (finalEmbedding index)
        (Finset.orderEmbOfFin_mem finalIndices rfl index)
    have hinside :
        finalEmbedding index ∈ colorClass :=
      regularized.selected_subset_colorClass
        (Finset.orderEmbOfFin_mem finalIndices rfl index)
    rw [if_pos hinside] at hraw
    simpa only [hselectedEmbedding] using hraw
  exact
    ⟨{
      selected := selected
      colorVector := regularized.colorVector
      monochromatic := hmonochromatic
      degreeConstant := degreeConstant
      degreeConstant_eq := rfl
      degree_uniform := hdegreeUniform
      retentionConstant := retentionConstant
      retentionConstant_eq := rfl
      retained_weight := hretained
      selected_weight_pos := hselectedWeightPos
      weightLevel := regularized.regularized.weightLevel
      weightLevel_pos :=
        regularized.regularized.weightLevel_pos
      weight_band := hweightBand
    }⟩

end Kakeya.Assouad

end
