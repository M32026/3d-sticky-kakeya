import MyLeanRepo.Kakeya.Assouad.PureWZ2.CallerCenterEnvelopeBodyCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.FiniteColoredDegreeSelection

/-!
# Finite simultaneous selection of quotient callers

At every scheduled ambient scale, color the raw envelope conflict graph.
Then perform one dependent color-vector pigeonhole and one simultaneous
degree regularization on the caller indices themselves.

The output is one caller subfamily that is monochromatic at every coordinate
and whose nonempty scheduled-owner classes have uniformly comparable
cardinality.  No coordinate is processed by a sequential restriction.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private theorem sum_orderEmbOfFin
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

private theorem filter_card_orderEmbOfFin
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
      have hembedding : embedding sourceIndex = index :=
        congrArg Subtype.val
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

def pureWZ2FiniteCallerCenterDegreeConstant
    (coordinateCount callerCard : ℕ) : ENNReal :=
  16 * (coordinateCount : ENNReal) *
    (Nat.log 2 (2 * callerCard) + 1 : ENNReal) ^
      coordinateCount

def pureWZ2FiniteCallerCenterRetentionConstant
    (coordinateCount callerCard : ℕ)
    (Color : Fin coordinateCount → Type)
    [∀ coordinate, Fintype (Color coordinate)] : ENNReal :=
  (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
    8 *
      (Nat.log 2 (2 * callerCard) + 1 : ENNReal) ^
        (coordinateCount + 1)

structure PureWZ2FiniteCallerCenterSelectionData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (callerBase : WZ2PaperPureTubeSubfamily quotient.callerCoarse)
    (coordinateCount : ℕ)
    (scales : Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (Color : Fin coordinateCount → Type)
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    (coloring :
      ∀ coordinate,
        PureWZ2CallerCenterEnvelopeColoringData
          quotient (scheduled coordinate) callerBase
          (Color coordinate))
    (weight : Fin callerBase.family.card → ENNReal) where
  selected : WZ2PaperPureTubeSubfamily callerBase.family
  colorVector : ∀ coordinate, Color coordinate
  monochromatic :
    ∀ coordinate selectedIndex,
      (coloring coordinate).color
          (pureWZ2CallerCenterScheduledOwner
            quotient (scheduled coordinate)
            (callerBase.embedding
              (selected.embedding selectedIndex))) =
        colorVector coordinate
  degreeConstant : ENNReal
  degreeConstant_eq :
    degreeConstant =
      pureWZ2FiniteCallerCenterDegreeConstant
        coordinateCount callerBase.family.card
  degree_uniform :
    ∀ coordinate,
      ∀ first second :
          Fin (scheduled coordinate).scaleData.coarse.card,
        0 <
            ((Finset.univ :
              Finset (Fin selected.family.card)).filter fun index =>
                pureWZ2CallerCenterScheduledOwner
                    quotient (scheduled coordinate)
                    (callerBase.embedding
                      (selected.embedding index)) =
                  first).card →
        0 <
            ((Finset.univ :
              Finset (Fin selected.family.card)).filter fun index =>
                pureWZ2CallerCenterScheduledOwner
                    quotient (scheduled coordinate)
                    (callerBase.embedding
                      (selected.embedding index)) =
                  second).card →
        (((Finset.univ :
          Finset (Fin selected.family.card)).filter fun index =>
            pureWZ2CallerCenterScheduledOwner
                quotient (scheduled coordinate)
                (callerBase.embedding
                  (selected.embedding index)) =
              first).card : ENNReal) ≤
          degreeConstant *
            (((Finset.univ :
              Finset (Fin selected.family.card)).filter fun index =>
                pureWZ2CallerCenterScheduledOwner
                    quotient (scheduled coordinate)
                    (callerBase.embedding
                      (selected.embedding index)) =
                  second).card : ENNReal)
  retentionConstant : ENNReal
  retentionConstant_eq :
    retentionConstant =
      pureWZ2FiniteCallerCenterRetentionConstant
        coordinateCount callerBase.family.card Color
  retained_weight :
    (∑ index : Fin callerBase.family.card, weight index) ≤
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

theorem pureWZ2_finite_caller_center_selection
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (callerBase : WZ2PaperPureTubeSubfamily quotient.callerCoarse)
    (coordinateCount : ℕ)
    (coordinateCountPos : 0 < coordinateCount)
    (scales : Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (Color : Fin coordinateCount → Type)
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    (coloring :
      ∀ coordinate,
        PureWZ2CallerCenterEnvelopeColoringData
          quotient (scheduled coordinate) callerBase
          (Color coordinate))
    (weight : Fin callerBase.family.card → ENNReal) :
    Nonempty
      (PureWZ2FiniteCallerCenterSelectionData
        quotient callerBase coordinateCount scales scheduled
        Color coloring weight) := by
  let Vertex : Fin coordinateCount → Type :=
    fun coordinate =>
      Fin (scheduled coordinate).scaleData.coarse.card
  let color :
      ∀ coordinate,
        Fin callerBase.family.card → Color coordinate :=
    fun coordinate callerIndex =>
      (coloring coordinate).color
        (pureWZ2CallerCenterScheduledOwner
          quotient (scheduled coordinate)
          (callerBase.embedding callerIndex))
  let parent :
      ∀ coordinate,
        Fin callerBase.family.card → Vertex coordinate :=
    fun coordinate callerIndex =>
      pureWZ2CallerCenterScheduledOwner
        quotient (scheduled coordinate)
        (callerBase.embedding callerIndex)
  rcases
      wz2_finite_colored_degree_selection
        coordinateCount Color Vertex color parent weight
        coordinateCountPos with
    ⟨regularized⟩
  let colorClass := regularized.colorClass
  let finalIndices := regularized.regularized.selected
  let selected :
      WZ2PaperPureTubeSubfamily callerBase.family :=
    WZ2PaperPureTubeSubfamily.fromFinset
      callerBase.family finalIndices
  have hmonochromatic :
      ∀ coordinate selectedIndex,
        (coloring coordinate).color
            (pureWZ2CallerCenterScheduledOwner
              quotient (scheduled coordinate)
              (callerBase.embedding
                (selected.embedding selectedIndex))) =
          regularized.colorVector coordinate := by
    intro coordinate selectedIndex
    have hfinal :
        selected.embedding selectedIndex ∈ finalIndices :=
      Finset.orderEmbOfFin_mem finalIndices rfl selectedIndex
    have hclass :
        selected.embedding selectedIndex ∈ colorClass :=
      regularized.selected_subset_colorClass hfinal
    have hmono :=
      regularized.monochromatic
        (selected.embedding selectedIndex) hclass coordinate
    simpa [color] using hmono
  let degreeConstant :=
    pureWZ2FiniteCallerCenterDegreeConstant
      coordinateCount callerBase.family.card
  have hdegree :
      ∀ coordinate,
        ∀ first second : Vertex coordinate,
          0 <
              ((Finset.univ :
                Finset (Fin selected.family.card)).filter fun index =>
                  parent coordinate
                      (selected.embedding index) =
                    first).card →
          0 <
              ((Finset.univ :
                Finset (Fin selected.family.card)).filter fun index =>
                  parent coordinate
                      (selected.embedding index) =
                    second).card →
          (((Finset.univ :
            Finset (Fin selected.family.card)).filter fun index =>
              parent coordinate
                  (selected.embedding index) =
                first).card : ENNReal) ≤
            degreeConstant *
              (((Finset.univ :
                Finset (Fin selected.family.card)).filter fun index =>
                  parent coordinate
                      (selected.embedding index) =
                    second).card : ENNReal) := by
    intro coordinate first second hfirst hsecond
    have hfirstCard :=
      filter_card_orderEmbOfFin
        finalIndices (parent coordinate) first
    have hsecondCard :=
      filter_card_orderEmbOfFin
        finalIndices (parent coordinate) second
    have hraw :=
      regularized.regularized.degree_uniform
        coordinate first second
        (by
          simpa [parent, Vertex] using
            (show 0 <
              (finalIndices.filter fun index =>
                parent coordinate index = first).card by
              rwa [← hfirstCard]))
        (by
          simpa [parent, Vertex] using
            (show 0 <
              (finalIndices.filter fun index =>
                parent coordinate index = second).card by
              rwa [← hsecondCard]))
    change
      (((Finset.univ :
        Finset (Fin finalIndices.card)).filter fun index =>
          parent coordinate
              (finalIndices.orderEmbOfFin rfl index) =
            first).card : ENNReal) ≤
        degreeConstant *
          (((Finset.univ :
            Finset (Fin finalIndices.card)).filter fun index =>
              parent coordinate
                  (finalIndices.orderEmbOfFin rfl index) =
                second).card : ENNReal)
    rw [hfirstCard, hsecondCard]
    simpa [degreeConstant,
      pureWZ2FiniteCallerCenterDegreeConstant,
      parent, Vertex] using hraw
  let retentionConstant :=
    pureWZ2FiniteCallerCenterRetentionConstant
      coordinateCount callerBase.family.card Color
  have hselectedSum :
      (∑ index : Fin selected.family.card,
        weight (selected.embedding index)) =
        ∑ index ∈ finalIndices, weight index :=
    sum_orderEmbOfFin finalIndices weight
  have hregularizedWeight :
      (∑ index : Fin callerBase.family.card,
        if index ∈ colorClass then weight index else 0) ≤
        (8 : ENNReal) *
          (Nat.log 2 (2 * callerBase.family.card) + 1 : ENNReal) ^
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
        (∑ index : Fin callerBase.family.card,
          if index ∈ colorClass then weight index else 0) ≤
          (8 : ENNReal) *
            (Nat.log 2 (2 * callerBase.family.card) + 1 : ENNReal) ^
              (coordinateCount + 1) *
            ∑ index ∈ finalIndices,
              (if index ∈ colorClass then weight index else 0) := by
      simpa [colorClass, finalIndices, Fintype.card_fin] using hraw
    rwa [hright] at hraw'
  have hcolorClassSum :
      (∑ index : Fin callerBase.family.card,
        if index ∈ colorClass then weight index else 0) =
        ∑ index ∈ colorClass, weight index := by
    rw [Finset.sum_ite]
    simp
  have hretained :
      (∑ index : Fin callerBase.family.card, weight index) ≤
        retentionConstant *
          ∑ index : Fin selected.family.card,
            weight (selected.embedding index) := by
    calc
      (∑ index : Fin callerBase.family.card, weight index) ≤
          (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
            ∑ index ∈ colorClass, weight index := by
        simpa [colorClass] using regularized.color_retained
      _ =
          (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
            (∑ index : Fin callerBase.family.card,
              if index ∈ colorClass then weight index else 0) := by
        rw [hcolorClassSum]
      _ ≤
          (Fintype.card (∀ coordinate, Color coordinate) : ENNReal) *
            ((8 : ENNReal) *
              (Nat.log 2 (2 * callerBase.family.card) + 1 : ENNReal) ^
                (coordinateCount + 1) *
              ∑ index ∈ finalIndices, weight index) := by
        gcongr
      _ =
          retentionConstant *
            ∑ index : Fin selected.family.card,
              weight (selected.embedding index) := by
        rw [hselectedSum]
        dsimp only [retentionConstant]
        dsimp only [pureWZ2FiniteCallerCenterRetentionConstant]
        ring
  have hselectedPositive :
      ∀ index : Fin selected.family.card,
        0 < weight (selected.embedding index) := by
    intro index
    have hselected :
        selected.embedding index ∈ finalIndices :=
      Finset.orderEmbOfFin_mem finalIndices rfl index
    have hclass :
        selected.embedding index ∈ colorClass :=
      regularized.selected_subset_colorClass hselected
    have hraw :=
      regularized.regularized.selected_weight_pos
        (selected.embedding index) hselected
    rw [if_pos hclass] at hraw
    exact hraw
  have hweightBand :
      ∀ index : Fin selected.family.card,
        regularized.regularized.weightLevel ≤
            weight (selected.embedding index) ∧
          weight (selected.embedding index) ≤
            2 * regularized.regularized.weightLevel := by
    intro index
    have hselected :
        selected.embedding index ∈ finalIndices :=
      Finset.orderEmbOfFin_mem finalIndices rfl index
    have hclass :
        selected.embedding index ∈ colorClass :=
      regularized.selected_subset_colorClass hselected
    have hraw :=
      regularized.regularized.weight_band
        (selected.embedding index) hselected
    rw [if_pos hclass] at hraw
    exact hraw
  exact
    ⟨{
      selected := selected
      colorVector := regularized.colorVector
      monochromatic := hmonochromatic
      degreeConstant := degreeConstant
      degreeConstant_eq := rfl
      degree_uniform := by
        simpa [parent, Vertex] using hdegree
      retentionConstant := retentionConstant
      retentionConstant_eq := rfl
      retained_weight := hretained
      selected_weight_pos := hselectedPositive
      weightLevel := regularized.regularized.weightLevel
      weightLevel_pos :=
        regularized.regularized.weightLevel_pos
      weight_band := hweightBand
    }⟩

end Kakeya.Assouad

end
