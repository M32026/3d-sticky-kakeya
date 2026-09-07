import MyLeanRepo.Kakeya.Assouad.PureWZ2.ExtremalSpatialCellLocalization

/-!
# Conditional extremal spatial-cell CWA producer

The public pure extremal configuration has no spatial support hypothesis.
The source union-volume upper bound is inherited by every local subshading,
but it does not by itself provide a fixed-radius cell carrying a prescribed
fraction of the indexed shaded mass.  This module therefore isolates that
geometric input and closes everything after it.

The missing geometric estimate must produce a fixed-radius cell with both
`source_mass_retention` and `per_tube_local_density`: the source pruning
controls the full source carrier of each tube, but that lower bound does not
automatically survive intersection with one cell.  The theorem below then applies
the finite weighted-selection route underlying
`weighted_degree_uniform_restricted_cwa` to the local shaded-volume weights,
with absorption required only for the constants actually produced.
Thus the final nearby pure CWA, local density, source-mass retention, and
local support all refer to the same selected family.  No direct-subfamily
CWA inheritance and no cardinality-only fallback are used.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The normalization used when the local weights are shaded volumes. -/
def pureWZ2SpatialCellNormalizationWeight
    (delta sourceLoss cellLoss : ℝ) : ENNReal :=
  Kakeya.realRpowENN delta sourceLoss *
    Kakeya.realRpowENN delta cellLoss *
      Kakeya.deltaTubeVolume delta

/-- Actual simultaneous-degree constant used by the spatial-cell schedule. -/
def pureWZ2SpatialCellDegreeConstant
    (epsilon : ℝ) (card : ℕ) : ENNReal :=
  16 * (geometricScaleCount epsilon : ENNReal) *
    (Nat.log 2 (2 * card) + 1 : ENNReal) ^
      geometricScaleCount epsilon

/-- Actual weighted-retention loss used by the spatial-cell schedule. -/
def pureWZ2SpatialCellRegularizationLoss
    (epsilon : ℝ) (card : ℕ) : ENNReal :=
  8 *
    (Nat.log 2 (2 * card) + 1 : ENNReal) ^
      (geometricScaleCount epsilon + 1)

/--
A fixed-cell selection before simultaneous degree regularization.

The local family may already be a subfamily of the per-tube pruning, but it
must retain the pruning density on each of its local shaded carriers.  The
field `source_mass_retention` is strictly the geometric high-weight-cell
estimate; it contains no CWA conclusion.
-/
structure PureWZ2SpatialCellPreselectionData
    {sigma sourceLoss pruningLoss cellLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss) where
  preSelected : WZ2PaperPureTubeSubfamily source.family
  preSelected_nonempty : preSelected.family.Nonempty
  selected_from_pruning :
    ∀ index, preSelected.embedding index ∈ pruning.indices
  localShading :
    Kakeya.Streamlined.TubeShading preSelected.family
  subshading :
    ∀ index,
      localShading.carrier index ⊆
        source.shading.carrier (preSelected.embedding index)
  per_tube_local_density :
    ∀ index,
      Kakeya.realRpowENN delta pruningLoss *
          (preSelected.family.tube index).volume ≤
        volume (localShading.carrier index)
  source_mass_retention :
    Kakeya.realRpowENN delta cellLoss *
        source.shading.mass ≤
      localShading.mass
  center : Point3
  family_bases_local :
    ∀ index,
      dist (preSelected.family.tube index).base center ≤ 3
  shading_support_local :
    localShading.union ⊆ Metric.closedBall center 1

namespace PureWZ2SpatialCellPreselectionData

variable
    {sigma sourceLoss pruningLoss cellLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss}
    (data :
      PureWZ2SpatialCellPreselectionData
        (cellLoss := cellLoss)
        source pruning)

/--
The source extremal volume upper bound passes to the cell-local union.

This is the exact consequence of `source.extremal.volume_upper`; the reverse
high-weight-cell estimate is the separate `source_mass_retention` field.
-/
theorem local_union_volume_upper :
    volume data.localShading.union ≤
      Kakeya.realRpowENN delta (sigma - sourceLoss) := by
  have localSubset :
      data.localShading.union ⊆ source.shading.union := by
    rintro point ⟨index, pointMem⟩
    exact
      ⟨data.preSelected.embedding index,
        data.subshading index pointMem⟩
  exact
    (measure_mono localSubset).trans
      source.extremal.volume_upper

end PureWZ2SpatialCellPreselectionData

/--
The weighted spatial-cell certificate together with its exact provenance in
the supplied preselection family.

The weighted regularizer may delete tubes.  It therefore records an embedding
of every final selected index into the preselection, rather than the false
converse assertion that the preselection covers every pruning index.
-/
structure PureWZ2SpatialCellSelectionFromPreselectionData
    {sigma sourceLoss inputLoss pruningLoss cellLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss}
    (data :
      PureWZ2SpatialCellPreselectionData
        (cellLoss := cellLoss) source pruning) where
  certificate :
    PureWZ2SpatialCellSelectionCertificate
      (inputLoss := inputLoss) source pruning
  preselectionIndex :
    Fin certificate.selected.family.card →
      Fin data.preSelected.family.card
  source_index_eq :
    ∀ index,
      certificate.selected.embedding index =
        data.preSelected.embedding (preselectionIndex index)
  localShading_subset_preselection :
    ∀ index,
      certificate.localShading.carrier index ⊆
        data.localShading.carrier (preselectionIndex index)

/--
The weighted restricted-CWA theorem with absorption required only at its
actual finite constants.

The shared theorem exposes a stronger all-finite-constants premise.  This
specialization unfolds the same closed finite selector so that the caller
pays only the degree and retention constants that are actually returned.
-/
theorem pureWZ2_weighted_restricted_cwa_actual
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (preSelected : WZ2PaperPureTubeSubfamily fine)
    (preSelectedNonempty : preSelected.family.Nonempty)
    (externalWeight :
      Fin preSelected.family.card → ENNReal)
    (normalizationWeight weightUpper : ENNReal)
    (normalizationWeight_ne_zero : normalizationWeight ≠ 0)
    (normalizationWeight_ne_top : normalizationWeight ≠ ⊤)
    (weightUpper_ne_top : weightUpper ≠ ⊤)
    (total_weight_lower :
      normalizationWeight * fine.enncard ≤
        ∑ index : Fin preSelected.family.card,
          externalWeight index)
    (weight_upper :
      ∀ index, externalWeight index ≤ weightUpper)
    (epsilon : ℝ)
    (epsilon_pos : 0 < epsilon)
    (delta_pos : 0 < delta)
    (delta_lt_one : delta < 1)
    (output_ne_top : outputConstant ≠ ⊤)
    (rounding_absorption :
      ENNReal.ofReal (Real.rpow delta (-epsilon)) *
          ambientConstant ≤
        outputConstant)
    (restriction_absorption :
      wz2PaperPureNearbyRestrictionConstant
          ambientConstant normalizationWeight
          (pureWZ2SpatialCellDegreeConstant
            epsilon preSelected.family.card)
          (pureWZ2SpatialCellRegularizationLoss
              epsilon preSelected.family.card *
            weightUpper) ≤
        outputConstant) :
    ∃ selectedPre :
        WZ2PaperPureTubeSubfamily preSelected.family,
      selectedPre.family.Nonempty ∧
      (∃ selectedIndices : Finset (Fin preSelected.family.card),
        selectedPre =
          WZ2PaperPureTubeSubfamily.fromFinset
            preSelected.family selectedIndices) ∧
      (∑ index : Fin preSelected.family.card,
          externalWeight index) ≤
        pureWZ2SpatialCellRegularizationLoss
            epsilon preSelected.family.card *
          ∑ index : Fin selectedPre.family.card,
            externalWeight (selectedPre.embedding index) ∧
      (∀ index : Fin selectedPre.family.card,
        (∑ source : Fin preSelected.family.card,
            externalWeight source) /
              (2 * preSelected.family.card : ENNReal) ≤
          externalWeight (selectedPre.embedding index)) ∧
      WZ2PaperPureCWAAtNearbyScales
        (WZ2PaperPureTubeSubfamily.comp
          preSelected selectedPre).family
        outputConstant := by
  let coordinateCount := geometricScaleCount epsilon
  have coordinateCountPos : 0 < coordinateCount :=
    Nat.succ_pos _
  let scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta :=
    geometricRequestedScales
      delta epsilon delta_pos delta_lt_one
        epsilon_pos coordinateCount
  let coverData :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant :=
    fun coordinate =>
      Classical.choice (ambient.2.2.2 (scales coordinate))
  let Vertex : Fin coordinateCount → Type :=
    fun coordinate =>
      Fin (coverData coordinate).scaleData.coarse.card
  let parent :
      ∀ coordinate,
        Fin preSelected.family.card → Vertex coordinate :=
    fun coordinate source =>
      (coverData coordinate).scaleData.cover.parent
        (preSelected.embedding source)
  rcases
      wz2_finite_weighted_degree_selection
        coordinateCount Vertex parent externalWeight
        coordinateCountPos with
    ⟨regularized⟩
  let selectedIndices := regularized.selected
  let selectedPre :=
    WZ2PaperPureTubeSubfamily.fromFinset
      preSelected.family selectedIndices
  let selected :=
    WZ2PaperPureTubeSubfamily.comp preSelected selectedPre
  let degreeConstant :=
    pureWZ2SpatialCellDegreeConstant
      epsilon preSelected.family.card
  let regularizationLoss :=
    pureWZ2SpatialCellRegularizationLoss
      epsilon preSelected.family.card
  have totalWeightPos :
      0 <
        ∑ index : Fin preSelected.family.card,
          externalWeight index := by
    have fineCardPos : 0 < fine.card := by
      have preCardPos : 0 < preSelected.family.card :=
        preSelectedNonempty
      have indexLt :=
        (preSelected.embedding ⟨0, preCardPos⟩).isLt
      omega
    have fineENNPos : 0 < fine.enncard := by
      change (0 : ENNReal) < (fine.card : ENNReal)
      exact_mod_cast fineCardPos
    exact
      (ENNReal.mul_pos
        normalizationWeight_ne_zero fineENNPos.ne').trans_le
        total_weight_lower
  have selectedIndicesNonempty : selectedIndices.Nonempty := by
    by_contra hnonempty
    have selectedEmpty : selectedIndices = ∅ := by
      simpa using hnonempty
    have retained := regularized.retained_weight
    have selectedSumZero :
        (∑ index ∈ regularized.selected,
          externalWeight index) = 0 := by
      have hregularizedEmpty :
          regularized.selected = ∅ := by
        simpa [selectedIndices] using selectedEmpty
      rw [hregularizedEmpty]
      simp
    rw [selectedSumZero, mul_zero] at retained
    exact (not_le_of_gt totalWeightPos) retained
  have selectedNonempty : selected.family.Nonempty := by
    change 0 < selectedIndices.card
    exact selectedIndicesNonempty.card_pos
  have degreeTop : degreeConstant ≠ ⊤ :=
    ENNReal.coe_ne_top
  have regularizationTop : regularizationLoss ≠ ⊤ :=
    ENNReal.coe_ne_top
  have embeddingMem :
      ∀ index : Fin selectedPre.family.card,
        selectedPre.embedding index ∈ selectedIndices := by
    intro index
    exact Finset.orderEmbOfFin_mem selectedIndices rfl index
  have selectedWeightFloor :
      ∀ index : Fin selectedPre.family.card,
        (∑ source : Fin preSelected.family.card,
            externalWeight source) /
              (2 * preSelected.family.card : ENNReal) ≤
          externalWeight (selectedPre.embedding index) := by
    intro index
    have cardFin :
        Fintype.card (Fin preSelected.family.card) =
          preSelected.family.card := by simp
    simpa [cardFin] using
      regularized.selected_weight_floor
        (selectedPre.embedding index) (embeddingMem index)
  have imageUniv :
      Finset.image selectedPre.embedding
          (Finset.univ :
            Finset (Fin selectedPre.family.card)) =
        selectedIndices := by
    have subset :
        Finset.image selectedPre.embedding
            (Finset.univ :
              Finset (Fin selectedPre.family.card)) ⊆
          selectedIndices := by
      intro source hsource
      rcases Finset.mem_image.mp hsource with
        ⟨index, _, rfl⟩
      exact embeddingMem index
    have cardEq :
        (Finset.image selectedPre.embedding
          (Finset.univ :
            Finset (Fin selectedPre.family.card))).card =
          selectedIndices.card := by
      rw [Finset.card_image_of_injective _
        selectedPre.embedding.injective]
      change
        (Finset.univ :
          Finset (Fin selectedIndices.card)).card =
            selectedIndices.card
      simp
    exact
      Finset.eq_of_subset_of_card_le subset
        (by rw [cardEq])
  have embeddingSurjective :
      ∀ source ∈ selectedIndices,
        ∃ index : Fin selectedPre.family.card,
          selectedPre.embedding index = source := by
    intro source hsource
    have sourceImage :
        source ∈
          Finset.image selectedPre.embedding
            (Finset.univ :
              Finset (Fin selectedPre.family.card)) := by
      rw [imageUniv]
      exact hsource
    rcases Finset.mem_image.mp sourceImage with
      ⟨index, _, hindex⟩
    exact ⟨index, hindex⟩
  have selectedWeightEq :
      (∑ index : Fin selectedPre.family.card,
          externalWeight (selectedPre.embedding index)) =
        ∑ source ∈ selectedIndices,
          externalWeight source := by
    calc
      (∑ index : Fin selectedPre.family.card,
          externalWeight (selectedPre.embedding index)) =
          ∑ source ∈
              Finset.image selectedPre.embedding
                (Finset.univ :
                  Finset (Fin selectedPre.family.card)),
            externalWeight source := by
        exact
          (Finset.sum_image
            (fun first _ second _ heq =>
              selectedPre.embedding.injective heq)).symm
      _ =
          ∑ source ∈ selectedIndices,
            externalWeight source := by
        rw [imageUniv]
  have retainedWeight :
      (∑ index : Fin preSelected.family.card,
          externalWeight index) ≤
        regularizationLoss *
          ∑ index : Fin selectedPre.family.card,
            externalWeight (selectedPre.embedding index) := by
    have retained := regularized.retained_weight
    have cardFin :
        Fintype.card (Fin preSelected.family.card) =
          preSelected.family.card := by
      simp
    rw [cardFin] at retained
    change
      (∑ index : Fin preSelected.family.card,
          externalWeight index) ≤
        regularizationLoss *
          ∑ index ∈ selectedIndices,
            externalWeight index at retained
    simpa [regularizationLoss,
      pureWZ2SpatialCellRegularizationLoss,
      coordinateCount] using
      (selectedWeightEq ▸ retained)
  have selectedWeightUpper :
      (∑ index : Fin selectedPre.family.card,
          externalWeight (selectedPre.embedding index)) ≤
        selected.family.enncard * weightUpper := by
    change
      (∑ index : Fin selectedPre.family.card,
          externalWeight (selectedPre.embedding index)) ≤
        (selectedPre.family.card : ENNReal) * weightUpper
    calc
      (∑ index : Fin selectedPre.family.card,
          externalWeight (selectedPre.embedding index)) ≤
          ∑ _index : Fin selectedPre.family.card,
            weightUpper := by
        exact
          Finset.sum_le_sum fun index _ =>
            weight_upper (selectedPre.embedding index)
      _ =
          (selectedPre.family.card : ENNReal) * weightUpper := by
        simp [Finset.sum_const]
  have cardinalityRetention :
      normalizationWeight * fine.enncard ≤
        (regularizationLoss * weightUpper) *
          selected.family.enncard := by
    calc
      normalizationWeight * fine.enncard ≤
          ∑ index : Fin preSelected.family.card,
            externalWeight index :=
        total_weight_lower
      _ ≤
          regularizationLoss *
            ∑ index : Fin selectedPre.family.card,
              externalWeight (selectedPre.embedding index) :=
        retainedWeight
      _ ≤
          regularizationLoss *
            (selected.family.enncard * weightUpper) := by
        gcongr
      _ =
          (regularizationLoss * weightUpper) *
            selected.family.enncard := by
        ring
  have filterCard :
      ∀ (coordinate : Fin coordinateCount)
        (vertex :
          Fin (coverData coordinate).scaleData.coarse.card),
        (selectedIndices.filter fun source =>
          parent coordinate source = vertex).card =
        ((Finset.univ :
          Finset (Fin selected.family.card)).filter fun source =>
            (coverData coordinate).scaleData.cover.parent
              (selected.embedding source) = vertex).card := by
    intro coordinate vertex
    let left :=
      selectedIndices.filter fun source =>
        parent coordinate source = vertex
    let right :=
      (Finset.univ :
        Finset (Fin selectedPre.family.card)).filter fun source =>
          parent coordinate (selectedPre.embedding source) =
            vertex
    have imageEq :
        Finset.image selectedPre.embedding right = left := by
      ext source
      simp only [left, right, Finset.mem_image,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨index, hparent, rfl⟩
        exact ⟨embeddingMem index, hparent⟩
      · rintro ⟨hsource, hparent⟩
        rcases embeddingSurjective source hsource with
          ⟨index, hindex⟩
        refine ⟨index, ?_, hindex⟩
        rwa [hindex]
    have cardEq :
        (Finset.image selectedPre.embedding right).card =
          right.card :=
      Finset.card_image_of_injective
        right selectedPre.embedding.injective
    change left.card = right.card
    rw [← imageEq, cardEq]
  have degreeUniform :
      ∀ coordinate : Fin coordinateCount,
        ∀ first second :
            Fin (coverData coordinate).scaleData.coarse.card,
          0 <
              ((Finset.univ :
                Finset (Fin selected.family.card)).filter fun source =>
                  (coverData coordinate).scaleData.cover.parent
                      (selected.embedding source) =
                    first).card →
          0 <
              ((Finset.univ :
                Finset (Fin selected.family.card)).filter fun source =>
                  (coverData coordinate).scaleData.cover.parent
                      (selected.embedding source) =
                    second).card →
          (((Finset.univ :
            Finset (Fin selected.family.card)).filter fun source =>
              (coverData coordinate).scaleData.cover.parent
                  (selected.embedding source) =
                first).card : ENNReal) ≤
            degreeConstant *
              (((Finset.univ :
                Finset (Fin selected.family.card)).filter fun source =>
                  (coverData coordinate).scaleData.cover.parent
                      (selected.embedding source) =
                    second).card : ENNReal) := by
    intro coordinate first second hfirst hsecond
    have hfirst' :
        0 <
          (selectedIndices.filter fun source =>
            parent coordinate source = first).card := by
      rw [filterCard coordinate first]
      exact hfirst
    have hsecond' :
        0 <
          (selectedIndices.filter fun source =>
            parent coordinate source = second).card := by
      rw [filterCard coordinate second]
      exact hsecond
    have main :=
      regularized.degree_uniform
        coordinate first second hfirst' hsecond'
    have cardFin :
        Fintype.card (Fin preSelected.family.card) =
          preSelected.family.card := by
      simp
    simpa [selectedIndices, degreeConstant,
      pureWZ2SpatialCellDegreeConstant, coordinateCount,
      cardFin, filterCard coordinate first,
      filterCard coordinate second] using main
  let R : ENNReal :=
    ENNReal.ofReal (Real.rpow delta (-epsilon))
  have RPos : 0 < R :=
    ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos delta_pos _)
  have RTop : R ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have ROne : 1 ≤ R := by
    have h :
        (1 : ℝ) < Real.rpow delta (-epsilon) :=
      Real.one_lt_rpow_of_pos_of_lt_one_of_neg
        delta_pos delta_lt_one (by linarith)
    simpa [R] using ENNReal.ofReal_le_ofReal h.le
  have rounding :
      ∀ requested : WZ2PaperRequestedScale delta,
        ∃ coordinate : Fin coordinateCount,
          requested.1 ≤ (scales coordinate).1 ∧
          ENNReal.ofReal (scales coordinate).1 <
            R * ENNReal.ofReal requested.1 :=
    geometricRequestedScale_rounding
      delta_pos delta_lt_one epsilon_pos
      (rfl :
        coordinateCount = geometricScaleCount epsilon)
  let retentionConstant :=
    regularizationLoss * weightUpper
  have retentionTop : retentionConstant ≠ ⊤ :=
    ENNReal.mul_ne_top regularizationTop weightUpper_ne_top
  have selectedCWA :
      WZ2PaperPureCWAAtNearbyScales
        selected.family outputConstant :=
    pure_cwa_restrict_with_rounding
      ambient selected selectedNonempty
      coordinateCount coordinateCountPos scales
      degreeConstant retentionConstant
      normalizationWeight
      normalizationWeight_ne_zero normalizationWeight_ne_top
      retentionTop degreeTop
      cardinalityRetention degreeUniform
      RPos RTop ROne rounding
      rounding_absorption output_ne_top
      (by
        simpa [degreeConstant, regularizationLoss,
          retentionConstant] using restriction_absorption)
  exact
    ⟨selectedPre, selectedNonempty, ⟨selectedIndices, rfl⟩,
      retainedWeight, selectedWeightFloor, selectedCWA⟩

/--
Recover a spatial-cell certificate from a genuine local preselection.

The two absorption hypotheses are scalar:

* `regularization_mass_absorption` pays the weighted dyadic loss from the
  gap between `cellLoss` and `inputLoss`;
* `restriction_absorption` pays the explicit nearby-CWA restriction
  constant.

Both are uniform in the finite constants returned by the weighted
regularizer.  The geometric hypotheses not already present in the
source/pruning interfaces are precisely the fields of the preselection data:
fixed-radius base/support localization, `source_mass_retention`, and the
local version of the pruning's pointwise tube-density lower bound.
-/
theorem pureWZ2_spatialCellSelectionCertificate_of_preselection
    {sigma sourceLoss inputLoss pruningLoss cellLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss)
    (data :
      PureWZ2SpatialCellPreselectionData
        (cellLoss := cellLoss)
        source pruning)
    (sourceLoss_lt_inputLoss : sourceLoss < inputLoss)
    (pruningLoss_le_inputLoss : pruningLoss ≤ inputLoss)
    (delta_lt_one : delta < 1)
    (regularization_mass_absorption :
      pureWZ2SpatialCellRegularizationLoss
            (inputLoss - sourceLoss)
            data.preSelected.family.card *
          Kakeya.realRpowENN delta
            (inputLoss - cellLoss) ≤
        1)
    (restriction_absorption :
      wz2PaperPureNearbyRestrictionConstant
          (Kakeya.realRpowENN delta (-sourceLoss))
          (pureWZ2SpatialCellNormalizationWeight
            delta sourceLoss cellLoss)
          (pureWZ2SpatialCellDegreeConstant
            (inputLoss - sourceLoss)
            data.preSelected.family.card)
          (pureWZ2SpatialCellRegularizationLoss
              (inputLoss - sourceLoss)
              data.preSelected.family.card *
            Kakeya.deltaTubeVolume delta) ≤
        Kakeya.realRpowENN delta (-inputLoss)) :
    Nonempty
      (PureWZ2SpatialCellSelectionFromPreselectionData
        (inputLoss := inputLoss) data) := by
  let density := Kakeya.realRpowENN delta pruningLoss
  let sourceDensity := Kakeya.realRpowENN delta sourceLoss
  let inputDensity := Kakeya.realRpowENN delta inputLoss
  let cellDensity := Kakeya.realRpowENN delta cellLoss
  let gapDensity :=
    Kakeya.realRpowENN delta (inputLoss - cellLoss)
  let tubeVolume := Kakeya.deltaTubeVolume delta
  let normalizationWeight :=
    pureWZ2SpatialCellNormalizationWeight
      delta sourceLoss cellLoss
  let externalWeight :
      Fin data.preSelected.family.card → ENNReal :=
    fun index => volume (data.localShading.carrier index)
  have sourceDensity_pos : 0 < sourceDensity := by
    dsimp only [sourceDensity, Kakeya.realRpowENN]
    exact ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos source.extremal.delta_pos _)
  have sourceDensity_ne_zero : sourceDensity ≠ 0 :=
    sourceDensity_pos.ne'
  have sourceDensity_ne_top : sourceDensity ≠ ⊤ := by
    dsimp only [sourceDensity, Kakeya.realRpowENN]
    exact ENNReal.ofReal_ne_top
  have cellDensity_pos : 0 < cellDensity := by
    dsimp only [cellDensity, Kakeya.realRpowENN]
    exact ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos source.extremal.delta_pos _)
  have cellDensity_ne_zero : cellDensity ≠ 0 :=
    cellDensity_pos.ne'
  have cellDensity_ne_top : cellDensity ≠ ⊤ := by
    dsimp only [cellDensity, Kakeya.realRpowENN]
    exact ENNReal.ofReal_ne_top
  have tubeVolume_pos : 0 < tubeVolume := by
    exact
      (tube_volume_scaling.2.1 delta
        source.extremal.delta_pos
        source.extremal.delta_le_one).1
  have tubeVolume_ne_zero : tubeVolume ≠ 0 :=
    tubeVolume_pos.ne'
  have tubeVolume_ne_top : tubeVolume ≠ ⊤ := by
    exact
      (tube_volume_scaling.2.1 delta
        source.extremal.delta_pos
        source.extremal.delta_le_one).2
  have normalizationWeight_eq :
      normalizationWeight =
        sourceDensity * cellDensity * tubeVolume := by
    rfl
  have normalizationWeight_ne_zero :
      normalizationWeight ≠ 0 := by
    rw [normalizationWeight_eq]
    exact
      mul_ne_zero
        (mul_ne_zero sourceDensity_ne_zero cellDensity_ne_zero)
        tubeVolume_ne_zero
  have normalizationWeight_ne_top :
      normalizationWeight ≠ ⊤ := by
    rw [normalizationWeight_eq]
    exact
      ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          sourceDensity_ne_top cellDensity_ne_top)
        tubeVolume_ne_top
  have weight_upper :
      ∀ index, externalWeight index ≤ tubeVolume := by
    intro index
    calc
      externalWeight index ≤
          volume (data.preSelected.family.tube index).carrier :=
        measure_mono (data.localShading.subset_body index)
      _ = tubeVolume := by
        exact
          tube_volume_scaling.1 delta
            (data.preSelected.family.tube index)
  have source_density_nominal :
      sourceDensity *
          (source.family.enncard * tubeVolume) ≤
        source.shading.mass := by
    have sourceDense := source.extremal.dense
    rw [Kakeya.Streamlined.Shading.IsLambdaDense] at sourceDense
    rw [tubeFamily_mass_eq_nominal] at sourceDense
    simpa [sourceDensity, tubeVolume,
      Kakeya.Streamlined.TubeFamily.nominalMass] using
      sourceDense
  have total_weight_lower :
      normalizationWeight * source.family.enncard ≤
        ∑ index : Fin data.preSelected.family.card,
          externalWeight index := by
    calc
      normalizationWeight * source.family.enncard =
          cellDensity *
            (sourceDensity *
              (source.family.enncard * tubeVolume)) := by
        rw [normalizationWeight_eq]
        ring
      _ ≤
          cellDensity * source.shading.mass := by
        gcongr
      _ ≤ data.localShading.mass := by
        simpa [cellDensity] using
          data.source_mass_retention
      _ =
          ∑ index : Fin data.preSelected.family.card,
            externalWeight index := rfl
  let epsilon := inputLoss - sourceLoss
  have epsilon_pos : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  have rounding_absorption :
      ENNReal.ofReal (Real.rpow delta (-epsilon)) *
          Kakeya.realRpowENN delta (-sourceLoss) ≤
        Kakeya.realRpowENN delta (-inputLoss) := by
    change
      Kakeya.realRpowENN delta (-epsilon) *
          Kakeya.realRpowENN delta (-sourceLoss) ≤
        Kakeya.realRpowENN delta (-inputLoss)
    rw [Subunit.realRpowENN_mul source.extremal.delta_pos]
    have exponent_eq :
        -epsilon + -sourceLoss = -inputLoss := by
      dsimp only [epsilon]
      ring
    rw [exponent_eq]
  have output_ne_top :
      Kakeya.realRpowENN delta (-inputLoss) ≠ ⊤ := by
    dsimp only [Kakeya.realRpowENN]
    exact ENNReal.ofReal_ne_top
  rcases
      pureWZ2_weighted_restricted_cwa_actual
        source.extremal.cwa_nearby_scales
        data.preSelected data.preSelected_nonempty
        externalWeight normalizationWeight tubeVolume
        normalizationWeight_ne_zero
        normalizationWeight_ne_top tubeVolume_ne_top
        total_weight_lower weight_upper epsilon epsilon_pos
        source.extremal.delta_pos delta_lt_one output_ne_top
        rounding_absorption restriction_absorption with
    ⟨selectedPre, selectedNonempty, _selectedIndices,
      retained_weight, _selectedWeightFloor, selected_cwa⟩
  let regularizationLoss :=
    pureWZ2SpatialCellRegularizationLoss
      epsilon data.preSelected.family.card
  let finalSelected :=
    WZ2PaperPureTubeSubfamily.comp
      data.preSelected selectedPre
  let finalShading :
      Kakeya.Streamlined.TubeShading finalSelected.family :=
    {
      carrier := fun index =>
        data.localShading.carrier
          (selectedPre.embedding index)
      measurable_carrier := fun index =>
        data.localShading.measurable_carrier
          (selectedPre.embedding index)
      subset_body := fun index => by
        have localSubset :=
          data.localShading.subset_body
            (selectedPre.embedding index)
        change
          data.localShading.carrier
              (selectedPre.embedding index) ⊆
            (selectedPre.family.tube index).carrier
        rw [selectedPre.tube_eq index]
        exact localSubset
    }
  have retained_local_mass :
      data.localShading.mass ≤
        regularizationLoss * finalShading.mass := by
    change
      (∑ index : Fin data.preSelected.family.card,
          volume (data.localShading.carrier index)) ≤
        regularizationLoss *
          ∑ index : Fin selectedPre.family.card,
            volume
              (data.localShading.carrier
                (selectedPre.embedding index))
    simpa [externalWeight] using retained_weight
  have input_density_le :
      inputDensity ≤ density := by
    exact
      pure_wz2_rpowENN_antitone
        source.extremal.delta_pos
        source.extremal.delta_le_one
        pruningLoss_le_inputLoss
  have final_local_dense :
      finalShading.IsLambdaDense inputDensity := by
    rw [Kakeya.Streamlined.Shading.IsLambdaDense]
    rw [tubeFamily_mass_eq_nominal]
    change
      inputDensity *
          (finalSelected.family.enncard * tubeVolume) ≤
        ∑ index : Fin finalSelected.family.card,
          volume (finalShading.carrier index)
    calc
      inputDensity *
            (finalSelected.family.enncard * tubeVolume) =
          ∑ _index : Fin finalSelected.family.card,
            inputDensity * tubeVolume := by
        change
          inputDensity *
              ((finalSelected.family.card : ENNReal) *
                tubeVolume) =
            ∑ _index : Fin finalSelected.family.card,
              inputDensity * tubeVolume
        simp [Finset.sum_const]
        ring
      _ ≤
          ∑ index : Fin finalSelected.family.card,
            volume (finalShading.carrier index) := by
        exact
          Finset.sum_le_sum fun index _ => by
            calc
              inputDensity * tubeVolume ≤
                  density * tubeVolume := by
                gcongr
              _ =
                  density *
                    (data.preSelected.family.tube
                      (selectedPre.embedding index)).volume := by
                rw [tube_volume_scaling.1 delta
                  (data.preSelected.family.tube
                    (selectedPre.embedding index))]
              _ ≤
                  volume
                    (data.localShading.carrier
                      (selectedPre.embedding index)) := by
                simpa [density] using
                  data.per_tube_local_density
                    (selectedPre.embedding index)
  have density_split :
      inputDensity = gapDensity * cellDensity := by
    dsimp only [inputDensity, gapDensity, cellDensity]
    rw [Subunit.realRpowENN_mul source.extremal.delta_pos]
    congr 1
    ring
  have final_source_mass_retention :
      inputDensity * source.shading.mass ≤
        finalShading.mass := by
    calc
      inputDensity * source.shading.mass =
          gapDensity *
            (cellDensity * source.shading.mass) := by
        rw [density_split]
        ring
      _ ≤ gapDensity * data.localShading.mass := by
        gcongr
        simpa [cellDensity] using
          data.source_mass_retention
      _ ≤
          gapDensity *
            (regularizationLoss * finalShading.mass) := by
        gcongr
      _ =
          (regularizationLoss * gapDensity) *
            finalShading.mass := by
        ring
      _ ≤ 1 * finalShading.mass := by
        gcongr
      _ = finalShading.mass := by simp
  have finalSelected_nonempty :
      finalSelected.family.Nonempty := by
    change selectedPre.family.Nonempty
    exact selectedNonempty
  have finalSelected_cwa :
      WZ2PaperPureCWAAtNearbyScales
        finalSelected.family
        (Kakeya.realRpowENN delta (-inputLoss)) := by
    simpa [finalSelected] using selected_cwa
  let certificate :
      PureWZ2SpatialCellSelectionCertificate
        (inputLoss := inputLoss) source pruning :=
    {
      selected := finalSelected
      selected_nonempty := finalSelected_nonempty
      selected_from_pruning := by
        intro index
        exact
          data.selected_from_pruning
            (selectedPre.embedding index)
      localShading := finalShading
      subshading := by
        intro index
        exact
          data.subshading
            (selectedPre.embedding index)
      source_mass_retention := by
        simpa [inputDensity] using
          final_source_mass_retention
      center := data.center
      family_bases_local := by
        intro index
        change
          dist (selectedPre.family.tube index).base
              data.center ≤ 3
        rw [selectedPre.tube_eq index]
        exact data.family_bases_local
          (selectedPre.embedding index)
      shading_support_local := by
        rintro point ⟨index, pointMem⟩
        exact
          data.shading_support_local
            ⟨selectedPre.embedding index, pointMem⟩
      local_dense := by
        simpa [inputDensity] using final_local_dense
      per_tube_density := by
        intro index
        have raw :=
          data.per_tube_local_density
            (selectedPre.embedding index)
        change
          inputDensity *
              volume (finalSelected.family.tube index).carrier ≤
            volume (finalShading.carrier index)
        calc
          inputDensity *
                volume (finalSelected.family.tube index).carrier ≤
              density *
                volume (finalSelected.family.tube index).carrier := by
            gcongr
          _ =
              density *
                volume
                  (data.preSelected.family.tube
                    (selectedPre.embedding index)).carrier := by
            rw [show
              finalSelected.family.tube index =
                data.preSelected.family.tube
                  (selectedPre.embedding index) from
              selectedPre.tube_eq index]
          _ ≤
              volume
                (data.localShading.carrier
                  (selectedPre.embedding index)) := by
            simpa [density, Kakeya.DeltaTube.volume] using raw
      restored_cwa := finalSelected_cwa
    }
  exact
    ⟨{
      certificate := certificate
      preselectionIndex := selectedPre.embedding
      source_index_eq := by
        intro index
        rfl
      localShading_subset_preselection := by
        intro index
        rfl
    }⟩

/--
The exact conditional replacement for the unresolved unconditional leaf.

Compared with `PureWZ2SpatialCellSelectionAndCWALeaf`, this proposition has
no CWA conclusion in its geometric data.  It asks only for the fixed-cell
preselection described above and for the two scalar absorptions needed by the
closed weighted restriction theorem.
-/
def PureWZ2SpatialCellPreselectionAndAbsorptionLeaf : Prop :=
  ∀ sigma inputLoss : ℝ,
    0 < inputLoss →
      ∃ sourceLoss pruningLoss cellLoss delta₀ : ℝ,
        0 < sourceLoss ∧
        sourceLoss < pruningLoss ∧
        pruningLoss ≤ inputLoss ∧
        0 < cellLoss ∧
        cellLoss < inputLoss ∧
        0 < delta₀ ∧
        delta₀ < 1 ∧
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₀ →
          ∀ source :
              PureWZ2ExtremalConfiguration
                sigma sourceLoss delta,
            ∀ pruning :
                PureWZ2PerTubeDensityPruningData
                  source pruningLoss,
              ∃ data :
                  PureWZ2SpatialCellPreselectionData
                    (cellLoss := cellLoss) source pruning,
                pureWZ2SpatialCellRegularizationLoss
                      (inputLoss - sourceLoss)
                      data.preSelected.family.card *
                    Kakeya.realRpowENN delta
                      (inputLoss - cellLoss) ≤
                  1 ∧
                wz2PaperPureNearbyRestrictionConstant
                    (Kakeya.realRpowENN delta (-sourceLoss))
                    (pureWZ2SpatialCellNormalizationWeight
                      delta sourceLoss cellLoss)
                    (pureWZ2SpatialCellDegreeConstant
                      (inputLoss - sourceLoss)
                      data.preSelected.family.card)
                    (pureWZ2SpatialCellRegularizationLoss
                        (inputLoss - sourceLoss)
                        data.preSelected.family.card *
                      Kakeya.deltaTubeVolume delta) ≤
                  Kakeya.realRpowENN delta (-inputLoss)

/--
The fixed-cell preselection plus weighted scalar absorptions closes the
original spatial-cell/CWA leaf.
-/
theorem pureWZ2_spatialCellSelectionAndCWALeaf_of_preselection
    (preselection :
      PureWZ2SpatialCellPreselectionAndAbsorptionLeaf) :
    PureWZ2SpatialCellSelectionAndCWALeaf := by
  intro sigma inputLoss inputLossPos
  rcases
      preselection sigma inputLoss inputLossPos with
    ⟨sourceLoss, pruningLoss, cellLoss, delta₀,
      sourceLossPos, sourceLossLtPruning,
      pruningLossLeInput, cellLossPos, cellLossLtInput,
      delta₀Pos, delta₀LtOne, produce⟩
  refine
    ⟨sourceLoss, pruningLoss, delta₀,
      sourceLossPos, sourceLossLtPruning,
      pruningLossLeInput, delta₀Pos, delta₀LtOne.le, ?_⟩
  intro delta deltaPos deltaLe source pruning
  rcases produce delta deltaPos deltaLe source pruning with
    ⟨data, massAbsorption, cwaAbsorption⟩
  rcases
      pureWZ2_spatialCellSelectionCertificate_of_preselection
        source pruning data
        (sourceLossLtPruning.trans_le pruningLossLeInput)
        pruningLossLeInput
        (deltaLe.trans_lt delta₀LtOne)
        massAbsorption cwaAbsorption
    with
    ⟨result⟩
  exact ⟨result.certificate⟩

end Kakeya.Assouad

end
