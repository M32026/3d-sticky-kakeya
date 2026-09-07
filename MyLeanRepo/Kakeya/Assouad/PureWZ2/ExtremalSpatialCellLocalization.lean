import MyLeanRepo.Kakeya.Assouad.PureWZ2.Critical
import MyLeanRepo.Kakeya.Assouad.PureWZ2.IndexedPerTubePruning
import MyLeanRepo.Kakeya.Assouad.PureWZ2.WeightedDegreeUniformRestrictedCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CompleteParentScheduleRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers
import MyLeanRepo.Kakeya.Assouad.Hairbrush.HomogeneousTwoEndsHelpers

/-!
# Same-scale spatial localization of pure WZ2 extremizers

The public pure extremal configuration has no support-ball hypothesis.
Consequently a fixed spatial cell cannot retain a source-uniform fraction of
an arbitrary translated or spatially separated source without an additional
localization estimate.

This module closes the parts of the proposed localization route that follow
from the current interfaces:

* aggregate density gives a nonempty per-tube dense pruning;
* a cell-selected local shading is still a source subshading;
* its union-volume upper bound follows from source containment;
* nearby-scale pure CWA and density at the weaker loss assemble a new
  extremal configuration at exactly the same `delta`; and
* the small-scale threshold is chosen before the source configuration.

The remaining conditional leaf is deliberately thin.  It asks for one
fixed-radius cell selection retaining the stated source mass, its local
density estimate, and recovered `WZ2PaperPureCWAAtNearbyScales` on the same
selected family.  The last field is the exact output to be supplied by
`weighted_degree_uniform_restricted_cwa` or
`complete_parent_schedule_regularization` after proving the corresponding
absorption bounds.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
The closed aggregate-to-per-tube pruning output for one source extremizer.

The selected indices retain half the shaded mass, a power fraction of the
indexed family, and a pointwise density lower bound on every retained source
tube.
-/
structure PureWZ2PerTubeDensityPruningData
    {sigma sourceLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (pruningLoss : ℝ) where
  indices : Finset (Fin source.family.card)
  nonempty : indices.Nonempty
  cardinality_retention :
    Kakeya.realRpowENN delta pruningLoss *
        source.family.enncard ≤
      (selectedTubeFamily source.family indices).enncard
  mass_retention :
    source.shading.mass ≤
      2 * (selectedTubeShading source.shading indices).mass
  per_tube_density :
    ∀ index ∈ indices,
      Kakeya.realRpowENN delta pruningLoss *
          (source.family.tube index).volume ≤
        volume (source.shading.carrier index)

/-- Construct the per-tube pruning data from the source aggregate density. -/
theorem exists_pureWZ2_perTubeDensityPruningData
    {sigma sourceLoss pruningLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (densitySeparation :
      Kakeya.realRpowENN delta pruningLoss ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta sourceLoss) :
    Nonempty
      (PureWZ2PerTubeDensityPruningData
        source pruningLoss) := by
  rcases
      pure_wz2_indexed_per_tube_pruning
        source.extremal.delta_pos
        source.extremal.delta_le_one
        source.extremal.nonempty
        source.shading
        source.extremal.dense
        densitySeparation with
    ⟨indices, indicesNonempty, cardinalityRetention,
      massRetention, perTubeDensity⟩
  exact
    ⟨{
      indices := indices
      nonempty := indicesNonempty
      cardinality_retention := cardinalityRetention
      mass_retention := massRetention
      per_tube_density := perTubeDensity
    }⟩

/--
The exact residual certificate after the closed per-tube pruning.

The ball radii are absolute and independent of the source.  The center may
depend on the source and is retained so that a later translation can put the
localized configuration in a fixed chart.  `source_mass_retention` is the
missing high-weight-cell estimate.  `local_dense` is the corresponding
integral/density estimate after restricting the shading to that cell.
`restored_cwa` is the multiscale combinatorial output for the very same
selected family.
-/
structure PureWZ2SpatialCellSelectionCertificate
    {sigma sourceLoss inputLoss pruningLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss) where
  selected : WZ2PaperPureTubeSubfamily source.family
  selected_nonempty : selected.family.Nonempty
  selected_from_pruning :
    ∀ index, selected.embedding index ∈ pruning.indices
  localShading :
    Kakeya.Streamlined.TubeShading selected.family
  subshading :
    ∀ index,
      localShading.carrier index ⊆
        source.shading.carrier (selected.embedding index)
  source_mass_retention :
    Kakeya.realRpowENN delta inputLoss *
        source.shading.mass ≤
      localShading.mass
  center : Point3
  family_bases_local :
    ∀ index,
      dist (selected.family.tube index).base center ≤ 3
  shading_support_local :
    localShading.union ⊆ Metric.closedBall center 1
  local_dense :
    localShading.IsLambdaDense
      (Kakeya.realRpowENN delta inputLoss)
  per_tube_density :
    ∀ index,
      Kakeya.realRpowENN delta inputLoss *
          volume (selected.family.tube index).carrier ≤
        volume (localShading.carrier index)
  restored_cwa :
    WZ2PaperPureCWAAtNearbyScales
      selected.family
      (Kakeya.realRpowENN delta (-inputLoss))

namespace PureWZ2SpatialCellSelectionCertificate

variable
    {sigma sourceLoss inputLoss pruningLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss}
    (certificate :
      PureWZ2SpatialCellSelectionCertificate
        (inputLoss := inputLoss) source pruning)

/-- Every selected source tube is one of the per-tube dense pruned tubes. -/
theorem selected_source_per_tube_density
    (index : Fin certificate.selected.family.card) :
    Kakeya.realRpowENN delta pruningLoss *
          (source.family.tube
            (certificate.selected.embedding index)).volume ≤
      volume
        (source.shading.carrier
          (certificate.selected.embedding index)) :=
  pruning.per_tube_density
    (certificate.selected.embedding index)
    (certificate.selected_from_pruning index)

/-- The cell-local shading union is literally contained in the source union. -/
theorem local_union_subset_source :
    certificate.localShading.union ⊆ source.shading.union := by
  rintro point ⟨index, pointMem⟩
  exact
    ⟨certificate.selected.embedding index,
      certificate.subshading index pointMem⟩

/--
The selected tube carriers have a fixed support bound around the cell center.

The radius `5` is absolute: base localization costs `3`, the unit axis costs
`1`, and the tube radius costs at most `1`.
-/
theorem family_support_local
    (index : Fin certificate.selected.family.card) :
    (certificate.selected.family.tube index).carrier ⊆
      Metric.closedBall certificate.center 5 := by
  intro point pointMem
  let tube := certificate.selected.family.tube index
  let midpoint :=
    tube.base + (1 / 2 : ℝ) • tube.direction
  have pointMidpoint :
      dist point midpoint ≤ 1 / 2 + delta := by
    exact
      tube_subset_midpoint_closedBall
        source.extremal.delta_pos tube pointMem
  have midpointBase :
      dist midpoint tube.base = 1 / 2 := by
    rw [dist_eq_norm]
    simp [midpoint, tube, norm_smul, tube.direction_unit]
  have midpointCenter :
      dist midpoint certificate.center ≤ 1 / 2 + 3 := by
    calc
      dist midpoint certificate.center ≤
          dist midpoint tube.base +
            dist tube.base certificate.center :=
        dist_triangle _ _ _
      _ ≤ 1 / 2 + 3 := by
        rw [midpointBase]
        gcongr
        exact certificate.family_bases_local index
  have pointCenter :
      dist point certificate.center ≤ 5 := by
    calc
      dist point certificate.center ≤
          dist point midpoint +
            dist midpoint certificate.center :=
        dist_triangle _ _ _
      _ ≤ (1 / 2 + delta) + (1 / 2 + 3) := by
        gcongr
      _ ≤ 5 := by
        linarith [source.extremal.delta_le_one]
  exact pointCenter

/--
Assemble the same-`delta` localized extremizer.

Only the loss is weakened.  Pure CWA and local density are supplied on the
selected family, while the volume upper bound is inherited from the source
through literal union containment.
-/
noncomputable def toLocalizedExtremal
    (sourceLoss_le_inputLoss : sourceLoss ≤ inputLoss) :
    PureWZ2ExtremalConfiguration sigma inputLoss delta where
  family := certificate.selected.family
  shading := certificate.localShading
  extremal :=
    {
      delta_pos := source.extremal.delta_pos
      delta_le_one := source.extremal.delta_le_one
      nonempty := certificate.selected_nonempty
      cwa_nearby_scales := certificate.restored_cwa
      dense := certificate.local_dense
      volume_upper := by
        calc
          volume certificate.localShading.union ≤
              volume source.shading.union :=
            measure_mono certificate.local_union_subset_source
          _ ≤ Kakeya.realRpowENN delta (sigma - inputLoss) :=
            (source.extremal.mono_loss
              sourceLoss_le_inputLoss).volume_upper
    }

end PureWZ2SpatialCellSelectionCertificate

/--
Provenance and locality retained by the final same-scale extremizer.

The `pruning` field exposes the closed per-tube density output.  The remaining
fields ensure that the final family and shading still come from that same
source and stay in one absolute-radius spatial cell.
-/
structure PureWZ2SameDeltaSpatialCellLocalizationData
    {sigma sourceLoss inputLoss delta : ℝ}
    (source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta) where
  pruningLoss : ℝ
  pruning :
    PureWZ2PerTubeDensityPruningData source pruningLoss
  sourceLoss_le_inputLoss : sourceLoss ≤ inputLoss
  sourceEmbedding :
    Fin localized.family.card ↪ Fin source.family.card
  source_tube_eq :
    ∀ index,
      localized.family.tube index =
        source.family.tube (sourceEmbedding index)
  selected_from_pruning :
    ∀ index, sourceEmbedding index ∈ pruning.indices
  shading_subsource :
    ∀ index,
      localized.shading.carrier index ⊆
        source.shading.carrier (sourceEmbedding index)
  ordinary_per_tube :
    ∀ index,
      (Kakeya.realRpowENN delta inputLoss / 2) *
            volume (localized.family.tube index).carrier ≤
        volume (localized.shading.carrier index)
  source_mass_retention :
    Kakeya.realRpowENN delta inputLoss *
        source.shading.mass ≤
      localized.shading.mass
  center : Point3
  family_bases_local :
    ∀ index,
      dist (localized.family.tube index).base center ≤ 3
  family_support_local :
    ∀ index,
      (localized.family.tube index).carrier ⊆
        Metric.closedBall center 5
  shading_support_local :
    localized.shading.union ⊆ Metric.closedBall center 1

namespace PureWZ2SpatialCellSelectionCertificate

/-- Package a cell certificate as final same-scale localization data. -/
noncomputable def toSameDeltaLocalizationData
    {sigma sourceLoss inputLoss pruningLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss}
    (certificate :
      PureWZ2SpatialCellSelectionCertificate
        (inputLoss := inputLoss) source pruning)
    (sourceLoss_le_inputLoss : sourceLoss ≤ inputLoss) :
    PureWZ2SameDeltaSpatialCellLocalizationData
      source
      (certificate.toLocalizedExtremal
        sourceLoss_le_inputLoss) where
  pruningLoss := pruningLoss
  pruning := pruning
  sourceLoss_le_inputLoss := sourceLoss_le_inputLoss
  sourceEmbedding := certificate.selected.embedding
  source_tube_eq := certificate.selected.tube_eq
  selected_from_pruning := certificate.selected_from_pruning
  shading_subsource := certificate.subshading
  ordinary_per_tube := by
    intro index
    have halfPower :
        Kakeya.realRpowENN delta inputLoss / (2 : ENNReal) ≤
          Kakeya.realRpowENN delta inputLoss := by
      rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
      calc
        Kakeya.realRpowENN delta inputLoss =
            Kakeya.realRpowENN delta inputLoss * 1 := by simp
        _ ≤ Kakeya.realRpowENN delta inputLoss * (2 : ENNReal) :=
          mul_le_mul_left' (by norm_num) _
    calc
      (Kakeya.realRpowENN delta inputLoss / 2) *
            volume
              ((certificate.toLocalizedExtremal
                sourceLoss_le_inputLoss).family.tube index).carrier ≤
          Kakeya.realRpowENN delta inputLoss *
            volume
              ((certificate.toLocalizedExtremal
                sourceLoss_le_inputLoss).family.tube index).carrier := by
        exact mul_le_mul_right' halfPower _
      _ ≤
          volume
            ((certificate.toLocalizedExtremal
              sourceLoss_le_inputLoss).shading.carrier index) :=
        certificate.per_tube_density index
  source_mass_retention := certificate.source_mass_retention
  center := certificate.center
  family_bases_local := certificate.family_bases_local
  family_support_local := certificate.family_support_local
  shading_support_local := certificate.shading_support_local

end PureWZ2SpatialCellSelectionCertificate

/--
The sole conditional leaf left by this module.

All losses and the geometric scale threshold are fixed before `source`.  For every
closed per-tube pruning output, the leaf must choose one fixed-radius spatial
cell, retain the stated source mass in a local shading, prove local density,
and restore pure nearby-scale CWA on the same selected family.

The strict inequality `sourceLoss < pruningLoss` is only scalar bookkeeping.
The producer below absorbs the factor `2` by shrinking the threshold, so this
leaf contains no separate power-absorption premise.
-/
def PureWZ2SpatialCellSelectionAndCWALeaf : Prop :=
  ∀ sigma inputLoss : ℝ,
    0 < inputLoss →
      ∃ sourceLoss pruningLoss delta₀ : ℝ,
        0 < sourceLoss ∧
        sourceLoss < pruningLoss ∧
        pruningLoss ≤ inputLoss ∧
        0 < delta₀ ∧
        delta₀ ≤ 1 ∧
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₀ →
          ∀ source :
              PureWZ2ExtremalConfiguration
                sigma sourceLoss delta,
            ∀ pruning :
                PureWZ2PerTubeDensityPruningData
                  source pruningLoss,
              Nonempty
                (PureWZ2SpatialCellSelectionCertificate
                  (inputLoss := inputLoss) source pruning)

/--
Uniform same-`delta` locality-preserving extremal producer.

The threshold precedes the source quantifier.  The output is a genuine
`PureWZ2ExtremalConfiguration sigma inputLoss delta` with explicit source
embedding, pruning provenance, retained source mass, bounded bases, and
fixed-radius shading support.
-/
def PureWZ2SameDeltaSpatialCellExtremalProducer : Prop :=
  ∀ sigma inputLoss : ℝ,
    0 < inputLoss →
      ∃ sourceLoss delta₀ : ℝ,
        0 < sourceLoss ∧
        sourceLoss ≤ inputLoss ∧
        0 < delta₀ ∧
        delta₀ ≤ 1 ∧
        ∀ delta : ℝ,
          0 < delta →
          delta ≤ delta₀ →
          ∀ source :
              PureWZ2ExtremalConfiguration
                sigma sourceLoss delta,
            ∃ localized :
                PureWZ2ExtremalConfiguration
                  sigma inputLoss delta,
              Nonempty
                (PureWZ2SameDeltaSpatialCellLocalizationData
                  source localized)

/--
The conditional spatial-cell/CWA leaf implies the uniform same-scale
extremal producer.
-/
theorem pureWZ2_sameDeltaSpatialCellExtremalProducer_of_leaf
    (leaf : PureWZ2SpatialCellSelectionAndCWALeaf) :
    PureWZ2SameDeltaSpatialCellExtremalProducer := by
  intro sigma inputLoss inputLossPos
  rcases leaf sigma inputLoss inputLossPos with
    ⟨sourceLoss, pruningLoss, cellDelta₀,
      sourceLossPos, sourceLossLtPruning, pruningLossLe,
      cellDelta₀Pos, cellDelta₀Le, selectCell⟩
  have sourceLossLe : sourceLoss ≤ inputLoss :=
    sourceLossLtPruning.le.trans pruningLossLe
  have pruningGapPos :
      0 < pruningLoss - sourceLoss := by
    linarith
  rcases
      Subunit.exists_delta₀_mul_pow_le_one
        2 (by norm_num)
        (pruningLoss - sourceLoss) pruningGapPos with
    ⟨absorptionDelta₀, absorptionDelta₀Pos,
      absorptionDelta₀Le, absorption⟩
  let delta₀ := min cellDelta₀ absorptionDelta₀
  have delta₀Pos : 0 < delta₀ :=
    lt_min cellDelta₀Pos absorptionDelta₀Pos
  have delta₀Le : delta₀ ≤ 1 :=
    (min_le_left cellDelta₀ absorptionDelta₀).trans
      cellDelta₀Le
  refine
    ⟨sourceLoss, delta₀, sourceLossPos, sourceLossLe,
      delta₀Pos, delta₀Le, ?_⟩
  intro delta deltaPos deltaLe source
  have deltaCell : delta ≤ cellDelta₀ :=
    deltaLe.trans (min_le_left cellDelta₀ absorptionDelta₀)
  have deltaAbsorption : delta ≤ absorptionDelta₀ :=
    deltaLe.trans (min_le_right cellDelta₀ absorptionDelta₀)
  have densitySeparation :
      Kakeya.realRpowENN delta pruningLoss ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta sourceLoss := by
    apply pure_wz2_pruning_power_bound deltaPos
    exact absorption delta deltaPos deltaAbsorption
  rcases
      exists_pureWZ2_perTubeDensityPruningData
        source densitySeparation with
    ⟨pruning⟩
  rcases
      selectCell delta deltaPos deltaCell source pruning with
    ⟨certificate⟩
  let localized :=
    certificate.toLocalizedExtremal sourceLossLe
  exact
    ⟨localized,
      ⟨certificate.toSameDeltaLocalizationData
        sourceLossLe⟩⟩

end Kakeya.Assouad

end
