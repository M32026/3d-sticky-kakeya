import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalWindowHeightPopularity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.StickyMultiplicity

/-!
# Original-family carrier for a source-volume-popular terminal window

The terminal graph window is indexed by the auxiliary active-cell family.
After source-volume height popularity, the paper argument must return to the
original tube family without adding back points at discarded heights. This
module performs exactly that change of indexing: every zero-extended source
carrier is restricted to the union of the popular graph window.

The resulting paper shading has exactly the graph-window union. It need not
be cubical, and no such property is asserted. Its equal-union partial-cell
shadow is the ordinary carrier used by later carrier-independent arguments.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The source-volume-popular graph carrier, reindexed on the original paper
tube family without changing its shaded union. -/
structure PureWZ2TerminalPopularSourceCarrierData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    (data : PureWZ2TerminalWindowHeightPopularData window) where
  zeroExtension : WZ2PaperSubfamilyZeroExtensionData
    terminal.sticky.selected terminal.sticky.refined
  shading : WZ1PaperTubeShading source.family
  carrier_eq : ∀ index, shading.carrier index =
    zeroExtension.ambientShading.carrier index ∩ data.graphWindow.shading.union
  subshading : PureWZ2PaperIsSubshading shading source.shading
  union_eq : shading.union = data.graphWindow.shading.union
  volume_eq : volume shading.union = volume data.graphWindow.shading.union
  height_region : shading.union ⊆ data.popular.heightRegion
  constant_multiplicity : shading.HasConstantMultiplicity
    terminalSource.multiplicity (2 * terminalSource.multiplicity)
  source_volume_retention :
    volume window.shading.union ≤
      (2 * data.popular.bins : ℕ) * volume shading.union
  partialShadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily shading source.extremal.delta_pos) :=
      pureWZ2PartialActiveCellShading shading source.extremal.delta_pos
  partialShadow_eq : partialShadow =
    pureWZ2PartialActiveCellShading shading source.extremal.delta_pos
  partialShadow_union : partialShadow.union = shading.union

/-- Reindex the popular graph window on the original source family. The
construction is a common spatial restriction of the zero extension, so point
multiplicity is unchanged on the retained union. -/
theorem PureWZ2TerminalWindowHeightPopularData.toSourceCarrier
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    (data : PureWZ2TerminalWindowHeightPopularData window) :
    Nonempty (PureWZ2TerminalPopularSourceCarrierData data) := by
  rcases wz2_paper_subfamily_zero_extension
      terminal.sticky.selected terminal.sticky.refined with
    ⟨zeroExtension⟩
  let shading : WZ1PaperTubeShading source.family :=
    { carrier := fun index =>
        zeroExtension.ambientShading.carrier index ∩
          data.graphWindow.shading.union
      measurable_carrier := fun index =>
        (zeroExtension.ambientShading.measurable_carrier index).inter
          (measurableSet_shading_union data.graphWindow.shading)
      subset_body := fun index => Set.inter_subset_left.trans
        (zeroExtension.ambientShading.subset_body index) }
  have hgraphAmbient : data.graphWindow.shading.union ⊆
      zeroExtension.ambientShading.union := by
    intro point hpoint
    have hprepared : point ∈ prepared.shadow.union :=
      data.graphWindow.subshading.union_subset hpoint
    have hterminal : point ∈ terminalSource.shading.union := by
      rwa [prepared.shadow_union] at hprepared
    have hrefined : point ∈ terminal.sticky.refined.union := by
      rwa [terminalSource.shading_eq] at hterminal
    rwa [zeroExtension.union_eq]
  have hunion : shading.union = data.graphWindow.shading.union := by
    apply Set.Subset.antisymm
    · rintro point ⟨index, _hsource, hgraph⟩
      exact hgraph
    · intro point hgraph
      rcases hgraphAmbient hgraph with ⟨index, hsource⟩
      exact ⟨index, hsource, hgraph⟩
  have hsub : PureWZ2PaperIsSubshading shading source.shading := by
    intro index point hpoint
    rcases zeroExtension.carrier_support index point hpoint.1 with
      ⟨selectedIndex, heq, hselected⟩
    subst index
    exact terminal.sticky.subshading selectedIndex hselected
  have hambientMultiplicity :
      zeroExtension.ambientShading.HasConstantMultiplicity
        terminalSource.multiplicity (2 * terminalSource.multiplicity) :=
    zeroExtension.constantMultiplicity (by
      rw [← terminalSource.shading_eq]
      exact terminalSource.constant_multiplicity)
  have hconstant : shading.HasConstantMultiplicity
      terminalSource.multiplicity (2 * terminalSource.multiplicity) := by
    intro point hpoint
    have hmultiplicity : shading.pointMultiplicity point =
        zeroExtension.ambientShading.pointMultiplicity point := by
      unfold Kakeya.Streamlined.Shading.pointMultiplicity
      congr 1
      ext index
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.1
      · intro hambient
        exact ⟨hambient, by rw [← hunion]; exact hpoint⟩
    rw [hmultiplicity]
    have hgraph : point ∈ data.graphWindow.shading.union := by
      rw [← hunion]
      exact hpoint
    exact hambientMultiplicity point (hgraphAmbient hgraph)
  have hheightRegion : shading.union ⊆ data.popular.heightRegion := by
    intro point hpoint
    have hgraph : point ∈ data.graphWindow.shading.union := by
      rw [← hunion]
      exact hpoint
    have hpopular : point ∈ data.popular.shading.union := by
      rw [← data.graphWindow_shading]
      exact hgraph
    rw [data.popular.union_eq] at hpopular
    exact hpopular.2
  have hretention : volume window.shading.union ≤
      (2 * data.popular.bins : ℕ) * volume shading.union := by
    calc
      volume window.shading.union ≤
          (2 * data.popular.bins : ℕ) * data.graphWindow.volumeSupply :=
        data.source_volume_retention
      _ = (2 * data.popular.bins : ℕ) *
          volume data.popular.shading.union := by
        rw [data.graphWindow_supply]
      _ = (2 * data.popular.bins : ℕ) *
          volume data.graphWindow.shading.union := by
        rw [data.graphWindow_shading]
      _ = (2 * data.popular.bins : ℕ) * volume shading.union := by
        rw [← hunion]
  let partialShadow :=
    pureWZ2PartialActiveCellShading shading source.extremal.delta_pos
  exact ⟨{
    zeroExtension := zeroExtension
    shading := shading
    carrier_eq := fun _ => rfl
    subshading := hsub
    union_eq := hunion
    volume_eq := congrArg volume hunion
    height_region := hheightRegion
    constant_multiplicity := hconstant
    source_volume_retention := hretention
    partialShadow := partialShadow
    partialShadow_eq := rfl
    partialShadow_union := by
      exact pureWZ2PartialActiveCellShading_union
        shading source.extremal.delta_pos
  }⟩

end Kakeya.Assouad

end
