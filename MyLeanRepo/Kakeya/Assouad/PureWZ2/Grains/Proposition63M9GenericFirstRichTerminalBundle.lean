import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RichStickyKernel
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WeakLipschitzPlaneMapRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63InitialRebalancing

/-!
# Generic terminal plane-map bundle for the first rich call

This module restricts an arbitrary weak plane map on a rich-kernel source
shading to the exact fine shading returned by the same terminal object.  It
retains both pointwise source-shading provenance and the induced union
inclusion, and transfers the source Lipschitz bound to the restricted map.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory

/-- The exact fine-map restriction attached to an arbitrary rich terminal. -/
structure Proposition63M9GenericFirstRichTerminalBundle
    {delta sigma outputLoss sourceLoss normalizationLoss incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {normalizationExponent : ℕ}
    {reentry : PureWZ2PropStickyReentryData (sigma := sigma) sourceShading
      normalizationExponent sourceLoss normalizationLoss}
    {power : Proposition63PowerScale delta sigma}
    (terminal : Proposition63RichTerminalStickyData
      (sigma := sigma) (outputLoss := outputLoss) sourceShading reentry
        power.requested)
    (rootPlaneMap : PaperWZ1WeakPlaneMapData sourceShading incidence)
    (coefficient : NNReal) where
  terminalPlaneMap : PaperWZ1WeakPlaneMapData terminal.data.refined incidence
  terminalPlaneMap_eq_root : terminalPlaneMap.planeMap = rootPlaneMap.planeMap
  terminal_sub_source : ∀ index point,
    point ∈ terminal.data.refined.carrier index →
      point ∈ sourceShading.carrier (terminal.data.selected.embedding index)
  terminal_union_subset_source : terminal.data.refined.union ⊆ sourceShading.union
  terminalPlaneMap_lipschitz : LipschitzWith coefficient
    (fun point : {point : Point3 // point ∈ terminal.data.refined.union} =>
      terminalPlaneMap.planeMap point)

/-- Restrict a root weak plane map along the terminal's selected family and
then along its exact fine subshading. -/
noncomputable def Proposition63M9GenericFirstRichTerminalBundle.ofTerminal
    {delta sigma outputLoss sourceLoss normalizationLoss incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {normalizationExponent : ℕ}
    {reentry : PureWZ2PropStickyReentryData (sigma := sigma) sourceShading
      normalizationExponent sourceLoss normalizationLoss}
    {power : Proposition63PowerScale delta sigma}
    (terminal : Proposition63RichTerminalStickyData
      (sigma := sigma) (outputLoss := outputLoss) sourceShading reentry
        power.requested)
    (rootPlaneMap : PaperWZ1WeakPlaneMapData sourceShading incidence)
    (coefficient : NNReal)
    (rootLipschitz : LipschitzWith coefficient
      (fun point : {point : Point3 // point ∈ sourceShading.union} =>
        rootPlaneMap.planeMap point)) :
    Proposition63M9GenericFirstRichTerminalBundle terminal rootPlaneMap
      coefficient := by
  let selectedPlaneMap : PaperWZ1WeakPlaneMapData
      (restrictPaperShading terminal.data.selected sourceShading) incidence :=
    PaperWZ1WeakPlaneMapData.restrictSubfamily rootPlaneMap terminal.data.selected
  let terminalPlaneMap : PaperWZ1WeakPlaneMapData terminal.data.refined incidence :=
    paperWeakPlaneMapRestrict selectedPlaneMap terminal.data.subshading
  have terminalSubSource : ∀ index point,
      point ∈ terminal.data.refined.carrier index →
        point ∈ sourceShading.carrier (terminal.data.selected.embedding index) := by
    intro index point pointMem
    exact terminal.data.subshading index pointMem
  have terminalUnionSubset : terminal.data.refined.union ⊆ sourceShading.union := by
    rintro point ⟨index, pointMem⟩
    exact ⟨terminal.data.selected.embedding index,
      terminalSubSource index point pointMem⟩
  have terminalLipschitz : LipschitzWith coefficient
      (fun point : {point : Point3 // point ∈ terminal.data.refined.union} =>
        terminalPlaneMap.planeMap point) := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    change dist (rootPlaneMap.planeMap first)
        (rootPlaneMap.planeMap second) ≤ ↑coefficient * dist first second
    exact rootLipschitz.dist_le_mul
      ⟨first, terminalUnionSubset first.prop⟩
      ⟨second, terminalUnionSubset second.prop⟩
  exact {
    terminalPlaneMap := terminalPlaneMap
    terminalPlaneMap_eq_root := rfl
    terminal_sub_source := terminalSubSource
    terminal_union_subset_source := terminalUnionSubset
    terminalPlaneMap_lipschitz := terminalLipschitz
  }

namespace Proposition63M9GenericFirstRichTerminalBundle

variable
    {delta sigma outputLoss sourceLoss normalizationLoss incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {normalizationExponent : ℕ}
    {reentry : PureWZ2PropStickyReentryData (sigma := sigma) sourceShading
      normalizationExponent sourceLoss normalizationLoss}
    {power : Proposition63PowerScale delta sigma}
    {terminal : Proposition63RichTerminalStickyData
      (sigma := sigma) (outputLoss := outputLoss) sourceShading reentry
        power.requested}
    {coefficient : NNReal}
    {rootPlaneMap : PaperWZ1WeakPlaneMapData sourceShading incidence}
    (bundle : Proposition63M9GenericFirstRichTerminalBundle
      terminal rootPlaneMap coefficient)

/-- Restrict arbitrary source local grains first to the terminal's selected
family and then to the exact refined shading stored in the same terminal. -/
noncomputable def restrictLocalGrains
    {C : ENNReal}
    (sourceLocalGrains : Proposition63InitialWeakLocalGrainData
      (incidence := incidence) sourceShading sigma C coefficient) :
    Proposition63InitialWeakLocalGrainData
      (incidence := incidence) terminal.data.refined sigma C coefficient := by
  let _bundle := bundle
  exact (sourceLocalGrains.restrictSubfamily terminal.data.selected).restrict
    terminal.data.subshading

/-- The restricted local-grain map is the original source map evaluated on
the same point with its terminal-to-source provenance. -/
theorem restrictLocalGrains_planeMap_eq
    {C : ENNReal}
    (sourceLocalGrains : Proposition63InitialWeakLocalGrainData
      (incidence := incidence) sourceShading sigma C coefficient)
    (point : {point : Point3 // point ∈ terminal.data.refined.union}) :
    (bundle.restrictLocalGrains sourceLocalGrains).planeMap point =
      sourceLocalGrains.planeMap
        ⟨point, bundle.terminal_union_subset_source point.prop⟩ := by
  rfl

/-- A cellwise source weak map remains cellwise after both terminal
restrictions. -/
theorem terminalPlaneMap_cellwise
    (rootCellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        rootPlaneMap.planeMap first = rootPlaneMap.planeMap second) :
    ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        bundle.terminalPlaneMap.planeMap first =
          bundle.terminalPlaneMap.planeMap second := by
  intro first second sameCell
  simpa only [bundle.terminalPlaneMap_eq_root] using
    rootCellwise first second sameCell

/-- A cellwise arbitrary local-grain map remains cellwise on the exact
terminal refinement. -/
theorem restrictLocalGrains_cellwise
    {C : ENNReal}
    (sourceLocalGrains : Proposition63InitialWeakLocalGrainData
      (incidence := incidence) sourceShading sigma C coefficient)
    (sourceCellwise : ∀
      (first second : {point : Point3 // point ∈ sourceShading.union}),
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        sourceLocalGrains.planeMap first =
          sourceLocalGrains.planeMap second) :
    ∀ (first second :
        {point : Point3 // point ∈ terminal.data.refined.union}),
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        (bundle.restrictLocalGrains sourceLocalGrains).planeMap first =
          (bundle.restrictLocalGrains sourceLocalGrains).planeMap second := by
  intro first second sameCell
  exact sourceCellwise
    ⟨first, bundle.terminal_union_subset_source first.prop⟩
    ⟨second, bundle.terminal_union_subset_source second.prop⟩ sameCell

/-- Identity finite planiness on the exact terminal refinement.  It retains
the terminal object and loses neither incidence nor shaded mass. -/
noncomputable def identityPlaniness
    (rootCellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        rootPlaneMap.planeMap first = rootPlaneMap.planeMap second) :
    BalancedFinitePlaninessData
      (coefficient := (coefficient : ℝ)) terminal.data.refined where
  incidence := incidence
  leftFactor := 1
  rightFactor := 1
  leftFactor_pos := by norm_num
  leftFactor_ne_top := by norm_num
  rightFactor_ne_top := by norm_num
  refinement := {
    shading := terminal.data.refined
    subshading := fun _ => Set.Subset.rfl
    cubical := terminal.data.refined_cubical
    planeMap := bundle.terminalPlaneMap
    planeMap_cellwise := bundle.terminalPlaneMap_cellwise rootCellwise
    lipschitz := by simpa using bundle.terminalPlaneMap_lipschitz
    mass_retention := by simp
  }

/-- Chart-ready initial local data on the exact terminal refinement.  The
planiness map and arbitrary local-grain map remain separate, while sharing
the original incidence and Lipschitz budgets. -/
noncomputable def initialLocalData
    {localLoss : ℝ}
    (sourceLocalGrains : Proposition63InitialWeakLocalGrainData
      (incidence := incidence) sourceShading sigma
        (Kakeya.realRpowENN delta (-localLoss)) coefficient)
    (rootCellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        rootPlaneMap.planeMap first = rootPlaneMap.planeMap second)
    (terminalMassPos : 0 < terminal.data.refined.mass) :
    PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := (coefficient : ℝ)) terminal.data.refined where
  planiness := bundle.identityPlaniness rootCellwise
  planiness_mass_pos := terminalMassPos
  incidence := incidence
  planiness_incidence_le := le_rfl
  incidence_nonnegative :=
    (bundle.identityPlaniness rootCellwise).incidence_nonnegative_of_mass_pos
      terminalMassPos
  localGrains := by
    simpa only [identityPlaniness, Real.toNNReal_coe] using
      bundle.restrictLocalGrains sourceLocalGrains

/-- Identity rebalancing on the same terminal refinement.  The caller only
supplies the genuine fine-scale positivity and the chart's parent-incidence
comparison; no schedule or scalar choice is made here. -/
noncomputable def initialRebalanced
    {localLoss : ℝ}
    (sourceLocalGrains : Proposition63InitialWeakLocalGrainData
      (incidence := incidence) sourceShading sigma
        (Kakeya.realRpowENN delta (-localLoss)) coefficient)
    (rootCellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        rootPlaneMap.planeMap first = rootPlaneMap.planeMap second)
    (terminalMassPos : 0 < terminal.data.refined.mass)
    (hdelta : 0 < delta)
    (hincidence : incidence ≤ power.requested.1 / 2) :
    Proposition63InitialRebalancedData terminal.data.balanced
      (bundle.initialLocalData sourceLocalGrains rootCellwise terminalMassPos)
      hdelta where
  shading := terminal.data.refined
  subshading := fun _ => Set.Subset.rfl
  cubical := terminal.data.refined_cubical
  mass_pos := terminalMassPos
  incidence_le_parent_half := hincidence
  localGrains := by
    simpa only [initialLocalData, identityPlaniness, Real.toNNReal_coe] using
      bundle.restrictLocalGrains sourceLocalGrains

end Proposition63M9GenericFirstRichTerminalBundle

end Kakeya.Assouad.PureWZ2

end
