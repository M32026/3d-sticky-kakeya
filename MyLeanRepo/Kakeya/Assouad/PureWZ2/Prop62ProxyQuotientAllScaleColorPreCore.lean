import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientSourceColor
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ScheduledParentConflictColoring
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientFiberRoute
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.FiniteColoredDegreeSelection
import Mathlib.Tactic

/-!
# Proposition 6.2 quotient pre-core with all-scale parent colors

At every coordinate of a public laminar schedule, color the canonical
representative lines for an arbitrary prescribed conflict scale.  The complete
vector of these colors and the fine source-conflict color form one source-color
type for the existing quotient pre-core adapter.

Thus the existing per-parent source-color pigeonhole makes every final genuine
metric fiber monochromatic at every schedule coordinate without any later
selection or cleanup.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Conflict graph on the canonical representative lines at one schedule level. -/
def pureWZ2Prop62RepresentativeParentScaledConflict
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (conflictScale : Fin schedule.levelCount → ℝ)
    (coordinate : Fin schedule.levelCount)
    (first second : Fin (schedule.scaleData coordinate).coarse.card) : Prop :=
  second ≠ first ∧
    wz1PaperLineDistance
        ((schedule.representativeLineFamily
          fineNonempty coordinate (schedule.actualScale coordinate)).tube second)
        ((schedule.representativeLineFamily
          fineNonempty coordinate (schedule.actualScale coordinate)).tube first) ≤
      conflictScale coordinate

/-- Proper representative-parent colors at arbitrary coordinatewise conflict scales. -/
structure PureWZ2Prop62RepresentativeParentScaledColoringData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (conflictScale : Fin schedule.levelCount → ℝ)
    (conflictDegree : Fin schedule.levelCount → ℕ) where
  color :
    ∀ coordinate,
      Fin (schedule.scaleData coordinate).coarse.card →
        Fin (conflictDegree coordinate + 1)
  proper :
    ∀ coordinate first second,
      first ≠ second →
      wz1PaperLineDistance
          ((schedule.representativeLineFamily
            fineNonempty coordinate (schedule.actualScale coordinate)).tube first)
          ((schedule.representativeLineFamily
            fineNonempty coordinate (schedule.actualScale coordinate)).tube second) ≤
        conflictScale coordinate →
      color coordinate first ≠ color coordinate second

/-- Proper coloring data at one coordinate and one prescribed conflict scale. -/
structure PureWZ2Prop62RepresentativeParentScaledLevelColoringData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (conflictScale : Fin schedule.levelCount → ℝ)
    (conflictDegree : Fin schedule.levelCount → ℕ)
    (coordinate : Fin schedule.levelCount) where
  color :
    Fin (schedule.scaleData coordinate).coarse.card →
      Fin (conflictDegree coordinate + 1)
  proper :
    ∀ first second,
      first ≠ second →
      wz1PaperLineDistance
          ((schedule.representativeLineFamily
            fineNonempty coordinate (schedule.actualScale coordinate)).tube first)
          ((schedule.representativeLineFamily
            fineNonempty coordinate (schedule.actualScale coordinate)).tube second) ≤
        conflictScale coordinate →
      color first ≠ color second

/-- Construct the proper representative-parent coloring at one coordinate. -/
theorem pureWZ2_prop62_representative_parent_scaled_level_coloring
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (conflictScale : Fin schedule.levelCount → ℝ)
    (conflictDegree : Fin schedule.levelCount → ℕ)
    (coordinate : Fin schedule.levelCount)
    (degreeBound :
      ∀ fixed,
        (Finset.univ.filter fun other =>
          pureWZ2Prop62RepresentativeParentScaledConflict
            schedule fineNonempty conflictScale coordinate fixed other).card ≤
          conflictDegree coordinate) :
    Nonempty
      (PureWZ2Prop62RepresentativeParentScaledLevelColoringData
        schedule fineNonempty conflictScale conflictDegree coordinate) := by
  let conflict :=
    pureWZ2Prop62RepresentativeParentScaledConflict
      schedule fineNonempty conflictScale coordinate
  have symmetric :
      ∀ first second,
        conflict first second → conflict second first := by
    intro first second conflictData
    exact
      ⟨conflictData.1.symm, by
        rw [wz1PaperLineDistance_symm]
        exact conflictData.2⟩
  have irreflexive :
      ∀ parent, ¬conflict parent parent := by
    intro parent conflictData
    exact conflictData.1 rfl
  rcases
      pureWZ2_greedy_proper_coloring
        symmetric irreflexive degreeBound
    with ⟨color, proper⟩
  exact
    ⟨{
      color := color
      proper := by
        intro first second distinct distanceClose
        apply proper first second
        exact
          ⟨distinct.symm, by
            rw [wz1PaperLineDistance_symm]
            exact distanceClose⟩
    }⟩

/-- Construct all coordinate colorings from coordinatewise conflict-degree bounds. -/
theorem pureWZ2_prop62_representative_parent_scaled_coloring
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (conflictScale : Fin schedule.levelCount → ℝ)
    (conflictDegree : Fin schedule.levelCount → ℕ)
    (degreeBound :
      ∀ coordinate fixed,
        (Finset.univ.filter fun other =>
          pureWZ2Prop62RepresentativeParentScaledConflict
            schedule fineNonempty conflictScale coordinate fixed other).card ≤
          conflictDegree coordinate) :
    Nonempty
      (PureWZ2Prop62RepresentativeParentScaledColoringData
        schedule fineNonempty conflictScale conflictDegree) := by
  let coordinateColoring :
      ∀ coordinate,
        PureWZ2Prop62RepresentativeParentScaledLevelColoringData
          schedule fineNonempty conflictScale conflictDegree coordinate :=
    fun coordinate =>
      Classical.choice <|
        pureWZ2_prop62_representative_parent_scaled_level_coloring
          schedule fineNonempty conflictScale conflictDegree coordinate
          (degreeBound coordinate)
  exact
    ⟨{
      color := fun coordinate => (coordinateColoring coordinate).color
      proper := by
        intro coordinate first second distinct distanceClose
        exact
          (coordinateColoring coordinate).proper
            first second distinct distanceClose
    }⟩

namespace PureWZ2Prop62RepresentativeParentScaledColoringData

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {conflictScale : Fin schedule.levelCount → ℝ}
    {conflictDegree : Fin schedule.levelCount → ℕ}
    (coloring :
      PureWZ2Prop62RepresentativeParentScaledColoringData
        schedule fineNonempty conflictScale conflictDegree)

/-- Color of the scheduled parent containing one ambient fine leaf. -/
def leafColor
    (coordinate : Fin schedule.levelCount)
    (source : Fin fine.card) :
    Fin (conflictDegree coordinate + 1) :=
  coloring.color coordinate
    ((schedule.scaleData coordinate).cover.parent source)

/-- A monochromatic fine subfamily has separated representative parents. -/
theorem hitRepresentativeLineFamily_stronglySeparated
    (coordinate : Fin schedule.levelCount)
    (targetScale : ℝ)
    (selected : WZ2PaperPureTubeSubfamily fine)
    (selectedColor : Fin (conflictDegree coordinate + 1))
    (monochromatic :
      ∀ source,
        coloring.leafColor coordinate (selected.embedding source) =
          selectedColor) :
    ∀ first second :
        Fin
          (Kakeya.Assouad.PureWZ2Prop62RepresentativeParentColoringData.hitRepresentativeLineFamily
            schedule fineNonempty coordinate targetScale selected).card,
      first ≠ second →
        conflictScale coordinate <
          wz1PaperLineDistance
            ((Kakeya.Assouad.PureWZ2Prop62RepresentativeParentColoringData.hitRepresentativeLineFamily
                schedule fineNonempty coordinate targetScale selected).tube first)
            ((Kakeya.Assouad.PureWZ2Prop62RepresentativeParentColoringData.hitRepresentativeLineFamily
                schedule fineNonempty coordinate targetScale selected).tube second) := by
  intro first second indexNe
  let hit :=
    (schedule.scaleData coordinate).cover.hitParentSubfamily selected
  rcases
      (schedule.scaleData coordinate).cover.hitParent_surjective
        selected first
    with ⟨firstSource, firstOwner⟩
  rcases
      (schedule.scaleData coordinate).cover.hitParent_surjective
        selected second
    with ⟨secondSource, secondOwner⟩
  have ambientNe : hit.embedding first ≠ hit.embedding second :=
    hit.embedding.injective.ne indexNe
  have colorEq :
      coloring.color coordinate (hit.embedding first) =
        coloring.color coordinate (hit.embedding second) := by
    have firstColor := monochromatic firstSource
    have secondColor := monochromatic secondSource
    dsimp only [leafColor] at firstColor secondColor
    rw [←
      (schedule.scaleData coordinate).cover.hitParent_ambient
        selected firstSource, firstOwner] at firstColor
    rw [←
      (schedule.scaleData coordinate).cover.hitParent_ambient
        selected secondSource, secondOwner] at secondColor
    exact firstColor.trans secondColor.symm
  have distanceFar :
      conflictScale coordinate <
        wz1PaperLineDistance
          ((schedule.representativeLineFamily
            fineNonempty coordinate (schedule.actualScale coordinate)).tube
              (hit.embedding first))
          ((schedule.representativeLineFamily
            fineNonempty coordinate (schedule.actualScale coordinate)).tube
              (hit.embedding second)) := by
    by_contra notFar
    exact
      (coloring.proper coordinate
        (hit.embedding first) (hit.embedding second) ambientNe
        (le_of_not_gt notFar)) colorEq
  simpa only [
    Kakeya.Assouad.PureWZ2Prop62RepresentativeParentColoringData.hitRepresentativeLineFamily_tube,
    PureWZ2Prop62LaminarPureSchedule.representativeLineFamily,
    wz2PaperRelabelTube_lineDistance_both] using distanceFar

end PureWZ2Prop62RepresentativeParentScaledColoringData

/-- One color records every scheduled-parent color and the fine source color. -/
abbrev PureWZ2Prop62ProxyQuotientAllScaleSourceColor
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (conflictDegree : Fin schedule.levelCount → ℕ) :=
  (∀ coordinate : Fin schedule.levelCount,
      Fin (conflictDegree coordinate + 1)) ×
    PureWZ2Prop62ProxyQuotientSourceColor

/-- The single combined color assigned to an ambient fine tube. -/
def pureWZ2Prop62ProxyQuotientAllScaleSourceColor
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {conflictScale : Fin schedule.levelCount → ℝ}
    {conflictDegree : Fin schedule.levelCount → ℕ}
    (parentColoring :
      PureWZ2Prop62RepresentativeParentScaledColoringData
        schedule fineNonempty conflictScale conflictDegree)
    (sourceConflict :
      PureWZ2Prop62SourceConflictColoringData fine)
    (source : Fin fine.card) :
    PureWZ2Prop62ProxyQuotientAllScaleSourceColor
      schedule conflictDegree :=
  (fun coordinate => parentColoring.leafColor coordinate source,
    sourceConflict.color source)

/--
The quotient pre-core obtained by using the all-coordinate parent-color vector
and the fine source-conflict color as one `SourceColor`.
-/
structure PureWZ2Prop62ProxyQuotientAllScaleColorPreCoreData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (upperColoring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate)
    (conflictScale : Fin schedule.levelCount → ℝ)
    (conflictDegree : Fin schedule.levelCount → ℕ) where
  parentColoring :
    PureWZ2Prop62RepresentativeParentScaledColoringData
      schedule fineNonempty conflictScale conflictDegree
  sourceConflict :
    PureWZ2Prop62SourceConflictColoringData fine
  adapter :
    PureWZ2Prop62ProxyQuotientPreCoreAdapterData
      schedule fineNonempty quotient width packetCoordinate
      strideBase weight metric upperColoring
      (PureWZ2Prop62ProxyQuotientAllScaleSourceColor
        schedule conflictDegree)
      (pureWZ2Prop62ProxyQuotientAllScaleSourceColor
        parentColoring sourceConflict)

/-- Construct the combined all-scale pre-core through the existing adapter. -/
theorem pureWZ2_prop62_proxy_quotient_allScaleColor_preCore
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (upperColoring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate)
    (conflictScale : Fin schedule.levelCount → ℝ)
    (conflictDegree : Fin schedule.levelCount → ℕ)
    (parentAxisDegree :
      ∀ coordinate fixed,
        (Finset.univ.filter fun other =>
          pureWZ2Prop62RepresentativeParentScaledConflict
            schedule fineNonempty conflictScale coordinate fixed other).card ≤
          conflictDegree coordinate)
    (selectionWeightPos :
      0 < ∑ source ∈ metric.selection.selected, weight source)
    (weightFinite : ∀ source : Fin fine.card, weight source ≠ ⊤)
    (deltaPos : 0 < delta)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2) :
    Nonempty
      (PureWZ2Prop62ProxyQuotientAllScaleColorPreCoreData
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metric upperColoring conflictScale
          conflictDegree) := by
  let parentColoring :=
    Classical.choice <|
      pureWZ2_prop62_representative_parent_scaled_coloring
        schedule fineNonempty conflictScale conflictDegree parentAxisDegree
  let sourceConflict :=
    pureWZ2Prop62ProxyQuotientSourceColoring
      deltaPos fineLine fineBase schedule.fine_distinct
  let sourceColor :=
    pureWZ2Prop62ProxyQuotientAllScaleSourceColor
      parentColoring sourceConflict
  let adapter :=
    Classical.choice <|
      pureWZ2_prop62_proxy_quotient_preCore_adapter
        schedule fineNonempty quotient width packetCoordinate strideBase
        weight metric upperColoring
        (PureWZ2Prop62ProxyQuotientAllScaleSourceColor
          schedule conflictDegree)
        sourceColor selectionWeightPos weightFinite fineLine fineBase
        rhoPos widthPos packetScaleLeRho sixWidthLe
  exact
    ⟨{
      parentColoring := parentColoring
      sourceConflict := sourceConflict
      adapter := adapter
    }⟩

namespace PureWZ2Prop62ProxyQuotientAllScaleColorPreCoreData

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    {metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {upperColoring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    {conflictScale : Fin schedule.levelCount → ℝ}
    {conflictDegree : Fin schedule.levelCount → ℕ}
    (data :
      PureWZ2Prop62ProxyQuotientAllScaleColorPreCoreData
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metric upperColoring conflictScale
          conflictDegree)

/-- The pre-core source loss is exactly the cardinality of the combined color. -/
theorem sourceColorLoss_eq_cardinality :
    data.adapter.preCore.retention.sourceColorLoss =
      (Fintype.card
        (PureWZ2Prop62ProxyQuotientAllScaleSourceColor
          schedule conflictDegree) : ENNReal) :=
  data.adapter.preCore.retention.sourceColorLoss_eq

/-- Exact product formula for the all-scale source-color loss. -/
theorem sourceColorLoss_eq :
    data.adapter.preCore.retention.sourceColorLoss =
      ((∏ coordinate : Fin schedule.levelCount,
          (conflictDegree coordinate + 1 : ℕ)) : ENNReal) *
        ((pureWZ2OrdinaryLineConflictDegree + 1 : ℕ) : ENNReal) := by
  rw [data.sourceColorLoss_eq_cardinality]
  norm_cast
  simp only [PureWZ2Prop62ProxyQuotientAllScaleSourceColor,
    Fintype.card_prod, Fintype.card_pi, Fintype.card_fin]

/-- Uniform degree and schedule-depth bounds control the combined source loss. -/
theorem sourceColorLoss_le_depthBound
    {degreeBound depthBound : ℕ}
    (degreeLe : ∀ coordinate, conflictDegree coordinate ≤ degreeBound)
    (depthLe : schedule.levelCount ≤ depthBound) :
    data.adapter.preCore.retention.sourceColorLoss ≤
      (((degreeBound + 1 : ℕ) : ENNReal) ^ depthBound) *
        ((pureWZ2OrdinaryLineConflictDegree + 1 : ℕ) : ENNReal) := by
  rw [data.sourceColorLoss_eq]
  gcongr
  have productBound :
      (∏ coordinate : Fin schedule.levelCount,
          (conflictDegree coordinate + 1 : ℕ)) ≤
        (degreeBound + 1) ^ schedule.levelCount := by
    calc
      (∏ coordinate : Fin schedule.levelCount,
          (conflictDegree coordinate + 1 : ℕ)) ≤
          ∏ coordinate' : Fin schedule.levelCount,
            (degreeBound + 1) := by
        exact
          Finset.prod_le_prod
            (fun _ _ => Nat.zero_le _)
            (fun coordinate _ => Nat.add_le_add_right
              (degreeLe coordinate) 1)
      _ = (degreeBound + 1) ^ schedule.levelCount := by
        simp
  have powerBound :
      (degreeBound + 1) ^ schedule.levelCount ≤
        (degreeBound + 1) ^ depthBound :=
    Nat.pow_le_pow_right (Nat.zero_lt_succ degreeBound) depthLe
  have powerBoundENN :
      (((degreeBound + 1) ^ schedule.levelCount : ℕ) : ENNReal) ≤
        (((degreeBound + 1) ^ depthBound : ℕ) : ENNReal) := by
    exact_mod_cast powerBound
  calc
    ((∏ coordinate : Fin schedule.levelCount,
        (conflictDegree coordinate + 1 : ℕ)) : ENNReal) ≤
        (((degreeBound + 1 : ℕ) ^ schedule.levelCount : ℕ) : ENNReal) := by
      exact_mod_cast productBound
    _ ≤ (((degreeBound + 1 : ℕ) : ENNReal) ^ depthBound) := by
      simpa only [Nat.cast_pow] using powerBoundENN

/-- The ambient fine subfamily underlying one final genuine metric fiber. -/
def finalMetricFiberAmbientSubfamily
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (parent :
      Fin metricCore.restriction.coarseSelected.family.card) :
    WZ2PaperPureTubeSubfamily fine where
  family := (metricCore.restriction.metricFiberSource parent).family
  embedding :=
    ((metricCore.restriction.metricFiberSource parent).embedding.trans
      metricCore.restriction.fineSelected.embedding).trans
        metricCore.metric.mesh.complete.selectedFine.embedding
  tube_eq := by
    intro source
    exact
      (metricCore.metricFiberAmbientIndex_tube parent source).symm

/-- Every final genuine metric fiber has one common combined source color. -/
theorem finalMetricFiber_monochromatic
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (metric_eq : metricCore.metric = metric)
    (preliminary_eq :
      metricCore.cleanup.preliminary =
        data.adapter.preCore.preliminary)
    (parent :
      Fin metricCore.restriction.coarseSelected.family.card) :
    ∃ selectedColor :
        PureWZ2Prop62ProxyQuotientAllScaleSourceColor
          schedule conflictDegree,
      ∀ source :
          Fin
            (metricCore.restriction.metricFiberSource parent).family.card,
        pureWZ2Prop62ProxyQuotientAllScaleSourceColor
            data.parentColoring data.sourceConflict
            (metricCore.metricFiberAmbientIndex parent source) =
          selectedColor := by
  subst metric
  refine
    ⟨data.adapter.preCore.leafBin.selectedColor
      (metricCore.restriction.coarseSelected.embedding parent), ?_⟩
  intro source
  let fiberSource :=
    (metricCore.restriction.metricFiberSource parent).embedding source
  let selectedSource :=
    metricCore.restriction.fineSelected.embedding fiberSource
  let ambientSource :=
    metricCore.metric.mesh.complete.selectedFine.embedding selectedSource
  have selectedSourcePulledBack :
      selectedSource ∈ metricCore.pulledBack := by
    have sourceImage :
        selectedSource ∈
          Finset.image metricCore.restriction.fineSelected.embedding
            Finset.univ :=
      Finset.mem_image.mpr
        ⟨fiberSource, Finset.mem_univ fiberSource, rfl⟩
    rwa [metricCore.restriction.fine_image_univ] at sourceImage
  have ambientCore :
      ambientSource ∈ metricCore.cleanup.core.core := by
    rw [← metricCore.ambientCore_eq, ← metricCore.image_eq]
    exact Finset.mem_image.mpr
      ⟨selectedSource, selectedSourcePulledBack, rfl⟩
  have ambientPreliminary :
      ambientSource ∈ data.adapter.preCore.preliminary := by
    rw [← preliminary_eq]
    exact metricCore.cleanup.core.core_subset ambientCore
  have ownerEq :
      metricCore.metric.ambientMetricParentOf ambientSource =
        metricCore.restriction.coarseSelected.embedding parent := by
    have sourceFiber :
        fiberSource ∈
          wz2PaperFullFiberIndices
            metricCore.restriction.fineSelected.family
            metricCore.restriction.coarseSelected.family parent :=
      Finset.orderEmbOfFin_mem
        (wz2PaperFullFiberIndices
          metricCore.restriction.fineSelected.family
          metricCore.restriction.coarseSelected.family parent)
        rfl source
    have sourceCovered :
        WZ1PaperTubeCovers
          (metricCore.metric.selectedFine.tube selectedSource)
          (metricCore.metric.metricParents.tube
            (metricCore.restriction.coarseSelected.embedding parent)) := by
      have localCovered :=
        (mem_wz2PaperFullFiberIndices_iff parent fiberSource).mp
          sourceFiber
      simpa only [selectedSource, fiberSource,
        metricCore.restriction.fineSelected.tube_eq,
        metricCore.restriction.coarseSelected.tube_eq] using localCovered
    have canonicalParent :
        metricCore.metric.metricParentOf selectedSource =
          metricCore.restriction.coarseSelected.embedding parent :=
      (metricCore.metric.section6Cover.toWZ1PaperTubeCover
        |>.parent_unique selectedSource
          (metricCore.restriction.coarseSelected.embedding parent)
          sourceCovered).symm
    change
      metricCore.metric.ambientMetricParentOf
          (metricCore.metric.mesh.complete.selectedFine.embedding
            selectedSource) =
        metricCore.restriction.coarseSelected.embedding parent
    rw [metricCore.metric.ambientMetricParentOf_embedding]
    exact canonicalParent
  simpa only [PureWZ2Prop62ProxyQuotientMetricCoreOutput.metricFiberAmbientIndex,
    ambientSource, selectedSource, fiberSource, ownerEq] using
    data.adapter.preCore.source_monochromatic
      ambientSource ambientPreliminary

/-- Coordinatewise projection of final-fiber combined monochromaticity. -/
theorem finalMetricFiber_parentColor_monochromatic
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (metric_eq : metricCore.metric = metric)
    (preliminary_eq :
      metricCore.cleanup.preliminary =
        data.adapter.preCore.preliminary)
    (parent :
      Fin metricCore.restriction.coarseSelected.family.card)
    (coordinate : Fin schedule.levelCount) :
    ∃ selectedColor : Fin (conflictDegree coordinate + 1),
      ∀ source :
          Fin
            (metricCore.restriction.metricFiberSource parent).family.card,
        data.parentColoring.leafColor coordinate
            (metricCore.metricFiberAmbientIndex parent source) =
          selectedColor := by
  rcases
      data.finalMetricFiber_monochromatic
        metricCore metric_eq preliminary_eq parent
    with ⟨selectedColor, monochromatic⟩
  refine ⟨selectedColor.1 coordinate, ?_⟩
  intro source
  exact congrArg (fun color => color.1 coordinate) (monochromatic source)

/-- Projection of final-fiber combined monochromaticity to the fine source color. -/
theorem finalMetricFiber_sourceColor_monochromatic
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (metric_eq : metricCore.metric = metric)
    (preliminary_eq :
      metricCore.cleanup.preliminary =
        data.adapter.preCore.preliminary)
    (parent :
      Fin metricCore.restriction.coarseSelected.family.card) :
    ∃ selectedColor : PureWZ2Prop62ProxyQuotientSourceColor,
      ∀ source :
          Fin
            (metricCore.restriction.metricFiberSource parent).family.card,
        data.sourceConflict.color
            (metricCore.metricFiberAmbientIndex parent source) =
          selectedColor := by
  rcases
      data.finalMetricFiber_monochromatic
        metricCore metric_eq preliminary_eq parent
    with ⟨selectedColor, monochromatic⟩
  refine ⟨selectedColor.2, ?_⟩
  intro source
  exact congrArg Prod.snd (monochromatic source)

/--
The fine-source component of the combined color retains the literal source
separation required by the metric-fiber CWA constructor.
-/
theorem finalMetricFibers_sourceStronglySeparated
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (metric_eq : metricCore.metric = metric)
    (preliminary_eq :
      metricCore.cleanup.preliminary =
        data.adapter.preCore.preliminary) :
    ∀ parent :
        Fin metricCore.restriction.coarseSelected.family.card,
      ∀ first second :
          Fin
            (metricCore.restriction.metricFiberSource parent).family.card,
        first ≠ second →
          wz2PaperLiteralSourceSeparationFactor * delta <
            wz1PaperLineDistance
              ((metricCore.restriction.metricFiberSource parent).family.tube
                first)
              ((metricCore.restriction.metricFiberSource parent).family.tube
                second) := by
  intro parent
  rcases
      data.finalMetricFiber_sourceColor_monochromatic
        metricCore metric_eq preliminary_eq parent
    with ⟨selectedColor, monochromatic⟩
  intro first second indexNe
  let firstAmbient := metricCore.metricFiberAmbientIndex parent first
  let secondAmbient := metricCore.metricFiberAmbientIndex parent second
  have ambientNe : firstAmbient ≠ secondAmbient := by
    exact
      metricCore.metric.mesh.complete.selectedFine.embedding.injective.ne <|
        metricCore.restriction.fineSelected.embedding.injective.ne <|
          (metricCore.restriction.metricFiberSource parent).embedding.injective.ne
            indexNe
  have colorEq :
      data.sourceConflict.color firstAmbient =
        data.sourceConflict.color secondAmbient :=
    (monochromatic first).trans (monochromatic second).symm
  by_contra notSeparated
  have distanceClose :
      wz1PaperLineDistance
          (fine.tube firstAmbient) (fine.tube secondAmbient) ≤
        wz2PaperLiteralSourceSeparationFactor * delta := by
    simpa only [firstAmbient, secondAmbient,
      metricCore.metricFiberAmbientIndex_tube] using
        le_of_not_gt notSeparated
  exact
    (data.sourceConflict.proper
      firstAmbient secondAmbient ambientNe distanceClose) colorEq

/--
At every coordinate, the representative parents hit by the same final genuine
metric fiber are separated at the prescribed conflict scale.
-/
theorem finalMetricFiber_hitRepresentativeLineFamily_stronglySeparated
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (metric_eq : metricCore.metric = metric)
    (preliminary_eq :
      metricCore.cleanup.preliminary =
        data.adapter.preCore.preliminary)
    (parent :
      Fin metricCore.restriction.coarseSelected.family.card)
    (coordinate : Fin schedule.levelCount)
    (targetScale : ℝ) :
    ∀ first second :
        Fin
          (Kakeya.Assouad.PureWZ2Prop62RepresentativeParentColoringData.hitRepresentativeLineFamily
            schedule fineNonempty coordinate targetScale
              (finalMetricFiberAmbientSubfamily metricCore parent)).card,
      first ≠ second →
        conflictScale coordinate <
          wz1PaperLineDistance
            ((Kakeya.Assouad.PureWZ2Prop62RepresentativeParentColoringData.hitRepresentativeLineFamily
                schedule fineNonempty coordinate targetScale
                  (finalMetricFiberAmbientSubfamily
                    metricCore parent)).tube first)
            ((Kakeya.Assouad.PureWZ2Prop62RepresentativeParentColoringData.hitRepresentativeLineFamily
                schedule fineNonempty coordinate targetScale
                  (finalMetricFiberAmbientSubfamily
                    metricCore parent)).tube second) := by
  rcases
      data.finalMetricFiber_parentColor_monochromatic
        metricCore metric_eq preliminary_eq parent coordinate
    with ⟨selectedColor, monochromatic⟩
  apply
    data.parentColoring.hitRepresentativeLineFamily_stronglySeparated
      coordinate targetScale
      (finalMetricFiberAmbientSubfamily metricCore parent)
      selectedColor
  intro source
  change
    data.parentColoring.leafColor coordinate
        (metricCore.metricFiberAmbientIndex parent source) =
      selectedColor
  exact monochromatic source

end PureWZ2Prop62ProxyQuotientAllScaleColorPreCoreData

end Kakeya.Assouad

end
