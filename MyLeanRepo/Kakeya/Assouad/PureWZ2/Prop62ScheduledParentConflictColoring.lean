import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TreePureSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62IndependentPureSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62SourceConflictCore

/-!
# Proposition 6.2 scheduled-parent conflict colors

At every old scheduled scale, each parent has a nonempty strict fiber.  A
bounded fine source in that fiber forces the parent base into a fixed absolute
window.  The ordinary line-conflict packing theorem therefore colors the
scheduled parent family with an absolute number of colors.

The preliminary dependent leaf vector records the color of the parent of each
leaf.  On one monochromatic leaf class, every hit scheduled parent inherits the
same parent color and is consequently strongly separated.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem pureWZ2_prop62_parent_base_le_eight
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperPureScaleCoverData fine scale C)
    (scaleLeOne : scale ≤ 1)
    (fineNonempty : fine.Nonempty)
    (fineBoundedBase : HasBoundedBase fine 4)
    (parent : Fin data.coarse.card) :
    ‖(data.coarse.tube parent).base‖ ≤ 8 := by
  have fiberNonempty :
      (wz2PaperOrdinaryFullFiberIndices
        fine data.coarse parent).Nonempty :=
    data.cover.fullFiber_nonempty_of_uniform
      fineNonempty data.full_fiber_uniform parent
  rcases fiberNonempty with ⟨source, sourceMem⟩
  have containment :
      (fine.tube source).carrier ⊆
        (data.coarse.tube parent).carrier :=
    (mem_wz2PaperOrdinaryFullFiberIndices_iff
      parent source).mp sourceMem
  rcases
      containment_alignment_bound
        data.delta_pos.le data.rho_pos
        (fine.tube source) (data.coarse.tube parent) containment
    with aligned | reversed
  · calc
      ‖(data.coarse.tube parent).base‖ ≤
          ‖(fine.tube source).base‖ +
            ‖(data.coarse.tube parent).base -
              (fine.tube source).base‖ := by
        have triangle :=
          norm_add_le
            ((fine.tube source).base)
            ((data.coarse.tube parent).base -
              (fine.tube source).base)
        simpa [add_sub_cancel_right] using triangle
      _ ≤ 4 + 3 * scale := by
        exact add_le_add
          (fineBoundedBase source)
          (by simpa [norm_sub_rev] using aligned.2)
      _ ≤ 8 := by nlinarith [data.rho_pos]
  · calc
      ‖(data.coarse.tube parent).base‖ ≤
          ‖(fine.tube source).base + (fine.tube source).direction‖ +
            ‖(data.coarse.tube parent).base -
              ((fine.tube source).base + (fine.tube source).direction)‖ := by
        have triangle :=
          norm_add_le
            ((fine.tube source).base + (fine.tube source).direction)
            ((data.coarse.tube parent).base -
              ((fine.tube source).base + (fine.tube source).direction))
        simpa [add_sub_cancel_right] using triangle
      _ ≤ (4 + 1) + 3 * scale := by
        gcongr
        · exact
            (norm_add_le _ _).trans <| by
              rw [(fine.tube source).direction_unit]
              linarith [fineBoundedBase source]
        · simpa [norm_sub_rev] using reversed.2
      _ ≤ 8 := by nlinarith [data.rho_pos]

/--
Conflict colors for the Section 6 axes representing the complete parents of
one literal Lemma 2.13 schedule.

The actual Definition 2.12 parents remain responsible for strict complete
fibers and their John witnesses.  Only the conflict metric is evaluated on
one chosen fine axis from each complete parent.
-/
structure PureWZ2Prop62RepresentativeParentColoringData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty) where
  coloring :
    ∀ coordinate,
      PureWZ2Prop62SourceConflictColoringData
        (schedule.representativeLineFamily
          fineNonempty coordinate
          (schedule.actualScale coordinate))

/--
Build the representative-axis colors from the exact packing estimate needed
at every scheduled actual scale.

This hypothesis is intentionally stated on parent representatives.  Ordinary
essential distinctness of the fine family alone only gives fine-scale
packing and cannot justify this actual-scale bound.
-/
theorem pureWZ2_prop62_representative_parent_coloring
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (parentAxisDegree :
      ∀ coordinate fixed,
        (Finset.univ.filter fun other =>
          other ≠ fixed ∧
            wz1PaperLineDistance
                ((schedule.representativeLineFamily
                  fineNonempty coordinate
                  (schedule.actualScale coordinate)).tube other)
                ((schedule.representativeLineFamily
                  fineNonempty coordinate
                  (schedule.actualScale coordinate)).tube fixed) ≤
              wz2PaperLiteralSourceSeparationFactor *
                schedule.actualScale coordinate).card ≤
          pureWZ2OrdinaryLineConflictDegree) :
    Nonempty
      (PureWZ2Prop62RepresentativeParentColoringData
        schedule fineNonempty) := by
  let coloring :
      ∀ coordinate,
        PureWZ2Prop62SourceConflictColoringData
          (schedule.representativeLineFamily
            fineNonempty coordinate
            (schedule.actualScale coordinate)) :=
    fun coordinate =>
      Classical.choice <| by
        let conflict :
            Fin (schedule.scaleData coordinate).coarse.card →
              Fin (schedule.scaleData coordinate).coarse.card → Prop :=
          fun first second =>
            second ≠ first ∧
              wz1PaperLineDistance
                  ((schedule.representativeLineFamily
                    fineNonempty coordinate
                    (schedule.actualScale coordinate)).tube second)
                  ((schedule.representativeLineFamily
                    fineNonempty coordinate
                    (schedule.actualScale coordinate)).tube first) ≤
                wz2PaperLiteralSourceSeparationFactor *
                  schedule.actualScale coordinate
        have symmetric :
            ∀ first second,
              conflict first second →
                conflict second first := by
          intro first second hconflict
          refine ⟨hconflict.1.symm, ?_⟩
          rw [wz1PaperLineDistance_symm]
          exact hconflict.2
        have irreflexive :
            ∀ parent, ¬conflict parent parent := by
          intro parent hconflict
          exact hconflict.1 rfl
        rcases
            pureWZ2_greedy_proper_coloring
              (D := pureWZ2OrdinaryLineConflictDegree)
              symmetric irreflexive
              (fun fixed => by
                rw [Finset.filter_congr_decidable]
                exact parentAxisDegree coordinate fixed)
          with
          ⟨color, proper⟩
        exact
          ⟨{
            color := color
            proper := by
              intro first second indexNe distanceClose
              exact
                proper first second
                  ⟨indexNe.symm, by
                    rw [wz1PaperLineDistance_symm]
                    exact distanceClose⟩
          }⟩
  exact ⟨{ coloring := coloring }⟩

namespace PureWZ2Prop62RepresentativeParentColoringData

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    (data :
      PureWZ2Prop62RepresentativeParentColoringData
        schedule fineNonempty)

/-- Color a leaf by the representative axis of its literal complete parent. -/
def leafColor
    (coordinate : Fin schedule.levelCount)
    (source : Fin fine.card) :
    Fin (pureWZ2OrdinaryLineConflictDegree + 1) :=
  (data.coloring coordinate).color
    ((schedule.scaleData coordinate).cover.parent source)

/--
The representative-axis family indexed by precisely the actual parents hit
by a selected fine subfamily.
-/
noncomputable def hitRepresentativeLineFamily
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (coordinate : Fin schedule.levelCount)
    (targetScale : ℝ)
    (selected : WZ2PaperPureTubeSubfamily fine) :
    Kakeya.Streamlined.TubeFamily targetScale where
  card :=
    ((schedule.scaleData coordinate).cover
      |>.hitParentSubfamily selected).family.card
  tube parent :=
    (schedule.representativeLineFamily
      fineNonempty coordinate targetScale).tube <|
        ((schedule.scaleData coordinate).cover
          |>.hitParentSubfamily selected).embedding parent

@[simp] theorem hitRepresentativeLineFamily_tube
    (coordinate : Fin schedule.levelCount)
    (targetScale : ℝ)
    (selected : WZ2PaperPureTubeSubfamily fine)
    (parent :
      Fin (hitRepresentativeLineFamily
        schedule fineNonempty coordinate targetScale selected).card) :
    (hitRepresentativeLineFamily
      schedule fineNonempty coordinate targetScale selected).tube parent =
        (schedule.representativeLineFamily
          fineNonempty coordinate targetScale).tube
            (((schedule.scaleData coordinate).cover
              |>.hitParentSubfamily selected).embedding parent) :=
  rfl

theorem hitRepresentativeLineFamily_lineClass
    (fineLineClass : WZ1PaperIsLineClass fine)
    (coordinate : Fin schedule.levelCount)
    (targetScale : ℝ)
    (selected : WZ2PaperPureTubeSubfamily fine) :
    WZ1PaperIsLineClass
      (hitRepresentativeLineFamily
        schedule fineNonempty coordinate targetScale selected) := by
  intro parent
  exact
    schedule.representativeLineFamily_lineClass
      fineNonempty fineLineClass coordinate targetScale
      (((schedule.scaleData coordinate).cover
        |>.hitParentSubfamily selected).embedding parent)

/--
One monochromatic selected leaf class has strongly separated representative
axes for all actual complete parents that it hits.
-/
theorem hitRepresentativeLineFamily_stronglySeparated
    (coordinate : Fin schedule.levelCount)
    (targetScale : ℝ)
    (selected : WZ2PaperPureTubeSubfamily fine)
    (selectedColor : Fin (pureWZ2OrdinaryLineConflictDegree + 1))
    (monochromatic :
      ∀ source,
        data.leafColor coordinate (selected.embedding source) =
          selectedColor) :
    ∀ first second :
        Fin (hitRepresentativeLineFamily
          schedule fineNonempty coordinate targetScale selected).card,
      first ≠ second →
        wz2PaperLiteralSourceSeparationFactor *
              schedule.actualScale coordinate <
          wz1PaperLineDistance
            ((hitRepresentativeLineFamily
              schedule fineNonempty coordinate targetScale selected).tube first)
            ((hitRepresentativeLineFamily
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
      (data.coloring coordinate).color (hit.embedding first) =
        (data.coloring coordinate).color (hit.embedding second) := by
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
      wz2PaperLiteralSourceSeparationFactor *
            schedule.actualScale coordinate <
        wz1PaperLineDistance
          ((schedule.representativeLineFamily
            fineNonempty coordinate
            (schedule.actualScale coordinate)).tube
              (hit.embedding first))
          ((schedule.representativeLineFamily
            fineNonempty coordinate
            (schedule.actualScale coordinate)).tube
              (hit.embedding second)) := by
    by_contra notFar
    exact
      ((data.coloring coordinate).proper
        (hit.embedding first) (hit.embedding second) ambientNe
        (le_of_not_gt notFar)) colorEq
  simpa only [hitRepresentativeLineFamily_tube,
    PureWZ2Prop62LaminarPureSchedule.representativeLineFamily,
    wz2PaperRelabelTube_lineDistance_both] using distanceFar

end PureWZ2Prop62RepresentativeParentColoringData

structure PureWZ2Prop62ScheduledParentColoringData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62PureSchedule fine ambientConstant scaleWindow) where
  coloring :
    ∀ coordinate,
      PureWZ2Prop62SourceConflictColoringData
        (schedule.scaleData coordinate).coarse

theorem pureWZ2_prop62_scheduled_parent_coloring
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62PureSchedule fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (actualScaleLeOne :
      ∀ coordinate, schedule.actualScale coordinate ≤ 1)
    (fineBoundedBase : HasBoundedBase fine 4) :
    Nonempty
      (PureWZ2Prop62ScheduledParentColoringData schedule) := by
  let coloring :
      ∀ coordinate,
        PureWZ2Prop62SourceConflictColoringData
          (schedule.scaleData coordinate).coarse :=
    fun coordinate =>
      Classical.choice <|
        pureWZ2_prop62_source_conflict_coloring
          (schedule.scaleData coordinate).rho_pos
          (schedule.coarse_line_class coordinate)
          (fun parent =>
            pureWZ2_prop62_parent_base_le_eight
              (schedule.scaleData coordinate)
              (actualScaleLeOne coordinate)
              fineNonempty fineBoundedBase parent)
          ((schedule.scaleData coordinate).cover
            |>.coarse_essentiallyDistinct_of_uniform
              (schedule.scaleData coordinate).rho_pos.le
              fineNonempty
              (schedule.scaleData coordinate).full_fiber_uniform)
  exact ⟨{ coloring := coloring }⟩

namespace PureWZ2Prop62ScheduledParentColoringData

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule fine ambientConstant scaleWindow}
    (data : PureWZ2Prop62ScheduledParentColoringData schedule)

def leafColor
    (coordinate : Fin schedule.levelCount)
    (source : Fin fine.card) :
    Fin (pureWZ2OrdinaryLineConflictDegree + 1) :=
  (data.coloring coordinate).color
    ((schedule.scaleData coordinate).cover.parent source)

theorem hitParents_stronglySeparated
    (coordinate : Fin schedule.levelCount)
    (selected : WZ2PaperPureTubeSubfamily fine)
    (selectedColor : Fin (pureWZ2OrdinaryLineConflictDegree + 1))
    (monochromatic :
      ∀ source,
        data.leafColor coordinate (selected.embedding source) =
          selectedColor) :
    ∀ first second :
        Fin ((schedule.scaleData coordinate).cover
          |>.hitParentSubfamily selected).family.card,
      first ≠ second →
        wz2PaperLiteralSourceSeparationFactor *
              schedule.actualScale coordinate <
          wz1PaperLineDistance
            (((schedule.scaleData coordinate).cover
              |>.hitParentSubfamily selected).family.tube first)
            (((schedule.scaleData coordinate).cover
              |>.hitParentSubfamily selected).family.tube second) := by
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
      (data.coloring coordinate).color (hit.embedding first) =
        (data.coloring coordinate).color (hit.embedding second) := by
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
      wz2PaperLiteralSourceSeparationFactor *
            schedule.actualScale coordinate <
        wz1PaperLineDistance
          ((schedule.scaleData coordinate).coarse.tube
            (hit.embedding first))
          ((schedule.scaleData coordinate).coarse.tube
            (hit.embedding second)) := by
    by_contra notFar
    exact
      ((data.coloring coordinate).proper
        (hit.embedding first) (hit.embedding second) ambientNe
        (le_of_not_gt notFar)) colorEq
  simpa only [hit, WZ2PaperPureTubeSubfamily.tube_eq] using distanceFar

end PureWZ2Prop62ScheduledParentColoringData

structure PureWZ2Prop62ScheduledParentCoordinateData
    {delta : ℝ}
    {ambientFine scheduledFine :
      Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62PureSchedule
        scheduledFine ambientConstant scaleWindow)
    (scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule)
    (embedding : Fin scheduledFine.card ↪ Fin ambientFine.card)
    (coordinateCount : ℕ)
    (Color : Fin coordinateCount → Type*)
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    (color : ∀ coordinate, Fin ambientFine.card → Color coordinate) where
  slot : Fin schedule.levelCount → Fin coordinateCount
  decode :
    ∀ scheduleCoordinate,
      Color (slot scheduleCoordinate) →
        Fin (pureWZ2OrdinaryLineConflictDegree + 1)
  decode_color :
    ∀ scheduleCoordinate source,
      decode scheduleCoordinate
          (color (slot scheduleCoordinate) (embedding source)) =
        scheduled.leafColor scheduleCoordinate source

namespace PureWZ2Prop62ScheduledParentCoordinateData

variable
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData fine scale C}
    {ambientConstant scaleWindow : ENNReal}
    {coordinateCount : ℕ}
    {Color : Fin coordinateCount → Type*}
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    {color : ∀ coordinate, Fin fine.card → Color coordinate}
    {weight : Fin fine.card → ENNReal}
    {preliminary :
      PureWZ2Prop62PreliminarySelectionData
        coordinateCount Color color weight}
    {width M : ℝ}
    {metricPreliminary :
      PureWZ2Prop62MetricPreliminaryOutput
        (rho := rho) oldData Color color weight preliminary width M}
    {schedule :
      PureWZ2Prop62PureSchedule
        metricPreliminary.metric.selectedFine
        ambientConstant scaleWindow}
    {scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule}
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled
        metricPreliminary.metric.mesh.complete.selectedFine.embedding
        coordinateCount Color color)

def selectedColor
    (scheduleCoordinate : Fin schedule.levelCount) :
    Fin (pureWZ2OrdinaryLineConflictDegree + 1) :=
  coordinates.decode scheduleCoordinate
    (preliminary.colorVector
      (coordinates.slot scheduleCoordinate))

theorem selectedPreliminary_monochromatic
    (scheduleCoordinate : Fin schedule.levelCount)
    (source : Fin metricPreliminary.metric.selectedFine.card)
    (sourceMem : source ∈ metricPreliminary.selectedPreliminary) :
    scheduled.leafColor scheduleCoordinate source =
      coordinates.selectedColor scheduleCoordinate := by
  rw [← coordinates.decode_color scheduleCoordinate source]
  exact congrArg (coordinates.decode scheduleCoordinate) <|
    metricPreliminary.selectedPreliminary_monochromatic
      source sourceMem (coordinates.slot scheduleCoordinate)

theorem core_monochromatic
    (auxiliary :
      PureWZ2Prop62AuxiliaryLevel
        schedule (Fin metricPreliminary.metric.metricParents.card))
    (scheduleCoordinate : Fin schedule.levelCount)
    (source :
      Fin (auxiliary.coreFine
        metricPreliminary.selectedPreliminary).family.card) :
    scheduled.leafColor scheduleCoordinate
        ((auxiliary.coreFine
          metricPreliminary.selectedPreliminary).embedding source) =
      coordinates.selectedColor scheduleCoordinate := by
  have coreMem :
      (auxiliary.coreFine
        metricPreliminary.selectedPreliminary).embedding source ∈
        auxiliary.coreIndices metricPreliminary.selectedPreliminary :=
    Finset.orderEmbOfFin_mem
      (auxiliary.coreIndices metricPreliminary.selectedPreliminary)
      rfl source
  have preliminaryMem :
      (auxiliary.coreFine
        metricPreliminary.selectedPreliminary).embedding source ∈
        metricPreliminary.selectedPreliminary :=
    (auxiliary.coreOutput metricPreliminary.selectedPreliminary
      |>.core_subset) coreMem
  exact
    coordinates.selectedPreliminary_monochromatic
      scheduleCoordinate
      ((auxiliary.coreFine
        metricPreliminary.selectedPreliminary).embedding source)
      preliminaryMem

theorem core_hitParents_stronglySeparated
    (scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule)
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled
        metricPreliminary.metric.mesh.complete.selectedFine.embedding
        coordinateCount Color color)
    (auxiliary :
      PureWZ2Prop62AuxiliaryLevel
        schedule (Fin metricPreliminary.metric.metricParents.card))
    (scheduleCoordinate : Fin schedule.levelCount) :
    ∀ first second :
        Fin (auxiliary.coreCoarse scheduleCoordinate
          metricPreliminary.selectedPreliminary).family.card,
      first ≠ second →
        wz2PaperLiteralSourceSeparationFactor *
              schedule.actualScale scheduleCoordinate <
          wz1PaperLineDistance
            ((auxiliary.coreCoarse scheduleCoordinate
              metricPreliminary.selectedPreliminary).family.tube first)
            ((auxiliary.coreCoarse scheduleCoordinate
              metricPreliminary.selectedPreliminary).family.tube second) := by
  exact
    PureWZ2Prop62ScheduledParentColoringData.hitParents_stronglySeparated
      scheduled
      scheduleCoordinate
      (auxiliary.coreFine metricPreliminary.selectedPreliminary)
      (coordinates.selectedColor scheduleCoordinate)
      (coordinates.core_monochromatic auxiliary scheduleCoordinate)

end PureWZ2Prop62ScheduledParentCoordinateData

end Kakeya.Assouad

end
