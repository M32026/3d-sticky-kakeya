import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricFiberRescaling
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AuxiliaryPureSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ScheduledParentConflictColoring
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62SourceConflictCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricCoreRescaledPhysicalCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricAuxiliaryFiber
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryNestedLocalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.BoundedOrdinaryRescaledLocality

/-!
# Proposition 6.2 metric fibers: requested descendant routes

This module implements the paper's lower-scale branch after the metric-parent
level has been inserted into the old laminar schedule.  The source family is
always the complete genuine Section 6 metric fiber in the one final tree core.
For an old coordinate strictly below the insertion, that fiber is saturated
for the old strict parent map, so the exact-scale pure witness restricts with
no additional CWA loss.

The public literal-rescaling route still distinguishes the synchronized WZ
line-cover geometry from the ordinary strict carrier cover.  No assigned
fiber is substituted for either relation.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Exact fine-family reindexing does not change the derived strict parent. -/
theorem WZ2PaperPurePartitioningCover.reindex_parent_eq
    {delta rho : ℝ}
    {source target : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover source coarse)
    (rhoNonnegative : 0 ≤ rho)
    (indexEquiv : Fin target.card ≃ Fin source.card)
    (tube_eq :
      ∀ index : Fin target.card,
        target.tube index = source.tube (indexEquiv index))
    (targetIndex : Fin target.card) :
    (cover.reindex indexEquiv tube_eq).parent targetIndex =
      cover.parent (indexEquiv targetIndex) := by
  apply
    (cover.reindex indexEquiv tube_eq).fullFiber_parent_unique
      rhoNonnegative
  · exact
      (cover.reindex indexEquiv tube_eq).parent_mem_fullFiber targetIndex
  · rw [mem_wz2PaperOrdinaryFullFiberIndices_iff, tube_eq]
    exact
      (mem_wz2PaperOrdinaryFullFiberIndices_iff
        (cover.parent (indexEquiv targetIndex))
        (indexEquiv targetIndex)).mp
          (cover.parent_mem_fullFiber (indexEquiv targetIndex))

/-- The derived parent of the pure hit-parent restriction is its hit parent. -/
theorem WZ2PaperPurePartitioningCover.restrictToHitParents_parent_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (rhoNonnegative : 0 ≤ rho)
    (selected : WZ2PaperPureTubeSubfamily fine)
    (source : Fin selected.family.card) :
    (cover.restrictToHitParents selected).parent source =
      cover.hitParent selected source := by
  apply
    (cover.restrictToHitParents selected).fullFiber_parent_unique
      rhoNonnegative
  · exact
      (cover.restrictToHitParents selected).parent_mem_fullFiber source
  · rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    rw [selected.tube_eq,
      (cover.hitParentSubfamily selected).tube_eq,
      cover.hitParent_ambient]
    exact
      (mem_wz2PaperOrdinaryFullFiberIndices_iff
        (cover.parent (selected.embedding source))
        (selected.embedding source)).mp
          (cover.parent_mem_fullFiber (selected.embedding source))

namespace PureWZ2Prop62AuxiliaryLevel

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule fine ambientConstant scaleWindow}
    {Aux : Type}
    [Fintype Aux] [DecidableEq Aux]
    (auxiliary : PureWZ2Prop62AuxiliaryLevel schedule Aux)

/-- The final-core output scale uses the canonical hit-parent map. -/
theorem outputScale_parent_eq_hitParent
    (coordinate : Fin schedule.levelCount)
    {selected : Finset (Fin fine.card)}
    (selectedNonempty : selected.Nonempty)
    (source : Fin (auxiliary.coreFine selected).family.card) :
    (auxiliary.outputScaleData coordinate selectedNonempty).cover.parent
        source =
      (schedule.scaleData coordinate).cover.hitParent
        (auxiliary.coreFine selected) source := by
  change
    (auxiliary.coreCover coordinate selected).parent source =
      (schedule.scaleData coordinate).cover.hitParent
        (auxiliary.coreFine selected) source
  exact
    (schedule.scaleData coordinate).cover
      |>.restrictToHitParents_parent_eq
        (schedule.scaleData coordinate).rho_pos.le
        (auxiliary.coreFine selected) source

end PureWZ2Prop62AuxiliaryLevel

namespace PureWZ2Prop62MetricCoreRestrictionData

variable
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData fine scale C}
    {width M : ℝ}
    {metric :
      PureWZ2Prop62MetricPacketOutput
        (rho := rho) oldData width M}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule
        metric.selectedFine ambientConstant scaleWindow}
    {auxiliary :
      PureWZ2Prop62AuxiliaryLevel
        schedule (Fin metric.metricParents.card)}
    {selected : Finset (Fin metric.selectedFine.card)}
    (restriction :
      PureWZ2Prop62MetricCoreRestrictionData
        metric.section6Cover (auxiliary.coreIndices selected))

/--
Both final-core records enumerate the same ambient `coreIndices`; this is the
exact finite equivalence from the Section 6 restriction to the pure schedule
restriction.
-/
noncomputable def restrictionCoreEquiv :
    Fin restriction.fineSelected.family.card ≃
      {source : Fin metric.selectedFine.card //
        source ∈ auxiliary.coreIndices selected} :=
  Equiv.ofBijective
    (fun source =>
      ⟨restriction.fineSelected.embedding source, by
        have imageMem :
            restriction.fineSelected.embedding source ∈
              Finset.image restriction.fineSelected.embedding
                Finset.univ :=
          Finset.mem_image.mpr
            ⟨source, Finset.mem_univ source, rfl⟩
        simpa only [restriction.fine_image_univ] using imageMem⟩)
    ⟨by
      intro first second equality
      apply restriction.fineSelected.embedding.injective
      exact congrArg Subtype.val equality,
     by
      intro ambientSource
      have imageMem :
          ambientSource.1 ∈
            Finset.image restriction.fineSelected.embedding
              Finset.univ := by
        simpa only [restriction.fine_image_univ] using ambientSource.2
      rcases Finset.mem_image.mp imageMem with
        ⟨source, _, sourceEq⟩
      refine ⟨source, ?_⟩
      apply Subtype.ext
      exact sourceEq⟩

/-- Exact reindexing from the final Section 6 fine family to the pure core. -/
noncomputable def coreIndexEquiv :
    Fin restriction.fineSelected.family.card ≃
      Fin (auxiliary.coreFine selected).family.card :=
  restriction.restrictionCoreEquiv.trans
    (((auxiliary.coreIndices selected).orderIsoOfFin rfl).symm.toEquiv)

theorem coreIndexEquiv_embedding
    (source : Fin restriction.fineSelected.family.card) :
    (auxiliary.coreFine selected).embedding
        (restriction.coreIndexEquiv source) =
      restriction.fineSelected.embedding source := by
  unfold coreIndexEquiv PureWZ2Prop62AuxiliaryLevel.coreFine
  change
    (auxiliary.coreIndices selected).orderEmbOfFin rfl
        (((auxiliary.coreIndices selected).orderIsoOfFin rfl).symm
          (restriction.restrictionCoreEquiv source)) =
      restriction.fineSelected.embedding source
  exact congrArg Subtype.val
    ((auxiliary.coreIndices selected).orderIsoOfFin rfl
      |>.apply_symm_apply (restriction.restrictionCoreEquiv source))

theorem coreIndexEquiv_tube
    (source : Fin restriction.fineSelected.family.card) :
    restriction.fineSelected.family.tube source =
      (auxiliary.coreFine selected).family.tube
        (restriction.coreIndexEquiv source) := by
  rw [restriction.fineSelected.tube_eq,
    (auxiliary.coreFine selected).tube_eq,
    restriction.coreIndexEquiv_embedding]

/--
Membership in the final genuine metric fiber is exactly the auxiliary label
of the corresponding ambient final-core leaf.
-/
theorem metricFiber_mem_iff_label_eq
    (label_eq :
      ∀ source,
        auxiliary.label source =
          metric.metricInput.packetParent
            (metric.mesh.restrictedOldData.cover.parent source))
    (parent : Fin restriction.coarseSelected.family.card)
    (source : Fin restriction.fineSelected.family.card) :
    source ∈
        wz2PaperFullFiberIndices
          restriction.fineSelected.family
          restriction.coarseSelected.family parent ↔
      auxiliary.label (restriction.fineSelected.embedding source) =
        restriction.coarseSelected.embedding parent := by
  have sourceImage :
      restriction.fineSelected.embedding source ∈
        Finset.image restriction.fineSelected.embedding Finset.univ :=
    Finset.mem_image.mpr
      ⟨source, Finset.mem_univ source, rfl⟩
  have sourceCore :
      restriction.fineSelected.embedding source ∈
        auxiliary.coreIndices selected := by
    simpa only [restriction.fine_image_univ] using sourceImage
  constructor
  · intro sourceFiber
    have ambientImage :
        restriction.fineSelected.embedding source ∈
          Finset.image restriction.fineSelected.embedding
            (wz2PaperFullFiberIndices
              restriction.fineSelected.family
              restriction.coarseSelected.family parent) :=
      Finset.mem_image.mpr ⟨source, sourceFiber, rfl⟩
    rw [restriction.fiber_image_eq] at ambientImage
    have ambientFiber := (Finset.mem_inter.mp ambientImage).2
    rw [metric.metricFiber_eq_assignedPackets,
      Finset.mem_filter] at ambientFiber
    exact (label_eq _).trans ambientFiber.2
  · intro sourceLabel
    have ambientFiber :
        restriction.fineSelected.embedding source ∈
          wz2PaperFullFiberIndices
            metric.selectedFine metric.metricParents
            (restriction.coarseSelected.embedding parent) := by
      rw [metric.metricFiber_eq_assignedPackets, Finset.mem_filter]
      exact
        ⟨Finset.mem_univ _, (label_eq _).symm.trans sourceLabel⟩
    have ambientInter :
        restriction.fineSelected.embedding source ∈
          auxiliary.coreIndices selected ∩
            wz2PaperFullFiberIndices
              metric.selectedFine metric.metricParents
              (restriction.coarseSelected.embedding parent) :=
      Finset.mem_inter.mpr ⟨sourceCore, ambientFiber⟩
    rw [← restriction.fiber_image_eq] at ambientInter
    rcases Finset.mem_image.mp ambientInter with
      ⟨candidate, candidateFiber, candidateEq⟩
    have candidateSource : candidate = source :=
      restriction.fineSelected.embedding.injective candidateEq
    simpa [candidateSource] using candidateFiber

/-- Every retained Section 6 parent has a nonempty complete metric fiber. -/
theorem metricFiber_nonempty
    (parent : Fin restriction.coarseSelected.family.card) :
    (wz2PaperFullFiberIndices
      restriction.fineSelected.family
      restriction.coarseSelected.family parent).Nonempty := by
  rcases restriction.section6Cover.parent_hit parent with
    ⟨source, sourceCovered⟩
  exact
    ⟨source,
      (mem_wz2PaperFullFiberIndices_iff parent source).mpr
        sourceCovered⟩

/--
The final metric fiber is saturated for every old coordinate strictly below
the inserted metric-parent level.
-/
theorem metricFiber_saturated_for_finer_coordinate
    (label_eq :
      ∀ source,
        auxiliary.label source =
          metric.metricInput.packetParent
            (metric.mesh.restrictedOldData.cover.parent source))
    (selectedNonempty : selected.Nonempty)
    (coordinate : Fin schedule.levelCount)
    (finerThanInsertion :
      auxiliary.insertionLevel < coordinate.1)
    (parent : Fin restriction.coarseSelected.family.card) :
    let coreScale :=
      auxiliary.outputScaleData coordinate selectedNonempty
    let reindexed :=
      coreScale.reindex restriction.coreIndexEquiv
        restriction.coreIndexEquiv_tube
    ∀ first second,
      reindexed.cover.parent first = reindexed.cover.parent second →
        (first ∈
            wz2PaperFullFiberIndices
              restriction.fineSelected.family
              restriction.coarseSelected.family parent ↔
          second ∈
            wz2PaperFullFiberIndices
              restriction.fineSelected.family
              restriction.coarseSelected.family parent) := by
  dsimp only
  intro first second parentEq
  let coreScale :=
    auxiliary.outputScaleData coordinate selectedNonempty
  have coreParentEq :
      coreScale.cover.parent (restriction.coreIndexEquiv first) =
        coreScale.cover.parent (restriction.coreIndexEquiv second) := by
    rw [← coreScale.cover.reindex_parent_eq
      coreScale.rho_pos.le restriction.coreIndexEquiv
      restriction.coreIndexEquiv_tube first]
    rw [← coreScale.cover.reindex_parent_eq
      coreScale.rho_pos.le restriction.coreIndexEquiv
      restriction.coreIndexEquiv_tube second]
    exact parentEq
  rw [
    auxiliary.outputScale_parent_eq_hitParent
      coordinate selectedNonempty (restriction.coreIndexEquiv first),
    auxiliary.outputScale_parent_eq_hitParent
      coordinate selectedNonempty (restriction.coreIndexEquiv second)
  ] at coreParentEq
  have ambientParentEq :
      (schedule.scaleData coordinate).cover.parent
          (restriction.fineSelected.embedding first) =
        (schedule.scaleData coordinate).cover.parent
          (restriction.fineSelected.embedding second) := by
    have embedded :=
      congrArg
        (auxiliary.coreCoarse coordinate selected).embedding
        coreParentEq
    change
      ((schedule.scaleData coordinate).cover.hitParentSubfamily
          (auxiliary.coreFine selected)).embedding
            ((schedule.scaleData coordinate).cover.hitParent
              (auxiliary.coreFine selected)
              (restriction.coreIndexEquiv first)) =
        ((schedule.scaleData coordinate).cover.hitParentSubfamily
          (auxiliary.coreFine selected)).embedding
            ((schedule.scaleData coordinate).cover.hitParent
              (auxiliary.coreFine selected)
              (restriction.coreIndexEquiv second))
      at embedded
    rw [
      (schedule.scaleData coordinate).cover.hitParent_ambient
        (auxiliary.coreFine selected)
        (restriction.coreIndexEquiv first),
      (schedule.scaleData coordinate).cover.hitParent_ambient
        (auxiliary.coreFine selected)
        (restriction.coreIndexEquiv second),
      restriction.coreIndexEquiv_embedding,
      restriction.coreIndexEquiv_embedding
    ] at embedded
    exact embedded
  have labelIff :=
    auxiliary.auxiliaryFiber_saturated_for_finer_coordinate
      coordinate finerThanInsertion
      (restriction.coarseSelected.embedding parent)
      (restriction.fineSelected.embedding first)
      (restriction.fineSelected.embedding second)
      ambientParentEq
  rw [
    restriction.metricFiber_mem_iff_label_eq label_eq parent first,
    restriction.metricFiber_mem_iff_label_eq label_eq parent second
  ]
  simpa only [
    PureWZ2Prop62AuxiliaryLevel.auxiliaryFiber,
    Finset.mem_filter, Finset.mem_univ, true_and
  ] using labelIff

/--
Restrict one final-core old witness to the complete genuine metric fiber.
The only constant change is the already-recorded final-core tree loss.
-/
noncomputable def metricFiberScaleData
    (label_eq :
      ∀ source,
        auxiliary.label source =
          metric.metricInput.packetParent
            (metric.mesh.restrictedOldData.cover.parent source))
    (selectedNonempty : selected.Nonempty)
    (coordinate : Fin schedule.levelCount)
    (finerThanInsertion :
      auxiliary.insertionLevel < coordinate.1)
    (parent : Fin restriction.coarseSelected.family.card)
    (fiberNonempty :
      (wz2PaperFullFiberIndices
        restriction.fineSelected.family
        restriction.coarseSelected.family parent).Nonempty) :
    WZ2PaperPureScaleCoverData
      (restriction.metricFiberSource parent).family
      (schedule.actualScale coordinate)
      (auxiliary.outputConstant selected) := by
  let coreScale :=
    auxiliary.outputScaleData coordinate selectedNonempty
  let reindexed :=
    coreScale.reindex restriction.coreIndexEquiv
      restriction.coreIndexEquiv_tube
  exact
    pureWZ2_prop62_restrictScaleToSaturated
      reindexed
      (wz2PaperFullFiberIndices
        restriction.fineSelected.family
        restriction.coarseSelected.family parent)
      fiberNonempty
      (restriction.metricFiber_saturated_for_finer_coordinate
        label_eq selectedNonempty coordinate finerThanInsertion parent)

end PureWZ2Prop62MetricCoreRestrictionData

/--
The data omitted by the bare finite pure schedule but present in the paper's
simultaneous Lemma 2.13 construction:

* the chosen coordinate is genuinely below the inserted metric-parent level;
* its final-core restriction has the synchronized WZ line-cover geometry;
* its hit parents retain the scheduled strong separation;
* numerical rounding either lands in that lower branch or in the inserted
  singleton top window.

The exact-scale CWA witness itself is not a field: it is constructed by
`metricFiberScaleData` from the one final augmented-tree core.
-/
structure PureWZ2Prop62MetricFiberRequestedRouteCertificate
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData fine scale C}
    {width M : ℝ}
    (metric :
      PureWZ2Prop62MetricPacketOutput
        (rho := rho) oldData width M)
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62PureSchedule
        metric.selectedFine ambientConstant scaleWindow)
    (auxiliary :
      PureWZ2Prop62AuxiliaryLevel
        schedule (Fin metric.metricParents.card))
    (selected : Finset (Fin metric.selectedFine.card))
    (selectedNonempty : selected.Nonempty)
    (restriction :
      PureWZ2Prop62MetricCoreRestrictionData
        metric.section6Cover (auxiliary.coreIndices selected))
    (label_eq :
      ∀ source,
        auxiliary.label source =
          metric.metricInput.packetParent
            (metric.mesh.restrictedOldData.cover.parent source))
    (sourceConstant : ENNReal) where
  rho_le_one : rho ≤ 1
  scale_separation : 100 * delta ≤ rho
  fine_bounded_base :
    HasBoundedBase metric.selectedFine 4
  source_constant_finite :
    WZ2PaperFiniteErrorConstant sourceConstant
  core_constant_le :
    auxiliary.outputConstant selected ≤ sourceConstant
  inserted_constant_le :
    pureWZ2Prop62InsertedCWALoss rho scale C *
        auxiliary.densityLoss selected ≤
      sourceConstant
  lower_line_cover :
    ∀ (parent : Fin restriction.coarseSelected.family.card)
      (coordinate : Fin schedule.levelCount)
      (finerThanInsertion :
        auxiliary.insertionLevel < coordinate.1),
      let scaleData :=
        (restriction.metricFiberScaleData
          label_eq selectedNonempty coordinate finerThanInsertion parent
          (restriction.metricFiber_nonempty parent)).mono
            core_constant_le
      ∀ source,
        WZ1PaperTubeCovers
          ((restriction.metricFiberSource parent).family.tube source)
          (scaleData.coarse.tube
            (scaleData.cover.parent source))
  lower_parent_embedding :
    ∀ (parent : Fin restriction.coarseSelected.family.card)
      (coordinate : Fin schedule.levelCount)
      (finerThanInsertion :
        auxiliary.insertionLevel < coordinate.1),
      let scaleData :=
        (restriction.metricFiberScaleData
          label_eq selectedNonempty coordinate finerThanInsertion parent
          (restriction.metricFiber_nonempty parent)).mono
            core_constant_le
      Fin scaleData.coarse.card ↪
        Fin (auxiliary.coreCoarse coordinate selected).family.card
  lower_parent_tube_eq :
    ∀ (parent : Fin restriction.coarseSelected.family.card)
      (coordinate : Fin schedule.levelCount)
      (finerThanInsertion :
        auxiliary.insertionLevel < coordinate.1)
      (middle : Fin
        ((restriction.metricFiberScaleData
          label_eq selectedNonempty coordinate finerThanInsertion parent
          (restriction.metricFiber_nonempty parent)).mono
            core_constant_le).coarse.card),
      let scaleData :=
        (restriction.metricFiberScaleData
          label_eq selectedNonempty coordinate finerThanInsertion parent
          (restriction.metricFiber_nonempty parent)).mono
            core_constant_le
      scaleData.coarse.tube middle =
        (auxiliary.coreCoarse coordinate selected).family.tube
          (lower_parent_embedding
            parent coordinate finerThanInsertion middle)
  requested_coordinate :
    ∀ requested : WZ2PaperRequestedScale (delta / rho),
      (∃ coordinate : Fin schedule.levelCount,
        auxiliary.insertionLevel < coordinate.1 ∧
          100 * delta ≤ schedule.actualScale coordinate ∧
          schedule.actualScale coordinate ≤ rho ∧
          requested.1 ≤ schedule.actualScale coordinate / rho ∧
          ENNReal.ofReal
              (schedule.actualScale coordinate / rho) <
            ((81000000 : ENNReal) * sourceConstant) *
              ENNReal.ofReal requested.1) ∨
      (4 : ENNReal) <
        ((81000000 : ENNReal) * sourceConstant) *
          ENNReal.ofReal requested.1

namespace PureWZ2Prop62MetricFiberRequestedRouteCertificate

variable
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData fine scale C}
    {width M : ℝ}
    {metric :
      PureWZ2Prop62MetricPacketOutput
        (rho := rho) oldData width M}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule
        metric.selectedFine ambientConstant scaleWindow}
    {auxiliary :
      PureWZ2Prop62AuxiliaryLevel
        schedule (Fin metric.metricParents.card)}
    {selected : Finset (Fin metric.selectedFine.card)}
    {selectedNonempty : selected.Nonempty}
    {restriction :
      PureWZ2Prop62MetricCoreRestrictionData
        metric.section6Cover (auxiliary.coreIndices selected)}
    {label_eq :
      ∀ source,
        auxiliary.label source =
          metric.metricInput.packetParent
            (metric.mesh.restrictedOldData.cover.parent source)}
    {sourceConstant : ENNReal}

/-- The exact lower-or-top route consumed by literal unit rescaling. -/
theorem requestedRoute
    (certificate :
      PureWZ2Prop62MetricFiberRequestedRouteCertificate
        metric schedule auxiliary selected selectedNonempty
        restriction label_eq sourceConstant)
    (scheduledParentSeparated :
      ∀ (coordinate : Fin schedule.levelCount)
        (first second :
          Fin (auxiliary.coreCoarse coordinate selected).family.card),
        first ≠ second →
          wz2PaperLiteralSourceSeparationFactor *
                schedule.actualScale coordinate <
            wz1PaperLineDistance
              ((auxiliary.coreCoarse coordinate selected).family.tube first)
              ((auxiliary.coreCoarse coordinate selected).family.tube second))
    (parent : Fin restriction.coarseSelected.family.card) :
    ∀ requested : WZ2PaperRequestedScale (delta / rho),
      (∃ (actual : ℝ)
        (scaleData :
          WZ2PaperPureScaleCoverData
            (restriction.metricFiberSource parent).family
            actual sourceConstant),
          100 * delta ≤ actual ∧
          actual ≤ rho ∧
          requested.1 ≤ actual / rho ∧
          ENNReal.ofReal (actual / rho) <
            ((81000000 : ENNReal) * sourceConstant) *
              ENNReal.ofReal requested.1 ∧
          WZ1PaperIsLineClass scaleData.coarse ∧
          (∀ source,
            WZ1PaperTubeCovers
              ((restriction.metricFiberSource parent).family.tube source)
              (scaleData.coarse.tube
                (scaleData.cover.parent source))) ∧
          (∀ middle,
            WZ2PaperDilatedTubeCovers 2
              (scaleData.coarse.tube middle)
              (restriction.coarseSelected.family.tube parent)) ∧
          (∀ first second, first ≠ second →
            wz2PaperLiteralSourceSeparationFactor * actual <
              wz1PaperLineDistance
                (scaleData.coarse.tube first)
                (scaleData.coarse.tube second)) ∧
          WZ2PaperOrdinaryNestedTargetLocalization
            (restriction.metricFiberSource parent).family
            scaleData.coarse
            (restriction.coarseSelected.family.tube parent)
            metric.metricInput.rho_pos) ∨
      (4 : ENNReal) <
        ((81000000 : ENNReal) * sourceConstant) *
          ENNReal.ofReal requested.1 := by
  intro requested
  rcases
      PureWZ2Prop62MetricFiberRequestedRouteCertificate.requested_coordinate
        certificate requested
    with lower | topWindow
  · rcases lower with
      ⟨coordinate, finerThanInsertion, treeSafe, actualLe,
        requestedLe, within⟩
    let scaleData :=
      (restriction.metricFiberScaleData
        label_eq selectedNonempty coordinate finerThanInsertion parent
        (restriction.metricFiber_nonempty parent)).mono
          certificate.core_constant_le
    let parentEmbedding :=
      certificate.lower_parent_embedding
        parent coordinate finerThanInsertion
    have coreMiddleLine :
        WZ1PaperIsLineClass
          (auxiliary.coreCoarse coordinate selected).family :=
      (schedule.coarse_line_class coordinate).subfamily
        (auxiliary.coreCoarse coordinate selected).toTubeSubfamily
    have middleLine :
        WZ1PaperIsLineClass scaleData.coarse := by
      intro middle
      rw [certificate.lower_parent_tube_eq
        parent coordinate finerThanInsertion middle]
      exact coreMiddleLine (parentEmbedding middle)
    have fineMiddle :
        ∀ source,
          WZ1PaperTubeCovers
            ((restriction.metricFiberSource parent).family.tube source)
            (scaleData.coarse.tube
              (scaleData.cover.parent source)) :=
      certificate.lower_line_cover
        parent coordinate finerThanInsertion
    have sourceLine :
        WZ1PaperIsLineClass
          (restriction.metricFiberSource parent).family :=
      restriction.section6Cover.fine_line_class.subfamily
        (restriction.metricFiberSource parent).toTubeSubfamily
    have anchorLine :
        WZ1PaperTubeInLineClass
          (restriction.coarseSelected.family.tube parent) :=
      restriction.section6Cover.coarse_line_class parent
    have sourceCovered :
        ∀ source,
          WZ1PaperTubeCovers
            ((restriction.metricFiberSource parent).family.tube source)
            (restriction.coarseSelected.family.tube parent) := by
      intro source
      rw [(restriction.metricFiberSource parent).tube_eq]
      exact
        (mem_wz2PaperFullFiberIndices_iff parent
          ((restriction.metricFiberSource parent).embedding source)).mp
          (Finset.orderEmbOfFin_mem
            (wz2PaperFullFiberIndices
              restriction.fineSelected.family
              restriction.coarseSelected.family parent)
            rfl source)
    have sourceNonempty :
        (restriction.metricFiberSource parent).family.Nonempty := by
      change
        0 <
          (wz2PaperFullFiberIndices
            restriction.fineSelected.family
            restriction.coarseSelected.family parent).card
      exact Finset.card_pos.mpr
        (restriction.metricFiber_nonempty parent)
    have middleAnchor :
        ∀ middle,
          WZ2PaperDilatedTubeCovers 2
            (scaleData.coarse.tube middle)
            (restriction.coarseSelected.family.tube parent) := by
      intro middle
      have middleFiberNonempty :=
        scaleData.cover.fullFiber_nonempty_of_uniform
          sourceNonempty scaleData.full_fiber_uniform middle
      rcases middleFiberNonempty with ⟨source, sourceMem⟩
      have sourceParent :
          scaleData.cover.parent source = middle :=
        (scaleData.cover.mem_fullFiber_iff_parent_eq
          scaleData.rho_pos.le middle source).mp sourceMem
      have fineToMiddle := fineMiddle source
      rw [sourceParent] at fineToMiddle
      have fineToAnchor := sourceCovered source
      have triangle :=
        wz1PaperLineDistance_triangle
          (scaleData.coarse.tube middle)
          ((restriction.metricFiberSource parent).family.tube source)
          (restriction.coarseSelected.family.tube parent)
      have symmetry :
          wz1PaperLineDistance
              (scaleData.coarse.tube middle)
              ((restriction.metricFiberSource parent).family.tube source) =
            wz1PaperLineDistance
              ((restriction.metricFiberSource parent).family.tube source)
              (scaleData.coarse.tube middle) :=
        wz1PaperLineDistance_symm _ _
      rw [symmetry] at triangle
      unfold WZ1PaperTubeCovers at fineToMiddle fineToAnchor
      unfold WZ2PaperDilatedTubeCovers
      nlinarith
    have middleSeparated :
        ∀ first second, first ≠ second →
          wz2PaperLiteralSourceSeparationFactor *
                schedule.actualScale coordinate <
            wz1PaperLineDistance
              (scaleData.coarse.tube first)
              (scaleData.coarse.tube second) := by
      intro first second indexNe
      have embeddedNe :
          parentEmbedding first ≠ parentEmbedding second :=
        parentEmbedding.injective.ne indexNe
      have separated :=
        scheduledParentSeparated
          coordinate (parentEmbedding first) (parentEmbedding second)
          embeddedNe
      have firstTube :
          scaleData.coarse.tube first =
            (auxiliary.coreCoarse coordinate selected).family.tube
              (parentEmbedding first) :=
        certificate.lower_parent_tube_eq
          parent coordinate finerThanInsertion first
      have secondTube :
          scaleData.coarse.tube second =
            (auxiliary.coreCoarse coordinate selected).family.tube
              (parentEmbedding second) :=
        certificate.lower_parent_tube_eq
          parent coordinate finerThanInsertion second
      rw [firstTube, secondTube]
      exact separated
    have targetLocal :
        ∀ target,
          ‖wz2PaperTubeMidpoint
            ((wz2PaperLiteralOrdinaryRescaledFamily
              (restriction.metricFiberSource parent).family
              (restriction.coarseSelected.family.tube parent)
              metric.metricInput.rho_pos).tube target)‖ ≤ 3 := by
      intro target
      exact
        wz2PaperLiteralOrdinaryRescaledTube_midpoint_norm_le_three_of_boundedBase
          metric.metricInput.rho_pos certificate.rho_le_one
          ((restriction.metricFiberSource parent).family.tube target)
          (restriction.coarseSelected.family.tube parent)
          (sourceLine target)
          (by
            rw [(restriction.metricFiberSource parent).tube_eq,
              restriction.fineSelected.tube_eq]
            exact certificate.fine_bounded_base
              (restriction.fineSelected.embedding
                ((restriction.metricFiberSource parent).embedding target)))
          (sourceCovered target)
    have localization :
        WZ2PaperOrdinaryNestedTargetLocalization
          (restriction.metricFiberSource parent).family
          scaleData.coarse
          (restriction.coarseSelected.family.tube parent)
          metric.metricInput.rho_pos :=
      wz2PaperOrdinaryNestedTargetLocalization_of_sourceCovers
        oldData.delta_pos scaleData.rho_pos metric.metricInput.rho_pos
        certificate.rho_le_one
        (restriction.metricFiberSource parent).family
        scaleData.coarse
        (restriction.coarseSelected.family.tube parent)
        sourceLine middleLine anchorLine
        sourceCovered middleAnchor targetLocal
    exact
      Or.inl
        ⟨schedule.actualScale coordinate, scaleData,
          treeSafe, actualLe, requestedLe, within,
          middleLine, fineMiddle, middleAnchor,
          middleSeparated, localization⟩
  · exact Or.inr topWindow

/--
Assemble the canonical public rescaling input for one final genuine metric
fiber.  The caller supplies only the source conflict-colour separation on the
already frozen final core; no further fine-family selection occurs here.
-/
noncomputable def toMetricFiberRescalingInput
    (certificate :
      PureWZ2Prop62MetricFiberRequestedRouteCertificate
        metric schedule auxiliary selected selectedNonempty
        restriction label_eq sourceConstant)
    (scheduledParentSeparated :
      ∀ (coordinate : Fin schedule.levelCount)
        (first second :
          Fin (auxiliary.coreCoarse coordinate selected).family.card),
        first ≠ second →
          wz2PaperLiteralSourceSeparationFactor *
                schedule.actualScale coordinate <
            wz1PaperLineDistance
              ((auxiliary.coreCoarse coordinate selected).family.tube first)
              ((auxiliary.coreCoarse coordinate selected).family.tube second))
    (parent : Fin restriction.coarseSelected.family.card)
    (sourceStronglySeparated :
      ∀ first second :
          Fin (restriction.metricFiberSource parent).family.card,
        first ≠ second →
          wz2PaperLiteralSourceSeparationFactor * delta <
            wz1PaperLineDistance
              ((restriction.metricFiberSource parent).family.tube first)
              ((restriction.metricFiberSource parent).family.tube second)) :
    PureWZ2Prop62MetricFiberRescalingInput
      restriction.section6Cover parent sourceConstant := by
  let sourceIndices :=
    wz2PaperFullFiberIndices
      restriction.fineSelected.family
      restriction.coarseSelected.family parent
  let sourceFamily := restriction.metricFiberSource parent
  let sourceEquiv :
      Fin sourceFamily.family.card ≃ sourceIndices :=
    (sourceIndices.orderIsoOfFin rfl).toEquiv
  have sourceLine :
      WZ1PaperIsLineClass sourceFamily.family :=
    restriction.section6Cover.fine_line_class.subfamily
      sourceFamily.toTubeSubfamily
  have sourceCovered :
      ∀ index,
        WZ1PaperTubeCovers
          (sourceFamily.family.tube index)
          (restriction.coarseSelected.family.tube parent) := by
    intro index
    rw [sourceFamily.tube_eq]
    exact
      (mem_wz2PaperFullFiberIndices_iff parent
        (sourceFamily.embedding index)).mp
        (Finset.orderEmbOfFin_mem sourceIndices rfl index)
  have targetLocality :
      ∀ index,
        ‖wz2PaperTubeMidpoint
          ((wz2PaperLiteralOrdinaryRescaledFamily
            sourceFamily.family
            (restriction.coarseSelected.family.tube parent)
            metric.metricInput.rho_pos).tube index)‖ ≤ 3 := by
    intro index
    exact
      wz2PaperLiteralOrdinaryRescaledTube_midpoint_norm_le_three_of_boundedBase
        metric.metricInput.rho_pos certificate.rho_le_one
        (sourceFamily.family.tube index)
        (restriction.coarseSelected.family.tube parent)
        (sourceLine index)
        (by
          rw [sourceFamily.tube_eq,
            restriction.fineSelected.tube_eq]
          exact certificate.fine_bounded_base
            (restriction.fineSelected.embedding
              (sourceFamily.embedding index)))
        (sourceCovered index)
  have physicalCWA :
      WZ2PaperBodyConvexWolffBound
        (wz2PaperLiteralOrdinaryRescaledFamily
          sourceFamily.family
          (restriction.coarseSelected.family.tube parent)
          metric.metricInput.rho_pos).toBodyFamily
        sourceConstant := by
    have raw :=
      restriction.metricFiberRescaledPhysicalCWA
        metric auxiliary selected label_eq parent certificate.rho_le_one
    intro convexSet convex
    exact (raw convexSet convex).trans (by
      gcongr
      exact certificate.inserted_constant_le)
  exact
    {
      rho_pos := metric.metricInput.rho_pos
      rho_le_one := certificate.rho_le_one
      delta_pos := oldData.delta_pos
      scale_separation := certificate.scale_separation
      sourceIndices := sourceIndices
      sourceIndices_eq := rfl
      sourceIndices_nonempty :=
        restriction.metricFiber_nonempty parent
      sourceFamily := sourceFamily.family
      sourceEquiv := sourceEquiv
      source_tube_eq := by
        intro index
        rfl
      source_line_class := sourceLine
      anchor_line_class :=
        restriction.section6Cover.coarse_line_class parent
      source_covered := sourceCovered
      source_strongly_separated := sourceStronglySeparated
      source_constant_finite := certificate.source_constant_finite
      target_locality := targetLocality
      rescaled_physical_cwa := physicalCWA
      requested_route :=
        certificate.requestedRoute scheduledParentSeparated parent
    }

end PureWZ2Prop62MetricFiberRequestedRouteCertificate

end Kakeya.Assouad

end
