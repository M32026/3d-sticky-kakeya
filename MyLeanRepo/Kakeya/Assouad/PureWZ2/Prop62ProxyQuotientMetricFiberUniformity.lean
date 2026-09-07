import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientPreCoreAdapter
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientInsertedCWA
import Mathlib.Tactic

/-!
# Proposition 6.2 quotient metric-fiber uniformity

The whole metric fibers are put in one `DMinus` class before any leaf cut.
The unique quotient auxiliary-tree cleanup then gives

`DMinus ≤ Λ * #(final metric fiber)`,

while restriction can only decrease the pre-core upper bound

`#(final metric fiber) < 2 * DMinus`.

Thus the final restricted complete metric fibers are uniformly comparable
with constant exactly `2 * Λ`.  No upper-parent copy bound is used.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62ProxyQuotientMetricCoreOutput

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
    (output :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)

/--
At the inserted auxiliary level, the ambient metric fiber is bounded by the
single cleanup-density factor times its surviving core intersection.
-/
theorem ambientMetricFiber_le_quotientDensityLoss_core
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (parent : Fin output.metric.metricParents.card)
    (coreFiberNonempty :
      (output.pulledBack ∩
        wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents parent).Nonempty) :
    ((wz2PaperFullFiberIndices
      output.metric.selectedFine
      output.metric.metricParents parent).card : ENNReal) ≤
      output.quotientDensityLoss *
        ((output.pulledBack ∩
          wz2PaperFullFiberIndices
            output.metric.selectedFine
            output.metric.metricParents parent).card : ENNReal) := by
  let ambientFiber :=
    output.cleanup.auxiliary.auxiliaryFiber
      (output.metricParentLabel parent)
  let ambientCoreFiber :=
    output.cleanup.core.core ∩ ambientFiber
  have ambientFiberImage :
      Finset.image
          output.metric.mesh.complete.selectedFine.embedding
          (wz2PaperFullFiberIndices
            output.metric.selectedFine
            output.metric.metricParents parent) =
        ambientFiber := by
    simpa only [ambientFiber] using
      output.metricFiber_image_eq_ambientAuxiliaryFiber
        fineLine fineBase rhoPos widthPos packetScaleLeRho
        sixWidthLe parent
  have ambientCoreFiberImage :
      Finset.image
          output.metric.mesh.complete.selectedFine.embedding
          (output.pulledBack ∩
            wz2PaperFullFiberIndices
              output.metric.selectedFine
              output.metric.metricParents parent) =
        ambientCoreFiber := by
    simpa only [ambientCoreFiber, ambientFiber] using
      output.coreMetricFiber_image_eq_ambientCoreAuxiliaryFiber
        fineLine fineBase rhoPos widthPos packetScaleLeRho
        sixWidthLe parent
  have ambientCoreFiberNonempty : ambientCoreFiber.Nonempty := by
    rcases coreFiberNonempty with ⟨source, sourceMem⟩
    exact
      ⟨output.metric.mesh.complete.selectedFine.embedding source, by
        rw [← ambientCoreFiberImage]
        exact Finset.mem_image.mpr ⟨source, sourceMem, rfl⟩⟩
  have densityNat :=
    output.cleanup.auxiliary_density
      (output.metricParentLabel parent) <| by
        simpa only [ambientCoreFiber, ambientFiber] using
          ambientCoreFiberNonempty
  have density :
      (output.cleanup.preliminary.card : ENNReal) *
          (ambientFiber.card : ENNReal) ≤
        (2 ^ (schedule.levelCount + 1) : ENNReal) *
          (ambientCoreFiber.card : ENNReal) *
          fine.enncard := by
    have densityCast :
        ((output.cleanup.preliminary.card *
          ambientFiber.card : ℕ) : ENNReal) ≤
          ((2 ^ (schedule.levelCount + 1) *
            ambientCoreFiber.card * fine.card : ℕ) : ENNReal) := by
      exact_mod_cast densityNat
    simpa only [
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      Kakeya.Streamlined.TubeFamily.enncard
    ] using densityCast
  have selectedPos :
      (output.cleanup.preliminary.card : ENNReal) ≠ 0 := by
    exact_mod_cast
      (Finset.card_pos.mpr
        output.cleanup.preliminary_nonempty).ne'
  have selectedTop :
      (output.cleanup.preliminary.card : ENNReal) ≠ ⊤ := by
    simp
  have ambientFiberCard :
      (wz2PaperFullFiberIndices
        output.metric.selectedFine
        output.metric.metricParents parent).card =
        ambientFiber.card := by
    rw [← ambientFiberImage]
    exact
      Finset.card_image_of_injective _
        output.metric.mesh.complete.selectedFine.embedding.injective |>.symm
  have ambientCoreFiberCard :
      (output.pulledBack ∩
        wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents parent).card =
        ambientCoreFiber.card := by
    rw [← ambientCoreFiberImage]
    exact
      Finset.card_image_of_injective _
        output.metric.mesh.complete.selectedFine.embedding.injective |>.symm
  rw [ambientFiberCard, ambientCoreFiberCard]
  calc
    (ambientFiber.card : ENNReal) =
        (output.cleanup.preliminary.card : ENNReal)⁻¹ *
          ((output.cleanup.preliminary.card : ENNReal) *
            (ambientFiber.card : ENNReal)) := by
      rw [← mul_assoc,
        ENNReal.inv_mul_cancel selectedPos selectedTop, one_mul]
    _ ≤
        (output.cleanup.preliminary.card : ENNReal)⁻¹ *
          ((2 ^ (schedule.levelCount + 1) : ENNReal) *
            (ambientCoreFiber.card : ENNReal) *
            fine.enncard) := by
      gcongr
    _ =
        output.quotientDensityLoss *
          (ambientCoreFiber.card : ENNReal) := by
      simp only [quotientDensityLoss,
        Kakeya.Streamlined.TubeFamily.enncard]
      ring

/-- Final restricted fibers have the cardinality of the corresponding core
intersection in the original metric family. -/
theorem finalMetricFiber_card_eq_coreMetricFiber
    (parent :
      Fin output.restriction.coarseSelected.family.card) :
    (wz2PaperFullFiberIndices
        output.restriction.fineSelected.family
        output.restriction.coarseSelected.family parent).card =
      (output.pulledBack ∩
        wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents
          (output.restriction.coarseSelected.embedding parent)).card := by
  rw [← output.restriction.fiber_image_eq parent]
  exact
    (Finset.card_image_of_injective _
      output.restriction.fineSelected.embedding.injective).symm

/-- Every final metric parent comes from the pre-cleanup `DMinus` class. -/
theorem finalMetricParent_mem_DMinusClass
    {SourceColor : Type*}
    [Fintype SourceColor] [DecidableEq SourceColor]
    [Nonempty SourceColor]
    {coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    {sourceColor : Fin fine.card → SourceColor}
    (adapter :
      PureWZ2Prop62ProxyQuotientPreCoreAdapterData
        schedule fineNonempty quotient width packetCoordinate
        strideBase weight output.metric coloring SourceColor sourceColor)
    (preliminary_eq :
      output.cleanup.preliminary = adapter.preCore.preliminary)
    (parent :
      Fin output.restriction.coarseSelected.family.card) :
    output.restriction.coarseSelected.embedding parent ∈
      adapter.preCore.fiberBin.selectedParents := by
  rcases output.restriction.section6Cover.parent_hit parent with
    ⟨source, sourceCovered⟩
  have sourcePulledBack :
      output.restriction.fineSelected.embedding source ∈
        output.pulledBack := by
    have sourceImage :
        output.restriction.fineSelected.embedding source ∈
          Finset.image output.restriction.fineSelected.embedding
            Finset.univ :=
      Finset.mem_image.mpr ⟨source, Finset.mem_univ source, rfl⟩
    rwa [output.restriction.fine_image_univ] at sourceImage
  let selectedSource :=
    output.restriction.fineSelected.embedding source
  let ambientSource :=
    output.metric.mesh.complete.selectedFine.embedding selectedSource
  have ambientCore : ambientSource ∈ output.cleanup.core.core := by
    rw [← output.ambientCore_eq, ← output.image_eq]
    exact Finset.mem_image.mpr
      ⟨selectedSource, sourcePulledBack, rfl⟩
  have ambientPreliminary :
      ambientSource ∈ adapter.preCore.preliminary := by
    rw [← preliminary_eq]
    exact output.cleanup.core.core_subset ambientCore
  have parentSelected :=
    adapter.preCore.preliminary_parent_selected
      ambientSource ambientPreliminary
  have selectedParentEq :
      output.metric.ambientMetricParentOf ambientSource =
        output.restriction.coarseSelected.embedding parent := by
    have covered :
        WZ1PaperTubeCovers
          (output.metric.selectedFine.tube selectedSource)
          (output.metric.metricParents.tube
            (output.restriction.coarseSelected.embedding parent)) := by
      simpa only [selectedSource,
        output.restriction.fineSelected.tube_eq,
        output.restriction.coarseSelected.tube_eq] using
          sourceCovered
    have canonicalParent :
        output.metric.metricParentOf selectedSource =
          output.restriction.coarseSelected.embedding parent := by
      exact
        (output.metric.section6Cover.toWZ1PaperTubeCover
          |>.parent_unique selectedSource
            (output.restriction.coarseSelected.embedding parent)
            covered).symm
    change
      output.metric.ambientMetricParentOf
          (output.metric.mesh.complete.selectedFine.embedding
            selectedSource) =
        output.restriction.coarseSelected.embedding parent
    rw [output.metric.ambientMetricParentOf_embedding]
    exact canonicalParent
  rwa [selectedParentEq] at parentSelected

/-- The final fiber remains below the upper edge of its original `DMinus`
class. -/
theorem finalMetricFiber_card_lt_two_DMinus
    {SourceColor : Type*}
    [Fintype SourceColor] [DecidableEq SourceColor]
    [Nonempty SourceColor]
    {coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    {sourceColor : Fin fine.card → SourceColor}
    (adapter :
      PureWZ2Prop62ProxyQuotientPreCoreAdapterData
        schedule fineNonempty quotient width packetCoordinate
        strideBase weight output.metric coloring SourceColor sourceColor)
    (preliminary_eq :
      output.cleanup.preliminary = adapter.preCore.preliminary)
    (parent :
      Fin output.restriction.coarseSelected.family.card) :
    (wz2PaperFullFiberIndices
        output.restriction.fineSelected.family
        output.restriction.coarseSelected.family parent).card <
      2 * adapter.preCore.fiberBin.DMinus := by
  let ambientParent :=
    output.restriction.coarseSelected.embedding parent
  have parentSelected :=
    output.finalMetricParent_mem_DMinusClass
      adapter preliminary_eq parent
  have band :=
    adapter.preCore.DMinus_band ambientParent parentSelected
  have ambientBandUpper :
      (wz2PaperFullFiberIndices
        output.metric.selectedFine output.metric.metricParents
          ambientParent).card <
        2 * adapter.preCore.fiberBin.DMinus := by
    calc
      (wz2PaperFullFiberIndices
          output.metric.selectedFine output.metric.metricParents
            ambientParent).card =
          (output.metric.completeMetricFiber ambientParent).card := rfl
      _ =
          (output.metric.ambientCompleteMetricFiber ambientParent).card :=
        (output.metric.ambientCompleteMetricFiber_card ambientParent).symm
      _ < 2 * adapter.preCore.fiberBin.DMinus := band.2
  rw [output.finalMetricFiber_card_eq_coreMetricFiber parent]
  exact
    (Finset.card_le_card Finset.inter_subset_right).trans_lt <| by
      exact ambientBandUpper

/-- The cleanup density transfers the lower edge of the original `DMinus`
class to every final metric fiber. -/
theorem DMinus_le_quotientDensityLoss_finalMetricFiber
    {SourceColor : Type*}
    [Fintype SourceColor] [DecidableEq SourceColor]
    [Nonempty SourceColor]
    {coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    {sourceColor : Fin fine.card → SourceColor}
    (adapter :
      PureWZ2Prop62ProxyQuotientPreCoreAdapterData
        schedule fineNonempty quotient width packetCoordinate
        strideBase weight output.metric coloring SourceColor sourceColor)
    (preliminary_eq :
      output.cleanup.preliminary = adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (parent :
      Fin output.restriction.coarseSelected.family.card) :
    (adapter.preCore.fiberBin.DMinus : ENNReal) ≤
      output.quotientDensityLoss *
        ((wz2PaperFullFiberIndices
          output.restriction.fineSelected.family
          output.restriction.coarseSelected.family parent).card :
          ENNReal) := by
  let ambientParent :=
    output.restriction.coarseSelected.embedding parent
  have parentSelected :=
    output.finalMetricParent_mem_DMinusClass
      adapter preliminary_eq parent
  have band :=
    adapter.preCore.DMinus_band ambientParent parentSelected
  have finalFiberNonempty :
      (wz2PaperFullFiberIndices
        output.restriction.fineSelected.family
        output.restriction.coarseSelected.family parent).Nonempty := by
    rcases output.restriction.lineCover.parent_surjective parent with
      ⟨source, parentEq⟩
    exact
      ⟨source,
        (mem_wz2PaperFullFiberIndices_iff parent source).mpr <| by
          rw [← parentEq]
          exact output.restriction.lineCover.parent_covers source⟩
  have coreFiberNonempty :
      (output.pulledBack ∩
        wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents ambientParent).Nonempty := by
    rcases finalFiberNonempty with ⟨source, sourceMem⟩
    have imageMem :
        output.restriction.fineSelected.embedding source ∈
          Finset.image output.restriction.fineSelected.embedding
            (wz2PaperFullFiberIndices
              output.restriction.fineSelected.family
              output.restriction.coarseSelected.family parent) :=
      Finset.mem_image.mpr ⟨source, sourceMem, rfl⟩
    rw [output.restriction.fiber_image_eq parent] at imageMem
    exact
      ⟨output.restriction.fineSelected.embedding source,
        imageMem⟩
  have density :=
    output.ambientMetricFiber_le_quotientDensityLoss_core
      fineLine fineBase rhoPos widthPos packetScaleLeRho
      sixWidthLe ambientParent coreFiberNonempty
  rw [← output.finalMetricFiber_card_eq_coreMetricFiber parent]
    at density
  have ambientBandLower :
      (adapter.preCore.fiberBin.DMinus : ENNReal) ≤
        ((wz2PaperFullFiberIndices
          output.metric.selectedFine output.metric.metricParents
            ambientParent).card : ENNReal) := by
    have raw :
        (adapter.preCore.fiberBin.DMinus : ENNReal) ≤
          ((output.metric.ambientCompleteMetricFiber
            ambientParent).card : ENNReal) := by
      exact_mod_cast band.1
    calc
      (adapter.preCore.fiberBin.DMinus : ENNReal) ≤
          ((output.metric.ambientCompleteMetricFiber
            ambientParent).card : ENNReal) := raw
      _ =
          ((output.metric.completeMetricFiber ambientParent).card :
            ENNReal) := by
        rw [output.metric.ambientCompleteMetricFiber_card ambientParent]
      _ =
          ((wz2PaperFullFiberIndices
            output.metric.selectedFine output.metric.metricParents
              ambientParent).card : ENNReal) := rfl
  exact
    ambientBandLower.trans density

/--
The final restricted complete metric fibers are uniformly comparable with
constant exactly `2 * Λ`.  Here `Λ` bounds the one and only quotient cleanup
density loss.
-/
theorem finalMetricFullFibers_uniform
    {SourceColor : Type*}
    [Fintype SourceColor] [DecidableEq SourceColor]
    [Nonempty SourceColor]
    {coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    {sourceColor : Fin fine.card → SourceColor}
    (adapter :
      PureWZ2Prop62ProxyQuotientPreCoreAdapterData
        schedule fineNonempty quotient width packetCoordinate
        strideBase weight output.metric coloring SourceColor sourceColor)
    (preliminary_eq :
      output.cleanup.preliminary = adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (Λ : ENNReal)
    (densityLoss_le : output.quotientDensityLoss ≤ Λ) :
    ∀ first second,
      ((wz2PaperFullFiberIndices
        output.restriction.fineSelected.family
        output.restriction.coarseSelected.family first).card :
          ENNReal) ≤
        (2 * Λ) *
          ((wz2PaperFullFiberIndices
            output.restriction.fineSelected.family
            output.restriction.coarseSelected.family second).card :
              ENNReal) := by
  intro first second
  have firstUpper :=
    output.finalMetricFiber_card_lt_two_DMinus
      adapter preliminary_eq first
  have secondLower :=
    output.DMinus_le_quotientDensityLoss_finalMetricFiber
      adapter preliminary_eq fineLine fineBase rhoPos widthPos
      packetScaleLeRho sixWidthLe second
  have firstUpperENN :
      ((wz2PaperFullFiberIndices
        output.restriction.fineSelected.family
        output.restriction.coarseSelected.family first).card :
          ENNReal) ≤
        2 * (adapter.preCore.fiberBin.DMinus : ENNReal) := by
    exact_mod_cast Nat.le_of_lt firstUpper
  calc
    ((wz2PaperFullFiberIndices
          output.restriction.fineSelected.family
          output.restriction.coarseSelected.family first).card :
        ENNReal) ≤
        2 * (adapter.preCore.fiberBin.DMinus : ENNReal) :=
      firstUpperENN
    _ ≤
        2 *
          (output.quotientDensityLoss *
            ((wz2PaperFullFiberIndices
              output.restriction.fineSelected.family
              output.restriction.coarseSelected.family second).card :
                ENNReal)) := by
      gcongr
    _ ≤
        2 *
          (Λ *
            ((wz2PaperFullFiberIndices
              output.restriction.fineSelected.family
              output.restriction.coarseSelected.family second).card :
                ENNReal)) := by
      gcongr
    _ =
        (2 * Λ) *
          ((wz2PaperFullFiberIndices
            output.restriction.fineSelected.family
            output.restriction.coarseSelected.family second).card :
              ENNReal) := by
      ring

end PureWZ2Prop62ProxyQuotientMetricCoreOutput

end Kakeya.Assouad

end
