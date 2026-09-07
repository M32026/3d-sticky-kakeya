import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PacketMetricAuxiliaryFiber
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62InsertedCWACore

/-!
# Proposition 6.2: quantitative metric fibers from the ancestry core

Transfer the one ambient augmented-tree density estimate through the exact
packet-hull pullback.  The resulting core-density loss is the paper's
`2^(L+1) * #U / #S`.  It is then applied to the pre-core inserted CWA and to
the preliminary metric-fiber cardinality comparison.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62AncestryMetricPreliminaryOutput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow}
    {scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {coordinateCount : ℕ}
    {Color : Fin coordinateCount → Type*}
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    {color : ∀ coordinate, Fin fine.card → Color coordinate}
    {weight : Fin fine.card → ENNReal}
    {preliminary :
      PureWZ2Prop62AncestryPreliminarySelectionData
        schedule scheduled rho width packetCoordinate
        Color color weight}
    {M : ℝ}
    (output :
      PureWZ2Prop62AncestryMetricPreliminaryOutput
        schedule scheduled width packetCoordinate
        Color color weight preliminary M)

def ancestryDensityLoss : ENNReal :=
  let _ := output
  (2 ^ (schedule.levelCount + 1) : ENNReal) *
    fine.enncard *
    (output.binnedAmbientPreliminary.card : ENNReal)⁻¹

theorem ambientAuxiliaryFiber_le_ancestryDensityLoss_core
    (label :
      schedule.CompleteAncestryLabel packetCoordinate
        (schedule.packetLineCell packetCoordinate width))
    (coreFiberNonempty :
      (output.ancestryAuxiliaryCore.ambientCore ∩
        output.ancestryAuxiliary.auxiliaryFiber label).Nonempty) :
    ((output.ancestryAuxiliary.auxiliaryFiber label).card : ENNReal) ≤
      output.ancestryDensityLoss *
        ((output.ancestryAuxiliaryCore.ambientCore ∩
          output.ancestryAuxiliary.auxiliaryFiber label).card :
          ENNReal) := by
  have selectedPos :
      0 < (output.binnedAmbientPreliminary.card : ENNReal) := by
    exact_mod_cast
      Finset.card_pos.mpr output.binnedAmbientPreliminary_nonempty
  have selectedTop :
      (output.binnedAmbientPreliminary.card : ENNReal) ≠ ⊤ := by
    simp
  have ambientCoreEq :
      output.ancestryAuxiliaryCore.ambientCore =
        (output.ancestryAuxiliary.coreOutput
          output.binnedAmbientPreliminary).core := by
    exact output.ancestryAuxiliaryCore.ambientCore_eq
  have densityNat :=
    (output.ancestryAuxiliary.coreOutput
      output.binnedAmbientPreliminary).auxiliary_density
      label <| by
        rw [← ambientCoreEq]
        exact coreFiberNonempty
  have densityNatAmbient :
      output.binnedAmbientPreliminary.card *
          (output.ancestryAuxiliary.auxiliaryFiber label).card ≤
        2 ^ (schedule.levelCount + 1) *
          (output.ancestryAuxiliaryCore.ambientCore ∩
            output.ancestryAuxiliary.auxiliaryFiber label).card *
          fine.card := by
    rw [ambientCoreEq]
    exact densityNat
  have densityENN :
      (output.binnedAmbientPreliminary.card : ENNReal) *
          ((output.ancestryAuxiliary.auxiliaryFiber label).card :
            ENNReal) ≤
        (2 ^ (schedule.levelCount + 1) : ENNReal) *
          ((output.ancestryAuxiliaryCore.ambientCore ∩
            output.ancestryAuxiliary.auxiliaryFiber label).card :
            ENNReal) *
          fine.enncard := by
    have densityCast :
        ((output.binnedAmbientPreliminary.card *
          (output.ancestryAuxiliary.auxiliaryFiber label).card : ℕ) :
          ENNReal) ≤
        ((2 ^ (schedule.levelCount + 1) *
          (output.ancestryAuxiliaryCore.ambientCore ∩
            output.ancestryAuxiliary.auxiliaryFiber label).card *
          fine.card : ℕ) : ENNReal) := by
      exact_mod_cast densityNatAmbient
    simpa only [
      Kakeya.Streamlined.TubeFamily.enncard,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat
    ] using densityCast
  calc
    ((output.ancestryAuxiliary.auxiliaryFiber label).card : ENNReal) =
        (output.binnedAmbientPreliminary.card : ENNReal)⁻¹ *
          ((output.binnedAmbientPreliminary.card : ENNReal) *
            ((output.ancestryAuxiliary.auxiliaryFiber label).card :
              ENNReal)) := by
      rw [← mul_assoc,
        ENNReal.inv_mul_cancel selectedPos.ne' selectedTop, one_mul]
    _ ≤
        (output.binnedAmbientPreliminary.card : ENNReal)⁻¹ *
          ((2 ^ (schedule.levelCount + 1) : ENNReal) *
            ((output.ancestryAuxiliaryCore.ambientCore ∩
              output.ancestryAuxiliary.auxiliaryFiber label).card :
              ENNReal) *
            fine.enncard) := by
      gcongr
    _ =
        output.ancestryDensityLoss *
          ((output.ancestryAuxiliaryCore.ambientCore ∩
            output.ancestryAuxiliary.auxiliaryFiber label).card :
            ENNReal) := by
      simp only [ancestryDensityLoss]
      ring

theorem metricFiber_le_ancestryDensityLoss_core
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (parentCovers :
      ∀ coordinate source,
        WZ1PaperTubeCovers
          (fine.tube source)
          ((schedule.scaleData coordinate).coarse.tube
            ((schedule.scaleData coordinate).cover.parent source)))
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (parent : Fin output.metric.metricParents.card)
    (coreFiberNonempty :
      (output.ancestryAuxiliaryCore.pullback.pulledBack ∩
        wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents parent).Nonempty) :
    ((wz2PaperFullFiberIndices
      output.metric.selectedFine
      output.metric.metricParents parent).card : ENNReal) ≤
      output.ancestryDensityLoss *
        ((output.ancestryAuxiliaryCore.pullback.pulledBack ∩
          wz2PaperFullFiberIndices
            output.metric.selectedFine
            output.metric.metricParents parent).card :
          ENNReal) := by
  have coreImageEq :=
    output.coreMetricFiber_image_eq_ambientCoreAuxiliaryFiber
      rhoPos widthPos packetScaleLeRho sixWidthLe parentCovers
      allAncestryCoordinatesUpper parent
  have coreAmbientNonempty :
      (output.ancestryAuxiliaryCore.ambientCore ∩
        output.ancestryAuxiliary.auxiliaryFiber
          (output.metricParentLabel parent)).Nonempty := by
    rcases coreFiberNonempty with ⟨source, sourceMem⟩
    exact
      ⟨output.metric.mesh.complete.selectedFine.embedding source,
        by
          rw [← coreImageEq]
          exact
            Finset.mem_image.mpr
              ⟨source, sourceMem, rfl⟩⟩
  have ambientBound :=
    output.ambientAuxiliaryFiber_le_ancestryDensityLoss_core
      (output.metricParentLabel parent) coreAmbientNonempty
  have fiberImageEq :=
    output.packetAuxiliaryFiber_metricParentLabel_image_eq parent
  have packetFiberEq :=
    output.packetAuxiliaryFiber_metricParentLabel_eq_metricFiber
      rhoPos widthPos packetScaleLeRho sixWidthLe parentCovers
      allAncestryCoordinatesUpper parent
  have fiberCard :
      (wz2PaperFullFiberIndices
        output.metric.selectedFine
        output.metric.metricParents parent).card =
        (output.ancestryAuxiliary.auxiliaryFiber
          (output.metricParentLabel parent)).card := by
    rw [← packetFiberEq, ← fiberImageEq]
    exact
      (Finset.card_image_of_injective _
        output.metric.mesh.complete.selectedFine.embedding.injective).symm
  have coreCard :
      (output.ancestryAuxiliaryCore.pullback.pulledBack ∩
        wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents parent).card =
        (output.ancestryAuxiliaryCore.ambientCore ∩
          output.ancestryAuxiliary.auxiliaryFiber
            (output.metricParentLabel parent)).card := by
    rw [← coreImageEq]
    exact
      (Finset.card_image_of_injective _
        output.metric.mesh.complete.selectedFine.embedding.injective).symm
  rw [fiberCard, coreCard]
  exact ambientBound

theorem metricFiber_uniform_after_ancestryCore
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (parentCovers :
      ∀ coordinate source,
        WZ1PaperTubeCovers
          (fine.tube source)
          ((schedule.scaleData coordinate).coarse.tube
            ((schedule.scaleData coordinate).cover.parent source)))
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (baseConstant : ENNReal)
    (ambientUniform :
      ∀ first second,
        ((wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents first).card : ENNReal) ≤
          baseConstant *
            ((wz2PaperFullFiberIndices
              output.metric.selectedFine
              output.metric.metricParents second).card : ENNReal))
    (first second : Fin output.metric.metricParents.card)
    (secondCoreNonempty :
      (output.ancestryAuxiliaryCore.pullback.pulledBack ∩
        wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents second).Nonempty) :
    ((output.ancestryAuxiliaryCore.pullback.pulledBack ∩
      wz2PaperFullFiberIndices
        output.metric.selectedFine
        output.metric.metricParents first).card : ENNReal) ≤
      (baseConstant * output.ancestryDensityLoss) *
        ((output.ancestryAuxiliaryCore.pullback.pulledBack ∩
          wz2PaperFullFiberIndices
            output.metric.selectedFine
            output.metric.metricParents second).card : ENNReal) := by
  have firstLe :
      ((output.ancestryAuxiliaryCore.pullback.pulledBack ∩
        wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents first).card : ENNReal) ≤
        ((wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents first).card : ENNReal) := by
    exact_mod_cast
      Finset.card_le_card Finset.inter_subset_right
  have secondLower :=
    output.metricFiber_le_ancestryDensityLoss_core
      rhoPos widthPos packetScaleLeRho sixWidthLe parentCovers
      allAncestryCoordinatesUpper second secondCoreNonempty
  calc
    ((output.ancestryAuxiliaryCore.pullback.pulledBack ∩
      wz2PaperFullFiberIndices
        output.metric.selectedFine
        output.metric.metricParents first).card : ENNReal) ≤
        ((wz2PaperFullFiberIndices
          output.metric.selectedFine
          output.metric.metricParents first).card : ENNReal) :=
      firstLe
    _ ≤
        baseConstant *
          ((wz2PaperFullFiberIndices
            output.metric.selectedFine
            output.metric.metricParents second).card : ENNReal) :=
      ambientUniform first second
    _ ≤
        baseConstant *
          (output.ancestryDensityLoss *
            ((output.ancestryAuxiliaryCore.pullback.pulledBack ∩
              wz2PaperFullFiberIndices
                output.metric.selectedFine
                output.metric.metricParents second).card : ENNReal)) := by
      gcongr
    _ =
        (baseConstant * output.ancestryDensityLoss) *
          ((output.ancestryAuxiliaryCore.pullback.pulledBack ∩
            wz2PaperFullFiberIndices
              output.metric.selectedFine
              output.metric.metricParents second).card : ENNReal) := by
      ring

end PureWZ2Prop62AncestryMetricPreliminaryOutput

end Kakeya.Assouad

end
