import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TreePureSchedule
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12AlignedExactSource
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryNestedScaleInputs

/-!
# Proposition 6.2: produce the old simultaneous pure schedule

This is the formal counterpart of the first sentence in the metric-parent
proof:

> Run the construction in the proof of Lemma 2.13 once.

The caller-rooted historical schedule already stores one simultaneous nested
family of exact-scale covers.  The aligned exact source supplies the pure
actual-John witness attached to each of those same canonical historical
choices.  This module combines them into `PureWZ2Prop62PureSchedule`.

No new cover is selected here.  Every pure coordinate remains synchronized
with the corresponding historical line cover.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private theorem pureWZ2_prop62_aligned_parent_eq_iff
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {pureCoarse internalCoarse :
      Kakeya.Streamlined.TubeFamily rho}
    {pureCover :
      WZ2PaperPurePartitioningCover fine pureCoarse}
    {internalCover :
      WZ2PaperPartitioningCover fine internalCoarse}
    (synchronization :
      WZ2PaperPureInternalCoverSynchronization
        fine internalCoarse internalCover)
    (coarse_eq : pureCoarse = internalCoarse)
    (cover_eq :
      HEq pureCover synchronization.publicCover)
    (first second : Fin fine.card) :
    pureCover.parent first = pureCover.parent second ↔
      internalCover.parent first = internalCover.parent second := by
  subst internalCoarse
  rw [heq_iff_eq] at cover_eq
  rw [cover_eq, synchronization.parent_eq first,
    synchronization.parent_eq second]

/--
The old pure schedule obtained from one caller-rooted synchronized Lemma 2.13
schedule.
-/
noncomputable def
    WZ2PaperAlignedPureExactSource.toProp62PureSchedule
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {outputConstant : ENNReal}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    (aligned :
      WZ2PaperAlignedPureExactSource
        sigma loss family shading)
    (historical :
      WZ2PaperCallerRootedSynchronizedScheduleData
        (Kakeya.realRpowENN delta (-loss))
        outputConstant caller
        aligned.sourceData.internalData.cwa_exact_scales)
    (outputFinite :
      WZ2PaperFiniteErrorConstant outputConstant) :
    PureWZ2Prop62PureSchedule
      family
      (Kakeya.realRpowENN delta (-loss))
      outputConstant := by
  let nested := historical.nestedSchedule
  let alignedScale :
      ∀ coordinate : Fin nested.scaleCount,
        WZ2PaperAlignedPureScheduleScaleData
          historical coordinate :=
    fun coordinate =>
      aligned.scheduleScaleData historical coordinate
  let scaleData :
      ∀ coordinate : Fin nested.scaleCount,
        WZ2PaperPureScaleCoverData
          family (nested.scale coordinate).1
          (Kakeya.realRpowENN delta (-loss)) :=
    fun coordinate => (alignedScale coordinate).pureScale
  let synchronization :
      ∀ coordinate : Fin nested.scaleCount,
        WZ2PaperPureInternalCoverSynchronization
          family
          (nested.scaleData coordinate).coarse
          (nested.scaleData coordinate).cover :=
    fun coordinate =>
      historical.coordinateSynchronization
        (fun rho =>
          aligned.sourceData.canonicalScaleSynchronization rho)
        coordinate
  exact
    {
      ambient_finite := aligned.sourceData.public_cwa.2.1
      scaleWindow_finite := outputFinite
      fine_distinct := aligned.sourceData.public_cwa.2.2.1
      levelCount := nested.scaleCount
      levelCount_pos := nested.scaleCount_pos
      actualScale := fun coordinate =>
        (nested.scale coordinate).1
      delta_le_actualScale := fun coordinate =>
        (nested.scale coordinate).2.1
      actualScale_antitone := by
        intro first second firstLeSecond
        exact nested.scale_antitone first second firstLeSecond
      scaleData := scaleData
      coarse_line_class := by
        intro coordinate
        have coarseEq :=
          (alignedScale coordinate).coarse_eq
        rw [coarseEq]
        exact
          (nested.scaleData coordinate).coarse_line_class
      parent_covers := by
        intro coordinate source
        let internalScale :=
          nested.scaleData coordinate
        exact
          (scaleData coordinate).parent_covers_of_internalSynchronization
            internalScale (synchronization coordinate)
            (alignedScale coordinate).coarse_eq
            (alignedScale coordinate).cover_eq source
      parent_nested := by
        intro level hnext first second hparent
        let fineCoordinate : Fin nested.scaleCount :=
          ⟨level, Nat.lt_of_succ_lt hnext⟩
        let coarseCoordinate : Fin nested.scaleCount :=
          ⟨level + 1, hnext⟩
        have internalCoarseParent :
            (nested.scaleData coarseCoordinate).cover.parent first =
              (nested.scaleData coarseCoordinate).cover.parent second :=
          (pureWZ2_prop62_aligned_parent_eq_iff
            (synchronization coarseCoordinate)
            (alignedScale coarseCoordinate).coarse_eq
            (alignedScale coarseCoordinate).cover_eq
            first second).mp hparent
        have internalFineParent :
            (nested.scaleData fineCoordinate).cover.parent first =
              (nested.scaleData fineCoordinate).cover.parent second :=
          nested.parent_nested level hnext first second
            internalCoarseParent
        exact
          (pureWZ2_prop62_aligned_parent_eq_iff
            (synchronization fineCoordinate)
            (alignedScale fineCoordinate).coarse_eq
            (alignedScale fineCoordinate).cover_eq
            first second).mpr internalFineParent
      rounding := by
        intro requested
        let coordinate := nested.representative requested
        exact
          ⟨coordinate, nested.requested_le requested,
            nested.within_output requested⟩
    }

namespace WZ2PaperAlignedPureExactSource

variable
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {outputConstant : ENNReal}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    (aligned :
      WZ2PaperAlignedPureExactSource
        sigma loss family shading)
    (historical :
      WZ2PaperCallerRootedSynchronizedScheduleData
        (Kakeya.realRpowENN delta (-loss))
        outputConstant caller
        aligned.sourceData.internalData.cwa_exact_scales)
    (outputFinite :
      WZ2PaperFiniteErrorConstant outputConstant)

abbrev prop62PureSchedule :
    PureWZ2Prop62PureSchedule
      family
      (Kakeya.realRpowENN delta (-loss))
      outputConstant :=
  aligned.toProp62PureSchedule historical outputFinite

@[simp] theorem prop62PureSchedule_levelCount :
    (aligned.prop62PureSchedule historical outputFinite).levelCount =
      historical.nestedSchedule.scaleCount := by
  rfl

@[simp] theorem prop62PureSchedule_actualScale
    (coordinate :
      Fin (aligned.prop62PureSchedule
        historical outputFinite).levelCount) :
    (aligned.prop62PureSchedule historical outputFinite).actualScale
        coordinate =
      (historical.nestedSchedule.scale coordinate).1 := by
  rfl

theorem prop62PureSchedule_scaleData_eq
    (coordinate :
      Fin (aligned.prop62PureSchedule
        historical outputFinite).levelCount) :
    HEq
      ((aligned.prop62PureSchedule
        historical outputFinite).scaleData coordinate)
      (aligned.scheduleScaleData historical coordinate).pureScale := by
  exact HEq.rfl

theorem prop62PureSchedule_coarse_eq
    (coordinate :
      Fin (aligned.prop62PureSchedule
        historical outputFinite).levelCount) :
    ((aligned.prop62PureSchedule
      historical outputFinite).scaleData coordinate).coarse =
      (historical.nestedSchedule.scaleData coordinate).coarse :=
  (aligned.scheduleScaleData historical coordinate).coarse_eq

theorem prop62PureSchedule_cover_eq
    (coordinate :
      Fin (aligned.prop62PureSchedule
        historical outputFinite).levelCount) :
    HEq
      ((aligned.prop62PureSchedule
        historical outputFinite).scaleData coordinate).cover
      ((historical.coordinateSynchronization
        (fun rho =>
          aligned.sourceData.canonicalScaleSynchronization rho)
        coordinate).publicCover) :=
  (aligned.scheduleScaleData historical coordinate).cover_eq

/--
The pure parent at every old schedule coordinate is strictly line-covered by
the same historical parent.  This is the synchronized geometry later
restricted to one final metric fiber.
-/
theorem prop62PureSchedule_parent_covers
    (coordinate :
      Fin (aligned.prop62PureSchedule
        historical outputFinite).levelCount) :
    ∀ source,
      WZ1PaperTubeCovers
        (family.tube source)
        (((aligned.prop62PureSchedule
          historical outputFinite).scaleData coordinate).coarse.tube
          (((aligned.prop62PureSchedule
            historical outputFinite).scaleData coordinate).cover.parent
            source)) := by
  let internalScale :=
    historical.nestedSchedule.scaleData coordinate
  let synchronization :=
    historical.coordinateSynchronization
      (fun rho =>
        aligned.sourceData.canonicalScaleSynchronization rho)
      coordinate
  exact
    ((aligned.prop62PureSchedule
        historical outputFinite).scaleData coordinate)
      |>.parent_covers_of_internalSynchronization
        internalScale synchronization
        (aligned.prop62PureSchedule_coarse_eq
          historical outputFinite coordinate)
        (aligned.prop62PureSchedule_cover_eq
          historical outputFinite coordinate)

end WZ2PaperAlignedPureExactSource

end Kakeya.Assouad

end
