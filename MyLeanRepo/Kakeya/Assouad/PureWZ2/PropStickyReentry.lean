import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureRescaledFiberWeakening

/-!
# Re-entry data for pure WZ2 Proposition 6.2

This module separates the loss-independent ordinary/cropped realization of an
exact Section-6 pair from the loss schedule used by one Proposition 6.2
invocation.

The conversion back to `PureWZ2CroppedCriticalNormalizationData` is
definition-preserving on the exact cropped family and shading.  It lets the
existing rich V4 pipeline consume either the root normalization or a later
coarse-output realization through one public input type.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
Increase the public loss while preserving the exact selected family, shading,
cover, and rescaled-fiber witnesses.
-/
noncomputable def PureWZ2PropStickyData.mono_loss
    {delta sigma firstLoss secondLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (data :
      PureWZ2PropStickyData
        (sigma := sigma) (outputLoss := firstLoss)
        sourceShading rho logExponent)
    (loss_le : firstLoss ≤ secondLoss) :
    PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := secondLoss)
      sourceShading rho logExponent := by
  have ratioPos : 0 < delta / rho.1 := by
    let parent : Fin data.coarse.card :=
      ⟨0, data.coarse_extremal.nonempty⟩
    rcases data.rescaledFiber parent with ⟨fiber⟩
    exact fiber.extremal.delta_pos
  have ratioLeOne : delta / rho.1 ≤ 1 :=
    (div_le_one data.coarse_extremal.delta_pos).mpr rho.2.1
  have coarsePower :
      Kakeya.realRpowENN rho.1 (2 - sigma - firstLoss) ≤
        Kakeya.realRpowENN rho.1 (2 - sigma - secondLoss) :=
    by
      apply ENNReal.ofReal_mono
      exact
        Real.rpow_le_rpow_of_exponent_ge
          data.coarse_extremal.delta_pos
          data.coarse_extremal.delta_le_one (by linarith)
  have fiberPower :
      Kakeya.realRpowENN (delta / rho.1)
          (2 - sigma - firstLoss) ≤
        Kakeya.realRpowENN (delta / rho.1)
          (2 - sigma - secondLoss) :=
    by
      apply ENNReal.ofReal_mono
      exact
        Real.rpow_le_rpow_of_exponent_ge
          ratioPos ratioLeOne (by linarith)
  exact
    {
      selected := data.selected
      selected_nonempty := data.selected_nonempty
      refined := data.refined
      subshading := data.subshading
      retained_mass := data.retained_mass
      refined_cubical := data.refined_cubical
      coarse := data.coarse
      cover := data.cover
      croppedCoarseShading := data.croppedCoarseShading
      balanced := data.balanced
      coarse_extremal := data.coarse_extremal.mono_loss loss_le
      rescaledFiber := fun parent =>
        Nonempty.map
          (fun fiber => fiber.mono_loss loss_le)
          (data.rescaledFiber parent)
      coarse_multiplicity_upper := by
        intro point
        exact
          (data.coarse_multiplicity_upper point).trans <| by
            gcongr
      fiber_multiplicity_upper := by
        intro parent point
        exact
          (data.fiber_multiplicity_upper parent point).trans <| by
            gcongr
    }

/--
Loss-independent ordinary provenance for one exact cropped Section-6 pair.

The ordinary source and its selected refinement are explicit.  The common
rigid frame and index equivalence identify the selected ordinary carriers with
the exact caller-supplied cropped family.  In particular,
`cropped_carrier_eq_dense_cubicalization` prevents a later kernel invocation
from replacing the caller's shading by an unrelated existential witness.
-/
structure PureWZ2PropStickyReentryGeometry
    {delta : ℝ}
    (ordinaryFamily : Kakeya.Streamlined.TubeFamily delta)
    (ordinaryShading : Kakeya.Streamlined.TubeShading ordinaryFamily)
    (croppedFamily : Kakeya.Streamlined.TubeFamily delta)
    (croppedShading : WZ1PaperTubeShading croppedFamily)
    (normalizationExponent : ℕ) where
  selected : Kakeya.Streamlined.TubeSubfamily ordinaryFamily
  selected_nonempty : selected.family.Nonempty
  ordinaryRefined : Kakeya.Streamlined.TubeShading selected.family
  ordinary_subshading :
    ∀ index,
      ordinaryRefined.carrier index ⊆
        ordinaryShading.carrier (selected.embedding index)
  retained_mass :
    wz2PaperPureRefinementFraction delta normalizationExponent *
        ordinaryShading.mass ≤
      ordinaryRefined.mass
  frame : Point3 ≃ᵃⁱ[ℝ] Point3
  indexEquiv : Fin selected.family.card ≃ Fin croppedFamily.card
  ordinary_carrier_image_eq :
    ∀ index,
      (croppedFamily.tube (indexEquiv index)).carrier =
        frame '' (selected.family.tube index).carrier
  ordinaryDensity : ENNReal
  ordinaryDensity_pos : 0 < ordinaryDensity
  ordinary_per_tube :
    ∀ index,
      ordinaryDensity *
            volume (selected.family.tube index).carrier ≤
        volume (ordinaryRefined.carrier index)
  ordinary_axial_window :
    ∀ index point,
      point ∈ frame '' ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 4
  cropped_carrier_eq_dense_cubicalization :
    ∀ index,
      croppedShading.carrier (indexEquiv index) =
        pureWZ2DenseCubicalization
          (croppedFamily.tube (indexEquiv index))
          (frame '' ordinaryRefined.carrier index)
  cropped_cubical : WZ1PaperIsCubicalShading croppedShading
  line_class : WZ1PaperIsLineClass croppedFamily
  ordinary_cell_containment :
    ∀ index (cell : ℤ × ℤ × ℤ),
      ((frame '' ordinaryRefined.carrier index) ∩
          wz1PaperGridCube delta cell).Nonempty →
        wz1PaperGridCube delta cell ⊆
          wz1PaperTubeCarrier
            (croppedFamily.tube (indexEquiv index))
  ordinary_bounded_base : HasBoundedBase croppedFamily 4

/--
One loss schedule and its extremality proofs on top of exact re-entry
geometry.

Both losses are selected before runtime family/scale data in the public
kernel.  The strict half-gap is the schedule invariant used by the current
complete-fiber normalization route.
-/
structure PureWZ2PropStickyReentryData
    {sigma delta : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    (croppedShading : WZ1PaperTubeShading croppedFamily)
    (normalizationExponent : ℕ)
    (sourceLoss normalizationLoss : ℝ) where
  sourceLoss_pos : 0 < sourceLoss
  normalizationLoss_pos : 0 < normalizationLoss
  sourceLoss_le_half : sourceLoss ≤ normalizationLoss / 2
  ordinarySource :
    PureWZ2ExtremalConfiguration sigma sourceLoss delta
  geometry :
    PureWZ2PropStickyReentryGeometry
      ordinarySource.family ordinarySource.shading
      croppedFamily croppedShading normalizationExponent
  ordinary_density_budget :
    Kakeya.realRpowENN delta sourceLoss / 2 ≤ geometry.ordinaryDensity
  cropped_top_level_cwa :
    WZ2PaperConvexWolffBound
      croppedFamily
      (Kakeya.realRpowENN delta (-normalizationLoss))
  cropped_extremal :
    WZ2PaperCroppedIsExtremal
      sigma normalizationLoss croppedFamily croppedShading

namespace PureWZ2PropStickyReentryData

variable
    {sigma delta : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {normalizationExponent : ℕ}
    {sourceLoss normalizationLoss : ℝ}
    (reentry :
      PureWZ2PropStickyReentryData
        (sigma := sigma) croppedShading normalizationExponent
        sourceLoss normalizationLoss)

/--
Recover the exact normalization input consumed by the existing rich V4
pipeline.  No family, shading, frame, or index is selected here.
-/
noncomputable def toNormalizationData :
    PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss)
      reentry.ordinarySource normalizationExponent where
  input_loss_le_half := reentry.sourceLoss_le_half
  selected := reentry.geometry.selected
  selected_nonempty := reentry.geometry.selected_nonempty
  ordinaryRefined := reentry.geometry.ordinaryRefined
  ordinary_subshading := reentry.geometry.ordinary_subshading
  retained_mass := reentry.geometry.retained_mass
  frame := reentry.geometry.frame
  croppedFamily := croppedFamily
  indexEquiv := reentry.geometry.indexEquiv
  ordinary_carrier_image_eq :=
    reentry.geometry.ordinary_carrier_image_eq
  ordinary_per_tube := by
    intro index
    calc
      (Kakeya.realRpowENN delta sourceLoss / 2) *
            volume (reentry.geometry.selected.family.tube index).carrier ≤
          reentry.geometry.ordinaryDensity *
            volume (reentry.geometry.selected.family.tube index).carrier :=
        mul_le_mul_left reentry.ordinary_density_budget _
      _ ≤
          volume (reentry.geometry.ordinaryRefined.carrier index) :=
        reentry.geometry.ordinary_per_tube index
  ordinary_axial_window := reentry.geometry.ordinary_axial_window
  croppedRefined := croppedShading
  cropped_carrier_eq_dense_cubicalization :=
    reentry.geometry.cropped_carrier_eq_dense_cubicalization
  cropped_cubical := reentry.geometry.cropped_cubical
  line_class := reentry.geometry.line_class
  cropped_top_level_cwa := reentry.cropped_top_level_cwa
  final_extremal := reentry.cropped_extremal
  ordinary_cell_containment :=
    reentry.geometry.ordinary_cell_containment
  ordinary_bounded_base := reentry.geometry.ordinary_bounded_base

/--
Retarget one exact re-entry pair to weaker source and normalization losses.
The ordinary family, cropped family, shading, rigid frame, and all provenance
are definitionally unchanged.
-/
noncomputable def mono_losses
    {nextSourceLoss nextNormalizationLoss : ℝ}
    (sourceLoss_le : sourceLoss ≤ nextSourceLoss)
    (normalizationLoss_le : normalizationLoss ≤ nextNormalizationLoss)
    (nextSourceLoss_pos : 0 < nextSourceLoss)
    (nextNormalizationLoss_pos : 0 < nextNormalizationLoss)
    (nextSourceLoss_le_half :
      nextSourceLoss ≤ nextNormalizationLoss / 2) :
    PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      nextSourceLoss nextNormalizationLoss where
  sourceLoss_pos := nextSourceLoss_pos
  normalizationLoss_pos := nextNormalizationLoss_pos
  sourceLoss_le_half := nextSourceLoss_le_half
  ordinarySource :=
    {
      family := reentry.ordinarySource.family
      shading := reentry.ordinarySource.shading
      extremal :=
        reentry.ordinarySource.extremal.mono_loss sourceLoss_le
    }
  geometry := reentry.geometry
  ordinary_density_budget := by
    have densityPower :
        Kakeya.realRpowENN delta nextSourceLoss ≤
          Kakeya.realRpowENN delta sourceLoss := by
      apply ENNReal.ofReal_mono
      exact
        Real.rpow_le_rpow_of_exponent_ge
          reentry.cropped_extremal.delta_pos
          reentry.cropped_extremal.delta_le_one sourceLoss_le
    calc
      Kakeya.realRpowENN delta nextSourceLoss / 2 ≤
          Kakeya.realRpowENN delta sourceLoss / 2 := by
        gcongr
      _ ≤ reentry.geometry.ordinaryDensity :=
        reentry.ordinary_density_budget
  cropped_top_level_cwa := by
    intro convexSet convex
    have constantPower :
        Kakeya.realRpowENN delta (-normalizationLoss) ≤
          Kakeya.realRpowENN delta (-nextNormalizationLoss) := by
      apply ENNReal.ofReal_mono
      exact
        Real.rpow_le_rpow_of_exponent_ge
          reentry.cropped_extremal.delta_pos
          reentry.cropped_extremal.delta_le_one (by linarith)
    exact
      (reentry.cropped_top_level_cwa convexSet convex).trans <| by
        gcongr
  cropped_extremal :=
    reentry.cropped_extremal.mono_loss normalizationLoss_le

end PureWZ2PropStickyReentryData

namespace PureWZ2CroppedCriticalNormalizationData

variable
    {sigma sourceLoss normalizationLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent)

/--
Project an existing normalization to the public re-entry input without
rebuilding the complete-fiber normalization.
-/
noncomputable def toPropStickyReentryData :
    0 < sourceLoss →
    0 < normalizationLoss →
    PureWZ2PropStickyReentryData
      (sigma := sigma) normalized.croppedRefined normalizationExponent
      sourceLoss normalizationLoss :=
  fun sourceLossPos normalizationLossPos =>
  {
  sourceLoss_pos := sourceLossPos
  normalizationLoss_pos := normalizationLossPos
  sourceLoss_le_half := normalized.input_loss_le_half
  ordinarySource := source
  geometry :=
    {
      selected := normalized.selected
      selected_nonempty := normalized.selected_nonempty
      ordinaryRefined := normalized.ordinaryRefined
      ordinary_subshading := normalized.ordinary_subshading
      retained_mass := normalized.retained_mass
      frame := normalized.frame
      indexEquiv := normalized.indexEquiv
      ordinary_carrier_image_eq :=
        normalized.ordinary_carrier_image_eq
      ordinaryDensity := Kakeya.realRpowENN delta sourceLoss / 2
      ordinaryDensity_pos := by
        apply ENNReal.div_pos
        · simp [Kakeya.realRpowENN,
            Real.rpow_pos_of_pos normalized.final_extremal.delta_pos]
        · norm_num
      ordinary_per_tube := normalized.ordinary_per_tube
      ordinary_axial_window := normalized.ordinary_axial_window
      cropped_carrier_eq_dense_cubicalization :=
        normalized.cropped_carrier_eq_dense_cubicalization
      cropped_cubical := normalized.cropped_cubical
      line_class := normalized.line_class
      ordinary_cell_containment :=
        normalized.ordinary_cell_containment
      ordinary_bounded_base := normalized.ordinary_bounded_base
    }
  ordinary_density_budget := le_rfl
  cropped_top_level_cwa := normalized.cropped_top_level_cwa
  cropped_extremal := normalized.final_extremal
  }

end PureWZ2CroppedCriticalNormalizationData

/--
The ordinary Proposition 6.2 output together with a re-entry certificate
indexed definitionally by its exact coarse family and exact cropped coarse
shading.
-/
structure PureWZ2ReentrantPropStickyData
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : WZ1PaperTubeShading source)
    (rho : WZ2PaperRequestedScale delta)
    (normalizationExponent logExponent : ℕ) where
  data :
    PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent
  coarseSourceLoss : ℝ
  coarseNormalizationLoss : ℝ
  coarseSourceLoss_pos : 0 < coarseSourceLoss
  coarseNormalizationLoss_pos : 0 < coarseNormalizationLoss
  coarseSourceLoss_budget : 3 * coarseSourceLoss ≤ outputLoss
  coarseNormalizationLoss_eq :
    coarseNormalizationLoss = (7 / 2 : ℝ) * coarseSourceLoss
  coarseReentry :
    PureWZ2PropStickyReentryData
      (sigma := sigma)
      data.croppedCoarseShading normalizationExponent
      coarseSourceLoss coarseNormalizationLoss

/--
One loss schedule and uniform threshold selected by the public re-entry
kernel.  Internal fixed-grid and tree-cleanup dependencies are already closed
before this value is exposed.
-/
structure PureWZ2PropStickyReentryKernelScheduleData
    {sigma outputLoss : ℝ}
    (normalizationExponent logExponent : ℕ) where
  sourceLoss : ℝ
  normalizationLoss : ℝ
  delta₀ : ℝ
  sourceLoss_pos : 0 < sourceLoss
  normalizationLoss_pos : 0 < normalizationLoss
  sourceLoss_le_half : sourceLoss ≤ normalizationLoss / 2
  normalizationLoss_lt_output : normalizationLoss < outputLoss
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  run :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      ∀ (croppedFamily :
          Kakeya.Streamlined.TubeFamily delta),
        ∀ (croppedShading : WZ1PaperTubeShading croppedFamily),
          ∀ _reentry :
              PureWZ2PropStickyReentryData
                (sigma := sigma)
                croppedShading normalizationExponent
                sourceLoss normalizationLoss,
            ∀ rho : WZ2PaperRequestedScale delta,
              Real.rpow delta (1 - outputLoss) ≤ rho.1 →
              rho.1 ≤ Real.rpow delta outputLoss →
                Nonempty
                  (PureWZ2PropStickyData
                    (sigma := sigma)
                    (outputLoss := outputLoss)
                    croppedShading rho logExponent)
  /--
  The rich finite-chain entry point.  It returns exact output-coarse re-entry
  provenance when the transported ordinary input satisfies the stronger
  root `1/8` axial window required by the V4 core.
  -/
  runReentrant :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      ∀ (croppedFamily :
          Kakeya.Streamlined.TubeFamily delta),
        ∀ (croppedShading : WZ1PaperTubeShading croppedFamily),
          ∀ reentry :
              PureWZ2PropStickyReentryData
                (sigma := sigma)
                croppedShading normalizationExponent
                sourceLoss normalizationLoss,
            (∀ index point,
              point ∈
                  reentry.geometry.frame ''
                    reentry.geometry.ordinaryRefined.carrier index →
                |point (2 : Fin 3)| ≤ 1 / 8) →
              ∀ rho : WZ2PaperRequestedScale delta,
                Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                rho.1 ≤ Real.rpow delta outputLoss →
                  Nonempty
                    (PureWZ2ReentrantPropStickyData
                      (sigma := sigma)
                      (outputLoss := outputLoss)
                      croppedShading rho
                      normalizationExponent logExponent)

/--
The public reusable Proposition 6.2 capability.  It retains the mathematical
critical package as a caller input while hiding the Node 3 implementation
oracles.
-/
def PureWZ2PropStickyReentryKernelAt
    (normalizationExponent logExponent : ℕ) : Prop :=
  ∀ sigma : ℝ,
    PureWZ2CriticalPackage sigma →
      ∀ outputLoss : ℝ,
        0 < outputLoss → outputLoss ≤ 1 →
          Nonempty
            (PureWZ2PropStickyReentryKernelScheduleData
              (sigma := sigma) (outputLoss := outputLoss)
              normalizationExponent logExponent)

/--
A finite two-call schedule.  The first call is deliberately run at the
second kernel's source loss, so every native first-coarse certificate can be
weakened to the exact second-call indices.
-/
structure PureWZ2PropStickyTwoCallLossSchedule
    {sigma secondOutputLoss : ℝ}
    (normalizationExponent logExponent : ℕ) where
  kernel :
    PureWZ2PropStickyReentryKernelScheduleData
      (sigma := sigma) (outputLoss := secondOutputLoss)
      normalizationExponent logExponent
  firstOutputLoss : ℝ
  firstOutputLoss_eq : firstOutputLoss = kernel.sourceLoss
  firstOutputLoss_pos : 0 < firstOutputLoss
  rootScaleCeiling : ℝ
  rootScaleCeiling_eq : rootScaleCeiling = kernel.delta₀ ^ 2
  rootScaleCeiling_pos : 0 < rootScaleCeiling

namespace PureWZ2PropStickyReentryKernelScheduleData

variable
    {sigma outputLoss : ℝ}
    {normalizationExponent logExponent : ℕ}
    (schedule :
      PureWZ2PropStickyReentryKernelScheduleData
        (sigma := sigma) (outputLoss := outputLoss)
        normalizationExponent logExponent)

/-- Turn one public kernel schedule into the pre-runtime finite two-call schedule. -/
noncomputable def toTwoCallLossSchedule :
    PureWZ2PropStickyTwoCallLossSchedule
      (sigma := sigma) (secondOutputLoss := outputLoss)
      normalizationExponent logExponent where
  kernel := schedule
  firstOutputLoss := schedule.sourceLoss
  firstOutputLoss_eq := rfl
  firstOutputLoss_pos := schedule.sourceLoss_pos
  rootScaleCeiling := schedule.delta₀ ^ 2
  rootScaleCeiling_eq := rfl
  rootScaleCeiling_pos := sq_pos_of_pos schedule.delta₀_pos

end PureWZ2PropStickyReentryKernelScheduleData

namespace PureWZ2ReentrantPropStickyData

variable
    {delta sigma secondOutputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent logExponent : ℕ}
    (schedule :
      PureWZ2PropStickyTwoCallLossSchedule
        (sigma := sigma) (secondOutputLoss := secondOutputLoss)
        normalizationExponent logExponent)
    (first :
      PureWZ2ReentrantPropStickyData
        (sigma := sigma) (outputLoss := schedule.firstOutputLoss)
        sourceShading rho normalizationExponent logExponent)

/--
Retarget the first call's exact coarse certificate to the precise loss
indices selected by the second kernel.
-/
noncomputable def reentryForNext :
    PureWZ2PropStickyReentryData
      (sigma := sigma)
      first.data.croppedCoarseShading normalizationExponent
      schedule.kernel.sourceLoss schedule.kernel.normalizationLoss :=
  first.coarseReentry.mono_losses
    (by
      rw [← schedule.firstOutputLoss_eq]
      linarith [
        first.coarseSourceLoss_budget,
        first.coarseSourceLoss_pos])
    (by
      rw [first.coarseNormalizationLoss_eq]
      linarith [
        first.coarseSourceLoss_budget,
        schedule.firstOutputLoss_eq,
        schedule.kernel.sourceLoss_le_half,
        first.coarseSourceLoss_pos,
        schedule.kernel.normalizationLoss_pos])
    schedule.kernel.sourceLoss_pos
    schedule.kernel.normalizationLoss_pos
    schedule.kernel.sourceLoss_le_half

end PureWZ2ReentrantPropStickyData

/--
The existing synchronized root realization together with its exact re-entry
input.  The wrapper does not rerun normalization.
-/
structure PureWZ2PropStickyReentrantRootRealizationData
    {sigma outputLoss scaleCeiling : ℝ}
    (normalizationExponent logExponent : ℕ) where
  realization :
    PureWZ2PropStickyRealizationData
      (sigma := sigma)
      (outputLoss := outputLoss)
      (scaleCeiling := scaleCeiling)
      normalizationExponent logExponent
  rootReentry :
    PureWZ2PropStickyReentryData
      (sigma := sigma)
      realization.normalized.croppedRefined normalizationExponent
      realization.sourceLoss realization.normalizationLoss
  reentrantOutput :
    ∀ rho : WZ2PaperRequestedScale realization.delta,
      Real.rpow realization.delta (1 - realization.continuationLoss) ≤ rho.1 →
      rho.1 ≤ Real.rpow realization.delta realization.continuationLoss →
        Nonempty
          (PureWZ2ReentrantPropStickyData
            (sigma := sigma)
            (outputLoss := outputLoss)
            realization.normalized.croppedRefined rho
            normalizationExponent logExponent)
  realizedReentrantOutput :
    Nonempty
      (PureWZ2ReentrantPropStickyData
        (sigma := sigma)
        (outputLoss := outputLoss)
        realization.normalized.croppedRefined realization.realizedRho
        normalizationExponent logExponent)

/--
At every requested smallness threshold, the root realization exposes the
exact re-entry object consumed by the reusable kernel.
-/
def PureWZ2PropStickyReentrantRootRealizationAt
    (normalizationExponent logExponent : ℕ) : Prop :=
  ∀ sigma : ℝ,
    PureWZ2CriticalPackage sigma →
      ∀ outputLoss scaleCeiling : ℝ,
        0 < outputLoss → 0 < scaleCeiling →
          Nonempty
            (PureWZ2PropStickyReentrantRootRealizationData
              (sigma := sigma)
              (outputLoss := outputLoss)
              (scaleCeiling := scaleCeiling)
              normalizationExponent logExponent)

/--
The single public Node 3 capability consumed by the serial Node 3 → 4 → 5
chain.  All fields use the same normalization and logarithmic exponents.
-/
structure PureWZ2PropStickyCapability where
  normalizationExponent : ℕ
  logExponent : ℕ
  normalization :
    PureWZ2CroppedCriticalNormalizationAt normalizationExponent
  continuation :
    PureWZ2CroppedPropStickyAt normalizationExponent logExponent
  realization :
    PureWZ2PropStickyRealizationAt normalizationExponent logExponent
  rootReentrant :
    PureWZ2PropStickyReentrantRootRealizationAt
      normalizationExponent logExponent
  kernel :
    PureWZ2PropStickyReentryKernelAt
      normalizationExponent logExponent

namespace PureWZ2PropStickyCapability

/-- Forget the re-entry fields and recover the historical Node 3 output. -/
theorem toLegacyFromCritical
    (capability : PureWZ2PropStickyCapability) :
    PureWZ2PropStickyFromCriticalStatement :=
  ⟨capability.normalizationExponent, capability.logExponent,
    capability.normalization, capability.continuation,
    capability.realization⟩

end PureWZ2PropStickyCapability

/-- Node 3 in the serial heavy-task chain, with one unified public capability. -/
def PureWZ2PropStickyStatement : Prop :=
  PureWZ2SubunitPackageStatement →
    PureWZ2CriticalExtractionStatement →
      Nonempty PureWZ2PropStickyCapability

end Kakeya.Assouad

end
