import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentRestrictedScheduleStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyCallerFiberScale
import MyLeanRepo.Kakeya.Assouad.PropStickySelectedScaleCover
import MyLeanRepo.Kakeya.Assouad.PropStickyWeakening

/-! # Restrict the caller-fiber strict schedule to one selected family -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_prop_sticky_prepared_one_parent_restricted_schedule :
    WZ2PropStickyPreparedOneParentRestrictedScheduleStatement := by
  intro delta sourceLoss stableLoss source shading caller
    preparationExponent prepared parent selection
    quantitative outputConstant hAbsorb
  let callerFiber :=
    wz2PaperPreparedOneParentFiber prepared parent
  let selected := selection.refinement.selected
  let callerFiberData :
      ∀ coordinate :
          Fin (wz2PaperPreparedOneParentFineScaleCount
            prepared parent),
        WZ2PaperCallerFiberScaleData
          prepared parent
            (wz2PaperPreparedOneParentFineCoordinate
              prepared parent coordinate) :=
    fun coordinate =>
      selection.branch.callerFiberData
        (wz2PaperPreparedOneParentFineCoordinate
          prepared parent coordinate)
        (wz2PaperPreparedOneParentFineCoordinate_le
          prepared parent coordinate)
  let scaleData :
      ∀ coordinate :
          Fin (wz2PaperPreparedOneParentFineScaleCount
            prepared parent),
        WZ2PaperScaleCoverData
          selected.family
          (prepared.strictScale
            (wz2PaperPreparedOneParentFineCoordinate
              prepared parent coordinate))
          outputConstant :=
    fun coordinate => by
      let restricted :=
        (callerFiberData coordinate).scaleData
          |>.restrictToSelectedHitParents
          selected quantitative.weight_ne_zero
          quantitative.weight_ne_top quantitative.global_retention
          (by
            intro first second
            have h :=
              quantitative.selected_uniform
                coordinate first second
            simpa [selected, callerFiberData] using h)
      exact restricted.mono hAbsorb
  exact
    ⟨{
      callerFiberData := callerFiberData
      scaleData := scaleData
      coarse_eq := by
        intro coordinate
        rfl
      cover_eq := by
        intro coordinate
        exact HEq.rfl
      coarse_strongly_separated := by
        intro coordinate first second hne
        let ambient := callerFiberData coordinate
        let hitCoarse :=
          ambient.scaleData.cover.hitParentSubfamily selected
        have hambientNe :
            hitCoarse.embedding first ≠
              hitCoarse.embedding second :=
          hitCoarse.embedding.injective.ne hne
        change
          wz2PaperLiteralSourceSeparationFactor *
                (prepared.strictScale
                  (wz2PaperPreparedOneParentFineCoordinate
                    prepared parent coordinate)).1 <
            wz1PaperLineDistance
              (hitCoarse.family.tube first)
              (hitCoarse.family.tube second)
        simpa only [hitCoarse.tube_eq] using
          ambient.coarse_strongly_separated
            (hitCoarse.embedding first)
            (hitCoarse.embedding second)
            hambientNe
    }⟩

end Kakeya.Assouad

end
