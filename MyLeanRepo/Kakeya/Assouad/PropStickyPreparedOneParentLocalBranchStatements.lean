import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentBranchStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyCallerFiberScaleStatements

/-!
# Nested branch selection on the caller-fiber local parent tree

For coordinates below the caller level, the caller fiber has one trivial
parent.  From the caller level toward finer scales, use the exact restricted
caller-fiber scale witnesses.  These parent maps form one nested tree, so the
weighted lower regularizer loses only `2 ^ strictScaleCount`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

def wz2PaperPreparedOneParentFineScaleCount
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (_parent : Fin prepared.callerStrict.coarse.card) : ℕ :=
  prepared.strictScaleCount - prepared.callerLevel.val

def wz2PaperPreparedOneParentFineCoordinate
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (parent : Fin prepared.callerStrict.coarse.card)
    (coordinate :
      Fin (wz2PaperPreparedOneParentFineScaleCount prepared parent)) :
    Fin prepared.strictScaleCount :=
  ⟨prepared.callerLevel.val + coordinate.val, by
    have hcaller := prepared.callerLevel.isLt
    have hcoordinate := coordinate.isLt
    dsimp only [wz2PaperPreparedOneParentFineScaleCount] at hcoordinate
    omega⟩

theorem wz2PaperPreparedOneParentFineCoordinate_le
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (parent : Fin prepared.callerStrict.coarse.card)
    (coordinate :
      Fin (wz2PaperPreparedOneParentFineScaleCount prepared parent)) :
    prepared.callerLevel.val ≤
      (wz2PaperPreparedOneParentFineCoordinate
        prepared parent coordinate).val := by
  dsimp only [wz2PaperPreparedOneParentFineCoordinate]
  omega

def WZ2PaperPreparedOneParentLocalParent
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (parent : Fin prepared.callerStrict.coarse.card)
    (callerFiberData :
      ∀ coordinate,
        prepared.callerLevel.val ≤ coordinate.val →
          WZ2PaperCallerFiberScaleData
            prepared parent coordinate)
    (coordinate :
      Fin (wz2PaperPreparedOneParentFineScaleCount prepared parent)) : Type :=
  Fin
    (callerFiberData
      (wz2PaperPreparedOneParentFineCoordinate
        prepared parent coordinate)
      (wz2PaperPreparedOneParentFineCoordinate_le
        prepared parent coordinate)).scaleData.coarse.card

noncomputable instance
    wz2PaperPreparedOneParentLocalParentFintype
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (parent : Fin prepared.callerStrict.coarse.card)
    (callerFiberData :
      ∀ coordinate,
        prepared.callerLevel.val ≤ coordinate.val →
          WZ2PaperCallerFiberScaleData
            prepared parent coordinate)
    (coordinate :
      Fin (wz2PaperPreparedOneParentFineScaleCount prepared parent)) :
    Fintype
      (WZ2PaperPreparedOneParentLocalParent
        prepared parent callerFiberData coordinate) := by
  unfold WZ2PaperPreparedOneParentLocalParent
  infer_instance

noncomputable instance
    wz2PaperPreparedOneParentLocalParentDecidableEq
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (parent : Fin prepared.callerStrict.coarse.card)
    (callerFiberData :
      ∀ coordinate,
        prepared.callerLevel.val ≤ coordinate.val →
          WZ2PaperCallerFiberScaleData
            prepared parent coordinate)
    (coordinate :
      Fin (wz2PaperPreparedOneParentFineScaleCount prepared parent)) :
    DecidableEq
      (WZ2PaperPreparedOneParentLocalParent
        prepared parent callerFiberData coordinate) := by
  unfold WZ2PaperPreparedOneParentLocalParent
  infer_instance

noncomputable def WZ2PaperPreparedOneParentLocalParentMap
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (parent : Fin prepared.callerStrict.coarse.card)
    (callerFiberData :
      ∀ coordinate,
        prepared.callerLevel.val ≤ coordinate.val →
          WZ2PaperCallerFiberScaleData
            prepared parent coordinate)
    (initial :
      Kakeya.Streamlined.TubeSubfamily
        (wz2PaperPreparedOneParentFiber prepared parent).family)
    (coordinate :
      Fin (wz2PaperPreparedOneParentFineScaleCount prepared parent)) :
    Fin initial.family.card →
      WZ2PaperPreparedOneParentLocalParent
        prepared parent callerFiberData coordinate :=
  fun sourceIndex =>
    (callerFiberData
      (wz2PaperPreparedOneParentFineCoordinate
        prepared parent coordinate)
      (wz2PaperPreparedOneParentFineCoordinate_le
        prepared parent coordinate)).scaleData.cover.parent
      (initial.embedding sourceIndex)

structure WZ2PaperPreparedOneParentLocalBranchData
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (parent : Fin prepared.callerStrict.coarse.card)
    (initial :
      Kakeya.Streamlined.TubeSubfamily
        (wz2PaperPreparedOneParentFiber prepared parent).family)
    (initialShading : WZ1PaperTubeShading initial.family) where
  callerFiberData :
    ∀ coordinate,
      prepared.callerLevel.val ≤ coordinate.val →
        WZ2PaperCallerFiberScaleData prepared parent coordinate
  regularized :
    WZ2PaperNestedWeightedParentRegularizationData
      (Fin initial.family.card)
      (fun sourceIndex => volume (initialShading.carrier sourceIndex))
      (wz2PaperPreparedOneParentFineScaleCount prepared parent)
      (WZ2PaperPreparedOneParentLocalParent
        prepared parent callerFiberData)
      (WZ2PaperPreparedOneParentLocalParentMap
        prepared parent callerFiberData initial)
  selected :
    Kakeya.Streamlined.TubeSubfamily initial.family
  selected_eq :
    selected =
      Kakeya.Streamlined.TubeSubfamily.fromFinset
        initial.family regularized.selected
  refined : WZ1PaperTubeShading selected.family
  refined_eq :
    refined = restrictPaperShading selected initialShading
  retained_mass :
    initialShading.mass ≤
      (2 : ENNReal) ^
          (wz2PaperPreparedOneParentFineScaleCount prepared parent) *
        refined.mass
  parent_mass_floor :
    ∀ coordinate,
      ∀ value :
          WZ2PaperPreparedOneParentLocalParent
            prepared parent callerFiberData coordinate,
        (regularized.selected.filter fun sourceIndex =>
          WZ2PaperPreparedOneParentLocalParentMap
              prepared parent callerFiberData initial
              coordinate sourceIndex =
            value).Nonempty →
          (1 / 2 : ENNReal) * refined.mass ≤
            (Fintype.card
                (WZ2PaperPreparedOneParentLocalParent
                  prepared parent callerFiberData coordinate) :
              ENNReal) *
              ∑ sourceIndex ∈
                  regularized.selected.filter fun sourceIndex =>
                    WZ2PaperPreparedOneParentLocalParentMap
                        prepared parent callerFiberData initial
                        coordinate sourceIndex =
                      value,
                volume (initialShading.carrier sourceIndex)

def WZ2PropStickyPreparedOneParentLocalBranchStatement : Prop :=
  ∀ {delta sourceLoss stableLoss : ℝ},
    ∀ {source : Kakeya.Streamlined.TubeFamily delta},
      ∀ {shading : WZ1PaperTubeShading source},
        ∀ {caller : Kakeya.Streamlined.AdmissibleScale delta},
          ∀ {preparationExponent : ℕ},
            ∀ (prepared :
                WZ2PaperCallerStrictPreparationData
                  (sourceLoss := sourceLoss)
                  (stableLoss := stableLoss)
                  shading caller preparationExponent),
              ∀ parent : Fin prepared.callerStrict.coarse.card,
                ∀ (initial :
                    Kakeya.Streamlined.TubeSubfamily
                      (wz2PaperPreparedOneParentFiber
                        prepared parent).family),
                  ∀ initialShading :
                      WZ1PaperTubeShading initial.family,
                    Nonempty
                      (WZ2PaperPreparedOneParentLocalBranchData
                        prepared parent initial initialShading)

end Kakeya.Assouad

end
