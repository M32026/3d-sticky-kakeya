import MyLeanRepo.Kakeya.Assouad.PropStickyLeafStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyNestedWeightedParentRegularizationStatements

/-!
# Nested weighted branch selection inside one caller parent

Fix one complete parent fiber of the caller-scale strict cover.  Restrict all
parent maps in the caller-rooted nested tree to that fiber, then prune only
whole nested branches.  The retained mass loss is exactly
`2 ^ prepared.strictScaleCount`; no scale-by-scale logarithmic loss appears.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

def wz2PaperPreparedOneParentFiber
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
    (parent : Fin prepared.callerStrict.coarse.card) :
    Kakeya.Streamlined.TubeSubfamily
      prepared.refinement.selected.family :=
  prepared.callerStrict.cover.fullFiberSubfamily parent

def wz2PaperPreparedOneParentShading
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
    (parent : Fin prepared.callerStrict.coarse.card) :
    WZ1PaperTubeShading
      (wz2PaperPreparedOneParentFiber prepared parent).family :=
  restrictPaperShading
    (wz2PaperPreparedOneParentFiber prepared parent)
    prepared.refinement.refined

def wz2PaperPreparedOneParentParentMap
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
    (coordinate : Fin prepared.strictScaleCount) :
    Fin (wz2PaperPreparedOneParentFiber prepared parent).family.card →
      Fin (prepared.strictScaleData coordinate).coarse.card :=
  fun sourceIndex =>
    (prepared.strictScaleData coordinate).cover.parent
      ((wz2PaperPreparedOneParentFiber prepared parent).embedding
        sourceIndex)

def wz2PaperPreparedOneParentSelectedParentMap
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
    (coordinate : Fin prepared.strictScaleCount) :
    Fin initial.family.card →
      Fin (prepared.strictScaleData coordinate).coarse.card :=
  fun sourceIndex =>
    wz2PaperPreparedOneParentParentMap prepared parent coordinate
      (initial.embedding sourceIndex)

structure WZ2PaperPreparedOneParentBranchFromSubfamilyData
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
  regularized :
    WZ2PaperNestedWeightedParentRegularizationData
      (Fin initial.family.card)
      (fun sourceIndex =>
        volume (initialShading.carrier sourceIndex))
      prepared.strictScaleCount
      (fun coordinate =>
        Fin (prepared.strictScaleData coordinate).coarse.card)
      (wz2PaperPreparedOneParentSelectedParentMap
        prepared parent initial)
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
      (2 : ENNReal) ^ prepared.strictScaleCount * refined.mass
  parent_mass_floor :
    ∀ coordinate,
      ∀ value : Fin (prepared.strictScaleData coordinate).coarse.card,
        (regularized.selected.filter fun sourceIndex =>
          wz2PaperPreparedOneParentSelectedParentMap
              prepared parent initial coordinate sourceIndex =
            value).Nonempty →
          (1 / 2 : ENNReal) * refined.mass ≤
            ((prepared.strictScaleData coordinate).coarse.card :
              ENNReal) *
              ∑ sourceIndex ∈
                  regularized.selected.filter fun sourceIndex =>
                    wz2PaperPreparedOneParentSelectedParentMap
                        prepared parent initial coordinate sourceIndex =
                      value,
                volume (initialShading.carrier sourceIndex)

def WZ2PropStickyPreparedOneParentBranchFromSubfamilyStatement : Prop :=
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
                      (WZ2PaperPreparedOneParentBranchFromSubfamilyData
                        prepared parent initial initialShading)

structure WZ2PaperPreparedOneParentBranchData
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
    (parent : Fin prepared.callerStrict.coarse.card) where
  regularized :
    WZ2PaperNestedWeightedParentRegularizationData
      (Fin (wz2PaperPreparedOneParentFiber prepared parent).family.card)
      (fun sourceIndex =>
        volume
          ((wz2PaperPreparedOneParentShading prepared parent).carrier
            sourceIndex))
      prepared.strictScaleCount
      (fun coordinate =>
        Fin (prepared.strictScaleData coordinate).coarse.card)
      (wz2PaperPreparedOneParentParentMap prepared parent)
  selected :
    Kakeya.Streamlined.TubeSubfamily
      (wz2PaperPreparedOneParentFiber prepared parent).family
  selected_eq :
    selected =
      Kakeya.Streamlined.TubeSubfamily.fromFinset
        (wz2PaperPreparedOneParentFiber prepared parent).family
        regularized.selected
  refined :
    WZ1PaperTubeShading selected.family
  refined_eq :
    refined =
      restrictPaperShading selected
        (wz2PaperPreparedOneParentShading prepared parent)
  retained_mass :
    (wz2PaperPreparedOneParentShading prepared parent).mass ≤
      (2 : ENNReal) ^ prepared.strictScaleCount * refined.mass
  parent_mass_floor :
    ∀ coordinate,
      ∀ value : Fin (prepared.strictScaleData coordinate).coarse.card,
        (regularized.selected.filter fun sourceIndex =>
          wz2PaperPreparedOneParentParentMap
              prepared parent coordinate sourceIndex =
            value).Nonempty →
          (1 / 2 : ENNReal) * refined.mass ≤
            ((prepared.strictScaleData coordinate).coarse.card :
              ENNReal) *
              ∑ sourceIndex ∈
                  regularized.selected.filter fun sourceIndex =>
                    wz2PaperPreparedOneParentParentMap
                        prepared parent coordinate sourceIndex =
                      value,
                volume
                  ((wz2PaperPreparedOneParentShading prepared parent)
                    |>.carrier sourceIndex)

def WZ2PropStickyPreparedOneParentBranchStatement : Prop :=
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
                Nonempty
                  (WZ2PaperPreparedOneParentBranchData
                    prepared parent)

end Kakeya.Assouad

end
