import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentSelectionStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyCallerFiberScaleStatements

/-!
# Quantitative retention and uniformity for one selected caller fiber

The complete caller fiber has a common per-tube mass floor.  Tube packing
keeps complete tube shadings, and nested branch pruning loses only
`2 ^ strictScaleCount`.  These facts give:

* weighted cardinality retention for the selected source family;
* uniform occupied fibers at each strict coordinate.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperPreparedOneParentQuantitativeData
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
    (selection :
      WZ2PaperPreparedOneParentSelectionData prepared parent) where
  weight : ENNReal
  weight_eq :
    weight =
      (1 / 2 : ENNReal) *
        Kakeya.realRpowENN delta sourceLoss
  massRetentionConstant : ENNReal
  massRetentionConstant_eq :
    massRetentionConstant =
      (packingConstant10000 : ENNReal) *
        (2 : ENNReal) ^
          (wz2PaperPreparedOneParentFineScaleCount prepared parent)
  cardinalityRetentionConstant : ENNReal
  cardinalityRetentionConstant_eq :
    cardinalityRetentionConstant =
      massRetentionConstant *
        (55296 * Kakeya.deltaTubeVolume 1)
  weight_ne_zero : weight ≠ 0
  weight_ne_top : weight ≠ ⊤
  global_retention :
    weight *
        (wz2PaperPreparedOneParentFiber
          prepared parent).family.enncard ≤
      cardinalityRetentionConstant *
        selection.refinement.selected.family.enncard
  selectedUniformConstant : ENNReal
  selectedUniformConstant_eq :
    selectedUniformConstant =
      (((1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta sourceLoss *
          Kakeya.realRpowENN delta 2)⁻¹ *
        (2 * prepared.structuralConstant *
          massRetentionConstant *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN delta 2)))
  selected_uniform :
    ∀ tailCoordinate :
        Fin (wz2PaperPreparedOneParentFineScaleCount
          prepared parent),
      let coordinate :=
        wz2PaperPreparedOneParentFineCoordinate
          prepared parent tailCoordinate
      let hcoordinate :=
        wz2PaperPreparedOneParentFineCoordinate_le
          prepared parent tailCoordinate
      let callerFiberData :=
        selection.branch.callerFiberData coordinate hcoordinate
      ∀ first second :
              Fin (callerFiberData.scaleData.cover
                |>.hitParentSubfamily
                  selection.refinement.selected).family.card,
        wz2PaperFullFiberCount
            selection.refinement.selected.family
            (callerFiberData.scaleData.cover
              |>.hitParentSubfamily
                selection.refinement.selected).family
            first ≤
          selectedUniformConstant *
            wz2PaperFullFiberCount
              selection.refinement.selected.family
              (callerFiberData.scaleData.cover
                |>.hitParentSubfamily
                  selection.refinement.selected).family
              second

def WZ2PropStickyPreparedOneParentQuantitativeStatement : Prop :=
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
                ∀ (selection :
                    WZ2PaperPreparedOneParentSelectionData
                      prepared parent),
                  Nonempty
                    (WZ2PaperPreparedOneParentQuantitativeData
                      prepared parent selection)

end Kakeya.Assouad

end
