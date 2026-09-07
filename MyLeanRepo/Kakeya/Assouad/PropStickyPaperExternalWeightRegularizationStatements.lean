import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteNearbyScheduleAssembly
import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization

/-!
# Nearby-scale regularization with external source weights

The fixed literal target family is indexed by source tubes, but the weight
that must be retained for the final paper refinement is the source shaded
mass, not the mass of the cubically saturated target shading.

This package applies the finite simultaneous-degree regularizer to an
arbitrary external weight on the target indices.  A uniform upper bound on
those weights converts weighted retention into selected cardinality
retention, which is exactly the input needed by the closed finite-schedule
nearby-CWA recovery.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperExternalWeightRegularizationData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ambientConstant outputConstant normalizationWeight weightUpper :
      ENNReal)
    (levelCount : ℕ)
    (externalWeight : Fin family.card → ENNReal) where
  schedule :
    WZ2PaperFiniteNearbyScheduleData
      (family := family)
      ambientConstant outputConstant levelCount
  selected : Kakeya.Streamlined.TubeSubfamily family
  selected_nonempty : selected.Nonempty
  selectedWeight : ENNReal
  selectedWeight_eq :
    selectedWeight =
      ∑ index : Fin selected.family.card,
        externalWeight (selected.embedding index)
  selectedWeightLevel : ENNReal
  selectedWeightLevel_pos :
    0 < selectedWeightLevel
  selectedWeightLevel_ne_top :
    selectedWeightLevel ≠ ⊤
  selected_weight_band :
    ∀ index : Fin selected.family.card,
      selectedWeightLevel ≤
          externalWeight (selected.embedding index) ∧
        externalWeight (selected.embedding index) ≤
          2 * selectedWeightLevel
  selected_weight_pos :
    ∀ index : Fin selected.family.card,
      0 < externalWeight (selected.embedding index)
  selected_weight_floor :
    0 < levelCount →
      ∀ index : Fin selected.family.card,
        (∑ source : Fin family.card, externalWeight source) /
              (2 * family.card : ENNReal) ≤
          externalWeight (selected.embedding index)
  regularizationLoss : ENNReal
  regularizationLoss_eq :
    regularizationLoss =
      (8 : ENNReal) *
        (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
          (levelCount + 2)
  retained_weight :
    (∑ index : Fin family.card, externalWeight index) ≤
      regularizationLoss * selectedWeight
  degreeConstant : ENNReal
  degreeConstant_eq :
    degreeConstant =
      16 * ((levelCount + 1 : ℕ) : ENNReal) *
        (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
          (levelCount + 1)
  degree_uniform :
    ∀ coordinate,
      ∀ first second :
          Fin (schedule.witness coordinate).scaleData.coarse.card,
        0 <
            ((Finset.univ :
                Finset (Fin selected.family.card)).filter
              fun source =>
                (schedule.witness coordinate).scaleData.cover.parent
                    (selected.embedding source) =
                  first).card →
          0 <
            ((Finset.univ :
                Finset (Fin selected.family.card)).filter
              fun source =>
                (schedule.witness coordinate).scaleData.cover.parent
                    (selected.embedding source) =
                  second).card →
          ((((Finset.univ :
              Finset (Fin selected.family.card)).filter
            fun source =>
              (schedule.witness coordinate).scaleData.cover.parent
                  (selected.embedding source) =
                first).card : ℕ) : ENNReal) ≤
            degreeConstant *
              ((((Finset.univ :
                  Finset (Fin selected.family.card)).filter
                fun source =>
                  (schedule.witness coordinate).scaleData.cover.parent
                      (selected.embedding source) =
                    second).card : ℕ) : ENNReal)
  cardinality_retention :
    normalizationWeight * family.enncard ≤
      (regularizationLoss * weightUpper) *
        selected.family.enncard
  cwa_nearby :
    WZ2PaperCWACoversAtNearbyScales
      selected.family outputConstant

def WZ2PaperExternalWeightRegularizationStatement : Prop :=
  WZ2PropStickyFiniteNearbyScheduleStatement →
  ∀ {delta : ℝ},
    0 < delta →
    delta ≤ 1 →
    ∀ {family : Kakeya.Streamlined.TubeFamily delta},
      family.Nonempty →
      WZ1PaperIsLineClass family →
      ∀ (ambientConstant outputConstant
          normalizationWeight weightUpper : ENNReal),
        normalizationWeight ≠ 0 →
        normalizationWeight ≠ ⊤ →
        weightUpper ≠ ⊤ →
        ∀ (externalWeight : Fin family.card → ENNReal),
          normalizationWeight * family.enncard ≤
            ∑ index : Fin family.card, externalWeight index →
          (∀ index, externalWeight index ≤ weightUpper) →
          ∀ levelCount : ℕ,
            2 < ambientConstant →
            ambientConstant ≠ ⊤ →
            ENNReal.ofReal (1 / delta) ≤
              ambientConstant ^ levelCount →
            ambientConstant * ambientConstant ≤ outputConstant →
            WZ2PaperCWACoversAtNearbyScales
              family ambientConstant →
            let degreeConstant :=
              16 * ((levelCount + 1 : ℕ) : ENNReal) *
                (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
                  (levelCount + 1)
            let regularizationLoss :=
              (8 : ENNReal) *
                (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
                  (levelCount + 2)
            max degreeConstant
                ((normalizationWeight⁻¹ *
                    (ambientConstant *
                      (regularizationLoss * weightUpper) *
                      degreeConstant)) *
                  ambientConstant) ≤
              outputConstant →
            Nonempty
              (WZ2PaperExternalWeightRegularizationData
                ambientConstant outputConstant
                normalizationWeight weightUpper
                levelCount externalWeight)

end Kakeya.Assouad

end
