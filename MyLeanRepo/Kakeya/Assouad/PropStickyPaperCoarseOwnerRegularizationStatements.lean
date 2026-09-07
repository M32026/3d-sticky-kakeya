import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDominantOwnerExactificationStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperExternalWeightRegularizationStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPositiveExternalWeightSupportStatements

/-!
# Ambient nearby-scale regularization of the retained coarse owner family

The owner exactification produces a retained subfamily of the ambient coarse
family and an exact balanced coarse shading on that subfamily.  Arbitrary
subfamilies do not inherit hereditary nearby-scale CWA.  We therefore extend
the retained carrier-volume weights by zero to the original coarse family and
run the finite external-weight regularizer there.  Positivity of every
selected weight then proves that the regularized selection lies back inside
the retained owner family.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperCoarseOwnerRegularizationData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells
        availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells
        availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {active :
      WZ2PaperBalancedActiveParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData hdelta hrho}
    {multiplicityLevel : ℕ}
    {degree :
      WZ2PaperBalancedParentDegreeData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel}
    {dominant :
      WZ2PaperDominantParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree}
    {owned :
      WZ2PaperDominantParentFineCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree dominant}
    (exactified :
      WZ2PaperDominantOwnerExactificationData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active multiplicityLevel degree
        dominant owned)
    (ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal)
    (levelCount : ℕ) where
  packed :
    Kakeya.Streamlined.TubeSubfamily coarse
  packed_eq :
    packed =
      Kakeya.Streamlined.TubeSubfamily.fromFinset
        coarse exactified.retainedParents
  sourceWeight :
    Fin
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        coarse exactified.retainedParents).family.card →
      ENNReal
  sourceWeight_eq :
    ∀ index,
      sourceWeight index =
        MeasureTheory.volume
          (exactified.coarseShading.carrier index)
  externalWeight : Fin coarse.card → ENNReal
  externalWeight_eq :
    externalWeight =
      wz2PaperZeroExtendedExternalWeight
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          coarse exactified.retainedParents)
        sourceWeight
  regularized :
    WZ2PaperExternalWeightRegularizationData
      (family := coarse)
      ambientConstant outputConstant normalizationWeight weightUpper
      levelCount externalWeight
  support :
    WZ2PaperPositiveExternalWeightSupportData
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        coarse exactified.retainedParents)
      sourceWeight regularized.selected
  selectedShading :
    WZ1PaperTubeShading regularized.selected.family
  selectedShading_eq :
    selectedShading =
      restrictPaperShading support.toPackedSubfamily
        exactified.coarseShading
  selected_nonempty :
    regularized.selected.family.Nonempty
  selected_cwa_nearby :
    WZ2PaperCWAAtNearbyScales
      regularized.selected.family outputConstant
  selected_top_level_convex_wolff :
    WZ2PaperConvexWolffBound
      regularized.selected.family
      ((normalizationWeight⁻¹ *
          (regularized.regularizationLoss * weightUpper)) *
        packedConstant)
  ambient_mass_lower :
    normalizationWeight * coarse.enncard ≤
      exactified.coarseShading.mass
  selected_mass_retention :
    exactified.coarseShading.mass ≤
      regularized.regularizationLoss *
        selectedShading.mass

def WZ2PaperCoarseOwnerRegularizationStatement : Prop :=
  WZ2PaperExternalWeightRegularizationStatement →
  WZ2PaperPositiveExternalWeightSupportStatement →
  ∀ {delta rho : ℝ},
    ∀ (hdelta : 0 < delta),
      ∀ (hrho : 0 < rho),
        rho ≤ 1 →
        ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
          ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
            ∀ (cover : WZ2PaperPartitioningCover fine coarse),
              ∀ (sourceShading : WZ1PaperTubeShading fine),
                ∀ (coarseCells : Finset WZ2PaperCellIndex),
                  ∀ (availableFineCells :
                      WZ2PaperCellIndex →
                        Finset WZ2PaperCellIndex),
                    ∀ (balancing :
                        WZ2PaperExactCellBalancingData
                          (rho := rho) sourceShading coarseCells
                          availableFineCells),
                      ∀ (coarseData :
                          WZ2PaperCoarseShadingData
                            cover sourceShading coarseCells
                            availableFineCells balancing),
                        ∀ (active :
                            WZ2PaperBalancedActiveParentCellsData
                              cover sourceShading coarseCells
                              availableFineCells balancing coarseData
                              hdelta hrho),
                          ∀ (multiplicityLevel : ℕ),
                            ∀ (degree :
                                WZ2PaperBalancedParentDegreeData
                                  cover sourceShading coarseCells
                                  availableFineCells balancing
                                  coarseData active
                                  multiplicityLevel),
                              ∀ (dominant :
                                  WZ2PaperDominantParentCellsData
                                    cover sourceShading coarseCells
                                    availableFineCells balancing
                                    coarseData active
                                    multiplicityLevel degree),
                                ∀ (owned :
                                    WZ2PaperDominantParentFineCellsData
                                      cover sourceShading coarseCells
                                      availableFineCells balancing
                                      coarseData active
                                      multiplicityLevel degree dominant),
                                  ∀ (exactified :
                                      WZ2PaperDominantOwnerExactificationData
                                        cover sourceShading coarseCells
                                        availableFineCells balancing
                                        coarseData active
                                        multiplicityLevel degree dominant
                                        owned),
                                    ∀ (ambientConstant outputConstant
                                        normalizationWeight weightUpper
                                        packedConstant : ENNReal),
                                      normalizationWeight ≠ 0 →
                                      normalizationWeight ≠ ⊤ →
                                      weightUpper ≠ ⊤ →
                                      normalizationWeight *
                                          coarse.enncard ≤
                                        exactified.coarseShading.mass →
                                      (∀ index,
                                        MeasureTheory.volume
                                            (exactified.coarseShading.carrier
                                              index) ≤
                                          weightUpper) →
                                      ∀ (levelCount : ℕ),
                                        2 < ambientConstant →
                                        ambientConstant ≠ ⊤ →
                                        ENNReal.ofReal (1 / rho) ≤
                                          ambientConstant ^ levelCount →
                                        ambientConstant * ambientConstant ≤
                                          outputConstant →
                                        WZ1PaperIsLineClass coarse →
                                        WZ1PaperIsEssentiallyDistinct coarse →
                                        WZ2PaperCWACoversAtNearbyScales
                                          coarse ambientConstant →
                                        WZ2PaperConvexWolffBound
                                          coarse packedConstant →
                                        let degreeConstant :=
                                          16 *
                                            ((levelCount + 1 : ℕ) : ENNReal) *
                                            (Nat.log 2
                                                (2 * coarse.card) + 1 :
                                              ENNReal) ^
                                              (levelCount + 1)
                                        let regularizationLoss :=
                                          (8 : ENNReal) *
                                            (Nat.log 2
                                                (2 * coarse.card) + 1 :
                                              ENNReal) ^
                                              (levelCount + 2)
                                        max degreeConstant
                                            ((normalizationWeight⁻¹ *
                                                (ambientConstant *
                                                  (regularizationLoss *
                                                    weightUpper) *
                                                  degreeConstant)) *
                                              ambientConstant) ≤
                                          outputConstant →
                                        Nonempty
                                          (WZ2PaperCoarseOwnerRegularizationData
                                            exactified ambientConstant
                                            outputConstant
                                            normalizationWeight
                                            weightUpper packedConstant
                                            levelCount)

end Kakeya.Assouad

end
