import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRepairedFinalBalancedCoverStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalMultiplicityComparisonStatements

/-!
# Multiplicity comparison for the repaired final balanced cover

The ghost-free final cover already carries the common dyadic bands
`mu_coarse` and `mu_fine`.  This package applies the global multiplicity
product estimate to those exact final shadings.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperRepairedFinalMultiplicityComparisonData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (bandData : WZ2PaperGlobalMultiplicityBandData shading)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (rebalancing :
      WZ2PaperWholeCellRebalancingRepairedData
        cover shading bandData hdelta hrho)
    (finalLogExponent : ℕ)
    (finalData :
      WZ2PaperRepairedFinalBalancedCoverData
        cover shading bandData hdelta hrho
        rebalancing finalLogExponent)
    (massLower volumeUpper : ENNReal) where
  comparison :
    WZ2PaperFinalMultiplicityComparisonData
      cover
      finalData.producer.coarseBand.selectedFineShading
      finalData.producer.coarseBand.selectedCoarseShading
      finalData.producer.finalCover.balanced
      finalData.producer.coarseBand.level
      finalData.producer.fiberBand.level
      massLower volumeUpper

def WZ2PaperRepairedFinalMultiplicityComparisonStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ (cover : WZ2PaperPartitioningCover fine coarse),
          ∀ (shading : WZ1PaperTubeShading fine),
            ∀ (bandData :
                WZ2PaperGlobalMultiplicityBandData shading),
              ∀ (hdelta : 0 < delta),
                ∀ (hrho : 0 < rho),
                  ∀ (rebalancing :
                      WZ2PaperWholeCellRebalancingRepairedData
                        cover shading bandData hdelta hrho),
                    ∀ (finalLogExponent : ℕ),
                      ∀ (finalData :
                          WZ2PaperRepairedFinalBalancedCoverData
                            cover shading bandData hdelta hrho
                            rebalancing finalLogExponent),
                        ∀ (massLower volumeUpper : ENNReal),
                          massLower ≤
                              finalData.producer.coarseBand.selectedFineShading.mass →
                          MeasureTheory.volume
                                finalData.producer.coarseBand.selectedFineShading.union ≤
                              volumeUpper →
                          Nonempty
                            (WZ2PaperRepairedFinalMultiplicityComparisonData
                              cover shading bandData hdelta hrho
                              rebalancing finalLogExponent finalData
                              massLower volumeUpper)

end Kakeya.Assouad

end
