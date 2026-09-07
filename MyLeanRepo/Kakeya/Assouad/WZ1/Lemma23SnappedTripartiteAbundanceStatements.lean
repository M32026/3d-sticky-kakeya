import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23BaseCyclePigeonholeStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedFourCycleAbundanceStatements

/-!
# Actual tripartite-edge abundance in WZ1 Lemma 23

This is the quantitative endpoint of Steps 3--4 before the projection theorem.
It keeps the actual snapped cells, actual snapped four-cycles, and the actual
centered tripartite edge map.
-/

namespace Kakeya.Assouad

noncomputable section

/--
After the two concrete Cauchy--Schwarz counts, fix the first cube's height and
global bin.  The bounded edge fiber then converts the surviving actual
four-cycles into a large actual tripartite graph.
-/
def WZ1Lemma23SnappedTripartiteAbundanceConclusion : Prop :=
  ∀ (rho : ℝ) (f g : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (localBinBound globalBinBound : ℕ),
    0 < rho →
    (∀ y ∈ wz1Lemma23SnappedYLayers cells,
      (wz1Lemma23SnappedLocalBinsAt
        rho g cells y).card ≤ localBinBound) →
    (∀ z ∈ wz1Lemma23SnappedHeights cells,
      (wz1Lemma23SnappedGlobalBinsAt
        rho f cells z).card ≤ globalBinBound) →
      ∃ baseHeightIndex baseGlobalBin : ℤ,
        let baseCycles :=
          wz1Lemma23SnappedBaseCycles
            rho f g cells baseHeightIndex baseGlobalBin
        let edge :=
          wz1Lemma23SnappedTripartiteEdge
            rho f g baseHeightIndex
        let edges := baseCycles.image edge
        cells.card ^ 4 ≤
          ((wz1Lemma23SnappedYLayers cells).card *
            localBinBound) ^ 2 *
          ((wz1Lemma23SnappedHeights cells).card ^ 2 *
            globalBinBound) *
          ((wz1Lemma23SnappedHeights cells).card *
            globalBinBound) *
          16 * edges.card

/-- Assemble the actual tripartite-edge abundance from its four finite leaves. -/
def WZ1Lemma23SnappedTripartiteAbundanceFromLeavesStatement : Prop :=
  WZ1Lemma23SnappedTripartiteFiberStatement →
    WZ1Lemma23SnappedTripartiteAbundanceConclusion

end

end Kakeya.Assouad
