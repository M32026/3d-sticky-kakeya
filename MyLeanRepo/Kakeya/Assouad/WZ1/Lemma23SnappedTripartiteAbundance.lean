import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23BaseCyclePigeonhole
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23BaseKeyImageBound
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedFourCycleAbundance
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedTripartiteFiber
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedTripartiteAbundanceStatements

/-!
# Assemble actual tripartite-edge abundance in WZ1 Lemma 23
-/

namespace Kakeya.Assouad

theorem wz1_lemma23_snapped_tripartite_abundance_from_leaves :
    WZ1Lemma23SnappedTripartiteAbundanceFromLeavesStatement := by
  intro hFiber rho f g cells localBinBound globalBinBound
    hrho hlocalBins hglobalBins
  let yLayers := wz1Lemma23SnappedYLayers cells
  let heights := wz1Lemma23SnappedHeights cells
  let allCycles := wz1Lemma23SnappedFourCycles rho f g cells
  let localKeyBound := yLayers.card * localBinBound
  let signatureBound := heights.card ^ 2 * globalBinBound
  let baseKeyBound := heights.card * globalBinBound
  have habundance :
      cells.card ^ 4 ≤
        localKeyBound ^ 2 * signatureBound *
          allCycles.card := by
    simpa [yLayers, heights, allCycles,
      localKeyBound, signatureBound] using
      (wz1_lemma23_snapped_four_cycle_abundance
        rho f g cells localBinBound globalBinBound
        hlocalBins hglobalBins)
  have hbaseKeys :
      (allCycles.image
        (wz1Lemma23BaseCycleKey rho f)).card ≤
          baseKeyBound := by
    simpa [allCycles, baseKeyBound, heights] using
      (wz1_lemma23_base_key_image_bound
        rho f g cells globalBinBound hglobalBins)
  rcases
      wz1_lemma23_base_cycle_pigeonhole
        rho f g cells baseKeyBound hbaseKeys with
    ⟨baseHeightIndex, baseGlobalBin, hpigeon⟩
  let baseCycles :=
    wz1Lemma23SnappedBaseCycles
      rho f g cells baseHeightIndex baseGlobalBin
  let edge :=
    wz1Lemma23SnappedTripartiteEdge
      rho f g baseHeightIndex
  let edges := baseCycles.image edge
  have hpigeon' :
      allCycles.card ≤ baseKeyBound * baseCycles.card := by
    simpa [allCycles, baseCycles] using hpigeon
  have hedge :
      baseCycles.card ≤ 16 * edges.card := by
    have h :=
      (hFiber rho f g cells
        baseHeightIndex baseGlobalBin hrho).2
    simpa [baseCycles, edge, edges] using h
  refine ⟨baseHeightIndex, baseGlobalBin, ?_⟩
  dsimp only
  calc
    cells.card ^ 4
        ≤ localKeyBound ^ 2 * signatureBound *
            allCycles.card :=
      habundance
    _ ≤ localKeyBound ^ 2 * signatureBound *
          (baseKeyBound * baseCycles.card) := by
      gcongr
    _ ≤ localKeyBound ^ 2 * signatureBound *
          (baseKeyBound * (16 * edges.card)) := by
      gcongr
    _ = localKeyBound ^ 2 * signatureBound *
          baseKeyBound * 16 * edges.card := by
      ring
    _ =
        (yLayers.card * localBinBound) ^ 2 *
          (heights.card ^ 2 * globalBinBound) *
          (heights.card * globalBinBound) *
          16 * edges.card := by
      rfl

/--
The complete finite Steps 3--4 output, after discharging the sharp-safe
sixteen-to-one edge-fiber bound.
-/
theorem wz1_lemma23_snapped_tripartite_abundance :
    WZ1Lemma23SnappedTripartiteAbundanceConclusion :=
  wz1_lemma23_snapped_tripartite_abundance_from_leaves
    wz1_lemma23_snapped_tripartite_fiber

end Kakeya.Assouad
