import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedGlobalBinPackage
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23WindowedGlobalPackage

/-!
# Sharp localized prepared graph for WZ1 Lemma 23

This package repeats the closed actual four-cycle and normalization assembly,
but uses the paper-faithful localized global-bin bound at radius `sqrt rho`
instead of the coarse whole-slice bound at radius one.
-/

namespace Kakeya.Assouad

noncomputable section

/--
The actual normalized graph on one y-residue class with the sharp localized
global-bin bound.
-/
structure WZ1Lemma23LocalizedPreparedPackage
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C)
    (localized :
      WZ1Lemma23LocalizedGlobalBinPackage windowed.global)
    (residue :
      WZ1Lemma23YResiduePackage windowed.global)
    (localBins :
      WZ1Lemma23LocalBinPackage
        (rho := rho) (sigma := sigma) C windowed.global.cells) where
  selectedLocal :
    WZ1Lemma23LocalBinPackage
      (rho := rho) (sigma := sigma) C residue.cells
  selectedLocal_g : selectedLocal.g = localBins.g
  selectedLocal_bound :
    selectedLocal.localBinBound = localBins.localBinBound
  baseHeightIndex : ℤ
  baseGlobalBin : ℤ
  actual :
    WZ1Lemma23ActualTripartitePackage
      rho windowed.global.extendedSlope selectedLocal.g
      residue.cells baseHeightIndex baseGlobalBin
  normalized : WZ1Lemma23NormalizedTripartitePackage rho
  normalized_sourceF : normalized.sourceF = actual.F
  normalized_sourceG₁ : normalized.sourceG₁ = actual.G₁
  normalized_sourceG₂ : normalized.sourceG₂ = actual.G₂
  normalized_sourceH : normalized.sourceH = actual.H
  normalized_sourceValues :
    normalized.sourceValues =
      wz1Lemma23SnappedBaseSliceValues
        rho windowed.global.extendedSlope residue.cells
        baseHeightIndex baseGlobalBin
  edge_card : normalized.H.card = actual.H.card
  abundance :
    residue.cells.card ^ 4 ≤
      ((wz1Lemma23SnappedYLayers residue.cells).card *
        selectedLocal.localBinBound) ^ 2 *
      ((wz1Lemma23SnappedHeights residue.cells).card ^ 2 *
        localized.globalBinBound) *
      ((wz1Lemma23SnappedHeights residue.cells).card *
        localized.globalBinBound) *
      16 * normalized.H.card

/--
Build the sharp localized actual graph on the selected y-residue cells.
-/
theorem wz1_lemma23_localized_prepared_package
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C)
    (localized :
      WZ1Lemma23LocalizedGlobalBinPackage windowed.global)
    (residue :
      WZ1Lemma23YResiduePackage windowed.global)
    (localBins :
      WZ1Lemma23LocalBinPackage
        (rho := rho) (sigma := sigma) C windowed.global.cells) :
    Nonempty
      (WZ1Lemma23LocalizedPreparedPackage
        windowed localized residue localBins) := by
  let selectedLocal :=
    localBins.restrict residue.cells residue.cells_subset
  rcases
      wz1_lemma23_actual_tripartite_package
        rho windowed.global.extendedSlope selectedLocal.g
        residue.cells selectedLocal.localBinBound
        localized.globalBinBound windowed.global.rho_pos
        selectedLocal.local_bins
        (localized.global_bins_mono residue.cells_subset) with
    ⟨baseHeightIndex, baseGlobalBin, actual, habundance⟩
  rcases actual.normalize windowed.global.rho_pos with
    ⟨normalized, hsourceF, hsourceG₁, hsourceG₂,
      hsourceH, hsourceValues⟩
  have hcard : normalized.H.card = actual.H.card := by
    rw [normalized.card_eq, hsourceH]
  exact
    ⟨{ selectedLocal := selectedLocal
       selectedLocal_g := rfl
       selectedLocal_bound := rfl
       baseHeightIndex := baseHeightIndex
       baseGlobalBin := baseGlobalBin
       actual := actual
       normalized := normalized
       normalized_sourceF := hsourceF
       normalized_sourceG₁ := hsourceG₁
       normalized_sourceG₂ := hsourceG₂
       normalized_sourceH := hsourceH
       normalized_sourceValues := hsourceValues
       edge_card := hcard
       abundance := by
         rw [hcard]
         exact habundance }⟩

end

end Kakeya.Assouad
