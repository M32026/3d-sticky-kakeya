import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23GlobalSlicePackage
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalBinPackage
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23NormalizedTripartitePackage

/-!
# Prepared normalized tripartite package for WZ1 Lemma 23

The global-slice package and local-bin package are attached to the same actual
finite cell family.  Their two per-layer bin bounds feed the closed actual
four-cycle construction.  The resulting actual tripartite graph is then
normalized at scale `sqrt rho`, exactly as required before applying
Theorem 22.
-/

namespace Kakeya.Assouad

noncomputable section

/--
The complete finite output of the global/local preparation, before the
remaining Theorem 22 Katz--Tao, separation, boundedness, and Case B exclusion
obligations.
-/
structure WZ1Lemma23PreparedNormalizedPackage
    (rho : ℝ) (f g : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (localBinBound globalBinBound : ℕ) where
  baseHeightIndex : ℤ
  baseGlobalBin : ℤ
  actual :
    WZ1Lemma23ActualTripartitePackage
      rho f g cells baseHeightIndex baseGlobalBin
  normalized : WZ1Lemma23NormalizedTripartitePackage rho
  normalized_sourceF : normalized.sourceF = actual.F
  normalized_sourceG₁ : normalized.sourceG₁ = actual.G₁
  normalized_sourceG₂ : normalized.sourceG₂ = actual.G₂
  normalized_sourceH : normalized.sourceH = actual.H
  normalized_sourceValues :
    normalized.sourceValues =
      wz1Lemma23SnappedBaseSliceValues
        rho f cells baseHeightIndex baseGlobalBin
  abundance :
    cells.card ^ 4 ≤
      ((wz1Lemma23SnappedYLayers cells).card *
        localBinBound) ^ 2 *
      ((wz1Lemma23SnappedHeights cells).card ^ 2 *
        globalBinBound) *
      ((wz1Lemma23SnappedHeights cells).card *
        globalBinBound) *
      16 * normalized.H.card

/--
Combine the two actual bin packages and normalize the resulting actual
tripartite graph.
-/
theorem wz1_lemma23_prepared_normalized_package
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (globalPackage :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C)
    (localPackage :
      WZ1Lemma23LocalBinPackage
        (rho := rho) (sigma := sigma) C globalPackage.cells) :
    ∃ package :
      WZ1Lemma23PreparedNormalizedPackage
        rho globalPackage.extendedSlope localPackage.g
        globalPackage.cells localPackage.localBinBound
        globalPackage.globalBinBound,
      package.normalized.H.card = package.actual.H.card := by
  rcases
      wz1_lemma23_actual_tripartite_package
        rho globalPackage.extendedSlope localPackage.g
        globalPackage.cells localPackage.localBinBound
        globalPackage.globalBinBound globalPackage.rho_pos
        localPackage.local_bins globalPackage.global_bins with
    ⟨baseHeightIndex, baseGlobalBin, actual, habundance⟩
  rcases actual.normalize globalPackage.rho_pos with
    ⟨normalized, hsourceF, hsourceG₁, hsourceG₂,
      hsourceH, hsourceValues⟩
  have hcard : normalized.H.card = actual.H.card := by
    rw [normalized.card_eq, hsourceH]
  let package :
      WZ1Lemma23PreparedNormalizedPackage
        rho globalPackage.extendedSlope localPackage.g
        globalPackage.cells localPackage.localBinBound
        globalPackage.globalBinBound :=
    { baseHeightIndex := baseHeightIndex
      baseGlobalBin := baseGlobalBin
      actual := actual
      normalized := normalized
      normalized_sourceF := hsourceF
      normalized_sourceG₁ := hsourceG₁
      normalized_sourceG₂ := hsourceG₂
      normalized_sourceH := hsourceH
      normalized_sourceValues := hsourceValues
      abundance := by
        rw [hcard]
        exact habundance }
  exact ⟨package, by simpa [package] using hcard⟩

end

end Kakeya.Assouad
