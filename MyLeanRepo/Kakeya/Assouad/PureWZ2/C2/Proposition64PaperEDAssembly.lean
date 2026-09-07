import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64PaperConflictDegree

/-!
# Proposition 6.4 paper-ED assembly

This file assembles the positive-carrier deletion, the exact-`Phi` conflict
degree bound, and the weighted Definition-2.12 selection used in the final
Lemma-3.5 cleanup of `wz2_64.tex`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Complete essentially-distinct selection on the final saturated isotropic
family.  The degree is counted in the original source parameter space. -/
theorem pureWZ2Proposition64_exactPaperEDSelection
    {sourceDelta imageDelta finalDelta width scale : ℝ}
    (g : ℝ → ℝ)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (htranslationHeight : translation 2 = 0)
    (hhalfHeight : 0 < halfHeight) (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hslabCenter : |slabCenter| ≤ 1)
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hexactLine : WZ1PaperIsLineClass
      (pureWZ2Proposition64ImageFamily imageDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight
          (by linarith : 0 < normalization) sourceFamily))
    (exactShading : WZ1PaperTubeShading
      (pureWZ2Proposition64ImageFamily imageDelta g slabCenter anchorHeight
        halfHeight normalization translation hhalfHeight
          (by linarith : 0 < normalization) sourceFamily))
    (popular : PureWZ2Proposition64PopularBoxData exactShading width)
    (hwidth : 0 < width)
    (himageDelta : 0 < imageDelta)
    (hfinalDelta : 0 < finalDelta)
    (hfinalDeltaSmall : finalDelta ≤ 1 / 96)
    (hscale : 1 ≤ scale)
    (hradius : scale * (6 * imageDelta) +
      2 * finalDelta ≤ 6 * finalDelta)
    (hboxScale : 18 * scale * width ≤ 1)
    (C : ENNReal) (hFrostman : TubeParameterFrostmanBound sourceFamily C)
    (hsourceWidth : sourceDelta ≤
      24000 * normalization * finalDelta / halfHeight)
    (hwidthOne : 24000 * normalization * finalDelta / halfHeight ≤ 1) :
    let sourceWindow := popular.union_subset_closedBall hwidth
      (lt_of_lt_of_le zero_lt_one hscale)
      (by linarith : 3 * scale * width ≤ 1)
    let finalShading := pureWZ2Proposition64FullIsotropicPaperShading
      popular.restricted popular.center scale
      himageDelta hfinalDelta
      (hfinalDeltaSmall.trans (by norm_num)) hscale hradius sourceWindow
    let K := C * Kakeya.realRpowENN
      (24000 * normalization * finalDelta / halfHeight) 2 *
        sourceFamily.enncard
    Nonempty (PureWZ2Proposition64PaperEDCleanupData finalShading K) := by
  dsimp only
  let exactFamily := pureWZ2Proposition64ImageFamily imageDelta g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
      (by linarith : 0 < normalization) sourceFamily
  let sourceWindow := popular.union_subset_closedBall hwidth
    (lt_of_lt_of_le zero_lt_one hscale)
    (by linarith : 3 * scale * width ≤ 1)
  let finalShading := pureWZ2Proposition64FullIsotropicPaperShading
    popular.restricted popular.center scale
      himageDelta hfinalDelta
      (hfinalDeltaSmall.trans (by norm_num)) hscale hradius sourceWindow
  let positive := paperPositiveMassSubfamily finalShading
  let K := C * Kakeya.realRpowENN
    (24000 * normalization * finalDelta / halfHeight) 2 *
      sourceFamily.enncard
  have hpositiveLine : WZ1PaperIsLineClass positive.family := by
    apply pureWZ2Proposition64_positiveIsotropicFamily_lineClass popular
      hexactLine hwidth (by linarith : 0 < imageDelta) hfinalDelta
      hfinalDeltaSmall hscale hradius hboxScale
  have hdegree : ∀ reference : Fin positive.family.card,
      (((Finset.univ.filter fun other =>
        pureWZ2Proposition64PaperConflict positive.family reference other).card :
          ENNReal)) ≤ K := by
    exact pureWZ2Proposition64_positivePaperConflictDegree g slabCenter
      anchorHeight halfHeight normalization translation popular.center scale
      sourceFamily htranslationHeight hhalfHeight hhalfHeightOne hnormalization
      hanchorSlope hslabCenter hsourceLine hexactLine finalShading
      hpositiveLine (popular.center_mem 2) hscale hfinalDelta C hFrostman
      hsourceWidth hwidthOne
  exact pureWZ2Proposition64_paperEDCleanup_of_ennreal_degree
    _ finalShading K hdegree

end Kakeya.Assouad

end
