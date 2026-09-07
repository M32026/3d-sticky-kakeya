import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseBalancedFiberCounting
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseAffineMaps

/-!
# Exact balanced coarse-strip pullback

This module combines the balanced-fiber counting theorem with the exact
self-adjoint strip pullback under `wideCoarsePhiG`.  Crucially, the source
radius retains the denominator `‖A normal‖`; replacing it by the weaker
`radius + error` loses the transverse width gain needed in Proposition 8.9.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/--
Pull one target strip on a balanced coarse endpoint set back to one common
source strip, preserving the exact normalizing factor.
-/
lemma anisotropic_coarse_strip_card_le_exact_source_strip
    {E : DiscreteSet 2}
    {v : Point2} {w : ℝ} {hw : 0 < w} {hwOne : w ≤ 1}
    {base anchor : Point2} {hv : ‖v‖ = 1}
    {delta epsilon : ℝ} {constant : ENNReal}
    (rescale :
      WZ1AnisotropicFrostmanRescalingData
        E (wideCoarsePhiG v w hw base anchor hv)
        delta w epsilon constant)
    (hdelta : 0 ≤ delta)
    (normal : Point2) (hnormal : ‖normal‖ = 1)
    (level radius : ℝ)
    (hradius : 0 ≤ radius) :
    let pullback := wideCoarsePhiGPullbackVector v w normal
    let pullbackNorm := ‖pullback‖
    let sourceNormal := (1 / pullbackNorm) • pullback
    let sourceLevel :=
      (level -
        inner ℝ
          (wideCoarsePhiG v w hw base anchor hv 0) normal) /
        pullbackNorm
    let sourceRadius := (radius + delta / w) / pullbackNorm
    ‖sourceNormal‖ = 1 ∧
      0 ≤ sourceRadius ∧
      (rescale.fiberMultiplicity : ENNReal) *
          ((rescale.coarse.filter fun point =>
            |inner ℝ point normal - level| ≤ radius).card :
              ENNReal) ≤
        ((rescale.selected.filter fun point =>
          |inner ℝ point sourceNormal - sourceLevel| ≤
            sourceRadius).card : ENNReal) := by
  classical
  dsimp only
  let pullback := wideCoarsePhiGPullbackVector v w normal
  let pullbackNorm := ‖pullback‖
  let sourceNormal := (1 / pullbackNorm) • pullback
  let sourceLevel :=
    (level -
      inner ℝ
        (wideCoarsePhiG v w hw base anchor hv 0) normal) /
      pullbackNorm
  let sourceRadius := (radius + delta / w) / pullbackNorm
  have herror : 0 ≤ delta / w := by
    exact div_nonneg hdelta hw.le
  have hpullbackLower :
      1 ≤ pullbackNorm := by
    exact
      wideCoarsePhiGPullbackVector_norm_lower
        hw hwOne hv hnormal
  have hpullbackPos : 0 < pullbackNorm := by
    linarith
  have hsourceNormal : ‖sourceNormal‖ = 1 := by
    dsimp only [sourceNormal]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < (1 / pullbackNorm : ℝ))]
    change (1 / pullbackNorm) * pullbackNorm = 1
    field_simp [hpullbackPos.ne']
  have hsourceRadius : 0 ≤ sourceRadius := by
    dsimp only [sourceRadius]
    positivity
  refine ⟨hsourceNormal, hsourceRadius, ?_⟩
  apply
    anisotropic_coarse_filter_card_le_selected_filter
      rescale
      (fun point =>
        |inner ℝ point normal - level| ≤ radius)
      (fun point =>
        |inner ℝ point sourceNormal - sourceLevel| ≤ sourceRadius)
  intro coarsePoint hcoarsePoint hcoarseStrip
    sourcePoint hsourcePoint hassignment
  have hclose :
      dist
        (wideCoarsePhiG v w hw base anchor hv sourcePoint)
        coarsePoint ≤ delta / w := by
    rw [← hassignment]
    exact rescale.assignment_close sourcePoint hsourcePoint
  have h :=
    wideCoarsePhiG_strip_pullback_exact
      hw hwOne base anchor hv normal hnormal
      level radius (delta / w)
      hradius herror
      sourcePoint coarsePoint hclose hcoarseStrip
  simpa [pullback, pullbackNorm, sourceNormal,
    sourceLevel, sourceRadius] using h.2.2

end Kakeya.Assouad
