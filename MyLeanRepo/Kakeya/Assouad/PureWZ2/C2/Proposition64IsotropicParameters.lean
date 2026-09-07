import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64PaperEDCleanup
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12LocalizedDoubledFiber

/-!
# Tube parameters under the final Proposition 6.4 isotropic similarity

This is the parameter-space form of the final Lemma 3.5 similarity.  It is
kept separate from the exact `Phi` parameter transform so the two inverse
distortion losses remain auditable.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Four vertical-line parameters after the centered isotropic similarity. -/
def pureWZ2Proposition64IsotropicTubeParams
    (center : Point3) (scale : ℝ) (params : TubeParams) : TubeParams where
  a := scale * (params.a + params.c * center 2 - center 0)
  b := scale * (params.b + params.d * center 2 - center 1)
  c := params.c
  d := params.d

/-- Direct parameter formula for the one-to-one isotropic paper tube. -/
theorem tubeParamsOfTube_isotropicPaperTube
    {sourceDelta targetDelta : ℝ}
    (center : Point3) (scale : ℝ)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hvertical : sourceTube.direction 2 ≠ 0) :
    tubeParamsOfTube
        (pureWZ2Proposition64IsotropicPaperTube
          (targetDelta := targetDelta) center scale sourceTube) =
      pureWZ2Proposition64IsotropicTubeParams center scale
        (tubeParamsOfTube sourceTube) := by
  apply TubeParams.ext <;>
    simp [tubeParamsOfTube, pureWZ2Proposition64IsotropicPaperTube,
      pureWZ2Proposition64IsotropicTubeParams,
      pureWZ2Proposition64IsotropicMap, point3] <;>
    field_simp [hvertical] <;> ring

/-- The canonical height-zero representative has the same transformed line
parameters as the unre-based isotropic tube. -/
theorem tubeParamsOfTube_isotropicRebasedPaperTube
    {sourceDelta targetDelta : ℝ}
    (center : Point3) (scale : ℝ)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (hvertical : sourceTube.direction 2 ≠ 0) :
    tubeParamsOfTube
        (pureWZ2Proposition64IsotropicRebasedPaperTube
          (targetDelta := targetDelta) center scale sourceTube) =
      pureWZ2Proposition64IsotropicTubeParams center scale
        (tubeParamsOfTube sourceTube) := by
  apply TubeParams.ext <;>
    simp [tubeParamsOfTube, pureWZ2Proposition64IsotropicRebasedPaperTube,
      pureWZ2Proposition64IsotropicPaperTube,
      pureWZ2Proposition64IsotropicTubeParams, wz1TubeAxisZeroPoint,
      pureWZ2Proposition64IsotropicMap] <;>
    field_simp [hvertical] <;> ring

/-- Invert a target parameter cluster through the positive isotropic map. -/
theorem pureWZ2Proposition64IsotropicTubeParams_inverse_cluster
    (center : Point3) {scale radius : ℝ}
    (hscale : 1 ≤ scale) (hcenter : |center 2| ≤ 1)
    (first second : TubeParams)
    (ha : |(pureWZ2Proposition64IsotropicTubeParams center scale first).a -
        (pureWZ2Proposition64IsotropicTubeParams center scale second).a| ≤ radius)
    (hb : |(pureWZ2Proposition64IsotropicTubeParams center scale first).b -
        (pureWZ2Proposition64IsotropicTubeParams center scale second).b| ≤ radius)
    (hc : |(pureWZ2Proposition64IsotropicTubeParams center scale first).c -
        (pureWZ2Proposition64IsotropicTubeParams center scale second).c| ≤ radius)
    (hd : |(pureWZ2Proposition64IsotropicTubeParams center scale first).d -
        (pureWZ2Proposition64IsotropicTubeParams center scale second).d| ≤ radius) :
    |first.a - second.a| ≤ 2 * radius ∧
      |first.b - second.b| ≤ 2 * radius ∧
      |first.c - second.c| ≤ 2 * radius ∧
      |first.d - second.d| ≤ 2 * radius := by
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  have hc' : |first.c - second.c| ≤ radius := by
    simpa [pureWZ2Proposition64IsotropicTubeParams] using hc
  have hd' : |first.d - second.d| ≤ radius := by
    simpa [pureWZ2Proposition64IsotropicTubeParams] using hd
  have ha' :
      |(first.a - second.a) + center 2 * (first.c - second.c)| ≤
        radius / scale := by
    have haRewrite :
        (pureWZ2Proposition64IsotropicTubeParams center scale first).a -
            (pureWZ2Proposition64IsotropicTubeParams center scale second).a =
          scale * ((first.a - second.a) +
            center 2 * (first.c - second.c)) := by
      simp [pureWZ2Proposition64IsotropicTubeParams]
      ring
    rw [haRewrite, abs_mul, abs_of_pos hscalePos] at ha
    exact (le_div_iff₀ hscalePos).2 (by simpa [mul_comm] using ha)
  have hb' :
      |(first.b - second.b) + center 2 * (first.d - second.d)| ≤
        radius / scale := by
    have hbRewrite :
        (pureWZ2Proposition64IsotropicTubeParams center scale first).b -
            (pureWZ2Proposition64IsotropicTubeParams center scale second).b =
          scale * ((first.b - second.b) +
            center 2 * (first.d - second.d)) := by
      simp [pureWZ2Proposition64IsotropicTubeParams]
      ring
    rw [hbRewrite, abs_mul, abs_of_pos hscalePos] at hb
    exact (le_div_iff₀ hscalePos).2 (by simpa [mul_comm] using hb)
  have hradiusNonneg : 0 ≤ radius := (abs_nonneg _).trans hc'
  have hradiusScale : radius / scale ≤ radius :=
    div_le_self hradiusNonneg hscale
  have hfirst : |first.a - second.a| ≤ 2 * radius := by
    have hsplit : first.a - second.a =
        ((first.a - second.a) + center 2 * (first.c - second.c)) -
          center 2 * (first.c - second.c) := by ring
    rw [hsplit]
    calc
      |_ - _| ≤ |(first.a - second.a) +
          center 2 * (first.c - second.c)| +
          |center 2 * (first.c - second.c)| := abs_sub _ _
      _ ≤ radius / scale + 1 * radius := by
        rw [abs_mul]
        gcongr
      _ ≤ 2 * radius := by linarith
  have hsecond : |first.b - second.b| ≤ 2 * radius := by
    have hsplit : first.b - second.b =
        ((first.b - second.b) + center 2 * (first.d - second.d)) -
          center 2 * (first.d - second.d) := by ring
    rw [hsplit]
    calc
      |_ - _| ≤ |(first.b - second.b) +
          center 2 * (first.d - second.d)| +
          |center 2 * (first.d - second.d)| := abs_sub _ _
      _ ≤ radius / scale + 1 * radius := by
        rw [abs_mul]
        gcongr
      _ ≤ 2 * radius := by linarith
  exact ⟨hfirst, hsecond, hc'.trans (by linarith), hd'.trans (by linarith)⟩

end Kakeya.Assouad

end
