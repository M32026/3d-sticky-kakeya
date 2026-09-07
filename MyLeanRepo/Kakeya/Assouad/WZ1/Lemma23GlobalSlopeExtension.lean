import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Global bounded slope extension for WZ1 Lemma 23

The final Proposition 9 slope is one-Lipschitz only on `[-1,1]`.  Snapping a
boundary slice point to the center of its spatial cell can move its height
slightly outside that interval.  Before forming the actual Lemma 23 graph we
therefore extend the slope globally and clamp it to the same bounded range.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Clamp a real value to the paper-normalized global slope range. -/
def wz1Lemma23ClampGlobalSlope (value : ℝ) : ℝ :=
  max (-3) (min 3 value)

private lemma wz1Lemma23ClampGlobalSlope_lipschitz :
    LipschitzWith 1 wz1Lemma23ClampGlobalSlope := by
  have hmin : LipschitzWith 1 (fun value : ℝ => min 3 value) :=
    LipschitzWith.const_min LipschitzWith.id 3
  have hmax : LipschitzWith 1 (fun value : ℝ => max (-3) value) :=
    LipschitzWith.const_max LipschitzWith.id (-3)
  have hcomp :
      LipschitzWith (1 * 1) wz1Lemma23ClampGlobalSlope :=
    hmax.comp hmin
  simpa [one_mul] using hcomp

/--
Extend a one-Lipschitz slope on `[-1,1]` to a globally one-Lipschitz function
bounded by `3`, without changing any value in the source interval.
-/
theorem wz1_lemma23_global_slope_extension
    (slope : ℝ → ℝ)
    (hlipschitz :
      LipschitzOnWith 1 slope (Set.Icc (-1 : ℝ) 1))
    (hbounded :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1, |slope z| ≤ 3) :
    ∃ extended : ℝ → ℝ,
      LipschitzOnWith 1 extended Set.univ ∧
      (∀ z, |extended z| ≤ 3) ∧
      ∀ z ∈ Set.Icc (-1 : ℝ) 1, extended z = slope z := by
  rcases hlipschitz.extend_real with
    ⟨raw, hrawLipschitz, hrawEq⟩
  let extended : ℝ → ℝ := fun z =>
    wz1Lemma23ClampGlobalSlope (raw z)
  have hextendedLipschitz :
      LipschitzWith 1 extended := by
    have hcomp :=
      wz1Lemma23ClampGlobalSlope_lipschitz.comp hrawLipschitz
    change LipschitzWith (1 * 1)
      (wz1Lemma23ClampGlobalSlope ∘ raw) at hcomp
    simpa [extended, Function.comp_def] using hcomp
  have hextendedBounded :
      ∀ z, |extended z| ≤ 3 := by
    intro z
    have hleft : -3 ≤ extended z := by
      simp [extended, wz1Lemma23ClampGlobalSlope]
    have hright : extended z ≤ 3 := by
      simp [extended, wz1Lemma23ClampGlobalSlope]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hextendedEq :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1, extended z = slope z := by
    intro z hz
    have hraw : raw z = slope z :=
      (hrawEq hz).symm
    have hslope := hbounded z hz
    have hleft : -3 ≤ slope z := (abs_le.mp hslope).1
    have hright : slope z ≤ 3 := (abs_le.mp hslope).2
    simp [extended, wz1Lemma23ClampGlobalSlope, hraw,
      hleft, hright]
  exact
    ⟨extended, hextendedLipschitz.lipschitzOnWith,
      hextendedBounded, hextendedEq⟩

end

end Kakeya.Assouad
