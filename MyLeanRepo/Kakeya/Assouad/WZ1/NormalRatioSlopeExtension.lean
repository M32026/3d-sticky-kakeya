import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Extend the genuine normal-ratio slope

In the global-grain argument the slope on the distinguished tube is not an
arbitrary auxiliary function.  At every retained height it is the ratio of
the first two horizontal coordinates of the rescaled plane normal.  This
module proves the quantitative quotient estimate and then applies the
Kirszbraun--Valentine extension theorem.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- Clamp a real number to the paper-normalized slope range. -/
private def clampNormalRatioSlope (value : ℝ) : ℝ :=
  max (-3) (min 3 value)

private lemma clampNormalRatioSlope_lipschitz :
    LipschitzWith 1 clampNormalRatioSlope := by
  have hmin : LipschitzWith 1 (fun value : ℝ => min 3 value) :=
    LipschitzWith.const_min LipschitzWith.id 3
  have hmax : LipschitzWith 1 (fun value : ℝ => max (-3) value) :=
    LipschitzWith.const_max LipschitzWith.id (-3)
  have hcomp := hmax.comp hmin
  change LipschitzWith 1 (fun value : ℝ => max (-3) (min 3 value))
  simpa only [one_mul, Function.comp_def] using hcomp

/--
Let `normal z` be the genuine plane normal at retained height `z`.  If these
normals are `K`-Lipschitz and their first coordinate stays at least `1/3` in
absolute value, then the paper slope `normal₁ / normal₀` extends to a global
`12 K`-Lipschitz function.  The extension is clamped only after Kirszbraun, so
it still agrees with the genuine coordinate ratio on every retained height.
-/
theorem normal_ratio_slope_extension
    {heights : Set ℝ} {normal : ℝ → Point3} {K : NNReal}
    (hnormal_unit : ∀ z ∈ heights, ‖normal z‖ = 1)
    (hnormal_transverse :
      ∀ z ∈ heights, 1 / 3 ≤ |normal z (0 : Fin 3)|)
    (hnormal_lipschitz : LipschitzOnWith K normal heights) :
    ∃ slope : ℝ → ℝ,
      LipschitzWith (12 * K) slope ∧
      (∀ z, |slope z| ≤ 3) ∧
      Set.EqOn
        (fun z => normal z (1 : Fin 3) / normal z (0 : Fin 3))
        slope heights := by
  let ratio : ℝ → ℝ := fun z =>
    normal z (1 : Fin 3) / normal z (0 : Fin 3)
  have hratio_lipschitz :
      LipschitzOnWith (12 * K) ratio heights := by
    apply LipschitzOnWith.of_dist_le_mul
    intro first hfirst second hsecond
    let firstNormal := normal first
    let secondNormal := normal second
    let a := firstNormal (1 : Fin 3)
    let b := firstNormal (0 : Fin 3)
    let c := secondNormal (1 : Fin 3)
    let d := secondNormal (0 : Fin 3)
    have hb_lower : 1 / 3 ≤ |b| :=
      hnormal_transverse first hfirst
    have hd_lower : 1 / 3 ≤ |d| :=
      hnormal_transverse second hsecond
    have hb_ne : b ≠ 0 := by
      have : 0 < |b| := lt_of_lt_of_le (by norm_num) hb_lower
      exact abs_ne_zero.mp this.ne'
    have hd_ne : d ≠ 0 := by
      have : 0 < |d| := lt_of_lt_of_le (by norm_num) hd_lower
      exact abs_ne_zero.mp this.ne'
    have hc_bound : |c| ≤ 1 := by
      have hcoord : |secondNormal (1 : Fin 3)| ≤ ‖secondNormal‖ :=
        PiLp.norm_apply_le secondNormal (1 : Fin 3)
      simpa [secondNormal, c, hnormal_unit second hsecond] using hcoord
    have hnumerator : |a - c| ≤ dist firstNormal secondNormal := by
      have hcoord :
          |(firstNormal - secondNormal) (1 : Fin 3)| ≤
            ‖firstNormal - secondNormal‖ :=
        PiLp.norm_apply_le
          (firstNormal - secondNormal) (1 : Fin 3)
      simpa [a, c, dist_eq_norm] using hcoord
    have hdenominator : |d - b| ≤ dist firstNormal secondNormal := by
      have hcoord :
          |(firstNormal - secondNormal) (0 : Fin 3)| ≤
            ‖firstNormal - secondNormal‖ :=
        PiLp.norm_apply_le
          (firstNormal - secondNormal) (0 : Fin 3)
      have heq :
          |d - b| =
            |(firstNormal - secondNormal) (0 : Fin 3)| := by
        simp only [d, b, PiLp.sub_apply]
        rw [show secondNormal 0 - firstNormal 0 =
          -(firstNormal 0 - secondNormal 0) by ring, abs_neg]
      rw [heq]
      simpa [dist_eq_norm] using hcoord
    have hquotient :
        |a / b - c / d| ≤ 12 * dist firstNormal secondNormal := by
      have halgebra :
          a / b - c / d =
            (a - c) / b + c * (d - b) / (b * d) := by
        field_simp [hb_ne, hd_ne]
        ring
      rw [halgebra]
      calc
        |(a - c) / b + c * (d - b) / (b * d)|
            ≤ |(a - c) / b| +
                |c * (d - b) / (b * d)| := abs_add_le _ _
        _ = |a - c| / |b| +
              |c| * |d - b| / (|b| * |d|) := by
          rw [abs_div, abs_div, abs_mul, abs_mul]
        _ ≤ dist firstNormal secondNormal / (1 / 3 : ℝ) +
              1 * dist firstNormal secondNormal /
                ((1 / 3 : ℝ) * (1 / 3 : ℝ)) := by
          gcongr
        _ = 12 * dist firstNormal secondNormal := by ring
    have hnormal_dist :
        dist firstNormal secondNormal ≤
          (K : ℝ) * dist first second := by
      simpa [firstNormal, secondNormal] using
        hnormal_lipschitz.dist_le_mul first hfirst second hsecond
    change dist (ratio first) (ratio second) ≤
      ((12 * K : NNReal) : ℝ) * dist first second
    rw [Real.dist_eq]
    change |a / b - c / d| ≤
      (12 * (K : ℝ)) * dist first second
    calc
      |a / b - c / d| ≤ 12 * dist firstNormal secondNormal :=
        hquotient
      _ ≤ 12 * ((K : ℝ) * dist first second) := by gcongr
      _ = (12 * (K : ℝ)) * dist first second := by ring
  rcases hratio_lipschitz.extend_real with
    ⟨rawSlope, hrawSlope_lipschitz, hrawSlope_eq⟩
  let slope : ℝ → ℝ := fun z =>
    clampNormalRatioSlope (rawSlope z)
  have hslope_lipschitz : LipschitzWith (12 * K) slope := by
    have hcomp :=
      clampNormalRatioSlope_lipschitz.comp hrawSlope_lipschitz
    simpa [slope, Function.comp_def] using hcomp
  have hslope_bound : ∀ z, |slope z| ≤ 3 := by
    intro z
    have hleft : -3 ≤ slope z := by
      simp [slope, clampNormalRatioSlope]
    have hright : slope z ≤ 3 := by
      simp [slope, clampNormalRatioSlope]
    exact abs_le.mpr ⟨hleft, hright⟩
  refine ⟨slope, hslope_lipschitz, hslope_bound, ?_⟩
  intro z hz
  have hratio_bound : |ratio z| ≤ 3 := by
    have hcoord : |normal z (1 : Fin 3)| ≤ ‖normal z‖ :=
      PiLp.norm_apply_le (normal z) (1 : Fin 3)
    have hnumerator : |normal z (1 : Fin 3)| ≤ 1 := by
      simpa [hnormal_unit z hz] using hcoord
    have hdenominator := hnormal_transverse z hz
    calc
      |ratio z| =
          |normal z (1 : Fin 3)| / |normal z (0 : Fin 3)| := by
        rw [abs_div]
      _ ≤ 1 / |normal z (0 : Fin 3)| := by gcongr
      _ ≤ 1 / (1 / 3 : ℝ) := by gcongr
      _ = 3 := by norm_num
  have hraw : ratio z = rawSlope z := hrawSlope_eq hz
  change ratio z = clampNormalRatioSlope (rawSlope z)
  rw [← hraw]
  have hleft : -3 ≤ ratio z := (abs_le.mp hratio_bound).1
  have hright : ratio z ≤ 3 := (abs_le.mp hratio_bound).2
  simp [clampNormalRatioSlope, min_eq_right hright, max_eq_right hleft]

end Kakeya.Assouad

end
