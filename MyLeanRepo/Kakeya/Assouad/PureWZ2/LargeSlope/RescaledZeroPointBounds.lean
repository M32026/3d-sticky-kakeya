import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ZeroPointBounds
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.TubeParameters
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Rescaled zero-point bounds via coaxial axis lines

Given a rescaled tube A whose axis line is the Φ-image of an original tube S's
axis line, prove that A's zero point equals Φ(axisPointAtHeight S z_mid), and
therefore satisfies the bounds needed by the line-class pigeonhole.

This is the bridge between bacon's `ConstructRescaledFamily` (which provides
the coaxial property) and the `LineClassPigeonholeSelection` (which needs
zero-point bounds).
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/--
If tube A's axis line is the Φ-image of tube S's axis line, then A's zero
point equals Φ applied to S's axis point at the slab midpoint.
-/
lemma rescaled_tube_zero_point_eq
    {delta rho : ℝ}
    {S : Kakeya.DeltaTube delta}
    {A : Kakeya.DeltaTube rho}
    (g : SlopeFunction) (c d m : ℝ) (hcd : c < d)
    (hSvertical : S.direction (2 : Fin 3) ≠ 0)
    (hAvertical : A.direction (2 : Fin 3) ≠ 0)
    (haxis : tubeAxisLine A = anisotropicRescalingMap g c d m '' tubeAxisLine S) :
    wz1TubeAxisZeroPoint A =
      anisotropicRescalingMap g c d m
        (tubeAxisPointAtHeight S (c + (d - c) / 2)) := by
  set z_mid : ℝ := c + (d - c) / 2 with hz_mid_def
  set p : Point3 := tubeAxisPointAtHeight S z_mid with hp_def
  set q : Point3 := anisotropicRescalingMap g c d m p with hq_def
  have hp_axis : p ∈ tubeAxisLine S := tubeAxisPointAtHeight_mem S z_mid
  have hq_axis : q ∈ tubeAxisLine A := by
    rw [haxis]
    exact ⟨p, hp_axis, rfl⟩
  have hp2 : p 2 = z_mid := tubeAxisPointAtHeight_coord_two S hSvertical z_mid
  have hne : d - c ≠ 0 := by linarith
  have hq2 : q 2 = 0 := by
    rw [hq_def]
    have h := (anisotropicRescalingMap_coord g c d m p).2.2
    rw [h, hp2]
    field_simp [hne] <;> ring
  have hq0 : q 0 = (tubeParamsOfTube A).a := by
    have h := tubeAxisLine_coord_zero A hAvertical hq_axis
    rw [h, hq2] <;> ring
  have hq1 : q 1 = (tubeParamsOfTube A).b := by
    have h := tubeAxisLine_coord_one A hAvertical hq_axis
    rw [h, hq2] <;> ring
  have h_zero_eq : wz1TubeAxisZeroPoint A = tubeAxisPointAtHeight A 0 := by
    ext i
    fin_cases i <;> simp [wz1TubeAxisZeroPoint, tubeAxisPointAtHeight] <;> ring
  have hA0 : (wz1TubeAxisZeroPoint A) 0 = (tubeParamsOfTube A).a := by
    rw [h_zero_eq]
    have h := tubeAxisPointAtHeight_coord_zero A hAvertical 0
    rw [h] <;> ring
  have hA1 : (wz1TubeAxisZeroPoint A) 1 = (tubeParamsOfTube A).b := by
    rw [h_zero_eq]
    have h := tubeAxisPointAtHeight_coord_one A hAvertical 0
    rw [h] <;> ring
  have hA2 : (wz1TubeAxisZeroPoint A) 2 = 0 := by
    rw [h_zero_eq]
    exact tubeAxisPointAtHeight_coord_two A hAvertical 0
  have h_main : q = wz1TubeAxisZeroPoint A := by
    ext i
    fin_cases i
    · exact hq0.trans hA0.symm
    · exact hq1.trans hA1.symm
    · exact hq2.trans hA2.symm
  exact h_main.symm

/--
X-coordinate bound for a rescaled tube with coaxial axis line.
|zero_x| ≤ 14/3.
-/
lemma rescaled_tube_zero_point_x_bound
    {delta rho : ℝ}
    {S : Kakeya.DeltaTube delta}
    {A : Kakeya.DeltaTube rho}
    (g : SlopeFunction) (c d m : ℝ)
    (hcd : c < d) (h_dc : d - c ≤ 1 / 25)
    (hcd_sub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hm_pos : 0 < m) (hm_one : m ≤ 1)
    (hg_norm : g.IsNormalized)
    (hS_line : WZ1PaperTubeInLineClass S)
    (hSvertical : S.direction (2 : Fin 3) ≠ 0)
    (hAvertical : A.direction (2 : Fin 3) ≠ 0)
    (haxis : tubeAxisLine A = anisotropicRescalingMap g c d m '' tubeAxisLine S) :
    |wz1TubeAxisZeroPoint A 0| ≤ 14 / 3 := by
  have h_eq := rescaled_tube_zero_point_eq g c d m hcd hSvertical hAvertical haxis
  rw [h_eq]
  let z_mid := c + (d - c) / 2
  let p := tubeAxisPointAtHeight S z_mid
  have h1 : -1 ≤ z_mid := by
    have hc_in : c ∈ Set.Icc c d := ⟨by linarith, by linarith⟩
    have h1 : -1 ≤ c := (hcd_sub hc_in).1
    dsimp only [z_mid] <;> linarith
  have h2 : z_mid ≤ 1 := by
    have hd_in : d ∈ Set.Icc c d := ⟨by linarith, by linarith⟩
    have h2 : d ≤ 1 := (hcd_sub hd_in).2
    dsimp only [z_mid] <;> linarith
  have hz_abs : |z_mid| ≤ 1 := abs_le.mpr ⟨h1, h2⟩
  have hpx : |p 0| ≤ 7 / 3 := axisPointAtHeight_x_bound hS_line z_mid hz_abs
  have hpy : |p 1| ≤ 7 / 3 := axisPointAtHeight_y_bound hS_line z_mid hz_abs
  have hg_abs : |g z_mid| ≤ 1 := (hg_norm z_mid ⟨h1, h2⟩).1
  have h_main : |p 0 + g z_mid * p 1| ≤ 14 / 3 := by
    calc |p 0 + g z_mid * p 1|
      ≤ |p 0| + |g z_mid * p 1| := by exact abs_add_le _ _
    _ = |p 0| + |g z_mid| * |p 1| := by rw [abs_mul]
    _ ≤ 7 / 3 + 1 * (7 / 3) := by gcongr
    _ = 14 / 3 := by norm_num
  have h_coord : (anisotropicRescalingMap g c d m p) 0 = p 0 + g z_mid * p 1 :=
    (anisotropicRescalingMap_coord g c d m p).1
  rw [h_coord]
  exact h_main

/--
Y-coordinate bound for a rescaled tube with coaxial axis line.
|zero_y| ≤ 7/150.
-/
lemma rescaled_tube_zero_point_y_bound
    {delta rho : ℝ}
    {S : Kakeya.DeltaTube delta}
    {A : Kakeya.DeltaTube rho}
    (g : SlopeFunction) (c d m : ℝ)
    (hcd : c < d) (h_dc : d - c ≤ 1 / 25)
    (hcd_sub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hm_pos : 0 < m) (hm_one : m ≤ 1)
    (hS_line : WZ1PaperTubeInLineClass S)
    (hSvertical : S.direction (2 : Fin 3) ≠ 0)
    (hAvertical : A.direction (2 : Fin 3) ≠ 0)
    (haxis : tubeAxisLine A = anisotropicRescalingMap g c d m '' tubeAxisLine S) :
    |wz1TubeAxisZeroPoint A 1| ≤ 7 / 150 := by
  have h_eq := rescaled_tube_zero_point_eq g c d m hcd hSvertical hAvertical haxis
  rw [h_eq]
  let z_mid := c + (d - c) / 2
  let p := tubeAxisPointAtHeight S z_mid
  have h1 : -1 ≤ z_mid := by
    have hc_in : c ∈ Set.Icc c d := ⟨by linarith, by linarith⟩
    have h1 : -1 ≤ c := (hcd_sub hc_in).1
    dsimp only [z_mid] <;> linarith
  have h2 : z_mid ≤ 1 := by
    have hd_in : d ∈ Set.Icc c d := ⟨by linarith, by linarith⟩
    have h2 : d ≤ 1 := (hcd_sub hd_in).2
    dsimp only [z_mid] <;> linarith
  have hz_abs : |z_mid| ≤ 1 := abs_le.mpr ⟨h1, h2⟩
  have hpy : |p 1| ≤ 7 / 3 := axisPointAtHeight_y_bound hS_line z_mid hz_abs
  have h_coord : (anisotropicRescalingMap g c d m p) 1 = (m * (d - c) / 2) * p 1 :=
    (anisotropicRescalingMap_coord g c d m p).2.1
  rw [h_coord]
  have hK_nonneg : 0 ≤ m * (d - c) / 2 := by positivity
  have h_abs : |m * (d - c) / 2 * p 1| = m * (d - c) / 2 * |p 1| := by
    rw [abs_mul, abs_of_nonneg hK_nonneg]
  rw [h_abs]
  calc m * (d - c) / 2 * |p 1|
    ≤ 1 * (1 / 25) / 2 * (7 / 3) := by gcongr
  _ = 7 / 150 := by norm_num

end Kakeya.Assouad

end
