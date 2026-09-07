import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryRescaledTube
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryRescaledLocality
import MyLeanRepo.Kakeya.Assouad.PropStickyStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import Mathlib.Tactic

/-!
# Fiber family IsInUnitBall

Proves that the canonical rescaled fiber family has `IsInUnitBall`, i.e., every
public tube carrier is contained in the Euclidean unit ball.

## Proof path

1. The source midpoint is bounded (from shading containment in axisBox).
2. The rescaled midpoint norm is bounded by the locality argument.
3. The public carrier is the ε-thickened unit segment centered at the rescaled midpoint.
4. For small ε, the entire carrier lies within the unit ball.

## Key bound

Given `‖sourceMid‖ ≤ C`, the rescaled midpoint has norm
`≤ (1 + 6*C) / 200`. The public carrier is contained in the ball of radius
`(1 + 6*C) / 200 + 1/2 + ε`.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set MeasureTheory Classical ENNReal
open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- Variant of the midpoint norm bound with a general source midpoint bound.

Given `‖wz2PaperTubeMidpoint source‖ ≤ C`, the rescaled tube midpoint has norm
at most `(1 + 6 * C) / 200`. -/
theorem wz2PaperLiteralOrdinaryRescaledTube_midpoint_norm_le_general
    {delta rho C : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hsourceLine : WZ1PaperTubeInLineClass source)
    (hcover : WZ1PaperTubeCovers source anchor)
    (hmidNorm : ‖wz2PaperTubeMidpoint source‖ ≤ C)
    (hC_nonneg : 0 ≤ C) :
    ‖wz2PaperTubeMidpoint
        (wz2PaperLiteralOrdinaryRescaledTube source anchor hrho)‖ ≤
      (1 + 6 * C) / 200 := by
  let sourceMid := wz2PaperTubeMidpoint source
  let sourceZero := wz1TubeAxisZeroPoint source
  let anchorZero := wz1TubeAxisZeroPoint anchor
  let parameter : ℝ :=
    source.base (2 : Fin 3) / source.direction (2 : Fin 3) + 1 / 2
  have hmidEq :
      sourceMid = sourceZero + parameter • source.direction := by
    dsimp only [sourceMid, sourceZero, parameter,
      wz2PaperTubeMidpoint, wz1TubeAxisZeroPoint]
    module
  have hcoord : |sourceMid (2 : Fin 3)| ≤ C :=
    (abs_coord_two_le_norm sourceMid).trans hmidNorm
  have hzeroTwo : sourceZero (2 : Fin 3) = 0 := by
    exact wz1TubeAxisZeroPoint_coord_two source hsourceLine.vertical
  have hcoordEq :
      sourceMid (2 : Fin 3) = parameter * source.direction (2 : Fin 3) := by
    rw [hmidEq]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      hzeroTwo, zero_add]
  have hproduct :
      |parameter| * |source.direction (2 : Fin 3)| ≤ C := by
    calc
      |parameter| * |source.direction (2 : Fin 3)| =
          |parameter * source.direction (2 : Fin 3)| := by
        rw [abs_mul]
      _ = |sourceMid (2 : Fin 3)| := by rw [hcoordEq]
      _ ≤ C := hcoord
  have hparameter : |parameter| ≤ 2 * C := by
    have hlower :
        (1 / 2 : ℝ) * |parameter| ≤
          |parameter| * |source.direction (2 : Fin 3)| := by
      calc
        (1 / 2 : ℝ) * |parameter| =
            |parameter| * (1 / 2 : ℝ) := by ring
        _ ≤ |parameter| * |source.direction (2 : Fin 3)| :=
          mul_le_mul_of_nonneg_left
            hsourceLine.vertical (abs_nonneg parameter)
    linarith
  have hzeroDistance :
      ‖sourceZero - anchorZero‖ ≤ rho / 2 := by
    simpa [sourceZero, anchorZero, dist_eq_norm] using
      hcover.components.1
  have hzeroImage :
      ‖wz2PaperLiteralUnitRescalingLinear anchor
          (sourceZero - anchorZero)‖ ≤
        1 / 200 := by
    calc
      ‖wz2PaperLiteralUnitRescalingLinear anchor
          (sourceZero - anchorZero)‖ ≤
          ‖sourceZero - anchorZero‖ / (100 * rho) :=
        wz2PaperLiteralUnitRescalingLinear_norm_le
          anchor hrho hrhoOne _
      _ ≤ (rho / 2) / (100 * rho) := by gcongr
      _ = 1 / 200 := by
        field_simp [hrho.ne'] <;> ring
  have hdirectionImage :
      ‖wz2PaperLiteralUnitRescalingLinear anchor source.direction‖ ≤
        3 / 200 :=
    wz2PaperLiteralUnitRescalingLinear_sourceDirection_norm_le
      hrho hrhoOne hcover
  have htargetMid :
      wz2PaperTubeMidpoint
          (wz2PaperLiteralOrdinaryRescaledTube source anchor hrho) =
        wz2PaperLiteralUnitRescalingMap anchor hrho sourceMid := by
    dsimp only [sourceMid, wz2PaperTubeMidpoint,
      wz2PaperLiteralOrdinaryRescaledTube]
    module
  have hanchorZeroMap :
      wz2PaperLiteralUnitRescalingMap anchor hrho anchorZero = 0 := by
    dsimp only [anchorZero]
    simp [wz2PaperLiteralUnitRescalingMap, unitRescalingMap]
  have hmapMid :
      wz2PaperLiteralUnitRescalingMap anchor hrho sourceMid =
        wz2PaperLiteralUnitRescalingLinear anchor
          (sourceMid - anchorZero) := by
    have hsub :=
      wz2PaperLiteralUnitRescalingMap_sub
        anchor hrho sourceMid anchorZero
    rw [hanchorZeroMap, sub_zero] at hsub
    exact hsub
  have hdecompose :
      sourceMid - anchorZero =
        (sourceZero - anchorZero) +
          parameter • source.direction := by
    rw [hmidEq]
    abel
  rw [htargetMid, hmapMid, hdecompose, map_add, map_smul]
  calc
    ‖wz2PaperLiteralUnitRescalingLinear anchor
        (sourceZero - anchorZero) +
      parameter •
        wz2PaperLiteralUnitRescalingLinear anchor source.direction‖ ≤
        ‖wz2PaperLiteralUnitRescalingLinear anchor
            (sourceZero - anchorZero)‖ +
          ‖parameter •
            wz2PaperLiteralUnitRescalingLinear anchor
              source.direction‖ :=
      norm_add_le _ _
    _ =
        ‖wz2PaperLiteralUnitRescalingLinear anchor
            (sourceZero - anchorZero)‖ +
          |parameter| *
            ‖wz2PaperLiteralUnitRescalingLinear anchor
              source.direction‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 / 200 + (2 * C) * (3 / 200) := by
      gcongr
    _ = (1 + 6 * C) / 200 := by ring

/-- The public ordinary rescaled tube carrier is contained in the unit ball.

Given `‖sourceMid‖ ≤ C` and `(1 + 6*C)/200 + 1/2 + epsilon ≤ 1`, the entire
public tube carrier lies in the Euclidean unit ball. -/
theorem wz2PaperLiteralOrdinaryRescaledTube_is_in_unit_ball
    {delta rho C : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hsourceLine : WZ1PaperTubeInLineClass source)
    (hcover : WZ1PaperTubeCovers source anchor)
    (hmidNorm : ‖wz2PaperTubeMidpoint source‖ ≤ C)
    (hC_nonneg : 0 ≤ C)
    (hepsilon : 0 < delta / rho)
    (hball : (1 + 6 * C) / 200 + 1 / 2 + delta / rho ≤ 1) :
    (wz2PaperLiteralOrdinaryRescaledTube source anchor hrho).IsInUnitBall := by
  let pub := wz2PaperLiteralOrdinaryRescaledTube source anchor hrho
  let pubMid := wz2PaperTubeMidpoint pub
  have hmid : ‖pubMid‖ ≤ (1 + 6 * C) / 200 :=
    wz2PaperLiteralOrdinaryRescaledTube_midpoint_norm_le_general
      hdelta hrho hrhoOne source anchor hsourceLine hcover hmidNorm hC_nonneg
  intro point hpoint
  let segment := Kakeya.unitSegment pub.base pub.direction
  have hcarrier : pub.carrier = Metric.cthickening (delta / rho) segment := by
    rfl
  rw [hcarrier] at hpoint
  have hsegmentCompact : IsCompact segment := by
    exact isCompact_Icc.image
      (continuous_const.add
        (continuous_id.smul continuous_const))
  have hdecomposition :
      Metric.cthickening (delta / rho) segment =
        ⋃ x ∈ segment, Metric.closedBall x (delta / rho) :=
    hsegmentCompact.cthickening_eq_biUnion_closedBall (by linarith)
  rw [hdecomposition] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨segPoint, hseg, hclosedBall⟩
  have hdist : dist point segPoint ≤ delta / rho := by
    simpa [Metric.mem_closedBall] using hclosedBall
  rcases (Set.mem_image _ _ _).mp hseg with ⟨t, ht, rfl⟩
  have hcenter : pub.base + t • pub.direction =
      pubMid + (t - 1 / 2 : ℝ) • pub.direction := by
    dsimp only [pubMid, wz2PaperTubeMidpoint]
    simp [smul_sub, sub_smul] <;> abel
  have hdist' : dist point (pubMid + (t - 1 / 2 : ℝ) • pub.direction) ≤ delta / rho := by
    rw [hcenter] at hdist
    exact hdist
  have hnorm1 : ‖pubMid + (t - 1 / 2 : ℝ) • pub.direction‖ ≤
      ‖pubMid‖ + |t - 1 / 2| := by
    calc
      ‖pubMid + (t - 1 / 2 : ℝ) • pub.direction‖ ≤
          ‖pubMid‖ + ‖(t - 1 / 2 : ℝ) • pub.direction‖ :=
        norm_add_le _ _
      _ = ‖pubMid‖ + |t - 1 / 2| * ‖pub.direction‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ = ‖pubMid‖ + |t - 1 / 2| := by
        rw [pub.direction_unit, mul_one]
  have htab : |t - 1 / 2| ≤ 1 / 2 := by
    have h1 : 0 ≤ t := ht.1
    have h2 : t ≤ 1 := ht.2
    rw [abs_le]
    constructor <;> linarith
  have hnorm2 : ‖pubMid + (t - 1 / 2 : ℝ) • pub.direction‖ ≤
      (1 + 6 * C) / 200 + 1 / 2 := by
    calc
      ‖pubMid + (t - 1 / 2 : ℝ) • pub.direction‖ ≤
          ‖pubMid‖ + |t - 1 / 2| := hnorm1
      _ ≤ (1 + 6 * C) / 200 + 1 / 2 := by
        gcongr <;> linarith
  have hfinal : ‖point‖ ≤ 1 := by
    have h : ‖point‖ ≤ ‖pubMid + (t - 1 / 2 : ℝ) • pub.direction‖ +
        ‖(pubMid + (t - 1 / 2 : ℝ) • pub.direction) - point‖ :=
      norm_le_norm_add_norm_sub (pubMid + (t - 1 / 2 : ℝ) • pub.direction) point
    have h3 : ‖(pubMid + (t - 1 / 2 : ℝ) • pub.direction) - point‖ =
        dist point (pubMid + (t - 1 / 2 : ℝ) • pub.direction) := by
      rw [← dist_eq_norm, dist_comm]
    rw [h3] at h
    calc
      ‖point‖ ≤ ‖pubMid + (t - 1 / 2 : ℝ) • pub.direction‖ +
          dist point (pubMid + (t - 1 / 2 : ℝ) • pub.direction) := h
      _ ≤ (1 + 6 * C) / 200 + 1 / 2 + delta / rho := by
        exact add_le_add hnorm2 hdist'
      _ ≤ 1 := hball
  simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall, dist_eq_norm] using hfinal

/-- Bound a source tube midpoint from a point in both paper and ordinary carriers.

If `p ∈ wz1PaperTubeCarrier source` (so `p ∈ axisBox 2 2 2`, hence `‖p‖ ≤ √3`)
and `p ∈ source.carrier` (ordinary carrier, so `infDist p segment ≤ δ`), then
the midpoint norm is at most `√3 + δ + 1/2 ≤ 4` for `δ ≤ 1`. -/
lemma midpoint_bounded_from_shading
    {delta : ℝ}
    {source : Kakeya.DeltaTube delta}
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (p : Point3)
    (hp_paper : p ∈ wz1PaperTubeCarrier source)
    (hp_ordinary : p ∈ source.carrier) :
    ‖wz2PaperTubeMidpoint source‖ ≤ 4 := by
  let m := wz2PaperTubeMidpoint source
  let seg := Kakeya.unitSegment source.base source.direction
  -- p ∈ axisBox 2 2 2 from paper carrier
  have hbox : p ∈ Kakeya.Streamlined.axisBox 2 2 2 := hp_paper.2
  have h1 : ∀ i : Fin 3, |p i| ≤ 1 := by
    have h1' : |p 0| ≤ 1 ∧ |p 1| ≤ 1 ∧ |p 2| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox
    intro i; fin_cases i <;> tauto
  have hnorm_p : ‖p‖ ≤ Real.sqrt 3 := by
    have h2 : ‖p‖ ^ 2 ≤ 3 := by
      have h3 : ‖p‖ = Real.sqrt ((p 0)^2 + (p 1)^2 + (p 2)^2) := by
        simp [PiLp.norm_eq_of_L2, Fin.sum_univ_succ] <;> ring_nf
      rw [h3]
      rw [Real.sq_sqrt (by positivity)]
      have h4 : (p 0)^2 ≤ 1 := by nlinarith [abs_le.mp (h1 0)]
      have h5 : (p 1)^2 ≤ 1 := by nlinarith [abs_le.mp (h1 1)]
      have h6 : (p 2)^2 ≤ 1 := by nlinarith [abs_le.mp (h1 2)]
      linarith
    have h4 : 0 ≤ ‖p‖ := by positivity
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  -- seg is compact and nonempty
  have hseg_compact : IsCompact seg := by
    exact isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  have hseg_nonempty : seg.Nonempty := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    have h1 : source.base + (0 : ℝ) • source.direction ∈ seg :=
      Set.mem_image_of_mem (fun t : ℝ => source.base + t • source.direction) h0
    have h2 : source.base + (0 : ℝ) • source.direction = source.base := by simp
    rw [h2] at h1
    exact ⟨source.base, h1⟩
  -- p ∈ ordinary carrier means infEDist p seg ≤ ENNReal.ofReal delta
  have hinf_edist : infEDist p seg ≤ ENNReal.ofReal delta := hp_ordinary
  -- compact seg achieves infEDist
  rcases hseg_compact.exists_infEDist_eq_edist hseg_nonempty p with ⟨r, hr_seg, hdist_eq⟩
  have hdist_edist : edist p r ≤ ENNReal.ofReal delta := by
    rw [← hdist_eq]; exact hinf_edist
  have hdist : dist p r ≤ delta := by
    have h := (edist_le_ofReal (by linarith)).mp hdist_edist
    exact h
  -- r = source.base + t • direction for t ∈ [0,1]
  rcases (Set.mem_image _ _ _).mp hr_seg with ⟨t, ht, rfl⟩
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  -- dist from segment point to midpoint m = |t - 1/2| ≤ 1/2
  have hdist_rm : dist (source.base + t • source.direction) m ≤ 1 / 2 := by
    have hm : m = source.base + (1 / 2 : ℝ) • source.direction := by
      rfl
    have h_eq : (source.base + t • source.direction) - m = (t - 1 / 2 : ℝ) • source.direction := by
      rw [hm]
      have h : (source.base + t • source.direction) - (source.base + (1 / 2 : ℝ) • source.direction) =
          (t - 1 / 2 : ℝ) • source.direction := by
        simp [sub_smul, smul_sub] <;> abel
      exact h
    rw [dist_eq_norm, h_eq, norm_smul, source.direction_unit]
    have h7 : ‖(t - 1 / 2 : ℝ)‖ = |t - 1 / 2| := Real.norm_eq_abs (t - 1 / 2)
    rw [h7, mul_one]
    rw [abs_le]; constructor <;> linarith
  -- triangle inequality: ‖m‖ ≤ ‖p‖ + dist p r + dist r m
  have h_final : ‖m‖ ≤ ‖p‖ + delta + 1 / 2 := by
    calc
      ‖m‖ ≤ ‖p‖ + ‖m - p‖ := by
        have h : ‖m‖ ≤ ‖p‖ + ‖p - m‖ := norm_le_norm_add_norm_sub p m
        have h9 : ‖p - m‖ = ‖m - p‖ := by rw [norm_sub_rev]
        rw [h9] at h; exact h
      _ = ‖p‖ + dist p m := by rw [← dist_eq_norm, dist_comm]
      _ ≤ ‖p‖ + (dist p (source.base + t • source.direction) + dist (source.base + t • source.direction) m) := by
        gcongr; exact dist_triangle p (source.base + t • source.direction) m
      _ ≤ ‖p‖ + delta + 1 / 2 := by linarith [hdist, hdist_rm]
  have h_bound : ‖m‖ ≤ Real.sqrt 3 + delta + 1 / 2 := by
    calc
      ‖m‖ ≤ ‖p‖ + delta + 1 / 2 := h_final
      _ ≤ Real.sqrt 3 + delta + 1 / 2 := by gcongr
  have h_le4 : Real.sqrt 3 + delta + 1 / 2 ≤ 4 := by
    have h_sqrt3_le2 : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    linarith
  linarith

end Kakeya.Assouad

end
