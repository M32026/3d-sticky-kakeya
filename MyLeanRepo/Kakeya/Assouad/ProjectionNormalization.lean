import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Coordinate normalization for WZ2 twisted projections

This module records the elementary implications and exact shear identity used
when passing from an extremal tube family to the normalized projection APIs.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Unit-ball containment bounds every tube basepoint by one. -/
lemma hasBoundedBase_of_isInUnitBall {delta : ℝ} (hdelta : 0 ≤ delta)
    {F : Kakeya.Streamlined.TubeFamily delta}
    (hF_ball : F.IsInUnitBall) :
    HasBoundedBase F 1 := by
  intro i
  have hbase_segment :
      (F.tube i).base ∈
        Kakeya.unitSegment (F.tube i).base (F.tube i).direction := by
    exact ⟨0, by norm_num, by simp [Kakeya.unitSegment]⟩
  have hbase_carrier : (F.tube i).base ∈ (F.tube i).carrier := by
    exact Metric.mem_cthickening_of_dist_le
      _ _ delta _ hbase_segment (by simpa using hdelta)
  have hbase_ball := hF_ball i hbase_carrier
  simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall,
    dist_zero_right] using hbase_ball

/-- A shading of unit-ball tubes stays in the slope window `z ∈ [-1,1]`. -/
lemma isInSlopeWindow_of_isInUnitBall {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (hF_ball : F.IsInUnitBall)
    (Y : Kakeya.Streamlined.TubeShading F) :
    IsInSlopeWindow Y := by
  intro x hx
  rcases hx with ⟨i, hxi⟩
  have hx_tube := Y.subset_body i hxi
  have hx_ball := hF_ball i hx_tube
  have hx_norm : ‖x‖ ≤ 1 := by
    simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall,
      dist_zero_right] using hx_ball
  have hz_abs : |x (2 : Fin 3)| ≤ 1 := by
    have hz_norm := PiLp.norm_apply_le x (2 : Fin 3)
    simpa [Real.norm_eq_abs] using hz_norm.trans hx_norm
  exact abs_le.mp hz_abs

/-- Slope-window containment is inherited by subshadings. -/
lemma IsInSlopeWindow.mono {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Z Y : Kakeya.Streamlined.TubeShading F}
    (hY : IsInSlopeWindow Y) (hZY : IsSubshading Z Y) :
    IsInSlopeWindow Z := by
  intro x hx
  rcases hx with ⟨i, hxi⟩
  exact hY ⟨i, hZY i hxi⟩

namespace SlopeFunction

/-- Subtract the value at zero without changing either derivative. -/
def centered (f : SlopeFunction) : SlopeFunction where
  toFun z := f z - f 0
  contDiff := f.contDiff.sub contDiff_const

@[simp]
lemma centered_apply (f : SlopeFunction) (z : ℝ) :
    f.centered z = f z - f 0 := rfl

@[simp]
lemma centered_zero (f : SlopeFunction) : f.centered 0 = 0 := by
  simp

@[simp]
lemma deriv_centered (f : SlopeFunction) (z : ℝ) :
    deriv f.centered z = deriv f z := by
  change deriv (fun x => f x - f 0) z = deriv f z
  exact deriv_sub_const (f 0)

@[simp]
lemma deriv_deriv_centered (f : SlopeFunction) (z : ℝ) :
    deriv (deriv f.centered) z = deriv (deriv f) z := by
  congr 1
  funext x
  exact deriv_centered f x

/-- Centering preserves the nonsingular slope condition. -/
lemma centered_isNonsingular {f : SlopeFunction}
    (hf : f.IsNonsingular) :
    f.centered.IsNonsingular := by
  intro z hz
  simpa using hf z hz

end SlopeFunction

/-- The horizontal shear that realizes slope centering on the source. -/
def centerSlopeShear (f : SlopeFunction) (p : Point3) : Point3 :=
  point3 (p (0 : Fin 3) - f 0 * p (1 : Fin 3))
    (p (1 : Fin 3)) (p (2 : Fin 3))

/-- Centering the slope is exactly precomposition by a horizontal shear. -/
lemma twistedProjection_centered (f : SlopeFunction) (p : Point3) :
    twistedProjection f.centered p =
      twistedProjection f (centerSlopeShear f p) := by
  ext i
  fin_cases i <;>
    simp [twistedProjection, centerSlopeShear, point3,
      EuclideanSpace.single_apply] <;> ring

end Kakeya.Assouad
