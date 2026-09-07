import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.OffsetProjectiveTotalNormal

/-!
# Fixed-scale projective normal transport

The preceding exact-image transport has Lipschitz constant `6*K/lambda`.
For the source constant `K = 10100`, the pre-runtime choice
`lambda = 60600 = 6 * 10100` makes this constant exactly one.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The fixed horizontal normalization scale used before the runtime data are
chosen.  Its value is exactly `6 * 10100`. -/
def pureWZ2FixedProjectiveNormalLambda : ℝ := 60600

theorem pureWZ2FixedProjectiveNormalLambda_eq :
    pureWZ2FixedProjectiveNormalLambda = 6 * 10100 := by
  norm_num [pureWZ2FixedProjectiveNormalLambda]

theorem pureWZ2FixedProjectiveNormalLambda_one_le :
    1 ≤ pureWZ2FixedProjectiveNormalLambda := by
  norm_num [pureWZ2FixedProjectiveNormalLambda]

/-- At the pre-runtime fixed scale, exact-image projective normal transport
turns a `10100`-Lipschitz source field into a unit-Lipschitz normalized field.
This contains no extension or saturation step. -/
theorem pureWZ2FixedProjectiveNormal_exactImage_lipschitz
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {b S : ℝ} {preimage : X → Y} {field : Y → Point3}
    (hb : 0 < b) (hb_one : b ≤ 1) (hS : 1 ≤ S)
    (hpreimage : ∀ first second,
      b * dist (preimage first) (preimage second) ≤ 3 * dist first second)
    (hfield : LipschitzWith 10100 field)
    (hcoord : ∀ point, field point 1 = 1) :
    LipschitzWith 1
      (fun point => pureWZ2OffsetProjectiveTotalNormalizedNormal b S
        pureWZ2FixedProjectiveNormalLambda (field (preimage point))) := by
  have htransport := pureWZ2OffsetProjectiveTotalNormalizedNormal_lipschitz_preimage
    (b := b) (S := S) (lambda := pureWZ2FixedProjectiveNormalLambda)
    (K := (10100 : NNReal)) hb hb_one hS pureWZ2FixedProjectiveNormalLambda_one_le
    hpreimage hfield hcoord
  norm_num [pureWZ2FixedProjectiveNormalLambda] at htransport
  exact htransport

/-- Before unit normalization, the fixed-scale projective chart is
`1/2`-Lipschitz on the exact image.  This sharper form is used by the
chart-preserving saturation extension. -/
theorem pureWZ2FixedProjectiveNormal_exactImage_chart_lipschitz
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {b S : ℝ} {preimage : X → Y} {field : Y → Point3}
    (hb : 0 < b) (hS : 1 ≤ S)
    (hpreimage : ∀ first second,
      b * dist (preimage first) (preimage second) ≤ 3 * dist first second)
    (hfield : LipschitzWith 10100 field)
    (hcoord : ∀ point, field point 1 = 1) :
    LipschitzWith (1 / 2 : NNReal)
      (fun point => pureWZ2OffsetProjectiveTotalNormal b S
        pureWZ2FixedProjectiveNormalLambda (field (preimage point))) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [dist_eq_norm]
  have hlambda : 1 ≤ pureWZ2FixedProjectiveNormalLambda :=
    pureWZ2FixedProjectiveNormalLambda_one_le
  have hfieldDist := hfield.dist_le_mul (preimage first) (preimage second)
  rw [dist_eq_norm] at hfieldDist
  calc
    ‖pureWZ2OffsetProjectiveTotalNormal b S
          pureWZ2FixedProjectiveNormalLambda (field (preimage first)) -
        pureWZ2OffsetProjectiveTotalNormal b S
          pureWZ2FixedProjectiveNormalLambda (field (preimage second))‖ ≤
      (b / pureWZ2FixedProjectiveNormalLambda) *
        ‖field (preimage first) - field (preimage second)‖ :=
          pureWZ2OffsetProjectiveTotalNormal_sub_norm_le hb hS hlambda _ _
            (hcoord _) (hcoord _)
    _ ≤ (b / pureWZ2FixedProjectiveNormalLambda) *
        ((10100 : ℝ) * dist (preimage first) (preimage second)) := by
          exact mul_le_mul_of_nonneg_left (by
            have hfieldDist' :
                ‖field (preimage first) - field (preimage second)‖ ≤
                  ((10100 : NNReal) : ℝ) *
                    dist (preimage first) (preimage second) := hfieldDist
            norm_num at hfieldDist' ⊢
            exact hfieldDist')
            (div_nonneg hb.le
              (zero_lt_one.trans_le hlambda).le)
    _ = (10100 / pureWZ2FixedProjectiveNormalLambda) *
        (b * dist (preimage first) (preimage second)) := by ring
    _ ≤ (10100 / pureWZ2FixedProjectiveNormalLambda) *
        (3 * dist first second) := by
          exact mul_le_mul_of_nonneg_left (hpreimage first second)
            (div_nonneg (by norm_num)
              (zero_lt_one.trans_le hlambda).le)
    _ = (((1 / 2 : NNReal) : NNReal) : ℝ) * dist first second := by
          norm_num [pureWZ2FixedProjectiveNormalLambda]
          ring

/-- On sources with vertical stretch at least `50`, the third projective
chart coordinate is `1/100`-Lipschitz on the exact image. -/
theorem pureWZ2FixedProjectiveNormal_exactImage_chart_coord_two_lipschitz
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {b S : ℝ} {preimage : X → Y} {field : Y → Point3}
    (hb : 0 < b) (hS : 50 ≤ S)
    (hpreimage : ∀ first second,
      b * dist (preimage first) (preimage second) ≤ 3 * dist first second)
    (hfield : LipschitzWith 10100 field) :
    LipschitzWith (1 / 100 : NNReal)
      (fun point =>
        pureWZ2OffsetProjectiveTotalNormal b S
          pureWZ2FixedProjectiveNormalLambda (field (preimage point)) 2) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [Real.dist_eq]
  have hSPos : 0 < S := by linarith
  have hlambdaPos : 0 < pureWZ2FixedProjectiveNormalLambda := by
    norm_num [pureWZ2FixedProjectiveNormalLambda]
  have hfieldDist := hfield.dist_le_mul (preimage first) (preimage second)
  rw [dist_eq_norm] at hfieldDist
  have hcoordBound := PiLp.norm_apply_le
    (field (preimage first) - field (preimage second)) (2 : Fin 3)
  rw [Real.norm_eq_abs] at hcoordBound
  have hcoordinate :
      |field (preimage first) 2 - field (preimage second) 2| ≤
        (10100 : ℝ) * dist (preimage first) (preimage second) :=
    hcoordBound.trans (by
      have hfieldDist' :
          ‖field (preimage first) - field (preimage second)‖ ≤
            ((10100 : NNReal) : ℝ) *
              dist (preimage first) (preimage second) := hfieldDist
      norm_num at hfieldDist' ⊢
      exact hfieldDist')
  simp only [pureWZ2OffsetProjectiveTotalNormal, point3_coord2]
  rw [← mul_sub, abs_mul, abs_of_pos
    (div_pos hb (mul_pos hlambdaPos hSPos))]
  calc
    b / (pureWZ2FixedProjectiveNormalLambda * S) *
        |field (preimage first) 2 - field (preimage second) 2| ≤
      b / (pureWZ2FixedProjectiveNormalLambda * S) *
        ((10100 : ℝ) * dist (preimage first) (preimage second)) := by
          exact mul_le_mul_of_nonneg_left hcoordinate
            (div_nonneg hb.le (mul_pos hlambdaPos hSPos).le)
    _ = (10100 / (pureWZ2FixedProjectiveNormalLambda * S)) *
        (b * dist (preimage first) (preimage second)) := by ring
    _ ≤ (10100 / (pureWZ2FixedProjectiveNormalLambda * S)) *
        (3 * dist first second) := by
          exact mul_le_mul_of_nonneg_left (hpreimage first second)
            (div_nonneg (by norm_num) (mul_pos hlambdaPos hSPos).le)
    _ ≤ (1 / 100 : ℝ) * dist first second := by
      have hdist : 0 ≤ dist first second := dist_nonneg
      have hcoefficient :
          3 * 10100 / (pureWZ2FixedProjectiveNormalLambda * S) ≤
            1 / 100 := by
        rw [div_le_iff₀ (mul_pos hlambdaPos hSPos)]
        norm_num [pureWZ2FixedProjectiveNormalLambda] at *
        nlinarith
      calc
        (10100 / (pureWZ2FixedProjectiveNormalLambda * S)) *
            (3 * dist first second) =
          (3 * 10100 / (pureWZ2FixedProjectiveNormalLambda * S)) *
            dist first second := by ring
        _ ≤ (1 / 100 : ℝ) * dist first second :=
          mul_le_mul_of_nonneg_right hcoefficient hdist
    _ = (((1 / 100 : NNReal) : NNReal) : ℝ) * dist first second := by
      norm_num

end Kakeya.Assouad

end
