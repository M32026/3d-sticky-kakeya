import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulCanonicalCutoffScaleBound

/-!
# Polynomial bound for the faithful retention factor

The selected retained-fiber proportion is

`(t / (8 * diameter))^a * (Delta / (2 * t))^(a^2)`.

Under `delta ≤ Delta ≤ t ≤ T`, it is bounded below by the same expression
with numerators `delta` and fixed denominators.  Its inverse cube therefore
costs exactly `delta^(-(3a + 3a^2))`, up to a fixed constant.
-/

namespace Kakeya.Cinematic

lemma div_rpow_neg_eq
    (x y exponent : ℝ)
    (hx : 0 < x)
    (hy : 0 < y) :
    Real.rpow (x / y) (-exponent) =
      Real.rpow y exponent *
        Real.rpow x (-exponent) := by
  have hxy : 0 ≤ x / y := by positivity
  calc
    Real.rpow (x / y) (-exponent) =
        (Real.rpow (x / y) exponent)⁻¹ :=
      Real.rpow_neg hxy exponent
    _ =
        (Real.rpow x exponent /
          Real.rpow y exponent)⁻¹ := by
      exact congrArg (fun z : ℝ => z⁻¹)
        (Real.div_rpow hx.le hy.le exponent)
    _ =
        Real.rpow y exponent /
          Real.rpow x exponent := by
      exact inv_div _ _
    _ =
        Real.rpow y exponent *
          (Real.rpow x exponent)⁻¹ := by
      rw [div_eq_mul_inv]
    _ =
        Real.rpow y exponent *
          Real.rpow x (-exponent) := by
      exact congrArg
        (fun z : ℝ => Real.rpow y exponent * z)
        (Real.rpow_neg hx.le exponent).symm

lemma canonical_retention_lower_bound
    (delta t Delta diameter T metricExponent : ℝ)
    (hdelta : 0 < delta)
    (hdiameter : 0 < diameter)
    (hT : 0 < T)
    (hmetric : 0 ≤ metricExponent)
    (hdeltaDelta : delta ≤ Delta)
    (hDeltaT : Delta ≤ t)
    (htT : t ≤ T) :
    Real.rpow (delta / (8 * diameter)) metricExponent *
          Real.rpow (delta / (2 * T)) (metricExponent ^ 2) ≤
      Real.rpow (t / (8 * diameter)) metricExponent *
        Real.rpow (Delta / (2 * t)) (metricExponent ^ 2) := by
  have ht : 0 < t := hdelta.trans_le (hdeltaDelta.trans hDeltaT)
  have hfirstBase :
      delta / (8 * diameter) ≤
        t / (8 * diameter) := by
    exact div_le_div_of_nonneg_right
      (hdeltaDelta.trans hDeltaT) (by positivity)
  have hsecondBase :
      delta / (2 * T) ≤
        Delta / (2 * t) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have hfirst :
      Real.rpow (delta / (8 * diameter)) metricExponent ≤
        Real.rpow (t / (8 * diameter)) metricExponent :=
    Real.rpow_le_rpow (by positivity) hfirstBase hmetric
  have hsecond :
      Real.rpow (delta / (2 * T)) (metricExponent ^ 2) ≤
        Real.rpow (Delta / (2 * t)) (metricExponent ^ 2) :=
    Real.rpow_le_rpow (by positivity) hsecondBase
      (sq_nonneg metricExponent)
  exact mul_le_mul hfirst hsecond
    (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (by positivity) _)

lemma canonical_retention_inv_le
    (delta t Delta diameter T metricExponent : ℝ)
    (hdelta : 0 < delta)
    (hdiameter : 0 < diameter)
    (hT : 0 < T)
    (hmetric : 0 ≤ metricExponent)
    (hdeltaDelta : delta ≤ Delta)
    (hDeltaT : Delta ≤ t)
    (htT : t ≤ T) :
    Real.rpow
        (Real.rpow (t / (8 * diameter)) metricExponent *
          Real.rpow (Delta / (2 * t)) (metricExponent ^ 2))
        (-1) ≤
      (Real.rpow (8 * diameter) metricExponent *
          Real.rpow (2 * T) (metricExponent ^ 2)) *
        Real.rpow delta
          (-(metricExponent + metricExponent ^ 2)) := by
  let lowerRetention :=
    Real.rpow (delta / (8 * diameter)) metricExponent *
      Real.rpow (delta / (2 * T)) (metricExponent ^ 2)
  let retention :=
    Real.rpow (t / (8 * diameter)) metricExponent *
      Real.rpow (Delta / (2 * t)) (metricExponent ^ 2)
  have ht : 0 < t := hdelta.trans_le (hdeltaDelta.trans hDeltaT)
  have hlowerPos : 0 < lowerRetention := by
    dsimp only [lowerRetention]
    exact mul_pos
      (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_pos_of_pos (by positivity) _)
  have hretentionPos : 0 < retention := by
    dsimp only [retention]
    have hDelta : 0 < Delta := hdelta.trans_le hdeltaDelta
    exact mul_pos
      (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_pos_of_pos (by positivity) _)
  have hlower : lowerRetention ≤ retention := by
    dsimp only [lowerRetention, retention]
    exact canonical_retention_lower_bound
      delta t Delta diameter T metricExponent
      hdelta hdiameter hT hmetric hdeltaDelta hDeltaT htT
  have hinverse :
      Real.rpow retention (-1) ≤
        Real.rpow lowerRetention (-1) := by
    exact
      (Real.rpow_le_rpow_iff_of_neg
        hretentionPos hlowerPos (by norm_num)).2 hlower
  have hfirst :
      Real.rpow
          (Real.rpow (delta / (8 * diameter)) metricExponent)
          (-1) =
        Real.rpow (8 * diameter) metricExponent *
          Real.rpow delta (-metricExponent) := by
    calc
      Real.rpow
          (Real.rpow (delta / (8 * diameter)) metricExponent)
          (-1) =
        Real.rpow (delta / (8 * diameter))
          (metricExponent * (-1)) := by
            exact
              (Real.rpow_mul (by positivity)
                metricExponent (-1)).symm
      _ = Real.rpow (delta / (8 * diameter))
          (-metricExponent) := by
            congr 1
            ring
      _ = Real.rpow (8 * diameter) metricExponent *
          Real.rpow delta (-metricExponent) :=
        div_rpow_neg_eq delta (8 * diameter)
          metricExponent hdelta (by positivity)
  have hsecond :
      Real.rpow
          (Real.rpow (delta / (2 * T)) (metricExponent ^ 2))
          (-1) =
        Real.rpow (2 * T) (metricExponent ^ 2) *
          Real.rpow delta (-(metricExponent ^ 2)) := by
    calc
      Real.rpow
          (Real.rpow (delta / (2 * T)) (metricExponent ^ 2))
          (-1) =
        Real.rpow (delta / (2 * T))
          (metricExponent ^ 2 * (-1)) := by
            exact
              (Real.rpow_mul (by positivity)
                (metricExponent ^ 2) (-1)).symm
      _ = Real.rpow (delta / (2 * T))
          (-(metricExponent ^ 2)) := by
            congr 1
            ring
      _ = Real.rpow (2 * T) (metricExponent ^ 2) *
          Real.rpow delta (-(metricExponent ^ 2)) :=
        div_rpow_neg_eq delta (2 * T)
          (metricExponent ^ 2) hdelta (by positivity)
  have hlowerPower :
      Real.rpow lowerRetention (-1) =
        (Real.rpow (8 * diameter) metricExponent *
            Real.rpow (2 * T) (metricExponent ^ 2)) *
          Real.rpow delta
            (-(metricExponent + metricExponent ^ 2)) := by
    have hmul :
        Real.rpow lowerRetention (-1) =
          Real.rpow
              (Real.rpow (delta / (8 * diameter)) metricExponent)
              (-1) *
            Real.rpow
              (Real.rpow (delta / (2 * T)) (metricExponent ^ 2))
              (-1) := by
      dsimp only [lowerRetention]
      exact Real.mul_rpow
        (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg (by positivity) _)
    have hdeltaPowers :
        Real.rpow delta (-metricExponent) *
            Real.rpow delta (-(metricExponent ^ 2)) =
          Real.rpow delta
            (-(metricExponent + metricExponent ^ 2)) := by
      calc
        Real.rpow delta (-metricExponent) *
              Real.rpow delta (-(metricExponent ^ 2)) =
            Real.rpow delta
              (-metricExponent + -(metricExponent ^ 2)) :=
          (Real.rpow_add hdelta _ _).symm
        _ = Real.rpow delta
              (-(metricExponent + metricExponent ^ 2)) := by
          congr 1
          ring
    rw [hmul, hfirst, hsecond, ← hdeltaPowers]
    ring
  simpa only [retention] using hinverse.trans_eq hlowerPower

lemma canonical_retention_inv_cube_le
    (delta t Delta diameter T metricExponent : ℝ)
    (hdelta : 0 < delta)
    (hdiameter : 0 < diameter)
    (hT : 0 < T)
    (hmetric : 0 ≤ metricExponent)
    (hdeltaDelta : delta ≤ Delta)
    (hDeltaT : Delta ≤ t)
    (htT : t ≤ T) :
    Real.rpow
        (Real.rpow (t / (8 * diameter)) metricExponent *
          Real.rpow (Delta / (2 * t)) (metricExponent ^ 2))
        (-3) ≤
      (Real.rpow (8 * diameter) (3 * metricExponent) *
          Real.rpow (2 * T) (3 * metricExponent ^ 2)) *
        Real.rpow delta
          (-(3 * metricExponent + 3 * metricExponent ^ 2)) := by
  let lowerRetention :=
    Real.rpow (delta / (8 * diameter)) metricExponent *
      Real.rpow (delta / (2 * T)) (metricExponent ^ 2)
  let retention :=
    Real.rpow (t / (8 * diameter)) metricExponent *
      Real.rpow (Delta / (2 * t)) (metricExponent ^ 2)
  have ht : 0 < t := hdelta.trans_le (hdeltaDelta.trans hDeltaT)
  have hlowerPos : 0 < lowerRetention := by
    dsimp only [lowerRetention]
    exact mul_pos
      (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_pos_of_pos (by positivity) _)
  have hretentionPos : 0 < retention := by
    dsimp only [retention]
    have hfirstBase : 0 < t / (8 * diameter) := by
      positivity
    have hsecondBase : 0 < Delta / (2 * t) := by
      have hDelta : 0 < Delta :=
        hdelta.trans_le hdeltaDelta
      positivity
    exact mul_pos
      (Real.rpow_pos_of_pos hfirstBase _)
      (Real.rpow_pos_of_pos hsecondBase _)
  have hlower : lowerRetention ≤ retention := by
    dsimp only [lowerRetention, retention]
    exact canonical_retention_lower_bound
      delta t Delta diameter T metricExponent
      hdelta hdiameter hT hmetric hdeltaDelta hDeltaT htT
  have hinverse :
      Real.rpow retention (-3) ≤
        Real.rpow lowerRetention (-3) := by
    exact
      (Real.rpow_le_rpow_iff_of_neg
        hretentionPos hlowerPos (by norm_num)).2 hlower
  have hfirst :
      Real.rpow
          (Real.rpow (delta / (8 * diameter)) metricExponent)
          (-3) =
        Real.rpow (8 * diameter) (3 * metricExponent) *
          Real.rpow delta (-(3 * metricExponent)) := by
    calc
      Real.rpow
          (Real.rpow (delta / (8 * diameter)) metricExponent)
          (-3) =
        Real.rpow (delta / (8 * diameter))
          (metricExponent * (-3)) := by
            exact
              (Real.rpow_mul (by positivity)
                metricExponent (-3)).symm
      _ =
        Real.rpow (delta / (8 * diameter))
          (-(3 * metricExponent)) := by
            congr 1
            ring
      _ =
        Real.rpow (8 * diameter) (3 * metricExponent) *
          Real.rpow delta (-(3 * metricExponent)) :=
        div_rpow_neg_eq delta (8 * diameter)
          (3 * metricExponent) hdelta (by positivity)
  have hsecond :
      Real.rpow
          (Real.rpow (delta / (2 * T)) (metricExponent ^ 2))
          (-3) =
        Real.rpow (2 * T) (3 * metricExponent ^ 2) *
          Real.rpow delta (-(3 * metricExponent ^ 2)) := by
    calc
      Real.rpow
          (Real.rpow (delta / (2 * T)) (metricExponent ^ 2))
          (-3) =
        Real.rpow (delta / (2 * T))
          (metricExponent ^ 2 * (-3)) := by
            exact
              (Real.rpow_mul (by positivity)
                (metricExponent ^ 2) (-3)).symm
      _ =
        Real.rpow (delta / (2 * T))
          (-(3 * metricExponent ^ 2)) := by
            congr 1
            ring
      _ =
        Real.rpow (2 * T) (3 * metricExponent ^ 2) *
          Real.rpow delta (-(3 * metricExponent ^ 2)) :=
        div_rpow_neg_eq delta (2 * T)
          (3 * metricExponent ^ 2) hdelta (by positivity)
  have hlowerPower :
      Real.rpow lowerRetention (-3) =
        (Real.rpow (8 * diameter) (3 * metricExponent) *
            Real.rpow (2 * T) (3 * metricExponent ^ 2)) *
          Real.rpow delta
            (-(3 * metricExponent + 3 * metricExponent ^ 2)) := by
    have hmul :
        Real.rpow lowerRetention (-3) =
          Real.rpow
              (Real.rpow (delta / (8 * diameter)) metricExponent)
              (-3) *
            Real.rpow
              (Real.rpow (delta / (2 * T)) (metricExponent ^ 2))
              (-3) := by
      dsimp only [lowerRetention]
      exact Real.mul_rpow
        (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg (by positivity) _)
    have hdeltaPowers :
        Real.rpow delta (-(3 * metricExponent)) *
            Real.rpow delta (-(3 * metricExponent ^ 2)) =
          Real.rpow delta
            (-(3 * metricExponent + 3 * metricExponent ^ 2)) := by
      calc
        Real.rpow delta (-(3 * metricExponent)) *
              Real.rpow delta (-(3 * metricExponent ^ 2)) =
            Real.rpow delta
              (-(3 * metricExponent) +
                -(3 * metricExponent ^ 2)) :=
          (Real.rpow_add hdelta _ _).symm
        _ = Real.rpow delta
              (-(3 * metricExponent +
                3 * metricExponent ^ 2)) := by
          congr 1
          ring
    rw [hmul, hfirst, hsecond, ← hdeltaPowers]
    ring
  simpa only [retention] using hinverse.trans_eq hlowerPower

end Kakeya.Cinematic
