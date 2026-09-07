import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulSanity

/-!
# Extreme-case checks for the faithful PDF Lemma 8.13 freeze

These lemmas isolate the closing-scale algebra for both `T ≤ 1` and `T > 1`.
They prevent a hidden `T ≃ 1` assumption from entering the final transport.
-/

namespace Kakeya.Assouad

noncomputable section

/-- The transported Kaufman scale is independent of the affine width after
substituting `s = width / T`. -/
lemma wz1Lemma8_13_transport_scale_identity
    {normalizationWidth endpointDistance width angularScale : ℝ}
    (hnormalizationWidth : 0 < normalizationWidth)
    (hangularScale :
      angularScale = width / normalizationWidth) :
    4 * normalizationWidth * endpointDistance * angularScale =
      4 * endpointDistance * width := by
  rw [hangularScale]
  field_simp [hnormalizationWidth.ne']

/-- With `radius = 4*T*D` and `rho₀ = radius*s`, the long-projection aspect
ratio is exactly `2/s`. -/
lemma wz1Lemma8_13_transport_aspect_identity
    {radius rho₀ angularScale : ℝ}
    (hradius : 0 < radius)
    (hangularScale : 0 < angularScale)
    (hrho₀ : rho₀ = radius * angularScale) :
    2 * radius / rho₀ = 2 / angularScale := by
  rw [hrho₀]
  field_simp [hradius.ne', hangularScale.ne']

/-- The endpoint-distance lower bound supplies a uniform lower bound on the
transport radius in both aspect-ratio branches. -/
lemma wz1Lemma8_13_transport_radius_lower
    {delta epsilonOne normalizationWidth aspect endpointDistance : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hepsilonOne : 0 < epsilonOne)
    (hepsilonOneUpper : epsilonOne < 1)
    (hnormalizationWidth : 0 < normalizationWidth)
    (haspect :
      aspect = max 1 normalizationWidth)
    (hnormalizationLower :
      Real.rpow delta (1 - epsilonOne) ≤ normalizationWidth)
    (hendpointDistance :
      1 / (4 * aspect) ≤ endpointDistance) :
    Real.rpow delta (1 - epsilonOne) ≤
      4 * normalizationWidth * endpointDistance := by
  have haspectPos : 0 < aspect := by
    rw [haspect]
    exact zero_lt_one.trans_le (le_max_left _ _)
  have hdistancePositive : 0 < endpointDistance := by
    have : 0 < 1 / (4 * aspect) := by positivity
    linarith
  have hscaled :
      normalizationWidth / aspect ≤
        4 * normalizationWidth * endpointDistance := by
    have hnonnegative : 0 ≤ normalizationWidth := hnormalizationWidth.le
    calc
      normalizationWidth / aspect =
          normalizationWidth * (1 / aspect) := by ring
      _ ≤ normalizationWidth * (4 * endpointDistance) := by
        gcongr
        have := hendpointDistance
        field_simp [haspectPos.ne'] at this ⊢
        nlinarith
      _ = 4 * normalizationWidth * endpointDistance := by ring
  have hpowerOne :
      Real.rpow delta (1 - epsilonOne) ≤ 1 := by
    exact Real.rpow_le_one hdelta.le hdeltaOne (by linarith)
  have hpowerAspect :
      Real.rpow delta (1 - epsilonOne) ≤
        normalizationWidth / aspect := by
    rw [haspect]
    by_cases hlarge : 1 ≤ normalizationWidth
    · rw [max_eq_right hlarge]
      field_simp [hnormalizationWidth.ne']
      exact hpowerOne
    · have hsmall : normalizationWidth ≤ 1 :=
        le_of_not_ge hlarge
      rw [max_eq_left hsmall]
      simpa using hnormalizationLower
  exact hpowerAspect.trans hscaled

/-- Both long-projection radius conditions survive the branch
`rho = max delta rho₀`. -/
lemma wz1Lemma8_13_transport_radius_conditions
    {delta epsilon eta epsilonOne angularScale radius rho₀ : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (heta : 0 < eta)
    (hetaEpsilon : eta < epsilon)
    (hetaEpsilonOne : eta < epsilonOne)
    (hepsilonOneUpper : epsilonOne < 1)
    (hangularScale : 0 < angularScale)
    (hangularScaleUpper :
      angularScale ≤ Real.rpow delta epsilon)
    (hradius : 0 < radius)
    (hradiusLower :
      Real.rpow delta (1 - epsilonOne) ≤ radius)
    (hrho₀ : rho₀ = radius * angularScale) :
    Real.rpow delta (-eta) * rho₀ ≤ radius ∧
      Real.rpow delta (-eta) * delta ≤ radius := by
  have hangularFactor :
      Real.rpow delta (-eta) * angularScale ≤ 1 := by
    calc
      Real.rpow delta (-eta) * angularScale
          ≤ Real.rpow delta (-eta) *
              Real.rpow delta epsilon := by
            exact mul_le_mul_of_nonneg_left
              hangularScaleUpper
              (Real.rpow_nonneg hdelta.le _)
      _ = Real.rpow delta (epsilon - eta) := by
        rw [show epsilon - eta = (-eta) + epsilon by ring]
        exact (Real.rpow_add hdelta (-eta) epsilon).symm
      _ ≤ 1 := Real.rpow_le_one hdelta.le hdeltaOne
        (by linarith)
  constructor
  · rw [hrho₀]
    calc
      Real.rpow delta (-eta) *
            (radius * angularScale) =
          radius *
            (Real.rpow delta (-eta) * angularScale) := by ring
      _ ≤ radius * 1 :=
        mul_le_mul_of_nonneg_left hangularFactor hradius.le
      _ = radius := by ring
  · have hdeltaProduct :
        Real.rpow delta (-eta) * delta =
          Real.rpow delta (1 - eta) := by
      rw [show 1 - eta = (-eta) + 1 by ring]
      calc
        Real.rpow delta (-eta) * delta =
            Real.rpow delta (-eta) *
              Real.rpow delta 1 := by
                congr 1
                exact (Real.rpow_one delta).symm
        _ = Real.rpow delta ((-eta) + 1) :=
          (Real.rpow_add hdelta (-eta) 1).symm
    rw [hdeltaProduct]
    exact
      (Real.rpow_le_rpow_of_exponent_ge
        hdelta hdeltaOne (by linarith)).trans hradiusLower

/-- The explicit endpoint window yields the real coarsening-factor estimate
used when the transported scale lies below `delta`. -/
lemma wz1Lemma8_13_coarsening_factor_bound
    {delta epsilonOne rho₀ : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hepsilonOne : 0 < epsilonOne)
    (hrho₀ : 0 < rho₀)
    (hscaleLower :
      delta ≤
        3 * Real.rpow delta (-epsilonOne) * rho₀) :
    2 * delta / rho₀ + 1 ≤
      7 * Real.rpow delta (-epsilonOne) := by
  have hpowerOne :
      1 ≤ Real.rpow delta (-epsilonOne) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hdelta hdeltaOne (by linarith)
  have hquotient :
      delta / rho₀ ≤
        3 * Real.rpow delta (-epsilonOne) := by
    exact (div_le_iff₀ hrho₀).2
      (by simpa [mul_assoc] using hscaleLower)
  calc
    2 * delta / rho₀ + 1 =
        2 * (delta / rho₀) + 1 := by ring
    _ ≤
        2 * (3 * Real.rpow delta (-epsilonOne)) + 1 := by
      gcongr
    _ ≤ 7 * Real.rpow delta (-epsilonOne) := by
      linarith

/-- The endpoint-distance window gives both the upper transported scale and
the lower scale needed in the preceding coarsening estimate. -/
lemma wz1Lemma8_13_endpoint_transport_window
    {delta epsilonOne width aspect endpointDistance rho₀ : ℝ}
    (hdelta : 0 < delta)
    (hdeltaWidth : delta ≤ width)
    (haspect : 0 < aspect)
    (haspectUpper :
      aspect ≤ 3 * Real.rpow delta (-epsilonOne))
    (hendpointLower :
      1 / (4 * aspect) ≤ endpointDistance)
    (hendpointUpper : endpointDistance ≤ 2)
    (hrho₀ : rho₀ = 4 * endpointDistance * width) :
    delta ≤
        3 * Real.rpow delta (-epsilonOne) * rho₀ ∧
      rho₀ ≤ 8 * width := by
  have hwidth : 0 < width := hdelta.trans_le hdeltaWidth
  have hdistancePositive : 0 < endpointDistance := by
    have : 0 < 1 / (4 * aspect) := by positivity
    linarith
  have hone :
      1 ≤ 4 * aspect * endpointDistance := by
    have := hendpointLower
    field_simp [haspect.ne'] at this ⊢
    nlinarith
  constructor
  · rw [hrho₀]
    calc
      delta ≤ width := hdeltaWidth
      _ ≤ 4 * aspect * endpointDistance * width := by
        have hnonnegative : 0 ≤ width := hwidth.le
        nlinarith
      _ ≤
          3 * Real.rpow delta (-epsilonOne) *
            (4 * endpointDistance * width) := by
        have hfactor :
            0 ≤ 4 * endpointDistance * width := by
          positivity
        calc
          4 * aspect * endpointDistance * width =
              aspect * (4 * endpointDistance * width) := by ring
          _ ≤
              (3 * Real.rpow delta (-epsilonOne)) *
                (4 * endpointDistance * width) :=
            mul_le_mul_of_nonneg_right haspectUpper hfactor
          _ =
              3 * Real.rpow delta (-epsilonOne) *
                (4 * endpointDistance * width) := by ring
  · rw [hrho₀]
    nlinarith

end

end Kakeya.Assouad
