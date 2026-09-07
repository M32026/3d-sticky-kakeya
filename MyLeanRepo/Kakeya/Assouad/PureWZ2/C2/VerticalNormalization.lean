import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.RawGlobalGrains
import MyLeanRepo.Kakeya.Assouad.WZ1.VerticalRescalingADProof
import MyLeanRepo.Kakeya.Assouad.WZ1.TransportNormalizeAD

/-!
# Vertical normalization of a pure raw C2 slope

This is the analytic half of paper Proposition 21.  It transforms the
configuration together with its slope and records the exact projection-set
identity.  Tube-family rediscretization and pure nearby-scale CWA transport
remain separate geometric leaves.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Linear part of the Proposition 21 vertical normalization. -/
def pureWZ2VerticalRescalingLinear (halfHeight normalization : ℝ) :
    Point3 →ₗ[ℝ] Point3 where
  toFun point := point3
    (point 0 / normalization ^ 2)
    (point 1 / normalization)
    (point 2 / halfHeight)
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;>
      simp [point3] <;> ring
  map_smul' scalar point := by
    ext coordinate
    fin_cases coordinate <;>
      simp [point3] <;> ring

theorem pureWZ2VerticalRescalingLinear_injective
    {halfHeight normalization : ℝ}
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization) :
    Function.Injective
      (pureWZ2VerticalRescalingLinear halfHeight normalization) := by
  intro first second heq
  have hzero := congrArg (fun point : Point3 => point 0) heq
  have hone := congrArg (fun point : Point3 => point 1) heq
  have htwo := congrArg (fun point : Point3 => point 2) heq
  simp only [pureWZ2VerticalRescalingLinear, LinearMap.coe_mk, AddHom.coe_mk]
    at hzero hone htwo
  simp [point3] at hzero hone htwo
  change first 0 / normalization ^ 2 =
    second 0 / normalization ^ 2 at hzero
  change first 1 / normalization = second 1 / normalization at hone
  change first 2 / halfHeight = second 2 / halfHeight at htwo
  ext coordinate
  fin_cases coordinate
  · exact (div_left_inj' (pow_ne_zero 2 hnormalization.ne')).mp hzero
  · exact (div_left_inj' hnormalization.ne').mp hone
  · exact (div_left_inj' hhalfHeight.ne').mp htwo

/-- The existing vertical map as an affine equivalence. -/
noncomputable def pureWZ2VerticalRescalingAffineEquiv
    (center halfHeight normalization : ℝ)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  AffineEquiv.ofLinearEquiv
    (LinearEquiv.ofInjectiveEndo
      (pureWZ2VerticalRescalingLinear halfHeight normalization)
      (pureWZ2VerticalRescalingLinear_injective
        hhalfHeight hnormalization))
    (point3 0 0 center) 0

@[simp] theorem pureWZ2VerticalRescalingAffineEquiv_apply
    (center halfHeight normalization : ℝ)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (point : Point3) :
    pureWZ2VerticalRescalingAffineEquiv center halfHeight normalization
        hhalfHeight hnormalization point =
      wz1VerticalRescalingMap center halfHeight normalization point := by
  rw [pureWZ2VerticalRescalingAffineEquiv,
    AffineEquiv.ofLinearEquiv_apply]
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2VerticalRescalingLinear,
      wz1VerticalRescalingMap, point3] <;> ring

theorem pureWZ2VerticalRescalingLinear_det
    (halfHeight normalization : ℝ) :
    LinearMap.det
        (pureWZ2VerticalRescalingLinear halfHeight normalization) =
      1 / (normalization ^ 3 * halfHeight) := by
  let basis : Module.Basis (Fin 3) ℝ Point3 :=
    PiLp.basisFun 2 ℝ (Fin 3)
  have hmatrix :
      LinearMap.toMatrix basis basis
          (pureWZ2VerticalRescalingLinear halfHeight normalization) =
        !![1 / normalization ^ 2, 0, 0;
           0, 1 / normalization, 0;
           0, 0, 1 / halfHeight] := by
    ext i j
    have hentry :
        (LinearMap.toMatrix basis basis
          (pureWZ2VerticalRescalingLinear halfHeight normalization)) i j =
          (pureWZ2VerticalRescalingLinear halfHeight normalization
            (basis j)) i := by
      simp [LinearMap.toMatrix_apply]
      rfl
    rw [hentry]
    fin_cases i <;> fin_cases j <;>
      simp [pureWZ2VerticalRescalingLinear, point3, basis,
        PiLp.basisFun_apply, PiLp.single_apply] <;> ring
  rw [← LinearMap.det_toMatrix basis, hmatrix]
  simp [Matrix.det_fin_three]
  ring

structure PureWZ2VerticalNormalizedGlobalData
    {delta sigma rawLoss extensionConstant : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (raw :
      PureWZ2RawC2GlobalGrainData
        shading sigma C rawLoss extensionConstant)
    (center halfHeight normalization : ℝ) where
  halfHeight_pos : 0 < halfHeight
  halfHeight_le_one : halfHeight ≤ 1
  normalization_one : 1 ≤ normalization
  source_window :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      center + halfHeight * t ∈ Set.Icc (-1 : ℝ) 1
  raw_bound :
    extensionConstant * Real.rpow delta (-rawLoss) ≤ normalization
  slope : SlopeFunction :=
    wz1VerticalRescaledSlope raw.slope center halfHeight normalization
  slope_eq : slope =
    wz1VerticalRescaledSlope raw.slope center halfHeight normalization
  normalized : slope.IsNormalized
  projection_identity :
    ∀ sourceSet : Set Point3, ∀ t : ℝ,
      scalarProjection (globalGrainDirection (slope t))
          (horizontalSlice
            (wz1VerticalRescalingMap
              center halfHeight normalization '' sourceSet) t) =
        (fun value : ℝ => value / normalization ^ 2) ''
          scalarProjection
            (globalGrainDirection
              (raw.slope (center + halfHeight * t)))
            (horizontalSlice sourceSet (center + halfHeight * t))
  global_ad :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope t))
          (horizontalSlice
            (wz1VerticalRescalingMap
              center halfHeight normalization '' shading.union) t))
        (delta / normalization ^ 2) (1 - sigma) (6 * C)

theorem PureWZ2RawC2GlobalGrainData.verticalNormalize
    {delta sigma rawLoss extensionConstant : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (raw :
      PureWZ2RawC2GlobalGrainData
        shading sigma C rawLoss extensionConstant)
    (center halfHeight normalization : ℝ)
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 1 ≤ normalization)
    (hwindow : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      center + halfHeight * t ∈ Set.Icc (-1 : ℝ) 1)
    (hrawBound :
      extensionConstant * Real.rpow delta (-rawLoss) ≤ normalization) :
    Nonempty
      (PureWZ2VerticalNormalizedGlobalData
        raw center halfHeight normalization) := by
  have hbounds : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |raw.slope z| ≤ normalization ∧
        |deriv raw.slope z| ≤ normalization ∧
          |deriv (deriv raw.slope) z| ≤ normalization := by
    intro z hz
    exact
      ⟨(raw.value_bound z hz).trans hrawBound,
        (raw.first_derivative_bound z hz).trans hrawBound,
        (raw.second_derivative_bound z hz).trans hrawBound⟩
  have hnormalizationPos : 0 < normalization := by linarith
  have hnormalized :
      (wz1VerticalRescaledSlope raw.slope center
        halfHeight normalization).IsNormalized := by
    intro t ht
    have hz := hwindow t ht
    rcases hbounds (center + halfHeight * t) hz with
      ⟨hvalue, hfirst, hsecond⟩
    have hhalfAbs : |halfHeight| ≤ 1 := by
      rw [abs_of_pos hhalfHeight]
      exact hhalfHeightOne
    have hvalueNew :
        |wz1VerticalRescaledSlope raw.slope center
            halfHeight normalization t| ≤ 1 := by
      change |raw.slope (center + halfHeight * t) / normalization| ≤ 1
      rw [abs_div, abs_of_pos hnormalizationPos]
      exact (div_le_one hnormalizationPos).2 hvalue
    have hfirstNew :
        |deriv (wz1VerticalRescaledSlope raw.slope center
          halfHeight normalization) t| ≤ 1 := by
      change |deriv (fun s =>
        raw.slope (center + halfHeight * s) / normalization) t| ≤ 1
      rw [deriv_rescaled_slope, abs_div, abs_mul,
        abs_of_pos hnormalizationPos]
      calc
        |halfHeight| * |deriv raw.slope
              (center + halfHeight * t)| / normalization ≤
            1 * normalization / normalization := by gcongr
        _ = 1 := by field_simp [hnormalizationPos.ne']
    have hsecondNew :
        |deriv (deriv (wz1VerticalRescaledSlope raw.slope center
          halfHeight normalization)) t| ≤ 1 := by
      change |deriv (deriv (fun s =>
        raw.slope (center + halfHeight * s) / normalization)) t| ≤ 1
      rw [second_deriv_rescaled_slope, abs_div, abs_mul, abs_pow,
        abs_of_pos hnormalizationPos]
      have hhalfSq : |halfHeight| ^ 2 ≤ 1 := by nlinarith [abs_nonneg halfHeight]
      calc
        |halfHeight| ^ 2 *
              |deriv (deriv raw.slope)
                (center + halfHeight * t)| / normalization ≤
            1 * normalization / normalization := by gcongr
        _ = 1 := by field_simp [hnormalizationPos.ne']
    exact ⟨hvalueNew, hfirstNew, hsecondNew⟩
  have hidentity : ∀ sourceSet : Set Point3, ∀ t : ℝ,
      scalarProjection
          (globalGrainDirection
            (wz1VerticalRescaledSlope raw.slope center
              halfHeight normalization t))
          (horizontalSlice
            (wz1VerticalRescalingMap center halfHeight normalization ''
              sourceSet) t) =
        (fun value : ℝ => value / normalization ^ 2) ''
          scalarProjection
            (globalGrainDirection
              (raw.slope (center + halfHeight * t)))
            (horizontalSlice sourceSet (center + halfHeight * t)) := by
    intro sourceSet t
    exact scalar_projection_equality raw.slope center halfHeight
      normalization hhalfHeight sourceSet t
  have hglobal : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection
            (wz1VerticalRescaledSlope raw.slope center
              halfHeight normalization t))
          (horizontalSlice
            (wz1VerticalRescalingMap center halfHeight normalization ''
              shading.union) t))
        (delta / normalization ^ 2) (1 - sigma) (6 * C) := by
    intro t ht
    rw [hidentity shading.union t]
    have hsource := raw.global_ad
      (center + halfHeight * t) (hwindow t ht)
    have hscale : 0 < (1 / normalization ^ 2 : ℝ) := by positivity
    have himage := hsource.image_mul hscale
    have hset :
        (fun value : ℝ => value / normalization ^ 2) =
          fun value : ℝ => (1 / normalization ^ 2) * value := by
      funext value
      ring
    rw [hset]
    have hscaleDelta :
        (1 / normalization ^ 2) * delta =
          delta / normalization ^ 2 := by ring
    rw [hscaleDelta] at himage
    exact himage
  exact ⟨{
    halfHeight_pos := hhalfHeight
    halfHeight_le_one := hhalfHeightOne
    normalization_one := hnormalization
    source_window := hwindow
    raw_bound := hrawBound
    slope := wz1VerticalRescaledSlope raw.slope center
      halfHeight normalization
    slope_eq := rfl
    normalized := hnormalized
    projection_identity := hidentity
    global_ad := hglobal }⟩

end Kakeya.Assouad

end
