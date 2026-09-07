import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicJointLocalGrains

/-!
# Scalar budgets for final-isotropic local grains

This module records the one final similarity scale used to normalize the
exact inverse-transpose normal and to absorb the target-grid saturation.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The fixed post-normalization Lipschitz constant. -/
def pureWZ2FinalIsotropicTargetK : NNReal :=
  ⟨1 / (16 * (lipschitzExtensionConstant Point3 : NNReal)), by
    exact div_nonneg (by norm_num)
      (mul_nonneg (by norm_num) (lipschitzExtensionConstant Point3).2)⟩

/-- A concrete scale large enough both to normalize the exact normal and to
pay for inverse-ball distortion. -/
def pureWZ2IsotropicJointRequiredScale
    {sourceDelta preDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) sourceFamily sourceShading g center hcd hm}
    {sourceLocal : PureWZ2LocalGrainData sourceShading sigma C}
    (exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal) : ℝ :=
  max 1 <| max
    (16 * (lipschitzExtensionConstant Point3 : ℝ) * (exact.K : ℝ))
    (25 * (2 / (d - c) + 2) *
      ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
        |>.toContinuousLinearEquiv.toContinuousLinearMap‖ ^ 2)

/-- Quantitative data required of the final isotropic normalization. -/
structure PureWZ2IsotropicJointLocalScaleData
    {sourceDelta preDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) sourceFamily sourceShading g center hcd hm}
    {sourceLocal : PureWZ2LocalGrainData sourceShading sigma C}
    (exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal) where
  scale : ℝ
  scale_pos : 0 < scale
  scale_one : 1 ≤ scale
  finalDelta : ℝ
  finalDelta_eq : finalDelta = 16 * scale * preDelta
  finalDelta_pos : 0 < finalDelta
  finalDelta_le_quarter : finalDelta ≤ 1 / 4
  exact_lipschitz : (exact.K : ℝ) ≤
    (pureWZ2FinalIsotropicTargetK : ℝ) * scale
  inverse_ball_budget :
    25 * (2 / (d - c) + 2) *
        ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ ^ 2 ≤ scale
  sourceDelta_pos : 0 < sourceDelta
  sourceDelta_le_preDelta : sourceDelta ≤ preDelta
  source_scale_budget :
    sourceDelta * (2 / (d - c) + 2) ≤ 16 * preDelta
  normal_lower : ∀ point,
    1 / (2 / (d - c) + 2) ≤
      ‖dPhiInvT g c d m (sourceLocal.planeMap point)‖

/-- Construct the scale record from its only genuine smallness condition.
The selected scale itself is the maximum of the two finite distortion costs
and one. -/
theorem exists_pureWZ2_isotropicJointLocalScaleData
    {sourceDelta preDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) sourceFamily sourceShading g center hcd hm}
    {sourceLocal : PureWZ2LocalGrainData sourceShading sigma C}
    (exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal)
    (hsourceDeltaPos : 0 < sourceDelta)
    (hpreDeltaPos : 0 < preDelta)
    (hsourcePre : sourceDelta ≤ preDelta)
    (hsourceScale : sourceDelta * (2 / (d - c) + 2) ≤ 16 * preDelta)
    (hnormal : ∀ point, 1 / (2 / (d - c) + 2) ≤
      ‖dPhiInvT g c d m (sourceLocal.planeMap point)‖)
    (hroom : pureWZ2IsotropicJointRequiredScale exact * preDelta ≤ 1 / 64) :
    Nonempty (PureWZ2IsotropicJointLocalScaleData exact) := by
  let scale := pureWZ2IsotropicJointRequiredScale exact
  let finalDelta := 16 * scale * preDelta
  have hLNonneg : 0 ≤ (lipschitzExtensionConstant Point3 : ℝ) :=
    (lipschitzExtensionConstant Point3).2
  have hscaleOne : 1 ≤ scale := by
    dsimp only [scale, pureWZ2IsotropicJointRequiredScale]
    exact le_max_left _ _
  have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscaleOne
  have hscaleExact :
      16 * (lipschitzExtensionConstant Point3 : ℝ) * (exact.K : ℝ) ≤ scale := by
    dsimp only [scale, pureWZ2IsotropicJointRequiredScale]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hscaleInverse : 25 * (2 / (d - c) + 2) *
      ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
        |>.toContinuousLinearEquiv.toContinuousLinearMap‖ ^ 2 ≤ scale := by
    dsimp only [scale, pureWZ2IsotropicJointRequiredScale]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hfinalPos : 0 < finalDelta := by
    dsimp only [finalDelta]
    positivity
  have hfinalQuarter : finalDelta ≤ 1 / 4 := by
    dsimp only [finalDelta]
    calc
      16 * scale * preDelta = 16 * (scale * preDelta) := by ring
      _ ≤ 16 * (1 / 64 : ℝ) := by gcongr
      _ = 1 / 4 := by norm_num
  have hexactLipschitz : (exact.K : ℝ) ≤
      (pureWZ2FinalIsotropicTargetK : ℝ) * scale := by
    have hLPos : 0 < (lipschitzExtensionConstant Point3 : ℝ) :=
      lipschitzExtensionConstant_pos Point3
    change (exact.K : ℝ) ≤
      (1 / (16 * (lipschitzExtensionConstant Point3 : ℝ))) * scale
    rw [show (1 / (16 * (lipschitzExtensionConstant Point3 : ℝ))) * scale =
        scale / (16 * (lipschitzExtensionConstant Point3 : ℝ)) by ring]
    exact (le_div_iff₀ (mul_pos (by norm_num) hLPos)).2 <| by
      nlinarith
  exact ⟨{
    scale := scale
    scale_pos := hscalePos
    scale_one := hscaleOne
    finalDelta := finalDelta
    finalDelta_eq := rfl
    finalDelta_pos := hfinalPos
    finalDelta_le_quarter := hfinalQuarter
    exact_lipschitz := hexactLipschitz
    inverse_ball_budget := hscaleInverse
    sourceDelta_pos := hsourceDeltaPos
    sourceDelta_le_preDelta := hsourcePre
    source_scale_budget := hsourceScale
    normal_lower := hnormal
  }⟩

namespace PureWZ2IsotropicJointLocalScaleData

theorem targetK_mul_scale
    {sourceDelta preDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) sourceFamily sourceShading g center hcd hm}
    {sourceLocal : PureWZ2LocalGrainData sourceShading sigma C}
    {exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal}
    (data : PureWZ2IsotropicJointLocalScaleData exact) :
    (exact.K : ℝ) ≤ (pureWZ2FinalIsotropicTargetK : ℝ) * data.scale := by
  exact data.exact_lipschitz

theorem extension_small
    {sourceDelta preDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) sourceFamily sourceShading g center hcd hm}
    {sourceLocal : PureWZ2LocalGrainData sourceShading sigma C}
    {exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal}
    (data : PureWZ2IsotropicJointLocalScaleData exact) :
    ((lipschitzExtensionConstant Point3 * pureWZ2FinalIsotropicTargetK :
        NNReal) : ℝ) * (data.finalDelta * Real.sqrt 3) ≤ 1 / 2 := by
  have hsqrt : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_nonneg 3]
  have hLPos : 0 < (lipschitzExtensionConstant Point3 : ℝ) :=
    lipschitzExtensionConstant_pos Point3
  change (lipschitzExtensionConstant Point3 : ℝ) *
      (1 / (16 * (lipschitzExtensionConstant Point3 : ℝ))) *
        (data.finalDelta * Real.sqrt 3) ≤ 1 / 2
  have hproduct : data.finalDelta * Real.sqrt 3 ≤ 1 / 2 := by
    calc
      data.finalDelta * Real.sqrt 3 ≤ (1 / 4 : ℝ) * 2 :=
        mul_le_mul data.finalDelta_le_quarter hsqrt
          (Real.sqrt_nonneg 3) (by norm_num)
      _ = 1 / 2 := by norm_num
  field_simp [hLPos.ne']
  nlinarith

theorem extension_one
    {sourceDelta preDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) sourceFamily sourceShading g center hcd hm}
    {sourceLocal : PureWZ2LocalGrainData sourceShading sigma C}
    {exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal}
    (_data : PureWZ2IsotropicJointLocalScaleData exact) :
    4 * ((lipschitzExtensionConstant Point3 *
      pureWZ2FinalIsotropicTargetK : NNReal) : ℝ) ≤ 1 := by
  have hLPos : 0 < (lipschitzExtensionConstant Point3 : ℝ) :=
    lipschitzExtensionConstant_pos Point3
  change 4 * ((lipschitzExtensionConstant Point3 : ℝ) *
    (1 / (16 * (lipschitzExtensionConstant Point3 : ℝ)))) ≤ 1
  field_simp [hLPos.ne']
  norm_num

theorem extension_error_eq
    {sourceDelta preDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) sourceFamily sourceShading g center hcd hm}
    {sourceLocal : PureWZ2LocalGrainData sourceShading sigma C}
    {exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal}
    (_data : PureWZ2IsotropicJointLocalScaleData exact) :
    4 * ((lipschitzExtensionConstant Point3 *
        pureWZ2FinalIsotropicTargetK : NNReal) : ℝ) *
        (_data.finalDelta * Real.sqrt 3) =
      (_data.finalDelta * Real.sqrt 3) / 4 := by
  have hLPos : 0 < (lipschitzExtensionConstant Point3 : ℝ) :=
    lipschitzExtensionConstant_pos Point3
  change 4 * ((lipschitzExtensionConstant Point3 : ℝ) *
      (1 / (16 * (lipschitzExtensionConstant Point3 : ℝ)))) *
      (_data.finalDelta * Real.sqrt 3) = _
  field_simp [hLPos.ne']
  ring

def sourceRho
    {sourceDelta preDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) sourceFamily sourceShading g center hcd hm}
    {sourceLocal : PureWZ2LocalGrainData sourceShading sigma C}
    {exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal}
    (data : PureWZ2IsotropicJointLocalScaleData exact) (rho : ℝ) : ℝ :=
  rho / (data.scale * (2 / (d - c) + 2))

theorem incidence_budget
    {sourceDelta preDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) sourceFamily sourceShading g center hcd hm}
    {sourceLocal : PureWZ2LocalGrainData sourceShading sigma C}
    {exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal}
    (data : PureWZ2IsotropicJointLocalScaleData exact) :
    3 * sourceDelta +
        4 * ((lipschitzExtensionConstant Point3 *
          pureWZ2FinalIsotropicTargetK : NNReal) : ℝ) *
          (data.finalDelta * Real.sqrt 3) ≤ data.finalDelta := by
  rw [data.extension_error_eq]
  have hsqrt : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_nonneg 3]
  have herror : data.finalDelta * Real.sqrt 3 / 4 ≤
      data.finalDelta / 2 := by
    have := mul_le_mul_of_nonneg_left hsqrt data.finalDelta_pos.le
    nlinarith
  have hsource : 6 * sourceDelta ≤ data.finalDelta := by
    have hpreDeltaNonneg : 0 ≤ preDelta :=
      data.sourceDelta_pos.le.trans data.sourceDelta_le_preDelta
    have hscaled : sourceDelta ≤ data.scale * preDelta :=
      data.sourceDelta_le_preDelta.trans <|
        (le_mul_of_one_le_left hpreDeltaNonneg data.scale_one)
    calc
      6 * sourceDelta ≤ 6 * (data.scale * preDelta) := by gcongr
      _ ≤ 16 * (data.scale * preDelta) :=
        mul_le_mul_of_nonneg_right (by norm_num)
          (mul_nonneg data.scale_pos.le hpreDeltaNonneg)
      _ = 16 * data.scale * preDelta := by ring
      _ = data.finalDelta := data.finalDelta_eq.symm
  nlinarith

theorem projection_budget
    {sourceDelta preDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) sourceFamily sourceShading g center hcd hm}
    {sourceLocal : PureWZ2LocalGrainData sourceShading sigma C}
    {exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal}
    (data : PureWZ2IsotropicJointLocalScaleData exact) :
    data.finalDelta * Real.sqrt 3 +
        (Real.sqrt 3 / 200) *
          (4 * ((lipschitzExtensionConstant Point3 *
            pureWZ2FinalIsotropicTargetK : NNReal) : ℝ) *
              (data.finalDelta * Real.sqrt 3)) ≤
      2 * data.finalDelta := by
  rw [data.extension_error_eq]
  have hsqrtNonneg := Real.sqrt_nonneg 3
  have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsqrt : Real.sqrt 3 ≤ 7 / 4 := by nlinarith
  have hsqrtMul : Real.sqrt 3 * Real.sqrt 3 = 3 := by nlinarith
  calc
    data.finalDelta * Real.sqrt 3 +
        Real.sqrt 3 / 200 * (data.finalDelta * Real.sqrt 3 / 4) =
      data.finalDelta * (Real.sqrt 3 + 3 / 800) := by
        calc
          _ = data.finalDelta * Real.sqrt 3 +
              data.finalDelta * (Real.sqrt 3 * Real.sqrt 3) / 800 := by ring
          _ = _ := by rw [hsqrtMul] <;> ring
    _ ≤ data.finalDelta * (7 / 4 + 3 / 800) := by
      exact mul_le_mul_of_nonneg_left (by linarith) data.finalDelta_pos.le
    _ ≤ 2 * data.finalDelta := by
      nlinarith [data.finalDelta_pos]

theorem sourceRho_lower
    {sourceDelta preDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) sourceFamily sourceShading g center hcd hm}
    {sourceLocal : PureWZ2LocalGrainData sourceShading sigma C}
    {exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal}
    (data : PureWZ2IsotropicJointLocalScaleData exact)
    {rho : ℝ} (hrhoLower : data.finalDelta ≤ rho) :
    sourceDelta ≤ data.sourceRho rho := by
  have hqPos : 0 < 2 / (d - c) + 2 := by positivity
  have hdenomPos : 0 < data.scale * (2 / (d - c) + 2) :=
    mul_pos data.scale_pos hqPos
  rw [sourceRho, le_div_iff₀ hdenomPos]
  calc
    sourceDelta * (data.scale * (2 / (d - c) + 2)) =
        data.scale * (sourceDelta * (2 / (d - c) + 2)) := by ring
    _ ≤ data.scale * (16 * preDelta) :=
      mul_le_mul_of_nonneg_left data.source_scale_budget data.scale_pos.le
    _ = 16 * data.scale * preDelta := by ring
    _ = data.finalDelta := data.finalDelta_eq.symm
    _ ≤ rho := hrhoLower

theorem sourceRho_one
    {sourceDelta preDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) sourceFamily sourceShading g center hcd hm}
    {sourceLocal : PureWZ2LocalGrainData sourceShading sigma C}
    {exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal}
    (data : PureWZ2IsotropicJointLocalScaleData exact)
    {rho : ℝ} (hrhoLower : data.finalDelta ≤ rho) (hrhoOne : rho ≤ 1) :
    data.sourceRho rho ≤ 1 := by
  have hrhoPos : 0 < rho := data.finalDelta_pos.trans_le hrhoLower
  have hqOne : 1 ≤ 2 / (d - c) + 2 := by
    have : 0 ≤ 2 / (d - c) := by positivity
    linarith
  have hdenomOne : 1 ≤ data.scale * (2 / (d - c) + 2) :=
    one_le_mul_of_one_le_of_one_le data.scale_one hqOne
  exact (div_le_self hrhoPos.le hdenomOne).trans hrhoOne

theorem inverse_ball
    {sourceDelta preDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) sourceFamily sourceShading g center hcd hm}
    {sourceLocal : PureWZ2LocalGrainData sourceShading sigma C}
    {exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal}
    (data : PureWZ2IsotropicJointLocalScaleData exact)
    {rho : ℝ} (hrhoLower : data.finalDelta ≤ rho) (hrhoOne : rho ≤ 1) :
    ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
        |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
        ((Real.sqrt rho + 2 * (data.finalDelta * Real.sqrt 3)) / data.scale) ≤
      Real.sqrt (data.sourceRho rho) := by
  let inverseNorm : ℝ :=
    ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
      |>.toContinuousLinearEquiv.toContinuousLinearMap‖
  let q : ℝ := 2 / (d - c) + 2
  have hrhoPos : 0 < rho := data.finalDelta_pos.trans_le hrhoLower
  have hqPos : 0 < q := by dsimp only [q] <;> positivity
  have hsourceRhoPos : 0 < data.sourceRho rho := by
    unfold sourceRho
    exact div_pos hrhoPos (mul_pos data.scale_pos hqPos)
  have hsqrtNonneg := Real.sqrt_nonneg rho
  have hsqrtSq := Real.sq_sqrt hrhoPos.le
  have hsqrtOne : Real.sqrt rho ≤ 1 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith⟩
  have hrhoSqrt : rho ≤ Real.sqrt rho := by nlinarith
  have hsqrtThree : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_nonneg 3]
  have hwitnessUpper : data.finalDelta * Real.sqrt 3 ≤ 2 * rho := by
    calc
      data.finalDelta * Real.sqrt 3 ≤ rho * Real.sqrt 3 :=
        mul_le_mul_of_nonneg_right hrhoLower (Real.sqrt_nonneg 3)
      _ ≤ rho * 2 := mul_le_mul_of_nonneg_left hsqrtThree hrhoPos.le
      _ = 2 * rho := by ring
  have hradiusUpper : Real.sqrt rho +
      2 * (data.finalDelta * Real.sqrt 3) ≤ 5 * Real.sqrt rho := by
    nlinarith
  have hinverseNonneg : 0 ≤ inverseNorm := by
    dsimp only [inverseNorm]
    exact norm_nonneg _
  have hleftNonneg : 0 ≤ inverseNorm *
      ((Real.sqrt rho + 2 * (data.finalDelta * Real.sqrt 3)) / data.scale) :=
    mul_nonneg hinverseNonneg <| div_nonneg
      (add_nonneg hsqrtNonneg
        (mul_nonneg (by norm_num)
          (mul_nonneg data.finalDelta_pos.le (Real.sqrt_nonneg 3))))
      data.scale_pos.le
  have hleftUpper : inverseNorm *
      ((Real.sqrt rho + 2 * (data.finalDelta * Real.sqrt 3)) / data.scale) ≤
      inverseNorm * ((5 * Real.sqrt rho) / data.scale) :=
    mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hradiusUpper data.scale_pos.le)
      hinverseNonneg
  have hbudget : 25 * q * inverseNorm ^ 2 ≤ data.scale := by
    simpa only [q, inverseNorm] using data.inverse_ball_budget
  have hupperSquare :
      (inverseNorm * ((5 * Real.sqrt rho) / data.scale)) ^ 2 ≤
        data.sourceRho rho := by
    unfold sourceRho
    calc
      (inverseNorm * ((5 * Real.sqrt rho) / data.scale)) ^ 2 =
          (rho / (data.scale * q)) *
            ((25 * q * inverseNorm ^ 2) / data.scale) := by
        field_simp [data.scale_pos.ne', hqPos.ne']
        nlinarith [hsqrtSq]
      _ ≤ (rho / (data.scale * q)) * 1 := by
        apply mul_le_mul_of_nonneg_left
        · exact (div_le_one data.scale_pos).2 hbudget
        · positivity
      _ = rho / (data.scale * q) := by ring
  apply (Real.le_sqrt hleftNonneg hsourceRhoPos.le).2
  exact (sq_le_sq₀ hleftNonneg <| mul_nonneg hinverseNonneg
    (div_nonneg (mul_nonneg (by norm_num) hsqrtNonneg)
      data.scale_pos.le)).2 hleftUpper |>.trans hupperSquare

theorem projection_base
    {sourceDelta preDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) sourceFamily sourceShading g center hcd hm}
    {sourceLocal : PureWZ2LocalGrainData sourceShading sigma C}
    {exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal}
    (data : PureWZ2IsotropicJointLocalScaleData exact)
    {rho : ℝ} (hrhoLower : data.finalDelta ≤ rho)
    (point : {point : Point3 // point ∈ sourceShading.union}) :
    (data.scale /
        ‖dPhiInvT g c d m (sourceLocal.planeMap point)‖) *
        data.sourceRho rho ≤ rho := by
  let q : ℝ := 2 / (d - c) + 2
  have hqPos : 0 < q := by dsimp only [q] <;> positivity
  have hnormalLower : 1 / q ≤
      ‖dPhiInvT g c d m (sourceLocal.planeMap point)‖ := by
    simpa only [q] using data.normal_lower point
  have hnormalPos : 0 <
      ‖dPhiInvT g c d m (sourceLocal.planeMap point)‖ :=
    lt_of_lt_of_le (by positivity) hnormalLower
  have hqNormal : 1 ≤ q *
      ‖dPhiInvT g c d m (sourceLocal.planeMap point)‖ := by
    have := mul_le_mul_of_nonneg_left hnormalLower hqPos.le
    field_simp [hqPos.ne'] at this
    exact this
  unfold sourceRho
  calc
    data.scale / ‖dPhiInvT g c d m (sourceLocal.planeMap point)‖ *
          (rho / (data.scale * q)) =
        rho / (q * ‖dPhiInvT g c d m (sourceLocal.planeMap point)‖) := by
      field_simp [data.scale_pos.ne', hqPos.ne', hnormalPos.ne']
    _ ≤ rho := div_le_self
      (data.finalDelta_pos.trans_le hrhoLower).le hqNormal

/-- Once the single final-scale record is available, every analytic and
geometric side condition of the final local-grain transport is automatic. -/
theorem toFinalLocalGrains
    {sourceDelta preDelta c d m sigma : ℝ}
    {C sourceConstant boxScheduleConstant cleanupScheduleConstant
      sourceScheduleConstant : ENNReal}
    {boxLevelCount cleanupLevelCount parentLevelCount : ℕ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := preDelta) sourceFamily sourceShading g center hcd hm}
    {sourceLocal : PureWZ2LocalGrainData sourceShading sigma C}
    {exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal}
    (scaleData : PureWZ2IsotropicJointLocalScaleData exact)
    (preparation : PureWZ2FinalIsotropicPreparationData
      (targetDelta := scaleData.finalDelta) raw.exactShading sourceConstant
      boxScheduleConstant cleanupScheduleConstant boxLevelCount
      cleanupLevelCount scaleData.scale)
    (assembly : PureWZ2IsotropicCleanupQuotientAssemblyData
      preparation.cleanupRegularized sourceScheduleConstant parentLevelCount) :
    Nonempty (PureWZ2LocalGrainData assembly.finalShading sigma (15 * C)) := by
  apply assembly.toFinalLocalGrains exact preparation
    scaleData.targetK_mul_scale scaleData.extension_small
    scaleData.extension_one scaleData.incidence_budget
    scaleData.projection_budget
    (fun rho _ _ => scaleData.sourceRho rho)
  · intro rho hrhoLower _
    exact scaleData.sourceRho_lower hrhoLower
  · intro rho hrhoLower hrhoOne
    exact scaleData.sourceRho_one hrhoLower hrhoOne
  · intro rho hrhoLower hrhoOne
    exact scaleData.inverse_ball hrhoLower hrhoOne
  · intro rho hrhoLower _ exactPoint
    apply scaleData.projection_base hrhoLower

end PureWZ2IsotropicJointLocalScaleData

end Kakeya.Assouad

end
