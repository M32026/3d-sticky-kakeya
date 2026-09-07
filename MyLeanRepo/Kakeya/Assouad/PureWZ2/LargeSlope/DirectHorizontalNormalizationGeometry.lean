import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHorizontalNormalizationPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalPopularBoxZeroPoint
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalNormalizationNormProduct

/-!
# Direct horizontal-normalization geometry

The final horizontal dilation uses one fixed scale.  Its popular-box width is
chosen with a factor-four safety margin: the tempting width `1 / lambda` would
already contribute `1 / 2` to a zero-point coordinate and therefore cannot
prove the paper line-class bound `1 / 3` merely from nonempty intersection.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

private theorem horizontalDilation_norm_le
    {lambda : ℝ} (hlambda : 1 ≤ lambda) (vector : Point3) :
    ‖point3 (lambda * vector 0) (lambda * vector 1) (vector 2)‖ ≤
      lambda * ‖vector‖ := by
  have hsource := point3_coord_norm_sq vector
  have htarget := point3_coord_norm_sq
    (point3 (lambda * vector 0) (lambda * vector 1) (vector 2))
  have hlambdaSq : 1 ≤ lambda ^ 2 := by nlinarith
  have hsquares :
      ‖point3 (lambda * vector 0) (lambda * vector 1) (vector 2)‖ ^ 2 ≤
        (lambda * ‖vector‖) ^ 2 := by
    rw [htarget, mul_pow, hsource]
    simp only [point3_coord0, point3_coord1, point3_coord2]
    nlinarith [sq_nonneg (vector 0), sq_nonneg (vector 1),
      sq_nonneg (vector 2),
      mul_le_mul_of_nonneg_right hlambdaSq (sq_nonneg (vector 2))]
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (by linarith) (norm_nonneg _))).mp hsquares

/-- The combined triangular/horizontal operator norm is bounded by the
horizontal factor times the triangular height factor. -/
theorem pureWZ2HorizontalNormalizedAffineEquiv_opNorm_le
    (g : SlopeFunction) {c d m lambda : ℝ}
    (anisotropicCenter horizontalCenter : Point3)
    (hcd : c < d) (hdc : d - c ≤ 1)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hlambda : 1 ≤ lambda)
    (hgmid : |g (c + (d - c) / 2)| ≤ 1) :
    ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
      horizontalCenter lambda hcd hm (by linarith)).linear
        |>.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤
      lambda * (2 / (d - c)) := by
  have hlength : 0 < d - c := sub_pos.mpr hcd
  have hheight : 2 ≤ 2 / (d - c) := by
    rw [le_div_iff₀ hlength]
    nlinarith
  have htransverse : |m * (d - c) / 2| ≤ 1 := by
    rw [abs_of_pos (by positivity : 0 < m * (d - c) / 2)]
    nlinarith [mul_nonneg hm.le (sub_nonneg.mpr hcd.le)]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro vector
  change
    ‖(pureWZ2HorizontalNormalizedAffineEquiv g c d m anisotropicCenter
      horizontalCenter lambda hcd hm (by linarith)).linear vector‖ ≤
        lambda * (2 / (d - c)) * ‖vector‖
  rw [pureWZ2HorizontalNormalizedAffineEquiv_linear_apply]
  calc
    ‖point3
        (lambda * (dPhiLin g c d m vector) 0)
        (lambda * (dPhiLin g c d m vector) 1)
        ((dPhiLin g c d m vector) 2)‖ ≤
      lambda * ‖dPhiLin g c d m vector‖ :=
        horizontalDilation_norm_le hlambda _
    _ ≤ lambda * ((2 / (d - c)) * ‖vector‖) := by
      gcongr
      simpa [dPhiLin] using anisotropicMap_opNorm_bound
        hgmid htransverse hheight vector
    _ = lambda * (2 / (d - c)) * ‖vector‖ := by ring

/-- Fixed horizontal dilation used by the direct exact-slope route. -/
def pureWZ2DirectHorizontalScale : ℝ :=
  pureWZ2DirectFinalGeometryConstant

/-- Horizontal popular-box width with room for carrier thickness and the
motion from an occupied height to target height zero. -/
def pureWZ2DirectHorizontalBoxWidth : ℝ :=
  1 / (4 * pureWZ2DirectHorizontalScale)

/-- Honest direction/normal product lower bound after the fixed horizontal
dilation. -/
def pureWZ2DirectHorizontalProductLower : ℝ :=
  1 / (3 * pureWZ2DirectHorizontalScale)

/-- Radius before the final reciprocal-grid rounding.  It is four times the
transported source radius, leaving one target-grid diameter for cubical
saturation. -/
def pureWZ2DirectHorizontalRawTargetScale
    (preDelta : ℝ) : ℝ :=
  4 * pureWZ2DirectHorizontalScale * preDelta

/-- Reciprocal-grid radius of the final horizontal target. -/
def pureWZ2DirectHorizontalTargetCount
    (preDelta : ℝ) : ℕ :=
  Nat.floor (1 / pureWZ2DirectHorizontalRawTargetScale preDelta)

def pureWZ2DirectHorizontalTargetScale
    (preDelta : ℝ) : ℝ :=
  1 / (pureWZ2DirectHorizontalTargetCount preDelta : ℝ)

/-- Reciprocal-grid radius before the final horizontal dilation. -/
def PureWZ2DirectSection6SourceAssembly.directPreHorizontalScale
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) : ℝ :=
  anisotropicPaperAlignedScale delta assembly.horizontalSource.c
    assembly.horizontalSource.d

/-- Final reciprocal-grid radius after the horizontal dilation. -/
def PureWZ2DirectSection6SourceAssembly.directHorizontalTargetScale
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) : ℝ :=
  pureWZ2DirectHorizontalTargetScale assembly.directPreHorizontalScale

theorem pureWZ2DirectHorizontalScale_pos :
    0 < pureWZ2DirectHorizontalScale := by
  exact pureWZ2DirectFinalGeometryConstant_pos

theorem pureWZ2DirectHorizontalScale_one :
    1 ≤ pureWZ2DirectHorizontalScale := by
  unfold pureWZ2DirectHorizontalScale pureWZ2DirectFinalGeometryConstant
  exact le_max_left _ _

theorem pureWZ2DirectHorizontalBoxWidth_pos :
    0 < pureWZ2DirectHorizontalBoxWidth := by
  unfold pureWZ2DirectHorizontalBoxWidth
  positivity [pureWZ2DirectHorizontalScale_pos]

theorem pureWZ2DirectHorizontalBoxWidth_le_one :
    pureWZ2DirectHorizontalBoxWidth ≤ 1 := by
  unfold pureWZ2DirectHorizontalBoxWidth
  have hscale := pureWZ2DirectHorizontalScale_one
  have hdenominator : (1 : ℝ) ≤ 4 * pureWZ2DirectHorizontalScale := by
    nlinarith
  simpa using one_div_le_one_div_of_le
    (show (0 : ℝ) < 1 by norm_num) hdenominator

theorem pureWZ2DirectHorizontalProductLower_pos :
    0 < pureWZ2DirectHorizontalProductLower := by
  unfold pureWZ2DirectHorizontalProductLower
  positivity [pureWZ2DirectHorizontalScale_pos]

theorem pureWZ2DirectHorizontal_incidenceLoss
    (sourceDelta : ℝ) :
    sourceDelta / pureWZ2DirectHorizontalProductLower =
      3 * pureWZ2DirectHorizontalScale * sourceDelta := by
  unfold pureWZ2DirectHorizontalProductLower
  field_simp [pureWZ2DirectHorizontalScale_pos.ne']
  <;> ring

theorem pureWZ2DirectHorizontalRawTargetScale_pos
    {preDelta : ℝ} (hpreDelta : 0 < preDelta) :
    0 < pureWZ2DirectHorizontalRawTargetScale preDelta := by
  unfold pureWZ2DirectHorizontalRawTargetScale
  positivity [pureWZ2DirectHorizontalScale_pos]

theorem pureWZ2DirectHorizontalTargetCount_pos
    {preDelta : ℝ} (hrawPos :
      0 < pureWZ2DirectHorizontalRawTargetScale preDelta)
    (hrawHalf : pureWZ2DirectHorizontalRawTargetScale preDelta ≤ 1 / 2) :
    0 < pureWZ2DirectHorizontalTargetCount preDelta := by
  apply Nat.floor_pos.mpr
  have : (2 : ℝ) ≤ 1 / pureWZ2DirectHorizontalRawTargetScale preDelta := by
    rw [le_div_iff₀ hrawPos]
    linarith
  linarith

theorem pureWZ2DirectHorizontalRawTargetScale_le_targetScale
    {preDelta : ℝ} (hrawPos :
      0 < pureWZ2DirectHorizontalRawTargetScale preDelta)
    (hrawHalf : pureWZ2DirectHorizontalRawTargetScale preDelta ≤ 1 / 2) :
    pureWZ2DirectHorizontalRawTargetScale preDelta ≤
      pureWZ2DirectHorizontalTargetScale preDelta := by
  let raw := pureWZ2DirectHorizontalRawTargetScale preDelta
  let count := pureWZ2DirectHorizontalTargetCount preDelta
  have hcountPos : 0 < count :=
    pureWZ2DirectHorizontalTargetCount_pos hrawPos hrawHalf
  have hcountLe : (count : ℝ) ≤ 1 / raw := Nat.floor_le (by positivity)
  change raw ≤ 1 / (count : ℝ)
  rw [le_div_iff₀ (by exact_mod_cast hcountPos)]
  calc
    raw * (count : ℝ) ≤ raw * (1 / raw) :=
      mul_le_mul_of_nonneg_left hcountLe hrawPos.le
    _ = 1 := by
      dsimp only [raw]
      simpa [one_div] using mul_inv_cancel₀ hrawPos.ne'

theorem pureWZ2DirectHorizontalTargetScale_lt_two_mul_raw
    {preDelta : ℝ} (hrawPos :
      0 < pureWZ2DirectHorizontalRawTargetScale preDelta)
    (hrawHalf : pureWZ2DirectHorizontalRawTargetScale preDelta ≤ 1 / 2) :
    pureWZ2DirectHorizontalTargetScale preDelta <
      2 * pureWZ2DirectHorizontalRawTargetScale preDelta := by
  let raw := pureWZ2DirectHorizontalRawTargetScale preDelta
  let count := pureWZ2DirectHorizontalTargetCount preDelta
  have hcountPos : 0 < count :=
    pureWZ2DirectHorizontalTargetCount_pos hrawPos hrawHalf
  have hfloorPlus : 1 / raw < (count : ℝ) + 1 := by
    exact Nat.lt_floor_add_one (1 / raw)
  have htwo : (2 : ℝ) ≤ 1 / raw := by
    rw [le_div_iff₀ hrawPos]
    linarith
  have hcountLower : 1 / (2 * raw) < (count : ℝ) := by
    have hsub : 1 / raw - 1 < (count : ℝ) := by linarith
    have hhalf : 1 / (2 * raw) ≤ 1 / raw - 1 := by
      have hrewrite : 1 / (2 * raw) = (1 / raw) / 2 := by
        field_simp [hrawPos.ne']
      rw [hrewrite]
      linarith
    exact hhalf.trans_lt hsub
  change 1 / (count : ℝ) < 2 * raw
  rw [div_lt_iff₀ (by exact_mod_cast hcountPos)]
  calc
    1 = (2 * raw) * (1 / (2 * raw)) := by
      symm
      rw [mul_div_cancel₀]
      positivity
    _ < (2 * raw) * (count : ℝ) :=
      mul_lt_mul_of_pos_left hcountLower (mul_pos (by norm_num) hrawPos)

theorem pureWZ2DirectHorizontalTargetScale_pos
    {preDelta : ℝ} (hrawPos :
      0 < pureWZ2DirectHorizontalRawTargetScale preDelta)
    (hrawHalf : pureWZ2DirectHorizontalRawTargetScale preDelta ≤ 1 / 2) :
    0 < pureWZ2DirectHorizontalTargetScale preDelta := by
  unfold pureWZ2DirectHorizontalTargetScale
  positivity [pureWZ2DirectHorizontalTargetCount_pos hrawPos hrawHalf]

theorem pureWZ2DirectHorizontalTargetScale_mul_count
    {preDelta : ℝ} (hrawPos :
      0 < pureWZ2DirectHorizontalRawTargetScale preDelta)
    (hrawHalf : pureWZ2DirectHorizontalRawTargetScale preDelta ≤ 1 / 2) :
    pureWZ2DirectHorizontalTargetScale preDelta *
      (pureWZ2DirectHorizontalTargetCount preDelta : ℝ) = 1 := by
  unfold pureWZ2DirectHorizontalTargetScale
  field_simp [show (pureWZ2DirectHorizontalTargetCount preDelta : ℝ) ≠ 0 by
    exact_mod_cast
      (pureWZ2DirectHorizontalTargetCount_pos hrawPos hrawHalf).ne']

private theorem directAnisotropicRawScale_pos
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) :
    0 < anisotropicPaperRawScale delta assembly.horizontalSource.c
      assembly.horizontalSource.d := by
  unfold anisotropicPaperRawScale
  exact div_pos (mul_pos (by norm_num) assembly.cfg.extremal.delta_pos)
    (sub_pos.mpr assembly.horizontalSource.ordered)

private theorem directAnisotropicRawScale_le_half
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) :
    anisotropicPaperRawScale delta assembly.horizontalSource.c
      assembly.horizontalSource.d ≤ 1 / 2 := by
  have hrhoPos : 0 < assembly.rho.1 :=
    assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1
  have hlength : assembly.horizontalSource.d -
      assembly.horizontalSource.c = assembly.rho.1 / 100 := by
    rw [assembly.horizontalSource.length_eq, assembly.horizontalSource_scale]
  have hrawEq : anisotropicPaperRawScale delta
      assembly.horizontalSource.c assembly.horizontalSource.d =
        1600 * delta / assembly.rho.1 := by
    unfold anisotropicPaperRawScale
    rw [hlength]
    field_simp [hrhoPos.ne']
    ring
  rw [hrawEq, div_le_iff₀ hrhoPos]
  have hfactor : 0 ≤ (1 / 2 : ℝ) - 1600 * assembly.rho.1 := by
    linarith [assembly.rho_tiny]
  nlinarith [assembly.delta_le_rho_sq, mul_nonneg hrhoPos.le hfactor]

theorem PureWZ2DirectSection6SourceAssembly.directPreHorizontalScale_pos
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) :
    0 < assembly.directPreHorizontalScale := by
  exact anisotropicPaperAlignedScale_pos
    (directAnisotropicRawScale_pos assembly)
    (directAnisotropicRawScale_le_half assembly)

theorem PureWZ2DirectSection6SourceAssembly.directPreHorizontalScale_upper
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) :
    assembly.directPreHorizontalScale < 3200 * delta / assembly.rho.1 := by
  calc
    assembly.directPreHorizontalScale <
        2 * anisotropicPaperRawScale delta assembly.horizontalSource.c
          assembly.horizontalSource.d :=
      anisotropicPaperAlignedScale_lt_two_mul_raw
        (directAnisotropicRawScale_pos assembly)
        (directAnisotropicRawScale_le_half assembly)
    _ = 3200 * delta / assembly.rho.1 := by
      unfold anisotropicPaperRawScale
      rw [show assembly.horizontalSource.d - assembly.horizontalSource.c =
        assembly.rho.1 / 100 by
          rw [assembly.horizontalSource.length_eq, assembly.horizontalSource_scale]]
      field_simp [show assembly.rho.1 ≠ 0 by
        exact ne_of_gt
          (assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1)]
      ring

theorem PureWZ2DirectSection6SourceAssembly.delta_le_directPreHorizontalScale
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) :
    delta ≤ assembly.directPreHorizontalScale := by
  have hlengthPos : 0 < assembly.horizontalSource.d -
      assembly.horizontalSource.c := sub_pos.mpr assembly.horizontalSource.ordered
  have hlengthSmall : assembly.horizontalSource.d -
      assembly.horizontalSource.c ≤ 16 := by
    rw [assembly.horizontalSource.length_eq, assembly.horizontalSource_scale]
    linarith [assembly.rho_tiny]
  have hraw := anisotropicPaperRawScale_le_aligned
    (directAnisotropicRawScale_pos assembly)
    (directAnisotropicRawScale_le_half assembly)
  calc
    delta ≤ 16 * delta /
        (assembly.horizontalSource.d - assembly.horizontalSource.c) := by
      rw [le_div_iff₀ hlengthPos]
      nlinarith [assembly.cfg.extremal.delta_pos]
    _ ≤ assembly.directPreHorizontalScale := hraw

theorem PureWZ2DirectSection6SourceAssembly.directHorizontalScale_mul_pre_le
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) :
    pureWZ2DirectHorizontalScale * assembly.directPreHorizontalScale ≤
      1 / 1000 := by
  let scale := pureWZ2DirectHorizontalScale
  let rho := assembly.rho.1
  have hscalePos : 0 < scale := pureWZ2DirectHorizontalScale_pos
  have hrhoPos : 0 < rho :=
    assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1
  have hrhoOne : rho ≤ 1 := assembly.rho_tiny.trans (by norm_num)
  have hpre := assembly.directPreHorizontalScale_upper
  have hproduct : scale * assembly.directPreHorizontalScale <
      scale * (3200 * delta / rho) :=
    mul_lt_mul_of_pos_left hpre hscalePos
  have hdeltaRhoEight := assembly.delta_le_rho_eight
  have hrhoSix : rho ^ 6 ≤ 1 := by
    exact pow_le_one₀ hrhoPos.le hrhoOne
  have hrhoSeven : rho ^ 7 ≤ rho := by
    calc
      rho ^ 7 = rho ^ 6 * rho := by ring
      _ ≤ 1 * rho := by gcongr
      _ = rho := by ring
  have hscaleRho : scale * rho ≤ 1 / 3200000 := by
    have hscaled := mul_le_mul_of_nonneg_left assembly.rho_final_tiny
      hscalePos.le
    have heq : scale * pureWZ2DirectFinalGeometryThreshold =
        1 / 3200000 := by
      change pureWZ2DirectFinalGeometryConstant *
        (1 / (3200000 * pureWZ2DirectFinalGeometryConstant)) =
          1 / 3200000
      field_simp [pureWZ2DirectFinalGeometryConstant_pos.ne']
    simpa [scale, heq] using hscaled
  have hupper : scale * (3200 * delta / rho) ≤ 1 / 1000 := by
    rw [show scale * (3200 * delta / rho) =
      (3200 * scale * delta) / rho by ring]
    apply (div_le_iff₀ hrhoPos).2
    calc
      3200 * scale * delta ≤ 3200 * scale * rho ^ 8 := by gcongr
      _ = (3200 * (scale * rho)) * rho ^ 7 := by ring
      _ ≤ (3200 * (1 / 3200000 : ℝ)) * rho ^ 7 := by gcongr
      _ = (1 / 1000 : ℝ) * rho ^ 7 := by norm_num
      _ ≤ (1 / 1000 : ℝ) * rho := by gcongr
  calc
    scale * assembly.directPreHorizontalScale ≤
        scale * (3200 * delta / rho) := hproduct.le
    _ ≤ 1 / 1000 := hupper

theorem PureWZ2DirectSection6SourceAssembly.directHorizontalRawTargetScale_pos
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) :
    0 < pureWZ2DirectHorizontalRawTargetScale
      assembly.directPreHorizontalScale :=
  pureWZ2DirectHorizontalRawTargetScale_pos
    assembly.directPreHorizontalScale_pos

theorem PureWZ2DirectSection6SourceAssembly.directHorizontalRawTargetScale_half
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) :
    pureWZ2DirectHorizontalRawTargetScale
        assembly.directPreHorizontalScale ≤ 1 / 2 := by
  unfold pureWZ2DirectHorizontalRawTargetScale
  nlinarith [assembly.directHorizontalScale_mul_pre_le]

theorem PureWZ2DirectSection6SourceAssembly.directHorizontalTargetScale_pos
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) :
    0 < assembly.directHorizontalTargetScale :=
  pureWZ2DirectHorizontalTargetScale_pos
    assembly.directHorizontalRawTargetScale_pos
    assembly.directHorizontalRawTargetScale_half

theorem PureWZ2DirectSection6SourceAssembly.directHorizontalRawTargetScale_le_target
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) :
    pureWZ2DirectHorizontalRawTargetScale assembly.directPreHorizontalScale ≤
      assembly.directHorizontalTargetScale :=
  pureWZ2DirectHorizontalRawTargetScale_le_targetScale
    assembly.directHorizontalRawTargetScale_pos
    assembly.directHorizontalRawTargetScale_half

theorem PureWZ2DirectSection6SourceAssembly.directHorizontalTargetScale_aligned
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) :
    assembly.directHorizontalTargetScale *
      (pureWZ2DirectHorizontalTargetCount assembly.directPreHorizontalScale : ℝ) =
        1 :=
  pureWZ2DirectHorizontalTargetScale_mul_count
    assembly.directHorizontalRawTargetScale_pos
    assembly.directHorizontalRawTargetScale_half

theorem PureWZ2DirectSection6SourceAssembly.directHorizontalTargetScale_le_one
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) :
    assembly.directHorizontalTargetScale ≤ 1 := by
  have hcountPos := pureWZ2DirectHorizontalTargetCount_pos
    assembly.directHorizontalRawTargetScale_pos
    assembly.directHorizontalRawTargetScale_half
  unfold directHorizontalTargetScale pureWZ2DirectHorizontalTargetScale
  have hcountOne : (1 : ℝ) ≤
      (pureWZ2DirectHorizontalTargetCount
        assembly.directPreHorizontalScale : ℕ) := by
    exact_mod_cast hcountPos
  simpa using one_div_le_one_div_of_le
    (show (0 : ℝ) < 1 by norm_num) hcountOne

theorem PureWZ2DirectSection6SourceAssembly.directHorizontalTargetScale_small
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) :
    assembly.directHorizontalTargetScale < 1 / 125 := by
  calc
    assembly.directHorizontalTargetScale <
        2 * pureWZ2DirectHorizontalRawTargetScale
          assembly.directPreHorizontalScale :=
      pureWZ2DirectHorizontalTargetScale_lt_two_mul_raw
        assembly.directHorizontalRawTargetScale_pos
        assembly.directHorizontalRawTargetScale_half
    _ = 8 * pureWZ2DirectHorizontalScale *
        assembly.directPreHorizontalScale := by
      unfold pureWZ2DirectHorizontalRawTargetScale
      ring
    _ ≤ 8 * (1 / 1000 : ℝ) := by
      nlinarith [assembly.directHorizontalScale_mul_pre_le]
    _ = 1 / 125 := by norm_num

theorem PureWZ2DirectSection6SourceAssembly.directHorizontal_radius_budget
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (retubing : PureWZ2DirectAnisotropicRetubingData assembly)
    (horizontalCenter : Point3) :
    ‖(pureWZ2HorizontalNormalizedAffineEquiv
      (pureWZ2DirectGeometrySlope assembly.horizontalSource)
      assembly.horizontalSource.c assembly.horizontalSource.d
      assembly.horizontalSource.m
      (pureWZ2DirectAnisotropicCenter retubing.popular)
      horizontalCenter pureWZ2DirectHorizontalScale
      assembly.horizontalSource.ordered
      assembly.horizontalSource.slopeScale_pos
      pureWZ2DirectHorizontalScale_pos).linear
        |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
        (6 * delta) + 2 * assembly.directHorizontalTargetScale ≤
      6 * assembly.directHorizontalTargetScale := by
  have hlengthOne : assembly.horizontalSource.d -
      assembly.horizontalSource.c ≤ 1 := by
    rw [assembly.horizontalSource.length_eq, assembly.horizontalSource_scale]
    linarith [assembly.rho_tiny]
  have hgmid :
      |pureWZ2DirectGeometrySlope assembly.horizontalSource
        (assembly.horizontalSource.c +
          (assembly.horizontalSource.d - assembly.horizontalSource.c) / 2)| ≤ 1 :=
    (retubing.geometrySlope_normalized _
      (retubing.interval_sub_unit ⟨by
        linarith [assembly.horizontalSource.ordered], by
        linarith [assembly.horizontalSource.ordered]⟩)).1
  have hop := pureWZ2HorizontalNormalizedAffineEquiv_opNorm_le
    (pureWZ2DirectGeometrySlope assembly.horizontalSource)
    (pureWZ2DirectAnisotropicCenter retubing.popular) horizontalCenter
    assembly.horizontalSource.ordered hlengthOne
    assembly.horizontalSource.slopeScale_pos
    assembly.horizontalSource.slopeScale_le_one
    pureWZ2DirectHorizontalScale_one hgmid
  have hraw := assembly.directHorizontalRawTargetScale_le_target
  have hprePos := assembly.directPreHorizontalScale_pos
  have hlengthPos : 0 < assembly.horizontalSource.d -
      assembly.horizontalSource.c :=
    sub_pos.mpr assembly.horizontalSource.ordered
  have hpreLower : 16 * delta /
      (assembly.horizontalSource.d - assembly.horizontalSource.c) ≤
        assembly.directPreHorizontalScale := by
    exact anisotropicPaperRawScale_le_aligned
      (directAnisotropicRawScale_pos assembly)
      (directAnisotropicRawScale_le_half assembly)
  have hsource :
      pureWZ2DirectHorizontalScale *
          (2 / (assembly.horizontalSource.d - assembly.horizontalSource.c)) *
          (6 * delta) ≤
        3 * pureWZ2DirectHorizontalScale * assembly.directPreHorizontalScale := by
    have hscaled := mul_le_mul_of_nonneg_left hpreLower
      (mul_nonneg (show (0 : ℝ) ≤ 3 / 4 by norm_num)
        pureWZ2DirectHorizontalScale_pos.le)
    calc
      pureWZ2DirectHorizontalScale *
          (2 / (assembly.horizontalSource.d - assembly.horizontalSource.c)) *
          (6 * delta) =
        (3 / 4 * pureWZ2DirectHorizontalScale) *
          (16 * delta /
            (assembly.horizontalSource.d - assembly.horizontalSource.c)) := by
          ring
      _ ≤ (3 / 4 * pureWZ2DirectHorizontalScale) *
          assembly.directPreHorizontalScale := hscaled
      _ = 3 * pureWZ2DirectHorizontalScale *
          assembly.directPreHorizontalScale / 4 := by ring
      _ ≤ 3 * pureWZ2DirectHorizontalScale *
          assembly.directPreHorizontalScale := by
        have hnonnegative : 0 ≤ 3 * pureWZ2DirectHorizontalScale *
            assembly.directPreHorizontalScale :=
          mul_nonneg (mul_nonneg (by norm_num)
            pureWZ2DirectHorizontalScale_pos.le) hprePos.le
        nlinarith
  have hnormSource :
      ‖(pureWZ2HorizontalNormalizedAffineEquiv
        (pureWZ2DirectGeometrySlope assembly.horizontalSource)
        assembly.horizontalSource.c assembly.horizontalSource.d
        assembly.horizontalSource.m
        (pureWZ2DirectAnisotropicCenter retubing.popular) horizontalCenter
        pureWZ2DirectHorizontalScale assembly.horizontalSource.ordered
        assembly.horizontalSource.slopeScale_pos
        pureWZ2DirectHorizontalScale_pos).linear
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
          (6 * delta) ≤
        3 * pureWZ2DirectHorizontalScale * assembly.directPreHorizontalScale := by
    exact (mul_le_mul_of_nonneg_right hop
      (mul_nonneg (by norm_num) assembly.cfg.extremal.delta_pos.le)).trans
        hsource
  have hthree : 3 * pureWZ2DirectHorizontalScale *
      assembly.directPreHorizontalScale ≤
        3 * assembly.directHorizontalTargetScale := by
    have hraw' : 4 * pureWZ2DirectHorizontalScale *
        assembly.directPreHorizontalScale ≤
          assembly.directHorizontalTargetScale := by
      simpa [pureWZ2DirectHorizontalRawTargetScale] using hraw
    have hnonnegative : 0 ≤ pureWZ2DirectHorizontalScale *
        assembly.directPreHorizontalScale :=
      mul_nonneg pureWZ2DirectHorizontalScale_pos.le hprePos.le
    nlinarith
  have htargetNonnegative := assembly.directHorizontalTargetScale_pos.le
  calc
    _ ≤ 3 * assembly.directHorizontalTargetScale +
        2 * assembly.directHorizontalTargetScale := by
      simpa [add_comm] using add_le_add_right (hnormSource.trans hthree)
        (2 * assembly.directHorizontalTargetScale)
    _ ≤ 6 * assembly.directHorizontalTargetScale := by nlinarith

/-- The exact combined image of the pulled-back horizontal box lies in the
half-open unit coordinate window.  Reciprocal-grid saturation therefore stays
inside the closed paper crop. -/
theorem PureWZ2ExternalWeightRegularizationData.directHorizontalPopular_cubical_crop
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount)
    (popular : PureWZ2HorizontalPopularBoxData
      (directFinalRaw (retubing := retubing)
        (regularized := regularized) data).exactShading
      pureWZ2DirectHorizontalBoxWidth) :
    ∀ index,
      wz1PaperCubicalSaturation assembly.directHorizontalTargetScale
        (pureWZ2HorizontalNormalizedMap
          (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          (pureWZ2DirectAnisotropicCenter retubing.popular) popular.center
          pureWZ2DirectHorizontalScale ''
            (pureWZ2HorizontalPopularPullbackNonemptyShading
              (directFinalRaw (retubing := retubing)
                (regularized := regularized) data) popular).carrier index) ⊆
        Kakeya.Streamlined.axisBox 2 2 2 := by
  let raw := directFinalRaw (retubing := retubing)
    (regularized := regularized) data
  let selected := pureWZ2HorizontalPopularPullbackSourceSubfamily raw popular
  let targetScale := assembly.directHorizontalTargetScale
  have htargetPos : 0 < targetScale := assembly.directHorizontalTargetScale_pos
  have hcountPos : 0 <
      pureWZ2DirectHorizontalTargetCount assembly.directPreHorizontalScale :=
    pureWZ2DirectHorizontalTargetCount_pos
      assembly.directHorizontalRawTargetScale_pos
      assembly.directHorizontalRawTargetScale_half
  have halign : targetScale *
      (pureWZ2DirectHorizontalTargetCount assembly.directPreHorizontalScale : ℝ) =
        1 := assembly.directHorizontalTargetScale_aligned
  intro index
  apply anisotropicPaperCubicalSaturation_subset_axisBox
    htargetPos hcountPos halign
  intro targetPoint htargetPoint coordinate
  rcases htargetPoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  have himage :
      anisotropicCenteredRescalingMap
          (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          (pureWZ2DirectAnisotropicCenter retubing.popular) sourcePoint ∈
        popular.restricted.carrier (selected.embedding index) := by
    rw [← pureWZ2HorizontalPopularPullbackNonemptyShading_image raw popular
      index]
    exact ⟨sourcePoint, hsourcePoint, rfl⟩
  have hbox :
      anisotropicCenteredRescalingMap
          (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          (pureWZ2DirectAnisotropicCenter retubing.popular) sourcePoint ∈
        popular.box := by
    rw [popular.restricted_carrier] at himage
    exact himage.2
  rw [popular.box_eq] at hbox
  have haxisBox := hbox.1
  have hwidthQuarter :
      pureWZ2DirectHorizontalScale *
          (pureWZ2DirectHorizontalBoxWidth / 2) = 1 / 8 := by
    unfold pureWZ2DirectHorizontalBoxWidth
    field_simp [pureWZ2DirectHorizontalScale_pos.ne']
    ring
  fin_cases coordinate
  · have hcoord := haxisBox (0 : Fin 3)
    have hscaled := mul_le_mul_of_nonneg_left hcoord
      pureWZ2DirectHorizontalScale_pos.le
    have hbound :
        |pureWZ2HorizontalNormalizedMap
          (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          (pureWZ2DirectAnisotropicCenter retubing.popular) popular.center
          pureWZ2DirectHorizontalScale sourcePoint 0| ≤ 1 / 8 := by
      simpa [pureWZ2HorizontalNormalizedMap, point3, abs_mul,
        abs_of_pos pureWZ2DirectHorizontalScale_pos, hwidthQuarter] using hscaled
    have hb := abs_le.mp hbound
    change (-1 : ℝ) ≤
        pureWZ2HorizontalNormalizedMap
          (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          (pureWZ2DirectAnisotropicCenter retubing.popular) popular.center
          pureWZ2DirectHorizontalScale sourcePoint 0 ∧
      pureWZ2HorizontalNormalizedMap
          (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          (pureWZ2DirectAnisotropicCenter retubing.popular) popular.center
          pureWZ2DirectHorizontalScale sourcePoint 0 < 1
    constructor
    · calc
        (-1 : ℝ) ≤ -(1 / 8 : ℝ) := by norm_num
        _ ≤ _ := hb.1
    · calc
        _ ≤ (1 / 8 : ℝ) := hb.2
        _ < 1 := by norm_num
  · have hcoord := haxisBox (1 : Fin 3)
    have hscaled := mul_le_mul_of_nonneg_left hcoord
      pureWZ2DirectHorizontalScale_pos.le
    have hbound :
        |pureWZ2HorizontalNormalizedMap
          (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          (pureWZ2DirectAnisotropicCenter retubing.popular) popular.center
          pureWZ2DirectHorizontalScale sourcePoint 1| ≤ 1 / 8 := by
      simpa [pureWZ2HorizontalNormalizedMap, point3, abs_mul,
        abs_of_pos pureWZ2DirectHorizontalScale_pos, hwidthQuarter] using hscaled
    have hb := abs_le.mp hbound
    change (-1 : ℝ) ≤
        pureWZ2HorizontalNormalizedMap
          (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          (pureWZ2DirectAnisotropicCenter retubing.popular) popular.center
          pureWZ2DirectHorizontalScale sourcePoint 1 ∧
      pureWZ2HorizontalNormalizedMap
          (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          (pureWZ2DirectAnisotropicCenter retubing.popular) popular.center
          pureWZ2DirectHorizontalScale sourcePoint 1 < 1
    constructor
    · calc
        (-1 : ℝ) ≤ -(1 / 8 : ℝ) := by norm_num
        _ ≤ _ := hb.1
    · calc
        _ ≤ (1 / 8 : ℝ) := hb.2
        _ < 1 := by norm_num
  · have hcoord :
        pureWZ2HorizontalNormalizedMap
          (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          (pureWZ2DirectAnisotropicCenter retubing.popular) popular.center
          pureWZ2DirectHorizontalScale sourcePoint 2 =
        2 * (sourcePoint 2 - assembly.horizontalSource.c) /
            (assembly.horizontalSource.d - assembly.horizontalSource.c) - 1 := by
      rw [pureWZ2HorizontalNormalizedMap]
      simp only [point3_coord2, popular.center_height, sub_zero]
      rw [anisotropicCenteredRescalingMap]
      simp only [PiLp.sub_apply, point3_coord2, sub_zero]
      exact (anisotropicRescalingMap_coord
        (pureWZ2DirectGeometrySlope assembly.horizontalSource)
        assembly.horizontalSource.c assembly.horizontalSource.d
        assembly.horizontalSource.m sourcePoint).2.2
    change (-1 : ℝ) ≤
        pureWZ2HorizontalNormalizedMap
          (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          (pureWZ2DirectAnisotropicCenter retubing.popular) popular.center
          pureWZ2DirectHorizontalScale sourcePoint 2 ∧
      pureWZ2HorizontalNormalizedMap
          (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          (pureWZ2DirectAnisotropicCenter retubing.popular) popular.center
          pureWZ2DirectHorizontalScale sourcePoint 2 < 1
    rw [hcoord]
    have hsourceHeight := directFinalSourceShading_height_open data
      (selected.embedding index) sourcePoint hsourcePoint.1
    have hlengthPos := sub_pos.mpr assembly.horizontalSource.ordered
    constructor
    · have hquotient : 0 ≤
          2 * (sourcePoint 2 - assembly.horizontalSource.c) /
            (assembly.horizontalSource.d - assembly.horizontalSource.c) := by
        exact div_nonneg (mul_nonneg (by norm_num)
          (sub_nonneg.mpr hsourceHeight.1)) hlengthPos.le
      linarith
    · apply (sub_lt_iff_lt_add).2
      apply (div_lt_iff₀ hlengthPos).2
      linarith [hsourceHeight.2]

/-- Select the fixed-width horizontal popular box used by the direct route. -/
theorem PureWZ2ExternalWeightRegularizationData.toDirectHorizontalPopularBoxFixed
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount) :
    Nonempty (PureWZ2HorizontalPopularBoxData
      (directFinalRaw (retubing := retubing)
        (regularized := regularized) data).exactShading
      pureWZ2DirectHorizontalBoxWidth) :=
  PureWZ2ExternalWeightRegularizationData.toDirectFinalHorizontalPopularBox
    (retubing := retubing) (regularized := regularized) data
    pureWZ2DirectHorizontalBoxWidth_pos
    pureWZ2DirectHorizontalBoxWidth_le_one

private theorem directHorizontalGeometry_budget
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) :
    pureWZ2DirectHorizontalScale *
        (pureWZ2DirectHorizontalBoxWidth / 2 +
          2 * ((assembly.horizontalSource.d - assembly.horizontalSource.c) +
            18 * delta)) ≤
      1 / 3 := by
  let scale := pureWZ2DirectHorizontalScale
  let rho := assembly.rho.1
  have hscalePos : 0 < scale := pureWZ2DirectHorizontalScale_pos
  have hrhoPos : 0 < rho :=
    assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1
  have hrhoOne : rho ≤ 1 :=
    assembly.rho_tiny.trans (by norm_num)
  have hdeltaRho : delta ≤ rho := by
    have hproduct : 0 ≤ rho * (1 - rho) :=
      mul_nonneg hrhoPos.le (sub_nonneg.mpr hrhoOne)
    nlinarith [assembly.delta_le_rho_sq]
  have hscaleRho : scale * rho ≤ 1 / 3200000 := by
    have hscaled := mul_le_mul_of_nonneg_left assembly.rho_final_tiny
      hscalePos.le
    have heq : scale * pureWZ2DirectFinalGeometryThreshold =
        1 / 3200000 := by
      change pureWZ2DirectFinalGeometryConstant *
        (1 / (3200000 * pureWZ2DirectFinalGeometryConstant)) =
          1 / 3200000
      field_simp [pureWZ2DirectFinalGeometryConstant_pos.ne']
    simpa [scale, heq] using hscaled
  have hscaleDelta : scale * delta ≤ 1 / 3200000 := by
    exact (mul_le_mul_of_nonneg_left hdeltaRho hscalePos.le).trans hscaleRho
  have hlength : assembly.horizontalSource.d -
      assembly.horizontalSource.c = rho / 100 := by
    rw [assembly.horizontalSource.length_eq, assembly.horizontalSource_scale]
  have hwidth : scale * (pureWZ2DirectHorizontalBoxWidth / 2) = 1 / 8 := by
    unfold pureWZ2DirectHorizontalBoxWidth
    dsimp only [scale]
    field_simp [pureWZ2DirectHorizontalScale_pos.ne']
    ring
  rw [hlength]
  calc
    scale *
        (pureWZ2DirectHorizontalBoxWidth / 2 +
          2 * (rho / 100 + 18 * delta)) =
      scale * (pureWZ2DirectHorizontalBoxWidth / 2) +
        2 / 100 * (scale * rho) + 36 * (scale * delta) := by ring
    _ ≤ 1 / 8 + 2 / 100 * (1 / 3200000) +
        36 * (1 / 3200000) := by
      rw [hwidth]
      gcongr
    _ ≤ 1 / 3 := by norm_num

namespace PureWZ2ExternalWeightRegularizationData

/-- Top-level CWA constant after the horizontal popular-box restriction and
deletion of empty pullback carriers. -/
def directHorizontalPopularSourceTopConstant
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount) : ENNReal :=
  pureWZ2HorizontalPopularPullbackCardinalityLoss delta
      pureWZ2DirectHorizontalBoxWidth regularized.selectedWeightLevel *
    directFinalSourceTopConstant (retubing := retubing)
      (regularized := regularized) data

/-- The horizontal nonempty pullback recovers top-level CWA through its
explicit mass-to-cardinality retention, rather than by treating CWA as
hereditary under arbitrary subfamilies. -/
theorem directHorizontalPopularSourceTopCWA
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount)
    (popular : PureWZ2HorizontalPopularBoxData
      (directFinalRaw (retubing := retubing)
        (regularized := regularized) data).exactShading
      pureWZ2DirectHorizontalBoxWidth) :
    WZ2PaperConvexWolffBound
      (pureWZ2HorizontalPopularPullbackSourceSubfamily
        (directFinalRaw (retubing := retubing)
          (regularized := regularized) data) popular).family
      (directHorizontalPopularSourceTopConstant
        (retubing := retubing) (regularized := regularized) data) := by
  let raw := directFinalRaw (retubing := retubing)
    (regularized := regularized) data
  let source := directFinalSourceShading (retubing := retubing)
    (regularized := regularized) data
  let selected := pureWZ2HorizontalPopularPullbackSourceSubfamily raw popular
  have hsourceLine : WZ1PaperIsLineClass data.selected.family :=
    (assembly.cfg.line_class.subfamily regularized.selected).subfamily
      data.selected
  have hcard := pureWZ2HorizontalPopularPullback_cardinality_retention
    raw popular assembly.cfg.extremal.delta_pos
    (assembly.delta_small.trans (by norm_num))
    pureWZ2DirectHorizontalBoxWidth_pos regularized.selectedWeightLevel
    regularized.selectedWeightLevel_pos.ne'
    regularized.selectedWeightLevel_ne_top
    (directFinalSourceShading_mass_lower data) hsourceLine
  exact (directFinalSourceTopCWA data).subfamily_of_cardinality selected hcard

/-- The combined triangular/horizontal transformation has the honest
direction-normal product lower bound `1 / (3 * lambda)` on the genuine
nonempty source family. -/
theorem directHorizontalPopular_norm_product_lower
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount)
    (popular : PureWZ2HorizontalPopularBoxData
      (directFinalRaw (retubing := retubing)
        (regularized := regularized) data).exactShading
      pureWZ2DirectHorizontalBoxWidth) :
    ∀ index point
      (hpoint : point ∈
        (pureWZ2HorizontalPopularPullbackNonemptyShading
          (directFinalRaw (retubing := retubing)
            (regularized := regularized) data) popular).carrier index),
      pureWZ2DirectHorizontalProductLower ≤
        ‖(pureWZ2HorizontalNormalizedAffineEquiv
          (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          (pureWZ2DirectAnisotropicCenter retubing.popular) popular.center
          pureWZ2DirectHorizontalScale assembly.horizontalSource.ordered
          assembly.horizontalSource.slopeScale_pos
          pureWZ2DirectHorizontalScale_pos).linear
          ((pureWZ2HorizontalPopularPullbackSourceSubfamily
            (directFinalRaw (retubing := retubing)
              (regularized := regularized) data) popular).family.tube
            index).direction‖ *
        ‖pureWZ2HorizontalNormalizedExactNormal
          (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m pureWZ2DirectHorizontalScale
          ((directHorizontalPopularNonemptySourceLocalGrains data popular).planeMap
            ⟨point, ⟨index, hpoint⟩⟩)‖ := by
  intro index point hpoint
  let direction :=
    ((pureWZ2HorizontalPopularPullbackSourceSubfamily
      (directFinalRaw (retubing := retubing)
        (regularized := regularized) data) popular).family.tube index).direction
  let normal :=
    (directHorizontalPopularNonemptySourceLocalGrains data popular).planeMap
      ⟨point, ⟨index, hpoint⟩⟩
  let targetProduct :=
    ‖(pureWZ2HorizontalNormalizedAffineEquiv
      (pureWZ2DirectGeometrySlope assembly.horizontalSource)
      assembly.horizontalSource.c assembly.horizontalSource.d
      assembly.horizontalSource.m
      (pureWZ2DirectAnisotropicCenter retubing.popular) popular.center
      pureWZ2DirectHorizontalScale assembly.horizontalSource.ordered
      assembly.horizontalSource.slopeScale_pos
      pureWZ2DirectHorizontalScale_pos).linear direction‖ *
    ‖pureWZ2HorizontalNormalizedExactNormal
      (pureWZ2DirectGeometrySlope assembly.horizontalSource)
      assembly.horizontalSource.c assembly.horizontalSource.d
      assembly.horizontalSource.m pureWZ2DirectHorizontalScale normal‖
  have htriangular :=
    directHorizontalPopularNonemptySource_direction_normal_product_lower
      data popular index point hpoint
  have htransport := pureWZ2HorizontalNormalized_norm_product_ge
    (pureWZ2DirectGeometrySlope assembly.horizontalSource)
    assembly.horizontalSource.ordered assembly.horizontalSource.slopeScale_pos
    pureWZ2DirectHorizontalScale_one
    (pureWZ2DirectAnisotropicCenter retubing.popular) popular.center
    direction normal
  have hscaled : (1 / 3 : ℝ) ≤
      pureWZ2DirectHorizontalScale * targetProduct := by
    exact htriangular.trans htransport
  change pureWZ2DirectHorizontalProductLower ≤ targetProduct
  calc
    pureWZ2DirectHorizontalProductLower =
        (1 / 3 : ℝ) / pureWZ2DirectHorizontalScale := by
      unfold pureWZ2DirectHorizontalProductLower
      ring
    _ ≤ targetProduct :=
      (div_le_iff₀ pureWZ2DirectHorizontalScale_pos).2 <| by
        simpa [mul_comm] using hscaled

/-- Exact horizontal target tubes obtained from the nonempty popular-box
pullback lie in the fixed paper line class. -/
theorem directHorizontalPopular_exactFamily_lineClass
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    {retubing : PureWZ2DirectAnisotropicRetubingData assembly}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    {regularized : PureWZ2DirectSourceRegularizationData
      retubing.popular scheduleConstant levelCount}
    {cleanup : PureWZ2AnisotropicPaperCenteredCleanupData
      (retubing.regularizedRaw regularized)
      (pureWZ2DirectRegularizedSourceTopConstant retubing regularized)}
    {outputConstant : ENNReal} {outputLevelCount : ℕ}
    (data : PureWZ2AnisotropicCleanupSourceRegularizationData cleanup
      regularized.outputConstant outputConstant
        regularized.selectedWeightLevel outputLevelCount)
    (popular : PureWZ2HorizontalPopularBoxData
      (directFinalRaw (retubing := retubing)
        (regularized := regularized) data).exactShading
      pureWZ2DirectHorizontalBoxWidth)
    {targetDelta : ℝ} :
    WZ1PaperIsLineClass
      (pureWZ2HorizontalNormalizedExactFamily (targetDelta := targetDelta)
        (pureWZ2HorizontalPopularPullbackSourceSubfamily
          (directFinalRaw (retubing := retubing)
            (regularized := regularized) data) popular).family
        (pureWZ2DirectGeometrySlope assembly.horizontalSource)
        assembly.horizontalSource.c assembly.horizontalSource.d
        assembly.horizontalSource.m
        (pureWZ2DirectAnisotropicCenter retubing.popular) popular.center
        pureWZ2DirectHorizontalScale assembly.horizontalSource.ordered
        assembly.horizontalSource.slopeScale_pos
        pureWZ2DirectHorizontalScale_pos) := by
  let raw := directFinalRaw (retubing := retubing)
    (regularized := regularized) data
  let selected := pureWZ2HorizontalPopularPullbackSourceSubfamily raw popular
  have hsourceLine : WZ1PaperIsLineClass data.selected.family :=
    (assembly.cfg.line_class.subfamily regularized.selected).subfamily
      data.selected
  have hselectedLine : WZ1PaperIsLineClass selected.family :=
    hsourceLine.subfamily selected
  have hlengthOne : assembly.horizontalSource.d -
      assembly.horizontalSource.c ≤ 1 := by
    rw [assembly.horizontalSource.length_eq, assembly.horizontalSource_scale]
    linarith [assembly.rho_tiny]
  have hscaleLength : pureWZ2DirectHorizontalScale *
      (assembly.horizontalSource.d - assembly.horizontalSource.c) ≤ 1 / 4 := by
    have hbudget := directHorizontalGeometry_budget assembly
    have hwidthNonnegative : 0 ≤ pureWZ2DirectHorizontalBoxWidth / 2 := by
      positivity [pureWZ2DirectHorizontalBoxWidth_pos]
    have hdeltaNonnegative : 0 ≤ delta := assembly.cfg.extremal.delta_pos.le
    have hlengthPositive : 0 < assembly.horizontalSource.d -
        assembly.horizontalSource.c :=
      sub_pos.mpr assembly.horizontalSource.ordered
    have hscaleNonnegative := pureWZ2DirectHorizontalScale_pos.le
    nlinarith [mul_nonneg hscaleNonnegative hwidthNonnegative,
      mul_nonneg hscaleNonnegative hdeltaNonnegative]
  have hgmid :
      |pureWZ2DirectGeometrySlope assembly.horizontalSource
        (assembly.horizontalSource.c +
          (assembly.horizontalSource.d - assembly.horizontalSource.c) / 2)| ≤ 1 :=
    (retubing.geometrySlope_normalized _
      (retubing.interval_sub_unit ⟨by
        linarith [assembly.horizontalSource.ordered], by
        linarith [assembly.horizontalSource.ordered]⟩)).1
  have hzero : ∀ index coordinate,
      coordinate = 0 ∨ coordinate = 1 →
      |pureWZ2HorizontalNormalizedZeroPoint
        (pureWZ2DirectGeometrySlope assembly.horizontalSource)
        assembly.horizontalSource.c assembly.horizontalSource.d
        assembly.horizontalSource.m
        (pureWZ2DirectAnisotropicCenter retubing.popular) popular.center
        pureWZ2DirectHorizontalScale (selected.family.tube index) coordinate| ≤
        1 / 3 := by
    intro index coordinate hcoordinate
    exact (pureWZ2HorizontalPopularPullback_zeroPoint_bound raw popular
      pureWZ2DirectHorizontalScale pureWZ2DirectHorizontalScale_pos
      assembly.cfg.extremal.delta_pos
      assembly.horizontalSource.slopeScale_le_one hlengthOne hgmid
      hsourceLine (directFinalSourceShading_height data)
      index coordinate hcoordinate).trans
        (directHorizontalGeometry_budget assembly)
  apply pureWZ2HorizontalNormalizedExactFamily_lineClass
    selected.family (pureWZ2DirectGeometrySlope assembly.horizontalSource)
      (pureWZ2DirectAnisotropicCenter retubing.popular) popular.center
      assembly.horizontalSource.ordered hlengthOne
      assembly.horizontalSource.slopeScale_pos
      assembly.horizontalSource.slopeScale_le_one
      pureWZ2DirectHorizontalScale_pos hscaleLength hgmid hselectedLine
  · intro index
    exact hzero index 0 (Or.inl rfl)
  · intro index
    exact hzero index 1 (Or.inr rfl)

end PureWZ2ExternalWeightRegularizationData

end Kakeya.Assouad

end
