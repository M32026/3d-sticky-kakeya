import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DiagonalRescaling
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalScaleData
import MyLeanRepo.Kakeya.Assouad.PureWZ2.IntervalSlopeJetExtension
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LineClassSlopeCompatibleNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.SlopeCompatibleNormalization

/-!
# Exact centered diagonal slope

This module implements the slope transported by the paper's pure diagonal
map, centered at the occupied height selected inside the mass-popular
subband.  The scale is `9/10` of the derivative-band scale.  This leaves a
fixed first-derivative margin, while the diagonal map reduces curvature by
the exact factor `1/100`.

The transported formula is retained on the whole active core.  Outside that
core, the compact-interval two-jet extension supplies a global calculus
witness without changing the paper-facing function where the transformed
shading lives.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- Translate the source height before applying the diagonal rescaling. -/
def pureWZ2HeightShiftedSlope
    (source : SlopeFunction) (anchor : ℝ) : SlopeFunction where
  toFun t := source (anchor + t)
  contDiff := source.contDiff.comp (contDiff_const.add contDiff_id)

theorem pureWZ2HeightShiftedSlope_deriv
    (source : SlopeFunction) (anchor t : ℝ) :
    deriv (pureWZ2HeightShiftedSlope source anchor) t =
      deriv source (anchor + t) := by
  change deriv (fun x : ℝ => source (anchor + x)) t = _
  exact deriv_comp_const_add source anchor t

theorem pureWZ2HeightShiftedSlope_second_deriv
    (source : SlopeFunction) (anchor t : ℝ) :
    deriv (deriv (pureWZ2HeightShiftedSlope source anchor)) t =
      deriv (deriv source) (anchor + t) := by
  have hfirst : deriv (pureWZ2HeightShiftedSlope source anchor) =
      fun x : ℝ => deriv source (anchor + x) := by
    funext x
    exact pureWZ2HeightShiftedSlope_deriv source anchor x
  rw [hfirst]
  exact deriv_comp_const_add (deriv source) anchor t

/-- The paper diagonal parameter with a one-percent derivative margin. -/
def pureWZ2ExactDiagonalScale
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta) : ℝ :=
  (9 : ℝ) / 10 * band.slopeScale

theorem pureWZ2ExactDiagonalScale_pos
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta) :
    0 < pureWZ2ExactDiagonalScale band := by
  exact mul_pos (by norm_num) band.slopeScale_pos

/-- Existing affine-diagonal geometry specialized to the paper's pure
diagonal map.  The wrapper records the specialization explicitly so callers
cannot silently switch back to the rotated Mobius chart. -/
structure PureWZ2ExactDiagonalAffineScaleData
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) where
  affineScale : PureWZ2AffineDiagonalScaleData subband
  anchor_midpoint : affineScale.slopeData.anchor = subband.anchor
  normalization_hundred :
    affineScale.slopeData.normalizationConstant = 100
  frame_zero : affineScale.slopeData.frameSlope = 0
  diagonal_scale : affineScale.slopeData.rotatedSlopeScale =
    pureWZ2ExactDiagonalScale band

/-- Construct the numerical affine-diagonal record with no horizontal
rotation.  Its spatial map is exactly the centered form of the paper's pure
diagonal map. -/
theorem PureWZ2MassPopularSubbandData.toExactDiagonalAffineScaleData
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    Nonempty (PureWZ2ExactDiagonalAffineScaleData subband) := by
  let source := band.lemma31.data.globalSlope
  let m := pureWZ2ExactDiagonalScale band
  let publicSlope :=
    pureWZ2FixedRotationLinearSlope source subband.anchor band.slopeScale
  let exactSlope :=
    pureWZ2AffineDiagonalExactSlope source 0 subband.anchor
      (100 / m) (m ^ 2 / 100)
  have hm : 0 < m := pureWZ2ExactDiagonalScale_pos band
  have hband := band.derivative_band subband.anchor subband.anchor_mem
  have htight :=
    band.derivative_tight_upper subband.anchor subband.anchor_mem
  have hpublic : publicSlope.IsNonsingular := by
    dsimp only [publicSlope, source]
    exact pureWZ2FixedRotationLinearSlope_nonsingular _
      band.slopeScale_pos hband.1 htight band.slopeScale_lower
  let slopeData : PureWZ2FixedRotationLinearSlopeData band :=
    { anchor := subband.anchor
      anchor_mem := subband.anchor_mem
      frameSlope := 0
      frameSlope_bound := by norm_num
      rotatedSlopeScale := m
      rotatedSlopeScale_pos := hm
      normalizationConstant := 100
      normalizationConstant_pos := by norm_num
      heightScale := 100 / m
      heightScale_eq := rfl
      transverseScale := m ^ 2 / 100
      transverseScale_eq := rfl
      publicSlope := publicSlope
      publicSlope_eq := rfl
      publicSlope_nonsingular := hpublic
      publicSlope_zero := by simp [publicSlope]
      exactSlope := exactSlope
      exactSlope_eq := rfl }
  let rho := band.lemma31.data.rho.1
  have hdelta : 0 < delta := band.lemma31.data.cfg.extremal.delta_pos
  have hrho : 0 < rho := hdelta.trans_le band.lemma31.data.rho.2.1
  have hmLower : rho / 2 ≤ m := by
    dsimp only [m, rho, pureWZ2ExactDiagonalScale]
    nlinarith [band.slopeScale_lower, band.slopeScale_pos]
  have hmOne : m ≤ 1 := by
    dsimp only [m, pureWZ2ExactDiagonalScale]
    nlinarith [band.slopeScale_le_one, band.slopeScale_pos]
  have hheightLower : 100 ≤ 100 / m := by
    exact (le_div_iff₀ hm).2 (by nlinarith [hmOne])
  have hheightUpper : 100 / m ≤ 200 / rho := by
    apply (div_le_iff₀ hm).2
    have hratio : (200 / rho) * (rho / 2) = 100 := by
      field_simp [hrho.ne']
      norm_num
    rw [← hratio]
    exact mul_le_mul_of_nonneg_left hmLower (by positivity)
  have htransversePos : 0 < m ^ 2 / 100 := by positivity
  have htransverseOne : m ^ 2 / 100 ≤ 1 / 100 := by
    nlinarith [sq_nonneg m]
  let targetDelta := 2 * (100 / m) * delta
  have htargetPos : 0 < targetDelta := by
    dsimp only [targetDelta]
    positivity
  have hsourceTarget : delta ≤ targetDelta := by
    dsimp only [targetDelta]
    have hone : 1 ≤ 2 * (100 / m) := by linarith [hheightLower]
    nlinarith
  have htargetUpper : targetDelta ≤ 1 / 10 := by
    calc
      targetDelta = 2 * (100 / m) * delta := rfl
      _ ≤ 2 * (200 / rho) * delta := by gcongr
      _ ≤ 400 * rho := by
        have hdeltaRho := band.lemma31.delta_le_rho_sq
        dsimp only [rho]
        rw [show 2 * (200 / band.lemma31.data.rho.1) * delta =
            400 * delta / band.lemma31.data.rho.1 by ring]
        exact (div_le_iff₀ hrho).2 <| by
          nlinarith [sq_nonneg band.lemma31.data.rho.1]
      _ ≤ 1 / 10 := by
        dsimp only [rho]
        linarith [band.lemma31.rho_tiny]
  let affineScale : PureWZ2AffineDiagonalScaleData subband :=
    { slopeData := slopeData
      slope_anchor_mem := by
        change subband.anchor ∈ Set.Icc subband.left subband.right
        rw [subband.anchor_eq]
        constructor <;> linarith [subband.ordered]
      rho := rho
      rho_eq := rfl
      rho_pos := hrho
      normalization_ge_hundred := by norm_num
      normalization_le_thousand := by norm_num
      rotated_lower := hmLower.trans' (by gcongr; norm_num)
      rotated_le_one := hmOne
      height_lower := hheightLower
      height_upper := hheightUpper.trans (by gcongr; norm_num)
      transverse_pos := htransversePos
      transverse_le := htransverseOne
      targetDelta := targetDelta
      targetDelta_eq := rfl
      targetDelta_pos := htargetPos
      source_le_target := hsourceTarget
      targetDelta_le_tenth := htargetUpper
      targetDelta_le_one := htargetUpper.trans (by norm_num) }
  exact ⟨{
    affineScale := affineScale
    anchor_midpoint := rfl
    normalization_hundred := rfl
    frame_zero := rfl
    diagonal_scale := rfl
  }⟩

/-- Exact centered slope transported by
`diag(1, m^2/100, 100/m)`, before extending its active two-jet. -/
def pureWZ2CenteredDiagonalExactSlope
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) : SlopeFunction :=
  diagonalRescaledSlope
    (pureWZ2HeightShiftedSlope band.lemma31.data.globalSlope subband.anchor)
    (pureWZ2ExactDiagonalScale band)

@[simp] theorem pureWZ2CenteredDiagonalExactSlope_apply
    {sigma epsilon delta t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    pureWZ2CenteredDiagonalExactSlope subband t =
      (100 / pureWZ2ExactDiagonalScale band ^ 2) *
        band.lemma31.data.globalSlope
          (subband.anchor + pureWZ2ExactDiagonalScale band / 100 * t) :=
  rfl

theorem pureWZ2CenteredDiagonalExactSlope_deriv
    {sigma epsilon delta t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    deriv (pureWZ2CenteredDiagonalExactSlope subband) t =
      (1 / pureWZ2ExactDiagonalScale band) *
        deriv band.lemma31.data.globalSlope
          (subband.anchor + pureWZ2ExactDiagonalScale band / 100 * t) := by
  rw [pureWZ2CenteredDiagonalExactSlope,
    diagonalRescaledSlope_deriv _ _
      (pureWZ2ExactDiagonalScale_pos band),
    pureWZ2HeightShiftedSlope_deriv]

theorem pureWZ2CenteredDiagonalExactSlope_second_deriv
    {sigma epsilon delta t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    deriv (deriv (pureWZ2CenteredDiagonalExactSlope subband)) t =
      (1 / 100) * deriv (deriv band.lemma31.data.globalSlope)
        (subband.anchor + pureWZ2ExactDiagonalScale band / 100 * t) := by
  rw [pureWZ2CenteredDiagonalExactSlope,
    diagonalRescaledSlope_deriv2 _ _
      (pureWZ2ExactDiagonalScale_pos band),
    pureWZ2HeightShiftedSlope_second_deriv]

/-- The exact slope stored by the zero-frame affine geometry record is the
same centered pure-diagonal slope used by the public certificate. -/
theorem PureWZ2ExactDiagonalAffineScaleData.exactSlope_eq_centeredDiagonal
    {sigma epsilon delta t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (data : PureWZ2ExactDiagonalAffineScaleData subband) :
    data.affineScale.slopeData.exactSlope t =
      pureWZ2CenteredDiagonalExactSlope subband t := by
  rw [data.affineScale.slopeData.exactSlope_eq, data.frame_zero]
  simp only [pureWZ2AffineDiagonalExactSlope,
    pureWZ2RotatedSlopeValue, zero_mul, add_zero, sub_zero, div_one]
  rw [data.anchor_midpoint]
  rw [data.affineScale.slopeData.heightScale_eq, data.diagonal_scale,
    data.affineScale.slopeData.transverseScale_eq, data.diagonal_scale]
  rw [data.normalization_hundred]
  rw [pureWZ2CenteredDiagonalExactSlope_apply]
  have hm := pureWZ2ExactDiagonalScale_pos band
  field_simp [hm.ne']

/-- Left endpoint of the target-height core corresponding to the selected
source subband. -/
def pureWZ2ExactDiagonalCoreLeft
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) : ℝ :=
  (100 / pureWZ2ExactDiagonalScale band) *
    (subband.left - subband.anchor)

/-- Right endpoint of the target-height core corresponding to the selected
source subband. -/
def pureWZ2ExactDiagonalCoreRight
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) : ℝ :=
  (100 / pureWZ2ExactDiagonalScale band) *
    (subband.right - subband.anchor)

theorem pureWZ2ExactDiagonalCore_ordered
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    pureWZ2ExactDiagonalCoreLeft subband <
      pureWZ2ExactDiagonalCoreRight subband := by
  unfold pureWZ2ExactDiagonalCoreLeft pureWZ2ExactDiagonalCoreRight
  have hfactor : 0 < 100 / pureWZ2ExactDiagonalScale band := by
    exact div_pos (by norm_num) (pureWZ2ExactDiagonalScale_pos band)
  apply mul_lt_mul_of_pos_left _ hfactor
  linarith [subband.ordered]

theorem pureWZ2ExactDiagonalCore_zero_mem
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    (0 : ℝ) ∈ Set.Icc (pureWZ2ExactDiagonalCoreLeft subband)
      (pureWZ2ExactDiagonalCoreRight subband) := by
  have hfactor : 0 < 100 / pureWZ2ExactDiagonalScale band := by
    exact div_pos (by norm_num) (pureWZ2ExactDiagonalScale_pos band)
  have hleft : subband.left ≤ subband.anchor := by
    rw [subband.anchor_eq]
    linarith [subband.ordered]
  have hright : subband.anchor ≤ subband.right := by
    rw [subband.anchor_eq]
    linarith [subband.ordered]
  constructor
  · unfold pureWZ2ExactDiagonalCoreLeft
    exact mul_nonpos_of_nonneg_of_nonpos hfactor.le (sub_nonpos.mpr hleft)
  · unfold pureWZ2ExactDiagonalCoreRight
    exact mul_nonneg hfactor.le (sub_nonneg.mpr hright)

/-- The centered diagonal target coordinate maps exactly back into the
selected source subband. -/
theorem pureWZ2ExactDiagonal_sourceHeight_mem
    {sigma epsilon delta t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (ht : t ∈ Set.Icc (pureWZ2ExactDiagonalCoreLeft subband)
      (pureWZ2ExactDiagonalCoreRight subband)) :
    subband.anchor + pureWZ2ExactDiagonalScale band / 100 * t ∈
      Set.Icc subband.left subband.right := by
  have hm := pureWZ2ExactDiagonalScale_pos band
  have hforward : 0 < pureWZ2ExactDiagonalScale band / 100 := by
    positivity
  have hinverse :
      pureWZ2ExactDiagonalScale band / 100 *
        (100 / pureWZ2ExactDiagonalScale band) = 1 := by
    field_simp [hm.ne']
  have hcancel (x : ℝ) :
      pureWZ2ExactDiagonalScale band / 100 *
          (100 / pureWZ2ExactDiagonalScale band * x) = x := by
    rw [← mul_assoc, hinverse, one_mul]
  constructor
  · have hmul := mul_le_mul_of_nonneg_left ht.1 hforward.le
    unfold pureWZ2ExactDiagonalCoreLeft at hmul
    rw [hcancel] at hmul
    linarith
  · have hmul := mul_le_mul_of_nonneg_left ht.2 hforward.le
    unfold pureWZ2ExactDiagonalCoreRight at hmul
    rw [hcancel] at hmul
    linarith

/-- The exact diagonal slope has the quantitative derivative margin needed
to survive extension from the active core to the public unit interval. -/
theorem pureWZ2CenteredDiagonalExactSlope_core_bounds
    {sigma epsilon delta t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (ht : t ∈ Set.Icc (pureWZ2ExactDiagonalCoreLeft subband)
      (pureWZ2ExactDiagonalCoreRight subband)) :
    (10 : ℝ) / 9 ≤
        |deriv (pureWZ2CenteredDiagonalExactSlope subband) t| ∧
      |deriv (pureWZ2CenteredDiagonalExactSlope subband) t| ≤
        (17 : ℝ) / 15 ∧
      |deriv (deriv (pureWZ2CenteredDiagonalExactSlope subband)) t| ≤
        1 / 100 := by
  let sourceHeight :=
    subband.anchor + pureWZ2ExactDiagonalScale band / 100 * t
  have hsourceSubband : sourceHeight ∈ Set.Icc subband.left subband.right :=
    pureWZ2ExactDiagonal_sourceHeight_mem subband ht
  have hsourceBand : sourceHeight ∈ Set.Icc band.left band.right :=
    ⟨subband.left_mem.trans hsourceSubband.1,
      hsourceSubband.2.trans subband.right_mem⟩
  have hderivative := band.derivative_band sourceHeight hsourceBand
  have htight := band.derivative_tight_upper sourceHeight hsourceBand
  have hsourcePaper : sourceHeight ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨band.lemma31.data.scaleData.slabLeft_mem.trans
        (band.left_mem.trans hsourceBand.1),
      (hsourceBand.2.trans band.right_mem).trans
        band.lemma31.data.scaleData.slabRight_mem⟩
  have hsecondSource :
      |deriv (deriv band.lemma31.data.globalSlope) sourceHeight| ≤ 1 :=
    (band.lemma31.data.globalSlope_normalized sourceHeight hsourcePaper).2.2
  have hm := pureWZ2ExactDiagonalScale_pos band
  rw [pureWZ2CenteredDiagonalExactSlope_deriv subband, abs_mul,
    abs_of_pos (one_div_pos.mpr hm)]
  rw [one_div]
  constructor
  · apply (le_inv_mul_iff₀ hm).2
    dsimp only [sourceHeight] at hderivative
    calc
      pureWZ2ExactDiagonalScale band * ((10 : ℝ) / 9) =
          band.slopeScale := by
        unfold pureWZ2ExactDiagonalScale
        ring
      _ ≤ |deriv band.lemma31.data.globalSlope
          (subband.anchor +
            pureWZ2ExactDiagonalScale band / 100 * t)| := hderivative.1
  constructor
  · apply (inv_mul_le_iff₀ hm).2
    dsimp only [sourceHeight] at htight
    calc
      |deriv band.lemma31.data.globalSlope
          (subband.anchor +
            pureWZ2ExactDiagonalScale band / 100 * t)| ≤
          band.slopeScale + band.lemma31.data.rho.1 / 50 := htight
      _ ≤ band.slopeScale + band.slopeScale / 50 := by
        gcongr
        exact band.slopeScale_lower
      _ = pureWZ2ExactDiagonalScale band * ((17 : ℝ) / 15) := by
        unfold pureWZ2ExactDiagonalScale
        ring
  · rw [pureWZ2CenteredDiagonalExactSlope_second_deriv subband, abs_mul]
    norm_num
    simpa only [sourceHeight] using hsecondSource

/-- Canonical two-jet extension of the exact centered diagonal slope from
its active target-height core. -/
def pureWZ2ExactDiagonalSlopeExtensionData
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    PureWZ2IntervalSlopeJetExtensionData
      (pureWZ2CenteredDiagonalExactSlope subband)
      (pureWZ2ExactDiagonalCoreLeft subband)
      (pureWZ2ExactDiagonalCoreRight subband)
      (pureWZ2ExactDiagonalCore_ordered subband).le :=
  Classical.choice <| pureWZ2_intervalSlopeJetExtension
    (pureWZ2CenteredDiagonalExactSlope subband)
    (pureWZ2ExactDiagonalCore_ordered subband).le

/-- Public exact diagonal slope.  It is globally smooth internally and is
literally the transported paper slope on the active target-height core. -/
def pureWZ2ExactDiagonalSlope
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) : SlopeFunction :=
  (pureWZ2ExactDiagonalSlopeExtensionData subband).slope

theorem pureWZ2ExactDiagonalSlope_eq_on_core
    {sigma epsilon delta t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (ht : t ∈ Set.Icc (pureWZ2ExactDiagonalCoreLeft subband)
      (pureWZ2ExactDiagonalCoreRight subband)) :
    pureWZ2ExactDiagonalSlope subband t =
      (100 / pureWZ2ExactDiagonalScale band ^ 2) *
        band.lemma31.data.globalSlope
          (subband.anchor + pureWZ2ExactDiagonalScale band / 100 * t) := by
  rw [pureWZ2ExactDiagonalSlope]
  rw [(pureWZ2ExactDiagonalSlopeExtensionData subband).eq_on t ht]
  rfl

/-- The extended exact slope obeys the public derivative bounds on the wider
interval `[-2,2]`.  This extra room permits a later slope-compatible
normalization centered anywhere in `[-1,1]`. -/
theorem pureWZ2ExactDiagonalSlope_bounds_on_two
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    ∀ t ∈ Set.Icc (-2 : ℝ) 2,
      1 ≤ |deriv (pureWZ2ExactDiagonalSlope subband) t| ∧
        |deriv (pureWZ2ExactDiagonalSlope subband) t| ≤ 2 ∧
        |deriv (deriv (pureWZ2ExactDiagonalSlope subband)) t| ≤
          1 / 100 := by
  have hcurvature : ∀ t ∈
      Set.Icc (pureWZ2ExactDiagonalCoreLeft subband)
        (pureWZ2ExactDiagonalCoreRight subband),
      |deriv (deriv (pureWZ2CenteredDiagonalExactSlope subband)) t| ≤
        (1 : ℝ) / 100 := by
    intro t ht
    exact (pureWZ2CenteredDiagonalExactSlope_core_bounds subband ht).2.2
  intro t ht
  let projected : ℝ := Set.projIcc
    (pureWZ2ExactDiagonalCoreLeft subband)
    (pureWZ2ExactDiagonalCoreRight subband)
    (pureWZ2ExactDiagonalCore_ordered subband).le t
  have hprojected : projected ∈
      Set.Icc (pureWZ2ExactDiagonalCoreLeft subband)
        (pureWZ2ExactDiagonalCoreRight subband) :=
    (Set.projIcc _ _ _ t).property
  have hprojectedBounds :=
    pureWZ2CenteredDiagonalExactSlope_core_bounds subband hprojected
  have hdistance : |t - projected| ≤ 2 := by
    calc
      |t - projected| ≤ |t - 0| := by
        exact abs_sub_projIcc_le_of_mem
          (pureWZ2ExactDiagonalCore_ordered subband).le
          (pureWZ2ExactDiagonalCore_zero_mem subband)
      _ = |t| := by ring_nf
      _ ≤ 2 := abs_le.mpr ht
  have hdrift :=
    (pureWZ2ExactDiagonalSlopeExtensionData subband).deriv_sub_proj_abs_le
      hcurvature t
  change |deriv (pureWZ2ExactDiagonalSlope subband) t -
      deriv (pureWZ2CenteredDiagonalExactSlope subband) projected| ≤
        (1 : ℝ) / 100 * |t - projected| at hdrift
  have hdriftSmall :
      |deriv (pureWZ2ExactDiagonalSlope subband) t -
        deriv (pureWZ2CenteredDiagonalExactSlope subband) projected| ≤
          (1 : ℝ) / 50 := by
    exact hdrift.trans <| by
      nlinarith [abs_nonneg (t - projected)]
  let extendedDeriv := deriv (pureWZ2ExactDiagonalSlope subband) t
  let coreDeriv :=
    deriv (pureWZ2CenteredDiagonalExactSlope subband) projected
  have habsDifference :
      abs (abs extendedDeriv - abs coreDeriv) ≤ (1 : ℝ) / 50 := by
    exact (abs_abs_sub_abs_le_abs_sub extendedDeriv coreDeriv).trans <| by
      simpa only [extendedDeriv, coreDeriv] using hdriftSmall
  have habsBounds := abs_le.mp habsDifference
  dsimp only [extendedDeriv, coreDeriv] at habsBounds
  constructor
  · nlinarith [hprojectedBounds.1]
  constructor
  · nlinarith [hprojectedBounds.2.1]
  · change |deriv (deriv
        (pureWZ2ExactDiagonalSlopeExtensionData subband).slope) t| ≤ _
    exact (pureWZ2ExactDiagonalSlopeExtensionData subband).second_deriv_abs_le
      hcurvature t

theorem pureWZ2ExactDiagonalSlope_nonsingular
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    (pureWZ2ExactDiagonalSlope subband).IsNonsingular := by
  intro t ht
  exact pureWZ2ExactDiagonalSlope_bounds_on_two subband t
    ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- The exact transported public slope is uniformly two-Lipschitz on the
wider interval used by its two-jet extension. -/
theorem pureWZ2ExactDiagonalSlope_lipschitzOn_two
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    LipschitzOnWith 2 (pureWZ2ExactDiagonalSlope subband)
      (Set.Icc (-2 : ℝ) 2) := by
  have hdifferentiable : Differentiable ℝ
      (pureWZ2ExactDiagonalSlope subband) :=
    (pureWZ2ExactDiagonalSlope subband).contDiff.differentiable (by norm_num)
  apply (convex_Icc (-2 : ℝ) 2).lipschitzOnWith_of_nnnorm_deriv_le
  · intro t _ht
    exact hdifferentiable.differentiableAt
  · intro t ht
    apply NNReal.coe_le_coe.mp
    simpa [Real.norm_eq_abs] using
      (pureWZ2ExactDiagonalSlope_bounds_on_two subband t ht).2.1

/-- A value bound for the exact public slope which keeps its genuine
transported value at zero.  In particular, this does not assume or conclude
that the public slope vanishes at the origin. -/
theorem pureWZ2ExactDiagonalSlope_abs_le
    {sigma epsilon delta t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |pureWZ2ExactDiagonalSlope subband t| ≤
      100 / pureWZ2ExactDiagonalScale band ^ 2 + 2 := by
  have hm : 0 < pureWZ2ExactDiagonalScale band :=
    pureWZ2ExactDiagonalScale_pos band
  have hanchor : subband.anchor ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨band.lemma31.data.scaleData.slabLeft_mem.trans
        (band.left_mem.trans subband.anchor_mem.1),
      subband.anchor_mem.2.trans <| band.right_mem.trans
        band.lemma31.data.scaleData.slabRight_mem⟩
  have hsource : |band.lemma31.data.globalSlope subband.anchor| ≤ 1 :=
    (band.lemma31.data.globalSlope_normalized subband.anchor hanchor).1
  have hzero : |pureWZ2ExactDiagonalSlope subband 0| ≤
      100 / pureWZ2ExactDiagonalScale band ^ 2 := by
    rw [pureWZ2ExactDiagonalSlope_eq_on_core subband
      (pureWZ2ExactDiagonalCore_zero_mem subband)]
    simp only [mul_zero, add_zero, abs_mul]
    rw [abs_of_pos (by positivity :
      0 < 100 / pureWZ2ExactDiagonalScale band ^ 2)]
    exact mul_le_of_le_one_right (by positivity) hsource
  have htTwo : t ∈ Set.Icc (-2 : ℝ) 2 :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hlipschitz :=
    (pureWZ2ExactDiagonalSlope_lipschitzOn_two subband).dist_le_mul
      t htTwo 0 (by norm_num)
  have hdifference :
      |pureWZ2ExactDiagonalSlope subband t -
          pureWZ2ExactDiagonalSlope subband 0| ≤ 2 := by
    calc
      |pureWZ2ExactDiagonalSlope subband t -
          pureWZ2ExactDiagonalSlope subband 0| ≤ 2 * |t| := by
        simpa [Real.dist_eq] using hlipschitz
      _ ≤ 2 := by
        have habs : |t| ≤ 1 := abs_le.mpr ht
        nlinarith
  calc
    |pureWZ2ExactDiagonalSlope subband t| ≤
        |pureWZ2ExactDiagonalSlope subband 0| +
          |pureWZ2ExactDiagonalSlope subband t -
            pureWZ2ExactDiagonalSlope subband 0| := by
      have := abs_add_le
        (pureWZ2ExactDiagonalSlope subband 0)
        (pureWZ2ExactDiagonalSlope subband t -
          pureWZ2ExactDiagonalSlope subband 0)
      simpa [add_sub_cancel] using this
    _ ≤ 100 / pureWZ2ExactDiagonalScale band ^ 2 + 2 :=
      add_le_add hzero hdifference

/-- Exact diagonal slope after the final derivative-preserving normalization
`diag(lambda^2, lambda, lambda)`. -/
def pureWZ2SlopeCompatibleExactDiagonalSlope
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (centerHeight lambda : ℝ) : SlopeFunction :=
  pureWZ2SlopeCompatibleNormalizedSlope
    (pureWZ2ExactDiagonalSlope subband) centerHeight lambda

/-- The final slope-compatible normalization preserves exact-diagonal
nonsingularity even when its center lies at an endpoint of `[-1,1]`. -/
theorem pureWZ2SlopeCompatibleExactDiagonalSlope_nonsingular
    {sigma epsilon delta centerHeight lambda : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hlambda : 1 ≤ lambda)
    (hcenter : centerHeight ∈ Set.Icc (-1 : ℝ) 1) :
    (pureWZ2SlopeCompatibleExactDiagonalSlope
      subband centerHeight lambda).IsNonsingular := by
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  intro t ht
  have hsource : centerHeight + t / lambda ∈ Set.Icc (-2 : ℝ) 2 := by
    have htAbs : |t| ≤ 1 := abs_le.mpr ht
    have hquotientAbs : |t / lambda| ≤ 1 := by
      rw [abs_div, abs_of_pos hlambdaPos]
      exact (div_le_one hlambdaPos).2 <| htAbs.trans hlambda
    rw [abs_le] at hquotientAbs
    exact ⟨by linarith [hcenter.1, hquotientAbs.1],
      by linarith [hcenter.2, hquotientAbs.2]⟩
  have hbounds := pureWZ2ExactDiagonalSlope_bounds_on_two
    subband (centerHeight + t / lambda) hsource
  change
    1 ≤ |deriv (pureWZ2LineClassNormalizedSlope
        (pureWZ2ExactDiagonalSlope subband) centerHeight lambda) t| ∧
      |deriv (pureWZ2LineClassNormalizedSlope
        (pureWZ2ExactDiagonalSlope subband) centerHeight lambda) t| ≤ 2 ∧
      |deriv (deriv (pureWZ2LineClassNormalizedSlope
        (pureWZ2ExactDiagonalSlope subband) centerHeight lambda)) t| ≤
        1 / 100
  rw [pureWZ2LineClassNormalizedSlope_deriv _ _ hlambdaPos,
    pureWZ2LineClassNormalizedSlope_second_deriv _ _ hlambdaPos]
  refine ⟨hbounds.1, hbounds.2.1, ?_⟩
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hlambdaPos)]
  calc
    1 / lambda *
        |deriv (deriv (pureWZ2ExactDiagonalSlope subband))
          (centerHeight + t / lambda)| ≤
      1 * (1 / 100 : ℝ) := by
        gcongr
        exact (div_le_one hlambdaPos).2 hlambda
        exact hbounds.2.2
    _ = 1 / 100 := by norm_num

/-- On the portion mapped back to the active core, the final public slope is
literally the source slope transported by the same composite diagonal map. -/
theorem pureWZ2SlopeCompatibleExactDiagonalSlope_eq_on_core
    {sigma epsilon delta centerHeight lambda t : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band)
    (hsource : centerHeight + t / lambda ∈
      Set.Icc (pureWZ2ExactDiagonalCoreLeft subband)
        (pureWZ2ExactDiagonalCoreRight subband)) :
    pureWZ2SlopeCompatibleExactDiagonalSlope subband centerHeight lambda t =
      lambda *
        ((100 / pureWZ2ExactDiagonalScale band ^ 2) *
          band.lemma31.data.globalSlope
            (subband.anchor + pureWZ2ExactDiagonalScale band / 100 *
              (centerHeight + t / lambda))) := by
  change lambda * (pureWZ2ExactDiagonalSlope subband)
      (centerHeight + t / lambda) = _
  rw [pureWZ2ExactDiagonalSlope_eq_on_core subband hsource]

/-- Public interval-domain certificate for the exact transported diagonal
slope. -/
theorem pureWZ2ExactDiagonalSlope_public_nonsingular
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (subband : PureWZ2MassPopularSubbandData band) :
    PureWZ2C2SlopeIsNonsingular
      (pureWZ2ExactDiagonalSlope subband).onUnitInterval :=
  SlopeFunction.nonsingular_onUnitInterval _
    (pureWZ2ExactDiagonalSlope_nonsingular subband)

end Kakeya.Assouad

end
