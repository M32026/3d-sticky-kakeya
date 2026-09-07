import MyLeanRepo.Kakeya.Assouad.PureWZ2.IntervalSlopeExtension
import MyLeanRepo.Kakeya.Assouad.SlopeRescaling
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.MassSlopeSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CroppedRefinementData
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PopularBoxLocalGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicProjectionIdentity

/-!
# Centered nonsingular rescaling from interval-local C2 data

This is the paper-domain counterpart of `large_slope_to_centered_nonsingular`.
The input representative is only C2 on `[-1,1]`.  We first move a fixed
distance into the interval, extend there with a smooth cutoff, and perform
the derivative pigeonhole and centered rescaling on that internal witness.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2IntervalNonsingularSlopeData
    (source : ℝ → ℝ) (a b L : ℝ) where
  c : ℝ
  d : ℝ
  m : ℝ
  left_mem : a ≤ c
  ordered : c < d
  right_mem : d ≤ b
  slopeScale_pos : 0 < m
  slopeScale_lower : L ≤ m
  slopeScale_le_one : m ≤ 1
  length_eq : d - c = L / 50
  sourceExtension : SlopeFunction
  extension_eq : ∀ x ∈ Set.Icc c d, sourceExtension x = source x
  extension_deriv_eq :
    ∀ x ∈ Set.Icc c d, deriv sourceExtension x = deriv source x
  extension_second_deriv_eq :
    ∀ x ∈ Set.Icc c d,
      deriv (deriv sourceExtension) x = deriv (deriv source) x
  derivative_band : ∀ x ∈ Set.Icc c d,
    m ≤ |deriv sourceExtension x| ∧
      |deriv sourceExtension x| ≤ 2 * m
  slope : SlopeFunction
  slope_nonsingular : slope.IsNonsingular
  slope_formula : ∀ t : ℝ,
    slope t =
      sourceExtension (c + (d - c) / 2 * (t + 1)) /
          (m * (d - c) / 2) -
        sourceExtension (c + (d - c) / 2) /
          (m * (d - c) / 2)

/-- Perform the Section-6 interval selection and rescaling from the actual
interval-local Node-5 representative. -/
theorem pureWZ2_interval_to_nonsingular_slope
    (source : ℝ → ℝ)
    (hsmooth : ContDiffOn ℝ 2 source (Set.Icc (-1 : ℝ) 1))
    (hnormalized : PureWZ2AmbientSlopeIsNormalized source)
    {a b L : ℝ}
    (hab : a < b)
    (hwidth : b - a = L)
    (hL : 0 < L)
    (hsub : Set.Icc a b ⊆ Set.Icc (-1 : ℝ) 1)
    (hlower : ∀ x ∈ Set.Icc a b, L ≤ |deriv source x|) :
    Nonempty (PureWZ2IntervalNonsingularSlopeData source a b L) := by
  let innerLeft := a + L / 100
  let innerRight := b - L / 100
  have hinnerLeft : a < innerLeft := by
    dsimp only [innerLeft]
    linarith
  have hinnerRight : innerRight < b := by
    dsimp only [innerRight]
    linarith
  have hinnerOrder : innerLeft < innerRight := by
    dsimp only [innerLeft, innerRight]
    linarith [hwidth]
  have hinnerLength : L / 4 ≤ innerRight - innerLeft := by
    dsimp only [innerLeft, innerRight]
    linarith [hwidth]
  have hinnerSub : Set.Icc innerLeft innerRight ⊆ Set.Icc a b := by
    intro x hx
    exact ⟨hinnerLeft.le.trans hx.1, hx.2.trans hinnerRight.le⟩
  have hinnerAmbient : Set.Icc innerLeft innerRight ⊆
      Set.Icc (-1 : ℝ) 1 := hinnerSub.trans hsub
  have hleftStrict : -1 < innerLeft := by
    have haLower := (hsub
      (show a ∈ Set.Icc a b from ⟨le_rfl, hab.le⟩)).1
    linarith
  have hrightStrict : innerRight < 1 := by
    have hbUpper := (hsub
      (show b ∈ Set.Icc a b from ⟨hab.le, le_rfl⟩)).2
    linarith
  let coreRadius := max |innerLeft| |innerRight|
  let innerRadius := (coreRadius + 1) / 2
  let outerRadius := (innerRadius + 1) / 2
  have hleftAbs : |innerLeft| < 1 :=
    abs_lt.mpr ⟨hleftStrict, hinnerOrder.trans hrightStrict⟩
  have hrightAbs : |innerRight| < 1 :=
    abs_lt.mpr ⟨hleftStrict.trans hinnerOrder, hrightStrict⟩
  have hcoreRadius : coreRadius < 1 := by
    exact max_lt hleftAbs hrightAbs
  have hcoreRadiusNonneg : 0 ≤ coreRadius := by
    exact (abs_nonneg innerLeft).trans (le_max_left _ _)
  have hinnerRadius : 0 < innerRadius := by
    dsimp only [innerRadius]
    linarith
  have hcoreInner : coreRadius < innerRadius := by
    dsimp only [innerRadius]
    linarith
  have hinnerOuter : innerRadius < outerRadius := by
    dsimp only [outerRadius]
    have hinnerRadiusOne : innerRadius < 1 := by
      dsimp only [innerRadius]
      linarith [hcoreRadius]
    linarith
  have houterOne : outerRadius < 1 := by
    dsimp only [outerRadius, innerRadius]
    linarith [hcoreRadius]
  rcases pureWZ2_intervalSlopeExtension source
      (Set.Icc innerLeft innerRight) 0
      innerRadius outerRadius hinnerRadius hinnerOuter
      (by
        intro x hx
        rw [Metric.mem_ball, Real.dist_eq]
        have habs : |x| ≤ coreRadius :=
          abs_le_max_abs_abs hx.1 hx.2
        simpa only [sub_zero] using habs.trans_lt hcoreInner)
      (by
        intro x hx
        rw [Metric.mem_closedBall, Real.dist_eq] at hx
        have hxabs : |x| < 1 := by
          simpa only [sub_zero] using hx.trans_lt houterOne
        exact abs_lt.mp hxabs)
      hsmooth with ⟨extension⟩
  have hsecond : ∀ x ∈ Set.Icc innerLeft innerRight,
      |deriv (deriv extension.slope) x| ≤ 1 := by
    intro x hx
    rw [extension.second_deriv_eq_on x hx]
    exact (hnormalized x (hinnerAmbient hx)).2.2
  have hlow : ∀ x ∈ Set.Icc innerLeft innerRight,
      L ≤ |deriv extension.slope x| := by
    intro x hx
    rw [extension.deriv_eq_on x hx]
    exact hlower x (hinnerSub hx)
  have hhigh : ∀ x ∈ Set.Icc innerLeft innerRight,
      |deriv extension.slope x| ≤ 1 := by
    intro x hx
    rw [extension.deriv_eq_on x hx]
    exact (hnormalized x (hinnerAmbient hx)).2.1
  rcases derivative_bracketing extension.slope.contDiff hsecond
      hinnerOrder hL hinnerLength hlow hhigh with
    ⟨c0, d0, m, hc0, hc0d0, hd0, hlength0, hm, hmLower, hmOne, hband⟩
  let c := c0
  let d := c0 + L / 50
  have hcd : c < d := by dsimp only [c, d]; linarith [hL]
  have hshort : L / 50 ≤ d0 - c0 := by
    calc
      L / 50 ≤ L / 4 := by linarith [hL]
      _ ≤ d0 - c0 := hlength0
  have hd : d ≤ b := by
    have : d ≤ d0 := by dsimp only [d, c]; linarith
    exact this.trans (hd0.trans hinnerRight.le)
  have hc : a ≤ c := hinnerLeft.le.trans hc0
  have hcdBracket : Set.Icc c d ⊆ Set.Icc c0 d0 := by
    intro x hx
    exact ⟨by simpa [c] using hx.1, hx.2.trans (by
      dsimp only [d, c]
      linarith)⟩
  have hcdCore : Set.Icc c d ⊆ Set.Icc innerLeft innerRight := by
    intro x hx
    exact ⟨hc0.trans (hcdBracket hx).1,
      (hcdBracket hx).2.trans hd0⟩
  have hband' : ∀ x ∈ Set.Icc c d,
      m ≤ |deriv extension.slope x| ∧
        |deriv extension.slope x| ≤ 2 * m := by
    intro x hx
    exact hband x (hcdBracket hx)
  have hsecond' : ∀ x ∈ Set.Icc c d,
      |deriv (deriv extension.slope) x| ≤ 1 := by
    intro x hx
    exact hsecond x (hcdCore hx)
  have hcdAmbient : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1 :=
    hcdCore.trans hinnerAmbient
  have hlength : d - c = L / 50 := by
    dsimp only [c, d]
    ring
  rcases slope_rescaling_to_centered_nonsingular_of_second
      extension.slope hcd hm hcdAmbient hband' hsecond'
      (by rw [hlength]; exact div_le_div_of_nonneg_right hmLower (by norm_num))
    with ⟨slope, hslope, _hzero, hformula⟩
  exact ⟨{
    c := c
    d := d
    m := m
    left_mem := hc
    ordered := hcd
    right_mem := hd
    slopeScale_pos := hm
    slopeScale_lower := hmLower
    slopeScale_le_one := hmOne
    length_eq := hlength
    sourceExtension := extension.slope
    extension_eq := fun x hx => extension.eq_on x (hcdCore hx)
    extension_deriv_eq := fun x hx => extension.deriv_eq_on x (hcdCore hx)
    extension_second_deriv_eq := fun x hx =>
      extension.second_deriv_eq_on x (hcdCore hx)
    derivative_band := hband'
    slope := slope
    slope_nonsingular := hslope
    slope_formula := hformula
  }⟩

/-- The mass-preserving paper selection used before the final horizontal
normalization.  All fields are indexed by one actual Node-5 configuration. -/
structure PureWZ2HorizontalSourceData
    {sigma inputLoss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta) where
  c : ℝ
  d : ℝ
  m : ℝ
  left_mem : -1 ≤ c
  ordered : c < d
  right_mem : d ≤ 1
  source_length : ℝ
  length_eq : d - c = source_length / 100
  slopeScale_pos : 0 < m
  slopeScale_lower : source_length ≤ m
  slopeScale_le_one : m ≤ 1
  globalSlope : SlopeFunction
  globalSlope_eq_on : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    globalSlope z = cfg.globalGrains.slope z
  globalSlope_normalized : globalSlope.IsNormalized
  derivative_band : ∀ z ∈ Set.Icc c d,
    m ≤ |deriv globalSlope z| ∧
      |deriv globalSlope z| ≤ 2 * m
  sourceShading : WZ1PaperTubeShading cfg.family
  source_in_interval : ∀ index, sourceShading.carrier index ⊆
    horizontalSlab c d
  source_mass_lower :
    Kakeya.realRpowENN delta (inputLoss + 3) *
        ENNReal.ofReal (d - c) ≤
      sourceShading.mass
  source_mass_card :
    ENNReal.ofReal (Real.pi / 4) *
        Kakeya.realRpowENN delta (inputLoss + 2) *
        cfg.family.enncard * ENNReal.ofReal (d - c) ≤
      sourceShading.mass
  sourceGlobalGrains : PureWZ2C2GlobalGrainData sourceShading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  /-- The restricted grain record keeps the ambient representative from the
  actual Node-5 configuration. -/
  source_global_slope_eq : sourceGlobalGrains.slope =
    cfg.globalGrains.slope
  sourceLocalGrains : PureWZ2LocalGrainData sourceShading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  /-- Internal smooth witness for the horizontal shear.  The affine map reads
  only its value at the selected midpoint.  This need not equal the source
  slope there: allowing a different constant shear is exactly what permits the
  paper-facing rescaled slope to have a nonzero intercept. -/
  geometrySlope : SlopeFunction
  geometrySlope_normalized : geometrySlope.IsNormalized
  f : PureWZ2C2SlopeFunction
  f_nonsingular : PureWZ2C2SlopeIsNonsingular f
  f_formula : ∀ t : PureWZ2UnitInterval,
    f t =
      anisotropicRescaledSlopeWithShear globalSlope c d m
        (geometrySlope (c + (d - c) / 2)) t.1

/-- Select the mass-popular one-fiftieth interval and construct the internal
nonsingular slope without replacing the actual Node-5 family. -/
theorem pureWZ2_horizontal_source_data
    {sigma inputLoss delta eta a b : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta)
    (globalSlope : SlopeFunction)
    (hglobalSlopeEq : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      globalSlope z = cfg.globalGrains.slope z)
    (hglobalSlopeNormalized : globalSlope.IsNormalized)
    (refined : LargeSlopeCroppedRefinementData cfg eta
      (Kakeya.realRpowENN delta (-inputLoss)) a b)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hderivative : ∀ z ∈ Set.Icc a b,
      b - a ≤ |deriv globalSlope z|) :
    ∃ data : PureWZ2HorizontalSourceData cfg,
      data.source_length = b - a := by
  have habAmbient : Set.Icc a b ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨refined.left_mem.trans hz.1,
      hz.2.trans refined.right_mem⟩
  have hwidth : 0 < b - a := sub_pos.mpr refined.ordered
  have hsourceDiff : ∀ z ∈ Set.Icc a b,
      DifferentiableAt ℝ globalSlope z := fun _ _ =>
    globalSlope.contDiff.differentiable (by norm_num) |>.differentiableAt
  have hglobalSlopeDerivC1 : ContDiff ℝ 1 (deriv globalSlope) :=
    globalSlope.contDiff.deriv'
  have hderivContinuous : ContinuousOn
      (deriv globalSlope) (Set.Icc a b) :=
    hglobalSlopeDerivC1.continuous.continuousOn
  have hderivDifferentiable : DifferentiableOn ℝ
      (deriv globalSlope) (interior (Set.Icc a b)) :=
    (hglobalSlopeDerivC1.differentiable (by norm_num)).differentiableOn
  have hderivSecondBound : ∀ z ∈ interior (Set.Icc a b),
      ‖deriv (deriv globalSlope) z‖ ≤ (1 : ℝ) := by
    intro z hz
    have hzab : z ∈ Set.Icc a b := interior_subset hz
    simpa [Real.norm_eq_abs] using
      (hglobalSlopeNormalized z (habAmbient hzab)).2.2
  have hderivLipschitz : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |deriv globalSlope x - deriv globalSlope y| ≤ |x - y| := by
    intro x hx y hy
    by_cases hxy : x ≤ y
    · have hupper := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
        hderivContinuous hderivDifferentiable
        (fun z hz => (abs_le.mp (by
          simpa [Real.norm_eq_abs] using hderivSecondBound z hz)).2)
        x hx y hy hxy
      have hlower := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
        hderivContinuous hderivDifferentiable
        (fun z hz => (abs_le.mp (by
          simpa [Real.norm_eq_abs] using hderivSecondBound z hz)).1)
        x hx y hy hxy
      rw [abs_of_nonpos (sub_nonpos.mpr hxy), abs_le]
      constructor <;> linarith
    · have hyx : y ≤ x := le_of_not_ge hxy
      have hupper := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
        hderivContinuous hderivDifferentiable
        (fun z hz => (abs_le.mp (by
          simpa [Real.norm_eq_abs] using hderivSecondBound z hz)).2)
        y hy x hx hyx
      have hlower := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
        hderivContinuous hderivDifferentiable
        (fun z hz => (abs_le.mp (by
          simpa [Real.norm_eq_abs] using hderivSecondBound z hz)).1)
        y hy x hx hyx
      rw [abs_of_nonneg (sub_nonneg.mpr hyx), abs_le]
      constructor <;> linarith
  have hmass :
      Kakeya.realRpowENN delta (inputLoss + 3) *
          ENNReal.ofReal (b - a) ≤
        shadedMassInSlab refined.shading a b := by
    have hfamilyOne : (1 : ENNReal) ≤ cfg.family.enncard := by
      change (1 : ENNReal) ≤ (cfg.family.card : ENNReal)
      exact_mod_cast cfg.extremal.nonempty
    have hdeltaPi : Kakeya.realRpowENN delta 1 ≤
        ENNReal.ofReal (Real.pi / 4) := by
      calc
        Kakeya.realRpowENN delta 1 = ENNReal.ofReal delta := by
          simp [Kakeya.realRpowENN]
        _ ≤ ENNReal.ofReal (Real.pi / 4) :=
          ENNReal.ofReal_mono (hdeltaSmall.trans (by
            linarith [Real.pi_gt_three]))
    calc
      Kakeya.realRpowENN delta (inputLoss + 3) *
            ENNReal.ofReal (b - a) =
          Kakeya.realRpowENN delta (inputLoss + 2) *
            Kakeya.realRpowENN delta 1 * ENNReal.ofReal (b - a) := by
              rw [← realRpowENN_add cfg.extremal.delta_pos]
              congr 2
              ring
      _ ≤ ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta (inputLoss + 2) *
            cfg.family.enncard * ENNReal.ofReal (b - a) := by
              calc
                _ ≤ Kakeya.realRpowENN delta (inputLoss + 2) *
                    (ENNReal.ofReal (Real.pi / 4) * cfg.family.enncard) *
                      ENNReal.ofReal (b - a) := by
                        gcongr
                        exact hdeltaPi.trans (by
                          simpa using mul_le_mul_left' hfamilyOne
                            (ENNReal.ofReal (Real.pi / 4)))
                _ = _ := by ring
      _ ≤ paperShadedMassInSlab refined.shading a b :=
        refined.slab_mass_card
  rcases mass_slope_selection_tight_hundredth_of_local
      globalSlope
      refined.ordered hderivContinuous.abs
      (fun x hx y hy =>
        (abs_abs_sub_abs_le _ _).trans (hderivLipschitz x hx y hy))
      hderivative
      (fun z hz =>
        (hglobalSlopeNormalized z (habAmbient hz)).2.1)
      refined.shading hmass with
    ⟨c, d, hc, hcd, hd, hlength,
      ⟨m, hm, hmLower, hmOne, hband, htight⟩, hmassFraction, hmassFinal⟩
  let sourceShading := pureWZ2PaperRestrictToSet refined.shading
    (horizontalSlab c d) (measurableSet_horizontalSlab c d)
  have hsourceSub : ∀ index, sourceShading.carrier index ⊆
      cfg.shading.carrier index := by
    intro index
    exact Set.inter_subset_left.trans (refined.subshading index)
  have hcdAmbient : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨refined.left_mem.trans (hc.trans hz.1),
      hz.2.trans (hd.trans refined.right_mem)⟩
  have hshort : d - c ≤ m / 100 := by
    rw [hlength]
    exact div_le_div_of_nonneg_right hmLower (by norm_num)
  let center : ℝ := c + (d - c) / 2
  let halfLength : ℝ := (d - c) / 2
  let normalizer : ℝ := m * (d - c) / 2
  let transformed : ℝ → ℝ := fun t =>
    globalSlope (center + halfLength * t) / normalizer -
      globalSlope center / normalizer
  have hhalfLength : 0 < halfLength := by
    dsimp only [halfLength]
    linarith
  have hnormalizer : 0 < normalizer := by
    dsimp only [normalizer]
    positivity
  have hmaps : Set.MapsTo (fun t : ℝ => center + halfLength * t)
      (Set.Icc (-1 : ℝ) 1) (Set.Icc c d) := by
    intro t ht
    dsimp only [center, halfLength]
    constructor
    · have ht0 : 0 ≤ t + 1 := by linarith [ht.1]
      have hproduct : 0 ≤ (d - c) / 2 * (t + 1) := by
        positivity
      linarith
    · have ht2 : t + 1 ≤ 2 := by linarith [ht.2]
      have hproduct : (d - c) / 2 * (t + 1) ≤ d - c := by
        calc
          (d - c) / 2 * (t + 1) ≤ (d - c) / 2 * 2 := by
            gcongr
          _ = d - c := by ring
      linarith
  have htransformedSmooth : ContDiffOn ℝ 2 transformed
      (Set.Icc (-1 : ℝ) 1) := by
    have haffine : ContDiff ℝ 2
        (fun t : ℝ => center + halfLength * t) := by fun_prop
    have hsourceComp : ContDiffOn ℝ 2
        (fun t : ℝ => globalSlope
          (center + halfLength * t)) (Set.Icc (-1 : ℝ) 1) := by
      have hcomp := globalSlope.contDiff.contDiffOn
        |>.mono hcdAmbient
        |>.comp haffine.contDiffOn hmaps
      simpa [Function.comp_def] using hcomp
    exact (hsourceComp.div_const normalizer).sub contDiffOn_const
  have htransformedFirst : ∀ t : ℝ, deriv transformed t =
      halfLength * deriv globalSlope
        (center + halfLength * t) / normalizer := by
    intro t
    dsimp only [transformed]
    rw [deriv_sub_const, deriv_div_const]
    have hmul := deriv_comp_mul_left halfLength
      (fun x => globalSlope (center + x)) t
    change deriv (fun u : ℝ =>
      (fun x => globalSlope (center + x))
        (halfLength * u)) t / normalizer = _
    rw [show deriv (fun u : ℝ =>
        (fun x => globalSlope (center + x))
          (halfLength * u)) t =
        halfLength * deriv
          (fun x => globalSlope (center + x))
            (halfLength * t) by simpa using hmul]
    rw [deriv_comp_const_add]
  have htransformedSecond : ∀ t : ℝ, deriv (deriv transformed) t =
      halfLength ^ 2 * deriv (deriv globalSlope)
        (center + halfLength * t) / normalizer := by
    intro t
    have hfirstFun : deriv transformed = fun u : ℝ =>
        halfLength * deriv globalSlope
          (center + halfLength * u) / normalizer :=
      funext htransformedFirst
    rw [hfirstFun]
    have hconst : (fun u : ℝ =>
        halfLength * deriv globalSlope
          (center + halfLength * u) / normalizer) =
      fun u : ℝ => (halfLength / normalizer) *
        deriv globalSlope (center + halfLength * u) := by
      funext u
      ring
    rw [hconst]
    have hscalar := deriv_fun_const_smul_field (x := t)
      (halfLength / normalizer)
      (fun u : ℝ =>
        deriv globalSlope (center + halfLength * u))
    rw [show deriv (fun u : ℝ => (halfLength / normalizer) *
        deriv globalSlope (center + halfLength * u)) t =
        (halfLength / normalizer) * deriv (fun u : ℝ =>
          deriv globalSlope
            (center + halfLength * u)) t by
      simpa only [smul_eq_mul] using hscalar]
    have hmul := deriv_comp_mul_left halfLength
      (fun x => deriv globalSlope (center + x)) t
    rw [show deriv (fun u : ℝ =>
        (fun x => deriv globalSlope (center + x))
          (halfLength * u)) t =
        halfLength * deriv
          (fun x => deriv globalSlope (center + x))
            (halfLength * t) by simpa using hmul]
    rw [deriv_comp_const_add]
    ring
  let f : PureWZ2C2SlopeFunction := fun t => transformed t.1
  have hfNonsingular : PureWZ2C2SlopeIsNonsingular f := by
    refine ⟨transformed, htransformedSmooth, ?_, ?_⟩
    · intro t
      rfl
    · intro t
      have hsourceMem := hmaps t.2
      have hbandAt := hband _ hsourceMem
      have hsecondAt :=
        (hglobalSlopeNormalized _ (hcdAmbient hsourceMem)).2.2
      have hfirstAbs : |deriv transformed t.1| =
          |deriv globalSlope
            (center + halfLength * t.1)| / m := by
        rw [htransformedFirst t.1, abs_div, abs_mul,
          abs_of_pos hhalfLength, abs_of_pos hnormalizer]
        dsimp only [halfLength, normalizer]
        field_simp [hm.ne', (sub_pos.mpr hcd).ne']
      have hsecondAbs : |deriv (deriv transformed) t.1| =
          (d - c) / (2 * m) *
            |deriv (deriv globalSlope)
              (center + halfLength * t.1)| := by
        rw [htransformedSecond t.1, abs_div, abs_mul, abs_pow,
          abs_of_pos hhalfLength, abs_of_pos hnormalizer]
        dsimp only [halfLength, normalizer]
        field_simp [hm.ne', (sub_pos.mpr hcd).ne']
      rw [hfirstAbs, hsecondAbs]
      constructor
      · exact (one_le_div₀ hm).2 hbandAt.1
      constructor
      · exact (div_le_iff₀ hm).2 (by linarith [hbandAt.2])
      · have hratioNonneg : 0 ≤ (d - c) / (2 * m) := by positivity
        have hratio : (d - c) / (2 * m) ≤ 1 / 100 := by
          apply (div_le_iff₀ (by positivity : 0 < 2 * m)).2
          nlinarith [hshort]
        calc
          (d - c) / (2 * m) *
                |deriv (deriv globalSlope)
                  (center + halfLength * t.1)|
              ≤ (d - c) / (2 * m) * 1 := by gcongr
          _ ≤ 1 / 100 := by simpa using hratio
  let geometrySlope : SlopeFunction :=
    { toFun := fun _ => globalSlope center
      contDiff := contDiff_const }
  exact ⟨{
    c := c
    d := d
    m := m
    left_mem := refined.left_mem.trans hc
    ordered := hcd
    right_mem := hd.trans refined.right_mem
    source_length := b - a
    length_eq := hlength
    slopeScale_pos := hm
    slopeScale_lower := hmLower
    slopeScale_le_one := hmOne
    globalSlope := globalSlope
    globalSlope_eq_on := hglobalSlopeEq
    globalSlope_normalized := hglobalSlopeNormalized
    derivative_band := hband
    sourceShading := sourceShading
    source_in_interval := fun _ => Set.inter_subset_right
    source_mass_lower := by
      change Kakeya.realRpowENN delta (inputLoss + 3) *
          ENNReal.ofReal (d - c) ≤ shadedMassInSlab refined.shading c d
      rw [hlength, ENNReal.ofReal_div_of_pos
        (by norm_num : (0 : ℝ) < 100), ENNReal.ofReal_ofNat]
      simpa only [div_eq_mul_inv, mul_assoc] using hmassFinal
    source_mass_card := by
      change ENNReal.ofReal (Real.pi / 4) *
          Kakeya.realRpowENN delta (inputLoss + 2) *
          cfg.family.enncard * ENNReal.ofReal (d - c) ≤
        shadedMassInSlab refined.shading c d
      have hcard :
          (ENNReal.ofReal (Real.pi / 4) *
              Kakeya.realRpowENN delta (inputLoss + 2) *
              cfg.family.enncard * ENNReal.ofReal (b - a)) / 100 ≤
            shadedMassInSlab refined.shading c d := by
        calc
          _ ≤ paperShadedMassInSlab refined.shading a b / 100 := by
            exact ENNReal.div_le_div refined.slab_mass_card (by norm_num)
          _ ≤ shadedMassInSlab refined.shading c d := hmassFraction
      rw [hlength, ENNReal.ofReal_div_of_pos
        (by norm_num : (0 : ℝ) < 100), ENNReal.ofReal_ofNat]
      simpa only [div_eq_mul_inv, mul_assoc] using hcard
    sourceGlobalGrains :=
      cfg.globalGrains.restrict_same_constant hsourceSub
    source_global_slope_eq := rfl
    sourceLocalGrains := cfg.localGrains.restrict hsourceSub
    geometrySlope := geometrySlope
    geometrySlope_normalized := by
      intro z _hz
      have hcenterMem : center ∈ Set.Icc c d := by
        dsimp only [center]
        constructor <;> linarith [hcd]
      have hvalue := (hglobalSlopeNormalized center
        (hcdAmbient hcenterMem)).1
      exact ⟨by simpa [geometrySlope] using hvalue, by
        simp [geometrySlope], by simp [geometrySlope]⟩
    f := f
    f_nonsingular := hfNonsingular
    f_formula := by
      intro t
      change transformed t.1 = _
      simp only [transformed, center, halfLength, normalizer,
        anisotropicRescaledSlopeWithShear, geometrySlope]
      ring
  }, rfl⟩

end Kakeya.Assouad

end
