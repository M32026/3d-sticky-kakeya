import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9WholeCellTraceSource
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9FirstRichMetricFiber
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WZ2EDSeparation

/-!
# Proposition 6.3 M9: family-free first-chart cardinality

This file bounds the public source family of the first whole-cell chart using
only ordinary essential distinctness and the radius-four basepoint bound of
the current normalization.  No selected-family CWA is used.
-/

noncomputable section
namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

attribute [local instance] Classical.propDecidable

private lemma point3_norm_sq_firstChart (v : Point3) :
    ‖v‖ ^ 2 = (v 0)^2 + (v 1)^2 + (v 2)^2 := by
  have h := EuclideanSpace.real_norm_sq_eq v
  rw [h]
  simp [Fin.sum_univ_succ] <;> ring

private lemma firstChart_coord_abs_lt_implies_norm_lt
    {v : Point3} {c delta : ℝ}
    (hc : 0 < c) (hdelta : 0 < delta)
    (h0 : |v 0| < c) (h1 : |v 1| < c) (h2 : |v 2| < c)
    (h3 : 3 * c^2 ≤ (delta / 16)^2) :
    ‖v‖ < delta / 16 := by
  have hs0 : (v 0)^2 < c^2 := by
    rw [show (v 0)^2 = |v 0|^2 by rw [sq_abs]]
    nlinarith [abs_nonneg (v 0)]
  have hs1 : (v 1)^2 < c^2 := by
    rw [show (v 1)^2 = |v 1|^2 by rw [sq_abs]]
    nlinarith [abs_nonneg (v 1)]
  have hs2 : (v 2)^2 < c^2 := by
    rw [show (v 2)^2 = |v 2|^2 by rw [sq_abs]]
    nlinarith [abs_nonneg (v 2)]
  have hnorm := point3_norm_sq_firstChart v
  have hnonneg : 0 ≤ ‖v‖ := norm_nonneg v
  have hright : 0 ≤ delta / 16 := by positivity
  nlinarith

/-- Radius-four version of the ordinary-ED packing estimate.  The direction
window is unchanged; only the base-coordinate count changes from `195` to
`259`. -/
theorem wz2_ed_packing_bound_boundedBase_four
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (distinct : WZ2PaperOrdinaryIsEssentiallyDistinct family)
    (boundedBase : HasBoundedBase family 4) :
    (family.card : ℝ) ≤
      (259 : ℝ)^3 * (67 : ℝ)^3 * delta^(-6 : ℝ) := by
  let c : ℝ := delta / 32
  have hc : 0 < c := by positivity
  let encode : Fin family.card → (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
    fun index =>
      (fun coordinate => ⌊(family.tube index).base coordinate / c⌋,
       fun coordinate => ⌊(family.tube index).direction coordinate / c⌋)
  have floor_close {x y : ℝ}
      (same : ⌊x / c⌋ = ⌊y / c⌋) : |x - y| < c := by
    set k : ℤ := ⌊x / c⌋ with hk
    have hx0 : (k : ℝ) ≤ x / c := Int.floor_le _
    have hx1 : x / c < (k : ℝ) + 1 := Int.lt_floor_add_one _
    have hk' : (k : ℝ) = (⌊y / c⌋ : ℝ) := by
      exact_mod_cast Eq.trans hk same
    have hy0 : (k : ℝ) ≤ y / c := by
      have := Int.floor_le (y / c)
      linarith
    have hy1 : y / c < (k : ℝ) + 1 := by
      have := Int.lt_floor_add_one (y / c)
      linarith
    have hquot : |x / c - y / c| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    have habs : |x - y| / c = |x / c - y / c| := by
      have heq : x - y = c * (x / c - y / c) := by
        field_simp [hc.ne'] <;> ring
      rw [heq, abs_mul, abs_of_pos hc]
      field_simp [hc.ne'] <;> ring
    calc
      |x - y| = (|x - y| / c) * c := by
        field_simp [hc.ne'] <;> ring
      _ < 1 * c := by rw [habs]; gcongr
      _ = c := by ring
  have encode_injective : Function.Injective encode := by
    intro left right same
    by_contra different
    have sameBase : (encode left).1 = (encode right).1 := by rw [same]
    have sameDirection : (encode left).2 = (encode right).2 := by rw [same]
    have hb0 := floor_close (congr_fun sameBase 0)
    have hb1 := floor_close (congr_fun sameBase 1)
    have hb2 := floor_close (congr_fun sameBase 2)
    have hd0 := floor_close (congr_fun sameDirection 0)
    have hd1 := floor_close (congr_fun sameDirection 1)
    have hd2 := floor_close (congr_fun sameDirection 2)
    have hcSquare : 3 * c^2 ≤ (delta / 16)^2 := by
      dsimp only [c]
      nlinarith
    have baseClose :
        ‖(family.tube left).base - (family.tube right).base‖ <
          delta / 16 :=
      firstChart_coord_abs_lt_implies_norm_lt hc hdelta
        hb0 hb1 hb2 hcSquare
    have directionClose :
        ‖(family.tube left).direction - (family.tube right).direction‖ <
          delta / 16 :=
      firstChart_coord_abs_lt_implies_norm_lt hc hdelta
        hd0 hd1 hd2 hcSquare
    exact (distinct left right different).1
      (close_tubes_contained_in_dilation hdelta
        baseClose.le directionClose.le)
  let baseRadius : ℤ := ⌈4 / c⌉
  let directionRadius : ℤ := ⌈1 / c⌉
  let baseRange : Finset ℤ := Finset.Icc (-baseRadius) baseRadius
  let directionRange : Finset ℤ :=
    Finset.Icc (-directionRadius) directionRadius
  let baseCodes : Finset (Fin 3 → ℤ) :=
    Fintype.piFinset (fun _ : Fin 3 => baseRange)
  let directionCodes : Finset (Fin 3 → ℤ) :=
    Fintype.piFinset (fun _ : Fin 3 => directionRange)
  let allCodes : Finset ((Fin 3 → ℤ) × (Fin 3 → ℤ)) :=
    baseCodes ×ˢ directionCodes
  have encode_mem : ∀ index, encode index ∈ allCodes := by
    intro index
    have baseCoordinate : ∀ coordinate : Fin 3,
        |(family.tube index).base coordinate| ≤ 4 := by
      intro coordinate
      rw [show |(family.tube index).base coordinate| =
          ‖(family.tube index).base coordinate‖ by
        simp [Real.norm_eq_abs]]
      exact (PiLp.norm_apply_le (family.tube index).base coordinate).trans
        (boundedBase index)
    have directionCoordinate : ∀ coordinate : Fin 3,
        |(family.tube index).direction coordinate| ≤ 1 := by
      intro coordinate
      rw [show |(family.tube index).direction coordinate| =
          ‖(family.tube index).direction coordinate‖ by
        simp [Real.norm_eq_abs]]
      simpa [(family.tube index).direction_unit] using
        PiLp.norm_apply_le (family.tube index).direction coordinate
    have baseMem : ∀ coordinate : Fin 3,
        ⌊(family.tube index).base coordinate / c⌋ ∈ baseRange := by
      intro coordinate
      have lower : -4 / c ≤ (family.tube index).base coordinate / c := by
        have := (abs_le.mp (baseCoordinate coordinate)).1
        gcongr
      have upper : (family.tube index).base coordinate / c ≤ 4 / c := by
        have := (abs_le.mp (baseCoordinate coordinate)).2
        gcongr
      have floorLower := Int.floor_le_floor lower
      have floorUpper := Int.floor_le_floor upper
      have negCeil : ⌊-4 / c⌋ = -baseRadius := by
        have : -4 / c = -(4 / c) := by ring
        rw [this, Int.floor_neg]
      have floorCeil : ⌊4 / c⌋ ≤ baseRadius := by
        simp [baseRadius, Int.floor_le_ceil]
      simp only [baseRange, Finset.mem_Icc]
      constructor <;> linarith
    have directionMem : ∀ coordinate : Fin 3,
        ⌊(family.tube index).direction coordinate / c⌋ ∈
          directionRange := by
      intro coordinate
      have lower : -1 / c ≤
          (family.tube index).direction coordinate / c := by
        have := (abs_le.mp (directionCoordinate coordinate)).1
        gcongr
      have upper : (family.tube index).direction coordinate / c ≤ 1 / c := by
        have := (abs_le.mp (directionCoordinate coordinate)).2
        gcongr
      have floorLower := Int.floor_le_floor lower
      have floorUpper := Int.floor_le_floor upper
      have negCeil : ⌊-1 / c⌋ = -directionRadius := by
        have : -1 / c = -(1 / c) := by ring
        rw [this, Int.floor_neg]
      have floorCeil : ⌊1 / c⌋ ≤ directionRadius := by
        simp [directionRadius, Int.floor_le_ceil]
      simp only [directionRange, Finset.mem_Icc]
      constructor <;> linarith
    simp only [allCodes, Finset.mem_product]
    exact ⟨by rw [Fintype.mem_piFinset]; exact baseMem,
      by rw [Fintype.mem_piFinset]; exact directionMem⟩
  have cardCodes : family.card ≤ allCodes.card := by
    have imageCard : (Finset.univ.image encode).card = family.card := by
      rw [Finset.card_image_of_injective _ encode_injective]
      simp
    have imageSubset : Finset.univ.image encode ⊆ allCodes := by
      intro code hcode
      rcases Finset.mem_image.mp hcode with ⟨index, _, rfl⟩
      exact encode_mem index
    rw [← imageCard]
    exact Finset.card_le_card imageSubset
  have baseRadiusNonnegative : 0 ≤ baseRadius := by
    simp [baseRadius, Int.ceil_nonneg]
    positivity
  have directionRadiusNonnegative : 0 ≤ directionRadius := by
    simp [directionRadius, Int.ceil_nonneg]
    positivity
  have baseRangeCard : (baseRange.card : ℝ) ≤ 2 * (4 / c) + 3 := by
    have hcard : baseRange.card = (2 * baseRadius + 1).toNat := by
      simp [baseRange, Int.card_Icc] <;> omega
    rw [hcard]
    have hnonnegative : 0 ≤ 2 * baseRadius + 1 := by linarith
    have hcast : (((2 * baseRadius + 1).toNat : ℕ) : ℝ) =
        2 * (baseRadius : ℝ) + 1 := by
      have : ((2 * baseRadius + 1).toNat : ℤ) =
          2 * baseRadius + 1 := Int.toNat_of_nonneg hnonnegative
      exact_mod_cast this
    rw [hcast]
    have := Int.ceil_lt_add_one (4 / c)
    linarith
  have directionRangeCard :
      (directionRange.card : ℝ) ≤ 2 * (1 / c) + 3 := by
    have hcard : directionRange.card =
        (2 * directionRadius + 1).toNat := by
      simp [directionRange, Int.card_Icc] <;> omega
    rw [hcard]
    have hnonnegative : 0 ≤ 2 * directionRadius + 1 := by linarith
    have hcast : (((2 * directionRadius + 1).toNat : ℕ) : ℝ) =
        2 * (directionRadius : ℝ) + 1 := by
      have : ((2 * directionRadius + 1).toNat : ℤ) =
          2 * directionRadius + 1 := Int.toNat_of_nonneg hnonnegative
      exact_mod_cast this
    rw [hcast]
    have := Int.ceil_lt_add_one (1 / c)
    linarith
  have baseCodesCard : (baseCodes.card : ℝ) =
      (baseRange.card : ℝ)^3 := by
    have hcard : baseCodes.card = ∏ _ : Fin 3, baseRange.card := by
      rw [Fintype.card_piFinset]
    rw [hcard]
    simp [Fin.prod_univ_succ]
  have directionCodesCard : (directionCodes.card : ℝ) =
      (directionRange.card : ℝ)^3 := by
    have hcard : directionCodes.card =
        ∏ _ : Fin 3, directionRange.card := by
      rw [Fintype.card_piFinset]
    rw [hcard]
    simp [Fin.prod_univ_succ]
  have allCodesCard : (allCodes.card : ℝ) =
      (baseCodes.card : ℝ) * (directionCodes.card : ℝ) := by
    simp [allCodes, Finset.card_product]
  have baseConstant : 2 * (4 / c) + 3 ≤ 259 / delta := by
    dsimp only [c]
    have identity : 2 * (4 / (delta / 32)) + 3 =
        256 / delta + 3 := by
      field_simp [hdelta.ne'] <;> ring
    rw [identity]
    have three : 3 ≤ 3 / delta := by
      have : 3 * delta ≤ 3 := by nlinarith
      calc
        3 = 3 * delta / delta := by field_simp [hdelta.ne'] <;> ring
        _ ≤ 3 / delta := by gcongr
    calc
      256 / delta + 3 ≤ 256 / delta + 3 / delta := by gcongr
      _ = 259 / delta := by field_simp [hdelta.ne'] <;> ring
  have directionConstant : 2 * (1 / c) + 3 ≤ 67 / delta := by
    dsimp only [c]
    have identity : 2 * (1 / (delta / 32)) + 3 =
        64 / delta + 3 := by
      field_simp [hdelta.ne'] <;> ring
    rw [identity]
    have three : 3 ≤ 3 / delta := by
      have : 3 * delta ≤ 3 := by nlinarith
      calc
        3 = 3 * delta / delta := by field_simp [hdelta.ne'] <;> ring
        _ ≤ 3 / delta := by gcongr
    calc
      64 / delta + 3 ≤ 64 / delta + 3 / delta := by gcongr
      _ = 67 / delta := by field_simp [hdelta.ne'] <;> ring
  have mainBound : (family.card : ℝ) ≤
      (259 / delta)^3 * (67 / delta)^3 := by
    calc
      (family.card : ℝ) ≤ (allCodes.card : ℝ) := by
        exact_mod_cast cardCodes
      _ = (baseCodes.card : ℝ) * (directionCodes.card : ℝ) :=
        allCodesCard
      _ = (baseRange.card : ℝ)^3 *
          (directionRange.card : ℝ)^3 := by
        rw [baseCodesCard, directionCodesCard]
      _ ≤ (2 * (4 / c) + 3)^3 * (2 * (1 / c) + 3)^3 := by
        gcongr <;> linarith
      _ ≤ (259 / delta)^3 * (67 / delta)^3 := by
        gcongr <;> linarith
  have rpowIdentity : delta^(-6 : ℝ) = 1 / delta^6 := by
    rw [show (-6 : ℝ) = -(6 : ℝ) by norm_num,
      Real.rpow_neg hdelta.le]
    simp [Real.rpow_natCast]
  calc
    (family.card : ℝ) ≤ (259 / delta)^3 * (67 / delta)^3 :=
      mainBound
    _ = (259 : ℝ)^3 * (67 : ℝ)^3 * delta^(-6 : ℝ) := by
      rw [rpowIdentity]
      field_simp [hdelta.ne'] <;> ring

private theorem tubeSubfamily_card_le_ambient
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family) :
    selected.family.card ≤ family.card := by
  simpa using
    Fintype.card_le_of_injective selected.embedding selected.embedding.injective

namespace Proposition63M9SampledFirstRichBoundaryData

variable
    {sigma outputLoss : Real}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    {aligned : Proposition63M9AlignedSampledStickyData cutoff}
    {normalizationWeight weightUpper : ENNReal}
    {nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := aligned.sticky.data.coarse)
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.stickyLoss))
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.selectedLoss))
      (proposition63CanonicalNearbyLevelCount
        cutoff.sampledM8RootLosses.stickyLoss)}
    {regularized : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) aligned.sticky.data nearbySchedule}
    {coefficient : Real} {K : Nat}
    {sampled : RegularizedAlignedSampledPlaninessData
      (coefficient := coefficient)
      (regularizedCompleteFiberCompatibleCover regularized)
      aligned.rootDelta_pos K}
    {preliminary : Proposition63M9SampledPreliminaryData
      cutoff regularized sampled}
    (first : Proposition63M9SampledFirstRichBoundaryData preliminary)

/-- The exact root-scale packing bound for any family selected inside the
first metric fibre. -/
theorem firstChart_metricFiber_cardinality_root_bound
    {tau epsilon₁ epsilon₃ retainedFactor : ℝ}
    (chart : Proposition63FirstChartData
      (localLoss := cutoff.initial.localLoss)
      (commonSliceLoss := cutoff.initial.localLoss)
      (chartLoss := cutoff.initial.lemma43SourceLoss)
      (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
      (coefficient := (1 : ℝ)) first.sticky.data first.power.Delta
      (ENNReal.ofReal retainedFactor)) :
    (chart.metricFiber.fiberFamily.family.card : ℝ) ≤
      (259 : ℝ)^3 * (67 : ℝ)^3 *
        aligned.aligned.requested.1^(-6 : ℝ) := by
  have ambientBound := wz2_ed_packing_bound_boundedBase_four
    first.current.normalization.final_extremal.delta_pos
    first.current.normalization.final_extremal.delta_le_one
    first.current.normalization.final_extremal.cwa_nearby_scales.2.2.1
    first.current.normalization.ordinary_bounded_base
  have selectedCard : chart.metricFiber.fiberFamily.family.card ≤
      first.current.normalization.croppedFamily.card := by
    let selected := first.sticky.data.selected.comp
      chart.metricFiber.fiberFamily
    exact tubeSubfamily_card_le_ambient selected
  have selectedCardReal :
      (chart.metricFiber.fiberFamily.family.card : ℝ) ≤
        (first.current.normalization.croppedFamily.card : ℝ) := by
    exact_mod_cast selectedCard
  exact selectedCardReal.trans ambientBound

/-- Rewrite the first metric-fibre cardinality bound at the family-free chart
ratio `q = first.power.h`. -/
theorem firstChart_metricFiber_cardinality_ratio_bound
    {tau epsilon₁ epsilon₃ retainedFactor : ℝ}
    (chart : Proposition63FirstChartData
      (localLoss := cutoff.initial.localLoss)
      (commonSliceLoss := cutoff.initial.localLoss)
      (chartLoss := cutoff.initial.lemma43SourceLoss)
      (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
      (coefficient := (1 : ℝ)) first.sticky.data first.power.Delta
      (ENNReal.ofReal retainedFactor)) :
    (chart.metricFiber.fiberFamily.family.card : ℝ) ≤
      (259 : ℝ)^3 * (67 : ℝ)^3 *
        Real.rpow first.power.h ((1 + sigma / 2) * (-6 : ℝ)) := by
  have rootBound := first.firstChart_metricFiber_cardinality_root_bound chart
  have ratioIdentity : aligned.aligned.requested.1^(-6 : ℝ) =
      Real.rpow first.power.h ((1 + sigma / 2) * (-6 : ℝ)) := by
    have hDelta : 0 < first.power.Delta := by
      rw [← first.power.scale_identity]
      exact Real.rpow_pos_of_pos first.power.h_pos _
    have hroot : aligned.aligned.requested.1 =
        first.power.h * first.power.Delta := by
      rw [first.power.h_eq]
      field_simp [hDelta.ne']
    have hrootRpow : aligned.aligned.requested.1 =
        Real.rpow first.power.h (1 + sigma / 2) := by
      calc
        aligned.aligned.requested.1 =
            first.power.h * first.power.Delta := hroot
        _ = Real.rpow first.power.h 1 *
            Real.rpow first.power.h (sigma / 2) := by
          rw [first.power.scale_identity]
          congr 1
          exact (Real.rpow_one first.power.h).symm
        _ = Real.rpow first.power.h (1 + sigma / 2) := by
          exact (Real.rpow_add first.power.h_pos 1 (sigma / 2)).symm
    calc
      aligned.aligned.requested.1^(-6 : ℝ) =
          (Real.rpow first.power.h (1 + sigma / 2))^(-6 : ℝ) :=
        congrArg (fun value : ℝ => value ^ (-6 : ℝ)) hrootRpow
      _ = Real.rpow first.power.h ((1 + sigma / 2) * (-6 : ℝ)) :=
        (Real.rpow_mul first.power.h_pos.le _ _).symm
  simpa only [ratioIdentity] using rootBound

/-- A fixed ninth-power weakening, convenient for family-free logarithmic
absorption.  The upper bound on `sigma` is deliberately explicit because it
is chosen outside the first-rich runtime record. -/
theorem firstChart_metricFiber_cardinality_ninth_power_bound
    {tau epsilon₁ epsilon₃ retainedFactor : ℝ}
    (chart : Proposition63FirstChartData
      (localLoss := cutoff.initial.localLoss)
      (commonSliceLoss := cutoff.initial.localLoss)
      (chartLoss := cutoff.initial.lemma43SourceLoss)
      (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
      (coefficient := (1 : ℝ)) first.sticky.data first.power.Delta
      (ENNReal.ofReal retainedFactor))
    (hsigmaOne : sigma ≤ 1) :
    (chart.metricFiber.fiberFamily.family.card : ℝ) ≤
      (259 : ℝ)^3 * (67 : ℝ)^3 *
        Real.rpow first.power.h (-9 : ℝ) := by
  refine (first.firstChart_metricFiber_cardinality_ratio_bound chart).trans ?_
  gcongr
  apply Real.rpow_le_rpow_of_exponent_ge
      first.power.h_pos first.power.h_le_one
  linarith

/-- The public source family of any whole-cell output has the same cardinality
as its metric fibre, hence inherits the family-free `q`-scale bound. -/
theorem firstChart_public_source_cardinality_ratio_bound
    {tau epsilon₁ epsilon₃ retainedFactor : ℝ}
    (chart : Proposition63FirstChartData
      (localLoss := cutoff.initial.localLoss)
      (commonSliceLoss := cutoff.initial.localLoss)
      (chartLoss := cutoff.initial.lemma43SourceLoss)
      (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
      (coefficient := (1 : ℝ)) first.sticky.data first.power.Delta
      (ENNReal.ofReal retainedFactor))
    (output : WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := cutoff.initial.lemma43SourceLoss)
      (chart.wholeCellShading first.current.normalization)
      (first.sticky.data.coarse.tube chart.metricFiber.parent)
      first.sticky.data.coarse_extremal.delta_pos) :
    (output.rescalingCertificate.publicFamily.card : ℝ) ≤
      (259 : ℝ)^3 * (67 : ℝ)^3 *
        Real.rpow first.power.h ((1 + sigma / 2) * (-6 : ℝ)) := by
  have sourceCard : output.rescalingCertificate.publicFamily.card =
      chart.metricFiber.fiberFamily.family.card := by
    have sourceCardENN : output.rescalingCertificate.publicFamily.enncard =
        chart.metricFiber.fiberFamily.family.enncard := by
      simpa using output.source_cardinality_eq
    exact Nat.cast_inj.mp sourceCardENN
  rw [sourceCard]
  exact first.firstChart_metricFiber_cardinality_ratio_bound chart

/-- Fixed ninth-power form of the public first-chart source bound. -/
theorem firstChart_public_source_cardinality_ninth_power_bound
    {tau epsilon₁ epsilon₃ retainedFactor : ℝ}
    (chart : Proposition63FirstChartData
      (localLoss := cutoff.initial.localLoss)
      (commonSliceLoss := cutoff.initial.localLoss)
      (chartLoss := cutoff.initial.lemma43SourceLoss)
      (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
      (coefficient := (1 : ℝ)) first.sticky.data first.power.Delta
      (ENNReal.ofReal retainedFactor))
    (output : WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := cutoff.initial.lemma43SourceLoss)
      (chart.wholeCellShading first.current.normalization)
      (first.sticky.data.coarse.tube chart.metricFiber.parent)
      first.sticky.data.coarse_extremal.delta_pos)
    (hsigmaOne : sigma ≤ 1) :
    (output.rescalingCertificate.publicFamily.card : ℝ) ≤
      (259 : ℝ)^3 * (67 : ℝ)^3 *
        Real.rpow first.power.h (-9 : ℝ) := by
  refine (first.firstChart_public_source_cardinality_ratio_bound
    chart output).trans ?_
  gcongr
  apply Real.rpow_le_rpow_of_exponent_ge
      first.power.h_pos first.power.h_le_one
  linarith

end Proposition63M9SampledFirstRichBoundaryData

end Kakeya.Assouad.PureWZ2

end
