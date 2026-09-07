import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RichRobustCloseBand
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9PaperLemma43Robust
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BodyMassPositivity

/-!
# Proposition 6.3 M9: rich-terminal Lemma 4.3 preparation

This module prepares the actual global point-multiplicity band directly from
the first rich terminal output.  In particular, it does not assert cropped
extremality for `rich.data.refined`.  The high shading is definitionally the
terminal refined shading and its lower multiplicity threshold is the exact
terminal product `fineDegreeFloor * muFine`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- The minimal extra receipt needed when the ordinary Lemma 4.3 preparation
is built from a rich terminal rather than from a fresh cropped extremizer.
The embedded `prepared` record contains the actual global dyadic band; the
additional field retains the mass comparison with the pre-rich cropped
shading, whose tube family is different. -/
structure Proposition63M9RichLemma43Preparation
    {delta sigma outputLoss sourceLoss normalizationLoss densityLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho) where
  prepared : Proposition63PaperLemma43Preparation
    (sigma := sigma) (sourceLoss := outputLoss)
    (densityLoss := densityLoss) rich.data.refined
  high_eq : prepared.high = rich.data.refined
  m0_eq : prepared.m0 =
    rich.terminal.fineDegreeFloor * rich.terminal.muFine
  total_mass_receipt :
    wz2PaperPureRefinementFraction delta 61 * croppedShading.mass ≤
      prepared.high.mass
  actual_band_common : ∀ index, prepared.band.band.carrier index =
    rich.data.refined.carrier index ∩ prepared.band.band.union
  actual_band_nonempty : prepared.band.band.union.Nonempty
  m0_lt_twice_bandMultiplicity :
    prepared.m0 < 2 * 2 ^ prepared.band.level
  hm24 : 24 ≤ 2 ^ prepared.band.level

/-- Prepare Lemma 4.3 from the first rich terminal.  The only analytic input
is the scalar inequality consumed by
`fineMultiplicity_density_of_scalar`; no extremality assertion for the
selected refined shading is required. -/
theorem proposition63_m9_rich_lemma43_preparation
    {delta sigma outputLoss sourceLoss normalizationLoss densityLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)
    (hdensityScalar :
      Kakeya.realRpowENN delta densityLoss *
          ((rich.terminal.regularity : ENNReal) *
            Kakeya.realRpowENN delta (sigma - normalizationLoss)) ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta (normalizationLoss + 2))
    (hdeltaSmall : delta ≤ 1 / 24)
    (hdegree : (96 : ENNReal) * stickyCoarseCloseCount ≤
      (rich.terminal.fineDegreeFloor : ENNReal)) :
    Nonempty (Proposition63M9RichLemma43Preparation
      (densityLoss := densityLoss) rich) := by
  let m0 := rich.terminal.fineDegreeFloor * rich.terminal.muFine
  let high := rich.data.refined
  have hdensity : Kakeya.realRpowENN delta densityLoss *
      rich.data.selected.family.enncard ≤ (m0 : ℕ) := by
    simpa only [m0] using
      rich.fineMultiplicity_density_of_scalar
        (Kakeya.realRpowENN delta densityLoss)
        (hdeltaSmall.trans (by norm_num)) hdensityScalar
  have hhighCommon : ∀ index, high.carrier index =
      rich.data.refined.carrier index ∩ high.union := by
    intro index
    ext point
    constructor
    · intro hpoint
      exact ⟨hpoint, ⟨index, hpoint⟩⟩
    · exact fun hpoint => hpoint.1
  have hhighMass : (1 / 2 : ENNReal) * rich.data.refined.mass ≤
      high.mass := by
    dsimp only [high]
    simpa only [one_mul] using
      mul_le_mul_left (show (1 / 2 : ENNReal) ≤ 1 by norm_num)
        rich.data.refined.mass
  have hm0Pos : 0 < m0 := by
    exact Nat.mul_pos rich.terminal.fineDegreeFloor_pos
      rich.terminal.muFine_pos
  let prepared : Proposition63PaperLemma43Preparation
      (sigma := sigma) (sourceLoss := outputLoss)
      (densityLoss := densityLoss) rich.data.refined := {
    m0 := m0
    high := high
    band := Classical.choice
      (wz2_paper_global_multiplicity_band high rich.terminal.fine_cubical)
    high_subshading := fun _ => Set.Subset.rfl
    high_cubical := rich.terminal.fine_cubical
    high_multiplicity := fun point hpoint =>
      rich.terminal.fine_pointMultiplicity_floor_on_union hpoint
    density_lower := hdensity
    high_mass := hhighMass
    high_common := hhighCommon
    m0_pos := hm0Pos
  }
  have hcroppedMass : 0 < croppedShading.mass :=
    paper_shading_mass_positive reentry.cropped_extremal.delta_pos
      (hdeltaSmall.trans (by norm_num)) reentry.geometry.line_class
      reentry.cropped_extremal.nonempty reentry.cropped_extremal.dense
  have hfractionPos : 0 < wz2PaperPureRefinementFraction delta 61 := by
    unfold wz2PaperPureRefinementFraction
    exact ENNReal.pow_pos
      (ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top) _
  have hrefinedMass : 0 < rich.data.refined.mass :=
    (ENNReal.mul_pos hfractionPos.ne' hcroppedMass.ne').trans_le
      rich.total_mass_retention
  have hbandMass : 0 < prepared.band.band.mass :=
    (ENNReal.div_pos hrefinedMass.ne' (by simp)).trans_le
      prepared.band.band_mass_retention
  have hbandNonempty : prepared.band.band.union.Nonempty := by
    by_contra hempty
    have hcarriers : ∀ index, prepared.band.band.carrier index = ∅ := by
      intro index
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨point, hpoint⟩
      exact hempty ⟨point, index, hpoint⟩
    have hmassZero : prepared.band.band.mass = 0 := by
      simp [Kakeya.Streamlined.Shading.mass, hcarriers]
    rw [hmassZero] at hbandMass
    exact (lt_irrefl 0) hbandMass
  have hm0Band : prepared.m0 < 2 * 2 ^ prepared.band.level := by
    rcases hbandNonempty with ⟨point, hpoint⟩
    have hhighPoint : point ∈ prepared.high.union := by
      rcases hpoint with ⟨index, hindex⟩
      have hsub : PaperIsSubshading prepared.band.band prepared.high := by
        rw [prepared.band.band_eq]
        exact wz1PaperDyadicBandSubshading_isSubshading
          prepared.high prepared.band.level
      exact ⟨index, hsub index hindex⟩
    have hm0 := prepared.high_multiplicity point hhighPoint
    have hmultEq : prepared.band.band.pointMultiplicity point =
        prepared.high.pointMultiplicity point := by
      rw [prepared.band.band_eq] at hpoint ⊢
      exact dyadicBandSubshading_pointMultiplicity_eq hpoint
    have hupper : prepared.band.band.pointMultiplicity point <
        2 ^ (prepared.band.level + 1) := by
      have hupperENN := (prepared.band.band_multiplicity point hpoint).2
      rw [show (2 : ENNReal) ^ (prepared.band.level + 1) =
          ((2 ^ (prepared.band.level + 1) : ℕ) : ENNReal) by norm_num]
        at hupperENN
      exact (Nat.cast_lt :
        (((prepared.band.band.pointMultiplicity point : ℕ) : ENNReal) <
            ((2 ^ (prepared.band.level + 1) : ℕ) : ENNReal) ↔
          prepared.band.band.pointMultiplicity point <
            2 ^ (prepared.band.level + 1))).mp hupperENN
    rw [← hmultEq] at hm0
    exact hm0.trans_lt (by simpa [pow_succ, mul_comm] using hupper)
  have hm0Large : 48 ≤ prepared.m0 := by
    change 48 ≤ rich.terminal.fineDegreeFloor * rich.terminal.muFine
    have hfloor : 48 ≤ rich.terminal.fineDegreeFloor := by
      have hfloorENN : (48 : ENNReal) ≤
          rich.terminal.fineDegreeFloor :=
        (show (48 : ENNReal) ≤ 96 * stickyCoarseCloseCount by
          unfold stickyCoarseCloseCount
          norm_num).trans hdegree
      exact (Nat.cast_le :
        (((48 : ℕ) : ENNReal) ≤
            ((rich.terminal.fineDegreeFloor : ℕ) : ENNReal) ↔
          48 ≤ rich.terminal.fineDegreeFloor)).mp hfloorENN
    exact hfloor.trans
      (Nat.le_mul_of_pos_right rich.terminal.fineDegreeFloor
        rich.terminal.muFine_pos)
  have hm24 : 24 ≤ 2 ^ prepared.band.level := by omega
  exact ⟨{
    prepared := prepared
    high_eq := rfl
    m0_eq := rfl
    total_mass_receipt := by
      simpa only [prepared, high] using rich.total_mass_retention
    actual_band_common := by
      simpa only [prepared, high] using prepared.band_common_source
    actual_band_nonempty := hbandNonempty
    m0_lt_twice_bandMultiplicity := hm0Band
    hm24 := hm24
  }⟩

/-- Run the pointwise-only robust Lemma 4.3 core on the band prepared from a
rich terminal.  The rich terminal supplies the robust close-count certificate,
the dyadic lower-scale bound, positivity of `delta`, and nonemptiness of the
selected family.  The CV estimate and broad-set absorption remain explicit:
they are genuine analytic inputs and are not consequences of the rich
terminal package. -/
theorem proposition63_m9_rich_pointwise_weak_map_from_preparation
    {delta sigma outputLoss sourceLoss normalizationLoss densityLoss theta
      incidenceBudget : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)
    (richPrepared : Proposition63M9RichLemma43Preparation
      (densityLoss := densityLoss) rich)
    (hCV : ∀ (E : Set Point3), MeasurableSet E →
      E ⊆ rich.data.refined.union → ∀ (L : ENNReal),
        (∀ point ∈ E, L ≤
          (paperShadingTrilinearMultiplicity rich.data.refined point) ^
            (1 / 2 : ℝ)) →
        L * volume E ≤
          C * (ENNReal.ofReal (delta ^ 2) *
            rich.data.selected.family.enncard) ^ (3 / 2 : ℝ))
    (hrhoSmall : rho.1 ≤ 1 / 10000)
    (hdegree : (96 : ENNReal) * stickyCoarseCloseCount ≤
      (rich.terminal.fineDegreeFloor : ENNReal))
    (htheta : 0 < theta)
    (hincidence : theta / rho.1 ≤ incidenceBudget)
    (hbroadAbsorb :
      let m := 2 ^ richPrepared.prepared.band.level
      let Q : ℕ := m ^ 3 / 4
      (2 : ENNReal) * (2 * m : ℕ) * C *
          (ENNReal.ofReal (delta ^ 2) *
            rich.data.selected.family.enncard) ^ (3 / 2 : ℝ) ≤
        (((Q : ENNReal) * ENNReal.ofReal theta) ^ (1 / 2 : ℝ)) *
          richPrepared.prepared.band.band.mass) :
    ∃ data : Proposition63PointwiseWeakMapRefinementData
        rich.data.refined incidenceBudget,
      WZ1PaperIsCubicalShading data.shading ∧
      data.leftFactor = 1 / 16 ∧
      data.rightFactor =
        ((Nat.log 2 rich.data.selected.family.card + 1 : ℕ) : ENNReal) := by
  apply proposition63_pointwise_weak_map_from_robust_preparation
      richPrepared.prepared hCV
      (reentry.cropped_extremal.delta_pos.trans_le rho.2.1) htheta
      hincidence richPrepared.hm24
      (rich.prepared_band_close_lt_div_twentyFour
        richPrepared.prepared hrhoSmall hdegree richPrepared.hm24)
      hbroadAbsorb reentry.cropped_extremal.delta_pos
      rich.data.selected_nonempty

/-- Construction-aware version of the rich-terminal pointwise producer.
It retains the actual narrow selection and normalized-cross identity used by
Lemma 4.3, while projecting to the historical output on demand. -/
theorem proposition63_m9_rich_pointwise_weak_map_witness_from_preparation
    {delta sigma outputLoss sourceLoss normalizationLoss densityLoss theta
      incidenceBudget : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)
    (richPrepared : Proposition63M9RichLemma43Preparation
      (densityLoss := densityLoss) rich)
    (hCV : ∀ (E : Set Point3), MeasurableSet E →
      E ⊆ rich.data.refined.union → ∀ (L : ENNReal),
        (∀ point ∈ E, L ≤
          (paperShadingTrilinearMultiplicity rich.data.refined point) ^
            (1 / 2 : ℝ)) →
        L * volume E ≤
          C * (ENNReal.ofReal (delta ^ 2) *
            rich.data.selected.family.enncard) ^ (3 / 2 : ℝ))
    (hrhoSmall : rho.1 ≤ 1 / 10000)
    (hdegree : (96 : ENNReal) * stickyCoarseCloseCount ≤
      (rich.terminal.fineDegreeFloor : ENNReal))
    (htheta : 0 < theta)
    (hincidence : theta / rho.1 ≤ incidenceBudget)
    (hbroadAbsorb :
      let m := 2 ^ richPrepared.prepared.band.level
      let Q : ℕ := m ^ 3 / 4
      (2 : ENNReal) * (2 * m : ℕ) * C *
          (ENNReal.ofReal (delta ^ 2) *
            rich.data.selected.family.enncard) ^ (3 / 2 : ℝ) ≤
        (((Q : ENNReal) * ENNReal.ofReal theta) ^ (1 / 2 : ℝ)) *
          richPrepared.prepared.band.band.mass) :
    ∃ witness : Proposition63M9PointwiseWeakMapWitness
        (source := rich.data.refined)
        (band := richPrepared.prepared.band.band)
        (kappa := rho.1) (incidenceBudget := incidenceBudget)
        (theta := theta)
        (Q := (2 ^ richPrepared.prepared.band.level) ^ 3 / 4),
      WZ1PaperIsCubicalShading witness.data.shading ∧
      witness.data.leftFactor = 1 / 16 ∧
      witness.data.rightFactor =
        ((Nat.log 2 rich.data.selected.family.card + 1 : ℕ) : ENNReal) := by
  apply proposition63_pointwise_weak_map_from_robust_preparation_with_witness
      (incidenceBudget := incidenceBudget) richPrepared.prepared hCV
      (reentry.cropped_extremal.delta_pos.trans_le rho.2.1) htheta
      hincidence richPrepared.hm24
      (rich.prepared_band_close_lt_div_twentyFour
        richPrepared.prepared hrhoSmall hdegree richPrepared.hm24)
      hbroadAbsorb reentry.cropped_extremal.delta_pos
      rich.data.selected_nonempty

end Kakeya.Assouad.PureWZ2

end
