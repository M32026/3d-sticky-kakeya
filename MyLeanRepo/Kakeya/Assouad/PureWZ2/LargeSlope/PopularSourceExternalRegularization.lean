import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.SubbandPopularBox
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PureExternalWeightRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FiniteScheduleParameters
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.BoundedSourceCardLog
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperAxisCoreVolume

/-!
# Public-pure regularization by the literal popular-box weights

The source family remains the ambient Node-5 family carrying public pure
nearby-scale CWA.  The external weight of a tube is its actual shaded volume
inside the selected derivative subband and popular spatial box.  Thus the
selected family produced below is simultaneously:

* a genuine subfamily of the public-pure source family;
* regularized for the actual public strict-fiber parent maps; and
* weighted by the same literal mass later transported by the affine map.

The weight need not itself be a cubical shading.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Explicit analytic receipt for the sharp source-cardinality window used by
the Section-6 anisotropic conflict budget.  This deliberately wraps the
literal Lemma-31 source family instead of extending the paper-facing Node-5
configuration or any re-entry capability record. -/
structure PureWZ2Section6SourceCardinalityReceipt
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta)
    (cardinalityLoss : ℝ) where
  upper : HasExtremalCardinalityUpper
    band.lemma31.data.cfg.family cardinalityLoss

/-- The first Section-6 source regularization inherits its logarithmic
cardinality envelope from the synchronized Node-5 re-entry provenance. -/
theorem PureWZ2Lemma32DerivativeBandAssembly.source_log_bound_of_raw
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta)
    (rawAbsorption :
      ENNReal.ofReal
          ((2 * pureWZ2BoundedSourceCardLogConstant) *
            (1 + Real.log delta⁻¹)) ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2) :
    (2 * (Nat.log 2
      (2 * band.lemma31.data.cfg.family.card) + 1) : ENNReal) ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 := by
  exact pureWZ2_bounded_source_ambient_dyadic_le_logSquare_of_raw
    band.lemma31.data.cfg.extremal.delta_pos
    band.lemma31.data.cfg.extremal.delta_le_one
    band.lemma31.data.cfg.extremal.nonempty
    band.lemma31.data.cfg.extremal.cwa_nearby_scales.2.2.1
    band.lemma31.data.cfg_bounded_base rawAbsorption

/-- Fixed popular-box and hundredth-band fraction. -/
def pureWZ2PopularSourceFraction : ENNReal :=
  ENNReal.ofReal (((1 / 8 : ℝ) ^ 3) / 27) * (1 / 100 : ENNReal)

/-- Per-source normalization supplied by the card-proportional Lemma-32 mass
floor after the hundredth-band and popular-box pigeonholes. -/
def pureWZ2PopularSourceNormalization
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta} :
    ENNReal :=
  pureWZ2PopularSourceFraction * ENNReal.ofReal (Real.pi / 4) *
    Kakeya.realRpowENN delta (band.massLoss + 2) *
      ENNReal.ofReal band.lemma31.data.rho.1 / 50

/-- Uniform upper bound for one literal popular-box weight.  The source
shading is restricted to a hundredth of the Lemma-32 derivative band, so the
sharp tube--slab estimate contributes the essential factor `rho`. -/
def pureWZ2PopularSourceWeightUpper
    {sigma epsilon delta : ℝ}
    (band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta) :
    ENNReal :=
  ENNReal.ofReal (band.lemma31.data.rho.1 * delta ^ 2)

/-- The actual ambient-indexed popular-box weight. -/
def pureWZ2PopularSourceWeight
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (popular : PureWZ2SubbandPopularBoxData subband)
    (index : Fin band.lemma31.data.cfg.family.card) : ENNReal :=
  volume (popular.popular.restricted.carrier index)

/-- Specialized public-pure regularization data for the literal popular box. -/
abbrev PureWZ2PopularSourceRegularizationData
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (popular : PureWZ2SubbandPopularBoxData subband)
    (scheduleConstant : ENNReal) (levelCount : ℕ) :=
  PureWZ2ExternalWeightRegularizationData
    band.sourceConstant scheduleConstant
      (pureWZ2PopularSourceNormalization (band := band))
      (pureWZ2PopularSourceWeightUpper band) levelCount
      (pureWZ2PopularSourceWeight popular)

namespace PureWZ2Section6SourceCardinalityReceipt

/-- Every source subfamily selected by the first external-weight
regularization inherits the sharp cardinality upper bound verbatim. -/
theorem selected_upper
    {sigma epsilon delta cardinalityLoss : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    (receipt : PureWZ2Section6SourceCardinalityReceipt band cardinalityLoss)
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    (regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount) :
    regularized.selected.family.enncard ≤
      Kakeya.realRpowENN delta (-2 - cardinalityLoss) := by
  apply le_trans ?_ receipt.upper
  change (regularized.selected.family.card : ENNReal) ≤
    (band.lemma31.data.cfg.family.card : ENNReal)
  have hcard : regularized.selected.family.card ≤
      band.lemma31.data.cfg.family.card := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective regularized.selected.embedding
        regularized.selected.embedding.injective
  exact_mod_cast hcard

end PureWZ2Section6SourceCardinalityReceipt

theorem pureWZ2_popularSourceNormalization_pos
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta} :
    0 < (pureWZ2PopularSourceNormalization (band := band)) := by
  have hdelta : 0 < delta := band.lemma31.data.cfg.extremal.delta_pos
  have hrho : 0 < band.lemma31.data.rho.1 :=
    hdelta.trans_le band.lemma31.data.rho.2.1
  have hfraction : 0 < pureWZ2PopularSourceFraction := by
    unfold pureWZ2PopularSourceFraction
    exact ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (by norm_num)).ne' (by norm_num)
  have hpi : 0 < ENNReal.ofReal (Real.pi / 4) :=
    ENNReal.ofReal_pos.mpr (by positivity)
  have hpower : 0 < Kakeya.realRpowENN delta
      (band.massLoss + 2) :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)
  have hrhoENN : 0 < ENNReal.ofReal band.lemma31.data.rho.1 :=
    ENNReal.ofReal_pos.mpr hrho
  have hfirst : 0 < pureWZ2PopularSourceFraction *
      ENNReal.ofReal (Real.pi / 4) :=
    ENNReal.mul_pos hfraction.ne' hpi.ne'
  have hsecond : 0 <
      (pureWZ2PopularSourceFraction * ENNReal.ofReal (Real.pi / 4)) *
        Kakeya.realRpowENN delta
          (band.massLoss + 2) :=
    ENNReal.mul_pos hfirst.ne' hpower.ne'
  have hthird : 0 <
      ((pureWZ2PopularSourceFraction * ENNReal.ofReal (Real.pi / 4)) *
          Kakeya.realRpowENN delta
            (band.massLoss + 2)) *
        ENNReal.ofReal band.lemma31.data.rho.1 :=
    ENNReal.mul_pos hsecond.ne' hrhoENN.ne'
  unfold pureWZ2PopularSourceNormalization
  exact ENNReal.div_pos hthird.ne' (by norm_num)

theorem pureWZ2_popularSourceNormalization_ne_top
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta} :
    pureWZ2PopularSourceNormalization (band := band) ≠ ⊤ := by
  unfold pureWZ2PopularSourceNormalization pureWZ2PopularSourceFraction
  repeat apply ENNReal.mul_ne_top
  · exact ENNReal.ofReal_ne_top
  · norm_num
  · exact ENNReal.ofReal_ne_top
  · simp [Kakeya.realRpowENN]
  · exact ENNReal.ofReal_ne_top
  · norm_num

/-- Fixed coefficient left after cancelling the derivative-band width and the
quadratic tube scale between the popular-source normalization and its sharp
per-tube weight bound. -/
def pureWZ2PopularSourceWeightRatioConstant : ENNReal :=
  50 *
    (pureWZ2PopularSourceFraction * ENNReal.ofReal (Real.pi / 4))⁻¹

/-- The sharp popular-source weight divided by its normalization loses only
the recorded mass exponent.  In particular, the common derivative-band
width cancels exactly and contributes no inverse power of `rho`. -/
theorem pureWZ2_popularSourceNormalization_inv_mul_weightUpper_le
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta} :
    (pureWZ2PopularSourceNormalization (band := band))⁻¹ *
        pureWZ2PopularSourceWeightUpper band ≤
      pureWZ2PopularSourceWeightRatioConstant *
        Kakeya.realRpowENN delta (-band.massLoss) := by
  have hdelta : 0 < delta := band.lemma31.data.cfg.extremal.delta_pos
  have hrho : 0 < band.lemma31.data.rho.1 :=
    hdelta.trans_le band.lemma31.data.rho.2.1
  have hfraction : 0 < pureWZ2PopularSourceFraction := by
    unfold pureWZ2PopularSourceFraction
    exact ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (by norm_num)).ne' (by norm_num)
  have hpi : 0 < ENNReal.ofReal (Real.pi / 4) :=
    ENNReal.ofReal_pos.mpr (by positivity)
  let coefficient : ENNReal :=
    pureWZ2PopularSourceFraction * ENNReal.ofReal (Real.pi / 4)
  have hcoefficientZero : coefficient ≠ 0 :=
    (ENNReal.mul_pos hfraction.ne' hpi.ne').ne'
  have hcoefficientTop : coefficient ≠ ⊤ := by
    dsimp only [coefficient]
    exact ENNReal.mul_ne_top (by
      unfold pureWZ2PopularSourceFraction
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num))
      ENNReal.ofReal_ne_top
  rw [ENNReal.inv_mul_le_iff
    (pureWZ2_popularSourceNormalization_pos (band := band)).ne'
    pureWZ2_popularSourceNormalization_ne_top]
  have hweight :
      pureWZ2PopularSourceWeightUpper band =
        ENNReal.ofReal band.lemma31.data.rho.1 *
          Kakeya.realRpowENN delta 2 := by
    unfold pureWZ2PopularSourceWeightUpper Kakeya.realRpowENN
    rw [ENNReal.ofReal_mul hrho.le]
    congr 1
    exact congrArg ENNReal.ofReal (Real.rpow_two delta).symm
  rw [hweight]
  unfold pureWZ2PopularSourceNormalization
    pureWZ2PopularSourceWeightRatioConstant
  change ENNReal.ofReal band.lemma31.data.rho.1 *
      Kakeya.realRpowENN delta 2 ≤
    (coefficient * Kakeya.realRpowENN delta (band.massLoss + 2) *
        ENNReal.ofReal band.lemma31.data.rho.1 / 50) *
      (50 * coefficient⁻¹ * Kakeya.realRpowENN delta (-band.massLoss))
  rw [div_eq_mul_inv]
  have hpower :
      Kakeya.realRpowENN delta (band.massLoss + 2) *
          Kakeya.realRpowENN delta (-band.massLoss) =
        Kakeya.realRpowENN delta 2 := by
    rw [← realRpowENN_add hdelta]
    congr 2
    ring
  apply le_of_eq
  symm
  calc
    (coefficient *
          Kakeya.realRpowENN delta (band.massLoss + 2) *
          ENNReal.ofReal band.lemma31.data.rho.1 * 50⁻¹) *
        (50 * coefficient⁻¹ *
          Kakeya.realRpowENN delta (-band.massLoss)) =
        (coefficient⁻¹ * coefficient) * (50⁻¹ * 50) *
          (ENNReal.ofReal band.lemma31.data.rho.1 *
            (Kakeya.realRpowENN delta (band.massLoss + 2) *
              Kakeya.realRpowENN delta (-band.massLoss))) := by ring
    _ = ENNReal.ofReal band.lemma31.data.rho.1 *
          Kakeya.realRpowENN delta 2 := by
      rw [ENNReal.inv_mul_cancel hcoefficientZero hcoefficientTop,
        ENNReal.inv_mul_cancel (by simp : (50 : ENNReal) ≠ 0)
          (by simp : (50 : ENNReal) ≠ ⊤), hpower]
      simp

/-- The literal popular-box mass supplies the required ambient weighted
cardinality floor without deleting or reindexing any source tube. -/
theorem PureWZ2SubbandPopularBoxData.normalization_mul_enncard_le_mass
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (popular : PureWZ2SubbandPopularBoxData subband) :
    pureWZ2PopularSourceNormalization (band := band) *
        band.lemma31.data.cfg.family.enncard ≤
      popular.popular.restricted.mass := by
  let boxFraction : ENNReal :=
    ENNReal.ofReal (((1 / 8 : ℝ) ^ 3) / 27)
  have hband :
      ENNReal.ofReal (Real.pi / 4) *
          Kakeya.realRpowENN delta
            (band.massLoss + 2) *
          band.lemma31.data.cfg.family.enncard *
          ENNReal.ofReal band.lemma31.data.rho.1 / 50 ≤
        band.literalBandShading.mass := by
    simpa using band.shaded_mass_card
  have hhundredth :
      band.literalBandShading.mass / 100 ≤ subband.shading.mass :=
    subband.mass_lower
  have hbox :
      boxFraction * subband.shading.mass ≤
        popular.popular.restricted.mass := by
    simpa [boxFraction] using popular.popular.mass_lower
  have hcombined :
      boxFraction * ((1 / 100 : ENNReal) *
          (ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta
              (band.massLoss + 2) *
            band.lemma31.data.cfg.family.enncard *
            ENNReal.ofReal band.lemma31.data.rho.1 / 50)) ≤
        popular.popular.restricted.mass := by
    calc
      boxFraction * ((1 / 100 : ENNReal) *
            (ENNReal.ofReal (Real.pi / 4) *
              Kakeya.realRpowENN delta
                (band.massLoss + 2) *
              band.lemma31.data.cfg.family.enncard *
              ENNReal.ofReal band.lemma31.data.rho.1 / 50)) ≤
          boxFraction * ((1 / 100 : ENNReal) *
            band.literalBandShading.mass) := by
              gcongr
      _ = boxFraction * (band.literalBandShading.mass / 100) := by
        simp [div_eq_mul_inv]
        ring
      _ ≤ boxFraction * subband.shading.mass := by gcongr
      _ ≤ popular.popular.restricted.mass := hbox
  unfold pureWZ2PopularSourceNormalization
  change
    (pureWZ2PopularSourceFraction * ENNReal.ofReal (Real.pi / 4) *
          Kakeya.realRpowENN delta
            (band.massLoss + 2) *
          ENNReal.ofReal band.lemma31.data.rho.1 / 50) *
        band.lemma31.data.cfg.family.enncard ≤
      popular.popular.restricted.mass
  have hfraction : pureWZ2PopularSourceFraction =
      boxFraction * (1 / 100 : ENNReal) := rfl
  rw [hfraction]
  convert hcombined using 1 <;> simp [div_eq_mul_inv] <;> ring

/-- Every ambient popular-box weight is bounded by the ordinary quadratic
paper-carrier volume. -/
theorem PureWZ2SubbandPopularBoxData.popularSourceWeight_le
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (popular : PureWZ2SubbandPopularBoxData subband)
    (index : Fin band.lemma31.data.cfg.family.card) :
    pureWZ2PopularSourceWeight popular index ≤
      pureWZ2PopularSourceWeightUpper band := by
  let tube := band.lemma31.data.cfg.family.tube index
  have hdelta : 0 < delta :=
    band.lemma31.data.cfg.extremal.delta_pos
  let bound : Set Point3 := {point |
    Metric.infDist point (tubeAxisLine tube) ≤ 6 * delta ∧
      point 2 ∈ Set.Icc subband.left subband.right}
  have hsubset : popular.popular.restricted.carrier index ⊆ bound := by
    intro point hpoint
    have hsubband : point ∈ subband.shading.carrier index :=
      popular.popular.restricted_subshading index hpoint
    have hpaper : point ∈ wz1PaperTubeCarrier tube :=
      subband.shading.subset_body index hsubband
    have hclosed : point ∈ Metric.cthickening (6 * delta)
        (tubeAxisLine tube) := hpaper.1
    have hinfEDist := Metric.mem_cthickening_iff.mp hclosed
    have hlineNonempty : (tubeAxisLine tube).Nonempty :=
      ⟨tube.base, 0, by simp [tubeAxisLine]⟩
    have hfinite : Metric.infEDist point (tubeAxisLine tube) ≠ ⊤ :=
      Metric.infEDist_ne_top hlineNonempty
    have hinf : Metric.infDist point (tubeAxisLine tube) ≤ 6 * delta := by
      have heq : ENNReal.ofReal
          (Metric.infDist point (tubeAxisLine tube)) =
            Metric.infEDist point (tubeAxisLine tube) :=
        ENNReal.ofReal_toReal hfinite
      rw [← heq] at hinfEDist
      exact (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg (by norm_num) hdelta.le)).mp hinfEDist
    rw [subband.carrier_eq] at hsubband
    exact ⟨hinf, hsubband.2⟩
  have hbound : volume bound ≤
      ENNReal.ofReal
        (4 * (6 * delta) ^ 2 * 2 *
          (subband.right - subband.left)) :=
    tube_thickening_zslab_volume_bound
      (mul_pos (by norm_num) hdelta) tube.direction_unit subband.ordered
      (band.lemma31.data.cfg.line_class index).vertical
  calc
    pureWZ2PopularSourceWeight popular index ≤
        volume bound :=
      measure_mono hsubset
    _ ≤ ENNReal.ofReal
        (4 * (6 * delta) ^ 2 * 2 *
          (subband.right - subband.left)) := hbound
    _ ≤ pureWZ2PopularSourceWeightUpper band := by
      apply ENNReal.ofReal_mono
      rw [subband.length_eq, band.length_eq]
      have hrho : 0 < band.lemma31.data.rho.1 :=
        hdelta.trans_le
          band.lemma31.data.rho.2.1
      have hdeltaSquare : 0 ≤ delta ^ 2 := sq_nonneg delta
      nlinarith

theorem pureWZ2_popular_source_external_regularization
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (popular : PureWZ2SubbandPopularBoxData subband)
    (scheduleConstant : ENNReal)
    (hscheduleFinite : WZ2PaperFiniteErrorConstant scheduleConstant)
    (levelCount : ℕ)
    (hambientTwo : 2 < band.sourceConstant)
    (hlevels : ENNReal.ofReal (1 / delta) ≤
      band.sourceConstant ^ levelCount)
    (hscheduleConstant :
      band.sourceConstant * band.sourceConstant ≤ scheduleConstant) :
    Nonempty (PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount) := by
  let family := band.lemma31.data.cfg.family
  let externalWeight : Fin family.card → ENNReal :=
    pureWZ2PopularSourceWeight popular
  have hmass :
      pureWZ2PopularSourceNormalization (band := band) * family.enncard ≤
        ∑ index : Fin family.card, externalWeight index := by
    change pureWZ2PopularSourceNormalization (band := band) *
        band.lemma31.data.cfg.family.enncard ≤
      popular.popular.restricted.mass
    exact popular.normalization_mul_enncard_le_mass
  simpa [PureWZ2PopularSourceRegularizationData, family, externalWeight] using
    (pureWZ2_external_weight_regularization
      band.lemma31.data.cfg.extremal.cwa_nearby_scales
      band.lemma31.data.cfg.extremal.nonempty
      band.lemma31.data.cfg.extremal.delta_le_one
      hscheduleFinite
      (pureWZ2_popularSourceNormalization_pos (band := band)).ne'
      pureWZ2_popularSourceNormalization_ne_top
      (by
        unfold pureWZ2PopularSourceWeightUpper
        exact ENNReal.ofReal_ne_top)
      externalWeight hmass
      (fun index => popular.popularSourceWeight_le index)
      levelCount hambientTwo hlevels hscheduleConstant)

/-- Uniform fixed-depth envelope for the first Section-6 source
regularization.  The logarithmic cardinality term comes from synchronized
re-entry provenance, while the sharp ratio bound has already cancelled the
selected derivative-band width. -/
theorem PureWZ2ExternalWeightRegularizationData.popular_outputConstant_le_logSquareEnvelope
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {scheduleConstant ambientBound scheduleBound : ENNReal}
    {levelCount : ℕ}
    (regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount)
    (hambient : band.sourceConstant ≤ ambientBound)
    (hschedule : scheduleConstant ≤ scheduleBound)
    (rawAbsorption :
      ENNReal.ofReal
          ((2 * pureWZ2BoundedSourceCardLogConstant) *
            (1 + Real.log delta⁻¹)) ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2)
    (hlogOne :
      1 ≤ (ENNReal.ofReal (Real.log (1 / delta))) ^ 2) :
    regularized.outputConstant ≤
      pureWZ2ExternalWeightRatioOutputEnvelope ambientBound scheduleBound
        (pureWZ2PopularSourceWeightRatioConstant *
          Kakeya.realRpowENN delta (-band.massLoss))
        ((ENNReal.ofReal (Real.log (1 / delta))) ^ 2) levelCount := by
  have hlog :
      (Nat.log 2 (2 * band.lemma31.data.cfg.family.card) + 1 : ENNReal) ≤
        (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 := by
    calc
      (Nat.log 2 (2 * band.lemma31.data.cfg.family.card) + 1 : ENNReal) ≤
          2 * (Nat.log 2
            (2 * band.lemma31.data.cfg.family.card) + 1 : ENNReal) := by
        simpa [two_mul] using
          (self_le_add_left
            (Nat.log 2
              (2 * band.lemma31.data.cfg.family.card) + 1 : ENNReal))
      _ ≤ (ENNReal.ofReal (Real.log (1 / delta))) ^ 2 :=
        band.source_log_bound_of_raw rawAbsorption
  apply regularized.outputConstant_le_externalWeightRatioOutputEnvelope
      hambient hschedule
      pureWZ2_popularSourceNormalization_inv_mul_weightUpper_le
      hlog hlogOne

/-- The first source regularization together with the finite schedule selected
for it.  Retaining the schedule certificate makes the strict lower bound on
the output constant available to the next regularization stage. -/
structure PureWZ2AutoPopularSourceRegularizationData
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (popular : PureWZ2SubbandPopularBoxData subband) where
  parameters : PureWZ2FiniteScheduleParameters band.sourceConstant
    (ENNReal.ofReal (1 / delta))
  levelCount_eq :
    parameters.levelCount =
      pureWZ2FixedScheduleLevelCount band.lemma31.data.targetLoss
  regularized : PureWZ2PopularSourceRegularizationData popular
    parameters.scheduleConstant parameters.levelCount

/-- First Section-6 source regularization with schedule depth fixed by a
positive loss before the runtime scale is chosen. -/
structure PureWZ2FixedPopularSourceRegularizationData
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (popular : PureWZ2SubbandPopularBoxData subband)
    (scheduleLoss : ℝ) where
  parameters : PureWZ2FiniteScheduleParameters band.sourceConstant
    (ENNReal.ofReal (1 / delta))
  levelCount_eq :
    parameters.levelCount = pureWZ2FixedScheduleLevelCount scheduleLoss
  regularized : PureWZ2PopularSourceRegularizationData popular
    parameters.scheduleConstant parameters.levelCount
  sourcePower_le_output :
    Kakeya.realRpowENN delta (-scheduleLoss) ≤ regularized.outputConstant

namespace PureWZ2AutoPopularSourceRegularizationData

/-- The automatically selected first regularization constant remains strictly
larger than two. -/
theorem outputConstant_gt_two
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    (data : PureWZ2AutoPopularSourceRegularizationData popular)
    (hambientTwo : 2 < band.sourceConstant) :
    2 < data.regularized.outputConstant :=
  data.regularized.outputConstant_gt_two
    hambientTwo data.parameters.square_le_schedule

end PureWZ2AutoPopularSourceRegularizationData

/-- Choose the finite schedule parameters for the first source
regularization.  The sole non-finitary premise is the strict lower bound on
the ambient nearby-CWA constant; all level-count and square-domination data
are selected internally. -/
theorem pureWZ2_popular_source_external_regularization_auto
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (popular : PureWZ2SubbandPopularBoxData subband)
    (hambientTwo : 2 < band.sourceConstant) :
    Nonempty (PureWZ2AutoPopularSourceRegularizationData popular) := by
  have htargetLoss : 0 < band.lemma31.data.targetLoss := by
    rw [band.lemma31.data.targetLoss_eq]
    exact div_pos band.lemma31.data.eta_pos (by norm_num)
  let parameters := fixedFiniteScheduleParameters
    band.lemma31.data.cfg.extremal.delta_pos
    band.lemma31.data.cfg.extremal.delta_le_one htargetLoss
    (show Kakeya.realRpowENN delta (-band.lemma31.data.targetLoss) ≤
        band.sourceConstant by rfl) hambientTwo
    band.lemma31.data.cfg.extremal.cwa_nearby_scales.2.1.2
  let regularized := Classical.choice <|
    pureWZ2_popular_source_external_regularization popular
      parameters.scheduleConstant parameters.schedule_finite
      parameters.levelCount hambientTwo parameters.target_le_power
      parameters.square_le_schedule
  exact ⟨{
    parameters := parameters
    levelCount_eq := rfl
    regularized := regularized
  }⟩

/-- Construct the first regularization with the prescribed fixed schedule
loss.  All three subsequent finite schedules may therefore reuse the same
pre-runtime depth. -/
theorem pureWZ2_popular_source_external_regularization_fixed
    {sigma epsilon delta scheduleLoss : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (popular : PureWZ2SubbandPopularBoxData subband)
    (hscheduleLoss : 0 < scheduleLoss)
    (hsourcePower : Kakeya.realRpowENN delta (-scheduleLoss) ≤
      band.sourceConstant)
    (hambientTwo : 2 < band.sourceConstant) :
    Nonempty (PureWZ2FixedPopularSourceRegularizationData
      popular scheduleLoss) := by
  let parameters := fixedFiniteScheduleParameters
    band.lemma31.data.cfg.extremal.delta_pos
    band.lemma31.data.cfg.extremal.delta_le_one hscheduleLoss hsourcePower
    hambientTwo band.lemma31.data.cfg.extremal.cwa_nearby_scales.2.1.2
  let regularized := Classical.choice <|
    pureWZ2_popular_source_external_regularization popular
      parameters.scheduleConstant parameters.schedule_finite
      parameters.levelCount hambientTwo parameters.target_le_power
      parameters.square_le_schedule
  exact ⟨{
    parameters := parameters
    levelCount_eq := rfl
    regularized := regularized
    sourcePower_le_output := hsourcePower.trans
      (regularized.ambientConstant_le_outputConstant
        ((by norm_num : (1 : ENNReal) ≤ 2).trans hambientTwo.le)
        parameters.square_le_schedule) }⟩

/-- The first Section-6 regularization level has a uniform lower bound in
terms of the saved popular-box normalization. -/
theorem PureWZ2ExternalWeightRegularizationData.popular_selectedWeightLevel_lower
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    (popular : PureWZ2SubbandPopularBoxData subband)
    {scheduleConstant : ENNReal} {levelCount : ℕ}
    (regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount) :
    pureWZ2PopularSourceNormalization (band := band) / 4 ≤
      regularized.selectedWeightLevel := by
  apply regularized.normalization_div_four_le_selectedWeightLevel
  change pureWZ2PopularSourceNormalization (band := band) *
      band.lemma31.data.cfg.family.enncard ≤
    popular.popular.restricted.mass
  exact popular.normalization_mul_enncard_le_mass

end Kakeya.Assouad

end
