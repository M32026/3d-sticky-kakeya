import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectAnisotropicRetubing
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PureExternalWeightRegularization
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperAxisCoreVolume

/-!
# Nearby-CWA regularization of the direct Node-6 source

The external weight of an ambient Node-5 tube is its actual mass in the
selected height interval and popular spatial box.  Positive selected weights
factor through the nonempty-carrier family used by the exact triangular map.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

def pureWZ2DirectPopularSourceNormalization
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg) : ENNReal :=
  ENNReal.ofReal (((1 / 8 : ℝ) ^ 3) / 27) *
    ENNReal.ofReal (Real.pi / 4) *
      Kakeya.realRpowENN delta (inputLoss + 2) *
        ENNReal.ofReal (source.d - source.c)

def pureWZ2DirectPopularSourceWeightUpper (delta : ℝ) : ENNReal :=
  (55296 * Kakeya.deltaTubeVolume 1) * Kakeya.realRpowENN delta 2

def pureWZ2DirectPopularSourceWeight
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    {source : PureWZ2HorizontalSourceData cfg}
    (popular : PureWZ2DirectHorizontalPopularBoxData source)
    (index : Fin cfg.family.card) : ENNReal :=
  volume (popular.popular.restricted.carrier index)

abbrev PureWZ2DirectSourceRegularizationData
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    {source : PureWZ2HorizontalSourceData cfg}
    (popular : PureWZ2DirectHorizontalPopularBoxData source)
    (scheduleConstant : ENNReal) (levelCount : ℕ) :=
  PureWZ2ExternalWeightRegularizationData
    (Kakeya.realRpowENN delta (-inputLoss)) scheduleConstant
    (pureWZ2DirectPopularSourceNormalization source)
    (pureWZ2DirectPopularSourceWeightUpper delta) levelCount
    (pureWZ2DirectPopularSourceWeight popular)

theorem pureWZ2DirectPopularSourceNormalization_pos
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg) :
    0 < pureWZ2DirectPopularSourceNormalization source := by
  unfold pureWZ2DirectPopularSourceNormalization
  have hbox : 0 < ENNReal.ofReal (((1 / 8 : ℝ) ^ 3) / 27) := by
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  have hcrossSection : 0 < ENNReal.ofReal (Real.pi / 4) := by
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hdeltaPower :
      0 < Kakeya.realRpowENN delta (inputLoss + 2) := by
    simp [Kakeya.realRpowENN, ENNReal.ofReal_pos,
      Real.rpow_pos_of_pos cfg.extremal.delta_pos]
  have hwidth : 0 < source.d - source.c := sub_pos.mpr source.ordered
  have hwidthENN : 0 < ENNReal.ofReal (source.d - source.c) :=
    ENNReal.ofReal_pos.mpr hwidth
  exact
    (ENNReal.mul_pos
      (ENNReal.mul_pos
        (ENNReal.mul_pos hbox.ne' hcrossSection.ne').ne'
        hdeltaPower.ne').ne'
      hwidthENN.ne')

theorem pureWZ2DirectPopularSourceNormalization_ne_top
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg) :
    pureWZ2DirectPopularSourceNormalization source ≠ ⊤ := by
  unfold pureWZ2DirectPopularSourceNormalization
  repeat' apply ENNReal.mul_ne_top
  all_goals first | exact ENNReal.ofReal_ne_top | simp [Kakeya.realRpowENN]

theorem PureWZ2DirectHorizontalPopularBoxData.normalization_mul_card_le_mass
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    {source : PureWZ2HorizontalSourceData cfg}
    (popular : PureWZ2DirectHorizontalPopularBoxData source) :
    pureWZ2DirectPopularSourceNormalization source * cfg.family.enncard ≤
      popular.popular.restricted.mass := by
  rw [← popular.source_mass_eq]
  unfold pureWZ2DirectPopularSourceNormalization
  calc
    (ENNReal.ofReal (((1 / 8 : ℝ) ^ 3) / 27) *
          ENNReal.ofReal (Real.pi / 4) *
          Kakeya.realRpowENN delta (inputLoss + 2) *
          ENNReal.ofReal (source.d - source.c)) * cfg.family.enncard =
        ENNReal.ofReal (((1 / 8 : ℝ) ^ 3) / 27) *
          (ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta (inputLoss + 2) *
            cfg.family.enncard * ENNReal.ofReal (source.d - source.c)) := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ ≤ popular.sourceShading.mass := popular.source_mass_card

theorem PureWZ2DirectHorizontalPopularBoxData.sourceWeight_le
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    {source : PureWZ2HorizontalSourceData cfg}
    (popular : PureWZ2DirectHorizontalPopularBoxData source)
    (hdeltaSmall : delta ≤ 1 / 24)
    (index : Fin cfg.family.card) :
    pureWZ2DirectPopularSourceWeight popular index ≤
      pureWZ2DirectPopularSourceWeightUpper delta := by
  have hsubset : popular.popular.restricted.carrier index ⊆
      wz1PaperTubeCarrier (cfg.family.tube index) :=
    popular.popular.restricted.subset_body index
  calc
    pureWZ2DirectPopularSourceWeight popular index ≤
        volume (wz1PaperTubeCarrier (cfg.family.tube index)) :=
      measure_mono hsubset
    _ ≤ pureWZ2DirectPopularSourceWeightUpper delta := by
      exact (wz2PaperTubeCarrier_convex_and_volume_quadratic
        wz2_paper_tube_carrier_geometry cfg.extremal.delta_pos hdeltaSmall
        (cfg.family.tube index) (cfg.line_class index)).2

theorem pureWZ2_direct_source_regularization
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    {source : PureWZ2HorizontalSourceData cfg}
    (popular : PureWZ2DirectHorizontalPopularBoxData source)
    (scheduleConstant : ENNReal)
    (hscheduleFinite : WZ2PaperFiniteErrorConstant scheduleConstant)
    (levelCount : ℕ)
    (hambientTwo : 2 < Kakeya.realRpowENN delta (-inputLoss))
    (hlevels : ENNReal.ofReal (1 / delta) ≤
      Kakeya.realRpowENN delta (-inputLoss) ^ levelCount)
    (hscheduleConstant :
      Kakeya.realRpowENN delta (-inputLoss) ^ 2 ≤ scheduleConstant)
    (hdeltaSmall : delta ≤ 1 / 24) :
    Nonempty (PureWZ2DirectSourceRegularizationData
      popular scheduleConstant levelCount) := by
  exact pureWZ2_external_weight_regularization
    cfg.extremal.cwa_nearby_scales cfg.extremal.nonempty
    cfg.extremal.delta_le_one hscheduleFinite
    (pureWZ2DirectPopularSourceNormalization_pos source).ne'
    (pureWZ2DirectPopularSourceNormalization_ne_top source)
    (by
      unfold pureWZ2DirectPopularSourceWeightUpper
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top)
        (by simp [Kakeya.realRpowENN]))
    (pureWZ2DirectPopularSourceWeight popular)
    popular.normalization_mul_card_le_mass
    (popular.sourceWeight_le hdeltaSmall) levelCount hambientTwo hlevels
    (by simpa [pow_two] using hscheduleConstant)

end Kakeya.Assouad

end
