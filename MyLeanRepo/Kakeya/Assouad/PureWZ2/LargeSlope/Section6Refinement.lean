import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ConfigurationRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CroppedRefinementData
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6ScaleData

/-!
# Same-source Section 6 refinement at a selected scale

This adapter turns a caller-selected Proposition-5 output at
`sqrt(delta) ≤ W` into the stable technical-lemma record.  The shading, slab
mass, cover, and restricted global/local grain data all come from the same
`PureWZ2Section6ScaleData`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- The paper technical scale `W = sqrt(delta)` as a requested scale. -/
def pureWZ2SqrtRequestedScale
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    WZ2PaperRequestedScale delta :=
  ⟨Real.sqrt delta, by
    constructor
    · have hsq : delta = (Real.sqrt delta) ^ 2 := by
        rw [Real.sq_sqrt hdelta.le]
      have hsqrtNonneg := Real.sqrt_nonneg delta
      have hsqrtOne := Real.sqrt_le_one.mpr hdeltaOne
      nlinarith
    · exact Real.sqrt_le_one.mpr hdeltaOne
  ⟩

@[simp] theorem pureWZ2SqrtRequestedScale_value
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    (pureWZ2SqrtRequestedScale hdelta hdeltaOne).1 = Real.sqrt delta := rfl

/-- `sqrt(delta)` belongs to the Section-6 power window for `loss ≤ 1/2`. -/
theorem pureWZ2_sqrt_scale_window
    {delta loss : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hlossNonneg : 0 ≤ loss) (hlossHalf : loss ≤ 1 / 2) :
    Real.rpow delta (1 - loss) ≤ Real.sqrt delta ∧
      Real.sqrt delta ≤ Real.rpow delta loss := by
  rw [show Real.sqrt delta = Real.rpow delta (1 / 2 : ℝ) by
    simp [Real.sqrt_eq_rpow]]
  constructor
  · apply Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne
    linarith
  · apply Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne
    linarith

/--
Convert one same-source Section-6 scale record into the technical refinement
record used by the derivative contradiction.
-/
def pureWZ2_section6Refinement
    {sigma loss delta eta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData
      cfg.shading sigma loss scale)
    (hlossNonneg : 0 ≤ loss)
    (hscaleLower : Real.sqrt delta ≤ scale.1)
    (hlossEta : 100 * loss ≤ eta) :
    LargeSlopeCroppedRefinementData cfg eta
      (Kakeya.realRpowENN delta (-loss))
      scaleData.slabLeft scaleData.slabRight := by
  have hCOne : 1 ≤ Kakeya.realRpowENN delta (-loss) := by
    rw [Kakeya.realRpowENN, ENNReal.one_le_ofReal]
    have hpow : Real.rpow delta 0 ≤ Real.rpow delta (-loss) :=
      Real.rpow_le_rpow_of_exponent_ge
        cfg.extremal.delta_pos cfg.extremal.delta_le_one (by linarith)
    simpa using hpow
  have hCTop : Kakeya.realRpowENN delta (-loss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  refine {
    left_mem := scaleData.slabLeft_mem
    ordered := scaleData.slab_ordered
    right_mem := scaleData.slabRight_mem
    scale_lower := ?_
    shading := scaleData.slabShading
    globalGrains :=
      cfg.globalGrains.restrict_same_constant scaleData.slab_subshading
    localGrains := cfg.localGrains.restrict scaleData.slab_subshading
    subshading := scaleData.slab_subshading
    slope_eq := rfl
    vertical_chart := ?_
    ad_constant_one := hCOne
    ad_constant_ne_top := hCTop
    ad_constant_bound := ?_
    slab_mass_card := ?_
  }
  · rw [scaleData.slab_width]
    show Kakeya.realRpowENN delta (1 / 2 : ℝ) ≤
      ENNReal.ofReal scale.1
    rw [show Kakeya.realRpowENN delta (1 / 2 : ℝ) =
        ENNReal.ofReal (Real.sqrt delta) by
      simp [Kakeya.realRpowENN, Real.sqrt_eq_rpow]]
    exact ENNReal.ofReal_le_ofReal hscaleLower
  · intro index
    have hline := (cfg.line_class index).1
    have hpositive : 0 < wz1PaperDirection
        (cfg.family.tube index) (2 : Fin 3) := by linarith
    have habs : |(cfg.family.tube index).direction (2 : Fin 3)| =
        wz1PaperDirection (cfg.family.tube index) (2 : Fin 3) := by
      simp [wz1PaperDirection]
      split_ifs with h
      · simp [abs_of_nonneg h]
      · have hnonpos : (cfg.family.tube index).direction (2 : Fin 3) ≤ 0 :=
          le_of_not_ge h
        simp [abs_of_nonpos hnonpos]
    rw [habs]
    exact hline
  · apply realRpowENN_antitone
      cfg.extremal.delta_pos cfg.extremal.delta_le_one
    linarith
  · rw [scaleData.slab_width]
    have hmass : paperShadedMassInSlab scaleData.slabShading
        scaleData.slabLeft scaleData.slabRight =
        scaleData.slabShading.mass := by
      apply Finset.sum_congr rfl
      intro index _
      rw [Set.inter_eq_left.mpr (scaleData.slab_in_slab index)]
    rw [hmass]
    exact scaleData.slab_mass

end Kakeya.Assouad

end
