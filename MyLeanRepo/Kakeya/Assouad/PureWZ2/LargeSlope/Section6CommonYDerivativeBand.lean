import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6Lemma32DerivativeBand
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.RotatedWeightedCommonYRefinement

/-!
# Run the Section-6 derivative selection after the common-y refinement

This is the paper-order bridge between Refinement 2 and the derivative
subinterval `J₀`.  Its source is exactly the whole-label common-slice shading
`F2`; the additional loss records the factor
`(1 / 4) * delta^(4 * badYLoss)` from that refinement.
-/

noncomputable section
namespace Kakeya.Assouad

open Set

/-- The common-y whole-label refinement can be used as the source of the
derivative interval selection.  One extra power of `delta` absorbs the fixed
factor `1 / 4`; no geometric data or slope is changed. -/
theorem PureWZ2Lemma31DerivativeAssembly.toLemma32DerivativeBandAfterCommonY
    {sigma epsilon delta : ℝ}
    (data : PureWZ2Lemma31DerivativeAssembly sigma epsilon delta)
    (popular : PureWZ2WeightedPopularGlobalGrainData data.data.cfg data.data.rho
      data.data.scaleData)
    (frameSlope : ℝ)
    (common : PureWZ2RotatedWeightedCommonYData data.data.cfg data.data.rho
      data.data.scaleData popular frameSlope) :
    ∃ band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta,
      band.lemma31 = data ∧ band.sourceShading.union = common.F2.union ∧
      band.massLoss =
        data.data.targetLoss + 4 * common.badYLoss + 1 := by
  let massLoss := data.data.targetLoss + 4 * common.badYLoss + 1
  have hdeltaOne : delta ≤ 1 := data.delta_small.trans (by norm_num)
  have hdeltaQuarter :
      Kakeya.realRpowENN delta 1 ≤ (1 / 4 : ENNReal) := by
    calc
      Kakeya.realRpowENN delta 1 = ENNReal.ofReal delta := by
        simp [Kakeya.realRpowENN]
      _ ≤ ENNReal.ofReal (1 / 4 : ℝ) :=
        ENNReal.ofReal_mono (data.delta_small.trans (by norm_num))
      _ = (1 / 4 : ENNReal) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
        norm_num
  have hretained :
      (1 / 4 : ENNReal) *
          Kakeya.realRpowENN delta (4 * common.badYLoss) *
          (ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta (data.data.targetLoss + 2) *
            data.data.cfg.family.enncard *
            ENNReal.ofReal data.data.rho.1) ≤
        common.F2.mass := by
    calc
      (1 / 4 : ENNReal) *
            Kakeya.realRpowENN delta (4 * common.badYLoss) *
            (ENNReal.ofReal (Real.pi / 4) *
              Kakeya.realRpowENN delta (data.data.targetLoss + 2) *
              data.data.cfg.family.enncard *
              ENNReal.ofReal data.data.rho.1) ≤
          (1 / 4 : ENNReal) *
            Kakeya.realRpowENN delta (4 * common.badYLoss) *
            data.data.scaleData.slabShading.mass := by
              gcongr
              exact data.data.scaleData.slab_mass
      _ ≤ common.F2.mass := common.F2_mass_retention
  have hpowerCard :
      Kakeya.realRpowENN delta (massLoss + 2) ≤
        (1 / 4 : ENNReal) *
          Kakeya.realRpowENN delta (4 * common.badYLoss) *
          Kakeya.realRpowENN delta (data.data.targetLoss + 2) := by
    calc
      Kakeya.realRpowENN delta (massLoss + 2) =
          Kakeya.realRpowENN delta 1 *
            (Kakeya.realRpowENN delta (4 * common.badYLoss) *
              Kakeya.realRpowENN delta (data.data.targetLoss + 2)) := by
        rw [← realRpowENN_add data.data.cfg.extremal.delta_pos,
          ← realRpowENN_add data.data.cfg.extremal.delta_pos]
        congr 1
        dsimp only [massLoss]
        ring
      _ ≤ (1 / 4 : ENNReal) *
          (Kakeya.realRpowENN delta (4 * common.badYLoss) *
            Kakeya.realRpowENN delta (data.data.targetLoss + 2)) := by
        gcongr
      _ = (1 / 4 : ENNReal) *
          Kakeya.realRpowENN delta (4 * common.badYLoss) *
          Kakeya.realRpowENN delta (data.data.targetLoss + 2) := by ring
  have hmassCard :
      ENNReal.ofReal (Real.pi / 4) *
          Kakeya.realRpowENN delta (massLoss + 2) *
          data.data.cfg.family.enncard *
          ENNReal.ofReal data.data.rho.1 ≤ common.F2.mass := by
    calc
      ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta (massLoss + 2) *
            data.data.cfg.family.enncard *
            ENNReal.ofReal data.data.rho.1 ≤
          ENNReal.ofReal (Real.pi / 4) *
            ((1 / 4 : ENNReal) *
              Kakeya.realRpowENN delta (4 * common.badYLoss) *
              Kakeya.realRpowENN delta (data.data.targetLoss + 2)) *
            data.data.cfg.family.enncard *
            ENNReal.ofReal data.data.rho.1 := by gcongr
      _ = (1 / 4 : ENNReal) *
          Kakeya.realRpowENN delta (4 * common.badYLoss) *
          (ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta (data.data.targetLoss + 2) *
            data.data.cfg.family.enncard *
            ENNReal.ofReal data.data.rho.1) := by ring
      _ ≤ common.F2.mass := hretained
  have hfamilyOne : (1 : ENNReal) ≤ data.data.cfg.family.enncard := by
    change (1 : ENNReal) ≤ (data.data.cfg.family.card : ENNReal)
    exact_mod_cast data.data.cfg.extremal.nonempty
  have hdeltaPi : Kakeya.realRpowENN delta 1 ≤
      ENNReal.ofReal (Real.pi / 4) := by
    have hreal : delta ≤ Real.pi / 4 :=
      data.delta_small.trans (by linarith [Real.pi_gt_three])
    calc
      Kakeya.realRpowENN delta 1 = ENNReal.ofReal delta := by
        simp [Kakeya.realRpowENN]
      _ ≤ ENNReal.ofReal (Real.pi / 4) := ENNReal.ofReal_mono hreal
  have hcoefficient : Kakeya.realRpowENN delta 1 ≤
      ENNReal.ofReal (Real.pi / 4) * data.data.cfg.family.enncard := by
    calc
      Kakeya.realRpowENN delta 1 ≤ ENNReal.ofReal (Real.pi / 4) := hdeltaPi
      _ = ENNReal.ofReal (Real.pi / 4) * 1 := by simp
      _ ≤ ENNReal.ofReal (Real.pi / 4) *
          data.data.cfg.family.enncard := by gcongr
  have hmass :
      Kakeya.realRpowENN delta (massLoss + 3) *
          ENNReal.ofReal data.data.rho.1 ≤ common.F2.mass := by
    calc
      Kakeya.realRpowENN delta (massLoss + 3) *
            ENNReal.ofReal data.data.rho.1 =
          Kakeya.realRpowENN delta (massLoss + 2) *
            Kakeya.realRpowENN delta 1 *
            ENNReal.ofReal data.data.rho.1 := by
              rw [← realRpowENN_add data.data.cfg.extremal.delta_pos]
              congr 2 <;> ring
      _ ≤ Kakeya.realRpowENN delta (massLoss + 2) *
          (ENNReal.ofReal (Real.pi / 4) *
            data.data.cfg.family.enncard) *
          ENNReal.ofReal data.data.rho.1 := by gcongr
      _ = ENNReal.ofReal (Real.pi / 4) *
          Kakeya.realRpowENN delta (massLoss + 2) *
          data.data.cfg.family.enncard *
          ENNReal.ofReal data.data.rho.1 := by ring
      _ ≤ common.F2.mass := hmassCard
  apply data.toLemma32DerivativeBandOn common.F2 massLoss
  · intro index
    rw [common.F2_eq]
    exact (wz2RefinedShading_subshading index).trans
      (data.data.scaleData.slab_subshading index)
  · exact common.F2_in_slab
  · exact hmassCard
  · exact hmass

/-- Core version of the paper-order bridge.  The derivative selection uses
only the whole-label common-slice shading and its retained mass; the stronger
quadratic frame estimate needed by the contradiction argument is irrelevant.

The fixed factor `1 / 4` is charged to one copy of the actual Section-6 power
`delta ^ epsilon`, rather than to a whole extra power of `delta`.  This keeps
the loss compatible with the later endpoint-cell cleanup. -/
theorem PureWZ2Lemma31DerivativeAssembly.toLemma32DerivativeBandAfterCommonYCore
    {sigma epsilon delta : ℝ}
    (data : PureWZ2Lemma31DerivativeAssembly sigma epsilon delta)
    (popular : PureWZ2WeightedPopularGlobalGrainData data.data.cfg data.data.rho
      data.data.scaleData)
    (frameSlope : ℝ)
    (common : PureWZ2RotatedWeightedCommonYCore data.data.cfg data.data.rho
      data.data.scaleData popular frameSlope)
    (hquarter : Kakeya.realRpowENN delta epsilon ≤ (1 / 4 : ENNReal)) :
    ∃ band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta,
      band.lemma31 = data ∧ band.sourceShading.union = common.F2.union ∧
      band.massLoss =
        data.data.targetLoss + 4 * common.badYLoss + epsilon := by
  let massLoss := data.data.targetLoss + 4 * common.badYLoss + epsilon
  have hretained :
      (1 / 4 : ENNReal) *
          Kakeya.realRpowENN delta (4 * common.badYLoss) *
          (ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta (data.data.targetLoss + 2) *
            data.data.cfg.family.enncard *
            ENNReal.ofReal data.data.rho.1) ≤
        common.F2.mass := by
    calc
      (1 / 4 : ENNReal) *
            Kakeya.realRpowENN delta (4 * common.badYLoss) *
            (ENNReal.ofReal (Real.pi / 4) *
              Kakeya.realRpowENN delta (data.data.targetLoss + 2) *
              data.data.cfg.family.enncard *
              ENNReal.ofReal data.data.rho.1) ≤
          (1 / 4 : ENNReal) *
            Kakeya.realRpowENN delta (4 * common.badYLoss) *
            data.data.scaleData.slabShading.mass := by
              gcongr
              exact data.data.scaleData.slab_mass
      _ ≤ common.F2.mass := common.F2_mass_retention
  have hpowerCard :
      Kakeya.realRpowENN delta (massLoss + 2) ≤
        (1 / 4 : ENNReal) *
          Kakeya.realRpowENN delta (4 * common.badYLoss) *
          Kakeya.realRpowENN delta (data.data.targetLoss + 2) := by
    calc
      Kakeya.realRpowENN delta (massLoss + 2) =
          Kakeya.realRpowENN delta epsilon *
            (Kakeya.realRpowENN delta (4 * common.badYLoss) *
              Kakeya.realRpowENN delta (data.data.targetLoss + 2)) := by
        rw [← realRpowENN_add data.data.cfg.extremal.delta_pos,
          ← realRpowENN_add data.data.cfg.extremal.delta_pos]
        congr 1
        dsimp only [massLoss]
        ring
      _ ≤ (1 / 4 : ENNReal) *
          (Kakeya.realRpowENN delta (4 * common.badYLoss) *
            Kakeya.realRpowENN delta (data.data.targetLoss + 2)) := by
        gcongr
      _ = (1 / 4 : ENNReal) *
          Kakeya.realRpowENN delta (4 * common.badYLoss) *
          Kakeya.realRpowENN delta (data.data.targetLoss + 2) := by ring
  have hmassCard :
      ENNReal.ofReal (Real.pi / 4) *
          Kakeya.realRpowENN delta (massLoss + 2) *
          data.data.cfg.family.enncard * ENNReal.ofReal data.data.rho.1 ≤
        common.F2.mass := by
    calc
      ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta (massLoss + 2) *
            data.data.cfg.family.enncard * ENNReal.ofReal data.data.rho.1 ≤
          ENNReal.ofReal (Real.pi / 4) *
            ((1 / 4 : ENNReal) *
              Kakeya.realRpowENN delta (4 * common.badYLoss) *
              Kakeya.realRpowENN delta (data.data.targetLoss + 2)) *
            data.data.cfg.family.enncard * ENNReal.ofReal data.data.rho.1 := by
              gcongr
      _ = (1 / 4 : ENNReal) *
          Kakeya.realRpowENN delta (4 * common.badYLoss) *
          (ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta (data.data.targetLoss + 2) *
            data.data.cfg.family.enncard *
            ENNReal.ofReal data.data.rho.1) := by ring
      _ ≤ common.F2.mass := hretained
  have hfamilyOne : (1 : ENNReal) ≤ data.data.cfg.family.enncard := by
    change (1 : ENNReal) ≤ (data.data.cfg.family.card : ENNReal)
    exact_mod_cast data.data.cfg.extremal.nonempty
  have hdeltaPi : Kakeya.realRpowENN delta 1 ≤
      ENNReal.ofReal (Real.pi / 4) := by
    have hreal : delta ≤ Real.pi / 4 :=
      data.delta_small.trans (by linarith [Real.pi_gt_three])
    calc
      Kakeya.realRpowENN delta 1 = ENNReal.ofReal delta := by
        simp [Kakeya.realRpowENN]
      _ ≤ ENNReal.ofReal (Real.pi / 4) := ENNReal.ofReal_mono hreal
  have hcoefficient : Kakeya.realRpowENN delta 1 ≤
      ENNReal.ofReal (Real.pi / 4) * data.data.cfg.family.enncard := by
    calc
      Kakeya.realRpowENN delta 1 ≤ ENNReal.ofReal (Real.pi / 4) := hdeltaPi
      _ = ENNReal.ofReal (Real.pi / 4) * 1 := by simp
      _ ≤ ENNReal.ofReal (Real.pi / 4) *
          data.data.cfg.family.enncard := by gcongr
  have hmass :
      Kakeya.realRpowENN delta (massLoss + 3) *
          ENNReal.ofReal data.data.rho.1 ≤ common.F2.mass := by
    calc
      Kakeya.realRpowENN delta (massLoss + 3) *
            ENNReal.ofReal data.data.rho.1 =
          Kakeya.realRpowENN delta (massLoss + 2) *
            Kakeya.realRpowENN delta 1 *
            ENNReal.ofReal data.data.rho.1 := by
              rw [← realRpowENN_add data.data.cfg.extremal.delta_pos]
              congr 2 <;> ring
      _ ≤ Kakeya.realRpowENN delta (massLoss + 2) *
          (ENNReal.ofReal (Real.pi / 4) *
            data.data.cfg.family.enncard) *
          ENNReal.ofReal data.data.rho.1 := by gcongr
      _ = ENNReal.ofReal (Real.pi / 4) *
          Kakeya.realRpowENN delta (massLoss + 2) *
          data.data.cfg.family.enncard *
          ENNReal.ofReal data.data.rho.1 := by ring
      _ ≤ common.F2.mass := hmassCard
  apply data.toLemma32DerivativeBandOn common.F2 massLoss
  · intro index
    rw [common.F2_eq]
    exact (wz2RefinedShading_subshading index).trans
      (data.data.scaleData.slab_subshading index)
  · exact common.F2_in_slab
  · exact hmassCard
  · exact hmass

/-- Positive-path common-slice and derivative-band data on one Lemma-31
configuration.  The frame is chosen at the midpoint of the original slab.
Its distance from the source slope on the eventual derivative band is kept
as an explicit certificate, rather than absorbed into a quadratic AD radius. -/
structure PureWZ2CoupledCommonYDerivativeBandData
    {sigma epsilon delta : ℝ}
    (data : PureWZ2Lemma31DerivativeAssembly sigma epsilon delta) where
  popular : PureWZ2WeightedPopularGlobalGrainData data.data.cfg data.data.rho
    data.data.scaleData
  frameSlope : ℝ
  frameSlope_eq : frameSlope = data.data.cfg.globalGrains.slope
    (data.data.scaleData.slabLeft +
      (data.data.scaleData.slabRight - data.data.scaleData.slabLeft) / 2)
  common : PureWZ2RotatedWeightedCommonYCore data.data.cfg data.data.rho
    data.data.scaleData popular frameSlope
  common_loss : common.badYLoss = data.eta / 2
  /-- The actual global-grain labels retained by the common-y refinement stay
  within one coarse-slab width of the fixed frame.  Keeping this certificate
  in the positive-path package is essential for transporting the Node-5 local
  normals after later height and tube-family restrictions. -/
  label_frame_close : ∀ label (hlabel : label ∈ common.selectedLabels),
    |data.data.cfg.globalGrains.slope
        ((pureWZ2PaperCellCenter delta
          (popular.label_anchor label
            (common.selectedLabels_subset hlabel))) 2) - frameSlope| ≤
      data.data.rho.1
  band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta
  band_lemma31 : band.lemma31 = data
  band_source_union : band.sourceShading.union = common.F2.union
  band_massLoss : band.massLoss =
    data.data.targetLoss + 4 * common.badYLoss + epsilon
  frame_abs : |frameSlope| ≤ 1
  frame_close_on_band : ∀ z ∈ Set.Icc band.left band.right,
    |frameSlope - data.data.globalSlope z| ≤ 1 / 4

/-- Select the positive common-y refinement before the derivative subband.
Only the ordinary one-Lipschitz variation of the actual Node-5 slope is used
to control the frame error. -/
theorem PureWZ2Lemma31DerivativeAssembly.toCoupledCommonYDerivativeBand
    {sigma epsilon delta : ℝ}
    (data : PureWZ2Lemma31DerivativeAssembly sigma epsilon delta) :
    Nonempty (PureWZ2CoupledCommonYDerivativeBandData data) := by
  rcases pureWZ2_weightedPopularGlobalGrains data.data.cfg data.data.rho
      data.data.scaleData with ⟨popular⟩
  let midpoint := data.data.scaleData.slabLeft +
    (data.data.scaleData.slabRight - data.data.scaleData.slabLeft) / 2
  let frameSlope := data.data.cfg.globalGrains.slope midpoint
  have hmidpoint : midpoint ∈ Set.Icc data.data.scaleData.slabLeft
      data.data.scaleData.slabRight := by
    dsimp only [midpoint]
    constructor <;> linarith [data.data.scaleData.slab_ordered]
  have hmidpointAmbient : midpoint ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨data.data.scaleData.slabLeft_mem.trans hmidpoint.1,
      hmidpoint.2.trans data.data.scaleData.slabRight_mem⟩
  have hframeAbs : |frameSlope| ≤ 1 := by
    exact (data.data.cfg.globalGrains.slope_normalized midpoint
      hmidpointAmbient).1
  have hlabelClose : ∀ label (hlabel : label ∈ popular.keptLabels),
      |data.data.cfg.globalGrains.slope
          ((pureWZ2PaperCellCenter delta
            (popular.label_anchor label hlabel)) 2) - frameSlope| ≤
        data.data.rho.1 := by
    intro label hlabel
    let anchorHeight := (pureWZ2PaperCellCenter delta
      (popular.label_anchor label hlabel)) 2
    have hanchorActive := (mem_pureWZ2GlobalGrainFiber
      data.data.cfg.globalGrains.slope delta popular.activeCells label
      (popular.label_anchor label hlabel)).mp
        (popular.label_anchor_mem label hlabel) |>.1
    have hactive : popular.label_anchor label hlabel ∈
        wz1PaperActiveCells data.data.scaleData.slabShading
          data.data.cfg.extremal.delta_pos := by
      simpa [popular.activeCells_eq] using hanchorActive
    rcases pureWZ2_activeCellCenter_mem_union
        data.data.cfg.extremal.delta_pos data.data.scaleData.slab_cubical
        hactive with ⟨index, hcarrier⟩
    have hanchorSlab : anchorHeight ∈
        Set.Icc data.data.scaleData.slabLeft
          data.data.scaleData.slabRight := by
      have hslab := data.data.scaleData.slab_in_slab index hcarrier
      change data.data.scaleData.slabLeft ≤ anchorHeight ∧
        anchorHeight ≤ data.data.scaleData.slabRight
      exact hslab
    have hanchorAmbient : anchorHeight ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨data.data.scaleData.slabLeft_mem.trans hanchorSlab.1,
        hanchorSlab.2.trans data.data.scaleData.slabRight_mem⟩
    have hlip := data.data.cfg.globalGrains.slope_lipschitzOn.dist_le_mul
      anchorHeight hanchorAmbient midpoint hmidpointAmbient
    have hspan : |anchorHeight - midpoint| ≤
        data.data.scaleData.slabRight - data.data.scaleData.slabLeft := by
      rw [abs_le]
      constructor <;> linarith [hanchorSlab.1, hanchorSlab.2,
        hmidpoint.1, hmidpoint.2]
    calc
      |data.data.cfg.globalGrains.slope anchorHeight - frameSlope| ≤
          |anchorHeight - midpoint| := by
        norm_num [frameSlope, Real.dist_eq] at hlip ⊢
        exact hlip
      _ ≤ data.data.scaleData.slabRight -
          data.data.scaleData.slabLeft := hspan
      _ = data.data.rho.1 := data.data.scaleData.slab_width
  have hframeSmall : data.data.rho.1 ≤ 1 / 100 :=
    data.rho_tiny.trans (by norm_num)
  rcases pureWZ2_rotatedWeightedCommonYRefinementCore_at_fine_power
      (stickyLoss := data.data.stickyLoss)
      (badYLoss := data.eta / 2) (power := epsilon)
      data.data.cfg data.data.rho data.data.scaleData popular
      (div_pos data.eta_pos (by norm_num))
      (by linarith [data.delta_small]) frameSlope hlabelClose hframeSmall
      data.data.rho_eq_power data.data.pointMultiplicity_upper
      (by simpa using data.common_y_small) with ⟨common, hcommonLoss⟩
  have hquarter : Kakeya.realRpowENN delta epsilon ≤
      (1 / 4 : ENNReal) := by
    calc
      Kakeya.realRpowENN delta epsilon =
          ENNReal.ofReal (Real.rpow delta epsilon) := rfl
      _ = ENNReal.ofReal data.data.rho.1 := by
        rw [data.data.rho_eq_power]
      _ ≤ ENNReal.ofReal (1 / 4 : ℝ) :=
        ENNReal.ofReal_mono (data.rho_tiny.trans (by norm_num))
      _ = (1 / 4 : ENNReal) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
        norm_num
  rcases data.toLemma32DerivativeBandAfterCommonYCore popular frameSlope
      common hquarter with ⟨band, hbandData, hbandSource, hbandLoss⟩
  have hframeCloseOnBand : ∀ z ∈ Set.Icc band.left band.right,
      |frameSlope - data.data.globalSlope z| ≤ 1 / 4 := by
    intro z hz
    have hzSlab : z ∈ Set.Icc data.data.scaleData.slabLeft
        data.data.scaleData.slabRight := by
      rw [← hbandData]
      exact ⟨band.left_mem.trans hz.1, hz.2.trans band.right_mem⟩
    have hzAmbient : z ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨data.data.scaleData.slabLeft_mem.trans hzSlab.1,
        hzSlab.2.trans data.data.scaleData.slabRight_mem⟩
    have hlip := data.data.cfg.globalGrains.slope_lipschitzOn.dist_le_mul
      midpoint hmidpointAmbient z hzAmbient
    have hspan : |midpoint - z| ≤
        data.data.scaleData.slabRight - data.data.scaleData.slabLeft := by
      rw [abs_le]
      constructor <;> linarith [hmidpoint.1, hmidpoint.2,
        hzSlab.1, hzSlab.2]
    have hcloseCfg : |frameSlope -
        data.data.cfg.globalGrains.slope z| ≤ data.data.rho.1 := by
      calc
        |frameSlope - data.data.cfg.globalGrains.slope z| ≤
            |midpoint - z| := by
          norm_num [frameSlope, Real.dist_eq] at hlip ⊢
          exact hlip
        _ ≤ data.data.scaleData.slabRight -
            data.data.scaleData.slabLeft := hspan
        _ = data.data.rho.1 := data.data.scaleData.slab_width
    rw [data.data.globalSlope_eq_on z hzAmbient]
    exact hcloseCfg.trans (data.rho_tiny.trans (by norm_num))
  exact ⟨{
    popular := popular
    frameSlope := frameSlope
    frameSlope_eq := rfl
    common := common
    common_loss := hcommonLoss
    label_frame_close := fun label hlabel =>
      hlabelClose label (common.selectedLabels_subset hlabel)
    band := band
    band_lemma31 := hbandData
    band_source_union := hbandSource
    band_massLoss := hbandLoss
    frame_abs := hframeAbs
    frame_close_on_band := hframeCloseOnBand
  }⟩

end Kakeya.Assouad
end
