import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Node6Lemma31ScaleInterface
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PowerWeightedCommonYNumerics
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FaithfulStep4Producer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FaithfulConvexOverload

/-!
# WZ2 Lemma 31 contradiction from one assembled power-scale slab
-/

noncomputable section
namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

theorem PureWZ2Lemma31ScaleAssembly.derivative_lower
    {sigma epsilon delta : ℝ}
    (data : PureWZ2Lemma31ScaleAssembly sigma epsilon delta)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hdeltaLtOne : delta < 1)
    (hdeltaSmall : delta ≤ 1 / 100)
    (hgeometrySmall : 256 * delta ≤ data.rho.1)
    (hscaleSmall : data.rho.1 ≤ 1 / 32)
    (hrhoQuarter : 64 * data.rho.1 ^ 2 ≤ 1 / 4)
    (hframeSmall : 2 * data.rho.1 ^ 2 ≤ 1 / 100)
    (hcommonSmall : Kakeya.realRpowENN delta
        (4 * (data.eta / 2) - data.targetLoss - data.targetLoss -
          (1 + epsilon) * data.stickyLoss) ≤
      ENNReal.ofReal (1 / 400000 : ℝ))
    (hprismSmall : Real.rpow delta
        (12 * data.eta - 4 * (data.eta / 2) - data.targetLoss) ≤
      1 / 100000)
    (hlocalADConstant : (36 : ENNReal) *
        (20 * Kakeya.realRpowENN delta (-data.targetLoss)) ≤
      Kakeya.realRpowENN delta (-(12 * data.eta)))
    (hoverloadAt : ∀ a b : ℝ, b - a ≤ Real.rpow delta epsilon →
      ∀ step4 : LargeSlopeFaithfulStep4Witness
          data.cfg.family sigma data.eta a b,
        ∃ W : Set Point3, Convex ℝ W ∧
          Kakeya.realRpowENN delta (-data.eta) * volume W *
              data.cfg.family.enncard <
            (wz1PaperBodyFamily
              data.cfg.family).containedCount W) :
    ∀ z ∈ Set.Icc data.scaleData.slabLeft data.scaleData.slabRight,
      data.scaleData.slabRight - data.scaleData.slabLeft ≤
        |deriv data.globalSlope z| := by
  intro z hz
  by_contra hderiv
  have hderivSmall :
      |deriv data.globalSlope z| <
        data.scaleData.slabRight - data.scaleData.slabLeft :=
    lt_of_not_ge hderiv
  let cfg := data.cfg
  let scale := data.rho
  have hwidth : data.scaleData.slabRight - data.scaleData.slabLeft = scale.1 :=
    data.scaleData.slab_width
  rcases pureWZ2_weightedPopularGlobalGrains cfg scale data.scaleData with
    ⟨popular⟩
  let frameSlope := cfg.globalGrains.slope z
  have hlabelClose : ∀ label (hlabel : label ∈ popular.keptLabels),
      |cfg.globalGrains.slope
          ((pureWZ2PaperCellCenter delta
            (popular.label_anchor label hlabel)) 2) - frameSlope| ≤
        2 * scale.1 ^ 2 := by
    intro label hlabel
    let anchor := pureWZ2PaperCellCenter delta
      (popular.label_anchor label hlabel)
    have hanchorActive := (mem_pureWZ2GlobalGrainFiber
      cfg.globalGrains.slope delta popular.activeCells label
      (popular.label_anchor label hlabel)).mp
        (popular.label_anchor_mem label hlabel) |>.1
    have hactive : popular.label_anchor label hlabel ∈
        wz1PaperActiveCells data.scaleData.slabShading
          cfg.extremal.delta_pos := by
      simpa [popular.activeCells_eq] using hanchorActive
    rcases pureWZ2_activeCellCenter_mem_union cfg.extremal.delta_pos
        data.scaleData.slab_cubical hactive with ⟨index, hcarrier⟩
    have hanchorSlab := data.scaleData.slab_in_slab index hcarrier
    have hclose := pureWZ2_slope_close_to_small_derivative_anchor
      data.globalSlope_normalized data.scaleData.slabLeft_mem
      data.scaleData.slab_ordered data.scaleData.slabRight_mem hz hanchorSlab
      hderivSmall
    rw [hwidth] at hclose
    have hzAmbient : z ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨data.scaleData.slabLeft_mem.trans hz.1,
        hz.2.trans data.scaleData.slabRight_mem⟩
    have hanchorAmbient : anchor 2 ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨data.scaleData.slabLeft_mem.trans hanchorSlab.1,
        hanchorSlab.2.trans data.scaleData.slabRight_mem⟩
    rw [data.globalSlope_eq_on _ hanchorAmbient,
      data.globalSlope_eq_on _ hzAmbient] at hclose
    simpa [frameSlope, anchor] using hclose
  rcases pureWZ2_rotatedWeightedCommonYRefinement_at_fine_power
      (stickyLoss := data.stickyLoss) (badYLoss := data.eta / 2)
      (power := epsilon) cfg scale data.scaleData popular (by
        exact div_pos data.eta_pos (by norm_num)) hdeltaLtOne frameSlope
      hlabelClose hframeSmall
      data.rho_eq_power data.pointMultiplicity_upper (by
        simpa using hcommonSmall) with ⟨common, hcommonLoss⟩
  let rho : ℝ := 64 * scale.1 ^ 2
  have hscalePos : 0 < scale.1 :=
    cfg.extremal.delta_pos.trans_le scale.2.1
  have hrhoPos : 0 < rho := by
    dsimp only [rho]
    exact mul_pos (by norm_num) (sq_pos_of_pos hscalePos)
  have hsqrtRho : Real.sqrt rho = 8 * scale.1 := by
    dsimp only [rho]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64),
      Real.sqrt_sq_eq_abs, abs_of_pos
        hscalePos]
    norm_num
  have hdeltaScaleSq : delta ≤ scale.1 ^ 2 := by
    rw [data.rho_eq_power]
    have hpower : Real.rpow delta 1 ≤
        Real.rpow delta (2 * epsilon) :=
      Real.rpow_le_rpow_of_exponent_ge
        (y := (1 : ℝ)) (z := 2 * epsilon) cfg.extremal.delta_pos
          cfg.extremal.delta_le_one (by linarith)
    have hrpowSq : Real.rpow delta (2 * epsilon) =
        (Real.rpow delta epsilon) ^ 2 := by
      calc
        Real.rpow delta (2 * epsilon) =
            Real.rpow delta (epsilon + epsilon) := by congr 1 <;> ring
        _ = Real.rpow delta epsilon * Real.rpow delta epsilon :=
          Real.rpow_add cfg.extremal.delta_pos _ _
        _ = (Real.rpow delta epsilon) ^ 2 := by ring
    calc
      delta = Real.rpow delta 1 := (Real.rpow_one delta).symm
      _ ≤ Real.rpow delta (2 * epsilon) := hpower
      _ = (Real.rpow delta epsilon) ^ 2 := hrpowSq
  have hdeltaRho : delta ≤ rho := by
    dsimp only [rho]
    nlinarith [hdeltaScaleSq]
  have hsixDeltaRho : 6 * delta ≤ rho := by
    dsimp only [rho]
    nlinarith [hdeltaScaleSq]
  have hdeltaBase : delta ≤ rho / 16 := by
    dsimp only [rho]
    nlinarith [hdeltaScaleSq]
  rcases pureWZ2_faithful_raw_prism_cover_of_frame_lower cfg scale
      data.scaleData popular frameSlope
      common.toPureWZ2RotatedWeightedCommonYCore (2 * scale.1 ^ 2)
      (by positivity) common.selected_label_frame_close (by
        nlinarith [hscalePos, hscaleSmall]) (by
        dsimp only [rho]
        nlinarith [sq_nonneg scale.1]) (by
        intro label hlabel
        have hselected : label ∈
            pureWZ2WeightedLabelsMeetingRotatedGoodSlice popular frameSlope
              common.goodY common.y0 := by
          simpa [common.selectedLabels_eq] using hlabel
        rcases Finset.mem_filter.mp hselected with ⟨_hkept, hslice⟩
        rcases hslice with ⟨slicePoint, hslicePoint⟩
        rcases pureWZ2_mem_ySlice_iff.mp hslicePoint with
          ⟨point, hpointGood, hpointEq⟩
        have hpointRegion : point ∈
            pureWZ2WeightedCroppedLabelRegion popular label := hpointGood.1
        have hpointCfg : point ∈ cfg.shading.union := by
          rw [pureWZ2WeightedCroppedLabelRegion_eq] at hpointRegion
          rcases Set.mem_iUnion₂.mp hpointRegion with
            ⟨sourceCell, hsourceCell, hpointCell⟩
          have hactive := (mem_pureWZ2GlobalGrainFiber
            cfg.globalGrains.slope delta popular.activeCells label sourceCell).mp
              hsourceCell |>.1
          have hslabActive : sourceCell ∈
              wz1PaperActiveCells data.scaleData.slabShading
                cfg.extremal.delta_pos := by
            simpa [popular.activeCells_eq] using hactive
          have hslabUnion : point ∈ data.scaleData.slabShading.union := by
            rw [data.scaleData.slab_cubical.union_eq_activeCells
              cfg.extremal.delta_pos]
            exact Set.mem_iUnion₂.mpr
              ⟨sourceCell, hslabActive, hpointCell⟩
          rcases hslabUnion with ⟨index, hcarrier⟩
          exact ⟨index, data.scaleData.slab_subshading index hcarrier⟩
        let source : {point : Point3 // point ∈ cfg.shading.union} :=
          ⟨point, hpointCfg⟩
        have hsourceClose :
            |cfg.globalGrains.slope (source.1 2) - frameSlope| ≤ 1 / 50 := by
          have hclose := common.selected_source_frame_close hlabel hpointRegion
          have hraw : delta / 2 + 2 * scale.1 ^ 2 ≤ 1 / 50 := by
            have hdeltaHalf : delta / 2 ≤ scale.1 / 512 := by
              linarith [hgeometrySmall]
            have hscaleSq2 : 2 * scale.1 ^ 2 ≤ scale.1 / 16 := by
              nlinarith [hscaleSmall, hscalePos]
            linarith
          exact hclose.trans hraw
        have hsourceY : pureWZ2HorizontalRotation frameSlope source.1 1 =
            common.y0 := by
          have hcoord := congr_arg (fun value : Point3 => value 1) hpointEq
          simpa [source, point3] using hcoord
        exact ⟨source, hpointRegion, by
          rw [hsourceY, sub_self, abs_zero]
          exact hscalePos.le, by
          simpa [cfg] using
            data.frameNormalCompatibility frameSlope source hsourceClose⟩)
      hrhoPos hsqrtRho hgeometrySmall hscaleSmall
      with ⟨raw⟩
  rcases pureWZ2_faithful_step4_producer_of_frame_lower cfg scale
      data.scaleData popular frameSlope
      common.toPureWZ2RotatedWeightedCommonYCore raw hsigma hsigmaOne
      (by rw [data.targetLoss_eq]; exact div_nonneg data.eta_pos.le (by norm_num))
      rfl hrhoPos
      hdeltaRho hsixDeltaRho hrhoQuarter hsqrtRho hgeometrySmall hscaleSmall
      hdeltaSmall hdeltaBase hlocalADConstant
      (by simpa [hcommonLoss] using hprismSmall)
      with ⟨step4⟩
  rcases hoverloadAt data.scaleData.slabLeft data.scaleData.slabRight
      (by rw [hwidth, data.rho_eq_power]) step4 with ⟨W, hconvex, hover⟩
  have hcwa := cfg.top_level_cwa W hconvex
  have hlossEta : data.targetLoss ≤ data.eta := by
    rw [data.targetLoss_eq]
    linarith [data.eta_pos]
  have hrpow : Kakeya.realRpowENN delta (-data.targetLoss) ≤
      Kakeya.realRpowENN delta (-data.eta) :=
    realRpowENN_antitone cfg.extremal.delta_pos cfg.extremal.delta_le_one
      (by linarith)
  have hupper : Kakeya.realRpowENN delta (-data.targetLoss) * volume W *
      cfg.family.enncard ≤ Kakeya.realRpowENN delta (-data.eta) * volume W *
        cfg.family.enncard := by gcongr
  exact (not_lt_of_ge (hcwa.trans hupper)) hover

end Kakeya.Assouad
end
