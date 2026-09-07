import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FaithfulStep4Numerics
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FaithfulStep4Witness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FaithfulPrismWholeAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CroppedStep4VolumeBound
import MyLeanRepo.Kakeya.Assouad.WZ1.ADScaleRefinement

/-!
# Faithful Step-4 witness producer
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set Finset

attribute [local instance] Classical.propDecidable

private lemma faithful_inner3 (x y : Point3) :
    inner ℝ x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  have h : inner ℝ x y = ∑ i : Fin 3, x i * y i := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    <;> simp [dotProduct, Fin.sum_univ_succ] <;> ring
  have h2 : ∑ i : Fin 3, x i * y i =
      x 0 * y 0 + x 1 * y 1 + x 2 * y 2 :=
    by
      simp [Fin.sum_univ_succ]
      ring
  rw [h, h2]

/-- Mass-regularize the faithful raw fixed-frame prism cover. -/
theorem pureWZ2_faithful_step4_producer_of_frame_lower
    {sigma loss delta rho eta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData cfg.shading sigma loss scale)
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (frameSlope : ℝ)
    (common : PureWZ2RotatedWeightedCommonYCore
      cfg scale scaleData popular frameSlope)
    (raw : PureWZ2FaithfulRawPrismCover
      cfg scale scaleData popular frameSlope common rho)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hloss : 0 ≤ loss)
    (hrhoEq : rho = 64 * scale.1 ^ 2)
    (hrhoPos : 0 < rho)
    (hdeltaRho : delta ≤ rho)
    (hsixDeltaRho : 6 * delta ≤ rho)
    (hrhoQuarter : rho ≤ 1 / 4)
    (hsqrtRho : Real.sqrt rho = 8 * scale.1)
    (hsmall : 256 * delta ≤ scale.1)
    (hscaleSmall : scale.1 ≤ 1 / 32)
    (hdeltaSmall : delta ≤ 1 / 100)
    (hdeltaBase : delta ≤ rho / 16)
    (hlocalADConstant : (36 : ENNReal) *
      (20 * Kakeya.realRpowENN delta (-loss)) ≤
      Kakeya.realRpowENN delta (-(12 * eta)))
    (hprismSmall : Real.rpow delta
      (12 * eta - 4 * common.badYLoss - loss) ≤ 1 / 100000) :
    Nonempty (LargeSlopeFaithfulStep4Witness cfg.family sigma eta
      scaleData.slabLeft scaleData.slabRight) := by
  let thresholdReal : ℝ :=
    36 * Real.rpow delta (12 * eta) * delta ^ 2 * Real.sqrt rho
  let threshold : ENNReal := ENNReal.ofReal thresholdReal
  have hthresholdPos : 0 < threshold := by
    apply ENNReal.ofReal_pos.mpr
    dsimp only [thresholdReal]
    have hsqrtPos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrhoPos
    have hpowPos : 0 < Real.rpow delta (12 * eta) :=
      Real.rpow_pos_of_pos cfg.extremal.delta_pos _
    exact mul_pos (mul_pos (mul_pos (by norm_num) hpowPos)
      (sq_pos_of_pos cfg.extremal.delta_pos)) hsqrtPos
  let piece : Fin cfg.family.card → Fin raw.prismCount → Set Point3 :=
    fun i j => if threshold ≤ volume (raw.piece i j) then raw.piece i j else ∅
  have hpieceMeasurable : ∀ i j, MeasurableSet (piece i j) := by
    intro i j
    by_cases hheavy : threshold ≤ volume (raw.piece i j)
    · simp [piece, hheavy, raw.piece_measurable i j]
    · simp [piece, hheavy]
  have hpieceSubRaw : ∀ i j, piece i j ⊆ raw.piece i j := by
    intro i j
    by_cases hheavy : threshold ≤ volume (raw.piece i j)
    · simp [piece, hheavy]
    · simp [piece, hheavy]
  have hpieceSubFine : ∀ i j, piece i j ⊆ common.F2.carrier i := by
    intro i j
    exact (hpieceSubRaw i j).trans fun _ hpoint =>
      (by rw [raw.piece_eq i j] at hpoint; exact hpoint.1)
  have hpieceSubPrism : ∀ i j, piece i j ⊆ raw.prism j := by
    intro i j
    exact (hpieceSubRaw i j).trans fun _ hpoint =>
      (by rw [raw.piece_eq i j] at hpoint; exact hpoint.2)
  have hpieceSubSegment : ∀ i j, piece i j ⊆
      tubeSegmentCarrier (6 * delta) (cfg.family.tube i).base
        (cfg.family.tube i).direction (raw.segmentStart i) rho := by
    intro i j
    exact (hpieceSubRaw i j).trans (raw.piece_sub_segment i j)
  have hmassLower : ∀ i j, volume (piece i j) ≠ 0 →
      threshold ≤ volume (piece i j) := by
    intro i j hnonzero
    by_cases hheavy : threshold ≤ volume (raw.piece i j)
    · simpa [piece, hheavy] using hheavy
    · have hempty : piece i j = ∅ := by simp [piece, hheavy]
      rw [hempty] at hnonzero
      simp at hnonzero
  have hrawMassUpper : ∀ i j, volume (raw.piece i j) ≤
      ENNReal.ofReal (36 * Real.sqrt rho * delta ^ 2) := by
    intro i j
    let tube := cfg.family.tube i
    let bound : Set Point3 := {point |
      Metric.infDist point (tubeAxisLine tube) ≤ 6 * delta ∧
        point 2 ∈ Set.Icc scaleData.slabLeft scaleData.slabRight}
    have hsubset : raw.piece i j ⊆ bound := by
      intro point hpoint
      have hF2 : point ∈ common.F2.carrier i := by
        rw [raw.piece_eq i j] at hpoint
        exact hpoint.1
      have hpaper : point ∈ wz1PaperTubeCarrier tube :=
        common.F2.subset_body i hF2
      have hclosed : point ∈ Metric.cthickening (6 * delta)
          (tubeAxisLine tube) := hpaper.1
      have hinfEDist := (Metric.mem_cthickening_iff.mp hclosed)
      have hlineNonempty : (tubeAxisLine tube).Nonempty :=
        ⟨tube.base, 0, by simp⟩
      have hfinite : Metric.infEDist point (tubeAxisLine tube) ≠ ⊤ :=
        Metric.infEDist_ne_top hlineNonempty
      have hinf : Metric.infDist point (tubeAxisLine tube) ≤ 6 * delta := by
        have heq : ENNReal.ofReal
            (Metric.infDist point (tubeAxisLine tube)) =
              Metric.infEDist point (tubeAxisLine tube) :=
          ENNReal.ofReal_toReal hfinite
        rw [← heq] at hinfEDist
        exact (ENNReal.ofReal_le_ofReal_iff
          (by linarith [cfg.extremal.delta_pos] : 0 ≤ 6 * delta)).mp hinfEDist
      exact ⟨hinf, common.F2_in_slab i hF2⟩
    have hmono : volume (raw.piece i j) ≤ volume bound :=
      measure_mono hsubset
    have hbound : volume bound ≤
        ENNReal.ofReal
          (4 * (6 * delta) ^ 2 * 2 *
            (scaleData.slabRight - scaleData.slabLeft)) :=
      tube_thickening_zslab_volume_bound
        (by linarith [cfg.extremal.delta_pos] : 0 < 6 * delta)
        tube.direction_unit scaleData.slab_ordered (by
          have hline := (cfg.line_class i).1
          have hpositive : 0 < wz1PaperDirection tube 2 := by linarith
          have habs : |tube.direction 2| = wz1PaperDirection tube 2 := by
            simp [wz1PaperDirection]
            split_ifs with h
            · simp [abs_of_nonneg h]
            · have hnonpos : tube.direction 2 ≤ 0 := le_of_not_ge h
              simp [abs_of_nonpos hnonpos]
          rw [habs]
          exact hline)
    have heq : 4 * (6 * delta) ^ 2 * 2 *
        (scaleData.slabRight - scaleData.slabLeft) =
          36 * Real.sqrt rho * delta ^ 2 := by
      rw [scaleData.slab_width, hsqrtRho]
      ring
    rw [heq] at hbound
    exact hmono.trans hbound
  have hmassUpper : ∀ i j, volume (piece i j) ≤
      ENNReal.ofReal (4000 * Real.sqrt rho * delta ^ 2) := by
    intro i j
    calc
      volume (piece i j) ≤ volume (raw.piece i j) :=
        measure_mono (hpieceSubRaw i j)
      _ ≤ ENNReal.ofReal (36 * Real.sqrt rho * delta ^ 2) :=
        hrawMassUpper i j
      _ ≤ ENNReal.ofReal (4000 * Real.sqrt rho * delta ^ 2) := by
        apply ENNReal.ofReal_mono
        have hsqrtNonneg := Real.sqrt_nonneg rho
        have hdeltaSq : 0 ≤ delta ^ 2 := sq_nonneg delta
        nlinarith
  have hnormalUnit : ∀ j, ‖raw.prismNormal j‖ = 1 := by
    exact raw.prismNormal_unit
  have hnormalY : ∀ j, pureWZ2HorizontalRotation frameSlope
      (raw.prismNormal j) 1 = 0 := by
    exact raw.prismNormal_rotated_y_zero
  have htransverse : ∀ j, raw.prism j ⊆
      {point | |inner ℝ (point - (raw.sourcePoint j).1)
        (raw.prismNormal j)| ≤ Real.sqrt rho} := by
    intro j point hpoint
    let rotation := pureWZ2HorizontalRotation frameSlope
    have hnear := raw.source_near_prism j point hpoint
    have hnormalRotUnit : ‖rotation (raw.prismNormal j)‖ = 1 := by
      rw [rotation.norm_map, hnormalUnit j]
    have hnormal0 : |rotation (raw.prismNormal j) 0| ≤ 1 := by
      have hcoord := PiLp.norm_apply_le (rotation (raw.prismNormal j)) 0
      simpa [Real.norm_eq_abs, hnormalRotUnit] using hcoord
    have hnormal2 : |rotation (raw.prismNormal j) 2| ≤ 1 := by
      have hcoord := PiLp.norm_apply_le (rotation (raw.prismNormal j)) 2
      simpa [Real.norm_eq_abs, hnormalRotUnit] using hcoord
    have hinner : inner ℝ (point - (raw.sourcePoint j).1)
        (raw.prismNormal j) =
      (rotation point 0 - rotation (raw.sourcePoint j).1 0) *
          rotation (raw.prismNormal j) 0 +
        (rotation point 2 - rotation (raw.sourcePoint j).1 2) *
          rotation (raw.prismNormal j) 2 := by
      rw [← rotation.inner_map_map
        (point - (raw.sourcePoint j).1) (raw.prismNormal j),
        rotation.map_sub]
      have hy := hnormalY j
      rw [faithful_inner3]
      rw [hy]
      simp
    change |inner ℝ (point - (raw.sourcePoint j).1)
      (raw.prismNormal j)| ≤ Real.sqrt rho
    rw [hinner]
    calc
      |(rotation point 0 - rotation (raw.sourcePoint j).1 0) *
          rotation (raw.prismNormal j) 0 +
        (rotation point 2 - rotation (raw.sourcePoint j).1 2) *
          rotation (raw.prismNormal j) 2| ≤
          |rotation point 0 - rotation (raw.sourcePoint j).1 0| +
            |rotation point 2 - rotation (raw.sourcePoint j).1 2| := by
        calc
          _ ≤ |rotation point 0 - rotation (raw.sourcePoint j).1 0| *
              |rotation (raw.prismNormal j) 0| +
            |rotation point 2 - rotation (raw.sourcePoint j).1 2| *
              |rotation (raw.prismNormal j) 2| := by
                simpa [abs_mul] using abs_add_le
                  ((rotation point 0 - rotation (raw.sourcePoint j).1 0) *
                    rotation (raw.prismNormal j) 0)
                  ((rotation point 2 - rotation (raw.sourcePoint j).1 2) *
                    rotation (raw.prismNormal j) 2)
          _ ≤ _ := by
            let dx := |rotation point 0 - rotation (raw.sourcePoint j).1 0|
            let dz := |rotation point 2 - rotation (raw.sourcePoint j).1 2|
            apply add_le_add
            · change dx * |rotation (raw.prismNormal j) 0| ≤ dx
              simpa only [mul_one] using
                mul_le_mul_of_nonneg_left hnormal0 (abs_nonneg _)
            · change dz * |rotation (raw.prismNormal j) 2| ≤ dz
              simpa only [mul_one] using
                mul_le_mul_of_nonneg_left hnormal2 (abs_nonneg _)
      _ ≤ (scale.1 + (8 * delta + 2 * raw.frameGap)) +
          (scale.1 + 8 * delta) := by
        exact add_le_add (by simpa [rotation, abs_sub_comm] using hnear.1)
          (by simpa [rotation, abs_sub_comm] using hnear.2)
      _ ≤ Real.sqrt rho := by
        rw [hsqrtRho]
        have h8 : 16 * delta ≤ scale.1 / 16 := by linarith
        have hgap : 2 * raw.frameGap ≤ scale.1 / 8 := by
          linarith [raw.frameGap_small]
        have hscalePos : 0 < scale.1 :=
          cfg.extremal.delta_pos.trans_le scale.2.1
        calc
          (scale.1 + (8 * delta + 2 * raw.frameGap)) +
              (scale.1 + 8 * delta) ≤
            scale.1 + scale.1 + scale.1 / 16 + scale.1 / 8 := by
              linarith
          _ ≤ 8 * scale.1 := by nlinarith
  have hrawLocalAD : ∀ i j, IsADSet1
      (scalarProjection (raw.prismNormal j) (raw.piece i j))
        rho (1 - sigma) (Kakeya.realRpowENN delta (-(12 * eta))) := by
    intro i j
    exact raw.piece_local_ad_of_frame_lower hdeltaSmall hrhoPos
      (hrhoQuarter.trans (by norm_num)) hdeltaBase hsqrtRho hsmall
      hscaleSmall hlocalADConstant i j
  have hpieceLocalAD : ∀ i j, volume (piece i j) ≠ 0 → IsADSet1
      (scalarProjection (raw.prismNormal j) (piece i j))
        rho (1 - sigma) (Kakeya.realRpowENN delta (-(12 * eta))) := by
    intro i j hnonzero
    have hheavy : threshold ≤ volume (raw.piece i j) := by
      by_contra hnot
      have hempty : piece i j = ∅ := by simp [piece, hnot]
      rw [hempty] at hnonzero
      simp at hnonzero
    simpa [piece, hheavy] using hrawLocalAD i j
  have hprismCard := raw.prism_card_upper hsigma hsigmaOne
    hrhoEq hprismSmall

  have hrawCoverMass : common.F2.mass ≤
      ∑ i : Fin cfg.family.card, ∑ j : Fin raw.prismCount,
        volume (raw.piece i j) := by
    apply Finset.sum_le_sum
    intro i _
    have hcover : common.F2.carrier i ⊆
        ⋃ j : Fin raw.prismCount, raw.piece i j := by
      intro point hpoint
      rcases raw.covers i point hpoint with ⟨j, hj⟩
      exact Set.mem_iUnion.mpr ⟨j, hj⟩
    exact (measure_mono hcover).trans
      (MeasureTheory.measure_iUnion_fintype_le volume (raw.piece i))
  have hperTubeDiscard : ∀ i,
      ∑ j : Fin raw.prismCount, volume (raw.piece i j) ≤
        ∑ j : Fin raw.prismCount, volume (piece i j) + 3 * threshold := by
    intro i
    let support := (Finset.univ : Finset (Fin raw.prismCount)).filter
      fun j => volume (raw.piece i j) ≠ 0
    have hsupportCard : support.card ≤ 3 := raw.support_card i
    have hsumRaw : ∑ j : Fin raw.prismCount, volume (raw.piece i j) =
        ∑ j ∈ support, volume (raw.piece i j) := by
      rw [Finset.sum_subset (show support ⊆ Finset.univ from subset_univ _)]
      intro j _ hnot
      simp [support] at hnot
      exact hnot
    have hsumPiece : ∑ j : Fin raw.prismCount, volume (piece i j) =
        ∑ j ∈ support, volume (piece i j) := by
      rw [Finset.sum_subset (show support ⊆ Finset.univ from subset_univ _)]
      intro j _ hnot
      have hzero : volume (raw.piece i j) = 0 := by
        simp [support] at hnot
        exact hnot
      have hnotHeavy : ¬ threshold ≤ volume (raw.piece i j) := by
        rw [hzero]
        exact not_le.mpr hthresholdPos
      simp [piece, hnotHeavy]
    rw [hsumRaw, hsumPiece]
    calc
      ∑ j ∈ support, volume (raw.piece i j) ≤
          ∑ j ∈ support, (volume (piece i j) + threshold) := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hheavy : threshold ≤ volume (raw.piece i j)
        · simp [piece, hheavy]
        · have hle : volume (raw.piece i j) ≤ threshold := le_of_not_ge hheavy
          simpa [piece, hheavy] using hle
      _ = ∑ j ∈ support, volume (piece i j) +
          (support.card : ENNReal) * threshold := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ support, volume (piece i j) + 3 * threshold := by
        gcongr
        exact_mod_cast hsupportCard
  let discarded : ENNReal := (cfg.family.card : ENNReal) * 3 * threshold
  have htotalDiscard :
      ∑ i : Fin cfg.family.card, ∑ j : Fin raw.prismCount,
          volume (raw.piece i j) ≤
        (∑ i : Fin cfg.family.card, ∑ j : Fin raw.prismCount,
          volume (piece i j)) + discarded := by
    calc
      ∑ i, ∑ j, volume (raw.piece i j) ≤
          ∑ i, (∑ j, volume (piece i j) + 3 * threshold) := by
        apply Finset.sum_le_sum
        intro i _
        exact hperTubeDiscard i
      _ = (∑ i, ∑ j, volume (piece i j)) + discarded := by
        simp [discarded, Finset.sum_add_distrib, Finset.sum_const]
        ring
  let target : ENNReal := threshold * cfg.family.enncard
  have htargetDiscardF2 : target + discarded ≤ common.F2.mass := by
    have hfamilyCard : cfg.family.enncard =
        (cfg.family.card : ENNReal) := rfl
    have hbudget := pureWZ2_faithful_pruning_budget
      cfg.extremal.delta_pos
        (cfg.extremal.delta_pos.trans_le scale.2.1) hsqrtRho hprismSmall
    have hbudgetCard : (cfg.family.card : ENNReal) * (4 * threshold) ≤
        (1 / 4 : ENNReal) *
          Kakeya.realRpowENN delta (4 * common.badYLoss) *
          (ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta (loss + 2) *
              cfg.family.enncard * ENNReal.ofReal scale.1) := by
      rw [hfamilyCard]
      dsimp only [threshold, thresholdReal] at hbudget ⊢
      calc
        (cfg.family.card : ENNReal) *
            (4 * ENNReal.ofReal
              (36 * Real.rpow delta (12 * eta) * delta ^ 2 *
                Real.sqrt rho)) ≤
          (cfg.family.card : ENNReal) *
            ((1 / 4 : ENNReal) *
              Kakeya.realRpowENN delta (4 * common.badYLoss) *
              (ENNReal.ofReal (Real.pi / 4) *
                Kakeya.realRpowENN delta (loss + 2) *
                  ENNReal.ofReal scale.1)) := by gcongr
        _ = (1 / 4 : ENNReal) *
          Kakeya.realRpowENN delta (4 * common.badYLoss) *
          (ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta (loss + 2) *
              (cfg.family.card : ENNReal) * ENNReal.ofReal scale.1) := by ring
    have htoSlab :
        (1 / 4 : ENNReal) *
          Kakeya.realRpowENN delta (4 * common.badYLoss) *
          (ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta (loss + 2) *
              cfg.family.enncard * ENNReal.ofReal scale.1) ≤
        (1 / 4 : ENNReal) *
          Kakeya.realRpowENN delta (4 * common.badYLoss) *
          scaleData.slabShading.mass := by
      gcongr
      exact scaleData.slab_mass
    have hfour : target + discarded =
        (cfg.family.card : ENNReal) * (4 * threshold) := by
      simp [target, discarded, hfamilyCard]
      ring
    rw [hfour]
    exact hbudgetCard.trans (htoSlab.trans (by
      exact common.F2_mass_retention))
  have htargetRaw : target + discarded ≤
      ∑ i : Fin cfg.family.card, ∑ j : Fin raw.prismCount,
        volume (raw.piece i j) :=
    htargetDiscardF2.trans hrawCoverMass
  have hdiscardedFinite : discarded ≠ ⊤ := by
    dsimp only [discarded]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by simp) (by norm_num))
      (by simp [threshold, ENNReal.ofReal_ne_top])
  have htarget : target ≤
      ∑ i : Fin cfg.family.card, ∑ j : Fin raw.prismCount,
        volume (piece i j) := by
    have hwithDiscard : target + discarded ≤
        (∑ i, ∑ j, volume (piece i j)) + discarded :=
      htargetRaw.trans htotalDiscard
    exact (ENNReal.add_le_add_iff_right hdiscardedFinite).mp hwithDiscard
  exact ⟨{
    rho := rho
    rho_eq := hrhoEq.trans (by rw [scaleData.slab_width])
    rho_pos := hrhoPos
    delta_le_rho := hdeltaRho
    six_delta_le_rho := hsixDeltaRho
    rho_le_quarter := hrhoQuarter
    sqrt_rho_eq := hsqrtRho.trans (by rw [scaleData.slab_width])
    fine := common.F2
    prismCount := raw.prismCount
    prismCount_pos := raw.prismCount_pos
    prism := raw.prism
    prismNormal := raw.prismNormal
    prismNormal_unit := hnormalUnit
    prismCenter := fun j => (raw.sourcePoint j).1
    prism_transverse := htransverse
    segmentStart := fun i _ => raw.segmentStart i
    piece := piece
    piece_measurable := hpieceMeasurable
    piece_sub_fine := hpieceSubFine
    piece_sub_prism := hpieceSubPrism
    piece_sub_segment := hpieceSubSegment
    total_piece_mass := by
      simpa [target, threshold, thresholdReal]
        using htarget
    piece_mass_lower := by
      intro i j hnonzero
      simpa [threshold, thresholdReal] using hmassLower i j hnonzero
    piece_mass_upper := hmassUpper
    piece_local_ad := hpieceLocalAD
    prism_card_upper := hprismCard
  }⟩

/-- Compatibility wrapper retaining the previous public signature. -/
theorem pureWZ2_faithful_step4_producer
    {sigma loss delta rho eta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta)
    (scale : WZ2PaperRequestedScale delta)
    (scaleData : PureWZ2Section6ScaleData cfg.shading sigma loss scale)
    (popular : PureWZ2WeightedPopularGlobalGrainData cfg scale scaleData)
    (frameSlope : ℝ)
    (common : PureWZ2RotatedWeightedCommonYData
      cfg scale scaleData popular frameSlope)
    (raw : PureWZ2FaithfulRawPrismCover
      cfg scale scaleData popular frameSlope
        common.toPureWZ2RotatedWeightedCommonYCore rho)
    (_compatibility : PureWZ2LocalGlobalCompatibility cfg)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hloss : 0 ≤ loss)
    (hrhoEq : rho = 64 * scale.1 ^ 2)
    (hrhoPos : 0 < rho)
    (hdeltaRho : delta ≤ rho)
    (hsixDeltaRho : 6 * delta ≤ rho)
    (hrhoQuarter : rho ≤ 1 / 4)
    (hsqrtRho : Real.sqrt rho = 8 * scale.1)
    (hsmall : 256 * delta ≤ scale.1)
    (hscaleSmall : scale.1 ≤ 1 / 32)
    (hdeltaSmall : delta ≤ 1 / 100)
    (hdeltaBase : delta ≤ rho / 16)
    (hlocalADConstant : (36 : ENNReal) *
      (20 * Kakeya.realRpowENN delta (-loss)) ≤
      Kakeya.realRpowENN delta (-(12 * eta)))
    (hprismSmall : Real.rpow delta
      (12 * eta - 4 * common.badYLoss - loss) ≤ 1 / 100000) :
    Nonempty (LargeSlopeFaithfulStep4Witness cfg.family sigma eta
      scaleData.slabLeft scaleData.slabRight) :=
  pureWZ2_faithful_step4_producer_of_frame_lower cfg scale scaleData popular
    frameSlope common.toPureWZ2RotatedWeightedCommonYCore raw
    hsigma hsigmaOne hloss hrhoEq hrhoPos hdeltaRho
    hsixDeltaRho hrhoQuarter hsqrtRho hsmall hscaleSmall hdeltaSmall
    hdeltaBase hlocalADConstant hprismSmall

end Kakeya.Assouad

end
