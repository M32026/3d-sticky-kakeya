import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularGraphParents
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleSources
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ProjectionHeavyFiberInSource
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23HeavyFiberThreshold
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23FullGrainNormalBound
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalBinPackage

/-!
# Terminal local bins from full-parent normal witnesses

The outer-popular graph carrier need not retain the absolute local source
mass needed to manufacture a full grain inside each localized piece.  The
paper-order replacement proves the normal bound first on the complete
balanced parent, transfers that bound to the outer-popular anchor through the
original one-Lipschitz plane map, and only then counts actual cells of the
outer-popular graph.

No point from a discarded height is inserted into the graph carrier.  The
complete parent is used only as an auxiliary witness for its normal.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The generalized unit-normal calculation has a fixed margin above `1/4`. -/
theorem pureWZ2_normal_first_component_generalized_margin
    (normal : Point3) (slope : ℝ)
    (hnorm : ‖normal‖ = 1)
    (hvertical : |normal (2 : Fin 3)| ≤ 1 / 2)
    (hslope : |slope| ≤ 3)
    (htilt :
      |normal (1 : Fin 3) -
          slope * normal (0 : Fin 3)| ≤ 1 / 14) :
    63 / 250 ≤ |normal (0 : Fin 3)| := by
  set a := normal (0 : Fin 3) with ha_def
  set b := normal (1 : Fin 3) with hb_def
  set c := normal (2 : Fin 3) with hc_def
  set m := slope with hm_def
  have hnormSq : a ^ 2 + b ^ 2 + c ^ 2 = 1 := by
    have hsq : ‖normal‖ ^ 2 = ∑ i : Fin 3, normal i ^ 2 :=
      EuclideanSpace.real_norm_sq_eq normal
    rw [hnorm] at hsq
    simpa [Fin.sum_univ_succ, add_assoc, ha_def, hb_def, hc_def] using hsq.symm
  have hcSq : c ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith [sq_abs c, abs_nonneg c]
  have hhoriz : (3 / 4 : ℝ) ≤ a ^ 2 + b ^ 2 := by
    nlinarith
  by_contra h
  have haSmall : |a| < 63 / 250 := by linarith
  have hbBound : |b| < 1448 / 1750 := by
    calc
      |b| = |(b - m * a) + m * a| := by rw [sub_add_cancel]
      _ ≤ |b - m * a| + |m * a| := abs_add_le _ _
      _ = |b - m * a| + |m| * |a| := by rw [abs_mul]
      _ ≤ 1 / 14 + 3 * |a| := by gcongr <;> linarith
      _ < 1 / 14 + 3 * (63 / 250 : ℝ) := by gcongr
      _ = 1448 / 1750 := by norm_num
  have hbSq : b ^ 2 < (1448 / 1750 : ℝ) ^ 2 := by
    have hsq : |b| ^ 2 < (1448 / 1750 : ℝ) ^ 2 := by
      gcongr <;> positivity
    simpa [sq_abs b] using hsq
  have haSq : a ^ 2 < (63 / 250 : ℝ) ^ 2 := by
    have hsq : |a| ^ 2 < (63 / 250 : ℝ) ^ 2 := by
      gcongr <;> positivity
    simpa [sq_abs a] using hsq
  have hnumeric :
      (63 / 250 : ℝ) ^ 2 + (1448 / 1750 : ℝ) ^ 2 < 3 / 4 := by
    norm_num
  nlinarith

/-- The full-grain argument retains the fixed margin needed for transport
within one side-`sqrt delta` parent. -/
theorem pureWZ2_full_grain_normal_first_component_generalized_margin
    (rho sigma eta : ℝ) (C : ENNReal)
    (slope : ℝ → ℝ)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hCtop : C ≠ ⊤)
    (hCpower : C ≤ Kakeya.realRpowENN rho (-eta))
    (hPlanarSmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt rho ≤ 1)
    (habsorb :
      Real.rpow rho (1 - 4 * eta / sigma) ≤
        Real.sqrt rho / 14)
    (input : WZ1Lemma23FullLocalGrainInputGeneralized
      rho sigma eta C slope) :
    63 / 250 ≤ |input.normal (0 : Fin 3)| := by
  rcases wz1_lemma23_normal_tilt_witness_from_full_grain_generalized
      rho sigma eta C slope hrho hrhoOne heta hPlanarSmall hrootSmall20 input with
    ⟨z, hz, htiltRoot⟩ | ⟨witness, _hwitnessHeight⟩
  · have hrootFourteenth : Real.sqrt rho ≤ 1 / 14 := by
      linarith [hrootSmall20]
    exact pureWZ2_normal_first_component_generalized_margin
      input.normal (slope z) input.normal_unit input.normal_vertical
      (input.slope_small z hz) (htiltRoot.trans hrootFourteenth)
  · have htilt := (wz1_lemma23_normal_tilt_generalized
      rho sigma eta C slope input.normal hrho hrhoOne hsigma hsigmaOne
      heta hetaSigma hCtop hCpower habsorb witness).2
    exact pureWZ2_normal_first_component_generalized_margin
      input.normal (slope witness.sliceHeight) witness.normal_unit
      witness.normal_vertical witness.slope_small htilt

structure PureWZ2TerminalPopularFullParentLocalBinData
    {sigma inputLoss delta stickyLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    {line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line}
    {selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents}
    {selectedCarrier :
      PureWZ2TerminalPopularSelectedParentCarrierData selection}
    {sources : PureWZ2TerminalPopularCoarseSourceFamily selection}
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    {prep : PureWZ2TerminalPopularGraphPreparation localized}
    (graphParents : PureWZ2TerminalPopularGraphParentData prep) where
  localBins : WZ1Lemma23LocalBinPackage
    (rho := delta) (sigma := sigma)
    (pureWZ2TerminalPopularGraphConstant delta inputLoss)
    prep.windowed.global.cells
  normal_first : ∀ cell (hcell : cell ∈ prep.windowed.global.cells),
    1 / 4 ≤ |prep.localGrains.planeMap
      (graphParents.anchorFor cell hcell) (0 : Fin 3)|

private lemma pureWZ2_terminalPopular_nat_le_ceil_add_one
    {n : ℕ} {X : ENNReal} (hX : X ≠ ⊤)
    (hn : (n : ENNReal) ≤ X) :
    n ≤ Nat.ceil X.toReal + 1 := by
  have hreal : (n : ℝ) ≤ X.toReal := by
    rw [← ENNReal.toReal_natCast n]
    exact (ENNReal.toReal_le_toReal (ENNReal.natCast_ne_top n) hX).mpr hn
  have hceil : n ≤ Nat.ceil X.toReal := by
    exact_mod_cast hreal.trans (Nat.le_ceil X.toReal)
  omega

/-- Construct the actual outer-popular local bins using full balanced parents
only as auxiliary normal witnesses. -/
theorem PureWZ2TerminalPopularGraphParentData.fullParentLocalBins
    {sigma inputLoss delta stickyLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    {line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line}
    {selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents}
    {selectedCarrier :
      PureWZ2TerminalPopularSelectedParentCarrierData selection}
    {sources : PureWZ2TerminalPopularCoarseSourceFamily selection}
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    {prep : PureWZ2TerminalPopularGraphPreparation localized}
    (graphParents : PureWZ2TerminalPopularGraphParentData prep)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hCpower : 10 * Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-eta))
    (hPlanarSmall : 32 * Real.rpow delta eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt delta ≤ 1)
    (habsorb : Real.rpow delta (1 - 4 * eta / sigma) ≤
      Real.sqrt delta / 14)
    (htransferSmall : 1000 * Real.sqrt delta ≤ 1)
    (hsourceVolume :
      (512 : ENNReal) * Kakeya.realRpowENN delta
          (3 / 2 + sigma / 2 + eta) ≤
        terminal.sticky.balanced.cellMass) :
    Nonempty (PureWZ2TerminalPopularFullParentLocalBinData
      (eta := eta) graphParents) := by
  let cells := prep.windowed.global.cells
  let C := pureWZ2TerminalPopularGraphConstant delta inputLoss
  have hbaseCtop :
      (10 * Kakeya.realRpowENN delta (-inputLoss) : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (by simp [Kakeya.realRpowENN])
  have hCtop : C ≠ ⊤ := by
    dsimp only [C, pureWZ2TerminalPopularGraphConstant]
    exact ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN])
  have hsourceExists : ∀ parent (hparent : parent ∈ localized.selectedParents),
      ∃ data : PureWZ2TerminalCoarseSourceData terminalSource,
        data.cell = parent := by
    intro parent hparent
    have hactive : parent ∈ terminal.sticky.balanced.activeCells :=
      weightClass.selectedParents_subset
        (selection.selected_subset_weightClass
          (localized.selected_subset hparent))
    exact terminalSource.coarseSourceAt parent hactive
  let sourceFor : ∀ parent, parent ∈ localized.selectedParents →
      PureWZ2TerminalCoarseSourceData terminalSource := fun parent hparent =>
    Classical.choose (hsourceExists parent hparent)
  have hsourceCell : ∀ parent (hparent : parent ∈ localized.selectedParents),
      (sourceFor parent hparent).cell = parent := by
    intro parent hparent
    exact Classical.choose_spec (hsourceExists parent hparent)
  have hsourceLower : ∀ parent (hparent : parent ∈ localized.selectedParents),
      Kakeya.realRpowENN delta (3 / 2 + sigma / 2 + eta) ≤
        volume (sourceFor parent hparent).coarseSource := by
    intro parent hparent
    let data := sourceFor parent hparent
    have hscaled : (512 : ENNReal) * Kakeya.realRpowENN delta
          (3 / 2 + sigma / 2 + eta) ≤
        512 * volume data.coarseSource := by
      calc
        _ ≤ terminal.sticky.balanced.cellMass := hsourceVolume
        _ = volume data.fullSource := data.fullSource_volume.symm
        _ ≤ (data.centers.card : ENNReal) * volume data.coarseSource :=
          data.volume_average
        _ ≤ 512 * volume data.coarseSource := by
          gcongr
          exact_mod_cast data.centers_card
    have h512Zero : (512 : ENNReal) ≠ 0 := by norm_num
    have h512Top : (512 : ENNReal) ≠ ⊤ := by norm_num
    apply (ENNReal.mul_le_mul_iff_left h512Zero h512Top).mp
    simpa [mul_comm] using hscaled
  have hfullNormalFirst : ∀ parent (hparent : parent ∈ localized.selectedParents),
      63 / 250 ≤ |source.localGrains.planeMap
        ⟨(sourceFor parent hparent).anchor, by
          let data := sourceFor parent hparent
          have hfull : data.anchor ∈ data.fullSource :=
            data.centers_subset data.anchor_mem
          rw [data.fullSource_eq] at hfull
          have hterminal : data.anchor ∈ terminal.sticky.refined.union := by
            rw [← terminalSource.shading_eq]
            exact hfull.1
          rcases hterminal with ⟨index, hindex⟩
          exact ⟨terminal.sticky.selected.embedding index,
            terminal.sticky.subshading index hindex⟩⟩ (0 : Fin 3)| := by
    intro parent hparent
    let data := sourceFor parent hparent
    have hfull : data.anchor ∈ data.fullSource :=
      data.centers_subset data.anchor_mem
    rw [data.fullSource_eq] at hfull
    have hterminal : data.anchor ∈ terminalSource.shading.union := hfull.1
    have hsource : data.anchor ∈ source.shading.union := by
      rw [terminalSource.shading_eq] at hterminal
      rcases hterminal with ⟨index, hindex⟩
      exact ⟨terminal.sticky.selected.embedding index,
        terminal.sticky.subshading index hindex⟩
    let normal := source.localGrains.planeMap ⟨data.anchor, hsource⟩
    have hnormalUnit : ‖normal‖ = 1 :=
      source.localGrains.planeMap_unit ⟨data.anchor, hsource⟩
    have hsourceBall : data.coarseSource ⊆
        Metric.closedBall data.anchor (Real.sqrt delta) := by
      intro point hpoint
      have h := data.coarseSource_subset hpoint
      simpa [terminal.sqrtRequested_eq] using h.2
    have hliteral := source.localGrains.local_ad delta le_rfl
      source.extremal.delta_le_one ⟨data.anchor, hsource⟩
    have hADFull : IsADSet1
        (scalarProjection normal
          (source.shading.union ∩ Metric.closedBall data.anchor
            (Real.sqrt delta)))
        delta (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss)) := by
      exact hbridge.1 _ delta (1 - sigma)
        (Kakeya.realRpowENN delta (-inputLoss))
        (scalarProjection_paperShading_subset_Icc hnormalUnit
          Set.inter_subset_left) hliteral
    have hcoarseSource : data.coarseSource ⊆
        source.shading.union ∩ Metric.closedBall data.anchor
          (Real.sqrt delta) := by
      intro point hpoint
      have hd := data.coarseSource_subset hpoint
      have hterminalPoint : point ∈ terminal.sticky.refined.union := by
        rw [← terminalSource.shading_eq]
        exact hd.1
      rcases hterminalPoint with ⟨index, hindex⟩
      exact ⟨⟨terminal.sticky.selected.embedding index,
        terminal.sticky.subshading index hindex⟩, hsourceBall hpoint⟩
    have hAD : IsADSet1 (scalarProjection normal data.coarseSource)
        delta (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss)) :=
      hADFull.mono (Set.image_mono hcoarseSource)
    rcases wz1_lemma23_projection_heavy_fiber_in_source
        (10 * Kakeya.realRpowENN delta (-inputLoss)) normal data.anchor
        data.coarseSource hnormalUnit data.coarseSource_measurable
        data.coarseSource_nonempty hsourceBall hAD source.extremal.delta_pos
        source.extremal.delta_le_one hbaseCtop with ⟨fiber⟩
    have hCOne : (1 : ENNReal) ≤
        10 * Kakeya.realRpowENN delta (-inputLoss) := hAD.2.2.2.1
    let fullInput : WZ1Lemma23FullLocalGrainInputGeneralized
        delta sigma eta (10 * Kakeya.realRpowENN delta (-inputLoss))
        source.globalGrains.slope :=
      { grain := fiber.grain
        grain_measurable := fiber.grain_measurable
        grain_finite := fiber.grain_finite
        heightLeft := data.heightLeft
        grain_height := by
          intro point hpoint
          simpa [terminal.sqrtRequested_eq] using
            data.source_height point (fiber.grain_in_source hpoint)
        grain_volume := fiber.grain_volume_of_source_lower
          source.extremal.delta_pos hCOne hCpower (hsourceLower parent hparent)
        center := data.anchor
        normal := normal
        localProjectionCenter := fiber.center
        normal_unit := hnormalUnit
        normal_vertical := source.planeMap_vertical_bound ⟨data.anchor, hsource⟩
        grain_square := fiber.grain_square
        grain_local_strip := fiber.grain_local_strip
        slope_small := by
          intro z hz
          exact source.globalGrains.slope_bound z (data.height_window (by
            simpa [terminal.sqrtRequested_eq] using hz))
        projected := fun z => scalarProjection
          (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice prepared.shadow.union z)
        globalAD := by
          intro z hz
          exact prepared.exactAD z (data.height_window (by
            simpa [terminal.sqrtRequested_eq] using hz))
        global_projection_sub := by
          intro z _hz
          rintro value ⟨point, hpoint, rfl⟩
          have hlift : point3 (point 0) (point 1) z ∈ fiber.grain :=
            wz1Lemma23_mem_planarSlice_iff.mp hpoint
          have hcoarse := fiber.grain_in_source hlift
          have hterminalPoint := (data.coarseSource_subset hcoarse).1
          have hprepared : point3 (point 0) (point 1) z ∈
              prepared.shadow.union := by
            rw [prepared.shadow_union]
            exact hterminalPoint
          refine ⟨point3 (point 0) (point 1) z,
            ⟨hprepared, by simp [point3]⟩, ?_⟩
          change inner ℝ (point3 (point 0) (point 1) z)
              (globalGrainDirection (source.globalGrains.slope z)) =
            point 0 + source.globalGrains.slope z * point 1
          rw [PiLp.inner_apply]
          simp [Fin.sum_univ_succ, globalGrainDirection, point3] }
    simpa [normal, fullInput] using
      pureWZ2_full_grain_normal_first_component_generalized_margin
        delta sigma eta (10 * Kakeya.realRpowENN delta (-inputLoss))
        source.globalGrains.slope source.extremal.delta_pos
        source.extremal.delta_le_one hsigma hsigmaOne heta hetaSigma
        hbaseCtop hCpower hPlanarSmall hrootSmall20 habsorb fullInput
  have hpopularNormalFirst :
      ∀ cell (hcell : cell ∈ cells),
        1 / 4 ≤ |prep.localGrains.planeMap
          (graphParents.anchorFor cell hcell) (0 : Fin 3)| := by
    intro cell hcell
    let parent := graphParents.parentOf cell
    let hparent : parent ∈ localized.selectedParents :=
      graphParents.parent_mem cell hcell
    let data := sourceFor parent hparent
    let popularAnchor := graphParents.anchorFor cell hcell
    have hfull : data.anchor ∈ data.fullSource :=
      data.centers_subset data.anchor_mem
    rw [data.fullSource_eq] at hfull
    have hfullParent : data.anchor ∈
        wz1PaperGridCube terminal.sqrtRequested.1 parent := by
      simpa only [data, hsourceCell parent hparent] using hfull.2
    have hpopularParent : popularAnchor ∈
        wz1PaperGridCube terminal.sqrtRequested.1 parent := by
      exact graphParents.anchorFor_mem_parent cell hcell
    have hanchorDist : dist data.anchor popularAnchor <
        2 * terminal.sqrtRequested.1 :=
      wz1_paper_grid_cube_diameter_lt_two_rho
        terminal.sticky.coarse_extremal.delta_pos hfullParent hpopularParent
    have hfullSource : data.anchor ∈ source.shading.union := by
      have hterminal : data.anchor ∈ terminal.sticky.refined.union := by
        rw [← terminalSource.shading_eq]
        exact hfull.1
      rcases hterminal with ⟨index, hindex⟩
      exact ⟨terminal.sticky.selected.embedding index,
        terminal.sticky.subshading index hindex⟩
    have hpopularShadow : popularAnchor ∈ prep.shadow.union :=
      graphParents.anchorFor_mem_shadow cell hcell
    have hpopularSource : popularAnchor ∈ source.shading.union :=
      prep.shadow_source hpopularShadow
    let fullNormal := source.localGrains.planeMap ⟨data.anchor, hfullSource⟩
    let popularNormal := source.localGrains.planeMap
      ⟨popularAnchor, hpopularSource⟩
    have hnormalDist : dist fullNormal popularNormal ≤
        dist data.anchor popularAnchor := by
      have h := source.localGrains.planeMap_lipschitz.dist_le_mul
        ⟨data.anchor, hfullSource⟩ ⟨popularAnchor, hpopularSource⟩
      simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using h
    have hcoord : |fullNormal 0 - popularNormal 0| ≤
        dist fullNormal popularNormal := by
      have h := PiLp.norm_apply_le (fullNormal - popularNormal) (0 : Fin 3)
      simpa [dist_eq_norm, Real.norm_eq_abs] using h
    have hnormalClose : |fullNormal 0 - popularNormal 0| ≤ 1 / 500 := by
      apply hcoord.trans (hnormalDist.trans (le_of_lt hanchorDist)) |>.trans
      rw [terminal.sqrtRequested_eq]
      nlinarith [Real.sqrt_nonneg delta]
    have hfullFirst : 63 / 250 ≤ |fullNormal 0| := by
      simpa [fullNormal, data, parent, hparent] using
        hfullNormalFirst parent hparent
    have habsTriangle : |fullNormal 0| ≤
        |popularNormal 0| + |fullNormal 0 - popularNormal 0| := by
      calc
        |fullNormal 0| =
            |(fullNormal 0 - popularNormal 0) + popularNormal 0| := by ring_nf
        _ ≤ _ := by
          simpa [add_comm] using
            abs_add_le (fullNormal 0 - popularNormal 0) (popularNormal 0)
    have hpopularFirst : 1 / 4 ≤ |popularNormal 0| := by linarith
    rw [prep.planeMap_eq_on_source ⟨popularAnchor, hpopularShadow⟩]
    exact hpopularFirst
  let sample : Finset ℝ := cells.image fun cell =>
    wz1Lemma23SnappedYValue delta cell.2.1
  have hcellExists : ∀ y (hy : y ∈ sample),
      ∃ cell ∈ cells, wz1Lemma23SnappedYValue delta cell.2.1 = y := by
    intro y hy
    simpa [sample] using Finset.mem_image.mp hy
  let cellFor : ∀ y, y ∈ sample → ℤ × ℤ × ℤ := fun y hy =>
    Classical.choose (hcellExists y hy)
  have hcellForMem : ∀ y (hy : y ∈ sample), cellFor y hy ∈ cells := by
    intro y hy
    exact (Classical.choose_spec (hcellExists y hy)).1
  have hcellForValue : ∀ y (hy : y ∈ sample),
      wz1Lemma23SnappedYValue delta (cellFor y hy).2.1 = y := by
    intro y hy
    exact (Classical.choose_spec (hcellExists y hy)).2
  let anchor : ℝ → Point3 := fun y => if hy : y ∈ sample then
    graphParents.anchorFor (cellFor y hy) (hcellForMem y hy) else 0
  have hanchorEq : ∀ y (hy : y ∈ sample), anchor y =
      graphParents.anchorFor (cellFor y hy) (hcellForMem y hy) := by
    intro y hy
    simp [anchor, hy]
  have hanchorMem : ∀ y (hy : y ∈ sample), anchor y ∈ prep.shadow.union := by
    intro y hy
    rw [hanchorEq y hy]
    exact graphParents.anchorFor_mem_shadow _ _
  have hvertical : ∀ y ∈ sample,
      |prep.localGrains.planeMap (anchor y) (2 : Fin 3)| ≤ 1 / 2 := by
    intro y hy
    exact prep.planeMap_vertical_bound (anchor y) (hanchorMem y hy)
  have hfirst : ∀ y ∈ sample,
      1 / 4 ≤ |prep.localGrains.planeMap (anchor y) (0 : Fin 3)| := by
    intro y hy
    rw [hanchorEq y hy]
    exact hpopularNormalFirst (cellFor y hy) (hcellForMem y hy)
  have hnormalDist : ∀ y₁ (hy₁ : y₁ ∈ sample),
      ∀ y₂ (hy₂ : y₂ ∈ sample),
        dist (prep.localGrains.planeMap (anchor y₁))
            (prep.localGrains.planeMap (anchor y₂)) ≤
          dist (anchor y₁) (anchor y₂) := by
    intro y₁ hy₁ y₂ hy₂
    rw [prep.planeMap_eq_on_paper ⟨anchor y₁, hanchorMem y₁ hy₁⟩]
    rw [prep.planeMap_eq_on_paper ⟨anchor y₂, hanchorMem y₂ hy₂⟩]
    have hlip := prep.localPaper.planeMap_lipschitz.dist_le_mul
      ⟨anchor y₁, by
        rw [← prep.ambient_union]
        exact prep.subshading.union_subset (hanchorMem y₁ hy₁)⟩
      ⟨anchor y₂, by
        rw [← prep.ambient_union]
        exact prep.subshading.union_subset (hanchorMem y₂ hy₂)⟩
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using hlip
  have hanchorDist : ∀ y₁ (hy₁ : y₁ ∈ sample),
      ∀ y₂ (hy₂ : y₂ ∈ sample),
        dist (anchor y₁) (anchor y₂) ≤ 4 * |y₁ - y₂| := by
    intro y₁ hy₁ y₂ hy₂
    rw [hanchorEq y₁ hy₁, hanchorEq y₂ hy₂]
    simpa [hcellForValue y₁ hy₁, hcellForValue y₂ hy₂] using
      graphParents.anchorFor_dist (cellFor y₁ hy₁) (hcellForMem y₁ hy₁)
        (cellFor y₂ hy₂) (hcellForMem y₂ hy₂)
  rcases wz1_lemma23_local_graph_extension_of_distortion sample anchor
      prep.localGrains.planeMap hvertical hfirst hnormalDist hanchorDist with
    ⟨g, hgLipschitz, hgBounded, hgAnchor⟩
  have hySample : ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      wz1Lemma23SnappedYValue delta y ∈ sample := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨cell, hcell, hcellY⟩
    exact Finset.mem_image.mpr ⟨cell, hcell,
      congrArg (wz1Lemma23SnappedYValue delta) hcellY⟩
  have hlayerBall : ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      ∀ idx (hidx : idx ∈ cells), idx.2.1 = y →
        dist (wz1Lemma23CellRepresentative prep.shadow
          source.extremal.delta_pos ⟨idx, prep.windowed.global.cells_active hidx⟩)
          (anchor (wz1Lemma23SnappedYValue delta y)) ≤ Real.sqrt delta := by
    intro y hy idx hidx hidxY
    let value := wz1Lemma23SnappedYValue delta y
    have hs := hySample y hy
    let chosen := cellFor value hs
    have hchosenMem : chosen ∈ cells := hcellForMem value hs
    have hchosenYValue : wz1Lemma23SnappedYValue delta chosen.2.1 =
        wz1Lemma23SnappedYValue delta y := by
      simpa [value] using hcellForValue value hs
    have hchosenY : chosen.2.1 = y :=
      wz1Lemma23SnappedYValue_injective source.extremal.delta_pos hchosenYValue
    have hparent : graphParents.parentOf chosen = graphParents.parentOf idx :=
      graphParents.same_y_parent chosen hchosenMem idx hidx
        (hchosenY.trans hidxY.symm)
    have hanchorSame : graphParents.anchorFor chosen hchosenMem =
        graphParents.anchorFor idx hidx := by
      simp only [PureWZ2TerminalPopularGraphParentData.anchorFor, hparent]
    rw [hanchorEq value hs, hanchorSame]
    exact graphParents.canonical_rep_dist_anchor idx hidx
  have hgraph : ∀ y ∈ wz1Lemma23SnappedYLayers cells,
      g (wz1Lemma23SnappedYValue delta y) =
        prep.localGrains.planeMap
          (anchor (wz1Lemma23SnappedYValue delta y)) (2 : Fin 3) /
        prep.localGrains.planeMap
          (anchor (wz1Lemma23SnappedYValue delta y)) (0 : Fin 3) := by
    intro y hy
    exact hgAnchor _ (hySample y hy)
  let X : ENNReal := 19 * C * Kakeya.realRpowENN
    (Real.sqrt delta / delta) (1 - sigma)
  let localBinBound : ℕ := Nat.ceil X.toReal + 1
  have hlocalBins : ∀ y ∈ wz1Lemma23SnappedYLayers cells,
      (wz1Lemma23SnappedLocalBinsAt delta g cells y).card ≤ localBinBound := by
    intro y hy
    have hbins := wz1_lemma23_actual_local_bins_at
      prep.shadow C prep.localGrains cells g
      (fun y => anchor (wz1Lemma23SnappedYValue delta y))
      source.extremal.delta_pos le_rfl source.extremal.delta_le_one
      prep.windowed.global.cells_active
      (fun y hy => hanchorMem _ (hySample y hy))
      (fun y hy => hvertical _ (hySample y hy))
      (fun y hy => hfirst _ (hySample y hy)) hgraph hlayerBall y hy
    exact pureWZ2_terminalPopular_nat_le_ceil_add_one
      (by
        dsimp only [X, C, pureWZ2TerminalPopularGraphConstant]
        exact ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num) hCtop)
          (by simp [Kakeya.realRpowENN]))
      (by simpa [X] using hbins)
  let localBins : WZ1Lemma23LocalBinPackage
      (rho := delta) (sigma := sigma) C cells :=
    { g := g
      g_lipschitz := hgLipschitz
      g_bounded := hgBounded
      localBinBound := localBinBound
      localBinBound_eq := rfl
      local_bins := hlocalBins }
  exact ⟨{ localBins := localBins, normal_first := hpopularNormalFirst }⟩

end Kakeya.Assouad

end
