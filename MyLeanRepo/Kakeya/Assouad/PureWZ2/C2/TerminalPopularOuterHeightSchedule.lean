import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularOuterHeightLift
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalGlobalBinGoodFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.BoundedGridLogCost

/-!
# Uniform scalar schedule for the terminal outer-height refill

The source terminal window has only `O(delta⁻¹/²)` occupied height layers.
After paying the one outer height-popularity logarithm, any local loss strictly
larger than half of the Alternative-A output loss absorbs that count into the
twice-normalized rich-height floor.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The outer volume-popular heights stay in the original terminal window and
hence obey its `O(delta⁻¹/²)` occupied-height bound. -/
theorem PureWZ2TerminalWindowHeightPopularData.popular_heights_le_window_cap
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    (data : PureWZ2TerminalWindowHeightPopularData window) :
    (data.popular.heightIndices.card : ENNReal) ≤
      ENNReal.ofReal (3 / Real.sqrt delta) := by
  have hsubset : data.popular.heightIndices ⊆
      wz1Lemma23SnappedHeights data.graphWindow.windowed.global.cells := by
    intro heightIndex hheight
    have hglobal : heightIndex ∈
        data.graphWindow.windowed.global.heightIndices := by
      rw [data.graphWindow.windowed.global.heightIndices_eq]
      exact data.popular.heightIndices_subset hheight
    have hsliceEq :
        data.graphWindow.shading.union ∩
              wz1Lemma23HeightSlab delta heightIndex =
          window.shading.union ∩
              wz1Lemma23HeightSlab delta heightIndex := by
      rw [data.graphWindow_shading, data.popular.union_eq]
      ext point
      constructor
      · rintro ⟨⟨hwindow, _hregion⟩, hslab⟩
        exact ⟨hwindow, hslab⟩
      · rintro ⟨hwindow, hslab⟩
        refine ⟨⟨hwindow, ?_⟩, hslab⟩
        rw [data.popular.heightRegion_eq]
        exact Set.mem_iUnion₂.mpr ⟨heightIndex, hheight, hslab⟩
    have hlayerNonempty :
        (data.graphWindow.windowed.global.layerCells heightIndex).Nonempty := by
      have hlayerPos : 0 < volume
          (data.graphWindow.shading.union ∩
            wz1Lemma23HeightSlab delta heightIndex) := by
        rw [hsliceEq]
        exact data.popular.layerMass_pos.trans_le
          (data.popular.layer_volume_band heightIndex hheight).1
      by_contra hempty
      have hlayerEmpty := Finset.not_nonempty_iff_eq_empty.mp hempty
      have hbound := data.graphWindow.windowed.global.layer_volume_bound
        heightIndex hglobal
      have harea := wz1_lemma23_exactSlice_area_le_two
        data.graphWindow.shading source.extremal.delta_pos
        (by
          intro point hpoint
          have hprepared := data.graphWindow.subshading.union_subset hpoint
          have hpaper : point ∈ terminalSource.shading.union := by
            rwa [prepared.shadow_union] at hprepared
          have hnorm := norm_le_two_of_mem_paperShading hpaper
          simpa [Metric.mem_closedBall, dist_zero_right] using hnorm)
        (data.graphWindow.windowed.global.selectedHeight heightIndex)
      rw [← data.graphWindow.windowed.global.layerCells_eq heightIndex,
        hlayerEmpty] at harea
      norm_num at harea
      have hsidePos : 0 < ENNReal.ofReal (gridSide (delta / 2)) := by
        apply ENNReal.ofReal_pos.mpr
        dsimp [gridSide]
        apply div_pos
        · nlinarith [source.extremal.delta_pos]
        · exact Real.sqrt_pos.mpr (by norm_num)
      have hzero : volume
          (data.graphWindow.shading.union ∩
            wz1Lemma23HeightSlab delta heightIndex) = 0 := by
        apply le_zero_iff.mp
        have hdiv : volume
              (data.graphWindow.shading.union ∩
                wz1Lemma23HeightSlab delta heightIndex) /
              ENNReal.ofReal (gridSide (delta / 2)) ≤ 0 :=
          hbound.trans harea.le
        have hmul := (ENNReal.div_le_iff hsidePos.ne'
          ENNReal.ofReal_ne_top).mp hdiv
        simpa using hmul
      exact (ne_of_gt hlayerPos) hzero
    rcases hlayerNonempty with ⟨cell, hcell⟩
    have hcellGlobal : cell ∈
        data.graphWindow.windowed.global.cells := by
      rw [data.graphWindow.windowed.global.cells_eq]
      exact Finset.mem_biUnion.mpr ⟨heightIndex, hglobal, hcell⟩
    exact Finset.mem_image.mpr ⟨cell, hcellGlobal,
      data.graphWindow.windowed.global.layer_height
        heightIndex hglobal cell hcell⟩
  have hreal := wz1Lemma23_height_layer_count
    source.extremal.delta_pos source.extremal.delta_le_one
    data.graphWindow.windowed.global_cells_window
  have hcardReal : (data.popular.heightIndices.card : ℝ) ≤
      3 / Real.sqrt delta := by
    have hcast : (data.popular.heightIndices.card : ℝ) ≤
        ((wz1Lemma23SnappedHeights
          data.graphWindow.windowed.global.cells).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    exact hcast.trans hreal
  exact (ENNReal.natCast_le_ofReal
    data.popular.heightIndices_nonempty.card_ne_zero).mpr hcardReal

/-- Uniformly absorb the outer height count and its one dyadic logarithm into
the twice-normalized Alternative-A rich-height floor. -/
theorem pureWZ2_terminalPopular_outerHeight_schedule
    {epsilon localMassLoss : ℝ}
    (hepsilonOne : epsilon < 1)
    (hgap : epsilon / 2 < localMassLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sigma inputLoss delta stickyLoss : ℝ}
        {logExponent : ℕ}
        {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
        {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
        {terminalSource : PureWZ2TerminalPreparedSource source terminal}
        {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
        {window : PureWZ2TerminalWindow prepared}
        (data : PureWZ2TerminalWindowHeightPopularData window),
        0 < delta → delta ≤ delta₀ →
          16 * Kakeya.realRpowENN delta localMassLoss *
              (data.popular.bins : ENNReal) *
              (data.popular.heightIndices.card : ENNReal) ≤
            pureWZ2TerminalPopularRichFloor delta epsilon := by
  let gap := localMassLoss - epsilon / 2
  have hgapPos : 0 < gap := by dsimp only [gap]; linarith
  rcases log_poly_decay_general 1104 gap (by norm_num) hgapPos with
    ⟨delta₀, hdelta₀, hdelta₀One, habsorb⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro sigma inputLoss delta stickyLoss logExponent source terminal
    terminalSource prepared window data hdelta hdeltaSmall
  have hdeltaOne : delta ≤ 1 := hdeltaSmall.trans hdelta₀One
  have hbins := data.bins_real_le_log
  have hcostReal : ((48 * data.popular.bins : ℕ) : ℝ) ≤
      Real.rpow delta (-gap) := by
    calc
      ((48 * data.popular.bins : ℕ) : ℝ) ≤
          1104 * (Real.log (1 / delta) + 1) := by
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        nlinarith
      _ ≤ 1 / delta ^ gap := habsorb delta hdelta hdeltaSmall
      _ = Real.rpow delta (-gap) := by
        simpa [one_div] using (Real.rpow_neg hdelta.le gap).symm
  have hcostENN : (48 * data.popular.bins : ENNReal) ≤
      Kakeya.realRpowENN delta (-gap) := by
    calc
      (48 * data.popular.bins : ENNReal) =
          ENNReal.ofReal (((48 * data.popular.bins : ℕ) : ℝ)) := by simp
      _ ≤ ENNReal.ofReal (Real.rpow delta (-gap)) :=
        ENNReal.ofReal_mono hcostReal
      _ = Kakeya.realRpowENN delta (-gap) := rfl
  have hcostAbsorb : (48 * data.popular.bins : ENNReal) *
      Kakeya.realRpowENN delta gap ≤ 1 := by
    calc
      _ ≤ Kakeya.realRpowENN delta (-gap) *
          Kakeya.realRpowENN delta gap := by gcongr
      _ = Kakeya.realRpowENN delta ((-gap) + gap) :=
        (realRpowENN_add hdelta (-gap) gap).symm
      _ = 1 := by simp [Kakeya.realRpowENN]
  have hheight := data.popular_heights_le_window_cap
  have hsqrtInv : ENNReal.ofReal (3 / Real.sqrt delta) =
      3 * Kakeya.realRpowENN delta (-1 / 2) := by
    have hsqrtEq : Real.sqrt delta =
        Real.rpow delta (1 / 2 : ℝ) := Real.sqrt_eq_rpow delta
    have hreal : 3 / Real.sqrt delta =
        3 * Real.rpow delta (-1 / 2) := by
      calc
        3 / Real.sqrt delta = 3 * (Real.sqrt delta)⁻¹ := by ring
        _ = 3 * (Real.rpow delta (1 / 2))⁻¹ := by
          rw [hsqrtEq]
        _ = 3 * Real.rpow delta (-(1 / 2)) :=
          congrArg (fun value : ℝ => 3 * value)
            (Real.rpow_neg hdelta.le (1 / 2 : ℝ)).symm
        _ = 3 * Real.rpow delta (-1 / 2) := by
          congr 2
          ring
    rw [hreal, ENNReal.ofReal_mul (by norm_num)]
    norm_num [Kakeya.realRpowENN]
  have hsourceBound :
      16 * Kakeya.realRpowENN delta localMassLoss *
          (data.popular.bins : ENNReal) *
          (data.popular.heightIndices.card : ENNReal) ≤
        (48 * data.popular.bins : ENNReal) *
          Kakeya.realRpowENN delta
            (gap + (epsilon - 1) / 2) := by
    calc
      _ ≤ 16 * Kakeya.realRpowENN delta localMassLoss *
          (data.popular.bins : ENNReal) *
          ENNReal.ofReal (3 / Real.sqrt delta) := by gcongr
      _ = (48 * data.popular.bins : ENNReal) *
          (Kakeya.realRpowENN delta localMassLoss *
            Kakeya.realRpowENN delta (-1 / 2)) := by
        rw [hsqrtInv]
        push_cast
        ring
      _ = (48 * data.popular.bins : ENNReal) *
          Kakeya.realRpowENN delta (localMassLoss - 1 / 2) := by
        rw [← realRpowENN_add hdelta]
        congr 2
        ring
      _ = (48 * data.popular.bins : ENNReal) *
          Kakeya.realRpowENN delta
            (gap + (epsilon - 1) / 2) := by
        congr 2
        dsimp only [gap]
        ring
  have hpowerSplit : Kakeya.realRpowENN delta
        (gap + (epsilon - 1) / 2) =
      Kakeya.realRpowENN delta gap *
        Kakeya.realRpowENN delta ((epsilon - 1) / 2) :=
    realRpowENN_add hdelta gap ((epsilon - 1) / 2)
  have hbaseFloor : Kakeya.realRpowENN delta ((epsilon - 1) / 2) ≤
      pureWZ2TerminalPopularRichFloor delta epsilon := by
    apply ENNReal.ofReal_mono
    have hscalePos : 0 < wz1Lemma23Theorem22Scale (delta / 625) := by
      dsimp only [wz1Lemma23Theorem22Scale]
      positivity
    have hscaleLe : wz1Lemma23Theorem22Scale (delta / 625) ≤
        Real.sqrt delta := by
      have hscaleEq : wz1Lemma23Theorem22Scale (delta / 625) =
          Real.sqrt delta / (125 * Real.sqrt 3) := by
        rw [wz1Lemma23Theorem22Scale, Real.sqrt_div hdelta.le]
        norm_num
        ring
      rw [hscaleEq]
      have hdenom : 1 ≤ 125 * Real.sqrt 3 := by
        have hsqrt : 1 ≤ Real.sqrt 3 := Real.one_le_sqrt.mpr (by norm_num)
        nlinarith
      exact div_le_self (Real.sqrt_nonneg delta) hdenom
    have hroot : Real.rpow (Real.sqrt delta) (epsilon - 1) ≤
        Real.rpow (wz1Lemma23Theorem22Scale (delta / 625))
          (epsilon - 1) :=
      Real.rpow_le_rpow_of_nonpos hscalePos hscaleLe (by linarith)
    have hrootEq : Real.rpow (Real.sqrt delta) (epsilon - 1) =
        Real.rpow delta ((epsilon - 1) / 2) := by
      have hsqrtEq : Real.sqrt delta =
          Real.rpow delta (1 / 2 : ℝ) := Real.sqrt_eq_rpow delta
      calc
        Real.rpow (Real.sqrt delta) (epsilon - 1) =
            Real.rpow (Real.rpow delta (1 / 2)) (epsilon - 1) := by
          rw [hsqrtEq]
        _ = Real.rpow delta ((1 / 2) * (epsilon - 1)) :=
          (Real.rpow_mul hdelta.le (1 / 2) (epsilon - 1)).symm
        _ = Real.rpow delta ((epsilon - 1) / 2) := by
          congr 1
          ring
    rw [← hrootEq]
    exact hroot
  calc
    16 * Kakeya.realRpowENN delta localMassLoss *
          (data.popular.bins : ENNReal) *
          (data.popular.heightIndices.card : ENNReal) ≤
        (48 * data.popular.bins : ENNReal) *
          Kakeya.realRpowENN delta
            (gap + (epsilon - 1) / 2) := hsourceBound
    _ = ((48 * data.popular.bins : ENNReal) *
          Kakeya.realRpowENN delta gap) *
        Kakeya.realRpowENN delta ((epsilon - 1) / 2) := by
      rw [hpowerSplit]
      ring
    _ ≤ Kakeya.realRpowENN delta ((epsilon - 1) / 2) := by
      simpa using mul_le_mul_right' hcostAbsorb
        (Kakeya.realRpowENN delta ((epsilon - 1) / 2))
    _ ≤ pureWZ2TerminalPopularRichFloor delta epsilon := hbaseFloor

/-- The graph-current volume-popular heights remain in the outer-popular
graph's one-window global cell package. -/
theorem PureWZ2TerminalPopularPreparedGraphData.popular_heights_le_window_cap
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
    {graphParents : PureWZ2TerminalPopularGraphParentData prep}
    {localCells : PureWZ2TerminalPopularLocalCellData
      (eta := eta) graphParents}
    (data : PureWZ2TerminalPopularPreparedGraphData localCells) :
    (data.heightPopular.heightIndices.card : ENNReal) ≤
      ENNReal.ofReal (3 / Real.sqrt delta) := by
  have hsubset : data.heightPopular.heightIndices ⊆
      wz1Lemma23SnappedHeights prep.windowed.global.cells := by
    intro heightIndex hheight
    have hglobal : heightIndex ∈ prep.windowed.global.heightIndices := by
      rw [prep.windowed.global.heightIndices_eq]
      exact data.heightPopular.heightIndices_subset hheight
    have hlayerNonempty :
        (prep.windowed.global.layerCells heightIndex).Nonempty := by
      have hlayerPos : 0 < volume
          (prep.shadow.union ∩ wz1Lemma23HeightSlab delta heightIndex) :=
        data.heightPopular.layerMass_pos.trans_le
          (data.heightPopular.layer_volume_band heightIndex hheight).1
      by_contra hempty
      have hlayerEmpty := Finset.not_nonempty_iff_eq_empty.mp hempty
      have hbound := prep.windowed.global.layer_volume_bound
        heightIndex hglobal
      have harea := wz1_lemma23_exactSlice_area_le_two prep.shadow
        source.extremal.delta_pos
        (by
          intro point hpoint
          have hsource := prep.shadow_source hpoint
          have hnorm := norm_le_two_of_mem_paperShading hsource
          simpa [Metric.mem_closedBall, dist_zero_right] using hnorm)
        (prep.windowed.global.selectedHeight heightIndex)
      rw [← prep.windowed.global.layerCells_eq heightIndex, hlayerEmpty]
        at harea
      norm_num at harea
      have hsidePos : 0 < ENNReal.ofReal (gridSide (delta / 2)) := by
        apply ENNReal.ofReal_pos.mpr
        dsimp [gridSide]
        apply div_pos
        · nlinarith [source.extremal.delta_pos]
        · exact Real.sqrt_pos.mpr (by norm_num)
      have hzero : volume
          (prep.shadow.union ∩ wz1Lemma23HeightSlab delta heightIndex) = 0 := by
        apply le_zero_iff.mp
        have hdiv : volume
              (prep.shadow.union ∩ wz1Lemma23HeightSlab delta heightIndex) /
              ENNReal.ofReal (gridSide (delta / 2)) ≤ 0 :=
          hbound.trans harea.le
        have hmul := (ENNReal.div_le_iff hsidePos.ne'
          ENNReal.ofReal_ne_top).mp hdiv
        simpa using hmul
      exact (ne_of_gt hlayerPos) hzero
    rcases hlayerNonempty with ⟨cell, hcell⟩
    have hcellGlobal : cell ∈ prep.windowed.global.cells := by
      rw [prep.windowed.global.cells_eq]
      exact Finset.mem_biUnion.mpr ⟨heightIndex, hglobal, hcell⟩
    exact Finset.mem_image.mpr ⟨cell, hcellGlobal,
      prep.windowed.global.layer_height heightIndex hglobal cell hcell⟩
  have hreal := wz1Lemma23_height_layer_count
    source.extremal.delta_pos source.extremal.delta_le_one
    prep.windowed.global_cells_window
  have hcardReal : (data.heightPopular.heightIndices.card : ℝ) ≤
      3 / Real.sqrt delta := by
    have hcast : (data.heightPopular.heightIndices.card : ℝ) ≤
        ((wz1Lemma23SnappedHeights
          prep.windowed.global.cells).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    exact hcast.trans hreal
  exact (ENNReal.natCast_le_ofReal
    data.heightPopular.heightIndices_nonempty.card_ne_zero).mpr hcardReal

/-- The graph-current height popularity has a logarithmic number of dyadic
classes, uniformly over every dependent outer-popular graph. -/
theorem PureWZ2TerminalPopularPreparedGraphData.height_bins_real_le_log
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
    {graphParents : PureWZ2TerminalPopularGraphParentData prep}
    {localCells : PureWZ2TerminalPopularLocalCellData
      (eta := eta) graphParents}
    (data : PureWZ2TerminalPopularPreparedGraphData localCells) :
    (data.heightPopular.bins : ℝ) ≤
      23 * (Real.log (1 / delta) + 1) := by
  have hdelta := source.extremal.delta_pos
  have hdeltaOne := source.extremal.delta_le_one
  have hheightCard :
      (wz1Lemma23BoundedHeightIndices delta hdelta).card ≤
        (wz1Lemma23BoundedCells delta hdelta).card :=
    Finset.card_image_le
  have hheightNonempty :
      (wz1Lemma23BoundedHeightIndices delta hdelta).Nonempty :=
    data.heightPopular.heightIndices_nonempty.mono
      data.heightPopular.heightIndices_subset
  have hcellsNonempty :
      (wz1Lemma23BoundedCells delta hdelta).Nonempty := by
    simpa [wz1Lemma23BoundedHeightIndices] using hheightNonempty
  have hbinsArg :
      2 * (wz1Lemma23BoundedHeightIndices delta hdelta).card ≤
        4 * (wz1Lemma23BoundedCells delta hdelta).card := by
    have hcellsPos : 0 < (wz1Lemma23BoundedCells delta hdelta).card :=
      hcellsNonempty.card_pos
    omega
  have hbinsLog :
      Nat.log 2 (2 * (wz1Lemma23BoundedHeightIndices delta hdelta).card) ≤
        Nat.log 2 (4 * (wz1Lemma23BoundedCells delta hdelta).card) :=
    Nat.log_mono_right hbinsArg
  have hcellsNe : (wz1Lemma23BoundedCells delta hdelta).card ≠ 0 :=
    hcellsNonempty.card_ne_zero
  have hfourEq :
      4 * (wz1Lemma23BoundedCells delta hdelta).card =
        (wz1Lemma23BoundedCells delta hdelta).card * 2 * 2 := by
    ring
  have hbinsNat : data.heightPopular.bins ≤
      Nat.log 2 (wz1Lemma23BoundedCells delta hdelta).card + 3 := by
    rw [data.heightPopular.bins_eq]
    calc
      Nat.log 2
          (2 * (wz1Lemma23BoundedHeightIndices delta hdelta).card) + 1 ≤
          Nat.log 2
            (4 * (wz1Lemma23BoundedCells delta hdelta).card) + 1 := by
        omega
      _ = Nat.log 2 (wz1Lemma23BoundedCells delta hdelta).card + 3 := by
        rw [hfourEq]
        calc
          Nat.log 2
                ((wz1Lemma23BoundedCells delta hdelta).card * 2 * 2) + 1 =
              Nat.log 2
                ((wz1Lemma23BoundedCells delta hdelta).card * 2) + 1 + 1 := by
            rw [Nat.log_mul_base (by omega)
              (Nat.mul_ne_zero hcellsNe (by omega))]
          _ = Nat.log 2 (wz1Lemma23BoundedCells delta hdelta).card +
                1 + 1 + 1 := by
            rw [Nat.log_mul_base (by omega) hcellsNe]
          _ = _ := by omega
  let L : ℝ := Real.log (1 / delta) + 1
  have hlog := wz1Lemma23BoundedCells_log_bound hdelta hdeltaOne
  have hLone : 1 ≤ L := by
    dsimp only [L]
    have hlogNonneg : 0 ≤ Real.log (1 / delta) := by
      apply Real.log_nonneg
      exact one_le_one_div hdelta hdeltaOne
    linarith
  have hnat : (data.heightPopular.bins : ℝ) ≤
      (Nat.log 2 (wz1Lemma23BoundedCells delta hdelta).card + 3 : ℕ) := by
    exact_mod_cast hbinsNat
  calc
    (data.heightPopular.bins : ℝ) ≤
        (Nat.log 2 (wz1Lemma23BoundedCells delta hdelta).card + 3 : ℕ) :=
      hnat
    _ ≤ 20 * L + 2 := by
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      linarith [hlog]
    _ ≤ 23 * L := by nlinarith

/-- The two finite regularizations in the outer-popular prepared graph have
uniformly polylogarithmic cost, hence are absorbed by any prescribed positive
power loss. -/
theorem pureWZ2_terminalPopular_extraCost_schedule
    {extraLoss : ℝ} (hextraLoss : 0 < extraLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sigma inputLoss delta stickyLoss eta : ℝ}
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
        {graphParents : PureWZ2TerminalPopularGraphParentData prep}
        {localCells : PureWZ2TerminalPopularLocalCellData
          (eta := eta) graphParents}
        (data : PureWZ2TerminalPopularPreparedGraphData localCells),
        0 < delta → delta ≤ delta₀ →
          (data.graph.residue.extraCost : ℝ) ≤
            Real.rpow delta (-extraLoss) := by
  rcases pureWZ2_boundedGrid_logCost_schedule hextraLoss with
    ⟨delta₀, hdelta₀, hdelta₀One, hschedule⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro sigma inputLoss delta stickyLoss eta logExponent source terminal
    terminalSource prepared window heightData carrier weightClass restricted
    restrictedPrepared line parents selection selectedCarrier sources localized
    prep graphParents localCells data hdelta hdeltaSmall
  have hdeltaOne : delta ≤ 1 := hdeltaSmall.trans hdelta₀One
  have hcellsSubset : prep.windowed.global.cells ⊆
      wz1Lemma23BoundedCells delta hdelta := by
    classical
    exact prep.windowed.global.cells_active.trans (Finset.filter_subset _ _)
  have hcard : prep.windowed.global.cells.card ≤
      (wz1Lemma23BoundedCells delta hdelta).card :=
    Finset.card_le_card hcellsSubset
  have hrawCard : data.rawResidue.cells.card ≤
      (wz1Lemma23BoundedCells delta hdelta).card :=
    (Finset.card_le_card data.rawResidue.cells_subset).trans hcard
  have hrawNonempty : data.rawResidue.cells.Nonempty := by
    rw [data.raw_residue_eq]
    exact data.popularSource.cells_nonempty
  have hboundedNonempty :
      (wz1Lemma23BoundedCells delta hdelta).Nonempty :=
    hrawNonempty.mono (data.rawResidue.cells_subset.trans hcellsSubset)
  have hrawLogNat : Nat.log 2 data.rawResidue.cells.card + 1 ≤
      Nat.log 2 (wz1Lemma23BoundedCells delta hdelta).card + 1 :=
    Nat.add_le_add_right (Nat.log_mono_right hrawCard) 1
  let L : ℝ := Real.log (1 / delta) + 1
  have hlog := wz1Lemma23BoundedCells_log_bound hdelta hdeltaOne
  have hrawLogReal :
      (Nat.log 2 data.rawResidue.cells.card + 1 : ℝ) ≤ 20 * L := by
    have hcast :
        (Nat.log 2 data.rawResidue.cells.card + 1 : ℝ) ≤
          (Nat.log 2 (wz1Lemma23BoundedCells delta hdelta).card + 1 : ℕ) := by
      exact_mod_cast hrawLogNat
    exact hcast.trans (by simpa [L] using hlog)
  apply hschedule delta hdelta hdeltaSmall
      data.heightPopular.bins
      (Nat.log 2 data.rawResidue.cells.card + 1)
      data.graph.residue.extraCost data.height_bins_real_le_log
      (by simpa [L, Nat.cast_add, Nat.cast_one] using hrawLogReal)
  rw [data.extraCost_eq]

/-- Uniform absorption for the height popularity selected on the current
outer-popular graph shadow. -/
theorem pureWZ2_terminalPopular_graphHeight_schedule
    {epsilon localMassLoss : ℝ}
    (hepsilonOne : epsilon < 1)
    (hgap : epsilon / 2 < localMassLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {sigma inputLoss delta stickyLoss eta : ℝ}
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
        {graphParents : PureWZ2TerminalPopularGraphParentData prep}
        {localCells : PureWZ2TerminalPopularLocalCellData
          (eta := eta) graphParents}
        (data : PureWZ2TerminalPopularPreparedGraphData localCells),
        0 < delta → delta ≤ delta₀ →
          8 * Kakeya.realRpowENN delta localMassLoss *
              (data.heightPopular.bins : ENNReal) *
              (data.heightPopular.heightIndices.card : ENNReal) ≤
            pureWZ2TerminalPopularRichFloor delta epsilon := by
  let gap := localMassLoss - epsilon / 2
  have hgapPos : 0 < gap := by dsimp only [gap]; linarith
  rcases pureWZ2_boundedGrid_logCost_schedule hgapPos with
    ⟨delta₀, hdelta₀, hdelta₀One, habsorb⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro sigma inputLoss delta stickyLoss eta logExponent source terminal
    terminalSource prepared window heightData carrier weightClass restricted
    restrictedPrepared line parents selection selectedCarrier sources localized
    prep graphParents localCells data hdelta hdeltaSmall
  have hdeltaOne : delta ≤ 1 := hdeltaSmall.trans hdelta₀One
  let L : ℝ := Real.log (1 / delta) + 1
  have hLone : 1 ≤ L := by
    dsimp only [L]
    have hlogNonneg : 0 ≤ Real.log (1 / delta) := by
      apply Real.log_nonneg
      exact one_le_one_div hdelta hdeltaOne
    linarith
  have hcostReal : ((24 * data.heightPopular.bins : ℕ) : ℝ) ≤
      Real.rpow delta (-gap) := by
    apply habsorb delta hdelta hdeltaSmall
      data.heightPopular.bins 12 (24 * data.heightPopular.bins)
    · exact data.height_bins_real_le_log
    · norm_num only [Nat.cast_ofNat]
      nlinarith
    · omega
  have hcostENN : (24 * data.heightPopular.bins : ENNReal) ≤
      Kakeya.realRpowENN delta (-gap) := by
    calc
      (24 * data.heightPopular.bins : ENNReal) =
          ENNReal.ofReal (((24 * data.heightPopular.bins : ℕ) : ℝ)) := by simp
      _ ≤ ENNReal.ofReal (Real.rpow delta (-gap)) :=
        ENNReal.ofReal_mono hcostReal
      _ = Kakeya.realRpowENN delta (-gap) := rfl
  have hcostAbsorb : (24 * data.heightPopular.bins : ENNReal) *
      Kakeya.realRpowENN delta gap ≤ 1 := by
    calc
      _ ≤ Kakeya.realRpowENN delta (-gap) *
          Kakeya.realRpowENN delta gap := by gcongr
      _ = Kakeya.realRpowENN delta ((-gap) + gap) :=
        (realRpowENN_add hdelta (-gap) gap).symm
      _ = 1 := by simp [Kakeya.realRpowENN]
  have hheight := data.popular_heights_le_window_cap
  have hsqrtInv : ENNReal.ofReal (3 / Real.sqrt delta) =
      3 * Kakeya.realRpowENN delta (-1 / 2) := by
    have hsqrtEq : Real.sqrt delta =
        Real.rpow delta (1 / 2 : ℝ) := Real.sqrt_eq_rpow delta
    have hreal : 3 / Real.sqrt delta =
        3 * Real.rpow delta (-1 / 2) := by
      calc
        3 / Real.sqrt delta = 3 * (Real.sqrt delta)⁻¹ := by ring
        _ = 3 * (Real.rpow delta (1 / 2))⁻¹ := by rw [hsqrtEq]
        _ = 3 * Real.rpow delta (-(1 / 2)) :=
          congrArg (fun value : ℝ => 3 * value)
            (Real.rpow_neg hdelta.le (1 / 2 : ℝ)).symm
        _ = 3 * Real.rpow delta (-1 / 2) := by congr 2 <;> ring
    rw [hreal, ENNReal.ofReal_mul (by norm_num)]
    norm_num [Kakeya.realRpowENN]
  have hsourceBound :
      8 * Kakeya.realRpowENN delta localMassLoss *
          (data.heightPopular.bins : ENNReal) *
          (data.heightPopular.heightIndices.card : ENNReal) ≤
        (24 * data.heightPopular.bins : ENNReal) *
          Kakeya.realRpowENN delta
            (gap + (epsilon - 1) / 2) := by
    calc
      _ ≤ 8 * Kakeya.realRpowENN delta localMassLoss *
          (data.heightPopular.bins : ENNReal) *
          ENNReal.ofReal (3 / Real.sqrt delta) := by gcongr
      _ = (24 * data.heightPopular.bins : ENNReal) *
          (Kakeya.realRpowENN delta localMassLoss *
            Kakeya.realRpowENN delta (-1 / 2)) := by
        rw [hsqrtInv]
        push_cast
        ring
      _ = (24 * data.heightPopular.bins : ENNReal) *
          Kakeya.realRpowENN delta (localMassLoss - 1 / 2) := by
        rw [← realRpowENN_add hdelta]
        congr 2
        ring
      _ = (24 * data.heightPopular.bins : ENNReal) *
          Kakeya.realRpowENN delta
            (gap + (epsilon - 1) / 2) := by
        congr 2
        dsimp only [gap]
        ring
  have hpowerSplit : Kakeya.realRpowENN delta
        (gap + (epsilon - 1) / 2) =
      Kakeya.realRpowENN delta gap *
        Kakeya.realRpowENN delta ((epsilon - 1) / 2) :=
    realRpowENN_add hdelta gap ((epsilon - 1) / 2)
  have hbaseFloor : Kakeya.realRpowENN delta ((epsilon - 1) / 2) ≤
      pureWZ2TerminalPopularRichFloor delta epsilon := by
    apply ENNReal.ofReal_mono
    have hscalePos : 0 < wz1Lemma23Theorem22Scale (delta / 625) := by
      dsimp only [wz1Lemma23Theorem22Scale]
      positivity
    have hscaleLe : wz1Lemma23Theorem22Scale (delta / 625) ≤
        Real.sqrt delta := by
      have hscaleEq : wz1Lemma23Theorem22Scale (delta / 625) =
          Real.sqrt delta / (125 * Real.sqrt 3) := by
        rw [wz1Lemma23Theorem22Scale, Real.sqrt_div hdelta.le]
        norm_num
        ring
      rw [hscaleEq]
      have hdenom : 1 ≤ 125 * Real.sqrt 3 := by
        have hsqrt : 1 ≤ Real.sqrt 3 :=
          Real.one_le_sqrt.mpr (by norm_num)
        nlinarith
      exact div_le_self (Real.sqrt_nonneg delta) hdenom
    have hroot : Real.rpow (Real.sqrt delta) (epsilon - 1) ≤
        Real.rpow (wz1Lemma23Theorem22Scale (delta / 625))
          (epsilon - 1) :=
      Real.rpow_le_rpow_of_nonpos hscalePos hscaleLe (by linarith)
    have hrootEq : Real.rpow (Real.sqrt delta) (epsilon - 1) =
        Real.rpow delta ((epsilon - 1) / 2) := by
      have hsqrtEq : Real.sqrt delta =
          Real.rpow delta (1 / 2 : ℝ) := Real.sqrt_eq_rpow delta
      calc
        Real.rpow (Real.sqrt delta) (epsilon - 1) =
            Real.rpow (Real.rpow delta (1 / 2)) (epsilon - 1) := by
          rw [hsqrtEq]
        _ = Real.rpow delta ((1 / 2) * (epsilon - 1)) :=
          (Real.rpow_mul hdelta.le (1 / 2) (epsilon - 1)).symm
        _ = Real.rpow delta ((epsilon - 1) / 2) := by
          congr 1
          ring
    rw [← hrootEq]
    exact hroot
  calc
    8 * Kakeya.realRpowENN delta localMassLoss *
          (data.heightPopular.bins : ENNReal) *
          (data.heightPopular.heightIndices.card : ENNReal) ≤
        (24 * data.heightPopular.bins : ENNReal) *
          Kakeya.realRpowENN delta
            (gap + (epsilon - 1) / 2) := hsourceBound
    _ = ((24 * data.heightPopular.bins : ENNReal) *
          Kakeya.realRpowENN delta gap) *
        Kakeya.realRpowENN delta ((epsilon - 1) / 2) := by
      rw [hpowerSplit]
      ring
    _ ≤ Kakeya.realRpowENN delta ((epsilon - 1) / 2) := by
      simpa using mul_le_mul_right' hcostAbsorb
        (Kakeya.realRpowENN delta ((epsilon - 1) / 2))
    _ ≤ pureWZ2TerminalPopularRichFloor delta epsilon := hbaseFloor

end Kakeya.Assouad

end
