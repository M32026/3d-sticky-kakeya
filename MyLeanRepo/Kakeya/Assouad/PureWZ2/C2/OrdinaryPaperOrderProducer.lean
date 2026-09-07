import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderMultiWindow
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderBlockRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.BalancedSafeCoarsePullbackBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalRelativeMassBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryOneScaleSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalUniformBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalProjectionThreshold
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseProjectionThreshold

/-!
# Paper-order ordinary one-scale producer

This is the geometric assembly boundary for WZ Lemma 24.  It performs both
sticky-scale block preparation steps, source-volume popularity before the
fixed-line choice, the Lemma-23 graph, `Z_popular`, `Z_lin`, residue-class
separation, and the final same-extremizer grain refinement.

Only the two aggregate quantitative inequalities remain visible to the outer
uniform small-scale schedule.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- The paper's first height-popularity cost is logarithmic in the common
`256 * rho` grid.  This is uniform in the source window and in every later
fixed-line choice. -/
theorem PureWZ2SourceWindowHeightPopularData.bins_real_le_log
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (data : PureWZ2SourceWindowHeightPopularData window (256 * rho))
    (hgraphOne : 256 * rho ≤ 1) :
    (data.popular.bins : ℝ) ≤
      23 * (Real.log (1 / (256 * rho)) + 1) := by
  have hgraph : 0 < 256 * rho := data.popular.graphScale_pos
  have hheightCard :
      (wz1Lemma23BoundedHeightIndices (256 * rho) hgraph).card ≤
        (wz1Lemma23BoundedCells (256 * rho) hgraph).card :=
    Finset.card_image_le
  have hheightNonempty :
      (wz1Lemma23BoundedHeightIndices (256 * rho) hgraph).Nonempty :=
    data.popular.heightIndices_nonempty.mono
      data.popular.heightIndices_subset
  have hcellsNonempty :
      (wz1Lemma23BoundedCells (256 * rho) hgraph).Nonempty := by
    simpa [wz1Lemma23BoundedHeightIndices] using hheightNonempty
  have hbinsArg :
      2 * (wz1Lemma23BoundedHeightIndices (256 * rho) hgraph).card ≤
        4 * (wz1Lemma23BoundedCells (256 * rho) hgraph).card := by
    have hcellsPos :
        0 < (wz1Lemma23BoundedCells (256 * rho) hgraph).card :=
      hcellsNonempty.card_pos
    omega
  have hbinsLog :
      Nat.log 2
          (2 * (wz1Lemma23BoundedHeightIndices (256 * rho) hgraph).card) ≤
        Nat.log 2
          (4 * (wz1Lemma23BoundedCells (256 * rho) hgraph).card) :=
    Nat.log_mono_right hbinsArg
  have hcellsNe :
      (wz1Lemma23BoundedCells (256 * rho) hgraph).card ≠ 0 :=
    hcellsNonempty.card_ne_zero
  have hfourEq :
      4 * (wz1Lemma23BoundedCells (256 * rho) hgraph).card =
        (wz1Lemma23BoundedCells (256 * rho) hgraph).card * 2 * 2 := by
    ring
  have hbinsNat : data.popular.bins ≤
      Nat.log 2 (wz1Lemma23BoundedCells (256 * rho) hgraph).card + 3 := by
    rw [data.popular.bins_eq]
    calc
      Nat.log 2
          (2 * (wz1Lemma23BoundedHeightIndices (256 * rho) hgraph).card) + 1 ≤
          Nat.log 2
            (4 * (wz1Lemma23BoundedCells (256 * rho) hgraph).card) + 1 := by
        omega
      _ = Nat.log 2 (wz1Lemma23BoundedCells (256 * rho) hgraph).card + 3 := by
        rw [hfourEq]
        calc
          Nat.log 2
                ((wz1Lemma23BoundedCells (256 * rho) hgraph).card * 2 * 2) + 1 =
              Nat.log 2
                ((wz1Lemma23BoundedCells (256 * rho) hgraph).card * 2) + 1 + 1 := by
            rw [Nat.log_mul_base (by omega)
              (Nat.mul_ne_zero hcellsNe (by omega))]
          _ = Nat.log 2
                (wz1Lemma23BoundedCells (256 * rho) hgraph).card + 1 + 1 + 1 := by
            rw [Nat.log_mul_base (by omega) hcellsNe]
          _ = _ := by omega
  let L : ℝ := Real.log (1 / (256 * rho)) + 1
  have hlog := wz1Lemma23BoundedCells_log_bound hgraph hgraphOne
  have hLone : 1 ≤ L := by
    dsimp only [L]
    have hlogNonneg : 0 ≤ Real.log (1 / (256 * rho)) := by
      apply Real.log_nonneg
      exact one_le_one_div hgraph hgraphOne
    linarith
  have hnat : (data.popular.bins : ℝ) ≤
      (Nat.log 2 (wz1Lemma23BoundedCells (256 * rho) hgraph).card + 3 : ℕ) := by
    exact_mod_cast hbinsNat
  calc
    (data.popular.bins : ℝ) ≤
        (Nat.log 2 (wz1Lemma23BoundedCells (256 * rho) hgraph).card + 3 : ℕ) :=
      hnat
    _ ≤ 20 * L + 2 := by
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      linarith [hlog]
    _ ≤ 23 * L := by nlinarith

/-- Although the popularity bins are defined using the ambient bounded grid,
the selected heights still meet the original one-window source.  Their actual
cardinality therefore has the paper-scale `O(rho⁻¹/²)` bound. -/
theorem PureWZ2SourceWindowHeightPopularData.popular_heights_le_window_cap
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (data : PureWZ2SourceWindowHeightPopularData window (256 * rho)) :
    (data.popular.heightIndices.card : ENNReal) ≤
      ENNReal.ofReal (4 / Real.sqrt rho) := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact source.extremal.delta_pos.trans_le
      twoScale.rhoRequested.property.1
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  let values : Finset ℝ := data.popular.heightIndices.image
    (wz1Lemma23SnappedBaseHeight (256 * rho))
  have hinjective : Function.Injective
      (wz1Lemma23SnappedBaseHeight (256 * rho)) := by
    intro first second heq
    have hside : 0 < gridSide ((256 * rho) / 2) := by
      simp [gridSide]
      positivity
    have hsum :
        ((first : ℝ) + 1 / 2) = ((second : ℝ) + 1 / 2) :=
      mul_right_cancel₀ hside.ne' (by
        simpa [wz1Lemma23SnappedBaseHeight] using heq)
    have hcast : (first : ℝ) = (second : ℝ) := by linarith
    exact_mod_cast hcast
  have hcard : values.card = data.popular.heightIndices.card :=
    Finset.card_image_of_injective _ hinjective
  have hvaluesNonempty : values.Nonempty :=
    data.popular.heightIndices_nonempty.image _
  let left := window.left - rho - gridSide ((256 * rho) / 2) / 2
  let right := window.left + Real.sqrt rho + rho +
    gridSide ((256 * rho) / 2) / 2
  have hrange : ∀ value ∈ values, left ≤ value ∧ value ≤ right := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with
      ⟨heightIndex, hheightIndex, rfl⟩
    have hlayerPos : 0 < volume (window.shading.union ∩
        wz1Lemma23HeightSlab (256 * rho) heightIndex) :=
      data.popular.layerMass_pos.trans_le
        (data.popular.layer_volume_band heightIndex hheightIndex).1
    have hlayerNonempty : (window.shading.union ∩
        wz1Lemma23HeightSlab (256 * rho) heightIndex).Nonempty := by
      by_contra hempty
      have hempty' : window.shading.union ∩
          wz1Lemma23HeightSlab (256 * rho) heightIndex = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hempty
      rw [hempty'] at hlayerPos
      simpa using hlayerPos
    rcases hlayerNonempty with ⟨point, hpointWindow, hpointSlab⟩
    have hwindow := window.union_height_window point hpointWindow
    have hslab := hpointSlab
    change point (2 : Fin 3) ∈
      Set.Ico (((heightIndex : ℝ)) * gridSide ((256 * rho) / 2))
        (((heightIndex : ℝ) + 1) * gridSide ((256 * rho) / 2)) at hslab
    dsimp only [left, right, wz1Lemma23SnappedBaseHeight]
    have hside : 0 < gridSide ((256 * rho) / 2) := by
      simp [gridSide]
      positivity
    constructor <;> nlinarith [hwindow.1, hwindow.2, hslab.1, hslab.2]
  have hseparated : ∀ first ∈ values, ∀ second ∈ values, first ≠ second →
      gridSide ((256 * rho) / 2) ≤ |first - second| := by
    intro first hfirst second hsecond hne
    rcases Finset.mem_image.mp hfirst with
      ⟨firstIndex, hfirstIndex, rfl⟩
    rcases Finset.mem_image.mp hsecond with
      ⟨secondIndex, hsecondIndex, rfl⟩
    have hindexNe : firstIndex ≠ secondIndex := by
      intro heq
      subst secondIndex
      exact hne rfl
    have hint : (1 : ℝ) ≤ |((firstIndex - secondIndex : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hindexNe)
    have hformula :
        wz1Lemma23SnappedBaseHeight (256 * rho) firstIndex -
            wz1Lemma23SnappedBaseHeight (256 * rho) secondIndex =
          ((firstIndex - secondIndex : ℤ) : ℝ) *
            gridSide ((256 * rho) / 2) := by
      simp [wz1Lemma23SnappedBaseHeight]
      ring
    rw [hformula, abs_mul, abs_of_pos (by
      simp [gridSide]
      positivity : 0 < gridSide ((256 * rho) / 2))]
    simpa using mul_le_mul_of_nonneg_right hint (by
      exact (show 0 < gridSide ((256 * rho) / 2) by
        simp [gridSide]
        positivity).le)
  have hcount := lemma23_separated_real_finset_card_le
    (by simp [gridSide]; positivity : 0 < gridSide ((256 * rho) / 2))
    hvaluesNonempty hrange hseparated
  rw [hcard] at hcount
  have hsqrtPos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  have hsqrtSq : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt hrho.le
  have hsqrtThree : Real.sqrt (3 : ℝ) < 2 := by
    nlinarith [Real.sqrt_nonneg 3,
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hsqrtThreePos : 0 < Real.sqrt (3 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  have hsqrtOne : Real.sqrt rho ≤ 1 := Real.sqrt_le_one.mpr hrhoOne
  have hside : gridSide ((256 * rho) / 2) =
      256 * rho / Real.sqrt 3 := by
    simp [gridSide]
    ring
  have hreal : (data.popular.heightIndices.card : ℝ) ≤
      4 / Real.sqrt rho := by
    have hcount' : (data.popular.heightIndices.card : ℝ) ≤
        (Real.sqrt rho + 2 * rho +
            gridSide ((256 * rho) / 2)) /
              gridSide ((256 * rho) / 2) + 1 := by
      exact hcount.trans_eq (by
        dsimp only [left, right]
        congr 1
        ring)
    rw [hside] at hcount'
    have honeInv : 1 ≤ 1 / Real.sqrt rho :=
      one_le_one_div hsqrtPos hsqrtOne
    have hrewrite :
        (Real.sqrt rho + 2 * rho + 256 * rho / Real.sqrt 3) /
              (256 * rho / Real.sqrt 3) + 1 =
            Real.sqrt 3 / (256 * Real.sqrt rho) +
              Real.sqrt 3 / 128 + 2 := by
      field_simp [hrho.ne', hsqrtPos.ne', hsqrtThreePos.ne']
      nlinarith
    have hratio :
        (Real.sqrt rho + 2 * rho + 256 * rho / Real.sqrt 3) /
            (256 * rho / Real.sqrt 3) + 1 ≤
          4 / Real.sqrt rho := by
      rw [hrewrite]
      have hfirst : Real.sqrt 3 / (256 * Real.sqrt rho) ≤
          2 / (256 * Real.sqrt rho) := by gcongr
      have hsecond : Real.sqrt 3 / 128 ≤ 2 / 128 := by gcongr
      have hfirst' : 2 / (256 * Real.sqrt rho) =
          (1 / 128) * (1 / Real.sqrt rho) := by
        field_simp [hsqrtPos.ne'] <;> norm_num
      have hsecond' : 2 / 128 ≤
          (1 / 64) * (1 / Real.sqrt rho) := by
        nlinarith [honeInv]
      have htwo : 2 ≤ 2 * (1 / Real.sqrt rho) := by
        nlinarith [honeInv]
      calc
        Real.sqrt 3 / (256 * Real.sqrt rho) +
              Real.sqrt 3 / 128 + 2 ≤
            2 / (256 * Real.sqrt rho) + 2 / 128 + 2 := by
              exact add_le_add (add_le_add hfirst hsecond) le_rfl
        _ ≤ (1 / 128) * (1 / Real.sqrt rho) +
              (1 / 64) * (1 / Real.sqrt rho) +
                2 * (1 / Real.sqrt rho) := by
              exact add_le_add (add_le_add hfirst'.le hsecond') htwo
        _ ≤ 4 / Real.sqrt rho := by
          have hinvNonneg : 0 ≤ 1 / Real.sqrt rho := by positivity
          calc
            (1 / 128) * (1 / Real.sqrt rho) +
                  (1 / 64) * (1 / Real.sqrt rho) +
                    2 * (1 / Real.sqrt rho) =
                (2 + 3 / 128) * (1 / Real.sqrt rho) := by ring
            _ ≤ 4 * (1 / Real.sqrt rho) := by gcongr <;> norm_num
            _ = 4 / Real.sqrt rho := by ring
    exact hcount'.trans hratio
  exact (ENNReal.natCast_le_ofReal
    data.popular.heightIndices_nonempty.card_ne_zero).mpr hreal

/-- Source-independent version of the actual one-window popularity cost.
Unlike the ambient radius-two grid count, this has only one half-power of
`rho`, which is the loss used in the paper's `Z_S` step. -/
noncomputable def pureWZ2OrdinaryPaperOrderWindowHeightCost
    (rho : ℝ) : ENNReal :=
  368 * ENNReal.ofReal (Real.log rho⁻¹ + 1) *
    Kakeya.realRpowENN rho (-(1 / 2 : ℝ))

theorem PureWZ2OrdinaryPaperOrderAllBlockCarrierData.window_height_cost_bound
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
    (hrho : 0 < rho) (hgraphOne : 256 * rho ≤ 1)
    (block : {block // block ∈ safe.blocks}) :
    (4 * (family.carrierData block).outerPopular.popular.bins : ENNReal) *
        ((family.carrierData block).outerPopular.popular.heightIndices.card :
          ENNReal) ≤
      pureWZ2OrdinaryPaperOrderWindowHeightCost rho := by
  let popular := (family.carrierData block).outerPopular
  have hrhoOne : rho ≤ 1 := by nlinarith
  have hinvOne : (1 : ℝ) ≤ rho⁻¹ :=
    (one_le_inv₀ hrho).mpr hrhoOne
  have hlogNonneg : 0 ≤ Real.log rho⁻¹ := by
    exact Real.log_nonneg hinvOne
  have hlogScaled : Real.log (1 / (256 * rho)) ≤ Real.log rho⁻¹ := by
    apply Real.log_le_log
    · positivity
    · rw [one_div]
      exact (inv_le_inv₀ (by positivity : 0 < 256 * rho) hrho).mpr
        (by nlinarith : rho ≤ 256 * rho)
  have hbinsReal :
      ((4 * popular.popular.bins : ℕ) : ℝ) ≤
        92 * (Real.log rho⁻¹ + 1) := by
    have hbins := popular.bins_real_le_log hgraphOne
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hbinsENN :
      (4 * popular.popular.bins : ENNReal) ≤
        ENNReal.ofReal (92 * (Real.log rho⁻¹ + 1)) := by
    calc
      (4 * popular.popular.bins : ENNReal) =
          ENNReal.ofReal (((4 * popular.popular.bins : ℕ) : ℝ)) := by simp
      _ ≤ ENNReal.ofReal (92 * (Real.log rho⁻¹ + 1)) :=
        ENNReal.ofReal_mono hbinsReal
  have hheight := popular.popular_heights_le_window_cap
  calc
    (4 * popular.popular.bins : ENNReal) *
          (popular.popular.heightIndices.card : ENNReal) ≤
        ENNReal.ofReal (92 * (Real.log rho⁻¹ + 1)) *
          ENNReal.ofReal (4 / Real.sqrt rho) :=
      mul_le_mul hbinsENN hheight (by positivity) (by positivity)
    _ = pureWZ2OrdinaryPaperOrderWindowHeightCost rho := by
      unfold pureWZ2OrdinaryPaperOrderWindowHeightCost
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 92)]
      rw [show ENNReal.ofReal (92 : ℝ) = 92 by norm_num]
      have hsqrt : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
      have hinv : (Real.sqrt rho)⁻¹ = Real.rpow rho (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow]
        exact (Real.rpow_neg hrho.le (1 / 2 : ℝ)).symm
      rw [div_eq_mul_inv, hinv, ENNReal.ofReal_mul
        (by norm_num : (0 : ℝ) ≤ 4)]
      rw [show ENNReal.ofReal (4 : ℝ) = 4 by norm_num]
      simp only [Kakeya.realRpowENN]
      norm_num
      ring

theorem pureWZ2OrdinaryPaperOrderWindowHeightCost_pos
    {rho : ℝ} (hrho : 0 < rho) (hrhoOne : rho ≤ 1) :
    0 < pureWZ2OrdinaryPaperOrderWindowHeightCost rho := by
  unfold pureWZ2OrdinaryPaperOrderWindowHeightCost
  apply ENNReal.mul_pos
  · exact mul_ne_zero (by norm_num) <|
      (ENNReal.ofReal_pos.mpr (by
        have hlog : 0 ≤ Real.log rho⁻¹ :=
          Real.log_nonneg ((one_le_inv₀ hrho).mpr hrhoOne)
        positivity)).ne'
  · exact (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hrho _)).ne'

@[simp] theorem pureWZ2OrdinaryPaperOrderWindowHeightCost_ne_top
    (rho : ℝ) :
    pureWZ2OrdinaryPaperOrderWindowHeightCost rho ≠ ⊤ := by
  unfold pureWZ2OrdinaryPaperOrderWindowHeightCost
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
    ENNReal.ofReal_ne_top

/-- The actual one-window source-height cost loses only `rho⁻¹/²`, up to one
logarithm. -/
theorem pureWZ2OrdinaryPaperOrderWindowHeightCost_power_schedule
    {heightLoss : ℝ} (hheightLoss : 1 / 2 < heightLoss) :
    ∃ rho₀ : ℝ, 0 < rho₀ ∧ rho₀ ≤ 1 ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ rho₀ →
        pureWZ2OrdinaryPaperOrderWindowHeightCost rho ≤
          Kakeya.realRpowENN rho (-heightLoss) := by
  let gap := heightLoss - 1 / 2
  have hgap : 0 < gap := by dsimp only [gap]; linarith
  rcases exists_delta_log_absorbed_ennreal
      (368 : ENNReal) (by norm_num) hgap (by norm_num : 0 < (1 : ℕ)) with
    ⟨rho₀, hrho₀, hrho₀One, habsorb⟩
  refine ⟨rho₀, hrho₀, hrho₀One, ?_⟩
  intro rho hrho hrhoSmall
  have hsplit : Kakeya.realRpowENN rho (-heightLoss) =
      Kakeya.realRpowENN rho (-gap) *
        Kakeya.realRpowENN rho (-(1 / 2 : ℝ)) := by
    rw [← realRpowENN_add hrho]
    congr 1
    dsimp only [gap]
    ring
  rw [hsplit]
  unfold pureWZ2OrdinaryPaperOrderWindowHeightCost
  simpa only [pow_one, add_comm] using mul_le_mul_right'
    (habsorb rho hrho hrhoSmall)
    (Kakeya.realRpowENN rho (-(1 / 2 : ℝ)))

/-- The one-window height cost is absorbed by the genuine rich-height floor
after spending one additional `rho^richLoss` factor. -/
theorem pureWZ2OrdinaryPaperOrderWindowHeightCost_richFloor_schedule
    {richLoss : ℝ} (hrichLoss : 0 < richLoss) (hrichOne : richLoss ≤ 1) :
    ∃ rho₀ : ℝ, 0 < rho₀ ∧ rho₀ ≤ 1 ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ rho₀ →
        512 * pureWZ2OrdinaryPaperOrderWindowHeightCost rho *
            Kakeya.realRpowENN rho richLoss ≤
          pureWZ2SourceHorizontalRichFloor rho richLoss := by
  let q : ENNReal := Kakeya.realRpowENN 2 (richLoss - 1)
  have hqZero : q ≠ 0 := by
    dsimp only [q, Kakeya.realRpowENN]
    exact (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos (by norm_num) _)).ne'
  have hqTop : q ≠ ⊤ := by
    dsimp only [q, Kakeya.realRpowENN]
    exact ENNReal.ofReal_ne_top
  let D : ENNReal := 188416 * q⁻¹
  have hDTop : D ≠ ⊤ := by
    dsimp only [D]
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.inv_ne_top.mpr hqZero)
  rcases exists_delta_log_absorbed_ennreal D hDTop
      (show 0 < richLoss / 2 by positivity)
      (by norm_num : 0 < (1 : ℕ)) with
    ⟨rho₀, hrho₀, hrho₀One, habsorb⟩
  refine ⟨rho₀, hrho₀, hrho₀One, ?_⟩
  intro rho hrho hrhoSmall
  let L : ENNReal := ENNReal.ofReal (Real.log rho⁻¹ + 1)
  have hcoefficient :
      188416 * L * Kakeya.realRpowENN rho (richLoss / 2) ≤ q := by
    have hscaled := mul_le_mul_right'
      (habsorb rho hrho hrhoSmall)
      (q * Kakeya.realRpowENN rho (richLoss / 2))
    have hcancelQ : q⁻¹ * q = 1 :=
      ENNReal.inv_mul_cancel hqZero hqTop
    have hcancelPower :
        Kakeya.realRpowENN rho (-(richLoss / 2)) *
            Kakeya.realRpowENN rho (richLoss / 2) = 1 := by
      rw [← realRpowENN_add hrho]
      simp [Kakeya.realRpowENN]
    dsimp only [D] at hscaled
    calc
      188416 * L * Kakeya.realRpowENN rho (richLoss / 2) =
          (188416 * q⁻¹ *
              ENNReal.ofReal (1 + Real.log rho⁻¹) ^ 1) *
            (q * Kakeya.realRpowENN rho (richLoss / 2)) := by
        dsimp only [L]
        rw [add_comm (Real.log rho⁻¹) 1]
        rw [pow_one]
        calc
          188416 * ENNReal.ofReal (1 + Real.log rho⁻¹) *
                Kakeya.realRpowENN rho (richLoss / 2) =
              (188416 * ENNReal.ofReal (1 + Real.log rho⁻¹) *
                Kakeya.realRpowENN rho (richLoss / 2)) * 1 := by simp
          _ = (188416 * ENNReal.ofReal (1 + Real.log rho⁻¹) *
                Kakeya.realRpowENN rho (richLoss / 2)) * (q⁻¹ * q) := by
              rw [hcancelQ]
          _ = _ := by ring
      _ ≤ Kakeya.realRpowENN rho (-(richLoss / 2)) *
            (q * Kakeya.realRpowENN rho (richLoss / 2)) := hscaled
      _ = q := by
        calc
          Kakeya.realRpowENN rho (-(richLoss / 2)) *
                (q * Kakeya.realRpowENN rho (richLoss / 2)) =
              q * (Kakeya.realRpowENN rho (-(richLoss / 2)) *
                Kakeya.realRpowENN rho (richLoss / 2)) := by ring
          _ = q := by rw [hcancelPower, mul_one]
  have hfloor : q * Kakeya.realRpowENN rho ((richLoss - 1) / 2) ≤
      pureWZ2SourceHorizontalRichFloor rho richLoss := by
    have hgraphPos : 0 < wz1Lemma23Theorem22Scale (256 * rho) := by
      unfold wz1Lemma23Theorem22Scale
      positivity
    have hgraphLe := pureWZ2_sourceFixedBinCoarse_deltaGraph_le_two_sqrt hrho
    have hreal :
        Real.rpow (2 * Real.sqrt rho) (richLoss - 1) ≤
          Real.rpow (wz1Lemma23Theorem22Scale (256 * rho))
            (richLoss - 1) :=
      Real.rpow_le_rpow_of_nonpos hgraphPos hgraphLe (by linarith)
    have hsplit :
        Kakeya.realRpowENN (2 * Real.sqrt rho) (richLoss - 1) =
          q * Kakeya.realRpowENN rho ((richLoss - 1) / 2) := by
      rw [realRpowENN_mul (by norm_num) (Real.sqrt_pos.mpr hrho)]
      dsimp only [q]
      congr 1
      simp only [Kakeya.realRpowENN, Real.sqrt_eq_rpow]
      apply congrArg ENNReal.ofReal
      calc
        (Real.rpow rho (1 / 2 : ℝ)).rpow (richLoss - 1) =
            Real.rpow rho ((1 / 2 : ℝ) * (richLoss - 1)) :=
          (Real.rpow_mul hrho.le _ _).symm
        _ = Real.rpow rho ((richLoss - 1) / 2) := by
          congr 1
          ring
    rw [← hsplit]
    exact ENNReal.ofReal_mono hreal
  calc
    512 * pureWZ2OrdinaryPaperOrderWindowHeightCost rho *
          Kakeya.realRpowENN rho richLoss =
        (188416 * L * Kakeya.realRpowENN rho (richLoss / 2)) *
          Kakeya.realRpowENN rho ((richLoss - 1) / 2) := by
      unfold pureWZ2OrdinaryPaperOrderWindowHeightCost
      dsimp only [L]
      have hleft : Kakeya.realRpowENN rho (-(1 / 2 : ℝ)) *
            Kakeya.realRpowENN rho richLoss =
          Kakeya.realRpowENN rho (richLoss - 1 / 2) := by
        rw [← realRpowENN_add hrho]
        congr 1
        ring
      have hright : Kakeya.realRpowENN rho (richLoss / 2) *
            Kakeya.realRpowENN rho ((richLoss - 1) / 2) =
          Kakeya.realRpowENN rho (richLoss - 1 / 2) := by
        rw [← realRpowENN_add hrho]
        congr 1
        ring
      calc
        512 * (368 * ENNReal.ofReal (Real.log rho⁻¹ + 1) *
              Kakeya.realRpowENN rho (-(1 / 2 : ℝ))) *
              Kakeya.realRpowENN rho richLoss =
            188416 * ENNReal.ofReal (Real.log rho⁻¹ + 1) *
              (Kakeya.realRpowENN rho (-(1 / 2 : ℝ)) *
                Kakeya.realRpowENN rho richLoss) := by norm_num; ring
        _ = 188416 * ENNReal.ofReal (Real.log rho⁻¹ + 1) *
              Kakeya.realRpowENN rho (richLoss - 1 / 2) := by rw [hleft]
        _ = 188416 * ENNReal.ofReal (Real.log rho⁻¹ + 1) *
              (Kakeya.realRpowENN rho (richLoss / 2) *
                Kakeya.realRpowENN rho ((richLoss - 1) / 2)) := by rw [hright]
        _ = _ := by ring
    _ ≤ q * Kakeya.realRpowENN rho ((richLoss - 1) / 2) := by gcongr
    _ ≤ pureWZ2SourceHorizontalRichFloor rho richLoss := hfloor

/-- A finite, source-independent bound for the outer `Z_S` bin count times
its number of retained height slabs.  It depends only on the graph scale and
is chosen before any source window or fixed line. -/
noncomputable def pureWZ2OrdinaryPaperOrderSourceHeightCost
    (rho : ℝ) (hrho : 0 < rho) : ENNReal :=
  let heights := wz1Lemma23BoundedHeightIndices (256 * rho) (by positivity)
  1 + 12 * ((Nat.log 2 (2 * heights.card) + 1 : ℕ) : ENNReal) *
    (heights.card : ENNReal)

theorem PureWZ2OrdinaryPaperOrderAllBlockCarrierData.source_height_cost_bound
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
    (hrho : 0 < rho)
    (block : {block // block ∈ safe.blocks}) :
    (12 * (family.carrierData block).outerPopular.popular.bins : ENNReal) *
        ((family.carrierData block).outerPopular.popular.heightIndices.card :
          ENNReal) ≤
      pureWZ2OrdinaryPaperOrderSourceHeightCost rho hrho := by
  let heights := wz1Lemma23BoundedHeightIndices (256 * rho) (by positivity)
  have hbins : (family.carrierData block).outerPopular.popular.bins =
      Nat.log 2 (2 * heights.card) + 1 := by
    simpa [heights] using
      (family.carrierData block).outerPopular.popular.bins_eq
  have hheight :
      (family.carrierData block).outerPopular.popular.heightIndices.card ≤
        heights.card :=
    Finset.card_le_card
      (by simpa [heights] using
        (family.carrierData block).outerPopular.popular.heightIndices_subset)
  unfold pureWZ2OrdinaryPaperOrderSourceHeightCost
  dsimp only
  rw [hbins]
  calc
    12 * (↑(Nat.log 2 (2 * heights.card) + 1) : ENNReal) *
          ↑(family.carrierData block).outerPopular.popular.heightIndices.card ≤
        12 * (↑(Nat.log 2 (2 * heights.card) + 1) : ENNReal) *
          ↑heights.card := by
      gcongr
    _ ≤ 1 + 12 * (↑(Nat.log 2 (2 * heights.card) + 1) : ENNReal) *
          ↑heights.card := by
      exact le_add_left le_rfl

theorem pureWZ2OrdinaryPaperOrderSourceHeightCost_pos
    (rho : ℝ) (hrho : 0 < rho) :
    0 < pureWZ2OrdinaryPaperOrderSourceHeightCost rho hrho := by
  unfold pureWZ2OrdinaryPaperOrderSourceHeightCost
  positivity

@[simp] theorem pureWZ2OrdinaryPaperOrderSourceHeightCost_ne_top
    (rho : ℝ) (hrho : 0 < rho) :
    pureWZ2OrdinaryPaperOrderSourceHeightCost rho hrho ≠ ⊤ := by
  simp only [pureWZ2OrdinaryPaperOrderSourceHeightCost]
  rw [ENNReal.add_ne_top]
  exact ⟨by norm_num, ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by norm_num) (by simp)) (by simp)⟩

/-- At a uniformly small internal scale, the first `Z_S` dyadic loss is
absorbed by any prescribed positive graph-scale power. -/
theorem pureWZ2_sourceWindowHeightBins_power_schedule
    {extraLoss : ℝ} (hextraLoss : 0 < extraLoss) :
    ∃ rho₀ : ℝ, 0 < rho₀ ∧ rho₀ ≤ 1 ∧
      ∀ {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
        {logExponent : ℕ}
        {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
        {twoScale : PureWZ2OneScaleTwoScaleStickyData
          source rho middleLoss stickyLoss logExponent}
        {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
        {prepared : PureWZ2SourceCarrierPreparation pullback}
        {window : PureWZ2SourceCarrierWindow prepared}
        (data : PureWZ2SourceWindowHeightPopularData window (256 * rho)),
        0 < rho → rho ≤ rho₀ →
          (4 * data.popular.bins : ENNReal) ≤
            Kakeya.realRpowENN (256 * rho) (-extraLoss) := by
  rcases log_poly_decay_general 92 extraLoss (by norm_num) hextraLoss with
    ⟨graphScale₀, hgraphScale₀, hgraphScale₀One, habsorb⟩
  let rho₀ := graphScale₀ / 256
  refine ⟨rho₀, by positivity,
    (div_le_self hgraphScale₀.le (by norm_num)).trans hgraphScale₀One, ?_⟩
  intro sigma inputLoss delta rho middleLoss stickyLoss logExponent source
    twoScale pullback prepared window data hrho hrhoSmall
  have hgraph : 0 < 256 * rho := by positivity
  have hgraphSmall : 256 * rho ≤ graphScale₀ := by
    calc
      256 * rho ≤ 256 * rho₀ := by gcongr
      _ = graphScale₀ := by unfold rho₀; ring
  have hgraphOne : 256 * rho ≤ 1 := hgraphSmall.trans hgraphScale₀One
  have hbins := data.bins_real_le_log hgraphOne
  have hreal : ((4 * data.popular.bins : ℕ) : ℝ) ≤
      Real.rpow (256 * rho) (-extraLoss) := by
    calc
      ((4 * data.popular.bins : ℕ) : ℝ) ≤
          92 * (Real.log (1 / (256 * rho)) + 1) := by
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        linarith
      _ ≤ 1 / (256 * rho) ^ extraLoss :=
        habsorb (256 * rho) hgraph hgraphSmall
      _ = Real.rpow (256 * rho) (-extraLoss) := by
        simpa [one_div] using (Real.rpow_neg hgraph.le extraLoss).symm
  calc
    (4 * data.popular.bins : ENNReal) =
        ENNReal.ofReal (((4 * data.popular.bins : ℕ) : ℝ)) := by simp
    _ ≤ ENNReal.ofReal (Real.rpow (256 * rho) (-extraLoss)) :=
      ENNReal.ofReal_mono hreal
    _ = Kakeya.realRpowENN (256 * rho) (-extraLoss) := rfl

/-- Simultaneously bound the first `Z_S` popularity cost on every safe block.
The bound is chosen before the dependent block family is constructed. -/
theorem PureWZ2OrdinaryPaperOrderAllBlockCarrierData.outer_bins_power_bound
    {sigma inputLoss delta rho middleLoss stickyLoss outerLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
    (houterLoss : 0 < outerLoss)
    (hrho : 0 < rho) (hrhoSmall : rho ≤
      Classical.choose (pureWZ2_sourceWindowHeightBins_power_schedule
        (extraLoss := outerLoss) houterLoss)) :
    ∀ block : {block // block ∈ safe.blocks},
      (2 * (family.carrierData block).outerPopular.popular.bins : ENNReal) ≤
        Kakeya.realRpowENN (256 * rho) (-outerLoss) := by
  intro block
  have hfour := (Classical.choose_spec
    (pureWZ2_sourceWindowHeightBins_power_schedule
      (extraLoss := outerLoss) houterLoss)).2.2
    (sigma := sigma) (inputLoss := inputLoss) (delta := delta)
    (rho := rho) (middleLoss := middleLoss) (stickyLoss := stickyLoss)
    (logExponent := logExponent) (source := source) (twoScale := twoScale)
    (pullback := pullback) (prepared := prepared)
    (window := (family.carrierData block).sourceWindow)
    (family.carrierData block).outerPopular hrho hrhoSmall
  calc
    (2 * (family.carrierData block).outerPopular.popular.bins : ENNReal) ≤
        (4 * (family.carrierData block).outerPopular.popular.bins : ENNReal) := by
      exact_mod_cast Nat.mul_le_mul_right
        (family.carrierData block).outerPopular.popular.bins (by omega : 2 ≤ 4)
    _ ≤ Kakeya.realRpowENN (256 * rho) (-outerLoss) := hfour

/-
Obsolete coarse-pullback graph budget. It identified the exact outer-popular
graph shadow with the uncut spatial residue and is intentionally unavailable.

/-- Convert the literal paper-order pullback estimate, including the first
height-popularity logarithm, into the unweighted graph-volume budget.  The
caller supplies one uniform upper bound for `2 * bins` and one small-scale
power comparison; all geometric factors come from the exact two-stage
pullback identities. -/
theorem PureWZ2OrdinaryPaperOrderAllBlockPreparationData.goodGraphBudget_of_coarse_pullback
    {sigma inputLoss delta rho middleLoss stickyLoss secondEta normalEta
      volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {firstPullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation firstPullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    (all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family)
    (hrhoSmall : twoScale.rhoRequested.1 ≤ 1 / 12)
    (hsecondFraction :
      Kakeya.realRpowENN twoScale.rhoRequested.1 secondEta ≤
        wz2PaperPureRefinementFraction
          twoScale.rhoRequested.1 logExponent)
    (hcoarseSigma : twoScale.coarseLoss ≤ sigma)
    (outerCost : ENNReal) (houterCostPos : 0 < outerCost)
    (houterCostTop : outerCost ≠ ⊤)
    (houterCost : ∀ block : {block // block ∈ safe.blocks},
      (2 * (family.carrierData block).outerPopular.popular.bins : ENNReal) ≤
        outerCost)
    (hpower :
      4 * outerCost *
          pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          (safe.blocks.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss) *
          volume twoScale.coarse.croppedCoarseShading.union ≤
        Kakeya.realRpowENN rho
            (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss)) :
    2 * ((safe.blocks.card : ENNReal) *
        Kakeya.realRpowENN (256 * rho)
          (1 + sigma / 2 + volumeLoss)) ≤
      ∑ block : {block // block ∈ safe.blocks},
        volume (all.graphPreparation block).prep.shadow.union := by
  let cost : ENNReal :=
    pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss
  let threshold : ENNReal := Kakeya.realRpowENN (256 * rho)
    (1 + sigma / 2 + volumeLoss)
  let coarseVolume : ENNReal :=
    volume twoScale.coarse.croppedCoarseShading.union
  let graphVolume : {block // block ∈ safe.blocks} → ENNReal := fun block =>
    volume (all.graphPreparation block).prep.shadow.union
  let common : ENNReal := 2 * outerCost * cost * coarseVolume
  have hstruct := prepared.coarse_pullback_graph_supply_lower
    hrhoSmall hsecondFraction hcoarseSigma
  have hall := all.aggregate_volume_supply_le_via_coarse_pullback
  have hweighted :
      2 * ∑ block : {block // block ∈ safe.blocks},
          (2 * (family.carrierData block).outerPopular.popular.bins : ℕ) *
            (cost * (graphVolume block * coarseVolume)) ≤
        common * ∑ block : {block // block ∈ safe.blocks},
          graphVolume block := by
    calc
      2 * ∑ block : {block // block ∈ safe.blocks},
          (2 * (family.carrierData block).outerPopular.popular.bins : ℕ) *
            (cost * (graphVolume block * coarseVolume)) ≤
        2 * ∑ block : {block // block ∈ safe.blocks},
          outerCost * (cost * (graphVolume block * coarseVolume)) := by
        gcongr with block
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using houterCost block
      _ = common * ∑ block : {block // block ∈ safe.blocks},
          graphVolume block := by
        calc
          2 * ∑ block : {block // block ∈ safe.blocks},
              outerCost * (cost * (graphVolume block * coarseVolume)) =
            ∑ block : {block // block ∈ safe.blocks},
              2 * (outerCost * (cost * (graphVolume block * coarseVolume))) := by
                rw [Finset.mul_sum]
          _ = ∑ block : {block // block ∈ safe.blocks},
              common * graphVolume block := by
            apply Finset.sum_congr rfl
            intro block _
            simp only [common]
            ring
          _ = common * ∑ block : {block // block ∈ safe.blocks},
              graphVolume block := by
            rw [Finset.mul_sum]
  have hscaled :
      common * (2 * ((safe.blocks.card : ENNReal) * threshold)) ≤
        common * ∑ block : {block // block ∈ safe.blocks},
          graphVolume block := by
    calc
      common * (2 * ((safe.blocks.card : ENNReal) * threshold)) =
          4 * outerCost * cost * (safe.blocks.card : ENNReal) * threshold *
            coarseVolume := by simp only [common]; ring
      _ ≤ Kakeya.realRpowENN rho
            (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) := by
        simpa [cost, threshold, coarseVolume, mul_assoc] using hpower
      _ ≤ volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
          volume twoScale.coarse.refined.union := hstruct
      _ ≤ 2 * ∑ block : {block // block ∈ safe.blocks},
          (2 * (family.carrierData block).outerPopular.popular.bins : ℕ) *
            (cost * (graphVolume block * coarseVolume)) := by
        simpa [cost, graphVolume, coarseVolume] using hall
      _ ≤ common * ∑ block : {block // block ∈ safe.blocks},
          graphVolume block := hweighted
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hcostPos : 0 < cost := by
    exact pureWZ2SourceHorizontalVolumeCost_pos hrho source.extremal.delta_pos
  have hcoarseVolumePos : 0 < coarseVolume := by
    have hpositive : 0 < Kakeya.realRpowENN
        twoScale.rhoRequested.1 (sigma + twoScale.coarseLoss) :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos twoScale.coarseGrains.extremal.delta_pos _)
    exact hpositive.trans_le (by
      simpa [coarseVolume] using twoScale.coarse.coarse_volume_lower)
  have hcommonZero : common ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) houterCostPos.ne') hcostPos.ne')
      hcoarseVolumePos.ne'
  have hcostTop : cost ≠ ⊤ := by
    exact pureWZ2SourceHorizontalVolumeCost_ne_top _ _ _ _
  have hcoarseVolumeTop : coarseVolume ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (by simp [Kakeya.realRpowENN])
      twoScale.coarse.coarse_extremal.volume_upper
  have hcommonTop : common ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) houterCostTop) hcostTop)
      hcoarseVolumeTop
  simpa only [threshold, graphVolume] using
    (ENNReal.mul_le_mul_iff_right hcommonZero hcommonTop).mp hscaled

-/

/-- The internal Lemma-23 popular heights in a paper-order block satisfy the
same geometric window bound as in the source-horizontal construction. -/
theorem PureWZ2OrdinaryPaperOrderGraphData.popular_heights_le_cap
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {prepared : PureWZ2OrdinaryPaperOrderPreparationData carriers}
    (data : PureWZ2OrdinaryPaperOrderGraphData
      (normalEta := normalEta) prepared) :
    (data.heightPopular.heightIndices.card : ENNReal) ≤
      PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho := by
  have hsubset : data.heightPopular.heightIndices ⊆
      wz1Lemma23SnappedHeights prepared.prep.windowed.global.cells := by
    intro heightIndex hheight
    have hglobal : heightIndex ∈
        prepared.prep.windowed.global.heightIndices := by
      rw [prepared.prep.windowed.global.heightIndices_eq]
      exact data.heightPopular.heightIndices_subset hheight
    have hlayerNonempty :
        (prepared.prep.windowed.global.layerCells heightIndex).Nonempty := by
      have hlayerPos : 0 < volume (prepared.prep.shadow.union ∩
          wz1Lemma23HeightSlab prepared.prep.graphScale heightIndex) :=
        data.heightPopular.layerMass_pos.trans_le
          (data.heightPopular.layer_volume_band heightIndex hheight).1
      by_contra hempty
      have hlayerEmpty := Finset.not_nonempty_iff_eq_empty.mp hempty
      have hbound := prepared.prep.windowed.global.layer_volume_bound
        heightIndex hglobal
      have harea := wz1_lemma23_exactSlice_area_le_two prepared.prep.shadow
        prepared.prep.graphScale_pos
        (by
          intro point hpoint
          have hpaper : point ∈ prepared.graphRetained.shading.union := by
            exact prepared.prep.shadow_union_subset hpoint
          have hnorm := norm_le_two_of_mem_paperShading hpaper
          simpa [Metric.mem_closedBall, dist_zero_right] using hnorm)
        (prepared.prep.windowed.global.selectedHeight heightIndex)
      rw [← prepared.prep.windowed.global.layerCells_eq heightIndex,
        hlayerEmpty] at harea
      norm_num at harea
      have hsidePos : 0 < ENNReal.ofReal
          (gridSide (prepared.prep.graphScale / 2)) := by
        apply ENNReal.ofReal_pos.mpr
        dsimp [gridSide]
        apply div_pos
        · nlinarith [prepared.prep.graphScale_pos]
        · exact Real.sqrt_pos.mpr (by norm_num)
      have hzero : volume (prepared.prep.shadow.union ∩
          wz1Lemma23HeightSlab prepared.prep.graphScale heightIndex) = 0 := by
        apply le_zero_iff.mp
        have hdiv : volume (prepared.prep.shadow.union ∩
              wz1Lemma23HeightSlab prepared.prep.graphScale heightIndex) /
              ENNReal.ofReal (gridSide (prepared.prep.graphScale / 2)) ≤ 0 :=
          hbound.trans harea.le
        have hmul := (ENNReal.div_le_iff hsidePos.ne'
          ENNReal.ofReal_ne_top).mp hdiv
        simpa using hmul
      exact (ne_of_gt hlayerPos) hzero
    rcases hlayerNonempty with ⟨cell, hcell⟩
    have hcellGlobal : cell ∈ prepared.prep.windowed.global.cells := by
      rw [prepared.prep.windowed.global.cells_eq]
      exact Finset.mem_biUnion.mpr ⟨heightIndex, hglobal, hcell⟩
    exact Finset.mem_image.mpr ⟨cell, hcellGlobal,
      (prepared.prep.windowed.global.layer_height
        heightIndex hglobal cell hcell)⟩
  have hreal := wz1Lemma23_height_layer_count
    prepared.prep.graphScale_pos prepared.prep.graphScale_one
    prepared.prep.windowed.global_cells_window
  have hcardReal : (data.heightPopular.heightIndices.card : ℝ) ≤
      3 / Real.sqrt prepared.prep.graphScale := by
    have hcast : (data.heightPopular.heightIndices.card : ℝ) ≤
        ((wz1Lemma23SnappedHeights
          prepared.prep.windowed.global.cells).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    exact hcast.trans hreal
  have henn := ENNReal.natCast_le_ofReal
    data.heightPopular.heightIndices_nonempty.card_ne_zero |>.mpr hcardReal
  simpa [PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap,
    prepared.prep.graphScale_eq] using henn

/-
The generic source-horizontal pipeline requires an equal-union whole-cell
shadow. The exact outer-popular ordinary carrier is a genuine partial-height
restriction, so it must not be coerced through that interface.

/-- Repackage the corrected paper-order block as the generic source-horizontal
pipeline used by the already proved uniform analytic and projection lemmas.
All fields are the same dependent witnesses; in particular no carrier or
slope is reconstructed. -/
def PureWZ2OrdinaryPaperOrderGraphData.toSourceHorizontalPipeline
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {prepared : PureWZ2OrdinaryPaperOrderPreparationData carriers}
    (data : PureWZ2OrdinaryPaperOrderGraphData
      (normalEta := normalEta) prepared) :
    PureWZ2SourceHorizontalPipelineData
      (normalEta := normalEta) twoScale where
  pullback := carriers.pullback
  prepared := carriers.prepared
  window := carriers.outerPopular.popularWindow
  line := carriers.line
  parents := carriers.parents
  selection := carriers.selection
  residue := carriers.residue
  retained := prepared.graphRetained
  prep := prepared.prep
  shadow_union := by
    rw [prepared.prep.shadow_eq]
    exact carriers.popular_graph_union
  graphParents := prepared.graphParents
  fineWitnesses := prepared.fineWitnesses
  normalFirst := data.normalFirst
  heightPopular := data.heightPopular
  popularSource := data.popularSource
  rawResidue := data.rawResidue
  rawResidue_eq := data.rawResidue_eq
  popularResidue := data.popularResidue
  graph := data.graph
  graph_residue_eq := data.graph_residue_eq
  heightFiberCost_eq := data.heightFiberCost_eq
  extraCost_eq := data.extraCost_eq
  volumeCost_eq := data.volumeCost_eq
  sharp := data.sharp

/-- The existing uniform internal-logarithm schedule applies verbatim to the
paper-order graph after the identity-preserving repackaging above. -/
theorem PureWZ2SourceHorizontalAnalyticThreshold.extra_paperOrder
    {theoremEta sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    (self : PureWZ2SourceHorizontalAnalyticThreshold theoremEta)
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {prepared : PureWZ2OrdinaryPaperOrderPreparationData carriers}
    (data : PureWZ2OrdinaryPaperOrderGraphData
      (normalEta := normalEta) prepared)
    (hrhoSmall : rho ≤ self.rho0) :
    (data.graph.residue.extraCost : ℝ) ≤
      Real.rpow prepared.prep.graphScale (-self.budget.extraLoss) := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  simpa [PureWZ2OrdinaryPaperOrderGraphData.toSourceHorizontalPipeline] using
    self.extra rho hrho hrhoSmall
      (twoScale := twoScale)
      data.toSourceHorizontalPipeline

-/

/-- The closed common-endpoint projection dichotomy applies to the exact
paper-order graph without changing its source family, shading, or slope. -/
theorem PureWZ2SourceHorizontalProjectionThreshold.alternativeA_paperOrder
    {sigma outputLoss inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    (self : PureWZ2SourceHorizontalProjectionThreshold sigma outputLoss)
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {prepared : PureWZ2OrdinaryPaperOrderPreparationData carriers}
    (graphData : PureWZ2OrdinaryPaperOrderGraphData
      (normalEta := normalEta) prepared)
    (data : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := self.theoremEta) graphData.sharp)
    (houtput : 0 < outputLoss) (houtputOne : outputLoss < 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (houtputSigma : outputLoss / 2 < sigma)
    {sourceCostLoss : ℝ}
    (hsourceCost : Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN data.ready.deltaGraph (-sourceCostLoss))
    (hsourceCostLoss : 0 ≤ sourceCostLoss)
    (hsourceCostCeiling : sourceCostLoss ≤ self.sourceCostLossCeiling)
    (hrhoSmall : rho ≤ self.rho₀) :
    WZ1Proposition8_9AlternativeAUnion
      data.ready.deltaGraph outputLoss
      data.common.F data.common.G₁ data.common.G₁ := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hgraphSmall : data.ready.deltaGraph ≤ self.reductionDelta₀ := by
    rw [data.ready.deltaGraph_eq, prepared.prep.graphScale_eq]
    exact self.graph_small rho hrho hrhoSmall
  have hgain : 10 * self.theoremEta + sourceCostLoss <
      self.projectionEta * (sigma - outputLoss / 2) := by
    calc
      10 * self.theoremEta + sourceCostLoss ≤
          10 * self.theoremEta + self.sourceCostLossCeiling := by gcongr
      _ < self.projectionEta * (sigma - outputLoss / 2) := self.gain
  have hconstantSmall :
      (648000000 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) ≤
        Kakeya.realRpowENN data.ready.deltaGraph
          (-(self.projectionEta * (sigma - outputLoss / 2) -
            (10 * self.theoremEta + sourceCostLoss)) / 2) := by
    have hceiling := self.constant_small rho hrho hrhoSmall
    rw [data.ready.deltaGraph_eq, prepared.prep.graphScale_eq]
    apply hceiling.trans
    apply ENNReal.ofReal_mono
    apply Real.rpow_le_rpow_of_exponent_ge
    · dsimp only [wz1Lemma23Theorem22Scale]
      positivity
    · exact (self.graph_small rho hrho hrhoSmall).trans
        (self.reductionDelta₀_le_half.trans (by norm_num))
    · have hactualGap :
          self.projectionEta * (sigma - outputLoss / 2) -
              (10 * self.theoremEta + sourceCostLoss) ≥
            self.projectionEta * (sigma - outputLoss / 2) -
              (10 * self.theoremEta + self.sourceCostLossCeiling) := by
        linarith
      nlinarith
  exact data.projection_alternative_a_strong
    houtput houtputOne hsigma hsigmaOne houtputSigma
    self.reduction hgraphSmall self.theoremEta_pos.le self.theoremEta_small
    hsourceCost hsourceCostLoss hgain hconstantSmall

/-- Uniform form of the literal `Z_lin ⊆ Z_S` source-window mass estimate.
The finite cost bounds exactly the already selected outer bin count and outer
height count; it contains no graph-shadow or coarse-carrier mass. -/
theorem PureWZ2OrdinaryPaperOrderRichGraphData.source_window_mass_bound_of_cost
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {prepared : PureWZ2OrdinaryPaperOrderPreparationData carriers}
    {graphData : PureWZ2OrdinaryPaperOrderGraphData
      (normalEta := normalEta) prepared}
    (data : PureWZ2OrdinaryPaperOrderRichGraphData
      (finalLoss := finalLoss) (theoremEta := theoremEta) graphData)
    (sourceHeightCost : ENNReal)
    (hcost : (12 * carriers.outerPopular.popular.bins : ENNReal) *
      (carriers.outerPopular.popular.heightIndices.card : ENNReal) ≤
        sourceHeightCost) :
    volume carriers.sourceWindow.shading.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
      sourceHeightCost * data.heightLift.shading.mass := by
  exact data.source_window_mass_bound.trans (by gcongr)

/-- If every source-regularized block is graph-ready, then the corresponding
good-block family carries a fixed fraction of the complete source-window
mass.  The hypothesis is pointwise on the same block; independent marginal
volume lower bounds are intentionally insufficient. -/
theorem PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData.aggregate_source_window_mass_bound
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    (data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss)
    (hregularizedGood :
      pureWZ2OrdinaryPaperOrderRegularizedBlocks safe ⊆
        pureWZ2OrdinaryPaperOrderGoodGraphBlocks all volumeLoss)
    (hrho : 0 < rho) :
    volume prepared.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
      4 * pureWZ2OrdinaryPaperOrderSourceHeightCost rho hrho *
        ∑ index : Fin data.indexCount,
          (data.rich index).heightLift.shading.mass := by
  let regularized := pureWZ2OrdinaryPaperOrderRegularizedBlocks safe
  let good := pureWZ2OrdinaryPaperOrderGoodGraphBlocks all volumeLoss
  let multiplicity : ENNReal := twoScale.coarse.fineMultiplicity
  let floor : ENNReal := pureWZ2SourceHorizontalRichFloor rho finalLoss
  let cost : ENNReal := pureWZ2OrdinaryPaperOrderSourceHeightCost rho hrho
  have hsource : volume prepared.shadow.union ≤
      4 * ∑ block ∈ good, volume (safe.blockWindow block).shading.union := by
    calc
      volume prepared.shadow.union ≤
          4 * ∑ block ∈ regularized,
            volume (safe.blockWindow block).shading.union := by
        simpa [regularized] using safe.regularizedBlocks_retains_quarter
      _ ≤ 4 * ∑ block ∈ good,
            volume (safe.blockWindow block).shading.union := by
        gcongr
  have hgoodIndexed :
      (∑ block ∈ good, volume (safe.blockWindow block).shading.union) =
        ∑ index : Fin data.indexCount,
          volume (safe.blockWindow (data.safeBlock index)).shading.union := by
    symm
    apply Finset.sum_bij (fun index _ => data.safeBlock index)
    · intro index _
      exact data.block_mem index
    · intro first _ second _ heq
      exact data.safeBlock_injective heq
    · intro block hblock
      rcases data.block_surjective block hblock with ⟨index, heq⟩
      exact ⟨index, Finset.mem_univ index, heq⟩
    · intro _index _
      rfl
  have hlocal :
      (∑ index : Fin data.indexCount,
          volume (safe.blockWindow (data.safeBlock index)).shading.union) *
          multiplicity * floor ≤
        cost * ∑ index : Fin data.indexCount,
          (data.rich index).heightLift.shading.mass := by
    calc
      _ = ∑ index : Fin data.indexCount,
          (volume (safe.blockWindow (data.safeBlock index)).shading.union *
            multiplicity * floor) := by
        rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ ∑ index : Fin data.indexCount,
          cost * (data.rich index).heightLift.shading.mass := by
        exact Finset.sum_le_sum fun index _ => by
          have hbound :=
            (data.rich index).source_window_mass_bound_of_cost
              cost (family.source_height_cost_bound hrho (data.safeBlock index))
          have hwindowVolume : volume
                (family.carrierData
                  (data.safeBlock index)).sourceWindow.shading.union =
              volume (safe.blockWindow (data.safeBlock index)).shading.union := by
            have hsourceWindow := family.carrierData_sourceWindow
              (data.safeBlock index)
            have hwindowShading :=
              (safe.blockWindow (data.safeBlock index)).window_shading
            exact congrArg (fun window => volume window.shading.union)
              hsourceWindow |>.trans
                (congrArg (fun shading => volume shading.union) hwindowShading)
          rw [hwindowVolume] at hbound
          simpa [cost, multiplicity, floor] using hbound
      _ = cost * ∑ index : Fin data.indexCount,
          (data.rich index).heightLift.shading.mass := by
        rw [Finset.mul_sum]
  calc
    volume prepared.shadow.union * multiplicity * floor ≤
        (4 * ∑ block ∈ good,
          volume (safe.blockWindow block).shading.union) *
            multiplicity * floor := by gcongr
    _ = 4 * ((∑ index : Fin data.indexCount,
          volume (safe.blockWindow (data.safeBlock index)).shading.union) *
            multiplicity * floor) := by rw [hgoodIndexed]; ring
    _ ≤ 4 * (cost * ∑ index : Fin data.indexCount,
          (data.rich index).heightLift.shading.mass) := by gcongr
    _ = 4 * cost * ∑ index : Fin data.indexCount,
          (data.rich index).heightLift.shading.mass := by ring

/-- The final mod-64 residue loses only its explicit factor `64` from the
same source-window aggregate estimate. -/
theorem PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData.PureWZ2OrdinaryPaperOrderBlockResidueData.selected_source_window_mass_bound
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    {data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss}
    (residueData :
      PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData.PureWZ2OrdinaryPaperOrderBlockResidueData
        data)
    (hregularizedGood :
      pureWZ2OrdinaryPaperOrderRegularizedBlocks safe ⊆
        pureWZ2OrdinaryPaperOrderGoodGraphBlocks all volumeLoss)
    (hrho : 0 < rho) :
    volume prepared.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
      256 * pureWZ2OrdinaryPaperOrderSourceHeightCost rho hrho *
        ∑ index : Fin residueData.selected.card,
          (data.rich
            (residueData.selectedIndex index)).heightLift.shading.mass := by
  calc
    _ ≤ 4 * pureWZ2OrdinaryPaperOrderSourceHeightCost rho hrho *
        ∑ index : Fin data.indexCount,
          (data.rich index).heightLift.shading.mass :=
      data.aggregate_source_window_mass_bound hregularizedGood hrho
    _ ≤ 4 * pureWZ2OrdinaryPaperOrderSourceHeightCost rho hrho *
        (64 * ∑ index : Fin residueData.selected.card,
          (data.rich
            (residueData.selectedIndex index)).heightLift.shading.mass) := by
      gcongr
      exact residueData.total_mass_le
    _ = 256 * pureWZ2OrdinaryPaperOrderSourceHeightCost rho hrho *
        ∑ index : Fin residueData.selected.card,
          (data.rich
            (residueData.selectedIndex index)).heightLift.shading.mass := by ring

/-- Convert the same-relative-density lower bound into the exact source-window
mass budget needed after regularized-block and residue selection.  This is a
pure scale inequality followed by the first-sticky multiplicity comparison;
no coarse-shading volume is introduced. -/
theorem PureWZ2SourceCarrierPreparation.final_source_window_mass_of_relative_budget
    {sigma inputLoss delta rho middleLoss stickyLoss secondEta finalLoss
      structuralLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (hrhoSmall : twoScale.rhoRequested.1 ≤ 1 / 12)
    (hsecondFraction :
      Kakeya.realRpowENN twoScale.rhoRequested.1 secondEta ≤
        wz2PaperPureRefinementFraction
          twoScale.rhoRequested.1 logExponent)
    (hcoarseSigma : twoScale.coarseLoss ≤ sigma)
    (hrho : 0 < rho)
    (hpower :
      512 * pureWZ2OrdinaryPaperOrderSourceHeightCost rho hrho *
          Kakeya.realRpowENN delta structuralLoss ≤
        Kakeya.realRpowENN rho
            (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
          wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta inputLoss *
          pureWZ2SourceHorizontalRichFloor rho finalLoss) :
    (256 * pureWZ2OrdinaryPaperOrderSourceHeightCost rho hrho) *
          (Kakeya.realRpowENN delta structuralLoss *
            (wz1PaperBodyFamily source.family).mass) ≤
      volume prepared.shadow.union *
        (twoScale.coarse.fineMultiplicity : ENNReal) *
        pureWZ2SourceHorizontalRichFloor rho finalLoss := by
  have hrelative := prepared.relative_mass_structural_lower
    hrhoSmall hsecondFraction hcoarseSigma
  have hscaled :
      (2 : ENNReal) *
          ((256 * pureWZ2OrdinaryPaperOrderSourceHeightCost rho hrho) *
            (Kakeya.realRpowENN delta structuralLoss *
              (wz1PaperBodyFamily source.family).mass)) ≤
        2 * (volume prepared.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss) := by
    calc
      _ = (512 * pureWZ2OrdinaryPaperOrderSourceHeightCost rho hrho *
            Kakeya.realRpowENN delta structuralLoss) *
          (wz1PaperBodyFamily source.family).mass := by ring
      _ ≤ (Kakeya.realRpowENN rho
              (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
            wz2PaperPureRefinementFraction delta logExponent *
            Kakeya.realRpowENN delta inputLoss *
            pureWZ2SourceHorizontalRichFloor rho finalLoss) *
          (wz1PaperBodyFamily source.family).mass := by gcongr
      _ = (Kakeya.realRpowENN rho
              (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
            (wz2PaperPureRefinementFraction delta logExponent *
              (Kakeya.realRpowENN delta inputLoss *
                (wz1PaperBodyFamily source.family).mass))) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss := by ring
      _ ≤ (2 * (volume prepared.shadow.union *
            (twoScale.coarse.fineMultiplicity : ENNReal))) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss := by gcongr
      _ = 2 * (volume prepared.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss) := by ring
  exact (ENNReal.mul_le_mul_iff_right
    (show (2 : ENNReal) ≠ 0 by norm_num)
    (show (2 : ENNReal) ≠ ⊤ by norm_num)).mp hscaled

/-
Obsolete coarse-pullback final-mass chain. The final ordinary shading is the
height-only source lift, whose local lower bound is now provided by
`PureWZ2OrdinaryPaperOrderRichGraphData.source_window_mass_bound`.

/-- One actual paper-order graph shadow controls its complete rich-height
lift after paying only the internal Lemma-23 logarithmic and height costs. -/
theorem PureWZ2OrdinaryPaperOrderRichGraphData.graph_height_mass_bound_uniform
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {prepared : PureWZ2OrdinaryPaperOrderPreparationData carriers}
    {graphData : PureWZ2OrdinaryPaperOrderGraphData
      (normalEta := normalEta) prepared}
    (data : PureWZ2OrdinaryPaperOrderRichGraphData
      (finalLoss := finalLoss) (theoremEta := theoremEta) graphData)
    (hextraPower : (graphData.graph.residue.extraCost : ℝ) ≤
      Real.rpow prepared.prep.graphScale (-extraLoss)) :
    volume prepared.prep.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
      PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss * data.heightLift.shading.mass := by
  let floor := pureWZ2SourceHorizontalRichFloor rho finalLoss
  have hpopular : volume carriers.sourceWindow.shading.union ≤
      (2 * carriers.outerPopular.popular.bins : ENNReal) *
        volume carriers.outerPopular.popular.shading.union := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat,
      carriers.outerPopular.popularWindow_supply] using
        carriers.source_volume_retention
  have hfloor : floor ≤ (data.rich.heightIndices.card : ENNReal) := by
    have hfloorEq : floor = Kakeya.realRpowENN
        data.ready.ready.deltaGraph (finalLoss - 1) := by
      dsimp only [floor]
      unfold pureWZ2SourceHorizontalRichFloor
      rw [data.ready.ready.deltaGraph_eq, prepared.prep.graphScale_eq]
    rw [hfloorEq]
    simpa [data.rich.heightIndices_card] using data.rich.richF_card
  have hpopularLayer : volume carriers.outerPopular.popular.shading.union ≤
      2 * (carriers.outerPopular.popular.heightIndices.card : ENNReal) *
        carriers.outerPopular.popular.layerMass := by
    rw [carriers.outerPopular.popular.volume_eq_sum]
    calc
      (∑ heightIndex ∈ carriers.outerPopular.popular.heightIndices,
          volume (carriers.sourceWindow.shading.union ∩
            wz1Lemma23HeightSlab prepared.prep.graphScale heightIndex)) ≤
        ∑ _heightIndex ∈ carriers.outerPopular.popular.heightIndices,
          2 * carriers.outerPopular.popular.layerMass := by
        exact Finset.sum_le_sum fun heightIndex hheight =>
          (carriers.outerPopular.popular.layer_volume_band
            heightIndex hheight).2
      _ = 2 * (carriers.outerPopular.popular.heightIndices.card : ENNReal) *
          carriers.outerPopular.popular.layerMass := by
        simp [Finset.sum_const]
        ring
  have hweightedMass :
      floor * volume carriers.sourceWindow.shading.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) ≤
        (4 * carriers.outerPopular.popular.bins : ENNReal) *
          (carriers.outerPopular.popular.heightIndices.card : ENNReal) *
            data.heightLift.shading.mass := by
    calc
      floor * volume carriers.sourceWindow.shading.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) ≤
        floor * ((2 * carriers.outerPopular.popular.bins : ENNReal) *
          volume carriers.outerPopular.popular.shading.union) *
            (twoScale.coarse.fineMultiplicity : ENNReal) := by gcongr
      _ ≤ floor * ((2 * carriers.outerPopular.popular.bins : ENNReal) *
          (2 * (carriers.outerPopular.popular.heightIndices.card : ENNReal) *
            carriers.outerPopular.popular.layerMass)) *
            (twoScale.coarse.fineMultiplicity : ENNReal) := by gcongr
      _ ≤ (data.rich.heightIndices.card : ENNReal) *
          ((2 * carriers.outerPopular.popular.bins : ENNReal) *
            (2 * (carriers.outerPopular.popular.heightIndices.card : ENNReal) *
              carriers.outerPopular.popular.layerMass)) *
            (twoScale.coarse.fineMultiplicity : ENNReal) := by gcongr
      _ = (4 * carriers.outerPopular.popular.bins : ENNReal) *
          (carriers.outerPopular.popular.heightIndices.card : ENNReal) *
          ((twoScale.coarse.fineMultiplicity : ENNReal) *
            ((data.rich.heightIndices.card : ENNReal) *
              carriers.outerPopular.popular.layerMass)) := by ring
      _ ≤ (4 * carriers.outerPopular.popular.bins : ENNReal) *
          (carriers.outerPopular.popular.heightIndices.card : ENNReal) *
            data.heightLift.shading.mass := by
        exact mul_le_mul_left' data.source_mass_lower
          ((4 * carriers.outerPopular.popular.bins : ENNReal) *
            (carriers.outerPopular.popular.heightIndices.card : ENNReal))
  have hbins : (4 * carriers.outerPopular.popular.bins : ENNReal) ≤
      Kakeya.realRpowENN prepared.prep.graphScale (-extraLoss) := by
    rw [prepared.prep.graphScale_eq]
    exact carriers.outerPopular.bins_power_bound
      (by
        have hgraph : 0 < 256 * rho := prepared.prep.graphScale_pos
        have hgraphOne : 256 * rho ≤ 1 := prepared.prep.graphScale_one
        exact hgraph)
  have hheight :
      (carriers.outerPopular.popular.heightIndices.card : ENNReal) ≤
        PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho := by
    have hreal := wz1Lemma23_height_layer_count
      carriers.outerPopular.popular.graphScale_pos prepared.prep.graphScale_one
      carriers.outerPopular.popularWindow.windowed.global_cells_window
    have henn := ENNReal.natCast_le_ofReal
      carriers.outerPopular.popular.heightIndices_nonempty.card_ne_zero |>.mpr
        (by
          have hsubset : carriers.outerPopular.popular.heightIndices ⊆
              wz1Lemma23SnappedHeights
                carriers.outerPopular.popularWindow.windowed.global.cells := by
            intro heightIndex hheight
            have hglobal : heightIndex ∈
                carriers.outerPopular.popularWindow.windowed.global.heightIndices := by
              rw [carriers.outerPopular.popularWindow.windowed.global.heightIndices_eq]
              exact carriers.outerPopular.popular.heightIndices_subset hheight
            have hlayerNonempty :=
              carriers.outerPopular.popularWindow.windowed.global.layerCells_nonempty
                heightIndex hglobal
            rcases hlayerNonempty with ⟨cell, hcell⟩
            exact Finset.mem_image.mpr ⟨cell, by
              rw [carriers.outerPopular.popularWindow.windowed.global.cells_eq]
              exact Finset.mem_biUnion.mpr ⟨heightIndex, hglobal, hcell⟩,
              carriers.outerPopular.popularWindow.windowed.global.layer_height
                heightIndex hglobal cell hcell⟩
          exact (show (carriers.outerPopular.popular.heightIndices.card : ℝ) ≤
              ((wz1Lemma23SnappedHeights
                carriers.outerPopular.popularWindow.windowed.global.cells).card : ℝ) by
                exact_mod_cast Finset.card_le_card hsubset).trans hreal)
    simpa [PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap,
      prepared.prep.graphScale_eq] using henn
  have hcost :
      (4 * carriers.outerPopular.popular.bins : ENNReal) *
          (carriers.outerPopular.popular.heightIndices.card : ENNReal) ≤
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss := by
    calc
      _ ≤ Kakeya.realRpowENN prepared.prep.graphScale (-extraLoss) *
          PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap rho := by
        gcongr
      _ = PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss := by
        rw [prepared.prep.graphScale_eq]
        unfold PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
        rfl
  calc
    volume carriers.sourceWindow.shading.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) * floor =
        floor * volume carriers.sourceWindow.shading.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) := by ring
    _ ≤ (4 * carriers.outerPopular.popular.bins : ENNReal) *
          (carriers.outerPopular.popular.heightIndices.card : ENNReal) *
            data.heightLift.shading.mass := hweightedMass
    _ ≤ PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss * data.heightLift.shading.mass := by gcongr

/-- Continue the exact paper-order coarse-pullback supply through graph
popularity and Lemma 23's internal height popularity.  The first `Z_S` cost
is the separate factor `outerCost`; `heightRetentionCost` pays only for the
later `Z_popular` and `Z_lin` steps. -/
theorem PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData.aggregate_height_mass_bound_via_coarse_pullback
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {firstPullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation firstPullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    (data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss)
    (hbad :
      2 * ((safe.blocks.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) ≤
        ∑ block : {block // block ∈ safe.blocks},
          volume (all.graphPreparation block).prep.shadow.union)
    (outerCost : ENNReal)
    (houterCost : ∀ block : {block // block ∈ safe.blocks},
      (2 * (family.carrierData block).outerPopular.popular.bins : ENNReal) ≤
        outerCost)
    (hextraPower : ∀ index : Fin data.indexCount,
      ((data.graphData index).graph.residue.extraCost : ℝ) ≤
        Real.rpow
          (all.graphPreparation (data.safeBlock index)).prep.graphScale
          (-extraLoss)) :
    volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
          volume twoScale.coarse.refined.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
      4 * outerCost *
        pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss *
        (∑ index : Fin data.indexCount,
          (data.rich index).heightLift.shading.mass) *
        volume twoScale.coarse.croppedCoarseShading.union := by
  let cost : ENNReal :=
    pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss
  let heightCost : ENNReal :=
    PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
      rho extraLoss
  let multiplicity : ENNReal := twoScale.coarse.fineMultiplicity
  let floor : ENNReal := pureWZ2SourceHorizontalRichFloor rho finalLoss
  let coarseVolume : ENNReal :=
    volume twoScale.coarse.croppedCoarseShading.union
  let allGraph := ∑ block : {block // block ∈ safe.blocks},
    volume (all.graphPreparation block).prep.shadow.union
  let goodGraph := ∑ block ∈
      pureWZ2OrdinaryPaperOrderGoodGraphBlocks all volumeLoss,
    volume (all.graphPreparation block).prep.shadow.union
  have hallRaw := all.aggregate_volume_supply_le_via_coarse_pullback
  have hweighted :
      2 * ∑ block : {block // block ∈ safe.blocks},
          (2 * (family.carrierData block).outerPopular.popular.bins : ℕ) *
            (cost * (volume (all.graphPreparation block).prep.shadow.union *
              coarseVolume)) ≤
        2 * outerCost * cost * allGraph * coarseVolume := by
    calc
      2 * ∑ block : {block // block ∈ safe.blocks},
          (2 * (family.carrierData block).outerPopular.popular.bins : ℕ) *
            (cost * (volume (all.graphPreparation block).prep.shadow.union *
              coarseVolume)) ≤
        2 * ∑ block : {block // block ∈ safe.blocks},
          outerCost *
            (cost * (volume (all.graphPreparation block).prep.shadow.union *
              coarseVolume)) := by
        gcongr with block
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using houterCost block
      _ = 2 * outerCost * cost * allGraph * coarseVolume := by
        calc
          2 * ∑ block : {block // block ∈ safe.blocks},
              outerCost *
                (cost * (volume
                  (all.graphPreparation block).prep.shadow.union *
                    coarseVolume)) =
            ∑ block : {block // block ∈ safe.blocks},
              (2 * outerCost * cost * coarseVolume) *
                volume (all.graphPreparation block).prep.shadow.union := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro block _
              ring
          _ = (2 * outerCost * cost * coarseVolume) * allGraph := by
            rw [Finset.mul_sum]
          _ = 2 * outerCost * cost * allGraph * coarseVolume := by ring
  have hall : volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
          volume twoScale.coarse.refined.union ≤
        2 * outerCost * cost * allGraph * coarseVolume := by
    exact hallRaw.trans (by simpa [cost, coarseVolume] using hweighted)
  have hgood : allGraph ≤ 2 * goodGraph := by
    simpa [allGraph, goodGraph] using
      all.goodGraphBlocks_retains_half hbad
  have hgoodIndexed : goodGraph =
      ∑ index : Fin data.indexCount,
        volume (all.graphPreparation
          (data.safeBlock index)).prep.shadow.union := by
    symm
    dsimp only [goodGraph]
    apply Finset.sum_bij (fun index _ => data.safeBlock index)
    · intro index _
      exact data.block_mem index
    · intro first _ second _ heq
      exact data.safeBlock_injective heq
    · intro block hblock
      rcases data.block_surjective block hblock with ⟨index, heq⟩
      exact ⟨index, Finset.mem_univ index, heq⟩
    · intro _index _
      rfl
  have hlocal :
      (∑ index : Fin data.indexCount,
          volume (all.graphPreparation
            (data.safeBlock index)).prep.shadow.union) *
          multiplicity * floor ≤
        heightCost * ∑ index : Fin data.indexCount,
          (data.rich index).heightLift.shading.mass := by
    calc
      _ = ∑ index : Fin data.indexCount,
          (volume (all.graphPreparation
              (data.safeBlock index)).prep.shadow.union *
            multiplicity * floor) := by
        rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ ∑ index : Fin data.indexCount,
          heightCost * (data.rich index).heightLift.shading.mass := by
        exact Finset.sum_le_sum fun index _ => by
          simpa [heightCost, multiplicity, floor] using
            (data.rich index).graph_height_mass_bound_uniform
              (hextraPower index)
      _ = heightCost * ∑ index : Fin data.indexCount,
          (data.rich index).heightLift.shading.mass := by
        rw [Finset.mul_sum]
  calc
    volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
          volume twoScale.coarse.refined.union * multiplicity * floor ≤
        (2 * outerCost * cost * allGraph * coarseVolume) *
          multiplicity * floor := by gcongr
    _ ≤ (2 * outerCost * cost * (2 * goodGraph) * coarseVolume) *
          multiplicity * floor := by gcongr
    _ = 4 * outerCost * cost * (goodGraph * multiplicity * floor) *
          coarseVolume := by ring
    _ = 4 * outerCost * cost *
        ((∑ index : Fin data.indexCount,
          volume (all.graphPreparation
            (data.safeBlock index)).prep.shadow.union) *
          multiplicity * floor) * coarseVolume := by rw [hgoodIndexed]
    _ ≤ 4 * outerCost * cost *
        (heightCost * ∑ index : Fin data.indexCount,
          (data.rich index).heightLift.shading.mass) * coarseVolume := by
      gcongr
    _ = 4 * outerCost *
        pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss *
        (∑ index : Fin data.indexCount,
          (data.rich index).heightLift.shading.mass) *
        volume twoScale.coarse.croppedCoarseShading.union := by
      simp only [cost, heightCost, coarseVolume]
      ring

/-- The fixed final residue supplied by the paper-order producer inherits the
aggregate height-mass bound. -/
theorem PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData.PureWZ2OrdinaryPaperOrderBlockResidueData.height_mass_bound_via_coarse_pullback
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {firstPullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation firstPullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    {data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss}
    (residueData :
      PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData.PureWZ2OrdinaryPaperOrderBlockResidueData
        data)
    (hbad :
      2 * ((safe.blocks.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) ≤
        ∑ block : {block // block ∈ safe.blocks},
          volume (all.graphPreparation block).prep.shadow.union)
    (outerCost : ENNReal)
    (houterCost : ∀ block : {block // block ∈ safe.blocks},
      (2 * (family.carrierData block).outerPopular.popular.bins : ENNReal) ≤
        outerCost)
    (hextraPower : ∀ index : Fin data.indexCount,
      ((data.graphData index).graph.residue.extraCost : ℝ) ≤
        Real.rpow
          (all.graphPreparation (data.safeBlock index)).prep.graphScale
          (-extraLoss)) :
    volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
          volume twoScale.coarse.refined.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
      256 * outerCost *
        pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss *
        (∑ index : Fin residueData.selected.card,
          (data.rich
            (residueData.selectedIndex index)).heightLift.shading.mass) *
        volume twoScale.coarse.croppedCoarseShading.union := by
  calc
    volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
          volume twoScale.coarse.refined.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
      4 * outerCost *
        pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
        PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
          rho extraLoss *
        (∑ index : Fin data.indexCount,
          (data.rich index).heightLift.shading.mass) *
        volume twoScale.coarse.croppedCoarseShading.union :=
      data.aggregate_height_mass_bound_via_coarse_pullback
        hbad outerCost houterCost hextraPower
    _ ≤ 4 * outerCost *
          pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho extraLoss *
          (64 * ∑ index : Fin residueData.selected.card,
            (data.rich
              (residueData.selectedIndex index)).heightLift.shading.mass) *
          volume twoScale.coarse.croppedCoarseShading.union := by
        gcongr
        exact residueData.total_mass_le
    _ = 256 * outerCost *
          pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho extraLoss *
          (∑ index : Fin residueData.selected.card,
            (data.rich
              (residueData.selectedIndex index)).heightLift.shading.mass) *
          volume twoScale.coarse.croppedCoarseShading.union := by ring

/-- Select the final mod-64 class after the paper-order graph construction,
retaining both the outer `Z_S` cost and the internal Lemma-23 height cost. -/
theorem PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData.selectResidue_height_mass_bound_via_coarse_pullback
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {firstPullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation firstPullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    (data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss)
    (hbad :
      2 * ((safe.blocks.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss)) ≤
        ∑ block : {block // block ∈ safe.blocks},
          volume (all.graphPreparation block).prep.shadow.union)
    (outerCost : ENNReal)
    (houterCost : ∀ block : {block // block ∈ safe.blocks},
      (2 * (family.carrierData block).outerPopular.popular.bins : ENNReal) ≤
        outerCost)
    (hextraPower : ∀ index : Fin data.indexCount,
      ((data.graphData index).graph.residue.extraCost : ℝ) ≤
        Real.rpow
          (all.graphPreparation (data.safeBlock index)).prep.graphScale
          (-extraLoss)) :
    ∃ residueData :
        PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData.PureWZ2OrdinaryPaperOrderBlockResidueData
          data,
      volume prepared.shadow.union *
            twoScale.fine.balanced.cellMass *
            volume twoScale.coarse.refined.union *
            (twoScale.coarse.fineMultiplicity : ENNReal) *
            pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
        256 * outerCost *
          pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho extraLoss *
          (∑ index : Fin residueData.selected.card,
            (data.rich
              (residueData.selectedIndex index)).heightLift.shading.mass) *
          volume twoScale.coarse.croppedCoarseShading.union := by
  rcases data.selectResidue with ⟨residueData⟩
  exact ⟨residueData, residueData.height_mass_bound_via_coarse_pullback
    hbad outerCost houterCost hextraPower⟩

/-- Cancel the common paper-order graph, height, and coarse-volume costs and
apply the same-extremizer grain refinement to the selected residue family. -/
theorem PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData.PureWZ2OrdinaryPaperOrderBlockResidueData.toOneScaleOfCoarsePullbackBudgets
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss structuralLoss extraLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {firstPullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation firstPullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {family : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData family}
    {data : PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData
      (finalLoss := finalLoss) (normalEta := normalEta)
      (theoremEta := theoremEta) all volumeLoss}
    (residueData :
      PureWZ2OrdinaryPaperOrderGraphGoodBlockFamilyData.PureWZ2OrdinaryPaperOrderBlockResidueData
        data)
    (outerCost : ENNReal)
    (houterCostPos : 0 < outerCost)
    (houterCostTop : outerCost ≠ ⊤)
    (hinputStructural : inputLoss ≤ structuralLoss)
    (hstructuralFinal : structuralLoss ≤ finalLoss)
    (grainProducer :
      ∀ targetFamily : Kakeya.Streamlined.TubeFamily delta,
        ∀ targetShading : WZ1PaperTubeShading targetFamily,
          WZ1PaperIsLineClass targetFamily →
          WZ2PaperCroppedIsExtremal
              sigma structuralLoss targetFamily targetShading →
            Nonempty
              (PureWZ2GrainRefinementData targetShading sigma finalLoss))
    (haggregate :
      volume prepared.shadow.union *
            twoScale.fine.balanced.cellMass *
            volume twoScale.coarse.refined.union *
            (twoScale.coarse.fineMultiplicity : ENNReal) *
            pureWZ2SourceHorizontalRichFloor rho finalLoss ≤
        256 * outerCost *
          pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho extraLoss *
          (∑ index : Fin residueData.selected.card,
            (data.rich
              (residueData.selectedIndex index)).heightLift.shading.mass) *
          volume twoScale.coarse.croppedCoarseShading.union)
    (hfinalAbsorb :
      (256 * outerCost *
          pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho extraLoss) *
          (Kakeya.realRpowENN delta structuralLoss *
            (wz1PaperBodyFamily source.family).mass) *
          volume twoScale.coarse.croppedCoarseShading.union ≤
        volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
          volume twoScale.coarse.refined.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss) :
    Nonempty (PureWZ2LocallyLinearOneScaleData source finalLoss
      (pureWZ2SourceHorizontalFinalScale rho)) := by
  let common : ENNReal :=
    256 * outerCost *
      pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
      PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
        rho extraLoss *
      volume twoScale.coarse.croppedCoarseShading.union
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hvolumeCostPos : 0 <
      pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss :=
    pureWZ2SourceHorizontalVolumeCost_pos hrho source.extremal.delta_pos
  have hheightCostPos : 0 <
      PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
        rho extraLoss := by
    unfold PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
      PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap
    have hscale : 0 < 256 * rho := by positivity
    have hpower : 0 < Real.rpow (256 * rho) (-extraLoss) :=
      Real.rpow_pos_of_pos hscale _
    have hroot : 0 < Real.sqrt (256 * rho) := Real.sqrt_pos.mpr hscale
    positivity
  have hcoarseVolumePos : 0 < volume
      twoScale.coarse.croppedCoarseShading.union := by
    have hpowerPos : 0 < Kakeya.realRpowENN
        twoScale.rhoRequested.1 (sigma + twoScale.coarseLoss) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos
        twoScale.coarseGrains.extremal.delta_pos _)
    exact hpowerPos.trans_le twoScale.coarse.coarse_volume_lower
  have hcommonZero : common ≠ 0 := by
    dsimp only [common]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (by norm_num) houterCostPos.ne') hvolumeCostPos.ne')
        hheightCostPos.ne')
      hcoarseVolumePos.ne'
  have hvolumeCostTop :
      pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss ≠ ⊤ :=
    pureWZ2SourceHorizontalVolumeCost_ne_top _ _ _ _
  have hheightCostTop :
      PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
        rho extraLoss ≠ ⊤ := by
    unfold PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
      PureWZ2SourceHorizontalGoodBlockFamilyData.snappedHeightCap
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hcoarseVolumeTop : volume
      twoScale.coarse.croppedCoarseShading.union ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (by simp [Kakeya.realRpowENN])
      twoScale.coarse.coarse_extremal.volume_upper
  have hcommonTop : common ≠ ⊤ := by
    dsimp only [common]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num) houterCostTop) hvolumeCostTop)
        hheightCostTop)
      hcoarseVolumeTop
  have hdenseBudget :
      Kakeya.realRpowENN delta structuralLoss *
          (wz1PaperBodyFamily source.family).mass ≤
        ∑ index : Fin residueData.selected.card,
          (data.rich
            (residueData.selectedIndex index)).heightLift.shading.mass := by
    have hscaled : common *
          (Kakeya.realRpowENN delta structuralLoss *
            (wz1PaperBodyFamily source.family).mass) ≤
        common * ∑ index : Fin residueData.selected.card,
          (data.rich
            (residueData.selectedIndex index)).heightLift.shading.mass := by
      calc
      common * (Kakeya.realRpowENN delta structuralLoss *
            (wz1PaperBodyFamily source.family).mass) =
        (256 * outerCost *
          pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho extraLoss) *
          (Kakeya.realRpowENN delta structuralLoss *
            (wz1PaperBodyFamily source.family).mass) *
          volume twoScale.coarse.croppedCoarseShading.union := by
        dsimp only [common]
        ring
      _ ≤
        volume prepared.shadow.union *
          twoScale.fine.balanced.cellMass *
          volume twoScale.coarse.refined.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss := hfinalAbsorb
      _ ≤ 256 * outerCost *
          pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho extraLoss *
          (∑ index : Fin residueData.selected.card,
            (data.rich
              (residueData.selectedIndex index)).heightLift.shading.mass) *
          volume twoScale.coarse.croppedCoarseShading.union := haggregate
      _ = common * ∑ index : Fin residueData.selected.card,
          (data.rich
            (residueData.selectedIndex index)).heightLift.shading.mass := by
        dsimp only [common]
        ring
    exact (ENNReal.mul_le_mul_iff_right hcommonZero hcommonTop).mp hscaled
  exact residueData.toOneScaleOfGrainProducer
    hinputStructural hstructuralFinal grainProducer
    (residueData.dense_of_sum_mass hdenseBudget)

-/

/-- Assemble the paper-order ordinary one-scale output from a same-block
graph-readiness certificate and one source-relative numerical absorption.
The final density is derived internally from `Z_lin ⊆ Z_S`; it is not a
dependent callback on the constructed graph or residue family. -/
theorem PureWZ2SourceCarrierPreparation.toOneScaleOfPaperOrderBudgets
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      theoremEta volumeLoss constantLoss extraLoss structuralLoss secondEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hfinal : 0 < finalLoss) (hfinalOne : finalLoss < 1)
    (hfinalSigma : finalLoss / 2 < sigma)
    (hnormalEta : 0 < normalEta) (hnormalEtaSigma : 4 * normalEta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) normalEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (hlocalizationAbsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1)
    (hmargin : 4 * rho ≤ Real.sqrt rho)
    (hCOne : (1 : ENNReal) ≤
      10 * Kakeya.realRpowENN delta (-inputLoss))
    (hCpower : ∀
      (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
      (carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
      (all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData carriers)
      (block : {block // block ∈ safe.blocks}),
      (10 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
        Real.rpow (all.graphPreparation block).prep.graphScale
          (-constantLoss))
    (hextraPower : ∀
      (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
      (carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
      (all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData carriers)
      (block : {block // block ∈ safe.blocks})
      (graphData : PureWZ2OrdinaryPaperOrderGraphData
        (normalEta := normalEta) (all.graphPreparation block)),
      (graphData.graph.residue.extraCost : ℝ) ≤
        Real.rpow (all.graphPreparation block).prep.graphScale (-extraLoss))
    (hedgeAbsorb : ∀
      (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
      (carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
      (all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData carriers)
      (block : {block // block ∈ safe.blocks}),
      Real.rpow (wz1Lemma23Theorem22Scale
          (all.graphPreparation block).prep.graphScale) (theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow (all.graphPreparation block).prep.graphScale
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss))
    (hKatzTao : ∀
      (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
      (carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
      (all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData carriers)
      (block : {block // block ∈ safe.blocks}),
      (4 : ENNReal) ≤ Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale
          (all.graphPreparation block).prep.graphScale) (-theoremEta))
    (hprojection : ∀
      (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
      (carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
      (all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData carriers)
      (block : {block // block ∈ safe.blocks})
      (graphData : PureWZ2OrdinaryPaperOrderGraphData
        (normalEta := normalEta) (all.graphPreparation block))
      (data : PureWZ2SourceHorizontalReadyGraph
        (theoremEta := theoremEta) graphData.sharp),
      WZ1Proposition8_9AlternativeAUnion
        data.ready.deltaGraph finalLoss
        data.common.F data.common.G₁ data.common.G₁)
    (hscaleOne : 5 * (256 * rho) ≤ 1)
    (hlengthLower :
      Real.rpow (5 * (256 * rho)) (1 / 2 + finalLoss) ≤
        twoScale.sqrtRequested.1)
    (hregularizedGood : ∀
      (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
      (carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
      (all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData carriers),
      pureWZ2OrdinaryPaperOrderRegularizedBlocks safe ⊆
        pureWZ2OrdinaryPaperOrderGoodGraphBlocks all volumeLoss)
    (hsecondFraction :
      Kakeya.realRpowENN twoScale.rhoRequested.1 secondEta ≤
        wz2PaperPureRefinementFraction
          twoScale.rhoRequested.1 logExponent)
    (hcoarseSigma : twoScale.coarseLoss ≤ sigma)
    (hinputStructural : inputLoss ≤ structuralLoss)
    (hstructuralFinal : structuralLoss ≤ finalLoss)
    (grainProducer :
      ∀ targetFamily : Kakeya.Streamlined.TubeFamily delta,
        ∀ targetShading : WZ1PaperTubeShading targetFamily,
          WZ1PaperIsLineClass targetFamily →
          WZ2PaperCroppedIsExtremal
              sigma structuralLoss targetFamily targetShading →
            Nonempty
              (PureWZ2GrainRefinementData targetShading sigma finalLoss))
    (hsourceDensityPower : ∀ hrho : 0 < rho,
      512 * pureWZ2OrdinaryPaperOrderSourceHeightCost rho hrho *
          Kakeya.realRpowENN delta structuralLoss ≤
        Kakeya.realRpowENN rho
            (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
          wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta inputLoss *
          pureWZ2SourceHorizontalRichFloor rho finalLoss) :
    Nonempty (PureWZ2LocallyLinearOneScaleData source finalLoss
      (pureWZ2SourceHorizontalFinalScale rho)) := by
  rcases prepared.balancedSafeBlockFamily hmargin with ⟨safe⟩
  rcases safe.ordinaryPaperOrderCarriers with ⟨carriers⟩
  rcases carriers.prepareAllBlocks hbridge hgraphOne hheightAbsorb with ⟨all⟩
  have hgood :
      (pureWZ2OrdinaryPaperOrderGoodGraphBlocks all volumeLoss).Nonempty :=
    safe.regularizedBlocks_nonempty.mono
      (hregularizedGood safe carriers all)
  rcases all.buildGraphGoodBlocks hbridge hsigma hsigmaOne hfinal hfinalOne
      hfinalSigma hnormalEta hnormalEtaSigma hcertificateOne hsourceFloor
      hlocalPower hglobalPower hPlanarSmall hrootSmall20 hlocalizationAbsorb
      hCOne (hCpower safe carriers all) (hextraPower safe carriers all)
      (hedgeAbsorb safe carriers all) (hKatzTao safe carriers all)
      (hprojection safe carriers all) hscaleOne hlengthLower hgood with
    ⟨graphFamily⟩
  rcases graphFamily.selectResidue with ⟨residueData⟩
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hrhoSmall : twoScale.rhoRequested.1 ≤ 1 / 12 := by
    rw [twoScale.rhoRequested_eq]
    nlinarith [hgraphOne]
  have haggregate := residueData.selected_source_window_mass_bound
    (hregularizedGood safe carriers all) hrho
  have hfinal := prepared.final_source_window_mass_of_relative_budget
    hrhoSmall hsecondFraction hcoarseSigma hrho (hsourceDensityPower hrho)
  let common : ENNReal :=
    256 * pureWZ2OrdinaryPaperOrderSourceHeightCost rho hrho
  have hcommonZero : common ≠ 0 := by
    dsimp only [common]
    exact mul_ne_zero (by norm_num)
      (pureWZ2OrdinaryPaperOrderSourceHeightCost_pos rho hrho).ne'
  have hcommonTop : common ≠ ⊤ := by
    dsimp only [common]
    exact ENNReal.mul_ne_top (by norm_num)
      (pureWZ2OrdinaryPaperOrderSourceHeightCost_ne_top rho hrho)
  have hdenseBudget :
      Kakeya.realRpowENN delta structuralLoss *
          (wz1PaperBodyFamily source.family).mass ≤
        ∑ index : Fin residueData.selected.card,
          (graphFamily.rich
            (residueData.selectedIndex index)).heightLift.shading.mass := by
    apply (ENNReal.mul_le_mul_iff_right hcommonZero hcommonTop).mp
    calc
      common * (Kakeya.realRpowENN delta structuralLoss *
          (wz1PaperBodyFamily source.family).mass) ≤
        volume prepared.shadow.union *
          (twoScale.coarse.fineMultiplicity : ENNReal) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss := by
        simpa [common] using hfinal
      _ ≤ common * ∑ index : Fin residueData.selected.card,
          (graphFamily.rich
            (residueData.selectedIndex index)).heightLift.shading.mass := by
        simpa [common] using haggregate
  exact residueData.toOneScaleOfGrainProducer
    hinputStructural hstructuralFinal grainProducer
    (residueData.dense_of_sum_mass hdenseBudget)

/-
Obsolete independent global-power wrapper. The graph-ready input must be
replaced by a same-block all-bin certificate, and final density must be
derived from the source-window height lift rather than a coarse-volume cross.

/-- Paper-order ordinary one-scale production from two numerical power
budgets chosen before the dependent graph and residue data.  The outer
`Z_S` cost remains separate from Lemma 23's internal height-retention cost. -/
theorem PureWZ2SourceCarrierPreparation.toOneScaleOfPaperOrderPowerBudgets
    {sigma inputLoss delta rho middleLoss stickyLoss finalLoss normalEta
      volumeLoss constantLoss extraLoss structuralLoss secondEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hfinal : 0 < finalLoss) (hfinalOne : finalLoss < 1)
    (hfinalSigma : finalLoss / 2 < sigma)
    (hnormalEta : 0 < normalEta) (hnormalEtaSigma : 4 * normalEta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) normalEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (hlocalizationAbsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1)
    (hmargin : 4 * rho ≤ Real.sqrt rho)
    (hCOne : (1 : ENNReal) ≤
      10 * Kakeya.realRpowENN delta (-inputLoss))
    (hCpower : ∀
      (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
      (carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
      (all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData carriers)
      (block : {block // block ∈ safe.blocks}),
      (10 * Kakeya.realRpowENN delta (-inputLoss)).toReal ≤
        Real.rpow (all.graphPreparation block).prep.graphScale
          (-constantLoss))
    (hextraPower : ∀
      (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
      (carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
      (all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData carriers)
      (block : {block // block ∈ safe.blocks})
      (graphData : PureWZ2OrdinaryPaperOrderGraphData
        (normalEta := normalEta) (all.graphPreparation block)),
      (graphData.graph.residue.extraCost : ℝ) ≤
        Real.rpow (all.graphPreparation block).prep.graphScale (-extraLoss))
    (hedgeAbsorb : ∀
      (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
      (carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
      (all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData carriers)
      (block : {block // block ∈ safe.blocks}),
      Real.rpow (wz1Lemma23Theorem22Scale
          (all.graphPreparation block).prep.graphScale)
            (projection.theoremEta - 3) ≤
        (wz1Lemma23EdgeConstant : ℝ)⁻¹ *
          Real.rpow (all.graphPreparation block).prep.graphScale
            (-3 / 2 + 4 * volumeLoss + 4 * constantLoss + 4 * extraLoss))
    (hKatzTao : ∀
      (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
      (carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
      (all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData carriers)
      (block : {block // block ∈ safe.blocks}),
      (4 : ENNReal) ≤ Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale
          (all.graphPreparation block).prep.graphScale)
            (-projection.theoremEta))
    {sourceCostLoss : ℝ}
    (hsourceCostLoss : 0 ≤ sourceCostLoss)
    (hsourceCostCeiling :
      sourceCostLoss ≤ projection.sourceCostLossCeiling)
    (hrhoProjection : rho ≤ projection.rho₀)
    (hsourceCost : ∀
      (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
      (carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
      (all : PureWZ2OrdinaryPaperOrderAllBlockPreparationData carriers)
      (block : {block // block ∈ safe.blocks})
      (graphData : PureWZ2OrdinaryPaperOrderGraphData
        (normalEta := normalEta) (all.graphPreparation block))
      (data : PureWZ2SourceHorizontalReadyGraph
        (theoremEta := projection.theoremEta) graphData.sharp),
      Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN data.ready.deltaGraph (-sourceCostLoss))
    (hscaleOne : 5 * (256 * rho) ≤ 1)
    (hlengthLower :
      Real.rpow (5 * (256 * rho)) (1 / 2 + finalLoss) ≤
        twoScale.sqrtRequested.1)
    (hsecondFraction :
      Kakeya.realRpowENN twoScale.rhoRequested.1 secondEta ≤
        wz2PaperPureRefinementFraction
          twoScale.rhoRequested.1 logExponent)
    (hcoarseSigma : twoScale.coarseLoss ≤ sigma)
    (outerCost : ENNReal) (houterCostPos : 0 < outerCost)
    (houterCostTop : outerCost ≠ ⊤)
    (houterCost : ∀
      (safe : PureWZ2BalancedSafeBlockFamilyData prepared)
      (carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
      (block : {block // block ∈ safe.blocks}),
      (2 * (carriers.carrierData block).outerPopular.popular.bins : ENNReal) ≤
        outerCost)
    (hgraphPower : ∀ safe : PureWZ2BalancedSafeBlockFamilyData prepared,
      4 * outerCost *
          pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          (safe.blocks.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss) *
          volume twoScale.coarse.croppedCoarseShading.union ≤
        Kakeya.realRpowENN rho
            (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss))
    (hinputStructural : inputLoss ≤ structuralLoss)
    (hstructuralFinal : structuralLoss ≤ finalLoss)
    (grainProducer :
      ∀ targetFamily : Kakeya.Streamlined.TubeFamily delta,
        ∀ targetShading : WZ1PaperTubeShading targetFamily,
          WZ1PaperIsLineClass targetFamily →
          WZ2PaperCroppedIsExtremal
              sigma structuralLoss targetFamily targetShading →
            Nonempty
              (PureWZ2GrainRefinementData targetShading sigma finalLoss))
    (hfinalPower :
      2 * (256 * outerCost *
          pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
          PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
            rho extraLoss) *
          Kakeya.realRpowENN delta structuralLoss *
          volume twoScale.coarse.croppedCoarseShading.union ≤
        Kakeya.realRpowENN rho
            (1 + sigma / 2 + middleLoss + stickyLoss / 2 + secondEta) *
          wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta inputLoss *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) *
          Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          pureWZ2SourceHorizontalRichFloor rho finalLoss) :
    Nonempty (PureWZ2LocallyLinearOneScaleData source finalLoss
      (pureWZ2SourceHorizontalFinalScale rho)) := by
  rcases prepared.balancedSafeBlockFamily hmargin with ⟨safe⟩
  rcases safe.ordinaryPaperOrderCarriers with ⟨carriers⟩
  rcases carriers.prepareAllBlocks hbridge hgraphOne hheightAbsorb with ⟨all⟩
  have hgraph := all.goodGraphBudget_of_coarse_pullback
    (normalEta := normalEta) (volumeLoss := volumeLoss)
    (by
      rw [twoScale.rhoRequested_eq]
      nlinarith [hcertificateOne])
    hsecondFraction hcoarseSigma outerCost houterCostPos houterCostTop
    (houterCost safe carriers) (hgraphPower safe)
  have hgood := all.goodGraphBlocks_nonempty hgraph
  rcases all.buildGraphGoodBlocks hbridge hsigma hsigmaOne hfinal hfinalOne
      hfinalSigma hnormalEta hnormalEtaSigma hcertificateOne hsourceFloor
      hlocalPower hglobalPower hPlanarSmall hrootSmall20 hlocalizationAbsorb
      hCOne (hCpower safe carriers all) (hextraPower safe carriers all)
      (hedgeAbsorb safe carriers all) (hKatzTao safe carriers all)
      (fun block graphData data =>
        projection.alternativeA_paperOrder graphData data
          hfinal hfinalOne hsigma hsigmaOne hfinalSigma
          (hsourceCost safe carriers all block graphData data)
          hsourceCostLoss hsourceCostCeiling hrhoProjection)
      hscaleOne hlengthLower hgood with
    ⟨graphFamily⟩
  rcases graphFamily.selectResidue with ⟨residueData⟩
  have haggregate := residueData.height_mass_bound_via_coarse_pullback
    hgraph outerCost (houterCost safe carriers)
    (fun index => hextraPower safe carriers all
      (graphFamily.safeBlock index) (graphFamily.graphData index))
  have hfinalAbsorb := prepared.final_mass_of_coarse_pullback_relative_budget
    (secondEta := secondEta)
    (by
      rw [twoScale.rhoRequested_eq]
      nlinarith [hgraphOne])
    hsecondFraction hcoarseSigma
    (256 * outerCost *
      pureWZ2SourceHorizontalVolumeCost rho delta sigma inputLoss *
      PureWZ2SourceHorizontalGoodBlockFamilyData.heightRetentionCost
        rho extraLoss) hfinalPower
  exact residueData.toOneScaleOfCoarsePullbackBudgets outerCost
    houterCostPos houterCostTop hinputStructural hstructuralFinal
    grainProducer haggregate hfinalAbsorb

-/

end Kakeya.Assouad

end
