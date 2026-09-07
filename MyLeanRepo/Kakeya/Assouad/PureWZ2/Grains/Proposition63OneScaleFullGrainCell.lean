import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FullGrainThreshold
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.MultiScaleLocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63BalancedCellData
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment

/-!
# One-scale local AD to a full-grain good line in one cell

This module instantiates the abstract thresholding/Fubini core on one active
cell of a balanced square-root-scale cover.  The local AD estimate is always
evaluated at an actual point of the current shading, and its direction is
transported to the same plane-map normal at the cell representative.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

attribute [local instance] Classical.propDecidable

/-- An internal AD set has a uniform covering bound on its whole (bounded)
support.  Nine unit intervals cover the built-in window `[-4,4]`. -/
theorem IsADSet1.externalCoveringNumber_le_nine
    {set : Set ℝ} {rho alpha : ℝ} {C : ENNReal}
    (data : IsADSet1 set rho alpha C)
    (hrhoOne : rho ≤ 1) :
    (↑(Metric.externalCoveringNumber (Real.toNNReal rho) set) : ENNReal) ≤
      9 * C * Kakeya.realRpowENN (1 / rho) alpha := by
  let centers : Finset ℝ :=
    {(-4 : ℝ), -3, -2, -1, 0, 1, 2, 3, 4}
  have hcover : set ⊆
      ⋃ center ∈ centers, Metric.closedBall center 1 := by
    intro value hvalue
    have hbounds : value ∈ Set.Icc (-4 : ℝ) 4 :=
      data.2.2.2.2.1 hvalue
    let index : ℤ := Int.floor value
    have hindexLower : -4 ≤ index := by
      rw [Int.le_floor]
      simpa only [Int.cast_neg, Int.cast_ofNat] using hbounds.1
    have hindexUpper : index ≤ 4 := by
      have hfloor : (index : ℝ) ≤ value := Int.floor_le value
      exact_mod_cast hfloor.trans hbounds.2
    have hindexMem : (index : ℝ) ∈ centers := by
      interval_cases index <;> simp [centers]
    have hdistance : dist value (index : ℝ) ≤ 1 := by
      rw [Real.dist_eq, abs_of_nonneg]
      · linarith [Int.lt_floor_add_one value]
      · linarith [Int.floor_le value]
    exact Set.mem_iUnion₂.mpr ⟨(index : ℝ), hindexMem, hdistance⟩
  let piece : ℝ → Set ℝ := fun center =>
    set ∩ Metric.closedBall center 1
  have hsetSubset : set ⊆ ⋃ center ∈ centers, piece center := by
    intro value hvalue
    rcases Set.mem_iUnion₂.mp (hcover hvalue) with
      ⟨center, hcenter, hball⟩
    exact Set.mem_iUnion₂.mpr
      ⟨center, hcenter, ⟨hvalue, hball⟩⟩
  have hpiece : ∀ center ∈ centers,
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
        (piece center)) : ENNReal) ≤
        C * Kakeya.realRpowENN (1 / rho) alpha := by
    intro center _
    have hrhoNonnegative : 0 ≤ rho := data.1.le
    have hscale : (⟨rho, hrhoNonnegative⟩ : NNReal) =
        Real.toNNReal rho := by
      apply Subtype.ext
      simp [Real.toNNReal_of_nonneg hrhoNonnegative]
    rw [← hscale]
    exact data.2.2.2.2.2 rho hrhoNonnegative le_rfl hrhoOne
      center 1 hrhoOne (by norm_num)
  have hunion := Kakeya.Assouad.externalCoveringNumber_biUnion_le_card
    (ε := Real.toNNReal rho) (s := centers) (A := piece) hpiece
  have hmono :
      (↑(Metric.externalCoveringNumber (Real.toNNReal rho) set) : ENNReal) ≤
        (↑(Metric.externalCoveringNumber (Real.toNNReal rho)
          (⋃ center ∈ centers, piece center)) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set hsetSubset
  have hcard : centers.card = 9 := by
    norm_num [centers]
  simpa [hcard, mul_assoc] using hmono.trans hunion

/-- One active square-root cell acquires a full-grain/good-line certificate
from a one-scale local AD output on the same shading and the same plane map.
All final ceiling and loss absorption is exposed through `coverBudget`. -/
theorem proposition63_oneScale_fullGrainFubiniCell_of_cells
    {delta sigma outputLoss queryScale sqrtScale K lineVolume : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (oneScale : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := outputLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point))
    (cells : Proposition63BalancedCellData (scale := sqrtScale)
      oneScale.shading)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ cells.activeCells)
    (hqueryOne : queryScale ≤ 1)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (hplaneUnit : ∀ point ∈ oneScale.shading.union,
      ‖planeMap point‖ = 1)
    (hK : 1 ≤ K)
    (hplaneLipschitz : ∀ first ∈ oneScale.shading.union,
      ∀ second ∈ oneScale.shading.union,
        dist (planeMap first) (planeMap second) ≤
          K * dist first second)
    (coverBudget : ℕ) (hcoverBudgetPos : 0 < coverBudget)
    (hcoverBudget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * K) + 2 : ENNReal) *
            (9 * Kakeya.realRpowENN delta (-outputLoss) *
              Kakeya.realRpowENN (1 / queryScale) (1 - sigma))) ≤
        (coverBudget : ENNReal))
    (hlineVolume : 0 < lineVolume)
    (hlineFloor : ENNReal.ofReal lineVolume ≤ cells.cellMass / 2) :
    Nonempty
      (Proposition63FullGrainFubiniCellData
        (oneScale.shading.union ∩ wz1PaperGridCube sqrtScale cell)
        (planeMap (cells.cellRep cell hcell))
        queryScale (2 * sqrtScale) lineVolume
        (cells.cellMass / 2)
        ((cells.cellMass / 2) / (2 * (coverBudget : ENNReal)))) := by
  let E := oneScale.shading.union ∩ wz1PaperGridCube sqrtScale cell
  let center := cells.cellRep cell hcell
  have hEMeasurable : MeasurableSet E :=
    oneScale.shading.union_measurable.inter
      (wz1PaperGridCube_measurable cell)
  have hEVolume : volume E = cells.cellMass :=
    cells.fine_cell_mass cell hcell
  have hEFinite : volume E ≠ ⊤ := by
    rw [hEVolume]
    exact cells.cellMass_ne_top
  have hcenterE : center ∈ E :=
    ⟨cells.cellRep_in_union cell hcell,
      cells.cellRep_in_cell cell hcell⟩
  have hqueryPos : 0 < queryScale :=
    (oneScale.local_ad center hcenterE.1).1
  have hsqrtPos : 0 < sqrtScale := by
    rw [hsqrtScale]
    exact Real.sqrt_pos.mpr hqueryPos
  have hEball : E ⊆ Metric.closedBall center (2 * sqrtScale) := by
    intro point hpoint
    exact (wz1_paper_grid_cube_diameter_lt_two_rho hsqrtPos
      hpoint.2 hcenterE.2).le
  have hlocalBound : ∀ point ∈ E,
      (↑(Metric.externalCoveringNumber (Real.toNNReal queryScale)
        (scalarProjection (planeMap point)
          (E ∩ Metric.closedBall point sqrtScale))) : ENNReal) ≤
        9 * Kakeya.realRpowENN delta (-outputLoss) *
          Kakeya.realRpowENN (1 / queryScale) (1 - sigma) := by
    intro point hpoint
    have hAD := oneScale.local_ad point hpoint.1
    have hsubset :
        scalarProjection (planeMap point)
            (E ∩ Metric.closedBall point sqrtScale) ⊆
          scalarProjection (planeMap point)
            (oneScale.shading.union ∩
              Metric.closedBall point (Real.sqrt queryScale)) := by
      rintro value ⟨other, hother, rfl⟩
      refine ⟨other, ⟨hother.1.1, ?_⟩, rfl⟩
      simpa [hsqrtScale] using hother.2
    have hrestricted := IsADSet1.mono hAD hsubset
    exact IsADSet1.externalCoveringNumber_le_nine hrestricted hqueryOne
  have htwice : 2 * (cells.cellMass / 2) ≤ volume E := by
    rw [hEVolume]
    exact (ENNReal.mul_div_cancel (by norm_num) (by norm_num)).le
  exact proposition63_fullGrainFubiniCell_of_planeMap
    (rho := queryScale) (radius := sqrtScale) (K := K)
    (lineVolume := lineVolume) hEMeasurable hEFinite hqueryPos
    hsqrtPos hsqrtScale center hcenterE hEball planeMap
    (hplaneUnit center hcenterE.1) hK
    (fun first hfirst second hsecond =>
      hplaneLipschitz first hfirst.1 second hsecond.1)
    (9 * Kakeya.realRpowENN delta (-outputLoss) *
      Kakeya.realRpowENN (1 / queryScale) (1 - sigma))
    (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (by simp [Kakeya.realRpowENN]))
      (by simp [Kakeya.realRpowENN])) hlocalBound
    (cells.cellMass / 2)
    ((cells.cellMass / 2) / (2 * (coverBudget : ENNReal)))
    (ENNReal.div_ne_top cells.cellMass_ne_top (by norm_num)) htwice
    hlineVolume hlineFloor coverBudget hcoverBudgetPos hcoverBudget rfl

/-- Backwards-compatible specialization to the spatial cells of a genuine
balanced Section-6 cover. -/
theorem proposition63_oneScale_fullGrainFubiniCell
    {delta sigma outputLoss queryScale sqrtScale K lineVolume : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (oneScale : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := outputLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point))
    {coarse : Kakeya.Streamlined.TubeFamily sqrtScale}
    {cover : PureWZ2Section6Cover family coarse}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover
      oneScale.shading coarseShading)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ balanced.activeCells)
    (hqueryOne : queryScale ≤ 1)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (hplaneUnit : ∀ point ∈ oneScale.shading.union,
      ‖planeMap point‖ = 1)
    (hK : 1 ≤ K)
    (hplaneLipschitz : ∀ first ∈ oneScale.shading.union,
      ∀ second ∈ oneScale.shading.union,
        dist (planeMap first) (planeMap second) ≤
          K * dist first second)
    (coverBudget : ℕ) (hcoverBudgetPos : 0 < coverBudget)
    (hcoverBudget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * K) + 2 : ENNReal) *
            (9 * Kakeya.realRpowENN delta (-outputLoss) *
              Kakeya.realRpowENN (1 / queryScale) (1 - sigma))) ≤
        (coverBudget : ENNReal))
    (hlineVolume : 0 < lineVolume)
    (hlineFloor : ENNReal.ofReal lineVolume ≤ balanced.cellMass / 2) :
    Nonempty
      (Proposition63FullGrainFubiniCellData
        (oneScale.shading.union ∩ wz1PaperGridCube sqrtScale cell)
        (planeMap (balanced.cellRep cell hcell))
        queryScale (2 * sqrtScale) lineVolume
        (balanced.cellMass / 2)
        ((balanced.cellMass / 2) / (2 * (coverBudget : ENNReal)))) := by
  let cells := Proposition63BalancedCellData.ofBalancedCover balanced
    (hsqrtScale.symm ▸ Real.sqrt_pos.mpr
      ((oneScale.local_ad (balanced.cellRep cell hcell)
        (balanced.cellRep_in_union cell hcell)).1))
  simpa only [cells, Proposition63BalancedCellData.ofBalancedCover,
    Proposition63BalancedCellData.cellRep] using
    proposition63_oneScale_fullGrainFubiniCell_of_cells planeMap oneScale
      cells cell hcell hqueryOne hsqrtScale hplaneUnit hK hplaneLipschitz
      coverBudget hcoverBudgetPos hcoverBudget hlineVolume hlineFloor

end Kakeya.Assouad.PureWZ2

end
