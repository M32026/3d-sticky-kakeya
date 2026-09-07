import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63SequentialReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SelectedCardinalityCancellation
import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers

/-!
# Uniform numerical budget for the Proposition 6.3 line-hit step

The balanced-cell mass appearing in the raw Fubini ledger is not itself a
quantity that can be fixed before the finite Lemma 4.11/4.12 iteration.  This
module isolates the paper-faithful replacement.  Every active coarse cell lies
in the finite literal paper window, so a lower bound for the refined union
volume gives a lower bound for the common balanced-cell mass.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

attribute [local instance] Classical.propDecidable

/-- Every finite `ENNReal` cover requirement has a positive natural
budget.  This keeps the cover cardinality a runtime choice while all loss
exponents and scale thresholds remain preselected. -/
theorem proposition63_exists_positive_nat_cover_budget
    (budget : ENNReal) (hbudgetTop : budget ≠ ⊤) :
    ∃ coverBudget : ℕ, 0 < coverBudget ∧
      budget ≤ (coverBudget : ENNReal) := by
  let realBudget : NNReal := budget.toNNReal
  obtain ⟨coverBudget, hcoverBudget⟩ := exists_nat_ge realBudget
  refine ⟨coverBudget + 1, by omega, ?_⟩
  have budgetEq : (realBudget : ENNReal) = budget := by
    exact ENNReal.coe_toNNReal hbudgetTop
  rw [← budgetEq]
  exact_mod_cast hcoverBudget.trans <| by
    norm_num

/-- The finite paper-grid window always contains the origin cell. -/
theorem proposition63_gridWindow_nonempty
    (scale : ℝ) (hscale : 0 < scale) :
    (wz1PaperGridIndicesInWindow scale hscale).Nonempty := by
  let bound : ℤ := ⌈1 / scale⌉ + 1
  have hceil : 0 ≤ ⌈1 / scale⌉ := by
    have hreal : (0 : ℝ) ≤ (⌈1 / scale⌉ : ℤ) :=
      (show (0 : ℝ) ≤ 1 / scale by positivity).trans
        (Int.le_ceil (1 / scale))
    exact_mod_cast hreal
  have hbound : 0 ≤ bound := by
    dsimp only [bound]
    omega
  have hzero : (0 : ℤ) ∈ Finset.Icc (-bound) bound :=
    Finset.mem_Icc.mpr ⟨by omega, hbound⟩
  refine ⟨((0 : ℤ), ((0 : ℤ), (0 : ℤ))), ?_⟩
  change ((0 : ℤ), ((0 : ℤ), (0 : ℤ))) ∈ Finset.Icc (-bound) bound ×ˢ
    (Finset.Icc (-bound) bound ×ˢ Finset.Icc (-bound) bound)
  apply Finset.mem_product.mpr
  constructor
  · exact hzero
  · apply Finset.mem_product.mpr
    exact ⟨hzero, hzero⟩

/-- Every active cell in a cells Section-6 cover belongs to the fixed
literal paper-grid window at the coarse scale. -/
theorem PureWZ2BalancedCoverData.activeCells_subset_gridWindow
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily scale}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (cells : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hscale : 0 < scale) :
    cells.activeCells ⊆ wz1PaperGridIndicesInWindow scale hscale := by
  intro cell hcell
  let point : Point3 := cellCorner scale cell
  have hpointCell : point ∈ wz1PaperGridCube scale cell :=
    cellCorner_mem_gridCube hscale cell
  have hpointUnion : point ∈ coarseShading.union := by
    rw [cells.coarse_union_eq]
    exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCell⟩
  rcases hpointUnion with ⟨index, hpointCarrier⟩
  have hpointBox : point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
    (coarseShading.subset_body index hpointCarrier).2
  have hwindow := paper_point_gridIndex_in_window hscale hpointBox
  have hindex : wz1PaperGridIndex scale point = cell :=
    (mem_wz1PaperGridCube scale cell point).mp hpointCell
  rwa [hindex] at hwindow

/-- Cardinality form of `activeCells_subset_gridWindow`. -/
theorem PureWZ2BalancedCoverData.activeCells_card_le_gridWindow
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily scale}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (cells : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hscale : 0 < scale) :
    cells.activeCells.card ≤
      (wz1PaperGridIndicesInWindow scale hscale).card :=
  Finset.card_le_card
    (PureWZ2BalancedCoverData.activeCells_subset_gridWindow cells hscale)

/-- A fixed lower bound for the total fine union converts to a fixed lower
bound for the common balanced-cell mass via the finite paper-grid window. -/
theorem PureWZ2BalancedCoverData.gridWindow_cellMass_lower
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily scale}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (cells : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hscale : 0 < scale) (volumeFloor : ENNReal)
    (hfloor : volumeFloor ≤ volume fineShading.union) :
    volumeFloor /
        ((wz1PaperGridIndicesInWindow scale hscale).card : ENNReal) ≤
      cells.cellMass := by
  let windowCount : ENNReal :=
    ((wz1PaperGridIndicesInWindow scale hscale).card : ENNReal)
  have hactive : (cells.activeCells.card : ENNReal) ≤ windowCount := by
    change (cells.activeCells.card : ENNReal) ≤
      ((wz1PaperGridIndicesInWindow scale hscale).card : ENNReal)
    exact_mod_cast
      PureWZ2BalancedCoverData.activeCells_card_le_gridWindow cells hscale
  have hscaled : volumeFloor ≤ windowCount * cells.cellMass := by
    calc
      volumeFloor ≤ volume fineShading.union := hfloor
      _ = (cells.activeCells.card : ENNReal) * cells.cellMass :=
        balanced_cover_fine_union_volume cells hscale
      _ ≤ windowCount * cells.cellMass :=
        mul_le_mul_right' hactive cells.cellMass
  have hwindowZero : windowCount ≠ 0 := by
    have hnonempty := proposition63_gridWindow_nonempty scale hscale
    have hcard : 0 < (wz1PaperGridIndicesInWindow scale hscale).card :=
      Finset.Nonempty.card_pos hnonempty
    simpa [windowCount] using hcard.ne'
  have hwindowTop : windowCount ≠ ⊤ := by
    simp [windowCount]
  apply (ENNReal.div_le_iff hwindowZero hwindowTop).2
  simpa [mul_comm] using hscaled

/-- Cropped extremality gives a union-volume floor after cancelling the fixed
family cardinality between density and point multiplicity.  No local-AD
conclusion is used. -/
theorem Proposition63ExtremalShadingData.union_volume_lower
    {delta sigma outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (state : Proposition63ExtremalShadingData
      (sigma := sigma) (outputLoss := outputLoss) source)
    (hline : WZ1PaperIsLineClass family)
    (hdeltaSmall : delta ≤ 1 / 12) :
    Kakeya.realRpowENN delta (outputLoss + 2) ≤
      volume state.shading.union := by
  let all := Kakeya.Streamlined.TubeSubfamily.fromFinset family Finset.univ
  have hcard : all.family.enncard = family.enncard := by
    simp [all, Kakeya.Streamlined.TubeSubfamily.fromFinset,
      Kakeya.Streamlined.TubeFamily.enncard]
  have hmassLower :
      Kakeya.realRpowENN delta (outputLoss + 2) * family.enncard ≤
        state.shading.mass := by
    have h := selected_cardinality_cancellation state.extremal hline all
      hdeltaSmall
    rwa [hcard] at h
  have hmassUpper : state.shading.mass ≤
      family.enncard * volume state.shading.union := by
    apply mass_le_of_pointMultiplicity_le
    intro point _
    change (state.shading.pointMultiplicity point : ENNReal) ≤
      family.enncard
    let indices : Finset (Fin family.card) :=
      Finset.univ.filter fun index =>
        point ∈ state.shading.carrier index
    have hnat : indices.card ≤ family.card := by
      calc
        indices.card ≤ (Finset.univ : Finset (Fin family.card)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = family.card := by simp
    change (indices.card : ENNReal) ≤ family.enncard
    simpa [Kakeya.Streamlined.TubeFamily.enncard] using hnat
  have hcardZero : family.enncard ≠ 0 := by
    simpa [Kakeya.Streamlined.TubeFamily.enncard] using
      state.extremal.nonempty.ne'
  have hcardTop : family.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  apply (ENNReal.mul_le_mul_iff_left hcardZero hcardTop).mp
  calc
    Kakeya.realRpowENN delta (outputLoss + 2) * family.enncard ≤
        state.shading.mass := hmassLower
    _ ≤ family.enncard * volume state.shading.union := hmassUpper
    _ = volume state.shading.union * family.enncard := by ring

/-- Backwards-compatible specialization for an already assembled one-scale
local-grain state. -/
theorem PureWZ2OneScaleLocalGrainData.union_volume_lower
    {delta sigma outputLoss queryScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {planeMap : Point3 → Point3}
    (oneScale : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := outputLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point))
    (hline : WZ1PaperIsLineClass family)
    (hdeltaSmall : delta ≤ 1 / 12) :
    Kakeya.realRpowENN delta (outputLoss + 2) ≤
      volume oneScale.shading.union :=
  Proposition63ExtremalShadingData.union_volume_lower
    ({ shading := oneScale.shading
       subshading := oneScale.subshading
       extremal := oneScale.extremal
       cwa := oneScale.cwa } :
      Proposition63ExtremalShadingData
        (sigma := sigma) (outputLoss := outputLoss) source)
    hline hdeltaSmall

/-- A real line-volume threshold fixed by a total-volume floor and the
coarse-scale paper-grid window. -/
def proposition63UniformLineVolume
    (volumeFloor : ENNReal) (scale : ℝ) (hscale : 0 < scale) : ℝ :=
  ((volumeFloor /
      ((wz1PaperGridIndicesInWindow scale hscale).card : ENNReal)) / 2).toReal

theorem proposition63UniformLineVolume_pos
    {volumeFloor : ENNReal} (hfloorPos : 0 < volumeFloor)
    (hfloorTop : volumeFloor ≠ ⊤)
    (scale : ℝ) (hscale : 0 < scale) :
    0 < proposition63UniformLineVolume volumeFloor scale hscale := by
  let windowCount : ENNReal :=
    ((wz1PaperGridIndicesInWindow scale hscale).card : ENNReal)
  have hwindowZero : windowCount ≠ 0 := by
    have hnonempty := proposition63_gridWindow_nonempty scale hscale
    have hcard : 0 < (wz1PaperGridIndicesInWindow scale hscale).card :=
      Finset.Nonempty.card_pos hnonempty
    simpa [windowCount] using hcard.ne'
  have hwindowTop : windowCount ≠ ⊤ := by
    simp [windowCount]
  have hquotPos : 0 < volumeFloor / windowCount :=
    ENNReal.div_pos hfloorPos.ne' hwindowTop
  have hhalfPos : 0 < (volumeFloor / windowCount) / 2 :=
    ENNReal.div_pos hquotPos.ne' (by norm_num)
  have hhalfTop : (volumeFloor / windowCount) / 2 ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.div_ne_top hfloorTop hwindowZero)
      (by norm_num)
  exact ENNReal.toReal_pos hhalfPos.ne' hhalfTop

theorem PureWZ2BalancedCoverData.uniformLineVolume_le_half_cellMass
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily scale}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (cells : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hscale : 0 < scale) (volumeFloor : ENNReal)
    (hfloorTop : volumeFloor ≠ ⊤)
    (hfloor : volumeFloor ≤ volume fineShading.union) :
    ENNReal.ofReal
        (proposition63UniformLineVolume volumeFloor scale hscale) ≤
      cells.cellMass / 2 := by
  let windowCount : ENNReal :=
    ((wz1PaperGridIndicesInWindow scale hscale).card : ENNReal)
  have hwindowZero : windowCount ≠ 0 := by
    have hnonempty := proposition63_gridWindow_nonempty scale hscale
    have hcard : 0 < (wz1PaperGridIndicesInWindow scale hscale).card :=
      Finset.Nonempty.card_pos hnonempty
    simpa [windowCount] using hcard.ne'
  have hquotTop : volumeFloor / windowCount ≠ ⊤ :=
    ENNReal.div_ne_top hfloorTop hwindowZero
  rw [proposition63UniformLineVolume, ENNReal.ofReal_toReal
    (ENNReal.div_ne_top hquotTop (by norm_num))]
  exact ENNReal.div_le_div_right
    (PureWZ2BalancedCoverData.gridWindow_cellMass_lower cells hscale
      volumeFloor hfloor) 2

/-- Family-independent form of the paper-grid cell-mass lower bound. -/
theorem Proposition63BalancedCellData.gridWindow_cellMass_lower
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    (cells : Proposition63BalancedCellData (scale := scale) fineShading)
    (volumeFloor : ENNReal)
    (hfloor : volumeFloor ≤ volume fineShading.union) :
    volumeFloor /
        ((wz1PaperGridIndicesInWindow scale cells.scale_pos).card : ENNReal) ≤
      cells.cellMass := by
  let windowCount : ENNReal :=
    ((wz1PaperGridIndicesInWindow scale cells.scale_pos).card : ENNReal)
  have hactive : (cells.activeCells.card : ENNReal) ≤ windowCount := by
    change (cells.activeCells.card : ENNReal) ≤
      ((wz1PaperGridIndicesInWindow scale cells.scale_pos).card : ENNReal)
    exact_mod_cast Finset.card_le_card cells.activeCells_subset_gridWindow
  have hscaled : volumeFloor ≤ windowCount * cells.cellMass := by
    calc
      volumeFloor ≤ volume fineShading.union := hfloor
      _ = (cells.activeCells.card : ENNReal) * cells.cellMass :=
        cells.fine_union_volume
      _ ≤ windowCount * cells.cellMass :=
        mul_le_mul_right' hactive cells.cellMass
  have hwindowZero : windowCount ≠ 0 := by
    have hnonempty := proposition63_gridWindow_nonempty scale cells.scale_pos
    have hcard : 0 < (wz1PaperGridIndicesInWindow scale
        cells.scale_pos).card := Finset.Nonempty.card_pos hnonempty
    simpa [windowCount] using hcard.ne'
  have hwindowTop : windowCount ≠ ⊤ := by simp [windowCount]
  apply (ENNReal.div_le_iff hwindowZero hwindowTop).2
  simpa [mul_comm] using hscaled

/-- A balanced spatial decomposition, including one transported from a
selected family with the same union, supports the canonical line threshold. -/
theorem Proposition63BalancedCellData.uniformLineVolume_le_half_cellMass
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    (cells : Proposition63BalancedCellData (scale := scale) fineShading)
    (volumeFloor : ENNReal) (hfloorTop : volumeFloor ≠ ⊤)
    (hfloor : volumeFloor ≤ volume fineShading.union) :
    ENNReal.ofReal
        (proposition63UniformLineVolume volumeFloor scale cells.scale_pos) ≤
      cells.cellMass / 2 := by
  let windowCount : ENNReal :=
    ((wz1PaperGridIndicesInWindow scale cells.scale_pos).card : ENNReal)
  have hwindowZero : windowCount ≠ 0 := by
    have hnonempty := proposition63_gridWindow_nonempty scale cells.scale_pos
    have hcard : 0 < (wz1PaperGridIndicesInWindow scale
        cells.scale_pos).card := Finset.Nonempty.card_pos hnonempty
    simpa [windowCount] using hcard.ne'
  have hquotTop : volumeFloor / windowCount ≠ ⊤ :=
    ENNReal.div_ne_top hfloorTop hwindowZero
  rw [proposition63UniformLineVolume, ENNReal.ofReal_toReal
    (ENNReal.div_ne_top hquotTop (by norm_num))]
  exact ENNReal.div_le_div_right
    (cells.gridWindow_cellMass_lower volumeFloor hfloor) 2

/-- The line-factor associated to the fixed line-volume threshold. -/
def proposition63UniformLineFactor
    (volumeFloor : ENNReal) (scale : ℝ) (hscale : 0 < scale) : ENNReal :=
  ENNReal.ofReal
    (proposition63UniformLineVolume volumeFloor scale hscale /
      (4 * (2 * scale) ^ 2))

theorem proposition63UniformLineFactor_pos
    {volumeFloor : ENNReal} (hfloorPos : 0 < volumeFloor)
    (hfloorTop : volumeFloor ≠ ⊤)
    (scale : ℝ) (hscale : 0 < scale) :
    0 < proposition63UniformLineFactor volumeFloor scale hscale := by
  apply ENNReal.ofReal_pos.mpr
  exact div_pos
    (proposition63UniformLineVolume_pos hfloorPos hfloorTop scale hscale)
    (by positivity)

/-- Construct the simultaneous full-grain candidate using a line-volume
threshold fixed solely by a supplied total-volume floor and the coarse-scale
paper-grid window. -/
theorem proposition63_oneScale_fullGrainCandidate_of_volumeFloor
    {delta sigma firstLoss secondLoss queryScale sqrtScale K : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point))
    (prepared : Proposition63OneScaleConstantMultiplicityData
      (secondLoss := secondLoss) planeMap original)
    (cells : Proposition63BalancedCellData (scale := sqrtScale)
      prepared.refined.shading)
    (hqueryPos : 0 < queryScale)
    (hqueryOne : queryScale ≤ 1)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (hplaneUnit : ∀ point ∈ original.shading.union,
      ‖planeMap point‖ = 1)
    (hK : 1 ≤ K)
    (hplaneLipschitz : ∀ first ∈ original.shading.union,
      ∀ second ∈ original.shading.union,
        dist (planeMap first) (planeMap second) ≤
          K * dist first second)
    (coverBudget : ℕ) (hcoverBudgetPos : 0 < coverBudget)
    (hcoverBudget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * K) + 2 : ENNReal) *
            (9 * Kakeya.realRpowENN delta (-secondLoss) *
              Kakeya.realRpowENN (1 / queryScale) (1 - sigma))) ≤
        (coverBudget : ENNReal))
    (volumeFloor : ENNReal) (hvolumeFloorPos : 0 < volumeFloor)
    (hvolumeFloorTop : volumeFloor ≠ ⊤)
    (hvolumeFloor : volumeFloor ≤ volume prepared.refined.shading.union) :
    Nonempty
      (Proposition63OneScaleFullGrainCandidateData planeMap original
        prepared cells
          (proposition63UniformLineVolume volumeFloor sqrtScale
            (hsqrtScale.symm ▸ Real.sqrt_pos.mpr hqueryPos))
          coverBudget) := by
  have hsqrtPos : 0 < sqrtScale := by
    rw [hsqrtScale]
    exact Real.sqrt_pos.mpr hqueryPos
  let lineVolume :=
    proposition63UniformLineVolume volumeFloor sqrtScale hsqrtPos
  have hlinePos : 0 < lineVolume :=
    proposition63UniformLineVolume_pos hvolumeFloorPos hvolumeFloorTop
      sqrtScale hsqrtPos
  have hlineFloor : ENNReal.ofReal lineVolume ≤ cells.cellMass / 2 :=
    Proposition63BalancedCellData.uniformLineVolume_le_half_cellMass cells
      volumeFloor hvolumeFloorTop hvolumeFloor
  simpa only [lineVolume, proof_irrel_heq] using
    proposition63_oneScale_fullGrainCandidate planeMap original prepared
      cells hqueryOne hsqrtScale hplaneUnit hK hplaneLipschitz
      coverBudget hcoverBudgetPos hcoverBudget hlinePos hlineFloor

/-- Canonical form of the full-grain producer: the required total-volume
floor is derived internally from the same one-scale cropped extremality. -/
theorem proposition63_oneScale_fullGrainCandidate_of_extremal
    {delta sigma firstLoss secondLoss queryScale sqrtScale K : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point))
    (prepared : Proposition63OneScaleConstantMultiplicityData
      (secondLoss := secondLoss) planeMap original)
    (cells : Proposition63BalancedCellData (scale := sqrtScale)
      prepared.refined.shading)
    (hline : WZ1PaperIsLineClass family)
    (hqueryPos : 0 < queryScale)
    (hqueryOne : queryScale ≤ 1)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (hplaneUnit : ∀ point ∈ original.shading.union,
      ‖planeMap point‖ = 1)
    (hK : 1 ≤ K)
    (hplaneLipschitz : ∀ first ∈ original.shading.union,
      ∀ second ∈ original.shading.union,
        dist (planeMap first) (planeMap second) ≤
          K * dist first second)
    (coverBudget : ℕ) (hcoverBudgetPos : 0 < coverBudget)
    (hcoverBudget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * K) + 2 : ENNReal) *
            (9 * Kakeya.realRpowENN delta (-secondLoss) *
              Kakeya.realRpowENN (1 / queryScale) (1 - sigma))) ≤
        (coverBudget : ENNReal))
    (hdeltaSmall : delta ≤ 1 / 12) :
    let volumeFloor := Kakeya.realRpowENN delta (secondLoss + 2)
    let lineVolume := proposition63UniformLineVolume volumeFloor sqrtScale
      (hsqrtScale.symm ▸ Real.sqrt_pos.mpr hqueryPos)
    Nonempty
      (Proposition63OneScaleFullGrainCandidateData planeMap original
        prepared cells lineVolume coverBudget) := by
  dsimp only
  have hsqrtPos : 0 < sqrtScale := by
    rw [hsqrtScale]
    exact Real.sqrt_pos.mpr hqueryPos
  have hfloor : Kakeya.realRpowENN delta (secondLoss + 2) ≤
      volume prepared.refined.shading.union :=
    PureWZ2OneScaleLocalGrainData.union_volume_lower prepared.refined
      hline hdeltaSmall
  exact proposition63_oneScale_fullGrainCandidate_of_volumeFloor
    planeMap original prepared cells hqueryPos hqueryOne hsqrtScale
    hplaneUnit hK hplaneLipschitz coverBudget hcoverBudgetPos hcoverBudget
    (Kakeya.realRpowENN delta (secondLoss + 2))
    (by simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos
      prepared.refined.extremal.delta_pos])
    (by simp [Kakeya.realRpowENN]) hfloor

/-- Complete current-relative line-hit step with every mass factor fixed before
the step.  The canonical line volume comes from one-scale extremality and the
finite coarse-grid window; the one shared natural budget is used both to
construct the Fubini certificates and to state the iterator loss. -/
theorem Proposition63CurrentShadingReentryData.lineHitCandidate_joint_one_scale_of_extremal_budget
    {delta sigma initialInputLoss normalizationLoss reentryLoss
      firstLoss secondLoss queryScale sqrtScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (planeMap : Point3 → Point3)
    (original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := queryScale) (Y := reentry.normalization.croppedRefined)
      (fun point => planeMap point))
    (prepared : Proposition63OneScaleConstantMultiplicityData
      (secondLoss := secondLoss) planeMap original)
    (cells : Proposition63BalancedCellData (scale := sqrtScale)
      prepared.refined.shading)
    (hqueryPos : 0 < queryScale) (hquerySmall : queryScale ≤ 1 / 4)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (hsqrtPos : 0 < sqrtScale)
    (hplaneUnit : ∀ point ∈ original.shading.union,
      ‖planeMap point‖ = 1)
    (coefficient : NNReal) (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hlipschitz : LipschitzWith coefficient planeMap)
    (uniformCoverBudget : ℕ) (hcoverBudgetPos : 0 < uniformCoverBudget)
    (hcoverBudget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            (9 * Kakeya.realRpowENN delta (-secondLoss) *
              Kakeya.realRpowENN (1 / queryScale) (1 - sigma))) ≤
        (uniformCoverBudget : ENNReal))
    (spatialScale variationScale : ℝ)
    (hvariationBudget :
      (coefficient : ℝ) * spatialScale ≤ variationScale)
    (constant : ENNReal)
    (hconstant : Kakeya.realRpowENN delta (-secondLoss) ≤ constant)
    (leftFactor rightFactor : ENNReal)
    (uniformPreparationLoss : ENNReal)
    (hpreparationLoss : prepared.preparationLoss ≤ uniformPreparationLoss)
    (hincoming : leftFactor * current.mass ≤
      rightFactor * original.shading.mass)
    (hdeltaSmall : delta ≤ 1 / 12) :
    let volumeFloor := Kakeya.realRpowENN delta (secondLoss + 2)
    let lineVolume := proposition63UniformLineVolume volumeFloor sqrtScale
      hsqrtPos
    let uniformLineFactor :=
      proposition63UniformLineFactor volumeFloor sqrtScale hsqrtPos
    let inverseCoverFactor :=
      ((1 : ENNReal) / 2) / (2 * (uniformCoverBudget : ENNReal))
    ∃ next : WZ1PaperTubeShading initialNormalized.croppedFamily,
      PaperIsSubshading next current ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union,
        next.pointMultiplicity point = current.pointMultiplicity point) ∧
      (∀ first ∈ next.union, ∀ second ∈ next.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale) ∧
      (∀ point ∈ next.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (next.union ∩ Metric.closedBall point
              (Real.sqrt queryScale)))
          queryScale (1 - sigma) constant) ∧
      (uniformLineFactor * inverseCoverFactor * leftFactor) * current.mass ≤
        (rightFactor * (uniformPreparationLoss * 2)) * next.mass := by
  dsimp only
  have hqueryOne : queryScale ≤ 1 := by linarith
  let volumeFloor := Kakeya.realRpowENN delta (secondLoss + 2)
  let lineVolume :=
    proposition63UniformLineVolume volumeFloor sqrtScale hsqrtPos
  let full := Classical.choice <|
    proposition63_oneScale_fullGrainCandidate_of_extremal planeMap original
      prepared cells reentry.normalization.line_class hqueryPos hqueryOne
      hsqrtScale hplaneUnit
      hcoefficientOne
      (fun first _ second _ => hlipschitz.dist_le_mul first second)
      uniformCoverBudget hcoverBudgetPos hcoverBudget hdeltaSmall
  have hlineFactor :
      proposition63UniformLineFactor volumeFloor sqrtScale hsqrtPos ≤
        ENNReal.ofReal (lineVolume / (4 * (2 * sqrtScale) ^ 2)) := by
    exact le_rfl
  exact reentry.lineHitCandidate_joint_one_scale_of_uniform_budget
    planeMap original prepared cells full original.extremal.delta_pos
    hqueryPos hquerySmall hsqrtPos coefficient hlipschitz spatialScale
    variationScale hvariationBudget constant hconstant leftFactor rightFactor
    (proposition63UniformLineFactor volumeFloor sqrtScale hsqrtPos)
    uniformPreparationLoss uniformCoverBudget hincoming hlineFactor
    hpreparationLoss le_rfl

end Kakeya.Assouad.PureWZ2

end
