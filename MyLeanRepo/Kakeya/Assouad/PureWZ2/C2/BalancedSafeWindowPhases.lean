import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.BalancedSafeWindow

/-!
# Two shifted phases cover all balanced source cells

The two `sqrt rho` grids with shifts `0` and `sqrt rho / 2` have no common
boundary layer.  Under `4 * rho ≤ sqrt rho`, every side-`rho` cell center is
at least `rho` from the endpoints of one of the two grids.  Hence one phase
retains at least half of any finite family of balanced cells.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

attribute [local instance] Classical.propDecidable

def pureWZ2BalancedWindowPhaseShift (rho : ℝ) (phase : Bool) : ℝ :=
  if phase then Real.sqrt rho / 2 else 0

def pureWZ2BalancedWindowPhaseBlock
    (rho : ℝ) (phase : Bool) (cell : ℤ × ℤ × ℤ) : ℤ :=
  Int.floor ((pureWZ2PaperCellCenterHeight rho cell -
    pureWZ2BalancedWindowPhaseShift rho phase) / Real.sqrt rho)

def pureWZ2BalancedWindowPhaseLeft
    (rho : ℝ) (phase : Bool) (cell : ℤ × ℤ × ℤ) : ℝ :=
  (pureWZ2BalancedWindowPhaseBlock rho phase cell : ℝ) * Real.sqrt rho +
    pureWZ2BalancedWindowPhaseShift rho phase

def pureWZ2BalancedCellSafeAtPhase
    (rho : ℝ) (phase : Bool) (cell : ℤ × ℤ × ℤ) : Prop :=
  pureWZ2PaperCellCenterHeight rho cell ∈
    Set.Icc
      (pureWZ2BalancedWindowPhaseLeft rho phase cell + rho)
      (pureWZ2BalancedWindowPhaseLeft rho phase cell +
        Real.sqrt rho - rho)

def pureWZ2BalancedSafePhaseCells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (phase : Bool) : Finset (ℤ × ℤ × ℤ) :=
  pullback.selectedCells.filter
    (pureWZ2BalancedCellSafeAtPhase rho phase)

private theorem pureWZ2BalancedWindowPhaseBlock_spec
    {rho : ℝ} (hrho : 0 < rho)
    (phase : Bool) (cell : ℤ × ℤ × ℤ) :
    pureWZ2BalancedWindowPhaseLeft rho phase cell ≤
        pureWZ2PaperCellCenterHeight rho cell ∧
      pureWZ2PaperCellCenterHeight rho cell <
        pureWZ2BalancedWindowPhaseLeft rho phase cell + Real.sqrt rho := by
  let root := Real.sqrt rho
  let shift := pureWZ2BalancedWindowPhaseShift rho phase
  let center := pureWZ2PaperCellCenterHeight rho cell
  let block := Int.floor ((center - shift) / root)
  have hroot : 0 < root := Real.sqrt_pos.mpr hrho
  have hlower : (block : ℝ) ≤ (center - shift) / root :=
    Int.floor_le _
  have hupper : (center - shift) / root < (block : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have hlower' : (block : ℝ) * root ≤ center - shift :=
    (le_div_iff₀ hroot).mp hlower
  have hupper' : center - shift < ((block : ℝ) + 1) * root :=
    (div_lt_iff₀ hroot).mp hupper
  change (block : ℝ) * root + shift ≤ center ∧
    center < (block : ℝ) * root + shift + root
  constructor <;> linarith

theorem pureWZ2BalancedCell_safe_at_one_phase
    {rho : ℝ} (hrho : 0 < rho)
    (hmargin : 4 * rho ≤ Real.sqrt rho)
    (cell : ℤ × ℤ × ℤ) :
    pureWZ2BalancedCellSafeAtPhase rho false cell ∨
      pureWZ2BalancedCellSafeAtPhase rho true cell := by
  let root := Real.sqrt rho
  let center := pureWZ2PaperCellCenterHeight rho cell
  let block := pureWZ2BalancedWindowPhaseBlock rho false cell
  let left := (block : ℝ) * root
  have hroot : 0 < root := Real.sqrt_pos.mpr hrho
  have hbase := pureWZ2BalancedWindowPhaseBlock_spec hrho false cell
  have hbase' : left ≤ center ∧ center < left + root := by
    simpa [left, center, root, pureWZ2BalancedWindowPhaseLeft,
      pureWZ2BalancedWindowPhaseShift, block] using hbase
  by_cases hsafe : center ∈ Set.Icc (left + rho) (left + root - rho)
  · exact Or.inl (by
      simpa [pureWZ2BalancedCellSafeAtPhase,
        pureWZ2BalancedWindowPhaseLeft, pureWZ2BalancedWindowPhaseShift,
        center, root, block, left] using hsafe)
  · right
    rw [Set.mem_Icc, not_and_or] at hsafe
    rcases hsafe with hlow | hhigh
    · have hlow' : center < left + rho := lt_of_not_ge hlow
      have hfloor : pureWZ2BalancedWindowPhaseBlock rho true cell = block - 1 := by
        apply Int.floor_eq_iff.mpr
        have hlowerReal : ((block - 1 : ℤ) : ℝ) ≤
            (center - root / 2) / root := by
          apply (le_div_iff₀ hroot).2
          push_cast
          nlinarith
        have hupperReal : (center - root / 2) / root <
            ((block - 1 : ℤ) : ℝ) + 1 := by
          apply (div_lt_iff₀ hroot).2
          push_cast
          nlinarith [hmargin]
        exact ⟨hlowerReal, hupperReal⟩
      have hleftTrue :
          pureWZ2BalancedWindowPhaseLeft rho true cell = left - root / 2 := by
        simp [pureWZ2BalancedWindowPhaseLeft,
          pureWZ2BalancedWindowPhaseShift, hfloor, left, root]
        ring
      rw [pureWZ2BalancedCellSafeAtPhase, hleftTrue]
      constructor <;> nlinarith [hbase'.1, hmargin]
    · have hhigh' : left + root - rho < center := lt_of_not_ge hhigh
      have hfloor : pureWZ2BalancedWindowPhaseBlock rho true cell = block := by
        apply Int.floor_eq_iff.mpr
        have hlowerReal : (block : ℝ) ≤
            (center - root / 2) / root := by
          apply (le_div_iff₀ hroot).2
          nlinarith [hmargin]
        have hupperReal : (center - root / 2) / root <
            (block : ℝ) + 1 := by
          apply (div_lt_iff₀ hroot).2
          nlinarith [hbase'.2]
        exact ⟨hlowerReal, hupperReal⟩
      have hleftTrue :
          pureWZ2BalancedWindowPhaseLeft rho true cell = left + root / 2 := by
        simp [pureWZ2BalancedWindowPhaseLeft,
          pureWZ2BalancedWindowPhaseShift, hfloor, left, root]
      rw [pureWZ2BalancedCellSafeAtPhase, hleftTrue]
      constructor <;> nlinarith [hbase'.2, hmargin]

theorem pureWZ2BalancedSafePhaseCells_cover
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (hmargin : 4 * rho ≤ Real.sqrt rho) :
    pullback.selectedCells ⊆
      pureWZ2BalancedSafePhaseCells (pullback := pullback) false ∪
        pureWZ2BalancedSafePhaseCells (pullback := pullback) true := by
  intro cell hcell
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  rcases pureWZ2BalancedCell_safe_at_one_phase hrho hmargin cell with
    hfalse | htrue
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hcell, hfalse⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hcell, htrue⟩)

theorem pureWZ2_exists_balanced_safe_phase
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (hmargin : 4 * rho ≤ Real.sqrt rho) :
    ∃ phase : Bool,
      pullback.selectedCells.card ≤
        2 * (pureWZ2BalancedSafePhaseCells
          (pullback := pullback) phase).card := by
  let safeFalse := pureWZ2BalancedSafePhaseCells
    (pullback := pullback) false
  let safeTrue := pureWZ2BalancedSafePhaseCells
    (pullback := pullback) true
  have hcover : pullback.selectedCells.card ≤
      safeFalse.card + safeTrue.card := by
    calc
      pullback.selectedCells.card ≤ (safeFalse ∪ safeTrue).card :=
        Finset.card_le_card (pureWZ2BalancedSafePhaseCells_cover hmargin)
      _ ≤ safeFalse.card + safeTrue.card := Finset.card_union_le _ _
  by_cases hcompare : safeFalse.card ≤ safeTrue.card
  · refine ⟨true, ?_⟩
    simpa [safeTrue] using hcover.trans (by omega :
      safeFalse.card + safeTrue.card ≤ 2 * safeTrue.card)
  · refine ⟨false, ?_⟩
    have hreverse : safeTrue.card ≤ safeFalse.card := by omega
    simpa [safeFalse] using hcover.trans (by omega :
      safeFalse.card + safeTrue.card ≤ 2 * safeFalse.card)

end Kakeya.Assouad
