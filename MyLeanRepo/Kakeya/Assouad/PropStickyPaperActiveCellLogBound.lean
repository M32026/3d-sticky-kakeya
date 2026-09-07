import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLinePackingCardinality
import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruningStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBoundaryLogCoefficient
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperInfrastructure

/-!
# Physical logarithmic bound for active literal paper cells

Every active `delta`-cell lies in the finite integer box fixed by the cropped
paper window.  Its cardinality is polynomial in `1 / delta`, so the dyadic
cell-count loss is bounded by the same physical logarithmic envelope used for
paper line families.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem wz2_paper_active_cell_log_bound
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) :
    (Nat.log 2
        (wz1PaperActiveCells shading hdelta).card + 1 : ℝ) ≤
      (5 / Real.log 2) * Real.log (1 / delta) +
        (5 * Real.log 163 / Real.log 2 + 2) := by
  let bound : ℤ := ⌈1 / delta⌉ + 1
  let interval : Finset ℤ := Finset.Icc (-bound) bound
  let window : Finset (ℤ × ℤ × ℤ) :=
    interval.product (interval.product interval)
  have hBoundNonneg : 0 ≤ bound := by
    have hceil : 0 ≤ ⌈1 / delta⌉ := by
      have hle : (0 : ℝ) ≤ (⌈1 / delta⌉ : ℤ) := by
        exact (show (0 : ℝ) ≤ 1 / delta by positivity).trans
          (Int.le_ceil (1 / delta))
      exact_mod_cast hle
    dsimp only [bound]
    omega
  let boundNat : ℕ := bound.natAbs
  have hBoundCast : (boundNat : ℤ) = bound := by
    dsimp only [boundNat]
    rw [Int.natCast_natAbs]
    exact abs_of_nonneg hBoundNonneg
  have hIntervalCard :
      interval.card = 2 * boundNat + 1 := by
    dsimp only [interval]
    rw [Int.card_Icc]
    rw [show (-bound : ℤ) = -(boundNat : ℤ) by rw [hBoundCast]]
    rw [show bound = (boundNat : ℤ) from hBoundCast.symm]
    have hnonneg :
        (0 : ℤ) ≤
          (boundNat : ℤ) + 1 - (-(boundNat : ℤ)) := by omega
    have hvalue :
        (boundNat : ℤ) + 1 - (-(boundNat : ℤ)) =
          ((2 * boundNat + 1 : ℕ) : ℤ) := by
      omega
    rw [hvalue]
    exact Int.toNat_natCast _
  have hWindowCard :
      window.card = (2 * boundNat + 1) ^ 3 := by
    simp [window, Finset.card_product, hIntervalCard, pow_succ]
    ring
  have hActiveWindow :
      wz1PaperActiveCells shading hdelta ⊆ window := by
    intro cell hcell
    exact (Finset.mem_filter.mp hcell).1
  have hActiveCard :
      (wz1PaperActiveCells shading hdelta).card ≤
        (2 * boundNat + 1) ^ 3 := by
    rw [← hWindowCard]
    exact Finset.card_le_card hActiveWindow
  let large : ℕ := Nat.ceil (80 / delta)
  have hLargePos : 0 < large := by
    apply Nat.ceil_pos.mpr
    positivity
  have hBoundNat :
      boundNat ≤ large := by
    have hBoundReal :
        (bound : ℝ) ≤ 80 / delta := by
      have hceilLt :
          (⌈1 / delta⌉ : ℝ) < 1 / delta + 1 :=
        Int.ceil_lt_add_one (1 / delta)
      have hdeltaInv : 1 ≤ 1 / delta := by
        exact (one_le_div hdelta).mpr hdeltaOne
      have hEighty :
          1 / delta + 2 ≤ 80 / delta := by
        have hmul :
            1 / delta + 2 ≤ 80 * (1 / delta) := by
          nlinarith
        convert hmul using 1 <;> field_simp [hdelta.ne'] <;> ring
      change (((⌈1 / delta⌉ + 1 : ℤ) : ℤ) : ℝ) ≤ 80 / delta
      norm_num only [Int.cast_add, Int.cast_one]
      linarith
    have hLargeReal :
        80 / delta ≤ (large : ℝ) :=
      Nat.le_ceil _
    have hcast : (boundNat : ℝ) = (bound : ℝ) := by
      exact_mod_cast hBoundCast
    have hReal :
        (boundNat : ℝ) ≤ (large : ℝ) := by
      rw [hcast]
      exact hBoundReal.trans hLargeReal
    exact_mod_cast hReal
  have hBase :
      2 * boundNat + 1 ≤ 2 * large + 1 := by
    omega
  have hCube :
      (2 * boundNat + 1) ^ 3 ≤
        (2 * large + 1) ^ 3 :=
    Nat.pow_le_pow_left hBase 3
  have hBaseOne : 1 ≤ 2 * large + 1 := by omega
  have hExponent :
      (2 * large + 1) ^ 3 ≤
        (2 * large + 1) ^ 5 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hCard :
      (wz1PaperActiveCells shading hdelta).card ≤
        (2 * Nat.ceil (80 / delta) + 1) ^ 5 := by
    exact hActiveCard.trans (hCube.trans hExponent)
  have hExplicit :=
    explicit_card_log_bound hdelta hdeltaOne hCard
  have hLogMono :
      (Nat.log 2
          (wz1PaperActiveCells shading hdelta).card + 1 : ℝ) ≤
        (Nat.log 2
          (2 * (wz1PaperActiveCells shading hdelta).card) + 1 : ℝ) := by
    have hCardDouble :
        (wz1PaperActiveCells shading hdelta).card ≤
          2 * (wz1PaperActiveCells shading hdelta).card := by
      omega
    have hNat :
        Nat.log 2 (wz1PaperActiveCells shading hdelta).card + 1 ≤
          Nat.log 2
              (2 * (wz1PaperActiveCells shading hdelta).card) + 1 :=
      Nat.add_le_add_right (Nat.log_mono_right hCardDouble) 1
    exact_mod_cast hNat
  exact hLogMono.trans hExplicit

theorem wz2_paper_active_cell_log_bound_ennreal
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) :
    ((Nat.log 2
        (wz1PaperActiveCells shading hdelta).card + 1 : ℕ) :
      ENNReal) ≤
      ENNReal.ofReal
        (wz2PaperBoundaryLogCoefficient *
          (1 + Real.log delta⁻¹)) := by
  have hRaw :=
    wz2_paper_active_cell_log_bound hdelta hdeltaOne shading
  have hLogNonneg : 0 ≤ Real.log delta⁻¹ := by
    apply Real.log_nonneg
    exact (one_le_inv₀ hdelta).mpr hdeltaOne
  have hA :
      5 / Real.log 2 ≤ wz2PaperBoundaryLogCoefficient := by
    dsimp only [wz2PaperBoundaryLogCoefficient]
    exact le_max_right _ _
  have hB :
      5 * Real.log 163 / Real.log 2 + 2 ≤
        wz2PaperBoundaryLogCoefficient := by
    dsimp only [wz2PaperBoundaryLogCoefficient]
    exact le_max_left _ _
  have hLogEq :
      Real.log (1 / delta) = Real.log delta⁻¹ := by
    congr 1
    field_simp [hdelta.ne']
  have hReal :
      (Nat.log 2
          (wz1PaperActiveCells shading hdelta).card + 1 : ℝ) ≤
        wz2PaperBoundaryLogCoefficient *
          (1 + Real.log delta⁻¹) := by
    calc
      (Nat.log 2
          (wz1PaperActiveCells shading hdelta).card + 1 : ℝ) ≤
        (5 / Real.log 2) * Real.log (1 / delta) +
          (5 * Real.log 163 / Real.log 2 + 2) := hRaw
      _ =
        (5 / Real.log 2) * Real.log delta⁻¹ +
          (5 * Real.log 163 / Real.log 2 + 2) := by
        rw [hLogEq]
      _ ≤
        wz2PaperBoundaryLogCoefficient * Real.log delta⁻¹ +
          wz2PaperBoundaryLogCoefficient := by
        gcongr
      _ =
        wz2PaperBoundaryLogCoefficient *
          (1 + Real.log delta⁻¹) := by ring
  rw [show
    ((Nat.log 2
        (wz1PaperActiveCells shading hdelta).card + 1 : ℕ) :
      ENNReal) =
      ENNReal.ofReal
        ((Nat.log 2
          (wz1PaperActiveCells shading hdelta).card + 1 : ℕ) :
          ℝ) by
    exact (ENNReal.ofReal_natCast _).symm]
  apply ENNReal.ofReal_mono
  norm_num only [Nat.cast_add, Nat.cast_one]
  exact hReal

theorem wz2_paper_available_cell_log_bound_ennreal
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {multiplicityCap : ENNReal}
    (pruning :
      WZ2PaperBoundaryCellPruningData
        (rho := rho) shading hdelta multiplicityCap) :
    ((Nat.log 2
        (∑ coarseCell ∈ pruning.coarseCells,
          (pruning.availableFineCells coarseCell).card) + 1 : ℕ) :
      ENNReal) ≤
      ENNReal.ofReal
        (wz2PaperBoundaryLogCoefficient *
          (1 + Real.log delta⁻¹)) := by
  have hAvailable :
      (∑ coarseCell ∈ pruning.coarseCells,
          (pruning.availableFineCells coarseCell).card) =
        pruning.safeFineCells.card := by
    simp_rw [pruning.availableFineCells_eq]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    apply congrArg Finset.card
    ext fineCell
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      rw [pruning.coarseCells_eq]
      exact Finset.mem_image.mpr
        ⟨fineCell, h, rfl⟩
  have hSafe :
      pruning.safeFineCells.card ≤
        (wz1PaperActiveCells shading hdelta).card :=
    Finset.card_le_card pruning.safeFineCells_subset
  have hLog :
      Nat.log 2
          (∑ coarseCell ∈ pruning.coarseCells,
            (pruning.availableFineCells coarseCell).card) + 1 ≤
        Nat.log 2
            (wz1PaperActiveCells shading hdelta).card + 1 := by
    rw [hAvailable]
    exact Nat.add_le_add_right (Nat.log_mono_right hSafe) 1
  exact_mod_cast
    (show
      ((Nat.log 2
          (wz1PaperActiveCells shading hdelta).card + 1 : ℕ) :
        ENNReal) ≤
        ENNReal.ofReal
          (wz2PaperBoundaryLogCoefficient *
            (1 + Real.log delta⁻¹)) from
      wz2_paper_active_cell_log_bound_ennreal
        hdelta hdeltaOne shading)
    |>.trans' (by exact_mod_cast hLog)

end Kakeya.Assouad

end
