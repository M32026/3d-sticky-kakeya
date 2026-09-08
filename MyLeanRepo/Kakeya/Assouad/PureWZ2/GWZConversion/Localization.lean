import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.Reanchoring
import MyLeanRepo.Kakeya.Assouad.WZ1.GridCovering
import MyLeanRepo.Kakeya.Hairbrush.Pigeonhole

/-!
# Fixed-cell localization for the reanchored GWZ conversion

Cover the fixed support ball by finitely many small measurable cells and
choose one cell carrying a controlled fraction of the indexed shaded mass.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Explicit number of cells in the fixed spatial localization grid. -/
def pureWZ2LocalizationCellCount (R radius : ℝ) : ℕ :=
  (Nat.ceil (2 * R * Real.sqrt 3 / radius) + 1) ^ 3

/-- One mass-retaining fixed-diameter spatial localization. -/
structure PureWZ2LocalizationData
    {delta R radius : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : Kakeya.Streamlined.TubeShading source) where
  cellCount : ℕ
  cellCount_eq :
    cellCount = pureWZ2LocalizationCellCount R radius
  cellCount_pos : 0 < cellCount
  center : Point3
  cell : Set Point3
  cell_measurable : MeasurableSet cell
  cell_subset_ball : cell ⊆ Metric.closedBall center radius
  localizedMass : ENNReal
  localizedMass_eq :
    localizedMass =
      ∑ index : Fin source.card,
        volume (shading.carrier index ∩ cell)
  mass_retained :
    shading.mass ≤ (cellCount : ENNReal) * localizedMass

/--
A finite cube grid of diameter at most `radius` localizes the shading mass.
The explicit cell count is `(N ^ 3)` for
`N = ceil (2 * R * sqrt 3 / radius)`.
-/
theorem pureWZ2_fixed_cell_localization
    {delta R radius : ℝ}
    (hR : 0 < R)
    (hradius : 0 < radius)
    {source : Kakeya.Streamlined.TubeFamily delta}
    (hsupport :
      ∀ index,
        (source.tube index).carrier ⊆
          Metric.closedBall (0 : Point3) R)
    (shading : Kakeya.Streamlined.TubeShading source)
    (hshadingPos : 0 < shading.mass)
    (hshadingFinite : shading.mass ≠ ⊤) :
    Nonempty (PureWZ2LocalizationData (R := R) (radius := radius) shading) := by
  let N : ℕ := Nat.ceil (2 * R * Real.sqrt 3 / radius) + 1
  have hN : 1 ≤ N := by
    dsimp only [N]
    omega
  have hdiam :
      Real.sqrt 3 * (2 * R / N) ≤ radius := by
    have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    have hceil :
        2 * R * Real.sqrt 3 / radius ≤
          (Nat.ceil (2 * R * Real.sqrt 3 / radius) : ℝ) :=
      Nat.le_ceil _
    have hNreal :
        2 * R * Real.sqrt 3 / radius < (N : ℝ) := by
      dsimp only [N]
      norm_num
      exact lt_of_le_of_lt hceil (lt_add_one _)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    calc
      Real.sqrt 3 * (2 * R / N)
          = (2 * R * Real.sqrt 3) / N := by ring
      _ ≤ radius := by
        rw [div_le_iff₀ hNpos]
        have hradiusNonneg : 0 ≤ radius := hradius.le
        have hscaled :
            2 * R * Real.sqrt 3 < radius * (N : ℝ) := by
          simpa [mul_comm] using (div_lt_iff₀ hradius).mp hNreal
        linarith
  rcases
      grid_covering_cover
        (0 : Point3) R radius hR.le N hN hradius hdiam with
    ⟨cells, hmeasurable, hcover, hcellDiameter⟩
  let indexType := Fin 3 → Fin N
  let weight : indexType → ENNReal := fun cellIndex =>
    ∑ index : Fin source.card,
      volume (shading.carrier index ∩ cells cellIndex)
  have hcarrierCover :
      ∀ index,
        shading.carrier index ⊆
          ⋃ cellIndex : indexType,
            shading.carrier index ∩ cells cellIndex := by
    intro index point hpoint
    have hpointSupport :
        dist point (0 : Point3) ≤ R := by
      simpa [Metric.mem_closedBall] using
        hsupport index (shading.subset_body index hpoint)
    rcases hcover point hpointSupport with
      ⟨cellIndex, hcell⟩
    exact Set.mem_iUnion.mpr
      ⟨cellIndex, hpoint, hcell⟩
  have hmassLe :
      shading.mass ≤ ∑ cellIndex : indexType, weight cellIndex := by
    calc
      shading.mass =
          ∑ index : Fin source.card,
            volume (shading.carrier index) := rfl
      _ ≤
          ∑ index : Fin source.card,
            ∑ cellIndex : indexType,
              volume (shading.carrier index ∩ cells cellIndex) := by
        apply Finset.sum_le_sum
        intro index _
        exact
          (measure_mono (hcarrierCover index)).trans
            (measure_iUnion_fintype_le _ _)
      _ =
          ∑ cellIndex : indexType,
            ∑ index : Fin source.card,
              volume (shading.carrier index ∩ cells cellIndex) := by
        rw [Finset.sum_comm]
      _ = ∑ cellIndex : indexType, weight cellIndex := rfl
  let allCells : Finset indexType := Finset.univ
  have hnonempty : allCells.Nonempty := Finset.univ_nonempty
  have hpigeon :
      ∃ cellIndex ∈ allCells,
        weight cellIndex ≥
          shading.mass / (allCells.card : ENNReal) := by
    apply Kakeya.Hairbrush.ennreal_sum_pigeonhole
      hshadingFinite
      (s := allCells) (f := weight)
    · simpa [allCells] using hmassLe
    · exact hnonempty
  rcases hpigeon with ⟨cellIndex, _, hweight⟩
  have hallZero : (allCells.card : ENNReal) ≠ 0 := by
    simp [allCells, indexType, N]
  have hallTop : (allCells.card : ENNReal) ≠ ⊤ := by simp
  have hweightPos : 0 < weight cellIndex := by
    have hdivPos :
        0 < shading.mass / (allCells.card : ENNReal) :=
      ENNReal.div_pos hshadingPos.ne' hallTop
    exact hdivPos.trans_le hweight
  have hcellNonempty : (cells cellIndex).Nonempty := by
    rcases Finset.sum_pos_iff.mp hweightPos with
      ⟨index, _, hindexPos⟩
    have hinter :
        (shading.carrier index ∩ cells cellIndex).Nonempty := by
      apply Set.nonempty_iff_ne_empty.mpr
      intro hempty
      rw [hempty, measure_empty] at hindexPos
      exact (lt_self_iff_false 0).mp hindexPos
    exact hinter.mono Set.inter_subset_right
  let center : Point3 := Classical.choose hcellNonempty
  have hcenterCell : center ∈ cells cellIndex :=
    Classical.choose_spec hcellNonempty
  have hcellSubset :
      cells cellIndex ⊆ Metric.closedBall center radius := by
    intro point hpoint
    have hdist := hcellDiameter cellIndex point center hpoint hcenterCell
    simpa [Metric.mem_closedBall] using hdist
  have hcard :
      (allCells.card : ENNReal) = (N ^ 3 : ℕ) := by
    simp [allCells, indexType, Fintype.card_fun]
  have hretained :
      shading.mass ≤ (N ^ 3 : ℕ) * weight cellIndex := by
    have hmul :
        shading.mass ≤
          (allCells.card : ENNReal) * weight cellIndex :=
      (by
        have h :=
          (ENNReal.div_le_iff_le_mul
            (Or.inl hallZero) (Or.inl hallTop)).mp hweight
        simpa [mul_comm] using h)
    rw [hcard] at hmul
    exact hmul
  exact
    ⟨{
      cellCount := N ^ 3
      cellCount_eq := by
        rfl
      cellCount_pos := by positivity
      center := center
      cell := cells cellIndex
      cell_measurable := hmeasurable cellIndex
      cell_subset_ball := hcellSubset
      localizedMass := weight cellIndex
      localizedMass_eq := rfl
      mass_retained := hretained
    }⟩

end Kakeya.Assouad

end
