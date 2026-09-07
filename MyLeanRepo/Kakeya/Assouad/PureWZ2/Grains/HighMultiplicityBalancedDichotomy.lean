import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HighMultiplicityDirectionInput
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HighMultiplicityThreshold
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DenseCloseDensityRefinement

/-!
# High-multiplicity balanced direction dichotomy

This is the non-dyadic starting point for planiness.  First retain the whole
fine cells whose multiplicity exceeds the cardinality density power.  Then
split those cells at `R = m / 24`.  The sparse branch has exactly the strict
close-count and cubic combinatorial budget needed by variable-`Q` planiness.
The dense branch is paid directly by the density power, so no upper
multiplicity band and no `log #family` loss are introduced.  The extra factor
two leaves room for a later relative dyadic band on the sparse branch.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- Quantitative output of the high-multiplicity balanced direction split. -/
inductive HighMultiplicityBalancedDichotomyData
    {delta kappa : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (densityPower : ENNReal) : Type
  | dense
      (m R : ℕ)
      (high denseCells selected : WZ1PaperTubeShading family)
      (center : Point3 → Fin family.card)
      (planeMap : PaperWZ1WeakPlaneMapData selected kappa)
      (R_def : R = m / 24)
      (R_pos : 0 < R)
      (budget : 24 * R ≤ m)
      (upper_budget : m ≤ 48 * R)
      (density_lower : densityPower * family.enncard ≤ (m : ENNReal))
      (high_subshading : PaperIsSubshading high source)
      (dense_subshading : PaperIsSubshading denseCells high)
      (selected_subshading : PaperIsSubshading selected denseCells)
      (selected_cubical : WZ1PaperIsCubicalShading selected)
      (center_measurable : Measurable center)
      (cluster : ∀ index point, point ∈ selected.carrier index →
        ‖wz1Cross (family.tube (center point)).direction
          (family.tube index).direction‖ < kappa)
      (center_cellwise : ∀ first second,
        wz1PaperGridIndex delta first =
          wz1PaperGridIndex delta second →
        center first = center second)
      (planeMap_cellwise : ∀ first second,
        wz1PaperGridIndex delta first =
          wz1PaperGridIndex delta second →
        planeMap.planeMap first = planeMap.planeMap second)
      (coordination_density : ∀ point ∈ selected.union,
        (densityPower / 48) * family.enncard ≤
          2 * (selected.pointMultiplicity point : ENNReal))
      (mass_retention :
        (densityPower / 48) * ((1 / 4 : ENNReal) * source.mass) ≤
          2 * selected.mass) :
      HighMultiplicityBalancedDichotomyData source densityPower
  | sparse
      (m R : ℕ)
      (high sparseCells : WZ1PaperTubeShading family)
      (R_def : R = m / 24)
      (R_pos : 0 < R)
      (budget : 24 * R ≤ m)
      (upper_budget : m ≤ 48 * R)
      (density_lower : densityPower * family.enncard ≤ (m : ENNReal))
      (coordination_density :
        (densityPower / 24) * family.enncard ≤ (2 * R : ℕ))
      (high_subshading : PaperIsSubshading high source)
      (sparse_subshading : PaperIsSubshading sparseCells high)
      (sparse_cubical : WZ1PaperIsCubicalShading sparseCells)
      (multiplicity_lower : ∀ point ∈ sparseCells.union,
        m ≤ sparseCells.pointMultiplicity point)
      (close_count : ∀ point ∈ sparseCells.union, ∀ index,
        point ∈ sparseCells.carrier index →
        paperCloseDirectionCount sparseCells point index kappa < R)
      (mass_retention :
        (1 / 4 : ENNReal) * source.mass ≤ sparseCells.mass) :
      HighMultiplicityBalancedDichotomyData source densityPower

/-- The high-multiplicity whole-cell restriction admits a balanced
dense/sparse direction split without a second dyadic pigeonhole. -/
theorem high_multiplicity_balanced_direction_dichotomy
    {delta sigma loss densityLoss kappa : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (extremal : WZ2PaperCroppedIsExtremal sigma loss family source)
    (hline : WZ1PaperIsLineClass family)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * loss)
    (hloss : 0 < loss)
    (hsmall : Kakeya.realRpowENN delta loss < 1 / 4)
    (hfixedAbsorb :
      (288 : ENNReal) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN delta (-sigma + 4 * loss)) :
    Nonempty (HighMultiplicityBalancedDichotomyData
      (kappa := kappa) source
      (Kakeya.realRpowENN delta densityLoss)) := by
  let densityPower := Kakeya.realRpowENN delta densityLoss
  rcases high_multiplicity_direction_input extremal hline hdeltaSmall
      hdensityLoss hloss hsmall with
    ⟨m, high, hhighSub, hhighCubical, hhighMultiplicity, hdensity,
      hhighMass, _hhighCommon, hmPos⟩
  have hmTwentyFour : 24 ≤ m :=
    twenty_four_le_multiplicity_of_density_power extremal hdeltaSmall
      hdensityLoss hfixedAbsorb hdensity
  let R := m / 24
  let threshold := 2 * R - 1
  let dense := denseCloseCellSet high kappa threshold
  let hDense := denseCloseCellSet_measurable high kappa threshold
  let denseCells := paperRestrictShadingToSet high dense hDense
  let sparseCells := paperRestrictShadingToSet high denseᶜ hDense.compl
  have hR : 0 < R := by
    dsimp only [R]
    omega
  have hbudget : 24 * R ≤ m := by
    dsimp only [R]
    omega
  have hmFortyEight : m ≤ 48 * R := by
    dsimp only [R]
    omega
  have hpay : (densityPower / 48) * family.enncard ≤
      (threshold : ENNReal) := by
    have hD : densityPower * family.enncard ≤ (m : ENNReal) := by
      simpa [densityPower] using hdensity
    have hmR : (m : ENNReal) / 48 ≤ (R : ENNReal) := by
      apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
      have hcast : (m : ENNReal) ≤ (48 * R : ℕ) := by
        exact_mod_cast hmFortyEight
      simpa [Nat.cast_mul, mul_comm] using hcast
    have hRThreshold : (R : ENNReal) ≤ (threshold : ENNReal) := by
      exact_mod_cast (show R ≤ threshold by
        dsimp only [threshold]
        omega)
    calc
      (densityPower / 48) * family.enncard =
          (densityPower * family.enncard) / 48 := by
        simp only [div_eq_mul_inv]
        ring
      _ ≤ (m : ENNReal) / 48 := by gcongr
      _ ≤ (R : ENNReal) := hmR
      _ ≤ (threshold : ENNReal) := hRThreshold
  rcases dense_or_sparse_close_mass high kappa threshold with
      hdense | hsparse
  · rcases dense_close_plane_map_refinement_density
        hhighCubical extremal.nonempty threshold (densityPower / 48) hpay with
      ⟨center, selected, planeMap, hcenterMeasurable, hselectedSub,
        hselectedCubical, hcluster, hcenterCell, _hmultiplicity,
        hplaneCell, hselectedMass⟩
    have hdenseSub : PaperIsSubshading denseCells high := by
      intro index point hpoint
      exact hpoint.1
    have hcoordinationDensity : ∀ point ∈ selected.union,
        (densityPower / 48) * family.enncard ≤
          2 * (selected.pointMultiplicity point : ENNReal) := by
      intro point hpoint
      have hpointDense : point ∈ denseCells.union := by
        rcases hpoint with ⟨index, hindex⟩
        exact ⟨index, hselectedSub index hindex⟩
      have hmult := _hmultiplicity point hpointDense
      exact hpay.trans <| by exact_mod_cast hmult.le
    have hquarter : (1 / 4 : ENNReal) * source.mass ≤
        denseCells.mass := by
      have hcoefficient : (1 / 4 : ENNReal) =
          (1 / 2 : ENNReal) * (1 / 2 : ENNReal) := by
        simp only [one_div]
        have hmul : (2 : ENNReal) * 2 = 4 := by norm_num
        have hinv : ((2 : ENNReal) * 2)⁻¹ =
            (2 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ := by
          rw [ENNReal.mul_inv] <;> norm_num
        rw [hmul] at hinv
        exact hinv
      calc
        (1 / 4 : ENNReal) * source.mass =
            (1 / 2 : ENNReal) *
              ((1 / 2 : ENNReal) * source.mass) := by
          rw [hcoefficient, mul_assoc]
        _ ≤ (1 / 2 : ENNReal) * high.mass := by gcongr
        _ ≤ denseCells.mass := hdense
    have hmass : (densityPower / 48) *
        ((1 / 4 : ENNReal) * source.mass) ≤ 2 * selected.mass := by
      exact (mul_le_mul_left' hquarter (densityPower / 48)).trans
        hselectedMass
    exact ⟨HighMultiplicityBalancedDichotomyData.dense
      m R high denseCells selected center planeMap rfl hR hbudget
      hmFortyEight
      (by simpa [densityPower] using hdensity) hhighSub hdenseSub
      hselectedSub hselectedCubical hcenterMeasurable hcluster hcenterCell
      hplaneCell hcoordinationDensity hmass⟩
  · rcases sparse_close_cellwise_refinement hhighCubical threshold with
      ⟨hsparseSub, hsparseCubical, hclose⟩
    have hsparseMultiplicity : ∀ point ∈ sparseCells.union,
        m ≤ sparseCells.pointMultiplicity point := by
      intro point hpoint
      have hpointHigh : point ∈ high.union := by
        rcases hpoint with ⟨index, hindex⟩
        exact ⟨index, hsparseSub index hindex⟩
      have hpointSparse : point ∈ denseᶜ := by
        rcases hpoint with ⟨index, hindex⟩
        exact hindex.2
      rw [paperPmRestrictShadingToSet hDense.compl hpointSparse]
      exact hhighMultiplicity point hpointHigh
    have hcloseStrict : ∀ point ∈ sparseCells.union, ∀ index,
        point ∈ sparseCells.carrier index →
        paperCloseDirectionCount sparseCells point index kappa < R := by
      intro point hpoint index hindex
      have hle : 2 * paperCloseDirectionCount sparseCells point index kappa ≤
          2 * R - 1 := by
        simpa [sparseCells, threshold, R] using
          hclose point hpoint index hindex
      omega
    have hquarter : (1 / 4 : ENNReal) * source.mass ≤ sparseCells.mass := by
      have hcoefficient : (1 / 4 : ENNReal) =
          (1 / 2 : ENNReal) * (1 / 2 : ENNReal) := by
        simp only [one_div]
        have hmul : (2 : ENNReal) * 2 = 4 := by norm_num
        have hinv : ((2 : ENNReal) * 2)⁻¹ =
            (2 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ := by
          rw [ENNReal.mul_inv] <;> norm_num
        rw [hmul] at hinv
        exact hinv
      calc
        (1 / 4 : ENNReal) * source.mass =
            (1 / 2 : ENNReal) *
              ((1 / 2 : ENNReal) * source.mass) := by
          rw [hcoefficient, mul_assoc]
        _ ≤ (1 / 2 : ENNReal) * high.mass := by gcongr
        _ ≤ sparseCells.mass := hsparse
    have hcoordinationDensity : (densityPower / 24) * family.enncard ≤
        (2 * R : ℕ) := by
      have hD : densityPower * family.enncard ≤ (m : ENNReal) := by
        simpa [densityPower] using hdensity
      have hdiv : (densityPower / 24) * family.enncard ≤
          (m : ENNReal) / 24 := by
        calc
          (densityPower / 24) * family.enncard =
              (densityPower * family.enncard) / 24 := by
            simp only [div_eq_mul_inv]
            ring
          _ ≤ (m : ENNReal) / 24 := by gcongr
      have hmR : (m : ENNReal) / 24 ≤ (2 * R : ℕ) := by
        apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
        have hnat : m ≤ (2 * R) * 24 := by omega
        exact_mod_cast hnat
      exact hdiv.trans hmR
    exact ⟨HighMultiplicityBalancedDichotomyData.sparse
      m R high sparseCells rfl hR hbudget hmFortyEight
      (by simpa [densityPower] using hdensity) hcoordinationDensity
      hhighSub hsparseSub
      hsparseCubical
      hsparseMultiplicity hcloseStrict hquarter⟩

end Kakeya.Assouad.PureWZ2

end
