import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellwiseDirectionDichotomy
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DyadicBandSelection

/-!
# Dyadic multiplicity and cellwise direction dichotomy

This is the non-vacuous starting point for the pure Lemma 12--16 plane-map
construction.  First select one dyadic multiplicity band.  Then split whole
fine cells into dense-close and sparse-close cells.

The dense branch already carries a genuine cellwise weak plane map and keeps
an explicit fraction of the source mass.  The sparse branch keeps a uniform
multiplicity lower bound and the exact transverse close-count hypothesis used
by the Q=1 narrow construction.  No empty shading, singleton family, or
constant plane map is introduced.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Quantitative output of the dyadic-band/direction dichotomy. -/
inductive DyadicDirectionDichotomyData
    {delta kappa : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family) : Type
  | dense
      (level : ℕ)
      (band denseCells selected : WZ1PaperTubeShading family)
      (center : Point3 → Fin family.card)
      (planeMap : PaperWZ1WeakPlaneMapData selected kappa)
      (band_subshading : PaperIsSubshading band source)
      (selected_subshading : PaperIsSubshading selected band)
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
      (multiplicity_half_lower : ∀ point ∈ selected.union,
        2 ^ level < 2 * selected.pointMultiplicity point)
      (multiplicity_upper : ∀ point ∈ selected.union,
        selected.pointMultiplicity point < 2 * 2 ^ level)
      (mass_retention :
        source.mass ≤
          ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) *
            8 * selected.mass) :
      DyadicDirectionDichotomyData source
  | sparse
      (level : ℕ)
      (band sparseCells : WZ1PaperTubeShading family)
      (band_subshading : PaperIsSubshading band source)
      (sparse_subshading : PaperIsSubshading sparseCells band)
      (sparse_cubical : WZ1PaperIsCubicalShading sparseCells)
      (multiplicity_lower : ∀ point ∈ sparseCells.union,
        2 ^ level ≤ sparseCells.pointMultiplicity point)
      (multiplicity_upper : ∀ point ∈ sparseCells.union,
        sparseCells.pointMultiplicity point < 2 * 2 ^ level)
      (close_count : ∀ point ∈ sparseCells.union, ∀ index,
        point ∈ sparseCells.carrier index →
        2 * paperCloseDirectionCount sparseCells point index kappa ≤
          2 ^ level)
      (mass_retention :
        source.mass ≤
          ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) *
            2 * sparseCells.mass) :
      DyadicDirectionDichotomyData source

/-- Every nonempty cubical paper shading admits the quantitative dense/sparse
direction dichotomy after one dyadic multiplicity selection. -/
theorem paper_dyadic_direction_dichotomy
    {delta kappa : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (hfamily : family.Nonempty)
    (hsourceCubical : WZ1PaperIsCubicalShading source) :
    Nonempty (DyadicDirectionDichotomyData
      (kappa := kappa) source) := by
  rcases exists_dyadic_band_with_mass_retention
      hsourceCubical hfamily with
    ⟨level, hbandCubical, hbandMultiplicity, hbandMass⟩
  let band := wz1PaperDyadicBandSubshading source level
  let m : ℕ := 2 ^ level
  have hbandSub : PaperIsSubshading band source := by
    intro index point hpoint
    exact hpoint.1
  have hbandUpper : ∀ point ∈ band.union,
      band.pointMultiplicity point < 2 * m := by
    intro point hpoint
    have hupper := (hbandMultiplicity point hpoint).2
    simpa [m, pow_succ, mul_comm] using hupper
  rcases dense_or_sparse_close_refinement
      hbandCubical hfamily m hbandUpper with hdense | hsparse
  · rcases hdense with
      ⟨hdenseMass, center, selected, planeMap,
        hcenterMeasurable, hselectedSubDense, hselectedCubical,
        hcluster, hcenterCell, _hmultiplicityDense, hplaneCell,
        hselectedMass⟩
    let dense := denseCloseCellSet band kappa m
    let hDense := denseCloseCellSet_measurable band kappa m
    let denseCells := paperRestrictShadingToSet band dense hDense
    have hselectedSubBand : PaperIsSubshading selected band := by
      intro index
      exact (hselectedSubDense index).trans fun _ hpoint => hpoint.1
    have hselectedHalfLower : ∀ point ∈ selected.union,
        m < 2 * selected.pointMultiplicity point := by
      intro point hpoint
      have hpointDense : point ∈ denseCells.union := by
        rcases hpoint with ⟨index, hindex⟩
        exact ⟨index, hselectedSubDense index hindex⟩
      exact _hmultiplicityDense point hpointDense
    have hselectedUpper : ∀ point ∈ selected.union,
        selected.pointMultiplicity point < 2 * m := by
      intro point hpoint
      have hpointBand : point ∈ band.union := by
        rcases hpoint with ⟨index, hindex⟩
        exact ⟨index, hselectedSubBand index hindex⟩
      have hpointSelectedSet :
          {index | point ∈ selected.carrier index} ⊆
            {index | point ∈ band.carrier index} := by
        intro index hindex
        exact hselectedSubBand index hindex
      have hcard : selected.pointMultiplicity point ≤
          band.pointMultiplicity point := by
        exact Finset.card_le_card (by
          intro index hindex
          simp only [Kakeya.Streamlined.Shading.pointMultiplicity,
            Finset.mem_filter, Finset.mem_univ, true_and] at hindex ⊢
          exact hselectedSubBand index hindex)
      exact hcard.trans_lt (hbandUpper point hpointBand)
    have hmass : source.mass ≤
        ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) *
          8 * selected.mass := by
      calc
        source.mass ≤
            ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) *
              band.mass := by
          simpa [band] using hbandMass
        _ ≤ ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) *
            (2 * denseCells.mass) := by
          gcongr
          have htwo : band.mass ≤ 2 * denseCells.mass := by
            have hcancel :
                (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
              rw [one_div]
              exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
            have hscaled :=
              mul_le_mul_left' hdenseMass (2 : ENNReal)
            calc
              band.mass = 2 * ((1 / 2 : ENNReal) * band.mass) := by
                rw [← mul_assoc, hcancel, one_mul]
              _ ≤ 2 * denseCells.mass := hscaled
          exact htwo
        _ ≤ ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) *
            (8 * selected.mass) := by
          have hscaled :=
            mul_le_mul_left' hselectedMass (8 : ENNReal)
          have hquarterCancel :
              (4 : ENNReal) * (1 / 4 : ENNReal) = 1 := by
            rw [one_div]
            exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
          have hcoefficientScalar :
              (8 : ENNReal) * (1 / 4 : ENNReal) = 2 := by
            calc
              (8 : ENNReal) * (1 / 4 : ENNReal) =
                  (2 * 4) * (1 / 4 : ENNReal) := by norm_num
              _ = 2 * (4 * (1 / 4 : ENNReal)) := by ring
              _ = 2 := by rw [hquarterCancel, mul_one]
          have hcoefficient :
              8 * ((1 / 4 : ENNReal) * denseCells.mass) =
                2 * denseCells.mass := by
            rw [← mul_assoc, hcoefficientScalar]
          rw [hcoefficient] at hscaled
          exact mul_le_mul_left' hscaled
            (((Nat.log 2 family.card + 1 : ℕ) : ENNReal))
        _ = ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) *
            8 * selected.mass := by ring
    exact ⟨DyadicDirectionDichotomyData.dense level band denseCells
      selected center planeMap hbandSub hselectedSubBand
      hselectedCubical hcenterMeasurable hcluster hcenterCell hplaneCell
      (by simpa [m] using hselectedHalfLower)
      (by simpa [m] using hselectedUpper) hmass⟩
  · rcases hsparse with
      ⟨hsparseMass, hsparseSub, hsparseCubical, hsparseClose⟩
    let dense := denseCloseCellSet band kappa m
    let hDense := denseCloseCellSet_measurable band kappa m
    let sparseCells := paperRestrictShadingToSet band denseᶜ hDense.compl
    have hsparseLower : ∀ point ∈ sparseCells.union,
        m ≤ sparseCells.pointMultiplicity point := by
      intro point hpoint
      have hpointBand : point ∈ band.union := by
        rcases hpoint with ⟨index, hindex⟩
        exact ⟨index, hsparseSub index hindex⟩
      have hpointSparse : point ∈ denseᶜ := by
        rcases hpoint with ⟨index, hindex⟩
        exact hindex.2
      rw [paperPmRestrictShadingToSet hDense.compl hpointSparse]
      exact (hbandMultiplicity point hpointBand).1
    have hsparseUpper : ∀ point ∈ sparseCells.union,
        sparseCells.pointMultiplicity point < 2 * m := by
      intro point hpoint
      have hpointBand : point ∈ band.union := by
        rcases hpoint with ⟨index, hindex⟩
        exact ⟨index, hsparseSub index hindex⟩
      have hcard : sparseCells.pointMultiplicity point ≤
          band.pointMultiplicity point := by
        apply Finset.card_le_card
        intro index hindex
        simp only [Kakeya.Streamlined.Shading.pointMultiplicity,
          Finset.mem_filter, Finset.mem_univ, true_and] at hindex ⊢
        exact hsparseSub index hindex
      exact hcard.trans_lt (hbandUpper point hpointBand)
    have hmass : source.mass ≤
        ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) *
          2 * sparseCells.mass := by
      calc
        source.mass ≤
            ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) *
              band.mass := by
          simpa [band] using hbandMass
        _ ≤ ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) *
            (2 * sparseCells.mass) := by
          gcongr
          have hcancel :
              (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
            rw [one_div]
            exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
          have hscaled :=
            mul_le_mul_left' hsparseMass (2 : ENNReal)
          calc
            band.mass = 2 * ((1 / 2 : ENNReal) * band.mass) := by
              rw [← mul_assoc, hcancel, one_mul]
            _ ≤ 2 * sparseCells.mass := hscaled
        _ = ((Nat.log 2 family.card + 1 : ℕ) : ENNReal) *
            2 * sparseCells.mass := by ring
    exact ⟨DyadicDirectionDichotomyData.sparse level band sparseCells
      hbandSub hsparseSub hsparseCubical
      (by simpa [m] using hsparseLower)
      (by simpa [m] using hsparseUpper)
      (by simpa [m] using hsparseClose) hmass⟩

end Kakeya.Assouad.PureWZ2

end
