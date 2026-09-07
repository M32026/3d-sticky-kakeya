import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellwiseDirectionDichotomy

/-!
# A direction dichotomy with the sparse combinatorial budget built in

The first cellwise direction dichotomy used the same multiplicity parameter
both as the dyadic lower bound and as twice the sparse close-count bound.
That is too weak for the variable-`Q` transverse-triple argument, which needs
`12 * R <= m` and `closeCount < R` simultaneously.

Here we split at `2 * (m / 12) - 1`.  On sparse cells this gives the required
strict close-count bound.  On dense cells the selected close cluster contains
at least `m / 12` active tubes, so the dyadic upper bound pays only the
absolute factor `48`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- A constant-factor version of the paper multiplicity-to-mass lemma. -/
private lemma paper_mass_lower_from_pointMultiplicity_const
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {selected source : WZ1PaperTubeShading family}
    (factor : ℕ)
    (hfactor : 0 < factor)
    (hmultiplicity : ∀ point ∈ source.union,
      source.pointMultiplicity point ≤
        factor * selected.pointMultiplicity point) :
    (factor : ENNReal)⁻¹ * source.mass ≤ selected.mass := by
  have hpoint : ∀ point : Point3,
      (source.pointMultiplicity point : ENNReal) ≤
        (factor : ENNReal) *
          (selected.pointMultiplicity point : ENNReal) := by
    intro point
    by_cases hp : point ∈ source.union
    · exact_mod_cast hmultiplicity point hp
    · have hzero : source.pointMultiplicity point = 0 := by
        simpa [Kakeya.Streamlined.Shading.pointMultiplicity,
          Kakeya.Streamlined.Shading.union] using hp
      simp [hzero]
  have hintegral :
      (∫⁻ point, (source.pointMultiplicity point : ENNReal)) ≤
        ∫⁻ point, (factor : ENNReal) *
          (selected.pointMultiplicity point : ENNReal) :=
    MeasureTheory.lintegral_mono hpoint
  have hmeasurable : Measurable fun point : Point3 =>
      (selected.pointMultiplicity point : ENNReal) := by
    have heq : (fun point : Point3 =>
        (selected.pointMultiplicity point : ENNReal)) =
        fun point => ∑ index : Fin family.card,
          (selected.carrier index).indicator
            (fun _ => (1 : ENNReal)) point := by
      funext point
      exact coe_pointMultiplicity_eq_sum_indicator selected point
    rw [heq]
    exact Finset.measurable_sum _ fun index _ =>
      measurable_const.indicator (selected.measurable_carrier index)
  have hconst :
      (∫⁻ point, (factor : ENNReal) *
        (selected.pointMultiplicity point : ENNReal)) =
        (factor : ENNReal) *
          (∫⁻ point,
            (selected.pointMultiplicity point : ENNReal)) := by
    rw [MeasureTheory.lintegral_const_mul]
    exact hmeasurable
  rw [lintegral_pointMultiplicity source, hconst,
    lintegral_pointMultiplicity selected] at hintegral
  have hscaled := mul_le_mul_left' hintegral (factor : ENNReal)⁻¹
  have hcancel : (factor : ENNReal)⁻¹ * (factor : ENNReal) = 1 :=
    ENNReal.inv_mul_cancel (by exact_mod_cast hfactor.ne') (by simp)
  calc
    (factor : ENNReal)⁻¹ * source.mass ≤
        (factor : ENNReal)⁻¹ *
          ((factor : ENNReal) * selected.mass) := hscaled
    _ = ((factor : ENNReal)⁻¹ * (factor : ENNReal)) *
          selected.mass := by rw [mul_assoc]
    _ = selected.mass := by rw [hcancel, one_mul]

/-- Quantitative dense/sparse output at the threshold `m / 12`. -/
inductive BalancedDirectionDichotomyData
    {delta kappa : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family) (m : ℕ) : Type
  | dense
      (R : ℕ)
      (denseCells selected : WZ1PaperTubeShading family)
      (center : Point3 → Fin family.card)
      (planeMap : PaperWZ1WeakPlaneMapData selected kappa)
      (R_def : R = m / 12)
      (R_pos : 0 < R)
      (budget : 12 * R ≤ m)
      (dense_subshading : PaperIsSubshading denseCells source)
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
      (multiplicity_lower : ∀ point ∈ selected.union,
        R ≤ selected.pointMultiplicity point)
      (mass_retention : source.mass ≤ 96 * selected.mass) :
      BalancedDirectionDichotomyData source m
  | sparse
      (R : ℕ)
      (sparseCells : WZ1PaperTubeShading family)
      (R_def : R = m / 12)
      (R_pos : 0 < R)
      (budget : 12 * R ≤ m)
      (sparse_subshading : PaperIsSubshading sparseCells source)
      (sparse_cubical : WZ1PaperIsCubicalShading sparseCells)
      (multiplicity_lower : ∀ point ∈ sparseCells.union,
        m ≤ sparseCells.pointMultiplicity point)
      (multiplicity_upper : ∀ point ∈ sparseCells.union,
        sparseCells.pointMultiplicity point < 2 * m)
      (close_count : ∀ point ∈ sparseCells.union, ∀ index,
        point ∈ sparseCells.carrier index →
        paperCloseDirectionCount sparseCells point index kappa < R)
      (mass_retention : source.mass ≤ 2 * sparseCells.mass) :
      BalancedDirectionDichotomyData source m

/-- Dense close-cluster selection at an independent threshold.  If the source
multiplicity is below `2m` and the threshold is `2R-1`, the selected cluster
retains at least `R` tubes and loses at most a factor `48` when
`R = m / 12`. -/
private theorem dense_close_div_twelve_refinement
    {delta kappa : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading source)
    (hfamily : family.Nonempty)
    (m : ℕ)
    (hm : 12 ≤ m)
    (hmultUpper : ∀ point ∈ source.union,
      source.pointMultiplicity point < 2 * m) :
    let R := m / 12
    let threshold := 2 * R - 1
    let dense := denseCloseCellSet source kappa threshold
    let hDense := denseCloseCellSet_measurable source kappa threshold
    let denseCells := paperRestrictShadingToSet source dense hDense
    ∃ (center : Point3 → Fin family.card)
      (selected : WZ1PaperTubeShading family)
      (planeMap : PaperWZ1WeakPlaneMapData selected kappa),
      Measurable center ∧
      PaperIsSubshading selected denseCells ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ index point, point ∈ selected.carrier index →
        ‖wz1Cross (family.tube (center point)).direction
          (family.tube index).direction‖ < kappa) ∧
      (∀ first second,
        wz1PaperGridIndex delta first =
          wz1PaperGridIndex delta second →
        center first = center second) ∧
      (∀ point ∈ selected.union,
        R ≤ selected.pointMultiplicity point) ∧
      (∀ first second,
        wz1PaperGridIndex delta first =
          wz1PaperGridIndex delta second →
        planeMap.planeMap first = planeMap.planeMap second) ∧
      (1 / 48 : ENNReal) * denseCells.mass ≤ selected.mass := by
  dsimp only
  let R := m / 12
  let threshold := 2 * R - 1
  let dense := denseCloseCellSet source kappa threshold
  let hDense := denseCloseCellSet_measurable source kappa threshold
  let denseCells := paperRestrictShadingToSet source dense hDense
  have hR : 0 < R := by
    dsimp only [R]
    omega
  rcases dense_close_cellwise_center
      (S := source) (kappa := kappa) hcubical hfamily threshold with
    ⟨center, hcenterMeasurable, hcenterDense, hcenterCell⟩
  let selected : WZ1PaperTubeShading family :=
    { carrier := fun index =>
        {point | point ∈ denseCells.carrier index ∧
          ‖wz1Cross (family.tube (center point)).direction
            (family.tube index).direction‖ < kappa}
      measurable_carrier := fun index =>
        (denseCells.measurable_carrier index).inter
          (measurable_cellwise_close_direction hcenterMeasurable index)
      subset_body := fun index point hpoint =>
        denseCells.subset_body index hpoint.1 }
  have hdenseCubical : WZ1PaperIsCubicalShading denseCells :=
    paperRestrictShadingToSet_cubical hDense hcubical
      (denseCloseCellSet_cube_union hcubical kappa threshold)
  have hselectedSub : PaperIsSubshading selected denseCells := by
    intro index point hpoint
    exact hpoint.1
  have hselectedCubical : WZ1PaperIsCubicalShading selected := by
    intro index point hpoint other hother
    have hcell : wz1PaperGridIndex delta other =
        wz1PaperGridIndex delta point :=
      (mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) other).mp hother
    have hcarrier : other ∈ denseCells.carrier index :=
      hdenseCubical index point hpoint.1 hother
    have hcenterEq : center other = center point :=
      hcenterCell other point hcell
    exact ⟨hcarrier, by simpa [hcenterEq] using hpoint.2⟩
  have hcluster : ∀ index point, point ∈ selected.carrier index →
      ‖wz1Cross (family.tube (center point)).direction
        (family.tube index).direction‖ < kappa := by
    intro index point hpoint
    exact hpoint.2
  let planeMap : PaperWZ1WeakPlaneMapData selected kappa :=
    { planeMap := fun point =>
        orthogonalNormal (family.tube (center point)).direction
      measurable := by
        have hfinite : Measurable fun candidate : Fin family.card =>
            orthogonalNormal (family.tube candidate).direction :=
          measurable_of_finite _
        exact hfinite.comp hcenterMeasurable
      unit := by
        intro point _
        exact orthogonalNormal_unit (family.tube (center point)).direction
      incidence := by
        intro index point hpoint
        exact orthogonalNormal_incidence_of_cross_lt
          (family.tube (center point)).direction
          (family.tube index).direction
          (family.tube (center point)).direction_unit
          (family.tube index).direction_unit hpoint.2 }
  have hmultiplicity : ∀ point ∈ denseCells.union,
      R ≤ selected.pointMultiplicity point := by
    intro point hpoint
    have hpointDense : point ∈ dense := by
      rcases hpoint with ⟨index, hindex⟩
      exact hindex.2
    have hlarge := (hcenterDense point hpoint).2
    have heq : paperCloseDirectionCount source point (center point) kappa =
        selected.pointMultiplicity point := by
      simp only [paperCloseDirectionCount,
        Kakeya.Streamlined.Shading.pointMultiplicity]
      congr 1
      apply Finset.ext
      intro index
      simp [selected, denseCells, paperRestrictShadingToSet, hpointDense]
    rw [heq] at hlarge
    dsimp only [threshold] at hlarge
    omega
  have hmassMultiplicity : ∀ point ∈ denseCells.union,
      denseCells.pointMultiplicity point ≤
        48 * selected.pointMultiplicity point := by
    intro point hpoint
    have hpointDense : point ∈ dense := by
      rcases hpoint with ⟨index, hindex⟩
      exact hindex.2
    have hpointSource : point ∈ source.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hindex.1⟩
    have hdenseMultiplicity : denseCells.pointMultiplicity point =
        source.pointMultiplicity point :=
      paperPmRestrictShadingToSet hDense hpointDense
    have hupper := hmultUpper point hpointSource
    have hlower := hmultiplicity point hpoint
    dsimp only [R] at hR hlower
    rw [hdenseMultiplicity]
    omega
  have hmass : (1 / 48 : ENNReal) * denseCells.mass ≤ selected.mass := by
    simpa [one_div] using
      (paper_mass_lower_from_pointMultiplicity_const 48 (by norm_num)
        hmassMultiplicity)
  have hplaneCell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      planeMap.planeMap first = planeMap.planeMap second := by
    intro first second hcell
    exact congrArg
      (fun index : Fin family.card =>
        orthogonalNormal (family.tube index).direction)
      (hcenterCell first second hcell)
  exact ⟨center, selected, planeMap, hcenterMeasurable, hselectedSub,
    hselectedCubical, hcluster, hcenterCell, (by
      intro point hpoint
      have hpointDense : point ∈ denseCells.union := by
        rcases hpoint with ⟨index, hindex⟩
        exact ⟨index, hselectedSub index hindex⟩
      exact hmultiplicity point hpointDense), hplaneCell, hmass⟩

/-- The dyadic direction dichotomy with constants compatible with the
variable-`Q` sparse transverse-triple budget. -/
theorem balanced_direction_dichotomy
    {delta kappa : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (hfamily : family.Nonempty)
    (hcubical : WZ1PaperIsCubicalShading source)
    (m : ℕ)
    (hm : 12 ≤ m)
    (hmultiplicityLower : ∀ point ∈ source.union,
      m ≤ source.pointMultiplicity point)
    (hmultiplicityUpper : ∀ point ∈ source.union,
      source.pointMultiplicity point < 2 * m) :
    Nonempty (BalancedDirectionDichotomyData
      (kappa := kappa) source m) := by
  let R := m / 12
  let threshold := 2 * R - 1
  let dense := denseCloseCellSet source kappa threshold
  let hDense := denseCloseCellSet_measurable source kappa threshold
  let denseCells := paperRestrictShadingToSet source dense hDense
  let sparseCells := paperRestrictShadingToSet source denseᶜ hDense.compl
  have hR : 0 < R := by
    dsimp only [R]
    omega
  have hbudget : 12 * R ≤ m := by
    dsimp only [R]
    omega
  rcases dense_or_sparse_close_mass source kappa threshold with
      hdense | hsparse
  · rcases dense_close_div_twelve_refinement
        (kappa := kappa) hcubical hfamily m hm hmultiplicityUpper with
      ⟨center, selected, planeMap, hcenterMeasurable, hselectedSub,
        hselectedCubical, hcluster, hcenterCell, hselectedMultiplicity,
        hplaneCell, hselectedMass⟩
    have hdenseSub : PaperIsSubshading denseCells source := by
      intro index point hpoint
      exact hpoint.1
    have hmass : source.mass ≤ 96 * selected.mass := by
      calc
        source.mass ≤ 2 * denseCells.mass := by
          have hscaled := mul_le_mul_left' hdense (2 : ENNReal)
          have hcancel : (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
            rw [one_div]
            exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
          calc
            source.mass = 2 * ((1 / 2 : ENNReal) * source.mass) := by
              rw [← mul_assoc, hcancel, one_mul]
            _ ≤ 2 * denseCells.mass := hscaled
        _ ≤ 2 * (48 * selected.mass) := by
          gcongr
          have hscaled := mul_le_mul_left' hselectedMass (48 : ENNReal)
          have hcancel : (48 : ENNReal) * (1 / 48 : ENNReal) = 1 := by
            rw [one_div]
            exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
          calc
            denseCells.mass =
                48 * ((1 / 48 : ENNReal) * denseCells.mass) := by
              rw [← mul_assoc, hcancel, one_mul]
            _ ≤ 48 * selected.mass := hscaled
        _ = 96 * selected.mass := by ring
    exact ⟨BalancedDirectionDichotomyData.dense R denseCells selected
      center planeMap rfl hR hbudget hdenseSub hselectedSub
      hselectedCubical hcenterMeasurable hcluster hcenterCell hplaneCell
      (by
        intro point hpoint
        exact hselectedMultiplicity point hpoint) hmass⟩
  · rcases sparse_close_cellwise_refinement hcubical threshold with
      ⟨hsparseSub, hsparseCubical, hclose⟩
    have hsparseMultiplicity : ∀ point ∈ sparseCells.union,
        m ≤ sparseCells.pointMultiplicity point := by
      intro point hpoint
      have hpointSource : point ∈ source.union := by
        rcases hpoint with ⟨index, hindex⟩
        exact ⟨index, hsparseSub index hindex⟩
      have hpointSparse : point ∈ denseᶜ := by
        rcases hpoint with ⟨index, hindex⟩
        exact hindex.2
      rw [paperPmRestrictShadingToSet hDense.compl hpointSparse]
      exact hmultiplicityLower point hpointSource
    have hcloseStrict : ∀ point ∈ sparseCells.union, ∀ index,
        point ∈ sparseCells.carrier index →
        paperCloseDirectionCount sparseCells point index kappa < R := by
      intro point hpoint index hindex
      have hle : 2 * paperCloseDirectionCount sparseCells point index kappa ≤
          2 * R - 1 := by
        simpa [sparseCells, threshold, R] using
          hclose point hpoint index hindex
      omega
    have hsparseMultiplicityUpper : ∀ point ∈ sparseCells.union,
        sparseCells.pointMultiplicity point < 2 * m := by
      intro point hpoint
      have hpointSource : point ∈ source.union := by
        rcases hpoint with ⟨index, hindex⟩
        exact ⟨index, hsparseSub index hindex⟩
      have hpointSparse : point ∈ denseᶜ := by
        rcases hpoint with ⟨index, hindex⟩
        exact hindex.2
      rw [paperPmRestrictShadingToSet hDense.compl hpointSparse]
      exact hmultiplicityUpper point hpointSource
    have hmass : source.mass ≤ 2 * sparseCells.mass := by
      have hscaled := mul_le_mul_left' hsparse (2 : ENNReal)
      have hcancel : (2 : ENNReal) * (1 / 2 : ENNReal) = 1 := by
        rw [one_div]
        exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      calc
        source.mass = 2 * ((1 / 2 : ENNReal) * source.mass) := by
          rw [← mul_assoc, hcancel, one_mul]
        _ ≤ 2 * sparseCells.mass := hscaled
    exact ⟨BalancedDirectionDichotomyData.sparse R sparseCells rfl hR
      hbudget hsparseSub hsparseCubical hsparseMultiplicity
      hsparseMultiplicityUpper hcloseStrict hmass⟩

end Kakeya.Assouad.PureWZ2

end
