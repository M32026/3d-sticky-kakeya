import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperTransversePairCount
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.TransversePairPaper
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperCubicalRefinement

/-!
# Cellwise plane map from the sparse-close branch and Q=1 pruning

On the sparse-close branch, at least half of all ordered active direction
pairs are transverse.  After `Q = 1` narrow pruning, every active triple has
small determinant.  Choosing a transverse pair constantly on each fine cell
therefore gives a genuine weak plane map on the whole narrow shading, without
the incompatible `12 R ≤ m` budget used by the older combinatorial wrapper.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- Lower-left corner of a paper grid cell. -/
private def sparseQ1CellCorner
    (delta : ℝ) (cell : ℤ × ℤ × ℤ) : Point3 :=
  WithLp.toLp 2 fun coordinate : Fin 3 =>
    delta * match coordinate with
      | 0 => cell.1
      | 1 => cell.2.1
      | 2 => cell.2.2

private lemma sparseQ1CellCorner_mem_cube
    {delta : ℝ} (hdelta : 0 < delta) (cell : ℤ × ℤ × ℤ) :
    sparseQ1CellCorner delta cell ∈ wz1PaperGridCube delta cell := by
  rw [mem_wz1PaperGridCube]
  simp only [sparseQ1CellCorner, wz1PaperGridIndex, gridIndex]
  have h0 : ⌊(delta * (cell.1 : ℝ)) / delta⌋ = cell.1 := by
    have h : (delta * (cell.1 : ℝ)) / delta = (cell.1 : ℝ) := by
      field_simp [hdelta.ne']
    rw [h]
    simp
  have h1 : ⌊(delta * (cell.2.1 : ℝ)) / delta⌋ = cell.2.1 := by
    have h : (delta * (cell.2.1 : ℝ)) / delta =
        (cell.2.1 : ℝ) := by
      field_simp [hdelta.ne']
    rw [h]
    simp
  have h2 : ⌊(delta * (cell.2.2 : ℝ)) / delta⌋ = cell.2.2 := by
    have h : (delta * (cell.2.2 : ℝ)) / delta =
        (cell.2.2 : ℝ) := by
      field_simp [hdelta.ne']
    rw [h]
    simp
  exact Prod.ext h0 (Prod.ext h1 h2)

/-- A point surviving narrow pruning has exactly the same active tube set as
in the source shading. -/
lemma paper_narrow_carrier_mem_iff
    {delta tau : ℝ} {Q : ℕ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    (narrow : PaperWZ1NarrowRefinementData Y tau Q)
    {point : Point3} (hpoint : point ∈ narrow.shading.union)
    (index : Fin F.card) :
    point ∈ narrow.shading.carrier index ↔ point ∈ Y.carrier index := by
  rcases hpoint with ⟨witness, hwitness⟩
  have hnotBroad : point ∉ paperCountedBroadSet Y tau Q := by
    rw [narrow.carrier_eq witness] at hwitness
    exact hwitness.2
  rw [narrow.carrier_eq index]
  simp [hnotBroad]

/-- Narrow pruning preserves point multiplicity at every surviving point. -/
lemma paper_narrow_pointMultiplicity_eq
    {delta tau : ℝ} {Q : ℕ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    (narrow : PaperWZ1NarrowRefinementData Y tau Q)
    {point : Point3} (hpoint : point ∈ narrow.shading.union) :
    narrow.shading.pointMultiplicity point = Y.pointMultiplicity point := by
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr 1
  ext index
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact paper_narrow_carrier_mem_iff narrow hpoint index

/-- Narrow pruning preserves close-direction counts at every surviving
point, because it removes a spatial set uniformly from all carriers. -/
lemma paper_narrow_closeDirectionCount_eq
    {delta tau kappa : ℝ} {Q : ℕ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    (narrow : PaperWZ1NarrowRefinementData Y tau Q)
    {point : Point3} (hpoint : point ∈ narrow.shading.union)
    (center : Fin F.card) :
    paperCloseDirectionCount narrow.shading point center kappa =
      paperCloseDirectionCount Y point center kappa := by
  unfold paperCloseDirectionCount
  congr 1
  apply Finset.filter_congr
  intro index _
  rw [paper_narrow_carrier_mem_iff narrow hpoint index]

/-- For `Q = 1`, no large active triple survives narrow pruning. -/
lemma paper_narrow_q1_triple_product_bound
    {delta tau : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    (narrow : PaperWZ1NarrowRefinementData Y tau 1)
    {point : Point3} (hpoint : point ∈ narrow.shading.union)
    {first second third : Fin F.card}
    (hfirst : point ∈ narrow.shading.carrier first)
    (hsecond : point ∈ narrow.shading.carrier second)
    (hthird : point ∈ narrow.shading.carrier third) :
    |wz1TripleProduct
      (F.tube first).direction
      (F.tube second).direction
      (F.tube third).direction| ≤ tau := by
  have hzero : paperLargeTripleCount narrow.shading point tau = 0 := by
    have hlt := narrow.large_triple_count_lt point hpoint
    omega
  by_contra hnot
  have hlarge : tau ≤ |wz1TripleProduct
      (F.tube first).direction
      (F.tube second).direction
      (F.tube third).direction| := (lt_of_not_ge hnot).le
  have hpositive : 0 < paperLargeTripleCount narrow.shading point tau := by
    unfold paperLargeTripleCount
    apply Finset.card_pos.mpr
    refine ⟨(first, (second, third)), ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_univ _, Finset.mem_product.mpr
        ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩,
      hfirst, hsecond, hthird, hlarge⟩
  omega

/-- Sparse close clusters and a pointwise multiplicity floor force at least
one transverse ordered pair through every point. -/
lemma paper_transverse_pair_exists_of_sparse_close
    {delta kappa : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    (fineMultiplicity : ℕ)
    (hmult : ∀ point ∈ Y.union,
      fineMultiplicity ≤ Y.pointMultiplicity point)
    (hclose : ∀ point ∈ Y.union, ∀ index,
      point ∈ Y.carrier index →
      2 * paperCloseDirectionCount Y point index kappa ≤
        fineMultiplicity) :
    ∀ point ∈ Y.union,
      ∃ first second : Fin F.card,
        point ∈ Y.carrier first ∧
        point ∈ Y.carrier second ∧
        kappa ≤ ‖wz1Cross (F.tube first).direction
          (F.tube second).direction‖ := by
  intro point hpoint
  let active : Finset (Fin F.card) :=
    Finset.univ.filter fun index => point ∈ Y.carrier index
  let transversePairs : Finset (Fin F.card × Fin F.card) :=
    (active ×ˢ active).filter fun pair =>
      kappa ≤ ‖wz1Cross (F.tube pair.1).direction
        (F.tube pair.2).direction‖
  have hpairsLower : Y.pointMultiplicity point ^ 2 ≤
      2 * transversePairs.card := by
    simpa only [active, transversePairs] using
      paper_transverse_ordered_pairs_lower
        hclose hmult point hpoint
  have hmultPositive : 0 < Y.pointMultiplicity point := by
    simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
    apply Finset.card_pos.mpr
    rcases hpoint with ⟨index, hindex⟩
    exact ⟨index, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hindex⟩⟩
  have hpairsPositive : 0 < transversePairs.card := by
    have hmultiplicitySquarePositive :
        0 < Y.pointMultiplicity point ^ 2 :=
      pow_pos hmultPositive 2
    omega
  rcases Finset.card_pos.mp hpairsPositive with ⟨pair, hpair⟩
  rcases Finset.mem_filter.mp hpair with ⟨hactive, htransverse⟩
  rcases Finset.mem_product.mp hactive with ⟨hfirst, hsecond⟩
  exact ⟨pair.1, pair.2,
    (Finset.mem_filter.mp hfirst).2,
    (Finset.mem_filter.mp hsecond).2, htransverse⟩

/-- The sparse-close branch followed by `Q = 1` narrow pruning carries a
measurable, fine-cell-constant transverse-pair normal on the whole surviving
shading.  No additional tube restriction is needed. -/
theorem paper_sparse_q1_cellwise_plane_map
    {delta kappa tau : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    (hdelta : 0 < delta) (hkappa : 0 < kappa)
    (hF : F.Nonempty)
    (hcubical : WZ1PaperIsCubicalShading Y)
    (fineMultiplicity : ℕ)
    (hmult : ∀ point ∈ Y.union,
      fineMultiplicity ≤ Y.pointMultiplicity point)
    (hclose : ∀ point ∈ Y.union, ∀ index,
      point ∈ Y.carrier index →
      2 * paperCloseDirectionCount Y point index kappa ≤
        fineMultiplicity)
    (narrow : PaperWZ1NarrowRefinementData Y tau 1) :
    ∃ (selection :
        PaperWZ1NarrowDirectionSelection narrow.shading kappa)
      (planeMap :
        PaperWZ1WeakPlaneMapData narrow.shading (tau / kappa)),
      WZ1PaperIsCubicalShading narrow.shading ∧
      (∀ first second,
        wz1PaperGridIndex delta first =
          wz1PaperGridIndex delta second →
        selection.first first = selection.first second ∧
        selection.second first = selection.second second) ∧
      (∀ first second,
        wz1PaperGridIndex delta first =
          wz1PaperGridIndex delta second →
        planeMap.planeMap first = planeMap.planeMap second) ∧
      (∀ point, planeMap.planeMap point = selection.normal point) ∧
      (1 / 2 : ENNReal) * Y.mass ≤ narrow.shading.mass := by
  classical
  let Z := narrow.shading
  have hZcubical : WZ1PaperIsCubicalShading Z :=
    narrow_pruning_preserves_cubical 1 hcubical narrow
  have hmultZ : ∀ point ∈ Z.union,
      fineMultiplicity ≤ Z.pointMultiplicity point := by
    intro point hpoint
    rw [paper_narrow_pointMultiplicity_eq narrow hpoint]
    have hpointY : point ∈ Y.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, narrow.subshading index hindex⟩
    exact hmult point hpointY
  have hcloseZ : ∀ point ∈ Z.union, ∀ index,
      point ∈ Z.carrier index →
      2 * paperCloseDirectionCount Z point index kappa ≤
        fineMultiplicity := by
    intro point hpoint index hindex
    rw [paper_narrow_closeDirectionCount_eq narrow hpoint index]
    have hpointY : point ∈ Y.union :=
      ⟨index, narrow.subshading index hindex⟩
    exact hclose point hpointY index (narrow.subshading index hindex)
  have htransverseZ : ∀ point ∈ Z.union,
      ∃ first second : Fin F.card,
        point ∈ Z.carrier first ∧
        point ∈ Z.carrier second ∧
        kappa ≤ ‖wz1Cross (F.tube first).direction
          (F.tube second).direction‖ :=
    paper_transverse_pair_exists_of_sparse_close
      fineMultiplicity hmultZ hcloseZ

  let Pair := Fin F.card × Fin F.card
  let pairEquiv : Pair ≃ Fin (Fintype.card Pair) :=
    Fintype.equivFin Pair
  letI : LinearOrder Pair := Equiv.linearOrder pairEquiv
  let defaultIndex : Fin F.card := ⟨0, hF⟩
  let defaultPair : Pair := (defaultIndex, defaultIndex)
  let Qualifies (point : Point3) (pair : Pair) : Prop :=
    point ∈ Z.carrier pair.1 ∧
    point ∈ Z.carrier pair.2 ∧
    kappa ≤ ‖wz1Cross (F.tube pair.1).direction
      (F.tube pair.2).direction‖
  let P (cell : ℤ × ℤ × ℤ) (pair : Pair) : Prop :=
    let corner := sparseQ1CellCorner delta cell
    (corner ∈ Z.union ∧ Qualifies corner pair) ∨
      (corner ∉ Z.union ∧ pair = defaultPair)
  let candidates (cell : ℤ × ℤ × ℤ) : Finset Pair :=
    Finset.univ.filter fun pair => P cell pair
  have hcandidates : ∀ cell, (candidates cell).Nonempty := by
    intro cell
    let corner := sparseQ1CellCorner delta cell
    by_cases hcorner : corner ∈ Z.union
    · rcases htransverseZ corner hcorner with
        ⟨first, second, hfirst, hsecond, htransverse⟩
      refine ⟨(first, second), Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ?_⟩⟩
      exact Or.inl ⟨hcorner, hfirst, hsecond, htransverse⟩
    · refine ⟨defaultPair, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ?_⟩⟩
      exact Or.inr ⟨hcorner, rfl⟩
  let chosenCell (cell : ℤ × ℤ × ℤ) : Pair :=
    (candidates cell).min' (hcandidates cell)
  have hchosenCell : ∀ cell, P cell (chosenCell cell) := by
    intro cell
    exact (Finset.mem_filter.mp
      (Finset.min'_mem (candidates cell) (hcandidates cell))).2
  let chosen (point : Point3) : Pair :=
    chosenCell (wz1PaperGridIndex delta point)
  let first (point : Point3) : Fin F.card := (chosen point).1
  let second (point : Point3) : Fin F.card := (chosen point).2
  have hgridMeasurable : Measurable (wz1PaperGridIndex delta) := by
    have h : Measurable (fun point : Point3 =>
        (⌊point 0 / delta⌋, ⌊point 1 / delta⌋,
          ⌊point 2 / delta⌋)) := by
      fun_prop
    convert h using 1
    funext point
    simp [wz1PaperGridIndex, gridIndex]
  have hchosenMeasurable : Measurable chosen := by
    change Measurable (chosenCell ∘ wz1PaperGridIndex delta)
    exact (show Measurable chosenCell from Measurable.of_discrete).comp
      hgridMeasurable
  have hfirstMeasurable : Measurable first := hchosenMeasurable.fst
  have hsecondMeasurable : Measurable second := hchosenMeasurable.snd
  have hchosenCellConstant : ∀ firstPoint secondPoint,
      wz1PaperGridIndex delta firstPoint =
        wz1PaperGridIndex delta secondPoint →
      chosen firstPoint = chosen secondPoint := by
    intro firstPoint secondPoint hcell
    simp [chosen, hcell]
  have hcornerData : ∀ point ∈ Z.union,
      let corner :=
        sparseQ1CellCorner delta (wz1PaperGridIndex delta point)
      corner ∈ Z.union ∧ Qualifies corner (chosen point) := by
    intro point hpoint
    let cell := wz1PaperGridIndex delta point
    let corner := sparseQ1CellCorner delta cell
    have hcornerCube : corner ∈ wz1PaperGridCube delta cell :=
      sparseQ1CellCorner_mem_cube hdelta cell
    rcases hpoint with ⟨index, hindex⟩
    have hcornerCarrier : corner ∈ Z.carrier index :=
      hZcubical index point hindex hcornerCube
    have hcornerUnion : corner ∈ Z.union := ⟨index, hcornerCarrier⟩
    have hspec := hchosenCell cell
    change P cell (chosen point) at hspec
    rcases hspec with hgood | hdefault
    · exact ⟨hcornerUnion, hgood.2⟩
    · exact False.elim (hdefault.1 hcornerUnion)
  have hfirstMem : ∀ point ∈ Z.union,
      point ∈ Z.carrier (first point) := by
    intro point hpoint
    let corner :=
      sparseQ1CellCorner delta (wz1PaperGridIndex delta point)
    have hsame : wz1PaperGridIndex delta corner =
        wz1PaperGridIndex delta point :=
      (mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) corner).mp
        (sparseQ1CellCorner_mem_cube hdelta
          (wz1PaperGridIndex delta point))
    exact (hZcubical.carrier_mem_iff_of_same_cell
      (first point) hsame).mp (hcornerData point hpoint).2.1
  have hsecondMem : ∀ point ∈ Z.union,
      point ∈ Z.carrier (second point) := by
    intro point hpoint
    let corner :=
      sparseQ1CellCorner delta (wz1PaperGridIndex delta point)
    have hsame : wz1PaperGridIndex delta corner =
        wz1PaperGridIndex delta point :=
      (mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) corner).mp
        (sparseQ1CellCorner_mem_cube hdelta
          (wz1PaperGridIndex delta point))
    exact (hZcubical.carrier_mem_iff_of_same_cell
      (second point) hsame).mp (hcornerData point hpoint).2.2.1
  have htransverse : ∀ point ∈ Z.union,
      kappa ≤ ‖wz1Cross (F.tube (first point)).direction
        (F.tube (second point)).direction‖ := by
    intro point hpoint
    exact (hcornerData point hpoint).2.2.2
  let selection : PaperWZ1NarrowDirectionSelection Z kappa :=
    { first := first
      second := second
      first_measurable := hfirstMeasurable
      second_measurable := hsecondMeasurable
      first_mem := hfirstMem
      second_mem := hsecondMem
      transverse := htransverse }
  let planeMap : PaperWZ1WeakPlaneMapData Z (tau / kappa) :=
    { planeMap := selection.normal
      measurable := selection.normal_measurable
      unit := by
        intro point hpoint
        let cross := wz1Cross (F.tube (first point)).direction
          (F.tube (second point)).direction
        have hcrossPositive : 0 < ‖cross‖ :=
          hkappa.trans_le (htransverse point hpoint)
        change ‖(‖cross‖)⁻¹ • cross‖ = 1
        rw [norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_pos hcrossPositive]
        field_simp [hcrossPositive.ne']
      incidence := by
        intro index point hpoint
        have hpointUnion : point ∈ Z.union := ⟨index, hpoint⟩
        let u := (F.tube (first point)).direction
        let v := (F.tube (second point)).direction
        let w := (F.tube index).direction
        let cross := wz1Cross u v
        have hcross : kappa ≤ ‖cross‖ := htransverse point hpointUnion
        have hcrossPositive : 0 < ‖cross‖ := hkappa.trans_le hcross
        have htriple : |wz1TripleProduct u v w| ≤ tau :=
          paper_narrow_q1_triple_product_bound narrow hpointUnion
            (hfirstMem point hpointUnion)
            (hsecondMem point hpointUnion) hpoint
        have hinner : inner ℝ w cross =
            wz1TripleProduct u v w := inner_cross_triple u v w
        change |inner ℝ w ((‖cross‖)⁻¹ • cross)| ≤ tau / kappa
        rw [inner_smul_right, hinner, abs_mul, abs_inv,
          abs_of_pos hcrossPositive]
        calc
          ‖cross‖⁻¹ * |wz1TripleProduct u v w| =
              |wz1TripleProduct u v w| / ‖cross‖ := by
            rw [div_eq_mul_inv, mul_comm]
          _ ≤ tau / kappa :=
            (div_le_div_of_nonneg_left (abs_nonneg _) hkappa hcross).trans
              (div_le_div_of_nonneg_right htriple hkappa.le) }
  have hselectionCell : ∀ firstPoint secondPoint,
      wz1PaperGridIndex delta firstPoint =
        wz1PaperGridIndex delta secondPoint →
      selection.first firstPoint = selection.first secondPoint ∧
      selection.second firstPoint = selection.second secondPoint := by
    intro firstPoint secondPoint hcell
    have hchosen := hchosenCellConstant firstPoint secondPoint hcell
    exact ⟨congrArg Prod.fst hchosen, congrArg Prod.snd hchosen⟩
  have hplaneCell : ∀ firstPoint secondPoint,
      wz1PaperGridIndex delta firstPoint =
        wz1PaperGridIndex delta secondPoint →
      planeMap.planeMap firstPoint = planeMap.planeMap secondPoint := by
    intro firstPoint secondPoint hcell
    rcases hselectionCell firstPoint secondPoint hcell with
      ⟨hfirst, hsecond⟩
    have hfirst' : first firstPoint = first secondPoint := hfirst
    have hsecond' : second firstPoint = second secondPoint := hsecond
    change selection.normal firstPoint = selection.normal secondPoint
    simp only [PaperWZ1NarrowDirectionSelection.normal, selection]
    rw [hfirst', hsecond']
  exact ⟨selection, planeMap, hZcubical, hselectionCell, hplaneCell,
    fun _ => rfl, narrow.mass_lower⟩

end Kakeya.Assouad.PureWZ2

end
