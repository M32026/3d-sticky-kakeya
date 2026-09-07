import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteLabelMassRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CubicalRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.NeighborPackingBound

/-!
# Fixed residue refinement for nearby coarse cells

Color `rho`-grid cells by their three coordinates modulo `3`.  Two points at
distance at most `rho` have grid indices differing by at most one in each
coordinate.  If their cells have the same residue, the indices are equal.
Keeping the heaviest of the 27 residue classes therefore upgrades same-cell
variation to a nearby-point estimate with only a fixed loss.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

private lemma nearby_abs_floor_sub_le {x y : ℝ} {n : ℕ}
    (h : |x - y| ≤ (n : ℝ)) :
    |(Int.floor x : ℤ) - (Int.floor y : ℤ)| ≤ (n : ℤ) := by
  have hxy : x - y ≤ (n : ℝ) := (abs_le.mp h).2
  have hyx : y - x ≤ (n : ℝ) := by
    have : |y - x| ≤ (n : ℝ) := by simpa [abs_sub_comm] using h
    exact (abs_le.mp this).2
  have hfloorXY : (Int.floor x : ℤ) - (Int.floor y : ℤ) ≤ (n : ℤ) := by
    by_contra hnot
    have hint : (Int.floor x : ℤ) - (Int.floor y : ℤ) ≥ (n : ℤ) + 1 := by
      omega
    have hreal : (Int.floor x : ℝ) - (Int.floor y : ℝ) ≥ (n : ℝ) + 1 := by
      exact_mod_cast hint
    linarith [Int.floor_le x, Int.lt_floor_add_one y]
  have hfloorYX : (Int.floor y : ℤ) - (Int.floor x : ℤ) ≤ (n : ℤ) := by
    by_contra hnot
    have hint : (Int.floor y : ℤ) - (Int.floor x : ℤ) ≥ (n : ℤ) + 1 := by
      omega
    have hreal : (Int.floor y : ℝ) - (Int.floor x : ℝ) ≥ (n : ℝ) + 1 := by
      exact_mod_cast hint
    linarith [Int.floor_le y, Int.lt_floor_add_one x]
  exact abs_le.mpr ⟨by linarith, hfloorXY⟩

private def gridResidue3 (cell : ℤ × ℤ × ℤ) : Fin 3 × Fin 3 × Fin 3 :=
  let residue (n : ℤ) : Fin 3 :=
    ⟨(n % 3).toNat, by
      have hnonneg : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
      have hlt : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
      omega⟩
  (residue cell.1, residue cell.2.1, residue cell.2.2)

private lemma gridResidue3_coordinate_eq
    {first second : ℤ}
    (hresidue :
      (⟨(first % 3).toNat, by
          have hnonneg : 0 ≤ first % 3 := Int.emod_nonneg first (by norm_num)
          have hlt : first % 3 < 3 := Int.emod_lt_of_pos first (by norm_num)
          omega⟩ : Fin 3) =
        ⟨(second % 3).toNat, by
          have hnonneg : 0 ≤ second % 3 := Int.emod_nonneg second (by norm_num)
          have hlt : second % 3 < 3 := Int.emod_lt_of_pos second (by norm_num)
          omega⟩)
    (hclose : |first - second| ≤ 2) :
    first = second := by
  have hmodNat : (first % 3).toNat = (second % 3).toNat :=
    congrArg Fin.val hresidue
  have hfirstNonneg : 0 ≤ first % 3 := Int.emod_nonneg first (by norm_num)
  have hsecondNonneg : 0 ≤ second % 3 := Int.emod_nonneg second (by norm_num)
  have hmod : first % 3 = second % 3 := by
    rw [← Int.toNat_of_nonneg hfirstNonneg,
      ← Int.toNat_of_nonneg hsecondNonneg]
    exact_mod_cast hmodNat
  have hdiv : (3 : ℤ) ∣ first - second := by
    have hzero : (first - second) % 3 = 0 := by
      rw [Int.sub_emod, hmod]
      simp
    exact Int.dvd_of_emod_eq_zero hzero
  rcases hdiv with ⟨multiple, hmultiple⟩
  have hmultipleSmall : |3 * multiple| ≤ 2 := by
    rw [← hmultiple]
    exact hclose
  have hmultipleZero : multiple = 0 := by
    by_contra hne
    have habs : (1 : ℤ) ≤ |multiple| := by
      exact (Int.add_one_le_iff.mpr (abs_pos.mpr hne))
    have hfactor : |3 * multiple| = 3 * |multiple| := by
      rw [abs_mul]
      norm_num
    rw [hfactor] at hmultipleSmall
    omega
  rw [hmultipleZero, mul_zero] at hmultiple
  omega

/-- Distance at most `rho` and equal mod-3 cell colors force equal grid
indices. -/
lemma nearby_same_residue_same_grid_cell
    {rho : ℝ} (hrho : 0 < rho) {p q : Point3}
    (hdist : dist p q ≤ rho)
    (hresidue :
      gridResidue3 (wz1PaperGridIndex rho p) =
        gridResidue3 (wz1PaperGridIndex rho q)) :
    wz1PaperGridIndex rho p = wz1PaperGridIndex rho q := by
  let first := wz1PaperGridIndex rho p
  let second := wz1PaperGridIndex rho q
  have hcoord : ∀ i : Fin 3, |p i / rho - q i / rho| ≤ 1 := by
    intro i
    have happly : |p i - q i| ≤ dist p q := PiLp.dist_apply_le p q i
    have hraw : |p i - q i| ≤ rho := happly.trans hdist
    have hdiv : |(p i - q i) / rho| ≤ rho / rho := by
      rw [abs_div, abs_of_pos hrho]
      gcongr
    have heq : (p i - q i) / rho = p i / rho - q i / rho := sub_div _ _ _
    rw [heq] at hdiv
    simpa [hrho.ne'] using hdiv
  have hfloor : ∀ i : Fin 3,
      |⌊p i / rho⌋ - ⌊q i / rho⌋| ≤ (2 : ℤ) := by
    intro i
    exact nearby_abs_floor_sub_le (n := 2)
      ((hcoord i).trans (by norm_num))
  have hres0 :
      (gridResidue3 first).1 = (gridResidue3 second).1 :=
    congrArg Prod.fst hresidue
  have hres1 :
      (gridResidue3 first).2.1 = (gridResidue3 second).2.1 :=
    congrArg (fun x => x.2.1) hresidue
  have hres2 :
      (gridResidue3 first).2.2 = (gridResidue3 second).2.2 :=
    congrArg (fun x => x.2.2) hresidue
  have h0 : first.1 = second.1 := by
    apply gridResidue3_coordinate_eq hres0
    simpa [first, second, wz1PaperGridIndex, gridIndex] using hfloor 0
  have h1 : first.2.1 = second.2.1 := by
    apply gridResidue3_coordinate_eq hres1
    simpa [first, second, wz1PaperGridIndex, gridIndex] using hfloor 1
  have h2 : first.2.2 = second.2.2 := by
    apply gridResidue3_coordinate_eq hres2
    simpa [first, second, wz1PaperGridIndex, gridIndex] using hfloor 2
  exact Prod.ext h0 (Prod.ext h1 h2)

/-- Fixed 27-color refinement upgrading same-cell plane-map variation to a
nearby-point estimate. -/
theorem paper_nearby_cell_residue_refinement
    {delta rho scale : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (planeMap : Point3 → Point3)
    (hrho : 0 < rho)
    (hsameCell : ∀ p ∈ S.union, ∀ q ∈ S.union,
      wz1PaperGridIndex rho p = wz1PaperGridIndex rho q →
        dist (planeMap p) (planeMap q) ≤ scale) :
    ∃ (selected : WZ1PaperTubeShading F),
      PaperIsSubshading selected S ∧
      (∀ p ∈ selected.union, ∀ q ∈ selected.union,
        dist p q ≤ rho → dist (planeMap p) (planeMap q) ≤ scale) ∧
      (∀ p ∈ selected.union,
        selected.pointMultiplicity p = S.pointMultiplicity p) ∧
      S.mass ≤ 27 * selected.mass := by
  let label : Point3 → Fin 3 × Fin 3 × Fin 3 := fun p =>
    gridResidue3 (wz1PaperGridIndex rho p)
  have hlabelMeasurable : Measurable label := by
    have hgrid : Measurable (wz1PaperGridIndex rho) := by
      have h : Measurable (fun p : Point3 =>
          (⌊p 0 / rho⌋, ⌊p 1 / rho⌋, ⌊p 2 / rho⌋)) := by
        fun_prop
      convert h using 1
      funext p
      simp [wz1PaperGridIndex, gridIndex]
    exact (show Measurable gridResidue3 from Measurable.of_discrete).comp hgrid
  rcases paper_finite_label_mass_refinement S label hlabelMeasurable with
    ⟨residue, selected, hsub, hselectedEq, hlabelSelected, hmass⟩
  refine ⟨selected, hsub, ?_, ?_, ?_⟩
  · intro p hp q hq hdist
    have hpS : p ∈ S.union := by
      rcases hp with ⟨i, hi⟩
      exact ⟨i, hsub i hi⟩
    have hqS : q ∈ S.union := by
      rcases hq with ⟨i, hi⟩
      exact ⟨i, hsub i hi⟩
    apply hsameCell p hpS q hqS
    apply nearby_same_residue_same_grid_cell hrho hdist
    change label p = label q
    rw [hlabelSelected p hp, hlabelSelected q hq]
  · rw [hselectedEq]
    exact paperFiniteLabelRestriction_pointMultiplicity_eq
      S label hlabelMeasurable residue (measurableSet_singleton residue)
  · have hcard : Fintype.card (Fin 3 × Fin 3 × Fin 3) = 27 := by decide
    simpa [hcard] using hmass

/-- At an integer-aligned coarse scale, the fixed residue refinement is also
constant on every fine `delta`-cell and therefore preserves cubicality. -/
theorem paper_aligned_nearby_cell_residue_refinement_cubical
    {delta rho scale : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (planeMap : Point3 → Point3)
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hcubical : WZ1PaperIsCubicalShading S)
    (K : ℕ) (hK : 0 < K) (hrhoEq : rho = (K : ℝ) * delta)
    (hsameCell : ∀ p ∈ S.union, ∀ q ∈ S.union,
      wz1PaperGridIndex rho p = wz1PaperGridIndex rho q →
        dist (planeMap p) (planeMap q) ≤ scale) :
    ∃ selected : WZ1PaperTubeShading F,
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ p ∈ selected.union, ∀ q ∈ selected.union,
        dist p q ≤ rho → dist (planeMap p) (planeMap q) ≤ scale) ∧
      (∀ p ∈ selected.union,
        selected.pointMultiplicity p = S.pointMultiplicity p) ∧
      S.mass ≤ 27 * selected.mass := by
  let label : Point3 → Fin 3 × Fin 3 × Fin 3 := fun p =>
    gridResidue3 (wz1PaperGridIndex rho p)
  have hlabelMeasurable : Measurable label := by
    have hgrid : Measurable (wz1PaperGridIndex rho) := by
      have h : Measurable (fun p : Point3 =>
          (⌊p 0 / rho⌋, ⌊p 1 / rho⌋, ⌊p 2 / rho⌋)) := by
        fun_prop
      convert h using 1
      funext p
      simp [wz1PaperGridIndex, gridIndex]
    exact (show Measurable gridResidue3 from Measurable.of_discrete).comp hgrid
  rcases paper_finite_label_mass_refinement S label hlabelMeasurable with
    ⟨residue, selected, hsub, hselectedEq, hlabelSelected, hmass⟩
  have hlabelFineCell : ∀ p q,
      wz1PaperGridIndex delta p = wz1PaperGridIndex delta q →
        label p = label q := by
    intro p q hfine
    have hcoarse := wz1PaperGridIndex_fine_to_coarse K hK hrhoEq hfine
    simp [label, hcoarse]
  have hselectedCubical : WZ1PaperIsCubicalShading selected := by
    rw [hselectedEq]
    exact paperFiniteLabelRestriction_cubical hcubical
      label hlabelMeasurable residue (measurableSet_singleton residue)
      hlabelFineCell
  refine ⟨selected, hsub, hselectedCubical, ?_, ?_, ?_⟩
  · intro p hp q hq hdist
    have hpS : p ∈ S.union := by
      rcases hp with ⟨i, hi⟩
      exact ⟨i, hsub i hi⟩
    have hqS : q ∈ S.union := by
      rcases hq with ⟨i, hi⟩
      exact ⟨i, hsub i hi⟩
    apply hsameCell p hpS q hqS
    apply nearby_same_residue_same_grid_cell hrho hdist
    change label p = label q
    rw [hlabelSelected p hp, hlabelSelected q hq]
  · rw [hselectedEq]
    exact paperFiniteLabelRestriction_pointMultiplicity_eq
      S label hlabelMeasurable residue (measurableSet_singleton residue)
  · have hcard : Fintype.card (Fin 3 × Fin 3 × Fin 3) = 27 := by decide
    simpa [hcard] using hmass

/-- Fine-cell specialization of the residue refinement which also preserves
paper cubicality.  The residue label is constant on every `delta`-grid cell,
so the selected common spatial restriction is again cubical. -/
theorem paper_fine_cell_residue_refinement_cubical
    {delta scale : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    (planeMap : Point3 → Point3)
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading S)
    (hsameCell : ∀ p ∈ S.union, ∀ q ∈ S.union,
      wz1PaperGridIndex delta p = wz1PaperGridIndex delta q →
        dist (planeMap p) (planeMap q) ≤ scale) :
    ∃ selected : WZ1PaperTubeShading F,
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ p ∈ selected.union, ∀ q ∈ selected.union,
        dist p q ≤ delta → dist (planeMap p) (planeMap q) ≤ scale) ∧
      (∀ p ∈ selected.union,
        selected.pointMultiplicity p = S.pointMultiplicity p) ∧
      S.mass ≤ 27 * selected.mass := by
  let label : Point3 → Fin 3 × Fin 3 × Fin 3 := fun p =>
    gridResidue3 (wz1PaperGridIndex delta p)
  have hlabelMeasurable : Measurable label := by
    have hgrid : Measurable (wz1PaperGridIndex delta) := by
      have h : Measurable (fun p : Point3 =>
          (⌊p 0 / delta⌋, ⌊p 1 / delta⌋,
            ⌊p 2 / delta⌋)) := by
        fun_prop
      convert h using 1
      funext p
      simp [wz1PaperGridIndex, gridIndex]
    exact (show Measurable gridResidue3 from Measurable.of_discrete).comp hgrid
  rcases paper_finite_label_mass_refinement S label hlabelMeasurable with
    ⟨residue, selected, hsub, hselectedEq, hlabelSelected, hmass⟩
  have hlabelCell : ∀ p q,
      wz1PaperGridIndex delta p = wz1PaperGridIndex delta q →
        label p = label q := by
    intro p q hgrid
    simp [label, hgrid]
  have hselectedCubical : WZ1PaperIsCubicalShading selected := by
    rw [hselectedEq]
    exact paperFiniteLabelRestriction_cubical
      hcubical label hlabelMeasurable residue
        (measurableSet_singleton residue) hlabelCell
  refine ⟨selected, hsub, hselectedCubical, ?_, ?_, ?_⟩
  · intro p hp q hq hdist
    have hpS : p ∈ S.union := by
      rcases hp with ⟨i, hi⟩
      exact ⟨i, hsub i hi⟩
    have hqS : q ∈ S.union := by
      rcases hq with ⟨i, hi⟩
      exact ⟨i, hsub i hi⟩
    apply hsameCell p hpS q hqS
    apply nearby_same_residue_same_grid_cell hdelta hdist
    change label p = label q
    rw [hlabelSelected p hp, hlabelSelected q hq]
  · rw [hselectedEq]
    exact paperFiniteLabelRestriction_pointMultiplicity_eq
      S label hlabelMeasurable residue (measurableSet_singleton residue)
  · have hcard : Fintype.card (Fin 3 × Fin 3 × Fin 3) = 27 := by decide
    simpa [hcard] using hmass

end Kakeya.Assouad

end
