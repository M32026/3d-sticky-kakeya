import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.TransversePairPaper
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DirectionControl
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperCubicalRefinement

/-!
# Cellwise weak planiness

The original measurable weak-planiness selector may choose a different
transverse pair at two points of the same cubical cell.  This module makes the
choice on the lower-left corner of each occupied `delta`-cell.  Cubicality
then makes the qualifying-pair predicate constant on the whole cell.  The
resulting normal is genuinely cellwise (rather than globally constant), keeps
the same one-quarter mass lower bound, and has incidence `tau / kappa`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Lower-left corner of a paper grid cell. -/
private def paperCellCorner (delta : ℝ) (cell : ℤ × ℤ × ℤ) : Point3 :=
  WithLp.toLp 2 fun i : Fin 3 =>
    delta * match i with
      | 0 => cell.1
      | 1 => cell.2.1
      | 2 => cell.2.2

private lemma paperCellCorner_mem_cube
    {delta : ℝ} (hdelta : 0 < delta) (cell : ℤ × ℤ × ℤ) :
    paperCellCorner delta cell ∈ wz1PaperGridCube delta cell := by
  rw [mem_wz1PaperGridCube]
  simp only [paperCellCorner, wz1PaperGridIndex, gridIndex]
  have h0 : ⌊(delta * (cell.1 : ℝ)) / delta⌋ = cell.1 := by
    have h : (delta * (cell.1 : ℝ)) / delta = (cell.1 : ℝ) := by
      field_simp [hdelta.ne']
    rw [h]
    simp
  have h1 : ⌊(delta * (cell.2.1 : ℝ)) / delta⌋ = cell.2.1 := by
    have h : (delta * (cell.2.1 : ℝ)) / delta = (cell.2.1 : ℝ) := by
      field_simp [hdelta.ne']
    rw [h]
    simp
  have h2 : ⌊(delta * (cell.2.2 : ℝ)) / delta⌋ = cell.2.2 := by
    have h : (delta * (cell.2.2 : ℝ)) / delta = (cell.2.2 : ℝ) := by
      field_simp [hdelta.ne']
    rw [h]
    simp
  exact Prod.ext h0 (Prod.ext h1 h2)

/-- A cubical narrow shading admits a weak plane map whose direction choice is
constant on every `delta`-cell. -/
theorem paper_cellwise_weak_planiness_from_narrow
    {delta kappa tau : ℝ} {Q R : ℕ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    (hdelta : 0 < delta)
    (hkappa : 0 < kappa)
    (hF : F.Nonempty)
    (hY_cubical : WZ1PaperIsCubicalShading Y)
    (narrow : PaperWZ1NarrowRefinementData Y tau Q)
    (hclose : ∀ p ∈ narrow.shading.union, ∀ i,
      p ∈ narrow.shading.carrier i →
        paperCloseDirectionCount narrow.shading p i kappa < R)
    (hmult : ∀ p ∈ narrow.shading.union,
      let mu := narrow.shading.pointMultiplicity p
      4 * (Q + 3 * R * mu ^ 2) ≤ 3 * mu ^ 3) :
    ∃ (selected : WZ1PaperTubeShading F)
      (selection : PaperWZ1NarrowDirectionSelection narrow.shading kappa)
      (planeMap : PaperWZ1WeakPlaneMapData selected (tau / kappa)),
      PaperIsSubshading selected narrow.shading ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ p q,
        wz1PaperGridIndex delta p = wz1PaperGridIndex delta q →
          planeMap.planeMap p = planeMap.planeMap q) ∧
      (∀ p q,
        wz1PaperGridIndex delta p = wz1PaperGridIndex delta q →
          selection.first p = selection.first q ∧
          selection.second p = selection.second q) ∧
      (∀ p, planeMap.planeMap p = selection.normal p) ∧
      (∀ p ∈ narrow.shading.union,
        narrow.shading.pointMultiplicity p ≤
          4 * selected.pointMultiplicity p) ∧
      (1 / 4 : ENNReal) * narrow.shading.mass ≤ selected.mass := by
  classical
  let Z := narrow.shading
  have hZ_cubical : WZ1PaperIsCubicalShading Z :=
    narrow_pruning_preserves_cubical Q hY_cubical narrow

  have hGoodPair : ∀ p : Point3, p ∈ Z.union →
      ∃ i j : Fin F.card,
        p ∈ Z.carrier i ∧
        p ∈ Z.carrier j ∧
        kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ ∧
        Z.pointMultiplicity p ≤ 4 * paperGoodThirdCount Z p i j tau := by
    intro p hp
    let A : Finset (Fin F.card) :=
      Finset.univ.filter fun i => p ∈ Z.carrier i
    have hAcard : A.card = Z.pointMultiplicity p := by
      simp [A, Kakeya.Streamlined.Shading.pointMultiplicity]
      rfl
    let Broad : Fin F.card → Fin F.card → Fin F.card → Prop :=
      fun i j k => tau ≤ |wz1TripleProduct
        (F.tube i).direction (F.tube j).direction (F.tube k).direction|
    let Close : Fin F.card → Fin F.card → Prop :=
      fun i j => ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ < kappa
    have hBroad :
        ((A.product (A.product A)).filter
          (fun x : Fin F.card × (Fin F.card × Fin F.card) =>
            Broad x.1 x.2.1 x.2.2)).card < Q := by
      let S := (A.product (A.product A)).filter
          (fun x : Fin F.card × (Fin F.card × Fin F.card) =>
            Broad x.1 x.2.1 x.2.2)
      have h1 : S.card = paperLargeTripleCount Z p tau := by
        have h_eq : S =
            (Finset.univ.product (Finset.univ.product Finset.univ)).filter
              (fun x : Fin F.card × (Fin F.card × Fin F.card) =>
                p ∈ Z.carrier x.1 ∧ p ∈ Z.carrier x.2.1 ∧
                p ∈ Z.carrier x.2.2 ∧ Broad x.1 x.2.1 x.2.2) := by
          apply Finset.ext
          intro x
          have hAmem : ∀ i : Fin F.card, i ∈ A ↔ p ∈ Z.carrier i := by
            intro i
            simp [A, Finset.mem_filter]
          simp [S, A, Broad, Finset.mem_filter, Finset.mem_product,
            Finset.mem_univ, hAmem]
          tauto
        rw [h_eq]
        rfl
      rw [h1]
      exact narrow.large_triple_count_lt p hp
    have hClose : ∀ i ∈ A, (A.filter fun j => Close i j).card < R := by
      intro i hi
      have hi' : p ∈ Z.carrier i := by
        simpa [A, Finset.mem_filter] using hi
      have hEq : (A.filter fun j => Close i j).card =
          paperCloseDirectionCount Z p i kappa := by
        simp [Close, A, paperCloseDirectionCount, Finset.filter_filter]
        congr
      rw [hEq]
      exact hclose p hp i hi'
    have hMain : 4 * (Q + 3 * R * A.card ^ 2) ≤ 3 * A.card ^ 3 := by
      rw [hAcard]
      exact hmult p hp
    rcases combinatorial_pigeonhole A Broad Close Q R hBroad hClose hMain with
      ⟨i, hi, j, hj, hNotClose, hCount⟩
    have hi' : p ∈ Z.carrier i := by simpa [A, Finset.mem_filter] using hi
    have hj' : p ∈ Z.carrier j := by simpa [A, Finset.mem_filter] using hj
    have hTransverse :
        kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ :=
      Std.not_lt.mp hNotClose
    let good := A.filter fun k =>
      ¬Broad i j k ∧ ¬Close i j ∧ ¬Close i k ∧ ¬Close j k
    have hSubset : good ⊆ A.filter fun k =>
        |wz1TripleProduct (F.tube i).direction (F.tube j).direction
          (F.tube k).direction| < tau := by
      intro k hk
      have hFilter : ¬Broad i j k ∧ ¬Close i j ∧ ¬Close i k ∧ ¬Close j k :=
        (Finset.mem_filter.mp hk).2
      have hkA : k ∈ A := (Finset.mem_filter.mp hk).1
      have hNarrow : ¬Broad i j k := hFilter.1
      simp only [Broad, not_le] at hNarrow
      exact Finset.mem_filter.mpr ⟨hkA, hNarrow⟩
    have hCount2 : good.card ≤ (A.filter fun k =>
        |wz1TripleProduct (F.tube i).direction (F.tube j).direction
          (F.tube k).direction| < tau).card :=
      Finset.card_le_card hSubset
    have hGoodThird : (A.filter fun k =>
        |wz1TripleProduct (F.tube i).direction (F.tube j).direction
          (F.tube k).direction| < tau).card =
        paperGoodThirdCount Z p i j tau := by
      simp [paperGoodThirdCount, A, Finset.filter_filter]
      congr
    have hFinal :
        Z.pointMultiplicity p ≤ 4 * paperGoodThirdCount Z p i j tau := by
      rw [hAcard] at *
      rw [← hGoodThird]
      exact hCount.trans (mul_le_mul_of_nonneg_left hCount2 (by norm_num))
    exact ⟨i, j, hi', hj', hTransverse, hFinal⟩

  let Pair := Fin F.card × Fin F.card
  let pairEquiv : Pair ≃ Fin (Fintype.card Pair) := Fintype.equivFin Pair
  letI : LinearOrder Pair := Equiv.linearOrder pairEquiv
  let defaultIndex : Fin F.card := ⟨0, hF⟩
  let defaultPair : Pair := (defaultIndex, defaultIndex)
  let Qualifies (p : Point3) (ij : Pair) : Prop :=
    p ∈ Z.carrier ij.1 ∧ p ∈ Z.carrier ij.2 ∧
    kappa ≤ ‖wz1Cross (F.tube ij.1).direction (F.tube ij.2).direction‖ ∧
    Z.pointMultiplicity p ≤ 4 * paperGoodThirdCount Z p ij.1 ij.2 tau
  let P (cell : ℤ × ℤ × ℤ) (ij : Pair) : Prop :=
    let p := paperCellCorner delta cell
    (p ∈ Z.union ∧ Qualifies p ij) ∨
      (p ∉ Z.union ∧ ij = defaultPair)
  let candidates (cell : ℤ × ℤ × ℤ) : Finset Pair :=
    Finset.univ.filter fun ij => P cell ij
  have hcandidates : ∀ cell, (candidates cell).Nonempty := by
    intro cell
    let p := paperCellCorner delta cell
    by_cases hp : p ∈ Z.union
    · rcases hGoodPair p hp with ⟨i, j, hi, hj, htrans, hcount⟩
      refine ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      exact Or.inl ⟨hp, hi, hj, htrans, hcount⟩
    · refine ⟨defaultPair, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      exact Or.inr ⟨hp, rfl⟩
  let chosenCell (cell : ℤ × ℤ × ℤ) : Pair :=
    (candidates cell).min' (hcandidates cell)
  have hchosenCell : ∀ cell, P cell (chosenCell cell) := by
    intro cell
    exact (Finset.mem_filter.mp
      (Finset.min'_mem (candidates cell) (hcandidates cell))).2
  let chosen (p : Point3) : Pair :=
    chosenCell (wz1PaperGridIndex delta p)
  let first (p : Point3) : Fin F.card := (chosen p).1
  let second (p : Point3) : Fin F.card := (chosen p).2
  have hchosen_measurable : Measurable chosen := by
    have hgrid : Measurable (wz1PaperGridIndex delta) := by
      have h : Measurable (fun p : Point3 =>
          (⌊p 0 / delta⌋, ⌊p 1 / delta⌋, ⌊p 2 / delta⌋)) := by
        fun_prop
      convert h using 1
      funext p
      simp [wz1PaperGridIndex, gridIndex]
    change Measurable (chosenCell ∘ wz1PaperGridIndex delta)
    exact (show Measurable chosenCell from Measurable.of_discrete).comp hgrid
  have hfirst_measurable : Measurable first := hchosen_measurable.fst
  have hsecond_measurable : Measurable second := hchosen_measurable.snd
  have hchosen_const : ∀ p q,
      wz1PaperGridIndex delta p = wz1PaperGridIndex delta q →
        chosen p = chosen q := by
    intro p q hcell
    simp [chosen, hcell]

  have hcorner_data : ∀ p ∈ Z.union,
      let corner := paperCellCorner delta (wz1PaperGridIndex delta p)
      corner ∈ Z.union ∧ Qualifies corner (chosen p) := by
    intro p hp
    let cell := wz1PaperGridIndex delta p
    let corner := paperCellCorner delta cell
    have hcornerCube : corner ∈ wz1PaperGridCube delta cell :=
      paperCellCorner_mem_cube hdelta cell
    rcases hp with ⟨i, hi⟩
    have hcornerCarrier : corner ∈ Z.carrier i :=
      hZ_cubical i p hi hcornerCube
    have hcornerUnion : corner ∈ Z.union := ⟨i, hcornerCarrier⟩
    have hspec := hchosenCell cell
    change P cell (chosen p) at hspec
    have hchosen_def : chosen p = chosenCell cell := rfl
    rw [hchosen_def] at hspec
    rcases hspec with hspec | hspec
    · exact ⟨hcornerUnion, hspec.2⟩
    · exact False.elim (hspec.1 hcornerUnion)
  have hfirst_mem : ∀ p ∈ Z.union, p ∈ Z.carrier (first p) := by
    intro p hp
    let corner := paperCellCorner delta (wz1PaperGridIndex delta p)
    have hdata := hcorner_data p hp
    have hsame : wz1PaperGridIndex delta corner =
        wz1PaperGridIndex delta p := by
      exact (mem_wz1PaperGridCube _ _ _).mp
        (paperCellCorner_mem_cube hdelta (wz1PaperGridIndex delta p))
    exact (paper_cubical_same_cell_same_carriers hZ_cubical corner p hsame
      (first p)).mp hdata.2.1
  have hsecond_mem : ∀ p ∈ Z.union, p ∈ Z.carrier (second p) := by
    intro p hp
    let corner := paperCellCorner delta (wz1PaperGridIndex delta p)
    have hdata := hcorner_data p hp
    have hsame : wz1PaperGridIndex delta corner =
        wz1PaperGridIndex delta p := by
      exact (mem_wz1PaperGridCube _ _ _).mp
        (paperCellCorner_mem_cube hdelta (wz1PaperGridIndex delta p))
    exact (paper_cubical_same_cell_same_carriers hZ_cubical corner p hsame
      (second p)).mp hdata.2.2.1
  have htransverse : ∀ p ∈ Z.union,
      kappa ≤ ‖wz1Cross (F.tube (first p)).direction
        (F.tube (second p)).direction‖ := by
    intro p hp
    exact (hcorner_data p hp).2.2.2.1
  have hgood_count : ∀ p ∈ Z.union,
      Z.pointMultiplicity p ≤
        4 * paperGoodThirdCount Z p (first p) (second p) tau := by
    intro p hp
    let corner := paperCellCorner delta (wz1PaperGridIndex delta p)
    have hdata := hcorner_data p hp
    have hsame : wz1PaperGridIndex delta corner =
        wz1PaperGridIndex delta p := by
      exact (mem_wz1PaperGridCube _ _ _).mp
        (paperCellCorner_mem_cube hdelta (wz1PaperGridIndex delta p))
    have hmult_eq : Z.pointMultiplicity corner = Z.pointMultiplicity p :=
      hZ_cubical.pointMultiplicity_eq_of_same_cell hsame
    have hgood_eq : paperGoodThirdCount Z corner (first p) (second p) tau =
        paperGoodThirdCount Z p (first p) (second p) tau := by
      unfold paperGoodThirdCount
      congr 1
      apply Finset.filter_congr
      intro k _
      rw [paper_cubical_same_cell_same_carriers hZ_cubical corner p hsame k]
    rw [← hmult_eq, ← hgood_eq]
    exact hdata.2.2.2.2

  let selection : PaperWZ1NarrowDirectionSelection Z kappa :=
    { first := first
      second := second
      first_measurable := hfirst_measurable
      second_measurable := hsecond_measurable
      first_mem := hfirst_mem
      second_mem := hsecond_mem
      transverse := htransverse }
  let selected : WZ1PaperTubeShading F :=
    { carrier := fun k =>
        {p | p ∈ Z.carrier k ∧
          |wz1TripleProduct (F.tube (first p)).direction
            (F.tube (second p)).direction (F.tube k).direction| < tau}
      measurable_carrier := fun k =>
        (Z.measurable_carrier k).inter
          (measurable_selected_carrier hfirst_measurable hsecond_measurable k)
      subset_body := fun k p hp => Z.subset_body k hp.1 }
  have hselected_sub : PaperIsSubshading selected Z := fun _ _ hp => hp.1
  have hselected_cubical : WZ1PaperIsCubicalShading selected := by
    intro k p hp q hq
    have hcell : wz1PaperGridIndex delta q = wz1PaperGridIndex delta p :=
      (mem_wz1PaperGridCube _ _ _).mp hq
    have hcarrier : q ∈ Z.carrier k :=
      hZ_cubical k p hp.1 hq
    have hchoice : chosen q = chosen p := hchosen_const q p hcell
    have hfirst : first q = first p := congrArg Prod.fst hchoice
    have hsecond : second q = second p := congrArg Prod.snd hchoice
    exact ⟨hcarrier, by simpa [hfirst, hsecond] using hp.2⟩
  have hmultiplicity : ∀ p ∈ Z.union,
      Z.pointMultiplicity p ≤ 4 * selected.pointMultiplicity p := by
    intro p hp
    have h1 := hgood_count p hp
    have h2 : paperGoodThirdCount Z p (first p) (second p) tau ≤
        selected.pointMultiplicity p := by
      simp [selected, Kakeya.Streamlined.Shading.pointMultiplicity,
        paperGoodThirdCount]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by norm_num))
  have hmass : (1 / 4 : ENNReal) * Z.mass ≤ selected.mass :=
    paper_mass_lower_from_pointMultiplicity hmultiplicity
  let planeMap : PaperWZ1WeakPlaneMapData selected (tau / kappa) :=
    { planeMap := selection.normal
      measurable := selection.normal_measurable
      unit := by
        intro p hp
        have hpZ : p ∈ Z.union := by
          rcases hp with ⟨k, hk⟩
          exact ⟨k, hk.1⟩
        let cross := wz1Cross (F.tube (first p)).direction
          (F.tube (second p)).direction
        have hpos : 0 < ‖cross‖ := hkappa.trans_le (htransverse p hpZ)
        change ‖(‖cross‖)⁻¹ • cross‖ = 1
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
        field_simp [hpos.ne']
      incidence := by
        intro i p hp
        have hpZ : p ∈ Z.union := ⟨i, hp.1⟩
        let u := (F.tube (first p)).direction
        let v := (F.tube (second p)).direction
        let w := (F.tube i).direction
        let cross := wz1Cross u v
        have hcross : kappa ≤ ‖cross‖ := htransverse p hpZ
        have hcross_pos : 0 < ‖cross‖ := hkappa.trans_le hcross
        have htriple : |wz1TripleProduct u v w| ≤ tau := le_of_lt hp.2
        have hinner : inner ℝ w cross = wz1TripleProduct u v w :=
          inner_cross_triple u v w
        change |inner ℝ w ((‖cross‖)⁻¹ • cross)| ≤ tau / kappa
        rw [inner_smul_right, hinner, abs_mul, abs_inv, abs_of_pos hcross_pos]
        calc
          ‖cross‖⁻¹ * |wz1TripleProduct u v w| =
              |wz1TripleProduct u v w| / ‖cross‖ := by
            rw [div_eq_mul_inv, mul_comm]
          _ ≤ tau / kappa :=
            (div_le_div_of_nonneg_left (abs_nonneg _) hkappa hcross).trans
              (div_le_div_of_nonneg_right htriple hkappa.le) }
  have hplane_cell : ∀ p q,
      wz1PaperGridIndex delta p = wz1PaperGridIndex delta q →
        planeMap.planeMap p = planeMap.planeMap q := by
    intro p q hcell
    have hchoice := hchosen_const p q hcell
    have hfirst : first p = first q := congrArg Prod.fst hchoice
    have hsecond : second p = second q := congrArg Prod.snd hchoice
    simp [planeMap, PaperWZ1NarrowDirectionSelection.normal, selection,
      hfirst, hsecond]
  exact ⟨selected, selection, planeMap, hselected_sub, hselected_cubical,
    hplane_cell, (fun p q hcell =>
      ⟨congrArg Prod.fst (hchosen_const p q hcell),
        congrArg Prod.snd (hchosen_const p q hcell)⟩),
    fun _ => rfl, hmultiplicity, hmass⟩

end Kakeya.Assouad

end
