import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellwiseFiniteLabelMassRefinement

/-!
# Cellwise finite labels attached to tube indices

Unlike a common spatial restriction, this refinement may keep different tube
indices at the same point.  In each active spatial cell it chooses one finite
tube label carrying maximal total shaded mass and deletes all other labels.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- Pointwise multiplicity domination implies the corresponding paper mass
domination for an arbitrary natural coefficient. -/
lemma paper_mass_le_from_pointMultiplicity_coefficient
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {source selected : WZ1PaperTubeShading F}
    (coefficient : ℕ)
    (hmultiplicity : ∀ point,
      source.pointMultiplicity point ≤
        coefficient * selected.pointMultiplicity point) :
    source.mass ≤ (coefficient : ENNReal) * selected.mass := by
  have hpoint : ∀ point : Point3,
      (source.pointMultiplicity point : ENNReal) ≤
        (coefficient : ENNReal) *
          (selected.pointMultiplicity point : ENNReal) := by
    intro point
    exact_mod_cast hmultiplicity point
  have hmono : (∫⁻ point,
      (source.pointMultiplicity point : ENNReal)) ≤
      ∫⁻ point, (coefficient : ENNReal) *
        (selected.pointMultiplicity point : ENNReal) :=
    lintegral_mono hpoint
  have hselectedMeasurable : Measurable fun point : Point3 =>
      (selected.pointMultiplicity point : ENNReal) := by
    have heq : (fun point : Point3 =>
        (selected.pointMultiplicity point : ENNReal)) =
        fun point => ∑ index : Fin F.card,
          (selected.carrier index).indicator
            (fun _ => (1 : ENNReal)) point := by
      funext point
      exact coe_pointMultiplicity_eq_sum_indicator selected point
    rw [heq]
    exact Finset.measurable_sum _ fun index _ =>
      measurable_const.indicator (selected.measurable_carrier index)
  rw [lintegral_pointMultiplicity source,
    lintegral_const_mul _ hselectedMeasurable,
    lintegral_pointMultiplicity selected] at hmono
  exact hmono

/-- Restrict each tube carrier to points where the tube has the label chosen
for the point's spatial cell. -/
def paperCellwiseTubeLabelRestriction
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Cell Label : Type*}
    [MeasurableSpace Cell] [Countable Label]
    [MeasurableSpace Label] [MeasurableSingletonClass Label]
    (S : WZ1PaperTubeShading F)
    (cell : Point3 → Cell) (hcell : Measurable cell)
    (belongs : Point3 → Fin F.card → Label → Prop)
    (hbelongs : ∀ index label,
      MeasurableSet {point | belongs point index label})
    (chosen : Cell → Label) (hchosen : Measurable chosen) :
    WZ1PaperTubeShading F :=
  { carrier := fun index =>
      S.carrier index ∩
        {point | belongs point index (chosen (cell point))}
    measurable_carrier := fun index => by
      have heq : {point | belongs point index (chosen (cell point))} =
          ⋃ label, {point | chosen (cell point) = label} ∩
            {point | belongs point index label} := by
        ext point
        simp
      rw [heq]
      exact (S.measurable_carrier index).inter <|
        MeasurableSet.iUnion fun label =>
          ((hchosen.comp hcell) (measurableSet_singleton label)).inter
            (hbelongs index label)
    subset_body := fun index =>
      Set.inter_subset_left.trans (S.subset_body index) }

lemma paperCellwiseTubeLabelRestriction_subshading
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Cell Label : Type*}
    [MeasurableSpace Cell] [Countable Label]
    [MeasurableSpace Label] [MeasurableSingletonClass Label]
    (S : WZ1PaperTubeShading F)
    (cell : Point3 → Cell) (hcell : Measurable cell)
    (belongs : Point3 → Fin F.card → Label → Prop)
    (hbelongs : ∀ index label,
      MeasurableSet {point | belongs point index label})
    (chosen : Cell → Label) (hchosen : Measurable chosen) :
    PaperIsSubshading
      (paperCellwiseTubeLabelRestriction S cell hcell belongs hbelongs
        chosen hchosen) S :=
  fun _ => Set.inter_subset_left

lemma paperCellwiseTubeLabelRestriction_belongs
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Cell Label : Type*}
    [MeasurableSpace Cell] [Countable Label]
    [MeasurableSpace Label] [MeasurableSingletonClass Label]
    (S : WZ1PaperTubeShading F)
    (cell : Point3 → Cell) (hcell : Measurable cell)
    (belongs : Point3 → Fin F.card → Label → Prop)
    (hbelongs : ∀ index label,
      MeasurableSet {point | belongs point index label})
    (chosen : Cell → Label) (hchosen : Measurable chosen) :
    ∀ index point, point ∈ (paperCellwiseTubeLabelRestriction
      S cell hcell belongs hbelongs chosen hchosen).carrier index →
      belongs point index (chosen (cell point)) := by
  intro index point hpoint
  exact hpoint.2

/-- Finite tube-label pigeonholing in every active cell. -/
theorem paper_cellwise_tube_label_mass_refinement
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Cell Label : Type*}
    [Countable Cell] [DecidableEq Cell]
    [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    [Fintype Label] [Nonempty Label] [DecidableEq Label]
    [MeasurableSpace Label] [MeasurableSingletonClass Label]
    (S : WZ1PaperTubeShading F)
    (hScubical : WZ1PaperIsCubicalShading S)
    (cell : Point3 → Cell) (hcell : Measurable cell)
    (activeCells : Finset Cell)
    (hsupport : ∀ point ∈ S.union, cell point ∈ activeCells)
    (belongs : Point3 → Fin F.card → Label → Prop)
    (hbelongsMeasurable : ∀ index label,
      MeasurableSet {point | belongs point index label})
    (hbelongsCover : ∀ index point, point ∈ S.carrier index →
      ∃ label, belongs point index label)
    (hcellConst : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      cell first = cell second)
    (hbelongsConst : ∀ index label first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      (belongs first index label ↔ belongs second index label))
    (hmeasurableChosen : ∀ chosen : Cell → Label, Measurable chosen) :
    ∃ (chosen : Cell → Label) (selected : WZ1PaperTubeShading F),
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ index point, point ∈ selected.carrier index →
        belongs point index (chosen (cell point))) ∧
      S.mass ≤ (Fintype.card Label : ENNReal) * selected.mass := by
  classical
  let cellSet (currentCell : Cell) : Set Point3 :=
    {point | cell point = currentCell}
  have hcellSetMeasurable : ∀ currentCell,
      MeasurableSet (cellSet currentCell) := fun currentCell =>
    hcell (measurableSet_singleton currentCell)
  let piece (currentCell : Cell) (label : Label)
      (index : Fin F.card) : Set Point3 :=
    S.carrier index ∩ cellSet currentCell ∩
      {point | belongs point index label}
  have hpieceMeasurable : ∀ currentCell label index,
      MeasurableSet (piece currentCell label index) := by
    intro currentCell label index
    exact ((S.measurable_carrier index).inter
      (hcellSetMeasurable currentCell)).inter
        (hbelongsMeasurable index label)
  let labelMass (currentCell : Cell) (label : Label) : ENNReal :=
    ∑ index : Fin F.card, volume (piece currentCell label index)
  let cellMass (currentCell : Cell) : ENNReal :=
    ∑ index : Fin F.card,
      volume (S.carrier index ∩ cellSet currentCell)
  have hcellCover : ∀ currentCell, cellMass currentCell ≤
      ∑ label : Label, labelMass currentCell label := by
    intro currentCell
    dsimp only [cellMass, labelMass]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro index _
    have hcover : S.carrier index ∩ cellSet currentCell ⊆
        ⋃ label : Label, piece currentCell label index := by
      intro point hpoint
      rcases hbelongsCover index point hpoint.1 with ⟨label, hlabel⟩
      exact Set.mem_iUnion.mpr ⟨label, ⟨hpoint.1, hpoint.2⟩, hlabel⟩
    calc
      volume (S.carrier index ∩ cellSet currentCell) ≤
          volume (⋃ label : Label, piece currentCell label index) :=
        measure_mono hcover
      _ ≤ ∑' label : Label, volume (piece currentCell label index) :=
        measure_iUnion_le _
      _ = ∑ label : Label, volume (piece currentCell label index) := by
        simp
  have hchoice : ∀ currentCell, ∃ label : Label,
      cellMass currentCell ≤
        (Fintype.card Label : ENNReal) * labelMass currentCell label := by
    intro currentCell
    rcases finset_ennreal_pigeonhole
        (s := (Finset.univ : Finset Label)) Finset.univ_nonempty
        (labelMass currentCell) with ⟨label, _, hlabel⟩
    exact ⟨label, (hcellCover currentCell).trans hlabel⟩
  choose chosen hchosen using hchoice
  let hchosenMeasurable : Measurable chosen :=
    hmeasurableChosen chosen
  let selected := paperCellwiseTubeLabelRestriction
    S cell hcell belongs hbelongsMeasurable chosen hchosenMeasurable
  have hsub : PaperIsSubshading selected S :=
    paperCellwiseTubeLabelRestriction_subshading
      S cell hcell belongs hbelongsMeasurable chosen hchosenMeasurable
  have hcubical : WZ1PaperIsCubicalShading selected := by
    intro index point hpoint other hother
    have hgrid : wz1PaperGridIndex delta other =
        wz1PaperGridIndex delta point :=
      (mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) other).mp hother
    have hotherS : other ∈ S.carrier index :=
      hScubical index point hpoint.1 hother
    have hcellEq : cell other = cell point :=
      hcellConst other point hgrid
    have hbelongsEq := hbelongsConst index (chosen (cell point))
      point other hgrid.symm
    exact ⟨hotherS, by
      change belongs other index (chosen (cell other))
      rw [hcellEq]
      exact hbelongsEq.mp hpoint.2⟩
  have hcellPartition : S.mass =
      ∑ currentCell ∈ activeCells, cellMass currentCell := by
    calc
      S.mass = ∑ index : Fin F.card, volume (S.carrier index) := rfl
      _ = ∑ index : Fin F.card, ∑ currentCell ∈ activeCells,
          volume (S.carrier index ∩ cellSet currentCell) := by
        apply Finset.sum_congr rfl
        intro index _
        let indexedPiece : Cell → Set Point3 := fun currentCell =>
          S.carrier index ∩ cellSet currentCell
        have hcover : S.carrier index =
            ⋃ currentCell ∈ activeCells, indexedPiece currentCell := by
          ext point
          constructor
          · intro hpoint
            have hactive := hsupport point ⟨index, hpoint⟩
            exact Set.mem_iUnion.mpr ⟨cell point,
              Set.mem_iUnion.mpr ⟨hactive, hpoint, rfl⟩⟩
          · intro hpoint
            rcases Set.mem_iUnion.mp hpoint with ⟨currentCell, hpoint⟩
            rcases Set.mem_iUnion.mp hpoint with ⟨_, hpoint⟩
            exact hpoint.1
        have hdisjoint : Set.PairwiseDisjoint activeCells indexedPiece := by
          intro first _ second _ hne
          change Disjoint (indexedPiece first) (indexedPiece second)
          rw [Set.disjoint_left]
          intro point hfirst hsecond
          exact hne (hfirst.2.symm.trans hsecond.2)
        have hmeasurable : ∀ currentCell ∈ activeCells,
            MeasurableSet (indexedPiece currentCell) := by
          intro currentCell _
          exact (S.measurable_carrier index).inter
            (hcellSetMeasurable currentCell)
        calc
          volume (S.carrier index) =
              volume (⋃ currentCell ∈ activeCells,
                indexedPiece currentCell) := by rw [← hcover]
          _ = ∑ currentCell ∈ activeCells,
              volume (indexedPiece currentCell) :=
            measure_biUnion_finset hdisjoint hmeasurable
          _ = ∑ currentCell ∈ activeCells,
              volume (S.carrier index ∩ cellSet currentCell) := rfl
      _ = ∑ currentCell ∈ activeCells, ∑ index : Fin F.card,
          volume (S.carrier index ∩ cellSet currentCell) := by
        rw [Finset.sum_comm]
      _ = ∑ currentCell ∈ activeCells, cellMass currentCell := rfl
  have hselectedMass : selected.mass =
      ∑ currentCell ∈ activeCells,
        labelMass currentCell (chosen currentCell) := by
    calc
      selected.mass = ∑ index : Fin F.card,
          volume (selected.carrier index) := rfl
      _ = ∑ index : Fin F.card, ∑ currentCell ∈ activeCells,
          volume (piece currentCell (chosen currentCell) index) := by
        apply Finset.sum_congr rfl
        intro index _
        let indexedPiece : Cell → Set Point3 := fun currentCell =>
          piece currentCell (chosen currentCell) index
        have hcover : selected.carrier index =
            ⋃ currentCell ∈ activeCells, indexedPiece currentCell := by
          ext point
          constructor
          · intro hpoint
            have hactive := hsupport point ⟨index, hpoint.1⟩
            exact Set.mem_iUnion.mpr ⟨cell point,
              Set.mem_iUnion.mpr
                ⟨hactive, ⟨hpoint.1, rfl⟩, hpoint.2⟩⟩
          · intro hpoint
            rcases Set.mem_iUnion.mp hpoint with ⟨currentCell, hpoint⟩
            rcases Set.mem_iUnion.mp hpoint with ⟨_, hpoint⟩
            have hcellPoint : cell point = currentCell := hpoint.1.2
            exact ⟨hpoint.1.1, by simpa [hcellPoint] using hpoint.2⟩
        have hdisjoint : Set.PairwiseDisjoint activeCells indexedPiece := by
          intro first _ second _ hne
          change Disjoint (indexedPiece first) (indexedPiece second)
          rw [Set.disjoint_left]
          intro point hfirst hsecond
          exact hne (hfirst.1.2.symm.trans hsecond.1.2)
        have hmeasurable : ∀ currentCell ∈ activeCells,
            MeasurableSet (indexedPiece currentCell) := by
          intro currentCell _
          exact hpieceMeasurable currentCell (chosen currentCell) index
        calc
          volume (selected.carrier index) =
              volume (⋃ currentCell ∈ activeCells,
                indexedPiece currentCell) := by rw [← hcover]
          _ = ∑ currentCell ∈ activeCells,
              volume (indexedPiece currentCell) :=
            measure_biUnion_finset hdisjoint hmeasurable
          _ = ∑ currentCell ∈ activeCells,
              volume (piece currentCell (chosen currentCell) index) := rfl
      _ = ∑ currentCell ∈ activeCells, ∑ index : Fin F.card,
          volume (piece currentCell (chosen currentCell) index) := by
        rw [Finset.sum_comm]
      _ = ∑ currentCell ∈ activeCells,
          labelMass currentCell (chosen currentCell) := rfl
  refine ⟨chosen, selected, hsub, hcubical, ?_, ?_⟩
  · exact paperCellwiseTubeLabelRestriction_belongs
      S cell hcell belongs hbelongsMeasurable chosen hchosenMeasurable
  · rw [hcellPartition, hselectedMass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro currentCell _
    exact hchosen currentCell

/-- Lower-left corner of a fine paper grid cell. -/
def tubeLabelCellCorner
    (delta : ℝ) (cell : ℤ × ℤ × ℤ) : Point3 :=
  WithLp.toLp 2 fun coordinate : Fin 3 =>
    delta * match coordinate with
      | 0 => cell.1
      | 1 => cell.2.1
      | 2 => cell.2.2

lemma tubeLabelCellCorner_mem_cube
    {delta : ℝ} (hdelta : 0 < delta) (cell : ℤ × ℤ × ℤ) :
    tubeLabelCellCorner delta cell ∈ wz1PaperGridCube delta cell := by
  rw [mem_wz1PaperGridCube]
  simp only [tubeLabelCellCorner, wz1PaperGridIndex, gridIndex]
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

/-- On a cubical shading, choose in every fine cell a tube label with maximal
active cardinality.  The selected multiplicity loses at most the number of
labels pointwise, not merely after integration. -/
theorem paper_fine_cell_tube_label_multiplicity_refinement
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Label : Type*}
    [Fintype Label] [Nonempty Label] [DecidableEq Label]
    [MeasurableSpace Label] [MeasurableSingletonClass Label]
    (S : WZ1PaperTubeShading F)
    (hScubical : WZ1PaperIsCubicalShading S)
    (hdelta : 0 < delta)
    (belongs : Point3 → Fin F.card → Label → Prop)
    (hbelongsMeasurable : ∀ index label,
      MeasurableSet {point | belongs point index label})
    (hbelongsCover : ∀ index point, point ∈ S.carrier index →
      ∃ label, belongs point index label)
    (hbelongsConst : ∀ index label first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      (belongs first index label ↔ belongs second index label)) :
    ∃ (chosen : (ℤ × ℤ × ℤ) → Label)
      (selected : WZ1PaperTubeShading F),
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ index point, point ∈ selected.carrier index →
        belongs point index (chosen (wz1PaperGridIndex delta point))) ∧
      (∀ point ∈ S.union,
        S.pointMultiplicity point ≤
          Fintype.card Label * selected.pointMultiplicity point) ∧
      S.mass ≤ (Fintype.card Label : ENNReal) * selected.mass := by
  classical
  let Cell := ℤ × ℤ × ℤ
  let atLabel (cell : Cell) (label : Label) : Finset (Fin F.card) :=
    Finset.univ.filter fun index =>
      tubeLabelCellCorner delta cell ∈ S.carrier index ∧
        belongs (tubeLabelCellCorner delta cell) index label
  have hchoice : ∀ cell : Cell, ∃ label : Label,
      ∑ candidate : Label, ((atLabel cell candidate).card : ENNReal) ≤
        (Fintype.card Label : ENNReal) *
          ((atLabel cell label).card : ENNReal) := by
    intro cell
    rcases finset_ennreal_pigeonhole
        (s := (Finset.univ : Finset Label)) Finset.univ_nonempty
        (fun label => ((atLabel cell label).card : ENNReal)) with
      ⟨label, _, hlabel⟩
    simpa using ⟨label, hlabel⟩
  choose chosen hchosen using hchoice
  have hchosenMeasurable : Measurable chosen := Measurable.of_discrete
  have hgridMeasurable : Measurable (wz1PaperGridIndex delta) := by
    have h : Measurable (fun point : Point3 =>
        (⌊point 0 / delta⌋, ⌊point 1 / delta⌋,
          ⌊point 2 / delta⌋)) := by fun_prop
    convert h using 1
    funext point
    simp [wz1PaperGridIndex, gridIndex]
  let selected := paperCellwiseTubeLabelRestriction
    S (wz1PaperGridIndex delta) hgridMeasurable
      belongs hbelongsMeasurable chosen hchosenMeasurable
  have hsub : PaperIsSubshading selected S :=
    paperCellwiseTubeLabelRestriction_subshading
      S (wz1PaperGridIndex delta) hgridMeasurable
        belongs hbelongsMeasurable chosen hchosenMeasurable
  have hcubical : WZ1PaperIsCubicalShading selected := by
    intro index point hpoint other hother
    have hgrid : wz1PaperGridIndex delta other =
        wz1PaperGridIndex delta point :=
      (mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) other).mp hother
    have hotherS : other ∈ S.carrier index :=
      hScubical index point hpoint.1 hother
    exact ⟨hotherS, by
      change belongs other index (chosen (wz1PaperGridIndex delta other))
      rw [hgrid]
      exact (hbelongsConst index (chosen (wz1PaperGridIndex delta point))
        point other hgrid.symm).mp hpoint.2⟩
  have hpointwise : ∀ point ∈ S.union,
      S.pointMultiplicity point ≤
        Fintype.card Label * selected.pointMultiplicity point := by
    intro point hpoint
    let cell := wz1PaperGridIndex delta point
    let corner := tubeLabelCellCorner delta cell
    have hcornerCube : corner ∈ wz1PaperGridCube delta cell :=
      tubeLabelCellCorner_mem_cube hdelta cell
    have hsame : wz1PaperGridIndex delta corner =
        wz1PaperGridIndex delta point :=
      (mem_wz1PaperGridCube delta cell corner).mp hcornerCube
    let active : Finset (Fin F.card) :=
      Finset.univ.filter fun index => point ∈ S.carrier index
    have hactiveCard : active.card = S.pointMultiplicity point := rfl
    have hactiveCover : active ⊆
        Finset.univ.biUnion fun label => atLabel cell label := by
      intro index hindex
      have hindexPoint : point ∈ S.carrier index :=
        (Finset.mem_filter.mp hindex).2
      rcases hbelongsCover index point hindexPoint with ⟨label, hlabel⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨label, Finset.mem_univ _, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact (hScubical.carrier_mem_iff_of_same_cell index hsame).mpr
          hindexPoint
      · exact (hbelongsConst index label point corner hsame.symm).mp hlabel
    have hcoverCard : active.card ≤
        ∑ label : Label, (atLabel cell label).card := by
      calc
        active.card ≤
            (Finset.univ.biUnion fun label => atLabel cell label).card :=
          Finset.card_le_card hactiveCover
        _ ≤ ∑ label ∈ (Finset.univ : Finset Label),
            (atLabel cell label).card := Finset.card_biUnion_le
        _ = ∑ label : Label, (atLabel cell label).card := by simp
    have hchosenNat : ∑ label : Label, (atLabel cell label).card ≤
        Fintype.card Label * (atLabel cell (chosen cell)).card := by
      exact_mod_cast hchosen cell
    have hselectedCard : (atLabel cell (chosen cell)).card =
        selected.pointMultiplicity point := by
      change (atLabel cell (chosen cell)).card =
        (Finset.univ.filter fun index : Fin F.card =>
          point ∈ selected.carrier index).card
      congr 1
      ext index
      simp only [atLabel, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hcornerCarrier, hcornerBelongs⟩
        have hpointCarrier :=
          (hScubical.carrier_mem_iff_of_same_cell index hsame).mp
            hcornerCarrier
        have hpointBelongs :=
          (hbelongsConst index (chosen cell) corner point hsame).mp
            hcornerBelongs
        exact ⟨hpointCarrier, by simpa [cell] using hpointBelongs⟩
      · intro hselected
        rcases hselected with ⟨hpointCarrier, hpointBelongs⟩
        have hcornerCarrier :=
          (hScubical.carrier_mem_iff_of_same_cell index hsame).mpr
            hpointCarrier
        have hcornerBelongs :=
          (hbelongsConst index (chosen cell) point corner hsame.symm).mp <| by
            simpa [selected, cell] using hpointBelongs
        exact ⟨hcornerCarrier, hcornerBelongs⟩
    rw [← hactiveCard, ← hselectedCard]
    exact hcoverCard.trans hchosenNat
  have hpointwiseAll : ∀ point, S.pointMultiplicity point ≤
      Fintype.card Label * selected.pointMultiplicity point := by
    intro point
    by_cases hpoint : point ∈ S.union
    · exact hpointwise point hpoint
    · have hzero : S.pointMultiplicity point = 0 := by
        simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
        apply Finset.card_eq_zero.mpr
        simp
        exact fun index hindex => hpoint ⟨index, hindex⟩
      rw [hzero]
      exact Nat.zero_le _
  have hmass := paper_mass_le_from_pointMultiplicity_coefficient
    (Fintype.card Label) hpointwiseAll
  refine ⟨chosen, selected, hsub, hcubical, ?_, hpointwise, ?_⟩
  · exact paperCellwiseTubeLabelRestriction_belongs
      S (wz1PaperGridIndex delta) hgridMeasurable belongs
        hbelongsMeasurable chosen hchosenMeasurable
  · exact hmass

end Kakeya.Assouad.PureWZ2

end
