import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.StableVerticalNormal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureCarrierDirectionAlignment
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureSharedParentDirection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.AmplifiedLabelMassRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.NearbyCellResidueRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalBallCellRefinement
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers

/-!
# Dense-cluster variation through a pure Definition 2.12 cover

For a dense direction cluster, select one pure parent in every spatial cell,
weighted by its strict full-fiber cardinality.  The total weight is the fine
family cardinality, so a pointwise density floor cancels it.  Ordinary strict
carrier containment gives direction variation without a Section 6 line cover.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- The active indices assigned to one pure parent form a subset of its
strict full fiber. -/
private lemma active_parent_card_le_fullFiber
    {delta parentRadius : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily parentRadius}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (hparentRadius : 0 < parentRadius)
    (S : WZ1PaperTubeShading fine) (point : Point3)
    (parent : Fin coarse.card) :
    (((Finset.univ.filter fun index : Fin fine.card =>
      cover.parent index = parent ∧ point ∈ S.carrier index).card : ℕ) :
        ENNReal) ≤
      ((wz2PaperOrdinaryFullFiberIndices fine coarse parent).card :
        ENNReal) := by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro index hindex
  have hparent : cover.parent index = parent :=
    (Finset.mem_filter.mp hindex).2.1
  exact (cover.mem_fullFiber_iff_parent_eq
    hparentRadius.le parent index).mpr hparent

/-- A three-link chain bounds the distance between its endpoints. -/
private lemma norm_sub_le_chain_three
    (first second third fourth : Point3)
    {firstBound secondBound thirdBound : ℝ}
    (hfirst : ‖first - second‖ ≤ firstBound)
    (hsecond : ‖second - third‖ ≤ secondBound)
    (hthird : ‖third - fourth‖ ≤ thirdBound) :
    ‖first - fourth‖ ≤ firstBound + secondBound + thirdBound := by
  have hdecomp : first - fourth =
      (first - second) + (second - third) + (third - fourth) := by
    abel
  rw [hdecomp]
  calc
    ‖(first - second) + (second - third) + (third - fourth)‖ ≤
        ‖(first - second) + (second - third)‖ +
          ‖third - fourth‖ := norm_add_le _ _
    _ ≤ (‖first - second‖ + ‖second - third‖) +
          ‖third - fourth‖ := by
      exact add_le_add
        (norm_add_le (first - second) (second - third))
        (le_refl ‖third - fourth‖)
    _ ≤ (firstBound + secondBound) + thirdBound := by
      exact add_le_add (add_le_add hfirst hsecond) hthird

/-- Two fine witnesses with the same pure strict-carrier parent have stable
vertical normals within the explicit cluster and carrier error budget. -/
private lemma stable_normals_close_of_pure_shared_parent
    {delta parentRadius kappa : ℝ}
    {centerFirst centerSecond witnessFirst witnessSecond :
      Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube parentRadius}
    (hdelta : 0 ≤ delta)
    (hparentRadius : 0 < parentRadius)
    (hparentRadiusSmall : parentRadius < 1 / 8)
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (hcenterFirstLine : WZ1PaperTubeInLineClass centerFirst)
    (hcenterSecondLine : WZ1PaperTubeInLineClass centerSecond)
    (hwitnessFirstLine : WZ1PaperTubeInLineClass witnessFirst)
    (hwitnessSecondLine : WZ1PaperTubeInLineClass witnessSecond)
    (hclusterFirst : ‖wz1Cross centerFirst.direction witnessFirst.direction‖ ≤
      kappa)
    (hclusterSecond : ‖wz1Cross centerSecond.direction witnessSecond.direction‖ ≤
      kappa)
    (hcontainedFirst : witnessFirst.carrier ⊆ parent.carrier)
    (hcontainedSecond : witnessSecond.carrier ⊆ parent.carrier) :
    ‖stableVerticalNormal (wz1PaperDirection centerFirst) -
      stableVerticalNormal (wz1PaperDirection centerSecond)‖ ≤
        8 * kappa + 16 * parentRadius := by
  have hfirstCenter :
      ‖wz1PaperDirection centerFirst - wz1PaperDirection witnessFirst‖ ≤
        2 * kappa := by
    apply paper_direction_sub_norm_le_of_cross_le
      hcenterFirstLine hwitnessFirstLine hkappaNonnegative hkappaHalf
    rw [← raw_cross_norm_eq_paper_cross_norm]
    exact hclusterFirst
  have hsecondCenter :
      ‖wz1PaperDirection centerSecond - wz1PaperDirection witnessSecond‖ ≤
        2 * kappa := by
    apply paper_direction_sub_norm_le_of_cross_le
      hcenterSecondLine hwitnessSecondLine hkappaNonnegative hkappaHalf
    rw [← raw_cross_norm_eq_paper_cross_norm]
    exact hclusterSecond
  have hwitnessClose :
      ‖wz1PaperDirection witnessFirst - wz1PaperDirection witnessSecond‖ ≤
        8 * parentRadius :=
    paper_directions_close_of_shared_carrier_parent
      hdelta hparentRadius hparentRadiusSmall
      hwitnessFirstLine hwitnessSecondLine hcontainedFirst hcontainedSecond
  have hcenterClose :
      ‖wz1PaperDirection centerFirst - wz1PaperDirection centerSecond‖ ≤
        4 * kappa + 8 * parentRadius := by
    have hchain := norm_sub_le_chain_three
      (wz1PaperDirection centerFirst)
      (wz1PaperDirection witnessFirst)
      (wz1PaperDirection witnessSecond)
      (wz1PaperDirection centerSecond)
      hfirstCenter hwitnessClose (by
        simpa [norm_sub_rev] using hsecondCenter)
    linarith
  calc
    ‖stableVerticalNormal (wz1PaperDirection centerFirst) -
        stableVerticalNormal (wz1PaperDirection centerSecond)‖ ≤
        2 * ‖wz1PaperDirection centerFirst -
          wz1PaperDirection centerSecond‖ :=
      stableVerticalNormal_sub_norm_le
        (paper_direction_cross_axis_lower hcenterFirstLine)
        (paper_direction_cross_axis_lower hcenterSecondLine)
    _ ≤ 2 * (4 * kappa + 8 * parentRadius) := by gcongr
    _ = 8 * kappa + 16 * parentRadius := by ring

/-- One-scale dense-cluster variation through a literal pure cover, with the
spatial comparison scale kept separate from the normal-variation budget. -/
theorem paper_pure_dense_parent_nearby_asymmetric_variation
    {delta parentRadius spatialScale variationScale kappa : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily parentRadius}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    {S : WZ1PaperTubeShading fine}
    (hfineNonempty : fine.Nonempty)
    (hline : WZ1PaperIsLineClass fine)
    (hSCubical : WZ1PaperIsCubicalShading S)
    (center : Point3 → Fin fine.card)
    (hcenterMeasurable : Measurable center)
    (hcenterCell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      center first = center second)
    (hcluster : ∀ index point, point ∈ S.carrier index →
      ‖wz1Cross (fine.tube (center point)).direction
        (fine.tube index).direction‖ ≤ kappa)
    (multiplicityCoefficient densityPower : ENNReal)
    (hdensityPoint : ∀ point ∈ S.union,
      densityPower * fine.enncard ≤
        multiplicityCoefficient *
          (S.pointMultiplicity point : ENNReal))
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (hparentRadius : 0 < parentRadius)
    (hparentRadiusSmall : parentRadius < 1 / 8)
    (hspatialScale : 0 < spatialScale)
    (hvariationScale : 0 < variationScale)
    (K : ℕ) (hK : 0 < K)
    (hspatialScaleAligned : spatialScale = (K : ℝ) * delta) :
    ∃ (planeMap : PaperWZ1WeakPlaneMapData S kappa)
      (selected : WZ1PaperTubeShading fine),
      (∀ point, planeMap.planeMap point =
        stableVerticalNormal
          (wz1PaperDirection (fine.tube (center point)))) ∧
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ point ∈ selected.union, ∀ other ∈ selected.union,
        dist point other ≤ spatialScale →
          dist (planeMap.planeMap point)
            (planeMap.planeMap other) ≤ variationScale) ∧
      (∀ point ∈ selected.union,
        selected.pointMultiplicity point = S.pointMultiplicity point) ∧
      densityPower * S.mass ≤
        (localPlaneMapCapCount
          (8 * kappa + 16 * parentRadius) variationScale : ENNReal) *
          27 * multiplicityCoefficient * selected.mass := by
  classical
  let planeMap : PaperWZ1WeakPlaneMapData S kappa :=
    { planeMap := fun point =>
        stableVerticalNormal
          (wz1PaperDirection (fine.tube (center point)))
      measurable := by
        have hfinite : Measurable fun index : Fin fine.card =>
            stableVerticalNormal
              (wz1PaperDirection (fine.tube index)) :=
          measurable_of_finite _
        exact hfinite.comp hcenterMeasurable
      unit := by
        intro point _
        apply stableVerticalNormal_unit
        exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
          (paper_direction_cross_axis_lower (hline (center point)))
      incidence := by
        intro index point hpoint
        have hcenterCross : 0 < ‖wz1Cross
            (wz1PaperDirection (fine.tube (center point)))
            verticalNormalAxis‖ :=
          (by norm_num : (0 : ℝ) < 1 / 2).trans_le
            (paper_direction_cross_axis_lower (hline (center point)))
        have hpaperCross : ‖wz1Cross
            (wz1PaperDirection (fine.tube (center point)))
            (wz1PaperDirection (fine.tube index))‖ ≤ kappa := by
          rw [← raw_cross_norm_eq_paper_cross_norm]
          exact hcluster index point hpoint
        rw [abs_inner_raw_eq_paperDirection]
        exact (stableVerticalNormal_incidence
          (wz1PaperDirection (fine.tube (center point)))
          (wz1PaperDirection (fine.tube index))
          (wz1PaperDirection_norm _) (wz1PaperDirection_norm _)
          hcenterCross).trans hpaperCross }
  have hcoarseNonempty : coarse.Nonempty := by
    let source : Fin fine.card := ⟨0, hfineNonempty⟩
    exact (Nat.zero_le (cover.parent source).1).trans_lt
      (cover.parent source).isLt
  let Cell := ℤ × ℤ × ℤ
  let Label := Fin coarse.card
  let cell : Point3 → Cell := wz1PaperGridIndex spatialScale
  have hcellMeasurable : Measurable cell := by
    have h : Measurable (fun point : Point3 =>
        (⌊point 0 / spatialScale⌋, ⌊point 1 / spatialScale⌋,
          ⌊point 2 / spatialScale⌋)) := by fun_prop
    convert h using 1
    funext point
    simp [cell, wz1PaperGridIndex, gridIndex]
  let activeCells : Finset Cell :=
    wz1PaperGridIndicesInWindow spatialScale hspatialScale
  let allowed : Cell → Finset Label := fun _ => Finset.univ
  have hsupport : ∀ point ∈ S.union, cell point ∈ activeCells := by
    intro point hpoint
    rcases hpoint with ⟨index, hindex⟩
    exact paper_point_gridIndex_in_window hspatialScale
      (S.subset_body index hindex).2
  let defaultParent : Label := ⟨0, hcoarseNonempty⟩
  letI : Nonempty Label := ⟨defaultParent⟩
  have hallowedNonempty : ∀ currentCell ∈ activeCells,
      (allowed currentCell).Nonempty := by
    intro _ _
    exact ⟨defaultParent, Finset.mem_univ _⟩
  let good (point : Point3) (parent : Label) : Prop :=
    ∃ index : Fin fine.card, point ∈ S.carrier index ∧
      cover.parent index = parent
  have hgoodMeasurable : ∀ parent : Label,
      MeasurableSet {point | good point parent} := by
    intro parent
    have heq : {point | good point parent} =
        ⋃ index : Fin fine.card,
          if cover.parent index = parent then S.carrier index else ∅ := by
      ext point
      simp [good]
      tauto
    rw [heq]
    apply MeasurableSet.iUnion
    intro index
    by_cases hparent : cover.parent index = parent
    · simp [hparent, S.measurable_carrier index]
    · simp [hparent]
  have hgoodAllowed : ∀ point ∈ S.union, ∀ parent : Label,
      good point parent → parent ∈ allowed (cell point) := by
    simp [allowed]
  let fiberCard : Label → ENNReal := fun parent =>
    ((wz2PaperOrdinaryFullFiberIndices fine coarse parent).card : ENNReal)
  let labelWeight : Cell → Label → ENNReal := fun _ parent => fiberCard parent
  let goodCount : Point3 → Cell → ENNReal := fun point currentCell =>
    ∑ parent ∈ allowed currentCell,
      ({point | good point parent}.indicator
        (fun _ => labelWeight currentCell parent)) point
  have hgoodCount : ∀ point currentCell, goodCount point currentCell =
      ∑ parent ∈ allowed currentCell,
        ({point | good point parent}.indicator
          (fun _ => labelWeight currentCell parent)) point := by
    intro _ _
    rfl
  have hfiberEq : ∀ parent : Label,
      wz2PaperOrdinaryFullFiberIndices fine coarse parent =
        Finset.univ.filter fun source => cover.parent source = parent := by
    intro parent
    ext source
    simpa using
      (cover.mem_fullFiber_iff_parent_eq hparentRadius.le parent source)
  have hfiberPartitionNat :
      ∑ parent : Label,
          (wz2PaperOrdinaryFullFiberIndices fine coarse parent).card =
        fine.card := by
    have hmaps : Set.MapsTo cover.parent
        (↑(Finset.univ : Finset (Fin fine.card)) : Set (Fin fine.card))
        (↑(Finset.univ : Finset Label) : Set Label) := by
      intro source _
      exact Finset.mem_univ _
    have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
    simp_rw [hfiberEq]
    simpa using hpartition.symm
  have hfiberSum : (∑ parent : Label, fiberCard parent) = fine.enncard := by
    change (∑ parent : Label,
      ((wz2PaperOrdinaryFullFiberIndices fine coarse parent).card : ENNReal)) =
        (fine.card : ENNReal)
    rw [← Nat.cast_sum, hfiberPartitionNat]
  have hlabelBound : ∀ currentCell ∈ activeCells,
      (∑ parent ∈ allowed currentCell,
        labelWeight currentCell parent) ≤ fine.enncard := by
    intro currentCell _
    simp [allowed, labelWeight, hfiberSum]
  have hpointwise : ∀ point ∈ S.union,
      densityPower * fine.enncard ≤
        multiplicityCoefficient * goodCount point (cell point) := by
    intro point hpoint
    let activeInParent (parent : Label) : Finset (Fin fine.card) :=
      Finset.univ.filter fun index =>
        cover.parent index = parent ∧ point ∈ S.carrier index
    have hactivePartition : S.pointMultiplicity point =
        ∑ parent : Label, (activeInParent parent).card := by
      have hmaps : Set.MapsTo cover.parent
          (↑(Finset.univ.filter fun index : Fin fine.card =>
            point ∈ S.carrier index) : Set (Fin fine.card))
          (↑(Finset.univ : Finset Label) : Set Label) := by
        intro index _
        exact Finset.mem_univ _
      have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
      have hfiberActive : ∀ parent : Label,
          (Finset.univ.filter fun index : Fin fine.card =>
            point ∈ S.carrier index).filter
              (fun index => cover.parent index = parent) =
            activeInParent parent := by
        intro parent
        ext index
        simp [activeInParent, and_comm]
      simp_rw [hfiberActive] at hpartition
      exact hpartition
    have hparentCap : ∀ parent : Label,
        ((activeInParent parent).card : ENNReal) ≤ fiberCard parent := by
      intro parent
      exact active_parent_card_le_fullFiber
        cover hparentRadius S point parent
    have hsumCap : (S.pointMultiplicity point : ENNReal) ≤
        goodCount point (cell point) := by
      rw [hactivePartition, Nat.cast_sum]
      calc
        ∑ parent : Label, ((activeInParent parent).card : ENNReal) ≤
            ∑ parent : Label,
              ({point | good point parent}.indicator
                (fun _ => fiberCard parent)) point := by
          apply Finset.sum_le_sum
          intro parent _
          by_cases hgood : good point parent
          · simp [Set.indicator_apply, hgood]
            exact hparentCap parent
          · have hempty : activeInParent parent = ∅ := by
              apply Finset.eq_empty_iff_forall_notMem.mpr
              intro index hindex
              apply hgood
              exact ⟨index, (Finset.mem_filter.mp hindex).2.2,
                (Finset.mem_filter.mp hindex).2.1⟩
            simp [Set.indicator_apply, hgood, hempty]
        _ = goodCount point (cell point) := by
          simp [goodCount, allowed, labelWeight]
    exact (hdensityPoint point hpoint).trans <| by gcongr
  rcases paper_cellwise_amplified_label_mass_refinement
      S cell hcellMeasurable activeCells hsupport allowed
      hallowedNonempty good hgoodMeasurable hgoodAllowed labelWeight
      goodCount hgoodCount (densityPower * fine.enncard)
      multiplicityCoefficient fine.enncard hpointwise hlabelBound with
    ⟨chosen, parentSelected, hparentSub, hparentSelectedEq, _hchosenAllowed,
      hparentGood, hparentMultiplicity, hparentMass⟩
  have hcellConst : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        cell first = cell second := by
    intro first second hgrid
    exact wz1PaperGridIndex_fine_to_coarse
      K hK hspatialScaleAligned hgrid
  have hgoodConst : ∀ parent first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        (good first parent ↔ good second parent) := by
    intro parent first second hgrid
    have hcarrier : ∀ index, first ∈ S.carrier index ↔
        second ∈ S.carrier index := fun index =>
      hSCubical.carrier_mem_iff_of_same_cell index hgrid
    constructor
    · rintro ⟨index, hindex, hparent⟩
      exact ⟨index, (hcarrier index).mp hindex, hparent⟩
    · rintro ⟨index, hindex, hparent⟩
      exact ⟨index, (hcarrier index).mpr hindex, hparent⟩
  have hparentCubical : WZ1PaperIsCubicalShading parentSelected := by
    rw [hparentSelectedEq]
    exact paperCellwisePredicateRestriction_cubical hSCubical
      cell hcellMeasurable good hgoodMeasurable chosen (by fun_prop)
      hcellConst hgoodConst
  have hdelta : 0 < delta := by
    have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
    rw [hspatialScaleAligned] at hspatialScale
    exact pos_of_mul_pos_right hspatialScale hKreal.le
  let naturalRadius : ℝ := 8 * kappa + 16 * parentRadius
  have hnaturalRadius : 0 ≤ naturalRadius := by
    dsimp only [naturalRadius]
    positivity
  have hsameCellNatural : ∀ point ∈ parentSelected.union,
      ∀ other ∈ parentSelected.union,
      wz1PaperGridIndex spatialScale point =
        wz1PaperGridIndex spatialScale other →
      dist (planeMap.planeMap point)
        (planeMap.planeMap other) ≤ naturalRadius := by
    intro point hpoint other hother hsameCell
    rcases hparentGood point hpoint with
      ⟨pointWitness, hpointWitness, hpointParent⟩
    rcases hparentGood other hother with
      ⟨otherWitness, hotherWitness, hotherParent⟩
    have hchosenEq : chosen (cell point) = chosen (cell other) := by
      simp [cell, hsameCell]
    have hparentsEq : cover.parent pointWitness =
        cover.parent otherWitness := by
      rw [hpointParent, hotherParent, hchosenEq]
    have hpointContained : (fine.tube pointWitness).carrier ⊆
        (coarse.tube (cover.parent pointWitness)).carrier := by
      exact (mem_wz2PaperOrdinaryFullFiberIndices_iff _ _).mp
        (cover.parent_mem_fullFiber pointWitness)
    have hotherContained : (fine.tube otherWitness).carrier ⊆
        (coarse.tube (cover.parent otherWitness)).carrier := by
      exact (mem_wz2PaperOrdinaryFullFiberIndices_iff _ _).mp
        (cover.parent_mem_fullFiber otherWitness)
    change ‖stableVerticalNormal
        (wz1PaperDirection (fine.tube (center point))) -
      stableVerticalNormal
        (wz1PaperDirection (fine.tube (center other)))‖ ≤ naturalRadius
    have hclose := stable_normals_close_of_pure_shared_parent
      hdelta.le hparentRadius hparentRadiusSmall hkappaNonnegative hkappaHalf
      (hline (center point)) (hline (center other))
      (hline pointWitness) (hline otherWitness)
      (hcluster pointWitness point hpointWitness)
      (hcluster otherWitness other hotherWitness)
      hpointContained (by simpa [hparentsEq] using hotherContained)
    exact hclose
  let occupied (currentCell : Cell) : Prop :=
    ∃ point ∈ parentSelected.union, cell point = currentCell
  let representative (currentCell : Cell) : Point3 :=
    if hcurrent : occupied currentCell then
      Classical.choose hcurrent
    else 0
  have hrepresentative : ∀ point ∈ parentSelected.union,
      representative (cell point) ∈ parentSelected.union ∧
        cell (representative (cell point)) = cell point := by
    intro point hpoint
    have hoccupied : occupied (cell point) :=
      ⟨point, hpoint, rfl⟩
    simp only [representative, dif_pos hoccupied]
    exact Classical.choose_spec hoccupied
  let localCenter : Cell → Point3 := fun currentCell =>
    planeMap.planeMap (representative currentCell)
  have hlocal : ∀ point ∈ parentSelected.union,
      dist (planeMap.planeMap point) (localCenter (cell point)) ≤
        naturalRadius := by
    intro point hpoint
    exact hsameCellNatural point hpoint
      (representative (cell point)) (hrepresentative point hpoint).1
      (hrepresentative point hpoint).2.symm
  have hplaneFine : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      planeMap.planeMap first = planeMap.planeMap second := by
    intro first second hgrid
    change stableVerticalNormal
        (wz1PaperDirection (fine.tube (center first))) =
      stableVerticalNormal
        (wz1PaperDirection (fine.tube (center second)))
    rw [hcenterCell first second hgrid]
  rcases paper_local_ball_cell_refinement
      parentSelected hparentCubical planeMap.planeMap planeMap.measurable
      cell hcellMeasurable hcellConst hplaneFine activeCells
      (by
        intro point hpoint
        have hpointS : point ∈ S.union := by
          rcases hpoint with ⟨index, hindex⟩
          exact ⟨index, hparentSub index hindex⟩
        exact hsupport point hpointS)
      localCenter hnaturalRadius hvariationScale hlocal with
    ⟨capSelected, hcapSubParent, hcapCubical, hcapSameCell,
      hcapMultiplicityParent, hcapMass⟩
  rcases paper_aligned_nearby_cell_residue_refinement_cubical
      planeMap.planeMap hdelta hspatialScale hcapCubical
      K hK hspatialScaleAligned hcapSameCell with
    ⟨selected, hselectedSubCap, hselectedCubical, hnearby,
      hselectedMultiplicityCap, hresidueMass⟩
  have hselectedSub : PaperIsSubshading selected S := fun index =>
    (hselectedSubCap index).trans
      ((hcapSubParent index).trans (hparentSub index))
  have hselectedMultiplicity : ∀ point ∈ selected.union,
      selected.pointMultiplicity point = S.pointMultiplicity point := by
    intro point hpoint
    have hpointCap : point ∈ capSelected.union := by
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, hselectedSubCap index hindex⟩
    have hpointParent : point ∈ parentSelected.union := by
      rcases hpointCap with ⟨index, hindex⟩
      exact ⟨index, hcapSubParent index hindex⟩
    exact (hselectedMultiplicityCap point hpoint).trans
      ((hcapMultiplicityParent point hpointCap).trans
        (hparentMultiplicity point hpointParent))
  have hscaled : fine.enncard * (densityPower * S.mass) ≤
      fine.enncard *
        (multiplicityCoefficient * parentSelected.mass) := by
    calc
      fine.enncard * (densityPower * S.mass) =
          (densityPower * fine.enncard) * S.mass := by ring
      _ ≤ multiplicityCoefficient * fine.enncard * parentSelected.mass :=
        hparentMass
      _ = fine.enncard *
          (multiplicityCoefficient * parentSelected.mass) := by ring
  have hcardZero : fine.enncard ≠ 0 := by
    change (fine.card : ENNReal) ≠ 0
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hfineNonempty
  have hcardTop : fine.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hparentCanceled : densityPower * S.mass ≤
      multiplicityCoefficient * parentSelected.mass :=
    (ENNReal.mul_le_mul_iff_right hcardZero hcardTop).mp hscaled
  refine ⟨planeMap, selected, (fun _ => rfl), hselectedSub,
    hselectedCubical, hnearby,
    hselectedMultiplicity, ?_⟩
  calc
    densityPower * S.mass ≤
        multiplicityCoefficient * parentSelected.mass := hparentCanceled
    _ ≤ multiplicityCoefficient *
        ((localPlaneMapCapCount naturalRadius variationScale : ENNReal) *
          capSelected.mass) := by gcongr
    _ ≤ multiplicityCoefficient *
        ((localPlaneMapCapCount naturalRadius variationScale : ENNReal) *
          (27 * selected.mass)) := by gcongr
    _ = (localPlaneMapCapCount
          (8 * kappa + 16 * parentRadius) variationScale : ENNReal) *
          27 * multiplicityCoefficient * selected.mass := by
      simp only [naturalRadius]
      ring

/-- Symmetric compatibility form in which the spatial and variation scales
are the same. -/
theorem paper_pure_dense_parent_nearby_variation
    {delta parentRadius cellScale kappa : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily parentRadius}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    {S : WZ1PaperTubeShading fine}
    (hfineNonempty : fine.Nonempty)
    (hline : WZ1PaperIsLineClass fine)
    (hSCubical : WZ1PaperIsCubicalShading S)
    (center : Point3 → Fin fine.card)
    (hcenterMeasurable : Measurable center)
    (hcenterCell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      center first = center second)
    (hcluster : ∀ index point, point ∈ S.carrier index →
      ‖wz1Cross (fine.tube (center point)).direction
        (fine.tube index).direction‖ ≤ kappa)
    (multiplicityCoefficient densityPower : ENNReal)
    (hdensityPoint : ∀ point ∈ S.union,
      densityPower * fine.enncard ≤
        multiplicityCoefficient *
          (S.pointMultiplicity point : ENNReal))
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (hparentRadius : 0 < parentRadius)
    (hparentRadiusSmall : parentRadius < 1 / 8)
    (hcellScale : 0 < cellScale)
    (hvariationScale : 0 < cellScale)
    (K : ℕ) (hK : 0 < K)
    (hcellScaleAligned : cellScale = (K : ℝ) * delta) :
    ∃ (planeMap : PaperWZ1WeakPlaneMapData S kappa)
      (selected : WZ1PaperTubeShading fine),
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ point ∈ selected.union, ∀ other ∈ selected.union,
        dist point other ≤ cellScale →
          dist (planeMap.planeMap point)
            (planeMap.planeMap other) ≤ cellScale) ∧
      (∀ point ∈ selected.union,
        selected.pointMultiplicity point = S.pointMultiplicity point) ∧
      densityPower * S.mass ≤
        (localPlaneMapCapCount
          (8 * kappa + 16 * parentRadius) cellScale : ENNReal) *
          27 * multiplicityCoefficient * selected.mass := by
  rcases paper_pure_dense_parent_nearby_asymmetric_variation
      cover hfineNonempty hline hSCubical center hcenterMeasurable
      hcenterCell hcluster multiplicityCoefficient densityPower hdensityPoint
      hkappaNonnegative hkappaHalf hparentRadius hparentRadiusSmall
      hcellScale hvariationScale K hK hcellScaleAligned with
    ⟨planeMap, selected, _hplaneMap, hsub, hcubical, hvariation,
      hmultiplicity, hmass⟩
  exact ⟨planeMap, selected, hsub, hcubical, hvariation,
    hmultiplicity, hmass⟩

end Kakeya.Assouad.PureWZ2

end
