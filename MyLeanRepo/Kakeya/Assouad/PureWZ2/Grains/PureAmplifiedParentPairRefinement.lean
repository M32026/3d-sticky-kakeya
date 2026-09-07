import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.AmplifiedLabelMassRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CubicalRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperTransversePairCount
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers

/-!
# Multiplicity-amplified parent pairs for a pure Definition 2.12 cover

The literal pure cover has no balanced coarse shading.  Its strict full
fibers nevertheless partition the fine indices through the uniquely derived
parent map.  We therefore allow every ordered pair of pure parents in every
spatial cell and weight a parent pair by the product of its two strict-fiber
cardinalities.  The total label weight is exactly the square of the fine
family cardinality.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The weighted parent-pair refinement for a literal pure partitioning
cover.  It uses only the derived strict-fiber parent map and retains point
multiplicity at every surviving point. -/
theorem paper_pure_amplified_parent_pair_refinement
    {delta parentRadius cellScale kappa : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily parentRadius}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    {S : WZ1PaperTubeShading fine}
    (hSCubical : WZ1PaperIsCubicalShading S)
    (hcoarseNonempty : coarse.Nonempty)
    (fineMultiplicity : ℕ)
    (hFineMultiplicity : ∀ p ∈ S.union,
      fineMultiplicity ≤ S.pointMultiplicity p)
    (hclose : ∀ p ∈ S.union, ∀ i, p ∈ S.carrier i →
      2 * paperCloseDirectionCount S p i kappa ≤ fineMultiplicity)
    (hparentRadius : 0 < parentRadius)
    (hcellScale : 0 < cellScale)
    (K : ℕ) (hK : 0 < K)
    (hcellScaleAligned : cellScale = (K : ℝ) * delta) :
    ∃ (chosen : (ℤ × ℤ × ℤ) → Fin coarse.card × Fin coarse.card)
      (selected : WZ1PaperTubeShading fine),
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ p ∈ selected.union,
        ∃ first second : Fin fine.card,
          p ∈ S.carrier first ∧ p ∈ S.carrier second ∧
          cover.parent first =
            (chosen (wz1PaperGridIndex cellScale p)).1 ∧
          cover.parent second =
            (chosen (wz1PaperGridIndex cellScale p)).2 ∧
          kappa ≤ ‖wz1Cross (fine.tube first).direction
            (fine.tube second).direction‖) ∧
      (∀ p ∈ selected.union,
        selected.pointMultiplicity p = S.pointMultiplicity p) ∧
      (fineMultiplicity : ENNReal) ^ 2 * S.mass ≤
        2 * fine.enncard ^ 2 * selected.mass := by
  classical
  let Cell := ℤ × ℤ × ℤ
  let Label := Fin coarse.card × Fin coarse.card
  let cell : Point3 → Cell := wz1PaperGridIndex cellScale
  have hcellMeasurable : Measurable cell := by
    have h : Measurable (fun p : Point3 =>
        (⌊p 0 / cellScale⌋, ⌊p 1 / cellScale⌋,
          ⌊p 2 / cellScale⌋)) := by
      fun_prop
    convert h using 1
    funext p
    simp [cell, wz1PaperGridIndex, gridIndex]
  let activeCells : Finset Cell :=
    wz1PaperGridIndicesInWindow cellScale hcellScale
  let allowed : Cell → Finset Label := fun _ => Finset.univ
  have hsupport : ∀ p ∈ S.union, cell p ∈ activeCells := by
    intro p hp
    rcases hp with ⟨index, hindex⟩
    have hbody := S.subset_body index hindex
    exact paper_point_gridIndex_in_window hcellScale hbody.2
  let parent : Fin coarse.card := ⟨0, hcoarseNonempty⟩
  letI : Nonempty Label := ⟨(parent, parent)⟩
  have hallowedNonempty : ∀ c ∈ activeCells, (allowed c).Nonempty := by
    intro _ _
    exact ⟨(parent, parent), Finset.mem_univ _⟩
  let good (p : Point3) (parents : Label) : Prop :=
    ∃ first second : Fin fine.card,
      p ∈ S.carrier first ∧ p ∈ S.carrier second ∧
      cover.parent first = parents.1 ∧
      cover.parent second = parents.2 ∧
      kappa ≤ ‖wz1Cross (fine.tube first).direction
        (fine.tube second).direction‖
  have hgoodMeasurable : ∀ parents : Label,
      MeasurableSet {p | good p parents} := by
    intro parents
    let pairs : Finset (Fin fine.card × Fin fine.card) :=
      Finset.univ.filter fun pair =>
        cover.parent pair.1 = parents.1 ∧
        cover.parent pair.2 = parents.2 ∧
        kappa ≤ ‖wz1Cross (fine.tube pair.1).direction
          (fine.tube pair.2).direction‖
    have heq : {p | good p parents} = ⋃ pair ∈ pairs,
        S.carrier pair.1 ∩ S.carrier pair.2 := by
      ext p
      simp only [good, pairs, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨first, second, hfirst, hsecond, hp1, hp2, htransverse⟩
        exact ⟨(first, second), ⟨hp1, hp2, htransverse⟩, hfirst, hsecond⟩
      · rintro ⟨pair, ⟨hp1, hp2, htransverse⟩, hfirst, hsecond⟩
        exact ⟨pair.1, pair.2, hfirst, hsecond, hp1, hp2, htransverse⟩
    rw [heq]
    exact Finset.measurableSet_biUnion pairs fun pair _ =>
      (S.measurable_carrier pair.1).inter (S.measurable_carrier pair.2)
  have hgoodAllowed : ∀ p ∈ S.union, ∀ parents : Label,
      good p parents → parents ∈ allowed (cell p) := by
    simp [allowed]
  let fiberCard : Fin coarse.card → ENNReal := fun currentParent =>
    ((wz2PaperOrdinaryFullFiberIndices fine coarse currentParent).card :
      ENNReal)
  let labelWeight : Cell → Label → ENNReal := fun _ parents =>
    fiberCard parents.1 * fiberCard parents.2
  let goodCount : Point3 → Cell → ENNReal := fun p c =>
    ∑ parents ∈ allowed c,
      ({p | good p parents}.indicator
        (fun _ => labelWeight c parents)) p
  have hgoodCount : ∀ p c, goodCount p c =
      ∑ parents ∈ allowed c,
        ({p | good p parents}.indicator
          (fun _ => labelWeight c parents)) p := by
    intro _ _
    rfl
  have hfiberEq : ∀ currentParent : Fin coarse.card,
      wz2PaperOrdinaryFullFiberIndices fine coarse currentParent =
        Finset.univ.filter fun source =>
          cover.parent source = currentParent := by
    intro currentParent
    ext source
    simpa using
      (cover.mem_fullFiber_iff_parent_eq
        hparentRadius.le currentParent source)
  have hfiberPartitionNat :
      ∑ currentParent : Fin coarse.card,
          (wz2PaperOrdinaryFullFiberIndices fine coarse currentParent).card =
        fine.card := by
    have hmaps : Set.MapsTo cover.parent
        (↑(Finset.univ : Finset (Fin fine.card)) : Set (Fin fine.card))
        (↑(Finset.univ : Finset (Fin coarse.card)) :
          Set (Fin coarse.card)) := by
      intro source _
      exact Finset.mem_univ _
    have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
    simp_rw [hfiberEq]
    simpa using hpartition.symm
  have hfiberSum :
      (∑ currentParent : Fin coarse.card, fiberCard currentParent) =
        fine.enncard := by
    change
      (∑ currentParent : Fin coarse.card,
        ((wz2PaperOrdinaryFullFiberIndices fine coarse currentParent).card :
          ENNReal)) = (fine.card : ENNReal)
    rw [← Nat.cast_sum, hfiberPartitionNat]
  have hlabelBound : ∀ c ∈ activeCells,
      (∑ parents ∈ allowed c, labelWeight c parents) ≤
        fine.enncard ^ 2 := by
    intro c _
    calc
      (∑ parents ∈ allowed c, labelWeight c parents) ≤
          ∑ parents : Label, labelWeight c parents := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ (allowed c)) (fun _ _ _ => bot_le)
      _ =
          (∑ currentParent : Fin coarse.card, fiberCard currentParent) *
            (∑ currentParent : Fin coarse.card, fiberCard currentParent) := by
        rw [Fintype.sum_prod_type]
        simp only [labelWeight]
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul]
      _ = fine.enncard ^ 2 := by rw [hfiberSum, pow_two]
  have hpointwise : ∀ p ∈ S.union,
      (fineMultiplicity : ENNReal) ^ 2 ≤
        2 * goodCount p (cell p) := by
    intro p hp
    let active : Finset (Fin fine.card) :=
      Finset.univ.filter fun i => p ∈ S.carrier i
    let transversePairs : Finset (Fin fine.card × Fin fine.card) :=
      (active ×ˢ active).filter fun pair =>
        kappa ≤ ‖wz1Cross (fine.tube pair.1).direction
          (fine.tube pair.2).direction‖
    have htransverseLower :
        (fineMultiplicity : ENNReal) ^ 2 ≤
          2 * (transversePairs.card : ENNReal) := by
      have hnat := paper_transverse_ordered_pairs_lower
        hclose hFineMultiplicity p hp
      have hm : (fineMultiplicity : ENNReal) ≤
          (S.pointMultiplicity p : ENNReal) := by
        exact_mod_cast hFineMultiplicity p hp
      calc
        (fineMultiplicity : ENNReal) ^ 2 ≤
            (S.pointMultiplicity p : ENNReal) ^ 2 :=
          pow_le_pow_left' hm 2
        _ ≤ 2 * (transversePairs.card : ENNReal) := by
          exact_mod_cast hnat
    let goodLabels : Finset Label :=
      (allowed (cell p)).filter fun parents => good p parents
    let fiberPairs (parents : Label) :
        Finset (Fin fine.card × Fin fine.card) :=
      transversePairs.filter fun pair =>
        cover.parent pair.1 = parents.1 ∧
        cover.parent pair.2 = parents.2
    have hdecomp : transversePairs = goodLabels.biUnion fiberPairs := by
      ext pair
      constructor
      · intro hpair
        have hfirst : p ∈ S.carrier pair.1 :=
          (Finset.mem_filter.mp (Finset.mem_product.mp
            (Finset.mem_filter.mp hpair).1).1).2
        have hsecond : p ∈ S.carrier pair.2 :=
          (Finset.mem_filter.mp (Finset.mem_product.mp
            (Finset.mem_filter.mp hpair).1).2).2
        let parents : Label :=
          (cover.parent pair.1, cover.parent pair.2)
        have hparentsAllowed : parents ∈ allowed (cell p) :=
          hgoodAllowed p hp parents
            ⟨pair.1, pair.2, hfirst, hsecond, rfl, rfl,
              (Finset.mem_filter.mp hpair).2⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨parents, Finset.mem_filter.mpr
          ⟨hparentsAllowed, ?_⟩, ?_⟩
        · exact ⟨pair.1, pair.2, hfirst, hsecond, rfl, rfl,
            (Finset.mem_filter.mp hpair).2⟩
        · exact Finset.mem_filter.mpr ⟨hpair, rfl, rfl⟩
      · intro hpair
        rcases Finset.mem_biUnion.mp hpair with
          ⟨parents, _hparents, hpairFiber⟩
        exact (Finset.mem_filter.mp hpairFiber).1
    have hfiberPairs : ∀ parents ∈ goodLabels,
        ((fiberPairs parents).card : ENNReal) ≤
          labelWeight (cell p) parents := by
      intro parents _
      let firstFiber : Finset (Fin fine.card) :=
        Finset.univ.filter fun i =>
          cover.parent i = parents.1 ∧ p ∈ S.carrier i
      let secondFiber : Finset (Fin fine.card) :=
        Finset.univ.filter fun i =>
          cover.parent i = parents.2 ∧ p ∈ S.carrier i
      have hsubset : fiberPairs parents ⊆
          firstFiber.product secondFiber := by
        intro pair hpair
        rcases Finset.mem_filter.mp hpair with ⟨htransverse, hp1, hp2⟩
        rcases Finset.mem_filter.mp htransverse with ⟨hactive, _⟩
        rcases Finset.mem_product.mp hactive with
          ⟨hfirstActive, hsecondActive⟩
        exact Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp1,
            (Finset.mem_filter.mp hfirstActive).2⟩,
           Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp2,
            (Finset.mem_filter.mp hsecondActive).2⟩⟩
      have hfirstSubset : firstFiber ⊆
          wz2PaperOrdinaryFullFiberIndices fine coarse parents.1 := by
        intro index hindex
        apply (cover.mem_fullFiber_iff_parent_eq
          hparentRadius.le parents.1 index).mpr
        exact (Finset.mem_filter.mp hindex).2.1
      have hsecondSubset : secondFiber ⊆
          wz2PaperOrdinaryFullFiberIndices fine coarse parents.2 := by
        intro index hindex
        apply (cover.mem_fullFiber_iff_parent_eq
          hparentRadius.le parents.2 index).mpr
        exact (Finset.mem_filter.mp hindex).2.1
      calc
        ((fiberPairs parents).card : ENNReal) ≤
            ((firstFiber.product secondFiber).card : ENNReal) := by
          exact_mod_cast Finset.card_le_card hsubset
        _ = (firstFiber.card : ENNReal) *
            (secondFiber.card : ENNReal) := by
          simp [Finset.card_product]
        _ ≤
            ((wz2PaperOrdinaryFullFiberIndices fine coarse parents.1).card :
              ENNReal) *
            ((wz2PaperOrdinaryFullFiberIndices fine coarse parents.2).card :
              ENNReal) := by
          gcongr <;> exact_mod_cast Finset.card_le_card
            (by assumption)
        _ = labelWeight (cell p) parents := by
          rfl
    have hsum : (transversePairs.card : ENNReal) ≤
        ∑ parents ∈ goodLabels, labelWeight (cell p) parents := by
      rw [hdecomp]
      have hcardUnion :
          ((goodLabels.biUnion fiberPairs).card : ENNReal) ≤
            ∑ parents ∈ goodLabels,
              ((fiberPairs parents).card : ENNReal) := by
        exact_mod_cast Finset.card_biUnion_le
      exact hcardUnion.trans <| by
        apply Finset.sum_le_sum
        intro parents hparents
        exact hfiberPairs parents hparents
    have hgoodWeight : goodCount p (cell p) =
        ∑ parents ∈ goodLabels, labelWeight (cell p) parents := by
      rw [hgoodCount p (cell p)]
      simp [goodLabels, Set.indicator_apply, Finset.sum_filter]
    calc
      (fineMultiplicity : ENNReal) ^ 2 ≤
          2 * (transversePairs.card : ENNReal) := htransverseLower
      _ ≤ 2 * ∑ parents ∈ goodLabels,
          labelWeight (cell p) parents := by gcongr
      _ = 2 * goodCount p (cell p) := by rw [hgoodWeight]
  rcases paper_cellwise_amplified_label_mass_refinement
      (Cell := Cell) (Label := Label)
      S cell hcellMeasurable activeCells hsupport allowed
      hallowedNonempty good hgoodMeasurable hgoodAllowed labelWeight
      goodCount hgoodCount
      ((fineMultiplicity : ENNReal) ^ 2) 2
      (fine.enncard ^ 2) hpointwise hlabelBound with
    ⟨chosen, selected, hsub, hselectedEq, _hchosenAllowed, hselectedGood,
      hselectedMultiplicity, hmass⟩
  have hcellConst : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        cell first = cell second := by
    intro first second hgrid
    exact wz1PaperGridIndex_fine_to_coarse
      K hK hcellScaleAligned hgrid
  have hgoodConst : ∀ parents first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        (good first parents ↔ good second parents) := by
    intro parents first second hgrid
    have hcarrier : ∀ index, first ∈ S.carrier index ↔
        second ∈ S.carrier index := by
      intro index
      exact hSCubical.carrier_mem_iff_of_same_cell index hgrid
    constructor
    · rintro ⟨i, j, hi, hj, hpi, hpj, htransverse⟩
      exact ⟨i, j, (hcarrier i).mp hi, (hcarrier j).mp hj,
        hpi, hpj, htransverse⟩
    · rintro ⟨i, j, hi, hj, hpi, hpj, htransverse⟩
      exact ⟨i, j, (hcarrier i).mpr hi, (hcarrier j).mpr hj,
        hpi, hpj, htransverse⟩
  have hselectedCubical : WZ1PaperIsCubicalShading selected := by
    rw [hselectedEq]
    exact paperCellwisePredicateRestriction_cubical hSCubical
      cell hcellMeasurable good hgoodMeasurable chosen (by fun_prop)
      hcellConst hgoodConst
  exact ⟨chosen, selected, hsub, hselectedCubical, hselectedGood,
    hselectedMultiplicity, hmass⟩

end Kakeya.Assouad

end
