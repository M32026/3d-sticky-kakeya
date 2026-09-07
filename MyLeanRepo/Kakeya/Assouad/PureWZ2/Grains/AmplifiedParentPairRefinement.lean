import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.AmplifiedLabelMassRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellwiseParentPairRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperTransversePairCount
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFinePullback

/-!
# Multiplicity-amplified coarse-parent-pair refinement

Instantiate the weighted label selector with ordered coarse-parent pairs.
The output is the mass-efficient parent-pair refinement needed by the paper's
Lemma 14.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

theorem paper_amplified_parent_pair_refinement
    {delta rho kappa : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading S : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hSSubFine : PaperIsSubshading S fineShading)
    (hSCubical : WZ1PaperIsCubicalShading S)
    (hcoarseNonempty : coarse.Nonempty)
    (fineMultiplicity : ℕ)
    (hFineMultiplicity : ∀ p ∈ S.union,
      fineMultiplicity ≤ S.pointMultiplicity p)
    (hclose : ∀ p ∈ S.union, ∀ i, p ∈ S.carrier i →
      2 * paperCloseDirectionCount S p i kappa ≤ fineMultiplicity)
    (fiberPower : ENNReal)
    (hfiber : ∀ parent p,
      (((Finset.univ.filter fun i : Fin fine.card =>
        PureWZ2.selectParent cover i = parent ∧ p ∈ S.carrier i).card : ℕ) :
        ENNReal) ≤ fiberPower *
          ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal))
    (K : ℕ) (hK : 0 < K) (hrhoAligned : rho = (K : ℝ) * delta) :
    ∃ (chosen : (ℤ × ℤ × ℤ) → Fin coarse.card × Fin coarse.card)
      (selected : WZ1PaperTubeShading fine),
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ p ∈ selected.union,
        ∃ first second : Fin fine.card,
          p ∈ S.carrier first ∧ p ∈ S.carrier second ∧
          PureWZ2.selectParent cover first =
            (chosen (wz1PaperGridIndex rho p)).1 ∧
          PureWZ2.selectParent cover second =
            (chosen (wz1PaperGridIndex rho p)).2 ∧
          kappa ≤ ‖wz1Cross (fine.tube first).direction
            (fine.tube second).direction‖) ∧
      (∀ p ∈ selected.union,
        selected.pointMultiplicity p = S.pointMultiplicity p) ∧
      (fineMultiplicity : ENNReal) ^ 2 * S.mass ≤
        (2 * fiberPower ^ 2) * fine.enncard ^ 2 * selected.mass := by
  classical
  let Cell := ℤ × ℤ × ℤ
  let Label := Fin coarse.card × Fin coarse.card
  let cell : Point3 → Cell := wz1PaperGridIndex rho
  have hcellMeasurable : Measurable cell := by
    have h : Measurable (fun p : Point3 =>
        (⌊p 0 / rho⌋, ⌊p 1 / rho⌋, ⌊p 2 / rho⌋)) := by
      fun_prop
    convert h using 1
    funext p
    simp [cell, wz1PaperGridIndex, gridIndex]
  let allowed : Cell → Finset Label := fun c =>
    (paperBalancedCellParents balanced c).product
      (paperBalancedCellParents balanced c)
  have hsupport : ∀ p ∈ S.union, cell p ∈ balanced.activeCells := by
    intro p hp
    apply paperBalanced_fine_point_active balanced p
    rcases hp with ⟨i, hi⟩
    exact ⟨i, hSSubFine i hi⟩
  have hallowedNonempty : ∀ c ∈ balanced.activeCells,
      (allowed c).Nonempty := by
    intro c hc
    rcases balanced.cellIntersection_nonempty c hc with ⟨p, hpS, hpCell⟩
    rcases hpS with ⟨i, hi⟩
    have hparent : PureWZ2.selectParent cover i ∈
        paperBalancedCellParents balanced c := by
      have hpc : wz1PaperGridIndex rho p = c :=
        (mem_wz1PaperGridCube rho c p).mp hpCell
      simpa [hpc] using
        selectedParent_mem_paperBalancedCellParents balanced hi
    exact ⟨(PureWZ2.selectParent cover i, PureWZ2.selectParent cover i),
      Finset.mem_product.mpr ⟨hparent, hparent⟩⟩
  let good (p : Point3) (parents : Label) : Prop :=
    ∃ first second : Fin fine.card,
      p ∈ S.carrier first ∧ p ∈ S.carrier second ∧
      PureWZ2.selectParent cover first = parents.1 ∧
      PureWZ2.selectParent cover second = parents.2 ∧
      kappa ≤ ‖wz1Cross (fine.tube first).direction
        (fine.tube second).direction‖
  have hgoodMeasurable : ∀ parents : Label,
      MeasurableSet {p | good p parents} := by
    intro parents
    let pairs : Finset (Fin fine.card × Fin fine.card) :=
      Finset.univ.filter fun pair =>
        PureWZ2.selectParent cover pair.1 = parents.1 ∧
        PureWZ2.selectParent cover pair.2 = parents.2 ∧
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
    intro p hp parents hgood
    rcases hgood with
      ⟨first, second, hfirst, hsecond, hp1, hp2, _htransverse⟩
    apply Finset.mem_product.mpr
    constructor
    · rw [← hp1]
      exact selectedParent_mem_paperBalancedCellParents balanced
        (hSSubFine first hfirst)
    · rw [← hp2]
      exact selectedParent_mem_paperBalancedCellParents balanced
        (hSSubFine second hsecond)
  let fiberCard : Fin coarse.card → ENNReal := fun parent =>
    ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal)
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
    intro p c
    rfl
  have hfiberPartitionNat :
      ∑ parent : Fin coarse.card,
          (wz2PaperFullFiberIndices fine coarse parent).card = fine.card := by
    have hmaps : Set.MapsTo (PureWZ2.selectParent cover)
        (↑(Finset.univ : Finset (Fin fine.card)) : Set (Fin fine.card))
        (↑(Finset.univ : Finset (Fin coarse.card)) :
          Set (Fin coarse.card)) := by
      intro source _
      exact Finset.mem_univ _
    have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
    have hfiberEq : ∀ parent : Fin coarse.card,
        wz2PaperFullFiberIndices fine coarse parent =
          Finset.univ.filter fun source =>
            PureWZ2.selectParent cover source = parent := by
      intro parent
      rw [cover.fullFiberIndices_eq]
      rfl
    simp_rw [hfiberEq]
    simpa using hpartition.symm
  have hfiberSum :
      (∑ parent : Fin coarse.card, fiberCard parent) = fine.enncard := by
    change
      (∑ parent : Fin coarse.card,
        ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal)) =
        (fine.card : ENNReal)
    rw [← Nat.cast_sum, hfiberPartitionNat]
  have hlabelBound : ∀ c ∈ balanced.activeCells,
      (∑ parents ∈ allowed c, labelWeight c parents) ≤
        fine.enncard ^ 2 := by
    intro c _hc
    calc
      (∑ parents ∈ allowed c, labelWeight c parents) ≤
          ∑ parents : Label, labelWeight c parents := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ (allowed c)) (fun _ _ _ => bot_le)
      _ = (∑ parent : Fin coarse.card, fiberCard parent) *
          (∑ parent : Fin coarse.card, fiberCard parent) := by
        rw [Fintype.sum_prod_type]
        simp only [labelWeight]
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul]
      _ = fine.enncard ^ 2 := by rw [hfiberSum, pow_two]
  have hpointwise : ∀ p ∈ S.union,
      (fineMultiplicity : ENNReal) ^ 2 ≤
        (2 * fiberPower ^ 2) * goodCount p (cell p) := by
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
        PureWZ2.selectParent cover pair.1 = parents.1 ∧
        PureWZ2.selectParent cover pair.2 = parents.2
    have hdecomp : transversePairs =
        goodLabels.biUnion fiberPairs := by
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
          (PureWZ2.selectParent cover pair.1,
            PureWZ2.selectParent cover pair.2)
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
        rcases Finset.mem_biUnion.mp hpair with ⟨parents, _hparents, hpairFiber⟩
        exact (Finset.mem_filter.mp hpairFiber).1
    have hfiberPairs : ∀ parents ∈ goodLabels,
        ((fiberPairs parents).card : ENNReal) ≤
          fiberPower ^ 2 * labelWeight (cell p) parents := by
      intro parents _
      let firstFiber : Finset (Fin fine.card) :=
        Finset.univ.filter fun i =>
          PureWZ2.selectParent cover i = parents.1 ∧ p ∈ S.carrier i
      let secondFiber : Finset (Fin fine.card) :=
        Finset.univ.filter fun i =>
          PureWZ2.selectParent cover i = parents.2 ∧ p ∈ S.carrier i
      have hsubset : fiberPairs parents ⊆ firstFiber.product secondFiber := by
        intro pair hpair
        rcases Finset.mem_filter.mp hpair with ⟨htransverse, hp1, hp2⟩
        rcases Finset.mem_filter.mp htransverse with ⟨hactive, _⟩
        rcases Finset.mem_product.mp hactive with ⟨hfirstActive, hsecondActive⟩
        exact Finset.mem_product.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp1,
            (Finset.mem_filter.mp hfirstActive).2⟩,
           Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp2,
            (Finset.mem_filter.mp hsecondActive).2⟩⟩
      have hfirstCap : (firstFiber.card : ENNReal) ≤
          fiberPower * fiberCard parents.1 := by
        simpa [firstFiber, fiberCard] using hfiber parents.1 p
      have hsecondCap : (secondFiber.card : ENNReal) ≤
          fiberPower * fiberCard parents.2 := by
        simpa [secondFiber, fiberCard] using hfiber parents.2 p
      calc
        ((fiberPairs parents).card : ENNReal) ≤
            ((firstFiber.product secondFiber).card : ENNReal) := by
          exact_mod_cast Finset.card_le_card hsubset
        _ = (firstFiber.card : ENNReal) * (secondFiber.card : ENNReal) := by
          simp [Finset.card_product]
        _ ≤ (fiberPower * fiberCard parents.1) *
            (fiberPower * fiberCard parents.2) := by gcongr
        _ = fiberPower ^ 2 * labelWeight (cell p) parents := by
          simp only [labelWeight]
          ring
    have hsum : (transversePairs.card : ENNReal) ≤
        fiberPower ^ 2 *
          ∑ parents ∈ goodLabels, labelWeight (cell p) parents := by
      rw [hdecomp]
      have hcardUnion :
          ((goodLabels.biUnion fiberPairs).card : ENNReal) ≤
            ∑ parents ∈ goodLabels, ((fiberPairs parents).card : ENNReal) := by
        exact_mod_cast Finset.card_biUnion_le
      calc
        ((goodLabels.biUnion fiberPairs).card : ENNReal) ≤
            ∑ parents ∈ goodLabels, ((fiberPairs parents).card : ENNReal) :=
          hcardUnion
        _ ≤ ∑ parents ∈ goodLabels,
            fiberPower ^ 2 * labelWeight (cell p) parents := by
          apply Finset.sum_le_sum
          intro parents hparents
          exact hfiberPairs parents hparents
        _ = fiberPower ^ 2 *
            ∑ parents ∈ goodLabels, labelWeight (cell p) parents := by
          rw [Finset.mul_sum]
    have hgoodWeight : goodCount p (cell p) =
        ∑ parents ∈ goodLabels, labelWeight (cell p) parents := by
      rw [hgoodCount p (cell p)]
      simp [goodLabels, Set.indicator_apply, Finset.sum_filter]
    calc
      (fineMultiplicity : ENNReal) ^ 2 ≤
          2 * (transversePairs.card : ENNReal) := htransverseLower
      _ ≤ 2 * (fiberPower ^ 2 *
          ∑ parents ∈ goodLabels, labelWeight (cell p) parents) := by
        gcongr
      _ = (2 * fiberPower ^ 2) * goodCount p (cell p) := by
        rw [hgoodWeight]
        ring
  let parent : Fin coarse.card := ⟨0, hcoarseNonempty⟩
  letI : Nonempty Label := ⟨(parent, parent)⟩
  rcases paper_cellwise_amplified_label_mass_refinement
      (Cell := Cell) (Label := Label)
      S cell hcellMeasurable balanced.activeCells hsupport allowed
      hallowedNonempty good hgoodMeasurable hgoodAllowed labelWeight
      goodCount hgoodCount
      ((fineMultiplicity : ENNReal) ^ 2) (2 * fiberPower ^ 2)
      (fine.enncard ^ 2) (by
        intro p hp
        exact hpointwise p hp) hlabelBound with
    ⟨chosen, selected, hsub, hselectedEq, _hchosenAllowed, hselectedGood,
      hselectedMultiplicity, hmass⟩
  have hcellConst : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        cell first = cell second := by
    intro first second hgrid
    exact wz1PaperGridIndex_fine_to_coarse K hK hrhoAligned hgrid
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
