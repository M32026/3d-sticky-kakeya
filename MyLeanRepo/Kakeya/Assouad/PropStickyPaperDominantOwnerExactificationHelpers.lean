import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDominantOwnerExactificationStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers

/-!
# Helper lemmas for dominant-owner exactification

Cardinality dyadic pigeonholing, complete-fiber cover restriction, and the
finite volume identities used by the exactification proof.
-/

noncomputable section

namespace Kakeya.Assouad

open Finset MeasureTheory

attribute [local instance] Classical.propDecidable

lemma dyadic_cardinality_pigeonhole
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ)
    (hs : s.Nonempty) (hpos : ∀ i ∈ s, 0 < f i)
    (K : ℕ) (hK : ∀ i ∈ s, Nat.log 2 (f i) < K) :
    ∃ (k : ℕ) (t : Finset α),
      t.Nonempty ∧ t ⊆ s ∧
      (∀ i ∈ t, 2 ^ k ≤ f i ∧ f i < 2 ^ (k + 1)) ∧
      s.card ≤ K * t.card := by
  let band : ℕ → Finset α := fun k =>
    s.filter (fun i => 2 ^ k ≤ f i ∧ f i < 2 ^ (k + 1))
  have h_cover : ∀ i ∈ s, ∃ k ∈ Finset.range K, i ∈ band k := by
    intro i hi
    let k := Nat.log 2 (f i)
    have hfk_pos : 0 < f i := hpos i hi
    have h1 : 2 ^ k ≤ f i := Nat.pow_log_le_self 2 hfk_pos.ne'
    have h2 : f i < 2 ^ (k + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) (f i)
    have hk_lt_K : k < K := hK i hi
    have hk_range : k ∈ Finset.range K := by
      simp only [Finset.mem_range]
      exact hk_lt_K
    have h_in_band : i ∈ band k := by
      simp only [band, Finset.mem_filter]
      exact ⟨hi, h1, h2⟩
    exact ⟨k, hk_range, h_in_band⟩
  have h_disjoint : ∀ k ∈ Finset.range K, ∀ l ∈ Finset.range K,
      k ≠ l → Disjoint (band k) (band l) := by
    intro k _ l _ hne
    simp only [band, Finset.disjoint_left]
    intro i hi1 hi2
    have h1 : 2 ^ k ≤ f i := (Finset.mem_filter.mp hi1).2.1
    have h2 : f i < 2 ^ (k + 1) := (Finset.mem_filter.mp hi1).2.2
    have h3 : 2 ^ l ≤ f i := (Finset.mem_filter.mp hi2).2.1
    have h4 : f i < 2 ^ (l + 1) := (Finset.mem_filter.mp hi2).2.2
    by_cases h : k < l
    · have h5 : k + 1 ≤ l := by omega
      have h6 : 2 ^ (k + 1) ≤ 2 ^ l := by
        gcongr
        norm_num
      have h7 : 2 ^ (k + 1) ≤ f i := h6.trans h3
      exact not_le.mpr h2 h7
    · have h6 : l < k := by omega
      have h7 : l + 1 ≤ k := by omega
      have h8 : 2 ^ (l + 1) ≤ 2 ^ k := by
        gcongr
        norm_num
      have h9 : 2 ^ (l + 1) ≤ f i := h8.trans h1
      exact not_le.mpr h4 h9
  have h_union : Finset.biUnion (Finset.range K) band = s := by
    ext i
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨k, _, hk⟩
      exact (Finset.mem_filter.mp hk).1
    · intro hi
      exact h_cover i hi
  have h_card : s.card = ∑ k ∈ Finset.range K, (band k).card := by
    rw [← Finset.card_biUnion h_disjoint, h_union]
  have hK_pos : 0 < K := by
    rcases hs with ⟨i, hi⟩
    have h : Nat.log 2 (f i) < K := hK i hi
    exact Nat.pos_of_ne_zero fun h0 => by
      rw [h0] at h
      simp at h
  have h_nonempty_range : (Finset.range K).Nonempty :=
    Finset.nonempty_range_iff.mpr (ne_of_gt hK_pos)
  have h_max : ∃ k ∈ Finset.range K,
      ∀ l ∈ Finset.range K, (band l).card ≤ (band k).card :=
    Finset.exists_max_image
      (Finset.range K) (fun k => (band k).card) h_nonempty_range
  rcases h_max with ⟨k, hk, hmax⟩
  let t := band k
  have ht_sub : t ⊆ s := Finset.filter_subset _ _
  have h_band : ∀ i ∈ t, 2 ^ k ≤ f i ∧ f i < 2 ^ (k + 1) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have h_sum_le : s.card ≤ K * t.card := by
    rw [h_card]
    calc
      ∑ l ∈ Finset.range K, (band l).card
          ≤ ∑ l ∈ Finset.range K, t.card := by
        apply Finset.sum_le_sum
        intro l hl
        exact hmax l hl
      _ = (Finset.range K).card * t.card := by
        simp [Finset.sum_const]
      _ = K * t.card := by simp
  have ht_nonempty : t.Nonempty := by
    by_contra h
    have h_empty : t = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using h
    rw [h_empty] at h_sum_le
    have h_s_empty : s = ∅ := by simpa using h_sum_le
    exact hs.ne_empty h_s_empty
  exact ⟨k, t, ht_nonempty, ht_sub, h_band, h_sum_le⟩

def WZ2PaperPartitioningCover.restrict
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (retainedParents : Finset (Fin coarse.card))
    (hretained : retainedParents.Nonempty) :
    WZ2PaperPartitioningCover
      (Kakeya.Streamlined.TubeSubfamily.fromFinset fine
        (Finset.univ.filter fun source =>
          cover.parent source ∈ retainedParents)).family
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        coarse retainedParents).family := by
  let selectedFineIndices :=
    Finset.univ.filter fun source : Fin fine.card =>
      cover.parent source ∈ retainedParents
  let selected :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset fine selectedFineIndices
  let coarseSub :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset coarse retainedParents
  let eCoarse : Fin retainedParents.card ≃ {p // p ∈ retainedParents} :=
    retainedParents.orderIsoOfFin rfl
  let restrictedParent :
      Fin selected.family.card → Fin coarseSub.family.card :=
    fun index =>
      let parent := cover.parent (selected.embedding index)
      have parent_mem : parent ∈ retainedParents := by
        have index_mem :
            selected.embedding index ∈ selectedFineIndices :=
          Finset.orderEmbOfFin_mem selectedFineIndices rfl index
        simpa [selectedFineIndices, Finset.mem_filter] using index_mem
      eCoarse.symm ⟨parent, parent_mem⟩
  have embedding_eq :
      ∀ index : Fin coarseSub.family.card,
        coarseSub.embedding index =
          (eCoarse index : Fin coarse.card) := by
    intro index
    rfl
  have restrictedParent_spec :
      ∀ index,
        coarseSub.embedding (restrictedParent index) =
          cover.parent (selected.embedding index) := by
    intro index
    let parent := cover.parent (selected.embedding index)
    have parent_mem : parent ∈ retainedParents := by
      have index_mem :
          selected.embedding index ∈ selectedFineIndices :=
        Finset.orderEmbOfFin_mem selectedFineIndices rfl index
      simpa [selectedFineIndices, Finset.mem_filter] using index_mem
    let parentSubtype : {p // p ∈ retainedParents} :=
      ⟨parent, parent_mem⟩
    have h1 :
        eCoarse (restrictedParent index) = parentSubtype :=
      eCoarse.apply_symm_apply parentSubtype
    have h2 :
        (eCoarse (restrictedParent index) : Fin coarse.card) =
          parent :=
      congrArg Subtype.val h1
    rw [embedding_eq, h2]
  refine
    { parent := restrictedParent
      parent_surjective := ?_
      parent_covers := ?_
      parent_unique := ?_
      parent_carrier_covers := ?_
      literal_parent_unique := ?_
      literal_doubled_fibers_disjoint := ?_
      doubled_fibers_disjoint := ?_ }
  · intro parent'
    let parent : Fin coarse.card := coarseSub.embedding parent'
    have parent_mem : parent ∈ retainedParents :=
      Finset.orderEmbOfFin_mem retainedParents rfl parent'
    rcases cover.parent_surjective parent with ⟨source, source_parent⟩
    have source_mem : source ∈ selectedFineIndices := by
      simp only [selectedFineIndices, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [source_parent]
      exact parent_mem
    let eFine :
        Fin selectedFineIndices.card ≃ {source // source ∈ selectedFineIndices} :=
      selectedFineIndices.orderIsoOfFin rfl
    let index : Fin selected.family.card :=
      eFine.symm ⟨source, source_mem⟩
    have embedding_source : selected.embedding index = source := by
      have h3 : eFine index = ⟨source, source_mem⟩ :=
        eFine.apply_symm_apply ⟨source, source_mem⟩
      exact congrArg Subtype.val h3
    have parent_eq : restrictedParent index = parent' := by
      apply coarseSub.embedding.injective
      rw [restrictedParent_spec, embedding_source, source_parent]
    exact ⟨index, parent_eq⟩
  · intro index
    have h := cover.parent_covers (selected.embedding index)
    have tube_eq :
        coarseSub.family.tube (restrictedParent index) =
          coarse.tube (cover.parent (selected.embedding index)) := by
      rw [coarseSub.tube_eq, restrictedParent_spec]
    rw [selected.tube_eq, tube_eq]
    exact h
  · intro index candidate' hcov
    have h :
        WZ1PaperTubeCovers
          (fine.tube (selected.embedding index))
          (coarse.tube (coarseSub.embedding candidate')) := by
      rw [← selected.tube_eq index, ← coarseSub.tube_eq candidate']
      exact hcov
    have ambient_eq :
        coarseSub.embedding candidate' =
          cover.parent (selected.embedding index) :=
      cover.parent_unique
        (selected.embedding index) (coarseSub.embedding candidate') h
    apply coarseSub.embedding.injective
    rw [ambient_eq, restrictedParent_spec]
  · intro index
    have h := cover.parent_carrier_covers (selected.embedding index)
    have tube_eq :
        coarseSub.family.tube (restrictedParent index) =
          coarse.tube (cover.parent (selected.embedding index)) := by
      rw [coarseSub.tube_eq, restrictedParent_spec]
    rw [selected.tube_eq, tube_eq]
    exact h
  · intro index candidate' hcov
    have h :
        WZ2PaperTubeCarrierCovers
          (fine.tube (selected.embedding index))
          (coarse.tube (coarseSub.embedding candidate')) := by
      rw [← selected.tube_eq index, ← coarseSub.tube_eq candidate']
      exact hcov
    have ambient_eq :
        coarseSub.embedding candidate' =
          cover.parent (selected.embedding index) :=
      cover.literal_parent_unique
        (selected.embedding index) (coarseSub.embedding candidate') h
    apply coarseSub.embedding.injective
    rw [ambient_eq, restrictedParent_spec]
  · intro first second hne
    let ambientFirst : Fin coarse.card := coarseSub.embedding first
    let ambientSecond : Fin coarse.card := coarseSub.embedding second
    have ambient_ne : ambientFirst ≠ ambientSecond := by
      intro h
      exact hne (coarseSub.embedding.injective h)
    rw [Finset.disjoint_left]
    intro source h1 h2
    have ambient_h1 :
        selected.embedding source ∈
          wz2PaperLiteralDoubledFiberIndices fine coarse ambientFirst := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hcontainment :=
        (Finset.mem_filter.mp h1).2
      rw [selected.tube_eq source, coarseSub.tube_eq first] at hcontainment
      exact hcontainment
    have ambient_h2 :
        selected.embedding source ∈
          wz2PaperLiteralDoubledFiberIndices fine coarse ambientSecond := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hcontainment :=
        (Finset.mem_filter.mp h2).2
      rw [selected.tube_eq source, coarseSub.tube_eq second] at hcontainment
      exact hcontainment
    exact
      ((Finset.disjoint_left.mp
          (cover.literal_doubled_fibers_disjoint
            ambientFirst ambientSecond ambient_ne))
        ambient_h1) ambient_h2
  · intro first second hne
    let ambientFirst : Fin coarse.card := coarseSub.embedding first
    let ambientSecond : Fin coarse.card := coarseSub.embedding second
    have ambient_ne : ambientFirst ≠ ambientSecond := by
      intro h
      exact hne (coarseSub.embedding.injective h)
    simp only [wz2PaperDoubledFiberIndices, Finset.disjoint_left]
    intro source h1 h2
    have h1' :
        wz1PaperLineDistance
            (selected.family.tube source)
            (coarseSub.family.tube first) ≤ rho := by
      simpa [Finset.mem_filter, Finset.mem_univ, true_and] using h1
    have h2' :
        wz1PaperLineDistance
            (selected.family.tube source)
            (coarseSub.family.tube second) ≤ rho := by
      simpa [Finset.mem_filter, Finset.mem_univ, true_and] using h2
    have ambient_h1 :
        selected.embedding source ∈
          wz2PaperDoubledFiberIndices fine coarse ambientFirst := by
      simp only [wz2PaperDoubledFiberIndices, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [selected.tube_eq, coarseSub.tube_eq] at h1'
      exact h1'
    have ambient_h2 :
        selected.embedding source ∈
          wz2PaperDoubledFiberIndices fine coarse ambientSecond := by
      simp only [wz2PaperDoubledFiberIndices, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [selected.tube_eq, coarseSub.tube_eq] at h2'
      exact h2'
    exact
      Finset.disjoint_left.mp
        (cover.doubled_fibers_disjoint
          ambientFirst ambientSecond ambient_ne)
        ambient_h1 ambient_h2

lemma WZ2PaperPartitioningCover.restrict_parent_spec
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (retainedParents : Finset (Fin coarse.card))
    (hretained : retainedParents.Nonempty)
    (index :
      Fin
        (Kakeya.Streamlined.TubeSubfamily.fromFinset fine
          (Finset.univ.filter fun source =>
            cover.parent source ∈ retainedParents)).family.card) :
    (Kakeya.Streamlined.TubeSubfamily.fromFinset
        coarse retainedParents).embedding
      ((cover.restrict retainedParents hretained).parent index) =
    cover.parent
      ((Kakeya.Streamlined.TubeSubfamily.fromFinset fine
        (Finset.univ.filter fun source =>
          cover.parent source ∈ retainedParents)).embedding index) := by
  let selected :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset fine
      (Finset.univ.filter fun source =>
        cover.parent source ∈ retainedParents)
  let coarseSub :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset coarse retainedParents
  let restrictedCover := cover.restrict retainedParents hretained
  have hcov :
      WZ1PaperTubeCovers
        (fine.tube (selected.embedding index))
        (coarse.tube
          (coarseSub.embedding (restrictedCover.parent index))) := by
    have h := restrictedCover.parent_covers index
    rw [selected.tube_eq, coarseSub.tube_eq] at h
    exact h
  exact
    cover.parent_unique
      (selected.embedding index)
      (coarseSub.embedding (restrictedCover.parent index)) hcov

lemma paperShading_union_volume_le_mass
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) :
    MeasureTheory.volume shading.union ≤ shading.mass := by
  have h_eq :
      shading.union =
        ⋃ index : Fin family.card, shading.carrier index := by
    ext point
    simp [Kakeya.Streamlined.Shading.union]
    rfl
  rw [h_eq]
  exact
    MeasureTheory.measure_iUnion_fintype_le
      MeasureTheory.volume shading.carrier

lemma selected_fine_cells_disjoint_across_coarse
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    {retainedCoarseCells : Finset WZ2PaperCellIndex}
    {selectedFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    (hcontainment :
      ∀ coarseCell ∈ retainedCoarseCells,
        ∀ fineCell ∈ selectedFineCells coarseCell,
          wz1PaperGridCube delta fineCell ⊆
            wz1PaperGridCube rho coarseCell)
    {first second : WZ2PaperCellIndex}
    (first_mem : first ∈ retainedCoarseCells)
    (second_mem : second ∈ retainedCoarseCells)
    (hne : first ≠ second) :
    Disjoint (selectedFineCells first) (selectedFineCells second) := by
  rw [Finset.disjoint_left]
  intro fineCell first_fine second_fine
  have h1 :
      wz1PaperGridCube delta fineCell ⊆
        wz1PaperGridCube rho first :=
    hcontainment first first_mem fineCell first_fine
  have h2 :
      wz1PaperGridCube delta fineCell ⊆
        wz1PaperGridCube rho second :=
    hcontainment second second_mem fineCell second_fine
  have volume_pos :
      0 < volume (wz1PaperGridCube delta fineCell) :=
    wz1PaperGridCube_volume_pos hdelta fineCell
  have nonempty : (wz1PaperGridCube delta fineCell).Nonempty := by
    by_contra h
    have empty : wz1PaperGridCube delta fineCell = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp h
    rw [empty] at volume_pos
    simp at volume_pos
  rcases nonempty with ⟨point, point_mem⟩
  have point_first : point ∈ wz1PaperGridCube rho first :=
    h1 point_mem
  have point_second : point ∈ wz1PaperGridCube rho second :=
    h2 point_mem
  have first_eq_second : first = second := by
    have hfirst :
        wz1PaperGridIndex rho point = first :=
      (mem_wz1PaperGridCube rho first point).mp point_first
    have hsecond :
        wz1PaperGridIndex rho point = second :=
      (mem_wz1PaperGridCube rho second point).mp point_second
    exact hfirst.symm.trans hsecond
  exact hne first_eq_second

lemma selected_fine_cells_union_volume
    {delta : ℝ}
    (hdelta : 0 < delta)
    {retainedCells : Finset WZ2PaperCellIndex}
    {selectedOwnerFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {level : ℕ}
    (hcard :
      ∀ cell ∈ retainedCells,
        (selectedOwnerFineCells cell).card = 2 ^ level)
    (hdisj :
      ∀ first ∈ retainedCells,
        ∀ second ∈ retainedCells,
          first ≠ second →
            Disjoint
              (selectedOwnerFineCells first)
              (selectedOwnerFineCells second))
    (fiberCellMass : ENNReal)
    (fiberCellMass_eq :
      fiberCellMass =
        volume (wz1PaperGridCube delta (0, 0, 0))) :
    volume
        (⋃ cell ∈ retainedCells,
          ⋃ fineCell ∈ selectedOwnerFineCells cell,
            wz1PaperGridCube delta fineCell) =
      (retainedCells.card : ENNReal) *
        (2 ^ level : ENNReal) * fiberCellMass := by
  let allCells := retainedCells.biUnion selectedOwnerFineCells
  have cube_disjoint :
      Set.PairwiseDisjoint
        (↑allCells) (fun cell => wz1PaperGridCube delta cell) := by
    intro first _ second _ hne
    exact wz1PaperGridCube_disjoint hne
  have h_union :
      (⋃ cell ∈ retainedCells,
        ⋃ fineCell ∈ selectedOwnerFineCells cell,
          wz1PaperGridCube delta fineCell) =
        ⋃ fineCell ∈ allCells,
          wz1PaperGridCube delta fineCell := by
    ext point
    simp only [allCells, Finset.mem_biUnion, Set.mem_iUnion]
    aesop
  rw [h_union]
  have h_volume :
      volume
          (⋃ fineCell ∈ allCells,
            wz1PaperGridCube delta fineCell) =
        (allCells.card : ENNReal) *
          volume (wz1PaperGridCube delta (0, 0, 0)) :=
    wz1PaperGridCube_volume_biUnion hdelta allCells
  rw [h_volume]
  have all_card :
      allCells.card = retainedCells.card * 2 ^ level := by
    rw [Finset.card_biUnion hdisj]
    rw [Finset.sum_congr rfl hcard]
    simp
  rw [all_card, fiberCellMass_eq]
  simp [mul_assoc]

end Kakeya.Assouad

end
