import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.BranchingProfile
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingInduction
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.OSBranchingIntervalCellCountStatement

/-!
# Cubic-grid cells after restricting the point set

Occupied ambient cells are in bijection with the occupied cells of a
restricted point set, by intersecting each ambient cell with the restriction.
-/

noncomputable section

namespace Kakeya.Assouad

lemma cubicGridCell_inter_subset
    {base level : ℕ}
    {A A' : DiscreteSet 3}
    (hsub : A' ⊆ A)
    {p : Point 3}
    (hp : p ∈ A') :
    A' ∩ cubicGridCell base level A p =
      cubicGridCell base level A' p := by
  ext q
  simp only [cubicGridCell, Finset.mem_inter,
    Finset.mem_filter]
  constructor
  · rintro ⟨hq', _hqA, hindex⟩
    exact ⟨hq', hindex⟩
  · rintro ⟨hq', hindex⟩
    exact ⟨hq', hsub hq', hindex⟩

lemma cubicGridPartition_restrict_eq_image
    {base level : ℕ}
    {A A' : DiscreteSet 3}
    (hsub : A' ⊆ A) :
    cubicGridPartition base level A' =
      (occupiedPartitionCells A'
        (fun k => cubicGridPartition base k A)
        level).image
          (fun cell => A' ∩ cell) := by
  ext restrictedCell
  constructor
  · intro hrestricted
    rcases Finset.mem_image.mp hrestricted with
      ⟨p, hp', rfl⟩
    let ambientCell :=
      cubicGridCell base level A p
    have hambient :
        ambientCell ∈
          cubicGridPartition base level A :=
      Finset.mem_image.mpr
        ⟨p, hsub hp', rfl⟩
    have hinter_nonempty :
        (A' ∩ ambientCell).Nonempty := by
      refine ⟨p, Finset.mem_inter.mpr
        ⟨hp', ?_⟩⟩
      simp [ambientCell, cubicGridCell, hsub hp']
    have hoccupied :
        ambientCell ∈
          occupiedPartitionCells A'
            (fun k =>
              cubicGridPartition base k A)
            level :=
      Finset.mem_filter.mpr
        ⟨hambient, hinter_nonempty⟩
    refine Finset.mem_image.mpr
      ⟨ambientCell, hoccupied, ?_⟩
    dsimp only [ambientCell]
    exact cubicGridCell_inter_subset hsub hp'
  · intro himage
    rcases Finset.mem_image.mp himage with
      ⟨ambientCell, hoccupied, rfl⟩
    have hambient :
        ambientCell ∈
          cubicGridPartition base level A :=
      (Finset.mem_filter.mp hoccupied).1
    rcases
        (Finset.mem_filter.mp hoccupied).2 with
      ⟨p, hp_inter⟩
    have hp' := (Finset.mem_inter.mp hp_inter).1
    have hp_cell := (Finset.mem_inter.mp hp_inter).2
    have hcell_eq :
        ambientCell =
          cubicGridCell base level A p := by
      rcases Finset.mem_image.mp hambient with
        ⟨representative, hrepresentative, hrepr⟩
      rw [← hrepr] at hp_cell
      rw [← hrepr]
      have hp_index :=
        (Finset.mem_filter.mp hp_cell).2
      simp only [cubicGridCell, hp_index]
    rw [hcell_eq,
      cubicGridCell_inter_subset hsub hp']
    exact Finset.mem_image.mpr
      ⟨p, hp', rfl⟩

lemma cubicGridPartition_restrict_map_injective
    {base level : ℕ}
    {A A' : DiscreteSet 3}
    (hsub : A' ⊆ A) :
    Set.InjOn
      (fun cell : DiscreteSet 3 =>
        A' ∩ cell)
      (occupiedPartitionCells A'
        (fun k => cubicGridPartition base k A)
        level) := by
  intro first hfirst second hsecond heq
  have hfirst_cell :
      first ∈ cubicGridPartition base level A :=
    (Finset.mem_filter.mp hfirst).1
  have hsecond_cell :
      second ∈ cubicGridPartition base level A :=
    (Finset.mem_filter.mp hsecond).1
  rcases
      (Finset.mem_filter.mp hfirst).2 with
    ⟨p, hp_first⟩
  have hp_second :
      p ∈ A' ∩ second := by
    change p ∈ (fun cell => A' ∩ cell) second
    rw [← heq]
    exact hp_first
  have hp_first_cell :=
    (Finset.mem_inter.mp hp_first).2
  have hp_second_cell :=
    (Finset.mem_inter.mp hp_second).2
  by_contra hne
  have hdisjoint :
      Disjoint first second :=
    cubicGridPartition_disjoint
      hfirst_cell hsecond_cell hne
  exact
    (Finset.disjoint_left.mp hdisjoint)
      hp_first_cell hp_second_cell

lemma cellCount_restrict_eq_occupied
    {base level : ℕ}
    {A A' : DiscreteSet 3}
    (hsub : A' ⊆ A) :
    cellCount base A' level =
      (occupiedPartitionCells A'
        (fun k => cubicGridPartition base k A)
        level).card := by
  rw [cellCount,
    cubicGridPartition_restrict_eq_image hsub,
    Finset.card_image_of_injOn
      (cubicGridPartition_restrict_map_injective
        hsub)]

lemma occupiedPartitionCells_sum_inter_card
    {base level : ℕ}
    {A A' : DiscreteSet 3}
    (hsub : A' ⊆ A) :
    ∑ cell ∈ occupiedPartitionCells A'
        (fun k => cubicGridPartition base k A) level,
        (A' ∩ cell).card =
      A'.card := by
  have hpartition :=
    cubicGridPartition_restrict_eq_image
      (base := base) (level := level) hsub
  have hinjective :=
    cubicGridPartition_restrict_map_injective
      (base := base) (level := level) hsub
  have hsum :=
    cubicGridPartition_sum_card
      (base := base) (level := level) (A := A')
  rw [hpartition] at hsum
  rw [Finset.sum_image] at hsum
  · exact hsum
  · intro first hfirst second hsecond heq
    exact hinjective hfirst hsecond heq

lemma cubicGridPartition_inter_parent_eq_image_descendants
    {base coarseLevel fineLevel : ℕ}
    {A A' : DiscreteSet 3}
    (hbase : 2 ≤ base)
    (hsub : A' ⊆ A)
    (hcoarse_fine : coarseLevel ≤ fineLevel)
    {parent : DiscreteSet 3}
    (hparent :
      parent ∈ cubicGridPartition base coarseLevel A)
    (hparent_occupied :
      (A' ∩ parent).Nonempty) :
    cubicGridPartition base fineLevel (A' ∩ parent) =
      (((occupiedPartitionCells A'
          (fun level =>
            cubicGridPartition base level A)
          fineLevel).filter
        fun child => child ⊆ parent).image
          fun child => A' ∩ child) := by
  let partition : ℕ → Finset (DiscreteSet 3) :=
    fun level => cubicGridPartition base level A
  have hchild_parent :
      ∀ level, level < fineLevel →
        ∀ child ∈ partition (level + 1),
          ∃ ancestor ∈ partition level,
            child ⊆ ancestor := by
    intro level _ child hchild
    exact cubicGridPartition_nesting
      (show 1 ≤ base by omega) hchild
  have hancestor :
      ∀ child ∈ partition fineLevel,
        ∃ ancestor ∈ partition coarseLevel,
          child ⊆ ancestor :=
    os_branching_find_ancestor
      partition fineLevel hchild_parent
      hcoarse_fine le_rfl
  have child_subset_parent :
      ∀ {p : Point 3},
        p ∈ A' →
        p ∈ parent →
        cubicGridCell base fineLevel A p ⊆ parent := by
    intro p hp' hp_parent
    have hpA := hsub hp'
    have hchild :
        cubicGridCell base fineLevel A p ∈
          partition fineLevel :=
      Finset.mem_image.mpr ⟨p, hpA, rfl⟩
    rcases hancestor
        (cubicGridCell base fineLevel A p)
        hchild with
      ⟨ancestor, hancestor_mem, hchild_sub⟩
    have hp_child :
        p ∈ cubicGridCell base fineLevel A p := by
      simp [cubicGridCell, hpA]
    have hp_ancestor := hchild_sub hp_child
    have hancestor_eq : ancestor = parent := by
      by_contra hne
      have hdisjoint :=
        cubicGridPartition_disjoint
          hancestor_mem hparent hne
      exact (Finset.disjoint_left.mp hdisjoint)
        hp_ancestor hp_parent
    rwa [hancestor_eq] at hchild_sub
  have intersection_eq_cell :
      ∀ {p : Point 3},
        p ∈ A' →
        p ∈ parent →
        A' ∩ cubicGridCell base fineLevel A p =
          cubicGridCell base fineLevel
            (A' ∩ parent) p := by
    intro p hp' hp_parent
    have hchild_sub :=
      child_subset_parent hp' hp_parent
    ext q
    simp only [cubicGridCell,
      Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨hq', hqA, hindex⟩
      exact ⟨⟨hq', hchild_sub
        (Finset.mem_filter.mpr ⟨hqA, hindex⟩)⟩,
        hindex⟩
    · rintro ⟨⟨hq', hq_parent⟩, hindex⟩
      exact ⟨hq', hsub hq', hindex⟩
  ext localCell
  constructor
  · intro hlocal
    rcases Finset.mem_image.mp hlocal with
      ⟨p, hp, rfl⟩
    have hp' := (Finset.mem_inter.mp hp).1
    have hp_parent := (Finset.mem_inter.mp hp).2
    let child := cubicGridCell base fineLevel A p
    have hchild_mem :
        child ∈ partition fineLevel :=
      Finset.mem_image.mpr
        ⟨p, hsub hp', rfl⟩
    have hchild_occupied :
        child ∈ occupiedPartitionCells
          A' partition fineLevel := by
      exact Finset.mem_filter.mpr
        ⟨hchild_mem, ⟨p,
          Finset.mem_inter.mpr
            ⟨hp', by
              simp [child, cubicGridCell, hsub hp']⟩⟩⟩
    have hchild_sub :
        child ⊆ parent :=
      child_subset_parent hp' hp_parent
    refine Finset.mem_image.mpr
      ⟨child,
        Finset.mem_filter.mpr
          ⟨hchild_occupied, hchild_sub⟩,
        ?_⟩
    dsimp only [child]
    exact intersection_eq_cell hp' hp_parent
  · intro himage
    rcases Finset.mem_image.mp himage with
      ⟨child, hchild, rfl⟩
    have hchild_occupied :=
      (Finset.mem_filter.mp hchild).1
    have hchild_sub :=
      (Finset.mem_filter.mp hchild).2
    rcases (Finset.mem_filter.mp
        hchild_occupied).2 with
      ⟨p, hp⟩
    have hp' := (Finset.mem_inter.mp hp).1
    have hp_child := (Finset.mem_inter.mp hp).2
    have hp_parent := hchild_sub hp_child
    have hchild_partition :=
      (Finset.mem_filter.mp hchild_occupied).1
    have hchild_eq :
        child = cubicGridCell base fineLevel A p := by
      rcases Finset.mem_image.mp hchild_partition with
        ⟨representative, hrepresentative, hrefl⟩
      rw [← hrefl] at hp_child
      rw [← hrefl]
      have hindex :=
        (Finset.mem_filter.mp hp_child).2
      simp only [cubicGridCell, hindex]
    rw [hchild_eq,
      intersection_eq_cell hp' hp_parent]
    exact Finset.mem_image.mpr
      ⟨p, Finset.mem_inter.mpr
        ⟨hp', hp_parent⟩, rfl⟩

lemma cellCount_inter_parent_eq_descendants
    {base coarseLevel fineLevel : ℕ}
    {A A' : DiscreteSet 3}
    (hbase : 2 ≤ base)
    (hsub : A' ⊆ A)
    (hcoarse_fine : coarseLevel ≤ fineLevel)
    {parent : DiscreteSet 3}
    (hparent :
      parent ∈ cubicGridPartition base coarseLevel A)
    (hparent_occupied :
      (A' ∩ parent).Nonempty) :
    cellCount base (A' ∩ parent) fineLevel =
      ((occupiedPartitionCells A'
          (fun level =>
            cubicGridPartition base level A)
          fineLevel).filter
        fun child => child ⊆ parent).card := by
  rw [cellCount,
    cubicGridPartition_inter_parent_eq_image_descendants
      hbase hsub hcoarse_fine hparent
      hparent_occupied]
  apply Finset.card_image_of_injOn
  intro first hfirst second hsecond heq
  have hfirst_occupied :=
    (Finset.mem_filter.mp hfirst).1
  have hsecond_occupied :=
    (Finset.mem_filter.mp hsecond).1
  have hfirst_mem :=
    (Finset.mem_filter.mp hfirst_occupied).1
  have hsecond_mem :=
    (Finset.mem_filter.mp hsecond_occupied).1
  have hfirst_nonempty :=
    (Finset.mem_filter.mp hfirst_occupied).2
  rcases hfirst_nonempty with ⟨p, hp⟩
  have hp_second :
      p ∈ A' ∩ second := by
    change p ∈ (fun child => A' ∩ child) second
    rw [← heq]
    exact hp
  have hp_first := (Finset.mem_inter.mp hp).2
  have hp_second' := (Finset.mem_inter.mp hp_second).2
  by_contra hne
  have hdisjoint :=
    cubicGridPartition_disjoint
      hfirst_mem hsecond_mem hne
  exact (Finset.disjoint_left.mp hdisjoint)
    hp_first hp_second'

end Kakeya.Assouad
