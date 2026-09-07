import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TreeCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.FinitePureNearbyAssembly
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureHitParentRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureFiberRestriction

/-!
# Proposition 6.2 one-pass tree cleanup: literal pure schedule

This connects the finite tree cleanup in `WZ2_prop62.tex` to the literal
ordinary full-fiber covers of Assouad Definition 2.12.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62PureSchedule
    {delta : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (ambientConstant scaleWindow : ENNReal) where
  ambient_finite :
    WZ2PaperFiniteErrorConstant ambientConstant
  scaleWindow_finite :
    WZ2PaperFiniteErrorConstant scaleWindow
  fine_distinct :
    WZ2PaperOrdinaryIsEssentiallyDistinct fine
  levelCount : ℕ
  levelCount_pos : 0 < levelCount
  actualScale : Fin levelCount → ℝ
  delta_le_actualScale :
    ∀ coordinate, delta ≤ actualScale coordinate
  actualScale_antitone :
    ∀ first second : Fin levelCount,
      first.val ≤ second.val →
        actualScale second ≤ actualScale first
  scaleData :
    ∀ coordinate,
      WZ2PaperPureScaleCoverData
        fine (actualScale coordinate) ambientConstant
  coarse_line_class :
    ∀ coordinate,
      WZ1PaperIsLineClass (scaleData coordinate).coarse
  parent_covers :
    ∀ coordinate source,
      WZ1PaperTubeCovers
        (fine.tube source)
        ((scaleData coordinate).coarse.tube
          ((scaleData coordinate).cover.parent source))
  parent_nested :
    ∀ level,
      ∀ hnext : level + 1 < levelCount,
        ∀ first second : Fin fine.card,
          (scaleData ⟨level + 1, hnext⟩).cover.parent first =
              (scaleData ⟨level + 1, hnext⟩).cover.parent second →
            (scaleData
                ⟨level, Nat.lt_of_succ_lt hnext⟩).cover.parent first =
              (scaleData
                ⟨level, Nat.lt_of_succ_lt hnext⟩).cover.parent second
  rounding :
    ∀ requested : WZ2PaperRequestedScale delta,
      ∃ coordinate : Fin levelCount,
        requested.1 ≤ actualScale coordinate ∧
          ENNReal.ofReal (actualScale coordinate) <
            scaleWindow * ENNReal.ofReal requested.1

namespace PureWZ2Prop62PureSchedule

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow)

abbrev Leaf := Fin fine.card

abbrev Node := Finset (Fin fine.card)

def coordinateAt (level : ℕ) : Fin schedule.levelCount :=
  if hlevel : level < schedule.levelCount then
    ⟨level, hlevel⟩
  else
    ⟨0, schedule.levelCount_pos⟩

@[simp] theorem coordinateAt_eq
    {level : ℕ}
    (hlevel : level < schedule.levelCount) :
    schedule.coordinateAt level = ⟨level, hlevel⟩ := by
  simp [coordinateAt, hlevel]

def nodeAt (level : ℕ) (leaf : Fin fine.card) :
    Finset (Fin fine.card) :=
  if level = 0 then
    Finset.univ
  else
    let coordinate := schedule.coordinateAt (level - 1)
    Finset.univ.filter fun source =>
      (schedule.scaleData coordinate).cover.parent source =
        (schedule.scaleData coordinate).cover.parent leaf

@[simp] theorem nodeAt_zero
    (leaf : Fin fine.card) :
    schedule.nodeAt 0 leaf = Finset.univ := by
  simp [nodeAt]

theorem nodeAt_succ
    {level : ℕ}
    (hlevel : level < schedule.levelCount)
    (leaf : Fin fine.card) :
    schedule.nodeAt (level + 1) leaf =
      Finset.univ.filter fun source =>
        (schedule.scaleData ⟨level, hlevel⟩).cover.parent source =
          (schedule.scaleData ⟨level, hlevel⟩).cover.parent leaf := by
  unfold nodeAt
  rw [if_neg (Nat.succ_ne_zero level)]
  simp only [Nat.add_sub_cancel]
  change
    Finset.univ.filter (fun source =>
      (schedule.scaleData (schedule.coordinateAt level)).cover.parent source =
        (schedule.scaleData (schedule.coordinateAt level)).cover.parent leaf) =
      Finset.univ.filter fun source =>
        (schedule.scaleData ⟨level, hlevel⟩).cover.parent source =
          (schedule.scaleData ⟨level, hlevel⟩).cover.parent leaf
  rw [schedule.coordinateAt_eq hlevel]

def tree :
    PureWZ2Prop62FiniteTree
      (Fin fine.card) (Finset (Fin fine.card))
      schedule.levelCount where
  nodeAt := schedule.nodeAt
  root_constant first second := by
    simp
  nested level hlevel first second heq := by
    by_cases hzero : level = 0
    · subst level
      simp
    · obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      have hnext :
          previous + 1 < schedule.levelCount := by
        omega
      have hcurrent :
          previous < schedule.levelCount := by
        omega
      have hfirstMem :
          first ∈ schedule.nodeAt (previous + 2) first := by
        rw [schedule.nodeAt_succ hnext]
        simp
      rw [heq] at hfirstMem
      have hparentNext :
          (schedule.scaleData
              ⟨previous + 1, hnext⟩).cover.parent first =
            (schedule.scaleData
              ⟨previous + 1, hnext⟩).cover.parent second := by
        simpa only [schedule.nodeAt_succ hnext,
          Finset.mem_filter, Finset.mem_univ, true_and] using hfirstMem
      have hparentCurrent :=
        schedule.parent_nested previous hnext first second hparentNext
      rw [schedule.nodeAt_succ hcurrent,
        schedule.nodeAt_succ hcurrent]
      ext source
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hparentCurrent]

theorem nodeAt_coordinate_eq_fullFiber
    (coordinate : Fin schedule.levelCount)
    (leaf : Fin fine.card) :
    schedule.nodeAt (coordinate.1 + 1) leaf =
      wz2PaperOrdinaryFullFiberIndices
        fine
        (schedule.scaleData coordinate).coarse
        ((schedule.scaleData coordinate).cover.parent leaf) := by
  rw [schedule.nodeAt_succ coordinate.2]
  ext source
  rw [
    (schedule.scaleData coordinate).cover.mem_fullFiber_iff_parent_eq
      (schedule.scaleData coordinate).rho_pos.le
  ]
  simp

theorem tree_fiber_coordinate_nodeAt_eq_fullFiber
    (coordinate : Fin schedule.levelCount)
    (leaf : Fin fine.card) :
    (tree (schedule := schedule)).fiber
        (coordinate.1 + 1)
        (schedule.nodeAt (coordinate.1 + 1) leaf) =
      wz2PaperOrdinaryFullFiberIndices
        fine
        (schedule.scaleData coordinate).coarse
        ((schedule.scaleData coordinate).cover.parent leaf) := by
  ext source
  constructor
  · intro hsource
    have hnode :
        schedule.nodeAt (coordinate.1 + 1) source =
          schedule.nodeAt (coordinate.1 + 1) leaf :=
      (Finset.mem_filter.mp hsource).2
    change
      schedule.nodeAt (coordinate.1 + 1) source =
        schedule.nodeAt (coordinate.1 + 1) leaf at hnode
    have hsourceOwn :
        source ∈
          wz2PaperOrdinaryFullFiberIndices
            fine
            (schedule.scaleData coordinate).coarse
            ((schedule.scaleData coordinate).cover.parent source) :=
      (schedule.scaleData coordinate).cover.parent_mem_fullFiber source
    rw [
      ← schedule.nodeAt_coordinate_eq_fullFiber coordinate source,
      hnode,
      schedule.nodeAt_coordinate_eq_fullFiber coordinate leaf
    ] at hsourceOwn
    exact hsourceOwn
  · intro hsource
    have hparent :
        (schedule.scaleData coordinate).cover.parent source =
          (schedule.scaleData coordinate).cover.parent leaf :=
      ((schedule.scaleData coordinate).cover.mem_fullFiber_iff_parent_eq
        (schedule.scaleData coordinate).rho_pos.le
        ((schedule.scaleData coordinate).cover.parent leaf)
        source).mp hsource
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ source, ?_⟩
    change
      schedule.nodeAt (coordinate.1 + 1) source =
        schedule.nodeAt (coordinate.1 + 1) leaf
    rw [schedule.nodeAt_succ coordinate.2,
      schedule.nodeAt_succ coordinate.2]
    ext candidate
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hparent]

/--
Parent equality at a finer schedule coordinate forces parent equality at
every earlier coordinate of the same simultaneous laminar schedule.
-/
theorem parent_eq_of_coordinate_le
    (coarse fineCoordinate : Fin schedule.levelCount)
    (coordinateLe : coarse.1 ≤ fineCoordinate.1)
    (first second : Fin fine.card)
    (fineParentEq :
      (schedule.scaleData fineCoordinate).cover.parent first =
        (schedule.scaleData fineCoordinate).cover.parent second) :
    (schedule.scaleData coarse).cover.parent first =
      (schedule.scaleData coarse).cover.parent second := by
  have fineNodeEq :
      schedule.nodeAt (fineCoordinate.1 + 1) first =
        schedule.nodeAt (fineCoordinate.1 + 1) second := by
    rw [schedule.nodeAt_succ fineCoordinate.2,
      schedule.nodeAt_succ fineCoordinate.2]
    ext source
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [fineParentEq]
  have fineTreeNodeEq :
      schedule.tree.nodeAt (fineCoordinate.1 + 1) first =
        schedule.tree.nodeAt (fineCoordinate.1 + 1) second := by
    exact fineNodeEq
  have coarseNodeEq :
      schedule.nodeAt (coarse.1 + 1) first =
        schedule.nodeAt (coarse.1 + 1) second := by
    have treeNodeEq :=
      schedule.tree.node_eq_of_le
        (coarse := coarse.1 + 1)
        (fine := fineCoordinate.1 + 1)
        (first := first)
        (second := second)
        (by omega)
        (by omega)
        fineTreeNodeEq
    exact treeNodeEq
  rw [schedule.nodeAt_succ coarse.2,
    schedule.nodeAt_succ coarse.2] at coarseNodeEq
  have firstMem :
      first ∈
        Finset.univ.filter fun source =>
          (schedule.scaleData coarse).cover.parent source =
            (schedule.scaleData coarse).cover.parent first := by
    simp
  rw [coarseNodeEq] at firstMem
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using firstMem

def coreIndices (selected : Finset (Fin fine.card)) :
    Finset (Fin fine.card) :=
  ((tree (schedule := schedule)).coreOutput selected).core

def coreFine (selected : Finset (Fin fine.card)) :
    WZ2PaperPureTubeSubfamily fine :=
  WZ2PaperPureTubeSubfamily.fromFinset fine
    (coreIndices (schedule := schedule) selected)

def coreCoarse
    (coordinate : Fin schedule.levelCount)
    (selected : Finset (Fin fine.card)) :
    WZ2PaperPureTubeSubfamily
      (schedule.scaleData coordinate).coarse :=
  (schedule.scaleData coordinate).cover.hitParentSubfamily
    (coreFine (schedule := schedule) selected)

def coreCover
    (coordinate : Fin schedule.levelCount)
    (selected : Finset (Fin fine.card)) :
    WZ2PaperPurePartitioningCover
      (coreFine (schedule := schedule) selected).family
      (coreCoarse (schedule := schedule) coordinate selected).family :=
  (schedule.scaleData coordinate).cover.restrictToHitParents
    (coreFine (schedule := schedule) selected)

def densityLoss
    (selected : Finset (Fin fine.card)) : ENNReal :=
  (2 ^ schedule.levelCount : ENNReal) *
    fine.enncard *
    (selected.card : ENNReal)⁻¹

def onePassConstant
    (selected : Finset (Fin fine.card)) : ENNReal :=
  ambientConstant * schedule.densityLoss selected

def outputConstant
    (selected : Finset (Fin fine.card)) : ENNReal :=
  max scaleWindow (schedule.onePassConstant selected)

theorem coreIndices_subset
    (selected : Finset (Fin fine.card)) :
    coreIndices (schedule := schedule) selected ⊆ selected :=
  ((tree (schedule := schedule)).coreOutput selected).core_subset

theorem selected_card_le_core
    (selected : Finset (Fin fine.card)) :
    selected.card ≤
      2 ^ schedule.levelCount *
        (coreIndices (schedule := schedule) selected).card :=
  ((tree (schedule := schedule)).coreOutput selected).global_retention

theorem coreIndices_nonempty
    {selected : Finset (Fin fine.card)}
    (hselected : selected.Nonempty) :
    (coreIndices (schedule := schedule) selected).Nonempty := by
  apply Finset.card_pos.mp
  have hselectedPos : 0 < selected.card :=
    Finset.card_pos.mpr hselected
  have hretention :=
    selected_card_le_core (schedule := schedule) selected
  by_contra hcore
  have hcoreZero :
      (coreIndices (schedule := schedule) selected).card = 0 :=
    Nat.eq_zero_of_not_pos hcore
  rw [hcoreZero, mul_zero] at hretention
  omega

theorem coreFine_nonempty
    {selected : Finset (Fin fine.card)}
    (hselected : selected.Nonempty) :
    (coreFine (schedule := schedule) selected).family.Nonempty := by
  change 0 < (coreIndices (schedule := schedule) selected).card
  exact Finset.card_pos.mpr
    (coreIndices_nonempty (schedule := schedule) hselected)

theorem coreFine_image_univ
    (selected : Finset (Fin fine.card)) :
    Finset.image
        (coreFine (schedule := schedule) selected).embedding
        Finset.univ =
      coreIndices (schedule := schedule) selected := by
  ext source
  constructor
  · intro hsource
    rcases Finset.mem_image.mp hsource with
      ⟨index, _hindex, rfl⟩
    exact
      Finset.orderEmbOfFin_mem
        (coreIndices (schedule := schedule) selected) rfl index
  · intro hsource
    let equivalence :
        Fin (coreIndices (schedule := schedule) selected).card ≃
          coreIndices (schedule := schedule) selected :=
      (coreIndices (schedule := schedule) selected).orderIsoOfFin rfl
        |>.toEquiv
    refine Finset.mem_image.mpr
      ⟨equivalence.symm ⟨source, hsource⟩,
        Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val
      (equivalence.apply_symm_apply ⟨source, hsource⟩)

theorem core_fullFiber_image_eq_inter
    (coordinate : Fin schedule.levelCount)
    (selected : Finset (Fin fine.card))
    (parent :
      Fin
        (coreCoarse
          (schedule := schedule) coordinate selected).family.card) :
    Finset.image
        (coreFine (schedule := schedule) selected).embedding
        (wz2PaperOrdinaryFullFiberIndices
          (coreFine (schedule := schedule) selected).family
          (coreCoarse
            (schedule := schedule) coordinate selected).family
          parent) =
      coreIndices (schedule := schedule) selected ∩
        wz2PaperOrdinaryFullFiberIndices
          fine
          (schedule.scaleData coordinate).coarse
          ((coreCoarse
            (schedule := schedule) coordinate selected).embedding
              parent) := by
  rw [wz2_paper_selected_fullFiber_image]
  ext source
  simp only [
    wz2PaperSelectedAmbientFullFiberIndices,
    Finset.mem_filter,
    Finset.mem_univ,
    true_and,
    Finset.mem_inter
  ]
  rw [coreFine_image_univ (schedule := schedule) selected]

theorem core_fullFiber_card_eq_inter
    (coordinate : Fin schedule.levelCount)
    (selected : Finset (Fin fine.card))
    (parent :
      Fin
        (coreCoarse
          (schedule := schedule) coordinate selected).family.card) :
    (wz2PaperOrdinaryFullFiberIndices
        (coreFine (schedule := schedule) selected).family
        (coreCoarse
          (schedule := schedule) coordinate selected).family
        parent).card =
      (coreIndices (schedule := schedule) selected ∩
        wz2PaperOrdinaryFullFiberIndices
          fine
          (schedule.scaleData coordinate).coarse
          ((coreCoarse
            (schedule := schedule) coordinate selected).embedding
              parent)).card := by
  rw [← core_fullFiber_image_eq_inter
    (schedule := schedule) coordinate selected parent]
  exact
    (Finset.card_image_of_injective _
      (coreFine
        (schedule := schedule) selected).embedding.injective).symm

theorem core_parent_has_leaf
    (coordinate : Fin schedule.levelCount)
    (selected : Finset (Fin fine.card))
    (parent :
      Fin
        (coreCoarse
          (schedule := schedule) coordinate selected).family.card) :
    ∃ leaf ∈ coreIndices (schedule := schedule) selected,
      (schedule.scaleData coordinate).cover.parent leaf =
        (coreCoarse
          (schedule := schedule) coordinate selected).embedding parent := by
  rcases
      (schedule.scaleData coordinate).cover.hitParent_surjective
        (coreFine (schedule := schedule) selected) parent with
    ⟨source, hsource⟩
  let leaf :=
    (coreFine (schedule := schedule) selected).embedding source
  have hleaf :
      leaf ∈ coreIndices (schedule := schedule) selected := by
    rw [← coreFine_image_univ (schedule := schedule) selected]
    exact Finset.mem_image.mpr
      ⟨source, Finset.mem_univ source, rfl⟩
  refine ⟨leaf, hleaf, ?_⟩
  change
    (schedule.scaleData coordinate).cover.parent leaf =
      ((schedule.scaleData coordinate).cover.hitParentSubfamily
        (coreFine
          (schedule := schedule) selected)).embedding parent
  rw [
    ← (schedule.scaleData coordinate).cover.hitParent_ambient
      (coreFine (schedule := schedule) selected) source,
    hsource
  ]

theorem core_fullFiber_card_eq_tree_inter
    (coordinate : Fin schedule.levelCount)
    (selected : Finset (Fin fine.card))
    (parent :
      Fin
        (coreCoarse
          (schedule := schedule) coordinate selected).family.card) :
    ∃ leaf ∈ coreIndices (schedule := schedule) selected,
      (schedule.scaleData coordinate).cover.parent leaf =
          (coreCoarse
            (schedule := schedule) coordinate selected).embedding parent ∧
        (wz2PaperOrdinaryFullFiberIndices
            (coreFine (schedule := schedule) selected).family
            (coreCoarse
              (schedule := schedule) coordinate selected).family
            parent).card =
          (coreIndices (schedule := schedule) selected ∩
            (tree (schedule := schedule)).fiber
              (coordinate.1 + 1)
              (schedule.nodeAt (coordinate.1 + 1) leaf)).card := by
  rcases core_parent_has_leaf
      (schedule := schedule) coordinate selected parent with
    ⟨leaf, hleaf, hparent⟩
  refine ⟨leaf, hleaf, hparent, ?_⟩
  rw [core_fullFiber_card_eq_inter
    (schedule := schedule) coordinate selected parent]
  rw [← hparent]
  rw [tree_fiber_coordinate_nodeAt_eq_fullFiber
    (schedule := schedule) coordinate leaf]

theorem core_fullFiber_count_le_ambient
    (coordinate : Fin schedule.levelCount)
    (selected : Finset (Fin fine.card))
    (parent :
      Fin
        (coreCoarse
          (schedule := schedule) coordinate selected).family.card) :
    wz2PaperOrdinaryFullFiberCount
        (coreFine (schedule := schedule) selected).family
        (coreCoarse
          (schedule := schedule) coordinate selected).family
        parent ≤
      wz2PaperOrdinaryFullFiberCount
        fine
        (schedule.scaleData coordinate).coarse
        ((coreCoarse
          (schedule := schedule) coordinate selected).embedding
            parent) := by
  rw [wz2PaperOrdinaryFullFiberCount,
    wz2PaperOrdinaryFullFiberCount,
    core_fullFiber_card_eq_inter
      (schedule := schedule) coordinate selected parent]
  exact_mod_cast
    Finset.card_le_card (Finset.inter_subset_right)

theorem ambient_fullFiber_count_le_densityLoss_core
    (coordinate : Fin schedule.levelCount)
    {selected : Finset (Fin fine.card)}
    (hselected : selected.Nonempty)
    (parent :
      Fin
        (coreCoarse
          (schedule := schedule) coordinate selected).family.card) :
    wz2PaperOrdinaryFullFiberCount
        fine
        (schedule.scaleData coordinate).coarse
        ((coreCoarse
          (schedule := schedule) coordinate selected).embedding
            parent) ≤
      schedule.densityLoss selected *
        wz2PaperOrdinaryFullFiberCount
          (coreFine (schedule := schedule) selected).family
          (coreCoarse
            (schedule := schedule) coordinate selected).family
          parent := by
  rcases core_fullFiber_card_eq_tree_inter
      (schedule := schedule) coordinate selected parent with
    ⟨leaf, hleafCore, hparent, hcard⟩
  have hleafFiber :
      leaf ∈
        (tree (schedule := schedule)).fiber
          (coordinate.1 + 1)
          (schedule.nodeAt (coordinate.1 + 1) leaf) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ leaf, ?_⟩
    rfl
  have hnonempty :
      (coreIndices (schedule := schedule) selected ∩
        (tree (schedule := schedule)).fiber
          (coordinate.1 + 1)
          (schedule.nodeAt (coordinate.1 + 1) leaf)).Nonempty :=
    Finset.nonempty_def.mpr
      ⟨leaf, Finset.mem_inter.mpr ⟨hleafCore, hleafFiber⟩⟩
  have hlevel :
      coordinate.1 + 1 ≤ schedule.levelCount := by
    omega
  have hdensityNat :=
    ((tree (schedule := schedule)).coreOutput selected).node_density
      (coordinate.1 + 1) hlevel
      (schedule.nodeAt (coordinate.1 + 1) leaf) hnonempty
  have hdensityNat' :
      selected.card *
          ((tree (schedule := schedule)).fiber
            (coordinate.1 + 1)
            (schedule.nodeAt (coordinate.1 + 1) leaf)).card ≤
        2 ^ schedule.levelCount *
          (coreIndices (schedule := schedule) selected ∩
            (tree (schedule := schedule)).fiber
              (coordinate.1 + 1)
              (schedule.nodeAt
                (coordinate.1 + 1) leaf)).card *
          fine.card := by
    simpa only [coreIndices, Fintype.card_fin] using hdensityNat
  have hdensity :
      (selected.card : ENNReal) *
          (((tree (schedule := schedule)).fiber
            (coordinate.1 + 1)
            (schedule.nodeAt (coordinate.1 + 1) leaf)).card :
            ENNReal) ≤
        (2 ^ schedule.levelCount : ENNReal) *
          ((coreIndices (schedule := schedule) selected ∩
            (tree (schedule := schedule)).fiber
              (coordinate.1 + 1)
              (schedule.nodeAt
                (coordinate.1 + 1) leaf)).card : ENNReal) *
          fine.enncard := by
    change
      (selected.card : ENNReal) *
          (((tree (schedule := schedule)).fiber
            (coordinate.1 + 1)
            (schedule.nodeAt (coordinate.1 + 1) leaf)).card :
            ENNReal) ≤
        (2 ^ schedule.levelCount : ENNReal) *
          ((coreIndices (schedule := schedule) selected ∩
            (tree (schedule := schedule)).fiber
              (coordinate.1 + 1)
              (schedule.nodeAt
                (coordinate.1 + 1) leaf)).card : ENNReal) *
          (fine.card : ENNReal)
    exact_mod_cast hdensityNat'
  have hselectedPos : 0 < (selected.card : ENNReal) := by
    exact_mod_cast Finset.card_pos.mpr hselected
  have hselectedTop : (selected.card : ENNReal) ≠ ⊤ := by
    simp
  have hbound :
      (((tree (schedule := schedule)).fiber
        (coordinate.1 + 1)
        (schedule.nodeAt (coordinate.1 + 1) leaf)).card :
        ENNReal) ≤
        schedule.densityLoss selected *
          ((coreIndices (schedule := schedule) selected ∩
            (tree (schedule := schedule)).fiber
              (coordinate.1 + 1)
              (schedule.nodeAt
                (coordinate.1 + 1) leaf)).card : ENNReal) := by
    calc
      (((tree (schedule := schedule)).fiber
          (coordinate.1 + 1)
          (schedule.nodeAt (coordinate.1 + 1) leaf)).card :
          ENNReal) =
          ((selected.card : ENNReal) *
            (selected.card : ENNReal)⁻¹) *
              (((tree (schedule := schedule)).fiber
                (coordinate.1 + 1)
                (schedule.nodeAt
                  (coordinate.1 + 1) leaf)).card : ENNReal) := by
        rw [ENNReal.mul_inv_cancel hselectedPos.ne' hselectedTop]
        simp
      _ =
          ((selected.card : ENNReal) *
              (((tree (schedule := schedule)).fiber
                (coordinate.1 + 1)
                (schedule.nodeAt
                  (coordinate.1 + 1) leaf)).card : ENNReal)) *
            (selected.card : ENNReal)⁻¹ := by
        ring
      _ ≤
          ((2 ^ schedule.levelCount : ENNReal) *
              ((coreIndices (schedule := schedule) selected ∩
                (tree (schedule := schedule)).fiber
                  (coordinate.1 + 1)
                  (schedule.nodeAt
                    (coordinate.1 + 1) leaf)).card : ENNReal) *
              fine.enncard) *
            (selected.card : ENNReal)⁻¹ := by
        gcongr
      _ =
          schedule.densityLoss selected *
            ((coreIndices (schedule := schedule) selected ∩
              (tree (schedule := schedule)).fiber
                (coordinate.1 + 1)
                (schedule.nodeAt
                  (coordinate.1 + 1) leaf)).card : ENNReal) := by
        simp only [densityLoss]
        ring
  rw [wz2PaperOrdinaryFullFiberCount,
    wz2PaperOrdinaryFullFiberCount]
  rw [← hparent]
  rw [← tree_fiber_coordinate_nodeAt_eq_fullFiber
    (schedule := schedule) coordinate leaf]
  rw [hcard]
  exact hbound

theorem core_fullFiber_uniform
    (coordinate : Fin schedule.levelCount)
    {selected : Finset (Fin fine.card)}
    (hselected : selected.Nonempty) :
    WZ2PaperPureFullFibersAreCUniform
      (coreFine (schedule := schedule) selected).family
      (coreCoarse
        (schedule := schedule) coordinate selected).family
      (schedule.onePassConstant selected) := by
  intro first second
  calc
    wz2PaperOrdinaryFullFiberCount
        (coreFine (schedule := schedule) selected).family
        (coreCoarse
          (schedule := schedule) coordinate selected).family
        first ≤
      wz2PaperOrdinaryFullFiberCount
        fine
        (schedule.scaleData coordinate).coarse
        ((coreCoarse
          (schedule := schedule) coordinate selected).embedding
            first) :=
      core_fullFiber_count_le_ambient
        (schedule := schedule) coordinate selected first
    _ ≤
      ambientConstant *
        wz2PaperOrdinaryFullFiberCount
          fine
          (schedule.scaleData coordinate).coarse
          ((coreCoarse
            (schedule := schedule) coordinate selected).embedding
              second) :=
      schedule.scaleData coordinate |>.full_fiber_uniform
        ((coreCoarse
          (schedule := schedule) coordinate selected).embedding first)
        ((coreCoarse
          (schedule := schedule) coordinate selected).embedding second)
    _ ≤
      ambientConstant *
        (schedule.densityLoss selected *
          wz2PaperOrdinaryFullFiberCount
            (coreFine (schedule := schedule) selected).family
            (coreCoarse
              (schedule := schedule) coordinate selected).family
            second) := by
      gcongr
      exact ambient_fullFiber_count_le_densityLoss_core
        (schedule := schedule) coordinate hselected second
    _ =
      schedule.onePassConstant selected *
        wz2PaperOrdinaryFullFiberCount
          (coreFine (schedule := schedule) selected).family
          (coreCoarse
            (schedule := schedule) coordinate selected).family
          second := by
      simp only [onePassConstant]
      ring

noncomputable def coreScaleData
    (coordinate : Fin schedule.levelCount)
    {selected : Finset (Fin fine.card)}
    (hselected : selected.Nonempty) :
    WZ2PaperPureScaleCoverData
      (coreFine (schedule := schedule) selected).family
      (schedule.actualScale coordinate)
      (schedule.onePassConstant selected) := by
  let restricted :=
    (schedule.scaleData coordinate).restrict
      (coreFine (schedule := schedule) selected)
      (coreCoarse (schedule := schedule) coordinate selected)
      (coreCover (schedule := schedule) coordinate selected)
      (core_fullFiber_uniform
        (schedule := schedule) coordinate hselected)
      (ambient_fullFiber_count_le_densityLoss_core
        (schedule := schedule) coordinate hselected)
  simpa only [onePassConstant, max_self, mul_comm] using restricted

theorem selectedFullFiber_count_le_of_core_density
    (coordinate : Fin schedule.levelCount)
    (pruningDepth : ℕ)
    {selected core : Finset (Fin fine.card)}
    (hselected : selected.Nonempty)
    (core_subset : core ⊆ selected)
    (node_density :
      ∀ node : Finset (Fin fine.card),
        (core ∩
          (tree (schedule := schedule)).fiber
            (coordinate.1 + 1) node).Nonempty →
          selected.card *
              ((tree (schedule := schedule)).fiber
                (coordinate.1 + 1) node).card ≤
            2 ^ pruningDepth *
              (core ∩
                (tree (schedule := schedule)).fiber
                  (coordinate.1 + 1) node).card *
              fine.card)
    (parent :
      Fin
        ((schedule.scaleData coordinate).cover.hitParentSubfamily
          (WZ2PaperPureTubeSubfamily.fromFinset fine core)).family.card) :
    wz2PaperOrdinaryFullFiberCount
        fine
        (schedule.scaleData coordinate).coarse
        (((schedule.scaleData coordinate).cover.hitParentSubfamily
          (WZ2PaperPureTubeSubfamily.fromFinset fine core)).embedding
            parent) ≤
      ((2 ^ pruningDepth : ENNReal) *
          fine.enncard *
          (selected.card : ENNReal)⁻¹) *
        wz2PaperOrdinaryFullFiberCount
          (WZ2PaperPureTubeSubfamily.fromFinset fine core).family
          ((schedule.scaleData coordinate).cover.hitParentSubfamily
            (WZ2PaperPureTubeSubfamily.fromFinset fine core)).family
          parent := by
  let coreFine :=
    WZ2PaperPureTubeSubfamily.fromFinset fine core
  let coreCoarse :=
    (schedule.scaleData coordinate).cover.hitParentSubfamily
      coreFine
  rcases
      (schedule.scaleData coordinate).cover.hitParent_surjective
        coreFine parent with
    ⟨source, hsource⟩
  let leaf := coreFine.embedding source
  have hleafCore : leaf ∈ core := by
    exact Finset.orderEmbOfFin_mem core rfl source
  have hleafFiber :
      leaf ∈
        (tree (schedule := schedule)).fiber
          (coordinate.1 + 1)
          (schedule.nodeAt (coordinate.1 + 1) leaf) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ leaf, rfl⟩
  have hnonempty :
      (core ∩
        (tree (schedule := schedule)).fiber
          (coordinate.1 + 1)
          (schedule.nodeAt (coordinate.1 + 1) leaf)).Nonempty :=
    Finset.nonempty_def.mpr
      ⟨leaf, Finset.mem_inter.mpr ⟨hleafCore, hleafFiber⟩⟩
  have hdensityNat :=
    node_density
      (schedule.nodeAt (coordinate.1 + 1) leaf) hnonempty
  have hdensity :
      (selected.card : ENNReal) *
          (((tree (schedule := schedule)).fiber
            (coordinate.1 + 1)
            (schedule.nodeAt (coordinate.1 + 1) leaf)).card :
            ENNReal) ≤
        (2 ^ pruningDepth : ENNReal) *
          ((core ∩
            (tree (schedule := schedule)).fiber
              (coordinate.1 + 1)
              (schedule.nodeAt
                (coordinate.1 + 1) leaf)).card : ENNReal) *
          fine.enncard := by
    change
      (selected.card : ENNReal) *
          (((tree (schedule := schedule)).fiber
            (coordinate.1 + 1)
            (schedule.nodeAt (coordinate.1 + 1) leaf)).card :
            ENNReal) ≤
        (2 ^ pruningDepth : ENNReal) *
          ((core ∩
            (tree (schedule := schedule)).fiber
              (coordinate.1 + 1)
              (schedule.nodeAt
                (coordinate.1 + 1) leaf)).card : ENNReal) *
          (fine.card : ENNReal)
    exact_mod_cast hdensityNat
  have hselectedPos : 0 < (selected.card : ENNReal) := by
    exact_mod_cast Finset.card_pos.mpr hselected
  have hselectedTop : (selected.card : ENNReal) ≠ ⊤ := by
    simp
  have hbound :
      (((tree (schedule := schedule)).fiber
        (coordinate.1 + 1)
        (schedule.nodeAt (coordinate.1 + 1) leaf)).card :
        ENNReal) ≤
        ((2 ^ pruningDepth : ENNReal) *
            fine.enncard *
            (selected.card : ENNReal)⁻¹) *
          ((core ∩
            (tree (schedule := schedule)).fiber
              (coordinate.1 + 1)
              (schedule.nodeAt
                (coordinate.1 + 1) leaf)).card : ENNReal) := by
    calc
      (((tree (schedule := schedule)).fiber
          (coordinate.1 + 1)
          (schedule.nodeAt (coordinate.1 + 1) leaf)).card :
          ENNReal) =
          ((selected.card : ENNReal) *
            (selected.card : ENNReal)⁻¹) *
              (((tree (schedule := schedule)).fiber
                (coordinate.1 + 1)
                (schedule.nodeAt
                  (coordinate.1 + 1) leaf)).card : ENNReal) := by
        rw [ENNReal.mul_inv_cancel hselectedPos.ne' hselectedTop]
        simp
      _ =
          ((selected.card : ENNReal) *
              (((tree (schedule := schedule)).fiber
                (coordinate.1 + 1)
                (schedule.nodeAt
                  (coordinate.1 + 1) leaf)).card : ENNReal)) *
            (selected.card : ENNReal)⁻¹ := by
        ring
      _ ≤
          ((2 ^ pruningDepth : ENNReal) *
              ((core ∩
                (tree (schedule := schedule)).fiber
                  (coordinate.1 + 1)
                  (schedule.nodeAt
                    (coordinate.1 + 1) leaf)).card : ENNReal) *
              fine.enncard) *
            (selected.card : ENNReal)⁻¹ := by
        gcongr
      _ =
          ((2 ^ pruningDepth : ENNReal) *
              fine.enncard *
              (selected.card : ENNReal)⁻¹) *
            ((core ∩
              (tree (schedule := schedule)).fiber
                (coordinate.1 + 1)
                (schedule.nodeAt
                  (coordinate.1 + 1) leaf)).card : ENNReal) := by
        ring
  have hparent :
      (schedule.scaleData coordinate).cover.parent leaf =
        coreCoarse.embedding parent := by
    change
      (schedule.scaleData coordinate).cover.parent
          (coreFine.embedding source) =
        coreCoarse.embedding parent
    rw [←
      (schedule.scaleData coordinate).cover.hitParent_ambient
        coreFine source, hsource]
  have hcoreFiberCard :
      (wz2PaperOrdinaryFullFiberIndices
          coreFine.family coreCoarse.family parent).card =
        (core ∩
          (tree (schedule := schedule)).fiber
            (coordinate.1 + 1)
            (schedule.nodeAt (coordinate.1 + 1) leaf)).card := by
    rw [wz2_paper_selected_fullFiber_card]
    change
      (wz2PaperSelectedAmbientFullFiberIndices
        coreFine (coreCoarse.embedding parent)).card =
      (core ∩
        (tree (schedule := schedule)).fiber
          (coordinate.1 + 1)
          (schedule.nodeAt (coordinate.1 + 1) leaf)).card
    congr 1
    ext ambientSource
    simp only [wz2PaperSelectedAmbientFullFiberIndices,
      Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter]
    have himage :
        Finset.image coreFine.embedding Finset.univ = core := by
      ext index
      constructor
      · intro hindex
        rcases Finset.mem_image.mp hindex with ⟨target, _, rfl⟩
        exact Finset.orderEmbOfFin_mem core rfl target
      · intro hindex
        let equivalence : Fin core.card ≃ core :=
          (core.orderIsoOfFin rfl).toEquiv
        exact Finset.mem_image.mpr
          ⟨equivalence.symm ⟨index, hindex⟩,
            Finset.mem_univ _,
            congrArg Subtype.val
              (equivalence.apply_symm_apply ⟨index, hindex⟩)⟩
    rw [himage, ← hparent]
    rw [tree_fiber_coordinate_nodeAt_eq_fullFiber
      (schedule := schedule) coordinate leaf]
  rw [wz2PaperOrdinaryFullFiberCount,
    wz2PaperOrdinaryFullFiberCount]
  rw [← hparent]
  rw [← tree_fiber_coordinate_nodeAt_eq_fullFiber
    (schedule := schedule) coordinate leaf]
  rw [hcoreFiberCard]
  exact hbound

noncomputable def outputScaleData
    (coordinate : Fin schedule.levelCount)
    {selected : Finset (Fin fine.card)}
    (hselected : selected.Nonempty) :
    WZ2PaperPureScaleCoverData
      (coreFine (schedule := schedule) selected).family
      (schedule.actualScale coordinate)
      (schedule.outputConstant selected) :=
  (schedule.coreScaleData coordinate hselected).mono
    (le_max_right _ _)

theorem densityLoss_ne_top
    {selected : Finset (Fin fine.card)}
    (hselected : selected.Nonempty) :
    schedule.densityLoss selected ≠ ⊤ := by
  have hselectedZero : (selected.card : ENNReal) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hselected).ne'
  have hpowerTop :
      (2 ^ schedule.levelCount : ENNReal) ≠ ⊤ := by
    simp
  have hfineTop : fine.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hinverseTop :
      (selected.card : ENNReal)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr hselectedZero
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top hpowerTop hfineTop) hinverseTop

theorem onePassConstant_ne_top
    {selected : Finset (Fin fine.card)}
    (hselected : selected.Nonempty) :
    schedule.onePassConstant selected ≠ ⊤ := by
  exact ENNReal.mul_ne_top
    schedule.ambient_finite.2
    (schedule.densityLoss_ne_top hselected)

theorem outputConstant_finite
    {selected : Finset (Fin fine.card)}
    (hselected : selected.Nonempty) :
    WZ2PaperFiniteErrorConstant
      (schedule.outputConstant selected) := by
  refine ⟨schedule.scaleWindow_finite.1.trans
      (le_max_left _ _), ?_⟩
  exact max_ne_top
    schedule.scaleWindow_finite.2
    (schedule.onePassConstant_ne_top hselected)

theorem coreDistinct
    (selected : Finset (Fin fine.card)) :
    WZ2PaperOrdinaryIsEssentiallyDistinct
      (coreFine (schedule := schedule) selected).family :=
  schedule.fine_distinct.subfamily
    (coreFine (schedule := schedule) selected)

theorem coreNearbyCWA
    {selected : Finset (Fin fine.card)}
    (hselected : selected.Nonempty) :
    WZ2PaperPureCWAAtNearbyScales
      (coreFine (schedule := schedule) selected).family
      (schedule.outputConstant selected) := by
  apply pureWZ2_nearby_from_finite_witnesses
    (schedule.scaleData ⟨0, schedule.levelCount_pos⟩).delta_pos
    (schedule.outputConstant_finite hselected).1
    (schedule.outputConstant_finite hselected).2
    (schedule.coreDistinct selected)
    schedule.levelCount schedule.levelCount_pos
    (fun coordinate =>
      ⟨schedule.actualScale coordinate,
        schedule.outputScaleData coordinate hselected⟩)
  intro requested
  rcases schedule.rounding requested with
    ⟨coordinate, hrequested, hwindow⟩
  refine ⟨coordinate, hrequested, ?_⟩
  exact hwindow.trans_le <| by
    gcongr
    exact le_max_left _ _

theorem core_weight_retention
    (selected : Finset (Fin fine.card))
    (weight : Fin fine.card → ENNReal)
    (weightLevel : ENNReal)
    (hlower :
      ∀ leaf ∈ selected, weightLevel ≤ weight leaf)
    (hupper :
      ∀ leaf ∈ selected, weight leaf ≤ 2 * weightLevel) :
    ∑ leaf ∈ selected, weight leaf ≤
      2 ^ (schedule.levelCount + 1) *
        ∑ leaf ∈ coreIndices (schedule := schedule) selected,
          weight leaf := by
  exact
    (tree (schedule := schedule)).dyadic_weight_retention
      selected weight weightLevel hlower hupper

end PureWZ2Prop62PureSchedule

end Kakeya.Assouad

end
