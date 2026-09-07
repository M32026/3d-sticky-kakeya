import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureNearbyTree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TreePureSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LocalizedActualFiberLineCover
import MyLeanRepo.Kakeya.Assouad.PropStickyParentNestedTransitivity

/-!
# Proposition 6.2: laminar schedule from independent pure witnesses

At geometrically separated requested scales, independently chosen literal
Definition 2.12 witnesses have nested complete strict fibers.  This is the
tree construction used in Lemma 2.13.

The Section 6 line-chart representation of the coarse parents is kept as an
explicit input.  It is not part of the public Definition 2.12 interface.
-/

noncomputable section

namespace Kakeya.Assouad

/--
A finite requested-scale net before Definition 2.12 chooses its actual
witness scales.

The adjacent separation already includes the factor `4 * C` needed to make
arbitrary nearby witnesses laminar.  The independent rounding constant
controls only the requested grid; one further factor `C` pays for the actual
nearby window.
-/
structure PureWZ2Prop62RequestedScaleSchedule
    (delta : ℝ)
    (ambientConstant scaleWindow : ENNReal) where
  scaleWindow_finite :
    WZ2PaperFiniteErrorConstant scaleWindow
  levelCount : ℕ
  levelCount_pos : 0 < levelCount
  requested :
    Fin levelCount → WZ2PaperRequestedScale delta
  requested_separated :
    ∀ first second : Fin levelCount,
      first.1 < second.1 →
        4 * ambientConstant.toReal * (requested second).1 ≤
          (requested first).1
  rounding :
    ∀ target : WZ2PaperRequestedScale delta,
      ∃ coordinate : Fin levelCount,
        target.1 ≤ (requested coordinate).1 ∧
          ENNReal.ofReal (requested coordinate).1 <
            scaleWindow * ENNReal.ofReal target.1

/--
The literal Lemma 2.13 tree before choosing Section 6 line representatives.

This record contains exactly the data supplied by public pure Definition 2.12:
complete strict fibers at finitely many actual scales, laminarity, and a
rounding map.  It deliberately has no `L₃` or line-metric cover fields.
-/
structure PureWZ2Prop62LaminarPureSchedule
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

namespace PureWZ2Prop62LaminarPureSchedule

/-- Total coordinate lookup, used only through in-range tree levels. -/
def coordinateAt
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (level : ℕ) :
    Fin schedule.levelCount :=
  if hlevel : level < schedule.levelCount then
    ⟨level, hlevel⟩
  else
    ⟨0, schedule.levelCount_pos⟩

@[simp] theorem coordinateAt_eq
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    {level : ℕ}
    (hlevel : level < schedule.levelCount) :
    schedule.coordinateAt level = ⟨level, hlevel⟩ := by
  simp [coordinateAt, hlevel]

/-- Rooted-tree node represented by the complete parent fiber at one level. -/
def nodeAt
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (level : ℕ)
    (leaf : Fin fine.card) :
    Finset (Fin fine.card) :=
  if level = 0 then
    Finset.univ
  else
    let coordinate :=
      schedule.coordinateAt (level - 1)
    Finset.univ.filter fun source =>
      (schedule.scaleData coordinate).cover.parent source =
        (schedule.scaleData coordinate).cover.parent leaf

@[simp] theorem nodeAt_zero
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (leaf : Fin fine.card) :
    schedule.nodeAt 0 leaf = Finset.univ := by
  simp [nodeAt]

theorem nodeAt_succ
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    {level : ℕ}
    (hlevel : level < schedule.levelCount)
    (leaf : Fin fine.card) :
    schedule.nodeAt (level + 1) leaf =
      Finset.univ.filter fun source =>
        (schedule.scaleData ⟨level, hlevel⟩).cover.parent source =
          (schedule.scaleData ⟨level, hlevel⟩).cover.parent leaf := by
  unfold nodeAt
  rw [if_neg (Nat.succ_ne_zero level)]
  change
    Finset.univ.filter (fun source =>
      (schedule.scaleData
        (schedule.coordinateAt level)).cover.parent source =
        (schedule.scaleData
          (schedule.coordinateAt level)).cover.parent leaf) =
      Finset.univ.filter fun source =>
        (schedule.scaleData ⟨level, hlevel⟩).cover.parent source =
          (schedule.scaleData ⟨level, hlevel⟩).cover.parent leaf
  rw [schedule.coordinateAt_eq hlevel]

/-- The literal laminar schedule as a finite rooted tree. -/
def tree
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow) :
    PureWZ2Prop62FiniteTree
      (Fin fine.card) (Finset (Fin fine.card))
      schedule.levelCount where
  nodeAt := schedule.nodeAt
  root_constant first second := by
    simp
  nested level hlevel first second nodeEq := by
    by_cases levelZero : level = 0
    · subst level
      simp
    · obtain ⟨previous, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero levelZero
      have nextBound : previous + 1 < schedule.levelCount := by
        omega
      have currentBound : previous < schedule.levelCount := by
        omega
      have firstMem :
          first ∈ schedule.nodeAt (previous + 2) first := by
        rw [schedule.nodeAt_succ nextBound]
        simp
      rw [nodeEq] at firstMem
      have nextParentEq :
          (schedule.scaleData
            ⟨previous + 1, nextBound⟩).cover.parent first =
          (schedule.scaleData
            ⟨previous + 1, nextBound⟩).cover.parent second := by
        simpa only [schedule.nodeAt_succ nextBound,
          Finset.mem_filter, Finset.mem_univ, true_and] using firstMem
      have currentParentEq :=
        schedule.parent_nested
          previous nextBound first second nextParentEq
      rw [schedule.nodeAt_succ currentBound,
        schedule.nodeAt_succ currentBound]
      ext source
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [currentParentEq]

theorem nodeAt_coordinate_eq_fullFiber
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
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
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (coordinate : Fin schedule.levelCount)
    (leaf : Fin fine.card) :
    schedule.tree.fiber
        (coordinate.1 + 1)
        (schedule.nodeAt (coordinate.1 + 1) leaf) =
      wz2PaperOrdinaryFullFiberIndices
        fine
        (schedule.scaleData coordinate).coarse
        ((schedule.scaleData coordinate).cover.parent leaf) := by
  ext source
  constructor
  · intro sourceMem
    have nodeEq :
        schedule.nodeAt (coordinate.1 + 1) source =
          schedule.nodeAt (coordinate.1 + 1) leaf :=
      (Finset.mem_filter.mp sourceMem).2
    have sourceOwn :
        source ∈
          wz2PaperOrdinaryFullFiberIndices
            fine
            (schedule.scaleData coordinate).coarse
            ((schedule.scaleData coordinate).cover.parent source) :=
      (schedule.scaleData coordinate).cover.parent_mem_fullFiber source
    rw [
      ← schedule.nodeAt_coordinate_eq_fullFiber coordinate source,
      nodeEq,
      schedule.nodeAt_coordinate_eq_fullFiber coordinate leaf
    ] at sourceOwn
    exact sourceOwn
  · intro sourceMem
    have parentEq :
        (schedule.scaleData coordinate).cover.parent source =
          (schedule.scaleData coordinate).cover.parent leaf :=
      ((schedule.scaleData coordinate).cover.mem_fullFiber_iff_parent_eq
        (schedule.scaleData coordinate).rho_pos.le
        ((schedule.scaleData coordinate).cover.parent leaf)
        source).mp sourceMem
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ source, ?_⟩
    change
      schedule.nodeAt (coordinate.1 + 1) source =
        schedule.nodeAt (coordinate.1 + 1) leaf
    rw [schedule.nodeAt_succ coordinate.2,
      schedule.nodeAt_succ coordinate.2]
    ext candidate
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [parentEq]

private theorem selectedFullFiber_count_le_of_core_densityCoefficient
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (coordinate : Fin schedule.levelCount)
    (densityConstant : ℕ)
    {selected core : Finset (Fin fine.card)}
    (selectedNonempty : selected.Nonempty)
    (_core_subset : core ⊆ selected)
    (node_density :
      ∀ node : Finset (Fin fine.card),
        (core ∩
          schedule.tree.fiber
            (coordinate.1 + 1) node).Nonempty →
          selected.card *
              (schedule.tree.fiber
                (coordinate.1 + 1) node).card ≤
            densityConstant *
              (core ∩
                schedule.tree.fiber
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
      ((densityConstant : ENNReal) *
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
        coreFine parent
    with ⟨source, sourceParent⟩
  let leaf := coreFine.embedding source
  have leafCore : leaf ∈ core := by
    exact Finset.orderEmbOfFin_mem core rfl source
  have leafFiber :
      leaf ∈
        schedule.tree.fiber
          (coordinate.1 + 1)
          (schedule.nodeAt (coordinate.1 + 1) leaf) := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ leaf, rfl⟩
  have coreFiberNonempty :
      (core ∩
        schedule.tree.fiber
          (coordinate.1 + 1)
          (schedule.nodeAt (coordinate.1 + 1) leaf)).Nonempty :=
    ⟨leaf, Finset.mem_inter.mpr ⟨leafCore, leafFiber⟩⟩
  have densityNat :=
    node_density
      (schedule.nodeAt (coordinate.1 + 1) leaf)
      coreFiberNonempty
  have densityENN :
      (selected.card : ENNReal) *
          ((schedule.tree.fiber
            (coordinate.1 + 1)
            (schedule.nodeAt (coordinate.1 + 1) leaf)).card :
            ENNReal) ≤
        (densityConstant : ENNReal) *
          ((core ∩
            schedule.tree.fiber
              (coordinate.1 + 1)
              (schedule.nodeAt
                (coordinate.1 + 1) leaf)).card : ENNReal) *
          fine.enncard := by
    change
      (selected.card : ENNReal) *
          ((schedule.tree.fiber
            (coordinate.1 + 1)
            (schedule.nodeAt (coordinate.1 + 1) leaf)).card :
            ENNReal) ≤
        (densityConstant : ENNReal) *
          ((core ∩
            schedule.tree.fiber
              (coordinate.1 + 1)
              (schedule.nodeAt
                (coordinate.1 + 1) leaf)).card : ENNReal) *
          (fine.card : ENNReal)
    exact_mod_cast densityNat
  have selectedPos : 0 < (selected.card : ENNReal) := by
    exact_mod_cast selectedNonempty.card_pos
  have selectedFinite : (selected.card : ENNReal) ≠ ⊤ := by
    simp
  have fiberBound :
      ((schedule.tree.fiber
        (coordinate.1 + 1)
        (schedule.nodeAt (coordinate.1 + 1) leaf)).card :
        ENNReal) ≤
        ((densityConstant : ENNReal) *
            fine.enncard *
            (selected.card : ENNReal)⁻¹) *
          ((core ∩
            schedule.tree.fiber
              (coordinate.1 + 1)
              (schedule.nodeAt
                (coordinate.1 + 1) leaf)).card : ENNReal) := by
    calc
      ((schedule.tree.fiber
          (coordinate.1 + 1)
          (schedule.nodeAt (coordinate.1 + 1) leaf)).card :
          ENNReal) =
          ((selected.card : ENNReal) *
            (selected.card : ENNReal)⁻¹) *
              ((schedule.tree.fiber
                (coordinate.1 + 1)
                (schedule.nodeAt
                  (coordinate.1 + 1) leaf)).card : ENNReal) := by
        rw [ENNReal.mul_inv_cancel
          selectedPos.ne' selectedFinite]
        simp
      _ =
          ((selected.card : ENNReal) *
              ((schedule.tree.fiber
                (coordinate.1 + 1)
                (schedule.nodeAt
                  (coordinate.1 + 1) leaf)).card : ENNReal)) *
            (selected.card : ENNReal)⁻¹ := by
        ring
      _ ≤
          ((densityConstant : ENNReal) *
              ((core ∩
                schedule.tree.fiber
                  (coordinate.1 + 1)
                  (schedule.nodeAt
                    (coordinate.1 + 1) leaf)).card : ENNReal) *
              fine.enncard) *
            (selected.card : ENNReal)⁻¹ := by
        gcongr
      _ =
          ((densityConstant : ENNReal) *
              fine.enncard *
              (selected.card : ENNReal)⁻¹) *
            ((core ∩
              schedule.tree.fiber
                (coordinate.1 + 1)
                (schedule.nodeAt
                  (coordinate.1 + 1) leaf)).card : ENNReal) := by
        ring
  have parentEq :
      (schedule.scaleData coordinate).cover.parent leaf =
        coreCoarse.embedding parent := by
    change
      (schedule.scaleData coordinate).cover.parent
          (coreFine.embedding source) =
        coreCoarse.embedding parent
    rw [←
      (schedule.scaleData coordinate).cover.hitParent_ambient
        coreFine source, sourceParent]
  have coreFiberCard :
      (wz2PaperOrdinaryFullFiberIndices
          coreFine.family coreCoarse.family parent).card =
        (core ∩
          schedule.tree.fiber
            (coordinate.1 + 1)
            (schedule.nodeAt (coordinate.1 + 1) leaf)).card := by
    rw [wz2_paper_selected_fullFiber_card]
    change
      (wz2PaperSelectedAmbientFullFiberIndices
        coreFine (coreCoarse.embedding parent)).card =
      (core ∩
        schedule.tree.fiber
          (coordinate.1 + 1)
          (schedule.nodeAt (coordinate.1 + 1) leaf)).card
    congr 1
    ext ambientSource
    simp only [
      wz2PaperSelectedAmbientFullFiberIndices,
      Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter
    ]
    have imageEq :
        Finset.image coreFine.embedding Finset.univ = core := by
      ext index
      constructor
      · intro indexMem
        rcases Finset.mem_image.mp indexMem with
          ⟨target, _targetUniv, rfl⟩
        exact Finset.orderEmbOfFin_mem core rfl target
      · intro indexMem
        let equivalence : Fin core.card ≃ core :=
          (core.orderIsoOfFin rfl).toEquiv
        exact
          Finset.mem_image.mpr
            ⟨equivalence.symm ⟨index, indexMem⟩,
              Finset.mem_univ _,
              congrArg Subtype.val
                (equivalence.apply_symm_apply
                  ⟨index, indexMem⟩)⟩
    rw [imageEq, ← parentEq]
    rw [schedule.tree_fiber_coordinate_nodeAt_eq_fullFiber
      coordinate leaf]
  rw [
    wz2PaperOrdinaryFullFiberCount,
    wz2PaperOrdinaryFullFiberCount,
    ← parentEq,
    ← schedule.tree_fiber_coordinate_nodeAt_eq_fullFiber
      coordinate leaf,
    coreFiberCard
  ]
  exact fiberBound

theorem selectedFullFiber_count_le_of_core_density
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (coordinate : Fin schedule.levelCount)
    (pruningDepth : ℕ)
    {selected core : Finset (Fin fine.card)}
    (selectedNonempty : selected.Nonempty)
    (core_subset : core ⊆ selected)
    (node_density :
      ∀ node : Finset (Fin fine.card),
        (core ∩
          schedule.tree.fiber
            (coordinate.1 + 1) node).Nonempty →
          selected.card *
              (schedule.tree.fiber
                (coordinate.1 + 1) node).card ≤
            2 ^ pruningDepth *
              (core ∩
                schedule.tree.fiber
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
          parent :=
  by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      schedule.selectedFullFiber_count_le_of_core_densityCoefficient
        coordinate (2 ^ pruningDepth) selectedNonempty core_subset
          node_density parent

theorem selectedFullFiber_count_le_of_core_densityConstant
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (coordinate : Fin schedule.levelCount)
    (densityConstant : ℕ)
    {selected core : Finset (Fin fine.card)}
    (selectedNonempty : selected.Nonempty)
    (core_subset : core ⊆ selected)
    (node_density :
      ∀ node : Finset (Fin fine.card),
        (core ∩
          schedule.tree.fiber
            (coordinate.1 + 1) node).Nonempty →
          selected.card *
              (schedule.tree.fiber
                (coordinate.1 + 1) node).card ≤
            densityConstant *
              (core ∩
                schedule.tree.fiber
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
      ((densityConstant : ENNReal) *
          fine.enncard *
          (selected.card : ENNReal)⁻¹) *
        wz2PaperOrdinaryFullFiberCount
          (WZ2PaperPureTubeSubfamily.fromFinset fine core).family
          ((schedule.scaleData coordinate).cover.hitParentSubfamily
            (WZ2PaperPureTubeSubfamily.fromFinset fine core)).family
          parent :=
  schedule.selectedFullFiber_count_le_of_core_densityCoefficient
    coordinate densityConstant selectedNonempty core_subset
      node_density parent

/--
Parent equality at a finer coordinate propagates to every earlier coordinate
of the literal Lemma 2.13 schedule.
-/
theorem parent_eq_of_coordinate_le
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (coarse fineCoordinate : Fin schedule.levelCount)
    (coordinateLe : coarse.1 ≤ fineCoordinate.1)
    (first second : Fin fine.card)
    (fineParentEq :
      (schedule.scaleData fineCoordinate).cover.parent first =
        (schedule.scaleData fineCoordinate).cover.parent second) :
    (schedule.scaleData coarse).cover.parent first =
      (schedule.scaleData coarse).cover.parent second := by
  let predicate :
      ∀ level : ℕ, coarse.1 ≤ level → Prop :=
    fun level _ =>
      ∀ hlevel : level < schedule.levelCount,
        (schedule.scaleData ⟨level, hlevel⟩).cover.parent first =
            (schedule.scaleData ⟨level, hlevel⟩).cover.parent second →
          (schedule.scaleData coarse).cover.parent first =
            (schedule.scaleData coarse).cover.parent second
  have base : predicate coarse.1 le_rfl := by
    intro hlevel hparent
    have coordinateEq :
        (⟨coarse.1, hlevel⟩ : Fin schedule.levelCount) =
          coarse := by
      apply Fin.ext
      rfl
    rwa [coordinateEq] at hparent
  have step :
      ∀ level (hcoarse : coarse.1 ≤ level),
        predicate level hcoarse →
          predicate (level + 1) (Nat.le.step hcoarse) := by
    intro level hcoarse inductionHypothesis hnext hparent
    have hcurrent : level < schedule.levelCount :=
      Nat.lt_of_succ_lt hnext
    have currentParent :
        (schedule.scaleData ⟨level, hcurrent⟩).cover.parent first =
          (schedule.scaleData ⟨level, hcurrent⟩).cover.parent second :=
      schedule.parent_nested level hnext first second hparent
    exact inductionHypothesis hcurrent currentParent
  have result :
      predicate fineCoordinate.1 coordinateLe :=
    Nat.le_induction base step fineCoordinate.1 coordinateLe
  exact result fineCoordinate.2 fineParentEq

/-- Choose one actual fine tube from every complete strict packet. -/
noncomputable def parentRepresentative
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (coordinate : Fin schedule.levelCount)
    (parent : Fin (schedule.scaleData coordinate).coarse.card) :
    Fin fine.card :=
  Classical.choose <|
    (schedule.scaleData coordinate).cover.fullFiber_nonempty_of_uniform
      fineNonempty
      (schedule.scaleData coordinate).full_fiber_uniform parent

theorem parentRepresentative_mem
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (coordinate : Fin schedule.levelCount)
    (parent : Fin (schedule.scaleData coordinate).coarse.card) :
    schedule.parentRepresentative fineNonempty coordinate parent ∈
      wz2PaperOrdinaryFullFiberIndices
        fine (schedule.scaleData coordinate).coarse parent :=
  Classical.choose_spec <|
    (schedule.scaleData coordinate).cover.fullFiber_nonempty_of_uniform
      fineNonempty
      (schedule.scaleData coordinate).full_fiber_uniform parent

/-- The chosen representative has the parent from whose complete fiber it came. -/
theorem parentRepresentative_parent
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (coordinate : Fin schedule.levelCount)
    (parent : Fin (schedule.scaleData coordinate).coarse.card) :
    (schedule.scaleData coordinate).cover.parent
        (schedule.parentRepresentative fineNonempty coordinate parent) =
      parent := by
  exact
    ((schedule.scaleData coordinate).cover.mem_fullFiber_iff_parent_eq
      (schedule.scaleData coordinate).rho_pos.le parent
      (schedule.parentRepresentative fineNonempty coordinate parent)).mp
      (schedule.parentRepresentative_mem fineNonempty coordinate parent)

/-- Representatives of distinct complete packets are distinct fine tubes. -/
theorem parentRepresentative_injective
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (coordinate : Fin schedule.levelCount) :
    Function.Injective
      (schedule.parentRepresentative fineNonempty coordinate) := by
  intro first second representativesEq
  calc
    first =
        (schedule.scaleData coordinate).cover.parent
          (schedule.parentRepresentative
            fineNonempty coordinate first) :=
      (schedule.parentRepresentative_parent
        fineNonempty coordinate first).symm
    _ =
        (schedule.scaleData coordinate).cover.parent
          (schedule.parentRepresentative
            fineNonempty coordinate second) := by
      rw [representativesEq]
    _ = second :=
      schedule.parentRepresentative_parent
        fineNonempty coordinate second

/-- One selected fine representative for each complete packet. -/
noncomputable def representativeSubfamily
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (coordinate : Fin schedule.levelCount) :
    WZ2PaperPureTubeSubfamily fine where
  family :=
    {
      card := (schedule.scaleData coordinate).coarse.card
      tube := fun parent =>
        fine.tube <|
          schedule.parentRepresentative fineNonempty coordinate parent
    }
  embedding :=
    {
      toFun := schedule.parentRepresentative fineNonempty coordinate
      inj' := schedule.parentRepresentative_injective fineNonempty coordinate
    }
  tube_eq := fun _ => rfl

theorem representativeSubfamily_lineClass
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (fineLineClass : WZ1PaperIsLineClass fine)
    (coordinate : Fin schedule.levelCount) :
    WZ1PaperIsLineClass
      (schedule.representativeSubfamily fineNonempty coordinate).family :=
  fineLineClass.subfamily
    (schedule.representativeSubfamily fineNonempty coordinate).toTubeSubfamily

theorem representativeSubfamily_boundedBase
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (fineBoundedBase : HasBoundedBase fine 4)
    (coordinate : Fin schedule.levelCount) :
    HasBoundedBase
      (schedule.representativeSubfamily fineNonempty coordinate).family 4 := by
  intro parent
  exact
    fineBoundedBase <|
      schedule.parentRepresentative fineNonempty coordinate parent

theorem representativeSubfamily_distinct
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (coordinate : Fin schedule.levelCount) :
    WZ2PaperOrdinaryIsEssentiallyDistinct
      (schedule.representativeSubfamily fineNonempty coordinate).family :=
  schedule.fine_distinct.subfamily
    (schedule.representativeSubfamily fineNonempty coordinate)

/--
The Section 6 line representative of a complete packet, relabelled at an
explicit radius without changing its supporting line.
-/
noncomputable def representativeLineFamily
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (coordinate : Fin schedule.levelCount)
    (targetScale : ℝ) :
    Kakeya.Streamlined.TubeFamily targetScale where
  card := (schedule.scaleData coordinate).coarse.card
  tube parent :=
    wz2PaperRelabelTube (targetScale := targetScale) <|
      wz2PaperCanonicalLineTube <|
        fine.tube <|
          schedule.parentRepresentative fineNonempty coordinate parent

theorem representativeLineFamily_lineClass
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (fineLineClass : WZ1PaperIsLineClass fine)
    (coordinate : Fin schedule.levelCount)
    (targetScale : ℝ) :
    WZ1PaperIsLineClass
      (schedule.representativeLineFamily
        fineNonempty coordinate targetScale) := by
  intro parent
  exact
    wz2PaperRelabelTube_lineClass <|
      wz2PaperCanonicalLineTube_lineClass <|
        fineLineClass <|
          schedule.parentRepresentative fineNonempty coordinate parent

/--
At sufficiently small actual scale, every member of a complete packet is
covered in the Section 6 line metric by its representative-axis enlargement.
-/
theorem parentRepresentative_lineCover
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (fineLineClass : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (coordinate : Fin schedule.levelCount)
    (actualSmall : schedule.actualScale coordinate ≤ 1 / 10000)
    (targetScale : ℝ)
    (actualTarget :
      1200000 * schedule.actualScale coordinate ≤ targetScale)
    (source : Fin fine.card) :
    WZ1PaperTubeCovers
      (fine.tube source)
      ((schedule.representativeLineFamily
          fineNonempty coordinate targetScale).tube
        ((schedule.scaleData coordinate).cover.parent source)) := by
  let parent :=
    (schedule.scaleData coordinate).cover.parent source
  have sourceMem :
      source ∈
        wz2PaperOrdinaryFullFiberIndices
          fine (schedule.scaleData coordinate).coarse parent :=
    (schedule.scaleData coordinate).cover.parent_mem_fullFiber source
  exact
    wz2_pure_actual_fullFiber_lineCoveredBy_representative
      (schedule.scaleData coordinate).cover
      (schedule.scaleData coordinate).delta_pos
      (schedule.delta_le_actualScale coordinate)
      actualSmall actualTarget fineLineClass fineBase parent
      (schedule.parentRepresentative fineNonempty coordinate parent)
      (schedule.parentRepresentative_mem
        fineNonempty coordinate parent)
      source sourceMem

/-- Forget the Section 6 line-chart certificates of an existing schedule. -/
def ofProp62PureSchedule
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow) :
    PureWZ2Prop62LaminarPureSchedule
      fine ambientConstant scaleWindow where
  ambient_finite := schedule.ambient_finite
  scaleWindow_finite := schedule.scaleWindow_finite
  fine_distinct := schedule.fine_distinct
  levelCount := schedule.levelCount
  levelCount_pos := schedule.levelCount_pos
  actualScale := schedule.actualScale
  delta_le_actualScale := schedule.delta_le_actualScale
  actualScale_antitone := schedule.actualScale_antitone
  scaleData := schedule.scaleData
  parent_nested := schedule.parent_nested
  rounding := schedule.rounding

instance pureScheduleCoe
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal} :
    Coe
      (PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow)
      (PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow) where
  coe := ofProp62PureSchedule

/--
Attach the Section 6 line-chart representation after constructing the public
laminar tree.  These are extra geometric certificates, not consequences of
Definition 2.12.
-/
noncomputable def toProp62PureSchedule
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (coarseLineClass :
      ∀ coordinate,
        WZ1PaperIsLineClass
          (schedule.scaleData coordinate).coarse)
    (parentLineCover :
      ∀ coordinate source,
        WZ1PaperTubeCovers
          (fine.tube source)
          ((schedule.scaleData coordinate).coarse.tube
            ((schedule.scaleData coordinate).cover.parent source))) :
    PureWZ2Prop62PureSchedule
      fine ambientConstant scaleWindow where
  ambient_finite := schedule.ambient_finite
  scaleWindow_finite := schedule.scaleWindow_finite
  fine_distinct := schedule.fine_distinct
  levelCount := schedule.levelCount
  levelCount_pos := schedule.levelCount_pos
  actualScale := schedule.actualScale
  delta_le_actualScale := schedule.delta_le_actualScale
  actualScale_antitone := schedule.actualScale_antitone
  scaleData := schedule.scaleData
  coarse_line_class := coarseLineClass
  parent_covers := parentLineCover
  parent_nested := schedule.parent_nested
  rounding := schedule.rounding

end PureWZ2Prop62LaminarPureSchedule

namespace WZ2PaperPureCWAAtNearbyScales

private theorem nearby_rho_lt_constant_mul_requested
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine C)
    {requested : WZ2PaperRequestedScale delta}
    (nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C) :
    nearby.rho < C.toReal * requested.1 := by
  have constantRealPos : 0 < C.toReal := by
    have constantOne : (1 : ℝ) ≤ C.toReal := by
      simpa only [ENNReal.toReal_one] using
        ENNReal.toReal_mono ambient.2.1.2 ambient.2.1.1
    exact zero_lt_one.trans_le constantOne
  have requestedPos : 0 < requested.1 :=
    ambient.1.trans_le requested.2.1
  have targetPos : 0 < C.toReal * requested.1 :=
    mul_pos constantRealPos requestedPos
  apply (ENNReal.ofReal_lt_ofReal_iff targetPos).mp
  calc
    ENNReal.ofReal nearby.rho <
        C * ENNReal.ofReal requested.1 :=
      nearby.within_factor
    _ =
        ENNReal.ofReal (C.toReal * requested.1) := by
      calc
        C * ENNReal.ofReal requested.1 =
            ENNReal.ofReal C.toReal *
              ENNReal.ofReal requested.1 := by
          rw [ENNReal.ofReal_toReal ambient.2.1.2]
        _ = ENNReal.ofReal (C.toReal * requested.1) :=
          (ENNReal.ofReal_mul constantRealPos.le).symm

/--
Package independently selected pure nearby witnesses into the Proposition 6.2
laminar schedule.

The separation hypothesis is imposed on requested scales.  The strict nearby
window then gives the stronger separation of actual scales needed by
`parent_maps_nested_of_gap`.
-/
noncomputable def toProp62IndependentLaminarSchedule
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (scaleWindowFinite :
      WZ2PaperFiniteErrorConstant scaleWindow)
    {levelCount : ℕ}
    (levelCountPos : 0 < levelCount)
    (requested :
      Fin levelCount → WZ2PaperRequestedScale delta)
    (nearby :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (requested coordinate) ambientConstant)
    (requestedSeparated :
      ∀ first second : Fin levelCount,
        first.1 < second.1 →
          4 * ambientConstant.toReal * (requested second).1 ≤
            (requested first).1)
    (rounding :
      ∀ target : WZ2PaperRequestedScale delta,
        ∃ coordinate : Fin levelCount,
          target.1 ≤ (nearby coordinate).rho ∧
            ENNReal.ofReal (nearby coordinate).rho <
              scaleWindow * ENNReal.ofReal target.1) :
    PureWZ2Prop62LaminarPureSchedule
      fine ambientConstant scaleWindow where
  ambient_finite := ambient.2.1
  scaleWindow_finite := scaleWindowFinite
  fine_distinct := ambient.2.2.1
  levelCount := levelCount
  levelCount_pos := levelCountPos
  actualScale := fun coordinate => (nearby coordinate).rho
  delta_le_actualScale := fun coordinate =>
    (requested coordinate).2.1.trans
      (nearby coordinate).requested_le
  actualScale_antitone := by
    intro first second firstLeSecond
    by_cases indicesEq : first = second
    · subst second
      exact le_rfl
    · have indicesLt : first.1 < second.1 := by
        exact lt_of_le_of_ne firstLeSecond
          (fun equality => indicesEq (Fin.ext equality))
      have nearbyUpper :=
        nearby_rho_lt_constant_mul_requested
          ambient (nearby second)
      have separated := requestedSeparated first second indicesLt
      exact le_trans nearbyUpper.le <| by
        calc
          ambientConstant.toReal * (requested second).1 ≤
              4 * ambientConstant.toReal * (requested second).1 := by
            have nonnegative :
                0 ≤ ambientConstant.toReal * (requested second).1 := by
              exact mul_nonneg ENNReal.toReal_nonneg <|
                ambient.1.le.trans (requested second).2.1
            nlinarith
          _ ≤ (requested first).1 := separated
          _ ≤ (nearby first).rho :=
            (nearby first).requested_le
  scaleData := fun coordinate => (nearby coordinate).scaleData
  parent_nested := by
    intro level hnext first second sameFineParent
    let fineCoordinate : Fin levelCount :=
      ⟨level + 1, hnext⟩
    let coarseCoordinate : Fin levelCount :=
      ⟨level, Nat.lt_of_succ_lt hnext⟩
    have fineUpper :=
      nearby_rho_lt_constant_mul_requested
        ambient (nearby fineCoordinate)
    have separated :
        4 * ambientConstant.toReal *
              (requested fineCoordinate).1 ≤
            (requested coarseCoordinate).1 :=
      requestedSeparated coarseCoordinate fineCoordinate (by
        simp [fineCoordinate, coarseCoordinate])
    have actualSeparated :
        4 * ((nearby fineCoordinate).rho - delta) ≤
          (nearby coarseCoordinate).rho := by
      have requestedCoarseLe :
          (requested coarseCoordinate).1 ≤
            (nearby coarseCoordinate).rho :=
        (nearby coarseCoordinate).requested_le
      have deltaNonnegative : 0 ≤ delta := ambient.1.le
      have fineActualNonnegative :
          0 ≤ (nearby fineCoordinate).rho :=
        (nearby fineCoordinate).scaleData.rho_pos.le
      nlinarith
    exact
      (nearby fineCoordinate).scaleData.cover
        |>.parent_maps_nested_of_gap
          (nearby coarseCoordinate).scaleData.cover
          ambient.1.le
          (nearby fineCoordinate).scaleData.rho_pos
          (nearby coarseCoordinate).scaleData.rho_pos
          ((requested fineCoordinate).2.1.trans
            (nearby fineCoordinate).requested_le)
          ((requested coarseCoordinate).2.1.trans
            (nearby coarseCoordinate).requested_le)
          actualSeparated first second sameFineParent
  rounding := rounding

/--
Choose the Definition 2.12 witness independently at every coordinate of a
separated requested-scale net and assemble the resulting laminar tree.
-/
noncomputable def toProp62LaminarSchedule
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant requestedWindow : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (requestedSchedule :
      PureWZ2Prop62RequestedScaleSchedule
        delta ambientConstant requestedWindow) :
    PureWZ2Prop62LaminarPureSchedule
      fine ambientConstant (ambientConstant * requestedWindow) := by
  let nearby :
      ∀ coordinate : Fin requestedSchedule.levelCount,
        WZ2PaperPureNearbyScaleCoverData
          fine (requestedSchedule.requested coordinate) ambientConstant :=
    fun coordinate =>
      Classical.choice <|
        ambient.2.2.2 (requestedSchedule.requested coordinate)
  refine
    ambient.toProp62IndependentLaminarSchedule
      ?_ requestedSchedule.levelCount_pos
      requestedSchedule.requested nearby
      requestedSchedule.requested_separated ?_
  · exact
      ⟨by
        simpa only [one_mul] using
          mul_le_mul ambient.2.1.1
            requestedSchedule.scaleWindow_finite.1 bot_le bot_le,
        ENNReal.mul_ne_top ambient.2.1.2
          requestedSchedule.scaleWindow_finite.2⟩
  · intro target
    rcases requestedSchedule.rounding target with
      ⟨coordinate, targetLeRequested, requestedWithin⟩
    refine
      ⟨coordinate,
        targetLeRequested.trans (nearby coordinate).requested_le,
        ?_⟩
    calc
      ENNReal.ofReal (nearby coordinate).rho <
          ambientConstant *
            ENNReal.ofReal (requestedSchedule.requested coordinate).1 :=
        (nearby coordinate).within_factor
      _ <
          ambientConstant *
            (requestedWindow * ENNReal.ofReal target.1) := by
        have ambientZero : ambientConstant ≠ 0 :=
          ne_of_gt <| zero_lt_one.trans_le ambient.2.1.1
        have ambientTop : ambientConstant ≠ ⊤ :=
          ambient.2.1.2
        simpa only [mul_comm] using
          ENNReal.mul_lt_mul_left
            ambientZero ambientTop requestedWithin
      _ =
          (ambientConstant * requestedWindow) *
            ENNReal.ofReal target.1 := by
        ring

/--
Compatibility constructor for callers that already have the additional
Section 6 line-chart certificates.
-/
noncomputable def toProp62IndependentPureSchedule
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (ambient :
      WZ2PaperPureCWAAtNearbyScales fine ambientConstant)
    (scaleWindowFinite :
      WZ2PaperFiniteErrorConstant scaleWindow)
    {levelCount : ℕ}
    (levelCountPos : 0 < levelCount)
    (requested :
      Fin levelCount → WZ2PaperRequestedScale delta)
    (nearby :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (requested coordinate) ambientConstant)
    (requestedSeparated :
      ∀ first second : Fin levelCount,
        first.1 < second.1 →
          4 * ambientConstant.toReal * (requested second).1 ≤
            (requested first).1)
    (coarseLineClass :
      ∀ coordinate,
        WZ1PaperIsLineClass
          (nearby coordinate).scaleData.coarse)
    (parentLineCover :
      ∀ coordinate source,
        WZ1PaperTubeCovers
          (fine.tube source)
          ((nearby coordinate).scaleData.coarse.tube
            ((nearby coordinate).scaleData.cover.parent source)))
    (rounding :
      ∀ target : WZ2PaperRequestedScale delta,
        ∃ coordinate : Fin levelCount,
          target.1 ≤ (nearby coordinate).rho ∧
            ENNReal.ofReal (nearby coordinate).rho <
              scaleWindow * ENNReal.ofReal target.1) :
    PureWZ2Prop62PureSchedule
      fine ambientConstant scaleWindow :=
  (ambient.toProp62IndependentLaminarSchedule
    scaleWindowFinite levelCountPos requested nearby
    requestedSeparated rounding).toProp62PureSchedule
      coarseLineClass parentLineCover

end WZ2PaperPureCWAAtNearbyScales

end Kakeya.Assouad

end
