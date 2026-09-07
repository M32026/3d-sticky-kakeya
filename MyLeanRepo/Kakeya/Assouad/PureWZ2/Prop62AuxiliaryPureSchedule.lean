import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AuxiliaryTreeCore

/-!
# Proposition 6.2 metric parents: old pure schedule after the augmented core

The final core is selected once from the old pure schedule together with the
auxiliary metric-parent ancestry level.  This module restricts every old
literal Definition 2.12 witness to that one core.  The only pruning loss is
`2^(L+1) * #U / #S`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62AuxiliaryLevel

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow}
    {Aux : Type}
    [Fintype Aux] [DecidableEq Aux]
    (auxiliary :
      PureWZ2Prop62AuxiliaryLevel schedule Aux)

def densityLoss
    (auxiliary :
      PureWZ2Prop62AuxiliaryLevel schedule Aux)
    (selected : Finset (Fin fine.card)) : ENNReal :=
  (2 ^ (schedule.levelCount + 1) : ENNReal) *
    fine.enncard *
    (selected.card : ENNReal)⁻¹

def onePassConstant
    (auxiliary :
      PureWZ2Prop62AuxiliaryLevel schedule Aux)
    (selected : Finset (Fin fine.card)) : ENNReal :=
  ambientConstant * auxiliary.densityLoss selected

def outputConstant
    (auxiliary :
      PureWZ2Prop62AuxiliaryLevel schedule Aux)
    (selected : Finset (Fin fine.card)) : ENNReal :=
  max scaleWindow (auxiliary.onePassConstant selected)

def coreIndices
    (selected : Finset (Fin fine.card)) :
    Finset (Fin fine.card) :=
  (auxiliary.coreOutput selected).core

def coreFine
    (selected : Finset (Fin fine.card)) :
    WZ2PaperPureTubeSubfamily fine :=
  WZ2PaperPureTubeSubfamily.fromFinset fine
    (auxiliary.coreIndices selected)

def coreCoarse
    (coordinate : Fin schedule.levelCount)
    (selected : Finset (Fin fine.card)) :
    WZ2PaperPureTubeSubfamily
      (schedule.scaleData coordinate).coarse :=
  (schedule.scaleData coordinate).cover.hitParentSubfamily
    (auxiliary.coreFine selected)

def coreCover
    (coordinate : Fin schedule.levelCount)
    (selected : Finset (Fin fine.card)) :
    WZ2PaperPurePartitioningCover
      (auxiliary.coreFine selected).family
      (auxiliary.coreCoarse coordinate selected).family :=
  (schedule.scaleData coordinate).cover.restrictToHitParents
    (auxiliary.coreFine selected)

theorem coreCoarse_hitParent_ambient
    (coordinate : Fin schedule.levelCount)
    (selected : Finset (Fin fine.card))
    (source : Fin (auxiliary.coreFine selected).family.card) :
    (auxiliary.coreCoarse coordinate selected).embedding
        ((schedule.scaleData coordinate).cover.hitParent
          (auxiliary.coreFine selected) source) =
      (schedule.scaleData coordinate).cover.parent
        ((auxiliary.coreFine selected).embedding source) := by
  exact
    (schedule.scaleData coordinate).cover.hitParent_ambient
      (auxiliary.coreFine selected) source

theorem core_nonempty
    {selected : Finset (Fin fine.card)}
    (selectedNonempty : selected.Nonempty) :
    (auxiliary.coreIndices selected).Nonempty := by
  apply Finset.card_pos.mp
  have selectedPos : 0 < selected.card :=
    Finset.card_pos.mpr selectedNonempty
  have retention :=
    (auxiliary.coreOutput selected).global_retention
  by_contra hcore
  have coreZero :
      (auxiliary.coreIndices selected).card = 0 :=
    Nat.eq_zero_of_not_pos hcore
  change
    selected.card ≤
      2 ^ (schedule.levelCount + 1) *
        (auxiliary.coreIndices selected).card at retention
  rw [coreZero, mul_zero] at retention
  omega

theorem coreFine_nonempty
    {selected : Finset (Fin fine.card)}
    (selectedNonempty : selected.Nonempty) :
    (auxiliary.coreFine selected).family.Nonempty := by
  change 0 < (auxiliary.coreIndices selected).card
  exact Finset.card_pos.mpr
    (auxiliary.core_nonempty selectedNonempty)

theorem ambientFiber_le_densityLoss_core
    (coordinate : Fin schedule.levelCount)
    {selected : Finset (Fin fine.card)}
    (selectedNonempty : selected.Nonempty)
    (parent :
      Fin (auxiliary.coreCoarse coordinate selected).family.card) :
    wz2PaperOrdinaryFullFiberCount
        fine
        (schedule.scaleData coordinate).coarse
        ((auxiliary.coreCoarse coordinate selected).embedding parent) ≤
      auxiliary.densityLoss selected *
        wz2PaperOrdinaryFullFiberCount
          (auxiliary.coreFine selected).family
          (auxiliary.coreCoarse coordinate selected).family
          parent := by
  apply
    PureWZ2Prop62PureSchedule.selectedFullFiber_count_le_of_core_density
      (schedule := schedule) coordinate
      (schedule.levelCount + 1)
      selectedNonempty
      (auxiliary.coreOutput selected).core_subset
  · intro node hnonempty
    exact
      (auxiliary.coreOutput selected).old_node_density
        coordinate node hnonempty

theorem coreFiber_le_ambient
    (coordinate : Fin schedule.levelCount)
    (selected : Finset (Fin fine.card))
    (parent :
      Fin (auxiliary.coreCoarse coordinate selected).family.card) :
    wz2PaperOrdinaryFullFiberCount
        (auxiliary.coreFine selected).family
        (auxiliary.coreCoarse coordinate selected).family
        parent ≤
      wz2PaperOrdinaryFullFiberCount
        fine
        (schedule.scaleData coordinate).coarse
        ((auxiliary.coreCoarse coordinate selected).embedding parent) := by
  rw [wz2PaperOrdinaryFullFiberCount,
    wz2PaperOrdinaryFullFiberCount,
    wz2_paper_selected_fullFiber_card]
  exact_mod_cast
    Finset.card_le_card <|
      show
        wz2PaperSelectedAmbientFullFiberIndices
            (auxiliary.coreFine selected)
            ((auxiliary.coreCoarse coordinate selected).embedding parent) ⊆
          wz2PaperOrdinaryFullFiberIndices
            fine (schedule.scaleData coordinate).coarse
            ((auxiliary.coreCoarse coordinate selected).embedding parent)
      by
        intro source hsource
        exact (Finset.mem_filter.mp hsource).2.2

theorem core_fullFiber_uniform
    (coordinate : Fin schedule.levelCount)
    {selected : Finset (Fin fine.card)}
    (selectedNonempty : selected.Nonempty) :
    WZ2PaperPureFullFibersAreCUniform
      (auxiliary.coreFine selected).family
      (auxiliary.coreCoarse coordinate selected).family
      (auxiliary.onePassConstant selected) := by
  intro first second
  calc
    wz2PaperOrdinaryFullFiberCount
        (auxiliary.coreFine selected).family
        (auxiliary.coreCoarse coordinate selected).family first ≤
      wz2PaperOrdinaryFullFiberCount
        fine (schedule.scaleData coordinate).coarse
        ((auxiliary.coreCoarse coordinate selected).embedding first) :=
      auxiliary.coreFiber_le_ambient coordinate selected first
    _ ≤
      ambientConstant *
        wz2PaperOrdinaryFullFiberCount
          fine (schedule.scaleData coordinate).coarse
          ((auxiliary.coreCoarse coordinate selected).embedding second) :=
      (schedule.scaleData coordinate).full_fiber_uniform _ _
    _ ≤
      ambientConstant *
        (auxiliary.densityLoss selected *
          wz2PaperOrdinaryFullFiberCount
            (auxiliary.coreFine selected).family
            (auxiliary.coreCoarse coordinate selected).family second) := by
      gcongr
      exact auxiliary.ambientFiber_le_densityLoss_core
        coordinate selectedNonempty second
    _ =
      auxiliary.onePassConstant selected *
        wz2PaperOrdinaryFullFiberCount
          (auxiliary.coreFine selected).family
          (auxiliary.coreCoarse coordinate selected).family second := by
      simp only [onePassConstant]
      ring

noncomputable def coreScaleData
    (coordinate : Fin schedule.levelCount)
    {selected : Finset (Fin fine.card)}
    (selectedNonempty : selected.Nonempty) :
    WZ2PaperPureScaleCoverData
      (auxiliary.coreFine selected).family
      (schedule.actualScale coordinate)
      (auxiliary.onePassConstant selected) := by
  let restricted :=
    (schedule.scaleData coordinate).restrict
      (auxiliary.coreFine selected)
      (auxiliary.coreCoarse coordinate selected)
      (auxiliary.coreCover coordinate selected)
      (auxiliary.core_fullFiber_uniform
        coordinate selectedNonempty)
      (auxiliary.ambientFiber_le_densityLoss_core
        coordinate selectedNonempty)
  have constantEq :
      max
          (auxiliary.onePassConstant selected)
          (auxiliary.densityLoss selected * ambientConstant) =
        auxiliary.onePassConstant selected := by
    simp only [onePassConstant, mul_comm, max_self]
  exact
    {
      delta_pos := restricted.delta_pos
      rho_pos := restricted.rho_pos
      coarse := (auxiliary.coreCoarse coordinate selected).family
      cover := auxiliary.coreCover coordinate selected
      full_fiber_uniform := by
        intro first second
        exact constantEq ▸ restricted.full_fiber_uniform first second
      rescaledFiber := by
        intro parent
        exact constantEq ▸ restricted.rescaledFiber parent
    }

noncomputable def outputScaleData
    (coordinate : Fin schedule.levelCount)
    {selected : Finset (Fin fine.card)}
    (selectedNonempty : selected.Nonempty) :
    WZ2PaperPureScaleCoverData
      (auxiliary.coreFine selected).family
      (schedule.actualScale coordinate)
      (auxiliary.outputConstant selected) := by
  let core :=
    auxiliary.coreScaleData coordinate selectedNonempty
  exact
    {
      delta_pos := core.delta_pos
      rho_pos := core.rho_pos
      coarse := (auxiliary.coreCoarse coordinate selected).family
      cover := auxiliary.coreCover coordinate selected
      full_fiber_uniform := by
        intro first second
        exact
          (auxiliary.core_fullFiber_uniform
            coordinate selectedNonempty first second).trans (by
          gcongr
          exact le_max_right _ _)
      rescaledFiber := by
        intro parent
        rcases
            (auxiliary.coreScaleData
              coordinate selectedNonempty).rescaledFiber parent
          with ⟨fiber⟩
        exact
          ⟨{
            normalization := fiber.normalization
            convex_wolff := fun convexSet convex =>
              (fiber.convex_wolff convexSet convex).trans (by
                gcongr
                · exact le_max_right _ _
                · exact le_rfl)
          }⟩
    }

theorem densityLoss_ne_top
    {selected : Finset (Fin fine.card)}
    (selectedNonempty : selected.Nonempty) :
    auxiliary.densityLoss selected ≠ ⊤ := by
  have selectedZero : (selected.card : ENNReal) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr selectedNonempty).ne'
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by simp) (by
      simp [Kakeya.Streamlined.TubeFamily.enncard]))
    (ENNReal.inv_ne_top.mpr selectedZero)

theorem outputConstant_finite
    {selected : Finset (Fin fine.card)}
    (selectedNonempty : selected.Nonempty) :
    WZ2PaperFiniteErrorConstant
      (auxiliary.outputConstant selected) := by
  have onePassTop :
      auxiliary.onePassConstant selected ≠ ⊤ :=
    ENNReal.mul_ne_top schedule.ambient_finite.2
      (auxiliary.densityLoss_ne_top selectedNonempty)
  exact
    ⟨schedule.scaleWindow_finite.1.trans (le_max_left _ _),
      max_ne_top schedule.scaleWindow_finite.2 onePassTop⟩

theorem coreNearbyCWA
    {selected : Finset (Fin fine.card)}
    (selectedNonempty : selected.Nonempty) :
    WZ2PaperPureCWAAtNearbyScales
      (auxiliary.coreFine selected).family
      (auxiliary.outputConstant selected) := by
  apply pureWZ2_nearby_from_finite_witnesses
    (schedule.scaleData ⟨0, schedule.levelCount_pos⟩).delta_pos
    (auxiliary.outputConstant_finite selectedNonempty).1
    (auxiliary.outputConstant_finite selectedNonempty).2
    (schedule.fine_distinct.subfamily
      (auxiliary.coreFine selected))
    schedule.levelCount schedule.levelCount_pos
    (fun coordinate =>
      ⟨schedule.actualScale coordinate,
        auxiliary.outputScaleData coordinate selectedNonempty⟩)
  intro requested
  rcases schedule.rounding requested with
    ⟨coordinate, requestedLe, window⟩
  exact
    ⟨coordinate, requestedLe,
      window.trans_le <| by
        gcongr
        exact le_max_left _ _⟩

end PureWZ2Prop62AuxiliaryLevel

end Kakeya.Assouad

end
