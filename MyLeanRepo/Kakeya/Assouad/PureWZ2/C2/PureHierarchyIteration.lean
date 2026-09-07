import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyBackwardSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleToSource
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.AnchoredHierarchyAssembly

/-!
# Dependent Pure WZ2 Corollary 5.6 iteration

This file carries out the finite Lemma-25 iteration on one ordinary paper
tube family.  It deliberately stops before the final popularity thinning and
endpoint reanchoring.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Input loss at level zero, and the preceding output loss thereafter. -/
def pureWZ2HierarchyLevelInputLoss
    {N : ℕ} {sigma hierarchyLoss : ℝ}
    (schedule : PureWZ2BackwardScheduleData N sigma hierarchyLoss)
    (level : ℕ) (hlevel : level < N) : ℝ :=
  match level with
  | 0 => schedule.sourceCeiling ⟨0, by omega⟩
  | previous + 1 => schedule.outputLoss ⟨previous, by omega⟩

theorem pureWZ2HierarchyLevelInputLoss_pos
    {N : ℕ} {sigma hierarchyLoss : ℝ}
    (schedule : PureWZ2BackwardScheduleData N sigma hierarchyLoss)
    (level : ℕ) (hlevel : level < N) :
    0 < pureWZ2HierarchyLevelInputLoss schedule level hlevel := by
  cases level with
  | zero => exact schedule.sourceCeiling_pos _
  | succ previous => exact schedule.outputLoss_pos _

theorem pureWZ2HierarchyLevelInputLoss_le_ceiling
    {N : ℕ} {sigma hierarchyLoss : ℝ}
    (schedule : PureWZ2BackwardScheduleData N sigma hierarchyLoss)
    (level : ℕ) (hlevel : level < N) :
    pureWZ2HierarchyLevelInputLoss schedule level hlevel ≤
      schedule.sourceCeiling ⟨level, hlevel⟩ := by
  cases level with
  | zero => simp [pureWZ2HierarchyLevelInputLoss]
  | succ previous =>
      simpa [pureWZ2HierarchyLevelInputLoss] using
        schedule.outputLoss_le_next_ceiling
          ⟨previous, by omega⟩ (by omega)

theorem pureWZ2HierarchyLevelInputLoss_le_outputLoss
    {N : ℕ} {sigma hierarchyLoss : ℝ}
    (schedule : PureWZ2BackwardScheduleData N sigma hierarchyLoss)
    (level : ℕ) (hlevel : level < N) :
    pureWZ2HierarchyLevelInputLoss schedule level hlevel ≤
      schedule.outputLoss ⟨level, hlevel⟩ := by
  exact (pureWZ2HierarchyLevelInputLoss_le_ceiling
    schedule level hlevel).trans <|
      (schedule.sourceCeiling_le ⟨level, hlevel⟩).trans (by
        have hpos := schedule.outputLoss_pos ⟨level, hlevel⟩
        linarith)

theorem pureWZ2HierarchyScale_pos
    {N : ℕ} {delta : ℝ} (hdelta : 0 < delta)
    (level : Fin N) :
    0 < wz1Corollary26Scale delta N level :=
  Real.rpow_pos_of_pos hdelta _

theorem pureWZ2HierarchyScale_le_one
    {N : ℕ} {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1) (level : Fin N) :
    wz1Corollary26Scale delta N level ≤ 1 := by
  apply Real.rpow_le_one hdelta.le hdeltaOne
  positivity

theorem pureWZ2Hierarchy_delta_le_scale
    {N : ℕ} {delta : ℝ} (hN : 2 ≤ N)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (level : Fin N) :
    delta ≤ wz1Corollary26Scale delta N level := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hlevel : (((level : ℕ) + 1 : ℝ) / (N : ℝ)) ≤ 1 := by
    rw [div_le_one hNpos]
    exact_mod_cast (show (level : ℕ) + 1 ≤ N by omega)
  have hpower := Real.rpow_le_rpow_of_exponent_ge
    hdelta hdeltaOne hlevel
  simpa [wz1Corollary26Scale] using hpower

theorem pureWZ2HierarchyScale_last
    {N : ℕ} {delta : ℝ} (hN : 2 ≤ N)
    (hdelta : 0 < delta) :
    wz1Corollary26Scale delta N (pureWZ2FinLast N hN) = delta := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hexponent :
      (((pureWZ2FinLast N hN : ℕ) + 1 : ℝ) / (N : ℝ)) = 1 := by
    have hnat : N - 1 + 1 = N := by omega
    have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
      exact_mod_cast hnat
    rw [show (pureWZ2FinLast N hN : ℕ) = N - 1 by rfl, hcast]
    exact div_self hNpos.ne'
  simp [wz1Corollary26Scale, hexponent]

private theorem pureWZ2_transport_subshading
    {delta : ℝ}
    {first second : Kakeya.Streamlined.TubeFamily delta}
    (hfamily : first = second)
    {refined source : WZ1PaperTubeShading first}
    (hsub : PureWZ2PaperIsSubshading refined source) :
    PureWZ2PaperIsSubshading
      (hfamily ▸ refined) (hfamily ▸ source) := by
  subst hfamily
  exact hsub

private theorem pureWZ2_transport_cubical
    {delta : ℝ}
    {first second : Kakeya.Streamlined.TubeFamily delta}
    (hfamily : first = second)
    {shading : WZ1PaperTubeShading first}
    (hcubical : WZ1PaperIsCubicalShading shading) :
    WZ1PaperIsCubicalShading (hfamily ▸ shading) := by
  subst hfamily
  exact hcubical

private theorem pureWZ2_transport_union
    {delta : ℝ}
    {first second : Kakeya.Streamlined.TubeFamily delta}
    (hfamily : first = second)
    (shading : WZ1PaperTubeShading first) :
    (hfamily ▸ shading : WZ1PaperTubeShading second).union =
      shading.union := by
  subst hfamily
  rfl

private theorem pureWZ2_transport_cropped_extremal
    {delta sigma loss : ℝ}
    {first second : Kakeya.Streamlined.TubeFamily delta}
    (hfamily : first = second)
    {shading : WZ1PaperTubeShading first}
    (hextremal : WZ2PaperCroppedIsExtremal
      sigma loss first shading) :
    WZ2PaperCroppedIsExtremal
      sigma loss second (hfamily ▸ shading) := by
  subst hfamily
  exact hextremal

private noncomputable def pureWZ2_transport_localGrains
    {delta sigma : ℝ}
    {first second : Kakeya.Streamlined.TubeFamily delta}
    (hfamily : first = second)
    {shading : WZ1PaperTubeShading first}
    {C : ENNReal}
    (data : PureWZ2LocalGrainData shading sigma C) :
    PureWZ2LocalGrainData (hfamily ▸ shading) sigma C := by
  subst hfamily
  exact data

private noncomputable def pureWZ2_transport_globalGrains
    {delta sigma : ℝ}
    {first second : Kakeya.Streamlined.TubeFamily delta}
    (hfamily : first = second)
    {shading : WZ1PaperTubeShading first}
    {C : ENNReal}
    (data : PureWZ2BoundedLipschitzGlobalGrainData shading sigma C) :
    PureWZ2BoundedLipschitzGlobalGrainData (hfamily ▸ shading) sigma C := by
  subst hfamily
  exact data

private theorem pureWZ2_transport_cropped_loss
    {delta sigma firstLoss secondLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hloss : firstLoss = secondLoss)
    (data : WZ2PaperCroppedIsExtremal
      sigma firstLoss family shading) :
    WZ2PaperCroppedIsExtremal
      sigma secondLoss family shading := by
  subst secondLoss
  exact data

private theorem pureWZ2_transport_volume_loss
    {delta sigma firstLoss secondLoss : ℝ}
    {set : Set Point3}
    (hloss : firstLoss = secondLoss)
    (data : Kakeya.realRpowENN delta (sigma + firstLoss) ≤
      MeasureTheory.volume set) :
    Kakeya.realRpowENN delta (sigma + secondLoss) ≤
      MeasureTheory.volume set := by
  subst secondLoss
  exact data

private noncomputable def pureWZ2_transport_local_loss
    {delta sigma firstLoss secondLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hloss : firstLoss = secondLoss)
    (data : PureWZ2LocalGrainData shading sigma
      (Kakeya.realRpowENN delta (-firstLoss))) :
    PureWZ2LocalGrainData shading sigma
      (Kakeya.realRpowENN delta (-secondLoss)) := by
  subst secondLoss
  exact data

private noncomputable def pureWZ2_transport_global_loss
    {delta sigma firstLoss secondLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hloss : firstLoss = secondLoss)
    (data : PureWZ2BoundedLipschitzGlobalGrainData shading sigma
      (Kakeya.realRpowENN delta (-firstLoss))) :
    PureWZ2BoundedLipschitzGlobalGrainData shading sigma
      (Kakeya.realRpowENN delta (-secondLoss)) := by
  subst secondLoss
  exact data

private theorem pureWZ2_transport_global_slope
    {delta sigma firstLoss secondLoss : ℝ}
    {first second : Kakeya.Streamlined.TubeFamily delta}
    (hfamily : first = second)
    {shading : WZ1PaperTubeShading first}
    (hloss : firstLoss = secondLoss)
    (data : PureWZ2BoundedLipschitzGlobalGrainData shading sigma
      (Kakeya.realRpowENN delta (-firstLoss))) :
    (pureWZ2_transport_globalGrains hfamily
      (pureWZ2_transport_global_loss hloss data)).slope = data.slope := by
  subst second
  subst secondLoss
  rfl

private theorem pureWZ2_transport_plane_vertical_bound
    {delta sigma firstLoss secondLoss : ℝ}
    {first second : Kakeya.Streamlined.TubeFamily delta}
    (hfamily : first = second)
    {shading : WZ1PaperTubeShading first}
    (hloss : firstLoss = secondLoss)
    (data : PureWZ2LocalGrainData shading sigma
      (Kakeya.realRpowENN delta (-firstLoss)))
    (hbound : ∀ point : {point : Point3 // point ∈ shading.union},
      |data.planeMap point (2 : Fin 3)| ≤ 1 / 2) :
    ∀ point : {point : Point3 //
        point ∈ (hfamily ▸ shading :
          WZ1PaperTubeShading second).union},
      |(pureWZ2_transport_localGrains hfamily
          (pureWZ2_transport_local_loss hloss data)).planeMap point
          (2 : Fin 3)| ≤ 1 / 2 := by
  subst second
  subst secondLoss
  exact hbound

private theorem pureWZ2_transport_eq_of_heq
    {index : Sort*} {object : index → Sort*}
    {first second target : index}
    (hfirst : first = target) (hsecond : second = target)
    {x : object first} {y : object second}
    (hxy : HEq x y) :
    (hfirst ▸ x) = (hsecond ▸ y) := by
  subst first
  subst second
  exact eq_of_heq hxy

/-- One recursively constructed hierarchy level and its source. -/
noncomputable def pureWZ2BuildHierarchyLevel
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (schedule : PureWZ2BackwardScheduleData N sigma hierarchyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ schedule.commonDeltaThreshold)
    (source0 : PureWZ2QuantitativeGrainConfiguration sigma
      schedule.initialSourceCeiling delta)
    (level : ℕ) (hlevel : level < N) :
    Σ source : PureWZ2QuantitativeGrainConfiguration sigma
        (pureWZ2HierarchyLevelInputLoss schedule level hlevel) delta,
      PureWZ2LocallyLinearOneScaleData source
        (schedule.outputLoss ⟨level, hlevel⟩)
        (wz1Corollary26Scale delta N ⟨level, hlevel⟩) :=
  match level with
  | 0 =>
      let levelFin : Fin N := ⟨0, by omega⟩
      have hnext : (levelFin : ℕ) + 1 < N := by
        change 1 < N
        exact lt_of_lt_of_le (by norm_num) schedule.levelCount_two
      have hdeltaLevel : delta ≤ schedule.deltaThreshold levelFin :=
        hdeltaThreshold.trans (schedule.commonDeltaThreshold_le levelFin)
      have hwindow := schedule.scale_window levelFin hnext hdelta hdeltaOne
      let produced := schedule.produce_intermediate levelFin hnext
        schedule.initialSourceCeiling schedule.initialSourceCeiling_pos le_rfl
        delta hdelta hdeltaLevel source0
        (wz1Corollary26Scale delta N levelFin)
        (pureWZ2Hierarchy_delta_le_scale schedule.levelCount_two
          hdelta hdeltaOne levelFin)
        (pureWZ2HierarchyScale_le_one hdelta hdeltaOne levelFin)
        hwindow.1 hwindow.2
      ⟨source0, produced.some⟩
  | previous + 1 =>
      let previousData := pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
        hdeltaThreshold source0 previous (by omega)
      have hadvance :
          pureWZ2HierarchyLevelInputLoss schedule previous (by omega) ≤
            schedule.outputLoss ⟨previous, by omega⟩ :=
        pureWZ2HierarchyLevelInputLoss_le_outputLoss
          schedule previous (by omega)
      let nextSource : PureWZ2QuantitativeGrainConfiguration sigma
          (schedule.outputLoss ⟨previous, by omega⟩) delta :=
        previousData.2.toGrainConfiguration hadvance
      have hinputEq : schedule.outputLoss ⟨previous, by omega⟩ =
          pureWZ2HierarchyLevelInputLoss schedule (previous + 1) hlevel := by
        simp [pureWZ2HierarchyLevelInputLoss]
      let source : PureWZ2QuantitativeGrainConfiguration sigma
          (pureWZ2HierarchyLevelInputLoss schedule (previous + 1) hlevel)
          delta := hinputEq ▸ nextSource
      let levelFin : Fin N := ⟨previous + 1, hlevel⟩
      have hinputPos := pureWZ2HierarchyLevelInputLoss_pos
        schedule (previous + 1) hlevel
      have hinputCeiling := pureWZ2HierarchyLevelInputLoss_le_ceiling
        schedule (previous + 1) hlevel
      have hdeltaLevel : delta ≤ schedule.deltaThreshold levelFin :=
        hdeltaThreshold.trans (schedule.commonDeltaThreshold_le levelFin)
      if hnext : (previous + 1) + 1 < N then
        let hwindow := schedule.scale_window levelFin hnext hdelta hdeltaOne
        let produced := schedule.produce_intermediate levelFin hnext
          (pureWZ2HierarchyLevelInputLoss schedule (previous + 1) hlevel)
          hinputPos hinputCeiling delta hdelta hdeltaLevel source
          (wz1Corollary26Scale delta N levelFin)
          (pureWZ2Hierarchy_delta_le_scale schedule.levelCount_two
            hdelta hdeltaOne levelFin)
          (pureWZ2HierarchyScale_le_one hdelta hdeltaOne levelFin)
          hwindow.1 hwindow.2
        ⟨source, produced.some⟩
      else
        have hlast : previous + 1 = N - 1 := by omega
        have hlevelFin : levelFin =
            pureWZ2FinLast N schedule.levelCount_two := by
          apply Fin.ext
          exact hlast
        have hdeltaLast : delta ≤ schedule.deltaThreshold
            (pureWZ2FinLast N schedule.levelCount_two) := by
          rw [← hlevelFin]
          exact hdeltaLevel
        have hrho : wz1Corollary26Scale delta N levelFin = delta := by
          rw [hlevelFin]
          exact pureWZ2HierarchyScale_last schedule.levelCount_two hdelta
        let produced := schedule.produce_terminal
          (pureWZ2HierarchyLevelInputLoss schedule (previous + 1) hlevel)
          hinputPos (by
            change pureWZ2HierarchyLevelInputLoss schedule
                (previous + 1) hlevel ≤ schedule.sourceCeiling levelFin at hinputCeiling
            rw [hlevelFin] at hinputCeiling
            exact hinputCeiling)
          delta hdelta hdeltaLast source
        have hloss : schedule.outputLoss levelFin = schedule.terminalLoss := by
          rw [hlevelFin]
          exact schedule.outputLoss_last
        ⟨source, hloss.symm ▸ hrho.symm ▸ produced.some⟩

/-- The source of level `k+1` is the retained shading produced at level `k`. -/
theorem pureWZ2BuildHierarchyLevel_source_shading
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (schedule : PureWZ2BackwardScheduleData N sigma hierarchyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ schedule.commonDeltaThreshold)
    (source0 : PureWZ2QuantitativeGrainConfiguration sigma
      schedule.initialSourceCeiling delta)
    {level : ℕ} (hlevel : Nat.succ level < N) :
    HEq
      (pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
        hdeltaThreshold source0 (Nat.succ level) hlevel).1.shading
      (pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
        hdeltaThreshold source0 level (by omega)).2.shading := by
  rw [pureWZ2BuildHierarchyLevel]
  by_cases hnext : level + 1 + 1 < N
  · rw [dif_pos hnext]
    rfl
  · rw [dif_neg hnext]
    rfl

/-- Every recursively produced source is on the initial tube family. -/
theorem pureWZ2BuildHierarchyLevel_family
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (schedule : PureWZ2BackwardScheduleData N sigma hierarchyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ schedule.commonDeltaThreshold)
    (source0 : PureWZ2QuantitativeGrainConfiguration sigma
      schedule.initialSourceCeiling delta)
    (level : ℕ) (hlevel : level < N) :
    (pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 level hlevel).1.family = source0.family := by
  induction level with
  | zero => rfl
  | succ previous ih =>
      rw [pureWZ2BuildHierarchyLevel]
      by_cases hnext : previous + 1 + 1 < N
      · rw [dif_pos hnext]
        exact ih (by omega)
      · rw [dif_neg hnext]
        exact ih (by omega)

/-- Every recursively produced source carries the original source slope. -/
theorem pureWZ2BuildHierarchyLevel_slope
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (schedule : PureWZ2BackwardScheduleData N sigma hierarchyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ schedule.commonDeltaThreshold)
    (source0 : PureWZ2QuantitativeGrainConfiguration sigma
      schedule.initialSourceCeiling delta)
    (level : ℕ) (hlevel : level < N) :
    (pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 level hlevel).1.globalGrains.slope =
        source0.globalGrains.slope := by
  induction level with
  | zero => rfl
  | succ previous ih =>
      have hadvance :
          pureWZ2HierarchyLevelInputLoss schedule previous (by omega) ≤
            schedule.outputLoss ⟨previous, by omega⟩ :=
        pureWZ2HierarchyLevelInputLoss_le_outputLoss
          schedule previous (by omega)
      have hstep :=
        PureWZ2LocallyLinearOneScaleData.toGrainConfiguration_slope
          (pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
            hdeltaThreshold source0 previous (by omega)).2 hadvance
      rw [pureWZ2BuildHierarchyLevel]
      by_cases hnext : previous + 1 + 1 < N
      · rw [dif_pos hnext]
        exact hstep.trans (ih (by omega))
      · rw [dif_neg hnext]
        exact hstep.trans (ih (by omega))

/-- After transporting both sides to the initial family, the source shading
of level `k+1` is literally the output shading of level `k`. -/
theorem pureWZ2BuildHierarchyLevel_source_shading_transport
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (schedule : PureWZ2BackwardScheduleData N sigma hierarchyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ schedule.commonDeltaThreshold)
    (source0 : PureWZ2QuantitativeGrainConfiguration sigma
      schedule.initialSourceCeiling delta)
    {level : ℕ} (hlevel : level + 1 < N) :
    let current := pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 (level + 1) hlevel
    let previous := pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 level (by omega)
    let currentFamily := pureWZ2BuildHierarchyLevel_family schedule hdelta
      hdeltaOne hdeltaThreshold source0 (level + 1) hlevel
    let previousFamily := pureWZ2BuildHierarchyLevel_family schedule hdelta
      hdeltaOne hdeltaThreshold source0 level (by omega)
    (currentFamily ▸ current.1.shading :
        WZ1PaperTubeShading source0.family) =
      (previousFamily ▸ previous.2.shading :
        WZ1PaperTubeShading source0.family) := by
  exact pureWZ2_transport_eq_of_heq _ _
    (pureWZ2BuildHierarchyLevel_source_shading schedule hdelta hdeltaOne
      hdeltaThreshold source0 hlevel)

/-- The output shading at one hierarchy level, transported to the fixed
initial tube family. -/
noncomputable def pureWZ2HierarchyShadingAt
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (schedule : PureWZ2BackwardScheduleData N sigma hierarchyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ schedule.commonDeltaThreshold)
    (source0 : PureWZ2QuantitativeGrainConfiguration sigma
      schedule.initialSourceCeiling delta)
    (level : ℕ) (hlevel : level < N) :
    WZ1PaperTubeShading source0.family :=
  let data := pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
    hdeltaThreshold source0 level hlevel
  let hfamily := pureWZ2BuildHierarchyLevel_family schedule hdelta
    hdeltaOne hdeltaThreshold source0 level hlevel
  hfamily ▸ data.2.shading

/-- One step of the paper's descending same-configuration refinement chain. -/
theorem pureWZ2HierarchyShadingAt_succ_subshading
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (schedule : PureWZ2BackwardScheduleData N sigma hierarchyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ schedule.commonDeltaThreshold)
    (source0 : PureWZ2QuantitativeGrainConfiguration sigma
      schedule.initialSourceCeiling delta)
    {level : ℕ} (hlevel : level + 1 < N) :
    PureWZ2PaperIsSubshading
      (pureWZ2HierarchyShadingAt schedule hdelta hdeltaOne
        hdeltaThreshold source0 (level + 1) hlevel)
      (pureWZ2HierarchyShadingAt schedule hdelta hdeltaOne
        hdeltaThreshold source0 level (by omega)) := by
  let current := pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
    hdeltaThreshold source0 (level + 1) hlevel
  let currentFamily := pureWZ2BuildHierarchyLevel_family schedule hdelta
    hdeltaOne hdeltaThreshold source0 (level + 1) hlevel
  have hsub : PureWZ2PaperIsSubshading
      (currentFamily ▸ current.2.shading)
      (currentFamily ▸ current.1.shading) :=
    pureWZ2_transport_subshading currentFamily current.2.subshading
  have hsource := pureWZ2BuildHierarchyLevel_source_shading_transport
    schedule hdelta hdeltaOne hdeltaThreshold source0 hlevel
  change PureWZ2PaperIsSubshading
    (currentFamily ▸ current.2.shading)
    (pureWZ2HierarchyShadingAt schedule hdelta hdeltaOne
      hdeltaThreshold source0 level (by omega))
  rw [hsource] at hsub
  exact hsub

/-- The final output shading is a subshading of every earlier hierarchy
level.  This is the finite-refinement invariant used in Lemma 25. -/
theorem pureWZ2HierarchyShadingAt_chain
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (schedule : PureWZ2BackwardScheduleData N sigma hierarchyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ schedule.commonDeltaThreshold)
    (source0 : PureWZ2QuantitativeGrainConfiguration sigma
      schedule.initialSourceCeiling delta)
    {first last : ℕ} (hfirst : first < N) (hlast : last < N)
    (horder : first ≤ last) :
    PureWZ2PaperIsSubshading
      (pureWZ2HierarchyShadingAt schedule hdelta hdeltaOne
        hdeltaThreshold source0 last hlast)
      (pureWZ2HierarchyShadingAt schedule hdelta hdeltaOne
        hdeltaThreshold source0 first hfirst) := by
  induction last with
  | zero =>
      have hfirstZero : first = 0 := by omega
      subst first
      exact fun _ => Set.Subset.rfl
  | succ previous ih =>
      by_cases heq : first = previous + 1
      · subst first
        exact fun _ => Set.Subset.rfl
      · have hfirstPrevious : first ≤ previous := by omega
        have hstep := pureWZ2HierarchyShadingAt_succ_subshading
          schedule hdelta hdeltaOne hdeltaThreshold source0 hlast
        have htail := ih (by omega) hfirstPrevious
        exact fun index => (hstep index).trans (htail index)

/-- The first retained level is a subshading of the initial source. -/
theorem pureWZ2HierarchyShadingAt_zero_subshading
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (schedule : PureWZ2BackwardScheduleData N sigma hierarchyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ schedule.commonDeltaThreshold)
    (source0 : PureWZ2QuantitativeGrainConfiguration sigma
      schedule.initialSourceCeiling delta) :
    PureWZ2PaperIsSubshading
      (pureWZ2HierarchyShadingAt schedule hdelta hdeltaOne
        hdeltaThreshold source0 0 (by
          have hN := schedule.levelCount_two
          omega))
      source0.shading := by
  have hzero : 0 < N := by
    have hN := schedule.levelCount_two
    omega
  let data := pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
    hdeltaThreshold source0 0 hzero
  let hfamily := pureWZ2BuildHierarchyLevel_family schedule hdelta
    hdeltaOne hdeltaThreshold source0 0 hzero
  exact pureWZ2_transport_subshading hfamily data.2.subshading

/-- Output of the dependent iteration before the paper's final popularity
thinning and endpoint reanchoring. -/
structure PureWZ2IteratedHierarchyData
    {sigma inputLoss delta : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (finalLoss hierarchyLoss : ℝ) where
  levelCount : ℕ
  levelCount_two : 2 ≤ levelCount
  shading : WZ1PaperTubeShading source.family
  subshading : PureWZ2PaperIsSubshading shading source.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  extremal : WZ2PaperCroppedIsExtremal
    sigma finalLoss source.family shading
  volume_lower : Kakeya.realRpowENN delta (sigma + finalLoss) ≤
    MeasureTheory.volume shading.union
  localGrains : PureWZ2LocalGrainData shading sigma
    (Kakeya.realRpowENN delta (-finalLoss))
  planeMap_vertical_bound :
    ∀ point : {point : Point3 // point ∈ shading.union},
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  sourceGlobalGrains : PureWZ2BoundedLipschitzGlobalGrainData shading sigma
    (Kakeya.realRpowENN delta (-finalLoss))
  source_slope_eq : sourceGlobalGrains.slope = source.globalGrains.slope
  trapezoids : Fin levelCount → Finset WZ1VerticalTrapezoid
  level_nonempty : ∀ level, (trapezoids level).Nonempty
  height_eq : ∀ level, ∀ trapezoid ∈ trapezoids level,
    trapezoid.height = wz1Corollary26Scale delta levelCount level
  slope_bound : ∀ level, ∀ trapezoid ∈ trapezoids level,
    |trapezoid.slope| ≤ 2
  length_bounds : ∀ level, ∀ trapezoid ∈ trapezoids level,
    Real.rpow (wz1Corollary26Scale delta levelCount level)
        (1 / 2 + hierarchyLoss) ≤ trapezoid.length ∧
      trapezoid.length ≤
        Real.sqrt (wz1Corollary26Scale delta levelCount level)
  separated_cores : ∀ level, ∀ trapezoid ∈ trapezoids level,
    ∀ other ∈ trapezoids level, trapezoid ≠ other →
      ∀ z ∈ trapezoid.core, ∀ w ∈ other.core,
        Real.sqrt (wz1Corollary26Scale delta levelCount level) ≤ |z - w|
  slope_approximation : ∀ level, ∀ trapezoid ∈ trapezoids level,
    ∀ z ∈ trapezoid.core,
      horizontalSlice shading.union z ≠ ∅ →
        |sourceGlobalGrains.slope z - trapezoid.affine z| ≤
          wz1Corollary26Scale delta levelCount level
  active_height_coverage : ∀ level, ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    horizontalSlice shading.union z ≠ ∅ →
      ∃ trapezoid ∈ trapezoids level, z ∈ trapezoid.core

/-- Assemble the outputs of the backward-scheduled one-scale calls on the
single final shading.  This is precisely the pre-popularity part of the
paper's Lemma-25 iteration. -/
theorem pureWZ2_construct_iterated_hierarchy
    {N : ℕ} {sigma hierarchyLoss delta : ℝ}
    (schedule : PureWZ2BackwardScheduleData N sigma hierarchyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdeltaThreshold : delta ≤ schedule.commonDeltaThreshold)
    (source0 : PureWZ2QuantitativeGrainConfiguration sigma
      schedule.initialSourceCeiling delta) :
    Nonempty
      (PureWZ2IteratedHierarchyData source0
        schedule.terminalLoss hierarchyLoss) := by
  let finalLevel := pureWZ2FinLast N schedule.levelCount_two
  let finalNat : ℕ := finalLevel
  have hfinalLt : finalNat < N := finalLevel.isLt
  let finalData := pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
    hdeltaThreshold source0 finalNat hfinalLt
  let finalFamily := pureWZ2BuildHierarchyLevel_family schedule hdelta
    hdeltaOne hdeltaThreshold source0 finalNat hfinalLt
  let finalShading : WZ1PaperTubeShading source0.family :=
    finalFamily ▸ finalData.2.shading
  have hfinalLoss : schedule.outputLoss ⟨finalNat, hfinalLt⟩ =
      schedule.terminalLoss := by
    change schedule.outputLoss finalLevel = schedule.terminalLoss
    exact schedule.outputLoss_last
  have hfinalScale : wz1Corollary26Scale delta N
      ⟨finalNat, hfinalLt⟩ = delta := by
    change wz1Corollary26Scale delta N finalLevel = delta
    exact pureWZ2HierarchyScale_last schedule.levelCount_two hdelta
  have hfinalSub : PureWZ2PaperIsSubshading finalShading source0.shading := by
    have hchain := pureWZ2HierarchyShadingAt_chain schedule hdelta hdeltaOne
      hdeltaThreshold source0 (first := 0) (last := finalNat)
      (by omega) hfinalLt (by
        dsimp only [finalNat, finalLevel, pureWZ2FinLast]
        omega)
    have hzero := pureWZ2HierarchyShadingAt_zero_subshading schedule hdelta
      hdeltaOne hdeltaThreshold source0
    exact fun index => (hchain index).trans (hzero index)
  have hfinalExtremalRaw := finalData.2.extremal
  have hfinalExtremal : WZ2PaperCroppedIsExtremal sigma
      schedule.terminalLoss source0.family finalShading :=
    pureWZ2_transport_cropped_extremal finalFamily
      (pureWZ2_transport_cropped_loss hfinalLoss hfinalExtremalRaw)
  have hfinalVolumeRaw := finalData.2.volume_lower
  have hfinalVolume : Kakeya.realRpowENN delta
        (sigma + schedule.terminalLoss) ≤
      MeasureTheory.volume finalShading.union := by
    have h := pureWZ2_transport_volume_loss hfinalLoss hfinalVolumeRaw
    rw [show finalShading.union = finalData.2.shading.union by
      exact pureWZ2_transport_union finalFamily finalData.2.shading]
    exact h
  let finalLocal : PureWZ2LocalGrainData finalShading sigma
      (Kakeya.realRpowENN delta (-schedule.terminalLoss)) :=
    pureWZ2_transport_localGrains finalFamily
      (pureWZ2_transport_local_loss hfinalLoss finalData.2.localGrains)
  let finalGlobal : PureWZ2BoundedLipschitzGlobalGrainData finalShading sigma
      (Kakeya.realRpowENN delta (-schedule.terminalLoss)) :=
    pureWZ2_transport_globalGrains finalFamily
      (pureWZ2_transport_global_loss hfinalLoss finalData.2.globalGrains)
  have hsourceSlope : finalGlobal.slope = source0.globalGrains.slope := by
    rw [pureWZ2_transport_global_slope finalFamily hfinalLoss
      finalData.2.globalGrains]
    exact finalData.2.slope_eq.trans
      (pureWZ2BuildHierarchyLevel_slope schedule hdelta hdeltaOne
        hdeltaThreshold source0 finalNat hfinalLt)
  have hplaneVertical : ∀ point : {point : Point3 //
      point ∈ finalShading.union},
      |finalLocal.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    exact pureWZ2_transport_plane_vertical_bound finalFamily hfinalLoss
      finalData.2.localGrains finalData.2.planeMap_vertical_bound
  let trapezoids : Fin N → Finset WZ1VerticalTrapezoid := fun level =>
    (pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 level level.isLt).2.trapezoids
  have hlevelFinal : ∀ level : Fin N, (level : ℕ) ≤ finalNat := by
    intro level
    dsimp only [finalNat, finalLevel, pureWZ2FinLast]
    omega
  have hfinalToLevel : ∀ level : Fin N,
      PureWZ2PaperIsSubshading finalShading
        (pureWZ2HierarchyShadingAt schedule hdelta hdeltaOne
          hdeltaThreshold source0 level level.isLt) := by
    intro level
    exact pureWZ2HierarchyShadingAt_chain schedule hdelta hdeltaOne
      hdeltaThreshold source0 level.isLt hfinalLt (hlevelFinal level)
  have hfinalUnion : ∀ level : Fin N, finalShading.union ⊆
      (pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
        hdeltaThreshold source0 level level.isLt).2.shading.union := by
    intro level
    have hsub := (hfinalToLevel level).union_subset
    change finalShading.union ⊆
      (pureWZ2BuildHierarchyLevel_family schedule hdelta hdeltaOne
        hdeltaThreshold source0 level level.isLt ▸
        (pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
          hdeltaThreshold source0 level level.isLt).2.shading :
          WZ1PaperTubeShading source0.family).union at hsub
    rw [pureWZ2_transport_union
      (pureWZ2BuildHierarchyLevel_family schedule hdelta hdeltaOne
        hdeltaThreshold source0 level level.isLt)
      (pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
        hdeltaThreshold source0 level level.isLt).2.shading] at hsub
    exact hsub
  refine ⟨{
    levelCount := N
    levelCount_two := schedule.levelCount_two
    shading := finalShading
    subshading := hfinalSub
    whole_cells := pureWZ2_transport_cubical finalFamily
      finalData.2.whole_cells
    extremal := hfinalExtremal
    volume_lower := hfinalVolume
    localGrains := finalLocal
    planeMap_vertical_bound := hplaneVertical
    sourceGlobalGrains := finalGlobal
    source_slope_eq := hsourceSlope
    trapezoids := trapezoids
    level_nonempty := ?_
    height_eq := ?_
    slope_bound := ?_
    length_bounds := ?_
    separated_cores := ?_
    slope_approximation := ?_
    active_height_coverage := ?_ }⟩
  · intro level
    exact (pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 level level.isLt).2.trapezoids_nonempty
  · intro level trapezoid htrapezoid
    exact (pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 level level.isLt).2.height_eq
        trapezoid htrapezoid
  · intro level trapezoid htrapezoid
    exact (pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 level level.isLt).2.slope_bound
        trapezoid htrapezoid
  · intro level trapezoid htrapezoid
    let levelData := pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 level level.isLt
    have hraw := levelData.2.length_bounds trapezoid htrapezoid
    have hloss : schedule.outputLoss level ≤ hierarchyLoss :=
      (schedule.outputLoss_le_terminal level).trans
        schedule.terminalLoss_le_hierarchyLoss
    have hscalePos := pureWZ2HierarchyScale_pos hdelta level
    have hscaleOne := pureWZ2HierarchyScale_le_one hdelta hdeltaOne level
    exact ⟨(Real.rpow_le_rpow_of_exponent_ge hscalePos hscaleOne
      (by linarith)).trans hraw.1, hraw.2⟩
  · intro level trapezoid htrapezoid other hother hne z hz w hw
    exact (pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 level level.isLt).2.separated_cores
        trapezoid htrapezoid other hother hne z hz w hw
  · intro level trapezoid htrapezoid z hz hactive
    let levelData := pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 level level.isLt
    have hslope := pureWZ2BuildHierarchyLevel_slope schedule hdelta
      hdeltaOne hdeltaThreshold source0 level level.isLt
    have hactiveLevel : horizontalSlice levelData.2.shading.union z ≠ ∅ := by
      apply Set.Nonempty.ne_empty
      apply Set.Nonempty.mono _ (Set.nonempty_iff_ne_empty.mpr hactive)
      intro point hpoint
      exact ⟨hfinalUnion level hpoint.1, hpoint.2⟩
    have hraw := levelData.2.slope_approximation trapezoid htrapezoid
      z hz hactiveLevel
    have hlevelSlope : levelData.2.globalGrains.slope =
        source0.globalGrains.slope := levelData.2.slope_eq.trans hslope
    simpa only [hsourceSlope, hlevelSlope] using hraw
  · intro level z hz hactive
    let levelData := pureWZ2BuildHierarchyLevel schedule hdelta hdeltaOne
      hdeltaThreshold source0 level level.isLt
    have hactiveLevel : horizontalSlice levelData.2.shading.union z ≠ ∅ := by
      apply Set.Nonempty.ne_empty
      apply Set.Nonempty.mono _ (Set.nonempty_iff_ne_empty.mpr hactive)
      intro point hpoint
      exact ⟨hfinalUnion level hpoint.1, hpoint.2⟩
    exact levelData.2.active_height_coverage z hz hactiveLevel

end Kakeya.Assouad
