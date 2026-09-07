import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantOneScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyExactTerminalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleLossMonotonicity

/-!
# Re-entry-preserving hierarchy prefix

The historical prefix iterator stored only the next grain configuration.  This
module records the exact dependent transition instead: every level contains
the incoming reentrant source and one `PureWZ2ReentrantOneScaleStepData`, so
the next source and next re-entry are definitionally the two projections of
the same receipt.
-/

noncomputable section

namespace Kakeya.Assouad

/-- One completed selected ordinary step, retaining the raw loss and the
selection parameters needed to recover its exact re-entry receipt. -/
structure PureWZ2ReentrantOneScaleOutput
    {sigma inputLoss delta : ℝ}
    {normalizationExponent : ℕ}
    (current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent)
    (outputLoss rho : ℝ) where
  grainLoss : ℝ
  outputEta : ℝ
  croppedMassFraction : ENNReal
  step : PureWZ2ReentrantOneScaleStepData current grainLoss outputLoss rho
    outputEta croppedMassFraction

namespace PureWZ2ReentrantOneScaleOutput

/-- The locally-linear output on the exact selected next source. -/
noncomputable def selected
    {sigma inputLoss delta outputLoss rho : ℝ}
    {normalizationExponent : ℕ}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    (output : PureWZ2ReentrantOneScaleOutput current outputLoss rho) :
    PureWZ2LocallyLinearOneScaleData output.step.nextSource outputLoss rho :=
  output.step.selectedOneScale

end PureWZ2ReentrantOneScaleOutput

/-- Source-parametric ordinary geometry with exact re-entry provenance.  The
loss and scale thresholds are chosen before the runtime dependent source. -/
def PureWZ2ReentrantOneScaleAtStatement
    (sigma : ℝ) (normalizationExponent : ℕ) : Prop :=
  ∀ outputLoss : ℝ,
    0 < sigma → sigma < 1 → 0 < outputLoss →
      ∃ sourceLossCeiling delta₀ : ℝ,
        0 < sourceLossCeiling ∧
        sourceLossCeiling ≤ outputLoss / 100 ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ inputLoss : ℝ,
          0 < inputLoss → inputLoss ≤ sourceLossCeiling →
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ current : PureWZ2ReentrantGrainSource
                sigma inputLoss delta normalizationExponent,
              ∀ rho : ℝ,
                delta ≤ rho → rho ≤ 1 →
                Real.rpow delta (1 - outputLoss) ≤ rho →
                rho ≤ Real.rpow delta outputLoss →
                  Nonempty
                    (PureWZ2ReentrantOneScaleOutput
                      current outputLoss rho)

/-- Exact-terminal geometry on the grain projection of an exact reentrant
source.  The re-entry is present at the call site and cannot be independently
reselected. -/
def PureWZ2ReentrantExactTerminalScaleAtStatement
    (sigma : ℝ) (normalizationExponent : ℕ) : Prop :=
  ∀ outputLoss : ℝ,
    0 < sigma → sigma < 1 → 0 < outputLoss →
      ∃ sourceLossCeiling delta₀ : ℝ,
        0 < sourceLossCeiling ∧
        sourceLossCeiling ≤ outputLoss / 100 ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ inputLoss : ℝ,
          0 < inputLoss → inputLoss ≤ sourceLossCeiling →
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ current : PureWZ2ReentrantGrainSource
                sigma inputLoss delta normalizationExponent,
              Nonempty
                (PureWZ2ExactTerminalLevelData current.grain outputLoss)

/-- Source-slab AD at one exact future ordinary scale and one preselected
middle loss.  The absorption is stored with the same constant as the AD
statement, so later consumers cannot combine independent witnesses. -/
def PureWZ2SourceRhoSlabADAt
    {sigma inputLoss delta : ℝ}
    {normalizationExponent : ℕ}
    (current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent)
    (targetRho middleLoss : ℝ) : Prop :=
  ∃ constant : ENNReal,
    (∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (globalGrainProjection current.grain.globalGrains.slope
          (globalGrainSlab current.grain.shading.union z targetRho))
        targetRho (1 - sigma) constant) ∧
    144 * constant ≤
      10 * Kakeya.realRpowENN targetRho (-middleLoss)

/-- A pre-scheduled family of source-slab AD certificates.  The admissibility
predicate is supplied by the finite hierarchy schedule and must include its
small-scale cutoff; no claim is made for arbitrary radii such as `rho = 1`. -/
def PureWZ2SourceRhoSlabADInvariant
    {sigma inputLoss delta : ℝ}
    {normalizationExponent : ℕ}
    (current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent)
    (admissible : ℝ → ℝ → Prop) : Prop :=
  ∀ middleLoss targetRho, admissible middleLoss targetRho →
    PureWZ2SourceRhoSlabADAt current targetRho middleLoss

/-- One synchronized transition retains a literal subshading of its incoming
grain source. -/
theorem PureWZ2ReentrantOneScaleStepData.next_union_subset_current
    {sigma inputLoss delta grainLoss outputLoss rho outputEta : ℝ}
    {normalizationExponent : ℕ}
    {croppedMassFraction : ENNReal}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    (step : PureWZ2ReentrantOneScaleStepData current grainLoss outputLoss rho
      outputEta croppedMassFraction) :
    step.next.grain.shading.union ⊆ current.grain.shading.union :=
  step.nextSource_union_subset.trans step.oneScale.subshading.union_subset

/-- The synchronized tube pruning changes neither the global slope chosen by
the raw ordinary step nor its equality with the incoming source slope. -/
theorem PureWZ2ReentrantOneScaleStepData.next_slope_eq_current
    {sigma inputLoss delta grainLoss outputLoss rho outputEta : ℝ}
    {normalizationExponent : ℕ}
    {croppedMassFraction : ENNReal}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    (step : PureWZ2ReentrantOneScaleStepData current grainLoss outputLoss rho
      outputEta croppedMassFraction) :
    step.next.grain.globalGrains.slope =
      current.grain.globalGrains.slope := by
  exact step.oneScale.slope_eq

namespace PureWZ2SourceRhoSlabADAt

/-- Restrict a fixed-radius source-slab certificate to a later source with a
literal smaller shading and the same global slope.  The AD constant and its
absorption are unchanged. -/
theorem mono
    {sigma inputLoss nextLoss delta targetRho middleLoss : ℝ}
    {normalizationExponent : ℕ}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    {next : PureWZ2ReentrantGrainSource
      sigma nextLoss delta normalizationExponent}
    (sourceSlab : PureWZ2SourceRhoSlabADAt current targetRho middleLoss)
    (hsub : next.grain.shading.union ⊆ current.grain.shading.union)
    (hslope : next.grain.globalGrains.slope =
      current.grain.globalGrains.slope) :
    PureWZ2SourceRhoSlabADAt next targetRho middleLoss := by
  rcases sourceSlab with ⟨constant, hAD, hconstant⟩
  refine ⟨constant, ?_, hconstant⟩
  intro z hz
  rw [hslope]
  apply (hAD z hz).mono
  rintro value ⟨point, hpoint, rfl⟩
  exact ⟨point,
    ⟨Set.inter_subset_inter hsub Set.Subset.rfl hpoint.1, hpoint.2⟩, rfl⟩

/-- One synchronized hierarchy transition preserves every fixed-radius
source-slab certificate without enlarging its constant. -/
theorem mono_step
    {sigma inputLoss delta grainLoss outputLoss rho outputEta targetRho
      middleLoss : ℝ}
    {normalizationExponent : ℕ}
    {croppedMassFraction : ENNReal}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    (sourceSlab : PureWZ2SourceRhoSlabADAt current targetRho middleLoss)
    (step : PureWZ2ReentrantOneScaleStepData current grainLoss outputLoss rho
      outputEta croppedMassFraction) :
    PureWZ2SourceRhoSlabADAt step.next targetRho middleLoss :=
  sourceSlab.mono step.next_union_subset_current step.next_slope_eq_current

end PureWZ2SourceRhoSlabADAt

namespace PureWZ2SourceRhoSlabADInvariant

/-- A whole pre-scheduled invariant is inherited pointwise by one selected
step.  No constants or losses are multiplied across hierarchy levels. -/
theorem mono_step
    {sigma inputLoss delta grainLoss outputLoss rho outputEta : ℝ}
    {normalizationExponent : ℕ}
    {croppedMassFraction : ENNReal}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    {admissible : ℝ → ℝ → Prop}
    (invariant : PureWZ2SourceRhoSlabADInvariant current admissible)
    (step : PureWZ2ReentrantOneScaleStepData current grainLoss outputLoss rho
      outputEta croppedMassFraction) :
    PureWZ2SourceRhoSlabADInvariant step.next admissible := by
  intro middleLoss targetRho hadmissible
  exact (invariant middleLoss targetRho hadmissible).mono_step step

end PureWZ2SourceRhoSlabADInvariant

/-- A finite forward chain of exact reentrant ordinary transitions. -/
inductive PureWZ2ReentrantPrefixChain
    (sigma delta : ℝ)
    (normalizationExponent : ℕ) :
    {inputLoss : ℝ} →
      PureWZ2ReentrantGrainSource
        sigma inputLoss delta normalizationExponent →
      ℕ → Type
  | nil
      {loss : ℝ}
      (current : PureWZ2ReentrantGrainSource
        sigma loss delta normalizationExponent) :
      PureWZ2ReentrantPrefixChain sigma delta normalizationExponent
        current 0
  | cons
      {inputLoss grainLoss outputLoss rho outputEta : ℝ}
      {croppedMassFraction : ENNReal}
      {current : PureWZ2ReentrantGrainSource
        sigma inputLoss delta normalizationExponent}
      (step : PureWZ2ReentrantOneScaleStepData current grainLoss outputLoss
        rho outputEta croppedMassFraction)
      {levelCount : ℕ}
      (tail : PureWZ2ReentrantPrefixChain sigma delta normalizationExponent
        step.next levelCount) :
      PureWZ2ReentrantPrefixChain sigma delta normalizationExponent
        current (levelCount + 1)

namespace PureWZ2ReentrantPrefixChain

/-- The literal reentrant source retained after the last transition. -/
noncomputable def finalSource
    {sigma delta : ℝ} {normalizationExponent : ℕ}
    {inputLoss : ℝ}
    {initial : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    {levelCount : ℕ}
    (chain : PureWZ2ReentrantPrefixChain sigma delta
      normalizationExponent initial levelCount) :
    Sigma fun finalLoss => PureWZ2ReentrantGrainSource
      sigma finalLoss delta normalizationExponent := by
  induction chain with
  | nil current => exact ⟨_, current⟩
  | cons _ tail ih => exact ih

/-- The final selected shading is contained in the initial grain shading. -/
theorem final_union_subset_initial
    {sigma delta : ℝ} {normalizationExponent : ℕ}
    {inputLoss : ℝ}
    {initial : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    {levelCount : ℕ}
    (chain : PureWZ2ReentrantPrefixChain sigma delta
      normalizationExponent initial levelCount) :
    chain.finalSource.2.grain.shading.union ⊆
      initial.grain.shading.union := by
  induction chain with
  | nil current => exact Set.Subset.rfl
  | cons step tail ih =>
      exact ih.trans step.next_union_subset_current

/-- Every synchronized step retains the initial global slope. -/
theorem final_slope_eq_initial
    {sigma delta : ℝ} {normalizationExponent : ℕ}
    {inputLoss : ℝ}
    {initial : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    {levelCount : ℕ}
    (chain : PureWZ2ReentrantPrefixChain sigma delta
      normalizationExponent initial levelCount) :
    chain.finalSource.2.grain.globalGrains.slope =
      initial.grain.globalGrains.slope := by
  induction chain with
  | nil current => rfl
  | cons step tail ih =>
      exact ih.trans step.next_slope_eq_current

/-- Every fixed-radius source-slab certificate on the initial source survives
the entire reentrant prefix with the same constant. -/
theorem sourceSlabADAt_final
    {sigma delta targetRho middleLoss : ℝ}
    {normalizationExponent : ℕ}
    {inputLoss : ℝ}
    {initial : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    {levelCount : ℕ}
    (chain : PureWZ2ReentrantPrefixChain sigma delta
      normalizationExponent initial levelCount)
    (sourceSlab :
      PureWZ2SourceRhoSlabADAt initial targetRho middleLoss) :
    PureWZ2SourceRhoSlabADAt chain.finalSource.2 targetRho middleLoss :=
  sourceSlab.mono chain.final_union_subset_initial
    chain.final_slope_eq_initial

/-- The full admissible source-slab invariant survives the entire prefix
pointwise, again without multiplying any loss or AD constant. -/
theorem sourceSlabADInvariant_final
    {sigma delta : ℝ}
    {normalizationExponent : ℕ}
    {inputLoss : ℝ}
    {initial : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    {levelCount : ℕ}
    (chain : PureWZ2ReentrantPrefixChain sigma delta
      normalizationExponent initial levelCount)
    {admissible : ℝ → ℝ → Prop}
    (invariant : PureWZ2SourceRhoSlabADInvariant initial admissible) :
    PureWZ2SourceRhoSlabADInvariant chain.finalSource.2 admissible := by
  intro middleLoss targetRho hadmissible
  exact chain.sourceSlabADAt_final
    (invariant middleLoss targetRho hadmissible)

/-- One level of a reentrant prefix, with all indices hidden except for the
runtime-independent ambient parameters. -/
structure LevelOutput
    (sigma delta : ℝ) (normalizationExponent : ℕ) where
  inputLoss : ℝ
  outputLoss : ℝ
  rho : ℝ
  current : PureWZ2ReentrantGrainSource
    sigma inputLoss delta normalizationExponent
  output : PureWZ2ReentrantOneScaleOutput current outputLoss rho

namespace LevelOutput

/-- The locally-linear data reindexed onto the exact next reentrant source. -/
noncomputable def selected
    {sigma delta : ℝ} {normalizationExponent : ℕ}
    (output : LevelOutput sigma delta normalizationExponent) :
    PureWZ2LocallyLinearOneScaleData output.output.step.nextSource
      output.outputLoss output.rho :=
  output.output.selected

end LevelOutput

/-- Read the selected ordinary output at one position of an arbitrary
reentrant chain. -/
noncomputable def outputAt
    {sigma delta : ℝ} {normalizationExponent : ℕ}
    {inputLoss : ℝ}
    {initial : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    {levelCount : ℕ}
    (chain : PureWZ2ReentrantPrefixChain sigma delta
      normalizationExponent initial levelCount)
    (level : Fin levelCount) :
    LevelOutput sigma delta normalizationExponent := by
  induction chain with
  | nil current =>
      exact Fin.elim0 level
  | @cons inputLoss grainLoss outputLoss rho outputEta
      croppedMassFraction current step levelCount tail ih =>
      refine Fin.cases ?_ (fun next => ih next) level
      exact {
        inputLoss := inputLoss
        outputLoss := outputLoss
        rho := rho
        current := current
        output := {
          grainLoss := grainLoss
          outputEta := outputEta
          croppedMassFraction := croppedMassFraction
          step := step } }

@[simp] theorem finalSource_cons
    {sigma delta : ℝ} {normalizationExponent : ℕ}
    {inputLoss grainLoss outputLoss rho outputEta : ℝ}
    {croppedMassFraction : ENNReal}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    (step : PureWZ2ReentrantOneScaleStepData current grainLoss outputLoss
      rho outputEta croppedMassFraction)
    {levelCount : ℕ}
    (tail : PureWZ2ReentrantPrefixChain sigma delta
      normalizationExponent step.next levelCount) :
    (PureWZ2ReentrantPrefixChain.cons step tail).finalSource =
      tail.finalSource := by
  rfl

@[simp] theorem outputAt_cons_zero
    {sigma delta : ℝ} {normalizationExponent : ℕ}
    {inputLoss grainLoss outputLoss rho outputEta : ℝ}
    {croppedMassFraction : ENNReal}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    (step : PureWZ2ReentrantOneScaleStepData current grainLoss outputLoss
      rho outputEta croppedMassFraction)
    {levelCount : ℕ}
    (tail : PureWZ2ReentrantPrefixChain sigma delta
      normalizationExponent step.next levelCount) :
    (PureWZ2ReentrantPrefixChain.cons step tail).outputAt
        (0 : Fin (levelCount + 1)) =
      { inputLoss := inputLoss
        outputLoss := outputLoss
        rho := rho
        current := current
        output := {
          grainLoss := grainLoss
          outputEta := outputEta
          croppedMassFraction := croppedMassFraction
          step := step } } := by
  rfl

@[simp] theorem outputAt_cons_succ
    {sigma delta : ℝ} {normalizationExponent : ℕ}
    {inputLoss grainLoss outputLoss rho outputEta : ℝ}
    {croppedMassFraction : ENNReal}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    (step : PureWZ2ReentrantOneScaleStepData current grainLoss outputLoss
      rho outputEta croppedMassFraction)
    {levelCount : ℕ}
    (tail : PureWZ2ReentrantPrefixChain sigma delta
      normalizationExponent step.next levelCount)
    (level : Fin levelCount) :
    (PureWZ2ReentrantPrefixChain.cons step tail).outputAt level.succ =
      tail.outputAt level := by
  rfl

/-- The final chain shading is contained in every selected ordinary output,
not merely in the initial source. -/
theorem final_union_subset_outputAt
    {sigma delta : ℝ} {normalizationExponent : ℕ}
    {inputLoss : ℝ}
    {initial : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    {levelCount : ℕ}
    (chain : PureWZ2ReentrantPrefixChain sigma delta
      normalizationExponent initial levelCount)
    (level : Fin levelCount) :
    chain.finalSource.2.grain.shading.union ⊆
      (chain.outputAt level).selected.shading.union := by
  induction chain with
  | nil current =>
      exact Fin.elim0 level
  | cons step tail ih =>
      refine Fin.cases ?_ (fun next => ih next) level
      change tail.finalSource.2.grain.shading.union ⊆
        step.next.grain.shading.union
      exact tail.final_union_subset_initial

/-- The final chain slope agrees with the slope in every selected ordinary
output. -/
theorem final_slope_eq_outputAt
    {sigma delta : ℝ} {normalizationExponent : ℕ}
    {inputLoss : ℝ}
    {initial : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    {levelCount : ℕ}
    (chain : PureWZ2ReentrantPrefixChain sigma delta
      normalizationExponent initial levelCount)
    (level : Fin levelCount) :
    chain.finalSource.2.grain.globalGrains.slope =
      (chain.outputAt level).selected.globalGrains.slope := by
  induction chain with
  | nil current =>
      exact Fin.elim0 level
  | cons step tail ih =>
      refine Fin.cases ?_ (fun next => ih next) level
      change tail.finalSource.2.grain.globalGrains.slope =
        step.next.grain.globalGrains.slope
      exact tail.final_slope_eq_initial

/-- The loss index of a nonempty chain's final source is the output loss of
its last selected ordinary level. -/
theorem finalSource_loss_eq_last_outputAt
    {sigma delta : ℝ} {normalizationExponent : ℕ}
    {inputLoss : ℝ}
    {initial : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    {levelCount : ℕ}
    (chain : PureWZ2ReentrantPrefixChain sigma delta
      normalizationExponent initial levelCount)
    (hlevelCount : 0 < levelCount) :
    chain.finalSource.1 =
      (chain.outputAt ⟨levelCount - 1, by omega⟩).outputLoss := by
  induction chain with
  | nil current => omega
  | @cons inputLoss grainLoss outputLoss rho outputEta
      croppedMassFraction current step levelCount tail ih =>
      by_cases htail : levelCount = 0
      · subst levelCount
        cases tail
        rfl
      · have htailPos : 0 < levelCount := by omega
        rw [finalSource_cons]
        let lastTail : Fin levelCount := ⟨levelCount - 1, by omega⟩
        have hlast :
            (⟨levelCount + 1 - 1, by omega⟩ : Fin (levelCount + 1)) =
              lastTail.succ := by
          apply Fin.ext
          change levelCount + 1 - 1 = (levelCount - 1) + 1
          omega
        rw [hlast, outputAt_cons_succ]
        exact ih htailPos

/-- Runtime-independent evidence that an arbitrary reentrant chain occupies
exactly the first `N - 1` paper scales and spends at most the hierarchy loss
at every ordinary level. -/
structure IsHierarchyPrefix
    {sigma delta : ℝ} {normalizationExponent : ℕ}
    {inputLoss : ℝ}
    {initial : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    {levelCount : ℕ}
    (chain : PureWZ2ReentrantPrefixChain sigma delta
      normalizationExponent initial levelCount)
    (hierarchyLoss : ℝ) (N : ℕ) : Prop where
  levelCount_two : 2 ≤ N
  levelCount_succ : levelCount + 1 = N
  outputLoss_le : ∀ level : Fin levelCount,
    (chain.outputAt level).outputLoss ≤ hierarchyLoss
  rho_eq : ∀ level : Fin levelCount,
    (chain.outputAt level).rho =
      wz1Corollary26Scale delta N
        ⟨level, by omega⟩

private theorem horizontalSlice_nonempty_mono
    {first second : Set Point3} {z : ℝ}
    (subset : first ⊆ second)
    (active : horizontalSlice first z ≠ ∅) :
    horizontalSlice second z ≠ ∅ := by
  apply Set.Nonempty.ne_empty
  apply Set.Nonempty.mono _ (Set.nonempty_iff_ne_empty.mpr active)
  intro point hpoint
  exact ⟨subset hpoint.1, hpoint.2⟩

/-- Forget re-entry only after an arbitrary dependent chain has reached its
literal final source.  Every ordinary level is transported to that final
carrier using final-subset active-height propagation and the common slope. -/
noncomputable def toOrdinaryPrefix
    {sigma delta hierarchyLoss : ℝ} {normalizationExponent : ℕ}
    {inputLoss : ℝ}
    {initial : PureWZ2ReentrantGrainSource
      sigma inputLoss delta normalizationExponent}
    {levelCount N : ℕ}
    (chain : PureWZ2ReentrantPrefixChain sigma delta
      normalizationExponent initial levelCount)
    (compatible : chain.IsHierarchyPrefix hierarchyLoss N) :
    PureWZ2OrdinaryHierarchyPrefixData chain.finalSource.2.grain
      hierarchyLoss N := by
  have hlevelCount : levelCount + 1 = N :=
    compatible.levelCount_succ
  let outputAtLevel := fun (level : Fin N)
      (hlevel : (level : ℕ) + 1 < N) =>
    chain.outputAt (⟨level, by omega⟩ : Fin levelCount)
  let trapezoids : ∀ level : Fin N, (level : ℕ) + 1 < N →
      Finset WZ1VerticalTrapezoid := fun level hlevel =>
    (outputAtLevel level hlevel).selected.trapezoids
  refine {
    levelCount_two := compatible.levelCount_two
    trapezoids := trapezoids
    level_nonempty := ?_
    height_eq := ?_
    slope_bound := ?_
    length_bounds := ?_
    separated_cores := ?_
    slope_approximation := ?_
    active_height_coverage := ?_ }
  · intro level hlevel
    exact (outputAtLevel level hlevel).selected.trapezoids_nonempty
  · intro level hlevel trapezoid htrapezoid
    let prefixLevel : Fin levelCount := ⟨level, by omega⟩
    have hrho := compatible.rho_eq prefixLevel
    exact ((outputAtLevel level hlevel).selected.height_eq
      trapezoid htrapezoid).trans hrho
  · intro level hlevel trapezoid htrapezoid
    exact (outputAtLevel level hlevel).selected.slope_bound
      trapezoid htrapezoid
  · intro level hlevel trapezoid htrapezoid
    let prefixLevel : Fin levelCount := ⟨level, by omega⟩
    let output := outputAtLevel level hlevel
    have hrho := compatible.rho_eq prefixLevel
    have hloss := compatible.outputLoss_le prefixLevel
    have hraw := output.selected.length_bounds trapezoid htrapezoid
    have hlower : Real.rpow output.rho (1 / 2 + hierarchyLoss) ≤
        Real.rpow output.rho (1 / 2 + output.outputLoss) :=
      Real.rpow_le_rpow_of_exponent_ge output.selected.rho_pos
        output.selected.rho_le_one (by linarith)
    constructor
    · rw [← hrho]
      exact hlower.trans hraw.1
    · rw [← hrho]
      exact hraw.2
  · intro level hlevel trapezoid htrapezoid other hother hne
    let prefixLevel : Fin levelCount := ⟨level, by omega⟩
    have hrho := compatible.rho_eq prefixLevel
    rw [← hrho]
    exact (outputAtLevel level hlevel).selected.separated_cores
      trapezoid htrapezoid other hother hne
  · intro level hlevel trapezoid htrapezoid z hz hactive
    let prefixLevel : Fin levelCount := ⟨level, by omega⟩
    let output := outputAtLevel level hlevel
    have hsubset := chain.final_union_subset_outputAt prefixLevel
    have hslope := chain.final_slope_eq_outputAt prefixLevel
    have hrho := compatible.rho_eq prefixLevel
    rw [hslope, ← hrho]
    exact output.selected.slope_approximation trapezoid htrapezoid z hz
      (horizontalSlice_nonempty_mono hsubset hactive)
  · intro level hlevel z hz hactive
    let prefixLevel : Fin levelCount := ⟨level, by omega⟩
    let output := outputAtLevel level hlevel
    exact output.selected.active_height_coverage z hz
      (horizontalSlice_nonempty_mono
        (chain.final_union_subset_outputAt prefixLevel) hactive)

/-- The exact terminal call is applied to the grain projection of the final
reentrant source; the matching re-entry remains available for the terminal
producer and cannot be replaced by a separately selected witness. -/
structure ExactTerminalOutput
    {sigma delta finalLoss : ℝ}
    {normalizationExponent : ℕ}
    (final : PureWZ2ReentrantGrainSource
      sigma finalLoss delta normalizationExponent)
    (outputLoss : ℝ) where
  terminal : PureWZ2ExactTerminalLevelData final.grain outputLoss

end PureWZ2ReentrantPrefixChain

/-- The three ordinary levels preceding the exact terminal level when the
fixed total hierarchy depth is four.  Each output is indexed by the exact
next reentrant source of its predecessor. -/
structure PureWZ2ReentrantThreeStepPrefixData
    {sigma initialLoss delta hierarchyLoss : ℝ}
    {normalizationExponent : ℕ}
    (initial : PureWZ2ReentrantGrainSource
      sigma initialLoss delta normalizationExponent) where
  firstLoss : ℝ
  first : PureWZ2ReentrantOneScaleOutput initial firstLoss
    (wz1Corollary26Scale delta 4 ⟨0, by omega⟩)
  first_loss_le : firstLoss ≤ hierarchyLoss
  secondLoss : ℝ
  second : PureWZ2ReentrantOneScaleOutput first.step.next secondLoss
    (wz1Corollary26Scale delta 4 ⟨1, by omega⟩)
  second_loss_le : secondLoss ≤ hierarchyLoss
  thirdLoss : ℝ
  third : PureWZ2ReentrantOneScaleOutput second.step.next thirdLoss
    (wz1Corollary26Scale delta 4 ⟨2, by omega⟩)
  third_loss_le : thirdLoss ≤ hierarchyLoss

namespace PureWZ2ReentrantThreeStepPrefixData

variable
    {sigma initialLoss delta hierarchyLoss : ℝ}
    {normalizationExponent : ℕ}
    {initial : PureWZ2ReentrantGrainSource
      sigma initialLoss delta normalizationExponent}
    (data : PureWZ2ReentrantThreeStepPrefixData
      (hierarchyLoss := hierarchyLoss) initial)

/-- The exact source retained after all three ordinary levels. -/
noncomputable abbrev final := data.third.step.next

private theorem final_union_subset_first :
    data.final.grain.shading.union ⊆ data.first.selected.shading.union := by
  exact data.third.step.next_union_subset_current |>.trans
    (data.second.step.next_union_subset_current)

private theorem final_union_subset_second :
    data.final.grain.shading.union ⊆ data.second.selected.shading.union :=
  data.third.step.next_union_subset_current

private theorem final_slope_eq_first :
    data.final.grain.globalGrains.slope =
      data.first.selected.globalGrains.slope := by
  exact data.third.step.next_slope_eq_current.trans
    data.second.step.next_slope_eq_current

private theorem final_slope_eq_second :
    data.final.grain.globalGrains.slope =
      data.second.selected.globalGrains.slope :=
  data.third.step.next_slope_eq_current

private theorem activeSlice_of_union_subset
    {first second : Set Point3} {z : ℝ}
    (subset : first ⊆ second)
    (active : horizontalSlice first z ≠ ∅) :
    horizontalSlice second z ≠ ∅ := by
  apply Set.Nonempty.ne_empty
  apply Set.Nonempty.mono _ (Set.nonempty_iff_ne_empty.mpr active)
  intro point hpoint
  exact ⟨subset hpoint.1, hpoint.2⟩

/-- Forget the re-entry witnesses only after the three ordinary levels have
been produced on one dependent chain. -/
noncomputable def toOrdinaryPrefix :
    PureWZ2OrdinaryHierarchyPrefixData data.final.grain hierarchyLoss 4 := by
  let trapezoids : ∀ level : Fin 4, (level : ℕ) + 1 < 4 →
      Finset WZ1VerticalTrapezoid := fun level _ =>
    if level.1 = 0 then data.first.selected.trapezoids
    else if level.1 = 1 then data.second.selected.trapezoids
    else data.third.selected.trapezoids
  refine {
    levelCount_two := by omega
    trapezoids := trapezoids
    level_nonempty := ?_
    height_eq := ?_
    slope_bound := ?_
    length_bounds := ?_
    separated_cores := ?_
    slope_approximation := ?_
    active_height_coverage := ?_ }
  · intro level hlevel
    have hlevelVal : (level : ℕ) < 3 := by omega
    fin_cases level <;> simp_all [trapezoids]
    all_goals first | exact data.first.selected.trapezoids_nonempty |
      exact data.second.selected.trapezoids_nonempty |
      exact data.third.selected.trapezoids_nonempty
  · intro level hlevel trapezoid htrapezoid
    have hlevelVal : (level : ℕ) < 3 := by omega
    fin_cases level <;> simp_all [trapezoids]
    · simpa using data.first.selected.height_eq trapezoid htrapezoid
    · simpa using data.second.selected.height_eq trapezoid htrapezoid
    · simpa using data.third.selected.height_eq trapezoid htrapezoid
  · intro level hlevel trapezoid htrapezoid
    have hlevelVal : (level : ℕ) < 3 := by omega
    fin_cases level <;> simp_all [trapezoids]
    · exact data.first.selected.slope_bound trapezoid htrapezoid
    · exact data.second.selected.slope_bound trapezoid htrapezoid
    · exact data.third.selected.slope_bound trapezoid htrapezoid
  · intro level hlevel trapezoid htrapezoid
    have hlevelVal : (level : ℕ) < 3 := by omega
    fin_cases level <;> simp_all [trapezoids]
    · have lower : Real.rpow
          (wz1Corollary26Scale delta 4 (0 : Fin 4))
          (1 / 2 + hierarchyLoss) ≤
          Real.rpow (wz1Corollary26Scale delta 4 (0 : Fin 4))
            (1 / 2 + data.firstLoss) :=
        Real.rpow_le_rpow_of_exponent_ge data.first.selected.rho_pos
          data.first.selected.rho_le_one (by linarith [data.first_loss_le])
      constructor
      · simpa [one_div] using lower.trans
          (data.first.selected.length_bounds trapezoid htrapezoid).1
      · simpa using
          (data.first.selected.length_bounds trapezoid htrapezoid).2
    · have lower : Real.rpow
          (wz1Corollary26Scale delta 4 (1 : Fin 4))
          (1 / 2 + hierarchyLoss) ≤
          Real.rpow (wz1Corollary26Scale delta 4 (1 : Fin 4))
            (1 / 2 + data.secondLoss) :=
        Real.rpow_le_rpow_of_exponent_ge data.second.selected.rho_pos
          data.second.selected.rho_le_one (by linarith [data.second_loss_le])
      constructor
      · simpa [one_div] using lower.trans
          (data.second.selected.length_bounds trapezoid htrapezoid).1
      · simpa using
          (data.second.selected.length_bounds trapezoid htrapezoid).2
    · have lower : Real.rpow
          (wz1Corollary26Scale delta 4 (2 : Fin 4))
          (1 / 2 + hierarchyLoss) ≤
          Real.rpow (wz1Corollary26Scale delta 4 (2 : Fin 4))
            (1 / 2 + data.thirdLoss) :=
        Real.rpow_le_rpow_of_exponent_ge data.third.selected.rho_pos
          data.third.selected.rho_le_one (by linarith [data.third_loss_le])
      constructor
      · simpa [one_div] using lower.trans
          (data.third.selected.length_bounds trapezoid htrapezoid).1
      · simpa using
          (data.third.selected.length_bounds trapezoid htrapezoid).2
  · intro level hlevel trapezoid htrapezoid other hother hne
    have hlevelVal : (level : ℕ) < 3 := by omega
    fin_cases level <;> simp_all [trapezoids]
    · simpa using data.first.selected.separated_cores trapezoid htrapezoid
        other hother hne
    · simpa using data.second.selected.separated_cores trapezoid htrapezoid
        other hother hne
    · simpa using data.third.selected.separated_cores trapezoid htrapezoid
        other hother hne
  · intro level hlevel trapezoid htrapezoid z hz hactive
    have hlevelVal : (level : ℕ) < 3 := by omega
    fin_cases level <;> simp_all [trapezoids]
    · rw [data.final_slope_eq_first]
      exact data.first.selected.slope_approximation trapezoid htrapezoid z hz
        (activeSlice_of_union_subset data.final_union_subset_first hactive)
    · rw [data.final_slope_eq_second]
      exact data.second.selected.slope_approximation trapezoid htrapezoid z hz
        (activeSlice_of_union_subset data.final_union_subset_second hactive)
    · exact data.third.selected.slope_approximation trapezoid htrapezoid z hz
        hactive
  · intro level hlevel z hz hactive
    have hlevelVal : (level : ℕ) < 3 := by omega
    fin_cases level <;> simp_all [trapezoids]
    · exact data.first.selected.active_height_coverage z hz
        (activeSlice_of_union_subset data.final_union_subset_first hactive)
    · exact data.second.selected.active_height_coverage z hz
        (activeSlice_of_union_subset data.final_union_subset_second hactive)
    · exact data.third.selected.active_height_coverage z hz hactive

end PureWZ2ReentrantThreeStepPrefixData

/-- Append the exact terminal level to the fixed three-step reentrant prefix.
The terminal is evaluated on the precise final grain source of the prefix. -/
theorem PureWZ2ReentrantThreeStepPrefixData.appendExactTerminal
    {sigma initialLoss delta hierarchyLoss finalLoss : ℝ}
    {normalizationExponent : ℕ}
    {initial : PureWZ2ReentrantGrainSource
      sigma initialLoss delta normalizationExponent}
    (ordinary : PureWZ2ReentrantThreeStepPrefixData
      (hierarchyLoss := hierarchyLoss) initial)
    (terminal : PureWZ2ExactTerminalLevelData ordinary.final.grain finalLoss)
    (hfinalHierarchy : finalLoss ≤ hierarchyLoss) :
    Nonempty (PureWZ2MixedRawHierarchyData
      ordinary.final.grain finalLoss hierarchyLoss) := by
  exact ordinary.toOrdinaryPrefix.appendExactTerminal terminal hfinalHierarchy

end Kakeya.Assouad

end
