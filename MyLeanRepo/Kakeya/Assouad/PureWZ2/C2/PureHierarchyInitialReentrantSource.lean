import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantSource

/-!
# Initial reentrant source for the Pure WZ2 hierarchy

The public Node 3 root already fixes one exact cropped family, shading, and
ordinary re-entry witness.  Its re-entry data supplies the line class,
cubicality, cropped extremality, and top-level CWA on that exact pair.  The
public Node 4 existence theorem, however, selects a separate grain
configuration and therefore cannot provide grain data on the root pair.

This file isolates the remaining same-witness payload, constructs the exact
initial reentrant source once that payload is supplied, and records the
strictly weaker fork that the current public inputs do construct.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- The bundled analytic grain payload which cannot be projected from the
current public root or from an independently existential Node 4 output. -/
structure PureWZ2HierarchyInitialAnalyticGrains
    {sigma loss delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) where
  globalGrains :
    PureWZ2LipschitzGlobalGrainData shading sigma
      (Kakeya.realRpowENN delta (-loss))
  localGrains :
    PureWZ2LocalGrainData shading sigma
      (Kakeya.realRpowENN delta (-loss))
  planeMap_vertical_bound :
    ∀ point : {point : Point3 // point ∈ shading.union},
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  slope_bound :
    ∀ z : ℝ, z ∈ Set.Icc (-1 : ℝ) 1 →
      |globalGrains.slope z| ≤ 3

/-- The exact same-root fields not derivable from the current public inputs.
The lower-volume inequality is kept separate from the bundled analytic grain
object because it is the scalar critical-floor boundary. -/
structure PureWZ2HierarchyInitialGrainFields
    {sigma loss delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) where
  volume_lower :
    Kakeya.realRpowENN delta (sigma + loss) ≤ volume shading.union
  analytic : PureWZ2HierarchyInitialAnalyticGrains
    (sigma := sigma) (loss := loss) shading

namespace PureWZ2HierarchyInitialGrainFields

/-- Combine the exact root re-entry structure with its missing analytic grain
payload.  Family and shading are definitionally shared. -/
noncomputable def toReentrantGrainSource
    {sigma sourceLoss normalizationLoss delta : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {normalizationExponent : ℕ}
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss)
    (fields : PureWZ2HierarchyInitialGrainFields
      (sigma := sigma) (loss := normalizationLoss) croppedShading)
    (ordinaryAxialWindowEighth :
      ∀ index point,
        point ∈
            reentry.geometry.frame ''
              reentry.geometry.ordinaryRefined.carrier index →
          |point (2 : Fin 3)| ≤ 1 / 8) :
    PureWZ2ReentrantGrainSource
      sigma normalizationLoss delta normalizationExponent where
  ordinaryLoss := sourceLoss
  grain := {
    family := croppedFamily
    shading := croppedShading
    line_class := reentry.geometry.line_class
    cubical := reentry.geometry.cropped_cubical
    extremal := reentry.cropped_extremal
    top_level_cwa := reentry.cropped_top_level_cwa
    volume_lower := fields.volume_lower
    globalGrains :=
      PureWZ2BoundedLipschitzGlobalGrainData.ofSlopeBound
        fields.analytic.globalGrains fields.analytic.slope_bound
    localGrains := fields.analytic.localGrains
    planeMap_vertical_bound := fields.analytic.planeMap_vertical_bound
  }
  reentry := reentry
  ordinary_axial_window_eighth := ordinaryAxialWindowEighth

end PureWZ2HierarchyInitialGrainFields

/-- The missing analytic payload specialized to one exact Node 3 root. -/
structure PureWZ2HierarchyInitialRootGrainFields
    {sigma outputLoss scaleCeiling : ℝ}
    {normalizationExponent logExponent : ℕ}
    (root : PureWZ2PropStickyReentrantRootRealizationData
      (sigma := sigma) (outputLoss := outputLoss)
      (scaleCeiling := scaleCeiling) normalizationExponent logExponent) where
  grainFields : PureWZ2HierarchyInitialGrainFields
    (sigma := sigma) (loss := root.realization.normalizationLoss)
    root.realization.normalized.croppedRefined
  ordinary_axial_window_eighth :
    ∀ index point,
      point ∈
          root.rootReentry.geometry.frame ''
            root.rootReentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8

/-- The exact additional field needed beyond the current public inputs.

The root and its analytic grain fields are selected inside one dependent
existential.  This deliberately does not quantify an unrelated grain
configuration and later ask for equality of existential witnesses. -/
def PureWZ2HierarchyInitialRootGrainField
    (capability : PureWZ2PropStickyCapability) : Prop :=
  ∀ sigma : ℝ,
    PureWZ2CriticalPackage sigma →
      ∀ outputLoss sourceDelta₀ : ℝ,
        0 < outputLoss → 0 < sourceDelta₀ →
          Nonempty
            (Sigma fun root :
              PureWZ2PropStickyReentrantRootRealizationData
                (sigma := sigma) (outputLoss := outputLoss)
                (scaleCeiling := sourceDelta₀)
                capability.normalizationExponent capability.logExponent =>
              PureWZ2HierarchyInitialRootGrainFields root)

/-- The existential initial source required by the reentrant hierarchy. -/
def PureWZ2HierarchyInitialReentrantSourceConclusion
    (capability : PureWZ2PropStickyCapability)
    (sigma outputLoss sourceDelta₀ : ℝ) : Prop :=
  ∃ sourceLoss sourceDelta : ℝ,
    0 < sourceLoss ∧
      sourceLoss < outputLoss ∧
      0 < sourceDelta ∧
      sourceDelta ≤ sourceDelta₀ ∧
      Nonempty
        (PureWZ2ReentrantGrainSource sigma sourceLoss sourceDelta
          capability.normalizationExponent)

/-- Pointwise producer for the initial reentrant hierarchy source.

Unlike the historical root-indexed boundaries below, this interface asks only
for the dependent grain/re-entry pair consumed by the hierarchy.  A concrete
Proposition 6.3 construction may therefore return its own exact pair without
identifying it with a separately selected `capability.rootReentrant` witness. -/
def PureWZ2HierarchyInitialReentrantSourceAt
    (capability : PureWZ2PropStickyCapability) (sigma : ℝ) : Prop :=
  ∀ outputLoss sourceDelta₀ : ℝ,
    0 < outputLoss → 0 < sourceDelta₀ →
      PureWZ2HierarchyInitialReentrantSourceConclusion
        capability sigma outputLoss sourceDelta₀

/-- Once the single same-root analytic field is available, the current public
inputs construct the desired initial reentrant hierarchy source. -/
theorem pureWZ2_hierarchy_initial_reentrant_source_of_root_grain_field
    (capability : PureWZ2PropStickyCapability)
    (_paperADBridge : PureWZ2PaperADBridgeStatement)
    (_grainsFromCritical : PureWZ2GrainsFromCriticalStatement)
    (rootGrain : PureWZ2HierarchyInitialRootGrainField capability)
    {sigma : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    {outputLoss sourceDelta₀ : ℝ}
    (outputLoss_pos : 0 < outputLoss)
    (sourceDelta₀_pos : 0 < sourceDelta₀) :
    PureWZ2HierarchyInitialReentrantSourceConclusion
      capability sigma outputLoss sourceDelta₀ := by
  rcases rootGrain sigma critical outputLoss sourceDelta₀
      outputLoss_pos sourceDelta₀_pos with ⟨⟨root, fields⟩⟩
  refine
    ⟨root.realization.normalizationLoss, root.realization.delta,
      root.realization.normalizationLoss_pos,
      root.realization.normalizationLoss_lt_continuation.trans
        root.realization.continuationLoss_lt_output,
      root.realization.delta_pos, root.realization.delta_le_ceiling, ?_⟩
  exact
    ⟨fields.grainFields.toReentrantGrainSource root.rootReentry
      fields.ordinary_axial_window_eighth⟩

/-- What the existing public root and public grain theorem currently provide:
one reentrant root and a separate grain witness at the same loss budget, but
possibly at a different scale, family, and shading. -/
structure PureWZ2HierarchyInitialPublicWitnessFork
    {sigma outputLoss sourceDelta₀ : ℝ}
    {normalizationExponent logExponent : ℕ}
    (root : PureWZ2PropStickyReentrantRootRealizationData
      (sigma := sigma) (outputLoss := outputLoss)
      (scaleCeiling := sourceDelta₀) normalizationExponent logExponent) where
  grainDelta : ℝ
  grainDelta_pos : 0 < grainDelta
  grainDelta_le_ceiling : grainDelta ≤ sourceDelta₀
  independentGrain :
    PureWZ2GrainConfiguration
      sigma root.realization.normalizationLoss grainDelta

/-- The four current public inputs reach exactly the independent-witness fork.
The AD bridge has no equality principle capable of identifying the two
existentially selected configurations. -/
theorem pureWZ2_hierarchy_initial_public_inputs_fork
    (capability : PureWZ2PropStickyCapability)
    (_paperADBridge : PureWZ2PaperADBridgeStatement)
    (grainsFromCritical : PureWZ2GrainsFromCriticalStatement)
    {sigma : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    {outputLoss sourceDelta₀ : ℝ}
    (outputLoss_pos : 0 < outputLoss)
    (sourceDelta₀_pos : 0 < sourceDelta₀) :
    Nonempty
      (Sigma fun root :
        PureWZ2PropStickyReentrantRootRealizationData
          (sigma := sigma) (outputLoss := outputLoss)
          (scaleCeiling := sourceDelta₀)
          capability.normalizationExponent capability.logExponent =>
        PureWZ2HierarchyInitialPublicWitnessFork root) := by
  rcases capability.rootReentrant sigma critical outputLoss sourceDelta₀
      outputLoss_pos sourceDelta₀_pos with ⟨root⟩
  rcases grainsFromCritical sigma critical
      root.realization.normalizationLoss sourceDelta₀
      root.realization.normalizationLoss_pos sourceDelta₀_pos with
    ⟨grainDelta, grainDelta_pos, grainDelta_le_ceiling, ⟨independentGrain⟩⟩
  exact
    ⟨⟨root,
      { grainDelta := grainDelta
        grainDelta_pos := grainDelta_pos
        grainDelta_le_ceiling := grainDelta_le_ceiling
        independentGrain := independentGrain }⟩⟩

/-- The strongest same-family conclusion obtained by adding the historical
`PureWZ2GrainsAtExtremizerStatement`: the grain refinement lives on the
root family, but the re-entry certificate still lives on the unrefined root
shading.  An additional dependent re-entry restriction theorem is therefore
required before this can become a `PureWZ2ReentrantGrainSource`. -/
structure PureWZ2HierarchyInitialRootRefinementFork
    {sigma inputLoss outputLoss scaleCeiling : ℝ}
    {normalizationExponent logExponent : ℕ}
    (root : PureWZ2PropStickyReentrantRootRealizationData
      (sigma := sigma) (outputLoss := inputLoss)
      (scaleCeiling := scaleCeiling) normalizationExponent logExponent) where
  refinement : PureWZ2GrainRefinementData
    root.realization.normalized.croppedRefined sigma outputLoss

/-- Compatibility package for the forthcoming Node 4 result.  The grain
refinement is indexed by the exact Node 3 root, and its re-entry certificate
is indexed by the exact refined shading.  Consumers therefore need no access
to the trace fields used to construct that certificate. -/
structure PureWZ2HierarchyExactReentryIndexedRefinement
    {sigma rootLoss outputLoss scaleCeiling : ℝ}
    {normalizationExponent logExponent : ℕ}
    (root : PureWZ2PropStickyReentrantRootRealizationData
      (sigma := sigma) (outputLoss := rootLoss)
      (scaleCeiling := scaleCeiling) normalizationExponent logExponent) where
  refinement : PureWZ2GrainRefinementData
    root.realization.normalized.croppedRefined sigma outputLoss
  slope_bound :
    ∀ z : ℝ, z ∈ Set.Icc (-1 : ℝ) 1 →
      |refinement.globalGrains.slope z| ≤ 3
  reentry : PureWZ2PropStickyReentryData
    (sigma := sigma) refinement.shading normalizationExponent
    root.realization.sourceLoss outputLoss
  ordinary_axial_window_eighth :
    ∀ index point,
      point ∈
          reentry.geometry.frame ''
            reentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8

namespace PureWZ2HierarchyExactReentryIndexedRefinement

/-- Forget the construction details and expose the exact initial hierarchy
state. -/
noncomputable def toReentrantGrainSource
    {sigma rootLoss outputLoss scaleCeiling : ℝ}
    {normalizationExponent logExponent : ℕ}
    {root : PureWZ2PropStickyReentrantRootRealizationData
      (sigma := sigma) (outputLoss := rootLoss)
      (scaleCeiling := scaleCeiling) normalizationExponent logExponent}
    (data : PureWZ2HierarchyExactReentryIndexedRefinement
      (outputLoss := outputLoss) root) :
    PureWZ2ReentrantGrainSource sigma outputLoss root.realization.delta
      normalizationExponent where
  ordinaryLoss := root.realization.sourceLoss
  grain := data.refinement.toQuantitativeGrainConfiguration data.slope_bound
  reentry := data.reentry
  ordinary_axial_window_eighth := data.ordinary_axial_window_eighth

end PureWZ2HierarchyExactReentryIndexedRefinement

/-- Quantifier-ordered adapter expected from a future exact Node 4 producer.
The root loss and scale cutoff are selected before the runtime root; the
producer then returns the refinement and re-entry as one dependent object. -/
structure PureWZ2HierarchyExactReentryIndexedRefinementSchedule
    (capability : PureWZ2PropStickyCapability)
    (sigma outputLoss : ℝ) where
  rootLoss : ℝ
  delta₀ : ℝ
  rootLoss_pos : 0 < rootLoss
  delta₀_pos : 0 < delta₀
  produce :
    ∀ scaleCeiling : ℝ,
      0 < scaleCeiling → scaleCeiling ≤ delta₀ →
        ∀ root : PureWZ2PropStickyReentrantRootRealizationData
          (sigma := sigma) (outputLoss := rootLoss)
          (scaleCeiling := scaleCeiling)
          capability.normalizationExponent capability.logExponent,
          Nonempty
            (PureWZ2HierarchyExactReentryIndexedRefinement
              (outputLoss := outputLoss) root)

/-- Name-independent compatibility type for the future Node 4 theorem. -/
def PureWZ2HierarchyExactReentryIndexedRefinementProducer
    (capability : PureWZ2PropStickyCapability) : Prop :=
  ∀ sigma : ℝ,
    PureWZ2CriticalPackage sigma →
      ∀ outputLoss : ℝ, 0 < outputLoss →
        Nonempty
          (PureWZ2HierarchyExactReentryIndexedRefinementSchedule
            capability sigma outputLoss)

/-- An exact-reentry-indexed Node 4 producer directly supplies the initial
reentrant hierarchy source.  No ordinary trace is reconstructed here. -/
theorem pureWZ2_hierarchy_initial_reentrant_source_of_exact_refinement_producer
    (capability : PureWZ2PropStickyCapability)
    (producer :
      PureWZ2HierarchyExactReentryIndexedRefinementProducer capability)
    {sigma : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    {outputLoss sourceDelta₀ : ℝ}
    (outputLoss_pos : 0 < outputLoss)
    (sourceDelta₀_pos : 0 < sourceDelta₀) :
    PureWZ2HierarchyInitialReentrantSourceConclusion
      capability sigma outputLoss sourceDelta₀ := by
  have halfOutputLoss_pos : 0 < outputLoss / 2 := by positivity
  rcases producer sigma critical (outputLoss / 2) halfOutputLoss_pos with
    ⟨schedule⟩
  let scaleCeiling := min sourceDelta₀ schedule.delta₀
  have scaleCeiling_pos : 0 < scaleCeiling :=
    lt_min sourceDelta₀_pos schedule.delta₀_pos
  rcases capability.rootReentrant sigma critical schedule.rootLoss
      scaleCeiling schedule.rootLoss_pos scaleCeiling_pos with ⟨root⟩
  rcases schedule.produce scaleCeiling scaleCeiling_pos (min_le_right _ _)
      root with ⟨refinement⟩
  exact
    ⟨outputLoss / 2, root.realization.delta, halfOutputLoss_pos, by linarith,
      root.realization.delta_pos,
      root.realization.delta_le_ceiling.trans (min_le_left _ _),
      ⟨refinement.toReentrantGrainSource⟩⟩

/-- Exact non-CWA leaf remaining after a same-family grain refinement has
been constructed.  It is the ordinary trace geometry for the refined
shading, together with its density budget.  The refinement itself already
supplies the output extremality and top-level CWA. -/
structure PureWZ2HierarchyInitialRefinementTraceFields
    {sigma inputLoss outputLoss scaleCeiling : ℝ}
    {normalizationExponent logExponent : ℕ}
    (root : PureWZ2PropStickyReentrantRootRealizationData
      (sigma := sigma) (outputLoss := inputLoss)
      (scaleCeiling := scaleCeiling) normalizationExponent logExponent)
    (refinement : PureWZ2GrainRefinementData
      root.realization.normalized.croppedRefined sigma outputLoss) where
  geometry : PureWZ2PropStickyReentryGeometry
    root.rootReentry.ordinarySource.family
    root.rootReentry.ordinarySource.shading
    root.realization.normalized.croppedFamily refinement.shading
    normalizationExponent
  ordinary_density_budget :
    Kakeya.realRpowENN root.realization.delta root.realization.sourceLoss / 2 ≤
      geometry.ordinaryDensity
  ordinary_axial_window_eighth :
    ∀ index point,
      point ∈ geometry.frame '' geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8

namespace PureWZ2HierarchyInitialRefinementTraceFields

/-- Rebuild re-entry on the exact refined shading.  No CWA leaf is needed:
the top-level CWA and cropped extremality are fields of the already-produced
grain refinement. -/
noncomputable def toReentryData
    {sigma inputLoss outputLoss scaleCeiling : ℝ}
    {normalizationExponent logExponent : ℕ}
    {root : PureWZ2PropStickyReentrantRootRealizationData
      (sigma := sigma) (outputLoss := inputLoss)
      (scaleCeiling := scaleCeiling) normalizationExponent logExponent}
    {refinement : PureWZ2GrainRefinementData
      root.realization.normalized.croppedRefined sigma outputLoss}
    (trace : PureWZ2HierarchyInitialRefinementTraceFields root refinement)
    (outputLoss_pos : 0 < outputLoss)
    (rootNormalizationLoss_le_output :
      root.realization.normalizationLoss ≤ outputLoss) :
    PureWZ2PropStickyReentryData
      (sigma := sigma) refinement.shading normalizationExponent
      root.realization.sourceLoss outputLoss where
  sourceLoss_pos := root.realization.sourceLoss_pos
  normalizationLoss_pos := outputLoss_pos
  sourceLoss_le_half := root.rootReentry.sourceLoss_le_half.trans <|
    div_le_div_of_nonneg_right rootNormalizationLoss_le_output (by norm_num)
  ordinarySource := root.rootReentry.ordinarySource
  geometry := trace.geometry
  ordinary_density_budget := trace.ordinary_density_budget
  cropped_top_level_cwa := refinement.top_level_cwa
  cropped_extremal := refinement.extremal

/-- Package the refinement and the exact refined-shading trace as one
reentrant hierarchy source. -/
noncomputable def toReentrantGrainSource
    {sigma inputLoss outputLoss scaleCeiling : ℝ}
    {normalizationExponent logExponent : ℕ}
    {root : PureWZ2PropStickyReentrantRootRealizationData
      (sigma := sigma) (outputLoss := inputLoss)
      (scaleCeiling := scaleCeiling) normalizationExponent logExponent}
    {refinement : PureWZ2GrainRefinementData
      root.realization.normalized.croppedRefined sigma outputLoss}
    (trace : PureWZ2HierarchyInitialRefinementTraceFields root refinement)
    (slope_bound : ∀ z : ℝ, z ∈ Set.Icc (-1 : ℝ) 1 →
      |refinement.globalGrains.slope z| ≤ 3)
    (outputLoss_pos : 0 < outputLoss)
    (rootNormalizationLoss_le_output :
      root.realization.normalizationLoss ≤ outputLoss) :
    PureWZ2ReentrantGrainSource sigma outputLoss root.realization.delta
      normalizationExponent where
  ordinaryLoss := root.realization.sourceLoss
  grain := refinement.toQuantitativeGrainConfiguration slope_bound
  reentry := trace.toReentryData outputLoss_pos rootNormalizationLoss_le_output
  ordinary_axial_window_eighth := trace.ordinary_axial_window_eighth

end PureWZ2HierarchyInitialRefinementTraceFields

/-- Select the same root first and apply the dependent grain theorem to that
exact root family and shading.  This avoids identifying independent
existential witnesses and exposes precisely the remaining re-entry gap. -/
theorem pureWZ2_hierarchy_initial_root_refinement_fork_of_grainsAtExtremizer
    (capability : PureWZ2PropStickyCapability)
    (_paperADBridge : PureWZ2PaperADBridgeStatement)
    (grainsAtExtremizer : PureWZ2GrainsAtExtremizerStatement)
    {sigma : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    {outputLoss sourceDelta₀ : ℝ}
    (outputLoss_pos : 0 < outputLoss)
    (sourceDelta₀_pos : 0 < sourceDelta₀) :
    ∃ inputLoss scaleCeiling : ℝ,
      0 < inputLoss ∧
        inputLoss ≤ outputLoss ∧
        0 < scaleCeiling ∧
        scaleCeiling ≤ sourceDelta₀ ∧
        Nonempty
          (Sigma fun root :
            PureWZ2PropStickyReentrantRootRealizationData
              (sigma := sigma) (outputLoss := inputLoss)
              (scaleCeiling := scaleCeiling)
              capability.normalizationExponent capability.logExponent =>
            PureWZ2HierarchyInitialRootRefinementFork
              (outputLoss := outputLoss) root) := by
  rcases grainsAtExtremizer sigma critical outputLoss outputLoss_pos with
    ⟨inputLoss, grainDelta₀, inputLoss_pos, inputLoss_le_output,
      grainDelta₀_pos, _grainDelta₀_le_one, restore⟩
  let scaleCeiling := min sourceDelta₀ grainDelta₀
  have scaleCeiling_pos : 0 < scaleCeiling := by
    exact lt_min sourceDelta₀_pos grainDelta₀_pos
  rcases capability.rootReentrant sigma critical inputLoss scaleCeiling
      inputLoss_pos scaleCeiling_pos with ⟨root⟩
  have rootDelta_le_grain : root.realization.delta ≤ grainDelta₀ :=
    root.realization.delta_le_ceiling.trans (min_le_right _ _)
  have rootExtremal : WZ2PaperCroppedIsExtremal sigma inputLoss
      root.realization.normalized.croppedFamily
      root.realization.normalized.croppedRefined :=
    root.rootReentry.cropped_extremal.mono_loss <|
      root.realization.normalizationLoss_lt_continuation.le.trans
        root.realization.continuationLoss_lt_output.le
  rcases restore root.realization.delta root.realization.delta_pos
      rootDelta_le_grain root.realization.normalized.croppedFamily
      root.realization.normalized.croppedRefined
      root.rootReentry.geometry.line_class rootExtremal with ⟨refinement⟩
  exact
    ⟨inputLoss, scaleCeiling, inputLoss_pos, inputLoss_le_output,
      scaleCeiling_pos, min_le_left _ _,
      ⟨⟨root, { refinement := refinement }⟩⟩⟩

/-- Close the initial reentrant source from the exact pair of non-CWA leaves:
a same-extremizer grain producer and ordinary-trace geometry for the produced
refinement. -/
theorem pureWZ2_hierarchy_initial_reentrant_source_of_grainsAtExtremizer_and_trace
    (capability : PureWZ2PropStickyCapability)
    (paperADBridge : PureWZ2PaperADBridgeStatement)
    (grainsAtExtremizer : PureWZ2GrainsAtExtremizerStatement)
    (refinedTrace : ∀
      {sigma inputLoss outputLoss scaleCeiling : ℝ}
      {normalizationExponent logExponent : ℕ}
      (root : PureWZ2PropStickyReentrantRootRealizationData
        (sigma := sigma) (outputLoss := inputLoss)
        (scaleCeiling := scaleCeiling) normalizationExponent logExponent)
      (refinement : PureWZ2GrainRefinementData
        root.realization.normalized.croppedRefined sigma outputLoss),
        Nonempty
          (PureWZ2HierarchyInitialRefinementTraceFields root refinement))
    (refinedSlopeBound : ∀
      {sigma inputLoss outputLoss scaleCeiling : ℝ}
      {normalizationExponent logExponent : ℕ}
      (root : PureWZ2PropStickyReentrantRootRealizationData
        (sigma := sigma) (outputLoss := inputLoss)
        (scaleCeiling := scaleCeiling) normalizationExponent logExponent)
      (refinement : PureWZ2GrainRefinementData
        root.realization.normalized.croppedRefined sigma outputLoss),
        ∀ z : ℝ, z ∈ Set.Icc (-1 : ℝ) 1 →
          |refinement.globalGrains.slope z| ≤ 3)
    {sigma : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    {outputLoss sourceDelta₀ : ℝ}
    (outputLoss_pos : 0 < outputLoss)
    (sourceDelta₀_pos : 0 < sourceDelta₀) :
    PureWZ2HierarchyInitialReentrantSourceConclusion
      capability sigma outputLoss sourceDelta₀ := by
  rcases pureWZ2_hierarchy_initial_root_refinement_fork_of_grainsAtExtremizer
      capability paperADBridge grainsAtExtremizer critical
      (show 0 < outputLoss / 2 by positivity)
      sourceDelta₀_pos with
    ⟨inputLoss, scaleCeiling, inputLoss_pos, inputLoss_le_halfOutput,
      scaleCeiling_pos, scaleCeiling_le_source, ⟨⟨root, fork⟩⟩⟩
  rcases refinedTrace root fork.refinement with ⟨trace⟩
  have rootNormalizationLoss_le_output :
      root.realization.normalizationLoss ≤ outputLoss / 2 :=
    (root.realization.normalizationLoss_lt_continuation.le.trans
      root.realization.continuationLoss_lt_output.le).trans
        inputLoss_le_halfOutput
  refine
    ⟨outputLoss / 2, root.realization.delta, by positivity, by linarith,
      root.realization.delta_pos,
      root.realization.delta_le_ceiling.trans scaleCeiling_le_source, ?_⟩
  exact
    ⟨trace.toReentrantGrainSource (refinedSlopeBound root fork.refinement)
      (show 0 < outputLoss / 2 by positivity)
      rootNormalizationLoss_le_output⟩

end Kakeya.Assouad

end
