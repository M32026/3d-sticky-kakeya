import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralGlobalOutputV2Statements
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FixedGridCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TreeCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsPacketCellInput
import MyLeanRepo.Kakeya.Assouad.ExtremalInfrastructure

/-!
# Proposition 6.2 paper sketch, revision 4

This file follows the five displayed results in `WZ2_prop62.tex`:

1. fixed-grid boundary removal;
2. one-pass stability of a finite CWA tree;
3. metric parents at the prescribed scale;
4. four-degree packet core and exact balancing;
5. Proposition 6.2.

Proof-internal claims such as the packing count, Chernoff sampling, critical
floor selection, and multiplicity multiplication are deliberately not
separate public targets.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad.Prop62PaperAudit.V4

attribute [local instance] Classical.propDecidable

abbrev CellIndex := WZ2PaperCellIndex

def logarithmicLoss (delta : ℝ) : ENNReal :=
  pureWZ2Prop62DirectionLevelCount delta

def finiteErrorConstant (constant : ENNReal) : Prop :=
  1 ≤ constant ∧ constant ≠ ⊤

def gridBoundaryBadSet (delta rho : ℝ) : Set Point3 :=
  wz2PaperGridBoundaryRegion delta rho

def outerBoundaryBadSet (rho : ℝ) : Set Point3 :=
  wz2PaperCropBoundaryRegion rho

def coarseParent (delta rho : ℝ) (cell : CellIndex) : CellIndex :=
  pureWZ2Prop62CoarseParent delta rho cell

def safeFineCells
    {delta rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (hdelta : 0 < delta) : Finset CellIndex :=
  pureWZ2Prop62SafeFineCells (rho := rho) shading hdelta

abbrev FixedGridBoundaryRemovalData
    {delta rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (hdelta : 0 < delta) :=
  PureWZ2Prop62FixedGridCleanupData
    (rho := rho) shading hdelta

/-- `WZ2_prop62.tex`, Lemma "Fixed-grid boundary removal". -/
def FixedGridBoundaryRemovalStatement : Prop :=
  ∃ gridConstant outerConstant : ENNReal,
    0 < gridConstant ∧ gridConstant ≠ ⊤ ∧
    0 < outerConstant ∧ outerConstant ≠ ⊤ ∧
    ∀ (delta rho : ℝ),
      ∀ (hdelta : 0 < delta), delta ≤ 1 / 100 →
      0 < rho → rho ≤ 1 → delta ≤ rho →
      ∀ (family : Kakeya.Streamlined.TubeFamily delta),
        WZ1PaperIsLineClass family →
        ∀ (shading : WZ1PaperTubeShading family),
          WZ1PaperIsCubicalShading shading →
          ∀ constant : ENNReal,
            finiteErrorConstant constant →
            WZ2PaperConvexWolffBound family constant →
            let gridUpper :=
              gridConstant * constant * ENNReal.ofReal (delta / rho) *
                logarithmicLoss delta *
                  (wz1PaperBodyFamily family).mass
            let outerUpper :=
              outerConstant * constant * ENNReal.ofReal rho *
                logarithmicLoss delta *
                  (wz1PaperBodyFamily family).mass
            (∑ source : Fin family.card,
                volume
                  (wz1PaperTubeCarrier (family.tube source) ∩
                    gridBoundaryBadSet delta rho)) ≤ gridUpper ∧
            (∑ source : Fin family.card,
                volume
                  (wz1PaperTubeCarrier (family.tube source) ∩
                    outerBoundaryBadSet rho)) ≤ outerUpper ∧
            (gridUpper + outerUpper ≤ shading.mass / 2 →
              Nonempty
                (FixedGridBoundaryRemovalData
                  (rho := rho) shading hdelta))

structure RescaledTreeNodeCWAData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {rho : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperLiteralDilatedPartitioningCover family coarse)
    (parent : Fin coarse.card)
    (rho_pos : 0 < rho)
    (constant : ENNReal) where
  targetFamily : Kakeya.Streamlined.TubeFamily (delta / rho)
  sourceIndex : Fin targetFamily.card → Fin family.card
  sourceIndex_mem :
    ∀ target,
      sourceIndex target ∈
        wz2PaperLiteralFullFiberIndices family coarse parent
  sourceIndex_injective : Function.Injective sourceIndex
  sourceIndex_surjective :
    ∀ source,
      source ∈ wz2PaperLiteralFullFiberIndices family coarse parent →
        ∃ target, sourceIndex target = source
  target_axis :
    ∀ target,
      tubeAxisLine (targetFamily.tube target) =
        wz2PaperLiteralUnitRescalingMap
            (coarse.tube parent) rho_pos ''
          tubeAxisLine (family.tube (sourceIndex target))
  target_line_class :
    WZ1PaperIsLineClass targetFamily
  target_essentially_distinct :
    WZ1PaperIsEssentiallyDistinct targetFamily
  convex_wolff :
    WZ2PaperConvexWolffBound targetFamily constant

structure FiniteCWATreeLevel
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (rho_pos : 0 < rho.1)
    (constant : ENNReal) where
  coarse : Kakeya.Streamlined.TubeFamily rho.1
  cover : WZ2PaperLiteralDilatedPartitioningCover family coarse
  coarse_line_class : WZ1PaperIsLineClass coarse
  coarse_essentially_distinct : WZ1PaperIsEssentiallyDistinct coarse
  full_fiber_uniform :
    ∀ first second,
      wz2PaperLiteralFullFiberCount family coarse first ≤
        constant * wz2PaperLiteralFullFiberCount family coarse second
  rescaledFiber :
    ∀ parent,
      Nonempty
        (RescaledTreeNodeCWAData
          cover parent rho_pos constant)

structure FiniteCWATree
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (constant : ENNReal)
    (depth B : ℕ) where
  source_line_class : WZ1PaperIsLineClass family
  source_essentially_distinct : WZ1PaperIsEssentiallyDistinct family
  source_convex_wolff :
    WZ2PaperConvexWolffBound family constant
  scale :
    Fin depth →
      Kakeya.Streamlined.AdmissibleScale delta
  scale_pos :
    ∀ coordinate, 0 < (scale coordinate).1
  scale_antitone :
    ∀ first second : Fin depth,
      first.1 ≤ second.1 →
        (scale second).1 ≤ (scale first).1
  level :
    ∀ coordinate,
      FiniteCWATreeLevel
        family (scale coordinate) (scale_pos coordinate) constant
  scale_net :
    ∀ target : Kakeya.Streamlined.AdmissibleScale delta,
      ∃ coordinate,
        target.1 ≤ (scale coordinate).1 ∧
          ENNReal.ofReal (scale coordinate).1 <
            constant ^ B * ENNReal.ofReal target.1
  tail_scale_net :
    ∀ first,
      ∀ target : Kakeya.Streamlined.AdmissibleScale delta,
        target.1 ≤ (scale first).1 →
          ∃ second,
            first.1 ≤ second.1 ∧
              target.1 ≤ (scale second).1 ∧
                ENNReal.ofReal (scale second).1 <
                  constant ^ B * ENNReal.ofReal target.1
  nested :
    ∀ first second : Fin depth,
      first.1 ≤ second.1 →
      ∀ source target,
        (level second).cover.parent source =
            (level second).cover.parent target →
          (level first).cover.parent source =
            (level first).cover.parent target

def FiniteCWATree.nodeFiber
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {constant : ENNReal}
    {depth B : ℕ}
    (tree : FiniteCWATree family constant depth B)
    (coordinate : Fin depth)
    (node : Fin (tree.level coordinate).coarse.card) :
    Finset (Fin family.card) :=
  wz2PaperLiteralFullFiberIndices
    family (tree.level coordinate).coarse node

structure OnePassTreeCleanupData
    {Leaf Node : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Node] [DecidableEq Node]
    {depth : ℕ}
    (tree : PureWZ2Prop62FiniteTree Leaf Node depth)
    (selected : Finset Leaf) where
  core : Finset Leaf
  core_subset : core ⊆ selected
  global_retention :
    selected.card ≤ 2 ^ depth * core.card
  node_density :
    ∀ level, level ≤ depth →
      ∀ node,
        (core ∩ tree.fiber level node).Nonempty →
          selected.card * (tree.fiber level node).card ≤
            2 ^ depth *
              (core ∩ tree.fiber level node).card *
              Fintype.card Leaf
  weighted_retention :
    ∀ (weight : Leaf → ENNReal) (weightLevel : ENNReal),
      (∀ leaf ∈ selected, weightLevel ≤ weight leaf) →
      (∀ leaf ∈ selected, weight leaf ≤ 2 * weightLevel) →
        ∑ leaf ∈ selected, weight leaf ≤
          2 ^ (depth + 1) * ∑ leaf ∈ core, weight leaf
  local_cwa_transfer :
    ∀ level, level ≤ depth →
      ∀ node,
        (core ∩ tree.fiber level node).Nonempty →
        ∀ (constant volumeFactor : ENNReal),
          ∀ count : Finset Leaf → ENNReal,
            (∀ first second, first ⊆ second →
              count first ≤ count second) →
            count (tree.fiber level node) ≤
                constant * volumeFactor *
                  (tree.fiber level node).card →
              count (core ∩ tree.fiber level node) ≤
                (constant * (2 ^ depth : ENNReal) *
                    (Fintype.card Leaf : ENNReal) *
                    (selected.card : ENNReal)⁻¹) *
                  volumeFactor *
                  ((core ∩ tree.fiber level node).card : ENNReal)

/-- `WZ2_prop62.tex`, Lemma "One-pass stability of a finite CWA tree". -/
def OnePassTreeCleanupStatement : Prop :=
  ∀ (Leaf Node : Type),
    ∀ [Fintype Leaf] [DecidableEq Leaf],
      ∀ [Fintype Node] [DecidableEq Node],
        ∀ (depth : ℕ),
          ∀ (tree : PureWZ2Prop62FiniteTree Leaf Node depth),
            ∀ (selected : Finset Leaf),
              selected.Nonempty →
                Nonempty (OnePassTreeCleanupData tree selected)

structure RescaledMetricFiberCWAData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (parent : Fin coarse.card)
    (rho_pos : 0 < rho)
    (constant : ENNReal) where
  sourceConstant : ENNReal
  rescalingInput :
    PureWZ2Prop62MetricFiberRescalingInput
      cover parent sourceConstant
  familyData :
    WZ2PaperLiteralUnitRescaledFamilyData
      rescalingInput.sourceFamily
      (coarse.tube parent) rho_pos
  familyData_eq :
    familyData = rescalingInput.literal
  rescalingCertificate :
    WZ2PaperAssouadToLiteralRescalingCertificate
      rho_pos
      (WZ2PaperAssouadUnitRescalingData.ofTube
        (coarse.tube parent) rho_pos)
      familyData 4000000
  rescalingCertificate_eq :
    HEq rescalingCertificate rescalingInput.certificate
  constant_eq :
    constant = (81000000 : ENNReal) * sourceConstant
  cwa :
    WZ2PaperPureCWAAtNearbyScales
      rescalingCertificate.publicFamily constant

structure MetricParentScaleData
    {delta : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (rho_pos : 0 < rho.1)
    (parentConstant fiberConstant : ENNReal) where
  coarse : Kakeya.Streamlined.TubeFamily rho.1
  section6Cover : PureWZ2Section6Cover fine coarse
  cover : WZ1PaperTubeCover fine coarse
  cover_eq :
    cover = section6Cover.toWZ1PaperTubeCover
  full_fiber_uniform :
    ∀ first second,
      wz2PaperFullFiberCount fine coarse first ≤
        parentConstant * wz2PaperFullFiberCount fine coarse second
  coarse_cwa :
    WZ2PaperPureCWAAtNearbyScales coarse parentConstant
  rescaledFiber :
    ∀ parent,
      Nonempty
        (RescaledMetricFiberCWAData
          section6Cover parent rho_pos fiberConstant)

structure MetricParentsAtPrescribedScaleData
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading source)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (fineParentDistanceConstant : ℝ)
    (parentConstant fiberConstant : ENNReal) where
  rho_pos : 0 < rho.1
  fine_parent_distance_constant_pos :
    0 < fineParentDistanceConstant
  refinement : WZ1PaperRefinement shading 10
  refined_nonempty : refinement.selected.family.Nonempty
  refined_cubical :
    WZ1PaperIsCubicalShading refinement.refined
  scaleData :
    MetricParentScaleData
      refinement.selected.family rho rho_pos
        parentConstant fiberConstant
  metric_fiber :
    ∀ sourceIndex parent,
      scaleData.cover.parent sourceIndex = parent ↔
        wz1PaperLineDistance
            (refinement.selected.family.tube sourceIndex)
            (scaleData.coarse.tube parent) ≤
          rho.1 / 2
  fine_parent_close :
    ∀ sourceIndex,
      wz1PaperLineDistance
          (refinement.selected.family.tube sourceIndex)
          (scaleData.coarse.tube
            (scaleData.cover.parent sourceIndex)) ≤
        fineParentDistanceConstant * rho.1

/-!
Paper-facing Target-3 output.

The preceding record is retained as an implementation ABI for the existing
ordinary-carrier metric pipeline.  This record is the literal Section-6
interface used by the five public targets.
-/
structure PaperMetricParentsAtPrescribedScaleData
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading source)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (fineParentDistanceConstant : ℝ)
    (parentConstant fiberConstant : ENNReal) where
  rho_pos : 0 < rho.1
  fine_parent_distance_constant_pos :
    0 < fineParentDistanceConstant
  refinement : WZ1PaperRefinement shading 10
  refined_nonempty : refinement.selected.family.Nonempty
  refined_cubical :
    WZ1PaperIsCubicalShading refinement.refined
  refined_line_class :
    WZ1PaperIsLineClass refinement.selected.family
  stable :
    WZ2PaperStableScaleCoverData
      refinement.selected.family rho parentConstant fiberConstant
  rescaled_fiber_cwa :
    ∀ parent,
      ∃ familyData :
          WZ2PaperStableUnitRescaledFamilyData
            stable.cover parent stable.rho_pos fiberConstant,
        WZ2PaperCWAAtNearbyScales
          familyData.targetFamily fiberConstant
  metric_fiber :
    ∀ sourceIndex parent,
      stable.cover.toWZ1PaperTubeCover.parent sourceIndex = parent ↔
        wz1PaperLineDistance
            (refinement.selected.family.tube sourceIndex)
            (stable.coarse.tube parent) ≤
          rho.1 / 2
  fine_parent_close :
    ∀ sourceIndex,
      wz1PaperLineDistance
          (refinement.selected.family.tube sourceIndex)
          (stable.coarse.tube
            (stable.cover.toWZ1PaperTubeCover.parent sourceIndex)) ≤
        fineParentDistanceConstant * rho.1

/-- `WZ2_prop62.tex`, Lemma "Metric parents at the prescribed scale". -/
def MetricParentsAtPrescribedScaleStatement : Prop :=
  ∀ A : ℕ, 1 ≤ A →
    ∃ cwaPower : ℕ,
      1 ≤ cwaPower ∧
      ∀ epsilon eta c₀ : ℝ,
        0 < epsilon →
        0 < eta →
        (cwaPower : ℝ) * eta ≤ epsilon / 100 →
        0 < c₀ →
        ∃ delta₀ : ℝ,
          0 < delta₀ ∧ delta₀ ≤ 1 / 100 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ (source : Kakeya.Streamlined.TubeFamily delta),
              source.Nonempty →
              ∀ (shading : WZ1PaperTubeShading source),
                WZ1PaperIsCubicalShading shading →
                WZ2PaperCWAAtNearbyScales source
                    (Kakeya.realRpowENN delta
                      (-(A : ℝ) * eta)) →
                shading.IsLambdaDense
                    (Kakeya.realRpowENN delta
                      ((A : ℝ) * eta)) →
                ∀ rho :
                    Kakeya.Streamlined.AdmissibleScale delta,
                  Real.rpow delta (1 - epsilon) ≤ rho.1 →
                  rho.1 ≤ Real.rpow delta epsilon →
                    Nonempty
                      (PaperMetricParentsAtPrescribedScaleData
                        shading rho c₀
                        (Kakeya.realRpowENN delta
                          (-(cwaPower : ℝ) * eta))
                        (Kakeya.realRpowENN delta
                          (-(cwaPower : ℝ) * eta)))

structure FourDegreePacketCoreData
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {eta : ℝ}
    {packetDensityExponent : ℕ}
    (hdelta : 0 < delta)
    (metric :
      MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
          parentConstant fiberConstant)
    (outputParentConstant outputFiberConstant : ENNReal) where
  refinement :
    WZ1PaperRefinement metric.refinement.refined 50
  refined_cubical :
    WZ1PaperIsCubicalShading refinement.refined
  coarse :
    Kakeya.Streamlined.TubeSubfamily metric.scaleData.coarse
  cover :
    PureWZ2Section6Cover
      refinement.selected.family coarse.family
  parent_commutes :
    ∀ sourceIndex,
      metric.scaleData.cover.parent
          (refinement.selected.embedding sourceIndex) =
        coarse.embedding
          (cover.toWZ1PaperTubeCover.parent sourceIndex)
  complete_metric_fibers :
    ∀ oldSource newParent,
      metric.scaleData.cover.parent oldSource =
          coarse.embedding newParent →
        ∃ newSource,
          refinement.selected.embedding newSource = oldSource
  refined_nonempty : refinement.selected.family.Nonempty
  coarseShading : WZ1PaperTubeShading coarse.family
  balanced :
    WZ1PaperBalancedCoverData
      cover.toWZ1PaperTubeCover
      refinement.refined coarseShading
  muFine : ℕ
  muCoarse : ℕ
  W : ℕ
  fiberFloor : ℕ
  muFine_pos : 0 < muFine
  muCoarse_pos : 0 < muCoarse
  W_pos : 0 < W
  fiberFloor_pos : 0 < fiberFloor
  regularity : ℕ
  regularity_pos : 0 < regularity
  packetCells : Finset (Fin coarse.family.card × CellIndex)
  packetCells_nonempty : packetCells.Nonempty
  packetCells_eq :
    packetCells =
      ((Finset.univ : Finset (Fin coarse.family.card)).product
        (wz1PaperActiveCells refinement.refined hdelta)).filter
          fun edge =>
            ((wz2PaperFullFiberIndices
                refinement.selected.family coarse.family edge.1).filter
              fun sourceIndex =>
                wz1PaperGridCube delta edge.2 ⊆
                  refinement.refined.carrier sourceIndex).Nonempty
  activeFineCells : Finset CellIndex
  active_fine_cells_eq :
    activeFineCells = packetCells.image Prod.snd
  activeCoarseCells : Finset CellIndex
  active_coarse_cells_eq :
    activeCoarseCells = balanced.activeCells
  active_coarse_cells_nonempty : activeCoarseCells.Nonempty
  coarseOfFine : CellIndex → CellIndex
  packet_coarse_support :
    ∀ edge ∈ packetCells,
      coarseOfFine edge.2 ∈ activeCoarseCells ∧
        wz1PaperGridCube delta edge.2 ⊆
          wz1PaperGridCube rho.1 (coarseOfFine edge.2) ∧
        wz1PaperGridCube rho.1 (coarseOfFine edge.2) ⊆
          wz1PaperTubeCarrier (coarse.family.tube edge.1)
  exact_fine_multiplicity :
    ∀ edge ∈ packetCells,
        ((wz2PaperFullFiberIndices
            refinement.selected.family coarse.family edge.1).filter
          fun sourceIndex =>
            wz1PaperGridCube delta edge.2 ⊆
              refinement.refined.carrier sourceIndex).card =
          muFine
  balanced_cell_mass :
    balanced.cellMass =
      W * volume (wz1PaperGridCube delta (0, 0, 0))
  coarse_multiplicity :
    ∀ cell ∈ activeCoarseCells,
      muCoarse ≤
          (Finset.univ.filter fun parent =>
            wz1PaperGridCube rho.1 cell ⊆
              coarseShading.carrier parent).card ∧
        (Finset.univ.filter fun parent =>
          wz1PaperGridCube rho.1 cell ⊆
            coarseShading.carrier parent).card ≤
          regularity * muCoarse
  fiber_cardinality :
    ∀ parent,
      fiberFloor ≤
          wz2PaperFullFiberCount
            refinement.selected.family coarse.family parent ∧
        wz2PaperFullFiberCount
            refinement.selected.family coarse.family parent <
          2 * fiberFloor
  parent_cwa :
    WZ2PaperPureCWAAtNearbyScales
      coarse.family outputParentConstant
  rescaled_fiber_cwa :
    ∀ parent,
      Nonempty
        (RescaledMetricFiberCWAData
          cover parent metric.rho_pos outputFiberConstant)
  packet_density :
    ∀ parent,
      Kakeya.realRpowENN delta
            ((packetDensityExponent : ℝ) * eta) *
            (fiberFloor : ENNReal) *
            Kakeya.realRpowENN delta 2 ≤
        (restrictPaperShading
          (wz2PaperFullFiberSubfamily
            refinement.selected.family coarse.family parent)
          refinement.refined).mass
  total_mass_retention :
    wz1PaperRefinementFraction delta 50 *
        metric.refinement.refined.mass ≤
      refinement.refined.mass

/--
Paper-facing Target-4 output on the exact Target-3 witness.

The carrier-faithful partitioning cover and the final literal rescaled full
fibers are stored directly.  Thus Target 5 never has to recover them from an
unrelated existential witness.
-/
structure PaperFourDegreePacketCoreData
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {eta : ℝ}
    {packetDensityExponent : ℕ}
    (hdelta : 0 < delta)
    (metric :
      PaperMetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
          parentConstant fiberConstant)
    (outputParentConstant outputFiberConstant : ENNReal) where
  refinement :
    WZ1PaperRefinement metric.refinement.refined 50
  refined_cubical :
    WZ1PaperIsCubicalShading refinement.refined
  coarse :
    Kakeya.Streamlined.TubeSubfamily metric.stable.coarse
  cover :
    WZ2PaperPartitioningCover
      refinement.selected.family coarse.family
  parent_commutes :
    ∀ sourceIndex,
      metric.stable.cover.toWZ1PaperTubeCover.parent
          (refinement.selected.embedding sourceIndex) =
        coarse.embedding
          (cover.toWZ1PaperTubeCover.parent sourceIndex)
  complete_metric_fibers :
    ∀ oldSource newParent,
      metric.stable.cover.toWZ1PaperTubeCover.parent oldSource =
          coarse.embedding newParent →
        ∃ newSource,
          refinement.selected.embedding newSource = oldSource
  refined_nonempty : refinement.selected.family.Nonempty
  coarseShading : WZ1PaperTubeShading coarse.family
  balanced :
    WZ1PaperBalancedCoverData
      cover.toWZ1PaperTubeCover
      refinement.refined coarseShading
  muFine : ℕ
  muCoarse : ℕ
  W : ℕ
  fiberFloor : ℕ
  muFine_pos : 0 < muFine
  muCoarse_pos : 0 < muCoarse
  W_pos : 0 < W
  fiberFloor_pos : 0 < fiberFloor
  regularity : ℕ
  regularity_pos : 0 < regularity
  packetCells : Finset (Fin coarse.family.card × CellIndex)
  packetCells_nonempty : packetCells.Nonempty
  packetCells_eq :
    packetCells =
      ((Finset.univ : Finset (Fin coarse.family.card)).product
        (wz1PaperActiveCells refinement.refined hdelta)).filter
          fun edge =>
            ((wz2PaperFullFiberIndices
                refinement.selected.family coarse.family edge.1).filter
              fun sourceIndex =>
                wz1PaperGridCube delta edge.2 ⊆
                  refinement.refined.carrier sourceIndex).Nonempty
  activeFineCells : Finset CellIndex
  active_fine_cells_eq :
    activeFineCells = packetCells.image Prod.snd
  activeCoarseCells : Finset CellIndex
  active_coarse_cells_eq :
    activeCoarseCells = balanced.activeCells
  active_coarse_cells_nonempty : activeCoarseCells.Nonempty
  coarseOfFine : CellIndex → CellIndex
  packet_coarse_support :
    ∀ edge ∈ packetCells,
      coarseOfFine edge.2 ∈ activeCoarseCells ∧
        wz1PaperGridCube delta edge.2 ⊆
          wz1PaperGridCube rho.1 (coarseOfFine edge.2) ∧
        wz1PaperGridCube rho.1 (coarseOfFine edge.2) ⊆
          wz1PaperTubeCarrier (coarse.family.tube edge.1)
  exact_fine_multiplicity :
    ∀ edge ∈ packetCells,
        ((wz2PaperFullFiberIndices
            refinement.selected.family coarse.family edge.1).filter
          fun sourceIndex =>
            wz1PaperGridCube delta edge.2 ⊆
              refinement.refined.carrier sourceIndex).card =
          muFine
  balanced_cell_mass :
    balanced.cellMass =
      W * volume (wz1PaperGridCube delta (0, 0, 0))
  coarse_multiplicity :
    ∀ cell ∈ activeCoarseCells,
      muCoarse ≤
          (Finset.univ.filter fun parent =>
            wz1PaperGridCube rho.1 cell ⊆
              coarseShading.carrier parent).card ∧
        (Finset.univ.filter fun parent =>
          wz1PaperGridCube rho.1 cell ⊆
            coarseShading.carrier parent).card ≤
          regularity * muCoarse
  fiber_cardinality :
    ∀ parent,
      fiberFloor ≤
          wz2PaperFullFiberCount
            refinement.selected.family coarse.family parent ∧
        wz2PaperFullFiberCount
            refinement.selected.family coarse.family parent <
          2 * fiberFloor
  parent_cwa :
    WZ2PaperCWAAtNearbyScales
      coarse.family outputParentConstant
  rescaled_fiber_cwa :
    ∀ parent,
      ∃ familyData :
          WZ2PaperStableUnitRescaledFamilyData
            cover parent metric.rho_pos outputFiberConstant,
        WZ2PaperCWAAtNearbyScales
          familyData.targetFamily outputFiberConstant
  packet_density :
    ∀ parent,
      Kakeya.realRpowENN delta
            ((packetDensityExponent : ℝ) * eta) *
            (fiberFloor : ENNReal) *
            Kakeya.realRpowENN delta 2 ≤
        (restrictPaperShading
          (cover.fullFiberSubfamily parent)
          refinement.refined).mass
  total_mass_retention :
    wz1PaperRefinementFraction delta 50 *
        metric.refinement.refined.mass ≤
      refinement.refined.mass

/--
`WZ2_prop62.tex`, Lemma "Four-degree packet core and exact balancing".
The packing and Chernoff arguments are proof steps inside this target.
-/
def FourDegreePacketCoreStatement : Prop :=
  ∃ polylogExponent : ℕ,
    ∀ inputDensityExponent inputCWAExponent : ℕ,
      ∃ packetDensityExponent cwaLossExponent : ℕ,
      inputDensityExponent ≤ packetDensityExponent ∧
      inputCWAExponent ≤ cwaLossExponent ∧
      ∀ eta : ℝ, 0 < eta →
        (packetDensityExponent : ℝ) * eta < 1 →
          ∃ delta₀ : ℝ,
              0 < delta₀ ∧ delta₀ ≤ 1 / 100 ∧
              ∀ (delta : ℝ), ∀ (hdelta : 0 < delta),
                delta ≤ delta₀ →
                ∀ (source : Kakeya.Streamlined.TubeFamily delta),
                  ∀ (sourceShading : WZ1PaperTubeShading source),
                    ∀ (rho : Kakeya.Streamlined.AdmissibleScale delta),
                      ∀ (fineParentDistanceConstant : ℝ),
                        ∀ (parentConstant fiberConstant : ENNReal),
                          ∀ (metric :
                              PaperMetricParentsAtPrescribedScaleData
                                sourceShading rho
                                  fineParentDistanceConstant
                                  parentConstant fiberConstant),
                            parentConstant ≤
                                Kakeya.realRpowENN delta
                                  (-(inputCWAExponent : ℝ) * eta) →
                            fiberConstant ≤
                                Kakeya.realRpowENN delta
                                  (-(inputCWAExponent : ℝ) * eta) →
                            metric.refinement.refined.IsLambdaDense
                                (Kakeya.realRpowENN delta
                                  ((inputDensityExponent : ℝ) * eta)) →
                            (∀ sourceIndex cell,
                              wz1PaperGridCube delta cell ⊆
                                  metric.refinement.refined.carrier
                                    sourceIndex →
                                ∃! coarseCell,
                                  wz1PaperGridCube delta cell ⊆
                                      wz1PaperGridCube rho.1 coarseCell ∧
                                    wz1PaperGridCube rho.1 coarseCell ⊆
                                      wz1PaperTubeCarrier
                                        (metric.stable.coarse.tube
                                          (metric.stable.cover
                                            |>.toWZ1PaperTubeCover.parent
                                            sourceIndex))) →
                              ∃ outputParentConstant
                                  outputFiberConstant : ENNReal,
                                outputParentConstant =
                                    Kakeya.realRpowENN delta
                                      (-(cwaLossExponent : ℝ) * eta) ∧
                                outputFiberConstant =
                                    Kakeya.realRpowENN delta
                                      (-(cwaLossExponent : ℝ) * eta) ∧
                                ∃ output :
                                    PaperFourDegreePacketCoreData
                                      (eta := eta)
                                      (packetDensityExponent :=
                                        packetDensityExponent)
                                      hdelta metric
                                      outputParentConstant
                                      outputFiberConstant,
                                  (output.regularity : ENNReal) ≤
                                    logarithmicLoss delta ^
                                      polylogExponent

/--
`WZ2_prop62.tex`, Proposition 6.2.

The source uses the cropped full-line nearby-scale extremality of Section 6.
The exact-scale source statement remains a stronger compatibility wrapper.
-/
def WZ2PaperNearbyLiteralPropStickyStatementV2 : Prop :=
  ∃ logExponent : ℕ,
  ∀ sigma : ℝ,
    0 < sigma → sigma < 1 →
    HasWZ2PaperCriticalVolumeFloor sigma →
      ∀ outputLoss : ℝ, 0 < outputLoss →
        ∃ inputLoss delta₀ : ℝ,
          0 < inputLoss ∧
          0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ source : Kakeya.Streamlined.TubeFamily delta,
              ∀ shading : WZ1PaperTubeShading source,
                WZ2PaperIsExtremal
                    sigma inputLoss source shading →
                  ∀ rho :
                      Kakeya.Streamlined.AdmissibleScale delta,
                    Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                    rho.1 ≤ Real.rpow delta outputLoss →
                      Nonempty
                        (WZ2PaperLiteralPropStickyDataV2
                          (sigma := sigma) (loss := outputLoss)
                          shading rho logExponent)

def Proposition62Statement : Prop :=
  WZ2PaperNearbyLiteralPropStickyStatementV2

end Kakeya.Assouad.Prop62PaperAudit.V4

end
