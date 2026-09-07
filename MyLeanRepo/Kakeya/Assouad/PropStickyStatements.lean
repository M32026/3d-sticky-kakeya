import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.RootRelativeBalancedCoverStatements

/-!
# WZ2 Section 6 `prop: sticky`

This module freezes the single-scale proposition used in Section 6 of
Wang--Zahl's Assouad-dimension paper.  The internal tube and shading model is
the cropped full-line convention fixed at the start of that section.

The public project endpoint remains
`Kakeya.Streamlined.StickyKakeyaHypothesis`.  The declarations below are
WZ2-owned internal data and do not change the GWZ-facing interface.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/--
WZ2 Definition 2's fixed-constant unit rescaling.

After rotating the anchor axis to the vertical direction, all three
coordinates are multiplied by the fixed paper constant `1 / 100`, while the
two transverse coordinates are additionally dilated by `rho⁻¹`.
-/
def wz2PaperLiteralUnitRescalingMap
    {rho : ℝ}
    (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (point : Point3) : Point3 :=
  (1 / 100 : ℝ) •
    unitRescalingMap
      (wz1TubeAxisZeroPoint anchor)
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor)
      rho hrho point

/-- The full geometric fiber over one coarse tube. -/
def wz2PaperFullFiberIndices
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) : Finset (Fin fine.card) :=
  Finset.univ.filter fun source =>
    WZ1PaperTubeCovers (fine.tube source) (coarse.tube parent)

/-- The genuine subfamily of all fine tubes in one full geometric fiber. -/
def wz2PaperFullFiberSubfamily
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) :
    Kakeya.Streamlined.TubeSubfamily fine :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset fine
    (wz2PaperFullFiberIndices fine coarse parent)

/-- Cardinality of one full geometric fiber. -/
def wz2PaperFullFiberCount
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) : ENNReal :=
  (wz2PaperFullFiberIndices fine coarse parent).card

/-- Pointwise shaded multiplicity inside one full geometric fiber. -/
def wz2PaperFullFiberPointMultiplicity
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (shading : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card)
    (point : Point3) : ℕ :=
  ((wz2PaperFullFiberIndices fine coarse parent).filter fun source =>
    point ∈ shading.carrier source).card

/--
The fiber defined using the doubled coarse tube.

The paper cover relation uses line distance at most `rho / 2`; replacing the
coarse tube by its two-fold dilate changes this threshold to `rho`.
-/
def wz2PaperDoubledFiberIndices
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) : Finset (Fin fine.card) :=
  Finset.univ.filter fun source =>
    wz1PaperLineDistance (fine.tube source) (coarse.tube parent) ≤ rho

/--
Literal containment used by the paper's definition of a cover.

The line-distance field retained in `WZ1PaperTubeCover` is still needed for
the quantitative line geometry.  This additional field restores the set
containment used by the proof of `multiScaleWolffLem` to form its nested tree.
-/
def WZ2PaperTubeCarrierCovers
    {delta rho : ℝ}
    (fine : Kakeya.DeltaTube delta)
    (coarse : Kakeya.DeltaTube rho) : Prop :=
  wz1PaperTubeCarrier fine ⊆ wz1PaperTubeCarrier coarse

/-- The paper's strict full geometric fiber `B[A]`, defined by literal
carrier containment rather than an auxiliary parent assignment. -/
def wz2PaperLiteralFullFiberIndices
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) : Finset (Fin fine.card) :=
  Finset.univ.filter fun source =>
    WZ2PaperTubeCarrierCovers
      (fine.tube source) (coarse.tube parent)

/-- Literal strict full-fiber cardinality. -/
def wz2PaperLiteralFullFiberCount
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) : ENNReal :=
  (wz2PaperLiteralFullFiberIndices fine coarse parent).card

/-- Literal doubled paper carrier.  The axis is unchanged and only the paper
neighborhood radius is doubled. -/
def wz2PaperDoubledTubeCarrier
    {rho : ℝ} (tube : Kakeya.DeltaTube rho) : Set Point3 :=
  Metric.cthickening (12 * rho) (tubeAxisLine tube) ∩
    Kakeya.Streamlined.axisBox 2 2 2

/-- The paper's doubled fiber `B[2A]`. -/
def wz2PaperLiteralDoubledFiberIndices
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) : Finset (Fin fine.card) :=
  Finset.univ.filter fun source =>
    wz1PaperTubeCarrier (fine.tube source) ⊆
      wz2PaperDoubledTubeCarrier (coarse.tube parent)

/--
A partitioning cover in the literal Section 2 sense.

The inherited parent map records the unique undilated geometric parent.
The additional field is the paper's doubled-fiber disjointness condition.
-/
structure WZ2PaperPartitioningCover
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    extends WZ1PaperTubeCover fine coarse where
  parent_carrier_covers :
    ∀ index,
      WZ2PaperTubeCarrierCovers
        (fine.tube index) (coarse.tube (parent index))
  literal_parent_unique :
    ∀ source candidate,
      WZ2PaperTubeCarrierCovers
          (fine.tube source) (coarse.tube candidate) →
        candidate = parent source
  literal_doubled_fibers_disjoint :
    ∀ first second, first ≠ second →
      Disjoint
        (wz2PaperLiteralDoubledFiberIndices fine coarse first)
        (wz2PaperLiteralDoubledFiberIndices fine coarse second)
  doubled_fibers_disjoint :
    ∀ first second, first ≠ second →
      Disjoint
        (wz2PaperDoubledFiberIndices fine coarse first)
        (wz2PaperDoubledFiberIndices fine coarse second)

/--
The normalized Convex Wolff inequality for one cropped paper tube family.
-/
def WZ2PaperConvexWolffBound
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (C : ENNReal) : Prop :=
  ∀ convexSet : Set Point3, Convex ℝ convexSet →
    (wz1PaperBodyFamily family).containedCount convexSet ≤
      C * volume convexSet * family.enncard

/--
The unit-rescaled full geometric fiber relative to its coarse tube.

Only the structural tube family is stored here.  A shading is added later
when proving item (ii) of `prop: sticky`.
-/
structure WZ2PaperUnitRescaledFamilyData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (parent : Fin coarse.card)
    (hrho : 0 < rho)
    (C : ENNReal) where
  targetFamily :
    Kakeya.Streamlined.TubeFamily (delta / rho)
  sourceIndex : Fin targetFamily.card → Fin fine.card
  sourceIndex_mem :
    ∀ target,
      sourceIndex target ∈
        wz2PaperFullFiberIndices fine coarse parent
  sourceIndex_injective : Function.Injective sourceIndex
  sourceIndex_surjective :
    ∀ source,
      source ∈ wz2PaperFullFiberIndices fine coarse parent →
        ∃ target, sourceIndex target = source
  target_axis :
    ∀ target,
      tubeAxisLine (targetFamily.tube target) =
        wz1PaperUnitRescalingMap
            (coarse.tube parent) hrho ''
          tubeAxisLine (fine.tube (sourceIndex target))
  target_line_class :
    WZ1PaperIsLineClass targetFamily
  convex_wolff :
    WZ2PaperConvexWolffBound targetFamily C

/-- One exact-scale cover appearing in the every-scale CWA. -/
structure WZ2PaperScaleCoverData
    {delta : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (C : ENNReal) where
  rho_pos : 0 < rho.1
  coarse : Kakeya.Streamlined.TubeFamily rho.1
  cover : WZ2PaperPartitioningCover fine coarse
  coarse_line_class :
    WZ1PaperIsLineClass coarse
  coarse_essentially_distinct :
    WZ1PaperIsEssentiallyDistinct coarse
  full_fiber_uniform :
    ∀ first second,
      wz2PaperFullFiberCount fine coarse first ≤
        C * wz2PaperFullFiberCount fine coarse second
  rescaledFiber :
    ∀ parent,
      Nonempty
        (WZ2PaperUnitRescaledFamilyData
          cover parent rho_pos C)

/--
Convex Wolff axioms at every exact scale, in the full-fiber paper semantics.

The project uses the GWZ exact-scale convention accepted by the WZ2
interface: one partitioning cover is supplied for every `rho ∈ [delta,1]`.
-/
def WZ2PaperCWAAtEveryScale
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (C : ENNReal) : Prop :=
  1 ≤ C ∧
    WZ1PaperIsLineClass family ∧
      WZ1PaperIsEssentiallyDistinct family ∧
        ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
          Nonempty (WZ2PaperScaleCoverData family rho C)

/--
The fixed-dilation paper cover relation used recursively.

The final caller-scale cover in `prop: sticky` still uses the strict WZ
threshold `rho / 2`.  Recursive covers use the validated independent-cover
geometry: an assigned parent may be farther away by one universal factor.
-/
def WZ2PaperDilatedTubeCovers
    (factor : ℝ)
    {delta rho : ℝ}
    (fine : Kakeya.DeltaTube delta)
    (coarse : Kakeya.DeltaTube rho) : Prop :=
  wz1PaperLineDistance fine coarse ≤ factor * rho / 2

/--
An assigned fixed-dilation cover.

Unlike the final `WZ2PaperPartitioningCover`, this recursive object does not
assert false undilated uniqueness or cross-scale partitioning.  Its fibers
are the fibers of the explicit surjective parent map.
-/
structure WZ2PaperDilatedTubeCover
    (factor : ℝ)
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho) where
  parent : Fin fine.card → Fin coarse.card
  parent_surjective : Function.Surjective parent
  parent_covers :
    ∀ index,
      WZ2PaperDilatedTubeCovers factor
        (fine.tube index) (coarse.tube (parent index))

namespace WZ2PaperDilatedTubeCover

/-- Assigned fine indices over one dilated-cover parent. -/
def fiberIndices
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperDilatedTubeCover factor fine coarse)
    (parent : Fin coarse.card) :
    Finset (Fin fine.card) :=
  Finset.univ.filter fun source =>
    cover.parent source = parent

/-- Assigned fiber cardinality for one dilated-cover parent. -/
def fiberCount
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperDilatedTubeCover factor fine coarse)
    (parent : Fin coarse.card) : ENNReal :=
  (cover.fiberIndices parent).card

end WZ2PaperDilatedTubeCover

/--
A carrier-faithful recursive partitioning cover.

The factor-two parent map is retained only as an auxiliary computable
assignment.  The paper-facing invariants use literal carrier containment:
the assigned parent contains the fine paper carrier, it is the unique such
parent, and the literal doubled fibers of distinct parents are disjoint.
-/
structure WZ2PaperLiteralDilatedPartitioningCover
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    extends WZ2PaperDilatedTubeCover 2 fine coarse where
  parent_carrier_covers :
    ∀ source,
      WZ2PaperTubeCarrierCovers
        (fine.tube source) (coarse.tube (parent source))
  literal_parent_unique :
    ∀ source candidate,
      WZ2PaperTubeCarrierCovers
          (fine.tube source) (coarse.tube candidate) →
        candidate = parent source
  literal_doubled_fibers_disjoint :
    ∀ first second, first ≠ second →
      Disjoint
        (wz2PaperLiteralDoubledFiberIndices fine coarse first)
        (wz2PaperLiteralDoubledFiberIndices fine coarse second)

namespace WZ2PaperLiteralDilatedPartitioningCover

/-- Assigned indices of a carrier-faithful recursive cover. -/
def fiberIndices
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperLiteralDilatedPartitioningCover fine coarse)
    (parent : Fin coarse.card) : Finset (Fin fine.card) :=
  cover.toWZ2PaperDilatedTubeCover.fiberIndices parent

/-- Assigned-fiber cardinality. -/
def fiberCount
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperLiteralDilatedPartitioningCover fine coarse)
    (parent : Fin coarse.card) : ENNReal :=
  (cover.fiberIndices parent).card

end WZ2PaperLiteralDilatedPartitioningCover

/-- Unit-rescaled assigned fiber for one recursive dilated cover. -/
structure WZ2PaperDilatedUnitRescaledFamilyData
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperDilatedTubeCover factor fine coarse)
    (parent : Fin coarse.card)
    (hrho : 0 < rho)
    (C : ENNReal) where
  targetFamily :
    Kakeya.Streamlined.TubeFamily (delta / rho)
  sourceIndex : Fin targetFamily.card → Fin fine.card
  sourceIndex_mem :
    ∀ target,
      sourceIndex target ∈ cover.fiberIndices parent
  sourceIndex_injective : Function.Injective sourceIndex
  sourceIndex_surjective :
    ∀ source,
      source ∈ cover.fiberIndices parent →
        ∃ target, sourceIndex target = source
  target_axis :
    ∀ target,
      tubeAxisLine (targetFamily.tube target) =
        wz1PaperUnitRescalingMap
            (coarse.tube parent) hrho ''
          tubeAxisLine (fine.tube (sourceIndex target))
  target_line_class :
    WZ1PaperIsLineClass targetFamily
  convex_wolff :
    WZ2PaperConvexWolffBound targetFamily C

/-- Unit-rescaling of a complete literal strict full fiber. -/
structure WZ2PaperLiteralFullFiberRescaledFamilyData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperLiteralDilatedPartitioningCover fine coarse)
    (parent : Fin coarse.card)
    (hrho : 0 < rho)
    (C : ENNReal) where
  targetFamily :
    Kakeya.Streamlined.TubeFamily (delta / rho)
  sourceIndex : Fin targetFamily.card → Fin fine.card
  sourceIndex_mem :
    ∀ target,
      sourceIndex target ∈
        wz2PaperLiteralFullFiberIndices fine coarse parent
  sourceIndex_injective : Function.Injective sourceIndex
  sourceIndex_surjective :
    ∀ source,
      source ∈ wz2PaperLiteralFullFiberIndices fine coarse parent →
        ∃ target, sourceIndex target = source
  target_axis :
    ∀ target,
      tubeAxisLine (targetFamily.tube target) =
        wz1PaperUnitRescalingMap
            (coarse.tube parent) hrho ''
          tubeAxisLine (fine.tube (sourceIndex target))
  target_line_class :
    WZ1PaperIsLineClass targetFamily
  convex_wolff :
    WZ2PaperConvexWolffBound targetFamily C

/--
One recursive nearby-scale witness with the universal factor-two line-cover
allowance.

The factor two is exactly what absorbs
`rho / 2 + sigma / 2 ≤ sigma` when two independently selected root parents
share a source child and `rho ≤ sigma`.
-/
structure WZ2PaperDilatedScaleCoverData
    {delta : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (rho : ℝ)
    (C : ENNReal) where
  rho_pos : 0 < rho
  coarse : Kakeya.Streamlined.TubeFamily rho
  cover : WZ2PaperDilatedTubeCover 2 fine coarse
  coarse_line_class :
    WZ1PaperIsLineClass coarse
  coarse_essentially_distinct :
    WZ1PaperIsEssentiallyDistinct coarse
  assigned_fiber_uniform :
    ∀ first second,
      cover.fiberCount first ≤
        C * cover.fiberCount second
  rescaledFiber :
    ∀ parent,
      Nonempty
        (WZ2PaperDilatedUnitRescaledFamilyData
          cover parent rho_pos C)

/-- One nearby-scale witness with the literal WZ2 partitioning/full-fiber
semantics. -/
structure WZ2PaperLiteralScaleCoverData
    {delta : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (rho : ℝ)
    (C : ENNReal) where
  rho_pos : 0 < rho
  coarse : Kakeya.Streamlined.TubeFamily rho
  cover :
    WZ2PaperLiteralDilatedPartitioningCover fine coarse
  coarse_line_class :
    WZ1PaperIsLineClass coarse
  coarse_essentially_distinct :
    WZ1PaperIsEssentiallyDistinct coarse
  full_fiber_uniform :
    ∀ first second,
      wz2PaperLiteralFullFiberCount fine coarse first ≤
        C * wz2PaperLiteralFullFiberCount fine coarse second
  rescaledFiber :
    ∀ parent,
      Nonempty
        (WZ2PaperLiteralFullFiberRescaledFamilyData
          cover parent rho_pos C)

/--
One nearby-scale witness from Assouad Definition 2.12.

The requested scale is `rho₀`; the actual cover scale may increase by the
allowed factor `C`.  The bound is written in `ENNReal` so the same normalized
constant used in the Convex-Wolff inequalities controls the scale window.
-/
structure WZ2PaperNearbyScaleCoverData
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (rho₀ : Kakeya.Streamlined.AdmissibleScale delta)
    (C : ENNReal) where
  rho : ℝ
  rho_pos : 0 < rho
  requested_le : rho₀.1 ≤ rho
  within_factor :
    ENNReal.ofReal rho <
      C * ENNReal.ofReal rho₀.1
  scaleData : WZ2PaperLiteralScaleCoverData family rho C

/--
Assouad Definition 2.12 in the cropped full-line model.

Paper text:

> “for every `rho_0 ∈ [delta,1]`, there exists
> `rho ∈ [rho_0, C rho_0)` ...”

The stronger GWZ exact-scale convention remains available separately as
`WZ2PaperCWAAtEveryScale`.
-/
def WZ2PaperCWAAtNearbyScales
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (C : ENNReal) : Prop :=
  1 ≤ C ∧
    WZ1PaperIsLineClass family ∧
      WZ1PaperIsEssentiallyDistinct family ∧
        ∀ rho₀ : Kakeya.Streamlined.AdmissibleScale delta,
          Nonempty
            (WZ2PaperNearbyScaleCoverData family rho₀ C)

/--
The stronger exact-scale cover data without top-level essential distinctness.

This helper is retained for the GWZ exact-scale source convention.  The
active paper output before the one-parent refinement is
`WZ2PaperCWACoversAtNearbyScales`.
-/
def WZ2PaperCWACoversAtEveryScale
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (C : ENNReal) : Prop :=
  1 ≤ C ∧
    WZ1PaperIsLineClass family ∧
      ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
        Nonempty (WZ2PaperScaleCoverData family rho C)

/--
The hereditary nearby-scale cover data without top-level essential
distinctness.

This is the conclusion used for a complete unit-rescaled parent fiber before
the Lemma 3.3 refinement restores essential distinctness.
-/
def WZ2PaperCWACoversAtNearbyScales
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (C : ENNReal) : Prop :=
  1 ≤ C ∧
    WZ1PaperIsLineClass family ∧
      ∀ rho₀ : Kakeya.Streamlined.AdmissibleScale delta,
        Nonempty
          (WZ2PaperNearbyScaleCoverData family rho₀ C)

/--
The selected complete rescaled full fiber carries hereditary nearby-scale
cover data.  Top-level essential distinctness is intentionally deferred to
the one-parent refinement.

The target axes use WZ2's literal Definition 2 rescaling map.  The historical
WZ rescaling remains available separately as `WZ2PaperUnitRescaledFamilyData`
and is used only as an intermediate source of normalized CWA before the
closed historical-to-literal transport.
-/
structure WZ2PaperStableUnitRescaledFamilyData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (parent : Fin coarse.card)
    (hrho : 0 < rho)
    (C : ENNReal) where
  targetFamily :
    Kakeya.Streamlined.TubeFamily (delta / rho)
  sourceIndex : Fin targetFamily.card → Fin fine.card
  sourceIndex_mem :
    ∀ target,
      sourceIndex target ∈
        wz2PaperFullFiberIndices fine coarse parent
  sourceIndex_injective : Function.Injective sourceIndex
  sourceIndex_surjective :
    ∀ source,
      source ∈ wz2PaperFullFiberIndices fine coarse parent →
        ∃ target, sourceIndex target = source
  target_axis :
    ∀ target,
      tubeAxisLine (targetFamily.tube target) =
        wz2PaperLiteralUnitRescalingMap
            (coarse.tube parent) hrho ''
          tubeAxisLine (fine.tube (sourceIndex target))
  target_line_class :
    WZ1PaperIsLineClass targetFamily
  convex_wolff :
    WZ2PaperConvexWolffBound targetFamily C
  cwa_covers_nearby_scales :
    WZ2PaperCWACoversAtNearbyScales targetFamily C

/--
The stable output of the multiscale closure lemma at one requested scale.

The coarse and rescaled-fiber constants live at different radii.  Keeping
them separate records the paper's two conclusions without incorrectly
transporting a normalized CWA bound from a full family to an unrescaled
subfamily.
-/
structure WZ2PaperStableScaleCoverData
    {delta : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (coarseConstant fiberConstant : ENNReal) where
  rho_pos : 0 < rho.1
  coarse : Kakeya.Streamlined.TubeFamily rho.1
  cover : WZ2PaperPartitioningCover fine coarse
  full_fiber_uniform :
    ∀ first second,
      wz2PaperFullFiberCount fine coarse first ≤
        coarseConstant *
          wz2PaperFullFiberCount fine coarse second
  coarse_cwa_nearby :
    WZ2PaperCWAAtNearbyScales coarse coarseConstant
  rescaledFiber :
    ∀ parent,
      Nonempty
        (WZ2PaperStableUnitRescaledFamilyData
          cover parent rho_pos fiberConstant)

/--
The exact-scale source extremality supplied by the GWZ-facing convention.

This is stronger than Assouad Definition 2.12 and is used only at the source
boundary.  Section 6 outputs use `WZ2PaperIsExtremal`, whose structural field
is the literal nearby-scale paper condition.
-/
structure WZ2PaperExactScaleExtremal
    {delta : ℝ}
    (sigma loss : ℝ)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (shading : WZ1PaperTubeShading family) : Prop where
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1
  nonempty : family.Nonempty
  cwa_exact_scales :
    WZ2PaperCWAAtEveryScale family
      (Kakeya.realRpowENN delta (-loss))
  multiscale_covering :
    WZ1PaperMultiscaleCoveringCondition family loss
  cubical : WZ1PaperIsCubicalShading shading
  dense :
    shading.IsLambdaDense
      (Kakeya.realRpowENN delta loss)
  volume_upper :
    volume shading.union ≤
      Kakeya.realRpowENN delta (sigma - loss)

namespace WZ2PaperExactScaleExtremal

/--
The source extremality package contains the literal structural hypotheses
from Definition 2.1(a)--(b).
-/
def toWZ1PaperDefinition2_1ABConditions
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (data :
      WZ2PaperExactScaleExtremal
        sigma loss family shading) :
    WZ1PaperDefinition2_1ABConditions loss family shading where
  delta_pos := data.delta_pos
  delta_le_one := data.delta_le_one
  line_class := data.cwa_exact_scales.2.1
  essentially_distinct := data.cwa_exact_scales.2.2.1
  multiscale_covering := data.multiscale_covering
  cubical := data.cubical

end WZ2PaperExactScaleExtremal

/-- Section 6 output extremality in the nearby-scale paper model. -/
structure WZ2PaperIsExtremal
    {delta : ℝ}
    (sigma loss : ℝ)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (shading : WZ1PaperTubeShading family) : Prop where
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1
  nonempty : family.Nonempty
  cwa_nearby_scales :
    WZ2PaperCWAAtNearbyScales family
      (Kakeya.realRpowENN delta (-loss))
  cubical : WZ1PaperIsCubicalShading shading
  dense :
    shading.IsLambdaDense
      (Kakeya.realRpowENN delta loss)
  volume_upper :
    volume shading.union ≤
      Kakeya.realRpowENN delta (sigma - loss)

/--
The lower-volume consequence of the critical definition of `sigma`, stated
in the same paper model as `prop: sticky`.

The Assouad paper defines `sigma` as the supremum of exponents admitting
counterexamples for every structural error `eta`.  Thus `floorLoss` controls
only the exponent in the union-volume lower bound, while
`structuralBudget` lets a later argument request the returned extremality
parameter `eta` to be sufficiently small.  This `eta` simultaneously
controls the nearby-scale CWA error and the aggregate shading density, just
as in the paper's definition of an extremal pair.
-/
def HasWZ2PaperCriticalVolumeFloor (sigma : ℝ) : Prop :=
  ∀ floorLoss structuralBudget : ℝ,
    0 < floorLoss →
    0 < structuralBudget →
    ∃ structuralLoss delta₀ : ℝ,
      0 < structuralLoss ∧
      structuralLoss ≤ structuralBudget ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ family : Kakeya.Streamlined.TubeFamily delta,
          family.Nonempty →
          ∀ shading : WZ1PaperTubeShading family,
            WZ2PaperCWAAtNearbyScales family
                (Kakeya.realRpowENN delta (-structuralLoss)) →
            WZ1PaperIsCubicalShading shading →
            shading.IsLambdaDense
                (Kakeya.realRpowENN delta structuralLoss) →
              Kakeya.realRpowENN delta (sigma + floorLoss) ≤
                volume shading.union

/--
The unit rescaling of the final shaded full fiber in item (ii).
-/
structure WZ2PaperUnitRescaledPairData
    {delta rho sigma strongLoss outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (refined : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card)
    (hrho : 0 < rho) where
  targetFamily :
    Kakeya.Streamlined.TubeFamily (delta / rho)
  targetShading : WZ1PaperTubeShading targetFamily
  sourceIndex : Fin targetFamily.card → Fin fine.card
  sourceIndex_mem :
    ∀ target,
      sourceIndex target ∈
        wz2PaperFullFiberIndices fine coarse parent
  sourceIndex_injective : Function.Injective sourceIndex
  sourceIndex_surjective :
    ∀ source,
      source ∈ wz2PaperFullFiberIndices fine coarse parent →
        ∃ target, sourceIndex target = source
  target_axis :
    ∀ target,
      tubeAxisLine (targetFamily.tube target) =
        wz1PaperUnitRescalingMap
            (coarse.tube parent) hrho ''
          tubeAxisLine (fine.tube (sourceIndex target))
  target_carrier_eq :
    ∀ target,
      targetShading.carrier target =
        wz1PaperCubicalSaturation (delta / rho)
          (wz1PaperUnitRescalingMap
              (coarse.tube parent) hrho ''
            refined.carrier (sourceIndex target))
  strongLoss_pos : 0 < strongLoss
  strongLoss_budget : 3 * strongLoss ≤ outputLoss
  extremal_strong :
    WZ2PaperIsExtremal
      sigma strongLoss targetFamily targetShading
  extremal :
    WZ2PaperIsExtremal
      sigma outputLoss targetFamily targetShading
  target_cardinality_lower :
    Kakeya.realRpowENN (delta / rho)
        (-2 + 2 * strongLoss) ≤
      targetFamily.enncard
  source_cardinality_eq :
    targetFamily.enncard =
      wz2PaperFullFiberCount fine coarse parent
  source_multiplicity_upper_strong :
    ∀ point,
      (wz2PaperFullFiberPointMultiplicity
          coarse refined parent point : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - strongLoss) *
          wz2PaperFullFiberCount fine coarse parent
  source_cardinality_lower :
    Kakeya.realRpowENN (delta / rho)
        (-2 + 2 * strongLoss) ≤
      wz2PaperFullFiberCount fine coarse parent

/--
The actual output of the one-parent WZ2 Lemma 3.3 analogue.

It first selects a refinement inside the supplied full fiber.  The final
Proposition assembly later synchronizes these refinements and reconstructs
item (ii) on the common final shading.
-/
structure WZ2PaperLemma3_3Data
    {delta rho sigma strongLoss outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (coarse : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (logExponent : ℕ) where
  refinement : WZ1PaperRefinement shading logExponent
  refined_cubical :
    WZ1PaperIsCubicalShading refinement.refined
  targetFamily :
    Kakeya.Streamlined.TubeFamily (delta / rho)
  targetShading : WZ1PaperTubeShading targetFamily
  image :
    WZ1PaperUnitRescaledImageData
      refinement.refined (fun _ => True)
      coarse hrho targetFamily targetShading
  strongLoss_pos : 0 < strongLoss
  strongLoss_budget : 3 * strongLoss ≤ outputLoss
  extremal_strong :
    WZ2PaperIsExtremal
      sigma strongLoss targetFamily targetShading
  extremal :
    WZ2PaperIsExtremal
      sigma outputLoss targetFamily targetShading
  target_cardinality_lower :
    Kakeya.realRpowENN (delta / rho)
        (-2 + 2 * strongLoss) ≤
      targetFamily.enncard
  source_cardinality_eq :
    targetFamily.enncard =
      refinement.selected.family.enncard
  source_multiplicity_upper_strong :
    ∀ point,
      (refinement.refined.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - strongLoss) *
          refinement.selected.family.enncard
  source_cardinality_lower :
    Kakeya.realRpowENN (delta / rho)
        (-2 + 2 * strongLoss) ≤
      refinement.selected.family.enncard

/-- The complete four-item output of WZ2 Section 6 `prop: sticky`. -/
structure WZ2LiteralPropStickyData
    {delta sigma loss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading source)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (logExponent : ℕ) where
  strongLoss : ℝ
  strongLoss_pos : 0 < strongLoss
  strongLoss_budget : 3 * strongLoss ≤ loss
  refinement : WZ1PaperRefinement shading logExponent
  refined_cubical :
    WZ1PaperIsCubicalShading refinement.refined
  refined_nonempty :
    ∀ index, (refinement.refined.carrier index).Nonempty
  coarse : Kakeya.Streamlined.TubeFamily rho.1
  cover :
    WZ2PaperPartitioningCover refinement.selected.family coarse
  coarseShading : WZ1PaperTubeShading coarse
  balanced :
    WZ1PaperBalancedCoverData
      cover.toWZ1PaperTubeCover
      refinement.refined coarseShading
  coarse_extremal_strong :
    WZ2PaperIsExtremal
      sigma strongLoss coarse coarseShading
  coarse_extremal :
    WZ2PaperIsExtremal
      sigma loss coarse coarseShading
  coarse_multiplicity_upper_strong :
    ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN rho.1
            (2 - sigma - strongLoss) *
          coarse.enncard
  coarse_cardinality_lower :
    Kakeya.realRpowENN rho.1
        (-2 + 2 * strongLoss) ≤
      coarse.enncard
  rescaledFiber :
    ∀ parent : Fin coarse.card,
      Nonempty
        (WZ2PaperUnitRescaledPairData
          (sigma := sigma)
          (strongLoss := strongLoss)
          (outputLoss := loss)
          cover refinement.refined parent
          coarse_extremal.delta_pos)
  coarse_multiplicity_upper :
    ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN rho.1 (2 - sigma - loss) *
          coarse.enncard
  fiber_multiplicity_upper :
    ∀ parent point,
      (wz2PaperFullFiberPointMultiplicity
          coarse refinement.refined parent point : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho.1)
            (2 - sigma - loss) *
          wz2PaperFullFiberCount
            refinement.selected.family coarse parent

/--
WZ2 Section 6 `prop: sticky`.

The sole critical-floor premise is the lower-volume consequence of the
critical exponent already fixed in the contradiction argument.  It is not an
additional hypothesis of the paper theorem.
-/
def WZ2LiteralPropStickyStatement : Prop :=
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
                WZ2PaperExactScaleExtremal
                    sigma inputLoss source shading →
                  ∀ rho :
                      Kakeya.Streamlined.AdmissibleScale delta,
                    Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                    rho.1 ≤ Real.rpow delta outputLoss →
                      Nonempty
                        (WZ2LiteralPropStickyData
                          (sigma := sigma) (loss := outputLoss)
                          shading rho logExponent)

/-- Full carrier-containment fiber in the actual WZ2 tube model. -/
def wz2FullFiberIndices
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) : Finset (Fin fine.card) :=
  Finset.univ.filter fun source =>
    (fine.tube source).carrier ⊆ (coarse.tube parent).carrier

/-- Cardinality of one actual full geometric fiber. -/
def wz2FullFiberCount
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) : ENNReal :=
  (wz2FullFiberIndices fine coarse parent).card

/-- Pointwise multiplicity in one actual full geometric fiber. -/
def wz2FullFiberPointMultiplicity
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (shading : Kakeya.Streamlined.TubeShading fine)
    (parent : Fin coarse.card)
    (point : Point3) : ℕ :=
  ((wz2FullFiberIndices fine coarse parent).filter fun source =>
    point ∈ shading.carrier source).card

/-- Fine tubes contained in the two-fold homothetic dilate of a coarse tube. -/
def wz2DoubledFullFiberIndices
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) : Finset (Fin fine.card) :=
  Finset.univ.filter fun source =>
    (fine.tube source).carrier ⊆
      wz1DilatedTubeCarrier 2 (coarse.tube parent)

/--
Paper-semantic certificate on one selected `TubeCover`.

The existing parent assignment is geometric and unique, hence its fibers are
exactly the full carrier-containment fibers.  Distinct doubled fibers are
disjoint, as required by the WZ2 partitioning-cover definition.
-/
structure WZ2GeometricPartitioningCertificate
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : Kakeya.Streamlined.TubeCover fine coarse) : Prop where
  parent_unique :
    ∀ source candidate,
      (fine.tube source).carrier ⊆
          (coarse.tube candidate).carrier →
        candidate = cover.parent source
  doubled_fibers_disjoint :
    ∀ first second, first ≠ second →
      Disjoint
        (wz2DoubledFullFiberIndices fine coarse first)
        (wz2DoubledFullFiberIndices fine coarse second)

/--
The WZ2 internal extremality predicate used after coarsening.

It retains the repository's every-scale `UniformTubeStructure`, density, and
volume normalization, but does not demand that a coarse formal unit-segment
carrier remain inside the original unit ball.  This is exactly the cropped
intermediate convention; the original fine input still uses `IsExtremalPair`.
-/
def WZ2ScaleExtremalPair
    {delta : ℝ}
    (sigma loss : ℝ)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (uniform : Kakeya.Streamlined.UniformTubeStructure family)
    (shading : Kakeya.Streamlined.TubeShading family) : Prop :=
  0 < delta ∧ delta ≤ 1 ∧
    family.Nonempty ∧ family.IsEssentiallyDistinct ∧
    uniform.uniformity ≤ Kakeya.realRpowENN delta (-loss) ∧
    uniform.IsFrostmanAtEveryScale
      (Kakeya.realRpowENN delta (-loss)) ∧
    shading.IsLambdaDense (Kakeya.realRpowENN delta loss) ∧
    volume shading.union ≤
      Kakeya.realRpowENN delta (sigma - loss) ∧
    Kakeya.realRpowENN delta (sigma + loss) ≤
      volume shading.union

/-- Literal side-length grid cubes used by the WZ2 balanced cover. -/
def wz2PropStickyGridCube
    (scale : ℝ) (cell : ℤ × ℤ × ℤ) : Set Point3 :=
  {point | gridIndex scale point = cell}

/-- A WZ2 shading is cubical at its literal tube radius. -/
def WZ2IsCubicalShading
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : Kakeya.Streamlined.TubeShading family) : Prop :=
  ∀ index point, point ∈ shading.carrier index →
    wz2PropStickyGridCube delta (gridIndex delta point) ⊆
      shading.carrier index

/-- Exact balanced-cover data from the paragraph preceding `prop: sticky`. -/
structure WZ2PropStickyBalancedCoverData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : Kakeya.Streamlined.TubeCover fine coarse)
    (refined : Kakeya.Streamlined.TubeShading fine)
    (coarseShading : Kakeya.Streamlined.TubeShading coarse) where
  point_compatibility :
    ∀ source point, point ∈ refined.carrier source →
      point ∈ coarseShading.carrier (cover.parent source)
  coarse_cubical : WZ2IsCubicalShading coarseShading
  activeCells : Finset (ℤ × ℤ × ℤ)
  coarse_union_eq :
    coarseShading.union =
      ⋃ cell ∈ activeCells, wz2PropStickyGridCube rho cell
  cellMass : ENNReal
  cellMass_pos : 0 < cellMass
  cellMass_ne_top : cellMass ≠ ⊤
  fine_cell_mass :
    ∀ cell ∈ activeCells,
      volume
          (refined.union ∩ wz2PropStickyGridCube rho cell) =
        cellMass

/--
Item (ii): the whole final full fiber, unit-rescaled relative to its coarse
tube, is extremal in the WZ2 setting.
-/
structure WZ2UnitRescaledFullFiberData
    {delta rho sigma strongLoss outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : Kakeya.Streamlined.TubeCover fine coarse)
    (geometric : WZ2GeometricPartitioningCertificate cover)
    (refined : Kakeya.Streamlined.TubeShading fine)
    (parent : Fin coarse.card)
    (hrho : 0 < rho) where
  targetFamily :
    Kakeya.Streamlined.TubeFamily (delta / rho)
  targetUniform :
    Kakeya.Streamlined.UniformTubeStructure targetFamily
  targetShading :
    Kakeya.Streamlined.TubeShading targetFamily
  strongLoss_pos : 0 < strongLoss
  strongLoss_budget : 3 * strongLoss < outputLoss
  target_extremal_strong :
    WZ2ScaleExtremalPair
      sigma strongLoss targetFamily targetUniform targetShading
  target_extremal :
    WZ2ScaleExtremalPair
      sigma outputLoss targetFamily targetUniform targetShading
  target_cardinality_lower :
    Kakeya.realRpowENN (delta / rho)
        (-2 + 2 * strongLoss) ≤
      targetFamily.enncard
  target_multiplicity_upper :
    ∀ point,
      (targetShading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
          (-sigma - strongLoss)
  sourceIndex : Fin targetFamily.card → Fin fine.card
  sourceIndex_mem :
    ∀ target,
      sourceIndex target ∈
        wz2FullFiberIndices fine coarse parent
  sourceIndex_surjective :
    ∀ source,
      source ∈ wz2FullFiberIndices fine coarse parent →
        ∃ target, sourceIndex target = source
  sourceFiberCap : ℕ
  sourceFiberCap_pos : 0 < sourceFiberCap
  sourceFiberCap_le_two : sourceFiberCap ≤ 2
  source_fiber_bound :
    ∀ source,
      ((Finset.univ.filter fun target =>
        sourceIndex target = source).card) ≤ sourceFiberCap
  source_fiber_absorption :
    (sourceFiberCap : ENNReal) ≤
      Kakeya.realRpowENN (delta / rho)
        (-(outputLoss - 3 * strongLoss))
  source_cardinality_lower :
    Kakeya.realRpowENN (delta / rho)
        (-2 + outputLoss - strongLoss) ≤
      wz2FullFiberCount fine coarse parent
  target_cardinality_upper :
    targetFamily.enncard ≤
      (sourceFiberCap : ENNReal) *
        wz2FullFiberCount fine coarse parent
  sourcePiece : Fin targetFamily.card → Set Point3
  sourcePiece_measurable :
    ∀ target, MeasurableSet (sourcePiece target)
  sourcePiece_subset :
    ∀ target,
      sourcePiece target ⊆
        refined.carrier (sourceIndex target)
  sourcePiece_cover :
    ∀ source,
      source ∈ wz2FullFiberIndices fine coarse parent →
        refined.carrier source ⊆
          ⋃ target : Fin targetFamily.card,
            if sourceIndex target = source then
              sourcePiece target
            else ∅
  target_axis :
    ∀ target,
      tubeAxisLine (targetFamily.tube target) =
        wz1PaperUnitRescalingMap
            (coarse.tube parent) hrho ''
          tubeAxisLine (fine.tube (sourceIndex target))
  target_carrier_eq :
    ∀ target,
      targetShading.carrier target =
        wz1PaperCubicalSaturation (delta / rho)
          (wz1PaperUnitRescalingMap
              (coarse.tube parent) hrho ''
            sourcePiece target)
  pullback_multiplicity_le :
    ∀ point,
      (wz2FullFiberPointMultiplicity
          coarse refined parent point : ENNReal) ≤
        (targetShading.pointMultiplicity
          (wz1PaperUnitRescalingMap
            (coarse.tube parent) hrho point) : ENNReal)
  source_multiplicity_upper :
    ∀ point,
      (wz2FullFiberPointMultiplicity
          coarse refined parent point : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
          (-sigma - strongLoss)

/-- The four conclusions of WZ2 Section 6 `prop: sticky`. -/
structure WZ2FormalCarrierPropStickyData
    {delta sigma loss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceUniform :
      Kakeya.Streamlined.UniformTubeStructure source)
    (shading : Kakeya.Streamlined.TubeShading source)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (logExponent : ℕ) where
  strongLoss : ℝ
  strongLoss_pos : 0 < strongLoss
  strongLoss_budget : 3 * strongLoss < loss
  selected : Kakeya.Streamlined.TubeSubfamily source
  refined :
    Kakeya.Streamlined.TubeShading selected.family
  subshading :
    ∀ index,
      refined.carrier index ⊆
        shading.carrier (selected.embedding index)
  retained_mass :
    wz1PaperRefinementFraction delta logExponent *
        shading.mass ≤
      refined.mass
  refined_nonempty :
    ∀ index, (refined.carrier index).Nonempty
  fineUniform :
    Kakeya.Streamlined.UniformTubeStructure selected.family
  refined_extremal :
    IsExtremalPair sigma loss
      selected.family fineUniform refined
  coarse :
    Kakeya.Streamlined.TubeFamily rho.1
  cover :
    Kakeya.Streamlined.TubeCover selected.family coarse
  geometric :
    WZ2GeometricPartitioningCertificate cover
  coarseUniform :
    Kakeya.Streamlined.UniformTubeStructure coarse
  coarseShading :
    Kakeya.Streamlined.TubeShading coarse
  balanced :
    WZ2PropStickyBalancedCoverData
      cover refined coarseShading
  coarse_extremal_strong :
    WZ2ScaleExtremalPair
      sigma strongLoss coarse coarseUniform coarseShading
  coarse_extremal :
    WZ2ScaleExtremalPair
      sigma loss coarse coarseUniform coarseShading
  coarse_multiplicity_absolute :
    ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN rho.1
          (-sigma - strongLoss)
  coarse_cardinality_lower :
    Kakeya.realRpowENN rho.1
        (-2 + 2 * strongLoss) ≤
      coarse.enncard
  rescaledFiber :
    ∀ parent : Fin coarse.card,
      Nonempty
        (WZ2UnitRescaledFullFiberData
          (sigma := sigma)
          (strongLoss := strongLoss)
          (outputLoss := loss)
          cover geometric refined parent
          coarse_extremal.1)
  coarse_multiplicity_upper :
    ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN rho.1 (2 - sigma - loss) *
          coarse.enncard
  fiber_multiplicity_upper :
    ∀ parent point,
      (wz2FullFiberPointMultiplicity
          coarse refined parent point : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho.1)
            (2 - sigma - loss) *
          wz2FullFiberCount selected.family coarse parent

/--
Forensic full-unit-segment version of `prop: sticky`.

This type is not the active paper theorem: its coarse and rescaled outputs
carry exact formal `UniformTubeStructure`s, the boundary already rejected by
the endpoint-effect audit.
-/
def WZ2FormalCarrierPropStickyStatement : Prop :=
  ∃ logExponent : ℕ,
  ∀ sigma : ℝ, 0 < sigma → sigma < 1 →
    HasCriticalVolumeFloor sigma →
      ∀ outputLoss : ℝ, 0 < outputLoss →
        ∃ inputLoss delta₀ : ℝ,
          0 < inputLoss ∧ inputLoss ≤ outputLoss ∧
          0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ source : Kakeya.Streamlined.TubeFamily delta,
              ∀ sourceUniform :
                  Kakeya.Streamlined.UniformTubeStructure source,
                ∀ shading :
                    Kakeya.Streamlined.TubeShading source,
                  IsExtremalPair
                      sigma inputLoss
                      source sourceUniform shading →
                  ∀ rho :
                      Kakeya.Streamlined.AdmissibleScale delta,
                    Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                    rho.1 ≤ Real.rpow delta outputLoss →
                      Nonempty
                        (WZ2FormalCarrierPropStickyData
                          (sigma := sigma) (loss := outputLoss)
                          sourceUniform shading rho logExponent)

/--
The active WZ2 Section 6 `prop: sticky` statement.

This is definitionally the cropped full-line theorem frozen above.  The
full-unit-segment variant is retained only under the explicit
`WZ2FormalCarrier...` name.
-/
abbrev WZ2PropStickyStatement : Prop :=
  WZ2LiteralPropStickyStatement

end Kakeya.Assouad
