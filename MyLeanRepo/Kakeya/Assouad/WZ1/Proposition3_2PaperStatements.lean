import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2Statements
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Paper-faithful boundary for WZ1 Proposition 3.2

These definitions are internal to the WZ1 proof.  They model the paper's
cropped neighborhoods of full coaxial lines and its existential good-covering
condition.  They deliberately do not expose a recursively rooted exact-radius
`UniformTubeStructure` on an intermediate coarse family.

The public WZ2 endpoint remains `Kakeya.Streamlined.StickyKakeyaHypothesis`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Orient a formal tube direction into the paper's positive vertical chart. -/
def wz1PaperDirection
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) : Point3 :=
  if 0 ≤ tube.direction (2 : Fin 3) then
    tube.direction
  else
    -tube.direction

/--
The paper's metric on coaxial lines in the fixed vertical chart.

The first term compares the intersections with `z = 0`; the second compares
the positively oriented unit directions.
-/
def wz1PaperLineDistance
    {delta rho : ℝ}
    (fine : Kakeya.DeltaTube delta)
    (coarse : Kakeya.DeltaTube rho) : ℝ :=
  dist (wz1TubeAxisZeroPoint fine)
      (wz1TubeAxisZeroPoint coarse) +
    InnerProductGeometry.angle
      (wz1PaperDirection fine)
      (wz1PaperDirection coarse)

/-- The literal axis-aligned paper cube of side length `scale`. -/
def wz1PaperGridCube
    (scale : ℝ) (cell : ℤ × ℤ × ℤ) : Set Point3 :=
  {point | gridIndex scale point = cell}

/-- Paper grid index at the literal cube side length. -/
def wz1PaperGridIndex
    (scale : ℝ) (point : Point3) : ℤ × ℤ × ℤ :=
  gridIndex scale point

@[simp] theorem mem_wz1PaperGridCube
    (scale : ℝ) (cell : ℤ × ℤ × ℤ) (point : Point3) :
    point ∈ wz1PaperGridCube scale cell ↔
      wz1PaperGridIndex scale point = cell := by
  rfl

/-- Union of all literal paper cells meeting `source`. -/
def wz1PaperCubicalSaturation
    (scale : ℝ) (source : Set Point3) : Set Point3 :=
  {point |
    ∃ sourcePoint ∈ source,
      wz1PaperGridIndex scale point =
        wz1PaperGridIndex scale sourcePoint}

/--
The actual three-dimensional paper tube: the `6 * delta` neighborhood of the
full coaxial line, cropped to `[-1,1]^3`.
-/
def wz1PaperTubeCarrier
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) : Set Point3 :=
  Metric.cthickening (6 * delta) (tubeAxisLine tube) ∩
    Kakeya.Streamlined.axisBox 2 2 2

/-- The indexed body family carried by paper tubes. -/
def wz1PaperBodyFamily
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta) :
    Kakeya.Streamlined.BodyFamily where
  card := family.card
  body index := ⟨wz1PaperTubeCarrier (family.tube index)⟩

/-- A shading in the literal cropped full-line tube convention of WZ1. -/
abbrev WZ1PaperTubeShading
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta) :=
  Kakeya.Streamlined.Shading (wz1PaperBodyFamily family)

/-- A paper shading is made from whole normalized standard cells. -/
def WZ1PaperIsCubicalShading
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) : Prop :=
  ∀ index point, point ∈ shading.carrier index →
    wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) ⊆
      shading.carrier index

/-- Membership in the fixed paper line class `L₃`. -/
def WZ1PaperTubeInLineClass
    {delta : ℝ}
    (tube : Kakeya.DeltaTube delta) : Prop :=
  (1 / 2 : ℝ) ≤ wz1PaperDirection tube (2 : Fin 3) ∧
    |wz1TubeAxisZeroPoint tube (0 : Fin 3)| ≤ 1 / 3 ∧
    |wz1TubeAxisZeroPoint tube (1 : Fin 3)| ≤ 1 / 3

/-- Membership in `L₃` implies the orientation-free vertical-chart bound. -/
theorem WZ1PaperTubeInLineClass.vertical
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (h : WZ1PaperTubeInLineClass tube) :
    (1 / 2 : ℝ) ≤ |tube.direction (2 : Fin 3)| := by
  unfold WZ1PaperTubeInLineClass at h
  unfold wz1PaperDirection at h
  split_ifs at h with hdirection
  · simpa [abs_of_nonneg hdirection] using h.1
  · have hnegative :
        tube.direction (2 : Fin 3) < 0 := lt_of_not_ge hdirection
    simpa [abs_of_neg hnegative] using h.1

/-- Membership in the fixed paper line class `L₃`. -/
def WZ1PaperIsLineClass
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta) : Prop :=
  ∀ index, WZ1PaperTubeInLineClass (family.tube index)

namespace WZ1PaperIsLineClass

theorem vertical
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (h : WZ1PaperIsLineClass family) :
    IsInVerticalChart family :=
  fun index => (h index).vertical

end WZ1PaperIsLineClass

/-- The positively oriented paper direction is still a unit vector. -/
theorem wz1PaperDirection_norm
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    ‖wz1PaperDirection tube‖ = 1 := by
  unfold wz1PaperDirection
  split_ifs
  · exact tube.direction_unit
  · simpa using tube.direction_unit

/--
The paper's unit-rescaling map relative to a positively oriented coarse line.

The paper permits a fixed dimensional constant `c(3) ∼ 1`; the canonical Lean
choice is `c(3) = 1 / 100`, hence transverse division by `100 * rho`.
-/
def wz1PaperUnitRescalingMap
    {rho : ℝ} (coarse : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) (point : Point3) : Point3 :=
  unitRescalingMap
    (wz1TubeAxisZeroPoint coarse)
    (wz1PaperDirection coarse)
    (wz1PaperDirection_norm coarse)
    (100 * rho) (by positivity)
    point

/-- Pairwise distinctness in the paper's coaxial-line metric. -/
def WZ1PaperIsEssentiallyDistinct
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta) : Prop :=
  ∀ first second, first ≠ second →
    delta <
      wz1PaperLineDistance
        (family.tube first) (family.tube second)

/--
The paper's geometric relation “the `rho`-tube `coarse` covers the
`delta`-tube `fine`”; see the paragraph immediately before Definition 2.1.
-/
def WZ1PaperTubeCovers
    {delta rho : ℝ}
    (fine : Kakeya.DeltaTube delta)
    (coarse : Kakeya.DeltaTube rho) : Prop :=
  wz1PaperLineDistance fine coarse ≤ rho / 2

/-- A coarse collection covers a fine collection in the paper's sense. -/
def WZ1PaperCollectionCovers
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho) : Prop :=
  ∀ source : Fin fine.card,
    ∃ parent : Fin coarse.card,
      WZ1PaperTubeCovers
        (fine.tube source) (coarse.tube parent)

/--
The unique geometric cover constructed in Proposition 3.2, Step 1.

The paper first obtains an ordinary covering collection and then refines it
so every retained fine tube is covered by exactly one retained coarse tube.
The `parent` map therefore records the geometric relation rather than an
arbitrary assignment.
-/
structure WZ1PaperTubeCover
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho) where
  parent : Fin fine.card → Fin coarse.card
  parent_surjective : Function.Surjective parent
  parent_covers :
    ∀ index,
      WZ1PaperTubeCovers
          (fine.tube index)
          (coarse.tube (parent index))
  parent_unique :
    ∀ source candidate,
      WZ1PaperTubeCovers
          (fine.tube source) (coarse.tube candidate) →
        candidate = parent source

namespace WZ1PaperTubeCover

/-- Fine indices assigned to one paper parent. -/
def fiberIndices
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ1PaperTubeCover fine coarse)
    (parent : Fin coarse.card) :
    Finset (Fin fine.card) := by
  classical
  exact Finset.univ.filter fun index =>
    cover.parent index = parent

/-- Shaded mass in one paper parent fiber. -/
def fiberShadedMass
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ1PaperTubeCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card) : ENNReal :=
  ∑ index ∈ cover.fiberIndices parent,
    volume (shading.carrier index)

/-- Fine point multiplicity inside one paper parent fiber. -/
def fiberPointMultiplicity
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ1PaperTubeCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card)
    (point : Point3) : ℕ := by
  classical
  exact
    (cover.fiberIndices parent).filter
      (fun index => point ∈ shading.carrier index) |>.card

end WZ1PaperTubeCover

/-- Paper-essential parallelism of two radius-`rho` tubes. -/
def WZ1PaperEssentiallyParallel
    {rho : ℝ}
    (first second : Kakeya.DeltaTube rho) : Prop :=
  ‖wz1PaperDirection first - wz1PaperDirection second‖ ≤ rho

/--
Definition 2.1(b): at every intermediate radius the family can be covered by
`rho`-tubes, at most `delta^(-loss)` of which are essentially parallel to any
common `rho`-tube.

The paper does not call this a “good covering,” and it does not require the
covering family itself to be essentially distinct.
-/
def WZ1PaperMultiscaleCoveringCondition
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (loss : ℝ) : Prop :=
  ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
    ∃ coarse : Kakeya.Streamlined.TubeFamily rho.1,
      WZ1PaperIsLineClass coarse ∧
        WZ1PaperCollectionCovers family coarse ∧
        ∀ reference : Kakeya.DeltaTube rho.1,
          WZ1PaperTubeInLineClass reference →
          ((Finset.univ.filter fun index =>
              WZ1PaperEssentiallyParallel
                (coarse.tube index) reference).card : ENNReal) ≤
            Kakeya.realRpowENN delta (-loss)

/--
The ambient tube/shading conditions together with Definition 2.1(a)--(b).

The cubical field belongs to the paper's definition of a shading. Item (c),
the aggregate shaded-mass lower bound, is added separately below because
Lemma 3.3 replaces it by the scaled lower bound `delta^eta * rho^2`.
-/
structure WZ1PaperDefinition2_1ABConditions
    {delta : ℝ}
    (coverLoss : ℝ)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (shading : WZ1PaperTubeShading family) : Prop where
  delta_pos : 0 < delta
  delta_le_one : delta ≤ 1
  line_class : WZ1PaperIsLineClass family
  essentially_distinct : WZ1PaperIsEssentiallyDistinct family
  multiscale_covering :
    WZ1PaperMultiscaleCoveringCondition family coverLoss
  cubical : WZ1PaperIsCubicalShading shading

/-- Definition 2.1(a)--(c), specialized to dimension three. -/
structure WZ1PaperDefinition2_1Conditions
    {delta : ℝ}
    (massLoss coverLoss : ℝ)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (shading : WZ1PaperTubeShading family) : Prop
    extends
      WZ1PaperDefinition2_1ABConditions
        coverLoss family shading where
  shaded_mass :
    Kakeya.realRpowENN delta massLoss ≤ shading.mass

/--
Definition 3.1 (`epsilon`-extremal), with the critical exponent made explicit.

The lower union-volume estimate is intentionally not a field: it is a
consequence of the critical-volume floor, not part of the definition of an
extremal pair.
-/
structure WZ1PaperIsEpsilonExtremal
    {delta : ℝ}
    (sigma loss : ℝ)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (shading : WZ1PaperTubeShading family) : Prop
    extends
      WZ1PaperDefinition2_1Conditions
        loss loss family shading where
  volume_upper :
    volume shading.union ≤
      Kakeya.realRpowENN delta (sigma - loss)

private theorem wz1PaperRealRpowENN_antitone
    {delta first second : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hloss : first ≤ second) :
    Kakeya.realRpowENN delta second ≤
      Kakeya.realRpowENN delta first := by
  apply ENNReal.ofReal_mono
  exact
    Real.rpow_le_rpow_of_exponent_ge
      hdelta hdeltaOne hloss

namespace WZ1PaperDefinition2_1Conditions

/-- Increasing the loss weakens every structural clause. -/
theorem mono_loss
    {delta firstMassLoss secondMassLoss
      firstCoverLoss secondCoverLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (data :
      WZ1PaperDefinition2_1Conditions
        firstMassLoss firstCoverLoss family shading)
    (hmass : firstMassLoss ≤ secondMassLoss)
    (hcover : firstCoverLoss ≤ secondCoverLoss) :
    WZ1PaperDefinition2_1Conditions
      secondMassLoss secondCoverLoss family shading := by
  refine
    { toWZ1PaperDefinition2_1ABConditions :=
        { delta_pos := data.delta_pos
          delta_le_one := data.delta_le_one
          line_class := data.line_class
          essentially_distinct := data.essentially_distinct
          cubical := data.cubical
          multiscale_covering := ?_ }
      shaded_mass := ?_
      }
  · intro rho
    rcases data.multiscale_covering rho with
      ⟨coarse, hlineClass, hcover, hparallel⟩
    refine ⟨coarse, hlineClass, hcover, ?_⟩
    intro reference hreference
    exact
      (hparallel reference hreference).trans
        (wz1PaperRealRpowENN_antitone
          data.delta_pos data.delta_le_one
          (by linarith [hcover]))
  · exact
      (wz1PaperRealRpowENN_antitone
          data.delta_pos data.delta_le_one hmass).trans
        data.shaded_mass

end WZ1PaperDefinition2_1Conditions

namespace WZ1PaperIsEpsilonExtremal

/-- Increasing the loss weakens paper extremality. -/
theorem mono_loss
    {delta sigma firstLoss secondLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (data :
      WZ1PaperIsEpsilonExtremal
        sigma firstLoss family shading)
    (hloss : firstLoss ≤ secondLoss) :
    WZ1PaperIsEpsilonExtremal
      sigma secondLoss family shading := by
  refine
    { toWZ1PaperDefinition2_1Conditions :=
        data.toWZ1PaperDefinition2_1Conditions.mono_loss
          hloss hloss
      volume_upper := data.volume_upper.trans ?_ }
  exact
    wz1PaperRealRpowENN_antitone
      data.delta_pos data.delta_le_one (by linarith)

end WZ1PaperIsEpsilonExtremal

/--
The lower-volume consequence of the paper's definitions of `M(s,t,delta)`,
`N(s,t)`, and `sigma_n`.

This is not a separately named hypothesis in the paper. It isolates the
inference used at equations (3.2) and (3.3): once `s,t` are chosen with
`N(s,t) ≤ sigma_n + outputLoss / 2`, every sufficiently small configuration
satisfying Definition 2.1(a)--(c) at those parameters has shaded-union volume
at least `delta^(sigma_n + outputLoss)`. A fully unconditional formalization
must derive this predicate from formal definitions of `M`, `N`, and
`sigma_n`.
-/
def HasWZ1PaperCriticalVolumeFloor (sigma : ℝ) : Prop :=
  ∀ outputLoss : ℝ, 0 < outputLoss →
    ∃ massLoss coverLoss delta₀ : ℝ,
      0 < massLoss ∧
      0 < coverLoss ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ family : Kakeya.Streamlined.TubeFamily delta,
          ∀ shading : WZ1PaperTubeShading family,
            WZ1PaperDefinition2_1Conditions
                massLoss coverLoss family shading →
              Kakeya.realRpowENN delta
                  (sigma + outputLoss) ≤
                volume shading.union

/-- The explicit `(\log(1/delta))^{-C}` factor in the paper's refinement relation. -/
def wz1PaperRefinementFraction
    (delta : ℝ) (logExponent : ℕ) : ENNReal :=
  (ENNReal.ofReal (Real.log (1 / delta)))⁻¹ ^ logExponent

/--
A refinement in the sense defined immediately before Definition 2.1.

The exponent is selected before the small scale `delta`; this prevents the
polylogarithmic retention constant from depending on the particular scale.
-/
structure WZ1PaperRefinement
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading source)
    (logExponent : ℕ) where
  selected : Kakeya.Streamlined.TubeSubfamily source
  refined : WZ1PaperTubeShading selected.family
  subshading :
    ∀ index,
      refined.carrier index ⊆
        shading.carrier (selected.embedding index)
  retained_mass :
    wz1PaperRefinementFraction delta logExponent *
        shading.mass ≤
      refined.mass

/-- Balanced cover, exactly as defined in the paragraph before Definition 2.1. -/
structure WZ1PaperBalancedCoverData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ1PaperTubeCover fine coarse)
    (refined : WZ1PaperTubeShading fine)
    (coarseShading : WZ1PaperTubeShading coarse) where
  point_compatibility :
    ∀ source point, point ∈ refined.carrier source →
      point ∈ coarseShading.carrier (cover.parent source)
  coarse_cubical :
    WZ1PaperIsCubicalShading coarseShading
  activeCells : Finset (ℤ × ℤ × ℤ)
  coarse_union_eq :
    coarseShading.union =
      ⋃ cell ∈ activeCells,
        wz1PaperGridCube rho cell
  cellMass : ENNReal
  cellMass_pos : 0 < cellMass
  cellMass_ne_top : cellMass ≠ ⊤
  fine_cell_mass :
    ∀ cell ∈ activeCells,
      volume
          (refined.union ∩
            wz1PaperGridCube rho cell) =
        cellMass

/-- The two pointwise conclusions of WZ1 Proposition 3.2. -/
structure WZ1PaperMultiplicityData
    {delta rho sigma loss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ1PaperTubeCover fine coarse)
    (refined : WZ1PaperTubeShading fine)
    (coarseShading : WZ1PaperTubeShading coarse) where
  coarse_multiplicity_upper :
    ∀ point,
      (coarseShading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN rho (-sigma - loss)
  fiber_multiplicity_upper :
    ∀ parent point,
      (cover.fiberPointMultiplicity
          refined parent point : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
          (-sigma - loss)

/-- Definition 2.1(a)--(c) and the pointwise cap produced by Lemma 3.3. -/
structure WZ1PaperLemma3_3TargetData
    (targetDelta sigma loss : ℝ) where
  family : Kakeya.Streamlined.TubeFamily targetDelta
  shading : WZ1PaperTubeShading family
  structural :
    WZ1PaperDefinition2_1Conditions
      loss loss family shading
  point_multiplicity_upper :
    ∀ point,
      (shading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN targetDelta (-sigma - loss)

/--
The exact unit-rescaling provenance common to Lemma 3.3 and Proposition 3.2.
-/
structure WZ1PaperUnitRescaledImageData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (refined : WZ1PaperTubeShading fine)
    (sourceActive : Fin fine.card → Prop)
    (coarse : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (targetFamily :
      Kakeya.Streamlined.TubeFamily (delta / rho))
    (targetShading : WZ1PaperTubeShading targetFamily) where
  sourceIndex : Fin targetFamily.card → Fin fine.card
  sourceIndex_active :
    ∀ targetIndex, sourceActive (sourceIndex targetIndex)
  sourceIndex_injective :
    Function.Injective sourceIndex
  sourceIndex_surjective :
    ∀ source, sourceActive source →
      ∃ targetIndex, sourceIndex targetIndex = source
  target_axis :
    ∀ targetIndex,
      tubeAxisLine (targetFamily.tube targetIndex) =
        wz1PaperUnitRescalingMap coarse hrho ''
          tubeAxisLine
            (fine.tube (sourceIndex targetIndex))
  target_carrier_eq :
    ∀ targetIndex,
      targetShading.carrier targetIndex =
        wz1PaperCubicalSaturation (delta / rho)
          (wz1PaperUnitRescalingMap coarse hrho ''
            refined.carrier (sourceIndex targetIndex))

/-- The refinement and structural target asserted by WZ Lemma 3.3. -/
structure WZ1PaperLemma3_3Data
    {delta rho sigma loss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (coarse : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (logExponent : ℕ) where
  refinement : WZ1PaperRefinement shading logExponent
  target : WZ1PaperLemma3_3TargetData
    (delta / rho) sigma loss
  image :
    WZ1PaperUnitRescaledImageData
      refinement.refined (fun _ => True)
      coarse hrho
      target.family target.shading

/-- Item (ii) of Proposition 3.2 for one final coarse tube. -/
structure WZ1PaperUnitRescaledParentFiberData
    {delta rho sigma loss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ1PaperTubeCover fine coarse)
    (refined : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card)
    (hrho : 0 < rho) where
  targetFamily : Kakeya.Streamlined.TubeFamily (delta / rho)
  targetShading : WZ1PaperTubeShading targetFamily
  image :
    WZ1PaperUnitRescaledImageData
      refined (fun source => cover.parent source = parent)
      (coarse.tube parent) hrho
      targetFamily targetShading
  extremal :
    WZ1PaperIsEpsilonExtremal
      sigma loss targetFamily targetShading

/-- The one-scale paper output of WZ1 Proposition 3.2. -/
structure WZ1PaperProposition3_2Data
    {delta sigma loss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading source)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (logExponent : ℕ) where
  refinement :
    WZ1PaperRefinement shading logExponent
  coarse :
    Kakeya.Streamlined.TubeFamily rho.1
  cover :
    WZ1PaperTubeCover refinement.selected.family coarse
  coarseShading :
    WZ1PaperTubeShading coarse
  coarse_extremal :
    WZ1PaperIsEpsilonExtremal
      sigma loss coarse coarseShading
  balanced :
    WZ1PaperBalancedCoverData
      cover refinement.refined coarseShading
  rescaledFiber :
    ∀ parent : Fin coarse.card,
      Nonempty
        (WZ1PaperUnitRescaledParentFiberData
          (sigma := sigma) (loss := loss)
          cover refinement.refined parent
          coarse_extremal.delta_pos)
  multiplicity :
    WZ1PaperMultiplicityData
      (sigma := sigma) (loss := loss)
      cover refinement.refined coarseShading

/--
The conditional form of WZ Proposition 3.2 after extracting the lower-volume
consequence used at equations (3.2) and (3.3).

All tube, shading, cover, refinement, balanced-cover, unit-rescaling, and
four numbered conclusions use the paper's conventions. The sole explicit
input `HasWZ1PaperCriticalVolumeFloor` is the still-separate formalization of
the consequence of `M`, `N`, and `sigma_n`; it is not an extra paper
hypothesis. No internal type in this statement is exported to GWZ.
-/
def WZ1PaperProposition3_2FromCriticalFloorStatement : Prop :=
  ∃ logExponent : ℕ,
  ∀ sigma : ℝ,
    HasWZ1PaperCriticalVolumeFloor sigma →
      ∀ loss : ℝ, 0 < loss →
        ∃ inputLoss delta₀ : ℝ,
          0 < inputLoss ∧
          0 < delta₀ ∧ delta₀ < 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ source : Kakeya.Streamlined.TubeFamily delta,
              ∀ shading : WZ1PaperTubeShading source,
                WZ1PaperIsEpsilonExtremal
                    sigma inputLoss source shading →
                  ∀ rho :
                      Kakeya.Streamlined.AdmissibleScale delta,
                    Real.rpow delta (1 - loss) ≤ rho.1 →
                    rho.1 ≤ Real.rpow delta loss →
                      Nonempty
                        (WZ1PaperProposition3_2Data
                          (sigma := sigma) (loss := loss)
                          shading rho logExponent)

end Kakeya.Assouad
