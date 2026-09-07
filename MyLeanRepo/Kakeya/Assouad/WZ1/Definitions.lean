import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Streamlined.Statements
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct

/-!
# Definitions for the WZ1 proof migration

Only reusable geometric objects shared by the WZ1 leaf targets live here.
-/

noncomputable section

namespace Kakeya.Assouad

open Matrix

/--
Intermediate WZ1 extremality for the paper's cropped tube collections.

The repository represents a tube by the full thickening of a unit segment,
whereas the paper clips every tube to a fixed ambient box.  Passing to a
coarser radius can therefore make the full formal carrier protrude outside
the unit ball even though the induced coarse shading stays in the paper's
window.  WZ1 Lemmas 12--20 consume only that shaded window.

The final Proposition 21 normalization must still construct an ordinary
`IsExtremalPair`; this predicate is only for the intermediate WZ1 chain.
-/
def WZ1ExtremalPair {delta : ℝ} (sigma epsilon : ℝ)
    (F : Kakeya.Streamlined.TubeFamily delta)
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F) : Prop :=
  0 < delta ∧ delta ≤ 1 ∧
    F.Nonempty ∧
    Y.union ⊆ Metric.closedBall (0 : Point3) 1 ∧
    F.IsEssentiallyDistinct ∧
    U.uniformity ≤ Kakeya.realRpowENN delta (-epsilon) ∧
    U.IsFrostmanAtEveryScale
      (Kakeya.realRpowENN delta (-epsilon)) ∧
    Y.IsLambdaDense (Kakeya.realRpowENN delta epsilon) ∧
    MeasureTheory.volume Y.union ≤
      Kakeya.realRpowENN delta (sigma - epsilon) ∧
    Kakeya.realRpowENN delta (sigma + epsilon) ≤
      MeasureTheory.volume Y.union

/--
Critical-volume floor in the cropped tube convention used by WZ1.

The paper's tubes are clipped to a fixed ambient box.  In the repository a
`DeltaTube` is the full thickening of a unit segment, so coarse formal
carriers can protrude outside the unit ball even when the entire shaded
configuration remains in the paper's window.
-/
def HasWZ1CriticalVolumeFloor (sigma : ℝ) : Prop :=
  ∀ loss : ℝ, 0 < loss →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          F.Nonempty →
          F.IsEssentiallyDistinct →
          ∀ U : Kakeya.Streamlined.UniformTubeStructure F,
            U.uniformity ≤ Kakeya.realRpowENN delta (-eta) →
            U.IsFrostmanAtEveryScale
              (Kakeya.realRpowENN delta (-eta)) →
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              Y.union ⊆ Metric.closedBall (0 : Point3) 1 →
              Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
                Kakeya.realRpowENN delta (sigma + loss) ≤
                  MeasureTheory.volume Y.union

/-- Full extremality implies the cropped WZ1 intermediate predicate. -/
lemma IsExtremalPair.toWZ1
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    (h : IsExtremalPair sigma epsilon F U Y) :
    WZ1ExtremalPair sigma epsilon F U Y := by
  rcases h with
    ⟨hdelta, hdelta_one, hF_nonempty, hF_ball, hF_distinct,
      hU_uniform, hU_frostman, hY_dense, hY_upper, hY_lower⟩
  refine
    ⟨hdelta, hdelta_one, hF_nonempty, ?_, hF_distinct,
      hU_uniform, hU_frostman, hY_dense, hY_upper, hY_lower⟩
  rintro p ⟨i, hp⟩
  exact hF_ball i (Y.subset_body i hp)

/--
Recover full extremality from the WZ1 intermediate predicate by supplying
the family unit-ball condition separately.

The balanced-cover chain only tracks `Y.union ⊆ closedBall 0 1`, because the
paper clips tubes to a window while the formal carriers may protrude.  When the
original family already satisfies `F.IsInUnitBall` (as obtained from the
extremal-counterexample sequence), the two predicates are equivalent.
-/
lemma WZ1ExtremalPair.toIsExtremalPair
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    (h : WZ1ExtremalPair sigma epsilon F U Y)
    (hF_ball : F.IsInUnitBall) :
    IsExtremalPair sigma epsilon F U Y := by
  rcases h with
    ⟨hdelta, hdelta_one, hF_nonempty, _hY_ball, hF_distinct,
      hU_uniform, hU_frostman, hY_dense, hY_upper, hY_lower⟩
  exact
    ⟨hdelta, hdelta_one, hF_nonempty, hF_ball, hF_distinct,
      hU_uniform, hU_frostman, hY_dense, hY_upper, hY_lower⟩

/-- Increasing the error exponent weakens WZ1 intermediate extremality. -/
lemma WZ1ExtremalPair.mono_epsilon
    {delta sigma epsilon₁ epsilon₂ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    (h : WZ1ExtremalPair sigma epsilon₁ F U Y)
    (hepsilon : epsilon₁ ≤ epsilon₂) :
    WZ1ExtremalPair sigma epsilon₂ F U Y := by
  rcases h with
    ⟨hdelta, hdelta_one, hF_nonempty, hY_ball, hF_distinct,
      hU_uniform, hU_frostman, hY_dense, hY_upper, hY_lower⟩
  have h_uniform_power :
      Kakeya.realRpowENN delta (-epsilon₁) ≤
        Kakeya.realRpowENN delta (-epsilon₂) := by
    apply ENNReal.ofReal_mono
    apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one
    linarith
  have h_density_power :
      Kakeya.realRpowENN delta epsilon₂ ≤
        Kakeya.realRpowENN delta epsilon₁ := by
    apply ENNReal.ofReal_mono
    exact
      Real.rpow_le_rpow_of_exponent_ge
        hdelta hdelta_one hepsilon
  have h_upper_power :
      Kakeya.realRpowENN delta (sigma - epsilon₁) ≤
        Kakeya.realRpowENN delta (sigma - epsilon₂) := by
    apply ENNReal.ofReal_mono
    apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one
    linarith
  have h_lower_power :
      Kakeya.realRpowENN delta (sigma + epsilon₂) ≤
        Kakeya.realRpowENN delta (sigma + epsilon₁) := by
    apply ENNReal.ofReal_mono
    apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one
    linarith
  refine
    ⟨hdelta, hdelta_one, hF_nonempty, hY_ball, hF_distinct,
      hU_uniform.trans h_uniform_power, ?_, ?_,
      hY_upper.trans h_upper_power,
      h_lower_power.trans hY_lower⟩
  · intro rho j K hK_convex hK_subset
    exact
      (hU_frostman rho j K hK_convex hK_subset).trans (by
        gcongr)
  · exact
      (mul_le_mul_right' h_density_power F.toBodyFamily.mass).trans
        hY_dense

/-- Euclidean cross product, transported back to `Point3`. -/
def wz1Cross (u v : Point3) : Point3 :=
  WithLp.toLp 2 ((u : Fin 3 → ℝ) ⨯₃ (v : Fin 3 → ℝ))

/-- Absolute scalar triple product used in WZ1's narrow-point argument. -/
def wz1TripleProduct (u v w : Point3) : ℝ :=
  Matrix.det ![(u : Fin 3 → ℝ), (v : Fin 3 → ℝ), (w : Fin 3 → ℝ)]

/--
The shaded trilinear multiplicity used by the WZ1 planiness interface.

This is definitionally the same finite sum as the CV trilinear multiplicity
after rewriting CV's `tripleVolume` as the absolute scalar triple product.
Keeping the definition in the lightweight WZ1 layer prevents proposition-only
targets from importing the completed CV proof chain.
-/
def wz1ShadingTrilinearMultiplicity
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F) (p : Point3) : ENNReal :=
  ∑ i : Fin F.card, ∑ j : Fin F.card, ∑ k : Fin F.card,
    Set.indicator (Y.carrier i) (fun _ => (1 : ENNReal)) p *
      Set.indicator (Y.carrier j) (fun _ => (1 : ENNReal)) p *
      Set.indicator (Y.carrier k) (fun _ => (1 : ENNReal)) p *
        ENNReal.ofReal
          |wz1TripleProduct
            (F.tube i).direction
            (F.tube j).direction
            (F.tube k).direction|

/--
One affine correction segment in the WZ1 Proposition 27 construction.
The correction is extended to a global `C²` function using Lemma 28.
-/
structure WZ1SegmentCorrection where
  x₁ : ℝ
  x₂ : ℝ
  y₁ : ℝ
  y₂ : ℝ
  buffer : ℝ
  x₁_lt_x₂ : x₁ < x₂
  buffer_pos : 0 < buffer

namespace WZ1SegmentCorrection

/-- The interval on which the correction must equal its affine segment. -/
def core (segment : WZ1SegmentCorrection) : Set ℝ :=
  Set.Icc segment.x₁ segment.x₂

/-- The expanded interval outside which the correction vanishes. -/
def support (segment : WZ1SegmentCorrection) : Set ℝ :=
  Set.Icc (segment.x₁ - segment.buffer)
    (segment.x₂ + segment.buffer)

/-- The affine function prescribed on the core interval. -/
def affine (segment : WZ1SegmentCorrection) (x : ℝ) : ℝ :=
  segment.y₁ + (x - segment.x₁) *
    ((segment.y₂ - segment.y₁) / (segment.x₂ - segment.x₁))

/-- The exact contribution on points known to be either in the core or off support. -/
def value (segment : WZ1SegmentCorrection) (x : ℝ) : ℝ := by
  classical
  exact if x ∈ segment.core then segment.affine x else 0

/-- Scale-explicit first-derivative cost from WZ1 Lemma 28. -/
def firstCost (segment : WZ1SegmentCorrection) : ℝ :=
  (|segment.y₁| + |segment.y₂|) / segment.buffer +
    |(segment.y₂ - segment.y₁) / (segment.x₂ - segment.x₁)|

/-- Scale-explicit second-derivative cost from WZ1 Lemma 28. -/
def secondCost (segment : WZ1SegmentCorrection) : ℝ :=
  (|segment.y₁| + |segment.y₂|) / segment.buffer ^ 2 +
    |(segment.y₂ - segment.y₁) / (segment.x₂ - segment.x₁)| /
      segment.buffer

/--
A zero-order cost obtained by integrating the first-derivative bound from a
point one unit to the left of the expanded support.
-/
def valueCost (segment : WZ1SegmentCorrection) : ℝ :=
  (segment.x₂ - segment.x₁ + 2 * segment.buffer + 1) *
    segment.firstCost

end WZ1SegmentCorrection

/-- Rotate a vector in `Point2` by ninety degrees. -/
noncomputable def wz1Perp2 (v : Point2) : Point2 :=
  (-v (1 : Fin 2)) •
      EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
    v (0 : Fin 2) •
      EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

/--
The width-`radius` strip around the affine line through `base` in direction
`direction`.  The projection-theorem statements separately require the
direction to be unit.
-/
def wz1LineNeighborhood
    (base direction : Point2) (radius : ℝ) : Set Point2 :=
  {p | |inner ℝ (p - base) (wz1Perp2 direction)| ≤ radius}

/-- Number of points of a finite planar set in one affine strip. -/
def wz1DiscreteLineCount
    (A : DiscreteSet 2) (base direction : Point2)
    (radius : ℝ) : ENNReal := by
  classical
  exact
    ((A.filter fun p =>
      p ∈ wz1LineNeighborhood base direction radius).card : ENNReal)

/-- The finite dot-difference image `a · (b₁ - b₂)` of a tripartite graph. -/
def wz1DotDifferenceSet
    (H : Finset (Point2 × Point2 × Point2)) : Set ℝ := by
  classical
  exact
    ↑(H.image fun h => inner ℝ h.1 (h.2.1 - h.2.2))

/-- Number of active ordered direction triples with determinant at least `tau`. -/
def wz1LargeTripleCount
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (p : Point3) (tau : ℝ) : ℕ := by
  classical
  exact
    ((Finset.univ.product (Finset.univ.product Finset.univ)).filter fun ijk =>
      p ∈ Y.carrier ijk.1 ∧
      p ∈ Y.carrier ijk.2.1 ∧
      p ∈ Y.carrier ijk.2.2 ∧
      tau ≤
        |wz1TripleProduct
          (F.tube ijk.1).direction
          (F.tube ijk.2.1).direction
          (F.tube ijk.2.2).direction|).card

/--
The paper's broad points: at least `Q` active ordered triples have determinant
at least `tau`.
-/
def wz1CountedBroadSet
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (tau : ℝ) (Q : ℕ) : Set Point3 :=
  {p | p ∈ Y.union ∧ Q ≤ wz1LargeTripleCount Y p tau}

/--
A large-mass narrow refinement in the WZ1 Lemma 11 argument.

At every retained point, fewer than `Q` active ordered triples have scalar
triple product at least `tau`.
-/
structure WZ1NarrowRefinementData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (tau : ℝ) (Q : ℕ) where
  shading : Kakeya.Streamlined.TubeShading F
  subshading : IsSubshading shading Y
  carrier_eq :
    ∀ i, shading.carrier i =
      Y.carrier i \ wz1CountedBroadSet Y tau Q
  mass_lower : (1 / 2 : ENNReal) * Y.mass ≤ shading.mass
  large_triple_count_lt :
    ∀ p ∈ shading.union,
      wz1LargeTripleCount shading p tau < Q

/-- Number of active third directions narrow relative to one selected pair. -/
def wz1GoodThirdCount
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (p : Point3) (i j : Fin F.card) (tau : ℝ) : ℕ := by
  classical
  exact
    (Finset.univ.filter fun k =>
      p ∈ Y.carrier k ∧
      |wz1TripleProduct
        (F.tube i).direction
        (F.tube j).direction
        (F.tube k).direction| < tau).card

/--
A pointwise choice of two quantitatively transverse active tube directions.
-/
structure WZ1NarrowDirectionSelection
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (kappa : ℝ) where
  first : Point3 → Fin F.card
  second : Point3 → Fin F.card
  first_measurable : Measurable first
  second_measurable : Measurable second
  first_mem :
    ∀ p ∈ Y.union, p ∈ Y.carrier (first p)
  second_mem :
    ∀ p ∈ Y.union, p ∈ Y.carrier (second p)
  transverse :
    ∀ p ∈ Y.union,
      kappa ≤
        ‖wz1Cross
          (F.tube (first p)).direction
          (F.tube (second p)).direction‖

/-- Number of active directions lying within the cross-product threshold of one active tube. -/
def wz1CloseDirectionCount
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (p : Point3) (i : Fin F.card) (kappa : ℝ) : ℕ := by
  classical
  exact
    (Finset.univ.filter fun j =>
      p ∈ Y.carrier j ∧
        ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ <
          kappa).card

/--
The same-configuration input package for the three WZ1 Lemma 11 leaves.

It packages the loss-dependent extremal selection, constant-multiplicity
refinement, counted-broad mass budget, and robust transversality on one
shading.  Thus the later pruning and pair-selection theorems cannot assemble
unrelated existential configurations.
-/
structure WZ1PlaninessPreparationData
    (sigma epsilon delta : ℝ) where
  family : Kakeya.Streamlined.TubeFamily delta
  uniform : Kakeya.Streamlined.UniformTubeStructure family
  shading : Kakeya.Streamlined.TubeShading family
  extremal : IsExtremalPair sigma epsilon family uniform shading
  lowerMultiplicity : ℕ
  upperMultiplicity : ℕ
  constant_multiplicity :
    shading.HasConstantMultiplicity lowerMultiplicity upperMultiplicity
  lowerMultiplicity_bound :
    Kakeya.realRpowENN delta (2 - sigma + epsilon) * family.enncard ≤
      (lowerMultiplicity : ENNReal)
  upperMultiplicity_bound :
    (upperMultiplicity : ENNReal) ≤
      Kakeya.realRpowENN delta (2 - sigma - epsilon) * family.enncard
  tau : ℝ
  kappa : ℝ
  largeTripleThreshold : ℕ
  closeDirectionThreshold : ℕ
  kappa_pos : 0 < kappa
  weak_incidence_scale :
    tau / kappa ≤ Real.rpow delta (sigma / 2)
  broad_measurable :
    MeasurableSet
      (wz1CountedBroadSet shading tau largeTripleThreshold)
  broad_mass_small :
    2 * (∫⁻ p in
      wz1CountedBroadSet shading tau largeTripleThreshold,
        (shading.pointMultiplicity p : ENNReal)) ≤ shading.mass
  robust_close_direction_count :
    ∀ p ∈ shading.union, ∀ i,
      p ∈ shading.carrier i →
        wz1CloseDirectionCount shading p i kappa <
          closeDirectionThreshold
  closeDirectionThreshold_bound :
    (closeDirectionThreshold : ENNReal) ≤
      Kakeya.realRpowENN delta (2 - sigma + epsilon) *
        family.enncard
  good_triple_budget :
    ∀ p ∈ shading.union,
      let mu := shading.pointMultiplicity p
      4 * (largeTripleThreshold +
        3 * closeDirectionThreshold * mu ^ 2) ≤
          3 * mu ^ 3

/-- The normalized cross-product normal attached to a selected active pair. -/
def WZ1NarrowDirectionSelection.normal
    {delta kappa : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (selection : WZ1NarrowDirectionSelection Y kappa)
    (p : Point3) : Point3 :=
  let cross :=
    wz1Cross
      (F.tube (selection.first p)).direction
      (F.tube (selection.second p)).direction
  (‖cross‖)⁻¹ • cross

/--
The weak plane map produced before the multiscale Lipschitz refinement.
-/
structure WZ1WeakPlaneMapData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (incidenceScale : ℝ) where
  planeMap : Point3 → Point3
  measurable : Measurable planeMap
  unit : ∀ p ∈ Y.union, ‖planeMap p‖ = 1
  incidence :
    ∀ i p, p ∈ Y.carrier i →
      |inner ℝ (F.tube i).direction (planeMap p)| ≤
        incidenceScale

/--
The same-configuration weak planiness output of WZ1 Lemma 11.
-/
structure WZ1WeakPlaninessPackage
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (tau : ℝ) (Q : ℕ) (kappa : ℝ) where
  narrow : WZ1NarrowRefinementData Y tau Q
  selection :
    WZ1NarrowDirectionSelection narrow.shading kappa
  selected : Kakeya.Streamlined.TubeShading F
  selected_subshading : IsSubshading selected narrow.shading
  selected_carrier_eq :
    ∀ k, selected.carrier k =
      {p | p ∈ narrow.shading.carrier k ∧
        |wz1TripleProduct
          (F.tube (selection.first p)).direction
          (F.tube (selection.second p)).direction
          (F.tube k).direction| < tau}
  selected_pointMultiplicity_lower :
    ∀ p ∈ narrow.shading.union,
      narrow.shading.pointMultiplicity p ≤
        4 * selected.pointMultiplicity p
  selected_mass_lower :
    (1 / 4 : ENNReal) * narrow.shading.mass ≤ selected.mass
  planeMap :
    WZ1WeakPlaneMapData selected (tau / kappa)
  planeMap_eq :
    ∀ p ∈ selected.union,
      planeMap.planeMap p = selection.normal p

/--
The complete same-configuration output of WZ1 Lemma 11.

The counted-broad pruning and the measurable transverse-pair selection are
performed on the shading chosen by `preparation`.  The selected shading is a
subshading of that same source and retains at least one eighth of its aggregate
mass: one half survives broad pruning and one quarter survives the
third-direction selection.
-/
structure WZ1WeakPlaninessAssemblyData
    {sigma epsilon delta : ℝ}
    (preparation :
      WZ1PlaninessPreparationData sigma epsilon delta) where
  package :
    WZ1WeakPlaninessPackage
      preparation.shading preparation.tau
        preparation.largeTripleThreshold preparation.kappa
  selected_subshading :
    IsSubshading package.selected preparation.shading
  selected_mass_lower :
    (1 / 8 : ENNReal) * preparation.shading.mass ≤
      package.selected.mass

/--
The extremal weak plane-map package produced after completing WZ1 Lemma 11.

`internalLoss` is chosen only after the critical-floor structural parameter is
known.  The preparation and both Lemma 11 refinements remain dependent fields
of one configuration.  The selected shading is then proved extremal with the
caller-requested weaker `outputLoss`.
-/
structure WZ1ExtremalWeakPlaneMapData
    (sigma outputLoss delta : ℝ) where
  internalLoss : ℝ
  internalLoss_pos : 0 < internalLoss
  internalLoss_le : internalLoss ≤ outputLoss
  preparation :
    WZ1PlaninessPreparationData sigma internalLoss delta
  assembly : WZ1WeakPlaninessAssemblyData preparation
  extremal :
    IsExtremalPair sigma outputLoss
      preparation.family preparation.uniform
      assembly.package.selected
  planeMap_incidence :
    ∀ i p, p ∈ assembly.package.selected.carrier i →
      |inner ℝ
        (preparation.family.tube i).direction
        (assembly.package.planeMap.planeMap p)| ≤
          Real.rpow delta (sigma / 2)

/--
The WZ1 planiness output on one refined shading.

The incidence constant is `6 * delta` in the repository normalization:
the Lemma 12 carrier-containment cover contributes projective direction error
`4 * delta` in addition to the fine-scale incidence error `delta`, and the
stored bound retains one unit of harmless slack.  WZ1 Lemma 15 preserves the
cube-constant plane map rather than replacing it at the endpoint.  The
Lipschitz constant is explicit because Lemma 15 produces a `delta`-dependent
power loss, not a unit Lipschitz map.
-/
structure WZ1PlaneMapData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F) where
  planeMap : Point3 → Point3
  measurable : Measurable planeMap
  lipschitzConstant : NNReal
  lipschitz : LipschitzOnWith lipschitzConstant planeMap Y.union
  unit : ∀ p ∈ Y.union, ‖planeMap p‖ = 1
  incidence :
    ∀ i p, p ∈ Y.carrier i →
      |inner ℝ (F.tube i).direction (planeMap p)| ≤ 6 * delta

/--
Number of directed coordinate caps used to refine one projective ball of
radius `radius` into sets of Euclidean diameter at most `scale`.

The factor two records the two antipodal lifts.  Each lift is partitioned
coordinatewise into a three-dimensional grid of mesh `scale / sqrt 3`.
-/
def wz1OrientationCapCount (radius scale : ℝ) : ℕ :=
  2 * (Nat.ceil (2 * Real.sqrt 3 * radius / scale) + 1) ^ 3

/--
The oriented finite-cap refinement in the final pigeonholing step of WZ1
Lemma 13.

The finite map `cell` records the spatial coarse cube.  The refinement retains
one directed coordinate cap per cell as a full measurable restriction of the
shading, loses at most the factor `capCount` in aggregate shaded mass, and
upgrades projective closeness to an oriented same-cell estimate for the
original sphere-valued plane map.
-/
structure WZ1OrientedCellRefinementData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    {cellCount : ℕ}
    (cell : Point3 → Fin cellCount)
    (planeMap : Point3 → Point3)
    (capCount : ℕ) (scale : ℝ) where
  selectedSet : Set Point3
  selectedSet_measurable : MeasurableSet selectedSet
  shading : Kakeya.Streamlined.TubeShading F
  subshading : IsSubshading shading Y
  carrier_eq :
    ∀ i, shading.carrier i = Y.carrier i ∩ selectedSet
  mass_lower :
    Y.mass ≤ (capCount : ENNReal) * shading.mass
  same_cell :
    ∀ p ∈ shading.union, ∀ q ∈ shading.union,
      cell p = cell q →
        dist (planeMap p) (planeMap q) ≤ scale

/--
The finest-scale exact-cell refinement used before WZ1 Lemma 15.

One finite directed plane-map cap is retained in each measurable `delta`-cell.
The resulting representative map is constant on cells, while remaining within
`delta` of the original sphere-valued plane map on the selected shading.
-/
structure WZ1FinestCellPlaneMapData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    {cellCount : ℕ}
    (cell : Point3 → Fin cellCount)
    (planeMap : Point3 → Point3)
    (capCount : ℕ) where
  representativeMap : Point3 → Point3
  representativeMap_measurable : Measurable representativeMap
  selectedSet : Set Point3
  selectedSet_measurable : MeasurableSet selectedSet
  shading : Kakeya.Streamlined.TubeShading F
  subshading : IsSubshading shading Y
  carrier_eq :
    ∀ i, shading.carrier i = Y.carrier i ∩ selectedSet
  mass_lower :
    Y.mass ≤ (capCount : ENNReal) * shading.mass
  representativeMap_unit :
    ∀ p ∈ shading.union, ‖representativeMap p‖ = 1
  representativeMap_close :
    ∀ p ∈ shading.union,
      dist (representativeMap p) (planeMap p) ≤ delta / 2
  constant_on_cells :
    ∀ p ∈ shading.union, ∀ q ∈ shading.union,
      cell p = cell q →
        representativeMap p = representativeMap q
  nearby_same_cell :
    ∀ p ∈ shading.union, ∀ q ∈ shading.union,
      dist p q ≤ delta →
        cell p = cell q

/-- Number of directed plane-map caps used at the finest spatial scale. -/
def wz1FinestPlaneMapCapCount (delta : ℝ) : ℕ :=
  wz1OrientationCapCount 1 (delta / 2)

/-- Number of active balanced cells whose representatives lie near one cell. -/
noncomputable def wz1NearbyActiveCellCount
    {rho : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (coarseShading : Kakeya.Streamlined.TubeShading coarse)
    {cellCount : ℕ}
    (cell : Point3 → Fin cellCount)
    (representative : Fin cellCount → Point3)
    (c : Fin cellCount) : ℕ := by
  classical
  exact
    (Finset.univ.filter fun d : Fin cellCount =>
      {p | p ∈ coarseShading.union ∧ cell p = d}.Nonempty ∧
        dist (representative c) (representative d) ≤ 6 * rho).card

/--
The fine-scale output of WZ1 Proposition 5, Step 2.

The paper first balances the shaded mass of the coarse-parent fibers and then
applies Lemma 6 (`rescaledCoveredTube`) inside every retained parent.  After
one global constant-multiplicity pigeonhole, this produces a mass-retaining
same-family refinement with the pointwise fiber cap required later in
Proposition 5.  The critical-volume floor enters through the unit-rescaled
Lemma 6 argument; this cap is not a direct consequence of the formal
contained-mass Frostman inequality.
-/
structure WZ1Proposition5FiberRefinementData
    {delta sigma outputLoss massLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (rho : Kakeya.Streamlined.AdmissibleScale delta) where
  refined : Kakeya.Streamlined.TubeShading F
  subshading : IsSubshading refined Y
  refined_extremal :
    WZ1ExtremalPair sigma outputLoss F U refined
  fineMultiplicity : ℕ
  fineMultiplicity_pos : 0 < fineMultiplicity
  fine_constant_multiplicity :
    refined.HasConstantMultiplicity
      fineMultiplicity (2 * fineMultiplicity)
  fine_multiplicity_lower :
    Kakeya.realRpowENN delta (-sigma + outputLoss) ≤
      (fineMultiplicity : ENNReal)
  retained_mass :
    Kakeya.realRpowENN delta massLoss *
        F.toBodyFamily.mass ≤
      refined.mass
  fiber_multiplicity_upper :
    ∀ j p,
      ((U.cover rho).toFactoring.fiberPointMultiplicity
          refined j p : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho.1)
          (-sigma - outputLoss)

/--
The fixed-scale spatial-cover output of WZ1 Proposition 5.

For one caller-selected admissible scale `rho`, the producer may pass to a
new extremal subshading.  Only that output shading is covered, and only at
that scale.  This is the paper input used in Lemma 32 before one horizontal
interval is selected; it is not an every-scale cover on a fixed shading.
-/
structure WZ1Proposition5SpatialCoverData
    {delta sigma outputLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (rho : Kakeya.Streamlined.AdmissibleScale delta) where
  refined : Kakeya.Streamlined.TubeShading F
  subshading : IsSubshading refined Y
  refined_extremal :
    WZ1ExtremalPair sigma outputLoss F U refined
  spatial_cover :
    CanCoverByBalls refined.union rho.1
      (Kakeya.realRpowENN delta (-outputLoss) *
        Kakeya.realRpowENN rho.1 (-3 + sigma))

/--
The two-scale self-similarity output of WZ1 Proposition 5, before choosing the
associated representatives used by Lemmas 12--14.

The fine family and coherent cover remain the original indexed objects; a
refinement is represented by a same-family subshading.  The coarse shading is
a measurable subshading of the induced shading at scale `rho`, together with
explicit fine-to-parent compatibility.

The cell fields are producer-owned Proposition 5 data.  They formalize the
paper's Step 5 simultaneous refinement: the coarse shading is saturated on
each retained spatial cell, the global fine union has one common cell-volume
band, and every active parent fiber has one common cell-volume band.  These
certificates, together with the coarse and fiber point-multiplicity bounds,
are what make the later associated-parent restriction quantitatively
mass-retaining.  The same-cell induced certificate preserves the provenance
of the fine witness when a later refinement keeps whole cells.
-/
structure WZ1BalancedCoverCoreData
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (rho : Kakeya.Streamlined.AdmissibleScale delta) where
  refined : Kakeya.Streamlined.TubeShading F
  subshading : IsSubshading refined Y
  refined_extremal :
    WZ1ExtremalPair sigma epsilon F U refined
  fineMultiplicity : ℕ
  fineMultiplicity_pos : 0 < fineMultiplicity
  fine_constant_multiplicity :
    refined.HasConstantMultiplicity
      fineMultiplicity (2 * fineMultiplicity)
  fine_multiplicity_lower :
    Kakeya.realRpowENN delta (-sigma + epsilon) ≤
      (fineMultiplicity : ENNReal)
  fiberMultiplicity : ℕ
  fiberMultiplicity_pos : 0 < fiberMultiplicity
  fiber_constant_multiplicity :
    ∀ j,
      (U.cover rho).toFactoring.FiberHasConstantMultiplicity
        refined j fiberMultiplicity (2 * fiberMultiplicity)
  coarseShading :
    Kakeya.Streamlined.TubeShading (U.coarse rho)
  coarseUniform :
    Kakeya.Streamlined.UniformTubeStructure (U.coarse rho)
  coarse_extremal :
    WZ1ExtremalPair sigma epsilon
      (U.coarse rho) coarseUniform coarseShading
  induced_subshading :
    (U.cover rho).toFactoring.IsInducedSubshading
      refined coarseShading rho.1
  coarse_nonempty : coarseShading.union.Nonempty
  coarseMultiplicity : ℕ
  coarseMultiplicity_pos : 0 < coarseMultiplicity
  coarse_constant_multiplicity :
    coarseShading.HasConstantMultiplicity
      coarseMultiplicity (2 * coarseMultiplicity)
  point_compatibility :
    ∀ i p, p ∈ refined.carrier i →
      p ∈ coarseShading.carrier ((U.cover rho).parent i)
  direction_alignment :
    ∀ i,
      ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
        ‖((U.coarse rho).tube ((U.cover rho).parent i)).direction -
          sign • (F.tube i).direction‖ ≤ 4 * rho.1
  coarse_multiplicity_upper :
    ∀ p,
      (coarseShading.pointMultiplicity p : ENNReal) ≤
        Kakeya.realRpowENN rho.1 (-sigma - epsilon)
  fiber_multiplicity_upper :
    ∀ j p,
      ((U.cover rho).toFactoring.fiberPointMultiplicity
          refined j p : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho.1)
          (-sigma - epsilon)
  cellCount : ℕ
  cell : Point3 → Fin cellCount
  cell_measurable : Measurable cell
  same_cell_induced_subshading :
    ∀ j c,
      {p | p ∈ coarseShading.carrier j ∧ cell p = c} ⊆
        ((U.coarse rho).tube j).carrier ∩
          Metric.cthickening rho.1
            {q |
              ∃ i,
                (U.cover rho).parent i = j ∧
                q ∈ refined.carrier i ∧
                cell q = c}
  cellMass : ENNReal
  cellMass_pos : 0 < cellMass
  cellMass_ne_top : cellMass ≠ ⊤
  fiberCellMass : ENNReal
  fiberCellMass_pos : 0 < fiberCellMass
  fiberCellMass_ne_top : fiberCellMass ≠ ⊤
  cell_diameter :
    ∀ p ∈ coarseShading.union, ∀ q ∈ coarseShading.union,
      cell p = cell q →
        dist p q ≤ 2 * rho.1
  coarse_cell_volume_lower :
    ∀ c : Fin cellCount,
      {p | p ∈ coarseShading.union ∧ cell p = c}.Nonempty →
        Kakeya.realRpowENN rho.1 3 / 1000000 ≤
          MeasureTheory.volume
            {p | p ∈ coarseShading.union ∧ cell p = c}
  coarse_cell_saturation :
    ∀ j c,
      {p | p ∈ coarseShading.carrier j ∧ cell p = c}.Nonempty →
      {p | p ∈ coarseShading.union ∧ cell p = c} ⊆
        coarseShading.carrier j
  cell_balance :
    ∀ c : Fin cellCount,
      {p | p ∈ coarseShading.union ∧ cell p = c}.Nonempty →
        cellMass ≤
            MeasureTheory.volume
              (refined.union ∩ {p | cell p = c}) ∧
          MeasureTheory.volume
              (refined.union ∩ {p | cell p = c}) ≤
            2 * cellMass
  fiber_cell_balance :
    ∀ j c,
      {p | p ∈ coarseShading.carrier j ∧ cell p = c}.Nonempty →
        fiberCellMass ≤
            MeasureTheory.volume
              ((U.cover rho).toFactoring.fiberShadedUnion refined j ∩
                {p | cell p = c}) ∧
          MeasureTheory.volume
              ((U.cover rho).toFactoring.fiberShadedUnion refined j ∩
                {p | cell p = c}) ≤
            2 * fiberCellMass

/--
The associated-cell refinement of a WZ1 Proposition 5 core package.

The paper first chooses, in every retained spatial cell, a point of high fine
multiplicity and keeps precisely the coarse parents associated to that point.
The core cell-saturation and parent-fiber cell-balance certificates turn the
coarse and fiber multiplicity bounds into quantitative fine-mass retention.
Only after this selection does one obtain a single representative per spatial
cell and the bounded nearby-cell graph used by Lemmas 12--14.
-/
structure WZ1BalancedCoverData
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    extends WZ1BalancedCoverCoreData
      (sigma := sigma) (epsilon := epsilon) U Y rho where
  representative : Fin cellCount → Point3
  cell_fine_witness :
    ∀ p ∈ coarseShading.union,
      representative (cell p) ∈ refined.union ∧
        cell (representative (cell p)) = cell p
  representative_associated :
    ∀ j p, p ∈ coarseShading.carrier j →
      ∃ i,
        (U.cover rho).parent i = j ∧
          representative (cell p) ∈ refined.carrier i
  neighborBound : ℕ
  neighborBound_pos : 0 < neighborBound
  neighborBound_le : neighborBound ≤ 10000
  nearby_active_cells :
    ∀ c : Fin cellCount,
      {p | p ∈ coarseShading.union ∧ cell p = c}.Nonempty →
        wz1NearbyActiveCellCount
          coarseShading cell representative c ≤ neighborBound

/--
An associated-cell output tied to the supplied Proposition 5 core.

The subshading witnesses rule out an unrelated existential balanced cover:
both the fine and coarse outputs are refinements of the concrete input core.
The weaker output loss is carried by `balanced.refined_extremal` and
`balanced.coarse_extremal`.
-/
structure WZ1AssociatedCellRefinementData
    {delta sigma coreLoss outputLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (core : WZ1BalancedCoverCoreData
      (sigma := sigma) (epsilon := coreLoss) U Y rho) where
  balanced :
    WZ1BalancedCoverData
      (sigma := sigma) (epsilon := outputLoss) U Y rho
  fine_subshading :
    IsSubshading balanced.refined core.refined
  coarse_subshading :
    IsSubshading balanced.coarseShading core.coarseShading
  active_parent_density :
    ∀ parent,
      balanced.coarseShading.carrier parent ≠ ∅ →
        Kakeya.realRpowENN delta outputLoss *
            (U.cover rho).toFactoring.fiberMass parent ≤
          (U.cover rho).toFactoring.fiberShadedMass
            balanced.refined parent
  cellCount_eq : balanced.cellCount = core.cellCount
  cell_eq :
    ∀ p, Fin.cast cellCount_eq (balanced.cell p) = core.cell p

/--
The transverse coarse-pair selection at the heart of WZ1 Lemma 13.

For every active balanced cell, `firstParent` and `secondParent` select two
coarse tubes.  The selected fine shading is a full measurable restriction to
points that lie in one fine child of each selected parent and whose two fine
directions are transverse.  The explicit mass inequality records the two
fiber-multiplicity losses, the two coarse-multiplicity pigeonhole losses, and
the factor two from constant fine multiplicity.
-/
structure WZ1TransverseCoarsePairData
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (finePlaneMap : Point3 → Point3)
    (fineKappa coarseKappa : ℝ) where
  firstParent : Fin balanced.cellCount → Fin (U.coarse rho).card
  secondParent : Fin balanced.cellCount → Fin (U.coarse rho).card
  selectedSet : Set Point3
  selectedSet_measurable : MeasurableSet selectedSet
  shading : Kakeya.Streamlined.TubeShading F
  subshading : IsSubshading shading balanced.refined
  carrier_eq :
    ∀ i, shading.carrier i =
      balanced.refined.carrier i ∩ selectedSet
  mass_lower :
    (balanced.fineMultiplicity : ENNReal) ^ 2 *
        balanced.refined.mass ≤
      4 *
        Kakeya.realRpowENN (delta / rho.1)
            (-sigma - epsilon) ^ 2 *
          Kakeya.realRpowENN rho.1 (-sigma - epsilon) ^ 2 *
            shading.mass
  common_fine_pair :
    ∀ p ∈ shading.union,
      ∃ i j : Fin F.card,
        p ∈ balanced.refined.carrier i ∧
        p ∈ balanced.refined.carrier j ∧
        (U.cover rho).parent i =
          firstParent (balanced.cell p) ∧
        (U.cover rho).parent j =
          secondParent (balanced.cell p) ∧
        fineKappa ≤
          ‖wz1Cross (F.tube i).direction (F.tube j).direction‖
  parent_transverse :
    ∀ p ∈ shading.union,
      coarseKappa ≤
        ‖wz1Cross
          ((U.coarse rho).tube
            (firstParent (balanced.cell p))).direction
          ((U.coarse rho).tube
            (secondParent (balanced.cell p))).direction‖
  first_incidence :
    ∀ p ∈ shading.union,
      |inner ℝ
        ((U.coarse rho).tube
          (firstParent (balanced.cell p))).direction
        (finePlaneMap p)| ≤ 5 * rho.1
  second_incidence :
    ∀ p ∈ shading.union,
      |inner ℝ
        ((U.coarse rho).tube
          (secondParent (balanced.cell p))).direction
        (finePlaneMap p)| ≤ 5 * rho.1

/--
The bounded-neighbor cell selection used in WZ1 Corollary 14.

The selected shading is obtained by retaining whole balanced cells from the
oriented Lemma 13 refinement.  Its mass loss is at most the number of colors
needed for the nearby-cell graph.  Inside the selected shading, points at
distance at most `rho` must belong to the same balanced cell, so the oriented
same-cell estimate upgrades to a one-scale estimate.
-/
structure WZ1NearbyCellSeparationData
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (source : Kakeya.Streamlined.TubeShading F)
    (planeMap : Point3 → Point3)
    (capCount : ℕ) (scale : ℝ)
    (oriented :
      WZ1OrientedCellRefinementData
        source balanced.cell planeMap capCount scale) where
  source_subshading : IsSubshading source balanced.refined
  selectedCells : Finset (Fin balanced.cellCount)
  selectedSet : Set Point3
  selectedSet_eq :
    selectedSet = {p | balanced.cell p ∈ selectedCells}
  selectedSet_measurable : MeasurableSet selectedSet
  shading : Kakeya.Streamlined.TubeShading F
  subshading : IsSubshading shading oriented.shading
  carrier_eq :
    ∀ i, shading.carrier i =
      oriented.shading.carrier i ∩ selectedSet
  mass_lower :
    oriented.shading.mass ≤
      ((balanced.neighborBound + 1 : ℕ) : ENNReal) * shading.mass
  nearby_same_cell :
    ∀ p ∈ shading.union, ∀ q ∈ shading.union,
      dist p q ≤ rho.1 →
        balanced.cell p = balanced.cell q
  one_scale_planeMap :
    ∀ p ∈ shading.union, ∀ q ∈ shading.union,
      dist p q ≤ rho.1 →
        dist (planeMap p) (planeMap q) ≤ scale

/--
Number of directed caps in the one-scale Lemma 13 assembly.

The coarse parent pair is transverse at scale `fineKappa - 8 * rho` and each
parent direction is incident to the fine plane map at scale `5 * rho`.
-/
def wz1OneScaleOrientationCapCount (rho fineKappa : ℝ) : ℕ :=
  wz1OrientationCapCount
    (10 * (5 * rho) / (fineKappa - 8 * rho)) rho

/--
The complete one-scale plane-map refinement obtained from WZ1 Lemma 13 and
Corollary 14.

The dependent fields retain the actual transverse parent pair, the directed
cap refinement, and the nearby-cell color class on one configuration.  The
last inequality is the exact product of the pair, orientation-cap, and graph
coloring losses.
-/
structure WZ1OneScalePlaneMapData
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon) U Y rho)
    (finePlaneMap : Point3 → Point3)
    (fineKappa : ℝ) where
  pair :
    WZ1TransverseCoarsePairData
      balanced finePlaneMap fineKappa
        (fineKappa - 8 * rho.1)
  oriented :
    WZ1OrientedCellRefinementData
      pair.shading balanced.cell finePlaneMap
        (wz1OneScaleOrientationCapCount rho.1 fineKappa)
        rho.1
  separated :
    WZ1NearbyCellSeparationData
      balanced pair.shading finePlaneMap
        (wz1OneScaleOrientationCapCount rho.1 fineKappa)
        rho.1 oriented
  subshading :
    IsSubshading separated.shading balanced.refined
  planeMap_measurable : Measurable finePlaneMap
  planeMap_unit :
    ∀ p ∈ separated.shading.union, ‖finePlaneMap p‖ = 1
  planeMap_incidence :
    ∀ i p, p ∈ separated.shading.carrier i →
      |inner ℝ (F.tube i).direction (finePlaneMap p)| ≤ rho.1
  one_scale :
    ∀ p ∈ separated.shading.union,
      ∀ q ∈ separated.shading.union,
        dist p q ≤ rho.1 →
          dist (finePlaneMap p) (finePlaneMap q) ≤ rho.1
  mass_lower :
    (balanced.fineMultiplicity : ENNReal) ^ 2 *
        balanced.refined.mass ≤
      4 *
        Kakeya.realRpowENN (delta / rho.1)
            (-sigma - epsilon) ^ 2 *
          Kakeya.realRpowENN rho.1 (-sigma - epsilon) ^ 2 *
            (wz1OneScaleOrientationCapCount rho.1 fineKappa : ENNReal) *
              ((balanced.neighborBound + 1 : ℕ) : ENNReal) *
                separated.shading.mass

/--
The nested two-scale configuration used in WZ1 Lemma 13.

The first balanced cover is taken at the robust-transversality scale
`robustScale`.  The second is taken at the smaller target scale `fineScale`
on the first refined shading.  The close-direction count is transferred from
the first cover to the second and absorbed by the second fine multiplicity
before invoking the complete one-scale plane-map assembly.
-/
structure WZ1TwoScalePlaneMapData
    {delta sigma robustLoss fineLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    (robustScale fineScale :
      Kakeya.Streamlined.AdmissibleScale delta)
    (robustCover :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := robustLoss)
        U Y robustScale)
    (fineCover :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := fineLoss)
        U robustCover.refined fineScale)
    (planeMap : Point3 → Point3) where
  packingConstant : ℕ
  packingConstant_pos : 0 < packingConstant
  robust_close_count :
    ∀ p ∈ fineCover.refined.union,
      ∀ i, p ∈ fineCover.refined.carrier i →
        (wz1CloseDirectionCount
            fineCover.refined p i robustScale.1 : ENNReal) ≤
          (packingConstant : ENNReal) *
            Kakeya.realRpowENN (delta / robustScale.1)
              (-sigma - robustLoss)
  close_count_absorbed :
    ∀ p ∈ fineCover.refined.union,
      ∀ i, p ∈ fineCover.refined.carrier i →
        2 *
            wz1CloseDirectionCount
              fineCover.refined p i robustScale.1 ≤
          fineCover.fineMultiplicity
  oneScale :
    WZ1OneScalePlaneMapData
      fineCover planeMap robustScale.1
  subshading :
    IsSubshading oneScale.separated.shading Y
  planeMap_measurable : Measurable planeMap
  planeMap_unit :
    ∀ p ∈ oneScale.separated.shading.union,
      ‖planeMap p‖ = 1
  planeMap_incidence :
    ∀ i p, p ∈ oneScale.separated.shading.carrier i →
      |inner ℝ (F.tube i).direction (planeMap p)| ≤ fineScale.1
  one_scale :
    ∀ p ∈ oneScale.separated.shading.union,
      ∀ q ∈ oneScale.separated.shading.union,
        dist p q ≤ fineScale.1 →
          dist (planeMap p) (planeMap q) ≤ fineScale.1

/--
One iteration of WZ1 Corollary 14 with all quantitative losses absorbed back
into extremality on the original fine family.

The plane map itself is unchanged.  The output shading is a subshading of the
source, remains extremal with the requested weaker loss, and satisfies the
nearby-point estimate at `scale`.  `massLoss` records the exact finite and
power losses before they are bounded by the output error budget.
-/
structure WZ1ExtremalOneScalePlaneMapData
    {delta sigma outputLoss incidenceScale : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (planeMap : Point3 → Point3)
    (scale : Kakeya.Streamlined.AdmissibleScale delta) where
  shading : Kakeya.Streamlined.TubeShading F
  subshading : IsSubshading shading Y
  extremal : WZ1ExtremalPair sigma outputLoss F U shading
  massLoss : ENNReal
  massLoss_one : 1 ≤ massLoss
  massLoss_ne_top : massLoss ≠ ⊤
  mass_retention : Y.mass ≤ massLoss * shading.mass
  massLoss_bound :
    massLoss ≤ Kakeya.realRpowENN delta (-outputLoss)
  planeMap_measurable : Measurable planeMap
  planeMap_unit :
    ∀ p ∈ shading.union, ‖planeMap p‖ = 1
  planeMap_incidence :
    ∀ i p, p ∈ shading.carrier i →
      |inner ℝ (F.tube i).direction (planeMap p)| ≤ incidenceScale
  one_scale :
    ∀ p ∈ shading.union, ∀ q ∈ shading.union,
      dist p q ≤ scale.1 →
        dist (planeMap p) (planeMap q) ≤ scale.1

/--
The finite nested sequence of Corollary 14 refinements used in WZ1 Lemma 15.

`stage 0` is the original shading.  Every later stage is a subshading of its
predecessor and is extremal with the common output loss.  The unchanged plane
map satisfies the `delta^(k / N)` nearby-point estimate on stage `k`.
-/
structure WZ1FinitePlaneMapIterationData
    {delta sigma outputLoss incidenceScale : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (planeMap : Point3 → Point3)
    (N : ℕ) where
  shading : Kakeya.Streamlined.TubeShading F
  subshading : IsSubshading shading Y
  extremal : WZ1ExtremalPair sigma outputLoss F U shading
  planeMap_measurable : Measurable planeMap
  planeMap_unit :
    ∀ p ∈ shading.union, ‖planeMap p‖ = 1
  planeMap_incidence :
    ∀ i p, p ∈ shading.carrier i →
      |inner ℝ (F.tube i).direction (planeMap p)| ≤ incidenceScale
  one_scale :
    ∀ k : ℕ, 1 ≤ k → k < N →
      ∀ p ∈ shading.union,
        ∀ q ∈ shading.union,
          dist p q ≤ Real.rpow delta ((k : ℝ) / (N : ℝ)) →
            dist (planeMap p) (planeMap q) ≤
              Real.rpow delta ((k : ℝ) / (N : ℝ))

/--
The scale-changed cubical plane-map output prepared before WZ1 Lemma 15.

The paper first applies Lemma 12 to a finer weak-plane configuration and
passes to a new coarse scale.  At that new scale the family again carries a
coherent uniform structure and is extremal, while its plane map is measurable,
unit-valued, incident at scale `6 * delta`, and constant at the finest spatial
scale consumed by Lemma 15.

Keeping the new family and uniform structure in this dependent package prevents
the coarse shading from being treated as a same-family subshading of its finer
source.
-/
structure WZ1CubicalPlaneMapData
    (sigma loss delta : ℝ) where
  family : Kakeya.Streamlined.TubeFamily delta
  uniform : Kakeya.Streamlined.UniformTubeStructure family
  shading : Kakeya.Streamlined.TubeShading family
  extremal : WZ1ExtremalPair sigma loss family uniform shading
  planeMap : Point3 → Point3
  planeMap_measurable : Measurable planeMap
  planeMap_unit :
    ∀ p ∈ shading.union, ‖planeMap p‖ = 1
  planeMap_incidence :
    ∀ i p, p ∈ shading.carrier i →
      |inner ℝ (family.tube i).direction (planeMap p)| ≤
        6 * delta
  finest_constancy :
    ∀ p ∈ shading.union, ∀ q ∈ shading.union,
      dist p q ≤ delta →
        planeMap p = planeMap q

/--
The final Lipschitz plane-map output of WZ1 Lemma 15.

The representative map is exactly constant at the finest spatial scale and
satisfies all intermediate one-scale bounds on one extremal shading.  The
explicit Lipschitz constant is absorbed by the requested power budget.
-/
structure WZ1LipschitzPlaneMapData
    {delta sigma outputLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F) where
  shading : Kakeya.Streamlined.TubeShading F
  subshading : IsSubshading shading Y
  extremal : WZ1ExtremalPair sigma outputLoss F U shading
  planeMap : Point3 → Point3
  planeMap_measurable : Measurable planeMap
  lipschitzConstant : NNReal
  lipschitz :
    LipschitzOnWith lipschitzConstant planeMap shading.union
  lipschitz_bound :
    (lipschitzConstant : ENNReal) ≤
      Kakeya.realRpowENN delta (-outputLoss)
  unit : ∀ p ∈ shading.union, ‖planeMap p‖ = 1
  incidence :
    ∀ i p, p ∈ shading.carrier i →
      |inner ℝ (F.tube i).direction (planeMap p)| ≤ 6 * delta

/-- Restrict the final Lipschitz plane map to its selected shading. -/
def WZ1LipschitzPlaneMapData.toPlaneMapData
    {delta sigma outputLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    (data : WZ1LipschitzPlaneMapData
      (sigma := sigma) (outputLoss := outputLoss) U Y) :
    WZ1PlaneMapData data.shading where
  planeMap := data.planeMap
  measurable := data.planeMap_measurable
  lipschitzConstant := data.lipschitzConstant
  lipschitz := data.lipschitz
  unit := data.unit
  incidence := data.incidence

/-- The every-scale local-grain output from WZ1 Section 4. -/
structure WZ1LocalGrainData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (sigma : ℝ) (C : ENNReal)
    extends WZ1PlaneMapData Y where
  local_ad :
    ∀ rho : ℝ, delta ≤ rho → rho ≤ 1 →
      ∀ p : Point3, p ∈ Y.union →
      IsADSet1
        (scalarProjection (toWZ1PlaneMapData.planeMap p)
          (Y.union ∩ Metric.closedBall p (Real.sqrt rho)))
        rho (1 - sigma) C

/-- The local scalar projection inside the paper's `sqrt rho` ball. -/
def wz1LocalProjection
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (planeMap : Point3 → Point3)
    (p : Point3) (rho : ℝ) : Set ℝ :=
  scalarProjection (planeMap p)
    (Y.union ∩ Metric.closedBall p (Real.sqrt rho))

/--
WZ1 Lemma 17 output at one pair of scales.

The selected shading remains on the original fine family.  In every spatial
ball of radius `tau`, its scalar projection in the unchanged plane-map
direction has the paper's `rho`-covering bound.
-/
structure WZ1LocalGrainCubeCountData
    {delta sigma outputLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (plane : WZ1PlaneMapData Y)
    (rho tau : Kakeya.Streamlined.AdmissibleScale delta) where
  shading : Kakeya.Streamlined.TubeShading F
  subshading : IsSubshading shading Y
  extremal : WZ1ExtremalPair sigma outputLoss F U shading
  outputPlane : WZ1PlaneMapData shading
  planeMap_eq : outputPlane.planeMap = plane.planeMap
  lipschitzConstant_eq :
    outputPlane.lipschitzConstant = plane.lipschitzConstant
  covering :
    ∀ p ∈ shading.union,
      (↑(Metric.externalCoveringNumber
        (Real.toNNReal rho.1)
        (scalarProjection (outputPlane.planeMap p)
          (shading.union ∩ Metric.closedBall p tau.1))) : ENNReal) ≤
        Kakeya.realRpowENN delta (-outputLoss) *
          Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)

/--
WZ1 Lemma 18 output at one pair of scales.

The Lemma 17 count is localized to every interval of radius `tau` inside the
projection of one `sqrt rho` spatial ball.
-/
structure WZ1LocalGrainIntervalData
    {delta sigma outputLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (plane : WZ1PlaneMapData Y)
    (rho tau : Kakeya.Streamlined.AdmissibleScale delta) where
  shading : Kakeya.Streamlined.TubeShading F
  subshading : IsSubshading shading Y
  extremal : WZ1ExtremalPair sigma outputLoss F U shading
  outputPlane : WZ1PlaneMapData shading
  planeMap_eq : outputPlane.planeMap = plane.planeMap
  lipschitzConstant_eq :
    outputPlane.lipschitzConstant = plane.lipschitzConstant
  interval_covering :
    ∀ p ∈ shading.union, ∀ x : ℝ,
      (↑(Metric.externalCoveringNumber
        (Real.toNNReal rho.1)
        (wz1LocalProjection shading outputPlane.planeMap p rho.1 ∩
          Metric.closedBall x tau.1)) : ENNReal) ≤
        Kakeya.realRpowENN delta (-outputLoss) *
          Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)

/-- WZ1 Lemma 19 output: the local-grain AD bound at one fixed scale. -/
structure WZ1LocalGrainOneScaleData
    {delta sigma outputLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (plane : WZ1PlaneMapData Y)
    (rho : Kakeya.Streamlined.AdmissibleScale delta) where
  shading : Kakeya.Streamlined.TubeShading F
  subshading : IsSubshading shading Y
  extremal : WZ1ExtremalPair sigma outputLoss F U shading
  outputPlane : WZ1PlaneMapData shading
  planeMap_eq : outputPlane.planeMap = plane.planeMap
  lipschitzConstant_eq :
    outputPlane.lipschitzConstant = plane.lipschitzConstant
  local_ad :
    ∀ p ∈ shading.union,
      IsADSet1
        (wz1LocalProjection shading outputPlane.planeMap p rho.1)
        rho.1 (1 - sigma)
        (Kakeya.realRpowENN delta (-outputLoss))

/--
WZ1 Lemma 20 output: one extremal subshading carrying every-scale local
grains for the unchanged Lipschitz plane map.
-/
structure WZ1EveryScaleLocalGrainData
    {delta sigma outputLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (plane : WZ1PlaneMapData Y) where
  shading : Kakeya.Streamlined.TubeShading F
  subshading : IsSubshading shading Y
  extremal : WZ1ExtremalPair sigma outputLoss F U shading
  localGrains :
    WZ1LocalGrainData shading sigma
      (Kakeya.realRpowENN delta (-outputLoss))
  planeMap_eq :
    localGrains.planeMap = plane.planeMap
  lipschitzConstant_eq :
    localGrains.lipschitzConstant = plane.lipschitzConstant
  lipschitz_bound :
    (localGrains.lipschitzConstant : ENNReal) ≤
      Kakeya.realRpowENN delta (-outputLoss)

/--
The coarse plane map produced by WZ1 Lemma 12 from a balanced two-scale cover.

It is constant on the balanced spatial cells, agrees there with the fine
plane map at the selected representative, and is a measurable unit plane map
for the coarse shading.  The incidence scale is explicit because the
repository's carrier-containment cover gives direction error `4 * rho`.
-/
structure WZ1CoarsePlaneMapData
    {delta sigma epsilon incidenceScale : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced : WZ1BalancedCoverData
      (sigma := sigma) (epsilon := epsilon) U Y rho)
    (finePlaneMap : Point3 → Point3) where
  planeMap :
    WZ1WeakPlaneMapData balanced.coarseShading incidenceScale
  constant_on_cells :
    ∀ p ∈ balanced.coarseShading.union,
      ∀ q ∈ balanced.coarseShading.union,
        balanced.cell p = balanced.cell q →
          planeMap.planeMap p = planeMap.planeMap q
  representative_eq :
    ∀ p ∈ balanced.coarseShading.union,
      planeMap.planeMap p =
        finePlaneMap (balanced.representative (balanced.cell p))

/-- The global-grain and normalized `C²` slope output from WZ1 Section 5. -/
structure WZ1GlobalGrainData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (sigma : ℝ) (C : ENNReal) where
  slope : SlopeFunction
  normalized : slope.IsNormalized
  global_slab_ad : HasGlobalSlabAD Y slope sigma C

/-- Exact-slice compatibility view of the slab global-grain certificate. -/
lemma WZ1GlobalGrainData.global_ad
    {delta sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (global : WZ1GlobalGrainData Y sigma C) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (global.slope z))
          (horizontalSlice Y.union z))
        delta (1 - sigma) C :=
  global.global_slab_ad.exactSlice

/--
The unnormalized `C²` global slope produced by WZ1 Proposition 27.

The paper first obtains power-size bounds for the value and first two
derivatives.  Only the subsequent vertical rescaling in Proposition 21
normalizes these bounds to one.  The fixed extension constant is therefore
kept explicit and is selected before the source scale threshold.
-/
structure WZ1RawGlobalGrainData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (sigma : ℝ) (C : ENNReal) (rawLoss extensionConstant : ℝ) where
  slope : SlopeFunction
  extensionConstant_one : 1 ≤ extensionConstant
  value_bound :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |slope z| ≤
        extensionConstant * Real.rpow delta (-rawLoss)
  first_derivative_bound :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |deriv slope z| ≤
        extensionConstant * Real.rpow delta (-rawLoss)
  second_derivative_bound :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |deriv (deriv slope) z| ≤
        extensionConstant * Real.rpow delta (-rawLoss)
  global_slab_ad : HasGlobalSlabAD Y slope sigma C

/-- Exact-slice compatibility view of raw slab global-grain control. -/
lemma WZ1RawGlobalGrainData.global_ad
    {delta sigma rawLoss extensionConstant : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (global :
      WZ1RawGlobalGrainData
        Y sigma C rawLoss extensionConstant) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (global.slope z))
          (horizontalSlice Y.union z))
        delta (1 - sigma) C :=
  global.global_slab_ad.exactSlice

/--
The global-grain output before the WZ1 Proposition 21 `C²` upgrade.

The paper's Proposition 9 produces only a Lipschitz slope.  Keeping this
function as a plain real-valued map prevents the formal API from smuggling in
the `ContDiff ℝ 2` field of `SlopeFunction` before the projection-theorem
argument has been proved.
-/
structure WZ1LipschitzGlobalGrainData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (sigma : ℝ) (C : ENNReal) where
  slope : ℝ → ℝ
  lipschitzConstant : NNReal
  lipschitz :
    LipschitzOnWith lipschitzConstant slope (Set.Icc (-1 : ℝ) 1)
  global_slab_ad : HasGlobalSlabAD Y slope sigma C

/-- Exact-slice compatibility view of Lipschitz slab global-grain control. -/
lemma WZ1LipschitzGlobalGrainData.global_ad
    {delta sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (global : WZ1LipschitzGlobalGrainData Y sigma C) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (global.slope z))
          (horizontalSlice Y.union z))
        delta (1 - sigma) C :=
  global.global_slab_ad.exactSlice

/--
The same-configuration global-planiness output before the every-scale local
grain refinement.

The global Lipschitz slope and the plane map live on one extremal shading.
Both Lipschitz constants use the same explicit input-loss power, so the
dependent Lemma 20 transition can refine this package without choosing an
unrelated existential configuration.
-/
structure WZ1GlobalPlaninessData
    (sigma inputLoss delta : ℝ) where
  family : Kakeya.Streamlined.TubeFamily delta
  uniform : Kakeya.Streamlined.UniformTubeStructure family
  shading : Kakeya.Streamlined.TubeShading family
  vertical_chart : IsInVerticalChart family
  extremal :
    WZ1ExtremalPair sigma inputLoss family uniform shading
  global_grains :
    WZ1LipschitzGlobalGrainData shading sigma
      (Kakeya.realRpowENN delta (-inputLoss))
  planeMap : WZ1PlaneMapData shading
  slope_lipschitz_bound :
    (global_grains.lipschitzConstant : ENNReal) ≤
      Kakeya.realRpowENN delta (-inputLoss)
  slope_bound :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |global_grains.slope z| ≤ 3
  planeMap_vertical_bound :
    ∀ p ∈ shading.union,
      |planeMap.planeMap p (2 : Fin 3)| ≤ 1 / 2
  planeMap_lipschitz_bound :
    (planeMap.lipschitzConstant : ENNReal) ≤
      Kakeya.realRpowENN delta (-inputLoss)

/--
The same-configuration global and local grains before the final mild
rescaling in WZ1 Proposition 9.

At this stage both Lipschitz constants may carry a small power loss.  The
paper applies its rescaling lemma once more before using Lemmas 23--24.
-/
structure WZ1PreNormalizedPlaninessGraininessData
    (sigma epsilon delta : ℝ) where
  family : Kakeya.Streamlined.TubeFamily delta
  uniform : Kakeya.Streamlined.UniformTubeStructure family
  shading : Kakeya.Streamlined.TubeShading family
  vertical_chart : IsInVerticalChart family
  constant : ENNReal
  extremal : WZ1ExtremalPair sigma epsilon family uniform shading
  constant_one : 1 ≤ constant
  constant_ne_top : constant ≠ ⊤
  constant_bound :
    constant ≤ Kakeya.realRpowENN delta (-epsilon)
  global_grains :
    WZ1LipschitzGlobalGrainData shading sigma constant
  local_grains :
    WZ1LocalGrainData shading sigma constant
  slope_lipschitz_bound :
    (global_grains.lipschitzConstant : ENNReal) ≤
      Kakeya.realRpowENN delta (-epsilon)
  slope_bound :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |global_grains.slope z| ≤ 3
  planeMap_vertical_bound :
    ∀ p ∈ shading.union,
      |local_grains.planeMap p (2 : Fin 3)| ≤ 1 / 2
  planeMap_lipschitz_bound :
    (local_grains.lipschitzConstant : ENNReal) ≤
      Kakeya.realRpowENN delta (-epsilon)

/--
The paper-faithful final output of WZ1 Proposition 9.

The final mild rescaling changes the tube family and scale and normalizes both
the global slope and the local plane map to be `1`-Lipschitz.  The power-sized
bounds are retained for later loss bookkeeping.
-/
structure WZ1PlaninessGraininessPackage
    (sigma epsilon delta : ℝ)
    extends
      WZ1PreNormalizedPlaninessGraininessData sigma epsilon delta where
  slope_one_lipschitz :
    LipschitzOnWith 1 global_grains.slope (Set.Icc (-1 : ℝ) 1)
  planeMap_one_lipschitz :
    LipschitzOnWith 1 local_grains.planeMap shading.union

/--
One vertical trapezoid in the WZ1 Corollary 26 hierarchy.

The graph strip over `core` is centered on the affine function
`slope * z + intercept` and has vertical half-height `height`.
-/
structure WZ1VerticalTrapezoid where
  left : ℝ
  right : ℝ
  left_lt_right : left < right
  slope : ℝ
  intercept : ℝ
  height : ℝ
  height_pos : 0 < height

namespace WZ1VerticalTrapezoid

/-- Horizontal support interval of a vertical trapezoid. -/
def core (trapezoid : WZ1VerticalTrapezoid) : Set ℝ :=
  Set.Icc trapezoid.left trapezoid.right

/-- Affine center line of a vertical trapezoid. -/
def affine (trapezoid : WZ1VerticalTrapezoid) (z : ℝ) : ℝ :=
  trapezoid.slope * z + trapezoid.intercept

/-- Horizontal length of a vertical trapezoid. -/
def length (trapezoid : WZ1VerticalTrapezoid) : ℝ :=
  trapezoid.right - trapezoid.left

/--
Exact containment of the graph strip of `child` in the graph strip of
`parent`.
-/
def IsContainedIn
    (child parent : WZ1VerticalTrapezoid) : Prop :=
  child.core ⊆ parent.core ∧
    ∀ z ∈ child.core,
      |child.affine z - parent.affine z| + child.height ≤
        parent.height

end WZ1VerticalTrapezoid

/-- The paper scale `rho_j = delta^((j+1)/N)` at a hierarchy level. -/
def wz1Corollary26Scale
    (delta : ℝ) (levelCount : ℕ) (level : Fin levelCount) : ℝ :=
  Real.rpow delta
    (((level : ℕ) + 1 : ℝ) / (levelCount : ℝ))

/--
One same-configuration locally-linear output at one scale.

Every active height of the retained shading lies in one of the separated
intervals, and the source global slope is approximated by that interval's
affine center line.
-/
structure WZ1LocallyLinearOneScaleData
    {sigma inputLoss delta : ℝ}
    (source :
      WZ1PlaninessGraininessPackage sigma inputLoss delta)
    (outputLoss : ℝ)
    (rho : Kakeya.Streamlined.AdmissibleScale delta) where
  shading :
    Kakeya.Streamlined.TubeShading source.family
  subshading : IsSubshading shading source.shading
  extremal :
    WZ1ExtremalPair sigma outputLoss
      source.family source.uniform shading
  multiplicity : ℕ
  multiplicity_pos : 0 < multiplicity
  constant_multiplicity :
    shading.HasConstantMultiplicity
      multiplicity (2 * multiplicity)
  local_grains :
    WZ1LocalGrainData shading sigma source.constant
  planeMap_eq :
    local_grains.planeMap = source.local_grains.planeMap
  global_slab_ad :
    HasGlobalSlabAD shading
      source.global_grains.slope sigma source.constant
  trapezoids : Finset WZ1VerticalTrapezoid
  trapezoids_nonempty : trapezoids.Nonempty
  height_eq :
    ∀ trapezoid ∈ trapezoids,
      trapezoid.height = rho.1
  slope_bound :
    ∀ trapezoid ∈ trapezoids,
      |trapezoid.slope| ≤ 2
  length_bounds :
    ∀ trapezoid ∈ trapezoids,
      Real.rpow rho.1 (1 / 2 + outputLoss) ≤
          trapezoid.length ∧
        trapezoid.length ≤ Real.sqrt rho.1
  separated_cores :
    ∀ trapezoid ∈ trapezoids,
      ∀ other ∈ trapezoids,
        trapezoid ≠ other →
          ∀ z ∈ trapezoid.core,
            ∀ w ∈ other.core,
              Real.sqrt rho.1 ≤ |z - w|
  slope_approximation :
    ∀ trapezoid ∈ trapezoids,
      ∀ z ∈ trapezoid.core,
        horizontalSlice shading.union z ≠ ∅ →
          |source.global_grains.slope z -
              trapezoid.affine z| ≤ rho.1
  active_height_coverage :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice shading.union z ≠ ∅ →
        ∃ trapezoid ∈ trapezoids,
          z ∈ trapezoid.core

/--
The genuine finite Corollary 26 hierarchy on one final retained shading.

Every level covers all active heights.  Adjacent levels are linked by a
unique actual parent trapezoid whose graph strip contains the child, rather
than by unrelated numerical endpoint fields.
-/
structure WZ1LocallyLinearHierarchyData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (sourceSlope : ℝ → ℝ)
    (outputLoss : ℝ) where
  levelCount : ℕ
  levelCount_two : 2 ≤ levelCount
  trapezoids :
    Fin levelCount → Finset WZ1VerticalTrapezoid
  level_nonempty :
    ∀ level, (trapezoids level).Nonempty
  height_eq :
    ∀ level, ∀ trapezoid ∈ trapezoids level,
      trapezoid.height =
        wz1Corollary26Scale delta levelCount level
  slope_bound :
    ∀ level, ∀ trapezoid ∈ trapezoids level,
      |trapezoid.slope| ≤ 2
  length_bounds :
    ∀ level, ∀ trapezoid ∈ trapezoids level,
      Real.rpow
            (wz1Corollary26Scale delta levelCount level)
            (1 / 2 + outputLoss) ≤
          trapezoid.length ∧
        trapezoid.length ≤
          Real.sqrt
            (wz1Corollary26Scale delta levelCount level)
  separated_cores :
    ∀ level,
      ∀ trapezoid ∈ trapezoids level,
        ∀ other ∈ trapezoids level,
          trapezoid ≠ other →
            ∀ z ∈ trapezoid.core,
              ∀ w ∈ other.core,
                Real.sqrt
                    (wz1Corollary26Scale
                      delta levelCount level) ≤
                  |z - w|
  slope_approximation :
    ∀ level,
      ∀ trapezoid ∈ trapezoids level,
        ∀ z ∈ trapezoid.core,
          horizontalSlice Y.union z ≠ ∅ →
            |sourceSlope z - trapezoid.affine z| ≤
              wz1Corollary26Scale delta levelCount level
  active_height_coverage :
    ∀ level,
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        horizontalSlice Y.union z ≠ ∅ →
          ∃ trapezoid ∈ trapezoids level,
            z ∈ trapezoid.core
  unique_parent :
    ∀ parentLevel childLevel : Fin levelCount,
      (parentLevel : ℕ) + 1 = (childLevel : ℕ) →
        ∀ child ∈ trapezoids childLevel,
          ∃! parent,
            parent ∈ trapezoids parentLevel ∧
              child.IsContainedIn parent

/--
Same-configuration output of the finite locally-linear iteration, before
Proposition 27 converts parent-child trapezoid differences into smooth
segment corrections.
-/
structure WZ1LocallyLinearHierarchyPackage
    {sigma inputLoss delta : ℝ}
    (source :
      WZ1PlaninessGraininessPackage sigma inputLoss delta)
    (outputLoss : ℝ) where
  shading :
    Kakeya.Streamlined.TubeShading source.family
  subshading : IsSubshading shading source.shading
  extremal :
    WZ1ExtremalPair sigma outputLoss
      source.family source.uniform shading
  local_grains :
    WZ1LocalGrainData shading sigma source.constant
  planeMap_eq :
    local_grains.planeMap = source.local_grains.planeMap
  source_global_slab_ad :
    HasGlobalSlabAD shading
      source.global_grains.slope sigma source.constant
  hierarchy :
    WZ1LocallyLinearHierarchyData
      shading source.global_grains.slope outputLoss

/--
Certificate relating one Proposition 27 correction segment to an actual
Corollary 26 trapezoid and, away from the first level, its unique parent.
-/
structure WZ1TrapezoidSegmentSource
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {sourceSlope : ℝ → ℝ}
    {outputLoss : ℝ}
    (hierarchy :
      WZ1LocallyLinearHierarchyData
        Y sourceSlope outputLoss)
    (level : Fin hierarchy.levelCount)
    (segment : WZ1SegmentCorrection) where
  trapezoid : WZ1VerticalTrapezoid
  trapezoid_mem :
    trapezoid ∈ hierarchy.trapezoids level
  parent :
    Option WZ1VerticalTrapezoid
  parent_at_first :
    (level : ℕ) = 0 → parent = none
  parent_after_first :
    ∀ parentLevel : Fin hierarchy.levelCount,
      (parentLevel : ℕ) + 1 = (level : ℕ) →
        ∃ parentTrapezoid,
          parent = some parentTrapezoid ∧
          parentTrapezoid ∈
            hierarchy.trapezoids parentLevel ∧
          trapezoid.IsContainedIn parentTrapezoid
  core_eq :
    segment.core = trapezoid.core
  affine_eq :
    ∀ z ∈ segment.core,
      segment.affine z =
        match parent with
        | none => trapezoid.affine z
        | some parentTrapezoid =>
            trapezoid.affine z - parentTrapezoid.affine z

/--
One nested affine correction hierarchy from WZ1 Corollary 26 and
Proposition 27.

The hierarchy is already converted to the finite segment-correction format
consumed by the closed smooth-extension assembler.  The three cost bounds are
the quantitative output of nesting and the final mild rescaling, not free
assumptions to the final package theorem.
-/
structure WZ1NestedSlopeCorrectionData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (sigma : ℝ) (C : ENNReal) (A : ℝ) where
  A_one : 1 ≤ A
  segments : Finset WZ1SegmentCorrection
  disjoint_support :
    ∀ segment ∈ segments, ∀ other ∈ segments,
      segment ≠ other →
        Disjoint segment.support other.support
  core_or_off_support :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      (∀ segment ∈ segments,
        z ∈ segment.core ∨ z ∉ segment.support) ∨
        horizontalSlice Y.union z = ∅
  valueCost :
    ∑ segment ∈ segments, segment.valueCost ≤ 1 / A
  firstCost :
    ∑ segment ∈ segments, segment.firstCost ≤ 1 / A
  secondCost :
    ∑ segment ∈ segments, segment.secondCost ≤ 1 / A
  global_slab_ad :
    HasGlobalSlabAD Y
      (fun z => ∑ segment ∈ segments, segment.value z)
      sigma C

/--
The same-configuration output of WZ1 Corollary 26, ready for the closed
Proposition 27 smooth segment assembler.
-/
structure WZ1NestedSlopeCorrectionPackage
    {sigma inputLoss delta : ℝ}
    (source :
      WZ1PlaninessGraininessPackage sigma inputLoss delta)
    (outputLoss A : ℝ) where
  shading :
    Kakeya.Streamlined.TubeShading source.family
  subshading : IsSubshading shading source.shading
  extremal :
    WZ1ExtremalPair sigma outputLoss
      source.family source.uniform shading
  local_grains :
    WZ1LocalGrainData shading sigma source.constant
  planeMap_eq :
    local_grains.planeMap = source.local_grains.planeMap
  planeMap_lipschitz_bound :
    (local_grains.lipschitzConstant : ENNReal) ≤
      Kakeya.realRpowENN delta (-outputLoss)
  corrections :
    WZ1NestedSlopeCorrectionData
      shading sigma source.constant A

/--
The total prescribed affine correction at one height, summed over the
finitely many Corollary 26 levels.
-/
noncomputable def wz1MultiscaleSegmentValue
    (levelCount : ℕ)
    (segments : Fin levelCount → Finset WZ1SegmentCorrection)
    (z : ℝ) : ℝ := by
  classical
  exact
    ∑ level : Fin levelCount,
      ∑ segment ∈ segments level, segment.value z

/--
The active zero-order extension cost at one height.

Only segments whose expanded support contains the height can contribute.
This pointwise quantity, rather than the sum over every trapezoid in the
hierarchy, is what the separated-support argument in Proposition 27 bounds.
-/
noncomputable def wz1ActiveSegmentValueCost
    (levelCount : ℕ)
    (segments : Fin levelCount → Finset WZ1SegmentCorrection)
    (z : ℝ) : ℝ := by
  classical
  exact
    ∑ level : Fin levelCount,
      ∑ segment ∈
        (segments level).filter (fun segment => z ∈ segment.support),
          segment.valueCost

/-- The active first-derivative extension cost at one height. -/
noncomputable def wz1ActiveSegmentFirstCost
    (levelCount : ℕ)
    (segments : Fin levelCount → Finset WZ1SegmentCorrection)
    (z : ℝ) : ℝ := by
  classical
  exact
    ∑ level : Fin levelCount,
      ∑ segment ∈
        (segments level).filter (fun segment => z ∈ segment.support),
          segment.firstCost

/-- The active second-derivative extension cost at one height. -/
noncomputable def wz1ActiveSegmentSecondCost
    (levelCount : ℕ)
    (segments : Fin levelCount → Finset WZ1SegmentCorrection)
    (z : ℝ) : ℝ := by
  classical
  exact
    ∑ level : Fin levelCount,
      ∑ segment ∈
        (segments level).filter (fun segment => z ∈ segment.support),
          segment.secondCost

/-- Carrier-independent segment data used by Proposition 27 before selecting
either the legacy slab-AD interface or the pure exact-slice interface. -/
structure WZ1MultiscaleSlopeCorrectionCoreData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (rawLoss : ℝ) where
  levelCount : ℕ
  levelCount_two : 2 ≤ levelCount
  segments : Fin levelCount → Finset WZ1SegmentCorrection
  disjoint_support_at_level :
    ∀ level, ∀ segment ∈ segments level, ∀ other ∈ segments level,
      segment ≠ other →
        Disjoint segment.support other.support
  core_or_off_support :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      (∀ level, ∀ segment ∈ segments level,
        z ∈ segment.core ∨ z ∉ segment.support) ∨
        horizontalSlice Y.union z = ∅
  active_value_cost :
    ∀ z : ℝ,
      wz1ActiveSegmentValueCost levelCount segments z ≤
        Real.rpow delta (-rawLoss)
  active_first_cost :
    ∀ z : ℝ,
      wz1ActiveSegmentFirstCost levelCount segments z ≤
        Real.rpow delta (-rawLoss)
  active_second_cost :
    ∀ z : ℝ,
      wz1ActiveSegmentSecondCost levelCount segments z ≤
        Real.rpow delta (-rawLoss)

/--
Paper-faithful output of the Corollary 26 nested-trapezoid hierarchy after
conversion to the segment format used by Lemma 28.

Supports are disjoint only within each scale level.  Proposition 27 estimates
the active cost at a fixed height by summing at most one contribution per
level; it does not sum the costs of all trapezoids globally.  The resulting
power loss remains explicit until the final Proposition 21 rescaling.
-/
structure WZ1MultiscaleSlopeCorrectionData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (sigma : ℝ) (C : ENNReal) (rawLoss : ℝ) where
  levelCount : ℕ
  levelCount_two : 2 ≤ levelCount
  segments : Fin levelCount → Finset WZ1SegmentCorrection
  disjoint_support_at_level :
    ∀ level, ∀ segment ∈ segments level, ∀ other ∈ segments level,
      segment ≠ other →
        Disjoint segment.support other.support
  core_or_off_support :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      (∀ level, ∀ segment ∈ segments level,
        z ∈ segment.core ∨ z ∉ segment.support) ∨
        horizontalSlice Y.union z = ∅
  active_value_cost :
    ∀ z : ℝ,
      wz1ActiveSegmentValueCost levelCount segments z ≤
        Real.rpow delta (-rawLoss)
  active_first_cost :
    ∀ z : ℝ,
      wz1ActiveSegmentFirstCost levelCount segments z ≤
        Real.rpow delta (-rawLoss)
  active_second_cost :
    ∀ z : ℝ,
      wz1ActiveSegmentSecondCost levelCount segments z ≤
        Real.rpow delta (-rawLoss)
  global_slab_ad :
    HasGlobalSlabAD Y
      (wz1MultiscaleSegmentValue levelCount segments)
      sigma C

namespace WZ1MultiscaleSlopeCorrectionData

/-- Forget only the legacy slab-AD field. -/
def toCore
    {delta sigma rawLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (data : WZ1MultiscaleSlopeCorrectionData Y sigma C rawLoss) :
    WZ1MultiscaleSlopeCorrectionCoreData Y rawLoss where
  levelCount := data.levelCount
  levelCount_two := data.levelCount_two
  segments := data.segments
  disjoint_support_at_level := data.disjoint_support_at_level
  core_or_off_support := data.core_or_off_support
  active_value_cost := data.active_value_cost
  active_first_cost := data.active_first_cost
  active_second_cost := data.active_second_cost

end WZ1MultiscaleSlopeCorrectionData

/--
The same-configuration Corollary 26 output before Proposition 27 and the
final mild rescaling.
-/
structure WZ1MultiscaleSlopeCorrectionPackage
    {sigma inputLoss delta : ℝ}
    (source :
      WZ1PlaninessGraininessPackage sigma inputLoss delta)
    (outputLoss : ℝ) where
  rawLoss : ℝ
  rawLoss_pos : 0 < rawLoss
  rawLoss_le : rawLoss ≤ outputLoss / 10
  shading :
    Kakeya.Streamlined.TubeShading source.family
  subshading : IsSubshading shading source.shading
  extremal :
    WZ1ExtremalPair sigma outputLoss
      source.family source.uniform shading
  local_grains :
    WZ1LocalGrainData shading sigma source.constant
  planeMap_eq :
    local_grains.planeMap = source.local_grains.planeMap
  planeMap_lipschitz_bound :
    (local_grains.lipschitzConstant : ENNReal) ≤
      Kakeya.realRpowENN delta (-outputLoss)
  corrections :
    WZ1MultiscaleSlopeCorrectionData
      shading sigma source.constant rawLoss

/-- Assemble the two independent WZ1 grain outputs into the WZ2 consumer API. -/
def WZ1GlobalGrainData.combine
    {delta sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (global : WZ1GlobalGrainData Y sigma C)
    (localGrains : WZ1LocalGrainData Y sigma C) :
    C2GrainStructure Y sigma C where
  slope := global.slope
  slope_normalized := global.normalized
  planeMap := localGrains.planeMap
  planeMap_measurable := localGrains.measurable
  planeMapLipschitzConstant := localGrains.lipschitzConstant
  planeMap_lipschitz := localGrains.lipschitz
  planeMap_unit := localGrains.unit
  planeMap_incidence := localGrains.incidence
  global_slab_ad := global.global_slab_ad
  local_ad := localGrains.local_ad

/--
The complete same-configuration WZ1 output consumed by WZ2.

Global and local grains are fields of one dependent package, preventing three
unrelated existential configurations from being assembled after the fact.
-/
structure WZ1C2GrainPackage
    (sigma epsilon delta : ℝ) where
  family : Kakeya.Streamlined.TubeFamily delta
  uniform : Kakeya.Streamlined.UniformTubeStructure family
  shading : Kakeya.Streamlined.TubeShading family
  constant : ENNReal
  extremal : IsExtremalPair sigma epsilon family uniform shading
  cardinality_upper : HasExtremalCardinalityUpper family epsilon
  vertical_chart : IsInVerticalChart family
  constant_one : 1 ≤ constant
  constant_ne_top : constant ≠ ⊤
  constant_bound :
    constant ≤ Kakeya.realRpowENN delta (-epsilon)
  global_grains :
    WZ1GlobalGrainData shading sigma constant
  local_grains :
    WZ1LocalGrainData shading sigma constant
  planeMap_lipschitz_bound :
    (local_grains.lipschitzConstant : ENNReal) ≤
      Kakeya.realRpowENN delta (-epsilon)

/-- Forget the WZ1 stage split and expose the combined WZ2 grain structure. -/
def WZ1C2GrainPackage.grains
    {sigma epsilon delta : ℝ}
    (package : WZ1C2GrainPackage sigma epsilon delta) :
    C2GrainStructure package.shading sigma package.constant :=
  package.global_grains.combine package.local_grains

end Kakeya.Assouad
