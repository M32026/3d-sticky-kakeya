import MyLeanRepo.Kakeya.Streamlined.StickyInput
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Definitions for the WZ2 Theorem 5.2 workstream

This file contains only shared data and predicates.  It uses the indexed tube
families consumed by the streamlined proof, so multiplicities survive
refinement and rescaling.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

abbrev Point (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Point2 := Point 2
abbrev Point3 := Kakeya.Streamlined.Point3

/-- A finite discretized subset of Euclidean space. -/
abbrev DiscreteSet (n : ℕ) := Finset (Point n)

namespace DiscreteSet

/-- Cardinality valued in `ℝ≥0∞`. -/
def enncard {n : ℕ} (A : DiscreteSet n) : ENNReal :=
  A.card

/-- Number of points of `A` in a closed ball. -/
def ballCount {n : ℕ} (A : DiscreteSet n) (x : Point n) (r : ℝ) : ENNReal := by
  classical
  exact ((A.filter fun y => dist y x ≤ r).card : ENNReal)

/-- All points lie in the closed unit ball. -/
def IsInUnitBall {n : ℕ} (A : DiscreteSet n) : Prop :=
  ∀ x ∈ A, dist x 0 ≤ 1

/-- Distinct points are separated at scale `δ`. -/
def IsDeltaSeparated {n : ℕ} (A : DiscreteSet n) (δ : ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → x ≠ y → δ ≤ dist x y

/--
Frostman non-concentration in the normalized finite-set form:
`#(A ∩ B(x,r)) ≤ C r^s #A`.
-/
def IsFrostman {n : ℕ} (A : DiscreteSet n)
    (δ s : ℝ) (C : ENNReal) : Prop :=
  ∀ x : Point n, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
    A.ballCount x r ≤ C * Kakeya.realRpowENN r s * A.enncard

/--
Katz--Tao non-concentration in the normalized finite-set form:
`#(A ∩ B(x,r)) ≤ C (r/δ)^s`.
-/
def IsKatzTao {n : ℕ} (A : DiscreteSet n)
    (δ s : ℝ) (C : ENNReal) : Prop :=
  ∀ x : Point n, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
    A.ballCount x r ≤ C * Kakeya.realRpowENN (r / δ) s

end DiscreteSet

/-- A globally defined `C²` representative of a slope function. -/
structure SlopeFunction where
  toFun : ℝ → ℝ
  contDiff : ContDiff ℝ 2 toFun

instance : CoeFun SlopeFunction (fun _ => ℝ → ℝ) :=
  ⟨SlopeFunction.toFun⟩

namespace SlopeFunction

/-- The bounded `C²` condition used before the large-slope step. -/
def IsNormalized (f : SlopeFunction) : Prop :=
  ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    |f z| ≤ 1 ∧ |deriv f z| ≤ 1 ∧
      |deriv (deriv f) z| ≤ 1

/-- The nonsingular slope condition used in the twisted-projection step. -/
def IsNonsingular (f : SlopeFunction) : Prop :=
  ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    1 ≤ |deriv f z| ∧ |deriv f z| ≤ 2 ∧
      |deriv (deriv f) z| ≤ 1 / 100

/-- Reverse the vertical parameter, used to move the negative half-window to `[0,1]`. -/
def reflected (f : SlopeFunction) : SlopeFunction where
  toFun z := f (-z)
  contDiff := by
    have hf : ContDiff ℝ 2 f := f.contDiff
    have hneg : ContDiff ℝ 2 (fun z : ℝ => -z) := contDiff_neg
    exact hf.comp hneg

end SlopeFunction

/-- The twisted projection `π_f(x,y,z) = (x + f(z)y, z)`. -/
def twistedProjection (f : SlopeFunction) (p : Point3) : Point2 :=
  (p (0 : Fin 3) + f (p (2 : Fin 3)) * p (1 : Fin 3)) •
      EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
    p (2 : Fin 3) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

/-- Continuity of the twisted projection in the spatial variable. -/
@[fun_prop]
lemma continuous_twistedProjection (f : SlopeFunction) :
    Continuous (twistedProjection f) := by
  have hf : Continuous f := f.contDiff.continuous
  have h0 : Continuous (fun p : Point3 => p (0 : Fin 3)) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (0 : Fin 3)
  have h1 : Continuous (fun p : Point3 => p (1 : Fin 3)) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (1 : Fin 3)
  have h2 : Continuous (fun p : Point3 => p (2 : Fin 3)) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)
  have hhorizontal :
      Continuous
        (fun p : Point3 =>
          p (0 : Fin 3) + f (p (2 : Fin 3)) * p (1 : Fin 3)) :=
    h0.add ((hf.comp h2).mul h1)
  exact (hhorizontal.smul continuous_const).add
    (h2.smul continuous_const)

/--
Remove the common `c₀ z` drift and reorder the twisted-projection coordinates
as `(z, horizontal)`, matching the graph convention in the cinematic API.
-/
def cinematicShear (c₀ : ℝ) (p : Point2) : ℝ × ℝ :=
  (p (1 : Fin 2), p (0 : Fin 2) - c₀ * p (1 : Fin 2))

/-- The point `(x,y,z)` in the fixed Euclidean coordinate frame. -/
def point3 (x y z : ℝ) : Point3 :=
  x • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
    y • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) +
      z • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)

/--
The affine anisotropic map used after the large-slope interval.  Its
horizontal shear centers the old slope at the midpoint, its `y`-scale is the
normalizing factor for the new slope, and its `z`-coordinate maps `[c,d]` to
`[-1,1]`.
-/
def anisotropicRescalingMap
    (g : SlopeFunction) (c d m : ℝ) (p : Point3) : Point3 :=
  point3
    (p (0 : Fin 3) +
      g (c + (d - c) / 2) * p (1 : Fin 3))
    ((m * (d - c) / 2) * p (1 : Fin 3))
    (2 * (p (2 : Fin 3) - c) / (d - c) - 1)

/-- The linear image of one direction under `anisotropicRescalingMap`. -/
def anisotropicImageDirection
    (g : SlopeFunction) (c d m : ℝ) (v : Point3) : Point3 :=
  point3
    (v (0 : Fin 3) +
      g (c + (d - c) / 2) * v (1 : Fin 3))
    ((m * (d - c) / 2) * v (1 : Fin 3))
    ((2 / (d - c)) * v (2 : Fin 3))

/-- The line `t ↦ (a+ct,b+dt,t)` used in Section 7. -/
def parameterLine (a b c d t : ℝ) : Point3 :=
  point3 (a + c * t) (b + d * t) t

/-- The graph parametrization of the twisted image of `parameterLine`. -/
def twistedCurve (f : SlopeFunction) (a b c d t : ℝ) : Point2 :=
  (a + c * t + f t * (b + d * t)) •
      EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
    t • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

/-- Horizontal coordinate of a cinematic curve with parameters `(a,b,d)`. -/
def cinematicEval (f : SlopeFunction) (a b d t : ℝ) : ℝ :=
  a + b * f t + d * t * f t

/-- Scalar projection of a set in `ℝ³`. -/
def scalarProjection (v : Point3) (E : Set Point3) : Set ℝ :=
  (fun x => inner ℝ x v) '' E

/--
The `δ`-thickened tube-axis segment of length `sqrt ρ` beginning at parameter
`start`.  This is the exact geometric object used in WZ Lemma 30.
-/
def tubeSegmentCarrier
    (δ : ℝ) (base direction : Point3) (start ρ : ℝ) : Set Point3 :=
  Metric.cthickening δ
    ((fun t : ℝ => base + t • direction) ''
      Set.Icc start (start + Real.sqrt ρ))

/--
The bounded oriented slab used in the Convex-Wolff contradiction.  The
intersection with the unit ball makes its volume finite while retaining
convexity.
-/
def orientedUnitSlab
    (center normal : Point3) (width : ℝ) : Set Point3 :=
  Kakeya.DeltaTube.unitBall ∩
    {x | |inner ℝ (x - center) normal| ≤ width}

/-- Horizontal slice at height `z`. -/
def horizontalSlice (E : Set Point3) (z : ℝ) : Set Point3 :=
  {x | x ∈ E ∧ x (2 : Fin 3) = z}

/-- Direction `(1,m,0)` of a global grain. -/
def globalGrainDirection (m : ℝ) : Point3 :=
  EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
    m • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)

/--
The scalar global-grain coordinate with the slope evaluated at each point's
height.

This is the quantity that becomes the horizontal coordinate after the
anisotropic rescaling in WZ Lemma 8.  Keeping the height dependence inside
the map is essential when a target `rho`-strip corresponds to a source
`delta`-slab.
-/
def globalGrainProjection (slope : ℝ → ℝ) (E : Set Point3) : Set ℝ :=
  (fun p =>
    inner ℝ p
      (globalGrainDirection (slope (p (2 : Fin 3))))) '' E

/--
The part of `E` in the source height window and within `delta` of `z`.

The explicit intersection with `[-1,1]` keeps the statement valid at the two
boundary heights and is exactly the window used in WZ2 after the large-slope
normalization.
-/
def globalGrainSlab (E : Set Point3) (z delta : ℝ) : Set Point3 :=
  E ∩ {p | p (2 : Fin 3) ∈ Set.Icc (z - delta) (z + delta)} ∩
    {p | p (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1}

/--
Definition 7 from WZ1, specialized to subsets of `ℝ`: at every coarser scale
`ρ`, every radius-`r` ball meets at most `C (r/ρ)^α` many `ρ`-balls of `E`.

This is deliberately an upper-bound-only predicate.  In particular it is
preserved by subsets, exactly as required in the paper.
-/
def IsADSet1 (E : Set ℝ) (δ α : ℝ) (C : ENNReal) : Prop :=
  0 < δ ∧ 0 < α ∧ α ≤ 1 ∧ 1 ≤ C ∧
    E ⊆ Set.Icc (-4 : ℝ) 4 ∧
    ∀ (rho : ℝ) (hrho : 0 ≤ rho), δ ≤ rho → rho ≤ 1 →
      ∀ x : ℝ, ∀ r : ℝ, rho ≤ r → r ≤ 1 →
        (↑(Metric.externalCoveringNumber
          ⟨rho, hrho⟩
          (E ∩ Metric.closedBall x r)) : ENNReal) ≤
            C * Kakeya.realRpowENN (r / rho) α

/--
Paper-faithful global-grain control on horizontal slabs of thickness
comparable to `delta`.

The original paper first proves this slab statement for cubical shadings and
only then rewrites it as an exact-slice statement.  The slab form is the one
that survives target-radius thickening in WZ Lemma 8.
-/
def HasGlobalSlabAD {δ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F)
    (slope : ℝ → ℝ) (sigma : ℝ) (C : ENNReal) : Prop :=
  ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    IsADSet1
      (globalGrainProjection slope
        (globalGrainSlab Y.union z δ))
      δ (1 - sigma) C

/-- The upper-bound AD predicate is inherited by arbitrary subsets. -/
lemma IsADSet1.mono {E E' : Set ℝ} {δ α : ℝ} {C : ENNReal}
    (hE : IsADSet1 E δ α C) (hsub : E' ⊆ E) :
    IsADSet1 E' δ α C := by
  rcases hE with ⟨hδ, hα, hα_one, hC, hbounded, hcover⟩
  refine
    ⟨hδ, hα, hα_one, hC, hsub.trans hbounded, ?_⟩
  intro rho hrho hdelta_rho hrho_one x r hrho_r hr_one
  have hmono :
      Metric.externalCoveringNumber ⟨rho, hrho⟩
          (E' ∩ Metric.closedBall x r) ≤
        Metric.externalCoveringNumber ⟨rho, hrho⟩
          (E ∩ Metric.closedBall x r) :=
    Metric.externalCoveringNumber_mono_set
      (Set.inter_subset_inter hsub Set.Subset.rfl)
  have hmono' :
      (↑(Metric.externalCoveringNumber ⟨rho, hrho⟩
        (E' ∩ Metric.closedBall x r)) : ENNReal) ≤
      (↑(Metric.externalCoveringNumber ⟨rho, hrho⟩
        (E ∩ Metric.closedBall x r)) : ENNReal) := by
    exact_mod_cast hmono
  exact hmono'.trans
    (hcover rho hrho hdelta_rho hrho_one x r hrho_r hr_one)

/-- Increasing the upper-bound constant preserves one-dimensional AD control. -/
lemma IsADSet1.mono_constant
    {E : Set ℝ} {δ α : ℝ} {C C' : ENNReal}
    (hE : IsADSet1 E δ α C) (hCC' : C ≤ C') :
    IsADSet1 E δ α C' := by
  rcases hE with
    ⟨hδ, hα, hα_one, hC, hbounded, hcover⟩
  refine
    ⟨hδ, hα, hα_one, hC.trans hCC', hbounded, ?_⟩
  intro rho hrho hdelta_rho hrho_one x r hrho_r hr_one
  exact
    (hcover rho hrho hdelta_rho hrho_one x r hrho_r hr_one).trans
      (mul_le_mul_left hCC'
        (Kakeya.realRpowENN (r / rho) α))

/--
Exact horizontal slices inherit the global AD bound from the slab statement.
-/
lemma HasGlobalSlabAD.exactSlice
    {δ sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    {Y : Kakeya.Streamlined.TubeShading F}
    {slope : ℝ → ℝ} {C : ENNReal}
    (h : HasGlobalSlabAD Y slope sigma C) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (slope z))
          (horizontalSlice Y.union z))
        δ (1 - sigma) C := by
  intro z hz
  have hslab := h z hz
  apply hslab.mono
  rintro value ⟨p, hp, rfl⟩
  refine ⟨p, ⟨⟨hp.1, ?_⟩, ?_⟩, ?_⟩
  · simp only [Set.mem_setOf_eq, hp.2]
    constructor <;> linarith [hslab.1]
  · simpa [hp.2] using hz
  · simp only [globalGrainProjection, hp.2]

/-- A set is coverable by at most `N` closed balls of radius `r`. -/
def CanCoverByBalls (E : Set Point3) (r : ℝ) (N : ENNReal) : Prop :=
  ∃ centers : Finset Point3,
    (centers.card : ENNReal) ≤ N ∧
      ∀ y ∈ E, ∃ x ∈ centers, y ∈ Metric.closedBall x r

/-- The horizontal slab with third coordinate in `[a,b]`. -/
def horizontalSlab (a b : ℝ) : Set Point3 :=
  {x | x (2 : Fin 3) ∈ Set.Icc a b}

/-- Total shaded mass inside a horizontal slab. -/
def shadedMassInSlab {F : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading F) (a b : ℝ) : ENNReal :=
  ∑ i : Fin F.card,
    MeasureTheory.volume (Y.carrier i ∩ horizontalSlab a b)

/--
The pointwise tube-count refinement used in Steps 1--3 of the large-slope
argument.  On the shaded part of the slab, the number of shaded tubes through
each point is comparable to `δ^(2-σ) #𝕋`, with the paper's `2η` losses.
-/
def HasRefinedPointMultiplicityInSlab {δ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F)
    (sigma eta a b : ℝ) : Prop :=
  ∀ p ∈ Y.union ∩ horizontalSlab a b,
    Kakeya.realRpowENN δ (2 - sigma + 2 * eta) * F.enncard ≤
        (Y.pointMultiplicity p : ENNReal) ∧
      (Y.pointMultiplicity p : ENNReal) ≤
        Kakeya.realRpowENN δ (2 - sigma - 2 * eta) * F.enncard

/--
The Convex-Wolff count used in the large-slope contradiction.  The factor
`deltaTubeVolume 1` records the unit-scale tube-volume normalization, so this
form follows directly from the every-scale Frostman condition without
silently identifying that volume with one.
-/
def ConvexWolffBound {δ : ℝ}
    (F : Kakeya.Streamlined.TubeFamily δ) (C : ENNReal) : Prop :=
  ∀ W : Set Point3, Convex ℝ W →
    F.toBodyFamily.containedCount W * Kakeya.deltaTubeVolume 1 ≤
      C * MeasureTheory.volume W * F.enncard

/-- One shading is pointwise contained in another. -/
def IsSubshading {F : Kakeya.Streamlined.BodyFamily}
    (Z Y : Kakeya.Streamlined.Shading F) : Prop :=
  ∀ i, Z.carrier i ⊆ Y.carrier i

/-- Twisted image of the shaded union. -/
def twistedUnion {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F) (f : SlopeFunction) : Set Point2 :=
  twistedProjection f '' Y.union

/--
The tube-Wolff ball condition used in Section 7, in the normalization
`#{T ⊆ T_ρ} ≤ C ρ² #𝕋`.
-/
def TubeWolffBound {δ : ℝ} (F : Kakeya.Streamlined.TubeFamily δ)
    (C : ENNReal) : Prop :=
  ∀ rho : ℝ, δ ≤ rho → rho ≤ 1 →
    ∀ T : Kakeya.DeltaTube rho,
      F.toBodyFamily.containedCount T.carrier ≤
        C * Kakeya.realRpowENN rho 2 * F.enncard

/--
The basepoints of a tube family stay in a fixed bounded parameter window.
Unlike containment of the full tube carriers in the unit ball, this condition
is stable when a tube is thickened to a coarser radius without changing its
axis segment.
-/
def HasBoundedBase {δ : ℝ}
    (F : Kakeya.Streamlined.TubeFamily δ) (R : ℝ) : Prop :=
  ∀ i, ‖(F.tube i).base‖ ≤ R

/--
The shading lies in the `z ∈ [-1,1]` domain on which the slope hypotheses are
quantified.  This condition is inherited by subshadings and is preserved by
explicitly clipping induced coarse shadings to the same window.
-/
def IsInSlopeWindow {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F) : Prop :=
  Y.union ⊆ horizontalSlab (-1) 1

/--
The paper's coarse shading at radius `r`, clipped to the slope window.  Each
coarse shaded piece is the part of its coarse tube within distance `r` of the
union of the fine shaded pieces assigned to it by the explicit tube cover.
-/
def IsWindowedExactInducedShading {δ rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily δ}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (P : Kakeya.Streamlined.TubeCover fine coarse)
    (Y : Kakeya.Streamlined.TubeShading fine)
    (W : Kakeya.Streamlined.TubeShading coarse)
    (r : ℝ) : Prop :=
  ∀ j, W.carrier j =
    (coarse.tube j).carrier ∩ horizontalSlab (-1) 1 ∩
      Metric.cthickening r
        {x | ∃ i : Fin fine.card, P.parent i = j ∧ x ∈ Y.carrier i}

/--
Windowed induced shading for a relation-valued coarse cover.

Unlike `TubeCover`, one fine carrier may be covered by a finite coarse block
without lying in any single distinguished block member.  The relation records
every admissible fine--coarse incidence and is therefore the faithful
interface for the four-tube representative blocks used in the repository
unit-segment model.
-/
def IsWindowedExactRelationInducedShading {δ rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily δ}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (Rel : Fin fine.card → Fin coarse.card → Prop)
    (Y : Kakeya.Streamlined.TubeShading fine)
    (W : Kakeya.Streamlined.TubeShading coarse)
    (r : ℝ) : Prop :=
  ∀ j, W.carrier j =
    (coarse.tube j).carrier ∩ horizontalSlab (-1) 1 ∩
      Metric.cthickening r
        {x | ∃ i : Fin fine.card, Rel i j ∧ x ∈ Y.carrier i}

/--
All tubes lie in the fixed direction chart used by the twisted projection:
their directions are uniformly transverse to the horizontal planes.

The absolute value makes this independent of the orientation chosen for the
axis segment.
-/
def IsInVerticalChart {δ : ℝ}
    (F : Kakeya.Streamlined.TubeFamily δ) : Prop :=
  ∀ i, (1 / 2 : ℝ) ≤ |(F.tube i).direction (2 : Fin 3)|

/-- An extremal pair in the contradiction argument for Theorem 5.2. -/
def IsExtremalPair {δ : ℝ} (sigma epsilon : ℝ)
    (F : Kakeya.Streamlined.TubeFamily δ)
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F) : Prop :=
  0 < δ ∧ δ ≤ 1 ∧
    F.Nonempty ∧ F.IsInUnitBall ∧ F.IsEssentiallyDistinct ∧
    U.uniformity ≤ Kakeya.realRpowENN δ (-epsilon) ∧
    U.IsFrostmanAtEveryScale (Kakeya.realRpowENN δ (-epsilon)) ∧
    Y.IsLambdaDense (Kakeya.realRpowENN δ epsilon) ∧
    MeasureTheory.volume Y.union ≤
      Kakeya.realRpowENN δ (sigma - epsilon) ∧
    Kakeya.realRpowENN δ (sigma + epsilon) ≤
      MeasureTheory.volume Y.union

/--
The upper side of the paper's extremal cardinality window in dimension three.

This is not derivable from the repository's current carrier-containment form
of every-scale Frostman control, so WZ1/C2 extraction must export it
explicitly.
-/
def HasExtremalCardinalityUpper {δ : ℝ}
    (F : Kakeya.Streamlined.TubeFamily δ) (epsilon : ℝ) : Prop :=
  F.enncard ≤ Kakeya.realRpowENN δ (-2 - epsilon)

/--
The bounded-window extremal package produced by anisotropic rescaling.

WZ1 Lemma 8 places the rescaled rectangular prism in a fixed coordinate box
and then re-discretizes the image.  It does not assert that the exact affine
image lies in the Euclidean unit ball.  The fixed base bound and slope-window
condition are the properties actually consumed by the twisted-projection
argument.
-/
def IsProjectionExtremalPair {δ : ℝ} (sigma epsilon : ℝ)
    (F : Kakeya.Streamlined.TubeFamily δ)
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F) : Prop :=
  0 < δ ∧ δ ≤ 1 ∧
    F.Nonempty ∧ HasBoundedBase F 4 ∧ F.IsEssentiallyDistinct ∧
    U.uniformity ≤ Kakeya.realRpowENN δ (-epsilon) ∧
    U.IsFrostmanAtEveryScale (Kakeya.realRpowENN δ (-epsilon)) ∧
    Y.IsLambdaDense (Kakeya.realRpowENN δ epsilon) ∧
    IsInSlopeWindow Y ∧
    MeasureTheory.volume Y.union ≤
      Kakeya.realRpowENN δ (sigma - epsilon) ∧
    Kakeya.realRpowENN δ (sigma + epsilon) ≤
      MeasureTheory.volume Y.union

/--
The hereditary volume floor supplied by the critical definition of `sigma`.
For every later loss `loss ≥ epsilon`, any subshading that still retains
`delta^loss` aggregate density has union volume at least
`delta^(sigma + loss)`.
-/
def HasHereditaryVolumeFloor {δ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F)
    (sigma epsilon : ℝ) : Prop :=
  ∀ loss : ℝ, epsilon ≤ loss →
    ∀ Z : Kakeya.Streamlined.TubeShading F,
      IsSubshading Z Y →
      Z.IsLambdaDense (Kakeya.realRpowENN δ loss) →
        Kakeya.realRpowENN δ (sigma + loss) ≤
          MeasureTheory.volume Z.union

/--
The volume floor at one fixed structural loss.  Unlike
`HasHereditaryVolumeFloor`, this does not claim that one extracted
configuration controls every weaker density parameter.
-/
def HasVolumeFloorAt {δ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F)
    (sigma loss : ℝ) : Prop :=
  ∀ Z : Kakeya.Streamlined.TubeShading F,
    IsSubshading Z Y →
    Z.IsLambdaDense (Kakeya.realRpowENN δ loss) →
      Kakeya.realRpowENN δ (sigma + loss) ≤
        MeasureTheory.volume Z.union

/-- Every retained tube carries at least `threshold` shaded mass. -/
def HasPerTubeMass {δ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F)
    (threshold : ENNReal) : Prop :=
  ∀ i, Y.carrier i = ∅ ∨
    threshold ≤ MeasureTheory.volume (Y.carrier i)

/--
A subshading obtained only by deleting whole indexed tubes.
-/
def IsWholeTubeSubshading {δ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    (Z Y : Kakeya.Streamlined.TubeShading F) : Prop :=
  ∀ i, Z.carrier i = Y.carrier i ∨ Z.carrier i = ∅

theorem IsWholeTubeSubshading.refl {δ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F) :
    IsWholeTubeSubshading Y Y := by
  intro i
  exact Or.inl rfl

theorem IsWholeTubeSubshading.trans {δ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    {W Z Y : Kakeya.Streamlined.TubeShading F}
    (hWZ : IsWholeTubeSubshading W Z)
    (hZY : IsWholeTubeSubshading Z Y) :
    IsWholeTubeSubshading W Y := by
  intro i
  rcases hWZ i with hW | hW
  · rcases hZY i with hZ | hZ
    · exact Or.inl (hW.trans hZ)
    · exact Or.inr (hW.trans hZ)
  · exact Or.inr hW

theorem HasPerTubeMass.mono_whole {δ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    {Y Z : Kakeya.Streamlined.TubeShading F}
    {threshold : ENNReal}
    (hY : HasPerTubeMass Y threshold)
    (hZY : IsWholeTubeSubshading Z Y) :
    HasPerTubeMass Z threshold := by
  intro i
  rcases hZY i with hEq | hEmpty
  · simpa [hEq] using hY i
  · exact Or.inl hEmpty

/--
Every retained tube carries the prescribed amount of shaded mass inside one
fixed horizontal slab.  This is the per-tube fullness used by WZ Lemma 30 in
Section 6, Step 4; global mass outside the selected slab is irrelevant.
-/
def HasPerTubeMassInSlab {δ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F)
    (a b : ℝ) (threshold : ENNReal) : Prop :=
  ∀ i, Y.carrier i ∩ horizontalSlab a b = ∅ ∨
    threshold ≤
      MeasureTheory.volume (Y.carrier i ∩ horizontalSlab a b)

/--
An indexed three-tube cover of the images of source pieces.  WZ Lemma 8
produces three target tubes for each source tube; this is intentionally not a
`TubeCover`, whose single parent cannot encode a three-way geometric cover.
The product index can be flattened to `Fin (F.card * 3)` in a later assembly.
-/
structure ThreeTubeImageCover {δ rho : ℝ}
    (F : Kakeya.Streamlined.TubeFamily δ)
    (Φ : Point3 → Point3)
    (source : Fin F.card → Set Point3) where
  tube : Fin F.card → Fin 3 → Kakeya.DeltaTube rho
  covered :
    ∀ i, Φ '' source i ⊆
      ⋃ k : Fin 3, (tube i k).carrier
  vertical :
    ∀ i k, (1 / 2 : ℝ) ≤ |(tube i k).direction (2 : Fin 3)|

/-- The full affine line coaxial with a tube, forgetting its unit endpoints. -/
def tubeAxisLine {delta : ℝ}
    (T : Kakeya.DeltaTube delta) : Set Point3 :=
  {p | ∃ t : ℝ, p = T.base + t • T.direction}

/--
A three-tube image cover whose target axes are exactly the affine images of
the corresponding source axes.  This records the provenance required by WZ
Lemma 8, rather than retaining only set coverage.
-/
structure CoaxialThreeTubeImageCover {δ rho : ℝ}
    (F : Kakeya.Streamlined.TubeFamily δ)
    (Φ : Point3 → Point3)
    (source : Fin F.card → Set Point3)
    extends ThreeTubeImageCover (rho := rho) F Φ source where
  coaxial :
    ∀ i, (source i).Nonempty →
      ∀ k, tubeAxisLine (toThreeTubeImageCover.tube i k) =
        Φ '' tubeAxisLine (F.tube i)

/--
A cleaned anisotropic target family with the source provenance needed for
multiscale transport and twisted-projection estimates.
-/
structure CleanedAnisotropicTarget
    {delta rho c d m : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (Y : Kakeya.Streamlined.TubeShading F)
    (g : SlopeFunction) where
  family : Kakeya.Streamlined.TubeFamily rho
  shading : Kakeya.Streamlined.TubeShading family
  sourceVertical : IsInVerticalChart F
  sourceParent : Fin family.card → Fin F.card
  sourceFiberCap :
    ∀ i,
      (Finset.univ.filter fun j => sourceParent j = i).card ≤ 3
  massLoss : ENNReal
  one_le_massLoss : 1 ≤ massLoss
  massLoss_ne_top : massLoss ≠ ⊤
  boundedBase : HasBoundedBase family 3
  vertical : IsInVerticalChart family
  distinct : family.IsEssentiallyDistinct
  coaxial :
    ∀ j,
      tubeAxisLine (family.tube j) =
        anisotropicRescalingMap g c d m ''
          tubeAxisLine (F.tube (sourceParent j))
  localCarrier :
    ∀ j,
      shading.carrier j ⊆
        Metric.cthickening rho
          (anisotropicRescalingMap g c d m ''
            (Y.carrier (sourceParent j) ∩ horizontalSlab c d))
  slopeWindow : IsInSlopeWindow shading
  massLower :
    ENNReal.ofReal m * shadedMassInSlab Y c d ≤
      massLoss * shading.mass

/-- Global and local grain data available before the large-slope step. -/
structure C2GrainStructure {δ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F)
    (sigma : ℝ) (C : ENNReal) where
  slope : SlopeFunction
  slope_normalized : slope.IsNormalized
  planeMap : Point3 → Point3
  planeMap_measurable : Measurable planeMap
  planeMapLipschitzConstant : NNReal
  planeMap_lipschitz :
    LipschitzOnWith planeMapLipschitzConstant planeMap Y.union
  planeMap_unit : ∀ p ∈ Y.union, ‖planeMap p‖ = 1
  planeMap_incidence :
    ∀ i p, p ∈ Y.carrier i →
      |inner ℝ (F.tube i).direction (planeMap p)| ≤ 6 * δ
  global_slab_ad : HasGlobalSlabAD Y slope sigma C
  local_ad :
    ∀ rho : ℝ, δ ≤ rho → rho ≤ 1 →
      ∀ p : Point3, p ∈ Y.union →
      IsADSet1
        (scalarProjection (planeMap p)
          (Y.union ∩ Metric.closedBall p (Real.sqrt rho)))
        rho (1 - sigma) C

/--
The exact-slice global AD condition used by the large-slope argument follows
from the paper-faithful `delta`-slab condition.
-/
lemma C2GrainStructure.global_ad
    {δ sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (G : C2GrainStructure Y sigma C) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (G.slope z))
          (horizontalSlice Y.union z))
        δ (1 - sigma) C := by
  exact G.global_slab_ad.exactSlice

/--
The geometric data constructed from the small-slope contradiction hypothesis
after the stable multiplicity refinement in paper Section 6.

The shading `fine` is the paper's `F₂`, split into measurable tube--prism
pieces.  The support bound records that one tube meets at most three vertical
prisms.  Nonzero pieces are both almost full tube segments and local AD sets,
so the WZ Lemma 30 direction estimate applies to each active tube in the
eventually selected prism.  The transverse-strip field is the common-center
geometry needed to place those tubes in one oriented slab.
-/
structure LargeSlopeStep4Witness
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (sigma eta a b : ℝ) where
  rho : ℝ
  rho_eq : rho = 64 * (b - a) ^ 2
  rho_pos : 0 < rho
  delta_le_rho : delta ≤ rho
  rho_le_quarter : rho ≤ 1 / 4
  sqrt_rho_eq : Real.sqrt rho = 8 * (b - a)
  fine : Kakeya.Streamlined.TubeShading F
  fine_subshading : IsSubshading fine Y
  fine_in_slab : ∀ i, fine.carrier i ⊆ horizontalSlab a b
  per_tube_full :
    HasPerTubeMassInSlab fine a b
      (ENNReal.ofReal
        (Real.rpow delta (11 * eta) * delta ^ 2 * Real.sqrt rho))
  prismCount : ℕ
  prismCount_pos : 0 < prismCount
  prism : Fin prismCount → Set Point3
  center : Fin prismCount → Point3
  normal : Fin prismCount → Point3
  normal_unit : ∀ j, ‖normal j‖ = 1
  prism_transverse :
    ∀ j, prism j ⊆
      {p |
        |inner ℝ (p - center j) (normal j)| ≤ Real.sqrt rho}
  segmentStart : Fin F.card → Fin prismCount → ℝ
  piece : Fin F.card → Fin prismCount → Set Point3
  piece_measurable : ∀ i j, MeasurableSet (piece i j)
  piece_sub_fine : ∀ i j, piece i j ⊆ fine.carrier i
  piece_sub_prism : ∀ i j, piece i j ⊆ prism j
  piece_sub_segment :
    ∀ i j, piece i j ⊆
      tubeSegmentCarrier delta (F.tube i).base (F.tube i).direction
        (segmentStart i j) rho
  support : Fin F.card → Finset (Fin prismCount)
  support_card : ∀ i, (support i).card ≤ 3
  mem_support_iff :
    ∀ i j, j ∈ support i ↔
      MeasureTheory.volume (piece i j) ≠ 0
  total_piece_mass :
    Kakeya.realRpowENN delta (12 * eta) *
        ENNReal.ofReal (Real.sqrt rho) ≤
      ∑ i : Fin F.card, ∑ j : Fin prismCount,
        MeasureTheory.volume (piece i j)
  piece_mass_lower :
    ∀ i j, MeasureTheory.volume (piece i j) ≠ 0 →
      ENNReal.ofReal
          (Real.rpow delta (12 * eta) * delta ^ 2 *
            Real.sqrt rho) ≤
        MeasureTheory.volume (piece i j)
  piece_mass_upper :
    ∀ i j,
      MeasureTheory.volume (piece i j) ≤
        ENNReal.ofReal (Real.sqrt rho * delta ^ 2)
  piece_local_ad :
    ∀ i j, MeasureTheory.volume (piece i j) ≠ 0 →
      IsADSet1
        (scalarProjection (normal j) (piece i j))
        rho (1 - sigma)
        (Kakeya.realRpowENN delta (-(12 * eta)))
  prism_card_upper :
    (prismCount : ENNReal) ≤
      Kakeya.realRpowENN delta (-(12 * eta)) *
        Kakeya.realRpowENN rho ((-1 + sigma) / 2)

/--
The Proposition 5 refinement and slab selection used before WZ Lemma 31.

The cover is asserted only on the selected slab and at its selected scale.
The point-multiplicity refinement in the proof of Lemma 31 is performed later,
after assuming that the slope is small on this interval.  It is therefore not
a field of this stable input package.
-/
structure LargeSlopeRefinementData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (Y : Kakeya.Streamlined.TubeShading F)
    (sigma eta : ℝ) (C : ENNReal)
    (G : C2GrainStructure Y sigma C)
    (a b : ℝ) where
  left_mem : -1 ≤ a
  ordered : a < b
  right_mem : b ≤ 1
  scale_lower :
    Kakeya.realRpowENN delta (1 / 2 : ℝ) ≤
      ENNReal.ofReal (b - a)
  shading : Kakeya.Streamlined.TubeShading F
  grains : C2GrainStructure shading sigma C
  subshading : IsSubshading shading Y
  slope_eq : grains.slope = G.slope
  vertical_chart : IsInVerticalChart F
  ad_constant_one : 1 ≤ C
  ad_constant_ne_top : C ≠ ⊤
  ad_constant_bound :
    C ≤ Kakeya.realRpowENN delta (-(eta / 100))
  extremal : IsExtremalPair sigma eta F U shading
  cardinality_upper :
    HasExtremalCardinalityUpper F (eta / 1000)
  slab_mass :
    Kakeya.realRpowENN delta eta *
        ENNReal.ofReal (b - a) ≤
      shadedMassInSlab shading a b
  cover :
    CanCoverByBalls
      (shading.union ∩ horizontalSlab a b) (b - a)
      (Kakeya.realRpowENN delta (-eta) *
        Kakeya.realRpowENN (b - a) (-2 + sigma))

end Kakeya.Assouad
