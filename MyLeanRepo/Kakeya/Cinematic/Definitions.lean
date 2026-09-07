import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Cinematic functions and quasi-products

Definitions 1.4--1.6 from Pramanik--Yang--Zahl,
*A Furstenberg-type problem for circles, and a Kaufman-type restricted
projection theorem in `ℝ³`* (arXiv:2207.02259).

The interval of definition is normalized to `[0, 1]`. Closed intervals and
closed metric balls are used throughout; these endpoint conventions do not
affect the estimates in the paper.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Cinematic

/-- The normalized compact interval on which cinematic functions are defined. -/
def unitInterval : Set ℝ := Set.Icc 0 1

/-- A point of the normalized parameter interval. -/
abbrev UnitPoint := {x : ℝ // x ∈ unitInterval}

noncomputable instance : CompactSpace UnitPoint := by
  change CompactSpace (Set.Icc (0 : ℝ) 1)
  infer_instance

/--
A real-valued `C²` function on the unit interval.

The value and its first two derivatives are intrinsic data on the interval.
The final field asserts that this jet comes from a global `C²` extension, but
the extension itself is not stored as data. Thus different extensions of the
same function do not produce distinct elements at distance zero.
-/
structure C2Function where
  value : C(UnitPoint, ℝ)
  firstDeriv : C(UnitPoint, ℝ)
  secondDeriv : C(UnitPoint, ℝ)
  hasExtension :
    ∃ extension : ℝ → ℝ,
      ContDiff ℝ 2 extension ∧
      (∀ x : UnitPoint, extension x = value x) ∧
      (∀ x : UnitPoint, deriv extension x = firstDeriv x) ∧
      ∀ x : UnitPoint, deriv (deriv extension) x = secondDeriv x

instance : CoeFun C2Function (fun _ => UnitPoint → ℝ) :=
  ⟨fun f x => f.value x⟩

namespace C2Function

/-- The continuous two-jet underlying a `C2Function`. -/
def toJet (f : C2Function) :
    C(UnitPoint, ℝ) × C(UnitPoint, ℝ) × C(UnitPoint, ℝ) :=
  (f.value, f.firstDeriv, f.secondDeriv)

theorem toJet_injective : Function.Injective toJet := by
  intro f g h
  cases f
  cases g
  simp_all [toJet]

/--
The `C²` metric is the product sup metric on value, first derivative, and
second derivative. Using a genuine `MetricSpace` lets the proof reuse
Mathlib's ball, separation, and doubling-space APIs.
-/
noncomputable instance : MetricSpace C2Function :=
  MetricSpace.induced toJet toJet_injective inferInstance

/-- A chosen global `C²` extension, used only to invoke calculus theorems. -/
noncomputable def extension (f : C2Function) : ℝ → ℝ :=
  Classical.choose f.hasExtension

theorem extension_contDiff (f : C2Function) : ContDiff ℝ 2 f.extension :=
  (Classical.choose_spec f.hasExtension).1

@[simp]
theorem extension_eq_value (f : C2Function) (x : UnitPoint) :
    f.extension x = f x :=
  (Classical.choose_spec f.hasExtension).2.1 x

@[simp]
theorem deriv_extension_eq_firstDeriv (f : C2Function) (x : UnitPoint) :
    deriv f.extension x = f.firstDeriv x :=
  (Classical.choose_spec f.hasExtension).2.2.1 x

@[simp]
theorem secondDeriv_extension_eq_secondDeriv (f : C2Function)
    (x : UnitPoint) :
    deriv (deriv f.extension) x = f.secondDeriv x :=
  (Classical.choose_spec f.hasExtension).2.2.2 x

end C2Function

/-- The pointwise distance between the two-jets of two functions. -/
def jetGap (f g : C2Function) (x : UnitPoint) : ℝ :=
  |f x - g x| +
    |f.firstDeriv x - g.firstDeriv x| +
    |f.secondDeriv x - g.secondDeriv x|

/--
The `C²` distance: the maximum of the three uniform distances encoded by the
product metric on the continuous two-jet.
-/
def c2Distance (f g : C2Function) : ℝ :=
  dist f g

/-- The closed `C²` ball used in the doubling and Frostman conditions. -/
def c2Ball (center : C2Function) (radius : ℝ) : Set C2Function :=
  Metric.closedBall center radius

@[simp]
theorem c2Distance_eq_dist (f g : C2Function) :
    c2Distance f g = dist f g :=
  rfl

@[simp]
theorem mem_c2Ball {f center : C2Function} {radius : ℝ} :
    f ∈ c2Ball center radius ↔ c2Distance f center ≤ radius := by
  simp [c2Ball, c2Distance, dist_comm]

theorem value_dist_le_c2Distance (f g : C2Function) :
    dist f.value g.value ≤ c2Distance f g := by
  change dist f.value g.value ≤
    dist (C2Function.toJet f) (C2Function.toJet g)
  simp [C2Function.toJet, Prod.dist_eq]

theorem firstDeriv_dist_le_c2Distance (f g : C2Function) :
    dist f.firstDeriv g.firstDeriv ≤ c2Distance f g := by
  change dist f.firstDeriv g.firstDeriv ≤
    dist (C2Function.toJet f) (C2Function.toJet g)
  simp [C2Function.toJet, Prod.dist_eq]

theorem secondDeriv_dist_le_c2Distance (f g : C2Function) :
    dist f.secondDeriv g.secondDeriv ≤ c2Distance f g := by
  change dist f.secondDeriv g.secondDeriv ≤
    dist (C2Function.toJet f) (C2Function.toJet g)
  simp [C2Function.toJet, Prod.dist_eq]

theorem abs_value_sub_le_c2Distance (f g : C2Function) (x : UnitPoint) :
    |f x - g x| ≤ c2Distance f g := by
  calc
    |f x - g x| = dist (f.value x) (g.value x) := by
      simp [Real.dist_eq]
    _ ≤ dist f.value g.value := ContinuousMap.dist_apply_le_dist x
    _ ≤ c2Distance f g := value_dist_le_c2Distance f g

theorem abs_firstDeriv_sub_le_c2Distance (f g : C2Function)
    (x : UnitPoint) :
    |f.firstDeriv x - g.firstDeriv x| ≤ c2Distance f g := by
  calc
    |f.firstDeriv x - g.firstDeriv x| =
        dist (f.firstDeriv x) (g.firstDeriv x) := by
      simp [Real.dist_eq]
    _ ≤ dist f.firstDeriv g.firstDeriv :=
      ContinuousMap.dist_apply_le_dist x
    _ ≤ c2Distance f g := firstDeriv_dist_le_c2Distance f g

theorem abs_secondDeriv_sub_le_c2Distance (f g : C2Function)
    (x : UnitPoint) :
    |f.secondDeriv x - g.secondDeriv x| ≤ c2Distance f g := by
  calc
    |f.secondDeriv x - g.secondDeriv x| =
        dist (f.secondDeriv x) (g.secondDeriv x) := by
      simp [Real.dist_eq]
    _ ≤ dist f.secondDeriv g.secondDeriv :=
      ContinuousMap.dist_apply_le_dist x
    _ ≤ c2Distance f g := secondDeriv_dist_le_c2Distance f g

theorem jetGap_le_three_mul_c2Distance (f g : C2Function)
    (x : UnitPoint) :
    jetGap f g x ≤ 3 * c2Distance f g := by
  have h₀ := abs_value_sub_le_c2Distance f g x
  have h₁ := abs_firstDeriv_sub_le_c2Distance f g x
  have h₂ := abs_secondDeriv_sub_le_c2Distance f g x
  simp only [jetGap]
  linarith

/--
A family of cinematic functions with cinematic constant `K` and doubling
constant `D` (Definition 1.6).

The doubling condition is expanded directly: every radius-`r` ball in the
family is covered by at most `D` radius-`r/2` balls with centers in the family.
-/
def IsCinematicFamily (family : Set C2Function) (K D : ℝ) : Prop :=
  (∀ ⦃f⦄, f ∈ family → ∀ ⦃g⦄, g ∈ family → c2Distance f g ≤ K) ∧
  (∀ ⦃f⦄, f ∈ family → ∀ r : ℝ, 0 < r →
    ∃ centers : Set C2Function,
      centers.Finite ∧ centers ⊆ family ∧
      (centers.ncard : ℝ) ≤ D ∧
      ∀ ⦃g⦄, g ∈ family → c2Distance f g ≤ r →
        ∃ h ∈ centers, c2Distance h g ≤ r / 2) ∧
  (∀ ⦃f⦄, f ∈ family → ∀ ⦃g⦄, g ∈ family →
    ∀ x : UnitPoint,
      K⁻¹ * c2Distance f g ≤ jetGap f g x)

/--
An absolute first-derivative bound for every function in a family.

This is deliberately separate from `IsCinematicFamily`: cinematic curvature
controls differences inside the family, while metric graph neighborhoods
require an absolute slope bound to compare them uniformly with vertical
neighborhoods.
-/
def HasUniformFirstDerivativeBound
    (family : Set C2Function) (L : ℝ) : Prop :=
  ∀ ⦃f⦄, f ∈ family → ∀ x : UnitPoint, |f.firstDeriv x| ≤ L

/--
An absolute `C²` jet bound for every function in a family.

Unlike `IsCinematicFamily`, this controls the location of the family in
`C²([0,1])`, not only pairwise differences. It is the normalization needed
when a small-scale threshold must be chosen uniformly before the concrete
family.
-/
def HasUniformC2Bound
    (family : Set C2Function) (M : ℝ) : Prop :=
  ∀ ⦃f⦄, f ∈ family → ∀ x : UnitPoint,
    |f x| ≤ M ∧
      |f.firstDeriv x| ≤ M ∧
      |f.secondDeriv x| ≤ M

namespace HasUniformC2Bound

theorem value
    {family : Set C2Function} {M : ℝ}
    (h : HasUniformC2Bound family M) :
    ∀ ⦃f⦄, f ∈ family → ∀ x : UnitPoint, |f x| ≤ M := by
  intro f hf x
  exact (h hf x).1

theorem firstDerivative
    {family : Set C2Function} {M : ℝ}
    (h : HasUniformC2Bound family M) :
    HasUniformFirstDerivativeBound family M := by
  intro f hf x
  exact (h hf x).2.1

theorem secondDerivative
    {family : Set C2Function} {M : ℝ}
    (h : HasUniformC2Bound family M) :
    ∀ ⦃f⦄, f ∈ family → ∀ x : UnitPoint,
      |f.secondDeriv x| ≤ M := by
  intro f hf x
  exact (h hf x).2.2

end HasUniformC2Bound

/-- A finite collection of cinematic functions, represented extensionally. -/
structure FiniteFunctionFamily where
  carrier : Set C2Function
  finite : carrier.Finite

namespace FiniteFunctionFamily

/-- Pairwise separation in the genuine `C²` metric. -/
def IsDeltaSeparated (F : FiniteFunctionFamily) (δ : ℝ) : Prop :=
  ∀ ⦃f⦄, f ∈ F.carrier →
    ∀ ⦃g⦄, g ∈ F.carrier → f ≠ g → δ ≤ dist f g

/-- The finite set underlying a finite function family. -/
def toFinset (F : FiniteFunctionFamily) : Finset C2Function :=
  F.finite.toFinset

/-- Number of functions in the family. -/
def card (F : FiniteFunctionFamily) : ℕ :=
  F.carrier.ncard

end FiniteFunctionFamily

/--
A union of intervals of length `δ`, with endpoints normalized to closed
intervals. The indexing set need not be finite, matching Definition 1.4.
-/
def IsUnionOfDeltaIntervals (E : Set ℝ) (δ : ℝ) : Prop :=
  ∃ starts : Set ℝ, E = ⋃ a ∈ starts, Set.Icc a (a + δ)

/--
Definition 1.4: a one-dimensional `(δ, α; C)₁` set.
-/
def IsDeltaSet (E : Set ℝ) (δ α C : ℝ) : Prop :=
  E ⊆ unitInterval ∧
  MeasurableSet E ∧
  IsUnionOfDeltaIntervals E δ ∧
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    volume (E ∩ Set.Icc a b) ≤
      ENNReal.ofReal
        (C * Real.rpow δ (1 - α) * Real.rpow (b - a) α)

/--
Definition 1.5: a
`(δ, α; C)₁ × (δ, β; C)₁` quasi-product.
-/
def IsQuasiProduct (E : Set (ℝ × ℝ)) (δ α β C : ℝ) : Prop :=
  MeasurableSet E ∧
  ∃ A : Set ℝ, ∃ fiber : ℝ → Set ℝ,
    IsDeltaSet A δ α C ∧
    (∀ a ∈ A, IsDeltaSet (fiber a) δ β C) ∧
    E = {p | p.1 ∈ A ∧ p.2 ∈ fiber p.1}

/-- Graph of a cinematic function over the unit interval. -/
def functionGraph (f : C2Function) : Set (ℝ × ℝ) :=
  {p | ∃ hp : p.1 ∈ unitInterval, p.2 = f ⟨p.1, hp⟩}

/--
The `δ`-neighborhood `f^δ` of the graph of `f`. The product metric on
`ℝ × ℝ` is an equivalent normalization of the Euclidean metric in the paper.
-/
def graphNeighborhood (f : C2Function) (δ : ℝ) : Set (ℝ × ℝ) :=
  Metric.thickening δ (functionGraph f)

theorem isOpen_graphNeighborhood (f : C2Function) (δ : ℝ) :
    IsOpen (graphNeighborhood f δ) :=
  Metric.isOpen_thickening

theorem measurableSet_graphNeighborhood (f : C2Function) (δ : ℝ) :
    MeasurableSet (graphNeighborhood f δ) :=
  (isOpen_graphNeighborhood f δ).measurableSet

/-- Number of graph neighborhoods containing a point, coerced to `ℝ`. -/
def multiplicity (F : FiniteFunctionFamily) (δ : ℝ) (p : ℝ × ℝ) : ℝ :=
  ∑ f ∈ F.toFinset,
    (graphNeighborhood f δ).indicator (fun _ => (1 : ℝ)) p

theorem measurable_multiplicity (F : FiniteFunctionFamily) (δ : ℝ) :
    Measurable (multiplicity F δ) := by
  classical
  unfold multiplicity
  apply Finset.measurable_fun_sum
  intro f hf
  exact measurable_const.indicator (measurableSet_graphNeighborhood f δ)

/--
The Frostman non-concentration condition (1.7) for a finite function family.
-/
def HasFrostmanBound (F : FiniteFunctionFamily)
    (δ ε ζ : ℝ) : Prop :=
  ∀ center : C2Function, ∀ r : ℝ, δ ≤ r →
    ((F.carrier ∩ c2Ball center r).ncard : ℝ) ≤
      Real.rpow δ (-ε) * Real.rpow (r / δ) ζ

/--
Katz--Tao non-concentration with a fixed multiplicative constant.

This is the form produced by the WZ2 Section 7 extraction: after passing to a
large subset, the family has cardinality at most `C / δ`, and the number of
functions in every ball of radius `r ∈ [δ,1]` is at most `C * (r / δ)`.
-/
def FiniteFunctionFamily.HasKatzTaoBound (F : FiniteFunctionFamily)
    (δ C : ℝ) : Prop :=
  (F.card : ℝ) ≤ C / δ ∧
    ∀ center : C2Function, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      ((F.carrier ∩ c2Ball center r).ncard : ℝ) ≤ C * (r / δ)

end Kakeya.Cinematic
