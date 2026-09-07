import MyLeanRepo.Kakeya.Streamlined.Geometry
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Indexed finite families, shadings, refinements, and factorings

Families are indexed by `Fin card`.  Thus two members may have identical
geometric carriers while retaining different identities and multiplicities.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/-- A finite indexed family of geometric bodies. -/
structure BodyFamily where
  card : ℕ
  body : Fin card → Body

namespace BodyFamily

/-- Union of all carriers in the family. -/
def union (F : BodyFamily) : Set Point3 :=
  {x | ∃ i : Fin F.card, x ∈ (F.body i).carrier}

/-- Total mass `∑ᵢ |Fᵢ|`, counting indexed repetitions. -/
def mass (F : BodyFamily) : ENNReal :=
  ∑ i : Fin F.card, (F.body i).volume

/-- Cardinality, coerced to `ℝ≥0∞`. -/
def enncard (F : BodyFamily) : ENNReal :=
  F.card

/-- Indices of members whose carriers are contained in `K`. -/
def containedIndices (F : BodyFamily) (K : Set Point3) : Finset (Fin F.card) := by
  classical
  exact Finset.univ.filter fun i => (F.body i).carrier ⊆ K

@[simp]
lemma mem_containedIndices_iff {F : BodyFamily} {K : Set Point3} {i : Fin F.card} :
    i ∈ F.containedIndices K ↔ (F.body i).carrier ⊆ K := by
  classical
  have h_eq : F.containedIndices K =
      Finset.univ.filter (fun j => (F.body j).carrier ⊆ K) := by
    apply Finset.ext
    intro j
    unfold BodyFamily.containedIndices
    simp [Finset.mem_filter]
    <;> tauto
  rw [h_eq]
  simp [Finset.mem_filter]
  <;> tauto

/-- Number of indexed members contained in `K`. -/
def containedCount (F : BodyFamily) (K : Set Point3) : ENNReal :=
  (F.containedIndices K).card

/-- Total volume of indexed members contained in `K`. -/
def containedMass (F : BodyFamily) (K : Set Point3) : ENNReal :=
  ∑ i ∈ F.containedIndices K, (F.body i).volume

/-- Every carrier is measurable. -/
def IsMeasurable (F : BodyFamily) : Prop :=
  ∀ i, (F.body i).IsMeasurable

/-- Every carrier is convex. -/
def IsConvex (F : BodyFamily) : Prop :=
  ∀ i, (F.body i).IsConvex

/-- Every carrier lies in the closed unit ball. -/
def IsInUnitBall (F : BodyFamily) : Prop :=
  ∀ i, (F.body i).carrier ⊆ unitBall.carrier

/-- Pairwise geometric distinctness of indexed members. -/
def IsSetLike (F : BodyFamily) : Prop :=
  Function.Injective F.body

end BodyFamily

/-- A measurable shading indexed by the members of `F`. -/
structure Shading (F : BodyFamily) where
  carrier : Fin F.card → Set Point3
  measurable_carrier : ∀ i, MeasurableSet (carrier i)
  subset_body : ∀ i, carrier i ⊆ (F.body i).carrier

namespace Shading

/-- Union of all shaded pieces. -/
def union {F : BodyFamily} (Y : Shading F) : Set Point3 :=
  {x | ∃ i : Fin F.card, x ∈ Y.carrier i}

/-- Total shaded mass. -/
def mass {F : BodyFamily} (Y : Shading F) : ENNReal :=
  ∑ i : Fin F.card, MeasureTheory.volume (Y.carrier i)

/-- Aggregate `λ`-density, written without division. -/
def IsLambdaDense {F : BodyFamily} (Y : Shading F) (lambda : ENNReal) : Prop :=
  lambda * F.mass ≤ Y.mass

/-- Pointwise number of shaded members containing `x`. -/
def pointMultiplicity {F : BodyFamily} (Y : Shading F) (x : Point3) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin F.card => x ∈ Y.carrier i).card

/-- The average multiplicity is at most `M`, expressed without division. -/
def HasAverageMultiplicityAtMost {F : BodyFamily} (Y : Shading F)
    (M : ENNReal) : Prop :=
  Y.mass ≤ M * MeasureTheory.volume Y.union

/-- The pointwise multiplicity is between `m` and `M` on the shaded union. -/
def HasConstantMultiplicity {F : BodyFamily} (Y : Shading F)
    (m M : ℕ) : Prop :=
  ∀ x ∈ Y.union, m ≤ Y.pointMultiplicity x ∧ Y.pointMultiplicity x ≤ M

end Shading

/-- A subfamily retaining the identity of each selected original member. -/
structure Subfamily (F : BodyFamily) where
  family : BodyFamily
  embedding : Fin family.card ↪ Fin F.card
  carrier_eq : ∀ i, (family.body i).carrier = (F.body (embedding i)).carrier

namespace Subfamily

/-- The selected mass is at least the fraction `c` of the original mass. -/
def RetainsMass {F : BodyFamily} (S : Subfamily F) (c : ENNReal) : Prop :=
  c * F.mass ≤ S.family.mass

end Subfamily

/-- A simultaneous subfamily and shading refinement. -/
structure Refinement {F : BodyFamily} (Y : Shading F) where
  subfamily : Subfamily F
  shading : Shading subfamily.family
  shading_subset :
    ∀ i, shading.carrier i ⊆ Y.carrier (subfamily.embedding i)

namespace Refinement

/-- The refined shaded mass is at least the fraction `c` of the original. -/
def RetainsMass {F : BodyFamily} {Y : Shading F} (R : Refinement Y)
    (c : ENNReal) : Prop :=
  c * Y.mass ≤ R.shading.mass

end Refinement

/--
A factoring of `fine` through `coarse`.  The parent map is part of the data,
so fibers remain unambiguous even when coarse carriers overlap.
-/
structure Factoring (fine coarse : BodyFamily) where
  parent : Fin fine.card → Fin coarse.card
  parent_surjective : Function.Surjective parent
  contained : ∀ i, (fine.body i).carrier ⊆ (coarse.body (parent i)).carrier

namespace Factoring

/-- Indices in the fiber over the coarse member `j`. -/
def fiberIndices {fine coarse : BodyFamily} (P : Factoring fine coarse)
    (j : Fin coarse.card) : Finset (Fin fine.card) := by
  classical
  exact Finset.univ.filter fun i => P.parent i = j

/-- Total fine mass in a parent fiber. -/
def fiberMass {fine coarse : BodyFamily} (P : Factoring fine coarse)
    (j : Fin coarse.card) : ENNReal :=
  ∑ i ∈ P.fiberIndices j, (fine.body i).volume

/-- Fine mass in a parent fiber whose carriers are contained in `K`. -/
def fiberContainedMass {fine coarse : BodyFamily} (P : Factoring fine coarse)
    (j : Fin coarse.card) (K : Set Point3) : ENNReal := by
  classical
  exact ∑ i ∈ (P.fiberIndices j).filter
    (fun i => (fine.body i).carrier ⊆ K), (fine.body i).volume

/-- Shaded mass in a parent fiber. -/
def fiberShadedMass {fine coarse : BodyFamily} (P : Factoring fine coarse)
    (Y : Shading fine) (j : Fin coarse.card) : ENNReal :=
  ∑ i ∈ P.fiberIndices j, MeasureTheory.volume (Y.carrier i)

/-- `Z` is exactly the coarse shading induced by `Y` at radius `r`. -/
def IsExactInducedShading {fine coarse : BodyFamily}
    (P : Factoring fine coarse)
    (Y : Shading fine) (Z : Shading coarse) (r : ℝ) : Prop :=
  ∀ j, Z.carrier j =
    (coarse.body j).carrier ∩
      Metric.cthickening r
        {x | ∃ i : Fin fine.card, P.parent i = j ∧ x ∈ Y.carrier i}

/--
`Z` is a measurable subshading of the exact induced shading. This relation is
used only after a separate density or mass-retention conclusion excludes the
empty subshading.
-/
def IsInducedSubshading {fine coarse : BodyFamily}
    (P : Factoring fine coarse)
    (Y : Shading fine) (Z : Shading coarse) (r : ℝ) : Prop :=
  ∀ j, Z.carrier j ⊆
    (coarse.body j).carrier ∩
      Metric.cthickening r
        {x | ∃ i : Fin fine.card, P.parent i = j ∧ x ∈ Y.carrier i}

/--
Compatibility alias for branches created before the exact/subshading split.
New statements should use one of the two explicit names above.
-/
abbrev IsInducedShading {fine coarse : BodyFamily}
    (P : Factoring fine coarse)
    (Y : Shading fine) (Z : Shading coarse) (r : ℝ) : Prop :=
  P.IsInducedSubshading Y Z r

end Factoring

/-- A finite indexed family of geometric `δ`-tubes. -/
structure TubeFamily (δ : ℝ) where
  card : ℕ
  tube : Fin card → Kakeya.DeltaTube δ

namespace TubeFamily

/-- Forget the tube parametrization and retain indexed carriers. -/
def toBodyFamily {δ : ℝ} (F : TubeFamily δ) : BodyFamily where
  card := F.card
  body i := tubeBody (F.tube i)

/-- Cardinality, coerced to `ℝ≥0∞`. -/
def enncard {δ : ℝ} (F : TubeFamily δ) : ENNReal :=
  F.card

/-- Nominal total tube mass `#F · |T_δ|`. -/
def nominalMass {δ : ℝ} (F : TubeFamily δ) : ENNReal :=
  F.enncard * Kakeya.deltaTubeVolume δ

/-- All tubes lie in the closed unit ball. -/
def IsInUnitBall {δ : ℝ} (F : TubeFamily δ) : Prop :=
  ∀ i, (F.tube i).IsInUnitBall

/-- The indexed tubes are pairwise essentially distinct. -/
def IsEssentiallyDistinct {δ : ℝ} (F : TubeFamily δ) : Prop :=
  ∀ i j, i ≠ j → (F.tube i).EssentiallyDistinct (F.tube j)

/-- The family is nonempty. -/
def Nonempty {δ : ℝ} (F : TubeFamily δ) : Prop :=
  0 < F.card

end TubeFamily

/-- A shading on an indexed tube family. -/
abbrev TubeShading {δ : ℝ} (F : TubeFamily δ) :=
  Shading F.toBodyFamily

/-- An explicit parent assignment from fine tubes to coarse tubes. -/
structure TubeCover {δ ρ : ℝ} (fine : TubeFamily δ) (coarse : TubeFamily ρ) where
  parent : Fin fine.card → Fin coarse.card
  parent_surjective : Function.Surjective parent
  nested :
    ∀ i, (fine.tube i).carrier ⊆ (coarse.tube (parent i)).carrier

namespace TubeCover

/-- Number of fine tubes assigned to a coarse tube. -/
def fiberCount {δ ρ : ℝ} {fine : TubeFamily δ} {coarse : TubeFamily ρ}
    (P : TubeCover fine coarse) (j : Fin coarse.card) : ENNReal := by
  classical
  exact ((Finset.univ.filter fun i : Fin fine.card => P.parent i = j).card : ENNReal)

/-- Fiber sizes are comparable by the factor `C`. -/
def IsCUniform {δ ρ : ℝ} {fine : TubeFamily δ} {coarse : TubeFamily ρ}
    (P : TubeCover fine coarse) (C : ENNReal) : Prop :=
  1 ≤ C ∧ ∀ j k, P.fiberCount j ≤ C * P.fiberCount k

end TubeCover

end Kakeya.Streamlined
