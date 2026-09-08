import MyLeanRepo.Kakeya.Streamlined.Geometry
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Indexed finite families, shadings, refinements, and factorings

Families are indexed by `Fin card`.  Thus two members may have identical
geometric carriers while retaining different identities and multiplicities.

`Factoring` is the authoritative partition-bookkeeping structure.  Its fibers
are inverse images of one chosen parent map and therefore form a disjoint
partition.  Geometric full-containment fibers are defined separately on tube
families; they may overlap and must never be used with factoring identities
without an explicit bridge.
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

/-- `containedMass` is monotone in the containing set. -/
lemma containedMass_mono (F : BodyFamily) {K K' : Set Point3} (h : K ⊆ K') :
    F.containedMass K ≤ F.containedMass K' := by
  have h1 : F.containedIndices K ⊆ F.containedIndices K' := by
    intro i hi
    have h2 : (F.body i).carrier ⊆ K := by
      simpa [BodyFamily.containedIndices] using hi
    have h3 : (F.body i).carrier ⊆ K' := subset_trans h2 h
    simpa [BodyFamily.containedIndices] using h3
  exact Finset.sum_le_sum_of_subset_of_nonneg h1 (fun i _ _ => by positivity)

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

/-- Cardinality of one parent fiber. -/
def fiberCount {fine coarse : BodyFamily} (P : Factoring fine coarse)
    (j : Fin coarse.card) : ENNReal :=
  (P.fiberIndices j).card

/-- Cardinalities of all fibers of a factoring are `C`-uniform. -/
def FibersAreCUniform {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (C : ENNReal) : Prop :=
  1 ≤ C ∧
    ∀ first second,
      P.fiberCount first ≤ C * P.fiberCount second

/-- Surjectivity makes every factoring fiber nonempty. -/
lemma one_le_fiberCount {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (j : Fin coarse.card) :
    1 ≤ P.fiberCount j := by
  rcases P.parent_surjective j with ⟨i, hi⟩
  unfold fiberCount fiberIndices
  exact_mod_cast
    (Finset.one_le_card.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩)

/-- A factoring fiber has at most the ambient fine cardinality. -/
lemma fiberCount_le_enncard {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (j : Fin coarse.card) :
    P.fiberCount j ≤ fine.enncard := by
  have hcard : (P.fiberIndices j).card ≤ fine.card := by
    simpa using
      (Finset.card_le_card
        (Finset.subset_univ (P.fiberIndices j)))
  unfold fiberCount BodyFamily.enncard
  exact_mod_cast hcard

/--
Every factoring is crudely fiber-uniform once the comparison constant
dominates the ambient fine cardinality.
-/
lemma fibersAreCUniform_of_enncard_le
    {fine coarse : BodyFamily} (P : Factoring fine coarse) {C : ENNReal}
    (hC : 1 ≤ C) (hcard : fine.enncard ≤ C) :
    P.FibersAreCUniform C := by
  refine ⟨hC, ?_⟩
  intro first second
  calc
    P.fiberCount first ≤ fine.enncard :=
      P.fiberCount_le_enncard first
    _ ≤ C := hcard
    _ ≤ C * P.fiberCount second := by
      simpa using mul_le_mul_right (P.one_le_fiberCount second) C

/-- The parent fibers partition all fine indices. -/
lemma sum_fiberCount {fine coarse : BodyFamily}
    (P : Factoring fine coarse) :
    ∑ j : Fin coarse.card, P.fiberCount j = fine.enncard := by
  classical
  have hsum :
      ∑ j : Fin coarse.card,
          ((Finset.univ.filter fun i : Fin fine.card =>
            P.parent i = j).card : ℕ) =
        fine.card := by
    calc
      ∑ j : Fin coarse.card,
          (Finset.univ.filter fun i : Fin fine.card =>
            P.parent i = j).card
          = (Finset.univ : Finset (Fin fine.card)).card := by
        symm
        exact Finset.card_eq_sum_card_fiberwise
          (fun i _ => Finset.mem_univ (P.parent i))
      _ = fine.card := by simp
  change
    ∑ j : Fin coarse.card,
        ((Finset.univ.filter fun i : Fin fine.card =>
          P.parent i = j).card : ENNReal) =
      (fine.card : ENNReal)
  exact_mod_cast hsum

/-- Fine indices whose factoring parent lies in `I`. -/
def fiberIndicesOver {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (I : Finset (Fin coarse.card)) :
    Finset (Fin fine.card) := by
  classical
  exact Finset.univ.filter fun i => P.parent i ∈ I

@[simp]
lemma mem_fiberIndicesOver_iff {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (I : Finset (Fin coarse.card))
    (i : Fin fine.card) :
    i ∈ P.fiberIndicesOver I ↔ P.parent i ∈ I := by
  simp [fiberIndicesOver]

/-- A parent-set preimage is the disjoint union of its factoring fibers. -/
lemma fiberIndicesOver_card {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (I : Finset (Fin coarse.card)) :
    ((P.fiberIndicesOver I).card : ENNReal) =
      ∑ j ∈ I, P.fiberCount j := by
  classical
  have hnat :
      (P.fiberIndicesOver I).card =
        ∑ j ∈ I,
          (Finset.univ.filter fun i : Fin fine.card =>
            P.parent i = j).card := by
    have hmaps :
        Set.MapsTo P.parent
          (↑(P.fiberIndicesOver I) : Set (Fin fine.card))
          (↑I : Set (Fin coarse.card)) := by
      intro i hi
      exact (P.mem_fiberIndicesOver_iff I i).mp hi
    have h :=
      Finset.card_eq_sum_card_fiberwise
        (s := P.fiberIndicesOver I) (t := I) hmaps
    calc
      (P.fiberIndicesOver I).card
          = ∑ j ∈ I,
              ((P.fiberIndicesOver I).filter fun i =>
                P.parent i = j).card := h
      _ = ∑ j ∈ I,
            (Finset.univ.filter fun i : Fin fine.card =>
              P.parent i = j).card := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        ext i
        constructor
        · intro hi
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
        · intro hi
          have hparent : P.parent i ∈ I := by
            rw [(Finset.mem_filter.mp hi).2]
            exact hj
          exact Finset.mem_filter.mpr
            ⟨(P.mem_fiberIndicesOver_iff I i).mpr hparent,
              (Finset.mem_filter.mp hi).2⟩
  change ((P.fiberIndicesOver I).card : ENNReal) =
    ∑ j ∈ I,
      ((Finset.univ.filter fun i : Fin fine.card =>
        P.parent i = j).card : ENNReal)
  exact_mod_cast hnat

/--
Fiber uniformity gives the exact counting inequality for a parent-set
preimage.
-/
lemma parentCard_mul_fineCard_le_uniformity_mul_coarseCard_mul_overCard
    {fine coarse : BodyFamily}
    (P : Factoring fine coarse) {C : ENNReal}
    (huniform : P.FibersAreCUniform C)
    (I : Finset (Fin coarse.card)) :
    (I.card : ENNReal) * fine.enncard ≤
      C * (coarse.card : ENNReal) *
        (P.fiberIndicesOver I).card := by
  rw [← P.sum_fiberCount, P.fiberIndicesOver_card I]
  calc
    (I.card : ENNReal) *
          (∑ k : Fin coarse.card, P.fiberCount k)
        = ∑ k : Fin coarse.card,
            (I.card : ENNReal) * P.fiberCount k := by
      rw [Finset.mul_sum]
    _ = ∑ k : Fin coarse.card,
          ∑ _j ∈ I, P.fiberCount k := by
      apply Finset.sum_congr rfl
      intro k _
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ _k : Fin coarse.card,
          ∑ j ∈ I, C * P.fiberCount j := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro j _
      exact huniform.2 k j
    _ = C * (coarse.card : ENNReal) *
          (∑ j ∈ I, P.fiberCount j) := by
      simp [Finset.sum_const, Finset.mul_sum, nsmul_eq_mul]
      ring

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

/-- Fine indices geometrically contained in one coarse tube. -/
def containedIndices {δ ρ : ℝ}
    (fine : TubeFamily δ) (coarse : TubeFamily ρ)
    (j : Fin coarse.card) : Finset (Fin fine.card) :=
  fine.toBodyFamily.containedIndices (coarse.tube j).carrier

@[simp]
lemma mem_containedIndices_iff {δ ρ : ℝ}
    {fine : TubeFamily δ} {coarse : TubeFamily ρ}
    {j : Fin coarse.card} {i : Fin fine.card} :
    i ∈ fine.containedIndices coarse j ↔
      (fine.tube i).carrier ⊆ (coarse.tube j).carrier := by
  exact BodyFamily.mem_containedIndices_iff

/-- The complete geometric containment fiber over one coarse tube. -/
def containedFamily {δ ρ : ℝ}
    (fine : TubeFamily δ) (coarse : TubeFamily ρ)
    (j : Fin coarse.card) : TubeFamily δ where
  card := (fine.containedIndices coarse j).card
  tube i := fine.tube ((fine.containedIndices coarse j).orderEmbOfFin rfl i)

/-- Cardinality of one complete geometric containment fiber. -/
def containedCount {δ ρ : ℝ}
    (fine : TubeFamily δ) (coarse : TubeFamily ρ)
    (j : Fin coarse.card) : ENNReal :=
  (fine.containedIndices coarse j).card

/-- Complete geometric containment fibers have comparable cardinalities. -/
def FibersAreCUniform {δ ρ : ℝ}
    (fine : TubeFamily δ) (coarse : TubeFamily ρ)
    (C : ENNReal) : Prop :=
  1 ≤ C ∧
    ∀ first second,
      fine.containedCount coarse first ≤
        C * fine.containedCount coarse second

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

/--
Regard a tube cover as a factoring of indexed body families.

This conversion is the only entry point from tube-cover parent data to
partition bookkeeping.  Paper-facing full-containment fibers do not use it.
-/
def toFactoring {δ ρ : ℝ} {fine : TubeFamily δ} {coarse : TubeFamily ρ}
    (P : TubeCover fine coarse) :
    Factoring fine.toBodyFamily coarse.toBodyFamily where
  parent := P.parent
  parent_surjective := P.parent_surjective
  contained := P.nested

lemma toFactoring_parent {δ ρ : ℝ}
    {fine : TubeFamily δ} {coarse : TubeFamily ρ}
    (P : TubeCover fine coarse) (i : Fin fine.card) :
    P.toFactoring.parent i = P.parent i :=
  rfl

/-- Compatibility name for the cardinality of an assigned parent-map fiber. -/
def fiberCount {δ ρ : ℝ}
    {fine : TubeFamily δ} {coarse : TubeFamily ρ}
    (P : TubeCover fine coarse) (j : Fin coarse.card) : ENNReal := by
  classical
  exact
    ((Finset.univ.filter fun i : Fin fine.card =>
      P.parent i = j).card : ENNReal)

/-- The compatibility count is the canonical assigned factoring count. -/
lemma toFactoring_fiberCount {δ ρ : ℝ}
    {fine : TubeFamily δ} {coarse : TubeFamily ρ}
    (P : TubeCover fine coarse) (j : Fin coarse.card) :
    P.toFactoring.fiberCount j = P.fiberCount j :=
  rfl

/-- Compose a fine-to-middle tube cover with a middle-to-coarse cover. -/
def comp {δ ρ σ : ℝ}
    {fine : TubeFamily δ} {middle : TubeFamily ρ} {coarse : TubeFamily σ}
    (inner : TubeCover fine middle) (outer : TubeCover middle coarse) :
    TubeCover fine coarse where
  parent i := outer.parent (inner.parent i)
  parent_surjective := outer.parent_surjective.comp inner.parent_surjective
  nested i := (inner.nested i).trans (outer.nested (inner.parent i))

@[simp] lemma comp_parent {δ ρ σ : ℝ}
    {fine : TubeFamily δ} {middle : TubeFamily ρ} {coarse : TubeFamily σ}
    (inner : TubeCover fine middle) (outer : TubeCover middle coarse)
    (i : Fin fine.card) :
    (inner.comp outer).parent i = outer.parent (inner.parent i) := rfl

/--
The factoring fiber of a composed cover is the union of the inner factoring
fibers over the corresponding outer factoring fiber.
-/
lemma comp_factoringFiberIndices {δ ρ σ : ℝ}
    {fine : TubeFamily δ} {middle : TubeFamily ρ} {coarse : TubeFamily σ}
    (inner : TubeCover fine middle) (outer : TubeCover middle coarse)
    (k : Fin coarse.card) :
    (inner.comp outer).toFactoring.fiberIndices k =
      Finset.univ.filter fun i : Fin fine.card =>
        inner.parent i ∈ outer.toFactoring.fiberIndices k := by
  change
    (Finset.univ.filter fun i : Fin fine.card =>
      outer.parent (inner.parent i) = k) =
      Finset.univ.filter fun i : Fin fine.card =>
        inner.parent i ∈
          (Finset.univ.filter fun j : Fin middle.card =>
            outer.parent j = k)
  ext i
  simp

/-- Every factored child belongs to the complete geometric containment fiber
over the same parent. -/
lemma factoringFiberIndices_subset_containedIndices
    {δ ρ : ℝ} {fine : TubeFamily δ} {coarse : TubeFamily ρ}
    (P : TubeCover fine coarse) (j : Fin coarse.card) :
    P.toFactoring.fiberIndices j ⊆ fine.containedIndices coarse j := by
  change
    (Finset.univ.filter fun i : Fin fine.card => P.parent i = j) ⊆
      fine.containedIndices coarse j
  intro index hindex
  have hparent :
      P.parent index = j :=
    (Finset.mem_filter.mp hindex).2
  rw [TubeFamily.mem_containedIndices_iff]
  have hnested := P.nested index
  rwa [hparent] at hnested

/-- Factoring-fiber cardinality is bounded by complete containment-fiber
cardinality. -/
lemma factoringFiberCount_le_containedCount
    {δ ρ : ℝ} {fine : TubeFamily δ} {coarse : TubeFamily ρ}
    (P : TubeCover fine coarse) (j : Fin coarse.card) :
    P.toFactoring.fiberCount j ≤ fine.containedCount coarse j := by
  change
    ((Finset.univ.filter fun i : Fin fine.card =>
      P.parent i = j).card : ENNReal) ≤
      ((fine.containedIndices coarse j).card : ENNReal)
  exact_mod_cast
    Finset.card_le_card
      (P.factoringFiberIndices_subset_containedIndices j)

/--
Every surjective parent map is crudely assigned-uniform once the comparison
constant dominates the total fine-family cardinality.
-/
lemma factoringFibersAreCUniform_of_enncard_le
    {δ ρ : ℝ} {fine : TubeFamily δ} {coarse : TubeFamily ρ}
    (P : TubeCover fine coarse) {C : ENNReal}
    (hC : 1 ≤ C) (hcard : fine.enncard ≤ C) :
    P.toFactoring.FibersAreCUniform C :=
  P.toFactoring.fibersAreCUniform_of_enncard_le hC hcard

/-- Complete geometric containment fibers have comparable cardinalities. -/
def IsCUniform {δ ρ : ℝ} {fine : TubeFamily δ} {coarse : TubeFamily ρ}
    (_P : TubeCover fine coarse) (C : ENNReal) : Prop :=
  fine.FibersAreCUniform coarse C

/--
Every strict surjective cover is crudely full-fiber uniform once the constant
dominates the total fine-family cardinality.
-/
lemma isCUniform_of_enncard_le
    {δ ρ : ℝ} {fine : TubeFamily δ} {coarse : TubeFamily ρ}
    (P : TubeCover fine coarse) {C : ENNReal}
    (hC : 1 ≤ C) (hcard : fine.enncard ≤ C) :
    P.IsCUniform C := by
  classical
  refine ⟨hC, ?_⟩
  intro first second
  have hFirstNat :
      (fine.containedIndices coarse first).card ≤ fine.card := by
    simpa using
      (Finset.card_le_card
        (Finset.subset_univ
          (fine.containedIndices coarse first)))
  have hFirst :
      fine.containedCount coarse first ≤ fine.enncard := by
    unfold TubeFamily.containedCount TubeFamily.enncard
    exact_mod_cast hFirstNat
  have hSecond :
      (1 : ENNReal) ≤ fine.containedCount coarse second := by
    rcases P.parent_surjective second with ⟨index, hindex⟩
    have hmem :
        index ∈ fine.containedIndices coarse second := by
      rw [TubeFamily.mem_containedIndices_iff]
      have hnested := P.nested index
      rwa [hindex] at hnested
    unfold TubeFamily.containedCount
    exact_mod_cast (Finset.card_pos.mpr ⟨index, hmem⟩)
  calc
    fine.containedCount coarse first ≤ fine.enncard := hFirst
    _ ≤ C := hcard
    _ ≤ C * fine.containedCount coarse second := by
      simpa using mul_le_mul_right hSecond C

end TubeCover

end Kakeya.Streamlined
