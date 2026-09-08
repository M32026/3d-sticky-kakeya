import MyLeanRepo.Kakeya.Integration.CompetitorModelBridge
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.SelfDilatedContainment
import MyLeanRepo.Kakeya.Streamlined.DividingScales.FullFiberRestriction

/-!
# The competitor hierarchy as one immutable WZ2 input

This file starts the hierarchy part of the competitor/WZ2 adapter.  The
source finset, shading, shaded-uniform hierarchy, and all quantitative
witnesses are stored together.  Every projected grid level below is defined
from that one stored hierarchy; no cover or assignment is reconstructed.

At a grid level we discard unused node indices by taking the image of the
stored assignment.  This makes the induced parent map surjective while
retaining an exact equation back to the original competitor index.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Integration

/-- Indices whose convex bodies are contained in an arbitrary set. -/
def convexBodyFamilyInSet
    {indexType : Type*} (s : Finset indexType)
    (W : indexType → ConvexSpaceBody Space3) (test : Set Space3) :
    Finset indexType := by
  classical
  exact s.filter fun index => (W index).carrier ⊆ test

@[simp] theorem mem_convexBodyFamilyInSet
    {indexType : Type*} (s : Finset indexType)
    (W : indexType → ConvexSpaceBody Space3) (test : Set Space3)
    (index : indexType) :
    index ∈ convexBodyFamilyInSet s W test ↔
      index ∈ s ∧ (W index).carrier ⊆ test := by
  classical
  simp [convexBodyFamilyInSet]

/-- Competitor `IsFrostmanIn`, whose tests are compact convex bodies, gives
the division-free product inequality on every convex set.  For a test set
`test`, take the convex hull of the finitely many family members contained in
`test`; this hull is a legal compact test body and is still contained in
`test`. -/
theorem convexBodyFrostman_product_on_convexSet
    {indexType : Type*} {s : Finset indexType}
    {W : indexType → ConvexSpaceBody Space3}
    {container : ConvexSpaceBody Space3} {frostman : ENNReal}
    (hFrostman : ConvexSpaceBody.IsFrostmanIn s W container frostman)
    (hContained : ∀ index ∈ s, W index ≤ container)
    (test : Set Space3) (hTestConvex : Convex ℝ test)
    (_hTestContainer : test ⊆ container.carrier) :
    (∑ index ∈ convexBodyFamilyInSet s W test,
        volume (W index).carrier) * volume container.carrier ≤
      frostman * (∑ index ∈ s, volume (W index).carrier) *
        volume test := by
  classical
  let captured : Finset indexType :=
    convexBodyFamilyInSet s W test
  by_cases hCaptured : captured = ∅
  · simp [captured, hCaptured]
  · have hCapturedNonempty : captured.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hCaptured
    let hull : ConvexSpaceBody Space3 :=
      captured.convexHull_biUnion W
    have hHullTest : hull.carrier ⊆ test := by
      apply (hCapturedNonempty.convexHull_biUnion_subset_iff W
        hTestConvex.isConvexSet).mpr
      intro index hindex
      exact (Finset.mem_filter.mp hindex).2
    have hHullContainer : hull ≤ container := by
      apply (hCapturedNonempty.convexHull_biUnion_le_iff W container).mpr
      intro index hindex
      exact hContained index (Finset.mem_filter.mp hindex).1
    have hFamilyInHull : Kakeya.familyIn s W hull = captured := by
      ext index
      constructor
      · intro hindex
        have hs : index ∈ s := (Finset.mem_filter.mp hindex).1
        have hbody : (W index).carrier ⊆ hull.carrier :=
          (Finset.mem_filter.mp hindex).2
        exact Finset.mem_filter.mpr
          ⟨hs, hbody.trans hHullTest⟩
      · intro hindex
        have hs : index ∈ s := (Finset.mem_filter.mp hindex).1
        have hHull : W index ≤ hull :=
          Finset.le_convexHull_biUnion W hindex
        exact Finset.mem_filter.mpr ⟨hs, hHull⟩
    have hCapturedMass :
        (∑ index ∈ captured, volume (W index).carrier) =
          Kakeya.densityIn s W hull * volume hull.carrier := by
      rw [← hFamilyInHull]
      exact Kakeya.sum_volume_eq_densityIn_mul_volume s W hull
    have hContainerMass :
        (∑ index ∈ s, volume (W index).carrier) =
          Kakeya.densityIn s W container * volume container.carrier :=
      Kakeya.sum_volume_eq_densityIn_mul_volume' hContained
    have hDensity := hFrostman hull hHullContainer
    change
      (∑ index ∈ captured, volume (W index).carrier) *
          volume container.carrier ≤
        frostman * (∑ index ∈ s, volume (W index).carrier) *
          volume test
    calc
      (∑ index ∈ captured, volume (W index).carrier) *
          volume container.carrier =
        (Kakeya.densityIn s W hull * volume hull.carrier) *
          volume container.carrier := by rw [hCapturedMass]
      _ ≤ (frostman * Kakeya.densityIn s W container *
          volume hull.carrier) * volume container.carrier := by
        gcongr
      _ = frostman *
          (Kakeya.densityIn s W container * volume container.carrier) *
            volume hull.carrier := by ring
      _ = frostman * (∑ index ∈ s, volume (W index).carrier) *
          volume hull.carrier := by rw [hContainerMass]
      _ ≤ frostman * (∑ index ∈ s, volume (W index).carrier) *
          volume test := by
        gcongr

/-- Contained mass of the canonical WZ2 enumeration is the corresponding
competitor source-index sum. -/
theorem competitorTubeFamily_containedMass
    {delta : NNReal} {indexType : Type*}
    (s : Finset indexType) (V : indexType → ShadedTube delta Space3)
    (test : Set Space3) :
    (competitorTubeFamily s V).toBodyFamily.containedMass test =
      ∑ sourceIndex ∈ convexBodyFamilyInSet s
          (fun index => (V index).toConvexSpaceBody) test,
        volume (V sourceIndex).carrier := by
  classical
  let selected : Finset (Fin s.card) :=
    (competitorTubeFamily s V).indicesIn test
  have hinjective : Set.InjOn
      (fun index : Fin s.card => competitorIndex s index)
      (selected : Set (Fin s.card)) :=
    fun first _ second _ heq => by
      apply (competitorIndexEquiv s).injective
      exact Subtype.ext heq
  have himage :
      Finset.image (fun index : Fin s.card => competitorIndex s index) selected =
        convexBodyFamilyInSet s
          (fun index => (V index).toConvexSpaceBody) test := by
    ext sourceIndex
    constructor
    · intro hsource
      rcases Finset.mem_image.mp hsource with ⟨index, hindex, rfl⟩
      apply (mem_convexBodyFamilyInSet _ _ _ _).mpr
      refine ⟨competitorIndex_mem s index, ?_⟩
      have hcontained :=
        ((competitorTubeFamily s V).mem_indicesIn_iff test index).mp hindex
      simpa [competitorTubeFamily_carrier] using hcontained
    · intro hsource
      have hdata := (mem_convexBodyFamilyInSet _ _ _ sourceIndex).mp hsource
      let index : Fin s.card := s.equivFin ⟨sourceIndex, hdata.1⟩
      have hindexSource : competitorIndex s index = sourceIndex := by
        simp [index, competitorIndex, competitorIndexEquiv]
      refine Finset.mem_image.mpr ⟨index, ?_, hindexSource⟩
      apply ((competitorTubeFamily s V).mem_indicesIn_iff test index).mpr
      simpa [competitorTubeFamily_carrier, hindexSource] using hdata.2
  change
    (∑ index ∈ selected,
      ((competitorTubeFamily s V).toBodyFamily.body index).volume) = _
  calc
    (∑ index ∈ selected,
        ((competitorTubeFamily s V).toBodyFamily.body index).volume) =
      ∑ index ∈ selected, volume (V (competitorIndex s index)).carrier := by
        apply Finset.sum_congr rfl
        intro index _
        simp [Kakeya.Streamlined.TubeFamily.toBodyFamily,
          Kakeya.Streamlined.tubeBody, Kakeya.Streamlined.Body.volume]
    _ = ∑ sourceIndex ∈
          Finset.image (fun index : Fin s.card => competitorIndex s index) selected,
          volume (V sourceIndex).carrier :=
      (Finset.sum_image
        (f := fun sourceIndex : indexType => volume (V sourceIndex).carrier)
        (g := fun index : Fin s.card => competitorIndex s index)
        (s := selected) hinjective).symm
    _ = _ := by rw [himage]

/-- One fixed competitor Sticky input, with every later projection tied to the
same shaded-uniform hierarchy. -/
structure CompetitorStickyInput
    (delta : NNReal) (ι : Type*) (N : ℕ) (C : NNReal)
    (lambda frostmanConstant : ENNReal) (supportRadius : ℝ) where
  s : Finset ι
  V : ι → ShadedTube delta Space3
  shadedUniform : ShadedTube.ShadedUniformTubeSet s V N C
  uniformConstant_le : C ≤ ShadedTube.ssfUniformConst 3
  fullness :
    lambda ≤ ShadedBody.fullness' s (fun i => (V i).toShadedBody)
  support :
    ∀ i ∈ s, (V i).carrier ⊆
      Metric.closedBall (0 : Space3) supportRadius
  leaf_separation :
    (s : Set ι).Pairwise (fun i j =>
      _root_.IsEssentiallyDistinct (V i).carrier (V j).carrier)
  node_frostman :
    shadedUniform.tubeUniform.IsFrostmanAtEveryScale frostmanConstant

namespace CompetitorStickyInput

variable {delta : NNReal} {ι : Type*} {N : ℕ} {C : NNReal}
  {lambda frostmanConstant : ENNReal} {supportRadius : ℝ}

local instance : DecidableEq ι := Classical.decEq ι

/-- The unique underlying competitor tube hierarchy stored in the input. -/
abbrev tubeUniform
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius) :=
  input.shadedUniform.tubeUniform

/-- The exact WZ2-indexed source family of the stored competitor leaves. -/
def source
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius) :
    Kakeya.Streamlined.TubeFamily (delta : ℝ) :=
  competitorTubeFamily input.s input.V

/-- The exact WZ2 shading on `source`. -/
def sourceShading
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius) :
    Kakeya.Streamlined.TubeShading input.source :=
  competitorTubeShading input.s input.V

/-- The occupied nodes at level `k`.  Taking the assignment image removes
every unused node and is what makes the projected parent map surjective. -/
def occupiedNodes
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (k : ℕ) : Finset ι := by
  classical
  exact input.s.image (input.tubeUniform.cover.assign k)

theorem occupiedNodes_subset_indexSet
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N) :
    input.occupiedNodes k ⊆ input.tubeUniform.cover.indexSet k := by
  classical
  intro node hnode
  rcases Finset.mem_image.mp hnode with ⟨index, hindex, rfl⟩
  exact input.tubeUniform.cover.assign_mem k hk index hindex

/-- The occupied competitor nodes, losslessly converted into the WZ2 tube
presentation at the exact grid radius. -/
def levelCoarse
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (k : ℕ) :
    Kakeya.Streamlined.TubeFamily (Tube.gridScale delta N k : ℝ) :=
  competitorPlainTubeFamily (input.occupiedNodes k)
    (input.tubeUniform.cover.tube k)

/-- The original competitor node assigned to one WZ2 source index, bundled
with its proof of occupancy. -/
def occupiedNodeOfSourceIndex
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (k : ℕ) (index : Fin input.source.card) : input.occupiedNodes k := by
  classical
  refine ⟨input.tubeUniform.cover.assign k
      (competitorIndex input.s index), ?_⟩
  exact Finset.mem_image.mpr
    ⟨competitorIndex input.s index, competitorIndex_mem input.s index, rfl⟩

/-- Parent assignment from the exact WZ2 source enumeration to the occupied
node enumeration. -/
def levelParent
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (k : ℕ) : Fin input.source.card → Fin (input.levelCoarse k).card :=
  fun index =>
    (input.occupiedNodes k).equivFin
      (input.occupiedNodeOfSourceIndex k index)

/-- Exact occurrence-level provenance of the projected parent assignment. -/
@[simp] theorem competitorIndex_levelParent
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (k : ℕ) (index : Fin input.source.card) :
    competitorIndex (input.occupiedNodes k) (input.levelParent k index) =
      input.tubeUniform.cover.assign k
        (competitorIndex input.s index) := by
  simp [levelParent, occupiedNodeOfSourceIndex, competitorIndex,
    competitorIndexEquiv]

theorem levelParent_surjective
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (k : ℕ) : Function.Surjective (input.levelParent k) := by
  classical
  intro parent
  have hparent : competitorIndex (input.occupiedNodes k) parent ∈
      input.occupiedNodes k :=
    competitorIndex_mem (input.occupiedNodes k) parent
  rcases Finset.mem_image.mp hparent with ⟨sourceIndex, hsource, hassigned⟩
  let sourceFin : Fin input.source.card := ⟨
    (input.s.equivFin ⟨sourceIndex, hsource⟩).val,
    by
      simpa [source] using
        (input.s.equivFin ⟨sourceIndex, hsource⟩).isLt⟩
  have hsourceFin : competitorIndex input.s sourceFin = sourceIndex := by
    simp [sourceFin, source, competitorIndex, competitorIndexEquiv]
  refine ⟨sourceFin, ?_⟩
  apply (competitorIndexEquiv (input.occupiedNodes k)).injective
  apply Subtype.ext
  have hprojected := input.competitorIndex_levelParent k sourceFin
  have hassigned' :
      input.tubeUniform.cover.assign k
          (competitorIndex input.s sourceFin) =
        competitorIndex (input.occupiedNodes k) parent := by
    rw [hsourceFin]
    exact hassigned
  simpa only [competitorIndex] using hprojected.trans hassigned'

/-- The fine carrier is contained in its assigned occupied node before any
WZ2 dilation is applied. -/
theorem source_carrier_subset_assigned_node
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N) (index : Fin input.source.card) :
    (input.source.tube index).carrier ⊆
      ((input.levelCoarse k).tube (input.levelParent k index)).carrier := by
  have hassigned :=
    input.tubeUniform.cover.le_tube_assign k hk
      (competitorIndex input.s index)
      (competitorIndex_mem input.s index)
  change
    (input.V (competitorIndex input.s index)).carrier ⊆
      (input.tubeUniform.cover.tube k
        (input.tubeUniform.cover.assign k
          (competitorIndex input.s index))).carrier at hassigned
  simpa [source, levelCoarse] using hassigned

/-- The occupied-node projection as a genuine surjective WZ2 dilated cover.
The only enlargement is the explicit centered factor `A`; the parent and
coarse tube still come from the stored competitor hierarchy. -/
def levelCover
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (A : ℝ) (hA : 1 ≤ A) {k : ℕ} (hk : k ≤ N) :
    Kakeya.Streamlined.DilatedTubeCover A input.source
      (input.levelCoarse k) where
  parent := input.levelParent k
  parent_surjective := input.levelParent_surjective k
  nested index :=
    (input.source_carrier_subset_assigned_node hk index).trans
      (Kakeya.Streamlined.GeometricLemmas.self_dilated_containment
        A hA ((input.levelCoarse k).tube (input.levelParent k index)))

/-- The undilated occupied-node cover consumed by the finite-grid to
all-real balanced-cover constructor. -/
def levelStrictCover
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N) :
    Kakeya.Streamlined.TubeCover input.source (input.levelCoarse k) where
  parent := input.levelParent k
  parent_surjective := input.levelParent_surjective k
  nested := input.source_carrier_subset_assigned_node hk

/-- Occupied parents at level `k` that meet an arbitrary same-scale test tube
through a common source leaf.  This is the exact WZ2-indexed reading of the
competitor hierarchy's bounded-overlap relation; it does not assert pairwise
essential distinctness of the parents. -/
def levelLeafMediatedMeetingParents
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (k : ℕ)
    (test : Kakeya.DeltaTube (Tube.gridScale delta N k : ℝ)) :
    Finset (Fin (input.levelCoarse k).card) := by
  classical
  exact Finset.univ.filter fun parent =>
    ∃ index : Fin input.source.card,
      (input.source.tube index).carrier ⊆
          ((input.levelCoarse k).tube parent).carrier ∧
        (input.source.tube index).carrier ⊆ test.carrier

/-- The stored competitor bounded-overlap certificate, transported without
loss to the occupied WZ2 parent family.  The overlap is deliberately mediated
by one common source leaf, exactly as in `Tube.UniformTubeSet.boundedOverlap`;
it is weaker than pairwise essential distinctness and remains valid for
longitudinal parent stacks. -/
theorem levelLeafMediatedMeetingParents_card_le
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N)
    (test : Kakeya.DeltaTube (Tube.gridScale delta N k : ℝ)) :
    ((input.levelLeafMediatedMeetingParents k test).card : ENNReal) ≤
      (C : ENNReal) := by
  classical
  let competitorTest : Tube (Tube.gridScale delta N k) Space3 :=
    deltaTubeToCompetitorTube test
  let meetingNodes : Finset ι :=
    (input.tubeUniform.cover.indexSet k).filter fun node =>
      ∃ sourceIndex ∈ input.s,
        (input.V sourceIndex).toConvexSpaceBody ≤
            (input.tubeUniform.cover.tube k node).toConvexSpaceBody ∧
          (input.V sourceIndex).toConvexSpaceBody ≤
            competitorTest.toConvexSpaceBody
  have himageSubset :
      Finset.image (competitorIndex (input.occupiedNodes k))
          (input.levelLeafMediatedMeetingParents k test) ⊆
        meetingNodes := by
    intro node hnode
    rcases Finset.mem_image.mp hnode with
      ⟨parent, hparent, rfl⟩
    rcases Finset.mem_filter.mp hparent with
      ⟨_hparentUniv, index, hsourceParent, hsourceTest⟩
    apply Finset.mem_filter.mpr
    refine
      ⟨input.occupiedNodes_subset_indexSet hk
          (competitorIndex_mem (input.occupiedNodes k) parent),
        competitorIndex input.s index, competitorIndex_mem input.s index, ?_, ?_⟩
    · change
        (input.V (competitorIndex input.s index)).carrier ⊆
          (input.tubeUniform.cover.tube k
            (competitorIndex (input.occupiedNodes k) parent)).carrier
      simpa [source, levelCoarse] using hsourceParent
    · change
        (input.V (competitorIndex input.s index)).carrier ⊆
          competitorTest.carrier
      simpa [source, competitorTest] using hsourceTest
  have himageCard :
      (Finset.image (competitorIndex (input.occupiedNodes k))
          (input.levelLeafMediatedMeetingParents k test)).card =
        (input.levelLeafMediatedMeetingParents k test).card := by
    apply Finset.card_image_of_injective
    intro first second heq
    apply (competitorIndexEquiv (input.occupiedNodes k)).injective
    exact Subtype.ext heq
  have hcardNat :
      (input.levelLeafMediatedMeetingParents k test).card ≤
        meetingNodes.card := by
    rw [← himageCard]
    exact Finset.card_le_card himageSubset
  have hbounded : (meetingNodes.card : NNReal) ≤ C := by
    simpa [meetingNodes, competitorTest] using
      input.tubeUniform.boundedOverlap k hk competitorTest
  calc
    ((input.levelLeafMediatedMeetingParents k test).card : ENNReal) ≤
        (meetingNodes.card : ENNReal) := by exact_mod_cast hcardNat
    _ ≤ (C : ENNReal) := by exact_mod_cast hbounded

/-- A source index belongs to the strict assigned fiber exactly when its
competitor source index belongs to the original assigned class. -/
theorem mem_levelStrictCover_fiberIndices_iff
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N) (parent : Fin (input.levelCoarse k).card)
    (index : Fin input.source.card) :
    index ∈ (input.levelStrictCover hk).toFactoring.fiberIndices parent ↔
      competitorIndex input.s index ∈
        Tube.coverClass input.s (input.tubeUniform.cover.assign k)
          (competitorIndex (input.occupiedNodes k) parent) := by
  constructor
  · intro hindex
    have hparent : input.levelParent k index = parent :=
      (Finset.mem_filter.mp hindex).2
    apply Finset.mem_filter.mpr
    refine ⟨competitorIndex_mem input.s index, ?_⟩
    rw [← input.competitorIndex_levelParent k index, hparent]
  · intro hclass
    have hsource := (Finset.mem_filter.mp hclass).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ index, ?_⟩
    apply (competitorIndexEquiv (input.occupiedNodes k)).injective
    apply Subtype.ext
    exact (input.competitorIndex_levelParent k index).trans hsource

/-- Exact occurrence-level image of one strict assigned fiber. -/
theorem image_levelStrictCover_fiberIndices
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N) (parent : Fin (input.levelCoarse k).card) :
    Finset.image (competitorIndex input.s)
        ((input.levelStrictCover hk).toFactoring.fiberIndices parent) =
      Tube.coverClass input.s (input.tubeUniform.cover.assign k)
        (competitorIndex (input.occupiedNodes k) parent) := by
  ext sourceIndex
  constructor
  · intro hsource
    rcases Finset.mem_image.mp hsource with ⟨index, hindex, rfl⟩
    exact (input.mem_levelStrictCover_fiberIndices_iff hk parent index).mp hindex
  · intro hsource
    have hsourceMem : sourceIndex ∈ input.s :=
      (Finset.mem_filter.mp hsource).1
    let index : Fin input.source.card := ⟨
      (input.s.equivFin ⟨sourceIndex, hsourceMem⟩).val,
      by
        simpa [source] using
          (input.s.equivFin ⟨sourceIndex, hsourceMem⟩).isLt⟩
    have hindexSource : competitorIndex input.s index = sourceIndex := by
      simp [index, competitorIndex, competitorIndexEquiv]
    refine Finset.mem_image.mpr ⟨index, ?_, hindexSource⟩
    apply (input.mem_levelStrictCover_fiberIndices_iff hk parent index).mpr
    rwa [hindexSource]

/-- Strict assigned fibers have exactly the original class cardinalities. -/
theorem levelStrictCover_fiberCount_eq_classCard
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N) (parent : Fin (input.levelCoarse k).card) :
    (input.levelStrictCover hk).toFactoring.fiberCount parent =
      ((Tube.coverClass input.s (input.tubeUniform.cover.assign k)
        (competitorIndex (input.occupiedNodes k) parent)).card : ENNReal) := by
  have hinjective : Function.Injective (competitorIndex input.s) := by
    intro first second heq
    apply (competitorIndexEquiv input.s).injective
    exact Subtype.ext heq
  change
    (((input.levelStrictCover hk).toFactoring.fiberIndices parent).card :
        ENNReal) = _
  exact_mod_cast
    ((Finset.card_image_of_injective
      ((input.levelStrictCover hk).toFactoring.fiberIndices parent)
      hinjective).symm.trans
        (congrArg Finset.card
          (input.image_levelStrictCover_fiberIndices hk parent)))

/-- The original two-sided class bracket is exactly assigned-fiber
uniformity for the strict occupied cover. -/
theorem levelStrictCover_assignedUniform
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N) :
    (input.levelStrictCover hk).toFactoring.FibersAreCUniform
      (max 1 ((C : ENNReal) ^ 2)) := by
  refine ⟨le_max_left _ _, ?_⟩
  intro first second
  let firstNode := competitorIndex (input.occupiedNodes k) first
  let secondNode := competitorIndex (input.occupiedNodes k) second
  have hfirst : firstNode ∈ input.tubeUniform.cover.indexSet k :=
    input.occupiedNodes_subset_indexSet hk
      (competitorIndex_mem (input.occupiedNodes k) first)
  have hsecond : secondNode ∈ input.tubeUniform.cover.indexSet k :=
    input.occupiedNodes_subset_indexSet hk
      (competitorIndex_mem (input.occupiedNodes k) second)
  have hupper := input.tubeUniform.card_class_le k hk firstNode hfirst
  have hlower := input.tubeUniform.le_card_class k hk secondNode hsecond
  rw [input.levelStrictCover_fiberCount_eq_classCard hk first,
    input.levelStrictCover_fiberCount_eq_classCard hk second]
  calc
    ((Tube.coverClass input.s (input.tubeUniform.cover.assign k)
          firstNode).card : ENNReal)
        ≤ (C : ENNReal) * input.tubeUniform.branchingN k := by
          exact_mod_cast hupper
    _ ≤ (C : ENNReal) *
          ((C : ENNReal) *
            ((Tube.coverClass input.s (input.tubeUniform.cover.assign k)
              secondNode).card : ENNReal)) := by
          gcongr
          exact_mod_cast hlower
    _ = (C : ENNReal) ^ 2 *
          ((Tube.coverClass input.s (input.tubeUniform.cover.assign k)
            secondNode).card : ENNReal) := by ring
    _ ≤ max 1 ((C : ENNReal) ^ 2) *
          ((Tube.coverClass input.s (input.tubeUniform.cover.assign k)
            secondNode).card : ENNReal) := by
          gcongr
          exact le_max_right _ _

/-- One strict assigned fiber, additionally filtered by containment in a
WZ2 test set. -/
def levelStrictCoverFiberInSet
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N) (parent : Fin (input.levelCoarse k).card)
    (test : Set Space3) : Finset (Fin input.source.card) := by
  classical
  exact (input.levelStrictCover hk).toFactoring.fiberIndices parent |>.filter
    fun index => (input.source.tube index).carrier ⊆ test

@[simp] theorem mem_levelStrictCoverFiberInSet
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N) (parent : Fin (input.levelCoarse k).card)
    (test : Set Space3) (index : Fin input.source.card) :
    index ∈ input.levelStrictCoverFiberInSet hk parent test ↔
      index ∈ (input.levelStrictCover hk).toFactoring.fiberIndices parent ∧
        (input.source.tube index).carrier ⊆ test := by
  classical
  change index ∈
      ((input.levelStrictCover hk).toFactoring.fiberIndices parent).filter
        (fun index => (input.source.tube index).carrier ⊆ test) ↔ _
  exact Finset.mem_filter

/-- Exact source-index image after additionally filtering one assigned fiber
by containment in an arbitrary test set. -/
theorem image_levelStrictCover_fiberContainedIndices
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N) (parent : Fin (input.levelCoarse k).card)
    (test : Set Space3) :
    Finset.image (fun index : Fin input.source.card => competitorIndex input.s index)
        (input.levelStrictCoverFiberInSet hk parent test) =
      convexBodyFamilyInSet
        (Tube.coverClass input.s (input.tubeUniform.cover.assign k)
          (competitorIndex (input.occupiedNodes k) parent))
        (fun sourceIndex => (input.V sourceIndex).toConvexSpaceBody) test := by
  ext sourceIndex
  constructor
  · intro hsource
    rcases Finset.mem_image.mp hsource with ⟨index, hindex, rfl⟩
    have hindexData :=
      (input.mem_levelStrictCoverFiberInSet hk parent test index).mp hindex
    apply (mem_convexBodyFamilyInSet _ _ _ _).mpr
    refine ⟨
      (input.mem_levelStrictCover_fiberIndices_iff hk parent index).mp
        hindexData.1, ?_⟩
    simpa [source] using hindexData.2
  · intro hsource
    have hsourceData :=
      (mem_convexBodyFamilyInSet _ _ _ sourceIndex).mp hsource
    have hsourceMem : sourceIndex ∈ input.s :=
      (Finset.mem_filter.mp hsourceData.1).1
    let index : Fin input.source.card := ⟨
      (input.s.equivFin ⟨sourceIndex, hsourceMem⟩).val,
      by
        simpa [source] using
          (input.s.equivFin ⟨sourceIndex, hsourceMem⟩).isLt⟩
    have hindexSource : competitorIndex input.s index = sourceIndex := by
      simp [index, competitorIndex, competitorIndexEquiv]
    refine Finset.mem_image.mpr ⟨index, ?_, hindexSource⟩
    apply (input.mem_levelStrictCoverFiberInSet hk parent test index).mpr
    refine ⟨
      (input.mem_levelStrictCover_fiberIndices_iff hk parent index).mpr
        (by simpa only [hindexSource] using hsourceData.1), ?_⟩
    simpa [source, hindexSource] using hsourceData.2

/-- Assigned-fiber contained mass is the original class sum on the exact same
source occurrences. -/
theorem levelStrictCover_fiberContainedMass
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N) (parent : Fin (input.levelCoarse k).card)
    (test : Set Space3) :
    (input.levelStrictCover hk).toFactoring.fiberContainedMass parent test =
      ∑ sourceIndex ∈ convexBodyFamilyInSet
          (Tube.coverClass input.s (input.tubeUniform.cover.assign k)
            (competitorIndex (input.occupiedNodes k) parent))
          (fun sourceIndex => (input.V sourceIndex).toConvexSpaceBody) test,
        volume (input.V sourceIndex).carrier := by
  let selected : Finset (Fin input.source.card) :=
    input.levelStrictCoverFiberInSet hk parent test
  have hinjective : Set.InjOn
      (fun index : Fin input.source.card => competitorIndex input.s index)
      (selected : Set (Fin input.source.card)) :=
    fun first _ second _ heq => by
      apply (competitorIndexEquiv input.s).injective
      exact Subtype.ext heq
  change
    (∑ index ∈ selected, (input.source.toBodyFamily.body index).volume) = _
  calc
    (∑ index ∈ selected, (input.source.toBodyFamily.body index).volume) =
        ∑ index ∈ selected,
          volume (input.V (competitorIndex input.s index)).carrier := by
      apply Finset.sum_congr rfl
      intro index _
      simp [source, Kakeya.Streamlined.TubeFamily.toBodyFamily,
        Kakeya.Streamlined.tubeBody, Kakeya.Streamlined.Body.volume]
    _ = ∑ sourceIndex ∈ Finset.image
          (fun index : Fin input.source.card => competitorIndex input.s index) selected,
          volume (input.V sourceIndex).carrier :=
      (Finset.sum_image
        (f := fun sourceIndex : ι => volume (input.V sourceIndex).carrier)
        (g := fun index : Fin input.source.card => competitorIndex input.s index)
        (s := selected) hinjective).symm
    _ = _ := by
      rw [show Finset.image
          (fun index : Fin input.source.card => competitorIndex input.s index) selected =
          convexBodyFamilyInSet
            (Tube.coverClass input.s (input.tubeUniform.cover.assign k)
              (competitorIndex (input.occupiedNodes k) parent))
            (fun sourceIndex => (input.V sourceIndex).toConvexSpaceBody) test by
        exact input.image_levelStrictCover_fiberContainedIndices hk parent test]

/-- Assigned-fiber total mass is the original class sum. -/
theorem levelStrictCover_fiberMass
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N) (parent : Fin (input.levelCoarse k).card) :
    (input.levelStrictCover hk).toFactoring.fiberMass parent =
      ∑ sourceIndex ∈
          Tube.coverClass input.s (input.tubeUniform.cover.assign k)
            (competitorIndex (input.occupiedNodes k) parent),
        volume (input.V sourceIndex).carrier := by
  let selected : Finset (Fin input.source.card) :=
    (input.levelStrictCover hk).toFactoring.fiberIndices parent
  have hinjective : Set.InjOn
      (fun index : Fin input.source.card => competitorIndex input.s index)
      (selected : Set (Fin input.source.card)) :=
    fun first _ second _ heq => by
      apply (competitorIndexEquiv input.s).injective
      exact Subtype.ext heq
  change
    (∑ index ∈ selected, (input.source.toBodyFamily.body index).volume) = _
  calc
    (∑ index ∈ selected, (input.source.toBodyFamily.body index).volume) =
        ∑ index ∈ selected,
          volume (input.V (competitorIndex input.s index)).carrier := by
      apply Finset.sum_congr rfl
      intro index _
      simp [source, Kakeya.Streamlined.TubeFamily.toBodyFamily,
        Kakeya.Streamlined.tubeBody, Kakeya.Streamlined.Body.volume]
    _ = ∑ sourceIndex ∈ Finset.image
          (fun index : Fin input.source.card => competitorIndex input.s index) selected,
          volume (input.V sourceIndex).carrier :=
      (Finset.sum_image
        (f := fun sourceIndex : ι => volume (input.V sourceIndex).carrier)
        (g := fun index : Fin input.source.card => competitorIndex input.s index)
        (s := selected) hinjective).symm
    _ = _ := by
      rw [show Finset.image
          (fun index : Fin input.source.card => competitorIndex input.s index) selected =
          Tube.coverClass input.s (input.tubeUniform.cover.assign k)
            (competitorIndex (input.occupiedNodes k) parent) by
        exact input.image_levelStrictCover_fiberIndices hk parent]

/-- The strict occupied cover carries exactly the competitor node-Frostman
witness, now in WZ2's division-free arbitrary-convex-set formulation. -/
theorem levelStrictCover_assignedFrostman
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N) :
    (input.levelStrictCover hk).AssignedFibersAreCFrostman
      frostmanConstant := by
  intro parent test hTestConvex hTestSubset
  let node := competitorIndex (input.occupiedNodes k) parent
  let cls :=
    Tube.coverClass input.s (input.tubeUniform.cover.assign k) node
  let W : ι → ConvexSpaceBody Space3 :=
    fun sourceIndex => (input.V sourceIndex).toConvexSpaceBody
  let container := (input.tubeUniform.cover.tube k node).toConvexSpaceBody
  have hnode : node ∈ input.tubeUniform.cover.indexSet k :=
    input.occupiedNodes_subset_indexSet hk
      (competitorIndex_mem (input.occupiedNodes k) parent)
  have hFrostman : ConvexSpaceBody.IsFrostmanIn cls W container
      frostmanConstant := by
    simpa [cls, W, container] using input.node_frostman k hk node hnode
  have hContained : ∀ sourceIndex ∈ cls, W sourceIndex ≤ container := by
    intro sourceIndex hsource
    have hsourceData := Finset.mem_filter.mp hsource
    have hle := input.tubeUniform.cover.le_tube_assign k hk sourceIndex
      hsourceData.1
    simpa [W, container, hsourceData.2] using hle
  have hProduct := convexBodyFrostman_product_on_convexSet
    hFrostman hContained test hTestConvex (by
      intro point hpoint
      have hpoint' := hTestSubset hpoint
      simpa [container, levelCoarse, node,
        Kakeya.Streamlined.TubeFamily.toBodyFamily,
        Kakeya.Streamlined.tubeBody] using hpoint')
  rw [input.levelStrictCover_fiberContainedMass hk parent test,
    input.levelStrictCover_fiberMass hk parent]
  simpa [cls, W, container, levelCoarse, node,
    Kakeya.Streamlined.TubeFamily.toBodyFamily,
    Kakeya.Streamlined.tubeBody, Kakeya.Streamlined.Body.volume] using hProduct

/-! ## Exact strict full fibers of the occupied level

These declarations deliberately use dilation `1`.  At that factor the WZ2
full-containment fiber is exactly the competitor `familyIn` of the same
stored node.  Larger dilations are a later geometric promotion and must not
be silently identified with this strict fiber.
-/

/-- The competitor-indexed complete containment fiber of one occupied node. -/
def levelSourceFullFiber
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (k : ℕ) (parent : Fin (input.levelCoarse k).card) : Finset ι :=
  Kakeya.familyIn input.s
    (fun index => (input.V index).toTube.toConvexSpaceBody)
    (input.tubeUniform.cover.tube k
      (competitorIndex (input.occupiedNodes k) parent)).toConvexSpaceBody

/-- Membership in the strict WZ2 full fiber is exactly membership in the
competitor complete containment fiber, under the canonical source index. -/
theorem mem_levelCoverOne_fullFiberIndices_iff
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N) (parent : Fin (input.levelCoarse k).card)
    (index : Fin input.source.card) :
    index ∈ (input.levelCover 1 le_rfl hk).fullContainmentFiberIndices parent ↔
      competitorIndex input.s index ∈ input.levelSourceFullFiber k parent := by
  rw [Kakeya.Streamlined.DilatedTubeCover.mem_fullContainmentFiberIndices_iff]
  simp only [levelSourceFullFiber, Kakeya.familyIn, Finset.mem_filter,
    competitorIndex_mem, true_and]
  simp [source, levelCoarse, Kakeya.Streamlined.dilatedTubeCarrier,
    AffineMap.homothety_one]
  constructor <;> intro h <;> exact h

/-- The exact source-index image of a strict WZ2 full fiber. -/
theorem image_levelCoverOne_fullFiberIndices
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N) (parent : Fin (input.levelCoarse k).card) :
    Finset.image (competitorIndex input.s)
        ((input.levelCover 1 le_rfl hk).fullContainmentFiberIndices parent) =
      input.levelSourceFullFiber k parent := by
  classical
  ext sourceIndex
  constructor
  · intro hsource
    rcases Finset.mem_image.mp hsource with ⟨index, hindex, rfl⟩
    exact (input.mem_levelCoverOne_fullFiberIndices_iff hk parent index).mp hindex
  · intro hsource
    have hsourceMem : sourceIndex ∈ input.s :=
      (Finset.mem_filter.mp hsource).1
    let index : Fin input.source.card := ⟨
      (input.s.equivFin ⟨sourceIndex, hsourceMem⟩).val,
      by
        simpa [source] using
          (input.s.equivFin ⟨sourceIndex, hsourceMem⟩).isLt⟩
    have hindexSource : competitorIndex input.s index = sourceIndex := by
      simp [index, competitorIndex, competitorIndexEquiv]
    refine Finset.mem_image.mpr ⟨index, ?_, hindexSource⟩
    apply (input.mem_levelCoverOne_fullFiberIndices_iff hk parent index).mpr
    rwa [hindexSource]

/-- Strict WZ2 full-fiber cardinality is exactly the cardinality of the
competitor complete containment fiber. -/
theorem levelCoverOne_fullFiber_card
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N) (parent : Fin (input.levelCoarse k).card) :
    ((input.levelCover 1 le_rfl hk).fullContainmentFiberIndices parent).card =
      (input.levelSourceFullFiber k parent).card := by
  rw [← input.image_levelCoverOne_fullFiberIndices hk parent]
  have hinjective : Function.Injective (competitorIndex input.s) := by
    intro first second heq
    apply (competitorIndexEquiv input.s).injective
    exact Subtype.ext heq
  exact (Finset.card_image_of_injective _ hinjective).symm

/-- The lower complete-fiber bracket comes from the assigned class inside
the same node; no equality of the two sets is asserted. -/
theorem branchingN_le_levelCoverOne_fullFiberCount
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N) (parent : Fin (input.levelCoarse k).card) :
    (input.tubeUniform.branchingN k : ENNReal) ≤
      (C : ENNReal) *
        (input.levelCover 1 le_rfl hk).fullContainmentFiberCount parent := by
  let node := competitorIndex (input.occupiedNodes k) parent
  have hnodeOccupied : node ∈ input.occupiedNodes k :=
    competitorIndex_mem (input.occupiedNodes k) parent
  have hnode : node ∈ input.tubeUniform.cover.indexSet k :=
    input.occupiedNodes_subset_indexSet hk hnodeOccupied
  have hclass := input.tubeUniform.le_card_class k hk node hnode
  have hclassSubset :
      Tube.coverClass input.s (input.tubeUniform.cover.assign k) node ⊆
        input.levelSourceFullFiber k parent := by
    simpa [levelSourceFullFiber, node] using
      (Tube.coverClass_subset_familyIn input.tubeUniform.cover hk node)
  have hcard :
      ((Tube.coverClass input.s (input.tubeUniform.cover.assign k) node).card :
          ENNReal) ≤
        ((input.levelSourceFullFiber k parent).card : ENNReal) := by
    exact_mod_cast Finset.card_le_card hclassSubset
  calc
    (input.tubeUniform.branchingN k : ENNReal)
        ≤ (C : ENNReal) *
            ((Tube.coverClass input.s
              (input.tubeUniform.cover.assign k) node).card : ENNReal) := by
          exact_mod_cast hclass
    _ ≤ (C : ENNReal) *
          ((input.levelSourceFullFiber k parent).card : ENNReal) := by
          gcongr
    _ = (C : ENNReal) *
          (input.levelCover 1 le_rfl hk).fullContainmentFiberCount parent := by
          rw [Kakeya.Streamlined.DilatedTubeCover.fullContainmentFiberCount,
            input.levelCoverOne_fullFiber_card hk parent]

/-- Bounded overlap upgrades the assigned-class upper bracket to the complete
strict-containment upper bracket, with the exact `C²` loss from `Uniform.lean`. -/
theorem levelCoverOne_fullFiberCount_le
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N) (parent : Fin (input.levelCoarse k).card) :
    (input.levelCover 1 le_rfl hk).fullContainmentFiberCount parent ≤
      (C : ENNReal) ^ 2 *
        input.tubeUniform.branchingN k := by
  let node := competitorIndex (input.occupiedNodes k) parent
  have hupper := input.tubeUniform.card_familyIn_le hk node
  rw [Kakeya.Streamlined.DilatedTubeCover.fullContainmentFiberCount,
    input.levelCoverOne_fullFiber_card hk parent]
  change ((input.levelSourceFullFiber k parent).card : ENNReal) ≤ _
  exact_mod_cast hupper

/-- Hence all strict complete fibers at one occupied level are comparable. -/
theorem levelCoverOne_fullFiber_uniform
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N)
    (first second : Fin (input.levelCoarse k).card) :
    (input.levelCover 1 le_rfl hk).fullContainmentFiberCount first ≤
      (C : ENNReal) ^ 3 *
        (input.levelCover 1 le_rfl hk).fullContainmentFiberCount second := by
  calc
    (input.levelCover 1 le_rfl hk).fullContainmentFiberCount first
        ≤ (C : ENNReal) ^ 2 * input.tubeUniform.branchingN k :=
          input.levelCoverOne_fullFiberCount_le hk first
    _ ≤ (C : ENNReal) ^ 2 *
          ((C : ENNReal) *
            (input.levelCover 1 le_rfl hk).fullContainmentFiberCount second) := by
          gcongr
          exact input.branchingN_le_levelCoverOne_fullFiberCount hk second
    _ = (C : ENNReal) ^ 3 *
          (input.levelCover 1 le_rfl hk).fullContainmentFiberCount second := by
          ring

/-- A class at the same grid level has at most `C²` times the reference
density of the complete strict fiber of any occupied node. -/
theorem classDensity_le_sq_mul_levelSourceFullFiberDensity
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N)
    (target : Fin (input.levelCoarse k).card)
    {node : ι} (hnode : node ∈ input.tubeUniform.cover.indexSet k) :
    Kakeya.densityIn
        (Tube.coverClass input.s (input.tubeUniform.cover.assign k) node)
        (fun sourceIndex => (input.V sourceIndex).toConvexSpaceBody)
        (input.tubeUniform.cover.tube k node).toConvexSpaceBody ≤
      (C : ENNReal) ^ 2 *
        Kakeya.densityIn
          (input.levelSourceFullFiber k target)
          (fun sourceIndex => (input.V sourceIndex).toConvexSpaceBody)
          (input.tubeUniform.cover.tube k
            (competitorIndex (input.occupiedNodes k) target)).toConvexSpaceBody := by
  let targetNode := competitorIndex (input.occupiedNodes k) target
  have htarget : targetNode ∈ input.tubeUniform.cover.indexSet k :=
    input.occupiedNodes_subset_indexSet hk
      (competitorIndex_mem (input.occupiedNodes k) target)
  have hclassCount := input.tubeUniform.card_class_le k hk node hnode
  have htargetLower := input.tubeUniform.le_card_class k hk targetNode htarget
  have htargetClassSubset :
      Tube.coverClass input.s (input.tubeUniform.cover.assign k) targetNode ⊆
        input.levelSourceFullFiber k target := by
    simpa [levelSourceFullFiber, targetNode] using
      (Tube.coverClass_subset_familyIn input.tubeUniform.cover hk targetNode)
  have hcount :
      ((Tube.coverClass input.s (input.tubeUniform.cover.assign k) node).card :
          ENNReal) ≤
        (C : ENNReal) ^ 2 *
          ((input.levelSourceFullFiber k target).card : ENNReal) := by
    calc
      ((Tube.coverClass input.s (input.tubeUniform.cover.assign k) node).card :
          ENNReal)
          ≤ (C : ENNReal) * input.tubeUniform.branchingN k := by
            exact_mod_cast hclassCount
      _ ≤ (C : ENNReal) *
            ((C : ENNReal) *
              ((Tube.coverClass input.s (input.tubeUniform.cover.assign k)
                targetNode).card : ENNReal)) := by
            gcongr
            exact_mod_cast htargetLower
      _ ≤ (C : ENNReal) ^ 2 *
            ((input.levelSourceFullFiber k target).card : ENNReal) := by
            have htargetCard :
                ((Tube.coverClass input.s
                  (input.tubeUniform.cover.assign k) targetNode).card :
                    ENNReal) ≤
                  ((input.levelSourceFullFiber k target).card : ENNReal) := by
              exact_mod_cast Finset.card_le_card htargetClassSubset
            calc
              (C : ENNReal) *
                    ((C : ENNReal) *
                      ((Tube.coverClass input.s
                        (input.tubeUniform.cover.assign k) targetNode).card :
                          ENNReal)) =
                  (C : ENNReal) ^ 2 *
                    ((Tube.coverClass input.s
                      (input.tubeUniform.cover.assign k) targetNode).card :
                        ENNReal) := by ring
              _ ≤ (C : ENNReal) ^ 2 *
                    ((input.levelSourceFullFiber k target).card : ENNReal) :=
                mul_le_mul_left' htargetCard _
  let fineVolume : ENNReal := Kakeya.deltaTubeVolume (delta : ℝ)
  let nodeVolume : ENNReal :=
    Kakeya.deltaTubeVolume (Tube.gridScale delta N k : ℝ)
  have hfineVolume : ∀ sourceIndex : ι,
      volume (input.V sourceIndex).carrier = fineVolume := by
    intro sourceIndex
    calc
      volume (input.V sourceIndex).carrier =
          (competitorTubeToDeltaTube (input.V sourceIndex).toTube).volume := by
        rw [competitorTubeToDeltaTube_volume]
      _ = fineVolume := by
        exact Kakeya.Streamlined.RandomTranslation.tube_volume_eq_deltaTubeVolume _
  have hnodeVolume : ∀ sourceNode : ι,
      volume (input.tubeUniform.cover.tube k sourceNode).carrier =
        nodeVolume := by
    intro sourceNode
    calc
      volume (input.tubeUniform.cover.tube k sourceNode).carrier =
          (competitorTubeToDeltaTube
            (input.tubeUniform.cover.tube k sourceNode)).volume := by
        rw [competitorTubeToDeltaTube_volume]
      _ = nodeVolume := by
        exact Kakeya.Streamlined.RandomTranslation.tube_volume_eq_deltaTubeVolume _
  have hclassContained :
      ∀ sourceIndex ∈
        Tube.coverClass input.s (input.tubeUniform.cover.assign k) node,
        (input.V sourceIndex).toConvexSpaceBody ≤
          (input.tubeUniform.cover.tube k node).toConvexSpaceBody := by
    intro sourceIndex hsource
    have hfamily :=
      Tube.coverClass_subset_familyIn input.tubeUniform.cover hk node hsource
    exact (Finset.mem_filter.mp hfamily).2
  have htargetContained :
      ∀ sourceIndex ∈ input.levelSourceFullFiber k target,
        (input.V sourceIndex).toConvexSpaceBody ≤
          (input.tubeUniform.cover.tube k targetNode).toConvexSpaceBody := by
    intro sourceIndex hsource
    exact (Finset.mem_filter.mp hsource).2
  rw [Kakeya.densityIn_of_all_le hclassContained,
    Kakeya.densityIn_of_all_le htargetContained]
  have hclassSum :
      (∑ sourceIndex ∈
          Tube.coverClass input.s (input.tubeUniform.cover.assign k) node,
          volume (input.V sourceIndex).carrier) =
        ((Tube.coverClass input.s (input.tubeUniform.cover.assign k) node).card :
          ENNReal) * fineVolume := by
    rw [Finset.sum_eq_card_nsmul (fun sourceIndex _ => hfineVolume sourceIndex),
      nsmul_eq_mul]
  have htargetSum :
      (∑ sourceIndex ∈ input.levelSourceFullFiber k target,
          volume (input.V sourceIndex).carrier) =
        ((input.levelSourceFullFiber k target).card : ENNReal) *
          fineVolume := by
    rw [Finset.sum_eq_card_nsmul (fun sourceIndex _ => hfineVolume sourceIndex),
      nsmul_eq_mul]
  rw [hclassSum, htargetSum, hnodeVolume node, hnodeVolume targetNode]
  have hquotient := ENNReal.div_le_div
    (mul_le_mul_right' hcount fineVolume) (le_refl nodeVolume)
  calc
    ((Tube.coverClass input.s (input.tubeUniform.cover.assign k) node).card :
        ENNReal) * fineVolume / nodeVolume
        ≤ ((C : ENNReal) ^ 2 *
            (input.levelSourceFullFiber k target).card) *
              fineVolume / nodeVolume := hquotient
    _ = (C : ENNReal) ^ 2 *
          ((input.levelSourceFullFiber k target).card *
            fineVolume / nodeVolume) := by
      simp [div_eq_mul_inv]
      ring

/-- The complete strict containment fiber of every occupied competitor node
is Frostman.  It is not identified with one assigned class: the proof covers
it by the bounded family of meeting-node classes and pays the explicit `C³`
loss. -/
theorem levelSourceFullFiber_isFrostmanIn
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N)
    (target : Fin (input.levelCoarse k).card) :
    ConvexSpaceBody.IsFrostmanIn
      (input.levelSourceFullFiber k target)
      (fun sourceIndex => (input.V sourceIndex).toConvexSpaceBody)
      (input.tubeUniform.cover.tube k
        (competitorIndex (input.occupiedNodes k) target)).toConvexSpaceBody
      ((C : ENNReal) ^ 3 * frostmanConstant) := by
  let targetNode := competitorIndex (input.occupiedNodes k) target
  let meeting :=
    input.tubeUniform.meetingNodes k
      (input.tubeUniform.cover.tube k targetNode)
  let classes : ι → Finset ι :=
    fun node => Tube.coverClass input.s
      (input.tubeUniform.cover.assign k) node
  have hcover :
      input.levelSourceFullFiber k target ⊆ meeting.biUnion classes := by
    simpa [levelSourceFullFiber, targetNode, meeting, classes] using
      (input.tubeUniform.familyIn_subset_biUnion_meetingNodes hk targetNode)
  have hmax := Kakeya.maxDensity_le_sum_of_subset_biUnion
    (W := fun sourceIndex => (input.V sourceIndex).toConvexSpaceBody) hcover
  have hterm : ∀ node ∈ meeting,
      Kakeya.maxDensity (classes node)
          (fun sourceIndex => (input.V sourceIndex).toConvexSpaceBody) ≤
        frostmanConstant * ((C : ENNReal) ^ 2 *
          Kakeya.densityIn (input.levelSourceFullFiber k target)
            (fun sourceIndex => (input.V sourceIndex).toConvexSpaceBody)
            (input.tubeUniform.cover.tube k targetNode).toConvexSpaceBody) := by
    intro node hnode
    have hnodeIndex : node ∈ input.tubeUniform.cover.indexSet k :=
      (Finset.mem_filter.mp hnode).1
    have hclassFrostman := input.node_frostman k hk node hnodeIndex
    have hclassContained : ∀ sourceIndex ∈ classes node,
        (input.V sourceIndex).toConvexSpaceBody ≤
          (input.tubeUniform.cover.tube k node).toConvexSpaceBody := by
      intro sourceIndex hsource
      have hfamily :=
        Tube.coverClass_subset_familyIn input.tubeUniform.cover hk node hsource
      exact (Finset.mem_filter.mp hfamily).2
    calc
      Kakeya.maxDensity (classes node)
          (fun sourceIndex => (input.V sourceIndex).toConvexSpaceBody)
          ≤ frostmanConstant *
              Kakeya.densityIn (classes node)
                (fun sourceIndex => (input.V sourceIndex).toConvexSpaceBody)
                (input.tubeUniform.cover.tube k node).toConvexSpaceBody :=
            hclassFrostman.maxDensity_le_of_carrier_subset hclassContained
      _ ≤ frostmanConstant * ((C : ENNReal) ^ 2 *
            Kakeya.densityIn (input.levelSourceFullFiber k target)
              (fun sourceIndex => (input.V sourceIndex).toConvexSpaceBody)
              (input.tubeUniform.cover.tube k targetNode).toConvexSpaceBody) := by
            gcongr
            exact input.classDensity_le_sq_mul_levelSourceFullFiberDensity
              hk target hnodeIndex
  have hmeetingCount : (meeting.card : ENNReal) ≤ (C : ENNReal) := by
    exact_mod_cast input.tubeUniform.card_meetingNodes_le hk
      (input.tubeUniform.cover.tube k targetNode)
  apply ConvexSpaceBody.IsFrostmanIn.of_maxDensity_le
  calc
    Kakeya.maxDensity (input.levelSourceFullFiber k target)
        (fun sourceIndex => (input.V sourceIndex).toConvexSpaceBody)
        ≤ ∑ node ∈ meeting, Kakeya.maxDensity (classes node)
            (fun sourceIndex => (input.V sourceIndex).toConvexSpaceBody) := hmax
    _ ≤ ∑ _node ∈ meeting,
          frostmanConstant * ((C : ENNReal) ^ 2 *
            Kakeya.densityIn (input.levelSourceFullFiber k target)
              (fun sourceIndex => (input.V sourceIndex).toConvexSpaceBody)
              (input.tubeUniform.cover.tube k targetNode).toConvexSpaceBody) :=
      Finset.sum_le_sum hterm
    _ = (meeting.card : ENNReal) *
          (frostmanConstant * ((C : ENNReal) ^ 2 *
            Kakeya.densityIn (input.levelSourceFullFiber k target)
              (fun sourceIndex => (input.V sourceIndex).toConvexSpaceBody)
              (input.tubeUniform.cover.tube k targetNode).toConvexSpaceBody)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C : ENNReal) *
          (frostmanConstant * ((C : ENNReal) ^ 2 *
            Kakeya.densityIn (input.levelSourceFullFiber k target)
              (fun sourceIndex => (input.V sourceIndex).toConvexSpaceBody)
              (input.tubeUniform.cover.tube k targetNode).toConvexSpaceBody)) := by
      gcongr
    _ = ((C : ENNReal) ^ 3 * frostmanConstant) *
          Kakeya.densityIn (input.levelSourceFullFiber k target)
            (fun sourceIndex => (input.V sourceIndex).toConvexSpaceBody)
            (input.tubeUniform.cover.tube k targetNode).toConvexSpaceBody := by
      ring

/-- The paper-semantic strict full fiber, in the exact product form required
by `PureWZ2GWZScaleData.full_fiber_frostman`. -/
theorem strict_full_fiber_frostman
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    {k : ℕ} (hk : k ≤ N)
    (parent : Fin (input.levelCoarse k).card) :
    let fiber :=
      Kakeya.Streamlined.TubeSubfamily.fromFinset input.source
        ((input.levelCover 1 le_rfl hk).fullContainmentFiberIndices parent)
    ∀ test : Set Space3,
      Convex ℝ test →
      test ⊆
        Kakeya.Streamlined.dilatedTubeCarrier 1
          ((input.levelCoarse k).tube parent) →
        fiber.family.toBodyFamily.containedMass test *
              volume
                (Kakeya.Streamlined.dilatedTubeCarrier 1
                  ((input.levelCoarse k).tube parent)) ≤
          ((C : ENNReal) ^ 3 * frostmanConstant) *
            fiber.family.toBodyFamily.mass * volume test := by
  dsimp only
  intro test hTestConvex hTestSubset
  let cover := input.levelCover 1 le_rfl hk
  let indices := cover.fullContainmentFiberIndices parent
  let fiber := Kakeya.Streamlined.TubeSubfamily.fromFinset input.source indices
  let containerSet :=
    Kakeya.Streamlined.dilatedTubeCarrier 1
      ((input.levelCoarse k).tube parent)
  let node := competitorIndex (input.occupiedNodes k) parent
  let W : ι → ConvexSpaceBody Space3 :=
    fun sourceIndex => (input.V sourceIndex).toConvexSpaceBody
  have hcontainerSet :
      containerSet = (input.tubeUniform.cover.tube k node).carrier := by
    simp [containerSet, node, levelCoarse,
      Kakeya.Streamlined.dilatedTubeCarrier, AffineMap.homothety_one]
  have himage :
      Finset.image fiber.embedding Finset.univ =
        input.source.indicesIn containerSet := by
    have hfromFinset :
        Finset.image fiber.embedding Finset.univ = indices := by
      exact Finset.image_orderEmbOfFin_univ indices rfl
    rw [hfromFinset]
    ext index
    rw [Kakeya.Streamlined.DilatedTubeCover.mem_fullContainmentFiberIndices_iff,
      Kakeya.Streamlined.TubeFamily.mem_indicesIn_iff]
  have hContainedMass :
      fiber.family.toBodyFamily.containedMass test =
        input.source.toBodyFamily.containedMass test :=
    fiber.containedMass_eq_ambient_of_image_eq
      containerSet test himage hTestSubset
  have hAllFiberContained :
      ∀ index,
        (fiber.family.toBodyFamily.body index).carrier ⊆ containerSet := by
    intro index
    change (fiber.family.tube index).carrier ⊆ containerSet
    rw [fiber.tube_eq index]
    have hindex : fiber.embedding index ∈ indices :=
      Finset.orderEmbOfFin_mem indices rfl index
    exact (cover.mem_fullContainmentFiberIndices_iff parent
      (fiber.embedding index)).mp hindex
  have hFiberMass :
      fiber.family.toBodyFamily.mass =
        input.source.toBodyFamily.containedMass containerSet := by
    rw [← Kakeya.Streamlined.BodyFamily.containedMass_eq_mass_of_all_contained
      fiber.family.toBodyFamily containerSet hAllFiberContained]
    exact fiber.containedMass_eq_ambient_of_image_eq
      containerSet containerSet himage (Set.Subset.rfl)
  have hCapturedTest :
      convexBodyFamilyInSet input.s W test =
        convexBodyFamilyInSet (input.levelSourceFullFiber k parent) W test := by
    ext sourceIndex
    simp only [mem_convexBodyFamilyInSet]
    constructor
    · rintro ⟨hsource, hbody⟩
      refine ⟨?_, hbody⟩
      apply Finset.mem_filter.mpr
      refine ⟨hsource, ?_⟩
      have hbodyContainer : (input.V sourceIndex).carrier ⊆ containerSet :=
        hbody.trans hTestSubset
      change (input.V sourceIndex).carrier ⊆
        (input.tubeUniform.cover.tube k node).carrier
      rwa [← hcontainerSet]
    · rintro ⟨hsource, hbody⟩
      exact ⟨(Finset.mem_filter.mp hsource).1, hbody⟩
  have hCapturedContainer :
      convexBodyFamilyInSet input.s W containerSet =
        input.levelSourceFullFiber k parent := by
    ext sourceIndex
    simp only [mem_convexBodyFamilyInSet, levelSourceFullFiber,
      Kakeya.familyIn, Finset.mem_filter]
    change
      (sourceIndex ∈ input.s ∧
        (input.V sourceIndex).carrier ⊆ containerSet) ↔
      (sourceIndex ∈ input.s ∧
        (input.V sourceIndex).carrier ⊆
          (input.tubeUniform.cover.tube k node).carrier)
    rw [hcontainerSet]
  have hSourceContainedMassTest :
      input.source.toBodyFamily.containedMass test =
        ∑ sourceIndex ∈
            convexBodyFamilyInSet (input.levelSourceFullFiber k parent) W test,
          volume (input.V sourceIndex).carrier := by
    change (competitorTubeFamily input.s input.V).toBodyFamily.containedMass test = _
    rw [competitorTubeFamily_containedMass input.s input.V test, hCapturedTest]
  have hSourceContainedMassContainer :
      input.source.toBodyFamily.containedMass containerSet =
        ∑ sourceIndex ∈ input.levelSourceFullFiber k parent,
          volume (input.V sourceIndex).carrier := by
    change (competitorTubeFamily input.s input.V).toBodyFamily.containedMass containerSet = _
    rw [competitorTubeFamily_containedMass input.s input.V containerSet,
      hCapturedContainer]
  have hSourceFrostman :=
    input.levelSourceFullFiber_isFrostmanIn hk parent
  have hProduct := convexBodyFrostman_product_on_convexSet
    hSourceFrostman
    (fun sourceIndex hsource => (Finset.mem_filter.mp hsource).2)
    test hTestConvex (by
      rw [← hcontainerSet]
      exact hTestSubset)
  rw [hContainedMass, hFiberMass, hSourceContainedMassTest,
    hSourceContainedMassContainer]
  change
    (∑ sourceIndex ∈
        convexBodyFamilyInSet (input.levelSourceFullFiber k parent) W test,
        volume (input.V sourceIndex).carrier) * volume containerSet ≤
      (((C : ENNReal) ^ 3 * frostmanConstant) *
        (∑ sourceIndex ∈ input.levelSourceFullFiber k parent,
          volume (input.V sourceIndex).carrier)) * volume test
  rw [hcontainerSet]
  simpa [W] using hProduct

end CompetitorStickyInput

end Kakeya.Integration

end
