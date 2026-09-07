import MyLeanRepo.Kakeya.Geometry.OuterJohnEllipsoid
import MyLeanRepo.Kakeya.Streamlined.Families

/-!
# Assouad Definition 2.12

This module records the public, ordinary-unit-segment interpretation of
Assouad Definition 2.12.  It deliberately contains no WZ line-distance cover,
cropped full-line carrier, or assigned-fiber uniformity.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- A requested Definition 2.12 scale lies between the fine scale and one. -/
abbrev WZ2PaperRequestedScale (delta : ℝ) :=
  {rho : ℝ // delta ≤ rho ∧ rho ≤ 1}

/-- A tube subfamily in the pure public layer. -/
structure WZ2PaperPureTubeSubfamily
    {delta : ℝ}
    (ambient : Kakeya.Streamlined.TubeFamily delta) where
  family : Kakeya.Streamlined.TubeFamily delta
  embedding : Fin family.card ↪ Fin ambient.card
  tube_eq :
    ∀ index,
      family.tube index = ambient.tube (embedding index)

namespace WZ2PaperPureTubeSubfamily

/-- Construct a pure tube subfamily from selected ambient indices. -/
noncomputable def fromFinset
    {delta : ℝ}
    (ambient : Kakeya.Streamlined.TubeFamily delta)
    (indices : Finset (Fin ambient.card)) :
    WZ2PaperPureTubeSubfamily ambient where
  family :=
    {
      card := indices.card
      tube := fun index =>
        ambient.tube (indices.orderEmbOfFin rfl index)
    }
  embedding := (indices.orderEmbOfFin rfl).toEmbedding
  tube_eq _ := rfl

/-- Compose two nested pure tube subfamilies. -/
def comp
    {delta : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    (outer : WZ2PaperPureTubeSubfamily ambient)
    (inner : WZ2PaperPureTubeSubfamily outer.family) :
    WZ2PaperPureTubeSubfamily ambient where
  family := inner.family
  embedding := inner.embedding.trans outer.embedding
  tube_eq index := by
    have htrans :
        (inner.embedding.trans outer.embedding) index =
          outer.embedding (inner.embedding index) :=
      Function.Embedding.trans_apply
        inner.embedding outer.embedding index
    rw [htrans, inner.tube_eq, outer.tube_eq]

end WZ2PaperPureTubeSubfamily

/-- Midpoint of the unit axis segment defining an ordinary tube. -/
def wz2PaperTubeMidpoint
    {rho : ℝ} (tube : Kakeya.DeltaTube rho) : Point3 :=
  tube.base + (1 / 2 : ℝ) • tube.direction

/-- The paper dilation `factor * A`, taken about the center of the tube. -/
def wz2PaperCenteredDilatedCarrier
    {rho : ℝ} (factor : ℝ) (tube : Kakeya.DeltaTube rho) :
    Set Point3 :=
  AffineMap.homothety (wz2PaperTubeMidpoint tube) factor ''
    tube.carrier

/-- An ordinary tube carrier is convex. -/
theorem wz2_paper_ordinary_tube_carrier_convex
    {rho : ℝ} (tube : Kakeya.DeltaTube rho) :
    Convex ℝ tube.carrier := by
  apply Convex.cthickening
  intro first hfirst second hsecond a b ha hb hab
  rcases hfirst with ⟨s, hs, rfl⟩
  rcases hsecond with ⟨t, ht, rfl⟩
  refine
    ⟨a * s + b * t,
      (convex_Icc (0 : ℝ) 1) hs ht ha hb hab, ?_⟩
  have hbase :
      a • tube.base + b • tube.base = tube.base := by
    rw [← add_smul, hab, one_smul]
  rw [smul_add, smul_add, smul_smul, smul_smul]
  rw [show
    a • tube.base + (a * s) • tube.direction +
        (b • tube.base + (b * t) • tube.direction) =
      (a • tube.base + b • tube.base) +
        ((a * s) • tube.direction +
          (b * t) • tube.direction) by abel]
  rw [hbase, ← add_smul]

/-- The center of an ordinary tube belongs to its carrier. -/
theorem wz2_paper_tubeMidpoint_mem_carrier
    {rho : ℝ} (tube : Kakeya.DeltaTube rho)
    (hrho : 0 ≤ rho) :
    wz2PaperTubeMidpoint tube ∈ tube.carrier := by
  apply Metric.mem_cthickening_of_dist_le
    (wz2PaperTubeMidpoint tube) (wz2PaperTubeMidpoint tube) rho
    (Kakeya.unitSegment tube.base tube.direction)
  · refine ⟨(1 / 2 : ℝ), ?_, rfl⟩
    constructor <;> norm_num
  · simp [hrho]

/-- Every positive-radius ordinary tube carrier is a convex body. -/
theorem wz2_paper_ordinary_tube_isConvexBody
    {rho : ℝ} (tube : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    JohnEllipsoid.IsConvexBody tube.carrier := by
  refine
    ⟨wz2_paper_ordinary_tube_carrier_convex tube, ?_, ?_⟩
  · apply IsCompact.cthickening
    exact
      isCompact_Icc.image
        (continuous_const.add
          (continuous_id.smul continuous_const))
  · refine ⟨wz2PaperTubeMidpoint tube, ?_⟩
    apply Metric.thickening_subset_interior_cthickening rho _
    rw [Metric.mem_thickening_iff]
    refine
      ⟨wz2PaperTubeMidpoint tube, ?_, by simpa using hrho⟩
    exact
      ⟨(1 / 2 : ℝ), by constructor <;> norm_num, rfl⟩

/-- A positive-radius ordinary tube carrier is compact. -/
theorem wz2_paper_ordinary_tube_carrier_compact
    {rho : ℝ} (tube : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    IsCompact tube.carrier :=
  (wz2_paper_ordinary_tube_isConvexBody tube hrho).2.1

/-- A positive-radius ordinary tube carrier is measurable. -/
theorem wz2_paper_ordinary_tube_carrier_measurable
    {rho : ℝ} (tube : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    MeasurableSet tube.carrier :=
  (wz2_paper_ordinary_tube_carrier_compact tube hrho).measurableSet

/-- A positive-radius ordinary tube carrier has positive volume. -/
theorem wz2_paper_ordinary_tube_volume_pos
    {rho : ℝ} (tube : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    0 < volume tube.carrier :=
  Measure.measure_pos_of_nonempty_interior volume
    (wz2_paper_ordinary_tube_isConvexBody tube hrho).2.2

/-- A positive-radius ordinary tube carrier has finite volume. -/
theorem wz2_paper_ordinary_tube_volume_ne_top
    {rho : ℝ} (tube : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    volume tube.carrier ≠ ⊤ :=
  (wz2_paper_ordinary_tube_carrier_compact tube hrho).measure_ne_top

/-- Exact volume scaling under the paper's centered dilation. -/
theorem wz2_paper_centeredDilatedCarrier_volume
    {rho factor : ℝ} (tube : Kakeya.DeltaTube rho) :
    volume (wz2PaperCenteredDilatedCarrier factor tube) =
      ENNReal.ofReal (|factor| ^ 3) * volume tube.carrier := by
  exact
    JohnEllipsoid.volume_homothety
      (wz2PaperTubeMidpoint tube) factor tube.carrier

/-- A positive dilation of a positive-radius ordinary tube has positive volume. -/
theorem wz2_paper_centeredDilatedCarrier_volume_pos
    {rho factor : ℝ} (tube : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) (hfactor : 0 < factor) :
    0 < volume (wz2PaperCenteredDilatedCarrier factor tube) := by
  rw [wz2_paper_centeredDilatedCarrier_volume]
  exact
    ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      (wz2_paper_ordinary_tube_volume_pos tube hrho).ne'

/-- A centered dilation of a positive-radius ordinary tube has finite volume. -/
theorem wz2_paper_centeredDilatedCarrier_volume_ne_top
    {rho factor : ℝ} (tube : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    volume (wz2PaperCenteredDilatedCarrier factor tube) ≠ ⊤ := by
  rw [wz2_paper_centeredDilatedCarrier_volume]
  exact
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (wz2_paper_ordinary_tube_volume_ne_top tube hrho)

/-- Every ordinary tube is contained in its centered two-fold dilation. -/
theorem wz2_paper_carrier_subset_centeredDilatedTwo
    {rho : ℝ} (tube : Kakeya.DeltaTube rho)
    (hrho : 0 ≤ rho) :
    tube.carrier ⊆ wz2PaperCenteredDilatedCarrier 2 tube := by
  intro point hpoint
  let center := wz2PaperTubeMidpoint tube
  let middle : Point3 :=
    (1 / 2 : ℝ) • center + (1 / 2 : ℝ) • point
  have hcenter : center ∈ tube.carrier :=
    wz2_paper_tubeMidpoint_mem_carrier tube hrho
  have hmiddle : middle ∈ tube.carrier := by
    exact
      wz2_paper_ordinary_tube_carrier_convex tube
        hcenter hpoint (by norm_num) (by norm_num) (by norm_num)
  refine ⟨middle, hmiddle, ?_⟩
  simp only [AffineMap.homothety_apply]
  dsimp only [middle, center]
  ext coordinate
  simp [wz2PaperTubeMidpoint]
  ring

/-- Centered dilations of a tube carrier are monotone in a positive factor. -/
theorem wz2_paper_centeredDilatedCarrier_mono
    {rho firstFactor secondFactor : ℝ}
    (tube : Kakeya.DeltaTube rho)
    (hrho : 0 ≤ rho)
    (hfirst : 0 ≤ firstFactor)
    (hsecond : 0 < secondFactor)
    (hfactors : firstFactor ≤ secondFactor) :
    wz2PaperCenteredDilatedCarrier firstFactor tube ⊆
      wz2PaperCenteredDilatedCarrier secondFactor tube := by
  rintro point ⟨source, hsource, rfl⟩
  let center := wz2PaperTubeMidpoint tube
  let coefficient := firstFactor / secondFactor
  let intermediate : Point3 :=
    (1 - coefficient) • center + coefficient • source
  have hcoefficientNonneg : 0 ≤ coefficient :=
    div_nonneg hfirst hsecond.le
  have hcoefficientOne : coefficient ≤ 1 :=
    (div_le_one hsecond).2 hfactors
  have hcenter : center ∈ tube.carrier :=
    wz2_paper_tubeMidpoint_mem_carrier tube hrho
  have hintermediate : intermediate ∈ tube.carrier := by
    exact
      wz2_paper_ordinary_tube_carrier_convex tube
        hcenter hsource
        (sub_nonneg.mpr hcoefficientOne)
        hcoefficientNonneg
        (by ring)
  refine ⟨intermediate, hintermediate, ?_⟩
  ext coordinate
  simp only [AffineMap.homothety_apply]
  dsimp only [intermediate, coefficient, center]
  simp [wz2PaperTubeMidpoint]
  field_simp [hsecond.ne']
  ring

/-- The strict full geometric fiber `B[A]`. -/
def wz2PaperOrdinaryFullFiberIndices
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) : Finset (Fin fine.card) :=
  Finset.univ.filter fun source =>
    (fine.tube source).carrier ⊆ (coarse.tube parent).carrier

/-- The geometric fiber `B[factor * A]`. -/
def wz2PaperOrdinaryDilatedFiberIndices
    (factor : ℝ)
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) : Finset (Fin fine.card) :=
  Finset.univ.filter fun source =>
    (fine.tube source).carrier ⊆
      wz2PaperCenteredDilatedCarrier factor (coarse.tube parent)

/-- Cardinality of one strict full geometric fiber. -/
def wz2PaperOrdinaryFullFiberCount
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (parent : Fin coarse.card) : ENNReal :=
  (wz2PaperOrdinaryFullFiberIndices fine coarse parent).card

/--
Essential distinctness in Assouad Section 2: neither ordinary tube carrier is
contained in the centered two-fold dilation of the other.
-/
def WZ2PaperOrdinaryIsEssentiallyDistinct
    {rho : ℝ}
    (family : Kakeya.Streamlined.TubeFamily rho) : Prop :=
  ∀ first second, first ≠ second →
    ¬(family.tube first).carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 (family.tube second) ∧
      ¬(family.tube second).carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 (family.tube first)

/-- A finite error constant in the sense of Definition 2.12. -/
def WZ2PaperFiniteErrorConstant (C : ENNReal) : Prop :=
  1 ≤ C ∧ C ≠ ⊤

/-- Strict full fibers have comparable indexed cardinalities. -/
def WZ2PaperPureFullFibersAreCUniform
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho)
    (C : ENNReal) : Prop :=
  ∀ first second,
    wz2PaperOrdinaryFullFiberCount fine coarse first ≤
      C * wz2PaperOrdinaryFullFiberCount fine coarse second

@[simp] theorem mem_wz2PaperOrdinaryFullFiberIndices_iff
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card) (source : Fin fine.card) :
    source ∈ wz2PaperOrdinaryFullFiberIndices fine coarse parent ↔
      (fine.tube source).carrier ⊆
        (coarse.tube parent).carrier := by
  simp [wz2PaperOrdinaryFullFiberIndices]

@[simp] theorem mem_wz2PaperOrdinaryDilatedFiberIndices_iff
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card) (source : Fin fine.card) :
    source ∈
        wz2PaperOrdinaryDilatedFiberIndices factor fine coarse parent ↔
      (fine.tube source).carrier ⊆
        wz2PaperCenteredDilatedCarrier factor
          (coarse.tube parent) := by
  simp [wz2PaperOrdinaryDilatedFiberIndices]

/--
A partitioning cover in the literal sense of Assouad Definition 2.12.

The structure contains no assigned parent.  The unique parent function is
derived below from cover existence and doubled-fiber disjointness.
-/
structure WZ2PaperPurePartitioningCover
    {delta rho : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (coarse : Kakeya.Streamlined.TubeFamily rho) : Prop where
  covers :
    ∀ source : Fin fine.card,
      ∃ parent : Fin coarse.card,
        source ∈ wz2PaperOrdinaryFullFiberIndices fine coarse parent
  doubled_fibers_disjoint :
    ∀ first second, first ≠ second →
      Disjoint
        (wz2PaperOrdinaryDilatedFiberIndices 2 fine coarse first)
        (wz2PaperOrdinaryDilatedFiberIndices 2 fine coarse second)

namespace WZ2PaperPurePartitioningCover

/-- A strict-fiber member also belongs to the corresponding doubled fiber. -/
theorem mem_doubledFiber_of_mem_fullFiber
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (hrho : 0 ≤ rho)
    {parent : Fin coarse.card} {source : Fin fine.card}
    (hsource :
      source ∈ wz2PaperOrdinaryFullFiberIndices fine coarse parent) :
    source ∈
      wz2PaperOrdinaryDilatedFiberIndices 2 fine coarse parent := by
  rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
  exact
    (mem_wz2PaperOrdinaryFullFiberIndices_iff parent source).mp hsource
      |>.trans
        (wz2_paper_carrier_subset_centeredDilatedTwo
          (coarse.tube parent) hrho)

/-- Literal partitioning makes the strict geometric parent unique. -/
theorem fullFiber_parent_unique
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (hrho : 0 ≤ rho)
    {source : Fin fine.card}
    {first second : Fin coarse.card}
    (hfirst :
      source ∈ wz2PaperOrdinaryFullFiberIndices fine coarse first)
    (hsecond :
      source ∈ wz2PaperOrdinaryFullFiberIndices fine coarse second) :
    first = second := by
  by_contra hne
  have hfirstDoubled :=
    mem_doubledFiber_of_mem_fullFiber hrho hfirst
  have hsecondDoubled :=
    mem_doubledFiber_of_mem_fullFiber hrho hsecond
  exact
    Finset.disjoint_left.mp
      (cover.doubled_fibers_disjoint first second hne)
      hfirstDoubled hsecondDoubled

/-- The unique strict geometric parent, derived from the paper cover. -/
noncomputable def parent
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (source : Fin fine.card) : Fin coarse.card :=
  Classical.choose (cover.covers source)

theorem parent_mem_fullFiber
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (source : Fin fine.card) :
    source ∈
      wz2PaperOrdinaryFullFiberIndices fine coarse
        (cover.parent source) :=
  Classical.choose_spec (cover.covers source)

@[simp] theorem mem_fullFiber_iff_parent_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (hrho : 0 ≤ rho)
    (parent : Fin coarse.card) (source : Fin fine.card) :
    source ∈ wz2PaperOrdinaryFullFiberIndices fine coarse parent ↔
      cover.parent source = parent := by
  constructor
  · intro hsource
    exact
      cover.fullFiber_parent_unique hrho
        (cover.parent_mem_fullFiber source) hsource
  · intro hparent
    rw [← hparent]
    exact cover.parent_mem_fullFiber source

/-- A nonempty strict fiber makes the derived parent map hit that parent. -/
theorem parent_surjective_of_fullFiber_nonempty
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (hrho : 0 ≤ rho)
    (hnonempty :
      ∀ parent : Fin coarse.card,
        (wz2PaperOrdinaryFullFiberIndices fine coarse parent).Nonempty) :
    Function.Surjective cover.parent := by
  intro parent
  rcases hnonempty parent with ⟨source, hsource⟩
  exact ⟨source, (cover.mem_fullFiber_iff_parent_eq hrho parent source).mp hsource⟩

/--
A uniform literal cover of a nonempty fine family has no empty coarse parent.
-/
theorem fullFiber_nonempty_of_uniform
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (fine_nonempty : fine.Nonempty)
    {C : ENNReal}
    (uniform :
      WZ2PaperPureFullFibersAreCUniform fine coarse C) :
    ∀ parent : Fin coarse.card,
      (wz2PaperOrdinaryFullFiberIndices fine coarse parent).Nonempty := by
  intro parent
  let source : Fin fine.card := ⟨0, fine_nonempty⟩
  rcases cover.covers source with ⟨occupied, hsource⟩
  by_contra hempty
  have hparentZero :
      wz2PaperOrdinaryFullFiberCount fine coarse parent = 0 := by
    rw [wz2PaperOrdinaryFullFiberCount]
    simp only [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.card_empty]
    norm_num
  have hoccupiedPos :
      0 < wz2PaperOrdinaryFullFiberCount fine coarse occupied := by
    rw [wz2PaperOrdinaryFullFiberCount]
    exact_mod_cast
      (Finset.card_pos.mpr ⟨source, hsource⟩)
  have hbound := uniform occupied parent
  rw [hparentZero, mul_zero] at hbound
  exact (not_lt_of_ge hbound) hoccupiedPos

/-- Uniformity makes the derived literal parent map surjective. -/
theorem parent_surjective_of_uniform
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (hrho : 0 ≤ rho)
    (fine_nonempty : fine.Nonempty)
    {C : ENNReal}
    (uniform :
      WZ2PaperPureFullFibersAreCUniform fine coarse C) :
    Function.Surjective cover.parent :=
  cover.parent_surjective_of_fullFiber_nonempty hrho
    (cover.fullFiber_nonempty_of_uniform fine_nonempty uniform)

/-- A literal partitioning cover with no empty fibers has an essentially
distinct coarse family in the paper's centered-dilation sense. -/
theorem coarse_essentiallyDistinct_of_fullFiber_nonempty
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (hrho : 0 ≤ rho)
    (hnonempty :
      ∀ parent : Fin coarse.card,
        (wz2PaperOrdinaryFullFiberIndices fine coarse parent).Nonempty) :
    WZ2PaperOrdinaryIsEssentiallyDistinct coarse := by
  intro first second hne
  constructor
  · intro hcontain
    rcases hnonempty first with ⟨source, hsource⟩
    have hfirst :
        source ∈
          wz2PaperOrdinaryDilatedFiberIndices 2 fine coarse first :=
      mem_doubledFiber_of_mem_fullFiber hrho hsource
    have hsecond :
        source ∈
          wz2PaperOrdinaryDilatedFiberIndices 2 fine coarse second := by
      rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
      exact
        ((mem_wz2PaperOrdinaryFullFiberIndices_iff first source).mp
          hsource).trans hcontain
    exact
      Finset.disjoint_left.mp
        (cover.doubled_fibers_disjoint first second hne)
        hfirst hsecond
  · intro hcontain
    rcases hnonempty second with ⟨source, hsource⟩
    have hsecond :
        source ∈
          wz2PaperOrdinaryDilatedFiberIndices 2 fine coarse second :=
      mem_doubledFiber_of_mem_fullFiber hrho hsource
    have hfirst :
        source ∈
          wz2PaperOrdinaryDilatedFiberIndices 2 fine coarse first := by
      rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
      exact
        ((mem_wz2PaperOrdinaryFullFiberIndices_iff second source).mp
          hsource).trans hcontain
    exact
      Finset.disjoint_left.mp
        (cover.doubled_fibers_disjoint first second hne)
        hfirst hsecond

/-- Finite uniformity supplies the nonempty fibers needed for coarse
essential distinctness. -/
theorem coarse_essentiallyDistinct_of_uniform
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (hrho : 0 ≤ rho)
    (fine_nonempty : fine.Nonempty)
    {C : ENNReal}
    (uniform :
      WZ2PaperPureFullFibersAreCUniform fine coarse C) :
    WZ2PaperOrdinaryIsEssentiallyDistinct coarse :=
  cover.coarse_essentiallyDistinct_of_fullFiber_nonempty hrho
    (cover.fullFiber_nonempty_of_uniform fine_nonempty uniform)

end WZ2PaperPurePartitioningCover

/-- Assouad's affine normalization of one convex parent body. -/
structure WZ2PaperAssouadUnitRescalingData
    {rho : ℝ} (parent : Kakeya.DeltaTube rho) where
  parent_convex_body :
    JohnEllipsoid.IsConvexBody parent.carrier

namespace WZ2PaperAssouadUnitRescalingData

/-- Every positive-radius ordinary tube has a canonical Assouad
normalization. -/
noncomputable def ofTube
    {rho : ℝ} (parent : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    WZ2PaperAssouadUnitRescalingData parent where
  parent_convex_body :=
    wz2_paper_ordinary_tube_isConvexBody parent hrho

/-- The canonical affine map sending the outer John ellipsoid to the unit ball. -/
noncomputable def map
    {rho : ℝ} {parent : Kakeya.DeltaTube rho}
    (normalization : WZ2PaperAssouadUnitRescalingData parent) :
    Point3 ≃ᵃ[ℝ] Point3 :=
  AffineEquiv.ofLinearEquiv
    normalization.parent_convex_body.outerJohnEllipsoidMap.symm
    normalization.parent_convex_body.outerJohnEllipsoidCenter
    0

/-- The canonical Assouad normalization sends the outer John ellipsoid exactly
onto the closed unit ball. -/
theorem outerJohn_image
    {rho : ℝ} {parent : Kakeya.DeltaTube rho}
    (normalization : WZ2PaperAssouadUnitRescalingData parent) :
    normalization.map ''
        normalization.parent_convex_body.outerJohnEllipsoid =
      Metric.closedBall (0 : Point3) 1 := by
  let center :=
    normalization.parent_convex_body.outerJohnEllipsoidCenter
  let linear :=
    normalization.parent_convex_body.outerJohnEllipsoidMap
  ext point
  constructor
  · rintro ⟨source, hsource, rfl⟩
    rw [JohnEllipsoid.ellipsoid_mem_iff] at hsource
    simpa [map, center, linear, Metric.mem_closedBall, dist_zero_right]
      using hsource
  · intro hpoint
    refine ⟨center + linear point, ?_, ?_⟩
    · rw [JohnEllipsoid.ellipsoid_mem_iff]
      change ‖linear.symm ((center + linear point) - center)‖ ≤ 1
      simpa [Metric.mem_closedBall, dist_zero_right] using hpoint
    · simp [map, center, linear]

end WZ2PaperAssouadUnitRescalingData

/-- Convex-Wolff counting for an indexed family of actual affine images. -/
def WZ2PaperBodyConvexWolffBound
    (family : Kakeya.Streamlined.BodyFamily)
    (C : ENNReal) : Prop :=
  ∀ convexSet : Set Point3, Convex ℝ convexSet →
    family.containedCount convexSet ≤
      C * volume convexSet * family.enncard

/-- Canonical index equivalence for one complete strict full fiber. -/
noncomputable def wz2PaperOrdinaryFullFiberIndexEquiv
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card) :
    Fin (wz2PaperOrdinaryFullFiberIndices fine coarse parent).card ≃
      {source : Fin fine.card //
        source ∈
          wz2PaperOrdinaryFullFiberIndices fine coarse parent} :=
  (wz2PaperOrdinaryFullFiberIndices fine coarse parent).orderIsoOfFin rfl
    |>.toEquiv

/-- The actual affine-image body family of one complete strict full fiber. -/
noncomputable def wz2PaperPureUnitRescaledFullFiberBodyFamily
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card)
    (normalization :
      WZ2PaperAssouadUnitRescalingData (coarse.tube parent)) :
    Kakeya.Streamlined.BodyFamily where
  card := (wz2PaperOrdinaryFullFiberIndices fine coarse parent).card
  body target :=
    ⟨normalization.map ''
      (fine.tube
        ((wz2PaperOrdinaryFullFiberIndexEquiv parent) target).1).carrier⟩

/-- The actual affine-image unit rescaling of one complete strict full fiber. -/
structure WZ2PaperPureUnitRescaledFullFiberData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card)
    (C : ENNReal) where
  normalization :
    WZ2PaperAssouadUnitRescalingData (coarse.tube parent)
  convex_wolff :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := fine) (coarse := coarse) parent normalization)
      C

/-- One literal Definition 2.12 cover at its actual selected scale. -/
structure WZ2PaperPureScaleCoverData
    {delta : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (rho : ℝ)
    (C : ENNReal) where
  delta_pos : 0 < delta
  rho_pos : 0 < rho
  coarse : Kakeya.Streamlined.TubeFamily rho
  cover : WZ2PaperPurePartitioningCover fine coarse
  full_fiber_uniform :
    WZ2PaperPureFullFibersAreCUniform fine coarse C
  rescaledFiber :
    ∀ parent : Fin coarse.card,
      Nonempty
        (WZ2PaperPureUnitRescaledFullFiberData
          (fine := fine) (coarse := coarse) parent C)

/--
One Definition 2.12 witness for the requested scale `rho₀`.

The actual scale is not given the extra type-level condition `rho ≤ 1`.
-/
structure WZ2PaperPureNearbyScaleCoverData
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (rho₀ : WZ2PaperRequestedScale delta)
    (C : ENNReal) where
  rho : ℝ
  requested_le : rho₀.1 ≤ rho
  within_factor :
    ENNReal.ofReal rho <
      C * ENNReal.ofReal rho₀.1
  scaleData : WZ2PaperPureScaleCoverData family rho C

/-- Assouad Definition 2.12 with literal fibers and a finite error constant. -/
def WZ2PaperPureCWAAtNearbyScales
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (C : ENNReal) : Prop :=
  0 < delta ∧
    WZ2PaperFiniteErrorConstant C ∧
      WZ2PaperOrdinaryIsEssentiallyDistinct family ∧
        ∀ rho₀ : WZ2PaperRequestedScale delta,
          Nonempty (WZ2PaperPureNearbyScaleCoverData family rho₀ C)

end Kakeya.Assouad

end
