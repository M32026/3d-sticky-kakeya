import MyLeanRepo.Kakeya.Assouad.PropStickyFullFiberHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.PaperPackingRefinement

/-!
# Paper refinement helpers for WZ2 `prop: sticky`

Restrict cropped-paper shadings to genuine tube subfamilies and isolate one
full geometric parent fiber.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Restrict a cropped-paper shading to a tube subfamily. -/
def restrictPaperShading
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (shading : WZ1PaperTubeShading family) :
    WZ1PaperTubeShading selected.family where
  carrier index := shading.carrier (selected.embedding index)
  measurable_carrier index :=
    shading.measurable_carrier (selected.embedding index)
  subset_body index := by
    have h := shading.subset_body (selected.embedding index)
    change shading.carrier (selected.embedding index) ⊆
      wz1PaperTubeCarrier (selected.family.tube index)
    rw [selected.tube_eq index]
    exact h

theorem restrictPaperShading_mass
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (shading : WZ1PaperTubeShading family) :
    (restrictPaperShading selected shading).mass =
      ∑ index : Fin selected.family.card,
        volume (shading.carrier (selected.embedding index)) :=
  rfl

theorem restrictPaperShading_cubical
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading) :
    WZ1PaperIsCubicalShading
      (restrictPaperShading selected shading) := by
  intro index point hpoint
  exact hcubical (selected.embedding index) point hpoint

/-- Paper line-distance essential distinctness restricts to tube subfamilies. -/
theorem WZ1PaperIsEssentiallyDistinct.subfamily
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hfamily : WZ1PaperIsEssentiallyDistinct family)
    (selected : Kakeya.Streamlined.TubeSubfamily family) :
    WZ1PaperIsEssentiallyDistinct selected.family := by
  intro first second hne
  have hembedding :
      selected.embedding first ≠ selected.embedding second := by
    intro heq
    exact hne (selected.embedding.injective heq)
  simpa only [selected.tube_eq] using
    hfamily (selected.embedding first)
      (selected.embedding second) hembedding

/-- Membership in the fixed paper line class restricts to tube subfamilies. -/
theorem WZ1PaperIsLineClass.subfamily
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hfamily : WZ1PaperIsLineClass family)
    (selected : Kakeya.Streamlined.TubeSubfamily family) :
    WZ1PaperIsLineClass selected.family := by
  intro index
  simpa only [selected.tube_eq] using
    hfamily (selected.embedding index)

/-- Indices whose cropped-paper shaded carrier has positive measure. -/
def paperPositiveMassIndices
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) :
    Finset (Fin family.card) :=
  Finset.univ.filter fun index =>
    volume (shading.carrier index) ≠ 0

/-- The genuine subfamily obtained by discarding zero-mass carriers. -/
def paperPositiveMassSubfamily
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) :
    Kakeya.Streamlined.TubeSubfamily family :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset family
    (paperPositiveMassIndices shading)

theorem paperPositiveMassSubfamily_carrier_nonempty
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (index : Fin (paperPositiveMassSubfamily shading).family.card) :
    (shading.carrier
      ((paperPositiveMassSubfamily shading).embedding index)).Nonempty := by
  apply Set.nonempty_iff_ne_empty.mpr
  intro hempty
  have hpositive :
      volume
          (shading.carrier
            ((paperPositiveMassSubfamily shading).embedding index)) ≠
        0 := by
    exact
      (Finset.mem_filter.mp
        (Finset.orderEmbOfFin_mem
          (paperPositiveMassIndices shading) rfl index)).2
  apply hpositive
  rw [hempty]
  simp

theorem restrictPaperShading_positiveMass_mass
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) :
    (restrictPaperShading
      (paperPositiveMassSubfamily shading) shading).mass =
      shading.mass := by
  rw [restrictPaperShading_mass]
  let indices := paperPositiveMassIndices shading
  let equivalence : Fin indices.card ≃ indices :=
    (indices.orderIsoOfFin rfl).toEquiv
  calc
    ∑ index : Fin (paperPositiveMassSubfamily shading).family.card,
        volume
          (shading.carrier
            ((paperPositiveMassSubfamily shading).embedding index)) =
        ∑ source : indices,
          volume (shading.carrier source.1) := by
      exact
        Fintype.sum_equiv equivalence
          (fun index :
              Fin (paperPositiveMassSubfamily shading).family.card =>
            volume
              (shading.carrier
                ((paperPositiveMassSubfamily shading).embedding index)))
          (fun source : indices =>
            volume (shading.carrier source.1))
          (fun _ => rfl)
    _ =
        ∑ source ∈ indices,
          volume (shading.carrier source) := by
      exact Finset.sum_coe_sort indices
        (fun source => volume (shading.carrier source))
    _ =
        ∑ source : Fin family.card,
          volume (shading.carrier source) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro source _ hsource
      have hzero :
          ¬volume (shading.carrier source) ≠ 0 := by
        simpa [indices, paperPositiveMassIndices] using hsource
      exact not_ne_iff.mp hzero
    _ = shading.mass := rfl

/--
Discard zero-mass carriers from a paper refinement.

This keeps the retained mass exactly and produces a genuine selected
subfamily whose every shaded carrier is nonempty.
-/
noncomputable def WZ1PaperRefinement.removeZeroMass
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {logExponent : ℕ}
    (refinement : WZ1PaperRefinement shading logExponent) :
    WZ1PaperRefinement shading logExponent := by
  let positive := paperPositiveMassSubfamily refinement.refined
  let selected : Kakeya.Streamlined.TubeSubfamily source :=
    { family := positive.family
      embedding :=
        positive.embedding.trans refinement.selected.embedding
      tube_eq := by
        intro index
        have htrans :
            (positive.embedding.trans
              refinement.selected.embedding) index =
              refinement.selected.embedding
                (positive.embedding index) :=
          Function.Embedding.trans_apply
            positive.embedding refinement.selected.embedding index
        rw [
          htrans,
          positive.tube_eq index,
          refinement.selected.tube_eq
            (positive.embedding index)
        ] }
  refine
    { selected := selected
      refined :=
        restrictPaperShading positive refinement.refined
      subshading := ?_
      retained_mass := ?_ }
  · intro index point hpoint
    exact
      refinement.subshading
        (positive.embedding index) hpoint
  · rw [restrictPaperShading_positiveMass_mass]
    exact refinement.retained_mass

theorem WZ1PaperRefinement.removeZeroMass_carrier_nonempty
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {logExponent : ℕ}
    (refinement : WZ1PaperRefinement shading logExponent)
    (index : Fin refinement.removeZeroMass.selected.family.card) :
    (refinement.removeZeroMass.refined.carrier index).Nonempty := by
  change
    (refinement.refined.carrier
      ((paperPositiveMassSubfamily
        refinement.refined).embedding index)).Nonempty
  exact paperPositiveMassSubfamily_carrier_nonempty
    refinement.refined index

theorem WZ1PaperRefinement.removeZeroMass_cubical
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {logExponent : ℕ}
    (refinement : WZ1PaperRefinement shading logExponent)
    (hcubical :
      WZ1PaperIsCubicalShading refinement.refined) :
    WZ1PaperIsCubicalShading
      refinement.removeZeroMass.refined := by
  change
    WZ1PaperIsCubicalShading
      (restrictPaperShading
        (paperPositiveMassSubfamily refinement.refined)
        refinement.refined)
  exact
    restrictPaperShading_cubical
      (paperPositiveMassSubfamily refinement.refined)
      hcubical

/-- The genuine subfamily of all fine tubes in one full geometric fiber. -/
def WZ2PaperPartitioningCover.fullFiberSubfamily
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (parent : Fin coarse.card) :
    Kakeya.Streamlined.TubeSubfamily fine :=
  wz2PaperFullFiberSubfamily fine coarse parent

/-- A genuine full geometric fiber inherits ambient paper essential distinctness. -/
theorem WZ2PaperPartitioningCover.fullFiberSubfamily_essentiallyDistinct
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (hfamily : WZ1PaperIsEssentiallyDistinct fine)
    (parent : Fin coarse.card) :
    WZ1PaperIsEssentiallyDistinct
      (cover.fullFiberSubfamily parent).family :=
  hfamily.subfamily (cover.fullFiberSubfamily parent)

theorem WZ2PaperPartitioningCover.fullFiberSubfamily_nonempty
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (parent : Fin coarse.card) :
    (cover.fullFiberSubfamily parent).Nonempty := by
  change 0 < (wz2PaperFullFiberIndices fine coarse parent).card
  exact Finset.card_pos.mpr (cover.fullFiber_nonempty parent)

theorem WZ2PaperPartitioningCover.fullFiberSubfamily_mem
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (parent : Fin coarse.card)
    (index : Fin (cover.fullFiberSubfamily parent).family.card) :
    (cover.fullFiberSubfamily parent).embedding index ∈
      wz2PaperFullFiberIndices fine coarse parent := by
  exact Finset.orderEmbOfFin_mem
    (wz2PaperFullFiberIndices fine coarse parent) rfl index

theorem WZ2PaperPartitioningCover.fullFiberSubfamily_covered
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (parent : Fin coarse.card)
    (index : Fin (cover.fullFiberSubfamily parent).family.card) :
    WZ1PaperTubeCovers
      ((cover.fullFiberSubfamily parent).family.tube index)
      (coarse.tube parent) := by
  rw [(cover.fullFiberSubfamily parent).tube_eq index]
  exact
    (mem_wz2PaperFullFiberIndices_iff parent
      ((cover.fullFiberSubfamily parent).embedding index)).mp
      (cover.fullFiberSubfamily_mem parent index)

/-- A canonical full-fiber member is literally contained in its parent carrier. -/
theorem WZ2PaperPartitioningCover.fullFiberSubfamily_carrier_covered
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (parent : Fin coarse.card)
    (index : Fin (cover.fullFiberSubfamily parent).family.card) :
    WZ2PaperTubeCarrierCovers
      ((cover.fullFiberSubfamily parent).family.tube index)
      (coarse.tube parent) := by
  rw [(cover.fullFiberSubfamily parent).tube_eq index]
  have hparent :
      cover.parent
          ((cover.fullFiberSubfamily parent).embedding index) =
        parent :=
    (cover.mem_fullFiber_iff_parent parent
      ((cover.fullFiberSubfamily parent).embedding index)).mp
      (cover.fullFiberSubfamily_mem parent index)
  have hcovered :=
    cover.parent_carrier_covers
      ((cover.fullFiberSubfamily parent).embedding index)
  simpa only [hparent] using hcovered

/--
Identify the indices of a supplied unit-rescaled full fiber with the subtype
of ambient indices in the full geometric fiber.
-/
noncomputable def
    WZ2PaperUnitRescaledFamilyData.targetEquivFullFiberSubtype
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C : ENNReal}
    (data :
      WZ2PaperUnitRescaledFamilyData
        cover parent hrho C) :
    Fin data.targetFamily.card ≃
      wz2PaperFullFiberIndices fine coarse parent := by
  let indices := wz2PaperFullFiberIndices fine coarse parent
  let toFiber :
      Fin data.targetFamily.card → indices :=
    fun target =>
      ⟨data.sourceIndex target, data.sourceIndex_mem target⟩
  apply Equiv.ofBijective toFiber
  constructor
  · intro first second heq
    apply data.sourceIndex_injective
    exact congrArg Subtype.val heq
  · intro source
    rcases data.sourceIndex_surjective
        source.1 source.2 with
      ⟨target, htarget⟩
    refine ⟨target, ?_⟩
    apply Subtype.ext
    exact htarget

@[simp] theorem
    WZ2PaperUnitRescaledFamilyData.targetEquivFullFiberSubtype_val
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C : ENNReal}
    (data :
      WZ2PaperUnitRescaledFamilyData
        cover parent hrho C)
    (target : Fin data.targetFamily.card) :
    (data.targetEquivFullFiberSubtype target).1 =
      data.sourceIndex target :=
  rfl

/--
Identify the indices of a supplied unit-rescaled full fiber with the
canonical source full-fiber subfamily.
-/
noncomputable def WZ2PaperUnitRescaledFamilyData.targetEquivFullFiber
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C : ENNReal}
    (data :
      WZ2PaperUnitRescaledFamilyData
        cover parent hrho C) :
    Fin data.targetFamily.card ≃
      Fin (cover.fullFiberSubfamily parent).family.card :=
  data.targetEquivFullFiberSubtype.trans
    ((wz2PaperFullFiberIndices
      fine coarse parent).orderIsoOfFin rfl).toEquiv.symm

@[simp] theorem
    WZ2PaperUnitRescaledFamilyData.targetEquivFullFiber_ambient
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C : ENNReal}
    (data :
      WZ2PaperUnitRescaledFamilyData
        cover parent hrho C)
    (target : Fin data.targetFamily.card) :
    (cover.fullFiberSubfamily parent).embedding
        (data.targetEquivFullFiber target) =
      data.sourceIndex target := by
  let indices := wz2PaperFullFiberIndices fine coarse parent
  let enumeration : Fin indices.card ≃ indices :=
    (indices.orderIsoOfFin rfl).toEquiv
  change
    (indices.orderEmbOfFin rfl)
        (enumeration.symm
          (data.targetEquivFullFiberSubtype target)) =
      data.sourceIndex target
  calc
    (indices.orderEmbOfFin rfl)
        (enumeration.symm
          (data.targetEquivFullFiberSubtype target)) =
        (data.targetEquivFullFiberSubtype target).1 := by
      exact congrArg Subtype.val
        (enumeration.apply_symm_apply
          (data.targetEquivFullFiberSubtype target))
    _ = data.sourceIndex target :=
      data.targetEquivFullFiberSubtype_val target

/--
Select from a stable target family exactly the tubes corresponding to a
source subfamily of the canonical full geometric fiber.
-/
noncomputable def
    WZ2PaperUnitRescaledFamilyData.targetSubfamilyForSource
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C : ENNReal}
    (data :
      WZ2PaperUnitRescaledFamilyData
        cover parent hrho C)
    (sourceSelected :
      Kakeya.Streamlined.TubeSubfamily
        (cover.fullFiberSubfamily parent).family) :
    Kakeya.Streamlined.TubeSubfamily data.targetFamily where
  family :=
    { card := sourceSelected.family.card
      tube := fun index =>
        data.targetFamily.tube
          (data.targetEquivFullFiber.symm
            (sourceSelected.embedding index)) }
  embedding :=
    { toFun := fun index =>
        data.targetEquivFullFiber.symm
          (sourceSelected.embedding index)
      inj' := fun first second heq =>
        sourceSelected.embedding.injective
          (data.targetEquivFullFiber.symm.injective heq) }
  tube_eq _ := rfl

theorem
    WZ2PaperUnitRescaledFamilyData.targetSubfamilyForSource_embedding_surjective
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C : ENNReal}
    (data :
      WZ2PaperUnitRescaledFamilyData
        cover parent hrho C)
    (sourceSelected :
      Kakeya.Streamlined.TubeSubfamily
        (cover.fullFiberSubfamily parent).family)
    (hSource : Function.Surjective sourceSelected.embedding) :
    Function.Surjective
      (data.targetSubfamilyForSource sourceSelected).embedding := by
  intro target
  let sourceIndex := data.targetEquivFullFiber target
  rcases hSource sourceIndex with ⟨selectedIndex, hselected⟩
  let selectedTarget :
      Fin (data.targetSubfamilyForSource sourceSelected).family.card :=
    ⟨selectedIndex.val, by
      simpa [WZ2PaperUnitRescaledFamilyData.targetSubfamilyForSource] using
        selectedIndex.isLt⟩
  refine ⟨selectedTarget, ?_⟩
  change
    data.targetEquivFullFiber.symm
        (sourceSelected.embedding selectedTarget) =
      target
  have hSelectedTarget :
      sourceSelected.embedding selectedTarget = sourceIndex := by
    apply Fin.ext
    exact congrArg Fin.val hselected
  rw [hSelectedTarget]
  exact data.targetEquivFullFiber.symm_apply_apply target

@[simp] theorem
    WZ2PaperUnitRescaledFamilyData.targetSubfamilyForSource_sourceIndex
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C : ENNReal}
    (data :
      WZ2PaperUnitRescaledFamilyData
        cover parent hrho C)
    (sourceSelected :
      Kakeya.Streamlined.TubeSubfamily
        (cover.fullFiberSubfamily parent).family)
    (index : Fin sourceSelected.family.card) :
    (cover.fullFiberSubfamily parent).embedding
        (sourceSelected.embedding index) =
      data.sourceIndex
        ((data.targetSubfamilyForSource
          sourceSelected).embedding index) := by
  change
    (cover.fullFiberSubfamily parent).embedding
        (sourceSelected.embedding index) =
      data.sourceIndex
        (data.targetEquivFullFiber.symm
          (sourceSelected.embedding index))
  simpa only [data.targetEquivFullFiber.apply_symm_apply] using
    data.targetEquivFullFiber_ambient
      (data.targetEquivFullFiber.symm
        (sourceSelected.embedding index))

/--
Axis provenance on the target subfamily selected by a source refinement.
-/
theorem WZ2PaperUnitRescaledFamilyData.targetSubfamilyForSource_axis
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C : ENNReal}
    (data :
      WZ2PaperUnitRescaledFamilyData
        cover parent hrho C)
    (sourceSelected :
      Kakeya.Streamlined.TubeSubfamily
        (cover.fullFiberSubfamily parent).family)
    (index : Fin sourceSelected.family.card) :
    tubeAxisLine
        ((data.targetSubfamilyForSource
          sourceSelected).family.tube index) =
      wz1PaperUnitRescalingMap
          (coarse.tube parent) hrho ''
        tubeAxisLine
          ((cover.fullFiberSubfamily parent).family.tube
            (sourceSelected.embedding index)) := by
  rw [
    (data.targetSubfamilyForSource
      sourceSelected).tube_eq index,
    data.target_axis,
    ← data.targetSubfamilyForSource_sourceIndex
      sourceSelected index,
    (cover.fullFiberSubfamily parent).tube_eq
  ]

/--
Package a shading on a supplied stable target family as the literal
coarse-relative image of a shading on the canonical source full fiber.
-/
noncomputable def
    WZ2PaperUnitRescaledFamilyData.toPaperUnitRescaledImageData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {parent : Fin coarse.card}
    {hrho : 0 < rho}
    {C : ENNReal}
    (data :
      WZ2PaperUnitRescaledFamilyData
        cover parent hrho C)
    (sourceShading :
      WZ1PaperTubeShading
        (cover.fullFiberSubfamily parent).family)
    (targetShading :
      WZ1PaperTubeShading data.targetFamily)
    (target_carrier_eq :
      ∀ target,
        targetShading.carrier target =
          wz1PaperCubicalSaturation (delta / rho)
            (wz1PaperUnitRescalingMap
                (coarse.tube parent) hrho ''
              sourceShading.carrier
                (data.targetEquivFullFiber target))) :
    WZ1PaperUnitRescaledImageData
      sourceShading (fun _ => True)
      (coarse.tube parent) hrho
      data.targetFamily targetShading where
  sourceIndex := data.targetEquivFullFiber
  sourceIndex_active _ := trivial
  sourceIndex_injective :=
    data.targetEquivFullFiber.injective
  sourceIndex_surjective _ _ :=
    data.targetEquivFullFiber.surjective _
  target_axis target := by
    calc
      tubeAxisLine (data.targetFamily.tube target) =
          wz1PaperUnitRescalingMap
              (coarse.tube parent) hrho ''
            tubeAxisLine
              (fine.tube (data.sourceIndex target)) :=
        data.target_axis target
      _ =
          wz1PaperUnitRescalingMap
              (coarse.tube parent) hrho ''
            tubeAxisLine
              ((cover.fullFiberSubfamily parent).family.tube
                (data.targetEquivFullFiber target)) := by
        rw [
          (cover.fullFiberSubfamily parent).tube_eq,
          data.targetEquivFullFiber_ambient target
        ]
  target_carrier_eq := target_carrier_eq

theorem WZ2PaperPartitioningCover.fullFiberShading_mass
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card) :
    (restrictPaperShading
      (cover.fullFiberSubfamily parent) shading).mass =
      ∑ source ∈ wz2PaperFullFiberIndices fine coarse parent,
        volume (shading.carrier source) := by
  rw [restrictPaperShading_mass]
  let indices := wz2PaperFullFiberIndices fine coarse parent
  let equivalence : Fin indices.card ≃ indices :=
    (indices.orderIsoOfFin rfl).toEquiv
  calc
    ∑ index : Fin (cover.fullFiberSubfamily parent).family.card,
        volume
          (shading.carrier
            ((cover.fullFiberSubfamily parent).embedding index)) =
        ∑ source : indices, volume (shading.carrier source.1) := by
      exact
        Fintype.sum_equiv equivalence
          (fun index :
              Fin (cover.fullFiberSubfamily parent).family.card =>
            volume
              (shading.carrier
                ((cover.fullFiberSubfamily parent).embedding index)))
          (fun source : indices => volume (shading.carrier source.1))
          (fun _ => rfl)
    _ = ∑ source ∈ indices, volume (shading.carrier source) := by
      exact Finset.sum_coe_sort indices
        (fun source => volume (shading.carrier source))

/--
The full geometric fibers partition the paper shading mass exactly.
-/
theorem WZ2PaperPartitioningCover.sum_fullFiberShading_mass
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine) :
    ∑ parent : Fin coarse.card,
        (restrictPaperShading
          (cover.fullFiberSubfamily parent) shading).mass =
      shading.mass := by
  simp_rw [cover.fullFiberShading_mass shading]
  have hsum :
      ∑ parent : Fin coarse.card,
          ∑ source ∈ Finset.univ with
              cover.parent source = parent,
            volume (shading.carrier source) =
        ∑ source : Fin fine.card,
          volume (shading.carrier source) := by
    exact
      Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ) (t := Finset.univ)
        (g := cover.parent)
        (fun _ _ => Finset.mem_univ _)
        (fun source => volume (shading.carrier source))
  calc
    ∑ parent : Fin coarse.card,
        ∑ source ∈ wz2PaperFullFiberIndices
            fine coarse parent,
          volume (shading.carrier source) =
        ∑ parent : Fin coarse.card,
          ∑ source ∈ cover.fiberIndices parent,
            volume (shading.carrier source) := by
      apply Finset.sum_congr rfl
      intro parent _
      rw [cover.fullFiberIndices_eq parent]
    _ = shading.mass := by
      change
        (∑ parent : Fin coarse.card,
            ∑ source ∈ Finset.univ with
                cover.parent source = parent,
              volume (shading.carrier source)) =
          ∑ source : Fin fine.card,
            volume (shading.carrier source)
      exact hsum

/--
Restrict the fine side of a paper partitioning cover.

The caller supplies the only non-hereditary field: every coarse parent must
still have a selected fine child.  Geometric coverage, uniqueness, and
doubled-fiber disjointness then restrict directly.
-/
def WZ2PaperPartitioningCover.restrictFine
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (parent_surjective :
      Function.Surjective fun index =>
        cover.parent (selected.embedding index)) :
    WZ2PaperPartitioningCover selected.family coarse where
  parent index := cover.parent (selected.embedding index)
  parent_surjective := parent_surjective
  parent_covers index := by
    rw [selected.tube_eq index]
    exact cover.parent_covers (selected.embedding index)
  parent_unique source candidate hcovered := by
    apply cover.parent_unique (selected.embedding source) candidate
    rw [← selected.tube_eq source]
    exact hcovered
  parent_carrier_covers index := by
    rw [selected.tube_eq index]
    exact cover.parent_carrier_covers (selected.embedding index)
  literal_parent_unique source candidate hcovered := by
    apply cover.literal_parent_unique
      (selected.embedding source) candidate
    rw [← selected.tube_eq source]
    exact hcovered
  literal_doubled_fibers_disjoint first second hne := by
    rw [Finset.disjoint_left]
    intro index hfirst hsecond
    have hambientFirst :
        selected.embedding index ∈
          wz2PaperLiteralDoubledFiberIndices fine coarse first := by
      simpa [wz2PaperLiteralDoubledFiberIndices,
        selected.tube_eq index] using hfirst
    have hambientSecond :
        selected.embedding index ∈
          wz2PaperLiteralDoubledFiberIndices fine coarse second := by
      simpa [wz2PaperLiteralDoubledFiberIndices,
        selected.tube_eq index] using hsecond
    exact
      ((Finset.disjoint_left.mp
          (cover.literal_doubled_fibers_disjoint first second hne))
        hambientFirst) hambientSecond
  doubled_fibers_disjoint first second hne := by
    rw [Finset.disjoint_left]
    intro index hfirst hsecond
    have hambientFirst :
        selected.embedding index ∈
          wz2PaperDoubledFiberIndices fine coarse first := by
      simpa [wz2PaperDoubledFiberIndices, selected.tube_eq index]
        using hfirst
    have hambientSecond :
        selected.embedding index ∈
          wz2PaperDoubledFiberIndices fine coarse second := by
      simpa [wz2PaperDoubledFiberIndices, selected.tube_eq index]
        using hsecond
    exact
      ((Finset.disjoint_left.mp
          (cover.doubled_fibers_disjoint first second hne))
        hambientFirst) hambientSecond

@[simp] theorem WZ2PaperPartitioningCover.restrictFine_parent
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (parent_surjective :
      Function.Surjective fun index =>
        cover.parent (selected.embedding index))
    (index : Fin selected.family.card) :
    (cover.restrictFine selected parent_surjective).parent index =
      cover.parent (selected.embedding index) :=
  rfl

@[simp] theorem WZ2PaperPartitioningCover.restrictFine_mem_fullFiber
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (parent_surjective :
      Function.Surjective fun index =>
        cover.parent (selected.embedding index))
    (parent : Fin coarse.card)
    (index : Fin selected.family.card) :
    index ∈
        wz2PaperFullFiberIndices
          selected.family coarse parent ↔
      cover.parent (selected.embedding index) = parent := by
  simpa using
    (WZ2PaperPartitioningCover.mem_fullFiber_iff_parent
      (cover.restrictFine selected parent_surjective)
      parent index)

/-- Compose two mass-retention bounds along nested tube subfamilies. -/
theorem compose_mass_retention
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (outer : Kakeya.Streamlined.TubeSubfamily family)
    (inner : Kakeya.Streamlined.TubeSubfamily outer.family)
    (scaleCount familyCard : ℕ)
    (hOuter :
      shading.mass ≤
        (packingConstant10000 : ENNReal) ^ scaleCount *
          (restrictPaperShading outer shading).mass)
    (hInner :
      (restrictPaperShading outer shading).mass ≤
        (8 : ENNReal) *
            (Nat.log 2 (2 * familyCard) + 1 : ENNReal) ^
              (scaleCount + 1) *
          (restrictPaperShading inner
            (restrictPaperShading outer shading)).mass) :
    shading.mass ≤
      ((packingConstant10000 : ENNReal) ^ scaleCount *
          (8 : ENNReal) *
          (Nat.log 2 (2 * familyCard) + 1 : ENNReal) ^
            (scaleCount + 1)) *
        (restrictPaperShading (outer.comp inner) shading).mass := by
  have hmass_eq :
      (restrictPaperShading inner
          (restrictPaperShading outer shading)).mass =
        (restrictPaperShading (outer.comp inner) shading).mass := by
    rw [restrictPaperShading_mass, restrictPaperShading_mass]
    apply Finset.sum_congr rfl
    intro index _
    rfl
  calc
    shading.mass
        ≤ (packingConstant10000 : ENNReal) ^ scaleCount *
            (restrictPaperShading outer shading).mass := hOuter
    _ ≤
        (packingConstant10000 : ENNReal) ^ scaleCount *
          ((8 : ENNReal) *
              (Nat.log 2 (2 * familyCard) + 1 : ENNReal) ^
                (scaleCount + 1) *
            (restrictPaperShading inner
              (restrictPaperShading outer shading)).mass) := by
      gcongr
    _ =
        ((packingConstant10000 : ENNReal) ^ scaleCount *
            (8 : ENNReal) *
            (Nat.log 2 (2 * familyCard) + 1 : ENNReal) ^
              (scaleCount + 1)) *
          (restrictPaperShading (outer.comp inner) shading).mass := by
      rw [hmass_eq]
      ring

/--
Restricting a paper shading to a tube subfamily cannot increase point
multiplicity: each selected index injects into the ambient index set.
-/
theorem restrictPaperShading_pointMultiplicity_le
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (shading : WZ1PaperTubeShading family)
    (point : Point3) :
    (restrictPaperShading selected shading).pointMultiplicity point ≤
      shading.pointMultiplicity point := by
  let selectedIndices : Finset (Fin selected.family.card) :=
    Finset.univ.filter fun index =>
      point ∈
        (restrictPaperShading selected shading).carrier index
  let ambientIndices : Finset (Fin family.card) :=
    Finset.univ.filter fun index =>
      point ∈ shading.carrier index
  have himage :
      Finset.image selected.embedding selectedIndices ⊆
        ambientIndices := by
    intro ambient hambient
    rcases Finset.mem_image.mp hambient with
      ⟨index, hindex, rfl⟩
    have hpoint :
        point ∈
          (restrictPaperShading selected shading).carrier index :=
      (Finset.mem_filter.mp hindex).2
    simpa [ambientIndices, restrictPaperShading] using hpoint
  have hcard :
      (Finset.image selected.embedding selectedIndices).card =
        selectedIndices.card := by
    rw [Finset.card_image_of_injective _ selected.embedding.injective]
  have hle :
      (Finset.image selected.embedding selectedIndices).card ≤
        ambientIndices.card :=
    Finset.card_le_card himage
  rw [hcard] at hle
  exact hle

/--
On one fixed indexed tube family, a pointwise subshading cannot increase
point multiplicity.
-/
theorem paperSubshading_pointMultiplicity_le
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (smaller larger : WZ1PaperTubeShading family)
    (hsub :
      ∀ index, smaller.carrier index ⊆ larger.carrier index)
    (point : Point3) :
    smaller.pointMultiplicity point ≤
      larger.pointMultiplicity point := by
  apply Finset.card_le_card
  intro index hindex
  rw [Finset.mem_filter] at hindex ⊢
  exact ⟨Finset.mem_univ index, hsub index hindex.2⟩

/--
A nonzero weighted lower cardinality bound forces the selected family to be
nonempty.
-/
theorem positive_card_from_retention
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (density retentionConstant : ENNReal)
    (hdensity_ne_zero : density ≠ 0)
    (hretention :
      density * family.enncard ≤
        retentionConstant * selected.family.enncard)
    (hretentionConstant_lt_top : retentionConstant ≠ ⊤)
    (hfamily_nonempty : 0 < family.card) :
    0 < selected.family.card := by
  by_contra h
  have h_zero : selected.family.card = 0 := by omega
  have h_enncard_zero : selected.family.enncard = 0 := by
    simp [Kakeya.Streamlined.TubeFamily.enncard, h_zero]
  have h_family_enncard_ne_zero : family.enncard ≠ 0 := by
    simp [Kakeya.Streamlined.TubeFamily.enncard,
      hfamily_nonempty] <;> omega
  have h_lhs_pos : 0 < density * family.enncard :=
    ENNReal.mul_pos hdensity_ne_zero h_family_enncard_ne_zero
  rw [h_enncard_zero] at hretention
  have h_rhs_zero :
      retentionConstant * (0 : ENNReal) = 0 := by simp
  rw [h_rhs_zero] at hretention
  exact not_le.mpr h_lhs_pos hretention

end Kakeya.Assouad
