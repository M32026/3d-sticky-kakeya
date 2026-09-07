import MyLeanRepo.Kakeya.Assouad.PureWZ2.FiniteMaximalQuotientNet
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingParentCover

/-!
# Quotient parents for Proposition 6.3 mild rescaling

Actual source parents can repeat or cluster on nearly identical supporting
lines, so selecting them directly pays a scale-dependent conflict degree.
This module first takes a maximal net of the corresponding target
representative axes.  Every actual source fiber is assigned to its net center
and remains whole.  The resulting center conflict graph has an absolute
degree, independent of `sourceRho / sourceDelta`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

attribute [local instance] Classical.propDecidable

/-- Absolute degree for the public doubled-fiber conflict graph on a
`callerRho / 4`-separated target-line net. -/
def proposition63MildRescalingQuotientConflictDegree : ℕ :=
  (2 * 6400 + 1) ^ 5

/-- Radius of the quotient parent attached to one source nearby scale. -/
def proposition63MildRescalingQuotientRho
    (sourceDelta sourceRho scale : ℝ) : ℝ :=
  5200000 * scale * sourceRho + 4 * scale * sourceDelta

theorem proposition63MildRescalingQuotientRho_pos
    {sourceDelta sourceRho scale : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceRho : 0 < sourceRho)
    (hscale : 1 ≤ scale) :
    0 < proposition63MildRescalingQuotientRho
      sourceDelta sourceRho scale := by
  unfold proposition63MildRescalingQuotientRho
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  nlinarith

theorem proposition63MildRescalingQuotientRho_containment
    {sourceDelta sourceRho scale : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceRho : 0 < sourceRho)
    (hscale : 1 ≤ scale) :
    (3 / 2 : ℝ) *
          (1300000 * scale * sourceRho +
            proposition63MildRescalingQuotientRho
              sourceDelta sourceRho scale / 4) +
        scale * sourceDelta ≤
      proposition63MildRescalingQuotientRho
        sourceDelta sourceRho scale := by
  unfold proposition63MildRescalingQuotientRho
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  have hscaledDelta : 0 ≤ scale * sourceDelta := by positivity
  have hscaledRho : 0 ≤ scale * sourceRho := by positivity
  nlinarith

/-- One maximal quotient of the target representatives arising from an
actual source Definition 2.12 scale. -/
structure Proposition63MildRescalingQuotientParentData
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho : ℝ}
    (representative : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho)
    (callerRho : ℝ) where
  caller_rho_pos : 0 < callerRho
  containment_budget :
    (3 / 2 : ℝ) *
          (1300000 * scale * sourceRho + callerRho / 4) +
        scale * sourceDelta ≤ callerRho
  net : WZ2FiniteMaximalQuotientNetData
    sourceScale.coarse.card
    (fun first second =>
      wz1PaperLineDistance
        ((proposition63MildRescalingFamily hscale raw).tube
          (representative.sourceRepresentative first))
        ((proposition63MildRescalingFamily hscale raw).tube
          (representative.sourceRepresentative second)))
    (callerRho / 4)

namespace Proposition63MildRescalingQuotientParentData

/-- Radius-`callerRho / 4` family used only for target-line packing. -/
def centerPackingFamily
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho callerRho : ℝ}
    {representative : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho}
    (data : Proposition63MildRescalingQuotientParentData
      representative callerRho) :
    Kakeya.Streamlined.TubeFamily (callerRho / 4) where
  card := data.net.centers.card
  tube parent :=
    wz2PaperRelabelTube (targetScale := callerRho / 4)
      ((proposition63MildRescalingFamily hscale raw).tube
        (representative.sourceRepresentative
          (data.net.centerEmbedding parent)))

/-- Public quotient parents on the same center axes. -/
def parentFamily
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho callerRho : ℝ}
    {representative : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho}
    (data : Proposition63MildRescalingQuotientParentData
      representative callerRho) :
    Kakeya.Streamlined.TubeFamily callerRho where
  card := data.net.centers.card
  tube parent :=
    wz2PaperRelabelTube (targetScale := callerRho)
      ((proposition63MildRescalingFamily hscale raw).tube
        (representative.sourceRepresentative
          (data.net.centerEmbedding parent)))

/-- Quotient-center ancestry of one target fine tube. -/
def assignedParent
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho callerRho : ℝ}
    {representative : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho}
    (data : Proposition63MildRescalingQuotientParentData
      representative callerRho)
    (target : Fin sourceFine.card) : Fin data.parentFamily.card :=
  data.net.center (sourceScale.cover.parent target)

theorem centerPacking_lineClass
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho callerRho : ℝ}
    {representative : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho}
    (data : Proposition63MildRescalingQuotientParentData
      representative callerRho) :
    WZ1PaperIsLineClass data.centerPackingFamily := by
  intro parent
  exact wz2PaperRelabelTube_lineClass
    (proposition63MildRescalingFamily_lineClass
      hscale raw representative.raw_line_class _)

theorem centerPacking_lineDistance
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho callerRho : ℝ}
    {representative : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho}
    (data : Proposition63MildRescalingQuotientParentData
      representative callerRho)
    (first second : Fin data.centerPackingFamily.card) :
    wz1PaperLineDistance
        (data.centerPackingFamily.tube first)
        (data.centerPackingFamily.tube second) =
      wz1PaperLineDistance
        ((proposition63MildRescalingFamily hscale raw).tube
          (representative.sourceRepresentative
            (data.net.centerEmbedding first)))
        ((proposition63MildRescalingFamily hscale raw).tube
          (representative.sourceRepresentative
            (data.net.centerEmbedding second))) := by
  change wz1PaperLineDistance (wz2PaperRelabelTube _)
      (wz2PaperRelabelTube _) = _
  rw [wz2PaperRelabelTube_lineDistance_both]

theorem parent_lineDistance
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho callerRho : ℝ}
    {representative : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho}
    (data : Proposition63MildRescalingQuotientParentData
      representative callerRho)
    (first second : Fin data.parentFamily.card) :
    wz1PaperLineDistance
        (data.parentFamily.tube first)
        (data.parentFamily.tube second) =
      wz1PaperLineDistance
        ((proposition63MildRescalingFamily hscale raw).tube
          (representative.sourceRepresentative
            (data.net.centerEmbedding first)))
        ((proposition63MildRescalingFamily hscale raw).tube
          (representative.sourceRepresentative
            (data.net.centerEmbedding second))) := by
  change wz1PaperLineDistance (wz2PaperRelabelTube _)
      (wz2PaperRelabelTube _) = _
  rw [wz2PaperRelabelTube_lineDistance_both]

theorem centerPacking_distinct
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho callerRho : ℝ}
    {representative : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho}
    (data : Proposition63MildRescalingQuotientParentData
      representative callerRho) :
    WZ1PaperIsEssentiallyDistinct data.centerPackingFamily := by
  intro first second hne
  rw [data.centerPacking_lineDistance first second]
  exact data.net.centers_separated first second hne

/-- The public parent family has the same supporting lines as the packing
family. -/
theorem parent_lineDistance_eq_centerPacking
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho callerRho : ℝ}
    {representative : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho}
    (data : Proposition63MildRescalingQuotientParentData
      representative callerRho)
    (first second : Fin data.parentFamily.card) :
    wz1PaperLineDistance
        (data.parentFamily.tube first)
        (data.parentFamily.tube second) =
      wz1PaperLineDistance
        (data.centerPackingFamily.tube first)
        (data.centerPackingFamily.tube second) := by
  rw [data.parent_lineDistance, data.centerPacking_lineDistance]

/-- Distinct quotient parents are separated at the net radius. -/
theorem parent_stronglySeparated
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho callerRho : ℝ}
    {representative : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho}
    (data : Proposition63MildRescalingQuotientParentData
      representative callerRho)
    (first second : Fin data.parentFamily.card)
    (hne : first ≠ second) :
    callerRho / 4 <
      wz1PaperLineDistance
        (data.parentFamily.tube first)
        (data.parentFamily.tube second) := by
  rw [data.parent_lineDistance_eq_centerPacking first second]
  exact data.centerPacking_distinct first second hne

theorem parent_lineClass
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho callerRho : ℝ}
    {representative : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho}
    (data : Proposition63MildRescalingQuotientParentData
      representative callerRho) :
    WZ1PaperIsLineClass data.parentFamily := by
  intro parent
  exact wz2PaperRelabelTube_lineClass
    (proposition63MildRescalingFamily_lineClass
      hscale raw representative.raw_line_class _)

theorem target_center_lineDistance_le
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho callerRho : ℝ}
    {representative : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho}
    (data : Proposition63MildRescalingQuotientParentData
      representative callerRho)
    (target : Fin sourceFine.card) :
    wz1PaperLineDistance
        ((proposition63MildRescalingFamily hscale raw).tube target)
        ((proposition63MildRescalingFamily hscale raw).tube
          (representative.sourceRepresentative
            (data.net.centerEmbedding (data.assignedParent target)))) ≤
      1300000 * scale * sourceRho + callerRho / 4 := by
  let actual := sourceScale.cover.parent target
  have hwithin :
      wz1PaperLineDistance
          ((proposition63MildRescalingFamily hscale raw).tube target)
          ((proposition63MildRescalingFamily hscale raw).tube
            (representative.sourceRepresentative actual)) ≤
        1300000 * scale * sourceRho := by
    apply representative.common_source_parent_lineDistance
    exact (representative.sourceRepresentative_parent actual).symm
  have hcenter :
      wz1PaperLineDistance
          ((proposition63MildRescalingFamily hscale raw).tube
            (representative.sourceRepresentative actual))
          ((proposition63MildRescalingFamily hscale raw).tube
            (representative.sourceRepresentative
              (data.net.centerEmbedding (data.net.center actual)))) ≤
        callerRho / 4 :=
    data.net.center_close actual
  change wz1PaperLineDistance _
      ((proposition63MildRescalingFamily hscale raw).tube
        (representative.sourceRepresentative
          (data.net.centerEmbedding (data.net.center actual)))) ≤ _
  exact (wz1PaperLineDistance_triangle _ _ _).trans
    (add_le_add hwithin hcenter)

theorem assigned_containment
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho callerRho : ℝ}
    {representative : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho}
    (data : Proposition63MildRescalingQuotientParentData
      representative callerRho)
    (target : Fin sourceFine.card) :
    ((proposition63MildRescalingFamily hscale raw).tube target).carrier ⊆
      (data.parentFamily.tube (data.assignedParent target)).carrier := by
  have hcontain := representative.target_carrier_subset_relabel_of_lineDistance
    data.caller_rho_pos target
    (representative.sourceRepresentative
      (data.net.centerEmbedding (data.assignedParent target)))
    (show
      (3 / 2 : ℝ) *
          wz1PaperLineDistance
            ((proposition63MildRescalingFamily hscale raw).tube target)
            ((proposition63MildRescalingFamily hscale raw).tube
              (representative.sourceRepresentative
                (data.net.centerEmbedding (data.assignedParent target)))) +
        scale * sourceDelta ≤ callerRho by
      calc
        (3 / 2 : ℝ) * wz1PaperLineDistance _ _ +
              scale * sourceDelta ≤
            (3 / 2 : ℝ) *
                (1300000 * scale * sourceRho + callerRho / 4) +
              scale * sourceDelta := by
          gcongr
          exact data.target_center_lineDistance_le target
        _ ≤ callerRho := data.containment_budget)
  simpa only [parentFamily] using hcontain

theorem assignedParent_surjective
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho callerRho : ℝ}
    {representative : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho}
    (data : Proposition63MildRescalingQuotientParentData
      representative callerRho) :
    Function.Surjective data.assignedParent := by
  intro quotientParent
  let actual := data.net.centerEmbedding quotientParent
  let target := representative.sourceRepresentative actual
  refine ⟨target, ?_⟩
  change data.net.center (sourceScale.cover.parent target) = quotientParent
  rw [representative.sourceRepresentative_parent actual]
  exact data.net.center_fixed quotientParent

/-- A selected target family, its hit quotient parents, and the exact ambient
parent-map compatibility. -/
structure Proposition63MildRescalingSelectedQuotientCoverData
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho callerRho : ℝ}
    {representative : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho}
    (quotient : Proposition63MildRescalingQuotientParentData
      representative callerRho)
    (selected : WZ2PaperPureTubeSubfamily
      (proposition63MildRescalingFamily hscale raw)) where
  selectedParents : WZ2PaperPureTubeSubfamily quotient.parentFamily
  cover : WZ2PaperPurePartitioningCover
    selected.family selectedParents.family
  parent_ambient : ∀ target,
    selectedParents.embedding (cover.parent target) =
      quotient.assignedParent (selected.embedding target)

/-- Restrict a quotient assignment to arbitrary selected target indices and
its hit quotient centers.  A separation certificate on those hit centers is
exactly what is needed for the literal doubled-fiber disjointness clause. -/
theorem restrictToSeparatedHitParents
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho callerRho : ℝ}
    {representative : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho}
    (data : Proposition63MildRescalingQuotientParentData
      representative callerRho)
    (selected : WZ2PaperPureTubeSubfamily
      (proposition63MildRescalingFamily hscale raw))
    (hseparated : ∀ first second : Fin data.parentFamily.card,
      first ≠ second →
      (∃ target : Fin selected.family.card,
        data.assignedParent (selected.embedding target) = first) →
      (∃ target : Fin selected.family.card,
        data.assignedParent (selected.embedding target) = second) →
        2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant * callerRho <
          wz1PaperLineDistance
            (data.parentFamily.tube first)
            (data.parentFamily.tube second)) :
    Nonempty (Proposition63MildRescalingSelectedQuotientCoverData
      data selected) := by
  let parentImage : Finset (Fin data.parentFamily.card) :=
    Finset.univ.image fun target : Fin selected.family.card =>
      data.assignedParent (selected.embedding target)
  let selectedParents : WZ2PaperPureTubeSubfamily data.parentFamily :=
    WZ2PaperPureTubeSubfamily.fromFinset data.parentFamily parentImage
  let parentEquiv : Fin parentImage.card ≃ parentImage :=
    (parentImage.orderIsoOfFin rfl).toEquiv
  have parentMem : ∀ target : Fin selected.family.card,
      data.assignedParent (selected.embedding target) ∈ parentImage := by
    intro target
    exact Finset.mem_image.mpr ⟨target, Finset.mem_univ target, rfl⟩
  let parent : Fin selected.family.card → Fin selectedParents.family.card :=
    fun target => parentEquiv.symm
      ⟨data.assignedParent (selected.embedding target), parentMem target⟩
  have parentAmbient : ∀ target,
      selectedParents.embedding (parent target) =
        data.assignedParent (selected.embedding target) := by
    intro target
    exact congrArg Subtype.val
      (parentEquiv.apply_symm_apply
        ⟨data.assignedParent (selected.embedding target), parentMem target⟩)
  have parentSurjective : Function.Surjective parent := by
    intro selectedParent
    have ambientMem : selectedParents.embedding selectedParent ∈ parentImage :=
      Finset.orderEmbOfFin_mem parentImage rfl selectedParent
    rcases Finset.mem_image.mp ambientMem with ⟨target, _, htarget⟩
    refine ⟨target, ?_⟩
    apply selectedParents.embedding.injective
    rw [parentAmbient, htarget]
  have doubledDisjoint : ∀ first second, first ≠ second →
      Disjoint
        (wz2PaperOrdinaryDilatedFiberIndices
          2 selected.family selectedParents.family first)
        (wz2PaperOrdinaryDilatedFiberIndices
          2 selected.family selectedParents.family second) := by
    apply wz2_paper_localized_ordinary_dilatedFiberIndices_disjoint
      (mul_pos (lt_of_lt_of_le zero_lt_one hscale) sourceScale.delta_pos)
      data.caller_rho_pos
      ((proposition63MildRescalingFamily_lineClass
        hscale raw representative.raw_line_class).subfamily
          selected.toTubeSubfamily)
      (data.parent_lineClass.subfamily selectedParents.toTubeSubfamily)
      (fun target => by
        change ‖wz2PaperTubeMidpoint (selected.family.tube target)‖ ≤ 3
        rw [selected.tube_eq]
        exact proposition63MildRescalingFamily_midpoint_local
          hscale raw representative.raw_line_class _)
    intro first second hne
    have ambientNe : selectedParents.embedding first ≠
        selectedParents.embedding second :=
      selectedParents.embedding.injective.ne hne
    have firstMem : selectedParents.embedding first ∈ parentImage :=
      Finset.orderEmbOfFin_mem parentImage rfl first
    have secondMem : selectedParents.embedding second ∈ parentImage :=
      Finset.orderEmbOfFin_mem parentImage rfl second
    rcases Finset.mem_image.mp firstMem with ⟨firstTarget, _, hfirst⟩
    rcases Finset.mem_image.mp secondMem with ⟨secondTarget, _, hsecond⟩
    change 2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant * callerRho <
      wz1PaperLineDistance
        (selectedParents.family.tube first)
        (selectedParents.family.tube second)
    rw [selectedParents.tube_eq, selectedParents.tube_eq]
    exact hseparated _ _ ambientNe
      ⟨firstTarget, hfirst⟩ ⟨secondTarget, hsecond⟩
  let cover : WZ2PaperPurePartitioningCover
      selected.family selectedParents.family := {
    covers := fun target => ⟨parent target, by
      rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
      rw [selected.tube_eq, selectedParents.tube_eq, parentAmbient]
      exact data.assigned_containment (selected.embedding target)⟩
    doubled_fibers_disjoint := doubledDisjoint
    }
  exact ⟨{
    selectedParents := selectedParents
    cover := cover
    parent_ambient := by
      intro target
      have hcoverParent : cover.parent target = parent target := by
        apply cover.fullFiber_parent_unique data.caller_rho_pos.le
        · exact cover.parent_mem_fullFiber target
        · rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
          rw [selected.tube_eq, selectedParents.tube_eq, parentAmbient]
          exact data.assigned_containment (selected.embedding target)
      rw [hcoverParent]
      exact parentAmbient target
  }⟩

/-- The quotient assignment together with strong center separation is a
literal Definition 2.12 partitioning cover. -/
theorem toPartitioningCover
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho callerRho : ℝ}
    {representative : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho}
    (data : Proposition63MildRescalingQuotientParentData
      representative callerRho)
    (hseparated : ∀ first second : Fin data.parentFamily.card,
      first ≠ second →
        2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant * callerRho <
          wz1PaperLineDistance
            (data.parentFamily.tube first)
            (data.parentFamily.tube second)) :
    WZ2PaperPurePartitioningCover
      (proposition63MildRescalingFamily hscale raw) data.parentFamily where
  covers target := by
    refine ⟨data.assignedParent target, ?_⟩
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    exact data.assigned_containment target
  doubled_fibers_disjoint :=
    wz2_paper_localized_ordinary_dilatedFiberIndices_disjoint
      (mul_pos (lt_of_lt_of_le zero_lt_one hscale) sourceScale.delta_pos)
      data.caller_rho_pos
      (proposition63MildRescalingFamily_lineClass
        hscale raw representative.raw_line_class)
      data.parent_lineClass
      (proposition63MildRescalingFamily_midpoint_local
        hscale raw representative.raw_line_class)
      hseparated

theorem centerConflict_degree
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho callerRho : ℝ}
    {representative : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho}
    (data : Proposition63MildRescalingQuotientParentData
      representative callerRho)
    (fixed : Fin data.centerPackingFamily.card) :
    ((Finset.univ : Finset (Fin data.centerPackingFamily.card)).filter
      (fun other =>
        wz1PaperLineDistance
            (data.centerPackingFamily.tube other)
            (data.centerPackingFamily.tube fixed) ≤
          2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
            callerRho)).card ≤
      proposition63MildRescalingQuotientConflictDegree := by
  have hpacking := tube_packing_bound_general
    data.centerPacking_distinct data.centerPacking_lineClass
    (by nlinarith [data.caller_rho_pos] : 0 < callerRho / 4)
    (2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant * callerRho)
    (by
      unfold wz2PaperLocalizedDoubledFiberLineDistanceConstant
      nlinarith [data.caller_rho_pos])
    fixed
  have hceil :
      Nat.ceil
          (8 *
            (2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
              callerRho) /
            (callerRho / 4)) =
        6400 := by
    have halgebra :
        8 *
            (2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
              callerRho) /
            (callerRho / 4) =
          (6400 : ℝ) := by
      unfold wz2PaperLocalizedDoubledFiberLineDistanceConstant
      field_simp [data.caller_rho_pos.ne']
      ring
    rw [halgebra]
    norm_num
  rw [hceil] at hpacking
  exact hpacking

/-- The same absolute degree bound stated on public quotient parents. -/
theorem parentConflict_degree
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho callerRho : ℝ}
    {representative : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho}
    (data : Proposition63MildRescalingQuotientParentData
      representative callerRho)
    (fixed : Fin data.parentFamily.card) :
    ((Finset.univ : Finset (Fin data.parentFamily.card)).filter
      (fun other =>
        wz1PaperLineDistance
            (data.parentFamily.tube fixed)
            (data.parentFamily.tube other) ≤
          2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
            callerRho)).card ≤
      proposition63MildRescalingQuotientConflictDegree := by
  change Fin data.net.centers.card at fixed
  have hbound := data.centerConflict_degree fixed
  change
    ((Finset.univ : Finset (Fin data.net.centers.card)).filter
      (fun other =>
        wz1PaperLineDistance
            (data.parentFamily.tube fixed)
            (data.parentFamily.tube other) ≤
          2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
            callerRho)).card ≤
      proposition63MildRescalingQuotientConflictDegree
  have hfilter :
      (Finset.univ : Finset (Fin data.net.centers.card)).filter
          (fun other =>
            wz1PaperLineDistance
                (data.parentFamily.tube fixed)
                (data.parentFamily.tube other) ≤
              2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
                callerRho) =
        (Finset.univ : Finset (Fin data.net.centers.card)).filter
          (fun other =>
            wz1PaperLineDistance
                (data.centerPackingFamily.tube other)
                (data.centerPackingFamily.tube fixed) ≤
              2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
                callerRho) := by
    apply Finset.filter_congr
    intro other _
    rw [data.parent_lineDistance_eq_centerPacking fixed other]
    exact ⟨fun h => by rwa [wz1PaperLineDistance_symm],
      fun h => by rwa [wz1PaperLineDistance_symm] at h⟩
  rw [hfilter]
  exact hbound

end Proposition63MildRescalingQuotientParentData

/-- Construct the maximal target-line quotient at one source actual scale. -/
theorem proposition63_mild_rescaling_quotient_parent
    {sourceDelta sourceRho scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {targetRho : ℝ}
    (representative : Proposition63MildRescalingParentCoverData
      sourceScale hscale raw targetRho) :
    Nonempty (Proposition63MildRescalingQuotientParentData representative
      (proposition63MildRescalingQuotientRho
        sourceDelta sourceRho scale)) := by
  let distance :
      Fin sourceScale.coarse.card →
        Fin sourceScale.coarse.card → ℝ := fun first second =>
    wz1PaperLineDistance
      ((proposition63MildRescalingFamily hscale raw).tube
        (representative.sourceRepresentative first))
      ((proposition63MildRescalingFamily hscale raw).tube
        (representative.sourceRepresentative second))
  have distanceSymmetric :
      ∀ first second, distance first second = distance second first :=
    fun first second => wz1PaperLineDistance_symm _ _
  have distanceSelf : ∀ parent, distance parent parent = 0 := by
    intro parent
    have hdirection :
        wz1PaperDirection
            ((proposition63MildRescalingFamily hscale raw).tube
              (representative.sourceRepresentative parent)) ≠ 0 := by
      intro hzero
      have hnorm := wz1PaperDirection_norm
        ((proposition63MildRescalingFamily hscale raw).tube
          (representative.sourceRepresentative parent))
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm
    simp [distance, wz1PaperLineDistance,
      InnerProductGeometry.angle_self hdirection]
  have parentCountPos : 0 < sourceScale.coarse.card := by
    let source : Fin sourceFine.card :=
      ⟨0, representative.source_nonempty⟩
    rcases sourceScale.cover.covers source with ⟨parent, _⟩
    exact lt_of_le_of_lt (Nat.zero_le parent.val) parent.isLt
  let callerRho := proposition63MildRescalingQuotientRho
    sourceDelta sourceRho scale
  have callerRhoPos : 0 < callerRho :=
    proposition63MildRescalingQuotientRho_pos
      sourceScale.delta_pos sourceScale.rho_pos hscale
  rcases wz2_finite_maximal_quotient_net
      sourceScale.coarse.card parentCountPos distance
      distanceSymmetric distanceSelf (callerRho / 4)
      (by positivity) with
    ⟨net⟩
  exact ⟨{
    caller_rho_pos := callerRhoPos
    containment_budget :=
      proposition63MildRescalingQuotientRho_containment
        sourceScale.delta_pos sourceScale.rho_pos hscale
    net := net
  }⟩

end Kakeya.Assouad.PureWZ2

end
