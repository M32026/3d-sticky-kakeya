import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FiniteMaximalQuotientNet
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.RepresentativeParentCover

/-!
# One-scale quotient parents for the exact Proposition 6.5 rescaling

At one source Definition 2.12 scale, the exact triangular map supplies one
target representative axis above every complete source fiber.  Those axes
need not yet have the strong separation required by the public target cover.
This file first takes a maximal `callerRho / 4` net of the representative
axes.  Every target tube is assigned to the net center of its complete source
fiber.

No fine tube and no source complete fiber is deleted here.  In particular, a
quotient fiber is proved to be exactly a union of complete source fibers.  The
net centers have an absolute conflict degree at the public separation radius;
a later finite-schedule module can therefore make one simultaneous weighted
selection without paying a scale-dependent packing loss.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Absolute degree for the public `200 * callerRho` conflict graph on a
`callerRho / 4` representative-line net. -/
def pureWZ2AnisotropicQuotientCenterConflictDegree : ℕ :=
  (2 * 6400 + 1) ^ 5

/-- A maximal quotient of the representative target axes at one scale. -/
structure PureWZ2AnisotropicParentQuotientData
    {sourceDelta sourceRho targetDelta targetRho lineBound callerRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    (representative : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv) where
  caller_rho_pos : 0 < callerRho
  containment_budget :
    (3 / 2 : ℝ) * (lineBound + callerRho / 4) + targetDelta ≤ callerRho
  net : PureWZ2FiniteMaximalQuotientNetData
    sourceScale.coarse.card
    (fun first second =>
      wz1PaperLineDistance
        (targetFine.tube (representative.targetRepresentative first))
        (targetFine.tube (representative.targetRepresentative second)))
    (callerRho / 4)

namespace PureWZ2AnisotropicParentQuotientData

/-- The radius-`callerRho / 4` family used only for line packing. -/
def centerPackingFamily
    {sourceDelta sourceRho targetDelta targetRho lineBound callerRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {representative : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv}
    (data : PureWZ2AnisotropicParentQuotientData
      (callerRho := callerRho) representative) :
    Kakeya.Streamlined.TubeFamily (callerRho / 4) where
  card := data.net.centers.card
  tube center :=
    wz2PaperRelabelTube (targetScale := callerRho / 4)
      (targetFine.tube
        (representative.targetRepresentative
          (data.net.centerEmbedding center)))

/-- The ordinary target parents, with the same center axes and the public
caller radius. -/
def parentFamily
    {sourceDelta sourceRho targetDelta targetRho lineBound callerRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {representative : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv}
    (data : PureWZ2AnisotropicParentQuotientData
      (callerRho := callerRho) representative) :
    Kakeya.Streamlined.TubeFamily callerRho where
  card := data.net.centers.card
  tube center :=
    wz2PaperRelabelTube (targetScale := callerRho)
      (targetFine.tube
        (representative.targetRepresentative
          (data.net.centerEmbedding center)))

/-- Quotient-center ancestry of one target fine tube. -/
def assignedParent
    {sourceDelta sourceRho targetDelta targetRho lineBound callerRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {representative : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv}
    (data : PureWZ2AnisotropicParentQuotientData
      (callerRho := callerRho) representative)
    (target : Fin targetFine.card) : Fin data.parentFamily.card :=
  data.net.center (sourceScale.cover.parent (sourceEquiv target))

theorem centerPacking_line_class
    {sourceDelta sourceRho targetDelta targetRho lineBound callerRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {representative : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv}
    (data : PureWZ2AnisotropicParentQuotientData
      (callerRho := callerRho) representative) :
    WZ1PaperIsLineClass data.centerPackingFamily := by
  intro center
  exact wz2PaperRelabelTube_lineClass
    (representative.target_line_class
      (representative.targetRepresentative
        (data.net.centerEmbedding center)))

theorem parent_line_class
    {sourceDelta sourceRho targetDelta targetRho lineBound callerRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {representative : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv}
    (data : PureWZ2AnisotropicParentQuotientData
      (callerRho := callerRho) representative) :
    WZ1PaperIsLineClass data.parentFamily := by
  intro center
  exact wz2PaperRelabelTube_lineClass
    (representative.target_line_class
      (representative.targetRepresentative
        (data.net.centerEmbedding center)))

theorem centerPacking_lineDistance
    {sourceDelta sourceRho targetDelta targetRho lineBound callerRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {representative : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv}
    (data : PureWZ2AnisotropicParentQuotientData
      (callerRho := callerRho) representative)
    (first second : Fin data.centerPackingFamily.card) :
    wz1PaperLineDistance
        (data.centerPackingFamily.tube first)
        (data.centerPackingFamily.tube second) =
      wz1PaperLineDistance
        (targetFine.tube
          (representative.targetRepresentative
            (data.net.centerEmbedding first)))
        (targetFine.tube
          (representative.targetRepresentative
            (data.net.centerEmbedding second))) := by
  change wz1PaperLineDistance
      (wz2PaperRelabelTube
        (targetFine.tube
          (representative.targetRepresentative
            (data.net.centerEmbedding first))))
      (wz2PaperRelabelTube
        (targetFine.tube
          (representative.targetRepresentative
            (data.net.centerEmbedding second)))) = _
  rw [wz2PaperRelabelTube_lineDistance_both]

theorem parent_lineDistance
    {sourceDelta sourceRho targetDelta targetRho lineBound callerRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {representative : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv}
    (data : PureWZ2AnisotropicParentQuotientData
      (callerRho := callerRho) representative)
    (first second : Fin data.parentFamily.card) :
    wz1PaperLineDistance
        (data.parentFamily.tube first)
        (data.parentFamily.tube second) =
      wz1PaperLineDistance
        (targetFine.tube
          (representative.targetRepresentative
            (data.net.centerEmbedding first)))
        (targetFine.tube
          (representative.targetRepresentative
            (data.net.centerEmbedding second))) := by
  change wz1PaperLineDistance
      (wz2PaperRelabelTube
        (targetFine.tube
          (representative.targetRepresentative
            (data.net.centerEmbedding first))))
      (wz2PaperRelabelTube
        (targetFine.tube
          (representative.targetRepresentative
            (data.net.centerEmbedding second)))) = _
  rw [wz2PaperRelabelTube_lineDistance_both]

/-- The quotient packing centers inherit the maximal-net separation. -/
theorem centerPacking_distinct
    {sourceDelta sourceRho targetDelta targetRho lineBound callerRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {representative : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv}
    (data : PureWZ2AnisotropicParentQuotientData
      (callerRho := callerRho) representative) :
    WZ1PaperIsEssentiallyDistinct data.centerPackingFamily := by
  intro first second hne
  rw [data.centerPacking_lineDistance first second]
  exact data.net.centers_separated first second hne

/-- A target fine axis is close to the quotient center of its complete source
fiber: first move inside the source fiber, then move to the maximal-net
center. -/
theorem target_center_lineDistance_le
    {sourceDelta sourceRho targetDelta targetRho lineBound callerRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {representative : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv}
    (data : PureWZ2AnisotropicParentQuotientData
      (callerRho := callerRho) representative)
    (target : Fin targetFine.card) :
    wz1PaperLineDistance
        (targetFine.tube target)
        (targetFine.tube
          (representative.targetRepresentative
            (data.net.centerEmbedding (data.assignedParent target)))) ≤
      lineBound + callerRho / 4 := by
  let actual := sourceScale.cover.parent (sourceEquiv target)
  have hrepresentativeParent :
      sourceScale.cover.parent
          (sourceEquiv (representative.targetRepresentative actual)) =
        actual := by
    rw [PureWZ2RepresentativeParentCoverData.targetRepresentative,
      sourceEquiv.apply_symm_apply]
    exact representative.sourceRepresentative_parent actual
  have hwithin :
      wz1PaperLineDistance
          (targetFine.tube target)
          (targetFine.tube
            (representative.targetRepresentative actual)) ≤
        lineBound := by
    apply representative.common_source_parent_lineDistance
    exact hrepresentativeParent.symm
  have hcenter :
      wz1PaperLineDistance
          (targetFine.tube
            (representative.targetRepresentative actual))
          (targetFine.tube
            (representative.targetRepresentative
              (data.net.centerEmbedding (data.net.center actual)))) ≤
        callerRho / 4 :=
    data.net.center_close actual
  change wz1PaperLineDistance
      (targetFine.tube target)
      (targetFine.tube
        (representative.targetRepresentative
          (data.net.centerEmbedding (data.net.center actual)))) ≤ _
  exact (wz1PaperLineDistance_triangle _ _ _).trans
    (add_le_add hwithin hcenter)

/-- Every target tube is strictly contained in its quotient parent. -/
theorem assigned_containment
    {sourceDelta sourceRho targetDelta targetRho lineBound callerRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {representative : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv}
    (data : PureWZ2AnisotropicParentQuotientData
      (callerRho := callerRho) representative)
    (target : Fin targetFine.card) :
    (targetFine.tube target).carrier ⊆
      (data.parentFamily.tube (data.assignedParent target)).carrier := by
  have hresult := representative.target_carrier_subset_relabel
    data.caller_rho_pos target
    (representative.targetRepresentative
      (data.net.centerEmbedding (data.assignedParent target)))
    (show
        (3 / 2 : ℝ) *
            wz1PaperLineDistance
              (targetFine.tube target)
              (targetFine.tube
                (representative.targetRepresentative
                  (data.net.centerEmbedding
                    (data.assignedParent target)))) +
              targetDelta ≤ callerRho by
        calc
          (3 / 2 : ℝ) *
                wz1PaperLineDistance
                  (targetFine.tube target)
                  (targetFine.tube
                    (representative.targetRepresentative
                      (data.net.centerEmbedding
                        (data.assignedParent target)))) +
              targetDelta ≤
            (3 / 2 : ℝ) * (lineBound + callerRho / 4) +
              targetDelta := by
                gcongr
                exact data.target_center_lineDistance_le target
          _ ≤ callerRho := data.containment_budget)
  simpa only [parentFamily, assignedParent] using hresult

/-- Every quotient center is hit by a target representative, so the target
assignment is surjective without deleting any complete source fiber. -/
theorem assignedParent_surjective
    {sourceDelta sourceRho targetDelta targetRho lineBound callerRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {representative : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv}
    (data : PureWZ2AnisotropicParentQuotientData
      (callerRho := callerRho) representative) :
    Function.Surjective data.assignedParent := by
  intro center
  let actual := data.net.centerEmbedding center
  let target := representative.targetRepresentative actual
  refine ⟨target, ?_⟩
  change data.net.center
      (sourceScale.cover.parent (sourceEquiv target)) = center
  have hparent :
      sourceScale.cover.parent (sourceEquiv target) = actual := by
    dsimp only [target]
    rw [PureWZ2RepresentativeParentCoverData.targetRepresentative,
      sourceEquiv.apply_symm_apply]
    exact representative.sourceRepresentative_parent actual
  rw [hparent]
  exact data.net.center_fixed center

/-- Before the common center selection, the quotient gives an honest strict
assigned-parent cover. -/
noncomputable def toPreAssignedParentCover
    {sourceDelta sourceRho targetDelta targetRho lineBound callerRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {representative : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv}
    (data : PureWZ2AnisotropicParentQuotientData
      (callerRho := callerRho) representative) :
    PureWZ2LocalizedPreAssignedParentCoverData
      targetFine data.parentFamily where
  delta_pos := representative.target_delta_pos
  rho_pos := data.caller_rho_pos
  fine_line_class := representative.target_line_class
  coarse_line_class := data.parent_line_class
  fine_midpoint_local := representative.target_midpoint_local
  assignedParent := data.assignedParent
  assigned_containment := data.assigned_containment

/-- Source actual parents assigned to one quotient center. -/
def centerActualParents
    {sourceDelta sourceRho targetDelta targetRho lineBound callerRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {representative : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv}
    (data : PureWZ2AnisotropicParentQuotientData
      (callerRho := callerRho) representative)
    (center : Fin data.net.centers.card) :
    Finset (Fin sourceScale.coarse.card) :=
  Finset.univ.filter fun actual => data.net.center actual = center

/-- Target indices corresponding to one complete source actual fiber. -/
def targetActualFiber
    {sourceDelta sourceRho targetDelta targetRho lineBound callerRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {representative : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv}
    (_data : PureWZ2AnisotropicParentQuotientData
      (callerRho := callerRho) representative)
    (actual : Fin sourceScale.coarse.card) :
    Finset (Fin targetFine.card) :=
  Finset.univ.filter fun target =>
    sourceScale.cover.parent (sourceEquiv target) = actual

/-- A quotient assignment fiber is exactly the union of the complete source
fibers assigned to that center. -/
theorem assignedFiber_eq_actual_biUnion
    {sourceDelta sourceRho targetDelta targetRho lineBound callerRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {representative : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv}
    (data : PureWZ2AnisotropicParentQuotientData
      (callerRho := callerRho) representative)
    (center : Fin data.net.centers.card) :
    (Finset.univ : Finset (Fin targetFine.card)).filter
        (fun target => data.assignedParent target = center) =
      Finset.biUnion (data.centerActualParents center)
        data.targetActualFiber := by
  ext target
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_biUnion]
  constructor
  · intro hcenter
    let actual := sourceScale.cover.parent (sourceEquiv target)
    refine ⟨actual, ?_, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ actual, hcenter⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ target, rfl⟩
  · rintro ⟨actual, hactual, htarget⟩
    have hactualCenter : data.net.center actual = center :=
      (Finset.mem_filter.mp hactual).2
    have htargetActual :
        sourceScale.cover.parent (sourceEquiv target) = actual :=
      (Finset.mem_filter.mp htarget).2
    change data.net.center
      (sourceScale.cover.parent (sourceEquiv target)) = center
    rw [htargetActual, hactualCenter]

/-- A target actual-fiber packet is the exact image, under `sourceEquiv`, of
the corresponding complete source strict fiber. -/
theorem targetActualFiber_eq_source_image
    {sourceDelta sourceRho targetDelta targetRho lineBound callerRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {representative : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv}
    (data : PureWZ2AnisotropicParentQuotientData
      (callerRho := callerRho) representative)
    (actual : Fin sourceScale.coarse.card) :
    Finset.image sourceEquiv (data.targetActualFiber actual) =
      wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceScale.coarse actual := by
  ext source
  constructor
  · intro hsource
    rcases Finset.mem_image.mp hsource with ⟨target, htarget, rfl⟩
    rw [sourceScale.cover.mem_fullFiber_iff_parent_eq
      sourceScale.rho_pos.le]
    exact (Finset.mem_filter.mp htarget).2
  · intro hsource
    let target := sourceEquiv.symm source
    refine Finset.mem_image.mpr ⟨target, ?_, sourceEquiv.apply_symm_apply source⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ target, by
        rw [sourceEquiv.apply_symm_apply]
        exact (sourceScale.cover.mem_fullFiber_iff_parent_eq
          sourceScale.rho_pos.le actual source).mp hsource⟩

/-- One target actual-fiber packet has exactly the source complete-fiber
cardinality. -/
theorem targetActualFiber_card_eq_source
    {sourceDelta sourceRho targetDelta targetRho lineBound callerRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {representative : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv}
    (data : PureWZ2AnisotropicParentQuotientData
      (callerRho := callerRho) representative)
    (actual : Fin sourceScale.coarse.card) :
    (data.targetActualFiber actual).card =
      (wz2PaperOrdinaryFullFiberIndices
        sourceFine sourceScale.coarse actual).card := by
  rw [← data.targetActualFiber_eq_source_image actual]
  exact Finset.card_image_of_injective _ sourceEquiv.injective |>.symm

/-- The conflict graph of quotient centers has an absolute degree, independent
of the ratio between the source parent scale and the target fine scale. -/
theorem centerConflict_degree
    {sourceDelta sourceRho targetDelta targetRho lineBound callerRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {representative : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv}
    (data : PureWZ2AnisotropicParentQuotientData
      (callerRho := callerRho) representative)
    (fixed : Fin data.centerPackingFamily.card) :
    ((Finset.univ : Finset (Fin data.centerPackingFamily.card)).filter
      (fun other =>
        wz1PaperLineDistance
            (data.centerPackingFamily.tube other)
            (data.centerPackingFamily.tube fixed) ≤
          2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant *
            callerRho)).card ≤
      pureWZ2AnisotropicQuotientCenterConflictDegree := by
  have hpacking := tube_packing_bound_general
    data.centerPacking_distinct data.centerPacking_line_class
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

end PureWZ2AnisotropicParentQuotientData

/-- Construct the one-scale maximal quotient net of target representative
axes. -/
theorem pureWZ2_anisotropic_parent_quotient
    {sourceDelta sourceRho targetDelta targetRho lineBound callerRho : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceConstant : ENNReal}
    {sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    (representative : PureWZ2RepresentativeParentCoverData
      (targetRho := targetRho) (lineBound := lineBound)
      sourceScale targetFine sourceEquiv)
    (hcallerRho : 0 < callerRho)
    (hcontainment :
      (3 / 2 : ℝ) * (lineBound + callerRho / 4) + targetDelta ≤
        callerRho) :
    Nonempty (PureWZ2AnisotropicParentQuotientData
      (callerRho := callerRho) representative) := by
  let distance :
      Fin sourceScale.coarse.card →
        Fin sourceScale.coarse.card → ℝ := fun first second =>
    wz1PaperLineDistance
      (targetFine.tube (representative.targetRepresentative first))
      (targetFine.tube (representative.targetRepresentative second))
  have distanceSymmetric :
      ∀ first second, distance first second = distance second first :=
    fun first second => wz1PaperLineDistance_symm _ _
  have distanceSelf : ∀ parent, distance parent parent = 0 := by
    intro parent
    have hdirection :
        wz1PaperDirection
            (targetFine.tube
              (representative.targetRepresentative parent)) ≠ 0 := by
      intro hzero
      have hnorm := wz1PaperDirection_norm
        (targetFine.tube (representative.targetRepresentative parent))
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm
    simp [distance, wz1PaperLineDistance,
      InnerProductGeometry.angle_self hdirection]
  have parentCountPos : 0 < sourceScale.coarse.card := by
    let source : Fin sourceFine.card := ⟨0, representative.source_nonempty⟩
    rcases sourceScale.cover.covers source with ⟨parent, _⟩
    exact lt_of_le_of_lt (Nat.zero_le parent.val) parent.isLt
  rcases pureWZ2_finite_maximal_quotient_net
      sourceScale.coarse.card parentCountPos distance
      distanceSymmetric distanceSelf (callerRho / 4)
      (by positivity) with
    ⟨net⟩
  exact ⟨{
    caller_rho_pos := hcallerRho
    containment_budget := hcontainment
    net := net
  }⟩

end Kakeya.Assouad

end
