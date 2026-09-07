import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RootNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.MultiplicityPreservingVariation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WeakLipschitzPlaneMapRefinement

/-!
# A fixed plane map on the finite-iteration root

The preliminary Lemma 4.12 iteration starts only after a weak plane map has
been constructed and made Lipschitz.  Current-shading re-entry changes the
tube family by a genuine subfamily selection and then dense-cubicalizes its
ordinary trace.  This module restricts the already chosen map through those
two operations and packages it with the exact resulting root normalization.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- A root normalization equipped with the fixed map used by every coordinate
of the subsequent finite dependent iteration. -/
structure Proposition63RootPlaneMapData
    {delta sigma initialInputLoss normalizationLoss reentryLoss densityLoss
      incidence : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (coefficient : NNReal) where
  root : Proposition63RootNormalizationData
    (outputLoss := reentry.reentryNormalizationLoss)
    reentry.ordinarySource normalizationExponent densityLoss
  planeMap : PaperWZ1WeakPlaneMapData
    root.normalization.croppedRefined incidence
  lipschitz : LipschitzWith coefficient
    (fun point : {point : Point3 //
      point ∈ root.normalization.croppedRefined.union} =>
        planeMap.planeMap point)
  cellwise : ∀ first second,
    wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
      planeMap.planeMap first = planeMap.planeMap second

/-- Enlarge only the recorded Lipschitz constant.  The root, plane map,
incidence bound, and coarse-cell constancy remain definitionally unchanged. -/
noncomputable def Proposition63RootPlaneMapData.weakenLipschitz
    {delta sigma initialInputLoss normalizationLoss reentryLoss densityLoss
      incidence : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    {sourceCoefficient targetCoefficient : NNReal}
    {reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current}
    (data : Proposition63RootPlaneMapData
      (densityLoss := densityLoss) (incidence := incidence)
      reentry sourceCoefficient)
    (hle : sourceCoefficient ≤ targetCoefficient) :
    Proposition63RootPlaneMapData
      (densityLoss := densityLoss) (incidence := incidence)
      reentry targetCoefficient where
  root := data.root
  planeMap := data.planeMap
  lipschitz := data.lipschitz.weaken hle
  cellwise := data.cellwise

/-- Restrict one fixed current-shading map through the exact normalization
chosen by current re-entry.  This transparent constructor exposes the
definitional identity of its root normalization to downstream provenance
transports; no new map is selected. -/
noncomputable def Proposition63RootPlaneMapData.ofCurrentReentry
    {delta sigma initialInputLoss normalizationLoss reentryLoss densityLoss
      incidence : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (coefficient : NNReal)
    (current_lipschitz : LipschitzWith coefficient
      (fun point : {point : Point3 // point ∈ current.union} =>
        currentMap.planeMap point))
    (current_cellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        currentMap.planeMap first = currentMap.planeMap second)
    (density_absorb :
      Kakeya.realRpowENN delta densityLoss ≤
        Kakeya.realRpowENN delta reentryLoss / 2) :
    Proposition63RootPlaneMapData
      (densityLoss := densityLoss) (incidence := incidence)
      reentry coefficient := by
  let root : Proposition63RootNormalizationData
      (outputLoss := reentry.reentryNormalizationLoss)
      reentry.ordinarySource normalizationExponent densityLoss :=
    Proposition63RootNormalizationData.ofNormalization
      reentry.normalization density_absorb
  let selectedMap : PaperWZ1WeakPlaneMapData
      (restrictPaperShading reentry.regularized.selected current) incidence :=
    Kakeya.Assouad.PureWZ2.PaperWZ1WeakPlaneMapData.restrictSubfamily
      currentMap reentry.regularized.selected
  let rootMap : PaperWZ1WeakPlaneMapData
      root.normalization.croppedRefined incidence :=
    paperWeakPlaneMapRestrict selectedMap reentry.denseSubshading
  have root_union_subset : root.normalization.croppedRefined.union ⊆
      current.union := by
    simpa only [root, Proposition63RootNormalizationData.ofNormalization]
      using reentry.normalization_croppedRefined_union_subset_current
  refine {
    root := root
    planeMap := rootMap
    lipschitz := ?_
    cellwise := ?_
  }
  · apply LipschitzWith.of_dist_le_mul
    intro first second
    simpa only [rootMap, selectedMap,
      PaperWZ1WeakPlaneMapData.restrictSubfamily,
      paperWeakPlaneMapRestrict, Subtype.dist_eq] using
        current_lipschitz.dist_le_mul
          ⟨first, root_union_subset first.prop⟩
          ⟨second, root_union_subset second.prop⟩
  · intro first second same_cell
    simpa only [rootMap, selectedMap,
      PaperWZ1WeakPlaneMapData.restrictSubfamily,
      paperWeakPlaneMapRestrict] using
        current_cellwise first second same_cell

/-- A strict axial certificate on the incoming ordinary normalization survives
the canonical current-reentry root-map constructor. -/
theorem Proposition63RootPlaneMapData.ofCurrentReentry_axialWindow
    {delta sigma initialInputLoss normalizationLoss reentryLoss densityLoss
      incidence bound : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (coefficient : NNReal)
    (current_lipschitz : LipschitzWith coefficient
      (fun point : {point : Point3 // point ∈ current.union} =>
        currentMap.planeMap point))
    (current_cellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        currentMap.planeMap first = currentMap.planeMap second)
    (density_absorb :
      Kakeya.realRpowENN delta densityLoss ≤
        Kakeya.realRpowENN delta reentryLoss / 2)
    (initialAxialWindow : ∀ index point,
      point ∈ initialNormalized.frame ''
          initialNormalized.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ bound) :
    let rootMap :=
      Proposition63RootPlaneMapData.ofCurrentReentry reentry currentMap
        coefficient current_lipschitz current_cellwise density_absorb
    ∀ index point,
      point ∈ rootMap.root.normalization.frame ''
          rootMap.root.normalization.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ bound := by
  dsimp only
  intro index point point_mem
  change point ∈ (AffineIsometryEquiv.refl ℝ Point3) ''
      reentry.ordinarySource.shading.carrier index at point_mem
  rcases point_mem with ⟨sourcePoint, source_mem, rfl⟩
  simpa using
    reentry.ordinaryAxialWindowOf initialAxialWindow index sourcePoint source_mem

/-- Existential compatibility wrapper for the canonical current-reentry
root-map constructor. -/
theorem proposition63_root_plane_map_of_current_reentry
    {delta sigma initialInputLoss normalizationLoss reentryLoss densityLoss
      incidence : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (currentMap : PaperWZ1WeakPlaneMapData current incidence)
    (coefficient : NNReal)
    (current_lipschitz : LipschitzWith coefficient
      (fun point : {point : Point3 // point ∈ current.union} =>
        currentMap.planeMap point))
    (current_cellwise : ∀ first second,
      wz1PaperGridIndex delta first = wz1PaperGridIndex delta second →
        currentMap.planeMap first = currentMap.planeMap second)
    (density_absorb :
      Kakeya.realRpowENN delta densityLoss ≤
        Kakeya.realRpowENN delta reentryLoss / 2) :
    Nonempty (Proposition63RootPlaneMapData
      (densityLoss := densityLoss) (incidence := incidence)
      reentry coefficient) :=
  ⟨Proposition63RootPlaneMapData.ofCurrentReentry reentry currentMap
    coefficient current_lipschitz current_cellwise density_absorb⟩

end Kakeya.Assouad.PureWZ2

end
