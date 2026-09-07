import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentTwoLevelCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SourceWitnessCoarseShading
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.OneScaleVariationGeometry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CubicalSlabLower

/-!
# Plane incidence for the dependent preliminary Lemma 4.12 step

The finite preliminary iteration keeps one plane map on the fixed root
family.  At a fresh Section-6 scale, the Córdoba argument is performed on a
coarse parent family.  A coarse parent/point pair therefore needs an actual
fine child in the same spatial cell; membership in the ambient coarse shading
alone is not enough.

This file records the exact paper transfer.  Fine incidence is evaluated at
the parent-specific shaded child, the plane normal is moved across one
`rho`-cell using the genuine Lipschitz constant, and the tube direction is
moved to the assigned parent using `paper_cover_parent_incidence`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Set

/-- The incidence budget obtained by moving a fine normal within one coarse
cell and then moving the fine tube direction to its Section-6 parent. -/
def proposition63DependentCoarseIncidence
    (rho fineIncidence : ℝ) (coefficient : NNReal) : ℝ :=
  fineIncidence + (coefficient : ℝ) * (rho * Real.sqrt 3) + rho / 2

/-- Parent-specific same-cell provenance transfers a fine incidence estimate
to the corresponding coarse tube.  The conclusion uses the original ambient
plane map; no sampled or constant replacement map is introduced. -/
theorem proposition63_coarse_incidence_of_source_witness
    {delta rho fineIncidence : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced : PureWZ2BalancedCoverData cover fineShading coarseShading}
    (sourceWitness : PureWZ2SourceWitnessCoarseShadingData balanced)
    {coarseFamily : Kakeya.Streamlined.TubeFamily rho}
    (selectedCoarse : WZ1PaperTubeShading coarseFamily)
    (ancestorEmbedding : Fin coarseFamily.card ↪ Fin coarse.card)
    (ancestor_tube_eq : ∀ index,
      coarseFamily.tube index = coarse.tube (ancestorEmbedding index))
    (selected_sub_sourceWitness : ∀ index,
      selectedCoarse.carrier index ⊆
        sourceWitness.shading.carrier (ancestorEmbedding index))
    (planeMap : Point3 → Point3) (coefficient : NNReal)
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hfineIncidence : ∀ index point,
      ∀ hpoint : point ∈ fineShading.carrier index,
        |@Inner.inner ℝ Point3 _ (fine.tube index).direction
          (planeMap point)| ≤ fineIncidence)
    (hrho : 0 < rho) :
    ∀ index point, ∀ hpoint : point ∈ selectedCoarse.carrier index,
      ‖planeMap point‖ = 1 →
      |@Inner.inner ℝ Point3 _ (coarseFamily.tube index).direction
        (planeMap point)| ≤
          proposition63DependentCoarseIncidence
            rho fineIncidence coefficient := by
  intro index point hpoint hpointUnit
  have hpointSourceWitness : point ∈
      sourceWitness.shading.carrier (ancestorEmbedding index) :=
    selected_sub_sourceWitness index hpoint
  rw [sourceWitness.shading_carrier_eq (ancestorEmbedding index)] at hpointSourceWitness
  rcases Set.mem_iUnion₂.mp hpointSourceWitness with
    ⟨cell, hcell, hpointCell⟩
  rcases sourceWitness.source_witness (ancestorEmbedding index) cell hcell with
    ⟨sourceIndex, sourcePoint, hparent, hsourcePoint, hsourceCell⟩
  have hsourceUnion : sourcePoint ∈ fineShading.union :=
    ⟨sourceIndex, hsourcePoint⟩
  have hsameCell :
      wz1PaperGridIndex rho sourcePoint = wz1PaperGridIndex rho point := by
    exact ((mem_wz1PaperGridCube rho cell sourcePoint).mp hsourceCell).trans
      ((mem_wz1PaperGridCube rho cell point).mp hpointCell).symm
  have hpointInSourceCell :
      point ∈ wz1PaperGridCube rho (wz1PaperGridIndex rho sourcePoint) :=
    (mem_wz1PaperGridCube rho _ point).mpr hsameCell.symm
  have hsourceInSourceCell :
      sourcePoint ∈
        wz1PaperGridCube rho (wz1PaperGridIndex rho sourcePoint) :=
    (mem_wz1PaperGridCube rho _ sourcePoint).mpr rfl
  have hpointDistance : dist sourcePoint point ≤ rho * Real.sqrt 3 :=
    wz1PaperGridCube_diameter hrho _ hsourceInSourceCell hpointInSourceCell
  have hmapDistance : dist (planeMap sourcePoint) (planeMap point) ≤
      (coefficient : ℝ) * (rho * Real.sqrt 3) :=
    (hplaneLipschitz.dist_le_mul sourcePoint point).trans
      (mul_le_mul_of_nonneg_left hpointDistance coefficient.coe_nonneg)
  have hfinePaper :
      |inner ℝ (wz1PaperDirection (fine.tube sourceIndex))
          (planeMap sourcePoint)| ≤ fineIncidence := by
    have hraw := hfineIncidence sourceIndex sourcePoint hsourcePoint
    unfold wz1PaperDirection
    split_ifs <;> simpa [inner_neg_left] using hraw
  have hfineAtPoint :
      |inner ℝ (wz1PaperDirection (fine.tube sourceIndex))
          (planeMap point)| ≤
        fineIncidence + (coefficient : ℝ) * (rho * Real.sqrt 3) := by
    have hinnerDifference :
        |inner ℝ (wz1PaperDirection (fine.tube sourceIndex))
            (planeMap point - planeMap sourcePoint)| ≤
          dist (planeMap sourcePoint) (planeMap point) := by
      calc
        |inner ℝ (wz1PaperDirection (fine.tube sourceIndex))
            (planeMap point - planeMap sourcePoint)| ≤
            ‖wz1PaperDirection (fine.tube sourceIndex)‖ *
              ‖planeMap point - planeMap sourcePoint‖ :=
          abs_real_inner_le_norm _ _
        _ = dist (planeMap sourcePoint) (planeMap point) := by
          rw [wz1PaperDirection_norm]
          simp [dist_eq_norm, norm_sub_rev]
    have hdecompose :
        inner ℝ (wz1PaperDirection (fine.tube sourceIndex))
            (planeMap point) =
          inner ℝ (wz1PaperDirection (fine.tube sourceIndex))
              (planeMap sourcePoint) +
            inner ℝ (wz1PaperDirection (fine.tube sourceIndex))
              (planeMap point - planeMap sourcePoint) := by
      rw [inner_sub_right]
      ring
    rw [hdecompose]
    calc
      |inner ℝ (wz1PaperDirection (fine.tube sourceIndex))
            (planeMap sourcePoint) +
          inner ℝ (wz1PaperDirection (fine.tube sourceIndex))
            (planeMap point - planeMap sourcePoint)| ≤
          |inner ℝ (wz1PaperDirection (fine.tube sourceIndex))
              (planeMap sourcePoint)| +
            |inner ℝ (wz1PaperDirection (fine.tube sourceIndex))
              (planeMap point - planeMap sourcePoint)| := abs_add_le _ _
      _ ≤ fineIncidence + (coefficient : ℝ) * (rho * Real.sqrt 3) :=
        add_le_add hfinePaper (hinnerDifference.trans hmapDistance)
  have hcover : WZ1PaperTubeCovers
      (fine.tube sourceIndex) (coarse.tube (ancestorEmbedding index)) := by
    rw [← hparent]
    exact cover.toPaperTubeCover.parent_covers sourceIndex
  have hparentIncidence := paper_cover_parent_incidence hcover
    hpointUnit hfineAtPoint
  rw [ancestor_tube_eq index]
  have hrawPaper :
      |inner ℝ (coarse.tube (ancestorEmbedding index)).direction
          (planeMap point)| =
        |inner ℝ (wz1PaperDirection
          (coarse.tube (ancestorEmbedding index))) (planeMap point)| := by
    unfold wz1PaperDirection
    split_ifs <;> simp [inner_neg_left]
  rw [hrawPaper]
  simpa [proposition63DependentCoarseIncidence, add_assoc] using
    hparentIncidence

/-- Package the caller's one fixed ambient plane map on the honest
source-witness coarse shading.  The map itself is unchanged: source witnesses
only certify unit norm and fine-to-coarse incidence at the new points. -/
noncomputable def source_witness_coarse_weak_plane_map
    {delta rho fineIncidence : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {balanced : PureWZ2BalancedCoverData cover fineShading coarseShading}
    (sourceWitness : PureWZ2SourceWitnessCoarseShadingData balanced)
    (planeMap : Point3 → Point3) (coefficient : NNReal)
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneUnit : ∀ point ∈ sourceWitness.shading.union,
      ‖planeMap point‖ = 1)
    (hfineIncidence : ∀ index point,
      ∀ hpoint : point ∈ fineShading.carrier index,
        |@Inner.inner ℝ Point3 _ (fine.tube index).direction
          (planeMap point)| ≤ fineIncidence)
    (hrho : 0 < rho) :
    PaperWZ1WeakPlaneMapData sourceWitness.shading
      (proposition63DependentCoarseIncidence rho fineIncidence coefficient) :=
  { planeMap := planeMap
    measurable := hplaneLipschitz.continuous.measurable
    unit := hplaneUnit
    incidence := by
      intro index point hpoint
      exact proposition63_coarse_incidence_of_source_witness sourceWitness
        sourceWitness.shading (Function.Embedding.refl _) (fun _ => rfl)
        (fun _ => Set.Subset.rfl) planeMap coefficient hplaneLipschitz
        hfineIncidence hrho index point hpoint (hplaneUnit point ⟨index, hpoint⟩) }

end Kakeya.Assouad.PureWZ2

end
