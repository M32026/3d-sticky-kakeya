import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.PlanarGridPartitionTree
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberAtomizationToOSStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberPullbackMass
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.WeightedOSBranchingUniformRefinement

/-!
# From projected-fiber atoms to a locally uniform subtree

Compose the planar partition tree, weighted OS pruning, and projected-fiber
pullback mass identity.
-/

open MeasureTheory

namespace Kakeya.Assouad

theorem projected_fiber_atomization_to_os :
    ProjectedFiberAtomizationToOSStatement := by
  intro delta F Y f threshold levelCount bandData base levels indexBound
    hbase atomized

  let μ : Measure Point2 := projectedFiberMeasure Y f
  let atom : Point2 → Set Point2 :=
    projectedFiberGridAtom bandData.band base levels
  let A : DiscreteSet 2 := atomized.centers
  let P : ℕ → Finset (Finset Point2) :=
    fun level => planarGridPartition base level A

  have hbase_pos' : (0 : ℝ) < (base : ℝ) := by
    exact_mod_cast (show 0 < base from by linarith)

  have h_mesh :
      2 < ((base ^ levels : ℝ)⁻¹) *
        (base ^ (levels + 1) : ℝ) := by
    have h1 :
        ((base ^ levels : ℝ)⁻¹) *
            (base ^ (levels + 1) : ℝ) =
          (base : ℝ) := by
      have h2 :
          (base ^ (levels + 1) : ℝ) =
            (base ^ levels : ℝ) * (base : ℝ) := by
        simp [pow_succ]
      rw [h2]
      field_simp [hbase_pos'.ne']
    rw [h1]
    exact_mod_cast (show 2 < base from by linarith)

  have hfine_pos : (0 : ℝ) < (base ^ levels : ℝ)⁻¹ := by
    positivity
  have hbase2 : 2 ≤ base := by linarith

  rcases planar_grid_partition_tree
      A atomized.centers_nonempty base (levels + 1) hbase2
      ((base ^ levels : ℝ)⁻¹) hfine_pos
      atomized.centers_separated h_mesh with
    ⟨h_partition, h_atomic, h_nesting, h_child_bound⟩

  let L : ℕ :=
    (2 * (Nat.log 2 ((base + 1) ^ 2) + 1)) ^
      (levels + 1)
  let childBound : ℕ := (base + 1) ^ 2
  have hcb_pos : 0 < childBound := by positivity

  rcases weighted_os_branching_uniform_refinement
      (β := Point2) μ
      (α := Point2) A atomized.centers_nonempty
      atom atomized.atom_measurable atomized.atom_disjoint
      atomized.atom_mass_pos atomized.atom_mass_ne_top
      atomized.atom_mass_comparable
      (levels + 1) childBound hcb_pos
      P h_partition h_atomic h_nesting h_child_bound with
    ⟨A', hA'_nonempty, hA'_sub, h_meas', h_sub, h_mass_ret,
      branchExponent, h_branch_bound, h_branch_unif⟩

  let retainedBand : Set Point2 := finiteAtomUnion A' atom
  let shading : Kakeya.Streamlined.TubeShading F :=
    projectionPullbackShading Y f retainedBand h_meas'

  have h_mass_identity :
      shading.mass = projectedFiberMeasure Y f retainedBand := by
    have hpm :
        (projectionPullbackShading Y f retainedBand h_meas').mass =
          ∫⁻ q in retainedBand,
            projectedFiberMultiplicity Y f q :=
      projected_fiber_pullback_mass
        (F := F) (Y := Y) (f := f)
        (X := retainedBand) h_meas'
    have hwd :
        projectedFiberMeasure Y f retainedBand =
          ∫⁻ q in retainedBand,
            projectedFiberMultiplicity Y f q :=
      MeasureTheory.withDensity_apply
        (projectedFiberMultiplicity Y f) h_meas'
    rw [hpm, hwd]

  have hRB_sub : retainedBand ⊆ atomized.retainedBand := by
    calc
      retainedBand = finiteAtomUnion A' atom := rfl
      _ ⊆ finiteAtomUnion A atom := h_sub
      _ = atomized.retainedBand :=
        atomized.retainedBand_eq.symm

  have h_subshading : IsSubshading shading atomized.shading := by
    intro i
    have h1 :
        shading.carrier i =
          Y.carrier i ∩
            twistedProjection f ⁻¹' retainedBand := by
      rfl
    have h2 :
        atomized.shading.carrier i =
          Y.carrier i ∩
            twistedProjection f ⁻¹' atomized.retainedBand := by
      rw [atomized.shading_eq]
      rfl
    rw [h1, h2]
    exact Set.inter_subset_inter_right _
      (Set.preimage_mono hRB_sub)

  have h1_atom :
      atomized.shading.mass =
        μ (finiteAtomUnion A atom) := by
    rw [atomized.mass_identity,
      atomized.retainedBand_eq]

  have h2_atom :
      shading.mass =
        μ (finiteAtomUnion A' atom) :=
    h_mass_identity

  have h_os_mass :
      atomized.shading.mass ≤
        (2 : ENNReal) * (L : ENNReal) * shading.mass := by
    rw [h1_atom, h2_atom]
    exact h_mass_ret

  let C_atom : ENNReal :=
    ((2 *
      (Nat.log 2
        (2 *
          (boundedPlanarGridCenters
            base levels indexBound).card) +
        1) : ℕ) : ENNReal)

  have h_total_mass :
      bandData.shading.mass ≤
        C_atom * ((2 : ENNReal) * (L : ENNReal)) *
          shading.mass := by
    have h1 :
        bandData.shading.mass ≤
          C_atom * atomized.shading.mass :=
      atomized.mass_retention
    have h2 :
        atomized.shading.mass ≤
          (2 : ENNReal) * (L : ENNReal) * shading.mass :=
      h_os_mass
    calc
      bandData.shading.mass ≤
          C_atom * atomized.shading.mass := h1
      _ ≤ C_atom *
          ((2 : ENNReal) * (L : ENNReal) *
            shading.mass) := by
        gcongr
      _ = C_atom *
          ((2 : ENNReal) * (L : ENNReal)) *
            shading.mass := by
        ring

  have h_twisted :
      twistedUnion shading f ⊆ retainedBand :=
    projectionPullback_twistedUnion_subset
      Y f retainedBand h_meas'

  refine
    ⟨A', hA'_nonempty, hA'_sub,
      retainedBand, rfl, h_meas', hRB_sub,
      shading, rfl, h_subshading, h_mass_identity,
      h_os_mass, h_total_mass, h_twisted,
      branchExponent, h_branch_bound, ?_⟩
  intro level parent hparent hnonempty
  exact h_branch_unif level parent hparent hnonempty

end Kakeya.Assouad
