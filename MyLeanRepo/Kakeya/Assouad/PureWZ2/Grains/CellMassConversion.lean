import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RobustCloseCountPhase2
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers
import Mathlib.Tactic

/-!
# Cell mass to average multiplicity conversion

Converts the balanced cover's `cellMass` into volume identities and a
Markov fiber-cap restriction suitable for Phase 2 of the robust close count
pipeline.

## Key results

1. `balanced_cover_coarse_volume`: coarse union volume = |activeCells| * cubeVolume
2. `balanced_cover_fine_union_volume`: fine union volume = |activeCells| * cellMass
3. `balanced_cover_markov_restriction`: apply Markov to get fiber-capped subshading

These feed directly into `markov_multiplicity_restriction` and `markov_fiber_cap`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

attribute [local instance] Classical.propDecidable

/-- Coarse union volume equals number of active cells times cube volume. -/
lemma balanced_cover_coarse_volume
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hrho_pos : 0 < rho) :
    MeasureTheory.volume coarseShading.union =
      (balanced.activeCells.card : ENNReal) *
        MeasureTheory.volume (wz1PaperGridCube rho (0, 0, 0)) := by
  rw [balanced.coarse_union_eq]
  exact wz1PaperGridCube_volume_biUnion hrho_pos balanced.activeCells

/-- Fine union volume equals number of active cells times cellMass. -/
lemma balanced_cover_fine_union_volume
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hrho_pos : 0 < rho) :
    MeasureTheory.volume fineShading.union =
      (balanced.activeCells.card : ENNReal) * balanced.cellMass := by
  have h1 : fineShading.union =
      ⋃ cell ∈ balanced.activeCells,
        (fineShading.union ∩ wz1PaperGridCube rho cell) := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hp
      have h2 : p ∈ coarseShading.union := by
        rcases hp with ⟨i, hi⟩
        let parent := selectParent cover i
        have hcovers : WZ1PaperTubeCovers (fine.tube i) (coarse.tube parent) :=
          selectedParent_covers cover i
        have h3 : p ∈ coarseShading.carrier parent :=
          balanced.point_compatibility i parent hcovers p hi
        exact ⟨parent, h3⟩
      have h4 : ∃ (cell : ℤ × ℤ × ℤ), cell ∈ balanced.activeCells ∧
          p ∈ wz1PaperGridCube rho cell := by
        rw [balanced.coarse_union_eq] at h2
        simpa [Set.mem_iUnion] using h2
      rcases h4 with ⟨cell, hcell, hpcube⟩
      exact ⟨cell, hcell, hp, hpcube⟩
    · rintro ⟨cell, _, hp, _⟩
      exact hp
  rw [h1]
  have h_disj : Set.PairwiseDisjoint (↑balanced.activeCells)
      (fun cell => fineShading.union ∩ wz1PaperGridCube rho cell) := by
    intro i _ j _ hne
    exact (wz1PaperGridCube_disjoint hne).mono Set.inter_subset_right Set.inter_subset_right
  have h_union_meas : MeasurableSet fineShading.union := by
    have h : fineShading.union = ⋃ (i : Fin fine.card), fineShading.carrier i := by
      ext x; simp [Kakeya.Streamlined.Shading.union]; tauto
    rw [h]
    exact MeasurableSet.iUnion fun i => fineShading.measurable_carrier i
  have h_meas : ∀ cell ∈ balanced.activeCells,
      MeasurableSet (fineShading.union ∩ wz1PaperGridCube rho cell) := by
    intro cell _
    exact h_union_meas.inter (wz1PaperGridCube_measurable cell)
  rw [MeasureTheory.measure_biUnion_finset h_disj h_meas]
  have h_sum : ∑ cell ∈ balanced.activeCells,
      volume (fineShading.union ∩ wz1PaperGridCube rho cell) =
      (balanced.activeCells.card : ENNReal) * balanced.cellMass := by
    rw [Finset.sum_congr rfl fun cell hcell => balanced.fine_cell_mass cell hcell]
    simp [Finset.sum_const]
  exact h_sum

/-- Apply Markov restriction using average multiplicity over fine union.

Given a balanced cover, set:
- `V := volume fineShading.union = |activeCells| * cellMass`
- `A := fineShading.mass / V` (average multiplicity)

Then `markov_multiplicity_restriction` gives a bad set of volume ≤ V/2
where point multiplicity > 2*A, and the restricted shading has fiber
multiplicity ≤ 2*A on all points outside the bad set.

This provides the `hfiber` input for Phase 3 with `fiberCap := 2 * A`. -/
lemma balanced_cover_markov_restriction
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hrho_pos : 0 < rho)
    (hmass_ne_top : fineShading.mass ≠ ⊤)
    (hmass_pos : fineShading.mass ≠ 0) :
    ∃ (bad : Set Point3) (restricted : WZ1PaperTubeShading fine),
      MeasurableSet bad ∧
      MeasureTheory.volume bad ≤ MeasureTheory.volume fineShading.union / 2 ∧
      (∀ p ∉ bad, (fineShading.pointMultiplicity p : ENNReal) ≤
          2 * (fineShading.mass / MeasureTheory.volume fineShading.union)) ∧
      (∀ (parent : Fin coarse.card) (p : Point3),
        (fiberPointMultiplicity cover restricted parent p : ENNReal) ≤
          2 * (fineShading.mass / MeasureTheory.volume fineShading.union)) ∧
      PaperIsSubshading restricted fineShading := by
  let V : ENNReal := MeasureTheory.volume fineShading.union
  have hV_eq : V = (balanced.activeCells.card : ENNReal) * balanced.cellMass :=
    balanced_cover_fine_union_volume balanced hrho_pos
  have hV_ne_top : V ≠ ⊤ := by
    rw [hV_eq]
    apply ENNReal.mul_ne_top
    · exact ENNReal.natCast_ne_top _
    · exact balanced.cellMass_ne_top
  have hV_ne_zero : V ≠ 0 := by
    rw [hV_eq]
    by_cases h : balanced.activeCells.Nonempty
    · have h1 : (balanced.activeCells.card : ENNReal) ≠ 0 := by
        have h2 : 0 < balanced.activeCells.card := Finset.Nonempty.card_pos h
        exact_mod_cast h2.ne'
      exact mul_ne_zero h1 balanced.cellMass_pos.ne'
    · have h2 : balanced.activeCells = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using h
      have h3 : coarseShading.union = ∅ := by
        rw [balanced.coarse_union_eq, h2]; simp
      have h4 : fineShading.union = ∅ := by
        have h5 : fineShading.union ⊆ coarseShading.union := by
          intro p hp
          rcases hp with ⟨i, hi⟩
          let parent := selectParent cover i
          have hcovers := selectedParent_covers cover i
          have h6 : p ∈ coarseShading.carrier parent :=
            balanced.point_compatibility i parent hcovers p hi
          exact ⟨parent, h6⟩
        rw [h3] at h5
        simpa using h5
      have h6 : fineShading.mass = 0 := by
        have h7 : ∀ (i : Fin fine.card), fineShading.carrier i = ∅ := by
          intro i
          have h8 : fineShading.carrier i ⊆ fineShading.union := by
            intro x hx; exact ⟨i, hx⟩
          rw [h4] at h8
          simpa using h8
        simp [Kakeya.Streamlined.Shading.mass, h7]
      rw [h6] at hmass_pos
      exact False.elim (hmass_pos rfl)
  let A : ENNReal := fineShading.mass / V
  have hA_pos : 0 < A := ENNReal.div_pos hmass_pos hV_ne_top
  have hA_ne_top : A ≠ ⊤ := ENNReal.div_ne_top hmass_ne_top hV_ne_zero
  have h_mass : fineShading.mass ≤ A * V := by
    have h_eq : A * V = fineShading.mass := by
      simp only [A]
      rw [ENNReal.div_mul_cancel hV_ne_zero hV_ne_top]
    exact h_eq.symm.le
  rcases markov_multiplicity_restriction fineShading V A hV_ne_top hA_pos hA_ne_top h_mass
    with ⟨bad, hbad_meas, hbad_vol, hgood⟩
  let restricted : WZ1PaperTubeShading fine :=
    restrictShading fineShading bad hbad_meas
  have hsub : PaperIsSubshading restricted fineShading :=
    restrictShading_subshading fineShading bad hbad_meas
  have hfiber : ∀ (parent : Fin coarse.card) (p : Point3),
      (fiberPointMultiplicity cover restricted parent p : ENNReal) ≤ 2 * A := by
    intro parent p
    by_cases hp : p ∉ bad
    · exact markov_fiber_cap (V := V) (A := A) hgood parent p hp
    · have hbad : p ∈ bad := by tauto
      have h_zero : fiberPointMultiplicity cover restricted parent p = 0 := by
        have h1 : ∀ (i : Fin fine.card), p ∉ restricted.carrier i := by
          intro i
          simp [restricted, restrictShading, hbad]
        have h2 : (Finset.univ.filter fun i : Fin fine.card =>
            selectParent cover i = parent ∧ p ∈ restricted.carrier i) = ∅ := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          simp
          intro _
          exact h1 i
        simpa [fiberPointMultiplicity] using h2
      rw [h_zero]
      simp
  exact ⟨bad, restricted, hbad_meas, hbad_vol, hgood, hfiber, hsub⟩

end Kakeya.Assouad.PureWZ2

end
