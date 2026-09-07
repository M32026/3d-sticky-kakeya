import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement

/-!
# Cell-wise mass decomposition for WZ1

This module decomposes a tube shading's mass over a finite measurable
partition.  It is the measure-theoretic input to the WZ1 Lemma 13
coarse-parent pigeonhole.
-/

attribute [local instance] Classical.propDecidable

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
Decompose shaded mass across finite measurable cells.

The fibers `{p | cell p = c}` partition the ambient space, so the total
shaded mass is the sum of the point-multiplicity integrals over the cells.
-/
lemma shading_mass_cell_decomposition
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {cellCount : ℕ} {cell : Point3 → Fin cellCount}
    (hcell_meas : Measurable cell) :
    Y.mass = ∑ c : Fin cellCount,
      ∫⁻ p in {p | cell p = c}, (Y.pointMultiplicity p : ENNReal) := by
  let cellSet : Fin cellCount → Set Point3 := fun c => {p | cell p = c}
  have hcells : ∀ c : Fin cellCount, MeasurableSet (cellSet c) := by
    intro c
    exact hcell_meas (MeasurableSet.singleton c)
  have hcells' :
      ∀ c ∈ (Finset.univ : Finset (Fin cellCount)),
        MeasurableSet (cellSet c) :=
    fun c _ => hcells c
  have hdisj :
      Set.PairwiseDisjoint
        (↑(Finset.univ : Finset (Fin cellCount))) cellSet := by
    intro c _ d _ hne
    have h : Disjoint (cellSet c) (cellSet d) := by
      rw [Set.disjoint_left]
      intro p hp1 hp2
      exact hne (hp1.symm.trans hp2)
    exact h
  have hunion : (⋃ c : Fin cellCount, cellSet c) = Set.univ := by
    ext p
    simp only [Set.mem_univ, iff_true, Set.mem_iUnion, cellSet]
    exact ⟨cell p, rfl⟩
  calc
    Y.mass = ∫⁻ p, (Y.pointMultiplicity p : ENNReal) :=
      (lintegral_pointMultiplicity Y).symm
    _ = ∫⁻ p in (Set.univ : Set Point3),
          (Y.pointMultiplicity p : ENNReal) := by simp
    _ = ∫⁻ p in (⋃ c : Fin cellCount, cellSet c),
          (Y.pointMultiplicity p : ENNReal) := by rw [hunion]
    _ = ∑ c : Fin cellCount, ∫⁻ p in cellSet c,
          (Y.pointMultiplicity p : ENNReal) := by
      have h_biunion :
          (⋃ c : Fin cellCount, cellSet c) =
            ⋃ c ∈ (Finset.univ : Finset (Fin cellCount)), cellSet c := by
        ext p
        simp
      rw [h_biunion]
      exact MeasureTheory.lintegral_biUnion_finset hdisj hcells'
        (fun p : Point3 => (Y.pointMultiplicity p : ENNReal))

end Kakeya.Assouad
