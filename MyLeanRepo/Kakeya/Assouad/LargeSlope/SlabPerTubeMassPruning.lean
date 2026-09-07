import MyLeanRepo.Kakeya.Assouad.Statements

/-!
WZ2 Section 6, Step 4: retain exactly the tubes with enough shaded mass
inside the selected slab, while recording the sharp finite discarded-mass
error.
-/

namespace Kakeya.Assouad

theorem slab_per_tube_mass_pruning :
    SlabPerTubeMassPruningStatement := by
  intro delta F Y a b threshold
  classical
  let m : Fin F.card → ENNReal := fun i =>
    MeasureTheory.volume (Y.carrier i ∩ horizontalSlab a b)
  let good : Finset (Fin F.card) :=
    Finset.univ.filter (fun i => threshold ≤ m i)
  let carrierZ (i : Fin F.card) : Set Point3 :=
    if i ∈ good then Y.carrier i else (∅ : Set Point3)
  have h_meas : ∀ i, MeasurableSet (carrierZ i) := by
    intro i
    by_cases h : i ∈ good
    · have h4 : carrierZ i = Y.carrier i := by
        dsimp only [carrierZ]
        rw [if_pos h]
      rw [h4]
      exact Y.measurable_carrier i
    · have h4 : carrierZ i = (∅ : Set Point3) := by
        dsimp only [carrierZ]
        rw [if_neg h]
      rw [h4]
      exact MeasurableSet.empty
  have h_subset_body : ∀ i, carrierZ i ⊆ (F.toBodyFamily.body i).carrier := by
    intro i
    by_cases h : i ∈ good
    · have h4 : carrierZ i = Y.carrier i := by
        dsimp only [carrierZ]
        rw [if_pos h]
      rw [h4]
      exact Y.subset_body i
    · have h4 : carrierZ i = (∅ : Set Point3) := by
        dsimp only [carrierZ]
        rw [if_neg h]
      rw [h4]
      exact Set.empty_subset _
  let Z : Kakeya.Streamlined.TubeShading F :=
    { carrier := carrierZ
      measurable_carrier := h_meas
      subset_body := h_subset_body }
  have hZ_carrier_good : ∀ i ∈ good, Z.carrier i = Y.carrier i := by
    intro i hi
    dsimp only [Z, carrierZ]
    rw [if_pos hi]
  have hZ_carrier_bad : ∀ i ∉ good, Z.carrier i = (∅ : Set Point3) := by
    intro i hi
    dsimp only [Z, carrierZ]
    rw [if_neg hi]
  have h_sub : IsSubshading Z Y := by
    intro i
    by_cases h : i ∈ good
    · rw [hZ_carrier_good i h]
    · rw [hZ_carrier_bad i h]
      exact Set.empty_subset _
  have h_per_tube : HasPerTubeMassInSlab Z a b threshold := by
    intro i
    by_cases h : i ∈ good
    · have h4 : Z.carrier i = Y.carrier i := hZ_carrier_good i h
      have h5 : threshold ≤ m i := (Finset.mem_filter.mp h).2
      rw [h4]
      exact Or.inr h5
    · have h4 : Z.carrier i = (∅ : Set Point3) := hZ_carrier_bad i h
      have h5 : Z.carrier i ∩ horizontalSlab a b = ∅ := by
        rw [h4]
        simp
      exact Or.inl h5
  have h_bad_zero : ∀ i ∉ good,
      MeasureTheory.volume (Z.carrier i ∩ horizontalSlab a b) = 0 := by
    intro i hi
    have h4 : Z.carrier i = (∅ : Set Point3) := hZ_carrier_bad i hi
    rw [h4]
    simp
  have h_mass_Z : shadedMassInSlab Z a b = ∑ i ∈ good, m i := by
    have h5 : shadedMassInSlab Z a b =
        ∑ i : Fin F.card, MeasureTheory.volume (Z.carrier i ∩ horizontalSlab a b) := by
      rfl
    rw [h5]
    have h6 : ∑ i : Fin F.card, MeasureTheory.volume (Z.carrier i ∩ horizontalSlab a b) =
        ∑ i ∈ good, MeasureTheory.volume (Z.carrier i ∩ horizontalSlab a b) := by
      rw [Finset.sum_subset (show good ⊆ Finset.univ from by simp)]
      intro i _ hi
      exact h_bad_zero i hi
    rw [h6]
    apply Finset.sum_congr rfl
    intro i hi
    have h7 : Z.carrier i = Y.carrier i := hZ_carrier_good i hi
    rw [h7]
  let badMass : ENNReal := ∑ i ∈ Finset.univ \ good, m i
  have h_bad_le : badMass ≤ threshold * F.enncard := by
    have h1 : ∀ i ∈ Finset.univ \ good, m i < threshold := by
      intro i hi
      have h2 : i ∉ good := (Finset.mem_sdiff).mp hi |>.2
      have h3 : ¬(threshold ≤ m i) := by
        by_contra h4
        have h5 : i ∈ good := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ i, h4⟩
        exact h2 h5
      exact lt_of_not_ge h3
    have h_card : (Finset.univ \ good).card ≤ F.card := by
      have h4 : (Finset.univ \ good) ⊆ (Finset.univ : Finset (Fin F.card)) := by simp
      have h5 : (Finset.univ \ good).card ≤ (Finset.univ : Finset (Fin F.card)).card :=
        Finset.card_le_card h4
      simpa using h5
    calc
      badMass
        ≤ ∑ i ∈ Finset.univ \ good, threshold := by
          apply Finset.sum_le_sum
          intro i hi
          exact (h1 i hi).le
      _ = threshold * (Finset.univ \ good).card := by
          rw [Finset.sum_const, mul_comm]
          ring
      _ ≤ threshold * F.enncard := by
          gcongr
          simpa [Kakeya.Streamlined.TubeFamily.enncard] using h_card
  have h_mass_split : shadedMassInSlab Y a b = shadedMassInSlab Z a b + badMass := by
    have h_disj : Disjoint good (Finset.univ \ good) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp hx2).2 hx1
    have h_univ : good ∪ (Finset.univ \ good) = (Finset.univ : Finset (Fin F.card)) := by
      ext x; simp
    have h2 : ∑ i ∈ good, m i + badMass =
        ∑ i ∈ good ∪ (Finset.univ \ good), m i := by
      rw [Finset.sum_union h_disj]
    rw [h_mass_Z, h2, h_univ]
    rfl
  have h_main : shadedMassInSlab Y a b ≤ shadedMassInSlab Z a b + threshold * F.enncard := by
    rw [h_mass_split]
    exact add_le_add_right h_bad_le (shadedMassInSlab Z a b)
  exact ⟨Z, h_sub, h_main, h_per_tube⟩

end Kakeya.Assouad
