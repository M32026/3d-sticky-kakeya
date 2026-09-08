import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.RestrictedFiberFrostmanTransfer

namespace Kakeya.Streamlined.RandomTranslation.WithShading

/--
The restricted fiber contained mass is at most the original fiber contained
mass.
-/
lemma restricted_fiber_containedMass_le
    {fine coarse : BodyFamily}
    (P : Factoring fine coarse)
    (fineSel : Subfamily fine)
    (coarseSel : Subfamily coarse)
    (Q : Factoring fineSel.family coarseSel.family)
    (hcompat : ∀ i,
      coarseSel.embedding (Q.parent i) =
        P.parent (fineSel.embedding i))
    (j : Fin coarseSel.family.card)
    (K : Set Point3) :
    Q.fiberContainedMass j K ≤
      P.fiberContainedMass (coarseSel.embedding j) K := by
  classical
  let e := fineSel.embedding
  let j' := coarseSel.embedding j
  let S := (Q.fiberIndices j).filter
    (fun i => (fineSel.family.body i).carrier ⊆ K)
  let T := (P.fiberIndices j').filter
    (fun i' => (fine.body i').carrier ⊆ K)
  have h1 : ∀ i ∈ S, e i ∈ T := by
    intro i hi
    have h_i_fiber : i ∈ Q.fiberIndices j :=
      (Finset.mem_filter.mp hi).1
    have h_i_cont : (fineSel.family.body i).carrier ⊆ K :=
      (Finset.mem_filter.mp hi).2
    have hQ : Q.parent i = j := by
      simpa [Factoring.fiberIndices, Finset.mem_filter] using h_i_fiber
    have hP : P.parent (e i) = j' := by
      calc
        P.parent (e i) =
            coarseSel.embedding (Q.parent i) := (hcompat i).symm
        _ = coarseSel.embedding j := by rw [hQ]
        _ = j' := rfl
    have hfine : (fine.body (e i)).carrier ⊆ K := by
      rw [← fineSel.carrier_eq i]
      exact h_i_cont
    simp only [T, Finset.mem_filter]
    exact
      ⟨by
        simpa [Factoring.fiberIndices, Finset.mem_filter] using hP,
        hfine⟩
  have h_image_subset : Finset.image e S ⊆ T := by
    rw [Finset.image_subset_iff]
    exact h1
  have h_vol :
      ∀ i ∈ S,
        (fineSel.family.body i).volume =
          (fine.body (e i)).volume := by
    intro i _
    have h_car :
        (fineSel.family.body i).carrier =
          (fine.body (e i)).carrier :=
      fineSel.carrier_eq i
    simp [Body.volume, h_car]
  dsimp only [Factoring.fiberContainedMass]
  calc
    ∑ i ∈ S, (fineSel.family.body i).volume =
        ∑ i ∈ S, (fine.body (e i)).volume := by
      apply Finset.sum_congr rfl
      exact h_vol
    _ = ∑ i' ∈ Finset.image e S, (fine.body i').volume := by
      rw [Finset.sum_image]
      intro i _ j _ h
      exact e.inj' h
    _ ≤ ∑ i' ∈ T, (fine.body i').volume := by
      apply Finset.sum_le_sum_of_subset_of_nonneg h_image_subset
      intro _ _ _
      simp

theorem restricted_fiber_frostman_transfer :
    RestrictedFiberFrostmanTransferStatement := by
  intro fine coarse P fineSel coarseSel Q hcompat C L hFrost hmass
  dsimp only [Factoring.FibersAreCFrostman]
  intro j K hK hKsub
  classical
  set j' := coarseSel.embedding j with hj'
  have hKsub' : K ⊆ (coarse.body j').carrier := by
    have h1 :
        (coarseSel.family.body j).carrier =
          (coarse.body j').carrier :=
      coarseSel.carrier_eq j
    rw [h1] at hKsub
    exact hKsub
  have hvol :
      (coarseSel.family.body j).volume =
        (coarse.body j').volume := by
    have h1 :
        (coarseSel.family.body j).carrier =
          (coarse.body j').carrier :=
      coarseSel.carrier_eq j
    simp [Body.volume, h1]
  have hcm :
      Q.fiberContainedMass j K ≤
        P.fiberContainedMass j' K :=
    restricted_fiber_containedMass_le
      P fineSel coarseSel Q hcompat j K
  have hFrost' :
      P.fiberContainedMass j' K * (coarse.body j').volume ≤
        C * P.fiberMass j' * MeasureTheory.volume K :=
    hFrost j' K hK hKsub'
  have hmass' : P.fiberMass j' ≤ L * Q.fiberMass j := hmass j
  calc
    Q.fiberContainedMass j K *
          (coarseSel.family.body j).volume =
        Q.fiberContainedMass j K *
          (coarse.body j').volume := by
      rw [hvol]
    _ ≤ P.fiberContainedMass j' K *
          (coarse.body j').volume := by
      gcongr
    _ ≤ C * P.fiberMass j' * MeasureTheory.volume K := hFrost'
    _ ≤ C * (L * Q.fiberMass j) * MeasureTheory.volume K := by
      gcongr
    _ = (L * C) * Q.fiberMass j * MeasureTheory.volume K := by
      simp [mul_assoc, mul_left_comm]

end Kakeya.Streamlined.RandomTranslation.WithShading
