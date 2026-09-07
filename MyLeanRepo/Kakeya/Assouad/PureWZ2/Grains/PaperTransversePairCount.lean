import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains

/-!
# Transverse ordered-pair counting for paper shadings

If every active fine tube has at most half the point multiplicity in its
`kappa`-close direction cluster, at least half of all ordered active pairs are
`kappa`-transverse.
-/

open scoped Classical

namespace Kakeya.Assouad

open Finset

lemma paper_transverse_ordered_pairs_lower
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F}
    {fineKappa : ℝ} {fineMultiplicity : ℕ}
    (hclose : ∀ p ∈ Y.union, ∀ i, p ∈ Y.carrier i →
      2 * paperCloseDirectionCount Y p i fineKappa ≤ fineMultiplicity)
    (h_mult_lower : ∀ p ∈ Y.union,
      fineMultiplicity ≤ Y.pointMultiplicity p)
    (p : Point3) (hp : p ∈ Y.union) :
    let active : Finset (Fin F.card) :=
      Finset.univ.filter fun i => p ∈ Y.carrier i
    let transversePairs : Finset (Fin F.card × Fin F.card) :=
      (active ×ˢ active).filter fun pair =>
        fineKappa ≤
          ‖wz1Cross (F.tube pair.1).direction
            (F.tube pair.2).direction‖
    2 * transversePairs.card ≥ (Y.pointMultiplicity p) ^ 2 := by
  let active : Finset (Fin F.card) :=
    Finset.univ.filter fun i => p ∈ Y.carrier i
  let multiplicity := Y.pointMultiplicity p
  have hactiveCard : active.card = multiplicity := by rfl
  have hfineLe : fineMultiplicity ≤ multiplicity := h_mult_lower p hp
  let closePartners (i : Fin F.card) : Finset (Fin F.card) :=
    Finset.univ.filter fun j =>
      p ∈ Y.carrier j ∧
        ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ < fineKappa
  let transversePartners (i : Fin F.card) : Finset (Fin F.card) :=
    Finset.univ.filter fun j =>
      p ∈ Y.carrier j ∧
        fineKappa ≤
          ‖wz1Cross (F.tube i).direction (F.tube j).direction‖
  have hcloseLe : ∀ i ∈ active,
      2 * (closePartners i).card ≤ fineMultiplicity := by
    intro i hi
    have hiY : p ∈ Y.carrier i := (Finset.mem_filter.mp hi).2
    exact hclose p hp i hiY
  have hunion : ∀ i ∈ active,
      closePartners i ∪ transversePartners i = active := by
    intro i _
    ext j
    simp only [closePartners, transversePartners, active,
      Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨hj, _⟩ | ⟨hj, _⟩) <;> exact hj
    · intro hj
      by_cases hcross :
          ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ < fineKappa
      · exact Or.inl ⟨hj, hcross⟩
      · exact Or.inr ⟨hj, le_of_not_gt hcross⟩
  have hdisjoint : ∀ i,
      Disjoint (closePartners i) (transversePartners i) := by
    intro i
    rw [Finset.disjoint_left]
    intro j hcloseJ htransverseJ
    exact (not_le_of_gt (Finset.mem_filter.mp hcloseJ).2.2)
      (Finset.mem_filter.mp htransverseJ).2.2
  have hcardSum : ∀ i ∈ active,
      (closePartners i).card + (transversePartners i).card =
        active.card := by
    intro i hi
    rw [← hunion i hi, Finset.card_union_of_disjoint (hdisjoint i)]
  have htransverseGe : ∀ i ∈ active,
      multiplicity ≤ 2 * (transversePartners i).card := by
    intro i hi
    have hclose' : 2 * (closePartners i).card ≤ multiplicity :=
      (hcloseLe i hi).trans hfineLe
    have hsum := hcardSum i hi
    rw [hactiveCard] at hsum
    omega
  let transversePairs : Finset (Fin F.card × Fin F.card) :=
    (active ×ˢ active).filter fun pair =>
      fineKappa ≤
        ‖wz1Cross (F.tube pair.1).direction
          (F.tube pair.2).direction‖
  have hpairSum : transversePairs.card =
      ∑ i ∈ active, (transversePartners i).card := by
    let firstSlices : Fin F.card → Finset (Fin F.card × Fin F.card) :=
      fun i => (transversePartners i).image fun j => (i, j)
    have hpairs : transversePairs = active.biUnion firstSlices := by
      ext pair
      constructor
      · intro hpair
        rcases Finset.mem_filter.mp hpair with ⟨hactivePair, htransverse⟩
        rcases Finset.mem_product.mp hactivePair with ⟨hfirst, hsecond⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨pair.1, hfirst, ?_⟩
        exact Finset.mem_image.mpr ⟨pair.2,
          Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp hsecond).2,
              htransverse⟩, rfl⟩
      · intro hpair
        rcases Finset.mem_biUnion.mp hpair with ⟨i, hi, hslice⟩
        rcases Finset.mem_image.mp hslice with ⟨j, hj, rfl⟩
        rcases Finset.mem_filter.mp hj with ⟨_, hjY, htransverse⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr
            ⟨hi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjY⟩⟩,
            htransverse⟩
    have hsliceDisjoint : ∀ i ∈ active, ∀ j ∈ active, i ≠ j →
        Disjoint (firstSlices i) (firstSlices j) := by
      intro i _ j _ hij
      rw [Finset.disjoint_left]
      intro pair hiPair hjPair
      rcases Finset.mem_image.mp hiPair with ⟨k, _, rfl⟩
      rcases Finset.mem_image.mp hjPair with ⟨l, _, hpair⟩
      exact hij (Prod.mk.inj hpair).1.symm
    rw [hpairs, Finset.card_biUnion hsliceDisjoint]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.card_image_of_injective _ (by simp [Function.Injective])]
  have hsum : ∑ i ∈ active, multiplicity ≤
      ∑ i ∈ active, 2 * (transversePartners i).card :=
    Finset.sum_le_sum fun i hi => htransverseGe i hi
  have hleft : ∑ _i ∈ active, multiplicity =
      active.card * multiplicity := by
    simp [Finset.sum_const]
  have hright : ∑ i ∈ active, 2 * (transversePartners i).card =
      2 * ∑ i ∈ active, (transversePartners i).card := by
    rw [Finset.mul_sum]
  rw [hleft, hright, hactiveCard, ← hpairSum] at hsum
  ring_nf at hsum ⊢
  exact hsum

end Kakeya.Assouad
