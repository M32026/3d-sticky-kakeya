import MyLeanRepo.Kakeya.Assouad.WZ1.MaximalSeparated

/-!
# Finite maximal nets with a canonical quotient map

A maximal separated subset of a finite index type supplies a quotient map
from every index to a nearby center.  The quotient fixes every center, hence
is surjective.  This is the finite combinatorial layer used before selecting
whole actual parent fibers.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- A finite separated net together with its canonical nearby-center quotient. -/
structure WZ2FiniteMaximalQuotientNetData
    (indexCount : ℕ)
    (distance : Fin indexCount → Fin indexCount → ℝ)
    (radius : ℝ) where
  centers : Finset (Fin indexCount)
  centers_nonempty : centers.Nonempty
  centerEmbedding :
    Fin centers.card ↪ Fin indexCount
  centerEmbedding_eq :
    centerEmbedding =
      (centers.orderEmbOfFin rfl).toEmbedding
  centers_separated :
    ∀ first second : Fin centers.card,
      first ≠ second →
        radius <
          distance
            (centerEmbedding first)
            (centerEmbedding second)
  center : Fin indexCount → Fin centers.card
  center_close :
    ∀ index,
      distance index (centerEmbedding (center index)) ≤ radius
  center_fixed :
    ∀ centerIndex,
      center (centerEmbedding centerIndex) = centerIndex
  center_surjective :
    Function.Surjective center

/--
Construct a maximal separated net on a nonempty finite type.

No triangle inequality is needed.  Symmetry and zero diagonal suffice for
the maximal separated relation and for proving that every center is fixed by
the quotient map.
-/
theorem wz2_finite_maximal_quotient_net
    (indexCount : ℕ)
    (indexCountPos : 0 < indexCount)
    (distance : Fin indexCount → Fin indexCount → ℝ)
    (distanceSymmetric :
      ∀ first second,
        distance first second = distance second first)
    (distanceSelf :
      ∀ index, distance index index = 0)
    (radius : ℝ)
    (radiusPos : 0 < radius) :
    Nonempty
      (WZ2FiniteMaximalQuotientNetData
        indexCount distance radius) := by
  let separated :
      Fin indexCount → Fin indexCount → Prop :=
    fun first second =>
      radius < distance first second
  have separatedSymmetric :
      ∀ {first second},
        separated first second →
          separated second first := by
    intro first second hseparated
    change radius < distance second first
    rw [distanceSymmetric]
    exact hseparated
  have separatedCardinality :
      ∀ indices : Finset (Fin indexCount),
        (∀ index ∈ indices, True) →
        (∀ first ∈ indices,
          ∀ second ∈ indices,
            first ≠ second →
              separated first second) →
        indices.card ≤ indexCount := by
    intro indices _ _
    simpa using
      Finset.card_le_card
        (show indices ⊆
            (Finset.univ : Finset (Fin indexCount)) by
          exact Finset.subset_univ indices)
  rcases
      exists_maximal_separated
        (fun _ : Fin indexCount => True)
        separated separatedSymmetric
        indexCount separatedCardinality
    with
    ⟨centers, _centersEligible,
      centersSeparated, centersCover⟩
  have centersNonempty : centers.Nonempty := by
    let index : Fin indexCount :=
      ⟨0, indexCountPos⟩
    rcases centersCover index trivial with
      ⟨center, centerMem, _⟩
    exact ⟨center, centerMem⟩
  let centerEquiv :
      Fin centers.card ≃ centers :=
    (centers.orderIsoOfFin rfl).toEquiv
  let centerEmbedding :
      Fin centers.card ↪ Fin indexCount :=
    (centers.orderEmbOfFin rfl).toEmbedding
  have nearbyCenter :
      ∀ index : Fin indexCount,
        ∃ centerIndex : Fin centers.card,
          distance index
              (centerEmbedding centerIndex) ≤ radius := by
    intro index
    rcases centersCover index trivial with
      ⟨center, centerMem, hcenter⟩
    let centerIndex : Fin centers.card :=
      centerEquiv.symm ⟨center, centerMem⟩
    refine ⟨centerIndex, ?_⟩
    have centerEmbeddingEq :
        centerEmbedding centerIndex = center := by
      exact
        congrArg Subtype.val
          (centerEquiv.apply_symm_apply
            ⟨center, centerMem⟩)
    rw [centerEmbeddingEq]
    rcases hcenter with hself | hnotSeparated
    · rw [hself, distanceSelf]
      exact radiusPos.le
    · exact le_of_not_gt hnotSeparated
  let center :
      Fin indexCount → Fin centers.card :=
    fun index => Classical.choose (nearbyCenter index)
  have centerClose :
      ∀ index,
        distance index
            (centerEmbedding (center index)) ≤ radius :=
    fun index =>
      Classical.choose_spec (nearbyCenter index)
  have centersSeparated' :
      ∀ first second : Fin centers.card,
        first ≠ second →
          radius <
            distance
              (centerEmbedding first)
              (centerEmbedding second) := by
    intro first second hne
    have firstMem :
        centerEmbedding first ∈ centers :=
      Finset.orderEmbOfFin_mem centers rfl first
    have secondMem :
        centerEmbedding second ∈ centers :=
      Finset.orderEmbOfFin_mem centers rfl second
    have embeddingNe :
        centerEmbedding first ≠
          centerEmbedding second :=
      centerEmbedding.injective.ne hne
    exact
      centersSeparated
        (centerEmbedding first) firstMem
        (centerEmbedding second) secondMem
        embeddingNe
  have centerFixed :
      ∀ centerIndex,
        center (centerEmbedding centerIndex) =
          centerIndex := by
    intro centerIndex
    by_contra hne
    have hseparated :=
      centersSeparated'
        centerIndex
        (center (centerEmbedding centerIndex))
        (fun heq => hne heq.symm)
    exact
      (not_lt_of_ge
        (centerClose
          (centerEmbedding centerIndex)))
        hseparated
  have centerSurjective :
      Function.Surjective center := by
    intro centerIndex
    exact
      ⟨centerEmbedding centerIndex,
        centerFixed centerIndex⟩
  exact
    ⟨{
      centers := centers
      centers_nonempty := centersNonempty
      centerEmbedding := centerEmbedding
      centerEmbedding_eq := rfl
      centers_separated := centersSeparated'
      center := center
      center_close := centerClose
      center_fixed := centerFixed
      center_surjective := centerSurjective
    }⟩

end Kakeya.Assouad

end
