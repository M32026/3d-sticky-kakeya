import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12

/-!
# A strict full fiber retaining the global selected-index fraction

The derived geometric parent of a literal partitioning cover partitions both
the ambient fine indices and any selected set of fine indices.  Therefore a
global cardinality-retention fraction is attained on at least one complete
strict full fiber.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
Select one parent for which the selected indices inside its strict full fiber
retain at least the global indexed-cardinality fraction.

The parent function is the one derived from literal full-fiber membership and
doubled-fiber disjointness.  No assigned-fiber structure is used.
-/
theorem pure_wz2_exists_full_fiber_retention_parent
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (hrho : 0 ≤ rho)
    (hfineNonempty : fine.Nonempty)
    (selected : Finset (Fin fine.card))
    (weight : ENNReal)
    (hglobal :
      weight * fine.enncard ≤ (selected.card : ENNReal)) :
    ∃ parent : Fin coarse.card,
      weight *
          wz2PaperOrdinaryFullFiberCount fine coarse parent ≤
        ((selected.filter fun source =>
          cover.parent source = parent).card : ENNReal) := by
  let ambientCount : Fin coarse.card → ENNReal := fun parent =>
    wz2PaperOrdinaryFullFiberCount fine coarse parent
  let selectedCount : Fin coarse.card → ENNReal := fun parent =>
    ((selected.filter fun source =>
      cover.parent source = parent).card : ENNReal)
  let source : Fin fine.card := ⟨0, hfineNonempty⟩
  rcases cover.covers source with ⟨occupied, _hsource⟩
  letI : Nonempty (Fin coarse.card) := ⟨occupied⟩
  have hambientSum :
      (∑ parent : Fin coarse.card, ambientCount parent) =
        fine.enncard := by
    calc
      (∑ parent : Fin coarse.card, ambientCount parent) =
          ∑ parent : Fin coarse.card,
            (((Finset.univ : Finset (Fin fine.card)).filter fun index =>
              cover.parent index = parent).card : ENNReal) := by
        apply Finset.sum_congr rfl
        intro parent _
        simp only [ambientCount, wz2PaperOrdinaryFullFiberCount]
        have hindices :
            wz2PaperOrdinaryFullFiberIndices fine coarse parent =
              (Finset.univ : Finset (Fin fine.card)).filter fun index =>
                cover.parent index = parent := by
          ext index
          rw [cover.mem_fullFiber_iff_parent_eq hrho]
          simp
        rw [hindices]
      _ = (fine.card : ENNReal) := by
        rw [← Nat.cast_sum]
        exact_mod_cast
          ((Finset.sum_card_fiberwise_eq_card_filter
            (Finset.univ : Finset (Fin fine.card))
            (Finset.univ : Finset (Fin coarse.card))
            cover.parent).trans (by simp))
      _ = fine.enncard := rfl
  have hselectedSum :
      (∑ parent : Fin coarse.card, selectedCount parent) =
        (selected.card : ENNReal) := by
    rw [← Nat.cast_sum]
    exact_mod_cast
      ((Finset.sum_card_fiberwise_eq_card_filter
        selected
        (Finset.univ : Finset (Fin coarse.card))
        cover.parent).trans (by simp))
  by_contra hnone
  push Not at hnone
  have hstrict :
      ∀ parent : Fin coarse.card,
        selectedCount parent <
          weight * ambientCount parent := by
    intro parent
    exact hnone parent
  have hsumStrict :
      (∑ parent : Fin coarse.card, selectedCount parent) <
        ∑ parent : Fin coarse.card,
          weight * ambientCount parent := by
    exact
      ENNReal.sum_lt_sum_of_nonempty
        (Finset.univ_nonempty : (Finset.univ :
          Finset (Fin coarse.card)).Nonempty)
        (fun parent _ => hstrict parent)
  have hright :
      (∑ parent : Fin coarse.card,
          weight * ambientCount parent) =
        weight * fine.enncard := by
    rw [← Finset.mul_sum, hambientSum]
  rw [hselectedSum, hright] at hsumStrict
  exact (not_lt_of_ge hglobal) hsumStrict

end Kakeya.Assouad

end
