import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.SubfamilyTransfer

/-!
# Rectangle subfamilies indexed by a finite set
-/

namespace Kakeya.Cinematic

namespace RectangleSubfamily

def ofFinset {delta t : ℝ} (R : RectangleFamily delta t)
    (selected : Finset (Fin R.card)) : RectangleSubfamily R where
  card := selected.card
  embedding := (selected.orderEmbOfFin rfl).toEmbedding

@[simp]
lemma ofFinset_card {delta t : ℝ} (R : RectangleFamily delta t)
    (selected : Finset (Fin R.card)) :
    (ofFinset R selected).card = selected.card :=
  rfl

lemma ofFinset_embedding_mem {delta t : ℝ}
    (R : RectangleFamily delta t)
    (selected : Finset (Fin R.card))
    (i : Fin (ofFinset R selected).card) :
    (ofFinset R selected).embedding i ∈ selected :=
  Finset.orderEmbOfFin_mem selected rfl i

lemma ofFinset_embedding_surjective {delta t : ℝ}
    (R : RectangleFamily delta t)
    (selected : Finset (Fin R.card)) :
    ∀ i ∈ selected,
      ∃ j : Fin (ofFinset R selected).card,
        (ofFinset R selected).embedding j = i := by
  intro i hi
  have himage :
      Finset.image (ofFinset R selected).embedding Finset.univ =
        selected :=
    Finset.image_orderEmbOfFin_univ selected rfl
  have hi' :
      i ∈ Finset.image (ofFinset R selected).embedding Finset.univ := by
    rw [himage]
    exact hi
  rcases Finset.mem_image.mp hi' with ⟨j, _, hj⟩
  exact ⟨j, hj⟩

lemma ofFinset_nonempty {delta t : ℝ}
    {R : RectangleFamily delta t}
    {selected : Finset (Fin R.card)}
    (hselected : selected.Nonempty) :
    (ofFinset R selected).family.Nonempty := by
  change 0 < selected.card
  exact hselected.card_pos

lemma ofFinset_incomparable {delta t : ℝ}
    {R : RectangleFamily delta t}
    {family : Set C2Function} {comparison : ℝ}
    (hR : R.IsPairwiseIncomparable family comparison)
    (selected : Finset (Fin R.card)) :
    (ofFinset R selected).family.IsPairwiseIncomparable
      family comparison := by
  intro i j hij
  apply hR
  intro heq
  exact hij ((ofFinset R selected).embedding.injective heq)

end RectangleSubfamily

end Kakeya.Cinematic
