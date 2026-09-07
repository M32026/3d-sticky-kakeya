import MyLeanRepo.Kakeya.Cinematic.Statements

/-!
# Rectangle subfamily API

Low-risk finite combinatorics supporting PYZ Lemma 24. The target constructs
a maximal pairwise incomparable indexed subfamily while preserving rectangle
identity through an embedding.
-/

namespace Kakeya.Cinematic

theorem rectangle_subfamily_selection :
    RectangleSubfamilySelectionStatement := by
  intro delta t family C hC R hR
  classical
  let Good : Finset (Fin R.card) → Prop := fun s =>
    ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (R.rectangle i).AreLambdaIncomparable (R.rectangle j) family C
  have h_empty : Good ∅ := by
    simp [Good]
  let GoodFinsets : Finset (Finset (Fin R.card)) :=
    Finset.univ.filter Good
  have h_nonempty : GoodFinsets.Nonempty := by
    refine' ⟨∅, _⟩
    simp [GoodFinsets, h_empty]
  rcases Finset.exists_max_image GoodFinsets (fun x : Finset (Fin R.card) => x.card) h_nonempty with
    ⟨s, hs_in, hs_max_card⟩
  have hs_good : Good s := (Finset.mem_filter.mp hs_in).2
  have hs_max : ∀ (t : Finset (Fin R.card)), s ⊆ t → Good t → s = t := by
    intro t hst ht
    have ht_in : t ∈ GoodFinsets := by
      simp only [GoodFinsets, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ht
    have h1 : t.card ≤ s.card := hs_max_card t ht_in
    have h2 : s.card ≤ t.card := Finset.card_le_card hst
    have h3 : s.card = t.card := by linarith
    exact Finset.eq_of_subset_of_card_le hst (by linarith)
  let e : Fin s.card ↪ Fin R.card :=
    (s.orderEmbOfFin rfl).toEmbedding
  let S : RectangleSubfamily R := {
    card := s.card,
    embedding := e
  }
  have h_image_eq : Finset.image e Finset.univ = s :=
    Finset.image_orderEmbOfFin_univ s rfl
  have h_surj : ∀ (x : Fin R.card), x ∈ s → ∃ (j : Fin s.card), e j = x := by
    intro x hx
    have h2 : x ∈ Finset.image e Finset.univ := by
      rw [h_image_eq]
      exact hx
    rcases Finset.mem_image.mp h2 with ⟨j, _, hj⟩
    exact ⟨j, hj⟩
  refine' ⟨S, _⟩
  constructor
  · -- S.family.CentersIn family
    intro j
    exact hR (e j)
  constructor
  · -- S.family.IsPairwiseIncomparable family C
    intro i j hne
    have h1 : e i ∈ s := Finset.orderEmbOfFin_mem s rfl i
    have h2 : e j ∈ s := Finset.orderEmbOfFin_mem s rfl j
    have h3 : e i ≠ e j := by
      intro h
      exact hne (e.inj' h)
    exact hs_good (e i) h1 (e j) h2 h3
  · -- covering condition
    intro i
    by_cases hi : i ∈ s
    · -- i ∈ s, find j such that e j = i
      rcases h_surj i hi with ⟨j, hj⟩
      refine' ⟨j, Or.inl _⟩
      exact hj.symm
    · -- i ∉ s, by maximality find k ∈ s comparable to i
      have h_not_good : ¬ Good (insert i s) := by
        intro h
        have h_ss : s ⊆ insert i s := Finset.subset_insert i s
        have h_eq : s = insert i s := hs_max (insert i s) h_ss h
        have : i ∈ s := by
          rw [h_eq]
          exact Finset.mem_insert_self i s
        exact hi this
      simp only [Good, not_forall] at h_not_good
      rcases h_not_good with ⟨a, ha, b, hb, hne, hcomp⟩
      have h_cases : a = i ∨ b = i := by
        by_contra h
        push Not at h
        have ha' : a ∈ s := by
          simp only [Finset.mem_insert] at ha
          tauto
        have hb' : b ∈ s := by
          simp only [Finset.mem_insert] at hb
          tauto
        have h_inc : (R.rectangle a).AreLambdaIncomparable (R.rectangle b) family C :=
          hs_good a ha' b hb' hne
        exact hcomp h_inc
      rcases h_cases with (h_eq1 | h_eq2)
      · -- a = i, b ∈ s
        have hb_not_i : b ≠ i := by
          intro h
          have h_contra : a = b := by
            rw [h_eq1, h]
          exact hne h_contra
        have hb_s : b ∈ s := by
          have h : b = i ∨ b ∈ s := by
            simp only [Finset.mem_insert] at hb
            exact hb
          rcases h with (h | h)
          · exfalso; exact hb_not_i h
          · exact h
        rcases h_surj b hb_s with ⟨j, hj⟩
        have h_main : (R.rectangle a).AreLambdaComparable (R.rectangle b) family C := by
          simpa [CurvilinearRectangle.AreLambdaIncomparable] using hcomp
        have h_main' : (R.rectangle i).AreLambdaComparable (R.rectangle b) family C := by
          rw [show a = i from h_eq1] at h_main
          exact h_main
        have h_emb : S.embedding j = b := by
          exact hj
        have h_rect : S.family.rectangle j = R.rectangle b := by
          have h : S.family.rectangle j = R.rectangle (S.embedding j) := by rfl
          rw [h, h_emb]
        refine' ⟨j, Or.inr _⟩
        rw [h_rect]
        exact h_main'
      · -- b = i, a ∈ s
        have ha_not_i : a ≠ i := by
          intro h
          have h_contra : a = b := by
            rw [h, h_eq2]
          exact hne h_contra
        have ha_s : a ∈ s := by
          have h : a = i ∨ a ∈ s := by
            simp only [Finset.mem_insert] at ha
            exact ha
          rcases h with (h | h)
          · exfalso; exact ha_not_i h
          · exact h
        rcases h_surj a ha_s with ⟨j, hj⟩
        have h_main : (R.rectangle a).AreLambdaComparable (R.rectangle b) family C := by
          simpa [CurvilinearRectangle.AreLambdaIncomparable] using hcomp
        have h_symm : (R.rectangle b).AreLambdaComparable (R.rectangle a) family C := by
          rcases h_main with ⟨U, hU_fam, hU_sub⟩
          refine' ⟨U, hU_fam, _⟩
          rw [Set.union_comm]
          exact hU_sub
        have h_symm' : (R.rectangle i).AreLambdaComparable (R.rectangle a) family C := by
          rw [show b = i from h_eq2] at h_symm
          exact h_symm
        have h_emb : S.embedding j = a := by
          exact hj
        have h_rect : S.family.rectangle j = R.rectangle a := by
          have h : S.family.rectangle j = R.rectangle (S.embedding j) := by rfl
          rw [h, h_emb]
        refine' ⟨j, Or.inr _⟩
        rw [h_rect]
        exact h_symm'

end Kakeya.Cinematic
