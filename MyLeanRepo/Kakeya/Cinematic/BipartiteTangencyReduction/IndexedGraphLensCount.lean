import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.IndexedGraphLensCountInputs

/-!
# Count an indexed family of non-overlapping graph lenses

Given a finite index set `S` and an `S`-indexed family of graph lenses whose
sides lie in a fixed pseudo-circle curve family and whose distinct indices give
non-overlapping lenses, the Marcus--Tardos graph-lens bound controls `S.card`.

The proof is pure finite packaging: pairwise non-overlap forces the indexed lens
map to be injective, so its image finset has the same cardinality and inherits
the side-membership and non-overlap hypotheses required by the supplied bound.
-/

namespace Kakeya.Cinematic

theorem indexed_graph_lens_count :
    IndexedGraphLensCountStatement := by
  classical
  intro C h_bound
  intro ι _ S curves h_family lens h_sides h_nonoverlap
  let lenses : Finset GraphLens := Finset.image lens S.attach
  have h_inj : Function.Injective lens := by
    intro i j h
    by_contra hne
    have h1 : (lens i).Nonoverlap (lens j) := h_nonoverlap i j hne
    have h2 : ¬(lens i).Overlap (lens j) := h1
    have h3 : (lens i).Overlap (lens i) := by
      constructor
      · exact Or.inl rfl
      · have h4 : max ((lens i).left : ℝ) (lens i).left = (lens i).left := by simp
        have h5 : min ((lens i).right : ℝ) (lens i).right = (lens i).right := by simp
        rw [h4, h5]
        exact (lens i).left_lt_right
    have h4 : (lens i).Overlap (lens j) := by
      rw [←h]
      exact h3
    exact h2 h4
  have h_sides' : ∀ L ∈ lenses, L.f ∈ curves ∧ L.g ∈ curves := by
    intro L hL
    have hL' : L ∈ Finset.image lens S.attach := hL
    rcases Finset.mem_image.mp hL' with ⟨i, _, rfl⟩
    exact h_sides i
  have h_nonoverlap' : ∀ L₁ ∈ lenses, ∀ L₂ ∈ lenses, L₁ ≠ L₂ → L₁.Nonoverlap L₂ := by
    intro L₁ hL₁ L₂ hL₂ hne
    have hL₁' : L₁ ∈ Finset.image lens S.attach := hL₁
    have hL₂' : L₂ ∈ Finset.image lens S.attach := hL₂
    rcases Finset.mem_image.mp hL₁' with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp hL₂' with ⟨j, _, rfl⟩
    have hij : i ≠ j := by
      intro h
      rw [h] at hne
      exact hne rfl
    exact h_nonoverlap i j hij
  have h_main := h_bound curves h_family lenses h_sides' h_nonoverlap'
  have h_card : lenses.card = S.card := by
    have h6 : lenses.card = S.attach.card :=
      Finset.card_image_of_injective S.attach h_inj
    rw [h6, Finset.card_attach]
  rw [h_card] at h_main
  exact h_main

end Kakeya.Cinematic
