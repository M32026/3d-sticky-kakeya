import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.BlockStructure
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.DyadicDecomposition
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.Definitions
import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.LeaderConfig
import Mathlib.Tactic
import Mathlib.Data.Finset.Card

/-!
# Transition-spanning lemma for Marcus-Tardos

If all elements of S precede all elements of T in a nodup list A,
then at most one dyadic block at any level contains elements from both S and T.

## Key result
- `at_most_one_block_spans_transition`: at most one block spans S/T boundary
-/

namespace MarcusTardos.TransitionSpanning

open BigOperators Finset LeaderConfig

variable {α : Type*} [DecidableEq α]

/-- Helper: restrict S/T to a sublist and preserve S-before-T ordering. -/
private lemma restrict_to_sublist {A B : List α} (hA : A.Nodup) (_hB : B.Nodup)
    (h_sub : B.Sublist A) (S T : Finset α)
    (hST : ∀ s ∈ S, ∀ t ∈ T, posOf s A < posOf t A) :
    ∀ s ∈ S ∩ B.toFinset, ∀ t ∈ T ∩ B.toFinset, posOf s B < posOf t B := by
  intro s hs t ht
  have hsS : s ∈ S := (Finset.mem_inter.mp hs).1
  have htT : t ∈ T := (Finset.mem_inter.mp ht).1
  have hsB : s ∈ B := by simpa [List.mem_toFinset] using (Finset.mem_inter.mp hs).2
  have htB : t ∈ B := by simpa [List.mem_toFinset] using (Finset.mem_inter.mp ht).2
  have hne : s ≠ t := by
    intro h
    have hst : s ∈ T := h ▸ htT
    have h_contra : posOf s A < posOf s A := hST s hsS s hst
    exact lt_irrefl _ h_contra
  have h1 : posOf s A < posOf t A := hST s hsS t htT
  exact (posOf_sublist_lt h_sub hA hsB htB hne).mpr h1

/-- Helper: a block in half L contains S and T elements iff it contains
    the restricted SL and TL elements. -/
private lemma block_span_iff {L : List α} (S T : Finset α) (s : List Bool)
    (hS_block : ∃ x ∈ S, x ∈ block L s) (hT_block : ∃ y ∈ T, y ∈ block L s)
    (SL TL : Finset α) (hSL : SL = S ∩ L.toFinset) (hTL : TL = T ∩ L.toFinset) :
    (∃ x ∈ SL, x ∈ block L s) ∧ (∃ y ∈ TL, y ∈ block L s) := by
  rcases hS_block with ⟨x, hxS, hxB⟩
  rcases hT_block with ⟨y, hyT, hyB⟩
  have hxL : x ∈ L := (block_sublist L s).subset hxB
  have hyL : y ∈ L := (block_sublist L s).subset hyB
  have hxSL : x ∈ SL := by
    rw [hSL]
    exact Finset.mem_inter.mpr ⟨hxS, by simpa [List.mem_toFinset] using hxL⟩
  have hyTL : y ∈ TL := by
    rw [hTL]
    exact Finset.mem_inter.mpr ⟨hyT, by simpa [List.mem_toFinset] using hyL⟩
  exact ⟨⟨x, hxSL, hxB⟩, ⟨y, hyTL, hyB⟩⟩

/-! ### Transition-spanning lemma -/

/--
If all elements of `S` precede all elements of `T` in a nodup list `A`,
then at most one dyadic block at level `l` contains elements from both `S` and `T`.
-/
lemma at_most_one_block_spans_transition {A : List α} (hA : A.Nodup) (l : ℕ)
    (S T : Finset α) (hS : S ⊆ A.toFinset) (hT : T ⊆ A.toFinset)
    (hST : ∀ s ∈ S, ∀ t ∈ T, posOf s A < posOf t A) :
    ∃ (s0 : List Bool), ∀ (s : List Bool), s.length = l →
      (∃ x ∈ S, x ∈ block A s) → (∃ y ∈ T, y ∈ block A s) → s = s0 := by
  induction l generalizing A S T hS hT hST with
  | zero =>
    refine' ⟨[], _⟩
    intro s hs _ _
    simpa [List.length] using hs
  | succ l ih =>
    let L := leftHalf A
    let R := rightHalf A
    let k := A.length / 2
    let SL := S ∩ L.toFinset
    let TL := T ∩ L.toFinset
    let SR := S ∩ R.toFinset
    let TR := T ∩ R.toFinset
    have hL_nodup : L.Nodup := hA.sublist (List.take_sublist k A)
    have hR_nodup : R.Nodup := hA.sublist (List.drop_sublist k A)
    have hST_L := restrict_to_sublist hA hL_nodup (List.take_sublist k A) S T hST
    have hST_R := restrict_to_sublist hA hR_nodup (List.drop_sublist k A) S T hST
    rcases ih hL_nodup SL TL (by simp [SL]) (by simp [TL]) hST_L with ⟨sL, hL_result⟩
    rcases ih hR_nodup SR TR (by simp [SR]) (by simp [TR]) hST_R with ⟨sR, hR_result⟩
    by_cases hL_spans : ∃ (s : List Bool), s.length = l ∧
        (∃ x ∈ SL, x ∈ block L s) ∧ (∃ y ∈ TL, y ∈ block L s)
    · -- Left half has a spanning block
      rcases hL_spans with ⟨sL', hsl', hxL, hyL⟩
      have h_sL_eq : sL = sL' := (hL_result sL' hsl' hxL hyL).symm
      refine' ⟨false :: sL', _⟩
      intro s hs hS_block hT_block
      cases s with
      | nil => simp at hs
      | cons b s' =>
        have hs' : s'.length = l := by simp [List.length] at hs <;> omega
        cases b
        · -- b = false: left block
          have h_span := block_span_iff S T s' hS_block hT_block SL TL rfl rfl
          have h_eq : s' = sL := hL_result s' hs' h_span.1 h_span.2
          have h_final : s' = sL' := by rw [h_eq, h_sL_eq]
          rw [h_final]
        · -- b = true: right block, impossible
          rcases hyL with ⟨yL, hyL_TL, hyL_B⟩
          rcases hS_block with ⟨x, hxS, hxB⟩
          have hxR : x ∈ R := (block_sublist R s').subset hxB
          have hyL_in_L : yL ∈ L := (block_sublist L sL').subset hyL_B
          have hyL_T : yL ∈ T := (Finset.mem_inter.mp hyL_TL).1
          have h1 : posOf x A < posOf yL A := hST x hxS yL hyL_T
          have hL_eq : L = List.take k A := by
            dsimp only [L, leftHalf, k]
          have hR_eq : R = List.drop k A := by
            dsimp only [R, rightHalf, k]
          have h2 : posOf yL A < k := posOf_lt_of_mem_take hA (by rw [hL_eq] at hyL_in_L; exact hyL_in_L)
          have h3 : k ≤ posOf x A := posOf_ge_of_mem_drop hA (by rw [hR_eq] at hxR; exact hxR)
          omega
    · -- Left half has no spanning block
      by_cases hR_spans : ∃ (s : List Bool), s.length = l ∧
          (∃ x ∈ SR, x ∈ block R s) ∧ (∃ y ∈ TR, y ∈ block R s)
      · -- Right half has a spanning block
        rcases hR_spans with ⟨sR', hsr', hxR, hyR⟩
        have h_sR_eq : sR = sR' := (hR_result sR' hsr' hxR hyR).symm
        refine' ⟨true :: sR', _⟩
        intro s hs hS_block hT_block
        cases s with
        | nil => simp at hs
        | cons b s' =>
          have hs' : s'.length = l := by simp [List.length] at hs <;> omega
          cases b
          · -- b = false: left block, impossible by hL_spans
            have h_span := block_span_iff S T s' hS_block hT_block SL TL rfl rfl
            exact False.elim (hL_spans ⟨s', hs', h_span.1, h_span.2⟩)
          · -- b = true: right block
            have h_span := block_span_iff S T s' hS_block hT_block SR TR rfl rfl
            have h_eq : s' = sR := hR_result s' hs' h_span.1 h_span.2
            have h_final : s' = sR' := by rw [h_eq, h_sR_eq]
            rw [h_final]
      · -- Neither half spans
        refine' ⟨[], _⟩
        intro s hs hS_block hT_block
        cases s with
        | nil => simp at hs
        | cons b s' =>
          have hs' : s'.length = l := by simp [List.length] at hs <;> omega
          cases b
          · -- b = false: impossible
            have h_span := block_span_iff S T s' hS_block hT_block SL TL rfl rfl
            exact False.elim (hL_spans ⟨s', hs', h_span.1, h_span.2⟩)
          · -- b = true: impossible
            have h_span := block_span_iff S T s' hS_block hT_block SR TR rfl rfl
            exact False.elim (hR_spans ⟨s', hs', h_span.1, h_span.2⟩)

end MarcusTardos.TransitionSpanning
