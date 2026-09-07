import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import Mathlib.Tactic

/-!
# 1D interval packing lemma for WZ1 trapezoid hierarchy

A finite family of pairwise d-separated intervals of length ≤ d, all
intersecting [-1, 1], has cardinality at most 2/d + 2.
-/

noncomputable section

namespace Kakeya.Assouad

open Finset Set

/--
For a d-separated nonempty finset of reals, the span max - min is at
least (card - 1) * d.
-/
lemma real_separated_span
    {S : Finset ℝ} {d : ℝ} (hd : 0 < d)
    (h_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → d ≤ |x - y|)
    (hne : S.Nonempty) :
    S.max' hne - S.min' hne ≥ ((S.card : ℝ) - 1) * d := by
  classical
  have h_main : ∀ (n : ℕ) (T : Finset ℝ) (hT : T.card = n)
      (hTne : T.Nonempty)
      (hT_sep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → d ≤ |x - y|),
      T.max' hTne - T.min' hTne ≥ ((n : ℝ) - 1) * d := by
    intro n
    induction n with
    | zero =>
      intro T hT hTne _
      exfalso
      rw [Finset.card_eq_zero] at hT
      rw [hT] at hTne
      simp at hTne
    | succ n' ih =>
      intro T hT hTne hT_sep
      by_cases h_n'_zero : n' = 0
      · -- card = 1
        subst h_n'_zero
        have h1 : T.card = 1 := hT
        rcases Finset.card_eq_one.mp h1 with ⟨x, hx⟩
        subst hx
        simp
        <;> norm_num
      · -- card ≥ 2
        have h_n'_pos : 0 < n' := Nat.pos_of_ne_zero h_n'_zero
        set m : ℝ := T.max' hTne with hm_def
        have hmem : m ∈ T := Finset.max'_mem T hTne
        set T' : Finset ℝ := T.erase m with hT'_def
        have hT'card : T'.card = n' := by
          rw [hT'_def, Finset.card_erase_of_mem hmem, hT] <;> omega
        have hT'pos : 0 < T'.card := by
          rw [hT'card] <;> exact h_n'_pos
        have hT'ne : T'.Nonempty := Finset.card_pos.mp hT'pos
        have hT'_sep : ∀ x ∈ T', ∀ y ∈ T', x ≠ y → d ≤ |x - y| := by
          intro x hx y hy hxy
          exact hT_sep x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy
        have h_ih := ih T' hT'card hT'ne hT'_sep
        set m' : ℝ := T'.max' hT'ne with hm'_def
        have hm'inT : m' ∈ T := Finset.mem_of_mem_erase (Finset.max'_mem T' hT'ne)
        have hne' : m ≠ m' := by
          intro h
          have h_cont : m ∈ T' := by
            rw [h] <;> exact Finset.max'_mem T' hT'ne
          have h : m ∉ T' := by
            simp [hT'_def]
          exact h h_cont
        have hgap : d ≤ |m - m'| := hT_sep m hmem m' hm'inT hne'
        have hle : m' ≤ m := Finset.le_max' T m' hm'inT
        have hgap' : m ≥ m' + d := by
          have h : |m - m'| = m - m' := by
            rw [abs_of_nonneg] <;> linarith
          rw [h] at hgap <;> linarith
        have hmin_eq : T.min' hTne = T'.min' hT'ne := by
          have h5 : T.min' hTne ≠ m := by
            intro h
            have h6 : ∀ y ∈ T, y = m := by
              intro y hy
              have h7 : T.min' hTne ≤ y := Finset.min'_le T y hy
              have h8 : y ≤ m := Finset.le_max' T y hy
              rw [h] at h7 <;> linarith
            have h9 : T.card = 1 := by
              have h10 : T = {m} := by
                ext y
                simp only [Finset.mem_singleton]
                constructor
                · exact h6 y
                · intro h11; rw [h11] <;> exact hmem
              rw [h10] <;> simp
            omega
          have h10 : T.min' hTne ∈ T' := by
            rw [hT'_def, Finset.mem_erase] <;> exact ⟨h5, Finset.min'_mem T hTne⟩
          have h11 : T'.min' hT'ne ≤ T.min' hTne :=
            Finset.min'_le T' (T.min' hTne) h10
          have h12 : T.min' hTne ≤ T'.min' hT'ne :=
            Finset.min'_le T (T'.min' hT'ne)
              (Finset.mem_of_mem_erase (Finset.min'_mem T' hT'ne))
          linarith
        rw [hmin_eq]
        have h_final : m - T'.min' hT'ne ≥ (((n' + 1 : ℕ) : ℝ) - 1) * d := by
          calc m - T'.min' hT'ne
              ≥ m' + d - T'.min' hT'ne := by linarith
            _ = (m' - T'.min' hT'ne) + d := by ring
            _ ≥ ((n' : ℝ) - 1) * d + d := by linarith [h_ih]
            _ = (n' : ℝ) * d := by ring
            _ = (((n' + 1 : ℕ) : ℝ) - 1) * d := by
              simp [Nat.cast_add] <;> ring
        exact h_final
  exact h_main S.card S rfl hne h_sep

/--
A d-separated finite subset of reals contained in [a, b] has cardinality
at most (b - a) / d + 1.
-/
lemma real_separated_card_bound
    {S : Finset ℝ} {d a b : ℝ} (hd : 0 < d) (h_ab : a ≤ b)
    (h_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → d ≤ |x - y|)
    (h_lo : ∀ x ∈ S, a ≤ x) (h_hi : ∀ x ∈ S, x ≤ b) :
    (S.card : ℝ) ≤ (b - a) / d + 1 := by
  by_cases hS : S = ∅
  · rw [hS]
    simp
    <;> have h : 0 ≤ (b - a) / d + 1 := by
      apply add_nonneg
      · apply div_nonneg <;> linarith
      · norm_num
    exact h
  have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
  let x_min := S.min' hne
  let x_max := S.max' hne
  have h_span : x_max - x_min ≥ ((S.card : ℝ) - 1) * d :=
    real_separated_span hd h_sep hne
  have h_lo' : a ≤ x_min := h_lo x_min (Finset.min'_mem S hne)
  have h_hi' : x_max ≤ b := h_hi x_max (Finset.max'_mem S hne)
  have h : ((S.card : ℝ) - 1) * d ≤ b - a := by linarith
  have h6 : (S.card : ℝ) - 1 ≤ (b - a) / d := by
    calc (S.card : ℝ) - 1
        = (((S.card : ℝ) - 1) * d) / d := by field_simp [hd.ne'] <;> ring
      _ ≤ (b - a) / d := by gcongr
  linarith

/--
A finite family of pairwise d-separated vertical trapezoids, each of length
≤ d and all intersecting [-1, 1], has cardinality at most 2/d + 2.

Maps each trapezoid to its left endpoint; the resulting real set is
d-separated and lies in [-1-d, 1]. Apply `real_separated_card_bound`.
-/
lemma separated_intervals_card_bound
    {s : Finset WZ1VerticalTrapezoid} {d : ℝ}
    (hd : 0 < d)
    (h_len : ∀ t ∈ s, t.length ≤ d)
    (h_sep : ∀ t ∈ s, ∀ u ∈ s, t ≠ u →
        ∀ z ∈ t.core, ∀ w ∈ u.core, d ≤ |z - w|)
    (h_intersect : ∀ t ∈ s, t.core ∩ Set.Icc (-1 : ℝ) 1 ≠ ∅) :
    (s.card : ℝ) ≤ 2 / d + 2 := by
  let S : Finset ℝ := Finset.image (fun t : WZ1VerticalTrapezoid => t.left) s
  have h_inj : Set.InjOn (fun t : WZ1VerticalTrapezoid => t.left) s := by
    intro t _ u _ heq
    by_contra hne
    have htl : t.left ∈ t.core := Set.left_mem_Icc.mpr t.left_lt_right.le
    have hul : u.left ∈ u.core := Set.left_mem_Icc.mpr u.left_lt_right.le
    have h_eq2 : t.left = u.left := by simpa using heq
    have h1 : d ≤ |t.left - u.left| :=
      h_sep t ‹t ∈ s› u ‹u ∈ s› hne t.left htl u.left hul
    rw [h_eq2] at h1
    simp at h1 <;> linarith
  have h_card : S.card = s.card := by
    rw [Finset.card_image_of_injOn h_inj]
  have h_sep_S : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → d ≤ |x - y| := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨t, htin, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨u, huin, rfl⟩
    have hne : t ≠ u := by
      intro h
      apply hxy
      rw [h]
    have htl : t.left ∈ t.core := Set.left_mem_Icc.mpr t.left_lt_right.le
    have hul : u.left ∈ u.core := Set.left_mem_Icc.mpr u.left_lt_right.le
    exact h_sep t htin u huin hne t.left htl u.left hul
  have h_lo : ∀ x ∈ S, -1 - d ≤ x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨t, htin, rfl⟩
    have h_nonempty : (t.core ∩ Set.Icc (-1 : ℝ) 1).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr (h_intersect t htin)
    rcases h_nonempty with ⟨z, hz⟩
    have hz1 : z ∈ t.core := hz.1
    have hz2 : z ∈ Set.Icc (-1 : ℝ) 1 := hz.2
    have h3 : -1 ≤ z := hz2.1
    have h4 : z ≤ t.right := (hz1 : z ∈ Set.Icc t.left t.right).2
    have h5 : t.right ≤ t.left + d := by
      have h6 : t.length ≤ d := h_len t htin
      have h7 : t.right = t.left + t.length := by
        simp [WZ1VerticalTrapezoid.length] <;> ring
      rw [h7]
      <;> linarith
    linarith
  have h_hi : ∀ x ∈ S, x ≤ 1 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨t, htin, rfl⟩
    have h_nonempty : (t.core ∩ Set.Icc (-1 : ℝ) 1).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr (h_intersect t htin)
    rcases h_nonempty with ⟨z, hz⟩
    have hz1 : z ∈ t.core := hz.1
    have hz2 : z ∈ Set.Icc (-1 : ℝ) 1 := hz.2
    have h3 : t.left ≤ z := (hz1 : z ∈ Set.Icc t.left t.right).1
    have h4 : z ≤ 1 := hz2.2
    linarith
  have h_ab : (-1 - d : ℝ) ≤ (1 : ℝ) := by linarith
  have h_main := real_separated_card_bound hd h_ab h_sep_S h_lo h_hi
  rw [h_card] at h_main
  have h_simp : (1 - (-1 - d)) / d + 1 = 2 / d + 2 := by
    field_simp [hd.ne'] <;> ring
  rw [h_simp] at h_main
  exact h_main

end Kakeya.Assouad
