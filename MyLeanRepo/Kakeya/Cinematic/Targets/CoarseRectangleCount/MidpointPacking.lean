import MyLeanRepo.Kakeya.Cinematic.Statements

/-!
# Midpoint packing bound

A 1D packing lemma: finitely many points in [a,b] pairwise separated by more
than s have cardinality at most (b-a)/s + 1.

This is identical to `point_packing_bound` in RectanglePacking.lean, but
reproduced here because target files do not import each other.
-/

namespace Kakeya.Cinematic

lemma midpoint_packing_bound {s : ℝ} (hs : 0 < s) {a b : ℝ} (hab : a ≤ b)
    (points : Finset ℝ)
    (hsub : ∀ x ∈ points, x ∈ Set.Icc a b)
    (hsep : ∀ x ∈ points, ∀ y ∈ points, x ≠ y → |x - y| > s) :
    (points.card : ℝ) ≤ (b - a) / s + 1 := by
  classical
  have h_main : ∀ (n : ℕ),
      ∀ (T : Finset ℝ), T.card = n →
        ∀ (c e : ℝ), c ≤ e →
          (∀ x ∈ T, x ∈ Set.Icc c e) →
          (∀ x ∈ T, ∀ y ∈ T, x ≠ y → |x - y| > s) →
          (T.card : ℝ) ≤ (e - c) / s + 1 := by
    intro n
    induction n with
    | zero =>
      intro T hT c e hce _ _
      have h_empty : T = ∅ := Finset.card_eq_zero.mp hT
      rw [h_empty]
      have h_nonneg : 0 ≤ e - c := by linarith
      have h_div : 0 ≤ (e - c) / s := by positivity
      simp <;> linarith
    | succ n ih =>
      intro T hT c e hce hT_sub hT_sep
      have hne : T.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        by_contra h
        rw [h] at hT
        simp at hT
      let m := Finset.min' T hne
      have hm_in : m ∈ T := Finset.min'_mem T hne
      have hm_min : ∀ x ∈ T, m ≤ x := fun x hx => Finset.min'_le T x hx
      let T' := T.erase m
      have h_card' : T'.card = n := by
        rw [Finset.card_erase_of_mem hm_in, hT]
        simp
      by_cases hT'_empty : T' = ∅
      · have h2 : T ⊆ {m} := by
          intro x hx
          by_cases h3 : x = m
          · exact h3 ▸ Finset.mem_singleton_self m
          · have h4 : x ∈ T' := by
              dsimp only [T']; exact Finset.mem_erase.mpr ⟨h3, hx⟩
            rw [hT'_empty] at h4; simp at h4
        have h3 : {m} ⊆ T := by
          intro x hx; rw [Finset.mem_singleton.mp hx]; exact hm_in
        have hT_eq : T = {m} := Finset.Subset.antisymm h2 h3
        rw [hT_eq]
        have h_nonneg : 0 ≤ e - c := by linarith
        have h_div : 0 ≤ (e - c) / s := by positivity
        simp <;> linarith
      · have hne' : T'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT'_empty
        have h_above : ∀ x ∈ T', x > m + s := by
          intro x hx
          have h_xinT : x ∈ T := Finset.mem_of_mem_erase hx
          have h_xne_m : x ≠ m := (Finset.mem_erase.mp hx).1
          have h_sep' : |x - m| > s := hT_sep x h_xinT m hm_in h_xne_m
          have h_xge_m : m ≤ x := hm_min x h_xinT
          have h_xsub_m : 0 ≤ x - m := by linarith
          have h_abs : |x - m| = x - m := abs_of_nonneg h_xsub_m
          rw [h_abs] at h_sep'; linarith
        obtain ⟨x, hx⟩ := hne'
        have h_xinT : x ∈ T := Finset.mem_of_mem_erase hx
        have h_xle_e : x ≤ e := (hT_sub x h_xinT).2
        have h_md_le_e : m + s ≤ e := by have h : m + s < x := h_above x hx; linarith
        have hT'_sub : ∀ x ∈ T', x ∈ Set.Icc (m + s) e := by
          intro x hx
          have h_xinT : x ∈ T := Finset.mem_of_mem_erase hx
          have h_xle_e : x ≤ e := (hT_sub x h_xinT).2
          have h_xge : m + s < x := h_above x hx
          exact ⟨by linarith, h_xle_e⟩
        have hT'_sep : ∀ x ∈ T', ∀ y ∈ T', x ≠ y → |x - y| > s := by
          intro x hx y hy hxy
          exact hT_sep x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy
        have h_ih' : (T'.card : ℝ) ≤ (e - (m + s)) / s + 1 :=
          ih T' h_card' (m + s) e h_md_le_e hT'_sub hT'_sep
        have h1 : (T.card : ℝ) = (T'.card : ℝ) + 1 := by
          rw [h_card', hT]
          norm_cast
        rw [h1]
        have hmc : m ≥ c := (hT_sub m hm_in).1
        have h_alg : (e - (m + s)) / s + 1 + 1 ≤ (e - c) / s + 1 := by
          have h_step1 : (e - (m + s)) / s + 1 + 1 = (e - m) / s + 1 := by
            have h : (e - (m + s)) / s = (e - m) / s - 1 := by
              field_simp [hs.ne'] <;> ring
            rw [h]; ring
          rw [h_step1]
          have h5 : e - m ≤ e - c := by linarith
          have h6 : (e - m) / s ≤ (e - c) / s := by gcongr
          linarith
        linarith
  exact h_main points.card points rfl a b hab hsub hsep

end Kakeya.Cinematic
