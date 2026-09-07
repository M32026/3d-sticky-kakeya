import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Algebra.Order.Chebyshev


/-!
# Energy-to-covering lemma

A combinatorial lemma used in the Kaufman projection theorem: if a finite set
S ⊂ ℝ has bounded γ-energy, then its δ-covering number is large.
-/

namespace Kakeya.Assouad

open Finset

/--
Energy-to-covering lemma.

Given a finite set `S ⊂ ℝ`, a set of `centers` whose δ-balls cover `S`,
and γ > 0, the γ-energy `E = Σ_{x,y∈S} |x-y|^(-γ)` satisfies
`E ≥ (N²/M - N) · (2δ)^(-γ)`, where `N = |S|` and `M = |centers|`.
-/
lemma energy_to_covering (S : Finset ℝ) (δ γ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (centers : Finset ℝ) (hcover : ∀ x ∈ S, ∃ c ∈ centers, |x - c| ≤ δ) :
    (∑ x ∈ S, ∑ y ∈ S, |x - y|^(-γ)) ≥
    (((S.card : ℝ)^2 / (centers.card : ℝ)) - (S.card : ℝ)) * (2 * δ)^(-γ) := by
  by_cases hS : S = ∅
  · rw [hS]
    simp
  · classical
    have hS_card_pos : 0 < S.card := by
      rw [Finset.card_pos]
      exact Finset.nonempty_iff_ne_empty.mpr hS
    have h_exists : ∃ (x : ℝ), x ∈ S := Finset.card_pos.mp hS_card_pos
    rcases h_exists with ⟨x, hx⟩

    have hcenters_ne_empty : centers ≠ ∅ := by
      rcases hcover x hx with ⟨c, hc, _⟩
      intro h
      rw [h] at hc
      simp at hc
    have hcenters_nonempty : centers.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hcenters_ne_empty
    have hM_pos : (centers.card : ℝ) > 0 := by
      have h : 0 < centers.card := Finset.card_pos.mpr hcenters_nonempty
      exact_mod_cast h

    -- Choose a center for each point
    let f : ℝ → ℝ := fun x =>
      if hx : x ∈ S then Classical.choose (hcover x hx) else 0
    have hf1 : ∀ x ∈ S, f x ∈ centers := by
      intro x hx
      simp [f, hx]
      exact (Classical.choose_spec (hcover x hx)).1
    have hf2 : ∀ x ∈ S, |x - f x| ≤ δ := by
      intro x hx
      simp [f, hx]
      exact (Classical.choose_spec (hcover x hx)).2

    let fiber : ℝ → Finset ℝ := fun c => S.filter (fun x => f x = c)

    have h_fiber_sub : ∀ c, fiber c ⊆ S := fun c => filter_subset _ _

    have h_fiber_cover : ∀ x ∈ S, x ∈ fiber (f x) := by
      intro x hx
      simp [fiber, hx]

    have h_union : centers.biUnion fiber = S := by
      apply Finset.ext
      intro x
      constructor
      · intro hx
        rcases Finset.mem_biUnion.mp hx with ⟨c, hc, hxc⟩
        exact h_fiber_sub c hxc
      · intro hx
        have h1 : f x ∈ centers := hf1 x hx
        have h2 : x ∈ fiber (f x) := h_fiber_cover x hx
        exact Finset.mem_biUnion.mpr ⟨f x, h1, h2⟩

    have h_disj : ∀ c1 ∈ centers, ∀ c2 ∈ centers, c1 ≠ c2 →
        Disjoint (fiber c1) (fiber c2) := by
      intro c1 _ c2 _ hne
      simp only [fiber, Finset.disjoint_left, mem_filter]
      intro x hx1 hx2
      have h1 : f x = c1 := hx1.2
      have h2 : f x = c2 := hx2.2
      have h3 : c1 = c2 := by rw [← h1, h2]
      exact hne h3

    have h_sum_card : ∑ c ∈ centers, (fiber c).card = S.card := by
      have h : (centers.biUnion fiber).card = ∑ c ∈ centers, (fiber c).card := by
        rw [Finset.card_biUnion h_disj]
      rw [← h, h_union]

    -- Triangle inequality helper
    have h_triangle : ∀ (a b : ℝ), |a + b| ≤ |a| + |b| := by
      intro a b
      have h1 : a + b ≤ |a| + |b| := by
        have h1a : a ≤ |a| := le_abs_self a
        have h1b : b ≤ |b| := le_abs_self b
        linarith
      have h2 : -(|a| + |b|) ≤ a + b := by
        have h2a : -|a| ≤ a := neg_abs_le a
        have h2b : -|b| ≤ b := neg_abs_le b
        linarith
      exact abs_le.mpr ⟨h2, h1⟩

    -- For x, y in the same fiber, |x - y| ≤ 2δ
    have h_dist : ∀ c x y, x ∈ fiber c → y ∈ fiber c → |x - y| ≤ 2 * δ := by
      intro c x y hx hy
      have hx' : x ∈ S := h_fiber_sub c hx
      have hy' : y ∈ S := h_fiber_sub c hy
      have hfx : f x = c := (mem_filter.mp hx).2
      have hfy : f y = c := (mem_filter.mp hy).2
      have h1 : |x - c| ≤ δ := by rw [← hfx]; exact hf2 x hx'
      have h2 : |y - c| ≤ δ := by rw [← hfy]; exact hf2 y hy'
      have h3 : |x - y| ≤ |x - c| + |y - c| := by
        have h4 : x - y = (x - c) + (c - y) := by ring
        rw [h4]
        have h5 : |(x - c) + (c - y)| ≤ |x - c| + |c - y| := h_triangle (x - c) (c - y)
        have h6 : |c - y| = |y - c| := by
          have h7 : c - y = -(y - c) := by ring
          rw [h7, abs_neg]
        have h8 : |(x - c) + (c - y)| ≤ |x - c| + |y - c| := by
          rw [h6] at h5
          exact h5
        exact h8
      linarith

    -- rpow monotonicity for negative exponent: 0 < a ≤ b → a^(-γ) ≥ b^(-γ)
    have h_rpow_dec : ∀ (a b : ℝ), 0 < a → a ≤ b → a^(-γ) ≥ b^(-γ) := by
      intro a b ha hab
      have hb_pos : 0 < b := by linarith
      have h_a_pos : 0 < a^(-γ) := by positivity
      have h_b_pos : 0 < b^(-γ) := by positivity
      have hlog_a : Real.log (a^(-γ)) = (-γ) * Real.log a := Real.log_rpow ha (-γ)
      have hlog_b : Real.log (b^(-γ)) = (-γ) * Real.log b := Real.log_rpow hb_pos (-γ)
      have hlog : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) (by linarith)
      have h4 : Real.log (a^(-γ)) ≥ Real.log (b^(-γ)) := by
        rw [hlog_a, hlog_b] <;> nlinarith
      exact (Real.log_le_log_iff h_b_pos h_a_pos).mp h4

    -- Lower bound for same-fiber pairs
    have h_bound : ∀ c x y, x ∈ fiber c → y ∈ fiber c → x ≠ y →
        |x - y|^(-γ) ≥ (2 * δ)^(-γ) := by
      intro c x y hx hy hxy
      have hdist : |x - y| ≤ 2 * δ := h_dist c x y hx hy
      have hpos : 0 < |x - y| := by
        apply abs_pos.mpr
        intro h
        exact hxy (by linarith)
      have hpos2 : 0 < 2 * δ := by linarith
      exact h_rpow_dec |x - y| (2 * δ) hpos hdist

    -- Restrict energy sum to same-fiber pairs
    let same_fiber_pairs : Finset (ℝ × ℝ) :=
      centers.biUnion fun c => (fiber c) ×ˢ (fiber c)

    have h_pair_disj : ∀ c1 ∈ centers, ∀ c2 ∈ centers, c1 ≠ c2 →
        Disjoint ((fiber c1) ×ˢ (fiber c1)) ((fiber c2) ×ˢ (fiber c2)) := by
      intro c1 _ c2 _ hne
      have h : Disjoint (fiber c1) (fiber c2) := h_disj c1 ‹_› c2 ‹_› hne
      exact Finset.disjoint_product.mpr (Or.inl h)

    have h_sum_product : (∑ x ∈ S, ∑ y ∈ S, |x - y|^(-γ)) =
        ∑ p ∈ S ×ˢ S, |p.1 - p.2|^(-γ) := by
      rw [Finset.sum_product] <;> rfl

    have h_subset : same_fiber_pairs ⊆ S ×ˢ S := by
      intro p hp
      rcases Finset.mem_biUnion.mp hp with ⟨c, _, hpc⟩
      have h1 : p.1 ∈ fiber c := (mem_product.mp hpc).1
      have h2 : p.2 ∈ fiber c := (mem_product.mp hpc).2
      exact mem_product.mpr ⟨h_fiber_sub c h1, h_fiber_sub c h2⟩

    have h_nonneg : ∀ p ∈ S ×ˢ S, 0 ≤ |p.1 - p.2|^(-γ) := by
      intro p _
      positivity

    have h_energy_ge : (∑ p ∈ S ×ˢ S, |p.1 - p.2|^(-γ)) ≥
        ∑ p ∈ same_fiber_pairs, |p.1 - p.2|^(-γ) :=
      Finset.sum_le_sum_of_subset_of_nonneg h_subset fun i _ _ => h_nonneg i ‹_›

    have h_sum_fibers : (∑ p ∈ same_fiber_pairs, |p.1 - p.2|^(-γ)) =
        ∑ c ∈ centers, ∑ p ∈ (fiber c) ×ˢ (fiber c), |p.1 - p.2|^(-γ) := by
      rw [Finset.sum_biUnion h_pair_disj] <;> rfl

    -- General fact: sum of X over off-diagonal pairs in s×s is (|s|²-|s|)·X
    have h_off_diag : ∀ (s : Finset ℝ) (X : ℝ),
        ∑ p ∈ s ×ˢ s, (if p.1 ≠ p.2 then X else 0) =
        ((s.card : ℝ)^2 - (s.card : ℝ)) * X := by
      intro s X
      have h_diag_card : ((s ×ˢ s).filter (fun p : ℝ × ℝ => p.1 = p.2)).card = s.card := by
        have h5 : (s ×ˢ s).filter (fun p : ℝ × ℝ => p.1 = p.2) = s.image (fun x => (x, x)) := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
          constructor
          · rintro ⟨h, h_eq⟩
            refine ⟨p.1, h.1, ?_⟩
            apply Prod.ext
            · simp
            · simp [h_eq]
          · rintro ⟨z, hz, h⟩
            have hpe : p = (z, z) := by
              have h' : z = p.1 ∧ z = p.2 := by simpa [Prod.ext_iff] using h
              apply Prod.ext
              · exact h'.1.symm
              · exact h'.2.symm
            have h1 : p.1 ∈ s := by rw [hpe] <;> exact hz
            have h2 : p.2 ∈ s := by rw [hpe] <;> exact hz
            have h3 : p.1 = p.2 := by rw [hpe] <;> rfl
            exact ⟨⟨h1, h2⟩, h3⟩
        rw [h5]
        rw [Finset.card_image_of_injective _ (fun x y h => by simpa using h)]
      have h_filter_ne : (s ×ˢ s).filter (fun p : ℝ × ℝ => p.1 ≠ p.2) =
          (s ×ˢ s) \ (s ×ˢ s).filter (fun p : ℝ × ℝ => p.1 = p.2) := by
        ext p
        simp [Finset.mem_sdiff]
        <;> tauto
      have h_disj : Disjoint ((s ×ˢ s).filter (fun p => p.1 ≠ p.2)) ((s ×ˢ s).filter (fun p => p.1 = p.2)) := by
        simp [Finset.disjoint_left] <;> tauto
      have h_sum_card : ((s ×ˢ s).filter (fun p => p.1 ≠ p.2)).card + ((s ×ˢ s).filter (fun p => p.1 = p.2)).card = (s ×ˢ s).card := by
        have h_union : (s ×ˢ s).filter (fun p => p.1 ≠ p.2) ∪ (s ×ˢ s).filter (fun p => p.1 = p.2) = s ×ˢ s := by
          ext p; simp <;> tauto
        rw [← Finset.card_union_of_disjoint h_disj, h_union]
      have h_card_real : (((s ×ˢ s).filter (fun p => p.1 ≠ p.2)).card : ℝ) =
          ((s ×ˢ s).card : ℝ) - (((s ×ˢ s).filter (fun p => p.1 = p.2)).card : ℝ) := by
        have h' : (((s ×ˢ s).filter (fun p => p.1 ≠ p.2)).card : ℝ) + (((s ×ˢ s).filter (fun p => p.1 = p.2)).card : ℝ) = ((s ×ˢ s).card : ℝ) := by
          exact_mod_cast h_sum_card
        linarith
      have h_sum : ∑ p ∈ s ×ˢ s, (if p.1 ≠ p.2 then X else 0) =
          (((s ×ˢ s).card : ℝ) - ((s ×ˢ s).filter (fun p => p.1 = p.2)).card : ℝ) * X := by
        have h_ite : ∑ p ∈ s ×ˢ s, (if p.1 ≠ p.2 then X else 0) =
            ∑ p ∈ (s ×ˢ s).filter (fun p : ℝ × ℝ => p.1 ≠ p.2), X := by
          rw [Finset.sum_ite]
          <;> simp
        rw [h_ite]
        have h_sum2 : ∑ p ∈ (s ×ˢ s).filter (fun p : ℝ × ℝ => p.1 ≠ p.2), X =
            ((s ×ˢ s).filter (fun p : ℝ × ℝ => p.1 ≠ p.2)).card * X := by
          rw [Finset.sum_const] <;> ring
        rw [h_sum2]
        rw [h_card_real] <;> ring
      rw [h_sum, h_diag_card, Finset.card_product]
      <;> norm_cast <;> ring

    -- Each fiber contributes at least N_c(N_c-1)(2δ)^(-γ)
    have h_fiber_energy : ∀ c ∈ centers,
        (∑ p ∈ (fiber c) ×ˢ (fiber c), |p.1 - p.2|^(-γ)) ≥
        ((fiber c).card : ℝ) * (((fiber c).card : ℝ) - 1) * (2 * δ)^(-γ) := by
      intro c hc
      have h1 : ∑ p ∈ (fiber c) ×ˢ (fiber c), |p.1 - p.2|^(-γ) ≥
          ∑ p ∈ (fiber c) ×ˢ (fiber c), if p.1 ≠ p.2 then (2 * δ)^(-γ) else 0 := by
        apply Finset.sum_le_sum
        intro p hp
        by_cases hne : p.1 ≠ p.2
        · have h1 : p.1 ∈ fiber c := (mem_product.mp hp).1
          have h2 : p.2 ∈ fiber c := (mem_product.mp hp).2
          simpa [hne] using h_bound c p.1 p.2 h1 h2 hne
        · simp [hne] <;> positivity
      have h2 := h_off_diag (fiber c) ((2 * δ)^(-γ))
      linarith

    have h_sum_ge : (∑ c ∈ centers, ∑ p ∈ (fiber c) ×ˢ (fiber c), |p.1 - p.2|^(-γ)) ≥
        ∑ c ∈ centers, (((fiber c).card : ℝ) * (((fiber c).card : ℝ) - 1) * (2 * δ)^(-γ)) := by
      apply Finset.sum_le_sum
      intro c hc
      exact h_fiber_energy c hc

    have h_algebra : ∑ c ∈ centers, (((fiber c).card : ℝ) * (((fiber c).card : ℝ) - 1) * (2 * δ)^(-γ)) =
        ((∑ c ∈ centers, ((fiber c).card : ℝ)^2) - (S.card : ℝ)) * (2 * δ)^(-γ) := by
      have h_factor : ∑ c ∈ centers, (((fiber c).card : ℝ) * (((fiber c).card : ℝ) - 1) * (2 * δ)^(-γ)) =
          (∑ c ∈ centers, ((fiber c).card : ℝ) * (((fiber c).card : ℝ) - 1)) * (2 * δ)^(-γ) := by
        rw [← Finset.sum_mul]
        <;> rfl
      rw [h_factor]
      have h3 : ∑ c ∈ centers, ((fiber c).card : ℝ) * (((fiber c).card : ℝ) - 1) =
          (∑ c ∈ centers, ((fiber c).card : ℝ)^2) - ∑ c ∈ centers, ((fiber c).card : ℝ) := by
        have h4 : ∀ c ∈ centers, ((fiber c).card : ℝ) * (((fiber c).card : ℝ) - 1) =
            ((fiber c).card : ℝ)^2 - ((fiber c).card : ℝ) := by
          intro c _
          ring
        rw [Finset.sum_congr rfl h4, Finset.sum_sub_distrib]
      rw [h3]
      have h_sum_card_real : ∑ c ∈ centers, ((fiber c).card : ℝ) = (S.card : ℝ) := by
        exact_mod_cast h_sum_card
      rw [h_sum_card_real] <;> ring

    -- Cauchy-Schwarz: Σ N_c² ≥ N²/M
    have h_cs : (S.card : ℝ)^2 ≤
        (centers.card : ℝ) * ∑ c ∈ centers, ((fiber c).card : ℝ)^2 := by
      have h : (∑ c ∈ centers, ((fiber c).card : ℝ)) ^ 2 ≤
          (centers.card : ℝ) * ∑ c ∈ centers, ((fiber c).card : ℝ)^2 :=
        sq_sum_le_card_mul_sum_sq
      have h_sum_card_real : ∑ c ∈ centers, ((fiber c).card : ℝ) = (S.card : ℝ) := by
        exact_mod_cast h_sum_card
      rw [h_sum_card_real] at h
      exact h

    have h_sum_sq_ge : ∑ c ∈ centers, ((fiber c).card : ℝ)^2 ≥
        (S.card : ℝ)^2 / (centers.card : ℝ) := by
      set X : ℝ := ∑ c ∈ centers, ((fiber c).card : ℝ)^2 with hX
      set M : ℝ := (centers.card : ℝ) with hM
      set N : ℝ := (S.card : ℝ) with hN
      have hM_pos' : 0 < M := hM_pos
      have h : N^2 ≤ M * X := h_cs
      have h7 : N^2 / M ≤ X := by
        have h8 : N^2 / M ≤ (M * X) / M := div_le_div_of_nonneg_right h (by linarith)
        have h9 : (M * X) / M = X := by
          have h10 : M ≠ 0 := hM_pos'.ne'
          simpa [h10] using mul_div_cancel_left X h10
        rw [h9] at h8
        exact h8
      simpa [hX, hM, hN] using h7

    have h1 : (∑ x ∈ S, ∑ y ∈ S, |x - y|^(-γ)) ≥
        ∑ p ∈ same_fiber_pairs, |p.1 - p.2|^(-γ) := by
      rw [h_sum_product]
      exact h_energy_ge
    have h2 : ∑ p ∈ same_fiber_pairs, |p.1 - p.2|^(-γ) ≥
        ((∑ c ∈ centers, ((fiber c).card : ℝ)^2) - (S.card : ℝ)) * (2 * δ)^(-γ) := by
      rw [h_sum_fibers]
      have h21 : (∑ c ∈ centers, ∑ p ∈ (fiber c) ×ˢ (fiber c), |p.1 - p.2|^(-γ)) ≥
          ((∑ c ∈ centers, ((fiber c).card : ℝ)^2) - (S.card : ℝ)) * (2 * δ)^(-γ) := by
        calc
          (∑ c ∈ centers, ∑ p ∈ (fiber c) ×ˢ (fiber c), |p.1 - p.2|^(-γ))
            ≥ ∑ c ∈ centers, (((fiber c).card : ℝ) * (((fiber c).card : ℝ) - 1) * (2 * δ)^(-γ)) := h_sum_ge
          _ = ((∑ c ∈ centers, ((fiber c).card : ℝ)^2) - (S.card : ℝ)) * (2 * δ)^(-γ) := h_algebra
      exact h21
    have h3 : ((∑ c ∈ centers, ((fiber c).card : ℝ)^2) - (S.card : ℝ)) * (2 * δ)^(-γ) ≥
        (((S.card : ℝ)^2 / (centers.card : ℝ)) - (S.card : ℝ)) * (2 * δ)^(-γ) := by
      have hX_pos : 0 < (2 * δ)^(-γ) := by positivity
      nlinarith [h_sum_sq_ge]
    linarith

end Kakeya.Assouad
