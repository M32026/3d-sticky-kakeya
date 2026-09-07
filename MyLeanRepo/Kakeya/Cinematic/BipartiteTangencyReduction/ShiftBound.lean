import MyLeanRepo.Kakeya.Cinematic.Geometry

/-!
# Small shift bound for finite function families

Given a finite family `F` and `K ≥ 1`, there exists `epsilon' > 0` such that
any shift function with `|shift f| ≤ epsilon'` for all `f ∈ F` satisfies
`|shift f - shift g| < c2Distance f g / (6 * K)` for all distinct `f, g ∈ F`.
-/

namespace Kakeya.Cinematic

lemma exists_epsilon_for_shift_bound
    (F : FiniteFunctionFamily) (K : ℝ) (hK : 1 ≤ K) :
    ∃ epsilon' : ℝ, 0 < epsilon' ∧
      ∀ (shift : C2Function → ℝ),
        (∀ f ∈ F.carrier, |shift f| ≤ epsilon') →
        ∀ f ∈ F.carrier, ∀ g ∈ F.carrier, f ≠ g →
          |shift f - shift g| < c2Distance f g / (6 * K) := by
  by_cases h_card : F.toFinset.card ≤ 1
  · -- Vacuously true when there is at most one function
    refine ⟨1, by norm_num, fun shift _ f hf g hg hfg => ?_⟩
    have h1 : f ∈ F.toFinset := by
      simpa [FiniteFunctionFamily.toFinset, Set.Finite.mem_toFinset] using hf
    have h2 : g ∈ F.toFinset := by
      simpa [FiniteFunctionFamily.toFinset, Set.Finite.mem_toFinset] using hg
    have h3 : F.toFinset.card ≤ 1 := h_card
    have h4 : f = g := by
      have h5 : ∀ a ∈ F.toFinset, ∀ b ∈ F.toFinset, a = b :=
        Finset.card_le_one.mp h3
      exact h5 f h1 g h2
    exact False.elim (hfg h4)
  · -- There are at least two functions; take minimum pairwise distance
    have h_card' : 1 < F.toFinset.card := by omega
    let pairs : Finset (C2Function × C2Function) :=
      F.toFinset ×ˢ F.toFinset
    let dists : Finset ℝ :=
      pairs.image (fun p : C2Function × C2Function => c2Distance p.1 p.2)
    let dists_pos : Finset ℝ :=
      dists.filter (fun d => 0 < d)
    have h_dists_pos_nonempty : dists_pos.Nonempty := by
      obtain ⟨f, hf, g, hg, hfg⟩ : ∃ (f : C2Function), f ∈ F.toFinset ∧
          ∃ (g : C2Function), g ∈ F.toFinset ∧ f ≠ g := by
        exact Finset.one_lt_card.mp h_card'
      have h_pos : 0 < c2Distance f g := by
        have h : c2Distance f g > 0 := dist_pos.mpr hfg
        exact h
      have h_in_dists : c2Distance f g ∈ dists := by
        apply Finset.mem_image.mpr
        exact ⟨(f, g), Finset.mem_product.mpr ⟨hf, hg⟩, rfl⟩
      exact ⟨c2Distance f g, Finset.mem_filter.mpr ⟨h_in_dists, h_pos⟩⟩
    let d_min : ℝ := Finset.min' dists_pos h_dists_pos_nonempty
    have h_d_min_in : d_min ∈ dists_pos := Finset.min'_mem dists_pos h_dists_pos_nonempty
    have h_d_min_pos : 0 < d_min := (Finset.mem_filter.mp h_d_min_in).2
    have h_d_min_le : ∀ f ∈ F.carrier, ∀ g ∈ F.carrier, f ≠ g →
        d_min ≤ c2Distance f g := by
      intro f hf g hg hfg
      have hf' : f ∈ F.toFinset := by
        simpa [FiniteFunctionFamily.toFinset, Set.Finite.mem_toFinset] using hf
      have hg' : g ∈ F.toFinset := by
        simpa [FiniteFunctionFamily.toFinset, Set.Finite.mem_toFinset] using hg
      have h_pos : 0 < c2Distance f g := dist_pos.mpr hfg
      have h_in_dists : c2Distance f g ∈ dists := by
        apply Finset.mem_image.mpr
        exact ⟨(f, g), Finset.mem_product.mpr ⟨hf', hg'⟩, rfl⟩
      have h_in_pos : c2Distance f g ∈ dists_pos :=
        Finset.mem_filter.mpr ⟨h_in_dists, h_pos⟩
      exact Finset.min'_le dists_pos (c2Distance f g) h_in_pos
    have hK_pos : 0 < K := by linarith
    let epsilon' : ℝ := d_min / (13 * K)
    have h_epsilon'_pos : 0 < epsilon' := by
      dsimp only [epsilon']
      positivity
    refine ⟨epsilon', h_epsilon'_pos, ?_⟩
    intro shift h_bound f hf g hg hfg
    have h1 : |shift f - shift g| ≤ |shift f| + |shift g| := by
      exact abs_sub _ _
    have h2 : |shift f| ≤ epsilon' := h_bound f hf
    have h3 : |shift g| ≤ epsilon' := h_bound g hg
    have h4 : |shift f - shift g| ≤ 2 * epsilon' := by linarith
    have h5 : 2 * epsilon' < d_min / (6 * K) := by
      dsimp only [epsilon']
      have h6 : 0 < d_min := h_d_min_pos
      have h7 : 0 < K := hK_pos
      have h8 : 2 * (d_min / (13 * K)) < d_min / (6 * K) := by
        have h10 : 0 < d_min := h6
        have h11 : 0 < K := h7
        have h12 : (2 : ℝ) / 13 < (1 : ℝ) / 6 := by norm_num
        have h13 : 2 / (13 * K) < 1 / (6 * K) := by
          have h14 : 2 / (13 * K) = (2 / 13) / K := by
            field_simp [h11.ne'] <;> ring
          have h15 : 1 / (6 * K) = (1 / 6) / K := by
            field_simp [h11.ne'] <;> ring
          rw [h14, h15]
          exact div_lt_div_of_pos_right h12 h11
        have h16 : 2 * (d_min / (13 * K)) = d_min * (2 / (13 * K)) := by ring
        have h17 : d_min / (6 * K) = d_min * (1 / (6 * K)) := by ring
        rw [h16, h17]
        exact mul_lt_mul_of_pos_left h13 h10
      exact h8
    have h9 : d_min / (6 * K) ≤ c2Distance f g / (6 * K) := by
      gcongr
      <;> exact h_d_min_le f hf g hg hfg
    exact lt_of_le_of_lt h4 (lt_of_lt_of_le h5 h9)

end Kakeya.Cinematic
