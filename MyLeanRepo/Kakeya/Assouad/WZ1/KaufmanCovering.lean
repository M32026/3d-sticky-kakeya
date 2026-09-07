import MyLeanRepo.Kakeya.Assouad.WZ1.EnergyToCovering


/-!
# Energy to covering number wrappers

Converts the `energy_to_covering` inequality into direct lower bounds
on `Metric.externalCoveringNumber`.

Includes both the standard version (off-diagonal pairs only) and a
regularized version using `max(dist, δ)` that counts all pairs.
-/

namespace Kakeya.Assouad

open Finset Metric

/--
Energy-to-covering-number wrapper.

Given a finite set `S ⊂ ℝ` with γ-energy bounded by `E`, the δ-external
covering number satisfies:
`externalCoveringNumber(δ, S) ≥ |S|² / (E · (2δ)^γ + |S|)`.
-/
lemma energy_to_covering_number
    (S : Finset ℝ) (δ γ E : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (hE : 0 ≤ E)
    (h_energy : ∑ x ∈ S, ∑ y ∈ S, |x - y|^(-γ) ≤ E) :
    (Metric.externalCoveringNumber (Real.toNNReal δ) (S : Set ℝ) : ENNReal) ≥
      ENNReal.ofReal ((S.card : ℝ)^2 / (E * (2 * δ)^γ + (S.card : ℝ))) := by
  by_cases hS : S = ∅
  · rw [hS]; simp
  · classical
    have hN_pos : 0 < (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    set B : ℝ := (S.card : ℝ)^2 / (E * (2 * δ)^γ + (S.card : ℝ)) with hB_def
    have h_denom_pos : 0 < E * (2 * δ)^γ + (S.card : ℝ) := by positivity
    have hB_nonneg : 0 ≤ B := by positivity

    have h_main : ∀ (C : Set ℝ), Metric.IsCover (Real.toNNReal δ) (S : Set ℝ) C →
        (Nat.ceil B : ENat) ≤ C.encard := by
      intro C hC
      have h_choose : ∀ (x : ℝ), x ∈ (S : Set ℝ) →
          ∃ (c : ℝ), c ∈ C ∧ |x - c| ≤ δ := by
        intro x hx
        rcases hC hx with ⟨c, hcC, hedist⟩
        have hedist' : edist x c ≤ ↑(Real.toNNReal δ) := by simpa using hedist
        have h_dist' : dist x c ≤ (Real.toNNReal δ : ℝ) := by
          rw [edist_dist] at hedist'
          exact ENNReal.ofReal_le_coe.mp hedist'
        have h_abs : |x - c| ≤ δ := by
          have h1 : dist x c = |x - c| := by
            simp [dist_eq_norm, Real.norm_eq_abs]
          have h2 : (Real.toNNReal δ : ℝ) = δ := Real.coe_toNNReal δ hδ.le
          rw [h1, h2] at h_dist'
          exact h_dist'
        exact ⟨c, hcC, h_abs⟩

      let f : ℝ → ℝ := fun x =>
        if hx : x ∈ S then Classical.choose (h_choose x hx) else 0
      have hf1 : ∀ x ∈ S, f x ∈ C := by
        intro x hx
        have h_fx : f x = Classical.choose (h_choose x hx) := by simp [f, hx]
        rw [h_fx]
        exact (Classical.choose_spec (h_choose x hx)).1
      have hf2 : ∀ x ∈ S, |x - f x| ≤ δ := by
        intro x hx
        have h_fx : f x = Classical.choose (h_choose x hx) := by simp [f, hx]
        rw [h_fx]
        exact (Classical.choose_spec (h_choose x hx)).2

      let centers : Finset ℝ := Finset.image f S
      have h_centers_subset : (centers : Set ℝ) ⊆ C := by
        intro z hz
        rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
        exact hf1 x hx
      have h_cover : ∀ x ∈ S, ∃ c ∈ centers, |x - c| ≤ δ := by
        intro x hx
        refine ⟨f x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, hf2 x hx⟩

      have h_energy' := energy_to_covering S δ γ hδ hγ centers h_cover

      have hcenters_pos : 0 < (centers.card : ℝ) := by
        by_contra h
        have h6 : (centers.card : ℝ) ≤ 0 := by linarith
        have h7 : 0 ≤ (centers.card : ℝ) := by positivity
        have h8 : (centers.card : ℝ) = 0 := by linarith
        have h9 : centers.card = 0 := by exact_mod_cast h8
        have h10 : centers = ∅ := by simpa using h9
        rw [h10] at h_cover
        have h11 : ∃ (x : ℝ), x ∈ S := Finset.nonempty_iff_ne_empty.mpr hS
        rcases h11 with ⟨x, hx⟩
        rcases h_cover x hx with ⟨c, hc, _⟩
        simp at hc

      set N : ℝ := (S.card : ℝ) with hN
      set M : ℝ := (centers.card : ℝ) with hM
      set D : ℝ := E * (2 * δ)^γ + N with hD
      have hD_pos : 0 < D := h_denom_pos
      have hM_pos : 0 < M := hcenters_pos
      have hpos : 0 ≤ 2 * δ := by linarith
      have h_rpow_pos : 0 < (2 * δ)^γ := by positivity

      have h5 : (N^2 / M - N) * (2 * δ)^(-γ) ≤ E := h_energy'.trans h_energy
      have h_inv : (2 * δ)^(-γ) = ((2 * δ)^γ)⁻¹ := by rw [Real.rpow_neg hpos]
      rw [h_inv] at h5
      have h7 : N^2 / M - N ≤ E * (2 * δ)^γ := by
        calc
          N^2 / M - N
            = ((N^2 / M - N) * ((2 * δ)^γ)⁻¹) * (2 * δ)^γ := by
              field_simp [h_rpow_pos.ne']
          _ ≤ E * (2 * δ)^γ := mul_le_mul_of_nonneg_right h5 (by positivity)

      have h8 : N^2 ≤ M * D := by
        have h9 : N^2 / M ≤ D := by simpa [hD] using h7
        calc
          N^2 = (N^2 / M) * M := by field_simp [hM_pos.ne']
          _ ≤ D * M := mul_le_mul_of_nonneg_right h9 (by positivity)
          _ = M * D := by ring

      have h4 : B ≤ M := by
        rw [hB_def, hD]
        calc
          N^2 / D ≤ (M * D) / D := by gcongr
          _ = M := by field_simp [hD_pos.ne']

      have h5' : Nat.ceil B ≤ centers.card := by
        rw [Nat.ceil_le]
        exact h4

      have h6 : (centers : Set ℝ).encard = (↑centers.card : ENat) :=
        Set.encard_coe_eq_coe_finsetCard centers
      have h7 : (centers : Set ℝ).encard ≤ C.encard := Set.encard_le_encard h_centers_subset
      rw [h6] at h7
      have h8 : (↑(Nat.ceil B) : ENat) ≤ (↑centers.card : ENat) := by
        exact_mod_cast h5'
      exact h8.trans h7

    have h9 : (Nat.ceil B : ENat) ≤ Metric.externalCoveringNumber (Real.toNNReal δ) (S : Set ℝ) := by
      rw [Metric.externalCoveringNumber]
      apply le_iInf_iff.mpr
      intro C
      apply le_iInf_iff.mpr
      intro hC
      exact h_main C hC

    have h10 : ENNReal.ofReal B ≤ (↑(Nat.ceil B) : ENNReal) := by
      rw [ENNReal.ofReal_le_natCast]
      exact Nat.le_ceil B
    have h11 : (↑(Nat.ceil B) : ENNReal) ≤
        (Metric.externalCoveringNumber (Real.toNNReal δ) (S : Set ℝ) : ENNReal) := by
      exact_mod_cast h9
    exact h10.trans h11

/--
Regularized energy-to-covering combinatorial lemma.

Given a finite set `S ⊂ ℝ`, centers covering `S` at scale δ, and γ > 0,
the regularized γ-energy satisfies:
`Σ_{x,y∈S} max(dist x y, δ)^(-γ) ≥ (|S|² / |centers|) · (2δ)^(-γ)`.

Unlike the standard version, this counts all pairs including diagonal,
because the regularization `max(dist, δ)` avoids the singularity at 0.
-/
lemma energy_to_covering_regularized
    (S : Finset ℝ) (δ γ : ℝ) (hδ : 0 < δ) (hγ : 0 < γ)
    (centers : Finset ℝ) (hcover : ∀ x ∈ S, ∃ c ∈ centers, dist x c ≤ δ) :
    (∑ x ∈ S, ∑ y ∈ S, (max (dist x y) δ)^(-γ)) ≥
    ((S.card : ℝ)^2 / (centers.card : ℝ)) * (2 * δ)^(-γ) := by
  by_cases hS : S = ∅
  · rw [hS]; simp
  · classical
    have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    have hcenters_nonempty : centers.Nonempty := by
      rcases hS_nonempty with ⟨x, hx⟩
      rcases hcover x hx with ⟨c, hc, _⟩
      exact ⟨c, hc⟩
    have hM_pos : (centers.card : ℝ) > 0 := by
      exact_mod_cast Finset.card_pos.mpr hcenters_nonempty

    let f : ℝ → ℝ := fun x =>
      if hx : x ∈ S then Classical.choose (hcover x hx) else 0
    have hf1 : ∀ x ∈ S, f x ∈ centers := by
      intro x hx
      simp [f, hx]
      exact (Classical.choose_spec (hcover x hx)).1
    have hf2 : ∀ x ∈ S, dist x (f x) ≤ δ := by
      intro x hx
      simp [f, hx]
      exact (Classical.choose_spec (hcover x hx)).2

    let fiber : ℝ → Finset ℝ := fun c => S.filter (fun x => f x = c)
    have h_fiber_sub : ∀ c, fiber c ⊆ S := fun c => filter_subset _ _

    have h_union : centers.biUnion fiber = S := by
      apply Finset.ext
      intro x
      constructor
      · intro hx
        rcases Finset.mem_biUnion.mp hx with ⟨c, hc, hxc⟩
        exact h_fiber_sub c hxc
      · intro hx
        have h1 : f x ∈ centers := hf1 x hx
        have h2 : x ∈ fiber (f x) := by
          simp [fiber, hx]
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

    -- rpow monotonicity for negative exponent
    have h_rpow_dec : ∀ (a b : ℝ), 0 < a → a ≤ b → a^(-γ) ≥ b^(-γ) := by
      intro a b ha hab
      have hb_pos : 0 < b := by linarith
      have hlog_a : Real.log (a^(-γ)) = (-γ) * Real.log a := Real.log_rpow ha (-γ)
      have hlog_b : Real.log (b^(-γ)) = (-γ) * Real.log b := Real.log_rpow hb_pos (-γ)
      have hlog : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) (by linarith)
      have h4 : Real.log (a^(-γ)) ≥ Real.log (b^(-γ)) := by
        rw [hlog_a, hlog_b]; nlinarith
      exact (Real.log_le_log_iff (by positivity) (by positivity)).mp h4

    -- Same-fiber pairs: max(dist x y, δ) ≤ 2δ
    have h_dist : ∀ c x y, x ∈ fiber c → y ∈ fiber c →
        max (dist x y) δ ≤ 2 * δ := by
      intro c x y hx hy
      have hfx : f x = c := (mem_filter.mp hx).2
      have hfy : f y = c := (mem_filter.mp hy).2
      have h1 : dist x c ≤ δ := by rw [← hfx]; exact hf2 x (h_fiber_sub c hx)
      have h2 : dist y c ≤ δ := by rw [← hfy]; exact hf2 y (h_fiber_sub c hy)
      have h3 : dist x y ≤ 2 * δ := by
        have h_tri : dist x y ≤ dist x c + dist c y := dist_triangle x c y
        have h_comm : dist c y = dist y c := dist_comm c y
        linarith
      have h4 : δ ≤ 2 * δ := by linarith
      exact max_le h3 h4

    have h_bound : ∀ c x y, x ∈ fiber c → y ∈ fiber c →
        (max (dist x y) δ)^(-γ) ≥ (2 * δ)^(-γ) := by
      intro c x y hx hy
      have hpos : 0 < max (dist x y) δ := by positivity
      have hle : max (dist x y) δ ≤ 2 * δ := h_dist c x y hx hy
      exact h_rpow_dec (max (dist x y) δ) (2 * δ) hpos hle

    let same_fiber_pairs : Finset (ℝ × ℝ) :=
      centers.biUnion fun c => (fiber c) ×ˢ (fiber c)

    have h_pair_disj : ∀ c1 ∈ centers, ∀ c2 ∈ centers, c1 ≠ c2 →
        Disjoint ((fiber c1) ×ˢ (fiber c1)) ((fiber c2) ×ˢ (fiber c2)) := by
      intro c1 _ c2 _ hne
      have h : Disjoint (fiber c1) (fiber c2) := h_disj c1 ‹_› c2 ‹_› hne
      exact Finset.disjoint_product.mpr (Or.inl h)

    have h_sum_product : (∑ x ∈ S, ∑ y ∈ S, (max (dist x y) δ)^(-γ)) =
        ∑ p ∈ S ×ˢ S, (max (dist p.1 p.2) δ)^(-γ) := by
      rw [Finset.sum_product]

    have h_subset : same_fiber_pairs ⊆ S ×ˢ S := by
      intro p hp
      rcases Finset.mem_biUnion.mp hp with ⟨c, _, hpc⟩
      have h1 : p.1 ∈ fiber c := (mem_product.mp hpc).1
      have h2 : p.2 ∈ fiber c := (mem_product.mp hpc).2
      exact mem_product.mpr ⟨h_fiber_sub c h1, h_fiber_sub c h2⟩

    have h_nonneg : ∀ p ∈ S ×ˢ S, 0 ≤ (max (dist p.1 p.2) δ)^(-γ) := by
      intro p _; positivity

    have h_energy_ge : (∑ p ∈ S ×ˢ S, (max (dist p.1 p.2) δ)^(-γ)) ≥
        ∑ p ∈ same_fiber_pairs, (max (dist p.1 p.2) δ)^(-γ) :=
      Finset.sum_le_sum_of_subset_of_nonneg h_subset fun i _ _ => h_nonneg i ‹_›

    have h_sum_fibers : (∑ p ∈ same_fiber_pairs, (max (dist p.1 p.2) δ)^(-γ)) =
        ∑ c ∈ centers, ∑ p ∈ (fiber c) ×ˢ (fiber c), (max (dist p.1 p.2) δ)^(-γ) := by
      rw [Finset.sum_biUnion h_pair_disj]

    have h_fiber_energy : ∀ c ∈ centers,
        (∑ p ∈ (fiber c) ×ˢ (fiber c), (max (dist p.1 p.2) δ)^(-γ)) ≥
        ((fiber c).card : ℝ)^2 * (2 * δ)^(-γ) := by
      intro c hc
      have h1 : ∑ p ∈ (fiber c) ×ˢ (fiber c), (max (dist p.1 p.2) δ)^(-γ) ≥
          ∑ p ∈ (fiber c) ×ˢ (fiber c), (2 * δ)^(-γ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact h_bound c p.1 p.2 (mem_product.mp hp).1 (mem_product.mp hp).2
      have h2 : ∑ p ∈ (fiber c) ×ˢ (fiber c), (2 * δ)^(-γ) =
          ((fiber c).card : ℝ)^2 * (2 * δ)^(-γ) := by
        rw [Finset.sum_const, Finset.card_product] <;> ring
      linarith

    have h_sum_ge : (∑ c ∈ centers, ∑ p ∈ (fiber c) ×ˢ (fiber c), (max (dist p.1 p.2) δ)^(-γ)) ≥
        ∑ c ∈ centers, (((fiber c).card : ℝ)^2 * (2 * δ)^(-γ)) := by
      apply Finset.sum_le_sum
      intro c hc
      exact h_fiber_energy c hc

    have h_factor : ∑ c ∈ centers, (((fiber c).card : ℝ)^2 * (2 * δ)^(-γ)) =
        (∑ c ∈ centers, ((fiber c).card : ℝ)^2) * (2 * δ)^(-γ) := by
      rw [← Finset.sum_mul]

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

    calc
      (∑ x ∈ S, ∑ y ∈ S, (max (dist x y) δ)^(-γ))
        = ∑ p ∈ S ×ˢ S, (max (dist p.1 p.2) δ)^(-γ) := h_sum_product
      _ ≥ ∑ p ∈ same_fiber_pairs, (max (dist p.1 p.2) δ)^(-γ) := h_energy_ge
      _ = ∑ c ∈ centers, ∑ p ∈ (fiber c) ×ˢ (fiber c), (max (dist p.1 p.2) δ)^(-γ) := h_sum_fibers
      _ ≥ ∑ c ∈ centers, (((fiber c).card : ℝ)^2 * (2 * δ)^(-γ)) := h_sum_ge
      _ = (∑ c ∈ centers, ((fiber c).card : ℝ)^2) * (2 * δ)^(-γ) := h_factor
      _ ≥ ((S.card : ℝ)^2 / (centers.card : ℝ)) * (2 * δ)^(-γ) :=
        mul_le_mul_of_nonneg_right h_sum_sq_ge (by positivity)

/--
Regularized energy-to-covering-number wrapper.

Given a finite set `S ⊂ ℝ` with regularized γ-energy bounded by `E`,
the δ-external covering number satisfies:
`externalCoveringNumber(δ, S) ≥ |S|² / (E · (2δ)^γ)`.

The regularization `max(dist, δ)` avoids the singularity at distance 0,
allowing all pairs (including diagonal) to contribute to the lower bound.
-/
lemma regularized_energy_to_covering_number
    (S : Finset ℝ) (δ γ E : ℝ) (hδ : 0 < δ) (hγ : 0 < γ) (hE : 0 ≤ E)
    (h_energy : ∑ x ∈ S, ∑ y ∈ S, (max (dist x y) δ)^(-γ) ≤ E) :
    (Metric.externalCoveringNumber (Real.toNNReal δ) (S : Set ℝ) : ENNReal) ≥
      ENNReal.ofReal ((S.card : ℝ)^2 / (E * (2 * δ)^γ)) := by
  by_cases hS : S = ∅
  · rw [hS]; simp
  · by_cases hE0 : E = 0
    · have h : (S.card : ℝ)^2 / (E * (2 * δ)^γ) = 0 := by
        rw [hE0]; simp
      rw [h]; simp
    · classical
      have hE_pos : 0 < E := by
        exact lt_of_le_of_ne hE (Ne.symm hE0)
      have hN_pos : 0 < (S.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
      set B : ℝ := (S.card : ℝ)^2 / (E * (2 * δ)^γ) with hB_def
      have h_denom_pos : 0 < E * (2 * δ)^γ := by positivity
      have hB_nonneg : 0 ≤ B := by positivity

      have h_main : ∀ (C : Set ℝ), Metric.IsCover (Real.toNNReal δ) (S : Set ℝ) C →
          (Nat.ceil B : ENat) ≤ C.encard := by
        intro C hC
        have h_choose : ∀ (x : ℝ), x ∈ (S : Set ℝ) →
            ∃ (c : ℝ), c ∈ C ∧ dist x c ≤ δ := by
          intro x hx
          rcases hC hx with ⟨c, hcC, hedist⟩
          have hedist' : edist x c ≤ ↑(Real.toNNReal δ) := by simpa using hedist
          have h_dist' : dist x c ≤ (Real.toNNReal δ : ℝ) := by
            rw [edist_dist] at hedist'
            exact ENNReal.ofReal_le_coe.mp hedist'
          have h_abs : dist x c ≤ δ := by
            have h2 : (Real.toNNReal δ : ℝ) = δ := Real.coe_toNNReal δ hδ.le
            rw [h2] at h_dist'
            exact h_dist'
          exact ⟨c, hcC, h_abs⟩

        let f : ℝ → ℝ := fun x =>
          if hx : x ∈ S then Classical.choose (h_choose x hx) else 0
        have hf1 : ∀ x ∈ S, f x ∈ C := by
          intro x hx
          have h_fx : f x = Classical.choose (h_choose x hx) := by simp [f, hx]
          rw [h_fx]
          exact (Classical.choose_spec (h_choose x hx)).1
        have hf2 : ∀ x ∈ S, dist x (f x) ≤ δ := by
          intro x hx
          have h_fx : f x = Classical.choose (h_choose x hx) := by simp [f, hx]
          rw [h_fx]
          exact (Classical.choose_spec (h_choose x hx)).2

        let centers : Finset ℝ := Finset.image f S
        have h_centers_subset : (centers : Set ℝ) ⊆ C := by
          intro z hz
          rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
          exact hf1 x hx
        have h_cover : ∀ x ∈ S, ∃ c ∈ centers, dist x c ≤ δ := by
          intro x hx
          refine ⟨f x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, hf2 x hx⟩

        have h_energy' := energy_to_covering_regularized S δ γ hδ hγ centers h_cover

        have hcenters_pos : 0 < (centers.card : ℝ) := by
          by_contra h
          have h6 : (centers.card : ℝ) ≤ 0 := by linarith
          have h7 : 0 ≤ (centers.card : ℝ) := by positivity
          have h8 : (centers.card : ℝ) = 0 := by linarith
          have h9 : centers.card = 0 := by exact_mod_cast h8
          have h10 : centers = ∅ := by simpa using h9
          rw [h10] at h_cover
          have h11 : ∃ (x : ℝ), x ∈ S := Finset.nonempty_iff_ne_empty.mpr hS
          rcases h11 with ⟨x, hx⟩
          rcases h_cover x hx with ⟨c, hc, _⟩
          simp at hc

        set N : ℝ := (S.card : ℝ) with hN
        set M : ℝ := (centers.card : ℝ) with hM
        set D : ℝ := E * (2 * δ)^γ with hD
        have hD_pos : 0 < D := h_denom_pos
        have hM_pos : 0 < M := hcenters_pos
        have hpos : 0 ≤ 2 * δ := by linarith
        have h_rpow_pos : 0 < (2 * δ)^γ := by positivity

        have h5 : (N^2 / M) * (2 * δ)^(-γ) ≤ E := h_energy'.trans h_energy
        have h_inv : (2 * δ)^(-γ) = ((2 * δ)^γ)⁻¹ := by rw [Real.rpow_neg hpos]
        rw [h_inv] at h5
        have h7 : N^2 / M ≤ E * (2 * δ)^γ := by
          calc
            N^2 / M
              = ((N^2 / M) * ((2 * δ)^γ)⁻¹) * (2 * δ)^γ := by
                field_simp [h_rpow_pos.ne']
            _ ≤ E * (2 * δ)^γ := mul_le_mul_of_nonneg_right h5 (by positivity)

        have h8 : N^2 ≤ M * D := by
          have h9 : N^2 / M ≤ D := by simpa [hD] using h7
          calc
            N^2 = (N^2 / M) * M := by field_simp [hM_pos.ne']
            _ ≤ D * M := mul_le_mul_of_nonneg_right h9 (by positivity)
            _ = M * D := by ring

        have h4 : B ≤ M := by
          rw [hB_def, hD]
          calc
            N^2 / D ≤ (M * D) / D := by gcongr
            _ = M := by field_simp [hD_pos.ne']

        have h5' : Nat.ceil B ≤ centers.card := by
          rw [Nat.ceil_le]
          exact h4

        have h6 : (centers : Set ℝ).encard = (↑centers.card : ENat) :=
          Set.encard_coe_eq_coe_finsetCard centers
        have h7 : (centers : Set ℝ).encard ≤ C.encard := Set.encard_le_encard h_centers_subset
        rw [h6] at h7
        have h8 : (↑(Nat.ceil B) : ENat) ≤ (↑centers.card : ENat) := by
          exact_mod_cast h5'
        exact h8.trans h7

      have h9 : (Nat.ceil B : ENat) ≤ Metric.externalCoveringNumber (Real.toNNReal δ) (S : Set ℝ) := by
        rw [Metric.externalCoveringNumber]
        apply le_iInf_iff.mpr
        intro C
        apply le_iInf_iff.mpr
        intro hC
        exact h_main C hC

      have h10 : ENNReal.ofReal B ≤ (↑(Nat.ceil B) : ENNReal) := by
        rw [ENNReal.ofReal_le_natCast]
        exact Nat.le_ceil B
      have h11 : (↑(Nat.ceil B) : ENNReal) ≤
          (Metric.externalCoveringNumber (Real.toNNReal δ) (S : Set ℝ) : ENNReal) := by
        exact_mod_cast h9
      exact h10.trans h11

end Kakeya.Assouad
