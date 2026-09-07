import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.FrostmanEnergy
import MyLeanRepo.Kakeya.Assouad.WZ1.AngularIntegral
import MyLeanRepo.Kakeya.Assouad.WZ1.KaufmanEnergyTotal
import MyLeanRepo.Kakeya.Assouad.WZ1.KaufmanCovering


/-!
# Kaufman Projection Theorem (complete)

Given Frostman sets F (points) and Λ (unit directions), and a dense bipartite
incidence graph H between them, there exists a direction θ ∈ Λ such that the
orthogonal projection of F onto θ has large δ-covering number.
-/

noncomputable section

namespace Kakeya.Assouad

open Finset Metric

/-- The fiber of H over direction θ: points in F incident to θ. -/
private def fiber (H : Finset (Point2 × Point2)) (θ : Point2) : Finset Point2 :=
  (H.filter (fun h => h.1 = θ)).image (fun h => h.2)

/-- Total projection energy bound using kaufman_total_energy_bound. -/
lemma projection_energy_total
    {F Λ : DiscreteSet 2} {δ C α β γ : ℝ}
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hγ_lt_alpha : γ < α) (hγ_lt_beta : γ < β)
    (hC : 0 ≤ C) (hC_ge_one : 1 ≤ C)
    (hF_frost : F.IsFrostman δ α (ENNReal.ofReal C))
    (hΛ_frost : Λ.IsFrostman δ β (ENNReal.ofReal C))
    (hF_sep : F.IsDeltaSeparated δ)
    (hΛ_sep : Λ.IsDeltaSeparated δ)
    (hF_ball : F.IsInUnitBall)
    (hunit : ∀ θ ∈ Λ, ‖θ‖ = 1)
    (hneF : F.Nonempty) (hneΛ : Λ.Nonempty)
    (H : Finset (Point2 × Point2))
    (hH_sub : ∀ h ∈ H, h.1 ∈ Λ ∧ h.2 ∈ F) :
    ∑ θ ∈ Λ, ∑ x ∈ fiber H θ, ∑ y ∈ fiber H θ,
        (max (dist (inner ℝ θ x) (inner ℝ θ y)) δ)^(-γ) ≤
    kaufman_total_const C α β γ * (F.card : ℝ)^2 * (Λ.card : ℝ) := by
  have h1 : ∀ θ ∈ Λ, fiber H θ ⊆ F := by
    intro θ _ x hx
    rcases Finset.mem_image.mp hx with ⟨h, hh, rfl⟩
    have h_in_H : h ∈ H := (Finset.mem_filter.mp hh).1
    exact (hH_sub h h_in_H).2
  have h2 : ∀ θ ∈ Λ, ∑ x ∈ fiber H θ, ∑ y ∈ fiber H θ,
        (max (dist (inner ℝ θ x) (inner ℝ θ y)) δ)^(-γ) ≤
      ∑ x ∈ F, ∑ y ∈ F, (max (|inner ℝ θ (x - y)|) δ)^(-γ) := by
    intro θ hθ
    have h3 : ∀ x ∈ fiber H θ, ∀ y ∈ fiber H θ,
        (max (dist (inner ℝ θ x) (inner ℝ θ y)) δ)^(-γ) =
        (max (|inner ℝ θ (x - y)|) δ)^(-γ) := by
      intro x _ y _
      have h4 : dist (inner ℝ θ x) (inner ℝ θ y) = |inner ℝ θ (x - y)| := by
        have h5 : inner ℝ θ x - inner ℝ θ y = inner ℝ θ (x - y) := by
          have h : inner ℝ θ (x - y) = inner ℝ θ x - inner ℝ θ y := inner_sub_right θ x y
          exact h.symm
        simp [dist_eq_norm, Real.norm_eq_abs, h5]
      rw [h4]
    have h_step1 : ∑ x ∈ fiber H θ, ∑ y ∈ fiber H θ, (max (dist (inner ℝ θ x) (inner ℝ θ y)) δ)^(-γ) ≤
        ∑ x ∈ fiber H θ, ∑ y ∈ fiber H θ, (max (|inner ℝ θ (x - y)|) δ)^(-γ) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      have h_eq := h3 x hx y hy
      exact h_eq.le
    have h_inner : ∀ x ∈ fiber H θ, ∑ y ∈ fiber H θ, (max (|inner ℝ θ (x - y)|) δ)^(-γ) ≤
        ∑ y ∈ F, (max (|inner ℝ θ (x - y)|) δ)^(-γ) := by
      intro x _
      apply Finset.sum_le_sum_of_subset_of_nonneg (h1 θ hθ)
      intro y _ _
      positivity
    have h_step2 : ∑ x ∈ fiber H θ, ∑ y ∈ fiber H θ, (max (|inner ℝ θ (x - y)|) δ)^(-γ) ≤
        ∑ x ∈ F, ∑ y ∈ F, (max (|inner ℝ θ (x - y)|) δ)^(-γ) := by
      calc
        ∑ x ∈ fiber H θ, ∑ y ∈ fiber H θ, _
          ≤ ∑ x ∈ fiber H θ, ∑ y ∈ F, _ := Finset.sum_le_sum (fun x hx => h_inner x hx)
        _ ≤ ∑ x ∈ F, ∑ y ∈ F, _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (h1 θ hθ)
          intro x _ _
          apply Finset.sum_nonneg
          intro y _
          positivity
    exact le_trans h_step1 h_step2
  have h_step3 : ∑ θ ∈ Λ, ∑ x ∈ fiber H θ, ∑ y ∈ fiber H θ, (max (dist (inner ℝ θ x) (inner ℝ θ y)) δ)^(-γ) ≤
      ∑ θ ∈ Λ, ∑ x ∈ F, ∑ y ∈ F, (max (|inner ℝ θ (x - y)|) δ)^(-γ) :=
    Finset.sum_le_sum (fun θ hθ => h2 θ hθ)
  have h_step4 : ∑ θ ∈ Λ, ∑ x ∈ F, ∑ y ∈ F, (max (|inner ℝ θ (x - y)|) δ)^(-γ) ≤
      kaufman_total_const C α β γ * (F.card : ℝ)^2 * (Λ.card : ℝ) :=
    kaufman_total_energy_bound hδ hδ_le_one hα hβ hγ hγ_lt_alpha hγ_lt_beta
      hC hC_ge_one hF_frost hΛ_frost hF_sep hF_ball hunit hneF hneΛ
  exact le_trans h_step3 h_step4

/-- Markov averaging: at least half the directions have energy ≤ twice the average. -/
lemma markov_good_directions
    {Λ : DiscreteSet 2} {E_total : ℝ}
    (E : Point2 → ℝ) (hE_nonneg : ∀ θ ∈ Λ, 0 ≤ E θ)
    (h_sum : ∑ θ ∈ Λ, E θ ≤ E_total)
    (hΛ_nonempty : Λ.Nonempty) :
    ∃ (Λ_good : Finset Point2),
      Λ_good ⊆ Λ ∧
      (Λ_good.card : ℝ) ≥ (Λ.card : ℝ) / 2 ∧
      ∀ θ ∈ Λ_good, E θ ≤ 2 * E_total / (Λ.card : ℝ) := by
  have hΛ_pos : 0 < (Λ.card : ℝ) := by exact_mod_cast hΛ_nonempty.card_pos
  let threshold : ℝ := 2 * E_total / (Λ.card : ℝ)
  let Λ_good : Finset Point2 := Λ.filter (fun θ => E θ ≤ threshold)
  let Λ_bad : Finset Point2 := Λ.filter (fun θ => E θ > threshold)
  have h1 : Λ = Λ_good ∪ Λ_bad := by
    ext θ
    simp only [Λ_good, Λ_bad, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hθ
      by_cases h : E θ ≤ threshold
      · exact Or.inl ⟨hθ, h⟩
      · have h' : E θ > threshold := by linarith
        exact Or.inr ⟨hθ, h'⟩
    · rintro (⟨hθ, _⟩ | ⟨hθ, _⟩) <;> exact hθ
  have h2 : Disjoint Λ_good Λ_bad := by
    rw [Finset.disjoint_left]
    intro θ h1 h2
    have h3 : E θ ≤ threshold := (Finset.mem_filter.mp h1).2
    have h4 : E θ > threshold := (Finset.mem_filter.mp h2).2
    linarith
  have h3 : (Λ.card : ℝ) = (Λ_good.card : ℝ) + (Λ_bad.card : ℝ) := by
    have h4 : Λ.card = Λ_good.card + Λ_bad.card := by
      rw [h1, Finset.card_union_of_disjoint h2]
    exact_mod_cast h4
  have h4 : Λ_good ⊆ Λ := filter_subset _ _
  have h5 : ∀ θ ∈ Λ_good, E θ ≤ threshold := by
    intro θ hθ
    exact (Finset.mem_filter.mp hθ).2
  by_cases h6 : (Λ_good.card : ℝ) ≥ (Λ.card : ℝ) / 2
  · exact ⟨Λ_good, h4, h6, h5⟩
  · have h7 : (Λ_bad.card : ℝ) > (Λ.card : ℝ) / 2 := by linarith
    have h8 : 0 < (Λ_bad.card : ℝ) := by linarith
    have h9 : 0 < Λ_bad.card := by exact_mod_cast h8
    have h9' : Λ_bad.Nonempty := Finset.card_pos.mp h9
    have h10 : ∀ θ ∈ Λ_bad, E θ > threshold := by
      intro θ hθ
      exact (Finset.mem_filter.mp hθ).2
    have h11 : ∑ θ ∈ Λ_bad, E θ > ∑ θ ∈ Λ_bad, threshold := by
      let θ0 : Point2 := Classical.choose h9'
      have hθ0 : θ0 ∈ Λ_bad := Classical.choose_spec h9'
      have h_pos : ∀ θ ∈ Λ_bad, 0 < E θ - threshold := by
        intro θ hθ
        have h : E θ > threshold := h10 θ hθ
        linarith
      have h1 : 0 < E θ0 - threshold := h_pos θ0 hθ0
      have h2 : ∑ θ ∈ Λ_bad, (E θ - threshold) ≥ E θ0 - threshold :=
        Finset.single_le_sum (fun θ hθ => (h_pos θ hθ).le) hθ0
      have h3 : ∑ θ ∈ Λ_bad, (E θ - threshold) = (∑ θ ∈ Λ_bad, E θ) - ∑ θ ∈ Λ_bad, threshold := by
        rw [Finset.sum_sub_distrib]
      have h4 : 0 < ∑ θ ∈ Λ_bad, (E θ - threshold) := by linarith
      rw [h3] at h4
      linarith
    have h12 : ∑ θ ∈ Λ_bad, threshold = (Λ_bad.card : ℝ) * threshold := by
      rw [Finset.sum_const] <;> ring
    rw [h12] at h11
    have h13 : (Λ_bad.card : ℝ) * threshold > E_total := by
      dsimp only [threshold]
      have h14 : 0 < (Λ.card : ℝ) := hΛ_pos
      have h15 : 0 ≤ E_total := by
        have h16 : 0 ≤ ∑ θ ∈ Λ, E θ := Finset.sum_nonneg (fun θ hθ => hE_nonneg θ hθ)
        linarith [h_sum]
      have h16 : (Λ_bad.card : ℝ) > (Λ.card : ℝ) / 2 := h7
      have hE_total_nonneg : 0 ≤ E_total := by
        have h16 : 0 ≤ ∑ θ ∈ Λ, E θ := Finset.sum_nonneg (fun θ hθ => hE_nonneg θ hθ)
        linarith [h_sum]
      have hE_total_pos : 0 < E_total := by
        by_contra h
        have hE0 : E_total = 0 := by linarith
        have h_thresh0 : threshold = 0 := by
          dsimp only [threshold]; rw [hE0]; simp
        have h_bad_pos : 0 < (Λ_bad.card : ℝ) := by linarith [h7]
        have h_bad_nonempty : Λ_bad.Nonempty := Finset.card_pos.mp (by exact_mod_cast h_bad_pos)
        obtain ⟨θ0, hθ0⟩ := h_bad_nonempty
        have h_gt : E θ0 > threshold := h10 θ0 hθ0
        rw [h_thresh0] at h_gt
        have hθ0_in_Λ : θ0 ∈ Λ := (show Λ_bad ⊆ Λ from filter_subset _ _) hθ0
        have hEθ0_le : E θ0 ≤ ∑ θ ∈ Λ, E θ :=
          Finset.single_le_sum (fun θ _ => hE_nonneg θ (by tauto)) hθ0_in_Λ
        have h_sum0 : ∑ θ ∈ Λ, E θ ≤ 0 := by rw [hE0] at h_sum; exact h_sum
        linarith
      have h_denom_pos : 0 < (Λ.card : ℝ) := hΛ_pos
      have h_factor_pos : 0 < 2 * E_total / (Λ.card : ℝ) := by
        apply div_pos
        · exact mul_pos (by norm_num) hE_total_pos
        · exact h_denom_pos
      have h17 : (Λ_bad.card : ℝ) * (2 * E_total / (Λ.card : ℝ)) >
          ((Λ.card : ℝ) / 2) * (2 * E_total / (Λ.card : ℝ)) :=
        mul_lt_mul_of_pos_right h16 h_factor_pos
      have h18 : ((Λ.card : ℝ) / 2) * (2 * E_total / (Λ.card : ℝ)) = E_total := by
        have h_ne : (Λ.card : ℝ) ≠ 0 := hΛ_pos.ne'
        calc
          ((Λ.card : ℝ) / 2) * (2 * E_total / (Λ.card : ℝ))
            = ((Λ.card : ℝ) * (2 * E_total)) / (2 * (Λ.card : ℝ)) := by ring
        _ = E_total := by
          field_simp [h_ne] <;> ring
      rw [h18] at h17
      exact h17
    have h14 : ∑ θ ∈ Λ, E θ ≥ ∑ θ ∈ Λ_bad, E θ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (show Λ_bad ⊆ Λ from filter_subset _ _)
      intro θ hθ _
      exact hE_nonneg θ hθ
    linarith [h11, h13, h14, h_sum]

/-- Projected regularized energy to covering number.

Given a finite set A mapped to ℝ by f, if the regularized energy is bounded by E,
then the δ-covering number of the image is at least N² / (E · (2δ)^γ). -/
lemma projected_energy_to_covering
    {α : Type*} [DecidableEq α] (A : Finset α) (f : α → ℝ)
    {δ γ E : ℝ} (hδ : 0 < δ) (hγ : 0 < γ) (hE : 0 ≤ E)
    (h_energy : ∑ x ∈ A, ∑ y ∈ A, (max (dist (f x) (f y)) δ)^(-γ) ≤ E) :
    Metric.externalCoveringNumber (Real.toNNReal δ) (f '' (A : Set α)) ≥
      ENNReal.ofReal ((A.card : ℝ)^2 / (E * (2 * δ)^γ)) := by
  by_cases hA : A = ∅
  · rw [hA]; simp
  · by_cases hE0 : E = 0
    · have h : (A.card : ℝ)^2 / (E * (2 * δ)^γ) = 0 := by
        rw [hE0]; simp
      rw [h]; simp
    · classical
      have hE_pos : 0 < E := by exact lt_of_le_of_ne hE (Ne.symm hE0)
      have hA_nonempty : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA
      have hA_pos : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hA_nonempty
      set B : ℝ := (A.card : ℝ)^2 / (E * (2 * δ)^γ) with hB_def
      have h_denom_pos : 0 < E * (2 * δ)^γ := by positivity
      have hB_nonneg : 0 ≤ B := by positivity

      have h_main : ∀ (C : Set ℝ), Metric.IsCover (Real.toNNReal δ) (f '' (A : Set α)) C →
          (Nat.ceil B : ENat) ≤ C.encard := by
        intro C hC
        have h_choose : ∀ (x : α), x ∈ A → ∃ (c : ℝ), c ∈ C ∧ dist (f x) c ≤ δ := by
          intro x hx
          have hz : f x ∈ f '' (A : Set α) := Set.mem_image_of_mem f hx
          have h_unfold : ∀ (z : ℝ), z ∈ f '' (A : Set α) → ∃ (c : ℝ), c ∈ C ∧ edist z c ≤ ↑(Real.toNNReal δ) := by
            exact hC
          rcases h_unfold (f x) hz with ⟨c, hcC, hed⟩
          have hdist : dist (f x) c ≤ (Real.toNNReal δ : ℝ) := by
            have h2 : edist (f x) c ≤ ↑(Real.toNNReal δ) := hed
            rw [edist_dist] at h2
            exact ENNReal.ofReal_le_coe.mp h2
          have h4 : (Real.toNNReal δ : ℝ) = δ := Real.coe_toNNReal δ hδ.le
          rw [h4] at hdist
          exact ⟨c, hcC, hdist⟩
        let c : α → ℝ := fun x => if h : x ∈ A then Classical.choose (h_choose x h) else 0
        have hcC : ∀ x ∈ A, c x ∈ C := by
          intro x hx
          have hcx : c x = Classical.choose (h_choose x hx) := by
            simp [c, hx]
          rw [hcx]
          exact (Classical.choose_spec (h_choose x hx)).1
        have hcdist : ∀ x ∈ A, dist (f x) (c x) ≤ δ := by
          intro x hx
          have hcx : c x = Classical.choose (h_choose x hx) := by
            simp [c, hx]
          rw [hcx]
          exact (Classical.choose_spec (h_choose x hx)).2
        let centers : Finset ℝ := A.image c
        have h_centers_subset : (centers : Set ℝ) ⊆ C := by
          intro z hz
          rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
          exact hcC x hx
        have hcC' := hcC
        have hcdist' := hcdist
        let group : ℝ → Finset α := fun u => A.filter (fun x => c x = u)
        have h_group_sub : ∀ u, group u ⊆ A := fun _ => filter_subset _ _
        have h_union : centers.biUnion group = A := by
          apply Finset.ext
          intro x
          constructor
          · intro hx
            rcases Finset.mem_biUnion.mp hx with ⟨u, _, hxu⟩
            exact h_group_sub u hxu
          · intro hx
            have h1 : c x ∈ centers := Finset.mem_image.mpr ⟨x, hx, rfl⟩
            have h2 : x ∈ group (c x) := by
              simp [group, hx]
            exact Finset.mem_biUnion.mpr ⟨c x, h1, h2⟩
        have h_disj : ∀ u1 ∈ centers, ∀ u2 ∈ centers, u1 ≠ u2 →
            Disjoint (group u1) (group u2) := by
          intro u1 _ u2 _ hne
          simp only [group, Finset.disjoint_left, mem_filter]
          intro x hx1 hx2
          have h1 : c x = u1 := hx1.2
          have h2 : c x = u2 := hx2.2
          have h3 : u1 = u2 := by rw [←h1, h2]
          exact hne h3
        have h_sum_card : ∑ u ∈ centers, (group u).card = A.card := by
          have h : (centers.biUnion group).card = ∑ u ∈ centers, (group u).card := by
            rw [Finset.card_biUnion h_disj]
          rw [←h, h_union]

        have h_centers_nonempty : centers.Nonempty :=
          Finset.Nonempty.image hA_nonempty c
        have hM_pos : 0 < (centers.card : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr h_centers_nonempty

        -- Same-group pairs have max(dist, δ)^(-γ) ≥ (2δ)^(-γ)
        have h_bound : ∀ u x y, x ∈ group u → y ∈ group u →
            (max (dist (f x) (f y)) δ)^(-γ) ≥ (2 * δ)^(-γ) := by
          intro u x y hx hy
          have hcx : c x = u := (mem_filter.mp hx).2
          have hcy : c y = u := (mem_filter.mp hy).2
          have h1 : dist (f x) u ≤ δ := by rw [←hcx]; exact hcdist x (h_group_sub u hx)
          have h2 : dist (f y) u ≤ δ := by rw [←hcy]; exact hcdist y (h_group_sub u hy)
          have h3 : dist (f x) (f y) ≤ 2 * δ := by
            have h4 : dist (f x) (f y) ≤ dist (f x) u + dist u (f y) := dist_triangle _ _ _
            have h5 : dist u (f y) = dist (f y) u := dist_comm _ _
            rw [h5] at h4
            linarith
          have h6 : max (dist (f x) (f y)) δ ≤ 2 * δ := by
            have h7 : δ ≤ 2 * δ := by linarith
            exact max_le h3 h7
          have hpos : 0 < max (dist (f x) (f y)) δ := by positivity
          have h_a : (max (dist (f x) (f y)) δ)^γ ≤ (2 * δ)^γ :=
            Real.rpow_le_rpow (by positivity) h6 (by linarith)
          have h1' : (max (dist (f x) (f y)) δ)^(-γ) = 1 / (max (dist (f x) (f y)) δ)^γ := by
            rw [Real.rpow_neg (by positivity)] <;> field_simp
          have h2' : (2 * δ)^(-γ) = 1 / (2 * δ)^γ := by
            rw [Real.rpow_neg (by positivity)] <;> field_simp
          rw [h1', h2']
          exact one_div_le_one_div_of_le (by positivity) h_a

        have h_group_energy : ∀ u ∈ centers,
            (∑ x ∈ group u, ∑ y ∈ group u, (max (dist (f x) (f y)) δ)^(-γ)) ≥
            ((group u).card : ℝ)^2 * (2 * δ)^(-γ) := by
          intro u hu
          have h1 : ∑ x ∈ group u, ∑ y ∈ group u, (max (dist (f x) (f y)) δ)^(-γ) ≥
              ∑ x ∈ group u, ∑ y ∈ group u, (2 * δ)^(-γ) := by
            apply Finset.sum_le_sum
            intro x _
            apply Finset.sum_le_sum
            intro y _
            exact h_bound u x y ‹_› ‹_›
          have h2 : ∑ x ∈ group u, ∑ y ∈ group u, (2 * δ)^(-γ) =
              ((group u).card : ℝ)^2 * (2 * δ)^(-γ) := by
            simp [Finset.sum_const, Finset.card_product] <;> ring
          linarith

        -- Sum over same-group pairs ≤ total sum
        let same_pairs : Finset (α × α) := centers.biUnion fun u => (group u) ×ˢ (group u)
        have h_pair_disj : ∀ u1 ∈ centers, ∀ u2 ∈ centers, u1 ≠ u2 →
            Disjoint ((group u1) ×ˢ (group u1)) ((group u2) ×ˢ (group u2)) := by
          intro u1 _ u2 _ hne
          have h : Disjoint (group u1) (group u2) := h_disj u1 ‹_› u2 ‹_› hne
          exact Finset.disjoint_product.mpr (Or.inl h)
        have h_subset : same_pairs ⊆ A ×ˢ A := by
          intro p hp
          rcases Finset.mem_biUnion.mp hp with ⟨u, _, hpc⟩
          have h1 : p.1 ∈ group u := (mem_product.mp hpc).1
          have h2 : p.2 ∈ group u := (mem_product.mp hpc).2
          exact mem_product.mpr ⟨h_group_sub u h1, h_group_sub u h2⟩
        have h_sum_ge : (∑ x ∈ A, ∑ y ∈ A, (max (dist (f x) (f y)) δ)^(-γ)) ≥
            (∑ u ∈ centers, ((group u).card : ℝ)^2) * (2 * δ)^(-γ) := by
          have h3 : (∑ x ∈ A, ∑ y ∈ A, (max (dist (f x) (f y)) δ)^(-γ)) =
              ∑ p ∈ A ×ˢ A, (max (dist (f p.1) (f p.2)) δ)^(-γ) := by
            rw [Finset.sum_product]
          rw [h3]
          have h4 : ∑ p ∈ A ×ˢ A, (max (dist (f p.1) (f p.2)) δ)^(-γ) ≥
              ∑ p ∈ same_pairs, (max (dist (f p.1) (f p.2)) δ)^(-γ) :=
            Finset.sum_le_sum_of_subset_of_nonneg h_subset (fun _ _ _ => by positivity)
          have h5 : ∑ p ∈ same_pairs, (max (dist (f p.1) (f p.2)) δ)^(-γ) =
              ∑ u ∈ centers, ∑ p ∈ (group u) ×ˢ (group u), (max (dist (f p.1) (f p.2)) δ)^(-γ) := by
            rw [Finset.sum_biUnion h_pair_disj]
          have h6 : ∑ u ∈ centers, ∑ p ∈ (group u) ×ˢ (group u), (max (dist (f p.1) (f p.2)) δ)^(-γ) ≥
              ∑ u ∈ centers, (((group u).card : ℝ)^2 * (2 * δ)^(-γ)) := by
            apply Finset.sum_le_sum
            intro u hu
            have h_eq : ∑ p ∈ (group u) ×ˢ (group u), (max (dist (f p.1) (f p.2)) δ)^(-γ) =
                ∑ x ∈ group u, ∑ y ∈ group u, (max (dist (f x) (f y)) δ)^(-γ) := by
              rw [Finset.sum_product]
            rw [h_eq]
            exact h_group_energy u hu
          calc
            ∑ p ∈ A ×ˢ A, _
              ≥ ∑ p ∈ same_pairs, _ := h4
          _ = ∑ u ∈ centers, ∑ p ∈ (group u) ×ˢ (group u), _ := h5
          _ ≥ ∑ u ∈ centers, (((group u).card : ℝ)^2 * (2 * δ)^(-γ)) := h6
          _ = (∑ u ∈ centers, ((group u).card : ℝ)^2) * (2 * δ)^(-γ) := by rw [Finset.sum_mul]

        -- Cauchy-Schwarz
        have h_cs : (A.card : ℝ)^2 ≤
            (centers.card : ℝ) * ∑ u ∈ centers, ((group u).card : ℝ)^2 := by
          have h : (∑ u ∈ centers, ((group u).card : ℝ)) ^ 2 ≤
              (centers.card : ℝ) * ∑ u ∈ centers, ((group u).card : ℝ)^2 :=
            sq_sum_le_card_mul_sum_sq
          have h_sum_card_real : ∑ u ∈ centers, ((group u).card : ℝ) = (A.card : ℝ) := by
            exact_mod_cast h_sum_card
          rw [h_sum_card_real] at h
          exact h
        have h_sum_sq_ge : ∑ u ∈ centers, ((group u).card : ℝ)^2 ≥
            (A.card : ℝ)^2 / (centers.card : ℝ) := by
          have h : (A.card : ℝ)^2 ≤ (centers.card : ℝ) * (∑ u ∈ centers, ((group u).card : ℝ)^2) := h_cs
          have h7 : (A.card : ℝ)^2 / (centers.card : ℝ) ≤ (∑ u ∈ centers, ((group u).card : ℝ)^2) := by
            have h8 : (A.card : ℝ)^2 / (centers.card : ℝ) ≤
                ((centers.card : ℝ) * (∑ u ∈ centers, ((group u).card : ℝ)^2)) / (centers.card : ℝ) := by
              gcongr
            have h9 : ((centers.card : ℝ) * (∑ u ∈ centers, ((group u).card : ℝ)^2)) / (centers.card : ℝ) =
                (∑ u ∈ centers, ((group u).card : ℝ)^2) := by
              have hM_ne : (centers.card : ℝ) ≠ 0 := hM_pos.ne'
              have h10 : ((centers.card : ℝ) * (∑ u ∈ centers, ((group u).card : ℝ)^2)) / (centers.card : ℝ) =
                  ((centers.card : ℝ) / (centers.card : ℝ)) * (∑ u ∈ centers, ((group u).card : ℝ)^2) := by ring
              rw [h10, div_self hM_ne]
              <;> ring
            rw [h9] at h8
            exact h8
          exact h7

        have h7 : ((A.card : ℝ)^2 / (centers.card : ℝ)) * (2 * δ)^(-γ) ≤ E := by
          calc
            ((A.card : ℝ)^2 / (centers.card : ℝ)) * (2 * δ)^(-γ)
              ≤ (∑ u ∈ centers, ((group u).card : ℝ)^2) * (2 * δ)^(-γ) := by gcongr <;> exact h_sum_sq_ge
          _ ≤ (∑ x ∈ A, ∑ y ∈ A, (max (dist (f x) (f y)) δ)^(-γ)) := h_sum_ge
          _ ≤ E := h_energy

        have h8 : (A.card : ℝ)^2 ≤ (centers.card : ℝ) * (E * (2 * δ)^γ) := by
          have h9 : 0 < (2 * δ)^γ := by positivity
          have h10 : ((A.card : ℝ)^2 / (centers.card : ℝ)) ≤ E * (2 * δ)^γ := by
            have h11 : ((A.card : ℝ)^2 / (centers.card : ℝ)) * (2 * δ)^(-γ) ≤ E := h7
            have h12 : (2 * δ)^(-γ) = 1 / (2 * δ)^γ := by
              rw [Real.rpow_neg (by linarith)] <;> field_simp
            rw [h12] at h11
            have h13 : ((A.card : ℝ)^2 / (centers.card : ℝ)) ≤ E * (2 * δ)^γ := by
              calc
                ((A.card : ℝ)^2 / (centers.card : ℝ))
                  = (((A.card : ℝ)^2 / (centers.card : ℝ)) * (1 / (2 * δ)^γ)) * (2 * δ)^γ := by
                    field_simp [h9.ne'] <;> ring
              _ ≤ E * (2 * δ)^γ := by gcongr <;> linarith
            exact h13
          calc
            (A.card : ℝ)^2
              = ((A.card : ℝ)^2 / (centers.card : ℝ)) * (centers.card : ℝ) := by
                field_simp [hM_pos.ne'] <;> ring
          _ ≤ (E * (2 * δ)^γ) * (centers.card : ℝ) := by gcongr <;> exact h10
          _ = (centers.card : ℝ) * (E * (2 * δ)^γ) := by ring

        have h9 : B ≤ (centers.card : ℝ) := by
          rw [hB_def]
          calc
            (A.card : ℝ)^2 / (E * (2 * δ)^γ)
              ≤ ((centers.card : ℝ) * (E * (2 * δ)^γ)) / (E * (2 * δ)^γ) := by gcongr
          _ = (centers.card : ℝ) := by field_simp [h_denom_pos.ne'] <;> ring

        have h10 : Nat.ceil B ≤ centers.card := by
          rw [Nat.ceil_le]
          exact h9

        have h11 : (centers : Set ℝ).encard = (↑centers.card : ENat) :=
          Set.encard_coe_eq_coe_finsetCard centers
        have h12 : (centers : Set ℝ).encard ≤ C.encard := Set.encard_le_encard h_centers_subset
        rw [h11] at h12
        have h13 : (↑(Nat.ceil B) : ENat) ≤ (↑centers.card : ENat) := by
          exact_mod_cast h10
        exact h13.trans h12

      have h9 : (Nat.ceil B : ENat) ≤ Metric.externalCoveringNumber (Real.toNNReal δ) (f '' (A : Set α)) := by
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
          (Metric.externalCoveringNumber (Real.toNNReal δ) (f '' (A : Set α)) : ENNReal) := by
        exact_mod_cast h9
      exact h10.trans h11

/-- Kaufman projection theorem with an explicit uniform constant. -/
theorem kaufman_projection
    {F Λ : DiscreteSet 2} {δ C d α β γ : ℝ}
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hγ_lt_alpha : γ < α) (hγ_lt_beta : γ < β)
    (hC : 0 ≤ C) (hd_pos : 0 < d)
    (hF_frost : F.IsFrostman δ α (ENNReal.ofReal C))
    (hΛ_frost : Λ.IsFrostman δ β (ENNReal.ofReal C))
    (hF_sep : F.IsDeltaSeparated δ)
    (hΛ_sep : Λ.IsDeltaSeparated δ)
    (hF_ball : F.IsInUnitBall)
    (hunit : ∀ θ ∈ Λ, ‖θ‖ = 1)
    (H : Finset (Point2 × Point2))
    (hH_sub : ∀ h ∈ H, h.1 ∈ Λ ∧ h.2 ∈ F)
    (h_dense : ∀ θ ∈ Λ, (fiber H θ).card ≥ d * F.card)
    (hneF : F.Nonempty) (hΛ_nonempty : Λ.Nonempty) :
    ∃ (θ : Point2), θ ∈ Λ ∧
      Metric.externalCoveringNumber (Real.toNNReal δ)
        (inner ℝ θ '' (F : Set Point2)) ≥
      ENNReal.ofReal
          (d ^ 2 /
            (2 * kaufman_total_const (max 1 C) α β γ * (2 : ℝ) ^ γ)) *
        Kakeya.realRpowENN δ (-γ) := by
  classical
  -- Prove C > 0 from Frostman
  have hC_pos : 0 < C := by
    by_contra h
    have hC0 : C = 0 := by linarith
    obtain ⟨θ, hθ⟩ := hΛ_nonempty
    have h1 : ((Λ.filter (fun y => dist y θ ≤ δ)).card : ℝ) ≤ C * δ^β * (Λ.card : ℝ) :=
      frostman_real_bound hδ hC hΛ_frost (by linarith) hδ_le_one
    have h2 : θ ∈ Λ.filter (fun y => dist y θ ≤ δ) := by
      simp only [Finset.mem_filter]
      exact ⟨hθ, by simp [hδ.le]⟩
    have h3 : 0 < (Λ.filter (fun y => dist y θ ≤ δ)).card := Finset.card_pos.mpr ⟨θ, h2⟩
    rw [hC0] at h1
    have h4 : ((Λ.filter (fun y => dist y θ ≤ δ)).card : ℝ) ≤ 0 := by simpa using h1
    have h5 : 0 < ((Λ.filter (fun y => dist y θ ≤ δ)).card : ℝ) := by exact_mod_cast h3
    linarith

  -- Use C' = max(1, C) to satisfy 1 ≤ C for the energy bound
  let C' : ℝ := max 1 C
  have hC'_ge_one : 1 ≤ C' := le_max_left _ _
  have hC'_pos : 0 < C' := by linarith
  have hC_le_C' : C ≤ C' := le_max_right _ _
  have h_ofReal_mono : ENNReal.ofReal C ≤ ENNReal.ofReal C' := by
    exact ENNReal.ofReal_le_ofReal hC_le_C'
  have hF_frost' : F.IsFrostman δ α (ENNReal.ofReal C') := by
    intro x r hδr hr1
    have h_orig := hF_frost x r hδr hr1
    have h_mono : ENNReal.ofReal C * Kakeya.realRpowENN r α * F.enncard ≤
               ENNReal.ofReal C' * Kakeya.realRpowENN r α * F.enncard := by
      gcongr
      <;> exact h_ofReal_mono
    exact le_trans h_orig h_mono
  have hΛ_frost' : Λ.IsFrostman δ β (ENNReal.ofReal C') := by
    intro x r hδr hr1
    have h_orig := hΛ_frost x r hδr hr1
    have h_mono : ENNReal.ofReal C * Kakeya.realRpowENN r β * Λ.enncard ≤
               ENNReal.ofReal C' * Kakeya.realRpowENN r β * Λ.enncard := by
      gcongr
      <;> exact h_ofReal_mono
    exact le_trans h_orig h_mono

  -- F is nonempty by hypothesis
  -- K_const positivity
  let K_const : ℝ := kaufman_total_const C' α β γ
  have hK_const_pos : 0 < K_const := by
    dsimp only [K_const, kaufman_total_const]
    have hK_ang_pos : 0 < kaufman_K_ang β γ := by
      dsimp only [kaufman_K_ang]
      have h1 : 0 < (Real.sqrt 2)^β := by positivity
      have h2 : 0 < (2 : ℝ)^γ := by positivity
      have h3 : 0 < (1 : ℝ) - (2 : ℝ)^(-(β - γ)) := by
        have h4 : 0 < β - γ := by linarith
        have h5 : 1 < (2 : ℝ)^(β - γ) := Real.one_lt_rpow (by norm_num) h4
        have h6 : (2 : ℝ)^(-(β - γ)) = ((2 : ℝ)^(β - γ))⁻¹ := by
          rw [Real.rpow_neg (by norm_num)] <;> field_simp
        rw [h6]
        have h7 : 0 < (2 : ℝ)^(β - γ) := by positivity
        have h8 : ((2 : ℝ)^(β - γ))⁻¹ < 1 := by
          have h9 : 1 / ((2 : ℝ)^(β - γ)) < 1 := by
            apply (div_lt_one h7).mpr
            exact h5
          simpa [one_div] using h9
        linarith
      positivity
    have hK_frost0_pos : 0 < kaufman_K_frost0 α γ := by
      dsimp only [kaufman_K_frost0]
      have h1 : 0 < (2 : ℝ)^(α - γ) - 1 := by
        have h2 : 0 < α - γ := by linarith
        have h3 : 1 < (2 : ℝ)^(α - γ) := Real.one_lt_rpow (by norm_num) h2
        linarith
      positivity
    have h4 : 0 < C' + kaufman_K_ang β γ * kaufman_K_frost0 α γ * (1 + C') + kaufman_K_ang β γ := by positivity
    exact mul_pos h4 hC'_pos

  have h_total_energy :
      ∑ θ ∈ Λ, ∑ x ∈ fiber H θ, ∑ y ∈ fiber H θ,
          (max (dist (inner ℝ θ x) (inner ℝ θ y)) δ)^(-γ) ≤
      K_const * (F.card : ℝ)^2 * (Λ.card : ℝ) :=
    projection_energy_total hδ hδ_le_one hα hβ hγ hγ_lt_alpha hγ_lt_beta
      hC'_pos.le hC'_ge_one hF_frost' hΛ_frost' hF_sep hΛ_sep hF_ball hunit hneF hΛ_nonempty H hH_sub

  let E_total := K_const * (F.card : ℝ)^2 * (Λ.card : ℝ)
  let E (θ : Point2) : ℝ :=
    ∑ x ∈ fiber H θ, ∑ y ∈ fiber H θ,
      (max (dist (inner ℝ θ x) (inner ℝ θ y)) δ)^(-γ)
  have hE_nonneg : ∀ θ ∈ Λ, 0 ≤ E θ := by
    intro θ _
    apply Finset.sum_nonneg
    intro x _
    apply Finset.sum_nonneg
    intro y _
    positivity
  have h_sum : ∑ θ ∈ Λ, E θ ≤ E_total := h_total_energy
  rcases markov_good_directions E hE_nonneg h_sum hΛ_nonempty with
    ⟨Λ_good, hΛg_sub, hΛg_card, hΛg_energy⟩
  have hΛg_nonempty : Λ_good.Nonempty := by
    by_contra h
    have h_empty : Λ_good = ∅ := by simpa using h
    rw [h_empty] at hΛg_card
    have h_pos : (Λ.card : ℝ) > 0 := by exact_mod_cast hΛ_nonempty.card_pos
    have h_cont : (0 : ℝ) ≥ (Λ.card : ℝ) / 2 := by simpa using hΛg_card
    linarith
  let θ : Point2 := Classical.choose hΛg_nonempty
  have hθ_good : θ ∈ Λ_good := Classical.choose_spec hΛg_nonempty
  have hθ_in_Λ : θ ∈ Λ := hΛg_sub hθ_good
  have hE_θ : E θ ≤ 2 * E_total / (Λ.card : ℝ) := hΛg_energy θ hθ_good
  have h_dense_θ : (fiber H θ).card ≥ d * F.card := h_dense θ hθ_in_Λ
  have h_fiber_nonempty : (fiber H θ).Nonempty := by
    have h12 : ((fiber H θ).card : ℝ) ≥ d * (F.card : ℝ) := by exact_mod_cast h_dense_θ
    have h13 : 0 < d * (F.card : ℝ) := mul_pos hd_pos (by exact_mod_cast hneF.card_pos)
    have h14 : 0 < ((fiber H θ).card : ℝ) := by linarith
    exact Finset.card_pos.mp (by exact_mod_cast h14)

  have hEθ_pos : 0 < E θ := by
    rcases h_fiber_nonempty with ⟨x, hx⟩
    let g' : Point2 → Point2 → ℝ := fun x' y =>
      (max (dist (inner ℝ θ x') (inner ℝ θ y)) δ)^(-γ)
    have hg_nonneg : ∀ x' ∈ fiber H θ, 0 ≤ ∑ y ∈ fiber H θ, g' x' y := by
      intro x' _
      apply Finset.sum_nonneg
      intro y _
      positivity
    have h4 : 0 < g' x x := by
      dsimp only [g']
      have h5 : dist (inner ℝ θ x) (inner ℝ θ x) = 0 := by simp
      rw [h5]
      have h6 : max (0 : ℝ) δ = δ := by rw [max_eq_right] <;> linarith
      rw [h6]
      exact Real.rpow_pos_of_pos hδ _
    have h5 : g' x x ≤ ∑ y ∈ fiber H θ, g' x y :=
      Finset.single_le_sum (fun y _ => by positivity) hx
    have h6 : 0 < ∑ y ∈ fiber H θ, g' x y := h4.trans_le h5
    have h7 : (∑ y ∈ fiber H θ, g' x y) ≤ E θ :=
      Finset.single_le_sum hg_nonneg hx
    exact h6.trans_le h7
  have hE_θ_bound : E θ ≤ 2 * K_const * (F.card : ℝ)^2 := by
    have hΛ_pos : 0 < (Λ.card : ℝ) := by exact_mod_cast hΛ_nonempty.card_pos
    have h : 2 * E_total / (Λ.card : ℝ) = 2 * K_const * (F.card : ℝ)^2 := by
      dsimp only [E_total]
      field_simp [hΛ_pos.ne'] <;> ring
    rw [h] at hE_θ
    exact hE_θ

  -- Apply projected energy-to-covering to the fiber
  have h_covering :
      Metric.externalCoveringNumber (Real.toNNReal δ) (inner ℝ θ '' (fiber H θ : Set Point2)) ≥
      ENNReal.ofReal (((fiber H θ).card : ℝ)^2 / ((E θ) * (2 * δ)^γ)) :=
    projected_energy_to_covering (fiber H θ) (inner ℝ θ) hδ hγ (by positivity) (le_refl (E θ))

  -- Projection of fiber is subset of projection of F
  have h_subset : (inner ℝ θ '' (fiber H θ : Set Point2)) ⊆ inner ℝ θ '' (F : Set Point2) := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    have hxF : x ∈ F := by
      have h_in_fiber : x ∈ fiber H θ := hx
      rcases Finset.mem_image.mp h_in_fiber with ⟨h, hh, rfl⟩
      have h_in_H : h ∈ H := (Finset.mem_filter.mp hh).1
      exact (hH_sub h h_in_H).2
    exact Set.mem_image_of_mem _ hxF

  have h_covering_monotone :
      Metric.externalCoveringNumber (Real.toNNReal δ) (inner ℝ θ '' (fiber H θ : Set Point2)) ≤
      Metric.externalCoveringNumber (Real.toNNReal δ) (inner ℝ θ '' (F : Set Point2)) :=
    Metric.externalCoveringNumber_mono_set h_subset

  have h_final_ineq :
      (Metric.externalCoveringNumber (Real.toNNReal δ) (inner ℝ θ '' (F : Set Point2)) : ENNReal) ≥
      ENNReal.ofReal (((fiber H θ).card : ℝ)^2 / ((E θ) * (2 * δ)^γ)) := by
    have h_covering' : (Metric.externalCoveringNumber (Real.toNNReal δ) (inner ℝ θ '' (fiber H θ : Set Point2)) : ENNReal) ≥
        ENNReal.ofReal (((fiber H θ).card : ℝ)^2 / ((E θ) * (2 * δ)^γ)) := h_covering
    have h_monotone' : (Metric.externalCoveringNumber (Real.toNNReal δ) (inner ℝ θ '' (fiber H θ : Set Point2)) : ENNReal) ≤
        (Metric.externalCoveringNumber (Real.toNNReal δ) (inner ℝ θ '' (F : Set Point2)) : ENNReal) := by
      exact_mod_cast h_covering_monotone
    exact h_covering'.trans h_monotone'

  have h_main_real : ((fiber H θ).card : ℝ)^2 / ((E θ) * (2 * δ)^γ) ≥
      d^2 / (2 * K_const * (2 : ℝ)^γ) * δ^(-γ) := by
    have h1 : (E θ) ≤ 2 * K_const * (F.card : ℝ)^2 := hE_θ_bound
    have h2 : ((fiber H θ).card : ℝ) ≥ d * (F.card : ℝ) := by exact_mod_cast h_dense_θ
    have h3 : 0 < (E θ) * (2 * δ)^γ := mul_pos hEθ_pos (by positivity)
    have h4 : 0 < d * (F.card : ℝ) := by
      exact mul_pos hd_pos (by exact_mod_cast hneF.card_pos)
    have h5 : 0 < (2 * K_const * (F.card : ℝ)^2) * (2 * δ)^γ := by positivity
    have h6 : (2 * δ)^γ = (2 : ℝ)^γ * δ^γ := by
      rw [Real.mul_rpow (by norm_num) (by linarith)] <;> ring
    have h7 : δ ^ γ * δ ^ (-γ) = 1 := by
      have h71 : δ ^ (-γ) = (δ ^ γ)⁻¹ := by
        rw [Real.rpow_neg hδ.le] <;> field_simp
      rw [h71]
      have h72 : 0 < δ ^ γ := Real.rpow_pos_of_pos hδ γ
      field_simp [h72.ne'] <;> ring
    calc
      ((fiber H θ).card : ℝ)^2 / ((E θ) * (2 * δ)^γ)
        ≥ (d * (F.card : ℝ))^2 / ((E θ) * (2 * δ)^γ) := by gcongr
    _ ≥ (d * (F.card : ℝ))^2 / ((2 * K_const * (F.card : ℝ)^2) * (2 * δ)^γ) := by
      have h_denom_le : (E θ) * (2 * δ)^γ ≤ (2 * K_const * (F.card : ℝ)^2) * (2 * δ)^γ := by
        gcongr <;> exact h1
      have h_num_pos : 0 ≤ (d * (F.card : ℝ))^2 := by positivity
      exact div_le_div_of_nonneg_left h_num_pos h3 h_denom_le
    _ = d^2 / (2 * K_const * (2 : ℝ)^γ) * δ^(-γ) := by
        rw [h6]
        have hF2_ne : (F.card : ℝ)^2 ≠ 0 := by positivity
        have hδγ_ne : δ ^ γ ≠ 0 := by positivity
        have h2γ_ne : (2 : ℝ)^γ ≠ 0 := by positivity
        have hK_ne : K_const ≠ 0 := hK_const_pos.ne'
        have h9 : δ^(-γ) = (δ^γ)⁻¹ := by
          rw [Real.rpow_neg hδ.le] <;> field_simp
        have h_goal : (d * (F.card : ℝ))^2 / ((2 * K_const * (F.card : ℝ)^2) * ((2 : ℝ)^γ * δ^γ)) =
            d^2 / (2 * K_const * (2 : ℝ)^γ) * (δ^γ)⁻¹ := by
          calc
            (d * (F.card : ℝ))^2 / ((2 * K_const * (F.card : ℝ)^2) * ((2 : ℝ)^γ * δ^γ))
              = d^2 * (F.card : ℝ)^2 / (2 * K_const * (F.card : ℝ)^2 * (2 : ℝ)^γ * δ^γ) := by ring
          _ = d^2 / (2 * K_const * (2 : ℝ)^γ * δ^γ) := by
              field_simp [hF2_ne, hK_ne, h2γ_ne, hδγ_ne] <;> ring
          _ = d^2 / (2 * K_const * (2 : ℝ)^γ) * (δ^γ)⁻¹ := by
              field_simp [hδγ_ne] <;> ring
        rw [h_goal, h9]

  -- C_raw uses C' (the max(1,C) constant)
  let C_raw : ENNReal := ENNReal.ofReal (d^2 / (2 * K_const * (2 : ℝ)^γ))
  have hC_raw_pos : 0 < C_raw := by
    dsimp only [C_raw]
    apply ENNReal.ofReal_pos.mpr
    have h_pos1 : 0 < d^2 := by positivity
    have h_pos2 : 0 < 2 * K_const * (2 : ℝ)^γ := by
      exact mul_pos (mul_pos (by norm_num) hK_const_pos) (by positivity)
    exact div_pos h_pos1 h_pos2

  have h_raw_bound : Metric.externalCoveringNumber (Real.toNNReal δ) (inner ℝ θ '' (F : Set Point2)) ≥
      C_raw * Kakeya.realRpowENN δ (-γ) := by
    have h1 : ENNReal.ofReal (((fiber H θ).card : ℝ)^2 / ((E θ) * (2 * δ)^γ)) ≥
        C_raw * Kakeya.realRpowENN δ (-γ) := by
      dsimp only [C_raw]
      have h2 : Kakeya.realRpowENN δ (-γ) = ENNReal.ofReal (δ^(-γ)) := by
        simp [Kakeya.realRpowENN] <;> rfl
      rw [h2]
      have h_pos1 : 0 ≤ d^2 / (2 * K_const * (2 : ℝ)^γ) := by positivity
      have h_pos2 : 0 ≤ δ^(-γ) := by positivity
      have h3 : ENNReal.ofReal (d^2 / (2 * K_const * (2 : ℝ)^γ)) * ENNReal.ofReal (δ^(-γ)) =
          ENNReal.ofReal ((d^2 / (2 * K_const * (2 : ℝ)^γ)) * δ^(-γ)) := by
        have h4 : ENNReal.ofReal ((d^2 / (2 * K_const * (2 : ℝ)^γ)) * δ^(-γ)) =
            ENNReal.ofReal (d^2 / (2 * K_const * (2 : ℝ)^γ)) * ENNReal.ofReal (δ^(-γ)) :=
          ENNReal.ofReal_mul (p := d^2 / (2 * K_const * (2 : ℝ)^γ)) (q := δ^(-γ)) h_pos1
        exact h4.symm
      rw [h3]
      exact ENNReal.ofReal_le_ofReal h_main_real
    exact h1.trans h_final_ineq

  refine ⟨θ, hθ_in_Λ, ?_⟩
  simpa [C_raw, K_const, C'] using h_raw_bound

end Kakeya.Assouad
