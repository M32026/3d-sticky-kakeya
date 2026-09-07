module

/-
  Packing bound for AffineLine and common tubes bound.
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.OSWPrelude

@[expose] public section


open scoped ENNReal NNReal

namespace DirecretisedFurstenbergEstimate.MainAppendix

open DirecretisedFurstenbergEstimate

/-! ### General packing bound for finite-dimensional normed spaces -/

lemma exists_packing_constant_general
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (R : ℝ) (hR : 0 < R) :
    ∃ (K : ℕ), ∀ (x : V) (S : Set V),
      S ⊆ Metric.closedBall x R →
      Set.Pairwise S (fun a b => (1 : ℝ) ≤ dist a b) →
      S.Finite ∧ S.encard ≤ (K : ENat) := by
  classical
  have h_compact : IsCompact (Metric.closedBall (0 : V) R) := by
    haveI : ProperSpace V := by exact ProperSpace.of_locallyCompactSpace ℝ
    exact isCompact_closedBall 0 R
  have h_uniform : {p : V × V | dist p.1 p.2 < (1 / 3 : ℝ)} ∈ uniformity V :=
    Metric.uniformity_basis_dist.mem_of_mem (by norm_num)
  rcases h_compact.totallyBounded _ h_uniform with ⟨N, hN_fin, hN_cover_raw⟩
  have hN_cover : (Metric.closedBall (0 : V) R) ⊆ ⋃ y ∈ N, Metric.ball y (1 / 3 : ℝ) := by
    intro z hz
    have h9 : z ∈ ⋃ y ∈ N, {x : V | dist x y < (1 / 3 : ℝ)} := hN_cover_raw hz
    simpa [Metric.ball, Set.mem_iUnion] using h9
  let N' : Finset V := Set.Finite.toFinset hN_fin
  let K : ℕ := N'.card
  use K
  intro x S h_sub h_sep
  let S0 : Set V := (fun y : V => y - x) '' S
  have hS0_sub : S0 ⊆ Metric.closedBall (0 : V) R := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    have h1 : dist y x ≤ R := h_sub hy
    have h2 : ‖y - x‖ ≤ R := by simpa [dist_eq_norm] using h1
    simpa [dist_zero_right] using h2
  have hS0_sep : Set.Pairwise S0 (fun a b => (1 : ℝ) ≤ dist a b) := by
    intro a ha b hb hne
    rcases ha with ⟨y, hy, rfl⟩
    rcases hb with ⟨z, hz, rfl⟩
    have h_yne_z : y ≠ z := by intro h; apply hne; simp [h]
    have h2 : (1 : ℝ) ≤ dist y z := h_sep hy hz h_yne_z
    have h3 : dist (y - x) (z - x) = dist y z := by
      simp [dist_eq_norm] <;> abel
    rw [h3]; exact h2
  have h_forall : ∀ (y : V), y ∈ S0 → ∃ (c : V), c ∈ N' ∧ dist y c < 1 / 3 := by
    intro y hy
    have h5 : y ∈ Metric.closedBall (0 : V) R := hS0_sub hy
    have h6 : y ∈ ⋃ c ∈ N, Metric.ball c (1 / 3 : ℝ) := hN_cover h5
    have h7 : ∃ (c : V), c ∈ N ∧ dist y c < 1 / 3 := by simpa [Set.mem_iUnion] using h6
    rcases h7 with ⟨c, hc1, hc2⟩
    have hc1' : c ∈ N' := by simpa [N', Set.Finite.mem_toFinset] using hc1
    exact ⟨c, hc1', hc2⟩
  let f : V → V := fun y => if h : y ∈ S0 then Classical.choose (h_forall y h) else 0
  have hf1 : ∀ y ∈ S0, f y ∈ N' := by
    intro y hy
    have h_eq : f y = Classical.choose (h_forall y hy) := by
      dsimp only [f]
      rw [dif_pos hy]
    rw [h_eq]
    exact (Classical.choose_spec (h_forall y hy)).1
  have hf2 : ∀ y ∈ S0, dist y (f y) < 1 / 3 := by
    intro y hy
    have h_eq : f y = Classical.choose (h_forall y hy) := by
      dsimp only [f]
      rw [dif_pos hy]
    rw [h_eq]
    exact (Classical.choose_spec (h_forall y hy)).2
  have h_inj : Set.InjOn f S0 := by
    intro y hy z hz h_eq
    by_cases h_yz : y = z
    · exact h_yz
    · have h_d1 : dist y (f y) < 1 / 3 := hf2 y hy
      have h_d2 : dist z (f z) < 1 / 3 := hf2 z hz
      have h_d3 : dist z (f y) < 1 / 3 := by have h4 : f z = f y := h_eq.symm; rw [h4] at h_d2; exact h_d2
      have h_tri : dist y z ≤ dist y (f y) + dist (f y) z := dist_triangle _ _ _
      have h_comm : dist (f y) z = dist z (f y) := dist_comm _ _
      have h_sum : dist y z < 1 / 3 + 1 / 3 := by
        calc dist y z
          ≤ dist y (f y) + dist z (f y) := by rw [h_comm] at h_tri; exact h_tri
        _ < 1 / 3 + 1 / 3 := add_lt_add h_d1 h_d3
      have h_dist : dist y z < 2 / 3 := by
        rw [show (1 / 3 : ℝ) + 1 / 3 = 2 / 3 by norm_num] at h_sum; exact h_sum
      have h_sep' : (1 : ℝ) ≤ dist y z := hS0_sep hy hz h_yz
      linarith
  have h_image : (f '' S0).Finite := by
    apply Set.Finite.subset N'.finite_toSet
    intro w hw; rcases hw with ⟨y, hy, rfl⟩; exact hf1 y hy
  have hS0_fin : S0.Finite := (Set.finite_image_iff h_inj).mp h_image
  have hS0_card : S0.encard ≤ (K : ENat) := by
    have h1 : S0.encard = (f '' S0).encard := (Set.InjOn.encard_image h_inj).symm
    rw [h1]
    have h2 : (f '' S0) ⊆ (N' : Set V) := by
      intro w hw
      rcases hw with ⟨y, hy, rfl⟩
      exact hf1 y hy
    have h3 : (f '' S0).encard ≤ (N' : Set V).encard := Set.encard_le_encard h2
    have h4 : (N' : Set V).encard = (N'.card : ENat) := by simp
    rw [h4] at h3
    exact h3
  have h_transl_inj : Set.InjOn (fun y : V => y - x) S := by intro y _ z _ h; simpa using h
  have hS_encard : S.encard = S0.encard := (Set.InjOn.encard_image h_transl_inj).symm
  have hS_fin : S.Finite := (Set.finite_image_iff h_transl_inj).mp hS0_fin
  rw [hS_encard]
  exact ⟨hS_fin, hS0_card⟩

/-! ### AffineLine packing bound -/

abbrev AffineLineEmbeddingV :=
  (EuclideanPlane →L[ℝ] EuclideanPlane) × EuclideanPlane

noncomputable def affineLine_packing_constant : ℕ :=
  Classical.choose (exists_packing_constant_general (R := (8 : ℝ)) (by norm_num)
    (V := AffineLineEmbeddingV))

lemma affineLine_packing_bound
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    {S : Set AffineLine}
    (h_sep : Set.Pairwise S (fun x y => Δ ≤ dist x y))
    (z : AffineLine)
    (h_sub : S ⊆ Metric.closedBall z (2 * Δ)) :
    S.Finite ∧ S.encard ≤ ↑affineLine_packing_constant := by
  let V := AffineLineEmbeddingV
  let f : AffineLine → V := fun ℓ => (ℓ.1.direction.starProjection, ℓ.offset)
  let S' : Set V := f '' S
  have h1 : ∀ ℓ₁ ℓ₂ : AffineLine, dist (f ℓ₁) (f ℓ₂) ≤ dist ℓ₁ ℓ₂ := by
    intro ℓ₁ ℓ₂
    let a := ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖
    let b := ‖ℓ₁.offset - ℓ₂.offset‖
    have h_distV : dist (f ℓ₁) (f ℓ₂) = max (‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖) (‖ℓ₁.offset - ℓ₂.offset‖) := by
      have h : dist (f ℓ₁) (f ℓ₂) = dist (ℓ₁.1.direction.starProjection, ℓ₁.offset) (ℓ₂.1.direction.starProjection, ℓ₂.offset) := by rfl
      rw [h]
      simp [dist_eq_norm]
      <;> rfl
    rw [h_distV]
    let a := ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖
    let b := ‖ℓ₁.offset - ℓ₂.offset‖
    have ha : 0 ≤ a := norm_nonneg _
    have hb : 0 ≤ b := norm_nonneg _
    have h : max a b ≤ a + b := max_le (le_add_of_nonneg_right hb) (le_add_of_nonneg_left ha)
    have h_distA : dist ℓ₁ ℓ₂ = a + b := by rfl
    rw [h_distA]
    exact h
  have h2 : ∀ ℓ₁ ℓ₂ : AffineLine, dist ℓ₁ ℓ₂ ≤ 2 * dist (f ℓ₁) (f ℓ₂) := by
    intro ℓ₁ ℓ₂
    let a := ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖
    let b := ‖ℓ₁.offset - ℓ₂.offset‖
    have h_distV : dist (f ℓ₁) (f ℓ₂) = max (‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖) (‖ℓ₁.offset - ℓ₂.offset‖) := by
      have h : dist (f ℓ₁) (f ℓ₂) = dist (ℓ₁.1.direction.starProjection, ℓ₁.offset) (ℓ₂.1.direction.starProjection, ℓ₂.offset) := by rfl
      rw [h]
      simp [dist_eq_norm]
      <;> rfl
    rw [h_distV]
    let a := ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖
    let b := ‖ℓ₁.offset - ℓ₂.offset‖
    have h4 : a ≤ max a b := le_max_left a b
    have h5 : b ≤ max a b := le_max_right a b
    have h : a + b ≤ 2 * max a b := by linarith
    have h_distA : dist ℓ₁ ℓ₂ = a + b := by rfl
    rw [h_distA]
    exact h
  have h_f_inj : Function.Injective f := by
    intro ℓ₁ ℓ₂ h
    have h_dist : dist (f ℓ₁) (f ℓ₂) = 0 := by rw [h] <;> simp
    have h2 : dist ℓ₁ ℓ₂ ≤ 2 * dist (f ℓ₁) (f ℓ₂) := h2 ℓ₁ ℓ₂
    rw [h_dist] at h2
    have h3 : dist ℓ₁ ℓ₂ ≤ 0 := by linarith
    have h4 : 0 ≤ dist ℓ₁ ℓ₂ := dist_nonneg
    have h5 : dist ℓ₁ ℓ₂ = 0 := by linarith
    exact dist_eq_zero.mp h5
  have hS'_sep : Set.Pairwise S' (fun a b => Δ / 2 ≤ dist a b) := by
    intro a ha b hb hne
    rcases ha with ⟨ℓ₁, hℓ₁, rfl⟩
    rcases hb with ⟨ℓ₂, hℓ₂, rfl⟩
    have h_ℓne : ℓ₁ ≠ ℓ₂ := by
      intro h
      apply hne
      have h' : f ℓ₁ = f ℓ₂ := by rw [h]
      exact h'
    have h3 : Δ ≤ dist ℓ₁ ℓ₂ := h_sep hℓ₁ hℓ₂ h_ℓne
    have h4 : dist ℓ₁ ℓ₂ ≤ 2 * dist (f ℓ₁) (f ℓ₂) := h2 ℓ₁ ℓ₂
    linarith
  have hS'_sub : S' ⊆ Metric.closedBall (f z) (2 * Δ) := by
    intro w hw
    rcases hw with ⟨ℓ, hℓ, rfl⟩
    have h5 : dist ℓ z ≤ 2 * Δ := h_sub hℓ
    have h6 : dist (f ℓ) (f z) ≤ dist ℓ z := h1 ℓ z
    exact le_trans h6 h5
  let g : V → V := fun w => (2 / Δ) • w
  let S'' : Set V := g '' S'
  have hS''_sep : Set.Pairwise S'' (fun a b => (1 : ℝ) ≤ dist a b) := by
    intro a ha b hb hne
    rcases ha with ⟨w1, hw1, rfl⟩
    rcases hb with ⟨w2, hw2, rfl⟩
    have h_wne : w1 ≠ w2 := by intro h; apply hne; simp [h]
    have h3 : Δ / 2 ≤ dist w1 w2 := hS'_sep hw1 hw2 h_wne
    have h4 : dist (g w1) (g w2) = (2 / Δ) * dist w1 w2 := by
      have h5 : dist (g w1) (g w2) = ‖g w1 - g w2‖ := by rw [dist_eq_norm]
      rw [h5]
      have h6 : g w1 - g w2 = (2 / Δ) • (w1 - w2) := by
        simp [g, smul_sub] <;> rfl
      rw [h6, norm_smul]
      have h9 : ‖(2 / Δ : ℝ)‖ = 2 / Δ := by
        rw [Real.norm_eq_abs, abs_of_pos]
        <;> field_simp [hΔ_pos.ne'] <;> linarith
      have h10 : ‖w1 - w2‖ = dist w1 w2 := by rw [dist_eq_norm]
      rw [h9, h10] <;> ring
    rw [h4]
    have h5 : (2 / Δ) * (Δ / 2) = 1 := by field_simp [hΔ_pos.ne'] <;> ring
    have h6 : (1 : ℝ) ≤ (2 / Δ) * dist w1 w2 := by
      calc (1 : ℝ)
        = (2 / Δ) * (Δ / 2) := h5.symm
      _ ≤ (2 / Δ) * dist w1 w2 := by gcongr
    exact h6
  have hS''_sub : S'' ⊆ Metric.closedBall (g (f z)) 8 := by
    intro w hw
    rcases hw with ⟨v, hv, rfl⟩
    have h5 : dist v (f z) ≤ 2 * Δ := hS'_sub hv
    have h6 : dist (g v) (g (f z)) = (2 / Δ) * dist v (f z) := by
      have h7 : dist (g v) (g (f z)) = ‖g v - g (f z)‖ := by rw [dist_eq_norm]
      rw [h7]
      have h8 : g v - g (f z) = (2 / Δ) • (v - f z) := by
        simp [g, smul_sub] <;> rfl
      rw [h8, norm_smul]
      have h9 : ‖(2 / Δ : ℝ)‖ = 2 / Δ := by
        rw [Real.norm_eq_abs, abs_of_pos]
        <;> field_simp [hΔ_pos.ne'] <;> linarith
      have h10 : ‖v - f z‖ = dist v (f z) := by rw [dist_eq_norm]
      rw [h9, h10] <;> ring
    have h7 : dist (g v) (g (f z)) ≤ 8 := by
      rw [h6]
      have h8 : (2 / Δ) * dist v (f z) ≤ (2 / Δ) * (2 * Δ) := by gcongr
      have h9 : (2 / Δ) * (2 * Δ) = 4 := by
        field_simp [hΔ_pos.ne'] <;> ring
      linarith
    simpa [Metric.mem_closedBall] using h7
  have h_prop := Classical.choose_spec (exists_packing_constant_general (R := (8 : ℝ)) (by norm_num)
    (V := V))
  rcases h_prop (g (f z)) S'' hS''_sub hS''_sep with ⟨hS''_fin, hS''_card⟩
  have h_g_inj : Function.Injective g := by
    intro v1 v2 h
    have h1 : (2 / Δ : ℝ) • v1 = (2 / Δ : ℝ) • v2 := h
    have h3 : ∀ (v : V), (Δ / 2 : ℝ) • ((2 / Δ : ℝ) • v) = v := by
      intro v
      have h4 : (Δ / 2 : ℝ) • ((2 / Δ : ℝ) • v) = ((Δ / 2 : ℝ) * (2 / Δ : ℝ)) • v := by
        rw [smul_smul]
      rw [h4]
      have h5 : (Δ / 2 : ℝ) * (2 / Δ : ℝ) = 1 := by field_simp [hΔ_pos.ne'] <;> ring
      rw [h5]
      simp
    have h6 : (Δ / 2 : ℝ) • ((2 / Δ : ℝ) • v1) = (Δ / 2 : ℝ) • ((2 / Δ : ℝ) • v2) := by rw [h1]
    have h7 := h3 v1
    have h8 := h3 v2
    rw [h7, h8] at h6
    exact h6
  have h_g_injOn : Set.InjOn g S' := fun x _ y _ h => h_g_inj h
  have hS'_fin : S'.Finite := (Set.finite_image_iff h_g_injOn).mp hS''_fin
  have h_f_injOn : Set.InjOn f S := fun x _ y _ h => h_f_inj h
  have hS_fin : S.Finite := (Set.finite_image_iff h_f_injOn).mp hS'_fin
  have hS_encard : S.encard = S''.encard := by
    calc S.encard
      = S'.encard := (Function.Injective.encard_image h_f_inj S).symm
    _ = S''.encard := (Function.Injective.encard_image h_g_inj S').symm
  rw [hS_encard]
  exact ⟨hS_fin, hS''_card⟩

/-- Packing constant for 1-separated sets in a 720-ball of AffineLineEmbeddingV. -/
noncomputable def affineLine_packing_constant_720 : ℕ :=
  Classical.choose (exists_packing_constant_general (R := (720 : ℝ)) (by norm_num)
    (V := AffineLineEmbeddingV))

/-- Packing bound for Δ/360-separated AffineLine sets in a Δ-ball.

    Uses embedding into V with dist(fx,fy) ≤ dist(x,y) ≤ 2·dist(fx,fy),
    scales by 720/Δ to get 1-separated points in a 720-ball. -/
lemma affineLine_packing_bound_720
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    {S : Set AffineLine}
    (h_sep : Set.Pairwise S (fun x y => Δ / 360 ≤ dist x y))
    (z : AffineLine)
    (h_sub : S ⊆ Metric.closedBall z Δ) :
    S.Finite ∧ S.encard ≤ ↑affineLine_packing_constant_720 := by
  let V := AffineLineEmbeddingV
  let f : AffineLine → V := fun ℓ => (ℓ.1.direction.starProjection, ℓ.offset)
  let S' : Set V := f '' S
  have h1 : ∀ ℓ₁ ℓ₂ : AffineLine, dist (f ℓ₁) (f ℓ₂) ≤ dist ℓ₁ ℓ₂ := by
    intro ℓ₁ ℓ₂
    have h_distV : dist (f ℓ₁) (f ℓ₂) = max (‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖) (‖ℓ₁.offset - ℓ₂.offset‖) := by
      have h : dist (f ℓ₁) (f ℓ₂) = max (dist (ℓ₁.1.direction.starProjection) (ℓ₂.1.direction.starProjection)) (dist ℓ₁.offset ℓ₂.offset) := by
        have h' := Prod.dist_eq (x := f ℓ₁) (y := f ℓ₂)
        simpa [f] using h'
      rw [h, dist_eq_norm, dist_eq_norm]
    rw [h_distV]
    let a := ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖
    let b := ‖ℓ₁.offset - ℓ₂.offset‖
    have ha : 0 ≤ a := norm_nonneg _
    have hb : 0 ≤ b := norm_nonneg _
    have h : max a b ≤ a + b := max_le (le_add_of_nonneg_right hb) (le_add_of_nonneg_left ha)
    have h_distA : dist ℓ₁ ℓ₂ = a + b := by rfl
    rw [h_distA]; exact h
  have h2 : ∀ ℓ₁ ℓ₂ : AffineLine, dist ℓ₁ ℓ₂ ≤ 2 * dist (f ℓ₁) (f ℓ₂) := by
    intro ℓ₁ ℓ₂
    have h_distV : dist (f ℓ₁) (f ℓ₂) = max (‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖) (‖ℓ₁.offset - ℓ₂.offset‖) := by
      have h : dist (f ℓ₁) (f ℓ₂) = max (dist (ℓ₁.1.direction.starProjection) (ℓ₂.1.direction.starProjection)) (dist ℓ₁.offset ℓ₂.offset) := by
        have h' := Prod.dist_eq (x := f ℓ₁) (y := f ℓ₂)
        simpa [f] using h'
      rw [h, dist_eq_norm, dist_eq_norm]
    rw [h_distV]
    let a := ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖
    let b := ‖ℓ₁.offset - ℓ₂.offset‖
    have h4 : a ≤ max a b := le_max_left a b
    have h5 : b ≤ max a b := le_max_right a b
    have h : a + b ≤ 2 * max a b := by linarith
    have h_distA : dist ℓ₁ ℓ₂ = a + b := by rfl
    rw [h_distA]; exact h
  have h_f_inj : Function.Injective f := by
    intro ℓ₁ ℓ₂ h
    have h_dist : dist (f ℓ₁) (f ℓ₂) = 0 := by rw [h] <;> simp
    have h3 : dist ℓ₁ ℓ₂ ≤ 2 * dist (f ℓ₁) (f ℓ₂) := h2 ℓ₁ ℓ₂
    rw [h_dist] at h3
    have h_pos : 0 ≤ dist ℓ₁ ℓ₂ := by positivity
    have h4 : dist ℓ₁ ℓ₂ = 0 := by linarith
    exact dist_eq_zero.mp h4
  have hS'_sep : Set.Pairwise S' (fun a b => Δ / 720 ≤ dist a b) := by
    intro a ha b hb hne
    rcases ha with ⟨ℓ₁, hℓ₁, rfl⟩
    rcases hb with ⟨ℓ₂, hℓ₂, rfl⟩
    have h_ℓne : ℓ₁ ≠ ℓ₂ := by intro h; apply hne; rw [h]
    have h3 : Δ / 360 ≤ dist ℓ₁ ℓ₂ := h_sep hℓ₁ hℓ₂ h_ℓne
    have h4 : dist ℓ₁ ℓ₂ ≤ 2 * dist (f ℓ₁) (f ℓ₂) := h2 ℓ₁ ℓ₂
    linarith
  have hS'_sub : S' ⊆ Metric.closedBall (f z) Δ := by
    intro w hw
    rcases hw with ⟨ℓ, hℓ, rfl⟩
    have h5 : dist ℓ z ≤ Δ := h_sub hℓ
    have h6 : dist (f ℓ) (f z) ≤ dist ℓ z := h1 ℓ z
    exact le_trans h6 h5
  let g : V → V := fun w => (720 / Δ) • w
  let S'' : Set V := g '' S'
  have hS''_sep : Set.Pairwise S'' (fun a b => (1 : ℝ) ≤ dist a b) := by
    intro a ha b hb hne
    rcases ha with ⟨w1, hw1, rfl⟩
    rcases hb with ⟨w2, hw2, rfl⟩
    have h_wne : w1 ≠ w2 := by intro h; apply hne; simp [h]
    have h3 : Δ / 720 ≤ dist w1 w2 := hS'_sep hw1 hw2 h_wne
    have h4 : dist (g w1) (g w2) = (720 / Δ) * dist w1 w2 := by
      have h5 : dist (g w1) (g w2) = ‖g w1 - g w2‖ := by rw [dist_eq_norm]
      rw [h5]
      have h6 : g w1 - g w2 = (720 / Δ) • (w1 - w2) := by simp [g, smul_sub] <;> rfl
      rw [h6, norm_smul]
      have h9 : ‖(720 / Δ : ℝ)‖ = 720 / Δ := by
        rw [Real.norm_eq_abs, abs_of_pos] <;> field_simp [hΔ_pos.ne'] <;> linarith
      have h10 : ‖w1 - w2‖ = dist w1 w2 := by rw [dist_eq_norm]
      rw [h9, h10] <;> ring
    rw [h4]
    have h5 : (720 / Δ) * (Δ / 720) = 1 := by field_simp [hΔ_pos.ne'] <;> ring
    have h6 : (1 : ℝ) ≤ (720 / Δ) * dist w1 w2 := by
      calc (1 : ℝ) = (720 / Δ) * (Δ / 720) := h5.symm
      _ ≤ (720 / Δ) * dist w1 w2 := by gcongr
    exact h6
  have hS''_sub : S'' ⊆ Metric.closedBall (g (f z)) 720 := by
    intro w hw
    rcases hw with ⟨v, hv, rfl⟩
    have h5 : dist v (f z) ≤ Δ := hS'_sub hv
    have h6 : dist (g v) (g (f z)) = (720 / Δ) * dist v (f z) := by
      have h7 : dist (g v) (g (f z)) = ‖g v - g (f z)‖ := by rw [dist_eq_norm]
      rw [h7]
      have h8 : g v - g (f z) = (720 / Δ) • (v - f z) := by simp [g, smul_sub] <;> rfl
      rw [h8, norm_smul]
      have h9 : ‖(720 / Δ : ℝ)‖ = 720 / Δ := by
        rw [Real.norm_eq_abs, abs_of_pos] <;> field_simp [hΔ_pos.ne'] <;> linarith
      have h10 : ‖v - f z‖ = dist v (f z) := by rw [dist_eq_norm]
      rw [h9, h10] <;> ring
    have h7 : dist (g v) (g (f z)) ≤ 720 := by
      rw [h6]
      have h8 : (720 / Δ) * dist v (f z) ≤ (720 / Δ) * Δ := by gcongr
      have h9 : (720 / Δ) * Δ = 720 := by field_simp [hΔ_pos.ne'] <;> ring
      linarith
    simpa [Metric.mem_closedBall] using h7
  have h_prop := Classical.choose_spec (exists_packing_constant_general (R := (720 : ℝ)) (by norm_num) (V := V))
  rcases h_prop (g (f z)) S'' hS''_sub hS''_sep with ⟨hS''_fin, hS''_card⟩
  have h_g_inj : Function.Injective g := by
    intro v1 v2 h
    have h1 : (720 / Δ : ℝ) • v1 = (720 / Δ : ℝ) • v2 := h
    have h3 : ∀ (v : V), (Δ / 720 : ℝ) • ((720 / Δ : ℝ) • v) = v := by
      intro v
      have h4 : (Δ / 720 : ℝ) • ((720 / Δ : ℝ) • v) = ((Δ / 720 : ℝ) * (720 / Δ : ℝ)) • v := by rw [smul_smul]
      rw [h4]
      have h5 : (Δ / 720 : ℝ) * (720 / Δ : ℝ) = 1 := by field_simp [hΔ_pos.ne'] <;> ring
      rw [h5]; simp
    have h4 : (Δ / 720 : ℝ) • ((720 / Δ : ℝ) • v1) = (Δ / 720 : ℝ) • ((720 / Δ : ℝ) • v2) := by
      rw [h1]
    have h6 := h3 v1
    have h7 := h3 v2
    rw [h6, h7] at h4
    exact h4
  have h_g_injOn : Set.InjOn g S' := fun x _ y _ h => h_g_inj h
  have hS'_fin : S'.Finite := (Set.finite_image_iff h_g_injOn).mp hS''_fin
  have h_f_injOn : Set.InjOn f S := fun x _ y _ h => h_f_inj h
  have hS_fin : S.Finite := (Set.finite_image_iff h_f_injOn).mp hS'_fin
  have hS_encard : S.encard = S''.encard := by
    calc S.encard
      = S'.encard := (Function.Injective.encard_image h_f_inj S).symm
    _ = S''.encard := (Function.Injective.encard_image h_g_inj S').symm
  rw [hS_encard]
  exact ⟨hS_fin, hS''_card⟩

/-! ### Covering-to-cardinality conversion -/

lemma separated_set_card_le_covering
    {X : Type*} [PseudoMetricSpace X] {δ : NNReal} {S : Set X}
    (hS_sep : Set.Pairwise S (fun x y => (δ : ℝ) ≤ dist x y))
    (K_pack : ℕ)
    (h_pack : ∀ (z : X) (T : Set X),
      Set.Pairwise T (fun x y => (δ : ℝ) ≤ dist x y) →
      T ⊆ Metric.closedBall z (2 * (δ : ℝ)) →
      T.Finite ∧ T.encard ≤ (K_pack : ENat))
    (hcov : (Metric.externalCoveringNumber δ S : ENNReal) < ⊤) :
    (S.encard : ENNReal) ≤ (K_pack : ENNReal) * (Metric.externalCoveringNumber δ S : ENNReal) := by
  classical
  have hcov' : Metric.externalCoveringNumber δ S < ⊤ := by exact_mod_cast hcov
  rcases DiscretisedFurstenbergEstimate.CoveringUtils.exists_external_cover_eq hcov' with ⟨C, hCcover, hC_eq⟩
  have hC_fin : C.Finite := by
    have h_lt : C.encard < ⊤ := by
      rw [hC_eq]
      exact hcov'
    exact Set.encard_lt_top_iff.mp h_lt
  let C' : Finset X := hC_fin.toFinset
  have hC'_eq : (C' : Set X) = C := hC_fin.coe_toFinset
  have h_each : ∀ c ∈ C', (S ∩ Metric.closedBall c (δ : ℝ)).Finite ∧
      (S ∩ Metric.closedBall c (δ : ℝ)).encard ≤ (K_pack : ENat) := by
    intro c hc
    let T := S ∩ Metric.closedBall c (δ : ℝ)
    have hT_subS : T ⊆ S := Set.inter_subset_left
    have hT_sep : Set.Pairwise T (fun x y => (δ : ℝ) ≤ dist x y) := hS_sep.mono hT_subS
    have hT_sub : T ⊆ Metric.closedBall c (2 * (δ : ℝ)) := by
      intro x hx
      have h1 : dist x c ≤ (δ : ℝ) := hx.2
      have h2 : dist x c ≤ 2 * (δ : ℝ) := by linarith
      exact h2
    exact h_pack c T hT_sep hT_sub
  let G : X → Finset X := fun c =>
    if h : c ∈ C' then (h_each c h).1.toFinset else ∅
  have hG_eq : ∀ (c : X) (hc : c ∈ C'), G c = (h_each c hc).1.toFinset := by
    intro c hc
    dsimp only [G]
    rw [dif_pos hc]
  have h_cover : S ⊆ ⋃ c ∈ (C' : Set X), S ∩ Metric.closedBall c (δ : ℝ) := by
    intro x hx
    have h10 : ∃ (c : X), c ∈ C ∧ edist x c ≤ ↑δ := hCcover hx
    rcases h10 with ⟨c, hc, hed⟩
    have hc' : c ∈ (C' : Set X) := by
      rw [hC'_eq] <;> exact hc
    have h11 : dist x c ≤ (δ : ℝ) := by
      simpa [edist_dist] using hed
    have h12 : x ∈ S ∩ Metric.closedBall c (δ : ℝ) := ⟨hx, h11⟩
    exact Set.mem_biUnion hc' h12
  let F : Finset X := C'.biUnion G
  have hF_sub : (S : Set X) ⊆ (F : Set X) := by
    intro x hx
    have h10 : ∃ (c : X), c ∈ C ∧ edist x c ≤ ↑δ := hCcover hx
    rcases h10 with ⟨c, hc, hed⟩
    have hc' : c ∈ (C' : Set X) := by
      rw [hC'_eq] <;> exact hc
    have h11 : dist x c ≤ (δ : ℝ) := by
      simpa [edist_dist] using hed
    have h12 : x ∈ S ∩ Metric.closedBall c (δ : ℝ) := ⟨hx, h11⟩
    have h13 : x ∈ (h_each c hc').1.toFinset := by simpa using h12
    have h14 : x ∈ G c := by rw [hG_eq c hc']; exact h13
    exact Finset.mem_biUnion.mpr ⟨c, hc', h14⟩
  have hS_fin : S.Finite := Set.Finite.subset (Finset.finite_toSet F) hF_sub
  let S' : Finset X := hS_fin.toFinset
  have hS'_eq : (S' : Set X) = S := hS_fin.coe_toFinset
  have hF_sub' : S' ⊆ F := by
    intro x hx
    have h_xinS : x ∈ S := by
      rw [←hS'_eq] <;> exact hx
    exact hF_sub h_xinS
  have h_card_F : F.card ≤ ∑ c ∈ C', (G c).card := by
    exact Finset.card_biUnion_le
  have h_main : S'.card ≤ K_pack * C'.card := by
    calc S'.card
      ≤ F.card := Finset.card_le_card hF_sub'
    _ ≤ ∑ c ∈ C', (G c).card := h_card_F
    _ ≤ ∑ c ∈ C', K_pack := by
      apply Finset.sum_le_sum
      intro c hc
      rw [hG_eq c hc]
      have h5 : (S ∩ Metric.closedBall c (δ : ℝ)).encard ≤ (K_pack : ENat) := (h_each c hc).2
      have h6 : ((h_each c hc).1.toFinset).card ≤ K_pack := by
        have h_fin : (S ∩ Metric.closedBall c (δ : ℝ)).Finite := (h_each c hc).1
        have h7 : (S ∩ Metric.closedBall c (δ : ℝ)).encard = ↑(h_fin.toFinset).card := by
          exact Set.Finite.encard_eq_coe_toFinset_card h_fin
        rw [h7] at h5
        exact_mod_cast h5
      exact h6
    _ = K_pack * C'.card := by
      simp [Finset.sum_const] <;> ring
  have h1 : (S.encard : ENNReal) = (S'.card : ENNReal) := by
    rw [←hS'_eq] <;> simp
  have h2 : (C'.card : ENNReal) = (Metric.externalCoveringNumber δ S : ENNReal) := by
    have h3 : (C'.card : ENat) = C.encard := by simp [←hC'_eq]
    have h4 : C.encard = Metric.externalCoveringNumber δ S := hC_eq
    have h5 : (C'.card : ENat) = Metric.externalCoveringNumber δ S := by
      rw [h3, h4]
    exact_mod_cast h5
  calc (S.encard : ENNReal)
    = (S'.card : ENNReal) := h1
  _ ≤ (K_pack : ENNReal) * (C'.card : ENNReal) := by exact_mod_cast h_main
  _ = (K_pack : ENNReal) * (Metric.externalCoveringNumber δ S : ENNReal) := by rw [h2]

/-- Packing-covering inequality using a LOCAL cardinality bound.
    If every δ-ball contains at most K_local elements of S,
    then |S| ≤ K_local * covering_δ(S).
    This does NOT require S to be separated. -/
lemma local_pack_card_le_covering
    {X : Type*} [PseudoMetricSpace X] {δ : NNReal} {S : Set X}
    (K_local : ℕ)
    (h_local : ∀ (z : X), (S ∩ Metric.closedBall z (δ : ℝ)).Finite ∧
        (S ∩ Metric.closedBall z (δ : ℝ)).encard ≤ (K_local : ENat))
    (hcov : (Metric.externalCoveringNumber δ S : ENNReal) < ⊤) :
    (S.encard : ENNReal) ≤ (K_local : ENNReal) * (Metric.externalCoveringNumber δ S : ENNReal) := by
  classical
  have hcov' : Metric.externalCoveringNumber δ S < ⊤ := by exact_mod_cast hcov
  rcases DiscretisedFurstenbergEstimate.CoveringUtils.exists_external_cover_eq hcov' with ⟨C, hCcover, hC_eq⟩
  have hC_fin : C.Finite := by
    have h_lt : C.encard < ⊤ := by
      rw [hC_eq]; exact hcov'
    exact Set.encard_lt_top_iff.mp h_lt
  let C' : Finset X := hC_fin.toFinset
  have hC'_eq : (C' : Set X) = C := hC_fin.coe_toFinset
  have h_each : ∀ c ∈ C', (S ∩ Metric.closedBall c (δ : ℝ)).Finite ∧
      (S ∩ Metric.closedBall c (δ : ℝ)).encard ≤ (K_local : ENat) := by
    intro c hc
    exact h_local c
  let G : X → Finset X := fun c =>
    if h : c ∈ C' then (h_each c h).1.toFinset else ∅
  have hG_eq : ∀ (c : X) (hc : c ∈ C'), G c = (h_each c hc).1.toFinset := by
    intro c hc
    dsimp only [G]
    rw [dif_pos hc]
  have h_cover : S ⊆ ⋃ c ∈ (C' : Set X), S ∩ Metric.closedBall c (δ : ℝ) := by
    intro x hx
    have h10 : ∃ (c : X), c ∈ C ∧ edist x c ≤ ↑δ := hCcover hx
    rcases h10 with ⟨c, hc, hed⟩
    have hc' : c ∈ (C' : Set X) := by
      rw [hC'_eq] <;> exact hc
    have h11 : dist x c ≤ (δ : ℝ) := by
      simpa [edist_dist] using hed
    have h12 : x ∈ S ∩ Metric.closedBall c (δ : ℝ) := ⟨hx, h11⟩
    exact Set.mem_biUnion hc' h12
  let F : Finset X := C'.biUnion G
  have hF_sub : (S : Set X) ⊆ (F : Set X) := by
    intro x hx
    have h10 : ∃ (c : X), c ∈ C ∧ edist x c ≤ ↑δ := hCcover hx
    rcases h10 with ⟨c, hc, hed⟩
    have hc' : c ∈ (C' : Set X) := by
      rw [hC'_eq] <;> exact hc
    have h11 : dist x c ≤ (δ : ℝ) := by
      simpa [edist_dist] using hed
    have h12 : x ∈ S ∩ Metric.closedBall c (δ : ℝ) := ⟨hx, h11⟩
    have h13 : x ∈ (h_each c hc').1.toFinset := by simpa using h12
    have h14 : x ∈ G c := by rw [hG_eq c hc']; exact h13
    exact Finset.mem_biUnion.mpr ⟨c, hc', h14⟩
  have hS_fin : S.Finite := Set.Finite.subset (Finset.finite_toSet F) hF_sub
  let S' : Finset X := hS_fin.toFinset
  have hS'_eq : (S' : Set X) = S := hS_fin.coe_toFinset
  have hF_sub' : S' ⊆ F := by
    intro x hx
    have h_xinS : x ∈ S := by
      rw [←hS'_eq] <;> exact hx
    exact hF_sub h_xinS
  have h_card_F : F.card ≤ ∑ c ∈ C', (G c).card := by
    exact Finset.card_biUnion_le
  have h_main : S'.card ≤ K_local * C'.card := by
    calc S'.card
      ≤ F.card := Finset.card_le_card hF_sub'
    _ ≤ ∑ c ∈ C', (G c).card := h_card_F
    _ ≤ ∑ c ∈ C', K_local := by
      apply Finset.sum_le_sum
      intro c hc
      rw [hG_eq c hc]
      have h5 : (S ∩ Metric.closedBall c (δ : ℝ)).encard ≤ (K_local : ENat) := (h_each c hc).2
      have h6 : ((h_each c hc).1.toFinset).card ≤ K_local := by
        have h_fin : (S ∩ Metric.closedBall c (δ : ℝ)).Finite := (h_each c hc).1
        have h7 : (S ∩ Metric.closedBall c (δ : ℝ)).encard = ↑(h_fin.toFinset).card := by exact Set.Finite.encard_eq_coe_toFinset_card h_fin
        rw [h7] at h5
        exact_mod_cast h5
      exact h6
    _ = K_local * C'.card := by
      simp [Finset.sum_const] <;> ring
  have h1 : (S.encard : ENNReal) = (S'.card : ENNReal) := by
    rw [←hS'_eq] <;> simp
  have h2 : (C'.card : ENNReal) = (Metric.externalCoveringNumber δ S : ENNReal) := by
    have h3 : (C'.card : ENat) = C.encard := by simp [←hC'_eq]
    have h4 : C.encard = Metric.externalCoveringNumber δ S := hC_eq
    have h5 : (C'.card : ENat) = Metric.externalCoveringNumber δ S := by
      rw [h3, h4]
    exact_mod_cast h5
  calc (S.encard : ENNReal)
    = (S'.card : ENNReal) := h1
  _ ≤ (K_local : ENNReal) * (C'.card : ENNReal) := by exact_mod_cast h_main
  _ = (K_local : ENNReal) * (Metric.externalCoveringNumber δ S : ENNReal) := by rw [h2]

/-! ### Common tubes bound -/

/-- Uniqueness of affine line through two distinct points. -/
lemma affineLine_unique_of_two_points {q q' : EuclideanPlane} (hne : q ≠ q')
    {ℓ₁ ℓ₂ : AffineLine} (hq1 : q ∈ ℓ₁.1) (hq'1 : q' ∈ ℓ₁.1)
    (hq2 : q ∈ ℓ₂.1) (hq'2 : q' ∈ ℓ₂.1) : ℓ₁ = ℓ₂ := by
  have h_vsub1 : q' - q ∈ ℓ₁.1.direction := AffineSubspace.vsub_mem_direction hq'1 hq1
  have h_vsub2 : q' - q ∈ ℓ₂.1.direction := AffineSubspace.vsub_mem_direction hq'2 hq2
  have h_ne_zero : q' - q ≠ 0 := by
    intro h
    have : q' = q := by simpa [sub_eq_zero] using h
    exact hne this.symm
  have h_span_le1 : ℝ ∙ (q' - q) ≤ ℓ₁.1.direction := by
    apply Submodule.span_le.mpr
    intro y hy
    have h_y_eq : y = q' - q := by simpa using hy
    rw [h_y_eq]
    exact h_vsub1
  have h_span_rank : Module.finrank ℝ (ℝ ∙ (q' - q)) = 1 :=
    finrank_span_singleton h_ne_zero
  have h_dir1 : ℝ ∙ (q' - q) = ℓ₁.1.direction :=
    Submodule.eq_of_le_of_finrank_eq h_span_le1 (by rw [h_span_rank, ℓ₁.2])
  have h_span_le2 : ℝ ∙ (q' - q) ≤ ℓ₂.1.direction := by
    apply Submodule.span_le.mpr
    intro y hy
    have h_y_eq : y = q' - q := by simpa using hy
    rw [h_y_eq]
    exact h_vsub2
  have h_dir2 : ℝ ∙ (q' - q) = ℓ₂.1.direction :=
    Submodule.eq_of_le_of_finrank_eq h_span_le2 (by rw [h_span_rank, ℓ₂.2])
  have hdir_eq : ℓ₁.1.direction = ℓ₂.1.direction := by
    rw [←h_dir1, h_dir2]
  apply Subtype.ext
  rw [AffineSubspace.eq_iff_direction_eq_of_mem hq1 hq2]
  exact hdir_eq

lemma common_tubes_bound_proof
    (Δ s C_s C_common : ℝ)
    (hΔ_pos : 0 < Δ) (hs_pos : 0 < s) (hC_s_pos : 0 < C_s)
    (hC_common_pos : 0 < C_common)
    (q q' : EuclideanPlane) (hr_pos : 0 < dist q q')
    (hq_bound : ‖q‖ ≤ 2) (hq'_bound : ‖q'‖ ≤ 2)
    (T_q T_q' : Set AffineLine)
    (hTq_separated : Set.Pairwise T_q (fun ℓ₁ ℓ₂ => Δ ≤ dist ℓ₁ ℓ₂))
    (hTq_deltaSet : IsDeltaSSet Δ s C_s T_q)
    (hTq_near : ∀ ℓ ∈ T_q, q ∈ Metric.cthickening (2 * Δ) ℓ.1)
    (hTq'_near : ∀ ℓ ∈ T_q', q' ∈ Metric.cthickening (2 * Δ) ℓ.1)
    (hTq_size : ENat.toENNReal T_q.encard ≤ ENNReal.ofReal (C_s * Δ ^ (-s)))
    (h_geom : ∀ (Δ' : ℝ), 0 < Δ' → ∀ (q q' : EuclideanPlane),
      ‖q‖ ≤ 2 → ‖q'‖ ≤ 2 → 0 < dist q q' →
      ∀ (ℓ : AffineLine),
        q ∈ Metric.cthickening (2 * Δ') ℓ.1 →
        q' ∈ Metric.cthickening (2 * Δ') ℓ.1 →
        ∃ (ℓ₀ : AffineLine), q ∈ ℓ₀.1 ∧ q' ∈ ℓ₀.1 ∧
          dist ℓ ℓ₀ ≤ 200 * (Δ' + Δ' / dist q q'))
    (h_const : C_s^2 * (1600 : ℝ)^s * (affineLine_packing_constant : ℝ) ≤ C_common) :
    ENat.toENNReal (T_q ∩ T_q').encard ≤
      ENNReal.ofReal (C_common * (dist q q') ^ (-s)) := by
  set r : ℝ := dist q q' with hr_def
  have hne : q ≠ q' := by
    intro h
    have h0 : r = 0 := by
      rw [hr_def, h, dist_self]
    linarith [hr_pos]
  have hr_le4 : r ≤ 4 := by
    calc r = dist q q' := rfl
      _ ≤ ‖q‖ + ‖q'‖ := dist_le_norm_add_norm q q'
      _ ≤ 2 + 2 := by linarith
      _ = 4 := by norm_num
  let S : Set AffineLine := T_q ∩ T_q'
  by_cases h_empty : S = ∅
  · have h : (T_q ∩ T_q') = ∅ := by simpa [S] using h_empty
    rw [h]
    simp
    <;> exact zero_le _
  · have h_nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty
    rcases h_nonempty with ⟨ℓstar, hℓstar⟩
    rcases h_geom Δ hΔ_pos q q' hq_bound hq'_bound hr_pos ℓstar
        (hTq_near ℓstar hℓstar.1) (hTq'_near ℓstar hℓstar.2)
      with ⟨ℓ₀, hq_in, hq'_in, _⟩
    have h_contain_all : S ⊆ Metric.closedBall ℓ₀ (200 * (Δ + Δ / r)) := by
      intro ℓ hℓ
      rcases h_geom Δ hΔ_pos q q' hq_bound hq'_bound hr_pos ℓ
          (hTq_near ℓ hℓ.1) (hTq'_near ℓ hℓ.2)
        with ⟨ℓ₁, hq1, hq'1, hdist⟩
      have h_eq : ℓ₁ = ℓ₀ := affineLine_unique_of_two_points hne hq1 hq'1 hq_in hq'_in
      rw [h_eq] at hdist
      exact hdist
    let ρ : ℝ := 200 * (Δ + Δ / r)
    have hρ_ge_D : Δ ≤ ρ := by
      dsimp only [ρ]
      have h1 : 0 ≤ Δ / r := by positivity
      linarith
    have hS_sub_Tq : S ⊆ T_q := Set.inter_subset_left
    have hS_sep : Set.Pairwise S (fun x y => Δ ≤ dist x y) := hTq_separated.mono hS_sub_Tq
    have h_delta_cover : (Metric.externalCoveringNumber Δ.toNNReal S : ENNReal) ≤
        ENNReal.ofReal C_s * (ENNReal.ofReal ρ) ^ s *
          (Metric.externalCoveringNumber Δ.toNNReal T_q : ENNReal) := by
      have h1 : S ⊆ (T_q : Set AffineLine) ∩ Metric.closedBall ℓ₀ ρ := by
        intro x hx; exact ⟨hS_sub_Tq hx, h_contain_all hx⟩
      have h2 : Metric.externalCoveringNumber Δ.toNNReal S ≤ Metric.externalCoveringNumber Δ.toNNReal ((T_q : Set AffineLine) ∩ Metric.closedBall ℓ₀ ρ) :=
        Metric.externalCoveringNumber_mono_set h1
      have h2' : (Metric.externalCoveringNumber Δ.toNNReal S : ENNReal) ≤ (Metric.externalCoveringNumber Δ.toNNReal ((T_q : Set AffineLine) ∩ Metric.closedBall ℓ₀ ρ) : ENNReal) := by
        exact_mod_cast h2
      have h3 := hTq_deltaSet.2.2.2.2 ℓ₀ ρ hρ_ge_D
      exact le_trans h2' h3
    have h_cov_Tq : (Metric.externalCoveringNumber Δ.toNNReal T_q : ENNReal) ≤
        ENNReal.ofReal (C_s * Δ ^ (-s)) := by
      have h1 : Metric.externalCoveringNumber Δ.toNNReal T_q ≤ (T_q : Set AffineLine).encard := by
        have hcover : Metric.IsCover Δ.toNNReal (T_q : Set AffineLine) (T_q : Set AffineLine) := by
          intro y hy
          have h_edist : edist y y ≤ ↑Δ.toNNReal := by
            rw [edist_dist, dist_self] <;> simp [hΔ_pos.le] <;> exact zero_le _
          exact ⟨y, hy, h_edist⟩
        exact hcover.externalCoveringNumber_le_encard
      have h1' : (Metric.externalCoveringNumber Δ.toNNReal T_q : ENNReal) ≤ ENat.toENNReal (T_q : Set AffineLine).encard := by
        exact_mod_cast h1
      exact le_trans h1' hTq_size
    have h_cover_bound : (Metric.externalCoveringNumber Δ.toNNReal S : ENNReal) ≤
        ENNReal.ofReal (C_s^2 * ρ ^ s * Δ ^ (-s)) := by
      calc (Metric.externalCoveringNumber Δ.toNNReal S : ENNReal)
        ≤ ENNReal.ofReal C_s * (ENNReal.ofReal ρ) ^ s *
            (Metric.externalCoveringNumber Δ.toNNReal T_q : ENNReal) := h_delta_cover
      _ ≤ ENNReal.ofReal C_s * (ENNReal.ofReal ρ) ^ s *
            ENNReal.ofReal (C_s * Δ ^ (-s)) := by gcongr
      _ = ENNReal.ofReal (C_s^2 * ρ ^ s * Δ ^ (-s)) := by
        have h_pos1 : 0 ≤ C_s := by linarith
        have h_pos2 : 0 ≤ ρ := by positivity
        have h_pos3 : 0 ≤ Δ ^ (-s) := by positivity
        have h_pos4 : 0 ≤ C_s * Δ ^ (-s) := by positivity
        have h_eq1 : ENNReal.ofReal (C_s * Δ ^ (-s)) = ENNReal.ofReal C_s * ENNReal.ofReal (Δ ^ (-s)) := by
          rw [ENNReal.ofReal_mul h_pos1]
        have h_eq2 : (ENNReal.ofReal ρ) ^ s = ENNReal.ofReal (ρ ^ s) := by
          rw [ENNReal.ofReal_rpow_of_nonneg h_pos2 (by linarith)]
        rw [h_eq2, h_eq1]
        have h_eq3 : ENNReal.ofReal C_s * ENNReal.ofReal (ρ ^ s) * (ENNReal.ofReal C_s * ENNReal.ofReal (Δ ^ (-s))) =
            ENNReal.ofReal (C_s ^ 2 * ρ ^ s * Δ ^ (-s)) := by
          have h_assoc : ENNReal.ofReal C_s * ENNReal.ofReal (ρ ^ s) * (ENNReal.ofReal C_s * ENNReal.ofReal (Δ ^ (-s))) =
              ENNReal.ofReal C_s * ENNReal.ofReal C_s * ENNReal.ofReal (ρ ^ s) * ENNReal.ofReal (Δ ^ (-s)) := by ring
          rw [h_assoc]
          have h1 : ENNReal.ofReal C_s * ENNReal.ofReal C_s = ENNReal.ofReal (C_s ^ 2) := by
            rw [←ENNReal.ofReal_mul h_pos1] <;> ring_nf
          rw [h1]
          have h2 : ENNReal.ofReal (C_s ^ 2) * ENNReal.ofReal (ρ ^ s) * ENNReal.ofReal (Δ ^ (-s)) =
              ENNReal.ofReal (C_s ^ 2 * ρ ^ s * Δ ^ (-s)) := by
            have h21 : ENNReal.ofReal (C_s ^ 2) * ENNReal.ofReal (ρ ^ s) = ENNReal.ofReal (C_s ^ 2 * ρ ^ s) := by
              rw [←ENNReal.ofReal_mul (show 0 ≤ C_s ^ 2 by positivity)]
            rw [h21]
            have h22 : ENNReal.ofReal (C_s ^ 2 * ρ ^ s) * ENNReal.ofReal (Δ ^ (-s)) = ENNReal.ofReal ((C_s ^ 2 * ρ ^ s) * Δ ^ (-s)) := by
              rw [←ENNReal.ofReal_mul (show 0 ≤ C_s ^ 2 * ρ ^ s by positivity)]
            rw [h22] <;> ring
          exact h2
        exact h_eq3
    have h_rho_bound : ρ ^ s * Δ ^ (-s) ≤ (1600 : ℝ)^s * r ^ (-s) := by
      have h_rho_eq : ρ = 200 * Δ * (1 + 1 / r) := by
        dsimp only [ρ]; field_simp [hr_pos.ne'] <;> ring
      rw [h_rho_eq]
      have h_pos_all : 0 < 200 * Δ * (1 + 1 / r) := by positivity
      have h200_pos : 0 ≤ (200 : ℝ) := by norm_num
      have hD_pos : 0 ≤ Δ := by linarith
      have h1pos : 0 ≤ 1 + 1 / r := by positivity
      have h_eq1 : (200 * Δ * (1 + 1 / r)) ^ s = (200 : ℝ)^s * (Δ * (1 + 1 / r)) ^ s := by
        have h_assoc : 200 * Δ * (1 + 1 / r) = 200 * (Δ * (1 + 1 / r)) := by ring
        rw [h_assoc]
        rw [Real.mul_rpow h200_pos (by positivity)]
      have h_eq2 : (Δ * (1 + 1 / r)) ^ s = Δ^s * (1 + 1 / r)^s := by
        rw [Real.mul_rpow hD_pos h1pos]
      have h_eq3 : Δ^s * Δ^(-s) = 1 := by
        have hD_pos' : 0 < Δ := hΔ_pos
        have h : Δ ^ (s + (-s)) = Δ^s * Δ^(-s) := Real.rpow_add hD_pos' s (-s)
        have h0 : s + (-s) = 0 := by ring
        rw [h0] at h
        have h1 : Δ ^ (0 : ℝ) = 1 := Real.rpow_zero Δ
        rw [h1] at h
        exact h.symm
      have h1 : (200 * Δ * (1 + 1 / r)) ^ s * Δ ^ (-s) = (200 : ℝ)^s * (1 + 1 / r)^s := by
        rw [h_eq1, h_eq2]
        <;> rw [show (200 : ℝ)^s * (Δ^s * (1 + 1 / r)^s) * Δ^(-s) = (200 : ℝ)^s * ((1 + 1 / r)^s) * (Δ^s * Δ^(-s)) by ring]
        <;> rw [h_eq3] <;> ring
      rw [h1]
      have h_s_neg : -s < 0 := by linarith
      have h_strict : StrictAntiOn (fun x : ℝ => x ^ (-s)) (Set.Ioi 0) :=
        Real.strictAntiOn_rpow_Ioi_of_exponent_neg h_s_neg
      have h2 : (1 + 1 / r)^s ≤ (8 : ℝ)^s * r^(-s) := by
        by_cases h_rle1 : r ≤ 1
        · have h3 : 1 + 1 / r ≤ 2 / r := by
            have h4 : 0 < r := hr_pos
            field_simp [h4.ne'] <;> linarith
          have h5 : (1 + 1 / r)^s ≤ (2 / r)^s := by gcongr <;> linarith
          have h6 : (2 / r)^s = (2 : ℝ)^s * r^(-s) := by
            have h7 : (2 / r)^s = (2 : ℝ)^s / r^s := Real.div_rpow (by norm_num) (by linarith) s
            rw [h7]
            have h8 : r^s * r^(-s) = 1 := by
              have h9 : r ^ (s + (-s)) = r^s * r^(-s) := Real.rpow_add hr_pos s (-s)
              have h10 : s + (-s) = 0 := by ring
              rw [h10] at h9
              have h11 : r ^ (0 : ℝ) = 1 := Real.rpow_zero r
              rw [h11] at h9
              exact h9.symm
            have h_div : (2 : ℝ)^s / r^s = (2 : ℝ)^s * r^(-s) := by
              have h_inv : (r^s)⁻¹ = r^(-s) := by
                have h_rpow_neg : r^(-s) = (r^s)⁻¹ := by
                  rw [Real.rpow_neg (by linarith)]
                  <;> ring
                exact h_rpow_neg.symm
              rw [div_eq_mul_inv, h_inv] <;> ring
            exact h_div
          rw [h6] at h5
          have h7 : (2 : ℝ)^s ≤ (8 : ℝ)^s := by
            gcongr <;> norm_num <;> linarith
          have h8 : (2 : ℝ)^s * r^(-s) ≤ (8 : ℝ)^s * r^(-s) := by
            gcongr
          exact le_trans h5 h8
        · have h_r_gt1 : 1 < r := by linarith
          have h3 : 1 + 1 / r ≤ 2 := by
            have h4 : 0 < r := hr_pos
            have h5 : 1 / r < 1 := by
              apply (div_lt_one h4).mpr
              exact h_r_gt1
            linarith
          have h4 : (1 + 1 / r)^s ≤ (2 : ℝ)^s := by gcongr <;> linarith
          have h14 : (4 : ℝ)^(-s) ≤ r^(-s) := by
            by_cases h : r < 4
            · have h4_pos : (4 : ℝ) ∈ Set.Ioi (0 : ℝ) := by simp [Set.mem_Ioi] <;> norm_num
              exact (h_strict hr_pos h4_pos h).le
            · have h' : r = 4 := by linarith
              rw [h']
          have h10 : (8 : ℝ)^s * (4 : ℝ)^(-s) = (2 : ℝ)^s := by
            have h11 : (8 : ℝ)^s = (2 : ℝ)^s * (4 : ℝ)^s := by
              have h12 : (8 : ℝ) = 2 * 4 := by norm_num
              rw [h12]
              rw [Real.mul_rpow (by norm_num) (by norm_num)]
              <;> ring
            rw [h11]
            have h13 : (4 : ℝ)^s * (4 : ℝ)^(-s) = 1 := by
              have h14 : (4 : ℝ) ^ (s + (-s)) = (4 : ℝ)^s * (4 : ℝ)^(-s) := Real.rpow_add (by norm_num) s (-s)
              have h15 : s + (-s) = 0 := by ring
              rw [h15] at h14
              have h16 : (4 : ℝ) ^ (0 : ℝ) = 1 := Real.rpow_zero (4 : ℝ)
              rw [h16] at h14
              exact h14.symm
            have h_goal : (2 : ℝ)^s * (4 : ℝ)^s * (4 : ℝ)^(-s) = (2 : ℝ)^s := by
              have h_assoc : (2 : ℝ)^s * (4 : ℝ)^s * (4 : ℝ)^(-s) = (2 : ℝ)^s * ((4 : ℝ)^s * (4 : ℝ)^(-s)) := by ring
              rw [h_assoc, h13] <;> ring
            exact h_goal
          have h9 : (2 : ℝ)^s ≤ (8 : ℝ)^s * r^(-s) := by
            calc (2 : ℝ)^s
              = (8 : ℝ)^s * (4 : ℝ)^(-s) := h10.symm
            _ ≤ (8 : ℝ)^s * r^(-s) := by gcongr
          exact le_trans h4 h9
      have h3 : (200 : ℝ)^s * (1 + 1 / r)^s ≤ (200 : ℝ)^s * ((8 : ℝ)^s * r^(-s)) := by gcongr
      have h4 : (200 : ℝ)^s * (8 : ℝ)^s = (1600 : ℝ)^s := by
        have h5 : (1600 : ℝ) = 200 * 8 := by norm_num
        rw [h5]
        rw [Real.mul_rpow (by norm_num) (by norm_num)] <;> ring
      calc (200 : ℝ)^s * (1 + 1 / r)^s
        ≤ (200 : ℝ)^s * ((8 : ℝ)^s * r^(-s)) := h3
      _ = (200 : ℝ)^s * (8 : ℝ)^s * r^(-s) := by ring
      _ = (1600 : ℝ)^s * r^(-s) := by rw [h4] <;> ring
    have h_cover_final : (Metric.externalCoveringNumber Δ.toNNReal S : ENNReal) ≤
        ENNReal.ofReal (C_s^2 * (1600 : ℝ)^s * r^(-s)) := by
      calc (Metric.externalCoveringNumber Δ.toNNReal S : ENNReal)
        ≤ ENNReal.ofReal (C_s^2 * ρ ^ s * Δ ^ (-s)) := h_cover_bound
      _ ≤ ENNReal.ofReal (C_s^2 * (1600 : ℝ)^s * r^(-s)) := by
        apply ENNReal.ofReal_le_ofReal
        have hCs2_pos : 0 ≤ C_s^2 := by positivity
        calc C_s^2 * ρ ^ s * Δ ^ (-s)
          = C_s^2 * (ρ ^ s * Δ ^ (-s)) := by ring
        _ ≤ C_s^2 * ((1600 : ℝ)^s * r^(-s)) := by gcongr
        _ = C_s^2 * (1600 : ℝ)^s * r^(-s) := by ring
    let δnn : NNReal := Δ.toNNReal
    have hδnn_eq : (δnn : ℝ) = Δ := by simp [δnn, hΔ_pos.le] <;> linarith
    have h_pack' : ∀ (z : AffineLine) (T : Set AffineLine),
        Set.Pairwise T (fun x y => (δnn : ℝ) ≤ dist x y) →
        T ⊆ Metric.closedBall z (2 * (δnn : ℝ)) →
        T.Finite ∧ T.encard ≤ (affineLine_packing_constant : ENat) := by
      intro z T hT_sep hT_sub
      have hT_sep' : Set.Pairwise T (fun x y => Δ ≤ dist x y) := by simpa [hδnn_eq] using hT_sep
      have hT_sub' : T ⊆ Metric.closedBall z (2 * Δ) := by simpa [hδnn_eq] using hT_sub
      exact affineLine_packing_bound Δ hΔ_pos hT_sep' z hT_sub'
    have hcov_fin : (Metric.externalCoveringNumber δnn S : ENNReal) < ⊤ := by
      calc (Metric.externalCoveringNumber δnn S : ENNReal)
        ≤ ENNReal.ofReal (C_s^2 * (1600 : ℝ)^s * r^(-s)) := h_cover_final
      _ < ⊤ := ENNReal.ofReal_lt_top
    have hS_sep' : Set.Pairwise S (fun x y : AffineLine => (δnn : ℝ) ≤ dist x y) := by
      simpa [hδnn_eq] using hS_sep
    have h_card : (S.encard : ENNReal) ≤
        (affineLine_packing_constant : ENNReal) * (Metric.externalCoveringNumber δnn S : ENNReal) :=
      separated_set_card_le_covering hS_sep' affineLine_packing_constant h_pack' hcov_fin
    have h_final : (S.encard : ENNReal) ≤
        ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C_s^2 * (1600 : ℝ)^s * r^(-s)) := by
      calc (S.encard : ENNReal)
        ≤ (affineLine_packing_constant : ENNReal) * (Metric.externalCoveringNumber δnn S : ENNReal) := h_card
      _ ≤ (affineLine_packing_constant : ENNReal) * ENNReal.ofReal (C_s^2 * (1600 : ℝ)^s * r^(-s)) := by gcongr
      _ = ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C_s^2 * (1600 : ℝ)^s * r^(-s)) := by
        have h1 : (affineLine_packing_constant : ENNReal) = ENNReal.ofReal (affineLine_packing_constant : ℝ) := by
          simp
        rw [h1]
        have h_pos1 : 0 ≤ (affineLine_packing_constant : ℝ) := by positivity
        have h_pos2 : 0 ≤ C_s^2 * (1600 : ℝ)^s * r^(-s) := by positivity
        rw [←ENNReal.ofReal_mul h_pos1]
        <;> congr 1 <;> ring
    have h_goal : (affineLine_packing_constant : ℝ) * C_s^2 * (1600 : ℝ)^s * r^(-s) ≤ C_common * r^(-s) := by
      have h_pos : 0 ≤ r^(-s) := by positivity
      nlinarith [h_const]
    have h_main : (S.encard : ENNReal) ≤ ENNReal.ofReal (C_common * r^(-s)) := by
      calc (S.encard : ENNReal)
        ≤ ENNReal.ofReal ((affineLine_packing_constant : ℝ) * C_s^2 * (1600 : ℝ)^s * r^(-s)) := h_final
      _ ≤ ENNReal.ofReal (C_common * r^(-s)) := by apply ENNReal.ofReal_le_ofReal; linarith
    simpa [S, hr_def] using h_main

end DirecretisedFurstenbergEstimate.MainAppendix
