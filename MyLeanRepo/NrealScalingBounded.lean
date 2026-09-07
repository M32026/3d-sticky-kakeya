module

/-
# Bounded scaling lemma for dyadic covering numbers

Uniform bound `Nreal δ (c • S) ≤ K_scale * Nreal δ S` for `0 < c ≤ L`,
where `K_scale` depends only on `L`.
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Metric Classical BigOperators

namespace WeakTwoEndsSumProduct

/-- An interval of length `c*δ` can be covered by at most `Nat.ceil c + 1`
    δ-dyadic intervals. -/
lemma cover_scaled_interval (δ c : ℝ) (hδ : 0 < δ) (hc : 0 < c) (a : ℝ) :
    ∃ (C : Finset ℤ), C.card ≤ Nat.ceil c + 1 ∧
      Set.Ico a (a + c * δ) ⊆ ⋃ k ∈ C, Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) := by
  let k0 : ℤ := Int.floor (a / δ)
  let n : ℕ := Nat.ceil c
  have h_c_le_n : c ≤ (n : ℝ) := Nat.le_ceil c
  have h_k0_le : (δ * (k0 : ℝ)) ≤ a := by
    have h : (k0 : ℝ) ≤ a / δ := Int.floor_le (a / δ)
    calc (δ * (k0 : ℝ)) ≤ δ * (a / δ) := by gcongr
      _ = a := by field_simp [hδ.ne'] <;> ring
  have h_a_lt : a < δ * ((k0 : ℝ) + 1) := by
    have h : a / δ < (k0 : ℝ) + 1 := Int.lt_floor_add_one (a / δ)
    calc a = δ * (a / δ) := by field_simp [hδ.ne'] <;> ring
      _ < δ * ((k0 : ℝ) + 1) := by gcongr
  have h_end : a + c * δ < δ * ((k0 : ℝ) + (n : ℝ) + 1) := by
    have h1 : a + c * δ < δ * ((k0 : ℝ) + 1) + c * δ := by linarith [h_a_lt]
    have h2 : δ * ((k0 : ℝ) + 1) + c * δ ≤ δ * ((k0 : ℝ) + 1) + (n : ℝ) * δ := by
      gcongr <;> linarith
    have h3 : δ * ((k0 : ℝ) + 1) + (n : ℝ) * δ = δ * ((k0 : ℝ) + (n : ℝ) + 1) := by ring
    linarith
  let k_end : ℤ := k0 + (n : ℤ)
  let C : Finset ℤ := Finset.Icc k0 k_end
  have hC_card : C.card = n + 1 := by
    simp [C, k_end, Finset.card_eq_zero] <;> omega
  have hC_le : C.card ≤ Nat.ceil c + 1 := by
    rw [hC_card] <;> simp [n] <;> omega
  have h_cover : Set.Ico a (a + c * δ) ⊆ ⋃ k ∈ C, Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) := by
    intro x hx
    let j : ℤ := Int.floor (x / δ)
    have h_j1 : (j : ℝ) ≤ x / δ := Int.floor_le (x / δ)
    have h_j2 : x / δ < (j : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
    have h44 : (k0 : ℝ) ≤ x / δ := by
      calc (k0 : ℝ) = (δ * (k0 : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
        _ ≤ x / δ := by gcongr; exact h_k0_le.trans hx.1
    have hj_ge : k0 ≤ j := by
      have h5 : (k0 : ℝ) ≤ x / δ ↔ k0 ≤ j := Iff.symm Int.le_floor
      exact h5.mp h44
    have hj_le : j ≤ k_end := by
      have h4 : x / δ < (k_end : ℝ) + 1 := by
        have h5 : x < a + c * δ := hx.2
        have h6 : x / δ < (a + c * δ) / δ := by gcongr
        have h7 : (a + c * δ) / δ < (k_end : ℝ) + 1 := by
          have h71 : (a + c * δ) / δ < (δ * ((k0 : ℝ) + (n : ℝ) + 1)) / δ := by gcongr
          have h72 : (δ * ((k0 : ℝ) + (n : ℝ) + 1)) / δ = (k0 : ℝ) + (n : ℝ) + 1 := by
            field_simp [hδ.ne'] <;> ring
          have h73 : (k_end : ℝ) = (k0 : ℝ) + (n : ℝ) := by
            simp [k_end] <;> norm_cast
          rw [h73]; rw [h72] at h71; exact h71
        linarith
      exact Int.floor_le_iff.mpr h4
    have hj_in : j ∈ C := Finset.mem_Icc.mpr ⟨hj_ge, hj_le⟩
    have h_x_in : x ∈ Set.Ico (δ * (j : ℝ)) (δ * ((j : ℝ) + 1)) := by
      constructor
      · calc δ * (j : ℝ) ≤ δ * (x / δ) := by gcongr
          _ = x := by field_simp [hδ.ne'] <;> ring
      · calc x = δ * (x / δ) := by field_simp [hδ.ne'] <;> ring
          _ < δ * ((j : ℝ) + 1) := by gcongr
    exact Set.mem_iUnion₂.mpr ⟨j, hj_in, h_x_in⟩
  exact ⟨C, hC_le, h_cover⟩

/-- Two δ-dyadic intervals sharing a point must have the same integer index. -/
lemma dyadic_interval_unique (δ : ℝ) (hδ : 0 < δ) (k1 k2 : ℤ)
    (h : (Set.Ico (δ * (k1 : ℝ)) (δ * ((k1 : ℝ) + 1)) ∩
          Set.Ico (δ * (k2 : ℝ)) (δ * ((k2 : ℝ) + 1))).Nonempty) :
    k1 = k2 := by
  rcases h with ⟨z, hz1, hz2⟩
  have h1 : (k1 : ℝ) ≤ z / δ := by
    calc (k1 : ℝ) = (δ * (k1 : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
      _ ≤ z / δ := by gcongr; exact hz1.1
  have h2 : z / δ < (k1 : ℝ) + 1 := by
    calc z / δ < (δ * ((k1 : ℝ) + 1)) / δ := by gcongr; exact hz1.2
      _ = (k1 : ℝ) + 1 := by field_simp [hδ.ne'] <;> ring
  have h3 : (k2 : ℝ) ≤ z / δ := by
    calc (k2 : ℝ) = (δ * (k2 : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
      _ ≤ z / δ := by gcongr; exact hz2.1
  have h4 : z / δ < (k2 : ℝ) + 1 := by
    calc z / δ < (δ * ((k2 : ℝ) + 1)) / δ := by gcongr; exact hz2.2
      _ = (k2 : ℝ) + 1 := by field_simp [hδ.ne'] <;> ring
  have h6 : k1 < k2 + 1 := by exact_mod_cast (show (k1 : ℝ) < (k2 : ℝ) + 1 from by linarith)
  have h7 : k2 < k1 + 1 := by exact_mod_cast (show (k2 : ℝ) < (k1 : ℝ) + 1 from by linarith)
  have h5 : k1 ≤ k2 := Int.le_of_lt_add_one h6
  have h8 : k2 ≤ k1 := Int.le_of_lt_add_one h7
  linarith

/-- Bijection between 1D dyadic cubes meeting a set and integer indices. -/
lemma cubesMeeting_equiv_idx (δ : ℝ) (hδ : 0 < δ) (S : Set ℝ) :
    (dyadicCubesMeeting δ (realLineCopy S)).encard =
    {k : ℤ | (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ S).Nonempty}.encard := by
  let f : ℤ → Set (EuclideanSpace ℝ (Fin 1)) := fun k => dyadicCube δ (fun _ => k)
  let idxA : Set ℤ := {k | (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ S).Nonempty}
  let mk1 (r : ℝ) : EuclideanSpace ℝ (Fin 1) :=
    (WithLp.equiv 2 (Fin 1 → ℝ)).symm fun (_ : Fin 1) => r
  have h_f_inj : Set.InjOn f idxA := by
    intro k1 _ k2 _ h
    let y : ℝ := δ * (k1 : ℝ)
    let x : EuclideanSpace ℝ (Fin 1) := mk1 y
    have hx1 : x ∈ f k1 := by
      simp [f, dyadicCube, x, mk1, WithLp.equiv_symm_apply] <;> constructor <;> linarith
    have hx2 : x ∈ f k2 := by rw [h] at hx1; exact hx1
    have h2 : y ∈ Set.Ico (δ * (k2 : ℝ)) (δ * ((k2 : ℝ) + 1)) := by
      simpa [f, dyadicCube, x, mk1, WithLp.equiv_symm_apply] using hx2 0
    have h_inter : (Set.Ico (δ * (k1 : ℝ)) (δ * ((k1 : ℝ) + 1)) ∩
        Set.Ico (δ * (k2 : ℝ)) (δ * ((k2 : ℝ) + 1))).Nonempty :=
      ⟨y, by constructor <;> linarith, h2⟩
    exact dyadic_interval_unique δ hδ k1 k2 h_inter
  have h_image : f '' idxA = dyadicCubesMeeting δ (realLineCopy S) := by
    ext Q
    simp only [Set.mem_image, Set.mem_setOf_eq, dyadicCubesMeeting, dyadicCubes]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hQ : (dyadicCube δ (fun _ => k) ∩ realLineCopy S).Nonempty := by
        rcases hk with ⟨y, hy1, hy2⟩
        let x : EuclideanSpace ℝ (Fin 1) := mk1 y
        have hx1 : x ∈ dyadicCube δ (fun _ => k) := by
          simp [dyadicCube, x, mk1, WithLp.equiv_symm_apply] <;> exact hy1
        have hx2 : x ∈ realLineCopy S := by
          simp [realLineCopy, x, mk1, WithLp.equiv_symm_apply] <;> exact hy2
        exact ⟨x, hx1, hx2⟩
      exact ⟨⟨fun _ => k, rfl⟩, hQ⟩
    · rintro ⟨⟨k, rfl⟩, hQ⟩
      have h_k_eq : (fun _ : Fin 1 => k 0) = k := by
        funext i; fin_cases i <;> rfl
      have hQ' : (Set.Ico (δ * (k 0 : ℝ)) (δ * ((k 0 : ℝ) + 1)) ∩ S).Nonempty := by
        rcases hQ with ⟨x, hx1, hx2⟩
        have h_coord : x 0 ∈ Set.Ico (δ * (k 0 : ℝ)) (δ * ((k 0 : ℝ) + 1)) := by
          simpa [dyadicCube] using hx1 0
        have h_S : x 0 ∈ S := by simpa [realLineCopy] using hx2
        exact ⟨x 0, h_coord, h_S⟩
      refine ⟨k 0, hQ', ?_⟩
      dsimp only [f]; rw [h_k_eq]
  calc (dyadicCubesMeeting δ (realLineCopy S)).encard
      = (f '' idxA).encard := by rw [h_image]
    _ = idxA.encard := h_f_inj.encard_image

/-- Uniform bounded scaling lemma for 1D dyadic covering numbers.
    `K_scale` depends only on `L`, not on `c` or `S`. -/
lemma Nreal_scaling_bounded {δ L : ℝ} (hδ : 0 < δ) (hL_pos : 0 < L) :
    ∃ (K_scale : ℕ), 0 < K_scale ∧
      ∀ (S : Set ℝ), Bornology.IsBounded S →
        ∀ (c : ℝ), 0 < c → c ≤ L →
          Nreal δ ((fun x : ℝ => c * x) '' S) ≤ (K_scale : ENNReal) * Nreal δ S := by
  let K_scale : ℕ := Nat.ceil (max 1 L) + 1
  have hK_pos : 0 < K_scale := by
    dsimp only [K_scale]; omega
  use K_scale, hK_pos
  intro S hS_bdd c hc_pos hc_le
  by_cases h_top : Nreal δ S = ⊤
  · rw [h_top]; simp
  let idxA : Set ℤ := {k | (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ S).Nonempty}
  let idxScaled : Set ℤ := {k | (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ ((fun x : ℝ => c * x) '' S)).Nonempty}
  have h_eq1 : (dyadicCubesMeeting δ (realLineCopy S)).encard = idxA.encard :=
    cubesMeeting_equiv_idx δ hδ S
  have h_eq2 : (dyadicCubesMeeting δ (realLineCopy ((fun x : ℝ => c * x) '' S))).encard = idxScaled.encard :=
    cubesMeeting_equiv_idx δ hδ ((fun x : ℝ => c * x) '' S)
  by_cases h_finite : idxA.Finite
  · let F : Finset ℤ := h_finite.toFinset
    have hF_mem : ∀ j, j ∈ F ↔ j ∈ idxA := by
      intro j; simp [F, Set.Finite.mem_toFinset]
    choose C_j hC_j_card hC_j_cover using fun j : ℤ =>
      cover_scaled_interval δ c hδ hc_pos (c * δ * (j : ℝ))
    let allC : Finset ℤ := Finset.biUnion F C_j
    have h_allC_card : allC.card ≤ K_scale * F.card := by
      calc allC.card ≤ ∑ j ∈ F, (C_j j).card := Finset.card_biUnion_le
        _ ≤ ∑ j ∈ F, K_scale := by
          gcongr with j hj
          have h1 : (C_j j).card ≤ Nat.ceil c + 1 := hC_j_card j
          have h2 : Nat.ceil c + 1 ≤ K_scale := by
            dsimp only [K_scale]
            have h3 : Nat.ceil c ≤ Nat.ceil (max 1 L) := by
              apply Nat.ceil_le_ceil; exact le_max_of_le_right hc_le
            omega
          exact h1.trans h2
        _ = K_scale * F.card := by simp [Finset.sum_const, mul_comm]
    have h_cover : idxScaled ⊆ (allC : Set ℤ) := by
      intro k hk
      rcases hk with ⟨z, hz_k, ⟨y, hy_S, rfl⟩⟩
      let j : ℤ := Int.floor (y / δ)
      have h_y_in : y ∈ Set.Ico (δ * (j : ℝ)) (δ * ((j : ℝ) + 1)) := by
        have h1 : (j : ℝ) ≤ y / δ := Int.floor_le (y / δ)
        have h2 : y / δ < (j : ℝ) + 1 := Int.lt_floor_add_one (y / δ)
        have h_y1 : δ * (j : ℝ) ≤ y := by
          have h : δ * (j : ℝ) ≤ δ * (y / δ) := by gcongr
          have h' : δ * (y / δ) = y := by field_simp [hδ.ne'] <;> ring
          rw [h'] at h; exact h
        have h_y2 : y < δ * ((j : ℝ) + 1) := by
          have h : δ * (y / δ) < δ * ((j : ℝ) + 1) := by gcongr
          have h' : δ * (y / δ) = y := by field_simp [hδ.ne'] <;> ring
          rw [h'] at h; exact h
        exact ⟨h_y1, h_y2⟩
      have hj_A : j ∈ idxA := ⟨y, h_y_in, hy_S⟩
      have hj_F : j ∈ F := (hF_mem j).mpr hj_A
      have h_cy_in : c * y ∈ Set.Ico (c * δ * (j : ℝ)) (c * δ * (j : ℝ) + c * δ) := by
        have h_y1 : c * δ * (j : ℝ) ≤ c * y := by
          have h : c * (δ * (j : ℝ)) ≤ c * y :=
            mul_le_mul_of_nonneg_left h_y_in.1 (by linarith)
          have h' : c * δ * (j : ℝ) = c * (δ * (j : ℝ)) := by ring
          rw [h']; exact h
        have h_y2 : c * y < c * δ * (j : ℝ) + c * δ := by
          have h : c * y < c * (δ * ((j : ℝ) + 1)) :=
            mul_lt_mul_of_pos_left h_y_in.2 hc_pos
          have h' : c * (δ * ((j : ℝ) + 1)) = c * δ * (j : ℝ) + c * δ := by ring
          rw [h'] at h; exact h
        exact ⟨h_y1, h_y2⟩
      have h_cover' : c * y ∈ ⋃ k' ∈ C_j j, Set.Ico (δ * (k' : ℝ)) (δ * ((k' : ℝ) + 1)) :=
        hC_j_cover j h_cy_in
      rcases Set.mem_iUnion₂.mp h_cover' with ⟨k', hk'_in, hcy_in'⟩
      have h_k'_eq_k : k' = k := by
        have h_inter : (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩
            Set.Ico (δ * (k' : ℝ)) (δ * ((k' : ℝ) + 1))).Nonempty :=
          ⟨c * y, hz_k, hcy_in'⟩
        exact (dyadic_interval_unique δ hδ k k' h_inter).symm
      rw [h_k'_eq_k] at hk'_in
      exact Finset.mem_biUnion.mpr ⟨j, hj_F, hk'_in⟩
    have h_encard_le : idxScaled.encard ≤ (allC.card : ENNReal) := by
      have h1 : idxScaled.encard ≤ (allC : Set ℤ).encard := Set.encard_mono h_cover
      have h2 : (allC : Set ℤ).encard = ↑allC.card := by simp
      have h3 : idxScaled.encard ≤ ↑allC.card := by
        rw [h2] at h1; exact h1
      exact_mod_cast h3
    have h_idxA_encard : idxA.encard = (F.card : ENNReal) := by
      have h4 : idxA = (F : Set ℤ) := by
        ext j; simp [F, Set.Finite.mem_toFinset]
      rw [h4]; simp
    have h5 : Nreal δ ((fun x : ℝ => c * x) '' S) = idxScaled.encard := by
      simpa [Nreal, dyadicCoveringNumber] using h_eq2
    have h6 : Nreal δ S = idxA.encard := by
      simpa [Nreal, dyadicCoveringNumber] using h_eq1
    rw [h5, h6, h_idxA_encard]
    calc idxScaled.encard ≤ (allC.card : ENNReal) := h_encard_le
      _ ≤ (K_scale : ENNReal) * (F.card : ENNReal) := by exact_mod_cast h_allC_card
  · -- idxA is infinite → Nreal δ S = ⊤, contradicting h_top
    have h_encard_top : idxA.encard = ⊤ := by
      rw [Set.encard_eq_top_iff]
      exact h_finite
    have hN_top : Nreal δ S = ⊤ := by
      have h7 : Nreal δ S = idxA.encard := by
        simpa [Nreal, dyadicCoveringNumber] using h_eq1
      rw [h7, h_encard_top] <;> simp
    exact False.elim (h_top hN_top)

/-- Uniform version: K_scale depends only on L, and the bound holds for all δ. -/
lemma Nreal_scaling_bounded_uniform {L : ℝ} (hL_pos : 0 < L) :
    ∃ (K_scale : ℕ), 0 < K_scale ∧
      ∀ (δ : ℝ), 0 < δ →
      ∀ (S : Set ℝ), Bornology.IsBounded S →
        ∀ (c : ℝ), 0 < c → c ≤ L →
          Nreal δ ((fun x : ℝ => c * x) '' S) ≤ (K_scale : ENNReal) * Nreal δ S := by
  let K_scale : ℕ := Nat.ceil (max 1 L) + 1
  have hK_pos : 0 < K_scale := by dsimp only [K_scale]; omega
  refine ⟨K_scale, hK_pos, ?_⟩
  intro δ hδ S hS_bdd c hc_pos hc_le
  have h := Nreal_scaling_bounded (hδ := hδ) (hL_pos := hL_pos)
  rcases h with ⟨K', hK'_pos, hK'⟩
  -- The proof of Nreal_scaling_bounded uses K' = Nat.ceil (max 1 L) + 1 = K_scale.
  -- We recover the bound for K_scale by noting K' is some natural that works,
  -- and K_scale ≥ K' because both are Nat.ceil (max 1 L) + 1.
  -- Since we can't prove equality from the existential, we instead
  -- re-run the core argument with the explicit K_scale.
  by_cases h_top : Nreal δ S = ⊤
  · rw [h_top]; simp
  let idxA : Set ℤ := {k | (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ S).Nonempty}
  let idxScaled : Set ℤ := {k | (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ ((fun x : ℝ => c * x) '' S)).Nonempty}
  have h_eq1 : (dyadicCubesMeeting δ (realLineCopy S)).encard = idxA.encard :=
    cubesMeeting_equiv_idx δ hδ S
  have h_eq2 : (dyadicCubesMeeting δ (realLineCopy ((fun x : ℝ => c * x) '' S))).encard = idxScaled.encard :=
    cubesMeeting_equiv_idx δ hδ ((fun x : ℝ => c * x) '' S)
  by_cases h_finite : idxA.Finite
  · let F : Finset ℤ := h_finite.toFinset
    have hF_mem : ∀ j, j ∈ F ↔ j ∈ idxA := by
      intro j; simp [F, Set.Finite.mem_toFinset]
    choose C_j hC_j_card hC_j_cover using fun j : ℤ =>
      cover_scaled_interval δ c hδ hc_pos (c * δ * (j : ℝ))
    let allC : Finset ℤ := Finset.biUnion F C_j
    have h_allC_card : allC.card ≤ K_scale * F.card := by
      calc allC.card ≤ ∑ j ∈ F, (C_j j).card := Finset.card_biUnion_le
        _ ≤ ∑ j ∈ F, K_scale := by
          gcongr with j hj
          have h1 : (C_j j).card ≤ Nat.ceil c + 1 := hC_j_card j
          have h2 : Nat.ceil c + 1 ≤ K_scale := by
            dsimp only [K_scale]
            have h3 : Nat.ceil c ≤ Nat.ceil (max 1 L) := by
              apply Nat.ceil_le_ceil; exact le_max_of_le_right hc_le
            omega
          exact h1.trans h2
        _ = K_scale * F.card := by simp [Finset.sum_const, mul_comm]
    have h_cover : idxScaled ⊆ (allC : Set ℤ) := by
      intro k hk
      rcases hk with ⟨z, hz_k, ⟨y, hy_S, rfl⟩⟩
      let j : ℤ := Int.floor (y / δ)
      have h_y_in : y ∈ Set.Ico (δ * (j : ℝ)) (δ * ((j : ℝ) + 1)) := by
        have h1 : (j : ℝ) ≤ y / δ := Int.floor_le (y / δ)
        have h2 : y / δ < (j : ℝ) + 1 := Int.lt_floor_add_one (y / δ)
        have h_y1 : δ * (j : ℝ) ≤ y := by
          have h : δ * (j : ℝ) ≤ δ * (y / δ) := by gcongr
          have h' : δ * (y / δ) = y := by field_simp [hδ.ne'] <;> ring
          rw [h'] at h; exact h
        have h_y2 : y < δ * ((j : ℝ) + 1) := by
          have h : δ * (y / δ) < δ * ((j : ℝ) + 1) := by gcongr
          have h' : δ * (y / δ) = y := by field_simp [hδ.ne'] <;> ring
          rw [h'] at h; exact h
        exact ⟨h_y1, h_y2⟩
      have hj_A : j ∈ idxA := ⟨y, h_y_in, hy_S⟩
      have hj_F : j ∈ F := (hF_mem j).mpr hj_A
      have h_cy_in : c * y ∈ Set.Ico (c * δ * (j : ℝ)) (c * δ * (j : ℝ) + c * δ) := by
        have h_y1 : c * δ * (j : ℝ) ≤ c * y := by
          have h : c * (δ * (j : ℝ)) ≤ c * y :=
            mul_le_mul_of_nonneg_left h_y_in.1 (by linarith)
          have h' : c * δ * (j : ℝ) = c * (δ * (j : ℝ)) := by ring
          rw [h']; exact h
        have h_y2 : c * y < c * δ * (j : ℝ) + c * δ := by
          have h : c * y < c * (δ * ((j : ℝ) + 1)) :=
            mul_lt_mul_of_pos_left h_y_in.2 hc_pos
          have h' : c * (δ * ((j : ℝ) + 1)) = c * δ * (j : ℝ) + c * δ := by ring
          rw [h'] at h; exact h
        exact ⟨h_y1, h_y2⟩
      have h_cover' : c * y ∈ ⋃ k' ∈ C_j j, Set.Ico (δ * (k' : ℝ)) (δ * ((k' : ℝ) + 1)) :=
        hC_j_cover j h_cy_in
      rcases Set.mem_iUnion₂.mp h_cover' with ⟨k', hk'_in, hcy_in'⟩
      have h_k'_eq_k : k' = k := by
        have h_inter : (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩
            Set.Ico (δ * (k' : ℝ)) (δ * ((k' : ℝ) + 1))).Nonempty :=
          ⟨c * y, hz_k, hcy_in'⟩
        exact (dyadic_interval_unique δ hδ k k' h_inter).symm
      rw [h_k'_eq_k] at hk'_in
      exact Finset.mem_biUnion.mpr ⟨j, hj_F, hk'_in⟩
    have h_encard_le : idxScaled.encard ≤ (allC.card : ENNReal) := by
      have h1 : idxScaled.encard ≤ (allC : Set ℤ).encard := Set.encard_mono h_cover
      have h2 : (allC : Set ℤ).encard = ↑allC.card := by simp
      have h3 : idxScaled.encard ≤ ↑allC.card := by
        rw [h2] at h1; exact h1
      exact_mod_cast h3
    have h_idxA_encard : idxA.encard = (F.card : ENNReal) := by
      have h4 : idxA = (F : Set ℤ) := by
        ext j; simp [F, Set.Finite.mem_toFinset]
      rw [h4]; simp
    have h5 : Nreal δ ((fun x : ℝ => c * x) '' S) = idxScaled.encard := by
      simpa [Nreal, dyadicCoveringNumber] using h_eq2
    have h6 : Nreal δ S = idxA.encard := by
      simpa [Nreal, dyadicCoveringNumber] using h_eq1
    rw [h5, h6, h_idxA_encard]
    calc idxScaled.encard ≤ (allC.card : ENNReal) := h_encard_le
      _ ≤ (K_scale : ENNReal) * (F.card : ENNReal) := by exact_mod_cast h_allC_card
  · have h_encard_top : idxA.encard = ⊤ := by
      rw [Set.encard_eq_top_iff]; exact h_finite
    have hN_top : Nreal δ S = ⊤ := by
      have h7 : Nreal δ S = idxA.encard := by
        simpa [Nreal, dyadicCoveringNumber] using h_eq1
      rw [h7, h_encard_top] <;> simp
    exact False.elim (h_top hN_top)

end WeakTwoEndsSumProduct
