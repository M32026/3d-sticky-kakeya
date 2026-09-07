module

/-
# Phase 0 Overlap Bound — Approximate Incidence

For fixed y ∈ [0,1] and a δ-parameter cube Q, the set of δ-grid points x
such that Q ∩ Pz(x,y) is nonempty has cardinality at most 7.

Uses approximate incidence: |p0*y+p1-x| ≤ 2δ for p ∈ Pz(x,y).

## Whiteprint node
`phase0_overlap_bound`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.ProductLikeProof
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open ProductLikeIncidence

/-- A set of δ-grid points contained in an interval of width ≤ 6δ
has cardinality at most 7. -/
lemma grid_points_in_six_delta_interval {δ : ℝ} (hδ : 0 < δ)
    {S : Set ℝ} (hS_grid : S ⊆ productLikeIntegerGrid δ)
    {lo hi : ℝ} (hS_sub : S ⊆ Set.Icc lo hi) (h_len : hi - lo ≤ 6 * δ) :
    S.Finite ∧ S.encard ≤ 7 := by
  classical
  let a : ℝ := lo / δ
  let b : ℝ := hi / δ
  have h_ab : b - a ≤ 6 := by
    dsimp only [a, b]
    have h : (hi - lo) / δ ≤ 6 := by
      calc (hi - lo) / δ ≤ (6 * δ) / δ := by gcongr
           _ = 6 := by field_simp [hδ.ne'] <;> ring
    have h2 : (hi - lo) / δ = hi / δ - lo / δ := by ring
    linarith
  let k_lo : ℤ := ⌈a⌉
  let k_hi : ℤ := ⌊b⌋
  by_cases h_case : k_lo ≤ k_hi
  · -- Case: there are integers in [a, b]
    have h1 : (k_hi : ℝ) - (k_lo : ℝ) ≤ 6 := by
      dsimp only [k_hi, k_lo]
      have h2 : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
      have h3 : a ≤ (⌈a⌉ : ℝ) := Int.le_ceil a
      linarith
    have h4 : k_hi - k_lo ≤ 6 := by exact_mod_cast h1
    let K_int : Finset ℤ := Finset.Icc k_lo k_hi
    have hK_card : K_int.card ≤ 7 := by
      have h5 : K_int.card = (k_hi - k_lo).toNat + 1 := by
        simp [K_int, Finset.Icc_eq_empty_of_lt, h_case, Int.toNat_of_nonneg]
        <;> omega
      rw [h5]
      have h6 : (k_hi - k_lo).toNat ≤ 6 := by
        exact Int.toNat_le.mpr h4
      omega
    let K : Set ℤ := {k | δ * (k : ℝ) ∈ S}
    have hK_sub : K ⊆ (K_int : Set ℤ) := by
      intro k hk
      have hx : δ * (k : ℝ) ∈ S := hk
      have h_range : lo ≤ δ * (k : ℝ) ∧ δ * (k : ℝ) ≤ hi := hS_sub hx
      have h6 : a ≤ (k : ℝ) := by
        dsimp only [a]
        have h_lo : lo ≤ δ * (k : ℝ) := h_range.1
        calc a = lo / δ := rfl
             _ ≤ (δ * (k : ℝ)) / δ := by gcongr
             _ = (k : ℝ) := by field_simp [hδ.ne'] <;> ring
      have h7 : (k : ℝ) ≤ b := by
        dsimp only [b]
        have h_hi : δ * (k : ℝ) ≤ hi := h_range.2
        calc (k : ℝ) = (δ * (k : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
             _ ≤ hi / δ := by gcongr
      have h8 : k_lo ≤ k := by
        dsimp only [k_lo]
        exact Int.ceil_le.mpr h6
      have h10 : k ≤ k_hi := by
        dsimp only [k_hi]
        exact Int.le_floor.mpr h7
      exact Finset.mem_Icc.mpr ⟨h8, h10⟩
    have hK_fin : K.Finite := Set.Finite.subset (Finset.finite_toSet K_int) hK_sub
    have hS_eq : S = (fun k : ℤ => δ * (k : ℝ)) '' K := by
      ext x
      simp only [K, Set.mem_image, Set.mem_setOf_eq]
      constructor
      · intro hx
        have hxg : x ∈ productLikeIntegerGrid δ := hS_grid hx
        rcases hxg with ⟨k, hk⟩
        refine ⟨k, ?_, hk.symm⟩
        rw [hk] at hx
        exact hx
      · rintro ⟨k, hk, rfl⟩
        exact hk
    have hS_fin : S.Finite := by
      rw [hS_eq]
      exact Set.Finite.image _ hK_fin
    have hS_encard : S.encard ≤ K.encard := by
      rw [hS_eq]
      exact Set.encard_image_le (fun k : ℤ => δ * (k : ℝ)) K
    have hK_encard : K.encard ≤ (K_int : Set ℤ).encard := Set.encard_le_encard hK_sub
    have h_final : S.encard ≤ 7 := by
      calc S.encard ≤ K.encard := hS_encard
           _ ≤ (K_int : Set ℤ).encard := hK_encard
           _ = ↑K_int.card := by simp
           _ ≤ 7 := by exact_mod_cast hK_card
    exact ⟨hS_fin, h_final⟩
  · -- Case: no integers in [a, b], so S is empty
    have h_contra : ∀ (k : ℤ), ¬(a ≤ (k : ℝ) ∧ (k : ℝ) ≤ b) := by
      intro k h
      have h10 : k_lo ≤ k := by
        dsimp only [k_lo]
        exact Int.ceil_le.mpr h.1
      have h12 : k ≤ k_hi := by
        dsimp only [k_hi]
        exact Int.le_floor.mpr h.2
      exact h_case (le_trans h10 h12)
    have hS_empty : S = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      have hxg : x ∈ productLikeIntegerGrid δ := hS_grid hx
      rcases hxg with ⟨k, hk⟩
      have h_range : lo ≤ x ∧ x ≤ hi := hS_sub hx
      have h6 : a ≤ (k : ℝ) := by
        dsimp only [a]
        have h_lo : lo ≤ x := h_range.1
        rw [hk] at h_lo
        calc a = lo / δ := rfl
             _ ≤ (δ * (k : ℝ)) / δ := by gcongr
             _ = (k : ℝ) := by field_simp [hδ.ne'] <;> ring
      have h7 : (k : ℝ) ≤ b := by
        dsimp only [b]
        have h_hi : x ≤ hi := h_range.2
        rw [hk] at h_hi
        calc (k : ℝ) = (δ * (k : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
             _ ≤ hi / δ := by gcongr
      exact h_contra k ⟨h6, h7⟩
    rw [hS_empty]
    simp

/-- For fixed y and δ-cube Q, the set of x ∈ X y with Q ∩ Pz(x,y) nonempty
has cardinality at most 7, under approximate incidence |p0*y+p1-x| ≤ 2δ. -/
lemma approximate_incidence_overlap_le_7 {δ : ℝ} (hδ_pos : 0 < δ)
    {Y : Set ℝ} {X : ℝ → Set ℝ} {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    {Pz : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2))}
    (hPz_approx : ∀ (z : EuclideanSpace ℝ (Fin 2)),
      ∀ p ∈ Pz z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ)
    (hX_grid : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ)
    (hyY : y ∈ Y)
    {Q : Set (EuclideanSpace ℝ (Fin 2))}
    (hQ_dyadic : Q ∈ dyadicCubes 2 δ) :
    let S : Set ℝ := {x ∈ X y | (Q ∩ Pz (mkPoint2 x y)).Nonempty}
    S.Finite ∧ S.encard ≤ 7 := by
  rcases hQ_dyadic with ⟨k, hQ_eq⟩
  let a : ℝ := δ * (k 0 : ℝ)
  let b : ℝ := δ * (k 1 : ℝ)
  have h_p_bounds : ∀ p ∈ Q,
      a ≤ p 0 ∧ p 0 < a + δ ∧ b ≤ p 1 ∧ p 1 < b + δ := by
    intro p hp
    have h : p ∈ dyadicCube δ k := by rw [hQ_eq] at hp; exact hp
    have h0 : p 0 ∈ Set.Ico (δ * (k 0 : ℝ)) (δ * ((k 0 : ℝ) + 1)) := h 0
    have h1 : p 1 ∈ Set.Ico (δ * (k 1 : ℝ)) (δ * ((k 1 : ℝ) + 1)) := h 1
    have ha : a = δ * (k 0 : ℝ) := by rfl
    have hb : b = δ * (k 1 : ℝ) := by rfl
    have h01 : a ≤ p 0 := by rw [ha]; exact h0.1
    have h02 : p 0 < a + δ := by
      rw [ha]
      have h_eq : δ * ((k 0 : ℝ) + 1) = δ * (k 0 : ℝ) + δ := by ring
      rw [h_eq] at h0
      exact h0.2
    have h11 : b ≤ p 1 := by rw [hb]; exact h1.1
    have h12 : p 1 < b + δ := by
      rw [hb]
      have h_eq : δ * ((k 1 : ℝ) + 1) = δ * (k 1 : ℝ) + δ := by ring
      rw [h_eq] at h1
      exact h1.2
    exact ⟨h01, h02, h11, h12⟩
  let raw_lo : ℝ := a * y + b
  let raw_hi : ℝ := (a + δ) * y + (b + δ)
  let lo : ℝ := raw_lo - 2 * δ
  let hi : ℝ := raw_hi + 2 * δ
  have h_len : hi - lo ≤ 6 * δ := by
    dsimp only [lo, hi, raw_lo, raw_hi]
    nlinarith [hy1]
  let S : Set ℝ := {x ∈ X y | (Q ∩ Pz (mkPoint2 x y)).Nonempty}
  have hS_grid : S ⊆ productLikeIntegerGrid δ := by
    intro x hx
    have h_x_in_Xy : x ∈ X y := hx.1
    have h : X y ⊆ productLikeUnitGrid δ := hX_grid y hyY
    have h2 : x ∈ productLikeUnitGrid δ := h h_x_in_Xy
    exact h2.1
  have hS_sub : S ⊆ Set.Icc lo hi := by
    intro x hx
    have h_nonempty : (Q ∩ Pz (mkPoint2 x y)).Nonempty := hx.2
    rcases h_nonempty with ⟨p, hpQ, hpPz⟩
    have hpb := h_p_bounds p hpQ
    have h_ineq : |p 0 * y + p 1 - x| ≤ 2 * δ := hPz_approx (mkPoint2 x y) p hpPz
    have h5 : raw_lo ≤ p 0 * y + p 1 := by
      dsimp only [raw_lo]; nlinarith [hy0, hpb.1, hpb.2.2.1]
    have h6 : p 0 * y + p 1 ≤ raw_hi := by
      dsimp only [raw_hi]; nlinarith [hy0, hy1, hpb.2.1, hpb.2.2.2]
    have h7 : |x - (p 0 * y + p 1)| ≤ 2 * δ := by
      have h_eq : |x - (p 0 * y + p 1)| = |p 0 * y + p 1 - x| := by
        rw [show x - (p 0 * y + p 1) = -(p 0 * y + p 1 - x) by ring, abs_neg]
      rw [h_eq]
      exact h_ineq
    have h8 : p 0 * y + p 1 - 2 * δ ≤ x := by linarith [abs_le.mp h7]
    have h9 : x ≤ p 0 * y + p 1 + 2 * δ := by linarith [abs_le.mp h7]
    have h10 : lo ≤ x := by
      dsimp only [lo]; linarith
    have h11 : x ≤ hi := by
      dsimp only [hi]; linarith
    exact ⟨h10, h11⟩
  exact grid_points_in_six_delta_interval hδ_pos hS_grid hS_sub h_len

end
