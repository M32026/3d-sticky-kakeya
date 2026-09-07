module

/-
# Coefficient Rounding Lemma

Given A ⊆ [1,2] and |x - x'| ≤ C·δ, the δ-covering number of A + x·A
is at most a constant (depending on C) times the δ-covering number of A + x'·A.

## Proof

Each point y = a + x·b in S = A + x·A maps to y' = a + x'·b in S' = A + x'·A
with |y - y'| ≤ 2Cδ. Thus every δ-dyadic cube meeting S is within O(C) cubes
of a cube meeting S'. The index set of cubes meeting S is contained in a
2⌈2C⌉+1-wide neighborhood of the index set for S'.
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

open Set MeasureTheory ENNReal Classical

noncomputable section

namespace ProductLikeIncidence

/-- The index set of δ-dyadic intervals meeting S. -/
def dyadicIndexSet (δ : ℝ) (S : Set ℝ) : Set ℤ :=
  {k : ℤ | (Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) ∩ S).Nonempty}

/-- Nreal δ S equals the encard of the index set of dyadic intervals meeting S. -/
lemma nreal_eq_index_encard {δ : ℝ} (hδ_pos : 0 < δ) {S : Set ℝ} :
    Nreal δ S = ENat.toENNReal (dyadicIndexSet δ S).encard := by
  let I : ℤ → Set ℝ := fun k => Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1))
  let K : Set ℤ := dyadicIndexSet δ S
  let f : ℤ → Set (EuclideanSpace ℝ (Fin 1)) := fun k => dyadicCube δ (fun _ => k)
  let mkPoint (y : ℝ) : EuclideanSpace ℝ (Fin 1) :=
    (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ => y)
  have h_f_inj : Set.InjOn f K := by
    intro k1 _ k2 _ h
    let z1 := mkPoint (δ * (k1 : ℝ))
    have hz1 : z1 ∈ f k1 := by
      have h : ∀ i : Fin 1, z1 i ∈ Set.Ico (δ * (k1 : ℝ)) (δ * ((k1 : ℝ) + 1)) := by
        intro i
        have h9 : z1 i = δ * (k1 : ℝ) := by simp [mkPoint] <;> rfl
        rw [h9] <;> constructor <;> linarith
      simpa [f, dyadicCube] using h
    have hz1' : z1 ∈ f k2 := by rw [h] at hz1; exact hz1
    have h4 : z1 0 ∈ Set.Ico (δ * (k2 : ℝ)) (δ * ((k2 : ℝ) + 1)) := by
      have h5 : ∀ i : Fin 1, z1 i ∈ Set.Ico (δ * (k2 : ℝ)) (δ * ((k2 : ℝ) + 1)) := by
        simpa [f, dyadicCube] using hz1'
      exact h5 0
    have h_z1 : z1 0 = δ * (k1 : ℝ) := by simp [mkPoint] <;> rfl
    rw [h_z1] at h4
    have h5 : (k2 : ℝ) ≤ (k1 : ℝ) := by
      have h51 : δ * (k2 : ℝ) ≤ δ * (k1 : ℝ) := h4.1
      have h52 : (δ * (k2 : ℝ)) / δ ≤ (δ * (k1 : ℝ)) / δ := by gcongr
      have h53 : (δ * (k2 : ℝ)) / δ = (k2 : ℝ) := by field_simp [hδ_pos.ne']
      have h54 : (δ * (k1 : ℝ)) / δ = (k1 : ℝ) := by field_simp [hδ_pos.ne']
      rw [h53, h54] at h52; exact h52
    have h6 : (k1 : ℝ) < (k2 : ℝ) + 1 := by
      have h61 : δ * (k1 : ℝ) < δ * ((k2 : ℝ) + 1) := h4.2
      have h62 : (δ * (k1 : ℝ)) / δ < (δ * ((k2 : ℝ) + 1)) / δ := by gcongr
      have h63 : (δ * (k1 : ℝ)) / δ = (k1 : ℝ) := by field_simp [hδ_pos.ne']
      have h64 : (δ * ((k2 : ℝ) + 1)) / δ = (k2 : ℝ) + 1 := by field_simp [hδ_pos.ne']
      rw [h63, h64] at h62; exact h62
    have h7 : k2 ≤ k1 := by exact_mod_cast h5
    have h8 : k1 < k2 + 1 := by exact_mod_cast h6
    omega
  have h_image_eq : f '' K = dyadicCubesMeeting (d := 1) δ (realLineCopy S) := by
    apply Set.Subset.antisymm
    · -- f '' K ⊆ dyadicCubesMeeting
      intro Q hQ
      rcases hQ with ⟨k, hk, rfl⟩
      rcases hk with ⟨x, hxI, hxS⟩
      let z := mkPoint x
      have hz1 : z ∈ f k := by
        have h : ∀ i : Fin 1, z i ∈ Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1)) := by
          intro i
          have h9 : z i = x := by simp [mkPoint] <;> rfl
          rw [h9]; exact hxI
        simpa [f, dyadicCube] using h
      have hz2 : z ∈ realLineCopy S := by
        have h_z0 : z 0 = x := by simp [mkPoint] <;> rfl
        have h : z 0 ∈ S := by rw [h_z0]; exact hxS
        simpa [realLineCopy] using h
      have h_meets : (f k ∩ realLineCopy S).Nonempty := ⟨z, hz1, hz2⟩
      exact ⟨⟨(fun _ => k), rfl⟩, h_meets⟩
    · -- dyadicCubesMeeting ⊆ f '' K
      intro Q hQ
      rcases hQ with ⟨hQ_cube, hQ_meets⟩
      rcases hQ_cube with ⟨k, rfl⟩
      rcases hQ_meets with ⟨z, hzQ, hzS⟩
      have h1 : z 0 ∈ Set.Ico (δ * (k 0 : ℝ)) (δ * ((k 0 : ℝ) + 1)) := hzQ 0
      have h2 : z 0 ∈ S := by simpa [realLineCopy] using hzS
      have h3 : (Set.Ico (δ * (k 0 : ℝ)) (δ * ((k 0 : ℝ) + 1)) ∩ S).Nonempty :=
        ⟨z 0, h1, h2⟩
      have h4 : k 0 ∈ K := by
        simpa [K, dyadicIndexSet] using h3
      have h5 : f (k 0) = dyadicCube δ k := by
        funext i
        <;> simp [f, dyadicCube]
        <;> rfl
      exact ⟨k 0, h4, h5⟩
  have h_encard : (f '' K).encard = K.encard :=
    h_f_inj.encard_image
  rw [h_image_eq] at h_encard
  have h_final : Nreal δ S = ENat.toENNReal (dyadicIndexSet δ S).encard := by
    dsimp only [Nreal, dyadicCoveringNumber]
    rw [h_encard]
    <;> rfl
  exact h_final

/-- **Coefficient rounding lemma**: if |x - x'| ≤ C·δ and A ⊆ [1,2], then
    Nδ(A + x·A) ≤ (2⌈2C⌉+1) · Nδ(A + x'·A). -/
theorem coefficient_rounding_covering
    {δ C : ℝ} (hδ_pos : 0 < δ) (hC_nonneg : 0 ≤ C)
    {A : Set ℝ} (hA_sub : A ⊆ Set.Icc 1 2)
    {x x' : ℝ} (h_close : |x - x'| ≤ C * δ) :
    Nreal δ (Set.image2 (fun a b => a + x * b) A A) ≤
      (2 * Nat.ceil (2 * C) + 1 : ENNReal) *
      Nreal δ (Set.image2 (fun a b => a + x' * b) A A) := by
  let S : Set ℝ := Set.image2 (fun a b => a + x * b) A A
  let S' : Set ℝ := Set.image2 (fun a b => a + x' * b) A A
  let I : ℤ → Set ℝ := fun k => Set.Ico (δ * (k : ℝ)) (δ * ((k : ℝ) + 1))
  let K : Set ℤ := dyadicIndexSet δ S
  let K' : Set ℤ := dyadicIndexSet δ S'
  let M : ℕ := Nat.ceil (2 * C)
  have hM_ge : (2 * C : ℝ) ≤ (M : ℝ) := Nat.le_ceil (2 * C)
  have hM_nonneg : 0 ≤ (M : ℝ) := by positivity
  -- Key index bound: if y ∈ I k, y' ∈ I k', |y - y'| ≤ 2Cδ, then |k - k'| ≤ M
  have h_index_bound : ∀ (k k' : ℤ) (y y' : ℝ),
      y ∈ I k → y' ∈ I k' → |y - y'| ≤ 2 * C * δ → |(k : ℤ) - k'| ≤ (M : ℤ) := by
    intro k k' y y' hy hy' hdist
    have h1 : δ * (k : ℝ) ≤ y := hy.1
    have h2 : y < δ * ((k : ℝ) + 1) := hy.2
    have h3 : δ * (k' : ℝ) ≤ y' := hy'.1
    have h4 : y' < δ * ((k' : ℝ) + 1) := hy'.2
    have h5 : |y - y'| ≤ (M : ℝ) * δ := by
      calc |y - y'| ≤ 2 * C * δ := hdist
        _ ≤ (M : ℝ) * δ := by gcongr
    have h6 : y - y' ≤ (M : ℝ) * δ := by
      calc y - y' ≤ |y - y'| := by exact le_abs_self (y - y')
        _ ≤ (M : ℝ) * δ := h5
    have h7 : y' - y ≤ (M : ℝ) * δ := by
      calc y' - y ≤ |y' - y| := by exact le_abs_self (y' - y)
        _ = |y - y'| := by rw [abs_sub_comm]
        _ ≤ (M : ℝ) * δ := h5
    have h_k_le : k ≤ k' + (M : ℤ) := by
      by_contra h
      have h8 : k ≥ k' + (M : ℤ) + 1 := by omega
      have h9 : (k : ℝ) ≥ (k' : ℝ) + (M : ℝ) + 1 := by exact_mod_cast h8
      have h14 : (k : ℝ) - (k' : ℝ) - 1 ≥ (M : ℝ) := by linarith
      have h15 : 0 ≤ δ := by linarith [hδ_pos]
      have h16 : δ * ((k : ℝ) - (k' : ℝ) - 1) ≥ (M : ℝ) * δ := by
        have h17 : δ * (M : ℝ) ≤ δ * ((k : ℝ) - (k' : ℝ) - 1) := mul_le_mul_of_nonneg_left h14 h15
        linarith
      have h13 : y - y' > δ * ((k : ℝ) - (k' : ℝ) - 1) := by linarith [hδ_pos]
      have h10 : y - y' > (M : ℝ) * δ := by
        calc y - y' > δ * ((k : ℝ) - (k' : ℝ) - 1) := h13
          _ ≥ (M : ℝ) * δ := h16
      linarith [h6]
    have h_k'_le : k' ≤ k + (M : ℤ) := by
      by_contra h
      have h8 : k' ≥ k + (M : ℤ) + 1 := by omega
      have h9 : (k' : ℝ) ≥ (k : ℝ) + (M : ℝ) + 1 := by exact_mod_cast h8
      have h14 : (k' : ℝ) - (k : ℝ) - 1 ≥ (M : ℝ) := by linarith
      have h15 : 0 ≤ δ := by linarith [hδ_pos]
      have h16 : δ * ((k' : ℝ) - (k : ℝ) - 1) ≥ (M : ℝ) * δ := by
        have h17 : δ * (M : ℝ) ≤ δ * ((k' : ℝ) - (k : ℝ) - 1) := mul_le_mul_of_nonneg_left h14 h15
        linarith
      have h13 : y' - y > δ * ((k' : ℝ) - (k : ℝ) - 1) := by linarith [hδ_pos]
      have h10 : y' - y > (M : ℝ) * δ := by
        calc y' - y > δ * ((k' : ℝ) - (k : ℝ) - 1) := h13
          _ ≥ (M : ℝ) * δ := h16
      linarith [h7]
    have h11 : |k - k'| ≤ (M : ℤ) := by
      rw [abs_le]
      constructor <;> omega
    exact h11
  -- For each k ∈ K, find k' ∈ K' with |k - k'| ≤ M
  have h_cover : ∀ k ∈ K, ∃ k' ∈ K', |(k : ℤ) - k'| ≤ (M : ℤ) := by
    intro k hk
    rcases hk with ⟨y, hyI, hyS⟩
    rcases hyS with ⟨a, ha, b, hb, rfl⟩
    let y' : ℝ := a + x' * b
    have hy'_S' : y' ∈ S' := by
      exact ⟨a, ha, b, hb, rfl⟩
    have h_dist : |(a + x * b) - y'| ≤ 2 * C * δ := by
      dsimp only [y']
      have h1 : |(a + x * b) - (a + x' * b)| = |x - x'| * |b| := by
        have h2 : (a + x * b) - (a + x' * b) = (x - x') * b := by ring
        rw [h2, abs_mul]
      rw [h1]
      have hb2 : b ∈ Set.Icc (1 : ℝ) 2 := hA_sub hb
      have h3 : |b| ≤ 2 := by
        have h4 : 1 ≤ b := hb2.1
        have h5 : b ≤ 2 := hb2.2
        rw [abs_of_nonneg (by linarith)] <;> linarith
      calc |x - x'| * |b| ≤ (C * δ) * |b| := by gcongr
        _ ≤ (C * δ) * 2 := by gcongr
        _ = 2 * C * δ := by ring
    let k' : ℤ := Int.floor (y' / δ)
    have hy'_I : y' ∈ I k' := by
      have h5 : δ * (k' : ℝ) ≤ y' := by
        have h6 : (k' : ℝ) ≤ y' / δ := Int.floor_le (y' / δ)
        have h7 : δ * (k' : ℝ) ≤ δ * (y' / δ) := by gcongr
        have h8 : δ * (y' / δ) = y' := by field_simp [hδ_pos.ne']
        linarith
      have h9 : y' < δ * ((k' : ℝ) + 1) := by
        have h10 : y' / δ < (k' : ℝ) + 1 := Int.lt_floor_add_one (y' / δ)
        have h11 : δ * (y' / δ) < δ * ((k' : ℝ) + 1) := by gcongr
        have h12 : δ * (y' / δ) = y' := by field_simp [hδ_pos.ne']
        linarith
      exact ⟨h5, h9⟩
    have hk' : k' ∈ K' := by
      simpa [K', dyadicIndexSet] using ⟨y', hy'_I, hy'_S'⟩
    have h_bound : |(k : ℤ) - k'| ≤ (M : ℤ) :=
      h_index_bound k k' (a + x * b) y' hyI hy'_I h_dist
    exact ⟨k', hk', h_bound⟩
  -- K ⊆ ⋃ j ∈ Finset.Icc (-M) M, (K' + j)
  let shift : ℤ → Set ℤ := fun j => {k' + j | k' ∈ K'}
  have hK_sub : K ⊆ ⋃ j ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), shift j := by
    intro k hk
    rcases h_cover k hk with ⟨k', hk', hbound⟩
    let j : ℤ := k - k'
    have hj1 : -(M : ℤ) ≤ j := by linarith [abs_le.mp hbound]
    have hj2 : j ≤ (M : ℤ) := by linarith [abs_le.mp hbound]
    have hj_in : j ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
      simp only [Finset.mem_Icc] <;> exact ⟨hj1, hj2⟩
    have h_k_in : k ∈ shift j := by
      dsimp only [shift]
      exact ⟨k', hk', by ring⟩
    exact Set.mem_iUnion₂.mpr ⟨j, hj_in, h_k_in⟩
  -- encard bound via surjection from K' × Finset
  let idxSet : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)
  let g : ℤ × ℤ → ℤ := fun p => p.1 + p.2
  let domain : Set (ℤ × ℤ) := K' ×ˢ (idxSet : Set ℤ)
  have h_image : g '' domain = ⋃ j ∈ idxSet, shift j := by
    ext z
    simp only [domain, g, Set.mem_image, Set.mem_prod, Set.mem_iUnion₂, shift]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.2, hp.2, p.1, hp.1, by ring⟩
    · rintro ⟨j, hj, k', hk', rfl⟩
      exact ⟨(k', j), ⟨hk', hj⟩, by ring⟩
  have h_final : K ⊆ g '' domain := by
    rw [h_image]
    exact hK_sub
  have h_encard_le : K.encard ≤ (g '' domain).encard := Set.encard_mono h_final
  have h_image_encard : (g '' domain).encard ≤ domain.encard := Set.encard_image_le g domain
  have h_domain_encard : domain.encard = K'.encard * (idxSet.card : ℕ) := by
    simpa [domain, Set.encard_prod] using rfl
  have h_idx_card : idxSet.card = 2 * M + 1 := by
    simp [idxSet, Finset.Icc_eq_empty_of_lt]
    <;> omega
  rw [nreal_eq_index_encard hδ_pos, nreal_eq_index_encard hδ_pos]
  have h_cast : (↑(2 * M + 1) : ENat) = (2 * ↑M + 1 : ENat) := by norm_cast
  have h_main : ENat.toENNReal K.encard ≤
      ENat.toENNReal (K'.encard * (2 * M + 1)) := by
    exact ENat.toENNReal_mono (le_trans h_encard_le (le_trans h_image_encard (by
      rw [h_domain_encard, h_idx_card, h_cast])))
  have h_mul : ENat.toENNReal (K'.encard * (2 * M + 1)) =
      (2 * M + 1 : ENNReal) * ENat.toENNReal K'.encard := by
    rw [ENat.toENNReal_mul]
    <;> simp [mul_comm]
    <;> ring
  rw [h_mul] at h_main
  exact h_main

end ProductLikeIncidence
