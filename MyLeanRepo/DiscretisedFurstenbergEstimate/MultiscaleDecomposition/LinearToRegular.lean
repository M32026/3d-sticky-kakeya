module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base

@[expose] public section

namespace DirecretisedFurstenbergEstimate
namespace MultiscaleDecomposition

lemma dyadic_square_contained_in_one_square
    {Δ : ℝ} {n : ℕ} (hn_pos : 0 < n)
    (h1 : (1 : ℝ) = (n : ℝ) * Δ)
    {k : ℕ} (hk : 0 < k) {a i : ℤ}
    (h_inter : Set.Nonempty (Set.Ico (a * Δ ^ k) ((a + 1) * Δ ^ k) ∩ Set.Ico (i : ℝ) (i + 1))) :
    (i : ℝ) ≤ a * Δ ^ k ∧ (a + 1 : ℝ) * Δ ^ k ≤ (i + 1 : ℝ) := by
  have hΔ : 0 < Δ := by nlinarith
  have hΔk_pos : 0 < Δ ^ k := by positivity
  have h_div_k : (n : ℝ) ^ k * Δ ^ k = 1 := by
    have h : (n : ℝ) ^ k * Δ ^ k = ((n : ℝ) * Δ) ^ k := by
      rw [←mul_pow] <;> ring
    rw [h, ←h1] <;> norm_num
  rcases h_inter with ⟨x, hx1, hx2⟩
  set y : ℝ := x * (n : ℝ) ^ k with hy_def
  have h1a : (a : ℝ) ≤ y := by
    have h_comm : Δ ^ k * (n : ℝ) ^ k = 1 := by rw [mul_comm, h_div_k]
    have hmul : a * Δ ^ k * (n : ℝ) ^ k = (a : ℝ) := by
      rw [mul_assoc, h_comm] <;> ring
    have h : a * Δ ^ k * (n : ℝ) ^ k ≤ x * (n : ℝ) ^ k := by
      gcongr
      <;> exact hx1.1
    rw [hmul] at h; exact h
  have h2a : y < (a + 1 : ℝ) := by
    have h_comm : Δ ^ k * (n : ℝ) ^ k = 1 := by rw [mul_comm, h_div_k]
    have hmul : (a + 1 : ℝ) * Δ ^ k * (n : ℝ) ^ k = (a + 1 : ℝ) := by
      rw [mul_assoc, h_comm] <;> ring
    have h : x * (n : ℝ) ^ k < (a + 1 : ℝ) * Δ ^ k * (n : ℝ) ^ k := by
      gcongr
      <;> exact hx1.2
    rw [hmul] at h; exact h
  have h_nk_pos : 0 < (n : ℝ) ^ k := by positivity
  have h3a : (i : ℝ) * (n : ℝ) ^ k ≤ y := by
    dsimp only [y]
    exact mul_le_mul_of_nonneg_right hx2.1 h_nk_pos.le
  have h4a : y < (i + 1 : ℝ) * (n : ℝ) ^ k := by
    dsimp only [y]
    exact mul_lt_mul_of_pos_right hx2.2 h_nk_pos
  have h_i_lt : (i : ℝ) * (n : ℝ) ^ k < (a + 1 : ℝ) := by linarith
  have h_a_lt : (a : ℝ) < (i + 1 : ℝ) * (n : ℝ) ^ k := by linarith
  have h_cast1 : ((i * n ^ k : ℤ) : ℝ) = (i : ℝ) * (n : ℝ) ^ k := by simp <;> ring
  have h_cast2 : (((i + 1) * n ^ k : ℤ) : ℝ) = (i + 1 : ℝ) * (n : ℝ) ^ k := by simp <;> ring
  have h5 : i * n ^ k ≤ a := by
    have h51 : ((i * n ^ k : ℤ) : ℝ) < ((a + 1 : ℤ) : ℝ) := by
      rw [h_cast1]
      simpa using h_i_lt
    have h52 : i * n ^ k < a + 1 := by exact_mod_cast h51
    omega
  have h6 : a + 1 ≤ (i + 1) * n ^ k := by
    have h61 : ((a : ℤ) : ℝ) < (((i + 1) * n ^ k : ℤ) : ℝ) := by
      rw [h_cast2]
      simpa using h_a_lt
    have h62 : a < (i + 1) * n ^ k := by exact_mod_cast h61
    omega
  have h_left : (i : ℝ) ≤ a * Δ ^ k := by
    have h_eq : (i : ℝ) = ((i * n ^ k : ℤ) : ℝ) * Δ ^ k := by
      have h : ((i * n ^ k : ℤ) : ℝ) * Δ ^ k = (i : ℝ) * ((n : ℝ) ^ k * Δ ^ k) := by
        simp [mul_assoc] <;> ring
      rw [h, h_div_k] <;> ring
    rw [h_eq]
    have h7 : 0 ≤ Δ ^ k := by positivity
    have h8 : ((i * n ^ k : ℤ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast h5
    exact mul_le_mul_of_nonneg_right h8 h7
  have h_right : (a + 1 : ℝ) * Δ ^ k ≤ (i + 1 : ℝ) := by
    have h_eq : (((i + 1) * n ^ k : ℤ) : ℝ) * Δ ^ k = (i + 1 : ℝ) := by
      have h : (((i + 1) * n ^ k : ℤ) : ℝ) * Δ ^ k = (i + 1 : ℝ) * ((n : ℝ) ^ k * Δ ^ k) := by
        simp [mul_assoc] <;> ring
      rw [h, h_div_k] <;> ring
    have h7 : (a + 1 : ℝ) * Δ ^ k ≤ (((i + 1) * n ^ k : ℤ) : ℝ) * Δ ^ k := by
      gcongr
      exact_mod_cast h6
    rw [h_eq] at h7
    exact h7
  exact ⟨h_left, h_right⟩

/-- Translation by integer vector preserves dyadic square counts when `1/Δ ∈ ℕ`.

    `homothetyS 1 i j` translates by `-(i,j)`. Since `i = i * n^k * Δ^k`,
    it maps dyadic `Δ^k`-squares to dyadic `Δ^k`-squares with shifted indices. -/
lemma dyadicSquareCount_translation {Δ : ℝ} {n : ℕ} (hn_pos : 0 < n)
    (h1 : (1 : ℝ) = (n : ℝ) * Δ) {k : ℕ} (i j : ℤ)
    (A : Set EuclideanPlane) :
    dyadicSquareCount (Δ ^ k) (homothetyS 1 i j '' A) = dyadicSquareCount (Δ ^ k) A := by
  let τ : EuclideanPlane → EuclideanPlane := homothetyS 1 i j
  let v : EuclideanPlane :=
    WithLp.toLp (2 : ENNReal) (fun k : Fin 2 => if k = 0 then (i : ℝ) else (j : ℝ))
  have hτ_v : ∀ (x : EuclideanPlane), τ x = x - v := by
    intro x; simp [τ, homothetyS, v] <;> ext k <;> fin_cases k <;> simp [mul_one] <;> ring
  let si : ℤ := i * (n ^ k)
  let sj : ℤ := j * (n ^ k)
  have h_div_k : (n : ℝ) ^ k * Δ ^ k = 1 := by
    have h : (n : ℝ) ^ k * Δ ^ k = ((n : ℝ) * Δ) ^ k := by rw [←mul_pow] <;> ring
    rw [h, ←h1] <;> norm_num
  have hsi : (si : ℝ) = (i : ℝ) * (n : ℝ) ^ k := by simp [si] <;> norm_cast
  have hsj : (sj : ℝ) = (j : ℝ) * (n : ℝ) ^ k := by simp [sj] <;> norm_cast
  -- Helper equalities: (a+si)*Δ^k = a*Δ^k + i, and ((a+si)+1)*Δ^k = (a+1)*Δ^k + i
  have h_c0_eq : ∀ (a : ℤ), ((a + si : ℤ) : ℝ) * Δ ^ k = (a : ℝ) * Δ ^ k + (i : ℝ) := by
    intro a
    have h_cast : ((a + si : ℤ) : ℝ) = (a : ℝ) + (si : ℝ) := by
      simp only [Int.cast_add] <;> norm_cast
    calc
      ((a + si : ℤ) : ℝ) * Δ ^ k
        = ((a : ℝ) + (si : ℝ)) * Δ ^ k := by rw [h_cast]
      _ = (a : ℝ) * Δ ^ k + (si : ℝ) * Δ ^ k := by ring
      _ = (a : ℝ) * Δ ^ k + (i : ℝ) * ((n : ℝ) ^ k * Δ ^ k) := by rw [hsi] <;> ring
      _ = (a : ℝ) * Δ ^ k + (i : ℝ) := by rw [h_div_k] <;> ring
  have h_c1_eq : ∀ (a : ℤ), (((a + si : ℤ) : ℝ) + 1) * Δ ^ k = ((a + 1 : ℝ) * Δ ^ k) + (i : ℝ) := by
    intro a
    have h_cast : ((a + si : ℤ) : ℝ) + 1 = (a : ℝ) + 1 + (si : ℝ) := by
      have h : ((a + si : ℤ) : ℝ) = (a : ℝ) + (si : ℝ) := by
        simp only [Int.cast_add] <;> norm_cast
      linarith
    calc
      (((a + si : ℤ) : ℝ) + 1) * Δ ^ k
        = ((a : ℝ) + 1 + (si : ℝ)) * Δ ^ k := by rw [h_cast]
      _ = ((a + 1 : ℝ) * Δ ^ k) + (si : ℝ) * Δ ^ k := by ring
      _ = ((a + 1 : ℝ) * Δ ^ k) + (i : ℝ) * ((n : ℝ) ^ k * Δ ^ k) := by rw [hsi] <;> ring
      _ = ((a + 1 : ℝ) * Δ ^ k) + (i : ℝ) := by rw [h_div_k] <;> ring
  have h_d0_eq : ∀ (b : ℤ), ((b + sj : ℤ) : ℝ) * Δ ^ k = (b : ℝ) * Δ ^ k + (j : ℝ) := by
    intro b
    have h_cast : ((b + sj : ℤ) : ℝ) = (b : ℝ) + (sj : ℝ) := by
      simp only [Int.cast_add] <;> norm_cast
    calc
      ((b + sj : ℤ) : ℝ) * Δ ^ k
        = ((b : ℝ) + (sj : ℝ)) * Δ ^ k := by rw [h_cast]
      _ = (b : ℝ) * Δ ^ k + (sj : ℝ) * Δ ^ k := by ring
      _ = (b : ℝ) * Δ ^ k + (j : ℝ) * ((n : ℝ) ^ k * Δ ^ k) := by rw [hsj] <;> ring
      _ = (b : ℝ) * Δ ^ k + (j : ℝ) := by rw [h_div_k] <;> ring
  have h_d1_eq : ∀ (b : ℤ), (((b + sj : ℤ) : ℝ) + 1) * Δ ^ k = ((b + 1 : ℝ) * Δ ^ k) + (j : ℝ) := by
    intro b
    have h_cast : ((b + sj : ℤ) : ℝ) + 1 = (b : ℝ) + 1 + (sj : ℝ) := by
      have h : ((b + sj : ℤ) : ℝ) = (b : ℝ) + (sj : ℝ) := by
        simp only [Int.cast_add] <;> norm_cast
      linarith
    calc
      (((b + sj : ℤ) : ℝ) + 1) * Δ ^ k
        = ((b : ℝ) + 1 + (sj : ℝ)) * Δ ^ k := by rw [h_cast]
      _ = ((b + 1 : ℝ) * Δ ^ k) + (sj : ℝ) * Δ ^ k := by ring
      _ = ((b + 1 : ℝ) * Δ ^ k) + (j : ℝ) * ((n : ℝ) ^ k * Δ ^ k) := by rw [hsj] <;> ring
      _ = ((b + 1 : ℝ) * Δ ^ k) + (j : ℝ) := by rw [h_div_k] <;> ring
  let shift : ℤ × ℤ → ℤ × ℤ := fun p => (p.1 - si, p.2 - sj)
  have h_inj : Function.Injective shift := by
    intro p q h; simp [shift, Prod.ext_iff] at h ⊢ <;> omega
  have h_key : ∀ (a b : ℤ),
      ((τ '' A) ∩ dyadicSquare (Δ ^ k) a b).Nonempty ↔
      (A ∩ dyadicSquare (Δ ^ k) (a + si) (b + sj)).Nonempty := by
    intro a b
    constructor
    · rintro ⟨y, ⟨x, hxA, rfl⟩, hy_sq⟩
      have h_tx0 : (τ x) 0 = x 0 - (i : ℝ) := by rw [hτ_v x] <;> simp [v] <;> rfl
      have h_tx1 : (τ x) 1 = x 1 - (j : ℝ) := by rw [hτ_v x] <;> simp [v] <;> rfl
      have h_y01 : (a : ℝ) * Δ ^ k ≤ (τ x) 0 := hy_sq.1.1
      have h_y02 : (τ x) 0 < ((a : ℝ) + 1) * Δ ^ k := hy_sq.1.2
      have h_y11 : (b : ℝ) * Δ ^ k ≤ (τ x) 1 := hy_sq.2.1
      have h_y12 : (τ x) 1 < ((b : ℝ) + 1) * Δ ^ k := hy_sq.2.2
      have h_goal01 : ((a + si : ℤ) : ℝ) * Δ ^ k ≤ x 0 := by
        linarith [h_c0_eq a, h_tx0, h_y01]
      have h_goal02 : x 0 < (((a + si : ℤ) : ℝ) + 1) * Δ ^ k := by
        linarith [h_c1_eq a, h_tx0, h_y02]
      have h_goal11 : ((b + sj : ℤ) : ℝ) * Δ ^ k ≤ x 1 := by
        linarith [h_d0_eq b, h_tx1, h_y11]
      have h_goal12 : x 1 < (((b + sj : ℤ) : ℝ) + 1) * Δ ^ k := by
        linarith [h_d1_eq b, h_tx1, h_y12]
      have h_x_in_sq : x ∈ dyadicSquare (Δ ^ k) (a + si) (b + sj) := by
        simp only [dyadicSquare, Set.mem_setOf_eq, Set.mem_Ico]
        exact ⟨⟨h_goal01, h_goal02⟩, ⟨h_goal11, h_goal12⟩⟩
      exact ⟨x, hxA, h_x_in_sq⟩
    · rintro ⟨x, hxA, hx_sq⟩
      have h_x01 : ((a + si : ℤ) : ℝ) * Δ ^ k ≤ x 0 := hx_sq.1.1
      have h_x02 : x 0 < (((a + si : ℤ) : ℝ) + 1) * Δ ^ k := hx_sq.1.2
      have h_x11 : ((b + sj : ℤ) : ℝ) * Δ ^ k ≤ x 1 := hx_sq.2.1
      have h_x12 : x 1 < (((b + sj : ℤ) : ℝ) + 1) * Δ ^ k := hx_sq.2.2
      have h_tx0 : (τ x) 0 = x 0 - (i : ℝ) := by rw [hτ_v x] <;> simp [v] <;> rfl
      have h_tx1 : (τ x) 1 = x 1 - (j : ℝ) := by rw [hτ_v x] <;> simp [v] <;> rfl
      have h_y01 : (a : ℝ) * Δ ^ k ≤ (τ x) 0 := by
        linarith [h_c0_eq a, h_tx0, h_x01]
      have h_y02 : (τ x) 0 < ((a : ℝ) + 1) * Δ ^ k := by
        linarith [h_c1_eq a, h_tx0, h_x02]
      have h_y11 : (b : ℝ) * Δ ^ k ≤ (τ x) 1 := by
        linarith [h_d0_eq b, h_tx1, h_x11]
      have h_y12 : (τ x) 1 < ((b : ℝ) + 1) * Δ ^ k := by
        linarith [h_d1_eq b, h_tx1, h_x12]
      have h_ty_in_sq : τ x ∈ dyadicSquare (Δ ^ k) a b := by
        simp only [dyadicSquare, Set.mem_setOf_eq, Set.mem_Ico]
        exact ⟨⟨h_y01, h_y02⟩, ⟨h_y11, h_y12⟩⟩
      exact ⟨τ x, ⟨x, hxA, rfl⟩, h_ty_in_sq⟩
  let S : Set (ℤ × ℤ) := {p | (A ∩ dyadicSquare (Δ ^ k) p.1 p.2).Nonempty}
  let S' : Set (ℤ × ℤ) := {p | ((τ '' A) ∩ dyadicSquare (Δ ^ k) p.1 p.2).Nonempty}
  have hS'_eq : S' = shift '' S := by
    ext ⟨a, b⟩
    simp only [S', S, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · intro h
      refine ⟨(a + si, b + sj), ?_, by simp [shift] <;> omega⟩
      exact (h_key a b).mp h
    · rintro ⟨p, hcd, h_eq⟩
      have h_eq' : (p.1 - si, p.2 - sj) = (a, b) := by simpa [shift] using h_eq
      have h_c : p.1 - si = a := congr_arg Prod.fst h_eq'
      have h_d : p.2 - sj = b := congr_arg Prod.snd h_eq'
      have h_c' : p.1 = a + si := by omega
      have h_d' : p.2 = b + sj := by omega
      have h_p_eq : p = (a + si, b + sj) := by
        ext <;> simp [h_c', h_d'] <;> omega
      rw [h_p_eq] at hcd
      exact (h_key a b).mpr hcd
  have h_main : S'.encard = S.encard := by
    rw [hS'_eq]
    exact h_inj.encard_image S
  have h1' : dyadicSquareCount (Δ ^ k) (τ '' A) = S'.encard := by rfl
  have h2' : dyadicSquareCount (Δ ^ k) A = S.encard := by rfl
  rw [h1', h2', h_main]
