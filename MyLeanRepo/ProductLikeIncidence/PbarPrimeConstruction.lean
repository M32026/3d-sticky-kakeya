module

/-
# Bi-Lipschitz Covering Number Comparison — Defect 3.6 Fix

Given a bi-Lipschitz map F, proves dyadic covering-number comparison
for any bounded set A:
  Nδ(F '' A) ≤ (4·C_U + 6)^2 · Nδ(A)
  Nδ(A) ≤ (4/C_L + 6)^2 · Nδ(F '' A)

Applies uniformly to Pbar, E3, and tube parameter sets P_y.

## Whiteprint node: defect_36_pbar_prime_construction
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Bornology ENNReal Finset

namespace Defect36

/-! ### Helpers -/

lemma abs_coord_le_norm (z : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    |z i| ≤ ‖z‖ := by
  have h6 : (z i) ^ 2 ≤ (z 0) ^ 2 + (z 1) ^ 2 := by
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
  have h7 : |z i| = Real.sqrt ((z i) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
  have h8 : ‖z‖ = Real.sqrt ((z 0) ^ 2 + (z 1) ^ 2) := by
    simpa [EuclideanSpace.norm_eq, Fin.sum_univ_two] using rfl
  rw [h7, h8]; apply Real.sqrt_le_sqrt; exact h6

lemma point_in_cubeContaining {δ : ℝ} (hδ : 0 < δ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ dyadicCube δ (fun i : Fin 2 => ⌊x i / δ⌋) := by
  intro i
  have h1 : (⌊x i / δ⌋ : ℝ) ≤ x i / δ := Int.floor_le (x i / δ)
  have h2 : x i / δ < (⌊x i / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one (x i / δ)
  have h3 : δ * (⌊x i / δ⌋ : ℝ) ≤ x i := by
    calc δ * (⌊x i / δ⌋ : ℝ) ≤ δ * (x i / δ) := by gcongr
      _ = x i := by field_simp [hδ.ne'] <;> ring
  have h4 : x i < δ * ((⌊x i / δ⌋ : ℝ) + 1) := by
    calc x i = δ * (x i / δ) := by field_simp [hδ.ne'] <;> ring
      _ < δ * ((⌊x i / δ⌋ : ℝ) + 1) := by gcongr
  exact ⟨h3, h4⟩

lemma cube_norm_spread {δ : ℝ} (hδ : 0 < δ) {k : Fin 2 → ℤ}
    {x y : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ dyadicCube δ k) (hy : y ∈ dyadicCube δ k) :
    ‖x - y‖ ≤ 2 * δ := by
  have h1 : ∀ i : Fin 2, |(x - y) i| ≤ δ := by
    intro i
    have hx1 : δ * (k i : ℝ) ≤ x i := (hx i).1
    have hx2 : x i < δ * ((k i : ℝ) + 1) := (hx i).2
    have hy1 : δ * (k i : ℝ) ≤ y i := (hy i).1
    have hy2 : y i < δ * ((k i : ℝ) + 1) := (hy i).2
    have h_eq : (x - y) i = x i - y i := by simp
    rw [h_eq, abs_le]
    constructor <;> linarith
  have h2 : |(x - y) 0| ≤ δ := h1 0
  have h3 : |(x - y) 1| ≤ δ := h1 1
  have h4 : ‖x - y‖ ^ 2 = ((x - y) 0) ^ 2 + ((x - y) 1) ^ 2 := by
    have h_norm : ∀ (z : EuclideanSpace ℝ (Fin 2)), ‖z‖ ^ 2 = (z 0) ^ 2 + (z 1) ^ 2 := by
      intro z
      have h : ‖z‖ = Real.sqrt ((z 0) ^ 2 + (z 1) ^ 2) := by
        simpa [EuclideanSpace.norm_eq, Fin.sum_univ_two] using rfl
      rw [h]; rw [Real.sq_sqrt] <;> positivity
    exact h_norm (x - y)
  have h_abs_sq : ∀ (r : ℝ), |r| ^ 2 = r ^ 2 := by intro r; simp [sq_abs]
  have h5 : ‖x - y‖ ^ 2 ≤ (|(x - y) 0| + |(x - y) 1|) ^ 2 := by
    rw [h4]
    have h_eq : (|(x - y) 0| + |(x - y) 1|) ^ 2 =
        ((x - y) 0) ^ 2 + ((x - y) 1) ^ 2 + 2 * (|(x - y) 0| * |(x - y) 1|) := by
      calc (|(x - y) 0| + |(x - y) 1|) ^ 2
        = |(x - y) 0| ^ 2 + |(x - y) 1| ^ 2 + 2 * (|(x - y) 0| * |(x - y) 1|) := by ring
      _ = ((x - y) 0) ^ 2 + |(x - y) 1| ^ 2 + 2 * (|(x - y) 0| * |(x - y) 1|) := by rw [h_abs_sq ((x - y) 0)]
      _ = ((x - y) 0) ^ 2 + ((x - y) 1) ^ 2 + 2 * (|(x - y) 0| * |(x - y) 1|) := by rw [h_abs_sq ((x - y) 1)]
    rw [h_eq] <;> nlinarith [abs_nonneg ((x - y) 0), abs_nonneg ((x - y) 1)]
  have h6 : 0 ≤ ‖x - y‖ := by positivity
  have h7 : 0 ≤ |(x - y) 0| + |(x - y) 1| := by positivity
  have h8 : ‖x - y‖ ≤ |(x - y) 0| + |(x - y) 1| := by
    nlinarith [h5, h6, h7]
  calc ‖x - y‖ ≤ |(x - y) 0| + |(x - y) 1| := h8
    _ ≤ δ + δ := by gcongr
    _ = 2 * δ := by ring

/-! ### Bounded square cube count -/

/-- Any δ-cube meeting a set S contained in [a,a+D]×[b,b+D] has grid indices
    within a bounded range, so the number of such cubes is ≤ (D/δ+6)^2. -/
lemma bounded_square_cube_count {δ D : ℝ} (hδ : 0 < δ) (hD : 0 ≤ D)
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {a b : ℝ} (hS1 : ∀ p ∈ S, a ≤ p 0) (hS2 : ∀ p ∈ S, p 0 ≤ a + D)
    (hS3 : ∀ p ∈ S, b ≤ p 1) (hS4 : ∀ p ∈ S, p 1 ≤ b + D) :
    (dyadicCubesMeeting δ S).Finite ∧
      ENat.toENNReal (dyadicCubesMeeting δ S).encard ≤
        ENNReal.ofReal ((D / δ + 6) ^ 2) := by
  let I_lo0 : ℤ := Int.floor (a / δ) - 2
  let I_hi0 : ℤ := Int.ceil ((a + D) / δ) + 1
  let I_lo1 : ℤ := Int.floor (b / δ) - 2
  let I_hi1 : ℤ := Int.ceil ((b + D) / δ) + 1
  let Idx0 := Finset.Icc I_lo0 I_hi0
  let Idx1 := Finset.Icc I_lo1 I_hi1
  let Idx : Finset (Fin 2 → ℤ) :=
    (Idx0.product Idx1).image (fun p : ℤ × ℤ => fun i => if i = 0 then p.1 else p.2)
  let Cubes : Finset (Set (EuclideanSpace ℝ (Fin 2))) :=
    Idx.image (fun k => dyadicCube δ k)
  have h1 : ∀ (k : Fin 2 → ℤ), dyadicCube δ k ∈ dyadicCubesMeeting δ S →
      k 0 ∈ Idx0 ∧ k 1 ∈ Idx1 := by
    intro k hk
    rcases hk with ⟨hQ_cube, ⟨p, hpQ, hpS⟩⟩
    have h_k0_hi : (k 0 : ℝ) ≤ (I_hi0 : ℝ) := by
      have h : δ * (k 0 : ℝ) ≤ p 0 := (hpQ 0).1
      have h2 : p 0 ≤ a + D := hS2 p hpS
      have h3 : δ * (k 0 : ℝ) ≤ a + D := by linarith
      have h4 : (k 0 : ℝ) ≤ (a + D) / δ := by
        calc (k 0 : ℝ) = (δ * (k 0 : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
          _ ≤ (a + D) / δ := by gcongr
      simp [I_hi0]; have hc : ((a + D) / δ) ≤ (Int.ceil ((a + D) / δ) : ℝ) := Int.le_ceil _
      linarith
    have h_k0_lo : (I_lo0 : ℝ) ≤ (k 0 : ℝ) := by
      have h : a < δ * ((k 0 : ℝ) + 1) := by linarith [hS1 p hpS, (hpQ 0).2]
      have h2 : a / δ < (k 0 : ℝ) + 1 := by
        calc a / δ < (δ * ((k 0 : ℝ) + 1)) / δ := by gcongr
          _ = (k 0 : ℝ) + 1 := by field_simp [hδ.ne'] <;> ring
      simp [I_lo0]; have hf : (Int.floor (a / δ) : ℝ) ≤ a / δ := Int.floor_le _
      linarith
    have h_k1_hi : (k 1 : ℝ) ≤ (I_hi1 : ℝ) := by
      have h : δ * (k 1 : ℝ) ≤ p 1 := (hpQ 1).1
      have h2 : p 1 ≤ b + D := hS4 p hpS
      have h3 : δ * (k 1 : ℝ) ≤ b + D := by linarith
      have h4 : (k 1 : ℝ) ≤ (b + D) / δ := by
        calc (k 1 : ℝ) = (δ * (k 1 : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
          _ ≤ (b + D) / δ := by gcongr
      simp [I_hi1]; have hc : ((b + D) / δ) ≤ (Int.ceil ((b + D) / δ) : ℝ) := Int.le_ceil _
      linarith
    have h_k1_lo : (I_lo1 : ℝ) ≤ (k 1 : ℝ) := by
      have h : b < δ * ((k 1 : ℝ) + 1) := by linarith [hS3 p hpS, (hpQ 1).2]
      have h2 : b / δ < (k 1 : ℝ) + 1 := by
        calc b / δ < (δ * ((k 1 : ℝ) + 1)) / δ := by gcongr
          _ = (k 1 : ℝ) + 1 := by field_simp [hδ.ne'] <;> ring
      simp [I_lo1]; have hf : (Int.floor (b / δ) : ℝ) ≤ b / δ := Int.floor_le _
      linarith
    have h_k0_lo' : I_lo0 ≤ k 0 := Int.cast_le.mp h_k0_lo
    have h_k0_hi' : k 0 ≤ I_hi0 := Int.cast_le.mp h_k0_hi
    have h_k1_lo' : I_lo1 ≤ k 1 := Int.cast_le.mp h_k1_lo
    have h_k1_hi' : k 1 ≤ I_hi1 := Int.cast_le.mp h_k1_hi
    exact ⟨Finset.mem_Icc.mpr ⟨h_k0_lo', h_k0_hi'⟩, Finset.mem_Icc.mpr ⟨h_k1_lo', h_k1_hi'⟩⟩
  have h_sub : dyadicCubesMeeting δ S ⊆ (Cubes : Set (Set (EuclideanSpace ℝ (Fin 2)))) := by
    intro Q hQ
    have hQ_cube : Q ∈ dyadicCubes 2 δ := hQ.1
    rcases hQ_cube with ⟨k, rfl⟩
    have h_bounds := h1 k hQ
    have h_pair : (k 0, k 1) ∈ Idx0.product Idx1 := by
      exact Finset.mem_product.mpr h_bounds
    have h_k_in_Idx : k ∈ Idx := by
      have h_img : (fun i : Fin 2 => if i = 0 then k 0 else k 1) ∈ Idx :=
        Finset.mem_image_of_mem _ h_pair
      have h_eq : (fun i : Fin 2 => if i = 0 then k 0 else k 1) = k := by
        funext i
        fin_cases i <;> simp
      rw [h_eq] at h_img
      exact h_img
    exact Finset.mem_image.mpr ⟨k, h_k_in_Idx, rfl⟩
  have h_fin : (dyadicCubesMeeting δ S).Finite :=
    Set.Finite.subset (Finset.finite_toSet Cubes) h_sub
  have h_card0 : ENat.toENNReal (dyadicCubesMeeting δ S).encard ≤
      (↑Cubes.card : ENNReal) := by
    exact_mod_cast Set.encard_mono h_sub
  have h_Cubes_le_Idx : Cubes.card ≤ Idx.card := Finset.card_image_le
  have h_product_card : (Idx0.product Idx1).card = Idx0.card * Idx1.card := by
    simp [Finset.card_product]
  have h_Idx_card : Idx.card ≤ Idx0.card * Idx1.card := by
    calc Idx.card ≤ (Idx0.product Idx1).card := Finset.card_image_le
      _ = Idx0.card * Idx1.card := h_product_card
  have h_lo_le_hi0 : I_lo0 ≤ I_hi0 := by
    have h_a_le : a ≤ a + D := by linarith [hD]
    have h1 : (Int.floor (a / δ) : ℝ) ≤ (Int.ceil ((a + D) / δ) : ℝ) := by
      have h2 : (Int.floor (a / δ) : ℝ) ≤ a / δ := Int.floor_le _
      have h3 : a / δ ≤ (a + D) / δ := by
        apply div_le_div_of_nonneg_right h_a_le hδ.le
      have h4 : (a + D) / δ ≤ (Int.ceil ((a + D) / δ) : ℝ) := Int.le_ceil _
      linarith
    have h_i_lo : (I_lo0 : ℝ) = (Int.floor (a / δ) : ℝ) - 2 := by
      simp [I_lo0] <;> norm_cast
    have h_i_hi : (I_hi0 : ℝ) = (Int.ceil ((a + D) / δ) : ℝ) + 1 := by
      simp [I_hi0] <;> norm_cast
    have h5 : (I_lo0 : ℝ) ≤ (I_hi0 : ℝ) := by
      rw [h_i_lo, h_i_hi] <;> linarith
    exact_mod_cast h5
  have h_lo_le_hi1 : I_lo1 ≤ I_hi1 := by
    have h_b_le : b ≤ b + D := by linarith [hD]
    have h1 : (Int.floor (b / δ) : ℝ) ≤ (Int.ceil ((b + D) / δ) : ℝ) := by
      have h2 : (Int.floor (b / δ) : ℝ) ≤ b / δ := Int.floor_le _
      have h3 : b / δ ≤ (b + D) / δ := by
        apply div_le_div_of_nonneg_right h_b_le hδ.le
      have h4 : (b + D) / δ ≤ (Int.ceil ((b + D) / δ) : ℝ) := Int.le_ceil _
      linarith
    have h_i_lo : (I_lo1 : ℝ) = (Int.floor (b / δ) : ℝ) - 2 := by
      simp [I_lo1] <;> norm_cast
    have h_i_hi : (I_hi1 : ℝ) = (Int.ceil ((b + D) / δ) : ℝ) + 1 := by
      simp [I_hi1] <;> norm_cast
    have h5 : (I_lo1 : ℝ) ≤ (I_hi1 : ℝ) := by
      rw [h_i_lo, h_i_hi] <;> linarith
    exact_mod_cast h5
  have h_card_Icc : ∀ (a b : ℤ), a ≤ b → ((Finset.Icc a b).card : ℝ) ≤ (b - a + 1 : ℝ) := by
    intro a b h
    have h' : a ≤ b + 1 := by linarith
    have h_int : (↑(Finset.Icc a b).card : ℤ) = b + 1 - a := Int.card_Icc_of_le a b h'
    have h'' : ((Finset.Icc a b).card : ℝ) = ↑(b + 1 - a : ℤ) := by
      exact_mod_cast h_int
    rw [h''] <;> norm_cast <;> linarith
  let K_real := D / δ + 6
  have hK_nonneg : 0 ≤ K_real := by positivity
  let K_nat := Nat.floor K_real
  have hK_le : (K_nat : ℝ) ≤ K_real := Nat.floor_le hK_nonneg
  have h_range0 : (I_hi0 - I_lo0 + 1 : ℝ) < D / δ + 6 := by
    have h1 : (Int.ceil ((a + D) / δ) : ℝ) < (a + D) / δ + 1 := Int.ceil_lt_add_one _
    have h2 : (Int.floor (a / δ) : ℝ) > a / δ - 1 := by
      have h2' : a / δ < (Int.floor (a / δ) : ℝ) + 1 := Int.lt_floor_add_one _
      linarith
    have h_i_hi : (I_hi0 : ℝ) = (Int.ceil ((a + D) / δ) : ℝ) + 1 := by
      simp [I_hi0] <;> norm_cast
    have h_i_lo : (I_lo0 : ℝ) = (Int.floor (a / δ) : ℝ) - 2 := by
      simp [I_lo0] <;> norm_cast
    have h3 : (I_hi0 - I_lo0 + 1 : ℝ) =
        (Int.ceil ((a + D) / δ) : ℝ) - (Int.floor (a / δ) : ℝ) + 4 := by
      rw [h_i_hi, h_i_lo] <;> ring
    rw [h3]
    have h4 : (Int.ceil ((a + D) / δ) : ℝ) - (Int.floor (a / δ) : ℝ) < D / δ + 2 := by
      have h5 : (Int.ceil ((a + D) / δ) : ℝ) - (Int.floor (a / δ) : ℝ) <
          (a + D) / δ + 1 - (a / δ - 1) := by linarith
      have h6 : (a + D) / δ + 1 - (a / δ - 1) = D / δ + 2 := by
        field_simp [hδ.ne'] <;> ring
      rw [h6] at h5
      exact h5
    linarith
  have h_range1 : (I_hi1 - I_lo1 + 1 : ℝ) < D / δ + 6 := by
    have h1 : (Int.ceil ((b + D) / δ) : ℝ) < (b + D) / δ + 1 := Int.ceil_lt_add_one _
    have h2 : (Int.floor (b / δ) : ℝ) > b / δ - 1 := by
      have h2' : b / δ < (Int.floor (b / δ) : ℝ) + 1 := Int.lt_floor_add_one _
      linarith
    have h_i_hi : (I_hi1 : ℝ) = (Int.ceil ((b + D) / δ) : ℝ) + 1 := by
      simp [I_hi1] <;> norm_cast
    have h_i_lo : (I_lo1 : ℝ) = (Int.floor (b / δ) : ℝ) - 2 := by
      simp [I_lo1] <;> norm_cast
    have h3 : (I_hi1 - I_lo1 + 1 : ℝ) =
        (Int.ceil ((b + D) / δ) : ℝ) - (Int.floor (b / δ) : ℝ) + 4 := by
      rw [h_i_hi, h_i_lo] <;> ring
    rw [h3]
    have h4 : (Int.ceil ((b + D) / δ) : ℝ) - (Int.floor (b / δ) : ℝ) < D / δ + 2 := by
      have h5 : (Int.ceil ((b + D) / δ) : ℝ) - (Int.floor (b / δ) : ℝ) <
          (b + D) / δ + 1 - (b / δ - 1) := by linarith
      have h6 : (b + D) / δ + 1 - (b / δ - 1) = D / δ + 2 := by
        field_simp [hδ.ne'] <;> ring
      rw [h6] at h5
      exact h5
    linarith
  have h_card0' : (Idx0.card : ℝ) ≤ K_real := by
    have h : (Idx0.card : ℝ) ≤ (I_hi0 - I_lo0 + 1 : ℝ) := h_card_Icc I_lo0 I_hi0 h_lo_le_hi0
    have h4 : (I_hi0 - I_lo0 + 1 : ℝ) < K_real := by simpa [K_real] using h_range0
    linarith
  have h_card1' : (Idx1.card : ℝ) ≤ K_real := by
    have h : (Idx1.card : ℝ) ≤ (I_hi1 - I_lo1 + 1 : ℝ) := h_card_Icc I_lo1 I_hi1 h_lo_le_hi1
    have h4 : (I_hi1 - I_lo1 + 1 : ℝ) < K_real := by simpa [K_real] using h_range1
    linarith
  have h : (Cubes.card : ℝ) ≤ K_real ^ 2 := by
    have h6 : (Cubes.card : ℝ) ≤ (Idx.card : ℝ) := by exact_mod_cast h_Cubes_le_Idx
    have h7 : (Idx.card : ℝ) ≤ (Idx0.card : ℝ) * (Idx1.card : ℝ) := by exact_mod_cast h_Idx_card
    calc (Cubes.card : ℝ)
      ≤ (Idx.card : ℝ) := h6
    _ ≤ (Idx0.card : ℝ) * (Idx1.card : ℝ) := h7
    _ ≤ K_real * K_real := by gcongr
    _ = K_real ^ 2 := by ring
  have h_Idx_card2 : (↑Cubes.card : ENNReal) ≤ ENNReal.ofReal ((D / δ + 6) ^ 2) := by
    have h9 : (Cubes.card : ℝ) ≤ (D / δ + 6) ^ 2 := by simpa [K_real] using h
    have h10 : ENNReal.ofReal (Cubes.card : ℝ) ≤ ENNReal.ofReal ((D / δ + 6) ^ 2) := ENNReal.ofReal_le_ofReal h9
    have h11 : (↑Cubes.card : ENNReal) = ENNReal.ofReal (Cubes.card : ℝ) := by simp
    rw [h11]; exact h10
  exact ⟨h_fin, le_trans h_card0 h_Idx_card2⟩

lemma finite_dyadicCubesMeeting_bounded {δ : ℝ} (hδ : 0 < δ)
    {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA_bdd : Bornology.IsBounded A) :
    (dyadicCubesMeeting δ A).Finite := by
  have h2 : ∃ (R : ℝ), ∀ p ∈ A, ‖p‖ ≤ R := isBounded_iff_forall_norm_le.mp hA_bdd
  rcases h2 with ⟨R, hR⟩
  let C := max R 0
  have hC1 : ∀ p ∈ A, -C ≤ p 0 := by
    intro p hp
    have h3 : ‖p‖ ≤ R := hR p hp
    have h4 : |p 0| ≤ ‖p‖ := abs_coord_le_norm p 0
    have h51 : |p 0| ≤ ‖p‖ := h4
    have h52 : ‖p‖ ≤ R := h3
    have h53 : R ≤ C := le_max_left R 0
    have h5 : |p 0| ≤ C := le_trans h51 (le_trans h52 h53)
    linarith [abs_le.mp h5]
  have hC2 : ∀ p ∈ A, p 0 ≤ C := by
    intro p hp
    have h3 : ‖p‖ ≤ R := hR p hp
    have h4 : |p 0| ≤ ‖p‖ := abs_coord_le_norm p 0
    have h51 : |p 0| ≤ ‖p‖ := h4
    have h52 : ‖p‖ ≤ R := h3
    have h53 : R ≤ C := le_max_left R 0
    have h5 : |p 0| ≤ C := le_trans h51 (le_trans h52 h53)
    linarith [abs_le.mp h5]
  have hC3 : ∀ p ∈ A, -C ≤ p 1 := by
    intro p hp
    have h3 : ‖p‖ ≤ R := hR p hp
    have h4 : |p 1| ≤ ‖p‖ := abs_coord_le_norm p 1
    have h51 : |p 1| ≤ ‖p‖ := h4
    have h52 : ‖p‖ ≤ R := h3
    have h53 : R ≤ C := le_max_left R 0
    have h5 : |p 1| ≤ C := le_trans h51 (le_trans h52 h53)
    linarith [abs_le.mp h5]
  have hC4 : ∀ p ∈ A, p 1 ≤ C := by
    intro p hp
    have h3 : ‖p‖ ≤ R := hR p hp
    have h4 : |p 1| ≤ ‖p‖ := abs_coord_le_norm p 1
    have h51 : |p 1| ≤ ‖p‖ := h4
    have h52 : ‖p‖ ≤ R := h3
    have h53 : R ≤ C := le_max_left R 0
    have h5 : |p 1| ≤ C := le_trans h51 (le_trans h52 h53)
    linarith [abs_le.mp h5]
  have hC_nonneg : 0 ≤ C := le_max_right R 0
  have hC2' : ∀ p ∈ A, p 0 ≤ -C + 2 * C := by
    intro p hp
    have h : p 0 ≤ C := hC2 p hp
    have h' : -C + 2 * C = C := by ring
    rw [h']
    exact h
  have hC4' : ∀ p ∈ A, p 1 ≤ -C + 2 * C := by
    intro p hp
    have h : p 1 ≤ C := hC4 p hp
    have h' : -C + 2 * C = C := by ring
    rw [h']
    exact h
  exact (bounded_square_cube_count (D := 2 * C) hδ (by linarith [hC_nonneg]) hC1 hC2' hC3 hC4').1

lemma lipschitz_image_bounded {C_U : ℝ} (hC_U : 0 ≤ C_U)
    {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hF_upper : ∀ x y, ‖F x - F y‖ ≤ C_U * ‖x - y‖)
    {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA_bdd : Bornology.IsBounded A) :
    Bornology.IsBounded (F '' A) := by
  have h2 : ∃ (R : ℝ), ∀ p ∈ A, ‖p‖ ≤ R := isBounded_iff_forall_norm_le.mp hA_bdd
  rcases h2 with ⟨R, hR⟩
  let C := max R 0
  have h3 : ∀ q ∈ F '' A, ‖q‖ ≤ ‖F 0‖ + C_U * C := by
    intro q hq
    rcases hq with ⟨p, hp, rfl⟩
    have h4 : ‖p‖ ≤ C := by
      have h5 : ‖p‖ ≤ R := hR p hp
      have h6 : R ≤ C := le_max_left R 0
      linarith
    have h5 : ‖F p - F 0‖ ≤ C_U * ‖p‖ := by simpa using hF_upper p 0
    have h_eq : F p = F 0 + (F p - F 0) := by abel
    rw [h_eq]
    calc ‖F 0 + (F p - F 0)‖
      ≤ ‖F 0‖ + ‖F p - F 0‖ := norm_add_le _ _
    _ ≤ ‖F 0‖ + C_U * ‖p‖ := by gcongr
    _ ≤ ‖F 0‖ + C_U * C := by gcongr
  exact isBounded_iff_forall_norm_le.mpr ⟨‖F 0‖ + C_U * C, h3⟩

/-! ### ENNReal helper -/

lemma finset_card_le_of_ennreal_bound {s : Finset (Set (EuclideanSpace ℝ (Fin 2)))}
    {K_real : ℝ} (hK_nonneg : 0 ≤ K_real)
    (h : ENat.toENNReal (↑s.card : ℕ∞) ≤ ENNReal.ofReal K_real) :
    s.card ≤ Nat.floor K_real := by
  have h1 : (↑s.card : ENNReal) ≤ ENNReal.ofReal K_real := by simpa using h
  have h2 : ENNReal.ofReal (s.card : ℝ) ≤ ENNReal.ofReal K_real := by
    have h3 : (↑s.card : ENNReal) = ENNReal.ofReal (s.card : ℝ) := by simp
    rw [h3] at h1; exact h1
  have h4 : (s.card : ℝ) ≤ K_real := by exact (ofReal_le_ofReal_iff hK_nonneg).mp h2
  have h5 : s.card ≤ Nat.floor K_real := by exact (Nat.le_floor_iff hK_nonneg).mpr h4
  exact h5

/-! ### Fiber counting -/

lemma finset_biUnion_card_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    {sA : Finset β} {K : ℕ}
    (f : β → Finset α) (h_bound : ∀ y ∈ sA, (f y).card ≤ K)
    {sF : Finset α} (h_sub : sF ⊆ Finset.biUnion sA f) :
    sF.card ≤ K * sA.card := by
  have h1 : (Finset.biUnion sA f).card ≤ ∑ y ∈ sA, (f y).card := by
    exact card_biUnion_le
  have h2 : ∑ y ∈ sA, (f y).card ≤ ∑ y ∈ sA, K := by gcongr <;> exact h_bound y ‹_›
  have h3 : ∑ y ∈ sA, K = K * sA.card := by
    simp [Finset.sum_const, mul_comm]
  calc sF.card
    ≤ (Finset.biUnion sA f).card := Finset.card_le_card h_sub
    _ ≤ ∑ y ∈ sA, (f y).card := h1
    _ ≤ ∑ y ∈ sA, K := h2
    _ = K * sA.card := h3

/-! ### Image of cube in square helper -/

/-- The Lipschitz image of a δ-cube is contained in a square of side 4·C_U·δ. -/
lemma image_cube_in_square {δ C_U : ℝ} (hδ : 0 < δ) (hC_U : 0 ≤ C_U)
    {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hF_upper : ∀ x y, ‖F x - F y‖ ≤ C_U * ‖x - y‖)
    {Q : Set (EuclideanSpace ℝ (Fin 2))} (hQ_cube : Q ∈ dyadicCubes 2 δ)
    {p0 : EuclideanSpace ℝ (Fin 2)} (hp0Q : p0 ∈ Q) :
    ∃ (a b D : ℝ), D = 4 * C_U * δ ∧ 0 ≤ D ∧
      (∀ q ∈ F '' Q, a ≤ q 0) ∧ (∀ q ∈ F '' Q, q 0 ≤ a + D) ∧
      (∀ q ∈ F '' Q, b ≤ q 1) ∧ (∀ q ∈ F '' Q, q 1 ≤ b + D) := by
  rcases hQ_cube with ⟨k, hk⟩
  let a := (F p0) 0 - C_U * 2 * δ
  let b := (F p0) 1 - C_U * 2 * δ
  let D := 4 * C_U * δ
  have hD_nonneg : 0 ≤ D := by positivity
  have h_bound : ∀ (x : EuclideanSpace ℝ (Fin 2)), x ∈ Q →
      |(F x) 0 - (F p0) 0| ≤ C_U * 2 * δ ∧ |(F x) 1 - (F p0) 1| ≤ C_U * 2 * δ := by
    intro x hxQ
    have hxQ' : x ∈ dyadicCube δ k := by rw [hk] at hxQ; exact hxQ
    have hp0Q' : p0 ∈ dyadicCube δ k := by rw [hk] at hp0Q; exact hp0Q
    have h_dist : ‖x - p0‖ ≤ 2 * δ := cube_norm_spread hδ hxQ' hp0Q'
    have h : ‖F x - F p0‖ ≤ C_U * 2 * δ := by
      have h1 : ‖F x - F p0‖ ≤ C_U * ‖x - p0‖ := hF_upper x p0
      have h2 : C_U * ‖x - p0‖ ≤ C_U * (2 * δ) := mul_le_mul_of_nonneg_left h_dist hC_U
      linarith
    have h0 : |(F x) 0 - (F p0) 0| ≤ ‖F x - F p0‖ := abs_coord_le_norm (F x - F p0) 0
    have h1 : |(F x) 1 - (F p0) 1| ≤ ‖F x - F p0‖ := abs_coord_le_norm (F x - F p0) 1
    exact ⟨by linarith, by linarith⟩
  have hS1 : ∀ q ∈ F '' Q, a ≤ q 0 := by
    intro q hq
    rcases hq with ⟨x, hxQ, rfl⟩
    have h' := (h_bound x hxQ).1
    have h'' : (F p0) 0 - C_U * 2 * δ ≤ (F x) 0 := by linarith [abs_le.mp h']
    have h_goal : a ≤ (F x) 0 := by
      have h_eq : a = (F p0) 0 - C_U * 2 * δ := by rfl
      rw [h_eq]; exact h''
    exact h_goal
  have hS2 : ∀ q ∈ F '' Q, q 0 ≤ a + D := by
    intro q hq
    rcases hq with ⟨x, hxQ, rfl⟩
    have h' := (h_bound x hxQ).1
    have h'' : (F x) 0 ≤ (F p0) 0 + C_U * 2 * δ := by linarith [abs_le.mp h']
    have h_eq : a + D = (F p0) 0 + C_U * 2 * δ := by
      simp only [a, D] <;> ring
    rw [h_eq]; exact h''
  have hS3 : ∀ q ∈ F '' Q, b ≤ q 1 := by
    intro q hq
    rcases hq with ⟨x, hxQ, rfl⟩
    have h' := (h_bound x hxQ).2
    have h'' : (F p0) 1 - C_U * 2 * δ ≤ (F x) 1 := by linarith [abs_le.mp h']
    have h_goal : b ≤ (F x) 1 := by
      have h_eq : b = (F p0) 1 - C_U * 2 * δ := by rfl
      rw [h_eq]; exact h''
    exact h_goal
  have hS4 : ∀ q ∈ F '' Q, q 1 ≤ b + D := by
    intro q hq
    rcases hq with ⟨x, hxQ, rfl⟩
    have h' := (h_bound x hxQ).2
    have h'' : (F x) 1 ≤ (F p0) 1 + C_U * 2 * δ := by linarith [abs_le.mp h']
    have h_eq : b + D = (F p0) 1 + C_U * 2 * δ := by
      simp only [b, D] <;> ring
    rw [h_eq]; exact h''
  exact ⟨a, b, D, rfl, hD_nonneg, hS1, hS2, hS3, hS4⟩

/-! ### Forward covering bound -/

/-- Forward: Nδ(F '' A) ≤ (4·C_U + 6)^2 · Nδ(A). -/
lemma lipschitz_covering_upper {δ C_U : ℝ} (hδ : 0 < δ) (hC_U : 0 ≤ C_U)
    {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hF_upper : ∀ x y, ‖F x - F y‖ ≤ C_U * ‖x - y‖)
    {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA_bdd : Bornology.IsBounded A) :
    ENat.toENNReal (dyadicCoveringNumber δ (F '' A)) ≤
      ENNReal.ofReal ((4 * C_U + 6) ^ 2) *
        ENat.toENNReal (dyadicCoveringNumber δ A) := by
  let K_real := (4 * C_U + 6) ^ 2
  have hK_nonneg : 0 ≤ K_real := by positivity
  let K := Nat.floor K_real
  have hK_le : (K : ℝ) ≤ K_real := Nat.floor_le hK_nonneg
  have hA_fin : (dyadicCubesMeeting δ A).Finite :=
    finite_dyadicCubesMeeting_bounded hδ hA_bdd
  have hFA_bdd : Bornology.IsBounded (F '' A) :=
    lipschitz_image_bounded hC_U hF_upper hA_bdd
  have hFA_fin : (dyadicCubesMeeting δ (F '' A)).Finite :=
    finite_dyadicCubesMeeting_bounded hδ hFA_bdd
  let sA := hA_fin.toFinset
  let sFA := hFA_fin.toFinset
  classical
  let cubeOfPoint := fun (x : EuclideanSpace ℝ (Fin 2)) =>
    dyadicCube δ (fun i : Fin 2 => ⌊x i / δ⌋)
  have h_exists : ∀ (Q : Set (EuclideanSpace ℝ (Fin 2))), Q ∈ sA →
      ∃ (s : Finset (Set (EuclideanSpace ℝ (Fin 2)))),
        (s : Set (Set (EuclideanSpace ℝ (Fin 2)))) = dyadicCubesMeeting δ (F '' Q) ∧
        s.card ≤ K := by
    intro Q hQ
    have hQ' : Q ∈ dyadicCubesMeeting δ A := by
      have h : (sA : Set _) = dyadicCubesMeeting δ A := hA_fin.coe_toFinset
      rw [← h]; exact hQ
    have h_nonempty : (Q ∩ A).Nonempty := hQ'.2
    let p0 : EuclideanSpace ℝ (Fin 2) := Classical.choose h_nonempty
    have hp0Q : p0 ∈ Q := (Classical.choose_spec h_nonempty).1
    have hQ_cube : Q ∈ dyadicCubes 2 δ := hQ'.1
    rcases image_cube_in_square hδ hC_U hF_upper hQ_cube hp0Q with
      ⟨a, b, D, hD_eq, hD_nonneg, hS1, hS2, hS3, hS4⟩
    have hK_eq : (D / δ + 6) ^ 2 = K_real := by
      rw [hD_eq]; field_simp [hδ.ne'] <;> ring
    let h_main := bounded_square_cube_count hδ hD_nonneg hS1 hS2 hS3 hS4
    let s := h_main.1.toFinset
    have hs_eq : (s : Set (Set (EuclideanSpace ℝ (Fin 2)))) = dyadicCubesMeeting δ (F '' Q) := by
      exact h_main.1.coe_toFinset
    have h_encard_eq : (↑s.card : ℕ∞) = (dyadicCubesMeeting δ (F '' Q)).encard := by
      have h2 : (dyadicCubesMeeting δ (F '' Q)).encard = ((s : Set (Set (EuclideanSpace ℝ (Fin 2))))).encard := by rw [hs_eq]
      rw [h2]
      exact Eq.symm (encard_coe_eq_coe_finsetCard s)
    have h_bound : ENat.toENNReal (↑s.card : ℕ∞) ≤ ENNReal.ofReal K_real := by
      have h3 : ENat.toENNReal (dyadicCubesMeeting δ (F '' Q)).encard ≤ ENNReal.ofReal ((D / δ + 6) ^ 2) := h_main.2
      have h4 : ENNReal.ofReal ((D / δ + 6) ^ 2) = ENNReal.ofReal K_real := by rw [hK_eq]
      rw [h4] at h3
      rw [h_encard_eq]
      exact h3
    have h_card : s.card ≤ K := finset_card_le_of_ennreal_bound hK_nonneg h_bound
    exact ⟨s, hs_eq, h_card⟩
  let cubesForQ (Q : Set (EuclideanSpace ℝ (Fin 2))) : Finset (Set (EuclideanSpace ℝ (Fin 2))) :=
    if hQ : Q ∈ sA then Classical.choose (h_exists Q hQ) else ∅
  have h_cubesForQ_spec : ∀ (Q : Set (EuclideanSpace ℝ (Fin 2))) (hQ : Q ∈ sA),
      (cubesForQ Q : Set (Set (EuclideanSpace ℝ (Fin 2)))) = dyadicCubesMeeting δ (F '' Q) ∧
      (cubesForQ Q).card ≤ K := by
    intro Q hQ
    have h : cubesForQ Q = Classical.choose (h_exists Q hQ) := by
      simp [cubesForQ, hQ]
    rw [h]
    exact Classical.choose_spec (h_exists Q hQ)
  have h_sub : sFA ⊆ Finset.biUnion sA cubesForQ := by
    intro R hR
    have hR' : R ∈ dyadicCubesMeeting δ (F '' A) := by
      have h : (sFA : Set _) = dyadicCubesMeeting δ (F '' A) := hFA_fin.coe_toFinset
      rw [← h]; exact hR
    rcases hR' with ⟨hR_cube, ⟨y, hyR, hyFA⟩⟩
    rcases hyFA with ⟨x, hxA, h_y_eq⟩
    let Q := cubeOfPoint x
    have hQ_cube : Q ∈ dyadicCubes 2 δ := ⟨_, rfl⟩
    have hQ_meet : (Q ∩ A).Nonempty := ⟨x, point_in_cubeContaining hδ x, hxA⟩
    have hQ_in : Q ∈ dyadicCubesMeeting δ A := ⟨hQ_cube, hQ_meet⟩
    have hQ_sA : Q ∈ sA := by
      simpa [sA, Set.Finite.mem_toFinset] using hQ_in
    have hR_in : R ∈ cubesForQ Q := by
      have h_spec : (cubesForQ Q : Set _) = dyadicCubesMeeting δ (F '' Q) :=
        (h_cubesForQ_spec Q hQ_sA).1
      have h_y_in_FQ : y ∈ F '' Q := by
        exact ⟨x, point_in_cubeContaining hδ x, h_y_eq⟩
      have hR'' : R ∈ dyadicCubesMeeting δ (F '' Q) := by
        have h_meet : (R ∩ F '' Q).Nonempty := ⟨y, hyR, h_y_in_FQ⟩
        exact ⟨hR_cube, h_meet⟩
      have h_goal : R ∈ (cubesForQ Q : Set _) := by
        rw [h_spec]; exact hR''
      exact h_goal
    exact Finset.mem_biUnion.mpr ⟨Q, hQ_sA, hR_in⟩
  have h_cubesForQ_bound : ∀ Q ∈ sA, (cubesForQ Q).card ≤ K :=
    fun Q hQ => (h_cubesForQ_spec Q hQ).2
  have h_count : sFA.card ≤ K * sA.card :=
    finset_biUnion_card_bound cubesForQ h_cubesForQ_bound h_sub
  have h_coeFA : (sFA : Set (Set (EuclideanSpace ℝ (Fin 2)))) = dyadicCubesMeeting δ (F '' A) :=
    hFA_fin.coe_toFinset
  have h_coeA : (sA : Set (Set (EuclideanSpace ℝ (Fin 2)))) = dyadicCubesMeeting δ A :=
    hA_fin.coe_toFinset
  have h_encardFA : (dyadicCubesMeeting δ (F '' A)).encard = ↑sFA.card := by
    have h : (dyadicCubesMeeting δ (F '' A)).encard = ↑(hFA_fin.toFinset.card) := by exact Finite.encard_eq_coe_toFinset_card hFA_fin
    simpa [sFA] using h
  have h_encardA : (dyadicCubesMeeting δ A).encard = ↑sA.card := by
    have h : (dyadicCubesMeeting δ A).encard = ↑(hA_fin.toFinset.card) := by exact Finite.encard_eq_coe_toFinset_card hA_fin
    simpa [sA] using h
  have h1 : ENat.toENNReal (dyadicCoveringNumber δ (F '' A)) = (↑sFA.card : ENNReal) := by
    simp [dyadicCoveringNumber, h_encardFA]
  have h2 : ENat.toENNReal (dyadicCoveringNumber δ A) = (↑sA.card : ENNReal) := by
    simp [dyadicCoveringNumber, h_encardA]
  rw [h1, h2]
  have h3 : (↑sFA.card : ENNReal) ≤ (↑K : ENNReal) * (↑sA.card : ENNReal) := by
    exact_mod_cast h_count
  have h4 : (↑K : ENNReal) ≤ ENNReal.ofReal K_real := by
    have h5 : (K : ℝ) ≤ K_real := hK_le
    have h6 : ENNReal.ofReal (K : ℝ) ≤ ENNReal.ofReal K_real := ENNReal.ofReal_le_ofReal h5
    have h7 : (↑K : ENNReal) = ENNReal.ofReal (K : ℝ) := by simp
    rw [h7]; exact h6
  calc (↑sFA.card : ENNReal)
    ≤ (↑K : ENNReal) * (↑sA.card : ENNReal) := h3
    _ ≤ ENNReal.ofReal K_real * (↑sA.card : ENNReal) := by gcongr <;> exact h4

/-! ### Backward covering bound -/

/-- Backward: Nδ(A) ≤ (4/C_L + 6)^2 · Nδ(F '' A). -/
lemma colipschitz_covering_lower {δ C_L C_U : ℝ} (hδ : 0 < δ) (hC_L : 0 < C_L) (hC_U_nonneg : 0 ≤ C_U)
    {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hF_lower : ∀ x y, C_L * ‖x - y‖ ≤ ‖F x - F y‖)
    (hF_upper : ∀ x y, ‖F x - F y‖ ≤ C_U * ‖x - y‖)
    {A : Set (EuclideanSpace ℝ (Fin 2))}
    (hA_bdd : Bornology.IsBounded A) :
    ENat.toENNReal (dyadicCoveringNumber δ A) ≤
      ENNReal.ofReal ((4 / C_L + 6) ^ 2) *
        ENat.toENNReal (dyadicCoveringNumber δ (F '' A)) := by
  let K_real := (4 / C_L + 6) ^ 2
  have hK_nonneg : 0 ≤ K_real := by positivity
  let K := Nat.floor K_real
  have hK_le : (K : ℝ) ≤ K_real := Nat.floor_le hK_nonneg
  have hA_fin : (dyadicCubesMeeting δ A).Finite :=
    finite_dyadicCubesMeeting_bounded hδ hA_bdd
  have hFA_bdd : Bornology.IsBounded (F '' A) :=
    lipschitz_image_bounded hC_U_nonneg hF_upper hA_bdd
  have hFA_fin : (dyadicCubesMeeting δ (F '' A)).Finite :=
    finite_dyadicCubesMeeting_bounded hδ hFA_bdd
  let sA := hA_fin.toFinset
  let sFA := hFA_fin.toFinset
  classical
  let cubeOfPoint := fun (x : EuclideanSpace ℝ (Fin 2)) =>
    dyadicCube δ (fun i : Fin 2 => ⌊x i / δ⌋)
  let pointForR (R : Set (EuclideanSpace ℝ (Fin 2))) : EuclideanSpace ℝ (Fin 2) :=
    if h : R ∈ sFA then
      have hR' : R ∈ dyadicCubesMeeting δ (F '' A) := by
        simpa [sFA, Set.Finite.mem_toFinset] using h
      Classical.choose hR'.2
    else 0
  have h_pointForR_prop : ∀ (R : Set (EuclideanSpace ℝ (Fin 2))) (hR : R ∈ sFA),
      (pointForR R) ∈ R ∧ (pointForR R) ∈ F '' A := by
    intro R hR
    have hR' : R ∈ dyadicCubesMeeting δ (F '' A) := by
      simpa [sFA, Set.Finite.mem_toFinset] using hR
    have h_nonempty : (R ∩ F '' A).Nonempty := hR'.2
    simp [pointForR, hR]
    exact Classical.choose_spec h_nonempty
  let xForR (R : Set (EuclideanSpace ℝ (Fin 2))) : EuclideanSpace ℝ (Fin 2) :=
    if h : R ∈ sFA then
      Classical.choose ((h_pointForR_prop R h).2)
    else 0
  have h_xForR_prop : ∀ (R : Set (EuclideanSpace ℝ (Fin 2))) (hR : R ∈ sFA),
      F (xForR R) = pointForR R ∧ xForR R ∈ A := by
    intro R hR
    have h_def : xForR R = Classical.choose ((h_pointForR_prop R hR).2) := by
      simp [xForR, hR]
    have h_spec := Classical.choose_spec ((h_pointForR_prop R hR).2)
    rw [h_def]
    exact ⟨h_spec.2, h_spec.1⟩
  let halfSide := 2 * δ / C_L
  let D := 2 * halfSide
  let squareFor (center : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
    {p | |p 0 - center 0| ≤ halfSide ∧ |p 1 - center 1| ≤ halfSide}
  have hD_nonneg : 0 ≤ D := by positivity
  have hS1 : ∀ (center : EuclideanSpace ℝ (Fin 2)), ∀ p ∈ squareFor center, center 0 - halfSide ≤ p 0 := by
    intro center p hp; have h' : |p 0 - center 0| ≤ halfSide := hp.1
    have h'' : -halfSide ≤ p 0 - center 0 := (abs_le.mp h').1; linarith
  have hS2 : ∀ (center : EuclideanSpace ℝ (Fin 2)), ∀ p ∈ squareFor center, p 0 ≤ center 0 - halfSide + D := by
    intro center p hp; have h' : |p 0 - center 0| ≤ halfSide := hp.1
    have h'' : p 0 - center 0 ≤ halfSide := (abs_le.mp h').2; linarith
  have hS3 : ∀ (center : EuclideanSpace ℝ (Fin 2)), ∀ p ∈ squareFor center, center 1 - halfSide ≤ p 1 := by
    intro center p hp; have h' : |p 1 - center 1| ≤ halfSide := hp.2
    have h'' : -halfSide ≤ p 1 - center 1 := (abs_le.mp h').1; linarith
  have hS4 : ∀ (center : EuclideanSpace ℝ (Fin 2)), ∀ p ∈ squareFor center, p 1 ≤ center 1 - halfSide + D := by
    intro center p hp; have h' : |p 1 - center 1| ≤ halfSide := hp.2
    have h'' : p 1 - center 1 ≤ halfSide := (abs_le.mp h').2; linarith
  have hK_eq : (D / δ + 6) ^ 2 = K_real := by
    simp [D, halfSide, K_real] <;> field_simp [hC_L.ne'] <;> ring
  have h_existsR : ∀ (R : Set (EuclideanSpace ℝ (Fin 2))), R ∈ sFA →
      ∃ (s : Finset (Set (EuclideanSpace ℝ (Fin 2)))),
        (s : Set (Set (EuclideanSpace ℝ (Fin 2)))) = dyadicCubesMeeting δ (squareFor (xForR R)) ∧
        s.card ≤ K := by
    intro R hR
    let center := xForR R
    let h_bdd := bounded_square_cube_count hδ hD_nonneg (hS1 center) (hS2 center) (hS3 center) (hS4 center)
    let s := h_bdd.1.toFinset
    have hs_eq : (s : Set (Set (EuclideanSpace ℝ (Fin 2)))) = dyadicCubesMeeting δ (squareFor center) :=
      h_bdd.1.coe_toFinset
    have h_encard_eq : (↑s.card : ℕ∞) = (dyadicCubesMeeting δ (squareFor center)).encard := by
      have h1 : (s : Set (Set (EuclideanSpace ℝ (Fin 2)))).encard = ↑s.card := by simp
      have h2 : (dyadicCubesMeeting δ (squareFor center)).encard = (s : Set (Set (EuclideanSpace ℝ (Fin 2)))).encard := by
        rw [hs_eq]
      exact h1.symm.trans h2.symm
    have h_bound : ENat.toENNReal (↑s.card : ℕ∞) ≤ ENNReal.ofReal K_real := by
      have h3 : ENat.toENNReal (dyadicCubesMeeting δ (squareFor center)).encard ≤ ENNReal.ofReal ((D / δ + 6) ^ 2) := h_bdd.2
      have h4 : ENNReal.ofReal ((D / δ + 6) ^ 2) = ENNReal.ofReal K_real := by rw [hK_eq]
      rw [h4] at h3
      rw [h_encard_eq]
      exact h3
    have h_card : s.card ≤ K := finset_card_le_of_ennreal_bound hK_nonneg h_bound
    exact ⟨s, hs_eq, h_card⟩
  let cubesForR (R : Set (EuclideanSpace ℝ (Fin 2))) : Finset (Set (EuclideanSpace ℝ (Fin 2))) :=
    if h : R ∈ sFA then Classical.choose (h_existsR R h) else ∅
  have h_cubesForR_spec : ∀ (R : Set (EuclideanSpace ℝ (Fin 2))) (hR : R ∈ sFA),
      (cubesForR R : Set (Set (EuclideanSpace ℝ (Fin 2)))) = dyadicCubesMeeting δ (squareFor (xForR R)) ∧
      (cubesForR R).card ≤ K := by
    intro R hR
    have h : cubesForR R = Classical.choose (h_existsR R hR) := by
      simp [cubesForR, hR]
    rw [h]
    exact Classical.choose_spec (h_existsR R hR)
  have h_sub : sA ⊆ Finset.biUnion sFA cubesForR := by
    intro Q hQ
    have hQ' : Q ∈ dyadicCubesMeeting δ A := by
      have h : (sA : Set _) = dyadicCubesMeeting δ A := hA_fin.coe_toFinset
      rw [← h]; exact hQ
    rcases hQ' with ⟨hQ_cube, ⟨x, hxQ, hxA⟩⟩
    let y := F x
    let R := cubeOfPoint y
    have hR_cube : R ∈ dyadicCubes 2 δ := ⟨_, rfl⟩
    have hR_meet : (R ∩ F '' A).Nonempty :=
      ⟨y, point_in_cubeContaining hδ y, ⟨x, hxA, rfl⟩⟩
    have hR_in : R ∈ dyadicCubesMeeting δ (F '' A) := ⟨hR_cube, hR_meet⟩
    have hR_sFA : R ∈ sFA := by
      simpa [sFA, Set.Finite.mem_toFinset] using hR_in
    have h_yR : pointForR R ∈ R ∧ pointForR R ∈ F '' A := h_pointForR_prop R hR_sFA
    have h_xR : F (xForR R) = pointForR R ∧ xForR R ∈ A := h_xForR_prop R hR_sFA
    have h_y_in_R : pointForR R ∈ R := h_yR.1
    have h_Fx_in_R : F (xForR R) ∈ R := by rw [h_xR.1]; exact h_y_in_R
    have h_FxQ_in_R : F x ∈ R := point_in_cubeContaining hδ y
    rcases hR_cube with ⟨k, hR_eq⟩
    have h1 : F x ∈ dyadicCube δ k := by
      rw [← hR_eq]; exact h_FxQ_in_R
    have h2 : F (xForR R) ∈ dyadicCube δ k := by
      rw [← hR_eq]; exact h_Fx_in_R
    have h_dist : ‖F x - F (xForR R)‖ ≤ 2 * δ := cube_norm_spread hδ h1 h2
    have h_cl : C_L * ‖x - xForR R‖ ≤ ‖F x - F (xForR R)‖ := hF_lower x (xForR R)
    have h5 : C_L * ‖x - xForR R‖ ≤ 2 * δ := by linarith [h_cl, h_dist]
    have h_final : ‖x - xForR R‖ ≤ 2 * δ / C_L := by
      calc ‖x - xForR R‖
        = (C_L * ‖x - xForR R‖) / C_L := by field_simp [hC_L.ne'] <;> ring
      _ ≤ (2 * δ) / C_L := by gcongr
    let center := xForR R
    have h_x_in_square : x ∈ squareFor center := by
      have h_c0 : |x 0 - center 0| ≤ ‖x - center‖ := abs_coord_le_norm (x - center) 0
      have h_c1 : |x 1 - center 1| ≤ ‖x - center‖ := abs_coord_le_norm (x - center) 1
      exact ⟨by linarith, by linarith⟩
    have hQ'' : Q ∈ dyadicCubesMeeting δ (squareFor center) := by
      have h_meet : (Q ∩ squareFor center).Nonempty := ⟨x, hxQ, h_x_in_square⟩
      exact ⟨hQ_cube, h_meet⟩
    have hQ_in : Q ∈ cubesForR R := by
      have h_spec : (cubesForR R : Set (Set (EuclideanSpace ℝ (Fin 2)))) = dyadicCubesMeeting δ (squareFor center) :=
        (h_cubesForR_spec R hR_sFA).1
      have h_goal : Q ∈ (cubesForR R : Set (Set (EuclideanSpace ℝ (Fin 2)))) := by
        rw [h_spec]
        exact hQ''
      exact h_goal
    exact Finset.mem_biUnion.mpr ⟨R, hR_sFA, hQ_in⟩
  have h_cubesForR_bound : ∀ R ∈ sFA, (cubesForR R).card ≤ K :=
    fun R hR => (h_cubesForR_spec R hR).2
  have h_count : sA.card ≤ K * sFA.card :=
    finset_biUnion_card_bound cubesForR h_cubesForR_bound h_sub
  have h_coeA : (sA : Set (Set (EuclideanSpace ℝ (Fin 2)))) = dyadicCubesMeeting δ A :=
    hA_fin.coe_toFinset
  have h_coeFA : (sFA : Set (Set (EuclideanSpace ℝ (Fin 2)))) = dyadicCubesMeeting δ (F '' A) :=
    hFA_fin.coe_toFinset
  have h_encardA : (dyadicCubesMeeting δ A).encard = ↑sA.card := by
    have h : (dyadicCubesMeeting δ A).encard = ↑(hA_fin.toFinset.card) := by exact Finite.encard_eq_coe_toFinset_card hA_fin
    simpa [sA] using h
  have h_encardFA : (dyadicCubesMeeting δ (F '' A)).encard = ↑sFA.card := by
    have h : (dyadicCubesMeeting δ (F '' A)).encard = ↑(hFA_fin.toFinset.card) := by exact Finite.encard_eq_coe_toFinset_card hFA_fin
    simpa [sFA] using h
  have h1 : ENat.toENNReal (dyadicCoveringNumber δ A) = (↑sA.card : ENNReal) := by
    simp [dyadicCoveringNumber, h_encardA]
  have h2 : ENat.toENNReal (dyadicCoveringNumber δ (F '' A)) = (↑sFA.card : ENNReal) := by
    simp [dyadicCoveringNumber, h_encardFA]
  rw [h1, h2]
  have h3 : (↑sA.card : ENNReal) ≤ (↑K : ENNReal) * (↑sFA.card : ENNReal) := by
    exact_mod_cast h_count
  have h4 : (↑K : ENNReal) ≤ ENNReal.ofReal K_real := by
    have h5 : (K : ℝ) ≤ K_real := hK_le
    have h6 : ENNReal.ofReal (K : ℝ) ≤ ENNReal.ofReal K_real := ENNReal.ofReal_le_ofReal h5
    have h7 : (↑K : ENNReal) = ENNReal.ofReal (K : ℝ) := by simp
    rw [h7]; exact h6
  calc (↑sA.card : ENNReal)
    ≤ (↑K : ENNReal) * (↑sFA.card : ENNReal) := h3
    _ ≤ ENNReal.ofReal K_real * (↑sFA.card : ENNReal) := by gcongr <;> exact h4

/-! ### Main theorem -/

/-- Given a bi-Lipschitz map F and bounded set Pbar, construct Pbar' := F '' Pbar
    and prove both covering comparisons. Applies uniformly to Pbar, E3,
    and tube parameter realization sets. -/
theorem pbar_prime_construction
    {δ : ℝ} (hδ_pos : 0 < δ)
    {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {C_L C_U : ℝ} (hC_L_pos : 0 < C_L) (hC_U_nonneg : 0 ≤ C_U)
    (hF_lower : ∀ x y, C_L * ‖x - y‖ ≤ ‖F x - F y‖)
    (hF_upper : ∀ x y, ‖F x - F y‖ ≤ C_U * ‖x - y‖)
    {Pbar : Set (EuclideanSpace ℝ (Fin 2))}
    (hPbar_bdd : Bornology.IsBounded Pbar) :
    let Pbar' := F '' Pbar
    Bornology.IsBounded Pbar' ∧
    ENat.toENNReal (dyadicCoveringNumber δ Pbar') ≠ ⊤ ∧
    ENat.toENNReal (dyadicCoveringNumber δ Pbar) ≠ ⊤ ∧
    ENat.toENNReal (dyadicCoveringNumber δ Pbar') ≤
      ENNReal.ofReal ((4 * C_U + 6) ^ 2) *
        ENat.toENNReal (dyadicCoveringNumber δ Pbar) ∧
    ENat.toENNReal (dyadicCoveringNumber δ Pbar) ≤
      ENNReal.ofReal ((4 / C_L + 6) ^ 2) *
        ENat.toENNReal (dyadicCoveringNumber δ Pbar') := by
  let Pbar' := F '' Pbar
  have hPbar'_bdd : Bornology.IsBounded Pbar' :=
    lipschitz_image_bounded hC_U_nonneg hF_upper hPbar_bdd
  have h_forward := lipschitz_covering_upper hδ_pos hC_U_nonneg hF_upper hPbar_bdd
  have h_backward := colipschitz_covering_lower hδ_pos hC_L_pos hC_U_nonneg hF_lower hF_upper hPbar_bdd
  have h_fin1 : (dyadicCubesMeeting δ Pbar').Finite :=
    finite_dyadicCubesMeeting_bounded hδ_pos hPbar'_bdd
  have h_fin2 : (dyadicCubesMeeting δ Pbar).Finite :=
    finite_dyadicCubesMeeting_bounded hδ_pos hPbar_bdd
  have h_ne_top1 : ENat.toENNReal (dyadicCoveringNumber δ Pbar') ≠ ⊤ := by
    simp [dyadicCoveringNumber, h_fin1]
    <;> exact_mod_cast h_fin1.encard.ne_top
  have h_ne_top2 : ENat.toENNReal (dyadicCoveringNumber δ Pbar) ≠ ⊤ := by
    simp [dyadicCoveringNumber, h_fin2]
    <;> exact_mod_cast h_fin2.encard.ne_top
  exact ⟨hPbar'_bdd, h_ne_top1, h_ne_top2, h_forward, h_backward⟩

end Defect36
