module

/-
  Shared S-set thickening utilities for EuclideanPlane and general metric spaces.

  Extracted from `AppendixA/A10_SSetUtils.lean` to break the circular dependency
  caused by that file importing the top-level target. Team B/C production files
  should import this shared module instead of `AppendixA/*`.

  Provides:
  - `IsDeltaSSet.thickening_general`: generic thickening with custom covering inflation
  - `plane_ball_grid_cover`: grid cover of a ball in EuclideanPlane
  - `plane_thickening_cover`: covering-number inflation for R-close sets in the plane
  - `IsDeltaSSet.thickening_plane`: S-set thickening on EuclideanPlane

  Whiteprint node: shared / sset_thickening
  Dependencies: Base, CoveringUtils
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.A10

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CoveringUtils

/-! ### Helper lemmas -/

/-- Rounding to nearest integer: `|z - round(z)| ≤ 1/2`. -/
lemma round_half (z : ℝ) : ∃ (k : ℤ), |z - (k : ℝ)| ≤ 1 / 2 := by
  let k : ℤ := Int.floor (z + 1 / 2)
  have h1 : (k : ℝ) ≤ z + 1 / 2 := Int.floor_le _
  have h2 : z + 1 / 2 < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have h3 : -1 / 2 ≤ z - (k : ℝ) := by linarith
  have h4 : z - (k : ℝ) < 1 / 2 := by linarith
  exact ⟨k, by rw [abs_le] <;> constructor <;> linarith⟩

/-- Coordinate bound in EuclideanPlane: `|x i| ≤ ‖x‖`. -/
lemma plane_coord_bound (x : EuclideanPlane) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  have h1 : x i ^ 2 ≤ ‖x‖ ^ 2 := by
    have h_norm2 : ‖x‖ ^ 2 = ∑ j : Fin 2, (x j)^2 := by
      rw [EuclideanSpace.norm_eq]
      have h_sum : ∑ j : Fin 2, ‖x j‖ ^ 2 = ∑ j : Fin 2, (x j)^2 := by
        apply Finset.sum_congr rfl
        intro j _
        have h_abs : ‖x j‖ = |x j| := by exact Real.norm_eq_abs (x.ofLp j)
        rw [h_abs]
        <;> rw [sq_abs]
      rw [Real.sq_sqrt (by positivity), h_sum]
    rw [h_norm2]
    apply Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ i)
  have h2 : 0 ≤ ‖x‖ := by positivity
  have h3 : |x i| ^ 2 ≤ ‖x‖ ^ 2 := by simpa [sq_abs] using h1
  have h4 : 0 ≤ |x i| := by positivity
  nlinarith

/-- Cardinality of symmetric integer interval `[-n, n]`. -/
lemma card_symm_int (n : ℕ) :
    (Finset.Icc (-(n : ℤ)) (n : ℤ)).card = 2 * n + 1 := by
  have h_equiv : Finset.Icc (-(n : ℤ)) (n : ℤ) = Finset.Ico (-(n : ℤ)) ((n : ℤ) + 1) := by
    ext x
    simp [Finset.mem_Icc, Finset.mem_Ico] <;> omega
  rw [h_equiv]
  have h_card : (Finset.Ico (-(n : ℤ)) ((n : ℤ) + 1)).card = 2 * n + 1 := by
    have h : ∀ (a b : ℤ), a ≤ b → (Finset.Ico a b).card = (b - a).toNat := by
      intro a b h
      exact Int.card_Ico a b
    have h' := h (-(n : ℤ)) ((n : ℤ) + 1) (by linarith)
    rw [h']
    <;> simp [Int.toNat_of_nonneg] <;> omega
  exact h_card

/-! ### General thickening -/

/-- General thickening lemma: if `A` is a `(δ, s, C)`-set, `A ⊆ B`, every point of `B`
is within distance `R` of some point of `A`, and `R`-close sets have covering numbers
inflated by at most `M`, then `B` is a `(δ, s, M * (1 + R/δ)^s * C)`-set.

Key: for `y ∈ B ∩ B(x, r)`, pick `a ∈ A` with `dist y a ≤ R`; then `dist a x ≤ r + R`.
Since `r ≥ δ`, `(r + R)^s ≤ (1 + R/δ)^s * r^s`. -/
lemma IsDeltaSSet.thickening_general {X : Type*} [PseudoMetricSpace X]
    {δ s C R : ℝ} {A B : Set X}
    (h : IsDeltaSSet δ s C A)
    (hA_sub_B : A ⊆ B)
    (hR_nonneg : 0 ≤ R)
    (h_close : ∀ y ∈ B, ∃ a ∈ A, dist y a ≤ R)
    (M : ℝ) (hM_pos : 0 < M)
    (h_inflate : ∀ (S T : Set X),
      (∀ y ∈ T, ∃ s ∈ S, dist y s ≤ R) →
      (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≤
        ENNReal.ofReal M * (Metric.externalCoveringNumber δ.toNNReal S : ENNReal)) :
    IsDeltaSSet δ s (M * (1 + R / δ) ^ s * C) B := by
  rcases h with ⟨hA_nonempty, hδ_pos, hC_pos, hs_nonneg, hmain⟩
  have hB_nonempty : B.Nonempty := hA_nonempty.mono hA_sub_B
  have hC'_pos : 0 < M * (1 + R / δ) ^ s * C := by positivity
  refine ⟨hB_nonempty, hδ_pos, hC'_pos, hs_nonneg, ?_⟩
  intro x r hr
  have h_rpos : 0 < r := by linarith
  let S' := A ∩ Metric.closedBall x (r + R)
  have h1 : ∀ y ∈ B ∩ Metric.closedBall x r, ∃ a ∈ S', dist y a ≤ R := by
    intro y hy
    have hyB : y ∈ B := hy.1
    have hyr : dist y x ≤ r := by simpa [Metric.mem_closedBall] using hy.2
    rcases h_close y hyB with ⟨a, haA, hdist⟩
    have h4 : dist a x ≤ r + R := by
      have h5 : dist a x ≤ dist a y + dist y x := dist_triangle a y x
      have h6 : dist a y ≤ R := by simpa [dist_comm] using hdist
      linarith
    exact ⟨a, ⟨haA, by simpa [Metric.mem_closedBall] using h4⟩, hdist⟩
  have h4 : (Metric.externalCoveringNumber δ.toNNReal (B ∩ Metric.closedBall x r) : ENNReal) ≤
      ENNReal.ofReal M * (Metric.externalCoveringNumber δ.toNNReal S' : ENNReal) :=
    h_inflate S' (B ∩ Metric.closedBall x r) h1
  have h6 : (Metric.externalCoveringNumber δ.toNNReal S' : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal (r + R)) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) :=
    hmain x (r + R) (by linarith)
  have h71 : r + R ≤ (1 + R / δ) * r := by
    have h72 : δ ≤ r := hr
    have h73 : R ≤ (R / δ) * r := by
      have h74 : 0 < δ := hδ_pos
      calc R = (R / δ) * δ := by field_simp [h74.ne'] <;> ring
           _ ≤ (R / δ) * r := by gcongr
    linarith
  have h7 : (ENNReal.ofReal (r + R)) ^ s ≤ (ENNReal.ofReal ((1 + R / δ) * r)) ^ s := by
    gcongr <;> linarith
  have h8 : (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal B : ENNReal) := by
    have h_enat : Metric.externalCoveringNumber δ.toNNReal A ≤
        Metric.externalCoveringNumber δ.toNNReal B :=
      Metric.externalCoveringNumber_mono_set hA_sub_B
    exact_mod_cast h_enat
  have h9 : ENNReal.ofReal (M * (1 + R / δ) ^ s * C) =
      ENNReal.ofReal M * ENNReal.ofReal ((1 + R / δ) ^ s) * ENNReal.ofReal C := by
    have hM_nonneg : 0 ≤ M := by linarith
    have h1s_nonneg : 0 ≤ (1 + R / δ) ^ s := by positivity
    have hC_nonneg : 0 ≤ C := by linarith
    have h1 : ENNReal.ofReal (M * ((1 + R / δ) ^ s)) =
        ENNReal.ofReal M * ENNReal.ofReal ((1 + R / δ) ^ s) :=
      ENNReal.ofReal_mul hM_nonneg
    have h2 : ENNReal.ofReal ((M * ((1 + R / δ) ^ s)) * C) =
        ENNReal.ofReal (M * ((1 + R / δ) ^ s)) * ENNReal.ofReal C :=
      ENNReal.ofReal_mul (by positivity)
    have h3 : M * (1 + R / δ) ^ s * C = (M * (1 + R / δ) ^ s) * C := by ring
    rw [h3, h2, h1] <;> ring
  have h10 : (ENNReal.ofReal ((1 + R / δ) * r)) ^ s =
      ENNReal.ofReal ((1 + R / δ) ^ s) * (ENNReal.ofReal r) ^ s := by
    have hRdiv : 0 ≤ R / δ := by positivity
    have h_pos1 : 0 ≤ 1 + R / δ := by linarith
    have h11 : ENNReal.ofReal ((1 + R / δ) * r) =
        ENNReal.ofReal (1 + R / δ) * ENNReal.ofReal r :=
      ENNReal.ofReal_mul h_pos1
    rw [h11, ENNReal.mul_rpow_of_nonneg _ _ hs_nonneg]
    have h12 : ENNReal.ofReal (1 + R / δ) ^ s = ENNReal.ofReal ((1 + R / δ) ^ s) :=
      ENNReal.ofReal_rpow_of_nonneg h_pos1 hs_nonneg
    rw [h12] <;> ring
  calc
    (Metric.externalCoveringNumber δ.toNNReal (B ∩ Metric.closedBall x r) : ENNReal)
      ≤ ENNReal.ofReal M * (Metric.externalCoveringNumber δ.toNNReal S' : ENNReal) := h4
    _ ≤ ENNReal.ofReal M * (ENNReal.ofReal C * (ENNReal.ofReal (r + R)) ^ s *
           (Metric.externalCoveringNumber δ.toNNReal A : ENNReal)) := by gcongr <;> exact h6
    _ ≤ ENNReal.ofReal M * (ENNReal.ofReal C * (ENNReal.ofReal ((1 + R / δ) * r)) ^ s *
           (Metric.externalCoveringNumber δ.toNNReal A : ENNReal)) := by gcongr <;> exact h7
    _ = ENNReal.ofReal M * ENNReal.ofReal C * (ENNReal.ofReal ((1 + R / δ) * r)) ^ s *
           (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by ring
    _ ≤ ENNReal.ofReal M * ENNReal.ofReal C * (ENNReal.ofReal ((1 + R / δ) * r)) ^ s *
           (Metric.externalCoveringNumber δ.toNNReal B : ENNReal) := by gcongr <;> exact h8
    _ = ENNReal.ofReal (M * (1 + R / δ) ^ s * C) * (ENNReal.ofReal r) ^ s *
           (Metric.externalCoveringNumber δ.toNNReal B : ENNReal) := by
      rw [h9, h10] <;> ring

/-! ### Plane grid covering -/

/-- In EuclideanPlane, a ball of radius `L` can be covered by at most
`(2 * L / δ + 4)^2` δ-balls using a square grid.
Rounding each coordinate to nearest multiple of δ gives Euclidean distance ≤ δ/√2 < δ. -/
lemma plane_ball_grid_cover {δ L : ℝ} (hδ_pos : 0 < δ) (hL_nonneg : 0 ≤ L)
    (c : EuclideanPlane) :
    ∃ (D : Finset EuclideanPlane),
      (D.card : ℝ) ≤ (2 * L / δ + 4) ^ 2 ∧
      Metric.IsCover δ.toNNReal (Metric.closedBall c L) D := by
  let n : ℕ := Nat.ceil (L / δ + 1 / 2)
  let idx : Finset ℤ := Finset.Icc (-(n : ℤ)) (n : ℤ)
  let e : EuclideanPlane ≃ (Fin 2 → ℝ) := WithLp.equiv 2 _
  let g : ℤ × ℤ → EuclideanPlane := fun p =>
    e.symm (fun i : Fin 2 => c i + (if i = 0 then (p.1 : ℝ) else (p.2 : ℝ)) * δ)
  let D : Finset EuclideanPlane := Finset.image g (idx ×ˢ idx)
  have h_n_le : (n : ℝ) ≤ L / δ + 3 / 2 := by
    have h : (n : ℝ) < L / δ + 1 / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have h_card : (D.card : ℝ) ≤ (2 * L / δ + 4) ^ 2 := by
    have h1 : D.card ≤ (idx ×ˢ idx).card := Finset.card_image_le
    have h2 : (idx ×ˢ idx).card = idx.card ^ 2 := by
      rw [Finset.card_product] <;> ring
    have h3 : idx.card = 2 * n + 1 := card_symm_int n
    have h4 : (D.card : ℝ) ≤ (2 * (n : ℝ) + 1) ^ 2 := by
      calc (D.card : ℝ)
          ≤ ((idx ×ˢ idx).card : ℝ) := by exact_mod_cast h1
        _ = (idx.card : ℝ) ^ 2 := by rw [h2] <;> norm_cast
        _ = (2 * (n : ℝ) + 1) ^ 2 := by rw [h3] <;> norm_cast
    have h5 : (2 * (n : ℝ) + 1) ^ 2 ≤ (2 * L / δ + 4) ^ 2 := by
      have h6 : 0 ≤ 2 * (n : ℝ) + 1 := by positivity
      have h7 : 2 * (n : ℝ) + 1 ≤ 2 * L / δ + 4 := by
        calc 2 * (n : ℝ) + 1
            ≤ 2 * (L / δ + 3 / 2) + 1 := by gcongr
          _ = 2 * L / δ + 4 := by ring
      gcongr
    exact h4.trans h5
  have h_cover : Metric.IsCover δ.toNNReal (Metric.closedBall c L) D := by
    intro y hy
    have h_norm : ‖y - c‖ ≤ L := by simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    have h_coord : ∀ (i : Fin 2), |(y - c) i| ≤ L := by
      intro i
      have h : |(y - c) i| ≤ ‖y - c‖ := plane_coord_bound (y - c) i
      linarith
    have h_round : ∀ (i : Fin 2), ∃ (k : ℤ), |((y - c) i / δ) - (k : ℝ)| ≤ 1 / 2 :=
      fun i => round_half (((y - c) i / δ))
    choose k hk using h_round
    have h_k_bound : ∀ (i : Fin 2), |(k i : ℝ)| ≤ (n : ℝ) := by
      intro i
      have h5 : |((y - c) i / δ)| ≤ L / δ := by
        have h6 : |(y - c) i| ≤ L := h_coord i
        have h7 : |((y - c) i / δ)| = |(y - c) i| / δ := by
          rw [abs_div, abs_of_pos hδ_pos]
        rw [h7]; gcongr
      have h_abs : |(k i : ℝ)| ≤ |((y - c) i / δ)| + |((y - c) i / δ) - (k i : ℝ)| := by
        set a := (y - c) i / δ with ha
        set b := (k i : ℝ) with hb
        have h : |a - (a - b)| ≤ |a| + |a - b| := by exact abs_sub a (a - b)
        have h_eq : a - (a - b) = b := by ring
        rw [h_eq] at h
        exact h
      have h9 : |(k i : ℝ)| ≤ L / δ + 1 / 2 := by
        calc |(k i : ℝ)|
            ≤ |((y - c) i / δ)| + |((y - c) i / δ) - (k i : ℝ)| := h_abs
          _ ≤ |((y - c) i / δ)| + 1 / 2 := by gcongr <;> exact hk i
          _ ≤ L / δ + 1 / 2 := by gcongr
      have h10 : L / δ + 1 / 2 ≤ (n : ℝ) := Nat.le_ceil _
      exact h9.trans h10
    have h_k_in_idx : ∀ (i : Fin 2), k i ∈ idx := by
      intro i
      have h11 : |(k i : ℝ)| ≤ (n : ℝ) := h_k_bound i
      have h12 : -(n : ℝ) ≤ (k i : ℝ) := by linarith [abs_le.mp h11]
      have h13 : (k i : ℝ) ≤ (n : ℝ) := by linarith [abs_le.mp h11]
      simp only [idx, Finset.mem_Icc]
      exact ⟨by exact_mod_cast h12, by exact_mod_cast h13⟩
    let p : ℤ × ℤ := (k 0, k 1)
    have hp : p ∈ idx ×ˢ idx := by
      exact Finset.mem_product.mpr ⟨h_k_in_idx 0, h_k_in_idx 1⟩
    have hg_in_D : g p ∈ D := Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have h_dist : ‖y - g p‖ ≤ δ := by
      have h1 : ∀ (i : Fin 2), |(y - g p) i| ≤ δ / 2 := by
        intro i
        have h2 : (y - g p) i = (y - c) i - (k i : ℝ) * δ := by
          have h_sub : (y - g p) i = y i - (g p) i := by
            have h : e (y - g p) = e y - e (g p) := by
              simp [e, WithLp.equiv] <;> rfl
            have h2 : (y - g p) i = (e (y - g p)) i := by exact Real.ext_cauchy rfl
            rw [h2, h] <;> rfl
          rw [h_sub]
          have h_gp : (g p) i = c i + (if i = 0 then (p.1 : ℝ) else (p.2 : ℝ)) * δ := by
            have h_eq1 : e (g p) = (fun j : Fin 2 => c j + (if j = 0 then (p.1 : ℝ) else (p.2 : ℝ)) * δ) := by
              simp [g, e, WithLp.equiv]
            have h_eq2 : (g p) i = (e (g p)) i := by exact Real.ext_cauchy rfl
            rw [h_eq2, h_eq1] <;> rfl
          rw [h_gp]
          have h_yc : (y - c) i = y i - c i := by
            have h : e (y - c) = e y - e c := by simp [e, WithLp.equiv] <;> rfl
            have h2 : (y - c) i = (e (y - c)) i := by exact Real.ext_cauchy rfl
            rw [h2, h] <;> rfl
          rw [h_yc]
          fin_cases i <;> simp [p] <;> ring
        rw [h2]
        have h3 : |((y - c) i / δ) - (k i : ℝ)| ≤ 1 / 2 := hk i
        have h4 : |(y - c) i - (k i : ℝ) * δ| = δ * |((y - c) i / δ) - (k i : ℝ)| := by
          have h_eq : (y - c) i - (k i : ℝ) * δ = δ * (((y - c) i / δ) - (k i : ℝ)) := by
            field_simp [hδ_pos.ne'] <;> ring
          rw [h_eq, abs_mul, abs_of_pos hδ_pos] <;> ring
        have h5 : δ * |((y - c) i / δ) - (k i : ℝ)| ≤ δ / 2 := by
          have h6 : |((y - c) i / δ) - (k i : ℝ)| ≤ 1 / 2 := hk i
          have h7 : δ * |((y - c) i / δ) - (k i : ℝ)| ≤ δ * (1 / 2) := by gcongr
          linarith
        rw [h4]
        exact h5
      have h5 : ‖y - g p‖ ^ 2 = ∑ i : Fin 2, ((y - g p) i)^2 := by
        rw [EuclideanSpace.norm_eq]
        have h6 : Real.sqrt (∑ i : Fin 2, ((y - g p) i)^2) ^ 2 = ∑ i : Fin 2, ((y - g p) i)^2 := by
          rw [Real.sq_sqrt] <;> positivity
        simpa using h6
      have h7 : ∑ i : Fin 2, ((y - g p) i)^2 ≤ ∑ i : Fin 2, (δ / 2)^2 := by
        apply Finset.sum_le_sum; intro i _
        have h8 : |(y - g p) i| ≤ δ / 2 := h1 i
        have h9 : ((y - g p) i)^2 ≤ (δ / 2)^2 := by
          calc ((y - g p) i)^2 = |(y - g p) i|^2 := by rw [sq_abs]
            _ ≤ (δ / 2)^2 := by gcongr
        exact h9
      have h10 : ‖y - g p‖ ^ 2 ≤ δ ^ 2 := by
        rw [h5]
        have h11 : ∑ i : Fin 2, (δ / 2)^2 = 2 * (δ / 2)^2 := by
          simp [Fin.sum_univ_two] <;> ring
        rw [h11] at h7
        nlinarith
      have h12 : 0 ≤ ‖y - g p‖ := by positivity
      nlinarith
    have h_edist : edist y (g p) ≤ ↑δ.toNNReal := by
      have h14 : dist y (g p) ≤ δ := by
        simpa [dist_eq_norm] using h_dist
      have h15 : edist y (g p) = ENNReal.ofReal (dist y (g p)) := by exact edist_dist y (g p)
      rw [h15]
      have h16 : ENNReal.ofReal (dist y (g p)) ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal h14
      have h17 : ENNReal.ofReal δ = ↑δ.toNNReal := by
        exact Eq.symm (ENNReal.ofNNReal_toNNReal δ)
      rw [h17] at h16
      exact h16
    exact ⟨g p, hg_in_D, h_edist⟩
  exact ⟨D, h_card, h_cover⟩

/-! ### Plane thickening cover -/

/-- Covering-number inflation for R-close sets in EuclideanPlane: if every point of `T`
is within distance `R` of some point of `S`, then `N_δ(T) ≤ (2*(R+δ)/δ + 4)^2 * N_δ(S)`.

Proof: take a δ-cover `C` of `S`. Every point of `T` is within `R+δ` of some center in `C`.
Each ball of radius `R+δ` is covered by a grid of δ-balls. -/
lemma plane_thickening_cover {δ R : ℝ} (hδ_pos : 0 < δ) (hR_nonneg : 0 ≤ R)
    {S T : Set EuclideanPlane}
    (h : ∀ y ∈ T, ∃ s ∈ S, dist y s ≤ R) :
    (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≤
      ENNReal.ofReal ((2 * (R + δ) / δ + 4) ^ 2) *
        (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := by
  by_cases h_top : Metric.externalCoveringNumber δ.toNNReal S = ⊤
  · have hM_ne_zero : (ENNReal.ofReal ((2 * (R + δ) / δ + 4) ^ 2)) ≠ 0 := by positivity
    rw [h_top]
    simp [hM_ne_zero]
    <;> exact le_top
  · have h_fin : Metric.externalCoveringNumber δ.toNNReal S < ⊤ :=
      lt_top_iff_ne_top.mpr h_top
    rcases DiscretisedFurstenbergEstimate.CoveringUtils.exists_external_cover_eq h_fin
      with ⟨C, hC, h_eq⟩
    let L : ℝ := R + δ
    have hL_nonneg : 0 ≤ L := by linarith
    choose D hD_card hD_cover using fun (c : EuclideanPlane) =>
      plane_ball_grid_cover hδ_pos hL_nonneg c
    have h1 : C.encard < ⊤ := by
      have h2 : C.encard = Metric.externalCoveringNumber δ.toNNReal S := h_eq
      rw [h2]; exact h_fin
    have hC_finite : C.Finite := by
      by_contra h3
      have h5 : C.encard = ⊤ := Set.Infinite.encard_eq h3
      exact ne_of_lt h1 h5
    let Cfin : Finset EuclideanPlane := hC_finite.toFinset
    have hCfin : (Cfin : Set EuclideanPlane) = C := hC_finite.coe_toFinset
    let Dfin : Finset EuclideanPlane := Cfin.biUnion (fun c => D c)
    have h_cover : Metric.IsCover δ.toNNReal T (Dfin : Set EuclideanPlane) := by
      intro y hy
      rcases h y hy with ⟨s, hsS, hdist_ys⟩
      rcases hC hsS with ⟨c, hcC, hdist_sc⟩
      have hdist_ys' : dist y s ≤ R := by simpa [dist_comm] using hdist_ys
      have hdist_sc' : dist s c ≤ δ := by
        have h : (nndist s c : ℝ) ≤ (δ.toNNReal : ℝ) := by exact_mod_cast hdist_sc
        have h2 : (nndist s c : ℝ) = dist s c := by exact coe_nndist s c
        have h3 : (δ.toNNReal : ℝ) = δ := by
          have h4 : (δ.toNNReal : ℝ) = max δ 0 := by
            simp [Real.toNNReal] <;> rfl
          rw [h4]
          have h5 : max δ 0 = δ := by
            rw [max_eq_left] <;> linarith
          exact h5
        rw [h2, h3] at h; exact h
      have hdist_yc : dist y c ≤ L := by
        calc dist y c ≤ dist y s + dist s c := dist_triangle y s c
             _ ≤ R + δ := by linarith
             _ = L := by ring
      have h_y_in_ball : y ∈ Metric.closedBall c L := by
        simpa [Metric.mem_closedBall] using hdist_yc
      rcases hD_cover c h_y_in_ball with ⟨d, hd_in_D, hdist_d⟩
      have hcCfin : c ∈ Cfin := by
        have h : c ∈ (Cfin : Set EuclideanPlane) := by
          rw [hCfin]; exact hcC
        exact Finset.mem_coe.mpr h
      have hd_in_Dfin : d ∈ Dfin := by
        exact Finset.mem_biUnion.mpr ⟨c, hcCfin, hd_in_D⟩
      exact ⟨d, hd_in_Dfin, hdist_d⟩
    have h4 : Metric.externalCoveringNumber δ.toNNReal T ≤ (Dfin.card : ENat) := by
      have h41 := Metric.IsCover.externalCoveringNumber_le_encard h_cover
      have h42 : (Dfin : Set EuclideanPlane).encard = (Dfin.card : ENat) := by exact Set.encard_coe_eq_coe_finsetCard Dfin
      rw [h42] at h41
      exact h41
    have h5 : Dfin.card ≤ ∑ c ∈ Cfin, (D c).card := Finset.card_biUnion_le
    have h6 : ∀ c ∈ Cfin, ((D c).card : ℝ) ≤ (2 * L / δ + 4) ^ 2 := by
      intro c _; exact hD_card c
    have h7 : (Dfin.card : ℝ) ≤ (Cfin.card : ℝ) * (2 * L / δ + 4) ^ 2 := by
      calc (Dfin.card : ℝ)
          ≤ ∑ c ∈ Cfin, ((D c).card : ℝ) := by exact_mod_cast h5
        _ ≤ ∑ c ∈ Cfin, (2 * L / δ + 4) ^ 2 := by
          apply Finset.sum_le_sum; intro c _; exact h6 c ‹_›
        _ = (Cfin.card : ℝ) * (2 * L / δ + 4) ^ 2 := by
          rw [Finset.sum_const] <;> ring
    have h8 : (2 * L / δ + 4) ^ 2 = (2 * (R + δ) / δ + 4) ^ 2 := by
      have h9 : L = R + δ := by rfl
      rw [h9] <;> rfl
    have h9 : (Dfin.card : ENNReal) ≤
        ENNReal.ofReal ((2 * (R + δ) / δ + 4) ^ 2) * (C.encard : ENNReal) := by
      have h10 : (Dfin.card : ℝ) ≤ (Cfin.card : ℝ) * (2 * (R + δ) / δ + 4) ^ 2 := by
        rw [h8] at h7; exact h7
      have h11 : C.encard = (Cfin.card : ENat) := by exact Set.Finite.encard_eq_coe_toFinset_card hC_finite
      rw [h11]
      have h12 : (Dfin.card : ENNReal) ≤
          ENNReal.ofReal ((Cfin.card : ℝ) * (2 * (R + δ) / δ + 4) ^ 2) := by
        have h121 : (Dfin.card : ENNReal) = ENNReal.ofReal (Dfin.card : ℝ) := by simp
        rw [h121]
        exact ENNReal.ofReal_le_ofReal h10
      have h13 : ENNReal.ofReal ((Cfin.card : ℝ) * (2 * (R + δ) / δ + 4) ^ 2) =
          ENNReal.ofReal ((2 * (R + δ) / δ + 4) ^ 2) * (Cfin.card : ENNReal) := by
        have h14 : 0 ≤ (Cfin.card : ℝ) := by positivity
        rw [ENNReal.ofReal_mul h14]
        <;> simp
        <;> ring
      rw [h13] at h12
      exact h12
    have h4' : (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≤ (Dfin.card : ENNReal) := by
      exact_mod_cast h4
    have h10 : (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≤
        ENNReal.ofReal ((2 * (R + δ) / δ + 4) ^ 2) * (C.encard : ENNReal) :=
      h4'.trans h9
    have h11 : (C.encard : ENNReal) = (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := by
      exact_mod_cast h_eq
    rw [h11] at h10
    exact h10

/-! ### Plane thickening -/

/-- Thickening on EuclideanPlane: if `A` is a `(δ, s, C)`-set, `A ⊆ B`, and every point
of `B` is within distance `R` of some point of `A`, then `B` is an S-set with constant
`(2*(R+δ)/δ + 4)^2 * (1 + R/δ)^s * C`. -/
lemma IsDeltaSSet.thickening_plane {δ s C R : ℝ} {A B : Set EuclideanPlane}
    (h : IsDeltaSSet δ s C A)
    (hA_sub_B : A ⊆ B)
    (hR_nonneg : 0 ≤ R)
    (h_close : ∀ y ∈ B, ∃ a ∈ A, dist y a ≤ R) :
    IsDeltaSSet δ s ((2 * (R + δ) / δ + 4) ^ 2 * (1 + R / δ) ^ s * C) B := by
  have hδ_pos : 0 < δ := h.2.1
  let M : ℝ := (2 * (R + δ) / δ + 4) ^ 2
  have hM_pos : 0 < M := by
    have h1 : 0 < 2 * (R + δ) / δ + 4 := by positivity
    exact sq_pos_of_pos h1
  exact IsDeltaSSet.thickening_general h hA_sub_B hR_nonneg h_close M hM_pos
    (fun S T hcl => plane_thickening_cover hδ_pos hR_nonneg hcl)

end DirecretisedFurstenbergEstimate.A10
