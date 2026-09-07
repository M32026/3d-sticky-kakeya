/-
# Symmetric center equals outer John ellipsoid center

If a convex body K is centrally symmetric about z, then the center of its
unique outer John ellipsoid equals z.

## Proof outline

Given K symmetric about z, and E = ellipsoid c A is a minimal ellipsoid:

1. For x ∈ K, A u = x - c and A v = 2z - x - c for some u, v ∈ B.
2. A(u - v) = 2(x - z), so A⁻¹(x - z) = (u - v)/2 ∈ B.
3. Thus K ⊆ ellipsoid z A.
4. ellipsoid z A has the same volume as ellipsoid c A (translation invariance).
5. Hence ellipsoid z A is also a minimal ellipsoid.
6. By uniqueness, ellipsoid c A = ellipsoid z A.
7. So (c-z) + A(B) = A(B). Since A(B) is bounded and nonempty, c-z = 0.

## Whiteprint node
symmetric_center
-/

import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Basic
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.VolumeUtils
import Mathlib.Tactic

noncomputable section

open MeasureTheory
open scoped Pointwise Real

namespace JohnEllipsoid

variable {n : ℕ} {K : Set (E n)}

/-- If d +ᵥ S = S for a bounded nonempty set S, then d = 0. -/
lemma bounded_vadd_invariant_eq_zero {S : Set (E n)} {d : E n}
    (hS : Bornology.IsBounded S) (hne : S.Nonempty) (h : d +ᵥ S = S) : d = 0 := by
  by_contra hd
  rcases hne with ⟨x, hx⟩
  have h1 : ∀ n : ℕ, x + (n : ℝ) • d ∈ S := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      have h2 : x + (n : ℝ) • d ∈ S := ih
      have h3 : d +ᵥ (x + (n : ℝ) • d) ∈ d +ᵥ S := Set.mem_image_of_mem _ h2
      have h4 : d +ᵥ (x + (n : ℝ) • d) = x + ((n + 1 : ℕ) : ℝ) • d := by
        simp [vadd_eq_add, add_smul, Nat.cast_add, Nat.cast_one] <;> abel
      rw [h4] at h3
      rw [h] at h3
      exact h3
  have h_bound : ∃ C : ℝ, ∀ (a : E n), a ∈ S → ∀ (b : E n), b ∈ S → dist a b ≤ C := by
    simpa [Metric.isBounded_iff] using hS
  rcases h_bound with ⟨C, hC⟩
  let R := C
  have hR : ∀ y ∈ S, dist y x ≤ R := by
    intro y hy
    have h : dist x y ≤ C := hC x hx y hy
    have h2 : dist y x = dist x y := dist_comm y x
    rw [h2]
    exact h
  have h4 : ∀ n : ℕ, (n : ℝ) * ‖d‖ ≤ R := by
    intro n
    have h5 : dist (x + (n : ℝ) • d) x ≤ R := hR (x + (n : ℝ) • d) (h1 n)
    have h6 : dist (x + (n : ℝ) • d) x = (n : ℝ) * ‖d‖ := by
      rw [dist_eq_norm]
      have h7 : ‖(x + (n : ℝ) • d) - x‖ = ‖(n : ℝ) • d‖ := by abel_nf
      rw [h7]
      have h8 : ‖(n : ℝ) • d‖ = |(n : ℝ)| * ‖d‖ := norm_smul (n : ℝ) d
      rw [h8]
      have h9 : |(n : ℝ)| = (n : ℝ) := by
        rw [abs_of_nonneg] <;> positivity
      rw [h9]
    rw [h6] at h5
    exact h5
  have hpos : 0 < ‖d‖ := by exact_mod_cast (norm_pos_iff.mpr hd)
  obtain ⟨n, hn⟩ := exists_nat_gt (R / ‖d‖)
  have h9 : (n : ℝ) * ‖d‖ > R := by
    have h10 : R / ‖d‖ < (n : ℝ) := hn
    have h11 : R < (n : ℝ) * ‖d‖ := by
      calc
        R = (R / ‖d‖) * ‖d‖ := by field_simp [hpos.ne'] <;> ring
        _ < (n : ℝ) * ‖d‖ := by gcongr
    exact h11
  have h12 := h4 n
  linarith

/-- If K is symmetric about z and K ⊆ ellipsoid c A, then K ⊆ ellipsoid z A. -/
lemma subset_ellipsoid_symmetric_center
    {z : E n} (hz : ∀ x : E n, x ∈ K → z + (z - x) ∈ K)
    (c : E n) (A : E n ≃ₗ[ℝ] E n)
    (h_sub : K ⊆ ellipsoid c A) :
    K ⊆ ellipsoid z A := by
  let B := Metric.closedBall (0 : E n) 1
  have hB_conv : Convex ℝ B := (strictConvex_closedBall ℝ (0 : E n) 1).convex
  have hB_sym : ∀ y ∈ B, -y ∈ B := by
    intro y hy
    simpa [B, Metric.mem_closedBall, norm_neg] using hy
  intro x hx
  have h_x_in_E : x ∈ ellipsoid c A := h_sub hx
  rcases h_x_in_E with ⟨y, hy_image, hxy⟩
  rcases hy_image with ⟨u, hu_B, hau⟩
  have h_cAu_x : c +ᵥ A u = x := by
    have h : c +ᵥ y = x := hxy
    have h2 : A u = y := hau
    rw [←h2] at h
    exact h
  have h_au : A u = x - c := by
    have h : c + A u = x := by simpa [vadd_eq_add] using h_cAu_x
    exact eq_sub_of_add_eq' h
  have h_sym : z + (z - x) ∈ K := hz x hx
  have h_sym_in_E : z + (z - x) ∈ ellipsoid c A := h_sub h_sym
  rcases h_sym_in_E with ⟨y', hy'_image, hy'_eq⟩
  rcases hy'_image with ⟨v, hv_B, hav⟩
  have h_cAv_sym : c +ᵥ A v = z + (z - x) := by
    have h : c +ᵥ y' = z + (z - x) := hy'_eq
    have h2 : A v = y' := hav
    rw [←h2] at h
    exact h
  have h_av : A v = z + (z - x) - c := by
    have h : c + A v = z + (z - x) := by simpa [vadd_eq_add] using h_cAv_sym
    exact eq_sub_of_add_eq' h
  have h1 : A (u - v) = (2 : ℝ) • (x - z) := by
    have h_sub : A (u - v) = A u - A v := A.map_sub u v
    rw [h_sub, h_au, h_av]
    simp [two_smul] <;> abel
  have h3' : A.symm (A (u - v)) = u - v := A.symm_apply_apply (u - v)
  rw [h1] at h3'
  have h4' : A.symm ((2 : ℝ) • (x - z)) = u - v := h3'
  have h5' : A.symm ((2 : ℝ) • (x - z)) = (2 : ℝ) • A.symm (x - z) := by
    exact A.symm.map_smul (2 : ℝ) (x - z)
  rw [h5'] at h4'
  have h6' : (2 : ℝ) • A.symm (x - z) = u - v := h4'
  have h7' : A.symm (x - z) = (1 / 2 : ℝ) • (u - v) := by
    have h8' : A.symm (x - z) = (1 / 2 : ℝ) • ((2 : ℝ) • A.symm (x - z)) := by
      simp [smul_smul] <;> ring
    rw [h8', h6'] <;> simp [smul_smul] <;> ring
  have h_neg_v : -v ∈ B := hB_sym v hv_B
  have h_in_B : (1 / 2 : ℝ) • (u - v) ∈ B := by
    have h9 : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • (-v) ∈ B :=
      hB_conv hu_B h_neg_v (by norm_num) (by norm_num) (by norm_num)
    have h10 : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • (-v) = (1 / 2 : ℝ) • (u - v) := by
      have h11 : (1 / 2 : ℝ) • (-v) = -((1 / 2 : ℝ) • v) := by rw [smul_neg]
      rw [h11]
      have h12 : (1 / 2 : ℝ) • u + -((1 / 2 : ℝ) • v) = (1 / 2 : ℝ) • u - (1 / 2 : ℝ) • v := by
        exact (sub_eq_add_neg ((1 / 2 : ℝ) • u) ((1 / 2 : ℝ) • v)).symm
      rw [h12]
      have h13 : (1 / 2 : ℝ) • u - (1 / 2 : ℝ) • v = (1 / 2 : ℝ) • (u - v) := by rw [← smul_sub]
      exact h13
    rw [h10] at h9
    exact h9
  set y_val := A.symm (x - z) with hy_def
  have hy_B : y_val ∈ B := by
    have h_eq : y_val = (1 / 2 : ℝ) • (u - v) := h7'
    rw [h_eq]
    exact h_in_B
  have h_zy : z +ᵥ A y_val = x := by
    have h : A y_val = x - z := A.apply_symm_apply (x - z)
    simp [vadd_eq_add, h] <;> abel
  have h_y_in_S : A y_val ∈ A '' B := Set.mem_image_of_mem A hy_B
  exact ⟨A y_val, h_y_in_S, h_zy⟩

/-- The symmetric center of a convex body equals the center of its outer John ellipsoid.

Takes uniqueness of the outer John ellipsoid as a hypothesis. -/
lemma symmetric_center_eq
    {z : E n} (hz : ∀ x : E n, x ∈ K → z + (z - x) ∈ K)
    (c : E n) (A : E n ≃ₗ[ℝ] E n)
    (hE : IsOuterJohnEllipsoid K c A)
    (h_unique : ∀ (c1 c2 : E n) (A1 A2 : E n ≃ₗ[ℝ] E n),
        IsOuterJohnEllipsoid K c1 A1 → IsOuterJohnEllipsoid K c2 A2 →
        ellipsoid c1 A1 = ellipsoid c2 A2) :
    c = z := by
  let B := Metric.closedBall (0 : E n) 1
  let S := A '' B
  have hB_strict : StrictConvex ℝ B := strictConvex_closedBall ℝ (0 : E n) 1
  have hB_conv : Convex ℝ B := hB_strict.convex
  have hB_sym : ∀ y ∈ B, -y ∈ B := by
    intro y hy
    simpa [B, Metric.mem_closedBall, norm_neg] using hy
  let A_clm : E n →L[ℝ] E n :=
    ⟨A.toLinearMap, LinearMap.continuous_of_finiteDimensional A.toLinearMap⟩
  have hA_cont : Continuous (A : E n → E n) := A_clm.cont
  have hB_bdd : Bornology.IsBounded B := Metric.isBounded_closedBall
  have hS_bdd : Bornology.IsBounded S := hB_bdd.image A_clm
  have hS_nonempty : S.Nonempty := ⟨A 0, by
    apply Set.mem_image_of_mem
    simp [B]⟩

  -- Step 1-3: K ⊆ ellipsoid z A
  have hK_sub : K ⊆ ellipsoid z A := by
    intro x hx
    have h_x_in_E : x ∈ ellipsoid c A := hE.1 hx
    rcases h_x_in_E with ⟨y, hy_image, hxy⟩
    rcases hy_image with ⟨u, hu_B, hau⟩
    have h_cAu_x : c +ᵥ A u = x := by
      have h : c +ᵥ y = x := hxy
      have h2 : A u = y := hau
      rw [←h2] at h
      exact h
    have h_au : A u = x - c := by
      have h : c + A u = x := by simpa [vadd_eq_add] using h_cAu_x
      exact eq_sub_of_add_eq' h
    have h_sym : z + (z - x) ∈ K := hz x hx
    have h_sym_in_E : z + (z - x) ∈ ellipsoid c A := hE.1 h_sym
    rcases h_sym_in_E with ⟨y', hy'_image, hy'_eq⟩
    rcases hy'_image with ⟨v, hv_B, hav⟩
    have h_cAv_sym : c +ᵥ A v = z + (z - x) := by
      have h : c +ᵥ y' = z + (z - x) := hy'_eq
      have h2 : A v = y' := hav
      rw [←h2] at h
      exact h
    have h_av : A v = z + (z - x) - c := by
      have h : c + A v = z + (z - x) := by simpa [vadd_eq_add] using h_cAv_sym
      exact eq_sub_of_add_eq' h
    have h1 : A (u - v) = (2 : ℝ) • (x - z) := by
      have h_sub : A (u - v) = A u - A v := A.map_sub u v
      rw [h_sub, h_au, h_av]
      simp [two_smul] <;> abel
    have h3' : A.symm (A (u - v)) = u - v := A.symm_apply_apply (u - v)
    rw [h1] at h3'
    have h4' : A.symm ((2 : ℝ) • (x - z)) = u - v := h3'
    have h5' : A.symm ((2 : ℝ) • (x - z)) = (2 : ℝ) • A.symm (x - z) := by
      exact A.symm.map_smul (2 : ℝ) (x - z)
    rw [h5'] at h4'
    have h6' : (2 : ℝ) • A.symm (x - z) = u - v := h4'
    have h7' : A.symm (x - z) = (1 / 2 : ℝ) • (u - v) := by
      have h8' : A.symm (x - z) = (1 / 2 : ℝ) • ((2 : ℝ) • A.symm (x - z)) := by
        simp [smul_smul] <;> ring
      rw [h8', h6'] <;> simp [smul_smul] <;> ring
    have h_neg_v : -v ∈ B := hB_sym v hv_B
    have h_in_B : (1 / 2 : ℝ) • (u - v) ∈ B := by
      have h9 : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • (-v) ∈ B :=
        hB_conv hu_B h_neg_v (by norm_num) (by norm_num) (by norm_num)
      have h10 : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • (-v) = (1 / 2 : ℝ) • (u - v) := by
        have h11 : (1 / 2 : ℝ) • (-v) = -((1 / 2 : ℝ) • v) := by rw [smul_neg]
        rw [h11]
        have h12 : (1 / 2 : ℝ) • u + -((1 / 2 : ℝ) • v) = (1 / 2 : ℝ) • u - (1 / 2 : ℝ) • v := by
          exact (sub_eq_add_neg ((1 / 2 : ℝ) • u) ((1 / 2 : ℝ) • v)).symm
        rw [h12]
        have h13 : (1 / 2 : ℝ) • u - (1 / 2 : ℝ) • v = (1 / 2 : ℝ) • (u - v) := by rw [← smul_sub]
        exact h13
      rw [h10] at h9
      exact h9
    set y_val := A.symm (x - z) with hy_def
    have hy_B : y_val ∈ B := by
      have h_eq : y_val = (1 / 2 : ℝ) • (u - v) := h7'
      rw [h_eq]
      exact h_in_B
    have h_zy : z +ᵥ A y_val = x := by
      have h : A y_val = x - z := A.apply_symm_apply (x - z)
      simp [vadd_eq_add, h] <;> abel
    have h_y_in_S : A y_val ∈ S := Set.mem_image_of_mem A hy_B
    exact ⟨A y_val, h_y_in_S, h_zy⟩

  -- Step 4: volume(ellipsoid z A) = volume(ellipsoid c A)
  have h_trans : ellipsoid z A = (z - c) +ᵥ ellipsoid c A := by
    ext y
    simp only [ellipsoid, Set.mem_vadd_set]
    constructor
    · rintro ⟨x, hx, rfl⟩
      let w := c +ᵥ x
      have hw : w ∈ ellipsoid c A := ⟨x, hx, by simp [w]⟩
      refine ⟨w, hw, ?_⟩
      have h : (z - c) +ᵥ w = z +ᵥ x := by
        simp [w, vadd_eq_add] <;> abel
      exact h
    · rintro ⟨w, hw, rfl⟩
      have h1 : ∃ y', y' ∈ A '' B ∧ c +ᵥ y' = w := hw
      rcases h1 with ⟨y', hy'_image, hcw⟩
      have h2 : ∃ x, x ∈ B ∧ A x = y' := by
        simpa [Set.mem_image] using hy'_image
      rcases h2 with ⟨x, hx, hax⟩
      have h3 : (z - c) +ᵥ w = z +ᵥ A x := by
        have h4 : c +ᵥ y' = w := hcw
        rw [←h4, ←hax]
        <;> simp [vadd_eq_add] <;> abel
      exact ⟨A x, Set.mem_image_of_mem A hx, h3.symm⟩
  have h_vol : volume (ellipsoid z A) = volume (ellipsoid c A) := by
    rw [h_trans]
    have h2 : ∀ (a : E n) (s : Set (E n)), volume (a +ᵥ s) = volume s := by
      intro a s
      exact measure_vadd volume a s
    exact h2 (z - c) (ellipsoid c A)

  -- Step 5: ellipsoid z A is also a minimal ellipsoid
  have hE' : IsOuterJohnEllipsoid K z A := by
    refine ⟨hK_sub, fun c' A' hsub => ?_⟩
    rw [h_vol]
    exact hE.2 c' A' hsub

  -- Step 6: uniqueness gives ellipsoid c A = ellipsoid z A
  have h_eq : ellipsoid c A = ellipsoid z A :=
    h_unique c z A A hE hE'

  -- Step 7: (c-z) + S = S, hence c = z
  have h1 : c +ᵥ S = z +ᵥ S := by
    simpa [ellipsoid] using h_eq
  have h_S_eq : (c - z) +ᵥ S = S := by
    ext y
    simp only [Set.mem_vadd_set]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h2 : c +ᵥ x ∈ c +ᵥ S := Set.mem_image_of_mem _ hx
      rw [h1] at h2
      rcases h2 with ⟨w, hw, hzw⟩
      have h3 : z + w = c + x := by simpa [vadd_eq_add] using hzw
      have h4 : w = (c - z) + x := by
        have h5 : z + w = c + x := h3
        have h6 : w = (c + x) - z := eq_sub_of_add_eq' h5
        rw [h6]
        have h7 : (c + x) - z = (c - z) + x := by
          simp [sub_eq_add_neg] <;> abel
        exact h7
      rw [h4] at hw
      exact hw
    · intro hy
      have h2 : z +ᵥ y ∈ z +ᵥ S := Set.mem_image_of_mem _ hy
      rw [←h1] at h2
      rcases h2 with ⟨w, hw, hcw⟩
      have h3 : c + w = z + y := by simpa [vadd_eq_add] using hcw
      have h4 : (c - z) + w = y := by
        have h5 : c + w = z + y := h3
        have h6 : w = (z + y) - c := eq_sub_of_add_eq' h5
        rw [h6]
        have h7 : (c - z) + ((z + y) - c) = y := by
          simp [sub_eq_add_neg] <;> abel
        exact h7
      exact ⟨w, hw, h4⟩
  have h_cz : c - z = 0 := bounded_vadd_invariant_eq_zero hS_bdd hS_nonempty h_S_eq
  simpa [sub_eq_zero] using h_cz

/-- Norm identity: ‖y - (1/2)•w‖² = (1/2)‖y‖² + (1/2)‖y-w‖² - (1/4)‖w‖². -/
private lemma half_norm_identity (y w : E n) :
    ‖y - (1 / 2 : ℝ) • w‖ ^ 2 =
    (1 / 2 : ℝ) * ‖y‖ ^ 2 + (1 / 2 : ℝ) * ‖y - w‖ ^ 2 - (1 / 4 : ℝ) * ‖w‖ ^ 2 := by
  set wh : E n := (1 / 2 : ℝ) • w with hwh
  have h1 : ‖y - wh‖ ^ 2 = ‖y‖ ^ 2 - 2 * inner ℝ y wh + ‖wh‖ ^ 2 :=
    norm_sub_sq_real y wh
  have h2 : inner ℝ y wh = (1 / 2 : ℝ) * inner ℝ y w := by
    simp [hwh, inner_smul_right] <;> ring
  have h3 : ‖wh‖ ^ 2 = (1 / 4 : ℝ) * ‖w‖ ^ 2 := by
    simp [hwh, norm_smul, abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num)] <;> ring
  have h4 : ‖y - w‖ ^ 2 = ‖y‖ ^ 2 - 2 * inner ℝ y w + ‖w‖ ^ 2 := norm_sub_sq_real y w
  rw [h1, h2, h3]
  linarith [h4]

/-- Direct proof that symmetric center equals John ellipsoid center, without uniqueness. -/
lemma symmetric_center_eq_direct (hn : 0 < n)
    {z : E n} (hz : ∀ x : E n, x ∈ K → z + (z - x) ∈ K)
    (c : E n) (A : E n ≃ₗ[ℝ] E n)
    (hE : IsOuterJohnEllipsoid K c A)
    (hK : IsConvexBody K) :
    c = z := by
  let B := Metric.closedBall (0 : E n) 1
  have hB_conv : Convex ℝ B := convex_closedBall (0 : E n) 1
  have hB_sym : ∀ y ∈ B, -y ∈ B := by
    intro y hy
    simpa [B, Metric.mem_closedBall, norm_neg] using hy
  let half : ℝ := 1 / 2

  -- Step 1: K ⊆ ellipsoid z A
  have hK_sub_z : K ⊆ ellipsoid z A := by
    intro x hx
    have h_x_in_E : x ∈ ellipsoid c A := hE.1 hx
    rcases h_x_in_E with ⟨y, hy_image, hxy⟩
    rcases hy_image with ⟨u, hu_B, hau⟩
    have h_cAu_x : c +ᵥ A u = x := by
      have h : c +ᵥ y = x := hxy
      have h2 : A u = y := hau
      rw [←h2] at h
      exact h
    have h_au : A u = x - c := by
      have h : c + A u = x := by simpa [vadd_eq_add] using h_cAu_x
      exact eq_sub_of_add_eq' h
    have h_sym : z + (z - x) ∈ K := hz x hx
    have h_sym_in_E : z + (z - x) ∈ ellipsoid c A := hE.1 h_sym
    rcases h_sym_in_E with ⟨y', hy'_image, hy'_eq⟩
    rcases hy'_image with ⟨v, hv_B, hav⟩
    have h_cAv_sym : c +ᵥ A v = z + (z - x) := by
      have h : c +ᵥ y' = z + (z - x) := hy'_eq
      have h2 : A v = y' := hav
      rw [←h2] at h
      exact h
    have h_av : A v = z + (z - x) - c := by
      have h : c + A v = z + (z - x) := by simpa [vadd_eq_add] using h_cAv_sym
      exact eq_sub_of_add_eq' h
    have h1 : A (u - v) = (2 : ℝ) • (x - z) := by
      have h_sub : A (u - v) = A u - A v := A.map_sub u v
      rw [h_sub, h_au, h_av] <;> simp [two_smul] <;> abel
    have h3' : A.symm (A (u - v)) = u - v := A.symm_apply_apply (u - v)
    rw [h1] at h3'
    have h4' : A.symm ((2 : ℝ) • (x - z)) = u - v := h3'
    have h5' : A.symm ((2 : ℝ) • (x - z)) = (2 : ℝ) • A.symm (x - z) := by
      exact A.symm.map_smul (2 : ℝ) (x - z)
    rw [h5'] at h4'
    have h6' : (2 : ℝ) • A.symm (x - z) = u - v := h4'
    have h7' : A.symm (x - z) = half • (u - v) := by
      have h8' : A.symm (x - z) = half • ((2 : ℝ) • A.symm (x - z)) := by
        simp [half, smul_smul] <;> ring
      rw [h8', h6'] <;> simp [half, smul_smul] <;> ring
    have h_neg_v : -v ∈ B := hB_sym v hv_B
    have h_in_B : half • (u - v) ∈ B := by
      have h9 : half • u + half • (-v) ∈ B :=
        hB_conv hu_B h_neg_v (by norm_num) (by norm_num) (by norm_num)
      have h10 : half • u + half • (-v) = half • (u - v) := by
        have h11 : half • (-v) = - (half • v) := by rw [smul_neg]
        have h12 : half • u + half • (-v) = half • u - half • v := by
          rw [h11] <;> exact sub_eq_add_neg _ _
        rw [h12, ←smul_sub]
      rw [h10] at h9
      exact h9
    set y_val := A.symm (x - z) with hy_def
    have hy_B : y_val ∈ B := by
      have h_eq : y_val = half • (u - v) := h7'
      rw [h_eq]
      exact h_in_B
    have h_zy : z +ᵥ A y_val = x := by
      have h : A y_val = x - z := A.apply_symm_apply (x - z)
      simp [vadd_eq_add, h] <;> abel
    have h_y_in_S : A y_val ∈ A '' B := Set.mem_image_of_mem A hy_B
    exact ⟨A y_val, h_y_in_S, h_zy⟩

  -- Step 2: Suppose c ≠ z, derive contradiction
  by_contra h
  let v : E n := z - c
  have hv_ne_zero : v ≠ 0 := by
    have h' : z ≠ c := by
      intro h''
      exact h h''.symm
    simpa [v, sub_eq_zero] using h'
  let w : E n := A.symm v
  have hw_ne_zero : w ≠ 0 := by
    intro h_w
    have h_v : v = 0 := by
      have h : A w = v := A.apply_symm_apply v
      rw [h_w] at h
      have h' : A (0 : E n) = 0 := by simp
      rw [h'] at h
      exact h.symm
    exact hv_ne_zero h_v
  let wh : E n := half • w

  -- For all x ∈ K: ‖A.symm(x-c)‖ ≤ 1 and ‖A.symm(x-c) - w‖ ≤ 1
  have h1 : ∀ x ∈ K, ‖A.symm (x - c)‖ ≤ 1 := by
    intro x hx
    have h_in : x ∈ ellipsoid c A := hE.1 hx
    rcases h_in with ⟨_, ⟨u, hu, rfl⟩, h_eq⟩
    have h2 : c + A u = x := by simpa [vadd_eq_add] using h_eq
    have h3 : A u = x - c := eq_sub_of_add_eq' h2
    have h4 : A.symm (x - c) = u := by
      have h5 : A.symm (A u) = u := A.symm_apply_apply u
      rw [h3] at h5
      exact h5
    rw [h4]
    simpa [B, Metric.mem_closedBall] using hu
  have h2 : ∀ x ∈ K, ‖A.symm (x - c) - w‖ ≤ 1 := by
    intro x hx
    have h_in : x ∈ ellipsoid z A := hK_sub_z hx
    rcases h_in with ⟨_, ⟨u, hu, rfl⟩, h_eq⟩
    have h2 : z + A u = x := by simpa [vadd_eq_add] using h_eq
    have h3 : A u = x - z := eq_sub_of_add_eq' h2
    have h4 : A.symm (x - z) = u := by
      have h5 : A.symm (A u) = u := A.symm_apply_apply u
      rw [h3] at h5
      exact h5
    have h6 : A.symm (x - c) - w = A.symm (x - z) := by
      have h7 : x - c = (x - z) + v := by simp [v] <;> abel
      rw [h7]
      have h8 : A.symm ((x - z) + v) = A.symm (x - z) + A.symm v := A.symm.map_add (x - z) v
      rw [h8]
      <;> simp [w] <;> abel
    rw [h6, h4]
    simpa [B, Metric.mem_closedBall] using hu

  -- ‖w‖ ≤ 2
  have hK_nonempty : K.Nonempty := hK.2.2.mono interior_subset
  rcases hK_nonempty with ⟨x0, hx0⟩
  let y0 := A.symm (x0 - c)
  have h_y0_norm : ‖y0‖ ≤ 1 := h1 x0 hx0
  have h_y0w_norm : ‖y0 - w‖ ≤ 1 := h2 x0 hx0
  have h_w_le_2 : ‖w‖ ≤ 2 := by
    have h : ‖w‖ = ‖y0 - (y0 - w)‖ := by abel_nf
    rw [h]
    calc ‖y0 - (y0 - w)‖ ≤ ‖y0‖ + ‖y0 - w‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith

  -- If ‖w‖ = 2, then K is a singleton, contradiction with nonempty interior
  have h_w_lt_2 : ‖w‖ < 2 := by
    by_contra h'
    have h_eq : ‖w‖ = 2 := by linarith
    have h_all : ∀ x ∈ K, A.symm (x - c) = wh := by
      intro x hx
      let y := A.symm (x - c)
      have hy1 : ‖y‖ ≤ 1 := h1 x hx
      have hy2 : ‖y - w‖ ≤ 1 := h2 x hx
      have h_id : ‖y - wh‖ ^ 2 = half * ‖y‖ ^ 2 + half * ‖y - w‖ ^ 2 - (1 / 4 : ℝ) * ‖w‖ ^ 2 :=
        half_norm_identity y w
      have h_bound : ‖y - wh‖ ^ 2 ≤ 0 := by
        rw [h_id, h_eq]
        have h9 : ‖y‖ ^ 2 ≤ 1 := by
          have h_pos : 0 ≤ ‖y‖ := by positivity
          calc ‖y‖ ^ 2 ≤ 1 ^ 2 := by gcongr
            _ = 1 := by norm_num
        have h10 : ‖y - w‖ ^ 2 ≤ 1 := by
          have h_pos : 0 ≤ ‖y - w‖ := by positivity
          calc ‖y - w‖ ^ 2 ≤ 1 ^ 2 := by gcongr
            _ = 1 := by norm_num
        have h_half_pos : 0 < half := by norm_num
        have h11 : half * ‖y‖ ^ 2 ≤ half := by
          have h : half * ‖y‖ ^ 2 ≤ half * 1 := mul_le_mul_of_nonneg_left h9 h_half_pos.le
          simpa using h
        have h12 : half * ‖y - w‖ ^ 2 ≤ half := by
          have h : half * ‖y - w‖ ^ 2 ≤ half * 1 := mul_le_mul_of_nonneg_left h10 h_half_pos.le
          simpa using h
        have h13 : half * ‖y‖ ^ 2 + half * ‖y - w‖ ^ 2 ≤ 1 := by
          calc half * ‖y‖ ^ 2 + half * ‖y - w‖ ^ 2 ≤ half + half := by gcongr
            _ = 1 := by norm_num
        linarith [h13]
      have h_nonneg : 0 ≤ ‖y - wh‖ ^ 2 := by positivity
      have h_eq2 : ‖y - wh‖ ^ 2 = 0 := by linarith
      have h_eq3 : ‖y - wh‖ = 0 := by
        simpa using h_eq2
      have h_eq4 : y - wh = 0 := by simpa [norm_eq_zero] using h_eq3
      exact sub_eq_zero.mp h_eq4
    have h_singleton : ∀ x ∈ K, x = c + A wh := by
      intro x hx
      have h5 : A.symm (x - c) = wh := h_all x hx
      have h6 : A (A.symm (x - c)) = A wh := by rw [h5]
      have h7 : A (A.symm (x - c)) = x - c := A.apply_symm_apply (x - c)
      rw [h7] at h6
      have h8 : x - c = A wh := h6
      have h9 : x = c + A wh := by
        calc x = c + (x - c) := by abel
          _ = c + A wh := by rw [h8]
      exact h9
    have hK_sub_singleton : K ⊆ {c + A wh} := by
      intro x hx
      exact Set.mem_singleton_iff.mpr (h_singleton x hx)
    -- Show interior of singleton is empty using nontriviality of E n
    let p := c + A wh
    have h_i : ∃ (i : Fin n), True := ⟨⟨0, hn⟩, trivial⟩
    rcases h_i with ⟨i, _⟩
    let v' : E n := EuclideanSpace.single i 1
    have hv' : v' ≠ 0 := by
      have hvi : v' i = 1 := by
        simp [v', EuclideanSpace.single_apply] <;> norm_num
      intro h
      rw [h] at hvi
      simp at hvi
    have h2 : interior ({p} : Set (E n)) = ∅ := by
      by_contra h3
      have h4 : (interior ({p} : Set (E n))).Nonempty := Set.nonempty_iff_ne_empty.mpr h3
      rcases h4 with ⟨q, hq⟩
      rcases Metric.isOpen_iff.mp isOpen_interior q hq with ⟨ε, hε_pos, hball⟩
      have hball' : Metric.ball q ε ⊆ ({p} : Set (E n)) := by
        intro z hz
        exact interior_subset (hball hz)
      have hq_in : q ∈ interior ({p} : Set (E n)) := hball (Metric.mem_ball_self hε_pos)
      have hq_eq : q = p := by
        have h : q ∈ ({p} : Set (E n)) := interior_subset hq_in
        simpa using h
      let z' : E n := q + (ε / 2) • v'
      have hz'_ball : z' ∈ Metric.ball q ε := by
        have h_dist : dist z' q = ‖(ε / 2) • v'‖ := by
          simp [z', dist_eq_norm] <;> rfl
        rw [Metric.mem_ball, h_dist]
        have h8 : ‖(ε / 2) • v'‖ = (ε / 2) * ‖v'‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)] <;> ring
        rw [h8]
        have h_norm_v' : ‖v'‖ = 1 := by
          simp [v', EuclideanSpace.norm_eq, Finset.sum_ite, Finset.mem_univ, if_true]
          <;> norm_num
        rw [h_norm_v']
        have h10 : (ε / 2) * (1 : ℝ) < ε := by linarith
        exact h10
      have hz'_in : z' ∈ ({p} : Set (E n)) := hball' hz'_ball
      have hz'_eq : z' = p := by simpa using hz'_in
      have h10 : (ε / 2) • v' = 0 := by
        simpa [z', hq_eq] using hz'_eq
      have h11 : v' = 0 := by
        simpa [smul_eq_zero, hε_pos.ne'] using h10
      exact hv' h11
    have h1 : interior K ⊆ interior ({p} : Set (E n)) := interior_mono hK_sub_singleton
    rw [h2] at h1
    have h_interior_empty : interior K = ∅ := by simpa using h1
    rcases hK.2.2 with ⟨x, hx⟩
    rw [h_interior_empty] at hx
    exact hx

  -- r = sqrt(1 - ‖w‖²/4), 0 < r < 1
  have h_pos1 : 0 < 1 - ‖w‖ ^ 2 / 4 := by
    have h_nonneg_w : 0 ≤ ‖w‖ := by positivity
    have h : ‖w‖ ^ 2 < 4 := by
      have h' : ‖w‖ < 2 := h_w_lt_2
      calc ‖w‖ ^ 2 < 2 ^ 2 := by gcongr
        _ = 4 := by norm_num
    linarith
  let r : ℝ := Real.sqrt (1 - ‖w‖ ^ 2 / 4)
  have h_r2 : r ^ 2 = 1 - ‖w‖ ^ 2 / 4 := Real.sq_sqrt (by linarith)
  have hr_pos : 0 < r := Real.sqrt_pos.mpr h_pos1
  have hr_lt_one : r < 1 := by
    have h : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne_zero
    have h_r2_lt_one : r ^ 2 < 1 := by
      rw [h_r2]
      have h_pos_w2 : 0 < ‖w‖ ^ 2 / 4 := by positivity
      linarith
    have hr_pos' : 0 ≤ r := by positivity
    nlinarith

  -- Scaled linear equiv A' = r • A
  let scale_lm : E n →L[ℝ] E n := r • (1 : E n →L[ℝ] E n)
  let scale : E n ≃ₗ[ℝ] E n :=
    { toFun := fun x : E n => r • x
      invFun := fun x : E n => (1 / r) • x
      left_inv := fun x => by
        change (1 / r) • (r • x) = x
        have h : (1 / r) • (r • x) = ((1 / r) * r) • x := by rw [smul_smul]
        rw [h]
        have h2 : (1 / r) * r = 1 := by field_simp [hr_pos.ne'] <;> ring
        rw [h2, one_smul]
      right_inv := fun x => by
        change r • ((1 / r) • x) = x
        have h : r • ((1 / r) • x) = (r * (1 / r)) • x := by rw [smul_smul]
        rw [h]
        have h2 : r * (1 / r) = 1 := by field_simp [hr_pos.ne'] <;> ring
        rw [h2, one_smul]
      map_add' := fun x y => smul_add r x y
      map_smul' := fun s x => by
        simp [smul_comm s r] <;> ring }
  have h_scale_eq : (scale : E n →ₗ[ℝ] E n) = scale_lm := by
    ext x
    simp [scale, scale_lm] <;> rfl
  let A' : E n ≃ₗ[ℝ] E n := A.trans scale
  let c' : E n := c + A wh

  -- K ⊆ ellipsoid c' A'
  have hK_sub' : K ⊆ ellipsoid c' A' := by
    intro x hx
    let y := A.symm (x - c)
    have hy1 : ‖y‖ ≤ 1 := h1 x hx
    have hy2 : ‖y - w‖ ≤ 1 := h2 x hx
    have h_id : ‖y - wh‖ ^ 2 = half * ‖y‖ ^ 2 + half * ‖y - w‖ ^ 2 - (1 / 4 : ℝ) * ‖w‖ ^ 2 :=
      half_norm_identity y w
    have h_bound : ‖y - wh‖ ^ 2 ≤ r ^ 2 := by
      rw [h_id, h_r2]
      have h9 : ‖y‖ ^ 2 ≤ 1 := by
        have h_pos : 0 ≤ ‖y‖ := by positivity
        calc ‖y‖ ^ 2 ≤ 1 ^ 2 := by gcongr
          _ = 1 := by norm_num
      have h10 : ‖y - w‖ ^ 2 ≤ 1 := by
        have h_pos : 0 ≤ ‖y - w‖ := by positivity
        calc ‖y - w‖ ^ 2 ≤ 1 ^ 2 := by gcongr
          _ = 1 := by norm_num
      have h_half_pos : 0 < half := by norm_num
      have h11 : half * ‖y‖ ^ 2 ≤ half * 1 := mul_le_mul_of_nonneg_left h9 h_half_pos.le
      have h11' : half * ‖y‖ ^ 2 ≤ half := by simpa using h11
      have h12 : half * ‖y - w‖ ^ 2 ≤ half * 1 := mul_le_mul_of_nonneg_left h10 h_half_pos.le
      have h12' : half * ‖y - w‖ ^ 2 ≤ half := by simpa using h12
      have h13 : half * ‖y‖ ^ 2 + half * ‖y - w‖ ^ 2 ≤ 1 := by
        calc half * ‖y‖ ^ 2 + half * ‖y - w‖ ^ 2 ≤ half + half := by gcongr
          _ = 1 := by norm_num
      have h_goal : half * ‖y‖ ^ 2 + half * ‖y - w‖ ^ 2 - (1 / 4 : ℝ) * ‖w‖ ^ 2 ≤ 1 - ‖w‖ ^ 2 / 4 := by
        linarith [h13]
      exact h_goal
    have h_norm : ‖y - wh‖ ≤ r := by
      have h7 : 0 ≤ ‖y - wh‖ := by positivity
      have h8 : 0 ≤ r := by positivity
      have h9 : |‖y - wh‖| ≤ |r| := sq_le_sq.mp h_bound
      have h10 : ‖y - wh‖ ≤ r := by
        rwa [abs_of_nonneg h7, abs_of_nonneg h8] at h9
      exact h10
    let u : E n := y - wh
    have hu_norm : ‖u‖ ≤ r := h_norm
    let u' : E n := (1 / r) • u
    have h_ineq : ‖u'‖ ≤ 1 := by
      have h_norm_u' : ‖u'‖ = (1 / r) * ‖u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)] <;> ring
      rw [h_norm_u']
      calc (1 / r) * ‖u‖ ≤ (1 / r) * r := by gcongr
        _ = 1 := by field_simp [hr_pos.ne'] <;> ring
    have hu'_in_B : u' ∈ B := by
      simpa [B, Metric.mem_closedBall] using h_ineq
    have h_A'u' : A' u' = A u := by
      have h1 : A' u' = scale (A u') := by rfl
      rw [h1]
      have h2 : A u' = (1 / r) • A u := by
        have h3 : A u' = A ((1 / r) • u) := by rfl
        rw [h3, A.map_smul] <;> ring
      rw [h2]
      have h4 : scale ((1 / r) • A u) = r • ((1 / r) • A u) := by rfl
      rw [h4]
      have h5 : r • ((1 / r) • A u) = (r * (1 / r)) • A u := by rw [smul_smul]
      rw [h5]
      have h6 : r * (1 / r) = 1 := by field_simp [hr_pos.ne'] <;> ring
      rw [h6, one_smul]
    have h_main : c' +ᵥ A' u' = x := by
      simp [c', h_A'u', vadd_eq_add]
      have h10 : A y = x - c := A.apply_symm_apply (x - c)
      have h11 : A u = A y - A wh := A.map_sub y wh
      rw [h11, h10] <;> abel
    exact ⟨A' u', Set.mem_image_of_mem A' hu'_in_B, h_main⟩

  -- Volume comparison
  have h_finrank : Module.finrank ℝ (E n) = n := by
    simpa [E] using finrank_euclideanSpace (R := ℝ) (ι := Fin n)
  have h_det_scale : LinearMap.det (scale : E n →ₗ[ℝ] E n) = r ^ n := by
    rw [h_scale_eq]
    have h : (scale_lm : E n →ₗ[ℝ] E n) = r • (1 : E n →ₗ[ℝ] E n) := by rfl
    rw [h, LinearMap.det_smul, h_finrank]
    <;> simp
  have h_det' : LinearMap.det (A' : E n →ₗ[ℝ] E n) = r ^ n * LinearMap.det (A : E n →ₗ[ℝ] E n) := by
    have h : (A' : E n →ₗ[ℝ] E n) = (scale : E n →ₗ[ℝ] E n).comp (A : E n →ₗ[ℝ] E n) := by rfl
    rw [h, LinearMap.det_comp, h_det_scale] <;> ring
  have h_abs' : |LinearMap.det (A' : E n →ₗ[ℝ] E n)| = r ^ n * |LinearMap.det (A : E n →ₗ[ℝ] E n)| := by
    rw [h_det', abs_mul]
    <;> rw [abs_of_nonneg (by positivity)]
  have h_rn_lt_one : r ^ n < 1 := by
    have h1 : 0 ≤ r := by positivity
    have h2 : r < 1 := hr_lt_one
    have h3 : 0 < n := hn
    have h4 : r ^ n < 1 ^ n := by gcongr
    simpa using h4
  have h_detA_pos : 0 < |LinearMap.det (A : E n →ₗ[ℝ] E n)| := by
    have h : IsUnit (LinearMap.det (A : E n →ₗ[ℝ] E n)) := LinearEquiv.isUnit_det' A
    exact abs_pos.mpr h.ne_zero
  have h_abs_lt : |LinearMap.det (A' : E n →ₗ[ℝ] E n)| < |LinearMap.det (A : E n →ₗ[ℝ] E n)| := by
    rw [h_abs']
    have h4 : r ^ n * |LinearMap.det (A : E n →ₗ[ℝ] E n)| < 1 * |LinearMap.det (A : E n →ₗ[ℝ] E n)| := by
      gcongr <;> linarith
    simpa using h4

  -- Contradiction
  have h_vol_le : volume (ellipsoid c' A') ≤ volume (ellipsoid c A) :=
    (volume_ellipsoid_le_iff c' A' c A).mpr (by linarith)
  have h_min : volume (ellipsoid c A) ≤ volume (ellipsoid c' A') := hE.2 c' A' hK_sub'
  have h_vol_eq : volume (ellipsoid c' A') = volume (ellipsoid c A) := le_antisymm h_vol_le h_min
  have h_abs_eq : |LinearMap.det (A' : E n →ₗ[ℝ] E n)| = |LinearMap.det (A : E n →ₗ[ℝ] E n)| := by
    have h1 : |LinearMap.det (A' : E n →ₗ[ℝ] E n)| ≤ |LinearMap.det (A : E n →ₗ[ℝ] E n)| :=
      (volume_ellipsoid_le_iff c' A' c A).mp h_vol_le
    have h2 : |LinearMap.det (A : E n →ₗ[ℝ] E n)| ≤ |LinearMap.det (A' : E n →ₗ[ℝ] E n)| :=
      (volume_ellipsoid_le_iff c A c' A').mp h_vol_eq.symm.le
    exact le_antisymm h1 h2
  linarith [h_abs_lt, h_abs_eq]

end JohnEllipsoid
