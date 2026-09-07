import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Tactic

/-!
# Neighbor packing bound for WZ1 balanced cover

For a grid partition of R^3 into cubes of side `s = 2*rho/sqrt 3` (diameter `2*rho`),
the number of cubes whose representatives lie within `6*rho` of a given cube's
representative is at most `13^3 = 2197 < 10000`.
-/

noncomputable section

namespace Kakeya.Assouad

open Finset

/-- If `|x - y| < N` for real `x, y` and positive integer `N`, then `|floor x - floor y| <= N`. -/
lemma wz1_abs_floor_sub_lt_le {x y : ℝ} {N : ℕ}
    (_hN : 0 < N) (h : |x - y| < (N : ℝ)) :
    |(⌊x⌋ : ℤ) - ⌊y⌋| ≤ (N : ℤ) := by
  have h1 : (⌊x⌋ : ℝ) - (⌊y⌋ : ℝ) < (N : ℝ) + 1 := by
    have hfx : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
    have hyf : y - (⌊y⌋ : ℝ) < 1 := by linarith [Int.lt_floor_add_one y]
    have hxy : x - y ≤ |x - y| := le_abs_self (x - y)
    linarith
  have h2 : (⌊y⌋ : ℝ) - (⌊x⌋ : ℝ) < (N : ℝ) + 1 := by
    have hfy : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
    have hxf : x - (⌊x⌋ : ℝ) < 1 := by linarith [Int.lt_floor_add_one x]
    have hyx : y - x ≤ |y - x| := le_abs_self (y - x)
    have h_abs : |y - x| = |x - y| := abs_sub_comm y x
    linarith
  have h3 : (⌊x⌋ : ℤ) - ⌊y⌋ ≤ (N : ℤ) := by
    by_contra h4
    have h5 : (⌊x⌋ : ℤ) - ⌊y⌋ > (N : ℤ) := by omega
    have h6 : ((⌊x⌋ : ℝ) - (⌊y⌋ : ℝ)) ≥ (N : ℝ) + 1 := by exact_mod_cast h5
    linarith
  have h4 : (⌊y⌋ : ℤ) - ⌊x⌋ ≤ (N : ℤ) := by
    by_contra h5
    have h6 : (⌊y⌋ : ℤ) - ⌊x⌋ > (N : ℤ) := by omega
    have h7 : ((⌊y⌋ : ℝ) - (⌊x⌋ : ℝ)) ≥ (N : ℝ) + 1 := by exact_mod_cast h6
    linarith
  have h5 : -(N : ℤ) ≤ (⌊x⌋ : ℤ) - ⌊y⌋ := by
    have h6 : (⌊y⌋ : ℤ) - ⌊x⌋ ≤ (N : ℤ) := h4
    omega
  exact abs_le.mpr ⟨h5, h3⟩

/-- Grid index of a point at scale `s`. -/
def gridIndex (s : ℝ) (p : Point3) : ℤ × ℤ × ℤ :=
  (⌊(p 0) / s⌋, ⌊(p 1) / s⌋, ⌊(p 2) / s⌋)

/-- Cardinality of an integer interval of length 12 is 13. -/
lemma card_Icc_13 (z : ℤ) : (Icc (z - 6) (z + 6)).card = 13 := by
  let f : ℤ → ℤ := fun x => x - (z - 6)
  have h_inj : Set.InjOn f (Icc (z - 6) (z + 6)) := by
    intro a _ b _ h
    simpa [f] using h
  have h_eq : (Icc (z - 6) (z + 6)).image f = Icc (0 : ℤ) 12 := by
    ext y
    simp only [Finset.mem_image, Finset.mem_Icc, f]
    constructor
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      constructor <;> omega
    · rintro ⟨hy1, hy2⟩
      refine ⟨y + (z - 6), ⟨by omega, by omega⟩, by omega⟩
  have h_card : (Icc (z - 6) (z + 6)).card = (Icc (0 : ℤ) 12).card := by
    rw [←h_eq, Finset.card_image_of_injOn h_inj]
  rw [h_card]
  <;> decide

/--
Neighbor packing bound for a grid partition.

If cells are indexed by distinct grid cubes of side `s = 2*rho/sqrt 3`, then at most
`13^3 = 2197` cells have representatives within `6*rho` of a given cell's representative.
-/
lemma neighbor_packing_bound
    {rho : ℝ} (hrho : 0 < rho)
    {cellCount : ℕ}
    (representative : Fin cellCount → Point3)
    (h_inj : Function.Injective
      (fun d : Fin cellCount =>
        gridIndex (2 * rho / Real.sqrt 3) (representative d)))
    (c : Fin cellCount) :
    (Finset.univ.filter fun d : Fin cellCount =>
      dist (representative c) (representative d) ≤ 6 * rho).card ≤ 10000 := by
  set s : ℝ := 2 * rho / Real.sqrt 3 with hs
  have hs_pos : 0 < s := by positivity
  have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h_ratio : 6 * rho / s = 3 * Real.sqrt 3 := by
    rw [hs]
    field_simp [hsqrt3_pos.ne'] <;> ring
  have h3sqrt3_lt_6 : 3 * Real.sqrt 3 < 6 := by
    have h : Real.sqrt 3 < 2 := Real.sqrt_lt' (by norm_num) |>.mpr (by norm_num)
    linarith
  set gc : ℤ × ℤ × ℤ := gridIndex s (representative c) with hgc
  let allowed : Finset (ℤ × ℤ × ℤ) :=
    (Icc (gc.1 - 6) (gc.1 + 6)) ×ˢ
    (Icc (gc.2.1 - 6) (gc.2.1 + 6)) ×ˢ
    (Icc (gc.2.2 - 6) (gc.2.2 + 6))
  have h_allowed_card : allowed.card = 2197 := by
    have h1 : allowed.card =
        ((Icc (gc.1 - 6) (gc.1 + 6)).card *
         ((Icc (gc.2.1 - 6) (gc.2.1 + 6)).card *
          (Icc (gc.2.2 - 6) (gc.2.2 + 6)).card)) := by
      simp [allowed, Finset.card_product]
    rw [h1, card_Icc_13 gc.1, card_Icc_13 gc.2.1, card_Icc_13 gc.2.2]
  have h_coord_bound : ∀ (x y : Point3),
      dist x y ≤ 6 * rho →
      ∀ k : Fin 3, |(x k / s) - (y k / s)| < 6 := by
    intro x y hdist k
    have h1 : |x k - y k| ≤ dist x y := PiLp.dist_apply_le x y k
    have h2 : |x k - y k| ≤ 6 * rho := h1.trans hdist
    have h3 : |(x k - y k) / s| ≤ 6 * rho / s := by
      calc
        |(x k - y k) / s|
          = |x k - y k| / s := by rw [abs_div, abs_of_pos hs_pos]
        _ ≤ (6 * rho) / s := by gcongr
        _ = 6 * rho / s := by ring
    have h4 : (x k / s) - (y k / s) = (x k - y k) / s := by rw [sub_div]
    rw [h4]
    rw [h_ratio] at h3
    exact h3.trans_lt h3sqrt3_lt_6
  have h_main : ∀ d ∈ Finset.univ,
      dist (representative c) (representative d) ≤ 6 * rho →
        gridIndex s (representative d) ∈ allowed := by
    intro d _ hdist
    have h0 := h_coord_bound (representative c) (representative d) hdist 0
    have h1 := h_coord_bound (representative c) (representative d) hdist 1
    have h2 := h_coord_bound (representative c) (representative d) hdist 2
    have hf0 := wz1_abs_floor_sub_lt_le (N := 6) (by norm_num) h0
    have hf1 := wz1_abs_floor_sub_lt_le (N := 6) (by norm_num) h1
    have hf2 := wz1_abs_floor_sub_lt_le (N := 6) (by norm_num) h2
    have hgc1 : gc.1 = ⌊(representative c) 0 / s⌋ := by simp [hgc, gridIndex]
    have hgc2 : gc.2.1 = ⌊(representative c) 1 / s⌋ := by simp [hgc, gridIndex]
    have hgc3 : gc.2.2 = ⌊(representative c) 2 / s⌋ := by simp [hgc, gridIndex]
    have hfa0 : -(6 : ℤ) ≤ ⌊(representative c) 0 / s⌋ - ⌊(representative d) 0 / s⌋ :=
      (abs_le.mp hf0).1
    have hfb0 : ⌊(representative c) 0 / s⌋ - ⌊(representative d) 0 / s⌋ ≤ (6 : ℤ) :=
      (abs_le.mp hf0).2
    have hfa1 : -(6 : ℤ) ≤ ⌊(representative c) 1 / s⌋ - ⌊(representative d) 1 / s⌋ :=
      (abs_le.mp hf1).1
    have hfb1 : ⌊(representative c) 1 / s⌋ - ⌊(representative d) 1 / s⌋ ≤ (6 : ℤ) :=
      (abs_le.mp hf1).2
    have hfa2 : -(6 : ℤ) ≤ ⌊(representative c) 2 / s⌋ - ⌊(representative d) 2 / s⌋ :=
      (abs_le.mp hf2).1
    have hfb2 : ⌊(representative c) 2 / s⌋ - ⌊(representative d) 2 / s⌋ ≤ (6 : ℤ) :=
      (abs_le.mp hf2).2
    simp only [gridIndex, allowed, Finset.mem_product, Finset.mem_Icc]
    <;> simp only [hgc1, hgc2, hgc3] at * <;> omega
  let S := Finset.univ.filter fun d : Fin cellCount =>
    dist (representative c) (representative d) ≤ 6 * rho
  have h_image : S.image (fun d => gridIndex s (representative d)) ⊆ allowed := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨d, hd, rfl⟩
    exact h_main d (Finset.mem_univ d) (Finset.mem_filter.mp hd).2
  have h_card_image : (S.image (fun d => gridIndex s (representative d))).card ≤ allowed.card :=
    Finset.card_le_card h_image
  have h_inj_on : Set.InjOn (fun d : Fin cellCount => gridIndex s (representative d)) S :=
    fun _ _ _ _ h => h_inj h
  have h_card_S : S.card = (S.image (fun d => gridIndex s (representative d))).card := by
    rw [Finset.card_image_of_injOn h_inj_on]
  rw [h_card_S]
  calc
    (S.image (fun d => gridIndex s (representative d))).card ≤ allowed.card := h_card_image
    _ = 2197 := h_allowed_card
    _ ≤ 10000 := by norm_num

end Kakeya.Assouad
