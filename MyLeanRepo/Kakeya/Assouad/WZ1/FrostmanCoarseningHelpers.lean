import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Int.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Nat.Cast.Basic

/-!
# Helper lemmas for WZ1 Frostman coarsening (Lemma 48)

1. Frostman extension beyond radius 1
2. 2D grid cell geometry (closeness and separation)
3. Max occupancy bound in a grid cell
-/

noncomputable section

namespace Kakeya.Assouad

open Finset

/-! ### 1. Frostman extension beyond radius 1 -/

lemma DiscreteSet.IsFrostman.extend
    {E : DiscreteSet 2} {delta alpha : ℝ} {C : ENNReal}
    (hFrost : E.IsFrostman delta alpha C)
    (_hE : E.IsInUnitBall) (hC : 1 ≤ C) (halpha : 0 ≤ alpha) :
    ∀ (x : Point2) (r : ℝ), delta ≤ r →
      E.ballCount x r ≤ C * Kakeya.realRpowENN r alpha * E.enncard := by
  intro x r hdr
  by_cases hr1 : r ≤ 1
  · exact hFrost x r hdr hr1
  · have h_ball_le : E.ballCount x r ≤ E.enncard := by
      simp only [DiscreteSet.ballCount, DiscreteSet.enncard]
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have h_rpow_real : (1 : ℝ) ≤ Real.rpow r alpha :=
      Real.one_le_rpow (by linarith) halpha
    have h_rpow_enn : (1 : ENNReal) ≤ Kakeya.realRpowENN r alpha := by
      have h_eq : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by norm_num
      rw [h_eq]
      simpa [Kakeya.realRpowENN] using ENNReal.ofReal_le_ofReal h_rpow_real
    have h_mul : (1 : ENNReal) ≤ C * Kakeya.realRpowENN r alpha :=
      one_le_mul hC h_rpow_enn
    have h_main : E.enncard ≤ C * Kakeya.realRpowENN r alpha * E.enncard :=
      le_mul_of_one_le_left' h_mul
    exact h_ball_le.trans h_main

/-! ### 2. 2D grid cell geometry -/

/-- Grid index of a point in 2D at scale `s`. -/
def gridIndex2D (s : ℝ) (p : Point2) : ℤ × ℤ :=
  (⌊(p 0) / s⌋, ⌊(p 1) / s⌋)

/-- Center of a grid cell in 2D. -/
def cellCenter2D (s : ℝ) (idx : ℤ × ℤ) : Point2 :=
  (((idx.1 : ℝ) + 1 / 2) * s) • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
  (((idx.2 : ℝ) + 1 / 2) * s) • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

/-- If a point has grid index `idx`, it is within `s / sqrt 2` of the cell center. -/
lemma grid_cell_close2D {s : ℝ} (hs : 0 < s) {p : Point2} {idx : ℤ × ℤ}
    (h : gridIndex2D s p = idx) :
    dist p (cellCenter2D s idx) ≤ s / Real.sqrt 2 := by
  let i := idx.1
  let j := idx.2
  have hi1 : (i : ℝ) ≤ (p 0) / s := by
    have h' : ⌊(p 0) / s⌋ = i := by simpa [gridIndex2D] using congr_arg Prod.fst h
    have h'' : (⌊(p 0) / s⌋ : ℝ) ≤ (p 0) / s := Int.floor_le _
    rw [h'] at h''; exact h''
  have hi2 : (p 0) / s < (i : ℝ) + 1 := by
    have h' : ⌊(p 0) / s⌋ = i := by simpa [gridIndex2D] using congr_arg Prod.fst h
    have h'' : (p 0) / s < (⌊(p 0) / s⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    rw [h'] at h''; exact h''
  have hj1 : (j : ℝ) ≤ (p 1) / s := by
    have h' : ⌊(p 1) / s⌋ = j := by simpa [gridIndex2D] using congr_arg Prod.snd h
    have h'' : (⌊(p 1) / s⌋ : ℝ) ≤ (p 1) / s := Int.floor_le _
    rw [h'] at h''; exact h''
  have hj2 : (p 1) / s < (j : ℝ) + 1 := by
    have h' : ⌊(p 1) / s⌋ = j := by simpa [gridIndex2D] using congr_arg Prod.snd h
    have h'' : (p 1) / s < (⌊(p 1) / s⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    rw [h'] at h''; exact h''
  set c0 : ℝ := ((i : ℝ) + 1 / 2) * s with hc0_def
  set c1 : ℝ := ((j : ℝ) + 1 / 2) * s with hc1_def
  have h1 : (i : ℝ) * s ≤ p 0 := by
    calc (i : ℝ) * s ≤ ((p 0) / s) * s := by gcongr
      _ = p 0 := by field_simp [hs.ne'] <;> ring
  have h2 : p 0 < ((i : ℝ) + 1) * s := by
    calc p 0 = ((p 0) / s) * s := by field_simp [hs.ne'] <;> ring
      _ < (((i : ℝ) + 1) * s) := by gcongr
  have hdx_upper : p 0 - c0 ≤ s / 2 := by
    dsimp only [c0]
    linarith
  have hdx_lower : -(s / 2) ≤ p 0 - c0 := by
    dsimp only [c0]
    linarith
  have hdx : |p 0 - c0| ≤ s / 2 := abs_le.mpr ⟨hdx_lower, hdx_upper⟩
  have h1' : (j : ℝ) * s ≤ p 1 := by
    calc (j : ℝ) * s ≤ ((p 1) / s) * s := by gcongr
      _ = p 1 := by field_simp [hs.ne'] <;> ring
  have h2' : p 1 < ((j : ℝ) + 1) * s := by
    calc p 1 = ((p 1) / s) * s := by field_simp [hs.ne'] <;> ring
      _ < (((j : ℝ) + 1) * s) := by gcongr
  have hdy_upper : p 1 - c1 ≤ s / 2 := by
    dsimp only [c1]
    linarith
  have hdy_lower : -(s / 2) ≤ p 1 - c1 := by
    dsimp only [c1]
    linarith
  have hdy : |p 1 - c1| ≤ s / 2 := abs_le.mpr ⟨hdy_lower, hdy_upper⟩
  have h_center0 : (cellCenter2D s idx) 0 = c0 := by
    simp [cellCenter2D] <;> ring
  have h_center1 : (cellCenter2D s idx) 1 = c1 := by
    simp [cellCenter2D] <;> ring
  have h_dist_sq : dist p (cellCenter2D s idx) ^ 2 ≤ (s / Real.sqrt 2) ^ 2 := by
    have h5 : dist p (cellCenter2D s idx) ^ 2 =
        (p 0 - (cellCenter2D s idx) 0) ^ 2 +
        (p 1 - (cellCenter2D s idx) 1) ^ 2 := by
      have h6 : dist p (cellCenter2D s idx) = ‖p - cellCenter2D s idx‖ := by
        rw [dist_eq_norm]
      rw [h6, PiLp.norm_eq_of_L2]
      have h7 : 0 ≤ ∑ k : Fin 2, ‖(p - cellCenter2D s idx) k‖ ^ 2 := by positivity
      have h8 : (Real.sqrt (∑ k : Fin 2, ‖(p - cellCenter2D s idx) k‖ ^ 2)) ^ 2 =
          ∑ k : Fin 2, ‖(p - cellCenter2D s idx) k‖ ^ 2 := Real.sq_sqrt h7
      rw [h8]
      rw [Fin.sum_univ_succ]
      <;> simp [Real.norm_eq_abs, sq_abs] <;> rfl
    rw [h5, h_center0, h_center1]
    have h8 : (p 0 - c0) ^ 2 ≤ (s / 2) ^ 2 := by
      have h9 : (p 0 - c0) ^ 2 = |p 0 - c0| ^ 2 := by rw [sq_abs]
      rw [h9]; gcongr
    have h10 : (p 1 - c1) ^ 2 ≤ (s / 2) ^ 2 := by
      have h11 : (p 1 - c1) ^ 2 = |p 1 - c1| ^ 2 := by rw [sq_abs]
      rw [h11]; gcongr
    have h12 : (s / Real.sqrt 2) ^ 2 = (s / 2) ^ 2 + (s / 2) ^ 2 := by
      have h13 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      field_simp [h13.ne'] <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [h12]
    linarith
  have h_nonneg : 0 ≤ dist p (cellCenter2D s idx) := dist_nonneg
  have h_rhs_nonneg : 0 ≤ s / Real.sqrt 2 := by positivity
  nlinarith

/-- Distinct cell centers are at least `s` apart. -/
lemma cell_centers_separated2D {s : ℝ} (hs : 0 < s)
    {idx idx' : ℤ × ℤ} (hne : idx ≠ idx') :
    dist (cellCenter2D s idx) (cellCenter2D s idx') ≥ s := by
  let i := idx.1
  let j := idx.2
  let i' := idx'.1
  let j' := idx'.2
  by_cases h_i : i ≠ i'
  · have h_diff : 1 ≤ |(i : ℤ) - (i' : ℤ)| := by
      by_contra h
      have h' : |(i : ℤ) - (i' : ℤ)| < 1 := by linarith
      have h_nonneg : 0 ≤ |(i : ℤ) - (i' : ℤ)| := abs_nonneg _
      have h_eq : |(i : ℤ) - (i' : ℤ)| = 0 := by omega
      have h'' : (i : ℤ) - (i' : ℤ) = 0 := abs_eq_zero.mp h_eq
      have h3 : i = i' := by omega
      exact h_i h3
    have h_diff' : (1 : ℝ) ≤ |(i : ℝ) - (i' : ℝ)| := by exact_mod_cast h_diff
    have h_coord : |(cellCenter2D s idx) 0 - (cellCenter2D s idx') 0| ≥ s := by
      have h_eq : (cellCenter2D s idx) 0 - (cellCenter2D s idx') 0 =
          ((i : ℝ) - (i' : ℝ)) * s := by
        simp [cellCenter2D] <;> ring
      rw [h_eq]
      have h : |((i : ℝ) - (i' : ℝ)) * s| = |((i : ℝ) - (i' : ℝ))| * s := by
        rw [abs_mul, abs_of_pos hs]
      rw [h]
      have h_goal : s ≤ |(i : ℝ) - (i' : ℝ)| * s := by
        simpa [one_mul] using mul_le_mul_of_nonneg_right h_diff' hs.le
      exact h_goal
    have h3 : |(cellCenter2D s idx) 0 - (cellCenter2D s idx') 0| ≤
        dist (cellCenter2D s idx) (cellCenter2D s idx') :=
      PiLp.dist_apply_le (cellCenter2D s idx) (cellCenter2D s idx') 0
    linarith
  · have h_j : j ≠ j' := by
      intro h
      have h_i' : i = i' := by tauto
      simp [Prod.ext_iff] at hne <;> tauto
    have h_diff : 1 ≤ |(j : ℤ) - (j' : ℤ)| := by
      by_contra h
      have h' : |(j : ℤ) - (j' : ℤ)| < 1 := by linarith
      have h_nonneg : 0 ≤ |(j : ℤ) - (j' : ℤ)| := abs_nonneg _
      have h_eq : |(j : ℤ) - (j' : ℤ)| = 0 := by omega
      have h'' : (j : ℤ) - (j' : ℤ) = 0 := abs_eq_zero.mp h_eq
      have h3 : j = j' := by omega
      exact h_j h3
    have h_diff' : (1 : ℝ) ≤ |(j : ℝ) - (j' : ℝ)| := by exact_mod_cast h_diff
    have h_coord : |(cellCenter2D s idx) 1 - (cellCenter2D s idx') 1| ≥ s := by
      have h_eq : (cellCenter2D s idx) 1 - (cellCenter2D s idx') 1 =
          ((j : ℝ) - (j' : ℝ)) * s := by
        simp [cellCenter2D] <;> ring
      rw [h_eq]
      have h : |((j : ℝ) - (j' : ℝ)) * s| = |((j : ℝ) - (j' : ℝ))| * s := by
        rw [abs_mul, abs_of_pos hs]
      rw [h]
      have h_goal : s ≤ |(j : ℝ) - (j' : ℝ)| * s := by
        simpa [one_mul] using mul_le_mul_of_nonneg_right h_diff' hs.le
      exact h_goal
    have h3 : |(cellCenter2D s idx) 1 - (cellCenter2D s idx') 1| ≤
        dist (cellCenter2D s idx) (cellCenter2D s idx') :=
      PiLp.dist_apply_le (cellCenter2D s idx) (cellCenter2D s idx') 1
    linarith

/-- Cell center map is injective for positive side length. -/
lemma cellCenter2D_injective {s : ℝ} (hs : 0 < s) :
    Function.Injective (cellCenter2D s) := by
  intro idx idx' h
  have h0 : (cellCenter2D s idx) 0 = (cellCenter2D s idx') 0 := by rw [h]
  have h1 : (cellCenter2D s idx) 1 = (cellCenter2D s idx') 1 := by rw [h]
  have h_eq0 : ((idx.1 : ℝ) + 1 / 2) * s = ((idx'.1 : ℝ) + 1 / 2) * s := by
    simpa [cellCenter2D] using h0
  have h_eq1 : ((idx.2 : ℝ) + 1 / 2) * s = ((idx'.2 : ℝ) + 1 / 2) * s := by
    simpa [cellCenter2D] using h1
  have hi : (idx.1 : ℝ) = (idx'.1 : ℝ) := by
    have h : ((idx.1 : ℝ) + 1 / 2) = ((idx'.1 : ℝ) + 1 / 2) :=
      (mul_left_inj' hs.ne').mp h_eq0
    linarith
  have hj : (idx.2 : ℝ) = (idx'.2 : ℝ) := by
    have h : ((idx.2 : ℝ) + 1 / 2) = ((idx'.2 : ℝ) + 1 / 2) :=
      (mul_left_inj' hs.ne').mp h_eq1
    linarith
  have hi' : idx.1 = idx'.1 := by exact_mod_cast hi
  have hj' : idx.2 = idx'.2 := by exact_mod_cast hj
  exact Prod.ext hi' hj'

/-! ### 3. Max occupancy bound in a grid cell -/

/-- If two reals have the same floor after division by `s > 0`, their difference is `< s`. -/
lemma same_floor_dist_lt {x y : ℝ} {s : ℝ} (hs_pos : 0 < s)
    (h : ⌊x / s⌋ = ⌊y / s⌋) : |x - y| < s := by
  have h1 : x / s - y / s < 1 := by
    have h1a : x / s < (⌊x / s⌋ : ℝ) + 1 := Int.lt_floor_add_one (x / s)
    have h1b : (⌊y / s⌋ : ℝ) ≤ y / s := Int.floor_le (y / s)
    rw [h] at h1a; linarith
  have h2 : y / s - x / s < 1 := by
    have h2a : y / s < (⌊y / s⌋ : ℝ) + 1 := Int.lt_floor_add_one (y / s)
    have h2b : (⌊x / s⌋ : ℝ) ≤ x / s := Int.floor_le (x / s)
    rw [←h] at h2a; linarith
  have h3 : |x / s - y / s| < 1 := by
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have h4 : |(x - y) / s| < 1 := by
    have h5 : (x - y) / s = x / s - y / s := by rw [sub_div]
    rw [h5]; exact h3
  have h6 : |x - y| / s < 1 := by
    have h7 : |(x - y) / s| = |x - y| / s := by
      rw [abs_div, abs_of_pos hs_pos]
    rw [h7] at h4; exact h4
  calc |x - y|
    = |x - y| / s * s := by field_simp [hs_pos.ne'] <;> ring
  _ < 1 * s := by gcongr
  _ = s := by ring

/--
A delta-separated set has at most `9 * (s/delta)^2` points in any grid cell of side `s`.
Uses injective subgrid map with subcell side `delta/2`.
-/
lemma max_occupancy2D {E : DiscreteSet 2} {delta s : ℝ}
    (hdelta : 0 < delta) (hs : 0 < s) (hds : delta ≤ s)
    (hsep : E.IsDeltaSeparated delta) (idx : ℤ × ℤ) :
    ((E.filter (fun x => gridIndex2D s x = idx)).card : ℝ) ≤ 9 * (s / delta)^2 := by
  let A : Finset Point2 := E.filter (fun x => gridIndex2D s x = idx)
  let subSide : ℝ := delta / 2
  have hsub_pos : 0 < subSide := by positivity
  let f : Point2 → ℤ × ℤ := fun x =>
    (⌊(x 0 - (idx.1 : ℝ) * s) / subSide⌋,
     ⌊(x 1 - (idx.2 : ℝ) * s) / subSide⌋)
  let N : ℕ := Nat.ceil (2 * s / delta)
  have hN_le : (N : ℝ) ≤ 3 * s / delta := by
    have h_pos : 0 ≤ 2 * s / delta := by positivity
    have h1 : (N : ℝ) ≤ 2 * s / delta + 1 := by
      simpa [N] using (Nat.ceil_lt_add_one h_pos).le
    have h2 : 1 ≤ s / delta := by
      rw [one_le_div hdelta]
      exact hds
    calc (N : ℝ) ≤ 2 * s / delta + 1 := h1
      _ ≤ 2 * s / delta + s / delta := by gcongr
      _ = 3 * s / delta := by ring
  let rangeZ : Finset ℤ := (Finset.range N).image (fun n : ℕ => (n : ℤ))
  have h_rangeZ_card : rangeZ.card = N := by
    rw [Finset.card_image_of_injOn] <;> simp [Set.InjOn] <;> omega
  let bounded : Finset (ℤ × ℤ) := rangeZ ×ˢ rangeZ
  have h_image_subset : A.image f ⊆ bounded := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    have hxA : gridIndex2D s x = idx := (Finset.mem_filter.mp hx).2
    have h_x1 : 0 ≤ x 0 - (idx.1 : ℝ) * s := by
      have h11 : (idx.1 : ℝ) ≤ x 0 / s := by
        rw [←show ⌊x 0 / s⌋ = idx.1 from by simpa [gridIndex2D] using congr_arg Prod.fst hxA]
        <;> exact Int.floor_le _
      have h : (idx.1 : ℝ) * s ≤ x 0 / s * s := by gcongr
      have h' : x 0 / s * s = x 0 := by field_simp [hs.ne'] <;> ring
      rw [h'] at h <;> linarith
    have h_x2 : x 0 - (idx.1 : ℝ) * s < s := by
      have h21 : x 0 / s < (idx.1 : ℝ) + 1 := by
        rw [←show ⌊x 0 / s⌋ = idx.1 from by simpa [gridIndex2D] using congr_arg Prod.fst hxA]
        <;> exact Int.lt_floor_add_one _
      have h : x 0 / s * s < ((idx.1 : ℝ) + 1) * s := by gcongr
      have h' : x 0 / s * s = x 0 := by field_simp [hs.ne'] <;> ring
      rw [h'] at h <;> linarith
    have h_y1 : 0 ≤ x 1 - (idx.2 : ℝ) * s := by
      have h11 : (idx.2 : ℝ) ≤ x 1 / s := by
        rw [←show ⌊x 1 / s⌋ = idx.2 from by simpa [gridIndex2D] using congr_arg Prod.snd hxA]
        <;> exact Int.floor_le _
      have h : (idx.2 : ℝ) * s ≤ x 1 / s * s := by gcongr
      have h' : x 1 / s * s = x 1 := by field_simp [hs.ne'] <;> ring
      rw [h'] at h <;> linarith
    have h_y2 : x 1 - (idx.2 : ℝ) * s < s := by
      have h21 : x 1 / s < (idx.2 : ℝ) + 1 := by
        rw [←show ⌊x 1 / s⌋ = idx.2 from by simpa [gridIndex2D] using congr_arg Prod.snd hxA]
        <;> exact Int.lt_floor_add_one _
      have h : x 1 / s * s < ((idx.2 : ℝ) + 1) * s := by gcongr
      have h' : x 1 / s * s = x 1 := by field_simp [hs.ne'] <;> ring
      rw [h'] at h <;> linarith
    have h3 : 0 ≤ (x 0 - (idx.1 : ℝ) * s) / subSide := by positivity
    have h4 : (x 0 - (idx.1 : ℝ) * s) / subSide < (N : ℝ) := by
      have h5 : (x 0 - (idx.1 : ℝ) * s) / subSide < 2 * s / delta := by
        have h51 : x 0 - (idx.1 : ℝ) * s < s := h_x2
        calc
          (x 0 - (idx.1 : ℝ) * s) / subSide
            = 2 * (x 0 - (idx.1 : ℝ) * s) / delta := by simp [subSide] <;> ring
          _ < 2 * s / delta := by gcongr
      have h6 : (2 * s / delta : ℝ) ≤ (N : ℝ) := by
        simpa [N] using Nat.le_ceil _
      exact h5.trans_le h6
    have h7 : 0 ≤ ⌊(x 0 - (idx.1 : ℝ) * s) / subSide⌋ := Int.floor_nonneg.mpr h3
    have h8 : ⌊(x 0 - (idx.1 : ℝ) * s) / subSide⌋ < (N : ℤ) := by
      exact_mod_cast Int.floor_lt.mpr h4
    have h3' : 0 ≤ (x 1 - (idx.2 : ℝ) * s) / subSide := by positivity
    have h4' : (x 1 - (idx.2 : ℝ) * s) / subSide < (N : ℝ) := by
      have h5' : (x 1 - (idx.2 : ℝ) * s) / subSide < 2 * s / delta := by
        have h51 : x 1 - (idx.2 : ℝ) * s < s := h_y2
        calc
          (x 1 - (idx.2 : ℝ) * s) / subSide
            = 2 * (x 1 - (idx.2 : ℝ) * s) / delta := by simp [subSide] <;> ring
          _ < 2 * s / delta := by gcongr
      have h6' : (2 * s / delta : ℝ) ≤ (N : ℝ) := by
        simpa [N] using Nat.le_ceil _
      exact h5'.trans_le h6'
    have h7' : 0 ≤ ⌊(x 1 - (idx.2 : ℝ) * s) / subSide⌋ := Int.floor_nonneg.mpr h3'
    have h8' : ⌊(x 1 - (idx.2 : ℝ) * s) / subSide⌋ < (N : ℤ) := by
      exact_mod_cast Int.floor_lt.mpr h4'
    have h_in1 : ⌊(x 0 - (idx.1 : ℝ) * s) / subSide⌋ ∈ rangeZ := by
      rw [Finset.mem_image]
      refine ⟨Int.toNat ⌊(x 0 - (idx.1 : ℝ) * s) / subSide⌋, ?_, ?_⟩
      · simp [Finset.mem_range, h8] <;> omega
      · simp [h7] <;> omega
    have h_in2 : ⌊(x 1 - (idx.2 : ℝ) * s) / subSide⌋ ∈ rangeZ := by
      rw [Finset.mem_image]
      refine ⟨Int.toNat ⌊(x 1 - (idx.2 : ℝ) * s) / subSide⌋, ?_, ?_⟩
      · simp [Finset.mem_range, h8'] <;> omega
      · simp [h7'] <;> omega
    simp only [bounded, Finset.mem_product]
    <;> exact ⟨h_in1, h_in2⟩
  have h_inj : Set.InjOn f A := by
    intro x hx y hy h_eq
    by_cases hxy : x = y
    · exact hxy
    · have hxA : x ∈ E := (Finset.mem_filter.mp hx).1
      have h_yA : y ∈ E := (Finset.mem_filter.mp hy).1
      have h_eq1 : ⌊(x 0 - (idx.1 : ℝ) * s) / subSide⌋ =
          ⌊(y 0 - (idx.1 : ℝ) * s) / subSide⌋ := by
        simpa [f] using congr_arg Prod.fst h_eq
      have h_eq2 : ⌊(x 1 - (idx.2 : ℝ) * s) / subSide⌋ =
          ⌊(y 1 - (idx.2 : ℝ) * s) / subSide⌋ := by
        simpa [f] using congr_arg Prod.snd h_eq
      have hdx : |x 0 - y 0| < subSide := by
        set x' := x 0 - (idx.1 : ℝ) * s with hx'
        set y' := y 0 - (idx.1 : ℝ) * s with hy'
        have h : |x' - y'| < subSide := same_floor_dist_lt hsub_pos h_eq1
        have h' : x' - y' = x 0 - y 0 := by simp [hx', hy'] <;> ring
        rw [h'] at h
        exact h
      have hdy : |x 1 - y 1| < subSide := by
        set x' := x 1 - (idx.2 : ℝ) * s with hx'
        set y' := y 1 - (idx.2 : ℝ) * s with hy'
        have h : |x' - y'| < subSide := same_floor_dist_lt hsub_pos h_eq2
        have h' : x' - y' = x 1 - y 1 := by simp [hx', hy'] <;> ring
        rw [h'] at h
        exact h
      have hdist_sq : dist x y ^ 2 < delta ^ 2 / 2 := by
        have h1 : dist x y ^ 2 = (x 0 - y 0)^2 + (x 1 - y 1)^2 := by
          have h2 : dist x y = ‖x - y‖ := by rw [dist_eq_norm]
          rw [h2, PiLp.norm_eq_of_L2]
          have h7 : 0 ≤ ∑ k : Fin 2, ‖(x - y) k‖ ^ 2 := by positivity
          have h8 : (Real.sqrt (∑ k : Fin 2, ‖(x - y) k‖ ^ 2)) ^ 2 =
              ∑ k : Fin 2, ‖(x - y) k‖ ^ 2 := Real.sq_sqrt h7
          rw [h8]
          rw [Fin.sum_univ_succ]
          <;> simp [Real.norm_eq_abs, sq_abs] <;> rfl
        rw [h1]
        have h4 : (x 0 - y 0)^2 < subSide^2 := by
          have h5 : (x 0 - y 0)^2 = |x 0 - y 0|^2 := by rw [sq_abs]
          rw [h5]; gcongr
        have h7 : (x 1 - y 1)^2 < subSide^2 := by
          have h8 : (x 1 - y 1)^2 = |x 1 - y 1|^2 := by rw [sq_abs]
          rw [h8]; gcongr
        have h9 : 2 * subSide^2 = delta^2 / 2 := by
          simp [subSide] <;> ring
        nlinarith
      have hdist : dist x y < delta := by
        have h10 : 0 ≤ dist x y := dist_nonneg
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have hsep' : delta ≤ dist x y := hsep hxA h_yA hxy
      linarith
  have h_card1 : A.card = (A.image f).card := by
    rw [Finset.card_image_of_injOn h_inj]
  have h_card2 : (A.image f).card ≤ bounded.card := Finset.card_le_card h_image_subset
  have h_bounded_card : bounded.card = N ^ 2 := by
    simp [bounded, Finset.card_product, h_rangeZ_card] <;> ring
  have h_main : A.card ≤ N ^ 2 := by
    rw [h_card1]
    rw [h_bounded_card] at h_card2
    exact h_card2
  have h_final : (N : ℝ)^2 ≤ 9 * (s / delta)^2 := by
    calc (N : ℝ)^2 ≤ (3 * s / delta)^2 := by gcongr
      _ = 9 * (s / delta)^2 := by ring
  have h_combined : (A.card : ℝ) ≤ 9 * (s / delta)^2 := by
    have h11 : (A.card : ℝ) ≤ (N : ℝ)^2 := by exact_mod_cast h_main
    exact h11.trans h_final
  exact h_combined

end Kakeya.Assouad
