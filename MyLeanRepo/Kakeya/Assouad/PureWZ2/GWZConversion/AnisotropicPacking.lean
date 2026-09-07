import MyLeanRepo.Kakeya.Streamlined.Families
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Anisotropic cell-packing lemma

General finite-dimensional packing bound with coordinate-dependent cell sizes.

Given a finite set of points in `ι → ℝ`, each coordinate bounded by `R i`,
such that any two distinct points differ by at least `s i` in at least one
coordinate, the cardinality is at most `∏ i, (2 * ceil(R i / s i) + 1)`.

This is used for the coarse conflict degree bound: partition the 5D
parameter space (direction transverse × midpoint transverse × longitudinal)
into cells and show at most one essentially distinct tube per cell.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

open Kakeya.Streamlined Metric

/-- Helper: if two real numbers have the same floor after division by s > 0,
their absolute difference is less than s. -/
private lemma abs_sub_lt_of_floor_eq' {x y s : ℝ} (hs : 0 < s)
    (h : Int.floor (x / s) = Int.floor (y / s)) : |x - y| < s := by
  let k := Int.floor (x / s)
  have hky : k = Int.floor (y / s) := h
  have h1 : (k : ℝ) ≤ x / s := Int.floor_le _
  have h2 : x / s < (k + 1 : ℝ) := Int.lt_floor_add_one _
  have h3 : (k : ℝ) ≤ y / s := by
    have h5 : (Int.floor (y / s) : ℝ) ≤ y / s := Int.floor_le _
    rw [←hky] at h5
    exact h5
  have h4 : y / s < (k + 1 : ℝ) := by
    have h5 : y / s < (Int.floor (y / s) + 1 : ℝ) := Int.lt_floor_add_one _
    rw [←hky] at h5
    exact h5
  have h51 : x / s - y / s < 1 := by linarith
  have h52 : y / s - x / s < 1 := by linarith
  have h_div1 : (x - y) / s < 1 := by
    have h' : (x - y) / s = x / s - y / s := by field_simp [hs.ne']
    rw [h'] <;> exact h51
  have h61 : x - y < s := (div_lt_one hs).mp h_div1
  have h_div2 : (y - x) / s < 1 := by
    have h' : (y - x) / s = y / s - x / s := by field_simp [hs.ne']
    rw [h'] <;> exact h52
  have h_yx : y - x < s := (div_lt_one hs).mp h_div2
  have h62 : -(s) < x - y := by linarith
  exact abs_lt.mpr ⟨h62, h61⟩

/--
Anisotropic cell-packing bound.

Given points in `ι → ℝ` with coordinate bounds `R i` and coordinate-wise
separation `s i` (any two distinct points differ by ≥ `s i` in at least one
coordinate), the cardinality is at most
`∏ i, (2 * Nat.ceil (R i / s i) + 1)`.

Proof: map each point to its coordinate floor tuple. Same cell implies all
coordinate differences `< s i`, contradicting separation. Range is bounded
by the coordinate radii.
-/
lemma anisotropic_cell_pack
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s R : ι → ℝ} (hs : ∀ i, 0 < s i) (hR : ∀ i, 0 ≤ R i)
    {V : Finset (ι → ℝ)}
    (hball : ∀ v ∈ V, ∀ i, |v i| ≤ R i)
    (hsep : ∀ v ∈ V, ∀ w ∈ V, v ≠ w → ∃ i, |v i - w i| ≥ s i) :
    V.card ≤ ∏ i : ι, (2 * Nat.ceil (R i / s i) + 1) := by
  let N : ι → ℕ := fun i => Nat.ceil (R i / s i)
  have hN_le : ∀ i, (N i : ℝ) ≥ R i / s i := fun i => Nat.le_ceil _

  let cell : (ι → ℝ) → (ι → ℤ) := fun v i => Int.floor ((v i) / (s i))

  have h_inj : Set.InjOn cell (V : Set (ι → ℝ)) := by
    intro v hv w hw h_eq
    by_contra hne
    have h_all : ∀ i, |v i - w i| < s i := by
      intro i
      have h_fl : Int.floor ((v i) / (s i)) = Int.floor ((w i) / (s i)) := by
        have h1 : cell v = cell w := h_eq
        exact congr_fun h1 i
      exact abs_sub_lt_of_floor_eq' (hs i) h_fl
    have h_contra : ∃ i, |v i - w i| ≥ s i := hsep v hv w hw hne
    rcases h_contra with ⟨i, hi⟩
    have h_lt : |v i - w i| < s i := h_all i
    linarith

  let range : Finset (ι → ℤ) := Fintype.piFinset fun i => Finset.Icc (-(N i : ℤ)) (N i : ℤ)

  have h_Icc : ∀ (i : ι), (Finset.Icc (-(N i : ℤ)) (N i : ℤ)).card = 2 * N i + 1 := by
    intro i
    rw [Int.card_Icc]
    have h9 : (N i : ℤ) + 1 - (-(N i : ℤ)) = 2 * (N i : ℤ) + 1 := by omega
    rw [h9]
    have h10 : (2 * (N i : ℤ) + 1).toNat = 2 * N i + 1 := by
      have h_nonneg : 0 ≤ 2 * (N i : ℤ) + 1 := by omega
      have h11 : (( (2 * (N i : ℤ) + 1).toNat : ℤ)) = 2 * (N i : ℤ) + 1 := Int.toNat_of_nonneg h_nonneg
      omega
    exact h10
  have h_range_card : range.card = ∏ i : ι, (2 * N i + 1) := by
    rw [Fintype.card_piFinset]
    apply Finset.prod_congr rfl
    intro i _
    exact h_Icc i

  have h_image_sub : Finset.image cell V ⊆ range := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨v, hv, rfl⟩
    have h_bounds : ∀ i, |v i| ≤ R i := hball v hv
    simp only [range, Fintype.mem_piFinset]
    intro i
    have h_coord : |v i| ≤ R i := h_bounds i
    have h_lower1 : -(R i) ≤ v i := (abs_le.mp h_coord).1
    have h_upper1 : v i ≤ R i := (abs_le.mp h_coord).2
    have h_pos : 0 < s i := hs i
    have h_lower2 : -(N i : ℝ) ≤ (v i) / (s i) := by
      have h1 : (-(R i)) / (s i) ≤ (v i) / (s i) :=
        div_le_div_of_nonneg_right h_lower1 (by linarith)
      have h2 : (-(R i)) / (s i) = -(R i / s i) := by
        field_simp [h_pos.ne'] <;> ring
      rw [h2] at h1
      linarith [hN_le i]
    have h_upper2 : (v i) / (s i) ≤ (N i : ℝ) := by
      have h1 : (v i) / (s i) ≤ (R i) / (s i) :=
        div_le_div_of_nonneg_right h_upper1 (by linarith)
      have h2 : (R i) / (s i) ≤ (N i : ℝ) := hN_le i
      linarith
    let z : ℤ := -(N i : ℤ)
    have h_lower3 : (z : ℝ) ≤ (v i) / (s i) := by
      have hz : (z : ℝ) = -(N i : ℝ) := by simp [z]
      rw [hz] <;> exact h_lower2
    have h_fl_lower : z ≤ Int.floor ((v i) / (s i)) := Int.le_floor.mpr h_lower3
    have h_upper3 : (v i) / (s i) ≤ ((N i : ℤ) : ℝ) := by simpa using h_upper2
    have h_fl_upper : Int.floor ((v i) / (s i)) ≤ (N i : ℤ) := by
      have h1 : (Int.floor ((v i) / (s i)) : ℝ) ≤ (v i) / (s i) := Int.floor_le _
      have h2 : (Int.floor ((v i) / (s i)) : ℝ) ≤ ((N i : ℤ) : ℝ) := by linarith
      exact_mod_cast h2
    exact Finset.mem_Icc.mpr ⟨h_fl_lower, h_fl_upper⟩

  have h_card_image : (Finset.image cell V).card = V.card :=
    Finset.card_image_of_injOn h_inj
  have h_card_le : (Finset.image cell V).card ≤ range.card := Finset.card_le_card h_image_sub
  rw [←h_card_image]
  rw [h_range_card] at h_card_le
  exact h_card_le

end Kakeya.Assouad
