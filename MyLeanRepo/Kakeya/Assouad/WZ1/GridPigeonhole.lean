import MyLeanRepo.Kakeya.Assouad.WZ1.GridCenter
import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Tactic

/-!
# Grid cover and pigeonhole lemmas for affine normalization
-/

noncomputable section

open Classical Finset

namespace Kakeya.Assouad

/-- Map a point to its integer grid cell index pair. -/
def pointToIntPair (r : ℝ) (p : Point2) : ℤ × ℤ :=
  (Int.floor (p 0 / r), Int.floor (p 1 / r))

/-- `gridCenter r p` depends only on `pointToIntPair r p`. -/
lemma gridCenter_of_intPair {r : ℝ} {p q : Point2}
    (h : pointToIntPair r p = pointToIntPair r q) :
    gridCenter r p = gridCenter r q := by
  have h0 : Int.floor (p 0 / r) = Int.floor (q 0 / r) := congr_arg Prod.fst h
  have h1 : Int.floor (p 1 / r) = Int.floor (q 1 / r) := congr_arg Prod.snd h
  ext i
  fin_cases i <;> simp [gridCenter_apply, h0, h1]

/-- `gridCenter r p` has the same integer grid index as `p`. -/
lemma pointToIntPair_gridCenter {r : ℝ} (hr : 0 < r) {p : Point2} :
    pointToIntPair r (gridCenter r p) = pointToIntPair r p := by
  have h_ne : r ≠ 0 := hr.ne'
  have h0 : Int.floor (gridCenter r p 0 / r) = Int.floor (p 0 / r) := by
    have h_eq : gridCenter r p 0 / r = (1 / 2 : ℝ) + (Int.floor (p 0 / r) : ℝ) := by
      simp [gridCenter_apply, h_ne] <;> field_simp [h_ne] <;> ring
    rw [h_eq]
    rw [Int.floor_eq_iff] <;> constructor <;> norm_num <;> linarith
  have h1 : Int.floor (gridCenter r p 1 / r) = Int.floor (p 1 / r) := by
    have h_eq : gridCenter r p 1 / r = (1 / 2 : ℝ) + (Int.floor (p 1 / r) : ℝ) := by
      simp [gridCenter_apply, h_ne] <;> field_simp [h_ne] <;> ring
    rw [h_eq]
    rw [Int.floor_eq_iff] <;> constructor <;> norm_num <;> linarith
  have h_main : (Int.floor (gridCenter r p 0 / r), Int.floor (gridCenter r p 1 / r)) =
      (Int.floor (p 0 / r), Int.floor (p 1 / r)) := by
    exact Prod.ext h0 h1
  simpa [pointToIntPair] using h_main

/-- For `A` in unit ball, grid center image has at most `100 / r^2` elements. -/
lemma grid_image_card_bound {A : DiscreteSet 2} (hA : A.IsInUnitBall)
    {r : ℝ} (hr : 0 < r) (hr_one : r ≤ 1) :
    (A.image (gridCenter r)).card ≤ 100 / r^2 := by
  set C : ℤ := ⌈1 / r⌉ with hC_def
  have hC_nonneg : 0 ≤ C := by positivity
  have hC_ge : (C : ℝ) ≥ 1 / r := Int.le_ceil (1 / r)
  have hC_le : (C : ℝ) ≤ 1 / r + 1 := by
    have h2 : C ≤ Int.floor (1 / r) + 1 := by
      rw [Int.ceil_le]
      have h3 : (1 / r : ℝ) ≤ ↑(Int.floor (1 / r) + 1) := by
        have h4 : (1 / r : ℝ) < (Int.floor (1 / r) : ℝ) + 1 := Int.lt_floor_add_one (1 / r)
        have h5 : (↑(Int.floor (1 / r) + 1) : ℝ) = (Int.floor (1 / r) : ℝ) + 1 := by simp
        rw [h5]
        exact le_of_lt h4
      exact h3
    have h3 : (C : ℝ) ≤ ↑(Int.floor (1 / r) + 1) := by exact_mod_cast h2
    have h4 : (↑(Int.floor (1 / r) + 1) : ℝ) ≤ 1 / r + 1 := by
      have h5 : (Int.floor (1 / r) : ℝ) ≤ 1 / r := Int.floor_le (1 / r)
      have h6 : (↑(Int.floor (1 / r) + 1) : ℝ) = (Int.floor (1 / r) : ℝ) + 1 := by simp
      rw [h6]
      linarith
    calc (C : ℝ) ≤ ↑(Int.floor (1 / r) + 1) := h3
      _ ≤ 1 / r + 1 := h4
  set lo : ℤ := -C with hlo
  set hi : ℤ := C with hhi
  set ints : Finset ℤ := Finset.Icc lo hi with hints
  set idxSet : Finset (ℤ × ℤ) := ints.product ints with hidxSet
  set idxFun : Point2 → ℤ × ℤ := pointToIntPair r with hidxFun
  set centers : Finset Point2 := A.image (gridCenter r) with hcenters
  set idxA : Finset (ℤ × ℤ) := A.image idxFun with hidxA

  have h_floor_bounds : ∀ (p : Point2), p ∈ A → ∀ i : Fin 2,
      lo ≤ Int.floor (p i / r) ∧ Int.floor (p i / r) ≤ hi := by
    intro p hp i
    have h_norm : ‖p‖ ≤ 1 := by simpa [dist_eq_norm] using hA p hp
    have h_coord : |p i| ≤ ‖p‖ := point2_coord_le_norm p i
    have h1 : -1 ≤ p i ∧ p i ≤ 1 := by
      have h2 : |p i| ≤ 1 := h_coord.trans h_norm
      exact abs_le.mp h2
    have h4 : -1 / r ≤ p i / r := by
      have h5 : 0 ≤ r := by linarith
      exact div_le_div_of_nonneg_right h1.1 h5
    have h6 : p i / r ≤ 1 / r := by
      have h7 : 0 ≤ r := by linarith
      exact div_le_div_of_nonneg_right h1.2 h7
    have h_lo : lo ≤ Int.floor (p i / r) := by
      have h14 : -(C : ℝ) ≤ (-1 : ℝ) / r := by
        have h15 : (C : ℝ) ≥ 1 / r := hC_ge
        have h16 : (-1 : ℝ) / r = -(1 / r) := by ring
        rw [h16]
        linarith
      have h13 : -(C : ℝ) ≤ p i / r := by
        calc -(C : ℝ) ≤ (-1 : ℝ) / r := h14
          _ ≤ p i / r := h4
      have h15 : (-C : ℤ) ≤ Int.floor (p i / r) := by
        rw [Int.le_floor]
        have h16 : (↑(-C) : ℝ) ≤ p i / r := by simpa using h13
        exact h16
      have h17 : lo ≤ -C := by simp [lo] <;> omega
      exact h17.trans h15
    have h_hi : Int.floor (p i / r) ≤ hi := by
      have h8 : Int.floor (p i / r) ≤ Int.floor (1 / r) := Int.floor_mono h6
      have h9 : Int.floor (1 / r) ≤ C := Int.floor_le_ceil (1 / r)
      exact h8.trans h9
    exact ⟨h_lo, h_hi⟩

  have h_bounds : ∀ p ∈ A, idxFun p ∈ idxSet := by
    intro p hp
    have h0 := h_floor_bounds p hp 0
    have h1 := h_floor_bounds p hp 1
    have h_mem0 : Int.floor (p 0 / r) ∈ ints := by
      rw [hints, Finset.mem_Icc] <;> exact ⟨h0.1, h0.2⟩
    have h_mem1 : Int.floor (p 1 / r) ∈ ints := by
      rw [hints, Finset.mem_Icc] <;> exact ⟨h1.1, h1.2⟩
    have h' : (Int.floor (p 0 / r), Int.floor (p 1 / r)) ∈ ints.product ints :=
      Finset.mem_product.mpr ⟨h_mem0, h_mem1⟩
    rw [hidxSet, hidxFun, pointToIntPair]
    exact h'

  have h_idxA_sub : idxA ⊆ idxSet := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
    exact h_bounds p hp

  have h_inj : Set.InjOn idxFun (centers : Set Point2) := by
    intro c1 hc1 c2 hc2 heq
    rcases Finset.mem_image.mp hc1 with ⟨p1, hp1, rfl⟩
    rcases Finset.mem_image.mp hc2 with ⟨p2, hp2, rfl⟩
    have h1 : idxFun p1 = idxFun p2 := by
      have ha : idxFun (gridCenter r p1) = idxFun p1 := pointToIntPair_gridCenter hr
      have hb : idxFun (gridCenter r p2) = idxFun p2 := pointToIntPair_gridCenter hr
      rw [ha, hb] at heq
      exact heq
    exact gridCenter_of_intPair h1

  have h_img : centers.image idxFun = idxA := by
    ext z
    simp only [hcenters, hidxA, Finset.mem_image]
    constructor
    · rintro ⟨c, ⟨p, hp, rfl⟩, rfl⟩
      have h : idxFun (gridCenter r p) = idxFun p := pointToIntPair_gridCenter hr
      rw [h]
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨gridCenter r p, ⟨p, hp, rfl⟩, pointToIntPair_gridCenter hr⟩

  have h_card1 : (centers.image idxFun).card = centers.card :=
    Finset.card_image_of_injOn h_inj

  have h_ints_card : ints.card = (2 * C + 1).toNat := by
    rw [hints, Int.card_Icc lo hi]
    have h2 : hi + 1 - lo = 2 * C + 1 := by
      simp [hlo, hhi] <;> omega
    rw [h2]

  have h_ints_bound : (ints.card : ℝ) ≤ 10 / r := by
    rw [h_ints_card]
    have h3 : 0 ≤ 2 * C + 1 := by omega
    have h4 : ((2 * C + 1).toNat : ℝ) = 2 * (C : ℝ) + 1 := by
      have h5 : ((2 * C + 1).toNat : ℤ) = 2 * C + 1 := Int.toNat_of_nonneg h3
      exact_mod_cast h5
    rw [h4]
    have h6 : 2 * (C : ℝ) + 1 ≤ 10 / r := by
      have h_two_pos : (0 : ℝ) ≤ 2 := by norm_num
      have h_step1 : 2 * (C : ℝ) + 1 ≤ 2 * (1 / r + 1) + 1 := by
        have h : 2 * (C : ℝ) ≤ 2 * (1 / r + 1) := by
          exact mul_le_mul_of_nonneg_left hC_le h_two_pos
        linarith
      have h_step2 : 2 * (1 / r + 1) + 1 = 2 / r + 3 := by ring
      have h_pos : 0 < r := hr
      have h_step3 : (3 : ℝ) ≤ 8 / r := by
        have h : 3 * r ≤ 8 := by nlinarith
        have h' : (3 * r) / r ≤ (8 : ℝ) / r := div_le_div_of_nonneg_right h (by positivity)
        have h'' : (3 * r) / r = (3 : ℝ) := by
          field_simp [h_pos.ne'] <;> ring
        rw [h''] at h'
        exact h'
      have h_step4 : 2 / r + 3 ≤ 2 / r + 8 / r := by linarith [h_step3]
      have h_step5 : 2 / r + 8 / r = 10 / r := by ring
      calc 2 * (C : ℝ) + 1
        ≤ 2 * (1 / r + 1) + 1 := h_step1
        _ = 2 / r + 3 := h_step2
        _ ≤ 2 / r + 8 / r := h_step4
        _ = 10 / r := h_step5
    exact h6

  have h_final : (centers.card : ℝ) ≤ 100 / r^2 := by
    have h11 : (centers.card : ℝ) = (centers.image idxFun).card := by exact_mod_cast h_card1.symm
    have h12 : (centers.image idxFun).card = idxA.card := by
      rw [h_img]
    have h13 : (idxA.card : ℝ) ≤ (idxSet.card : ℝ) := by exact_mod_cast Finset.card_le_card h_idxA_sub
    have h14 : (idxSet.card : ℝ) = (ints.card : ℝ)^2 := by
      have h15 : idxSet = ints.product ints := by simp [idxSet]
      have h16 : idxSet.card = ints.card * ints.card := by
        rw [h15]
        exact Finset.card_product ints ints
      have h17 : (idxSet.card : ℝ) = (ints.card : ℝ) * (ints.card : ℝ) := by
        exact_mod_cast h16
      have h18 : (ints.card : ℝ) * (ints.card : ℝ) = (ints.card : ℝ)^2 := by ring
      rw [h17, h18]
    have h18 : (ints.card : ℝ)^2 ≤ (10 / r)^2 := by gcongr
    have h19 : (10 / r)^2 = 100 / r^2 := by ring
    calc (centers.card : ℝ)
      = (centers.image idxFun).card := h11
      _ = (idxA.card : ℝ) := by exact_mod_cast h12
      _ ≤ (idxSet.card : ℝ) := h13
      _ = (ints.card : ℝ)^2 := h14
      _ ≤ (10 / r)^2 := h18
      _ = 100 / r^2 := h19
  exact_mod_cast h_final

/-- For `A` in unit ball, grid center image has at most `(2/r + 2)^2` elements.
Tighter than `grid_image_card_bound` for small `r`. -/
lemma grid_image_card_bound_tight {A : DiscreteSet 2} (hA : A.IsInUnitBall)
    {r : ℝ} (hr : 0 < r) (hr_one : r ≤ 1) :
    ((A.image (gridCenter r)).card : ℝ) ≤ (2 / r + 2) ^ 2 := by
  set f : ℤ := ⌊1 / r⌋ with hf_def
  have hf_le : (f : ℝ) ≤ 1 / r := Int.floor_le (1 / r)
  have hf_nonneg : 0 ≤ f := by
    have h1 : (1 : ℝ) ≤ 1 / r := by
      have h2 : 0 < r := hr
      have h3 : r ≤ 1 := hr_one
      field_simp [h2.ne'] <;> linarith
    have h4 : (↑(1 : ℤ) : ℝ) ≤ 1 / r := by
      have h5 : (↑(1 : ℤ) : ℝ) = (1 : ℝ) := by norm_cast
      rw [h5]
      exact h1
    have h6 : (1 : ℤ) ≤ f := Int.le_floor.mpr h4
    have h7 : 0 ≤ f := by exact le_trans (by norm_num) h6
    exact h7
  set lo : ℤ := -f - 1 with hlo
  set hi : ℤ := f with hhi
  set ints : Finset ℤ := Finset.Icc lo hi with hints
  set idxSet : Finset (ℤ × ℤ) := ints.product ints with hidxSet
  set idxFun : Point2 → ℤ × ℤ := pointToIntPair r with hidxFun
  set centers : Finset Point2 := A.image (gridCenter r) with hcenters
  set idxA : Finset (ℤ × ℤ) := A.image idxFun with hidxA

  have h_floor_bounds : ∀ (p : Point2), p ∈ A → ∀ i : Fin 2,
      lo ≤ Int.floor (p i / r) ∧ Int.floor (p i / r) ≤ hi := by
    intro p hp i
    have h_norm : ‖p‖ ≤ 1 := by simpa [dist_eq_norm] using hA p hp
    have h_coord : |p i| ≤ ‖p‖ := point2_coord_le_norm p i
    have h1 : -1 ≤ p i ∧ p i ≤ 1 := by
      have h2 : |p i| ≤ 1 := h_coord.trans h_norm
      exact abs_le.mp h2
    have h4 : -1 / r ≤ p i / r := by
      have h5 : 0 ≤ r := by linarith
      exact div_le_div_of_nonneg_right h1.1 h5
    have h6 : p i / r ≤ 1 / r := by
      have h7 : 0 ≤ r := by linarith
      exact div_le_div_of_nonneg_right h1.2 h7
    have h_hi : Int.floor (p i / r) ≤ hi := by
      have h7 : Int.floor (p i / r) ≤ Int.floor (1 / r) := Int.floor_mono h6
      simpa [hi, hf_def] using h7
    have h_lo : lo ≤ Int.floor (p i / r) := by
      have h9 : (1 : ℝ) / r < (f : ℝ) + 1 := by
        have h91 : (1 : ℝ) / r < (↑⌊1 / r⌋ : ℝ) + 1 := Int.lt_floor_add_one (1 / r)
        have h92 : (↑⌊1 / r⌋ : ℝ) = (f : ℝ) := by
          exact_mod_cast rfl
        rw [h92] at h91
        exact h91
      have h10 : p i / r ≥ -1 / r := h4
      have h11 : -1 / r > -(f : ℝ) - 1 := by
        have h111 : (1 : ℝ) / r < (f : ℝ) + 1 := h9
        have h112 : -(1 / r : ℝ) > -((f : ℝ) + 1) := by
          exact neg_lt_neg h111
        have h113 : -(1 / r : ℝ) = -1 / r := by ring
        have h114 : -((f : ℝ) + 1) = -(f : ℝ) - 1 := by ring
        rw [h113, h114] at h112
        exact h112
      have h12 : p i / r > -(f : ℝ) - 1 := by
        calc p i / r ≥ -1 / r := h10
          _ > -(f : ℝ) - 1 := h11
      have h13 : (↑(lo) : ℝ) ≤ p i / r := by
        have h14 : (↑(lo) : ℝ) = -(f : ℝ) - 1 := by
          simp [hlo] <;> norm_cast <;> ring
        rw [h14]
        exact le_of_lt h12
      have h15 : lo ≤ Int.floor (p i / r) := Int.le_floor.mpr h13
      exact h15
    exact ⟨h_lo, h_hi⟩

  have h_bounds : ∀ p ∈ A, idxFun p ∈ idxSet := by
    intro p hp
    have h0 := h_floor_bounds p hp 0
    have h1 := h_floor_bounds p hp 1
    have h_mem0 : Int.floor (p 0 / r) ∈ ints := by
      rw [hints, Finset.mem_Icc] <;> exact ⟨h0.1, h0.2⟩
    have h_mem1 : Int.floor (p 1 / r) ∈ ints := by
      rw [hints, Finset.mem_Icc] <;> exact ⟨h1.1, h1.2⟩
    have h' : (Int.floor (p 0 / r), Int.floor (p 1 / r)) ∈ ints.product ints :=
      Finset.mem_product.mpr ⟨h_mem0, h_mem1⟩
    rw [hidxSet, hidxFun, pointToIntPair]
    exact h'

  have h_idxA_sub : idxA ⊆ idxSet := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
    exact h_bounds p hp

  have h_inj : Set.InjOn idxFun (centers : Set Point2) := by
    intro c1 hc1 c2 hc2 heq
    rcases Finset.mem_image.mp hc1 with ⟨p1, hp1, rfl⟩
    rcases Finset.mem_image.mp hc2 with ⟨p2, hp2, rfl⟩
    have h1 : idxFun p1 = idxFun p2 := by
      have ha : idxFun (gridCenter r p1) = idxFun p1 := pointToIntPair_gridCenter hr
      have hb : idxFun (gridCenter r p2) = idxFun p2 := pointToIntPair_gridCenter hr
      rw [ha, hb] at heq
      exact heq
    exact gridCenter_of_intPair h1

  have h_img : centers.image idxFun = idxA := by
    ext z
    simp only [hcenters, hidxA, Finset.mem_image]
    constructor
    · rintro ⟨c, ⟨p, hp, rfl⟩, rfl⟩
      have h : idxFun (gridCenter r p) = idxFun p := pointToIntPair_gridCenter hr
      rw [h]
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨gridCenter r p, ⟨p, hp, rfl⟩, pointToIntPair_gridCenter hr⟩

  have h_card1 : (centers.image idxFun).card = centers.card :=
    Finset.card_image_of_injOn h_inj

  have h_ints_card : (ints.card : ℝ) = 2 * (f : ℝ) + 2 := by
    have h_pos : lo ≤ hi := by
      simp [hlo, hhi] <;> omega
    have h1 : ints.card = (hi - lo + 1).toNat := by
      rw [hints, Int.card_Icc]
      <;> simp [hlo, hhi] <;> omega
    rw [h1]
    have h2 : 0 ≤ hi - lo + 1 := by omega
    have h3 : ((hi - lo + 1).toNat : ℤ) = (hi - lo + 1) := Int.toNat_of_nonneg h2
    have h4 : ((hi - lo + 1).toNat : ℝ) = ((hi - lo + 1 : ℤ) : ℝ) := by exact_mod_cast h3
    rw [h4]
    simp [hlo, hhi] <;> ring

  have h_final : (centers.card : ℝ) ≤ (2 / r + 2) ^ 2 := by
    have h11 : (centers.card : ℝ) = ((centers.image idxFun).card : ℝ) := by exact_mod_cast h_card1.symm
    rw [h11]
    have h12 : ((centers.image idxFun).card : ℝ) = (idxA.card : ℝ) := by
      rw [h_img] <;> rfl
    rw [h12]
    have h13 : (idxA.card : ℝ) ≤ (idxSet.card : ℝ) := by exact_mod_cast Finset.card_le_card h_idxA_sub
    have h14 : (idxSet.card : ℝ) = (ints.card : ℝ) ^ 2 := by
      have h15 : idxSet.card = ints.card * ints.card := by
        rw [hidxSet]
        exact Finset.card_product ints ints
      have h16 : (idxSet.card : ℝ) = (ints.card : ℝ) * (ints.card : ℝ) := by exact_mod_cast h15
      rw [h16]
      <;> ring
    rw [h14] at h13
    have h17 : (ints.card : ℝ) ≤ 2 / r + 2 := by
      rw [h_ints_card]
      have h18 : 2 * (f : ℝ) + 2 ≤ 2 / r + 2 := by
        have h19 : 2 * (f : ℝ) ≤ 2 / r := by
          have h20 : (f : ℝ) ≤ 1 / r := by simpa [hhi] using hf_le
          calc
            2 * (f : ℝ) = 2 * (f : ℝ) := rfl
            _ ≤ 2 * (1 / r) := by gcongr
            _ = 2 / r := by ring
        linarith
      exact h18
    have h20 : (ints.card : ℝ) ^ 2 ≤ (2 / r + 2) ^ 2 := by gcongr
    exact h13.trans h20

  exact h_final
lemma grid_cell_diameter_2d (r : ℝ) (hr : 0 < r) {p q : Point2}
    (h : gridCenter r p = gridCenter r q) : dist p q ≤ 2 * r := by
  set c := gridCenter r p with hc
  have h1 : dist p c ≤ r := gridCenter_rho_close r hr p
  have h2 : dist c q ≤ r := by
    have h3 : gridCenter r q = c := h.symm
    have h4 : dist q (gridCenter r q) ≤ r := gridCenter_rho_close r hr q
    rw [h3] at h4
    exact dist_comm q c ▸ h4
  calc dist p q ≤ dist p c + dist c q := dist_triangle p c q
    _ ≤ r + r := by linarith
    _ = 2 * r := by ring

/-- General pigeonhole: some cell has fiber ≥ |H| / |cells|. -/
lemma finset_pigeonhole {α β : Type*} [DecidableEq β]
    {H : Finset α} {f : α → β} {cells : Finset β}
    (hmaps : ∀ h ∈ H, f h ∈ cells) (hne : cells.Nonempty) :
    ∃ c ∈ cells,
      (H.card : ℝ) ≤ (cells.card : ℝ) * ((H.filter (fun h => f h = c)).card : ℝ) := by
  have h_partition : ∑ c ∈ cells, (H.filter (fun h => f h = c)).card = H.card := by
    have h_union : (cells.biUnion (fun c => H.filter (fun h => f h = c))) = H := by
      ext h
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨c, _, hh⟩
        exact (Finset.mem_filter.mp hh).1
      · intro hh
        exact ⟨f h, hmaps h hh, by simp [hh]⟩
    have h_disj : ∀ c1 ∈ cells, ∀ c2 ∈ cells, c1 ≠ c2 →
        Disjoint (H.filter (fun h => f h = c1)) (H.filter (fun h => f h = c2)) := by
      intro c1 _ c2 _ hneq
      simp only [Finset.disjoint_left, Finset.mem_filter]
      intro x hx1 hx2
      have h10 : f x = c1 := hx1.2
      have h11 : f x = c2 := hx2.2
      exact hneq (h10.symm.trans h11)
    rw [← Finset.card_biUnion h_disj, h_union]
  by_contra h
  push Not at h
  have hcard_pos : 0 < (cells.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  have h_lt : ∀ c ∈ cells,
      ((H.filter (fun h => f h = c)).card : ℝ) < (H.card : ℝ) / (cells.card : ℝ) := by
    intro c hc
    have h_strict : (cells.card : ℝ) * ((H.filter (fun h => f h = c)).card : ℝ) < (H.card : ℝ) := h c hc
    have h_goal : ((H.filter (fun h => f h = c)).card : ℝ) < (H.card : ℝ) / (cells.card : ℝ) := by
      have h_div : ((cells.card : ℝ) * ((H.filter (fun h => f h = c)).card : ℝ)) / (cells.card : ℝ) < (H.card : ℝ) / (cells.card : ℝ) :=
        div_lt_div_of_pos_right h_strict hcard_pos
      have h_eq : ((cells.card : ℝ) * ((H.filter (fun h => f h = c)).card : ℝ)) / (cells.card : ℝ) = ((H.filter (fun h => f h = c)).card : ℝ) := by
        field_simp [hcard_pos.ne'] <;> ring
      rw [h_eq] at h_div
      exact h_div
    exact h_goal
  have h_sum_lt : ∑ c ∈ cells, ((H.filter (fun h => f h = c)).card : ℝ) <
      ∑ _c ∈ cells, (H.card : ℝ) / (cells.card : ℝ) := by
    apply Finset.sum_lt_sum_of_nonempty hne
    intro c hc
    exact h_lt c hc
  have h_rhs : ∑ _c ∈ cells, (H.card : ℝ) / (cells.card : ℝ) = (H.card : ℝ) := by
    have h_sum : ∑ _c ∈ cells, (H.card : ℝ) / (cells.card : ℝ) =
        (cells.card : ℝ) * ((H.card : ℝ) / (cells.card : ℝ)) := by
      rw [Finset.sum_const] <;> ring
    rw [h_sum]
    field_simp [hcard_pos.ne'] <;> ring
  rw [h_rhs] at h_sum_lt
  have h_eq : ∑ c ∈ cells, ((H.filter (fun h => f h = c)).card : ℝ) = (H.card : ℝ) := by
    exact_mod_cast h_partition
  rw [h_eq] at h_sum_lt
  exact lt_irrefl (H.card : ℝ) h_sum_lt

/-- Product-grid pigeonhole for edges. -/
lemma grid_pigeonhole_edges
    {F G1 G2 : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {r : ℝ} (hr : 0 < r) (hr_one : r ≤ 1)
    (h_support : ∀ h ∈ H, h.1 ∈ F ∧ h.2.1 ∈ G1 ∧ h.2.2 ∈ G2)
    (hF_unit : F.IsInUnitBall) (hG1_unit : G1.IsInUnitBall) (hG2_unit : G2.IsInUnitBall) :
    ∃ (cF cG1 cG2 : Point2),
      (H.filter (fun h =>
        gridCenter r h.1 = cF ∧
        gridCenter r h.2.1 = cG1 ∧
        gridCenter r h.2.2 = cG2)).card ≥
      Nat.ceil ((H.card : ℝ) / (1000000 / r^6)) := by
  set centersF := F.image (gridCenter r) with hcF
  set centersG1 := G1.image (gridCenter r) with hcG1
  set centersG2 := G2.image (gridCenter r) with hcG2
  set cells : Finset (Point2 × Point2 × Point2) :=
    centersF.product (centersG1.product centersG2) with hcells
  set f : (Point2 × Point2 × Point2) → (Point2 × Point2 × Point2) := fun h =>
    (gridCenter r h.1, (gridCenter r h.2.1, gridCenter r h.2.2)) with hf

  have hmaps : ∀ h ∈ H, f h ∈ cells := by
    intro h hh
    have hs := h_support h hh
    have hF : gridCenter r h.1 ∈ centersF := Finset.mem_image.mpr ⟨h.1, hs.1, rfl⟩
    have hG1 : gridCenter r h.2.1 ∈ centersG1 := Finset.mem_image.mpr ⟨h.2.1, hs.2.1, rfl⟩
    have hG2 : gridCenter r h.2.2 ∈ centersG2 := Finset.mem_image.mpr ⟨h.2.2, hs.2.2, rfl⟩
    have hinner : (gridCenter r h.2.1, gridCenter r h.2.2) ∈ centersG1.product centersG2 :=
      Finset.mem_product.mpr ⟨hG1, hG2⟩
    have h : (gridCenter r h.1, (gridCenter r h.2.1, gridCenter r h.2.2)) ∈ cells :=
      Finset.mem_product.mpr ⟨hF, hinner⟩
    rw [hf]
    exact h

  have hcardF : (centersF.card : ℝ) ≤ 100 / r^2 := grid_image_card_bound hF_unit hr hr_one
  have hcardG1 : (centersG1.card : ℝ) ≤ 100 / r^2 := grid_image_card_bound hG1_unit hr hr_one
  have hcardG2 : (centersG2.card : ℝ) ≤ 100 / r^2 := grid_image_card_bound hG2_unit hr hr_one

  have hcard6 : (cells.card : ℝ) ≤ 1000000 / r^6 := by
    have h1 : (cells.card : ℝ) = (centersF.card : ℝ) * ((centersG1.card : ℝ) * (centersG2.card : ℝ)) := by
      have h_eq : cells = centersF.product (centersG1.product centersG2) := by simp [cells]
      rw [h_eq]
      have h2 : (centersF.product (centersG1.product centersG2)).card =
          centersF.card * (centersG1.product centersG2).card := Finset.card_product _ _
      rw [h2]
      have h3 : (centersG1.product centersG2).card = centersG1.card * centersG2.card := Finset.card_product _ _
      rw [h3]
      norm_cast
    rw [h1]
    have h2 : (centersF.card : ℝ) * ((centersG1.card : ℝ) * (centersG2.card : ℝ)) ≤
        (100 / r^2) * ((100 / r^2) * (100 / r^2)) := by gcongr <;> positivity
    have h3 : (100 / r^2) * ((100 / r^2) * (100 / r^2)) = 1000000 / r^6 := by ring
    rw [h3] at h2
    exact h2

  by_cases hH_empty : H = ∅
  · subst hH_empty
    refine ⟨(0 : Point2), (0 : Point2), (0 : Point2), ?_⟩
    simp
  · have hH_ne : H.Nonempty := Finset.nonempty_iff_ne_empty.mpr hH_empty
    have hcentersF_ne : centersF.Nonempty := by
      rcases hH_ne with ⟨h, hh⟩
      have hs := h_support h hh
      exact ⟨gridCenter r h.1, Finset.mem_image.mpr ⟨h.1, hs.1, rfl⟩⟩
    have hcells_ne : cells.Nonempty := by
      rcases hcentersF_ne with ⟨cF, hcF⟩
      rcases hH_ne with ⟨h, hh⟩
      have hs := h_support h hh
      set cG1 : Point2 := gridCenter r h.2.1 with hcG1_def
      set cG2 : Point2 := gridCenter r h.2.2 with hcG2_def
      have hcG1 : cG1 ∈ centersG1 := Finset.mem_image.mpr ⟨h.2.1, hs.2.1, rfl⟩
      have hcG2 : cG2 ∈ centersG2 := Finset.mem_image.mpr ⟨h.2.2, hs.2.2, rfl⟩
      have hinner : (cG1, cG2) ∈ centersG1.product centersG2 :=
        Finset.mem_product.mpr ⟨hcG1, hcG2⟩
      have h : (cF, (cG1, cG2)) ∈ cells := Finset.mem_product.mpr ⟨hcF, hinner⟩
      exact ⟨(cF, (cG1, cG2)), h⟩

    rcases finset_pigeonhole hmaps hcells_ne with ⟨ct, hct_in, hbound⟩
    rcases ct with ⟨cF, cG1, cG2⟩
    let ct' : Point2 × Point2 × Point2 := (cF, (cG1, cG2))
    have hct'_in : ct' ∈ cells := by simpa [ct'] using hct_in

    have h_filter_eq : H.filter (fun h : Point2 × Point2 × Point2 =>
        gridCenter r h.1 = cF ∧
        gridCenter r h.2.1 = cG1 ∧
        gridCenter r h.2.2 = cG2) =
        H.filter (fun h => f h = ct') := by
      ext h
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hh, h1, h2, h3⟩
        have h_goal : f h = ct' := by
          simp only [hf, ct']
          apply Prod.ext
          · exact h1
          · apply Prod.ext
            · exact h2
            · exact h3
        exact ⟨hh, h_goal⟩
      · rintro ⟨hh, h4⟩
        have h5 : f h = ct' := h4
        have h6 : gridCenter r h.1 = cF ∧ gridCenter r h.2.1 = cG1 ∧ gridCenter r h.2.2 = cG2 := by
          simpa [hf, ct', Prod.ext_iff] using h5
        exact ⟨hh, h6.1, h6.2.1, h6.2.2⟩

    have h_main : (H.filter (fun h => f h = ct')).card ≥ Nat.ceil ((H.card : ℝ) / (1000000 / r^6)) := by
      have h4 : (H.card : ℝ) ≤ (cells.card : ℝ) * ((H.filter (fun h => f h = ct')).card : ℝ) := hbound
      have h5 : (cells.card : ℝ) * ((H.filter (fun h => f h = ct')).card : ℝ) ≤
          (1000000 / r^6) * ((H.filter (fun h => f h = ct')).card : ℝ) := by gcongr
      have h6 : (H.card : ℝ) ≤ (1000000 / r^6) * ((H.filter (fun h => f h = ct')).card : ℝ) :=
        h4.trans h5
      have h7 : 0 < 1000000 / r^6 := by positivity
      have h8 : ((H.filter (fun h => f h = ct')).card : ℝ) ≥ (H.card : ℝ) / (1000000 / r^6) := by
        have h_div : ((1000000 / r^6) * ((H.filter (fun h => f h = ct')).card : ℝ)) / (1000000 / r^6) =
            ((H.filter (fun h => f h = ct')).card : ℝ) := by
          field_simp [h7.ne'] <;> ring
        have h_ineq : ((1000000 / r^6) * ((H.filter (fun h => f h = ct')).card : ℝ)) / (1000000 / r^6) ≥
            (H.card : ℝ) / (1000000 / r^6) := by
          exact div_le_div_of_nonneg_right h6 (by positivity)
        rw [h_div] at h_ineq
        exact h_ineq
      have h9 : Nat.ceil ((H.card : ℝ) / (1000000 / r^6)) ≤ (H.filter (fun h => f h = ct')).card :=
        Nat.ceil_le.mpr h8
      exact h9
    have h_final : (H.filter (fun h =>
        gridCenter r h.1 = cF ∧
        gridCenter r h.2.1 = cG1 ∧
        gridCenter r h.2.2 = cG2)).card ≥ Nat.ceil ((H.card : ℝ) / (1000000 / r^6)) := by
      rw [h_filter_eq]
      exact h_main
    exact ⟨cF, cG1, cG2, h_final⟩

/-- Scaling relation: `gridCenter r p = 3 • gridCenter (r/3) (p/3)`. -/
lemma gridCenter_scaling (r : ℝ) (hr : 0 < r) (p : Point2) :
    gridCenter r p = (3 : ℝ) • gridCenter (r / 3) ((1 / 3 : ℝ) • p) := by
  ext i
  have h1 : ((1 / 3 : ℝ) • p) i = p i / 3 := by
    simp [smul_eq_mul] <;> ring
  have h2 : gridCenter (r / 3) ((1 / 3 : ℝ) • p) i =
      ((Int.floor (p i / r) : ℝ) + 1 / 2) * (r / 3) := by
    rw [gridCenter_apply, h1]
    have h3 : (p i / 3) / (r / 3) = p i / r := by
      field_simp [hr.ne'] <;> ring
    rw [h3] <;> ring
  have h4 : ((3 : ℝ) • gridCenter (r / 3) ((1 / 3 : ℝ) • p)) i =
      3 * (gridCenter (r / 3) ((1 / 3 : ℝ) • p) i) := by
    simp [smul_eq_mul] <;> ring
  have h5 : (gridCenter r p) i = ((Int.floor (p i / r) : ℝ) + 1 / 2) * r := by
    rw [gridCenter_apply] <;> ring
  rw [h5, h4, h2] <;> ring

/--
For a set `A` contained in the radius-3 ball, the grid center image at scale
`r` has at most `(6/r + 2)^2` elements.
-/
lemma grid_image_card_bound_radius3 {A : DiscreteSet 2}
    (hA : ∀ p ∈ A, dist p 0 ≤ 3) {r : ℝ} (hr : 0 < r) (hr_le3 : r ≤ 3) :
    ((A.image (gridCenter r)).card : ℝ) ≤ (6 / r + 2) ^ 2 := by
  let A' : DiscreteSet 2 := A.image (fun p : Point2 => (1 / 3 : ℝ) • p)
  have hA'_unit : A'.IsInUnitBall := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    have h1 : dist p 0 ≤ 3 := hA p hp
    have h2 : dist ((1 / 3 : ℝ) • p) 0 = (1 / 3 : ℝ) * dist p 0 := by
      simp [dist_eq_norm, norm_smul] <;> ring
    rw [h2] <;> linarith
  have h3 : A.image (gridCenter r) =
      (A'.image (gridCenter (r / 3))).image (fun q : Point2 => (3 : ℝ) • q) := by
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      let q : Point2 := (1 / 3 : ℝ) • p
      have hq : q ∈ A' := Finset.mem_image.mpr ⟨p, hp, rfl⟩
      refine ⟨gridCenter (r / 3) q, ⟨q, hq, rfl⟩, ?_⟩
      exact (gridCenter_scaling r hr p).symm
    · rintro ⟨y, ⟨q, hq, rfl⟩, rfl⟩
      rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
      exact ⟨p, hp, gridCenter_scaling r hr p⟩
  rw [h3]
  have h_inj : Function.Injective (fun q : Point2 => (3 : ℝ) • q) := by
    intro x y h
    simpa [smul_eq_mul] using h
  have h4 : (( (A'.image (gridCenter (r / 3))).image (fun q : Point2 => (3 : ℝ) • q)).card) =
      (A'.image (gridCenter (r / 3))).card :=
    Finset.card_image_of_injective _ h_inj
  rw [h4]
  have hr3_pos : 0 < r / 3 := by positivity
  have hr3_one : r / 3 ≤ 1 := by linarith
  have h_bound : ((A'.image (gridCenter (r / 3))).card : ℝ) ≤ (2 / (r / 3) + 2) ^ 2 :=
    grid_image_card_bound_tight hA'_unit hr3_pos hr3_one
  have h_eq : (2 / (r / 3) + 2 : ℝ) = 6 / r + 2 := by
    field_simp [hr.ne'] <;> ring
  rw [h_eq] at h_bound
  exact h_bound

end Kakeya.Assouad
