import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedTripartiteFiberStatements
import Mathlib.Tactic

/-!
# Bounded fibers of the snapped WZ1 Lemma 23 tripartite encoding

After fixing the base height and base global bin, the three edge coordinates
determine all y- and z-indices.  Each successive scalar-bin constraint leaves
at most two x-indices, so every actual edge has at most `2^4 = 16` actual
four-cycle preimages.
-/

namespace Kakeya.Assouad

noncomputable section

open Finset

private lemma two_div_sqrt3_gt_one :
    (1 : ℝ) < 2 / Real.sqrt 3 := by
  have h1 : 0 < Real.sqrt 3 :=
    Real.sqrt_pos.mpr (by norm_num)
  have h2 : Real.sqrt 3 < 2 := by
    nlinarith
      [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  calc
    (1 : ℝ) = Real.sqrt 3 / Real.sqrt 3 := by
      field_simp [h1.ne']
      <;> nlinarith
    _ < 2 / Real.sqrt 3 := by gcongr

private lemma finset_int_three_elements
    {s : Finset ℤ} (h : 3 ≤ s.card) :
    ∃ n1 n2 n3 : ℤ,
      n1 ∈ s ∧ n2 ∈ s ∧ n3 ∈ s ∧
        n1 < n2 ∧ n2 < n3 := by
  have hne : s.Nonempty :=
    Finset.card_pos.mp (by linarith)
  let a := Finset.min' s hne
  have ha : a ∈ s := Finset.min'_mem s hne
  have ha_le : ∀ x ∈ s, a ≤ x :=
    fun x hx => Finset.min'_le s x hx
  let s2 := s.erase a
  have h2 : s2.card = s.card - 1 := by
    rw [Finset.card_erase_of_mem ha] <;> omega
  have h3 : 2 ≤ s2.card := by omega
  have hne2 : s2.Nonempty :=
    Finset.card_pos.mp (by linarith)
  let b := Finset.min' s2 hne2
  have hb : b ∈ s2 := Finset.min'_mem s2 hne2
  have hb_s : b ∈ s := Finset.mem_of_mem_erase hb
  have hne_ab : b ≠ a := Finset.ne_of_mem_erase hb
  have hb_le : ∀ x ∈ s2, b ≤ x :=
    fun x hx => Finset.min'_le s2 x hx
  have hab : a < b := by
    have hle : a ≤ b := ha_le b hb_s
    exact lt_of_le_of_ne hle hne_ab.symm
  let s3 := s2.erase b
  have h4 : s3.card = s2.card - 1 := by
    rw [Finset.card_erase_of_mem hb] <;> omega
  have h5 : 1 ≤ s3.card := by omega
  have hne3 : s3.Nonempty :=
    Finset.card_pos.mp (by linarith)
  let c := Finset.min' s3 hne3
  have hc : c ∈ s3 := Finset.min'_mem s3 hne3
  have hc_s2 : c ∈ s2 := Finset.mem_of_mem_erase hc
  have hc_s : c ∈ s := Finset.mem_of_mem_erase hc_s2
  have hne_bc : c ≠ b := Finset.ne_of_mem_erase hc
  have hbc : b < c := by
    have hle : b ≤ c := hb_le c hc_s2
    exact lt_of_le_of_ne hle hne_bc.symm
  exact
    ⟨a, b, c, ha, hb_s, hc_s, hab, hbc⟩

private lemma grid_interval_at_most_two
    (rho : ℝ) (hrho : 0 < rho)
    (a b : ℝ) (hlen : b - a ≤ rho) :
    ∃ s : Finset ℤ,
      (∀ n : ℤ,
        n ∈ s ↔
          ((n : ℝ) + 1 / 2) *
              (rho / Real.sqrt 3) ∈ Set.Ico a b) ∧
      s.card ≤ 2 := by
  let side := rho / Real.sqrt 3
  have hside_pos : 0 < side := by positivity
  have h2side : rho < 2 * side := by
    have h : (2 : ℝ) / Real.sqrt 3 > 1 :=
      two_div_sqrt3_gt_one
    have h' :
        2 * side = (2 / Real.sqrt 3) * rho := by
      ring
    rw [h']
    nlinarith
  let lo : ℤ := Int.ceil (a / side - 1 / 2)
  let hi : ℤ := Int.floor (b / side - 1 / 2)
  let s : Finset ℤ :=
    (Finset.Icc lo hi).filter fun n =>
      ((n : ℝ) + 1 / 2) * side ∈ Set.Ico a b
  have hmem :
      ∀ n : ℤ,
        n ∈ s ↔
          ((n : ℝ) + 1 / 2) * side ∈ Set.Ico a b := by
    intro n
    simp only [s, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      have h1 :
          a ≤ ((n : ℝ) + 1 / 2) * side := h.1
      have h2 :
          ((n : ℝ) + 1 / 2) * side < b := h.2
      have hlo : lo ≤ n := by
        simp only [lo]
        have h3 : a / side - 1 / 2 ≤ (n : ℝ) := by
          calc
            a / side - 1 / 2
                ≤ (((n : ℝ) + 1 / 2) * side) /
                    side - 1 / 2 := by
              gcongr
            _ = (n : ℝ) := by
              field_simp [hside_pos.ne']
              <;> ring
        exact Int.ceil_le.mpr h3
      have hhi : n ≤ hi := by
        simp only [hi]
        have h3 : (n : ℝ) < b / side - 1 / 2 := by
          calc
            (n : ℝ) =
                (((n : ℝ) + 1 / 2) * side) /
                    side - 1 / 2 := by
              field_simp [hside_pos.ne']
              <;> ring
            _ < b / side - 1 / 2 := by gcongr
        exact Int.le_floor.mpr (by linarith)
      exact ⟨⟨hlo, hhi⟩, h⟩
  have hcard : s.card ≤ 2 := by
    by_contra h
    have h' : 3 ≤ s.card := by omega
    rcases finset_int_three_elements h' with
      ⟨n1, n2, n3, hn1, _hn2, hn3, h12, h23⟩
    have hdiff :
        (n3 : ℝ) - (n1 : ℝ) ≥ 2 := by
      exact_mod_cast (by linarith)
    have hval1 :
        ((n1 : ℝ) + 1 / 2) * side ∈ Set.Ico a b :=
      (hmem n1).mp hn1
    have hval3 :
        ((n3 : ℝ) + 1 / 2) * side ∈ Set.Ico a b :=
      (hmem n3).mp hn3
    have hspan :
        ((n3 : ℝ) + 1 / 2) * side -
            ((n1 : ℝ) + 1 / 2) * side <
          b - a := by
      linarith [hval1.1, hval3.2]
    have hspan2 :
        ((n3 : ℝ) + 1 / 2) * side -
            ((n1 : ℝ) + 1 / 2) * side =
          ((n3 : ℝ) - (n1 : ℝ)) * side := by
      ring
    rw [hspan2] at hspan
    have h4 :
        2 * side ≤
          ((n3 : ℝ) - (n1 : ℝ)) * side := by
      nlinarith
    linarith
  exact ⟨s, hmem, hcard⟩

private lemma floor_bin_at_most_two
    (rho : ℝ) (hrho : 0 < rho)
    (c : ℝ) (bin : ℤ) :
    ∃ s : Finset ℤ,
      (∀ x : ℤ,
        x ∈ s ↔
          Int.floor
              ((((x : ℝ) + 1 / 2) *
                    (rho / Real.sqrt 3) + c) / rho) =
            bin) ∧
      s.card ≤ 2 := by
  let side := rho / Real.sqrt 3
  let left := (bin : ℝ) * rho - c
  let right := ((bin : ℝ) + 1) * rho - c
  have hlen : right - left = rho := by ring
  rcases
      grid_interval_at_most_two
        rho hrho left right (by linarith) with
    ⟨s, hmem, hcard⟩
  let selected : Finset ℤ :=
    s.filter fun x =>
      Int.floor
          ((((x : ℝ) + 1 / 2) * side + c) / rho) =
        bin
  have hfloor :
      ∀ x : ℤ,
        Int.floor
            ((((x : ℝ) + 1 / 2) * side + c) / rho) =
            bin ↔
          ((x : ℝ) + 1 / 2) * side ∈
            Set.Ico left right := by
    intro x
    rw [Int.floor_eq_iff]
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · calc
          (bin : ℝ) * rho - c
              ≤ ((((x : ℝ) + 1 / 2) * side + c) /
                    rho) * rho - c := by
            gcongr
          _ = ((x : ℝ) + 1 / 2) * side := by
            field_simp [hrho.ne']
            <;> ring
      · calc
          ((x : ℝ) + 1 / 2) * side =
              ((((x : ℝ) + 1 / 2) * side + c) /
                  rho) * rho - c := by
            field_simp [hrho.ne']
            <;> ring
          _ < ((bin : ℝ) + 1) * rho - c := by
            gcongr
    · rintro ⟨h1, h2⟩
      constructor
      · calc
          (bin : ℝ) =
              (((bin : ℝ) * rho - c) + c) / rho := by
            field_simp [hrho.ne']
            <;> ring
          _ ≤ (((x : ℝ) + 1 / 2) * side + c) /
              rho := by
            gcongr
      · calc
          (((x : ℝ) + 1 / 2) * side + c) / rho
              < ((((bin : ℝ) + 1) * rho - c) + c) /
                  rho := by
            gcongr
          _ = (bin : ℝ) + 1 := by
            field_simp [hrho.ne']
            <;> ring
  have hselected :
      ∀ x : ℤ,
        x ∈ selected ↔
          Int.floor
              ((((x : ℝ) + 1 / 2) * side + c) / rho) =
            bin := by
    intro x
    simp only [selected, Finset.mem_filter]
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      exact ⟨(hmem x).mpr ((hfloor x).mp h), h⟩
  exact
    ⟨selected, hselected,
      (Finset.card_filter_le _ _).trans hcard⟩

private lemma snapped_height_point_injective_z
    (rho : ℝ) (hrho : 0 < rho)
    (f : ℝ → ℝ) (baseHeightIndex : ℤ)
    (idx1 idx2 : ℤ × ℤ × ℤ) :
    wz1Lemma23SnappedHeightPoint rho f baseHeightIndex idx1 =
        wz1Lemma23SnappedHeightPoint rho f baseHeightIndex idx2 →
      idx1.2.2 = idx2.2.2 := by
  let side := gridSide (rho / 2)
  have hside_pos : 0 < side := by
    simp only [side, gridSide]
    positivity
  intro h
  have h0 :
      (wz1Lemma23SnappedHeightPoint
          rho f baseHeightIndex idx1) 0 =
        (wz1Lemma23SnappedHeightPoint
          rho f baseHeightIndex idx2) 0 := by
    rw [h]
  have h1 :
      ∀ idx,
        (wz1Lemma23SnappedHeightPoint
            rho f baseHeightIndex idx) 0 =
          ((idx.2.2 : ℝ) - (baseHeightIndex : ℝ)) *
            side := by
    intro idx
    simp [wz1Lemma23SnappedHeightPoint,
      wz1Lemma23SnappedBaseHeight,
      wz1Lemma23HeightGraphPoint,
      wz1Lemma23SnappedPoint, wz1Lemma23CellCenter,
      point3, side]
    <;> ring
  rw [h1 idx1, h1 idx2] at h0
  have h2 :
      ((idx1.2.2 : ℝ) - (idx2.2.2 : ℝ)) * side =
        0 := by
    linarith
  have h3 :
      (idx1.2.2 : ℝ) = (idx2.2.2 : ℝ) := by
    have h4 :
        (idx1.2.2 : ℝ) - (idx2.2.2 : ℝ) = 0 :=
      (mul_eq_zero.mp h2).resolve_right hside_pos.ne'
    linarith
  exact_mod_cast h3

private lemma snapped_local_point_injective_y
    (rho : ℝ) (hrho : 0 < rho)
    (g : ℝ → ℝ)
    (idx1 idx2 : ℤ × ℤ × ℤ) :
    wz1Lemma23SnappedLocalPoint rho g idx1 =
        wz1Lemma23SnappedLocalPoint rho g idx2 →
      idx1.2.1 = idx2.2.1 := by
  let side := gridSide (rho / 2)
  have hside_pos : 0 < side := by
    simp only [side, gridSide]
    positivity
  intro h
  have h1 :
      (wz1Lemma23SnappedLocalPoint rho g idx1) 1 =
        (wz1Lemma23SnappedLocalPoint rho g idx2) 1 := by
    rw [h]
  have h2 :
      ∀ idx,
        (wz1Lemma23SnappedLocalPoint rho g idx) 1 =
          ((idx.2.1 : ℝ) + 1 / 2) * side := by
    intro idx
    simp [wz1Lemma23SnappedLocalPoint,
      wz1Lemma23LocalGraphPoint,
      wz1Lemma23CenteredLocal,
      wz1Lemma23SnappedPoint, wz1Lemma23CellCenter,
      point3, side]
    <;> aesop
    <;> ring
  rw [h2 idx1, h2 idx2] at h1
  have h3 :
      ((idx1.2.1 : ℝ) - (idx2.2.1 : ℝ)) * side =
        0 := by
    linarith
  have h4 :
      (idx1.2.1 : ℝ) = (idx2.2.1 : ℝ) := by
    have h5 :
        (idx1.2.1 : ℝ) - (idx2.2.1 : ℝ) = 0 :=
      (mul_eq_zero.mp h3).resolve_right hside_pos.ne'
    linarith
  exact_mod_cast h4

lemma wz1Lemma23_global_bin_x_bound
    (rho : ℝ) (hrho : 0 < rho)
    (f : ℝ → ℝ) (y z : ℤ) (bin : ℤ) :
    ∃ s : Finset ℤ,
      (∀ x : ℤ,
        x ∈ s ↔
          wz1Lemma23SnappedGlobalBin rho f (x, y, z) =
            bin) ∧
      s.card ≤ 2 := by
  let side := rho / Real.sqrt 3
  have hside_eq : gridSide (rho / 2) = side := by
    simp [gridSide, side]
    ring
  let c : ℝ :=
    f (((z : ℝ) + 1 / 2) * side) *
      (((y : ℝ) + 1 / 2) * side)
  have h_cell0 :
      ∀ x : ℤ,
        (wz1Lemma23SnappedPoint rho (x, y, z)) 0 =
          ((x : ℝ) + 1 / 2) * side := by
    intro x
    simp [wz1Lemma23SnappedPoint,
      wz1Lemma23CellCenter, point3, hside_eq]
    <;> aesop
    <;> ring
  have h_cell1 :
      ∀ x : ℤ,
        (wz1Lemma23SnappedPoint rho (x, y, z)) 1 =
          ((y : ℝ) + 1 / 2) * side := by
    intro x
    simp [wz1Lemma23SnappedPoint,
      wz1Lemma23CellCenter, point3, hside_eq]
    <;> aesop
    <;> ring
  have h_cell2 :
      ∀ x : ℤ,
        (wz1Lemma23SnappedPoint rho (x, y, z)) 2 =
          ((z : ℝ) + 1 / 2) * side := by
    intro x
    simp [wz1Lemma23SnappedPoint,
      wz1Lemma23CellCenter, point3, hside_eq]
    <;> aesop
    <;> ring
  have h_global_coord :
      ∀ x : ℤ,
        wz1Lemma23GlobalCoordinate f
            (wz1Lemma23SnappedPoint rho (x, y, z)) =
          ((x : ℝ) + 1 / 2) * side + c := by
    intro x
    rw [wz1Lemma23GlobalCoordinate,
      h_cell0 x, h_cell1 x, h_cell2 x] <;> rfl
  have h_main :
      ∀ x : ℤ,
        wz1Lemma23SnappedGlobalBin rho f (x, y, z) =
          Int.floor
            ((((x : ℝ) + 1 / 2) * side + c) / rho) := by
    intro x
    simp only [wz1Lemma23SnappedGlobalBin]
    rw [h_global_coord x]
  rcases floor_bin_at_most_two rho hrho c bin with
    ⟨s, hmem, hcard⟩
  refine ⟨s, ?_, hcard⟩
  intro x
  rw [h_main x]
  exact hmem x

private lemma local_bin_x_bound
    (rho : ℝ) (hrho : 0 < rho)
    (g : ℝ → ℝ) (y z : ℤ) (bin : ℤ) :
    ∃ s : Finset ℤ,
      (∀ x : ℤ,
        x ∈ s ↔
          (wz1Lemma23SnappedLocalKey rho g
            (x, y, z)).2 = bin) ∧
      s.card ≤ 2 := by
  let side := rho / Real.sqrt 3
  have hside_eq : gridSide (rho / 2) = side := by
    simp [gridSide, side]
    ring
  let c : ℝ :=
    g (((y : ℝ) + 1 / 2) * side) *
      (((z : ℝ) + 1 / 2) * side)
  have h_cell0 :
      ∀ x : ℤ,
        (wz1Lemma23SnappedPoint rho (x, y, z)) 0 =
          ((x : ℝ) + 1 / 2) * side := by
    intro x
    simp [wz1Lemma23SnappedPoint,
      wz1Lemma23CellCenter, point3, hside_eq]
    <;> aesop
    <;> ring
  have h_cell1 :
      ∀ x : ℤ,
        (wz1Lemma23SnappedPoint rho (x, y, z)) 1 =
          ((y : ℝ) + 1 / 2) * side := by
    intro x
    simp [wz1Lemma23SnappedPoint,
      wz1Lemma23CellCenter, point3, hside_eq]
    <;> aesop
    <;> ring
  have h_cell2 :
      ∀ x : ℤ,
        (wz1Lemma23SnappedPoint rho (x, y, z)) 2 =
          ((z : ℝ) + 1 / 2) * side := by
    intro x
    simp [wz1Lemma23SnappedPoint,
      wz1Lemma23CellCenter, point3, hside_eq]
    <;> aesop
    <;> ring
  have h_local_coord :
      ∀ x : ℤ,
        wz1Lemma23LocalCoordinate g
            (wz1Lemma23SnappedPoint rho (x, y, z)) =
          ((x : ℝ) + 1 / 2) * side + c := by
    intro x
    rw [wz1Lemma23LocalCoordinate,
      h_cell0 x, h_cell1 x, h_cell2 x] <;> rfl
  have h_main :
      ∀ x : ℤ,
        (wz1Lemma23SnappedLocalKey rho g
          (x, y, z)).2 =
          Int.floor
            ((((x : ℝ) + 1 / 2) * side + c) / rho) := by
    intro x
    simp only [wz1Lemma23SnappedLocalKey]
    rw [h_local_coord x]
  rcases floor_bin_at_most_two rho hrho c bin with
    ⟨s, hmem, hcard⟩
  refine ⟨s, ?_, hcard⟩
  intro x
  rw [h_main x]
  exact hmem x

theorem wz1_lemma23_snapped_tripartite_fiber :
    WZ1Lemma23SnappedTripartiteFiberStatement := by
  intro rho f g cells baseHeightIndex baseGlobalBin hrho
  classical
  dsimp only
  let cycles :=
    wz1Lemma23SnappedBaseCycles
      rho f g cells baseHeightIndex baseGlobalBin
  let edge :=
    wz1Lemma23SnappedTripartiteEdge
      rho f g baseHeightIndex
  let edges := cycles.image edge
  have h_main :
      ∀ value ∈ edges,
        (cycles.filter fun path =>
          edge path = value).card ≤ 16 := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with
      ⟨p0, hp0, rfl⟩
    set z2 : ℤ := p0.2.1.2.2 with hz2_def
    set y1 : ℤ := p0.1.2.1 with hy1_def
    set y3 : ℤ := p0.2.2.1.2.1 with hy3_def
    set z1 : ℤ := baseHeightIndex with hz1_def
    let fiber :=
      cycles.filter fun path => edge path = edge p0
    rcases
        wz1Lemma23_global_bin_x_bound
          rho hrho f y1 z1 baseGlobalBin with
      ⟨X1, hX1_mem, hX1_card⟩
    let X2 (x1 : ℤ) : Finset ℤ :=
      Classical.choose
        (local_bin_x_bound rho hrho g y1 z2
          (wz1Lemma23SnappedLocalKey rho g
            (x1, y1, z1)).2)
    have hX2_spec :
        ∀ x1 : ℤ,
          (∀ x : ℤ,
            x ∈ X2 x1 ↔
              (wz1Lemma23SnappedLocalKey rho g
                (x, y1, z2)).2 =
              (wz1Lemma23SnappedLocalKey rho g
                (x1, y1, z1)).2) ∧
          (X2 x1).card ≤ 2 := by
      intro x1
      exact
        Classical.choose_spec
          (local_bin_x_bound rho hrho g y1 z2
            (wz1Lemma23SnappedLocalKey rho g
              (x1, y1, z1)).2)
    let X3 (x2 : ℤ) : Finset ℤ :=
      Classical.choose
        (wz1Lemma23_global_bin_x_bound rho hrho f y3 z2
          (wz1Lemma23SnappedGlobalBin rho f
            (x2, y1, z2)))
    have hX3_spec :
        ∀ x2 : ℤ,
          (∀ x : ℤ,
            x ∈ X3 x2 ↔
              wz1Lemma23SnappedGlobalBin rho f
                (x, y3, z2) =
              wz1Lemma23SnappedGlobalBin rho f
                (x2, y1, z2)) ∧
          (X3 x2).card ≤ 2 := by
      intro x2
      exact
        Classical.choose_spec
          (wz1Lemma23_global_bin_x_bound rho hrho f y3 z2
            (wz1Lemma23SnappedGlobalBin rho f
              (x2, y1, z2)))
    let X4 (x3 : ℤ) : Finset ℤ :=
      Classical.choose
        (local_bin_x_bound rho hrho g y3 z1
          (wz1Lemma23SnappedLocalKey rho g
            (x3, y3, z2)).2)
    have hX4_spec :
        ∀ x3 : ℤ,
          (∀ x : ℤ,
            x ∈ X4 x3 ↔
              (wz1Lemma23SnappedLocalKey rho g
                (x, y3, z1)).2 =
              (wz1Lemma23SnappedLocalKey rho g
                (x3, y3, z2)).2) ∧
          (X4 x3).card ≤ 2 := by
      intro x3
      exact
        Classical.choose_spec
          (local_bin_x_bound rho hrho g y3 z1
            (wz1Lemma23SnappedLocalKey rho g
              (x3, y3, z2)).2)
    let Path :=
      (ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ)
    let S3 (x1 x2 : ℤ) : Finset Path :=
      (X3 x2).biUnion fun x3 =>
        (X4 x3).image fun x4 =>
          ((x1, y1, z1), (x2, y1, z2),
            (x3, y3, z2), (x4, y3, z1))
    let S2 (x1 : ℤ) : Finset Path :=
      (X2 x1).biUnion fun x2 => S3 x1 x2
    let candidates : Finset Path :=
      X1.biUnion fun x1 => S2 x1
    have h_edge_unfold :
        ∀ path,
          edge path =
            (wz1Lemma23SnappedHeightPoint
                rho f baseHeightIndex path.2.1,
              wz1Lemma23SnappedLocalPoint rho g path.1,
              wz1Lemma23SnappedLocalPoint
                rho g path.2.2.1) := by
      intro path
      simp [edge, wz1Lemma23SnappedTripartiteEdge,
        wz1Lemma23TripartiteEdge] <;> rfl
    have hfiber_subset :
        fiber ⊆ candidates := by
      intro path hpath
      have hpath_cycles :
          path ∈ cycles := (Finset.mem_filter.mp hpath).1
      have hedge :
          edge path = edge p0 :=
        (Finset.mem_filter.mp hpath).2
      have hfour :
          path ∈
            wz1Lemma23SnappedFourCycles rho f g cells :=
        (Finset.mem_filter.mp hpath_cycles).1
      have hbaseHeight :
          wz1Lemma23SnappedHeight path.1 =
            baseHeightIndex :=
        (Finset.mem_filter.mp hpath_cycles).2.1
      have hbaseGlobal :
          wz1Lemma23SnappedGlobalBin rho f path.1 =
            baseGlobalBin :=
        (Finset.mem_filter.mp hpath_cycles).2.2
      have hfour_data :
          wz1Lemma23SameSnappedLocalGrain
              rho g path.1 path.2.1 ∧
          wz1Lemma23SameSnappedLocalGrain
              rho g path.2.2.2 path.2.2.1 ∧
          wz1Lemma23SnappedHeight path.1 =
              wz1Lemma23SnappedHeight path.2.2.2 ∧
          wz1Lemma23SnappedHeight path.2.1 =
              wz1Lemma23SnappedHeight path.2.2.1 ∧
          wz1Lemma23SnappedGlobalBin rho f path.2.1 =
              wz1Lemma23SnappedGlobalBin
                rho f path.2.2.1 := by
        simp only [wz1Lemma23SnappedFourCycles,
          wz1Lemma23FourCycles, Finset.mem_filter] at hfour
        exact hfour.2
      have hy1 : path.1.2.1 = y1 := by
        have hcoordinate :
            (edge path).2.1 = (edge p0).2.1 := by
          rw [hedge]
        rw [h_edge_unfold path, h_edge_unfold p0] at hcoordinate
        exact
          snapped_local_point_injective_y
            rho hrho g path.1 p0.1 hcoordinate
      have hz2 : path.2.1.2.2 = z2 := by
        have hcoordinate :
            (edge path).1 = (edge p0).1 := by
          rw [hedge]
        rw [h_edge_unfold path, h_edge_unfold p0] at hcoordinate
        exact
          snapped_height_point_injective_z
            rho hrho f baseHeightIndex
            path.2.1 p0.2.1 hcoordinate
      have hy3 : path.2.2.1.2.1 = y3 := by
        have hcoordinate :
            (edge path).2.2 = (edge p0).2.2 := by
          rw [hedge]
        rw [h_edge_unfold path, h_edge_unfold p0] at hcoordinate
        exact
          snapped_local_point_injective_y
            rho hrho g path.2.2.1 p0.2.2.1
            hcoordinate
      have hz1 : path.1.2.2 = z1 := by
        simpa [z1, wz1Lemma23SnappedHeight] using
          hbaseHeight
      have hpath2_y : path.2.1.2.1 = y1 := by
        have hkey :
            wz1Lemma23SnappedLocalKey rho g path.1 =
              wz1Lemma23SnappedLocalKey
                rho g path.2.1 :=
          hfour_data.1
        have hfirst :
            path.1.2.1 = path.2.1.2.1 := by
          simpa [wz1Lemma23SnappedLocalKey] using
            congr_arg Prod.fst hkey
        exact hfirst.symm.trans hy1
      have hpath3_z : path.2.2.1.2.2 = z2 := by
        have hheight :
            path.2.1.2.2 = path.2.2.1.2.2 := by
          simpa [wz1Lemma23SnappedHeight] using
            hfour_data.2.2.2.1
        exact hheight.symm.trans hz2
      have hpath4_y : path.2.2.2.2.1 = y3 := by
        have hkey :
            wz1Lemma23SnappedLocalKey rho g path.2.2.2 =
              wz1Lemma23SnappedLocalKey
                rho g path.2.2.1 :=
          hfour_data.2.1
        have hfirst :
            path.2.2.2.2.1 = path.2.2.1.2.1 := by
          simpa [wz1Lemma23SnappedLocalKey] using
            congr_arg Prod.fst hkey
        exact hfirst.trans hy3
      have hpath4_z : path.2.2.2.2.2 = z1 := by
        have hheight :
            path.1.2.2 = path.2.2.2.2.2 := by
          simpa [wz1Lemma23SnappedHeight] using
            hfour_data.2.2.1
        exact hheight.symm.trans hz1
      set x1 : ℤ := path.1.1 with hx1
      set x2 : ℤ := path.2.1.1 with hx2
      set x3 : ℤ := path.2.2.1.1 with hx3
      set x4 : ℤ := path.2.2.2.1 with hx4
      have hx1_mem : x1 ∈ X1 := by
        apply (hX1_mem x1).mpr
        have heq :
            (x1, y1, z1) = path.1 := by
          ext <;> simp [hx1, hy1, hz1] <;> tauto
        rw [heq]
        exact hbaseGlobal
      have hx2_mem : x2 ∈ X2 x1 := by
        apply (hX2_spec x1).1 x2 |>.mpr
        have heq2 :
            (x2, y1, z2) = path.2.1 := by
          ext <;> simp [hx2, hpath2_y, hz2] <;> tauto
        have heq1 :
            (x1, y1, z1) = path.1 := by
          ext <;> simp [hx1, hy1, hz1] <;> tauto
        rw [heq2, heq1]
        exact congr_arg Prod.snd hfour_data.1.symm
      have hx3_mem : x3 ∈ X3 x2 := by
        apply (hX3_spec x2).1 x3 |>.mpr
        have heq3 :
            (x3, y3, z2) = path.2.2.1 := by
          ext <;> simp [hx3, hy3, hpath3_z] <;> tauto
        have heq2 :
            (x2, y1, z2) = path.2.1 := by
          ext <;> simp [hx2, hpath2_y, hz2] <;> tauto
        rw [heq3, heq2]
        exact hfour_data.2.2.2.2.symm
      have hx4_mem : x4 ∈ X4 x3 := by
        apply (hX4_spec x3).1 x4 |>.mpr
        have heq4 :
            (x4, y3, z1) = path.2.2.2 := by
          ext <;> simp [hx4, hpath4_y, hpath4_z] <;>
            tauto
        have heq3 :
            (x3, y3, z2) = path.2.2.1 := by
          ext <;> simp [hx3, hy3, hpath3_z] <;> tauto
        rw [heq4, heq3]
        exact congr_arg Prod.snd hfour_data.2.1
      have hpath_eq :
          path =
            ((x1, y1, z1), (x2, y1, z2),
              (x3, y3, z2), (x4, y3, z1)) := by
        ext <;>
          simp [hx1, hx2, hx3, hx4, hy1, hz1,
            hpath2_y, hz2, hy3, hpath3_z,
            hpath4_y, hpath4_z] <;>
          tauto
      rw [hpath_eq]
      simp only [candidates, Finset.mem_biUnion]
      refine ⟨x1, hx1_mem, ?_⟩
      simp only [S2, Finset.mem_biUnion]
      refine ⟨x2, hx2_mem, ?_⟩
      simp only [S3, Finset.mem_biUnion]
      refine ⟨x3, hx3_mem, ?_⟩
      exact Finset.mem_image.mpr ⟨x4, hx4_mem, rfl⟩
    have hS3 :
        ∀ x1 x2 : ℤ, (S3 x1 x2).card ≤ 4 := by
      intro x1 x2
      let fourth (x3 : ℤ) : Finset Path :=
        (X4 x3).image fun x4 =>
          ((x1, y1, z1), (x2, y1, z2),
            (x3, y3, z2), (x4, y3, z1))
      calc
        (S3 x1 x2).card
            ≤ ∑ x3 ∈ X3 x2, (fourth x3).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _x3 ∈ X3 x2, 2 := by
          apply Finset.sum_le_sum
          intro x3 _
          exact Finset.card_image_le.trans (hX4_spec x3).2
        _ = (X3 x2).card * 2 := by simp
        _ ≤ 2 * 2 := by
          nlinarith [(hX3_spec x2).2]
        _ = 4 := by norm_num
    have hS2 :
        ∀ x1 : ℤ, (S2 x1).card ≤ 8 := by
      intro x1
      calc
        (S2 x1).card
            ≤ ∑ x2 ∈ X2 x1, (S3 x1 x2).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _x2 ∈ X2 x1, 4 :=
          Finset.sum_le_sum fun x2 _ => hS3 x1 x2
        _ = (X2 x1).card * 4 := by simp
        _ ≤ 2 * 4 := by
          nlinarith [(hX2_spec x1).2]
        _ = 8 := by norm_num
    have hcandidates : candidates.card ≤ 16 := by
      calc
        candidates.card
            ≤ ∑ x1 ∈ X1, (S2 x1).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _x1 ∈ X1, 8 :=
          Finset.sum_le_sum fun x1 _ => hS2 x1
        _ = X1.card * 8 := by simp
        _ ≤ 2 * 8 := by nlinarith
        _ = 16 := by norm_num
    exact
      (Finset.card_le_card hfiber_subset).trans hcandidates
  exact
    ⟨h_main,
      Finset.card_le_mul_card_image cycles 16 h_main⟩

end

end Kakeya.Assouad
