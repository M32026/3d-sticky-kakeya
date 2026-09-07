module

/-
  Transfer lemmas for dyadic-square thickening on a common dyadic grid.

  Given P and Q = config.pointSet where:
  - P ⊆ Q
  - Q is the union of Δ^m-dyadic squares each intersecting P
  - 1/Δ is a positive integer (common dyadic base)

  Then:
  1. P and Q occupy exactly the same dyadic cells at every scale Δ^i, i ≤ m
  2. IsDyadicUniform transfers exactly (same N)
  3. IsSetBetweenScales transfers with geometric constant inflation
  4. IsRegularBetweenScales transfers with geometric constant inflation

  Whiteprint node: section9 / thickening_transfer
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.DyadicUniform
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.ExactDyadicCount
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Geometry.SSetThickening
public import MyLeanRepo.DiscretisedFurstenbergEstimate.LemmaE_Helpers
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.MultiscaleDecomposition

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DirecretisedFurstenbergEstimate.A10
open LemmaE

/-! # Geometric helpers -/

/-- Any two points in a dyadic square of side δ are at distance ≤ 2δ.
    (Uses L1 bound: √(a²+b²) ≤ |a|+|b| ≤ 2δ.) -/
lemma dyadicSquare_diameter {δ : ℝ} (hδ_pos : 0 < δ) {i j : ℤ} {x y : EuclideanPlane}
    (hx : x ∈ dyadicSquare δ i j) (hy : y ∈ dyadicSquare δ i j) :
    dist x y ≤ 2 * δ := by
  have h1 : |x 0 - y 0| ≤ δ := by
    have hxi1 : (i : ℝ) * δ ≤ x 0 := hx.1.1
    have hxi2 : x 0 < ((i : ℝ) + 1) * δ := hx.1.2
    have hyi1 : (i : ℝ) * δ ≤ y 0 := hy.1.1
    have hyi2 : y 0 < ((i : ℝ) + 1) * δ := hy.1.2
    rw [abs_sub_le_iff] <;> constructor <;> linarith
  have h2 : |x 1 - y 1| ≤ δ := by
    have hxj1 : (j : ℝ) * δ ≤ x 1 := hx.2.1
    have hxj2 : x 1 < ((j : ℝ) + 1) * δ := hx.2.2
    have hyj1 : (j : ℝ) * δ ≤ y 1 := hy.2.1
    have hyj2 : y 1 < ((j : ℝ) + 1) * δ := hy.2.2
    rw [abs_sub_le_iff] <;> constructor <;> linarith
  have h3 : dist x y ≤ |x 0 - y 0| + |x 1 - y 1| := by
    let v := x - y
    have h_norm2 : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
      have h := EuclideanSpace.real_norm_sq_eq v
      rw [h, Fin.sum_univ_two]
    have h_ineq : ‖v‖ ^ 2 ≤ (|v 0| + |v 1|) ^ 2 := by
      rw [h_norm2]
      have h4 : v 0 ^ 2 + v 1 ^ 2 ≤ (|v 0| + |v 1|) ^ 2 := by
        have h51 : |v 0| ^ 2 = (v 0) ^ 2 := by rw [sq_abs]
        have h52 : |v 1| ^ 2 = (v 1) ^ 2 := by rw [sq_abs]
        have h_pos : 0 ≤ 2 * |v 0| * |v 1| := by positivity
        have h_eq : (|v 0| + |v 1|) ^ 2 = |v 0| ^ 2 + |v 1| ^ 2 + 2 * |v 0| * |v 1| := by ring
        rw [h_eq, h51, h52]
        exact le_add_of_nonneg_right h_pos
      exact h4
    have h8 : 0 ≤ ‖v‖ := by positivity
    have h9 : 0 ≤ |v 0| + |v 1| := by positivity
    have h10 : ‖v‖ ≤ |v 0| + |v 1| := by nlinarith
    have hv0 : v 0 = x 0 - y 0 := by simp [v]
    have hv1 : v 1 = x 1 - y 1 := by simp [v]
    rw [dist_eq_norm]
    rw [hv0, hv1] at h10
    exact h10
  linarith

/-! # Nested containment on common dyadic base -/

/-- A Δ^m-dyadic square that meets a Δ^i-dyadic square (i ≤ m) is contained
    in it, when 1/Δ is a positive integer. -/
lemma dyadicSquare_nested_pow
    {n_dyadic : ℕ} (hn_pos : 0 < n_dyadic)
    {Δ : ℝ} (hΔ_int : (1 : ℝ) = (n_dyadic : ℝ) * Δ)
    {m i : ℕ} (hi_le_m : i ≤ m)
    {k l a b : ℤ}
    (h_inter : (dyadicSquare (Δ ^ m) k l ∩ dyadicSquare (Δ ^ i) a b).Nonempty) :
    dyadicSquare (Δ ^ m) k l ⊆ dyadicSquare (Δ ^ i) a b :=
  dyadicSquare_nested_containment hn_pos hΔ_int hi_le_m
    (p := (a, b)) (q := (k, l)) h_inter

/-! # Exact occupied-cell equality -/

/-- If Q is the union of Δ^m-dyadic squares each intersecting P, P ⊆ Q,
    and all scales share the common dyadic base Δ = 1/n, then P and Q
    intersect exactly the same dyadic squares at any scale Δ^i with i ≤ m. -/
lemma same_occupied_cells
    {P Q : Set EuclideanPlane} {n_dyadic : ℕ} {Δ : ℝ} {m i : ℕ}
    (hn_pos : 0 < n_dyadic)
    (hΔ_int : (1 : ℝ) = (n_dyadic : ℝ) * Δ)
    (hi_le_m : i ≤ m)
    (hP_sub_Q : P ⊆ Q)
    (hQ_thick : ∀ y ∈ Q, ∃ (S : Set EuclideanPlane),
      (∃ (k l : ℤ), S = dyadicSquare (Δ ^ m) k l) ∧
      y ∈ S ∧ (P ∩ S).Nonempty) :
    ∀ (a b : ℤ), (P ∩ dyadicSquare (Δ ^ i) a b).Nonempty ↔
      (Q ∩ dyadicSquare (Δ ^ i) a b).Nonempty := by
  intro a b
  constructor
  · rintro ⟨p, hpP, hpS⟩
    exact ⟨p, hP_sub_Q hpP, hpS⟩
  · rintro ⟨q, hqQ, hqS⟩
    rcases hQ_thick q hqQ with ⟨S, ⟨k, l, hS_eq⟩, hq_in_S, ⟨p, hpP, hp_in_S⟩⟩
    have hS_sub : S ⊆ dyadicSquare (Δ ^ i) a b := by
      rw [hS_eq]
      have h_inter' : (dyadicSquare (Δ ^ m) k l ∩ dyadicSquare (Δ ^ i) a b).Nonempty := by
        rw [hS_eq] at hq_in_S
        exact ⟨q, hq_in_S, hqS⟩
      exact dyadicSquare_nested_pow hn_pos hΔ_int hi_le_m h_inter'
    have hp_in_coarse : p ∈ dyadicSquare (Δ ^ i) a b := hS_sub hp_in_S
    exact ⟨p, hpP, hp_in_coarse⟩

/-! # Exact IsDyadicUniform transfer -/

/-- Transfer IsDyadicUniform from P to its Δ^m-square thickening Q. -/
lemma IsDyadicUniform.thickening_transfer
    {P Q : Set EuclideanPlane} {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    {n_dyadic : ℕ}
    (h : IsDyadicUniform P m Δ N)
    (hP_sub_Q : P ⊆ Q)
    (hn_pos : 0 < n_dyadic)
    (hΔ_int : (1 : ℝ) = (n_dyadic : ℝ) * Δ)
    (hQ_thick : ∀ y ∈ Q, ∃ (S : Set EuclideanPlane),
      (∃ (k l : ℤ), S = dyadicSquare (Δ ^ m) k l) ∧
      y ∈ S ∧ (P ∩ S).Nonempty) :
    IsDyadicUniform Q m Δ N := by
  rcases h with ⟨hΔ_pos, hΔ_lt_one, hP_nonempty, hN_pos, hmain⟩
  have hQ_nonempty : Q.Nonempty := hP_nonempty.mono hP_sub_Q
  refine' ⟨hΔ_pos, hΔ_lt_one, hQ_nonempty, hN_pos, _⟩
  intro i hi a b hnonempty
  have h_i_le_m : i ≤ m := by omega
  have h_i1_le_m : i + 1 ≤ m := by omega
  have h_iff_P : (P ∩ dyadicSquare (Δ ^ i) a b).Nonempty :=
    (same_occupied_cells hn_pos hΔ_int h_i_le_m hP_sub_Q hQ_thick a b).mpr hnonempty
  have h_same_set : {p : ℤ × ℤ | ((Q ∩ dyadicSquare (Δ ^ i) a b) ∩ dyadicSquare (Δ ^ (i + 1)) p.1 p.2).Nonempty} =
      {p : ℤ × ℤ | ((P ∩ dyadicSquare (Δ ^ i) a b) ∩ dyadicSquare (Δ ^ (i + 1)) p.1 p.2).Nonempty} := by
    ext p
    rcases p with ⟨k, l⟩
    simp only [Set.mem_setOf_eq]
    by_cases h_inter : (dyadicSquare (Δ ^ (i + 1)) k l ∩ dyadicSquare (Δ ^ i) a b).Nonempty
    · have h_nest : dyadicSquare (Δ ^ (i + 1)) k l ⊆ dyadicSquare (Δ ^ i) a b :=
        @dyadicSquare_nested_pow n_dyadic hn_pos Δ hΔ_int (i + 1) i (by omega) k l a b h_inter
      have hQ_iff : ((Q ∩ dyadicSquare (Δ ^ i) a b) ∩ dyadicSquare (Δ ^ (i + 1)) k l).Nonempty ↔
          (Q ∩ dyadicSquare (Δ ^ (i + 1)) k l).Nonempty := by
        constructor
        · rintro ⟨x, hx1, hx2⟩; exact ⟨x, hx1.1, hx2⟩
        · rintro ⟨x, hxQ, hxFine⟩; exact ⟨x, ⟨hxQ, h_nest hxFine⟩, hxFine⟩
      have hP_iff : ((P ∩ dyadicSquare (Δ ^ i) a b) ∩ dyadicSquare (Δ ^ (i + 1)) k l).Nonempty ↔
          (P ∩ dyadicSquare (Δ ^ (i + 1)) k l).Nonempty := by
        constructor
        · rintro ⟨x, hx1, hx2⟩; exact ⟨x, hx1.1, hx2⟩
        · rintro ⟨x, hxP, hxFine⟩; exact ⟨x, ⟨hxP, h_nest hxFine⟩, hxFine⟩
      rw [hQ_iff, hP_iff]
      exact (same_occupied_cells hn_pos hΔ_int h_i1_le_m hP_sub_Q hQ_thick k l).symm
    · have h_not_inter : ¬(dyadicSquare (Δ ^ (i + 1)) k l ∩ dyadicSquare (Δ ^ i) a b).Nonempty := h_inter
      have h_disj : Disjoint (dyadicSquare (Δ ^ (i + 1)) k l) (dyadicSquare (Δ ^ i) a b) := by
        rw [Set.disjoint_left]
        intro x hx1 hx2
        exact h_not_inter ⟨x, hx1, hx2⟩
      have hQ_empty : ((Q ∩ dyadicSquare (Δ ^ i) a b) ∩ dyadicSquare (Δ ^ (i + 1)) k l) = ∅ := by
        have h_sub : (Q ∩ dyadicSquare (Δ ^ i) a b) ∩ dyadicSquare (Δ ^ (i + 1)) k l ⊆
            dyadicSquare (Δ ^ i) a b ∩ dyadicSquare (Δ ^ (i + 1)) k l := by
          intro x hx; exact ⟨hx.1.2, hx.2⟩
        have h_empty : (dyadicSquare (Δ ^ i) a b ∩ dyadicSquare (Δ ^ (i + 1)) k l) = ∅ := by
          rw [Set.inter_comm]; exact h_disj.inter_eq
        have h : ((Q ∩ dyadicSquare (Δ ^ i) a b) ∩ dyadicSquare (Δ ^ (i + 1)) k l) ⊆ (∅ : Set EuclideanPlane) := by
          rw [h_empty] at h_sub
          exact h_sub
        exact Set.subset_empty_iff.mp h
      have hP_empty : ((P ∩ dyadicSquare (Δ ^ i) a b) ∩ dyadicSquare (Δ ^ (i + 1)) k l) = ∅ := by
        have h_sub : (P ∩ dyadicSquare (Δ ^ i) a b) ∩ dyadicSquare (Δ ^ (i + 1)) k l ⊆
            dyadicSquare (Δ ^ i) a b ∩ dyadicSquare (Δ ^ (i + 1)) k l := by
          intro x hx; exact ⟨hx.1.2, hx.2⟩
        have h_empty : (dyadicSquare (Δ ^ i) a b ∩ dyadicSquare (Δ ^ (i + 1)) k l) = ∅ := by
          rw [Set.inter_comm]; exact h_disj.inter_eq
        have h : ((P ∩ dyadicSquare (Δ ^ i) a b) ∩ dyadicSquare (Δ ^ (i + 1)) k l) ⊆ (∅ : Set EuclideanPlane) := by
          rw [h_empty] at h_sub
          exact h_sub
        exact Set.subset_empty_iff.mp h
      simp [hQ_empty, hP_empty]
  have h_same_count : dyadicSquareCount (Δ ^ (i + 1)) (Q ∩ dyadicSquare (Δ ^ i) a b) =
      dyadicSquareCount (Δ ^ (i + 1)) (P ∩ dyadicSquare (Δ ^ i) a b) := by
    dsimp only [dyadicSquareCount]
    rw [h_same_set]
  rw [h_same_count]
  exact hmain i hi a b h_iff_P

/-! # IsSetBetweenScales transfer with geometric inflation -/

/-- Universal geometric inflation constant (using 2δ diameter bound). -/
def thickeningGeomFactor (s : ℝ) : ℝ :=
  (2 * (2 + 1) + 4) ^ 2 * (1 + 2) ^ s

/-- Transfer IsSetBetweenScales from P to its Δ^m-square thickening Q.

    Coarse scale δ_c = Δ^b, fine scale δ_f = Δ^a, with b ≤ a ≤ m.
    Nesting uses b ≤ m. -/
lemma IsSetBetweenScales.thickening_transfer
    {P Q : Set EuclideanPlane} {δ_f δ_c s C : ℝ}
    {m a b : ℕ} {Δ : ℝ} {n_dyadic : ℕ}
    (h : IsSetBetweenScales P δ_f δ_c s C)
    (hP_sub_Q : P ⊆ Q)
    (hn_pos : 0 < n_dyadic)
    (hΔ_int : (1 : ℝ) = (n_dyadic : ℝ) * Δ)
    (hΔ_lt_one : Δ < 1)
    (hδ_f_eq : δ_f = Δ ^ a)
    (hδ_c_eq : δ_c = Δ ^ b)
    (hb_le_a : b ≤ a)
    (ha_le_m : a ≤ m)
    (hQ_thick : ∀ y ∈ Q, ∃ (S : Set EuclideanPlane),
      (∃ (k l : ℤ), S = dyadicSquare (Δ ^ m) k l) ∧
      y ∈ S ∧ (P ∩ S).Nonempty) :
    IsSetBetweenScales Q δ_f δ_c s (thickeningGeomFactor s * C) := by
  rcases h with ⟨hδ_f_pos, hδ_c_pos, hδ_f_le_c, hs, hC_pos, hmain⟩
  have hΔ_pos : 0 < Δ := by
    have h : (n_dyadic : ℝ) * Δ = 1 := Eq.symm hΔ_int
    have h' : 0 < (n_dyadic : ℝ) := by exact_mod_cast hn_pos
    nlinarith
  have hb_le_m : b ≤ m := le_trans hb_le_a ha_le_m
  have hC_geom_pos : 0 < thickeningGeomFactor s := by
    dsimp only [thickeningGeomFactor] <;> positivity
  have hC'_pos : 0 < thickeningGeomFactor s * C := mul_pos hC_geom_pos hC_pos
  refine' ⟨hδ_f_pos, hδ_c_pos, hδ_f_le_c, hs, hC'_pos, _⟩
  intro i j hnonempty
  let A := homothetyS δ_c i j '' (P ∩ dyadicSquare δ_c i j)
  let B := homothetyS δ_c i j '' (Q ∩ dyadicSquare δ_c i j)
  have hA_sub_B : A ⊆ B := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨y, ⟨hP_sub_Q hy.1, hy.2⟩, rfl⟩
  set R : ℝ := 2 * Δ ^ m / δ_c with hR_def
  have hR_nonneg : 0 ≤ R := by
    rw [hR_def] <;> have h1 : 0 < δ_c := hδ_c_pos <;> positivity
  set δ' : ℝ := δ_f / δ_c with hδ'_def
  have hδ'_pos : 0 < δ' := by rw [hδ'_def] <;> positivity
  have h_close : ∀ y ∈ B, ∃ (a' : EuclideanPlane), a' ∈ A ∧ dist y a' ≤ R := by
    intro y hy
    rcases hy with ⟨q, hq, rfl⟩
    rcases hQ_thick q hq.1 with ⟨S, ⟨k, l, hS_eq⟩, hq_in_S, ⟨p, hpP, hp_in_S⟩⟩
    have hS_sub : S ⊆ dyadicSquare δ_c i j := by
      rw [hS_eq, hδ_c_eq]
      have hqS' : q ∈ dyadicSquare (Δ ^ b) i j := by
        rw [←hδ_c_eq] <;> exact hq.2
      have h_inter' : (dyadicSquare (Δ ^ m) k l ∩ dyadicSquare (Δ ^ b) i j).Nonempty := by
        rw [hS_eq] at hq_in_S
        exact ⟨q, hq_in_S, hqS'⟩
      exact dyadicSquare_nested_pow hn_pos hΔ_int hb_le_m h_inter'
    have hp_in_coarse : p ∈ dyadicSquare δ_c i j := hS_sub hp_in_S
    have hdist : dist q p ≤ 2 * Δ ^ m := by
      rw [hS_eq] at hq_in_S hp_in_S
      exact dyadicSquare_diameter (pow_pos hΔ_pos m) hq_in_S hp_in_S
    have h9 : dist (homothetyS δ_c i j q) (homothetyS δ_c i j p) = (1 / δ_c) * dist q p := by
      have h10 : homothetyS δ_c i j q - homothetyS δ_c i j p = (1 / δ_c) • (q - p) := by
        ext z
        simp [homothetyS]
        <;> ring
      calc dist (homothetyS δ_c i j q) (homothetyS δ_c i j p)
        = ‖homothetyS δ_c i j q - homothetyS δ_c i j p‖ := by rw [dist_eq_norm]
      _ = ‖(1 / δ_c) • (q - p)‖ := by rw [h10]
      _ = ‖(1 / δ_c)‖ * ‖q - p‖ := by rw [norm_smul]
      _ = |1 / δ_c| * ‖q - p‖ := by
        have h12 : ‖(1 / δ_c)‖ = |1 / δ_c| := by exact Real.norm_eq_abs (1 / δ_c)
        rw [h12]
      _ = (1 / δ_c) * dist q p := by
        have hpos : 0 < 1 / δ_c := by positivity
        rw [abs_of_pos hpos, dist_eq_norm] <;> ring
    have h_p_img : homothetyS δ_c i j p ∈ A := ⟨p, ⟨hpP, hp_in_coarse⟩, rfl⟩
    exact ⟨homothetyS δ_c i j p, h_p_img, by
      rw [h9]
      have h10 : (1 / δ_c) * dist q p ≤ (1 / δ_c) * (2 * Δ ^ m) := by gcongr
      have h11 : (1 / δ_c) * (2 * Δ ^ m) = R := by
        rw [hR_def] <;> ring
      rw [h11] at h10
      exact h10⟩
  have h_P_nonempty : (P ∩ dyadicSquare δ_c i j).Nonempty := by
    have h_iff := same_occupied_cells hn_pos hΔ_int hb_le_m hP_sub_Q hQ_thick i j
    have h_q : (Q ∩ dyadicSquare (Δ ^ b) i j).Nonempty := by
      rw [hδ_c_eq] at hnonempty
      exact hnonempty
    have h_P : (P ∩ dyadicSquare (Δ ^ b) i j).Nonempty := h_iff.mpr h_q
    rw [hδ_c_eq]
    exact h_P
  have hA_sset : IsDeltaSSet δ' s C A := by
    simpa [δ', hδ'_def] using hmain i j h_P_nonempty
  have h_ratio_le : R / δ' ≤ 2 := by
    rw [hR_def, hδ'_def, hδ_f_eq, hδ_c_eq]
    have h1 : (2 * Δ ^ m / Δ ^ b) / (Δ ^ a / Δ ^ b) = 2 * Δ ^ m / Δ ^ a := by
      field_simp [pow_pos hΔ_pos a, pow_pos hΔ_pos b] <;> ring
    rw [h1]
    have h2 : Δ ^ m ≤ Δ ^ a := by
      have h3 : a ≤ m := ha_le_m
      exact (pow_le_pow_iff_right_of_lt_one₀ hΔ_pos hΔ_lt_one).mpr ha_le_m
    have h5 : 0 < Δ ^ a := pow_pos hΔ_pos a
    have h6 : Δ ^ m / Δ ^ a ≤ 1 := (div_le_one h5).mpr h2
    have h7 : 2 * (Δ ^ m / Δ ^ a) ≤ 2 := by linarith
    simpa [mul_div_assoc] using h7
  set M_actual : ℝ := (2 * (R + δ') / δ' + 4) ^ 2 * (1 + R / δ') ^ s with hM_actual_def
  have hM_actual_pos : 0 < M_actual := by rw [hM_actual_def] <;> positivity
  have h_actual : IsDeltaSSet δ' s (M_actual * C) B :=
    DirecretisedFurstenbergEstimate.A10.IsDeltaSSet.thickening_plane hA_sset hA_sub_B hR_nonneg h_close
  have hM_le : M_actual ≤ thickeningGeomFactor s := by
    rw [hM_actual_def, thickeningGeomFactor]
    have h1 : R / δ' ≤ 2 := h_ratio_le
    have h2 : 0 ≤ R / δ' := by positivity
    have h3 : (2 * (R + δ') / δ' + 4) ^ 2 ≤ (2 * (2 + 1) + 4) ^ 2 := by
      have h4 : 2 * (R + δ') / δ' + 4 = 2 * (R / δ') + 6 := by
        field_simp [hδ'_pos.ne'] <;> ring
      rw [h4]
      have h5 : 0 ≤ 2 * (R / δ') + 6 := by positivity
      have h6 : 2 * (R / δ') + 6 ≤ 2 * (2 + 1) + 4 := by linarith [h1]
      nlinarith
    have h7 : (1 + R / δ') ^ s ≤ (1 + 2) ^ s := by
      apply Real.rpow_le_rpow
      · linarith
      · linarith
      · exact hs
    gcongr
  have h7 : M_actual * C ≤ thickeningGeomFactor s * C :=
    mul_le_mul_of_nonneg_right hM_le hC_pos.le
  exact LemmaE.IsDeltaSSet.weaken_constant h_actual h7

/-! # IsRegularBetweenScales transfer with geometric inflation -/

/-- Transfer IsRegularBetweenScales from P to its Δ^m-square thickening Q. -/
lemma IsRegularBetweenScales.thickening_transfer
    {P Q : Set EuclideanPlane} {δ_f δ_c s C K : ℝ}
    {m a b : ℕ} {Δ : ℝ} {n_dyadic : ℕ}
    (h : IsRegularBetweenScales P δ_f δ_c s C K)
    (hP_sub_Q : P ⊆ Q)
    (hn_pos : 0 < n_dyadic)
    (hΔ_int : (1 : ℝ) = (n_dyadic : ℝ) * Δ)
    (hΔ_lt_one : Δ < 1)
    (hδ_f_eq : δ_f = Δ ^ a)
    (hδ_c_eq : δ_c = Δ ^ b)
    (hb_le_a : b ≤ a)
    (ha_le_m : a ≤ m)
    (hQ_thick : ∀ y ∈ Q, ∃ (S : Set EuclideanPlane),
      (∃ (k l : ℤ), S = dyadicSquare (Δ ^ m) k l) ∧
      y ∈ S ∧ (P ∩ S).Nonempty) :
    IsRegularBetweenScales Q δ_f δ_c s
      (thickeningGeomFactor s * C)
      ((2 * (2 + 1) + 4) ^ 2 * K) := by
  have h_set : IsSetBetweenScales P δ_f δ_c s C := h.1
  have hK_pos : 0 < K := h.2.1
  have hδ_f_pos : 0 < δ_f := h_set.1
  have hδ_c_pos : 0 < δ_c := h_set.2.1
  have hΔ_pos : 0 < Δ := by
    have h : (n_dyadic : ℝ) * Δ = 1 := Eq.symm hΔ_int
    have h' : 0 < (n_dyadic : ℝ) := by exact_mod_cast hn_pos
    nlinarith
  have hb_le_m : b ≤ m := le_trans hb_le_a ha_le_m
  have h_reg : ∀ (i j : ℤ), (P ∩ dyadicSquare δ_c i j).Nonempty →
      (Metric.externalCoveringNumber (Real.sqrt (δ_f / δ_c)).toNNReal
         (homothetyS δ_c i j '' (P ∩ dyadicSquare δ_c i j)) : ENNReal) ≤
      ENNReal.ofReal (K * Real.rpow (δ_f / δ_c) (-s / 2)) := h.2.2
  let K' := (2 * (2 + 1) + 4) ^ 2 * K
  have hK'_pos : 0 < K' := by dsimp only [K'] <;> positivity
  have h_set_Q : IsSetBetweenScales Q δ_f δ_c s (thickeningGeomFactor s * C) :=
    IsSetBetweenScales.thickening_transfer h_set hP_sub_Q hn_pos hΔ_int hΔ_lt_one
      hδ_f_eq hδ_c_eq hb_le_a ha_le_m hQ_thick
  refine' ⟨h_set_Q, hK'_pos, _⟩
  intro i j hnonempty
  let A := homothetyS δ_c i j '' (P ∩ dyadicSquare δ_c i j)
  let B := homothetyS δ_c i j '' (Q ∩ dyadicSquare δ_c i j)
  set r : ℝ := Real.sqrt (δ_f / δ_c) with hr_def
  set R : ℝ := 2 * Δ ^ m / δ_c with hR_def
  have hr_pos : 0 < r := by rw [hr_def] <;> positivity
  have hR_nonneg : 0 ≤ R := by rw [hR_def] <;> positivity
  have hA_sub_B : A ⊆ B := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨y, ⟨hP_sub_Q hy.1, hy.2⟩, rfl⟩
  have h_close : ∀ y ∈ B, ∃ (a' : EuclideanPlane), a' ∈ A ∧ dist y a' ≤ R := by
    intro y hy
    rcases hy with ⟨q, hq, rfl⟩
    rcases hQ_thick q hq.1 with ⟨S, ⟨k, l, hS_eq⟩, hq_in_S, ⟨p, hpP, hp_in_S⟩⟩
    have hS_sub : S ⊆ dyadicSquare δ_c i j := by
      rw [hS_eq, hδ_c_eq]
      have hqS' : q ∈ dyadicSquare (Δ ^ b) i j := by
        rw [←hδ_c_eq] <;> exact hq.2
      have h_inter' : (dyadicSquare (Δ ^ m) k l ∩ dyadicSquare (Δ ^ b) i j).Nonempty := by
        rw [hS_eq] at hq_in_S
        exact ⟨q, hq_in_S, hqS'⟩
      exact dyadicSquare_nested_pow hn_pos hΔ_int hb_le_m h_inter'
    have hp_in_coarse : p ∈ dyadicSquare δ_c i j := hS_sub hp_in_S
    have hdist : dist q p ≤ 2 * Δ ^ m := by
      rw [hS_eq] at hq_in_S hp_in_S
      exact dyadicSquare_diameter (pow_pos hΔ_pos m) hq_in_S hp_in_S
    have h9 : dist (homothetyS δ_c i j q) (homothetyS δ_c i j p) = (1 / δ_c) * dist q p := by
      have h10 : homothetyS δ_c i j q - homothetyS δ_c i j p = (1 / δ_c) • (q - p) := by
        ext z; simp [homothetyS] <;> ring
      calc dist (homothetyS δ_c i j q) (homothetyS δ_c i j p)
        = ‖homothetyS δ_c i j q - homothetyS δ_c i j p‖ := by rw [dist_eq_norm]
      _ = ‖(1 / δ_c) • (q - p)‖ := by rw [h10]
      _ = ‖(1 / δ_c)‖ * ‖q - p‖ := by rw [norm_smul]
      _ = |1 / δ_c| * ‖q - p‖ := by
        have h12 : ‖(1 / δ_c)‖ = |1 / δ_c| := by exact Real.norm_eq_abs (1 / δ_c)
        rw [h12]
      _ = (1 / δ_c) * dist q p := by
        have hpos : 0 < 1 / δ_c := by positivity
        rw [abs_of_pos hpos, dist_eq_norm] <;> ring
    have h_p_img : homothetyS δ_c i j p ∈ A := ⟨p, ⟨hpP, hp_in_coarse⟩, rfl⟩
    exact ⟨homothetyS δ_c i j p, h_p_img, by
      rw [h9]
      have h10 : (1 / δ_c) * dist q p ≤ (1 / δ_c) * (2 * Δ ^ m) := by gcongr
      have h11 : (1 / δ_c) * (2 * Δ ^ m) = R := by
        rw [hR_def] <;> ring
      rw [h11] at h10
      exact h10⟩
  have h_ratio_le : R / r ≤ 2 := by
    have h1 : R ≤ 2 * r := by
      rw [hR_def, hr_def]
      have h2 : 0 < δ_c := hδ_c_pos
      have h3 : 0 < δ_f := hδ_f_pos
      have h4 : (2 * Δ ^ m / δ_c) ^ 2 ≤ (2 * Real.sqrt (δ_f / δ_c)) ^ 2 := by
        have h5 : (2 * Δ ^ m / δ_c) ^ 2 = 4 * Δ ^ (2 * m) / δ_c ^ 2 := by
          field_simp [h2.ne'] <;> ring
        have h6 : (2 * Real.sqrt (δ_f / δ_c)) ^ 2 = 4 * (δ_f / δ_c) := by
          have h7 : 0 ≤ δ_f / δ_c := by positivity
          have h8 : (Real.sqrt (δ_f / δ_c)) ^ 2 = δ_f / δ_c := Real.sq_sqrt h7
          calc (2 * Real.sqrt (δ_f / δ_c)) ^ 2
            = 4 * (Real.sqrt (δ_f / δ_c)) ^ 2 := by ring
          _ = 4 * (δ_f / δ_c) := by rw [h8] <;> ring
        rw [h5, h6]
        have h8 : Δ ^ (2 * m) ≤ δ_c * δ_f := by
          rw [hδ_c_eq, hδ_f_eq, ←pow_add]
          have h9 : a + b ≤ 2 * m := by omega
          exact pow_le_pow_of_le_one (by linarith) hΔ_lt_one.le (show b + a ≤ 2 * m by omega)
        have h10 : 4 * Δ ^ (2 * m) / δ_c ^ 2 ≤ 4 * (δ_f / δ_c) := by
          calc 4 * Δ ^ (2 * m) / δ_c ^ 2
            ≤ 4 * (δ_c * δ_f) / δ_c ^ 2 := by gcongr
          _ = 4 * (δ_f / δ_c) := by field_simp [h2.ne'] <;> ring
        exact h10
      have h11 : 0 ≤ 2 * Δ ^ m / δ_c := by positivity
      have h12 : 0 ≤ 2 * Real.sqrt (δ_f / δ_c) := by positivity
      nlinarith
    calc R / r ≤ (2 * r) / r := by gcongr
      _ = 2 := by field_simp [hr_pos.ne'] <;> ring
  have h_cover_B : (Metric.externalCoveringNumber r.toNNReal B : ENNReal) ≤
      ENNReal.ofReal ((2 * (R + r) / r + 4) ^ 2) *
      (Metric.externalCoveringNumber r.toNNReal A : ENNReal) :=
    plane_thickening_cover hr_pos hR_nonneg h_close
  have hM_le : (2 * (R + r) / r + 4) ^ 2 ≤ (2 * (2 + 1) + 4) ^ 2 := by
    have h1 : R / r ≤ 2 := h_ratio_le
    have h2 : 2 * (R + r) / r + 4 = 2 * (R / r) + 6 := by
      field_simp [hr_pos.ne'] <;> ring
    rw [h2]
    have h3 : 0 ≤ 2 * (R / r) + 6 := by positivity
    have h4 : 2 * (R / r) + 6 ≤ 2 * (2 + 1) + 4 := by linarith [h1]
    nlinarith
  have h_P_nonempty : (P ∩ dyadicSquare δ_c i j).Nonempty := by
    have h_iff := same_occupied_cells hn_pos hΔ_int hb_le_m hP_sub_Q hQ_thick i j
    have h_q : (Q ∩ dyadicSquare (Δ ^ b) i j).Nonempty := by
      rw [hδ_c_eq] at hnonempty
      exact hnonempty
    have h_P : (P ∩ dyadicSquare (Δ ^ b) i j).Nonempty := h_iff.mpr h_q
    rw [hδ_c_eq]
    exact h_P
  have h_cover_A : (Metric.externalCoveringNumber r.toNNReal A : ENNReal) ≤
      ENNReal.ofReal (K * Real.rpow (δ_f / δ_c) (-s / 2)) := h_reg i j h_P_nonempty
  have h13 : ENNReal.ofReal ((2 * (R + r) / r + 4) ^ 2) ≤
      ENNReal.ofReal ((2 * (2 + 1) + 4) ^ 2) := ENNReal.ofReal_le_ofReal hM_le
  calc (Metric.externalCoveringNumber r.toNNReal B : ENNReal)
      ≤ ENNReal.ofReal ((2 * (R + r) / r + 4) ^ 2) *
          (Metric.externalCoveringNumber r.toNNReal A : ENNReal) := h_cover_B
    _ ≤ ENNReal.ofReal ((2 * (2 + 1) + 4) ^ 2) *
          (Metric.externalCoveringNumber r.toNNReal A : ENNReal) :=
      mul_le_mul_of_nonneg_right h13 (by positivity)
    _ ≤ ENNReal.ofReal ((2 * (2 + 1) + 4) ^ 2) *
          ENNReal.ofReal (K * Real.rpow (δ_f / δ_c) (-s / 2)) :=
      mul_le_mul_of_nonneg_left h_cover_A (by positivity)
    _ = ENNReal.ofReal (((2 * (2 + 1) + 4) ^ 2 * K) *
          Real.rpow (δ_f / δ_c) (-s / 2)) := by
      have h_pos : 0 < (2 * (2 + 1) + 4) ^ 2 := by norm_num
      have h_eq : ((2 * (2 + 1) + 4) ^ 2 * K) * Real.rpow (δ_f / δ_c) (-s / 2) =
          (2 * (2 + 1) + 4) ^ 2 * (K * Real.rpow (δ_f / δ_c) (-s / 2)) := by ring
      rw [h_eq, ←ENNReal.ofReal_mul (by positivity)]
      <;> rfl

end DirecretisedFurstenbergEstimate.MultiscaleDecomposition
