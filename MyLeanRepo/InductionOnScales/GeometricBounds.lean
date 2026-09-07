module

public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Geometric packing bounds for the polylogarithmic estimate

Provides two cardinality bounds derived from the geometry of
`NiceConfiguration`:

- `tube_count_bound`: the number of tubes incident with a fixed fine square
  is at most `12 / δ²`.
- `point_count_bound`: the number of fine points is at most `1 / δ²`.
-/

attribute [local instance] Classical.propDecidable

namespace InductionOnScales

section GeometricBounds

variable {n : ℕ} {s C₁ : ℝ} {M : ℕ}

/-- Any tube incident with a square contained in the unit square has its
intercept index `b` in a bounded range: `-(2^n + 1) ≤ b ≤ 2^(n+1) - 1`. -/
lemma intercept_index_bound {n : ℕ} (T : DyadicTube n) (p : DyadicSquare n)
    (h_inc : (T.toSet ∩ p.toSet).Nonempty)
    (h_bounded : p.toSet ⊆ unitSquare)
    (h_strip : T.IsInAllowedParameterStrip) :
    -(2 ^ n + 1 : ℤ) ≤ T.b ∧ T.b ≤ (2 ^ (n + 1) : ℤ) - 1 := by
  set δ := dyadicDelta n with hδ_def
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_inv : (1 : ℝ) / δ = (2 ^ n : ℝ) := by
    simp only [hδ_def, dyadicDelta_eq_inv] <;> field_simp
  rcases h_inc with ⟨point, hpoint_T, hpoint_p⟩
  let x := point.1
  let y := point.2
  have hx0 : 0 ≤ x := (h_bounded hpoint_p).1.1
  have hx1 : x < 1 := (h_bounded hpoint_p).1.2
  have hy0 : 0 ≤ y := (h_bounded hpoint_p).2.1
  have hy1 : y < 1 := (h_bounded hpoint_p).2.2
  rcases hpoint_T with ⟨slope, hslope_in, intercept, hintercept_in, h_eq⟩
  have hslope_ge : -1 ≤ slope := by
    have h1 : (T.a : ℝ) ≥ -((2 ^ n : ℕ) : ℝ) := by exact_mod_cast h_strip.1
    have h_pos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
    have h5 : δ = 1 / (2 ^ n : ℝ) := by
      rw [hδ_def]
      exact dyadicDelta_eq_inv n
    have h_cast : ((2 ^ n : ℕ) : ℝ) = (2 ^ n : ℝ) := by norm_cast
    have h4 : ((2 ^ n : ℕ) : ℝ) * δ = 1 := by
      rw [h5, h_cast]
      field_simp [h_pos.ne'] <;> ring
    have h2 : (T.a : ℝ) * δ ≥ -1 := by
      have h3 : (T.a : ℝ) * δ ≥ -((2 ^ n : ℕ) : ℝ) * δ := by gcongr
      linarith [h4]
    linarith [hslope_in.1]
  have hslope_lt : slope < 1 + δ := by
    have h1 : (T.a : ℝ) < ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast h_strip.2
    have h_pos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
    have h4 : δ = 1 / (2 ^ n : ℝ) := by
      rw [hδ_def]
      exact dyadicDelta_eq_inv n
    have h_cast : ((2 ^ n : ℕ) : ℝ) = (2 ^ n : ℝ) := by norm_cast
    have h3 : ((2 ^ n : ℕ) : ℝ) * δ = 1 := by
      rw [h4, h_cast]
      field_simp [h_pos.ne'] <;> ring
    have h2 : ((T.a + 1 : ℝ) * δ) < 1 + δ := by nlinarith
    linarith [hslope_in.2]
  have hc : intercept = y - slope * x := by linarith
  have hc_gt : -(1 + δ) < intercept := by
    rw [hc]
    by_cases h : 0 ≤ slope
    · have h3 : slope * x < 1 + δ := by
        have h4 : slope * x < (1 + δ) * 1 := by
          exact mul_lt_mul'' hslope_lt (by linarith) (by linarith) (by linarith)
        simpa using h4
      nlinarith
    · have h3 : slope * x ≤ 0 := by nlinarith
      nlinarith
  have hc_lt : intercept < 2 := by
    rw [hc]
    by_cases h : 0 ≤ slope
    · have h3 : slope * x ≥ 0 := by nlinarith
      nlinarith
    · have h3 : slope * x > -1 := by
        have h4 : slope * x > slope := by nlinarith
        linarith
      nlinarith
  have hTb1 : (T.b : ℝ) * δ ≤ intercept := hintercept_in.1
  have hTb2 : intercept < (T.b + 1 : ℝ) * δ := hintercept_in.2
  have hTb_upper : (T.b : ℝ) < (2 ^ (n + 1) : ℝ) := by
    have h5 : (T.b : ℝ) * δ < 2 := by linarith
    have h6 : (T.b : ℝ) < 2 / δ := by
      calc (T.b : ℝ)
        = ((T.b : ℝ) * δ) / δ := by field_simp [hδ_pos.ne'] <;> ring
      _ < 2 / δ := by gcongr
    have h7 : 2 / δ = (2 ^ (n + 1) : ℝ) := by
      have h8 : 2 / δ = 2 * (1 / δ) := by ring
      rw [h8, hδ_inv] <;> norm_cast <;> ring
    rw [h7] at h6
    exact h6
  have hTb_lower : (T.b : ℝ) > -((2 ^ n : ℝ) + 2) := by
    have h5 : (T.b + 1 : ℝ) * δ > -(1 + δ) := by linarith
    have h6 : (T.b : ℝ) * δ > -(1 + 2 * δ) := by linarith
    have h7 : (T.b : ℝ) > -(1 / δ + 2) := by
      calc (T.b : ℝ)
        = ((T.b : ℝ) * δ) / δ := by field_simp [hδ_pos.ne'] <;> ring
      _ > (-(1 + 2 * δ)) / δ := by gcongr
      _ = -(1 / δ + 2) := by field_simp [hδ_pos.ne'] <;> ring
    rw [hδ_inv] at h7
    simpa using h7
  have hTb_upper_int : T.b ≤ (2 ^ (n + 1) : ℤ) - 1 := by
    have h8 : (T.b : ℝ) < (2 ^ (n + 1) : ℝ) := hTb_upper
    have h9 : T.b < (2 ^ (n + 1) : ℤ) := by exact_mod_cast h8
    omega
  have hTb_lower_int : -(2 ^ n + 1 : ℤ) ≤ T.b := by
    have h9 : (T.b : ℝ) > -((2 ^ n : ℝ) + 2) := hTb_lower
    have h10 : T.b > -((2 ^ n : ℤ) + 2) := by exact_mod_cast h9
    omega
  exact ⟨hTb_lower_int, hTb_upper_int⟩

/-- Bound on the number of tubes in a family incident with a fixed fine square. -/
lemma tube_count_bound {n : ℕ} {s C₁ : ℝ} {M : ℕ}
    (config : NiceConfiguration n s C₁ M)
    (p : DyadicSquare n) (hp : p ∈ config.points) :
    (M : ℝ) ≤ 12 / (dyadicDelta n)^2 := by
  set δ := dyadicDelta n with hδ_def
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  let S := config.tubeFamily p hp
  have hS_card : S.card = M := config.h_size p hp
  let A := Finset.Ico (-(2 ^ n : ℤ)) (2 ^ n : ℤ)
  let B := Finset.Icc (-(2 ^ n + 1 : ℤ)) ((2 ^ (n + 1) : ℤ) - 1)
  have h_main : ∀ T ∈ S, T.a ∈ A ∧ T.b ∈ B := by
    intro T hT
    have hT_in_tubes : T ∈ config.tubes := config.h_subset p hp hT
    have h_strip : T.IsInAllowedParameterStrip := config.h_tube_parameters T hT_in_tubes
    have h_inc : (T.toSet ∩ p.toSet).Nonempty := config.h_incidence p hp T hT
    have h_bounded : p.toSet ⊆ unitSquare := config.h_bounded p hp
    have h_bounds := intercept_index_bound T p h_inc h_bounded h_strip
    have h_a1 : -(2 ^ n : ℤ) ≤ T.a := h_strip.1
    have h_a2 : T.a < (2 ^ n : ℤ) := h_strip.2
    exact ⟨Finset.mem_Ico.mpr ⟨h_a1, h_a2⟩,
      Finset.mem_Icc.mpr ⟨h_bounds.1, h_bounds.2⟩⟩
  let f : DyadicTube n → ℤ × ℤ := fun T => (T.a, T.b)
  have h_inj : Set.InjOn f S := by
    intro T1 _ T2 _ h
    have h1 : T1.a = T2.a := by simp [f] at h <;> tauto
    have h2 : T1.b = T2.b := by simp [f] at h <;> tauto
    cases T1 <;> cases T2 <;> simp_all
  have h_image_sub : S.image f ⊆ A ×ˢ B := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨T, hT, rfl⟩
    have h1 := h_main T hT
    exact Finset.mem_product.mpr ⟨h1.1, h1.2⟩
  have h_card_le : S.card ≤ (A ×ˢ B).card := by
    calc S.card
      = (S.image f).card := by rw [Finset.card_image_of_injOn h_inj]
    _ ≤ (A ×ˢ B).card := Finset.card_le_card h_image_sub
  have hA_card : A.card = 2 ^ (n + 1) := by
    have h_le : (-(2 ^ n : ℤ)) ≤ (2 ^ n : ℤ) := by
      have h_nonneg : 0 ≤ (2 ^ n : ℤ) := by positivity
      linarith
    have h1_int : (A.card : ℤ) = (2 ^ n : ℤ) - (-(2 ^ n : ℤ)) := Int.card_Ico_of_le _ _ h_le
    have h1 : (A.card : ℝ) = (2 ^ n : ℝ) - (-(2 ^ n : ℝ)) := by exact_mod_cast h1_int
    have h2 : (A.card : ℝ) = (2 ^ (n + 1) : ℝ) := by
      rw [h1]
      have h3 : (2 ^ n : ℝ) - (-(2 ^ n : ℝ)) = 2 * (2 ^ n : ℝ) := by ring
      rw [h3]
      have h4 : 2 * (2 ^ n : ℝ) = (2 ^ (n + 1) : ℝ) := by
        norm_cast <;> ring
      exact h4
    exact_mod_cast h2
  have hB_card : B.card = 3 * 2 ^ n + 1 := by
    have h_le : (-(2 ^ n + 1 : ℤ)) ≤ (2 ^ (n + 1) : ℤ) := by
      have h_nonneg : 0 ≤ (2 ^ n : ℤ) := by positivity
      have h_eq : (2 ^ (n + 1) : ℤ) = 2 * (2 ^ n : ℤ) := by
        simp [pow_succ] <;> ring
      rw [h_eq]
      linarith
    have h_le' : (-(2 ^ n + 1 : ℤ)) ≤ ((2 ^ (n + 1) : ℤ) - 1) + 1 := by
      have h_simp : ((2 ^ (n + 1) : ℤ) - 1) + 1 = (2 ^ (n + 1) : ℤ) := by omega
      rw [h_simp]
      exact h_le
    have h1_int : (B.card : ℤ) = (((2 ^ (n + 1) : ℤ) - 1) + 1 - (-(2 ^ n + 1 : ℤ))) :=
      Int.card_Icc_of_le _ _ h_le'
    have h1 : (B.card : ℝ) = (((2 ^ (n + 1) : ℝ) - 1) + 1 - (-(2 ^ n + 1 : ℝ))) := by exact_mod_cast h1_int
    have h2 : (B.card : ℝ) = (3 * 2 ^ n + 1 : ℝ) := by
      rw [h1]
      have h3 : ((2 ^ (n + 1) : ℝ) - 1) + 1 - (-(2 ^ n + 1 : ℝ)) = (2 ^ (n + 1) : ℝ) + (2 ^ n : ℝ) + 1 := by ring
      rw [h3]
      have h4 : (2 ^ (n + 1) : ℝ) = 2 * (2 ^ n : ℝ) := by norm_cast <;> ring
      rw [h4] <;> ring
    exact_mod_cast h2
  have hAB_card : (A ×ˢ B).card = A.card * B.card := Finset.card_product _ _
  rw [hAB_card, hA_card, hB_card] at h_card_le
  have h9 : 2 ^ (n + 1) * (3 * 2 ^ n + 1) ≤ 12 * 4 ^ n := by
    have h10 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    rw [h10]
    have h11 : 2 * 2 ^ n * (3 * 2 ^ n + 1) ≤ 12 * (2 ^ n) ^ 2 := by
      nlinarith [pow_nonneg (show (0 : ℕ) ≤ 2 by norm_num) n]
    have h12 : (2 ^ n) ^ 2 = 4 ^ n := by
      have h13 : (2 ^ n) ^ 2 = 2 ^ (n * 2) := by
        rw [pow_mul] <;> ring
      have h14 : 4 ^ n = 2 ^ (2 * n) := by
        have h15 : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [h15, pow_mul] <;> ring
      rw [h13, h14] <;> ring_nf
    rw [h12] at h11
    exact h11
  have h10 : S.card ≤ 12 * 4 ^ n := h_card_le.trans h9
  have h11 : (S.card : ℝ) ≤ 12 * (4 ^ n : ℝ) := by exact_mod_cast h10
  have h12 : (4 ^ n : ℝ) = 1 / δ^2 := by
    have h13 : δ = 1 / (2 ^ n : ℝ) := by
      simp only [hδ_def, dyadicDelta_eq_inv]
    have h14 : (4 ^ n : ℝ) = (2 ^ n : ℝ)^2 := by
      have h15 : (4 ^ n : ℕ) = (2 ^ n)^2 := by
        have h16 : (2 ^ n) ^ 2 = 4 ^ n := by
          have h17 : (2 ^ n) ^ 2 = 2 ^ (n * 2) := by rw [pow_mul] <;> ring
          have h18 : 4 ^ n = 2 ^ (2 * n) := by
            have h19 : (4 : ℕ) = 2 ^ 2 := by norm_num
            rw [h19, pow_mul] <;> ring
          rw [h17, h18] <;> ring_nf
        exact h16.symm
      exact_mod_cast h15
    rw [h14, h13]
    field_simp <;> ring
  have h14 : (M : ℝ) = (S.card : ℝ) := by
    rw [hS_card] <;> norm_cast
  have h15 : (S.card : ℝ) ≤ 12 / δ^2 := by
    have h16 : (S.card : ℝ) ≤ 12 * (4 ^ n : ℝ) := h11
    rw [h12] at h16
    have h17 : 12 * (1 / δ^2) = 12 / δ^2 := by ring
    rw [h17] at h16
    exact h16
  rw [h14]
  exact h15

/-- A fine square contained in the unit square has indices in `[0, 2^n)`. -/
lemma square_index_bounds {n : ℕ} (p : DyadicSquare n)
    (h_bounded : p.toSet ⊆ unitSquare) :
    0 ≤ p.i ∧ p.i < (2 ^ n : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ n : ℤ) := by
  set δ := dyadicDelta n with hδ_def
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_inv : (1 : ℝ) / δ = (2 ^ n : ℝ) := by
    simp only [hδ_def, dyadicDelta_eq_inv] <;> field_simp
  let pt_ll : InductionPlane := ((p.i : ℝ) * δ, (p.j : ℝ) * δ)
  have hpt_ll_in : pt_ll ∈ p.toSet := by
    simp only [pt_ll, DyadicSquare.toSet, Set.mem_prod, Set.mem_Ico]
    <;> constructor <;> constructor <;> linarith [hδ_pos]
  have h_ll_in_unit : pt_ll ∈ unitSquare := h_bounded hpt_ll_in
  have hpi0 : 0 ≤ p.i := by
    have h : 0 ≤ (p.i : ℝ) * δ := h_ll_in_unit.1.1
    have h' : 0 ≤ (p.i : ℝ) := by nlinarith [hδ_pos]
    exact_mod_cast h'
  have hpj0 : 0 ≤ p.j := by
    have h : 0 ≤ (p.j : ℝ) * δ := h_ll_in_unit.2.1
    have h' : 0 ≤ (p.j : ℝ) := by nlinarith [hδ_pos]
    exact_mod_cast h'
  let pt_mid : InductionPlane := ((p.i + 1 / 2 : ℝ) * δ, (p.j : ℝ) * δ)
  have hpt_mid_in : pt_mid ∈ p.toSet := by
    simp only [pt_mid, DyadicSquare.toSet, Set.mem_prod, Set.mem_Ico]
    <;> constructor <;> constructor <;> linarith [hδ_pos]
  have h_mid_in_unit : pt_mid ∈ unitSquare := h_bounded hpt_mid_in
  have h_i_lt : (p.i + 1 / 2 : ℝ) * δ < 1 := h_mid_in_unit.1.2
  have hpi_upper : p.i < (2 ^ n : ℤ) := by
    have h : (p.i : ℝ) + 1 / 2 < 1 / δ := by
      calc (p.i + 1 / 2 : ℝ)
        = ((p.i + 1 / 2 : ℝ) * δ) / δ := by field_simp [hδ_pos.ne'] <;> ring
      _ < 1 / δ := by gcongr
    rw [hδ_inv] at h
    have h' : (p.i : ℝ) < (2 ^ n : ℝ) := by linarith
    exact_mod_cast h'
  let pt_mid2 : InductionPlane := ((p.i : ℝ) * δ, (p.j + 1 / 2 : ℝ) * δ)
  have hpt_mid2_in : pt_mid2 ∈ p.toSet := by
    simp only [pt_mid2, DyadicSquare.toSet, Set.mem_prod, Set.mem_Ico]
    <;> constructor <;> constructor <;> linarith [hδ_pos]
  have h_mid2_in_unit : pt_mid2 ∈ unitSquare := h_bounded hpt_mid2_in
  have h_j_lt : (p.j + 1 / 2 : ℝ) * δ < 1 := h_mid2_in_unit.2.2
  have hpj_upper : p.j < (2 ^ n : ℤ) := by
    have h : (p.j : ℝ) + 1 / 2 < 1 / δ := by
      calc (p.j + 1 / 2 : ℝ)
        = ((p.j + 1 / 2 : ℝ) * δ) / δ := by field_simp [hδ_pos.ne'] <;> ring
      _ < 1 / δ := by gcongr
    rw [hδ_inv] at h
    have h' : (p.j : ℝ) < (2 ^ n : ℝ) := by linarith
    exact_mod_cast h'
  exact ⟨hpi0, hpi_upper, hpj0, hpj_upper⟩

/-- Bound on the number of fine points: at most `1 / δ² = 4^n`. -/
lemma point_count_bound {n : ℕ} {s C₁ : ℝ} {M : ℕ}
    (config : NiceConfiguration n s C₁ M) :
    (config.points.card : ℝ) ≤ 1 / (dyadicDelta n)^2 := by
  set δ := dyadicDelta n with hδ_def
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  let f : DyadicSquare n → ℤ × ℤ := fun p => (p.i, p.j)
  have h_inj : Set.InjOn f config.points := by
    intro p1 _ p2 _ h
    have h1 : p1.i = p2.i := by simp [f] at h <;> tauto
    have h2 : p1.j = p2.j := by simp [f] at h <;> tauto
    cases p1 <;> cases p2 <;> simp_all
  let A := Finset.Ico (0 : ℤ) (2 ^ n : ℤ)
  have h_main : ∀ p ∈ config.points, f p ∈ A ×ˢ A := by
    intro p hp
    have h_bounded : p.toSet ⊆ unitSquare := config.h_bounded p hp
    have h_bounds := square_index_bounds p h_bounded
    have hi : p.i ∈ A := Finset.mem_Ico.mpr ⟨h_bounds.1, h_bounds.2.1⟩
    have hj : p.j ∈ A := Finset.mem_Ico.mpr ⟨h_bounds.2.2.1, h_bounds.2.2.2⟩
    exact Finset.mem_product.mpr ⟨hi, hj⟩
  have h_image_sub : config.points.image f ⊆ A ×ˢ A := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
    exact h_main p hp
  have h_card_le : config.points.card ≤ (A ×ˢ A).card := by
    calc config.points.card
      = (config.points.image f).card := by rw [Finset.card_image_of_injOn h_inj]
    _ ≤ (A ×ˢ A).card := Finset.card_le_card h_image_sub
  have hA_card : A.card = 2 ^ n := by
    have h_le : (0 : ℤ) ≤ (2 ^ n : ℤ) := by positivity
    have h1_int : (A.card : ℤ) = (2 ^ n : ℤ) - 0 := Int.card_Ico_of_le _ _ h_le
    have h1 : (A.card : ℝ) = (2 ^ n : ℝ) - 0 := by exact_mod_cast h1_int
    have h2 : (A.card : ℝ) = (2 ^ n : ℝ) := by
      rw [h1] <;> ring
    exact_mod_cast h2
  have hAB_card : (A ×ˢ A).card = (2 ^ n) ^ 2 := by
    rw [Finset.card_product, hA_card] <;> ring
  rw [hAB_card] at h_card_le
  have h10 : config.points.card ≤ 4 ^ n := by
    have h11 : (2 ^ n) ^ 2 = 4 ^ n := by
      have h12 : (2 ^ n) ^ 2 = 2 ^ (n * 2) := by rw [pow_mul] <;> ring
      have h13 : 4 ^ n = 2 ^ (2 * n) := by
        have h14 : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [h14, pow_mul] <;> ring
      rw [h12, h13] <;> ring_nf
    rw [h11] at h_card_le
    exact h_card_le
  have h12 : (config.points.card : ℝ) ≤ (4 ^ n : ℝ) := by exact_mod_cast h10
  have h13 : (4 ^ n : ℝ) = 1 / δ^2 := by
    have h14 : δ = 1 / (2 ^ n : ℝ) := by
      simp only [hδ_def, dyadicDelta_eq_inv]
    have h15 : (4 ^ n : ℝ) = (2 ^ n : ℝ)^2 := by
      have h16 : (4 ^ n : ℕ) = (2 ^ n)^2 := by
        have h17 : (2 ^ n) ^ 2 = 4 ^ n := by
          have h18 : (2 ^ n) ^ 2 = 2 ^ (n * 2) := by rw [pow_mul] <;> ring
          have h19 : 4 ^ n = 2 ^ (2 * n) := by
            have h20 : (4 : ℕ) = 2 ^ 2 := by norm_num
            rw [h20, pow_mul] <;> ring
          rw [h18, h19] <;> ring_nf
        exact h17.symm
      exact_mod_cast h16
    rw [h15, h14] <;> field_simp <;> ring
  rw [h13] at h12
  exact h12

end GeometricBounds

end InductionOnScales
