module

/-
  DyadicTube capacity pruning theorem.

  Fässler-Orponen route:
  1. Maximum-cardinality capacity-respecting subset S (powerset max)
  2. Maximality → saturated ancestor for every deleted leaf
  3. Half-capacity cover of ALL original leaves
  4. S-set cover-sum cancellation → c * C^{-1} * δ_n^{-s} survivor lower
  5. Capacity bounds → absolute local growth
  6. Divide by global survivor lower → relative S-set inheritance

  Output (explicit constants):
    - card(S) ≥ (1 / (C * 2^{s+1})) * δ_n^{-s}
    - card(S) ≤ 28 * δ_n^{-s}
    - IsDeltaSSet δ_n s (125 * 2^{s+1} * C) S

  Whiteprint node: dyadic_tube_pruning
  Dependencies: Base, DyadicTubes, CardinalityLowerBound
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.CardinalityLowerBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Bridge_SSetTransfer
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.FrontEndLemmas

open DiscretisedFurstenbergEstimate

/-! ### Infrastructure -/

/-- Ancestor of a level-n dyadic tube at level j ≤ n. -/
def dyadicTubeAncestor {n : ℕ} (j : ℕ) (h : j ≤ n) (T : DyadicTube n) :
    DyadicTube j :=
  let shift : ℤ := 2 ^ (n - j)
  ⟨T.a / shift, T.b / shift⟩

/-- Tubes in S that are descendants of ancestor A at level j. -/
def tubesInCube {n j : ℕ} (h : j ≤ n)
    (A : DyadicTube j) (S : Finset (DyadicTube n)) :
    Finset (DyadicTube n) :=
  S.filter (fun T => dyadicTubeAncestor j h T = A)

/-- Capacity of a level-j tube cube at base scale n: (δ_j / δ_n)^s. -/
def dyadicTubeCap (n j : ℕ) (s : ℝ) : ℝ :=
  (dyadicDelta j / dyadicDelta n) ^ s

lemma dyadicTubeCap_leaf {n : ℕ} {s : ℝ} : dyadicTubeCap n n s = 1 := by
  have hpos : 0 < dyadicDelta n := dyadicDelta_pos n
  have h1 : dyadicDelta n / dyadicDelta n = 1 := div_self hpos.ne'
  rw [dyadicTubeCap, h1]
  simp

lemma dyadicTubeCap_one_le {n j : ℕ} {s : ℝ} (hs_pos : 0 < s) (h : j ≤ n) :
    1 ≤ dyadicTubeCap n j s := by
  have h2 : dyadicDelta j ≥ dyadicDelta n := by
    have h1 : j ≤ n := h
    have h21 : (2 : ℝ)^j ≤ (2 : ℝ)^n := by gcongr <;> norm_num
    have h5 : 1 / (2 : ℝ)^j ≥ 1 / (2 : ℝ)^n :=
      one_div_le_one_div_of_le (by positivity) h21
    simpa [dyadicDelta] using h5
  have h3 : 0 < dyadicDelta n := dyadicDelta_pos n
  have h4 : dyadicDelta j / dyadicDelta n ≥ 1 := by
    calc dyadicDelta j / dyadicDelta n
      ≥ dyadicDelta n / dyadicDelta n := by gcongr
    _ = 1 := div_self h3.ne'
  have h5 : 0 ≤ s := by linarith
  exact Real.one_le_rpow h4 h5

/-- floor(x) ≥ x/2 for x ≥ 1. -/
lemma floor_ge_half (x : ℝ) (hx : 1 ≤ x) : x / 2 ≤ ↑(Nat.floor x) := by
  have h1 : 0 ≤ x := by linarith
  have h2 : x < (Nat.floor x : ℝ) + 1 := Nat.lt_floor_add_one x
  by_cases h : (Nat.floor x : ℝ) ≥ 1
  · by_cases h3 : x < 2
    · linarith
    · have h4 : x ≥ 2 := by linarith
      linarith
  · have h5 : (Nat.floor x : ℝ) < 1 := by linarith
    have h6 : Nat.floor x = 0 := by
      by_contra h7
      have h8 : Nat.floor x ≥ 1 := by omega
      have h9 : (Nat.floor x : ℝ) ≥ 1 := by exact_mod_cast h8
      linarith
    have h7 : x < 1 := by
      rw [h6] at h2
      norm_num at h2
      exact h2
    linarith [hx]

/-- The four children of a level-j dyadic tube. -/
def dyadicTubeChildren {j : ℕ} (T : DyadicTube j) :
    Finset (DyadicTube (j + 1)) :=
  {⟨2 * T.a, 2 * T.b⟩, ⟨2 * T.a + 1, 2 * T.b⟩,
   ⟨2 * T.a, 2 * T.b + 1⟩, ⟨2 * T.a + 1, 2 * T.b + 1⟩}

/-- Helper: integer division by 2^(k-1) gives either 2*(x/2^k) or 2*(x/2^k)+1. -/
lemma int_div_two_pow_sub (x : ℤ) (k : ℕ) (hk : 0 < k) :
    x / 2^(k - 1) = 2 * (x / 2^k) ∨ x / 2^(k - 1) = 2 * (x / 2^k) + 1 := by
  set q := x / 2^k with hq
  set r := x % 2^k with hr
  have h1 : x = q * 2^k + r := by exact Eq.symm (Int.ediv_mul_add_emod x (2 ^ k))
  have h2 : 0 ≤ r := Int.emod_nonneg _ (by positivity)
  have h3 : r < 2^k := Int.emod_lt_of_pos _ (by positivity)
  have h4 : (2^k : ℤ) = 2 * (2^(k - 1) : ℤ) := by
    cases k with | zero => omega | succ k' => simp [pow_succ] <;> ring
  have h_pos : 0 < (2^(k - 1) : ℤ) := by positivity
  have h5 : x = (2 * q) * (2^(k - 1) : ℤ) + r := by
    have h51 : q * (2^k : ℤ) = q * (2 * (2^(k - 1) : ℤ)) := by
      congr 1 <;> exact h4
    rw [h1, h51] <;> ring
  have h6 : x / (2^(k - 1) : ℤ) = 2 * q + r / (2^(k - 1) : ℤ) := by
    have h5' : x = r + (2^(k - 1) : ℤ) * (2 * q) := by linarith
    rw [h5']
    have h7 : (r + (2^(k - 1) : ℤ) * (2 * q)) / (2^(k - 1) : ℤ) =
        r / (2^(k - 1) : ℤ) + 2 * q := by
      rw [Int.add_mul_ediv_left] <;> positivity
    rw [h7] <;> ring
  have h9 : r / 2^(k - 1) = 0 ∨ r / 2^(k - 1) = 1 := by
    have h10 : 0 ≤ r / 2^(k - 1) := by apply Int.ediv_nonneg <;> linarith
    have h11 : r / 2^(k - 1) < 2 := by
      apply Int.ediv_lt_of_lt_mul
      · positivity
      · calc r < 2^k := h3
             _ = 2 * 2^(k - 1) := by
               cases k with | zero => contradiction | succ k' => simp [pow_succ] <;> ring
    omega
  rw [h6]
  rcases h9 with (h9 | h9)
  · rw [h9] <;> exact Or.inl (by ring)
  · rw [h9] <;> exact Or.inr (by ring)

/-- The level-(j+1) ancestor is a child of the level-j ancestor. -/
lemma ancestor_child_nat {n : ℕ} {j : ℕ} (hjn : j < n)
    (t : DyadicTube n) :
    dyadicTubeAncestor (j + 1) (by omega) t ∈
      dyadicTubeChildren (dyadicTubeAncestor j (by linarith) t) := by
  have hk : 0 < n - j := by omega
  have ha := int_div_two_pow_sub t.a (n - j) hk
  have hb := int_div_two_pow_sub t.b (n - j) hk
  dsimp only [dyadicTubeAncestor, dyadicTubeChildren]
  rcases ha with (ha | ha) <;> rcases hb with (hb | hb) <;>
    (simp [ha, hb] <;> tauto)

/-! ### Capacity respecting and maximal subset -/

def TubeCapacityRespecting {n : ℕ} {s : ℝ}
    (S : Finset (DyadicTube n)) : Prop :=
  ∀ (j : ℕ) (hj : j ≤ n) (A : DyadicTube j),
    (tubesInCube hj A S).card ≤ Nat.floor (dyadicTubeCap n j s)

/-- Existence of maximum-cardinality capacity-respecting subset. -/
lemma exists_maximal_tube_capacity_respecting {n : ℕ} {s : ℝ}
    (rawTubes : Finset (DyadicTube n))
    (hs_pos : 0 < s) :
    ∃ (S : Finset (DyadicTube n)),
      S ⊆ rawTubes ∧
      TubeCapacityRespecting (s := s) S ∧
      ∀ (t : DyadicTube n), t ∈ rawTubes → t ∉ S →
        ∃ (j : ℕ) (hj : j ≤ n) (A : DyadicTube j),
          dyadicTubeAncestor j hj t = A ∧
          (tubesInCube hj A S).card = Nat.floor (dyadicTubeCap n j s) := by
  let allCandidates := (Finset.powerset rawTubes).filter (TubeCapacityRespecting (s := s))
  have h_empty : (∅ : Finset (DyadicTube n)) ∈ allCandidates := by
    simp [allCandidates, TubeCapacityRespecting, tubesInCube] <;> omega
  have h_nonempty : allCandidates.Nonempty := ⟨∅, h_empty⟩
  rcases Finset.exists_max_image allCandidates (fun S => S.card) h_nonempty with
    ⟨S, hS_in, hS_max⟩
  have hS_sub : S ⊆ rawTubes := by
    have h1 : S ∈ Finset.powerset rawTubes := (Finset.mem_filter.mp hS_in).1
    exact Finset.mem_powerset.mp h1
  have hS_cap : TubeCapacityRespecting (s := s) S :=
    (Finset.mem_filter.mp hS_in).2
  refine' ⟨S, hS_sub, hS_cap, _⟩
  intro t ht hnt
  let S' := insert t S
  have hS'_sub : S' ⊆ rawTubes := by
    intro x hx
    simp only [S', Finset.mem_insert] at hx
    rcases hx with (rfl | hx)
    · exact ht
    · exact hS_sub hx
  have hS'_card : S'.card > S.card := by
    have h_card : S'.card = S.card + 1 := by
      rw [show S' = insert t S from rfl]
      simp [hnt] <;> omega
    linarith
  have hS'_not_cand : ¬ TubeCapacityRespecting (s := s) S' := by
    intro h
    have h2 : S' ∈ allCandidates := by
      rw [Finset.mem_filter] <;> exact ⟨Finset.mem_powerset.mpr hS'_sub, h⟩
    have h3 := hS_max S' h2
    omega
  have h_viol : ∃ (j : ℕ) (hj : j ≤ n) (A : DyadicTube j),
      (tubesInCube hj A S').card > Nat.floor (dyadicTubeCap n j s) := by
    simpa [TubeCapacityRespecting] using hS'_not_cand
  rcases h_viol with ⟨j, hj, A, hQ⟩
  have ht_in : t ∈ tubesInCube hj A S' := by
    by_contra h
    have h_cont : tubesInCube hj A S' = tubesInCube hj A S := by
      ext x
      simp only [tubesInCube, Finset.mem_filter, S', Finset.mem_insert]
      constructor
      · rintro ⟨hx1, hx2⟩
        have hx3 : x ∈ S := by
          rcases hx1 with (rfl | hx3)
          · have h_contra : x ∈ tubesInCube hj A S' := by
              simp only [tubesInCube, Finset.mem_filter]
              exact ⟨by simp [S'], hx2⟩
            exact False.elim (h h_contra)
          · exact hx3
        exact ⟨hx3, hx2⟩
      · rintro ⟨hx1, hx2⟩
        exact ⟨Or.inr hx1, hx2⟩
    rw [h_cont] at hQ
    have h9 : (tubesInCube hj A S).card ≤ Nat.floor (dyadicTubeCap n j s) := hS_cap j hj A
    linarith
  have h12 : dyadicTubeAncestor j hj t = A := (Finset.mem_filter.mp ht_in).2
  have h5 : tubesInCube hj A S' = insert t (tubesInCube hj A S) := by
    ext x
    simp only [tubesInCube, Finset.mem_filter, S', Finset.mem_insert]
    constructor
    · rintro ⟨hx1, hx2⟩
      rcases hx1 with (rfl | hx3)
      · exact Or.inl rfl
      · exact Or.inr ⟨hx3, hx2⟩
    · rintro (rfl | ⟨hx3, hx2⟩)
      · exact ⟨Or.inl rfl, h12⟩
      · exact ⟨Or.inr hx3, hx2⟩
  rw [h5] at hQ
  by_cases h6 : t ∈ tubesInCube hj A S
  · have h7 : t ∈ S := (Finset.mem_filter.mp h6).1
    exact False.elim (hnt h7)
  · have h_card2 : (insert t (tubesInCube hj A S)).card =
        (tubesInCube hj A S).card + 1 := by
      simp [h6] <;> omega
    rw [h_card2] at hQ
    have h8 : (tubesInCube hj A S).card ≥ Nat.floor (dyadicTubeCap n j s) := by omega
    have h9 : (tubesInCube hj A S).card ≤ Nat.floor (dyadicTubeCap n j s) := hS_cap j hj A
    have h10 : (tubesInCube hj A S).card = Nat.floor (dyadicTubeCap n j s) := by omega
    exact ⟨j, hj, A, h12, h10⟩

/-! ### Root tube cubes -/

/-- Level-0 tube cubes covering bounded parameters. -/
def rootTubeCubes : Finset (DyadicTube 0) :=
  (Finset.Icc (-2 : ℤ) 1).biUnion fun a =>
    (Finset.Icc (-3 : ℤ) 3).image fun b => ⟨a, b⟩

lemma rootTubeCubes_card : rootTubeCubes.card = 28 := by
  have h : rootTubeCubes = (Finset.Icc (-2 : ℤ) 1).biUnion fun a =>
      (Finset.Icc (-3 : ℤ) 3).image fun b => (⟨a, b⟩ : DyadicTube 0) := by rfl
  rw [h]
  have h_disj : ∀ (a1 : ℤ), a1 ∈ Finset.Icc (-2 : ℤ) 1 → ∀ (a2 : ℤ), a2 ∈ Finset.Icc (-2 : ℤ) 1 → a1 ≠ a2 →
      Disjoint ((Finset.Icc (-3 : ℤ) 3).image fun b : ℤ => (⟨a1, b⟩ : DyadicTube 0))
               ((Finset.Icc (-3 : ℤ) 3).image fun b : ℤ => (⟨a2, b⟩ : DyadicTube 0)) := by
    intro a1 _ a2 _ hne
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨b1, _, rfl⟩
    rcases Finset.mem_image.mp hx2 with ⟨b2, _, h_eq⟩
    injection h_eq with h_a
    exact hne h_a.symm
  rw [Finset.card_biUnion h_disj]
  have h_sum : ∑ a ∈ Finset.Icc (-2 : ℤ) 1, ((Finset.Icc (-3 : ℤ) 3).image fun b : ℤ => (⟨a, b⟩ : DyadicTube 0)).card =
      ∑ a ∈ Finset.Icc (-2 : ℤ) 1, (Finset.Icc (-3 : ℤ) 3).card := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.card_image_of_injective]
    <;> intro b1 b2 h <;> injection h <;> omega
  rw [h_sum]
  have h1 : (Finset.Icc (-3 : ℤ) 3).card = 7 := by decide
  have h2 : (Finset.Icc (-2 : ℤ) 1).card = 4 := by decide
  have h3 : ∑ a ∈ Finset.Icc (-2 : ℤ) 1, (Finset.Icc (-3 : ℤ) 3).card =
      (Finset.Icc (-2 : ℤ) 1).card * (Finset.Icc (-3 : ℤ) 3).card := by
    rw [Finset.sum_const] <;> ring
  rw [h3, h2, h1] <;> norm_num

/-- Every tube with bounded parameters has a level-0 ancestor in rootTubeCubes. -/
lemma rootTubeCubes_cover {n : ℕ} (T : DyadicTube n)
    (h_slope : |T.slope| ≤ 3 / 2) (h_intercept : |T.intercept| ≤ 3) :
    dyadicTubeAncestor 0 (by linarith) T ∈ rootTubeCubes := by
  have h_slope_def : T.slope = (T.a : ℝ) * dyadicDelta n := by rfl
  have h_int_def : T.intercept = (T.b : ℝ) * dyadicDelta n := by rfl
  have ha_real1 : -3 / 2 ≤ (T.a : ℝ) / (2 : ℝ)^n := by
    have h1 : -3 / 2 ≤ T.slope := by
      have h2 : -(3 / 2 : ℝ) ≤ T.slope := (abs_le.mp h_slope).1
      linarith
    rw [h_slope_def] at h1
    have h2 : (T.a : ℝ) * dyadicDelta n = (T.a : ℝ) / (2 : ℝ)^n := by
      simp [dyadicDelta] <;> field_simp <;> ring
    rw [h2] at h1
    exact h1
  have ha_real2 : (T.a : ℝ) / (2 : ℝ)^n ≤ 3 / 2 := by
    have h1 : T.slope ≤ 3 / 2 := (abs_le.mp h_slope).2
    rw [h_slope_def] at h1
    have h2 : (T.a : ℝ) * dyadicDelta n = (T.a : ℝ) / (2 : ℝ)^n := by
      simp [dyadicDelta] <;> field_simp <;> ring
    rw [h2] at h1
    exact h1
  have hb_real1 : -3 ≤ (T.b : ℝ) / (2 : ℝ)^n := by
    have h1 : -3 ≤ T.intercept := (abs_le.mp h_intercept).1
    rw [h_int_def] at h1
    have h2 : (T.b : ℝ) * dyadicDelta n = (T.b : ℝ) / (2 : ℝ)^n := by
      simp [dyadicDelta] <;> field_simp <;> ring
    rw [h2] at h1
    exact h1
  have hb_real2 : (T.b : ℝ) / (2 : ℝ)^n ≤ 3 := by
    have h1 : T.intercept ≤ 3 := (abs_le.mp h_intercept).2
    rw [h_int_def] at h1
    have h2 : (T.b : ℝ) * dyadicDelta n = (T.b : ℝ) / (2 : ℝ)^n := by
      simp [dyadicDelta] <;> field_simp <;> ring
    rw [h2] at h1
    exact h1
  set y : ℤ := 2 ^ n with hy_def
  have hy_pos : 0 < y := by positivity
  have hy_ne : y ≠ 0 := hy_pos.ne'
  let qa : ℤ := T.a / y
  let qb : ℤ := T.b / y
  have h_upper : ∀ (x : ℤ), ((x / y : ℤ) : ℝ) ≤ (x : ℝ) / (y : ℝ) := by
    intro x
    have h : (x / y) * y ≤ x := Int.ediv_mul_le x hy_ne
    have h' : (((x / y : ℤ) : ℝ)) * (y : ℝ) ≤ (x : ℝ) := by exact_mod_cast h
    have h_y_pos' : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy_pos
    calc ((x / y : ℤ) : ℝ)
      = (((x / y : ℤ) : ℝ)) * (y : ℝ) / (y : ℝ) := by field_simp [h_y_pos'.ne'] <;> ring
    _ ≤ (x : ℝ) / (y : ℝ) := by gcongr
  have h_lower : ∀ (x : ℤ), (x : ℝ) / (y : ℝ) - 1 < ((x / y : ℤ) : ℝ) := by
    intro x
    have h1 : x % y < y := Int.emod_lt_of_pos x hy_pos
    have h2 : x = (x / y) * y + x % y := by exact Eq.symm (Int.ediv_mul_add_emod x y)
    have h3 : x < (x / y + 1) * y := by
      have h4 : (x / y) * y + x % y < (x / y + 1) * y := by
        have h5 : (x / y + 1) * y = (x / y) * y + y := by ring
        rw [h5]
        have h6 : (x / y) * y + x % y < (x / y) * y + y := by linarith [h1]
        exact h6
      linarith [h2, h4]
    have h5 : (x : ℝ) < (((x / y + 1 : ℤ) : ℝ)) * (y : ℝ) := by exact_mod_cast h3
    have h_y_pos' : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy_pos
    have h6 : (x : ℝ) / (y : ℝ) < (((x / y + 1 : ℤ) : ℝ)) := by
      calc (x : ℝ) / (y : ℝ)
        < ((((x / y + 1 : ℤ) : ℝ)) * (y : ℝ)) / (y : ℝ) := by gcongr
      _ = (((x / y + 1 : ℤ) : ℝ)) := by field_simp [h_y_pos'.ne'] <;> ring
    have h7 : (((x / y + 1 : ℤ) : ℝ)) = ((x / y : ℤ) : ℝ) + 1 := by simp
    rw [h7] at h6
    linarith
  have ha_real1' : -3 / 2 ≤ (T.a : ℝ) / (y : ℝ) := by
    simpa [hy_def] using ha_real1
  have ha_real2' : (T.a : ℝ) / (y : ℝ) ≤ 3 / 2 := by
    simpa [hy_def] using ha_real2
  have hb_real1' : -3 ≤ (T.b : ℝ) / (y : ℝ) := by
    simpa [hy_def] using hb_real1
  have hb_real2' : (T.b : ℝ) / (y : ℝ) ≤ 3 := by
    simpa [hy_def] using hb_real2
  have ha_int1 : -2 ≤ qa := by
    have h7 : (T.a : ℝ) / (y : ℝ) - 1 < (qa : ℝ) := h_lower T.a
    have h8 : (qa : ℝ) > -5 / 2 := by linarith [ha_real1']
    by_contra h
    have h9 : qa ≤ -3 := by omega
    have h10 : (qa : ℝ) ≤ -3 := by exact_mod_cast h9
    linarith
  have ha_int2 : qa ≤ 1 := by
    have h7 : (qa : ℝ) ≤ (T.a : ℝ) / (y : ℝ) := h_upper T.a
    have h8 : (qa : ℝ) ≤ 3 / 2 := by linarith [ha_real2']
    by_contra h
    have h9 : qa ≥ 2 := by omega
    have h10 : (qa : ℝ) ≥ 2 := by exact_mod_cast h9
    linarith
  have hb_int1 : -3 ≤ qb := by
    have h7 : (T.b : ℝ) / (y : ℝ) - 1 < (qb : ℝ) := h_lower T.b
    have h8 : (qb : ℝ) > -4 := by linarith [hb_real1']
    by_contra h
    have h9 : qb ≤ -4 := by omega
    have h10 : (qb : ℝ) ≤ -4 := by exact_mod_cast h9
    linarith
  have hb_int2 : qb ≤ 3 := by
    have h7 : (qb : ℝ) ≤ (T.b : ℝ) / (y : ℝ) := h_upper T.b
    have h8 : (qb : ℝ) ≤ 3 := by linarith [hb_real2']
    by_contra h
    have h9 : qb ≥ 4 := by omega
    have h10 : (qb : ℝ) ≥ 4 := by exact_mod_cast h9
    linarith
  have ha_in : qa ∈ Finset.Icc (-2 : ℤ) 1 := by
    simp only [Finset.mem_Icc] <;> omega
  have hb_in : qb ∈ Finset.Icc (-3 : ℤ) 3 := by
    simp only [Finset.mem_Icc] <;> omega
  simp only [rootTubeCubes, Finset.mem_biUnion]
  refine' ⟨qa, ha_in, _⟩
  simp only [Finset.mem_image]
  refine' ⟨qb, hb_in, _⟩
  have h_qa : qa = T.a / y := by rfl
  have h_qb : qb = T.b / y := by rfl
  simp [dyadicTubeAncestor, hy_def, h_qa, h_qb] <;> rfl

/-! ### Half-capacity cover -/

structure SomeDyadicTube where
  level : ℕ
  tube : DyadicTube level

def SomeDyadicTube.side (T : SomeDyadicTube) : ℝ := dyadicDelta T.level

/-- Leaf case for half-cap cover. -/
def halfCapCoverTubeLeaf {n : ℕ} (s : ℝ)
    (S : Finset (DyadicTube n)) (A : DyadicTube n) :
    Finset SomeDyadicTube :=
  if (tubesInCube (by linarith) A S).card > 0 then
    {⟨n, A⟩}
  else
    ∅

noncomputable def halfCapCoverTube {n : ℕ} (s : ℝ)
    (S : Finset (DyadicTube n))
    (j : ℕ) (hjn : j ≤ n)
    (A : DyadicTube j) :
    Finset SomeDyadicTube :=
  if h : j < n then
    if ((tubesInCube hjn A S).card : ℝ) ≥ (dyadicTubeCap n j s) / 2 then
      {⟨j, A⟩}
    else
      (dyadicTubeChildren A).biUnion (fun child =>
        halfCapCoverTube s S (j + 1) (by omega) child)
  else
    have h_jn : j = n := by omega
    halfCapCoverTubeLeaf s S (h_jn ▸ A)
termination_by n - j

noncomputable def halfCapCoverTubes {n : ℕ} (s : ℝ)
    (S : Finset (DyadicTube n)) :
    Finset SomeDyadicTube :=
  rootTubeCubes.biUnion (fun A => halfCapCoverTube s S 0 (by linarith) A)

/-- All elements of halfCapCoverTube have level ≤ n. -/
lemma halfCapCoverTube_level_le {n : ℕ} {s : ℝ} {S : Finset (DyadicTube n)}
    {j : ℕ} {hj : j ≤ n} {A : DyadicTube j} {Q : SomeDyadicTube}
    (hQ : Q ∈ halfCapCoverTube s S j hj A) : Q.level ≤ n := by
  have h_ind : ∀ (m : ℕ), m ≤ n →
      ∀ (j : ℕ) (hjn : j ≤ n) (h_eq : n - j = m) (A : DyadicTube j)
        (Q : SomeDyadicTube), Q ∈ halfCapCoverTube s S j hjn A → Q.level ≤ n := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hmn j hjn h_eq A Q hQ
      by_cases hlt : j < n
      · by_cases hcap : ((tubesInCube hjn A S).card : ℝ) ≥ (dyadicTubeCap n j s) / 2
        · unfold halfCapCoverTube at hQ
          rw [dif_pos hlt] at hQ
          rw [if_pos hcap] at hQ
          simp only [Finset.mem_singleton] at hQ
          rw [hQ] <;> exact hjn
        · unfold halfCapCoverTube at hQ
          rw [dif_pos hlt] at hQ
          rw [if_neg hcap] at hQ
          rcases Finset.mem_biUnion.mp hQ with ⟨child, hchild, hQ⟩
          have h_child_lt : n - (j + 1) < m := by omega
          exact ih (n - (j + 1)) h_child_lt (by omega) (j + 1) (by omega) rfl child Q hQ
      · have h_jn : j = n := by omega
        cases h_jn with
        | refl =>
          have h_not_lt : ¬n < n := by omega
          have h_eval : halfCapCoverTube s S n (by linarith) A = halfCapCoverTubeLeaf s S A := by
            unfold halfCapCoverTube
            rw [dif_neg h_not_lt] <;> rfl
          rw [h_eval] at hQ
          have h_pos : (tubesInCube (by linarith) A S).card > 0 := by
            by_contra h
            rw [halfCapCoverTubeLeaf, if_neg h] at hQ
            simp at hQ
          have h_leaf : halfCapCoverTubeLeaf s S A = {⟨n, A⟩} := by
            rw [halfCapCoverTubeLeaf, if_pos h_pos] <;> rfl
          rw [h_leaf] at hQ
          have hQ' : Q = ⟨n, A⟩ := by simpa using hQ
          rw [hQ'] <;> rfl
  exact h_ind (n - j) (by omega) j hj rfl A Q hQ

/-- All elements of halfCapCoverTube have level ≥ j. -/
lemma halfCapCoverTube_level_ge {n : ℕ} {s : ℝ} {S : Finset (DyadicTube n)}
    {j : ℕ} {hj : j ≤ n} {A : DyadicTube j} {Q : SomeDyadicTube}
    (hQ : Q ∈ halfCapCoverTube s S j hj A) : j ≤ Q.level := by
  have h_ind : ∀ (m : ℕ), m ≤ n →
      ∀ (j : ℕ) (hjn : j ≤ n) (h_eq : n - j = m) (A : DyadicTube j)
        (Q : SomeDyadicTube), Q ∈ halfCapCoverTube s S j hjn A → j ≤ Q.level := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hmn j hjn h_eq A Q hQ
      by_cases hlt : j < n
      · by_cases hcap : ((tubesInCube hjn A S).card : ℝ) ≥ (dyadicTubeCap n j s) / 2
        · unfold halfCapCoverTube at hQ
          rw [dif_pos hlt] at hQ
          rw [if_pos hcap] at hQ
          simp only [Finset.mem_singleton] at hQ
          rw [hQ] <;> rfl
        · unfold halfCapCoverTube at hQ
          rw [dif_pos hlt] at hQ
          rw [if_neg hcap] at hQ
          rcases Finset.mem_biUnion.mp hQ with ⟨child, hchild, hQ⟩
          have h_child_lt : n - (j + 1) < m := by omega
          have h_ge : j + 1 ≤ Q.level := ih (n - (j + 1)) h_child_lt (by omega) (j + 1) (by omega) rfl child Q hQ
          omega
      · have h_jn : j = n := by omega
        cases h_jn with
        | refl =>
          have h_not_lt : ¬n < n := by omega
          have h_eval : halfCapCoverTube s S n (by linarith) A = halfCapCoverTubeLeaf s S A := by
            unfold halfCapCoverTube
            rw [dif_neg h_not_lt] <;> rfl
          rw [h_eval] at hQ
          have h_pos : (tubesInCube (by linarith) A S).card > 0 := by
            by_contra h
            rw [halfCapCoverTubeLeaf, if_neg h] at hQ
            simp at hQ
          have h_leaf : halfCapCoverTubeLeaf s S A = {⟨n, A⟩} := by
            rw [halfCapCoverTubeLeaf, if_pos h_pos] <;> rfl
          rw [h_leaf] at hQ
          have hQ' : Q = ⟨n, A⟩ := by simpa using hQ
          rw [hQ'] <;> rfl
  exact h_ind (n - j) (by omega) j hj rfl A Q hQ

/-- Cover cubes have ≥ cap/2 survivors. -/
lemma halfCapCover_half_cap {n : ℕ} {s : ℝ} {S : Finset (DyadicTube n)}
    {j : ℕ} {hj : j ≤ n} {A : DyadicTube j}
    (hQ : (⟨j, A⟩ : SomeDyadicTube) ∈ halfCapCoverTube s S j hj A) :
    ((tubesInCube hj A S).card : ℝ) ≥ (dyadicTubeCap n j s) / 2 := by
  by_cases hlt : j < n
  · unfold halfCapCoverTube at hQ
    rw [dif_pos hlt] at hQ
    by_cases hcap : ((tubesInCube hj A S).card : ℝ) ≥ (dyadicTubeCap n j s) / 2
    · exact hcap
    · rw [if_neg hcap] at hQ
      rcases Finset.mem_biUnion.mp hQ with ⟨child, hchild, hQ⟩
      have h_ge : j + 1 ≤ (⟨j, A⟩ : SomeDyadicTube).level := halfCapCoverTube_level_ge hQ
      simp at h_ge <;> omega
  · have h_jn : j = n := by omega
    cases h_jn with
    | refl =>
      have h_not_lt : ¬n < n := by omega
      have h_eval : halfCapCoverTube s S n (by linarith) A = halfCapCoverTubeLeaf s S A := by
        unfold halfCapCoverTube
        rw [dif_neg h_not_lt] <;> rfl
      rw [h_eval] at hQ
      have h_pos : (tubesInCube (by linarith) A S).card > 0 := by
        by_contra h
        rw [halfCapCoverTubeLeaf, if_neg h] at hQ
        simp at hQ
      have h_cap1 : dyadicTubeCap n n s = 1 := dyadicTubeCap_leaf
      rw [h_cap1]
      have h4 : (tubesInCube (by linarith) A S).card ≥ 1 := Nat.succ_le_iff.mpr h_pos
      have h5 : ((tubesInCube (by linarith) A S).card : ℝ) ≥ 1 := by exact_mod_cast h4
      have h6 : ((tubesInCube (by linarith) A S).card : ℝ) ≥ 1 / 2 := by linarith
      exact h6

/-- Descendant set of a cover cube at scale n (empty if level > n). -/
def descendantSet (n : ℕ) (Q : SomeDyadicTube) : Set (DyadicTube n) :=
  if h : Q.level ≤ n then
    {T | dyadicTubeAncestor Q.level h T = Q.tube}
  else
    ∅

/-- A child's level-j ancestor is its parent tube. -/
lemma child_ancestor_is_parent {j : ℕ} {T : DyadicTube j}
    {child : DyadicTube (j + 1)} (hchild : child ∈ dyadicTubeChildren T) :
    dyadicTubeAncestor j (by linarith) child = T := by
  have hdiv2 : ∀ (x : ℤ), (2 * x) / 2 = x := by
    intro x; rw [Int.mul_ediv_cancel_left _ (by norm_num)]
  have hdiv2_add1 : ∀ (x : ℤ), (2 * x + 1) / 2 = x := by
    intro x; omega
  simp only [dyadicTubeChildren, Finset.mem_insert, Finset.mem_singleton] at hchild
  rcases hchild with (rfl | rfl | rfl | rfl)
  all_goals {
    simp [dyadicTubeAncestor, hdiv2, hdiv2_add1] <;> rfl
  }

/-- Helper: (x / 2^(k-1)) / 2 = x / 2^k for k > 0. -/
lemma int_ediv_two_pow_comp (x : ℤ) (k : ℕ) (hk : 0 < k) :
    (x / 2^(k - 1)) / 2 = x / 2^k := by
  have h := int_div_two_pow_sub x k hk
  rcases h with (h | h)
  · rw [h]
    have h5 : (2 * (x / 2^k)) / 2 = x / 2^k := by
      rw [Int.mul_ediv_cancel_left _ (by norm_num)]
    exact h5
  · rw [h]
    have h5 : (2 * (x / 2^k) + 1) / 2 = x / 2^k := by omega
    exact h5

/-- Composition: level-j ancestor of level-(j+1) ancestor equals level-j ancestor. -/
lemma ancestor_composition {n : ℕ} {j : ℕ} (hjn : j < n) (t : DyadicTube n) :
    dyadicTubeAncestor j (by linarith) t =
    dyadicTubeAncestor j (by linarith) (dyadicTubeAncestor (j + 1) (by omega) t) := by
  have hk : 0 < n - j := by omega
  have ha : (t.a / 2 ^ (n - j - 1)) / 2 = t.a / 2 ^ (n - j) :=
    int_ediv_two_pow_comp t.a (n - j) hk
  have hb : (t.b / 2 ^ (n - j - 1)) / 2 = t.b / 2 ^ (n - j) :=
    int_ediv_two_pow_comp t.b (n - j) hk
  have h_eq : n - (j + 1) = n - j - 1 := by omega
  simp [dyadicTubeAncestor, h_eq, ha, hb] <;> rfl

/-- Helper: dyadicTubeAncestor at the same level is identity. -/
lemma dyadicTubeAncestor_self {k : ℕ} (T : DyadicTube k) :
    dyadicTubeAncestor k (by linarith) T = T := by
  simp [dyadicTubeAncestor] <;> rfl

/-- General integer division composition: (x / 2^a) / 2^b = x / 2^(a+b). -/
lemma int_ediv_two_pow_comp_gen (x : ℤ) (a b : ℕ) :
    (x / 2^a) / 2^b = x / 2^(a + b) := by
  induction b with
  | zero => simp
  | succ b' ih =>
    have h1 : (x / 2^a) / 2^(b' + 1) = ((x / 2^a) / 2^b') / 2 := by
      have h2 := int_ediv_two_pow_comp (x / 2^a) (b' + 1) (by positivity)
      exact h2.symm
    rw [h1, ih]
    have h3 := int_ediv_two_pow_comp x (a + b' + 1) (by positivity)
    have h4 : a + b' + 1 = a + (b' + 1) := by omega
    rw [h4] at h3
    exact h3

/-- General ancestor composition: level-j ancestor of level-k ancestor is level-j ancestor. -/
lemma dyadicTubeAncestor_compose {n : ℕ} {j k : ℕ} (hjk : j ≤ k) (hkn : k ≤ n)
    (T : DyadicTube n) :
    dyadicTubeAncestor j hjk (dyadicTubeAncestor k hkn T) =
    dyadicTubeAncestor j (by linarith) T := by
  have h_sum : (n - k) + (k - j) = n - j := by omega
  have ha : (T.a / 2^(n - k)) / 2^(k - j) = T.a / 2^(n - j) := by
    rw [int_ediv_two_pow_comp_gen T.a (n - k) (k - j), h_sum]
  have hb : (T.b / 2^(n - k)) / 2^(k - j) = T.b / 2^(n - j) := by
    rw [int_ediv_two_pow_comp_gen T.b (n - k) (k - j), h_sum]
  simp [dyadicTubeAncestor, ha, hb] <;> rfl

/-- Every member of the half-cap cover from c has c as its level-j ancestor. -/
lemma halfCapCoverTube_member_ancestor {n : ℕ} {s : ℝ} {S : Finset (DyadicTube n)} :
    ∀ (j : ℕ) (hjn : j ≤ n) (c : DyadicTube j) (Q' : SomeDyadicTube),
      Q' ∈ halfCapCoverTube s S j hjn c →
        ∃ (hlev : j ≤ Q'.level), dyadicTubeAncestor j hlev Q'.tube = c := by
  have h_ind : ∀ (m : ℕ), m ≤ n →
      ∀ (j : ℕ) (hjn : j ≤ n) (h_eq : n - j = m) (c : DyadicTube j)
        (Q' : SomeDyadicTube), Q' ∈ halfCapCoverTube s S j hjn c →
          ∃ (hlev : j ≤ Q'.level), dyadicTubeAncestor j hlev Q'.tube = c := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hmn j hjn h_eq c Q' hQ'
      by_cases hlt : j < n
      · by_cases hcap : ((tubesInCube hjn c S).card : ℝ) ≥ (dyadicTubeCap n j s) / 2
        · unfold halfCapCoverTube at hQ'
          rw [dif_pos hlt, if_pos hcap] at hQ'
          simp only [Finset.mem_singleton] at hQ'
          subst hQ'
          refine' ⟨le_refl j, dyadicTubeAncestor_self c⟩
        · unfold halfCapCoverTube at hQ'
          rw [dif_pos hlt, if_neg hcap] at hQ'
          rcases Finset.mem_biUnion.mp hQ' with ⟨child, hchild, hQ'⟩
          have h_child_lt : n - (j + 1) < m := by omega
          rcases ih (n - (j + 1)) h_child_lt (by omega) (j + 1) (by omega) rfl child Q' hQ' with ⟨hlev1, hanc1⟩
          have hlev : j ≤ Q'.level := by omega
          refine' ⟨hlev, _⟩
          have h_j_lt_level : j < Q'.level := by omega
          have hcomp : dyadicTubeAncestor j hlev Q'.tube =
              dyadicTubeAncestor j (by omega) (dyadicTubeAncestor (j + 1) hlev1 Q'.tube) :=
            ancestor_composition h_j_lt_level Q'.tube
          rw [hcomp, hanc1]
          exact child_ancestor_is_parent hchild
      · have h_jn : j = n := by omega
        cases h_jn with
        | refl =>
          have h_not_lt : ¬n < n := by omega
          have h_eval : halfCapCoverTube s S n (by linarith) c = halfCapCoverTubeLeaf s S c := by
            unfold halfCapCoverTube; rw [dif_neg h_not_lt] <;> rfl
          rw [h_eval] at hQ'
          by_cases hpos : (tubesInCube (by linarith) c S).card > 0
          · rw [halfCapCoverTubeLeaf, if_pos hpos] at hQ'
            simp only [Finset.mem_singleton] at hQ'
            subst hQ'
            refine' ⟨le_refl n, dyadicTubeAncestor_self c⟩
          · rw [halfCapCoverTubeLeaf, if_neg hpos] at hQ'
            simp at hQ'
  intro j hjn c Q' hQ'
  exact h_ind (n - j) (by omega) j hjn rfl c Q' hQ'

/-- Half-cap covers from different children are disjoint. -/
lemma halfCapCoverTube_disjoint {n : ℕ} {s : ℝ} {S : Finset (DyadicTube n)}
    {j : ℕ} {T : DyadicTube j} {c1 c2 : DyadicTube (j + 1)}
    (hjn : j + 1 ≤ n)
    (hc1 : c1 ∈ dyadicTubeChildren T) (hc2 : c2 ∈ dyadicTubeChildren T) (hne : c1 ≠ c2) :
    Disjoint (halfCapCoverTube s S (j + 1) hjn c1)
             (halfCapCoverTube s S (j + 1) hjn c2) := by
  rw [Finset.disjoint_left]
  intro Q' hQ'1 hQ'2
  rcases halfCapCoverTube_member_ancestor (j + 1) hjn c1 Q' hQ'1 with ⟨hlev1, hanc1⟩
  rcases halfCapCoverTube_member_ancestor (j + 1) hjn c2 Q' hQ'2 with ⟨hlev2, hanc2⟩
  have h3 : c1 = c2 := hanc1.symm.trans hanc2
  exact hne h3

/-- Within a single cover, distinct cubes have disjoint descendant sets. -/
lemma halfCapCoverTube_descendant_disjoint {n : ℕ} {s : ℝ} {S : Finset (DyadicTube n)}
    {j : ℕ} {hj : j ≤ n} {A : DyadicTube j} {Q1 Q2 : SomeDyadicTube}
    (hQ1 : Q1 ∈ halfCapCoverTube s S j hj A)
    (hQ2 : Q2 ∈ halfCapCoverTube s S j hj A)
    (hne : Q1 ≠ Q2) :
    Disjoint (descendantSet n Q1) (descendantSet n Q2) := by
  have h_ind : ∀ (m : ℕ), m ≤ n →
      ∀ (j : ℕ) (hjn : j ≤ n) (h_eq : n - j = m) (A : DyadicTube j)
        (Q1 Q2 : SomeDyadicTube), Q1 ∈ halfCapCoverTube s S j hjn A →
          Q2 ∈ halfCapCoverTube s S j hjn A → Q1 ≠ Q2 →
            Disjoint (descendantSet n Q1) (descendantSet n Q2) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hmn j hjn h_eq A Q1 Q2 hQ1 hQ2 hne
      by_cases hlt : j < n
      · by_cases hcap : ((tubesInCube hjn A S).card : ℝ) ≥ (dyadicTubeCap n j s) / 2
        · unfold halfCapCoverTube at hQ1 hQ2
          rw [dif_pos hlt, if_pos hcap] at hQ1 hQ2
          simp only [Finset.mem_singleton] at hQ1 hQ2
          exfalso; exact hne (hQ1.trans hQ2.symm)
        · unfold halfCapCoverTube at hQ1 hQ2
          rw [dif_pos hlt, if_neg hcap] at hQ1 hQ2
          rcases Finset.mem_biUnion.mp hQ1 with ⟨c1, hc1, hQ1'⟩
          rcases Finset.mem_biUnion.mp hQ2 with ⟨c2, hc2, hQ2'⟩
          by_cases hc : c1 = c2
          · subst hc
            have h_child_lt : n - (j + 1) < m := by omega
            exact ih (n - (j + 1)) h_child_lt (by omega) (j + 1) (by omega) rfl c1 Q1 Q2 hQ1' hQ2' hne
          · have h_main : ∀ (T : DyadicTube n), T ∈ descendantSet n Q1 → T ∉ descendantSet n Q2 := by
              intro T hT1 hT2
              have h1 : Q1.level ≤ n := halfCapCoverTube_level_le hQ1'
              have h2 : Q2.level ≤ n := halfCapCoverTube_level_le hQ2'
              rcases halfCapCoverTube_member_ancestor (j + 1) (by omega) c1 Q1 hQ1' with ⟨hlev1, hanc1⟩
              rcases halfCapCoverTube_member_ancestor (j + 1) (by omega) c2 Q2 hQ2' with ⟨hlev2, hanc2⟩
              have hT1' : dyadicTubeAncestor Q1.level h1 T = Q1.tube := by
                simpa [descendantSet, h1] using hT1
              have hT2' : dyadicTubeAncestor Q2.level h2 T = Q2.tube := by
                simpa [descendantSet, h2] using hT2
              have h_anc1 : dyadicTubeAncestor (j + 1) (by omega) T = c1 := by
                have hcomp : dyadicTubeAncestor (j + 1) (by omega) T =
                    dyadicTubeAncestor (j + 1) (by omega) (dyadicTubeAncestor Q1.level h1 T) :=
                  (dyadicTubeAncestor_compose (by omega) h1 T).symm
                rw [hcomp, hT1', hanc1]
              have h_anc2 : dyadicTubeAncestor (j + 1) (by omega) T = c2 := by
                have hcomp : dyadicTubeAncestor (j + 1) (by omega) T =
                    dyadicTubeAncestor (j + 1) (by omega) (dyadicTubeAncestor Q2.level h2 T) :=
                  (dyadicTubeAncestor_compose (by omega) h2 T).symm
                rw [hcomp, hT2', hanc2]
              rw [h_anc1] at h_anc2
              exact hc h_anc2
            have h_disj : Disjoint (descendantSet n Q1) (descendantSet n Q2) := by
              exact Set.disjoint_left.mpr h_main
            exact h_disj
      · have h_jn : j = n := by omega
        cases h_jn with
        | refl =>
          have h_not_lt : ¬n < n := by omega
          have h_eval1 : halfCapCoverTube s S n (by linarith) A = halfCapCoverTubeLeaf s S A := by
            unfold halfCapCoverTube; rw [dif_neg h_not_lt] <;> rfl
          rw [h_eval1] at hQ1 hQ2
          by_cases hpos : (tubesInCube (by linarith) A S).card > 0
          · rw [halfCapCoverTubeLeaf, if_pos hpos] at hQ1 hQ2
            simp only [Finset.mem_singleton] at hQ1 hQ2
            exfalso; exact hne (hQ1.trans hQ2.symm)
          · rw [halfCapCoverTubeLeaf, if_neg hpos] at hQ1
            simp at hQ1
  exact h_ind (n - j) (by omega) j hj rfl A Q1 Q2 hQ1 hQ2 hne

lemma halfCapCoverTubes_disjoint {n : ℕ} {s : ℝ} {S : Finset (DyadicTube n)}
    {Q1 Q2 : SomeDyadicTube}
    (hQ1 : Q1 ∈ halfCapCoverTubes s S)
    (hQ2 : Q2 ∈ halfCapCoverTubes s S)
    (hne : Q1 ≠ Q2) :
    Disjoint (descendantSet n Q1) (descendantSet n Q2) := by
  rcases Finset.mem_biUnion.mp hQ1 with ⟨A1, hA1, hQ1'⟩
  rcases Finset.mem_biUnion.mp hQ2 with ⟨A2, hA2, hQ2'⟩
  by_cases hA : A1 = A2
  · subst hA
    exact halfCapCoverTube_descendant_disjoint hQ1' hQ2' hne
  · have h_main : ∀ (T : DyadicTube n), T ∈ descendantSet n Q1 → T ∉ descendantSet n Q2 := by
      intro T hT1 hT2
      have h1 : Q1.level ≤ n := halfCapCoverTube_level_le hQ1'
      have h2 : Q2.level ≤ n := halfCapCoverTube_level_le hQ2'
      have hT1' : dyadicTubeAncestor Q1.level h1 T = Q1.tube := by
        simpa [descendantSet, h1] using hT1
      have hT2' : dyadicTubeAncestor Q2.level h2 T = Q2.tube := by
        simpa [descendantSet, h2] using hT2
      rcases halfCapCoverTube_member_ancestor 0 (by linarith) A1 Q1 hQ1' with ⟨hlev1, hanc1⟩
      rcases halfCapCoverTube_member_ancestor 0 (by linarith) A2 Q2 hQ2' with ⟨hlev2, hanc2⟩
      have h_anc1 : dyadicTubeAncestor 0 (by linarith) T = A1 := by
        have hcomp : dyadicTubeAncestor 0 (by linarith) T =
            dyadicTubeAncestor 0 (by linarith) (dyadicTubeAncestor Q1.level h1 T) :=
          (dyadicTubeAncestor_compose (by omega) h1 T).symm
        rw [hcomp, hT1', hanc1]
      have h_anc2 : dyadicTubeAncestor 0 (by linarith) T = A2 := by
        have hcomp : dyadicTubeAncestor 0 (by linarith) T =
            dyadicTubeAncestor 0 (by linarith) (dyadicTubeAncestor Q2.level h2 T) :=
          (dyadicTubeAncestor_compose (by omega) h2 T).symm
        rw [hcomp, hT2', hanc2]
      rw [h_anc1] at h_anc2
      exact hA h_anc2
    exact Set.disjoint_left.mpr h_main

/-- Path lemma: if some ancestor on the path meets half-cap, the cover contains a cube above t. -/
lemma halfCapCoverTube_path_cover {n : ℕ} {s : ℝ} {S : Finset (DyadicTube n)} :
    ∀ (m : ℕ), m ≤ n →
    ∀ (j : ℕ) (hj : j ≤ n) (h_eq : n - j = m) (A : DyadicTube j) (t : DyadicTube n),
      dyadicTubeAncestor j hj t = A →
      (∃ (k : ℕ) (hk : j ≤ k) (hkn : k ≤ n) (B : DyadicTube k),
        dyadicTubeAncestor k hkn t = B ∧
        ((tubesInCube hkn B S).card : ℝ) ≥ (dyadicTubeCap n k s) / 2) →
      ∃ (Q : SomeDyadicTube), Q ∈ halfCapCoverTube s S j hj A ∧ t ∈ descendantSet n Q := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hmn j hj h_eq A t ht_anc h_exists
    by_cases hcap : ((tubesInCube hj A S).card : ℝ) ≥ (dyadicTubeCap n j s) / 2
    · refine' ⟨⟨j, A⟩, _, _⟩
      · by_cases hlt : j < n
        · unfold halfCapCoverTube
          rw [dif_pos hlt, if_pos hcap] <;> simp
        · have h_jn : j = n := by omega
          cases h_jn with | refl =>
            have h_not_lt : ¬n < n := by omega
            have h10 : dyadicTubeCap n n s = 1 := dyadicTubeCap_leaf
            have h_pos : (tubesInCube (by linarith) A S).card > 0 := by
              have h9 : ((tubesInCube (by linarith) A S).card : ℝ) ≥ (dyadicTubeCap n n s) / 2 := hcap
              rw [h10] at h9
              by_contra h10
              have h11 : (tubesInCube (by linarith) A S).card = 0 := by omega
              rw [h11] at h9 <;> norm_num at h9
            unfold halfCapCoverTube
            rw [dif_neg h_not_lt, halfCapCoverTubeLeaf, if_pos h_pos] <;> simp
      · have hlev : j ≤ n := hj
        simpa [descendantSet, hlev] using ht_anc
    · have hlt : j < n := by
        by_contra h
        have h_jn : j = n := by omega
        rcases h_exists with ⟨k, hk1, hk2, B, hanc, hk⟩
        have h_kj : k = j := by omega
        subst h_kj
        have h_eq : dyadicTubeAncestor k hk2 t = dyadicTubeAncestor k (by omega) t := by congr
        have h_B : B = A := by
          rw [←hanc, h_eq, ht_anc]
        rw [h_B] at hk
        exact hcap hk
      let child := dyadicTubeAncestor (j + 1) (by omega) t
      have hchild : child ∈ dyadicTubeChildren A := by
        rw [← ht_anc]
        exact ancestor_child_nat hlt t
      have h_ih' : ∃ (k : ℕ) (hk : j + 1 ≤ k) (hkn : k ≤ n) (B : DyadicTube k),
          dyadicTubeAncestor k hkn t = B ∧
          ((tubesInCube hkn B S).card : ℝ) ≥ (dyadicTubeCap n k s) / 2 := by
        rcases h_exists with ⟨k, hk1, hk2, B, hanc, hk⟩
        by_cases h : j < k
        · exact ⟨k, by omega, hk2, B, hanc, hk⟩
        · have h_kj : k = j := by omega
          subst h_kj
          have h_eq : dyadicTubeAncestor k hk2 t = dyadicTubeAncestor k (by omega) t := by congr
          have h_B : B = A := by
            rw [←hanc, h_eq, ht_anc]
          rw [h_B] at hk
          exfalso
          exact hcap hk
      have h_child_lt : n - (j + 1) < m := by omega
      rcases ih (n - (j + 1)) h_child_lt (by omega) (j + 1) (by omega) rfl child t
          (by rfl) h_ih' with ⟨Q, hQ, htdesc⟩
      refine' ⟨Q, _, htdesc⟩
      unfold halfCapCoverTube
      rw [dif_pos hlt, if_neg hcap]
      exact Finset.mem_biUnion.mpr ⟨child, hchild, hQ⟩

/-- The half-cap cover covers ALL tubes in rawTubes. -/
lemma halfCapCoverTubes_covers_all {n : ℕ} {s : ℝ}
    {rawTubes S : Finset (DyadicTube n)}
    (hs_pos : 0 < s)
    (hS_sub : S ⊆ rawTubes)
    (hS_cap : TubeCapacityRespecting (s := s) S)
    (h_max : ∀ (t : DyadicTube n), t ∈ rawTubes → t ∉ S →
      ∃ (j : ℕ) (hj : j ≤ n) (A : DyadicTube j),
        dyadicTubeAncestor j hj t = A ∧
        (tubesInCube hj A S).card = Nat.floor (dyadicTubeCap n j s))
    (hraw_slope : ∀ U ∈ rawTubes, |U.slope| ≤ 3 / 2)
    (hraw_intercept : ∀ U ∈ rawTubes, |U.intercept| ≤ 3) :
    ∀ (t : DyadicTube n), t ∈ rawTubes →
      ∃ (Q : SomeDyadicTube), Q ∈ halfCapCoverTubes s S ∧
        t ∈ descendantSet n Q := by
  intro t ht
  set A0 : DyadicTube 0 := dyadicTubeAncestor 0 (by linarith) t with hA0_def
  have hA0_in : A0 ∈ rootTubeCubes :=
    rootTubeCubes_cover t (hraw_slope t ht) (hraw_intercept t ht)
  have h_exists : ∃ (k : ℕ) (hk : 0 ≤ k) (hkn : k ≤ n) (B : DyadicTube k),
      dyadicTubeAncestor k hkn t = B ∧
      ((tubesInCube hkn B S).card : ℝ) ≥ (dyadicTubeCap n k s) / 2 := by
    by_cases hts : t ∈ S
    · let B : DyadicTube n := dyadicTubeAncestor n (by linarith) t
      have hB : B = t := dyadicTubeAncestor_self t
      have h1 : t ∈ tubesInCube (by linarith) B S := by
        simp only [tubesInCube, Finset.mem_filter]
        have h_anc : dyadicTubeAncestor n (by linarith) t = B := by
          rw [dyadicTubeAncestor_self, hB]
        exact ⟨hts, h_anc⟩
      have h2 : (tubesInCube (by linarith) B S).card ≥ 1 :=
        Finset.card_pos.mpr ⟨t, h1⟩
      have h3 : ((tubesInCube (by linarith) B S).card : ℝ) ≥ 1 := by exact_mod_cast h2
      have h4 : dyadicTubeCap n n s = 1 := dyadicTubeCap_leaf
      have h5 : ((tubesInCube (by linarith) B S).card : ℝ) ≥ (dyadicTubeCap n n s) / 2 := by
        rw [h4]; linarith
      exact ⟨n, by omega, by omega, B, rfl, h5⟩
    · rcases h_max t ht hts with ⟨j, hj, A, hanc, hcard⟩
      have hcap1 : dyadicTubeCap n j s ≥ 1 := dyadicTubeCap_one_le hs_pos hj
      have h4 : ((tubesInCube hj A S).card : ℝ) ≥ (dyadicTubeCap n j s) / 2 := by
        have h5 : ((tubesInCube hj A S).card : ℝ) = ↑(Nat.floor (dyadicTubeCap n j s)) := by
          exact_mod_cast hcard
        rw [h5]
        exact floor_ge_half (dyadicTubeCap n j s) hcap1
      exact ⟨j, by omega, hj, A, hanc, h4⟩
  rcases halfCapCoverTube_path_cover (n - 0) (by omega) 0 (by linarith) (by omega) A0 t
      (by rfl) h_exists with ⟨Q, hQ, htdesc⟩
  refine' ⟨Q, _, htdesc⟩
  simp only [halfCapCoverTubes, Finset.mem_biUnion]
  exact ⟨A0, hA0_in, hQ⟩

/-- External covering number is subadditive over finite unions. -/
lemma externalCoveringNumber_biUnion_le {X : Type*} [PseudoMetricSpace X]
    {ε : NNReal} {ι : Type*} (I : Finset ι) (A : ι → Set X) :
    Metric.externalCoveringNumber ε (⋃ i ∈ I, A i) ≤
      ∑ i ∈ I, Metric.externalCoveringNumber ε (A i) := by
  by_cases h : (∀ i ∈ I, Metric.externalCoveringNumber ε (A i) ≠ ⊤)
  · have h_choose : ∀ (i : ι), i ∈ I → ∃ (C_i : Set X),
        Metric.IsCover ε (A i) C_i ∧
        C_i.encard = Metric.externalCoveringNumber ε (A i) := by
      intro i hi
      letI : Nonempty {C : Set X // Metric.IsCover ε (A i) C} :=
        ⟨⟨A i, by simp⟩⟩
      have h_exists := ENat.exists_eq_iInf
        (fun (C : {C : Set X // Metric.IsCover ε (A i) C}) => (C.val : Set X).encard)
      rcases h_exists with ⟨C, hC_eq⟩
      have h_ext : (C.val : Set X).encard = Metric.externalCoveringNumber ε (A i) := by
        rw [hC_eq]
        simp_rw [Metric.externalCoveringNumber, iInf_subtype] <;> rfl
      exact ⟨C.val, C.property, h_ext⟩
    let C : ι → Set X := fun i =>
      if h : i ∈ I then Classical.choose (h_choose i h) else ∅
    have hC_cover : ∀ i ∈ I, Metric.IsCover ε (A i) (C i) := by
      intro i hi
      have hC_def : C i = Classical.choose (h_choose i hi) := by simp [C, hi]
      rw [hC_def]
      exact (Classical.choose_spec (h_choose i hi)).1
    have hC_eq : ∀ i ∈ I, (C i).encard = Metric.externalCoveringNumber ε (A i) := by
      intro i hi
      have hC_def : C i = Classical.choose (h_choose i hi) := by simp [C, hi]
      rw [hC_def]
      exact (Classical.choose_spec (h_choose i hi)).2
    let C_union : Set X := ⋃ i ∈ I, C i
    have h_cover : Metric.IsCover ε (⋃ i ∈ I, A i) C_union := by
      intro x hx
      have h_mem : ∃ (i : ι), i ∈ I ∧ x ∈ A i := by
        simpa [Set.mem_iUnion₂] using hx
      rcases h_mem with ⟨i, hi, hxi⟩
      have h : ∃ c, c ∈ C i ∧ edist x c ≤ ε := hC_cover i hi hxi
      rcases h with ⟨c, hc, hdist⟩
      have hc' : c ∈ C_union := by
        simp only [C_union, Set.mem_iUnion₂]
        exact ⟨i, hi, hc⟩
      exact ⟨c, hc', hdist⟩
    have h1 : Metric.externalCoveringNumber ε (⋃ i ∈ I, A i) ≤ C_union.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard h_cover
    have h_fin : ∀ i ∈ I, (C i).Finite := by
      intro i hi
      have h_ne_top : (C i).encard ≠ ⊤ := by
        rw [hC_eq i hi]; exact h i hi
      exact Set.encard_ne_top_iff.mp h_ne_top
    let Cfin : ι → Finset X := fun i =>
      if h : i ∈ I then (h_fin i h).toFinset else ∅
    have hCfin_coe : ∀ i ∈ I, (Cfin i : Set X) = C i := by
      intro i hi
      have hdef : Cfin i = (h_fin i hi).toFinset := by simp [Cfin, hi]
      rw [hdef]
      exact (h_fin i hi).coe_toFinset
    let Ufinset : Finset X := I.biUnion Cfin
    have hU_eq : (Ufinset : Set X) = C_union := by
      ext x
      simp only [Ufinset, Finset.mem_coe, Finset.mem_biUnion, C_union, Set.mem_iUnion₂]
      constructor
      · rintro ⟨i, hi, hx⟩
        have h_in : x ∈ (Cfin i : Set X) := hx
        have h_eq : (Cfin i : Set X) = C i := hCfin_coe i hi
        exact ⟨i, hi, h_eq ▸ h_in⟩
      · rintro ⟨i, hi, hx⟩
        have h_eq : (Cfin i : Set X) = C i := hCfin_coe i hi
        have h_goal : x ∈ C i := hx
        have h_in : x ∈ (Cfin i : Set X) := by
          have h : x ∈ C i := h_goal
          have h' : (Cfin i : Set X) = C i := h_eq
          exact h'.symm ▸ h
        exact ⟨i, hi, h_in⟩
    have h2 : C_union.encard ≤ ∑ i ∈ I, (C i).encard := by
      rw [← hU_eq]
      have h3 : (Ufinset : Set X).encard = ↑Ufinset.card := by simp
      rw [h3]
      have h4 : ↑Ufinset.card ≤ ∑ i ∈ I, ↑(Cfin i).card := by
        exact_mod_cast Finset.card_biUnion_le
      have h5 : ∑ i ∈ I, ↑(Cfin i).card ≤ ∑ i ∈ I, (C i).encard := by
        apply Finset.sum_le_sum
        intro i hi
        have h6 : (Cfin i : Set X) = C i := hCfin_coe i hi
        have h7 : ↑(Cfin i).card = (C i).encard := by
          simpa using congr_arg Set.encard h6
        rw [h7]
      exact le_trans (by exact_mod_cast h4) h5
    have h6 : ∑ i ∈ I, (C i).encard = ∑ i ∈ I, Metric.externalCoveringNumber ε (A i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hC_eq i hi
    calc
      Metric.externalCoveringNumber ε (⋃ i ∈ I, A i)
        ≤ C_union.encard := h1
      _ ≤ ∑ i ∈ I, (C i).encard := h2
      _ = ∑ i ∈ I, Metric.externalCoveringNumber ε (A i) := h6
  · have h' : ∃ i ∈ I, Metric.externalCoveringNumber ε (A i) = ⊤ := by
      simpa [not_forall] using h
    rcases h' with ⟨i, hi, htop⟩
    have h5 : (∑ j ∈ I, Metric.externalCoveringNumber ε (A j)) = ⊤ := by
      have h_zero_le : ∀ (j : ι), j ∈ I → 0 ≤ Metric.externalCoveringNumber ε (A j) :=
        fun _ _ => bot_le
      have h6 : Metric.externalCoveringNumber ε (A i) ≤ ∑ j ∈ I, Metric.externalCoveringNumber ε (A j) :=
        Finset.single_le_sum h_zero_le hi
      rw [htop] at h6
      simpa using h6
    rw [h5] <;> exact le_top

/-- S-set cover sum bound for finite DyadicTube sets. -/
lemma sset_cover_sum_radii_bound_tubes
    {n : ℕ} {δ s C : ℝ} {P : Set (DyadicTube n)}
    (hP : IsDeltaSSet δ s C P)
    (hP_fin : P.Finite)
    (hδ_pos : 0 < δ) (hs_pos : 0 < s)
    {ι : Type*} (I : Finset ι)
    (Q : ι → Set (DyadicTube n))
    (r : ι → ℝ)
    (hcover : P ⊆ ⋃ i ∈ I, Q i)
    (hr_geδ : ∀ i ∈ I, δ ≤ r i)
    (hr_nonneg : ∀ i ∈ I, 0 ≤ r i)
    (hQ_in_ball : ∀ i ∈ I, ∃ c : DyadicTube n, Q i ⊆ Metric.closedBall c (r i)) :
    (1 : ℝ) ≤ C * ∑ i ∈ I, (r i)^s := by
  let δnn := δ.toNNReal
  have hδnn_pos : 0 < δnn := by
    have h : (δnn : ℝ) = δ := by rw [Real.coe_toNNReal] <;> linarith
    exact NNReal.coe_pos.mp (h ▸ hδ_pos)
  have hP_nonempty : P.Nonempty := hP.1
  have hC_pos : 0 < C := hP.2.2.1
  have hs_nonneg : 0 ≤ s := by linarith
  have hNP_ne_top : Metric.externalCoveringNumber δnn P ≠ ⊤ := by
    have hfc := Metric.exists_finite_isCover_of_totallyBounded hδnn_pos.ne'
      hP_fin.totallyBounded
    rcases hfc with ⟨N, _, hNfin, hNcover⟩
    have h : Metric.externalCoveringNumber δnn P ≤ N.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hNcover
    have h2 : N.encard ≠ ⊤ := by exact Set.encard_ne_top_iff.mpr hNfin
    exact ne_top_of_le_ne_top h2 h
  have hNP_pos : 0 < Metric.externalCoveringNumber δnn P :=
    Metric.externalCoveringNumber_pos_iff.mpr hP_nonempty
  have h_bound : ∀ i ∈ I, (Metric.externalCoveringNumber δnn (P ∩ Q i) : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal (r i)) ^ s *
        (Metric.externalCoveringNumber δnn P : ENNReal) := by
    intro i hi
    rcases hQ_in_ball i hi with ⟨c, hc⟩
    have h1 : P ∩ Q i ⊆ P ∩ Metric.closedBall c (r i) := by gcongr <;> exact hc
    have h2 : (Metric.externalCoveringNumber δnn (P ∩ Q i) : ENNReal) ≤
        (Metric.externalCoveringNumber δnn (P ∩ Metric.closedBall c (r i)) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set h1
    have h3 := hP.2.2.2.2 c (r i) (hr_geδ i hi)
    exact le_trans h2 h3
  have h_sub : (Metric.externalCoveringNumber δnn P : ENNReal) ≤
      ∑ i ∈ I, (Metric.externalCoveringNumber δnn (P ∩ Q i) : ENNReal) := by
    have h4 : P ⊆ ⋃ i ∈ I, P ∩ Q i := by
      intro x hx
      have h5 : x ∈ ⋃ i ∈ I, Q i := hcover hx
      have h_mem : ∃ (i : ι), i ∈ I ∧ x ∈ Q i := by
        simpa [Set.mem_iUnion₂] using h5
      rcases h_mem with ⟨i, hi, hxi⟩
      exact Set.mem_iUnion₂.mpr ⟨i, hi, ⟨hx, hxi⟩⟩
    have h5 : (Metric.externalCoveringNumber δnn P : ENNReal) ≤
        (Metric.externalCoveringNumber δnn (⋃ i ∈ I, P ∩ Q i) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set h4
    have h6 : (Metric.externalCoveringNumber δnn (⋃ i ∈ I, P ∩ Q i) : ENNReal) ≤
        ∑ i ∈ I, (Metric.externalCoveringNumber δnn (P ∩ Q i) : ENNReal) := by
      have h7 := externalCoveringNumber_biUnion_le (ε := δnn) I (fun i => P ∩ Q i)
      have h_sum_coe : ((∑ i ∈ I, Metric.externalCoveringNumber δnn (P ∩ Q i) : ENat) : ENNReal) =
          ∑ i ∈ I, (Metric.externalCoveringNumber δnn (P ∩ Q i) : ENNReal) := by
        have h_main : ∀ (s : Finset ι), ((∑ i ∈ s, Metric.externalCoveringNumber δnn (P ∩ Q i) : ENat) : ENNReal) =
            ∑ i ∈ s, (Metric.externalCoveringNumber δnn (P ∩ Q i) : ENNReal) := by
          intro s
          induction s using Finset.induction with
          | empty => simp
          | @insert a s ha ih =>
            rw [Finset.sum_insert ha, Finset.sum_insert ha]
            have h_add : ((Metric.externalCoveringNumber δnn (P ∩ Q a) + ∑ i ∈ s, Metric.externalCoveringNumber δnn (P ∩ Q i) : ENat) : ENNReal) =
                (Metric.externalCoveringNumber δnn (P ∩ Q a) : ENNReal) + ((∑ i ∈ s, Metric.externalCoveringNumber δnn (P ∩ Q i) : ENat) : ENNReal) := by
              norm_cast
            rw [h_add, ih]
        exact h_main I
      have h8 : (Metric.externalCoveringNumber δnn (⋃ i ∈ I, P ∩ Q i) : ENNReal) ≤
          ((∑ i ∈ I, Metric.externalCoveringNumber δnn (P ∩ Q i) : ENat) : ENNReal) := by
        exact_mod_cast h7
      rw [h_sum_coe] at h8
      exact h8
    exact le_trans h5 h6
  have h_sum_rpow : ∑ i ∈ I, (ENNReal.ofReal (r i)) ^ s =
      ENNReal.ofReal (∑ i ∈ I, (r i)^s) := by
    have h3 : ∀ i ∈ I, (ENNReal.ofReal (r i)) ^ s = ENNReal.ofReal ((r i)^s) := by
      intro i _
      rw [← ENNReal.ofReal_rpow_of_nonneg (hr_nonneg i ‹_›) hs_nonneg] <;> rfl
    rw [Finset.sum_congr rfl h3]
    have h4 : ∀ (fins : Finset ι), fins ⊆ I → ∑ i ∈ fins, ENNReal.ofReal ((r i)^s) = ENNReal.ofReal (∑ i ∈ fins, (r i)^s) := by
      intro fins hfins
      induction fins using Finset.induction with
      | empty => simp
      | @insert a fins ha ih =>
        have ha' : a ∈ I := hfins (Finset.mem_insert_self a fins)
        have hfins' : fins ⊆ I := fun x hx => hfins (Finset.mem_insert_of_mem hx)
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        have h_nonneg1 : 0 ≤ (r a)^s := Real.rpow_nonneg (hr_nonneg a ha') s
        have h_nonneg2 : 0 ≤ ∑ i ∈ fins, (r i)^s := by
          apply Finset.sum_nonneg
          intro i hi
          exact Real.rpow_nonneg (hr_nonneg i (hfins' hi)) s
        rw [ih hfins', ← ENNReal.ofReal_add h_nonneg1 h_nonneg2]
    exact h4 I (by simp)
  have h7 : ∑ i ∈ I, (Metric.externalCoveringNumber δnn (P ∩ Q i) : ENNReal) ≤
      (ENNReal.ofReal C * ENNReal.ofReal (∑ i ∈ I, (r i)^s)) *
        (Metric.externalCoveringNumber δnn P : ENNReal) := by
    calc
      ∑ i ∈ I, (Metric.externalCoveringNumber δnn (P ∩ Q i) : ENNReal)
        ≤ ∑ i ∈ I, (ENNReal.ofReal C * (ENNReal.ofReal (r i)) ^ s *
              (Metric.externalCoveringNumber δnn P : ENNReal)) :=
          Finset.sum_le_sum h_bound
      _ = (∑ i ∈ I, (ENNReal.ofReal C * (ENNReal.ofReal (r i)) ^ s)) *
          (Metric.externalCoveringNumber δnn P : ENNReal) := by
        rw [Finset.sum_mul]
      _ = (ENNReal.ofReal C * ∑ i ∈ I, (ENNReal.ofReal (r i)) ^ s) *
          (Metric.externalCoveringNumber δnn P : ENNReal) := by
        rw [Finset.mul_sum]
      _ = (ENNReal.ofReal C * ENNReal.ofReal (∑ i ∈ I, (r i)^s)) *
          (Metric.externalCoveringNumber δnn P : ENNReal) := by
        rw [h_sum_rpow]
  have h8 : (Metric.externalCoveringNumber δnn P : ENNReal) ≤
      (ENNReal.ofReal C * ENNReal.ofReal (∑ i ∈ I, (r i)^s)) *
        (Metric.externalCoveringNumber δnn P : ENNReal) :=
    le_trans h_sub h7
  let NP_ENN : ENNReal := ENat.toENNReal (Metric.externalCoveringNumber δnn P)
  have hNP_ENN_ne_top : NP_ENN ≠ ⊤ := by
    simp only [NP_ENN, ENat.toENNReal_ne_top]
    exact hNP_ne_top
  have hNP_ENN_pos : 0 < NP_ENN := by
    have h_ne_zero : Metric.externalCoveringNumber δnn P ≠ 0 := hNP_pos.ne'
    have h : (Metric.externalCoveringNumber δnn P : ENNReal) ≠ 0 := by
      intro h2
      have h3 : Metric.externalCoveringNumber δnn P = 0 := by exact_mod_cast h2
      exact h_ne_zero h3
    have h_zero_le : 0 ≤ (Metric.externalCoveringNumber δnn P : ENNReal) := by simp
    exact lt_of_le_of_ne h_zero_le h.symm
  let NP : ℝ := NP_ENN.toReal
  have hNP_pos' : 0 < NP := by
    have h_iff : 0 < NP_ENN.toReal ↔ 0 < NP_ENN ∧ NP_ENN < ⊤ := by
      rw [ENNReal.toReal_pos_iff]
    have h_lt_top : NP_ENN < ⊤ := Ne.lt_top hNP_ENN_ne_top
    exact h_iff.mpr ⟨hNP_ENN_pos, h_lt_top⟩
  have h9 : NP ≤ (C * ∑ i ∈ I, (r i)^s) * NP := by
    have h10 : ENNReal.ofReal C * ENNReal.ofReal (∑ i ∈ I, (r i)^s) =
        ENNReal.ofReal (C * ∑ i ∈ I, (r i)^s) := by
      rw [← ENNReal.ofReal_mul] <;> positivity
    rw [h10] at h8
    have h11 : NP_ENN ≤ ENNReal.ofReal (C * ∑ i ∈ I, (r i)^s) * NP_ENN := h8
    have h_b_ne_top : (ENNReal.ofReal (C * ∑ i ∈ I, (r i)^s) * NP_ENN) ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · exact ENNReal.ofReal_ne_top
      · exact hNP_ENN_ne_top
    have h12 : (ENNReal.ofReal (C * ∑ i ∈ I, (r i)^s) * NP_ENN).toReal =
        (ENNReal.ofReal (C * ∑ i ∈ I, (r i)^s)).toReal * NP_ENN.toReal := by
      rw [ENNReal.toReal_mul] <;> simp [hNP_ENN_ne_top]
    have h_iff : NP_ENN.toReal ≤ (ENNReal.ofReal (C * ∑ i ∈ I, (r i)^s) * NP_ENN).toReal :=
      (ENNReal.toReal_le_toReal hNP_ENN_ne_top h_b_ne_top).mpr h11
    have h13 : NP_ENN.toReal ≤ (ENNReal.ofReal (C * ∑ i ∈ I, (r i)^s) * NP_ENN).toReal := h_iff
    rw [h12] at h13
    have h_nonneg_sum : 0 ≤ ∑ i ∈ I, (r i)^s := by
      apply Finset.sum_nonneg
      intro i hi
      exact Real.rpow_nonneg (hr_nonneg i hi) s
    have h_nonneg : 0 ≤ C * ∑ i ∈ I, (r i)^s := mul_nonneg hC_pos.le h_nonneg_sum
    have h14 : (ENNReal.ofReal (C * ∑ i ∈ I, (r i)^s)).toReal = C * ∑ i ∈ I, (r i)^s := by
      rw [ENNReal.toReal_ofReal h_nonneg]
    rw [h14] at h13
    exact h13
  have h10 : (1 : ℝ) ≤ C * ∑ i ∈ I, (r i)^s := by
    have h11 : NP ≤ (C * ∑ i ∈ I, (r i)^s) * NP := h9
    have h12 : 0 < NP := hNP_pos'
    nlinarith
  exact h10

/-- Partition of a tube cube into its four children. -/
lemma tubesInCube_children_card {n : ℕ} {j : ℕ} (hjn : j < n)
    (T : DyadicTube j) (S : Finset (DyadicTube n)) :
    (tubesInCube (by linarith) T S).card =
      ∑ child ∈ dyadicTubeChildren T, (tubesInCube (by omega) child S).card := by
  have h1 : tubesInCube (by linarith) T S =
      (dyadicTubeChildren T).biUnion (fun child => tubesInCube (by omega) child S) := by
    ext t
    simp only [tubesInCube, Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨ht, hanc⟩
      let child := dyadicTubeAncestor (j + 1) (by omega) t
      have hchild : child ∈ dyadicTubeChildren T := by
        rw [←hanc]
        exact ancestor_child_nat hjn t
      exact ⟨child, hchild, ht, rfl⟩
    · rintro ⟨child, hchild, ht, hanc⟩
      have hcomp : dyadicTubeAncestor j (by linarith) t =
          dyadicTubeAncestor j (by linarith) (dyadicTubeAncestor (j + 1) (by omega) t) :=
        ancestor_composition hjn t
      have hpar : dyadicTubeAncestor j (by linarith) t = T := by
        rw [hcomp, hanc, child_ancestor_is_parent hchild]
      exact ⟨ht, hpar⟩
  rw [h1]
  have h_disj : ∀ c1 ∈ dyadicTubeChildren T, ∀ c2 ∈ dyadicTubeChildren T, c1 ≠ c2 →
      Disjoint (tubesInCube (by omega) c1 S) (tubesInCube (by omega) c2 S) := by
    intro c1 _ c2 _ hne
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    have h1 : dyadicTubeAncestor (j + 1) (by omega) t = c1 := (Finset.mem_filter.mp ht1).2
    have h2 : dyadicTubeAncestor (j + 1) (by omega) t = c2 := (Finset.mem_filter.mp ht2).2
    rw [h1] at h2
    exact hne h2
  rw [Finset.card_biUnion h_disj]

/-- Integer division bounds: if a / d = q (floor division), then q*d ≤ a < (q+1)*d. -/
lemma int_ediv_bounds (a : ℤ) {d : ℤ} (hd_pos : 0 < d) (q : ℤ) (h_eq : a / d = q) :
    q * d ≤ a ∧ a < (q + 1) * d := by
  have h5 : a = (a / d) * d + (a % d) := by
    exact Eq.symm (Int.ediv_mul_add_emod a d)
  have h4 : 0 ≤ a % d := Int.emod_nonneg a (by linarith)
  have h6 : a % d < d := Int.emod_lt_of_pos a hd_pos
  rw [h_eq] at *
  constructor
  · linarith
  · linarith

/-- Scale relation: δ_j = 2^(n-j) * δ_n. -/
lemma dyadicDelta_scale {n j : ℕ} (hjn : j ≤ n) :
    dyadicDelta j = (2 ^ (n - j) : ℝ) * dyadicDelta n := by
  have h_sum : (n - j) + j = n := by omega
  simp only [dyadicDelta]
  have h2 : (2 : ℝ)^((n - j) + j) = (2 : ℝ)^(n - j) * (2 : ℝ)^j := by
    rw [pow_add]
  have h2' : (2 : ℝ)^n = (2 : ℝ)^(n - j) * (2 : ℝ)^j := by
    have h3 : (2 : ℝ)^n = (2 : ℝ)^((n - j) + j) := by rw [h_sum]
    rw [h3, h2]
  have h_pos1 : (0 : ℝ) < (2 : ℝ)^(n - j) := by positivity
  have h_pos2 : (0 : ℝ) < (2 : ℝ)^j := by positivity
  have h4 : ((2 ^ (n - j) : ℝ) * (1 / (2 : ℝ)^n)) = 1 / (2 : ℝ)^j := by
    have h5 : (1 : ℝ) / (2 : ℝ)^n = 1 / ((2 : ℝ)^(n - j) * (2 : ℝ)^j) := by rw [h2']
    rw [h5]
    field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
  exact h4.symm

/-- Any member Q of a half-capacity cover has ≥ cap(Q.level)/2 survivors in S. -/
lemma halfCapCover_half_cap_general {n : ℕ} {s : ℝ} {S : Finset (DyadicTube n)}
    {j : ℕ} {hj : j ≤ n} {A : DyadicTube j} {Q : SomeDyadicTube}
    (hQ : Q ∈ halfCapCoverTube s S j hj A) :
    ((tubesInCube (halfCapCoverTube_level_le hQ) Q.tube S).card : ℝ) ≥
      (dyadicTubeCap n Q.level s) / 2 := by
  have h_main : ∀ (m : ℕ), m ≤ n →
      ∀ (j : ℕ) (hjn : j ≤ n) (h_eq : n - j = m) (A : DyadicTube j)
        (Q : SomeDyadicTube) (hlev : Q.level ≤ n),
        Q ∈ halfCapCoverTube s S j hjn A →
          ((tubesInCube hlev Q.tube S).card : ℝ) ≥
            (dyadicTubeCap n Q.level s) / 2 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hmn j hjn h_eq A Q hlev hQ
      by_cases hlt : j < n
      · by_cases hcap : ((tubesInCube hjn A S).card : ℝ) ≥ (dyadicTubeCap n j s) / 2
        · unfold halfCapCoverTube at hQ
          rw [dif_pos hlt, if_pos hcap] at hQ
          simp only [Finset.mem_singleton] at hQ
          subst hQ
          exact hcap
        · unfold halfCapCoverTube at hQ
          rw [dif_pos hlt, if_neg hcap] at hQ
          rcases Finset.mem_biUnion.mp hQ with ⟨child, hchild, hQ'⟩
          have h_child_lt : n - (j + 1) < m := by omega
          exact ih (n - (j + 1)) h_child_lt (by omega) (j + 1) (by omega) rfl child Q hlev hQ'
      · have h_jn : j = n := by omega
        cases h_jn with | refl =>
          have h_not_lt : ¬n < n := by omega
          have h_eval : halfCapCoverTube s S n (by linarith) A = halfCapCoverTubeLeaf s S A := by
            unfold halfCapCoverTube; rw [dif_neg h_not_lt] <;> rfl
          rw [h_eval] at hQ
          have h_pos : (tubesInCube (by linarith) A S).card > 0 := by
            by_contra h
            rw [halfCapCoverTubeLeaf, if_neg h] at hQ <;> simp at hQ
          have h_leaf : halfCapCoverTubeLeaf s S A = {⟨n, A⟩} := by
            rw [halfCapCoverTubeLeaf, if_pos h_pos] <;> rfl
          rw [h_leaf] at hQ
          have hQ' : Q = ⟨n, A⟩ := by simpa using hQ
          subst hQ'
          have h_cap1 : dyadicTubeCap n n s = 1 := dyadicTubeCap_leaf
          have h4 : (tubesInCube (by linarith) A S).card ≥ 1 := Nat.succ_le_iff.mpr h_pos
          have h5 : ((tubesInCube (by linarith) A S).card : ℝ) ≥ 1 := by exact_mod_cast h4
          have h6 : ((tubesInCube (by linarith) A S).card : ℝ) ≥ (dyadicTubeCap n n s) / 2 := by
            rw [h_cap1]; linarith
          exact h6
  exact h_main (n - j) (by omega) j hj rfl A Q (halfCapCoverTube_level_le hQ) hQ

/-- If x/d = y/d for positive d, then |x-y| < d. -/
lemma int_ediv_same_abs_lt {x y : ℤ} {d : ℤ} (hd_pos : 0 < d)
    (h : x / d = y / d) : |x - y| < d := by
  have h1 : x = (x / d) * d + x % d := by exact Eq.symm (Int.ediv_mul_add_emod x d)
  have h2 : y = (y / d) * d + y % d := by exact Eq.symm (Int.ediv_mul_add_emod y d)
  have h3 : x - y = x % d - y % d := by
    have h4 : x - y = ((x / d) * d + x % d) - ((y / d) * d + y % d) := by
      exact congr_arg₂ (fun (a b : ℤ) => a - b) h1 h2
    rw [h4]
    have h5 : ((x / d) * d + x % d) - ((y / d) * d + y % d) = x % d - y % d := by
      rw [h] <;> simp [sub_eq_add_neg] <;> ring
    exact h5
  rw [h3]
  have h4 : 0 ≤ x % d := Int.emod_nonneg _ (by positivity)
  have h5 : x % d < d := Int.emod_lt_of_pos _ (by positivity)
  have h6 : 0 ≤ y % d := Int.emod_nonneg _ (by positivity)
  have h7 : y % d < d := Int.emod_lt_of_pos _ (by positivity)
  have h8 : x % d - y % d < d := by linarith
  have h9 : -(x % d - y % d) < d := by linarith
  rw [abs_lt] <;> constructor <;> linarith

/-- Tubes with same level-j ancestor have distance < 2*dyadicDelta j. -/
lemma same_ancestor_dist_lt {n j : ℕ} (hj : j ≤ n)
    (T1 T2 : DyadicTube n)
    (h : dyadicTubeAncestor j hj T1 = dyadicTubeAncestor j hj T2) :
    T1.dist T2 < 2 * dyadicDelta j := by
  set d : ℤ := 2 ^ (n - j) with hd_def
  have hd_pos : 0 < d := by positivity
  have ha1 : T1.a / d = T2.a / d := by
    simpa [dyadicTubeAncestor] using congr_arg DyadicTube.a h
  have hb1 : T1.b / d = T2.b / d := by
    simpa [dyadicTubeAncestor] using congr_arg DyadicTube.b h
  have ha2 : |T1.a - T2.a| < d := int_ediv_same_abs_lt hd_pos ha1
  have hb2 : |T1.b - T2.b| < d := int_ediv_same_abs_lt hd_pos hb1
  have h_dist : T1.dist T2 = dyadicDelta n *
      ((|(T1.a - T2.a : ℤ)| : ℝ) + (|(T1.b - T2.b : ℤ)| : ℝ)) :=
    DyadicTube.dist_eq T1 T2
  rw [h_dist]
  have h7 : ((|(T1.a - T2.a : ℤ)| : ℝ) + (|(T1.b - T2.b : ℤ)| : ℝ)) < 2 * (d : ℝ) := by
    have h71 : (|(T1.a - T2.a : ℤ)| : ℝ) < (d : ℝ) := by exact_mod_cast ha2
    have h72 : (|(T1.b - T2.b : ℤ)| : ℝ) < (d : ℝ) := by exact_mod_cast hb2
    linarith
  have h_sum : (n - j) + j = n := by omega
  have h8 : dyadicDelta n * (d : ℝ) = dyadicDelta j := by
    have h10 : dyadicDelta n * (d : ℝ) = (1 : ℝ) / (2 : ℝ)^n * (2 : ℝ)^(n - j) := by
      simp [dyadicDelta, hd_def] <;> ring
    rw [h10]
    have h11 : (2 : ℝ)^(n - j) * (2 : ℝ)^j = (2 : ℝ)^n := by
      rw [← pow_add, h_sum]
    have h12 : (1 : ℝ) / (2 : ℝ)^n * (2 : ℝ)^(n - j) = (1 : ℝ) / (2 : ℝ)^j := by
      have h_pos1 : (0 : ℝ) < (2 : ℝ)^n := by positivity
      have h_pos2 : (0 : ℝ) < (2 : ℝ)^j := by positivity
      field_simp [h_pos1.ne', h_pos2.ne']
      <;> rw [h11] <;> ring
    exact h12
  have h10 : 0 < dyadicDelta n := dyadicDelta_pos n
  calc dyadicDelta n * (((|(T1.a - T2.a : ℤ)| : ℝ) + (|(T1.b - T2.b : ℤ)| : ℝ)))
    < dyadicDelta n * (2 * (d : ℝ)) := mul_lt_mul_of_pos_left h7 h10
  _ = 2 * (dyadicDelta n * (d : ℝ)) := by ring
  _ = 2 * dyadicDelta j := by rw [h8]

/-- Descendant set of Q is contained in a closed ball of radius 2*dyadicDelta Q.level. -/
lemma descendantSet_in_ball {n : ℕ} {Q : SomeDyadicTube} (h : Q.level ≤ n)
    {c : DyadicTube n} (hc : c ∈ descendantSet n Q) :
    descendantSet n Q ⊆ Metric.closedBall c (2 * dyadicDelta Q.level) := by
  intro T hT
  have h1 : dyadicTubeAncestor Q.level h T = Q.tube := by
    simpa [descendantSet, h] using hT
  have h2 : dyadicTubeAncestor Q.level h c = Q.tube := by
    simpa [descendantSet, h] using hc
  have h3 : T.dist c < 2 * dyadicDelta Q.level :=
    same_ancestor_dist_lt h T c (h1.trans h2.symm)
  exact h3.le

/-- A finset of integers whose multiples of δ lie in a closed interval of length < 5δ has at most 5 elements. -/
lemma finset_int_in_interval_le_5 {s : Finset ℤ} {lo hi δ : ℝ} (hδ : 0 < δ)
    (h_len : hi - lo < 5 * δ)
    (h : ∀ k ∈ s, lo ≤ (k : ℝ) * δ ∧ (k : ℝ) * δ ≤ hi) :
    s.card ≤ 5 := by
  by_cases h_empty : s.Nonempty
  · let k_min := Finset.min' s h_empty
    let k_max := Finset.max' s h_empty
    have hk_min : k_min ∈ s := Finset.min'_mem s h_empty
    have hk_max : k_max ∈ s := Finset.max'_mem s h_empty
    have h1 : lo ≤ (k_min : ℝ) * δ := (h k_min hk_min).1
    have h2 : (k_max : ℝ) * δ ≤ hi := (h k_max hk_max).2
    have h3 : k_min ≤ k_max := Finset.min'_le s k_max hk_max
    have h4 : ((k_max : ℝ) - (k_min : ℝ)) * δ < 5 * δ := by
      have h5 : (k_max : ℝ) * δ - (k_min : ℝ) * δ ≤ hi - lo := by linarith
      have h6 : (k_max : ℝ) * δ - (k_min : ℝ) * δ = ((k_max : ℝ) - (k_min : ℝ)) * δ := by ring
      rw [h6] at h5
      linarith
    have h7 : (k_max : ℝ) - (k_min : ℝ) < 5 := by
      nlinarith
    have h8 : k_max - k_min < 5 := by exact_mod_cast h7
    have h9 : k_max - k_min ≤ 4 := by omega
    have h9 : ∀ k ∈ s, k_min ≤ k ∧ k ≤ k_max := by
      intro k hk
      exact ⟨Finset.min'_le s k hk, Finset.le_max' s k hk⟩
    have h10 : s ⊆ Finset.Icc k_min k_max := by
      intro k hk
      exact Finset.mem_Icc.mpr (h9 k hk)
    have h11 : s.card ≤ (Finset.Icc k_min k_max).card := Finset.card_le_card h10
    have h12 : (Finset.Icc k_min k_max).card = (k_max - k_min).natAbs + 1 := by
      simp [Finset.card_eq_zero]
      <;> omega
    rw [h12] at h11
    omega
  · simpa [Finset.not_nonempty_iff_eq_empty.mp h_empty] using by omega

/-- A ball of radius r < 2δ_j intersects at most 25 level-j dyadic cubes. -/
lemma ball_cube_count_le_25 {n j : ℕ} (hjn : j ≤ n)
    (x : DyadicTube n) (r : ℝ) (hr : r < 2 * dyadicDelta j)
    (cubes : Finset (DyadicTube j))
    (hcubes : ∀ A ∈ cubes, ∃ (T : DyadicTube n),
      dyadicTubeAncestor j hjn T = A ∧ T ∈ Metric.closedBall x r) :
    cubes.card ≤ 25 := by
  have hδ_pos : 0 < dyadicDelta j := dyadicDelta_pos j
  have h_len_gen : 2 * r + dyadicDelta j < 5 * dyadicDelta j := by linarith
  have h_len_slope : (x.slope + r) - (x.slope - r - dyadicDelta j) < 5 * dyadicDelta j := by
    have h : (x.slope + r) - (x.slope - r - dyadicDelta j) = 2 * r + dyadicDelta j := by ring
    rw [h]; exact h_len_gen
  have h_len_intercept : (x.intercept + r) - (x.intercept - r - dyadicDelta j) < 5 * dyadicDelta j := by
    have h : (x.intercept + r) - (x.intercept - r - dyadicDelta j) = 2 * r + dyadicDelta j := by ring
    rw [h]; exact h_len_gen
  let a_vals := cubes.image (fun A : DyadicTube j => A.a)
  let b_vals := cubes.image (fun A : DyadicTube j => A.b)
  set d : ℤ := 2 ^ (n - j) with hd_def
  have hd_pos : 0 < d := by positivity
  have h_scale : dyadicDelta j = (d : ℝ) * dyadicDelta n := by
    rw [dyadicDelta_scale hjn, hd_def] <;> norm_cast
  have hδn_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have ha_bound : a_vals.card ≤ 5 := by
    refine' finset_int_in_interval_le_5 (s := a_vals) (δ := dyadicDelta j)
      (lo := x.slope - r - dyadicDelta j) (hi := x.slope + r) hδ_pos h_len_slope _
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨A, hA, rfl⟩
    rcases hcubes A hA with ⟨T, hanc, hTball⟩
    have h_slope : |T.slope - x.slope| ≤ r := by
      have h1 : |T.slope - x.slope| ≤ T.dist x := by
        simp [DyadicTube.dist] <;> linarith [abs_nonneg (T.intercept - x.intercept)]
      have h2 : T.dist x ≤ r := hTball
      linarith [T.dist_comm x]
    have h4 : T.a / d = A.a := by
      simpa [dyadicTubeAncestor, hd_def] using congr_arg DyadicTube.a hanc
    have h_bounds := int_ediv_bounds T.a hd_pos A.a h4
    have h5 : (A.a : ℝ) * (d : ℝ) ≤ (T.a : ℝ) := by exact_mod_cast h_bounds.1
    have h6 : (T.a : ℝ) < ((A.a : ℝ) + 1) * (d : ℝ) := by exact_mod_cast h_bounds.2
    have h7 : (A.a : ℝ) * dyadicDelta j ≤ T.slope := by
      have h9 : T.slope = (T.a : ℝ) * dyadicDelta n := by rfl
      have h10 : (A.a : ℝ) * dyadicDelta j = ((A.a : ℝ) * (d : ℝ)) * dyadicDelta n := by
        rw [h_scale] <;> ring
      rw [h10, h9]
      exact mul_le_mul_of_nonneg_right h5 hδn_pos.le
    have h10 : T.slope < (A.a : ℝ) * dyadicDelta j + dyadicDelta j := by
      have h11 : T.slope = (T.a : ℝ) * dyadicDelta n := by rfl
      have h12 : (A.a : ℝ) * dyadicDelta j + dyadicDelta j = (((A.a : ℝ) + 1) * (d : ℝ)) * dyadicDelta n := by
        rw [h_scale] <;> ring
      rw [h11, h12]
      exact mul_lt_mul_of_pos_right h6 hδn_pos
    have h12 : x.slope - r ≤ T.slope := by
      have h13 : |T.slope - x.slope| ≤ r := h_slope
      have h14 : -r ≤ T.slope - x.slope := by linarith [abs_le.mp h13]
      linarith
    have h15 : T.slope ≤ x.slope + r := by
      have h16 : |T.slope - x.slope| ≤ r := h_slope
      have h17 : T.slope - x.slope ≤ r := by linarith [abs_le.mp h16]
      linarith
    have h18 : x.slope - r - dyadicDelta j ≤ (A.a : ℝ) * dyadicDelta j := by
      have h_eq : T.slope < (A.a : ℝ) * dyadicDelta j + dyadicDelta j := h10
      have h21 : x.slope - r - dyadicDelta j < (A.a : ℝ) * dyadicDelta j := by linarith
      exact h21.le
    have h19 : (A.a : ℝ) * dyadicDelta j ≤ x.slope + r := by
      exact h7.trans h15
    exact ⟨h18, h19⟩
  have hb_bound : b_vals.card ≤ 5 := by
    refine' finset_int_in_interval_le_5 (s := b_vals) (δ := dyadicDelta j)
      (lo := x.intercept - r - dyadicDelta j) (hi := x.intercept + r) hδ_pos h_len_intercept _
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨A, hA, rfl⟩
    rcases hcubes A hA with ⟨T, hanc, hTball⟩
    have h_intercept : |T.intercept - x.intercept| ≤ r := by
      have h1 : |T.intercept - x.intercept| ≤ T.dist x := by
        simp [DyadicTube.dist] <;> linarith [abs_nonneg (T.slope - x.slope)]
      have h2 : T.dist x ≤ r := hTball
      linarith [T.dist_comm x]
    have h4 : T.b / d = A.b := by
      simpa [dyadicTubeAncestor, hd_def] using congr_arg DyadicTube.b hanc
    have h_bounds := int_ediv_bounds T.b hd_pos A.b h4
    have h5 : (A.b : ℝ) * (d : ℝ) ≤ (T.b : ℝ) := by exact_mod_cast h_bounds.1
    have h6 : (T.b : ℝ) < ((A.b : ℝ) + 1) * (d : ℝ) := by exact_mod_cast h_bounds.2
    have h7 : (A.b : ℝ) * dyadicDelta j ≤ T.intercept := by
      have h9 : T.intercept = (T.b : ℝ) * dyadicDelta n := by rfl
      have h10 : (A.b : ℝ) * dyadicDelta j = ((A.b : ℝ) * (d : ℝ)) * dyadicDelta n := by
        rw [h_scale] <;> ring
      rw [h10, h9]
      exact mul_le_mul_of_nonneg_right h5 hδn_pos.le
    have h10 : T.intercept < (A.b : ℝ) * dyadicDelta j + dyadicDelta j := by
      have h11 : T.intercept = (T.b : ℝ) * dyadicDelta n := by rfl
      have h12 : (A.b : ℝ) * dyadicDelta j + dyadicDelta j = (((A.b : ℝ) + 1) * (d : ℝ)) * dyadicDelta n := by
        rw [h_scale] <;> ring
      rw [h11, h12]
      exact mul_lt_mul_of_pos_right h6 hδn_pos
    have h12 : x.intercept - r ≤ T.intercept := by
      have h13 : |T.intercept - x.intercept| ≤ r := h_intercept
      have h14 : -r ≤ T.intercept - x.intercept := by linarith [abs_le.mp h13]
      linarith
    have h15 : T.intercept ≤ x.intercept + r := by
      have h16 : |T.intercept - x.intercept| ≤ r := h_intercept
      have h17 : T.intercept - x.intercept ≤ r := by linarith [abs_le.mp h16]
      linarith
    have h18 : x.intercept - r - dyadicDelta j ≤ (A.b : ℝ) * dyadicDelta j := by
      have h_eq : T.intercept < (A.b : ℝ) * dyadicDelta j + dyadicDelta j := h10
      have h21 : x.intercept - r - dyadicDelta j < (A.b : ℝ) * dyadicDelta j := by linarith
      exact h21.le
    have h19 : (A.b : ℝ) * dyadicDelta j ≤ x.intercept + r := by
      exact h7.trans h15
    exact ⟨h18, h19⟩
  let prod_img := cubes.image (fun A : DyadicTube j => (A.a, A.b))
  have h_inj : Function.Injective (fun A : DyadicTube j => (A.a, A.b)) := by
    intro A1 A2 h
    have h1 : A1.a = A2.a := (Prod.ext_iff.mp h).1
    have h2 : A1.b = A2.b := (Prod.ext_iff.mp h).2
    cases A1 <;> cases A2 <;> simp_all
  have h_card : cubes.card = prod_img.card := by
    rw [Finset.card_image_of_injective _ h_inj]
  rw [h_card]
  have h_sub : prod_img ⊆ a_vals ×ˢ b_vals := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨A, hA, rfl⟩
    exact Finset.mem_product.mpr ⟨
      Finset.mem_image.mpr ⟨A, hA, rfl⟩,
      Finset.mem_image.mpr ⟨A, hA, rfl⟩⟩
  have h9 : prod_img.card ≤ (a_vals ×ˢ b_vals).card := Finset.card_le_card h_sub
  have h10 : (a_vals ×ˢ b_vals).card = a_vals.card * b_vals.card := Finset.card_product _ _
  rw [h10] at h9
  calc prod_img.card
    ≤ a_vals.card * b_vals.card := h9
  _ ≤ 5 * 5 := by gcongr <;> linarith
  _ = 25 := by norm_num

/-- Upper bound: a capacity-respecting subset with bounded slope/intercept has
    cardinality ≤ 28 * δ_n^{-s}. -/
lemma capacity_respecting_upper_bound {n : ℕ} {s : ℝ} {S : Finset (DyadicTube n)}
    (hS_cap : @TubeCapacityRespecting n s S)
    (hS_slope : ∀ U ∈ S, |U.slope| ≤ 3 / 2)
    (hS_intercept : ∀ U ∈ S, |U.intercept| ≤ 3)
    (δ_n : ℝ) (hδn_pos : 0 < δ_n) (hδn_eq : δ_n = dyadicDelta n) :
    (S.card : ℝ) ≤ (28 : ℝ) * δ_n^(-s) := by
  have h1 : ∀ A ∈ rootTubeCubes, (tubesInCube (by linarith) A S).card ≤ Nat.floor (dyadicTubeCap n 0 s) :=
    fun A _ => hS_cap 0 (by linarith) A
  have h2 : ∀ T ∈ S, dyadicTubeAncestor 0 (by linarith) T ∈ rootTubeCubes := by
    intro T hT
    exact rootTubeCubes_cover T (hS_slope T hT) (hS_intercept T hT)
  have h3 : S = rootTubeCubes.biUnion (fun A => tubesInCube (by linarith) A S) := by
    ext T
    simp only [Finset.mem_biUnion, tubesInCube, Finset.mem_filter]
    constructor
    · intro hT
      exact ⟨dyadicTubeAncestor 0 (by linarith) T, h2 T hT, hT, rfl⟩
    · rintro ⟨A, _, hT, _⟩
      exact hT
  have h_disj : ∀ A1 ∈ rootTubeCubes, ∀ A2 ∈ rootTubeCubes, A1 ≠ A2 →
      Disjoint (tubesInCube (by linarith) A1 S) (tubesInCube (by linarith) A2 S) := by
    intro A1 _ A2 _ hne
    rw [Finset.disjoint_left]
    intro T hT1 hT2
    have h4 : dyadicTubeAncestor 0 (by linarith) T = A1 := (Finset.mem_filter.mp hT1).2
    have h5 : dyadicTubeAncestor 0 (by linarith) T = A2 := (Finset.mem_filter.mp hT2).2
    rw [h4] at h5
    exact hne h5
  rw [h3]
  rw [Finset.card_biUnion h_disj]
  have h4 : ∑ A ∈ rootTubeCubes, (tubesInCube (by linarith) A S).card ≤
      ∑ A ∈ rootTubeCubes, Nat.floor (dyadicTubeCap n 0 s) :=
    Finset.sum_le_sum h1
  have h5 : (∑ A ∈ rootTubeCubes, Nat.floor (dyadicTubeCap n 0 s)) =
      rootTubeCubes.card * Nat.floor (dyadicTubeCap n 0 s) := by
    rw [Finset.sum_const] <;> ring
  rw [h5] at h4
  have h6 : rootTubeCubes.card = 28 := rootTubeCubes_card
  rw [h6] at h4
  have h7 : dyadicTubeCap n 0 s = δ_n^(-s) := by
    have hδ0 : dyadicDelta 0 = 1 := by
      simp [dyadicDelta] <;> norm_num
    have h_cap : dyadicTubeCap n 0 s = ((1 : ℝ) / dyadicDelta n)^s := by
      simp only [dyadicTubeCap, hδ0] <;> ring
    rw [h_cap]
    have h9 : ((1 : ℝ) / dyadicDelta n)^s = ((1 : ℝ) / δ_n)^s := by
      rw [hδn_eq]
    rw [h9]
    have h10 : ((1 : ℝ) / δ_n)^s = δ_n^(-s) := by
      have h11 : (1 : ℝ) / δ_n = δ_n⁻¹ := by field_simp [hδn_pos.ne'] <;> ring
      rw [h11]
      have h12 : (δ_n⁻¹)^s = (δ_n^s)⁻¹ := by
        rw [← Real.inv_rpow hδn_pos.le]
      have h13 : δ_n^(-s) = (δ_n^s)⁻¹ := Real.rpow_neg hδn_pos.le s
      rw [h12, h13]
    exact h10
  rw [h7] at h4
  have h8 : ((28 * Nat.floor (δ_n^(-s)) : ℕ) : ℝ) ≤ (28 : ℝ) * δ_n^(-s) := by
    have hpos : 0 ≤ δ_n^(-s) := by positivity
    have h9 : (Nat.floor (δ_n^(-s)) : ℝ) ≤ δ_n^(-s) := Nat.floor_le hpos
    have h10 : ((28 * Nat.floor (δ_n^(-s)) : ℕ) : ℝ) = (28 : ℝ) * (Nat.floor (δ_n^(-s)) : ℝ) := by
      norm_cast
    rw [h10]
    gcongr
    <;> norm_num
  have h10 : ((∑ A ∈ rootTubeCubes, (tubesInCube (by linarith) A S).card : ℕ) : ℝ) ≤
      ((28 * Nat.floor (δ_n^(-s)) : ℕ) : ℝ) := by exact_mod_cast h4
  linarith

end DiscretisedFurstenbergEstimate.FrontEndLemmas
