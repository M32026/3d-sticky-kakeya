module

public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Local geometry and homothety

Properties of `squareHomothety`, `containingSquare`, and the geometric homothety
`S_Q` that maps a coarse dyadic square `Q` to `[0,1)^2`.

## Whiteprint node
`InductionOnScales/LocalGeometry`
-/

open scoped BigOperators

noncomputable section

/-- `dyadicDelta n` is positive. -/
lemma dyadicDelta_pos (n : ℕ) : 0 < dyadicDelta n := by
  apply Real.rpow_pos_of_pos
  norm_num

/-- The refinement factor is positive. -/
lemma coarseRefinementFactor_pos (n m : ℕ) : 0 < coarseRefinementFactor n m := by
  simp [coarseRefinementFactor] <;> positivity

/-- `(2^k : ℝ) * dyadicDelta (k + m) = dyadicDelta m`. -/
lemma two_pow_mul_dyadicDelta (k m : ℕ) :
    ((2 ^ k : ℕ) : ℝ) * dyadicDelta (k + m) = dyadicDelta m := by
  have h_pos : (0 : ℝ) < 2 := by norm_num
  have h1 : ((2 ^ k : ℕ) : ℝ) = Real.rpow 2 (k : ℝ) := by simp
  rw [h1, dyadicDelta, dyadicDelta]
  have h2 : Real.rpow 2 (k : ℝ) * Real.rpow 2 (-((k + m : ℕ) : ℝ)) =
      Real.rpow 2 ((k : ℝ) + -((k + m : ℕ) : ℝ)) :=
    (Real.rpow_add h_pos (k : ℝ) (-((k + m : ℕ) : ℝ))).symm
  rw [h2]
  have h3 : (k : ℝ) + -((k + m : ℕ) : ℝ) = -(m : ℝ) := by
    simp [add_assoc] <;> ring_nf <;> norm_cast <;> omega
  rw [h3]

/-- Relationship between dyadic scales and refinement factor. -/
lemma dyadicDelta_mul_refinement (n m : ℕ) (hnm : m ≤ n) :
    (coarseRefinementFactor n m : ℝ) * dyadicDelta n = dyadicDelta m := by
  let k := n - m
  have h1 : n = k + m := by omega
  have h_main : ((2 ^ k : ℕ) : ℝ) * dyadicDelta n = dyadicDelta m := by
    rw [h1]
    exact two_pow_mul_dyadicDelta k m
  simpa [coarseRefinementFactor] using h_main

/-- `dyadicDelta n / dyadicDelta m = dyadicDelta (n - m)`. -/
lemma dyadicDelta_ratio (n m : ℕ) (hnm : m ≤ n) :
    dyadicDelta n / dyadicDelta m = dyadicDelta (n - m) := by
  let k := n - m
  have h1 : n = k + m := by omega
  have h_pos : 0 < dyadicDelta m := dyadicDelta_pos m
  have h2 : dyadicDelta n = dyadicDelta k * dyadicDelta m := by
    rw [h1]
    have h_pos2 : (0 : ℝ) < 2 := by norm_num
    simp only [dyadicDelta]
    have h3 : -((k + m : ℕ) : ℝ) = -((k : ℕ) : ℝ) + -(m : ℝ) := by
      simp [add_assoc] <;> ring_nf <;> norm_cast <;> omega
    rw [h3]
    have h4 : Real.rpow 2 (-((k : ℕ) : ℝ) + -(m : ℝ)) =
        Real.rpow 2 (-((k : ℕ) : ℝ)) * Real.rpow 2 (-(m : ℝ)) :=
      Real.rpow_add h_pos2 (-((k : ℕ) : ℝ)) (-(m : ℝ))
    exact h4
  rw [h2]
  field_simp [h_pos.ne'] <;> ring

/-- If `squareContained hnm p Q`, the homothety image has non-negative coordinates. -/
lemma squareHomothety_nonneg {n m : ℕ} {hnm : m ≤ n}
    {p : DyadicSquare n} {Q : DyadicSquare m}
    (h : squareContained hnm p Q) :
    0 ≤ (squareHomothety hnm Q p).i ∧ 0 ≤ (squareHomothety hnm Q p).j := by
  let R := coarseRefinementFactor n m
  have hi : (Q.i : ℤ) * R ≤ p.i := h.1
  have hj : (Q.j : ℤ) * R ≤ p.j := h.2.2.1
  have hR_pos : 0 < R := coarseRefinementFactor_pos n m
  constructor
  · dsimp only [squareHomothety]
    exact sub_nonneg.mpr hi
  · dsimp only [squareHomothety]
    exact sub_nonneg.mpr hj

/-- If `squareContained hnm p Q`, the homothety image coordinates are strictly
less than the refinement factor. -/
lemma squareHomothety_lt_refinement {n m : ℕ} {hnm : m ≤ n}
    {p : DyadicSquare n} {Q : DyadicSquare m}
    (h : squareContained hnm p Q) :
    (squareHomothety hnm Q p).i < coarseRefinementFactor n m ∧
    (squareHomothety hnm Q p).j < coarseRefinementFactor n m := by
  let R := coarseRefinementFactor n m
  have hi1 : (Q.i : ℤ) * R ≤ p.i := h.1
  have hi2 : p.i < (Q.i + 1) * R := h.2.1
  have hj1 : (Q.j : ℤ) * R ≤ p.j := h.2.2.1
  have hj2 : p.j < (Q.j + 1) * R := h.2.2.2
  have hR_pos : 0 < R := coarseRefinementFactor_pos n m
  constructor
  · dsimp only [squareHomothety]
    have h : p.i - Q.i * R < R := by
      have h : p.i - Q.i * R < R := by linarith
      exact h
    exact h
  · dsimp only [squareHomothety]
    have h : p.j - Q.j * R < R := by
      have h : p.j - Q.j * R < R := by linarith
      exact h
    exact h

/-- The image square's `toSet` is contained in the unit square. -/
lemma squareHomothety_toSet_subset_unitSquare {n m : ℕ} {hnm : m ≤ n}
    {p : DyadicSquare n} {Q : DyadicSquare m}
    (h : squareContained hnm p Q) :
    (squareHomothety hnm Q p).toSet ⊆ unitSquare := by
  let q := squareHomothety hnm Q p
  let R := coarseRefinementFactor n m
  have h_i1 : 0 ≤ (q.i : ℝ) := by exact_mod_cast (squareHomothety_nonneg h).1
  have h_i2 : (q.i : ℝ) < (R : ℝ) := by exact_mod_cast (squareHomothety_lt_refinement h).1
  have h_j1 : 0 ≤ (q.j : ℝ) := by exact_mod_cast (squareHomothety_nonneg h).2
  have h_j2 : (q.j : ℝ) < (R : ℝ) := by exact_mod_cast (squareHomothety_lt_refinement h).2
  have hδ'_pos : 0 < dyadicDelta (n - m) := dyadicDelta_pos (n - m)
  have hR1 : (R : ℝ) * dyadicDelta (n - m) = 1 := by
    have h : (R : ℝ) = Real.rpow 2 ((n - m : ℕ) : ℝ) := by
      simp [R, coarseRefinementFactor] <;> norm_cast
    rw [h]
    have h2 : Real.rpow 2 ((n - m : ℕ) : ℝ) * Real.rpow 2 (-((n - m : ℕ) : ℝ)) = 1 := by
      have h_pos : (0 : ℝ) < 2 := by norm_num
      have h3 : Real.rpow 2 ((n - m : ℕ) : ℝ) * Real.rpow 2 (-((n - m : ℕ) : ℝ)) =
          Real.rpow 2 (((n - m : ℕ) : ℝ) + -((n - m : ℕ) : ℝ)) :=
        (Real.rpow_add h_pos ((n - m : ℕ) : ℝ) (-((n - m : ℕ) : ℝ))).symm
      rw [h3]
      have h4 : ((n - m : ℕ) : ℝ) + -((n - m : ℕ) : ℝ) = 0 := by ring
      rw [h4] <;> norm_num
    simpa [dyadicDelta] using h2
  have h_i3 : (q.i + 1 : ℝ) ≤ (R : ℝ) := by
    have h9 : q.i < R := (squareHomothety_lt_refinement h).1
    have h10 : q.i + 1 ≤ R := by
      exact Int.add_one_le_of_lt h9
    exact_mod_cast h10
  have h_j3 : (q.j + 1 : ℝ) ≤ (R : ℝ) := by
    have h9 : q.j < R := (squareHomothety_lt_refinement h).2
    have h10 : q.j + 1 ≤ R := by
      exact Int.add_one_le_of_lt h9
    exact_mod_cast h10
  intro x hx
  simp only [DyadicSquare.toSet, Set.mem_prod] at hx ⊢
  constructor
  · constructor
    · exact mul_nonneg h_i1 (le_of_lt hδ'_pos) |>.trans hx.1.1
    · calc x.1 < ((q.i + 1 : ℝ)) * dyadicDelta (n - m) := hx.1.2
        _ ≤ (R : ℝ) * dyadicDelta (n - m) := by gcongr
        _ = 1 := hR1
  · constructor
    · exact mul_nonneg h_j1 (le_of_lt hδ'_pos) |>.trans hx.2.1
    · calc x.2 < ((q.j + 1 : ℝ)) * dyadicDelta (n - m) := hx.2.2
        _ ≤ (R : ℝ) * dyadicDelta (n - m) := by gcongr
        _ = 1 := hR1

/-- `containingSquare hnm p` is indeed a containing coarse square. -/
lemma containingSquare_squareContained {n m : ℕ} (hnm : m ≤ n) (p : DyadicSquare n) :
    squareContained hnm p (containingSquare hnm p) := by
  set Q : DyadicSquare m := containingSquare hnm p with hQ
  set R : ℝ := (coarseRefinementFactor n m : ℝ) with hR
  have hR_pos : 0 < R := by
    rw [hR]
    have h : 0 < (coarseRefinementFactor n m : ℝ) := by exact_mod_cast coarseRefinementFactor_pos n m
    exact h
  have h_i1 : (Q.i : ℝ) ≤ (p.i : ℝ) / R := Int.floor_le _
  have h_i2 : (p.i : ℝ) / R < (Q.i : ℝ) + 1 := Int.lt_floor_add_one _
  have h_i3 : (Q.i : ℝ) * R ≤ (p.i : ℝ) := by
    calc (Q.i : ℝ) * R ≤ ((p.i : ℝ) / R) * R := by gcongr
      _ = (p.i : ℝ) := by field_simp [hR_pos.ne'] <;> ring
  have h_i4 : (p.i : ℝ) < ((Q.i : ℝ) + 1) * R := by
    calc (p.i : ℝ) = ((p.i : ℝ) / R) * R := by field_simp [hR_pos.ne'] <;> ring
      _ < ((Q.i : ℝ) + 1) * R := by gcongr
  have h_j1 : (Q.j : ℝ) ≤ (p.j : ℝ) / R := Int.floor_le _
  have h_j2 : (p.j : ℝ) / R < (Q.j : ℝ) + 1 := Int.lt_floor_add_one _
  have h_j3 : (Q.j : ℝ) * R ≤ (p.j : ℝ) := by
    calc (Q.j : ℝ) * R ≤ ((p.j : ℝ) / R) * R := by gcongr
      _ = (p.j : ℝ) := by field_simp [hR_pos.ne'] <;> ring
  have h_j4 : (p.j : ℝ) < ((Q.j : ℝ) + 1) * R := by
    calc (p.j : ℝ) = ((p.j : ℝ) / R) * R := by field_simp [hR_pos.ne'] <;> ring
      _ < ((Q.j : ℝ) + 1) * R := by gcongr
  have h_goal1 : Q.i * coarseRefinementFactor n m ≤ p.i := by
    have h : (Q.i : ℝ) * (coarseRefinementFactor n m : ℝ) ≤ (p.i : ℝ) := by
      rw [←hR] <;> exact h_i3
    exact_mod_cast h
  have h_goal2 : p.i < (Q.i + 1) * coarseRefinementFactor n m := by
    have h : (p.i : ℝ) < ((Q.i + 1 : ℝ)) * (coarseRefinementFactor n m : ℝ) := by
      rw [←hR] <;> exact h_i4
    exact_mod_cast h
  have h_goal3 : Q.j * coarseRefinementFactor n m ≤ p.j := by
    have h : (Q.j : ℝ) * (coarseRefinementFactor n m : ℝ) ≤ (p.j : ℝ) := by
      rw [←hR] <;> exact h_j3
    exact_mod_cast h
  have h_goal4 : p.j < (Q.j + 1) * coarseRefinementFactor n m := by
    have h : (p.j : ℝ) < ((Q.j + 1 : ℝ)) * (coarseRefinementFactor n m : ℝ) := by
      rw [←hR] <;> exact h_j4
    exact_mod_cast h
  exact ⟨h_goal1, h_goal2, h_goal3, h_goal4⟩

/-- The geometric homothety `S_Q` mapping `Q` to `[0,1)^2`. -/
def homothetyS_Q (m : ℕ) (Q : DyadicSquare m) (x : InductionPlane) : InductionPlane :=
  let Δ := dyadicDelta m
  ((x.1 - (Q.i : ℝ) * Δ) / Δ, (x.2 - (Q.j : ℝ) * Δ) / Δ)

/-- Key scalar identity: `(a - Qi * R) * δ' = (a * δ - Qi * Δ) / Δ`. -/
lemma homothety_scalar_identity (n m : ℕ) (hnm : m ≤ n) (a : ℝ) (Qi : ℤ) :
    (a - (Qi : ℝ) * (coarseRefinementFactor n m : ℝ)) * dyadicDelta (n - m) =
    (a * dyadicDelta n - (Qi : ℝ) * dyadicDelta m) / dyadicDelta m := by
  let R := (coarseRefinementFactor n m : ℝ)
  let δ := dyadicDelta n
  let Δ := dyadicDelta m
  let δ' := dyadicDelta (n - m)
  have hRδ : R * δ = Δ := dyadicDelta_mul_refinement n m hnm
  have hδ : δ = δ' * Δ := by
    have h : δ' * Δ = δ := by
      calc δ' * Δ
        = δ / Δ * Δ := by rw [dyadicDelta_ratio n m hnm]
      _ = δ := by
        have hΔ_pos : 0 < Δ := dyadicDelta_pos m
        field_simp [hΔ_pos.ne'] <;> ring
    exact h.symm
  have hΔ_pos : 0 < Δ := dyadicDelta_pos m
  calc (a - (Qi : ℝ) * R) * δ'
    = a * δ' - (Qi : ℝ) * R * δ' := by ring
  _ = a * (δ / Δ) - (Qi : ℝ) * R * (δ / Δ) := by rw [dyadicDelta_ratio n m hnm]
  _ = (a * δ - (Qi : ℝ) * R * δ) / Δ := by field_simp [hΔ_pos.ne'] <;> ring
  _ = (a * δ - (Qi : ℝ) * (R * δ)) / Δ := by ring_nf
  _ = (a * δ - (Qi : ℝ) * Δ) / Δ := by rw [hRδ]

/-- The image of `p.toSet` under `S_Q` equals `(squareHomothety hnm Q p).toSet`. -/
lemma squareHomothety_toSet_eq_image {n m : ℕ} (hnm : m ≤ n)
    (p : DyadicSquare n) (Q : DyadicSquare m) :
    homothetyS_Q m Q '' p.toSet = (squareHomothety hnm Q p).toSet := by
  let q := squareHomothety hnm Q p
  let δ := dyadicDelta n
  let Δ := dyadicDelta m
  let δ' := dyadicDelta (n - m)
  have hqi : (q.i : ℝ) = (p.i : ℝ) - (Q.i : ℝ) * (coarseRefinementFactor n m : ℝ) := by
    simp [q, squareHomothety] <;> norm_cast
  have hqj : (q.j : ℝ) = (p.j : ℝ) - (Q.j : ℝ) * (coarseRefinementFactor n m : ℝ) := by
    simp [q, squareHomothety] <;> norm_cast
  have hΔ_pos : 0 < Δ := dyadicDelta_pos m
  ext ⟨x', y'⟩
  simp only [Set.mem_image, DyadicSquare.toSet, Set.mem_prod, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, h_eq⟩
    have h_x' : (x.1 - (Q.i : ℝ) * Δ) / Δ = x' := by
      injection h_eq with h1 _ <;> exact h1.symm
    have h_y' : (x.2 - (Q.j : ℝ) * Δ) / Δ = y' := by
      injection h_eq with _ h2 <;> exact h2.symm
    have h1 : (q.i : ℝ) * δ' ≤ x' := by
      have h_id : (q.i : ℝ) * δ' = ((p.i : ℝ) * δ - (Q.i : ℝ) * Δ) / Δ := by
        rw [hqi]
        exact homothety_scalar_identity n m hnm (p.i : ℝ) Q.i
      rw [h_id]
      rw [←h_x']
      gcongr
      <;> exact hx.1.1
    have h2 : x' < ((q.i + 1 : ℝ)) * δ' := by
      have hqi1 : (q.i + 1 : ℝ) = (p.i + 1 : ℝ) - (Q.i : ℝ) * (coarseRefinementFactor n m : ℝ) := by
        rw [hqi] <;> ring
      have h_id : ((q.i + 1 : ℝ)) * δ' = (((p.i + 1 : ℝ)) * δ - (Q.i : ℝ) * Δ) / Δ := by
        rw [hqi1]
        exact homothety_scalar_identity n m hnm (p.i + 1 : ℝ) Q.i
      rw [h_id]
      rw [←h_x']
      gcongr
      <;> exact hx.1.2
    have h3 : (q.j : ℝ) * δ' ≤ y' := by
      have h_id : (q.j : ℝ) * δ' = ((p.j : ℝ) * δ - (Q.j : ℝ) * Δ) / Δ := by
        rw [hqj]
        exact homothety_scalar_identity n m hnm (p.j : ℝ) Q.j
      rw [h_id]
      rw [←h_y']
      gcongr
      <;> exact hx.2.1
    have h4 : y' < ((q.j + 1 : ℝ)) * δ' := by
      have hqj1 : (q.j + 1 : ℝ) = (p.j + 1 : ℝ) - (Q.j : ℝ) * (coarseRefinementFactor n m : ℝ) := by
        rw [hqj] <;> ring
      have h_id : ((q.j + 1 : ℝ)) * δ' = (((p.j + 1 : ℝ)) * δ - (Q.j : ℝ) * Δ) / Δ := by
        rw [hqj1]
        exact homothety_scalar_identity n m hnm (p.j + 1 : ℝ) Q.j
      rw [h_id]
      rw [←h_y']
      gcongr
      <;> exact hx.2.2
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  · rintro ⟨hx', hy'⟩
    let x : InductionPlane := (x' * Δ + (Q.i : ℝ) * Δ, y' * Δ + (Q.j : ℝ) * Δ)
    have hx1 : (p.i : ℝ) * δ ≤ x.1 := by
      have h_id : (q.i : ℝ) * δ' = ((p.i : ℝ) * δ - (Q.i : ℝ) * Δ) / Δ := by
        rw [hqi] <;> exact homothety_scalar_identity n m hnm (p.i : ℝ) Q.i
      have h : (q.i : ℝ) * δ' ≤ x' := hx'.1
      have h2 : ((p.i : ℝ) * δ - (Q.i : ℝ) * Δ) / Δ ≤ x' := by
        rw [←h_id] <;> exact h
      have h3 : (p.i : ℝ) * δ - (Q.i : ℝ) * Δ ≤ x' * Δ := by
        calc (p.i : ℝ) * δ - (Q.i : ℝ) * Δ
          = (((p.i : ℝ) * δ - (Q.i : ℝ) * Δ) / Δ) * Δ := by field_simp [hΔ_pos.ne'] <;> ring
        _ ≤ x' * Δ := by gcongr
      have h4 : x.1 = x' * Δ + (Q.i : ℝ) * Δ := by rfl
      rw [h4]
      linarith
    have hx2 : x.1 < ((p.i + 1 : ℝ)) * δ := by
      have hqi1 : (q.i + 1 : ℝ) = (p.i + 1 : ℝ) - (Q.i : ℝ) * (coarseRefinementFactor n m : ℝ) := by
        rw [hqi] <;> ring
      have h_id : ((q.i + 1 : ℝ)) * δ' = (((p.i + 1 : ℝ)) * δ - (Q.i : ℝ) * Δ) / Δ := by
        rw [hqi1] <;> exact homothety_scalar_identity n m hnm (p.i + 1 : ℝ) Q.i
      have h : x' < ((q.i + 1 : ℝ)) * δ' := hx'.2
      have h2 : x' < (((p.i + 1 : ℝ)) * δ - (Q.i : ℝ) * Δ) / Δ := by
        rw [←h_id] <;> exact h
      have h3 : x' * Δ < ((p.i + 1 : ℝ)) * δ - (Q.i : ℝ) * Δ := by
        calc x' * Δ
          < ((((p.i + 1 : ℝ)) * δ - (Q.i : ℝ) * Δ) / Δ) * Δ := by gcongr
        _ = ((p.i + 1 : ℝ)) * δ - (Q.i : ℝ) * Δ := by field_simp [hΔ_pos.ne'] <;> ring
      have h4 : x.1 = x' * Δ + (Q.i : ℝ) * Δ := by rfl
      rw [h4]
      linarith
    have hy1 : (p.j : ℝ) * δ ≤ x.2 := by
      have h_id : (q.j : ℝ) * δ' = ((p.j : ℝ) * δ - (Q.j : ℝ) * Δ) / Δ := by
        rw [hqj] <;> exact homothety_scalar_identity n m hnm (p.j : ℝ) Q.j
      have h : (q.j : ℝ) * δ' ≤ y' := hy'.1
      have h2 : ((p.j : ℝ) * δ - (Q.j : ℝ) * Δ) / Δ ≤ y' := by
        rw [←h_id] <;> exact h
      have h3 : (p.j : ℝ) * δ - (Q.j : ℝ) * Δ ≤ y' * Δ := by
        calc (p.j : ℝ) * δ - (Q.j : ℝ) * Δ
          = (((p.j : ℝ) * δ - (Q.j : ℝ) * Δ) / Δ) * Δ := by field_simp [hΔ_pos.ne'] <;> ring
        _ ≤ y' * Δ := by gcongr
      have h4 : x.2 = y' * Δ + (Q.j : ℝ) * Δ := by rfl
      rw [h4]
      linarith
    have hy2 : x.2 < ((p.j + 1 : ℝ)) * δ := by
      have hqj1 : (q.j + 1 : ℝ) = (p.j + 1 : ℝ) - (Q.j : ℝ) * (coarseRefinementFactor n m : ℝ) := by
        rw [hqj] <;> ring
      have h_id : ((q.j + 1 : ℝ)) * δ' = (((p.j + 1 : ℝ)) * δ - (Q.j : ℝ) * Δ) / Δ := by
        rw [hqj1] <;> exact homothety_scalar_identity n m hnm (p.j + 1 : ℝ) Q.j
      have h : y' < ((q.j + 1 : ℝ)) * δ' := hy'.2
      have h2 : y' < (((p.j + 1 : ℝ)) * δ - (Q.j : ℝ) * Δ) / Δ := by
        rw [←h_id] <;> exact h
      have h3 : y' * Δ < ((p.j + 1 : ℝ)) * δ - (Q.j : ℝ) * Δ := by
        calc y' * Δ
          < ((((p.j + 1 : ℝ)) * δ - (Q.j : ℝ) * Δ) / Δ) * Δ := by gcongr
        _ = ((p.j + 1 : ℝ)) * δ - (Q.j : ℝ) * Δ := by field_simp [hΔ_pos.ne'] <;> ring
      have h4 : x.2 = y' * Δ + (Q.j : ℝ) * Δ := by rfl
      rw [h4]
      linarith
    refine ⟨x, ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩, ?_⟩
    have h_eq1 : (homothetyS_Q m Q x).1 = x' := by
      have h : (homothetyS_Q m Q x).1 = (x.1 - (Q.i : ℝ) * Δ) / Δ := by rfl
      rw [h]
      have hx_def : x.1 = x' * Δ + (Q.i : ℝ) * Δ := by rfl
      rw [hx_def]
      have h5 : (x' * Δ + (Q.i : ℝ) * Δ - (Q.i : ℝ) * Δ) / Δ = x' := by
        have h6 : x' * Δ + (Q.i : ℝ) * Δ - (Q.i : ℝ) * Δ = x' * Δ := by ring
        rw [h6]
        field_simp [hΔ_pos.ne'] <;> ring
      exact h5
    have h_eq2 : (homothetyS_Q m Q x).2 = y' := by
      have h : (homothetyS_Q m Q x).2 = (x.2 - (Q.j : ℝ) * Δ) / Δ := by rfl
      rw [h]
      have hy_def : x.2 = y' * Δ + (Q.j : ℝ) * Δ := by rfl
      rw [hy_def]
      have h5 : (y' * Δ + (Q.j : ℝ) * Δ - (Q.j : ℝ) * Δ) / Δ = y' := by
        have h6 : y' * Δ + (Q.j : ℝ) * Δ - (Q.j : ℝ) * Δ = y' * Δ := by ring
        rw [h6]
        field_simp [hΔ_pos.ne'] <;> ring
      exact h5
    exact Prod.ext h_eq1 h_eq2

/-- Homothety preserves slopes. -/
lemma homothety_preserves_slope (m : ℕ) (Q : DyadicSquare m)
    (slope intercept : ℝ) (x : InductionPlane)
    (h : x.2 = slope * x.1 + intercept) :
    (homothetyS_Q m Q x).2 = slope * (homothetyS_Q m Q x).1 +
      (slope * (Q.i : ℝ) * dyadicDelta m + intercept - (Q.j : ℝ) * dyadicDelta m) /
        dyadicDelta m := by
  let Δ := dyadicDelta m
  have hΔ_pos : 0 < Δ := dyadicDelta_pos m
  simp only [homothetyS_Q]
  have h1 : x.2 = slope * x.1 + intercept := h
  have h_goal : (x.2 - (Q.j : ℝ) * Δ) / Δ =
      slope * ((x.1 - (Q.i : ℝ) * Δ) / Δ) +
      (slope * (Q.i : ℝ) * Δ + intercept - (Q.j : ℝ) * Δ) / Δ := by
    have h_rhs : slope * ((x.1 - (Q.i : ℝ) * Δ) / Δ) + (slope * (Q.i : ℝ) * Δ + intercept - (Q.j : ℝ) * Δ) / Δ =
        (slope * x.1 + intercept - (Q.j : ℝ) * Δ) / Δ := by
      field_simp [hΔ_pos.ne'] <;> ring
    rw [h_rhs]
    have h_lhs : (x.2 - (Q.j : ℝ) * Δ) / Δ = (slope * x.1 + intercept - (Q.j : ℝ) * Δ) / Δ := by
      rw [h1]
    exact h_lhs
  exact h_goal

/-- The local slope cell index correctly captures the slope at scale `n - m`. -/
lemma localSlopeCellIndex_correct (n m : ℕ) (hnm : m ≤ n) (T : DyadicTube n) :
    (localSlopeCellIndex m T.a : ℝ) * dyadicDelta (n - m) ≤ T.slope ∧
    T.slope < ((localSlopeCellIndex m T.a + 1 : ℝ)) * dyadicDelta (n - m) := by
  let k := localSlopeCellIndex m T.a
  let two_m := ((2 ^ m : ℕ) : ℝ)
  let δ' := dyadicDelta (n - m)
  have h_two_m_pos : 0 < two_m := by positivity
  have h_δ'_pos : 0 < δ' := dyadicDelta_pos (n - m)
  have h_floor1 : (k : ℝ) ≤ (T.a : ℝ) / two_m := Int.floor_le _
  have h_floor2 : (T.a : ℝ) / two_m < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have hδ : dyadicDelta n = δ' / two_m := by
    dsimp only [δ', two_m, dyadicDelta]
    have h_two_m : ((2 ^ m : ℕ) : ℝ) = Real.rpow 2 (m : ℝ) := by simp
    have h_pos : (0 : ℝ) < 2 := by norm_num
    have h_rpow_pos : 0 < Real.rpow 2 (m : ℝ) := Real.rpow_pos_of_pos h_pos _
    have h_ne_zero : Real.rpow 2 (m : ℝ) ≠ 0 := h_rpow_pos.ne'
    have h_eq : Real.rpow 2 (-((n - m : ℕ) : ℝ)) =
        Real.rpow 2 (-((n - m : ℕ) : ℝ) - (m : ℝ)) * Real.rpow 2 (m : ℝ) := by
      have h_add := Real.rpow_add h_pos (-((n - m : ℕ) : ℝ) - (m : ℝ)) (m : ℝ)
      have h_simp : (-((n - m : ℕ) : ℝ) - (m : ℝ)) + (m : ℝ) = -((n - m : ℕ) : ℝ) := by ring
      rw [h_simp] at h_add
      exact h_add
    have h_main : Real.rpow 2 (-((n - m : ℕ) : ℝ)) / Real.rpow 2 (m : ℝ) =
        Real.rpow 2 (-((n - m : ℕ) : ℝ) - (m : ℝ)) := by
      exact (eq_div_iff h_ne_zero).mpr h_eq.symm |>.symm
    rw [h_two_m]
    have h2 : -((n - m : ℕ) : ℝ) - (m : ℝ) = -(n : ℝ) := by
      have h3 : (n : ℝ) = ((n - m : ℕ) : ℝ) + (m : ℝ) := by exact_mod_cast (by omega)
      linarith
    have h_goal : Real.rpow 2 (-(n : ℝ)) = Real.rpow 2 (-((n - m : ℕ) : ℝ)) / Real.rpow 2 (m : ℝ) := by
      rw [h_main, h2]
    exact h_goal
  have h_slope : T.slope = (T.a : ℝ) * dyadicDelta n := by rfl
  have h_slope2 : T.slope = ((T.a : ℝ) / two_m) * δ' := by
    rw [h_slope, hδ] <;> ring
  constructor
  · rw [h_slope2]
    exact mul_le_mul_of_nonneg_right h_floor1 (le_of_lt h_δ'_pos)
  · rw [h_slope2]
    exact mul_lt_mul_of_pos_right h_floor2 h_δ'_pos

/-- `squareHomothety` is injective in `p` for fixed `Q`. -/
lemma squareHomothety_injective {n m : ℕ} {hnm : m ≤ n} (Q : DyadicSquare m) :
    Function.Injective (fun (p : DyadicSquare n) => squareHomothety hnm Q p) := by
  intro p1 p2 h
  have hi : (squareHomothety hnm Q p1).i = (squareHomothety hnm Q p2).i := by
    exact congr_arg (fun (s : DyadicSquare (n - m)) => s.i) h
  have hj : (squareHomothety hnm Q p1).j = (squareHomothety hnm Q p2).j := by
    exact congr_arg (fun (s : DyadicSquare (n - m)) => s.j) h
  have hpi : p1.i = p2.i := by simpa [squareHomothety] using hi
  have hpj : p1.j = p2.j := by simpa [squareHomothety] using hj
  cases p1; cases p2; simp_all

/-- If `squareContained hnm p Q`, then `p.toSet ⊆ Q.toSet`. -/
lemma squareContained_toSet_subset {n m : ℕ} {hnm : m ≤ n}
    {p : DyadicSquare n} {Q : DyadicSquare m}
    (h : squareContained hnm p Q) : p.toSet ⊆ Q.toSet := by
  set R : ℝ := (coarseRefinementFactor n m : ℝ) with hR
  set δ : ℝ := dyadicDelta n with hδ
  set Δ : ℝ := dyadicDelta m with hΔ
  have hRδ : R * δ = Δ := by
    simpa [hR, hδ, hΔ] using dyadicDelta_mul_refinement n m hnm
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have h_i1 : (Q.i : ℝ) * R ≤ (p.i : ℝ) := by
    have h2 : Q.i * coarseRefinementFactor n m ≤ p.i := h.1
    have h3 : (Q.i : ℝ) * (coarseRefinementFactor n m : ℝ) ≤ (p.i : ℝ) := by exact_mod_cast h2
    simpa [hR] using h3
  have h_i2 : p.i + 1 ≤ (Q.i + 1) * coarseRefinementFactor n m := by
    have h2 : p.i < (Q.i + 1) * coarseRefinementFactor n m := h.2.1
    exact Int.add_one_le_of_lt h2
  have h_i2' : (p.i + 1 : ℝ) ≤ ((Q.i + 1 : ℝ)) * R := by
    have h2 : p.i + 1 ≤ (Q.i + 1) * coarseRefinementFactor n m := h_i2
    have h3 : (p.i + 1 : ℝ) ≤ ((Q.i + 1 : ℝ)) * (coarseRefinementFactor n m : ℝ) := by exact_mod_cast h2
    simpa [hR] using h3
  have h_j1 : (Q.j : ℝ) * R ≤ (p.j : ℝ) := by
    have h2 : Q.j * coarseRefinementFactor n m ≤ p.j := h.2.2.1
    have h3 : (Q.j : ℝ) * (coarseRefinementFactor n m : ℝ) ≤ (p.j : ℝ) := by exact_mod_cast h2
    simpa [hR] using h3
  have h_j2 : p.j + 1 ≤ (Q.j + 1) * coarseRefinementFactor n m := by
    have h2 : p.j < (Q.j + 1) * coarseRefinementFactor n m := h.2.2.2
    exact Int.add_one_le_of_lt h2
  have h_j2' : (p.j + 1 : ℝ) ≤ ((Q.j + 1 : ℝ)) * R := by
    have h2 : p.j + 1 ≤ (Q.j + 1) * coarseRefinementFactor n m := h_j2
    have h3 : (p.j + 1 : ℝ) ≤ ((Q.j + 1 : ℝ)) * (coarseRefinementFactor n m : ℝ) := by exact_mod_cast h2
    simpa [hR] using h3
  intro x hx
  simp only [DyadicSquare.toSet, Set.mem_prod] at hx ⊢
  have h_ix1 : (Q.i : ℝ) * Δ ≤ x.1 := by
    have h3 : (Q.i : ℝ) * Δ = ((Q.i : ℝ) * R) * δ := by
      calc (Q.i : ℝ) * Δ
        = (Q.i : ℝ) * (R * δ) := by rw [hRδ]
      _ = ((Q.i : ℝ) * R) * δ := by ring
    rw [h3]
    have h4 : ((Q.i : ℝ) * R) * δ ≤ (p.i : ℝ) * δ := by
      exact mul_le_mul_of_nonneg_right h_i1 (le_of_lt hδ_pos)
    exact h4.trans hx.1.1
  have h_ix2 : x.1 < ((Q.i + 1 : ℝ)) * Δ := by
    have h3 : ((Q.i + 1 : ℝ)) * Δ = (((Q.i + 1 : ℝ)) * R) * δ := by
      calc ((Q.i + 1 : ℝ)) * Δ
        = ((Q.i + 1 : ℝ)) * (R * δ) := by rw [hRδ]
      _ = (((Q.i + 1 : ℝ)) * R) * δ := by ring
    rw [h3]
    have h4 : (p.i + 1 : ℝ) * δ ≤ (((Q.i + 1 : ℝ)) * R) * δ := by
      exact mul_le_mul_of_nonneg_right h_i2' (le_of_lt hδ_pos)
    exact hx.1.2.trans_le h4
  have h_jx1 : (Q.j : ℝ) * Δ ≤ x.2 := by
    have h3 : (Q.j : ℝ) * Δ = ((Q.j : ℝ) * R) * δ := by
      calc (Q.j : ℝ) * Δ
        = (Q.j : ℝ) * (R * δ) := by rw [hRδ]
      _ = ((Q.j : ℝ) * R) * δ := by ring
    rw [h3]
    have h4 : ((Q.j : ℝ) * R) * δ ≤ (p.j : ℝ) * δ := by
      exact mul_le_mul_of_nonneg_right h_j1 (le_of_lt hδ_pos)
    exact h4.trans hx.2.1
  have h_jx2 : x.2 < ((Q.j + 1 : ℝ)) * Δ := by
    have h3 : ((Q.j + 1 : ℝ)) * Δ = (((Q.j + 1 : ℝ)) * R) * δ := by
      calc ((Q.j + 1 : ℝ)) * Δ
        = ((Q.j + 1 : ℝ)) * (R * δ) := by rw [hRδ]
      _ = (((Q.j + 1 : ℝ)) * R) * δ := by ring
    rw [h3]
    have h4 : (p.j + 1 : ℝ) * δ ≤ (((Q.j + 1 : ℝ)) * R) * δ := by
      exact mul_le_mul_of_nonneg_right h_j2' (le_of_lt hδ_pos)
    exact hx.2.2.trans_le h4
  exact ⟨⟨h_ix1, h_ix2⟩, ⟨h_jx1, h_jx2⟩⟩

/-- If a fine tube `T` intersects a fine square `p` contained in `Q`, then the
image of the intersection under `S_Q` is nonempty and lies in the image square. -/
lemma homothety_intersection_nonempty {n m : ℕ} {hnm : m ≤ n}
    {T : DyadicTube n} {p : DyadicSquare n} {Q : DyadicSquare m}
    (h_cont : squareContained hnm p Q)
    (h_inc : (T.toSet ∩ p.toSet).Nonempty) :
    ∃ (x : InductionPlane), x ∈ T.toSet ∧ x ∈ p.toSet ∧
      homothetyS_Q m Q x ∈ (squareHomothety hnm Q p).toSet := by
  rcases h_inc with ⟨x, hxT, hxp⟩
  refine ⟨x, hxT, hxp, ?_⟩
  have h : homothetyS_Q m Q x ∈ homothetyS_Q m Q '' p.toSet := ⟨x, hxp, rfl⟩
  rw [squareHomothety_toSet_eq_image hnm p Q] at h
  exact h

end

lemma InductionOnScales.homothety_scalar_identity (n m : ℕ) (hnm : m ≤ n) (a : ℝ) (Qi : ℤ) :
    (a - (Qi : ℝ) * (coarseRefinementFactor n m : ℝ)) * dyadicDelta (n - m) =
    (a * dyadicDelta n - (Qi : ℝ) * dyadicDelta m) / dyadicDelta m :=
  _root_.homothety_scalar_identity n m hnm a Qi
