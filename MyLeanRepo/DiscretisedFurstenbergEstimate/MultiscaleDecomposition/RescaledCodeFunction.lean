module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

namespace DirecretisedFurstenbergEstimate.MultiscaleDecomposition

/-- The partial code function shifts: if `N' k = N (a + k)`, then
    `codeFunctionPartialSum m' Δ N' j = codeFunctionPartialSum m Δ N (a + j) - codeFunctionPartialSum m Δ N a`. -/
lemma codeFunctionPartialSum_shift {m a j : ℕ} {Δ : ℝ} {N : ℕ → ℕ} :
    codeFunctionPartialSum m Δ (fun k : ℕ => N (a + k)) j =
    codeFunctionPartialSum m Δ N (a + j) - codeFunctionPartialSum m Δ N a := by
  dsimp only [codeFunctionPartialSum]
  have h : ∑ i ∈ Finset.range (a + j), Real.log (N i) / Real.log (1 / Δ) =
      (∑ i ∈ Finset.range a, Real.log (N i) / Real.log (1 / Δ)) +
      ∑ i ∈ Finset.range j, Real.log (N (a + i)) / Real.log (1 / Δ) := by
    rw [Finset.sum_range_add]
    <;> rfl
  linarith

/-- `codeFunctionPartialSum m Δ N 0 = 0`. -/
lemma codeFunctionPartialSum_zero {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ} :
    codeFunctionPartialSum m Δ N 0 = 0 := by
  simp [codeFunctionPartialSum]

/-- `codeFunction m Δ N 0 = 0`. -/
lemma codeFunction_zero {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ} :
    codeFunction m Δ N 0 = 0 := by
  rw [codeFunction]
  <;> simp

/-- `codeFunction m Δ N (j : ℝ) = codeFunctionPartialSum m Δ N j` for `0 < j < m`. -/
lemma codeFunction_nat {m j : ℕ} {Δ : ℝ} {N : ℕ → ℕ} (h1 : 0 < j) (h2 : j < m) :
    codeFunction m Δ N (j : ℝ) = codeFunctionPartialSum m Δ N j := by
  rw [codeFunction]
  have h_pos : ¬(j : ℝ) ≤ 0 := by
    have h : (j : ℝ) > 0 := by exact_mod_cast h1
    linarith
  have h_lt : ¬(m : ℝ) ≤ (j : ℝ) := by
    have h : (j : ℝ) < (m : ℝ) := by exact_mod_cast h2
    linarith
  rw [if_neg h_pos, if_neg h_lt]
  have h_floor : ⌊(j : ℝ)⌋₊ = j := by simp
  rw [h_floor]
  <;> simp

/-- `codeFunction m Δ N (j : ℝ) = codeFunctionPartialSum m Δ N j` for `0 ≤ j ≤ m`. -/
lemma codeFunction_nat_le {m j : ℕ} {Δ : ℝ} {N : ℕ → ℕ} (h : j ≤ m) :
    codeFunction m Δ N (j : ℝ) = codeFunctionPartialSum m Δ N j := by
  by_cases h0 : j = 0
  · subst h0
    simp [codeFunction, codeFunctionPartialSum]
    <;> norm_num
  · have hpos : 0 < j := Nat.pos_of_ne_zero h0
    by_cases hlt : j < m
    · exact codeFunction_nat hpos hlt
    · have heq : j = m := by omega
      rw [heq]
      rw [codeFunction]
      have h1 : ¬(m : ℝ) ≤ 0 := by
        have h2 : 0 < m := by
          have h3 : 0 < j := hpos
          omega
        have h4 : (m : ℝ) > 0 := by exact_mod_cast h2
        linarith
      simp [h1]
      <;> norm_num

/-- For `0 ≤ x < m`, `codeFunction` is linear interpolation between partial sums. -/
lemma codeFunction_interp {m : ℕ} {Δ : ℝ} {N : ℕ → ℕ} {x : ℝ} (hx1 : 0 ≤ x) (hx2 : x < (m : ℝ)) :
    codeFunction m Δ N x =
      codeFunctionPartialSum m Δ N ⌊x⌋₊ + (x - ⌊x⌋₊ : ℝ) *
        (codeFunctionPartialSum m Δ N (⌊x⌋₊ + 1) - codeFunctionPartialSum m Δ N ⌊x⌋₊) := by
  by_cases hx0 : x = 0
  · subst hx0
    simp [codeFunction, codeFunctionPartialSum]
    <;> norm_num
  · have hx_pos : 0 < x := by exact lt_of_le_of_ne hx1 (Ne.symm hx0)
    rw [codeFunction]
    have h1 : ¬x ≤ 0 := by linarith
    have h2 : ¬(m : ℝ) ≤ x := by linarith
    rw [if_neg h1, if_neg h2]
    <;> rfl

/-- `⌊(a : ℝ) + x⌋₊ = a + ⌊x⌋₊` for `a : ℕ`, `0 ≤ x`. -/
lemma floor_add_nat {a : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    ⌊(a : ℝ) + x⌋₊ = a + ⌊x⌋₊ := by
  have h1 : ((a + ⌊x⌋₊ : ℕ) : ℝ) ≤ (a : ℝ) + x := by
    have h2 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
    simp [h2] <;> linarith
  have h3 : (a : ℝ) + x < ((a + ⌊x⌋₊ : ℕ) + 1 : ℝ) := by
    have h4 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    simp [h4] <;> linarith
  have h5 : 0 ≤ (a : ℝ) + x := by linarith
  rw [Nat.floor_eq_iff h5]
  exact ⟨h1, h3⟩

/-- The code function of a rescaled uniform set: if `N' k = N (a + k)` and `a + m' ≤ m`,
    then `codeFunction m' Δ N' x = codeFunction m Δ N (a + x) - codeFunction m Δ N a`
    for all `x ∈ [0, m']`. -/
lemma rescaled_codeFunction {m m' a : ℕ} {Δ : ℝ} {N : ℕ → ℕ}
    (h : a + m' ≤ m) (hm'_pos : 0 < m') (x : ℝ) (hx1 : 0 ≤ x) (hx2 : x ≤ (m' : ℝ)) :
    codeFunction m' Δ (fun k : ℕ => N (a + k)) x =
    codeFunction m Δ N (a + x) - codeFunction m Δ N a := by
  set N' : ℕ → ℕ := fun k : ℕ => N (a + k) with hN'
  have h_partial : ∀ (j : ℕ), codeFunctionPartialSum m' Δ N' j =
      codeFunctionPartialSum m Δ N (a + j) - codeFunctionPartialSum m Δ N a := by
    intro j
    exact codeFunctionPartialSum_shift (m := m) (a := a) (j := j)
  have h_a_code : codeFunction m Δ N (a : ℝ) = codeFunctionPartialSum m Δ N a :=
    codeFunction_nat_le (by omega)
  by_cases hx0 : x = 0
  · -- x = 0
    subst hx0
    have h_goal : codeFunction m' Δ N' 0 = 0 := codeFunction_zero
    rw [h_goal]
    have h8 : codeFunction m Δ N (↑a + 0) = codeFunction m Δ N ↑a := by
      have h9 : (↑a + 0 : ℝ) = (↑a : ℝ) := by ring
      rw [h9]
    rw [h8]
    <;> rw [h_a_code]
    <;> ring
  · -- x > 0
    have hx_pos : 0 < x := by exact lt_of_le_of_ne hx1 (Ne.symm hx0)
    by_cases hx_top : x ≥ (m' : ℝ)
    · -- x = m'
      have h_x_eq : x = (m' : ℝ) := by linarith
      subst h_x_eq
      have h_am'_le_m : a + m' ≤ m := h
      have h_am'_code : codeFunction m Δ N ((a + m' : ℕ) : ℝ) = codeFunctionPartialSum m Δ N (a + m') :=
        codeFunction_nat_le h_am'_le_m
      have h_m'_code : codeFunction m' Δ N' (m' : ℝ) = codeFunctionPartialSum m' Δ N' m' :=
        codeFunction_nat_le (by linarith)
      have h_goal : codeFunctionPartialSum m' Δ N' m' =
          codeFunctionPartialSum m Δ N (a + m') - codeFunctionPartialSum m Δ N a :=
        h_partial m'
      have h_cast : (↑a + ↑m' : ℝ) = ↑(a + m') := by
        simp [Nat.cast_add] <;> ring
      rw [h_cast, h_m'_code, h_am'_code, h_a_code]
      <;> exact h_goal
    · -- 0 < x < m'
      have hx_lt : x < (m' : ℝ) := by linarith
      have h_ax_lt : (a : ℝ) + x < (m : ℝ) := by
        have h1 : (a : ℝ) + x < (a : ℝ) + (m' : ℝ) := by gcongr
        have h2 : (a : ℝ) + (m' : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
        linarith
      let j : ℕ := ⌊x⌋₊
      have h_j_lt_m' : j < m' := by
        have h1 : (j : ℝ) < (m' : ℝ) := by
          have h2 : (j : ℝ) ≤ x := Nat.floor_le hx1
          linarith
        exact_mod_cast h1
      have h_floor_add : ⌊(a : ℝ) + x⌋₊ = a + j := floor_add_nat hx1
      have h_main1 : codeFunction m' Δ N' x =
          codeFunctionPartialSum m' Δ N' j + (x - (j : ℝ)) *
            (codeFunctionPartialSum m' Δ N' (j + 1) - codeFunctionPartialSum m' Δ N' j) :=
        codeFunction_interp hx1 hx_lt
      have h_main2 : codeFunction m Δ N ((a : ℝ) + x) =
          codeFunctionPartialSum m Δ N (a + j) + (x - (j : ℝ)) *
            (codeFunctionPartialSum m Δ N (a + j + 1) - codeFunctionPartialSum m Δ N (a + j)) := by
        have h := codeFunction_interp (Δ := Δ) (N := N) (by linarith) h_ax_lt
        rw [h_floor_add] at h
        have h_cast2 : (↑a + x - ↑(a + j) : ℝ) = (x - ↑j : ℝ) := by
          simp [Nat.cast_add] <;> ring
        rw [h_cast2] at h
        exact h
      rw [h_main1, h_main2]
      rw [h_a_code, h_partial j, h_partial (j + 1)]
      <;> ring_nf

end DirecretisedFurstenbergEstimate.MultiscaleDecomposition
