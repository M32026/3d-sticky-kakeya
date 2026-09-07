import MyLeanRepo.Kakeya.Cinematic.Section5.GlobalizationInputs

/-!
# Helper lemmas for centered-sixteenth interval cover

Reusable building blocks for the geometric tiling construction used in
`centered_sixteenth_interval_cover`.
-/

namespace Kakeya.Cinematic

namespace CenteredCoverHelpers

open ParameterInterval Set

/-- Construct a `ParameterInterval` from explicit bounds. -/
def mkParameterInterval (left right : ℝ)
    (h0 : 0 ≤ left) (h1 : left ≤ right) (h2 : right ≤ 1) :
    ParameterInterval where
  left := left
  right := right
  left_mem := ⟨h0, by linarith⟩
  right_mem := ⟨by linarith, h2⟩
  left_le_right := h1

@[simp]
theorem mkParameterInterval_left (left right : ℝ) (h0 h1 h2) :
    (mkParameterInterval left right h0 h1 h2).left = left := by
  rfl

@[simp]
theorem mkParameterInterval_right (left right : ℝ) (h0 h1 h2) :
    (mkParameterInterval left right h0 h1 h2).right = right := by
  rfl

/-- The geometric sequence of interval lengths. -/
noncomputable def geomLength (rho : ℝ) (n : ℕ) : ℝ :=
  4 * rho * (17 / 15 : ℝ) ^ n

theorem geomLength_succ (rho : ℝ) (n : ℕ) :
    geomLength rho (n + 1) = (17 / 15 : ℝ) * geomLength rho n := by
  simp [geomLength, pow_succ]
  ring

/-- Tiling identity: right endpoint of sixteenth of L(n) equals
left endpoint of sixteenth of L(n+1). -/
theorem sixteenth_tiling (rho : ℝ) (n : ℕ) :
    17 * geomLength rho n / 32 = 15 * geomLength rho (n + 1) / 32 := by
  rw [geomLength_succ]
  ring

/--
Characterize the centered sixteenth of `[0, L]` as `Set.Icc (15*L/32) (17*L/32)`,
provided `0 ≤ L ≤ 1`.
-/
theorem left_interval_sixteenth (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1) :
    let I : ParameterInterval := mkParameterInterval 0 L (by norm_num) (by linarith) (by linarith)
    I.realCenteredCarrier (1 / 16) = Set.Icc (15 * L / 32) (17 * L / 32) := by
  let I : ParameterInterval := mkParameterInterval 0 L (by norm_num) (by linarith) (by linarith)
  have h_mid : I.midpoint = L / 2 := by
    simp [I, mkParameterInterval, ParameterInterval.midpoint]
    <;> ring
  have h_len : I.length = L := by
    simp [I, mkParameterInterval, ParameterInterval.length]
  have h_rad : (1 / 16 : ℝ) * I.length / 2 = L / 32 := by
    rw [h_len]
    ring
  ext x
  simp only [realCenteredCarrier, mem_setOf_eq, unitInterval, mem_Icc]
  constructor
  · rintro ⟨⟨hx0, hx1⟩, habs⟩
    rw [h_mid, h_rad] at habs
    have h' := abs_le.mp habs
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    have hx0 : 0 ≤ x := by linarith
    have hx1 : x ≤ 1 := by linarith
    have h : |x - L / 2| ≤ L / 32 := by
      rw [abs_le]
      constructor <;> linarith
    exact ⟨⟨hx0, hx1⟩, by
      rw [h_mid, h_rad]
      exact h⟩

/--
Characterize the centered sixteenth of `[1-L, 1]` as
`Set.Icc (1 - 17*L/32) (1 - 15*L/32)`, provided `0 ≤ L ≤ 1`.
-/
theorem right_interval_sixteenth (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1) :
    let I : ParameterInterval :=
      mkParameterInterval (1 - L) 1 (by linarith) (by linarith) (by norm_num)
    I.realCenteredCarrier (1 / 16) =
      Set.Icc (1 - 17 * L / 32) (1 - 15 * L / 32) := by
  let I : ParameterInterval :=
    mkParameterInterval (1 - L) 1 (by linarith) (by linarith) (by norm_num)
  have h_mid : I.midpoint = 1 - L / 2 := by
    simp [I, mkParameterInterval, ParameterInterval.midpoint]
    <;> ring
  have h_len : I.length = L := by
    simp [I, mkParameterInterval, ParameterInterval.length]
  have h_rad : (1 / 16 : ℝ) * I.length / 2 = L / 32 := by
    rw [h_len]
    ring
  ext x
  simp only [realCenteredCarrier, mem_setOf_eq, unitInterval, mem_Icc]
  constructor
  · rintro ⟨⟨hx0, hx1⟩, habs⟩
    rw [h_mid, h_rad] at habs
    have h' := abs_le.mp habs
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    have hx0 : 0 ≤ x := by linarith
    have hx1 : x ≤ 1 := by linarith
    have h : |x - (1 - L / 2)| ≤ L / 32 := by
      rw [abs_le]
      constructor <;> linarith
    exact ⟨⟨hx0, hx1⟩, by
      rw [h_mid, h_rad]
      exact h⟩

/--
Characterize the centered sixteenth of `[a, a+L]` as
`Set.Icc (a + 15*L/32) (a + 17*L/32)`, provided `0 ≤ a` and `a + L ≤ 1`.
-/
theorem middle_interval_sixteenth (a L : ℝ) (ha0 : 0 ≤ a) (haL : a + L ≤ 1)
    (hL0 : 0 ≤ L) :
    let I : ParameterInterval :=
      mkParameterInterval a (a + L) ha0 (by linarith) haL
    I.realCenteredCarrier (1 / 16) =
      Set.Icc (a + 15 * L / 32) (a + 17 * L / 32) := by
  let I : ParameterInterval :=
    mkParameterInterval a (a + L) ha0 (by linarith) haL
  have h_mid : I.midpoint = a + L / 2 := by
    simp [I, mkParameterInterval, ParameterInterval.midpoint]
    <;> ring
  have h_len : I.length = L := by
    simp [I, mkParameterInterval, ParameterInterval.length]
  have h_rad : (1 / 16 : ℝ) * I.length / 2 = L / 32 := by
    rw [h_len]
    ring
  ext x
  simp only [realCenteredCarrier, mem_setOf_eq, unitInterval, mem_Icc]
  constructor
  · rintro ⟨⟨hx0, hx1⟩, habs⟩
    rw [h_mid, h_rad] at habs
    have h' := abs_le.mp habs
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    have hx0 : 0 ≤ x := by linarith
    have hx1 : x ≤ 1 := by linarith
    have h : |x - (a + L / 2)| ≤ L / 32 := by
      rw [abs_le]
      constructor <;> linarith
    exact ⟨⟨hx0, hx1⟩, by
      rw [h_mid, h_rad]
      exact h⟩

/--
Tiling coverage: the union of `n` consecutive closed intervals of length `d`
covers `Set.Icc a (a + n * d)`. Requires `0 < n`.
-/
theorem union_tiling_cover (a d : ℝ) (n : ℕ) (hn : 0 < n) (hd : 0 ≤ d) :
    Set.Icc a (a + (n : ℝ) * d) ⊆
      ⋃ k : Fin n, Set.Icc (a + (k : ℝ) * d) (a + ((k : ℝ) + 1) * d) := by
  intro x hx
  have h1 : a ≤ x := hx.1
  have h2 : x ≤ a + (n : ℝ) * d := hx.2
  by_cases hd0 : d = 0
  · subst hd0
    have hxa : x = a := by simp at h2 ⊢ <;> linarith
    let ik : Fin n := ⟨0, hn⟩
    exact mem_iUnion.mpr ⟨ik, by simp [hxa]⟩
  · have hd_pos : 0 < d := by
      have h : 0 ≤ d := hd
      by_contra h'
      have : d = 0 := by linarith
      exact hd0 this
    let y := x - a
    have hy0 : 0 ≤ y := by linarith
    have hy1 : y ≤ (n : ℝ) * d := by linarith
    let k0 : ℕ := Nat.floor (y / d)
    have hk01 : (k0 : ℝ) ≤ y / d := Nat.floor_le (by positivity)
    have hk02 : y / d < (k0 : ℝ) + 1 := Nat.lt_floor_add_one (y / d)
    by_cases h_k : k0 < n
    · have h_left : a + (k0 : ℝ) * d ≤ x := by
        have h : (k0 : ℝ) * d ≤ y := by
          calc (k0 : ℝ) * d ≤ (y / d) * d := by gcongr
            _ = y := by field_simp [hd_pos.ne'] <;> ring
        linarith
      have h_right : x ≤ a + ((k0 : ℝ) + 1) * d := by
        have h : y < ((k0 : ℝ) + 1) * d := by
          calc y = (y / d) * d := by field_simp [hd_pos.ne'] <;> ring
            _ < ((k0 : ℝ) + 1) * d := by gcongr
        linarith
      let ik : Fin n := ⟨k0, h_k⟩
      exact mem_iUnion.mpr ⟨ik, ⟨h_left, h_right⟩⟩
    · have h_ge : n ≤ k0 := by omega
      have h_y_eq : y = (n : ℝ) * d := by
        have h1 : (n : ℝ) ≤ (k0 : ℝ) := by exact_mod_cast h_ge
        have h2 : (n : ℝ) ≤ y / d := by linarith
        have h3 : (n : ℝ) * d ≤ y := by
          calc (n : ℝ) * d ≤ (y / d) * d := by gcongr
            _ = y := by field_simp [hd_pos.ne'] <;> ring
        linarith
      let k1 : ℕ := n - 1
      have hk1_lt_n : k1 < n := by omega
      have h_k1_add : k1 + 1 = n := by omega
      have h4 : (k1 : ℝ) + 1 = (n : ℝ) := by exact_mod_cast h_k1_add
      have h_left : a + (k1 : ℝ) * d ≤ x := by
        have h5 : (k1 : ℝ) * d ≤ y := by
          rw [h_y_eq]
          have h6 : (k1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega)
          gcongr
        linarith
      have h_right : x ≤ a + ((k1 : ℝ) + 1) * d := by
        rw [h4]
        linarith [h_y_eq]
      let ik : Fin n := ⟨k1, hk1_lt_n⟩
      exact mem_iUnion.mpr ⟨ik, ⟨h_left, h_right⟩⟩

/--
Logarithmic bound on the number of geometric steps.

If `4 * rho * (17/15)^(N-1) ≤ L_max` with `0 < rho ≤ 1/24` and `0 < L_max ≤ 1`,
then `(N : ℝ) ≤ 1 + |Real.log rho| / Real.log (17/15)`.
-/
theorem geom_steps_log_bound (rho L_max : ℝ) (N : ℕ)
    (hrho_pos : 0 < rho) (hrho_le : rho ≤ 1 / 24)
    (hL_max_pos : 0 < L_max) (hL_max_le : L_max ≤ 1)
    (h : geomLength rho (N - 1) ≤ L_max) :
    (N : ℝ) ≤ 1 + |Real.log rho| / Real.log (17 / 15) := by
  have h_log1715_pos : 0 < Real.log (17 / 15 : ℝ) := by
    apply Real.log_pos
    norm_num
  cases N with
  | zero =>
    have h_rhs_pos : 0 ≤ 1 + |Real.log rho| / Real.log (17 / 15) := by positivity
    exact_mod_cast h_rhs_pos
  | succ N' =>
    have h' : 4 * rho * (17 / 15 : ℝ) ^ N' ≤ L_max := h
    have h1 : (17 / 15 : ℝ) ^ N' ≤ L_max / (4 * rho) := by
      have h4pos : 0 < 4 * rho := by linarith
      calc
        (17 / 15 : ℝ) ^ N'
          = (4 * rho * (17 / 15 : ℝ) ^ N') / (4 * rho) := by
            field_simp [h4pos.ne'] <;> ring
        _ ≤ L_max / (4 * rho) := by gcongr
    have h2 : Real.log ((17 / 15 : ℝ) ^ N') ≤ Real.log (L_max / (4 * rho)) :=
      Real.log_le_log (by positivity) h1
    have h3 : (N' : ℝ) * Real.log (17 / 15 : ℝ) ≤ Real.log (L_max / (4 * rho)) := by
      rw [Real.log_pow] at h2
      exact h2
    have h4 : Real.log (L_max / (4 * rho)) = Real.log (L_max / 4) - Real.log rho := by
      have h_eq : L_max / (4 * rho) = (L_max / 4) / rho := by ring
      rw [h_eq, Real.log_div (by positivity) (by positivity)]
      <;> ring
    have h5 : Real.log (L_max / 4) ≤ 0 := by
      apply Real.log_nonpos
      <;> norm_num <;> linarith
    have h6 : Real.log rho < 0 := by
      apply Real.log_neg
      <;> linarith
    have h7 : |Real.log rho| = -Real.log rho := by
      rw [abs_of_neg h6] <;> ring
    rw [h4] at h3
    have h8 : (N' : ℝ) * Real.log (17 / 15 : ℝ) ≤ |Real.log rho| := by
      rw [h7] at *
      <;> linarith
    have h9 : (N' : ℝ) ≤ |Real.log rho| / Real.log (17 / 15 : ℝ) := by
      calc
        (N' : ℝ)
          = ((N' : ℝ) * Real.log (17 / 15 : ℝ)) / Real.log (17 / 15 : ℝ) := by
            field_simp [h_log1715_pos.ne'] <;> ring
        _ ≤ |Real.log rho| / Real.log (17 / 15 : ℝ) := by gcongr
    have h10 : ((N'.succ : ℝ)) ≤ 1 + |Real.log rho| / Real.log (17 / 15 : ℝ) := by
      have h11 : ((N'.succ : ℝ)) = (N' : ℝ) + 1 := by simp
      rw [h11]
      linarith [h9]
    exact h10

/--
Geometric tiling coverage for left-facing intervals.

If `a : ℕ → ℝ` satisfies `17*a(k)/32 = 15*a(k+1)/32`, then the union of
`Set.Icc (15*a(k)/32) (17*a(k)/32)` for `k ∈ Fin (n+1)` covers
`Set.Icc (15*a(0)/32) (17*a(n)/32)`.
-/
theorem geometric_left_cover (a : ℕ → ℝ) (n : ℕ)
    (h_tile : ∀ k, 17 * a k / 32 = 15 * a (k + 1) / 32) :
    Set.Icc (15 * a 0 / 32) (17 * a n / 32) ⊆
      ⋃ k : Fin (n + 1), Set.Icc (15 * a k / 32) (17 * a k / 32) := by
  induction n with
  | zero =>
    intro x hx
    let ik : Fin 1 := ⟨0, by norm_num⟩
    exact mem_iUnion.mpr ⟨ik, hx⟩
  | succ n ih =>
    intro x hx
    have h_left : 15 * a 0 / 32 ≤ x := hx.1
    have h_right : x ≤ 17 * a (n + 1) / 32 := hx.2
    by_cases h : x ≤ 17 * a n / 32
    · have h_ih : x ∈
          (⋃ k : Fin (n + 1), Set.Icc (15 * a k / 32) (17 * a k / 32)) :=
        ih ⟨h_left, h⟩
      rcases mem_iUnion.mp h_ih with ⟨k, hk⟩
      let k' : Fin (n + 2) := ⟨k.val, by omega⟩
      exact mem_iUnion.mpr ⟨k', hk⟩
    · have h' : 15 * a (n + 1) / 32 ≤ x := by
        have h_tile' : 17 * a n / 32 = 15 * a (n + 1) / 32 := h_tile n
        linarith
      let ik : Fin (n + 2) := ⟨n + 1, by omega⟩
      exact mem_iUnion.mpr ⟨ik, ⟨h', h_right⟩⟩

/--
Geometric tiling coverage for right-facing intervals.

If `a : ℕ → ℝ` satisfies `17*a(k)/32 = 15*a(k+1)/32`, then the union of
`Set.Icc (1-17*a(k)/32) (1-15*a(k)/32)` for `k ∈ Fin (n+1)` covers
`Set.Icc (1-17*a(n)/32) (1-15*a(0)/32)`.
-/
theorem geometric_right_cover (a : ℕ → ℝ) (n : ℕ)
    (h_tile : ∀ k, 17 * a k / 32 = 15 * a (k + 1) / 32) :
    Set.Icc (1 - 17 * a n / 32) (1 - 15 * a 0 / 32) ⊆
      ⋃ k : Fin (n + 1),
        Set.Icc (1 - 17 * a k / 32) (1 - 15 * a k / 32) := by
  induction n with
  | zero =>
    intro x hx
    let ik : Fin 1 := ⟨0, by norm_num⟩
    exact mem_iUnion.mpr ⟨ik, hx⟩
  | succ n ih =>
    intro x hx
    have h_left : 1 - 17 * a (n + 1) / 32 ≤ x := hx.1
    have h_right : x ≤ 1 - 15 * a 0 / 32 := hx.2
    have h_tile' : 17 * a n / 32 = 15 * a (n + 1) / 32 := h_tile n
    by_cases h : x ≤ 1 - 17 * a n / 32
    · have h_upper : x ≤ 1 - 15 * a (n + 1) / 32 := by
        rw [←h_tile'] <;> exact h
      let ik : Fin (n + 2) := ⟨n + 1, by omega⟩
      exact mem_iUnion.mpr ⟨ik, ⟨h_left, h_upper⟩⟩
    · have h_lower : 1 - 17 * a n / 32 ≤ x := by linarith
      have h_ih : x ∈
          (⋃ k : Fin (n + 1),
            Set.Icc (1 - 17 * a k / 32) (1 - 15 * a k / 32)) :=
        ih ⟨h_lower, h_right⟩
      rcases mem_iUnion.mp h_ih with ⟨k, hk⟩
      let k' : Fin (n + 2) := ⟨k.val, by omega⟩
      exact mem_iUnion.mpr ⟨k', hk⟩

/--
Fin-friendly version of geometric left cover: for `0 < n`, covers
`Set.Icc (15*a(0)/32) (17*a(n-1)/32)` with `Fin n` intervals.
-/
theorem geometric_left_cover_fin (a : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (h_tile : ∀ k, 17 * a k / 32 = 15 * a (k + 1) / 32) :
    Set.Icc (15 * a 0 / 32) (17 * a (n - 1) / 32) ⊆
      ⋃ k : Fin n, Set.Icc (15 * a k / 32) (17 * a k / 32) := by
  have h_main := geometric_left_cover a (n - 1) h_tile
  have h_eq : (n - 1) + 1 = n := by omega
  intro x hx
  have h4 : x ∈
      ⋃ k : Fin ((n - 1) + 1),
        Set.Icc (15 * a k / 32) (17 * a k / 32) := h_main hx
  rcases mem_iUnion.mp h4 with ⟨k, hk⟩
  have h_k_lt : k.val < n := by
    have h : k.val < (n - 1) + 1 := k.is_lt
    have h_eq2 : (n - 1) + 1 = n := by omega
    linarith
  let k' : Fin n := ⟨k.val, h_k_lt⟩
  have h_val : k'.val = k.val := by rfl
  exact mem_iUnion.mpr ⟨k', by simpa [h_val] using hk⟩

/--
Fin-friendly version of geometric right cover: for `0 < n`, covers
`Set.Icc (1-17*a(n-1)/32) (1-15*a(0)/32)` with `Fin n` intervals.
-/
theorem geometric_right_cover_fin (a : ℕ → ℝ) (n : ℕ) (hn : 0 < n)
    (h_tile : ∀ k, 17 * a k / 32 = 15 * a (k + 1) / 32) :
    Set.Icc (1 - 17 * a (n - 1) / 32) (1 - 15 * a 0 / 32) ⊆
      ⋃ k : Fin n,
        Set.Icc (1 - 17 * a k / 32) (1 - 15 * a k / 32) := by
  have h_main := geometric_right_cover a (n - 1) h_tile
  have h_eq : (n - 1) + 1 = n := by omega
  intro x hx
  have h4 : x ∈
      ⋃ k : Fin ((n - 1) + 1),
        Set.Icc (1 - 17 * a k / 32) (1 - 15 * a k / 32) := h_main hx
  rcases mem_iUnion.mp h4 with ⟨k, hk⟩
  have h_k_lt : k.val < n := by
    have h : k.val < (n - 1) + 1 := k.is_lt
    have h_eq2 : (n - 1) + 1 = n := by omega
    linarith
  let k' : Fin n := ⟨k.val, h_k_lt⟩
  have h_val : k'.val = k.val := by rfl
  exact mem_iUnion.mpr ⟨k', by simpa [h_val] using hk⟩

end CenteredCoverHelpers

end Kakeya.Cinematic
