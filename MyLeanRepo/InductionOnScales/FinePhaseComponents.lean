module

public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.Homothety
public import MyLeanRepo.InductionOnScales.SSet
public import MyLeanRepo.InductionOnScales.SlopeCells

@[expose] public section

/-!
# Fine phase construction

Given a fine tube family at scale n with uniform slope-cell counts,
construct a local tube family at scale k = n-m that:
- Preserves the occupied slope cells (OS 5.4)
- Forms a tube SSet with constant C * 16^s
- Intersects the corresponding local square

This is the core of Phase B (OS Proposition 5.1, lines 796-842).
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace InductionOnScales.FineConfig

/-- If T is in the allowed parameter strip at scale n, then its local slope
cell index at scale m is in the allowed parameter strip at scale k = n - m. -/
lemma local_slope_cell_in_strip {n m : ℕ} (hnm : m ≤ n)
    {k : ℕ} (hk : k = n - m)
    (T : DyadicTube n) (hT : T.IsInAllowedParameterStrip) :
    -((2 ^ k : ℕ) : ℤ) ≤ localSlopeCellIndex m T.a ∧
    localSlopeCellIndex m T.a < ((2 ^ k : ℕ) : ℤ) := by
  let a := localSlopeCellIndex m T.a
  have h_eq : (a : ℝ) = ⌊(T.a : ℝ) / ((2 ^ m : ℕ) : ℝ)⌋ := by rfl
  have h_pos_m : 0 < (2 ^ m : ℝ) := by positivity
  have h5 : (n : ℝ) = (m : ℝ) + (k : ℝ) := by
    simp [hk, Nat.cast_sub hnm] <;> ring
  have h6 : (2 ^ n : ℝ) = (2 ^ m : ℝ) * (2 ^ k : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_natCast]
    rw [h5, Real.rpow_add] <;> norm_num
  -- Lower bound: a ≥ -2^k
  have h7 : (T.a : ℝ) / (2 ^ m : ℝ) ≥ -(2 ^ k : ℝ) := by
    have h8 : (T.a : ℝ) ≥ -(2 ^ n : ℝ) := by exact_mod_cast hT.1
    have h9 : -(2 ^ n : ℝ) = -(2 ^ m : ℝ) * (2 ^ k : ℝ) := by rw [h6] <;> ring
    have h10 : (T.a : ℝ) / (2 ^ m : ℝ) ≥ (-(2 ^ n : ℝ)) / (2 ^ m : ℝ) := by gcongr
    rw [h9] at h10
    have h11 : (-(2 ^ m : ℝ) * (2 ^ k : ℝ)) / (2 ^ m : ℝ) = -(2 ^ k : ℝ) := by
      field_simp [h_pos_m.ne'] <;> ring
    rw [h11] at h10
    exact h10
  have h12 : -((2 ^ k : ℕ) : ℤ) ≤ a := by
    have h13 : ((-((2 ^ k : ℕ) : ℤ) : ℝ)) ≤ (T.a : ℝ) / ((2 ^ m : ℕ) : ℝ) := by
      exact_mod_cast h7
    have h14 : (-((2 ^ k : ℕ) : ℤ)) ≤ a := by
      have h15 : a = ⌊(T.a : ℝ) / ((2 ^ m : ℕ) : ℝ)⌋ := by rfl
      rw [h15]
      have h16 : (-((2 ^ k : ℕ) : ℤ)) ≤ ⌊(T.a : ℝ) / ((2 ^ m : ℕ) : ℝ)⌋ := by
        rw [Int.le_floor]
        simpa using h13
      exact h16
    exact h14
  -- Upper bound: a < 2^k
  have h15 : (T.a : ℝ) / (2 ^ m : ℝ) < (2 ^ k : ℝ) := by
    have h16 : (T.a : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast hT.2
    have h17 : (2 ^ n : ℝ) = (2 ^ m : ℝ) * (2 ^ k : ℝ) := h6
    have h18 : (T.a : ℝ) / (2 ^ m : ℝ) < (2 ^ n : ℝ) / (2 ^ m : ℝ) := by gcongr
    rw [h17] at h18
    have h19 : ((2 ^ m : ℝ) * (2 ^ k : ℝ)) / (2 ^ m : ℝ) = (2 ^ k : ℝ) := by
      field_simp [h_pos_m.ne'] <;> ring
    rw [h19] at h18
    exact h18
  have h20 : a < ((2 ^ k : ℕ) : ℤ) := by
    have h21 : (a : ℝ) ≤ (T.a : ℝ) / ((2 ^ m : ℕ) : ℝ) := Int.floor_le _
    have h15' : (T.a : ℝ) / ((2 ^ m : ℕ) : ℝ) < (2 ^ k : ℝ) := by simpa using h15
    have h22 : (a : ℝ) < (2 ^ k : ℝ) := lt_of_le_of_lt h21 h15'
    exact_mod_cast h22
  exact ⟨h12, h20⟩

/-- Given a square q at scale k and a slope index a in the allowed strip,
there exists an intercept b such that the dyadic tube ⟨a, b⟩ intersects q. -/
lemma local_tube_exists_inline (k : ℕ) (q : DyadicSquare k) (a : ℤ)
    (ha : -((2 ^ k : ℕ) : ℤ) ≤ a ∧ a < ((2 ^ k : ℕ) : ℤ)) :
    ∃ (b : ℤ), (((⟨a, b⟩ : DyadicTube k).toSet) ∩ q.toSet).Nonempty := by
  let d := dyadicDelta k
  have hd_pos : 0 < d := dyadicDelta_pos k
  let x0 : ℝ := (q.i : ℝ) * d
  let y0 : ℝ := (q.j : ℝ) * d
  let slope : ℝ := (a : ℝ) * d
  let interc : ℝ := y0 - slope * x0
  let b : ℤ := ⌊interc / d⌋
  have h1 : (b : ℝ) * d ≤ interc := by
    have h : (b : ℝ) ≤ interc / d := Int.floor_le (interc / d)
    have h2 : (b : ℝ) * d ≤ (interc / d) * d := by gcongr
    have h3 : (interc / d) * d = interc := by field_simp [hd_pos.ne'] <;> ring
    rw [h3] at h2; exact h2
  have h2 : interc < ((b : ℝ) + 1) * d := by
    have h : interc / d < (b : ℝ) + 1 := Int.lt_floor_add_one (interc / d)
    have h2 : (interc / d) * d < ((b : ℝ) + 1) * d := by gcongr
    have h3 : (interc / d) * d = interc := by field_simp [hd_pos.ne'] <;> ring
    rw [h3] at h2; exact h2
  have hx0 : x0 ∈ Set.Ico ((q.i : ℝ) * d) ((q.i + 1 : ℝ) * d) := by
    simp only [x0, Set.mem_Ico]; constructor <;> simp [hd_pos] <;> linarith
  have hy0 : y0 ∈ Set.Ico ((q.j : ℝ) * d) ((q.j + 1 : ℝ) * d) := by
    simp only [y0, Set.mem_Ico]; constructor <;> simp [hd_pos] <;> linarith
  have hsq : (x0, y0) ∈ q.toSet := by
    simp only [DyadicSquare.toSet, Set.mem_prod]; exact ⟨hx0, hy0⟩
  have hsl : slope ∈ Set.Ico ((a : ℝ) * d) ((a + 1 : ℝ) * d) := by
    simp only [slope, Set.mem_Ico]; constructor <;> simp [hd_pos] <;> linarith
  have hint : interc ∈ Set.Ico ((b : ℝ) * d) ((b + 1 : ℝ) * d) := by
    simp only [Set.mem_Ico]; exact ⟨h1, h2⟩
  have heq : y0 = slope * x0 + interc := by simp only [y0, slope, x0, interc] <;> ring
  have htube : (x0, y0) ∈ (⟨a, b⟩ : DyadicTube k).toSet := by
    simp only [DyadicTube.toSet, Set.mem_setOf_eq]
    exact ⟨slope, hsl, interc, hint, heq⟩
  exact ⟨b, ⟨(x0, y0), htube, hsq⟩⟩

/-- Geometric lemma: if tubes all intersect a common square p ⊆ [0,1)² and
their slopes (left endpoints) are within r of c, then their intercepts
(left endpoints) are within 7*r of some center value (for r ≥ δ). -/
lemma intercepts_bounded_by_slope_interval' {n : ℕ} (p : DyadicSquare n)
    (F : Finset (DyadicTube n))
    (h_inc : ∀ T ∈ F, (T.toSet ∩ p.toSet).Nonempty)
    (h_bounded : p.toSet ⊆ unitSquare)
    (h_params : ∀ T ∈ F, T.IsInAllowedParameterStrip)
    (c : ℝ) (r : ℝ) (hr : dyadicDelta n ≤ r)
    (h_slopes : ∀ T ∈ F, |T.slope - c| ≤ r) :
    ∃ (b_center : ℝ), ∀ T ∈ F, |T.intercept - b_center| ≤ 7 * r := by
  let δ := dyadicDelta n
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_le_one : δ ≤ 1 := by
    have h_eq : δ = 1 / (2 ^ n : ℝ) := by exact_mod_cast dyadicDelta_eq_inv n
    rw [h_eq]
    have h2 : (1 : ℝ) ≤ (2 ^ n : ℝ) := by exact_mod_cast Nat.one_le_pow n 2 (by norm_num)
    exact (div_le_one (by positivity)).mpr h2
  have hr_pos : 0 ≤ r := by linarith [hδ_pos, hr]
  let x₀ : ℝ := (p.i : ℝ) * δ
  let y₀ : ℝ := (p.j : ℝ) * δ
  let b_center : ℝ := y₀ - c * x₀
  refine' ⟨b_center, _⟩
  intro T hT
  rcases h_inc T hT with ⟨⟨x, y⟩, hTtube, hTp⟩
  simp only [DyadicTube.toSet, Set.mem_setOf_eq] at hTtube
  rcases hTtube with ⟨σ, hσ, cint, hcint, h_eq⟩
  have h_x_in : x ∈ Set.Ico ((p.i : ℝ) * δ) ((p.i + 1 : ℝ) * δ) := (Set.mem_prod.mp hTp).1
  have h_y_in : y ∈ Set.Ico ((p.j : ℝ) * δ) ((p.j + 1 : ℝ) * δ) := (Set.mem_prod.mp hTp).2
  have h_x_bound : |x - x₀| < δ := by
    have h1 : (p.i : ℝ) * δ ≤ x := h_x_in.1
    have h2 : x < (p.i + 1 : ℝ) * δ := h_x_in.2
    have h3 : -δ < x - x₀ := by simp [x₀] <;> linarith
    have h4 : x - x₀ < δ := by simp [x₀] <;> linarith
    exact abs_lt.mpr ⟨h3, h4⟩
  have h_y_bound : |y - y₀| < δ := by
    have h1 : (p.j : ℝ) * δ ≤ y := h_y_in.1
    have h2 : y < (p.j + 1 : ℝ) * δ := h_y_in.2
    have h3 : -δ < y - y₀ := by simp [y₀] <;> linarith
    have h4 : y - y₀ < δ := by simp [y₀] <;> linarith
    exact abs_lt.mpr ⟨h3, h4⟩
  have hσ1 : (T.a : ℝ) * δ ≤ σ := hσ.1
  have hσ2 : σ < ((T.a : ℝ) + 1) * δ := hσ.2
  have h_slope_def : T.slope = (T.a : ℝ) * δ := by exact rfl
  have hσ_close : |σ - c| ≤ r + δ := by
    have h1 : |T.slope - c| ≤ r := h_slopes T hT
    have h21 : -δ < σ - T.slope := by rw [h_slope_def] <;> linarith
    have h22 : σ - T.slope < δ := by rw [h_slope_def] <;> linarith
    have h2 : |σ - T.slope| < δ := abs_lt.mpr ⟨h21, h22⟩
    have h3 : |σ - c| ≤ |σ - T.slope| + |T.slope - c| := abs_sub_le σ T.slope c
    linarith
  have h_x_nonneg : 0 ≤ x := by
    have h : (x, y) ∈ unitSquare := h_bounded hTp
    exact (Set.mem_prod.mp h).1.1
  have h_x_lt_one : x < 1 := by
    have h : (x, y) ∈ unitSquare := h_bounded hTp
    exact (Set.mem_prod.mp h).1.2
  have h_x_abs : |x| ≤ 1 := by
    rw [abs_le] <;> constructor <;> linarith
  have hTparam : T.IsInAllowedParameterStrip := h_params T hT
  have h_slope_ge_neg_one : -1 ≤ T.slope := by
    have h2 : -((2 ^ n : ℕ) : ℤ) ≤ T.a := hTparam.1
    have h3 : -(2 ^ n : ℝ) ≤ (T.a : ℝ) := by exact_mod_cast h2
    have h5 : δ = 1 / (2 ^ n : ℝ) := by exact_mod_cast dyadicDelta_eq_inv n
    have h6 : (T.a : ℝ) * δ ≥ -1 := by
      rw [h5]
      have h7 : (T.a : ℝ) * (1 / (2 ^ n : ℝ)) = (T.a : ℝ) / (2 ^ n : ℝ) := by field_simp <;> ring
      rw [h7]
      have h8 : (T.a : ℝ) / (2 ^ n : ℝ) ≥ -1 := by
        calc (T.a : ℝ) / (2 ^ n : ℝ)
          ≥ (-(2 ^ n : ℝ)) / (2 ^ n : ℝ) := by gcongr
        _ = -1 := by field_simp <;> ring
      exact h8
    exact h6
  have h_slope_plus_delta_le_one : T.slope + δ ≤ 1 := by
    have h3 : T.a < ((2 ^ n : ℕ) : ℤ) := hTparam.2
    have h4 : (T.a + 1 : ℝ) ≤ (2 ^ n : ℝ) := by exact_mod_cast (by omega)
    have h5 : δ = 1 / (2 ^ n : ℝ) := by exact_mod_cast dyadicDelta_eq_inv n
    have h6 : (T.a + 1 : ℝ) * δ ≤ 1 := by
      rw [h5]
      have h7 : (T.a + 1 : ℝ) * (1 / (2 ^ n : ℝ)) = (T.a + 1 : ℝ) / (2 ^ n : ℝ) := by field_simp <;> ring
      rw [h7]
      have h8 : (T.a + 1 : ℝ) / (2 ^ n : ℝ) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        exact h4
      exact h8
    have h9 : T.slope + δ = (T.a + 1 : ℝ) * δ := by
      simp [DyadicTube.slope] <;> ring
    rw [h9]
    exact h6
  have h_c_abs : |c| ≤ 1 + r := by
    have h3 : |T.slope - c| ≤ r := h_slopes T hT
    have h4 : -r ≤ T.slope - c := (abs_le.mp h3).1
    have h5 : T.slope - c ≤ r := (abs_le.mp h3).2
    have h6 : c ≤ 1 + r := by linarith [h_slope_plus_delta_le_one]
    have h7 : -(1 + r) ≤ c := by linarith [h_slope_ge_neg_one]
    rw [abs_le] <;> constructor <;> linarith
  have h_triangle : ∀ (a b : ℝ), |a - b| ≤ |a| + |b| := by
    intro a b
    have h3 : a - b = a + (-b) := by ring
    rw [h3]
    have h : |a + (-b)| ≤ |a| + |(-b)| := abs_add_le a (-b)
    have h2 : |(-b)| = |b| := by simp
    rw [h2] at h
    exact h
  have h_main_ineq : |cint - b_center| ≤ |y - y₀| + |σ - c| * |x| + |c| * |x - x₀| := by
    have h_eq2 : cint = y - σ * x := by linarith
    rw [h_eq2]
    have h1 : (y - σ * x) - (y₀ - c * x₀) = (y - y₀) - ((σ - c) * x + c * (x - x₀)) := by ring
    rw [h1]
    have h2 : |(y - y₀) - ((σ - c) * x + c * (x - x₀))| ≤ |y - y₀| + |(σ - c) * x + c * (x - x₀)| := by
      exact h_triangle (y - y₀) ((σ - c) * x + c * (x - x₀))
    have h3 : |(σ - c) * x + c * (x - x₀)| ≤ |σ - c| * |x| + |c| * |x - x₀| := by
      have h4 : |(σ - c) * x + c * (x - x₀)| ≤ |(σ - c) * x| + |c * (x - x₀)| := by
        exact abs_add_le ((σ - c) * x) (c * (x - x₀))
      have h5 : |(σ - c) * x| = |σ - c| * |x| := by rw [abs_mul]
      have h6 : |c * (x - x₀)| = |c| * |x - x₀| := by rw [abs_mul]
      rw [h5, h6] at h4
      exact h4
    linarith
  have h4 : |y - y₀| ≤ δ := by linarith [h_y_bound]
  have h5 : |σ - c| * |x| ≤ r + δ := by
    have h52 : |σ - c| ≤ r + δ := hσ_close
    have h53 : |x| ≤ 1 := h_x_abs
    have h : |σ - c| * |x| ≤ (r + δ) * |x| := mul_le_mul_of_nonneg_right h52 (abs_nonneg x)
    have h2 : (r + δ) * |x| ≤ (r + δ) * 1 := mul_le_mul_of_nonneg_left h53 (by linarith)
    linarith
  have h6 : |c| * |x - x₀| ≤ (1 + r) * δ := by
    have h63 : |c| ≤ 1 + r := h_c_abs
    have h61 : |x - x₀| ≤ δ := by linarith [h_x_bound]
    have h_step1 : |c| * |x - x₀| ≤ (1 + r) * |x - x₀| := mul_le_mul_of_nonneg_right h63 (abs_nonneg (x - x₀))
    have h_step2 : (1 + r) * |x - x₀| ≤ (1 + r) * δ := mul_le_mul_of_nonneg_left h61 (by linarith)
    exact le_trans h_step1 h_step2
  have h_cint_close : |cint - b_center| ≤ 3 * δ + r + r * δ := by
    calc |cint - b_center|
      ≤ |y - y₀| + |σ - c| * |x| + |c| * |x - x₀| := h_main_ineq
    _ ≤ δ + (r + δ) + (1 + r) * δ := by linarith
    _ = 3 * δ + r + r * δ := by ring
  have hcint1 : T.intercept ≤ cint := by
    simpa [DyadicTube.intercept] using hcint.1
  have hcint2 : cint < T.intercept + δ := by
    have h : cint < ((T.b : ℝ) + 1) * δ := by
      simpa [DyadicTube.intercept] using hcint.2
    have h2 : ((T.b : ℝ) + 1) * δ = T.intercept + δ := by
      simp [DyadicTube.intercept] <;> ring
    rw [h2] at h
    exact h
  have h_Tint_close : |T.intercept - cint| < δ := by
    have h1 : T.intercept ≤ cint := hcint1
    have h2 : cint < T.intercept + δ := hcint2
    have h3 : -δ < T.intercept - cint := by linarith
    have h4 : T.intercept - cint < δ := by linarith
    exact abs_lt.mpr ⟨h3, h4⟩
  have h10 : |T.intercept - b_center| ≤ |T.intercept - cint| + |cint - b_center| := abs_sub_le T.intercept cint b_center
  have h_sum : |T.intercept - cint| + |cint - b_center| ≤ 4 * δ + r + r * δ := by
    have h11 : |T.intercept - cint| < δ := h_Tint_close
    have h12 : |cint - b_center| ≤ 3 * δ + r + r * δ := h_cint_close
    linarith
  have h13 : 4 * δ + r + r * δ ≤ 7 * r := by
    have h14 : δ ≤ r := hr
    have h16 : 4 * δ ≤ 4 * r := by gcongr
    have h17 : r * δ ≤ r := by
      have h18 : δ ≤ 1 := hδ_le_one
      have h19 : 0 ≤ r := hr_pos
      calc r * δ ≤ r * 1 := by gcongr
        _ = r := by ring
    linarith
  have h_final : |T.intercept - b_center| ≤ 7 * r := by
    calc |T.intercept - b_center|
      ≤ |T.intercept - cint| + |cint - b_center| := h10
    _ ≤ 4 * δ + r + r * δ := h_sum
    _ ≤ 7 * r := h13
  exact h_final

/-- If `F` is a tube SSet at scale n, all tubes intersect a common square p,
and we take one representative per slope cell at scale m, then the resulting
local tubes at scale k = n - m form a tube SSet with constant `C * 16^s`. -/
lemma fine_tube_family_from_cells_sset
    {n m : ℕ} (hnm : m ≤ n)
    (p : DyadicSquare n)
    {s C : ℝ} (hs : 0 ≤ s)
    (F : Finset (DyadicTube n))
    (hF : IsFiniteTubeSSet s C F)
    (h_inc : ∀ T ∈ F, (T.toSet ∩ p.toSet).Nonempty)
    (h_bounded : p.toSet ⊆ unitSquare)
    (h_params : ∀ T ∈ F, T.IsInAllowedParameterStrip)
    (m_Q : ℕ) (hmQ_pos : 0 < m_Q)
    (h_uniform : ∀ (a : ℤ), (F.filter (fun T => localSlopeCellIndex m T.a = a)).card =
        if a ∈ F.image (fun T => localSlopeCellIndex m T.a) then m_Q else 0)
    {k : ℕ} (hk : k = n - m)
    (G : Finset (DyadicTube k))
    (hG_cells : G.image (fun U => U.a) = F.image (fun T => localSlopeCellIndex m T.a))
    (hG_inj : Set.InjOn (fun (U : DyadicTube k) => U.a) G)
    (q : DyadicSquare k) :
    IsFiniteTubeSSet s (C * Real.rpow 16 s) G := by
  let δ_k := dyadicDelta k
  let δ_n := dyadicDelta n
  have hδk_pos : 0 < δ_k := dyadicDelta_pos k
  have hδn_pos : 0 < δ_n := dyadicDelta_pos n
  have hδn_leδk : δ_n ≤ δ_k := by
    have h : δ_n = δ_k / ((2 ^ m : ℕ) : ℝ) := by
      simp only [δ_n, δ_k, dyadicDelta]
      have h2 : (n : ℝ) = (m : ℝ) + (k : ℝ) := by
        simp [hk, Nat.cast_sub hnm] <;> ring
      rw [h2]
      simp [Real.rpow_add] <;> field_simp <;> ring
    rw [h]
    have h3 : (1 : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow m 2 (by norm_num)
    have h4 : δ_k / ((2 ^ m : ℕ) : ℝ) ≤ δ_k := by
      apply div_le_self
      · exact le_of_lt hδk_pos
      · exact h3
    exact h4
  have hF_ne : F.Nonempty := hF.1
  have hC_one : 1 ≤ C := hF.2.1
  have h_cells_nonempty : (F.image (fun T => localSlopeCellIndex m T.a)).Nonempty := by
    exact Finset.Nonempty.image hF_ne _
  let cells := F.image (fun T => localSlopeCellIndex m T.a)
  let fiber (a : ℤ) : Finset (DyadicTube n) := F.filter (fun T => localSlopeCellIndex m T.a = a)
  have hG_nonempty : G.Nonempty := by
    have h_img : (G.image (fun U => U.a)).Nonempty := by
      rw [hG_cells]
      exact h_cells_nonempty
    exact Finset.Nonempty.of_image h_img
  have h_card : (G.card : ℝ) = (cells.card : ℝ) := by
    have h1 : (G.image (fun U => U.a)).card = G.card := by
      rw [Finset.card_image_of_injOn hG_inj]
    have h2 : (G.image (fun U => U.a)).card = cells.card := by
      rw [hG_cells]
    norm_cast at h1 h2 ⊢ <;> omega
  have hF_part : F = cells.biUnion fiber := by
    ext T
    simp only [Finset.mem_biUnion, fiber, Finset.mem_filter]
    constructor
    · intro hT
      exact ⟨localSlopeCellIndex m T.a, Finset.mem_image.mpr ⟨T, hT, rfl⟩, hT, rfl⟩
    · rintro ⟨a, _, hT, _⟩
      exact hT
  have h_fibers_disjoint : ∀ a ∈ cells, ∀ b ∈ cells, a ≠ b → Disjoint (fiber a) (fiber b) := by
    intro a _ b _ hne
    rw [Finset.disjoint_left]
    intro T hTa hTb
    have h1 : localSlopeCellIndex m T.a = a := (Finset.mem_filter.mp hTa).2
    have h2 : localSlopeCellIndex m T.a = b := (Finset.mem_filter.mp hTb).2
    rw [h1] at h2
    exact hne h2
  have hF_card : (F.card : ℝ) = (G.card : ℝ) * (m_Q : ℝ) := by
    have h1 : (F.card : ℝ) = ∑ a ∈ cells, ((fiber a).card : ℝ) := by
      have h_eq : F.card = ∑ a ∈ cells, (fiber a).card := by
        rw [hF_part, Finset.card_biUnion h_fibers_disjoint]
      exact_mod_cast h_eq
    rw [h1]
    have h_sum : ∑ a ∈ cells, ((fiber a).card : ℝ) = (cells.card : ℝ) * (m_Q : ℝ) := by
      have h2 : ∀ a ∈ cells, ((fiber a).card : ℝ) = (m_Q : ℝ) := by
        intro a ha
        have h4 : (fiber a).card = if a ∈ cells then m_Q else 0 := h_uniform a
        have h5 : (fiber a).card = m_Q := by
          rw [h4, if_pos ha]
        exact_mod_cast h5
      rw [Finset.sum_congr rfl h2]
      simp [Finset.sum_const] <;> ring
    rw [h_sum, h_card] <;> ring
  have h16s_one : 1 ≤ Real.rpow 16 s := by
    apply Real.one_le_rpow
    · norm_num
    · exact hs
  have hC'_one : 1 ≤ C * Real.rpow 16 s := by
    calc 1 = 1 * 1 := by ring
    _ ≤ C * Real.rpow 16 s := by gcongr <;> linarith
  refine' ⟨hG_nonempty, hC'_one, hs, _ , _⟩
  · -- Separation
    intro U hU V hV hne
    have h_a_ne : U.a ≠ V.a := by
      intro h; apply hne; exact hG_inj hU hV h
    have h_abs : 1 ≤ |(U.a : ℝ) - (V.a : ℝ)| := by
      have h_int : (U.a : ℤ) ≠ (V.a : ℤ) := h_a_ne
      have h2 : 0 < |U.a - V.a| := by
        apply abs_pos.mpr
        exact sub_ne_zero.mpr h_int
      have h3 : 1 ≤ |U.a - V.a| := by exact Int.le_def.mpr h2
      exact_mod_cast h3
    have h_slope_dist : δ_k ≤ |U.slope - V.slope| := by
      have h : U.slope - V.slope = ((U.a : ℝ) - (V.a : ℝ)) * δ_k := by
        simp [DyadicTube.slope] <;> ring
      have h4 : 1 * δ_k ≤ |(U.a : ℝ) - (V.a : ℝ)| * δ_k :=
        mul_le_mul_of_nonneg_right h_abs (le_of_lt hδk_pos)
      have h5 : δ_k ≤ |(U.a : ℝ) - (V.a : ℝ)| * δ_k := by simpa using h4
      rw [h, abs_mul, abs_of_pos hδk_pos]
      exact h5
    exact le_trans h_slope_dist (le_max_left _ _)
  · -- Frostman
    intro center r hr
    let c_slope : ℝ := (center.a : ℝ) * δ_k
    let R : ℝ := r + δ_k
    have hR_geδn : δ_n ≤ R := by linarith [hδn_leδk]
    have hR_le2r : R ≤ 2 * r := by linarith
    let F_r : Finset (DyadicTube n) := F.filter (fun T => |T.slope - c_slope| ≤ R)
    have hFr_sub : F_r ⊆ F := Finset.filter_subset _ _
    have hFr_slopes : ∀ T ∈ F_r, |T.slope - c_slope| ≤ R := by
      intro T hT; exact (Finset.mem_filter.mp hT).2
    have h_geom := intercepts_bounded_by_slope_interval' p F_r
      (fun T hT => h_inc T (hFr_sub hT))
      h_bounded
      (fun T hT => h_params T (hFr_sub hT))
      c_slope R hR_geδn hFr_slopes
    rcases h_geom with ⟨b_center, h_b_center⟩
    let center_n : DyadicTube n := ⟨center.a * (2 ^ m : ℤ), ⌊b_center / δ_n⌋⟩
    have h_center_slope : center_n.slope = c_slope := by
      have h : δ_k = ((2 ^ m : ℕ) : ℝ) * δ_n := by
        simp only [δ_k, δ_n, dyadicDelta]
        have h2 : (n : ℝ) = (m : ℝ) + (k : ℝ) := by
          simp [hk, Nat.cast_sub hnm] <;> ring
        rw [h2]
        simp [Real.rpow_add] <;> field_simp <;> ring
      have h_main : ((center.a * (2 ^ m : ℤ) : ℝ)) * δ_n = (center.a : ℝ) * δ_k := by
        rw [h]
        simp [Int.cast_mul]
        <;> ring
      simpa [center_n, DyadicTube.slope, c_slope] using h_main
    have h_center_intercept_close : |center_n.intercept - b_center| < δ_n := by
      simp [center_n, DyadicTube.intercept]
      have h1 : (⌊b_center / δ_n⌋ : ℝ) ≤ b_center / δ_n := Int.floor_le _
      have h2 : b_center / δ_n < (⌊b_center / δ_n⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have h3 : (⌊b_center / δ_n⌋ : ℝ) * δ_n ≤ b_center := by
        calc (⌊b_center / δ_n⌋ : ℝ) * δ_n ≤ (b_center / δ_n) * δ_n := by gcongr
        _ = b_center := by field_simp [hδn_pos.ne'] <;> ring
      have h4 : b_center < (⌊b_center / δ_n⌋ : ℝ) * δ_n + δ_n := by
        calc b_center = (b_center / δ_n) * δ_n := by field_simp [hδn_pos.ne'] <;> ring
        _ < ((⌊b_center / δ_n⌋ : ℝ) + 1) * δ_n := by gcongr
        _ = (⌊b_center / δ_n⌋ : ℝ) * δ_n + δ_n := by ring
      rw [abs_sub_lt_iff] <;> constructor <;> linarith
    have hFr_in_ball : ∀ T ∈ F_r, tubeParamDist T center_n ≤ 8 * R := by
      intro T hT
      have h1 : |T.slope - center_n.slope| ≤ R := by
        rw [h_center_slope]; exact hFr_slopes T hT
      have h2 : |T.intercept - b_center| ≤ 7 * R := h_b_center T hT
      have h_symm : |b_center - center_n.intercept| = |center_n.intercept - b_center| := by
        rw [show b_center - center_n.intercept = -(center_n.intercept - b_center) by ring, abs_neg]
      have h_tri : |T.intercept - center_n.intercept| ≤ |T.intercept - b_center| + |b_center - center_n.intercept| :=
        abs_sub_le T.intercept b_center center_n.intercept
      have h_close_le : |center_n.intercept - b_center| ≤ δ_n := by
        exact le_of_lt h_center_intercept_close
      have h3 : |T.intercept - center_n.intercept| ≤ 8 * R := by
        have h_step1 : |T.intercept - center_n.intercept| ≤ |T.intercept - b_center| + |center_n.intercept - b_center| := by
          calc |T.intercept - center_n.intercept|
            ≤ |T.intercept - b_center| + |b_center - center_n.intercept| := h_tri
          _ = |T.intercept - b_center| + |center_n.intercept - b_center| := by
            rw [h_symm]
        have h_step2 : |T.intercept - b_center| + |center_n.intercept - b_center| ≤ 7 * R + δ_n :=
          add_le_add h2 h_close_le
        have h_step3 : 7 * R + δ_n ≤ 8 * R := by
          have h24 : (8 : ℝ) * R = 7 * R + R := by ring
          rw [h24]
          rw [add_le_add_iff_left]
          exact hR_geδn
        exact le_trans h_step1 (le_trans h_step2 h_step3)
      have h1' : |T.slope - center_n.slope| ≤ 8 * R := by
        have hR_nonneg : 0 ≤ R := by linarith
        linarith [h1]
      exact max_le h1' h3
    let G_r := G.filter (fun U => tubeParamDist U center ≤ r)
    let cells_r := G_r.image (fun U => U.a)
    have h_cell_slope : ∀ (U : DyadicTube k), U ∈ G_r →
        ∀ (T : DyadicTube n), T ∈ F → localSlopeCellIndex m T.a = U.a →
          |T.slope - c_slope| ≤ R := by
      intro U hU T _ h_eq
      have h_dist : tubeParamDist U center ≤ r := (Finset.mem_filter.mp hU).2
      have h_slope_dist : |U.slope - center.slope| ≤ r := le_trans (le_max_left _ _) h_dist
      have h4 : |(U.a : ℝ) - (center.a : ℝ)| * δ_k ≤ r := by
        have h5 : U.slope - center.slope = ((U.a : ℝ) - (center.a : ℝ)) * δ_k := by
          simp [DyadicTube.slope] <;> ring
        rw [h5] at h_slope_dist
        rw [abs_mul, abs_of_pos hδk_pos] at h_slope_dist
        exact h_slope_dist
      have h_bounds := localSlopeCellIndex_correct n m hnm T
      rw [h_eq] at h_bounds
      have hδk_eq : δ_k = dyadicDelta (n - m) := by simp [δ_k, hk]
      have h6 : (U.a : ℝ) * δ_k ≤ T.slope := by
        rw [hδk_eq]; exact h_bounds.1
      have h7 : T.slope < ((U.a : ℝ) + 1) * δ_k := by
        rw [hδk_eq]; exact h_bounds.2
      have h8 : c_slope = (center.a : ℝ) * δ_k := by rfl
      have h9 : -R ≤ T.slope - c_slope := by
        rw [h8]
        have h10 : T.slope - (center.a : ℝ) * δ_k ≥ ((U.a : ℝ) - (center.a : ℝ)) * δ_k := by linarith
        have h11 : ((U.a : ℝ) - (center.a : ℝ)) * δ_k ≥ -|(U.a : ℝ) - (center.a : ℝ)| * δ_k := by
          have h12 : -|(U.a : ℝ) - (center.a : ℝ)| ≤ (U.a : ℝ) - (center.a : ℝ) := by
            exact neg_abs_le ((U.a : ℝ) - (center.a : ℝ))
          exact mul_le_mul_of_nonneg_right h12 (by linarith)
        linarith
      have h10 : T.slope - c_slope ≤ R := by
        rw [h8]
        have h11 : T.slope - (center.a : ℝ) * δ_k < ((U.a : ℝ) - (center.a : ℝ)) * δ_k + δ_k := by linarith
        have h12 : ((U.a : ℝ) - (center.a : ℝ)) * δ_k ≤ |(U.a : ℝ) - (center.a : ℝ)| * δ_k := by
          have h13 : (U.a : ℝ) - (center.a : ℝ) ≤ |(U.a : ℝ) - (center.a : ℝ)| := le_abs_self _
          exact mul_le_mul_of_nonneg_right h13 (by linarith)
        linarith
      have h_abs : |T.slope - c_slope| ≤ R := by
        apply abs_le.mpr
        exact ⟨h9, h10⟩
      exact h_abs
    let fiber (a : ℤ) : Finset (DyadicTube n) := F.filter (fun T => localSlopeCellIndex m T.a = a)
    have h_fiber_sub_Fr : ∀ a ∈ cells_r, fiber a ⊆ F_r := by
      intro a ha T hT
      have h5 : localSlopeCellIndex m T.a = a := (Finset.mem_filter.mp hT).2
      have h6 : T ∈ F := (Finset.mem_filter.mp hT).1
      rcases Finset.mem_image.mp ha with ⟨U, hU, rfl⟩
      have h8 : |T.slope - c_slope| ≤ R := h_cell_slope U hU T h6 h5
      simp only [F_r, Finset.mem_filter]
      exact ⟨h6, h8⟩
    have h_fibers_disjoint : ∀ a ∈ cells_r, ∀ b ∈ cells_r, a ≠ b → Disjoint (fiber a) (fiber b) := by
      intro a _ b _ hne
      rw [Finset.disjoint_left]
      intro T hTa hTb
      have h1 : localSlopeCellIndex m T.a = a := (Finset.mem_filter.mp hTa).2
      have h2 : localSlopeCellIndex m T.a = b := (Finset.mem_filter.mp hTb).2
      rw [h1] at h2
      exact hne h2
    have h_fiber_card : ∀ a ∈ cells_r, (fiber a).card = m_Q := by
      intro a ha
      have h_cells_r_sub : cells_r ⊆ cells := by
        have h1 : cells_r ⊆ G.image (fun U : DyadicTube k => U.a) := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨U, hU, rfl⟩
          have hU' : U ∈ G := (Finset.mem_filter.mp hU).1
          exact Finset.mem_image.mpr ⟨U, hU', rfl⟩
        have h2 : G.image (fun U : DyadicTube k => U.a) = cells := hG_cells
        rw [←h2]
        exact h1
      have h3 : a ∈ cells := h_cells_r_sub ha
      have h4 : (fiber a).card = if a ∈ cells then m_Q else 0 := h_uniform a
      rw [h4, if_pos h3]
    let union_fibers := cells_r.biUnion fiber
    have h_union_sub_Fr : union_fibers ⊆ F_r := by
      intro T hT
      rcases Finset.mem_biUnion.mp hT with ⟨a, ha, hTa⟩
      exact h_fiber_sub_Fr a ha hTa
    have h_union_card : (union_fibers.card : ℝ) = (cells_r.card : ℝ) * (m_Q : ℝ) := by
      have h_eq : union_fibers.card = ∑ a ∈ cells_r, (fiber a).card := by
        rw [Finset.card_biUnion h_fibers_disjoint]
      have h_cast : (union_fibers.card : ℝ) = ∑ a ∈ cells_r, ((fiber a).card : ℝ) := by
        rw [h_eq, Nat.cast_sum]
      rw [h_cast]
      have h2 : ∀ a ∈ cells_r, ((fiber a).card : ℝ) = (m_Q : ℝ) := by
        intro a ha
        have h3 : (fiber a).card = m_Q := h_fiber_card a ha
        exact_mod_cast h3
      have h_sum : ∑ a ∈ cells_r, ((fiber a).card : ℝ) = (cells_r.card : ℝ) * (m_Q : ℝ) := by
        rw [Finset.sum_congr rfl h2]
        simp [Finset.sum_const] <;> ring
      exact h_sum
    have h_inj_r : Set.InjOn (fun (U : DyadicTube k) => U.a) G_r := by
      intro U hU V hV h
      exact hG_inj (Finset.mem_filter.mp hU).1 (Finset.mem_filter.mp hV).1 h
    have h_cells_r_card : (cells_r.card : ℝ) = (G_r.card : ℝ) := by
      rw [Finset.card_image_of_injOn h_inj_r]
    have h_count1 : (G_r.card : ℝ) * (m_Q : ℝ) ≤ (F_r.card : ℝ) := by
      have h : (union_fibers.card : ℝ) ≤ (F_r.card : ℝ) := by
        exact_mod_cast Finset.card_le_card h_union_sub_Fr
      rw [h_union_card, h_cells_r_card] at h
      exact h
    have hFr_sub_ball : F_r ⊆ F.filter (fun T => tubeParamDist T center_n ≤ 8 * R) := by
      intro T hT
      simp only [Finset.mem_filter]
      exact ⟨hFr_sub hT, hFr_in_ball T hT⟩
    have h_frost : ((F.filter (fun T => tubeParamDist T center_n ≤ 8 * R)).card : ℝ) ≤
        C * Real.rpow (8 * R) s * (F.card : ℝ) := hF.2.2.2.2 center_n (8 * R) (by linarith [hδn_leδk])
    have h9 : (F_r.card : ℝ) ≤ C * Real.rpow (8 * R) s * (F.card : ℝ) := by
      have h10 : (F_r.card : ℝ) ≤ ((F.filter (fun T => tubeParamDist T center_n ≤ 8 * R)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hFr_sub_ball
      exact h10.trans h_frost
    have h10 : (G_r.card : ℝ) * (m_Q : ℝ) ≤ C * Real.rpow (8 * R) s * (F.card : ℝ) := by
      linarith
    have h11 : (G_r.card : ℝ) ≤ C * Real.rpow (8 * R) s * (G.card : ℝ) := by
      rw [hF_card] at h10
      have h_pos : (m_Q : ℝ) > 0 := by exact_mod_cast hmQ_pos
      nlinarith
    have h12 : Real.rpow (8 * R) s ≤ Real.rpow (16 * r) s := by
      have h13 : 8 * R ≤ 16 * r := by linarith
      exact Real.rpow_le_rpow (by linarith) h13 hs
    have h_rpos : 0 < r := by linarith [hδk_pos, hr]
    have h14 : Real.rpow (16 * r) s = Real.rpow 16 s * Real.rpow r s :=
      Real.mul_rpow (show (0 : ℝ) ≤ 16 by norm_num) (show (0 : ℝ) ≤ r by linarith)
    calc (G_r.card : ℝ)
      ≤ C * Real.rpow (8 * R) s * (G.card : ℝ) := h11
    _ ≤ C * Real.rpow (16 * r) s * (G.card : ℝ) := by
      have h_nonneg1 : 0 ≤ C := by linarith
      have h_nonneg2 : 0 ≤ (G.card : ℝ) := Nat.cast_nonneg G.card
      have h15 : C * Real.rpow (8 * R) s ≤ C * Real.rpow (16 * r) s :=
        mul_le_mul_of_nonneg_left h12 h_nonneg1
      exact mul_le_mul_of_nonneg_right h15 h_nonneg2
    _ = C * Real.rpow 16 s * Real.rpow r s * (G.card : ℝ) := by
      rw [h14] <;> ring
    _ = (C * Real.rpow 16 s) * Real.rpow r s * (G.card : ℝ) := by ring

/-- Given a fine tube family F at scale n with uniform slope-cell counts,
and a local square q at scale k = n-m, construct a local tube family G at
scale k that preserves slope cells, forms a tube SSet, and intersects q. -/
lemma construct_fine_tube_family
    {n m : ℕ} (hnm : m ≤ n)
    (p : DyadicSquare n)
    {s C : ℝ} (hs : 0 ≤ s)
    (F : Finset (DyadicTube n))
    (hF : IsFiniteTubeSSet s C F)
    (h_inc : ∀ T ∈ F, (T.toSet ∩ p.toSet).Nonempty)
    (h_bounded : p.toSet ⊆ unitSquare)
    (h_params : ∀ T ∈ F, T.IsInAllowedParameterStrip)
    (m_Q : ℕ) (hmQ_pos : 0 < m_Q)
    (h_uniform : ∀ (a : ℤ), (F.filter (fun T => localSlopeCellIndex m T.a = a)).card =
        if a ∈ F.image (fun T => localSlopeCellIndex m T.a) then m_Q else 0)
    {k : ℕ} (hk : k = n - m)
    (q : DyadicSquare k) :
    ∃ (G : Finset (DyadicTube k)),
      G.image (fun U => U.a) = F.image (fun T => localSlopeCellIndex m T.a) ∧
      Set.InjOn (fun (U : DyadicTube k) => U.a) G ∧
      IsFiniteTubeSSet s (C * Real.rpow 16 s) G ∧
      ∀ U ∈ G, (U.toSet ∩ q.toSet).Nonempty := by
  let cells := F.image (fun T => localSlopeCellIndex m T.a)
  -- For each cell index a, choose a local tube with slope index a intersecting q
  have h_choose : ∀ (a : ℤ), a ∈ cells →
      ∃ (U : DyadicTube k), U.a = a ∧ (U.toSet ∩ q.toSet).Nonempty := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨T, hT, rfl⟩
    have h_strip := local_slope_cell_in_strip hnm hk T (h_params T hT)
    rcases local_tube_exists_inline k q (localSlopeCellIndex m T.a) h_strip with ⟨b, hb⟩
    refine' ⟨⟨localSlopeCellIndex m T.a, b⟩, rfl, hb⟩
  -- Use Classical.choose to get a function from cells to tubes
  choose U hUa hUinc using h_choose
  -- Define a total function by using a dummy tube for indices not in cells
  let U_total (a : ℤ) : DyadicTube k :=
    if h : a ∈ cells then U a h else ⟨0, 0⟩
  let G : Finset (DyadicTube k) := cells.image U_total
  have hU_total_eq : ∀ (a : ℤ), ∀ (ha : a ∈ cells), U_total a = U a ha := by
    intro a ha
    simp [U_total, ha]
  have hG_inj : Set.InjOn (fun (U : DyadicTube k) => U.a) G := by
    intro U1 hU1 U2 hU2 h
    rcases Finset.mem_image.mp hU1 with ⟨a1, ha1, rfl⟩
    rcases Finset.mem_image.mp hU2 with ⟨a2, ha2, rfl⟩
    have h1 : (U_total a1).a = (U_total a2).a := h
    have h2 : a1 = a2 := by
      rw [hU_total_eq a1 ha1, hU_total_eq a2 ha2] at h1
      rw [hUa a1 ha1, hUa a2 ha2] at h1
      exact h1
    rw [h2]
  have hG_cells : G.image (fun U => U.a) = cells := by
    have h1 : G.image (fun U => U.a) = cells.image (fun a : ℤ => (U_total a).a) := by
      rw [Finset.image_image] <;> rfl
    have h2 : cells.image (fun a : ℤ => (U_total a).a) = cells.image (fun a : ℤ => a) := by
      apply Finset.image_congr
      intro a ha
      have h3 : (U_total a).a = a := by
        rw [hU_total_eq a ha, hUa a ha]
      exact h3
    have h4 : cells.image (fun a : ℤ => a) = cells := by simp
    calc G.image (fun U => U.a)
      = cells.image (fun a : ℤ => (U_total a).a) := h1
    _ = cells.image (fun a : ℤ => a) := h2
    _ = cells := h4
  have h_sset : IsFiniteTubeSSet s (C * Real.rpow 16 s) G :=
    fine_tube_family_from_cells_sset hnm p hs F hF h_inc h_bounded h_params
      m_Q hmQ_pos h_uniform hk G hG_cells hG_inj q
  have h_incidence : ∀ U ∈ G, (U.toSet ∩ q.toSet).Nonempty := by
    intro U hU
    rcases Finset.mem_image.mp hU with ⟨a, ha, rfl⟩
    rw [hU_total_eq a ha]
    exact hUinc a ha
  exact ⟨G, hG_cells, hG_inj, h_sset, h_incidence⟩
