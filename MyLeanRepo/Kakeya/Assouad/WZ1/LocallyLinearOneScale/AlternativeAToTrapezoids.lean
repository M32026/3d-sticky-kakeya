import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions

/-!
# Alternative A → Vertical Trapezoids Conversion

Given the strip condition from Alternative A and the set of active heights,
construct a nonempty family of separated vertical trapezoids with the required
geometric properties and slope approximation.

## Strategy

Case split on the direction component `d₁`:

1. **Non-vertical** (`|d₁| ≥ 1/√5`): Use slope `m = -d₀/d₁`, intercept `0`.
   The strip condition directly gives `|f z - m·z| ≤ ρ`.

2. **Nearly-vertical** (`|d₁| < 1/√5`): All strip heights cluster in an interval
   of length `< ρ`. Use constant approximation (slope `0`, intercept `f z₀`).
   Lipschitz + height range bound gives `|f z - f z₀| ≤ ρ`.

In both cases, pick a reference height `z₀ ∈ Z` and build one trapezoid with
core `[z₀, z₀ + L]` where `L = ρ^(1/2 + outputLoss)`. A singleton family
vacuously satisfies separated cores.
-/

namespace Kakeya.Assouad

/-! ### Helper: Diameter lower bound for separated finite sets -/

lemma diameter_lower_bound_of_separated
    (S : Finset ℝ) (hS : S.Nonempty)
    (s : ℝ) (_hs : 0 < s)
    (h_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → s ≤ |x - y|) :
    (S.card - 1 : ℝ) * s ≤ S.max' hS - S.min' hS := by
  classical
  have h_main : ∀ (n : ℕ), ∀ (T : Finset ℝ), T.card = n →
      (hT : T.Nonempty) →
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → s ≤ |x - y|) →
      (n - 1 : ℝ) * s ≤ T.max' hT - T.min' hT := by
    intro n
    induction n with
    | zero =>
      intro T hcard hT _
      exfalso
      have h_empty : T = ∅ := Finset.card_eq_zero.mp hcard
      rw [h_empty] at hT
      simp [Finset.Nonempty] at hT
    | succ n' ih =>
      intro T hcard hT hsepT
      by_cases h_one : T.card = 1
      · have h_n' : n' = 0 := by omega
        subst h_n'
        simpa using show (0 : ℝ) ≤ T.max' hT - T.min' hT from
          sub_nonneg.mpr (Finset.min'_le_max' T hT)
      · have h_n'_pos : 1 ≤ n' := by omega
        let x := T.min' hT
        have hx : x ∈ T := Finset.min'_mem T hT
        let T' := T.erase x
        have h_card' : T'.card = n' := by
          have h : T'.card = T.card - 1 := Finset.card_erase_of_mem hx
          rw [h, hcard] <;> omega
        have hT' : T'.Nonempty := by
          apply Finset.card_pos.mp
          rw [h_card'] <;> omega
        have h_sep' : ∀ y ∈ T', ∀ z ∈ T', y ≠ z → s ≤ |y - z| := by
          intro y hy z hz hyz
          exact hsepT y (Finset.mem_erase.mp hy |>.2) z (Finset.mem_erase.mp hz |>.2) hyz
        have h_ih := ih T' h_card' hT' h_sep'
        let y := T'.min' hT'
        have hy : y ∈ T' := Finset.min'_mem T' hT'
        have h_y_in_T : y ∈ T := (Finset.mem_erase.mp hy).2
        have h_x_lt_y : x < y := by
          have h1 : x ≤ y := Finset.min'_le T y h_y_in_T
          have h2 : x ≠ y := by
            intro h_eq
            have h_contra : y ∉ T' := by
              rw [show y = x from h_eq.symm]
              simp [T']
            exact h_contra hy
          exact lt_of_le_of_ne h1 h2
        have h_dist : s ≤ y - x := by
          have h3 := hsepT y h_y_in_T x hx (by linarith)
          have h4 : |y - x| = y - x := by rw [abs_of_pos] <;> linarith
          rw [h4] at h3 <;> exact h3
        have h_max_in_T' : T.max' hT ∈ T' := by
          have h_ne_max : T.max' hT ≠ x := by
            intro h_eq
            have h_all : ∀ z ∈ T, z ≤ x := by
              intro z hz
              rw [←h_eq]
              exact Finset.le_max' T z hz
            have h_y_le : y ≤ x := h_all y h_y_in_T
            linarith
          have h5 : T.max' hT ∈ T := Finset.max'_mem T hT
          simpa [T', h_ne_max] using h5
        have h_max_eq : T.max' hT = T'.max' hT' := by
          have h1 : T'.max' hT' ≤ T.max' hT :=
            Finset.le_max' T (T'.max' hT')
              ((Finset.mem_erase.mp (Finset.max'_mem T' hT')).2)
          have h2 : T.max' hT ≤ T'.max' hT' :=
            Finset.le_max' T' (T.max' hT) h_max_in_T'
          linarith
        have h_goal : (n' : ℝ) * s ≤ T.max' hT - x := by
          have h1 : (n' : ℝ) * s = ((n' : ℝ) - 1) * s + s := by ring
          rw [h1]
          have h3 : ((n' : ℝ) - 1) * s ≤ T'.max' hT' - y := by
            rw [show T'.min' hT' = y from rfl] at h_ih
            exact h_ih
          linarith [h_dist, h_max_eq]
        have h_final : ((n' + 1 : ℕ) - 1 : ℝ) * s ≤ T.max' hT - T.min' hT := by
          have h4 : T.min' hT = x := by rfl
          have h5 : ((n' + 1 : ℕ) - 1 : ℝ) = (n' : ℝ) := by simp
          rw [h5, h4]
          exact h_goal
        exact h_final
  exact h_main S.card S rfl hS h_sep

/-! ### Helper: Interval extension -/

lemma extend_interval_to_length
    (S : Finset ℝ) (hS : S.Nonempty)
    (L_min L_max : ℝ) (hLmin_pos : 0 < L_min) (hLmin_le : L_min ≤ L_max)
    (h_diam : S.max' hS - S.min' hS ≤ L_max) :
    ∃ (a b : ℝ), a ≤ b ∧ L_min ≤ b - a ∧ b - a ≤ L_max ∧
      (∀ x ∈ S, a ≤ x ∧ x ≤ b) := by
  let a := S.min' hS
  let b := S.max' hS
  have h_ab : a ≤ b := Finset.min'_le_max' S hS
  by_cases h_long : b - a ≥ L_min
  · refine ⟨a, b, h_ab, h_long, h_diam, fun x hx => ?_⟩
    exact ⟨Finset.min'_le S x hx, Finset.le_max' S x hx⟩
  · refine ⟨a, a + L_min, by linarith, by linarith, by linarith, fun x hx => ?_⟩
    have h1 : a ≤ x := Finset.min'_le S x hx
    have h2 : x ≤ a + L_min := by
      have h3 : x ≤ b := Finset.le_max' S x hx
      linarith
    exact ⟨h1, h2⟩

/-! ### Helper: Slope bound and affine approximation (non-vertical) -/

lemma slope_bound_from_direction
    (d : Point2) (hd : ‖d‖ = 1)
    (h_d1 : |d 1| ≥ 1 / Real.sqrt 5) :
    |(-d 0 / d 1)| ≤ 2 := by
  set d₀ := d 0 with hd₀
  set d₁ := d 1 with hd₁
  have hnorm : d₀^2 + d₁^2 = 1 := by
    simpa [EuclideanSpace.norm_eq] using hd
  have h_d1_sq : d₁^2 ≥ 1 / 5 := by
    have h1 : d₁^2 = |d₁|^2 := by simp [sq_abs]
    rw [h1]
    have h2 : (1 / Real.sqrt 5) ^ 2 ≤ |d₁| ^ 2 := by gcongr
    have h3 : (1 / Real.sqrt 5) ^ 2 = 1 / 5 := by field_simp <;> norm_num
    linarith
  have h_d1_ne_zero : d₁ ≠ 0 := by nlinarith
  have h : d₀^2 ≤ 4 * d₁^2 := by nlinarith
  have h5 : |d₀ / d₁| ^ 2 ≤ 4 := by
    calc
      |d₀ / d₁| ^ 2 = d₀^2 / d₁^2 := by simp [sq_abs] <;> ring
      _ ≤ 4 * d₁^2 / d₁^2 := by gcongr
      _ = 4 := by field_simp [h_d1_ne_zero] <;> ring
  have h6 : |d₀ / d₁| ≤ 2 := by
    have h7 : 0 ≤ |d₀ / d₁| := by positivity
    nlinarith
  have h8 : |(-d₀ / d₁)| = |d₀ / d₁| := by
    rw [show (-d₀ / d₁) = -(d₀ / d₁) by ring, abs_neg]
  rw [h8]; exact h6

lemma strip_affine_approximation
    (d : Point2) (rho : ℝ) (hrho : 0 < rho)
    (f : ℝ → ℝ) (z : ℝ)
    (h_d1 : |d 1| ≥ 1 / Real.sqrt 5)
    (h_strip : |d 0 * z + d 1 * f z| ≤ rho / (5 * Real.sqrt 3)) :
    |f z - (-(d 0 / d 1)) * z| ≤ rho := by
  set d₀ := d 0 with hd₀
  set d₁ := d 1 with hd₁
  have h_d1_sq : d₁^2 ≥ 1 / 5 := by
    have h1 : d₁^2 = |d₁|^2 := by simp [sq_abs]
    rw [h1]
    have h2 : (1 / Real.sqrt 5) ^ 2 ≤ |d₁| ^ 2 := by gcongr
    have h3 : (1 / Real.sqrt 5) ^ 2 = 1 / 5 := by field_simp <;> norm_num
    linarith
  have h_d1_ne_zero : d₁ ≠ 0 := by nlinarith
  have h_main : |f z - (-(d₀ / d₁)) * z| = |d₀ * z + d₁ * f z| / |d₁| := by
    have h : f z - (-(d₀ / d₁)) * z = (d₀ * z + d₁ * f z) / d₁ := by
      field_simp [h_d1_ne_zero] <;> ring
    rw [h, abs_div] <;> rfl
  rw [h_main]
  have h_step1 : |d₀ * z + d₁ * f z| / |d₁| ≤
      (rho / (5 * Real.sqrt 3)) / |d₁| :=
    div_le_div_of_nonneg_right h_strip (by positivity)
  have h_step2 : (rho / (5 * Real.sqrt 3)) / |d₁| ≤
      (rho / (5 * Real.sqrt 3)) / (1 / Real.sqrt 5) := by
    have h_pos_num : 0 ≤ rho / (5 * Real.sqrt 3) := by positivity
    have h_pos_den : 0 < (1 / Real.sqrt 5) := by positivity
    have h_le : (1 / Real.sqrt 5) ≤ |d₁| := h_d1
    exact div_le_div_of_nonneg_left h_pos_num h_pos_den h_le
  have h_bound2 : (rho / (5 * Real.sqrt 3)) / (1 / Real.sqrt 5) ≤ rho := by
    have h4 : Real.sqrt 5 / (5 * Real.sqrt 3) ≤ 1 := by
      have h5 : 0 < 5 * Real.sqrt 3 := by positivity
      have h6 : Real.sqrt 5 ≤ 5 * Real.sqrt 3 := by
        nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 3,
          Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      exact (div_le_one h5).mpr h6
    have h7 : (rho / (5 * Real.sqrt 3)) / (1 / Real.sqrt 5) =
        rho * (Real.sqrt 5 / (5 * Real.sqrt 3)) := by field_simp
    rw [h7]
    have h8 : 0 ≤ rho := by linarith
    nlinarith
  linarith

/-! ### Helper: Height range bound and constant approximation (nearly-vertical) -/

lemma height_range_bound_of_strip
    (d : Point2) (rho C c : ℝ) (_hrho : 0 < rho) (hc : 0 < c)
    (f : ℝ → ℝ) (hf_lip : ∀ x y, |f x - f y| ≤ |x - y|)
    (h_gap : c ≤ |d 0| - |d 1|)
    (z1 z2 : ℝ)
    (h_strip1 : |d 0 * z1 + d 1 * f z1| ≤ C * rho)
    (h_strip2 : |d 0 * z2 + d 1 * f z2| ≤ C * rho) :
    |z1 - z2| ≤ 2 * C * rho / c := by
  set d₀ := d 0 with hd₀
  set d₁ := d 1 with hd₁
  set E := d₀ * z1 + d₁ * f z1 - (d₀ * z2 + d₁ * f z2) with hE
  have hE_eq : E = d₀ * (z1 - z2) + d₁ * (f z1 - f z2) := by
    simp [hE] <;> ring
  have h_absE : |E| ≤ 2 * C * rho := by
    have h : |E| ≤ |d₀ * z1 + d₁ * f z1| + |d₀ * z2 + d₁ * f z2| := by
      simpa [hE] using abs_sub (d₀ * z1 + d₁ * f z1) (d₀ * z2 + d₁ * f z2)
    linarith
  have h_abs1 : |d₀ * (z1 - z2)| = |d₀| * |z1 - z2| := by rw [abs_mul]
  have h_abs2 : |d₁ * (f z1 - f z2)| = |d₁| * |f z1 - f z2| := by rw [abs_mul]
  have h : |d₀ * (z1 - z2)| ≤ |E| + |d₁ * (f z1 - f z2)| := by
    calc
      |d₀ * (z1 - z2)|
        = |E - d₁ * (f z1 - f z2)| := by rw [hE_eq] <;> ring
      _ ≤ |E| + |d₁ * (f z1 - f z2)| := by
        exact abs_sub E (d₁ * (f z1 - f z2))
  have h2 : |d₀| * |z1 - z2| ≤ |E| + |d₁| * |f z1 - f z2| := by
    rw [h_abs1, h_abs2] at h
    exact h
  have h_d1_nonneg : 0 ≤ |d₁| := by positivity
  have h4 : |f z1 - f z2| ≤ |z1 - z2| := hf_lip z1 z2
  have h_step : |d₁| * |f z1 - f z2| ≤ |d₁| * |z1 - z2| :=
    mul_le_mul_of_nonneg_left h4 h_d1_nonneg
  have h3 : |d₀| * |z1 - z2| ≤ 2 * C * rho + |d₁| * |z1 - z2| := by
    linarith [h2, h_absE, h_step]
  have h4' : (|d₀| - |d₁|) * |z1 - z2| ≤ 2 * C * rho := by linarith
  have h5 : c * |z1 - z2| ≤ 2 * C * rho := by
    have h6 : c ≤ |d₀| - |d₁| := h_gap
    have h7 : 0 ≤ |z1 - z2| := by positivity
    nlinarith
  have h8 : |z1 - z2| ≤ 2 * C * rho / c := by
    calc
      |z1 - z2| = (c * |z1 - z2|) / c := by
        field_simp [hc.ne'] <;> ring
      _ ≤ (2 * C * rho) / c := by gcongr
  exact h8

lemma constant_approximation_near_vertical
    (d : Point2) (rho C c : ℝ) (hrho : 0 < rho) (hc : 0 < c)
    (f : ℝ → ℝ) (hf_lip : ∀ x y, |f x - f y| ≤ |x - y|)
    (h_gap : c ≤ |d 0| - |d 1|)
    (h_const : 2 * C / c ≤ 1)
    (z0 z : ℝ)
    (h_strip0 : |d 0 * z0 + d 1 * f z0| ≤ C * rho)
    (h_strip : |d 0 * z + d 1 * f z| ≤ C * rho) :
    |f z - f z0| ≤ rho := by
  have h1 : |z - z0| ≤ 2 * C * rho / c :=
    height_range_bound_of_strip d rho C c hrho hc f hf_lip h_gap z z0
      h_strip h_strip0
  have h2 : |f z - f z0| ≤ |z - z0| := hf_lip z z0
  have h3 : |f z - f z0| ≤ 2 * C * rho / c := by linarith
  have h4 : 2 * C * rho / c ≤ rho := by
    have h5 : 2 * C * rho / c = (2 * C / c) * rho := by ring
    rw [h5]
    have h6 : (2 * C / c) * rho ≤ rho := by
      have h7 : 2 * C / c ≤ 1 := h_const
      have h8 : 0 ≤ rho := by linarith
      nlinarith
    exact h6
  linarith

/-! ### Gap condition for nearly-vertical case -/

/-- If `|d₁| < 1/√5` and `‖d‖ = 1`, then `|d₀| - |d₁| ≥ 1/√5`. -/
lemma near_vertical_gap
    (d : Point2) (hd : ‖d‖ = 1)
    (h_d1_small : |d 1| < 1 / Real.sqrt 5) :
    1 / Real.sqrt 5 ≤ |d 0| - |d 1| := by
  set d₀ := d 0 with hd₀
  set d₁ := d 1 with hd₁
  have hnorm : d₀^2 + d₁^2 = 1 := by
    simpa [EuclideanSpace.norm_eq] using hd
  have h_d1_sq : d₁^2 < 1 / 5 := by
    have h1 : d₁^2 = |d₁|^2 := by simp [sq_abs]
    rw [h1]
    have h2 : |d₁| ^ 2 < (1 / Real.sqrt 5) ^ 2 := by gcongr
    have h3 : (1 / Real.sqrt 5) ^ 2 = 1 / 5 := by field_simp <;> norm_num
    rw [h3] at h2
    exact h2
  have h_d0_sq : d₀^2 > 4 / 5 := by nlinarith
  have h_d0_abs : |d₀| > 2 / Real.sqrt 5 := by
    have h1 : |d₀| ^ 2 = d₀^2 := by simp [sq_abs]
    have h2 : (2 / Real.sqrt 5) ^ 2 = 4 / 5 := by field_simp <;> norm_num
    have h3 : |d₀| ^ 2 > (2 / Real.sqrt 5) ^ 2 := by
      rw [h1, h2]; exact h_d0_sq
    have h4 : 0 ≤ |d₀| := by positivity
    have h5 : 0 ≤ 2 / Real.sqrt 5 := by positivity
    have h6 : |d₀| > 2 / Real.sqrt 5 := by
      nlinarith [sq_nonneg (|d₀| - 2 / Real.sqrt 5)]
    exact h6
  have h3 : |d₀| - |d₁| > 1 / Real.sqrt 5 := by
    have h4 : |d₀| > 2 / Real.sqrt 5 := h_d0_abs
    have h5 : |d₁| < 1 / Real.sqrt 5 := h_d1_small
    have h6 : |d₀| - |d₁| > 2 / Real.sqrt 5 - 1 / Real.sqrt 5 := by linarith
    have h7 : 2 / Real.sqrt 5 - 1 / Real.sqrt 5 = 1 / Real.sqrt 5 := by ring
    rw [h7] at h6
    exact h6
  exact le_of_lt h3

/-- `2 * (1/(5√3)) / (1/√5) = 2/√15 < 1`. -/
lemma near_vertical_const :
    2 * (1 / (5 * Real.sqrt 3)) / (1 / Real.sqrt 5) ≤ 1 := by
  have h1 : 0 < Real.sqrt 3 := by positivity
  have h2 : 2 * Real.sqrt 5 ≤ 5 * Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 3,
      Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have h3 : 2 * (1 / (5 * Real.sqrt 3)) / (1 / Real.sqrt 5) =
      2 * Real.sqrt 5 / (5 * Real.sqrt 3) := by field_simp
  rw [h3]
  have h4 : 0 < 5 * Real.sqrt 3 := by positivity
  exact (div_le_one h4).mpr h2

/-! ### Main conversion lemma -/

/--
Convert Alternative A strip data into a vertical trapezoid.

Given a nonempty set `Z` of active heights satisfying the de-normalized strip
condition, produce one trapezoid with core `[z₀, z₀ + L]` where
`L = ρ^(1/2 + outputLoss)`. The slope approximation holds at every height
in `Z` that falls inside the core.
-/
lemma alternative_a_to_trapezoid
    {rho outputLoss : ℝ}
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (houtputLoss : 0 < outputLoss)
    {f : ℝ → ℝ}
    (hf_lip : ∀ x y, |f x - f y| ≤ |x - y|)
    (Z : Finset ℝ)
    (hZ_nonempty : Z.Nonempty)
    (d : Point2)
    (hd : ‖d‖ = 1)
    (h_strip : ∀ z ∈ Z, |d 0 * z + d 1 * f z| ≤ rho / (5 * Real.sqrt 3)) :
    ∃ (T : WZ1VerticalTrapezoid),
      T.height = rho ∧
      |T.slope| ≤ 2 ∧
      Real.rpow rho (1 / 2 + outputLoss) ≤ T.length ∧
      T.length ≤ Real.sqrt rho ∧
      (∀ z ∈ T.core, z ∈ Z → |f z - T.affine z| ≤ rho) ∧
      ∃ (z0 : ℝ), z0 ∈ Z ∧ z0 ∈ T.core := by
  classical
  let z0 := Z.min' hZ_nonempty
  have hz0 : z0 ∈ Z := Finset.min'_mem Z hZ_nonempty
  let L := Real.rpow rho (1 / 2 + outputLoss)
  have hL_pos : 0 < L := Real.rpow_pos_of_pos hrho _
  have hL_le_sqrt : L ≤ Real.sqrt rho := by
    have h_exp : 1 / 2 ≤ 1 / 2 + outputLoss := by linarith
    have h_log_rho : Real.log rho ≤ 0 := Real.log_nonpos (by linarith) hrho_one
    have h_pos1 : 0 < L := Real.rpow_pos_of_pos hrho _
    have h_pos2 : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
    have h_log : Real.log L ≤ Real.log (Real.sqrt rho) := by
      have h_log_L : Real.log L = (1 / 2 + outputLoss) * Real.log rho := by
        have hL1 : L = Real.rpow rho (1 / 2 + outputLoss) := by rfl
        rw [hL1]
        exact Real.log_rpow hrho (1 / 2 + outputLoss)
      rw [h_log_L]
      have hsqrt : Real.log (Real.sqrt rho) = (1 / 2 : ℝ) * Real.log rho := by
        rw [Real.log_sqrt (by linarith)] <;> ring
      rw [hsqrt]
      exact mul_le_mul_of_nonpos_right h_exp h_log_rho
    exact (Real.log_le_log_iff h_pos1 h_pos2).mp h_log
  by_cases h_case : |d 1| ≥ 1 / Real.sqrt 5
  · -- Non-vertical case
    let m := -d 0 / d 1
    have h_slope_bound : |m| ≤ 2 := by
      have h := slope_bound_from_direction d hd h_case
      have h_eq : |m| = |(-d 0 / d 1)| := by
        simp [m] <;> ring
      rw [h_eq]
      exact h
    let T : WZ1VerticalTrapezoid :=
      { left := z0
        right := z0 + L
        left_lt_right := by linarith
        slope := m
        intercept := 0
        height := rho
        height_pos := hrho }
    have h_T_height : T.height = rho := by rfl
    have h_T_slope : |T.slope| ≤ 2 := h_slope_bound
    have h_T_length : T.length = L := by
      simp [T, WZ1VerticalTrapezoid.length] <;> ring
    have h_approx : ∀ z ∈ T.core, z ∈ Z → |f z - T.affine z| ≤ rho := by
      intro z hz_core hz_Z
      have h_strip_z := h_strip z hz_Z
      have h_affine : T.affine z = m * z := by
        simp [T, WZ1VerticalTrapezoid.affine, m] <;> ring
      rw [h_affine]
      have h_eq2 : f z - m * z = f z - (-(d 0 / d 1)) * z := by
        simp [m] <;> ring
      rw [h_eq2]
      exact strip_affine_approximation d rho hrho f z h_case h_strip_z
    have h_z0_in_core : z0 ∈ T.core := by
      simp [T, WZ1VerticalTrapezoid.core] <;> linarith
    exact ⟨T, h_T_height, h_T_slope,
      by rw [h_T_length] <;> linarith,
      by rw [h_T_length] <;> exact hL_le_sqrt,
      h_approx, z0, hz0, h_z0_in_core⟩
  · -- Nearly-vertical case
    have h_d1_small : |d 1| < 1 / Real.sqrt 5 := by
      exact lt_of_not_ge h_case
    set C := (1 : ℝ) / (5 * Real.sqrt 3) with hC
    set c := (1 : ℝ) / Real.sqrt 5 with hc_def
    have hc_pos : 0 < c := by positivity
    have h_gap : c ≤ |d 0| - |d 1| := near_vertical_gap d hd h_d1_small
    have h_const : 2 * C / c ≤ 1 := near_vertical_const
    let T : WZ1VerticalTrapezoid :=
      { left := z0
        right := z0 + L
        left_lt_right := by linarith
        slope := 0
        intercept := f z0
        height := rho
        height_pos := hrho }
    have h_T_height : T.height = rho := by rfl
    have h_T_slope : |T.slope| ≤ 2 := by
      simp [T] <;> norm_num
    have h_T_length : T.length = L := by
      simp [T, WZ1VerticalTrapezoid.length] <;> ring
    have h_approx : ∀ z ∈ T.core, z ∈ Z → |f z - T.affine z| ≤ rho := by
      intro z hz_core hz_Z
      have h_C_rho : C * rho = rho / (5 * Real.sqrt 3) := by
        simp [C] <;> ring
      have h_strip_z : |d 0 * z + d 1 * f z| ≤ C * rho := by
        rw [h_C_rho]
        exact h_strip z hz_Z
      have h_strip0 : |d 0 * z0 + d 1 * f z0| ≤ C * rho := by
        rw [h_C_rho]
        exact h_strip z0 hz0
      have h_affine : T.affine z = f z0 := by
        simp [T, WZ1VerticalTrapezoid.affine] <;> ring
      rw [h_affine]
      exact constant_approximation_near_vertical d rho C c hrho hc_pos f hf_lip
        h_gap h_const z0 z h_strip0 h_strip_z
    have h_z0_in_core : z0 ∈ T.core := by
      simp [T, WZ1VerticalTrapezoid.core] <;> linarith
    exact ⟨T, h_T_height, h_T_slope,
      by rw [h_T_length] <;> linarith,
      by rw [h_T_length] <;> exact hL_le_sqrt,
      h_approx, z0, hz0, h_z0_in_core⟩

end Kakeya.Assouad
