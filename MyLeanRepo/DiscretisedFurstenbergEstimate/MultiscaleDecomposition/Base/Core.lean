module

/-
Copyright (c) 2024 The Discretised Furstenberg Estimate Team.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raven Team
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.GeneralAdapter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils

@[expose] public section

noncomputable section

namespace DirecretisedFurstenbergEstimate

namespace MultiscaleDecomposition

/-! # Core definitions for multiscale decomposition

This module contains the foundational definitions:
- `dyadicSquare`, `homothetyS`: dyadic geometry
- `IsSetBetweenScales`, `IsRegularBetweenScales`: multiscale set properties
- `IsUniform`: uniform covering at dyadic scales
- `codeFunction`: the branching function of a uniform set
- `slope`, `linearInterpolant`, `EpsLinear`, `EpsSuperlinear`: function approximation
- Basic lemmas: `slope_convex`, `largest_slope_eq`, `merged_superlinear`
-/

-- ======================================================================
-- Dyadic squares and homotheties
-- ======================================================================

/-- A dyadic square at scale `Δ` with lower-left corner `(i*Δ, j*Δ)`. -/
def dyadicSquare (Δ : ℝ) (i j : ℤ) : Set EuclideanPlane :=
  {p | p 0 ∈ Set.Ico (i * Δ) ((i + 1) * Δ) ∧ p 1 ∈ Set.Ico (j * Δ) ((j + 1) * Δ)}

/-- The homothety mapping `dyadicSquare Δ i j` to `[0,1)^2`. -/
def homothetyS (Δ : ℝ) (i j : ℤ) : EuclideanPlane → EuclideanPlane :=
  fun p =>
    let lower : EuclideanPlane :=
      WithLp.toLp (2 : ENNReal)
        (fun k : Fin 2 => if k = 0 then (i : ℝ) * Δ else (j : ℝ) * Δ)
    (1 / Δ : ℝ) • (p - lower)

-- ======================================================================
-- Between-scales set properties
-- ======================================================================

/-- `P` is an `(s,C)`-set between scales `δ` and `Δ` if, for every dyadic
`Δ`-square `Q` intersecting `P`, the rescaled set `S_Q(P ∩ Q)` is a
`(δ/Δ, s, C)`-set. See OS Definition around line 941. -/
def IsSetBetweenScales (P : Set EuclideanPlane) (δ Δ s C : ℝ) : Prop :=
  0 < δ ∧ 0 < Δ ∧ δ ≤ Δ ∧ 0 ≤ s ∧ 0 < C ∧
  ∀ (i j : ℤ), (P ∩ dyadicSquare Δ i j).Nonempty →
    IsDeltaSSet (δ / Δ) s C (homothetyS Δ i j '' (P ∩ dyadicSquare Δ i j))

/-- `P` is `(s,C,K)`-regular between scales `δ` and `Δ` if it is an
`(s,C)`-set between those scales and additionally satisfies the half-scale
covering bound `|S_Q(P∩Q)|_{(δ/Δ)^{1/2}} ≤ K * (δ/Δ)^{-s/2}`.
See OS Definition around line 942. -/
def IsRegularBetweenScales (P : Set EuclideanPlane) (δ Δ s C K : ℝ) : Prop :=
  IsSetBetweenScales P δ Δ s C ∧ 0 < K ∧
  ∀ (i j : ℤ), (P ∩ dyadicSquare Δ i j).Nonempty →
    (Metric.externalCoveringNumber (Real.sqrt (δ / Δ)).toNNReal
       (homothetyS Δ i j '' (P ∩ dyadicSquare Δ i j)) : ENNReal) ≤
      ENNReal.ofReal (K * Real.rpow (δ / Δ) (-s / 2))

-- ======================================================================
-- Uniform sets
-- ======================================================================

/-- `P` is `(Δ^i)_{i=0}^{m-1}`-uniform if there is a sequence `N` such that
for every `i < m` and every dyadic `Δ^i`-square `Q` intersecting `P`, the
`Δ^(i+1)`-covering number of `P ∩ Q` equals `N i`.
See OS Definition 950. -/
def IsUniform (P : Set EuclideanPlane) (m : ℕ) (Δ : ℝ) (N : ℕ → ℕ) : Prop :=
  0 < Δ ∧ Δ < 1 ∧ P.Nonempty ∧
  (∀ i < m, N i ≥ 1) ∧
  ∀ (i : ℕ), i < m → ∀ (a b : ℤ),
    (P ∩ dyadicSquare (Δ ^ i) a b).Nonempty →
    (Metric.externalCoveringNumber (Δ ^ (i + 1)).toNNReal
       (P ∩ dyadicSquare (Δ ^ i) a b) : ENNReal) =
      (↑(N i) : ENNReal)

-- ======================================================================
-- Code function
-- ======================================================================

/-- The partial sums of the code function:
`f(j) = Σ_{i=0}^{j-1} log(N i) / log(1/Δ)`. -/
def codeFunctionPartialSum (m : ℕ) (Δ : ℝ) (N : ℕ → ℕ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, Real.log (N i) / Real.log (1 / Δ)

/-- The code function `f_P : [0,m] → ℝ` associated to a uniform set,
linearly interpolated between integer points. See OS line 1144. -/
def codeFunction (m : ℕ) (Δ : ℝ) (N : ℕ → ℕ) (x : ℝ) : ℝ :=
  if x ≤ 0 then 0
  else if x ≥ m then codeFunctionPartialSum m Δ N m
  else
    let j : ℕ := ⌊x⌋₊
    let t : ℝ := x - j
    codeFunctionPartialSum m Δ N j +
      t * (codeFunctionPartialSum m Δ N (j + 1) - codeFunctionPartialSum m Δ N j)

-- ======================================================================
-- ε-linear and ε-superlinear functions
-- ======================================================================

/-- The slope of `f` on `[a,b]`: `s_f(a,b) = (f(b)-f(a))/(b-a)`. -/
def slope (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (f b - f a) / (b - a)

/-- The linear interpolant of `f` on `[a,b]`:
`L_{f,a,b}(x) = f(a) + s_f(a,b) * (x-a)`. -/
def linearInterpolant (f : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  fun x => f a + slope f a b * (x - a)

/-- `f` is `ε`-linear on `[a,b]` if it stays within `ε(b-a)` of its
linear interpolant. See OS Definition 1149. -/
def EpsLinear (f : ℝ → ℝ) (a b ε : ℝ) : Prop :=
  a < b ∧ ∀ x ∈ Set.Icc a b, |f x - linearInterpolant f a b x| ≤ ε * (b - a)

/-- `f` is `ε`-superlinear on `[a,b]` if it stays above its linear
interpolant minus `ε(b-a)`. See OS Definition 1162. -/
def EpsSuperlinear (f : ℝ → ℝ) (a b ε : ℝ) : Prop :=
  a < b ∧ ∀ x ∈ Set.Icc a b, f x ≥ linearInterpolant f a b x - ε * (b - a)

-- ======================================================================
-- Basic properties
-- ======================================================================

/-- ε-linear implies ε-superlinear. -/
lemma EpsLinear.toSuperlinear {f : ℝ → ℝ} {a b ε : ℝ}
    (h : EpsLinear f a b ε) : EpsSuperlinear f a b ε := by
  have h1 : a < b := h.1
  have h2 : ∀ x ∈ Set.Icc a b, |f x - linearInterpolant f a b x| ≤ ε * (b - a) := h.2
  refine' ⟨h1, _⟩
  intro x hx
  have h3 : |f x - linearInterpolant f a b x| ≤ ε * (b - a) := h2 x hx
  have h4 : -(ε * (b - a)) ≤ f x - linearInterpolant f a b x := by
    linarith [abs_le.mp h3]
  linarith

/-- The linear interpolant agrees with f at the endpoints. -/
lemma linearInterpolant_endpoints (f : ℝ → ℝ) (a b : ℝ) (h : a < b) :
    linearInterpolant f a b a = f a ∧ linearInterpolant f a b b = f b := by
  constructor
  · simp [linearInterpolant, slope] <;> ring
  · simp [linearInterpolant, slope]
    <;> field_simp [show (b - a : ℝ) ≠ 0 by linarith] <;> ring

/-- An ε-superlinear function with non-negative slope has f(x) ≥ f(a) - ε(b-a). -/
lemma EpsSuperlinear.lower_bound {f : ℝ → ℝ} {a b ε : ℝ}
    (h : EpsSuperlinear f a b ε) (hslope : 0 ≤ slope f a b) :
    ∀ x ∈ Set.Icc a b, f x ≥ f a - ε * (b - a) := by
  intro x hx
  have h1 : f x ≥ linearInterpolant f a b x - ε * (b - a) := h.2 x hx
  have h2 : linearInterpolant f a b x ≥ f a := by
    have h3 : x - a ≥ 0 := by exact sub_nonneg.mpr (hx.1)
    have h4 : slope f a b * (x - a) ≥ 0 := by positivity
    simpa [linearInterpolant] using h4
  linarith

-- ======================================================================
-- Helper lemmas for combinatorialKaufman
-- ======================================================================

/-- Slope convexity: for a < x < b, slope(f,a,b) is a weighted average
    of slope(f,a,x) and slope(f,x,b). -/
lemma slope_convex (f : ℝ → ℝ) {a x b : ℝ} (hax : a < x) (hxb : x < b) :
    slope f a b =
      ((x - a) / (b - a)) * slope f a x +
      ((b - x) / (b - a)) * slope f x b := by
  have h1 : b - a ≠ 0 := by linarith
  have h2 : x - a ≠ 0 := by linarith
  have h3 : b - x ≠ 0 := by linarith
  dsimp only [slope]
  field_simp [h1, h2, h3] <;> ring

/-- slope(f, x, b) is continuous on (-∞, b). -/
lemma slope_right_continuous (f : ℝ → ℝ) (hf : Continuous f) (b : ℝ) :
    ContinuousOn (fun x : ℝ ↦ slope f x b) (Set.Iio b) := by
  have h1 : Continuous (fun x : ℝ ↦ f b - f x) := by fun_prop
  have h2 : Continuous (fun x : ℝ ↦ b - x) := by fun_prop
  have h3 : ∀ (x : ℝ), x ∈ Set.Iio b → b - x ≠ 0 := by
    intro x hx; simp only [Set.mem_Iio] at hx; linarith
  exact h1.continuousOn.div h2.continuousOn h3

/-- Given a < c < b, slope(a,b) > s, slope(c,b) < s, f continuous,
    there exists a largest x₀ ∈ [a,c] with slope(x₀,b) = s,
    and slope(y,b) ≤ s for all y ∈ (x₀, c]. -/
lemma largest_slope_eq (f : ℝ → ℝ) (hf : Continuous f) {a c b s : ℝ}
    (hac : a < c) (hcb : c < b)
    (h1 : slope f a b > s) (h2 : slope f c b < s) :
    ∃ (x0 : ℝ), a ≤ x0 ∧ x0 ≤ c ∧ slope f x0 b = s ∧
      ∀ y ∈ Set.Ioc x0 c, slope f y b ≤ s := by
  let g : ℝ → ℝ := fun x ↦ slope f x b
  have hg_cont : ContinuousOn g (Set.Icc a c) := by
    apply ContinuousOn.mono (s := Set.Iio b)
    · exact slope_right_continuous f hf b
    · intro x hx; simp only [Set.mem_Icc, Set.mem_Iio] at *; linarith
  have h_s_in_image : s ∈ g '' Set.Icc a c := by
    have h_ivt : Set.Icc (g c) (g a) ⊆ g '' Set.Icc a c :=
      intermediate_value_Icc' hac.le hg_cont
    have h_s_in : s ∈ Set.Icc (g c) (g a) := by
      exact ⟨le_of_lt h2, le_of_lt h1⟩
    exact h_ivt h_s_in
  rcases h_s_in_image with ⟨xmid, hxmid, hxmid_eq⟩
  let S : Set ℝ := Set.Icc a c ∩ g ⁻¹' {s}
  have hS_nonempty : S.Nonempty := ⟨xmid, hxmid, hxmid_eq⟩
  have hS_closed : IsClosed S :=
    hg_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hS_bdd : BddAbove S := ⟨c, fun x hx ↦ hx.1.2⟩
  let x0 := sSup S
  have hx0_in_S : x0 ∈ S := hS_closed.csSup_mem hS_nonempty hS_bdd
  have hx0_Icc : x0 ∈ Set.Icc a c := hx0_in_S.1
  have h_slope : g x0 = s := hx0_in_S.2
  have h_main : ∀ y ∈ Set.Ioc x0 c, g y ≤ s := by
    intro y hy
    by_contra h
    push Not at h
    have h_gt : g y > s := h
    have h_y_lt_c : y < c := by
      have h_y_le_c : y ≤ c := hy.2
      by_contra h_eq
      have : y = c := by linarith
      rw [this] at h_gt
      exact False.elim (not_lt.mpr (le_of_lt h2) h_gt)
    have h_cont2 : ContinuousOn g (Set.Icc y c) := by
      apply ContinuousOn.mono (s := Set.Iio b)
      · exact slope_right_continuous f hf b
      · intro z hz; simp only [Set.mem_Icc, Set.mem_Iio] at *; linarith
    have h_s_in_image2 : s ∈ g '' Set.Icc y c := by
      have h_ivt : Set.Icc (g c) (g y) ⊆ g '' Set.Icc y c :=
        intermediate_value_Icc' (by linarith) h_cont2
      have h_s_in : s ∈ Set.Icc (g c) (g y) := by
        exact ⟨le_of_lt h2, le_of_lt h_gt⟩
      exact h_ivt h_s_in
    rcases h_s_in_image2 with ⟨z, hz, hz_eq⟩
    have hz_in_Icc_yc : z ∈ Set.Icc y c := hz
    have hz_ge_y : y ≤ z := hz_in_Icc_yc.1
    have hz_le_c : z ≤ c := hz_in_Icc_yc.2
    have hz_ne_y : z ≠ y := by
      intro eq; rw [eq] at hz_eq; exact False.elim (not_le.mpr h_gt (le_of_eq hz_eq))
    have hz_gt_y : y < z := lt_of_le_of_ne hz_ge_y hz_ne_y.symm
    have hz_ge_x0 : x0 ≤ z := by linarith [hy.1]
    have h_a_le_z : a ≤ z := by linarith [hx0_Icc.1, hz_ge_x0]
    have hz_in_S : z ∈ S := ⟨⟨h_a_le_z, hz_le_c⟩, hz_eq⟩
    have hz_le_x0 : z ≤ x0 := le_csSup hS_bdd hz_in_S
    have hz_eq_x0 : z = x0 := by linarith
    rw [hz_eq_x0] at hz_gt_y
    exact False.elim (not_lt.mpr (le_of_lt hy.1) hz_gt_y)
  exact ⟨x0, hx0_Icc.1, hx0_Icc.2, h_slope, h_main⟩

/-- If [c_k, d_k] is ε-linear with slope < s, and x0 < c_k with slope(x0,d_k)=s
    and slope(y,d_k) ≤ s for y ∈ (x0, c_k], then [x0,d_k] is ε-superlinear at slope s. -/
lemma merged_superlinear (f : ℝ → ℝ) {x0 c_k d_k s ε : ℝ}
    (hε : 0 ≤ ε)
    (h_x0_lt_c : x0 < c_k) (h_c_lt_d : c_k < d_k)
    (h_slope : slope f x0 d_k = s)
    (h_slope_c : slope f c_k d_k < s)
    (h_eps_lin : EpsLinear f c_k d_k ε)
    (h_mon : ∀ y ∈ Set.Ioc x0 c_k, slope f y d_k ≤ s) :
    EpsSuperlinear f x0 d_k ε := by
  have h_x0_lt_d : x0 < d_k := by linarith
  constructor
  · exact h_x0_lt_d
  intro x hx
  have h_x_ge_x0 : x0 ≤ x := hx.1
  have h_x_le_d : x ≤ d_k := hx.2
  by_cases h_case : x ≤ c_k
  · -- Case 1: x ∈ [x0, c_k]
    by_cases h_eq : x = x0
    · rw [h_eq]
      have h_lin : linearInterpolant f x0 d_k x0 = f x0 := by simp [linearInterpolant]
      rw [h_lin]
      have h : 0 ≤ ε * (d_k - x0) := by positivity
      linarith
    · have h_x_gt_x0 : x0 < x := by exact lt_of_le_of_ne hx.1 (Ne.symm h_eq)
      have h_slope_x : slope f x d_k ≤ s := h_mon x ⟨h_x_gt_x0, h_case⟩
      have hden : 0 < d_k - x0 := by linarith
      have hpos1 : 0 < x - x0 := by linarith
      set w1 := (x - x0) / (d_k - x0) with hw1_def
      set w2 := (d_k - x) / (d_k - x0) with hw2_def
      have hw1_pos : 0 < w1 := by positivity
      have hw2_nonneg : 0 ≤ w2 := by positivity
      have hwsum : w1 + w2 = 1 := by
        simp [hw1_def, hw2_def] <;> field_simp [hden.ne'] <;> ring
      have h_x_lt_d : x < d_k := by
        by_contra h'; have : x = d_k := by linarith
        rw [this] at h_x_gt_x0; linarith
      have h_conv : slope f x0 d_k = w1 * slope f x0 x + w2 * slope f x d_k :=
        slope_convex f h_x_gt_x0 h_x_lt_d
      have h_eq1 : s = w1 * slope f x0 x + w2 * slope f x d_k := by
        rw [h_slope] at h_conv; exact h_conv
      have h_slope_x0x : slope f x0 x ≥ s := by
        have h_ineq1 : w1 * slope f x0 x + w2 * slope f x d_k ≤ w1 * slope f x0 x + w2 * s := by gcongr
        have h_ineq2 : s ≤ w1 * slope f x0 x + w2 * s := by
          have h_eq2 : w1 * slope f x0 x + w2 * slope f x d_k = s := h_eq1.symm
          linarith
        have h_ineq3 : s - w2 * s ≤ w1 * slope f x0 x := by linarith
        have h_ineq4 : (1 - w2) * s ≤ w1 * slope f x0 x := by
          have h : (1 - w2) * s = s - w2 * s := by ring
          rw [h]; exact h_ineq3
        have h_ineq5 : w1 * s ≤ w1 * slope f x0 x := by
          have h6 : 1 - w2 = w1 := by linarith [hwsum]
          rw [h6] at h_ineq4; exact h_ineq4
        have h7 : 0 < w1 := hw1_pos
        have h9 : s ≤ slope f x0 x := by
          calc s = (w1 * s) / w1 := by field_simp [h7.ne'] <;> ring
               _ ≤ (w1 * slope f x0 x) / w1 := by gcongr
               _ = slope f x0 x := by field_simp [h7.ne'] <;> ring
        exact h9
      have h_f_ge : f x ≥ f x0 + s * (x - x0) := by
        dsimp only [slope] at h_slope_x0x
        have h : (f x - f x0) / (x - x0) ≥ s := h_slope_x0x
        have h2 : f x - f x0 ≥ s * (x - x0) := by
          calc (f x - f x0)
            = ((f x - f x0) / (x - x0)) * (x - x0) := by field_simp [hpos1.ne'] <;> ring
          _ ≥ s * (x - x0) := by gcongr
        linarith
      have h_lin : linearInterpolant f x0 d_k x = f x0 + slope f x0 d_k * (x - x0) := by
        simp [linearInterpolant]
      rw [h_lin, h_slope]
      have h_abs_nonneg : 0 ≤ ε * (d_k - x0) := by positivity
      linarith
  · -- Case 2: x ∈ (c_k, d_k]
    have h_x_gt_c : c_k < x := by linarith
    have h_eps_super : EpsSuperlinear f c_k d_k ε := h_eps_lin.toSuperlinear
    have h_alt_form : f x ≥ f d_k - slope f c_k d_k * (d_k - x) - ε * (d_k - c_k) := by
      have h_super := h_eps_super.2 x ⟨by linarith, h_x_le_d⟩
      have h_eq : f c_k + slope f c_k d_k * (x - c_k) =
               f d_k - slope f c_k d_k * (d_k - x) := by
        dsimp only [slope]
        field_simp [show (d_k - c_k : ℝ) ≠ 0 by linarith] <;> ring
      have h_lin : linearInterpolant f c_k d_k x = f c_k + slope f c_k d_k * (x - c_k) := by
        simp [linearInterpolant]
      rw [h_lin] at h_super
      rw [h_eq] at h_super
      exact h_super
    have h10 : f d_k = f x0 + s * (d_k - x0) := by
      dsimp only [slope] at h_slope
      have hden : d_k - x0 ≠ 0 := by linarith
      field_simp [hden] at h_slope ⊢ <;> linarith
    have h_dk_x_nonneg : 0 ≤ d_k - x := by linarith
    have h14 : ε * (d_k - c_k) ≤ ε * (d_k - x0) := by
      have h15 : d_k - c_k ≤ d_k - x0 := by linarith
      gcongr
    have h_main : f x ≥ f x0 + s * (x - x0) - ε * (d_k - x0) := by
      calc f x
        ≥ f d_k - slope f c_k d_k * (d_k - x) - ε * (d_k - c_k) := h_alt_form
      _ ≥ f d_k - s * (d_k - x) - ε * (d_k - c_k) := by
        have h16 : slope f c_k d_k < s := h_slope_c
        have h17 : 0 ≤ d_k - x := h_dk_x_nonneg
        have h18 : (s - slope f c_k d_k) * (d_k - x) ≥ 0 := by
          have h19 : 0 < s - slope f c_k d_k := by linarith
          exact mul_nonneg (by linarith) h17
        have h20 : -slope f c_k d_k * (d_k - x) ≥ -s * (d_k - x) := by
          have h21 : -slope f c_k d_k * (d_k - x) - (-s * (d_k - x)) = (s - slope f c_k d_k) * (d_k - x) := by ring
          linarith
        linarith
      _ = f x0 + s * (d_k - x0) - s * (d_k - x) - ε * (d_k - c_k) := by rw [h10]
      _ = f x0 + s * (x - x0) - ε * (d_k - c_k) := by ring
      _ ≥ f x0 + s * (x - x0) - ε * (d_k - x0) := by linarith [h14]
    have h_lin : linearInterpolant f x0 d_k x = f x0 + slope f x0 d_k * (x - x0) := by
      simp [linearInterpolant]
    rw [h_lin, h_slope]
    exact h_main

end MultiscaleDecomposition

end DirecretisedFurstenbergEstimate

end
