module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.IntervalUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.TubeNullNonuniform
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.TubeNullAdapter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.MainAssembly
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Uniform tube-null lemma via Arzelà-Ascoli compactness

Given the non-uniform quantitative Rademacher theorem (for each monotone f
there exists some τ_f), we prove a uniform τ using compactness of the space
of 2-Lipschitz monotone functions on [0,1] with f(0)=0.

Then we scale to [0,m] and convert to the `TubeNullResult` format.
-/

noncomputable section

namespace CombinatorialKaufman.TubeNull

open MeasureTheory Set Metric Filter Finset BoundedContinuousFunction

/-! ========================================================================
   Compactness setup
   ======================================================================== -/

/-- The unit interval [0,1] as a subtype. -/
abbrev UI : Type := ↥(Set.Icc (0 : ℝ) 1)

/-- Bounded continuous functions on the unit interval. -/
abbrev BCF := BoundedContinuousFunction UI ℝ

/-- The point 0 in UI. -/
def zeroUI : UI := ⟨0, by simp⟩

/-- The point 1 in UI. -/
def oneUI : UI := ⟨1, by simp⟩

/-- Extend a BCF on [0,1] constantly to all of ℝ. -/
def extend (f : BCF) : ℝ → ℝ := fun x =>
  if h : 0 ≤ x ∧ x ≤ 1 then f ⟨x, h⟩
  else if x < 0 then f zeroUI
  else f oneUI

lemma extend_at {f : BCF} {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) :
    extend f x = f ⟨x, hx⟩ := by
  simp [extend, hx]

/-- Transfer ε-linearity: if f is (ε/2)-linear on [c,d] and g is uniformly
    close enough to f, then g is ε-linear on [c,d]. -/
lemma transfer_epsilon_linear {f g : BCF} {c d : ℝ}
    (hcd : c < d) (hc : 0 ≤ c) (hd : d ≤ 1)
    {ε : ℝ} (hε : 0 < ε)
    (h_f_lin : EpsilonLinear (extend f) (ε / 2) c d)
    (h_close : ‖g - f‖ < ε * (d - c) / 8) :
    EpsilonLinear (extend g) ε c d := by
  let L := d - c
  have hL_pos : 0 < L := by linarith
  let c' : UI := ⟨c, ⟨hc, by linarith⟩⟩
  let d' : UI := ⟨d, ⟨by linarith, hd⟩⟩
  have h_x_in : ∀ (x : ℝ), x ∈ Set.Icc c d → 0 ≤ x ∧ x ≤ 1 := by
    intro x hx
    have h1 : 0 ≤ x := le_trans hc hx.1
    have h2 : x ≤ 1 := le_trans hx.2 hd
    exact ⟨h1, h2⟩
  have h_eval_g : ∀ (x : ℝ) (hx : x ∈ Set.Icc c d), extend g x = g ⟨x, h_x_in x hx⟩ := by
    intro x hx
    simp [extend, h_x_in x hx]
  have h_eval_f : ∀ (x : ℝ) (hx : x ∈ Set.Icc c d), extend f x = f ⟨x, h_x_in x hx⟩ := by
    intro x hx
    simp [extend, h_x_in x hx]
  have h1 : ∀ (x : ℝ), x ∈ Set.Icc c d → |extend g x - extend f x| ≤ ‖g - f‖ := by
    intro x hx
    rw [h_eval_g x hx, h_eval_f x hx]
    have h : |(g - f) ⟨x, h_x_in x hx⟩| ≤ ‖g - f‖ :=
      BoundedContinuousFunction.norm_coe_le_norm (g - f) _
    simpa using h
  have hc' : c ∈ Set.Icc c d := ⟨by linarith, by linarith⟩
  have hd' : d ∈ Set.Icc c d := ⟨by linarith, by linarith⟩
  have h_diff_c : |extend f c - extend g c| ≤ ‖g - f‖ := by
    rw [h_eval_f c hc', h_eval_g c hc']
    have h : |(f - g) c'| ≤ ‖f - g‖ := BoundedContinuousFunction.norm_coe_le_norm (f - g) c'
    have h' : ‖f - g‖ = ‖g - f‖ := by
      exact norm_sub_rev f g
    rw [h'] at h
    simpa using h
  have h_diff_d : |extend f d - extend g d| ≤ ‖g - f‖ := by
    rw [h_eval_f d hd', h_eval_g d hd']
    have h : |(f - g) d'| ≤ ‖f - g‖ := BoundedContinuousFunction.norm_coe_le_norm (f - g) d'
    have h' : ‖f - g‖ = ‖g - f‖ := by
      exact norm_sub_rev f g
    rw [h'] at h
    simpa using h
  have h_slope_diff : |chordSlope (extend f) c d - chordSlope (extend g) c d| ≤ 2 * ‖g - f‖ / L := by
    dsimp only [chordSlope]
    have h_abs : |((extend f d - extend f c) - (extend g d - extend g c)) / L| ≤ (2 * ‖g - f‖) / L := by
      rw [abs_div, abs_of_pos hL_pos]
      have h_inner : |(extend f d - extend f c) - (extend g d - extend g c)| ≤ 2 * ‖g - f‖ := by
        have h_eq : (extend f d - extend f c) - (extend g d - extend g c) =
            (extend f d - extend g d) - (extend f c - extend g c) := by ring
        rw [h_eq]
        have h : |(extend f d - extend g d) - (extend f c - extend g c)| ≤
            |extend f d - extend g d| + |extend f c - extend g c| := by
          exact abs_sub _ _
        linarith
      gcongr
    have h_goal : (extend f d - extend f c) / L - (extend g d - extend g c) / L =
        ((extend f d - extend f c) - (extend g d - extend g c)) / L := by
      field_simp [hL_pos.ne'] <;> ring
    rw [h_goal]
    exact h_abs
  have h2 : ∀ (x : ℝ), x ∈ Set.Icc c d →
      |chordValue (extend f) c d x - chordValue (extend g) c d x| ≤ 3 * ‖g - f‖ := by
    intro x hx
    have h_xc_nonneg : 0 ≤ x - c := by linarith [hx.1]
    have h_xc_le : x - c ≤ L := by linarith [hx.2]
    have h_eq2 : chordValue (extend f) c d x - chordValue (extend g) c d x =
        (extend f c - extend g c) + (chordSlope (extend f) c d - chordSlope (extend g) c d) * (x - c) := by
      simp [chordValue, chordSlope] <;> ring
    rw [h_eq2]
    let A := extend f c - extend g c
    let B := (chordSlope (extend f) c d - chordSlope (extend g) c d) * (x - c)
    have h_tri : |A + B| ≤ |A| + |B| := by
      exact IsAbsoluteValue.abv_add abs A B
    calc |A + B|
      ≤ |A| + |B| := h_tri
    _ = |A| + |B| := by rfl
    _ = |extend f c - extend g c| + |chordSlope (extend f) c d - chordSlope (extend g) c d| * |x - c| := by
        simp only [A, B, abs_mul] <;> rfl
    _ ≤ ‖g - f‖ + (2 * ‖g - f‖ / L) * (x - c) := by
        gcongr <;> rw [abs_of_nonneg h_xc_nonneg] <;> linarith
    _ ≤ ‖g - f‖ + 2 * ‖g - f‖ := by
        have h : (2 * ‖g - f‖ / L) * (x - c) ≤ 2 * ‖g - f‖ := by
          calc (2 * ‖g - f‖ / L) * (x - c)
            ≤ (2 * ‖g - f‖ / L) * L := by gcongr <;> linarith
          _ = 2 * ‖g - f‖ := by field_simp [hL_pos.ne'] <;> ring
        linarith
    _ = 3 * ‖g - f‖ := by ring
  have h_goal : ∀ (x : ℝ), x ∈ Set.Icc c d →
      |extend g x - chordValue (extend g) c d x| ≤ ε * (d - c) := by
    intro x hx
    set a := extend g x - extend f x with ha_def
    set b := extend f x - chordValue (extend f) c d x with hb_def
    set e := chordValue (extend f) c d x - chordValue (extend g) c d x with he_def
    have h_eq : extend g x - chordValue (extend g) c d x = a + b + e := by
      dsimp only [a, b, e] <;> ring
    have h_tri1 : |a + b + e| ≤ |a + b| + |e| := by
      exact IsAbsoluteValue.abv_add abs (a + b) e
    have h_tri2 : |a + b| ≤ |a| + |b| := by
      exact IsAbsoluteValue.abv_add abs a b
    have h_tri : |a + b + e| ≤ |a| + |b| + |e| := by
      calc |a + b + e| ≤ |a + b| + |e| := h_tri1
           _ ≤ |a| + |b| + |e| := by linarith
    have h_abs1 : |a| ≤ ‖g - f‖ := h1 x hx
    have h_abs2 : |b| ≤ (ε / 2) * L := h_f_lin x hx
    have h_abs3 : |e| ≤ 3 * ‖g - f‖ := h2 x hx
    have h_main : |extend g x - chordValue (extend g) c d x| < ε * L := by
      rw [h_eq]
      calc |a + b + e|
        ≤ |a| + |b| + |e| := h_tri
      _ ≤ ‖g - f‖ + (ε / 2) * L + 3 * ‖g - f‖ := by linarith
      _ = (ε / 2) * L + 4 * ‖g - f‖ := by ring
      _ < ε * L := by
        have h4 : ‖g - f‖ < ε * L / 8 := h_close
        linarith
    have h_final : |extend g x - chordValue (extend g) c d x| ≤ ε * (d - c) := by
      simpa [L] using h_main.le
    exact h_final
  exact h_goal

/-! ========================================================================
   Compact set of 2-Lipschitz monotone functions with f(0)=0
   ======================================================================== -/

/-- The set of 2-Lipschitz, monotone functions on [0,1] with f(0)=0. -/
def K : Set BCF :=
  {f | (∀ (x y : UI), |f x - f y| ≤ 2 * |(x : ℝ) - (y : ℝ)|) ∧
       (∀ (x y : UI), (x : ℝ) ≤ (y : ℝ) → f x ≤ f y) ∧
       f zeroUI = 0}

lemma K_closed : IsClosed K := by
  let S1 : UI × UI → Set BCF := fun p =>
    {f | |f p.1 - f p.2| ≤ 2 * |(p.1 : ℝ) - (p.2 : ℝ)|}
  let S2 : UI × UI → Set BCF := fun p =>
    {f | (p.1 : ℝ) ≤ (p.2 : ℝ) → f p.1 ≤ f p.2}
  have hS1 : ∀ p, IsClosed (S1 p) := by
    intro p
    exact isClosed_le (by continuity) (by continuity)
  have hS2 : ∀ p, IsClosed (S2 p) := by
    intro p
    by_cases h : (p.1 : ℝ) ≤ (p.2 : ℝ)
    · have h' : S2 p = {f : BCF | f p.1 ≤ f p.2} := by
        ext f
        simp only [S2, Set.mem_setOf_eq]
        <;> simp [h] <;> tauto
      rw [h']
      exact isClosed_le (by continuity) (by continuity)
    · have h' : S2 p = Set.univ := by
        ext f
        simp only [S2, Set.mem_setOf_eq, Set.mem_univ]
        <;> tauto
      rw [h']
      exact isClosed_univ
  have h1 : IsClosed (⋂ p, S1 p) := isClosed_iInter hS1
  have h2 : IsClosed (⋂ p, S2 p) := isClosed_iInter hS2
  have h3 : IsClosed {f : BCF | f zeroUI = 0} := by
    have h_cont : Continuous (fun f : BCF => f zeroUI) := by fun_prop
    exact isClosed_eq h_cont continuous_const
  have hK_eq : K = (⋂ p, S1 p) ∩ (⋂ p, S2 p) ∩ {f | f zeroUI = 0} := by
    ext f
    simp only [K, S1, S2, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    <;> aesop
  rw [hK_eq]
  exact h1.inter h2 |>.inter h3

lemma K_in_s : ∀ (f : BCF) (x : UI), f ∈ K → f x ∈ Set.Icc (-2 : ℝ) 2 := by
  intro f x hf
  have h_lip : ∀ (x y : UI), |f x - f y| ≤ 2 * |(x : ℝ) - (y : ℝ)| := hf.1
  have h_zero : f zeroUI = 0 := hf.2.2
  have h_abs : |f x| ≤ 2 := by
    have h : |f x| = |f x - f zeroUI| := by rw [h_zero] <;> ring_nf
    rw [h]
    have h2 := h_lip x zeroUI
    have h3 : |(x : ℝ) - (zeroUI : ℝ)| = x.val := by
      have h4 : 0 ≤ x.val := x.prop.1
      simp [zeroUI, abs_of_nonneg h4] <;> linarith
    rw [h3] at h2
    have h5 : x.val ≤ 1 := x.prop.2
    linarith
  exact ⟨by linarith [abs_le.mp h_abs], by linarith [abs_le.mp h_abs]⟩

lemma K_equicont : Equicontinuous (fun (i : {f // f ∈ K}) => (i.val : UI → ℝ)) := by
  have h_main : ∀ (x : UI), EquicontinuousAt (fun (i : {f // f ∈ K}) => (i.val : UI → ℝ)) x := by
    intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    refine ⟨ε / 2, by positivity, fun y hy i => ?_⟩
    have h_lip : ∀ (a b : UI), |i.val a - i.val b| ≤ 2 * |(a : ℝ) - (b : ℝ)| := i.prop.1
    have h_dist : dist y x < ε / 2 := hy
    have h_abs : |(y : ℝ) - (x : ℝ)| < ε / 2 := by
      have h_eq : dist y x = |(y : ℝ) - (x : ℝ)| := Real.dist_eq _ _
      rw [h_eq] at h_dist
      exact h_dist
    have h' : |i.val y - i.val x| ≤ 2 * |(y : ℝ) - (x : ℝ)| := h_lip y x
    have h'' : |i.val y - i.val x| < ε := by linarith
    have h_out : dist (i.val x) (i.val y) < ε := by
      have h_eq : dist (i.val x) (i.val y) = |i.val x - i.val y| := Real.dist_eq _ _
      rw [h_eq]
      have h_comm : |i.val x - i.val y| = |i.val y - i.val x| := by
        exact abs_sub_comm (i.val x) (i.val y)
      rw [h_comm]
      exact h''
    exact h_out
  exact fun x => h_main x

lemma K_compact : IsCompact K :=
  BoundedContinuousFunction.arzela_ascoli₂
    (Set.Icc (-2 : ℝ) 2)
    isCompact_Icc
    K
    K_closed
    K_in_s
    K_equicont

/-! ========================================================================
   Convert a ℝ → ℝ function to BCF
   ======================================================================== -/

/-- Create a BCF from a function 2-Lipschitz and monotone on [0,1] with h(0)=0. -/
def mkBCF (h : ℝ → ℝ)
    (h_lip : ∀ x y, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 → |h x - h y| ≤ 2 * |x - y|)
    (h_mon : ∀ x y, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 → x ≤ y → h x ≤ h y)
    (h_zero : h 0 = 0) : BCF :=
  let h_fun : UI → ℝ := fun x => h x.val
  have h_dist : ∀ (x y : UI), dist (h_fun x) (h_fun y) ≤ 2 * dist x y := by
    intro x y
    have h_ineq : |h x.val - h y.val| ≤ 2 * |x.val - y.val| := h_lip x.val y.val x.prop y.prop
    have h1 : dist (h_fun x) (h_fun y) = |h x.val - h y.val| := by
      rw [Real.dist_eq] <;> rfl
    have h21 : dist x y = dist (x : ℝ) (y : ℝ) := by rfl
    have h22 : dist (x : ℝ) (y : ℝ) = |(x : ℝ) - (y : ℝ)| := Real.dist_eq _ _
    have h2 : dist x y = |x.val - y.val| := by
      rw [h21, h22] <;> rfl
    rw [h1, h2]
    exact h_ineq
  have h_lip' : LipschitzWith (2 : NNReal) h_fun := LipschitzWith.of_dist_le_mul h_dist
  let h_cont : Continuous h_fun := h_lip'.continuous
  let h_cm : C(UI, ℝ) := ⟨_, h_cont⟩
  BoundedContinuousFunction.mkOfCompact h_cm

lemma mkBCF_in_K (h : ℝ → ℝ)
    (h_lip : ∀ x y, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 → |h x - h y| ≤ 2 * |x - y|)
    (h_mon : ∀ x y, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 → x ≤ y → h x ≤ h y)
    (h_zero : h 0 = 0) : mkBCF h h_lip h_mon h_zero ∈ K := by
  dsimp only [mkBCF]
  constructor
  · intro x y
    simpa [BoundedContinuousFunction.mkOfCompact_apply] using h_lip x.val y.val x.prop y.prop
  · constructor
    · intro x y hxy
      simpa [BoundedContinuousFunction.mkOfCompact_apply] using h_mon x.val y.val x.prop y.prop hxy
    · simp [BoundedContinuousFunction.mkOfCompact_apply, h_zero, zeroUI] <;> rfl

lemma mkBCF_extend (h : ℝ → ℝ)
    (h_lip : ∀ x y, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 → |h x - h y| ≤ 2 * |x - y|)
    (h_mon : ∀ x y, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 → x ≤ y → h x ≤ h y)
    (h_zero : h 0 = 0) :
    ∀ (x : ℝ), x ∈ Set.Icc (0:ℝ) 1 → extend (mkBCF h h_lip h_mon h_zero) x = h x := by
  intro x hx
  have h1 : extend (mkBCF h h_lip h_mon h_zero) x = (mkBCF h h_lip h_mon h_zero) ⟨x, hx⟩ := by
    rw [extend_at hx]
  rw [h1]
  have h2 : (mkBCF h h_lip h_mon h_zero) ⟨x, hx⟩ = h x := by
    dsimp only [mkBCF]
    rw [BoundedContinuousFunction.mkOfCompact_apply] <;> rfl
  exact h2

/-! ========================================================================
   Uniform tube-null on [0,1] via compactness
   ======================================================================== -/

/-- Uniform quantitative Rademacher on [0,1]: there exists τ > 0 such that
    every 2-Lipschitz monotone function h with h(0)=0 admits a finite family
    of ε-linear intervals of length ≥ τ covering all but ε of [0,1]. -/
lemma tubeNull_uniform_unit_interval {ε : ℝ} (hε : 0 < ε) :
    ∃ (τ : ℝ), 0 < τ ∧ ∀ (h : ℝ → ℝ),
      (∀ x y, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 → |h x - h y| ≤ 2 * |x - y|) →
      (∀ x y, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 → x ≤ y → h x ≤ h y) →
      h 0 = 0 →
      ∃ (I : Finset (ℝ × ℝ)),
        (∀ p ∈ I, EpsilonLinear h ε p.1 p.2) ∧
        (∀ p ∈ I, p.2 - p.1 ≥ τ) ∧
        (∀ p ∈ I, 0 ≤ p.1 ∧ p.2 ≤ 1) ∧
        (∀ p ∈ I, ∀ q ∈ I, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1) ∧
        1 - ∑ p ∈ I, (p.2 - p.1) ≤ ε := by
  by_cases h_main : (∃ (τ : ℝ), 0 < τ ∧ ∀ (h : ℝ → ℝ),
      (∀ x y, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 → |h x - h y| ≤ 2 * |x - y|) →
      (∀ x y, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 → x ≤ y → h x ≤ h y) →
      h 0 = 0 → ∃ (I : Finset (ℝ × ℝ)),
        (∀ p ∈ I, EpsilonLinear h ε p.1 p.2) ∧
        (∀ p ∈ I, p.2 - p.1 ≥ τ) ∧
        (∀ p ∈ I, 0 ≤ p.1 ∧ p.2 ≤ 1) ∧
        (∀ p ∈ I, ∀ q ∈ I, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1) ∧
        1 - ∑ p ∈ I, (p.2 - p.1) ≤ ε)
  · exact h_main
  · -- Assume no uniform τ exists
    have h_neg : ∀ (τ : ℝ), 0 < τ → ∃ (h : ℝ → ℝ),
        (∀ x y, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 → |h x - h y| ≤ 2 * |x - y|) ∧
        (∀ x y, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 → x ≤ y → h x ≤ h y) ∧
        h 0 = 0 ∧
        ∀ (I : Finset (ℝ × ℝ)), ¬ (
          (∀ p ∈ I, EpsilonLinear h ε p.1 p.2) ∧
          (∀ p ∈ I, p.2 - p.1 ≥ τ) ∧
          (∀ p ∈ I, 0 ≤ p.1 ∧ p.2 ≤ 1) ∧
          (∀ p ∈ I, ∀ q ∈ I, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1) ∧
          1 - ∑ p ∈ I, (p.2 - p.1) ≤ ε) := by
      simpa [not_exists, not_and, not_forall] using h_main
    choose h_n hn_lip hn_mon hn_zero hn_bad using fun n : ℕ =>
      h_neg (1 / ((n : ℝ) + 1)) (by positivity)
    let seq : ℕ → BCF := fun n => mkBCF (h_n n) (hn_lip n) (hn_mon n) (hn_zero n)
    have h_seq_in_K : ∀ n, seq n ∈ K := fun n =>
      mkBCF_in_K (h_n n) (hn_lip n) (hn_mon n) (hn_zero n)
    -- Sequential compactness
    have h_seq_compact : ∃ (h' : BCF), h' ∈ K ∧ ∃ (φ : ℕ → ℕ), StrictMono φ ∧
        Filter.Tendsto (fun k : ℕ => seq (φ k)) Filter.atTop (nhds h') := by
      exact K_compact.tendsto_subseq (x := seq) h_seq_in_K
    rcases h_seq_compact with ⟨h', hh'_in_K, φ, hφ_mono, h_tendsto⟩
    -- Extend h' to ℝ → ℝ
    let h : ℝ → ℝ := extend h'
    have h_mon_h : MonotoneOn h (Set.Icc (0:ℝ) 1) := by
      intro x hx y hy hxy
      have h'_mon : ∀ (a b : UI), (a : ℝ) ≤ (b : ℝ) → h' a ≤ h' b := hh'_in_K.2.1
      let x' : UI := ⟨x, hx⟩
      let y' : UI := ⟨y, hy⟩
      have h1 : h x = h' x' := by
        dsimp only [h]
        rw [extend_at hx] <;> rfl
      have h2 : h y = h' y' := by
        dsimp only [h]
        rw [extend_at hy] <;> rfl
      rw [h1, h2]
      exact h'_mon x' y' hxy
    -- Apply non-uniform theorem to h with ε/2
    rcases tubeNull_nonuniform (ε := ε / 2) (by linarith) h 0 1 (by norm_num) h_mon_h
      with ⟨τ_h, hτ_pos, I, hI_eps, hI_len, hI_cont, hI_nonover, hI_cover⟩
    -- Transfer: for each p ∈ I, eventually EpsilonLinear for seq(φ k)
    have h_each : ∀ p ∈ I, ∃ (N : ℕ), ∀ k ≥ N,
        EpsilonLinear (extend (seq (φ k))) ε p.1 p.2 := by
      intro p hp
      have h_p_lin : EpsilonLinear h (ε / 2) p.1 p.2 := hI_eps p hp
      have hcd : p.1 < p.2 := by
        have h_len : p.2 - p.1 ≥ τ_h * (1 - 0) := hI_len p hp
        have h_pos : 0 < τ_h * (1 - 0) := by positivity
        linarith
      have hc : 0 ≤ p.1 := (hI_cont p hp).1
      have hd : p.2 ≤ 1 := (hI_cont p hp).2
      let δ := ε * (p.2 - p.1) / 8
      have hδ_pos : 0 < δ := by positivity
      have h_eventually : ∀ᶠ (k : ℕ) in Filter.atTop, ‖seq (φ k) - h'‖ < δ := by
        have h_atTop : ∀ (ε' : ℝ), 0 < ε' → ∃ N, ∀ n ≥ N, dist (seq (φ n)) h' < ε' :=
          Metric.tendsto_atTop.mp h_tendsto
        rcases h_atTop δ hδ_pos with ⟨N, hN⟩
        filter_upwards [Filter.eventually_ge_atTop N] with k hk
        have h_dist : dist (seq (φ k)) h' < δ := hN k hk
        simpa [dist_eq_norm] using h_dist
      rcases Filter.eventually_atTop.mp h_eventually with ⟨N, hN⟩
      refine ⟨N, fun k hk => ?_⟩
      have h_close : ‖seq (φ k) - h'‖ < δ := hN k hk
      exact transfer_epsilon_linear hcd hc hd hε h_p_lin h_close
    -- Finite intersection of eventually properties
    let P : ℕ → (ℝ × ℝ) → Prop := fun k p =>
      EpsilonLinear (extend (seq (φ k))) ε p.1 p.2
    have h_uniform : ∃ (N : ℕ), ∀ k ≥ N, ∀ p ∈ I, P k p := by
      have h_ind : ∀ (I' : Finset (ℝ × ℝ)), (∀ p ∈ I', ∃ N, ∀ k ≥ N, P k p) →
          ∃ N, ∀ k ≥ N, ∀ p ∈ I', P k p := by
        intro I'
        induction I' using Finset.induction with
        | empty =>
            intro _
            refine ⟨0, fun k _ p hp => by simp at hp⟩
        | @insert p I' hp ih =>
            intro h4
            have h5 : ∃ N1, ∀ k ≥ N1, P k p := h4 p (Finset.mem_insert_self p I')
            have h6 : ∃ N2, ∀ k ≥ N2, ∀ q ∈ I', P k q :=
              ih (fun q hq => h4 q (Finset.mem_insert_of_mem hq))
            rcases h5 with ⟨N1, hN1⟩
            rcases h6 with ⟨N2, hN2⟩
            refine ⟨max N1 N2, fun k hk => ?_⟩
            intro q hq
            by_cases hq' : q = p
            · rw [hq']
              exact hN1 k (le_trans (le_max_left N1 N2) hk)
            · have hq'' : q ∈ I' := by simpa [hq', hp] using hq
              exact hN2 k (le_trans (le_max_right N1 N2) hk) q hq''
      exact h_ind I h_each
    rcases h_uniform with ⟨N, hN⟩
    -- Choose k large enough so 1/(φ(k)+1) < τ_h
    have hφ_real : Filter.Tendsto (fun k : ℕ => (φ k : ℝ)) Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      have hφ_nat : ∀ (n : ℕ), ∃ N, ∀ k ≥ N, φ k ≥ n :=
        Filter.tendsto_atTop_atTop.mp hφ_mono.tendsto_atTop
      rcases hφ_nat (Nat.ceil b) with ⟨N, hN⟩
      refine ⟨N, fun k hk => ?_⟩
      have h : φ k ≥ Nat.ceil b := hN k hk
      have h' : (φ k : ℝ) ≥ b := by
        have h'' : (φ k : ℝ) ≥ (Nat.ceil b : ℝ) := by exact_mod_cast h
        have h3 : (Nat.ceil b : ℝ) ≥ b := Nat.le_ceil b
        linarith
      exact h'
    have hφ_tendsto : Filter.Tendsto (fun k : ℕ => (φ k : ℝ) + 1) Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      have h_main : ∀ (b' : ℝ), ∃ N, ∀ n ≥ N, (φ n : ℝ) ≥ b' :=
        Filter.tendsto_atTop_atTop.mp hφ_real
      rcases h_main (b - 1) with ⟨N, hN⟩
      refine ⟨N, fun k hk => ?_⟩
      have h : (φ k : ℝ) ≥ b - 1 := hN k hk
      linarith
    have h_tendsto_one : Filter.Tendsto (fun k : ℕ => 1 / ((φ k : ℝ) + 1)) Filter.atTop (nhds 0) := by
      have h : Filter.Tendsto (fun k : ℕ => ((φ k : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) :=
        hφ_tendsto.inv_tendsto_atTop
      have h_eq : (fun k : ℕ => 1 / ((φ k : ℝ) + 1)) = (fun k : ℕ => ((φ k : ℝ) + 1)⁻¹) := by
        funext k <;> field_simp <;> ring
      rw [h_eq]
      exact h
    have h_exists_k : ∃ (k : ℕ), k ≥ N ∧ 1 / (((φ k : ℝ)) + 1) < τ_h := by
      have h : ∀ᶠ (k : ℕ) in Filter.atTop, 1 / (((φ k : ℝ)) + 1) < τ_h := by
        have h_ball : ∀ᶠ (k : ℕ) in Filter.atTop, 1 / (((φ k : ℝ)) + 1) ∈ Metric.ball 0 τ_h :=
          h_tendsto_one (Metric.ball_mem_nhds 0 hτ_pos)
        filter_upwards [h_ball] with k hk
        have h_pos : 0 < (φ k : ℝ) + 1 := by positivity
        have h_in : (1 / (((φ k : ℝ)) + 1)) ∈ Metric.ball (0 : ℝ) τ_h := hk
        have h_goal : dist (1 / (((φ k : ℝ)) + 1)) (0 : ℝ) < τ_h := h_in
        have h_dist : dist (1 / (((φ k : ℝ)) + 1)) (0 : ℝ) = |1 / (((φ k : ℝ)) + 1)| := by
          simp [Real.dist_eq] <;> ring
        rw [h_dist] at h_goal
        have h_abs2 : |1 / (((φ k : ℝ)) + 1)| = 1 / (((φ k : ℝ)) + 1) := by
          rw [abs_of_pos] <;> positivity
        rw [h_abs2] at h_goal
        exact h_goal
      rcases Filter.eventually_atTop.mp h with ⟨N', hN'⟩
      refine ⟨max N N', le_max_left N N', ?_⟩
      exact hN' (max N N') (le_max_right N N')
    rcases h_exists_k with ⟨k, hk_ge, hk_lt⟩
    let h_k := h_n (φ k)
    -- The intervals I satisfy all conditions for h_k with τ = 1/(φ(k)+1)
    have h_k_eps : ∀ p ∈ I, EpsilonLinear h_k ε p.1 p.2 := by
      intro p hp
      have h1 : EpsilonLinear (extend (seq (φ k))) ε p.1 p.2 := hN k hk_ge p hp
      have h2 : ∀ x ∈ Set.Icc p.1 p.2, extend (seq (φ k)) x = h_k x := by
        intro x hx
        have h_x_in : 0 ≤ x ∧ x ≤ 1 := by
          have hc : 0 ≤ p.1 := (hI_cont p hp).1
          have hd : p.2 ≤ 1 := (hI_cont p hp).2
          exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
        have h_seq_eq : seq (φ k) = mkBCF h_k (hn_lip (φ k)) (hn_mon (φ k)) (hn_zero (φ k)) := by rfl
        rw [h_seq_eq]
        exact mkBCF_extend h_k (hn_lip (φ k)) (hn_mon (φ k)) (hn_zero (φ k)) x h_x_in
      have h_goal : EpsilonLinear h_k ε p.1 p.2 := by
        intro x hx'
        have h4 : |extend (seq (φ k)) x - chordValue (extend (seq (φ k))) p.1 p.2 x| ≤ ε * (p.2 - p.1) := h1 x hx'
        have h5 : ∀ y ∈ Set.Icc p.1 p.2, extend (seq (φ k)) y = h_k y := h2
        have h6 : chordValue (extend (seq (φ k))) p.1 p.2 x = chordValue h_k p.1 p.2 x := by
          have h_p12 : p.1 < p.2 := by
            have h_len : p.2 - p.1 ≥ τ_h * (1 - 0) := hI_len p hp
            have h_pos : 0 < τ_h * (1 - 0) := by positivity
            linarith
          have h_p1_in : p.1 ∈ Set.Icc p.1 p.2 := ⟨by linarith, by linarith⟩
          have h_p2_in : p.2 ∈ Set.Icc p.1 p.2 := ⟨by linarith, by linarith⟩
          have h_eq1 : extend (seq (φ k)) p.1 = h_k p.1 := h5 p.1 h_p1_in
          have h_eq2 : extend (seq (φ k)) p.2 = h_k p.2 := h5 p.2 h_p2_in
          simp [chordValue, chordSlope, h_eq1, h_eq2]
        have h7 : extend (seq (φ k)) x = h_k x := h5 x hx'
        rw [h7, h6] at h4
        exact h4
      exact h_goal
    have h_k_len : ∀ p ∈ I, p.2 - p.1 ≥ (1 / (((φ k : ℝ)) + 1)) := by
      intro p hp
      have h1 : p.2 - p.1 ≥ τ_h * (1 - 0) := hI_len p hp
      have h_simp : τ_h * (1 - 0) = τ_h := by ring
      rw [h_simp] at h1
      linarith
    have h_k_cont : ∀ p ∈ I, 0 ≤ p.1 ∧ p.2 ≤ 1 := hI_cont
    have h_k_nonover : ∀ p ∈ I, ∀ q ∈ I, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1 := hI_nonover
    have h_k_cover : 1 - ∑ p ∈ I, (p.2 - p.1) ≤ ε := by
      have h1 : (1 - 0) - ∑ p ∈ I, (p.2 - p.1) ≤ (ε / 2) * (1 - 0) := hI_cover
      have h_simp : (1 - 0) = (1 : ℝ) := by ring
      rw [h_simp] at h1
      linarith
    have h_contra := hn_bad (φ k) I
    exact False.elim (h_contra ⟨h_k_eps, h_k_len, h_k_cont, h_k_nonover, h_k_cover⟩)

/-! ========================================================================
   Scale from [0,1] to arbitrary [a,b]
   ======================================================================== -/

/-- Uniform quantitative Rademacher on [a,b]: there exists τ > 0 such that
    every 2-Lipschitz monotone function on [a,b] admits a finite family
    of ε-linear intervals of length ≥ τ*(b-a) covering all but ε*(b-a) of [a,b]. -/
lemma tubeNull_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ (τ : ℝ), 0 < τ ∧ ∀ (f : ℝ → ℝ) (a b : ℝ),
      a < b →
      (∀ x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b → |f x - f y| ≤ 2 * |x - y|) →
      (∀ x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y → f x ≤ f y) →
      ∃ (I : Finset (ℝ × ℝ)),
        (∀ p ∈ I, EpsilonLinear f ε p.1 p.2) ∧
        (∀ p ∈ I, p.2 - p.1 ≥ τ * (b - a)) ∧
        (∀ p ∈ I, a ≤ p.1 ∧ p.2 ≤ b) ∧
        (∀ p ∈ I, ∀ q ∈ I, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1) ∧
        (b - a) - ∑ p ∈ I, (p.2 - p.1) ≤ ε * (b - a) := by
  rcases tubeNull_uniform_unit_interval hε with ⟨τ, hτ_pos, h_main⟩
  refine ⟨τ, hτ_pos, ?_⟩
  intro f a b hab h_lip h_mon
  set L : ℝ := b - a with hL_def
  have hL_pos : 0 < L := by linarith
  -- Normalize f to [0,1]
  let h : ℝ → ℝ := fun t => (f (a + t * L) - f a) / L
  have h_lip_h : ∀ x y, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 → |h x - h y| ≤ 2 * |x - y| := by
    intro x y hx hy
    have hx1 : 0 ≤ x := hx.1
    have hx2 : x ≤ 1 := hx.2
    have hy1 : 0 ≤ y := hy.1
    have hy2 : y ≤ 1 := hy.2
    have hL_nonneg : 0 ≤ L := by linarith
    have h21 : a + x * L ∈ Set.Icc a b := by
      have h_xL_nonneg : 0 ≤ x * L := mul_nonneg hx1 hL_nonneg
      have h_left : a ≤ a + x * L := by linarith
      have h_right : a + x * L ≤ b := by
        have h : x * L ≤ L := by
          calc x * L ≤ 1 * L := by exact mul_le_mul_of_nonneg_right hx2 hL_nonneg
               _ = L := by ring
        have hL : a + L = b := by linarith [hL_def]
        linarith
      exact ⟨h_left, h_right⟩
    have h22 : a + y * L ∈ Set.Icc a b := by
      have h_yL_nonneg : 0 ≤ y * L := mul_nonneg hy1 hL_nonneg
      have h_left : a ≤ a + y * L := by linarith
      have h_right : a + y * L ≤ b := by
        have h : y * L ≤ L := by
          calc y * L ≤ 1 * L := by exact mul_le_mul_of_nonneg_right hy2 hL_nonneg
               _ = L := by ring
        have hL : a + L = b := by linarith [hL_def]
        linarith
      exact ⟨h_left, h_right⟩
    have h1_raw : |f (a + x * L) - f (a + y * L)| ≤ 2 * |a + x * L - (a + y * L)| := h_lip (a + x * L) (a + y * L) h21 h22
    have h1 : |f (a + x * L) - f (a + y * L)| ≤ 2 * |x * L - y * L| := by
      have h_eq : |a + x * L - (a + y * L)| = |x * L - y * L| := by
        have h : a + x * L - (a + y * L) = x * L - y * L := by ring
        rw [h]
      rw [h_eq] at h1_raw
      exact h1_raw
    have h5 : |h x - h y| = |f (a + x * L) - f (a + y * L)| / L := by
      dsimp only [h]
      have h_eq : (f (a + x * L) - f a) / L - (f (a + y * L) - f a) / L =
          (f (a + x * L) - f (a + y * L)) / L := by
        field_simp [hL_pos.ne'] <;> ring
      have h_abs : |(f (a + x * L) - f a) / L - (f (a + y * L) - f a) / L| =
          |(f (a + x * L) - f (a + y * L)) / L| := by rw [h_eq]
      rw [h_abs]
      have h_abs2 : |(f (a + x * L) - f (a + y * L)) / L| =
          |f (a + x * L) - f (a + y * L)| / |L| := by rw [abs_div]
      rw [h_abs2, abs_of_pos hL_pos]
    rw [h5]
    have h6 : |x * L - y * L| = |x - y| * L := by
      have h7 : x * L - y * L = (x - y) * L := by ring
      rw [h7, abs_mul, abs_of_pos hL_pos] <;> ring
    rw [h6] at h1
    have h7 : |f (a + x * L) - f (a + y * L)| / L ≤ 2 * |x - y| := by
      calc |f (a + x * L) - f (a + y * L)| / L
        ≤ (2 * (|x - y| * L)) / L := by gcongr
      _ = 2 * |x - y| := by field_simp [hL_pos.ne'] <;> ring
    exact h7
  have h_mon_h : ∀ x y, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 → x ≤ y → h x ≤ h y := by
    intro x y hx hy hxy
    have hx1 : 0 ≤ x := hx.1
    have hx2 : x ≤ 1 := hx.2
    have hy1 : 0 ≤ y := hy.1
    have hy2 : y ≤ 1 := hy.2
    have hL_nonneg : 0 ≤ L := by linarith
    have h21 : a + x * L ∈ Set.Icc a b := by
      have h_xL_nonneg : 0 ≤ x * L := mul_nonneg hx1 hL_nonneg
      have h_left : a ≤ a + x * L := by linarith
      have h_right : a + x * L ≤ b := by
        have h : x * L ≤ L := by
          calc x * L ≤ 1 * L := by exact mul_le_mul_of_nonneg_right hx2 hL_nonneg
               _ = L := by ring
        have hL : a + L = b := by linarith [hL_def]
        linarith
      exact ⟨h_left, h_right⟩
    have h22 : a + y * L ∈ Set.Icc a b := by
      have h_yL_nonneg : 0 ≤ y * L := mul_nonneg hy1 hL_nonneg
      have h_left : a ≤ a + y * L := by linarith
      have h_right : a + y * L ≤ b := by
        have h : y * L ≤ L := by
          calc y * L ≤ 1 * L := by exact mul_le_mul_of_nonneg_right hy2 hL_nonneg
               _ = L := by ring
        have hL : a + L = b := by linarith [hL_def]
        linarith
      exact ⟨h_left, h_right⟩
    have h_ineq : a + x * L ≤ a + y * L := by
      have h : x * L ≤ y * L := mul_le_mul_of_nonneg_right hxy hL_nonneg
      linarith
    have h4 : f (a + x * L) ≤ f (a + y * L) := h_mon (a + x * L) (a + y * L) h21 h22 h_ineq
    dsimp only [h]
    have h5 : (f (a + x * L) - f a) / L ≤ (f (a + y * L) - f a) / L := by
      have h6 : f (a + x * L) - f a ≤ f (a + y * L) - f a := by linarith
      exact div_le_div_of_nonneg_right h6 (by linarith)
    exact h5
  have h_zero_h : h 0 = 0 := by
    dsimp only [h]
    field_simp [hL_pos.ne'] <;> ring_nf
  rcases h_main h h_lip_h h_mon_h h_zero_h with ⟨I0, hI0_eps, hI0_len, hI0_cont, hI0_nonover, hI0_cover⟩
  -- Map intervals back to [a,b]
  let map_pair : ℝ × ℝ → ℝ × ℝ := fun p => (a + p.1 * L, a + p.2 * L)
  let I : Finset (ℝ × ℝ) := Finset.image map_pair I0
  have h_inj : Set.InjOn map_pair I0 := by
    intro p _ q _ h
    have h1 : a + p.1 * L = a + q.1 * L := by simpa [map_pair] using congr_arg Prod.fst h
    have h2 : a + p.2 * L = a + q.2 * L := by simpa [map_pair] using congr_arg Prod.snd h
    have hp1 : p.1 = q.1 := by apply mul_left_cancel₀ hL_pos.ne'; linarith
    have hp2 : p.2 = q.2 := by apply mul_left_cancel₀ hL_pos.ne'; linarith
    exact Prod.ext hp1 hp2
  have hI_eps : ∀ p ∈ I, EpsilonLinear f ε p.1 p.2 := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨p0, hp0, rfl⟩
    let c := p0.1
    let d := p0.2
    have hcd : c < d := by
      have h_len : d - c ≥ τ := hI0_len p0 hp0
      linarith [hτ_pos]
    have h_eps_h : EpsilonLinear h ε c d := hI0_eps p0 hp0
    have h_main1 : ∀ (x : ℝ), x ∈ Set.Icc (a + c * L) (a + d * L) →
        |f x - chordValue f (a + c * L) (a + d * L) x| ≤ ε * ((a + d * L) - (a + c * L)) := by
      intro x hx
      let t := (x - a) / L
      have ht1 : c ≤ t := by
        dsimp only [t]
        have h_left1 : a + c * L ≤ x := hx.1
        have h : c * L ≤ x - a := by linarith
        have h' : c ≤ (x - a) / L := by
          calc c = (c * L) / L := by field_simp [hL_pos.ne'] <;> ring
            _ ≤ (x - a) / L := by gcongr
        exact h'
      have ht2 : t ≤ d := by
        dsimp only [t]
        have h_right1 : x ≤ a + d * L := hx.2
        have h : x - a ≤ d * L := by linarith
        have h' : (x - a) / L ≤ d := by
          calc (x - a) / L ≤ (d * L) / L := by gcongr
            _ = d := by field_simp [hL_pos.ne'] <;> ring
        exact h'
      have h_x_eq : x = a + t * L := by
        dsimp only [t]
        field_simp [hL_pos.ne'] <;> ring
      have h_f_t : f x = f a + L * h t := by
        rw [h_x_eq]
        dsimp only [h]
        field_simp [hL_pos.ne'] <;> ring
      have h_lin : chordValue f (a + c * L) (a + d * L) x =
          f a + L * chordValue h c d t := by
        rw [h_x_eq]
        have h_eq2 : chordValue f (a + c * L) (a + d * L) (a + t * L) =
            f a + L * chordValue h c d t := by
          have h_fA : f (a + c * L) = f a + L * h c := by
            dsimp only [h] <;> field_simp [hL_pos.ne'] <;> ring
          have h_fB : f (a + d * L) = f a + L * h d := by
            dsimp only [h] <;> field_simp [hL_pos.ne'] <;> ring
          have h_slope : chordSlope f (a + c * L) (a + d * L) = chordSlope h c d := by
            dsimp only [chordSlope]
            rw [h_fA, h_fB]
            have h_eq1 : (f a + L * h d) - (f a + L * h c) = L * (h d - h c) := by ring
            have h_eq2 : (a + d * L) - (a + c * L) = L * (d - c) := by ring
            have hcd_pos : d - c ≠ 0 := by linarith [hcd]
            rw [h_eq1, h_eq2]
            field_simp [hL_pos.ne', hcd_pos] <;> ring
          have h_XA : (a + t * L) - (a + c * L) = (t - c) * L := by ring
          have h_cv : chordValue f (a + c * L) (a + d * L) (a + t * L) =
              f (a + c * L) + chordSlope f (a + c * L) (a + d * L) * ((a + t * L) - (a + c * L)) := by
            rfl
          rw [h_cv, h_fA, h_slope, h_XA]
          have h_final : f a + L * h c + chordSlope h c d * ((t - c) * L) =
              f a + L * chordValue h c d t := by
            have h_cv2 : chordValue h c d t = h c + chordSlope h c d * (t - c) := by rfl
            rw [h_cv2] <;> ring
          exact h_final
        exact h_eq2
      rw [h_f_t, h_lin]
      have h9 : |f a + L * h t - (f a + L * chordValue h c d t)| = L * |h t - chordValue h c d t| := by
        have h10 : f a + L * h t - (f a + L * chordValue h c d t) = L * (h t - chordValue h c d t) := by ring
        rw [h10, abs_mul, abs_of_pos hL_pos] <;> ring
      rw [h9]
      have h10 : |h t - chordValue h c d t| ≤ ε * (d - c) := h_eps_h t ⟨ht1, ht2⟩
      have h11 : L * |h t - chordValue h c d t| ≤ L * (ε * (d - c)) := by gcongr
      have h12 : L * (ε * (d - c)) = ε * ((a + d * L) - (a + c * L)) := by
        simp [hL_def] <;> ring
      rw [h12] at h11
      exact h11
    exact h_main1
  have hI_len : ∀ p ∈ I, p.2 - p.1 ≥ τ * L := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨p0, hp0, rfl⟩
    have h1 : p0.2 - p0.1 ≥ τ := hI0_len p0 hp0
    dsimp only [map_pair]
    have h2 : (a + p0.2 * L) - (a + p0.1 * L) = (p0.2 - p0.1) * L := by ring
    rw [h2]
    have h3 : (p0.2 - p0.1) * L ≥ τ * L := by gcongr
    exact h3
  have hI_cont : ∀ p ∈ I, a ≤ p.1 ∧ p.2 ≤ b := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨p0, hp0, rfl⟩
    have h1 : 0 ≤ p0.1 := (hI0_cont p0 hp0).1
    have h2 : p0.2 ≤ 1 := (hI0_cont p0 hp0).2
    dsimp only [map_pair]
    have hL_nonneg : 0 ≤ L := by linarith
    have h_left : a ≤ a + p0.1 * L := by
      have h : 0 ≤ p0.1 * L := mul_nonneg h1 hL_nonneg
      linarith
    have h_right : a + p0.2 * L ≤ b := by
      have h : p0.2 * L ≤ L := by
        have h' : p0.2 ≤ 1 := h2
        have h'' : p0.2 * L ≤ 1 * L := mul_le_mul_of_nonneg_right h' hL_nonneg
        ring_nf at h'' ⊢ <;> exact h''
      have hL : a + L = b := by linarith [hL_def]
      linarith
    exact ⟨h_left, h_right⟩
  have hI_nonover : ∀ p ∈ I, ∀ q ∈ I, p ≠ q → p.2 ≤ q.1 ∨ q.2 ≤ p.1 := by
    intro p hp q hq hne
    rcases Finset.mem_image.mp hp with ⟨p0, hp0, rfl⟩
    rcases Finset.mem_image.mp hq with ⟨q0, hq0, rfl⟩
    have hne0 : p0 ≠ q0 := by
      intro h
      apply hne
      simp [h]
    have h := hI0_nonover p0 hp0 q0 hq0 hne0
    have hL_nonneg : 0 ≤ L := by linarith
    cases h with
    | inl h =>
      have h_mul : p0.2 * L ≤ q0.1 * L := mul_le_mul_of_nonneg_right h hL_nonneg
      have h' : (a + p0.2 * L) ≤ (a + q0.1 * L) := by linarith
      exact Or.inl h'
    | inr h =>
      have h_mul : q0.2 * L ≤ p0.1 * L := mul_le_mul_of_nonneg_right h hL_nonneg
      have h' : (a + q0.2 * L) ≤ (a + p0.1 * L) := by linarith
      exact Or.inr h'
  have h_sum : ∑ p ∈ I, (p.2 - p.1) = L * ∑ p0 ∈ I0, (p0.2 - p0.1) := by
    have h3 : ∑ p ∈ I, (p.2 - p.1) = ∑ p0 ∈ I0, ((map_pair p0).2 - (map_pair p0).1) := by
      rw [Finset.sum_image h_inj] <;> rfl
    rw [h3]
    have h4 : ∀ p0 ∈ I0, ((map_pair p0).2 - (map_pair p0).1) = L * (p0.2 - p0.1) := by
      intro p0 _
      dsimp only [map_pair] <;> ring
    have h5 : ∑ p0 ∈ I0, ((map_pair p0).2 - (map_pair p0).1) = ∑ p0 ∈ I0, (L * (p0.2 - p0.1)) := by
      apply Finset.sum_congr rfl
      intro p0 hp0
      exact h4 p0 hp0
    rw [h5]
    rw [← Finset.mul_sum]
  have hI_cover : L - ∑ p ∈ I, (p.2 - p.1) ≤ ε * L := by
    rw [h_sum]
    have h1 : 1 - ∑ p0 ∈ I0, (p0.2 - p0.1) ≤ ε := hI0_cover
    have h2 : L - L * ∑ p0 ∈ I0, (p0.2 - p0.1) = L * (1 - ∑ p0 ∈ I0, (p0.2 - p0.1)) := by ring
    rw [h2]
    have h3 : L * (1 - ∑ p0 ∈ I0, (p0.2 - p0.1)) ≤ L * ε := by gcongr
    have h4 : L * ε = ε * L := by ring
    rw [h4] at h3
    exact h3
  have h_final : (b - a) - ∑ p ∈ I, (p.2 - p.1) ≤ ε * (b - a) := by
    have hL : b - a = L := by simp [hL_def]
    rw [hL]
    exact hI_cover
  exact ⟨I, hI_eps, hI_len, hI_cont, hI_nonover, h_final⟩

/-! ========================================================================
   Final TubeNullResult: convert to List format with LipschitzOnWith/MonotoneOn
   ======================================================================== -/

/-- The uniform tube-null lemma in the exact format required by `TubeNullResult`. -/
theorem tubeNull_result : MainAssembly.TubeNullResult := by
  dsimp only [MainAssembly.TubeNullResult]
  intro ε' hε'
  rcases tubeNull_uniform hε' with ⟨τ0, hτ0_pos, h_main⟩
  refine ⟨τ0, hτ0_pos, ?_⟩
  intro f m hm_pos hlip hmon
  -- Convert LipschitzOnWith and MonotoneOn to explicit forms
  have h_lip' : ∀ x y, x ∈ Set.Icc 0 m → y ∈ Set.Icc 0 m →
      |f x - f y| ≤ 2 * |x - y| := by
    intro x y hx hy
    have h_edist : edist (f x) (f y) ≤ (2 : NNReal) * edist x y := hlip hx hy
    have h_dist : dist (f x) (f y) ≤ 2 * dist x y := by
      have h1 : ENNReal.ofReal (dist (f x) (f y)) ≤ ENNReal.ofReal (2 * dist x y) := by
        simpa [edist_dist, ENNReal.ofReal_mul] using h_edist
      have h2 : 0 ≤ dist x y := by positivity
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
    simpa [Real.dist_eq] using h_dist
  have h_mon' : ∀ x y, x ∈ Set.Icc 0 m → y ∈ Set.Icc 0 m → x ≤ y → f x ≤ f y := by
    intro x y hx hy hxy
    exact hmon hx hy hxy
  rcases h_main f 0 m hm_pos h_lip' h_mon' with ⟨I, hI_eps, hI_len, hI_cont, hI_nonover, hI_cover⟩
  -- Convert Finset to sorted List
  have hI_len' : ∀ p ∈ I, p.2 - p.1 ≥ τ0 * m := by
    intro p hp
    have h := hI_len p hp
    have h_simp : (m - 0 : ℝ) = m := by ring
    rw [h_simp] at h
    exact h
  have hI_cover' : m - ∑ p ∈ I, (p.2 - p.1) ≤ ε' * m := by
    have h_simp : (m - 0 : ℝ) = m := by ring
    rw [h_simp] at hI_cover
    exact hI_cover
  exact adapt_finset_to_list hτ0_pos hm_pos hI_eps hI_len' hI_cont hI_nonover hI_cover'

end CombinatorialKaufman.TubeNull

end
