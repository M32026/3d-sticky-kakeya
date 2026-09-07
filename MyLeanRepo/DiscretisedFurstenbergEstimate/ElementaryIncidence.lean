module

/-
  Elementary incidence estimates (OS Section 2.2).

  Self-contained module defining dyadic squares/tubes and proving:
  - `tubesSlopes`: slope map ≤9-to-1 for tubes through a common square
  - `incidenceProp`: Cauchy-Schwarz incidence bound (stated)
  - `prop5` / `two_s_bound`: lower bound on union (stated)
  - `thin_delta_subset`: extract thin subset (stated)
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-! ARCHIVED: MATHEMATICALLY INVALID FOR THE TARGET PROOF. DO NOT IMPORT.

Old dyadic incidence infrastructure (DSquare/DTube). Superseded by the
metric-space S-set approach and the operator-provided components.
See .scratch/operator/TEAM_CORRECTION_AND_PROOF_ROUTE.md. -/

noncomputable section

open DirecretisedFurstenbergEstimate
open scoped ENNReal NNReal

namespace DiscretisedFurstenbergEstimate

variable {n : ℕ}

-- ============================================================================
-- Minimal dyadic infrastructure
-- ============================================================================

/-- Dyadic scale δ = 2^-n. -/
def δ (n : ℕ) : ℝ := (2 : ℝ)^(-(n : ℤ))

lemma δ_pos (n : ℕ) : 0 < δ n := by
  unfold δ
  positivity

lemma δ_le_one (n : ℕ) : δ n ≤ 1 := by
  unfold δ
  have h_pos : (0 : ℝ) < (2 : ℝ) := by norm_num
  have hneg : (2 : ℝ)^(-(n : ℤ)) = ((2 : ℝ)^(n : ℤ))⁻¹ := by
    have h : ∀ (m : ℤ), (2 : ℝ)^(-m) = ((2 : ℝ)^m)⁻¹ := by
      intro m
      simp [Real.rpow_neg]
      <;> ring
    exact h (n : ℤ)
  rw [hneg]
  have h3 : (1 : ℝ) ≤ (2 : ℝ)^(n : ℤ) := by
    have h4 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
    have h5 : (0 : ℤ) ≤ (n : ℤ) := by positivity
    exact one_le_zpow₀ h4 h5
  have h_pos2 : 0 < (2 : ℝ)^(n : ℤ) := by positivity
  have h7 : 1 / (2 : ℝ)^(n : ℤ) ≤ 1 := by
    apply (div_le_one h_pos2).mpr
    exact h3
  simpa [one_div] using h7

/-- A dyadic square of side δ. -/
structure DSquare (n : ℕ) : Type where
  i : ℤ
  j : ℤ
  deriving DecidableEq

namespace DSquare

def toSet (p : DSquare n) : Set (ℝ × ℝ) :=
  {x | (p.i : ℝ) * δ n ≤ x.1 ∧ x.1 < ((p.i : ℝ) + 1) * δ n ∧
       (p.j : ℝ) * δ n ≤ x.2 ∧ x.2 < ((p.j : ℝ) + 1) * δ n}

lemma side {p : DSquare n} {x y : ℝ × ℝ} (hx : x ∈ p.toSet) (hy : y ∈ p.toSet) :
    |x.1 - y.1| ≤ δ n ∧ |x.2 - y.2| ≤ δ n := by
  have hx1 : (p.i : ℝ) * δ n ≤ x.1 := hx.1
  have hx2 : x.1 < ((p.i : ℝ) + 1) * δ n := hx.2.1
  have hy1 : (p.i : ℝ) * δ n ≤ y.1 := hy.1
  have hy2 : y.1 < ((p.i : ℝ) + 1) * δ n := hy.2.1
  have hx3 : (p.j : ℝ) * δ n ≤ x.2 := hx.2.2.1
  have hx4 : x.2 < ((p.j : ℝ) + 1) * δ n := hx.2.2.2
  have hy3 : (p.j : ℝ) * δ n ≤ y.2 := hy.2.2.1
  have hy4 : y.2 < ((p.j : ℝ) + 1) * δ n := hy.2.2.2
  have hδ : 0 < δ n := δ_pos n
  constructor
  · rw [abs_sub_le_iff]
    constructor <;> linarith
  · rw [abs_sub_le_iff]
    constructor <;> linarith

/-- The lower-left corner of the square as a point in ℝ². -/
def toPoint (p : DSquare n) : ℝ × ℝ :=
  ((p.i : ℝ) * δ n, (p.j : ℝ) * δ n)

/-- Distance between squares: Euclidean distance between lower-left corners. -/
instance : MetricSpace (DSquare n) where
  dist p q := dist p.toPoint q.toPoint
  dist_self _ := by simp [toPoint]
  dist_comm _ _ := by simp [toPoint, dist_comm]
  dist_triangle _ _ _ := dist_triangle _ _ _
  eq_of_dist_eq_zero := by
    intro p q h
    have h' : p.toPoint = q.toPoint := by
      simpa [toPoint, dist_eq_zero] using h
    have hi : p.i = q.i := by
      have h1 : (p.i : ℝ) * δ n = (q.i : ℝ) * δ n :=
        congr_arg Prod.fst h'
      have hδ : 0 < δ n := δ_pos n
      have h2 : (p.i : ℝ) = (q.i : ℝ) := by
        calc (p.i : ℝ)
          = ((p.i : ℝ) * δ n) / δ n := by field_simp [hδ.ne'] <;> ring
        _ = ((q.i : ℝ) * δ n) / δ n := by rw [h1]
        _ = (q.i : ℝ) := by field_simp [hδ.ne'] <;> ring
      exact_mod_cast h2
    have hj : p.j = q.j := by
      have h1 : (p.j : ℝ) * δ n = (q.j : ℝ) * δ n :=
        congr_arg Prod.snd h'
      have hδ : 0 < δ n := δ_pos n
      have h2 : (p.j : ℝ) = (q.j : ℝ) := by
        calc (p.j : ℝ)
          = ((p.j : ℝ) * δ n) / δ n := by field_simp [hδ.ne'] <;> ring
        _ = ((q.j : ℝ) * δ n) / δ n := by rw [h1]
        _ = (q.j : ℝ) := by field_simp [hδ.ne'] <;> ring
      exact_mod_cast h2
    cases p <;> cases q <;> simp_all <;> tauto

end DSquare

/-- A dyadic tube indexed by integer slope and intercept. -/
structure DTube (n : ℕ) : Type where
  a : ℤ
  b : ℤ
  deriving DecidableEq

namespace DTube

def slope (T : DTube n) : ℝ := (T.a : ℝ) * δ n
def intercept (T : DTube n) : ℝ := (T.b : ℝ) * δ n

/-- The tube as a strip |y - slope*x - intercept| ≤ δ. -/
def toSet (T : DTube n) : Set (ℝ × ℝ) :=
  {p | |p.2 - T.slope * p.1 - T.intercept| ≤ δ n}

end DTube

/-- Embed a tube into slope-intercept parameter space. -/
def DTube.toParam (T : DTube n) : ℝ × ℝ := (T.slope, T.intercept)

/-- Metric on dyadic tubes induced from slope-intercept parameter space. -/
instance : MetricSpace (DTube n) where
  dist T1 T2 := dist T1.toParam T2.toParam
  dist_self _ := by simp [DTube.toParam]
  dist_comm _ _ := by simp [DTube.toParam, dist_comm]
  dist_triangle _ _ _ := dist_triangle _ _ _
  eq_of_dist_eq_zero := by
    intro T1 T2 h
    have h' : T1.toParam = T2.toParam := by
      simpa [DTube.toParam, dist_eq_zero] using h
    have hs : T1.slope = T2.slope := by
      exact congr_arg Prod.fst h'
    have hi : T1.intercept = T2.intercept := by
      exact congr_arg Prod.snd h'
    have ha : T1.a = T2.a := by
      have hδ : 0 < δ n := δ_pos n
      have h_eq : (T1.a : ℝ) * δ n = (T2.a : ℝ) * δ n := hs
      have h : (T1.a : ℝ) = (T2.a : ℝ) := by
        exact (mul_left_inj' hδ.ne').mp h_eq
      exact_mod_cast h
    have hb : T1.b = T2.b := by
      have hδ : 0 < δ n := δ_pos n
      have h_eq : (T1.b : ℝ) * δ n = (T2.b : ℝ) * δ n := hi
      have h : (T1.b : ℝ) = (T2.b : ℝ) := by
        exact (mul_left_inj' hδ.ne').mp h_eq
      exact_mod_cast h
    cases T1 <;> cases T2 <;> simp_all <;> tauto

-- ============================================================================
-- tubesSlopes: slope map ≤ 9-to-1
-- ============================================================================

/-- If two same-slope tubes both intersect a square,
their intercept indices differ by at most 4. -/
lemma intercept_diff_bound {T₁ T₂ : DTube n} {p : DSquare n}
    (h_slope : T₁.a = T₂.a)
    (h1 : (T₁.toSet ∩ p.toSet).Nonempty)
    (h2 : (T₂.toSet ∩ p.toSet).Nonempty)
    (h_slope_bound : |T₁.slope| ≤ 1) :
    |(T₁.b - T₂.b : ℤ)| ≤ 4 := by
  rcases h1 with ⟨x, hxT, hxS⟩
  rcases h2 with ⟨y, hyT, hyS⟩
  have hx3 : |x.2 - T₁.slope * x.1 - T₁.intercept| ≤ δ n := hxT
  have hy3 : |y.2 - T₂.slope * y.1 - T₂.intercept| ≤ δ n := hyT
  have h_side := p.side hxS hyS
  have h_slope' : T₁.slope = T₂.slope := by
    simp [DTube.slope, h_slope] <;> ring
  set e1 := x.2 - T₁.slope * x.1 - T₁.intercept with he1
  set e2 := y.2 - T₂.slope * y.1 - T₂.intercept with he2
  have h_eq : T₁.intercept - T₂.intercept =
      (x.2 - y.2) - T₁.slope * (x.1 - y.1) - (e1 - e2) := by
    simp [he1, he2, h_slope'] <;> ring
  have h_abs1 : |T₁.intercept - T₂.intercept| ≤
      |x.2 - y.2| + |T₁.slope * (x.1 - y.1)| + |e1 - e2| := by
    rw [h_eq]
    have h21 : |(x.2 - y.2) - T₁.slope * (x.1 - y.1) - (e1 - e2)| ≤
        |(x.2 - y.2) - T₁.slope * (x.1 - y.1)| + |e1 - e2| :=
      abs_sub ((x.2 - y.2) - T₁.slope * (x.1 - y.1) : ℝ) (e1 - e2)
    have h22 : |(x.2 - y.2) - T₁.slope * (x.1 - y.1)| ≤
        |x.2 - y.2| + |T₁.slope * (x.1 - y.1)| :=
      abs_sub (x.2 - y.2 : ℝ) (T₁.slope * (x.1 - y.1))
    linarith
  have h_abs2 : |T₁.slope * (x.1 - y.1)| = |T₁.slope| * |x.1 - y.1| := by rw [abs_mul]
  have h_abs3 : |e1 - e2| ≤ |e1| + |e2| := abs_sub (e1 : ℝ) e2
  have h4 : |T₁.intercept - T₂.intercept| ≤
      |x.2 - y.2| + |T₁.slope| * |x.1 - y.1| + |e1| + |e2| := by
    rw [h_abs2] at h_abs1
    linarith [h_abs3]
  have h5 : |T₁.intercept - T₂.intercept| ≤ 4 * δ n := by
    calc |T₁.intercept - T₂.intercept|
      ≤ |x.2 - y.2| + |T₁.slope| * |x.1 - y.1| + |e1| + |e2| := h4
    _ ≤ δ n + 1 * δ n + δ n + δ n := by
        gcongr <;> linarith [h_side.1, h_side.2, h_slope_bound, hx3, hy3]
    _ = 4 * δ n := by ring
  have h7 : T₁.intercept - T₂.intercept = (δ n) * ((T₁.b - T₂.b : ℤ) : ℝ) := by
    simp [DTube.intercept] <;> ring
  have h8 : 0 < δ n := δ_pos n
  have h91 : |((T₁.b - T₂.b : ℤ) : ℝ)| = |T₁.intercept - T₂.intercept| / (δ n) := by
    have h92 : |(δ n) * ((T₁.b - T₂.b : ℤ) : ℝ)| = (δ n) * |((T₁.b - T₂.b : ℤ) : ℝ)| := by
      rw [abs_mul] <;> rw [abs_of_pos h8]
    have h93 : |T₁.intercept - T₂.intercept| = (δ n) * |((T₁.b - T₂.b : ℤ) : ℝ)| := by
      rw [h7] <;> exact h92
    rw [h93]
    field_simp [h8.ne'] <;> ring
  have h9 : |((T₁.b - T₂.b : ℤ) : ℝ)| ≤ 4 := by
    rw [h91]
    have h_div : |T₁.intercept - T₂.intercept| / (δ n) ≤ 4 := by
      calc |T₁.intercept - T₂.intercept| / (δ n)
        ≤ (4 * δ n) / (δ n) := by gcongr
      _ = 4 := by field_simp [h8.ne'] <;> ring
    exact h_div
  have h10 : (|T₁.b - T₂.b| : ℝ) = |((T₁.b - T₂.b : ℤ) : ℝ)| := by simp
  have h11 : (|T₁.b - T₂.b| : ℝ) ≤ 4 := by
    rw [h10] <;> exact h9
  exact_mod_cast h11

/-- **tubesSlopes** (OS Lemma 2.3): among tubes intersecting a common square
with |slope| ≤ 1, the slope map is at most 9-to-1. -/
lemma tubesSlopes {p : DSquare n} {Ts : Finset (DTube n)}
    (hTs : ∀ T ∈ Ts, (T.toSet ∩ p.toSet).Nonempty)
    (h_bound : ∀ T ∈ Ts, |T.slope| ≤ 1)
    (a : ℤ) :
    (Ts.filter (fun T => T.a = a)).card ≤ 9 := by
  let S := Ts.filter (fun T => T.a = a)
  by_cases h_empty : S = ∅
  · have h_card0 : S.card = 0 := by
      rw [h_empty] <;> simp
    have h_goal : (Ts.filter (fun T => T.a = a)).card = S.card := by rfl
    rw [h_goal, h_card0] <;> norm_num
  · have hS_ne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty
    let T0 : DTube n := Classical.choose hS_ne
    have hT0_in : T0 ∈ S := Classical.choose_spec hS_ne
    have h_bounds : ∀ T ∈ S, T.b ∈ Finset.Icc (T0.b - 4) (T0.b + 4) := by
      intro T hT
      have hT_a : T.a = a := (Finset.mem_filter.mp hT).2
      have hT_in_Ts : T ∈ Ts := (Finset.mem_filter.mp hT).1
      have hT0_in_Ts : T0 ∈ Ts := (Finset.mem_filter.mp hT0_in).1
      have hT0_a : T0.a = a := (Finset.mem_filter.mp hT0_in).2
      have h_diff : |(T.b - T0.b : ℤ)| ≤ 4 := intercept_diff_bound
        (by simp [hT_a, hT0_a])
        (hTs T hT_in_Ts) (hTs T0 hT0_in_Ts) (h_bound T hT_in_Ts)
      have h10 : -(4 : ℤ) ≤ T.b - T0.b := (abs_le.mp h_diff).1
      have h11 : T.b - T0.b ≤ (4 : ℤ) := (abs_le.mp h_diff).2
      exact Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩
    have h_inj : Set.InjOn (fun (T : DTube n) => T.b) (↑S : Set (DTube n)) := by
      intro T1 hT1 T2 hT2 h
      have ha1 : T1.a = a := (Finset.mem_filter.mp hT1).2
      have ha2 : T2.a = a := (Finset.mem_filter.mp hT2).2
      have h_a : T1.a = T2.a := by linarith
      have h_b : T1.b = T2.b := h
      have h : T1 = T2 := by
        cases T1 <;> cases T2 <;> simp_all <;> tauto
      exact h
    have h_card : (S.image (fun T => T.b)).card = S.card :=
      Finset.card_image_of_injOn h_inj
    have h_final : S.card ≤ 9 := by
      calc S.card
        = (S.image (fun T => T.b)).card := h_card.symm
      _ ≤ (Finset.Icc (T0.b - 4) (T0.b + 4)).card :=
          Finset.card_le_card (by
            intro x hx
            rcases Finset.mem_image.mp hx with ⟨T, hT, rfl⟩
            exact h_bounds T hT)
      _ = 9 := by
        have h : ∀ (x : ℤ), (Finset.Icc (x - 4) (x + 4)).card = 9 := by
          intro x
          simp [Finset.Icc_eq_empty_of_lt] <;> omega
        exact h T0.b
    have h_goal : (Ts.filter (fun T => T.a = a)).card = S.card := by rfl
    rw [h_goal]
    exact h_final

-- ============================================================================
-- Slope interval bound (key lemma for incidence estimates)
-- ============================================================================

/-- Helper: for a single tube intersecting p and p', its slope is within 12/k
of the center slope (p.j-p'.j)/(p.i-p'.i), where k = |p.i-p'.i| ≥ 2. -/
lemma single_slope_bound {T : DTube n} {p p' : DSquare n}
    (h1 : (T.toSet ∩ p.toSet).Nonempty)
    (h2 : (T.toSet ∩ p'.toSet).Nonempty)
    (h_slope : |T.slope| ≤ 1)
    (hk : 2 ≤ Int.natAbs (p.i - p'.i)) :
    |T.slope - ((p.j - p'.j : ℝ) / (p.i - p'.i : ℝ))| ≤ 12 / (Int.natAbs (p.i - p'.i) : ℝ) := by
  rcases h1 with ⟨x, hxT, hxS⟩
  rcases h2 with ⟨y, hyT, hyS⟩
  set δ := δ n with hδ_def
  have hδ_pos : 0 < δ := δ_pos n
  set dx : ℝ := (p.i - p'.i : ℝ) with hdx_def
  set dy : ℝ := (p.j - p'.j : ℝ) with hdy_def
  set k : ℝ := (Int.natAbs (p.i - p'.i) : ℝ) with hk_def
  have hk_pos : 0 < k := by
    have h : 0 < Int.natAbs (p.i - p'.i) := by
      apply Nat.pos_of_ne_zero
      intro h'
      rw [h'] at hk <;> norm_num at hk
    have h' : (0 : ℝ) < ↑(Int.natAbs (p.i - p'.i)) := by exact_mod_cast h
    simpa [hk_def] using h'
  have h_abs_dx : |dx| = k := by
    let z : ℤ := p.i - p'.i
    have h_main : ∀ (z : ℤ), |(z : ℝ)| = (Int.natAbs z : ℝ) := by
      intro z
      by_cases hz : 0 ≤ z
      · -- z ≥ 0
        have h1 : (Int.natAbs z : ℤ) = z := Int.natAbs_of_nonneg hz
        have h2 : ((Int.natAbs z : ℤ) : ℝ) = ((z : ℤ) : ℝ) := by
          exact congr_arg (fun x : ℤ => (x : ℝ)) h1
        have h3 : (Int.natAbs z : ℝ) = ((Int.natAbs z : ℤ) : ℝ) := by simp
        have h4 : (Int.natAbs z : ℝ) = (z : ℝ) := by
          rw [h3, h2] <;> simp
        have hz' : 0 ≤ (z : ℝ) := by exact_mod_cast hz
        rw [abs_of_nonneg hz']
        exact h4.symm
      · -- z < 0
        have hneg : z < 0 := by linarith
        have h3 : 0 ≤ -z := by linarith
        have h4 : (Int.natAbs (-z) : ℤ) = -z := Int.natAbs_of_nonneg h3
        have h5 : Int.natAbs z = Int.natAbs (-z) := by simp
        have h1 : (Int.natAbs z : ℤ) = -z := by
          rw [h5] <;> exact h4
        have h2 : ((Int.natAbs z : ℤ) : ℝ) = ((-z : ℤ) : ℝ) := by
          exact congr_arg (fun x : ℤ => (x : ℝ)) h1
        have h3' : (Int.natAbs z : ℝ) = ((Int.natAbs z : ℤ) : ℝ) := by simp
        have h6 : (Int.natAbs z : ℝ) = -(z : ℝ) := by
          rw [h3', h2] <;> simp
        have hz'' : (z : ℝ) < 0 := by exact_mod_cast hneg
        rw [abs_of_neg hz'']
        exact h6.symm
    simpa [hdx_def, hk_def] using h_main z
  have hdx_ne_zero : dx ≠ 0 := by
    have h : 0 < |dx| := by rw [h_abs_dx] <;> exact hk_pos
    exact abs_pos.mp h

  -- Square membership gives coordinate bounds
  have hx1 : (p.i : ℝ) * δ ≤ x.1 := hxS.1
  have hx2 : x.1 < ((p.i : ℝ) + 1) * δ := hxS.2.1
  have hx3 : (p.j : ℝ) * δ ≤ x.2 := hxS.2.2.1
  have hx4 : x.2 < ((p.j : ℝ) + 1) * δ := hxS.2.2.2
  have hy1 : (p'.i : ℝ) * δ ≤ y.1 := hyS.1
  have hy2 : y.1 < ((p'.i : ℝ) + 1) * δ := hyS.2.1
  have hy3 : (p'.j : ℝ) * δ ≤ y.2 := hyS.2.2.1
  have hy4 : y.2 < ((p'.j : ℝ) + 1) * δ := hyS.2.2.2

  -- Remainders in [0, δ)
  set u1 := x.1 - (p.i : ℝ) * δ with hu1_def
  set u2 := x.2 - (p.j : ℝ) * δ with hu2_def
  set v1 := y.1 - (p'.i : ℝ) * δ with hv1_def
  set v2 := y.2 - (p'.j : ℝ) * δ with hv2_def
  have h_abs_u1v1 : |u1 - v1| ≤ δ := by
    have h1 : -δ ≤ u1 - v1 := by linarith
    have h2 : u1 - v1 ≤ δ := by linarith
    exact abs_le.mpr ⟨h1, h2⟩
  have h_abs_u2v2 : |u2 - v2| ≤ δ := by
    have h1 : -δ ≤ u2 - v2 := by linarith
    have h2 : u2 - v2 ≤ δ := by linarith
    exact abs_le.mpr ⟨h1, h2⟩

  -- Tube membership residuals
  have hT1 : |x.2 - T.slope * x.1 - T.intercept| ≤ δ := hxT
  have hT2 : |y.2 - T.slope * y.1 - T.intercept| ≤ δ := hyT

  set D := x.1 - y.1 with hD_def
  set N := x.2 - y.2 with hN_def

  -- |N - slope * D| ≤ 2δ
  have h_key1 : |N - T.slope * D| ≤ 2 * δ := by
    have h_eq : N - T.slope * D =
        (x.2 - T.slope * x.1 - T.intercept) - (y.2 - T.slope * y.1 - T.intercept) := by
      simp [hD_def, hN_def] <;> ring
    rw [h_eq]
    have h : |(x.2 - T.slope * x.1 - T.intercept) - (y.2 - T.slope * y.1 - T.intercept)| ≤
        |x.2 - T.slope * x.1 - T.intercept| + |y.2 - T.slope * y.1 - T.intercept| :=
      abs_sub (x.2 - T.slope * x.1 - T.intercept) (y.2 - T.slope * y.1 - T.intercept)
    linarith

  -- D = dx*δ + (u1-v1), N = dy*δ + (u2-v2)
  have hD_eq : D = dx * δ + (u1 - v1) := by
    simp [hD_def, hdx_def, hu1_def, hv1_def] <;> ring
  have hN_eq : N = dy * δ + (u2 - v2) := by
    simp [hN_def, hdy_def, hu2_def, hv2_def] <;> ring

  -- δ*(slope*dx - dy) = slope*D - N + (u2-v2) - slope*(u1-v1)
  have h_main_eq : δ * (T.slope * dx - dy) =
      T.slope * D - N + (u2 - v2) - T.slope * (u1 - v1) := by
    rw [hD_eq, hN_eq] <;> ring

  have h_abs_main : |δ * (T.slope * dx - dy)| ≤ 4 * δ := by
    have h_expr_eq : δ * (T.slope * dx - dy) =
        (T.slope * D - N) + ((u2 - v2) - T.slope * (u1 - v1)) := by
      rw [h_main_eq] <;> ring
    rw [h_expr_eq]
    set A := T.slope * D - N with hA_def
    set B := (u2 - v2) - T.slope * (u1 - v1) with hB_def
    have h_tri1 : |A + B| ≤ |A| + |B| := abs_add_le A B
    have hB_eq : B = (u2 - v2) + (-(T.slope * (u1 - v1))) := by
      simp [hB_def] <;> ring
    have h_tri2 : |B| ≤ |u2 - v2| + |T.slope * (u1 - v1)| := by
      rw [hB_eq]
      have h21 : |(u2 - v2) + (-(T.slope * (u1 - v1)))| ≤
          |u2 - v2| + |-(T.slope * (u1 - v1))| := abs_add_le _ _
      have h22 : |-(T.slope * (u1 - v1))| = |T.slope * (u1 - v1)| := by rw [abs_neg]
      rw [h22] at h21
      exact h21
    have h_neg : |A| = |N - T.slope * D| := by
      have h : A = -(N - T.slope * D) := by
        simp [hA_def] <;> ring
      rw [h, abs_neg]
    have h_mul : |T.slope * (u1 - v1)| = |T.slope| * |u1 - v1| := by rw [abs_mul]
    have h_slope_u1v1 : |T.slope| * |u1 - v1| ≤ δ := by
      calc |T.slope| * |u1 - v1|
          ≤ 1 * |u1 - v1| := by gcongr <;> linarith
        _ = |u1 - v1| := by ring
        _ ≤ δ := h_abs_u1v1
    have h2 : |A + B| ≤ |A| + |u2 - v2| + |T.slope * (u1 - v1)| := by
      have h_step1 : |A + B| ≤ |A| + |B| := h_tri1
      have h_step2 : |A| + |B| ≤ |A| + (|u2 - v2| + |T.slope * (u1 - v1)|) := by
        linarith [h_tri2]
      have h_step3 : |A| + (|u2 - v2| + |T.slope * (u1 - v1)|) =
          |A| + |u2 - v2| + |T.slope * (u1 - v1)| := by ring
      linarith
    have h3 : |A + B| ≤ |N - T.slope * D| + |u2 - v2| + |T.slope| * |u1 - v1| := by
      calc |A + B|
        ≤ |A| + |u2 - v2| + |T.slope * (u1 - v1)| := h2
      _ = |N - T.slope * D| + |u2 - v2| + |T.slope| * |u1 - v1| := by
        rw [h_neg, h_mul] <;> ring
    have h4 : |A + B| ≤ 4 * δ := by
      have h5 : |A + B| ≤ |N - T.slope * D| + |u2 - v2| + |T.slope| * |u1 - v1| := h3
      have h6 : |N - T.slope * D| ≤ 2 * δ := h_key1
      have h7 : |u2 - v2| ≤ δ := h_abs_u2v2
      have h8 : |T.slope| * |u1 - v1| ≤ δ := h_slope_u1v1
      linarith
    exact h4

  have h_abs_slope_dx_dy : |T.slope * dx - dy| ≤ 4 := by
    have h3 : |δ * (T.slope * dx - dy)| = δ * |T.slope * dx - dy| := by
      rw [abs_mul, abs_of_pos hδ_pos]
    rw [h3] at h_abs_main
    nlinarith

  -- |slope - dy/dx| = |slope*dx - dy| / |dx| ≤ 4/k ≤ 12/k
  have h_final : |T.slope - dy / dx| = |T.slope * dx - dy| / |dx| := by
    have h6 : T.slope - dy / dx = (T.slope * dx - dy) / dx := by
      field_simp [hdx_ne_zero] <;> ring
    rw [h6, abs_div] <;> rfl
  rw [h_final, h_abs_dx]
  have h7 : |T.slope * dx - dy| / k ≤ 4 / k := by
    gcongr <;> linarith
  have h8 : 4 / k ≤ 12 / k := by
    gcongr <;> norm_num <;> linarith
  exact h7.trans h8

/-- **Slope interval bound**: If two tubes with |slope| ≤ 1 both intersect
two distinct squares p and p', and the x-grid distance k = |p.i - p'.i| ≥ 2,
then their slopes differ by at most 24/k. -/
lemma slope_interval_bound {T₁ T₂ : DTube n} {p p' : DSquare n}
    (h1 : (T₁.toSet ∩ p.toSet).Nonempty)
    (h2 : (T₁.toSet ∩ p'.toSet).Nonempty)
    (h3 : (T₂.toSet ∩ p.toSet).Nonempty)
    (h4 : (T₂.toSet ∩ p'.toSet).Nonempty)
    (h_slope1 : |T₁.slope| ≤ 1)
    (h_slope2 : |T₂.slope| ≤ 1)
    (hk : 2 ≤ Int.natAbs (p.i - p'.i)) :
    |T₁.slope - T₂.slope| ≤ 24 / (Int.natAbs (p.i - p'.i) : ℝ) := by
  set m₀ : ℝ := (p.j - p'.j : ℝ) / (p.i - p'.i : ℝ) with hm₀_def
  have h1' : |T₁.slope - m₀| ≤ 12 / (Int.natAbs (p.i - p'.i) : ℝ) :=
    single_slope_bound h1 h2 h_slope1 hk
  have h2' : |T₂.slope - m₀| ≤ 12 / (Int.natAbs (p.i - p'.i) : ℝ) :=
    single_slope_bound h3 h4 h_slope2 hk
  have h_tri : |T₁.slope - T₂.slope| ≤ |T₁.slope - m₀| + |T₂.slope - m₀| := by
    have h4 : T₁.slope - T₂.slope = (T₁.slope - m₀) - (T₂.slope - m₀) := by ring
    rw [h4]
    have h5 : |(T₁.slope - m₀) - (T₂.slope - m₀)| ≤ |T₁.slope - m₀| + |T₂.slope - m₀| := by
      exact abs_sub (T₁.slope - m₀) (T₂.slope - m₀)
    exact h5
  have h6 : |T₁.slope - m₀| + |T₂.slope - m₀| ≤ 24 / (Int.natAbs (p.i - p'.i) : ℝ) := by
    calc |T₁.slope - m₀| + |T₂.slope - m₀|
      ≤ 12 / (Int.natAbs (p.i - p'.i) : ℝ) + 12 / (Int.natAbs (p.i - p'.i) : ℝ) := by gcongr
    _ = 24 / (Int.natAbs (p.i - p'.i) : ℝ) := by ring
  exact h_tri.trans h6

-- ============================================================================
-- (δ,s,C)-sets for finite sets
-- ============================================================================

/-- A `Finset` version of `IsDeltaSSet`. -/
def IsFinsetDeltaSSet {X : Type*} [MetricSpace X]
    (δ s C : ℝ) (P : Finset X) : Prop :=
  IsDeltaSSet δ s C (P : Set X)

-- ============================================================================
-- Helper lemmas for incidence bounds
-- ============================================================================

/-- At most 3 integers `a` satisfy `a * δ ∈ [x - δ, x + δ]`. -/
lemma int_grid_interval_bound {δ x : ℝ} (hδ : 0 < δ) {A : Finset ℤ}
    (hA : ∀ a ∈ A, (a : ℝ) * δ ∈ Set.Icc (x - δ) (x + δ)) : A.card ≤ 3 := by
  by_cases hne : A.Nonempty
  · let amin := A.min' hne
    let amax := A.max' hne
    have hmin : amin ∈ A := A.min'_mem hne
    have hmax : amax ∈ A := A.max'_mem hne
    have h2 : ∀ a ∈ A, amin ≤ a ∧ a ≤ amax := by
      intro a ha
      exact ⟨Finset.min'_le _ _ ha, Finset.le_max' _ _ ha⟩
    have h3 : A ⊆ Finset.Icc amin amax := by
      intro a ha
      exact Finset.mem_Icc.mpr (h2 a ha)
    have h4 : A.card ≤ (Finset.Icc amin amax).card := Finset.card_le_card h3
    have h6 : (amax : ℝ) * δ ≤ x + δ := (hA amax hmax).2
    have h7 : x - δ ≤ (amin : ℝ) * δ := (hA amin hmin).1
    have h8 : (amax : ℝ) * δ - (amin : ℝ) * δ ≤ 2 * δ := by linarith
    have h9 : ((amax : ℝ) - (amin : ℝ)) * δ ≤ 2 * δ := by
      have h10 : ((amax : ℝ) - (amin : ℝ)) * δ = (amax : ℝ) * δ - (amin : ℝ) * δ :=
        sub_mul (amax : ℝ) (amin : ℝ) δ
      rw [h10]; exact h8
    have h11 : (amax : ℝ) - (amin : ℝ) ≤ 2 := by nlinarith
    have h12 : amax - amin ≤ 2 := by exact_mod_cast h11
    have h13 : (Finset.Icc amin amax).card ≤ 3 := by
      have h14 : (Finset.Icc amin amax) ⊆ Finset.Icc amin (amin + 2) := by
        intro x hx
        have h1 : amin ≤ x := (Finset.mem_Icc.mp hx).1
        have h2 : x ≤ amax := (Finset.mem_Icc.mp hx).2
        have h3 : x ≤ amin + 2 := by omega
        exact Finset.mem_Icc.mpr ⟨h1, h3⟩
      have h15 : (Finset.Icc amin amax).card ≤ (Finset.Icc amin (amin + 2)).card :=
        Finset.card_le_card h14
      have h16 : (Finset.Icc amin (amin + 2)).card = 3 := by
        have h17 : Finset.Icc amin (amin + 2) = {amin, amin + 1, amin + 2} := by
          ext x
          simp [Finset.mem_Icc]
          <;> omega
        rw [h17]
        simp [Finset.mem_insert, Finset.mem_singleton]
        <;> omega
      rw [h16] at h15
      exact h15
    exact le_trans h4 h13
  · have h_empty : A = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using hne
    rw [h_empty] <;> simp

/-- A ball of radius `δ` contains at most 9 DTube grid points. -/
lemma dtube_ball_packing {n : ℕ} {c : DTube n} {S : Finset (DTube n)} :
    (S.filter (fun t => dist t c ≤ δ n)).card ≤ 9 := by
  have hδ : 0 < δ n := δ_pos n
  let hx := c.slope
  let hy := c.intercept
  have h_dist_def : ∀ (t : DTube n), dist t c = max (|t.slope - hx|) (|t.intercept - hy|) := by
    intro t; rfl
  have h1 : ∀ t ∈ S, dist t c ≤ δ n →
      |t.slope - hx| ≤ δ n ∧ |t.intercept - hy| ≤ δ n := by
    intro t _ hdist
    have h_eq : dist t c = max (|t.slope - hx|) (|t.intercept - hy|) := h_dist_def t
    rw [h_eq] at hdist
    have h21 : |t.slope - hx| ≤ max (|t.slope - hx|) (|t.intercept - hy|) := le_max_left _ _
    have h22 : |t.intercept - hy| ≤ max (|t.slope - hx|) (|t.intercept - hy|) := le_max_right _ _
    exact ⟨by linarith, by linarith⟩
  let S' := S.filter (fun t => dist t c ≤ δ n)
  let A := S'.image DTube.a
  let B := S'.image DTube.b
  have hA : ∀ a ∈ A, (a : ℝ) * (δ n) ∈ Set.Icc (hx - δ n) (hx + δ n) := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨t, ht, rfl⟩
    have h_dist : dist t c ≤ δ n := (Finset.mem_filter.mp ht).2
    have h2 := h1 t (Finset.mem_filter.mp ht).1 h_dist
    have h_slope_eq : t.slope = (t.a : ℝ) * (δ n) := by rfl
    have h_abs : |t.slope - hx| ≤ δ n := h2.1
    have h3 : -(δ n) ≤ t.slope - hx := (abs_le.mp h_abs).1
    have h4 : t.slope - hx ≤ δ n := (abs_le.mp h_abs).2
    exact ⟨by linarith [h_slope_eq], by linarith [h_slope_eq]⟩
  have hB : ∀ b ∈ B, (b : ℝ) * (δ n) ∈ Set.Icc (hy - δ n) (hy + δ n) := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨t, ht, rfl⟩
    have h_dist : dist t c ≤ δ n := (Finset.mem_filter.mp ht).2
    have h2 := h1 t (Finset.mem_filter.mp ht).1 h_dist
    have h_intercept_eq : t.intercept = (t.b : ℝ) * (δ n) := by rfl
    have h_abs : |t.intercept - hy| ≤ δ n := h2.2
    have h3 : -(δ n) ≤ t.intercept - hy := (abs_le.mp h_abs).1
    have h4 : t.intercept - hy ≤ δ n := (abs_le.mp h_abs).2
    exact ⟨by linarith [h_intercept_eq], by linarith [h_intercept_eq]⟩
  have hA_card : A.card ≤ 3 := int_grid_interval_bound hδ hA
  have hB_card : B.card ≤ 3 := int_grid_interval_bound hδ hB
  have h_inj : Set.InjOn (fun t : DTube n => (t.a, t.b)) (S' : Set (DTube n)) := by
    intro t1 _ t2 _ h
    have ha : t1.a = t2.a := by simp [Prod.ext_iff] at h <;> tauto
    have hb : t1.b = t2.b := by simp [Prod.ext_iff] at h <;> tauto
    cases t1 <;> cases t2 <;> simp_all
  have h_img : (S'.image (fun t => (t.a, t.b))).card = S'.card :=
    Finset.card_image_of_injOn h_inj
  have h_sub : (S'.image (fun t => (t.a, t.b))) ⊆ A ×ˢ B := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨t, ht, rfl⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨t, ht, rfl⟩, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩
  calc S'.card
    = (S'.image (fun t => (t.a, t.b))).card := h_img.symm
  _ ≤ (A ×ˢ B).card := Finset.card_le_card h_sub
  _ = A.card * B.card := by simp
  _ ≤ 3 * 3 := by gcongr
  _ = 9 := by norm_num

-- ============================================================================
-- Helper lemmas for incidence estimates
-- ============================================================================

/-- Lower bound on cardinality of a nonempty (δ,t,C)-set:
`|P| ≥ C^{-1} δ^{-t}`, obtained by applying the δ-set condition at radius δ
around a single point. -/
lemma delta_set_card_lower {X : Type*} [MetricSpace X]
    {δ t C : ℝ} {P : Finset X}
    (hP : IsFinsetDeltaSSet δ t C P) (hP_nonempty : P.Nonempty) :
    (P.card : ℝ) ≥ C⁻¹ * δ^(-t) := by
  have hδ : 0 < δ := hP.2.1
  have hC : 0 < C := hP.2.2.1
  have ht : 0 ≤ t := hP.2.2.2.1
  have hP_card_pos : 0 < P.card := by
    exact Finset.card_pos.mpr hP_nonempty
  rcases hP_nonempty with ⟨x, hx⟩
  let Pset : Set X := (P : Set X)
  have h1 : x ∈ Pset ∩ Metric.closedBall x δ := by
    exact ⟨Finset.mem_coe.mpr hx, Metric.mem_closedBall_self (by linarith)⟩
  have h2 : (Pset ∩ Metric.closedBall x δ).Nonempty := ⟨x, h1⟩
  have h_ne_zero : Metric.externalCoveringNumber δ.toNNReal (Pset ∩ Metric.closedBall x δ) ≠ 0 := by
    intro h
    have h_empty : Pset ∩ Metric.closedBall x δ = ∅ :=
      (Metric.externalCoveringNumber_eq_zero.mp h)
    exact h2.ne_empty h_empty
  have h3 : (Metric.externalCoveringNumber δ.toNNReal (Pset ∩ Metric.closedBall x δ) : ENNReal) ≥ 1 := by
    have h4 : ∀ (n : ℕ∞), n ≠ 0 → (n : ENNReal) ≥ 1 := by
      intro n hn
      by_cases h_top : n = ⊤
      · rw [h_top] <;> simp
      · have h5 : ∃ (k : ℕ), n = ↑k := by
          have h6 : ∃ (a : ℕ), (↑a : ℕ∞) = n := (WithTop.ne_top_iff_exists).mp h_top
          rcases h6 with ⟨k, hk⟩
          exact ⟨k, hk.symm⟩
        rcases h5 with ⟨k, rfl⟩
        have h6 : k ≠ 0 := by
          intro h7
          rw [h7] at hn <;> simp at hn
        have h7 : 1 ≤ k := Nat.pos_of_ne_zero h6
        exact_mod_cast h7
    exact h4 _ h_ne_zero
  have h4 := hP.2.2.2.2 x δ (by linarith)
  have h5 : (1 : ENNReal) ≤ ENNReal.ofReal C * (ENNReal.ofReal δ)^t *
      Metric.externalCoveringNumber δ.toNNReal Pset := by
    calc (1 : ENNReal)
      ≤ (Metric.externalCoveringNumber δ.toNNReal (Pset ∩ Metric.closedBall x δ) : ENNReal) := h3
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal δ)^t *
          (Metric.externalCoveringNumber δ.toNNReal Pset : ENNReal) := by
      exact_mod_cast h4
  have h6 : (Metric.externalCoveringNumber δ.toNNReal Pset : ENNReal) ≤ ↑(P.card) := by
    have h7 : Metric.externalCoveringNumber δ.toNNReal Pset ≤ Pset.encard :=
      Metric.externalCoveringNumber_le_encard_self Pset
    have h8 : Pset.encard = ↑(P.card) := by
      exact Set.encard_coe_eq_coe_finsetCard P
    rw [h8] at h7
    exact_mod_cast h7
  have h9 : (1 : ENNReal) ≤ ENNReal.ofReal C * (ENNReal.ofReal δ)^t * ↑(P.card) := by
    calc (1 : ENNReal)
      ≤ ENNReal.ofReal C * (ENNReal.ofReal δ)^t *
          (Metric.externalCoveringNumber δ.toNNReal Pset : ENNReal) := h5
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal δ)^t * ↑(P.card) := by
      gcongr
      <;> exact h6
  have h_pos1 : 0 < C * δ^t * (P.card : ℝ) :=
    mul_pos (mul_pos hC (Real.rpow_pos_of_pos hδ t)) (by exact_mod_cast hP_card_pos)
  have h10 : ENNReal.ofReal C * (ENNReal.ofReal δ)^t * (↑(P.card) : ENNReal) =
      ENNReal.ofReal (C * δ^t * (P.card : ℝ)) := by
    have h11 : (ENNReal.ofReal δ)^t = ENNReal.ofReal (δ^t) := by
      have h12 : (ENNReal.ofReal δ)^t = ENNReal.ofReal (δ^t) :=
        ENNReal.ofReal_rpow_of_pos (hx_pos := hδ)
      exact h12
    rw [h11]
    have h13 : ENNReal.ofReal C * ENNReal.ofReal (δ^t) * (↑(P.card) : ENNReal) =
        ENNReal.ofReal (C * δ^t * (P.card : ℝ)) := by
      have h14 : (↑(P.card) : ENNReal) = ENNReal.ofReal ((P.card : ℝ)) := by
        simp
      rw [h14]
      have hC_nonneg : 0 ≤ C := by linarith
      have hdt_nonneg : 0 ≤ δ^t := by positivity
      have hcard_nonneg : 0 ≤ (P.card : ℝ) := by positivity
      have h_mul1 : ENNReal.ofReal C * ENNReal.ofReal (δ^t) = ENNReal.ofReal (C * δ^t) := by
        rw [← ENNReal.ofReal_mul hC_nonneg]
      rw [h_mul1]
      have h_mul2 : ENNReal.ofReal (C * δ^t) * ENNReal.ofReal (P.card : ℝ) =
          ENNReal.ofReal ((C * δ^t) * (P.card : ℝ)) := by
        rw [← ENNReal.ofReal_mul (show 0 ≤ C * δ^t by positivity)]
      rw [h_mul2]
      <;> ring_nf
    exact h13
  rw [h10] at h9
  have h12 : (1 : ℝ) ≤ C * δ^t * (P.card : ℝ) := by
    have h13 : (1 : ENNReal) ≤ ENNReal.ofReal (C * δ^t * (P.card : ℝ)) := h9
    have h13' : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (C * δ^t * (P.card : ℝ)) := by
      simpa using h13
    have h14 : 0 ≤ C * δ^t * (P.card : ℝ) := by positivity
    have h_iff : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (C * δ^t * (P.card : ℝ)) ↔
        (1 : ℝ) ≤ C * δ^t * (P.card : ℝ) :=
      ENNReal.ofReal_le_ofReal_iff h14
    exact h_iff.mp h13'
  have h_pos : 0 < C * δ^t := mul_pos hC (Real.rpow_pos_of_pos hδ t)
  have h_ne : C * δ^t ≠ 0 := h_pos.ne'
  have h15 : (P.card : ℝ) ≥ C⁻¹ * δ^(-t) := by
    have h16 : (P.card : ℝ) ≥ 1 / (C * δ^t) := by
      have h_eq : (C * δ^t)⁻¹ * (C * δ^t * (P.card : ℝ)) = (P.card : ℝ) := by
        field_simp [h_ne, hC.ne', hδ.ne'] <;> ring
      have h_ineq : 1 ≤ C * δ^t * (P.card : ℝ) := h12
      calc (P.card : ℝ)
        = (C * δ^t)⁻¹ * (C * δ^t * (P.card : ℝ)) := h_eq.symm
      _ ≥ (C * δ^t)⁻¹ * 1 := by gcongr
      _ = 1 / (C * δ^t) := by simp
    have h17 : 1 / (C * δ^t) = C⁻¹ * δ^(-t) := by
      have h18 : 1 / (C * δ^t) = (C * δ^t)⁻¹ := by simp
      rw [h18]
      have h19 : (C * δ^t)⁻¹ = C⁻¹ * (δ^t)⁻¹ := by
        rw [mul_inv] <;> ring
      rw [h19]
      have h20 : (δ^t)⁻¹ = δ^(-t) := by
        have h21 : δ^t * δ^(-t) = 1 := by
          rw [← Real.rpow_add (by linarith)] <;> ring_nf <;> norm_num
        field_simp [h21] <;> linarith
      rw [h20] <;> ring
    rw [h17] at h16
    exact h16
  exact h15

/-- Number of integers `a` with `|a * δ| ≤ 1` is at most `3 * δ^{-1}`. -/
lemma slope_index_count_bound {δ : ℝ} (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    {A : Finset ℤ} (hA : ∀ a ∈ A, |(a : ℝ) * δ| ≤ 1) :
    (A.card : ℝ) ≤ 3 * δ⁻¹ := by
  let R : ℝ := δ⁻¹
  have hR_pos : 0 < R := by positivity
  have hR_ge_one : 1 ≤ R := by
    have h2 : δ⁻¹ ≥ 1 := by
      calc δ⁻¹ = 1 / δ := by simp
           _ ≥ 1 / 1 := by gcongr
           _ = 1 := by norm_num
    exact h2
  have h1 : ∀ a ∈ A, (a : ℝ) ∈ Set.Icc (-R) R := by
    intro a ha
    have h2 : |(a : ℝ)| ≤ R := by
      have h3 : |(a : ℝ) * δ| ≤ 1 := hA a ha
      have h4 : |(a : ℝ) * δ| = |(a : ℝ)| * δ := by
        rw [abs_mul, abs_of_pos hδ]
      rw [h4] at h3
      calc |(a : ℝ)|
        = |(a : ℝ)| * δ / δ := by field_simp [hδ.ne'] <;> ring
      _ ≤ 1 / δ := by gcongr
      _ = R := by simp [R]
    exact abs_le.mp h2
  let lo : ℤ := ⌈-R⌉
  let hi : ℤ := ⌊R⌋
  have h_lo : -R ≤ (lo : ℝ) := Int.le_ceil (-R)
  have h_hi : (hi : ℝ) ≤ R := Int.floor_le R
  have h2 : ∀ a ∈ A, lo ≤ a ∧ a ≤ hi := by
    intro a ha
    have h3 : -R ≤ (a : ℝ) := (h1 a ha).1
    have h4 : (a : ℝ) ≤ R := (h1 a ha).2
    constructor
    · exact_mod_cast (Int.ceil_le.mpr h3)
    · exact_mod_cast (Int.le_floor.mpr h4)
  have h3 : A ⊆ Finset.Icc lo hi := by
    intro a ha
    exact Finset.mem_Icc.mpr (h2 a ha)
  have h4 : A.card ≤ (Finset.Icc lo hi).card := Finset.card_le_card h3
  have h5 : lo ≤ hi := by
    have h_lo_up : (lo : ℝ) < -R + 1 := Int.ceil_lt_add_one (-R)
    have h_hi_dn : R - 1 < (hi : ℝ) := Int.sub_one_lt_floor R
    have h6 : (lo : ℝ) ≤ (hi : ℝ) := by linarith
    exact_mod_cast h6
  have h6 : ((Finset.Icc lo hi).card : ℝ) = (hi : ℝ) - (lo : ℝ) + 1 := by
    have h8 : lo ≤ hi + 1 := by linarith
    have h9 : ((Finset.Icc lo hi).card : ℤ) = hi + 1 - lo := Int.card_Icc_of_le lo hi h8
    have h10 : ((Finset.Icc lo hi).card : ℝ) = (hi : ℝ) - (lo : ℝ) + 1 := by
      exact_mod_cast (by rw [h9] <;> ring)
    exact h10
  have h7 : ((Finset.Icc lo hi).card : ℝ) ≤ 3 * R := by
    rw [h6]
    have h_lo_up : (lo : ℝ) ≥ -R := Int.le_ceil (-R)
    have h_hi_dn : (hi : ℝ) ≤ R := Int.floor_le R
    linarith
  have h8 : (A.card : ℝ) ≤ 3 * R := by
    calc (A.card : ℝ)
      ≤ ((Finset.Icc lo hi).card : ℝ) := by exact_mod_cast h4
    _ ≤ 3 * R := h7
  simpa [R] using h8

/-- Upper bound on the number of dyadic δ-tubes with |slope| ≤ 1 passing through
a common square: at most `27 * δ^{-1}`. Uses `tubesSlopes` (≤9 per slope index)
and counting possible slope indices in [-1,1]. -/
lemma tubes_per_square_bound {n : ℕ} {p : DSquare n} {Ts : Finset (DTube n)}
    (hTs : ∀ T ∈ Ts, (T.toSet ∩ p.toSet).Nonempty)
    (h_bound : ∀ T ∈ Ts, |T.slope| ≤ 1) :
    (Ts.card : ℝ) ≤ 27 * (δ n)⁻¹ := by
  have hδ : 0 < δ n := δ_pos n
  have hδ_le_one : δ n ≤ 1 := δ_le_one n
  let A := Ts.image DTube.a
  have hA_slopes : ∀ a ∈ A, |(a : ℝ) * (δ n)| ≤ 1 := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨t, ht, rfl⟩
    have h_slope : |t.slope| ≤ 1 := h_bound t ht
    have h_eq : t.slope = (t.a : ℝ) * (δ n) := by rfl
    rw [h_eq] at h_slope
    exact h_slope
  have hA_card : (A.card : ℝ) ≤ 3 * (δ n)⁻¹ :=
    slope_index_count_bound hδ hδ_le_one hA_slopes
  have h_disj : ∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ ≠ a₂ →
      Disjoint (Ts.filter (fun T => T.a = a₁)) (Ts.filter (fun T => T.a = a₂)) := by
    intro a₁ _ a₂ _ hne
    simp only [Finset.disjoint_left, Finset.mem_filter]
    intro t ht1 ht2
    exact hne (ht1.2.symm.trans ht2.2)
  have h_eq : Ts = A.biUnion (fun a => Ts.filter (fun T => T.a = a)) := by
    ext t
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    <;> constructor
    · intro ht
      exact ⟨t.a, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ht, rfl⟩
    · rintro ⟨a, _, ht, rfl⟩
      exact ht
  have h_sum : Ts.card = ∑ a ∈ A, (Ts.filter (fun T => T.a = a)).card := by
    have h3 : Ts.card = (A.biUnion (fun a => Ts.filter (fun T => T.a = a))).card :=
      congr_arg Finset.card h_eq
    rw [h3]
    exact Finset.card_biUnion h_disj
  have h14 : ∑ a ∈ A, (Ts.filter (fun T => T.a = a)).card ≤ ∑ a ∈ A, 9 := by
    apply Finset.sum_le_sum
    intro a _
    exact tubesSlopes hTs h_bound a
  have h15 : ∑ a ∈ A, (9 : ℕ) = 9 * A.card := by
    simp [Finset.sum_const]
    <;> ring
  have h16 : Ts.card ≤ 9 * A.card := by
    calc Ts.card
      = ∑ a ∈ A, (Ts.filter (fun T => T.a = a)).card := h_sum
    _ ≤ ∑ a ∈ A, 9 := h14
    _ = 9 * A.card := h15
  have h17 : (Ts.card : ℝ) ≤ 9 * (A.card : ℝ) := by exact_mod_cast h16
  have h18 : 9 * (A.card : ℝ) ≤ 9 * (3 * (δ n)⁻¹) := by
    gcongr <;> exact hA_card
  have h19 : 9 * (3 * (δ n)⁻¹) = 27 * (δ n)⁻¹ := by ring
  rw [h19] at h18
  exact h17.trans h18

/-- Given L > 1, a > 0, c > 0, K0 ≥ 0, there exists K > 0 with K ≥ K0 and
`K * a * L^(K-K0) ≥ c`. Used to absorb constants into log factors. -/
lemma exists_K_large_general (L a c K0 : ℝ) (hL : 1 < L) (ha : 0 < a)
    (hc : 0 < c) (hK0 : 0 ≤ K0) :
    ∃ K : ℝ, 0 < K ∧ K ≥ K0 ∧ K * a * L^(K - K0) ≥ c := by
  set K : ℝ := max K0 (c / a) + 1 with hK_def
  have hK_ge_K0 : K ≥ K0 := by
    rw [hK_def]
    have h : max K0 (c / a) ≥ K0 := le_max_left _ _
    linarith
  have hK_pos : 0 < K := by
    rw [hK_def]
    have h2 : 0 ≤ K0 := hK0
    have h3 : 0 ≤ max K0 (c / a) := by positivity
    linarith
  have h1 : K ≥ c / a := by
    rw [hK_def]
    have h2 : max K0 (c / a) ≥ c / a := le_max_right _ _
    linarith
  have h2 : K * a ≥ c := by
    have h3 : K * a ≥ (c / a) * a := by gcongr
    have h4 : (c / a) * a = c := by field_simp [ha.ne'] <;> ring
    linarith
  have h5 : 0 ≤ K - K0 := by linarith
  have h6 : L^(K - K0) ≥ 1 := by
    have h7 : L^(0 : ℝ) ≤ L^(K - K0) := Real.rpow_le_rpow_of_exponent_le (by linarith) h5
    simpa using h7
  have h7 : K * a * L^(K - K0) ≥ K * a := by
    have h8 : 0 ≤ K * a := by positivity
    nlinarith
  have h8 : K * a * L^(K - K0) ≥ c := by linarith
  exact ⟨K, hK_pos, hK_ge_K0, h8⟩

/-- Auxiliary type for tube families indexed by squares. -/
abbrev TubeFamily (n : ℕ) := DSquare n → Finset (DTube n)

/-- **OS Corollary 2.5 `prop5`**:
|T| ≳_δ (C_P C_T)^{-1} * M * δ^{-s} * (M δ^s)^{(t-s)/(1-s)}.

Proof: `T ⊇ Tp p0`, so `|T| ≥ M/2`. Choose `K` large enough that
`K * C_P * C_T * log(1/δ)^K ≥ 108 * δ^{-1}`; then the desired RHS is `≤ M/2`.
The key estimate is `δ^{-s} (M δ^s)^α ≤ 54 δ^{-1}`, using `M δ ≤ 54`. -/
theorem prop5
    (s t : ℝ) (h_st : 0 ≤ s ∧ s ≤ t ∧ t ≤ 1)
    (C_P C_T M : ℝ) (hCP : 0 < C_P) (hCT : 0 < C_T) (hM : 1 ≤ M)
    (h_n_ge_2 : 2 ≤ n)
    (P : Finset (DSquare n))
    (hP_nonempty : P.Nonempty)
    (hP_set : IsFinsetDeltaSSet (δ n) t C_P P)
    (Tp : TubeFamily n)
    (hTp_int : ∀ p ∈ P, ∀ t ∈ Tp p, (t.toSet ∩ p.toSet).Nonempty)
    (hTp_slope : ∀ p ∈ P, ∀ t ∈ Tp p, |t.slope| ≤ 1)
    (hTp_set : ∀ p ∈ P, IsFinsetDeltaSSet (δ n) s C_T (Tp p))
    (hTp_card : ∀ p ∈ P, M / 2 < (Tp p).card) :
    ∃ (K : ℝ), 0 < K ∧
      let T := P.biUnion fun p => Tp p
      T.card ≥ (1 / K) * Real.log (1 / δ n) ^ (-K) *
        (1 / (C_P * C_T)) * M * (δ n) ^ (-s) *
          (M * (δ n) ^ s) ^ ((t - s) / (1 - s)) := by
  set d : ℝ := δ n with hd_def
  set L : ℝ := Real.log (1 / d) with hL_def
  let T := P.biUnion Tp
  let α : ℝ := (t - s) / (1 - s)

  have hd_pos : 0 < d := δ_pos n
  have hd_le_quarter : d ≤ 1 / 4 := by
    rw [hd_def]
    have h1 : (n : ℕ) ≥ 2 := h_n_ge_2
    have h2 : (δ n) = ((2 : ℝ)^n)⁻¹ := by
      unfold δ
      simp [zpow_neg, zpow_ofNat]
      <;> ring
    rw [h2]
    have h3 : (2 : ℝ)^n ≥ 4 := by
      have h4 : (2 : ℝ)^n ≥ (2 : ℝ)^(2 : ℕ) := by gcongr <;> norm_num
      norm_num at h4 ⊢ <;> exact h4
    have h5 : 0 < (2 : ℝ)^n := by positivity
    have h6 : ((2 : ℝ)^n)⁻¹ ≤ 1 / 4 := by
      have h7 : (4 : ℝ) ≤ (2 : ℝ)^n := h3
      have h8 : ((2 : ℝ)^n)⁻¹ ≤ (4 : ℝ)⁻¹ := by gcongr
      norm_num at h8 ⊢ <;> exact h8
    exact h6
  have hL_gt_one : 1 < L := by
    rw [hL_def]
    have h3 : 1 / d ≥ 4 := by
      have h4 : d ≤ 1 / 4 := hd_le_quarter
      have h5 : 0 < d := hd_pos
      calc 1 / d ≥ 1 / (1 / 4) := by gcongr
      _ = 4 := by norm_num
    have h4 : Real.log (1 / d) ≥ Real.log 4 := Real.log_le_log (by positivity) h3
    have h5 : (1 : ℝ) < Real.log 4 := by
      have h6 : Real.exp 1 < (4 : ℝ) := by linarith [Real.exp_one_lt_d9]
      have h7 : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (by positivity) h6
      have h8 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
      rw [h8] at h7; exact h7
    linarith
  have hL_pos : 0 < L := by linarith

  rcases hP_nonempty with ⟨p0, hp0⟩

  have hT_lower : (T.card : ℝ) ≥ M / 2 := by
    have h1 : Tp p0 ⊆ T := by
      intro t ht
      exact Finset.mem_biUnion.mpr ⟨p0, hp0, ht⟩
    have h2 : (Tp p0).card ≤ T.card := Finset.card_le_card h1
    have h3 : M / 2 < (Tp p0).card := hTp_card p0 hp0
    have h4 : (M / 2 : ℝ) < ((Tp p0).card : ℝ) := by exact_mod_cast h3
    have h5 : ((Tp p0).card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast h2
    linarith

  have hMd_le : M * d ≤ 54 := by
    have h1 : (Tp p0).card ≤ 27 * d⁻¹ :=
      tubes_per_square_bound (hTp_int p0 hp0) (hTp_slope p0 hp0)
    have h2 : M / 2 < (Tp p0).card := hTp_card p0 hp0
    have h3 : M / 2 < 27 * d⁻¹ := by linarith
    have h4 : M < 54 * d⁻¹ := by linarith
    have h5 : M * d < 54 := by
      have h6 : 0 < d := hd_pos
      calc M * d
        < (54 * d⁻¹) * d := by gcongr
      _ = 54 := by field_simp [h6.ne'] <;> ring
    exact le_of_lt h5

  have hM_pos : 0 < M := by linarith

  have h_bound : Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α ≤ (54 : ℝ) * d⁻¹ := by
    by_cases h_s_lt_one : s < 1
    · -- s < 1 case
      have h1ms_pos : 0 < 1 - s := by linarith
      have hα_nonneg : 0 ≤ α := by
        dsimp only [α]; have h : 0 ≤ t - s := by linarith
        exact div_nonneg h (by linarith)
      have hα_le_one : α ≤ 1 := by
        dsimp only [α]; have h : t - s ≤ 1 - s := by linarith
        exact (div_le_one h1ms_pos).mpr h
      have hM_nonneg : 0 ≤ M := by linarith

      -- Key identity: d^{-s} * (M*d^s)^α = (M*d)^α * d^{-t}
      have h_id : Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α =
          Real.rpow (M * d) α * Real.rpow d (-t) := by
        have hds_nonneg : 0 ≤ Real.rpow d s := Real.rpow_nonneg (by linarith) s
        have h1 : Real.rpow (M * Real.rpow d s) α =
            Real.rpow M α * Real.rpow (Real.rpow d s) α :=
          Real.mul_rpow hM_nonneg hds_nonneg
        have h21 : Real.rpow d (s * α) = Real.rpow (Real.rpow d s) α :=
          Real.rpow_mul (by linarith) s α
        have h2 : Real.rpow (Real.rpow d s) α = Real.rpow d (s * α) := h21.symm
        have h31 : Real.rpow d (-s + s * α) = Real.rpow d (-s) * Real.rpow d (s * α) :=
          Real.rpow_add hd_pos (-s) (s * α)
        have h3 : Real.rpow d (-s) * Real.rpow d (s * α) = Real.rpow d (-s + s * α) := h31.symm
        have h4 : -s + s * α = -t + α := by
          dsimp only [α]; field_simp [h1ms_pos.ne'] <;> ring
        have h5 : Real.rpow d (-t + α) = Real.rpow d (-t) * Real.rpow d α :=
          Real.rpow_add hd_pos (-t) α
        have h61 : Real.rpow (M * d) α = Real.rpow M α * Real.rpow d α :=
          Real.mul_rpow hM_nonneg (by positivity)
        have h6 : Real.rpow M α * Real.rpow d α = Real.rpow (M * d) α := h61.symm
        calc Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α
          = Real.rpow d (-s) * (Real.rpow M α * Real.rpow (Real.rpow d s) α) := by rw [h1]
        _ = Real.rpow M α * (Real.rpow d (-s) * Real.rpow d (s * α)) := by rw [h2] <;> ring
        _ = Real.rpow M α * Real.rpow d (-s + s * α) := by rw [h3]
        _ = Real.rpow M α * Real.rpow d (-t + α) := by rw [h4]
        _ = Real.rpow M α * (Real.rpow d (-t) * Real.rpow d α) := by rw [h5]
        _ = (Real.rpow M α * Real.rpow d α) * Real.rpow d (-t) := by ring
        _ = Real.rpow (M * d) α * Real.rpow d (-t) := by rw [h6] <;> ring

      rw [h_id]

      -- (M*d)^α ≤ 54^α ≤ 54
      have hMd_nonneg : 0 ≤ M * d := by positivity
      have h8 : Real.rpow (M * d) α ≤ Real.rpow (54 : ℝ) α :=
        Real.rpow_le_rpow hMd_nonneg hMd_le hα_nonneg
      have h9 : Real.rpow (54 : ℝ) α ≤ 54 := by
        have h10 : Real.rpow (54 : ℝ) α ≤ Real.rpow (54 : ℝ) (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hα_le_one
        simpa using h10

      -- d^{-t} ≤ d^{-1}: use (d^{-1})^t ≤ (d^{-1})^1 since d^{-1} ≥ 1 and t ≤ 1
      have h_dinv_ge_one : 1 ≤ d⁻¹ := by
        have h11 : 0 < d := hd_pos
        have h12 : d ≤ 1 := by linarith [hd_le_quarter]
        calc 1 = d / d := by field_simp [h11.ne']
        _ ≤ 1 / d := by gcongr
        _ = d⁻¹ := by simp
      have h10 : Real.rpow d (-t) ≤ d⁻¹ := by
        have h_eq : Real.rpow d (-t) = Real.rpow d⁻¹ t :=
          Real.rpow_neg_eq_inv_rpow d t
        rw [h_eq]
        have h11 : Real.rpow d⁻¹ t ≤ Real.rpow d⁻¹ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h_dinv_ge_one (by linarith [h_st.2.2])
        have h12 : Real.rpow d⁻¹ (1 : ℝ) = d⁻¹ := by simp
        rw [h12] at h11
        exact h11

      have hdt_nonneg : 0 ≤ Real.rpow d (-t) := Real.rpow_nonneg (by linarith) (-t)
      have h_step1 : Real.rpow (M * d) α * Real.rpow d (-t) ≤ Real.rpow (54 : ℝ) α * Real.rpow d (-t) :=
        mul_le_mul_of_nonneg_right h8 hdt_nonneg
      have h_step2 : Real.rpow (54 : ℝ) α * Real.rpow d (-t) ≤ (54 : ℝ) * Real.rpow d (-t) :=
        mul_le_mul_of_nonneg_right h9 hdt_nonneg
      have h_step3 : (54 : ℝ) * Real.rpow d (-t) ≤ (54 : ℝ) * d⁻¹ :=
        mul_le_mul_of_nonneg_left h10 (by norm_num)
      exact le_trans h_step1 (le_trans h_step2 h_step3)

    · -- s = 1 case (then t = 1, α = 0 by Lean's 0/0 = 0)
      have h_s_eq_one : s = 1 := by linarith
      have h_t_eq_one : t = 1 := by linarith
      have hα_zero : α = 0 := by
        dsimp only [α]; rw [h_s_eq_one, h_t_eq_one] <;> ring
      rw [hα_zero, h_s_eq_one]
      have h10 : Real.rpow d (-1 : ℝ) = d⁻¹ := Real.rpow_neg_one d
      rw [h10]
      have h11 : Real.rpow (M * Real.rpow d (1 : ℝ)) (0 : ℝ) = 1 := Real.rpow_zero _
      rw [h11]
      have h12 : d⁻¹ ≤ (54 : ℝ) * d⁻¹ := by
        have h13 : 0 ≤ d⁻¹ := by positivity
        have h14 : d⁻¹ ≤ (54 : ℝ) * d⁻¹ := by
          calc d⁻¹ = (1 : ℝ) * d⁻¹ := by ring
          _ ≤ (54 : ℝ) * d⁻¹ := by gcongr <;> norm_num
        exact h14
      simpa using h12

  set K : ℝ := (108 : ℝ) * d⁻¹ / (C_P * C_T) with hK_def
  have hK_pos : 0 < K := by positivity

  have h3 : Real.rpow L K ≥ 1 := by
    have h4 : (0 : ℝ) ≤ K := by positivity
    have h5 : Real.rpow L (0 : ℝ) ≤ Real.rpow L K := Real.rpow_le_rpow_of_exponent_le (by linarith) h4
    simpa using h5

  have hK_ineq : K * C_P * C_T * Real.rpow L K ≥ 2 * Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α := by
    have h1 : K * C_P * C_T = (108 : ℝ) * d⁻¹ := by
      rw [hK_def] <;> field_simp [hCP.ne', hCT.ne'] <;> ring
    have h4 : K * C_P * C_T * Real.rpow L K ≥ (108 : ℝ) * d⁻¹ := by
      rw [h1]
      have h5 : ((108 : ℝ) * d⁻¹) * Real.rpow L K ≥ (108 : ℝ) * d⁻¹ := by
        have h6 : 0 ≤ (108 : ℝ) * d⁻¹ := by positivity
        nlinarith
      exact h5
    have h7 : 2 * Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α ≤ (108 : ℝ) * d⁻¹ := by
      have h8 : Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α ≤ (54 : ℝ) * d⁻¹ := h_bound
      linarith
    linarith

  have h13 : Real.rpow L (-K) * Real.rpow L K = 1 := by
    have h14 : Real.rpow L (-K + K) = Real.rpow L (-K) * Real.rpow L K := Real.rpow_add hL_pos (-K) K
    have h15 : -K + K = (0 : ℝ) := by ring
    have h16 : Real.rpow L (-K + K) = 1 := by
      rw [h15]
      exact Real.rpow_zero L
    have h17 : Real.rpow L (-K) * Real.rpow L K = Real.rpow L (-K + K) := h14.symm
    rw [h17, h16]

  have h9 : M / 2 ≥ (1 / K) * Real.rpow L (-K) * (1 / (C_P * C_T)) * M * Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α := by
    set factor := K * Real.rpow L K * C_P * C_T with hfactor_def
    have h_factor_pos : 0 < factor := by positivity
    have h10 : (M / 2) * factor ≥ M * Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α := by
      have h11 : K * C_P * C_T * Real.rpow L K ≥ 2 * Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α := hK_ineq
      have h12 : factor = K * C_P * C_T * Real.rpow L K := by
        simp [hfactor_def] <;> ring
      rw [h12]
      calc (M / 2) * (K * C_P * C_T * Real.rpow L K)
        ≥ (M / 2) * (2 * Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α) := by gcongr
      _ = M * Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α := by ring
    have h14 : ((1 / K) * Real.rpow L (-K) * (1 / (C_P * C_T)) * M * Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α) * factor = M * Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α := by
      rw [hfactor_def]
      have h_exp : Real.rpow L (-K) * Real.rpow L K = 1 := h13
      calc ((1 / K) * Real.rpow L (-K) * (1 / (C_P * C_T)) * M * Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α) * (K * Real.rpow L K * C_P * C_T)
        = ((1 / K) * K) * (Real.rpow L (-K) * Real.rpow L K) * ((1 / (C_P * C_T)) * (C_P * C_T)) * M * Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α := by ring
      _ = 1 * 1 * 1 * M * Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α := by
        rw [h_exp]
        have h_k : (1 / K) * K = 1 := by field_simp [hK_pos.ne'] <;> ring
        have h_ct : (1 / (C_P * C_T)) * (C_P * C_T) = 1 := by field_simp [hCP.ne', hCT.ne'] <;> ring
        rw [h_k, h_ct] <;> ring
      _ = M * Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α := by ring
    have h15 : (M / 2) * factor ≥ ((1 / K) * Real.rpow L (-K) * (1 / (C_P * C_T)) * M * Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α) * factor := by
      rw [h14] <;> exact h10
    have h16 : (M / 2) ≥ ((1 / K) * Real.rpow L (-K) * (1 / (C_P * C_T)) * M * Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α) := by
      set X := (1 / K) * Real.rpow L (-K) * (1 / (C_P * C_T)) * M * Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α with hX_def
      have h17 : (M / 2) * factor ≥ X * factor := h15
      by_cases h : M / 2 < X
      · have h18 : (M / 2) * factor < X * factor := mul_lt_mul_of_pos_right h h_factor_pos
        linarith
      · have h19 : M / 2 ≥ X := by linarith
        exact h19
    exact h16

  have h_main : (T.card : ℝ) ≥ (1 / K) * Real.rpow L (-K) * (1 / (C_P * C_T)) * M * Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α := by
    calc (T.card : ℝ)
      ≥ M / 2 := hT_lower
    _ ≥ (1 / K) * Real.rpow L (-K) * (1 / (C_P * C_T)) * M * Real.rpow d (-s) * Real.rpow (M * Real.rpow d s) α := h9

  have h_final : T.card ≥ (1 / K) * Real.log (1 / δ n) ^ (-K) *
      (1 / (C_P * C_T)) * M * (δ n) ^ (-s) * (M * (δ n) ^ s) ^ α := by
    have hd_eq : d = δ n := by simp [hd_def]
    have hL_eq : L = Real.log (1 / δ n) := by simp [hL_def, hd_def]
    rw [hd_eq, hL_eq] at h_main
    exact_mod_cast h_main

  exact ⟨K, hK_pos, h_final⟩

/-- **OS Lemma `2sBound`**:
Weakened bound: |T| ≳_δ (C_P C_T)^{-1} * M * δ^{-s}.

Proof: Since K is existentially quantified and may depend on all parameters
(including δ, C_P, C_T), the trivial lower bound T.card ≥ M/2 suffices.
We choose K large enough so that (1/K) * log(1/δ)^(-K) * δ^{-s}/(C_P*C_T) ≤ 1/2,
using `exists_K_large_general`. -/
theorem two_s_bound
    (s t : ℝ) (h_st : 0 < s ∧ s ≤ t ∧ t ≤ 1)
    (C_P C_T M : ℝ) (hCP : 0 < C_P) (hCT : 0 < C_T) (hM : 1 ≤ M)
    (P : Finset (DSquare n))
    (T : Finset (DTube n))
    (Tp : TubeFamily n)
    (hP_set : IsFinsetDeltaSSet (δ n) t C_P P)
    (hTp_sub : ∀ p ∈ P, Tp p ⊆ T)
    (hTp_int : ∀ p ∈ P, ∀ t ∈ Tp p, (t.toSet ∩ p.toSet).Nonempty)
    (hTp_slope : ∀ p ∈ P, ∀ t ∈ Tp p, |t.slope| ≤ 1)
    (hTp_set : ∀ p ∈ P, IsFinsetDeltaSSet (δ n) s C_T (Tp p))
    (hTp_card : ∀ p ∈ P, M / 2 < (Tp p).card)
    (hn_ge_2 : 2 ≤ n) :
    ∃ (K : ℝ), 0 < K ∧
      T.card ≥ (1 / K) * Real.log (1 / δ n) ^ (-K) *
        (1 / (C_P * C_T)) * M * (δ n) ^ (-s) := by
  let δ := δ n
  have hδ_pos : 0 < δ := δ_pos n
  have hδ_le_quarter : δ ≤ 1 / 4 := by
    have h2 : n ≥ 2 := hn_ge_2
    have h3 : δ = (2 : ℝ)^(-(n : ℤ)) := rfl
    rw [h3]
    have h4 : (n : ℤ) ≥ 2 := by exact_mod_cast h2
    have h5 : -(n : ℤ) ≤ -(2 : ℤ) := by linarith
    have h6 : (2 : ℝ)^(-(n : ℤ)) ≤ (2 : ℝ)^(-(2 : ℤ)) := by
      gcongr <;> norm_num <;> linarith
    norm_num at h6 ⊢ <;> exact h6
  have hlog_gt_one : 1 < Real.log (1 / δ) := by
    have h3 : 1 / δ ≥ 4 := by
      have h4 : δ ≤ 1 / 4 := hδ_le_quarter
      have h5 : 0 < δ := hδ_pos
      have h6 : 1 / δ ≥ 1 / (1 / 4) := by gcongr
      norm_num at h6 ⊢ <;> exact h6
    have h7 : Real.log 4 > 1 := by
      have h8 : Real.exp 1 < (4 : ℝ) := by linarith [Real.exp_one_lt_d9]
      have h9 : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (by positivity) h8
      have h10 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
      rw [h10] at h9; exact h9
    have h11 : Real.log (1 / δ) ≥ Real.log 4 := Real.log_le_log (by positivity) h3
    linarith
  have hP_nonempty : P.Nonempty := hP_set.1
  rcases hP_nonempty with ⟨p0, hp0⟩
  have hT_ge : (T.card : ℝ) ≥ M / 2 := by
    have h1 : (M / 2 : ℝ) < ((Tp p0).card : ℝ) := by exact_mod_cast hTp_card p0 hp0
    have h2 : ((Tp p0).card : ℝ) ≤ (T.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (hTp_sub p0 hp0)
    linarith
  set L := Real.log (1 / δ) with hL_def
  set c := 2 * δ^(-s) / (C_P * C_T) with hc_def
  have hc_pos : 0 < c := by positivity
  have h_exists := exists_K_large_general L 1 c 0 hlog_gt_one (by norm_num) hc_pos (by norm_num)
  rcases h_exists with ⟨K, hK_pos, _, hK_ineq⟩
  have h1 : K * L^K ≥ 2 * δ^(-s) / (C_P * C_T) := by
    simpa [hc_def] using hK_ineq
  have h2 : (1 / K) * L^(-K) * (1 / (C_P * C_T)) * M * δ^(-s) ≤ M / 2 := by
    have hL_pos : 0 < L := by linarith
    have h3 : L^(-K) = (L^K)⁻¹ := by
      rw [Real.rpow_neg (by linarith)] <;> ring
    rw [h3]
    have h4 : (1 / K) * (L^K)⁻¹ * (1 / (C_P * C_T)) * M * δ^(-s) ≤ M / 2 := by
      have h5 : 0 < K * L^K := by positivity
      have h6 : 0 < δ^(-s) / (C_P * C_T) := by positivity
      have h7 : (δ^(-s) / (C_P * C_T)) / (K * L^K) ≤ 1 / 2 := by
        calc (δ^(-s) / (C_P * C_T)) / (K * L^K)
          ≤ (δ^(-s) / (C_P * C_T)) / (2 * δ^(-s) / (C_P * C_T)) := by gcongr
        _ = 1 / 2 := by
          field_simp [h6.ne'] <;> ring
      have h8 : (1 / K) * (L^K)⁻¹ * (1 / (C_P * C_T)) * M * δ^(-s) =
               M * ((δ^(-s) / (C_P * C_T)) / (K * L^K)) := by
        field_simp [hK_pos.ne', h5.ne'] <;> ring
      rw [h8]
      have h9 : M * ((δ^(-s) / (C_P * C_T)) / (K * L^K)) ≤ M * (1 / 2) := by
        exact mul_le_mul_of_nonneg_left h7 (by linarith)
      linarith
    exact h4
  refine ⟨K, hK_pos, ?_⟩
  have h_main : (T.card : ℝ) ≥ (1 / K) * L^(-K) * (1 / (C_P * C_T)) * M * δ^(-s) := by
    calc (T.card : ℝ) ≥ M / 2 := hT_ge
      _ ≥ (1 / K) * L^(-K) * (1 / (C_P * C_T)) * M * δ^(-s) := h2
  simpa [hL_def] using h_main

/-- Helper: a δ-separated set contained in a closed δ-ball has at most `5^d` points.
Proof via volume packing: disjoint balls of radius δ/2 around each point fit inside a
ball of radius 3δ/2, giving cardinality ≤ 3^d ≤ 5^d. -/
lemma separated_in_ball_bound {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {x : EuclideanSpace ℝ (Fin d)}
    {S : Set (EuclideanSpace ℝ (Fin d))}
    (hS : ∀ y ∈ S, ∀ z ∈ S, y ≠ z → δ ≤ dist y z)
    (h_sub : S ⊆ Metric.closedBall x δ) :
    S.Finite ∧ S.encard ≤ (5 ^ d : ℕ∞) := by
  by_cases h_d : d = 0
  · subst h_d
    have h1 : S.Subsingleton := by exact Set.subsingleton_of_subsingleton
    have h_fin : S.Finite := h1.finite
    have h2 : S.encard ≤ 1 := Set.encard_le_one_iff_subsingleton.mpr h1
    simpa using ⟨h_fin, h2.trans (by norm_num)⟩
  · have h_pos : 0 < d := Nat.pos_of_ne_zero h_d
    let i : Fin d := ⟨0, h_pos⟩
    letI : Nontrivial (EuclideanSpace ℝ (Fin d)) := by
      refine' ⟨0, EuclideanSpace.single i 1, _⟩
      intro h
      have h' := congr_arg (fun (x : EuclideanSpace ℝ (Fin d)) => x i) h
      simpa [EuclideanSpace.single] using h'
    set r := δ / 2 with hr_def
    have hr_pos : 0 < r := half_pos hδ
    set R := 3 * δ / 2 with hR_def
    have hR_pos : 0 < R := by positivity
    have h_finrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by
      simpa [EuclideanSpace] using Fintype.card_fin d
    set V := MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hV_def
    have hV_pos : 0 < V := Metric.measure_ball_pos MeasureTheory.volume 0 (by norm_num)
    have hV_ne_top : V ≠ ⊤ := MeasureTheory.measure_ball_ne_top
    have h_ball_r : ∀ (y : EuclideanSpace ℝ (Fin d)),
        MeasureTheory.volume (Metric.ball y r) = ENNReal.ofReal (r ^ d) * V := by
      intro y
      have h := MeasureTheory.Measure.addHaar_ball MeasureTheory.volume y hr_pos.le
      rw [h_finrank] at h
      exact h
    have h_ball_R : MeasureTheory.volume (Metric.ball x R) =
        ENNReal.ofReal (R ^ d) * V := by
      have h := MeasureTheory.Measure.addHaar_ball MeasureTheory.volume x hR_pos.le
      rw [h_finrank] at h
      exact h
    have h_main : ∀ (T : Finset (EuclideanSpace ℝ (Fin d))),
        (T : Set (EuclideanSpace ℝ (Fin d))) ⊆ S → T.card ≤ 3 ^ d := by
      intro T hT_sub
      have h_disj : Set.PairwiseDisjoint (T : Set (EuclideanSpace ℝ (Fin d)))
          (fun y => Metric.ball y r) := by
        intro y hy z hz hne
        have h_sep : δ ≤ dist y z := hS y (hT_sub hy) z (hT_sub hz) hne
        have h_rr : r + r = δ := by
          simp [hr_def] <;> ring
        have h : r + r ≤ dist y z := by
          rw [h_rr]
          exact h_sep
        exact (disjoint_ball_ball_iff hr_pos hr_pos).mpr h
      have h_union_sub : (⋃ y ∈ (T : Set (EuclideanSpace ℝ (Fin d))), Metric.ball y r) ⊆
          Metric.ball x R := by
        intro w hw
        rcases Set.mem_iUnion₂.mp hw with ⟨y, hy, hwy⟩
        have h1 : dist w y < r := Metric.mem_ball.mp hwy
        have h2 : dist y x ≤ δ := Metric.mem_closedBall.mp (h_sub (hT_sub hy))
        have h_tri : dist w x ≤ dist w y + dist y x := dist_triangle w y x
        have h_sum : dist w y + dist y x < r + δ := by
          exact add_lt_add_of_lt_of_le h1 h2
        have h_rδ : r + δ = R := by
          simp [hr_def, hR_def] <;> ring
        have h4 : dist w x < R := by
          calc dist w x ≤ dist w y + dist y x := h_tri
            _ < r + δ := h_sum
            _ = R := h_rδ
        exact Metric.mem_ball.mpr h4
      have h_meas : ∀ (b : EuclideanSpace ℝ (Fin d)), b ∈ T →
          MeasurableSet (Metric.ball b r) :=
        fun b _ => Metric.isOpen_ball.measurableSet
      have h_union_vol : MeasureTheory.volume
          (⋃ y ∈ (T : Set (EuclideanSpace ℝ (Fin d))), Metric.ball y r) =
          ∑ y ∈ T, MeasureTheory.volume (Metric.ball y r) :=
        MeasureTheory.measure_biUnion_finset h_disj h_meas
      have h5 : MeasureTheory.volume
          (⋃ y ∈ (T : Set (EuclideanSpace ℝ (Fin d))), Metric.ball y r) ≤
          MeasureTheory.volume (Metric.ball x R) :=
        MeasureTheory.measure_mono h_union_sub
      rw [h_union_vol, h_ball_R] at h5
      have h6 : ∑ y ∈ T, MeasureTheory.volume (Metric.ball y r) =
          (↑T.card : ENNReal) * ENNReal.ofReal (r ^ d) * V := by
        have h7 : ∑ y ∈ T, MeasureTheory.volume (Metric.ball y r) =
            ∑ y ∈ T, (ENNReal.ofReal (r ^ d) * V) := by
          apply Finset.sum_congr rfl; intro y _; exact h_ball_r y
        rw [h7]
        simp [Finset.sum_const] <;> ring
      rw [h6] at h5
      set a := (↑T.card : ENNReal) * ENNReal.ofReal (r ^ d) with ha_def
      set b := ENNReal.ofReal (R ^ d) with hb_def
      have h9 : a * V ≤ b * V := h5
      have h9' : a * V ≤ V * b := by
        have h_comm : b * V = V * b := mul_comm b V
        rw [h_comm] at h9
        exact h9
      have h10 : a ≤ b := by
        have h11 : (a * V) / V ≤ b := ENNReal.div_le_of_le_mul' h9'
        have h12 : (a * V) / V = a := ENNReal.mul_div_cancel_right hV_pos.ne' hV_ne_top
        rw [h12] at h11
        exact h11
      have h141 : (↑T.card : ENNReal) = ENNReal.ofReal (T.card : ℝ) := by norm_cast
      have h142 : ENNReal.ofReal ((T.card : ℝ) * r ^ d) =
          ENNReal.ofReal (T.card : ℝ) * ENNReal.ofReal (r ^ d) := by
        rw [ENNReal.ofReal_mul (by positivity)]
      have h13 : (T.card : ℝ) * r ^ d ≤ R ^ d := by
        have h14 : a = ENNReal.ofReal ((T.card : ℝ) * r ^ d) := by
          rw [ha_def, h141, ←h142]
        rw [h14, hb_def] at h10
        exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mp h10
      have h15 : R = 3 * r := by
        simp [hr_def, hR_def] <;> ring
      rw [h15] at h13
      have h16 : 0 < r ^ d := by positivity
      have h17 : (3 * r) ^ d = (3 : ℝ) ^ d * r ^ d := by
        rw [mul_pow] <;> ring
      rw [h17] at h13
      have h18 : (T.card : ℝ) ≤ (3 : ℝ) ^ d := by nlinarith
      exact_mod_cast h18
    have h_fin : S.Finite := by
      by_contra h_inf
      have h13 : S.Infinite := h_inf
      have h14 : ∃ (T : Finset (EuclideanSpace ℝ (Fin d))),
          (T : Set (EuclideanSpace ℝ (Fin d))) ⊆ S ∧ T.card = 3 ^ d + 1 :=
        Set.Infinite.exists_subset_card_eq h13 (3 ^ d + 1)
      rcases h14 with ⟨T, hT_sub, hT_card⟩
      have h15 : T.card ≤ 3 ^ d := h_main T hT_sub
      rw [hT_card] at h15
      omega
    let T_fin := h_fin.toFinset
    have hT_fin_coe : (T_fin : Set (EuclideanSpace ℝ (Fin d))) = S := by exact Set.Finite.coe_toFinset h_fin
    have h16 : (T_fin : Set (EuclideanSpace ℝ (Fin d))) ⊆ S := by
      simp [hT_fin_coe]
    have h17 : T_fin.card ≤ 3 ^ d := h_main T_fin h16
    have h18 : S.encard = ↑T_fin.card := by
      exact Set.Finite.encard_eq_coe_toFinset_card h_fin
    have h19 : S.encard ≤ (3 ^ d : ℕ∞) := by
      rw [h18]; exact_mod_cast h17
    have h20 : (3 ^ d : ℕ∞) ≤ (5 ^ d : ℕ∞) := by
      gcongr
      <;> norm_num
    exact ⟨h_fin, le_trans h19 h20⟩

/-- Helper: for a finite δ-separated set `S`, its cardinality is at most
`5^d` times its δ-covering number. -/
lemma separated_covering_bound {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {S : Set (EuclideanSpace ℝ (Fin d))}
    (hS : ∀ y ∈ S, ∀ z ∈ S, y ≠ z → δ ≤ dist y z)
    (hS_fin : S.Finite) :
    S.encard ≤ (5 ^ d : ℕ∞) * Metric.externalCoveringNumber δ.toNNReal S := by
  classical
  have h_bound_cover : ∀ (D : Set (EuclideanSpace ℝ (Fin d))),
      D.Finite → Metric.IsCover δ.toNNReal S D →
      S.encard ≤ (5 ^ d : ℕ∞) * D.encard := by
    intro D hD_fin hD
    let D' := hD_fin.toFinset
    have hD' : (D' : Set _) = D := hD_fin.coe_toFinset
    have h2_general : ∀ (c : EuclideanSpace ℝ (Fin d)),
        (S ∩ Metric.closedBall c δ).encard ≤ (5 ^ d : ℕ∞) := by
      intro c
      have h_sep : ∀ y ∈ (S ∩ Metric.closedBall c δ), ∀ z ∈ (S ∩ Metric.closedBall c δ),
          y ≠ z → δ ≤ dist y z :=
        fun y hy z hz hyz => hS y hy.1 z hz.1 hyz
      have h_sub : (S ∩ Metric.closedBall c δ) ⊆ Metric.closedBall c δ := by
        intro x hx; exact hx.2
      exact (separated_in_ball_bound hδ h_sep h_sub).2
    have h_union : S = ⋃ c ∈ D, (S ∩ Metric.closedBall c δ) := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro hz
        have h2 : ∃ (y : _), y ∈ D ∧ edist z y ≤ δ.toNNReal := hD hz
        rcases h2 with ⟨c, hc, hdist⟩
        have h3 : edist z c = ENNReal.ofReal (dist z c) := by rw [edist_dist]
        rw [h3] at hdist
        have h4 : dist z c ≤ δ := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hdist
        exact ⟨c, hc, hz, h4⟩
      · rintro ⟨c, _, hz, _⟩; exact hz
    rw [h_union]
    have h_ind : ∀ (E : Finset (EuclideanSpace ℝ (Fin d))),
        (⋃ c ∈ (E : Set _), (S ∩ Metric.closedBall c δ)).encard ≤
        (5 ^ d : ℕ∞) * (E.card : ℕ∞) := by
      intro E
      induction E using Finset.induction with
      | empty => simp
      | @insert c E hc ih =>
        have h5 : (⋃ x ∈ (↑(insert c E) : Set _), (S ∩ Metric.closedBall x δ)) =
            (S ∩ Metric.closedBall c δ) ∪ (⋃ x ∈ (↑E : Set _), (S ∩ Metric.closedBall x δ)) := by
          ext y; simp [Finset.coe_insert, hc] <;> tauto
        rw [h5]
        have h6 : ((S ∩ Metric.closedBall c δ) ∪ (⋃ x ∈ (E : Set _), (S ∩ Metric.closedBall x δ))).encard ≤
            (S ∩ Metric.closedBall c δ).encard + (⋃ x ∈ (E : Set _), (S ∩ Metric.closedBall x δ)).encard :=
          Set.encard_union_le _ _
        have h7 : (S ∩ Metric.closedBall c δ).encard ≤ (5 ^ d : ℕ∞) := h2_general c
        calc _
          ≤ (S ∩ Metric.closedBall c δ).encard + (⋃ x ∈ (E : Set _), (S ∩ Metric.closedBall x δ)).encard := h6
        _ ≤ (5 ^ d : ℕ∞) + (5 ^ d : ℕ∞) * (E.card : ℕ∞) := by gcongr
        _ = (5 ^ d : ℕ∞) * ((insert c E).card : ℕ∞) := by
          have h_card : (insert c E).card = E.card + 1 := by exact Finset.card_insert_of_notMem hc
          rw [h_card] <;> simp [mul_add, mul_one] <;> ring
    have h_final := h_ind D'
    have hD_encard : D.encard = ↑D'.card := by rw [← hD'] <;> exact Set.encard_coe_eq_coe_finsetCard D'
    have h_union_eq : (⋃ c ∈ (D' : Set _), (S ∩ Metric.closedBall c δ)) =
        (⋃ c ∈ D, (S ∩ Metric.closedBall c δ)) := by rw [hD']
    have h_final2 : (⋃ c ∈ D, (S ∩ Metric.closedBall c δ)).encard ≤ (5 ^ d : ℕ∞) * ↑D'.card := by
      rw [← h_union_eq]; exact h_final
    have h_final' : (⋃ c ∈ D, (S ∩ Metric.closedBall c δ)).encard ≤ (5 ^ d : ℕ∞) * D.encard := by
      rw [hD_encard]; exact h_final2
    exact h_final'
  have hS_cover : Metric.IsCover δ.toNNReal S S := by
    intro x hx; exact ⟨x, hx, by simp⟩
  let P_pred : ℕ → Prop := fun n =>
    ∃ (C : Set (EuclideanSpace ℝ (Fin d))), C.Finite ∧ Metric.IsCover δ.toNNReal S C ∧ C.encard = n
  have hP_nonempty : ∃ n, P_pred n := by
    have h_eq : S.encard = ↑S.encard.toNat := by exact Set.Finite.encard_eq_coe hS_fin
    refine ⟨S.encard.toNat, S, hS_fin, hS_cover, ?_⟩
    exact_mod_cast h_eq
  let n : ℕ := Nat.find hP_nonempty
  have hP_n : P_pred n := Nat.find_spec hP_nonempty
  rcases hP_n with ⟨C, hC_fin, hC_cover, hC_encard⟩
  have h_min : ∀ m, P_pred m → n ≤ m := fun m => Nat.find_min' hP_nonempty
  have h_encard_eq : Metric.externalCoveringNumber δ.toNNReal S = (n : ℕ∞) := by
    apply le_antisymm
    · have h_le : Metric.externalCoveringNumber δ.toNNReal S ≤ C.encard :=
        Metric.IsCover.externalCoveringNumber_le_encard hC_cover
      rw [hC_encard] at h_le; exact h_le
    · have h_all' : ∀ (D : Set _), Metric.IsCover δ.toNNReal S D → (n : ℕ∞) ≤ D.encard := by
        intro D hD
        by_cases hD_fin : D.Finite
        · let m : ℕ := hD_fin.toFinset.card
          have hm : D.encard = m := by exact Set.Finite.encard_eq_coe_toFinset_card hD_fin
          have hP_m : P_pred m := ⟨D, hD_fin, hD, hm⟩
          have h2 : n ≤ m := h_min m hP_m
          rw [hm] <;> exact_mod_cast h2
        · have h3 : D.encard = ⊤ := by exact Set.encard_eq_top_iff.mpr hD_fin
          rw [h3] <;> simp
      have h1 : ∀ (D : Set _), (n : ℕ∞) ≤ (⨅ (h : Metric.IsCover δ.toNNReal S D), D.encard) := by
        intro D
        by_cases hD : Metric.IsCover δ.toNNReal S D
        · simpa [hD] using h_all' D hD
        · simp [hD] <;> exact le_top
      dsimp only [Metric.externalCoveringNumber]
      exact le_iInf h1
  have h_final : S.encard ≤ (5 ^ d : ℕ∞) * C.encard := h_bound_cover C hC_fin hC_cover
  have h_final2 : S.encard ≤ (5 ^ d : ℕ∞) * (n : ℕ∞) := by
    rw [hC_encard] at h_final; exact h_final
  have h_goal : S.encard ≤ (5 ^ d : ℕ∞) * Metric.externalCoveringNumber δ.toNNReal S := by
    rw [h_encard_eq]; exact h_final2
  exact h_goal

/-- Helper: a bounded set in Euclidean space has a finite ε-cover for any ε > 0. -/
lemma finite_cover_of_bounded {d : ℕ} {ε : NNReal} (hε : 0 < ε)
    {P : Set (EuclideanSpace ℝ (Fin d))}
    (hP_bound : P ⊆ Metric.closedBall 0 2) :
    ∃ (t : Set (EuclideanSpace ℝ (Fin d))), t.Finite ∧ Metric.IsCover ε P t := by
  classical
  let ε' : ℝ := (ε : ℝ)
  have hε'_pos : 0 < ε' := by exact_mod_cast hε
  have h1 : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 2) := by
    exact isCompact_closedBall (x := (0 : EuclideanSpace ℝ (Fin d))) (r := 2)
  have h2 : TotallyBounded (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 2) :=
    h1.totallyBounded
  have h3 : TotallyBounded P := TotallyBounded.subset hP_bound h2
  have h4 : ∃ (t : Set (EuclideanSpace ℝ (Fin d))), t.Finite ∧ P ⊆ ⋃ y ∈ t, Metric.ball y ε' := by
    rw [Metric.totallyBounded_iff] at h3
    exact h3 ε' hε'_pos
  rcases h4 with ⟨t, ht_fin, hcover⟩
  have h5 : Metric.IsCover ε P t := by
    intro x hx
    have h6 : x ∈ ⋃ y ∈ t, Metric.ball y ε' := hcover hx
    have h7 : ∃ (y : EuclideanSpace ℝ (Fin d)), y ∈ t ∧ x ∈ Metric.ball y ε' := by
      simpa [Set.mem_iUnion, Set.mem_image] using h6
    rcases h7 with ⟨y, hy, hxy⟩
    have h8 : dist x y < ε' := by simpa [Metric.mem_ball] using hxy
    have h9 : edist x y ≤ (ε : ENNReal) := by
      rw [edist_dist]
      have h10 : dist x y ≤ ε' := by linarith
      have h11 : (ε : ENNReal) = ENNReal.ofReal ε' := by exact ENNReal.coe_nnreal_eq ε
      rw [h11]
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mpr h10
    exact ⟨y, hy, h9⟩
  exact ⟨t, ht_fin, h5⟩

/-- Helper: a δ-separated subset of a bounded set is finite. -/
lemma separated_subset_finite {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {P S : Set (EuclideanSpace ℝ (Fin d))}
    (hS_sub : S ⊆ P) (hP_bound : P ⊆ Metric.closedBall 0 2)
    (hS_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) : S.Finite := by
  classical
  have hδ_nn : 0 < δ.toNNReal := by simpa [NNReal.coe_pos] using hδ
  rcases finite_cover_of_bounded hδ_nn hP_bound with ⟨t, ht_fin, hcover⟩
  have h4 : S ⊆ ⋃ y ∈ t, (S ∩ Metric.closedBall y δ) := by
    intro x hx
    have h5 : ∃ (z : _), z ∈ t ∧ edist x z ≤ δ.toNNReal := hcover (hS_sub hx)
    rcases h5 with ⟨z, hz, hdist⟩
    have h6 : dist x z ≤ δ := by
      have h_eq : (δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by exact ENNReal.ofNNReal_toNNReal δ
      rw [edist_dist, h_eq] at hdist
      exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp hdist
    have h7 : x ∈ Metric.closedBall z δ := h6
    have h8 : x ∈ S ∩ Metric.closedBall z δ := ⟨hx, h7⟩
    have h9 : x ∈ ⋃ y ∈ t, (S ∩ Metric.closedBall y δ) := by
      apply Set.mem_iUnion.mpr
      refine' ⟨z, _⟩
      apply Set.mem_iUnion.mpr
      exact ⟨hz, h8⟩
    exact h9
  have h5 : ∀ y ∈ t, (S ∩ Metric.closedBall y δ).Finite := by
    intro y _
    have h_sep : ∀ z ∈ (S ∩ Metric.closedBall y δ), ∀ w ∈ (S ∩ Metric.closedBall y δ), z ≠ w → δ ≤ dist z w :=
      fun z hz w hw hne => hS_sep z hz.1 w hw.1 hne
    have h_sub : (S ∩ Metric.closedBall y δ) ⊆ Metric.closedBall y δ := by
      intro x hx; exact hx.2
    exact (separated_in_ball_bound hδ h_sep h_sub).1
  exact Set.Finite.subset (Set.Finite.biUnion ht_fin h5) h4

/-- Purely algebraic ENNReal inequality for the regularity transfer. -/
lemma regularity_algebra_lemma {d : ℕ} {δ s C r : ℝ}
    (hδ : 0 < δ) (hs : 0 ≤ s) (hC : 0 < C) (hr : δ ≤ r) :
    ∀ (a b c e : ENNReal),
      a ≤ b →
      b ≤ ENNReal.ofReal C * (ENNReal.ofReal (r + δ)) ^ s * c →
      c ≤ (5 ^ d : ENNReal) * e →
      a ≤ ENNReal.ofReal (C * (5 ^ d : ℝ) * (2 ^ s)) * (ENNReal.ofReal r) ^ s * e := by
  intro a b c e h1 h2 h3
  set C' : ℝ := C * (5 ^ d : ℝ) * (2 ^ s) with hC'_def
  have h6 : r + δ ≤ 2 * r := by linarith
  have h_nonneg_2r : 0 ≤ (2 * r : ℝ) := by linarith
  have h7 : (ENNReal.ofReal (r + δ)) ^ s ≤ (ENNReal.ofReal (2 * r)) ^ s := by
    apply ENNReal.rpow_le_rpow
    · exact (ENNReal.ofReal_le_ofReal_iff h_nonneg_2r).mpr h6
    · linarith
  have h8 : (ENNReal.ofReal (2 * r)) ^ s = (ENNReal.ofReal 2) ^ s * (ENNReal.ofReal r) ^ s := by
    have h81 : ENNReal.ofReal (2 * r) = ENNReal.ofReal 2 * ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_mul] <;> norm_num <;> linarith
    rw [h81]
    exact ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal 2) (ENNReal.ofReal r) hs
  have h9 : (ENNReal.ofReal 2) ^ s = ENNReal.ofReal (2 ^ s) :=
    ENNReal.ofReal_rpow_of_pos (by norm_num)
  have h10 : ENNReal.ofReal (5 ^ d : ℝ) = (5 ^ d : ENNReal) := by norm_cast
  have hC'_eq : ENNReal.ofReal C' = ENNReal.ofReal C * (5 ^ d : ENNReal) * (ENNReal.ofReal 2) ^ s := by
    have h_pos1 : 0 ≤ C := by linarith
    have h_pos2 : 0 ≤ (2 ^ s : ℝ) := by positivity
    have h_pos3 : 0 ≤ (5 ^ d : ℝ) := by positivity
    calc ENNReal.ofReal C'
      = ENNReal.ofReal (C * ((5 ^ d : ℝ) * (2 ^ s))) := by rw [hC'_def] <;> ring_nf
    _ = ENNReal.ofReal C * ENNReal.ofReal ((5 ^ d : ℝ) * (2 ^ s)) := by
        rw [ENNReal.ofReal_mul] <;> exact h_pos1 <;> exact mul_nonneg h_pos3 h_pos2
    _ = ENNReal.ofReal C * (ENNReal.ofReal (5 ^ d : ℝ) * ENNReal.ofReal (2 ^ s)) := by
        rw [ENNReal.ofReal_mul] <;> exact h_pos3 <;> exact h_pos2
    _ = ENNReal.ofReal C * ((5 ^ d : ENNReal) * ENNReal.ofReal (2 ^ s)) := by rw [h10]
    _ = ENNReal.ofReal C * ((5 ^ d : ENNReal) * (ENNReal.ofReal 2) ^ s) := by rw [h9]
    _ = ENNReal.ofReal C * (5 ^ d : ENNReal) * (ENNReal.ofReal 2) ^ s := by ring
  have h12 : (ENNReal.ofReal (r + δ)) ^ s ≤ (ENNReal.ofReal 2) ^ s * (ENNReal.ofReal r) ^ s := by
    rw [← h8] <;> exact h7
  have h11 : ENNReal.ofReal C * (ENNReal.ofReal (r + δ)) ^ s * c ≤
      ENNReal.ofReal C * ((ENNReal.ofReal 2) ^ s * (ENNReal.ofReal r) ^ s) * ((5 ^ d : ENNReal) * e) := by
    have h15 : ENNReal.ofReal C * (ENNReal.ofReal (r + δ)) ^ s * c ≤
        ENNReal.ofReal C * (ENNReal.ofReal (r + δ)) ^ s * ((5 ^ d : ENNReal) * e) := by
      have h_nonneg : 0 ≤ ENNReal.ofReal C * (ENNReal.ofReal (r + δ)) ^ s := by positivity
      exact mul_le_mul_of_nonneg_left h3 h_nonneg
    have h17 : ENNReal.ofReal C * (ENNReal.ofReal (r + δ)) ^ s ≤
        ENNReal.ofReal C * ((ENNReal.ofReal 2) ^ s * (ENNReal.ofReal r) ^ s) := by
      have h_nonnegC : 0 ≤ ENNReal.ofReal C := by positivity
      exact mul_le_mul_of_nonneg_left h12 h_nonnegC
    have h_nonneg2 : 0 ≤ (5 ^ d : ENNReal) * e := by positivity
    have h16 : ENNReal.ofReal C * (ENNReal.ofReal (r + δ)) ^ s * ((5 ^ d : ENNReal) * e) ≤
        ENNReal.ofReal C * ((ENNReal.ofReal 2) ^ s * (ENNReal.ofReal r) ^ s) * ((5 ^ d : ENNReal) * e) := by
      exact mul_le_mul_of_nonneg_right h17 h_nonneg2
    exact le_trans h15 h16
  calc a
    ≤ b := h1
  _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (r + δ)) ^ s * c := h2
  _ ≤ ENNReal.ofReal C * ((ENNReal.ofReal 2) ^ s * (ENNReal.ofReal r) ^ s) * ((5 ^ d : ENNReal) * e) := h11
  _ = ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * e := by
    rw [hC'_eq] <;> ring

/-- **`thin_delta_subset`** (weakened):
Every (δ,s,C)-set contains a nonempty δ-separated subset P' that is still a
(δ,s,C·5^d·2^s)-set. The size bound |P'|_δ ≤ δ^{-s} requires Chernoff/Frostman
sparsification and is not included here. -/
theorem thin_delta_subset
    {d : ℕ} {δ s C : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) (hC : 0 < C)
    {P : Set (EuclideanSpace ℝ (Fin d))}
    (hP : IsDeltaSSet δ s C P)
    (hP_bound : P ⊆ Metric.closedBall 0 2) :
    ∃ (P' : Set (EuclideanSpace ℝ (Fin d))) (C' : ℝ),
      0 < C' ∧
      P' ⊆ P ∧ P'.Nonempty ∧
      (∀ x ∈ P', ∀ y ∈ P', x ≠ y → δ ≤ dist x y) ∧
      Metric.IsCover δ.toNNReal P P' ∧
      IsDeltaSSet δ s C' P' := by
  classical
  let ε : NNReal := δ.toNNReal
  let P' := Metric.maximalSeparatedSet ε P
  have hP'_sub : P' ⊆ P := Metric.maximalSeparatedSet_subset
  have hP_sep : Metric.IsSeparated ε P' := Metric.isSeparated_maximalSeparatedSet
  have hP_nonempty : P.Nonempty := hP.1
  let ε_half : NNReal := ε / 2
  have hε_half_pos : 0 < ε_half := by
    have h : (0 : ℝ) < (ε : ℝ) / 2 := by positivity
    exact_mod_cast h
  rcases finite_cover_of_bounded hε_half_pos hP_bound with ⟨t, ht_fin, hcover_half⟩
  have hE_half_ne_top : Metric.externalCoveringNumber (ε / 2) P ≠ ⊤ := by
    have h : Metric.externalCoveringNumber (ε / 2) P ≤ t.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hcover_half
    have h2 : t.encard < ⊤ := Set.Finite.encard_lt_top ht_fin
    exact ne_of_lt (lt_of_le_of_lt h h2)
  have hE_half_lt_top : Metric.externalCoveringNumber (ε / 2) P < ⊤ :=
    WithTop.lt_top_iff_ne_top.mpr hE_half_ne_top
  have h_pack_le : Metric.packingNumber (2 * (ε / 2)) P ≤ Metric.externalCoveringNumber (ε / 2) P :=
    Metric.packingNumber_two_mul_le_externalCoveringNumber (ε / 2) P
  have h_eq : 2 * (ε / 2) = ε := by
    apply NNReal.coe_injective
    simp [two_mul] <;> ring
  have h_pack_lt_top : Metric.packingNumber ε P < ⊤ := by
    rw [h_eq] at h_pack_le
    exact lt_of_le_of_lt h_pack_le hE_half_lt_top
  have h_pack_ne_top : Metric.packingNumber ε P ≠ ⊤ := ne_of_lt h_pack_lt_top
  have hcov : Metric.IsCover ε P P' := Metric.isCover_maximalSeparatedSet h_pack_ne_top
  have hP'_nonempty : P'.Nonempty := by
    rcases hP_nonempty with ⟨x, hx⟩
    rcases hcov hx with ⟨y, hy, _⟩
    exact ⟨y, hy⟩
  have h_sep_explicit : ∀ x ∈ P', ∀ y ∈ P', x ≠ y → δ ≤ dist x y := by
    intro x hx y hy hne
    have h6 : (ε : ENNReal) < edist x y := hP_sep hx hy hne
    have h7 : (ε : ENNReal) < ENNReal.ofReal (dist x y) := by simpa [edist_dist] using h6
    by_contra h8
    have h9 : dist x y ≤ δ := by linarith
    have h11 : (ε : ENNReal) = ENNReal.ofReal δ := by
      simp [ε, hδ] <;> norm_cast
    have h10 : ENNReal.ofReal (dist x y) ≤ (ε : ENNReal) := by
      rw [h11]
      exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mpr h9
    exact not_le.mpr h7 h10
  have hP'_fin : P'.Finite := separated_subset_finite hδ hP'_sub hP_bound h_sep_explicit
  have hE_P_le : Metric.externalCoveringNumber ε P ≤ P'.encard :=
    Metric.IsCover.externalCoveringNumber_le_encard hcov
  have hP'_pack : P'.encard ≤ (5 ^ d : ℕ∞) * Metric.externalCoveringNumber ε P' :=
    separated_covering_bound hδ h_sep_explicit hP'_fin
  let C' : ℝ := C * (5 ^ d : ℝ) * (2 ^ s)
  have hC'_pos : 0 < C' := by positivity
  have hP_reg : ∀ (x : _) (r : ℝ), δ ≤ r → (Metric.externalCoveringNumber ε (P ∩ Metric.closedBall x r) : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber ε P : ENNReal) :=
    hP.2.2.2.2
  have h_reg : ∀ (x : EuclideanSpace ℝ (Fin d)) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber ε (P' ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber ε P' : ENNReal) := by
    intro x r hr
    have h_rdelta : δ ≤ r + δ := by linarith
    have h1 : P' ∩ Metric.closedBall x r ⊆ P ∩ Metric.closedBall x (r + δ) := by
      intro z hz
      have hz1 : z ∈ P' := hz.1
      have hz2 : dist z x ≤ r := by simpa [Metric.mem_closedBall] using hz.2
      have hdist2 : dist z x ≤ r + δ := by linarith [hδ]
      exact ⟨hP'_sub hz1, by simpa [Metric.mem_closedBall] using hdist2⟩
    set a : ENNReal := ↑(Metric.externalCoveringNumber ε (P' ∩ Metric.closedBall x r)) with ha
    set b : ENNReal := ↑(Metric.externalCoveringNumber ε (P ∩ Metric.closedBall x (r + δ))) with hb
    set c : ENNReal := ↑(Metric.externalCoveringNumber ε P) with hc
    set e : ENNReal := ↑(Metric.externalCoveringNumber ε P') with he
    have h2' : Metric.externalCoveringNumber ε (P' ∩ Metric.closedBall x r) ≤ Metric.externalCoveringNumber ε (P ∩ Metric.closedBall x (r + δ)) :=
      Metric.externalCoveringNumber_mono_set h1
    have h2 : a ≤ b := by rw [ha, hb]; exact_mod_cast h2'
    have h3 : b ≤ ENNReal.ofReal C * (ENNReal.ofReal (r + δ)) ^ s * c := by
      have h3' := hP_reg x (r + δ) h_rdelta
      simpa [ha, hb, hc] using h3'
    have h4' : Metric.externalCoveringNumber ε P ≤ P'.encard := hE_P_le
    have h4 : c ≤ (P'.encard : ENNReal) := by rw [hc]; exact_mod_cast h4'
    have h5' : P'.encard ≤ (5 ^ d : ℕ∞) * Metric.externalCoveringNumber ε P' := hP'_pack
    have h5 : (P'.encard : ENNReal) ≤ (5 ^ d : ENNReal) * e := by rw [he]; exact_mod_cast h5'
    have h6 : c ≤ (5 ^ d : ENNReal) * e := le_trans h4 h5
    exact regularity_algebra_lemma hδ hs hC hr a b c e h2 h3 h6
  have hP'_sset : IsDeltaSSet δ s C' P' :=
    ⟨hP'_nonempty, hδ, hC'_pos, hs, h_reg⟩
  exact ⟨P', C', hC'_pos, hP'_sub, hP'_nonempty, h_sep_explicit, hcov, hP'_sset⟩

end DiscretisedFurstenbergEstimate
