/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.GridScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoreWindow
public import Kakeya.DimensionThree.MainLemma2.GridRounding

/-!
# Grid bookkeeping for the floor derivation

Three facts about the grid `ρ_k = δ^{k/N}` (`Tube.gridScale δ N k`) that the (F) derivation spends:

* `ceil_window_of_ratio` — the existing `hfloor` binder states the window `𝒲` in the source's real
  form `(ρ_b/ρ_a)^{1-ε} ≤ ρ_b/ρ_m ≤ (ρ_b/ρ_a)^ε` (l.4025–4028), while the twin's level clause
  `le_level_maxDensity` is read on the ceiling form `a + ⌈ε(b-a)⌉₊ ≤ m ≤ b - ⌈ε(b-a)⌉₊`
  (`StickyKakeya.dividingScalesKatzTao`'s `hgridAll`).  On the grid the two coincide; this is the
  bridge from the first to the second, which F4 needs to read W1 at a window level.
* `ratio_ge_of_ceil_window` — on the ceiling window, with the window's separation
  `ρ_b ≤ δ^ε ρ_a` (`IsKatzTaoDividingWindow.scale_sep`), `Θ_m = ρ_a/ρ_m ≥ δ^{-ε²}`: the refined
  source's "`log Θ_m / log(1/δ) ≥ ε²/2` once `δ_f` is decreased" (l.4117), here without the `/2`.
* `four_mul_gridScale_le_of_log` — the two-scale lemma's factor-`4` gap `4ρ_m ≤ ρ_p` for
  `p < m`, from the existing threshold `2·ssfGridLen δ ≤ log(1/δ)`
  (`exists_threshold_two_mul_ssfGridLen_le_log`), since `log 4 < 2`.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.ML2Core

/-! ## The window: real form ⇒ ceiling form -/

/-- On the grid, `(ρ_b/ρ_a)^{1-ε} ≤ ρ_b/ρ_m` and `ρ_b/ρ_m ≤ (ρ_b/ρ_a)^ε` (for `a < m < b`,
`0 < δ < 1`) put `m` in the ceiling window `a + ⌈ε(b-a)⌉₊ ≤ m ≤ b - ⌈ε(b-a)⌉₊`. -/
theorem ceil_window_of_ratio {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ < 1) {N a b m : ℕ}
    (hN : 0 < N) (ham : a < m) (hmb : m < b) {ε : ℝ}
    (hlo : ((Tube.gridScale δ N b : ℝ) / (Tube.gridScale δ N a : ℝ)) ^ (1 - ε)
      ≤ (Tube.gridScale δ N b : ℝ) / (Tube.gridScale δ N m : ℝ))
    (hhi : (Tube.gridScale δ N b : ℝ) / (Tube.gridScale δ N m : ℝ)
      ≤ ((Tube.gridScale δ N b : ℝ) / (Tube.gridScale δ N a : ℝ)) ^ ε) :
    a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ m ∧ m + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b := by
  have hδr : (0 : ℝ) < (δ : ℝ) := hδ0
  have hδr1 : (δ : ℝ) < 1 := hδ1
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- the ratios are powers of `δ`
  have hgrid : ∀ k : ℕ, (Tube.gridScale δ N k : ℝ) = (δ : ℝ) ^ ((k : ℝ) / (N : ℝ)) := by
    intro k
    simp [Tube.gridScale, NNReal.coe_rpow]
  have hratio : ∀ k l : ℕ, (Tube.gridScale δ N k : ℝ) / (Tube.gridScale δ N l : ℝ)
      = (δ : ℝ) ^ (((k : ℝ) - (l : ℝ)) / (N : ℝ)) := by
    intro k l
    rw [hgrid, hgrid, ← Real.rpow_sub hδr]
    congr 1
    ring
  rw [hratio, hratio, ← Real.rpow_mul hδr.le] at hlo
  rw [hratio, hratio, ← Real.rpow_mul hδr.le] at hhi
  -- `δ < 1` reverses the exponents
  have hlo' : ((b : ℝ) - (m : ℝ)) / (N : ℝ) ≤ ((b : ℝ) - (a : ℝ)) / (N : ℝ) * (1 - ε) :=
    (Real.rpow_le_rpow_left_iff_of_base_lt_one hδr hδr1).mp hlo
  have hhi' : ((b : ℝ) - (a : ℝ)) / (N : ℝ) * ε ≤ ((b : ℝ) - (m : ℝ)) / (N : ℝ) :=
    (Real.rpow_le_rpow_left_iff_of_base_lt_one hδr hδr1).mp hhi
  have hba : (0 : ℝ) < (b : ℝ) - (a : ℝ) := by
    have : (a : ℝ) < b := by exact_mod_cast ham.trans hmb
    linarith
  constructor
  · -- `m - a ≥ ε (b - a)`, so `⌈ε (b - a)⌉₊ ≤ m - a`
    have h1 : ε * ((b : ℝ) - (a : ℝ)) ≤ (m : ℝ) - (a : ℝ) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hNr] at hlo'
      nlinarith
    have h2 : ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ m - a := by
      rw [Nat.ceil_le]
      have : ((m - a : ℕ) : ℝ) = (m : ℝ) - (a : ℝ) := by
        rw [Nat.cast_sub ham.le]
      rw [this]; exact h1
    omega
  · -- `b - m ≥ ε (b - a)`, so `⌈ε (b - a)⌉₊ ≤ b - m`
    have h1 : ε * ((b : ℝ) - (a : ℝ)) ≤ (b : ℝ) - (m : ℝ) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hNr] at hhi'
      linarith
    have h2 : ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b - m := by
      rw [Nat.ceil_le]
      have : ((b - m : ℕ) : ℝ) = (b : ℝ) - (m : ℝ) := by
        rw [Nat.cast_sub hmb.le]
      rw [this]; exact h1
    omega

/-! ## `Θ_m ≥ δ^{-ε²}` on the ceiling window -/

/-- On the ceiling window, with the window's separation `ρ_b ≤ δ^ε ρ_a`, the ratio
`Θ_m = ρ_a/ρ_m` is at least `δ^{-ε²}`. -/
theorem ratio_ge_of_ceil_window {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ < 1) {N a b m : ℕ}
    (hN : 0 < N) {ε : ℝ} (hε : 0 ≤ ε)
    (hsep : (Tube.gridScale δ N b : ℝ) ≤ (δ : ℝ) ^ ε * (Tube.gridScale δ N a : ℝ))
    (hm : a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ m) :
    (δ : ℝ) ^ (-(ε ^ 2)) ≤ (Tube.gridScale δ N a : ℝ) / (Tube.gridScale δ N m : ℝ) := by
  have hδr : (0 : ℝ) < (δ : ℝ) := hδ0
  have hδr1 : (δ : ℝ) < 1 := hδ1
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hgrid : ∀ k : ℕ, (Tube.gridScale δ N k : ℝ) = (δ : ℝ) ^ ((k : ℝ) / (N : ℝ)) := by
    intro k
    simp [Tube.gridScale, NNReal.coe_rpow]
  have hratio : (Tube.gridScale δ N a : ℝ) / (Tube.gridScale δ N m : ℝ)
      = (δ : ℝ) ^ (((a : ℝ) - (m : ℝ)) / (N : ℝ)) := by
    rw [hgrid, hgrid, ← Real.rpow_sub hδr]
    congr 1
    ring
  -- the separation says `(b - a)/N ≥ ε`
  have hsep' : ε ≤ ((b : ℝ) - (a : ℝ)) / (N : ℝ) := by
    rw [hgrid, hgrid, ← Real.rpow_add hδr] at hsep
    have := (Real.rpow_le_rpow_left_iff_of_base_lt_one hδr hδr1).mp hsep
    have hdiv : ((b : ℝ) - (a : ℝ)) / (N : ℝ) = (b : ℝ) / (N : ℝ) - (a : ℝ) / (N : ℝ) := by ring
    linarith
  -- the ceiling window says `m - a ≥ ε (b - a)`
  have hma : ε * ((b : ℝ) - (a : ℝ)) ≤ (m : ℝ) - (a : ℝ) := by
    have h1 : ε * ((b : ℝ) - (a : ℝ)) ≤ (⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    push_cast at h2
    linarith
  rw [hratio]
  refine Real.rpow_le_rpow_of_exponent_ge hδr hδr1.le ?_
  -- `(a - m)/N ≤ -ε²`, i.e. `(m - a)/N ≥ ε · (b - a)/N ≥ ε · ε`
  have hba : (0 : ℝ) ≤ (b : ℝ) - (a : ℝ) := by
    by_contra hneg
    have hneg' : (b : ℝ) - (a : ℝ) < 0 := lt_of_not_ge hneg
    have : ((b : ℝ) - (a : ℝ)) / (N : ℝ) < 0 := div_neg_of_neg_of_pos hneg' hNr
    linarith
  have h3 : ε * ε ≤ ((m : ℝ) - (a : ℝ)) / (N : ℝ) := by
    calc ε * ε ≤ ε * (((b : ℝ) - (a : ℝ)) / (N : ℝ)) := by gcongr
      _ = (ε * ((b : ℝ) - (a : ℝ))) / (N : ℝ) := by ring
      _ ≤ ((m : ℝ) - (a : ℝ)) / (N : ℝ) := by gcongr
  have : ((a : ℝ) - (m : ℝ)) / (N : ℝ) = -(((m : ℝ) - (a : ℝ)) / (N : ℝ)) := by ring
  rw [this]
  nlinarith

/-! ## The factor-`4` gap from the existing grid threshold -/

/-- **H4's gap**: once `2N ≤ log(1/δ)`, consecutive grid scales are `4`-separated,
`4 ρ_{k+1} ≤ ρ_k`, because `log 4 < 2`. -/
theorem four_mul_gridScale_succ_le_of_log {δ : NNReal} (hδ0 : 0 < δ) {N : ℕ} (hN : 0 < N)
    (hlog : 2 * (N : ℝ) ≤ Real.log (1 / (δ : ℝ))) (k : ℕ) :
    4 * Tube.gridScale δ N (k + 1) ≤ Tube.gridScale δ N k := by
  have hδr : (0 : ℝ) < (δ : ℝ) := hδ0
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [← NNReal.coe_le_coe]
  push_cast
  simp only [Tube.gridScale, NNReal.coe_rpow]
  -- `δ^{(k+1)/N} = δ^{k/N} · δ^{1/N}` and `4 δ^{1/N} ≤ 1`
  have hsplit : (δ : ℝ) ^ (((k + 1 : ℕ) : ℝ) / (N : ℝ))
      = (δ : ℝ) ^ ((k : ℝ) / (N : ℝ)) * (δ : ℝ) ^ (1 / (N : ℝ)) := by
    rw [← Real.rpow_add hδr]
    congr 1
    push_cast
    ring
  have hlog4 : Real.log 4 < 2 := by
    have h : (4 : ℝ) < Real.exp 2 := by
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      rw [h2]; nlinarith
    calc Real.log 4 < Real.log (Real.exp 2) := Real.log_lt_log (by norm_num) h
      _ = 2 := Real.log_exp 2
  have hquarter : (δ : ℝ) ^ (1 / (N : ℝ)) ≤ 1 / 4 := by
    have hlogδ : Real.log (δ : ℝ) = -Real.log (1 / (δ : ℝ)) := by
      rw [one_div, Real.log_inv, neg_neg]
    have hlogpow : Real.log ((δ : ℝ) ^ (1 / (N : ℝ))) = -(Real.log (1 / (δ : ℝ)) / (N : ℝ)) := by
      rw [Real.log_rpow hδr, hlogδ]; ring
    have hlog14 : Real.log (1 / 4 : ℝ) = -Real.log 4 := by rw [one_div, Real.log_inv]
    have h1 : Real.log ((δ : ℝ) ^ (1 / (N : ℝ))) ≤ Real.log (1 / 4 : ℝ) := by
      rw [hlogpow, hlog14]
      have : 2 ≤ Real.log (1 / (δ : ℝ)) / (N : ℝ) := by rw [le_div_iff₀ hNr]; linarith
      linarith
    exact (Real.log_le_log_iff (Real.rpow_pos_of_pos hδr _) (by norm_num)).mp h1
  rw [hsplit]
  have hk : (0 : ℝ) ≤ (δ : ℝ) ^ ((k : ℝ) / (N : ℝ)) := Real.rpow_nonneg hδr.le _
  calc (4 : ℝ) * ((δ : ℝ) ^ ((k : ℝ) / (N : ℝ)) * (δ : ℝ) ^ (1 / (N : ℝ)))
      ≤ 4 * ((δ : ℝ) ^ ((k : ℝ) / (N : ℝ)) * (1 / 4)) := by gcongr
    _ = (δ : ℝ) ^ ((k : ℝ) / (N : ℝ)) := by ring

/-- The gap across any two levels `p < m` of the grid, from the consecutive gap and antitonicity. -/
theorem four_mul_gridScale_le_of_log {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ}
    (hN : 0 < N) (hlog : 2 * (N : ℝ) ≤ Real.log (1 / (δ : ℝ))) {p m : ℕ} (hpm : p < m) :
    4 * Tube.gridScale δ N m ≤ Tube.gridScale δ N p := by
  calc 4 * Tube.gridScale δ N m ≤ 4 * Tube.gridScale δ N (p + 1) := by
        gcongr
        exact Tube.gridScale_antitone hδ0 hδ1 N hpm
    _ ≤ Tube.gridScale δ N p := four_mul_gridScale_succ_le_of_log hδ0 hN hlog p

/-! ### X2 — the grid's own bounded jump -/

/-- **X2 — the grid's own bounded jump.**  Consecutive grid scales differ by the single factor
`δ ^ (1 / Tube.ssfGridLen δ)`, and `Tube.ssfGridLen δ = ⌈log log (1/δ)⌉₊` beats every fixed
reciprocal, so for `η' > 0` fixed *before* `δ` one grid step costs at most `δ ^ η'` below an
explicit threshold.  Constant exactly `δ ^ η'`, no absolute factor.

This renders the refined source's hypothesis **l.4013, `M ≥ max{512 N / η₁, 8 / η'}`** on its tower
`ρ_k = δ^{k/M}/40` (l.4023): `ρ_{k+1}/ρ_k = δ^{1/M}` and `M ≥ 8/η'` give `ρ_{k+1} ≥ δ^{η'/8} ρ_k`,
and that clause has no other job in the lemma — it keeps one step of the tower inside the `δ^{η'}`
budget of the count floor.  **The asymmetry (C-X2):** the source's `M` is *fixed* and the bound is a
*hypothesis*, while the tree's `N = Tube.ssfGridLen δ` *grows with `δ`* and the bound is a
*threshold* — favourable here, and the same `M`-vs-`ssfGridLen δ` divergence that -R3 priced as fatal and  settled for the loss ledger.  Both halves are existing:
`Tube.gridScale_div_gridScale` and `Kakeya.StickyKakeya.exists_ssfGridLen_rpow_threshold`. -/
theorem exists_threshold_gridScale_step {η' : ℝ} (hη' : 0 < η') :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : NNReal, 0 < δ → δ ≤ δ₀ → ∀ k : ℕ,
        (δ : ℝ) ^ η' * (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ)
          ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) (k + 1) : ℝ) := by
  obtain ⟨δ₀, hδ₀, hδ₀1, hthr⟩ := StickyKakeya.exists_ssfGridLen_rpow_threshold 1 η' hη'
  refine ⟨min δ₀ (1 / 2), lt_min hδ₀ (by norm_num), (min_le_left _ _).trans hδ₀1, ?_⟩
  intro δ hδ0 hδle k
  have hδr : (0 : ℝ) < (δ : ℝ) := hδ0
  have hδr1 : (δ : ℝ) < 1 := by
    have : (δ : ℝ) ≤ 1 / 2 := by exact_mod_cast hδle.trans (min_le_right _ _)
    linarith
  have hδη : (δ : ℝ) ^ η' ≤ 1 := Real.rpow_le_one hδr.le hδr1.le hη'.le
  rcases Nat.eq_zero_or_pos (Tube.ssfGridLen δ) with hN0 | hNpos
  · -- a degenerate grid: every scale is `1`
    simp only [Tube.gridScale, hN0, Nat.cast_zero, div_zero, NNReal.rpow_zero,
      NNReal.coe_one, mul_one]
    exact hδη
  · have hNr : (0 : ℝ) < (Tube.ssfGridLen δ : ℝ) := by exact_mod_cast hNpos
    -- the threshold: `1/N ≤ η'`
    have h := hthr δ hδ0 (hδle.trans (min_le_left _ _))
    have h' : (δ : ℝ) ^ (-1 / (Tube.ssfGridLen δ : ℝ)) ≤ (δ : ℝ) ^ (-η') := by
      have := NNReal.coe_le_coe.mpr h
      rwa [NNReal.coe_rpow, NNReal.coe_rpow] at this
    have h1N : 1 / (Tube.ssfGridLen δ : ℝ) ≤ η' := by
      have := (Real.rpow_le_rpow_left_iff_of_base_lt_one hδr hδr1).mp h'
      have e : -1 / (Tube.ssfGridLen δ : ℝ) = -(1 / (Tube.ssfGridLen δ : ℝ)) := by ring
      rw [e] at this
      linarith
    -- the ratio of consecutive scales is `δ^{1/N}`
    have hρk : (0 : ℝ) < (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ) := by
      exact_mod_cast Tube.gridScale_pos hδ0 _ _
    have hratio : (Tube.gridScale δ (Tube.ssfGridLen δ) (k + 1) : ℝ)
        / (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ)
        = (δ : ℝ) ^ (1 / (Tube.ssfGridLen δ : ℝ)) := by
      have := Tube.gridScale_div_gridScale hδ0 (Tube.ssfGridLen δ) (k + 1) k
      have h2 := congrArg (fun x : NNReal => (x : ℝ)) this
      simp only [NNReal.coe_div, NNReal.coe_rpow] at h2
      rw [h2]
      congr 1
      push_cast
      ring
    have hstep : (δ : ℝ) ^ η' ≤ (δ : ℝ) ^ (1 / (Tube.ssfGridLen δ : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hδr hδr1.le h1N
    calc (δ : ℝ) ^ η' * (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ)
        ≤ (δ : ℝ) ^ (1 / (Tube.ssfGridLen δ : ℝ)) * (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ) :=
          mul_le_mul_of_nonneg_right hstep hρk.le
      _ = (Tube.gridScale δ (Tube.ssfGridLen δ) (k + 1) : ℝ) := by
          rw [← hratio, div_mul_cancel₀ _ hρk.ne']

end Kakeya.ML2Core

end
