/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.FibrePacking
public import Kakeya.Frostman
public import Kakeya.GridScale
public import Kakeya.MultiScaleFac.Loss
public import Kakeya.MultiScaleFac.RefineStep
public import Kakeya.MultiScaleFac.Stopping
public import Kakeya.Sticky
public import Kakeya.Tube.Basic
public import Kakeya.Tube.CardEssentiallyDistinct
public import Kakeya.Uniform
public import Kakeya.MultiScaleFac.Bridge

/-!
# The gaps between the stopping time and the amended dichotomy, half (A)

The grid-side hypotheses at the grid length `ssfGridLen δ`, and the gap lemmas that turn what the
stopping time hands out into the clauses the amended half-(A) dichotomy displays.  Everything above
this file is reusable geometry; everything in it is dichotomy-specific plumbing.

Sliced out of the former `DividingScalesA`.
-/

@[expose] public section

open MeasureTheory Real Metric
open scoped Topology

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### The grid-side hypotheses at the grid length `ssfGridLen δ`

The split stopping-time layer constrains its *grid* length only from below — `16 ≤ N_grid`,
`1 ≤ ε ^ 2 * N_grid`, `N_step ≤ N_grid` — together with the separation `δ ≤ 16 ^ (-N_grid)` that
`Tube.exists_uniformTubeSet_subfamily` also demands.  Since `ssfGridLen δ` diverges
as `δ → 0`, all four hold at `N_grid := ssfGridLen δ` below a threshold depending only on the step
bound and on `ε`.  That is the entire arithmetic content of moving the hierarchy onto GWZ's own
grid, and it is what decouples the grid length from the step bound.

The divergence of `⌈log log 1/δ⌉` is also recorded, in a real-valued form, as
`Kakeya.StickyKakeya.exists_threshold_le_ssfGridLen` in `Kakeya/StickyKakeya/CrossScale.lean`; that
module is not imported here. -/

section SsfGridHypotheses

/-- **Every grid-side hypothesis of the split stopping-time layer, at `N_grid := ssfGridLen δ`.**
A threshold `δ₀` below which `16 ≤ N_grid`, `1 ≤ ε ^ 2 * N_grid`, `N ≤ N_grid` and the grid
separation `δ ≤ 16 ^ (-N_grid)` all hold.  It depends only on the step bound `N` and on `ε`, never
on the family. -/
theorem exists_threshold_ssfGridLen_hypotheses (N : ℕ) {ε : ℝ} (hεpos : 0 < ε) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
        16 ≤ ssfGridLen δ ∧ N ≤ ssfGridLen δ ∧ 1 ≤ ε ^ 2 * (ssfGridLen δ : ℝ) ∧
          δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ)) := by
  let K : ℕ := max 16 (max N ⌈(1 : ℝ) / ε ^ 2⌉₊)
  have hK16 : 16 ≤ K := by
    dsimp [K]
    exact le_max_left _ _
  have hKN : N ≤ K := by
    dsimp [K]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hKceil : ⌈(1 : ℝ) / ε ^ 2⌉₊ ≤ K := by
    dsimp [K]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hdiv : ∃ δ₁ : NNReal, 0 < δ₁ ∧ δ₁ ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₁ → K ≤ ssfGridLen δ := by
    refine ⟨Real.toNNReal (Real.exp (-(Real.exp (K : ℝ)))), ?_, ?_, ?_⟩
    · exact Real.toNNReal_pos.mpr (Real.exp_pos _)
    · have h : (Real.toNNReal (Real.exp (-(Real.exp (K : ℝ)))) : ℝ) ≤ 1 := by
        rw [Real.coe_toNNReal (Real.exp (-(Real.exp (K : ℝ)))) (Real.exp_nonneg _)]
        exact (Real.exp_le_one_iff).mpr (neg_nonpos.mpr (Real.exp_nonneg (K : ℝ)))
      exact NNReal.coe_le_coe.mp h
    · intro δ hδpos hδle
      set L : ℝ := Real.log (1 / (δ : ℝ)) with hL_def
      set M : ℕ := ssfGridLen δ with hM_def
      have hδRpos : 0 < (δ : ℝ) := by exact_mod_cast hδpos
      have hδleexp : (δ : ℝ) ≤ Real.exp (-(Real.exp (K : ℝ))) := by
        have h1 : (δ : ℝ) ≤ ((Real.toNNReal (Real.exp (-(Real.exp (K : ℝ)))) : NNReal) : ℝ) :=
          NNReal.coe_le_coe.mp hδle
        have hδ₀val : ((Real.toNNReal (Real.exp (-(Real.exp (K : ℝ)))) : NNReal) : ℝ) =
            Real.exp (-(Real.exp (K : ℝ))) := by
          exact Real.coe_toNNReal (Real.exp (-(Real.exp (K : ℝ)))) (Real.exp_nonneg _)
        rwa [hδ₀val] at h1
      have hδle1 : (δ : ℝ) ≤ 1 := by
        exact le_trans hδleexp (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_nonneg (K : ℝ))))
      have hlogδ : Real.log (δ : ℝ) ≤ -(Real.exp (K : ℝ)) := by
        have h := Real.log_le_log hδRpos hδleexp
        rwa [Real.log_exp] at h
      have hL : L = -Real.log (δ : ℝ) := by
        rw [hL_def, one_div]
        exact Real.log_inv (δ : ℝ)
      have hLge : Real.exp (K : ℝ) ≤ L := by
        rw [hL]
        linarith
      have hLpos : 0 < L := by
        have h := Real.exp_pos (K : ℝ)
        linarith
      have hK_le_logL : (K : ℝ) ≤ Real.log L := by
        have h := Real.log_le_log (Real.exp_pos (K : ℝ)) hLge
        rwa [Real.log_exp] at h
      have hMge : (K : ℝ) ≤ (M : ℝ) := by
        rw [hM_def, ssfGridLen, ← hL_def]
        exact le_trans hK_le_logL (Nat.le_ceil (Real.log L))
      exact_mod_cast hMge
  obtain ⟨δ₁, hδ₁pos, hδ₁le1, h₁⟩ := hdiv
  obtain ⟨δ₂, hδ₂pos, hδ₂le1, h₂⟩ :=
    exists_threshold_polylog_pow_ssfGridLen_le (1 : ℝ) (by norm_num) 0 1 (1 : ℝ) (by norm_num)
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, (min_le_left _ _).trans hδ₁le1, ?_⟩
  intro δ hδpos hδle
  have hδle₁ : δ ≤ δ₁ := hδle.trans (min_le_left _ _)
  have hδle₂ : δ ≤ δ₂ := hδle.trans (min_le_right _ _)
  have hdivδ : K ≤ ssfGridLen δ := h₁ hδpos hδle₁
  have h16 : 16 ≤ ssfGridLen δ := le_trans hK16 hdivδ
  have hN : N ≤ ssfGridLen δ := le_trans hKN hdivδ
  have hsep : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ)) := (h₂ hδpos hδle₂).2.1
  have h1ε : 1 ≤ ε ^ 2 * (ssfGridLen δ : ℝ) := by
    have hle : (1 : ℝ) / ε ^ 2 ≤ (ssfGridLen δ : ℝ) :=
      le_trans (Nat.le_ceil ((1 : ℝ) / ε ^ 2))
        (by exact_mod_cast (le_trans hKceil hdivδ))
    have hε2pos : 0 < ε ^ 2 := pow_pos hεpos 2
    calc
      1 = ε ^ 2 * ((1 : ℝ) / ε ^ 2) := by
        rw [mul_comm, div_mul_cancel₀ (1 : ℝ) (ne_of_gt hε2pos)]
      _ ≤ ε ^ 2 * (ssfGridLen δ : ℝ) := mul_le_mul_of_nonneg_left hle (le_of_lt hε2pos)
  exact ⟨h16, hN, h1ε, hsep⟩

/-- **A long block spans a scale ratio of at least `δ ^ (-ε)`.**  This is the separation clause
`σ_b ≤ δ ^ ε · σ_a` of alternative (ii), read on an arbitrary grid: a long block has
`b - a > ⌈ε · N⌉ ≥ ε · N`, so the ratio of its two grid scales is `δ ^ ((b - a) / N) ≤ δ ^ ε`. -/
theorem gridScale_le_rpow_mul_gridScale_of_isLongBlock {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {N : ℕ} (hN : 0 < N) {ε : ℝ} {a b : ℕ} (hlong : IsLongBlock N ε a b) :
    (gridScale δ N b : ℝ) ≤ (δ : ℝ) ^ ε * (gridScale δ N a : ℝ) := by
  have hδposR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδ1R : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hs : ∀ k : ℕ, (gridScale δ N k : ℝ) = (δ : ℝ) ^ ((k : ℝ) / (N : ℝ)) := by
    intro k
    rw [gridScale]
    exact NNReal.coe_rpow δ ((k : ℝ) / (N : ℝ))
  have hlong' : ⌈ε * (N : ℝ)⌉₊ + a < b := by
    simpa [IsLongBlock] using hlong
  have hceil : ε * (N : ℝ) ≤ ((⌈ε * (N : ℝ)⌉₊ : ℕ) : ℝ) := by
    exact Nat.le_ceil (ε * (N : ℝ))
  have hnat : ((⌈ε * (N : ℝ)⌉₊ : ℕ) : ℝ) + (a : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast (le_of_lt hlong')
  have hsum : ε * (N : ℝ) + (a : ℝ) ≤ (b : ℝ) := by
    linarith
  have hexp : ε + (a : ℝ) / (N : ℝ) ≤ (b : ℝ) / (N : ℝ) := by
    rw [le_div_iff₀ hNposR]
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hNposR)]
    linarith
  calc
    (gridScale δ N b : ℝ) = (δ : ℝ) ^ ((b : ℝ) / (N : ℝ)) := hs b
    _ ≤ (δ : ℝ) ^ (ε + (a : ℝ) / (N : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge hδposR hδ1R hexp
    _ = (δ : ℝ) ^ ε * (δ : ℝ) ^ ((a : ℝ) / (N : ℝ)) :=
        Real.rpow_add hδposR ε ((a : ℝ) / (N : ℝ))
    _ = (δ : ℝ) ^ ε * (gridScale δ N a : ℝ) := by
        rw [hs a]

end SsfGridHypotheses

/-! ### The four remaining gaps of the amended dichotomy

The proof of `Kakeya.MultiScaleFac.dividingScalesFrostman` below runs the hoisted stopping time
`Kakeya.MultiScaleFac.exists_maximal_cuts_state_instance_hoisted_blocks_quad` at the grid length
`ssfGridLen δ`,
converts its two losses into `Kakeya.MultiScaleFac.totalLoss`, builds the returned bundle out of the
returned `Kakeya.MultiScaleFac.GridUniform`, and splits on whether some adjacent pair of the cut set
is long.  What it does not do is the four analytic steps below, each of which is isolated here as a
named lemma whose hypotheses are, verbatim, the data the stopping time hands out.

Each of the four returns its own constant `B` and polylogarithmic degree `K`; the dichotomy raises
all four to a common pair by `ssf_loss_raise`, which is why none of them may be stated with the
final constant already substituted.

*Alternative (i) uses the explicit-power form.*  The consumer
`Kakeya.MultiScaleFac.isFrostmanAtEveryScale_of_cuts_blockPow_uniform` charges the terminal block
constant as a bounded power.  This is necessary because the hoisted stopping time bounds that
constant by
`(C₁^{M+1} (1 - \log δ)^{K₁(M+1)})^L` with `M = ssfGridLen δ` and `L ≤ N + 1`.  The latter is
`\exp(Θ((\log\log 1/δ)^2))`, which exceeds every fixed power of `1 - \log δ` as `δ → 0`.
Charging the block constant explicitly as `C_b^p` gives a conclusion quadratic in `M`, hence a
`gridLoss`, and is wide enough to carry. -/

section SsfGaps

/-- The combined loss dominates its grid half, the gap half being at least `1`.  The grid half is
real-valued and the combined loss is not, so the comparison is stated after the coercion. -/
private theorem gridLoss_le_totalLoss (A : NNReal) (hA : 1 ≤ A) (K c : ℕ) {δ : NNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ENNReal.ofReal (gridLoss A K δ) ≤ totalLoss A K c δ := by
  have hg : (1 : ℝ) ≤ gridLoss A K δ := one_le_gridLoss A hA K hδ1
  have hs : (1 : ℝ) ≤ scaleGapLoss c δ := one_le_scaleGapLoss c hδ hδ1
  have hreal : gridLoss A K δ ≤ gridLoss A K δ * scaleGapLoss c δ :=
    le_mul_of_one_le_right (le_trans zero_le_one hg) hs
  rw [totalLoss_eq_ofReal]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **The exponent one step past a terminal index is at most `ε`.**  The chain `η_k ≤ ε η_{k+1}`
with `0 ≤ η_0` makes `η` increasing up to `N`, so `η_{m+1} ≤ η_N ≤ ε` for `m < N`.  This is the
last hypothesis of `Kakeya.MultiScaleFac.alternative_two_of_terminal_block_sharp`. -/
theorem eta_succ_le_eps {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : ε = 1 / Real.sqrt (N : ℝ))
    (η : ℕ → ℝ) (hη0 : 0 ≤ η 0) (hgap : ∀ k < N, η k ≤ ε * η (k + 1)) (hηN : η N ≤ ε)
    {m : ℕ} (hm : m < N) :
    η (m + 1) ≤ ε := by
  have hnonneg : ∀ k ≤ N, 0 ≤ η k := eta_nonneg_of_gap N hN hε η hη0 hgap
  have hε1 : ε ≤ 1 := by
    rw [hε]
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have hsqrt : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
      refine (Real.le_sqrt (by norm_num) (by positivity : 0 ≤ (N : ℝ))).2 ?_
      exact_mod_cast (show 1 * 1 ≤ N by nlinarith)
    rw [div_le_one]
    · exact hsqrt
    · exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hstep : ∀ k < N, η k ≤ η (k + 1) := by
    intro k hk
    have hk' : 0 ≤ η (k + 1) := hnonneg (k + 1) (Nat.succ_le_iff.mpr hk)
    calc
      η k ≤ ε * η (k + 1) := hgap k hk
      _ ≤ η (k + 1) := mul_le_of_le_one_left hk' hε1
  have hadd : ∀ d : ℕ, (m + 1) + d ≤ N → η (m + 1) ≤ η ((m + 1) + d) := by
    intro d
    induction d with
    | zero => intro _; exact le_rfl
    | succ d ih =>
      intro hdN
      have hd_lt : (m + 1) + d < N := by omega
      exact le_trans (ih (by omega)) (hstep ((m + 1) + d) hd_lt)
  have hmm : (m + 1) + (N - (m + 1)) ≤ N := by omega
  have hto : η (m + 1) ≤ η ((m + 1) + (N - (m + 1))) := hadd (N - (m + 1)) hmm
  have heq : (m + 1) + (N - (m + 1)) = N := by omega
  exact le_trans (by simpa [heq] using hto) hηN

/-- A common upper bound for the constants returned by the four gap lemmas and by the hierarchy. -/
theorem exists_common_const (B₀ B₁ B₂ B₃ Cq : NNReal) (hCq : 1 ≤ Cq) :
    ∃ D : NNReal, 1 ≤ D ∧ B₀ ≤ D ∧ B₁ ≤ D ∧ B₂ ≤ D ∧ B₃ ≤ D ∧ Cq ≤ D := by
  refine ⟨max B₀ (max B₁ (max B₂ (max B₃ Cq))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans hCq (le_trans (le_max_right B₃ Cq)
      (le_trans (le_max_right B₂ (max B₃ Cq))
        (le_trans (le_max_right B₁ (max B₂ (max B₃ Cq)))
          (le_max_right B₀ (max B₁ (max B₂ (max B₃ Cq)))))))
  · exact le_max_left B₀ (max B₁ (max B₂ (max B₃ Cq)))
  · exact le_trans (le_max_left B₁ (max B₂ (max B₃ Cq)))
      (le_max_right B₀ (max B₁ (max B₂ (max B₃ Cq))))
  · exact le_trans (le_trans (le_max_left B₂ (max B₃ Cq)) (le_max_right B₁ (max B₂ (max B₃ Cq))))
      (le_max_right B₀ (max B₁ (max B₂ (max B₃ Cq))))
  · exact le_trans (le_trans (le_trans (le_max_left B₃ Cq) (le_max_right B₂ (max B₃ Cq)))
      (le_max_right B₁ (max B₂ (max B₃ Cq)))) (le_max_right B₀ (max B₁ (max B₂ (max B₃ Cq))))
  · exact le_trans (le_trans (le_trans (le_max_right B₃ Cq) (le_max_right B₂ (max B₃ Cq)))
      (le_max_right B₁ (max B₂ (max B₃ Cq)))) (le_max_right B₀ (max B₁ (max B₂ (max B₃ Cq))))

/-- A common upper bound for the polylogarithmic degrees returned by the four gap lemmas and by the
stopping time. -/
theorem exists_common_deg (K₀ K₁ K₂ K₃ K₄ : ℕ) :
    ∃ K : ℕ, K₀ ≤ K ∧ K₁ ≤ K ∧ K₂ ≤ K ∧ K₃ ≤ K ∧ K₄ ≤ K := by
  exact ⟨K₀ + K₁ + K₂ + K₃ + K₄, by omega, by omega, by omega, by omega, by omega⟩

/-- A common threshold below the three thresholds the dichotomy collects. -/
theorem exists_common_threshold {δ₁ δ₂ δ₃ : NNReal} (h₁ : 0 < δ₁) (h₁' : δ₁ ≤ 1)
    (h₂ : 0 < δ₂) (h₃ : 0 < δ₃) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ δ₀ ≤ δ₁ ∧ δ₀ ≤ δ₂ ∧ δ₀ ≤ δ₃ := by
  refine ⟨min (min δ₁ δ₂) δ₃, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_min (lt_min h₁ h₂) h₃
  · calc
      min (min δ₁ δ₂) δ₃ ≤ min δ₁ δ₂ := min_le_left _ _
      _ ≤ δ₁ := min_le_left _ _
      _ ≤ 1 := h₁'
  · calc
      min (min δ₁ δ₂) δ₃ ≤ min δ₁ δ₂ := min_le_left _ _
      _ ≤ δ₁ := min_le_left _ _
  · calc
      min (min δ₁ δ₂) δ₃ ≤ min δ₁ δ₂ := min_le_left _ _
      _ ≤ δ₂ := min_le_right _ _
  · exact min_le_right _ _

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The hierarchy constant of `Kakeya.MultiScaleFac.GridUniform.toUniformTubeSet` dominates the
ambient uniformity constant. -/
theorem le_uniformTubeSetCuOf (C : NNReal) : C ≤ uniformTubeSetCuOf (E := E) C := by
  rw [uniformTubeSetCuOf]
  exact le_max_left _ _

omit [Nontrivial E] in
/-- An empty family is Frostman in every node of any hierarchy over it, at every error. -/
theorem isFrostmanAtEveryScale_of_not_nonempty {ι : Type*} {δ : NNReal}
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C)
    (hs : ¬ s.Nonempty) (A : ENNReal) :
    𝒰.IsFrostmanAtEveryScale A := by
  have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
  simp [UniformTubeSet.IsFrostmanAtEveryScale, ConvexSpaceBody.IsFrostmanIn, hs',
    coverClass, densityIn_empty]

omit [Nontrivial E] in
/-- The leaf-anchored counterpart of `isFrostmanAtEveryScale_of_not_nonempty`: an empty family
is Frostman at every real scale, at every error, the anchor quantifier being vacuous. -/
theorem leaf_isFrostmanAtEveryScale_of_not_nonempty {ι : Type*} {δ : NNReal}
    {s : Finset ι} {T : ι → Tube δ E} (hs : ¬ s.Nonempty) (A : ENNReal) :
    StickyKakeya.IsFrostmanAtEveryScale s T A := by
  have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
  intro ρ _ _ i₀ hi₀
  rw [hs'] at hi₀
  exact absurd hi₀ (Finset.notMem_empty i₀)

/-- **The leaf-anchored error of alternative (i) is a grid loss.**  The engine constant enters at
the grid-length power `M + 1`, which is the base exponent of `gridLoss`, and the block constant at
the `δ`-independent power `p`, which by `gridLoss_pow` only enlarges the base and the degree. -/
private theorem blockPow_le_gridLoss {δ : NNReal} (hδ1 : δ ≤ 1) (A Cg : NNReal) (hA : 1 ≤ A)
    (hCg : 1 ≤ Cg) (Kg p : ℕ) {Ct : NNReal}
    (hCt : (Ct : ENNReal) ≤ ENNReal.ofReal (gridLoss Cg Kg δ)) :
    (A : ENNReal) ^ (ssfGridLen δ + 1) * (Ct : ENNReal) ^ p
      ≤ ENNReal.ofReal (gridLoss (A * Cg ^ p) (Kg * p) δ) := by
  have hg1 : (1 : ℝ) ≤ gridLoss Cg Kg δ := one_le_gridLoss Cg hCg Kg hδ1
  have hg0 : (0 : ℝ) ≤ gridLoss Cg Kg δ := le_trans (by norm_num) hg1
  have hCtR : (Ct : ℝ) ≤ gridLoss Cg Kg δ := by
    rw [← ENNReal.ofReal_coe_nnreal] at hCt
    exact (ENNReal.ofReal_le_ofReal_iff hg0).mp hCt
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := by exact_mod_cast le_trans (zero_le_one) hA
  have hCtR0 : (0 : ℝ) ≤ (Ct : ℝ) := by positivity
  have hCtRp : (Ct : ℝ) ^ p ≤ (gridLoss Cg Kg δ) ^ p :=
    pow_le_pow_left₀ hCtR0 hCtR p
  have hCgp : (gridLoss Cg Kg δ) ^ p = gridLoss (Cg ^ p) (Kg * p) δ := by
    rw [gridLoss_pow, Nat.mul_comm]
  have hAgl : (A : ℝ) ^ (ssfGridLen δ + 1) = gridLoss A 0 δ := by
    simp [gridLoss]
  have hleR :
      (A : ℝ) ^ (ssfGridLen δ + 1) * (Ct : ℝ) ^ p ≤ gridLoss (A * Cg ^ p) (Kg * p) δ := by
    calc
      (A : ℝ) ^ (ssfGridLen δ + 1) * (Ct : ℝ) ^ p
          ≤ (A : ℝ) ^ (ssfGridLen δ + 1) * (gridLoss Cg Kg δ) ^ p := by
        exact mul_le_mul_of_nonneg_left hCtRp (pow_nonneg hA0 (ssfGridLen δ + 1))
      _ = gridLoss A (0) δ * gridLoss (Cg ^ p) (Kg * p) δ := by
        rw [hAgl, hCgp]
      _ = gridLoss (A * Cg ^ p) (0 + Kg * p) δ := gridLoss_mul A (Cg ^ p) 0 (Kg * p) δ
      _ = gridLoss (A * Cg ^ p) (Kg * p) δ := by rw [zero_add]
  have hAEn : (A : ENNReal) ^ (ssfGridLen δ + 1) =
      ENNReal.ofReal ((A : ℝ) ^ (ssfGridLen δ + 1)) := by
    rw [ENNReal.ofReal_pow hA0, ENNReal.ofReal_coe_nnreal]
  have hCtEn : (Ct : ENNReal) ^ p = ENNReal.ofReal ((Ct : ℝ) ^ p) := by
    rw [ENNReal.ofReal_pow hCtR0, ENNReal.ofReal_coe_nnreal]
  calc
    (A : ENNReal) ^ (ssfGridLen δ + 1) * (Ct : ENNReal) ^ p
        = ENNReal.ofReal ((A : ℝ) ^ (ssfGridLen δ + 1)) * ENNReal.ofReal ((Ct : ℝ) ^ p) := by
      rw [hAEn, hCtEn]
    _ = ENNReal.ofReal ((A : ℝ) ^ (ssfGridLen δ + 1) * (Ct : ℝ) ^ p) := by
      exact (ENNReal.ofReal_mul (pow_nonneg hA0 (ssfGridLen δ + 1))).symm
    _ ≤ ENNReal.ofReal (gridLoss (A * Cg ^ p) (Kg * p) δ) := ENNReal.ofReal_le_ofReal hleR

/-- **In the all-short branch the cut set has at least three elements.**  A two-element cut set is
`{0, M}` with the two adjacent, and with `16 ≤ M` and `ε ≤ 1/64` the block `(0, M)` is long. -/
private theorem three_le_card_of_short {M : ℕ} (hM : 16 ≤ M) {ε : ℝ} (hεpos : 0 < ε)
    (hε64 : ε ≤ 1 / 64) (S : Finset ℕ) (h0 : 0 ∈ S) (hMS : M ∈ S)
    (hshort : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) → ¬ IsLongBlock M ε a b) :
    3 ≤ S.card := by
  by_contra h
  have hc_le : S.card ≤ 2 := by omega
  have h0neM : (0 : ℕ) ≠ M := by omega
  have hpair : ({0, M} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h0
    · exact hMS
  have hpair_card : ({0, M} : Finset ℕ).card = 2 := by
    simp [h0neM]
  have hc_ge : 2 ≤ S.card := by
    have hmono : ({0, M} : Finset ℕ).card ≤ S.card := Finset.card_mono hpair
    omega
  have hScard2 : S.card = 2 := le_antisymm hc_le hc_ge
  have hS : S = ({0, M} : Finset ℕ) := by
    symm
    exact Finset.eq_of_subset_of_card_le hpair (by omega)
  have hadj : ∀ x ∈ S, ¬(0 < x ∧ x < M) := by
    intro x hxS
    have hxmem : x ∈ ({0, M} : Finset ℕ) := by
      simpa [hS] using hxS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
    rcases hxmem with rfl | rfl
    · omega
    · omega
  have hlt : (0 : ℕ) < M := by omega
  have hnotLong : ¬ IsLongBlock M ε 0 M := hshort 0 h0 M hMS hlt hadj
  have hlong : IsLongBlock M ε 0 M := by
    unfold IsLongBlock
    simp only [add_zero]
    have hM1 : 1 ≤ M := by omega
    have hM16R : (16 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hle : ε * (M : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by
      calc
        ε * (M : ℝ) ≤ (1 / 64 : ℝ) * (M : ℝ) := by
          exact mul_le_mul_of_nonneg_right hε64 (by positivity)
        _ ≤ (M : ℝ) - 1 := by nlinarith [hM16R]
        _ = ((M - 1 : ℕ) : ℝ) := by simp [hM1]
    have hcomp : ⌈ε * (M : ℝ)⌉₊ ≤ M - 1 := (Nat.ceil_le).mpr hle
    omega
  exact hnotLong hlong

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The constant of alternative (i), raised to the displayed loss.**  The node-anchored reading
costs the factor `nodeClassConst · C_v^3` of `isFrostmanAtEveryScale_nodes_of_fibre` and a floor at
`tubeVolRatio`; both are absorbed into `B`, and the product of the engine constant with the `p`-th
power of the block constant is a `gridLoss`, hence a `totalLoss`. -/
private theorem alternativeOne_const_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ε : ℝ} (hεpos : 0 < ε) (A Cg Cv B : NNReal) (hA1 : 1 ≤ A) (hCg : 1 ≤ Cg)
    (Kg p c : ℕ) {Ct : NNReal}
    (hCtG : (Ct : ENNReal) ≤ ENNReal.ofReal (gridLoss Cg Kg δ))
    (hB1 : 1 ≤ B) (hGB : A * Cg ^ p ≤ B)
    (hDB : nodeClassConst (E := E) * Cv ^ 3 ≤ B) (hTB : tubeVolRatio (E := E) ≤ B) :
    max ((nodeClassConst (E := E) : ENNReal) * (Cv : ENNReal) ^ 3 *
          ((A : ENNReal) ^ (ssfGridLen δ + 1) * (Ct : ENNReal) ^ p *
            ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε)))))
        (tubeVolRatio (E := E) : ENNReal)
      ≤ (B : ENNReal) * totalLoss B (Kg * p) c δ
          * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε))) := by
  refine max_le ?_ ?_
  · have hDcast : ((nodeClassConst (E := E) * Cv ^ 3 : NNReal) : ENNReal) =
        (nodeClassConst (E := E) : ENNReal) * (Cv : ENNReal) ^ 3 := by
      rw [ENNReal.coe_mul, ENNReal.coe_pow]
    have houter :
        (nodeClassConst (E := E) : ENNReal) * (Cv : ENNReal) ^ 3 ≤ (B : ENNReal) := by
      rw [← hDcast]
      exact (ENNReal.coe_le_coe).mpr hDB
    have hG1 : (1 : NNReal) ≤ A * Cg ^ p := by
      exact one_le_mul_of_one_le_of_one_le hA1 (one_le_pow₀ hCg)
    have hblock := blockPow_le_gridLoss hδ1 A Cg hA1 hCg Kg p hCtG
    have hgrid : gridLoss (A * Cg ^ p) (Kg * p) δ ≤ gridLoss B (Kg * p) δ :=
      gridLoss_mono hG1 hGB le_rfl hδ1
    have hgridB : ENNReal.ofReal (gridLoss B (Kg * p) δ) ≤ totalLoss B (Kg * p) c δ :=
      gridLoss_le_totalLoss B hB1 (Kg * p) c hδ hδ1
    have hmiddle :
        (A : ENNReal) ^ (ssfGridLen δ + 1) * (Ct : ENNReal) ^ p
          ≤ totalLoss B (Kg * p) c δ := by
      calc
        (A : ENNReal) ^ (ssfGridLen δ + 1) * (Ct : ENNReal) ^ p
            ≤ ENNReal.ofReal (gridLoss (A * Cg ^ p) (Kg * p) δ) := hblock
        _ ≤ ENNReal.ofReal (gridLoss B (Kg * p) δ) := ENNReal.ofReal_le_ofReal hgrid
        _ ≤ totalLoss B (Kg * p) c δ := hgridB
    have hprod :
        ((nodeClassConst (E := E) : ENNReal) * (Cv : ENNReal) ^ 3) *
            ((A : ENNReal) ^ (ssfGridLen δ + 1) * (Ct : ENNReal) ^ p)
        ≤ (B : ENNReal) * totalLoss B (Kg * p) c δ := by
      exact mul_le_mul' houter hmiddle
    calc
      (nodeClassConst (E := E) : ENNReal) * (Cv : ENNReal) ^ 3 *
          ((A : ENNReal) ^ (ssfGridLen δ + 1) * (Ct : ENNReal) ^ p *
            ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε))))
          = ((nodeClassConst (E := E) : ENNReal) * (Cv : ENNReal) ^ 3 *
              ((A : ENNReal) ^ (ssfGridLen δ + 1) * (Ct : ENNReal) ^ p)) *
              ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε))) := by
            ac_rfl
      _ ≤ ((B : ENNReal) * totalLoss B (Kg * p) c δ) *
            ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε))) := by
          exact mul_le_mul' hprod le_rfl
  · have hTBe : (tubeVolRatio (E := E) : ENNReal) ≤ (B : ENNReal) :=
      ENNReal.coe_le_coe.mpr hTB
    have h1tot : (1 : ENNReal) ≤ totalLoss B (Kg * p) c δ :=
      one_le_totalLoss B hB1 (Kg * p) c hδ hδ1
    have h1pow : (1 : ENNReal) ≤ ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε))) := by
      have hδ0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
      have hδ1R : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
      have hεnonpos : -(5 * ε) ≤ 0 := by linarith
      have hR : (1 : ℝ) ≤ (δ : ℝ) ^ (-(5 * ε)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ0 hδ1R hεnonpos
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hR
    have hle1 : (B : ENNReal) * (1 : ENNReal) ≤
        (B : ENNReal) * totalLoss B (Kg * p) c δ := by
      exact mul_le_mul' (le_rfl : (B : ENNReal) ≤ (B : ENNReal)) h1tot
    calc
      (tubeVolRatio (E := E) : ENNReal) ≤ (B : ENNReal) := hTBe
      _ = (B : ENNReal) * (1 : ENNReal) := (mul_one _).symm
      _ = (B : ENNReal) * (1 : ENNReal) * (1 : ENNReal) := (mul_one _).symm
      _ ≤ (B : ENNReal) * totalLoss B (Kg * p) c δ *
            ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε))) := by
          exact mul_le_mul' hle1 h1pow

/-- **Alternative (i) of the amended GWZ Lemma 7.7(A), at the hoisted block constant.**  The
all-short branch of the dichotomy: a cut set `S` all of whose adjacent blocks are short and carry
the block bound at the terminal constant `Ct`, together with the unit-scale bound `hbase`, force
the retained family to be Frostman at every grid scale with error `B · totalLoss · δ^{-5ε}`.

Both readings are returned.  The *leaf-anchored* one
(`Kakeya.StickyKakeya.IsFrostmanAtEveryScale`) is what the proof actually produces, through
`Kakeya.MultiScaleFac.isFrostmanAtEveryScale_of_cuts_blockPow_uniform`; the *node-anchored* one
is its image under `Kakeya.MultiScaleFac.isFrostmanAtEveryScale_nodes_of_fibre`, read on the
hierarchy `𝒰` supplied here.  The leaf reading is the stronger datum: it mentions no hierarchy at
all, so a consumer may transport it to *any* hierarchy — in particular to one whose uniformity
constant is dimension-only — which the node reading, tied to `𝒰` and hence to `Cv`, cannot do. -/
theorem alternativeOne_of_cuts (hn : Module.finrank ℝ E = 3)
    (N : ℕ) (hN : 4096 ≤ N) {ε : ℝ} (hε : ε = 1 / Real.sqrt (N : ℝ))
    (Cv Cg : NNReal) (hCv : 1 ≤ Cv) (hCg : 1 ≤ Cg) (Kg c : ℕ) :
    ∃ (B : NNReal) (K : ℕ), 1 ≤ B ∧ Cv ≤ B ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 →
        δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ)) → 16 ≤ ssfGridLen δ →
        1 ≤ ε ^ 2 * (ssfGridLen δ : ℝ) →
      ∀ (s : Finset ι) (T : ι → Tube δ E), s.Nonempty →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ 𝒰 : UniformTubeSet s T (ssfGridLen δ) Cv,
      ComparableFibreCounts s T (gridScales δ (ssfGridLen δ)) Cv →
      ∀ Ct : NNReal, 1 ≤ Ct → (Ct : ENNReal) ≤ ENNReal.ofReal (gridLoss Cg Kg δ) →
      ∀ (η : ℕ → ℝ) (m : ℕ), m < N →
        0 ≤ η 0 → (∀ k < N, η k ≤ ε * η (k + 1)) → η N ≤ ε →
      ∀ S : Finset ℕ, 0 ∈ S → ssfGridLen δ ∈ S → S ⊆ Finset.range (ssfGridLen δ + 1) →
        S.card = m + 2 →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
        BlockFrostman s T (ssfGridLen δ) Ct (η m) a b ∧
          ¬ IsLongBlock (ssfGridLen δ) ε a b) →
      (∀ i₀ ∈ s,
        ConvexSpaceBody.frostmanConstant (fibreIndex s T δ 1 i₀) (fibreBodies T δ)
            ((T i₀).rescale 1).toConvexSpaceBody
          ≤ (Ct : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-(η m)))) →
      StickyKakeya.IsFrostmanAtEveryScale s T
          ((B : ENNReal) * totalLoss B K c δ
            * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε)))) ∧
        𝒰.IsFrostmanAtEveryScale
          ((B : ENNReal) * totalLoss B K c δ
            * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε)))) := by
  classical
  have hεpos : 0 < ε := eps_pos_of_eq_one_div_sqrt (by omega : 16 ≤ N) hε
  have hε64 : ε ≤ 1 / 64 := eps_le_one_div_64_of_eq_one_div_sqrt hN hε
  have hNpos : 0 < N := by omega
  obtain ⟨A, hA1, HFR⟩ :=
    isFrostmanAtEveryScale_of_cuts_blockPow_uniform.{u, _} (E := E) hn hεpos hε64 Cv hCv
  set G : NNReal := A * Cg ^ (N + 1) with hG_def
  set D : NNReal := nodeClassConst (E := E) * Cv ^ 3 with hD_def
  set B : NNReal := max (max Cv G) (max D (tubeVolRatio (E := E))) with hB_def
  have hCvB : Cv ≤ B := le_trans (le_max_left _ _) (le_max_left _ _)
  have hGB : G ≤ B := le_trans (le_max_right _ _) (le_max_left _ _)
  have hDB : D ≤ B := le_trans (le_max_left _ _) (le_max_right _ _)
  have hTB : tubeVolRatio (E := E) ≤ B := le_trans (le_max_right _ _) (le_max_right _ _)
  have hB1 : (1 : NNReal) ≤ B := le_trans hCv hCvB
  refine ⟨B, Kg * (N + 1), hB1, hCvB, ?_⟩
  intro ι δ hδ hδ1 hδ16 h16M hεM s T hs hball 𝒰 hCF Ct hCt1 hCtG η m hm hη0 hηgap hηN
    S h0S hMS hSsub hScard hAll hunit
  have hδ1R : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hMpos : 0 < ssfGridLen δ := by omega
  have hηm : 0 ≤ η m := eta_nonneg_of_gap N hNpos hε η hη0 hηgap m (le_of_lt hm)
  have hηm1 : η (m + 1) ≤ ε := eta_succ_le_eps hNpos hε η hη0 hηgap hηN hm
  have hζεε : η m ≤ ε * ε :=
    le_trans (hηgap m hm) (mul_le_mul_of_nonneg_left hηm1 (le_of_lt hεpos))
  have hScard3 : 3 ≤ S.card :=
    three_le_card_of_short h16M hεpos hε64 S h0S hMS
      (fun a ha b hb hab hadj => (hAll a ha b hb hab hadj).2)
  have hScardp : S.card ≤ N + 1 := by omega
  have hleaf := HFR (ssfGridLen δ) hMpos hεM hδ hδ1R hδ16 s T hball 𝒰 hCF Ct hCt1 (N + 1)
    (by omega) S hScardp hScard3 h0S hMS hSsub (η m) hηm hζεε hAll hunit
  have hnodes := isFrostmanAtEveryScale_nodes_of_fibre hδ hδ1 hMpos hδ16 𝒰 hs hleaf
  have hconst := alternativeOne_const_le (E := E) hδ hδ1 hεpos A Cg Cv B hA1 hCg Kg (N + 1) c hCtG
      hB1 hGB hDB hTB
  refine ⟨?_, UniformTubeSet.IsFrostmanAtEveryScale.mono hnodes hconst⟩
  -- the leaf reading, at the same displayed constant: the node reading only *adds* the factor
  -- `nodeClassConst · Cv ³ ≥ 1`, so the bound absorbing that factor absorbs the bare one too.
  refine StickyKakeya.IsFrostmanAtEveryScale.mono_constant hleaf (le_trans ?_ hconst)
  refine le_trans ?_ (le_max_left _ _)
  refine le_mul_of_one_le_left (by simp) ?_
  have hone : (1 : NNReal) ≤ nodeClassConst (E := E) * Cv ^ 3 :=
    one_le_mul_of_one_le_of_one_le one_le_nodeClassConst (one_le_pow₀ hCv)
  calc (1 : ENNReal) = ((1 : NNReal) : ENNReal) := by norm_num
    _ ≤ ((nodeClassConst (E := E) * Cv ^ 3 : NNReal) : ENNReal) := ENNReal.coe_le_coe.mpr hone
    _ = (nodeClassConst (E := E) : ENNReal) * (Cv : ENNReal) ^ 3 := by
        rw [ENNReal.coe_mul, ENNReal.coe_pow]

/-- **A grid ratio raised to a nonnegative exponent is at least one.**  The grid scale at an index
`b ≤ M` is at least the leaf scale `δ`, so the displayed ratio `σ_b/δ` is at least `1`. -/
private theorem one_le_gridRatio_rpow {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {M b : ℕ}
    (hM : 0 < M) (hb : b ≤ M) {ζ : ℝ} (hζ : 0 ≤ ζ) :
    (1 : ENNReal) ≤ ENNReal.ofReal (((gridScale δ M b : ℝ) / (δ : ℝ)) ^ ζ) := by
  have hgs : δ ≤ gridScale δ M b := by
    have h := gridScale_antitone hδ hδ1 M hb
    rwa [gridScale_self δ hM] at h
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hgsR : (δ : ℝ) ≤ (gridScale δ M b : ℝ) := by exact_mod_cast hgs
  have hratio : (1 : ℝ) ≤ (gridScale δ M b : ℝ) / (δ : ℝ) := (one_le_div hδR).mpr hgsR
  have hpow : (1 : ℝ) ≤ ((gridScale δ M b : ℝ) / (δ : ℝ)) ^ ζ := Real.one_le_rpow hratio hζ
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal hpow

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The node-anchored constant of a cut-scale bound, raised to the displayed loss.**  This is
`alternativeOne_const_le` with the fixed power `δ^{-5ε}` replaced by an arbitrary displayed
factor `X ≥ 1`: the node reading costs `nodeClassConst · C_v^3` and a floor at `tubeVolRatio`, both
absorbed into `B`, while the engine constant at the grid-length power times the `p`-th power of the
block constant is a `gridLoss`, hence a `totalLoss`. -/
private theorem nodeClass_const_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (A Cg Cv B : NNReal) (hA1 : 1 ≤ A) (hCg : 1 ≤ Cg) (Kg p c : ℕ) {Ct : NNReal}
    (hCtG : (Ct : ENNReal) ≤ ENNReal.ofReal (gridLoss Cg Kg δ))
    (hB1 : 1 ≤ B) (hGB : A * Cg ^ p ≤ B)
    (hDB : nodeClassConst (E := E) * Cv ^ 3 ≤ B) (hTB : tubeVolRatio (E := E) ≤ B)
    {X : ENNReal} (hX : 1 ≤ X) :
    max ((nodeClassConst (E := E) : ENNReal) * (Cv : ENNReal) ^ 3 *
          ((A : ENNReal) ^ (ssfGridLen δ + 1) * (Ct : ENNReal) ^ p * X))
        (tubeVolRatio (E := E) : ENNReal)
      ≤ (B : ENNReal) * totalLoss B (Kg * p) c δ * X := by
  refine max_le ?_ ?_
  · have hDcast : ((nodeClassConst (E := E) * Cv ^ 3 : NNReal) : ENNReal) =
        (nodeClassConst (E := E) : ENNReal) * (Cv : ENNReal) ^ 3 := by
      rw [ENNReal.coe_mul, ENNReal.coe_pow]
    have houter :
        (nodeClassConst (E := E) : ENNReal) * (Cv : ENNReal) ^ 3 ≤ (B : ENNReal) := by
      rw [← hDcast]
      exact (ENNReal.coe_le_coe).mpr hDB
    have hG1 : (1 : NNReal) ≤ A * Cg ^ p := by
      exact one_le_mul_of_one_le_of_one_le hA1 (one_le_pow₀ hCg)
    have hblock := blockPow_le_gridLoss hδ1 A Cg hA1 hCg Kg p hCtG
    have hgrid : gridLoss (A * Cg ^ p) (Kg * p) δ ≤ gridLoss B (Kg * p) δ :=
      gridLoss_mono hG1 hGB le_rfl hδ1
    have hgridB : ENNReal.ofReal (gridLoss B (Kg * p) δ) ≤ totalLoss B (Kg * p) c δ :=
      gridLoss_le_totalLoss B hB1 (Kg * p) c hδ hδ1
    have hmiddle :
        (A : ENNReal) ^ (ssfGridLen δ + 1) * (Ct : ENNReal) ^ p
          ≤ totalLoss B (Kg * p) c δ := by
      calc
        (A : ENNReal) ^ (ssfGridLen δ + 1) * (Ct : ENNReal) ^ p
            ≤ ENNReal.ofReal (gridLoss (A * Cg ^ p) (Kg * p) δ) := hblock
        _ ≤ ENNReal.ofReal (gridLoss B (Kg * p) δ) := ENNReal.ofReal_le_ofReal hgrid
        _ ≤ totalLoss B (Kg * p) c δ := hgridB
    have hprod :
        ((nodeClassConst (E := E) : ENNReal) * (Cv : ENNReal) ^ 3) *
            ((A : ENNReal) ^ (ssfGridLen δ + 1) * (Ct : ENNReal) ^ p)
        ≤ (B : ENNReal) * totalLoss B (Kg * p) c δ := by
      exact mul_le_mul' houter hmiddle
    calc
      (nodeClassConst (E := E) : ENNReal) * (Cv : ENNReal) ^ 3 *
          ((A : ENNReal) ^ (ssfGridLen δ + 1) * (Ct : ENNReal) ^ p * X)
          = ((nodeClassConst (E := E) : ENNReal) * (Cv : ENNReal) ^ 3 *
              ((A : ENNReal) ^ (ssfGridLen δ + 1) * (Ct : ENNReal) ^ p)) * X := by
            ac_rfl
      _ ≤ ((B : ENNReal) * totalLoss B (Kg * p) c δ) * X := by
          exact mul_le_mul' hprod le_rfl
  · have hTBe : (tubeVolRatio (E := E) : ENNReal) ≤ (B : ENNReal) :=
      ENNReal.coe_le_coe.mpr hTB
    have h1tot : (1 : ENNReal) ≤ totalLoss B (Kg * p) c δ :=
      one_le_totalLoss B hB1 (Kg * p) c hδ hδ1
    have hle1 : (B : ENNReal) * (1 : ENNReal) ≤
        (B : ENNReal) * totalLoss B (Kg * p) c δ := by
      exact mul_le_mul' (le_rfl : (B : ENNReal) ≤ (B : ENNReal)) h1tot
    calc
      (tubeVolRatio (E := E) : ENNReal) ≤ (B : ENNReal) := hTBe
      _ = (B : ENNReal) * (1 : ENNReal) := (mul_one _).symm
      _ = (B : ENNReal) * (1 : ENNReal) * (1 : ENNReal) := (mul_one _).symm
      _ ≤ (B : ENNReal) * totalLoss B (Kg * p) c δ * X := by
          exact mul_le_mul' hle1 hX

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The node-transport constant of a block bound, raised to the displayed loss.**  The passage
from the fibre family to the node family costs `nodeTransportConst · C_v^5`, and the terminal block
constant is charged to the displayed loss; both are absorbed into `B`. -/
private theorem nodeTransport_const_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (Cg Cv B : NNReal) (hCg : 1 ≤ Cg) (K c : ℕ) {Ct : NNReal}
    (hCtG : (Ct : ENNReal) ≤ ENNReal.ofReal (gridLoss Cg K δ))
    (hB1 : 1 ≤ B) (hCgB : Cg ≤ B) (hNB : nodeTransportConst (E := E) * Cv ^ 5 ≤ B)
    {X : ENNReal} :
    (nodeTransportConst (E := E) : ENNReal) * (Cv : ENNReal) ^ 5 * ((Ct : ENNReal) * X)
      ≤ (B : ENNReal) * totalLoss B K c δ * X := by
  have hNcast : ((nodeTransportConst (E := E) * Cv ^ 5 : NNReal) : ENNReal) =
        (nodeTransportConst (E := E) : ENNReal) * (Cv : ENNReal) ^ 5 := by
      rw [ENNReal.coe_mul, ENNReal.coe_pow]
  have houter :
        (nodeTransportConst (E := E) : ENNReal) * (Cv : ENNReal) ^ 5 ≤ (B : ENNReal) := by
      rw [← hNcast]
      exact (ENNReal.coe_le_coe).mpr hNB
  have hgrid : gridLoss Cg K δ ≤ gridLoss B K δ := gridLoss_mono hCg hCgB le_rfl hδ1
  have hgridB : ENNReal.ofReal (gridLoss B K δ) ≤ totalLoss B K c δ :=
    gridLoss_le_totalLoss B hB1 K c hδ hδ1
  have hmiddle : (Ct : ENNReal) ≤ totalLoss B K c δ := by
    calc
      (Ct : ENNReal) ≤ ENNReal.ofReal (gridLoss Cg K δ) := hCtG
      _ ≤ ENNReal.ofReal (gridLoss B K δ) := ENNReal.ofReal_le_ofReal hgrid
      _ ≤ totalLoss B K c δ := hgridB
  have hprod :
      ((nodeTransportConst (E := E) : ENNReal) * (Cv : ENNReal) ^ 5) * (Ct : ENNReal)
        ≤ (B : ENNReal) * totalLoss B K c δ := by
    exact mul_le_mul' houter hmiddle
  calc
    (nodeTransportConst (E := E) : ENNReal) * (Cv : ENNReal) ^ 5 * ((Ct : ENNReal) * X)
        = ((nodeTransportConst (E := E) : ENNReal) * (Cv : ENNReal) ^ 5 * (Ct : ENNReal)) * X := by
          ac_rfl
    _ ≤ ((B : ENNReal) * totalLoss B K c δ) * X := by
        exact mul_le_mul' hprod le_rfl

/-- **A non-terminal cut point has two cut points at or above it**, namely itself and the terminal
one.  This is the hypothesis of `Kakeya.MultiScaleFac.cutScale_le_of_cuts_blockPow_uniform` that
selects the indices at which the telescoping over the blocks below has something to telescope. -/
private theorem two_le_filter_card {S : Finset ℕ} {b M : ℕ} (hbS : b ∈ S) (hMS : M ∈ S)
    (hbM : b < M) :
    2 ≤ (S.filter (fun x => b ≤ x)).card := by
  classical
  have hb_mem : b ∈ S.filter (fun x => b ≤ x) := by
    rw [Finset.mem_filter]
    exact ⟨hbS, le_rfl⟩
  have hM_mem : M ∈ S.filter (fun x => b ≤ x) := by
    rw [Finset.mem_filter]
    exact ⟨hMS, le_of_lt hbM⟩
  have hbM_diff : b ≠ M := ne_of_lt hbM
  have hpair_sub : ({b, M} : Finset ℕ) ⊆ S.filter (fun x => b ≤ x) := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with hx | hx
    · simpa [hx] using hb_mem
    · rw [Finset.mem_singleton] at hx
      simpa [hx] using hM_mem
  have hpair_card : ({b, M} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by
      intro hmem
      rw [Finset.mem_singleton] at hmem
      exact hbM_diff hmem)]
    rw [Finset.card_singleton]
  rw [← hpair_card]
  exact Finset.card_le_card hpair_sub

/-- **The node reading of a cut-scale fibre bound.**  The leaf-anchored bound at the grid scale
`σ_b`, in the shape `Kakeya.MultiScaleFac.cutScale_le_of_cuts_blockPow_uniform` returns it, becomes
a bound on the Frostman constant of the class of a level-`b` node inside that node, through
`Kakeya.MultiScaleFac.isFrostmanIn_coverClass_of_fibre_grid`. -/
private theorem bulletOne_nodes_of_fibre {ι : Type*} {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : 0 < ssfGridLen δ) (hδ16 : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ)))
    {s : Finset ι} {T : ι → Tube δ E} {Cv : NNReal}
    (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cv) (hs : s.Nonempty)
    {b : ℕ} (hb : b ≤ ssfGridLen δ) {j : ι} (hj : j ∈ 𝒰.cover.indexSet b)
    (A Cg B : NNReal) (hA1 : 1 ≤ A) (hCg : 1 ≤ Cg) (Kg p c : ℕ) {Ct : NNReal}
    (hCtG : (Ct : ENNReal) ≤ ENNReal.ofReal (gridLoss Cg Kg δ))
    (hB1 : 1 ≤ B) (hGB : A * Cg ^ p ≤ B)
    (hDB : nodeClassConst (E := E) * Cv ^ 3 ≤ B) (hTB : tubeVolRatio (E := E) ≤ B)
    {ζ : ℝ} (hζ : 0 ≤ ζ)
    (hfib : ∀ i₀ ∈ s,
      ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (gridScale δ (ssfGridLen δ) b) i₀)
          (fibreBodies T δ) ((T i₀).rescale (gridScale δ (ssfGridLen δ) b)).toConvexSpaceBody
        ≤ (A : ENNReal) ^ (ssfGridLen δ + 1) * (Ct : ENNReal) ^ p *
            ENNReal.ofReal (((gridScale δ (ssfGridLen δ) b : ℝ) / (δ : ℝ)) ^ ζ)) :
    ConvexSpaceBody.frostmanConstant (coverClass s (𝒰.cover.assign b) j)
        (fun i => (T i).toConvexSpaceBody) (𝒰.cover.tube b j).toConvexSpaceBody
      ≤ (B : ENNReal) * totalLoss B (Kg * p) c δ *
          ENNReal.ofReal (((gridScale δ (ssfGridLen δ) b : ℝ) / (δ : ℝ)) ^ ζ) := by
  let X : ENNReal := ENNReal.ofReal (((gridScale δ (ssfGridLen δ) b : ℝ) / (δ : ℝ)) ^ ζ)
  rw [fibreBodies_self] at hfib
  have hB : ∀ i₀ ∈ s,
      ConvexSpaceBody.IsFrostmanIn (fibreIndex s T δ (gridScale δ (ssfGridLen δ) b) i₀)
        (fun i => (T i).toConvexSpaceBody)
        ((T i₀).rescale (gridScale δ (ssfGridLen δ) b)).toConvexSpaceBody
        ((A : ENNReal) ^ (ssfGridLen δ + 1) * (Ct : ENNReal) ^ p * X) :=
    fun i₀ hi₀ => ConvexSpaceBody.frostmanConstant_le_iff.mp (hfib i₀ hi₀)
  have hcls := isFrostmanIn_coverClass_of_fibre_grid hδ hδ1 hM hδ16 𝒰 hb hj hs hB
  exact le_trans (ConvexSpaceBody.frostmanConstant_le_of_isFrostmanIn hcls)
    (nodeClass_const_le hδ hδ1 A Cg Cv B hA1 hCg Kg p c hCtG hB1 hGB hDB hTB
      (one_le_gridRatio_rpow hδ hδ1 hM hb hζ))

/-- **The node reading at the finest grid index.**  At `b = M` the grid scale is the leaf scale, so
the class of a node is the family of leaves it collects and
`Kakeya.MultiScaleFac.isFrostmanIn_coverClass_bottom` bounds its Frostman constant by the
dimensional `tubeVolRatio`, with no telescoping and no displayed ratio. -/
private theorem bulletOne_bottom {ι : Type*} {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : 0 < ssfGridLen δ) {s : Finset ι} {T : ι → Tube δ E} {Cv B : NNReal}
    (𝒰 : UniformTubeSet s T (ssfGridLen δ) Cv) (hB1 : 1 ≤ B)
    (hTB : tubeVolRatio (E := E) ≤ B) (K c : ℕ) {ζ : ℝ} (_hζ : 0 ≤ ζ)
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet (ssfGridLen δ)) :
    ConvexSpaceBody.frostmanConstant (coverClass s (𝒰.cover.assign (ssfGridLen δ)) j)
        (fun i => (T i).toConvexSpaceBody)
        (𝒰.cover.tube (ssfGridLen δ) j).toConvexSpaceBody
      ≤ (B : ENNReal) * totalLoss B K c δ *
          ENNReal.ofReal
            (((gridScale δ (ssfGridLen δ) (ssfGridLen δ) : ℝ) / (δ : ℝ)) ^ ζ) := by
  have hδR0 : (0 : ℝ) < (δ : ℝ) := by
    exact_mod_cast hδ
  have hgrid : gridScale δ (ssfGridLen δ) (ssfGridLen δ) = δ := gridScale_self δ hM
  have hRatio : ((gridScale δ (ssfGridLen δ) (ssfGridLen δ) : ℝ) / (δ : ℝ)) = (1 : ℝ) := by
    rw [hgrid]
    exact div_self (ne_of_gt hδR0)
  have hTBe : (tubeVolRatio (E := E) : ENNReal) ≤ (B : ENNReal) :=
    ENNReal.coe_le_coe.mpr hTB
  have h1Tot : (1 : ENNReal) ≤ totalLoss B K c δ :=
    one_le_totalLoss B hB1 K c hδ hδ1
  have hle1 : (B : ENNReal) * (1 : ENNReal) ≤
      (B : ENNReal) * totalLoss B K c δ := by
    exact mul_le_mul' (le_rfl : (B : ENNReal) ≤ (B : ENNReal)) h1Tot
  calc
    ConvexSpaceBody.frostmanConstant (coverClass s (𝒰.cover.assign (ssfGridLen δ)) j)
        (fun i => (T i).toConvexSpaceBody)
        (𝒰.cover.tube (ssfGridLen δ) j).toConvexSpaceBody
        ≤ (tubeVolRatio (E := E) : ENNReal) := by
          exact ConvexSpaceBody.frostmanConstant_le_of_isFrostmanIn
            (isFrostmanIn_coverClass_bottom hδ hδ1 hM 𝒰 hj)
    _ ≤ (B : ENNReal) := hTBe
    _ = (B : ENNReal) * (1 : ENNReal) := (mul_one _).symm
    _ = (B : ENNReal) * (1 : ENNReal) * (1 : ENNReal) := (mul_one _).symm
    _ ≤ (B : ENNReal) * totalLoss B K c δ *
          ENNReal.ofReal
            (((gridScale δ (ssfGridLen δ) (ssfGridLen δ) : ℝ) / (δ : ℝ)) ^ ζ) := by
        rw [hRatio, one_rpow, ENNReal.ofReal_one]
        exact mul_le_mul' hle1 le_rfl

/-- **The first upper bound of alternative (ii), read at the nodes.**  The class of a level-`b` node
is Frostman inside that node, with the exponent `ζ = η_m` of the terminal stopping-time step and the
ratio `σ_b/δ`.  The block bound of the stopping time is telescoped from `b` down to the finest level
`M` and translated to node classes by `isFrostmanIn_coverClass_of_fibre_grid`. -/
theorem bulletOne_of_cuts (_hn : Module.finrank ℝ E = 3) (N : ℕ)
    (Cv Cg : NNReal) (hCv : 1 ≤ Cv) (hCg : 1 ≤ Cg) (Kg c : ℕ) :
    ∃ (B : NNReal) (K : ℕ), 1 ≤ B ∧ Cv ≤ B ∧ Kg ≤ K ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 →
        δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ)) → 0 < ssfGridLen δ →
      ∀ (s : Finset ι) (T : ι → Tube δ E), s.Nonempty →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ 𝒰 : UniformTubeSet s T (ssfGridLen δ) Cv,
      ComparableFibreCounts s T (gridScales δ (ssfGridLen δ)) Cv →
      ∀ Ct : NNReal, 1 ≤ Ct → (Ct : ENNReal) ≤ ENNReal.ofReal (gridLoss Cg Kg δ) →
      ∀ ζ : ℝ, 0 ≤ ζ →
      ∀ S : Finset ℕ, 0 ∈ S → ssfGridLen δ ∈ S → S ⊆ Finset.range (ssfGridLen δ + 1) →
        S.card ≤ N + 1 →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
        BlockFrostman s T (ssfGridLen δ) Ct ζ a b) →
      ∀ b ∈ S, 0 < b → ∀ j ∈ 𝒰.cover.indexSet b,
        ConvexSpaceBody.frostmanConstant (coverClass s (𝒰.cover.assign b) j)
            (fun i => (T i).toConvexSpaceBody)
            (𝒰.cover.tube b j).toConvexSpaceBody
          ≤ (B : ENNReal) * totalLoss B K c δ *
              ENNReal.ofReal (((gridScale δ (ssfGridLen δ) b : ℝ) / (δ : ℝ)) ^ ζ) := by
  classical
  obtain ⟨Acut, hAcut1, HCUT⟩ :=
    cutScale_le_of_cuts_blockPow_uniform.{u, _} (E := E) Cv hCv
  set B : NNReal := max (max Cv (Acut * Cg ^ (N + 1)))
      (max (nodeClassConst (E := E) * Cv ^ 3) (tubeVolRatio (E := E)))
  have hB1 : 1 ≤ B := by
    exact le_trans hCv (le_trans (le_max_left _ _) (le_max_left _ _))
  have hCvB : Cv ≤ B := le_trans (le_max_left _ _) (le_max_left _ _)
  have hGB : Acut * Cg ^ (N + 1) ≤ B :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hDB : nodeClassConst (E := E) * Cv ^ 3 ≤ B :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hTB : tubeVolRatio (E := E) ≤ B :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨B, Kg * (N + 1), hB1, hCvB, ?_, ?_⟩
  · exact Nat.le_mul_of_pos_right _ (by omega)
  · intro ι δ hδ hδ1 hδ16 hM s T hs hball 𝒰 hCF Ct hCt1 hCtG ζ hζ S h0S hMS hSsub hScard
      hBlock b hbS hb0 j hj
    have hδ1R : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
    have hbM : b ≤ ssfGridLen δ := Nat.lt_succ_iff.mp (Finset.mem_range.mp (hSsub hbS))
    by_cases hbeq : b = ssfGridLen δ
    · subst hbeq
      exact bulletOne_bottom hδ hδ1 hM 𝒰 hB1 hTB (Kg * (N + 1)) c hζ hj
    · have hblt : b < ssfGridLen δ := lt_of_le_of_ne hbM hbeq
      have hcard2 := two_le_filter_card hbS hMS hblt
      have hfib : ∀ i₀ ∈ s,
          ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (gridScale δ (ssfGridLen δ) b) i₀)
              (fibreBodies T δ) ((T i₀).rescale (gridScale δ (ssfGridLen δ) b)).toConvexSpaceBody
            ≤ (Acut : ENNReal) ^ (ssfGridLen δ + 1) * (Ct : ENNReal) ^ (N + 1) *
                ENNReal.ofReal (((gridScale δ (ssfGridLen δ) b : ℝ) / (δ : ℝ)) ^ ζ) :=
        fun i₀ hi₀ =>
          HCUT (ssfGridLen δ) hM hδ hδ1R hδ16 s T hball 𝒰 hCF Ct hCt1 (N + 1) (by omega) S
            hScard h0S hMS hSsub ζ hζ hBlock b hbS hb0 hcard2 i₀ hi₀
      exact bulletOne_nodes_of_fibre hδ hδ1 hM hδ16 𝒰 hs hbM hj Acut Cg B hAcut1 hCg
        Kg (N + 1) c hCtG hB1 hGB hDB hTB hζ hfib

/-- **The second upper bound of alternative (ii), read at the nodes.**  The level-`b` nodes under a
level-`a` node are Frostman inside it, with the exponent `ζ = η_m` and the ratio `σ_a/σ_b`.  Here
`(a, b)` is an adjacent pair of the cut set, so the only work is the translation
`Kakeya.MultiScaleFac.isFrostmanIn_nodesUnder_of_fibre`, costing `nodeTransportConst · C_v^5`. -/
theorem bulletTwo_of_blockFrostman (_hn : Module.finrank ℝ E = 3)
    (Cv Cg : NNReal) (hCv : 1 ≤ Cv) (hCg : 1 ≤ Cg) (Kg c : ℕ) :
    ∃ (B : NNReal) (K : ℕ), 1 ≤ B ∧ Cv ≤ B ∧ Kg ≤ K ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 →
        δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ)) → 0 < ssfGridLen δ →
      ∀ (s : Finset ι) (T : ι → Tube δ E), s.Nonempty →
      ∀ 𝒰 : UniformTubeSet s T (ssfGridLen δ) Cv,
      ∀ Ct : NNReal, (Ct : ENNReal) ≤ ENNReal.ofReal (gridLoss Cg Kg δ) →
      ∀ ζ : ℝ, 0 ≤ ζ →
      ∀ a b : ℕ, a < b → b ≤ ssfGridLen δ →
      BlockFrostman s T (ssfGridLen δ) Ct ζ a b →
      ∀ j ∈ 𝒰.cover.indexSet a,
        ConvexSpaceBody.frostmanConstant (𝒰.nodesUnder b a j)
            (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
            (𝒰.cover.tube a j).toConvexSpaceBody
          ≤ (B : ENNReal) * totalLoss B K c δ *
              ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
                  / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ζ) := by
  let B : NNReal := max (max Cv Cg) (nodeTransportConst (E := E) * Cv ^ 5)
  let K : ℕ := Kg
  refine ⟨B, K, ?_, ?_, ?_, ?_⟩
  · exact le_trans hCv (le_trans (le_max_left Cv Cg)
      (le_max_left (max Cv Cg) (nodeTransportConst (E := E) * Cv ^ 5)))
  · exact le_trans (le_max_left Cv Cg)
      (le_max_left (max Cv Cg) (nodeTransportConst (E := E) * Cv ^ 5))
  · exact le_rfl
  · intro ι δ hδ hδ1 hδ16 hM s T hs 𝒰 Ct hCtG ζ hζ a b hab hbM hblock j hj
    have hB1 : 1 ≤ B := by
      exact le_trans hCv (le_trans (le_max_left Cv Cg)
        (le_max_left (max Cv Cg) (nodeTransportConst (E := E) * Cv ^ 5)))
    have hCgB : Cg ≤ B := by
      exact le_trans (le_max_right Cv Cg)
        (le_max_left (max Cv Cg) (nodeTransportConst (E := E) * Cv ^ 5))
    have hNB : nodeTransportConst (E := E) * Cv ^ 5 ≤ B := by
      exact le_max_right (max Cv Cg) (nodeTransportConst (E := E) * Cv ^ 5)
    have hB : ∀ i₂ ∈ s,
        ConvexSpaceBody.IsFrostmanIn (fibreIndex s T δ (gridScale δ (ssfGridLen δ) a) i₂)
          (fibreBodies T (gridScale δ (ssfGridLen δ) b))
          ((T i₂).rescale (2 * gridScale δ (ssfGridLen δ) a)).toConvexSpaceBody
          ((Ct : ENNReal) * ENNReal.ofReal
            (((gridScale δ (ssfGridLen δ) a : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ζ)) := by
      intro i₂ hi₂
      exact ConvexSpaceBody.frostmanConstant_le_iff.mp (hblock i₂ hi₂)
    have ha : a < ssfGridLen δ := lt_of_lt_of_le hab hbM
    have h8d : 8 * δ ≤ gridScale δ (ssfGridLen δ) a :=
      eight_delta_le_gridScale hδ hδ1 ha hδ16
    have h2δ : 2 * δ ≤ gridScale δ (ssfGridLen δ) a := by
      refine le_trans (mul_le_mul_of_nonneg_right (by norm_num : (2 : NNReal) ≤ 8) ?_) h8d
      exact le_of_lt hδ
    have hnode := isFrostmanIn_nodesUnder_of_fibre hδ hδ1 hCv hs 𝒰 (le_of_lt hab) ha.le hbM h2δ hj
      hB
    exact le_trans (ConvexSpaceBody.frostmanConstant_le_of_isFrostmanIn hnode)
      (nodeTransport_const_le hδ hδ1 Cg Cv B hCg Kg c hCtG hB1 hCgB hNB)

/-! ### The lower bound of alternative (ii), moved to the nodes and to the `ε` window

`Kakeya.MultiScaleFac.alternative_two_of_terminal_block_sharp` delivers the lower bound in the
leaf-anchored form: on the window at exponent `(1+2κ)ε` with `κ = N/⌈log log 1/δ⌉`, at the factor
`δ^{-27/⌈log log 1/δ⌉}`, anchored at the doubled leaf `T_{i₀}^{(2ρ)}`, and only at the leaves of a
majority set `F`.  The amended statement needs it on GWZ's `ε` window, at a `totalLoss`, anchored at
the concentric `ρ`-rescale of a level-`b` node, and at *every* level-`b` node.  Three moves:

* the window widens from `(1+2κ)ε` to `ε`; the residual is `2κε(b-a) ≤ 2εN = 2√N` grid steps, hence
  a `Kakeya.MultiScaleFac.scaleGapLoss` and not a fixed power of `δ`
  (`Kakeya.MultiScaleFac.window_endpoint_le_scaleGapLoss_mul`).  This is what makes GWZ's `ε` window
  reachable at all: on a grid of length `N` the window has to be `3ε` and the gap to `ε` is a fixed
  power of `δ`;
* the factor `δ^{-27/⌈log log 1/δ⌉}` is already `Kakeya.MultiScaleFac.scaleGapLoss 27 δ`, so it is
  absorbed into the displayed loss; the container is moved by
  `Kakeya.StickyKakeya.le_scaleGapLoss_mul_frostmanConstant_nodesIn`;
* the majority set disappears, by the ancestor split
  `Kakeya.StickyKakeya.exists_frostmanConstant_nodesIn_rescale_le`, whose universal upper bound `Ψ`
  at the coarse level is supplied here by the second bullet.

Comparability of node Frostman constants across a level — the band of
`Kakeya.StickyKakeya.exists_homogenized_subfamily` — is what the last move ultimately rests on, and
no such band is available on the family the stopping time returns.  Two sharper obstructions were
recorded while attempting a band-free, purely combinatorial route:

* the coarse upper bound is stated here at the concrete value `C₃ · totalLoss C₃ K₃ c δ ·
  (σ_a/σ_b)^ζ` that the second bullet actually produces, and not as a bound by an ambient `Ψ`.  An
  ambient `Ψ` is vacuous: universally quantified and absent from the conclusion, it is satisfied by
  `Ψ = ⊤` for every family, so only the uniformity of `𝒰` and the lower bound on the majority set
  `F` would carry content.  Those two alone do not suffice: let `s` be the disjoint union of a
  planar packing `A` of `δ`-tubes inside a `δ`-slab
  and a parallel packing `B`, placed apart.  Both have `σ^{-(n-1)}` tubes of every grid radius `σ`,
  so a single hierarchy with a single branching number covers the union, and `F := A` meets
  `s.card = 2 * F.card` and is concentrated at every scale of the window, so it satisfies the
  leaf-anchored lower bound.  At a level-`b` node `j` under `B` the level-`b` nodes inside
  `T_j^{(ρ)}` are a full packing, their Frostman constant is `O(1)`, and the left-hand side is
  `δ^{-(1-ε) ζ' (b-a)/M}`, a fixed power of `δ`, which no `Kakeya.MultiScaleFac.totalLoss` absorbs;
* the goal at a node is equivalent to a *counting* deficiency,
  `|𝕋_b[T_j^{(ρ)}]| ≤ loss · (ρ/σ_b)^{n-1-ζ'}`.  One direction is the volume-sharpened form of
  `Kakeya.MultiScaleFac.card_mul_frostmanConstant_nodesIn_le` read at `K₁ = T_j`, with
  `Kakeya.StickyKakeya.one_le_frostmanConstant_tube` supplying the sub-body; and counts *are*
  comparable across a level, by the private
  `Kakeya.MultiScaleFac.card_nodesUnder_le_mul_card_nodesUnder`, so no band is needed to carry a
  count from a leaf of `F` to an arbitrary node.  What is missing is the
  step producing the deficiency at the leaf: a lower bound on a Frostman constant bounds `Δ_max / Δ`
  from below, and `Δ_max` of a family of nodes is *not* bounded by the bounded-overlap field of
  `Tube.UniformTubeSet` — the planar family above has bounded overlap and
  `Δ_max ≈ ρ/σ_b`.  Recovering the count needs an upper bound for `Δ_max`, that is, a band again, or
  an a priori packing bound `|𝕋_b[T_a]| ≲ (σ_a/σ_b)^{n-1}` for the hierarchy, which bushes refute.

## How the bullet is now proved

The section `Bullet3Core` above reduces the bullet to a single statement about *one grid level*.
`Kakeya.StickyKakeya.le_frostmanConstant_nodesIn_rescale_of_grid` shows: if the lower bound holds at
**every** node of a grid level `c` with `4 ρ_c ≤ ρ`, then it holds at every level-`b` node against
the real container `T_j^{(ρ)}`, at the price of one factor `Λ`.  That factor is the ratio of node
counts, which the second obstruction above correctly identifies as the place where half (A) differs
from half (B); it is *not* a power of `δ`, by the ancestor split at an unrestricted radius
(`Kakeya.MultiScaleFac.card_nodesIn_le_mul_card_nodesUnder_ratio`, whose packing count displays
`4ρ/ρ_c` in place of the fixed `32` of the old restricted form).  For `c` the grid index just below
`ρ/4` the ratio is under four grid steps, so `Λ` is a `Kakeya.MultiScaleFac.scaleGapLoss` and
`Kakeya.MultiScaleFac.totalLoss` absorbs it.  The monotonicity of `Kakeya.maxDensity` that half (B)
uses at this step is thereby replaced, and no band is needed for it.

What is left is exactly the *universal-in-the-node* hypothesis of that lemma, at the level `c` of
`ρ`.  The stopping time delivers the lower bound at the leaves of the majority set `F`, hence — by
`Kakeya.MultiScaleFac.frostmanConstant_fibre_le_mul_frostmanConstant_nodesIn` — at the `8
ρ_c`-dilate of the *single* level-`c` node carrying a leaf of `F`, and the first obstruction above
shows that uniformity and `F` alone do not spread it to the other nodes.  Spreading it needs a
two-sided band on `ConvexSpaceBody.frostmanConstant (𝒰.nodesUnder b c p)` that is indexed by the
*pair* `(c, b)`, since neither `c` nor `b` is known before the stopping time terminates.

That band is now available.  `Kakeya.MultiScaleFac.exists_maximal_cuts_banded_hoisted_selfBand`
carries a `Kakeya.MultiScaleFac.PairBandOn` on the terminal family's *own* grid-uniform cover, not
merely on a superfamily, and the bullet is proved from it as
`Kakeya.MultiScaleFac.bulletThree_of_alternativeTwo_banded`.  That statement supersedes the one
this note used to introduce, and differs from it in exactly two ways: it takes the grid-uniform
system together with its band in place of a bare `Tube.UniformTubeSet`, and it
displays its loss at an enlarged gap budget `cB`.  The enlargement is forced by the last step of the
argument: the clamp from the narrow window of exponent `(1 + 2κ)ε + 6/(b - a)` back onto GWZ's `ε`
window crosses `⌈8√N⌉` grid steps, each costing one unit of budget.  `cB` still depends on `N` and
the ambient dimension alone, so the displayed loss remains subpolynomial, and
`Kakeya.MultiScaleFac.dividingScalesFrostman` states all four of its gap conclusions at that one
budget. -/

/-! ### Side conditions of the sharp alternative (ii) -/

/-- The grid-length hypothesis `3N ≤ M` of the sharp dichotomy, over `ℝ`. -/
theorem three_mul_cast_le {N : ℕ} {δ : NNReal} (h : 3 * N ≤ ssfGridLen δ) :
    (3 : ℝ) * (N : ℝ) ≤ (ssfGridLen δ : ℝ) := by
  exact_mod_cast h

/-- The window-widening parameter `κ = N/M` is positive. -/
theorem kappa_pos {N : ℕ} {δ : NNReal} (hN : 0 < N) (hM : 0 < ssfGridLen δ) :
    0 < (N : ℝ) / (ssfGridLen δ : ℝ) := by
  exact div_pos (Nat.cast_pos.mpr hN) (Nat.cast_pos.mpr hM)

/-- The window-widening parameter `κ = N/M` meets `N ≤ κM` with equality. -/
theorem le_kappa_mul {N : ℕ} {δ : NNReal} (hM : 0 < ssfGridLen δ) :
    (N : ℝ) ≤ ((N : ℝ) / (ssfGridLen δ : ℝ)) * (ssfGridLen δ : ℝ) := by
  have h0 : (ssfGridLen δ : ℝ) ≠ 0 := by
    exact ne_of_gt (Nat.cast_pos.mpr hM)
  rw [div_mul_cancel₀ _ h0]

/-- The `16`-separation of the grid forces `δ < 1` strictly, which the sharp dichotomy needs. -/
theorem delta_lt_one {δ : NNReal} (_hδ : 0 < δ) (h16M : 16 ≤ ssfGridLen δ)
    (hδ16 : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ))) : (δ : ℝ) < 1 := by
  have hMpos : 0 < (ssfGridLen δ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num) h16M)
  calc
    (δ : ℝ) ≤ (16 : ℝ) ^ (-(ssfGridLen δ : ℝ)) := by
      simpa [NNReal.coe_rpow] using (NNReal.coe_le_coe.mpr hδ16)
    _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg (x := (16 : ℝ)) (by norm_num) (by linarith)

end SsfGaps

end MultiScaleFac

end Kakeya

end
