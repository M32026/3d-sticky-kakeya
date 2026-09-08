/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ChainUniform
public import Kakeya.MultiScaleFac.Clump
public import Kakeya.MultiScaleFac.Assembly
public import Kakeya.MultiScaleFac.Loss
public import Kakeya.MultiScaleFac.ProductFinal
public import Kakeya.MultiScaleFac.Refine

/-!
# The refined stopping time of GWZ Lemma 7.7(A)

The printed form of GWZ Lemma 7.7(A) — the dichotomy asserted for the family `𝕋` itself, with no
passage to a subfamily — is false; the counterexample is recorded in the docstring of the repaired
`Kakeya.MultiScaleFac.dividingScalesFrostman` and in the implementation note of the blueprint.  The
repair is to state the dichotomy for a refinement `s' ⊆ s` of proportion `δ^ε`,
which is exactly the convention of Wang–Zahl, whose corresponding dichotomies always output a
`δ^ε` refinement.

This file states the ingredients of that repair.  The repaired lemma itself is
`Kakeya.MultiScaleFac.dividingScalesFrostman`, in `Kakeya/MultiScaleFac.lean`.

The design turns on one asymmetry.  An upper bound on a Frostman constant descends to a
proportional subfamily at a bounded cost (`Kakeya.MultiScaleFac.frostmanConstant_le_of_subfamily`);
a **lower** bound descends in no generality at all.  Hence:

* the invariant `Good` of the stopping time is a family of *upper* bounds, so it survives every
  refinement step — `card_fibreIndex_le_mul_of_card_le` converts the global proportion into a
  per-fibre proportion, which is the legitimate residue of the printed proof's appeal to
  uniformity, and `Kakeya.MultiScaleFac.BlockFrostmanAt.of_subfamily` then moves the bound;
* the terminal step, which reads off a *lower* bound, discards nothing at all: the retained family
  is the final state itself and the failing side is kept only as a distinguished subset `F` of
  anchors, so the failure is read relative to the very family in which the conclusion's fibres are
  formed and no descent step arises.

Re-uniformization is performed *before* the test at each level, as part of the state, and never
after it: a re-uniformization following the test would move the fibres against which the test was
run, and the failure of the test does not survive that move.

## The two roles of `N`

`N` originally served both as the length of the scale grid `gridScale δ N ·` and as the bound on
the number of stopping-time steps, the two being welded together by `ε = 1/√N`.  In the
grid-side lemmas of this file — `exists_refined_cut_core`, `exists_rounding_grid_index_sharp`,
`dividingScales_lower_bound_on_failing_nodes_sharp`, `alternative_two_of_terminal_block_sharp` and
the `_blockPow_uniform` chain — `N` is now purely
the grid length, and the equation `ε = 1/√N` has been replaced by the individual facts those
proofs use: `0 < ε`, an upper bound on `ε` (`ε ≤ 1` or `ε ≤ 1/64`), the fineness threshold
`1 ≤ ε² N`, and `16 ≤ N`.  All of these hold with `ε` fixed and `N` taken large.

In `exists_rounding_grid_index_sharp`, `dividingScales_lower_bound_on_failing_nodes_sharp`,
`alternative_two_of_terminal_block_sharp` and `exists_refined_cut_hoisted` the grid length and `ε`
are moreover quantified *after* the `∃ C`, so a single constant serves every grid length.  For
`exists_refined_cut_hoisted` this forces the grid-length dependence of the two losses to be
displayed rather than hidden — `2(N+1)A^{N+1}(1 - \log δ)^{K(N+1)}` for the cardinality loss and
`(C'')^{N+1}(1 - \log δ)^{K''(N+1)}` for the block constant — because the underlying
re-uniformization `Kakeya.MultiScaleFac.exists_uniformize_subfamily_hoisted` costs one factor per
grid level and admits no form with a grid-length-independent base *and* exponent.  This is what
makes those lemmas usable at
the `δ`-dependent grid length `⌈log log 1/δ⌉` of GWZ Definition 2.1: a statement of the form
"for each `N` there is a constant" cannot be instantiated there, since the constant would have to
be chosen after a quantity depending on `δ`.  The hoisted forms are strictly stronger, so every
existing caller still goes through by obtaining `C` first and supplying its `N` afterwards.

`card_le_mul_rpow_neg_of_refinement_chain` and `eta_nonneg_of_gap` still carry `ε = 1/√N`, because
there `N` genuinely bounds the number of steps: it indexes the exponent chain `η : ℕ → ℝ` and
controls the accumulated powers `C''₀ ^ (N+1)`.
-/

@[expose] public section

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- **The scale separation of a long block.**  For a long block `(a,b)` the fine grid scale
`σ_b = gridScale δ N b` lies below `δ^ε σ_a`: by the explicit ratio formula
`gridScale_div_gridScale` the exponent `((b-a : ℕ) : ℝ) / N` is at least `ε`, and `x ↦ δ^x` is
antitone for `0 < δ ≤ 1`. -/
private lemma gridScale_b_le_rpow_eps_mul_gridScale_a_of_isLongBlock (N : ℕ) (hN : 0 < N)
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) ≤ 1) {ε : ℝ} {a b : ℕ} (hab : a < b)
    (hlong : IsLongBlock N ε a b) :
    (gridScale δ N b : ℝ) ≤ (δ : ℝ) ^ ε * (gridScale δ N a : ℝ) := by
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hδposR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hθpos : 0 < (gridScale δ N a : ℝ) := by exact_mod_cast (gridScale_pos hδ N a)
  have hlong' : ⌈ε * (N : ℝ)⌉₊ + a < b := by simpa [IsLongBlock] using hlong
  have hε_le : ε ≤ ((b - a : ℕ) : ℝ) / (N : ℝ) := by
    rw [le_div_iff₀ hNposR]
    exact (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈ε * (N : ℝ)⌉₊ ≤ b - a))
  have hratio : (gridScale δ N b : ℝ) / (gridScale δ N a : ℝ) =
      (δ : ℝ) ^ (((b - a : ℕ) : ℝ) / (N : ℝ)) := by
    rw [← NNReal.coe_div, gridScale_div_gridScale hδ N b a, NNReal.coe_rpow,
      show -(((a : ℝ) - (b : ℝ)) / (N : ℝ)) = ((b - a : ℕ) : ℝ) / (N : ℝ) by
        rw [Nat.cast_sub hab.le]; ring]
  rw [← div_le_iff₀ hθpos, hratio]
  exact Real.rpow_le_rpow_of_exponent_ge hδposR hδ1 hε_le

/-! ### A global proportion is a proportion in every fibre -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **A global proportion is a proportion in every fibre, uninflated anchor.**  The `σ = δ` case of
`card_fibreIndex_le_mul_of_card_le` with the anchor on the right inflated only by `4` rather than by
`8`: at the base member scale the branching-number detour reaches the fibre already at `4ρ`.  This
is the form `Kakeya.MultiScaleFac.BlockFrostmanAt.of_subfamily` consumes. -/
theorem card_fibreIndex_le_mul_of_card_le_four {ι : Type*} {δ ρ Cu : NNReal} {t t' : Finset ι}
    {T : ι → Tube δ E} (h : Tube.IsUniformAtScale t T ρ Cu)
    (h' : Tube.IsUniformAtScale t' T ρ Cu) (_htt' : t' ⊆ t) (hδρ : δ ≤ ρ)
    (hparent : (h'.parent.card : ℝ) ≤ (h.parent.card : ℝ))
    {A : ℝ} (hA1 : 1 ≤ A) (hA : (t.card : ℝ) ≤ A * (t'.card : ℝ)) {i₀ : ι} (hi₀ : i₀ ∈ t') :
    ((fibreIndex t T δ ρ i₀).card : ℝ)
      ≤ (Cu : ℝ) ^ 6 * A * ((fibreIndex t' T δ (4 * ρ) i₀).card : ℝ) := by
  classical
  set F : ℕ := (fibreIndex t T δ ρ i₀).card with hF
  set G : ℕ := (fibreIndex t' T δ (4 * ρ) i₀).card with hG
  set Q : ι → ι → Prop := fun j i => (T i).toConvexSpaceBody ≤
    (h.parentTube j).toConvexSpaceBody with hQ
  set Q' : ι → ι → Prop := fun j i => (T i).toConvexSpaceBody ≤
    (h'.parentTube j).toConvexSpaceBody with hQ'
  have hA_nonneg : 0 ≤ A := le_trans (by norm_num) hA1
  have hCu_nonneg : 0 ≤ (Cu : ℝ) := Cu.coe_nonneg
  have hPlower : (h.parent.card : NNReal) * h.branchingN ≤ Cu ^ 2 * (t.card : NNReal) := by
    have hswap : (∑ j ∈ h.parent, ((t.filter (fun i => Q j i)).card : NNReal))
        = (∑ i ∈ t, ((h.parent.filter (fun j => Q j i)).card : NNReal)) := by
      rw [← Nat.cast_sum, ← Nat.cast_sum]
      congr 1
      simp_rw [Finset.card_filter]
      rw [Finset.sum_comm]
    calc
      (h.parent.card : NNReal) * h.branchingN
          = ∑ _j ∈ h.parent, h.branchingN := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ h.parent, Cu * ((t.filter (fun i => Q j i)).card : NNReal) :=
          Finset.sum_le_sum fun j hj => by simpa only [hQ] using h.le_mul_card_filter hj
      _ = Cu * ∑ i ∈ t, ((h.parent.filter (fun j => Q j i)).card : NNReal) := by
          rw [← Finset.mul_sum, hswap]
      _ ≤ Cu * ∑ _i ∈ t, Cu :=
          mul_le_mul' le_rfl (Finset.sum_le_sum fun i hi => by
            simpa only [hQ] using h.parents_containing_tube_card_le hδρ (T i) hi le_rfl)
      _ = Cu ^ 2 * (t.card : NNReal) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have ht'upper : (t'.card : NNReal) ≤ Cu * (h'.parent.card : NNReal) * h'.branchingN := by
    have hcover : t' ⊆ Finset.biUnion h'.parent (fun j => t'.filter (fun i => Q' j i)) := by
      intro i hi
      obtain ⟨j, hj, hle⟩ := h'.exists_le_rescale hi
      exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨hi, hle⟩⟩
    calc
      (t'.card : NNReal)
          ≤ ((Finset.biUnion h'.parent (fun j => t'.filter (fun i => Q' j i))).card : NNReal) :=
            Nat.cast_le.mpr (Finset.card_le_card hcover)
      _ ≤ ∑ j ∈ h'.parent, ((t'.filter (fun i => Q' j i)).card : NNReal) := by
            exact_mod_cast Finset.card_biUnion_le (s := h'.parent)
              (t := fun j => t'.filter (fun i => Q' j i))
      _ ≤ ∑ _j ∈ h'.parent, (Cu * h'.branchingN) :=
            Finset.sum_le_sum fun j hj => by simpa only [hQ'] using h'.card_filter_le hj
      _ = Cu * (h'.parent.card : NNReal) * h'.branchingN := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hFnum_R : (F : ℝ) ≤ (Cu : ℝ) ^ 2 * (h.branchingN : ℝ) := by
    exact_mod_cast card_fibreIndex_le_mul_branchingN_atScale h i₀
  have hPlower_R : (h.parent.card : ℝ) * (h.branchingN : ℝ) ≤ (Cu : ℝ) ^ 2 * (t.card : ℝ) := by
    exact_mod_cast hPlower
  have ht'upper_R : (t'.card : ℝ) ≤ (Cu : ℝ) * (h'.parent.card : ℝ) * (h'.branchingN : ℝ) := by
    exact_mod_cast ht'upper
  have hN'den_R : (h'.branchingN : ℝ) ≤ (Cu : ℝ) * (G : ℝ) := by
    exact_mod_cast branchingN_le_mul_card_fibreIndex_atScale h' hi₀
  by_cases hP : (h.parent.card : ℝ) = 0
  · have ht_empty : t = ∅ := by
      rw [← Finset.card_eq_zero]
      by_contra hc
      obtain ⟨i, hi⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
      obtain ⟨j, hj, _⟩ := h.exists_le_rescale hi
      simp [Finset.card_eq_zero.mp (by exact_mod_cast hP : h.parent.card = 0)] at hj
    have hF_zero : (F : ℝ) = 0 := by
      rw [hF, ht_empty]
      simp [fibreIndex, Kakeya.familyIn]
    rw [hF_zero]
    exact mul_nonneg (mul_nonneg (pow_nonneg hCu_nonneg 6) hA_nonneg) (Nat.cast_nonneg G)
  · have hCu2 : (0 : ℝ) ≤ (Cu : ℝ) ^ 2 := pow_nonneg hCu_nonneg 2
    have hPpos : 0 < (h.parent.card : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hP)
    have hcancel : (h.branchingN : ℝ) ≤ (Cu : ℝ) ^ 4 * A * (G : ℝ) := by
      refine (mul_le_mul_iff_of_pos_left hPpos).mp ?_
      calc
        (h.parent.card : ℝ) * (h.branchingN : ℝ) ≤ (Cu : ℝ) ^ 2 * (t.card : ℝ) := hPlower_R
        _ ≤ (Cu : ℝ) ^ 2 * (A * (t'.card : ℝ)) := mul_le_mul_of_nonneg_left hA hCu2
        _ ≤ (Cu : ℝ) ^ 2 * (A * ((Cu : ℝ) * (h'.parent.card : ℝ) * (h'.branchingN : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht'upper_R hA_nonneg) hCu2
        _ ≤ (Cu : ℝ) ^ 2 * (A * ((Cu : ℝ) * (h.parent.card : ℝ) * ((Cu : ℝ) * (G : ℝ)))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (mul_le_mul (mul_le_mul_of_nonneg_left hparent hCu_nonneg) hN'den_R
                (h'.branchingN).coe_nonneg (mul_nonneg hCu_nonneg (Nat.cast_nonneg _)))
              hA_nonneg) hCu2
        _ = (h.parent.card : ℝ) * ((Cu : ℝ) ^ 4 * A * (G : ℝ)) := by ring
    calc
      (F : ℝ) ≤ (Cu : ℝ) ^ 2 * (h.branchingN : ℝ) := hFnum_R
      _ ≤ (Cu : ℝ) ^ 2 * ((Cu : ℝ) ^ 4 * A * (G : ℝ)) := mul_le_mul_of_nonneg_left hcancel hCu2
      _ = (Cu : ℝ) ^ 6 * A * (G : ℝ) := by ring

/-! ### Monotonicity of the uniformity constants -/

/-! ### The per-cut step for the retained side -/

/-- `ε = 1/√N` with `N ≥ 4096` is at most `1/64`.  The companion of
`Kakeya.MultiScaleFac.eps_pos_of_eq_one_div_sqrt`, stated because several grid-side lemmas take the
bound `ε ≤ 1/64` as a hypothesis and every caller derives it from the same two facts. -/
theorem eps_le_one_div_64_of_eq_one_div_sqrt {N : ℕ} (hN : 4096 ≤ N) {ε : ℝ}
    (hε : ε = 1 / Real.sqrt (N : ℝ)) : ε ≤ 1 / 64 := by
  have hN' : (64 : ℝ) ^ 2 ≤ (N : ℝ) := by
    rw [show (64 : ℝ) ^ 2 = 4096 by norm_num]; exact_mod_cast hN
  rw [hε]
  exact one_div_le_one_div_of_le (by norm_num) ((Real.le_sqrt' (by norm_num)).mpr hN')

/-- **A block of length at least two admits a cut with `⌈εL⌉` to spare on both sides**, when
`ε ≤ 1/64`.

This is the arithmetic behind `margin_add_margin_le`: for `L ≤ 64` the ceiling is `1` and `2 ≤ L`;
for `L > 64` it is at most `L/64 + 1`, and `2 (L/64 + 1) ≤ L`. -/
private theorem two_mul_ceil_le_of_le_one_div_64 {ε : ℝ} (hεpos : 0 < ε) (hε64 : ε ≤ 1 / 64)
    {L : ℕ} (hL : 2 ≤ L) : 2 * ⌈ε * (L : ℝ)⌉₊ ≤ L := by
  have hLnonneg : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hkey : (64 : ℝ) * (⌈ε * (L : ℝ)⌉₊ : ℝ) < (L : ℝ) + 64 := by
    have hlt : (⌈ε * (L : ℝ)⌉₊ : ℝ) < ε * (L : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    linarith [mul_le_mul_of_nonneg_right hε64 hLnonneg]
  have hnat : 64 * ⌈ε * (L : ℝ)⌉₊ < L + 64 := by exact_mod_cast hkey
  omega

/-- **The margin fits twice inside one long block.**  This is what lets the vacuous branch of
`exists_refined_cut_core` exhibit a cut at `⌈ε(b-a)⌉` to spare on both sides. -/
private theorem margin_add_margin_le {ε : ℝ} (hεpos : 0 < ε) (hε64 : ε ≤ 1 / 64)
    {N a b : ℕ} (hab : a < b) (hceil1 : 1 ≤ ⌈ε * (N : ℝ)⌉₊)
    (hlong' : ⌈ε * (N : ℝ)⌉₊ + a < b) :
    a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b := by
  have hab2 : 2 ≤ b - a := by omega
  have htwice : 2 * ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b - a := by
    rw [← Nat.cast_sub hab.le]
    exact two_mul_ceil_le_of_le_one_div_64 hεpos hε64 hab2
  omega

/-! ### The stopping margin `⌈ε ⌈ε M⌉⌉`

Both halves of the multiscale factorization place their cuts at distance at least the stopping
margin `w = ⌈ε ⌈ε M⌉⌉` from the ends of the block being cut, and both need the same handful of
ceiling estimates about it.  They are collected here, in the module both halves import, so that
there is a single copy.  The `KT` namespace is historical: these facts are stated once and used by
half (A) and by the Katz–Tao half alike. -/

/-- **The stopping margin is positive** on a nonempty grid. -/
theorem KT.stoppingMargin_pos {ε : ℝ} (hεpos : 0 < ε) {M : ℕ} (hM : 0 < M) :
    0 < ⌈ε * ((⌈ε * (M : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ :=
  Nat.ceil_pos.mpr (mul_pos hεpos
    (Nat.cast_pos.mpr (Nat.ceil_pos.mpr (mul_pos hεpos (Nat.cast_pos.mpr hM)))))

/-- **The stopping margin does not exceed the grid length**, since `ε ≤ 1` and each ceiling is
therefore bounded by its own argument. -/
theorem KT.stoppingMargin_le {ε : ℝ} (hεpos : 0 < ε) (hε1 : ε ≤ 1) (M : ℕ) :
    ⌈ε * ((⌈ε * (M : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ ≤ M := by
  have hεnonneg : 0 ≤ ε := le_of_lt hεpos
  have h : ∀ n : ℕ, ⌈ε * (n : ℝ)⌉₊ ≤ n := fun n =>
    Nat.ceil_le.mpr (by linarith [mul_le_mul_of_nonneg_right hε1 (Nat.cast_nonneg (α := ℝ) n)])
  exact (h _).trans (h M)

/-- **The real-valued form of the margin bound `M ≤ w N`.**  Both ceilings dominate their
arguments, so `w ≥ ε ⌈ε M⌉ ≥ ε² M`; multiplying by `N > 0` and using `ε² N = 1` gives `w N ≥ M`.
The cast back to `ℕ` is `KT.le_mul_stoppingMargin`. -/
private theorem KT.le_mul_stoppingMargin_real {ε : ℝ} (hεpos : 0 < ε) {N : ℕ}
    (hεN : ε ^ 2 * (N : ℝ) = 1) (M : ℕ) :
    (M : ℝ) ≤ ((⌈ε * ((⌈ε * (M : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) * (N : ℝ) := by
  have h4 : ε ^ 2 * (M : ℝ) ≤ ((⌈ε * ((⌈ε * (M : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left (Nat.le_ceil (ε * (M : ℝ))) (le_of_lt hεpos)
    have h2 := Nat.le_ceil (ε * ((⌈ε * (M : ℝ)⌉₊ : ℕ) : ℝ))
    linarith
  calc
    (M : ℝ) = (ε ^ 2 * (M : ℝ)) * (N : ℝ) := by rw [mul_right_comm, hεN, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg N)

/-- **The grid length is at most the margin times the step budget**, which is the hypothesis
`Kakeya.MultiScaleFac.exists_maximal_cuts_abstract_state_margin` needs, and which holds for every
grid length precisely because `ε² N = 1`. -/
theorem KT.le_mul_stoppingMargin {ε : ℝ} (hεpos : 0 < ε) {N : ℕ}
    (hεN : ε ^ 2 * (N : ℝ) = 1) (M : ℕ) :
    M ≤ ⌈ε * ((⌈ε * (M : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ * N := by
  exact_mod_cast KT.le_mul_stoppingMargin_real hεpos hεN M

/-- **A long block accommodates the stopping margin.** -/
theorem KT.stoppingMargin_le_ceil_of_isLongBlock {ε : ℝ} (hεpos : 0 < ε) {M a b : ℕ}
    (hlong : IsLongBlock M ε a b) :
    ⌈ε * ((⌈ε * (M : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ ≤ ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ := by
  unfold IsLongBlock at hlong
  refine Nat.ceil_le_ceil (mul_le_mul_of_nonneg_left ?_ hεpos.le)
  have hk_lt : (((⌈ε * (M : ℝ)⌉₊ : ℕ) : ℝ) + (a : ℝ)) < (b : ℝ) := by exact_mod_cast hlong
  linarith

/-- **A long block has room for two stopping margins.**  The margin `w = ⌈ε⌈εM⌉⌉` is at most `ε`
times the length `⌈εM⌉` that a block must exceed to be long, rounded up, so two of them fit inside
a long block with room to spare once `ε ≤ 1/64`. -/
theorem KT.two_mul_stoppingMargin_le_of_isLongBlock {ε : ℝ} (hεpos : 0 < ε) (hε64 : ε ≤ 1 / 64)
    {M a b : ℕ} (hlong : IsLongBlock M ε a b) :
    a + ⌈ε * ((⌈ε * (M : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ + ⌈ε * ((⌈ε * (M : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ ≤ b := by
  set k : ℕ := ⌈ε * (M : ℝ)⌉₊ with hk
  have hlong' : k + a < b := by simpa [IsLongBlock, hk] using hlong
  have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have key : 2 * ⌈ε * (k : ℝ)⌉₊ < k + 2 := by
    have hR : (2 : ℝ) * (⌈ε * (k : ℝ)⌉₊ : ℕ) < (k : ℝ) + 2 := by
      linarith [Nat.ceil_lt_add_one (a := ε * (k : ℝ)) (by positivity),
        mul_le_mul_of_nonneg_right hε64 hknn]
    exact_mod_cast hR
  omega

/-- **The polylogarithmic base `1 - log δ` is at least one** for `0 < δ ≤ 1`. -/
theorem KT.one_le_one_sub_log {δ' : NNReal} (hδ : 0 < δ') (hδ1 : (δ' : ℝ) ≤ 1) :
    (1 : ℝ) ≤ 1 - Real.log (δ' : ℝ) := by
  linarith [Real.log_nonpos (NNReal.coe_pos.mpr hδ).le hδ1]

/-- **Folding the initial refinement into the level count.** -/
theorem KT.hoisted_card_accum {x y z Pi G : ℝ} (hG0 : 0 ≤ G) (_hPi0 : 0 ≤ Pi)
    (hPiG : Pi ≤ G) (hy : 0 ≤ y) (_hz : 0 ≤ z) (m : ℕ) (h1 : x ≤ Pi * y)
    (h2 : y ≤ G ^ m * z) : x ≤ G ^ (m + 1) * z := by
  calc x ≤ Pi * y := h1
    _ ≤ G * y := mul_le_mul_of_nonneg_right hPiG hy
    _ ≤ G * (G ^ m * z) := mul_le_mul_of_nonneg_left h2 hG0
    _ = G ^ (m + 1) * z := by ring

/-! ### The grid-length-dependent constants of the per-cut step -/

/-- **The hoisted per-cut block constant is at least one.** -/
private theorem one_le_hoisted_coef {A : ℝ} (hA : 1 ≤ A) (X : NNReal) :
    (1 : NNReal) ≤ 2 * Real.toNNReal A * max 1 X := by
  have hA' : (1 : NNReal) ≤ Real.toNNReal A := by
    rw [← Real.toNNReal_one]
    exact Real.toNNReal_le_toNNReal hA
  exact one_le_mul (one_le_mul one_le_two hA') (le_max_left 1 X)

/-- **The grid-length-dependent per-cut constant is a power of a fixed constant.**  Since
`2(m+1) ≤ 2^{m+1}`, the factor `2(m+1)A^{m+1}` produced by the per-cut step at grid length `m` is
at most `(2A)^{m+1}`, and the grid-length-independent factors are absorbed by raising their maximum
with `1` to the same power. -/
private theorem coef_le_pow_succ {A : ℝ} (hA : 1 ≤ A) (Cv Cu₀ volfac Crest : NNReal) (m : ℕ) :
    Cv ^ 6 * Real.toNNReal ((2 : ℝ) * (m + 1 : ℝ) * A ^ (m + 1)) * Cu₀ * volfac * Crest
      ≤ (2 * Real.toNNReal A * max 1 (Cv ^ 6 * Cu₀ * volfac * Crest)) ^ (m + 1) := by
  have hA0 : (0 : ℝ) ≤ A := zero_le_one.trans hA
  have hT : Real.toNNReal ((2 : ℝ) * (m + 1 : ℝ) * A ^ (m + 1))
      ≤ (2 * Real.toNNReal A) ^ (m + 1) := by
    have hmle : ((m : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ m := by
      exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_two_pow_self : m < 2 ^ m))
    have hstep2 : (2 : ℝ) * (m + 1 : ℝ) * A ^ (m + 1) ≤ (2 * A) ^ (m + 1) := by
      rw [mul_pow, pow_succ' (2 : ℝ) m]
      exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hA0 (m + 1))
    refine (Real.toNNReal_le_toNNReal hstep2).trans_eq ?_
    rw [Real.toNNReal_pow (mul_nonneg (by norm_num) hA0),
      Real.toNNReal_mul (by norm_num : (0 : ℝ) ≤ (2 : ℝ))]
    norm_num
  set Y : NNReal := Cv ^ 6 * Cu₀ * volfac * Crest with hY
  calc
    Cv ^ 6 * Real.toNNReal ((2 : ℝ) * (m + 1 : ℝ) * A ^ (m + 1)) * Cu₀ * volfac * Crest
        = Real.toNNReal ((2 : ℝ) * (m + 1 : ℝ) * A ^ (m + 1)) * Y := by rw [hY]; ring
    _ ≤ (2 * Real.toNNReal A) ^ (m + 1) * (max 1 Y) ^ (m + 1) :=
        mul_le_mul' hT ((le_max_right 1 Y).trans (le_self_pow (le_max_left 1 Y) (by omega)))
    _ = (2 * Real.toNNReal A * max 1 Y) ^ (m + 1) := (mul_pow _ _ _).symm

/-- **The per-cut step for the retained side** (blueprint `lem:blockRestrictStep_refined`).  From
the passing side `P ⊆ t` of the per-node split test, an aligned interior cut index `c` and a subset
`P' ⊆ P` carrying the fine half `(c,b)` at the next exponent at *every* node; the coarse half
`(a,c)` is `exists_blockRestrictStep` verbatim, and re-uniformizing `P'` gives the next state `t'`.
This is the form with **every constant supplied from outside**. -/
private theorem exists_refined_cut_core (N : ℕ) (hN : 16 ≤ N)
    {ε : ℝ} (hεpos : 0 < ε) (hε64 : ε ≤ 1 / 64)
    (M₀ : ℝ) (hM₀ : 1 ≤ M₀) (K₀ : ℕ) (Cu₀ Cv Crest C'' : NNReal)
    (hCu0Cv : Cu₀ ≤ Cv) (hCrest : 1 ≤ Crest)
    (hblockRestrict : ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 →
      δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      UniformTubeSet s T N (uniformTubeSetCuOf (E := E) Cv) →
      ComparableFibreCounts s T (gridScales δ N) (uniformTubeSetCuOf (E := E) Cv) →
      BlockRestrictStep s T N ε Crest)
    (hunif : ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s t : Finset ι) (T : ι → Tube δ E), t ⊆ s →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (↑s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      ∀ (Cs : NNReal) (𝒢 : GridUniform s T N Cs),
      ∃ t' ⊆ t,
        (t.card : ℝ) ≤ M₀ * (1 - Real.log (δ : ℝ)) ^ K₀ * (t'.card : ℝ) ∧
          ∃ 𝒢' : GridUniform t' T N Cu₀,
            (∀ k (hk : k ≤ N), (𝒢'.uniformAt k hk).parent ⊆ (𝒢.uniformAt k hk).parent) ∧
            (∀ k, 𝒢'.cover.tube k = 𝒢.cover.tube k) ∧
            ComparableFibreCounts t' T (gridScales δ N) Cu₀ ∧
            ComparableFibreCountsInflated t' T (gridScales δ N) Cu₀)
    (hC'' : Cv ^ 6 * Real.toNNReal ((2 : ℝ) * (N + 1 : ℝ) * M₀) * Cu₀ *
      (Tube.volume_le.C (Module.finrank ℝ E) / Tube.le_volume.c (Module.finrank ℝ E)) *
      Crest ≤ C'') :
    ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s t : Finset ι) (T : ι → Tube δ E), t ⊆ s →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (↑s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      Nonempty (GridUniform t T N Cv) →
      ComparableFibreCounts t T (gridScales δ N) Cv →
      ∀ (C : NNReal) (ζ ζ' : ℝ), 0 ≤ ζ → ζ ≤ ε * ζ' → ζ' ≤ ε →
      ∀ a b : ℕ, b ≤ N → IsLongBlock N ε a b →
      BlockFrostman t T N C ζ a b →
      t.card ≤ 2 * (passingNodes t T N C ε ζ' a b).card →
      ∃ c : ℕ, a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c ∧
          c + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b ∧ ∃ t' ⊆ t,
        (t.card : ℝ) ≤ (2 : ℝ) * (N + 1 : ℝ) * M₀ * (1 - Real.log (δ : ℝ)) ^ K₀ *
            (t'.card : ℝ) ∧
          Nonempty (GridUniform t' T N Cv) ∧
          ComparableFibreCounts t' T (gridScales δ N) Cv ∧
          ComparableFibreCountsInflated t' T (gridScales δ N) Cv ∧
          BlockFrostman t' T N
            (C'' * Real.toNNReal ((1 - Real.log (δ : ℝ)) ^ K₀) * C) ζ' a c ∧
          BlockFrostman t' T N
            (C'' * Real.toNNReal ((1 - Real.log (δ : ℝ)) ^ K₀) * C) ζ' c b ∧
          ∀ (C₂ : NNReal) (ζ₂ : ℝ) (a₂ b₂ : ℕ), 0 ≤ ζ₂ → a₂ ≤ b₂ → b₂ ≤ N →
            BlockFrostman t T N C₂ ζ₂ a₂ b₂ →
            BlockFrostman t' T N
              (C'' * Real.toNNReal ((1 - Real.log (δ : ℝ)) ^ K₀) * C₂) ζ₂ a₂ b₂ := by
  classical
  let volfac : NNReal :=
    Tube.volume_le.C (Module.finrank ℝ E) / Tube.le_volume.c (Module.finrank ℝ E)
  let coef : NNReal :=
    Cv ^ 6 * Real.toNNReal ((2 : ℝ) * (N + 1 : ℝ) * M₀) * Cu₀
  intro ι δ hδ hδ1 hδ0 s t T hts hball hED hGrid hComp C ζ ζ' hζ hζζ' hζ'ε a b hbN hlong
    hfrost hpass
  · let P := passingNodes t T N C ε ζ' a b
    have hPsplit : ∀ i₀ ∈ P, NodeSplitTest t T N C ε ζ' a b i₀ := fun i₀ hi₀ =>
      (Finset.mem_filter.mp hi₀).2
    have hpassP : t.card ≤ 2 * P.card := hpass
    have hlong' : ⌈ε * (N : ℝ)⌉₊ + a < b := by simpa [IsLongBlock] using hlong
    have hab : a < b := by omega
    by_cases ht : t = ∅
    · subst ht
      have hceil1 : 1 ≤ ⌈ε * (N : ℝ)⌉₊ :=
        Nat.ceil_pos.mpr (mul_pos hεpos (by exact_mod_cast (by omega : 0 < N)))
      refine ⟨a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊, le_rfl,
        margin_add_margin_le hεpos hε64 hab hceil1 hlong',
        ∅, Finset.Subset.refl _, by simp, hGrid, hComp, ?_, ?_, ?_, ?_⟩
      · intro ρ hρ i₀ hi₀; simp at hi₀
      · intro i₀ hi₀; simp at hi₀
      · intro i₀ hi₀; simp at hi₀
      · intro _ _ _ _ _ _ _ _ i₀ hi₀; simp at hi₀
    · have hPne : P.Nonempty := by
        by_contra hP0
        rw [Finset.not_nonempty_iff_eq_empty] at hP0
        exact ht (Finset.card_eq_zero.mp (by rw [hP0] at hpassP; simpa using hpassP))
      obtain ⟨c, hcab1, hcab2, P', hP'P, hP'ne, hPcard, hfine⟩ :=
        exists_common_cut_of_forall_nodeSplitTest hbN hPne hPsplit
      have hm1 : 1 ≤ ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ := by
        have hlt : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
        exact Nat.ceil_pos.mpr (mul_pos hεpos (by linarith))
      have hac : a < c := by omega
      have hcb : c < b := by omega
      have hcb' : c ≤ b := le_of_lt hcb
      have hcN : c ≤ N := le_trans hcb' hbN
      have hζ'0 : 0 ≤ ζ' := (mul_nonneg_iff_of_pos_left hεpos).mp (hζ.trans hζζ')
      have htball : ∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1 := fun i hi =>
        hball i (hts hi)
      rcases hGrid with ⟨𝒢⟩
      have hbr : BlockRestrictStep t T N ε Crest :=
        hblockRestrict hδ hδ1 hδ0 t T htball 𝒢.toUniformTubeSet
          (hComp.mono (le_max_left _ _))
      have hcoarse_t : BlockFrostman t T N (Crest * C) ζ' a c :=
        hbr C ζ ζ' hζ hζζ' a c b hcab1 hcb hbN hfrost
      have hEDt : (↑t : Set ι).Pairwise (fun i j =>
          IsEssentiallyDistinct (T i).carrier (T j).carrier) :=
        Set.Pairwise.mono (Finset.coe_subset.mpr hts) hED
      have hPt : P ⊆ t := Finset.filter_subset _ t
      have hP't : P' ⊆ t := fun i hi => hPt (hP'P hi)
      obtain ⟨t', htt', hPcard', 𝒢', hves, _htube', hComp', hCompInfl⟩ :=
        hunif hδ hδ0 (s := t) (t := P') (T := T) hP't htball hEDt Cv 𝒢
      have htt't : t' ⊆ t := subset_trans htt' hP't
      have hGrid' : Nonempty (GridUniform t' T N Cv) := ⟨𝒢'.mono hCu0Cv⟩
      have hComp'Cv : ComparableFibreCounts t' T (gridScales δ N) Cv :=
        hComp'.mono hCu0Cv
      have hCompInflCv : ComparableFibreCountsInflated t' T (gridScales δ N) Cv :=
        hCompInfl.mono hCu0Cv
      have hA_accum : (t.card : ℝ) ≤
          (2 : ℝ) * (N + 1 : ℝ) * M₀ * (1 - Real.log (δ : ℝ)) ^ K₀ * (t'.card : ℝ) := by
        have h1 : (t.card : ℝ) ≤ 2 * (P.card : ℝ) := by exact_mod_cast hpassP
        have h2 : (P.card : ℝ) ≤ (N + 1 : ℝ) * (P'.card : ℝ) := by exact_mod_cast hPcard
        calc
          (t.card : ℝ) ≤ 2 * (N + 1 : ℝ) * (P'.card : ℝ) := by rw [mul_assoc]; linarith
          _ ≤ 2 * (N + 1 : ℝ) * (M₀ * (1 - Real.log (δ : ℝ)) ^ K₀ * (t'.card : ℝ)) :=
              mul_le_mul_of_nonneg_left hPcard' (by positivity)
          _ = 2 * (N + 1 : ℝ) * M₀ * (1 - Real.log (δ : ℝ)) ^ K₀ * (t'.card : ℝ) := by ring
      have hlogδ : Real.log (δ : ℝ) ≤ 0 := Real.log_nonpos (by positivity) hδ1
      have hone_le : (1 : ℝ) ≤ 1 - Real.log (δ : ℝ) := by linarith
      set poly : NNReal := Real.toNNReal ((1 - Real.log (δ : ℝ)) ^ K₀) with hpoly_def
      set Aδ : NNReal :=
        Real.toNNReal ((2 : ℝ) * (N + 1 : ℝ) * M₀ * (1 - Real.log (δ : ℝ)) ^ K₀) with hAδ_def
      set coefδ : NNReal := Cv ^ 6 * Aδ * Cu₀ with hcoefδ_def
      have hAδ_le : Aδ ≤ Real.toNNReal ((2 : ℝ) * (N + 1 : ℝ) * M₀) * poly := by
        rw [hAδ_def, hpoly_def, ← Real.toNNReal_mul (by positivity)]
      have hcoefδ_le : coefδ ≤ coef * poly := by
        rw [hcoefδ_def]
        calc
          Cv ^ 6 * Aδ * Cu₀
              ≤ Cv ^ 6 * (Real.toNNReal ((2 : ℝ) * (N + 1 : ℝ) * M₀) * poly) * Cu₀ := by
                gcongr
          _ = coef * poly := by dsimp [coef]; ring
      have hcard_gen : ∀ (k : ℕ) (hk : k ≤ N) (i₀ : ι), i₀ ∈ t' →
          ((fibreIndex t T δ (gridScale δ N k) i₀).card : ENNReal) ≤
            (coefδ : ENNReal) * ((fibreIndex t' T δ (gridScale δ N k) i₀).card : ENNReal) := by
        intro k hk i₀ hi₀
        let A : ℝ := (2 : ℝ) * (N + 1 : ℝ) * M₀ * (1 - Real.log (δ : ℝ)) ^ K₀
        have hNpos : 0 < N := by omega
        have hδρ : δ ≤ gridScale δ N k := by
          calc
            δ = gridScale δ N N := (gridScale_self δ hNpos).symm
            _ ≤ gridScale δ N k := gridScale_antitone hδ hδ1 N hk
        have hpow1 : (1 : ℝ) ≤ (1 - Real.log (δ : ℝ)) ^ K₀ := one_le_pow₀ hone_le
        have h2N1 : (1 : ℝ) ≤ (2 : ℝ) * (N + 1 : ℝ) := by
          have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
          linarith
        have hA1 : 1 ≤ A := by
          have hprod : (1 : ℝ) ≤ (2 : ℝ) * (N + 1 : ℝ) * (M₀ : ℝ) := by nlinarith
          calc
            (1 : ℝ) = 1 * 1 := by norm_num
            _ ≤ ((2 : ℝ) * (N + 1 : ℝ) * (M₀ : ℝ)) * ((1 - Real.log (δ : ℝ)) ^ K₀) :=
              mul_le_mul hprod hpow1 zero_le_one (by linarith)
            _ = A := by dsimp [A]
        have hA_nonneg : 0 ≤ A := zero_le_one.trans hA1
        have hAcum : (t.card : ℝ) ≤ A * (t'.card : ℝ) := by
          simpa [A] using hA_accum
        let h : Tube.IsUniformAtScale t T (gridScale δ N k) Cv := 𝒢.uniformAt k hk
        let h' : Tube.IsUniformAtScale t' T (gridScale δ N k) Cv := (𝒢'.mono hCu0Cv).uniformAt k hk
        have hparent : (h'.parent.card : ℝ) ≤ (h.parent.card : ℝ) := by
          have hsub : h'.parent ⊆ h.parent := hves k hk
          exact_mod_cast (Finset.card_le_card hsub)
        have hcard4 : ((fibreIndex t T δ (gridScale δ N k) i₀).card : ℝ) ≤
            (Cv : ℝ) ^ 6 * A * ((fibreIndex t' T δ (4 * gridScale δ N k) i₀).card : ℝ) :=
          card_fibreIndex_le_mul_of_card_le_four h h' htt't hδρ hparent hA1 hAcum hi₀
        have hdef : ((fibreIndex t' T δ (4 * gridScale δ N k) i₀).card : NNReal) ≤
            Cu₀ * ((fibreIndex t' T δ (gridScale δ N k) i₀).card : NNReal) :=
          hCompInfl (gridScale δ N k) (gridScale_mem_gridScales δ hk) i₀ hi₀ i₀ hi₀
        have hdefR : ((fibreIndex t' T δ (4 * gridScale δ N k) i₀).card : ℝ) ≤
            (Cu₀ : ℝ) * ((fibreIndex t' T δ (gridScale δ N k) i₀).card : ℝ) := by
          exact_mod_cast hdef
        have hfac : 0 ≤ (Cv : ℝ) ^ 6 * A :=
          mul_nonneg (pow_nonneg (by positivity) 6) hA_nonneg
        have hRb : ((fibreIndex t T δ (gridScale δ N k) i₀).card : ℝ) ≤
            (Cv : ℝ) ^ 6 * A * (Cu₀ : ℝ) * ((fibreIndex t' T δ (gridScale δ N k) i₀).card : ℝ) := by
          calc
            ((fibreIndex t T δ (gridScale δ N k) i₀).card : ℝ) ≤
                (Cv : ℝ) ^ 6 * A * ((fibreIndex t' T δ (4 * gridScale δ N k) i₀).card : ℝ) := hcard4
            _ ≤ (Cv : ℝ) ^ 6 * A
                  * ((Cu₀ : ℝ) * ((fibreIndex t' T δ (gridScale δ N k) i₀).card : ℝ)) :=
                mul_le_mul_of_nonneg_left hdefR hfac
            _ = (Cv : ℝ) ^ 6 * A * (Cu₀ : ℝ)
                  * ((fibreIndex t' T δ (gridScale δ N k) i₀).card : ℝ) := by ring
        have hAδR : (Aδ : ℝ) = A := by
          rw [hAδ_def]
          exact Real.coe_toNNReal _ hA_nonneg
        have hcoefδR : (coefδ : ℝ) = (Cv : ℝ) ^ 6 * A * (Cu₀ : ℝ) := by
          dsimp [coefδ]
          rw [hAδR]
        have hR : ((fibreIndex t T δ (gridScale δ N k) i₀).card : ℝ) ≤
            (coefδ : ℝ) * ((fibreIndex t' T δ (gridScale δ N k) i₀).card : ℝ) := by
          simpa [hcoefδR] using hRb
        have hH : ((fibreIndex t T δ (gridScale δ N k) i₀).card : NNReal) ≤
            coefδ * ((fibreIndex t' T δ (gridScale δ N k) i₀).card : NNReal) := by
          exact_mod_cast hR
        exact ENNReal.coe_le_coe.mpr hH
      have hfine' : BlockFrostman t' T N (coefδ * volfac * C) ζ' c b := by
        intro i₀ hi₀
        have hi₀P' : i₀ ∈ P' := htt' hi₀
        have hAt : BlockFrostmanAt t T N C ζ' c b i₀ := hfine i₀ hi₀P'
        have hcard : ((fibreIndex t T δ (gridScale δ N c) i₀).card : ENNReal) ≤
            (coefδ : ENNReal) * ((fibreIndex t' T δ (gridScale δ N c) i₀).card : ENNReal) :=
          hcard_gen c hcN i₀ hi₀
        exact BlockFrostmanAt.of_subfamily hδ hδ1 (a := c) (b := b) hcb' hbN htt't hi₀
          hcard hAt
      have hcoarse' : BlockFrostman t' T N (coefδ * volfac * (Crest * C)) ζ' a c := by
        intro i₀ hi₀
        have hAt : BlockFrostmanAt t T N (Crest * C) ζ' a c i₀ := hcoarse_t i₀ (htt't hi₀)
        have hcard : ((fibreIndex t T δ (gridScale δ N a) i₀).card : ENNReal) ≤
            (coefδ : ENNReal) * ((fibreIndex t' T δ (gridScale δ N a) i₀).card : ENNReal) :=
          hcard_gen a (le_trans (le_of_lt hac) hcN) i₀ hi₀
        exact BlockFrostmanAt.of_subfamily hδ hδ1 (a := a) (b := c) (le_of_lt hac) hcN htt't
          hi₀ hcard hAt
      have hbase : coef * volfac * Crest ≤ C'' := hC''
      have hcv : coefδ * volfac ≤ C'' * poly := by
        calc
          coefδ * volfac ≤ coef * poly * volfac := by gcongr
          _ = coef * volfac * 1 * poly := by ring
          _ ≤ coef * volfac * Crest * poly := by gcongr
          _ ≤ C'' * poly := by gcongr
      have hCfine : coefδ * volfac * C ≤ C'' * poly * C := by gcongr
      have hCcoarse : coefδ * volfac * (Crest * C) ≤ C'' * poly * C := by
        have h1 : coefδ * volfac * Crest ≤ C'' * poly := by
          calc
            coefδ * volfac * Crest ≤ coef * poly * volfac * Crest := by gcongr
            _ = coef * volfac * Crest * poly := by ring
            _ ≤ C'' * poly := by gcongr
        calc
          coefδ * volfac * (Crest * C) = coefδ * volfac * Crest * C := by ring
          _ ≤ C'' * poly * C := by gcongr
      have hfine0 : BlockFrostman t' T N
          (C'' * Real.toNNReal ((1 - Real.log (δ : ℝ)) ^ K₀) * C) ζ' c b :=
        hfine'.mono hδ hδ1 hCfine hζ'0 le_rfl hcb'
      have hcoarse0 : BlockFrostman t' T N
          (C'' * Real.toNNReal ((1 - Real.log (δ : ℝ)) ^ K₀) * C) ζ' a c :=
        hcoarse'.mono hδ hδ1 hCcoarse hζ'0 le_rfl hac.le
      have hdescend_gen : ∀ (C₂ : NNReal) (ζ₂ : ℝ) (a₂ b₂ : ℕ), 0 ≤ ζ₂ → a₂ ≤ b₂ → b₂ ≤ N →
          BlockFrostman t T N C₂ ζ₂ a₂ b₂ →
          BlockFrostman t' T N (C'' * poly * C₂) ζ₂ a₂ b₂ := by
        intro C₂ ζ₂ a₂ b₂ hζ₂ hab₂ hb₂N hBF
        have hstep : BlockFrostman t' T N (coefδ * volfac * C₂) ζ₂ a₂ b₂ := by
          intro i₀ hi₀
          have hAt : BlockFrostmanAt t T N C₂ ζ₂ a₂ b₂ i₀ := hBF i₀ (htt't hi₀)
          exact BlockFrostmanAt.of_subfamily hδ hδ1 hab₂ hb₂N htt't hi₀
            (hcard_gen a₂ (le_trans hab₂ hb₂N) i₀ hi₀) hAt
        have hC2 : coefδ * volfac * C₂ ≤ C'' * poly * C₂ := by gcongr
        exact hstep.mono hδ hδ1 hC2 hζ₂ le_rfl hab₂
      exact ⟨c, hcab1, hcab2,
        ⟨t', htt't, hA_accum, hGrid', hComp'Cv, hCompInflCv, hcoarse0, hfine0,
        hdescend_gen⟩⟩

/-- **The per-cut step with every constant quantified before the grid length.**  The hoisted form of
`exists_refined_cut_core`: the base `A` of the cardinality loss, its polylogarithmic exponent `K`,
the uniformity constant `Cv`, and the base `C''` and exponent `K''` of the output block constant are
all chosen **before** the grid length `N` and before `ε`, at the price of writing the grid-length
dependence of both losses out in full. -/
theorem exists_refined_cut_hoisted (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ (A : ℝ) (K K'' : ℕ) (Cv C'' : NNReal), 1 ≤ A ∧ Cu ≤ Cv ∧ 1 ≤ C'' ∧
      ∀ (N : ℕ), 16 ≤ N → ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 64 →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s t : Finset ι) (T : ι → Tube δ E), t ⊆ s →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (↑s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      Nonempty (GridUniform t T N Cv) →
      ComparableFibreCounts t T (gridScales δ N) Cv →
      ∀ (C : NNReal) (ζ ζ' : ℝ), 0 ≤ ζ → ζ ≤ ε * ζ' → ζ' ≤ ε →
      ∀ a b : ℕ, b ≤ N → IsLongBlock N ε a b →
      BlockFrostman t T N C ζ a b →
      t.card ≤ 2 * (passingNodes t T N C ε ζ' a b).card →
      ∃ c : ℕ, a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c ∧
          c + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b ∧ ∃ t' ⊆ t,
        (t.card : ℝ) ≤ (2 : ℝ) * (N + 1 : ℝ) * A ^ (N + 1) *
            (1 - Real.log (δ : ℝ)) ^ (K * (N + 1)) * (t'.card : ℝ) ∧
          Nonempty (GridUniform t' T N Cv) ∧
          ComparableFibreCounts t' T (gridScales δ N) Cv ∧
          ComparableFibreCountsInflated t' T (gridScales δ N) Cv ∧
          BlockFrostman t' T N
            (C'' ^ (N + 1) *
              Real.toNNReal ((1 - Real.log (δ : ℝ)) ^ (K'' * (N + 1))) * C) ζ' a c ∧
          BlockFrostman t' T N
            (C'' ^ (N + 1) *
              Real.toNNReal ((1 - Real.log (δ : ℝ)) ^ (K'' * (N + 1))) * C) ζ' c b ∧
          ∀ (C₂ : NNReal) (ζ₂ : ℝ) (a₂ b₂ : ℕ), 0 ≤ ζ₂ → a₂ ≤ b₂ → b₂ ≤ N →
            BlockFrostman t T N C₂ ζ₂ a₂ b₂ →
            BlockFrostman t' T N
              (C'' ^ (N + 1) *
                Real.toNNReal ((1 - Real.log (δ : ℝ)) ^ (K'' * (N + 1))) * C₂) ζ₂ a₂ b₂ := by
  obtain ⟨A, Kh, Cu₀, hA, hCu₀, hunif⟩ := exists_uniformize_subfamily_hoisted (E := E)
  have hCuCv : Cu ≤ max Cu Cu₀ := le_max_left _ _
  have hCu0Cv : Cu₀ ≤ max Cu Cu₀ := le_max_right _ _
  have hCv : (1 : NNReal) ≤ max Cu Cu₀ := le_trans hCu hCuCv
  obtain ⟨Crest, hCrest, hblockRestrict⟩ :=
    exists_blockRestrictStep (E := E)
      (uniformTubeSetCuOf (E := E) (max Cu Cu₀))
      (le_trans hCv (le_max_left _ _))
  refine ⟨A, Kh, Kh, max Cu Cu₀,
    2 * Real.toNNReal A *
      max 1 ((max Cu Cu₀) ^ 6 * Cu₀ *
        (Tube.volume_le.C (Module.finrank ℝ E) / Tube.le_volume.c (Module.finrank ℝ E)) * Crest),
    hA, hCuCv, one_le_hoisted_coef hA _, ?_⟩
  intro N hN ε hεpos hε64
  refine exists_refined_cut_core N hN hεpos hε64 (A ^ (N + 1)) (one_le_pow₀ hA)
    (Kh * (N + 1)) Cu₀ (max Cu Cu₀) Crest _ hCu0Cv hCrest ?_ ?_ ?_
  · intro ι δ hδ hδ1 hδ0 s T hballs huni hcmp
    exact hblockRestrict N (by omega) hεpos hδ hδ1 hδ0 s T hballs huni hcmp
  · intro ι δ hδ hδ0 s t T hts hballs hEDs Cs 𝒢
    exact hunif N (by omega) hδ hδ0 s t T hts hballs hEDs Cs 𝒢
  · exact coef_le_pow_succ hA _ Cu₀ _ Crest N

/-! ### From the grid test window to the real conclusion window -/

/-- **Rounding a real scale into the grid window, on the `⌈log log 1/δ⌉`-grid** (blueprint
`lem:real_scale_rounding_cost`).  Separating the grid length `M` from the step count `N` gives the
window exponent `(1+2κ)ε` in place of `3ε`, the honest costs `δ^{-3/M}` on the exponent rebase and
`δ^{24/M}` on the anchor transfer — both subpolynomial `Kakeya.MultiScaleFac.scaleGapLoss` — and
`ζ' ≤ 1` in place of `ζ' ≤ ε`. -/
private theorem exists_rounding_grid_index_sharp (hn : Module.finrank ℝ E = 3)
    (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ C : NNReal, 1 ≤ C ∧
      ∀ (M N : ℕ), 16 ≤ M → 0 < N → (3 : ℝ) * (N : ℝ) ≤ (M : ℝ) →
      ∀ {ε κ : ℝ}, ε = 1 / Real.sqrt (N : ℝ) → 0 < κ → (N : ℝ) ≤ κ * (M : ℝ) →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) < 1 → δ ≤ (16 : NNReal) ^ (-(M : ℝ)) →
      ∀ (t : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      UniformTubeSet t T M Cu →
      ∀ ζ' : ℝ, 0 ≤ ζ' → ζ' ≤ 1 →
      ∀ a b : ℕ, b ≤ M → IsLongBlock M ε a b →
      ∀ F ⊆ t, ∀ ρ : NNReal, 0 < ρ →
        (gridScale δ M b : ℝ) *
            ((gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)) ^ ((1 + 2 * κ) * ε) ≤ (ρ : ℝ) →
        (ρ : ℝ) ≤ (gridScale δ M a : ℝ) *
            ((gridScale δ M b : ℝ) / (gridScale δ M a : ℝ)) ^ ((1 + 2 * κ) * ε) →
      ∃ c : ℕ, 3 ≤ c ∧
        (gridScale δ M c : ℝ) ≤ (ρ : ℝ) ∧ (ρ : ℝ) ≤ (gridScale δ M (c - 3) : ℝ) ∧
        a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c ∧ c + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b ∧
        ((ρ : ℝ) / (gridScale δ M b : ℝ)) ^ ζ'
            ≤ (δ : ℝ) ^ (-(3 / (M : ℝ))) *
                ((gridScale δ M c : ℝ) / (gridScale δ M b : ℝ)) ^ ζ' ∧
        ∀ i₀ ∈ F,
          ENNReal.ofReal ((δ : ℝ) ^ (24 / (M : ℝ))) *
              ConvexSpaceBody.frostmanConstant (fibreIndex t T δ (gridScale δ M c) i₀)
                (fibreBodies T (gridScale δ M b))
                ((T i₀).rescale (2 * gridScale δ M c)).toConvexSpaceBody
            ≤ (C : ENNReal) *
                ConvexSpaceBody.frostmanConstant (fibreIndex t T δ ρ i₀)
                  (fibreBodies T (gridScale δ M b))
                  ((T i₀).rescale (2 * ρ)).toConvexSpaceBody := by
  obtain ⟨C, hC1, htransfer⟩ := frostmanConstant_fibre_lower_transfer_sharp (E := E) hn Cu hCu
  refine ⟨C, hC1, ?_⟩
  intro M N hM hN hNM ε κ hε hκ hNκM ι δ hδ hδ1 hδ0 t T hball hu ζ' hζ'0 hζ'1 a b hbM hlong F hFt
    ρ hρ hρl hρr
  obtain ⟨c, h3c, hc2b, hadm1, hc1M, hσc_le_ρ, hρ_le_σc3⟩ :=
    exists_admissible_cut_index_sharp hδ hδ1 (by omega : 0 < M) hN hNM hε hκ hNκM hbM hlong hρ
      hρl hρr
  exact ⟨c, h3c, hσc_le_ρ, hρ_le_σc3, hadm1, hc1M,
    ratio_rpow_le_gridScale_ratio_rpow_sharp hδ hδ1.le hM hζ'0 hζ'1 hρ hσc_le_ρ hρ_le_σc3,
    fun i₀ hi₀F => htransfer M hM hδ hδ1.le hδ0 t T hball hu b c hc2b hbM ρ hσc_le_ρ hρ_le_σc3
      i₀ (hFt hi₀F)⟩

/-- **From the grid test window to the real conclusion window, on the `⌈log log 1/δ⌉`-grid.**
Blueprint `lem:grid_to_real_scale_loss`, with the grid length `M` separated from the step count `N`:
the window exponent is `(1+2κ)ε` and the compounded cost of the two roundings is the honest
`δ^{-27/M} = δ^{-3/M} · δ^{-24/M}`, a subpolynomial `Kakeya.MultiScaleFac.scaleGapLoss`. -/
private theorem dividingScales_lower_bound_on_failing_nodes_sharp
    (hn : Module.finrank ℝ E = 3)
    (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ C : NNReal, 1 ≤ C ∧
      ∀ (M N : ℕ), 16 ≤ M → 0 < N → (3 : ℝ) * (N : ℝ) ≤ (M : ℝ) →
      ∀ {ε κ : ℝ}, ε = 1 / Real.sqrt (N : ℝ) → 0 < κ → (N : ℝ) ≤ κ * (M : ℝ) →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) < 1 → δ ≤ (16 : NNReal) ^ (-(M : ℝ)) →
      ∀ (t : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      UniformTubeSet t T M Cu →
      ∀ Ct : NNReal, 1 ≤ Ct →
      ∀ ζ' : ℝ, 0 ≤ ζ' → ζ' ≤ 1 →
      ∀ a b : ℕ, a < b → b ≤ M → IsLongBlock M ε a b →
      ∀ F ⊆ t, (∀ i₀ ∈ F, ¬ NodeSplitTest t T M Ct ε ζ' a b i₀) →
      ∀ ρ : NNReal,
        (gridScale δ M b : ℝ) *
            ((gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)) ^ ((1 + 2 * κ) * ε) ≤ (ρ : ℝ) →
        (ρ : ℝ) ≤ (gridScale δ M a : ℝ) *
            ((gridScale δ M b : ℝ) / (gridScale δ M a : ℝ)) ^ ((1 + 2 * κ) * ε) →
      ∀ i₀ ∈ F,
        ENNReal.ofReal (((ρ : ℝ) / (gridScale δ M b : ℝ)) ^ ζ')
          ≤ (C : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-(27 / (M : ℝ)))) *
              ConvexSpaceBody.frostmanConstant (fibreIndex t T δ ρ i₀)
                (fibreBodies T (gridScale δ M b))
                ((T i₀).rescale (2 * ρ)).toConvexSpaceBody := by
  classical
  obtain ⟨C, hC1, hring⟩ := exists_rounding_grid_index_sharp (E := E) hn Cu hCu
  refine ⟨C, hC1, ?_⟩
  intro M N hM hN hNM ε κ hε hκ hNκM ι δ hδ hδ1 hδ0 t T hball hu Ct hCt ζ' hζ'0 hζ'1 a b hab hbM
    hlong F hFt hfail ρ hρl hρr
  have hδposR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδnonneg : 0 ≤ (δ : ℝ) := le_of_lt hδposR
  have hσb_posR : (0 : ℝ) < (gridScale δ M b : ℝ) := by
    exact_mod_cast (gridScale_pos hδ M b)
  have hσa_posR : (0 : ℝ) < (gridScale δ M a : ℝ) := by
    exact_mod_cast (gridScale_pos hδ M a)
  have hρposR : (0 : ℝ) < (ρ : ℝ) :=
    lt_of_lt_of_le (mul_pos hσb_posR (Real.rpow_pos_of_pos (div_pos hσa_posR hσb_posR) _)) hρl
  have hρ : 0 < ρ := by exact_mod_cast hρposR
  obtain ⟨c, -, hσc_le_ρ, hρ_le_σc3, hadm1, hc1M, hratio, htransfer⟩ :=
    hring M N hM hN hNM hε hκ hNκM hδ hδ1 hδ0 t T hball hu ζ' hζ'0 hζ'1 a b hbM hlong F hFt ρ hρ
      hρl hρr
  have hfail_c : ∀ i₀ ∈ F, ¬ BlockFrostmanAt t T M Ct ζ' c b i₀ := fun i₀ hi₀F hb =>
    hfail i₀ hi₀F (⟨c, hadm1, hc1M, hb⟩ : NodeSplitTest t T M Ct ε ζ' a b i₀)
  intro i₀ hi₀F
  let X : ENNReal := ENNReal.ofReal ((δ : ℝ) ^ (-(3 / (M : ℝ))))
  let G : ENNReal := ENNReal.ofReal ((δ : ℝ) ^ (24 / (M : ℝ)))
  let G' : ENNReal := ENNReal.ofReal ((δ : ℝ) ^ (-(24 / (M : ℝ))))
  let H : ENNReal := ENNReal.ofReal ((δ : ℝ) ^ (-(27 / (M : ℝ))))
  let Y : ENNReal := ENNReal.ofReal (((gridScale δ M c : ℝ) / (gridScale δ M b : ℝ)) ^ ζ')
  let Fc : ENNReal := ConvexSpaceBody.frostmanConstant
      (fibreIndex t T δ (gridScale δ M c) i₀) (fibreBodies T (gridScale δ M b))
      ((T i₀).rescale (2 * gridScale δ M c)).toConvexSpaceBody
  let Fρ : ENNReal := ConvexSpaceBody.frostmanConstant (fibreIndex t T δ ρ i₀)
      (fibreBodies T (gridScale δ M b)) ((T i₀).rescale (2 * ρ)).toConvexSpaceBody
  have hZ : ENNReal.ofReal (((ρ : ℝ) / (gridScale δ M b : ℝ)) ^ ζ') ≤ X * Y := by
    dsimp [X, Y]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδnonneg (-(3 / (M : ℝ))))]
    exact ENNReal.ofReal_le_ofReal hratio
  have htest_lt : (Ct : ENNReal) * Y < Fc :=
    not_le.mp (by simpa [BlockFrostmanAt, Fc, Y] using hfail_c i₀ hi₀F)
  have hYleCtY : Y ≤ (Ct : ENNReal) * Y := by
    simpa using mul_le_mul' (ENNReal.coe_le_coe.mpr hCt) (le_refl Y)
  have hGFc : G * Fc ≤ (C : ENNReal) * Fρ := by
    dsimp [G, Fc, Fρ]; exact htransfer i₀ hi₀F
  have hGG' : G' * G = 1 := by
    dsimp [G', G]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδnonneg (-(24 / (M : ℝ)))),
      ← Real.rpow_add hδposR]
    simp
  have hXG' : X * G' = H := by
    dsimp [X, G', H]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδnonneg (-(3 / (M : ℝ)))),
      ← Real.rpow_add hδposR,
      show -(3 / (M : ℝ)) + -(24 / (M : ℝ)) = -(27 / (M : ℝ)) by ring]
  calc
    ENNReal.ofReal (((ρ : ℝ) / (gridScale δ M b : ℝ)) ^ ζ') ≤ X * Y := hZ
    _ ≤ X * Fc := mul_le_mul' le_rfl (hYleCtY.trans htest_lt.le)
    _ = X * (G' * G) * Fc := by rw [hGG', mul_one]
    _ = X * G' * (G * Fc) := by ring
    _ ≤ X * G' * ((C : ENNReal) * Fρ) := mul_le_mul' le_rfl hGFc
    _ = (C : ENNReal) * H * Fρ := by rw [hXG']; ring

/-! ### The stopping time and its terminal step -/

/-- The exponent sequence of the stopping time is nonnegative up to the grid length.  The geometric
gap `η k ≤ ε η (k+1)` propagates `0 ≤ η 0` upwards because `ε > 0`. -/
theorem eta_nonneg_of_gap (N : ℕ) (hN : 0 < N) {ε : ℝ} (hε : ε = 1 / Real.sqrt (N : ℝ))
    (η : ℕ → ℝ) (hη0 : 0 ≤ η 0) (hηgap : ∀ k < N, η k ≤ ε * η (k + 1)) :
    ∀ k ≤ N, 0 ≤ η k := by
  have hεpos : 0 < ε := by
    rw [hε]
    exact one_div_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))
  intro k
  induction k with
  | zero => exact fun _ => hη0
  | succ n ih =>
    exact fun hnN => (mul_nonneg_iff_of_pos_left hεpos).mp
      ((ih (by omega)).trans (hηgap n (by omega)))

/-- **Alternative (ii) from a terminal long block, on the `⌈log log 1/δ⌉`-grid.**  The terminal step
of half (A) on that grid: the window exponent is `(1+2κ)ε` and the interpolation factor is
`δ^{-27/M}`, a `Kakeya.MultiScaleFac.scaleGapLoss`.  The majority set `F`, the separation
`σ_b ≤ δ^ε σ_a` and the anchoring at the doubled leaf are as in `lem:terminal_alternative_two`. -/
theorem alternative_two_of_terminal_block_sharp (hn : Module.finrank ℝ E = 3)
    (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ C : NNReal, 1 ≤ C ∧
      ∀ (M N : ℕ), 16 ≤ M → 0 < N → (3 : ℝ) * (N : ℝ) ≤ (M : ℝ) →
      ∀ {ε κ : ℝ}, ε = 1 / Real.sqrt (N : ℝ) → 0 < κ → (N : ℝ) ≤ κ * (M : ℝ) →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) < 1 → δ ≤ (16 : NNReal) ^ (-(M : ℝ)) →
      ∀ (t : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      UniformTubeSet t T M Cu →
      ∀ Ct : NNReal, 1 ≤ Ct →
      ∀ (η : ℕ → ℝ) (m : ℕ), 0 ≤ η m → η m ≤ ε * η (m + 1) → η (m + 1) ≤ ε →
      ∀ a b : ℕ, a < b → b ≤ M → IsLongBlock M ε a b →
      ¬ (t.card ≤ 2 * (passingNodes t T M Ct ε (η (m + 1)) a b).card) →
      ∃ F ⊆ t, t.card ≤ 2 * F.card ∧
        (gridScale δ M b : ℝ) ≤ (δ : ℝ) ^ ε * (gridScale δ M a : ℝ) ∧
        ∀ ρ : NNReal,
          (gridScale δ M b : ℝ) *
              ((gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)) ^ ((1 + 2 * κ) * ε) ≤ (ρ : ℝ) →
          (ρ : ℝ) ≤ (gridScale δ M a : ℝ) *
              ((gridScale δ M b : ℝ) / (gridScale δ M a : ℝ)) ^ ((1 + 2 * κ) * ε) →
          ∀ i₀ ∈ F,
            ENNReal.ofReal (((ρ : ℝ) / (gridScale δ M b : ℝ)) ^ η (m + 1))
              ≤ (C : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-(27 / (M : ℝ)))) *
                  ConvexSpaceBody.frostmanConstant (fibreIndex t T δ ρ i₀)
                    (fibreBodies T (gridScale δ M b))
                    ((T i₀).rescale (2 * ρ)).toConvexSpaceBody := by
  classical
  obtain ⟨C, hC1, hring⟩ :=
    dividingScales_lower_bound_on_failing_nodes_sharp (E := E) hn Cu hCu
  refine ⟨C, hC1, ?_⟩
  intro M N hM hN hNM ε κ hε hκ hNκM ι δ hδ hδ1 hδ0 t T hball hu Ct hCt η m hη0 hηm hηε a b hab
    hbM hlong hnotPass
  have hεpos : 0 < ε := by
    rw [hε]
    exact one_div_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))
  have hεle1 : ε ≤ 1 := by
    have hsqrt : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
      simpa using Real.sqrt_le_sqrt (by exact_mod_cast hN : (1 : ℝ) ≤ (N : ℝ))
    rw [hε, div_le_one (by linarith)]
    exact hsqrt
  let F : Finset ι := failingNodes t T M Ct ε (η (m + 1)) a b
  have hFsub : F ⊆ t := failingNodes_subset t T M Ct ε (η (m + 1)) a b
  have hcard : t.card ≤ 2 * F.card :=
    Or.resolve_left
      (card_le_two_mul_card_passingNodes_or_failingNodes t T M Ct ε (η (m + 1)) a b) hnotPass
  have hfail : ∀ i₀ ∈ F, ¬ NodeSplitTest t T M Ct ε (η (m + 1)) a b i₀ := fun i₀ hi₀ =>
    (mem_failingNodes.mp hi₀).2
  have hsep : (gridScale δ M b : ℝ) ≤ (δ : ℝ) ^ ε * (gridScale δ M a : ℝ) :=
    gridScale_b_le_rpow_eps_mul_gridScale_a_of_isLongBlock M (by omega) hδ hδ1.le hab hlong
  have hη'0 : 0 ≤ η (m + 1) := (mul_nonneg_iff_of_pos_left hεpos).mp (hη0.trans hηm)
  have hη'1 : η (m + 1) ≤ 1 := hηε.trans hεle1
  refine ⟨F, hFsub, hcard, hsep, ?_⟩
  intro ρ hρl hρr
  exact hring M N hM hN hNM hε hκ hNκM hδ hδ1 hδ0 t T hball hu Ct hCt (η (m + 1)) hη'0 hη'1 a b
    hab hbM hlong F hFsub hfail ρ hρl hρr

/-! ### Alternative (i) at a polylogarithmic block constant -/

/-! **Alternative (i) with a polylogarithmic block constant** (blueprint
`lem:alternative_one_polylog`).

`Kakeya.MultiScaleFac.isFrostmanAtEveryScale_of_cuts` quantifies its block constant `Cb` before
`δ`, so it cannot be applied to the terminal constant of
`Kakeya.MultiScaleFac.exists_maximal_cuts_state_instance_hoisted_blocks_quad`, which is only
bounded by `C₁ (1 - log δ)^{K₁}`.  The same obstruction occurs in the assembly of
`Kakeya.MultiScaleFac.dividingScalesFrostman`.  This is that theorem's all-short branch, restated
with the block constant allowed to
depend on `δ` through a fixed power of `1 - log δ`, and it is the only place where the
polylogarithm accumulated by the stopping time meets alternative (i).

The absorption is legitimate because the `5ε` budget is not tight.  The exponent actually spent by
`isFrostmanAtEveryScale_of_cuts` is `ζ + (4ε + 6ε²) + 12ε² ≤ 4ε + 19ε²`, leaving a margin of
`ε - 19ε²`, which is at least `ε/2` once `ε ≤ 1/38`; the hypothesis `ε ≤ 1/64` gives it.  A
polylogarithmic
factor is `δ^{-ε/2}` below a threshold `δ₀(N, K₁)` by
`Kakeya.StickyKakeya.exists_threshold_mul_pow_one_sub_log_le_rpow_neg` — the same mechanism, and
the same reason for a threshold, as in `card_le_mul_rpow_neg_of_refinement_chain`, and legitimate
for the same reason: `N`, and with it `ε` and `K₁`, are quantified before `δ`.

The output constant `C` is again `δ`-independent, so this is a genuine restoration of the shape
alternative (i) is required to have, not a weakening of it. -/

/-- **The arithmetic budget for alternative (i).**  Once `ε ≤ 1/64` and `ζ ≤ ε²`, the exponent
actually spent is `ζ + 4ε + 18ε² + ε/2`, and the `ε/2` margin leaves it below the `5ε` error
budget. -/
private theorem eps_margin_arithmetic {ε ζ : ℝ} (hεpos : 0 < ε) (hε : ε ≤ (1 : ℝ) / 64)
    (hζ0 : 0 ≤ ζ) (hζε : ζ ≤ ε * ε) :
    0 ≤ ζ + 4 * ε + 6 * ε ^ 2 + ε / 2 ∧ ζ + 4 * ε + 18 * ε ^ 2 + ε / 2 ≤ 5 * ε :=
  ⟨by linarith [sq_nonneg ε], by linarith [mul_le_mul_of_nonneg_left hε hεpos.le]⟩

/-- The `δ`-independent engine constant for a chain of `J+2` gaps, keeping the `Cb`-power explicit.
This is `Kakeya.MultiScaleFac.frostmanConstant_fibre_le_prod_of_cuts_sharp` with the `Cb`-dependence
of its constant exposed, the factor `Cb ^ (J + 2)` appearing separately; that is what makes a
polylogarithmic block constant absorbable.  The engine constant precedes `N` and `J` as well. -/
private theorem frostmanConstant_fibre_le_prod_of_cuts_sharp_poly
    (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ engine : NNReal, 1 ≤ engine ∧
      ∀ (N J : ℕ), 0 < N →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      UniformTubeSet s T N Cu →
      ComparableFibreCounts s T (gridScales δ N) Cu →
      ∀ Cb : NNReal, 1 ≤ Cb →
      ∀ (S : Finset ℕ) (hcard : S.card = J + 3), 0 ∈ S → N ∈ S → S ⊆ Finset.range (N + 1) →
      ∀ ζ : ℝ, 0 ≤ ζ →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) → 0 < a →
        BlockFrostman s T N Cb ζ a b) →
      ∀ i₀ ∈ s,
        ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (cutChain δ N J S hcard 1) i₀)
            (fibreBodies T δ) ((T i₀).rescale (cutChain δ N J S hcard 1)).toConvexSpaceBody
          ≤ (engine : ENNReal) ^ (J + 2) * (Cb : ENNReal) ^ (J + 2) *
              ENNReal.ofReal (((cutChain δ N J S hcard 1 : ℝ) / (δ : ℝ)) ^ ζ) := by
  classical
  obtain ⟨engine, hE1, hmain⟩ := frostmanConstant_fibre_le_prod (E := E) Cu Cu hCu
  refine ⟨engine, hE1, ?_⟩
  intro N J hN ι δ hδ hδ1 hδ0 s T hball hu hcmp Cb hCb S hcard h0 hNS hsub ζ hζ hBlock i₀ hi₀
  let σ : Fin (J + 3) → NNReal := cutChain δ N J S hcard
  let X : Fin (J + 2) → ENNReal :=
    fun m => if m = 0 then 1 else (Cb : ENNReal) * cutChainFactor δ N J S hcard ζ m
  have hσ0 : σ 0 = 1 := by
    simpa [σ] using cutChain_zero hcard h0
  have hσlast : σ (Fin.last (J + 2)) = δ := by
    simpa [σ] using cutChain_last hcard hN hNS hsub
  have hanti : Antitone σ := by
    simpa [σ] using cutChain_antitone hδ hδ1 hcard
  have hgap : ∀ m : Fin (J + 2), 16 * σ m.succ ≤ σ m.castSucc := by
    intro m
    simpa [σ] using cutChain_gap hδ hδ1 hδ0 hcard hsub m
  have hu_chain : ChainUniformTubeSet s T (J + 2) (finChain σ) Cu :=
    chainUniformCutChain (E := E) hu hcard hsub
  have hcmp_chain : ∀ i₁ ∈ s, ∀ i₂ ∈ s,
      ((fibreIndex s T δ (σ 1) i₁).card : NNReal) ≤
        Cu * ((fibreIndex s T δ (σ 1) i₂).card : NNReal) := by
    intro i₁ hi₁ i₂ hi₂
    have hmem : cutChain δ N J S hcard 1 ∈ gridScales δ N := cutChain_mem_gridScales hcard hsub 1
    simpa [σ] using (hcmp (cutChain δ N J S hcard 1) hmem i₁ hi₁ i₂ hi₂)
  have hXtop : ∀ m, X m ≠ ⊤ := by
    intro m
    by_cases hm0 : m = 0
    · simp [X, hm0]
    · dsimp [X]
      rw [if_neg hm0]
      exact ENNReal.mul_ne_top (by simp) (cutChainFactor_ne_top δ N J S hcard ζ m)
  have hX0 : (1 : ENNReal) ≤ X 0 := by
    simp [X]
  have hFr : ∀ m : Fin (J + 2), m ≠ 0 → ∀ i₁ ∈ s,
      ConvexSpaceBody.IsFrostmanIn
        (fibreIndex s T δ (σ m.castSucc) i₁) (fibreBodies T (σ m.succ))
        ((T i₁).rescale (2 * σ m.castSucc)).toConvexSpaceBody (X m) := by
    intro m hm i₁ hi₁
    let a : ℕ := (S.orderIsoOfFin hcard m.castSucc : ℕ)
    let b : ℕ := (S.orderIsoOfFin hcard m.succ : ℕ)
    have hab_adj := orderIsoOfFin_castSucc_lt_succ hcard m
    have haS : a ∈ S := by simp [a]
    have hbS : b ∈ S := by simp [b]
    have ha0 : 0 < a := by
      have hpos_mc : (0 : Fin (J + 3)) < m.castSucc :=
        Fin.pos_iff_ne_zero.mpr fun hz => hm (Fin.ext (by simpa using congrArg Fin.val hz))
      have hlt : ((S.orderIsoOfFin hcard 0 : ℕ) < (S.orderIsoOfFin hcard m.castSucc : ℕ)) := by
        exact_mod_cast (S.orderIsoOfFin hcard).strictMono hpos_mc
      rwa [orderIsoOfFin_zero_eq hcard h0] at hlt
    have hBlockAB : BlockFrostman s T N Cb ζ a b := hBlock a haS b hbS hab_adj.1 hab_adj.2 ha0
    have hAt := hBlockAB i₁ hi₁
    dsimp [X]
    rw [if_neg hm]
    exact (ConvexSpaceBody.frostmanConstant_le_iff.mp (by
      simpa [BlockFrostmanAt, a, b, σ, cutChainFactor, cutChain_apply] using hAt))
  have hmain' := hmain J hδ hδ1 s T hball σ hσ0 hσlast hanti hgap hu_chain hcmp_chain X hXtop hX0
    hFr i₀ hi₀
  have htel : (∏ k : Fin (J + 1), cutChainFactor δ N J S hcard ζ k.succ) =
      ENNReal.ofReal (((cutChain δ N J S hcard 1 : ℝ) / (δ : ℝ)) ^ ζ) := by
    let ρ : Fin (J + 2) → NNReal := fun k => cutChain δ N J S hcard k.succ
    let r : Fin (J + 1) → ℝ := fun k => (ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)
    have hchain_pos : ∀ k : Fin (J + 2), 0 < (ρ k : ℝ) := fun k => by
      exact_mod_cast (cutChain_apply .. ▸ gridScale_pos hδ N (S.orderIsoOfFin hcard k.succ) :
        0 < cutChain δ N J S hcard k.succ)
    have hr_nonneg : ∀ k : Fin (J + 1), 0 ≤ r k := fun k =>
      div_nonneg (hchain_pos k.castSucc).le (hchain_pos k.succ).le
    have htel_ratios : (∏ k : Fin (J + 1), r k) =
        (cutChain δ N J S hcard 1 : ℝ) / (δ : ℝ) := by
      rw [show (∏ k : Fin (J + 1), r k) = (ρ 0 : ℝ) / (ρ (Fin.last (J + 1)) : ℝ) from
        prod_ratio_telescope (J + 1) ρ hchain_pos]
      change (cutChain δ N J S hcard 1 : ℝ) / (cutChain δ N J S hcard (Fin.last (J + 2)) : ℝ) = _
      rw [cutChain_last hcard hN hNS hsub]
    calc
      ∏ k : Fin (J + 1), cutChainFactor δ N J S hcard ζ k.succ
          = ∏ k : Fin (J + 1), ENNReal.ofReal (r k ^ ζ) :=
            Finset.prod_congr rfl fun k _ => by
              dsimp [r, ρ]; unfold cutChainFactor; congr 1
      _ = ENNReal.ofReal (∏ k : Fin (J + 1), r k ^ ζ) :=
            (ENNReal.ofReal_prod_of_nonneg (fun k _ => Real.rpow_nonneg (hr_nonneg k) ζ)).symm
      _ = ENNReal.ofReal (((cutChain δ N J S hcard 1 : ℝ) / (δ : ℝ)) ^ ζ) := by
            rw [← htel_ratios]
            exact congrArg _ (Real.finsetProd_rpow
              (s := (Finset.univ : Finset (Fin (J + 1)))) (f := r) (fun k _ => hr_nonneg k) ζ)
  have hXprod : (∏ m : Fin (J + 2), X m) =
      (Cb : ENNReal) ^ (J + 1) *
        ENNReal.ofReal (((cutChain δ N J S hcard 1 : ℝ) / (δ : ℝ)) ^ ζ) := by
    calc
      ∏ m : Fin (J + 2), X m
          = ∏ k : Fin (J + 1), (Cb : ENNReal) * cutChainFactor δ N J S hcard ζ k.succ := by
            rw [Fin.prod_univ_succ]; simp [X]
      _ = (Cb : ENNReal) ^ (J + 1) *
            ∏ k : Fin (J + 1), cutChainFactor δ N J S hcard ζ k.succ := by
            rw [Finset.prod_mul_distrib]; simp
      _ = _ := by rw [htel]
  calc
    ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (cutChain δ N J S hcard 1) i₀)
          (fibreBodies T δ) ((T i₀).rescale (cutChain δ N J S hcard 1)).toConvexSpaceBody
        = ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (σ 1) i₀)
          (fibreBodies T δ) ((T i₀).rescale (σ 1)).toConvexSpaceBody := by
            simp [σ]
    _ ≤ (engine : ENNReal) ^ (J + 2) * ∏ m, X m := hmain'
    _ = (engine : ENNReal) ^ (J + 2) * (Cb : ENNReal) ^ (J + 1) *
          ENNReal.ofReal (((cutChain δ N J S hcard 1 : ℝ) / (δ : ℝ)) ^ ζ) := by
            rw [hXprod, ← mul_assoc]
    _ ≤ (engine : ENNReal) ^ (J + 2) * (Cb : ENNReal) ^ (J + 2) *
          ENNReal.ofReal (((cutChain δ N J S hcard 1 : ℝ) / (δ : ℝ)) ^ ζ) :=
          mul_le_mul' (mul_le_mul' le_rfl
            (pow_le_pow_right₀ (by exact_mod_cast hCb) (by omega))) le_rfl

/-! ### The same three bounds with the block constant carried as an explicit power

The three lemmas above assume the block constant `Cb` to be at most `C₁ (1 - \log δ)^{K₁}` with
`C₁` and `K₁` quantified before `δ`.  The hoisted stopping time of GWZ Lemma 7.7(A) does not
deliver a block constant of that shape: what it bounds is a `δ`-dependent loss whose logarithm
grows like `(\log\log 1/δ)^2`, which exceeds every fixed power of `1 - \log δ`.

The three lemmas below make no assumption at all on `Cb`.  They carry it through the chain as an
explicit factor `Cb^p`, where `p` is any bound on the number of blocks — that is, on the
cardinality of the cut set.  Two things are gained.  The output constant no longer mentions `C₁`,
so it is genuinely uniform in the block constant; and the exponent of `Cb` is the *stopping-time*
length rather than the grid length, which is what lets a caller whose grid length depends on `δ`
still pay a `δ`-independent power of the block loss.

Each of the three is the exact analogue of the corresponding `_polylog_uniform` lemma above, which
is recovered by taking `p := N + 1` and using `Cb^{N+1} ≤ C₁^{N+1}(1 - \log δ)^{K₁(N+1)}`. -/

/-- **The cut-scale bound with the block constant carried as an explicit power.**
`Kakeya.StickyKakeya.cutScale_le_of_cuts_polylog_uniform` with the polylogarithmic hypothesis on the
block constant removed altogether: the chain telescopes over at most `S.card` blocks, so one factor
of `Cb` is spent per block and the bound carries `Cb ^ p` for any `p` with `S.card ≤ p`. -/
theorem cutScale_le_of_cuts_blockPow_uniform (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ C : NNReal, 1 ≤ C ∧
      ∀ (N : ℕ), 0 < N →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      UniformTubeSet s T N Cu →
      ComparableFibreCounts s T (gridScales δ N) Cu →
      ∀ Cb : NNReal, 1 ≤ Cb →
      ∀ p : ℕ, 1 ≤ p →
      ∀ S : Finset ℕ, S.card ≤ p → 0 ∈ S → N ∈ S → S ⊆ Finset.range (N + 1) →
      ∀ ζ : ℝ, 0 ≤ ζ →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) → BlockFrostman s T N Cb ζ a b) →
      ∀ k ∈ S, 0 < k → 2 ≤ (S.filter (fun x => k ≤ x)).card → ∀ i₀ ∈ s,
        ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (gridScale δ N k) i₀)
            (fibreBodies T δ) ((T i₀).rescale (gridScale δ N k)).toConvexSpaceBody
          ≤ (C : ENNReal) ^ (N + 1) * (Cb : ENNReal) ^ p *
              ENNReal.ofReal (((gridScale δ N k : ℝ) / (δ : ℝ)) ^ ζ) := by
  classical
  obtain ⟨Cmax, hCmax1, hEmain⟩ :=
    frostmanConstant_fibre_le_prod_of_cuts_sharp_poly (E := E) Cu hCu
  refine ⟨Cmax, hCmax1, ?_⟩
  intro N hN ι δ hδ hδ1 hδ0 s T hball hu hcmp Cb hCb p hp S hScardp h0S hNS hsub ζ hζ hBlock k hkS
    hk0 hcard2 i₀ hi₀
  let m : ℕ := (S.filter (fun x => k ≤ x)).card
  let J : ℕ := m - 2
  let S' : Finset ℕ := restrictCuts S k
  have hScard : S.card ≤ N + 1 := by simpa using Finset.card_le_card hsub
  have hfilt : m ≤ S.card := Finset.card_le_card (Finset.filter_subset _ S)
  have hmsub : m ≤ N + 1 := hfilt.trans hScard
  have hJcard : (S.filter (fun x => k ≤ x)).card = J + 2 := by dsimp [J, m]; omega
  have hJ2 : J + 2 ≤ N + 1 := by omega
  have hcardS' : S'.card = J + 3 := by
    dsimp [S', J]; rw [card_restrictCuts hk0]; dsimp [m]; omega
  have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (hsub hkS))
  have h0S' : 0 ∈ S' := zero_mem_restrictCuts S k
  have hNS' : N ∈ S' := mem_restrictCuts_of_le hNS hkN
  have hsubS' : S' ⊆ Finset.range (N + 1) := restrictCuts_subset_range hsub
  have hBlock' : ∀ a ∈ S', ∀ b ∈ S', a < b → (∀ x ∈ S', ¬(a < x ∧ x < b)) → 0 < a →
      BlockFrostman s T N Cb ζ a b := by
    intro a ha b hb hab hadj ha0
    have hka : k ≤ a := by
      rcases Finset.mem_insert.mp ha with rfl | haf
      · omega
      · exact (Finset.mem_filter.mp haf).2
    obtain ⟨haS, hbS, hadjS⟩ := adjacent_of_adjacent_restrictCuts (S := S) hk0 ha hb hka hab hadj
    exact hBlock a haS b hbS hab hadjS
  have hbound := hEmain N J hN hδ hδ1 hδ0 s T hball hu hcmp
    Cb hCb S' hcardS' h0S' hNS' hsubS' ζ hζ hBlock' i₀ hi₀
  rw [cutChain_restrictCuts_one δ N J hkS hk0 hcardS'] at hbound
  have hJ2p : J + 2 ≤ p := hJcard ▸ hfilt.trans hScardp
  exact hbound.trans (mul_le_mul'
    (mul_le_mul' (pow_le_pow_right₀ (by exact_mod_cast hCmax1) hJ2)
      (pow_le_pow_right₀ (by exact_mod_cast hCb) hJ2p)) le_rfl)

/-- **The per-grid-scale bound with the block constant carried as an explicit power.**
`Kakeya.StickyKakeya.gridScale_le_of_cuts_polylog_uniform` with the polylogarithmic hypothesis on
the block constant removed: the factor `Cb ^ p` replaces the polylogarithm verbatim, `p` being any
bound on `S.card`.  The grid exponent is unchanged at `ζ + (4ε + 6ε²)`. -/
private theorem gridScale_le_of_cuts_blockPow_uniform (hn : Module.finrank ℝ E = 3)
    (ε : ℝ) (hεpos : 0 < ε) (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ A : NNReal, 1 ≤ A ∧
      ∀ (N : ℕ), 0 < N → 1 ≤ ε ^ 2 * (N : ℝ) →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 →
      δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      UniformTubeSet s T N Cu →
      ComparableFibreCounts s T (gridScales δ N) Cu →
      ∀ Cb : NNReal, 1 ≤ Cb →
      ∀ p : ℕ, 1 ≤ p →
      ∀ S : Finset ℕ, S.card ≤ p → 3 ≤ S.card → 0 ∈ S → N ∈ S → S ⊆ Finset.range (N + 1) →
      ∀ ζ : ℝ, 0 ≤ ζ →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
        BlockFrostman s T N Cb ζ a b ∧ ¬ IsLongBlock N ε a b) →
      (∀ i₀ ∈ s,
        ConvexSpaceBody.frostmanConstant (fibreIndex s T δ 1 i₀) (fibreBodies T δ)
            ((T i₀).rescale 1).toConvexSpaceBody
          ≤ (Cb : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-ζ))) →
      ∀ k ≤ N, ∀ i₀ ∈ s,
        ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (gridScale δ N k) i₀)
            (fibreBodies T δ) ((T i₀).rescale (gridScale δ N k)).toConvexSpaceBody
          ≤ (A : ENNReal) ^ (N + 1) * (Cb : ENNReal) ^ p *
              ENNReal.ofReal ((δ : ℝ) ^ (-(ζ + 4 * ε + 6 * ε ^ 2))) := by
  classical
  have hε0 : 0 ≤ ε := le_of_lt hεpos
  let n4 : ℕ := Module.finrank ℝ E
  obtain ⟨Cd, hCd1, hCd⟩ := frostmanConstant_gridScale_deflate_uniform (E := E) Cu hCu
  obtain ⟨Ccut, hCcut1, hCcut⟩ := cutScale_le_of_cuts_blockPow_uniform (E := E) Cu hCu
  let Ccrude : NNReal := 2 * Tube.volume_le.C n4 / Tube.le_volume.c n4
  let C0 : NNReal := max Ccut Ccrude
  let A : NNReal := Cd * C0
  have hCcut_le_C0 : Ccut ≤ C0 := le_max_left _ _
  have hCcrude_le_C0 : Ccrude ≤ C0 := le_max_right _ _
  have hC01 : (1 : NNReal) ≤ C0 := hCcut1.trans hCcut_le_C0
  have hC0_le_A : C0 ≤ A := by simpa using mul_le_mul' hCd1 (le_refl C0)
  have hA1 : 1 ≤ A := hC01.trans hC0_le_A
  refine ⟨A, hA1, ?_⟩
  intro N hN hεN ι δ hδ hδ1 hδ0 s T hball hu hcmp Cb hCb p hp S hScardp hcardS h0S hNS hsub ζ hζ
    hBlock hbase k hk i₀ hi₀
  have hNpos : 0 < N := hN
  have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hεsq : (1 : ℝ) / (N : ℝ) ≤ ε ^ 2 := (div_le_iff₀ hNposR).mpr hεN
  let target : ENNReal := ENNReal.ofReal ((δ : ℝ) ^ (-(ζ + 4 * ε + 6 * ε ^ 2)))
  let P : ENNReal := (Cb : ENNReal) ^ p
  let expN (d : ℕ) : ℝ := -(((Module.finrank ℝ E : ℝ) + 1) * (d : ℝ) +
      2 * (Module.finrank ℝ E : ℝ)) / (N : ℝ)
  set Fk := ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (gridScale δ N k) i₀)
      (fibreBodies T δ) ((T i₀).rescale (gridScale δ N k)).toConvexSpaceBody with hFk_def
  have hδposR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδnonneg : 0 ≤ (δ : ℝ) := le_of_lt hδposR
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNposR
  have hdiv_σmδ : ∀ m : ℕ, (gridScale δ N m : ℝ) / (δ : ℝ)
      = (δ : ℝ) ^ (((m : ℝ) - (N : ℝ)) / (N : ℝ)) := by
    intro m
    rw [show ((m : ℝ) - (N : ℝ)) / (N : ℝ) = (m : ℝ) / (N : ℝ) - 1 by field_simp,
      Real.rpow_sub hδposR, Real.rpow_one,
      show (gridScale δ N m : ℝ) = (δ : ℝ) ^ ((m : ℝ) / (N : ℝ)) by simp [gridScale]]
  have h_neg1_le : ∀ m : ℕ, -1 ≤ ((m : ℝ) - (N : ℝ)) / (N : ℝ) := by
    intro m
    rw [le_div_iff₀ hNposR]
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hP1 : 1 ≤ P := one_le_pow₀ (by exact_mod_cast hCb)
  have hC0A : ∀ Q : ENNReal, (C0 : ENNReal) ^ (N + 1) * P * Q
      ≤ (A : ENNReal) ^ (N + 1) * P * Q := fun _ =>
    mul_le_mul' (mul_le_mul' (pow_le_pow_left₀ bot_le (by exact_mod_cast hC0_le_A) _) le_rfl) le_rfl
  have hδζ_le_target : ENNReal.ofReal ((δ : ℝ) ^ (-ζ)) ≤ target :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hδposR hδ1
      (by nlinarith [hζ, hε0, sq_nonneg ε]))
  change Fk ≤ (A : ENNReal) ^ (N + 1) * P * target
  have hcut : ∀ j ≤ N, j ∈ S → j < N → ∀ i₀ ∈ s,
      ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (gridScale δ N j) i₀)
          (fibreBodies T δ) ((T i₀).rescale (gridScale δ N j)).toConvexSpaceBody
        ≤ (C0 : ENNReal) ^ (N + 1) * P * ENNReal.ofReal ((δ : ℝ) ^ (-ζ)) := by
    intro j hj hjS hjN i₀ hi₀
    by_cases hj0 : j = 0
    · subst j
      rw [gridScale_zero]
      have hCb_le : (Cb : ENNReal) ≤ (C0 : ENNReal) ^ (N + 1) * P :=
        (le_self_pow (by exact_mod_cast hCb) (by omega : p ≠ 0)).trans
          (by simpa using mul_le_mul' (one_le_pow₀ (by exact_mod_cast hC01) :
            (1 : ENNReal) ≤ (C0 : ENNReal) ^ (N + 1)) (le_refl P))
      exact (hbase i₀ hi₀).trans (mul_le_mul' hCb_le le_rfl)
    · have hjpos : 0 < j := by omega
      have hcard2 : 2 ≤ (S.filter (fun x => j ≤ x)).card := by
        have hpair : ({j, N} : Finset ℕ) ⊆ S.filter (fun x => j ≤ x) := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hjS, le_rfl⟩
          · exact Finset.mem_filter.mpr ⟨hNS, by omega⟩
        have h := Finset.card_le_card hpair
        rwa [Finset.card_pair (by omega : j ≠ N)] at h
      have hBlockj : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
          BlockFrostman s T N Cb ζ a b := fun a ha b hb hab hadj =>
        (hBlock a ha b hb hab hadj).1
      have hcutj := hCcut N hNpos hδ hδ1 hδ0 s T hball hu hcmp Cb hCb p hp S hScardp h0S hNS hsub
        ζ hζ hBlockj j hjS hjpos hcard2 i₀ hi₀
      have hratioζ : ((gridScale δ N j : ℝ) / (δ : ℝ)) ^ ζ ≤ (δ : ℝ) ^ (-ζ) := by
        rw [hdiv_σmδ j, ← Real.rpow_mul hδnonneg]
        refine Real.rpow_le_rpow_of_exponent_ge hδposR hδ1 ?_
        simpa using mul_le_mul_of_nonneg_right (h_neg1_le j) hζ
      calc
        ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (gridScale δ N j) i₀)
            (fibreBodies T δ) ((T i₀).rescale (gridScale δ N j)).toConvexSpaceBody
            ≤ (Ccut : ENNReal) ^ (N + 1) * P
                * ENNReal.ofReal (((gridScale δ N j : ℝ) / (δ : ℝ)) ^ ζ) := by
              simpa [P] using hcutj
        _ ≤ (Ccut : ENNReal) ^ (N + 1) * P * ENNReal.ofReal ((δ : ℝ) ^ (-ζ)) :=
              mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hratioζ)
        _ ≤ (C0 : ENNReal) ^ (N + 1) * P * ENNReal.ofReal ((δ : ℝ) ^ (-ζ)) :=
              mul_le_mul' (mul_le_mul' (pow_le_pow_left₀ bot_le
                (by exact_mod_cast hCcut_le_C0) (N + 1)) le_rfl) le_rfl
  by_cases hk0 : k = 0
  · subst k
    rw [hFk_def]
    calc
      ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (gridScale δ N 0) i₀) (fibreBodies T δ)
          ((T i₀).rescale (gridScale δ N 0)).toConvexSpaceBody
          ≤ (C0 : ENNReal) ^ (N + 1) * P * ENNReal.ofReal ((δ : ℝ) ^ (-ζ)) :=
            hcut 0 (Nat.zero_le N) h0S hNpos i₀ hi₀
      _ ≤ (C0 : ENNReal) ^ (N + 1) * P * target := mul_le_mul' le_rfl hδζ_le_target
      _ ≤ (A : ENNReal) ^ (N + 1) * P * target := hC0A target
  · by_cases hkN2 : N - 2 ≤ k
    · have hδσk : δ ≤ gridScale δ N k := by
        calc
          δ = gridScale δ N N := (gridScale_self δ hNpos).symm
          _ ≤ gridScale δ N k := gridScale_antitone hδ hδ1 N hk
      have hσk1 : gridScale δ N k ≤ 1 := gridScale_le_one hδ1 N k
      have hcrude := frostmanConstant_fibre_le_ratio_pow (s := s) (T := T) (σ := δ)
        (ρ := gridScale δ N k) hδ hδσk hσk1 hi₀
      have hcrude' : Fk ≤ ((Ccrude * (gridScale δ N k / δ) ^ 2 : NNReal) : ENNReal) := by
        dsimp [Ccrude]
        simpa [n4, hn, hFk_def] using hcrude
      have hratio : ((gridScale δ N k : ℝ) / (δ : ℝ)) ^ 2
          ≤ (δ : ℝ) ^ (-(ζ + 4 * ε + 6 * ε ^ 2)) := by
        rw [hdiv_σmδ k, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hδnonneg]
        refine Real.rpow_le_rpow_of_exponent_ge hδposR hδ1 ?_
        have hkge : (-2 : ℝ) ≤ (k : ℝ) - (N : ℝ) := by
          have : (N : ℝ) ≤ (k : ℝ) + 2 := by exact_mod_cast (by omega : N ≤ k + 2)
          linarith
        rw [div_mul_eq_mul_div, le_div_iff₀ hNposR]
        push_cast
        nlinarith [hkge, hεN, mul_nonneg hζ hNposR.le, (mul_pos hεpos hNposR).le]
      have hCcrude_le : (Ccrude : ENNReal) ≤ (A : ENNReal) ^ (N + 1) * P := by
        calc
          (Ccrude : ENNReal) ≤ (C0 : ENNReal) := by exact_mod_cast hCcrude_le_C0
          _ ≤ (C0 : ENNReal) ^ (N + 1) := le_self_pow (by exact_mod_cast hC01) (by omega)
          _ ≤ (A : ENNReal) ^ (N + 1) :=
                pow_le_pow_left₀ bot_le (by exact_mod_cast hC0_le_A) (N + 1)
          _ ≤ (A : ENNReal) ^ (N + 1) * P := by
                simpa using mul_le_mul' (le_refl ((A : ENNReal) ^ (N + 1))) hP1
      refine hcrude'.trans ?_
      calc
        ((Ccrude * (gridScale δ N k / δ) ^ 2 : NNReal) : ENNReal)
            = ENNReal.ofReal ((Ccrude * (gridScale δ N k / δ) ^ 2 : NNReal) : ℝ) := by
                rw [← ENNReal.ofReal_coe_nnreal]
        _ ≤ ENNReal.ofReal ((Ccrude : ℝ) * (δ : ℝ) ^ (-(ζ + 4 * ε + 6 * ε ^ 2))) :=
                ENNReal.ofReal_le_ofReal
                  (mul_le_mul_of_nonneg_left hratio (by positivity : (0 : ℝ) ≤ (Ccrude : ℝ)))
        _ = (Ccrude : ENNReal) * target := by
                dsimp [target]
                rw [ENNReal.ofReal_mul' (Real.rpow_nonneg hδnonneg _), ENNReal.ofReal_coe_nnreal]
        _ ≤ (A : ENNReal) ^ (N + 1) * P * target := mul_le_mul' hCcrude_le le_rfl
    · have hk3 : k ≤ N - 3 := by omega
      by_cases hkS : k ∈ S
      · calc
          Fk ≤ (C0 : ENNReal) ^ (N + 1) * P * ENNReal.ofReal ((δ : ℝ) ^ (-ζ)) :=
                hcut k hk hkS (by omega) i₀ hi₀
          _ ≤ (C0 : ENNReal) ^ (N + 1) * P * target := mul_le_mul' le_rfl hδζ_le_target
          _ ≤ (A : ENNReal) ^ (N + 1) * P * target := hC0A target
      · obtain ⟨a, haS, b, hbS, hak, hkb, hadj⟩ := exists_adjacent_containing h0S hNS hk hkS
        have haN : a ≤ N := by omega
        have haNlt : a < N := by omega
        have hd2 : a + (k - a) + 2 ≤ N := by omega
        have hab : a < b := lt_trans hak hkb
        have hshort : ¬ IsLongBlock N ε a b := (hBlock a haS b hbS hab hadj).2
        have hshortR : ((k - a : ℕ) : ℝ) ≤ ε * (N : ℝ) :=
          sub_le_of_not_isLongBlock hshort hak hkb
        have hdef := hCd N hNpos hδ hδ1 hδ0 s T hball hu a (k - a) hd2 i₀ hi₀
        have hcut_at_a := hcut a haN haS haNlt i₀ hi₀
        have hdeflR : -(4 * ε + 6 * ε ^ 2) ≤ expN (k - a) := by
          dsimp [expN]
          rw [show (Module.finrank ℝ E : ℝ) = (3 : ℝ) by exact_mod_cast hn, neg_div]
          exact neg_le_neg (deflate_exponent_le hNpos hεN (Nat.cast_nonneg _) hshortR)
        rw [Nat.add_sub_cancel' hak.le] at hdef
        have hprod : ENNReal.ofReal ((δ : ℝ) ^ expN (k - a)) *
            ENNReal.ofReal ((δ : ℝ) ^ (-ζ)) ≤ target := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδnonneg (expN (k - a))),
            ← Real.rpow_add hδposR]
          exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hδposR hδ1 (by linarith))
        have hCd_C0_le_A : ((Cd * C0 ^ (N + 1) : NNReal) : ENNReal) ≤ (A : ENNReal) ^ (N + 1) := by
          dsimp [A]
          rw [mul_pow]
          exact mul_le_mul' (le_self_pow (by exact_mod_cast hCd1) (by omega)) le_rfl
        calc
          Fk ≤ (Cd : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ expN (k - a)) *
              ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (gridScale δ N a) i₀)
                (fibreBodies T δ) ((T i₀).rescale (gridScale δ N a)).toConvexSpaceBody := hdef
          _ ≤ (Cd : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ expN (k - a)) *
              ((C0 : ENNReal) ^ (N + 1) * P * ENNReal.ofReal ((δ : ℝ) ^ (-ζ))) :=
                  mul_le_mul' le_rfl hcut_at_a
          _ = ((Cd * C0 ^ (N + 1) : NNReal) : ENNReal) * P *
              (ENNReal.ofReal ((δ : ℝ) ^ expN (k - a)) * ENNReal.ofReal ((δ : ℝ) ^ (-ζ))) := by
                  rw [ENNReal.coe_mul, ENNReal.coe_pow]
                  ac_rfl
          _ ≤ ((Cd * C0 ^ (N + 1) : NNReal) : ENNReal) * P * target := mul_le_mul' le_rfl hprod
          _ ≤ (A : ENNReal) ^ (N + 1) * P * target :=
                  mul_le_mul' (mul_le_mul' hCd_C0_le_A le_rfl) le_rfl

/-- **Alternative (i) of GWZ Lemma 7.7(A) with the block constant carried as an explicit power.**
This removes the fixed-polylogarithmic hypothesis on the block constant: the error is
`A^{N+1} Cb^p δ^{-5ε}` with `p` any bound on the cardinality of the cut set, and `A` depends only on
the ambient dimension, on `ε` and on `Cu`.  This is the form the amended Lemma 7.7(A) consumes. -/
theorem isFrostmanAtEveryScale_of_cuts_blockPow_uniform (hn : Module.finrank ℝ E = 3)
    {ε : ℝ} (hεpos : 0 < ε) (hε64 : ε ≤ 1 / 64) (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ A : NNReal, 1 ≤ A ∧
      ∀ (N : ℕ), 0 < N → 1 ≤ ε ^ 2 * (N : ℝ) →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 →
      δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      UniformTubeSet s T N Cu →
      ComparableFibreCounts s T (gridScales δ N) Cu →
      ∀ Cb : NNReal, 1 ≤ Cb →
      ∀ p : ℕ, 1 ≤ p →
      ∀ S : Finset ℕ, S.card ≤ p → 3 ≤ S.card → 0 ∈ S → N ∈ S → S ⊆ Finset.range (N + 1) →
      ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ ε * ε →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
        BlockFrostman s T N Cb ζ a b ∧ ¬ IsLongBlock N ε a b) →
      (∀ i₀ ∈ s,
        ConvexSpaceBody.frostmanConstant (fibreIndex s T δ 1 i₀) (fibreBodies T δ)
            ((T i₀).rescale 1).toConvexSpaceBody
          ≤ (Cb : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-ζ))) →
      StickyKakeya.IsFrostmanAtEveryScale s T
        ((A : ENNReal) ^ (N + 1) * (Cb : ENNReal) ^ p *
          ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε)))) := by
  obtain ⟨Ag, hAg1, hA⟩ := gridScale_le_of_cuts_blockPow_uniform (E := E) hn ε hεpos Cu hCu
  obtain ⟨C₂, hC₂, hD⟩ := isFrostmanAtEveryScale_of_grid_bounds_factor (E := E) hn ε Cu hCu
  refine ⟨C₂ * Ag, one_le_mul hC₂ hAg1, ?_⟩
  intro N hN hεN ι δ hδ hδ1 hδ0 s T hball huni hcomp Cb hCb1 p hp S hScardp hScard h0 hNS hsub ζ hζ0
    hζεε hinv hbase
  have hN16 : 16 ≤ N := by
    by_contra hnot
    have hcast : (N : ℝ) ≤ 15 := by exact_mod_cast (by omega : N ≤ 15)
    have hε2 : ε ^ 2 ≤ (1 : ℝ) / 4096 := by nlinarith
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  let Lgrid : ENNReal := (Ag : ENNReal) ^ (N + 1) * (Cb : ENNReal) ^ p
  have hLgrid : 1 ≤ Lgrid := by
    simpa only [one_mul] using mul_le_mul'
      (one_le_pow₀ (by exact_mod_cast hAg1 : (1 : ENNReal) ≤ (Ag : ENNReal)))
      (one_le_pow₀ (by exact_mod_cast hCb1 : (1 : ENNReal) ≤ (Cb : ENNReal)))
  have hζ'0 : 0 ≤ ζ + 4 * ε + 6 * ε ^ 2 := by linarith [sq_nonneg ε]
  have hA' := hD N hN16 hεN hδ hδ1 hδ0 s T hball huni hcomp
    Lgrid hLgrid (ζ + 4 * ε + 6 * ε ^ 2) hζ'0 fun k hk i₀ hi₀ =>
      hA N hN hεN hδ hδ1 hδ0 s T hball huni hcomp Cb hCb1 p hp S hScardp hScard h0 hNS
        hsub ζ hζ0 hinv hbase k hk i₀ hi₀
  refine hA'.mono_constant ?_
  have hB := (eps_margin_arithmetic hεpos hε64 hζ0 hζεε).2
  have hQle : ENNReal.ofReal ((δ : ℝ) ^ (-(ζ + 4 * ε + 6 * ε ^ 2 + 12 * ε ^ 2))) ≤
      ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε))) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge
      (by exact_mod_cast hδ : (0 : ℝ) < (δ : ℝ)) hδ1 (neg_le_neg (by linarith)))
  have hC_pow : (C₂ : ENNReal) * (Ag : ENNReal) ^ (N + 1) ≤
      ((C₂ * Ag : NNReal) : ENNReal) ^ (N + 1) := by
    rw [ENNReal.coe_mul, mul_pow]
    exact mul_le_mul' (le_self_pow
      (by exact_mod_cast hC₂ : (1 : ENNReal) ≤ (C₂ : ENNReal)) (by omega : N + 1 ≠ 0)) le_rfl
  calc
    (C₂ : ENNReal) * Lgrid * ENNReal.ofReal ((δ : ℝ) ^ (-(ζ + 4 * ε + 6 * ε ^ 2 + 12 * ε ^ 2)))
        = (C₂ * (Ag : ENNReal) ^ (N + 1) * (Cb : ENNReal) ^ p) *
            ENNReal.ofReal ((δ : ℝ) ^ (-(ζ + 4 * ε + 6 * ε ^ 2 + 12 * ε ^ 2))) := by
            simp only [Lgrid, mul_assoc]
    _ ≤ ((C₂ * Ag : NNReal) : ENNReal) ^ (N + 1) * (Cb : ENNReal) ^ p *
          ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε))) :=
          mul_le_mul' (mul_le_mul' hC_pow le_rfl) hQle

end MultiScaleFac

end Kakeya
