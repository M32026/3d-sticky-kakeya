/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallCoreRestrictBalls
public import Kakeya.DimensionThree.MainLemma2.BallDimsPigeonhole
public import Kakeya.DimensionThree.Slab.Multiplicity

/-!
# Gluing the per-ball data of Lemma 9.2 into the global `BallData` inputs

General-branch steps **G5a**.
`Kakeya.VeryNotSticky.exists_ballFactoring_core` is a **per-ball** existential producing, in each
ball `B`, a body family `parts`, bodies `Wb : Finset core.σ → ConvexSpaceBody E₃` and a block map
`blk : core.σ → Finset core.σ`. `Kakeya.VeryNotSticky.BallDataCore.toBallData` wants **one**
global `(ω, bodies, Wb, blk)`. This file supplies the five pieces the gluing needs.

## (i) Each retained segment has a *unique* ball, so the global tag is well defined

Tagging by ball — `ω := core.bι × Finset core.σ`, `blk p := (ballTag p, blk_{ballTag p} p)` — is
the only way to keep `Wb` well defined, and it requires each segment to lie in the segment
family of **exactly one** ball, which no `BallDataCore` field states. It is nevertheless
provable as soon as the segment's shade is non-empty:
`Kakeya.VeryNotSticky.ball_unique_of_shade_nonempty` derives it from `Y_piece` (the shade lies
in its ball's piece) and `P_disjoint` (the pieces are disjoint). The shade *is* non-empty on
the Markov tier: `Kakeya.VeryNotSticky.carrier_volume_pos` gives `|T_B| > 0` from
`segs_thickness` and `Kakeya.HasThicknesses.le_volume`, and `segs_density` —
which `Kakeya.VeryNotSticky.markovDyadicTierCore_segs_density` delivers verbatim — then forces
`|Y_B(T_B)| > 0`. `Kakeya.VeryNotSticky.BallDataCore.ballTag` is the resulting tag and
`Kakeya.VeryNotSticky.ballTag_eq_of_segs_density` is its correctness.

## (ii) The block-inhabitation clause, additively

`exists_ballFactoring_core` does not expose `∀ j ∈ parts, ∃ p ∈ s', blk p = j`, and that clause
cannot be derived from its ten exposed clauses (obligation `G4-O1`). Rather than modify G2,
`Kakeya.VeryNotSticky.exists_ballFactoring_core_inhab` delivers it **additively**, by pruning the
uninhabited parts: every clause of `exists_ballFactoring_core` is universally quantified over
`parts` except `bodies_antiClustering`, which is monotone in the family
(`Kakeya.maxDensity_mono`). G2's pin stays intact for its other readers.

## (iii) The tier retention is absorbable

`Kakeya.VeryNotSticky.tierRetention` is `2 (⌈log₂ (1/(c₁ δ^{2η}))⌉₊ + 1)`, polylogarithmic in
`1/δ`. `Kakeya.VeryNotSticky.eventually_le_rpow_neg_of_polylog` is the reusable absorber — any
`NNReal`-valued function of `δ` bounded by `A + B log₂ (1/δ)` is eventually `≤ δ^{-ε}` — and
`Kakeya.VeryNotSticky.eventually_tierRetention_le_rpow` is its instance at the tier's factor.
This is obligation `G3-O1`.

## (iv) Carrier retention becomes shade retention inside one dyadic class

Lemma 9.2's retention is a statement about **carrier** masses; the tier's `hret` binder is
about **shade** masses. Inside one dyadic shade-fraction class the two are comparable up to a
factor `2`: `Kakeya.VeryNotSticky.volume_carrier_le_shadeFractionClass` gives
`|T| ≤ 2^k |Y(T)|` and the minimality
`Kakeya.VeryNotSticky.not_volume_carrier_le_of_lt_shadeFractionClass` gives
`2^k |Y(T)| ≤ 2 |T|`, so `Kakeya.VeryNotSticky.shade_retention_of_carrier_retention` converts a
retention factor `L` into `2 L`. This is obligations `G3-O3`/`G4-O4`. The factor `2` is not
cosmetic: at class `k` the shade fraction is only pinned to the dyadic window `[2^{-k}, 2^{1-k})`.

## (v) No `C₀`-raising construction is needed

`Kakeya.VeryNotSticky.dimsConstant C₀ ρ CF = max C₀ (ρ CF)` collapses to `C₀` as soon as
`ρ CF ≤ 4 ≤ C₀` (`Kakeya.VeryNotSticky.dimsConstant_eq_left_of_le`), and G4's discharged
budget `ρ CF ≤ 4` (`Kakeya.VeryNotSticky.three_halves_mul_lemma92Constant_le`) together with
conjunct 1's `4 ≤ C₀bd` supplies exactly that. So `bd.C₀ = C₀bd` **survives unchanged** and no
`withC₀` operation is owed.

Nothing here changes a existing statement.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped NNReal ENNReal Topology

universe u

namespace Kakeya.VeryNotSticky

variable {cfg : VeryNotSticky.{u}}

/-! ### (i) The ball tag: each retained segment has a unique ball -/

/-- **A segment with non-empty shade lies in the segment family of at most one ball.** The
shade lies in the piece of any ball owning the segment (`Y_piece`) and the pieces are pairwise
disjoint (`P_disjoint`), so a common point forces the balls to agree. This is the fact that
makes a global body-tagging map well defined; no `BallDataCore` field states it. -/
theorem ball_unique_of_shade_nonempty (core : BallDataCore cfg)
    {B B' : core.bι} (hB : B ∈ core.bs) (hB' : B' ∈ core.bs)
    {p : core.σ} (hp : p ∈ core.segs B) (hp' : p ∈ core.segs B')
    (hne : ((core.Y p).shade).Nonempty) : B = B' := by
  by_contra hBB
  obtain ⟨x, hx⟩ := hne
  have h1 : x ∈ core.P B := core.Y_piece B hB p hp hx
  have h2 : x ∈ core.P B' := core.Y_piece B' hB' p hp' hx
  have := core.P_disjoint hB hB' hBB
  exact (Set.disjoint_left.mp this h1) h2

/-- **A segment's carrier has positive volume**: its thickness profile is
`(r₁, δ, δ)` with all three positive, and `Kakeya.HasThicknesses.le_volume` turns that into a
positive lower bound. -/
theorem carrier_volume_pos (core : BallDataCore cfg)
    {B : core.bι} (hB : B ∈ core.bs) {p : core.σ} (hp : p ∈ core.segs B) :
    0 < volume (core.Y p).carrier := by
  have hprof := core.segs_thickness B hB p hp
  have hr : (0 : ℝ) < (cfg.r₁ : ℝ) := by
    have : (0 : NNReal) < cfg.r₁ := NNReal.rpow_pos cfg.hδ
    exact_mod_cast this
  have hd : (0 : ℝ) < (cfg.δ : ℝ) := by exact_mod_cast cfg.hδ
  have hvol := Kakeya.HasThicknesses.le_volume core.hC₀ (core.Y p).toConvexSpaceBody
      hr.le hd.le hd.le hprof
  refine lt_of_lt_of_le ?_ hvol
  rw [ENNReal.ofReal_pos]
  have hC : (0 : ℝ) < (core.C₀ : ℝ) := by
    have := core.hC₀; exact lt_of_lt_of_le zero_lt_one (by exact_mod_cast this)
  positivity

/-- **On the Markov tier the shade of a segment is non-empty.** `segs_density` bounds the shade
mass below by a positive multiple of the carrier mass, which is positive. -/
theorem shade_nonempty_of_segs_density (core : BallDataCore cfg) {c : ENNReal} (hc : c ≠ 0)
    {B : core.bι} (hB : B ∈ core.bs) {p : core.σ} (hp : p ∈ core.segs B)
    (hdens : c * volume (core.Y p).carrier ≤ volume (core.Y p).shade) :
    ((core.Y p).shade).Nonempty := by
  have hpos : 0 < volume (core.Y p).shade :=
    lt_of_lt_of_le (ENNReal.mul_pos hc (carrier_volume_pos core hB hp).ne') hdens
  rw [Set.nonempty_iff_ne_empty]
  intro hemp
  rw [hemp, measure_empty] at hpos
  exact absurd hpos (lt_irrefl 0)

open scoped Classical in
/-- **The ball tag of a segment.** On a segment belonging to some ball this is a ball owning it;
elsewhere it is an arbitrary ball of the (non-empty) family. Its point is
`Kakeya.VeryNotSticky.ballTag_eq_of_segs_density`: on the Markov tier the tag is *the* ball, so
`ω := core.bι × …` gives a well-defined global body index. -/
noncomputable def BallDataCore.ballTag (core : BallDataCore cfg) (p : core.σ) : core.bι :=
  if h : ∃ B, B ∈ core.bs ∧ p ∈ core.segs B then h.choose else core.bs_nonempty.choose

open scoped Classical in
/-- The tag of a segment of some ball is a ball owning that segment. -/
theorem ballTag_spec (core : BallDataCore cfg) {B : core.bι} (hB : B ∈ core.bs) {p : core.σ}
    (hp : p ∈ core.segs B) :
    core.ballTag p ∈ core.bs ∧ p ∈ core.segs (core.ballTag p) := by
  classical
  have h : ∃ B, B ∈ core.bs ∧ p ∈ core.segs B := ⟨B, hB, hp⟩
  rw [BallDataCore.ballTag, dif_pos h]
  exact h.choose_spec

open scoped Classical in
/-- **The tag is correct on segments with non-empty shade.** -/
theorem ballTag_eq_of_shade_nonempty (core : BallDataCore cfg) {B : core.bι} (hB : B ∈ core.bs)
    {p : core.σ} (hp : p ∈ core.segs B) (hne : ((core.Y p).shade).Nonempty) :
    core.ballTag p = B := by
  obtain ⟨hmem, hseg⟩ := ballTag_spec core hB hp
  exact ball_unique_of_shade_nonempty core hmem hB hseg hp hne

open scoped Classical in
/-- **The tag is correct on the Markov tier**, i.e. whenever the core carries the `segs_density`
binder of `Kakeya.VeryNotSticky.BallDataCore.toBallData`. This is the well-definedness the
per-ball → global gluing of Lemma 9.2's data rests on. -/
theorem ballTag_eq_of_segs_density (core : BallDataCore cfg) {c₁ : NNReal} (hc₁ : 0 < c₁)
    (hdens : ∀ B ∈ core.bs, ∀ p ∈ core.segs B,
      (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) * volume (core.Y p).carrier ≤
        volume (core.Y p).shade)
    {B : core.bι} (hB : B ∈ core.bs) {p : core.σ} (hp : p ∈ core.segs B) :
    core.ballTag p = B := by
  have hc : (c₁ : ENNReal) * (cfg.δ : ENNReal) ^ (2 * cfg.η) ≠ 0 := by
    refine (ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr hc₁.ne') ?_).ne'
    exact (ENNReal.rpow_pos (by exact_mod_cast cfg.hδ) ENNReal.coe_ne_top).ne'
  exact ballTag_eq_of_shade_nonempty core hB hp
    (shade_nonempty_of_segs_density core hc hB hp (hdens B hB p hp))

/-! ### (ii) The block-inhabitation clause of the per-ball factoring -/

open scoped Classical in
/-- **`Kakeya.VeryNotSticky.exists_ballFactoring_core` with the block-inhabitation clause**
(obligation `G4-O1`), delivered additively rather than by identification G2. The extra last clause
`∀ j ∈ parts, ∃ p ∈ s', blk p = j` is what a global body family needs in order that
`bodies B` contain no phantom body; it is obtained by pruning the uninhabited parts, which is
sound because every other clause is universally quantified over `parts` and
`bodies_antiClustering` is monotone in the family. -/
theorem exists_ballFactoring_core_inhab (cfg : VeryNotSticky.{u}) (core : BallDataCore cfg)
    {B : core.bι} (hB : B ∈ core.bs) :
    ∃ (s' : Finset core.σ) (parts : Finset (Finset core.σ))
      (Wb : Finset core.σ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
      (blk : core.σ → Finset core.σ),
      s' ⊆ core.segs B ∧
      (∑ p ∈ core.segs B, volume (core.Y p).carrier ≤
        ConvexSpaceBody.nonempty_biasedFactorization.L 3 (core.segs B).card (cfg.δ / cfg.r₁)
            cfg.ϱ *
          ∑ p ∈ s', volume (core.Y p).carrier) ∧
      (∀ p ∈ s', blk p ∈ parts) ∧
      (∀ p ∈ s', (core.Y p).toConvexSpaceBody ≤ Wb (blk p)) ∧
      (∀ j ∈ parts, (Wb j).carrier ⊆ closedBall (core.ctr B) (cfg.r₁ : ℝ)) ∧
      (∀ j ∈ parts,
        ConvexSpaceBody.IsFrostmanIn (s'.filter fun p => blk p = j)
          (fun p => (core.Y p).toConvexSpaceBody) (Wb j) (lemma92Constant cfg.ϱ)) ∧
      (∀ j ∈ parts,
        ∀ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)), K ≤ Wb j →
          densityIn (s'.filter fun p => blk p = j)
              (fun p => (core.Y p).toConvexSpaceBody) K ≤
            (lemma92Bias core.C₀ cfg.ϱ : ENNReal) *
              (volume K.carrier / volume (Wb j).carrier) ^ cfg.ϱ *
              densityIn (s'.filter fun p => blk p = j)
                (fun p => (core.Y p).toConvexSpaceBody) (Wb j)) ∧
      maxDensity parts Wb ≤
        (lemma92Bias core.C₀ cfg.ϱ : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) ∧
      (∀ j ∈ parts,
        (lemma92Constant cfg.ϱ : ENNReal)⁻¹ *
            (volume (Wb j).carrier / volume (closedBall (core.ctr B) (cfg.r₁ : ℝ))) ^ cfg.ϱ *
            maxDensity s' (fun p => (core.Y p).toConvexSpaceBody) ≤
          densityIn (s'.filter fun p => blk p = j)
            (fun p => (core.Y p).toConvexSpaceBody) (Wb j)) ∧
      (∀ j ∈ parts, ∀ j' ∈ parts,
        ethickness ℝ (Wb j).carrier ≤ lemma92Constant cfg.ϱ • ethickness ℝ (Wb j').carrier) ∧
      (∀ j ∈ parts, ∃ p ∈ s', blk p = j) := by
  classical
  obtain ⟨s', parts, Wb, blk, hs', hret, hmem, hle, hball, hfro, hbias, hanti, hdens, hsim⟩ :=
    exists_ballFactoring_core cfg core hB
  refine ⟨s', parts.filter fun j => ∃ p ∈ s', blk p = j, Wb, blk, hs', hret, ?_, hle,
    fun j hj => hball j (Finset.mem_filter.1 hj).1,
    fun j hj => hfro j (Finset.mem_filter.1 hj).1,
    fun j hj => hbias j (Finset.mem_filter.1 hj).1, ?_,
    fun j hj => hdens j (Finset.mem_filter.1 hj).1,
    fun j hj j' hj' => hsim j (Finset.mem_filter.1 hj).1 j' (Finset.mem_filter.1 hj').1,
    fun j hj => (Finset.mem_filter.1 hj).2⟩
  · intro p hp
    exact Finset.mem_filter.2 ⟨hmem p hp, p, hp, rfl⟩
  · exact le_trans (maxDensity_mono Wb (Finset.filter_subset _ _)) hanti

/-! ### (iii) Absorbing a polylogarithmic loss constant -/

/-- **The reusable absorber.** A `NNReal`-valued function of the scale which is bounded by
`A + B log₂ (1/δ)` is eventually below `δ^{-ε}`, for every `ε > 0`. Every loss constant the
general branch accumulates — the tier retention, the dims-class loss, the heavy-ball factor —
is of that shape, which is exactly what `Kakeya.VeryNotSticky.BallData`'s `Cg` field asks
(`hCg` records only `1 ≤ Cg`; the consumers read `Cg ≤ δ^{-ε}`). -/
theorem eventually_le_rpow_neg_of_polylog {f : NNReal → NNReal} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ d : NNReal, 0 < d → d ≤ 1 → (f d : ℝ) ≤ A + B * Real.logb 2 ((d : ℝ))⁻¹)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ((f d : NNReal) : ENNReal) ≤ (d : ENNReal) ^ (-ε) := by
  have hkey : ∀ᶠ x : ℝ in atTop, A + B * Real.logb 2 x ≤ x ^ ε := by
    have h1 := polylog_rpow_atTop (ρ := (2 : ℝ)) (by norm_num) (ε := ε / 2) (by linarith)
    have h2 : ∀ᶠ x : ℝ in atTop, A + B ≤ x ^ (ε / 2) :=
      (tendsto_rpow_atTop (y := ε / 2) (by linarith)).eventually_ge_atTop (A + B)
    filter_upwards [h1, h2, eventually_ge_atTop (1 : ℝ)] with x hx1 hx2 hx3
    have hL : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx3
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx3
    have hnn : (0 : ℝ) ≤ (1 + Real.logb 2 x) ^ 2 := by positivity
    have hstep : A + B * Real.logb 2 x ≤ (A + B) * (1 + Real.logb 2 x) ^ 2 := by
      nlinarith [mul_nonneg hA hL, mul_nonneg hB hL, mul_nonneg hA (mul_nonneg hL hL),
        mul_nonneg hB (mul_nonneg hL hL)]
    calc A + B * Real.logb 2 x ≤ (A + B) * (1 + Real.logb 2 x) ^ 2 := hstep
      _ ≤ x ^ (ε / 2) * x ^ (ε / 2) := by
          refine mul_le_mul hx2 hx1 hnn (le_trans (by linarith) hx2)
      _ = x ^ ε := by rw [← Real.rpow_add hx0]; norm_num
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hkey
  have hmax : (0 : ℝ) < max x₀ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have ht0 : (0 : ℝ≥0) < ((max x₀ 1)⁻¹).toNNReal := Real.toNNReal_pos.2 (inv_pos.2 hmax)
  have htc : (((max x₀ 1)⁻¹).toNNReal : ℝ) = (max x₀ 1)⁻¹ :=
    Real.coe_toNNReal _ (le_of_lt (inv_pos.2 hmax))
  filter_upwards [Ioo_mem_nhdsGT ht0] with d hd
  have hd0 : 0 < d := hd.1
  have hd0R : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hdt : (d : ℝ) < (max x₀ 1)⁻¹ := by
    have h := NNReal.coe_lt_coe.2 hd.2
    rwa [htc] at h
  have hx : max x₀ 1 ≤ ((d : ℝ))⁻¹ := by
    rw [le_inv_comm₀ hmax hd0R]
    exact hdt.le
  have hd1 : d ≤ 1 := by
    have h1 : (d : ℝ) ≤ 1 := by
      have : (max x₀ 1)⁻¹ ≤ 1 := by
        rw [inv_le_one_iff₀]
        exact Or.inr (le_max_right _ _)
      linarith
    exact_mod_cast h1
  have key := hx₀ ((d : ℝ))⁻¹ (le_trans (le_max_left _ _) hx)
  have hreal : (f d : ℝ) ≤ ((d : ℝ))⁻¹ ^ ε := le_trans (hf d hd0 hd1) key
  have hnn : (f d : ℝ≥0) ≤ d ^ (-ε) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_rpow, Real.rpow_neg hd0R.le,
      ← Real.inv_rpow hd0R.le]
    simpa using hreal
  calc ((f d : NNReal) : ENNReal) ≤ ((d ^ (-ε) : ℝ≥0) : ENNReal) := by exact_mod_cast hnn
    _ = (d : ENNReal) ^ (-ε) := ENNReal.coe_rpow_of_ne_zero hd0.ne' _

/-- The tier retention factor of `Kakeya.VeryNotSticky.tierRetention` as a function of the scale
alone, so that it can be read along the filter `𝓝[>] 0`. -/
noncomputable def tierRetentionAt (c₁ d : NNReal) (η : ℝ) : NNReal :=
  2 * ((shadeFractionClassBound (c₁ * d ^ (2 * η)) + 1 : ℕ) : NNReal)

@[simp] theorem tierRetention_eq_tierRetentionAt (cfg : VeryNotSticky.{u}) (c₁ : NNReal) :
    tierRetention cfg c₁ = tierRetentionAt c₁ cfg.δ cfg.η := rfl

/-- `⌈x⌉₊ ≤ max x 0 + 1` in `ℝ`, valid without a sign hypothesis. -/
theorem natCeil_le_max_add_one (x : ℝ) : ((⌈x⌉₊ : ℕ) : ℝ) ≤ max x 0 + 1 := by
  rcases le_total x 0 with h | h
  · have h0 : ⌈x⌉₊ = 0 := Nat.ceil_eq_zero.2 h
    have hm : (0 : ℝ) ≤ max x 0 := le_max_right _ _
    rw [h0]
    push_cast
    linarith
  · have h1 : ((⌈x⌉₊ : ℕ) : ℝ) < x + 1 := Nat.ceil_lt_add_one h
    have h2 : x ≤ max x 0 := le_max_left _ _
    linarith

/-- **The tier retention factor is polylogarithmic in `1/δ`**, with the explicit envelope
`A + B log₂(1/δ)` at `A = 2 max (log₂ (1/c₁)) 0 + 4` and `B = 4 η`. -/
theorem tierRetentionAt_le_polylog {c₁ : NNReal} (hc₁ : 0 < c₁) {η : ℝ} (hη : 0 ≤ η)
    {d : NNReal} (hd : 0 < d) (hd1 : d ≤ 1) :
    ((tierRetentionAt c₁ d η : NNReal) : ℝ) ≤
      (2 * max (Real.logb 2 ((c₁ : ℝ))⁻¹) 0 + 4) + (4 * η) * Real.logb 2 ((d : ℝ))⁻¹ := by
  have hlogb_rpow : ∀ x y : ℝ, 0 < x → Real.logb 2 (x ^ y) = y * Real.logb 2 x := by
    intro x y hx
    rw [Real.logb, Real.logb, Real.log_rpow hx]
    ring
  have hc₁R : (0 : ℝ) < (c₁ : ℝ) := hc₁
  have hdR : (0 : ℝ) < (d : ℝ) := hd
  have hd1R : (d : ℝ) ≤ 1 := hd1
  set L : ℝ := Real.logb 2 ((d : ℝ))⁻¹ with hL
  have hLnn : 0 ≤ L := by
    rw [hL]
    refine Real.logb_nonneg (by norm_num) ?_
    rw [le_inv_comm₀ zero_lt_one hdR]
    simpa using hd1R
  have hηL : (0 : ℝ) ≤ (2 * η) * L := mul_nonneg (by linarith) hLnn
  have hcoe : ((c₁ * d ^ (2 * η) : NNReal) : ℝ) = (c₁ : ℝ) * (d : ℝ) ^ (2 * η) := by
    rw [NNReal.coe_mul, NNReal.coe_rpow]
  have hLd : Real.logb 2 (d : ℝ) = -L := by rw [hL, Real.logb_inv]; ring
  have hd2 : (((d : ℝ) ^ (2 * η))⁻¹) = (d : ℝ) ^ (-(2 * η)) :=
    (Real.rpow_neg hdR.le (2 * η)).symm
  have hX : Real.logb 2 (((c₁ * d ^ (2 * η) : NNReal) : ℝ))⁻¹ =
      Real.logb 2 ((c₁ : ℝ))⁻¹ + (2 * η) * L := by
    rw [hcoe, mul_inv, Real.logb_mul (by positivity) (by positivity), hd2,
      hlogb_rpow _ _ hdR, hLd]
    ring
  have hceil : ((shadeFractionClassBound (c₁ * d ^ (2 * η)) : ℕ) : ℝ) ≤
      max (Real.logb 2 ((c₁ : ℝ))⁻¹) 0 + (2 * η) * L + 1 := by
    have hdef : shadeFractionClassBound (c₁ * d ^ (2 * η))
        = ⌈Real.logb 2 (((c₁ * d ^ (2 * η) : NNReal) : ℝ))⁻¹⌉₊ := rfl
    rw [hdef]
    refine le_trans (natCeil_le_max_add_one _) ?_
    have h0 : (0 : ℝ) ≤ max (Real.logb 2 ((c₁ : ℝ))⁻¹) 0 := le_max_right _ _
    have hmx : max (Real.logb 2 (((c₁ * d ^ (2 * η) : NNReal) : ℝ))⁻¹) 0 ≤
        max (Real.logb 2 ((c₁ : ℝ))⁻¹) 0 + (2 * η) * L := by
      refine max_le ?_ (by linarith)
      rw [hX]
      linarith [le_max_left (Real.logb 2 ((c₁ : ℝ))⁻¹) (0 : ℝ)]
    linarith
  unfold tierRetentionAt
  push_cast
  linarith

/-- **Obligation `G3-O1`: the tier retention is absorbable.** -/
theorem eventually_tierRetentionAt_le_rpow {c₁ : NNReal} (hc₁ : 0 < c₁) {η : ℝ} (hη : 0 ≤ η)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      ((tierRetentionAt c₁ d η : NNReal) : ENNReal) ≤ (d : ENNReal) ^ (-ε) :=
  eventually_le_rpow_neg_of_polylog
    (A := 2 * max (Real.logb 2 ((c₁ : ℝ))⁻¹) 0 + 4) (B := 4 * η)
    (by positivity) (by positivity)
    (fun d hd hd1 => tierRetentionAt_le_polylog hc₁ hη hd hd1) hε

/-- The same, in the shape the general-branch producers read it: at every configuration whose
scale and `η` are pinned. -/
theorem eventually_tierRetention_le_rpow {c₁ : NNReal} (hc₁ : 0 < c₁) {η : ℝ} (hη : 0 ≤ η)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : NNReal in 𝓝[>] 0, ∀ cfg : VeryNotSticky.{u}, cfg.δ = d → cfg.η = η →
      ((tierRetention cfg c₁ : NNReal) : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-ε) := by
  filter_upwards [eventually_tierRetentionAt_le_rpow hc₁ hη hε] with d hd cfg hδ hη'
  rw [tierRetention_eq_tierRetentionAt, hδ, hη']
  exact hd

/-! ### (iv) Carrier retention becomes shade retention inside one dyadic class -/

/-- **Obligations `G3-O3`/`G4-O4`: carrier retention becomes shade retention, at the cost of a
factor `2`.** Inside one dyadic shade-fraction class `k` the two mass functionals are
comparable: `|T| ≤ 2^k |Y(T)|` by the definition of the class and `2^k |Y(T)| ≤ 2 |T|` by its
minimality. So a retention factor `L` for the carriers is a retention factor `2 L` for the
shades. This is what converts Lemma 9.2's output — a statement about carrier masses — into the
`hret` binder of `Kakeya.VeryNotSticky.tierCore`, which is about shade masses. -/
theorem shade_retention_of_carrier_retention (core : BallDataCore cfg)
    {base s' : Finset core.σ} (hs' : s' ⊆ base) {k : ℕ}
    (hcl : ∀ p ∈ base, shadeFractionClass core p = k)
    (hmk : ∀ p ∈ base, ∃ N : ℕ,
      volume (core.Y p).carrier ≤ 2 ^ N * volume (core.Y p).shade)
    {L : ENNReal}
    (hret : ∑ p ∈ base, volume (core.Y p).carrier ≤
      L * ∑ p ∈ s', volume (core.Y p).carrier) :
    ∑ p ∈ base, volume (core.Y p).shade ≤ 2 * L * ∑ p ∈ s', volume (core.Y p).shade := by
  -- upper: `|T| ≤ 2^k |Y(T)|` on `base`
  have hup : ∀ p ∈ base, volume (core.Y p).carrier ≤ 2 ^ k * volume (core.Y p).shade := by
    intro p hp
    obtain ⟨N, hN⟩ := hmk p hp
    have := volume_carrier_le_shadeFractionClass core hN
    rwa [hcl p hp] at this
  -- lower: `2^k |Y(T)| ≤ 2 |T|` on `base`, by minimality of the class
  have hlow : ∀ p ∈ base, 2 ^ k * volume (core.Y p).shade ≤ 2 * volume (core.Y p).carrier := by
    intro p hp
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero, one_mul]
      calc volume (core.Y p).shade ≤ volume (core.Y p).carrier :=
            measure_mono (core.Y p).shade_subset
        _ ≤ 2 * volume (core.Y p).carrier := le_mul_of_one_le_left zero_le (by norm_num)
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hlt : j < shadeFractionClass core p := by rw [hcl p hp]; omega
      have hstrict : 2 ^ j * volume (core.Y p).shade ≤ volume (core.Y p).carrier :=
        le_of_lt (not_le.1 (not_volume_carrier_le_of_lt_shadeFractionClass core hlt))
      calc (2 : ENNReal) ^ (j + 1) * volume (core.Y p).shade
          = 2 * (2 ^ j * volume (core.Y p).shade) := by rw [pow_succ]; ring
        _ ≤ 2 * volume (core.Y p).carrier := by gcongr
  have h2k0 : (2 : ENNReal) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2ktop : (2 : ENNReal) ^ k ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  have hchain : (∑ p ∈ base, volume (core.Y p).shade) * 2 ^ k ≤
      (2 * L * ∑ p ∈ s', volume (core.Y p).shade) * 2 ^ k := by
    calc (∑ p ∈ base, volume (core.Y p).shade) * 2 ^ k
        = ∑ p ∈ base, 2 ^ k * volume (core.Y p).shade := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun p _ => mul_comm _ _
      _ ≤ ∑ p ∈ base, 2 * volume (core.Y p).carrier := Finset.sum_le_sum hlow
      _ = 2 * ∑ p ∈ base, volume (core.Y p).carrier := by rw [Finset.mul_sum]
      _ ≤ 2 * (L * ∑ p ∈ s', volume (core.Y p).carrier) := by gcongr
      _ ≤ 2 * (L * ∑ p ∈ s', 2 ^ k * volume (core.Y p).shade) := by
          gcongr with p hp
          exact hup p (hs' hp)
      _ = (2 * L * ∑ p ∈ s', volume (core.Y p).shade) * 2 ^ k := by
          rw [← Finset.mul_sum]; ring
  exact (ENNReal.mul_le_mul_iff_left h2k0 h2ktop).1 hchain

/-! ### (v) `dimsConstant` collapses: no `C₀`-raising construction -/

/-- **`dimsConstant C₀ ρ CF = C₀` whenever `ρ CF ≤ 4 ≤ C₀`.** With conjunct 1's `4 ≤ C₀bd` and
G4's discharged budget `ρ CF ≤ 4` (`Kakeya.VeryNotSticky.three_halves_mul_lemma92Constant_le`)
the dimensions pigeonhole returns the thickness profile at the *unchanged* constant, so
`bd.C₀ = C₀bd` survives and no `withC₀` operation is owed. -/
theorem dimsConstant_eq_left_of_le {C₀ ρ CF : NNReal} (h4 : 4 ≤ C₀) (hb : ρ * CF ≤ 4) :
    dimsConstant C₀ ρ CF = C₀ := by
  unfold dimsConstant
  exact max_eq_left (le_trans hb h4)

/-- The instance the general branch uses: at the ratio `ρ = 3/2` and Lemma 9.2's constant, with
`ϱ ≤ 1/21`, the dimensions constant is the input `C₀` itself. -/
theorem dimsConstant_eq_left_of_lemma92 {C₀ : NNReal} (h4 : 4 ≤ C₀) {ϱ : ℝ} (hϱ : ϱ ≤ 1 / 21) :
    dimsConstant C₀ (3 / 2) (lemma92Constant ϱ) = C₀ :=
  dimsConstant_eq_left_of_le h4 (three_halves_mul_lemma92Constant_le hϱ)

end Kakeya.VeryNotSticky
