/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Factoring
public import Kakeya.StickyKakeya.BallReduction
public import Kakeya.Factoring.Pigeonhole

/-!
# Multiplicity bounds at an ambient radius `R > 1`

The `b`-scale plank tubes of the coarse endgame do **not** lie in the unit ball, and cannot be
made to: a `Kakeya.Tube` has core length exactly `1`, so a tube attached to a plank that hugs
`∂B₁` necessarily pokes out.  What `Kakeya.ml1Boot.plankTube_carrier_subset_closedBall` gives is
containment in `closedBall 0 (3/2 + √3 + C b)`, and `3/2 + √3 > 1` is not slack.

Every consumer of those tubes, however, only ever uses the unit-ball hypothesis to feed the
family to a *multiplicity upper bound* stated in `B₁`.  This file supplies the missing reduction:
an upper bound valid for families in `B₁` upgrades, at a dimensional constant, to one valid for
families in `B_R` for any `δ`-independent `R ≥ 1`.

## The reduction

Three steps, none of which moves the tubes:

1. **Discard the sparsely shaded tubes** (`_root_.ShadedBody.discardLowShading` at level `1/2`).  What
   survives carries half the shade mass, so the multiplicity of the whole is at most twice that
   of the survivors, and — this is the point — *every* member of the survivors has shade density
   at least `λ / 2`, hence so does every subfamily of it.  This is what makes the fullness
   hypothesis descend to the cells of step 2, which it does not do without the discard.
2. **Cut `B_R` into `O(1)` cells.**  `Kakeya.StickyKakeya.exists_ball_assignment` provides a
   finite set `xs` of centres, depending only on `R`, such that every `b`-tube in `B_R` with
   `b ≤ 1/4` lies in `closedBall x 1` for some `x ∈ xs`.  Assigning each tube such a centre
   partitions the index set, and `Kakeya.ml1Boot.multiplicity_le_sum_fiberwise` bounds the
   multiplicity of the whole by the sum of the cells' multiplicities.
3. **Translate each cell into `B₁`** and apply the hypothesis there.  Multiplicity, fullness and
   `maxDensity` are all translation invariant (`ShadedBody.multiplicity_translate_const`,
   `ShadedBody.fullness_translate_const`, `Kakeya.StickyKakeya.maxDensity_tube_translate`), so
   nothing has to be carried back by hand.

The total loss is `2 * xs.card`, a constant fixed before the scale, which the consumers absorb
into their subpolynomial factor.

## The plank-width side condition

Step 2 needs `b ≤ 1/4`.  On the Section 8 route the `b`-tube scale is
`Kakeya.ml1Boot.plankPigeonhole.C * bp` with `bp ≤ 2 * δ̃ ^ (6 ε)`, so the condition is bought
from the eventually-filter: `Kakeya.ml1Boot.eventually_mul_two_rpow_le`.  This is also exactly
the hypothesis `hbq1` of the two `b`-tube producers, and
`Kakeya.ml1Boot.plankTube_carrier_subset_closedBall_of_le` reads the same condition to place the
tubes in `closedBall 0 (9/2)`; the three demands coincide and are discharged together.

## Main statements

* `Kakeya.ml1Boot.eventually_nnreal_rpow_le`, `Kakeya.ml1Boot.eventually_mul_two_rpow_le`: the
  plank-width side condition, bought from the filter;
* `Kakeya.ml1Boot.multiplicity_le_sum_fiberwise`: multiplicity is subadditive along a partition
  of the index set;
* `Kakeya.ml1Boot.multiplicity_le_of_ball_of_unitBall`: the reduction itself.
-/

@[expose] public section

open MeasureTheory ShadedBody Filter Topology Metric
open scoped NNReal ENNReal

namespace Kakeya

namespace ml1Boot

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ### The plank-width side condition -/

/-- **A positive power of the scale is eventually below any positive constant.**

The threshold is `c ^ (1 / e)`; monotonicity of `NNReal.rpow` in the base does the rest.  This is
the `NNReal`-valued companion of `Kakeya.ml1Boot.eventually_rpow_le`, which lands in `ENNReal`
and is awkward to use against a hypothesis stated in `ℝ`. -/
theorem eventually_nnreal_rpow_le {c : NNReal} (hc : 0 < c) {e : ℝ} (he : 0 < e) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, δ ^ e ≤ c := by
  have hc' : 0 < c ^ (1 / e) := NNReal.rpow_pos hc
  filter_upwards [eventually_le_nhdsGT hc'] with δ hδ
  calc δ ^ e ≤ (c ^ (1 / e)) ^ e := NNReal.rpow_le_rpow hδ he.le
    _ = c := by
        rw [← NNReal.rpow_mul, one_div_mul_cancel (ne_of_gt he), NNReal.rpow_one]

/-- **The plank-width side condition, bought from the eventually-filter.**

For a constant `C` fixed before the scale and a positive exponent `e`, every `b` bounded by
`2 δ ^ e` satisfies `C * b ≤ c`, once `δ` is small enough.

This is the honest form of the obligation that the ledger of
`Kakeya.ml1Boot.multTildeT_of_planksClose` records as the plank-width smallness `hbq1`.  It is
*not* a statement about `b_p` that needs a numerical value of the constant: only `C`'s finiteness
and `0 < e` are used, so the numeral `plankPigeonhole.C = 6144` never has to be computed.  What
makes it available is that `b_p` is quantified *inside* the `∀ᶠ δ̃` of that statement, with
`b_p ≤ 2 δ̃ ^ (6 ε)` in scope and `ε` fixed before `δ̃`. -/
theorem eventually_mul_two_rpow_le (C : NNReal) {e : ℝ} (he : 0 < e) {c : NNReal} (hc : 0 < c) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, ∀ b : NNReal, b ≤ 2 * δ ^ e → C * b ≤ c := by
  have hdenpos : (0 : NNReal) < 2 * C + 1 := lt_of_lt_of_le zero_lt_one le_add_self
  have hthr : 0 < c / (2 * C + 1) := div_pos hc hdenpos
  filter_upwards [eventually_nnreal_rpow_le hthr he] with δ hδ b hb
  have step : C * b ≤ 2 * C * (c / (2 * C + 1)) := by
    calc C * b ≤ C * (2 * δ ^ e) := by gcongr
      _ = 2 * C * δ ^ e := by ring
      _ ≤ 2 * C * (c / (2 * C + 1)) := by gcongr
  refine step.trans ?_
  rw [← mul_div_assoc, div_le_iff₀ hdenpos]
  calc 2 * C * c ≤ 2 * C * c + c := le_self_add
    _ = c * (2 * C + 1) := by ring

/-! ### Multiplicity is subadditive along a partition of the index set -/

/-- **Multiplicity is subadditive along a partition of the index set.**

If `g` maps `t` into `xs`, then the multiplicity of `(t, V)` is at most the sum, over `x ∈ xs`,
of the multiplicities of the fibres `{i ∈ t | g i = x}`.

The numerator splits exactly, `∑_{i ∈ t} |Y i| = ∑_{x ∈ xs} ∑_{i ∈ t, g i = x} |Y i|`, while the
denominator only shrinks along a fibre, `|⋃_{fibre} Y| ≤ |⋃_t Y|`, and a smaller denominator makes
a larger quotient.  Nothing is assumed about `V` and no nondegeneracy is needed: in `ENNReal` the
degenerate cases (`0 / 0 = 0`, an empty fibre) come out on the right side of the inequality by
themselves. -/
theorem multiplicity_le_sum_fiberwise {ι ν : Type*} [DecidableEq ν]
    (t : Finset ι) (V : ι → ShadedBody E) (xs : Finset ν) (g : ι → ν)
    (hg : ∀ i ∈ t, g i ∈ xs) :
    ShadedBody.multiplicity t V
      ≤ ∑ x ∈ xs, ShadedBody.multiplicity {i ∈ t | g i = x} V := by
  classical
  have hsplit : ∑ i ∈ t, volume (V i).shade
      = ∑ x ∈ xs, ∑ i ∈ {i ∈ t | g i = x}, volume (V i).shade :=
    (Finset.sum_fiberwise_of_maps_to hg (fun i => volume (V i).shade)).symm
  rw [ShadedBody.multiplicity_eq_div, hsplit, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_le_sum ?_
  intro x _
  have hmono : volume (⋃ i ∈ {i ∈ t | g i = x}, (V i).shade)
      ≤ volume (⋃ i ∈ t, (V i).shade) := by
    refine measure_mono ?_
    refine Set.biUnion_subset_biUnion_left ?_
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  calc (∑ i ∈ {i ∈ t | g i = x}, volume (V i).shade)
        * (volume (⋃ i ∈ t, (V i).shade))⁻¹
      ≤ (∑ i ∈ {i ∈ t | g i = x}, volume (V i).shade)
        * (volume (⋃ i ∈ {i ∈ t | g i = x}, (V i).shade))⁻¹ := by
        exact mul_le_mul_left' (ENNReal.inv_le_inv.mpr hmono) _
    _ = ShadedBody.multiplicity {i ∈ t | g i = x} V := by
        rw [ShadedBody.multiplicity_eq_div, div_eq_mul_inv]


/-! ### Absorbing a constant into a negative power of the scale -/

/-- **A constant times a higher power of the scale is eventually below a lower power.**

The form in which the two losses of `Kakeya.ml1Boot.multiplicity_le_of_ball_of_unitBall` — the
factor `2` of the discard and the cell count `M` — are absorbed, and also the form in which the
fullness threshold is relaxed from `ηs` to `ηs / 2`. -/
theorem eventually_mul_rpow_le_rpow {K : ENNReal} (hK : K ≠ ⊤) {p q : ℝ} (hqp : q < p) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, K * (δ : ENNReal) ^ p ≤ (δ : ENNReal) ^ q := by
  filter_upwards [eventually_finite_const_le_rpow_neg hK (a := p - q) (by linarith),
    self_mem_nhdsWithin] with δ hδ hδ0
  have hδpos : (0 : NNReal) < δ := hδ0
  have hδne : (δ : ENNReal) ≠ 0 := by
    simpa using (ne_of_gt hδpos)
  have hδtop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  calc K * (δ : ENNReal) ^ p ≤ (δ : ENNReal) ^ (-(p - q)) * (δ : ENNReal) ^ p := by gcongr
    _ = (δ : ENNReal) ^ (-(p - q) + p) := (ENNReal.rpow_add _ _ hδne hδtop).symm
    _ = (δ : ENNReal) ^ q := by ring_nf

/-! ### The reduction -/

/-- Translating a shaded tube translates its underlying shaded body. -/
theorem shadedTube_translate_toShadedBody {b : NNReal} (S : ShadedTube b E) (v : E) :
    (S.translate v).toShadedBody = (S.toShadedBody).translate v := rfl

/-- **A multiplicity upper bound valid in `B₁` upgrades to one valid in `B_R`.**

For a `δ`-independent radius `R ≥ 1` there is a `δ`-independent cardinality `M` — the number of
cells `Kakeya.StickyKakeya.exists_ball_assignment` needs to cover `B_R` — such that the following
holds for every family of shaded `b`-tubes in `B_R` with `b ≤ 1/4`.

Suppose the family has fullness at least `lam`, and suppose `Bound` bounds the multiplicity of
every *nonempty subfamily* that one translation carries into `B₁` and whose fullness is at least
`lam / 2`.  Then the multiplicity of the whole family is at most `2 M * Bound`.

The two halves of the loss are the two pigeonholes: the `2` pays for discarding the sparsely
shaded tubes, which is what makes the fullness hypothesis descend to a subfamily at all, and the
`M` pays for summing over the cells.  Both are fixed before the scale, so a consumer working
inside an eventually-filter absorbs them into its subpolynomial factor.

The hypothesis is stated at `lam / 2` rather than at `lam` because that is exactly what the
discard delivers: every retained tube has shade density at least `λ(𝕋, Y) / 2 ≥ lam / 2`, and a
family all of whose members have density at least `lam / 2` has fullness at least `lam / 2`
(`Kakeya.ml1Boot.le_fullness_of_dens_lower`) — the step that fails for a bare subfamily and is
the reason the discard cannot be omitted. -/
theorem multiplicity_le_of_ball_of_unitBall [Nontrivial E] (R : ℝ) (hR : 1 ≤ R) :
    ∃ M : ℕ, 0 < M ∧
      ∀ {b : NNReal}, 0 < b → (b : ℝ) ≤ 1 / 4 →
        ∀ {κ : Type*} (t : Finset κ) (Tb : κ → ShadedTube b E)
          {lam : NNReal} {Bound : ENNReal},
          (∀ l ∈ t, (Tb l).carrier ⊆ Metric.closedBall 0 R) →
          (lam : ENNReal)
              ≤ (ShadedBody.fullness t (fun l => (Tb l).toShadedBody) : ENNReal) →
          (∀ (t' : Finset κ) (v : E), t' ⊆ t → t'.Nonempty →
              (∀ l ∈ t', ((Tb l).translate v).carrier ⊆ Metric.closedBall 0 1) →
              ((lam / 2 : NNReal) : ENNReal)
                ≤ (ShadedBody.fullness t'
                    (fun l => ((Tb l).translate v).toShadedBody) : ENNReal) →
              ShadedBody.multiplicity t'
                  (fun l => ((Tb l).translate v).toShadedBody) ≤ Bound) →
          ShadedBody.multiplicity t (fun l => (Tb l).toShadedBody)
            ≤ 2 * (M : ENNReal) * Bound := by
  classical
  obtain ⟨xs, hxs_ne, hxs_norm, hnet⟩ := StickyKakeya.exists_ball_assignment (E := E) R hR
  refine ⟨xs.card, Finset.card_pos.mpr hxs_ne, ?_⟩
  intro b hb0 hb4 κ t Tb lam Bound hball hfull hunit
  set V : κ → ShadedBody E := fun l => (Tb l).toShadedBody with hV
  -- Step 1: discard the sparsely shaded tubes.
  set t₁ : Finset κ := _root_.ShadedBody.discardLowShading t V (1 / 2) with ht₁
  have ht₁t : t₁ ⊆ t := _root_.ShadedBody.discardLowShading_subset t V (1 / 2)
  have hhalf : ((1 : NNReal) - 1 / 2) = 1 / 2 := by
    rw [show (1 : NNReal) - 1 / 2 = 1 / 2 from by
      refine tsub_eq_of_eq_add ?_
      norm_num]
  have hmass : ((1 / 2 : NNReal) : ENNReal) * ∑ i ∈ t, volume (V i).shade
      ≤ ∑ i ∈ t₁, volume (V i).shade := by
    have h := _root_.ShadedBody.one_sub_mul_sum_volume_shade_le_sum_discardLowShading t V
      (c := 1 / 2) (by norm_num)
    rwa [hhalf] at h
  have hstep1 : ShadedBody.multiplicity t V ≤ 2 * ShadedBody.multiplicity t₁ V := by
    refine ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset t V t₁ V 2 ?_ ?_
    · exact Set.biUnion_subset_biUnion_left (fun i hi => ht₁t hi)
    · have htwo : ((1 / 2 : NNReal) : ENNReal) = (2 : ENNReal)⁻¹ := by
        simp [ENNReal.coe_div]
      have h2 : (2 : ENNReal) * (((1 / 2 : NNReal) : ENNReal)
          * ∑ i ∈ t, volume (V i).shade) ≤ 2 * ∑ i ∈ t₁, volume (V i).shade :=
        mul_le_mul_left' hmass 2
      calc ∑ i ∈ t, volume (V i).shade
          = (2 : ENNReal) * (((1 / 2 : NNReal) : ENNReal)
              * ∑ i ∈ t, volume (V i).shade) := by
            rw [htwo, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
        _ ≤ 2 * ∑ i ∈ t₁, volume (V i).shade := h2
  -- Step 2: the cells of the ball assignment.
  obtain ⟨x₀, hx₀⟩ := hxs_ne
  set g : κ → E := fun l =>
    if h : ∃ x ∈ xs, ((Tb l).toTube).carrier ⊆ Metric.closedBall x 1 then h.choose else x₀
    with hg_def
  have hg : ∀ l ∈ t₁, g l ∈ xs := by
    intro l _
    by_cases h : ∃ x ∈ xs, ((Tb l).toTube).carrier ⊆ Metric.closedBall x 1
    · simp only [hg_def, dif_pos h]
      exact h.choose_spec.1
    · simp only [hg_def, dif_neg h]
      exact hx₀
  have hgball : ∀ l ∈ t₁, ((Tb l).toTube).carrier ⊆ Metric.closedBall (g l) 1 := by
    intro l hl
    have hcond : ∃ x ∈ xs, ((Tb l).toTube).carrier ⊆ Metric.closedBall x 1 :=
      hnet hb4 ((Tb l).toTube) (hball l (ht₁t hl))
    simp only [hg_def, dif_pos hcond]
    exact hcond.choose_spec.2
  have hstep2 : ShadedBody.multiplicity t₁ V
      ≤ ∑ x ∈ xs, ShadedBody.multiplicity {l ∈ t₁ | g l = x} V :=
    multiplicity_le_sum_fiberwise t₁ V xs g hg
  -- Step 3: each cell, translated into `B₁`.
  have hcell : ∀ x ∈ xs, ShadedBody.multiplicity {l ∈ t₁ | g l = x} V ≤ Bound := by
    intro x _
    rcases Finset.eq_empty_or_nonempty {l ∈ t₁ | g l = x} with hemp | hne
    · rw [hemp]
      simp [ShadedBody.multiplicity_eq_div]
    · have hsub : {l ∈ t₁ | g l = x} ⊆ t := fun l hl =>
        ht₁t (Finset.mem_filter.mp hl).1
      -- the density lower bound inherited from the discard
      have hdens : ∀ l ∈ {l ∈ t₁ | g l = x},
          ((lam / 2 : NNReal) : ENNReal) * volume (Tb l).carrier
            ≤ volume (Tb l).shade := by
        intro l hl
        have hl₁ : l ∈ t₁ := (Finset.mem_filter.mp hl).1
        have hkeep := _root_.ShadedBody.le_volume_shade_of_mem_discardLowShading (V := V)
          (c := 1 / 2) hl₁
        refine le_trans ?_ hkeep
        have hcast : ((lam / 2 : NNReal) : ENNReal)
            = ((1 / 2 : NNReal) : ENNReal) * (lam : ENNReal) := by
          rw [← ENNReal.coe_mul, ENNReal.coe_inj]
          ring
        rw [hcast]
        exact mul_le_mul_right' (mul_le_mul_left' hfull _) _
      -- hence a fullness lower bound for the cell, transported across the translation
      have hfullcell : ((lam / 2 : NNReal) : ENNReal)
          ≤ (ShadedBody.fullness {l ∈ t₁ | g l = x}
              (fun l => ((Tb l).translate (-x)).toShadedBody) : ENNReal) := by
        have h := le_fullness_of_dens_lower (E := E) hb0 hne Tb (lam := lam / 2) hdens
        have heq : ShadedBody.fullness {l ∈ t₁ | g l = x}
            (fun l => ((Tb l).translate (-x)).toShadedBody)
            = ShadedBody.fullness {l ∈ t₁ | g l = x} V :=
          ShadedBody.fullness_translate_const _ V (-x)
        rw [heq]
        exact h
      -- the translated cell lies in the unit ball
      have hballcell : ∀ l ∈ {l ∈ t₁ | g l = x},
          ((Tb l).translate (-x)).carrier ⊆ Metric.closedBall 0 1 := by
        intro l hl
        have hl₁ : l ∈ t₁ := (Finset.mem_filter.mp hl).1
        have hgx : g l = x := (Finset.mem_filter.mp hl).2
        have hin : ((Tb l).toTube).carrier ⊆ Metric.closedBall x 1 := by
          rw [← hgx]; exact hgball l hl₁
        rw [StickyKakeya.shadedTube_translate_carrier]
        intro z hz
        obtain ⟨w, hw, rfl⟩ := hz
        have hwx : w ∈ Metric.closedBall x 1 := hin hw
        rw [Metric.mem_closedBall] at hwx ⊢
        simpa [dist_eq_norm, neg_add_eq_sub, norm_sub_rev] using hwx
      have := hunit {l ∈ t₁ | g l = x} (-x) hsub hne hballcell hfullcell
      have heq2 : ShadedBody.multiplicity {l ∈ t₁ | g l = x}
          (fun l => ((Tb l).translate (-x)).toShadedBody)
          = ShadedBody.multiplicity {l ∈ t₁ | g l = x} V :=
        ShadedBody.multiplicity_translate_const _ V (-x)
      rwa [heq2] at this
  -- Assemble.
  calc ShadedBody.multiplicity t V
      ≤ 2 * ShadedBody.multiplicity t₁ V := hstep1
    _ ≤ 2 * ∑ x ∈ xs, ShadedBody.multiplicity {l ∈ t₁ | g l = x} V :=
        mul_le_mul_left' hstep2 2
    _ ≤ 2 * ∑ _x ∈ xs, Bound := by
        exact mul_le_mul_left' (Finset.sum_le_sum hcell) 2
    _ = 2 * (xs.card : ENNReal) * Bound := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]

end ml1Boot

end Kakeya
