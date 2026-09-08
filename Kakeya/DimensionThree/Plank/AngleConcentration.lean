/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.AngleDef
public import Mathlib.Algebra.Order.Floor.Extended

/-!
# The angular concentration input `hconc` of the dense-box estimate (GWZ Lemma 6.8)

`Plank.denseBoxEstimate_boxNormalised` takes the *typical intersection angle* concentration

`Tri(𝒫, Z) ≤ Mtyp · Tri_{θ₀}(𝒫, Z)`,  `Tri_{θ₀}` = pairs with `θ₀ - a/b ≤ ∠ ≤ 2θ₀`,

as a hypothesis (`hconc`).  This file derives it from the two qualitative outputs of GWZ Lemma 6.11
that are actually available at the plank level:

* `Kakeya.HasMaxPlankAngleBound`: every pair of planks through a common point has effective angle
  `≤ Cang · θ` (so *all* incident pairs live in `[0, 2·Cang·θ]`);
* the *stability* clause: every sub-fibre keeping at least an `A⁻¹`-fraction of a fibre still has
  maximal plank angle `≥ θ / Cstab`.

## The mathematical route, and why it works

The route is: (1) a *pointwise* lower bound "at least half of the pairs through `x` sit at angle
`≳ θ / Cstab`"; (2) the layer-cake identity turning pointwise pair counts into intersection mass;
(3) a dyadic pigeonhole over the *reduced* angular range `[θ/(8·Cstab), 2·Cang·θ]`, whose length
ratio is `16·Cang·Cstab` — independent of `a/b`.

Step (1) is the mathematical core, and it contradicts the `note` preceding
`lem:dyadicAngleMassPigeonhole` in `blueprint/src/GWZAdapted/extra6.tex`, which asserts that the
quadratic pair count is *false* and offers a Turán extremal graph (a disjoint union of `|F|/A`
cliques of size `A`, with intra-cluster angles `∼ θ` and inter-cluster angles `≪ θ`) as a
counterexample.  That counterexample is not realisable: `Prism3D.angle` is a genuine (projective)
distance, and satisfies the quasi-triangle inequality `Prism3D.angle_le_two_mul_add_angle`.
If `i, j` lie in one cluster and `k` in another, then `∠(i,j) ≤ 2(∠(i,k) + ∠(k,j)) ≪ θ`,
contradicting `∠(i,j) ∼ θ`.  Because the small-angle graph is a *metric* small-distance graph,
the correct count
is not Turán's but the trivial ball bound: for each `i`, the set
`t i = {j ∈ F | ∠(i,j) < ρ}` has angular diameter `< 4ρ`, hence — by stability — cardinality
`< |F| / A`, so

`#{pairs at angle < ρ} = Σᵢ |t i| ≤ |F|² / A ≤ |F|² / 2`.

No bounded-overlap covering, no net, and no packing bound is needed.

## The honest cost: `Cstar` is sub-polynomial in `a⁻¹`, not absolute

`denseBoxEstimate_boxNormalised` needs `θ ≤ Cstar · θ₀` (the concentration must sit at the *top* of
the angular range), because `ShadedSlab.triAtAngle_le_card_sq_theta` has `θ₀` in the denominator.
A plain dyadic pigeonhole over `[a/b, Cang·θ]` gives only `θ₀ ≲ θ` and is therefore *not* enough.
Step (1) is exactly what buys `θ₀ ≳ θ`, but it pays for it with `Cstar = 8·Cstab`, and the smallest
`Cstab` available per-fibre is `Kakeya.plankAngleScaleB a = exp((log a⁻¹)^{3/4})`, which is
sub-polynomial in `a⁻¹` rather than absolute.  Accordingly the main theorem
`Plank.exists_typicalIntersectionAngle_of_stableFibres` keeps `Cstab` an explicit parameter and
returns `Cstar = 8 · Cstab`; nothing here is stated with an absolute outer constant, and
`denseBoxEstimate_boxNormalised` is left untouched.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section


namespace Plank

variable {ι : Type*}

/-! ## Angle bookkeeping -/

/-- `Prism3D.planeAngleNN` is the `ℝ≥0`-truncation of `Prism3D.angle`.  The two definitions
`Prism3D.angle` and `Prism3D.planeAngle` have syntactically identical bodies, so this holds by
`rfl`; the repository has no named lemma bridging them, and `simp`/`rw` will not do it. -/
theorem planeAngleNN_eq_toNNReal_angle {a₁ b₁ c₁ a₂ b₂ c₂ : ℝ≥0}
    {h₁ : a₁ ≤ b₁} {h₁' : b₁ ≤ c₁} {h₂ : a₂ ≤ b₂} {h₂' : b₂ ≤ c₂}
    (P : Prism3D a₁ b₁ c₁ h₁ h₁') (Q : Prism3D a₂ b₂ c₂ h₂ h₂') :
    P.planeAngleNN Q = (Prism3D.angle P Q).toNNReal := rfl

/-- **Upper bound for `maxPlankAngle` from raw pairwise angles.**  If every ordered pair of planks
indexed by `t` has raw plane angle at most `c`, and the resolution floor `a / b` is also at most
`c`, then the effective maximal plank angle of `t` is at most `c`.  This is the direction of the
`effectivePlankAngle = 1 ⊓ ((a/b) ⊔ ∠)` bookkeeping that the stability clause consumes. -/
theorem maxPlankAngle_le_of_angle_le {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (V : ι → Plank a b hab hb1) (t : Finset ι) (c : ℝ)
    (hcab : ((a / b : ℝ≥0) : ℝ) ≤ c)
    (h : ∀ i ∈ t, ∀ j ∈ t, Prism3D.angle (V i) (V j) ≤ c) :
    ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ) ≤ c := by
  have hc0 : 0 ≤ c := by
    have : 0 ≤ ((a / b : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
    linarith
  set c_nn : ℝ≥0 := Real.toNNReal c with hc_nn_def
  have hc_nn_coe : (c_nn : ℝ) = c := Real.coe_toNNReal c hc0
  have hcab_nn : (a / b : ℝ≥0) ≤ c_nn := by
    rw [← NNReal.coe_le_coe, hc_nn_coe]
    exact hcab
  have hangle_nn : ∀ i ∈ t, ∀ j ∈ t, (Prism3D.angle (V i) (V j)).toNNReal ≤ c_nn := by
    intro i hi j hj
    exact Real.toNNReal_le_toNNReal (h i hi j hj)
  have h_eff : ∀ i ∈ t, ∀ j ∈ t, Kakeya.effectivePlankAngle (V i) (V j) ≤ c_nn := by
    intro i hi j hj
    calc
      Kakeya.effectivePlankAngle (V i) (V j) = (1 : ℝ≥0) ⊓ ((a / b) ⊔ (V i).planeAngleNN (V j))
          := rfl
      _ ≤ (a / b) ⊔ (V i).planeAngleNN (V j) := inf_le_right
      _ = (a / b) ⊔ (Prism3D.angle (V i) (V j)).toNNReal := by
        rw [planeAngleNN_eq_toNNReal_angle (V i) (V j)]
      _ ≤ c_nn := sup_le hcab_nn (hangle_nn i hi j hj)
  have h_max_nn : Kakeya.maxPlankAngle V t ≤ c_nn := by
    rw [Kakeya.maxPlankAngle]
    exact Kakeya.maxAngle_le h_eff
  have h_real : ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ) ≤ (c_nn : ℝ) := by exact_mod_cast h_max_nn
  rw [hc_nn_coe] at h_real
  exact h_real

/-! ## Step 1: the pointwise quadratic pair count -/

/-- **Angular balls inside a stable fibre are small.**  Let `F` be a fibre whose sub-families of
maximal plank angle at most `c` are all *thin*, in the sense that a sub-family `t ⊆ F` with
`|t| ≥ A⁻¹ |F|` always has `maxPlankAngle V t > c` (this is the contrapositive form of the GWZ
Lemma 6.11 stability clause).  If `4ρ ≤ c` and `a / b ≤ c`, then every angular ball
`{j ∈ F | ∠(Vᵢ, Vⱼ) < ρ}` has cardinality at most `A⁻¹ |F|`.

The only geometry used is the quasi-triangle inequality `Prism3D.angle_le_two_mul_add_angle`: two
members of the ball are at angle `< 2(ρ + ρ) = 4ρ` from each other.  This is the step the blueprint
`note` before `lem:dyadicAngleMassPigeonhole` overlooks — its Turán extremal graph is not
realisable by a distance. -/
theorem card_angleBall_le_of_stable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (V : ι → Plank a b hab hb1) (F : Finset ι) {A ρ c : ℝ}
    (_hρ : 0 ≤ ρ) (hcab : ((a / b : ℝ≥0) : ℝ) ≤ c) (h4ρ : 4 * ρ ≤ c)
    (hstab : ∀ t ⊆ F, A⁻¹ * (F.card : ℝ) ≤ (t.card : ℝ) →
      c < ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ))
    (i : ι) :
    (((F.filter (fun j => Prism3D.angle (V i) (V j) < ρ)).card : ℝ)) ≤ A⁻¹ * (F.card : ℝ) := by
  set ball := F.filter (fun j => Prism3D.angle (V i) (V j) < ρ) with hball_def
  have hball_sub_F : ball ⊆ F := Finset.filter_subset _ _
  by_contra! h
  -- h: A⁻¹ * (F.card : ℝ) < (ball.card : ℝ)
  have hle : A⁻¹ * (F.card : ℝ) ≤ (ball.card : ℝ) := le_of_lt h
  have hmax_gt : c < ((Kakeya.maxPlankAngle V ball : ℝ≥0) : ℝ) :=
    hstab ball hball_sub_F hle
  have hpair : ∀ j ∈ ball, ∀ k ∈ ball, Prism3D.angle (V j) (V k) ≤ c := by
    intro j hj k hk
    rcases Finset.mem_filter.mp hj with ⟨hj_mem, hangle_ji_lt⟩
    rcases Finset.mem_filter.mp hk with ⟨hk_mem, hangle_ik_lt⟩
    have hangle_jk : Prism3D.angle (V j) (V k) < 4 * ρ := by
      calc
        Prism3D.angle (V j) (V k) ≤ 2 * (Prism3D.angle (V j) (V i) + Prism3D.angle (V i) (V k)) :=
          Prism3D.angle_le_two_mul_add_angle (V j) (V i) (V k)
        _ = 2 * (Prism3D.angle (V i) (V j) + Prism3D.angle (V i) (V k)) := by
          rw [Prism3D.angle_comm]
        _ < 2 * (ρ + ρ) := by
          nlinarith
        _ = 4 * ρ := by ring
    nlinarith
  have hmax_le : ((Kakeya.maxPlankAngle V ball : ℝ≥0) : ℝ) ≤ c :=
    maxPlankAngle_le_of_angle_le V ball c hcab hpair
  linarith

open scoped Classical in
/-- **At least half of the pairs in a stable fibre sit at angle `≥ ρ`.**  Summing
`Plank.card_angleBall_le_of_stable` over `i ∈ F` bounds the number of ordered pairs at angle `< ρ`
by `A⁻¹ |F|² ≤ |F|² / 2`, so the complementary set of pairs has at least half of all `|F|²` pairs.

This is the honest quadratic lower bound.  The naive union bound `Σᵢ |ball i| ≤ |F| · maxᵢ |ball i|`
suffices — no bounded-overlap net is required, because the bound on each individual ball is already
`|F| / A`. -/
theorem card_product_le_two_mul_card_bigAngle {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (V : ι → Plank a b hab hb1) (F : Finset ι) {A ρ c : ℝ}
    (hA : 2 ≤ A) (hρ : 0 ≤ ρ) (hcab : ((a / b : ℝ≥0) : ℝ) ≤ c) (h4ρ : 4 * ρ ≤ c)
    (hstab : ∀ t ⊆ F, A⁻¹ * (F.card : ℝ) ≤ (t.card : ℝ) →
      c < ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ)) :
    (F ×ˢ F).card
      ≤ 2 * ((F ×ˢ F).filter (fun p => ρ ≤ Prism3D.angle (V p.1) (V p.2))).card := by
  -- split the total cardinality into big-angle plus small-angle pairs
  have hsplit := Finset.card_filter_add_card_filter_not
    (fun p : ι × ι => ρ ≤ Prism3D.angle (V p.1) (V p.2)) (s := F ×ˢ F)
  -- the small-angle pairs form a union of angular balls, each of size `≤ A⁻¹ |F|`
  have hsmall : (((F ×ˢ F).filter fun p => ¬ρ ≤ Prism3D.angle (V p.1) (V p.2)).card : ℝ)
      ≤ A⁻¹ * ((F.card : ℝ) * (F.card : ℝ)) := by
    have h : ((F ×ˢ F).filter fun p => ¬ρ ≤ Prism3D.angle (V p.1) (V p.2)).card
        = ∑ i ∈ F, (F.filter fun j => Prism3D.angle (V i) (V j) < ρ).card := by
      simp only [not_le]
      rw [Finset.card_filter, Finset.sum_product]
      exact Finset.sum_congr rfl fun i _ => (Finset.card_filter _ _).symm
    rw [h, Nat.cast_sum]
    calc ∑ i ∈ F, ((F.filter fun j => Prism3D.angle (V i) (V j) < ρ).card : ℝ)
        ≤ ∑ _i ∈ F, A⁻¹ * (F.card : ℝ) :=
          Finset.sum_le_sum fun i _ => card_angleBall_le_of_stable V F hρ hcab h4ρ hstab i
      _ = A⁻¹ * ((F.card : ℝ) * (F.card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  -- `A⁻¹ ≤ 1/2`, so the small-angle pairs are at most half of all `|F|²` pairs
  have hhalf : A⁻¹ * ((F.card : ℝ) * (F.card : ℝ)) ≤ 1 / 2 * ((F.card : ℝ) * (F.card : ℝ)) :=
    mul_le_mul_of_nonneg_right
      (by simpa [one_div] using (one_div_le_one_div (by linarith) two_pos).mpr hA)
      (mul_self_nonneg _)
  have htot : ((F ×ˢ F).card : ℝ) = (F.card : ℝ) * (F.card : ℝ) := by
    rw [Finset.card_product, Nat.cast_mul]
  have hsplitR : (((F ×ˢ F).filter fun p => ρ ≤ Prism3D.angle (V p.1) (V p.2)).card : ℝ)
      + (((F ×ˢ F).filter fun p => ¬ρ ≤ Prism3D.angle (V p.1) (V p.2)).card : ℝ)
      = ((F ×ˢ F).card : ℝ) := by exact_mod_cast hsplit
  have : ((F ×ˢ F).card : ℝ)
      ≤ 2 * (((F ×ˢ F).filter fun p => ρ ≤ Prism3D.angle (V p.1) (V p.2)).card : ℝ) := by
    linarith
  exact_mod_cast this

/-! ## Step 2: the layer-cake identity for filtered pairwise intersection mass -/

open scoped Classical in
/-- **Layer cake for band-restricted pairwise shade-intersection mass.**  For any relation `R` on
the index type, the total mass of the pairwise shade intersections restricted to `R` is the integral
of the *pointwise* number of `R`-pairs in the shade fibre:

`Σᵢ Σ_{j : R i j} |Zᵢ ∩ Zⱼ| = ∫ #{(i,j) ∈ 𝒫_Z(x)² | R i j} dx`.

Taking `R = ⊤` gives `Tri(T, Z) = ∫ |𝒫_Z(x)|²`, and taking `R` to be the angular window gives
`Tri_{θ₀}`.  So a single *pointwise* pair-count inequality integrates directly into the
mass statement required by `hconc`.  This is the double-sum analogue of the (private) Fubini step
`sum_volume_shade_inter_eq_lintegral` of `Kakeya.DimensionThree.Plank.RepresentativeSelection`. -/
theorem sum_filter_volume_shade_inter_eq_lintegral (T : Finset ι)
    (Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (R : ι → ι → Prop) :
    ∑ i ∈ T, ∑ j ∈ T with R i j, volume ((Z i).shade ∩ (Z j).shade)
      = ∫⁻ x, (((Kakeya.shadeFibre T Z x ×ˢ Kakeya.shadeFibre T Z x).filter
          (fun p => R p.1 p.2)).card : ENNReal) := by
  classical
  have hmeas (i j : ι) : MeasurableSet ((Z i).shade ∩ (Z j).shade) :=
    (Z i).measurableSet_shade.inter (Z j).measurableSet_shade
  -- the weighted indicator of `Zᵢ ∩ Zⱼ`, whose integral is the `R`-weighted intersection mass
  set g : ι → ι → EuclideanSpace ℝ (Fin 3) → ENNReal := fun i j x =>
    ((Z i).shade ∩ (Z j).shade).indicator (fun _ => (1 : ENNReal)) x *
      (if R i j then 1 else 0) with hg
  have hmeas_g (i j : ι) : Measurable (g i j) :=
    (measurable_const.indicator (hmeas i j)).mul_const _
  have hvol (i j : ι) : ∫⁻ x, ((Z i).shade ∩ (Z j).shade).indicator (fun _ => (1 : ENNReal)) x
      = volume ((Z i).shade ∩ (Z j).shade) :=
    MeasureTheory.lintegral_indicator_one (hmeas i j)
  -- pointwise: the filtered pair count of the fibre is the double sum of the weights
  have hpt (x : EuclideanSpace ℝ (Fin 3)) :
      (((Kakeya.shadeFibre T Z x ×ˢ Kakeya.shadeFibre T Z x).filter
        (fun p => R p.1 p.2)).card : ENNReal) = ∑ i ∈ T, ∑ j ∈ T, g i j x := by
    rw [Finset.card_filter, Finset.sum_product]
    simp only [hg, Kakeya.shadeFibre, Finset.sum_filter, Set.indicator_apply, Set.mem_inter_iff,
      Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : x ∈ (Z i).shade
    · rw [if_pos h1]
      exact Finset.sum_congr rfl fun j _ => by
        simp only [and_iff_right h1, ite_mul, one_mul, zero_mul]
    · simp only [h1, false_and, if_false, zero_mul, Finset.sum_const_zero]
  -- integrate: Fubini for finite sums of nonnegative measurable functions
  rw [MeasureTheory.lintegral_congr hpt, MeasureTheory.lintegral_finsetSum _
    fun i _ => Finset.measurable_sum _ fun j _ => hmeas_g i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.lintegral_finsetSum _ fun j _ => hmeas_g i j, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hR : R i j
  · simp only [hg, if_pos hR, mul_one, hvol]
  · simp only [hg, if_neg hR, mul_zero, MeasureTheory.lintegral_zero]

/-! ## Step 3: the dyadic angular ladder and the pigeonhole -/

/-- **The dyadic ladder covers a bounded angular range.**  Let `ρ ∈ (0, 1]` be the bottom of the
range, `δ ≥ 0` the angular resolution, and put `θ_k = min (2^k ρ) 1`.  Every `α` with
`ρ - δ ≤ α ≤ 2` and `α ≤ 2^N ρ` lies in one of the `N + 1` windows `[θ_k - δ, 2 θ_k]`,
`0 ≤ k ≤ N` — the windows used by `ShadedSlab.triAtAngle`.

The capping at `1` is what makes every `θ_k` an admissible typical angle for
`Plank.denseBoxEstimate_boxNormalised` (which requires `θ₀ ≤ 1`); the top window `[1 - δ, 2]`
absorbs everything above `1`, and raw plane angles never exceed `π/2 < 2`.  The lower endpoint
`θ_k - δ` is what lets the *bottom* window reach down to `ρ - δ`. -/
theorem exists_dyadic_window (δ ρ α : ℝ) (N : ℕ)
    (hδ : 0 ≤ δ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hlb : ρ - δ ≤ α) (hα2 : α ≤ 2) (hαN : α ≤ 2 ^ N * ρ) :
    ∃ k ∈ Finset.range (N + 1),
      min (2 ^ k * ρ) 1 - δ ≤ α ∧ α ≤ 2 * min (2 ^ k * ρ) 1 := by
  -- doubling the argument of the cap costs at most a factor `2`
  have hmin_ineq (x : ℝ) : min (2 * x) 1 ≤ 2 * min x 1 := by
    rcases le_total x 1 with hx | hx
    · rw [min_eq_left hx]; exact min_le_left _ _
    · rw [min_eq_right hx]; exact (min_le_right _ _).trans (by norm_num)
  -- `N` is admissible, so the search below terminates
  have hNmem : α ≤ 2 * min (2 ^ N * ρ) 1 := by
    have h2N : (0 : ℝ) < 2 ^ N * ρ := by positivity
    rcases le_total ((2 : ℝ) ^ N * ρ) 1 with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hS : {k : ℕ | α ≤ 2 * min (2 ^ k * ρ) 1}.Nonempty := ⟨N, hNmem⟩
  -- the least admissible `k`: minimality gives the lower endpoint
  refine ⟨Nat.find hS, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.find_le hNmem)), ?_,
    Nat.find_spec hS⟩
  rcases Nat.eq_zero_or_pos (Nat.find hS) with hk0 | hk0
  · rw [hk0]
    simpa [min_eq_left hρ1] using hlb
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0.ne'
    have h_ineq : 2 * min ((2 : ℝ) ^ m * ρ) 1 < α :=
      lt_of_not_ge (Nat.find_min hS (by omega))
    have h_trans : min ((2 : ℝ) ^ Nat.find hS * ρ) 1 ≤ 2 * min ((2 : ℝ) ^ m * ρ) 1 := by
      rw [hm, pow_succ, mul_comm ((2 : ℝ) ^ m) 2, mul_assoc]
      exact hmin_ineq _
    linarith

open scoped Classical in
/-- **Pigeonhole over a finite family of pair-windows.**  If every `R`-pair carrying nonzero weight
lies in at least one of the `|B|` windows `S k`, then some single window carries at least a
`|B|⁻¹` fraction of the total `R`-weight.  Weights live in `ℝ≥0∞`, and the argument is the finite
maximum, so no finiteness or positivity hypothesis is needed. -/
theorem exists_mem_sum_filter_le_card_mul {κ : Type*} (B : Finset κ) (hB : B.Nonempty)
    (T : Finset ι) (v : ι → ι → ENNReal) (R : ι → ι → Prop) (S : κ → ι → ι → Prop)
    (hcov : ∀ i ∈ T, ∀ j ∈ T, R i j → v i j ≠ 0 → ∃ k ∈ B, S k i j) :
    ∃ k ∈ B, (∑ i ∈ T, ∑ j ∈ T with R i j, v i j)
      ≤ (B.card : ENNReal) * ∑ i ∈ T, ∑ j ∈ T with S k i j, v i j := by
  -- termwise covering: every R-pair with nonzero weight is covered by some S k
  have hpair : ∀ i ∈ T, ∀ j ∈ T, (if R i j then v i j else 0) ≤ ∑ k ∈ B, (if S k i j then v i j
      else 0) := by
    intro i hi j hj
    by_cases hR : R i j
    · rw [if_pos hR]
      by_cases hzero : v i j = 0
      · simp [hzero]
      · rcases hcov i hi j hj hR hzero with ⟨k₀, hk₀B, hSk₀⟩
        have hpos : ∀ k ∈ B, 0 ≤ (if S k i j then v i j else 0) := by
          intro k hk; simp
        have hsing : (if S k₀ i j then v i j else 0) ≤ ∑ k ∈ B, (if S k i j then v i j else 0) :=
          Finset.single_le_sum hpos hk₀B
        have : (if S k₀ i j then v i j else 0) = v i j := by simp [hSk₀]
        rw [this] at hsing
        exact hsing
    · simp [hR]
  -- pick k₀ ∈ B maximising the S k -filtered sum
  rcases Finset.exists_max_image B (fun k => ∑ i ∈ T, ∑ j ∈ T with S k i j, v i j) hB with ⟨k₀,
      hk₀B, hmax⟩
  refine ⟨k₀, hk₀B, ?_⟩
  calc
    (∑ i ∈ T, ∑ j ∈ T with R i j, v i j)
        = ∑ i ∈ T, ∑ j ∈ T, (if R i j then v i j else 0) := by simp [Finset.sum_filter]
    _ ≤ ∑ i ∈ T, ∑ j ∈ T, ∑ k ∈ B, (if S k i j then v i j else 0) := by
      refine Finset.sum_le_sum (fun i hi => ?_)
      refine Finset.sum_le_sum (fun j hj => ?_)
      exact hpair i hi j hj
    _ = ∑ k ∈ B, ∑ i ∈ T, ∑ j ∈ T, (if S k i j then v i j else 0) := by
      calc
        ∑ i ∈ T, ∑ j ∈ T, ∑ k ∈ B, (if S k i j then v i j else 0)
            = ∑ i ∈ T, ∑ k ∈ B, ∑ j ∈ T, (if S k i j then v i j else 0) := by
              refine Finset.sum_congr rfl (fun i hi => ?_)
              rw [Finset.sum_comm]
        _ = ∑ k ∈ B, ∑ i ∈ T, ∑ j ∈ T, (if S k i j then v i j else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ k ∈ B, ∑ i ∈ T, ∑ j ∈ T with S k i j, v i j := by simp [Finset.sum_filter]
    _ ≤ (B.card : ENNReal) * (∑ i ∈ T, ∑ j ∈ T with S k₀ i j, v i j) := by
      have hsum : (∑ k ∈ B, ∑ i ∈ T, ∑ j ∈ T with S k i j, v i j) ≤ (B.card : ENNReal) *
        (∑ i ∈ T, ∑ j ∈ T with S k₀ i j, v i j) := by
        calc
          (∑ k ∈ B, ∑ i ∈ T, ∑ j ∈ T with S k i j, v i j) ≤ (∑ k ∈ B,
            (∑ i ∈ T, ∑ j ∈ T with S k₀ i j, v i j)) :=
            Finset.sum_le_sum (fun k hk => hmax k hk)
          _ = (B.card : ENNReal) * (∑ i ∈ T, ∑ j ∈ T with S k₀ i j, v i j) := by
            simp
      exact hsum

/-! ## Assembling the three steps

The three lemmas below are the steps of `Plank.exists_typicalIntersectionAngle_of_stableFibres`,
isolated so that each elaborates in a small context: the pointwise pair count at *every* point
(including the two degenerate regimes), its integrated mass form, and the raw-angle bound extracted
from the one-sided typical-angle hypothesis. -/

/-- **The pointwise pair count, at every point and in both angular regimes.**  With
`ρ = max (a/b) (θ / (8 Cstab))` the bottom of the dyadic ladder, at least half of the ordered pairs
of planks through any point sit at angle `≥ ρ - a/b`.

There are three cases and only one of them is Step 1.  If `x` lies in no shading the fibre is empty
and both sides vanish.  If `θ / (8 Cstab) ≤ a / b` then `ρ = a / b`, the threshold `ρ - a/b` is `0`,
and *every* pair qualifies by `Prism3D.angle_nonneg` — no stability input is needed, which is what
makes the statement true without a lower bound on `θ`.  Only in the remaining case
`a / b < θ / (8 Cstab)` (which forces `0 < θ`) is the genuine ball-counting argument
`Plank.card_product_le_two_mul_card_bigAngle` invoked, at `c = θ / (2 Cstab) = 4 ρ`; the strict
inequality `c < θ / Cstab` it needs comes from `0 < θ` and `1 ≤ Cstab`. -/
theorem pointwise_card_le_two_mul_bigAngle {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (V : ι → Plank a b hab hb1) (T : Finset ι)
    (Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (θ : ℝ≥0) (Cstab A : ℝ)
    (ha : 0 < a) (hb : 0 < b) (_hθ1 : θ ≤ 1) (hA : 2 ≤ A) (hCstab : 1 ≤ Cstab)
    (hstab : ∀ x ∈ ⋃ i ∈ T, (Z i).shade, ∀ t ⊆ Kakeya.shadeFibre T Z x,
      A⁻¹ * ((Kakeya.shadeFibre T Z x).card : ℝ) ≤ (t.card : ℝ) →
        (θ : ℝ) / Cstab ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ))
    (x : EuclideanSpace ℝ (Fin 3)) :
    (Kakeya.shadeFibre T Z x ×ˢ Kakeya.shadeFibre T Z x).card
      ≤ 2 * ((Kakeya.shadeFibre T Z x ×ˢ Kakeya.shadeFibre T Z x).filter
          (fun p => max ((a / b : ℝ≥0) : ℝ) ((θ : ℝ) / (8 * Cstab)) - ((a / b : ℝ≥0) : ℝ)
            ≤ Prism3D.angle (V p.1) (V p.2))).card := by
  set d := ((a / b : ℝ≥0) : ℝ)
  set s := (θ : ℝ) / (8 * Cstab) with hs
  set F := Kakeya.shadeFibre T Z x with hF
  set ρ := max d s with hρ
  have hab : 0 < d := NNReal.coe_pos.mpr (div_pos ha hb)
  by_cases hx : x ∈ ⋃ i ∈ T, (Z i).shade
  · by_cases h_case : d < s
    · -- CASE 3: a/b < θ/(8*Cstab), so ρ = θ/(8*Cstab). Use card_product_le_two_mul_card_bigAngle.
      -- Everything below is linear arithmetic in the atoms `θ/Cstab` and `ρ = s = θ/(8Cstab)`
      -- once the single rescaling identity is recorded; the threshold is `c = 4ρ = θ/(2Cstab)`.
      have h8 : s = (θ : ℝ) / Cstab / 8 := by rw [hs, div_div, mul_comm]
      have hρ_eq : ρ = s := hρ.trans (max_eq_right h_case.le)
      have hρ0 : 0 ≤ ρ := by
        rw [hρ_eq, hs]
        exact div_nonneg (NNReal.coe_nonneg θ) (by linarith)
      have hstab' : ∀ t ⊆ F, A⁻¹ * (F.card : ℝ) ≤ (t.card : ℝ) →
          4 * ρ < ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ) := fun t ht hcard =>
        lt_of_lt_of_le (by linarith) (hstab x hx t ht hcard)
      refine (card_product_le_two_mul_card_bigAngle V F (A := A) (ρ := ρ) (c := 4 * ρ)
          hA hρ0 (by linarith) le_rfl hstab').trans
        (Nat.mul_le_mul le_rfl (Finset.card_le_card fun p hp => ?_))
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, by linarith [hp.2]⟩
    · -- CASE 2: (θ : ℝ) / (8 * Cstab) ≤ ((a / b : ℝ≥0) : ℝ), so the threshold `ρ - a/b` is `0`
      have h_sub0 : ρ - d = 0 := by
        rw [hρ, max_eq_left (not_lt.mp h_case), sub_self]
      rw [Finset.filter_true_of_mem fun p _ => by
        rw [h_sub0]; exact Prism3D.angle_nonneg (V p.1) (V p.2)]
      omega
  · -- CASE 1: x is not in the union, so F = ∅, both sides are 0
    have hF_empty : F = ∅ := by
      rw [hF, Finset.eq_empty_iff_forall_notMem]
      intro i hi
      rw [Kakeya.mem_shadeFibre] at hi
      exact hx (Set.mem_biUnion (Finset.mem_coe.mpr hi.1) hi.2)
    rw [hF_empty]
    simp

open scoped Classical in
/-- **From the pointwise pair count to pairwise intersection mass.**  A pointwise inequality between
the number of all ordered pairs in a shade fibre and the number of `R`-pairs integrates, through the
layer-cake identity `Plank.sum_filter_volume_shade_inter_eq_lintegral`, to the same inequality
between the total pairwise intersection mass `Tri` and its `R`-restricted part.  This is the only
place where the measure-theoretic Fubini step is used, and it is stated for an arbitrary relation
`R` so that it can be reused. -/
theorem sum_le_two_mul_sum_filter_of_pointwise (T : Finset ι)
    (Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (R : ι → ι → Prop)
    (h : ∀ x : EuclideanSpace ℝ (Fin 3),
      (Kakeya.shadeFibre T Z x ×ˢ Kakeya.shadeFibre T Z x).card
        ≤ 2 * ((Kakeya.shadeFibre T Z x ×ˢ Kakeya.shadeFibre T Z x).filter
            (fun p => R p.1 p.2)).card) :
    (∑ i ∈ T, ∑ j ∈ T, volume ((Z i).shade ∩ (Z j).shade))
      ≤ 2 * ∑ i ∈ T, ∑ j ∈ T with R i j, volume ((Z i).shade ∩ (Z j).shade) := by
  -- Layer-cake identity for the full product (R = True)
  have hLHS_eq : (∑ i ∈ T, ∑ j ∈ T, volume ((Z i).shade ∩ (Z j).shade))
      = ∫⁻ x, ((Kakeya.shadeFibre T Z x ×ˢ Kakeya.shadeFibre T Z x).card : ENNReal) := by
    calc
      (∑ i ∈ T, ∑ j ∈ T, volume ((Z i).shade ∩ (Z j).shade))
          = ∑ i ∈ T, ∑ j ∈ T with True, volume ((Z i).shade ∩ (Z j).shade) := by
        simp
      _ = ∫⁻ x, (((Kakeya.shadeFibre T Z x ×ˢ Kakeya.shadeFibre T Z x).filter (fun p =>
          True)).card : ENNReal) := by
        simpa using sum_filter_volume_shade_inter_eq_lintegral T Z (fun _ _ => True)
      _ = ∫⁻ x, ((Kakeya.shadeFibre T Z x ×ˢ Kakeya.shadeFibre T Z x).card : ENNReal) := by
        refine MeasureTheory.lintegral_congr fun x => ?_
        simp
  -- Layer-cake identity for the given R
  have hRHS_eq : ∑ i ∈ T, ∑ j ∈ T with R i j, volume ((Z i).shade ∩ (Z j).shade)
      = ∫⁻ x, (((Kakeya.shadeFibre T Z x ×ˢ Kakeya.shadeFibre T Z x).filter
          (fun p => R p.1 p.2)).card : ENNReal) :=
    sum_filter_volume_shade_inter_eq_lintegral T Z R
  -- Pointwise inequality cast to ENNReal
  have hcast : ∀ x, ((Kakeya.shadeFibre T Z x ×ˢ Kakeya.shadeFibre T Z x).card : ENNReal)
      ≤ (2 : ENNReal) * (((Kakeya.shadeFibre T Z x ×ˢ Kakeya.shadeFibre T Z x).filter
          (fun p => R p.1 p.2)).card : ENNReal) := by
    intro x
    have hxcast : ((Kakeya.shadeFibre T Z x ×ˢ Kakeya.shadeFibre T Z x).card : ENNReal)
        ≤ ((2 * ((Kakeya.shadeFibre T Z x ×ˢ Kakeya.shadeFibre T Z x).filter (fun p => R p.1
            p.2)).card : ℕ) : ENNReal) :=
      by exact_mod_cast h x
    calc
      ((Kakeya.shadeFibre T Z x ×ˢ Kakeya.shadeFibre T Z x).card : ENNReal)
          ≤ ((2 * ((Kakeya.shadeFibre T Z x ×ˢ Kakeya.shadeFibre T Z x).filter (fun p => R p.1
              p.2)).card : ℕ) : ENNReal) :=
        hxcast
      _ = (2 : ENNReal) * (((Kakeya.shadeFibre T Z x ×ˢ Kakeya.shadeFibre T Z x).filter (fun p
          => R p.1 p.2)).card : ENNReal) := by
        simp [Nat.cast_mul]
  calc
    (∑ i ∈ T, ∑ j ∈ T, volume ((Z i).shade ∩ (Z j).shade))
        = ∫⁻ x, ((Kakeya.shadeFibre T Z x ×ˢ Kakeya.shadeFibre T Z x).card : ENNReal) := hLHS_eq
    _ ≤ ∫⁻ x, ((2 : ENNReal) * (((Kakeya.shadeFibre T Z x ×ˢ Kakeya.shadeFibre T Z x).filter
        (fun p => R p.1 p.2)).card : ENNReal)) :=
      MeasureTheory.lintegral_mono hcast
    _ = (2 : ENNReal) * ∫⁻ x, (((Kakeya.shadeFibre T Z x ×ˢ Kakeya.shadeFibre T Z x).filter
        (fun p => R p.1 p.2)).card : ENNReal) := by
      rw [MeasureTheory.lintegral_const_mul' (2 : ENNReal) _ (by norm_num : (2 : ENNReal) ≠ ∞)]
    _ = (2 : ENNReal) * (∑ i ∈ T, ∑ j ∈ T with R i j, volume ((Z i).shade ∩ (Z j).shade)) := by
      rw [hRHS_eq]
    _ = 2 * ∑ i ∈ T, ∑ j ∈ T with R i j, volume ((Z i).shade ∩ (Z j).shade) := by norm_num

/-- **Raw-angle bound from the one-sided typical-angle hypothesis.**  Two planks whose shadings meet
at a common point are, by `Kakeya.HasMaxPlankAngleBound`, at effective angle at most `Cang · θ`;
since the effective angle caps the raw angle at `1` the conclusion has to be stated with the slack
factor `2`, and the case `1 ≤ Cang · θ` is then covered by the absolute bound
`Prism3D.angle ≤ π / 2 ≤ 2`.  This is exactly the input the dyadic window lemma
`Plank.exists_dyadic_window` needs at the top of the angular range. -/
theorem angle_le_two_mul_of_maxPlankAngleBound {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (V : ι → Plank a b hab hb1) (T : Finset ι)
    (Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (θ Cang : ℝ≥0)
    (hang : Kakeya.HasMaxPlankAngleBound T Z V θ Cang)
    {i j : ι} (hi : i ∈ T) (hj : j ∈ T) {x : EuclideanSpace ℝ (Fin 3)}
    (hxi : x ∈ (Z i).shade) (hxj : x ∈ (Z j).shade) :
    Prism3D.angle (V i) (V j) ≤ 2 * (Cang : ℝ) * (θ : ℝ) := by
  -- `i` and `j` lie in the shade fibre at `x`, so their effective angle is `≤ Cang * θ`
  have h_eff : (1 : ℝ≥0) ⊓ ((a / b) ⊔ (Prism3D.angle (V i) (V j)).toNNReal) ≤ Cang * θ :=
    (Kakeya.le_maxAngle (ang := fun i j => Kakeya.effectivePlankAngle (V i) (V j))
        ((Kakeya.mem_shadeFibre T Z x i).mpr ⟨hi, hxi⟩)
        ((Kakeya.mem_shadeFibre T Z x j).mpr ⟨hj, hxj⟩)).trans
      (hang x (Set.mem_iUnion₂.mpr ⟨i, hi, hxi⟩))
  have hprod : (0 : ℝ) ≤ (Cang : ℝ) * (θ : ℝ) := by positivity
  rcases le_or_gt 1 ((Cang : ℝ) * (θ : ℝ)) with h | h
  · -- the effective angle is capped at `1`, so use the absolute bound `angle ≤ π / 2 ≤ 2`
    linarith [Prism3D.angle_le_pi_div_two (V i) (V j), Real.pi_le_four]
  · -- `Cang * θ < 1`, so the cap is inactive and the raw angle itself is `≤ Cang * θ`
    have hC1 : Cang * θ < 1 := by rw [← NNReal.coe_lt_coe]; push_cast; exact h
    have hangle := Real.toNNReal_le_iff_le_coe.mp
      (le_sup_right.trans ((inf_le_iff.mp h_eff).resolve_left (not_le.mpr hC1)))
    rw [NNReal.coe_mul] at hangle
    linarith

/-! ## The `hconc` theorem -/

open scoped Classical in
/-- **The angular concentration input of the dense-box estimate (GWZ Lemma 6.8).**

Fix a local family `(V, Z)` of shaded planks — `Z` is any family of shaded bodies, so this applies
verbatim to the local shadings `(Y i).shade ∩ box ∩ prism` of a shifted slab box, and it says
nothing about carriers, so the carrier coherence `(Z i).carrier = (V i).carrier` required by
`Plank.denseBoxEstimate_boxNormalised` is untouched.  Assume:

* `hang`: all incident plank pairs have effective angle `≤ Cang · θ`
  (`Kakeya.HasMaxPlankAngleBound`, from `Kakeya.findingTypicalAngleOfIntersection`);
* `hstab`: every sub-fibre keeping an `A⁻¹`-fraction of a fibre still has maximal plank angle
  `≥ θ / Cstab` (the stability clause of `Kakeya.typicalAngleFibre`, where
  `Cstab = Kakeya.plankAngleScaleB a`, or of `Kakeya.findingTypicalAngleOfIntersection`, where
  `Cstab = C · a ^ (-ε)`);
* `hN`: `N` dyadic doublings cover the reduced range, i.e. `2 · Cang · θ ≤ 2^N · ρ` with
  `ρ = max (a/b) (θ / (8 Cstab))`.  Note `2 Cang θ / ρ ≤ 16 · Cang · Cstab` *independently of
  `a/b`*, so `N = O(log(Cang · Cstab))` always suffices — see
  `Plank.exists_pow_two_mul_ge`.  This is what Step 1 buys: without it the ladder would have to
  start at `a/b` and `N` would be `O(log(b/a))`.

Then there is a dyadic angular scale `θ₀ ∈ [a/b, 1]` with `θ ≤ 8 · Cstab · θ₀` at which the pairwise
intersection mass concentrates, with loss `Mtyp = 2(N+1)`:

`Tri ≤ 2(N+1) · Tri_{θ₀}`.

**The comparability constant is `Cstar = 8 · Cstab`, which is sub-polynomial in `a⁻¹` and not
absolute.**  This is unavoidable: it is Step 1 (the ball bound against the stability clause) that
puts `θ₀` at the *top* of the range, and the stability clause is only available with the
stopping-time scale.  Absorbing `Mtyp = 2(N+1)` into `a ^ (-2η)` needs `a` small in terms of `η`;
see `Plank.exists_bandCount_le_rpow`.  Neither loss is charged to
`Plank.denseBoxEstimate_boxNormalised`, which is left unchanged. -/
theorem exists_typicalIntersectionAngle_of_stableFibres
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (V : ι → Plank a b hab hb1) (T : Finset ι)
    (Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (θ Cang : ℝ≥0) (Cstab A : ℝ) (N : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hθ1 : θ ≤ 1) (hA : 2 ≤ A) (hCstab : 1 ≤ Cstab)
    (hang : Kakeya.HasMaxPlankAngleBound T Z V θ Cang)
    (hstab : ∀ x ∈ ⋃ i ∈ T, (Z i).shade, ∀ t ⊆ Kakeya.shadeFibre T Z x,
      A⁻¹ * ((Kakeya.shadeFibre T Z x).card : ℝ) ≤ (t.card : ℝ) →
        (θ : ℝ) / Cstab ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ))
    (hN : 2 * (Cang : ℝ) * (θ : ℝ)
      ≤ 2 ^ N * max ((a / b : ℝ≥0) : ℝ) ((θ : ℝ) / (8 * Cstab))) :
    ∃ θ0 : ℝ,
      ((a / b : ℝ≥0) : ℝ) ≤ θ0 ∧ θ0 ≤ 1 ∧ (θ : ℝ) ≤ 8 * Cstab * θ0 ∧
      (∑ i ∈ T, ∑ j ∈ T, volume ((Z i).shade ∩ (Z j).shade))
        ≤ (((2 * (N + 1) : ℕ) : ℝ≥0) : ENNReal) *
          (∑ i ∈ T, ∑ j ∈ T with
              (θ0 - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
                Prism3D.angle (V i) (V j) ≤ 2 * θ0),
            volume ((Z i).shade ∩ (Z j).shade)) := by
  set ρ := max ((a / b : ℝ≥0) : ℝ) ((θ : ℝ) / (8 * Cstab)) with hρ_def
  have h8 : (0 : ℝ) < 8 * Cstab := by linarith
  have h_ab_nonneg : 0 ≤ ((a / b : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have h_ab_pos : 0 < ((a / b : ℝ≥0) : ℝ) := by
    exact_mod_cast div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hθ1' : (θ : ℝ) ≤ 1 := by exact_mod_cast hθ1
  have h_ab_le_one : ((a / b : ℝ≥0) : ℝ) ≤ 1 := by
    exact_mod_cast div_le_one_of_le₀ hab (by positivity)
  have h_theta_div_le_one : (θ : ℝ) / (8 * Cstab) ≤ 1 := (div_le_one h8).mpr (by linarith)
  have hρ_pos : 0 < ρ := h_ab_pos.trans_le (le_max_left _ _)
  have hρ_le_one : ρ ≤ 1 := max_le h_ab_le_one h_theta_div_le_one
  have h_ab_le_ρ : ((a / b : ℝ≥0) : ℝ) ≤ ρ := le_max_left _ _
  have h_theta_div_le_ρ : (θ : ℝ) / (8 * Cstab) ≤ ρ := le_max_right _ _
  have h_angle_le_two : ∀ i j : ι, Prism3D.angle (V i) (V j) ≤ 2 := fun i j =>
    (Prism3D.angle_le_pi_div_two (V i) (V j)).trans (by linarith [Real.pi_le_four])
  -- STEP A: mass form of the pointwise pair count
  have h_mass_ineq : (∑ i ∈ T, ∑ j ∈ T, volume ((Z i).shade ∩ (Z j).shade))
      ≤ 2 * (∑ i ∈ T, ∑ j ∈ T with (ρ - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j)),
        volume ((Z i).shade ∩ (Z j).shade)) :=
    sum_le_two_mul_sum_filter_of_pointwise T Z _ fun x =>
      pointwise_card_le_two_mul_bigAngle V T Z θ Cstab A ha hb hθ1 hA hCstab hstab x
  -- STEP B: dyadic pigeonhole over the ladder `min (2 ^ k * ρ) 1`
  have hcov : ∀ i ∈ T, ∀ j ∈ T,
      (ρ - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j)) →
      volume ((Z i).shade ∩ (Z j).shade) ≠ 0 →
      ∃ k ∈ Finset.range (N + 1),
        (min (2 ^ k * ρ) 1 - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
         Prism3D.angle (V i) (V j) ≤ 2 * min (2 ^ k * ρ) 1) := by
    intro i hi j hj hbig hvol
    obtain ⟨x, hx⟩ := MeasureTheory.nonempty_of_measure_ne_zero hvol
    exact exists_dyadic_window _ ρ _ N h_ab_nonneg hρ_pos hρ_le_one hbig (h_angle_le_two i j)
      ((angle_le_two_mul_of_maxPlankAngleBound V T Z θ Cang hang hi hj hx.1 hx.2).trans hN)
  obtain ⟨k, -, h_pigeon⟩ := exists_mem_sum_filter_le_card_mul (Finset.range (N + 1))
    ⟨0, by simp⟩ T (fun i j => volume ((Z i).shade ∩ (Z j).shade))
    (fun i j => ρ - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j))
    (fun (k : ℕ) (i j : ι) =>
      min (2 ^ k * ρ) 1 - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
      Prism3D.angle (V i) (V j) ≤ 2 * min (2 ^ k * ρ) 1)
    hcov
  -- STEP C: endpoints and assembly.  `θ0 = min (2 ^ k * ρ) 1` sits above `ρ`, which carries both
  -- the `a / b` lower endpoint and the comparability `θ ≤ 8 · Cstab · θ0`.
  set θ0 := min (2 ^ k * ρ) 1 with hθ0_def
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hρ_le_θ0 : ρ ≤ θ0 := le_min (le_mul_of_one_le_left hρ_pos.le h2k) hρ_le_one
  rw [Finset.card_range] at h_pigeon
  refine ⟨θ0, h_ab_le_ρ.trans hρ_le_θ0, hθ0_def ▸ min_le_right _ _,
    by rw [mul_comm (8 * Cstab) θ0]; exact (div_le_iff₀ h8).mp (h_theta_div_le_ρ.trans hρ_le_θ0),
    ?_⟩
  calc
    (∑ i ∈ T, ∑ j ∈ T, volume ((Z i).shade ∩ (Z j).shade))
        ≤ 2 * (∑ i ∈ T, ∑ j ∈ T with (ρ - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j)),
          volume ((Z i).shade ∩ (Z j).shade)) := h_mass_ineq
    _ ≤ 2 * (((N + 1 : ℕ) : ENNReal) * (∑ i ∈ T, ∑ j ∈ T with
          (θ0 - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
            Prism3D.angle (V i) (V j) ≤ 2 * θ0),
        volume ((Z i).shade ∩ (Z j).shade))) := by
      convert mul_le_mul_right h_pigeon 2 using 6
    _ = _ := by push_cast; ring

/-! ## Controlling the band count -/

/-- **A dyadic ladder of logarithmic length covers a bounded range.**  For `ρ > 0` there is an
`N` with `Θ ≤ 2^N ρ` and `N ≤ log₂ (max (Θ/ρ) 1) + 1`.  Applied with
`Θ = 2 · Cang · θ` and `ρ = max (a/b) (θ/(8 Cstab))` this gives
`Θ / ρ ≤ 16 · Cang · Cstab`, hence `N ≤ log₂(16 · Cang · Cstab) + 1`: the band count depends on the
stability scale only *logarithmically*, and not at all on `a / b`. -/
theorem exists_pow_two_mul_ge (ρ Θ : ℝ) (hρ : 0 < ρ) :
    ∃ N : ℕ, Θ ≤ 2 ^ N * ρ ∧ (N : ℝ) ≤ Real.logb 2 (max (Θ / ρ) 1) + 1 := by
  obtain ⟨M, hM⟩ : ∃ M, M = max (Θ / ρ) 1 := ⟨_, rfl⟩
  have hM1 : (1 : ℝ) ≤ M := hM ▸ le_max_right _ _
  rw [← hM]
  refine ⟨⌈Real.logb 2 M⌉₊, ?_,
    (Nat.ceil_lt_add_one (Real.logb_nonneg one_lt_two hM1)).le⟩
  rw [← div_le_iff₀ hρ]
  refine (hM ▸ le_max_left (Θ / ρ) 1).trans ?_
  calc M = (2 : ℝ) ^ (Real.logb 2 M) :=
        (Real.rpow_logb two_pos (by norm_num) (by linarith)).symm
    _ ≤ (2 : ℝ) ^ ((⌈Real.logb 2 M⌉₊ : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two (Nat.le_ceil _)
    _ = _ := Real.rpow_natCast 2 _

/-- **Sub-linearity of `L ^ (3/4)`, in the form the band count needs.**  For any `c₁, c₂ ≥ 0` and
`η > 0` there is a threshold `L₀ ≥ 1` beyond which `c₁ + c₂ · L ^ (3/4) ≤ 2 η L`.  Both summands are
absorbed separately: `c₁ ≤ η L` for `L ≥ c₁ / η`, and `c₂ · L ^ (3/4) ≤ η L` for
`L ≥ (c₂ / η) ^ 4`, because `L ^ (3/4) = L · L ^ (-1/4)` and `t ↦ t ^ (-1/4)` is antitone. -/
private theorem exists_threshold_rpow_three_quarters {c₁ c₂ η : ℝ}
    (_hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hη : 0 < η) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → c₁ + c₂ * L ^ (3 / 4 : ℝ) ≤ 2 * η * L := by
  refine ⟨max 1 (max (c₁ / η) ((c₂ / η) ^ (4 : ℝ))), le_max_left _ _, fun L hL => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hL)
  -- `c₁ ≤ η L`, since `L ≥ c₁ / η`
  have hc1 : c₁ ≤ η * L := by
    rw [← div_le_iff₀' hη]
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  -- `c₂ ≤ η · L ^ (1/4)`, since `L ≥ (c₂ / η) ^ 4` and `t ↦ t ^ (1/4)` is monotone
  have hc2 : c₂ ≤ η * L ^ (1 / 4 : ℝ) := by
    have h4 : ((c₂ / η) ^ (4 : ℝ)) ^ (1 / 4 : ℝ) ≤ L ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (((le_max_right _ _).trans (le_max_right _ _)).trans hL)
        (by norm_num)
    rw [← Real.rpow_mul (by positivity)] at h4
    norm_num at h4
    rwa [← div_le_iff₀' hη]
  -- `c₂ · L ^ (3/4) ≤ η · L ^ (1/4) · L ^ (3/4) = η L`
  calc c₁ + c₂ * L ^ (3 / 4 : ℝ)
      ≤ η * L + (η * L ^ (1 / 4 : ℝ)) * L ^ (3 / 4 : ℝ) := by gcongr
    _ = η * L + η * (L ^ (1 / 4 : ℝ) * L ^ (3 / 4 : ℝ)) := by ring
    _ = 2 * η * L := by rw [← Real.rpow_add hLpos]; norm_num; ring

/-- **The stability scale contributes only `(log a⁻¹) ^ (3/4)` to the band count.**  Unfolding
`Kakeya.plankAngleScaleB` and splitting the logarithm of the product bounds the band count by an
absolute constant plus `(log a⁻¹) ^ (3/4) / log 2`.  The `max … 1` guard makes the estimate hold
also for tiny `Cang` (including `Cang = 0`, where the logarithm of the product degenerates). -/
private theorem logb_scaleB_le (Cang : ℝ≥0) {a : ℝ≥0} (ha : 0 < a) (ha1 : a < 1) :
    Real.logb 2 (16 * (Cang : ℝ) * Kakeya.plankAngleScaleB a) + 1
      ≤ (Real.log (max (16 * (Cang : ℝ)) 1) / Real.log 2 + 1)
        + (Real.log (a : ℝ)⁻¹) ^ (3 / 4 : ℝ) / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set L := Real.log (a : ℝ)⁻¹ with hL_def
  have hL_nonneg : 0 ≤ L := by
    rw [hL_def, Real.log_inv, neg_nonneg]
    exact Real.log_nonpos (by exact_mod_cast ha.le) (by exact_mod_cast ha1.le)
  have hLp : 0 ≤ L ^ (3 / 4 : ℝ) := Real.rpow_nonneg hL_nonneg _
  set D := max (16 * (Cang : ℝ)) 1 with hD
  have hDge1 : (1 : ℝ) ≤ D := le_max_right _ _
  -- `log (16 · Cang · B) ≤ log D + L ^ (3/4)`, uniformly in the sign of `Cang`
  have key : Real.log (16 * (Cang : ℝ) * Kakeya.plankAngleScaleB a)
      ≤ Real.log D + L ^ (3 / 4 : ℝ) := by
    have hlogD : 0 ≤ Real.log D := Real.log_nonneg hDge1
    rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ 16 * (Cang : ℝ)) with h0 | h0
    · rw [← h0, zero_mul, Real.log_zero]; linarith
    · rw [Kakeya.plankAngleScaleB, ← hL_def,
        Real.log_mul h0.ne' (Real.exp_ne_zero _), Real.log_exp]
      exact add_le_add_left (Real.log_le_log h0 (le_max_left _ _)) _
  have hdiv : Real.log (16 * (Cang : ℝ) * Kakeya.plankAngleScaleB a) / Real.log 2
      ≤ (Real.log D + L ^ (3 / 4 : ℝ)) / Real.log 2 :=
    div_le_div_of_nonneg_right key hlog2.le
  rw [add_div] at hdiv
  rw [← Real.log_div_log]
  linarith

/-- **The band count is absorbed by `a ^ (-2η)` once `a` is small.**  With the per-fibre stability
scale `Cstab = Kakeya.plankAngleScaleB a = exp((log a⁻¹)^{3/4})`, the band count of
`Plank.exists_typicalIntersectionAngle_of_stableFibres` satisfies
`N ≤ log₂(16 · Cang · Cstab) + 1 = O((log a⁻¹)^{3/4})`, while `a ^ (-2η) = exp(2η · log a⁻¹)`.
Since `t^{3/4} = o(t)`, the multiplicity requirement
`(Mtyp : ℝ≥0∞) ≤ a ^ (-(2η))` of `Plank.denseBoxEstimate_boxNormalised` holds for all sufficiently
small `a`.  The threshold `a₀` genuinely depends on `η` (and on `Cang`), and at the constant `1`
implicit in this statement no absolute threshold works: as `a → 1⁻` one has `a^{-2η} → 1` while
`2(N+1) ≥ 2`.  It is exactly that implicit `1` which
`Plank.exists_combined_absorption` replaces by a uniform `Ceta`, and thereby dispenses with the
threshold; this lemma is kept unchanged because `Plank.denseBoxEstimate_boxNormalised` consumes
it in the `Ceta = 1` form. -/
theorem exists_bandCount_le_rpow (Cang : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    ∃ a₀ : ℝ≥0, 0 < a₀ ∧ a₀ < 1 ∧ ∀ {a : ℝ≥0}, 0 < a → a < a₀ → ∀ N : ℕ,
      (N : ℝ) ≤ Real.logb 2 (16 * (Cang : ℝ) * Kakeya.plankAngleScaleB a) + 1 →
      (((2 * (N + 1 : ℕ) : ℕ) : ℝ≥0) : ENNReal) ≤ (a : ENNReal) ^ (-(2 * η)) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set D := max (16 * (Cang : ℝ)) 1 with hD
  have hlogD_nonneg : 0 ≤ Real.log D := Real.log_nonneg (le_max_right _ _)
  set c₂ := 2 / Real.log 2 with hc₂
  have hc₂_nonneg : 0 ≤ c₂ := div_nonneg (by norm_num) (by positivity)
  set c₁ := 2 * (Real.log D / Real.log 2) + 4 with hc₁
  have hc₁_nonneg : 0 ≤ c₁ := by
    dsimp [c₁]; positivity
  rcases exists_threshold_rpow_three_quarters hc₁_nonneg hc₂_nonneg hη with ⟨L₀, hL₀_ge_one, hL₀⟩
  -- a₀ = exp (-L₀) ∈ (0,1)
  set a₀' : ℝ := Real.exp (-L₀) with ha₀'_def
  have ha₀'_pos : 0 < a₀' := Real.exp_pos _
  have ha₀'_lt_one : a₀' < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  let a₀ : ℝ≥0 := ⟨a₀', ha₀'_pos.le⟩
  have ha₀_lt_one : a₀ < 1 := ha₀'_lt_one
  refine ⟨a₀, ha₀'_pos, ha₀_lt_one, ?_⟩
  intro a ha ha_lt_a₀ N hN
  set L := Real.log ((a : ℝ)⁻¹) with hL_def
  have hL_ge_L₀ : L₀ ≤ L := by
    rw [hL_def, Real.log_inv]
    have hlog_lt : Real.log (a : ℝ) < Real.log a₀' :=
      Real.log_lt_log (by exact_mod_cast ha) (by exact_mod_cast ha_lt_a₀)
    rw [ha₀'_def, Real.log_exp] at hlog_lt
    linarith
  -- The band count is `O(L ^ (3/4))`, by `logb_scaleB_le`
  have hN_bound : (N : ℝ) ≤ Real.log D / Real.log 2 + L ^ (3/4 : ℝ) / Real.log 2 + 1 := by
    have hlb := logb_scaleB_le Cang ha (ha_lt_a₀.trans ha₀_lt_one)
    rw [← hD, ← hL_def] at hlb
    linarith
  -- Sub-linearity turns that into `2 * (N + 1) ≤ 2 * η * L`
  have h2Np1 : 2 * ((N : ℝ) + 1) ≤ 2 * η * L := by
    have h := hL₀ L hL_ge_L₀
    have hkey : c₂ * L ^ (3/4 : ℝ) = 2 * (L ^ (3/4 : ℝ) / Real.log 2) := by rw [hc₂]; ring
    rw [hc₁] at h
    linarith
  have h_real_goal : ((2 * (N + 1 : ℕ) : ℕ) : ℝ) ≤ (a : ℝ) ^ (-(2 * η : ℝ)) := by
    have heq : Real.exp (2 * η * L) = (a : ℝ) ^ (-(2 * η : ℝ)) := by
      rw [Real.rpow_def_of_pos (show (0 : ℝ) < (a : ℝ) by exact_mod_cast ha), hL_def,
        Real.log_inv]
      ring_nf
    have h_exp : 2 * η * L + 1 ≤ (a : ℝ) ^ (-(2 * η : ℝ)) := heq ▸ Real.add_one_le_exp _
    push_cast
    linarith
  rw [← ENNReal.coe_rpow_of_ne_zero (by exact_mod_cast ha.ne' : (a : ℝ≥0) ≠ 0)]
  exact ENNReal.coe_le_coe.mpr (NNReal.coe_le_coe.mp (by simpa using h_real_goal))

/-! ## Our own: absorbing the *product* `Cstar · Mtyp`

`Plank.exists_bandCount_le_rpow` absorbs the multiplicity `Mtyp = 2(N+1)` alone into `a^{-2η}` and
leaves the comparability constant `Cstar = 8·Cstab` to be charged to the outer constant of
`Plank.denseBoxEstimate_boxNormalised`.  That is honest only because that lemma quantifies `Cstar`
*before* the configuration; with the per-fibre stability scale `Cstab = Kakeya.plankAngleScaleB a`
the constant `Cstar = 8·B(a)` depends on `a`, so no such prior quantification is available.

Both losses are sub-polynomial, so their product still is, and it is absorbed by a *single* factor
`Ceta · a^{-η}` with `Ceta` uniform.  That recovered factor `a^η` is what
`Plank.denseBoxEstimate_boxNormalised_combined` converts into a stronger dense-box estimate.

The uniform `Ceta` is what makes the absorption threshold-free.  Charging the product to the bare
`a^{-η}` would force a smallness hypothesis on `a`, because `a^{-η} → 1` as `a → 1⁻` while the
product stays above `8`; allowing a constant factor removes the obstruction entirely, on the coarse
range by explicit `exp`/`log` monotonicity and nowhere by a second geometric argument. -/

/-- **`exp (η log a⁻¹) = a ^ (-η)`.**  The elementary rewriting that turns the exponential form of
the band-count estimate into the `rpow` form the dense-box layer consumes.  It carries a single
exponent, because the *combined* absorption spends only one factor `a^{-η}` on the product
`Cstar · Mtyp`. -/
private theorem exp_mul_log_inv_eq_rpow {a : ℝ≥0} (ha : 0 < a) (η : ℝ) :
    Real.exp (η * Real.log (a : ℝ)⁻¹) = (a : ℝ) ^ (-η) := by
  calc
    Real.exp (η * Real.log (a : ℝ)⁻¹) = Real.exp (η * (-Real.log (a : ℝ))) := by
      rw [Real.log_inv]
    _ = Real.exp ((-η) * Real.log (a : ℝ)) := by ring_nf
    _ = Real.exp (Real.log (a : ℝ) * (-η)) := by rw [mul_comm]
    _ = (a : ℝ) ^ (-η) := by
      rw [Real.rpow_def_of_pos (by exact_mod_cast ha) (-η)]

/-- **Transfer of a real product bound to `ENNReal`.**  The cast bookkeeping for
`Plank.exists_combined_absorption`: an inequality `x·y ≤ Ceta · a ^ (-η)` proved in `ℝ` for
`x, y, Ceta : ℝ≥0` lifts to the coercions into `ENNReal`, because `a ≠ 0`.  The uniform factor
`Ceta` is carried because the absorption is threshold-free and therefore cannot be stated at
`Ceta = 1`. -/
private theorem coe_mul_le_mul_rpow_of_real_le {a : ℝ≥0} (ha : 0 < a) {η : ℝ} {Ceta x y : ℝ≥0}
    (h : (x : ℝ) * (y : ℝ) ≤ (Ceta : ℝ) * (a : ℝ) ^ (-η)) :
    ((x : ℝ≥0) : ENNReal) * ((y : ℝ≥0) : ENNReal)
      ≤ (Ceta : ENNReal) * (a : ENNReal) ^ (-η) := by
  have h_ne_zero : a ≠ 0 := by exact_mod_cast ha.ne'
  have h_nn : (x : ℝ≥0) * (y : ℝ≥0) ≤ (Ceta : ℝ≥0) * (a ^ (-η : ℝ) : ℝ≥0) := by
    have hℝ : (x : ℝ) * (y : ℝ) ≤ ((Ceta : ℝ≥0) * (a ^ (-η : ℝ) : ℝ≥0) : ℝ) := by
      calc
        (x : ℝ) * (y : ℝ) ≤ (Ceta : ℝ) * (a : ℝ) ^ (-η) := h
        _ = ((Ceta : ℝ≥0) : ℝ) * (((a ^ (-η : ℝ) : ℝ≥0) : ℝ)) := by simp
        _ = ((Ceta : ℝ≥0) * (a ^ (-η : ℝ) : ℝ≥0) : ℝ) := by simp
    exact NNReal.coe_le_coe.mpr hℝ
  calc
    ((x : ℝ≥0) : ENNReal) * ((y : ℝ≥0) : ENNReal) = ((x * y : ℝ≥0) : ENNReal) := by simp
    _ ≤ ((Ceta : ℝ≥0) * (a ^ (-η : ℝ) : ℝ≥0) : ℝ≥0) := ENNReal.coe_le_coe.mpr h_nn
    _ = ((Ceta : ℝ≥0) : ENNReal) * ((a ^ (-η : ℝ) : ℝ≥0) : ENNReal) := by simp
    _ = (Ceta : ENNReal) * (a : ENNReal) ^ (-η) := by
      simp [ENNReal.coe_rpow_of_ne_zero h_ne_zero (-η)]

/-- **The comparability constant `Cstar = 8·B(a)` as an `ℝ≥0` scalar.**
`Kakeya.plankAngleScaleB` is an exponential, hence positive, so the truncation `Real.toNNReal`
is inactive on `8·B(a)` and the coercion back to `ℝ` is the identity.  This is the bridge
between the real-valued `Cstab` parameter
of `Plank.exists_typicalIntersectionAngle_of_stableFibres` and the `ℝ≥0`-valued `Cstar` argument of
`Plank.denseBoxEstimate_boxNormalised_combined`. -/
theorem coe_toNNReal_eight_mul_plankAngleScaleB (a : ℝ≥0) :
    (((8 * Kakeya.plankAngleScaleB a).toNNReal : ℝ≥0) : ℝ) = 8 * Kakeya.plankAngleScaleB a := by
  have hpos : 0 ≤ 8 * Kakeya.plankAngleScaleB a := by
    have hpos' : 0 ≤ Kakeya.plankAngleScaleB a := by
      rw [Kakeya.plankAngleScaleB]
      exact (Real.exp_pos _).le
    nlinarith
  simpa using Real.coe_toNNReal (8 * Kakeya.plankAngleScaleB a) hpos

/-- **`1 ≤ Cstar` for `0 < a < 1`.**  For `a < 1` one has `log a⁻¹ > 0`, hence
`(log a⁻¹)^{3/4} ≥ 0` and `B(a) ≥ 1`, so `8·B(a) ≥ 8`.  Supplied for the consumers that still need
the lower bound `1 ≤ Cstar` (e.g. `Plank.denseBoxEstimate_boxNormalised`); the *combined* estimate
does not require it. -/
theorem one_le_toNNReal_eight_mul_plankAngleScaleB {a : ℝ≥0} (ha : 0 < a) (ha1 : a < 1) :
    (1 : ℝ≥0) ≤ (8 * Kakeya.plankAngleScaleB a).toNNReal := by
  have hlogpos : 0 < Real.log (a : ℝ)⁻¹ := Kakeya.log_inv_pos ha ha1
  have h_nonneg : 0 ≤ (Real.log (a : ℝ)⁻¹) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (hlogpos.le) _
  have hB_ge_one : 1 ≤ Kakeya.plankAngleScaleB a := by
    calc
      1 ≤ Real.exp ((Real.log (a : ℝ)⁻¹) ^ (3 / 4 : ℝ)) := Real.one_le_exp h_nonneg
      _ = Kakeya.plankAngleScaleB a := rfl
  have h8B_nonneg : 0 ≤ 8 * Kakeya.plankAngleScaleB a := by
    have hB_nonneg : 0 ≤ Kakeya.plankAngleScaleB a := by
      have : 0 < Kakeya.plankAngleScaleB a := by
        unfold Kakeya.plankAngleScaleB
        exact Real.exp_pos _
      exact this.le
    nlinarith
  have h8B_ge_one : (1 : ℝ) ≤ 8 * Kakeya.plankAngleScaleB a := by
    nlinarith
  have h_coe : ((8 * Kakeya.plankAngleScaleB a).toNNReal : ℝ) = 8 * Kakeya.plankAngleScaleB a :=
    Real.coe_toNNReal _ h8B_nonneg
  have h_coe_ge_one : (1 : ℝ) ≤ ((8 * Kakeya.plankAngleScaleB a).toNNReal : ℝ) := by
    rw [h_coe]
    exact h8B_ge_one
  exact_mod_cast h_coe_ge_one

/-- **Transfer of the Phase B comparability clause to the `ℝ≥0` form.**  The conclusion
`θ ≤ 8·Cstab·θ₀` of `Plank.exists_typicalIntersectionAngle_of_stableFibres` at
`Cstab = Kakeya.plankAngleScaleB a` is literally the hypothesis `θ ≤ Cstar·θ₀` of
`Plank.denseBoxEstimate_boxNormalised_combined` with
`Cstar = (8 · Kakeya.plankAngleScaleB a).toNNReal`. -/
theorem theta_le_coe_toNNReal_eight_mul_plankAngleScaleB {a θ : ℝ≥0} {θ0 : ℝ}
    (h : (θ : ℝ) ≤ 8 * Kakeya.plankAngleScaleB a * θ0) :
    (θ : ℝ) ≤ (((8 * Kakeya.plankAngleScaleB a).toNNReal : ℝ≥0) : ℝ) * θ0 := by
  have hpos : 0 < Kakeya.plankAngleScaleB a := by
    unfold Kakeya.plankAngleScaleB
    exact Real.exp_pos _
  have h_nonneg : 0 ≤ 8 * Kakeya.plankAngleScaleB a := by nlinarith
  calc
    (θ : ℝ) ≤ 8 * Kakeya.plankAngleScaleB a * θ0 := h
    _ = ((8 * Kakeya.plankAngleScaleB a : ℝ) : ℝ) * θ0 := by ring
    _ = ((Real.toNNReal (8 * Kakeya.plankAngleScaleB a) : ℝ) : ℝ) * θ0 := by
      rw [Real.coe_toNNReal _ h_nonneg]
    _ = (((8 * Kakeya.plankAngleScaleB a).toNNReal : ℝ≥0) : ℝ) * θ0 := rfl

/-- **`B(a)` is antitone in `a`.**  `Kakeya.plankAngleScaleB a = exp((log a⁻¹)^{3/4})` and
`log a⁻¹` decreases as `a` grows, so a lower bound `a₀ ≤ a` on the scale gives an upper bound on
`B(a)`.  This is the only monotonicity used on the coarse range `[a₀, 1)` of
`Plank.exists_combined_absorption`; in particular no comparison between
`Kakeya.plankAngleScaleA a` and `Kakeya.plankAngleScaleB a` is involved. -/
theorem plankAngleScaleB_le_of_le {a₀ a : ℝ≥0} (ha₀ : 0 < a₀) (hle : a₀ ≤ a) (ha1 : a < 1) :
    Kakeya.plankAngleScaleB a ≤ Kakeya.plankAngleScaleB a₀ := by
  have ha_pos : 0 < a := lt_of_lt_of_le ha₀ hle
  have ha₀_lt_one : a₀ < 1 := lt_of_le_of_lt hle ha1
  have haR_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha_pos
  have haR_lt_one : (a : ℝ) < 1 := by exact_mod_cast ha1
  have ha₀R_pos : (0 : ℝ) < (a₀ : ℝ) := by exact_mod_cast ha₀
  have ha₀R_lt_one : (a₀ : ℝ) < 1 := by exact_mod_cast ha₀_lt_one
  have ha₀R_le_aR : (a₀ : ℝ) ≤ (a : ℝ) := by exact_mod_cast hle
  have hlog_a_nonneg : 0 ≤ Real.log ((a : ℝ)⁻¹) :=
    (Kakeya.log_inv_pos ha_pos ha1).le
  have hlog_a₀_nonneg : 0 ≤ Real.log ((a₀ : ℝ)⁻¹) :=
    (Kakeya.log_inv_pos ha₀ ha₀_lt_one).le
  have hlog_inv_le : Real.log ((a : ℝ)⁻¹) ≤ Real.log ((a₀ : ℝ)⁻¹) := by
    rw [Real.log_inv, Real.log_inv]
    have hlog_le : Real.log (a₀ : ℝ) ≤ Real.log (a : ℝ) :=
      Real.log_le_log ha₀R_pos ha₀R_le_aR
    linarith
  have h_rpow_le : (Real.log ((a : ℝ)⁻¹)) ^ (3/4 : ℝ) ≤ (Real.log ((a₀ : ℝ)⁻¹)) ^ (3/4 : ℝ) :=
    Real.rpow_le_rpow hlog_a_nonneg hlog_inv_le (by norm_num : (0 : ℝ) ≤ (3/4 : ℝ))
  calc
    Kakeya.plankAngleScaleB a = Real.exp ((Real.log ((a : ℝ)⁻¹)) ^ (3/4 : ℝ)) := rfl
    _ ≤ Real.exp ((Real.log ((a₀ : ℝ)⁻¹)) ^ (3/4 : ℝ)) := Real.exp_le_exp.mpr h_rpow_le
    _ = Kakeya.plankAngleScaleB a₀ := rfl

/-- **The combined loss is absorbed by `a^{-η}` once `log a⁻¹` is large.**  The *fine* half of
`Plank.exists_combined_absorption`, stated as a scalar inequality on `L = log a⁻¹` rather than as a
smallness threshold on `a`.  With `Cstab = Kakeya.plankAngleScaleB a = exp(L^{3/4})`, the two losses
returned by `Plank.exists_typicalIntersectionAngle_of_stableFibres` are `Cstar = 8·Cstab` and
`Mtyp = 2(N+1)` with `N ≤ log₂(16·Cang·Cstab) + 1`.  The band count obeys
`2(N+1) ≤ c₁ + c₂·L^{3/4} ≤ exp(c₁ + c₂·L^{3/4})`, so

`Cstar · Mtyp ≤ exp(log 8 + c₁ + (1 + c₂)·L^{3/4})`,

and the sub-linearity `L^{3/4} = o(L)` of `Plank.exists_threshold_rpow_three_quarters` (applied with
`η/2` in place of `η`) makes the exponent at most `η·L` as soon as `L ≥ L₀`, i.e.
`Cstar · Mtyp ≤ exp(η·L) = a^{-η}`.

`L₀` depends on `η` and `Cang` only.  It is *not* a threshold on the configuration: the
complementary range `L ≤ L₀` is handled by the explicit finite bound
`Plank.exists_combined_loss_bound`, and the two halves are combined into a single uniform constant
in `Plank.exists_combined_absorption`. -/
theorem exists_logThreshold_combined_loss_le_rpow (Cang : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ {a : ℝ≥0}, 0 < a → a < 1 → L₀ ≤ Real.log (a : ℝ)⁻¹ → ∀ N : ℕ,
      (N : ℝ) ≤ Real.logb 2 (16 * (Cang : ℝ) * Kakeya.plankAngleScaleB a) + 1 →
      (8 * Kakeya.plankAngleScaleB a) * (2 * ((N : ℝ) + 1)) ≤ (a : ℝ) ^ (-η) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set D := max (16 * (Cang : ℝ)) 1 with hD
  have hlogD_nonneg : 0 ≤ Real.log D := Real.log_nonneg (le_max_right _ _)
  -- c₂, c₁ as in the band-count estimate; c₂', c₁' for the combined product `Cstar · Mtyp`
  set c₂ := 2 / Real.log 2 with hc₂
  have hc₂_nonneg : 0 ≤ c₂ := div_nonneg (by norm_num) (by positivity)
  set c₁ := 2 * (Real.log D / Real.log 2) + 4 with hc₁
  have hc₁_nonneg : 0 ≤ c₁ := by
    dsimp [c₁]; positivity
  set c₂' := 1 + c₂ with hc₂'
  have hc₂'_nonneg : 0 ≤ c₂' := by rw [hc₂']; linarith
  have hlog8_nonneg : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ (8 : ℝ))
  set c₁' := Real.log 8 + c₁ with hc₁'
  have hc₁'_nonneg : 0 ≤ c₁' := by rw [hc₁']; linarith
  -- Sub-linearity at η/2 gives L₀
  rcases exists_threshold_rpow_three_quarters hc₁'_nonneg hc₂'_nonneg (half_pos hη) with
    ⟨L₀, hL₀_ge_one, hL₀⟩
  refine ⟨L₀, hL₀_ge_one, ?_⟩
  intro a ha ha1 hL_ge_L₀ N hN
  set L := Real.log ((a : ℝ)⁻¹) with hL_def
  set B := Kakeya.plankAngleScaleB a with hB_def
  have hB_eq : B = Real.exp (L ^ (3/4 : ℝ)) := by
    dsimp [B, Kakeya.plankAngleScaleB, L, hL_def]
  -- The band count is `O(L ^ (3/4))`, by `logb_scaleB_le`
  have hN_bound : (N : ℝ) ≤ Real.log D / Real.log 2 + L ^ (3/4 : ℝ) / Real.log 2 + 1 := by
    have hlb := logb_scaleB_le Cang ha ha1
    rw [← hD, ← hL_def, ← hB_def] at hlb
    linarith
  -- 2*(N+1) ≤ c₁ + c₂*L^(3/4) ≤ exp(c₁ + c₂*L^(3/4))
  have h2Np1_exp : 2 * ((N : ℝ) + 1) ≤ Real.exp (c₁ + c₂ * L ^ (3/4 : ℝ)) := by
    have hkey : c₂ * L ^ (3/4 : ℝ) = 2 * (L ^ (3/4 : ℝ) / Real.log 2) := by rw [hc₂]; ring
    linarith [Real.add_one_le_exp (c₁ + c₂ * L ^ (3/4 : ℝ)), hc₁]
  -- 8*B = exp(log 8 + L^(3/4)), so the product is ≤ exp(c₁' + c₂'*L^(3/4))
  have h8B_eq : 8 * B = Real.exp (Real.log 8 + L ^ (3/4 : ℝ)) := by
    rw [hB_eq, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 8)]
  -- Assemble, using the sub-linearity bound `c₁' + c₂' * L ^ (3/4) ≤ 2 * (η/2) * L = η * L`
  calc
    (8 * B) * (2 * ((N : ℝ) + 1))
        ≤ Real.exp (Real.log 8 + L ^ (3/4 : ℝ)) * Real.exp (c₁ + c₂ * L ^ (3/4 : ℝ)) := by
      rw [h8B_eq]
      exact mul_le_mul_of_nonneg_left h2Np1_exp (by positivity)
    _ = Real.exp ((Real.log 8 + c₁) + (1 + c₂) * L ^ (3/4 : ℝ)) := by
      rw [← Real.exp_add]; ring_nf
    _ = Real.exp (c₁' + c₂' * L ^ (3/4 : ℝ)) := by rw [hc₁', hc₂']
    _ ≤ Real.exp (η * L) := Real.exp_le_exp.mpr (by linarith [hL₀ L hL_ge_L₀])
    _ = (a : ℝ) ^ (-η) := exp_mul_log_inv_eq_rpow ha η

/-- **On the coarse range `log a⁻¹ ≤ L₀` the combined loss is bounded by an explicit constant.**
Everything in sight is monotone in `L = log a⁻¹`: the stability scale is
`Kakeya.plankAngleScaleB a = exp(L^{3/4}) ≤ exp(L₀^{3/4})` and, by `Plank.logb_scaleB_le`, the
dyadic band count obeys

`N ≤ (log (max (16·Cang) 1) / log 2 + 1) + L^{3/4} / log 2 ≤ Nmax`,

with `Nmax` the same expression at `L₀`.  Hence `8·B(a) · 2(N+1) ≤ 8·exp(L₀^{3/4})·2·(Nmax + 1)`,
a finite constant depending on `Cang` and `L₀` only.  No compactness and no smallness hypothesis is
involved; this is `exp`/`log` monotonicity, and it is the half that the earlier threshold form of
`Plank.exists_combined_absorption` simply declined to prove. -/
theorem exists_combined_loss_bound (Cang : ℝ≥0) (L₀ : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {a : ℝ≥0}, 0 < a → a < 1 → Real.log (a : ℝ)⁻¹ ≤ L₀ → ∀ N : ℕ,
      (N : ℝ) ≤ Real.logb 2 (16 * (Cang : ℝ) * Kakeya.plankAngleScaleB a) + 1 →
      (8 * Kakeya.plankAngleScaleB a) * (2 * ((N : ℝ) + 1)) ≤ M := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- `K` is the value of `(log a⁻¹) ^ (3/4)` at the top `L₀` of the coarse range
  set K := max L₀ 0 ^ (3 / 4 : ℝ)
  have hK0 : 0 ≤ K := Real.rpow_nonneg (le_max_right L₀ 0) _
  have hKd : 0 ≤ K / Real.log 2 := div_nonneg hK0 hlog2.le
  have hQ0 : 0 ≤ Real.log (max (16 * (Cang : ℝ)) 1) / Real.log 2 :=
    div_nonneg (Real.log_nonneg (le_max_right _ _)) hlog2.le
  refine ⟨8 * Real.exp K * (2 * (Real.log (max (16 * (Cang : ℝ)) 1) / Real.log 2 + 1
      + K / Real.log 2 + 1)), mul_nonneg (by positivity) (by linarith), ?_⟩
  intro a ha ha1 hL N hN
  have hN' := hN.trans (logb_scaleB_le Cang ha ha1)
  set W := Real.log (a : ℝ)⁻¹ ^ (3 / 4 : ℝ) with hW
  have hpow : W ≤ K := by
    rw [hW]
    exact Real.rpow_le_rpow (Kakeya.log_inv_pos ha ha1).le (hL.trans (le_max_left _ _))
      (by norm_num)
  have hB : Kakeya.plankAngleScaleB a ≤ Real.exp K := Real.exp_le_exp.mpr hpow
  have hdiv : W / Real.log 2 ≤ K / Real.log 2 := by gcongr
  exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)

/-- **`1 ≤ a ^ (-η)` for `0 < a < 1` and `η > 0`.**  The trivial fact that lets the coarse range of
`Plank.exists_combined_absorption` charge its finite bound to `Ceta` alone. -/
theorem one_le_rpow_neg_of_lt_one {a : ℝ≥0} (ha : 0 < a) (ha1 : a < 1) {η : ℝ} (hη : 0 < η) :
    (1 : ℝ) ≤ (a : ℝ) ^ (-η) := by
  have haRpos : 0 < (a : ℝ) := by exact_mod_cast ha
  have haR_lt_one : (a : ℝ) < 1 := by exact_mod_cast ha1
  have ha_nonneg : 0 ≤ (a : ℝ) := haRpos.le
  have ha_pow_η_lt_one : (a : ℝ) ^ η < 1 := by
    calc
      (a : ℝ) ^ η < 1 ^ η := Real.rpow_lt_rpow ha_nonneg haR_lt_one hη
      _ = 1 := by simp
  have ha_pow_η_pos : 0 < (a : ℝ) ^ η := Real.rpow_pos_of_pos haRpos η
  have h_one_lt_inv : (1 : ℝ) < ((a : ℝ) ^ η)⁻¹ := by
    have h1pos : 0 < (1 : ℝ) := by norm_num
    have htemp := (one_div_lt_one_div h1pos ha_pow_η_pos).mpr ha_pow_η_lt_one
    simpa using htemp
  calc
    (1 : ℝ) ≤ ((a : ℝ) ^ η)⁻¹ := h_one_lt_inv.le
    _ = (a : ℝ) ^ (-η) := by rw [Real.rpow_neg ha_nonneg η]

/-- **The combined absorption, real-valued form.**  The whole mathematical content of
`Plank.exists_combined_absorption`, with none of its cast bookkeeping: for a uniform `Ceta ≥ 1`
depending on `η` and `Cang` only, `8·B(a) · 2(N+1) ≤ Ceta · a^{-η}` for **every** `0 < a < 1`.

The proof is the scalar case split on `L = log a⁻¹` announced in
`Plank.exists_logThreshold_combined_loss_le_rpow`: above the sub-linearity threshold `L₀`
supplied by that lemma the product is already `≤ a^{-η}`; on the complementary range
`Plank.exists_combined_loss_bound` gives an explicit finite `M`, and `a^{-η} ≥ 1`
(`Plank.one_le_rpow_neg_of_lt_one`) lets `M` be charged to the constant alone.  Taking
`Ceta = max 1 M` covers both.  Both branches are inequalities between real scalars; there is no
second geometric argument anywhere. -/
theorem exists_combined_absorption_real (Cang : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    ∃ Ceta : ℝ, 1 ≤ Ceta ∧ ∀ {a : ℝ≥0}, 0 < a → a < 1 → ∀ N : ℕ,
      (N : ℝ) ≤ Real.logb 2 (16 * (Cang : ℝ) * Kakeya.plankAngleScaleB a) + 1 →
      (8 * Kakeya.plankAngleScaleB a) * (2 * ((N : ℝ) + 1)) ≤ Ceta * (a : ℝ) ^ (-η) := by
  obtain ⟨L₀, hL₀1, hfine⟩ := exists_logThreshold_combined_loss_le_rpow Cang hη
  obtain ⟨M, hM0, hcoarse⟩ := exists_combined_loss_bound Cang L₀
  refine ⟨max 1 M, le_max_left _ _, ?_⟩
  intro a ha ha1 N hN
  have haRpos : 0 < (a : ℝ) := by exact_mod_cast ha
  have haRpow_nonneg : 0 ≤ (a : ℝ) ^ (-η) := (Real.rpow_pos_of_pos haRpos _).le
  rcases le_total L₀ (Real.log (a : ℝ)⁻¹) with h | h
  · have hfine' := hfine ha ha1 h N hN
    calc
      (8 * Kakeya.plankAngleScaleB a) * (2 * ((N : ℝ) + 1)) ≤ (a : ℝ) ^ (-η) := hfine'
      _ = 1 * (a : ℝ) ^ (-η) := by ring
      _ ≤ max 1 M * (a : ℝ) ^ (-η) := mul_le_mul_of_nonneg_right (le_max_left _ _) haRpow_nonneg
  · have hcoarse' := hcoarse ha ha1 h N hN
    have hone : (1 : ℝ) ≤ (a : ℝ) ^ (-η) := one_le_rpow_neg_of_lt_one ha ha1 hη
    have hmax_nonneg : 0 ≤ max 1 M := by
      have h1 : 0 ≤ (1 : ℝ) := by norm_num
      exact le_trans h1 (le_max_left _ _)
    calc
      (8 * Kakeya.plankAngleScaleB a) * (2 * ((N : ℝ) + 1)) ≤ M := hcoarse'
      _ ≤ max 1 M := le_max_right _ _
      _ = max 1 M * 1 := by ring
      _ ≤ max 1 M * (a : ℝ) ^ (-η) := mul_le_mul_of_nonneg_left hone hmax_nonneg

/-- **The product `Cstar · Mtyp` is absorbed by `Ceta · a^{-η}`, for every `0 < a < 1`.**  With
`Cstab = Kakeya.plankAngleScaleB a`, the two losses returned by
`Plank.exists_typicalIntersectionAngle_of_stableFibres` are `Cstar = 8·Cstab` and `Mtyp = 2(N+1)`
with `N ≤ log₂(16·Cang·Cstab) + 1`.  Their product is bounded by `Ceta · a^{-η}` for a *uniform*
`Ceta > 0` depending on `η` and `Cang` only and quantified before every geometric datum, with **no
smallness hypothesis on `a`**.

This is exactly the product hypothesis of `Plank.denseBoxEstimate_boxNormalised_combined`, which
already takes `Ceta` as a parameter subject only to `0 < Ceta`.  The exponent is `-η`, not `-2η`:
charging the product *once* is precisely the factor `a^η` that the combined dense-box estimate
recovers over `Plank.denseBoxEstimate_boxNormalised`.

**On the removed threshold.**  An earlier form of this lemma asserted the bound at `Ceta = 1` and
therefore had to carry a threshold `a < a₀`, its docstring claiming that "no absolute threshold
works".  That claim is true at `Ceta = 1` — as `a → 1⁻` one has `a^{-η} → 1` while
`Cstar · Mtyp ≥ 8` — and false as soon as `Ceta` is allowed to be a uniform constant larger
than `1`, which is all any consumer ever needed.  The mathematics is
`Plank.exists_combined_absorption_real`; this statement is that one pushed through the `ℝ≥0` and
`ENNReal` coercions.

This lemma does not supersede `Plank.exists_bandCount_le_rpow`, which is what the unchanged
`Plank.denseBoxEstimate_boxNormalised` consumes at `Ceta = 1` and which therefore keeps its
threshold. -/
theorem exists_combined_absorption (Cang : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    ∃ Ceta : ℝ≥0, 0 < Ceta ∧ ∀ {a : ℝ≥0}, 0 < a → a < 1 → ∀ N : ℕ,
      (N : ℝ) ≤ Real.logb 2 (16 * (Cang : ℝ) * Kakeya.plankAngleScaleB a) + 1 →
      (((8 * Kakeya.plankAngleScaleB a).toNNReal : ℝ≥0) : ENNReal) *
          (((2 * (N + 1 : ℕ) : ℕ) : ℝ≥0) : ENNReal)
        ≤ (Ceta : ENNReal) * (a : ENNReal) ^ (-η) := by
  obtain ⟨CetaR, hCetaR1, hreal⟩ := exists_combined_absorption_real Cang hη
  have hCetaRpos : (0 : ℝ) < CetaR := by linarith
  refine ⟨CetaR.toNNReal, Real.toNNReal_pos.mpr hCetaRpos, ?_⟩
  intro a ha ha1 N hN
  refine coe_mul_le_mul_rpow_of_real_le ha ?_
  have hx : (((8 * Kakeya.plankAngleScaleB a).toNNReal : ℝ≥0) : ℝ) = 8 * Kakeya.plankAngleScaleB
      a :=
    coe_toNNReal_eight_mul_plankAngleScaleB a
  have hy : ((((2 * (N + 1 : ℕ) : ℕ) : ℝ≥0)) : ℝ) = 2 * ((N : ℝ) + 1) := by
    push_cast
    ring
  have hC : ((CetaR.toNNReal : ℝ≥0) : ℝ) = CetaR :=
    Real.coe_toNNReal CetaR (by linarith)
  rw [hx, hy, hC]
  exact hreal ha ha1 N hN

/-- **Pulling a constant out of the truncation.**  For `K : ℝ≥0` the truncation
`Real.toNNReal` is inactive on `8·K·B(a)`, so the rescaled comparability constant factors as
`K` times the unrescaled one.  This is the only bookkeeping separating
`Plank.exists_combined_absorption_scaled` from `Plank.exists_combined_absorption`. -/
theorem toNNReal_eight_mul_scaled (K a : ℝ≥0) :
    (8 * ((K : ℝ) * Kakeya.plankAngleScaleB a)).toNNReal
      = K * (8 * Kakeya.plankAngleScaleB a).toNNReal := by
  apply NNReal.eq
  have hposB : 0 ≤ Kakeya.plankAngleScaleB a := by
    unfold Kakeya.plankAngleScaleB; exact (Real.exp_pos _).le
  have hposK : 0 ≤ (K : ℝ) := NNReal.coe_nonneg _
  have hpos1 : 0 ≤ 8 * ((K : ℝ) * Kakeya.plankAngleScaleB a) := by nlinarith
  have hpos2 : 0 ≤ 8 * Kakeya.plankAngleScaleB a := by nlinarith
  calc
    ((8 * ((K : ℝ) * Kakeya.plankAngleScaleB a)).toNNReal : ℝ) = 8 * ((K : ℝ) *
        Kakeya.plankAngleScaleB a) :=
      Real.coe_toNNReal _ hpos1
    _ = (K : ℝ) * (8 * Kakeya.plankAngleScaleB a) := by ring
    _ = (K : ℝ) * ((8 * Kakeya.plankAngleScaleB a).toNNReal : ℝ) := by rw [Real.coe_toNNReal _
        hpos2]
    _ = ((K * (8 * Kakeya.plankAngleScaleB a).toNNReal : ℝ≥0) : ℝ) := rfl

/-- **The combined absorption at a rescaled stability constant.**
`Plank.exists_combined_absorption` with `Kakeya.plankAngleScaleB a` replaced by
`K · Kakeya.plankAngleScaleB a` for a fixed `K ≥ 1`.

The rescaling is needed because the global stability clause that GWZ Lemma 6.11 actually delivers is
at `2 · Kakeya.plankAngleScaleB a` and not at `Kakeya.plankAngleScaleB a`: the typical angle `θ` is
selected by a dyadic pigeonhole across fibres, so it agrees with the fibre-local typical angle only
up to the factor `2` of the angle comparison, and that factor composes with the per-fibre stability
scale.

Since `K` is a constant it is simply absorbed into the uniform constant: apply
`Plank.exists_combined_absorption` at `Cang · K`, obtaining `Ceta₁`, and take `Ceta = K · Ceta₁`.
The earlier threshold form had to spend half the exponent, `K ≤ a^{-η/2}`, on the rescaling and so
paid a smaller threshold `a₀`; with a uniform constant available there is nothing to pay, and the
statement holds for every `0 < a < 1`. -/
theorem exists_combined_absorption_scaled (K Cang : ℝ≥0) (hK : 1 ≤ K) {η : ℝ} (hη : 0 < η) :
    ∃ Ceta : ℝ≥0, 0 < Ceta ∧ ∀ {a : ℝ≥0}, 0 < a → a < 1 → ∀ N : ℕ,
      (N : ℝ) ≤ Real.logb 2 (16 * (Cang : ℝ) * ((K : ℝ) * Kakeya.plankAngleScaleB a)) + 1 →
      (((8 * ((K : ℝ) * Kakeya.plankAngleScaleB a)).toNNReal : ℝ≥0) : ENNReal) *
          (((2 * (N + 1 : ℕ) : ℕ) : ℝ≥0) : ENNReal)
        ≤ (Ceta : ENNReal) * (a : ENNReal) ^ (-η) := by
  obtain ⟨Ceta₁, hCeta₁, habs⟩ := exists_combined_absorption (Cang * K) hη
  have hKpos : 0 < K := by
    have h0_lt_one : (0 : ℝ≥0) < 1 := by norm_num
    exact lt_of_lt_of_le h0_lt_one hK
  refine ⟨K * Ceta₁, mul_pos hKpos hCeta₁, ?_⟩
  intro a ha ha1 N hN
  have hN' : (N : ℝ) ≤ Real.logb 2 (16 * ((Cang * K : ℝ≥0) : ℝ) * Kakeya.plankAngleScaleB a) + 1
      := by
    have h_eq : 16 * (Cang : ℝ) * ((K : ℝ) * Kakeya.plankAngleScaleB a) =
        16 * ((Cang * K : ℝ≥0) : ℝ) * Kakeya.plankAngleScaleB a := by
      push_cast
      ring
    simpa [h_eq] using hN
  have hun : (((8 * Kakeya.plankAngleScaleB a).toNNReal : ℝ≥0) : ENNReal) *
      (((2 * (N + 1 : ℕ) : ℕ) : ℝ≥0) : ENNReal) ≤ (Ceta₁ : ENNReal) * (a : ENNReal) ^ (-η) :=
    habs ha ha1 N hN'
  calc
    (((8 * ((K : ℝ) * Kakeya.plankAngleScaleB a)).toNNReal : ℝ≥0) : ENNReal) *
        (((2 * (N + 1 : ℕ) : ℕ) : ℝ≥0) : ENNReal)
        = ((K * (8 * Kakeya.plankAngleScaleB a).toNNReal : ℝ≥0) : ENNReal) *
            (((2 * (N + 1 : ℕ) : ℕ) : ℝ≥0) : ENNReal) := by
      have h : ((8 * ((K : ℝ) * Kakeya.plankAngleScaleB a)).toNNReal : ℝ≥0) =
          (K * (8 * Kakeya.plankAngleScaleB a).toNNReal : ℝ≥0) :=
        toNNReal_eight_mul_scaled K a
      simp [h]
    _ = (K : ENNReal) * ((((8 * Kakeya.plankAngleScaleB a).toNNReal : ℝ≥0) : ENNReal) *
        (((2 * (N + 1 : ℕ) : ℕ) : ℝ≥0) : ENNReal)) := by
      simp [ENNReal.coe_mul, mul_assoc]
    _ ≤ (K : ENNReal) * ((Ceta₁ : ENNReal) * (a : ENNReal) ^ (-η)) :=
      mul_le_mul' le_rfl hun
    _ = ((K * Ceta₁ : ℝ≥0) : ENNReal) * (a : ENNReal) ^ (-η) := by
      simp [ENNReal.coe_mul, mul_assoc]

end Plank

end
