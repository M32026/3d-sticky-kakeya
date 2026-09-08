/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.Normalized

/-!
# Main Lemma 1, Case (ii): The plank pigeonhole

Split out of `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

namespace ml1Boot

/-! ### The plank pigeonhole -/

/-- **The constant `C_{lem:ml1bootPlankPigeonhole}`** of the plank pigeonhole (blueprint
`def:ml1bootPlankConstant`): the total loss of the plank pigeonhole, the product of the
factoring constant `2` of `lemmafactmax`, of the constant `8` absorbing the passage from the
dyadic classes of the two affine thicknesses `τ₁, τ₂` to a single pair `(a, b)`, and of the
volume-comparison constant `Metric.volume_comparison.C 3` in `ℝ³`.

It depends only on the ambient dimension `3`; in particular not on `δ̃`, on `ρ`, on `γ`, on
`j`, or on the family. -/
noncomputable abbrev plankPigeonhole.C : NNReal := 16 * Metric.volume_comparison.C 3

/-- **The constant `C^vol_{lem:ml1bootPlankPigeonhole}`** (blueprint
`def:ml1bootPlankVolumeConstant`): the *volume* counterpart of the shape constant
`Kakeya.ml1Boot.plankPigeonhole.C`, used in item `item:plankVolume` of
`Kakeya.ml1Boot.exists_plankDimensions`.

The exponent on `C_𝕎` is `3` and not `1`: it is the shape constant of `item:plankDims`
propagated through a product of three thicknesses.  Like `Kakeya.ml1Boot.plankPigeonhole.C`
it depends only on the ambient dimension `3`; in particular not on `δ̃`, `a`, `b`, `ρ`, `γ`,
`j`, or the family.  See blueprint `note:ml1bootPlankVolumeConstantCubed`. -/
noncomputable abbrev plankPigeonhole.C_vol : NNReal :=
  8 * plankPigeonhole.C ^ 3 * Metric.volume_comparison.C 3

/-- **Both numerical requirements on the plank volume constant** (blueprint
`lem:ml1bootPlankVolumeConstantBounds`).

The declared value `8 C³ · Metric.volume_comparison.C 3` of
`Kakeya.ml1Boot.plankPigeonhole.C_vol` dominates the two quantities that the proof of
`Kakeya.ml1Boot.exists_plankDimensions`(iv) has to weaken, namely the upper constant `8 C³`
and the reciprocal of the lower constant `c₃ C⁻³` of
`Kakeya.ml1Boot.volume_bounds_of_isPlankOfDimensions`.

Writing `V = Metric.volume_comparison.C 3 = 4³ / c₃ ≥ 64`, the first reads `8 C³ ≤ 8 C³ V`
and the second `C³ V / 64 ≤ 8 C³ V`.  No tight computation is claimed.  As in
`Kakeya.ml1Boot.plankInTube_constant_bounds` the constant is carried as a parameter;
instantiating `C := Kakeya.ml1Boot.plankPigeonhole.C` returns the blueprint statement. -/
theorem plankPigeonhole_volume_constant_bounds {C : NNReal} (hC : 1 ≤ C) :
    8 * C ^ 3 ≤ 8 * C ^ 3 * Metric.volume_comparison.C 3 ∧
      C ^ 3 / Metric.lt_volume_convexHull.c 3 ≤ 8 * C ^ 3 * Metric.volume_comparison.C 3 := by
  have hc_pos : 0 < Metric.lt_volume_convexHull.c 3 := Metric.lt_volume_convexHull.c_pos 3
  have hc_ne : Metric.lt_volume_convexHull.c 3 ≠ 0 := hc_pos.ne'
  have hV : Metric.volume_comparison.C 3 = 4 ^ 3 / Metric.lt_volume_convexHull.c 3 := rfl
  constructor
  · have hVge1 : 1 ≤ Metric.volume_comparison.C 3 := by
      dsimp [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
      norm_num
    exact le_mul_of_one_le_right (by positivity : 0 ≤ 8 * C ^ 3) hVge1
  · rw [div_le_iff₀ hc_pos, hV]
    have hclear : (8 * C ^ 3 * (4 ^ 3 / Metric.lt_volume_convexHull.c 3)) *
        Metric.lt_volume_convexHull.c 3 = 8 * C ^ 3 * 4 ^ 3 := by
      rw [mul_assoc, div_mul_cancel₀ (4 ^ 3) hc_ne]
    rw [hclear]
    calc
      C ^ 3 ≤ C ^ 3 * (8 * 4 ^ 3) := by
        exact le_mul_of_one_le_right (by positivity : 0 ≤ (C ^ 3 : NNReal))
          (by norm_num : (1 : NNReal) ≤ 8 * 4 ^ 3)
      _ = 8 * C ^ 3 * 4 ^ 3 := by ring

section Pigeonhole

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **`ENNReal.dyadic_pigeonhole₁''` made nonemptiness-preserving**, at no cost in hypotheses.

The engine `Real.dyadic_pigeonhole` (`Kakeya/Pigeonhole.lean:105`-`106`) short-circuits on
`s.sum w ≤ 0` and answers `∅`, so `ENNReal.dyadic_pigeonhole₁''` retains no index at all when the
total weight vanishes.  That is harmless for the weight inequality and fatal for any caller that
needs a surviving index.

The repair needs neither positive weight nor fullness: on the degenerate branch the returned
weight inequality already forces `s.sum w = 0`, so *any* singleton `{i₀}` with `i₀ ∈ s` satisfies
the same inequality, and the dyadic comparison over a singleton is `f i₀ ≤ 2 * f i₀`.

Nonemptiness is stated as an implication rather than as a bare `s'.Nonempty` because that is the
unconditional form: a subset of an empty `s` cannot be nonempty. -/
theorem exists_dyadicClass_nonempty {ι : Type*} {s : Finset ι}
    (w : ι → ENNReal) (f : ι → ENNReal) {a b : NNReal} (ha : 0 < a)
    (h : ∀ i ∈ s, f i ∈ Set.Icc (a : ENNReal) (b : ENNReal)) :
    ∃ s' ⊆ s, (s.Nonempty → s'.Nonempty) ∧
      (∑ i ∈ s, w i
          ≤ ENNReal.ofReal (1 + Real.logb (2 : ℝ) ((b : ℝ) / (a : ℝ))) * ∑ i ∈ s', w i) ∧
        ∀ i ∈ s', ∀ j ∈ s', f i ≤ 2 * f j := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · exact ⟨∅, by simp, by simp, by simp, by simp⟩
  · obtain ⟨s', hsub, hsum, hdy⟩ := ENNReal.dyadic_pigeonhole₁'' s w f ha h
    rcases s'.eq_empty_or_nonempty with rfl | hne
    · have hsum0 : (∑ i ∈ s, w i) = 0 := by
        apply le_antisymm
        · simpa using hsum
        · exact zero_le
      refine ⟨{i₀}, ?_, ?_, ?_, ?_⟩
      · exact Finset.singleton_subset_iff.mpr hi₀
      · intro _
        exact Finset.singleton_nonempty i₀
      · rw [hsum0]
        exact zero_le
      · intro i hi j hj
        rw [Finset.mem_singleton] at hi hj
        subst hi
        subst hj
        exact le_mul_of_one_le_left zero_le one_le_two
    · exact ⟨s', hsub, fun _ => hne, hsum, hdy⟩

/-- **(after GWZ Lemma 4.1, the cross-`m` step) One pair of dimensions for all parents at once**
(blueprint `lem:ml1bootCommonPlankDims`).

`ConvexSpaceBody.Factorization.simDims` compares the affine thicknesses of two parts of the
*same* factorization, so it makes the planks over a single parent `m` comparable with
constant `2` and says nothing across different `m`.  This lemma is the missing upgrade: given
a designated part `rep m` over each parent and the a priori ranges of the three affine
thicknesses, two applications of `ENNReal.dyadic_pigeonhole₁''` — one for `τ₁`, one for `τ₂`,
both weighted by `w` — retain a set of parents `tρ'` carrying all but a
`(1 + log₂ (ρ / δ̃))²` fraction of the weight, on which a *single* pair `(ap, bp)` describes
every plank over every surviving parent.

The constants multiply as `2 · 2 · 2 = 8`: a factor `2` from `simDims` inside each of the two
factorizations being compared, and a factor `2` from each dyadic class.  Hence the hypothesis
`8 ≤ C`, which `Kakeya.ml1Boot.plankPigeonhole.C ≥ 1024` satisfies with room to spare.

The two range hypotheses are exactly what the geometry of the intended application supplies:
`τ₀ ∈ [1/2, 1]` because a plank contains a `δ̃`-tube (whose core is a unit segment, so its
circumradius is at least `1/2`) and lies in `B₁`; and `τ₁, τ₂ ∈ [δ̃, ρ]` because a plank
contains a `δ̃`-tube and lies in a `ρ`-tube, which is within `ρ` of a line.

`rep` is taken as data rather than chosen internally so that the caller controls which part
represents each parent; the conclusion is vacuous over a parent whose set of parts is empty,
which is what happens to a parent whose fibre is emptied by the refinement.

The clause `t_ρ.Nonempty → t_ρ'.Nonempty` costs nothing and is not a positivity assumption on
the weight: it comes from `Kakeya.ml1Boot.exists_dyadicClass_nonempty` in place of
`ENNReal.dyadic_pigeonhole₁''`, which returns `∅` when the total weight vanishes.  It is stated
as an implication because that is the unconditional form. -/
theorem exists_commonPlankDims {C ρ δt : NNReal} (hC : 8 ≤ C) (hδt : 0 < δt) (hδρ : δt ≤ ρ)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u : Finset ι} {tρ : Finset κ}
    (V : ι → ConvexSpaceBody E) (pρ : ι → κ) (w : κ → ENNReal)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u pρ m) V 2)
    (rep : κ → Finset ι) (hrep : ∀ m ∈ tρ, rep m ∈ (F m).parts)
    (hτ₀ : ∀ m ∈ tρ, ∀ part ∈ (F m).parts,
      Metric.ethickness ℝ (part.convexHull_biUnion V).carrier 0 ∈
        Set.Icc (2⁻¹ : ENNReal) 1)
    (hτ₁ : ∀ m ∈ tρ, ∀ part ∈ (F m).parts,
      Metric.ethickness ℝ (part.convexHull_biUnion V).carrier 1 ∈
        Set.Icc (δt : ENNReal) (ρ : ENNReal))
    (hτ₂ : ∀ m ∈ tρ, ∀ part ∈ (F m).parts,
      Metric.ethickness ℝ (part.convexHull_biUnion V).carrier 2 ∈
        Set.Icc (δt : ENNReal) (ρ : ENNReal)) :
    ∃ tρ' ⊆ tρ, (tρ.Nonempty → tρ'.Nonempty) ∧ ∃ ap bp : NNReal, δt ≤ ap ∧ ap ≤ bp ∧ bp ≤ ρ ∧
      ∑ m ∈ tρ, w m
          ≤ ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) ^ 2 * ∑ m ∈ tρ', w m ∧
        ∀ m ∈ tρ', IsPlankFamilyOfDimensions C ap bp (F m).parts
          (fun part => part.convexHull_biUnion V) := by
  classical
  let t₁ : κ → ENNReal := fun m => Metric.ethickness ℝ ((rep m).convexHull_biUnion V).carrier 1
  let t₂ : κ → ENNReal := fun m => Metric.ethickness ℝ ((rep m).convexHull_biUnion V).carrier 2
  let L : ENNReal := ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ)))
  have hτ₁rep : ∀ m ∈ tρ, t₁ m ∈ Set.Icc (δt : ENNReal) (ρ : ENNReal) := by
    intro m hm
    simpa [t₁] using hτ₁ m hm (rep m) (hrep m hm)
  have hτ₂rep : ∀ m ∈ tρ, t₂ m ∈ Set.Icc (δt : ENNReal) (ρ : ENNReal) := by
    intro m hm
    simpa [t₂] using hτ₂ m hm (rep m) (hrep m hm)
  obtain ⟨tρ₁, htρ₁sub, htρ₁ne, htρ₁sum, htρ₁dyad⟩ :=
    exists_dyadicClass_nonempty (s := tρ) w t₁ (a := δt) (b := ρ) hδt hτ₁rep
  have hτ₂rep₁ : ∀ m ∈ tρ₁, t₂ m ∈ Set.Icc (δt : ENNReal) (ρ : ENNReal) :=
    fun m hm => hτ₂rep m (htρ₁sub hm)
  obtain ⟨tρ', htρ'sub₁, htρ'ne₁, htρ'sum, htρ'dyad⟩ :=
    exists_dyadicClass_nonempty (s := tρ₁) w t₂ (a := δt) (b := ρ) hδt hτ₂rep₁
  have htρ'sub : tρ' ⊆ tρ := htρ'sub₁.trans htρ₁sub
  have htρ'ne : tρ.Nonempty → tρ'.Nonempty := fun hne => htρ'ne₁ (htρ₁ne hne)
  have hsum : (∑ m ∈ tρ, w m) ≤ L ^ 2 * (∑ m ∈ tρ', w m) := by
    dsimp [L]
    calc
      (∑ m ∈ tρ, w m)
          ≤ ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) * (∑ m ∈ tρ₁, w m) := htρ₁sum
      _ ≤ ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) *
            (ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) * (∑ m ∈ tρ', w m)) := by
          exact mul_le_mul_right htρ'sum _
      _ = ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) ^ 2 * (∑ m ∈ tρ', w m) := by
          rw [← mul_assoc, pow_two]
  rcases tρ'.eq_empty_or_nonempty with htρ'empty | ⟨m₀, hm₀⟩
  · refine ⟨tρ', htρ'sub, htρ'ne, δt, ρ, le_rfl, hδρ, le_rfl, ?_, ?_⟩
    · simpa [htρ'empty] using hsum
    · intro m hm
      simp [htρ'empty] at hm
  · let ap : NNReal := (t₂ m₀).toNNReal
    let bp : NNReal := (t₁ m₀).toNNReal
    have hm₀ρ : m₀ ∈ tρ := htρ'sub hm₀
    have hm₀₁ : m₀ ∈ tρ₁ := htρ'sub₁ hm₀
    have ht₂top : t₂ m₀ ≠ ⊤ := by
      exact ne_of_lt (lt_of_le_of_lt (hτ₂rep m₀ hm₀ρ).2 ENNReal.coe_lt_top)
    have ht₁top : t₁ m₀ ≠ ⊤ := by
      exact ne_of_lt (lt_of_le_of_lt (hτ₁rep m₀ hm₀ρ).2 ENNReal.coe_lt_top)
    have ht₂eq : (ap : ENNReal) = t₂ m₀ := by
      dsimp [ap]
      exact ENNReal.coe_toNNReal ht₂top
    have ht₁eq : (bp : ENNReal) = t₁ m₀ := by
      dsimp [bp]
      exact ENNReal.coe_toNNReal ht₁top
    have hδap : δt ≤ ap := ENNReal.coe_le_coe.mp (by
      rw [ht₂eq]
      exact (hτ₂rep m₀ hm₀ρ).1)
    have hapbp : ap ≤ bp := ENNReal.coe_le_coe.mp (by
      rw [ht₂eq, ht₁eq]
      dsimp [t₁, t₂]
      exact Metric.ethickness_antitone (by norm_num : (1 : ℕ) ≤ (2 : ℕ)))
    have hbpρ : bp ≤ ρ := ENNReal.coe_le_coe.mp (by
      rw [ht₁eq]
      exact (hτ₁rep m₀ hm₀ρ).2)
    have hplank : ∀ m ∈ tρ', IsPlankFamilyOfDimensions C ap bp (F m).parts
        (fun part => part.convexHull_biUnion V) := by
      intro m hm part hpart
      let W := part.convexHull_biUnion V
      let eth0 : ENNReal := Metric.ethickness ℝ W.carrier 0
      let eth1 : ENNReal := Metric.ethickness ℝ W.carrier 1
      let eth2 : ENNReal := Metric.ethickness ℝ W.carrier 2
      have hmρ : m ∈ tρ := htρ'sub hm
      have hm₁ : m ∈ tρ₁ := htρ'sub₁ hm
      have hτ₀part : (2⁻¹ : ENNReal) ≤ eth0 ∧ eth0 ≤ 1 := by
        simpa [eth0, W] using (hτ₀ m hmρ part hpart)
      have hsim1_up : eth1 ≤ 2 * t₁ m := by
        dsimp [eth1, W, t₁]
        exact (F m).simDims part hpart (rep m) (hrep m hmρ) 1
      have hsim1_lo : t₁ m ≤ 2 * eth1 := by
        dsimp [eth1, W, t₁]
        exact (F m).simDims (rep m) (hrep m hmρ) part hpart 1
      have hsim2_up : eth2 ≤ 2 * t₂ m := by
        dsimp [eth2, W, t₂]
        exact (F m).simDims part hpart (rep m) (hrep m hmρ) 2
      have hsim2_lo : t₂ m ≤ 2 * eth2 := by
        dsimp [eth2, W, t₂]
        exact (F m).simDims (rep m) (hrep m hmρ) part hpart 2
      have ht₁up : t₁ m ≤ 2 * t₁ m₀ := htρ₁dyad m hm₁ m₀ hm₀₁
      have ht₁lo : t₁ m₀ ≤ 2 * t₁ m := htρ₁dyad m₀ hm₀₁ m hm₁
      have ht₂up : t₂ m ≤ 2 * t₂ m₀ := htρ'dyad m hm m₀ hm₀
      have ht₂lo : t₂ m₀ ≤ 2 * t₂ m := htρ'dyad m₀ hm₀ m hm
      have hC0 : (C : ENNReal)⁻¹ ≤ eth0 ∧ eth0 ≤ (C : ENNReal) := by
        constructor
        · have h8C : (8 : ENNReal) ≤ (C : ENNReal) := by exact_mod_cast hC
          have hC8 : (C : ENNReal)⁻¹ ≤ (8 : ENNReal)⁻¹ := ENNReal.inv_le_inv.mpr h8C
          have h82 : (8 : ENNReal)⁻¹ ≤ (2 : ENNReal)⁻¹ := ENNReal.inv_le_inv.mpr (by norm_num)
          exact le_trans (le_trans hC8 h82) hτ₀part.1
        · have h1C : (1 : ENNReal) ≤ (C : ENNReal) := by
            exact le_trans (by norm_num : (1 : ENNReal) ≤ (8 : ENNReal)) (by exact_mod_cast hC)
          exact le_trans hτ₀part.2 h1C
      have hC1 : (C : ENNReal)⁻¹ * (bp : ENNReal) ≤ eth1 ∧
          eth1 ≤ (C : ENNReal) * (bp : ENNReal) := by
        constructor
        · have hbp4 : (bp : ENNReal) ≤ 4 * eth1 := by
            calc
              (bp : ENNReal) = t₁ m₀ := ht₁eq
              _ ≤ 2 * t₁ m := ht₁lo
              _ ≤ 2 * (2 * eth1) := by
                exact mul_le_mul_right hsim1_lo (2 : ENNReal)
              _ = 4 * eth1 := by rw [← mul_assoc]; norm_num
          have h4inv : (4 : ENNReal)⁻¹ * (bp : ENNReal) ≤ eth1 :=
            (ENNReal.inv_mul_le_iff (by norm_num : (4 : ENNReal) ≠ 0)
              (by exact ENNReal.coe_ne_top : (4 : ENNReal) ≠ ⊤)).mpr hbp4
          have hC4inv : (C : ENNReal)⁻¹ ≤ (4 : ENNReal)⁻¹ := by
            have h4C : (4 : ENNReal) ≤ (C : ENNReal) := by
              exact le_trans (by norm_num : (4 : ENNReal) ≤ (8 : ENNReal)) (by exact_mod_cast hC)
            exact ENNReal.inv_le_inv.mpr h4C
          exact le_trans (mul_le_mul_left hC4inv (bp : ENNReal)) h4inv
        · have h4bp : eth1 ≤ 4 * (bp : ENNReal) := by
            calc
              eth1 ≤ 2 * t₁ m := hsim1_up
              _ ≤ 2 * (2 * t₁ m₀) := by
                exact mul_le_mul_right ht₁up (2 : ENNReal)
              _ = 4 * t₁ m₀ := by rw [← mul_assoc]; norm_num
              _ = 4 * (bp : ENNReal) := by rw [ht₁eq]
          have h4C : (4 : ENNReal) ≤ (C : ENNReal) := by
            exact le_trans (by norm_num : (4 : ENNReal) ≤ (8 : ENNReal)) (by exact_mod_cast hC)
          exact le_trans h4bp (mul_le_mul_left h4C (bp : ENNReal))
      have hC2 : (C : ENNReal)⁻¹ * (ap : ENNReal) ≤ eth2 ∧
          eth2 ≤ (C : ENNReal) * (ap : ENNReal) := by
        constructor
        · have hap4 : (ap : ENNReal) ≤ 4 * eth2 := by
            calc
              (ap : ENNReal) = t₂ m₀ := ht₂eq
              _ ≤ 2 * t₂ m := ht₂lo
              _ ≤ 2 * (2 * eth2) := by
                exact mul_le_mul_right hsim2_lo (2 : ENNReal)
              _ = 4 * eth2 := by rw [← mul_assoc]; norm_num
          have h4inv : (4 : ENNReal)⁻¹ * (ap : ENNReal) ≤ eth2 :=
            (ENNReal.inv_mul_le_iff (by norm_num : (4 : ENNReal) ≠ 0)
              (by exact ENNReal.coe_ne_top : (4 : ENNReal) ≠ ⊤)).mpr hap4
          have hC4inv : (C : ENNReal)⁻¹ ≤ (4 : ENNReal)⁻¹ := by
            have h4C : (4 : ENNReal) ≤ (C : ENNReal) := by
              exact le_trans (by norm_num : (4 : ENNReal) ≤ (8 : ENNReal)) (by exact_mod_cast hC)
            exact ENNReal.inv_le_inv.mpr h4C
          exact le_trans (mul_le_mul_left hC4inv (ap : ENNReal)) h4inv
        · have h4ap : eth2 ≤ 4 * (ap : ENNReal) := by
            calc
              eth2 ≤ 2 * t₂ m := hsim2_up
              _ ≤ 2 * (2 * t₂ m₀) := by
                exact mul_le_mul_right ht₂up (2 : ENNReal)
              _ = 4 * t₂ m₀ := by rw [← mul_assoc]; norm_num
              _ = 4 * (ap : ENNReal) := by rw [ht₂eq]
          have h4C : (4 : ENNReal) ≤ (C : ENNReal) := by
            exact le_trans (by norm_num : (4 : ENNReal) ≤ (8 : ENNReal)) (by exact_mod_cast hC)
          exact le_trans h4ap (mul_le_mul_left h4C (ap : ENNReal))
      exact ⟨hC0, hC1, hC2⟩
    refine ⟨tρ', htρ'sub, htρ'ne, ap, bp, hδap, hapbp, hbpρ, hsum, hplank⟩

/-- **Item (iv) of the plank pigeonhole from item (iii)** (blueprint
`lem:ml1bootPlankPigeonholeVolume`).

A plank of dimensions `a × b × 1` with shape constant `C_𝕎` has volume comparable to `a b` with
the *volume* constant `C^vol`.  This is `Kakeya.ml1Boot.volume_bounds_of_isPlankOfDimensions`
at `C := plankPigeonhole.C`, with both sides weakened by
`Kakeya.ml1Boot.plankPigeonhole_volume_constant_bounds`.

No ethickness/affine-thickness translation is needed: `Kakeya.IsPlankOfDimensions` is already
stated in the ethicknesses, which is what the cited volume lemma consumes.  The blueprint
statement carries `0 < a ≤ b ≤ 1`; they are not needed here, so the Lean form is stronger. -/
theorem volume_bounds_of_isPlankOfDimensions_vol (hdim : Module.finrank ℝ E = 3)
    {a b : NNReal} {W : ConvexSpaceBody E}
    (hW : IsPlankOfDimensions plankPigeonhole.C a b W) :
    (plankPigeonhole.C_vol : ENNReal)⁻¹ * (a : ENNReal) * (b : ENNReal) ≤ volume W.carrier ∧
      volume W.carrier
        ≤ (plankPigeonhole.C_vol : ENNReal) * (a : ENNReal) * (b : ENNReal) := by
  have hVge : (1 : NNReal) ≤ Metric.volume_comparison.C 3 := by
    dsimp [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
    norm_num
  have hC1 : 1 ≤ plankPigeonhole.C := by
    dsimp [plankPigeonhole.C]
    exact le_trans (by norm_num : (1 : NNReal) ≤ (16 : NNReal))
      (le_mul_of_one_le_right (by norm_num : (0 : NNReal) ≤ 16) hVge)
  have hC0 : plankPigeonhole.C ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hC1)
  have hc3pos : 0 < Metric.lt_volume_convexHull.c 3 := Metric.lt_volume_convexHull.c_pos 3
  have hCvol0 : plankPigeonhole.C_vol ≠ 0 := by
    have hCvolpos : 0 < plankPigeonhole.C_vol := by
      dsimp [plankPigeonhole.C_vol]
      positivity
    exact ne_of_gt hCvolpos
  have hVol :=
    volume_bounds_of_isPlankOfDimensions hdim hC1 (C := plankPigeonhole.C) hW
  obtain ⟨hL, hU⟩ := hVol
  have hcb := plankPigeonhole_volume_constant_bounds hC1
  have hcmulNN : (plankPigeonhole.C : NNReal) ^ 3 ≤
      plankPigeonhole.C_vol * Metric.lt_volume_convexHull.c 3 := by
    have hx : (plankPigeonhole.C : NNReal) ^ 3 / Metric.lt_volume_convexHull.c 3 ≤
        plankPigeonhole.C_vol := by
      simpa [plankPigeonhole.C_vol] using hcb.2
    exact (div_le_iff₀ hc3pos).mp hx
  have hcmulE : (plankPigeonhole.C : ENNReal) ^ 3 ≤
      (plankPigeonhole.C_vol : ENNReal) * (Metric.lt_volume_convexHull.c 3 : ENNReal) := by
    exact_mod_cast hcmulNN
  have hCvolE : (plankPigeonhole.C_vol : ENNReal) =
      8 * (plankPigeonhole.C : ENNReal) ^ 3 * (Metric.volume_comparison.C 3 : ENNReal) := by
    change ((8 * plankPigeonhole.C ^ 3 * Metric.volume_comparison.C 3 : NNReal) : ENNReal) =
      8 * (plankPigeonhole.C : ENNReal) ^ 3 * (Metric.volume_comparison.C 3 : ENNReal)
    simp [ENNReal.coe_mul, ENNReal.coe_pow]
  have hVgeE : (1 : ENNReal) ≤ (Metric.volume_comparison.C 3 : ENNReal) := by
    exact_mod_cast hVge
  constructor
  · have hC3E0 : (plankPigeonhole.C : ENNReal) ^ 3 ≠ 0 := by
      exact pow_ne_zero 3 (by exact_mod_cast hC0)
    have hC3Et : (plankPigeonhole.C : ENNReal) ^ 3 ≠ ⊤ := by
      exact ENNReal.pow_ne_top ENNReal.coe_ne_top
    have hCvolE0 : (plankPigeonhole.C_vol : ENNReal) ≠ 0 := by exact_mod_cast hCvol0
    have hCvolEt : (plankPigeonhole.C_vol : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hA : (plankPigeonhole.C_vol : ENNReal)⁻¹ * (plankPigeonhole.C : ENNReal) ^ 3 ≤
        (Metric.lt_volume_convexHull.c 3 : ENNReal) := by
      calc
        (plankPigeonhole.C_vol : ENNReal)⁻¹ * (plankPigeonhole.C : ENNReal) ^ 3
            ≤ (plankPigeonhole.C_vol : ENNReal)⁻¹ *
                ((plankPigeonhole.C_vol : ENNReal) *
                  (Metric.lt_volume_convexHull.c 3 : ENNReal)) := by
              exact mul_le_mul_right hcmulE (plankPigeonhole.C_vol : ENNReal)⁻¹
        _ = (Metric.lt_volume_convexHull.c 3 : ENNReal) := by
          rw [← mul_assoc]
          rw [ENNReal.inv_mul_cancel hCvolE0 hCvolEt]
          rw [one_mul]
    have hinv : (plankPigeonhole.C_vol : ENNReal)⁻¹ ≤
        ((plankPigeonhole.C : ENNReal) ^ 3)⁻¹ *
          (Metric.lt_volume_convexHull.c 3 : ENNReal) := by
      calc
        (plankPigeonhole.C_vol : ENNReal)⁻¹
            = (plankPigeonhole.C_vol : ENNReal)⁻¹ * 1 := (mul_one _).symm
        _ = (plankPigeonhole.C_vol : ENNReal)⁻¹ *
              ((plankPigeonhole.C : ENNReal) ^ 3 *
                ((plankPigeonhole.C : ENNReal) ^ 3)⁻¹) := by
              rw [ENNReal.mul_inv_cancel hC3E0 hC3Et]
        _ = ((plankPigeonhole.C_vol : ENNReal)⁻¹ * (plankPigeonhole.C : ENNReal) ^ 3) *
              ((plankPigeonhole.C : ENNReal) ^ 3)⁻¹ := by
              rw [← mul_assoc]
        _ ≤ (Metric.lt_volume_convexHull.c 3 : ENNReal) *
              ((plankPigeonhole.C : ENNReal) ^ 3)⁻¹ := by
              exact mul_le_mul_left hA ((plankPigeonhole.C : ENNReal) ^ 3)⁻¹
        _ = ((plankPigeonhole.C : ENNReal) ^ 3)⁻¹ *
              (Metric.lt_volume_convexHull.c 3 : ENNReal) := by
              rw [mul_comm]
    calc
      (plankPigeonhole.C_vol : ENNReal)⁻¹ * (a : ENNReal) * (b : ENNReal)
          = (plankPigeonhole.C_vol : ENNReal)⁻¹ * ((a : ENNReal) * (b : ENNReal)) := by
            rw [mul_assoc]
      _ ≤ ((plankPigeonhole.C : ENNReal) ^ 3)⁻¹ * (Metric.lt_volume_convexHull.c 3 : ENNReal) *
              ((a : ENNReal) * (b : ENNReal)) := by
            exact mul_le_mul_left hinv ((a : ENNReal) * (b : ENNReal))
      _ ≤ volume W.carrier := hL
  · calc
      volume W.carrier
          ≤ 8 * (plankPigeonhole.C : ENNReal) ^ 3 * ((a : ENNReal) * (b : ENNReal)) := hU
      _ ≤ 8 * (plankPigeonhole.C : ENNReal) ^ 3 * (Metric.volume_comparison.C 3 : ENNReal) *
              ((a : ENNReal) * (b : ENNReal)) := by
            have hb : 8 * (plankPigeonhole.C : ENNReal) ^ 3 ≤
                8 * (plankPigeonhole.C : ENNReal) ^ 3 *
                  (Metric.volume_comparison.C 3 : ENNReal) :=
              le_mul_of_one_le_right (by positivity : 0 ≤ 8 * (plankPigeonhole.C : ENNReal) ^ 3)
                hVgeE
            exact mul_le_mul_left hb ((a : ENNReal) * (b : ENNReal))
      _ ≤ (plankPigeonhole.C_vol : ENNReal) * ((a : ENNReal) * (b : ENNReal)) := by
        rw [hCvolE]
      _ = (plankPigeonhole.C_vol : ENNReal) * (a : ENNReal) * (b : ENNReal) := by
        rw [← mul_assoc]

/-- **The two pigeonhole losses, as a single polylogarithm** (blueprint
`lem:ml1bootPlankPigeonholeLossArith`).

`ConvexSpaceBody.nonempty_factorization.C 3 n δ̃` is the loss `L_{3,n,δ̃}` of the weighted
factorization lemma, and `(1 + log₂ (ρ / δ̃)) ^ 2` the loss of the cross-parent pigeonhole
`Kakeya.ml1Boot.exists_commonPlankDims`.  Their product is a single polylogarithm of degree
`6` times a constant fixed before `δ̃`.  No filter occurs. -/
theorem plankPigeonhole_loss_le_polylog {Ccard : NNReal} (hCcard : 1 ≤ Ccard)
    {δt ρ : NNReal} (hδt0 : 0 < δt) (hδt1 : δt ≤ 1) (hδρ : δt ≤ ρ) (hρ1 : ρ ≤ 1)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : (n : ℝ) ≤ (Ccard : ℝ) * (δt : ℝ) ^ (-4 : ℝ)) :
    ConvexSpaceBody.nonempty_factorization.C 3 n δt
        * ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) ^ 2
      ≤ ENNReal.ofReal (4 * (1 + Real.logb 2 (Ccard : ℝ)))
          * ENNReal.ofReal (1 + Real.logb 2 (1 / (δt : ℝ))) ^ 6 := by
  -- `x := log₂ (1/δ̃) ≥ 0` is the polylogarithm base; `c := log₂ Ccard ≥ 0`.
  let x : ℝ := Real.logb 2 (1 / (δt : ℝ))
  have hδtpos : (0 : ℝ) < (δt : ℝ) := by exact_mod_cast hδt0
  have h1_δ : (1 : ℝ) ≤ 1 / (δt : ℝ) := by
    exact (one_le_div hδtpos).mpr (by exact_mod_cast hδt1)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) h1_δ
  -- ρ/δ̃ ∈ [1, 1/δ̃], so log₂ (ρ/δ̃) ∈ [0, x]
  have hδinv0 : 0 ≤ (δt : ℝ)⁻¹ := inv_nonneg.mpr hδtpos.le
  have hρδ_le : (ρ : ℝ) / (δt : ℝ) ≤ 1 / (δt : ℝ) := by
    have hmρ : (ρ : ℝ) * (δt : ℝ)⁻¹ ≤ (1 : ℝ) * (δt : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hρ1) hδinv0
    calc
      (ρ : ℝ) / (δt : ℝ) = (ρ : ℝ) * (δt : ℝ)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (1 : ℝ) * (δt : ℝ)⁻¹ := hmρ
      _ = 1 / (δt : ℝ) := by rw [div_eq_mul_inv]
  have hρδ_1 : (1 : ℝ) ≤ (ρ : ℝ) / (δt : ℝ) := by
    exact (one_le_div hδtpos).mpr (by exact_mod_cast hδρ)
  have hρpos : (0 : ℝ) < (ρ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le hδt0 hδρ)
  have hρδ_pos : (0 : ℝ) < (ρ : ℝ) / (δt : ℝ) := div_pos hρpos hδtpos
  have hlogρδ : Real.logb 2 ((ρ : ℝ) / (δt : ℝ)) ≤ x := by
    simpa [x] using
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hρδ_pos hρδ_le
  have hB2 : ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) ^ 2 ≤
      ENNReal.ofReal (1 + x) ^ 2 := by
    exact pow_le_pow_left₀ zero_le
      (ENNReal.ofReal_le_ofReal (by linarith)) 2
  -- the `n` factor: 1 + log₂ n ≤ 4 (1 + c) (1 + x)
  let c : ℝ := Real.logb 2 (Ccard : ℝ)
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hCcard)
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hn1)
  have hlogbδ : Real.logb 2 (δt : ℝ) = -Real.logb 2 (1 / (δt : ℝ)) := by
    rw [one_div, Real.logb_inv]
    ring
  have hlogδ4 : Real.logb 2 ((δt : ℝ) ^ (-4 : ℝ)) = 4 * x := by
    calc
      Real.logb 2 ((δt : ℝ) ^ (-4 : ℝ)) = (-4 : ℝ) * Real.logb 2 (δt : ℝ) := by
        rw [Real.logb_rpow_eq_mul_logb_of_pos hδtpos]
      _ = 4 * x := by
        rw [hlogbδ]
        dsimp [x]
        ring
  have hδ4pos : (0 : ℝ) < (δt : ℝ) ^ (-4 : ℝ) := Real.rpow_pos_of_pos hδtpos (-4 : ℝ)
  have hδ4ne : (δt : ℝ) ^ (-4 : ℝ) ≠ 0 := ne_of_gt hδ4pos
  have hCpos : (0 : ℝ) < (Ccard : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : NNReal) < 1) hCcard)
  have hlogb_n : Real.logb 2 (n : ℝ) ≤ c + 4 * x := by
    calc
      Real.logb 2 (n : ℝ) ≤ Real.logb 2 ((Ccard : ℝ) * (δt : ℝ) ^ (-4 : ℝ)) := by
        exact Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hnpos
          (by exact hn)
      _ = Real.logb 2 (Ccard : ℝ) + Real.logb 2 ((δt : ℝ) ^ (-4 : ℝ)) := by
        rw [Real.logb_mul (ne_of_gt hCpos) hδ4ne]
      _ = c + 4 * x := by
        dsimp [c]
        rw [hlogδ4]
  have hpoly : (1 : ℝ) + Real.logb 2 (n : ℝ) ≤ (4 * (1 + c)) * (1 + x) := by
    calc
      1 + Real.logb 2 (n : ℝ) ≤ 1 + (c + 4 * x) := by linarith
      _ ≤ (1 + c) * (1 + 4 * x) := by
        have hcx : 0 ≤ c * x := mul_nonneg hc0 hx0
        nlinarith
      _ ≤ (1 + c) * (4 * (1 + x)) := by
        have h14 : 1 + 4 * x ≤ 4 * (1 + x) := by nlinarith
        have h1c : (0 : ℝ) ≤ 1 + c := by nlinarith
        exact mul_le_mul_of_nonneg_left h14 h1c
      _ = 4 * (1 + c) * (1 + x) := by ring
  -- push the real bounds through `ENNReal.ofReal`
  have hEn : ENNReal.ofReal (1 + Real.logb 2 ((n : ℝ) / 1)) ≤
      ENNReal.ofReal (4 * (1 + c)) * ENNReal.ofReal (1 + x) := by
    calc
      ENNReal.ofReal (1 + Real.logb 2 ((n : ℝ) / 1)) ≤
          ENNReal.ofReal ((4 * (1 + c)) * (1 + x)) := by
        apply ENNReal.ofReal_le_ofReal
        rwa [div_one]
      _ = ENNReal.ofReal (4 * (1 + c)) * ENNReal.ofReal (1 + x) := by
        exact ENNReal.ofReal_mul (by nlinarith [hc0] : 0 ≤ 4 * (1 + c))
  calc
    ConvexSpaceBody.nonempty_factorization.C 3 n δt
        * ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) ^ 2
        = ENNReal.ofReal (1 + Real.logb 2 ((n : ℝ) / 1)) * ENNReal.ofReal (1 + x) ^ 3 *
            ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) ^ 2 := by
          unfold ConvexSpaceBody.nonempty_factorization.C
          dsimp [x]
    _ ≤ ENNReal.ofReal (1 + Real.logb 2 ((n : ℝ) / 1)) *
          ENNReal.ofReal (1 + x) ^ 3 * ENNReal.ofReal (1 + x) ^ 2 := by
        gcongr
    _ ≤ (ENNReal.ofReal (4 * (1 + c)) * ENNReal.ofReal (1 + x)) *
          ENNReal.ofReal (1 + x) ^ 3 * ENNReal.ofReal (1 + x) ^ 2 := by
        gcongr
    _ = ENNReal.ofReal (4 * (1 + c)) * ENNReal.ofReal (1 + x) ^ 6 := by
        ring
    _ = ENNReal.ofReal (4 * (1 + Real.logb 2 (Ccard : ℝ))) *
          ENNReal.ofReal (1 + Real.logb 2 (1 / (δt : ℝ))) ^ 6 := by
        simp [c, x]

/-- Duplicate of the private `eventually_const_le_rpow_neg` in
`Kakeya/DimensionThree/MainLemma1/FrostmanAtEveryScaleCase.lean` (which a Fuse golfer
extracted from `Kakeya.const_le_rpow_neg`).  The original is `private`, so it cannot be
cited; this copy is used by `Kakeya.ml1Boot.eventually_plankPigeonhole_loss_le`.  As `δ → 0⁺`
every finite constant `C ≥ 1` is dominated by `δ ^ (-α)`, and `δ ≤ 1`. -/
private lemma eventually_const_le_rpow_neg {C : ENNReal} (hC1 : 1 ≤ C) (hCtop : C ≠ ⊤)
    {α : ℝ} (hα : 0 < α) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, 0 < δ ∧ δ ≤ 1 ∧ C ≤ (δ : ENNReal) ^ (-α) := by
  have hCpos : (0 : ENNReal) < C := zero_lt_one.trans_le hC1
  have htop : C ^ (-1 / α) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg' hCpos hCtop
  have hδ₁ : (0 : NNReal) < min 1 (C ^ (-1 / α)).toNNReal :=
    lt_min zero_lt_one (by
      rw [← ENNReal.coe_pos, ENNReal.coe_toNNReal htop]
      exact ENNReal.rpow_pos hCpos hCtop)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ₁)]
    with δ (hδ_pos : 0 < δ) hδ_lt
  refine ⟨hδ_pos, hδ_lt.le.trans (min_le_left _ _),
    const_le_rpow_neg hC1 hCtop hα hδ_pos ?_⟩
  calc
    (δ : ENNReal) ≤ ((C ^ (-1 / α)).toNNReal : ENNReal) :=
      ENNReal.coe_le_coe.mpr (hδ_lt.le.trans (min_le_right _ _))
    _ = C ^ (-1 / α) := ENNReal.coe_toNNReal htop

/-- **The two pigeonhole losses are below `δ̃ ^ (-ε'')`** (blueprint
`lem:ml1bootPlankPigeonholeLoss`).

The intersection of three eventualities: `δ̃ ≤ 1`, the polylogarithm absorption
`ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg` at `k = 6` and exponent `ε'' / 2`, and
the absorption of the fixed constant `A = 4 (1 + log₂ C_card)` at the same exponent.

`ρ` and `n` are quantified *inside* the eventuality, which is what the consumer needs: the
parent scale and the cardinality of the tube family are chosen after `δ̃`.  This is legitimate
because `Kakeya.ml1Boot.plankPigeonhole_loss_le_polylog` is uniform in both. -/
theorem eventually_plankPigeonhole_loss_le {ε'' : ℝ} (hε'' : 0 < ε'')
    {Ccard : NNReal} (hCcard : 1 ≤ Ccard) :
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0, ∀ ρ : NNReal, δt ≤ ρ → ρ ≤ 1 →
      ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ (Ccard : ℝ) * (δt : ℝ) ^ (-4 : ℝ) →
        ConvexSpaceBody.nonempty_factorization.C 3 n δt
            * ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) ^ 2
          ≤ (δt : ENNReal) ^ (-ε'') := by
  let A : ENNReal := ENNReal.ofReal (4 * (1 + Real.logb 2 (Ccard : ℝ)))
  have hlog : 0 ≤ Real.logb 2 (Ccard : ℝ) :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hCcard)
  have hA1 : 1 ≤ A := by
    dsimp [A]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have hAtop : A ≠ ⊤ := by
    dsimp [A]
    exact ENNReal.ofReal_ne_top
  have hε₂ : 0 < ε'' / 2 := half_pos hε''
  have hevt_const : ∀ᶠ (δt : NNReal) in 𝓝[>] 0,
      0 < δt ∧ δt ≤ 1 ∧ A ≤ (δt : ENNReal) ^ (-(ε'' / 2)) :=
    eventually_const_le_rpow_neg hA1 hAtop hε₂
  have hevt_poly : ∀ᶠ (δt : NNReal) in 𝓝[>] 0,
      ENNReal.ofReal (1 + Real.logb 2 (1 / (δt : ℝ))) ^ 6
        ≤ (δt : ENNReal) ^ (-(ε'' / 2)) :=
    ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg hε₂ 6
  filter_upwards [hevt_const, hevt_poly] with δt hconst hpoly
  rcases hconst with ⟨hδt0, hδt1, hA_le⟩
  intro ρ hδρ hρ1 n hn1 hn
  calc
    ConvexSpaceBody.nonempty_factorization.C 3 n δt
        * ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) ^ 2
        ≤ A * ENNReal.ofReal (1 + Real.logb 2 (1 / (δt : ℝ))) ^ 6 := by
          exact plankPigeonhole_loss_le_polylog hCcard hδt0 hδt1 hδρ hρ1 hn1 hn
    _ ≤ (δt : ENNReal) ^ (-(ε'' / 2)) * (δt : ENNReal) ^ (-(ε'' / 2)) := by
          exact mul_le_mul' hA_le hpoly
    _ = (δt : ENNReal) ^ (-ε'') := by
          have hδne : (δt : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδt0)
          have hδtop : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
          rw [← ENNReal.rpow_add (-(ε'' / 2)) (-(ε'' / 2)) hδne hδtop]
          congr 1
          ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The transverse ethickness of a dilated tube.**  For a tube `T` of scale `δ` and a ratio
`c > 0`, the `c`-dilate has transverse ethickness at most `c δ` in every rank `k` with
`1 ≤ k ≤ n - 1`.

`Kakeya.Tube.dilate` is a homothety of ratio `c` about the tube's centre, so
`Metric.ethickness_homothety_image_le` scales every ethickness by `‖c‖₊`, and
`Kakeya.ml1Boot.tube_ethickness_bounds` evaluates the undilated transverse ethickness at `δ`.

Note that the dilate is *not* contained in any tube of scale `c δ`: the homothety lengthens the
unit core to length `c`, so a tube containing it needs scale at least `(c-1)/2 + c δ`.  The point
of routing through the homothety is that lengthening the core is a rank-`0` deformation which the
rank-`k ≥ 1` thickness does not feel, so the transverse bound is exactly `c δ` regardless.

At `c = 1` this is `Kakeya.ml1Boot.tube_ethickness_bounds` read as an inequality. -/
theorem ethickness_dilate_tube_le (hn : 2 ≤ Module.finrank ℝ E) {δ : NNReal} (T : Tube δ E)
    {c : ℝ} (hc : 0 < c) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ Module.finrank ℝ E - 1) :
    Metric.ethickness ℝ (Tube.dilate T c).carrier k ≤ ENNReal.ofReal c * (δ : ENNReal) := by
  have hcarrier :
      (Tube.dilate T c).carrier = (AffineMap.homothety T.center c) '' T.carrier := by
    rw [Kakeya.Tube.dilate]
    simp
  calc
    Metric.ethickness ℝ (Tube.dilate T c).carrier k
        ≤ ‖c‖₊ * Metric.ethickness ℝ T.carrier k := by
          rw [hcarrier]
          exact Metric.ethickness_homothety_image_le T.center c T.carrier k
    _ = ‖c‖₊ * (δ : ENNReal) := by
          rw [(tube_ethickness_bounds hn T).2.2 k hk1 hk2]
    _ = ENNReal.ofReal c * (δ : ENNReal) := by
          congr 1
          rw [ENNReal.ofReal_eq_coe_nnreal hc.le]
          congr 1
          exact Real.nnnorm_of_nonneg hc.le

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Ethickness ranges of a plank spanned by `δ̃`-tubes** (blueprint
`lem:ml1bootPlankEthicknessRanges`).

Six inequalities, each a containment followed by `Metric.ethickness_monotone`.  The lower bounds
come from a single contained `δ̃`-tube through `Kakeya.ml1Boot.tube_ethickness_bounds`; the
`τ₀` upper bound from `W ⊆ B₁` through `Metric.ethickness_le_of_subset_closedBall`, and the
`τ₁, τ₂` upper bounds from `W ⊆ T_ρ` through the same tube lemma applied to `T_ρ`.

These are exactly the three range hypotheses of
`Kakeya.ml1Boot.exists_commonPlankDims`, which is why they are proved here. -/
theorem ethickness_bounds_convexHull_tubes (hdim : Module.finrank ℝ E = 3)
    {δt ρ : NNReal} (_hδt0 : 0 < δt) (_hδρ : δt ≤ ρ) (_hρ1 : ρ ≤ 1)
    {ι : Type*} {t : Finset ι} (ht : t.Nonempty)
    (T : ι → Tube δt E) (Tρ : Tube ρ E)
    (hball : ∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hsub : ∀ i ∈ t, (T i).carrier ⊆ Tρ.carrier) :
    Metric.ethickness ℝ
          (t.convexHull_biUnion fun i => (T i).toConvexSpaceBody).carrier 0 ∈
        Set.Icc (2⁻¹ : ENNReal) 1 ∧
      Metric.ethickness ℝ
            (t.convexHull_biUnion fun i => (T i).toConvexSpaceBody).carrier 1 ∈
          Set.Icc (δt : ENNReal) (ρ : ENNReal) ∧
        Metric.ethickness ℝ
              (t.convexHull_biUnion fun i => (T i).toConvexSpaceBody).carrier 2 ∈
            Set.Icc (δt : ENNReal) (ρ : ENNReal) := by
  classical
  let W : ConvexSpaceBody E := t.convexHull_biUnion fun i => (T i).toConvexSpaceBody
  have hn : 2 ≤ Module.finrank ℝ E := by
    omega
  have hk1 : (1 : ℕ) ≤ Module.finrank ℝ E - 1 := by
    omega
  have hk2 : (2 : ℕ) ≤ Module.finrank ℝ E - 1 := by
    omega
  have hmem : ∀ i : ι, i ∈ t → (T i).carrier ⊆ W.carrier := by
    intro i hi
    dsimp [W]
    rw [Finset.Nonempty.convexHull_biUnion_carrier ht]
    exact fun x hx =>
      Convexity.subset_convexHull_self (Set.subset_biUnion_of_mem hi hx)
  have hWsub : W.carrier ⊆ Tρ.carrier := by
    dsimp [W]
    rw [Finset.Nonempty.convexHull_biUnion_subset_iff ht
      (fun i => (T i).toConvexSpaceBody) Tρ.convex']
    intro i hi
    exact hsub i hi
  have hWball : W.carrier ⊆ Metric.closedBall (0 : E) 1 := by
    dsimp [W]
    rw [Finset.Nonempty.convexHull_biUnion_subset_iff ht
      (fun i => (T i).toConvexSpaceBody) (convex_closedBall 0 1).isConvexSet]
    intro i hi
    exact hball i hi
  have h0up : Metric.ethickness ℝ W.carrier 0 ≤ (1 : ENNReal) := by
    exact Metric.ethickness_le_of_subset_closedBall (x := (0 : E)) 1 hWball 0
  have h1up : Metric.ethickness ℝ W.carrier 1 ≤ (ρ : ENNReal) := by
    exact (Metric.ethickness_monotone hWsub 1).trans
      (le_of_eq ((tube_ethickness_bounds hn Tρ).2.2 1 (by norm_num) hk1))
  have h2up : Metric.ethickness ℝ W.carrier 2 ≤ (ρ : ENNReal) := by
    exact (Metric.ethickness_monotone hWsub 2).trans
      (le_of_eq ((tube_ethickness_bounds hn Tρ).2.2 2 (by norm_num) hk2))
  obtain ⟨i, hi⟩ := ht
  have h0lo0 : (2⁻¹ : ENNReal) ≤ Metric.ethickness ℝ (T i).carrier 0 := by
    simpa using (tube_ethickness_bounds hn (T i)).1
  have h0lo : (2⁻¹ : ENNReal) ≤ Metric.ethickness ℝ W.carrier 0 := by
    exact h0lo0.trans (Metric.ethickness_monotone (hmem i hi) 0)
  have h1lo : (δt : ENNReal) ≤ Metric.ethickness ℝ W.carrier 1 := by
    calc
      (δt : ENNReal) = Metric.ethickness ℝ (T i).carrier 1 :=
        ((tube_ethickness_bounds hn (T i)).2.2 1 (by norm_num) hk1).symm
      _ ≤ Metric.ethickness ℝ W.carrier 1 := Metric.ethickness_monotone (hmem i hi) 1
  have h2lo : (δt : ENNReal) ≤ Metric.ethickness ℝ W.carrier 2 := by
    calc
      (δt : ENNReal) = Metric.ethickness ℝ (T i).carrier 2 :=
        ((tube_ethickness_bounds hn (T i)).2.2 2 (by norm_num) hk2).symm
      _ ≤ Metric.ethickness ℝ W.carrier 2 := Metric.ethickness_monotone (hmem i hi) 2
  exact ⟨⟨h0lo, h0up⟩, ⟨⟨h1lo, h1up⟩, ⟨h2lo, h2up⟩⟩⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Ethickness ranges of a plank spanned by `δ̃`-tubes lying in a *dilated* parent** (blueprint
`lem:ml1bootPlankEthicknessRanges`, read at a dilated parent).

This is `Kakeya.ml1Boot.ethickness_bounds_convexHull_tubes` with the parent containment weakened
from `T_i ⊆ T_ρ` to `T_i ⊆ c · T_ρ`, which is what a parent family merged by
`Kakeya.ml1Boot.exists_merged_rhoParentFamily` supplies.  The two transverse brackets widen from
`ρ` to `c ρ` and nothing else moves:

* the `τ₀` bracket `[1/2, 1]` is untouched, because its upper bound comes from `hball` — the
  containment of the tubes in the unit ball — and not from the parent at all;
* the two lower bounds `δ̃` are untouched, because they come from a single *contained* `δ̃`-tube
  through `Kakeya.ml1Boot.tube_ethickness_bounds` and never mention the parent;
* the two upper bounds pass through `Kakeya.ml1Boot.ethickness_dilate_tube_le`, which is where
  the factor `c` enters, in place of the undilated `tube_ethickness_bounds`.

Both sides of each widened bracket carry a single power of `ρ`, so the factor `c` sits on the
ratio rather than on a spurious lower-order term.  At `c = 1` the dilate is the identity and
every bracket is the original one. -/
theorem ethickness_bounds_convexHull_tubes_dilate (hdim : Module.finrank ℝ E = 3)
    {δt ρ : NNReal} (_hδt0 : 0 < δt) (_hδρ : δt ≤ ρ) {c : ℝ} (hc : 0 < c)
    {ι : Type*} {t : Finset ι} (ht : t.Nonempty)
    (T : ι → Tube δt E) (Tρ : Tube ρ E)
    (hball : ∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hsub : ∀ i ∈ t, (T i).carrier ⊆ (Tube.dilate Tρ c).carrier) :
    Metric.ethickness ℝ
          (t.convexHull_biUnion fun i => (T i).toConvexSpaceBody).carrier 0 ∈
        Set.Icc (2⁻¹ : ENNReal) 1 ∧
      Metric.ethickness ℝ
            (t.convexHull_biUnion fun i => (T i).toConvexSpaceBody).carrier 1 ∈
          Set.Icc (δt : ENNReal) (ENNReal.ofReal c * (ρ : ENNReal)) ∧
        Metric.ethickness ℝ
              (t.convexHull_biUnion fun i => (T i).toConvexSpaceBody).carrier 2 ∈
            Set.Icc (δt : ENNReal) (ENNReal.ofReal c * (ρ : ENNReal)) := by
  classical
  let W : ConvexSpaceBody E := t.convexHull_biUnion fun i => (T i).toConvexSpaceBody
  have hn : 2 ≤ Module.finrank ℝ E := by
    omega
  have hk1 : (1 : ℕ) ≤ Module.finrank ℝ E - 1 := by
    omega
  have hk2 : (2 : ℕ) ≤ Module.finrank ℝ E - 1 := by
    omega
  have hmem : ∀ i : ι, i ∈ t → (T i).carrier ⊆ W.carrier := by
    intro i hi
    dsimp [W]
    rw [Finset.Nonempty.convexHull_biUnion_carrier ht]
    exact fun x hx =>
      Convexity.subset_convexHull_self (Set.subset_biUnion_of_mem hi hx)
  have hWsub : W.carrier ⊆ (Tube.dilate Tρ c).carrier := by
    dsimp [W]
    rw [Finset.Nonempty.convexHull_biUnion_subset_iff ht
      (fun i => (T i).toConvexSpaceBody) (Tube.dilate Tρ c).convex']
    intro i hi
    exact hsub i hi
  have hWball : W.carrier ⊆ Metric.closedBall (0 : E) 1 := by
    dsimp [W]
    rw [Finset.Nonempty.convexHull_biUnion_subset_iff ht
      (fun i => (T i).toConvexSpaceBody) (convex_closedBall 0 1).isConvexSet]
    intro i hi
    exact hball i hi
  have h0up : Metric.ethickness ℝ W.carrier 0 ≤ (1 : ENNReal) := by
    exact Metric.ethickness_le_of_subset_closedBall (x := (0 : E)) 1 hWball 0
  have h1up : Metric.ethickness ℝ W.carrier 1 ≤ ENNReal.ofReal c * (ρ : ENNReal) := by
    exact (Metric.ethickness_monotone hWsub 1).trans
      (ethickness_dilate_tube_le hn Tρ hc (by norm_num) hk1)
  have h2up : Metric.ethickness ℝ W.carrier 2 ≤ ENNReal.ofReal c * (ρ : ENNReal) := by
    exact (Metric.ethickness_monotone hWsub 2).trans
      (ethickness_dilate_tube_le hn Tρ hc (by norm_num) hk2)
  obtain ⟨i, hi⟩ := ht
  have h0lo0 : (2⁻¹ : ENNReal) ≤ Metric.ethickness ℝ (T i).carrier 0 := by
    simpa using (tube_ethickness_bounds hn (T i)).1
  have h0lo : (2⁻¹ : ENNReal) ≤ Metric.ethickness ℝ W.carrier 0 := by
    exact h0lo0.trans (Metric.ethickness_monotone (hmem i hi) 0)
  have h1lo : (δt : ENNReal) ≤ Metric.ethickness ℝ W.carrier 1 := by
    calc
      (δt : ENNReal) = Metric.ethickness ℝ (T i).carrier 1 :=
        ((tube_ethickness_bounds hn (T i)).2.2 1 (by norm_num) hk1).symm
      _ ≤ Metric.ethickness ℝ W.carrier 1 := Metric.ethickness_monotone (hmem i hi) 1
  have h2lo : (δt : ENNReal) ≤ Metric.ethickness ℝ W.carrier 2 := by
    calc
      (δt : ENNReal) = Metric.ethickness ℝ (T i).carrier 2 :=
        ((tube_ethickness_bounds hn (T i)).2.2 2 (by norm_num) hk2).symm
      _ ≤ Metric.ethickness ℝ W.carrier 2 := Metric.ethickness_monotone (hmem i hi) 2
  exact ⟨⟨h0lo, h0up⟩, ⟨⟨h1lo, h1up⟩, ⟨h2lo, h2up⟩⟩⟩

/-- **Gluing the per-parent subfamilies into one index set** (blueprint
`lem:ml1bootPlankPigeonholeGlue`).

Each block `um m` lies in the fibre over `m`, so the blocks lie in distinct fibres of `pρ` and
cutting the union down to the fibre over `m` returns `um m` when `m ∈ tρ'` and nothing
otherwise.  This is what makes discarding the parents outside `tρ'` harmless: it deletes only
whole fibres, so the factorizations over the surviving parents are untouched, and items (iii)
and (iv) of `Kakeya.ml1Boot.exists_plankDimensions` become statements about an empty set of
parts over a discarded parent. -/
theorem fibre_biUnion_eq {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {u : Finset ι} {tρ tρ' : Finset κ} (htρ' : tρ' ⊆ tρ) (pρ : ι → κ)
    (um : κ → Finset ι) (hum : ∀ m ∈ tρ, um m ⊆ fibre u pρ m) :
    (∀ m ∈ tρ', fibre (tρ'.biUnion um) pρ m = um m) ∧
      ∀ m ∈ tρ, m ∉ tρ' → fibre (tρ'.biUnion um) pρ m = ∅ := by
  constructor
  · intro m hmtρ'
    ext i
    constructor
    · intro hi
      rw [fibre] at hi
      rw [Finset.mem_filter] at hi
      rcases hi with ⟨hbi, hpi⟩
      rw [Finset.mem_biUnion] at hbi
      rcases hbi with ⟨m', hm', him'⟩
      have hfib' : i ∈ u.filter (fun j => pρ j = m') := hum m' (htρ' hm') him'
      have hpm' : pρ i = m' := (Finset.mem_filter.mp hfib').2
      have hm'eq : m' = m := hpm'.symm.trans hpi
      rw [hm'eq] at him'
      exact him'
    · intro him
      have hfib : i ∈ u.filter (fun j => pρ j = m) := hum m (htρ' hmtρ') him
      have hpm : pρ i = m := (Finset.mem_filter.mp hfib).2
      rw [fibre]
      rw [Finset.mem_filter]
      rw [Finset.mem_biUnion]
      exact ⟨⟨m, hmtρ', him⟩, hpm⟩
  · intro m hmtρ hmn
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    rw [fibre] at hi
    rw [Finset.mem_filter] at hi
    rcases hi with ⟨hbi, hpi⟩
    rw [Finset.mem_biUnion] at hbi
    rcases hbi with ⟨m', hm', him'⟩
    have hfib' : i ∈ u.filter (fun p => pρ p = m') := hum m' (htρ' hm') him'
    have hpm' : pρ i = m' := (Finset.mem_filter.mp hfib').2
    have hm'eq : m' = m := hpm'.symm.trans hpi
    exact hmn (by simpa [hm'eq] using hm')

/-- **Chaining a per-fibre loss with a cross-fibre loss** (blueprint
`lem:ml1bootPlankPigeonholeChain`).

Purely combinatorial, and entirely in `[0, ∞]`, where multiplying an inequality by a constant is
monotone and nothing is cancelled.  Decompose over the fibres, apply the per-fibre loss `L`,
then the cross-fibre loss `D`, then recompose using
`Kakeya.ml1Boot.fibre_biUnion_eq`. -/
theorem sum_le_of_fibrewise_loss {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {u : Finset ι} {tρ tρ' : Finset κ} (htρ' : tρ' ⊆ tρ) (pρ : ι → κ)
    (hpρ : ∀ i ∈ u, pρ i ∈ tρ) (um : κ → Finset ι) (hum : ∀ m ∈ tρ, um m ⊆ fibre u pρ m)
    (w : ι → ENNReal) {L D : ENNReal}
    (hL : ∀ m ∈ tρ, ∑ i ∈ fibre u pρ m, w i ≤ L * ∑ i ∈ um m, w i)
    (hD : ∑ m ∈ tρ, ∑ i ∈ um m, w i ≤ D * ∑ m ∈ tρ', ∑ i ∈ um m, w i) :
    ∑ i ∈ u, w i ≤ L * D * ∑ i ∈ tρ'.biUnion um, w i := by
  classical
  have hdisj : (tρ' : Set κ).PairwiseDisjoint um := by
    intro m hm m' hm' hmm'
    change Disjoint (um m) (um m')
    rw [Finset.disjoint_left]
    intro i him him'
    have hfibm : i ∈ fibre u pρ m := hum m (htρ' hm) him
    have hfibm' : i ∈ fibre u pρ m' := hum m' (htρ' hm') him'
    have hpm : pρ i = m := (Finset.mem_filter.mp hfibm).2
    have hpm' : pρ i = m' := (Finset.mem_filter.mp hfibm').2
    exact hmm' (hpm.symm.trans hpm')
  calc
    (∑ i ∈ u, w i) = ∑ m ∈ tρ, ∑ i ∈ fibre u pρ m, w i := by
      simp only [fibre]
      exact (Finset.sum_fiberwise_of_maps_to hpρ w).symm
  _ ≤ ∑ m ∈ tρ, L * ∑ i ∈ um m, w i := by
      exact Finset.sum_le_sum (fun _ hm => hL _ hm)
  _ = L * ∑ m ∈ tρ, ∑ i ∈ um m, w i := by
      rw [← Finset.mul_sum]
  _ ≤ L * (D * ∑ m ∈ tρ', ∑ i ∈ um m, w i) := by
      exact mul_le_mul_right hD L
  _ = L * D * ∑ i ∈ tρ'.biUnion um, w i := by
      rw [← mul_assoc]
      rw [← Finset.sum_biUnion hdisj]

/-- The factorization loss `Kakeya.ConvexSpaceBody.nonempty_factorization.C` is monotone in its
cardinality argument.  This is what lets the per-fibre loss of
`Kakeya.ml1Boot.isCRefinement_plankPigeonhole` be enlarged from `|u[m]|` to the single
`m`-independent value `|u|`; the case `m = 0` is covered because `Real.logb 2 0 = 0`. -/
private lemma nonempty_factorization_C_mono_card {m n : ℕ} (hmn : m ≤ n) (hn : 1 ≤ n)
    (dim : ℕ) (δ : NNReal) :
    ConvexSpaceBody.nonempty_factorization.C dim m δ
      ≤ ConvexSpaceBody.nonempty_factorization.C dim n δ := by
  unfold ConvexSpaceBody.nonempty_factorization.C
  have hlog : Real.logb 2 (m : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0]
      simpa [Real.logb_zero] using
        (Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hn) :
          0 ≤ Real.logb 2 (n : ℝ))
    · exact Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (by exact_mod_cast hmpos) (by exact_mod_cast hmn)
  have hob : ENNReal.ofReal (1 + Real.logb 2 ((m : ℝ) / 1)) ≤
      ENNReal.ofReal (1 + Real.logb 2 ((n : ℝ) / 1)) := by
    exact ENNReal.ofReal_le_ofReal (by
      rw [div_one, div_one]
      exact add_le_add (le_rfl : (1 : ℝ) ≤ (1 : ℝ)) hlog)
  exact mul_le_mul_left hob _

/-- `Kakeya.ml1Boot.card_le` transported from `ℝ≥0∞` to `ℝ`, which is the form the cardinality
hypothesis of `Kakeya.ml1Boot.eventually_plankPigeonhole_loss_le` is stated in. -/
private lemma card_le_real (hdim : Module.finrank ℝ E = 3) {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hED : (s : Set ι).Pairwise fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) :
    (s.card : ℝ) ≤ (cardBound.C : ℝ) * (δ : ℝ) ^ (-4 : ℝ) := by
  have hcard : (s.card : ENNReal) ≤ (cardBound.C : ENNReal) * (δ : ENNReal) ^ (-4 : ℝ) :=
    card_le hdim hδ hδ1 s T hball hED
  have hδ0R : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have heq0 : (δ : ENNReal) ^ (-4 : ℝ) = ENNReal.ofReal ((δ : ℝ) ^ (-4 : ℝ)) := by
    rw [← ENNReal.ofReal_coe_nnreal (p := (δ : NNReal))]
    exact ENNReal.ofReal_rpow_of_pos (x := (δ : ℝ)) (p := (-4 : ℝ)) hδ0R
  have heq : (cardBound.C : ENNReal) * (δ : ENNReal) ^ (-4 : ℝ)
      = ENNReal.ofReal ((cardBound.C : ℝ) * (δ : ℝ) ^ (-4 : ℝ)) := by
    rw [← (ENNReal.ofReal_coe_nnreal (p := (cardBound.C : NNReal)))]
    rw [heq0]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (cardBound.C : ℝ))]
  have h' : ENNReal.ofReal (s.card : ℝ) ≤ ENNReal.ofReal ((cardBound.C : ℝ) * (δ : ℝ) ^ (-4 : ℝ)) := by
    rw [ENNReal.ofReal_natCast, ← heq]
    exact hcard
  have hnn : 0 ≤ (cardBound.C : ℝ) * (δ : ℝ) ^ (-4 : ℝ) := by
    exact mul_nonneg (by positivity : 0 ≤ (cardBound.C : ℝ))
      ((Real.rpow_pos_of_pos hδ0R (-4 : ℝ)).le)
  exact (ENNReal.ofReal_le_ofReal_iff hnn).mp h'

/-- The refinement constant of `Kakeya.ml1Boot.isCRefinement_plankPigeonhole` against the
multiplicative loss it is the reciprocal of: the `ℝ≥0`-inverse of `δ ^ ε` coerces to the
`ℝ≥0∞`-power `δ ^ (-ε)`. -/
private lemma coe_inv_nnrpow_eq_rpow_neg {δ : NNReal} (hδ : 0 < δ) {ε : ℝ} (hε : 0 ≤ ε) :
    (((⟨(δ : ℝ) ^ ε, by positivity⟩ : NNReal)⁻¹ : NNReal) : ENNReal) = (δ : ENNReal) ^ (-ε) := by
  have hD0 : (⟨(δ : ℝ) ^ ε, by positivity⟩ : NNReal) ≠ 0 := by
    have hδ0R : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
    exact_mod_cast (ne_of_gt (Real.rpow_pos_of_pos hδ0R ε))
  rw [ENNReal.coe_inv hD0]
  change (↑(δ ^ ε : NNReal) : ENNReal)⁻¹ = (δ : ENNReal) ^ (-ε)
  rw [ENNReal.coe_rpow_of_nonneg δ hε]
  rw [ENNReal.rpow_neg]

/-- The filter-free core of `Kakeya.ml1Boot.isCRefinement_plankPigeonhole`: the per-fibre loss is
made `m`-independent, chained with the cross-fibre loss, and the product of the two is absorbed
into `δ̃ ^ (-ε'')`.  The absorption is supplied as the hypothesis `hloss`, which is what
`Kakeya.ml1Boot.eventually_plankPigeonhole_loss_le` provides for all small `δ̃`. -/
private lemma sum_le_rpow_neg_of_plankLosses (hdim : Module.finrank ℝ E = 3) {ε'' : ℝ}
    {δt ρ : NNReal} (hδt : 0 < δt) (hδt1 : δt ≤ 1)
    (hloss : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ (cardBound.C : ℝ) * (δt : ℝ) ^ (-4 : ℝ) →
      ConvexSpaceBody.nonempty_factorization.C 3 n δt
          * ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) ^ 2
        ≤ (δt : ENNReal) ^ (-ε''))
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u : Finset ι} {tρ tρ' : Finset κ}
    (T : ι → ShadedTube δt E) (pρ : ι → κ) (um : κ → Finset ι)
    (hune : u.Nonempty)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hED : (u : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier))
    (hpρ : ∀ i ∈ u, pρ i ∈ tρ) (htρ' : tρ' ⊆ tρ)
    (hum : ∀ m ∈ tρ, um m ⊆ fibre u pρ m)
    (hper : ∀ m ∈ tρ, ∑ i ∈ fibre u pρ m, volume ((T i).toShadedBody).shade
      ≤ ConvexSpaceBody.nonempty_factorization.C 3 (fibre u pρ m).card δt
        * ∑ i ∈ um m, volume ((T i).toShadedBody).shade)
    (hcross : ∑ m ∈ tρ, ∑ i ∈ um m, volume ((T i).toShadedBody).shade
      ≤ ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) ^ 2
        * ∑ m ∈ tρ', ∑ i ∈ um m, volume ((T i).toShadedBody).shade) :
    ∑ i ∈ u, volume ((T i).toShadedBody).shade
      ≤ (δt : ENNReal) ^ (-ε'')
        * ∑ i ∈ tρ'.biUnion um, volume ((T i).toShadedBody).shade := by
  classical
  let w : ι → ENNReal := fun i => volume ((T i).toShadedBody).shade
  let L : ENNReal := ConvexSpaceBody.nonempty_factorization.C 3 u.card δt
  let D : ENNReal := ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) ^ 2
  have hu1 : 1 ≤ u.card := Finset.card_pos.mpr hune
  have hL : ∀ m ∈ tρ, ∑ i ∈ fibre u pρ m, w i ≤ L * ∑ i ∈ um m, w i := by
    intro m hm
    have hcardle : (fibre u pρ m).card ≤ u.card := by
      rw [fibre]
      exact Finset.card_le_card (fun i hi => (Finset.mem_filter.mp hi).1)
    have hmono : ConvexSpaceBody.nonempty_factorization.C 3 (fibre u pρ m).card δt ≤ L := by
      dsimp [L]
      exact nonempty_factorization_C_mono_card hcardle hu1 3 δt
    calc
      ∑ i ∈ fibre u pρ m, w i
          ≤ ConvexSpaceBody.nonempty_factorization.C 3 (fibre u pρ m).card δt
              * ∑ i ∈ um m, w i := by
            dsimp [w]
            exact hper m hm
      _ ≤ L * ∑ i ∈ um m, w i := mul_le_mul_left hmono (∑ i ∈ um m, w i)
  have hD : ∑ m ∈ tρ, ∑ i ∈ um m, w i ≤ D * ∑ m ∈ tρ', ∑ i ∈ um m, w i := by
    dsimp [w, D]
    exact hcross
  have hchain : (∑ i ∈ u, w i) ≤ L * D * ∑ i ∈ tρ'.biUnion um, w i :=
    sum_le_of_fibrewise_loss htρ' pρ hpρ um hum w (L := L) (D := D) hL hD
  have hcardbd : (u.card : ℝ) ≤ (cardBound.C : ℝ) * (δt : ℝ) ^ (-4 : ℝ) :=
    card_le_real hdim hδt hδt1 u (fun i => (T i).toTube) hball hED
  have hloss' : L * D ≤ (δt : ENNReal) ^ (-ε'') := by
    dsimp [L, D]
    exact hloss u.card hu1 hcardbd
  simpa [w] using calc
    (∑ i ∈ u, w i) ≤ L * D * ∑ i ∈ tρ'.biUnion um, w i := hchain
    _ ≤ (δt : ENNReal) ^ (-ε'') * ∑ i ∈ tρ'.biUnion um, w i :=
      mul_le_mul_left hloss' (∑ i ∈ tρ'.biUnion um, w i)

/-- The exit step of `Kakeya.ml1Boot.isCRefinement_plankPigeonhole`: a weighted-sum inequality with
loss `δ̃ ^ (-ε'')` is a `δ̃ ^ ε''`-refinement.  This is `Kakeya.ShadedBody.isCRefinement_of_sum_le`
with the constant put in the form the plank pigeonhole states it in. -/
private lemma isCRefinement_of_sum_le_rpow {δt : NNReal} (hδt : 0 < δt) {ε'' : ℝ} (hε'' : 0 < ε'')
    {ι : Type*} {u s' : Finset ι} (T : ι → ShadedTube δt E) (hs' : s' ⊆ u)
    (hsum : ∑ i ∈ u, volume ((T i).toShadedBody).shade
      ≤ (δt : ENNReal) ^ (-ε'') * ∑ i ∈ s', volume ((T i).toShadedBody).shade) :
    ShadedBody.IsCRefinement s' (fun i => (T i).toShadedBody) u (fun i => (T i).toShadedBody)
      ⟨(δt : ℝ) ^ ε'', by positivity⟩ := by
  let D : NNReal := ⟨(δt : ℝ) ^ ε'', by positivity⟩
  have hD0 : D ≠ 0 := by
    have hδtR : (0 : ℝ) < (δt : ℝ) := by exact_mod_cast hδt
    dsimp [D]
    exact_mod_cast (ne_of_gt (Real.rpow_pos_of_pos hδtR ε''))
  have hDinv0 : D⁻¹ ≠ 0 := inv_ne_zero hD0
  have hcoef : ((D⁻¹ : NNReal) : ENNReal) = (δt : ENNReal) ^ (-ε'') := by
    dsimp [D]
    exact coe_inv_nnrpow_eq_rpow_neg hδt hε''.le
  have hsum' : (∑ i ∈ u, volume ((T i).toShadedBody).shade) ≤
      ((D⁻¹ : NNReal) : ENNReal) * ∑ i ∈ s', volume ((T i).toShadedBody).shade := by
    rw [hcoef]
    exact hsum
  simpa [D, inv_inv] using ShadedBody.isCRefinement_of_sum_le (s := u) (s' := s')
    (V := fun i => (T i).toShadedBody) hs' (D := (D : NNReal)⁻¹) hDinv0 hsum'

/-- **Item (i) of the plank pigeonhole from the two weight losses** (blueprint
`lem:ml1bootPlankPigeonholeRefine`).

Four citations.  Upgrade the per-fibre loss from `|u[m]|` to `|u|` by monotonicity of
`n ↦ 1 + log₂ n`; chain the two losses with `Kakeya.ml1Boot.sum_le_of_fibrewise_loss`; bound
their product by `δ̃ ^ (-ε'')` with `Kakeya.ml1Boot.eventually_plankPigeonhole_loss_le`, whose
cardinality hypothesis is `Kakeya.ml1Boot.card_le` together with nonemptiness of `u`; and convert
the resulting weighted-sum inequality with `Kakeya.isCRefinement_of_sum_le`. -/
theorem isCRefinement_plankPigeonhole (hdim : Module.finrank ℝ E = 3) {ε'' : ℝ} (hε'' : 0 < ε'') :
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0, ∀ ρ : NNReal, δt ≤ ρ → ρ ≤ 1 →
      ∀ {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u : Finset ι} {tρ tρ' : Finset κ}
        (T : ι → ShadedTube δt E) (pρ : ι → κ) (um : κ → Finset ι),
        u.Nonempty →
        (∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (u : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        (∀ i ∈ u, pρ i ∈ tρ) → tρ' ⊆ tρ →
        (∀ m ∈ tρ, um m ⊆ fibre u pρ m) →
        (∀ m ∈ tρ, ∑ i ∈ fibre u pρ m, volume ((T i).toShadedBody).shade
            ≤ ConvexSpaceBody.nonempty_factorization.C 3 (fibre u pρ m).card δt
              * ∑ i ∈ um m, volume ((T i).toShadedBody).shade) →
        (∑ m ∈ tρ, ∑ i ∈ um m, volume ((T i).toShadedBody).shade
            ≤ ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) ^ 2
              * ∑ m ∈ tρ', ∑ i ∈ um m, volume ((T i).toShadedBody).shade) →
        ShadedBody.IsCRefinement (tρ'.biUnion um) (fun i => (T i).toShadedBody) u
          (fun i => (T i).toShadedBody) ⟨(δt : ℝ) ^ ε'', by positivity⟩ := by
  filter_upwards [self_mem_nhdsWithin, eventually_plankPigeonhole_loss_le hε'' cardBound.one_le_C]
    with δt hδt hloss
  intro ρ hδρ hρ1 ι κ _ _ u tρ tρ' T pρ um hune hball hED hpρ htρ' hum hper hcross
  have hs' : tρ'.biUnion um ⊆ u :=
    Finset.biUnion_subset.mpr (fun m hm => by
      intro i hi
      have hfib : i ∈ fibre u pρ m := hum m (htρ' hm) hi
      rw [fibre] at hfib
      exact (Finset.mem_filter.mp hfib).1)
  exact isCRefinement_of_sum_le_rpow hδt hε'' T hs'
    (sum_le_rpow_neg_of_plankLosses hdim hδt (hδρ.trans hρ1) (hloss ρ hδρ hρ1)
      T pρ um hune hball hED hpρ htρ' hum hper hcross)

/-- The empty factorization.  `ConvexSpaceBody.Factorization` extends `Finpartition`, and
`Finpartition.empty` partitions `⊥ = (∅ : Finset ι)` with no parts, so the two quantified fields
`maxDensity_le_mul` and `simDims` are vacuous and `isKatzTao` is `maxDensity ∅ _ ≤ C`.

Stated as an existence statement rather than a `def` so that its `parts` are pinned down by a
theorem.  It is what supplies a factorization over a parent whose fibre has been emptied. -/
theorem exists_emptyFactorization {ι : Type*} [DecidableEq ι]
    (V : ι → ConvexSpaceBody E) (C : NNReal) :
    ∃ F : ConvexSpaceBody.Factorization (∅ : Finset ι) V C, F.parts = ∅ := by
  let P : Finpartition (∅ : Finset ι) := Finpartition.empty (α := Finset ι)
  let F : ConvexSpaceBody.Factorization (∅ : Finset ι) V C :=
    ⟨P, by simp [IsKatzTao, P], by simp [P], by simp [P]⟩
  exact ⟨F, rfl⟩

/-- Transport of a factorization along an equality of the index set, with its parts unchanged.

Needed twice in `Kakeya.ml1Boot.exists_plankDimensions_geom`: the factorizations come indexed by
the blocks `um m`, whereas `Kakeya.ml1Boot.exists_commonPlankDims` and the conclusion of the plank
pigeonhole index them by the fibres `fibre (tρ.biUnion um) pρ m` and
`fibre (tρ'.biUnion um) pρ m`, which are the same `Finset`s but not syntactically. -/
theorem exists_factorizationCopy {ι : Type*} [DecidableEq ι] {V : ι → ConvexSpaceBody E}
    {C : NNReal} {s s' : Finset ι} (F : ConvexSpaceBody.Factorization s V C) (h : s = s') :
    ∃ F' : ConvexSpaceBody.Factorization s' V C, F'.parts = F.parts := by
  subst h
  exact ⟨F, rfl⟩

omit [BorelSpace E] in
/-- The three thickness ranges over a single part of a single parent (blueprint
`lem:ml1bootPlankEthicknessRanges`, specialised to a part of the factorization of a fibre).

`Kakeya.ml1Boot.ethickness_bounds_convexHull_tubes` applied to the tubes indexed by `part`, whose
containment in the parent tube `Tρ m` is `Kakeya.ml1Boot.IsParentFamily.le_parent` read at the
fixed parent `m`, using that `pρ i = m` for every `i` in a fibre over `m`. -/
private lemma perParent_ethickness_ranges (hdim : Module.finrank ℝ E = 3)
    {δt ρ : NNReal} (hδt : 0 < δt) (hδρ : δt ≤ ρ) (hρ1 : ρ ≤ 1)
    {ι κ : Type*} [DecidableEq κ] {u : Finset ι} {tρ : Finset κ}
    (T : ι → ShadedTube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamily u (fun i => (T i).toTube) tρ Tρ pρ)
    {m : κ} {part : Finset ι} (hpart : part ⊆ fibre u pρ m) (hne : part.Nonempty) :
    Metric.ethickness ℝ
          (part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier 0
        ∈ Set.Icc (2⁻¹ : ENNReal) 1 ∧
      Metric.ethickness ℝ
            (part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier 1
          ∈ Set.Icc (δt : ENNReal) (ρ : ENNReal) ∧
        Metric.ethickness ℝ
              (part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier 2
            ∈ Set.Icc (δt : ENNReal) (ρ : ENNReal) := by
  classical
  exact ethickness_bounds_convexHull_tubes hdim hδt hδρ hρ1 hne
      (fun i => (T i).toTube) (Tρ m) (by
        intro i hi
        exact hball i ((Finset.mem_filter.mp (hpart hi)).1)) (by
        intro i hi
        have hpm : pρ i = m := (Finset.mem_filter.mp (hpart hi)).2
        have hle : (T i).toTube.toConvexSpaceBody ≤ (Tρ (pρ i)).toConvexSpaceBody :=
          hparent.le_parent i ((Finset.mem_filter.mp (hpart hi)).1)
        rw [hpm] at hle
        exact SetLike.coe_subset_coe.mpr hle)

omit [BorelSpace E] in
/-- The three thickness ranges over a single part of a single *dilate* parent (blueprint
`lem:ml1bootPlankEthicknessRanges`, specialised to a part of the factorization of a fibre and
read at a dilated parent).

`Kakeya.ml1Boot.ethickness_bounds_convexHull_tubes_dilate` applied to the tubes indexed by
`part`, whose containment in the `c`-dilate of the parent tube `Tρ m` is
`Kakeya.ml1Boot.IsParentFamilyDilate.le_parent_dilate` read at the fixed parent `m`, using that
`pρ i = m` for every `i` in a fibre over `m`.

This is `Kakeya.ml1Boot.perParent_ethickness_ranges` with the parent hypothesis weakened from
`Kakeya.ml1Boot.IsParentFamily` to `Kakeya.ml1Boot.IsParentFamilyDilate c`.  The parent is read
in exactly one place — the containment clause — so that single `le_parent` becomes
`le_parent_dilate` and the two transverse brackets widen from `ρ` to `c ρ`.  The index-`0`
bracket `[1/2, 1]` is unchanged, because it comes from `hball` and not from the parent.

At `c = 1` this is `Kakeya.ml1Boot.perParent_ethickness_ranges` verbatim. -/
private lemma perParent_ethickness_ranges_dilate [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ρ : NNReal} (hδt : 0 < δt) (hδρ : δt ≤ ρ) {c : ℝ} (hc : 0 < c)
    {ι κ : Type*} [DecidableEq κ] {u : Finset ι} {tρ : Finset κ}
    (T : ι → ShadedTube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamilyDilate c u (fun i => (T i).toTube) tρ Tρ pρ)
    {m : κ} {part : Finset ι} (hpart : part ⊆ fibre u pρ m) (hne : part.Nonempty) :
    Metric.ethickness ℝ
          (part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier 0
        ∈ Set.Icc (2⁻¹ : ENNReal) 1 ∧
      Metric.ethickness ℝ
            (part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier 1
          ∈ Set.Icc (δt : ENNReal) (ENNReal.ofReal c * (ρ : ENNReal)) ∧
        Metric.ethickness ℝ
              (part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier 2
            ∈ Set.Icc (δt : ENNReal) (ENNReal.ofReal c * (ρ : ENNReal)) := by
  classical
  exact ethickness_bounds_convexHull_tubes_dilate hdim hδt hδρ hc hne
      (fun i => (T i).toTube) (Tρ m) (by
        intro i hi
        exact hball i ((Finset.mem_filter.mp (hpart hi)).1)) (by
        intro i hi
        have hpm : pρ i = m := (Finset.mem_filter.mp (hpart hi)).2
        have hle : (T i).toTube.toConvexSpaceBody ≤ Tube.dilate (Tρ (pρ i)) c :=
          hparent.le_parent_dilate i ((Finset.mem_filter.mp (hpart hi)).1)
        rw [hpm] at hle
        exact SetLike.coe_subset_coe.mpr hle)

/-- The weighted maximal-density factorization of the fibre over a single parent: the application
of `ConvexSpaceBody.nonempty_factorization.factorization_weighted` with the shading masses
`|Ỹ i|` as the weight, which is what makes the retained block heavy in shading rather than merely
in body volume.

Its `δ̃ ≤ ethickness.scale` hypothesis is `Tube.le_ethickness_scale`, and its unit-ball hypothesis
is `hball` restricted along `fibre u pρ m ⊆ u`. -/
private lemma exists_fibreFactorization (hdim : Module.finrank ℝ E = 3) {δt : NNReal}
    (hδt : 0 < δt) {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u : Finset ι}
    (T : ι → ShadedTube δt E) (pρ : ι → κ)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1)
    {m : κ} (hne : (fibre u pρ m).Nonempty) :
    ∃ s' ⊆ fibre u pρ m, s'.Nonempty ∧
      ∑ i ∈ fibre u pρ m, volume ((T i).toShadedBody).shade
          ≤ ConvexSpaceBody.nonempty_factorization.C 3 (fibre u pρ m).card δt
            * ∑ i ∈ s', volume ((T i).toShadedBody).shade ∧
        ∃ F : ConvexSpaceBody.Factorization s' (fun i => (T i).toConvexSpaceBody) 2,
          F.parts.Nonempty := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  let s : Finset ι := fibre u pρ m
  let V : ι → ConvexSpaceBody E := fun i => (T i).toConvexSpaceBody
  let w : ι → ENNReal := fun i => volume ((T i).toShadedBody).shade
  have hs1 : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi
    have hif : i ∈ fibre u pρ m := by simpa [s] using hi
    rw [fibre] at hif
    have hiu : i ∈ u := (Finset.mem_filter.mp hif).1
    simpa [V] using hball i hiu
  have hs2 : ∀ i ∈ s, δt ≤ Metric.ethickness.scale ℝ (V i).carrier := by
    intro i hi
    simpa [V] using Tube.le_ethickness_scale (T i).toTube
  rcases ConvexSpaceBody.nonempty_factorization.factorization_weighted
      (s := s) (V := V) (δ := δt) (w := w) hδt hne hs1 hs2 with
    ⟨s', hsub, hne', hsum, F, hFne⟩
  refine ⟨s', hsub, hne', ?_, F, hFne⟩
  rw [hdim] at hsum
  simpa [s, V, w] using hsum

/-- **(blueprint `lem:ml1bootPlankPigeonholePerParent`) The factorization over a single parent,
with the three thickness ranges**, gathered over all parents at once.

The proof applies the *weighted* factorization lemma
`ConvexSpaceBody.nonempty_factorization.factorization_weighted` to the fibre over each parent, with
the weight `w i = |Ỹ i|`; this is `Kakeya.ml1Boot.exists_fibreFactorization`.  It is essential that
the weighted form is cited and not
`ConvexSpaceBody.nonempty_factorization.weight_subfamily`, whose heavy-subfamily bound is on the
*body* volumes `volume (V i).carrier`: for a family of `δ̃`-tubes those volumes are all equal, so
that bound degenerates to a statement about cardinality and says nothing about where the shading
sits, hence cannot produce the shading-mass loss required below.  The three thickness ranges over a
part are `Kakeya.ml1Boot.perParent_ethickness_ranges`, and everything else here is the gathering of
the per-parent statements into total functions.

Two differences from the blueprint statement, both bookkeeping.  First, the blueprint fixes one
parent `m ∈ t_ρ` and returns a nonempty `u_m` with a factorization of it; here the conclusion is
gathered into total functions `um : κ → Finset ι` and
`F : (m : κ) → ConvexSpaceBody.Factorization (um m) _ 2`, because
`Kakeya.ml1Boot.exists_commonPlankDims` consumes a factorization for *every* `m : κ` and gathering
the per-parent statements would need choice at the type level.  Off `t_ρ` nothing is asserted, so
`um m = ∅` with the empty factorization there.  Second, nonemptiness of `u_m` is recorded in the
form actually used, namely `(F m).parts.Nonempty`, which is what supplies the representative part
of `Kakeya.ml1Boot.exists_commonPlankDims`. -/
theorem exists_perParentFactorization (hdim : Module.finrank ℝ E = 3)
    {δt ρ : NNReal} (hδt : 0 < δt) (_hδt2 : δt ≤ 2⁻¹) (hδρ : δt ≤ ρ) (hρ1 : ρ ≤ 1)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u : Finset ι} {tρ : Finset κ}
    (T : ι → ShadedTube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamily u (fun i => (T i).toTube) tρ Tρ pρ)
    (hsurj : Set.SurjOn pρ u tρ) :
    ∃ um : κ → Finset ι, (∀ m ∈ tρ, um m ⊆ fibre u pρ m) ∧
      ∃ F : (m : κ) → ConvexSpaceBody.Factorization (um m)
          (fun i => (T i).toConvexSpaceBody) 2,
        (∀ m ∈ tρ, (F m).parts.Nonempty) ∧
          (∀ m ∈ tρ, ∑ i ∈ fibre u pρ m, volume ((T i).toShadedBody).shade
              ≤ ConvexSpaceBody.nonempty_factorization.C 3 (fibre u pρ m).card δt
                * ∑ i ∈ um m, volume ((T i).toShadedBody).shade) ∧
            ∀ m ∈ tρ, ∀ part ∈ (F m).parts,
              Metric.ethickness ℝ (part.convexHull_biUnion
                    (fun i => (T i).toConvexSpaceBody)).carrier 0
                  ∈ Set.Icc (2⁻¹ : ENNReal) 1 ∧
                Metric.ethickness ℝ (part.convexHull_biUnion
                      (fun i => (T i).toConvexSpaceBody)).carrier 1
                    ∈ Set.Icc (δt : ENNReal) (ρ : ENNReal) ∧
                  Metric.ethickness ℝ (part.convexHull_biUnion
                        (fun i => (T i).toConvexSpaceBody)).carrier 2
                      ∈ Set.Icc (δt : ENNReal) (ρ : ENNReal) := by
  classical
  have hfib : ∀ m ∈ tρ, (fibre u pρ m).Nonempty := by
    intro m hm
    obtain ⟨i, hiu, hpi⟩ := hsurj hm
    exact ⟨i, by rw [fibre]; exact Finset.mem_filter.mpr ⟨hiu, hpi⟩⟩
  have key : ∀ m ∈ tρ,
      ∃ s' ⊆ fibre u pρ m, s'.Nonempty ∧
        (∑ i ∈ fibre u pρ m, volume ((T i).toShadedBody).shade
          ≤ ConvexSpaceBody.nonempty_factorization.C 3 (fibre u pρ m).card δt
            * ∑ i ∈ s', volume ((T i).toShadedBody).shade) ∧
          ∃ F : ConvexSpaceBody.Factorization s' (fun i => (T i).toConvexSpaceBody) 2,
            F.parts.Nonempty :=
    fun m hm => exists_fibreFactorization hdim hδt T pρ hball (hfib m hm)
  obtain ⟨E0, _hE0⟩ := exists_emptyFactorization
    (V := fun i => (T i).toConvexSpaceBody) 2
  let um : κ → Finset ι := fun m => if h : m ∈ tρ then (key m h).choose else ∅
  let F : (m : κ) → ConvexSpaceBody.Factorization (um m) (fun i => (T i).toConvexSpaceBody) 2 :=
    fun m => if h : m ∈ tρ then
        (exists_factorizationCopy ((key m h).choose_spec.2.2.2).choose (by simp [um, h])).choose
      else (exists_factorizationCopy E0 (by simp [um, h])).choose
  have hum : ∀ m ∈ tρ, um m ⊆ fibre u pρ m := by
    intro m hm
    dsimp [um]
    rw [dif_pos hm]
    exact (key m hm).choose_spec.1
  have hon : ∀ m : κ, ∀ h : m ∈ tρ, (F m).parts = (((key m h).choose_spec.2.2.2).choose).parts := by
    intro m hm
    dsimp [F]
    rw [dif_pos hm]
    exact (exists_factorizationCopy ((key m hm).choose_spec.2.2.2).choose
      (by simp [um, hm])).choose_spec
  have hFne : ∀ m ∈ tρ, (F m).parts.Nonempty := by
    intro m hm
    rw [hon m hm]
    exact ((key m hm).choose_spec.2.2.2).choose_spec
  have hsum : ∀ m ∈ tρ,
      (∑ i ∈ fibre u pρ m, volume ((T i).toShadedBody).shade
        ≤ ConvexSpaceBody.nonempty_factorization.C 3 (fibre u pρ m).card δt
          * ∑ i ∈ um m, volume ((T i).toShadedBody).shade) := by
    intro m hm
    dsimp [um]
    rw [dif_pos hm]
    exact (key m hm).choose_spec.2.2.1
  have hper : ∀ m ∈ tρ, ∀ part ∈ (F m).parts,
      Metric.ethickness ℝ (part.convexHull_biUnion
            (fun i => (T i).toConvexSpaceBody)).carrier 0
          ∈ Set.Icc (2⁻¹ : ENNReal) 1 ∧
        Metric.ethickness ℝ (part.convexHull_biUnion
              (fun i => (T i).toConvexSpaceBody)).carrier 1
            ∈ Set.Icc (δt : ENNReal) (ρ : ENNReal) ∧
          Metric.ethickness ℝ (part.convexHull_biUnion
                (fun i => (T i).toConvexSpaceBody)).carrier 2
              ∈ Set.Icc (δt : ENNReal) (ρ : ENNReal) := by
    intro m hm part hpart
    have partNe : part.Nonempty := (F m).nonempty_of_mem_parts hpart
    have partSub : part ⊆ um m := (F m).toFinpartition.subset hpart
    have hmsub : part ⊆ fibre u pρ m := by
      intro i hi
      exact hum m hm (partSub hi)
    exact perParent_ethickness_ranges hdim hδt hδρ hρ1 T Tρ pρ hball hparent hmsub partNe
  exact ⟨um, hum, F, hFne, hsum, hper⟩

/-- **(blueprint `lem:ml1bootPlankPigeonholePerParent`, read at a dilated parent) The
factorization over a single *dilate* parent, with the three thickness ranges.**

This is `Kakeya.ml1Boot.exists_perParentFactorization` with the parent hypothesis weakened from
`Kakeya.ml1Boot.IsParentFamily` to `Kakeya.ml1Boot.IsParentFamilyDilate c`, which is what a
parent family merged by `Kakeya.ml1Boot.exists_merged_rhoParentFamily` supplies.

Nothing in the selection changes.  The parent is read in exactly two places: `.mapsTo`, which
`Kakeya.ml1Boot.IsParentFamilyDilate` carries verbatim, and the containment clause inside
`Kakeya.ml1Boot.perParent_ethickness_ranges`, which becomes
`Kakeya.ml1Boot.perParent_ethickness_ranges_dilate`.  The whole weighted factorization stage —
`Kakeya.ml1Boot.exists_fibreFactorization` and the gathering into total functions — never sees
the parent tubes at all, only the fibres of `pρ`, so it is reused unchanged.

## The transverse brackets are stated at the scale `c ρ`, as an `ℝ≥0`

`Kakeya.ml1Boot.perParent_ethickness_ranges_dilate` delivers the two transverse brackets with
upper endpoint `ENNReal.ofReal c * ρ`.  Since `ENNReal.ofReal c = ↑c.toNNReal`, that product is
literally `↑(c.toNNReal * ρ)`, the coercion of a single `ℝ≥0`.  Stating the conclusion in that
form is not cosmetic: it makes the output *syntactically* the bracket shape of
`Kakeya.ml1Boot.exists_perParentFactorization` read at the scale `ρ' = c.toNNReal * ρ`, so that
`Kakeya.ml1Boot.exists_plankDimensions_geom` — and through it
`Kakeya.ml1Boot.exists_commonPlankDims`, whose three range hypotheses these are — applies at
`ρ'` with no edit whatever.  That is the whole reason the dilated pigeonhole needs no dilated
cross-`m` step.

Both endpoints of each widened bracket carry a single power of `ρ`, so `c` sits on the ratio.
The index-`0` bracket `[1/2, 1]` does not move, because it comes from `hball` and not from the
parent.  At `c = 1` we have `c.toNNReal * ρ = ρ` and this is
`Kakeya.ml1Boot.exists_perParentFactorization` verbatim.

`hρ1 : ρ ≤ 1` is *not* a hypothesis here, unlike in the undilated form: the only consumer of it
there was the `τ₀` bracket of `Kakeya.ml1Boot.ethickness_bounds_convexHull_tubes`, and the
dilated route reaches that bracket through `hball` instead.  `0 < c` is not a hypothesis either;
it is `Kakeya.ml1Boot.IsParentFamilyDilate.one_le`. -/
theorem exists_perParentFactorization_dilate [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ρ : NNReal} (hδt : 0 < δt) (_hδt2 : δt ≤ 2⁻¹) (hδρ : δt ≤ ρ) {c : ℝ}
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u : Finset ι} {tρ : Finset κ}
    (T : ι → ShadedTube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamilyDilate c u (fun i => (T i).toTube) tρ Tρ pρ)
    (hsurj : Set.SurjOn pρ u tρ) :
    ∃ um : κ → Finset ι, (∀ m ∈ tρ, um m ⊆ fibre u pρ m) ∧
      ∃ F : (m : κ) → ConvexSpaceBody.Factorization (um m)
          (fun i => (T i).toConvexSpaceBody) 2,
        (∀ m ∈ tρ, (F m).parts.Nonempty) ∧
          (∀ m ∈ tρ, ∑ i ∈ fibre u pρ m, volume ((T i).toShadedBody).shade
              ≤ ConvexSpaceBody.nonempty_factorization.C 3 (fibre u pρ m).card δt
                * ∑ i ∈ um m, volume ((T i).toShadedBody).shade) ∧
            ∀ m ∈ tρ, ∀ part ∈ (F m).parts,
              Metric.ethickness ℝ (part.convexHull_biUnion
                    (fun i => (T i).toConvexSpaceBody)).carrier 0
                  ∈ Set.Icc (2⁻¹ : ENNReal) 1 ∧
                Metric.ethickness ℝ (part.convexHull_biUnion
                      (fun i => (T i).toConvexSpaceBody)).carrier 1
                    ∈ Set.Icc (δt : ENNReal) ((c.toNNReal * ρ : NNReal) : ENNReal) ∧
                  Metric.ethickness ℝ (part.convexHull_biUnion
                        (fun i => (T i).toConvexSpaceBody)).carrier 2
                      ∈ Set.Icc (δt : ENNReal) ((c.toNNReal * ρ : NNReal) : ENNReal) := by
  classical
  have hfib : ∀ m ∈ tρ, (fibre u pρ m).Nonempty := by
    intro m hm
    obtain ⟨i, hiu, hpi⟩ := hsurj hm
    exact ⟨i, by rw [fibre]; exact Finset.mem_filter.mpr ⟨hiu, hpi⟩⟩
  have key : ∀ m ∈ tρ,
      ∃ s' ⊆ fibre u pρ m, s'.Nonempty ∧
        (∑ i ∈ fibre u pρ m, volume ((T i).toShadedBody).shade
          ≤ ConvexSpaceBody.nonempty_factorization.C 3 (fibre u pρ m).card δt
            * ∑ i ∈ s', volume ((T i).toShadedBody).shade) ∧
          ∃ F : ConvexSpaceBody.Factorization s' (fun i => (T i).toConvexSpaceBody) 2,
            F.parts.Nonempty :=
    fun m hm => exists_fibreFactorization hdim hδt T pρ hball (hfib m hm)
  obtain ⟨E0, _hE0⟩ := exists_emptyFactorization
    (V := fun i => (T i).toConvexSpaceBody) 2
  let um : κ → Finset ι := fun m => if h : m ∈ tρ then (key m h).choose else ∅
  let F : (m : κ) → ConvexSpaceBody.Factorization (um m) (fun i => (T i).toConvexSpaceBody) 2 :=
    fun m => if h : m ∈ tρ then
        (exists_factorizationCopy ((key m h).choose_spec.2.2.2).choose (by simp [um, h])).choose
      else (exists_factorizationCopy E0 (by simp [um, h])).choose
  have hum : ∀ m ∈ tρ, um m ⊆ fibre u pρ m := by
    intro m hm
    dsimp [um]
    rw [dif_pos hm]
    exact (key m hm).choose_spec.1
  have hon : ∀ m : κ, ∀ h : m ∈ tρ, (F m).parts = (((key m h).choose_spec.2.2.2).choose).parts := by
    intro m hm
    dsimp [F]
    rw [dif_pos hm]
    exact (exists_factorizationCopy ((key m hm).choose_spec.2.2.2).choose
      (by simp [um, hm])).choose_spec
  have hFne : ∀ m ∈ tρ, (F m).parts.Nonempty := by
    intro m hm
    rw [hon m hm]
    exact ((key m hm).choose_spec.2.2.2).choose_spec
  have hsum : ∀ m ∈ tρ,
      (∑ i ∈ fibre u pρ m, volume ((T i).toShadedBody).shade
        ≤ ConvexSpaceBody.nonempty_factorization.C 3 (fibre u pρ m).card δt
          * ∑ i ∈ um m, volume ((T i).toShadedBody).shade) := by
    intro m hm
    dsimp [um]
    rw [dif_pos hm]
    exact (key m hm).choose_spec.2.2.1
  have hper : ∀ m ∈ tρ, ∀ part ∈ (F m).parts,
      Metric.ethickness ℝ (part.convexHull_biUnion
            (fun i => (T i).toConvexSpaceBody)).carrier 0
          ∈ Set.Icc (2⁻¹ : ENNReal) 1 ∧
        Metric.ethickness ℝ (part.convexHull_biUnion
              (fun i => (T i).toConvexSpaceBody)).carrier 1
            ∈ Set.Icc (δt : ENNReal) ((c.toNNReal * ρ : NNReal) : ENNReal) ∧
          Metric.ethickness ℝ (part.convexHull_biUnion
                (fun i => (T i).toConvexSpaceBody)).carrier 2
              ∈ Set.Icc (δt : ENNReal) ((c.toNNReal * ρ : NNReal) : ENNReal) := by
    intro m hm part hpart
    have partNe : part.Nonempty := (F m).nonempty_of_mem_parts hpart
    have partSub : part ⊆ um m := (F m).toFinpartition.subset hpart
    have hmsub : part ⊆ fibre u pρ m := by
      intro i hi
      exact hum m hm (partSub hi)
    have hc : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hparent.one_le
    have hcoe : ENNReal.ofReal c * (ρ : ENNReal) = ((c.toNNReal * ρ : NNReal) : ENNReal) := by
      rw [ENNReal.coe_mul]
      rfl
    rw [← hcoe]
    exact perParent_ethickness_ranges_dilate hdim hδt hδρ hc T Tρ pρ hball hparent hmsub partNe
  exact ⟨um, hum, F, hFne, hsum, hper⟩

/-- The companion of `Kakeya.ml1Boot.fibre_biUnion_eq` outside the parent set: a glued index set
has an empty fibre over any `m` which is not a parent at all, because each block lies in a fibre
over a genuine parent. -/
theorem fibre_biUnion_eq_empty_of_notMem {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {u : Finset ι} {tρ tρ' : Finset κ} (htρ' : tρ' ⊆ tρ) (pρ : ι → κ) (um : κ → Finset ι)
    (hum : ∀ m ∈ tρ, um m ⊆ fibre u pρ m) {m : κ} (hm : m ∉ tρ) :
    fibre (tρ'.biUnion um) pρ m = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i hi
  rw [fibre] at hi
  rw [Finset.mem_filter] at hi
  rcases hi with ⟨hbi, hpi⟩
  rw [Finset.mem_biUnion] at hbi
  rcases hbi with ⟨m', hm', him'⟩
  have hfib' : i ∈ u.filter (fun p => pρ p = m') := hum m' (htρ' hm') him'
  have hpm' : pρ i = m' := (Finset.mem_filter.mp hfib').2
  have hm'eq : m' = m := hpm'.symm.trans hpi
  exact hm (by simpa [hm'eq] using htρ' hm')

/-- **The geometric half of the plank pigeonhole**: items (iii) and the cross-parent weight loss,
with no filter and no shading hypotheses.

Given per-parent blocks `um m` and factorizations `F m` whose planks have the three thickness
ranges, `Kakeya.ml1Boot.exists_commonPlankDims` at `C := Kakeya.ml1Boot.plankPigeonhole.C` (legal
since that constant is at least `1024 ≥ 8`) retains `tρ' ⊆ tρ` carrying all but a
`(1 + log₂ (ρ / δ̃))²` fraction of the weight `w m = ∑ i ∈ um m, |Ỹ i|` and produces a single pair
`(ap, bp)` describing every plank over every surviving parent.  The factorizations are then
re-indexed by the fibres of the glued set `tρ'.biUnion um`
(`Kakeya.ml1Boot.fibre_biUnion_eq`, `Kakeya.ml1Boot.fibre_biUnion_eq_empty_of_notMem` and
`Kakeya.ml1Boot.exists_factorizationCopy`), the discarded parents receiving the empty
factorization, over which item (iii) is vacuous.

`t_ρ.Nonempty → t_ρ'.Nonempty` transports verbatim from
`Kakeya.ml1Boot.exists_commonPlankDims`; it is what
`Kakeya.ml1Boot.exists_plankDimensions` turns into nonemptiness of its subfamily. -/
theorem exists_plankDimensions_geom {δt ρ : NNReal} (hδt : 0 < δt) (hδρ : δt ≤ ρ)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u : Finset ι} {tρ : Finset κ}
    (T : ι → ShadedTube δt E) (pρ : ι → κ) (um : κ → Finset ι)
    (hum : ∀ m ∈ tρ, um m ⊆ fibre u pρ m)
    (F : (m : κ) → ConvexSpaceBody.Factorization (um m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hFne : ∀ m ∈ tρ, (F m).parts.Nonempty)
    (hranges : ∀ m ∈ tρ, ∀ part ∈ (F m).parts,
      Metric.ethickness ℝ (part.convexHull_biUnion
            (fun i => (T i).toConvexSpaceBody)).carrier 0
          ∈ Set.Icc (2⁻¹ : ENNReal) 1 ∧
        Metric.ethickness ℝ (part.convexHull_biUnion
              (fun i => (T i).toConvexSpaceBody)).carrier 1
            ∈ Set.Icc (δt : ENNReal) (ρ : ENNReal) ∧
          Metric.ethickness ℝ (part.convexHull_biUnion
                (fun i => (T i).toConvexSpaceBody)).carrier 2
              ∈ Set.Icc (δt : ENNReal) (ρ : ENNReal)) :
    ∃ tρ' ⊆ tρ, (tρ.Nonempty → tρ'.Nonempty) ∧ ∃ ap bp : NNReal, δt ≤ ap ∧ ap ≤ bp ∧ bp ≤ ρ ∧
      (∑ m ∈ tρ, ∑ i ∈ um m, volume ((T i).toShadedBody).shade
          ≤ ENNReal.ofReal (1 + Real.logb 2 ((ρ : ℝ) / (δt : ℝ))) ^ 2
            * ∑ m ∈ tρ', ∑ i ∈ um m, volume ((T i).toShadedBody).shade) ∧
        ∃ F' : (m : κ) → ConvexSpaceBody.Factorization (fibre (tρ'.biUnion um) pρ m)
            (fun i => (T i).toConvexSpaceBody) 2,
          (∀ m ∈ tρ, ∀ part ∈ (F' m).parts, part.Nonempty) ∧
            ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F' m).parts
              (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)) := by
  classical
  let V : ι → ConvexSpaceBody E := fun i => (T i).toConvexSpaceBody
  let w : κ → ENNReal := fun m => ∑ i ∈ um m, volume ((T i).toShadedBody).shade
  have hC : 8 ≤ plankPigeonhole.C := by
    have hVge : (1 : NNReal) ≤ Metric.volume_comparison.C 3 := by
      dsimp [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
      norm_num
    dsimp [plankPigeonhole.C]
    exact le_trans (by norm_num : (8 : NNReal) ≤ 16)
      (le_mul_of_one_le_right (by norm_num : (0 : NNReal) ≤ 16) hVge)
  have heq0 : ∀ m ∈ tρ, fibre (tρ.biUnion um) pρ m = um m :=
    (fibre_biUnion_eq (Finset.Subset.refl tρ) pρ um hum).1
  have hemp : ∀ m : κ, m ∉ tρ → fibre (tρ.biUnion um) pρ m = ∅ := fun m hm =>
    fibre_biUnion_eq_empty_of_notMem (Finset.Subset.refl tρ) pρ um hum hm
  obtain ⟨E0, hE0⟩ := exists_emptyFactorization (V := V) 2
  let F0 : (m : κ) → ConvexSpaceBody.Factorization (fibre (tρ.biUnion um) pρ m) V 2 :=
    fun m => if h : m ∈ tρ then
        (exists_factorizationCopy (F m) (heq0 m h).symm).choose
      else
        (exists_factorizationCopy E0 (hemp m h).symm).choose
  have hp0 : ∀ m : κ, m ∈ tρ → (F0 m).parts = (F m).parts := by
    intro m h
    dsimp [F0]
    rw [dif_pos h]
    exact (exists_factorizationCopy (F m) (heq0 m h).symm).choose_spec
  have hp0' : ∀ m : κ, m ∉ tρ → (F0 m).parts = ∅ := by
    intro m h
    dsimp [F0]
    rw [dif_neg h]
    exact ((exists_factorizationCopy E0 (hemp m h).symm).choose_spec).trans hE0
  let rep : κ → Finset ι := fun m => if h : m ∈ tρ then (hFne m h).choose else ∅
  have hrep : ∀ m : κ, m ∈ tρ → rep m ∈ (F0 m).parts := by
    intro m h
    dsimp [rep]
    rw [dif_pos h]
    rw [hp0 m h]
    exact (hFne m h).choose_spec
  have hτ0 : ∀ m : κ, m ∈ tρ → ∀ part ∈ (F0 m).parts,
      Metric.ethickness ℝ (part.convexHull_biUnion V).carrier 0 ∈ Set.Icc (2⁻¹ : ENNReal) 1 := by
    intro m hm part hpart
    rw [hp0 m hm] at hpart
    exact (hranges m hm part hpart).1
  have hτ1 : ∀ m : κ, m ∈ tρ → ∀ part ∈ (F0 m).parts,
    Metric.ethickness ℝ (part.convexHull_biUnion V).carrier 1 ∈ Set.Icc (δt : ENNReal) (ρ : ENNReal) := by
    intro m hm part hpart
    rw [hp0 m hm] at hpart
    exact (hranges m hm part hpart).2.1
  have hτ2 : ∀ m : κ, m ∈ tρ → ∀ part ∈ (F0 m).parts,
    Metric.ethickness ℝ (part.convexHull_biUnion V).carrier 2 ∈ Set.Icc (δt : ENNReal) (ρ : ENNReal) := by
    intro m hm part hpart
    rw [hp0 m hm] at hpart
    exact (hranges m hm part hpart).2.2
  obtain ⟨tρ', hsub, hne, ap, bp, hδap, hapb, hbpρ, hwt, hplank⟩ :=
    exists_commonPlankDims (C := plankPigeonhole.C) hC hδt hδρ (V := V) pρ (w := w) F0 rep hrep hτ0 hτ1 hτ2
  have hFib1 : ∀ m ∈ tρ', fibre (tρ'.biUnion um) pρ m = um m :=
    (fibre_biUnion_eq hsub pρ um hum).1
  have hMid : ∀ m : κ, m ∈ tρ → m ∉ tρ' → fibre (tρ'.biUnion um) pρ m = ∅ :=
    (fibre_biUnion_eq hsub pρ um hum).2
  have hOff : ∀ m : κ, m ∉ tρ → fibre (tρ'.biUnion um) pρ m = ∅ := fun m hm =>
    fibre_biUnion_eq_empty_of_notMem hsub pρ um hum hm
  let F' : (m : κ) → ConvexSpaceBody.Factorization (fibre (tρ'.biUnion um) pρ m) V 2 :=
    fun m => if h1 : m ∈ tρ' then
        (exists_factorizationCopy (F m) (hFib1 m h1).symm).choose
      else if h2 : m ∈ tρ then
        (exists_factorizationCopy E0 (hMid m h2 h1).symm).choose
      else
        (exists_factorizationCopy E0 (hOff m h2).symm).choose
  have hEq : ∀ m : κ, m ∈ tρ' → (F' m).parts = (F m).parts := by
    intro m h
    dsimp [F']
    rw [dif_pos h]
    exact (exists_factorizationCopy (F m) (hFib1 m h).symm).choose_spec
  have hEmpty : ∀ m : κ, m ∉ tρ' → (F' m).parts = ∅ := by
    intro m hm
    dsimp [F']
    rw [dif_neg hm]
    by_cases hmt : m ∈ tρ
    · rw [dif_pos hmt]
      exact ((exists_factorizationCopy E0 (hMid m hmt hm).symm).choose_spec).trans hE0
    · rw [dif_neg hmt]
      exact ((exists_factorizationCopy E0 (hOff m hmt).symm).choose_spec).trans hE0
  have nonempty : ∀ m : κ, m ∈ tρ → ∀ part ∈ (F' m).parts, part.Nonempty := by
    intro m hm
    by_cases hm' : m ∈ tρ'
    · intro part hpart
      rw [hEq m hm'] at hpart
      exact (F m).nonempty_of_mem_parts hpart
    · intro part hpart
      rw [hEmpty m hm'] at hpart
      simp at hpart
  have hplankF : ∀ m : κ, m ∈ tρ → IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F' m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)) := by
    intro m hm
    by_cases hm' : m ∈ tρ'
    · have hmρ : m ∈ tρ := hsub hm'
      have hmEq : (F' m).parts = (F0 m).parts := (hEq m hm').trans (hp0 m hmρ).symm
      rw [hmEq]
      exact hplank m hm'
    · rw [hEmpty m hm']
      intro part hpart
      simp at hpart
  refine ⟨tρ', hsub, hne, ap, bp, hδap, hapb, hbpρ, by simpa [w] using hwt, F', nonempty, hplankF⟩

/-- **(after GWZ Lemma 4.1, applied at scale `ρ`) Common plank dimensions over all `ρ`-tubes**
(blueprint
`lem:ml1bootPlankPigeonhole`).

Write `C_𝕎 = Kakeya.ml1Boot.plankPigeonhole.C` and let `ε'' > 0`.  For all sufficiently small
`δ̃ > 0`: given `δ̃ ≤ ρ ≤ 1`, a nonempty family `𝕋̃` of pairwise essentially distinct
`δ̃`-tubes in `B₁ ⊆ ℝ³` with a shading, and a parent family `(t_ρ, 𝕋̃_ρ, p_ρ)` at scale `ρ`
with `p_ρ` surjective, there are a subfamily `u''`, widths `δ̃ ≤ a ≤ b ≤ ρ`, and for each
`m ∈ t_ρ` a factorization of the restricted fibre `𝕋̃[T̃_{ρ,m}]|_{u''}` with constant `2`,
such that

* (i) (`item:plankRefine`) `(𝕋̃|_{u''}, Ỹ)` is a `δ̃ ^ ε''`-refinement of `(𝕋̃, Ỹ)`;
* (iii) (`item:plankDims`) every plank over every `ρ`-tube has dimensions comparable to
  `a × b × 1` with the *same* `a` and `b`, with constant `C_𝕎`;
* (iv) (`item:plankVolume`) `C_𝕎⁻¹ a b ≤ |W_{m,t}| ≤ C_𝕎 a b`.

Blueprint item (ii) (`item:plankFactors`), that `𝕎_m` `2`-factors the restricted fibre
`𝕋̃[T̃_{ρ,m}]|_{u''}`, is not a separate clause here: it is carried by the *type* of `F`,
namely `ConvexSpaceBody.Factorization (fibre u'' pρ m) _ 2`.  The remaining clause of the
conclusion, that every part of every factorization is nonempty, is an extra Lean-side
obligation rather than a blueprint item: it is implicit in the blueprint's "a finite
partition `𝒫_m` … into nonempty blocks", but `ConvexSpaceBody.Factorization` does not carry
it, and the planks have to be convex hulls of nonempty blocks for (iii) and (iv) to have
content.

`u''` is nonempty.  This is not an extra assumption anywhere: `u.Nonempty` and
`Kakeya.ml1Boot.IsParentFamily.mapsTo` make `t_ρ` nonempty, the pigeonhole of
`Kakeya.ml1Boot.exists_plankDimensions_geom` keeps a parent (it is run through
`Kakeya.ml1Boot.exists_dyadicClass_nonempty`, which patches the degenerate zero-weight answer of
`ENNReal.dyadic_pigeonhole₁''` to a singleton), and over a surviving parent
`Kakeya.ml1Boot.exists_perParentFactorization` supplies a part, which as a block of a
`Finpartition` of `u_m` is a nonempty subset of `u_m`.

The blueprint's partition `𝒫_m` and plank family `𝕎_m` are the `Finpartition` underlying the
`ConvexSpaceBody.Factorization` and the family `fun part => part.convexHull_biUnion V` that
that structure is about, so they are not separate data here. -/
theorem exists_plankDimensions (hdim : Module.finrank ℝ E = 3) {ε'' : ℝ} (hε'' : 0 < ε'') :
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0, ∀ ρ : NNReal, δt ≤ ρ → ρ ≤ 1 →
      ∀ {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u : Finset ι} {tρ : Finset κ}
        (T : ι → ShadedTube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ),
        u.Nonempty →
        (∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (u : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        IsParentFamily u (fun i => (T i).toTube) tρ Tρ pρ →
        Set.SurjOn pρ u tρ →
        ∃ u'' ⊆ u, u''.Nonempty ∧ ∃ ap bp : NNReal, δt ≤ ap ∧ ap ≤ bp ∧ bp ≤ ρ ∧
          ∃ F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
              (fun i => (T i).toConvexSpaceBody) 2,
            -- (i)
            ShadedBody.IsCRefinement u'' (fun i => (T i).toShadedBody) u
                (fun i => (T i).toShadedBody) ⟨(δt : ℝ) ^ ε'', by positivity⟩ ∧
            -- extra Lean-side obligation; blueprint (ii) `item:plankFactors` is the type of `F`
            (∀ m ∈ tρ, ∀ part ∈ (F m).parts, part.Nonempty) ∧
            -- (iii)
            (∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
              (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody))) ∧
            -- (iv)
            ∀ m ∈ tρ, ∀ part ∈ (F m).parts,
              (plankPigeonhole.C_vol : ENNReal)⁻¹ * (ap : ENNReal) * (bp : ENNReal)
                  ≤ volume (part.convexHull_biUnion
                      (fun i => (T i).toConvexSpaceBody)).carrier ∧
                volume (part.convexHull_biUnion
                    (fun i => (T i).toConvexSpaceBody)).carrier
                  ≤ (plankPigeonhole.C_vol : ENNReal) * (ap : ENNReal) * (bp : ENNReal) := by
  filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : NNReal) < 2⁻¹ by norm_num)),
      isCRefinement_plankPigeonhole hdim hε'']
    with δt hδt hδt2 hrefine
  intro ρ hδρ hρ1 ι κ _ _ u tρ T Tρ pρ hune hball hED hparent hsurj
  obtain ⟨um, hum, F, hFne, hper, hranges⟩ :=
    exists_perParentFactorization hdim hδt hδt2.le hδρ hρ1 T Tρ pρ hball hparent hsurj
  obtain ⟨tρ', htρ', htρ'ne, ap, bp, hδap, hapbp, hbpρ, hcross, F', hFne', hdims⟩ :=
    exists_plankDimensions_geom hδt hδρ T pρ um hum F hFne hranges
  refine ⟨tρ'.biUnion um, ?_, ?_, ap, bp, hδap, hapbp, hbpρ, F', ?_, hFne', hdims, ?_⟩
  · exact Finset.biUnion_subset.mpr (fun m hm => by
      intro i hi
      have hfib : i ∈ fibre u pρ m := hum m (htρ' hm) hi
      rw [fibre] at hfib
      exact (Finset.mem_filter.mp hfib).1)
  · obtain ⟨i₀, hi₀⟩ := hune
    have htρne : tρ.Nonempty := ⟨pρ i₀, hparent.mapsTo i₀ hi₀⟩
    obtain ⟨m₀, hm₀⟩ := htρ'ne htρne
    obtain ⟨part, hpart⟩ := hFne m₀ (htρ' hm₀)
    obtain ⟨i, hi⟩ := (F m₀).nonempty_of_mem_parts hpart
    exact ⟨i, Finset.mem_biUnion.mpr ⟨m₀, hm₀, (F m₀).toFinpartition.subset hpart hi⟩⟩
  · exact hrefine ρ hδρ hρ1 T pρ um hune hball hED hparent.mapsTo htρ' hum hper hcross
  · intro m hm part hpart
    exact volume_bounds_of_isPlankOfDimensions_vol hdim (hdims m hm part hpart)

/-- **(after GWZ Lemma 4.1, applied at a *dilated* parent scale) Common plank dimensions over
all `ρ`-tubes** (blueprint `lem:ml1bootPlankPigeonhole`, read at a dilated parent).

This is `Kakeya.ml1Boot.exists_plankDimensions` with the parent hypothesis weakened from
`Kakeya.ml1Boot.IsParentFamily` to `Kakeya.ml1Boot.IsParentFamilyDilate c`, the hypothesis
`ρ ≤ 1` replaced by `c ρ ≤ 1`, and the conclusion `b ≤ ρ` correspondingly relaxed to
`b ≤ c ρ`.  That is the form the coarse endgame needs: the `ρ`-parents it can obtain pairwise
essentially distinct are the merged ones of
`Kakeya.ml1Boot.exists_merged_rhoParentFamily`, which are parents only up to a dilation, and
`b ≤ c ρ` is exactly the hypothesis `hbρ` of
`Kakeya.ml1Boot.plankTube_subset_parent_dilate_dilate`.

## Why no stage of the pigeonhole has to be redone

Put `ρ' = c.toNNReal * ρ`.  The parent family is read in exactly two places, and every other
stage is scale-generic:

* `Kakeya.ml1Boot.exists_perParentFactorization_dilate` replaces
  `Kakeya.ml1Boot.exists_perParentFactorization`.  Its three thickness ranges come out in the
  brackets `[δ̃, ρ']` — the coercion `↑(c.toNNReal * ρ)` of a single `ℝ≥0`, not a product of
  two `ℝ≥0∞`s — so they are *syntactically* the ranges of the undilated lemma at scale `ρ'`.
* `Kakeya.ml1Boot.exists_plankDimensions_geom` is then applied **verbatim at `ρ'`**.  It never
  mentions a parent family: its inputs are the factorizations, the fibres of `pρ` and those
  three brackets, and its cross-`m` step
  `Kakeya.ml1Boot.exists_commonPlankDims` is likewise stated at a bare scale.  It returns
  `b ≤ ρ'`, which is `b ≤ c ρ`.
* `Kakeya.ml1Boot.isCRefinement_plankPigeonhole` is applied **verbatim at `ρ'`** as well.  It
  takes the parent only through `.mapsTo`, which `Kakeya.ml1Boot.IsParentFamilyDilate` carries
  unchanged, and its cross-fibre loss is the `(1 + log₂ (ρ'/δ̃))²` that
  `Kakeya.ml1Boot.exists_plankDimensions_geom` produced at the same `ρ'`.

The two side conditions are discharged from the two hypotheses and nothing else.  `δ̃ ≤ ρ'`
is `δ̃ ≤ ρ ≤ c ρ`, using `1 ≤ c` from
`Kakeya.ml1Boot.IsParentFamilyDilate.one_le`; and `ρ' ≤ 1` is precisely `c ρ ≤ 1`, which is
why that is the hypothesis carried rather than `ρ ≤ 1`.  Note that `ρ ≤ 1` follows from it, so
this is a genuine strengthening of the hypothesis, paid for by the weakened parent relation.

The refinement constant `δ̃ ^ ε''` of item (i) is unchanged: `ε''` is fixed before `ρ`, and the
`ρ`-dependence of the pigeonhole loss is absorbed for all small `δ̃` by
`Kakeya.ml1Boot.eventually_plankPigeonhole_loss_le`, uniformly over `ρ ≤ 1` — read here at
`ρ' ≤ 1`.  The plank shape and volume constants `Kakeya.ml1Boot.plankPigeonhole.C` and
`Kakeya.ml1Boot.plankPigeonhole.C_vol` do not move either, since `c` enters only the width `b`
and never the comparison between `a`, `b` and the plank.

At `c = 1` the dilate is the identity, `ρ' = ρ`, `b ≤ 1 * ρ` is `b ≤ ρ`, and this is
`Kakeya.ml1Boot.exists_plankDimensions` verbatim. -/
theorem exists_plankDimensions_dilate [Nontrivial E] (hdim : Module.finrank ℝ E = 3) {ε'' : ℝ}
    (hε'' : 0 < ε'') :
    ∀ᶠ (δt : NNReal) in 𝓝[>] 0, ∀ (ρ : NNReal) (c : ℝ), δt ≤ ρ → c * (ρ : ℝ) ≤ 1 →
      ∀ {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u : Finset ι} {tρ : Finset κ}
        (T : ι → ShadedTube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ),
        u.Nonempty →
        (∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (u : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        IsParentFamilyDilate c u (fun i => (T i).toTube) tρ Tρ pρ →
        Set.SurjOn pρ u tρ →
        ∃ u'' ⊆ u, u''.Nonempty ∧ ∃ ap bp : NNReal, δt ≤ ap ∧ ap ≤ bp ∧
          (bp : ℝ) ≤ c * (ρ : ℝ) ∧
          ∃ F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
              (fun i => (T i).toConvexSpaceBody) 2,
            -- (i)
            ShadedBody.IsCRefinement u'' (fun i => (T i).toShadedBody) u
                (fun i => (T i).toShadedBody) ⟨(δt : ℝ) ^ ε'', by positivity⟩ ∧
            -- extra Lean-side obligation; blueprint (ii) `item:plankFactors` is the type of `F`
            (∀ m ∈ tρ, ∀ part ∈ (F m).parts, part.Nonempty) ∧
            -- (iii)
            (∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
              (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody))) ∧
            -- (iv)
            ∀ m ∈ tρ, ∀ part ∈ (F m).parts,
              (plankPigeonhole.C_vol : ENNReal)⁻¹ * (ap : ENNReal) * (bp : ENNReal)
                  ≤ volume (part.convexHull_biUnion
                      (fun i => (T i).toConvexSpaceBody)).carrier ∧
                volume (part.convexHull_biUnion
                    (fun i => (T i).toConvexSpaceBody)).carrier
                  ≤ (plankPigeonhole.C_vol : ENNReal) * (ap : ENNReal) * (bp : ENNReal) := by
  filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : NNReal) < 2⁻¹ by norm_num)),
      isCRefinement_plankPigeonhole hdim hε'']
    with δt hδt hδt2 hrefine
  intro ρ c hδρ hcρ1 ι κ _ _ u tρ T Tρ pρ hune hball hED hparent hsurj
  have hc1 : (1 : ℝ) ≤ c := hparent.one_le
  have hc0 : (0 : ℝ) ≤ c := le_trans zero_le_one hc1
  set ρ' : NNReal := c.toNNReal * ρ
  have hcNN : (1 : NNReal) ≤ c.toNNReal := (Real.one_le_toNNReal).mpr hc1
  have hδρ' : δt ≤ ρ' := by
    dsimp [ρ']
    exact le_trans hδρ (by
      simpa [mul_comm] using
        (le_mul_of_one_le_right (show (0 : NNReal) ≤ ρ from bot_le) hcNN))
  have hρ'1 : ρ' ≤ 1 := by
    dsimp [ρ']
    refine (NNReal.coe_le_coe.mp ?_)
    rw [NNReal.coe_mul]
    rw [Real.coe_toNNReal c hc0]
    exact hcρ1
  obtain ⟨um, hum, F, hFne, hper, hranges⟩ :=
    exists_perParentFactorization_dilate hdim hδt hδt2.le hδρ T Tρ pρ hball hparent hsurj
  obtain ⟨tρ', htρ', htρ'ne, ap, bp, hδap, hapbp, hbpρ', hcross, F', hFne', hdims⟩ :=
    exists_plankDimensions_geom hδt hδρ' T pρ um hum F hFne hranges
  have hbp : (bp : ℝ) ≤ c * (ρ : ℝ) := by
    have h := NNReal.coe_le_coe.mpr hbpρ'
    rw [NNReal.coe_mul] at h
    rw [Real.coe_toNNReal c hc0] at h
    exact h
  refine ⟨tρ'.biUnion um, ?_, ?_, ap, bp, hδap, hapbp, hbp, F', ?_, hFne', hdims, ?_⟩
  · exact Finset.biUnion_subset.mpr (fun m hm => by
      intro i hi
      have hfib : i ∈ fibre u pρ m := hum m (htρ' hm) hi
      rw [fibre] at hfib
      exact (Finset.mem_filter.mp hfib).1)
  · obtain ⟨i₀, hi₀⟩ := hune
    have htρne : tρ.Nonempty := ⟨pρ i₀, hparent.mapsTo i₀ hi₀⟩
    obtain ⟨m₀, hm₀⟩ := htρ'ne htρne
    obtain ⟨part, hpart⟩ := hFne m₀ (htρ' hm₀)
    obtain ⟨i, hi⟩ := (F m₀).nonempty_of_mem_parts hpart
    exact ⟨i, Finset.mem_biUnion.mpr ⟨m₀, hm₀, (F m₀).toFinpartition.subset hpart hi⟩⟩
  · exact hrefine ρ' hδρ' hρ'1 T pρ um hune hball hED hparent.mapsTo htρ' hum hper hcross
  · intro m hm part hpart
    exact volume_bounds_of_isPlankOfDimensions_vol hdim (hdims m hm part hpart)

/-- **Filtering along the assignment deletes only whole classes**: the
`Tube.coverClass` analogue of `Kakeya.ml1Boot.fibre_filter_mem`.

If `u''` is cut out of `u` by the condition that a member's node lie in a set `K` of nodes, then
for every `P ∈ K` the class of `P` in `u''` is the *whole* class of `P` in `u`: the filter removes
exactly the members whose node lies outside `K`, and none of those is assigned to a `P ∈ K`.

This is the device a *whole-class* selection would run on, and it is why such a selection would
repair the two-sided branching brackets for free.  `Tube.coverClass_subset_of_subset`
gives only the upper direction, which is what makes the lower brackets
`Tube.UniformTubeSet.le_card_class` and
`ShadedTube.ShadedUniformTubeSet.le_card_shadeClass` fail on a general subfamily: a class may
keep a single member while the retained mass sits elsewhere.  On a filter along `assign` they
instead hold verbatim, at the same constant and the same `branchingN`, the surviving classes
being literally unchanged.

**It is recorded and not used.**  The selection of `Kakeya.ml1Boot.exists_plankDimensions` is not
of this shape, and could not be made so: its inner stage
`Kakeya.ml1Boot.exists_perParentFactorization` selects *inside* each fibre by shading mass, and
its parent map is built pointwise by `Kakeya.ml1Boot.exists_parentFamily_of_pointwiseTubes` and is
unrelated to `Tube.GridCoverSystem.assign`.  See the blueprint discussion attached to
`lem:ml1bootPlankPigeonhole` for the full verdict. -/
theorem coverClass_filter_mem {ι : Type*} [DecidableEq ι] (u : Finset ι) (assign : ι → ι)
    (K : Finset ι) {P : ι} (hP : P ∈ K) :
    Tube.coverClass (u.filter fun i => assign i ∈ K) assign P
      = Tube.coverClass u assign P := by
  classical
  ext i
  simp only [Tube.coverClass, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hiu, -⟩, hEq⟩
    exact ⟨hiu, hEq⟩
  · rintro ⟨hiu, hEq⟩
    exact ⟨⟨hiu, by rw [hEq]; exact hP⟩, hEq⟩

/-! ### Can the plank conclusion be established at an externally prescribed subfamily?

`Kakeya.ml1Boot.exists_plankDimensions` chooses its own subfamily, and so does the uniformity
producer `ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`.  Composing them raises the
question of whether the plank half can instead be run at an index set chosen elsewhere.  The six
declarations below settle that question on the plank side.  **They are recorded and not used**,
and they change no existing statement.

**(C1) There is no whole-fibre factorization, and there cannot be one at a constant that depends
only on the ambient dimension.**  Every producer of `ConvexSpaceBody.Factorization` in the
repository returns a factorization of a *selected* set:
`ConvexSpaceBody.nonempty_factorization.factorization_weighted` (`Kakeya/Factorization.lean:815`)
and `ConvexSpaceBody.nonempty_factorization.factorization` (`Kakeya/Factorization.lean:535`) both
return an `s' ⊆ s` chosen by two dyadic pigeonholes;
`ConvexSpaceBody.nonempty_biasedFactorization` (`Kakeya/Factorization.lean:1588`) does the same
for `ConvexSpaceBody.BiasedFactorization`;
`ConvexSpaceBody.Factorization.ofSubsetParts` (`Kakeya/Factorization.lean:186`) keeps a
sub-collection of *whole* parts; and
`ConvexSpaceBody.exists_factorization_of_eq_empty` (`Kakeya/Factorization.lean:222`) together with
`Kakeya.ml1Boot.exists_emptyFactorization` covers the empty set.

The nearest thing to a whole-set producer is the private
`ConvexSpaceBody.nonempty_factorization.exists_factorization_of_parts`
(`Kakeya/Factorization.lean:700`), which factorizes `A.sup id` for an *arbitrary* sub-collection
`A` of the blocks of `ConvexSpaceBody.greedy_partition`.  At `A = (greedy_partition s V).parts` its
conclusion is a factorization of the whole of `s`, by `Finpartition.sup_parts`.  What blocks that
instantiation is its two hypotheses, and they are exactly what the two pigeonholes buy:

* `hcomp` (`Kakeya/Factorization.lean:703`), `maxDensity t V ≤ 2 * maxDensity t' V` across
  retained blocks, bought by `ConvexSpaceBody.nonempty_factorization.constructA_weighted`
  (`Kakeya/Factorization.lean:552`) at the weight loss `1 + log₂ |s|`.  Over the whole greedy
  partition it fails: the blocks are extracted in decreasing density and the a priori range of
  that score is `[1, |s|]` (`Kakeya/Factorization.lean:353`-`363`).
* `hsim` (`Kakeya/Factorization.lean:704`), the `simDims` clause, bought by
  `ConvexSpaceBody.nonempty_factorization.constructB_weighted` (`Kakeya/Factorization.lean:584`)
  at the weight loss `(1 + log₂ (1 / δ̃)) ^ dim`.  Over the whole partition it fails for the same
  reason: the a priori range of each ethickness is `[δ̃, 1]`
  (`Kakeya/Factorization.lean:376`-`385`).

So a whole-fibre variant would need `hcomp` at a constant `≥ |s|` and `hsim` at a constant
`≥ 1 / δ̃`.  Both are `δ̃`-dependent and both flow into the factorization constant `C`, hence into
the plank constant, hence into `Kakeya.IsPlankOfDimensions C ap bp` — whose brackets
`[C⁻¹ bp, C bp]` assert nothing once `C ≥ 1 / δ̃`.  A "worse constant" therefore does not buy the
whole fibre, and intra-fibre discarding does not disappear.  Two further facts make the route
unavailable even in the degenerate `δ̃`-dependent form:
`ConvexSpaceBody.nonempty_factorization.exists_factorization_of_parts` is `private`, and
`ConvexSpaceBody.nonempty_factorization.maxDensity_le_mul_of_parts`
(`Kakeya/Factorization.lean:620`) hard-codes the constant `2`.

**(C2) A factorization of `fibre u₁ pρ m` into `ap × bp × 1` planks does not restrict to
`fibre s' pρ m` at the same band, and the constant leaves no slack.**  Of the six brackets of
`Kakeya.IsPlankOfDimensions` (`Kakeya/Factoring/FlatPrisms.lean:79`-`85`) the three *upper* ones
descend to any sub-body, by monotonicity of `Metric.ethickness`; that is
`Kakeya.ml1Boot.ethickness_le_of_subset_of_isPlankOfDimensions` below.  The failure is confined
to the two *lower* brackets `C⁻¹ * b ≤ τ₁` (`Kakeya/Factoring/FlatPrisms.lean:82`) and
`C⁻¹ * a ≤ τ₂` (`Kakeya/Factoring/FlatPrisms.lean:84`), and it is quantitative rather than
qualitative: by `Kakeya.ml1Boot.le_mul_ethickness_of_isPlankOfDimensions` those two brackets pin
the band to the part's own thicknesses, `b ≤ C τ₁` and `a ≤ C τ₂`, so a *common* band forces any
two parts to have thicknesses within a factor `C ^ 2` of one another
(`Kakeya.ml1Boot.ethickness_le_sq_mul_of_isPlankOfDimensions_pair`).  An arbitrary `s'` may meet
one part in a single `δ̃`-tube while leaving another part whole, and then
`Kakeya.ml1Boot.plankBand_le_mul_of_subset_tube` caps the band at `C δ̃` while the untouched part
still needs `bp`, which `Kakeya.ml1Boot.exists_plankDimensions_geom` allows anywhere up to `ρ`.
`Kakeya.ml1Boot.not_exists_commonPlankBand_of_subset_tube` is that contradiction as a theorem:
once `C ^ 2 δ̃ < τ₁` of the untouched part, *no* pair `(a, b)` bands both.  Since
`plankPigeonhole.C` is fixed before `δ̃` and `ρ = δ̃ ^ (6 ε)`, the hypothesis of that theorem is
satisfiable for all small `δ̃`.  So the answer to (C2) is no, with no slack.

Re-grouping does not repair it.  Merging parts thickens the merged hull, which is the direction
the lower bracket wants and the wrong direction for the upper bracket `τ₁ ≤ C b` at the same `b`;
and it changes the `Finpartition`, so the merged blocks are no longer blocks of
`ConvexSpaceBody.greedy_partition` and
`ConvexSpaceBody.nonempty_factorization.exists_factorization_of_parts` no longer applies.
Re-banding, on the other hand, *is* free part by part:
`Kakeya.ml1Boot.exists_isPlankOfDimensions_ownBand` shows every nonempty block of `δ̃`-tubes
inside `B₁ ∩ T_ρ` is a plank at constant `2` for its own band `τ₂ × τ₁ × 1`.  The obstruction is
therefore not plankness but the *common* band, and restoring a common band means a dyadic
pigeonhole over the parts, which discards parts, which discards members of the prescribed
`fibre s' pρ m` — precisely the freedom a caller-prescribed index set withholds.

**(C3) There is no analogue of `Kakeya.ml1Boot.exists_plankFactorization_of_subsetParts`
(`Kakeya/DimensionThree/MainLemma1/Rescaling/KatzTao.lean:1679`) that keeps `t ∩ s'` from each
part `t` and re-bands.**  Two independent fields fail, both on the same configuration as (C2):

* `ConvexSpaceBody.Factorization.simDims` (`Kakeya/Factorization.lean:98`), which asks the parts'
  ethicknesses to be pairwise comparable at the factorization constant `2`.  A part thinned to a
  single `δ̃`-tube has `τ₁ = δ̃` while an untouched part has `τ₁` up to `ρ`, a ratio up to
  `ρ / δ̃ = δ̃ ^ (6 ε - 1)`, unbounded as `δ̃ → 0`.  Re-banding cannot help: `simDims` mentions no
  band.
* `ConvexSpaceBody.Factorization.maxDensity_le_mul` (`Kakeya/Factorization.lean:96`), for the
  reason already recorded at `Kakeya/Factorization.lean:183`-`185`: its right-hand side is
  attached to the part's own hull, which shrinks when members are dropped from inside the part.

`ConvexSpaceBody.Factorization.ofSubsetParts` survives dropping *other* parts precisely because
neither field is disturbed then; intersecting every part with `s'` disturbs both.  So (C3) is no,
and the smallest failing points are `Kakeya/Factorization.lean:98` and
`Kakeya/Factorization.lean:96`, ahead of the plank brackets at
`Kakeya/Factoring/FlatPrisms.lean:82` and `:84`.
-/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The three upper brackets of a plank descend to any sub-body.**

`Kakeya.IsPlankOfDimensions` is two-sided, but only its lower half is sensitive to shrinking:
`Metric.ethickness_monotone` carries each of `τ₀ ≤ C`, `τ₁ ≤ C b`, `τ₂ ≤ C a` from `W` to any
`W'` inside it, with the same `C`, `a`, `b`.  This isolates the failure of restriction to the
lower brackets `Kakeya/Factoring/FlatPrisms.lean:80`, `:82`, `:84`. -/
theorem ethickness_le_of_subset_of_isPlankOfDimensions {C a b : NNReal}
    {W W' : ConvexSpaceBody E} (hsub : W'.carrier ⊆ W.carrier)
    (hW : IsPlankOfDimensions C a b W) :
    Metric.ethickness ℝ W'.carrier 0 ≤ (C : ENNReal) ∧
      Metric.ethickness ℝ W'.carrier 1 ≤ (C : ENNReal) * (b : ENNReal) ∧
        Metric.ethickness ℝ W'.carrier 2 ≤ (C : ENNReal) * (a : ENNReal) := by
  constructor
  · exact (Metric.ethickness_monotone hsub 0).trans hW.1.2
  · constructor
    · exact (Metric.ethickness_monotone hsub 1).trans hW.2.1.2
    · exact (Metric.ethickness_monotone hsub 2).trans hW.2.2.2

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The band of a plank is pinned by the plank's own thicknesses.**

The two lower brackets of `Kakeya.IsPlankOfDimensions` read, after multiplying by `C`, as
`b ≤ C τ₁(W)` and `a ≤ C τ₂(W)`.  This is the form in which the band of a *restricted* part is
capped: whatever a sub-body's thicknesses are, they cap the band any factorization containing it
may use. -/
theorem le_mul_ethickness_of_isPlankOfDimensions {C a b : NNReal} (hC : C ≠ 0)
    {W : ConvexSpaceBody E} (hW : IsPlankOfDimensions C a b W) :
    (b : ENNReal) ≤ (C : ENNReal) * Metric.ethickness ℝ W.carrier 1 ∧
      (a : ENNReal) ≤ (C : ENNReal) * Metric.ethickness ℝ W.carrier 2 := by
  have hC0 : (C : ENNReal) ≠ 0 := by exact_mod_cast hC
  have hCtop : (C : ENNReal) ≠ ⊤ := by simp
  constructor
  · calc
      (b : ENNReal) = (C : ENNReal) * ((C : ENNReal)⁻¹ * (b : ENNReal)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hC0 hCtop, one_mul]
      _ ≤ (C : ENNReal) * Metric.ethickness ℝ W.carrier 1 := by
        gcongr; exact hW.2.1.1
  · calc
      (a : ENNReal) = (C : ENNReal) * ((C : ENNReal)⁻¹ * (a : ENNReal)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hC0 hCtop, one_mul]
      _ ≤ (C : ENNReal) * Metric.ethickness ℝ W.carrier 2 := by
        gcongr; exact hW.2.2.1

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A plank inside a single `δ̃`-tube caps both band parameters at `C δ̃`.**

The concrete form of `Kakeya.ml1Boot.le_mul_ethickness_of_isPlankOfDimensions` for the
configuration an arbitrary restriction can create: a part of `fibre u₁ pρ m` met by `s'` in a
single member has its hull inside that member's `δ̃`-tube, and then
`Kakeya.ml1Boot.tube_ethickness_bounds` gives `τ₁ = τ₂ = δ̃` for the tube, so `a, b ≤ C δ̃`.
Since the plank pigeonhole allows `bp` anywhere in `[δ̃, ρ]`, this is a genuine restriction and
not a triviality. -/
theorem plankBand_le_mul_of_subset_tube (hdim : Module.finrank ℝ E = 3)
    {C a b δt : NNReal} (hC : C ≠ 0) (Tδ : Tube δt E)
    {W : ConvexSpaceBody E} (hWsub : W.carrier ⊆ Tδ.carrier)
    (hW : IsPlankOfDimensions C a b W) :
    a ≤ C * δt ∧ b ≤ C * δt := by
  have hn : 2 ≤ Module.finrank ℝ E := by omega
  have hk1 : (1 : ℕ) ≤ Module.finrank ℝ E - 1 := by omega
  have hk2 : (2 : ℕ) ≤ Module.finrank ℝ E - 1 := by omega
  have h1up : Metric.ethickness ℝ W.carrier 1 ≤ (δt : ENNReal) :=
    (Metric.ethickness_monotone hWsub 1).trans
      (le_of_eq ((tube_ethickness_bounds hn Tδ).2.2 1 (by norm_num) hk1))
  have h2up : Metric.ethickness ℝ W.carrier 2 ≤ (δt : ENNReal) :=
    (Metric.ethickness_monotone hWsub 2).trans
      (le_of_eq ((tube_ethickness_bounds hn Tδ).2.2 2 (by norm_num) hk2))
  have hC0 : (C : ENNReal) ≠ 0 := by exact_mod_cast hC
  have hCtop : (C : ENNReal) ≠ ⊤ := by simp
  constructor
  · have ha : (a : ENNReal) ≤ (C : ENNReal) * Metric.ethickness ℝ W.carrier 2 := by
      calc
        (a : ENNReal) = (C : ENNReal) * ((C : ENNReal)⁻¹ * (a : ENNReal)) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hC0 hCtop, one_mul]
        _ ≤ (C : ENNReal) * Metric.ethickness ℝ W.carrier 2 := by
          gcongr; exact hW.2.2.1
    refine (ENNReal.coe_le_coe.mp ?_)
    calc
      (a : ENNReal) ≤ (C : ENNReal) * Metric.ethickness ℝ W.carrier 2 := ha
      _ ≤ (C : ENNReal) * (δt : ENNReal) := by gcongr
      _ = ((C * δt : NNReal) : ENNReal) := by norm_num [ENNReal.coe_mul]
  · have hb : (b : ENNReal) ≤ (C : ENNReal) * Metric.ethickness ℝ W.carrier 1 := by
      calc
        (b : ENNReal) = (C : ENNReal) * ((C : ENNReal)⁻¹ * (b : ENNReal)) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hC0 hCtop, one_mul]
        _ ≤ (C : ENNReal) * Metric.ethickness ℝ W.carrier 1 := by
          gcongr; exact hW.2.1.1
    refine (ENNReal.coe_le_coe.mp ?_)
    calc
      (b : ENNReal) ≤ (C : ENNReal) * Metric.ethickness ℝ W.carrier 1 := hb
      _ ≤ (C : ENNReal) * (δt : ENNReal) := by gcongr
      _ = ((C * δt : NNReal) : ENNReal) := by norm_num

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **A common band forces the parts' thicknesses to agree up to `C ^ 2`.**

Combining the upper bracket of one plank with
`Kakeya.ml1Boot.le_mul_ethickness_of_isPlankOfDimensions` for the other: two bodies carrying the
*same* pair `(a, b)` at the same constant have `τ₁` and `τ₂` within a factor `C ^ 2`.  This is the
exact price of the word "same" in `Kakeya.IsPlankFamilyOfDimensions`, and the reason a
caller-prescribed subfamily cannot be banded: restriction moves different parts by different
amounts. -/
theorem ethickness_le_sq_mul_of_isPlankOfDimensions_pair {C a b : NNReal} (hC : C ≠ 0)
    {W W' : ConvexSpaceBody E} (hW : IsPlankOfDimensions C a b W)
    (hW' : IsPlankOfDimensions C a b W') :
    Metric.ethickness ℝ W'.carrier 1 ≤ (C : ENNReal) ^ 2 * Metric.ethickness ℝ W.carrier 1 ∧
      Metric.ethickness ℝ W'.carrier 2 ≤ (C : ENNReal) ^ 2 * Metric.ethickness ℝ W.carrier 2 := by
  have hC0 : (C : ENNReal) ≠ 0 := by exact_mod_cast hC
  have hCtop : (C : ENNReal) ≠ ⊤ := by simp
  constructor
  · calc
      Metric.ethickness ℝ W'.carrier 1 ≤ (C : ENNReal) * (b : ENNReal) := hW'.2.1.2
      _ ≤ (C : ENNReal) * ((C : ENNReal) * Metric.ethickness ℝ W.carrier 1) := by
        have hb : (b : ENNReal) ≤ (C : ENNReal) * Metric.ethickness ℝ W.carrier 1 := by
          calc
            (b : ENNReal) = (C : ENNReal) * ((C : ENNReal)⁻¹ * (b : ENNReal)) := by
              rw [← mul_assoc, ENNReal.mul_inv_cancel hC0 hCtop, one_mul]
            _ ≤ (C : ENNReal) * Metric.ethickness ℝ W.carrier 1 := by
              gcongr; exact hW.2.1.1
        gcongr
      _ = (C : ENNReal) ^ 2 * Metric.ethickness ℝ W.carrier 1 := by
        rw [← mul_assoc, ← pow_two]
  · calc
      Metric.ethickness ℝ W'.carrier 2 ≤ (C : ENNReal) * (a : ENNReal) := hW'.2.2.2
      _ ≤ (C : ENNReal) * ((C : ENNReal) * Metric.ethickness ℝ W.carrier 2) := by
        have ha : (a : ENNReal) ≤ (C : ENNReal) * Metric.ethickness ℝ W.carrier 2 := by
          calc
            (a : ENNReal) = (C : ENNReal) * ((C : ENNReal)⁻¹ * (a : ENNReal)) := by
              rw [← mul_assoc, ENNReal.mul_inv_cancel hC0 hCtop, one_mul]
            _ ≤ (C : ENNReal) * Metric.ethickness ℝ W.carrier 2 := by
              gcongr; exact hW.2.2.1
        gcongr
      _ = (C : ENNReal) ^ 2 * Metric.ethickness ℝ W.carrier 2 := by
        rw [← mul_assoc, ← pow_two]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The obstruction of (C2) and (C3) as a theorem: a thinned part and a full part admit no
common band.**

If one body lies inside a `δ̃`-tube and another has `τ₁ > C ^ 2 δ̃`, then *no* pair `(a, b)` makes
both `Kakeya.IsPlankOfDimensions C a b`.  This is what a restriction along an arbitrary `s' ⊆ u₁`
can produce inside one fibre — keep a single member of one part, keep another part whole — and it
is why `Kakeya.ml1Boot.exists_plankFactorization_of_subsetParts` has no intersect-and-re-band
analogue.  The hypothesis is satisfiable in the intended regime because `plankPigeonhole.C` is
fixed before `δ̃` while the untouched part's `τ₁` may be as large as `ρ = δ̃ ^ (6 ε)`. -/
theorem not_exists_commonPlankBand_of_subset_tube (hdim : Module.finrank ℝ E = 3)
    {C δt : NNReal} (hC : C ≠ 0) (Tδ : Tube δt E)
    {W W' : ConvexSpaceBody E} (hWsub : W.carrier ⊆ Tδ.carrier)
    (hgt : (C : ENNReal) ^ 2 * (δt : ENNReal) < Metric.ethickness ℝ W'.carrier 1) :
    ¬ ∃ a b : NNReal, IsPlankOfDimensions C a b W ∧ IsPlankOfDimensions C a b W' := by
  rintro ⟨a, b, hW, hW'⟩
  have hn : 2 ≤ Module.finrank ℝ E := by
    omega
  have hk1 : (1 : ℕ) ≤ Module.finrank ℝ E - 1 := by
    omega
  have h1up : Metric.ethickness ℝ W.carrier 1 ≤ (δt : ENNReal) := by
    exact (Metric.ethickness_monotone hWsub 1).trans
      (le_of_eq ((tube_ethickness_bounds hn Tδ).2.2 1 (by norm_num) hk1))
  have hsq := (ethickness_le_sq_mul_of_isPlankOfDimensions_pair hC hW hW').1
  have hle : Metric.ethickness ℝ W'.carrier 1 ≤ (C : ENNReal) ^ 2 * (δt : ENNReal) := by
    calc
      Metric.ethickness ℝ W'.carrier 1 ≤ (C : ENNReal) ^ 2 * Metric.ethickness ℝ W.carrier 1 := hsq
      _ ≤ (C : ENNReal) ^ 2 * (δt : ENNReal) := by gcongr
  exact (not_lt_of_ge hle) hgt

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Re-banding a single part is free, at constant `2`.**

Every nonempty block of `δ̃`-tubes lying in `B₁` and in a common `ρ`-tube is an `a × b × 1` plank
at constant `2` for *its own* band `a = τ₂`, `b = τ₁`, with `δ̃ ≤ a ≤ b ≤ ρ`.  The three range
hypotheses come from `Kakeya.ml1Boot.ethickness_bounds_convexHull_tubes`, and the six brackets are
then immediate because the band is read off the body itself.

This is the positive half of (C2): plankness is never what a restriction destroys, and a part met
by an arbitrary `s'` in a nonempty set is still a plank.  What a restriction destroys is the
*common* band shared across parts and across parents, and
`Kakeya.ml1Boot.not_exists_commonPlankBand_of_subset_tube` shows no constant repairs that. -/
theorem exists_isPlankOfDimensions_ownBand (hdim : Module.finrank ℝ E = 3)
    {δt ρ : NNReal} (hδt0 : 0 < δt) (hδρ : δt ≤ ρ) (hρ1 : ρ ≤ 1)
    {ι : Type*} {t : Finset ι} (ht : t.Nonempty)
    (T : ι → Tube δt E) (Tρ : Tube ρ E)
    (hball : ∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hsub : ∀ i ∈ t, (T i).carrier ⊆ Tρ.carrier) :
    ∃ a b : NNReal, δt ≤ a ∧ a ≤ b ∧ b ≤ ρ ∧
      IsPlankOfDimensions 2 a b
        (t.convexHull_biUnion fun i => (T i).toConvexSpaceBody) := by
  classical
  let W : ConvexSpaceBody E := t.convexHull_biUnion fun i => (T i).toConvexSpaceBody
  let eth0 : ENNReal := Metric.ethickness ℝ W.carrier 0
  let eth1 : ENNReal := Metric.ethickness ℝ W.carrier 1
  let eth2 : ENNReal := Metric.ethickness ℝ W.carrier 2
  have hb := ethickness_bounds_convexHull_tubes hdim hδt0 hδρ hρ1 ht T Tρ hball hsub
  have h0ic : eth0 ∈ Set.Icc (2⁻¹ : ENNReal) 1 := by
    simpa [W, eth0] using hb.1
  have h1ic : eth1 ∈ Set.Icc (δt : ENNReal) (ρ : ENNReal) := by
    simpa [W, eth1] using hb.2.1
  have h2ic : eth2 ∈ Set.Icc (δt : ENNReal) (ρ : ENNReal) := by
    simpa [W, eth2] using hb.2.2
  have h1top : eth1 ≠ ⊤ := ne_of_lt (lt_of_le_of_lt h1ic.2 ENNReal.coe_lt_top)
  have h2top : eth2 ≠ ⊤ := ne_of_lt (lt_of_le_of_lt h2ic.2 ENNReal.coe_lt_top)
  let b : NNReal := eth1.toNNReal
  let a : NNReal := eth2.toNNReal
  have hbEq : (b : ENNReal) = eth1 := by
    dsimp [b, eth1, W]
    exact ENNReal.coe_toNNReal h1top
  have haEq : (a : ENNReal) = eth2 := by
    dsimp [a, eth2, W]
    exact ENNReal.coe_toNNReal h2top
  have hδa : δt ≤ a := ENNReal.coe_le_coe.mp (by
    rw [haEq]
    exact h2ic.1)
  have hab : a ≤ b := ENNReal.coe_le_coe.mp (by
    rw [haEq, hbEq]
    simpa [eth1, eth2, W] using (Metric.ethickness_antitone (by norm_num : (1 : ℕ) ≤ (2 : ℕ))))
  have hbρ : b ≤ ρ := ENNReal.coe_le_coe.mp (by
    rw [hbEq]
    exact h1ic.2)
  have hplank : IsPlankOfDimensions 2 a b W := by
    unfold IsPlankOfDimensions
    have h2 : ((2 : NNReal) : ENNReal) = (2 : ENNReal) := by norm_num
    rw [h2]
    constructor
    · constructor
      · simpa [W, eth0] using h0ic.1
      · exact le_trans h0ic.2 (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal))
    · constructor
      · constructor
        · rw [hbEq]
          calc
            (2 : ENNReal)⁻¹ * eth1 ≤ 1 * eth1 := by
              exact mul_le_mul_left (by norm_num : (2 : ENNReal)⁻¹ ≤ 1) eth1
            _ = eth1 := by rw [one_mul]
        · rw [hbEq]
          calc
            eth1 = 1 * eth1 := by rw [one_mul]
            _ ≤ (2 : ENNReal) * eth1 := by
              exact mul_le_mul_left (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal)) eth1
      · constructor
        · rw [haEq]
          calc
            (2 : ENNReal)⁻¹ * eth2 ≤ 1 * eth2 := by
              exact mul_le_mul_left (by norm_num : (2 : ENNReal)⁻¹ ≤ 1) eth2
            _ = eth2 := by rw [one_mul]
        · rw [haEq]
          calc
            eth2 = 1 * eth2 := by rw [one_mul]
            _ ≤ (2 : ENNReal) * eth2 := by
              exact mul_le_mul_left (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal)) eth2
  exact ⟨a, b, hδa, hab, hbρ, hplank⟩

end Pigeonhole

end ml1Boot

end Kakeya
