/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.GapsKT
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFixedTowerStopping

/-!
# A `GridUniformCore` from a bare `UniformTubeSet` — and the price, measured

 split `MultiScaleFac.GridUniform` into `GridUniformCore` (cover, `uniformAt`,
`parent_eq`, `tube_eq`, `le_card_class`) plus `clumped` and `nice`, and restated the Katz-Tao
alternatives over the core so that a **fixed tower** — a bare `Tube.UniformTubeSet` — can drive
them.  This file closes that route: it builds the core from the tube set.

## The constant is `Cu ^ 3`, not `Cu ^ 2` — and here is exactly why

The route named in `SpineFixedTowerStopping.lean` is
`Tube.UniformTubeSet.toChain` ≫ `Tube.ChainUniformTubeSet.uniformAt`, which delivers
`Tube.IsUniformAtScale` at `Cu ^ 2` (`ChainUniform.lean:374`, the containment bracket of
`card_filter_le`).  That is **not by itself a `GridUniformCore`**, and the gap is one field:

> `GridUniformCore.le_card_class` (`FibreCommon.lean:757`) is **tight** —
> `(uniformAt k hk).branchingN ≤ (coverClass t (cover.assign k) P).card`, with *no* constant —
> whereas `Tube.UniformTubeSet.le_card_class` (`Uniform.lean:173`) carries one:
> `branchingN k ≤ C * (coverClass …).card`.

So the tube set's own branching number cannot be handed over unchanged.  The fix is to hand over
`𝒰.branchingN k / Cu`, which *is* tight against the class; the cost is that the containment upper
bound has to be re-read against the shrunken branching number:

  `card_filter ≤ Cu ^ 2 * 𝒰.branchingN k = Cu ^ 3 * (𝒰.branchingN k / Cu)`,

so the structure's constant is `Cu ^ 3`.  The two lower-bound fields
(`le_mul_card_filter`, `le_card_class`) hold already at `Cu`, and `boundedOverlap` at `Cu`; the
single field that forces the third power is `card_filter_le`.

**This is a correction to the `Cu²` sizing carried in the dispatch and in
`SpineFixedTowerStopping.lean`'s A3 note, and it is stated rather than fitted.**  It changes no
conclusion of that note: 's A3 finding is that `Cu` is bracketed by a
**δ-free** constant at every site this landing reaches (`ssfUniformConst` δ-free; the floor sites
at `Cu ≤ Cu₀` with `Cu₀` δ-free and already carrying `Cu ^ 8`).  A δ-free constant cubed is still
δ-free, so `Cu ^ 3` enters no δ-exponent account — no `hexp` term, no `κ'`, no `` row — exactly
as `Cu ^ 2` did.  `cu_cube_le_cu_pow_eight` records that it still sits inside the `Cu ^ 8` bracket
the floor sites carry, which is the concrete form of the claim.

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `toGridUniformCore` | the tube set's `t`, `T`; **no shading** | none — per-scale, one per level |
| `toGridUniformCore_cover` | as above | none |
| `cu_cube_le_cu_pow_eight` | none | none |

No shading enters: `GridUniformCore` is a statement about tubes, nodes and classes only.

## A1-a

`GridUniformCore` appears here, in the Katz-Tao alternatives, in `BlockKatzTaoOn` /
`passingNodesKT`, and in the fixed-tower stopping run.  It appears in **no** field of
`FloorHypothesisAt`, `FloorDataAtTrichotomy`, `RefinedFloorHypothesis`, `hfac` or
`ML2Reduction.IsKatzTaoDividingWindow(Levels)` — this file adds no interface statement at all, only
a constructor and a `rfl` lemma.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory Tube

namespace Kakeya.ML2Core

section GridUniformCoreOfTubeSet

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The class of a node sits inside the set of members *contained* in that node: a member assigned
to `P` lies in `P`'s tube by `GridCoverSystem.le_tube_assign`.  This is the inclusion that turns
the class lower bound of `Tube.UniformTubeSet` into the containment lower bound
`Tube.IsUniformAtScale.le_mul_card_filter` asks for. -/
theorem coverClass_subset_filter_le_tube (𝒰 : Tube.UniformTubeSet t T N Cu) {k : ℕ} (hk : k ≤ N)
    {P : ι} :
    coverClass t (𝒰.cover.assign k) P
      ⊆ {i ∈ t | (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k P).toConvexSpaceBody} := by
  classical
  intro i hi
  simp only [coverClass, Finset.mem_filter] at hi ⊢
  refine ⟨hi.1, ?_⟩
  have h := 𝒰.cover.le_tube_assign k hk i hi.1
  rwa [hi.2] at h

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The shrunken branching number is tight against the class.**  This is the field
`MultiScaleFac.GridUniformCore.le_card_class` asks for, and the reason the branching number has to
be divided by `Cu` before it can be handed over. -/
theorem branchingN_div_le_card_class (hCu : 1 ≤ Cu) (𝒰 : Tube.UniformTubeSet t T N Cu)
    {k : ℕ} (hk : k ≤ N) {P : ι} (hP : P ∈ 𝒰.cover.indexSet k) :
    𝒰.branchingN k / Cu ≤ ((coverClass t (𝒰.cover.assign k) P).card : NNReal) := by
  have hCu0 : (0 : NNReal) < Cu := lt_of_lt_of_le zero_lt_one hCu
  rw [div_le_iff₀ hCu0, mul_comm]
  exact 𝒰.le_card_class k hk P hP

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- …and therefore against the larger *containment* set, which is what
`Tube.IsUniformAtScale.le_mul_card_filter` is stated over. -/
theorem branchingN_div_le_card_filter (hCu : 1 ≤ Cu) (𝒰 : Tube.UniformTubeSet t T N Cu)
    {k : ℕ} (hk : k ≤ N) {P : ι} (hP : P ∈ 𝒰.cover.indexSet k) :
    𝒰.branchingN k / Cu
      ≤ (({i ∈ t | (T i).toConvexSpaceBody
            ≤ (𝒰.cover.tube k P).toConvexSpaceBody}).card : NNReal) := by
  classical
  refine (branchingN_div_le_card_class hCu 𝒰 hk hP).trans ?_
  exact_mod_cast Finset.card_le_card (coverClass_subset_filter_le_tube 𝒰 hk)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The identity that fixes the constant at the third power: the containment bracket is proved
against `𝒰.branchingN k`, and reading it against `𝒰.branchingN k / Cu` costs one more `Cu`. -/
theorem cu_cube_mul_div (hCu : 1 ≤ Cu) (b : NNReal) : Cu ^ 3 * (b / Cu) = Cu ^ 2 * b := by
  have hCu0 : Cu ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hCu)
  field_simp

/-- **A bare `Tube.UniformTubeSet` supplies a `MultiScaleFac.GridUniformCore`, at `Cu ^ 3`.**

The branching number handed to the per-scale witness is `𝒰.branchingN k / Cu`, *not*
`𝒰.branchingN k`: the core's `le_card_class` is tight against the class while the tube set's is
only tight up to `Cu`, so the branching number must be divided before it will fit.  The
containment upper bound is then read against the shrunken number and costs the third power.  See
the module docstring for why the third power is free.

**Family/shading:** `t`, `T`; no shading.  **Level pair:** none — per-scale data. -/
noncomputable def _root_.Tube.UniformTubeSet.toGridUniformCore (hCu : 1 ≤ Cu)
    (𝒰 : Tube.UniformTubeSet t T N Cu) :
    Kakeya.MultiScaleFac.GridUniformCore t T N (Cu ^ 3) where
  cover := 𝒰.cover
  uniformAt k hk :=
    { branchingN := 𝒰.branchingN k / Cu
      parent := 𝒰.cover.indexSet k
      parentTube := 𝒰.cover.tube k
      exists_le_rescale := fun {i} hi =>
        ⟨𝒰.cover.assign k i, 𝒰.cover.assign_mem k hk i hi, 𝒰.cover.le_tube_assign k hk i hi⟩
      boundedOverlap := fun V =>
        (𝒰.boundedOverlap k hk V).trans (le_self_pow₀ hCu (by norm_num))
      parentTube_injOn := 𝒰.tube_injOn k hk
      card_filter_le := fun {j} hj => by
        classical
        rw [cu_cube_mul_div hCu]
        exact 𝒰.toChain.card_filter_le hCu hk hj
      le_mul_card_filter := fun {j} hj => by
        classical
        refine (branchingN_div_le_card_filter hCu 𝒰 hk hj).trans ?_
        calc (({i ∈ t | (T i).toConvexSpaceBody
                ≤ (𝒰.cover.tube k j).toConvexSpaceBody}).card : NNReal)
            = 1 * (({i ∈ t | (T i).toConvexSpaceBody
                ≤ (𝒰.cover.tube k j).toConvexSpaceBody}).card : NNReal) := (one_mul _).symm
          _ ≤ Cu ^ 3 * (({i ∈ t | (T i).toConvexSpaceBody
                ≤ (𝒰.cover.tube k j).toConvexSpaceBody}).card : NNReal) := by
              gcongr
              exact one_le_pow₀ hCu }
  parent_eq _ _ := rfl
  tube_eq _ _ _ _ := rfl
  le_card_class k hk P hP := branchingN_div_le_card_class hCu 𝒰 hk hP

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The core built from a tube set has **that tube set's own cover**, definitionally.  This is the
`hcov` the `_core` Katz-Tao alternatives ask for, at `rfl`. -/
theorem toGridUniformCore_cover (hCu : 1 ≤ Cu) (𝒰 : Tube.UniformTubeSet t T N Cu) :
    𝒰.cover = (𝒰.toGridUniformCore hCu).cover := rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The `Cu ^ 3` of `Tube.UniformTubeSet.toGridUniformCore` still sits inside the `Cu ^ 8` bracket
the floor sites already carry, so it costs no new row — the same conclusion
`cu_sq_le_cu_pow_eight` records for the square. -/
theorem cu_cube_le_cu_pow_eight (hCu : 1 ≤ Cu) : Cu ^ 3 ≤ Cu ^ 8 :=
  pow_le_pow_right₀ hCu (by norm_num)


section FixedTowerAlternatives

open MultiScaleFac _root_.StickyKakeya

/-! ### The Katz-Tao alternatives, run on the fixed tower

The point of the whole `GridUniformCore` split, : both alternatives now take the
inherited tower itself and return statements about **that** tower's cover.
-/

/-- **Alternative (i) of GWZ Lemma 7.7(B), run on a fixed tower.**  The `GridUniformCore` is the
one `Tube.UniformTubeSet.toGridUniformCore` builds from `𝒰` itself, so `hcov` is `rfl` and the
conclusion is about `𝒰` — no fresh hierarchy is manufactured anywhere in the chain.  This is the
form 's *"then `towerUniformAtScaleData_of_uniformTubeSet` at
`Cu²` builds a `GridUniformCore` from a bare `UniformTubeSet` and the payload side closes"*, with
the constant corrected to `Cu ^ 3` (see the module docstring).

**Family/shading:** `t`, `T`; no shading.  **Level pair:** the cut set `S`; no window pair. -/
theorem alternativeOneKT_of_cutsKT_fixedTower (hn : Module.finrank ℝ E = 3)
    (Cu Cb : NNReal) (hCu : 1 ≤ Cu) (hCb : 1 ≤ Cb) :
    ∃ (B : NNReal) (K c : ℕ), 1 ≤ B ∧ Cb ≤ B ∧
      ∀ (N : ℕ), 4096 ≤ N → ∀ {ε : ℝ}, ε = 1 / Real.sqrt (N : ℝ) →
      ∀ (Mgrid : ℕ), 16 ≤ Mgrid → N ≤ Mgrid →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 → δ ≤ (16 : NNReal) ^ (-(Mgrid : ℝ)) →
      Mgrid ≤ ssfGridLen δ →
      ∀ (t : Finset ι) (T : ι → Tube δ E), t.Nonempty →
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (𝒰 : Tube.UniformTubeSet t T Mgrid Cu),
      ∀ (ζ : ℝ), 0 ≤ ζ → ζ ≤ ε →
      ∀ S : Finset ℕ, 0 ∈ S → Mgrid ∈ S →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
        BlockKatzTaoOn t (𝒰.toGridUniformCore hCu).uniformAt Cb ζ a b ∧ ¬ IsLongBlock Mgrid ε a b) →
      𝒰.IsKatzTaoAtEveryScale
        ((B : ENNReal) * totalLoss B K c δ
          * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε)))) := by
  obtain ⟨B, K, c, hB1, hCbB, h⟩ :=
    MultiScaleFac.alternativeOneKT_of_cutsKT_core.{u, _} (E := E) hn (Cu ^ 3) Cu Cb
      (one_le_pow₀ hCu) hCu hCb
  refine ⟨B, K, c, hB1, hCbB, ?_⟩
  intro N hN eps heps Mgrid hM16 hNM ιx δ hd0 hd1 hdM hMss t T hs hball 𝒰 zeta hz0 hzeps S hS0
    hSM hblocks
  exact h N hN heps Mgrid hM16 hNM hd0 hd1 hdM hMss t T hs hball (𝒰.toGridUniformCore hCu) 𝒰 rfl
    zeta hz0 hzeps S hS0 hSM hblocks

/-- **Alternative (ii) of GWZ Lemma 7.7(B), run on a fixed tower.**  As the previous, for the
terminal-block alternative: every index set and every tube in the conclusion is `𝒰`'s own.

**Family/shading:** `t`, `T`; no shading.  **Level pair:** `(a,b)` with the interior index `c` of
the window; the window is the index window `a + ⌈ε(b-a)⌉ ≤ c`, `c + ⌈ε(b-a)⌉ ≤ b`. -/
theorem alternativeTwoKT_of_terminal_block_fixedTower (hn : Module.finrank ℝ E = 3)
    (Cu Cb : NNReal) (hCu : 1 ≤ Cu) (hCb : 1 ≤ Cb) :
    ∃ (C : NNReal) (K cL : ℕ), 1 ≤ C ∧ Cb ≤ C ∧
      ∀ (N : ℕ), 4096 ≤ N → ∀ {ε : ℝ}, ε = 1 / Real.sqrt (N : ℝ) →
      ∀ (Mgrid : ℕ), 16 ≤ Mgrid → N ≤ Mgrid →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 → δ ≤ (16 : NNReal) ^ (-(Mgrid : ℝ)) →
      Mgrid ≤ ssfGridLen δ →
      ∀ (t : Finset ι) (T : ι → Tube δ E), t.Nonempty →
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (𝒰 : Tube.UniformTubeSet t T Mgrid Cu),
      ∀ (ζ ζ' : ℝ), 0 ≤ ζ → 0 ≤ ζ' →
      ∀ S : Finset ℕ, 0 ∈ S → Mgrid ∈ S →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
        BlockKatzTaoOn t (𝒰.toGridUniformCore hCu).uniformAt Cb ζ a b) →
      ∀ a b : ℕ, a ∈ S → b ∈ S → a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
      IsLongBlock Mgrid ε a b → b ≤ Mgrid →
      ¬ (t.card ≤ 2 * (passingNodesKT t (𝒰.toGridUniformCore hCu).uniformAt Cb ε ζ' a b).card) →
      ∃ F ⊆ 𝒰.cover.indexSet a,
        (((𝒰.cover.indexSet a).card : ENNReal)
            ≤ (C : ENNReal) * totalLoss C K cL δ * (F.card : ENNReal)) ∧
        Kakeya.maxDensity (𝒰.cover.indexSet a)
            (fun j => (𝒰.cover.tube a j).toConvexSpaceBody)
          ≤ (C : ENNReal) * totalLoss C K cL δ
              * ENNReal.ofReal ((gridScale δ Mgrid a : ℝ) ^ (-ζ)) ∧
        (∀ j ∈ 𝒰.cover.indexSet a,
          Kakeya.maxDensity (𝒰.nodesUnder b a j)
              (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
            ≤ (C : ENNReal) * totalLoss C K cL δ
                * ENNReal.ofReal
                (((gridScale δ Mgrid a : ℝ) / (gridScale δ Mgrid b : ℝ)) ^ ζ)) ∧
        (∀ c : ℕ, a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c →
          c + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b →
          ∀ j ∈ F,
            ENNReal.ofReal (((gridScale δ Mgrid a : ℝ) / (gridScale δ Mgrid c : ℝ)) ^ ζ')
              ≤ (C : ENNReal) * totalLoss C K cL δ *
                  Kakeya.maxDensity
                    (𝒰.nodesIn c
                      (((𝒰.cover.tube a j).rescale
                          (8 * gridScale δ Mgrid a)).toConvexSpaceBody))
                    (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)) := by
  obtain ⟨C, K, cL, hC1, hCbC, h⟩ :=
    MultiScaleFac.alternativeTwoKT_of_terminal_block_core.{u, _} (E := E) hn (Cu ^ 3) Cu Cb
      (one_le_pow₀ hCu) hCu hCb
  refine ⟨C, K, cL, hC1, hCbC, ?_⟩
  intro N hN eps heps Mgrid hM16 hNM ιx δ hd0 hd1 hdM hMss t T hs hball 𝒰 zeta zeta' hz0 hz'0 S
    hS0 hSM hblocks a b haS hbS hab hadj hlong hbM hnotpass
  exact h N hN heps Mgrid hM16 hNM hd0 hd1 hdM hMss t T hs hball (𝒰.toGridUniformCore hCu) 𝒰 rfl
    zeta zeta' hz0 hz'0 S hS0 hSM hblocks a b haS hbS hab hadj hlong hbM hnotpass

end FixedTowerAlternatives

end GridUniformCoreOfTubeSet

end Kakeya.ML2Core

end
