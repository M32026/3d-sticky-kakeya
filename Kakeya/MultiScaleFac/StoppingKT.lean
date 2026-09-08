/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.Homogenize
public import Kakeya.MultiScaleFac.StoppingA
public import Kakeya.MultiScaleFac.Loss
public import Kakeya.MultiScaleFac.RefineKT
public import Kakeya.MultiScaleFac.RefineStep

/-!
# The half-(B) stopping time, hoisted and banded

The Katz-Tao stopping time with its constants hoisted before `δ`, its banded variant, and the
quadratic loss accounting both are displayed at.

This module is the merge of the former `MultiScaleRefineKTHoisted`, `MultiScaleStoppingKTBand`,
`SsfLossQuad`.  Each keeps its own section, so its file-level `open`s and `variable`s stay confined
to it. -/

/-!
# The Katz-Tao stopping time carrying a homogenization band

The stopping time of `Kakeya/MultiScaleFac/StoppingKT.lean` returns a grid-uniform system on which
the block bound and the terminal alternative hold.  The amended dichotomy needs one more clause on
that same family: the paired homogenization band of
`Kakeya.Homogenize.exists_homogenizing_pass_gridUniform`.

Neither order of the two operations works on its own.  A band established *before* the stopping time
does not survive its refinements, and the stopping time's own terminal alternative does not survive
a band established *afterwards*: `Kakeya.maxDensity` only falls when members are deleted, and both
operations delete, while the failing half of the terminal test compares `tL.card` with the number of
passing nodes and moves under any deletion.  The band therefore has to be established inside each
refinement step, as its last operation.

That is what this file does, and the one structural obstruction it has to clear is the *constant*.
A homogenizing pass inflates the grid-uniform constant, so the composite of a refinement step and a
pass cannot preserve any single constant unless the refinement step's output constant is
independent of its input.  It is: the re-uniformization
`Kakeya.MultiScaleFac.exists_uniformize_subfamily_hoisted` hands back a system with a canonical
constant `Cu₀` whatever the constant of the system it was run against.  So
`Kakeya.MultiScaleFac.exists_refined_cutKT_hoisted_in` takes an arbitrary input constant and returns
`Cu₀`, and the pass turns `Cu₀` into `gridUniformBandConst Cu₀ 2`; the state of the stopping time is
read at that constant, and the composite maps it to itself.

The per-round cost gains one factor `(1 - log δ)^{2 (Mgrid+2)(Mgrid+1)}`, quadratic in the grid
length where the refinement step's own factor is linear.  It is absorbed by `gridLoss`, whose
polylogarithmic exponent is quadratic in `ssfGridLen δ` for exactly this reason, and the number of
rounds is at most `N + 1` with `N` fixed before `δ`, so `Kakeya.MultiScaleFac.gridLoss_pow` keeps
the accumulated cost a `gridLoss`.
-/

@[expose] public section

open MeasureTheory Real Metric ConvexSpaceBody
open Kakeya.Homogenize
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

universe u

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

variable {ι : Type*}

/-! ### The band, as a predicate on a grid-uniform system -/

open scoped Classical in
/-- **The paired homogenization band carried by a grid-uniform system** (blueprint
`def:pairBandOn`).  For every pair of levels `a`, `c` of the grid and every level-`a` node in use,
the maximal density of the level-`c` nodes met by the class of that node lies in
`[Φ a c, C₁ · Φ a c]`.  Naming it as a predicate lets it be threaded through the abstract run. -/
def PairBandOn {δ : NNReal} (t : Finset ι) {T : ι → Tube δ E} {Mgrid : ℕ} {Cv : NNReal}
    (𝒢 : GridUniform t T Mgrid Cv) (C₁ : NNReal) (Φ : ℕ → ℕ → ENNReal) (M : ℕ) : Prop :=
  ∀ a ≤ M, ∀ c ≤ M, ∀ j ∈ 𝒢.cover.indexSet a,
    Φ a c ≤ Kakeya.maxDensity
              ((coverClass t (𝒢.cover.assign a) j).image (𝒢.cover.assign c))
              (fun j' => (𝒢.cover.tube c j').toConvexSpaceBody) ∧
      Kakeya.maxDensity
          ((coverClass t (𝒢.cover.assign a) j).image (𝒢.cover.assign c))
          (fun j' => (𝒢.cover.tube c j').toConvexSpaceBody) ≤ (C₁ : ENNReal) * Φ a c

/-! ### Transport along a refined grid-uniform system -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The index sets of a grid-uniform system whose `uniformAt` parents sit inside those of another
are contained in the other's index sets. -/
private theorem gridUniform_indexSet_subset -- (extracted by Fuse golfer)
    {δ : NNReal} {N : ℕ} {t t' : Finset ι} {T : ι → Tube δ E} {Cv Cv' : NNReal}
    {𝒢 : GridUniform t T N Cv} {𝒢' : GridUniform t' T N Cv'}
    (hpar : ∀ k (hk : k ≤ N), (𝒢'.uniformAt k hk).parent ⊆ (𝒢.uniformAt k hk).parent) :
    ∀ n ≤ N, 𝒢'.cover.indexSet n ⊆ 𝒢.cover.indexSet n := fun n hn => by
  simpa only [𝒢'.parent_eq n hn, 𝒢.parent_eq n hn] using hpar n hn

omit [Nontrivial E] in
/-- A block Katz-Tao bound descends from one grid-uniform system to another whose `uniformAt`
parents sit inside it and whose cover tubes agree; the two grid-uniform constants are unrelated,
which is what distinguishes this from `Kakeya.MultiScaleFac.BlockKatzTaoAt.of_gridUniform_subcover`.
-/
private theorem blockKatzTaoOn_of_parent_subset -- (extracted by Fuse golfer)
    {δ : NNReal} {N : ℕ} {t t' : Finset ι} {T : ι → Tube δ E} {Cv Cv' : NNReal}
    {𝒢 : GridUniform t T N Cv} {𝒢' : GridUniform t' T N Cv'}
    (hpar : ∀ k (hk : k ≤ N), (𝒢'.uniformAt k hk).parent ⊆ (𝒢.uniformAt k hk).parent)
    (htub : ∀ k, 𝒢'.cover.tube k = 𝒢.cover.tube k) {C : NNReal} {ζ : ℝ} {a b : ℕ}
    {s s' : Finset ι} (hs : s' ⊆ s) (h : BlockKatzTaoOn s 𝒢.uniformAt C ζ a b) :
    BlockKatzTaoOn s' 𝒢'.uniformAt C ζ a b :=
  BlockKatzTaoOn.of_subcover hpar (fun n hn j hj => by
    have hjc : j ∈ 𝒢'.cover.indexSet n := by rwa [𝒢'.parent_eq n hn] at hj
    rw [𝒢'.tube_eq n hn j hjc, 𝒢.tube_eq n hn j (gridUniform_indexSet_subset hpar n hn hjc),
      htub n]) hs h

/-! ### The refinement step with its input constant freed -/

/-- **The hoisted Katz-Tao refinement step, at an arbitrary input constant** (blueprint
`lem:ktRefinedCutHoistedIn`).  `exists_refined_cutKT_hoisted_in` with the input and output constants
separated, as interleaving a homogenizing pass requires: the pass inflates the constant, so the step
has to accept whatever the pass produced while still returning the canonical one. -/
theorem exists_refined_cutKT_hoisted_in :
    ∃ (A : ℝ) (K : ℕ) (Cv : NNReal), 1 ≤ A ∧ 1 ≤ Cv ∧
      ∀ (Mgrid : ℕ), 0 < Mgrid → ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 64 →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ (16 : NNReal) ^ (-(Mgrid : ℝ)) →
      ∀ (t : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (↑t : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      ∀ (Cin : NNReal) (𝒢 : GridUniform t T Mgrid Cin) (C : NNReal) (ζ ζ' : ℝ), 0 ≤ ζ →
        ζ ≤ ε * ζ' →
      ∀ a b : ℕ, a < b → b ≤ Mgrid → IsLongBlock Mgrid ε a b →
      BlockKatzTaoOn t 𝒢.uniformAt C ζ a b →
      t.card ≤ 2 * (passingNodesKT t 𝒢.uniformAt C ε ζ' a b).card →
      ∃ (t' : Finset ι) (𝒢' : GridUniform t' T Mgrid Cv) (c : ℕ),
        t' ⊆ t ∧ a + ⌈ε * ((⌈ε * (Mgrid : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ ≤ c ∧
        c + ⌈ε * ((⌈ε * (Mgrid : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ ≤ b ∧
        (t.card : ℝ) ≤ 2 * ((Mgrid : ℝ) + 1) * (A ^ (Mgrid + 1)
            * (1 - Real.log (δ : ℝ)) ^ (K * (Mgrid + 1))) * (t'.card : ℝ) ∧
        (∀ n ≤ Mgrid, 𝒢'.cover.indexSet n ⊆ 𝒢.cover.indexSet n) ∧
        (∀ n, 𝒢'.cover.tube n = 𝒢.cover.tube n) ∧
        BlockKatzTaoOn t' 𝒢'.uniformAt C ζ' a c ∧
        BlockKatzTaoOn t' 𝒢'.uniformAt C ζ' c b := by
  classical
  obtain ⟨A, K, Cu₀, hA, hCu₀, hunif⟩ := exists_uniformize_subfamily_hoisted.{u, _} (E := E)
  refine ⟨A, K, Cu₀, hA, hCu₀, ?_⟩
  intro Mgrid hMg ε hεpos hε64 ι δ hδ hδN t T hball hED Cin 𝒢 C ζ ζ' hζ hgap a b hab hbN hlong hgood
    htest
  have hδ1 : δ ≤ 1 := hδN.trans (NNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (neg_lt_zero.mpr (by exact_mod_cast hMg))).le
  by_cases ht : t.Nonempty
  · have hPne : (passingNodesKT t 𝒢.uniformAt C ε ζ' a b).Nonempty :=
      Finset.card_pos.mp (by have := ht.card_pos; omega)
    obtain ⟨c, hac, hcb, P', hP'P, hP'ne, hcardP, hcoarse⟩ :=
      exists_common_cut_of_forall_nodeSplitTestKT hbN hPne
        (fun _ hi₀ => (mem_passingNodesKT.mp hi₀).2)
    have hP't : P' ⊆ t := hP'P.trans (passingNodesKT_subset _ _ _ _ _ _ _)
    obtain ⟨t', ht'P, hcard', 𝒢'₀, hpar₀, htub₀, _, _⟩ :=
      hunif Mgrid hMg hδ hδN t P' T hP't hball hED Cin 𝒢
    have hw_le : ⌈ε * ((⌈ε * (Mgrid : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ ≤ ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ :=
      KT.stoppingMargin_le_ceil_of_isLongBlock hεpos hlong
    refine ⟨t', 𝒢'₀, c, ht'P.trans hP't, (Nat.add_le_add_left hw_le a).trans hac,
      (Nat.add_le_add_left hw_le c).trans hcb, ?_,
      gridUniform_indexSet_subset hpar₀, htub₀,
      blockKatzTaoOn_of_parent_subset hpar₀ htub₀ ht'P hcoarse,
      blockKatzTaoOn_of_parent_subset hpar₀ htub₀ ht'P
        (BlockKatzTaoOn.anchor_le hδ hδ1 hεpos hζ hgap (le_trans (Nat.le_add_right a _) hac) hcb
          (BlockKatzTaoOn.subset hgood hP't))⟩
    calc (t.card : ℝ)
        ≤ 2 * (((Mgrid : ℝ) + 1) * (P'.card : ℝ)) := by
          exact_mod_cast htest.trans (Nat.mul_le_mul_left 2 hcardP)
      _ ≤ 2 * (((Mgrid : ℝ) + 1) * ((A ^ (Mgrid + 1)
          * (1 - Real.log (δ : ℝ)) ^ (K * (Mgrid + 1))) * (t'.card : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcard' (by positivity))
            (by norm_num)
      _ = _ := by ring
  · have hte : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    obtain ⟨t', ht'Pt, hcard', 𝒢'₀, hpar₀, htub₀, _, _⟩ :=
      hunif Mgrid hMg hδ hδN t t T (Finset.Subset.refl t) hball hED Cin 𝒢
    have ht'e : t' = ∅ := Finset.subset_empty.mp (by rw [← hte]; exact ht'Pt)
    have hnm : ∀ i, i ∉ t' := by simp [ht'e]
    exact ⟨t', 𝒢'₀, a + ⌈ε * ((⌈ε * (Mgrid : ℝ)⌉₊ : ℕ) : ℝ)⌉₊, ht'Pt, le_rfl,
      KT.two_mul_stoppingMargin_le_of_isLongBlock hεpos hε64 hlong,
      by rw [hte, ht'e, Finset.card_empty, Nat.cast_zero, mul_zero],
      gridUniform_indexSet_subset hpar₀, htub₀, fun i hi => absurd hi (hnm i),
      fun i hi => absurd hi (hnm i)⟩

/-! ### The stopping-time run with the band in the state -/

omit [Nontrivial E] in
/-- **The run of the hoisted Katz-Tao stopping time, with the homogenization band carried through**
(blueprint `lem:ktHoistedCutsRunBand`).  `Kakeya.StickyKakeya.exists_hoisted_cutsKT_run` with one
clause added to the state: the family and the system it carries come with a paired band, supplied at
the initial state and re-supplied by each step, so that the terminal state carries one. -/
theorem exists_hoisted_cutsKT_run_band
    (N Mgrid w : ℕ) (hw : 0 < w) (hwM : w ≤ Mgrid) (hwN : Mgrid ≤ w * N)
    {ε : ℝ} (η : ℕ → ℝ) (hηpos : ∀ k, k ≤ N → 0 ≤ η k)
    (hηmono : ∀ k l, k ≤ l → l ≤ N → η k ≤ η l)
    (hηgap : ∀ k, k < N → η k ≤ ε * η (k + 1))
    {ι : Type u} {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (s₀ : Finset ι) (T : ι → Tube δ E) (Cv C C₁ : NNReal)
    (P : ℝ) (hP1 : 1 ≤ P)
    (𝒢₀ : GridUniform s₀ T Mgrid Cv)
    (hgood₀ : BlockKatzTaoOn s₀ 𝒢₀.uniformAt C (η 0) 0 Mgrid)
    (Φ₀ : ℕ → ℕ → ENNReal) (hband₀ : PairBandOn s₀ 𝒢₀ C₁ Φ₀ Mgrid)
    (hcut : ∀ (t : Finset ι) (𝒢 : GridUniform t T Mgrid Cv), t ⊆ s₀ →
      ∀ ζ ζ' : ℝ, 0 ≤ ζ → ζ ≤ ε * ζ' →
      ∀ a b : ℕ, a < b → b ≤ Mgrid → IsLongBlock Mgrid ε a b →
      BlockKatzTaoOn t 𝒢.uniformAt C ζ a b →
      t.card ≤ 2 * (passingNodesKT t 𝒢.uniformAt C ε ζ' a b).card →
      ∃ (t' : Finset ι) (𝒢' : GridUniform t' T Mgrid Cv) (c : ℕ) (Φ : ℕ → ℕ → ENNReal),
        t' ⊆ t ∧ a + w ≤ c ∧ c + w ≤ b ∧
        (t.card : ℝ) ≤ P * (t'.card : ℝ) ∧
        (∀ n ≤ Mgrid, 𝒢'.cover.indexSet n ⊆ 𝒢.cover.indexSet n) ∧
        (∀ n, 𝒢'.cover.tube n = 𝒢.cover.tube n) ∧
        BlockKatzTaoOn t' 𝒢'.uniformAt C ζ' a c ∧
        BlockKatzTaoOn t' 𝒢'.uniformAt C ζ' c b ∧
        PairBandOn t' 𝒢' C₁ Φ Mgrid) :
    ∃ (S : Finset ℕ) (m : ℕ) (tL : Finset ι) (𝒢L : GridUniform tL T Mgrid Cv)
      (Φ : ℕ → ℕ → ENNReal),
      m < N ∧ tL ⊆ s₀ ∧ (s₀.card : ℝ) ≤ P ^ m * (tL.card : ℝ) ∧
      (∀ n ≤ Mgrid, 𝒢L.cover.indexSet n ⊆ 𝒢₀.cover.indexSet n) ∧
      (∀ n, 𝒢L.cover.tube n = 𝒢₀.cover.tube n) ∧
      0 ∈ S ∧ Mgrid ∈ S ∧ S ⊆ Finset.range (Mgrid + 1) ∧ S.card = m + 2 ∧
      PairBandOn tL 𝒢L C₁ Φ Mgrid ∧
      ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
        BlockKatzTaoOn tL 𝒢L.uniformAt C (η m) a b ∧
          (¬ IsLongBlock Mgrid ε a b ∨
            ¬ (tL.card
              ≤ 2 * (passingNodesKT tL 𝒢L.uniformAt C ε (η (m + 1)) a b).card)) := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP1
  set σ : Type _ := { p : (t : Finset ι) × GridUniform t T Mgrid Cv //
      p.1 ⊆ s₀ ∧ ∃ Φ : ℕ → ℕ → ENNReal, PairBandOn p.1 p.2 C₁ Φ Mgrid }
  set Good : ℕ → ℕ → ℕ → σ → Prop :=
    fun j a b x => BlockKatzTaoOn x.1.1 x.1.2.uniformAt C (η j) a b
  set Test : ℕ → ℕ → ℕ → σ → Prop :=
    fun j a b x =>
      x.1.1.card ≤ 2 * (passingNodesKT x.1.1 x.1.2.uniformAt C ε (η j) a b).card
  set Rel : ℕ → σ → σ → Prop :=
    fun k x y => y.1.1 ⊆ x.1.1 ∧ (x.1.1.card : ℝ) ≤ P ^ k * (y.1.1.card : ℝ) ∧
      (∀ n ≤ Mgrid, y.1.2.cover.indexSet n ⊆ x.1.2.cover.indexSet n) ∧
      (∀ n, y.1.2.cover.tube n = x.1.2.cover.tube n)
  have hrefl : ∀ x : σ, Rel 0 x x := fun x =>
    ⟨Finset.Subset.refl _, by simp, fun n _ => Finset.Subset.refl _, fun n => rfl⟩
  have hcomp : ∀ (k l : ℕ) (x y z : σ), Rel k x y → Rel l y z → Rel (k + l) x z := by
    intro k l x y z h₁ h₂
    refine ⟨h₂.1.trans h₁.1, ?_, fun n hn => (h₂.2.2.1 n hn).trans (h₁.2.2.1 n hn),
      fun n => (h₂.2.2.2 n).trans (h₁.2.2.2 n)⟩
    rw [pow_add, mul_assoc]
    exact h₁.2.1.trans (mul_le_mul_of_nonneg_left h₂.2.1 (pow_nonneg hP0 k))
  have hmono : ∀ j j' : ℕ, j ≤ j' → j' ≤ N → ∀ a b : ℕ, a < b → ∀ x : σ,
      Good j a b x → Good j' a b x := fun j j' hjj' hj' a b hab x hg =>
    BlockKatzTaoOn.mono hδ hδ1 le_rfl (hηpos j (hjj'.trans hj')) (hηmono j j' hjj' hj') hab.le hg
  have hdescend : ∀ j a b : ℕ, a < b → b ≤ Mgrid → ∀ x y : σ, Rel 1 x y →
      Good j a b x → Good j a b y := by
    intro j a b _hab _hbN x y hxy hg i₀ hi₀
    exact BlockKatzTaoAt.of_gridUniform_subcover x.1.2 y.1.2 hxy.2.2.1 hxy.2.2.2 (hg i₀ (hxy.1 hi₀))
  have hsplitEng : ∀ j a b : ℕ, j + 1 ≤ N → a < b → b ≤ Mgrid → IsLongBlock Mgrid ε a b →
      ∀ x : σ, Good j a b x → Test (j + 1) a b x →
      ∃ (y : σ) (c : ℕ), Rel 1 x y ∧ a + w ≤ c ∧ c + w ≤ b ∧
        Good (j + 1) a c y ∧ Good (j + 1) c b y := by
    intro j a b hj1 hab hbN hlong x hg htest
    obtain ⟨t', 𝒢', c, Φ, ht'x, hac, hcb, hcard', hpar', htub', hcoarse, hfine, hband⟩ :=
      hcut x.1.1 x.1.2 x.2.1 (η j) (η (j + 1)) (hηpos j (by omega)) (hηgap j (by omega))
        a b hab hbN hlong hg htest
    exact ⟨⟨⟨t', 𝒢'⟩, ht'x.trans x.2.1, ⟨Φ, hband⟩⟩, c, ⟨ht'x, by rwa [pow_one], hpar', htub'⟩,
      hac, hcb, hcoarse, hfine⟩
  obtain ⟨S, m, x, hm, hRel, h0, hMem, hsub, hcard, hconc⟩ :=
    exists_maximal_cuts_abstract_state_margin (σ := σ) Mgrid N w hw hwM hwN Good Test
      (IsLongBlock Mgrid ε) Rel ⟨⟨s₀, 𝒢₀⟩, Finset.Subset.refl s₀, ⟨Φ₀, hband₀⟩⟩
      hrefl hcomp hgood₀ hmono hdescend hsplitEng
  obtain ⟨Φ, hband⟩ := x.2.2
  refine ⟨S, m, x.1.1, x.1.2, Φ, hm, x.2.1, hRel.2.1, hRel.2.2.1, hRel.2.2.2,
    h0, hMem, hsub, hcard, hband, hconc⟩

/-! ### Numerical preliminaries for the accumulated loss -/

omit [Nontrivial E] in
/-- **The band weakens in its ratio** (blueprint `lem:pairBandOnMono`).  A two-sided bracket at
ratio `C₁` is one at any larger ratio, the lower half being untouched. -/
theorem PairBandOn.mono {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E} {Mgrid : ℕ} {Cv : NNReal}
    {𝒢 : GridUniform t T Mgrid Cv} {C₁ C₁' : NNReal} (hC : C₁ ≤ C₁') {Φ : ℕ → ℕ → ENNReal}
    {M : ℕ} (h : PairBandOn t 𝒢 C₁ Φ M) : PairBandOn t 𝒢 C₁' Φ M := fun a ha c hc j hj =>
  ⟨(h a ha c hc j hj).1,
    (h a ha c hc j hj).2.trans (mul_le_mul_left (by exact_mod_cast hC) (Φ a c))⟩

/-- **The displayed per-round loss grows with the grid length** (blueprint
`lem:hoistedStoppingLossMonoGrid`).  The shape `2(M+1) A^{M+1} W^{K(M+1)}` is increasing in `M` once
`A` and `W` are at least one, which lets a per-round loss displayed at an arbitrary grid length be
compared with `hoistedStoppingLoss_le_gridLoss`, which is stated at `ssfGridLen δ`. -/
theorem hoistedStoppingLoss_mono_grid {A W : ℝ} (hA : 1 ≤ A) (hW : 1 ≤ W) (K : ℕ) {Mg M : ℕ}
    (hMg : Mg ≤ M) :
    2 * ((Mg : ℝ) + 1) * A ^ (Mg + 1) * W ^ (K * (Mg + 1))
      ≤ 2 * ((M : ℝ) + 1) * A ^ (M + 1) * W ^ (K * (M + 1)) := by
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hW0 : (0 : ℝ) ≤ W := by linarith
  have hMgR : (Mg : ℝ) ≤ M := Nat.cast_le.mpr hMg
  exact mul_le_mul (mul_le_mul (by linarith) (pow_le_pow_right₀ hA (by omega))
      (pow_nonneg hA0 _) (by linarith))
    (pow_le_pow_right₀ hW (Nat.mul_le_mul_left K (by omega))) (pow_nonneg hW0 _)
    (mul_nonneg (by linarith) (pow_nonneg hA0 _))

/-- **The accumulated loss of the banded stopping time, on the real line.**  All of the analytic
content of `bandStoppingLoss_le_totalLoss` below, which only coerces it into `ℝ≥0∞`.  The step's
factor is linear in the grid length and fits into `gridLoss` over `≤ ssfGridLen δ + 1` rounds; the
pass's factor is *quadratic*, and what pays for it is that the number of rounds is at most `N + 1`
with `N` fixed before `δ`. -/
private theorem bandStoppingLoss_le_gridLoss_mul_scaleGapLoss {A : ℝ} (hA : 1 ≤ A) (K N : ℕ) :
    ∃ (Cl δ₀ : NNReal) (Kt : ℕ), 1 ≤ Cl ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ → ∀ (Mg L : ℕ), Mg ≤ ssfGridLen δ → L ≤ N + 1 →
        L ≤ Mg + 1 →
        (2 * ((Mg : ℝ) + 1) * (A ^ (Mg + 1) * (1 - Real.log (δ : ℝ)) ^ (K * (Mg + 1)))
            * (1 - Real.log (δ : ℝ)) ^ (2 * ((Mg + 2) * (Mg + 1)))) ^ L
          ≤ gridLoss Cl Kt δ * scaleGapLoss 0 δ := by
  classical
  have hA0 : (0 : ℝ) ≤ A := by linarith
  let Anr : NNReal := Real.toNNReal A
  have hAnr : (Anr : ℝ) = A := Real.coe_toNNReal A hA0
  have hAnr1 : 1 ≤ Anr := by rw [← NNReal.coe_le_coe, NNReal.coe_one, hAnr]; exact hA
  obtain ⟨d1, hd1pos, hd1le1, hthresh⟩ :=
    exists_threshold_hoistedStoppingLoss_le_gridLoss Anr hAnr1 K (A := Anr) hAnr1
  refine ⟨Anr, d1, (K + 3) + (N + 1) * 6, hAnr1, hd1pos, hd1le1, ?_⟩
  intro δ hδ hδd1 Mg L hMg hLN hLMg
  have hδ1 : δ ≤ 1 := hδd1.trans hd1le1
  set W : ℝ := 1 - Real.log (δ : ℝ) with hWdef
  have hW1 : (1 : ℝ) ≤ W := KT.one_le_one_sub_log hδ (by exact_mod_cast hδ1)
  have hW0 : (0 : ℝ) ≤ W := zero_le_one.trans hW1
  set X : ℝ := 2 * ((Mg : ℝ) + 1) * A ^ (Mg + 1) * W ^ (K * (Mg + 1)) with hXdef
  set Y : ℝ := W ^ (2 * ((Mg + 2) * (Mg + 1))) with hYdef
  have hX0 : (0 : ℝ) ≤ X := by
    rw [hXdef]
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hA0 _)) (pow_nonneg hW0 _)
  have hY0 : (0 : ℝ) ≤ Y := by rw [hYdef]; exact pow_nonneg hW0 _
  have hXpow : X ^ L ≤ gridLoss Anr (K + 3) δ := by
    refine (pow_le_pow_left₀ hX0 ?_ L).trans (by simpa [hWdef] using hthresh δ hδ hδd1 L (by omega))
    simpa [hXdef, hAnr] using
      hoistedStoppingLoss_mono_grid (A := A) (W := W) hA hW1 K (M := ssfGridLen δ) hMg
  have hG0 : (0 : ℝ) ≤ gridLoss Anr (K + 3) δ :=
    zero_le_one.trans (one_le_gridLoss Anr hAnr1 _ hδ1)
  have hYpow : Y ^ L ≤ gridLoss 1 ((N + 1) * 6) δ := by
    calc Y ^ L ≤ gridLoss 1 6 δ ^ L :=
          pow_le_pow_left₀ hY0 (by
            simpa [hYdef, hWdef] using polylog_pow_le_gridLoss hδ1 hMg (C := 1) (by norm_num)) L
      _ ≤ gridLoss 1 6 δ ^ (N + 1) :=
          pow_le_pow_right₀ (one_le_gridLoss 1 (by norm_num) 6 hδ1) hLN
      _ = gridLoss 1 ((N + 1) * 6) δ := by simpa [one_pow] using gridLoss_pow 1 6 (N + 1) δ
  have hbracket : 2 * ((Mg : ℝ) + 1) * (A ^ (Mg + 1) * W ^ (K * (Mg + 1))) * Y = X * Y := by
    rw [hXdef]; ring
  rw [hbracket, mul_pow]
  refine le_trans ?_ (le_mul_of_one_le_right
    (zero_le_one.trans (one_le_gridLoss Anr hAnr1 _ hδ1)) (one_le_scaleGapLoss 0 hδ hδ1))
  calc X ^ L * Y ^ L ≤ gridLoss Anr (K + 3) δ * gridLoss 1 ((N + 1) * 6) δ :=
        mul_le_mul hXpow hYpow (pow_nonneg hY0 L) hG0
    _ = _ := by simpa [mul_one] using gridLoss_mul Anr 1 (K + 3) ((N + 1) * 6) δ

/-- **The accumulated loss of the banded stopping time is a `totalLoss`** (blueprint
`lem:bandStoppingLossLeTotalLoss`).

The `ℝ≥0∞` reading of `bandStoppingLoss_le_gridLoss_mul_scaleGapLoss`, which carries all of the
accounting; `totalLoss` is by definition the `ENNReal.ofReal` of the real product bounded there. -/
theorem bandStoppingLoss_le_totalLoss {A : ℝ} (hA : 1 ≤ A) (K N : ℕ) :
    ∃ (Cl δ₀ : NNReal) (Kt : ℕ), 1 ≤ Cl ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal}, 0 < δ → δ ≤ δ₀ → ∀ (Mg L : ℕ), Mg ≤ ssfGridLen δ → L ≤ N + 1 →
        L ≤ Mg + 1 →
        ENNReal.ofReal
            ((2 * ((Mg : ℝ) + 1) * (A ^ (Mg + 1) * (1 - Real.log (δ : ℝ)) ^ (K * (Mg + 1)))
              * (1 - Real.log (δ : ℝ)) ^ (2 * ((Mg + 2) * (Mg + 1)))) ^ L)
          ≤ totalLoss Cl Kt 0 δ := by
  obtain ⟨Cl, d0, Kt, hCl1, hd0pos, hd0le1, hReal⟩ :=
    bandStoppingLoss_le_gridLoss_mul_scaleGapLoss hA K N
  exact ⟨Cl, d0, Kt, hCl1, hd0pos, hd0le1, fun hdpos hdle Mg L hMg hLN hLMg =>
    totalLoss_eq_ofReal .. ▸ ENNReal.ofReal_le_ofReal (hReal hdpos hdle Mg L hMg hLN hLMg)⟩

/-! ### One refinement step followed by one homogenizing pass -/

/-- **Composing a cut loss with a pass loss, weakening the cut factor.**

A step that loses a factor `L` followed by a pass that loses a factor `P` loses `L' * P` for any
`L'` above `L`.  This is the shape both clauses of
`Kakeya.MultiScaleFac.exists_cutKT_pass_data` display their cardinality loss in. -/
private theorem le_mul_mul_of_le_mul_of_le_mul {x y z L L' P : ℝ} (hxy : x ≤ L * y)
    (hyz : y ≤ P * z) (hL : L ≤ L') (hL0 : 0 ≤ L) (hy : 0 ≤ y) :
    x ≤ L' * P * z := -- (extracted by Fuse golfer)
  hxy.trans <| (mul_le_mul hL hyz hy (hL0.trans hL)).trans_eq (mul_assoc _ _ _).symm

/-- **The data of the banded Katz-Tao stopping time: a start state and a step, at one constant**
(blueprint `lem:ktCutPassData`).  Both clauses are read at the same grid-uniform constant `Cv`: the
refinement step accepts an arbitrary input constant and returns the canonical `Cu₀`, and the pass
turns `Cu₀` into `Cv = gridUniformBandConst Cu₀ 2`, so the composite maps `Cv` to `Cv` and can be
iterated.  The quadratic pass factor is displayed separately from the cut's linear one. -/
theorem exists_cutKT_pass_data (hn : Module.finrank ℝ E = 3) :
    ∃ (A : ℝ) (K : ℕ) (Cv δ₀ : NNReal), 1 ≤ A ∧ 1 ≤ Cv ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      (∀ (Mgrid : ℕ), 0 < Mgrid →
        ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ → δ ≤ (16 : NNReal) ^ (-(Mgrid : ℝ)) →
        ∀ (s : Finset ι) (T : ι → Tube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (↑s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        ∃ s' ⊆ s,
          (s.card : ℝ) ≤ (A ^ (Mgrid + 1) * (1 - Real.log (δ : ℝ)) ^ (K * (Mgrid + 1)))
              * (1 - Real.log (δ : ℝ)) ^ (2 * ((Mgrid + 2) * (Mgrid + 1))) * (s'.card : ℝ) ∧
          ∃ (𝒢 : GridUniform s' T Mgrid Cv) (Φ : ℕ → ℕ → ENNReal),
            PairBandOn s' 𝒢 2 Φ Mgrid) ∧
      (∀ (Mgrid : ℕ), 0 < Mgrid → ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 64 →
        ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ → δ ≤ (16 : NNReal) ^ (-(Mgrid : ℝ)) →
        ∀ (t : Finset ι) (T : ι → Tube δ E),
        (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        (↑t : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
        ∀ (𝒢 : GridUniform t T Mgrid Cv) (C : NNReal) (ζ ζ' : ℝ), 0 ≤ ζ → ζ ≤ ε * ζ' →
        ∀ a b : ℕ, a < b → b ≤ Mgrid → IsLongBlock Mgrid ε a b →
        BlockKatzTaoOn t 𝒢.uniformAt C ζ a b →
        t.card ≤ 2 * (passingNodesKT t 𝒢.uniformAt C ε ζ' a b).card →
        ∃ (t' : Finset ι) (𝒢' : GridUniform t' T Mgrid Cv) (c : ℕ) (Φ : ℕ → ℕ → ENNReal),
          t' ⊆ t ∧ a + ⌈ε * ((⌈ε * (Mgrid : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ ≤ c ∧
          c + ⌈ε * ((⌈ε * (Mgrid : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ ≤ b ∧
          (t.card : ℝ) ≤ 2 * ((Mgrid : ℝ) + 1)
              * (A ^ (Mgrid + 1) * (1 - Real.log (δ : ℝ)) ^ (K * (Mgrid + 1)))
              * (1 - Real.log (δ : ℝ)) ^ (2 * ((Mgrid + 2) * (Mgrid + 1))) * (t'.card : ℝ) ∧
          (∀ n ≤ Mgrid, 𝒢'.cover.indexSet n ⊆ 𝒢.cover.indexSet n) ∧
          (∀ n, 𝒢'.cover.tube n = 𝒢.cover.tube n) ∧
          BlockKatzTaoOn t' 𝒢'.uniformAt C ζ' a c ∧
          BlockKatzTaoOn t' 𝒢'.uniformAt C ζ' c b ∧
          PairBandOn t' 𝒢' 2 Φ Mgrid) := by
  classical
  obtain ⟨d0, hd0pos, hd0le1, hpass⟩ := exists_homogenizing_pass_gridUniform (E := E) hn
  obtain ⟨A0, K0, Cvcut, hA0, hCvcut, hcut⟩ := exists_refined_cutKT_hoisted_in.{u, _} (E := E)
  obtain ⟨A1, K1, Cu1, hA1, hCu1, hgrid⟩ := exists_gridUniform_subfamily_hoisted.{u, _} (E := E)
  refine ⟨max A0 A1, max K0 K1, gridUniformBandConst (E := E) (max Cvcut Cu1) 2, d0,
    le_max_of_le_left hA0, one_le_pow₀ one_le_bandRestrictConst, hd0pos, hd0le1, ?start, ?step⟩
  · intro Mgrid hMg ι δ hδ hδd0 hδN s T hball hED
    have hW1 : (1 : ℝ) ≤ 1 - Real.log (δ : ℝ) :=
      KT.one_le_one_sub_log hδ (by exact_mod_cast hδd0.trans hd0le1)
    have hWnn : (0 : ℝ) ≤ 1 - Real.log (δ : ℝ) := zero_le_one.trans hW1
    have hA1nn : (0 : ℝ) ≤ A1 := zero_le_one.trans hA1
    have hAnn : (0 : ℝ) ≤ max A0 A1 := (zero_le_one.trans hA0).trans (le_max_left A0 A1)
    obtain ⟨s1, hs1s, hloss1, ⟨𝒢1⟩, _, _⟩ :=
      hgrid Mgrid hMg hδ hδN s s T (Finset.Subset.refl s) hball hED
    let 𝒢1m : GridUniform s1 T Mgrid (max Cvcut Cu1) := 𝒢1.mono (le_max_right Cvcut Cu1)
    have hball1 : ∀ i ∈ s1, (T i).carrier ⊆ Metric.closedBall (0 : E) 1 :=
      fun i hi => hball i (hs1s hi)
    have hED1 : (s1 : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
      :=
      Set.Pairwise.mono (Finset.coe_subset.mpr hs1s) hED
    obtain ⟨s2, hs2s1, hloss2, 𝒢2, Φ2, hassign2, htube2, hidx2, hband2⟩ :=
      hpass (δ := δ) hδ hδd0 Mgrid (max Cvcut Cu1) s1 T hball1 hED1 𝒢1m
    refine ⟨s2, subset_trans hs2s1 hs1s, ?_, ⟨𝒢2, Φ2, ?_⟩⟩
    · exact le_mul_mul_of_le_mul_of_le_mul hloss1 hloss2
        (mul_le_mul (pow_le_pow_left₀ hA1nn (le_max_right A0 A1) (Mgrid + 1))
          (pow_le_pow_right₀ hW1 (Nat.mul_le_mul_right (Mgrid + 1) (le_max_right K0 K1)))
          (pow_nonneg hWnn _) (pow_nonneg hAnn _))
        (mul_nonneg (pow_nonneg hA1nn _) (pow_nonneg hWnn _)) (Nat.cast_nonneg _)
    · exact hband2
  · intro Mgrid hMg ε hεpos hε64 ι δ hδ hδd0 hδN t T hball hED 𝒢 C ζ ζ' hζ hgap
      a b hab hbN hlong hgood htest
    have hW1 : (1 : ℝ) ≤ 1 - Real.log (δ : ℝ) :=
      KT.one_le_one_sub_log hδ (by exact_mod_cast hδd0.trans hd0le1)
    have hWnn : (0 : ℝ) ≤ 1 - Real.log (δ : ℝ) := zero_le_one.trans hW1
    have hA0nn : (0 : ℝ) ≤ A0 := zero_le_one.trans hA0
    obtain ⟨t1, 𝒢1, c, ht1t, hac, hcb, hloss1, hpar1, htub1, hcoarse1, hfine1⟩ :=
      hcut Mgrid hMg hεpos hε64 hδ hδN t T hball hED _ 𝒢 C ζ ζ' hζ hgap
        a b hab hbN hlong hgood htest
    have hball1 : ∀ i ∈ t1, (T i).carrier ⊆ Metric.closedBall (0 : E) 1 :=
      fun i hi => hball i (ht1t hi)
    have hED1 : (t1 : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
      :=
      Set.Pairwise.mono (Finset.coe_subset.mpr ht1t) hED
    let 𝒢1m : GridUniform t1 T Mgrid (max Cvcut Cu1) := 𝒢1.mono (le_max_left Cvcut Cu1)
    obtain ⟨t2, ht2t1, hloss2, 𝒢2, Φ2, hassign2, htube2, hidx2, hband2⟩ :=
      hpass (δ := δ) hδ hδd0 Mgrid (max Cvcut Cu1) t1 T hball1 hED1 𝒢1m
    have hIdx : ∀ n (hn : n ≤ Mgrid), 𝒢2.cover.indexSet n ⊆ 𝒢1.cover.indexSet n := by
      intro n hn x hx
      rw [hidx2 n hn] at hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact 𝒢1.cover.assign_mem n hn i (ht2t1 hi)
    have hpar2 : ∀ n (hn : n ≤ Mgrid), (𝒢2.uniformAt n hn).parent ⊆ (𝒢1.uniformAt n hn).parent := by
      intro n hn
      rw [𝒢2.parent_eq n hn, 𝒢1.parent_eq n hn]
      exact hIdx n hn
    have htube2' : ∀ n, 𝒢2.cover.tube n = 𝒢1.cover.tube n := htube2
    have htub2_all : ∀ n (hn : n ≤ Mgrid), ∀ j ∈ (𝒢2.uniformAt n hn).parent,
        (𝒢2.uniformAt n hn).parentTube j = (𝒢1.uniformAt n hn).parentTube j := by
      intro n hn j hj
      rw [𝒢2.parent_eq n hn] at hj
      rw [𝒢2.tube_eq n hn j hj, 𝒢1.tube_eq n hn j (hIdx n hn hj), htube2' n]
    refine ⟨t2, 𝒢2, c, Φ2, subset_trans ht2t1 ht1t, hac, hcb, ?loss, ?idx, ?tub, ?coarse, ?fine,
      ?band⟩
    · refine le_mul_mul_of_le_mul_of_le_mul hloss1 hloss2 ?_
        (mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hA0nn _) (pow_nonneg hWnn _)))
        (Nat.cast_nonneg _)
      simpa only [mul_assoc] using refinedCut_loss_le_budget_gen hA0 (le_max_left A0 A1) hW1
        (Nat.mul_le_mul_right (Mgrid + 1) (le_max_left K0 K1)) Mgrid
    · intro n hn
      exact subset_trans (hIdx n hn) (hpar1 n hn)
    · exact fun n => (htube2' n).trans (htub1 n)
    · exact BlockKatzTaoOn.of_subcover hpar2 htub2_all ht2t1 hcoarse1
    · exact BlockKatzTaoOn.of_subcover hpar2 htub2_all ht2t1 hfine1
    · exact hband2

/-! ### The banded stopping time -/

/-- **The banded Katz-Tao stopping time, hoisted and split** (blueprint
`lem:ktMaximalCutsHoistedBlocksCore`).  `exists_maximal_cutsKT_hoisted_core` with a homogenizing
pass performed at the end of every round, so that the terminal family carries the paired band on the
very system the block bound and the terminal alternative speak about.  Added: the dimension
hypothesis `hn`, a threshold `δ₀`, and the pass factor in the displayed per-round loss. -/
theorem exists_maximal_cutsKT_hoisted_blocks_core (hn : Module.finrank ℝ E = 3) :
    ∃ (A : ℝ) (K : ℕ) (Cv C₁ δ₀ : NNReal), 1 ≤ A ∧ 1 ≤ Cv ∧ 1 ≤ C₁ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (N : ℕ), 4096 ≤ N → ∀ {ε : ℝ}, ε = 1 / Real.sqrt (N : ℝ) →
      ∀ (Mgrid : ℕ), 16 ≤ Mgrid →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ → δ ≤ (16 : NNReal) ^ (-(Mgrid : ℝ)) →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (↑s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      ∀ η : ℕ → ℝ, (∀ k, k ≤ N → 0 ≤ η k) → (∀ k l, k ≤ l → l ≤ N → η k ≤ η l) →
        (∀ k, k < N → η k ≤ ε * η (k + 1)) →
      Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody)
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η 0)) →
      ∃ (S : Finset ℕ) (m : ℕ) (tL : Finset ι) (𝒢L : GridUniform tL T Mgrid Cv)
        (Φ : ℕ → ℕ → ENNReal),
        m < N ∧ tL ⊆ s ∧
        (s.card : ℝ)
            ≤ (2 * ((Mgrid : ℝ) + 1)
                * (A ^ (Mgrid + 1) * (1 - Real.log (δ : ℝ)) ^ (K * (Mgrid + 1)))
                * (1 - Real.log (δ : ℝ)) ^ (2 * ((Mgrid + 2) * (Mgrid + 1)))) ^ (m + 1)
              * (tL.card : ℝ) ∧
        0 ∈ S ∧ Mgrid ∈ S ∧ S ⊆ Finset.range (Mgrid + 1) ∧ S.card = m + 2 ∧
        PairBandOn tL 𝒢L C₁ Φ Mgrid ∧
        ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
          BlockKatzTaoOn tL 𝒢L.uniformAt C₁ (η m) a b ∧
            (¬ IsLongBlock Mgrid ε a b ∨
              ¬ (tL.card
                ≤ 2 * (passingNodesKT tL 𝒢L.uniformAt C₁ ε (η (m + 1)) a b).card)) := by
  classical
  obtain ⟨A, K, Cv, d0, hA, hCv, hd0pos, hd0le1, hstart, hstep⟩ :=
    exists_cutKT_pass_data.{u, _} (E := E) hn
  obtain ⟨Cblock, hCblock1, hzero⟩ := exists_blockKatzTao_zero_right.{u, _} (E := E) Cv hCv
  set C₁ : NNReal := max Cblock 2
  refine ⟨A, K, Cv, C₁, d0, hA, hCv, hCblock1.trans (le_max_left Cblock 2), hd0pos, hd0le1, ?_⟩
  intro N hN eps heps Mgrid hMgrid iota delta hdelta hδd0 hdeltaN s T hball hED eta hetapos
    hetamono hetagap hDens
  have hMpos : 0 < Mgrid := by omega
  have hMgR : (0 : ℝ) ≤ (Mgrid : ℝ) := Nat.cast_nonneg _
  have hfree : (1 : ℝ) ≤ 2 * ((Mgrid : ℝ) + 1) := by linarith
  have hepspos : 0 < eps := eps_pos_of_eq_one_div_sqrt (by omega : 16 ≤ N) heps
  have heps64 : eps ≤ 1 / 64 := eps_le_one_div_64_of_eq_one_div_sqrt hN heps
  have heps1 : eps ≤ 1 := by linarith
  have hepssq : eps ^ 2 * (N : ℝ) = 1 :=
    eps_sq_mul_eq_one_of_eq_one_div_sqrt (by omega : 0 < N) heps
  have hdelta2 : 2 * delta ≤ 1 := by
    have hM16 : (16 : ℝ) ≤ (Mgrid : ℝ) := by exact_mod_cast hMgrid
    have hc := NNReal.coe_le_coe.mpr (hdeltaN.trans
      (NNReal.rpow_le_rpow_of_exponent_le
        (by rw [← NNReal.coe_le_coe, NNReal.coe_one, NNReal.coe_ofNat]; norm_num)
        (by linarith : -(Mgrid : ℝ) ≤ -(1 : ℝ))))
    rw [NNReal.coe_rpow, NNReal.coe_ofNat, Real.rpow_neg_one] at hc
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_one, NNReal.coe_ofNat]
    linarith
  have hdelta1 : delta ≤ 1 :=
    le_trans (le_mul_of_one_le_left zero_le one_le_two) hdelta2
  have hW1 : (1 : ℝ) ≤ 1 - Real.log (delta : ℝ) :=
    KT.one_le_one_sub_log hdelta (by exact_mod_cast hdelta1)
  have hA1pow : (1 : ℝ) ≤ A ^ (Mgrid + 1) := one_le_pow₀ hA
  have hWpow1 : (1 : ℝ) ≤ (1 - Real.log (delta : ℝ)) ^ (K * (Mgrid + 1)) := one_le_pow₀ hW1
  have hWpow2 : (1 : ℝ) ≤ (1 - Real.log (delta : ℝ)) ^ (2 * ((Mgrid + 2) * (Mgrid + 1))) :=
    one_le_pow₀ hW1
  have hPi0 : (0 : ℝ) ≤ (A ^ (Mgrid + 1) * (1 - Real.log (delta : ℝ)) ^ (K * (Mgrid + 1)))
      * (1 - Real.log (delta : ℝ)) ^ (2 * ((Mgrid + 2) * (Mgrid + 1))) :=
    zero_le_one.trans
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA1pow hWpow1) hWpow2)
  set P : ℝ := 2 * ((Mgrid : ℝ) + 1) * (A ^ (Mgrid + 1)
      * (1 - Real.log (delta : ℝ)) ^ (K * (Mgrid + 1)))
      * (1 - Real.log (delta : ℝ)) ^ (2 * ((Mgrid + 2) * (Mgrid + 1))) with hPdef
  have hP1 : (1 : ℝ) ≤ P := by
    rw [hPdef]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hfree (one_le_mul_of_one_le_of_one_le hA1pow hWpow1)) hWpow2
  have hPiG : (A ^ (Mgrid + 1) * (1 - Real.log (delta : ℝ)) ^ (K * (Mgrid + 1)))
      * (1 - Real.log (delta : ℝ)) ^ (2 * ((Mgrid + 2) * (Mgrid + 1))) ≤ P := by
    rw [hPdef, mul_assoc (2 * ((Mgrid : ℝ) + 1))]
    exact le_mul_of_one_le_left hPi0 hfree
  have hw : 0 < ⌈eps * ((⌈eps * (Mgrid : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ := KT.stoppingMargin_pos hepspos hMpos
  have hwM : ⌈eps * ((⌈eps * (Mgrid : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ ≤ Mgrid :=
    KT.stoppingMargin_le hepspos heps1 Mgrid
  have hwN : Mgrid ≤ ⌈eps * ((⌈eps * (Mgrid : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ * N :=
    KT.le_mul_stoppingMargin hepspos hepssq Mgrid
  obtain ⟨s0, hs0s, hcard0, ⟨calG0, Φ0, hband0⟩⟩ :=
    hstart Mgrid hMpos hdelta hδd0 hdeltaN s T hball hED
  have hDens0 : Kakeya.maxDensity s0 (fibreBodies T delta)
      ≤ ENNReal.ofReal ((delta : ℝ) ^ (-eta 0)) := by
    rw [fibreBodies_self]
    exact le_trans (Kakeya.maxDensity_mono _ hs0s) hDens
  have hgood0 : BlockKatzTaoOn s0 calG0.uniformAt C₁ (eta 0) 0 Mgrid :=
    BlockKatzTaoOn.mono hdelta hdelta1 (le_max_left Cblock 2) (hetapos 0 (Nat.zero_le N))
      (le_refl (eta 0)) (Nat.zero_le Mgrid)
      (hzero Mgrid hMpos hdelta hdelta1 hdelta2 s0 T calG0.uniformAt (eta 0)
        (hetapos 0 (Nat.zero_le N)) hDens0)
  have hband0' : PairBandOn s0 calG0 C₁ Φ0 Mgrid := PairBandOn.mono (le_max_right Cblock 2) hband0
  have hcutfield : ∀ (t : Finset iota) (calG : GridUniform t T Mgrid Cv), t ⊆ s0 →
      ∀ zeta zeta' : ℝ, 0 ≤ zeta → zeta ≤ eps * zeta' →
      ∀ a b : ℕ, a < b → b ≤ Mgrid → IsLongBlock Mgrid eps a b →
      BlockKatzTaoOn t calG.uniformAt C₁ zeta a b →
      t.card ≤ 2 * (passingNodesKT t calG.uniformAt C₁ eps zeta' a b).card →
      ∃ (t' : Finset iota) (calG' : GridUniform t' T Mgrid Cv) (c : ℕ) (Φ : ℕ → ℕ → ENNReal),
        t' ⊆ t ∧ a + ⌈eps * ((⌈eps * (Mgrid : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ ≤ c ∧
        c + ⌈eps * ((⌈eps * (Mgrid : ℝ)⌉₊ : ℕ) : ℝ)⌉₊ ≤ b ∧
        (t.card : ℝ) ≤ P * (t'.card : ℝ) ∧
        (∀ n ≤ Mgrid, calG'.cover.indexSet n ⊆ calG.cover.indexSet n) ∧
        (∀ n, calG'.cover.tube n = calG.cover.tube n) ∧
        BlockKatzTaoOn t' calG'.uniformAt C₁ zeta' a c ∧
        BlockKatzTaoOn t' calG'.uniformAt C₁ zeta' c b ∧
        PairBandOn t' calG' C₁ Φ Mgrid := by
    intro t calG hts0 zeta zeta' hzeta hgap a b hab hbM hlong hg htest
    obtain ⟨t', calG', c, Φ, ht't, hac, hcb, hcard', hpar, htub, hcoarse, hfine, hband⟩ :=
      hstep Mgrid hMpos hepspos heps64 hdelta hδd0 hdeltaN t T
        (fun i hi => hball i (hs0s (hts0 hi)))
        (Set.Pairwise.mono (Finset.coe_subset.mpr (Finset.Subset.trans hts0 hs0s)) hED)
        calG C₁ zeta zeta' hzeta hgap a b hab hbM hlong hg htest
    refine ⟨t', calG', c, Φ, ht't, hac, hcb, ?_, hpar, htub, hcoarse, hfine,
      PairBandOn.mono (le_max_right Cblock 2) hband⟩
    rw [hPdef]
    exact hcard'
  obtain ⟨S, m, tL, calGL, Φ, hm, htLs0, hcardm, -, -, h0, hMmem, hsub, hScard, hbandL,
    hAll⟩ :=
    exists_hoisted_cutsKT_run_band N Mgrid _ hw hwM hwN eta hetapos hetamono hetagap
      hdelta hdelta1 s0 T Cv C₁ C₁ P hP1 calG0 hgood0 Φ0 hband0' hcutfield
  refine ⟨S, m, tL, calGL, Φ, hm, Finset.Subset.trans htLs0 hs0s, ?_, h0, hMmem, hsub, hScard,
    hbandL, hAll⟩
  exact KT.hoisted_card_accum (zero_le_one.trans hP1) hPi0 hPiG (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) m hcard0 hcardm

/-! ### The clause the amended dichotomy consumes -/

open scoped Classical in
/-- **The block invariant, the terminal alternative and the homogenization band of the ported
stopping time** (blueprint `lem:ktMaximalCutsHoistedBlocks`).  Stated separately from
`Kakeya.StickyKakeya.exists_maximal_cutsKT_hoisted` because it names the grid-uniform system
returned there: for every adjacent pair of the cut set the block bound holds at the exponent `η m`,
and the pair is short or fails the split test; the terminal family carries the paired band. -/
theorem exists_maximal_cutsKT_hoisted_blocks (hn : Module.finrank ℝ E = 3) :
    ∃ (Cv C₁ : NNReal), 1 ≤ Cv ∧ 1 ≤ C₁ ∧
      ∀ (N : ℕ), 4096 ≤ N → ∃ (Cl δ₀ : NNReal) (Kt cg : ℕ), 1 ≤ Cl ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ε : ℝ}, ε = 1 / Real.sqrt (N : ℝ) →
      ∀ (Mgrid : ℕ), 16 ≤ Mgrid → N ≤ Mgrid →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ → δ ≤ (16 : NNReal) ^ (-(Mgrid : ℝ)) →
      Mgrid ≤ ssfGridLen δ →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (↑s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      ∀ η : ℕ → ℝ, (∀ k, k ≤ N → 0 ≤ η k) → (∀ k l, k ≤ l → l ≤ N → η k ≤ η l) →
        (∀ k, k < N → η k ≤ ε * η (k + 1)) →
      Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody)
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η 0)) →
      ∃ (S : Finset ℕ) (m : ℕ) (tL : Finset ι) (𝒢L : GridUniform tL T Mgrid Cv)
        (Φ : ℕ → ℕ → ENNReal),
        m < N ∧ tL ⊆ s ∧
        (s.card : ENNReal) ≤ totalLoss Cl Kt cg δ * (tL.card : ENNReal) ∧
        0 ∈ S ∧ Mgrid ∈ S ∧ S ⊆ Finset.range (Mgrid + 1) ∧
        (∀ a ≤ Mgrid, ∀ c ≤ Mgrid, ∀ j ∈ 𝒢L.cover.indexSet a,
          Φ a c ≤ Kakeya.maxDensity
                ((coverClass tL (𝒢L.cover.assign a) j).image (𝒢L.cover.assign c))
                (fun j' => (𝒢L.cover.tube c j').toConvexSpaceBody) ∧
            Kakeya.maxDensity
                ((coverClass tL (𝒢L.cover.assign a) j).image (𝒢L.cover.assign c))
                (fun j' => (𝒢L.cover.tube c j').toConvexSpaceBody)
              ≤ (C₁ : ENNReal) * Φ a c) ∧
        ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
          BlockKatzTaoOn tL 𝒢L.uniformAt C₁ (η m) a b ∧
            (¬ IsLongBlock Mgrid ε a b ∨
              ¬ (tL.card
                ≤ 2 * (passingNodesKT tL 𝒢L.uniformAt C₁ ε (η (m + 1)) a b).card)) := by
  classical
  obtain ⟨A, K, Cv, C1, d0c, hA, hCv, hC1, hd0cpos, hd0cle1, hcore⟩ :=
    exists_maximal_cutsKT_hoisted_blocks_core.{u, _} (E := E) hn
  refine ⟨Cv, C1, hCv, hC1, fun N hN => ?_⟩
  obtain ⟨Cl, d1, Kt, hCl1, hd1pos, hd1le1, hloss⟩ :=
    bandStoppingLoss_le_totalLoss (A := A) hA K N
  refine ⟨Cl, min d0c d1, Kt, 0, hCl1, lt_min hd0cpos hd1pos,
    (min_le_left _ _).trans hd0cle1, ?_⟩
  intro eps heps Mgrid hM16 hNM iota delta hdpos hdd0 hd16 hMssf s T hball hED
    eta hetapos hetamono hetagap hDens
  obtain ⟨S, m, tL, calG, Phi, hm, htLs, hcard, h0, hMmem, hsub, hScard, hband, hAll⟩ :=
    hcore N hN heps Mgrid hM16 hdpos (hdd0.trans (min_le_left _ _)) hd16 s T hball hED eta hetapos
      hetamono hetagap hDens
  exact ⟨S, m, tL, calG, Phi, hm, htLs, natCast_le_mul_natCast_of_ofReal_le
    (hloss hdpos (hdd0.trans (min_le_right _ _)) Mgrid (m + 1) hMssf (by omega) (by omega)) hcard,
    h0, hMmem, hsub, hband, hAll⟩

/-! ### The threshold the accumulated loss is absorbed at -/

/-- **The threshold form of the quadratic accumulated loss**, a consumer-facing restatement of
`Kakeya.StickyKakeya.selfBandStoppingLoss_le_gridLoss` (blueprint
`lem:selfBandStoppingLossLeGridLoss`).  Below a threshold chosen before `δ` and depending only on
the per-level base `A1`, the per-round loss of `exists_maximal_cuts_banded_hoisted_selfBand` raised
to the number of rounds is a `gridLoss` whose base `A` is free. -/
theorem exists_threshold_selfBandStoppingLoss_le_gridLoss {A1 : ℝ} (hA1 : 1 ≤ A1) (K N : ℕ)
    {A : NNReal} (hA : 1 ≤ A) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : NNReal, 0 < δ → δ ≤ δ₀ →
        ∀ Mg L : ℕ, Mg ≤ ssfGridLen δ → L ≤ N + 1 → L ≤ Mg + 1 →
          (2 * ((Mg : ℝ) + 1) * A1 ^ (Mg + 1)
              * (1 - Real.log (δ : ℝ)) ^ (K * ((Mg + 2) * (Mg + 1)))) ^ L
            ≤ gridLoss A (3 + (N + 1) * (3 * K)) δ := by
  classical
  let Anr : NNReal := Real.toNNReal A1
  have hAnr : (Anr : ℝ) = A1 := Real.coe_toNNReal A1 (by linarith : 0 ≤ A1)
  have hAnr1 : 1 ≤ Anr := by
    exact_mod_cast (by simpa [hAnr] using hA1 : 1 ≤ (Anr : ℝ))
  obtain ⟨d1, hd1pos, hd1le1, hthresh⟩ :=
    exists_threshold_hoistedStoppingLoss_le_gridLoss Anr hAnr1 0 (A := (1 : NNReal)) le_rfl
  refine ⟨d1, hd1pos, hd1le1, ?_⟩
  intro δ hδ hδd1 Mg L hMg hLN hLMg
  have hδ1 : δ ≤ 1 := le_trans hδd1 hd1le1
  set W : ℝ := 1 - Real.log (δ : ℝ) with hWdef
  have hW1 : (1 : ℝ) ≤ W := by
    dsimp [W]
    have hlog : Real.log (δ : ℝ) ≤ 0 :=
      Real.log_nonpos (by positivity) (by exact_mod_cast hδ1)
    linarith
  have hW0 : (0 : ℝ) ≤ W := by linarith
  have hA10 : (0 : ℝ) ≤ A1 := by linarith
  set X : ℝ := 2 * ((Mg : ℝ) + 1) * A1 ^ (Mg + 1) with hXdef
  set Y : ℝ := W ^ (K * ((Mg + 2) * (Mg + 1))) with hYdef
  have hX0 : (0 : ℝ) ≤ X := by
    dsimp [X]
    exact mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * ((Mg : ℝ) + 1)) (pow_nonneg hA10 _)
  have hY0 : (0 : ℝ) ≤ Y := by
    dsimp [Y]
    exact pow_nonneg hW0 _
  have hbracket :
      (2 * ((Mg : ℝ) + 1) * A1 ^ (Mg + 1) * W ^ (K * ((Mg + 2) * (Mg + 1)))) = X * Y := by
    unfold X Y
    ring
  have hXs : L ≤ ssfGridLen δ + 1 := by omega
  have hxbase_le : X ≤ 2 * ((ssfGridLen δ : ℝ) + 1) * (Anr : ℝ) ^ (ssfGridLen δ + 1)
      * W ^ (0 * (ssfGridLen δ + 1)) := by
    have hbase := hoistedStoppingLoss_mono_grid (A := A1) (W := W) hA1 hW1 0 (M := ssfGridLen δ)
      hMg
    simpa [hXdef, hAnr] using hbase
  have hxpow' : X ^ L ≤ (2 * ((ssfGridLen δ : ℝ) + 1) * (Anr : ℝ) ^ (ssfGridLen δ + 1)
      * W ^ (0 * (ssfGridLen δ + 1))) ^ L := by
    exact pow_le_pow_left₀ hX0 hxbase_le L
  have hXpow : X ^ L ≤ gridLoss 1 3 δ := by
    have hthr := hthresh δ hδ hδd1 L hXs
    simpa [hWdef] using (le_trans hxpow' hthr)
  have hYpow : Y ^ L ≤ gridLoss 1 ((N + 1) * (3 * K)) δ := by
    simpa [hYdef, hWdef] using (polylog_pow_quad_pow_le_gridLoss hδ1 hMg hLN K)
  have hG1 : (1 : ℝ) ≤ gridLoss 1 3 δ := one_le_gridLoss 1 (by norm_num) 3 hδ1
  have hG0 : (0 : ℝ) ≤ gridLoss 1 3 δ := by linarith
  have hmain : X ^ L * Y ^ L ≤ gridLoss 1 (3 + (N + 1) * (3 * K)) δ := by
    calc
      X ^ L * Y ^ L ≤ gridLoss 1 3 δ * gridLoss 1 ((N + 1) * (3 * K)) δ :=
        mul_le_mul hXpow hYpow (pow_nonneg hY0 L) hG0
      _ = gridLoss 1 (3 + (N + 1) * (3 * K)) δ := by
        simpa [mul_one] using gridLoss_mul 1 1 3 ((N + 1) * (3 * K)) δ
  have hbaseA : gridLoss 1 (3 + (N + 1) * (3 * K)) δ ≤ gridLoss A (3 + (N + 1) * (3 * K)) δ :=
    gridLoss_mono (A := (1 : NNReal)) (A' := A) (by norm_num) hA
      (K := 3 + (N + 1) * (3 * K)) (K' := 3 + (N + 1) * (3 * K)) le_rfl hδ1
  rw [hbracket, mul_pow]
  exact le_trans hmain hbaseA

end MultiScaleFac

end Kakeya

end
