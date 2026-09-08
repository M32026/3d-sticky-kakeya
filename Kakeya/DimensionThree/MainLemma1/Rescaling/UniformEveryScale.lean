/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Uniform.GridNet
public import Kakeya.Uniform
public import Kakeya.Factoring.FlatPrisms
public import Kakeya.DimensionThree.MainLemma1.Cases

/-!
# One-sided uniformity at every scale, at an absolute constant

This file discharges clause (iii) of `Kakeya.ml1Boot.exists_fineNormalization_lower`: the
uniformity of the normalized fine family on the `ssf` grid of its own scale.

## The obstruction that is dissolved here

The docstring of `Kakeya.ml1Boot.exists_fineNormalization_lower` records three obstructions on two
routes to that clause, and the last of them was said not to dissolve by writing more Lean:
re-gridding a *transported* source hierarchy runs out of source levels, and the blueprint's
intended repair `lem:uniformEveryScale` carries a loss `δ ^ (-o(1))` that cannot be absorbed into a
constant fixed before the scale.

Both routes are unnecessary.  The clause is read at `Kakeya.IsFlatPrismUniform`, GWZ Definition 2.2
**minus** `le_card_shadeClass` and `branchingN_le`, over `Kakeya.IsFlatPrismUniformTubeSet`, GWZ
Definition 2.1 **minus** `Tube.UniformTubeSet.le_card_class`.  Every surviving clause is either
free data or an *upper* bound:

* `cover` is free data — a nested system of node tubes;
* `branchingN` and `localN` are free data, appearing only on the large side of upper bounds, so
  taking both to be `#u'` makes `card_class_le`, `card_shadeClass_le` and `le_branchingN` vacuous
  at any constant `≥ 1`;
* `tube_injOn` is an injectivity requirement on the node indexing;
* `boundedOverlap` is the only geometric content, and it is a purely metric packing statement
  about a *net* of node tubes, with an absolute constant.

The deleted clauses are exactly the ones that would force a genuine regularization of the family —
a lower bound on a class size is destroyed by refinement, and restoring it is what costs GWZ its
`exp(O((log log 1/δ)²))`.  With them gone, the hierarchy can simply be **built directly on the
output family**, with no refinement, no transport, and no `δ`-dependence in the constant at all.

## What the construction is

`Kakeya.exists_initial_gridCoverSystem` (`Kakeya/MultiScaleFac/Clump.lean`) already builds exactly
such a hierarchy — nodes drawn from `Tube.grid_net_tight`, assignment by a single downward
recursion — with the absolute overlap constant `Tube.overlapConstBOTight`.  Its one obstacle here
is its smallness hypothesis `δ ≤ 16 ^ (-N)`, which the `ssf` grid length does **not** supply:
`Tube.ssfGridLen dt = ⌈log log (1/dt)⌉₊` fails `dt ≤ 16 ^ (-N)` on genuine ranges of `dt`, e.g. at
`dt = e ^ (-3)`, where `N = 2` and `16 ^ (-2) = 1/256 < dt`.

But that hypothesis is used *only* to know that consecutive grid scales differ by a factor `2`, and
**the factor `2` the `ssf` grid does supply unconditionally**: `N ⌈log L⌉₊ ≤ log L + 1 ≤ L` for
`L = log (1/dt) ≥ 1` and `N = 0` below, so `dt ≤ 2 ^ (-N)` always
(`Kakeya.ml1Boot.ssfGridLen_rpow_le`).  `Kakeya.ml1Boot.exists_gridCoverSystem_of_ratio` is
therefore that construction with the hypothesis weakened to the ratio bound, and
`Kakeya.ml1Boot.nonempty_isFlatPrismUniform_ssf` is the resulting one-sided uniformity, at
`Tube.overlapConstBOTight 3` — an absolute constant, quantified before everything.

The subpolynomial loss of `lem:uniformEveryScale` is not paid late; it is **not paid at all**,
because it belongs to the two-sided reading and the consumer asks only for the one-sided one.
-/

@[expose] public section

open MeasureTheory

namespace Kakeya
namespace ml1Boot

open scoped NNReal
open _root_.Tube

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

variable {ι : Type*}


/-- The node at one scale of the downward recursion.  Copied, with the smallness hypothesis
weakened from `δ ≤ 16 ^ (-N)` to the ratio bound it is used through, from the private
`Kakeya.GridCoverNode` of `Kakeya/MultiScaleFac/Clump.lean`. -/
structure UesNode {δ : NNReal} {N k : ℕ} (t : Finset ι) (T : ι → Tube δ E) (i : ι)
    (Gk : (k : ℕ) → Finset (Tube (gridScale δ N k) E)) where
  tube : Tube (gridScale δ N k) E
  mem_ball : tube.midpoint ∈ Metric.closedBall (0 : E) 3
  mem_net : (k < N) → tube ∈ Gk k
  contains : i ∈ t → (T i).toConvexSpaceBody ≤ tube.toConvexSpaceBody

/-- The downward-recursive node assignment. -/
noncomputable def uesNodes {δ : NNReal} {N : ℕ}
    (hN : 0 < N)
    (hsep2 : ∀ k, k < N → 2 * ((gridScale δ N (k + 1) : NNReal) : ℝ) ≤ (gridScale δ N k : ℝ))
    (t : Finset ι) (T : ι → Tube δ E)
    (hmid : ∀ (i : ι), i ∈ t → (T i).midpoint ∈ Metric.closedBall (0 : E) 3)
    (i₀ : ι) (hi₀ : i₀ ∈ t)
    (Gk : (k : ℕ) → Finset (Tube (gridScale δ N k) E))
    (hGmid : (k : ℕ) → (hk : k ≤ N) → ∀ W ∈ Gk k, W.midpoint ∈ Metric.closedBall (0 : E) 3)
    (hGcover : (k : ℕ) → (hk : k < N) → ∀ {σ : NNReal} (U : Tube σ E),
      2 * (σ : ℝ) ≤ (gridScale δ N k : ℝ) →
      U.midpoint ∈ Metric.closedBall (0 : E) 3 →
      ∃ W ∈ Gk k, U.toConvexSpaceBody ≤ W.toConvexSpaceBody) :
    (k : ℕ) → (hk : k ≤ N) → (i : ι) → UesNode (k := k) (Gk := Gk) t T i
  | k, hk, i => by
      by_cases hk_eq : k = N
      · subst k
        by_cases hi : i ∈ t
        · exact ⟨(T i).rescale _, hmid i hi, fun hlt => absurd hlt (lt_irrefl N),
            fun _ => by rw [gridScale_self δ hN, Tube.toConvexSpaceBody_rescale_self]⟩
        · exact ⟨(T i₀).rescale _, hmid i₀ hi₀, fun hlt => absurd hlt (lt_irrefl N),
            fun h => absurd h hi⟩
      · have hkN : k < N := by omega
        let fine := uesNodes hN hsep2 t T hmid i₀ hi₀ Gk hGmid hGcover (k + 1)
          (Nat.succ_le_of_lt hkN) i
        have hspec := (hGcover k hkN fine.tube (hsep2 k hkN) fine.mem_ball).choose_spec
        exact ⟨_, hGmid k hk _ hspec.1, fun _ => hspec.1,
          fun hi => (fine.contains hi).trans hspec.2⟩
  termination_by k => N - k
  decreasing_by omega

/-- **The nested cover system at a grid that merely halves.**

This is `Kakeya.exists_initial_gridCoverSystem` (`Kakeya/MultiScaleFac/Clump.lean`) with its
smallness hypothesis `δ ≤ 16 ^ (-N)` replaced by the *only* consequence of it that the proof uses:
that consecutive grid scales differ by a factor `2`.  The weakening matters because the `ssf` grid
length `Tube.ssfGridLen δ` supplies the factor `2` unconditionally
(`Kakeya.ml1Boot.two_mul_ssfGrid_succ_le`) but not the factor `16`. -/
theorem exists_gridCoverSystem_of_ratio {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N : ℕ}
    (hN : 0 < N)
    (hsep2 : ∀ k, k < N → 2 * ((gridScale δ N (k + 1) : NNReal) : ℝ) ≤ (gridScale δ N k : ℝ))
    (t : Finset ι) (T : ι → Tube δ E)
    (hball : ∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hT_inj : Set.InjOn (fun i => (T i).carrier) (t : Set ι)) :
    ∃ 𝒞 : GridCoverSystem t T N,
      ∀ k ≤ N,
        Set.InjOn (𝒞.tube k) (𝒞.indexSet k : Set ι) ∧
        ∀ V : Tube (gridScale δ N k) E,
          ((𝒞.indexSet k).filter (fun v => ∃ i ∈ t,
            (T i).toConvexSpaceBody ≤ (𝒞.tube k v).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
              Tube.overlapConstBOTight (Module.finrank ℝ E) := by
  classical
  rcases t.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · exact
      ⟨{ indexSet := fun _ => (∅ : Finset ι),
         assign := fun _ => id,
         tube := fun k v => (T v).rescale (gridScale δ N k),
         assign_mem := fun _ _ i hi => absurd hi (Finset.notMem_empty i),
         le_tube_assign := fun _ _ i hi => absurd hi (Finset.notMem_empty i),
         nested := fun _ _ i hi => absurd hi (Finset.notMem_empty i),
         tube_nested := fun _ _ i hi => absurd hi (Finset.notMem_empty i) }, by simp⟩
  · choose Gk hGnet using fun k : ℕ =>
      Tube.grid_net_tight (E := E) (gridScale_pos hδ N k) (gridScale_le_one hδ1 N k)
    have hGcover : (k : ℕ) → (hk : k < N) → ∀ {σ : NNReal} (U : Tube σ E),
        2 * (σ : ℝ) ≤ (gridScale δ N k : ℝ) →
        U.midpoint ∈ Metric.closedBall (0 : E) 3 →
        ∃ W ∈ Gk k, U.toConvexSpaceBody ≤ W.toConvexSpaceBody := by
      intro k _ σ U h2σ hUmid
      exact ((hGnet k).1 U h2σ hUmid).imp fun _ h => ⟨h.1, h.2.1⟩
    have hGmid : (k : ℕ) → (hk : k ≤ N) → ∀ W ∈ Gk k,
        W.midpoint ∈ Metric.closedBall (0 : E) 3 := fun k _ => (hGnet k).2.2.2
    have hmid : ∀ i ∈ t, (T i).midpoint ∈ Metric.closedBall (0 : E) 3 := fun i hi =>
      Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 3)
        (Tube.midpoint_mem_closedBall_of_subset hδ (T i) (hball i hi))
    let G := uesNodes hN hsep2 t T hmid i₀ hi₀ Gk hGmid hGcover
    let W : (k : ℕ) → ι → Tube (gridScale δ N k) E :=
      fun k v => if hk : k ≤ N then (G k hk v).tube else (T v).rescale (gridScale δ N k)
    let rep : (k : ℕ) → Tube (gridScale δ N k) E → ι := fun k U =>
      if h : ∃ j ∈ t, W k j = U then h.choose else i₀
    have hrep_spec : ∀ k, ∀ i ∈ t, rep k (W k i) ∈ t ∧ W k (rep k (W k i)) = W k i := by
      intro k i hi
      have hprop : ∃ j ∈ t, W k j = W k i := ⟨i, hi, rfl⟩
      simp only [rep, hprop, ↓reduceDIte]
      exact Classical.choose_spec hprop
    have hrep_idem : ∀ k, ∀ i ∈ t, W k (rep k (W k i)) = W k i :=
      fun k i hi => (hrep_spec k i hi).2
    have hW_eq : ∀ k (hk : k ≤ N) (i : ι), W k i = (G k hk i).tube := fun k hk i => dif_pos hk
    have hW_contains : ∀ k (hk : k ≤ N), ∀ i ∈ t,
        (T i).toConvexSpaceBody ≤ (W k i).toConvexSpaceBody :=
      fun k hk i hi => (hW_eq k hk i) ▸ (G k hk i).contains hi
    have hW_step : ∀ k (hk : k < N) (i : ι),
        W k i = (hGcover k hk (G (k + 1) hk i).tube (hsep2 k hk)
          (G (k + 1) hk i).mem_ball).choose := by
      intro k hk i
      simp only [W, dif_pos hk.le, G]
      conv_lhs => rw [uesNodes, dif_neg hk.ne]
    have hW_le_step : ∀ k (hk : k < N) (i : ι),
        (W (k + 1) i).toConvexSpaceBody ≤ (W k i).toConvexSpaceBody := by
      intro k hk i
      rw [hW_step k hk i, hW_eq (k + 1) hk i]
      exact (hGcover k hk (G (k + 1) hk i).tube (hsep2 k hk)
        (G (k + 1) hk i).mem_ball).choose_spec.2
    have choose_congr : ∀ (k : ℕ) (hk : k < N) (U U' : Tube (gridScale δ N (k + 1)) E),
        U = U' → ∀ (h1 : 2 * ((gridScale δ N (k + 1) : NNReal) : ℝ) ≤ (gridScale δ N k : ℝ))
          (h2 : U.midpoint ∈ Metric.closedBall (0 : E) 3)
          (h2' : U'.midpoint ∈ Metric.closedBall (0 : E) 3),
        (hGcover k hk U h1 h2).choose = (hGcover k hk U' h1 h2').choose := by
      rintro k hk U _ rfl _ _ _; rfl
    have step_congr : ∀ k, k < N → ∀ i j : ι, W (k + 1) i = W (k + 1) j → W k i = W k j := by
      intro k hk i j hWstep
      rw [hW_eq (k + 1) hk i, hW_eq (k + 1) hk j] at hWstep
      rw [hW_step k hk i, hW_step k hk j]
      exact choose_congr k hk _ _ hWstep (hsep2 k hk) (G (k + 1) hk i).mem_ball
        (G (k + 1) hk j).mem_ball
    let 𝒞 : GridCoverSystem t T N :=
      { indexSet := fun k => t.image (fun i => rep k (W k i))
        assign := fun k i => rep k (W k i)
        tube := W
        assign_mem := fun _ _ i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
        le_tube_assign := fun k hk i hi => by
          rw [hrep_idem k i hi]; exact hW_contains k hk i hi
        nested := fun k hk i hi j hj hassign =>
          congrArg (rep k) (step_congr k hk i j
            ((hrep_idem (k + 1) i hi).symm.trans
              ((congrArg (W (k + 1)) hassign).trans (hrep_idem (k + 1) j hj))))
        tube_nested := fun k hk i hi => by
          rw [hrep_idem (k + 1) i hi, hrep_idem k i hi]; exact hW_le_step k hk i }
    have hW_mem_net : ∀ k (hklt : k < N) (m : ι), m ∈ t.image (fun i => rep k (W k i)) →
        W k m ∈ Gk k := by
      intro k hklt m hm
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
      rw [hrep_idem k i hi, hW_eq k hklt.le i]
      exact (G k hklt.le i).mem_net hklt
    have hrep_base : ∀ k, ∀ v ∈ t.image (fun i => rep k (W k i)), v = rep k (W k v) := by
      intro k v hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      rw [hrep_idem k i hi]
    have hNice_inj : ∀ k, Set.InjOn (𝒞.tube k) (𝒞.indexSet k : Set ι) :=
      fun k v hv v' hv' htube =>
        (hrep_base k v hv).trans ((congrArg (rep k) htube).trans (hrep_base k v' hv').symm)
    refine ⟨𝒞, fun k hk => ⟨hNice_inj k, ?_⟩⟩
    · by_cases hkeq : k = N
      · subst k
        have hδρ : δ = gridScale δ N N := (gridScale_self δ hN).symm
        intro V
        refine le_trans (Finset.card_le_one.mpr ?_)
          (Nat.mul_pos Nat.zero_lt_two (Nat.pow_pos (Nat.succ_pos _)))
        have hmemt : ∀ v ∈ 𝒞.indexSet N, v ∈ t := fun v hv => by
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv; exact (hrep_spec N i hi).1
        have hcarV : ∀ v ∈ 𝒞.indexSet N, ∀ U : ι,
            (T U).toConvexSpaceBody ≤ (𝒞.tube N v).toConvexSpaceBody →
            (T U).toConvexSpaceBody ≤ V.toConvexSpaceBody → (T v).carrier = V.carrier := by
          intro v hv U hUv hUV
          calc (T v).carrier = (𝒞.tube N v).carrier :=
                Tube.carrier_eq_of_subset' hδρ (T v) (W N v)
                  (SetLike.coe_subset_coe.mpr (hW_contains N le_rfl v (hmemt v hv)))
            _ = (T U).carrier := (Tube.carrier_eq_of_subset' hδρ (T U) (𝒞.tube N v)
                (SetLike.coe_subset_coe.mpr hUv)).symm
            _ = V.carrier :=
                Tube.carrier_eq_of_subset' hδρ (T U) V (SetLike.coe_subset_coe.mpr hUV)
        intro a ha b hb
        obtain ⟨haP, U, hUt, hUa, hUV⟩ := Finset.mem_filter.mp ha
        obtain ⟨hbP, U', hU't, hU'b, hU'V⟩ := Finset.mem_filter.mp hb
        exact hT_inj (hmemt a haP) (hmemt b hbP)
          ((hcarV a haP U hUa hUV).trans (hcarV b hbP U' hU'b hU'V).symm)
      · have hklt : k < N := Nat.lt_of_le_of_ne hk hkeq
        intro V
        refine (Finset.card_le_card_of_injOn (W k) (fun v hv => ?_)
            ((hNice_inj k).mono fun x hx => (Finset.mem_filter.mp hx).1)).trans
          (Tube.grid_overlap_tight (δ := δ) (gridScale_pos hδ N k) (Gk k) (hGnet k).2.1 V)
        obtain ⟨hvP, i, hit, hiv, hiV⟩ := Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr ⟨hW_mem_net k hklt v hvP, T i, hball i hit, hiv, hiV⟩

/-! ### One-sided uniformity at an absolute constant -/

/-- **One-sided tube uniformity is free at every scale of a halving grid.**

No refinement of the family, no transport of an input hierarchy and no `δ`-dependent loss: the
hierarchy is built directly by `Kakeya.ml1Boot.exists_gridCoverSystem_of_ratio`, and the two
surviving brackets of the one-sided reading are an upper bounded-overlap count — absolute, from
`Tube.grid_overlap_tight` — and an upper class bracket, which the *free* branching datum
`branchingN k = #t` makes vacuous.  The two clauses the one-sided reading deletes,
`Tube.UniformTubeSet.le_card_class` and its shaded companions, are the only ones that would force
a genuine regularization, and with them the `δ ^ (-o(1))` loss of GWZ's every-scale lemma. -/
theorem nonempty_isFlatPrismUniformTubeSet_of_ratio {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {N : ℕ} (hN : 0 < N)
    (hsep2 : ∀ k, k < N → 2 * ((gridScale δ N (k + 1) : NNReal) : ℝ) ≤ (gridScale δ N k : ℝ))
    (t : Finset ι) (T : ι → Tube δ E)
    (hball : ∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hT_inj : Set.InjOn (fun i => (T i).carrier) (t : Set ι))
    {C : NNReal} (hC1 : 1 ≤ C)
    (hC : ((Tube.overlapConstBOTight (Module.finrank ℝ E) : ℕ) : NNReal) ≤ C) :
    Nonempty (IsFlatPrismUniformTubeSet t T N C) := by
  classical
  obtain ⟨𝒞, h𝒞⟩ := exists_gridCoverSystem_of_ratio hδ hδ1 hN hsep2 t T hball hT_inj
  refine ⟨{ cover := 𝒞
            branchingN := fun _ => (t.card : NNReal)
            tube_injOn := fun k hk => (h𝒞 k hk).1
            boundedOverlap := ?_
            card_class_le := ?_ }⟩
  · intro k hk V
    have h := (h𝒞 k hk).2 V
    have h' : (((𝒞.indexSet k).filter (fun j => ∃ i ∈ t,
        (T i).toConvexSpaceBody ≤ (𝒞.tube k j).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card : NNReal)
        ≤ ((Tube.overlapConstBOTight (Module.finrank ℝ E) : ℕ) : NNReal) := by
      exact_mod_cast h
    exact h'.trans hC
  · intro k hk j hj
    have hsub : (Tube.coverClass t (𝒞.assign k) j).card ≤ t.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have h1 : ((Tube.coverClass t (𝒞.assign k) j).card : NNReal) ≤ (t.card : NNReal) := by
      exact_mod_cast hsub
    exact h1.trans (le_mul_of_one_le_left (by positivity) hC1)

/-- **One-sided shaded uniformity is free at every scale of a halving grid.**

The shaded reading adds `card_shadeClass_le` and `le_branchingN`, both upper bounds on quantities
bounded by `#t`, and both free data; so the shaded package costs nothing beyond
`Kakeya.ml1Boot.nonempty_isFlatPrismUniformTubeSet_of_ratio`. -/
theorem nonempty_isFlatPrismUniform_of_ratio {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {N : ℕ} (hN : 0 < N)
    (hsep2 : ∀ k, k < N → 2 * ((gridScale δ N (k + 1) : NNReal) : ℝ) ≤ (gridScale δ N k : ℝ))
    (t : Finset ι) (V : ι → ShadedTube δ E)
    (hball : ∀ i ∈ t, (V i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hT_inj : Set.InjOn (fun i => (V i).carrier) (t : Set ι))
    {C : NNReal} (hC1 : 1 ≤ C)
    (hC : ((Tube.overlapConstBOTight (Module.finrank ℝ E) : ℕ) : NNReal) ≤ C) :
    Nonempty (IsFlatPrismUniform t V N C) := by
  classical
  obtain ⟨𝒰⟩ := nonempty_isFlatPrismUniformTubeSet_of_ratio hδ hδ1 hN hsep2 t
    (fun i => (V i).toTube) hball hT_inj hC1 hC
  refine ⟨{ tubeUniform := 𝒰
            branchingN := fun _ => (t.card : NNReal)
            localN := fun _ _ => (t.card : NNReal)
            card_shadeClass_le := ?_
            le_branchingN := ?_ }⟩
  · intro x hx k hk i hi hxi
    have hsub : (ShadedTube.shadeClass t V (𝒰.cover.assign k) (𝒰.cover.assign k i) x).card
        ≤ t.card :=
      Finset.card_le_card ((ShadedTube.shadeClass_subset t V _ _ x).trans
        (Finset.filter_subset _ _))
    have h1 : ((ShadedTube.shadeClass t V (𝒰.cover.assign k) (𝒰.cover.assign k i) x).card
        : NNReal) ≤ (t.card : NNReal) := by exact_mod_cast hsub
    exact h1.trans (le_mul_of_one_le_left (by positivity) hC1)
  · intro x hx k hk
    exact le_mul_of_one_le_left (by positivity) hC1

/-! ### The `ssf` grid -/

/-- `dt ≤ 2 ^ (-N)` at the `ssf` grid length `N = Tube.ssfGridLen dt`. -/
theorem Tube.ssfGridLen_rpow_le (dt : NNReal) (hdt1 : dt ≤ 1) :
    dt ≤ (2 : NNReal) ^ (-((Tube.ssfGridLen dt : ℕ) : ℝ)) := by
  set N : ℕ := Tube.ssfGridLen dt with hN
  set L : ℝ := Real.log (1 / (dt : ℝ)) with hL
  have hdtR : (dt : ℝ) ≤ 1 := hdt1
  have hdt0 : (0 : ℝ) ≤ (dt : ℝ) := dt.coe_nonneg
  -- L ≥ 0
  have hL0 : 0 ≤ L := by
    rcases eq_or_lt_of_le hdt0 with h | h
    · simp [hL, ← h]
    · rw [hL, one_div, Real.log_inv]
      simpa using Real.log_nonpos h.le hdtR
  -- N * log 2 ≤ L
  have hNL : (N : ℝ) * Real.log 2 ≤ L := by
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
      linarith
    have hNle : (N : ℝ) ≤ L := by
      rcases le_or_gt L 1 with hle | hlt
      · -- log L ≤ 0 so ceil = 0
        have : Real.log L ≤ 0 := by
          rcases lt_or_ge 0 L with hp | hp
          · exact Real.log_nonpos hp.le hle
          · have : L = 0 := le_antisymm hp hL0
            simp [this]
        have hN0 : N = 0 := by
          rw [hN, Tube.ssfGridLen, ← hL]
          simpa using Nat.ceil_eq_zero.mpr this
        rw [hN0]; simpa using hL0
      · have h1 : (N : ℝ) ≤ Real.log L + 1 := by
          rw [hN, Tube.ssfGridLen, ← hL]
          exact (Nat.ceil_lt_add_one (Real.log_nonneg hlt.le)).le
        have h2 : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos (by linarith)
        linarith
    have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg _
    nlinarith [Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)]
  -- conclude
  rcases eq_or_lt_of_le hdt0 with h | hpos
  · have : dt = 0 := by exact_mod_cast h.symm
    simp [this]
  · rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
    push_cast
    have hd : (dt:ℝ) = Real.exp (-L) := by
      rw [hL, one_div, Real.log_inv, neg_neg, Real.exp_log hpos]
    have h2 : Real.exp (Real.log 2 * (-(N:ℝ))) = (2:ℝ) ^ (-(N:ℝ)) :=
      (Real.rpow_def_of_pos (by norm_num) _).symm
    calc (dt:ℝ) = Real.exp (-L) := hd
      _ ≤ Real.exp (Real.log 2 * (-(N:ℝ))) := Real.exp_le_exp.mpr (by nlinarith)
      _ = (2:ℝ) ^ (-(N:ℝ)) := h2

/-- **Consecutive grid scales are `2`-separated** when `δ ≤ 2 ^ (-N)`.  The halved analogue of
`Tube.sixteen_mul_Tube.gridScale_succ_le`; the weaker ratio is what the `ssf` grid length supplies
unconditionally (`Tube.ssfGridLen_rpow_le`). -/
theorem two_mul_Tube.gridScale_succ_le {δ : NNReal} (hδ : 0 < δ) {N : ℕ}
    (hδ0 : δ ≤ (2 : NNReal) ^ (-(N : ℝ))) {k : ℕ} (hk : k < N) :
    2 * Tube.gridScale δ N (k + 1) ≤ Tube.gridScale δ N k := by
  have hN0 : 0 < N := lt_of_le_of_lt (Nat.zero_le k) hk
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN0)
  have hE : 0 ≤ (1 : ℝ) / (N : ℝ) := by positivity
  have hδinv : δ ^ ((1 : ℝ) / (N : ℝ)) ≤ (1 : NNReal) / 2 := by
    calc
      δ ^ ((1 : ℝ) / (N : ℝ))
          ≤ ((2 : NNReal) ^ (-(N : ℝ))) ^ ((1 : ℝ) / (N : ℝ)) := NNReal.rpow_le_rpow hδ0 hE
      _ = (2 : NNReal) ^ ((-(N : ℝ)) * ((1 : ℝ) / (N : ℝ))) := by rw [NNReal.rpow_mul]
      _ = (2 : NNReal) ^ (-(1 : ℝ)) := by congr 1; field_simp
      _ = (1 : NNReal) / 2 := by rw [NNReal.rpow_neg_one]; norm_num
  have hδle1 : 2 * δ ^ ((1 : ℝ) / (N : ℝ)) ≤ 1 := by
    calc
      2 * δ ^ ((1 : ℝ) / (N : ℝ)) ≤ 2 * ((1 : NNReal) / 2) := by gcongr
      _ = 1 := by norm_num
  have hfac : Tube.gridScale δ N (k + 1) = Tube.gridScale δ N k * δ ^ ((1 : ℝ) / (N : ℝ)) := by
    unfold Tube.gridScale
    rw [show (((k + 1 : ℕ) : ℝ) / (N : ℝ)) =
          (((k : ℕ) : ℝ) / (N : ℝ)) + (1 : ℝ) / (N : ℝ) by
          push_cast; field_simp]
    rw [NNReal.rpow_add (ne_of_gt hδ)]
  calc
    2 * Tube.gridScale δ N (k + 1)
        = 2 * (Tube.gridScale δ N k * δ ^ ((1 : ℝ) / (N : ℝ))) := by rw [hfac]
    _ = Tube.gridScale δ N k * (2 * δ ^ ((1 : ℝ) / (N : ℝ))) := by ring
    _ ≤ Tube.gridScale δ N k * 1 := by gcongr
    _ = Tube.gridScale δ N k := by rw [mul_one]

/-- Above the bottom grid level the scale is at least `2 δ`. -/
theorem two_mul_le_Tube.gridScale {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N k : ℕ} (hk : k < N)
    (hδN : δ ≤ (2 : NNReal) ^ (-(N : ℝ))) : 2 * δ ≤ Tube.gridScale δ N k := by
  have hN0 : 0 < N := lt_of_le_of_lt (Nat.zero_le k) hk
  have hkN : k + 1 ≤ N := Nat.succ_le_of_lt hk
  have hgeom : 2 * Tube.gridScale δ N (k + 1) ≤ Tube.gridScale δ N k :=
    two_mul_Tube.gridScale_succ_le hδ hδN hk
  have hδσ : δ ≤ Tube.gridScale δ N (k + 1) := by
    have h' : Tube.gridScale δ N N ≤ Tube.gridScale δ N (k + 1) :=
      Tube.gridScale_antitone hδ hδ1 N hkN
    rwa [Tube.gridScale_self δ hN0] at h'
  calc
    2 * δ ≤ 2 * Tube.gridScale δ N (k + 1) := by gcongr
    _ ≤ Tube.gridScale δ N k := hgeom

/-- **The `ssf` grid halves at every step**, with no smallness assumption on `dt`. -/
theorem two_mul_ssfGrid_succ_le {dt : NNReal} (hdt : 0 < dt) (hdt1 : dt ≤ 1)
    {k : ℕ} (hk : k < Tube.ssfGridLen dt) :
    2 * Tube.gridScale dt (Tube.ssfGridLen dt) (k + 1) ≤ Tube.gridScale dt (Tube.ssfGridLen dt) k :=
  two_mul_Tube.gridScale_succ_le hdt (Tube.ssfGridLen_rpow_le dt hdt1) hk

/-- `2 dt ≤ σ_k` for every `ssf` grid level above the bottom. -/
theorem two_mul_le_ssfGrid {dt : NNReal} (hdt : 0 < dt) (hdt1 : dt ≤ 1)
    {k : ℕ} (hk : k < Tube.ssfGridLen dt) :
    2 * dt ≤ Tube.gridScale dt (Tube.ssfGridLen dt) k :=
  two_mul_le_Tube.gridScale hdt hdt1 hk (Tube.ssfGridLen_rpow_le dt hdt1)



/-- `0 < Tube.ssfGridLen dt` as soon as `dt ≤ 1 / 4`. -/
theorem ssfGridLen_pos {dt : NNReal} (hdt0 : 0 < dt) (hdt : dt ≤ 1 / 4) :
    0 < Tube.ssfGridLen dt := by
  have hdtR : (0 : ℝ) < (dt : ℝ) := hdt0
  have hdt4 : (dt : ℝ) ≤ 1 / 4 := by exact_mod_cast hdt
  have h4 : (4 : ℝ) ≤ 1 / (dt : ℝ) := by
    rw [le_div_iff₀ hdtR]; linarith
  have hlog4 : (1 : ℝ) < Real.log 4 := by
    have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]; push_cast; ring
    rw [this]; linarith
  have hlog : (1 : ℝ) < Real.log (1 / (dt : ℝ)) := by
    refine hlog4.trans_le (Real.log_le_log (by norm_num) h4)
  rw [Tube.ssfGridLen, Nat.ceil_pos]
  exact Real.log_pos hlog

/-- Members of a pairwise essentially distinct family have pairwise distinct carriers. -/
theorem injOn_carrier_of_pairwise_essentiallyDistinct {δ : NNReal} (hδ : 0 < δ)
    (t : Finset ι) (T : ι → Tube δ E)
    (hED : (t : Set ι).Pairwise fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) :
    Set.InjOn (fun i => (T i).carrier) (t : Set ι) := by
  intro i hi j hj h_eq
  by_contra hne
  have hEDij : IsEssentiallyDistinct (T i).carrier (T j).carrier := hED hi hj hne
  rw [show (T i).carrier = (T j).carrier from h_eq] at hEDij
  have hvol_pos : volume (T j).carrier ≠ 0 := by
    have h1 : (0 : NNReal) <
        Tube.le_volume.c (Module.finrank ℝ E) * δ ^ (Module.finrank ℝ E - 1) :=
      mul_pos (Tube.le_volume.c_pos _) (pow_pos hδ _)
    exact ne_of_gt (lt_of_lt_of_le (by exact_mod_cast h1) (Tube.le_volume (T j)))
  exact absurd hEDij
    (not_isEssentiallyDistinct_self hvol_pos (T j).isCompact.measure_lt_top.ne)

/-- **The every-scale one-sided uniformity of a normalized family, at an absolute constant.**

This is the clause the fine normalization owes: for *any* family of essentially distinct
`dt`-tubes in the unit ball, with `dt ≤ 1 / 4`, one-sided uniformity holds on the full `ssf` grid
`Tube.ssfGridLen dt` at the absolute constant `Tube.overlapConstBOTight 3`, which depends only on
the dimension.  Nothing is refined and nothing is transported. -/
theorem nonempty_isFlatPrismUniform_ssf {dt : NNReal} (hdt0 : 0 < dt) (hdt : dt ≤ 1 / 4)
    (t : Finset ι) (V : ι → ShadedTube dt E)
    (hball : ∀ i ∈ t, (V i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hED : (t : Set ι).Pairwise
      fun i j => IsEssentiallyDistinct (V i).carrier (V j).carrier)
    {C : NNReal} (hC1 : 1 ≤ C)
    (hC : ((Tube.overlapConstBOTight (Module.finrank ℝ E) : ℕ) : NNReal) ≤ C) :
    Nonempty (IsFlatPrismUniform t V (Tube.ssfGridLen dt) C) := by
  have hdt1 : dt ≤ 1 := hdt.trans (by rw [div_le_one (by norm_num : (0:NNReal) < 4)]; norm_num)
  refine nonempty_isFlatPrismUniform_of_ratio hdt0 hdt1 (ssfGridLen_pos hdt0 hdt) ?_ t V hball
    (injOn_carrier_of_pairwise_essentiallyDistinct hdt0 t (fun i => (V i).toTube) hED) hC1 hC
  intro k hk
  have h := two_mul_ssfGrid_succ_le hdt0 hdt1 hk
  exact_mod_cast h

/-- The absolute bounded-overlap constant of the every-scale hierarchy is below the fine
normalization's own loss constant. -/
theorem overlapConstBOTight_le_fineFactor_C :
    ((_root_.Tube.overlapConstBOTight 3 : ℕ) : NNReal) ≤ fineFactor.C := by
  have hN : _root_.Tube.normalization.C 3 = (64 : NNReal) := by
    unfold _root_.Tube.normalization.C; norm_num
  have hcr : (1 : NNReal) ≤ _root_.Tube.comparableReplacement.C 3 ((4 * (64 : NNReal)) ^ 6) :=
    _root_.Tube.comparableReplacement.one_le_C 3 _
  have hlow : (16 : NNReal) * ((4 * (64 : NNReal)) ^ 12) ≤ fineFactor.C := by
    unfold fineFactor.C fineNormalize.C
    rw [hN]
    gcongr
    refine le_trans ?_ le_self_add
    exact le_mul_of_one_le_right (by positivity) hcr
  refine le_trans ?_ hlow
  have hlhs : ((_root_.Tube.overlapConstBOTight 3 : ℕ) : NNReal) = 2 * (9220 : NNReal) ^ 6 := by
    unfold _root_.Tube.overlapConstBOTight
    push_cast
    norm_num
  rw [hlhs]
  norm_num

omit [Nontrivial E] in
/-- **A nonempty one-sidedly uniform family has constant at least `1`.**

The bounded-overlap count of Definition 2.1(ii) at the coarsest grid scale `ρ_0 = 1`, tested
against a member's own unit rescale, is at least one, so the constant it is bounded by is. -/
theorem one_le_of_isFlatPrismUniform {ι : Type*} {δ : NNReal} (hδ1 : δ ≤ 1)
    {u : Finset ι} (hu : u.Nonempty) {U : ι → ShadedTube δ E} {N : ℕ} {C : NNReal}
    (h : IsFlatPrismUniform u U N C) : 1 ≤ C := by
  classical
  obtain ⟨i₀, hi₀⟩ := hu
  set 𝒰 := h.tubeUniform with h𝒰
  have hg0 : _root_.Tube.gridScale δ N 0 = 1 := _root_.Tube.gridScale_zero δ N
  set W : Tube (_root_.Tube.gridScale δ N 0) E :=
    (U i₀).toTube.rescale (_root_.Tube.gridScale δ N 0) with hW
  have hbo := 𝒰.boundedOverlap 0 (Nat.zero_le N) W
  have hmem : 𝒰.cover.assign 0 i₀ ∈ (𝒰.cover.indexSet 0).filter (fun j => ∃ i ∈ u,
      ((U i).toTube).toConvexSpaceBody ≤ (𝒰.cover.tube 0 j).toConvexSpaceBody ∧
      ((U i).toTube).toConvexSpaceBody ≤ W.toConvexSpaceBody) := by
    refine Finset.mem_filter.mpr ⟨𝒰.cover.assign_mem 0 (Nat.zero_le N) i₀ hi₀,
      i₀, hi₀, 𝒰.cover.le_tube_assign 0 (Nat.zero_le N) i₀ hi₀, ?_⟩
    exact _root_.Tube.le_rescale _ (by rw [hg0]; exact hδ1)
  have hcard : 1 ≤ ((𝒰.cover.indexSet 0).filter (fun j => ∃ i ∈ u,
      ((U i).toTube).toConvexSpaceBody ≤ (𝒰.cover.tube 0 j).toConvexSpaceBody ∧
      ((U i).toTube).toConvexSpaceBody ≤ W.toConvexSpaceBody)).card :=
    Finset.card_pos.mpr ⟨_, hmem⟩
  have hcardN : (1 : NNReal) ≤ (((𝒰.cover.indexSet 0).filter (fun j => ∃ i ∈ u,
      ((U i).toTube).toConvexSpaceBody ≤ (𝒰.cover.tube 0 j).toConvexSpaceBody ∧
      ((U i).toTube).toConvexSpaceBody ≤ W.toConvexSpaceBody)).card : NNReal) := by
    exact_mod_cast hcard
  exact hcardN.trans hbo

/-- `1 ≤ Tube.overlapConstBOTight n`. -/
theorem one_le_overlapConstBOTight (n : ℕ) :
    (1 : NNReal) ≤ ((_root_.Tube.overlapConstBOTight n : ℕ) : NNReal) := by
  have : 1 ≤ _root_.Tube.overlapConstBOTight n :=
    Nat.one_le_iff_ne_zero.mpr (by unfold _root_.Tube.overlapConstBOTight; positivity)
  exact_mod_cast this

/-- **The one-sided uniformity hypothesis of the Main Lemma 1 chain is not a restriction.**

Every hypothesis of `Kakeya.ml1Boot.nonempty_isFlatPrismUniform_ssf` is already carried by the
statements that *assume* `Kakeya.IsFlatPrismUniform u U (Tube.ssfGridLen τ) C_unif` — notably
`Kakeya.ml1Boot.multiplicity_le_middle_avg` and `Kakeya.ml1Boot.multiplicity_le_middle`, both of
which assume `T_θ ⊆ B₁`, `U k ⊆ T_θ` for `k ∈ u`, and pairwise essential distinctness on `u`, and
both of which are read under a scale prefix forcing `τ ≤ δ ^ ε θ ≤ 1/4`.  So the uniformity
hypothesis of those statements can be discharged at the *absolute* constant
`Tube.overlapConstBOTight 3` by any caller, and `C_unif` need never be produced.

This is the general form of what closes clause (iii) of
`Kakeya.ml1Boot.exists_fineNormalization_lower`: in the one-sided reading, uniformity is not a
property a family may fail to have. -/
theorem nonempty_isFlatPrismUniform_of_subset_tube {τ θ : NNReal} (hτ0 : 0 < τ)
    (hτ4 : τ ≤ 1 / 4) (Tθ : Tube θ E) (u : Finset ι) (U : ι → ShadedTube τ E)
    (hTθ : Tθ.carrier ⊆ Metric.closedBall (0 : E) 1)
    (hsub : ∀ k ∈ u, (U k).carrier ⊆ Tθ.carrier)
    (hED : (u : Set ι).Pairwise
      fun k k' => IsEssentiallyDistinct (U k).carrier (U k').carrier) :
    Nonempty (IsFlatPrismUniform u U (Tube.ssfGridLen τ)
      ((_root_.Tube.overlapConstBOTight (Module.finrank ℝ E) : ℕ) : NNReal)) :=
  nonempty_isFlatPrismUniform_ssf hτ0 hτ4 u U (fun k hk => (hsub k hk).trans hTθ) hED
    (one_le_overlapConstBOTight _) le_rfl

end ml1Boot
end Kakeya
