/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.ChainScale
public import Kakeya.MultiScaleFac.Chain
public import Kakeya.MultiScaleFac.Density
public import Kakeya.MultiScaleFac.Branching

/-!
# The node reading of the multiscale chain of GWZ Lemma 7.7(A)

`Kakeya.MultiScaleFac.maxDensity_le_prod_of_grid_cuts` builds the abstract chain that
`Tube.ParentBodyDensity.maxDensity_le_prod_of_uniform_at_scales` (GWZ Lemma 7.4) consumes out of
*leaf* representatives, so its per-level Katz–Tao input is the leaf fibre family
`fibreIndex s T (σ (m+1)) (σ m) i₀`.  That family counts a coarse tube once for every `δ`-tube
inside it, so a Frostman bound for it carries the branching number `N_{σ_{m+1}}` of the level,
and telescoping the product then retains a spurious `∏_{k=1}^{M-1} N_{σ_k}`, which is of size
`δ^{-(n-1)}`.

GWZ's per-level families are the *node* families of Definition 2.1: the `σ_{m+1}`-tubes inside
one `σ_m`-tube, one body per node, and no branching number.  This file builds the Lemma 7.4
chain out of those, and exports `maxDensity_le_prod_of_grid_cuts_nodes`.

## The chain

With `1 = σ 0 ≥ … ≥ σ M = δ` a `16`-separated grid and
`𝒰 : ChainUniformTubeSet s T M σ Cu` a uniform hierarchy along it, the chain is

* level `k < M`: the level-`k` nodes of `𝒰` that contain at least one `δ`-tube of `s`, with body
  `(𝒰.cover.tube k j).rescale (ρ k)` for the inflated scale `ρ k = 2 σ k`;
* level `M`: the leaves themselves, with body `(T i).rescale δ`, so that the leaf-to-chain
  cover map is the identity and Lemma 7.4's injectivity hypothesis is free.

The projection sends a node to a node of the previous level containing one of its `δ`-tubes
(`node_rescale_le_node_rescale_of_shared_tube`), and the level-`0` count is bounded by the
number of `1`-scale nodes carrying a `δ`-tube, which `card_parent_with_leaf_le` bounds by
`Cu² · 9 ^ (2n)` — a separated net of leaf representatives together with the bounded-overlap
clause of the bundle, read through `ChainUniformTubeSet.uniformAt`, whose constant is `Cu ^ 2`.

Only the finest gap is not a node-to-node gap: it compares the leaves with the `δ`-nodes, and
this is where the single factor `𝒰.branchingN M` of the conclusion comes from
(`exists_isKatzTao_leaf_of_isKatzTao_node`).  The same factor appears on the leaf side of
`densityIn_fibre_prod`, so it cancels downstream and must not be removed here.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-! ### Geometric preliminaries -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **A node sits inside a fattening of any of its `δ`-tubes.**  If a tube `Tl` lies in a node `V`
of scale `σb`, then the `r`-rescale of `V` lies in the `θ`-rescale of `Tl` as soon as
`4 σb + r ≤ θ`.  This is the first half of `node_rescale_le_node_rescale_of_shared_tube`. -/
theorem node_rescale_le_leaf_rescale {δ σb : NNReal} (Tl : Tube δ E) (V : Tube σb E)
    {r θ : NNReal} (hbr : σb ≤ r) (hθ : 4 * σb + r ≤ θ)
    (h : Tl.toConvexSpaceBody ≤ V.toConvexSpaceBody) :
    (V.rescale r).toConvexSpaceBody ≤ (Tl.rescale θ).toConvexSpaceBody :=
  -- `(Tl.rescale (4 * σb)).rescale θ = Tl.rescale θ` holds by `rfl` (`Tube.rescale_rescale`).
  Tube.rescale_le_rescale_of_body_le V (Tl.rescale (4 * σb)) hbr hθ (Tube.rescale_le_of_le Tl V h)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- A bounded rescaling of a tube in the unit ball stays in the ball of radius `9`, which is
the radius `R + 3` that `Tube.ParentBodyDensity.maxDensity_le_prod_of_uniform_at_scales` requires of
all chain bodies when `R = 6`. -/
theorem leaf_rescale_carrier_subset_closedBall {δ : NNReal} (X : Tube δ E)
    (hball : X.carrier ⊆ Metric.closedBall (0 : E) 1) {τ : NNReal} (hτ : (τ : ℝ) ≤ 6) :
    (X.rescale τ).carrier ⊆ Metric.closedBall (0 : E) 9 := by
  have htemp : (X.rescale τ).carrier ⊆ Metric.closedBall (0 : E) (1 + 6 + 0) := by
    simpa using Tube.rescale_translate_carrier_subset_closedBall X hball
      (by norm_num : (0 : ℝ) ≤ 6) (by linarith [NNReal.coe_nonneg δ] : (τ : ℝ) ≤ (δ : ℝ) + 6)
      (0 : E) (by norm_num : ‖(0 : E)‖ ≤ (0 : ℝ))
  exact htemp.trans (Metric.closedBall_subset_closedBall (by norm_num))

/-- **The number of scale-`1` nodes carrying a `δ`-tube is bounded by a dimensional constant.**
Bounded overlap caps the nodes sharing a `δ`-tube with a fixed `σ k`-tube, and a `1/2`-separated
net of leaf representatives (`exists_tube_net`, of size `9 ^ (2n)` at scale `1`) reaches every
leaf; the per-scale reading `ChainUniformTubeSet.uniformAt` gives the bound `Cu ^ 2 · 9 ^ (2n)`. -/
theorem card_parent_with_leaf_le {ι : Type*} {δ : NNReal} (hδ : (δ : ℝ) ≤ 1 / 2)
    {s : Finset ι} (hs : s.Nonempty) {T : ι → Tube δ E}
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    {N : ℕ} {σ : ℕ → NNReal} {Cu : NNReal}
    (𝒰 : ChainUniformTubeSet s T N σ Cu) (hCu : 1 ≤ Cu) {k : ℕ} (hk : k ≤ N) (hν : σ k = 1) :
    (((𝒰.cover.indexSet k).filter (fun j => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody)).card : ℝ)
      ≤ ((Cu ^ 2 : NNReal) : ℝ) * 9 ^ (2 * Module.finrank ℝ E) := by
  classical
  have hBO : ∀ V : Tube (1 : NNReal) E,
      (((𝒰.cover.indexSet k).filter (fun j => ∃ i ∈ s,
          (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card : NNReal) ≤ Cu ^ 2 := by
    rw [← hν]
    exact fun V => (𝒰.boundedOverlap k hk V).trans (le_self_pow hCu (by norm_num))
  obtain ⟨s', f, hs'sub, hf_mem, hcont, hcard⟩ :=
    exists_tube_net s hs T hball (θ := (1 : NNReal)) (by norm_num)
  rw [show (1 + ((1 : NNReal) : ℝ) / 8) / (((1 : NNReal) : ℝ) / 8) = (9 : ℝ) by norm_num] at hcard
  have hleaf_containment : ∀ i ∈ s,
      (T i).toConvexSpaceBody ≤ ((T (f i)).rescale 1).toConvexSpaceBody := fun i hi => by
    have h := hcont δ 1 (by simp only [NNReal.coe_one]; linarith) i hi
    rwa [Tube.toConvexSpaceBody_rescale_self] at h
  set P := (𝒰.cover.indexSet k).filter (fun j => ∃ i ∈ s,
    (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody) with hP
  set Q := fun (p : ι) => (𝒰.cover.indexSet k).filter (fun j => ∃ i ∈ s,
    (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
    (T i).toConvexSpaceBody ≤ ((T p).rescale 1).toConvexSpaceBody) with hQ
  have h_cover : P ⊆ s'.biUnion Q := by
    intro j hj
    obtain ⟨hj_parent, i, hi_s, hi_le⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_biUnion.mpr ⟨f i, hf_mem i hi_s,
      Finset.mem_filter.mpr ⟨hj_parent, i, hi_s, hi_le, hleaf_containment i hi_s⟩⟩
  calc
    (P.card : ℝ) ≤ ((s'.biUnion Q).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card h_cover)
    _ ≤ ∑ p ∈ s', ((Q p).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ s', ((Cu ^ 2 : NNReal) : ℝ) :=
      Finset.sum_le_sum fun p _ => by exact_mod_cast hBO ((T p).rescale 1)
    _ = (s'.card : ℝ) * ((Cu ^ 2 : NNReal) : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Cu ^ 2 : NNReal) : ℝ) * 9 ^ (2 * Module.finrank ℝ E) :=
      (mul_le_mul_of_nonneg_right hcard (NNReal.coe_nonneg _)).trans_eq (mul_comm _ _)

/-! ### The inflated scales of the node chain -/

/-- **The scale function of the node chain.**  The grid inflated by a factor `2`, except at the
finest level where it must be exactly `δ`.  Compared with `exists_inflated_scales` the two
leaf-slack inequalities are replaced by the single node-slack inequality
`σ_m + 4 σ_{m+1} + ρ_{m+1} ≤ ρ_m`, which holds for a `16`-separated grid. -/
theorem exists_inflated_scales_node {M : ℕ} (hM : 0 < M) {δ : NNReal} (_hδ : 0 < δ)
    (σ : Fin (M + 1) → NNReal) (hσ0 : σ 0 = 1) (hσlast : σ (Fin.last M) = δ)
    (hanti : Antitone σ) (hgap : ∀ m : Fin M, 16 * σ m.succ ≤ σ m.castSucc) :
    ∃ ρ : Fin (M + 1) → NNReal,
      1 ≤ ρ 0 ∧ ρ 0 ≤ 4 ∧ ρ (Fin.last M) = δ ∧ Antitone ρ ∧
      (∀ m : Fin M, 4 * ρ m.succ ≤ ρ m.castSucc) ∧
      (∀ k, ρ k ≤ 2) ∧
      (∀ k, σ k ≤ ρ k) ∧
      (∀ m : Fin M, ρ m.succ ≤ 2 * σ m.succ) ∧
      (∀ m : Fin M, ρ m.succ ≤ 1) ∧
      (∀ m : Fin M, σ m.castSucc + 4 * σ m.succ + ρ m.succ ≤ ρ m.castSucc) := by
  have h0_ne_last : (0 : Fin (M + 1)) ≠ Fin.last M := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_last]; omega
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Fin (M + 1) → NNReal,
      ∀ k, ρ k = if k = Fin.last M then δ else 2 * σ k := ⟨_, fun _ => rfl⟩
  have hσ_le_one : ∀ k, σ k ≤ 1 := fun k => (hanti (Fin.zero_le k)).trans hσ0.le
  have hρb : ∀ k, σ k ≤ ρ k ∧ ρ k ≤ 2 * σ k := fun k => by
    rcases eq_or_ne k (Fin.last M) with rfl | hk
    · rw [hρ, if_pos rfl, hσlast, two_mul]; exact ⟨le_rfl, le_add_self⟩
    · rw [hρ, if_neg hk, two_mul]; exact ⟨le_add_self, le_rfl⟩
  have hlb : ∀ k, σ k ≤ ρ k := fun k => (hρb k).1
  have hub : ∀ k, ρ k ≤ 2 * σ k := fun k => (hρb k).2
  have hρ0 : ρ 0 = 2 := by rw [hρ, if_neg h0_ne_last, hσ0, mul_one]
  have hρ_castSucc : ∀ m : Fin M, ρ m.castSucc = 2 * σ m.castSucc :=
    fun m => by rw [hρ, if_neg (Fin.castSucc_ne_last m)]
  have h8 : ∀ m : Fin M, 8 * σ m.succ ≤ σ m.castSucc :=
    fun m => le_trans (mul_le_mul_left (by norm_num) _) (hgap m)
  refine ⟨ρ, by rw [hρ0]; norm_num, by rw [hρ0]; norm_num, by rw [hρ, if_pos rfl], ?_, ?_, ?_,
    hlb, fun m => hub _, ?_, ?_⟩
  · intro i j hij
    rcases eq_or_ne j (Fin.last M) with rfl | hj
    · rw [hρ, if_pos rfl]
      exact (hσlast.symm.le.trans (hanti (Fin.le_last i))).trans (hlb i)
    · have hi : i ≠ Fin.last M := fun h => hj (le_antisymm (Fin.le_last j) (h ▸ hij))
      rw [hρ, if_neg hj, hρ, if_neg hi]
      exact mul_le_mul_right (hanti hij) 2
  · intro m
    calc 4 * ρ m.succ ≤ 4 * (2 * σ m.succ) := mul_le_mul_right (hub _) 4
      _ = 8 * σ m.succ := by ring
      _ ≤ σ m.castSucc := h8 m
      _ ≤ ρ m.castSucc := hlb _
  · intro k
    calc ρ k ≤ 2 * σ k := hub k
      _ ≤ 2 * 1 := mul_le_mul_right (hσ_le_one k) 2
      _ = 2 := mul_one 2
  · intro m
    calc ρ m.succ ≤ 2 * σ m.succ := hub _
      _ ≤ 8 * σ m.succ := mul_le_mul_left (by norm_num) _
      _ ≤ σ m.castSucc := h8 m
      _ ≤ 1 := hσ_le_one _
  · intro m
    have h : 4 * σ m.succ + ρ m.succ ≤ σ m.castSucc :=
      calc 4 * σ m.succ + ρ m.succ ≤ 4 * σ m.succ + 2 * σ m.succ := add_le_add_right (hub _) _
        _ = 6 * σ m.succ := by ring
        _ ≤ 8 * σ m.succ := mul_le_mul_left (by norm_num) _
        _ ≤ σ m.castSucc := h8 m
    rw [hρ_castSucc m, two_mul, add_assoc]
    exact add_le_add_right h _

/-- Two tubes of the same radius `δ ≤ 1` have comparable volumes: the two-sided tube-volume
bounds `Tube.volume_le` and `Tube.le_volume` differ only by the dimensional factor
`katzTaoRescaleConst E`.  Used at the finest gap, where a leaf and a `δ`-node containing it
must be traded against each other. -/
theorem volume_tube_le_mul_volume_tube {δ : NNReal} (hδ1 : δ ≤ 1) (A B : Tube δ E) :
    volume A.carrier ≤ (katzTaoRescaleConst E : ENNReal) * volume B.carrier := by
  set n := Module.finrank ℝ E
  have h_mul : (Tube.volume_le.C n : ENNReal)
      ≤ (katzTaoRescaleConst E : ENNReal) * (Tube.le_volume.c n : ENNReal) := by
    have hn : Tube.volume_le.C n ≤ katzTaoRescaleConst E * Tube.le_volume.c n := by
      rw [show katzTaoRescaleConst E * Tube.le_volume.c n
        = Tube.volume_le.C n * 2 ^ (n - 1) from div_mul_cancel₀ _ (Tube.le_volume.c_pos n).ne']
      exact le_mul_of_one_le_right zero_le (one_le_pow₀ one_le_two)
    rw [← ENNReal.coe_mul]
    exact_mod_cast hn
  calc
    volume A.carrier ≤ (Tube.volume_le.C n : ENNReal) * ((δ : ENNReal) ^ (n - 1)) := by
      simpa using Tube.volume_le hδ1 A
    _ ≤ (katzTaoRescaleConst E : ENNReal)
          * ((Tube.le_volume.c n : ENNReal) * ((δ : ENNReal) ^ (n - 1))) := by
      rw [← mul_assoc]; exact mul_le_mul_left h_mul _
    _ ≤ (katzTaoRescaleConst E : ENNReal) * volume B.carrier :=
      mul_le_mul_right (by simpa using Tube.le_volume B) _

omit [Nontrivial E] in
/-- **Fattening a test body by three times a radius it already contains costs `(2 ^ n) ^ 3`.**
The scale-free form of `volume_cthickening_nat_mul_le_of_ball` for convex *bodies*, which is
how a Katz–Tao hypothesis is evaluated at a slightly enlarged test body. -/
theorem volume_cthickening_body_le {K : ConvexSpaceBody E} {p : E} {r : ℝ} (hr : 0 ≤ r)
    (hp : Metric.closedBall p r ⊆ K.carrier) :
    volume (K.cthickening (3 * r)).carrier
      ≤ (ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℝ E)) ^ 3 * volume K.carrier := by
  change volume (Metric.cthickening (3 * r) K.carrier) ≤ _
  simpa using Kakeya.MultiScaleFac.volume_cthickening_nat_mul_le_of_ball
    K.carrier K.convex K.isCompact p hr hp 3

/-- **Regrouping a sum along a map with bounded fibres.**  If every fibre of `g` inside `t` has
at most `c` elements, then summing a weight along `g` costs at most `c` times the sum of the
weight over the image.  This is the multiplicity step of the finest gap, where several leaves
share one `δ`-node. -/
theorem sum_comp_le_mul_sum {α β : Type*} [DecidableEq β] (t : Finset α) (g : α → β)
    (w : β → ENNReal) {c : ENNReal}
    (hc : ∀ b ∈ t.image g, ((t.filter (fun a => g a = b)).card : ENNReal) ≤ c) :
    ∑ a ∈ t, w (g a) ≤ c * ∑ b ∈ t.image g, w b := by
  rw [Finset.sum_comp w g, Finset.mul_sum]
  exact Finset.sum_le_sum fun b hb => by
    rw [nsmul_eq_mul]; exact mul_le_mul_left (hc b hb) (w b)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- A tube contains the closed ball of its own radius about either endpoint, so any convex body
dominating the tube contains that ball.  This supplies the "`K` already contains a ball of
radius `δ`" hypothesis of `volume_cthickening_body_le` for a nonempty filtered family. -/
theorem closedBall_subset_carrier_of_body_le {δ : NNReal} (A : Tube δ E) {K : ConvexSpaceBody E}
    (hAK : A.toConvexSpaceBody ≤ K) :
    Metric.closedBall A.x (δ : ℝ) ⊆ K.carrier := by
  have h_ball_sub_carrier : Metric.closedBall A.x (δ : ℝ) ⊆ A.carrier := by
    rw [A.carrier_eq]
    exact Set.subset_biUnion_of_mem (u := fun z => Metric.closedBall z (δ : ℝ))
      (left_mem_segment ℝ A.x A.y)
  exact h_ball_sub_carrier.trans (SetLike.coe_subset_coe.mpr hAK)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- If a `δ`-tube `A` sits inside both a `δ`-tube `B` and a convex body `K`, then `B` sits inside
the `3δ`-thickening of `K`: indeed `B ⊆ A^{(4δ)}`, which is the `3δ`-thickening of `A`. -/
theorem tube_body_le_cthickening_of_body_le {δ : NNReal} {K : ConvexSpaceBody E}
    (A B : Tube δ E) (hAB : A.toConvexSpaceBody ≤ B.toConvexSpaceBody)
    (hAK : A.toConvexSpaceBody ≤ K) :
    B.toConvexSpaceBody ≤ K.cthickening (3 * (δ : ℝ)) := by
  have h_sub_eq : ((4 * δ : NNReal) : ℝ) - (δ : ℝ) = 3 * (δ : ℝ) := by push_cast; ring
  calc
    B.toConvexSpaceBody ≤ (A.rescale (4 * δ)).toConvexSpaceBody := Tube.rescale_le_of_le A B hAB
    _ = A.toConvexSpaceBody.cthickening (3 * (δ : ℝ)) := by
      rw [← h_sub_eq]
      exact (Tube.toConvexBody_cthickening_sub A (le_mul_of_one_le_left' (by norm_num))).symm
    _ ≤ K.cthickening (3 * (δ : ℝ)) := ConvexSpaceBody.cthickening_mono _ hAK

/-- **The container of a chain fibre.**  If a coarse (`σa`-scale) node `Va` contains the `δ`-tubes
`Tl` and `Tp`, and a fine (`σb`-scale) node `Vb` also contains `Tl`, then `Vb` lies in the
`5σa`-thickening of `Tp`.  This is what puts a whole `proj`-fibre over a node inside a single set
`gapNodeIndex _ i₀ (5 * σa)` with `i₀` a fixed `δ`-tube of that node. -/
theorem node_body_le_leaf_rescale_of_shared_tube {δ σa σb : NNReal}
    (Va : Tube σa E) (Vb : Tube σb E) (Tl Tp : Tube δ E)
    (hδb : δ ≤ 4 * σb) (hθ : 4 * σa + 4 * σb ≤ 5 * σa)
    (h1 : Tl.toConvexSpaceBody ≤ Vb.toConvexSpaceBody)
    (h2 : Tl.toConvexSpaceBody ≤ Va.toConvexSpaceBody)
    (h3 : Tp.toConvexSpaceBody ≤ Va.toConvexSpaceBody) :
    Vb.toConvexSpaceBody ≤ (Tp.rescale (5 * σa)).toConvexSpaceBody := by
  calc
    Vb.toConvexSpaceBody ≤ (Tl.rescale (4 * σb)).toConvexSpaceBody :=
      Tube.body_le_rescale_of_le Tl Vb h1
    _ ≤ ((Tp.rescale (4 * σa)).rescale (4 * σa + 4 * σb)).toConvexSpaceBody :=
      Tube.rescale_le_rescale_of_body_le Tl (Tp.rescale (4 * σa)) hδb le_rfl
        (h2.trans (Tube.body_le_rescale_of_le Tp Va h3))
    _ = (Tp.rescale (4 * σa + 4 * σb)).toConvexSpaceBody := by simp [Tube.rescale_rescale]
    _ ≤ (Tp.rescale (5 * σa)).toConvexSpaceBody := Tube.rescale_le_rescale_of_radius_le Tp hθ

/-- **A Katz–Tao bound for the `δ`-nodes gives one for the leaves, at the cost of the branching
number.**  For a `Cu`-uniform hierarchy along `σ` with `σ k = δ`, a set `F` of leaves and a set `G`
containing every level-`k` node that carries a leaf of `F`: if `G` is `Δ`-Katz–Tao then `F` is
`A · Cu² · N_k · Δ`-Katz–Tao, where `A` depends only on the ambient dimension. -/
theorem exists_isKatzTao_leaf_of_isKatzTao_node :
    ∃ A : NNReal, 0 < A ∧
      ∀ {ι : Type u} {N : ℕ} {σ : ℕ → NNReal} {k : ℕ} {δ : NNReal},
        0 < δ → (δ : ℝ) ≤ 1 → k ≤ N → σ k = δ →
      ∀ {s : Finset ι} {T : ι → Tube δ E} {Cu : NNReal}
        (𝒰 : ChainUniformTubeSet s T N σ Cu), 1 ≤ Cu →
      ∀ (F G : Finset ι), F ⊆ s →
        (∀ i ∈ F, ∀ j ∈ 𝒰.cover.indexSet k,
          (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody → j ∈ G) →
        ∀ {Δ : ENNReal},
        ConvexSpaceBody.IsKatzTao G (fun j => (𝒰.cover.tube k j).toConvexSpaceBody) Δ →
        ConvexSpaceBody.IsKatzTao F (fun i => (T i).toConvexSpaceBody)
          ((A : ENNReal) * ((Cu ^ 2 : NNReal) : ENNReal) * (𝒰.branchingN k : ENNReal) * Δ) := by
  classical
  set n := Module.finrank ℝ E with hn_def
  set A : NNReal := katzTaoRescaleConst E * (2 : NNReal) ^ (3 * n) with hA_def
  have hApos : 0 < A := mul_pos katzTaoRescaleConst_pos (by positivity)
  refine ⟨A, hApos, ?_⟩
  intro ι N σ k δ hδpos hδ1 hk hν s T Cu 𝒰 hCu F G hFs hG Δ hKT
  subst hν
  set h : Tube.IsUniformAtScale s T (σ k) (Cu ^ 2) := 𝒰.uniformAt hCu hk with hh
  have hδ1' : σ k ≤ (1 : NNReal) := by exact_mod_cast hδ1
  rw [ConvexSpaceBody.isKatzTao_iff] at hKT ⊢
  intro K
  have hpar : ∀ i : ι, ∃ j : ι, i ∈ s → (j ∈ h.parent ∧
      (T i).toConvexSpaceBody ≤ (h.parentTube j).toConvexSpaceBody) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨j, hj, hle⟩ := h.exists_le_rescale hi
      exact ⟨j, fun _ => ⟨hj, hle⟩⟩
    · exact ⟨i, fun hi' => absurd hi' hi⟩
  choose par hpar using hpar
  set FK := F.filter (fun i => (T i).toConvexSpaceBody ≤ K) with hFKdef
  rcases FK.eq_empty_or_nonempty with hempty | ⟨i₁, hi₁⟩
  · simp [hempty]
  have hi₁F : i₁ ∈ F := (Finset.mem_filter.mp hi₁).1
  have hi₁K : (T i₁).toConvexSpaceBody ≤ K := (Finset.mem_filter.mp hi₁).2
  have hballK : Metric.closedBall (T i₁).x ((σ k : NNReal) : ℝ) ⊆ K.carrier :=
    closedBall_subset_carrier_of_body_le (T i₁) hi₁K
  have hrpos : 0 ≤ ((σ k : NNReal) : ℝ) := NNReal.coe_nonneg _
  set K' := K.cthickening (3 * ((σ k : NNReal) : ℝ)) with hK'def
  have hnode_le : ∀ i ∈ FK, (h.parentTube (par i)).toConvexSpaceBody ≤ K' := by
    intro i hi
    have hiF : i ∈ F := (Finset.mem_filter.mp hi).1
    have hiK : (T i).toConvexSpaceBody ≤ K := (Finset.mem_filter.mp hi).2
    have htemp := tube_body_le_cthickening_of_body_le (T i) (h.parentTube (par i))
      (hpar i (hFs hiF)).2 hiK
    simpa [hK'def] using htemp
  have himg : FK.image par ⊆ G.filter (fun j => (h.parentTube j).toConvexSpaceBody ≤ K') := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    have hiF : i ∈ F := (Finset.mem_filter.mp hi).1
    have hpar_mem : par i ∈ h.parent := (hpar i (hFs hiF)).1
    have hpar_body : (T i).toConvexSpaceBody ≤ (h.parentTube (par i)).toConvexSpaceBody :=
      (hpar i (hFs hiF)).2
    exact Finset.mem_filter.mpr
      ⟨hG i hiF (par i) hpar_mem hpar_body, hnode_le i hi⟩
  have hfib : ∀ b ∈ FK.image par,
      ((FK.filter (fun i => par i = b)).card : ENNReal)
        ≤ ((Cu ^ 2 * h.branchingN : NNReal) : ENNReal) := by
    intro b hb
    obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.mp hb
    have hi₀F : i₀ ∈ F := (Finset.mem_filter.mp hi₀).1
    have hsub : FK.filter (fun i => par i = par i₀) ⊆
        s.filter (fun i => (T i).toConvexSpaceBody ≤
          (h.parentTube (par i₀)).toConvexSpaceBody) := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      have hiF : i ∈ F := (Finset.mem_filter.mp hi.1).1
      refine ⟨hFs hiF, ?_⟩
      have hle := (hpar i (hFs hiF)).2
      rw [hi.2] at hle
      exact hle
    have hcard1 : ((FK.filter (fun i => par i = par i₀)).card : NNReal)
        ≤ ((s.filter (fun i => (T i).toConvexSpaceBody ≤
            (h.parentTube (par i₀)).toConvexSpaceBody)).card : NNReal) := by
      exact_mod_cast Finset.card_le_card hsub
    have hpar_i₀_mem : par i₀ ∈ h.parent := (hpar i₀ (hFs hi₀F)).1
    have hcard2 := h.card_filter_le hpar_i₀_mem
    have h1 : ((FK.filter (fun i => par i = par i₀)).card : NNReal) ≤ Cu ^ 2 * h.branchingN :=
      le_trans hcard1 hcard2
    exact_mod_cast h1
  have hpow_eq : (ENNReal.ofReal ((2 : ℝ) ^ n)) ^ 3 = ((2 : NNReal) ^ (3 * n) : ENNReal) := by
    calc
      (ENNReal.ofReal ((2 : ℝ) ^ n)) ^ 3 = ENNReal.ofReal (((2 : ℝ) ^ n) ^ 3) := by simp
      _ = ENNReal.ofReal ((2 : ℝ) ^ (3 * n)) := by ring_nf
      _ = ((2 : NNReal) ^ (3 * n) : ENNReal) := by simp
  calc
    ∑ i ∈ FK, volume ((T i).toConvexSpaceBody).carrier
        ≤ ∑ i ∈ FK, (katzTaoRescaleConst E : ENNReal) * volume (h.parentTube (par i)).carrier :=
      Finset.sum_le_sum fun i hi => volume_tube_le_mul_volume_tube hδ1' (T i) (h.parentTube (par i))
    _ ≤ (katzTaoRescaleConst E : ENNReal) * (((Cu ^ 2 * h.branchingN : NNReal) : ENNReal) *
          ∑ b ∈ FK.image par, volume (h.parentTube b).carrier) := by
      rw [← Finset.mul_sum]
      gcongr
      exact sum_comp_le_mul_sum FK par (fun b => volume (h.parentTube b).carrier) hfib
    _ ≤ (katzTaoRescaleConst E : ENNReal) * (((Cu ^ 2 * h.branchingN : NNReal) : ENNReal) *
          (Δ * ((ENNReal.ofReal ((2 : ℝ) ^ n)) ^ 3 * volume K.carrier))) := by
      gcongr
      exact ((Finset.sum_le_sum_of_subset himg).trans (hKT K')).trans
        (by gcongr; exact volume_cthickening_body_le hrpos hballK)
    _ = ((A : ENNReal) * ((Cu ^ 2 : NNReal) : ENNReal) * (h.branchingN : ENNReal) * Δ)
          * volume K.carrier := by
      rw [hpow_eq, hA_def]
      push_cast
      ring

/-- The per-gap constants of the node chain are the same at every gap except the finest one,
where the leaf multiplicity enters; this evaluates the resulting product.  The point is that the
exceptional factor `B` appears with exponent `1`, not `M`. -/
theorem prod_ite_succ_last_mul {M : ℕ} (j : Fin M) (K B : ENNReal) (Δ : Fin M → ENNReal) :
    ∏ m : Fin M, ((if m = j then B else K) * Δ m)
      = B * K ^ (M - 1) * ∏ m, Δ m := by
  classical
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin M)) _ (Finset.mem_univ j),
    Finset.prod_congr rfl (fun m hm => if_neg (Finset.ne_of_mem_erase hm)),
    Finset.prod_const, if_pos rfl, Finset.card_erase_of_mem (Finset.mem_univ j),
    Finset.card_univ, Fintype.card_fin]

/-- The constant bookkeeping of the node chain: the per-gap rescaling constant `Kc` enters with
exponent `M - 1`, the finest-gap constant `A` with exponent `1`, and both are absorbed into a
single constant raised to the power `M`, leaving the leaf multiplicity `Cu * N` as the only
explicit factor. -/
theorem chain_const_arith {M : ℕ} (hM : 0 < M) {C₀ : ℝ} (hC₀ : 0 < C₀) (A Kc Cu N : NNReal)
    (P : ENNReal) :
    ENNReal.ofReal C₀ ^ M *
        (((A : ENNReal) * (Cu : ENNReal) * (N : ENNReal)) * (Kc : ENNReal) ^ (M - 1) * P)
      ≤ ENNReal.ofReal (C₀ * ((A : ℝ) + 1) * ((Kc : ℝ) + 1)) ^ M *
          ((Cu : ENNReal) * (N : ENNReal)) * P := by
  have hRHS_factor : ENNReal.ofReal (C₀ * ((A : ℝ) + 1) * ((Kc : ℝ) + 1)) =
      ENNReal.ofReal C₀ * ((A + 1 : NNReal) : ENNReal) * ((Kc + 1 : NNReal) : ENNReal) := by
    rw [ENNReal.ofReal_mul (mul_nonneg hC₀.le (by positivity)), ENNReal.ofReal_mul hC₀.le]
    push_cast
    simp [ENNReal.ofReal_add]
  have hA_ineq : (A : ENNReal) ≤ ((A + 1 : NNReal) : ENNReal) ^ M :=
    le_trans (by exact_mod_cast le_self_add (a := A) (b := (1 : NNReal)))
      (le_self_pow (by simp) hM.ne')
  have hKc_ineq : (Kc : ENNReal) ^ (M - 1) ≤ ((Kc + 1 : NNReal) : ENNReal) ^ M :=
    le_trans (ENNReal.pow_le_pow_left (by exact_mod_cast le_self_add))
      (pow_le_pow_right' (by simp) (Nat.sub_le M 1))
  calc
    ENNReal.ofReal C₀ ^ M
          * (((A : ENNReal) * (Cu : ENNReal) * (N : ENNReal)) * (Kc : ENNReal) ^ (M - 1) * P)
        = ENNReal.ofReal C₀ ^ M * ((A : ENNReal) * (Kc : ENNReal) ^ (M - 1))
            * ((Cu : ENNReal) * (N : ENNReal)) * P := by ring
    _ ≤ ENNReal.ofReal C₀ ^ M
            * (((A + 1 : NNReal) : ENNReal) ^ M * ((Kc + 1 : NNReal) : ENNReal) ^ M)
            * ((Cu : ENNReal) * (N : ENNReal)) * P := by
      gcongr
    _ = ENNReal.ofReal (C₀ * ((A : ℝ) + 1) * ((Kc : ℝ) + 1)) ^ M
          * ((Cu : ENNReal) * (N : ENNReal)) * P := by
      rw [hRHS_factor, mul_pow, mul_pow]; ring

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- A chain body at a node level lies in the ball of radius `9 = R + 3` (with `R = 6`): the node
lies in the `4σ`-rescale of any of its `δ`-tubes, which is in the unit ball. -/
theorem node_rescale_carrier_subset_closedBall {δ σ ρ : NNReal}
    (V : Tube σ E) (Tl : Tube δ E) (hball : Tl.carrier ⊆ Metric.closedBall (0 : E) 1)
    (hTV : Tl.toConvexSpaceBody ≤ V.toConvexSpaceBody)
    (hσρ : σ ≤ ρ) (hσ1 : (σ : ℝ) ≤ 1) (hρ2 : (ρ : ℝ) ≤ 2) :
    (V.rescale ρ).carrier ⊆ Metric.closedBall (0 : E) 9 := by
  have hτ : ((4 * σ + ρ : NNReal) : ℝ) ≤ 6 := by push_cast; linarith
  exact (SetLike.coe_subset_coe.mpr
    (node_rescale_le_leaf_rescale Tl V hσρ le_rfl hTV)).trans
    (leaf_rescale_carrier_subset_closedBall Tl hball hτ)

/-- **The Katz–Tao input of a node-to-node gap.**  A set `Fw` of fine (level-`kb`) nodes each
sharing a `δ`-tube with a fixed coarse (level-`ka`) node `𝒰.cover.tube ka p` is contained in
`gapNodeIndex 𝒰 kb ℓp (5 σ_ka)` for any `δ`-tube `T ℓp` of that coarse node, so a Katz–Tao bound
for the latter transfers to `Fw`, and to its inflated bodies up to `katzTaoRescaleConst E`. -/
theorem isKatzTao_node_fibre {ι : Type u} {δ : NNReal}
    {s : Finset ι} {T : ι → Tube δ E} {Cu : NNReal} {N : ℕ} {σ : ℕ → NNReal}
    (𝒰 : ChainUniformTubeSet s T N σ Cu) {ka kb : ℕ}
    {ρb : NNReal}
    (hσb : 0 < σ kb) (hbρ : σ kb ≤ ρb) (hρb2 : ρb ≤ 2 * σ kb) (hρb1 : ρb ≤ 1)
    (hδb : δ ≤ 4 * σ kb) (h45 : 4 * σ ka + 4 * σ kb ≤ 5 * σ ka)
    {Δ : ENNReal} {p ℓp : ι}
    (hℓpp : (T ℓp).toConvexSpaceBody ≤ (𝒰.cover.tube ka p).toConvexSpaceBody)
    (hKT : ConvexSpaceBody.IsKatzTao (gapNodeIndex 𝒰 kb ℓp (5 * σ ka))
      (fun j => (𝒰.cover.tube kb j).toConvexSpaceBody) Δ)
    (Fw : Finset ι) (hFw : Fw ⊆ 𝒰.cover.indexSet kb)
    (hfib : ∀ w ∈ Fw, ∃ i, (T i).toConvexSpaceBody ≤ (𝒰.cover.tube kb w).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ (𝒰.cover.tube ka p).toConvexSpaceBody) :
    ConvexSpaceBody.IsKatzTao Fw (fun w => ((𝒰.cover.tube kb w).rescale ρb).toConvexSpaceBody)
      ((katzTaoRescaleConst E : ENNReal) * Δ) := by
  have hsub : Fw ⊆ gapNodeIndex 𝒰 kb ℓp (5 * σ ka) := by
    rw [gapNodeIndex_eq_filter 𝒰 kb ℓp (5 * σ ka)]
    intro w hw
    obtain ⟨i, hi_w, hi_p⟩ := hfib w hw
    exact Finset.mem_filter.mpr ⟨hFw hw,
      node_body_le_leaf_rescale_of_shared_tube (𝒰.cover.tube ka p) (𝒰.cover.tube kb w) (T i)
        (T ℓp) hδb h45 hi_w hi_p hℓpp⟩
  refine isKatzTao_rescale_le Fw (𝒰.cover.tube kb) hσb hbρ hρb2 hρb1 ?_
  simpa [Tube.toConvexSpaceBody_rescale_self] using hKT.subset hsub

/-- **The Katz–Tao input of the finest gap.**  `isKatzTao_node_fibre` with the leaves in place of
the fine nodes: a set `Fw` of `δ`-tubes of a fixed level-`ka` node is `A · Cu² · N_kl · Δ`-Katz–Tao
as soon as the `δ`-*node* family inside `T_{ℓp}^{(5σ_ka)}` is `Δ`-Katz–Tao, where `kl` is the level
of the bundle sitting at the leaf scale, `σ kl = δ`. -/
theorem exists_isKatzTao_leaf_fibre :
    ∃ A : NNReal, 0 < A ∧
      ∀ {ι : Type u} {N : ℕ} {σ : ℕ → NNReal} {ka kl : ℕ} {δ : NNReal},
        0 < δ → (δ : ℝ) ≤ 1 → kl ≤ N → σ kl = δ →
      ∀ {s : Finset ι} {T : ι → Tube δ E} {Cu : NNReal}
        (𝒰 : ChainUniformTubeSet s T N σ Cu), 1 ≤ Cu →
      4 * σ ka + 4 * σ kl ≤ 5 * σ ka →
      ∀ {Δ : ENNReal} {p ℓp : ι},
        (T ℓp).toConvexSpaceBody ≤ (𝒰.cover.tube ka p).toConvexSpaceBody →
        ConvexSpaceBody.IsKatzTao (gapNodeIndex 𝒰 kl ℓp (5 * σ ka))
          (fun j => (𝒰.cover.tube kl j).toConvexSpaceBody) Δ →
      ∀ (Fw : Finset ι), Fw ⊆ s →
        (∀ w ∈ Fw, (T w).toConvexSpaceBody ≤ (𝒰.cover.tube ka p).toConvexSpaceBody) →
        ConvexSpaceBody.IsKatzTao Fw (fun w => (T w).toConvexSpaceBody)
          ((A : ENNReal) * ((Cu ^ 2 : NNReal) : ENNReal) * (𝒰.branchingN kl : ENNReal) * Δ) :=
by
  obtain ⟨A, hA, hleafKT⟩ := exists_isKatzTao_leaf_of_isKatzTao_node (E := E)
  refine ⟨A, hA, ?_⟩
  intro ι N σ ka kl δ hδpos hδ1 hkl hν s T Cu 𝒰 hCu hθ Δ p ℓp hℓpp hKT Fw hFw hFw_body
  have hδb : δ ≤ 4 * σ kl := by rw [hν]; exact le_mul_of_one_le_left' (by norm_num)
  refine hleafKT hδpos hδ1 hkl hν 𝒰 hCu Fw (gapNodeIndex 𝒰 kl ℓp (5 * σ ka)) hFw ?_ hKT
  intro i hi j hj hTij
  rw [gapNodeIndex_eq_filter 𝒰 kl ℓp (5 * σ ka)]
  exact Finset.mem_filter.mpr ⟨hj,
    node_body_le_leaf_rescale_of_shared_tube (𝒰.cover.tube ka p) (𝒰.cover.tube kl j) (T i)
      (T ℓp) hδb hθ hTij (hFw_body i hi) hℓpp⟩

end MultiScaleFac

end Kakeya
