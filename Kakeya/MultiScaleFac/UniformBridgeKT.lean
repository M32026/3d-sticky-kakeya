/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.RefineKT
public import Kakeya.MultiScaleFac.Assembly
public import Kakeya.Uniform.ParentBodyDensity

/-!
# Translating the Katz–Tao stopping time into the node language

The Katz–Tao counterpart of the node translations of `Kakeya/MultiScaleFac/Bridge.lean`, and vastly
cheaper than them.

`Kakeya.maxDensity` is a supremum of densities over *all* test bodies, so it carries no anchor of
its own: a container enters only by selecting an index set, and `Δ_max` is monotone in that set.
Consequently both directions of the node translation in half (B) are plain set inclusions —
upper bounds by shrinking the index set, the lower bound by enlarging it — with no volume
comparison and no constant.  Half (A) needed a whole bridge layer for the same two steps, because
`C_F` is a *ratio* anchored at a test body and moving the anchor costs volume comparisons.

The two inclusions are:

* `nodesUnder b a j ⊆ gapNodeIndex (u b) i₀ (5 σ_a)` for any member `i₀` of the class of `j`.  The
  factor `5` in the container convention of `MultiScaleFac.BlockKatzTaoAt` was chosen for exactly
  this: `T i₀ ≤ tube a j` gives `tube a j ≤ (T i₀)^{(4σ_a)}` by `Tube.rescale_le_of_le`, and
  `4 ≤ 5`.
* `gapNodeIndex (u c) i₀ (5 σ_a) ⊆ nodesIn c ((tube a j)^{(8σ_a)})`, which is why the lower bound of
  alternative (ii) is stated on a dilate of the anchor node: the stopping time delivers its bound on
  the `5σ_a`-thickening of a *leaf*, a container five times thicker than `tube a j`, so the
  inclusion runs the wrong way for a lower bound until the anchor is dilated.  Chasing
  `T i₀ ≤ tube a j` gives `(T i₀)^{(5σ_a)} ⊆ (tube a j)^{(6σ_a)}`; `8` is taken to match half (A)
  and for room.
-/

@[expose] public section

open MeasureTheory Real Metric ConvexSpaceBody
open Tube

namespace Kakeya

open StickyKakeya


universe u

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

variable {ι : Type*} {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cv : NNReal}

namespace MultiScaleFac

open _root_.StickyKakeya




end MultiScaleFac

section  -- Declarations lie in the root `Tube` namespace.
open MultiScaleFac


omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem _root_.Tube.GridUniform.toUniformTubeSet_cover (𝒢 : GridUniform t T N Cv) :
    𝒢.toUniformTubeSet.cover = 𝒢.cover := rfl


end

namespace MultiScaleFac

open _root_.StickyKakeya

section TopScaleCount

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A tube of radius at least one contains the ambient ball.**  A `ρ`-tube is the
`ρ`-neighbourhood of a unit-length core, so one whose core starts at the origin contains
`closedBall 0 ρ`, hence `closedBall 0 1` once `1 ≤ ρ`.  The radius is a parameter rather than fixed
at `1` so that the lemma applies at `gridScale δ N 0`, which equals `1` but not syntactically. -/
theorem exists_tube_superset_closedBall (ρ : NNReal) (hρ : 1 ≤ ρ) :
    ∃ V : Tube ρ E, Metric.closedBall (0 : E) 1 ⊆ V.carrier := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hvne : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have he_norm : ‖(‖v‖⁻¹ • v)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvne]
  have hdist : dist (0 : E) (‖v‖⁻¹ • v) = 1 := by
    simp [dist_eq_norm, he_norm]
  refine ⟨Tube.mk' ρ hdist, ?_⟩
  have h0 : (0 : E) ∈ segment ℝ (Tube.mk' ρ hdist).x (Tube.mk' ρ hdist).y := by
    rw [Tube.mk'_x]
    exact left_mem_segment ℝ _ _
  refine subset_trans ?_ (Tube.closedBall_subset_carrier_of_mem_segment _ h0)
  exact Metric.closedBall_subset_closedBall (by exact_mod_cast hρ)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The top grid scale carries boundedly many nodes.**  At `k = 0` the grid scale is `1` and some
`1`-tube `V` contains the whole ambient ball, so every member of `s` lies in `V`; every node of
`parent 0` has a nonempty class, hence shares a member with `V`, and Definition 2.1(ii) applied to
`V` counts all of `parent 0`.  This is the total-node-count hypothesis of GWZ Lemma 7.4. -/
theorem card_parent_zero_le {s : Finset ι} {C : NNReal} (𝒰 : UniformTubeSet s T N C)
    (hs : s.Nonempty) (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) :
    ((𝒰.cover.indexSet 0).card : NNReal) ≤ C := by
  classical
  have hgs : (1 : NNReal) ≤ gridScale δ N 0 := by rw [gridScale_zero]
  obtain ⟨V, hV⟩ := exists_tube_superset_closedBall (E := E) (gridScale δ N 0) hgs
  have hbo := 𝒰.boundedOverlap 0 (Nat.zero_le N) V
  refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) hbo
  intro j hj
  rw [Finset.mem_filter]
  refine ⟨hj, ?_⟩
  obtain ⟨i, hi⟩ := coverClass_nonempty_of_mem_parent 𝒰 (Nat.zero_le N) hs hj
  simp only [coverClass, Finset.mem_filter] at hi
  obtain ⟨his, hij⟩ := hi
  refine ⟨i, his, ?_, ?_⟩
  · have h := 𝒰.cover.le_tube_assign 0 (Nat.zero_le N) i his
    rwa [hij] at h
  · refine SetLike.coe_subset_coe.mp ?_
    exact subset_trans (hball i his) hV

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Every node of the system lies in a fixed ball.**  A node contains a member, the members lie in
`B_1`, and a node tube has radius at most `1` and a unit-length core, so
`Tube.subset_ball_of_carrier_subset_ball` puts the node in `B_4`.  This is the containment
hypothesis of GWZ Lemma 7.4 for the node chain, at every level at once. -/
theorem node_carrier_subset_ball {s : Finset ι} {C : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (𝒰 : UniformTubeSet s T N C) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    {k : ℕ} (hk : k ≤ N) {j : ι} (hj : j ∈ 𝒰.cover.indexSet k) :
    (𝒰.cover.tube k j).carrier ⊆ Metric.closedBall (0 : E) 4 := by
  classical
  obtain ⟨i, hi⟩ := coverClass_nonempty_of_mem_parent 𝒰 hk hs hj
  simp only [coverClass, Finset.mem_filter] at hi
  obtain ⟨his, hij⟩ := hi
  have hcov : (T i).carrier ⊆ (𝒰.cover.tube k j).carrier := by
    have h := 𝒰.cover.le_tube_assign k hk i his
    rw [hij] at h
    exact SetLike.coe_subset_coe.mpr h
  have hmain := Tube.subset_ball_of_carrier_subset_ball hδ (gridScale_pos hδ N k)
    (T i) (𝒰.cover.tube k j) (hball i his) hcov
  refine subset_trans hmain (Metric.closedBall_subset_closedBall ?_)
  have hle : (gridScale δ N k : ℝ) ≤ 1 := by exact_mod_cast gridScale_le_one hδ1 N k
  linarith

end TopScaleCount

end MultiScaleFac

section  -- Declarations lie in the root `Tube` namespace.
open MultiScaleFac


/-- **The ancestor of a node at a coarser grid index.**  `GridCoverSystem` records the assignment of
*members* to nodes, not of nodes to nodes; the node map is recovered by following any member of the
node's class up to the coarser index.  Well-definedness is not needed — the choice is made once by
`Classical.choose` — only the two properties below, and both hold for any member. -/
noncomputable def _root_.Tube.UniformTubeSet.nodeAncestor {s : Finset ι} {C : NNReal}
    (𝒰 : UniformTubeSet s T N C) (b a : ℕ) (w : ι) : ι :=
  open scoped Classical in
  if h : (coverClass s (𝒰.cover.assign b) w).Nonempty then 𝒰.cover.assign a h.choose else w

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The witnessing member of a node used by `MultiScaleFac.UniformTubeSet.nodeAncestor`. -/
theorem _root_.Tube.UniformTubeSet.exists_nodeAncestor_witness {s : Finset ι} {C : NNReal}
    (𝒰 : UniformTubeSet s T N C) {b a : ℕ} (hb : b ≤ N) (hs : s.Nonempty)
    {w : ι} (hw : w ∈ 𝒰.cover.indexSet b) :
    ∃ i ∈ s, 𝒰.cover.assign b i = w ∧ 𝒰.nodeAncestor b a w = 𝒰.cover.assign a i := by
  classical
  have hne := coverClass_nonempty_of_mem_parent 𝒰 hb hs hw
  have hspec : hne.choose ∈ s ∧ 𝒰.cover.assign b hne.choose = w := by
    simpa [coverClass] using hne.choose_spec
  refine ⟨hne.choose, hspec.1, hspec.2, ?_⟩
  simp only [UniformTubeSet.nodeAncestor, dif_pos hne]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem _root_.Tube.UniformTubeSet.nodeAncestor_mem {s : Finset ι} {C : NNReal}
    (𝒰 : UniformTubeSet s T N C) {b a : ℕ} (ha : a ≤ N) (hb : b ≤ N) (hs : s.Nonempty)
    {w : ι} (hw : w ∈ 𝒰.cover.indexSet b) : 𝒰.nodeAncestor b a w ∈ 𝒰.cover.indexSet a := by
  obtain ⟨i, his, _, heq⟩ := 𝒰.exists_nodeAncestor_witness hb hs hw
  rw [heq]
  exact 𝒰.cover.assign_mem a ha i his

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- A node lies inside its ancestor at a coarser grid index: the iterated nesting
`MultiScaleFac.tube_assign_le_of_le` of the hierarchy, read on nodes. -/
theorem _root_.Tube.UniformTubeSet.tube_le_tube_nodeAncestor {s : Finset ι} {C : NNReal}
    (𝒰 : UniformTubeSet s T N C) {b a : ℕ} (hab : a ≤ b) (hb : b ≤ N) (hs : s.Nonempty)
    {w : ι} (hw : w ∈ 𝒰.cover.indexSet b) :
    (𝒰.cover.tube b w).toConvexSpaceBody
      ≤ (𝒰.cover.tube a (𝒰.nodeAncestor b a w)).toConvexSpaceBody := by
  obtain ⟨i, his, hwi, heq⟩ := 𝒰.exists_nodeAncestor_witness hb hs hw
  rw [heq, ← hwi]
  exact tube_assign_le_of_le 𝒰.cover hab hb his


end

namespace MultiScaleFac

open _root_.StickyKakeya

section TopScaleCount

end TopScaleCount

section Telescope

/-- **GWZ Lemma 7.4 on the node chain of a uniform set of tubes.**
`StickyKakeya.maxDensity_le_prod_of_uniform_at_scales` instantiated with the nodes of `𝒰` at grid
index `cuts (Fin.last M)` playing the part of the leaves: the chain is the grid scales at the
indices `cuts j`, the node families are the parents of `𝒰` there, and the projection is
`MultiScaleFac.UniformTubeSet.nodeAncestor`.  The leaf multiplicity is `1`. -/
theorem exists_maxDensity_parent_le_prod (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ Ceng : ℝ, 0 < Ceng ∧
      ∀ (N : ℕ), 0 < N →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s : Finset ι) (T : ι → Tube δ E), s.Nonempty →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (𝒰 : UniformTubeSet s T N Cu) (M : ℕ), 0 < M →
      ∀ cuts : Fin (M + 1) → ℕ, cuts 0 = 0 → (∀ j, cuts j ≤ N) → StrictMono cuts →
      ∀ Δ : Fin M → ENNReal, (∀ m, Δ m ≠ ⊤) →
      (∀ m : Fin M, ∀ p ∈ 𝒰.cover.indexSet (cuts m.castSucc),
        Kakeya.maxDensity (𝒰.nodesUnder (cuts m.succ) (cuts m.castSucc) p)
            (fun w => (𝒰.cover.tube (cuts m.succ) w).toConvexSpaceBody) ≤ Δ m) →
      Kakeya.maxDensity (𝒰.cover.indexSet (cuts (Fin.last M)))
          (fun w => (𝒰.cover.tube (cuts (Fin.last M)) w).toConvexSpaceBody)
        ≤ ENNReal.ofReal Ceng ^ M * ∏ m, Δ m := by
  classical
  obtain ⟨Ceng, hCeng, hmain⟩ :=
    Tube.ParentBodyDensity.maxDensity_le_prod_of_uniform_at_scales.{u, _} (E := E) 4 (by norm_num)
      ((Cu : ℝ) + 1) (by positivity)
  refine ⟨Ceng, hCeng, ?_⟩
  intro N hN ι δ hδ hδ1 hδ0 s T hs hball 𝒰 M hM cuts hcuts0 hcutsN hcutsMono Δ hΔtop hgap
  set ρ : Fin (M + 1) → NNReal := fun j => gridScale δ N (cuts j) with hρdef
  have hcutsMono' : Monotone cuts := hcutsMono.monotone
  have hρ0 : ρ 0 = 1 := by simp only [hρdef, hcuts0, gridScale_zero]
  have hρanti : Antitone ρ := by
    intro j j' hjj'
    exact gridScale_antitone hδ hδ1 N (hcutsMono' hjj')
  have hρsep : ∀ m : Fin M, 4 * ρ m.succ ≤ ρ m.castSucc := by
    intro m
    have hlt : cuts m.castSucc < cuts m.succ := hcutsMono (Fin.castSucc_lt_succ (i := m))
    have h16 := sixteen_mul_gridScale_le hδ hδ1 hδ0 hlt (hcutsN m.succ)
    calc 4 * ρ m.succ ≤ 16 * ρ m.succ := by
          simp only [hρdef]
          gcongr
          norm_num
      _ ≤ ρ m.castSucc := h16
  have hnode : ∀ j : Fin (M + 1), ∀ w ∈ 𝒰.cover.indexSet (cuts j),
      (𝒰.cover.tube (cuts j) w).carrier ⊆ Metric.closedBall (0 : E) 4 :=
    fun j w hw => node_carrier_subset_ball hδ hδ1 𝒰 hs hball (hcutsN j) hw
  refine le_trans (hmain (δ := ρ (Fin.last M)) (gridScale_pos hδ N _)
    (by exact_mod_cast gridScale_le_one hδ1 N _)
    (𝒰.cover.indexSet (cuts (Fin.last M))) (𝒰.cover.tube (cuts (Fin.last M)))
    (fun w hw => hnode (Fin.last M) w hw) M hM ρ (by rw [hρ0]) (by rw [hρ0]; norm_num) rfl
    hρanti hρsep (κ := fun j => ι) (fun j => 𝒰.cover.tube (cuts j))
    (fun j => 𝒰.cover.indexSet (cuts j))
    (fun m => 𝒰.nodeAncestor (cuts m.succ) (cuts m.castSucc))
    ?hprojmem ?hprojle ?hcard0 ?hballall ?hne id (fun i hi => hi) (fun i _ => le_rfl)
    (Set.injOn_id _) Δ hΔtop ?hKT) (le_refl _)
  case hprojmem =>
    intro m w hw
    exact 𝒰.nodeAncestor_mem (hcutsN m.castSucc) (hcutsN m.succ) hs hw
  case hprojle =>
    intro m w hw
    exact 𝒰.tube_le_tube_nodeAncestor (hcutsMono (Fin.castSucc_lt_succ (i := m))).le
      (hcutsN m.succ) hs hw
  case hcard0 =>
    have h := card_parent_zero_le 𝒰 hs hball
    have h' : ((𝒰.cover.indexSet 0).card : ℝ) ≤ (Cu : ℝ) := by exact_mod_cast h
    have hpow : (1 : ℝ) ≤ ((4 : ℝ) + 3) ^ (2 * Module.finrank ℝ E) := by
      apply one_le_pow₀; norm_num
    have hCu0 : (0 : ℝ) ≤ (Cu : ℝ) := Cu.coe_nonneg
    calc ((𝒰.cover.indexSet (cuts 0)).card : ℝ)
        = ((𝒰.cover.indexSet 0).card : ℝ) := by rw [hcuts0]
      _ ≤ (Cu : ℝ) := h'
      _ ≤ ((Cu : ℝ) + 1) * ((4 : ℝ) + 3) ^ (2 * Module.finrank ℝ E) := by nlinarith
  case hballall =>
    intro j w hw
    refine subset_trans (hnode j w hw) (Metric.closedBall_subset_closedBall ?_)
    norm_num
  case hne =>
    intro m
    obtain ⟨i, hi⟩ := hs
    exact ⟨𝒰.cover.assign (cuts m.castSucc) i,
      𝒰.cover.assign_mem (cuts m.castSucc) (hcutsN m.castSucc) i hi⟩
  case hKT =>
    intro m p hp
    refine le_trans (Kakeya.maxDensity_mono _ ?_) (hgap m p hp)
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [UniformTubeSet.nodesUnder_eq_nodesIn, UniformTubeSet.mem_nodesIn_iff]
    refine ⟨hw.1, ?_⟩
    have hle := 𝒰.tube_le_tube_nodeAncestor (hcutsMono (Fin.castSucc_lt_succ (i := m))).le
      (hcutsN m.succ) hs hw.1
    rwa [hw.2] at hle

/-- **The per-gap factors of the node chain telescope.**  Each gap contributes
`C (σ_{c_m}/σ_{c_{m+1}})^ζ`, and the ratios telescope to `σ_{c_0}/σ_{c_M}`.  Because every gap
carries the *same* exponent `ζ` — the constant does not grow along the Katz–Tao stopping time — the
product is a single power, with no accumulated loss beyond `C^M`. -/
theorem prod_gapFactor_eq (hδ : 0 < δ) {M : ℕ} (cuts : Fin (M + 1) → ℕ) (C : NNReal) (ζ : ℝ) :
    (∏ m : Fin M, (C : ENNReal) * ENNReal.ofReal
        (((gridScale δ N (cuts m.castSucc) : ℝ) / (gridScale δ N (cuts m.succ) : ℝ)) ^ ζ))
      = (C : ENNReal) ^ M * ENNReal.ofReal
        (((gridScale δ N (cuts 0) : ℝ) / (gridScale δ N (cuts (Fin.last M)) : ℝ)) ^ ζ) := by
  classical
  set ρ : Fin (M + 1) → NNReal := fun j => gridScale δ N (cuts j) with hρdef
  have hρpos : ∀ j, 0 < (ρ j : ℝ) := by
    intro j
    exact_mod_cast gridScale_pos hδ N (cuts j)
  set r : Fin M → ℝ := fun m => (ρ m.castSucc : ℝ) / (ρ m.succ : ℝ) with hrdef
  have hrnn : ∀ m : Fin M, 0 ≤ r m := fun m =>
    div_nonneg (hρpos m.castSucc).le (hρpos m.succ).le
  have hprod : (∏ m : Fin M, r m) = (ρ 0 : ℝ) / (ρ (Fin.last M) : ℝ) :=
    prod_ratio_telescope M ρ hρpos
  calc (∏ m : Fin M, (C : ENNReal) * ENNReal.ofReal (r m ^ ζ))
      = (C : ENNReal) ^ M * ∏ m : Fin M, ENNReal.ofReal (r m ^ ζ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = (C : ENNReal) ^ M * ENNReal.ofReal (∏ m : Fin M, r m ^ ζ) := by
        rw [ENNReal.ofReal_prod_of_nonneg (fun m _ => Real.rpow_nonneg (hrnn m) ζ)]
    _ = (C : ENNReal) ^ M * ENNReal.ofReal (((ρ 0 : ℝ) / (ρ (Fin.last M) : ℝ)) ^ ζ) := by
        rw [Real.finsetProd_rpow (s := (Finset.univ : Finset (Fin M))) (f := r)
          (fun m _ => hrnn m) ζ, hprod]

/-- The telescoped product at a chain starting from the top of the grid: with `cuts 0 = 0` the first
scale is `1`, so the product is `C^M · σ_{c_M}^{-ζ}`. -/
theorem prod_gapFactor_eq_of_start (hδ : 0 < δ) {M : ℕ} (cuts : Fin (M + 1) → ℕ)
    (hcuts0 : cuts 0 = 0) (C : NNReal) (ζ : ℝ) :
    (∏ m : Fin M, (C : ENNReal) * ENNReal.ofReal
        (((gridScale δ N (cuts m.castSucc) : ℝ) / (gridScale δ N (cuts m.succ) : ℝ)) ^ ζ))
      = (C : ENNReal) ^ M
        * ENNReal.ofReal ((gridScale δ N (cuts (Fin.last M)) : ℝ) ^ (-ζ)) := by
  rw [prod_gapFactor_eq hδ cuts C ζ, hcuts0, gridScale_zero]
  congr 2
  have hpos : (0 : ℝ) < (gridScale δ N (cuts (Fin.last M)) : ℝ) := by
    exact_mod_cast gridScale_pos hδ N (cuts (Fin.last M))
  rw [show ((1 : NNReal) : ℝ) / (gridScale δ N (cuts (Fin.last M)) : ℝ)
      = ((gridScale δ N (cuts (Fin.last M)) : ℝ))⁻¹ by
    rw [NNReal.coe_one, one_div]]
  rw [← Real.rpow_neg_one, ← Real.rpow_mul hpos.le, neg_one_mul]

/-- **The node-chain bound of GWZ Lemma 7.7(B), alternative (i), in the form the dichotomy uses.**
If every gap of the chain carries the block bound at the *same* exponent `ζ` and constant `C`, then
the node family at the bottom of the chain has `Δ_max ≤ (Ceng · C)^M · σ_{c_M}^{-ζ}`.  The whole
`M`-dependence is in the base, and `M ≤ N + 1` is `δ`-independent, so the factor is absorbed by any
positive power of `δ` below a threshold. -/
theorem exists_maxDensity_parent_le (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ Ceng : ℝ, 0 < Ceng ∧
      ∀ (N : ℕ), 0 < N →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s : Finset ι) (T : ι → Tube δ E), s.Nonempty →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (𝒰 : UniformTubeSet s T N Cu) (M : ℕ), 0 < M →
      ∀ cuts : Fin (M + 1) → ℕ, cuts 0 = 0 → (∀ j, cuts j ≤ N) → StrictMono cuts →
      ∀ (C : NNReal) (ζ : ℝ),
      (∀ m : Fin M, ∀ p ∈ 𝒰.cover.indexSet (cuts m.castSucc),
        Kakeya.maxDensity (𝒰.nodesUnder (cuts m.succ) (cuts m.castSucc) p)
            (fun w => (𝒰.cover.tube (cuts m.succ) w).toConvexSpaceBody)
          ≤ (C : ENNReal) * ENNReal.ofReal
              (((gridScale δ N (cuts m.castSucc) : ℝ)
                / (gridScale δ N (cuts m.succ) : ℝ)) ^ ζ)) →
      Kakeya.maxDensity (𝒰.cover.indexSet (cuts (Fin.last M)))
          (fun w => (𝒰.cover.tube (cuts (Fin.last M)) w).toConvexSpaceBody)
        ≤ (ENNReal.ofReal Ceng * (C : ENNReal)) ^ M
            * ENNReal.ofReal ((gridScale δ N (cuts (Fin.last M)) : ℝ) ^ (-ζ)) := by
  obtain ⟨Ceng, hCeng, hmain⟩ := exists_maxDensity_parent_le_prod.{u, _} (E := E) Cu hCu
  refine ⟨Ceng, hCeng, ?_⟩
  intro N hN ι δ hδ hδ1 hδ0 s T hs hball 𝒰 M hM cuts hcuts0 hcutsN hcutsMono C ζ hgap
  have h := hmain N hN hδ hδ1 hδ0 s T hs hball 𝒰 M hM cuts hcuts0 hcutsN hcutsMono
    (fun m => (C : ENNReal) * ENNReal.ofReal
      (((gridScale δ N (cuts m.castSucc) : ℝ) / (gridScale δ N (cuts m.succ) : ℝ)) ^ ζ))
    (fun m => ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) hgap
  rw [prod_gapFactor_eq_of_start hδ cuts hcuts0 C ζ] at h
  calc Kakeya.maxDensity (𝒰.cover.indexSet (cuts (Fin.last M)))
          (fun w => (𝒰.cover.tube (cuts (Fin.last M)) w).toConvexSpaceBody)
      ≤ ENNReal.ofReal Ceng ^ M * ((C : ENNReal) ^ M
          * ENNReal.ofReal ((gridScale δ N (cuts (Fin.last M)) : ℝ) ^ (-ζ))) := h
    _ = (ENNReal.ofReal Ceng * (C : ENNReal)) ^ M
          * ENNReal.ofReal ((gridScale δ N (cuts (Fin.last M)) : ℝ) ^ (-ζ)) := by
        rw [mul_pow]; ring

end Telescope

section ShortGap

end ShortGap

end MultiScaleFac

section  -- Declarations lie in the root `Tube` namespace.
open MultiScaleFac


omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The nesting of the hierarchy, iterated.**  Members sharing a node at a fine grid index share
their nodes at every coarser index; `GridCoverSystem.nested` is the single step. -/
theorem _root_.Tube.GridCoverSystem.assign_eq_of_assign_eq {s : Finset ι}
    (𝒞 : GridCoverSystem s T N)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ N) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (h : 𝒞.assign b i = 𝒞.assign b j) : 𝒞.assign a i = 𝒞.assign a j := by
  have hmain : ∀ d : ℕ, a + d ≤ N → 𝒞.assign (a + d) i = 𝒞.assign (a + d) j →
      𝒞.assign a i = 𝒞.assign a j := by
    intro d
    induction d with
    | zero => intro _ h0; simpa using h0
    | succ e ih =>
        intro hle he
        refine ih (by omega) ?_
        exact 𝒞.nested (a + e) (by omega) i hi j hj (by simpa [← Nat.add_assoc] using he)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hab
  subst hd
  exact hmain d hb h

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Passing to a finer index only increases the number of nodes under a fixed node.**  Every
`k`-node under `p` has a member whose `b`-node is again under `p` and has the given `k`-node as its
ancestor, so `MultiScaleFac.UniformTubeSet.nodeAncestor` maps the `b`-nodes under `p` *onto* the
`k`-nodes under `p`.  The `k`-ancestor is independent of which member is chosen. -/
theorem _root_.Tube.UniformTubeSet.card_nodesUnder_le_of_le {s : Finset ι} {C : NNReal}
    (𝒰 : UniformTubeSet s T N C) (hs : s.Nonempty) {a k b : ℕ} (hkb : k ≤ b) (hb : b ≤ N)
    {p : ι} :
    (𝒰.nodesUnder k a p).card ≤ (𝒰.nodesUnder b a p).card := by
  classical
  have hkN : k ≤ N := le_trans hkb hb
  refine Finset.card_le_card_of_surjOn (𝒰.nodeAncestor b k) ?_
  intro w hw
  simp only [Finset.mem_coe] at hw ⊢
  rw [UniformTubeSet.nodesUnder_eq_nodesIn, UniformTubeSet.mem_nodesIn_iff] at hw
  obtain ⟨hwp, hwle⟩ := hw
  have hne := coverClass_nonempty_of_mem_parent 𝒰 hkN hs hwp
  have hspec : hne.choose ∈ s ∧ 𝒰.cover.assign k hne.choose = w := by
    simpa [coverClass] using hne.choose_spec
  obtain ⟨hi_s, hi_w⟩ := hspec
  refine ⟨𝒰.cover.assign b hne.choose, ?_, ?_⟩
  · simp only [Finset.mem_coe]
    rw [UniformTubeSet.nodesUnder_eq_nodesIn, UniformTubeSet.mem_nodesIn_iff]
    refine ⟨𝒰.cover.assign_mem b hb _ hi_s, ?_⟩
    refine le_trans ?_ hwle
    have h := tube_assign_le_of_le 𝒰.cover hkb hb hi_s
    rwa [hi_w] at h
  · obtain ⟨i', hi'_s, hi'_eq, hanc⟩ :=
      𝒰.exists_nodeAncestor_witness (a := k) hb hs (𝒰.cover.assign_mem b hb _ hi_s)
    rw [hanc]
    have := 𝒰.cover.assign_eq_of_assign_eq hkb hb hi'_s hi_s hi'_eq
    rw [this, hi_w]


end

namespace MultiScaleFac

open _root_.StickyKakeya

section ShortGap

omit [Nontrivial E] in
/-- **The crude bound on a short gap.**  Over a *short* block the count at an interior index is
dominated by the count at the far end (`card_nodesUnder_le_of_le`), and `Δ_max` is at most that
count.  This is what supplies the per-gap datum at a grid index that is not a cut of the stopping
time, the implicit loss `(σ_a/σ_b)^{n-1}` being subpolynomial because the block is short. -/
theorem maxDensity_nodesUnder_le_card_far {s : Finset ι} {C : NNReal}
    (𝒰 : UniformTubeSet s T N C) (hs : s.Nonempty) {a k b : ℕ} (hkb : k ≤ b) (hb : b ≤ N)
    {p : ι} :
    Kakeya.maxDensity (𝒰.nodesUnder k a p)
        (fun w => (𝒰.cover.tube k w).toConvexSpaceBody)
      ≤ ((𝒰.nodesUnder b a p).card : ENNReal) := by
  refine le_trans (Kakeya.maxDensity_le_card _ _) ?_
  exact_mod_cast 𝒰.card_nodesUnder_le_of_le hs hkb hb

end ShortGap

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The nodes of a grid-uniform system under a node of a coarser scale lie in the container of
`MultiScaleFac.BlockKatzTaoAt` anchored at any member of that node's class.  This is the inclusion
the *upper* bounds of alternative (ii) transport along. -/
theorem nodesUnder_subset_gapNodeIndex_core (_hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (𝒞 : GridUniformCore t T N Cv) {Cw : NNReal} {𝒱 : Tube.UniformTubeSet t T N Cw}
    (hcov : 𝒱.cover = 𝒞.cover)
    {a b : ℕ} (_ha : a ≤ N) (hb : b ≤ N) (_hab : a ≤ b) {j i₀ : ι}
    (hi₀ : (T i₀).toConvexSpaceBody ≤ (𝒞.cover.tube a j).toConvexSpaceBody) :
    𝒱.nodesUnder b a j
      ⊆ gapNodeIndexAtScale (𝒞.uniformAt b hb) i₀ (5 * gridScale δ N a) := by
  classical
  intro j' hj'
  rw [UniformTubeSet.nodesUnder_eq_nodesIn, UniformTubeSet.mem_nodesIn_iff] at hj'
  simp only [hcov] at hj'
  obtain ⟨hj'p, hj'le⟩ := hj'
  have hj'p' : j' ∈ (𝒞.uniformAt b hb).parent := by
    rw [𝒞.parent_eq b hb]; exact hj'p
  have h4 : (𝒞.cover.tube a j).toConvexSpaceBody
      ≤ ((T i₀).rescale (4 * gridScale δ N a)).toConvexSpaceBody :=
    Tube.rescale_le_of_le (T i₀) (𝒞.cover.tube a j) hi₀
  have h45 : ((T i₀).rescale (4 * gridScale δ N a)).toConvexSpaceBody
      ≤ ((T i₀).rescale (5 * gridScale δ N a)).toConvexSpaceBody :=
    Tube.rescale_le_rescale_of_radius_le (T i₀) (by gcongr; norm_num)
  simp only [gapNodeIndexAtScale, Kakeya.familyIn, Finset.mem_filter]
  refine ⟨hj'p', ?_⟩
  rw [𝒞.tube_eq b hb j' hj'p]
  exact le_trans hj'le (le_trans h4 h45)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The original, derived from the core sibling**.  Statement
unchanged; the proof routes through `GridUniformCore`, which a bare `Tube.UniformTubeSet` supplies
(`Kakeya.ML2Core.towerUniformAtScaleData_of_uniformTubeSet`, at `Cu³` -- (2)
corrects the `Cu²`: `GridUniformCore.le_card_class` is tight, which forces the branching number
over at `branchingN/Cu` and costs the third power.  `δ`-free either way, so no exponent account
moves). -/
theorem nodesUnder_subset_gapNodeIndex (hδ : 0 < δ) (hδ1 : δ ≤ 1) (𝒢 : GridUniform t T N Cv)
    {a b : ℕ} (ha : a ≤ N) (hb : b ≤ N) (hab : a ≤ b) {j i₀ : ι}
    (hi₀ : (T i₀).toConvexSpaceBody ≤ (𝒢.cover.tube a j).toConvexSpaceBody) :
    𝒢.toUniformTubeSet.nodesUnder b a j
      ⊆ gapNodeIndexAtScale (𝒢.uniformAt b hb) i₀ (5 * gridScale δ N a) :=
  nodesUnder_subset_gapNodeIndex_core hδ hδ1 𝒢.toGridUniformCore rfl ha hb hab hi₀

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The container of `MultiScaleFac.BlockKatzTaoAt` anchored at a member of a node's class lies
inside the `8σ_a`-dilate of that node.  This is the inclusion the *lower* bound of alternative (ii)
transports along, and it is why that bound is stated on the dilate rather than on the node. -/
theorem gapNodeIndex_subset_nodesIn_core (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 < N)
    (𝒞 : GridUniformCore t T N Cv) {Cw : NNReal}
    {𝒱 : Tube.UniformTubeSet t T N Cw} (hcov : 𝒱.cover = 𝒞.cover)
    {a c : ℕ} (ha : a ≤ N) (hc : c ≤ N) {j i₀ : ι}
    (hi₀ : (T i₀).toConvexSpaceBody ≤ (𝒞.cover.tube a j).toConvexSpaceBody) :
    gapNodeIndexAtScale (𝒞.uniformAt c hc) i₀ (5 * gridScale δ N a)
      ⊆ 𝒱.nodesIn c
          (((𝒞.cover.tube a j).rescale (8 * gridScale δ N a)).toConvexSpaceBody) := by
  classical
  have hσapos : 0 < gridScale δ N a := gridScale_pos hδ N a
  intro j' hj'
  simp only [gapNodeIndexAtScale, Kakeya.familyIn, Finset.mem_filter] at hj'
  obtain ⟨hj'p, hj'le⟩ := hj'
  have hj'c : j' ∈ 𝒞.cover.indexSet c := by rwa [𝒞.parent_eq c hc] at hj'p
  have hδσ : δ ≤ gridScale δ N a := by
    have h := gridScale_antitone hδ hδ1 N ha
    rwa [gridScale_self δ hN] at h
  have hδle : δ ≤ 5 * gridScale δ N a := by
    calc δ ≤ gridScale δ N a := hδσ
      _ ≤ 5 * gridScale δ N a := by nlinarith [hσapos.le]
  have hθ : gridScale δ N a + 5 * gridScale δ N a ≤ 8 * gridScale δ N a := by
    nlinarith [hσapos.le]
  have hchase : ((T i₀).rescale (5 * gridScale δ N a)).toConvexSpaceBody
      ≤ ((𝒞.cover.tube a j).rescale (8 * gridScale δ N a)).toConvexSpaceBody :=
    Tube.rescale_le_rescale_of_body_le (T i₀) (𝒞.cover.tube a j) hδle hθ hi₀
  rw [UniformTubeSet.mem_nodesIn_iff]
  simp only [hcov]
  refine ⟨hj'c, ?_⟩
  rw [← 𝒞.tube_eq c hc j' hj'c]
  exact le_trans hj'le hchase

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The original, derived from the core sibling.**  Statement unchanged. -/
theorem gapNodeIndex_subset_nodesIn (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 < N)
    (𝒢 : GridUniform t T N Cv)
    {a c : ℕ} (ha : a ≤ N) (hc : c ≤ N) {j i₀ : ι}
    (hi₀ : (T i₀).toConvexSpaceBody ≤ (𝒢.cover.tube a j).toConvexSpaceBody) :
    gapNodeIndexAtScale (𝒢.uniformAt c hc) i₀ (5 * gridScale δ N a)
      ⊆ 𝒢.toUniformTubeSet.nodesIn c
          (((𝒢.cover.tube a j).rescale (8 * gridScale δ N a)).toConvexSpaceBody) :=
  gapNodeIndex_subset_nodesIn_core hδ hδ1 hN 𝒢.toGridUniformCore rfl ha hc hi₀

omit [Nontrivial E] in
/-- **Alternative (ii)-2 of GWZ Lemma 7.7(B), translated.**  The per-anchor block bound of the
stopping time, read on the nodes under a node of the coarse scale.  No constant is paid: this is
`MultiScaleFac.nodesUnder_subset_gapNodeIndex` followed by monotonicity of `Δ_max`. -/
theorem maxDensity_nodesUnder_le_of_blockKatzTaoAt_core (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (𝒞 : GridUniformCore t T N Cv) {Cw : NNReal}
    {𝒱 : Tube.UniformTubeSet t T N Cw} (hcov : 𝒱.cover = 𝒞.cover)
    {a b : ℕ} (ha : a ≤ N) (hb : b ≤ N) (hab : a ≤ b) {j i₀ : ι}
    (_hjp : j ∈ 𝒞.cover.indexSet a)
    (hi₀ : (T i₀).toConvexSpaceBody ≤ (𝒞.cover.tube a j).toConvexSpaceBody)
    {C : NNReal} {ζ : ℝ} (h : BlockKatzTaoAt 𝒞.uniformAt C ζ a b i₀) :
    Kakeya.maxDensity (𝒱.nodesUnder b a j)
        (fun j' => (𝒞.cover.tube b j').toConvexSpaceBody)
      ≤ (C : ENNReal) * ENNReal.ofReal
          (((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ ζ) := by
  classical
  refine le_trans (maxDensity_le_of_subset_of_eqOn
    (nodesUnder_subset_gapNodeIndex_core hδ hδ1 𝒞 hcov ha hb hab hi₀) ?_) (h hb)
  intro j' hj'
  rw [UniformTubeSet.nodesUnder_eq_nodesIn, UniformTubeSet.mem_nodesIn_iff] at hj'
  simp only [hcov] at hj'
  rw [𝒞.tube_eq b hb j' hj'.1]

omit [Nontrivial E] in
/-- **The original, derived from the core sibling.**  Statement unchanged. -/
theorem maxDensity_nodesUnder_le_of_blockKatzTaoAt (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (𝒢 : GridUniform t T N Cv) {a b : ℕ} (ha : a ≤ N) (hb : b ≤ N) (hab : a ≤ b) {j i₀ : ι}
    (hjp : j ∈ 𝒢.cover.indexSet a)
    (hi₀ : (T i₀).toConvexSpaceBody ≤ (𝒢.cover.tube a j).toConvexSpaceBody)
    {C : NNReal} {ζ : ℝ} (h : BlockKatzTaoAt 𝒢.uniformAt C ζ a b i₀) :
    Kakeya.maxDensity (𝒢.toUniformTubeSet.nodesUnder b a j)
        (fun j' => (𝒢.cover.tube b j').toConvexSpaceBody)
      ≤ (C : ENNReal) * ENNReal.ofReal
          (((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ ζ) :=
  maxDensity_nodesUnder_le_of_blockKatzTaoAt_core hδ hδ1 𝒢.toGridUniformCore rfl ha hb hab hjp hi₀ h

omit [Nontrivial E] in
/-- **Alternative (ii)-3 of GWZ Lemma 7.7(B), translated.**  A lower bound on the node family of
the stopping time's container is a lower bound on the node family of the dilated anchor node, again
at no cost: this is `MultiScaleFac.gapNodeIndex_subset_nodesIn` followed by monotonicity of
`Δ_max`. -/
theorem maxDensity_gapNodeIndex_le_maxDensity_nodesIn_core (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 < N)
    (𝒞 : GridUniformCore t T N Cv) {Cw : NNReal}
    {𝒱 : Tube.UniformTubeSet t T N Cw} (hcov : 𝒱.cover = 𝒞.cover)
    {a c : ℕ} (ha : a ≤ N) (hc : c ≤ N) {j i₀ : ι}
    (hi₀ : (T i₀).toConvexSpaceBody ≤ (𝒞.cover.tube a j).toConvexSpaceBody) :
    Kakeya.maxDensity (gapNodeIndexAtScale (𝒞.uniformAt c hc) i₀ (5 * gridScale δ N a))
        (fun j' => ((𝒞.uniformAt c hc).parentTube j').toConvexSpaceBody)
      ≤ Kakeya.maxDensity
          (𝒱.nodesIn c
            (((𝒞.cover.tube a j).rescale (8 * gridScale δ N a)).toConvexSpaceBody))
          (fun j' => (𝒞.cover.tube c j').toConvexSpaceBody) := by
  classical
  refine maxDensity_le_of_subset_of_eqOn
    (gapNodeIndex_subset_nodesIn_core hδ hδ1 hN 𝒞 hcov ha hc hi₀) ?_
  intro j' hj'
  have hj'p : j' ∈ (𝒞.uniformAt c hc).parent := by
    simpa [gapNodeIndexAtScale, Kakeya.familyIn] using (Finset.mem_filter.mp hj').1
  have hj'c : j' ∈ 𝒞.cover.indexSet c := by rwa [𝒞.parent_eq c hc] at hj'p
  rw [𝒞.tube_eq c hc j' hj'c]

omit [Nontrivial E] in
/-- **The original, derived from the core sibling.**  Statement unchanged. -/
theorem maxDensity_gapNodeIndex_le_maxDensity_nodesIn (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 < N)
    (𝒢 : GridUniform t T N Cv) {a c : ℕ} (ha : a ≤ N) (hc : c ≤ N) {j i₀ : ι}
    (hi₀ : (T i₀).toConvexSpaceBody ≤ (𝒢.cover.tube a j).toConvexSpaceBody) :
    Kakeya.maxDensity (gapNodeIndexAtScale (𝒢.uniformAt c hc) i₀ (5 * gridScale δ N a))
        (fun j' => ((𝒢.uniformAt c hc).parentTube j').toConvexSpaceBody)
      ≤ Kakeya.maxDensity
          (𝒢.toUniformTubeSet.nodesIn c
            (((𝒢.cover.tube a j).rescale (8 * gridScale δ N a)).toConvexSpaceBody))
          (fun j' => (𝒢.cover.tube c j').toConvexSpaceBody) :=
  maxDensity_gapNodeIndex_le_maxDensity_nodesIn_core hδ hδ1 hN 𝒢.toGridUniformCore rfl ha hc hi₀

section CoarseChain

/-- **The cut indices at or below `k`, with `k` adjoined.**  The chain of GWZ Lemma 7.4 for the node
family at grid index `k` must start at `0` and end at `k`, so it is enumerated from this set rather
than from the cut set itself.  Mirror of `MultiScaleFac.restrictCuts`, which keeps the fine side. -/
def coarseCuts (S : Finset ℕ) (k : ℕ) : Finset ℕ := insert k (S.filter (fun x => x ≤ k))

/-- **The chain of grid indices from the top of the grid down to `k`.**  Enumerating
`MultiScaleFac.coarseCuts` gives a strictly increasing family `0 = c_0 < … < c_M = k` in which every
`c_m` with `m < M` is a cut of `S`, and no cut lies strictly between consecutive members.  So every
gap of the chain is a gap of the cut set except possibly the last, which lies in a *short* block. -/
theorem exists_coarseChain {S : Finset ℕ} {k : ℕ} (h0 : 0 ∈ S) (hk0 : 0 < k) :
    ∃ (M : ℕ) (cuts : Fin (M + 1) → ℕ), 0 < M ∧ cuts 0 = 0 ∧ cuts (Fin.last M) = k ∧
      StrictMono cuts ∧ (∀ j, cuts j ≤ k) ∧
      (∀ m : Fin M, cuts m.castSucc ∈ S) ∧
      (∀ m : Fin M, cuts m.succ ∈ S ∨ cuts m.succ = k) ∧
      (∀ m : Fin M, ∀ x ∈ S, ¬(cuts m.castSucc < x ∧ x < cuts m.succ)) := by
  classical
  have hk_mem : k ∈ coarseCuts S k := Finset.mem_insert_self _ _
  have h0_mem : (0 : ℕ) ∈ coarseCuts S k :=
    Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨h0, Nat.zero_le k⟩)
  have hcases : ∀ x ∈ coarseCuts S k, x = k ∨ x ∈ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact Or.inl rfl
    · exact Or.inr (Finset.mem_filter.mp hx').1
  have hmem_le : ∀ x ∈ coarseCuts S k, x ≤ k := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact le_rfl
    · exact (Finset.mem_filter.mp hx').2
  have hmem_of : ∀ x ∈ S, x ≤ k → x ∈ coarseCuts S k := fun x hx hle =>
    Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hx, hle⟩)
  have hsub : coarseCuts S k ⊆ Finset.range (k + 1) := fun x hx =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (hmem_le x hx))
  have hcard2 : 2 ≤ (coarseCuts S k).card := by
    have hpair : ({0, k} : Finset ℕ) ⊆ coarseCuts S k := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact h0_mem
      · rw [Finset.mem_singleton] at hx'; rw [hx']; exact hk_mem
    have hcp : ({0, k} : Finset ℕ).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
    calc 2 = ({0, k} : Finset ℕ).card := hcp.symm
      _ ≤ (coarseCuts S k).card := Finset.card_le_card hpair
  obtain ⟨M, hM⟩ : ∃ M, (coarseCuts S k).card = M + 1 :=
    ⟨(coarseCuts S k).card - 1, by omega⟩
  have hMpos : 0 < M := by omega
  have hfine_le : ∀ m : Fin M, ((coarseCuts S k).orderIsoOfFin hM m.succ : ℕ) ≤ k :=
    fun m => hmem_le _ ((coarseCuts S k).orderIsoOfFin hM m.succ).property
  have hcoarse : ∀ m : Fin M, ((coarseCuts S k).orderIsoOfFin hM m.castSucc : ℕ) ∈ S := by
    intro m
    have hlt := (orderIsoOfFin_castSucc_lt_succ hM m).1
    have hne : ((coarseCuts S k).orderIsoOfFin hM m.castSucc : ℕ) ≠ k :=
      Nat.ne_of_lt (lt_of_lt_of_le hlt (hfine_le m))
    rcases hcases _ ((coarseCuts S k).orderIsoOfFin hM m.castSucc).property with heq | hmem'
    · exact absurd heq hne
    · exact hmem'
  have hfine : ∀ m : Fin M,
      ((coarseCuts S k).orderIsoOfFin hM m.succ : ℕ) ∈ S ∨
        ((coarseCuts S k).orderIsoOfFin hM m.succ : ℕ) = k := by
    intro m
    rcases hcases _ ((coarseCuts S k).orderIsoOfFin hM m.succ).property with heq | hmem'
    · exact Or.inr heq
    · exact Or.inl hmem'
  have hadj : ∀ m : Fin M, ∀ x ∈ S,
      ¬(((coarseCuts S k).orderIsoOfFin hM m.castSucc : ℕ) < x ∧
        x < ((coarseCuts S k).orderIsoOfFin hM m.succ : ℕ)) := by
    intro m x hxS hlt
    have hxk : x ≤ k := le_trans (Nat.le_of_lt hlt.2) (hfine_le m)
    exact (orderIsoOfFin_castSucc_lt_succ hM m).2 x (hmem_of x hxS hxk) hlt
  exact ⟨M, fun j => ((coarseCuts S k).orderIsoOfFin hM j : ℕ), hMpos,
    orderIsoOfFin_zero_eq hM h0_mem, orderIsoOfFin_last_eq hM hk_mem hsub,
    fun i j hij => ((coarseCuts S k).orderIsoOfFin hM).lt_iff_lt.mpr hij,
    fun j => orderIsoOfFin_le hM hsub j, hcoarse, hfine, hadj⟩

end CoarseChain

section CrudeGap

/-- **The crude gap factor.**  The ratio of the two node-scale volumes, times the dimensional
tube-volume ratio.  Over a *short* block `σ_a/σ_b ≤ δ^{-(ε + 2/N)}`, so this is subpolynomial. -/
noncomputable def crudeGapFactor (δ : NNReal) (N a b : ℕ) : ENNReal :=
  (tubeVolRatio (E := E) : ENNReal)
    * ENNReal.ofReal
        (((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ (Module.finrank ℝ E - 1))

/-- **The count of nodes under a node, from the block bound at that gap.**
`MultiScaleFac.card_nodesUnder_mul_le_densityIn` compares the count with the density of those nodes
inside the anchor node, and that density is at most `Δ_max` of the family, hence at most the block
bound.  Left in multiplied form; the division is done once, in `maxDensity_nodesUnder_le_crude`. -/
theorem card_nodesUnder_mul_le_of_maxDensity_le {t : Finset ι} {Cv : NNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (𝒰 : UniformTubeSet t T N Cv) {a b : ℕ} (ha : a ≤ N)
    {p : ι} {Δ : ENNReal}
    (h : Kakeya.maxDensity (𝒰.nodesUnder b a p)
          (fun w => (𝒰.cover.tube b w).toConvexSpaceBody) ≤ Δ) :
    ((𝒰.nodesUnder b a p).card : ENNReal)
        * (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
            * ((gridScale δ N b : ENNReal) ^ (Module.finrank ℝ E - 1)))
      ≤ Δ * (((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
            * ((gridScale δ N a : ENNReal) ^ (Module.finrank ℝ E - 1))) := by
  refine le_trans (card_nodesUnder_mul_le_densityIn hδ hδ1 𝒰 ha) ?_
  exact mul_le_mul_left (le_trans (Kakeya.le_maxDensity _ _ _) h) _

/-- **The crude datum for a gap that is not a gap of the cut set.**  For `k ≤ b` the `k`-nodes under
a node are at most as many as the `b`-nodes under it, `Δ_max` is at most that count, and the count
is controlled by the block bound at the gap `(a,b)` at the price of one volume ratio.  This supplies
the last gap of the chain when the index being bounded is not a cut of the stopping time. -/
theorem maxDensity_nodesUnder_le_crude {t : Finset ι} {Cv : NNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (𝒰 : UniformTubeSet t T N Cv) (hs : t.Nonempty)
    {a k b : ℕ} (ha : a ≤ N) (hkb : k ≤ b) (hb : b ≤ N) {p : ι} {Δ : ENNReal}
    (h : Kakeya.maxDensity (𝒰.nodesUnder b a p)
          (fun w => (𝒰.cover.tube b w).toConvexSpaceBody) ≤ Δ) :
    Kakeya.maxDensity (𝒰.nodesUnder k a p)
        (fun w => (𝒰.cover.tube k w).toConvexSpaceBody)
      ≤ Δ * crudeGapFactor (E := E) δ N a b := by
  classical
  have hcnpos : 0 < Tube.le_volume.c (Module.finrank ℝ E) :=
    Tube.le_volume.c_pos (Module.finrank ℝ E)
  have hσb : (0 : NNReal) < gridScale δ N b := gridScale_pos hδ N b
  have hc0 : ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
      * ((gridScale δ N b : ENNReal) ^ (Module.finrank ℝ E - 1)) ≠ 0 :=
    mul_ne_zero (by simpa using hcnpos.ne') (pow_ne_zero _ (by simpa using hσb.ne'))
  have hctop : ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
      * ((gridScale δ N b : ENNReal) ^ (Module.finrank ℝ E - 1)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hcrude : crudeGapFactor (E := E) δ N a b
      = (tubeVolRatio (E := E) : ENNReal)
          * ((gridScale δ N a / gridScale δ N b : NNReal) : ENNReal)
              ^ (Module.finrank ℝ E - 1) := by
    rw [crudeGapFactor]
    congr 1
    rw [← NNReal.coe_div, ENNReal.ofReal_pow (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  have hkey : Tube.volume_le.C (Module.finrank ℝ E)
        * gridScale δ N a ^ (Module.finrank ℝ E - 1)
      = tubeVolRatio (E := E) * (gridScale δ N a / gridScale δ N b) ^ (Module.finrank ℝ E - 1)
          * (Tube.le_volume.c (Module.finrank ℝ E)
              * gridScale δ N b ^ (Module.finrank ℝ E - 1)) := by
    rw [tubeVolRatio, div_pow]
    field_simp
  refine le_trans (maxDensity_nodesUnder_le_card_far 𝒰 hs hkb hb) ?_
  refine (ENNReal.mul_le_mul_iff_left hc0 hctop).mp ?_
  refine le_trans (card_nodesUnder_mul_le_of_maxDensity_le hδ hδ1 𝒰 ha h) ?_
  rw [hcrude, mul_assoc]
  refine mul_le_mul_right (le_of_eq ?_) Δ
  calc ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
        * ((gridScale δ N a : ENNReal) ^ (Module.finrank ℝ E - 1))
      = ((Tube.volume_le.C (Module.finrank ℝ E)
            * gridScale δ N a ^ (Module.finrank ℝ E - 1) : NNReal) : ENNReal) := by
        push_cast; ring
    _ = ((tubeVolRatio (E := E) * (gridScale δ N a / gridScale δ N b) ^ (Module.finrank ℝ E - 1)
          * (Tube.le_volume.c (Module.finrank ℝ E)
              * gridScale δ N b ^ (Module.finrank ℝ E - 1)) : NNReal) : ENNReal) := by
        rw [hkey]
    _ = (tubeVolRatio (E := E) : ENNReal)
          * ((gridScale δ N a / gridScale δ N b : NNReal) : ENNReal)
              ^ (Module.finrank ℝ E - 1)
        * (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
            * ((gridScale δ N b : ENNReal) ^ (Module.finrank ℝ E - 1))) := by
        push_cast; ring

end CrudeGap

section AlternativeOne

/-- At the top of the grid the node density is at most the node count, which is at most the
uniformity constant (`MultiScaleFac.card_parent_zero_le`).  This is the base case of the chain: the
chain of GWZ Lemma 7.4 has no gaps at `k = 0`. -/
theorem maxDensity_parent_zero_le {t : Finset ι} {C : NNReal} (𝒰 : UniformTubeSet t T N C)
    (hs : t.Nonempty) (hball : ∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) :
    Kakeya.maxDensity (𝒰.cover.indexSet 0) (fun w => (𝒰.cover.tube 0 w).toConvexSpaceBody)
      ≤ (C : ENNReal) := by
  refine le_trans (Kakeya.maxDensity_le_card _ _) ?_
  exact_mod_cast card_parent_zero_le 𝒰 hs hball

/-- **The node-density bound at a cut index, over `GridUniformCore`** (route (a)).  The `GridUniform`-phrased original below is the special case
`Cw := uniformTubeSetCuOf Cv`, `𝒱 := 𝒢.toUniformTubeSet`, `hcov := rfl`.  Here the uniform tube
set is a *parameter*, so a bare `Tube.UniformTubeSet t T N Cu` and the `GridUniformCore t T N Cu²`
that `towerUniformAtScaleData_of_uniformTubeSet` builds from it can be supplied directly.

**Why `Cw` is a theorem parameter rather than a `∀` binder.**  This is not a binder swap: the
statement opens `∃ Cbig : NNReal, 1 ≤ Cbig ∧ ∀ …`, and `Cbig` is built from the uniformity
constant of the tube set, so that constant cannot be bound *after* it.  Hoisting `Cw` to the left
of the existential is what makes the dependence expressible at all.

**The constant, named.**  Write `Ceng Cw` for the engine constant that
`exists_maxDensity_parent_le` returns at `Cw`.  Then

  `Cbig = 1 + Cv + Real.toNNReal (Ceng Cw) + Cw`,

linear in `Cw` above a `Cw`-dependent engine constant.  At the `Cu²` reading (`Cv := Cu ^ 2`, `Cw := Cu`) this is `1 + Cu ^ 2 + Real.toNNReal (Ceng Cu) + Cu`: **the squaring is
paid once, in `Cv`, and the chain does not compound it** — the `N + 1` power is taken of
`Cbig * (1 + Ct)` exactly as in the original.  No `δ`-exponent moves (`Cu` is absolute at
every site this landing reaches, so `Cu²` is `δ`-free).

**On-path through `MultiScaleFac/Ports.lean:336` only.**  The sole consumer of the original is
`alternative_two_of_terminal_blockKT_grid` (`Ports.lean:373`).  It is *not* reached through
`exists_maxDensity_parent_le_of_index`, which builds its own chain; so both need a core form and
neither is redundant — do not prune this one as subsumed. -/
theorem exists_maxDensity_parent_le_of_cutIndex_core (Cv Cw : NNReal)
    (_hCv : 1 ≤ Cv) (hCw : 1 ≤ Cw) :
    ∃ Cbig : NNReal, 1 ≤ Cbig ∧
      ∀ (N : ℕ), 0 < N →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (t : Finset ι) (T : ι → Tube δ E), t.Nonempty →
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (𝒞 : GridUniformCore t T N Cv) (𝒱 : Tube.UniformTubeSet t T N Cw),
        𝒱.cover = 𝒞.cover →
      ∀ (Ct : NNReal) (ζ : ℝ),
      ∀ S : Finset ℕ, 0 ∈ S →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
        BlockKatzTaoOn t 𝒞.uniformAt Ct ζ a b) →
      ∀ k, k ∈ S → k ≤ N →
      Kakeya.maxDensity (𝒞.cover.indexSet k)
          (fun w => (𝒞.cover.tube k w).toConvexSpaceBody)
        ≤ ((Cbig * (1 + Ct) : NNReal) : ENNReal) ^ (N + 1)
            * ENNReal.ofReal ((gridScale δ N k : ℝ) ^ (-ζ)) := by
  classical
  have hCu : (1 : NNReal) ≤ Cw := hCw
  obtain ⟨Ceng, hCeng, hmain⟩ :=
    exists_maxDensity_parent_le.{u, _} (E := E) (Cw) hCu
  have hone : (1 : NNReal)
      ≤ 1 + Cv + Real.toNNReal Ceng + Cw := by
    calc (1 : NNReal) ≤ 1 + Cv := self_le_add_right _ _
      _ ≤ 1 + Cv + Real.toNNReal Ceng := self_le_add_right _ _
      _ ≤ _ := self_le_add_right _ _
  refine ⟨1 + Cv + Real.toNNReal Ceng + Cw, hone, ?_⟩
  intro N hN ι δ hδ hδ1 hδ0 t T hs hball 𝒞 𝒱 hcov Ct ζ S h0 hblocks k hkS hkN
  set Cbig : NNReal := 1 + Cv + Real.toNNReal Ceng + Cw with hCbig
  have hCbig1 : (1 : NNReal) ≤ Cbig := hCbig ▸ hone
  have hCt1 : (1 : NNReal) ≤ 1 + Ct := self_le_add_right _ _
  have hbase1 : (1 : NNReal) ≤ Cbig * (1 + Ct) := one_le_mul hCbig1 hCt1
  have hbase1' : (1 : ENNReal) ≤ ((Cbig * (1 + Ct) : NNReal) : ENNReal) := by
    exact_mod_cast hbase1
  have hCuCbig : Cw ≤ Cbig := by
    rw [hCbig]; exact le_add_self
  have hCu_le : Cw ≤ Cbig * (1 + Ct) := by
    calc Cw ≤ Cbig := hCuCbig
      _ = Cbig * 1 := by rw [mul_one]
      _ ≤ Cbig * (1 + Ct) := by gcongr
  have hCengR : Ceng ≤ ((Cbig : NNReal) : ℝ) := by
    rw [hCbig]
    push_cast
    rw [Real.coe_toNNReal Ceng hCeng.le]
    have h1 : (0 : ℝ) ≤ (Cv : ℝ) := Cv.coe_nonneg
    have h2 : (0 : ℝ) ≤ ((Cw : NNReal) : ℝ) :=
      (Cw).coe_nonneg
    linarith
  have hCengE : ENNReal.ofReal Ceng ≤ ((Cbig : NNReal) : ENNReal) := by
    calc ENNReal.ofReal Ceng ≤ ENNReal.ofReal ((Cbig : NNReal) : ℝ) :=
          ENNReal.ofReal_le_ofReal hCengR
      _ = ((Cbig : NNReal) : ENNReal) := ENNReal.ofReal_coe_nnreal
  by_cases hk0 : k = 0
  · subst hk0
    have hzero := maxDensity_parent_zero_le (N := N) 𝒱 hs hball
    simp only [hcov] at hzero
    refine le_trans hzero ?_
    rw [gridScale_zero]
    simp only [NNReal.coe_one, Real.one_rpow, ENNReal.ofReal_one, mul_one]
    calc ((Cw : NNReal) : ENNReal)
        ≤ ((Cbig * (1 + Ct) : NNReal) : ENNReal) := by exact_mod_cast hCu_le
      _ = ((Cbig * (1 + Ct) : NNReal) : ENNReal) ^ 1 := by rw [pow_one]
      _ ≤ ((Cbig * (1 + Ct) : NNReal) : ENNReal) ^ (N + 1) :=
        pow_le_pow_right₀ hbase1' (by omega)
  · have hk0' : 0 < k := Nat.pos_of_ne_zero hk0
    obtain ⟨M, cuts, hMpos, hcuts0, hcutsLast, hStrict, hcutsLek, hcoarse, hfine, hadj⟩ :=
      exists_coarseChain h0 hk0'
    have hcutsN : ∀ j, cuts j ≤ N := fun j => le_trans (hcutsLek j) hkN
    have hMN : M ≤ N := by
      have hinj : Function.Injective cuts := hStrict.injective
      have himg : (Finset.univ : Finset (Fin (M + 1))).image cuts ⊆ Finset.range (N + 1) := by
        intro x hx
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hj ▸ hcutsN j))
      have hcard : ((Finset.univ : Finset (Fin (M + 1))).image cuts).card = M + 1 := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      have hle := Finset.card_le_card himg
      rw [hcard, Finset.card_range] at hle
      omega
    have hgap : ∀ m : Fin M, ∀ p ∈ 𝒱.cover.indexSet (cuts m.castSucc),
        Kakeya.maxDensity
            (𝒱.nodesUnder (cuts m.succ) (cuts m.castSucc) p)
            (fun w => (𝒱.cover.tube (cuts m.succ) w).toConvexSpaceBody)
          ≤ (Ct : ENNReal) * ENNReal.ofReal
              (((gridScale δ N (cuts m.castSucc) : ℝ)
                / (gridScale δ N (cuts m.succ) : ℝ)) ^ ζ) := by
      intro m p hp
      simp only [hcov] at hp ⊢
      have haS : cuts m.castSucc ∈ S := hcoarse m
      have hcS : cuts m.succ ∈ S := by
        rcases hfine m with hmem | heq
        · exact hmem
        · rw [heq]; exact hkS
      have hac : cuts m.castSucc < cuts m.succ := hStrict (Fin.castSucc_lt_succ (i := m))
      have hblk := hblocks _ haS _ hcS hac (hadj m)
      have hne := coverClass_nonempty_of_mem_parent 𝒱 (hcutsN m.castSucc) hs
        (by simpa [hcov] using hp)
      have hspec : hne.choose ∈ t ∧ 𝒞.cover.assign (cuts m.castSucc) hne.choose = p := by
        simpa [coverClass, hcov] using hne.choose_spec
      have hile : (T hne.choose).toConvexSpaceBody
          ≤ (𝒞.cover.tube (cuts m.castSucc) p).toConvexSpaceBody := by
        have := 𝒞.cover.le_tube_assign (cuts m.castSucc) (hcutsN m.castSucc) _ hspec.1
        rwa [hspec.2] at this
      exact maxDensity_nodesUnder_le_of_blockKatzTaoAt_core hδ hδ1 𝒞 hcov (hcutsN m.castSucc)
        (hcutsN m.succ) hac.le hp hile (hblk _ hspec.1)
    have hchain := hmain N hN hδ hδ1 hδ0 t T hs hball 𝒱 M hMpos cuts hcuts0
      hcutsN hStrict Ct ζ hgap
    rw [hcutsLast] at hchain
    simp only [hcov] at hchain
    refine le_trans hchain (mul_le_mul_left ?_ _)
    calc (ENNReal.ofReal Ceng * (Ct : ENNReal)) ^ M
        ≤ ((Cbig * (1 + Ct) : NNReal) : ENNReal) ^ M := by
          refine pow_le_pow_left' ?_ M
          calc ENNReal.ofReal Ceng * (Ct : ENNReal)
              ≤ ((Cbig : NNReal) : ENNReal) * (((1 + Ct : NNReal)) : ENNReal) := by
                refine mul_le_mul' hCengE ?_
                exact_mod_cast le_add_self (a := Ct) (b := (1 : NNReal))
            _ = ((Cbig * (1 + Ct) : NNReal) : ENNReal) := by push_cast; ring
      _ ≤ ((Cbig * (1 + Ct) : NNReal) : ENNReal) ^ (N + 1) :=
          pow_le_pow_right₀ hbase1' (by omega)

/-- **The node-density bound at a cut index.**  Every gap of the chain
`MultiScaleFac.exists_coarseChain` for a *cut* index `k` is a gap of the cut set, so every gap
carries the block bound at the same exponent and `MultiScaleFac.exists_maxDensity_parent_le` applies
verbatim.  The chain has at most `N + 1` members, so the accumulated constant is `δ`-independent.

**The statement is unchanged**; the proof is now one line through
`exists_maxDensity_parent_le_of_cutIndex_core` at `Cw := uniformTubeSetCuOf Cv`. -/
theorem exists_maxDensity_parent_le_of_cutIndex (Cv : NNReal)
    (hCv : 1 ≤ Cv) :
    ∃ Cbig : NNReal, 1 ≤ Cbig ∧
      ∀ (N : ℕ), 0 < N →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (t : Finset ι) (T : ι → Tube δ E), t.Nonempty →
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (𝒢 : GridUniform t T N Cv) (Ct : NNReal) (ζ : ℝ),
      ∀ S : Finset ℕ, 0 ∈ S →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
        BlockKatzTaoOn t 𝒢.uniformAt Ct ζ a b) →
      ∀ k, k ∈ S → k ≤ N →
      Kakeya.maxDensity (𝒢.cover.indexSet k)
          (fun w => (𝒢.cover.tube k w).toConvexSpaceBody)
        ≤ ((Cbig * (1 + Ct) : NNReal) : ENNReal) ^ (N + 1)
            * ENNReal.ofReal ((gridScale δ N k : ℝ) ^ (-ζ)) := by
  obtain ⟨Cbig, hCbig1, h⟩ :=
    exists_maxDensity_parent_le_of_cutIndex_core.{u, _} (E := E) Cv
      (uniformTubeSetCuOf (E := E) Cv) hCv (le_trans hCv (le_max_left _ _))
  refine ⟨Cbig, hCbig1, ?_⟩
  intro N hN ι δ hδ hδ1 hδ0 t T hs hball 𝒢 Ct ζ S h0 hblocks k hkS hkN
  exact h N hN hδ hδ1 hδ0 t T hs hball 𝒢.toGridUniformCore 𝒢.toUniformTubeSet rfl Ct ζ
    S h0 hblocks k hkS hkN

end AlternativeOne

section AlternativeOneGeneral

/-- **The node chain telescope with one exceptional gap.**  As
`MultiScaleFac.exists_maxDensity_parent_le`, except that the *last* gap is allowed an extra factor
`Gb` — what the chain of `exists_coarseChain` needs when the index being bounded is not a cut.  The
factor is isolated rather than folded into the constant because `Gb` is subpolynomial in `δ` while
`Gb^{N+1}` is not. -/
theorem exists_maxDensity_parent_le_extra (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ Ceng : ℝ, 0 < Ceng ∧
      ∀ (N : ℕ), 0 < N →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (s : Finset ι) (T : ι → Tube δ E), s.Nonempty →
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (𝒰 : UniformTubeSet s T N Cu) (M : ℕ), 0 < M →
      ∀ cuts : Fin (M + 1) → ℕ, cuts 0 = 0 → (∀ j, cuts j ≤ N) → StrictMono cuts →
      ∀ (C : NNReal) (ζ : ℝ) (Gb : ENNReal), Gb ≠ ⊤ →
      (∀ m : Fin M, ∀ p ∈ 𝒰.cover.indexSet (cuts m.castSucc),
        Kakeya.maxDensity (𝒰.nodesUnder (cuts m.succ) (cuts m.castSucc) p)
            (fun w => (𝒰.cover.tube (cuts m.succ) w).toConvexSpaceBody)
          ≤ (C : ENNReal) * ENNReal.ofReal
                (((gridScale δ N (cuts m.castSucc) : ℝ)
                  / (gridScale δ N (cuts m.succ) : ℝ)) ^ ζ)
              * (if m.succ = Fin.last M then Gb else 1)) →
      Kakeya.maxDensity (𝒰.cover.indexSet (cuts (Fin.last M)))
          (fun w => (𝒰.cover.tube (cuts (Fin.last M)) w).toConvexSpaceBody)
        ≤ (ENNReal.ofReal Ceng * (C : ENNReal)) ^ M * Gb
            * ENNReal.ofReal ((gridScale δ N (cuts (Fin.last M)) : ℝ) ^ (-ζ)) := by
  obtain ⟨Ceng, hCeng, hmain⟩ := exists_maxDensity_parent_le_prod.{u, _} (E := E) Cu hCu
  refine ⟨Ceng, hCeng, ?_⟩
  intro N hN ι δ hδ hδ1 hδ0 s T hs hball 𝒰 M hM cuts hcuts0 hcutsN hcutsMono C ζ Gb hGbtop hgap
  set f : Fin M → ENNReal := fun m => (C : ENNReal) * ENNReal.ofReal
    (((gridScale δ N (cuts m.castSucc) : ℝ) / (gridScale δ N (cuts m.succ) : ℝ)) ^ ζ) with hfdef
  set g : Fin M → ENNReal := fun m => if m.succ = Fin.last M then Gb else 1 with hgdef
  have htop : ∀ m : Fin M, f m * g m ≠ ⊤ := by
    intro m
    apply ENNReal.mul_ne_top
    · rw [hfdef]
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
    · by_cases h : m.succ = Fin.last M
      · simp [hgdef, h, hGbtop]
      · simp [hgdef, h, ENNReal.one_ne_top]
  have h := hmain N hN hδ hδ1 hδ0 s T hs hball 𝒰 M hM cuts hcuts0 hcutsN hcutsMono
    (fun m => f m * g m) htop hgap
  rw [Finset.prod_mul_distrib] at h
  rw [prod_gapFactor_eq_of_start hδ cuts hcuts0 C ζ] at h
  set m₀ : Fin M := ⟨M - 1, by omega⟩ with hm₀
  have hm₀val : m₀.val = M - 1 := by simp [hm₀]
  have hlast0 : m₀.succ = Fin.last M := by
    apply Fin.ext
    rw [Fin.val_succ, Fin.val_last]
    omega
  have hgm0 : g m₀ = Gb := by
    simp [hgdef, hlast0]
  have hg_one : ∀ b : Fin M, b ≠ m₀ → g b = 1 := by
    intro b hbne
    rw [hgdef]
    simp [show b.succ ≠ Fin.last M by
      intro hsucc
      apply hbne
      apply Fin.ext
      have hval : b.val + 1 = M := by
        have hs : (b.succ : ℕ) = (Fin.last M : ℕ) := congrArg Fin.val hsucc
        rw [Fin.val_succ, Fin.val_last] at hs
        exact hs
      omega]
  have hprod₀ : ∀ b ∈ (Finset.univ : Finset (Fin M)), b ≠ m₀ → g b = 1 := by
    intro b _ hbne
    exact hg_one b hbne
  have hprod₁ : m₀ ∉ (Finset.univ : Finset (Fin M)) → g m₀ = 1 := by
    intro h; exact False.elim (h (by simp))
  have hprodig : (∏ m : Fin M, g m) = g m₀ :=
    Finset.prod_eq_single (s := (Finset.univ : Finset (Fin M))) (f := g) m₀ hprod₀ hprod₁
  have hprodg : (∏ m : Fin M, g m) = Gb := by
    rw [hprodig, hgm0]
  rw [hprodg] at h
  calc Kakeya.maxDensity (𝒰.cover.indexSet (cuts (Fin.last M)))
          (fun w => (𝒰.cover.tube (cuts (Fin.last M)) w).toConvexSpaceBody)
      ≤ ENNReal.ofReal Ceng ^ M * (((C : ENNReal) ^ M
          * ENNReal.ofReal ((gridScale δ N (cuts (Fin.last M)) : ℝ) ^ (-ζ))) * Gb) := h
    _ = (ENNReal.ofReal Ceng * (C : ENNReal)) ^ M * Gb
          * ENNReal.ofReal ((gridScale δ N (cuts (Fin.last M)) : ℝ) ^ (-ζ)) := by
        rw [mul_pow]; ring

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The short-gap factor is subpolynomial.**  Over a gap `(a,b)` of length `b - a ≤ εN + 1` the
two ingredients of the crude datum — the ratio `(σ_k/σ_b)^ζ` and `MultiScaleFac.crudeGapFactor` —
are both powers of `σ_a/σ_b = δ^{-(b-a)/N} ≤ δ^{-(ε + 1/N)}`, so their product is
`δ^{-(ζ + n - 1)(ε + 1/N)}` up to a dimensional ratio: about `2.05 ε` when `n = 3` and `ζ ≤ ε`. -/
theorem shortGapExtra_le {ε ζ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hNpos : 0 < N)
    (hζ : 0 ≤ ζ) {a k b : ℕ} (hak : a ≤ k) (_hkb : k ≤ b)
    (hshort : (b : ℝ) - (a : ℝ) ≤ ε * (N : ℝ) + 1) :
    ENNReal.ofReal (((gridScale δ N k : ℝ) / (gridScale δ N b : ℝ)) ^ ζ)
        * crudeGapFactor (E := E) δ N a b
      ≤ ((tubeVolRatio (E := E) : NNReal) : ENNReal)
          * ENNReal.ofReal ((δ : ℝ) ^
              (-((ζ + ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) * (ε + 1 / (N : ℝ))))) := by
  unfold crudeGapFactor
  set n1 : ℕ := Module.finrank ℝ E - 1
  set ν : ℝ := ε + 1 / (N : ℝ) with hν
  have hδ0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδ1' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hσa : (0 : ℝ) ≤ (gridScale δ N a : ℝ) := by exact_mod_cast (gridScale_pos hδ N a).le
  have hσk : (0 : ℝ) ≤ (gridScale δ N k : ℝ) := by exact_mod_cast (gridScale_pos hδ N k).le
  have hσb : (0 : ℝ) < (gridScale δ N b : ℝ) := by exact_mod_cast gridScale_pos hδ N b
  have hσb' : (0 : ℝ) ≤ (gridScale δ N b : ℝ) := hσb.le
  have hσk_div_b : (0 : ℝ) ≤ ((gridScale δ N k : ℝ) / (gridScale δ N b : ℝ)) :=
    div_nonneg hσk hσb'
  have hσa_div_b : (0 : ℝ) ≤ ((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) :=
    div_nonneg hσa hσb'
  have hdiv : ((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) =
      (δ : ℝ) ^ (-(((b : ℝ) - (a : ℝ)) / (N : ℝ))) := by
    rw [← NNReal.coe_div, gridScale_div_gridScale hδ N a b, NNReal.coe_rpow]
  have hle1 : ((b : ℝ) - (a : ℝ)) / (N : ℝ) ≤ ε + 1 / (N : ℝ) := by
    have h0 : ((b : ℝ) - (a : ℝ)) / (N : ℝ) ≤ (ε * (N : ℝ) + 1) / (N : ℝ) :=
      div_le_div_of_nonneg_right hshort hN0.le
    have h1 : (ε * (N : ℝ) + 1) / (N : ℝ) = ε + 1 / (N : ℝ) := by
      field_simp [hN0.ne']
    rwa [h1] at h0
  have hexp : -ν ≤ -(((b : ℝ) - (a : ℝ)) / (N : ℝ)) := by
    rw [hν]
    exact neg_le_neg hle1
  have hbase : ((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ≤ (δ : ℝ) ^ (-ν) := by
    rw [hdiv]
    exact Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1' hexp
  have hka : ((gridScale δ N k : ℝ) / (gridScale δ N b : ℝ)) ≤
      ((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) := by
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast gridScale_antitone hδ hδ1 N hak) hσb'
  have hk2 : ((gridScale δ N k : ℝ) / (gridScale δ N b : ℝ)) ≤ (δ : ℝ) ^ (-ν) :=
    le_trans hka hbase
  have hpow_ζ : ((gridScale δ N k : ℝ) / (gridScale δ N b : ℝ)) ^ ζ ≤ ((δ : ℝ) ^ (-ν)) ^ ζ := by
    exact Real.rpow_le_rpow hσk_div_b hk2 hζ
  have hpow_n1 : ((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ n1 ≤
      ((δ : ℝ) ^ (-ν)) ^ n1 := by
    exact pow_le_pow_left₀ hσa_div_b hbase n1
  have hrhs : ((δ : ℝ) ^ (-ν)) ^ ζ * ((δ : ℝ) ^ (-ν)) ^ n1 =
      (δ : ℝ) ^ (-((ζ + (n1 : ℝ)) * ν)) := by
    rw [← Real.rpow_mul (le_of_lt hδ0) (-ν) ζ]
    rw [← Real.rpow_natCast ((δ : ℝ) ^ (-ν)) n1]
    rw [← Real.rpow_mul (le_of_lt hδ0) (-ν) (n1 : ℝ)]
    rw [← Real.rpow_add hδ0]
    have heqexp : (-ν) * ζ + (-ν) * (n1 : ℝ) = -((ζ + (n1 : ℝ)) * ν) := by ring
    exact congrArg (fun e : ℝ => (δ : ℝ) ^ e) heqexp
  have hml : ((gridScale δ N k : ℝ) / (gridScale δ N b : ℝ)) ^ ζ *
        ((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ n1
      ≤ (δ : ℝ) ^ (-((ζ + (n1 : ℝ)) * ν)) := by
    calc
      ((gridScale δ N k : ℝ) / (gridScale δ N b : ℝ)) ^ ζ *
            ((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ n1
          ≤ ((δ : ℝ) ^ (-ν)) ^ ζ * ((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ n1 := by
              exact mul_le_mul_of_nonneg_right hpow_ζ (pow_nonneg hσa_div_b n1)
      _ ≤ ((δ : ℝ) ^ (-ν)) ^ ζ * ((δ : ℝ) ^ (-ν)) ^ n1 := by
              exact mul_le_mul_of_nonneg_left hpow_n1
                (Real.rpow_nonneg (Real.rpow_nonneg (le_of_lt hδ0) (-ν)) ζ)
      _ = (δ : ℝ) ^ (-((ζ + (n1 : ℝ)) * ν)) := hrhs
  have hnonneg_ζ : (0 : ℝ) ≤ ((gridScale δ N k : ℝ) / (gridScale δ N b : ℝ)) ^ ζ :=
    Real.rpow_nonneg hσk_div_b ζ
  calc
    ENNReal.ofReal (((gridScale δ N k : ℝ) / (gridScale δ N b : ℝ)) ^ ζ)
        * (tubeVolRatio * ENNReal.ofReal (((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ n1))
        = tubeVolRatio * (ENNReal.ofReal (((gridScale δ N k : ℝ) / (gridScale δ N b : ℝ)) ^ ζ)
            * ENNReal.ofReal (((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ n1)) := by
          ring
    _ = tubeVolRatio * ENNReal.ofReal (((gridScale δ N k : ℝ) / (gridScale δ N b : ℝ)) ^ ζ
        * ((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ n1) := by
          rw [← ENNReal.ofReal_mul hnonneg_ζ]
    _ ≤ tubeVolRatio * ENNReal.ofReal ((δ : ℝ) ^ (-((ζ + (n1 : ℝ)) * ν))) := by
          exact mul_le_mul_right (ENNReal.ofReal_le_ofReal hml) _

/-- **The node-density bound at an arbitrary grid index, over `GridUniformCore`**
(route (a)).  As
`exists_maxDensity_parent_le_of_cutIndex_core` is to
`exists_maxDensity_parent_le_of_cutIndex`, so this is to
`exists_maxDensity_parent_le_of_index`: the uniform tube set is a *parameter* rather than
`𝒢.toUniformTubeSet`, tied to the core only by `hcov : 𝒱.cover = 𝒞.cover`.

**Why `Cw` is a theorem parameter.**  Same reason as at the cut-index form: the statement opens
`∃ Cbig : NNReal, 1 ≤ Cbig ∧ ∀ …` and `Cbig` is built from the tube set's uniformity constant, so
that constant must be bound to the *left* of the existential.  This is not a binder swap.

**The constant, named.**  Write `Ceng' Cw` for the constant that
`exists_maxDensity_parent_le_extra` returns at `Cw`.  Then

  `Cbig = max Cw (max (1 + Real.toNNReal (Ceng' Cw)) (1 + tubeVolRatio))`,

so the dependence on `Cw` is again through a single `max` and the engine constant — **no power of
`Cw` is taken**.  At the `Cu²` reading (`Cv := Cu ^ 2`, `Cw := Cu`) the squaring lives entirely in
`Cv`, which does not enter `Cbig` at all here, and the `N + 2` power is of `Cbig * Ct` exactly as
in the original.  The `δ`-exponent
`-((ζ + (n - 1)) * (ε + 1 / N))` is untouched: `Cu²` is `δ`-free at every site this landing
reaches, so it enters no exponent account.

**Independent of `exists_maxDensity_parent_le_of_cutIndex_core`.**  This form builds its own chain
through `exists_maxDensity_parent_le_extra` and does not call the cut-index form; the two are
siblings, not a chain. -/
theorem exists_maxDensity_parent_le_of_index_core (Cv Cw : NNReal)
    (_hCv : 1 ≤ Cv) (hCw : 1 ≤ Cw) :
    ∃ Cbig : NNReal, 1 ≤ Cbig ∧
      ∀ (N : ℕ), 0 < N →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (t : Finset ι) (T : ι → Tube δ E), t.Nonempty →
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (𝒞 : GridUniformCore t T N Cv) (𝒱 : Tube.UniformTubeSet t T N Cw),
        𝒱.cover = 𝒞.cover →
      ∀ (Ct : NNReal) (ε ζ : ℝ), 1 ≤ Ct → 0 ≤ ζ → 0 ≤ ε →
      ∀ S : Finset ℕ, 0 ∈ S → N ∈ S →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
        BlockKatzTaoOn t 𝒞.uniformAt Ct ζ a b ∧ (b : ℝ) - (a : ℝ) ≤ ε * (N : ℝ) + 1) →
      ∀ k, k ≤ N →
      Kakeya.maxDensity (𝒞.cover.indexSet k)
          (fun w => (𝒞.cover.tube k w).toConvexSpaceBody)
        ≤ ((Cbig * Ct : NNReal) : ENNReal) ^ (N + 2)
            * ENNReal.ofReal ((δ : ℝ) ^
                (-((ζ + ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) * (ε + 1 / (N : ℝ)))))
            * ENNReal.ofReal ((gridScale δ N k : ℝ) ^ (-ζ)) := by
  classical
  have hCu : (1 : NNReal) ≤ Cw := hCw
  obtain ⟨Ceng, hCeng, hextra⟩ :=
    exists_maxDensity_parent_le_extra.{u, _} (E := E) (Cw) hCu
  set n1 : ℕ := Module.finrank ℝ E - 1 with hn1
  set Cbig : NNReal := max (Cw)
    (max ((1 : NNReal) + Real.toNNReal Ceng) (1 + tubeVolRatio (E := E))) with hCbig
  have hCuCbig : Cw ≤ Cbig := le_max_left _ _
  have hCbig1 : (1 : NNReal) ≤ Cbig := le_trans hCu hCuCbig
  have htv1 : (1 : NNReal) + tubeVolRatio (E := E) ≤ Cbig := by
    rw [hCbig]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hCengR : Ceng ≤ ((Cbig : NNReal) : ℝ) := by
    rw [hCbig]
    have h1 : (0 : ℝ) ≤ Ceng := hCeng.le
    calc Ceng = (Real.toNNReal Ceng : ℝ) := by rw [Real.coe_toNNReal Ceng h1]
      _ ≤ (((1 : NNReal) + Real.toNNReal Ceng : NNReal) : ℝ) := by
          exact_mod_cast (le_add_of_nonneg_left (show (0 : NNReal) ≤ 1 by norm_num))
      _ ≤ ((max (Cw)
            (max ((1 : NNReal) + Real.toNNReal Ceng)
              (1 + tubeVolRatio (E := E))) : NNReal) : ℝ) := by
          exact_mod_cast
            (le_trans (le_max_left (1 + Real.toNNReal Ceng) (1 + tubeVolRatio (E := E)))
              (le_max_right (Cw)
                (max ((1 : NNReal) + Real.toNNReal Ceng) (1 + tubeVolRatio (E := E)))))
  have hCengE : ENNReal.ofReal Ceng ≤ ((Cbig : NNReal) : ENNReal) := by
    calc ENNReal.ofReal Ceng ≤ ENNReal.ofReal ((Cbig : NNReal) : ℝ) :=
          ENNReal.ofReal_le_ofReal hCengR
      _ = ((Cbig : NNReal) : ENNReal) := ENNReal.ofReal_coe_nnreal
  refine ⟨Cbig, hCbig1, ?_⟩
  intro N hNpos ι δ hδ hδ1 hδ0 t T hs hball 𝒞 𝒱 hcov Ct ε ζ hCt hζ hε
    S h0 hNmem hblocks k hkN
  set ν : ℝ := ε + 1 / (N : ℝ) with hν
  set Gb : ENNReal :=
    ((1 + tubeVolRatio (E := E) : NNReal) : ENNReal)
      * ENNReal.ofReal ((δ : ℝ) ^ (-((ζ + (n1 : ℝ)) * ν))) with hGb
  have hbase1 : (1 : NNReal) ≤ Cbig * Ct := one_le_mul hCbig1 hCt
  have hbase1' : (1 : ENNReal) ≤ ((Cbig * Ct : NNReal) : ENNReal) := by
    exact_mod_cast hbase1
  have hCu_le : Cw ≤ Cbig * Ct := by
    calc Cw ≤ Cbig := hCuCbig
      _ = Cbig * 1 := by rw [mul_one]
      _ ≤ Cbig * Ct := by gcongr
  have h1tvC : (1 : NNReal) + tubeVolRatio (E := E) ≤ Cbig * Ct := by
    calc (1 : NNReal) + tubeVolRatio (E := E) ≤ Cbig := htv1
      _ = Cbig * 1 := by rw [mul_one]
      _ ≤ Cbig * Ct := by gcongr
  have hδ0R : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hδ1R : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hN0R : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hνnn : (0 : ℝ) ≤ ν := by
    rw [hν]
    exact add_nonneg hε (div_nonneg zero_le_one (le_of_lt hN0R))
  have hθ0 : 0 ≤ (ζ + (n1 : ℝ)) * ν := by
    exact mul_nonneg (add_nonneg hζ (Nat.cast_nonneg n1)) hνnn
  have hδpow1 : (1 : ℝ) ≤ (δ : ℝ) ^ (-((ζ + (n1 : ℝ)) * ν)) := by
    calc (1 : ℝ) = (δ : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ (δ : ℝ) ^ (-((ζ + (n1 : ℝ)) * ν)) :=
          Real.rpow_le_rpow_of_exponent_ge hδ0R hδ1R (by linarith)
  have hGb1 : (1 : ENNReal) ≤ Gb := by
    unfold Gb
    calc (1 : ENNReal) = (1 : ENNReal) * 1 := by rw [mul_one]
      _ ≤ (((1 + tubeVolRatio (E := E) : NNReal) : ENNReal)
            * ENNReal.ofReal ((δ : ℝ) ^ (-((ζ + (n1 : ℝ)) * ν)))) := by
          refine mul_le_mul' ?_ ?_
          · exact_mod_cast self_le_add_right (a := (1 : NNReal)) (b := tubeVolRatio (E := E))
          · rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal hδpow1
  have hGbtop : Gb ≠ ⊤ := by
    unfold Gb
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  by_cases hk0 : k = 0
  · subst hk0
    have hzero := maxDensity_parent_zero_le (N := N) 𝒱 hs hball
    simp only [hcov] at hzero
    refine le_trans hzero ?_
    rw [gridScale_zero]
    simp only [NNReal.coe_one, Real.one_rpow, ENNReal.ofReal_one, mul_one]
    calc ((Cw : NNReal) : ENNReal)
        ≤ ((Cbig * Ct : NNReal) : ENNReal) := by exact_mod_cast hCu_le
      _ = ((Cbig * Ct : NNReal) : ENNReal) ^ 1 := by rw [pow_one]
      _ ≤ ((Cbig * Ct : NNReal) : ENNReal) ^ (N + 2) :=
          pow_le_pow_right₀ hbase1' (by omega)
      _ ≤ ((Cbig * Ct : NNReal) : ENNReal) ^ (N + 2)
            * ENNReal.ofReal ((δ : ℝ) ^ (-((ζ + (n1 : ℝ)) * ν))) := by
          have hδpow1e : (1 : ENNReal) ≤ ENNReal.ofReal ((δ : ℝ) ^ (-((ζ + (n1 : ℝ)) * ν))) := by
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal hδpow1
          calc ((Cbig * Ct : NNReal) : ENNReal) ^ (N + 2)
              = ((Cbig * Ct : NNReal) : ENNReal) ^ (N + 2) * (1 : ENNReal) := by rw [mul_one]
            _ ≤ ((Cbig * Ct : NNReal) : ENNReal) ^ (N + 2)
                * ENNReal.ofReal ((δ : ℝ) ^ (-((ζ + (n1 : ℝ)) * ν))) := by
                exact mul_le_mul' le_rfl hδpow1e
  · have hk0' : 0 < k := Nat.pos_of_ne_zero hk0
    obtain ⟨M, cuts, hMpos, hcuts0, hcutsLast, hStrict, hcutsLek, hcoarse, hfine, hadj⟩ :=
      exists_coarseChain h0 hk0'
    have hcutsN : ∀ j, cuts j ≤ N := fun j => le_trans (hcutsLek j) hkN
    have hMN : M ≤ N := by
      have hinj : Function.Injective cuts := hStrict.injective
      have himg : (Finset.univ : Finset (Fin (M + 1))).image cuts ⊆ Finset.range (N + 1) := by
        intro x hx
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hj ▸ hcutsN j))
      have hcard : ((Finset.univ : Finset (Fin (M + 1))).image cuts).card = M + 1 := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      have hle := Finset.card_le_card himg
      rw [hcard, Finset.card_range] at hle
      omega
    have hgap : ∀ m : Fin M, ∀ p ∈ 𝒱.cover.indexSet (cuts m.castSucc),
        Kakeya.maxDensity
            (𝒱.nodesUnder (cuts m.succ) (cuts m.castSucc) p)
            (fun w => (𝒱.cover.tube (cuts m.succ) w).toConvexSpaceBody)
          ≤ (Ct : ENNReal) * ENNReal.ofReal
              (((gridScale δ N (cuts m.castSucc) : ℝ)
                / (gridScale δ N (cuts m.succ) : ℝ)) ^ ζ)
            * (if m.succ = Fin.last M then Gb else 1) := by
      intro m p hp
      simp only [hcov] at hp ⊢
      have hami : cuts m.castSucc ∈ S := hcoarse m
      have hac : cuts m.castSucc < cuts m.succ := hStrict (Fin.castSucc_lt_succ (i := m))
      have hne := coverClass_nonempty_of_mem_parent 𝒱 (hcutsN m.castSucc) hs
        (by simpa [hcov] using hp)
      have hspec : hne.choose ∈ t ∧ 𝒞.cover.assign (cuts m.castSucc) hne.choose = p := by
        simpa [coverClass, hcov] using hne.choose_spec
      have hile : (T hne.choose).toConvexSpaceBody
          ≤ (𝒞.cover.tube (cuts m.castSucc) p).toConvexSpaceBody := by
        have := 𝒞.cover.le_tube_assign (cuts m.castSucc) (hcutsN m.castSucc) _ hspec.1
        rwa [hspec.2] at this
      by_cases hmemS : cuts m.succ ∈ S
      · have hblk := hblocks _ hami _ hmemS hac (hadj m)
        have hmain := maxDensity_nodesUnder_le_of_blockKatzTaoAt_core hδ hδ1 𝒞 hcov
          (hcutsN m.castSucc)
          (hcutsN m.succ) hac.le hp hile (hblk.1 _ hspec.1)
        have hif : (1 : ENNReal) ≤ (if m.succ = Fin.last M then Gb else 1) := by
          by_cases h : m.succ = Fin.last M
          · simp [h, hGb1]
          · simp [h]
        apply le_trans hmain
        simpa using (mul_le_mul_right hif ((Ct : ENNReal) * ENNReal.ofReal
            (((gridScale δ N (cuts m.castSucc) : ℝ)
              / (gridScale δ N (cuts m.succ) : ℝ)) ^ ζ)))
      · have hc : cuts m.succ = k := by
          rcases hfine m with hmem | heq
          · exact False.elim (hmemS hmem)
          · exact heq
        have hkS : k ∉ S := by simpa [hc] using hmemS
        have hlast : m.succ = Fin.last M := by
          apply hStrict.injective
          rw [hc, hcutsLast]
        set a : ℕ := cuts m.castSucc with ha
        have haSu : a ∈ S := by simpa [ha] using hami
        have haK : a < k := by
          rw [ha]
          exact lt_of_lt_of_le hac (le_of_eq hc)
        obtain ⟨a', ha'S, b, hbS, ha'k, hkb, hadj'⟩ :=
          exists_adjacent_containing (S := S) h0 hNmem hkN hkS
        have hhabb : a < b := lt_trans haK hkb
        have hale : a ≤ a' := by
          by_contra hnot
          have ha'a : a' < a := Nat.lt_of_not_ge hnot
          exact (hadj' a haSu ⟨ha'a, hhabb⟩)
        have ha'le : a' ≤ a := by
          by_contra hnot
          have haa' : a < a' := Nat.lt_of_not_ge hnot
          have ha'ck : a' < cuts m.succ := by rwa [hc]
          exact (hadj m a' ha'S ⟨haa', ha'ck⟩)
        have ha'a_eq : a' = a := le_antisymm ha'le hale
        have hadj'a : ∀ x ∈ S, ¬(a < x ∧ x < b) := by
          simpa [ha'a_eq] using hadj'
        have haN : a ≤ N := le_trans (le_of_lt haK) hkN
        have hbN : b ≤ N := by
          by_contra hnot
          have hNb : N < b := Nat.lt_of_not_ge hnot
          exact (hadj'a N hNmem ⟨lt_of_lt_of_le haK hkN, hNb⟩)
        have hkkb : k ≤ b := hkb.le
        obtain ⟨hblk, hshort⟩ := hblocks a haSu b hbS hhabb hadj'a
        have hbm : Kakeya.maxDensity (𝒱.nodesUnder b a p)
            (fun w => (𝒱.cover.tube b w).toConvexSpaceBody)
            ≤ (Ct : ENNReal) * ENNReal.ofReal
                (((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ ζ) := by
          simp only [hcov]
          exact maxDensity_nodesUnder_le_of_blockKatzTaoAt_core hδ hδ1 𝒞 hcov
            haN hbN hhabb.le hp hile
            (hblk _ hspec.1)
        have hmain := maxDensity_nodesUnder_le_crude hδ hδ1 𝒱 hs
          haN hkkb hbN hbm
        simp only [hcov] at hmain
        have hσa : (0 : ℝ) < (gridScale δ N a : ℝ) := by
          rw [ha]; exact_mod_cast gridScale_pos hδ N (cuts m.castSucc)
        have hσk : (0 : ℝ) < (gridScale δ N k : ℝ) := by exact_mod_cast gridScale_pos hδ N k
        have hσb : (0 : ℝ) < (gridScale δ N b : ℝ) := by exact_mod_cast gridScale_pos hδ N b
        have hnonneg_ak : (0 : ℝ) ≤ (gridScale δ N a : ℝ) / (gridScale δ N k : ℝ) :=
          div_nonneg hσa.le hσk.le
        have hnonneg_kb : (0 : ℝ) ≤ (gridScale δ N k : ℝ) / (gridScale δ N b : ℝ) :=
          div_nonneg hσk.le hσb.le
        have hratio : (gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)
            = (gridScale δ N a : ℝ) / (gridScale δ N k : ℝ)
                * (gridScale δ N k : ℝ) / (gridScale δ N b : ℝ) := by
          field_simp [hσk.ne', hσb.ne']
        have hpow_split : ((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ ζ
            = ((gridScale δ N a : ℝ) / (gridScale δ N k : ℝ)) ^ ζ
                * ((gridScale δ N k : ℝ) / (gridScale δ N b : ℝ)) ^ ζ := by
          have hR : ((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ ζ
              = (((gridScale δ N a : ℝ) / (gridScale δ N k : ℝ))
                    * ((gridScale δ N k : ℝ) / (gridScale δ N b : ℝ))) ^ ζ := by
            congr 1
            field_simp [hσk.ne', hσb.ne']
          rw [hR]
          exact Real.mul_rpow hnonneg_ak hnonneg_kb
        have hofreal_split : ENNReal.ofReal
              (((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ ζ)
            = ENNReal.ofReal (((gridScale δ N a : ℝ) / (gridScale δ N k : ℝ)) ^ ζ)
                * ENNReal.ofReal (((gridScale δ N k : ℝ) / (gridScale δ N b : ℝ)) ^ ζ) := by
          rw [hpow_split]
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hnonneg_ak ζ)]
        have hshortB : ENNReal.ofReal (((gridScale δ N k : ℝ) / (gridScale δ N b : ℝ)) ^ ζ)
            * crudeGapFactor (E := E) δ N a b
            ≤ ((tubeVolRatio (E := E) : NNReal) : ENNReal)
                * ENNReal.ofReal ((δ : ℝ) ^ (-((ζ + (n1 : ℝ)) * ν))) := by
          have := shortGapExtra_le (E := E) hδ hδ1 hNpos hζ (le_of_lt haK) hkkb hshort
          simpa [ν] using this
        have hTVe : (↑(tubeVolRatio (E := E) : NNReal) : ENNReal) ≤
            (↑(1 + tubeVolRatio (E := E) : NNReal) : ENNReal) := by
          exact_mod_cast self_le_add_left (a := tubeVolRatio (E := E)) (b := (1 : NNReal))
        have hfinal : ((Ct : ENNReal) * ENNReal.ofReal
              (((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ ζ)) * crudeGapFactor
                (E := E) δ N a b
            ≤ (Ct : ENNReal) * ENNReal.ofReal
                (((gridScale δ N a : ℝ) / (gridScale δ N k : ℝ)) ^ ζ) * Gb := by
          calc ((Ct : ENNReal) * ENNReal.ofReal
                (((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ ζ)) * crudeGapFactor
                      (E := E) δ N a b
              = (Ct : ENNReal) * (ENNReal.ofReal
                  (((gridScale δ N a : ℝ) / (gridScale δ N b : ℝ)) ^ ζ)
                  * crudeGapFactor (E := E) δ N a b) := by rw [mul_assoc]
            _ = (Ct : ENNReal) * (ENNReal.ofReal
                  (((gridScale δ N a : ℝ) / (gridScale δ N k : ℝ)) ^ ζ)
                  * ENNReal.ofReal (((gridScale δ N k : ℝ) / (gridScale δ N b : ℝ)) ^ ζ)
                  * crudeGapFactor (E := E) δ N a b) := by rw [hofreal_split]
            _ = (Ct : ENNReal) * ENNReal.ofReal
                (((gridScale δ N a : ℝ) / (gridScale δ N k : ℝ)) ^ ζ)
                * (ENNReal.ofReal (((gridScale δ N k : ℝ) / (gridScale δ N b : ℝ)) ^ ζ)
                    * crudeGapFactor (E := E) δ N a b) := by ring
            _ = (Ct : ENNReal) * (ENNReal.ofReal
                (((gridScale δ N a : ℝ) / (gridScale δ N k : ℝ)) ^ ζ)
                * (ENNReal.ofReal (((gridScale δ N k : ℝ) / (gridScale δ N b : ℝ)) ^ ζ)
                    * crudeGapFactor (E := E) δ N a b)) := by rw [mul_assoc]
            _ ≤ (Ct : ENNReal) * (ENNReal.ofReal
                (((gridScale δ N a : ℝ) / (gridScale δ N k : ℝ)) ^ ζ)
                * (((tubeVolRatio (E := E) : NNReal) : ENNReal)
                    * ENNReal.ofReal ((δ : ℝ) ^ (-((ζ + (n1 : ℝ)) * ν))))) := by
                exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hshortB)
            _ ≤ (Ct : ENNReal) * (ENNReal.ofReal
                (((gridScale δ N a : ℝ) / (gridScale δ N k : ℝ)) ^ ζ)
                * (((1 + tubeVolRatio (E := E) : NNReal) : ENNReal)
                    * ENNReal.ofReal ((δ : ℝ) ^ (-((ζ + (n1 : ℝ)) * ν))))) := by
                exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul_left hTVe
                  (ENNReal.ofReal ((δ : ℝ) ^ (-((ζ + (n1 : ℝ)) * ν))))))
            _ = (Ct : ENNReal) * ENNReal.ofReal
                (((gridScale δ N a : ℝ) / (gridScale δ N k : ℝ)) ^ ζ) * Gb := by
                rw [← mul_assoc, ← hGb]
        have hif : (if m.succ = Fin.last M then Gb else 1) = Gb := if_pos hlast
        rw [hif, hc]
        exact le_trans hmain hfinal
    have hGbtop' : Gb ≠ ⊤ := hGbtop
    have hchain := hextra N hNpos hδ hδ1 hδ0 t T hs hball 𝒱 M hMpos cuts hcuts0
      hcutsN hStrict Ct ζ Gb hGbtop' hgap
    rw [hcutsLast] at hchain
    simp only [hcov] at hchain
    set PB : ENNReal := ((Cbig * Ct : NNReal) : ENNReal) with hPB
    have hpowN1 : PB ^ M ≤ PB ^ (N + 1) := by
      rw [hPB]
      exact pow_le_pow_right₀ hbase1' (by omega)
    have hbaseP : ENNReal.ofReal Ceng * (Ct : ENNReal) ≤ PB := by
      rw [hPB]
      calc ENNReal.ofReal Ceng * (Ct : ENNReal)
          ≤ ((Cbig : NNReal) : ENNReal) * ((Ct : NNReal) : ENNReal) := mul_le_mul' hCengE le_rfl
        _ = ((Cbig * Ct : NNReal) : ENNReal) := by push_cast; ring
    have htvP : ((1 + tubeVolRatio (E := E) : NNReal) : ENNReal) ≤ PB := by
      rw [hPB]; exact_mod_cast h1tvC
    have hstep : (ENNReal.ofReal Ceng * (Ct : ENNReal)) ^ M
        * ((1 + tubeVolRatio (E := E) : NNReal) : ENNReal) ≤ PB ^ (N + 2) := by
      calc (ENNReal.ofReal Ceng * (Ct : ENNReal)) ^ M
            * ((1 + tubeVolRatio (E := E) : NNReal) : ENNReal)
          ≤ PB ^ M * PB := mul_le_mul' (pow_le_pow_left' hbaseP M) htvP
        _ ≤ PB ^ (N + 1) * PB := mul_le_mul' hpowN1 le_rfl
        _ = PB ^ (N + 2) := by rw [← pow_succ (a := PB) (n := N + 1)]
    have hcore : (ENNReal.ofReal Ceng * (Ct : ENNReal)) ^ M * Gb
        ≤ PB ^ (N + 2) * ENNReal.ofReal ((δ : ℝ) ^ (-((ζ + (n1 : ℝ)) * ν))) := by
      calc (ENNReal.ofReal Ceng * (Ct : ENNReal)) ^ M * Gb
          = ((ENNReal.ofReal Ceng * (Ct : ENNReal)) ^ M
              * ((1 + tubeVolRatio (E := E) : NNReal) : ENNReal))
            * ENNReal.ofReal ((δ : ℝ) ^ (-((ζ + (n1 : ℝ)) * ν))) := by rw [hGb, mul_assoc]
        _ ≤ PB ^ (N + 2) * ENNReal.ofReal ((δ : ℝ) ^ (-((ζ + (n1 : ℝ)) * ν))) :=
            mul_le_mul_left hstep _
    refine le_trans hchain ?_
    exact mul_le_mul_left hcore (ENNReal.ofReal ((gridScale δ N k : ℝ) ^ (-ζ)))

/-- **The node-density bound at an arbitrary grid index.**  The extension of
`exists_maxDensity_parent_le_of_cutIndex` from cut indices to all `k ≤ N`.  For `k ∉ S` the chain
`MultiScaleFac.coarseCuts S k` has exactly one gap that is not a gap of `S`, namely its last, and
that gap is paid for by `maxDensity_nodesUnder_le_crude` at the subpolynomial price of
`MultiScaleFac.shortGapExtra_le`.

**The statement is unchanged**; the proof is now one line through
`exists_maxDensity_parent_le_of_index_core` at `Cw := uniformTubeSetCuOf Cv`. -/
theorem exists_maxDensity_parent_le_of_index (Cv : NNReal)
    (hCv : 1 ≤ Cv) :
    ∃ Cbig : NNReal, 1 ≤ Cbig ∧
      ∀ (N : ℕ), 0 < N →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 → δ ≤ (16 : NNReal) ^ (-(N : ℝ)) →
      ∀ (t : Finset ι) (T : ι → Tube δ E), t.Nonempty →
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ (𝒢 : GridUniform t T N Cv) (Ct : NNReal) (ε ζ : ℝ), 1 ≤ Ct → 0 ≤ ζ → 0 ≤ ε →
      ∀ S : Finset ℕ, 0 ∈ S → N ∈ S →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
        BlockKatzTaoOn t 𝒢.uniformAt Ct ζ a b ∧ (b : ℝ) - (a : ℝ) ≤ ε * (N : ℝ) + 1) →
      ∀ k, k ≤ N →
      Kakeya.maxDensity (𝒢.cover.indexSet k)
          (fun w => (𝒢.cover.tube k w).toConvexSpaceBody)
        ≤ ((Cbig * Ct : NNReal) : ENNReal) ^ (N + 2)
            * ENNReal.ofReal ((δ : ℝ) ^
                (-((ζ + ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) * (ε + 1 / (N : ℝ)))))
            * ENNReal.ofReal ((gridScale δ N k : ℝ) ^ (-ζ)) := by
  obtain ⟨Cbig, hCbig1, h⟩ :=
    exists_maxDensity_parent_le_of_index_core.{u, _} (E := E) Cv
      (uniformTubeSetCuOf (E := E) Cv) hCv (le_trans hCv (le_max_left _ _))
  refine ⟨Cbig, hCbig1, ?_⟩
  intro N hNpos ι δ hδ hδ1 hδ0 t T hs hball 𝒢 Ct ε ζ hCt hζ hε S h0 hNmem hblocks k hkN
  exact h N hNpos hδ hδ1 hδ0 t T hs hball 𝒢.toGridUniformCore 𝒢.toUniformTubeSet rfl
    Ct ε ζ hCt hζ hε S h0 hNmem hblocks k hkN

end AlternativeOneGeneral

section Window

end Window

section AlternativeOneFinal

end AlternativeOneFinal

section AlternativeTwoKT

end AlternativeTwoKT

section EmptyFamily

/-- **The nodeless uniform structure on an empty family.**  Alternative (i) of half (B) bounds
`Δ_max` of the *node* family, so it is not automatic when the family is empty: the parents of an
arbitrary system need not be empty.  Every clause of `GridCoverSystem` quantifies over members and
so holds vacuously; the uniformity clauses quantify over nodes, of which there are none. -/
noncomputable def emptyUniformTubeSet {s : Finset ι} (hs : s = ∅) (T : ι → Tube δ E) (N : ℕ)
    (C : NNReal) (tb : (k : ℕ) → ι → Tube (gridScale δ N k) E) :
    UniformTubeSet s T N C where
  cover :=
    { indexSet := fun _ => ∅
      assign := fun _ i => i
      tube := tb
      assign_mem := by
        intro k _ i hi; rw [hs] at hi; exact absurd hi (Finset.notMem_empty i)
      le_tube_assign := by
        intro k _ i hi; rw [hs] at hi; exact absurd hi (Finset.notMem_empty i)
      nested := by
        intro k _ i hi; rw [hs] at hi; exact absurd hi (Finset.notMem_empty i)
      tube_nested := by
        intro k _ i hi; rw [hs] at hi; exact absurd hi (Finset.notMem_empty i) }
  branchingN := fun _ => 1
  tube_injOn := by intro k _; simp
  boundedOverlap := by intro k _ V; simp
  card_class_le := by intro k _ j hj; exact absurd hj (Finset.notMem_empty j)
  le_card_class := by intro k _ j hj; exact absurd hj (Finset.notMem_empty j)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem emptyUniformTubeSet_parent {s : Finset ι} (hs : s = ∅) (T : ι → Tube δ E) (N : ℕ)
    (C : NNReal) (tb : (k : ℕ) → ι → Tube (gridScale δ N k) E) (k : ℕ) :
    (emptyUniformTubeSet hs T N C tb).cover.indexSet k = ∅ := rfl

omit [Nontrivial E] in
/-- The nodeless structure is Katz–Tao at every scale with any error. -/
theorem isKatzTaoAtEveryScale_emptyUniformTubeSet {s : Finset ι} (hs : s = ∅) (T : ι → Tube δ E)
    (N : ℕ) (C : NNReal) (tb : (k : ℕ) → ι → Tube (gridScale δ N k) E) (A : ENNReal) :
    (emptyUniformTubeSet hs T N C tb).IsKatzTaoAtEveryScale A := by
  intro k _
  rw [emptyUniformTubeSet_parent, Kakeya.maxDensity_empty]
  exact bot_le

end EmptyFamily

end MultiScaleFac

end Kakeya
