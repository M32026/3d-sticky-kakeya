/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleSubmult
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTwoScale
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCountFloorObstruction

/-!
# Two-scale submultiplicativity on the window's cells

The refined source's `lemtwoscalemaxdensity` (l.4959–4975): the maximal density of the level-`c`
cells under a level-`a` node factors through an intermediate level `p`,
`Δ_max(𝕋_c[T_a]) ≤ C² · Δ_max(𝕋_p) · max_{T_p} Δ_max(𝕋_c[T_p])`.  The tree's rendering is
`Kakeya.MultiScaleSubmult.maxDensity_le_two_fibreDeltaMax`, GWZ Lemma 7.4 at `M = 2`, stated on
an abstract three-level hierarchy with a projection.  This leaf instantiates it on the window's
containment families `Tube.UniformTubeSet.nodesUnder`:

* level `2` — the level-`c` cells inside the node `T_a = 𝒰.cover.tube a j`,
  `Q₂ = 𝒰.nodesUnder c a j`;
* level `1` — their level-`p` **ancestors** `Q₁ = Q₂.image (coarseNode p c)`, read off a class
  member
  (`Kakeya.ML2Reduction.coarseNode`), so that the containment `T_c ≤ T_p` is the chain's own
  `tube_le_coarseNode`;
* level `0` — one ambient tube of radius `4` centred at the origin, which contains every node that
  meets the unit ball (`node_carrier_subset_closedBall_four`); the source's `ρ_0 = 1` is the tree
  lemma's `1 ≤ ρ_0 ≤ 4`.

The ancestors need **not** lie inside `T_a` (a `p`-node containing a `c`-cell inside `T_a` may stick
out of it), which is exactly the containment-versus-assignment gap names.  The second theorem
prices it: the ancestors of the cells inside `T_a` are all inside the (at most `Cu`) level-`a` nodes
that meet `T_a` through a member (`boundedOverlap` at `T_a`), so
`Δ_max(Q₁) ≤ Cu · max_{j'} Δ_max(𝒰.nodesUnder p a j')` — the parent-density clause of alternative
(F) then bounds the right-hand side by `Cu · δ^{-2η'}`, and "the producer must carry the constant" is this `Cu`.

Side conditions carried as binders: the factor-`4` gap `4 ρ_c ≤ ρ_p`
(a tree-side condition, absent from the source's lemma; F6 supplies it from a threshold), the
members inside the unit ball, and `δ ≤ 1`.  The other H4 items — `1 ≤ ρ_0 ≤ 4`, containment in a
ball, the coarsest-level count cap — are discharged here by the ambient tube.
-/

@[expose] public section

open MeasureTheory Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- **A node that meets the unit ball through a member lies in the ball of radius `4`.**  A tube of
radius `ρ ≤ 1` has diameter at most `3`. -/
theorem node_carrier_subset_closedBall_four {ι : Type*} {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    {k : ℕ} (hk : k ≤ N) {j : ι} (hj : j ∈ 𝒰.cover.indexSet k) :
    (𝒰.cover.tube k j).carrier ⊆ Metric.closedBall (0 : E) 4 := by
  classical
  obtain ⟨i, hi⟩ := Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent 𝒰 hk hs hj
  simp only [Tube.coverClass, Finset.mem_filter] at hi
  have hTi : (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody := by
    have := 𝒰.cover.le_tube_assign k hk i hi.1
    rwa [hi.2] at this
  -- a point of the member: inside the unit ball and inside the node
  have hx : (T i).midpoint ∈ (T i).carrier := Tube.midpoint_mem_carrier hδ0 (T i)
  have hx1 : ‖(T i).midpoint‖ ≤ 1 := by
    have := hball i hi.1 hx
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hxnode : (T i).midpoint ∈ (𝒰.cover.tube k j).carrier := hTi hx
  have hρ : (gridScale δ N k : ℝ) ≤ 1 := by exact_mod_cast Tube.gridScale_le_one hδ1 N k
  set mid := _root_.midpoint ℝ (𝒰.cover.tube k j).x (𝒰.cover.tube k j).y with hmid
  have hsub := Tube.carrier_subset_closedBall_midpoint (E := E) (𝒰.cover.tube k j)
  have hxmid : dist (T i).midpoint mid ≤ 1 / 2 + (gridScale δ N k : ℝ) := by
    have := hsub hxnode
    rwa [Metric.mem_closedBall] at this
  intro z hz
  have hzmid : dist z mid ≤ 1 / 2 + (gridScale δ N k : ℝ) := by
    have := hsub hz
    rwa [Metric.mem_closedBall] at this
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖z‖ = dist z 0 := (dist_zero_right z).symm
    _ ≤ dist z mid + dist mid (T i).midpoint + dist (T i).midpoint 0 := dist_triangle4 _ _ _ _
    _ ≤ (1 / 2 + (gridScale δ N k : ℝ)) + (1 / 2 + (gridScale δ N k : ℝ)) + 1 := by
        gcongr
        · rw [dist_comm]; exact hxmid
        · rw [dist_zero_right]; exact hx1
    _ ≤ 4 := by linarith

open scoped Classical in
/-- **The two-scale bound on the window's cells (F1).**  There is a constant `C = C(E)` such that
for
every hierarchy on members inside the unit ball, every node `j`, and every three levels `a`, `p ≤ c`
with the factor-`4` gap `4 ρ_c ≤ ρ_p`,
`Δ_max(𝒰.nodesUnder c a j)
  ≤ C² · Δ_max(ancestors) · max_{jp ∈ ancestors} Δ_max(𝒰.nodesUnder c p jp)`,
the ancestors being the level-`p` `coarseNode`s of the cells. -/
theorem exists_twoScale_nodesUnder :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ 1 →
      ∀ {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
        (𝒰 : Tube.UniformTubeSet s T N Cu), s.Nonempty →
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ∀ {a p c : ℕ}, p ≤ c → c ≤ N → 4 * gridScale δ N c ≤ gridScale δ N p →
      ∀ j : ι,
        Kakeya.maxDensity (𝒰.nodesUnder c a j) (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
          ≤ ENNReal.ofReal C ^ 2
            * Kakeya.maxDensity
                ((𝒰.nodesUnder c a j).image (ML2Reduction.coarseNode 𝒰.cover.toChain p c))
                (fun jp => (𝒰.cover.tube p jp).toConvexSpaceBody)
            * ((𝒰.nodesUnder c a j).image (ML2Reduction.coarseNode 𝒰.cover.toChain p c)).sup
                (fun jp => Kakeya.maxDensity
                  ((coverClass s (𝒰.cover.assign p) jp).image (𝒰.cover.assign c))
                  (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)) := by
  obtain ⟨C, hC, hmain⟩ :=
    Kakeya.MultiScaleSubmult.maxDensity_le_two_fibreDeltaMax (E := E) 5 (by norm_num) 1 one_pos
  refine ⟨C, hC, ?_⟩
  intro ι δ hδ0 hδ1 s T N Cu 𝒰 hs hball a p c hpc hc hgap j
  classical
  set Q2 : Finset ι := 𝒰.nodesUnder c a j with hQ2
  set proj : ι → ι := ML2Reduction.coarseNode 𝒰.cover.toChain p c with hproj
  set Q1 : Finset ι := Q2.image proj with hQ1
  set W2 : ι → ConvexSpaceBody E := fun j' => (𝒰.cover.tube c j').toConvexSpaceBody with hW2
  set W1 : ι → ConvexSpaceBody E := fun jp => (𝒰.cover.tube p jp).toConvexSpaceBody with hW1
  rcases Q2.eq_empty_or_nonempty with hQ2e | hQ2ne
  · rw [hQ2e, Kakeya.maxDensity_empty]
    exact zero_le
  have hp : p ≤ N := hpc.trans hc
  -- every level-`c` cell is active (has a class member), so its ancestor is a genuine node
  have hQ2idx : ∀ jc ∈ Q2, jc ∈ 𝒰.cover.indexSet c := fun jc hjc =>
    (Finset.mem_filter.mp hjc).1
  have hactive : ∀ jc ∈ Q2, jc ∈ ML2Reduction.activeNodes 𝒰.cover.toChain c := by
    intro jc hjc
    refine Finset.mem_filter.mpr ⟨hQ2idx jc hjc, ?_⟩
    exact Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent 𝒰 hc hs (hQ2idx jc hjc)
  have hQ1idx : ∀ jp ∈ Q1, jp ∈ 𝒰.cover.indexSet p := by
    intro jp hjp
    obtain ⟨jc, hjc, rfl⟩ := Finset.mem_image.mp hjp
    exact ML2Reduction.coarseNode_mem 𝒰.cover.toChain hp (hactive jc hjc)
  have hcontain : ∀ jc ∈ Q2, W2 jc ≤ W1 (proj jc) := fun jc hjc =>
    ML2Reduction.tube_le_coarseNode 𝒰.cover.toChain hpc hc (hactive jc hjc)
  -- the ambient tube: radius `4`, centred at the origin
  obtain ⟨u, hu⟩ : ∃ u : E, ‖u‖ = 1 := exists_norm_eq E zero_le_one
  set amb : Tube 4 E := Tube.ofMidpointDirection 4 0 u hu with hamb
  have hambmid : _root_.midpoint ℝ amb.x amb.y = 0 := by
    rw [midpoint_eq_smul_add]
    change (⅟(2 : ℝ)) • ((0 - (1 / 2 : ℝ) • u) + (0 + (1 / 2 : ℝ) • u)) = 0
    simp
  have hamb_ball : amb.carrier ⊆ Metric.closedBall (0 : E) 5 := by
    intro z hz
    have := Tube.carrier_subset_closedBall_midpoint (E := E) amb hz
    rw [hambmid, Metric.mem_closedBall] at this
    rw [Metric.mem_closedBall]
    have h4 : ((4 : NNReal) : ℝ) = 4 := by norm_num
    rw [h4] at this
    linarith
  have hball_amb : Metric.closedBall (0 : E) 4 ⊆ amb.carrier := by
    intro z hz
    rw [amb.carrier_eq]
    refine Set.mem_biUnion (midpoint_mem_segment amb.x amb.y) ?_
    rw [hambmid]
    simpa using hz
  have hnode4 : ∀ k ≤ N, ∀ j' ∈ 𝒰.cover.indexSet k,
      (𝒰.cover.tube k j').carrier ⊆ Metric.closedBall (0 : E) 4 :=
    fun k hk j' hj' => node_carrier_subset_closedBall_four hδ0 hδ1 𝒰 hs hball hk hj'
  -- the three-level data of the lemma
  let ρ : Fin 3 → NNReal := fun k => match k with
    | ⟨0, _⟩ => 4
    | ⟨1, _⟩ => gridScale δ N p
    | ⟨_ + 2, _⟩ => gridScale δ N c
  let tb : ∀ k : Fin 3, ι → Tube (ρ k) E := fun k => match k with
    | ⟨0, _⟩ => fun _ => amb
    | ⟨1, _⟩ => fun jp => 𝒰.cover.tube p jp
    | ⟨_ + 2, _⟩ => fun jc => 𝒰.cover.tube c jc
  let Q : ∀ _k : Fin 3, Finset ι := fun k => match k with
    | ⟨0, _⟩ => {j}
    | ⟨1, _⟩ => Q1
    | ⟨_ + 2, _⟩ => Q2
  let pr : ∀ _m : Fin 2, ι → ι := fun m => match m with
    | ⟨0, _⟩ => fun _ => j
    | ⟨_ + 1, _⟩ => proj
  have hρ1 : (1 : NNReal) ≤ ρ 0 := by change (1 : NNReal) ≤ 4; norm_num
  have hρ4 : ρ 0 ≤ 4 := by change (4 : NNReal) ≤ 4; exact le_rfl
  have hρ2 : 0 < ρ 2 := by change 0 < gridScale δ N c; exact Tube.gridScale_pos hδ0 N c
  have hgap1 : 4 * ρ 1 ≤ ρ 0 := by
    change 4 * gridScale δ N p ≤ 4
    have := Tube.gridScale_le_one hδ1 N p
    calc 4 * gridScale δ N p ≤ 4 * 1 := by gcongr
      _ = 4 := by norm_num
  have hgap2 : 4 * ρ 2 ≤ ρ 1 := by change 4 * gridScale δ N c ≤ gridScale δ N p; exact hgap
  have key := hmain ρ hρ1 hρ4 hρ2 hgap1 hgap2 (κ := fun _ => ι) tb Q pr ?_ ?_ ?_ ?_ ?_
  · -- read the conclusion on the concrete data
    have key' : Kakeya.maxDensity Q2 W2
        ≤ ENNReal.ofReal C ^ 2
          * (Kakeya.MultiScaleSubmult.fibreDeltaMax Q1 W1 ({j} : Finset ι) (fun _ => j)
            * Kakeya.MultiScaleSubmult.fibreDeltaMax Q2 W2 Q1 proj) := by
      rw [Fin.prod_univ_two] at key
      exact key
    have hf1 : Kakeya.MultiScaleSubmult.fibreDeltaMax Q1 W1 ({j} : Finset ι) (fun _ => j)
        = Kakeya.maxDensity Q1 W1 := by
      unfold Kakeya.MultiScaleSubmult.fibreDeltaMax
      rw [Finset.sup_singleton]
      congr 1
      exact Finset.filter_true_of_mem (fun _ _ => rfl)
    have hf2 : Kakeya.MultiScaleSubmult.fibreDeltaMax Q2 W2 Q1 proj
        ≤ Q1.sup (fun jp => Kakeya.maxDensity
            ((coverClass s (𝒰.cover.assign p) jp).image (𝒰.cover.assign c)) W2) := by
      unfold Kakeya.MultiScaleSubmult.fibreDeltaMax
      refine Finset.sup_mono_fun (fun jp _ => ?_)
      refine Kakeya.maxDensity_mono W2 ?_
      intro jc hjc
      obtain ⟨hjcQ2, hjceq⟩ := Finset.mem_filter.mp hjc
      -- the member the ancestor is read off is in the class of `jp` and is assigned to `jc`
      have hne : (Tube.coverClass s (𝒰.cover.toChain.assign c) jc).Nonempty :=
        (Finset.mem_filter.mp (hactive jc hjcQ2)).2
      have hmem := hne.choose_spec
      simp only [Tube.coverClass, Finset.mem_filter] at hmem
      have hproj_eq : proj jc = 𝒰.cover.assign p hne.choose := by
        change ML2Reduction.coarseNode 𝒰.cover.toChain p c jc = _
        rw [ML2Reduction.coarseNode, dif_pos hne]
        rfl
      refine Finset.mem_image.mpr ⟨hne.choose, ?_, hmem.2⟩
      simp only [Tube.coverClass, Finset.mem_filter]
      exact ⟨hmem.1, hproj_eq.symm.trans hjceq⟩
    calc Kakeya.maxDensity Q2 W2
        ≤ ENNReal.ofReal C ^ 2
          * (Kakeya.MultiScaleSubmult.fibreDeltaMax Q1 W1 ({j} : Finset ι) (fun _ => j)
            * Kakeya.MultiScaleSubmult.fibreDeltaMax Q2 W2 Q1 proj) := key'
      _ = ENNReal.ofReal C ^ 2 * Kakeya.maxDensity Q1 W1
            * Kakeya.MultiScaleSubmult.fibreDeltaMax Q2 W2 Q1 proj := by rw [hf1]; ring
      _ ≤ ENNReal.ofReal C ^ 2 * Kakeya.maxDensity Q1 W1
            * Q1.sup (fun jp => Kakeya.maxDensity
                ((coverClass s (𝒰.cover.assign p) jp).image (𝒰.cover.assign c)) W2) :=
        mul_le_mul' le_rfl hf2
  · -- the projections land in the coarser level
    intro m
    fin_cases m
    · intro w _
      change j ∈ ({j} : Finset ι)
      exact Finset.mem_singleton_self j
    · intro w hw
      change proj w ∈ Q1
      exact Finset.mem_image_of_mem proj hw
  · -- the containments
    intro m
    fin_cases m
    · intro w hw
      change (𝒰.cover.tube p w).toConvexSpaceBody ≤ amb.toConvexSpaceBody
      refine SetLike.coe_subset_coe.mpr ?_
      exact (hnode4 p hp w (hQ1idx w hw)).trans hball_amb
    · intro w hw
      change (𝒰.cover.tube c w).toConvexSpaceBody ≤ (𝒰.cover.tube p (proj w)).toConvexSpaceBody
      exact hcontain w hw
  · -- the coarsest level has one node
    change (({j} : Finset ι).card : ℝ) ≤ 1 * (5 + 3) ^ (2 * Module.finrank ℝ E)
    rw [Finset.card_singleton, one_mul]
    exact_mod_cast one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 5 + 3)
  · -- everything lies in the ball of radius `5`
    intro k
    fin_cases k
    · intro t _
      change amb.carrier ⊆ Metric.closedBall (0 : E) 5
      exact hamb_ball
    · intro t ht
      change (𝒰.cover.tube p t).carrier ⊆ Metric.closedBall (0 : E) 5
      exact (hnode4 p hp t (hQ1idx t ht)).trans (Metric.closedBall_subset_closedBall (by norm_num))
    · intro t ht
      change (𝒰.cover.tube c t).carrier ⊆ Metric.closedBall (0 : E) 5
      exact (hnode4 c hc t (hQ2idx t ht)).trans (Metric.closedBall_subset_closedBall (by norm_num))
  · -- the two coarser levels are nonempty
    intro m
    fin_cases m
    · change ({j} : Finset ι).Nonempty
      exact Finset.singleton_nonempty j
    · change Q1.Nonempty
      exact hQ2ne.image proj

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The ancestors' level-`a` nodes are few.**  Every level-`p` ancestor `coarseNode p c jc` of a
cell `jc` inside `T_a` lies inside the level-`a` node `coarseNode a c jc` of the same member, and
those level-`a` nodes meet `T_a` through that member, so `boundedOverlap` at `T_a` caps their number
by `Cu`. -/
theorem card_image_coarseNode_le {ι : Type*} {δ : NNReal}
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N Cu) (hs : s.Nonempty) {a c : ℕ} (hac : a ≤ c) (hc : c ≤ N)
    (j : ι) :
    (open scoped Classical in
      (((𝒰.nodesUnder c a j).image (ML2Reduction.coarseNode 𝒰.cover.toChain a c)).card : NNReal))
      ≤ Cu := by
  classical
  have ha : a ≤ N := hac.trans hc
  have hsub : (𝒰.nodesUnder c a j).image (ML2Reduction.coarseNode 𝒰.cover.toChain a c)
      ⊆ (𝒰.cover.indexSet a).filter (fun j' => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ (𝒰.cover.tube a j').toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ (𝒰.cover.tube a j).toConvexSpaceBody) := by
    intro j' hj'
    obtain ⟨jc, hjc, rfl⟩ := Finset.mem_image.mp hj'
    obtain ⟨hjcidx, hjcle⟩ := Finset.mem_filter.mp hjc
    -- the member the ancestor is read off
    by_cases hne : (Tube.coverClass s (𝒰.cover.toChain.assign c) jc).Nonempty
    · have hmem := hne.choose_spec
      simp only [Tube.coverClass, Finset.mem_filter] at hmem
      have hi : hne.choose ∈ s := hmem.1
      have hTc : (T hne.choose).toConvexSpaceBody ≤ (𝒰.cover.tube c jc).toConvexSpaceBody := by
        have := 𝒰.cover.le_tube_assign c hc _ hi
        rwa [show 𝒰.cover.assign c hne.choose = jc from hmem.2] at this
      have hTa : (T hne.choose).toConvexSpaceBody
          ≤ (𝒰.cover.tube a (𝒰.cover.assign a hne.choose)).toConvexSpaceBody :=
        𝒰.cover.le_tube_assign a ha _ hi
      rw [ML2Reduction.coarseNode, dif_pos hne]
      refine Finset.mem_filter.mpr ⟨𝒰.cover.assign_mem a ha _ hi, hne.choose, hi, hTa, ?_⟩
      exact hTc.trans hjcle
    · exact absurd (Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent 𝒰 hc hs hjcidx) hne
  exact le_trans (by exact_mod_cast Finset.card_le_card hsub)
    (𝒰.boundedOverlap a ha (𝒰.cover.tube a j))

omit [Nontrivial E] in
open scoped Classical in
/-- **The ancestors' density is paid by the level-`a` nodes (F1b).**  Each level-`p` ancestor of a
cell inside `T_a` lies inside the level-`a` node of the same member, there are at most `Cu` such
level-`a` nodes (`card_image_coarseNode_le`), and `maxDensity` is subadditive over a union
(`maxDensity_le_sum_of_subset_biUnion`); so
`Δ_max(ancestors) ≤ Cu · max_{j' ∈ indexSet a} Δ_max(𝒰.nodesUnder p a j')` — the parent-density
clause of alternative (F) then bounds the right-hand side by `Cu · δ^{-2η'}`. -/
theorem maxDensity_ancestors_le_mul_sup {ι : Type*} {δ : NNReal}
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N Cu) (hs : s.Nonempty) {a p c : ℕ} (hap : a ≤ p) (hpc : p ≤ c)
    (hc : c ≤ N) (j : ι) :
    Kakeya.maxDensity ((𝒰.nodesUnder c a j).image (ML2Reduction.coarseNode 𝒰.cover.toChain p c))
        (fun jp => (𝒰.cover.tube p jp).toConvexSpaceBody)
      ≤ (Cu : ENNReal) * (𝒰.cover.indexSet a).sup (fun j' => Kakeya.maxDensity (𝒰.nodesUnder p a j')
          (fun jp => (𝒰.cover.tube p jp).toConvexSpaceBody)) := by
  have hp : p ≤ N := hpc.trans hc
  have ha : a ≤ N := hap.trans hp
  set W1 : ι → ConvexSpaceBody E := fun jp => (𝒰.cover.tube p jp).toConvexSpaceBody with hW1
  set Q2 := 𝒰.nodesUnder c a j with hQ2
  set A := Q2.image (ML2Reduction.coarseNode 𝒰.cover.toChain a c) with hA
  have hQ2idx : ∀ jc ∈ Q2, jc ∈ 𝒰.cover.indexSet c := fun jc hjc => (Finset.mem_filter.mp hjc).1
  -- every ancestor lies inside the level-`a` node of the same member
  have hsub : Q2.image (ML2Reduction.coarseNode 𝒰.cover.toChain p c)
      ⊆ A.biUnion (fun j' => 𝒰.nodesUnder p a j') := by
    intro jp hjp
    obtain ⟨jc, hjc, rfl⟩ := Finset.mem_image.mp hjp
    have hne : (Tube.coverClass s (𝒰.cover.toChain.assign c) jc).Nonempty :=
      Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent 𝒰 hc hs (hQ2idx jc hjc)
    have hmem := hne.choose_spec
    simp only [Tube.coverClass, Finset.mem_filter] at hmem
    refine Finset.mem_biUnion.mpr ⟨ML2Reduction.coarseNode 𝒰.cover.toChain a c jc,
      Finset.mem_image_of_mem _ hjc, ?_⟩
    rw [ML2Reduction.coarseNode, dif_pos hne, ML2Reduction.coarseNode, dif_pos hne]
    refine Finset.mem_filter.mpr ⟨𝒰.cover.assign_mem p hp _ hmem.1, ?_⟩
    exact 𝒰.cover.toChain.tube_assign_le hap hp hmem.1
  have hAidx : ∀ j' ∈ A, j' ∈ 𝒰.cover.indexSet a := by
    intro j' hj'
    obtain ⟨jc, hjc, rfl⟩ := Finset.mem_image.mp hj'
    have hact : jc ∈ ML2Reduction.activeNodes 𝒰.cover.toChain c :=
      Finset.mem_filter.mpr ⟨hQ2idx jc hjc,
        Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent 𝒰 hc hs (hQ2idx jc hjc)⟩
    exact ML2Reduction.coarseNode_mem 𝒰.cover.toChain ha hact
  have hcardA : ((A.card : ℕ) : ENNReal) ≤ (Cu : ENNReal) := by
    have := card_image_coarseNode_le 𝒰 hs (hap.trans hpc) hc j
    exact_mod_cast this
  calc Kakeya.maxDensity (Q2.image (ML2Reduction.coarseNode 𝒰.cover.toChain p c)) W1
      ≤ ∑ j' ∈ A, Kakeya.maxDensity (𝒰.nodesUnder p a j') W1 :=
        Kakeya.maxDensity_le_sum_of_subset_biUnion W1 hsub
    _ ≤ ∑ _j' ∈ A, (𝒰.cover.indexSet a).sup
          (fun j' => Kakeya.maxDensity (𝒰.nodesUnder p a j') W1) :=
        Finset.sum_le_sum (fun j' hj' => Finset.le_sup (f := fun j' =>
          Kakeya.maxDensity (𝒰.nodesUnder p a j') W1) (hAidx j' hj'))
    _ = (A.card : ENNReal) * (𝒰.cover.indexSet a).sup
          (fun j' => Kakeya.maxDensity (𝒰.nodesUnder p a j') W1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Cu : ENNReal) * (𝒰.cover.indexSet a).sup
          (fun j' => Kakeya.maxDensity (𝒰.nodesUnder p a j') W1) := by gcongr

/-! ### The two-scale constant, named -/

universe v

/-- **The two-scale constant `C₀ = C₀(E)`** of `exists_twoScale_nodesUnder`, named so that the
closure hypothesis `hclose` of `floor_of_windowLevels_of_maximizerVolume` (F4a) refers to a
definite constant rather than a fresh universally quantified one.  The
universe `u` of the index type `ι` is a parameter of the constant only because it is one of the
existential's: `twoScaleConst.{u, v} E`. -/
noncomputable def twoScaleConst (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] : ℝ :=
  Classical.choose (exists_twoScale_nodesUnder.{u, v} (E := E))

theorem twoScaleConst_pos (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] :
    0 < twoScaleConst.{u, v} E :=
  (Classical.choose_spec (exists_twoScale_nodesUnder.{u, v} (E := E))).1

open scoped Classical in
/-- `exists_twoScale_nodesUnder` at its own constant. -/
theorem twoScaleConst_spec {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type u} {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    {a p c : ℕ} (hpc : p ≤ c) (hc : c ≤ N) (hgap : 4 * gridScale δ N c ≤ gridScale δ N p)
    (j : ι) :
    Kakeya.maxDensity (𝒰.nodesUnder c a j) (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
      ≤ ENNReal.ofReal (twoScaleConst.{u, v} E) ^ 2
        * Kakeya.maxDensity
            ((𝒰.nodesUnder c a j).image (ML2Reduction.coarseNode 𝒰.cover.toChain p c))
            (fun jp => (𝒰.cover.tube p jp).toConvexSpaceBody)
        * ((𝒰.nodesUnder c a j).image (ML2Reduction.coarseNode 𝒰.cover.toChain p c)).sup
            (fun jp => Kakeya.maxDensity
              ((coverClass s (𝒰.cover.assign p) jp).image (𝒰.cover.assign c))
              (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)) := by
  obtain ⟨-, h⟩ := Classical.choose_spec (exists_twoScale_nodesUnder.{u, v} (E := E))
  exact h hδ0 hδ1 𝒰 hs hball (a := a) hpc hc hgap j

end Kakeya.ML2Core

end
