/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FibreCommon
public import Kakeya.Sticky
public import Kakeya.Uniform
public import Kakeya.MultiScaleFac.Branching

/-!
# Bridging the node reading to the leaf reading

**This file is scaffolding.**  It exists so that the migration to
`Tube.UniformTubeSet` can proceed one downstream file at a time instead of as a single
atomic rewrite, and it is to be deleted once no file references it.

Two bridges are needed, and only two.

* The node class against the leaf-anchored fibre.  These are the two objects the two developments
  compute with: `coverClass s (assign k) v` is the set of leaves *assigned to* the node `v`, whereas
  `fibreIndex s T δ ρ i₀` is the set of leaves inside the `ρ`-thickening of the leaf `T_{i₀}`.  Each
  sits inside the other up to a bounded dilation of the anchor, which is what
  `Tube.rescale_le_of_le` provides with its factor `4` — the reason the grid is taken
  `16`-separated.
* The nodes under a node against the gap fibre, the same comparison one level up.

Every downstream transfer of a Frostman constant then goes through
`Kakeya.MultiScaleFac.frostmanConstant_mono_anchor`, which pays a volume ratio, and through the
cardinality comparison of the two index sets, which the bounded-overlap clause pays for.
-/

@[expose] public section

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

/-! ### Node classes against leaf-anchored fibres -/

/-! ### The nodes under a node against the gap fibre -/

/-! ### From leaf-anchored fibre bounds to node-anchored class bounds

This is the substance of the translation.  A bound of the shape "every leaf-anchored fibre at the
grid scale `ρ_k` is `B`-Frostman in its anchor" becomes "every class of a node at grid index `k` is
`B'`-Frostman in that node", with `B'` larger than `B` by a dimensional constant and a power of the
uniformity constant.

The route does *not* pass through the fibre at the inflated scale `4ρ_k`, which would put the
hypothesis outside the range `ρ ≤ 1` at the coarsest grid index.  Instead the class, which does sit
inside the `4ρ_k`-fibre of any of its members, is covered by boundedly many *exact-scale* fibres
(`Kakeya.MultiScaleFac.exists_gapFibre_cover_of_ratio`), and `Kakeya.maxDensity` is subadditive over
such a covering.  So the hypothesis is only ever used at grid scales. -/

/-! ### The bottom grid scale, and the translation at every grid index -/

/-! ### Thickening a test body

Alternatives (ii)-2 and (ii)-3 of Lemma 7.7(A) speak about the family of *nodes* at the fine
grid index, whereas the leaf-anchored form speaks about the leaves thickened to that grid
radius.  Passing between the two moves each member by at most the grid radius, so a test body
for one family becomes, for the other, that body thickened by the grid radius.  That thickening
is affordable exactly because the test body already contains a tube of that radius: its every
affine thickness is then at least the radius, and
`Kakeya.Metric.volume_cthickening_le_prod` bounds the thickened volume by `4 ^ n` times the
product of the thicknesses, which `Convex.ethickness_prod_le_volume` returns to the volume. -/

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- `Metric.ethickness.scale` is monotone, being an infimum of the monotone `Metric.ethickness`. -/
theorem ethickness_scale_mono {X Y : Set E} (h : X ⊆ Y) :
    Metric.ethickness.scale ℝ X ≤ Metric.ethickness.scale ℝ Y :=
  Finset.le_inf fun i hi => (Finset.inf_le hi).trans (Metric.ethickness_monotone h i)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A convex body containing a `ρ`-tube accommodates the scale `ρ`.**  This is the hypothesis of
`Kakeya.Metric.volume_cthickening_le_prod`, and it is what makes the passage between the node
family and the thickened leaf family cost only a dimensional constant. -/
theorem le_ethickness_scale_of_tube_le {ρ : NNReal} (V : Tube ρ E) {K : ConvexSpaceBody E}
    (h : V.toConvexSpaceBody ≤ K) :
    (ρ : ENNReal) ≤ Metric.ethickness.scale ℝ K.carrier :=
  (Tube.le_ethickness_scale V).trans (ethickness_scale_mono h)

/-- The dimensional cost of thickening a test body by a scale it already accommodates. -/
noncomputable def thickenVolConst : NNReal :=
  4 ^ Module.finrank ℝ E / Metric.lt_volume_convexHull.c (Module.finrank ℝ E)

/-- The `ρ`-thickening of a convex body, as a convex body. -/
noncomputable def thickenBody (K : ConvexSpaceBody E) (ρ : NNReal) : ConvexSpaceBody E where
  carrier := Metric.cthickening (ρ : ℝ) K.carrier
  convex' := (((Convexity.IsConvexSet.convex K.convex').cthickening _)).isConvexSet
  isCompact' := K.isCompact.cthickening
  nonempty' := K.nonempty.mono (Metric.self_subset_cthickening K.carrier)

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem thickenBody_carrier (K : ConvexSpaceBody E) (ρ : NNReal) :
    (thickenBody K ρ).carrier = Metric.cthickening (ρ : ℝ) K.carrier := rfl

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
private theorem le_thickenBody (K : ConvexSpaceBody E) (ρ : NNReal) : K ≤ thickenBody K ρ :=
  Metric.self_subset_cthickening K.carrier

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The rescaling of a tube to any radius lies in the thickening by that radius: both are determined
by the same core, and the core lies in the original carrier. -/
theorem rescale_le_thickenBody {δ : NNReal} (T : Tube δ E) (ρ : NNReal)
    {K : ConvexSpaceBody E} (h : T.toConvexSpaceBody ≤ K) :
    (T.rescale ρ).toConvexSpaceBody ≤ thickenBody K ρ := by
  intro w hw
  change w ∈ (T.rescale ρ).carrier at hw
  rw [(T.rescale ρ).carrier_eq] at hw
  obtain ⟨z, hz, hdist⟩ := Set.mem_iUnion₂.mp hw
  refine Metric.mem_cthickening_of_dist_le w z (ρ : ℝ) K.carrier (h (?_ : z ∈ T.carrier)) hdist
  rw [T.carrier_eq]
  exact Set.mem_iUnion₂.mpr ⟨z, hz, Metric.mem_closedBall_self δ.coe_nonneg⟩

/-! ### Iterated nesting of the hierarchy -/

/-- The dimensional cost of thickening a test body by `m` times a scale it accommodates. -/
noncomputable def thickenVolConstN (m : ℕ) : NNReal :=
  (2 * (m + 1)) ^ Module.finrank ℝ E / Metric.lt_volume_convexHull.c (Module.finrank ℝ E)

omit [ProperSpace E] in
/-- **Thickening by `m` times an accommodated scale.**  Unlike `volume_cthickening_le_of_le_scale`
this needs no relation between `ρ` and the smallest affine thickness beyond `ρ ≤ m · scale`:
`Kakeya.Metric.volume_cthickening_le_prod_add` bounds the thickened volume by `2 ^ n ∏ (ρ + ω_i)`
unconditionally, and each factor is then at most `(m + 1) ω_i`. -/
theorem volume_cthickening_le_of_le_nsmul_scale {X : Set E} (hX : Convex ℝ X) {ρ : NNReal} {m : ℕ}
    (hρ : (ρ : ENNReal) ≤ (m : ENNReal) * Metric.ethickness.scale ℝ X) :
    volume (Metric.cthickening (ρ : ℝ) X)
      ≤ (thickenVolConstN (E := E) m : ENNReal) * volume X := by
  set n := Module.finrank ℝ E with hn
  have hDc : (thickenVolConstN (E := E) m : ENNReal)
      * (Metric.lt_volume_convexHull.c n : ENNReal)
      = (((2 * ((m : NNReal) + 1)) ^ n : NNReal) : ENNReal) := by
    rw [← ENNReal.coe_mul]
    exact ENNReal.coe_inj.mpr (div_mul_cancel₀ _ (Metric.lt_volume_convexHull.c_pos n).ne')
  calc
    volume (Metric.cthickening (ρ : ℝ) X)
        ≤ (2 : ENNReal) ^ n *
            ∏ i ∈ Finset.range n, ((ρ : ENNReal) + Metric.ethickness ℝ X i) := by
          simpa only [hn] using volume_cthickening_le_prod_add X ρ
    _ ≤ (2 : ENNReal) ^ n *
          ∏ i ∈ Finset.range n, (((m : ENNReal) + 1) * Metric.ethickness ℝ X i) :=
        mul_le_mul' le_rfl (Finset.prod_le_prod' fun i hi => by
          rw [add_mul, one_mul]
          exact add_le_add_left (hρ.trans (mul_le_mul' le_rfl
            (Metric.ethickness.scale_le X (Finset.mem_range.mp hi)))) _)
    _ = (((2 * ((m : NNReal) + 1)) ^ n : NNReal) : ENNReal) *
          ∏ i ∈ Finset.range n, Metric.ethickness ℝ X i := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← mul_assoc, ← mul_pow]
        push_cast
        ring
    _ ≤ (thickenVolConstN (E := E) m : ENNReal) * volume X := by
        rw [← hDc, mul_assoc]
        exact mul_le_mul' le_rfl (by simpa only [hn] using hX.ethickness_prod_le_volume)

/-- **The volume of a test body thickened by `m` times a tube radius it contains.** -/
theorem volume_thickenBody_le_nsmul {σ : NNReal} (V : Tube σ E) {K : ConvexSpaceBody E}
    (hV : V.toConvexSpaceBody ≤ K) {ρ : NNReal} {m : ℕ} (hρ : ρ ≤ (m : NNReal) * σ) :
    volume (thickenBody K ρ).carrier
      ≤ (thickenVolConstN (E := E) m : ENNReal) * volume K.carrier := by
  refine volume_cthickening_le_of_le_nsmul_scale (Convexity.IsConvexSet.convex K.convex') ?_
  calc (ρ : ENNReal) ≤ (m : ENNReal) * (σ : ENNReal) := by exact_mod_cast hρ
    _ ≤ (m : ENNReal) * Metric.ethickness.scale ℝ K.carrier :=
        mul_le_mul_right (le_ethickness_scale_of_tube_le V hV) _

/-! ### Counting the nodes under a node -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **A member of a coarse class has its fine node under that coarse node.** -/
theorem assign_mem_nodesUnder {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : UniformTubeSet s T N C) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ N) {j : ι} {i : ι}
    (hi : i ∈ coverClass s (𝒰.cover.assign a) j) :
    𝒰.cover.assign b i ∈ 𝒰.nodesUnder b a j := by
  classical
  simp only [coverClass, Finset.mem_filter] at hi
  obtain ⟨his, hasgn⟩ := hi
  rw [UniformTubeSet.nodesUnder, UniformTubeSet.nodesIn, Finset.mem_filter]
  exact ⟨𝒰.cover.assign_mem b hb i his,
    hasgn ▸ tube_assign_le_of_le (𝒢 := 𝒰.cover) hab hb his⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The branching number of a nonempty family is positive at every grid index: some member's class
is nonempty, and `le_card_class` bounds the branching number by `C` times its size. -/
theorem branchingN_pos {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : UniformTubeSet s T N C) (_hC : 1 ≤ C) (hs : s.Nonempty) {k : ℕ} (hk : k ≤ N) :
    0 < 𝒰.branchingN k := by
  classical
  obtain ⟨i, hi⟩ := hs
  have hmem : i ∈ coverClass s (𝒰.cover.assign k) (𝒰.cover.assign k i) := by
    simp [coverClass, hi]
  have h1 : (1 : NNReal) ≤ (coverClass s (𝒰.cover.assign k) (𝒰.cover.assign k i)).card := by
    exact_mod_cast Finset.one_le_card.mpr ⟨i, hmem⟩
  have hone : (1 : NNReal) ≤ C * 𝒰.branchingN k :=
    h1.trans (𝒰.card_class_le k hk _ (𝒰.cover.assign_mem k hk i hi))
  rcases eq_zero_or_pos (𝒰.branchingN k) with h | h
  · simp [h] at hone
  · exact h

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **A coarse class is covered by the fine classes under it.**  The classes at index `b` partition
`s`, and by `assign_mem_nodesUnder` every member of the coarse class has its fine node under the
coarse one, so the coarse class is contained in the union of the fine classes indexed by
`nodesUnder`. -/
theorem coverClass_subset_biUnion_nodesUnder {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} [DecidableEq ι] (𝒰 : UniformTubeSet s T N C) {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ N) {j : ι} :
    coverClass s (𝒰.cover.assign a) j
      ⊆ (𝒰.nodesUnder b a j).biUnion (fun j' => coverClass s (𝒰.cover.assign b) j') := by
  classical
  intro i hi
  have his : i ∈ s := by simp only [coverClass, Finset.mem_filter] at hi; exact hi.1
  exact Finset.mem_biUnion.mpr
    ⟨_, assign_mem_nodesUnder 𝒰 hab hb hi, by simp [coverClass, his]⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The coarse class against the number of fine nodes under the coarse node.** -/
theorem card_coverClass_le_mul_card_nodesUnder {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ N)
    {j : ι} :
    ((coverClass s (𝒰.cover.assign a) j).card : NNReal)
      ≤ ((𝒰.nodesUnder b a j).card : NNReal) * (C * 𝒰.branchingN b) := by
  classical
  have hcast : ((coverClass s (𝒰.cover.assign a) j).card : NNReal)
      ≤ ∑ j' ∈ 𝒰.nodesUnder b a j, ((coverClass s (𝒰.cover.assign b) j').card : NNReal) := by
    exact_mod_cast le_trans (Finset.card_le_card (coverClass_subset_biUnion_nodesUnder 𝒰 hab hb))
      Finset.card_biUnion_le
  refine hcast.trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun j' hj' => 𝒰.card_class_le b hb j' ?_
  simp only [UniformTubeSet.nodesUnder, UniformTubeSet.nodesIn, Finset.mem_filter] at hj'
  exact hj'.1

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The coarse branching number against the number of fine nodes.**  This is the counting identity
`N_{ρ_a} ≈ |𝕋_b[T_a]| · N_{ρ_b}` that makes the branching factor cancel between the two sides of the
node/leaf comparison. -/
theorem branchingN_le_mul_card_nodesUnder {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ N)
    (ha : a ≤ N) {j : ι} (hj : j ∈ 𝒰.cover.indexSet a) :
    𝒰.branchingN a ≤ C ^ 2 * (((𝒰.nodesUnder b a j).card : NNReal) * 𝒰.branchingN b) := by
  calc 𝒰.branchingN a ≤ C * ((coverClass s (𝒰.cover.assign a) j).card : NNReal) :=
        𝒰.le_card_class a ha j hj
    _ ≤ C * (((𝒰.nodesUnder b a j).card : NNReal) * (C * 𝒰.branchingN b)) :=
        mul_le_mul_right (card_coverClass_le_mul_card_nodesUnder 𝒰 hab hb) C
    _ = C ^ 2 * (((𝒰.nodesUnder b a j).card : NNReal) * 𝒰.branchingN b) := by ring

/-! ### Generic density bounds by cardinality -/

omit [Nontrivial E] [ProperSpace E] in
/-- A density is at most the cardinality weighted by the largest member volume. -/
theorem densityIn_mul_volume_le_card_mul {ι' : Type*} {t : Finset ι'} {W : ι' → ConvexSpaceBody E}
    (K : ConvexSpaceBody E) {vhi : ENNReal} (h : ∀ i ∈ t, volume (W i).carrier ≤ vhi) :
    Kakeya.densityIn t W K * volume K.carrier ≤ (t.card : ENNReal) * vhi := by
  unfold Kakeya.densityIn
  refine (ENNReal.mul_le_of_le_div le_rfl).trans ?_
  calc ∑ i ∈ t.filter (fun i => W i ≤ K), volume (W i).carrier
      ≤ ∑ _i ∈ t.filter (fun i => W i ≤ K), vhi :=
        Finset.sum_le_sum fun i hi => h i (Finset.mem_filter.mp hi).1
    _ = ((t.filter (fun i => W i ≤ K)).card : ENNReal) * vhi := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (t.card : ENNReal) * vhi :=
        mul_le_mul_left (by exact_mod_cast Finset.card_filter_le t (fun i => W i ≤ K)) vhi

/-! ### The node family under a node, against its density in that node -/

/-! ### The node family at a fine index, against the thickened leaf family

Alternative (ii)-2 compares the family of nodes at the fine index `b` sitting under a node at the
coarse index `a` with the leaves thickened to `ρ_b`.  The two families are related by the assignment
`i ↦ a_b(i)`, whose fibres are the classes; a node therefore stands for about `N_{ρ_b}` leaves, and
that branching factor appears on both sides of the comparison and cancels.  The `maxDensity` side
also moves each member by at most `ρ_b`, which is why the test body has to be thickened. -/

/-- The size of the covering of a `4ρ`-inflated fibre by exact-scale fibres, from
`Kakeya.MultiScaleFac.exists_gapFibre_cover_of_ratio` at ratio `4`. -/
noncomputable def gapCoverCard : NNReal :=
  2 * (25 : NNReal) ^ (2 * Module.finrank ℝ E) * (4 : NNReal) ^ (2 * Module.finrank ℝ E)

/-- **One node against its class.**  The volume of a node at index `b`, weighted by the branching
number, is at most a dimensional multiple of the total volume of the `ρ_b`-thickenings of its class:
the class has at least `N_{ρ_b}/C` members, each contributing at least `c_n ρ_b^{n-1}`, while the
node itself contributes at most `C_n ρ_b^{n-1}`. -/
theorem volume_node_mul_branchingN_le_sum_class {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (_hδ : 0 < δ) (hδ1 : δ ≤ 1) (𝒰 : UniformTubeSet s T N C)
    {b : ℕ} (hb : b ≤ N) {j' : ι} (hj' : j' ∈ 𝒰.cover.indexSet b) :
    volume (𝒰.cover.tube b j').carrier * (𝒰.branchingN b : ENNReal)
      ≤ (tubeVolRatio (E := E) : ENNReal) * (C : ENNReal)
          * ∑ i ∈ coverClass s (𝒰.cover.assign b) j',
              volume ((fibreBodies T (gridScale δ N b)) i).carrier := by
  classical
  have hbranchE : (𝒰.branchingN b : ENNReal)
      ≤ (C : ENNReal) * ((coverClass s (𝒰.cover.assign b) j').card : ENNReal) := by
    exact_mod_cast 𝒰.le_card_class b hb j' hj'
  set n : ℕ := Module.finrank ℝ E
  set p : ℕ := n - 1
  set c : NNReal := Tube.le_volume.c n
  set Cn : NNReal := Tube.volume_le.C n
  set ρ : NNReal := gridScale δ N b
  set cls : Finset ι := coverClass s (𝒰.cover.assign b) j'
  have hnodeVol : volume (𝒰.cover.tube b j').carrier
      ≤ (Cn : ENNReal) * (ρ : ENNReal) ^ p := by
    simpa only [Cn, ρ, p, n, ENNReal.coe_mul, ENNReal.coe_pow] using
      Tube.volume_le (gridScale_le_one hδ1 N b) (𝒰.cover.tube b j')
  have hvol_i : ∀ i ∈ cls, (c : ENNReal) * (ρ : ENNReal) ^ p
      ≤ volume ((fibreBodies T ρ) i).carrier := fun i _ => by
    simpa only [fibreBodies, c, p, n, ρ, ENNReal.coe_mul, ENNReal.coe_pow] using
      Tube.le_volume ((T i).rescale ρ)
  have hsum : (cls.card : ENNReal) * ((c : ENNReal) * (ρ : ENNReal) ^ p)
      ≤ ∑ i ∈ cls, volume ((fibreBodies T ρ) i).carrier := by
    simpa only [nsmul_eq_mul] using Finset.card_nsmul_le_sum cls _ _ hvol_i
  have hrc : (tubeVolRatio (E := E) : ENNReal) * (c : ENNReal) = (Cn : ENNReal) := by
    rw [← ENNReal.coe_mul]
    exact ENNReal.coe_inj.mpr (div_mul_cancel₀ Cn (Tube.le_volume.c_pos n).ne')
  calc volume (𝒰.cover.tube b j').carrier * (𝒰.branchingN b : ENNReal)
      ≤ (Cn : ENNReal) * (ρ : ENNReal) ^ p * ((C : ENNReal) * (cls.card : ENNReal)) :=
        mul_le_mul' hnodeVol hbranchE
    _ = (tubeVolRatio (E := E) : ENNReal) * (C : ENNReal)
          * ((cls.card : ENNReal) * ((c : ENNReal) * (ρ : ENNReal) ^ p)) := by
        rw [← hrc]
        ring
    _ ≤ (tubeVolRatio (E := E) : ENNReal) * (C : ENNReal)
          * ∑ i ∈ cls, volume ((fibreBodies T ρ) i).carrier := mul_le_mul' le_rfl hsum

/-- **Summed over a set of nodes.**  Distinct nodes have disjoint classes, the assignment being a
function, so the per-node bound sums to a bound by the total volume over the union of the
classes. -/
theorem sum_volume_nodes_mul_branchingN_le {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} [DecidableEq ι] (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (𝒰 : UniformTubeSet s T N C) {b : ℕ} (hb : b ≤ N) {t₀ : Finset ι}
    (ht₀ : t₀ ⊆ 𝒰.cover.indexSet b) :
    (∑ j' ∈ t₀, volume (𝒰.cover.tube b j').carrier) * (𝒰.branchingN b : ENNReal)
      ≤ (tubeVolRatio (E := E) : ENNReal) * (C : ENNReal)
          * ∑ i ∈ t₀.biUnion (fun j' => coverClass s (𝒰.cover.assign b) j'),
              volume ((fibreBodies T (gridScale δ N b)) i).carrier := by
  classical
  have hdisj : (t₀ : Set ι).PairwiseDisjoint
      (fun j' => coverClass s (𝒰.cover.assign b) j') := by
    intro j₁ _ j₂ _ hne
    simp only [Function.onFun, Finset.disjoint_left, coverClass, Finset.mem_filter]
    exact fun i h₁ h₂ => hne (h₁.2 ▸ h₂.2 ▸ rfl)
  rw [Finset.sum_biUnion hdisj, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_le_sum fun j' hj' =>
    volume_node_mul_branchingN_le_sum_class hδ hδ1 𝒰 hb (ht₀ hj')

/-- **The transport, node side.**  The density of the fine nodes under a coarse node in any test
body, weighted by the branching number, is controlled by the maximal density of the thickened leaves
of the `4ρ_a`-fibre of a member of the coarse class.  The test body must be thickened by `ρ_b` to
receive the leaves, which costs a dimensional factor because it already contains a `ρ_b`-tube. -/
theorem densityIn_nodesUnder_mul_branchingN_le {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (𝒰 : UniformTubeSet s T N C)
    {a b : ℕ} (_hab : a ≤ b) (ha : a ≤ N) (hb : b ≤ N) {j i₀ : ι}
    (hi₀ : i₀ ∈ coverClass s (𝒰.cover.assign a) j) (K' : ConvexSpaceBody E) :
    Kakeya.densityIn (𝒰.nodesUnder b a j)
          (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody) K'
        * (𝒰.branchingN b : ENNReal)
      ≤ (tubeVolRatio (E := E) : ENNReal) * (C : ENNReal)
          * (thickenVolConstN (E := E) 1 : ENNReal)
          * Kakeya.maxDensity (fibreIndex s T δ (4 * gridScale δ N a) i₀)
              (fibreBodies T (gridScale δ N b)) := by
  classical
  set σa : NNReal := gridScale δ N a
  set σb : NNReal := gridScale δ N b
  set NB : ι → ConvexSpaceBody E := fun j' => (𝒰.cover.tube b j').toConvexSpaceBody
  set Fib : Finset ι := fibreIndex s T δ (4 * σa) i₀
  set M : ENNReal := Kakeya.maxDensity Fib (fibreBodies T σb)
  set t₀ : Finset ι := (𝒰.nodesUnder b a j).filter (fun j' => NB j' ≤ K')
  set U : Finset ι := t₀.biUnion (fun j' => coverClass s (𝒰.cover.assign b) j')
  set L : ENNReal := ∑ j' ∈ t₀, volume (NB j').carrier
  set S : ENNReal := ∑ i ∈ U, volume ((fibreBodies T σb) i).carrier
  set v : ENNReal := volume K'.carrier
  set TVC : ENNReal := (thickenVolConstN (E := E) 1 : ENNReal)
  set R : ENNReal := (tubeVolRatio (E := E) : ENNReal) * (C : ENNReal)
  set BN : ENNReal := (𝒰.branchingN b : ENNReal)
  have hd : Kakeya.densityIn (𝒰.nodesUnder b a j) NB K' = L / v := rfl
  have hmemNds : ∀ {j'}, j' ∈ 𝒰.nodesUnder b a j → j' ∈ 𝒰.cover.indexSet b ∧
      (𝒰.cover.tube b j').toConvexSpaceBody ≤ (𝒰.cover.tube a j).toConvexSpaceBody :=
    fun {j'} h => (𝒰.mem_nodesIn_iff b (𝒰.cover.tube a j).toConvexSpaceBody j').mp h
  have ht₀ : t₀ ⊆ 𝒰.cover.indexSet b := fun j' hj' =>
    (hmemNds (Finset.mem_filter.mp hj').1).1
  by_cases ht₀empty : t₀ = ∅
  · simp only [hd, L, ht₀empty, Finset.sum_empty, ENNReal.zero_div, zero_mul]
    exact zero_le
  · obtain ⟨j₁, hj₁t₀⟩ := Finset.nonempty_iff_ne_empty.mpr ht₀empty
    have hNBj₁ : NB j₁ ≤ K' := (Finset.mem_filter.mp hj₁t₀).2
    have hUmem : ∀ i ∈ U, i ∈ Fib ∧ fibreBodies T σb i ≤ thickenBody K' σb := by
      intro i hiU
      obtain ⟨j'', hj''t₀, hiU''⟩ := Finset.mem_biUnion.mp hiU
      obtain ⟨his, hassign⟩ := Finset.mem_filter.mp hiU''
      obtain ⟨hj''nds, hNB⟩ := Finset.mem_filter.mp hj''t₀
      have h1T : (T i).toConvexSpaceBody ≤ (𝒰.cover.tube b j'').toConvexSpaceBody :=
        hassign ▸ 𝒰.cover.le_tube_assign b hb i his
      obtain ⟨hi₀s, hassign₀⟩ := Finset.mem_filter.mp hi₀
      have h3 : (𝒰.cover.tube a j).toConvexSpaceBody
          ≤ ((T i₀).rescale (4 * σa)).toConvexSpaceBody :=
        Tube.rescale_le_of_le (T i₀) (𝒰.cover.tube a j)
          (hassign₀ ▸ 𝒰.cover.le_tube_assign a ha i₀ hi₀s)
      refine ⟨?_, rescale_le_thickenBody (T i) σb (h1T.trans hNB)⟩
      simp only [Fib, fibreIndex_self]
      exact Finset.mem_filter.mpr ⟨his, h1T.trans ((hmemNds hj''nds).2.trans h3)⟩
    have hvol : volume (thickenBody K' σb).carrier ≤ TVC * v :=
      volume_thickenBody_le_nsmul (𝒰.cover.tube b j₁) hNBj₁ (by simp only [σb, Nat.cast_one,
        one_mul, le_refl])
    have hS2 : S ≤ M * (TVC * v) :=
      (Kakeya.sum_volume_le_maxDensity_mul_volume' (fun i hi => (hUmem i hi).2)).trans
        (mul_le_mul' (Kakeya.maxDensity_mono (fibreBodies T σb)
          (fun i hi => (hUmem i hi).1)) hvol)
    have hmain : L * BN ≤ R * TVC * M * v :=
      (sum_volume_nodes_mul_branchingN_le hδ hδ1 𝒰 hb ht₀).trans
        (le_of_le_of_eq (mul_le_mul_right hS2 R) (by ring))
    have hposb : 0 < volume (NB j₁).carrier :=
      lt_of_lt_of_le (ENNReal.coe_pos.mpr (mul_pos (Tube.le_volume.c_pos _)
        (pow_pos (gridScale_pos hδ N b) _)))
        (by simpa only [NB, ENNReal.coe_mul, ENNReal.coe_pow] using
          Tube.le_volume (𝒰.cover.tube b j₁))
    have hv0 : v ≠ 0 := (lt_of_lt_of_le hposb (measure_mono hNBj₁)).ne'
    have hvtop : v ≠ ⊤ := K'.isCompact.measure_ne_top
    rw [hd, div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv]
    exact (ENNReal.div_le_iff_le_mul (Or.inl hv0) (Or.inl hvtop)).mpr hmain

/-- **Covering the inflated fibre.**  A bound valid on every exact-scale `ρ_a`-fibre passes to the
`4ρ_a`-inflated fibre at the cost of the covering size. -/
theorem maxDensity_fibre_inflated_le {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} (hδ : 0 < δ) {a b : ℕ} (h2δ : 2 * δ ≤ gridScale δ N a) {i₀ : ι} {Y : ENNReal}
    (hY : ∀ i₂ ∈ s, Kakeya.maxDensity (fibreIndex s T δ (gridScale δ N a) i₂)
      (fibreBodies T (gridScale δ N b)) ≤ Y) :
    Kakeya.maxDensity (fibreIndex s T δ (4 * gridScale δ N a) i₀)
        (fibreBodies T (gridScale δ N b))
      ≤ (gapCoverCard (E := E) : ENNReal) * Y := by
  classical
  have hρpos : 0 < gridScale δ N a := gridScale_pos hδ N a
  obtain ⟨A, hAs, hAcard, hAcov⟩ :=
    exists_gapFibre_cover_of_ratio (s := s) (T := T) (δ := δ) (σ := δ)
      (ρ := gridScale δ N a) (ρ' := 4 * gridScale δ N a) hρpos le_rfl h2δ
      (le_mul_of_one_le_left hρpos.le (by norm_num)) i₀
  have hne : ((gridScale δ N a : NNReal) : ℝ) ≠ 0 := by exact_mod_cast hρpos.ne'
  rw [show ((4 * gridScale δ N a : NNReal) : ℝ) / ((gridScale δ N a : NNReal) : ℝ) = 4 by
    push_cast; field_simp] at hAcard
  have hAcardE : (A.card : ENNReal) ≤ (gapCoverCard (E := E) : ENNReal) := by
    rw [gapCoverCard]
    exact_mod_cast hAcard
  refine (maxDensity_le_sum_of_subset_biUnion (W := fibreBodies T (gridScale δ N b))
    (fun i hi => Finset.mem_biUnion.mpr (hAcov i hi))).trans ?_
  refine (Finset.sum_le_sum fun i₂ hi₂ => hY i₂ (hAs hi₂)).trans ?_
  simpa using mul_le_mul_left hAcardE Y

/-- **The transport, anchor side.**  The density of an exact-scale `ρ_a`-fibre of thickened leaves
in its own doubled anchor is at most the branching number times the density of the fine nodes in
the coarse node.  This is the same branching factor as in
`densityIn_nodesUnder_mul_branchingN_le`, and the two cancel. -/
theorem densityIn_fibre_thick_le_mul_densityIn_nodesUnder {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (𝒰 : UniformTubeSet s T N C) {a b : ℕ} (hab : a ≤ b) (ha : a ≤ N) (hb : b ≤ N)
    {i₂ : ι} (hi₂ : i₂ ∈ s) {j : ι} (hj : j ∈ 𝒰.cover.indexSet a) :
    Kakeya.densityIn (fibreIndex s T δ (gridScale δ N a) i₂)
        (fibreBodies T (gridScale δ N b))
        ((T i₂).rescale (2 * gridScale δ N a)).toConvexSpaceBody
      ≤ (tubeVolRatio (E := E) : ENNReal) ^ 2 * (C : ENNReal) ^ 4
          * (𝒰.branchingN b : ENNReal)
          * Kakeya.densityIn (𝒰.nodesUnder b a j)
              (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
              (𝒰.cover.tube a j).toConvexSpaceBody := by
  set n : ℕ := Module.finrank ℝ E
  set p : ℕ := n - 1
  set σa : NNReal := gridScale δ N a
  set σb : NNReal := gridScale δ N b
  set c : NNReal := Tube.le_volume.c n
  set Cn : NNReal := Tube.volume_le.C n
  set r : NNReal := Cn / c with hr_def
  set W : ι → ConvexSpaceBody E := fibreBodies T σb
  set anchor : ConvexSpaceBody E := ((T i₂).rescale (2 * σa)).toConvexSpaceBody
  set nds : Finset ι := 𝒰.nodesUnder b a j
  set Wnd : ι → ConvexSpaceBody E := fun j' => (𝒰.cover.tube b j').toConvexSpaceBody
  set Kn : ConvexSpaceBody E := (𝒰.cover.tube a j).toConvexSpaceBody
  set fib : Finset ι := fibreIndex s T δ σa i₂
  set Dfib : ENNReal := Kakeya.densityIn fib W anchor
  set Dnod : ENNReal := Kakeya.densityIn nds Wnd Kn
  set X : ENNReal := (c : ENNReal) * (σa : ENNReal) ^ p with hX_def
  set Y : ENNReal := (c : ENNReal) * (σb : ENNReal) ^ p with hY_def
  set Cσan : ENNReal := (Cn : ENNReal) * (σa : ENNReal) ^ p with hCσan_def
  set Cσbn : ENNReal := (Cn : ENNReal) * (σb : ENNReal) ^ p with hCσbn_def
  have hσa_pos : 0 < σa := gridScale_pos hδ N a
  have hc_ne : c ≠ 0 := (Tube.le_volume.c_pos n).ne'
  have hX0 : X ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hc_ne) (pow_ne_zero p (by exact_mod_cast hσa_pos.ne'))
  have hX_top : X ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  have hvol_lb : X ≤ volume anchor.carrier := by
    refine le_trans ?_ (Tube.le_volume ((T i₂).rescale (2 * σa)))
    rw [hX_def]
    push_cast
    gcongr
    exact le_mul_of_one_le_left zero_le one_le_two
  have hband_f : Dfib * X ≤ (fib.card : ENNReal) * Cσbn :=
    (mul_le_mul_right hvol_lb Dfib).trans
      (densityIn_mul_volume_le_card_mul anchor (vhi := Cσbn)
        fun i _ => Tube.volume_le (gridScale_le_one hδ1 N b) ((T i).rescale σb))
  have hcardfibE : (fib.card : ENNReal) ≤ (C : ENNReal) ^ 4 * (nds.card : ENNReal)
      * (𝒰.branchingN b : ENNReal) := by
    have h : (fib.card : NNReal) ≤ C ^ 4 * (nds.card : NNReal) * 𝒰.branchingN b := by
      calc (fib.card : NNReal) ≤ C ^ 2 * 𝒰.branchingN a :=
            card_fibreIndex_le_of_uniformTubeSet 𝒰 ha hi₂
        _ ≤ C ^ 2 * (C ^ 2 * ((nds.card : NNReal) * 𝒰.branchingN b)) :=
            mul_le_mul_right (branchingN_le_mul_card_nodesUnder 𝒰 hab hb ha hj) (C ^ 2)
        _ = C ^ 4 * (nds.card : NNReal) * 𝒰.branchingN b := by ring
    exact_mod_cast h
  have hband_h : (nds.card : ENNReal) * Y ≤ Dnod * Cσan :=
    card_nodesUnder_mul_le_densityIn hδ hδ1 𝒰 (a := a) (b := b) ha (j := j)
  have hrc : (r : ENNReal) * (c : ENNReal) = (Cn : ENNReal) := by
    rw [← ENNReal.coe_mul, hr_def, div_mul_cancel₀ Cn hc_ne]
  have hcast_a : Cσan = (r : ENNReal) * X := by rw [hCσan_def, hX_def, ← mul_assoc, hrc]
  have hcast_b : Cσbn = (r : ENNReal) * Y := by rw [hCσbn_def, hY_def, ← mul_assoc, hrc]
  have hrco : (r : ENNReal) = (tubeVolRatio (E := E) : ENNReal) := rfl
  refine (ENNReal.mul_le_mul_iff_right hX0 hX_top).mp ?_
  calc
    X * Dfib = Dfib * X := mul_comm X Dfib
    _ ≤ (fib.card : ENNReal) * Cσbn := hband_f
    _ ≤ ((C : ENNReal) ^ 4 * (nds.card : ENNReal) * (𝒰.branchingN b : ENNReal))
          * ((r : ENNReal) * Y) := by
        rw [← hcast_b]; exact mul_le_mul_left hcardfibE Cσbn
    _ = (C : ENNReal) ^ 4 * (𝒰.branchingN b : ENNReal) * (r : ENNReal)
          * ((nds.card : ENNReal) * Y) := by ring
    _ ≤ (C : ENNReal) ^ 4 * (𝒰.branchingN b : ENNReal) * (r : ENNReal)
          * (Dnod * ((r : ENNReal) * X)) := by
        rw [← hcast_a]
        exact mul_le_mul_right hband_h
          ((C : ENNReal) ^ 4 * (𝒰.branchingN b : ENNReal) * (r : ENNReal))
    _ = X * ((tubeVolRatio (E := E) : ENNReal) ^ 2 * (C : ENNReal) ^ 4
          * (𝒰.branchingN b : ENNReal) * Dnod) := by rw [← hrco]; ring

/-! ### Alternative (ii)-2, translated -/

/-- The dimensional constant of `isFrostmanIn_nodesUnder_of_fibre`: three tube-volume comparisons,
one test-body thickening and the covering of the inflated fibre. -/
noncomputable def nodeTransportConst : NNReal :=
  tubeVolRatio (E := E) ^ 3 * thickenVolConstN (E := E) 1 * gapCoverCard (E := E)

/-- **Alternative (ii)-2, translated.**  If every exact-scale `ρ_a`-fibre of leaves thickened to
`ρ_b` is `B`-Frostman in its doubled anchor, then the nodes at index `b` under any node at index
`a` are Frostman in that node, with the constant multiplied by `nodeTransportConst * C ^ 5`.  The
branching number `N_{ρ_b}` cancels between the two sides. -/
theorem isFrostmanIn_nodesUnder_of_fibre {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C) (hs : s.Nonempty)
    (𝒰 : UniformTubeSet s T N C) {a b : ℕ} (hab : a ≤ b) (ha : a ≤ N) (hb : b ≤ N)
    (h2δ : 2 * δ ≤ gridScale δ N a) {j : ι} (hj : j ∈ 𝒰.cover.indexSet a) {B : ENNReal}
    (hB : ∀ i₂ ∈ s, ConvexSpaceBody.IsFrostmanIn (fibreIndex s T δ (gridScale δ N a) i₂)
      (fibreBodies T (gridScale δ N b))
      ((T i₂).rescale (2 * gridScale δ N a)).toConvexSpaceBody B) :
    ConvexSpaceBody.IsFrostmanIn (𝒰.nodesUnder b a j)
      (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
      (𝒰.cover.tube a j).toConvexSpaceBody
      ((nodeTransportConst (E := E) : ENNReal) * (C : ENNReal) ^ 5 * B) := by
  obtain ⟨i₀, hi₀⟩ := coverClass_nonempty_of_mem_parent 𝒰 ha hs hj
  set NB : ι → ConvexSpaceBody E := fun j' => (𝒰.cover.tube b j').toConvexSpaceBody
  set Kj : ConvexSpaceBody E := (𝒰.cover.tube a j).toConvexSpaceBody
  set Dnod : ENNReal := Kakeya.densityIn (𝒰.nodesUnder b a j) NB Kj
  set ν : ENNReal := ((𝒰.branchingN b : NNReal) : ENNReal)
  set TV : ENNReal := (tubeVolRatio (E := E) : ENNReal)
  set TC1 : ENNReal := (thickenVolConstN (E := E) 1 : ENNReal)
  set gcc : ENNReal := (gapCoverCard (E := E) : ENNReal)
  have hδb : δ ≤ gridScale δ N b := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [Nat.le_zero.mp hb]; simp [gridScale, hδ1]
    · simpa [gridScale_self δ hN] using gridScale_antitone hδ hδ1 N hb
  have hν0 : ν ≠ 0 := ENNReal.coe_ne_zero.mpr (branchingN_pos 𝒰 hC hs hb).ne'
  have hNTC : (nodeTransportConst (E := E) : ENNReal) = TV ^ 3 * TC1 * gcc := by
    simp [nodeTransportConst, TV, TC1, gcc, mul_assoc]
  have hstep2 : ∀ i₂ ∈ s, Kakeya.maxDensity (fibreIndex s T δ (gridScale δ N a) i₂)
      (fibreBodies T (gridScale δ N b))
        ≤ B * (TV ^ 2 * (C : ENNReal) ^ 4 * ν * Dnod) := by
    intro i₂ hi₂
    have hmem : ∀ i ∈ fibreIndex s T δ (gridScale δ N a) i₂,
        fibreBodies T (gridScale δ N b) i ≤
          ((T i₂).rescale (2 * gridScale δ N a)).toConvexSpaceBody := fun i hi =>
      (show i ∈ s ∧ fibreBodies T (gridScale δ N b) i ≤
          ((T i₂).rescale (2 * gridScale δ N a)).toConvexSpaceBody by
        simpa [fibreIndex, Kakeya.familyIn] using
          fibreIndex_subset_two_mul_of_member_le (σ := δ) (σ' := gridScale δ N b)
            (ρ := gridScale δ N a) le_rfl hδb (gridScale_antitone hδ hδ1 N hab) i₂ hi).2
    exact ((hB i₂ hi₂).maxDensity_le_of_carrier_subset hmem).trans
      (mul_le_mul_right
        (densityIn_fibre_thick_le_mul_densityIn_nodesUnder hδ hδ1 𝒰 hab ha hb hi₂ hj) B)
  intro K' _
  refine (ENNReal.mul_le_mul_iff_right hν0 ENNReal.coe_ne_top).mp ?_
  calc
    ν * Kakeya.densityIn (𝒰.nodesUnder b a j) NB K'
        = Kakeya.densityIn (𝒰.nodesUnder b a j) NB K' * ν := mul_comm _ _
    _ ≤ TV * (C : ENNReal) * TC1
            * Kakeya.maxDensity (fibreIndex s T δ (4 * gridScale δ N a) i₀)
                (fibreBodies T (gridScale δ N b)) :=
        densityIn_nodesUnder_mul_branchingN_le hδ hδ1 𝒰 hab ha hb hi₀ K'
    _ ≤ TV * (C : ENNReal) * TC1 *
            (gcc * (B * (TV ^ 2 * (C : ENNReal) ^ 4 * ν * Dnod))) := by
        gcongr
        exact maxDensity_fibre_inflated_le hδ h2δ hstep2
    _ = ν * ((nodeTransportConst (E := E) : ENNReal) * (C : ENNReal) ^ 5 * B * Dnod) := by
        rw [hNTC]; ring

/-! ### The majority set, translated -/

/-- The nodes at index `b` a quarter of whose class is good. -/
noncomputable def goodNodes {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : UniformTubeSet s T N C) (b : ℕ) (G : Finset ι) : Finset ι :=
  open scoped Classical in
  (𝒰.cover.indexSet b).filter (fun j =>
    (coverClass s (𝒰.cover.assign b) j).card
      ≤ 4 * ((coverClass s (𝒰.cover.assign b) j) ∩ G).card)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **A majority of leaves gives a fixed proportion of nodes.**  If half of the leaves are good,
the nodes a quarter of whose class is good form a fixed proportion of all nodes: the remaining
nodes carry at most three quarters of the leaves of their classes, so the good nodes carry at least
a quarter of all leaves, and comparable class sizes turn that into a proportion of nodes. -/
theorem card_parent_le_mul_card_goodNodes {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (hC : 1 ≤ C) (𝒰 : UniformTubeSet s T N C) {b : ℕ} (hb : b ≤ N)
    {G : Finset ι} (hG : G ⊆ s) (hGcard : s.card ≤ 2 * G.card) :
    ((𝒰.cover.indexSet b).card : NNReal) ≤ 4 * C ^ 2 * ((goodNodes 𝒰 b G).card : NNReal) := by
  classical
  set P := 𝒰.cover.indexSet b with hPdef
  set cl : ι → Finset ι := fun j => coverClass s (𝒰.cover.assign b) j with hcldef
  set Gd := goodNodes 𝒰 b G with hGddef
  have hGdsub : Gd ⊆ P := Finset.filter_subset _ _
  have hpart : s.card = ∑ j ∈ P, (cl j).card := by
    simp only [hcldef, coverClass]
    exact Finset.card_eq_sum_card_fiberwise fun i hi => 𝒰.cover.assign_mem b hb i hi
  have hpartG : G.card = ∑ j ∈ P, (cl j ∩ G).card := by
    have hcl : ∀ j, cl j ∩ G = G.filter fun i => 𝒰.cover.assign b i = j := fun j => by
      ext i
      simp only [hcldef, coverClass, Finset.mem_inter, Finset.mem_filter]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hG h.1, h.2⟩, h.1⟩⟩
    simp only [hcl]
    exact Finset.card_eq_sum_card_fiberwise fun i hi => 𝒰.cover.assign_mem b hb i (hG hi)
  have hsum_s : s.card = (∑ j ∈ Gd, (cl j).card) + (∑ j ∈ P \ Gd, (cl j).card) := by
    rw [hpart, add_comm]; exact (Finset.sum_sdiff hGdsub).symm
  have hsum_G : G.card = (∑ j ∈ Gd, (cl j ∩ G).card) + (∑ j ∈ P \ Gd, (cl j ∩ G).card) := by
    rw [hpartG, add_comm]; exact (Finset.sum_sdiff hGdsub).symm
  have hB_A : (∑ j ∈ Gd, (cl j ∩ G).card) ≤ (∑ j ∈ Gd, (cl j).card) :=
    Finset.sum_le_sum fun j _ => Finset.card_le_card Finset.inter_subset_left
  have h4BcAc : 4 * (∑ j ∈ P \ Gd, (cl j ∩ G).card) ≤ (∑ j ∈ P \ Gd, (cl j).card) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    obtain ⟨hjP, hjGd⟩ := Finset.mem_sdiff.mp hj
    by_contra hlt
    exact hjGd (by
      rw [hGddef, goodNodes, Finset.mem_filter]
      exact ⟨by simpa [P] using hjP, by simpa [cl] using (Nat.not_le.mp hlt).le⟩)
  have hkey : s.card ≤ 4 * ∑ j ∈ Gd, (cl j).card := by omega
  by_cases hs : s.Nonempty
  · have hsmall : (∑ j ∈ Gd, ((cl j).card : NNReal))
        ≤ (Gd.card : NNReal) * (C * 𝒰.branchingN b) :=
      (Finset.sum_le_sum fun j hj => 𝒰.card_class_le b hb j (hGdsub hj)).trans_eq
        (by rw [Finset.sum_const, nsmul_eq_mul])
    have hbig : (P.card : NNReal) * 𝒰.branchingN b ≤ C * (s.card : NNReal) := by
      calc
        (P.card : NNReal) * 𝒰.branchingN b = ∑ _j ∈ P, 𝒰.branchingN b := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ j ∈ P, C * ((cl j).card : NNReal) :=
              Finset.sum_le_sum fun j hj => 𝒰.le_card_class b hb j hj
        _ = C * (s.card : NNReal) := by rw [← Finset.mul_sum, hpart]; push_cast; ring
    have hkeyN : (s.card : NNReal) ≤ 4 * ∑ j ∈ Gd, ((cl j).card : NNReal) := by
      exact_mod_cast hkey
    refine le_of_mul_le_mul_right ?_ (branchingN_pos 𝒰 hC hs hb)
    calc
      (P.card : NNReal) * 𝒰.branchingN b ≤ C * (s.card : NNReal) := hbig
      _ ≤ C * (4 * ∑ j ∈ Gd, ((cl j).card : NNReal)) := mul_le_mul_right hkeyN C
      _ ≤ C * (4 * ((Gd.card : NNReal) * (C * 𝒰.branchingN b))) :=
          mul_le_mul_right (mul_le_mul_right hsmall 4) C
      _ = 4 * C ^ 2 * (Gd.card : NNReal) * 𝒰.branchingN b := by ring
  · have hGdP : Gd = P := by
      rw [hGddef, goodNodes, ← hPdef, Finset.filter_eq_self]
      intro j _
      simp [coverClass, Finset.not_nonempty_iff_eq_empty.mp hs]
    rw [← hGdP]
    exact le_mul_of_one_le_left zero_le
      ((one_le_pow₀ hC).trans (le_mul_of_one_le_left zero_le (by norm_num)))

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Every good node has a good leaf in its class. -/
theorem exists_good_mem_coverClass_of_mem_goodNodes {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (_hC : 1 ≤ C) (hs : s.Nonempty) (𝒰 : UniformTubeSet s T N C) {b : ℕ}
    (hb : b ≤ N) {G : Finset ι} {j : ι} (hj : j ∈ goodNodes 𝒰 b G) :
    ∃ i ∈ coverClass s (𝒰.cover.assign b) j, i ∈ G := by
  classical
  have hj' : j ∈ (𝒰.cover.indexSet b).filter (fun j =>
      (coverClass s (𝒰.cover.assign b) j).card
        ≤ 4 * ((coverClass s (𝒰.cover.assign b) j) ∩ G).card) := by
    simpa [goodNodes] using hj
  obtain ⟨hjp, hq⟩ := Finset.mem_filter.mp hj'
  obtain ⟨i₀, hi₀cls⟩ := coverClass_nonempty_of_mem_parent 𝒰 hb hs hjp
  obtain ⟨i, hiinter⟩ : ((coverClass s (𝒰.cover.assign b) j) ∩ G).Nonempty :=
    Finset.card_pos.mp (by have := Finset.card_pos.mpr ⟨i₀, hi₀cls⟩; omega)
  exact ⟨i, (Finset.mem_inter.mp hiinter).1, (Finset.mem_inter.mp hiinter).2⟩

/-! ### Aligning the nodes of a fibre with a dilated container

Alternative (ii)-3 is a *lower* bound, so its container has to be the one the leaf-anchored bound
already reaches, not the node itself.  The two are related by the containments recorded here.  Note
that neither of the two primitives the container chase seems to ask for is actually new.  A triangle
inequality turning `\operatorname{cth}_r(P)` into `P^{(r+\rho)}` is `Tube.cthickening_carrier`,
which gives it as an *equality*; and absorbing a containment into one dilation is
`Tube.rescale_le_rescale_of_body_le` (`Kakeya/MultiScaleFac/Branching.lean`), which even lets the
target radius be any `θ ≥ ρ + r` and so telescopes the whole chase into two steps. -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The alignment of alternative (ii)-3.**  If `j` is a node at the fine index `b` sitting inside
a node `j'` at the intermediate index `c` and `i₀` is a leaf of the class of `j`, then every leaf of
the exact-scale `ρ_c`-fibre of `i₀` has its `b`-node inside the `8ρ_c`-dilate of `j'` (the radii
accumulate to `2ρ_c + 4ρ_b ≤ 6ρ_c`). -/
theorem assign_mem_nodesIn_of_mem_fibre {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hNpos : 0 < N)
    (𝒰 : UniformTubeSet s T N C) {b c : ℕ} (hb : b ≤ N) (hcb : c ≤ b) {j j' i₀ : ι}
    (hi₀ : i₀ ∈ coverClass s (𝒰.cover.assign b) j)
    (hjj' : (𝒰.cover.tube b j).toConvexSpaceBody ≤ (𝒰.cover.tube c j').toConvexSpaceBody)
    {i : ι} (hi : i ∈ Kakeya.StickyKakeya.fibreIndex s T δ (gridScale δ N c) i₀) :
    𝒰.cover.assign b i ∈ 𝒰.nodesIn b
      (((𝒰.cover.tube c j').rescale (8 * gridScale δ N c)).toConvexSpaceBody) := by
  classical
  set σb : NNReal := gridScale δ N b
  set σc : NNReal := gridScale δ N c
  rw [coverClass, Finset.mem_filter] at hi₀
  rw [Kakeya.StickyKakeya.fibreIndex_self, Finset.mem_filter] at hi
  have hσbσc : σb ≤ σc := gridScale_antitone hδ hδ1 N hcb
  have hδ4σb : δ ≤ 4 * σb :=
    (by simpa [gridScale_self δ hNpos] using gridScale_antitone hδ hδ1 N hb :
      δ ≤ σb).trans (le_mul_of_one_le_left (by simp) (by norm_num))
  have hradius : σc + (σc + 4 * σb) ≤ 8 * σc :=
    calc σc + (σc + 4 * σb) ≤ σc + (σc + 4 * σc) := by gcongr
      _ = 6 * σc := by ring
      _ ≤ 8 * σc := mul_le_mul_left (by norm_num) _
  refine (𝒰.mem_nodesIn_iff b _ _).mpr ⟨𝒰.cover.assign_mem b hb i hi.1,
    (Tube.rescale_le_of_le (T i) (𝒰.cover.tube b (𝒰.cover.assign b i))
        (𝒰.cover.le_tube_assign b hb i hi.1)).trans
      ((Tube.rescale_le_rescale_of_body_le (T i) ((T i₀).rescale σc) hδ4σb le_rfl hi.2).trans
        (Tube.rescale_le_rescale_of_body_le (T i₀) (𝒰.cover.tube c j')
          (hδ4σb.trans le_add_self) hradius
          ((𝒰.cover.le_tube_assign b hb i₀ hi₀.1).trans (by rw [hi₀.2]; exact hjj'))))⟩

/-! ### The reverse transports, for alternative (ii)-3

The forward transports (`densityIn_nodesUnder_mul_branchingN_le`,
`densityIn_fibre_thick_le_mul_densityIn_nodesUnder`) turn a *fibre* bound into a *node* bound, which
is what an upper bound needs.  Alternative (ii)-3 needs the opposite: a lower bound on a node
Frostman constant from a lower bound on a fibre one, which means bounding the fibre constant
*above* by the node constant.  So both transports are needed with the inequalities reversed, and
the branching number `N_{ρ_b}` cancels between them exactly as before. -/

/-- Two tube dilations of comparable radii have comparable volumes. -/
theorem volume_rescale_le_mul_volume_rescale_of_le {δ₁ δ₂ : NNReal} (T₁ : Tube δ₁ E)
    (T₂ : Tube δ₂ E) {r₁ r₂ : NNReal} (hr : r₁ ≤ r₂) (hr₁ : r₁ ≤ 1) :
    volume (T₁.rescale r₁).carrier
      ≤ (tubeVolRatio (E := E) : ENNReal) * volume (T₂.rescale r₂).carrier := by
  have hccnn : tubeVolRatio (E := E) * Tube.le_volume.c (Module.finrank ℝ E)
      = Tube.volume_le.C (Module.finrank ℝ E) := by
    unfold tubeVolRatio
    exact div_mul_cancel₀ _ (Tube.le_volume.c_pos _).ne'
  calc volume (T₁.rescale r₁).carrier
      ≤ (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
          * (r₁ : ENNReal) ^ (Module.finrank ℝ E - 1) := by
        exact_mod_cast Tube.volume_le hr₁ (T₁.rescale r₁)
    _ ≤ (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
          * (r₂ : ENNReal) ^ (Module.finrank ℝ E - 1) := by gcongr
    _ = (tubeVolRatio (E := E) : ENNReal) * ((Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
          * (r₂ : ENNReal) ^ (Module.finrank ℝ E - 1)) := by
        rw [← mul_assoc, ← ENNReal.coe_mul, hccnn]
    _ ≤ (tubeVolRatio (E := E) : ENNReal) * volume (T₂.rescale r₂).carrier :=
        mul_le_mul_right (by exact_mod_cast Tube.le_volume (T₂.rescale r₂)) _

/-- The size of the covering used by `card_fibreIndex_inflated_le` at ratio `r`. -/
noncomputable def gapCoverCardN (r : ℕ) : NNReal :=
  2 * (25 : NNReal) ^ (2 * Module.finrank ℝ E) * (r : NNReal) ^ (2 * Module.finrank ℝ E)

/-- **An inflated fibre has boundedly many members, in units of the branching number.**  The
cardinality companion of `maxDensity_fibre_inflated_le`: cover the `r ρ_k`-fibre by exact-scale
`ρ_k`-fibres and bound each of those by `card_fibreIndex_le_of_uniformTubeSet`. -/
theorem card_fibreIndex_inflated_le {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (hδ : 0 < δ) (𝒰 : UniformTubeSet s T N C) {k : ℕ} (hk : k ≤ N)
    (h2δ : 2 * δ ≤ gridScale δ N k) {r : ℕ} (hr : 1 ≤ r) (i₀ : ι) :
    ((Kakeya.StickyKakeya.fibreIndex s T δ ((r : NNReal) * gridScale δ N k) i₀).card : NNReal)
      ≤ gapCoverCardN (E := E) r * C ^ 2 * 𝒰.branchingN k := by
  classical
  have hρpos : 0 < gridScale δ N k := gridScale_pos hδ N k
  obtain ⟨A, hAs, hAcard, hAcov⟩ :=
    exists_gapFibre_cover_of_ratio (s := s) (T := T) (δ := δ) (σ := δ)
      (ρ := gridScale δ N k) (ρ' := (r : NNReal) * gridScale δ N k) hρpos le_rfl h2δ
      (le_mul_of_one_le_left hρpos.le (by exact_mod_cast hr)) i₀
  have hcard : ((fibreIndex s T δ ((r : NNReal) * gridScale δ N k) i₀).card : NNReal)
      ≤ ∑ i₂ ∈ A, ((fibreIndex s T δ (gridScale δ N k) i₂).card : NNReal) := by
    have hsub : fibreIndex s T δ ((r : NNReal) * gridScale δ N k) i₀
        ⊆ A.biUnion (fun i₂ => fibreIndex s T δ (gridScale δ N k) i₂) := fun i hi =>
      Finset.mem_biUnion.mpr (hAcov i hi)
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hAcardN : (A.card : NNReal) ≤ gapCoverCardN (E := E) r := by
    have hne : ((gridScale δ N k : NNReal) : ℝ) ≠ 0 := by exact_mod_cast hρpos.ne'
    rw [show ((((r : NNReal) * gridScale δ N k : NNReal) : ℝ)
        / ((gridScale δ N k : NNReal) : ℝ)) = (r : ℝ) by push_cast; field_simp] at hAcard
    have h : (A.card : NNReal) ≤ 2 * (25 : NNReal) ^ (2 * Module.finrank ℝ E)
        * (r : NNReal) ^ (2 * Module.finrank ℝ E) := by exact_mod_cast hAcard
    exact h
  calc
    ((fibreIndex s T δ ((r : NNReal) * gridScale δ N k) i₀).card : NNReal)
        ≤ ∑ i₂ ∈ A, ((fibreIndex s T δ (gridScale δ N k) i₂).card : NNReal) := hcard
    _ ≤ ∑ _i₂ ∈ A, C ^ 2 * 𝒰.branchingN k :=
        Finset.sum_le_sum fun i₂ hi₂ => card_fibreIndex_le_of_uniformTubeSet 𝒰 hk (hAs hi₂)
    _ = (A.card : NNReal) * (C ^ 2 * 𝒰.branchingN k) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ gapCoverCardN (E := E) r * C ^ 2 * 𝒰.branchingN k := by
      rw [mul_assoc]
      exact mul_le_mul_left hAcardN (C ^ 2 * 𝒰.branchingN k)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **A clumped class fills the exact-scale fibre of any of its members.**  Given `clumped` — the
class of a node lies inside a single `ρ_k/4`-tube fibre — the whole class lies in the exact-scale
`ρ_k`-fibre of any member `i₀`, and the class lower bound of Definition 2.1 then gives the
branching number.  `UniformTubeSet` cannot supply this, so it appears as a hypothesis. -/
theorem branchingN_le_mul_card_fibreIndex_of_clumped {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C) {k : ℕ} (hk : k ≤ N) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hclump : ∃ i₂, coverClass s (𝒰.cover.assign k) (𝒰.cover.assign k i₀)
        ⊆ Kakeya.StickyKakeya.fibreIndex s T δ (gridScale δ N k / 4) i₂) :
    𝒰.branchingN k
      ≤ C * ((Kakeya.StickyKakeya.fibreIndex s T δ (gridScale δ N k) i₀).card : NNReal) := by
  classical
  obtain ⟨i₂, hclump⟩ := hclump
  have hmem : ∀ i ∈ coverClass s (𝒰.cover.assign k) (𝒰.cover.assign k i₀), i ∈ s ∧
      (T i).toConvexSpaceBody ≤ ((T i₂).rescale (gridScale δ N k / 4)).toConvexSpaceBody := by
    intro i hi
    have h := hclump hi
    rwa [Kakeya.StickyKakeya.fibreIndex_self, Finset.mem_filter] at h
  have hstep : ((T i₂).rescale (gridScale δ N k / 4)).toConvexSpaceBody
      ≤ ((T i₀).rescale (gridScale δ N k)).toConvexSpaceBody := by
    have h := Tube.rescale_le_of_le (T i₀) ((T i₂).rescale (gridScale δ N k / 4))
      (hmem i₀ (by simp [coverClass, hi₀])).2
    rwa [mul_comm, div_mul_cancel₀ _ (by norm_num : (4 : NNReal) ≠ 0)] at h
  have hcard : ((coverClass s (𝒰.cover.assign k) (𝒰.cover.assign k i₀)).card : NNReal)
      ≤ ((Kakeya.StickyKakeya.fibreIndex s T δ (gridScale δ N k) i₀).card : NNReal) := by
    refine Nat.cast_le.mpr (Finset.card_le_card fun i hi => ?_)
    rw [Kakeya.StickyKakeya.fibreIndex_self]
    exact Finset.mem_filter.mpr ⟨(hmem i hi).1, (hmem i hi).2.trans hstep⟩
  exact (𝒰.le_card_class k hk (𝒰.cover.assign k i₀)
    (𝒰.cover.assign_mem k hk i₀ hi₀)).trans (mul_le_mul_right hcard C)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The dilated test bodies of alternative (ii)-3 stay inside its container.**  A body inside the
doubled leaf anchor `T_{i₀}^{(2ρ_c)}`, thickened by `4ρ_b`, still lies in `P_{c,j'}^{(8ρ_c)}`: the
radii accumulate to `ρ_c + 2ρ_c + 4ρ_b ≤ 7ρ_c`.  This is what fixes the constant `8`. -/
theorem thickenBody_le_container {δ : NNReal} {T : ι → Tube δ E} {σb σc : NNReal}
    (hσ : σb ≤ σc) {i₀ : ι} {P : Tube σc E}
    (hi₀P : (T i₀).toConvexSpaceBody ≤ P.toConvexSpaceBody) (hδσc : δ ≤ 2 * σc)
    {K' : ConvexSpaceBody E} (hK' : K' ≤ ((T i₀).rescale (2 * σc)).toConvexSpaceBody) :
    thickenBody K' (4 * σb) ≤ (P.rescale (8 * σc)).toConvexSpaceBody := by
  have hradius : σc + (2 * σc + 4 * σb) ≤ 8 * σc := by
    calc σc + (2 * σc + 4 * σb) ≤ σc + (2 * σc + 4 * σc) := by gcongr
      _ = 7 * σc := by ring
      _ ≤ 8 * σc := mul_le_mul_left (by norm_num) _
  calc thickenBody K' (4 * σb) = K'.cthickening ((4 * σb : NNReal) : ℝ) := rfl
    _ ≤ ((T i₀).rescale (2 * σc)).toConvexSpaceBody.cthickening ((4 * σb : NNReal) : ℝ) :=
      ConvexSpaceBody.cthickening_mono _ hK'
    _ = ((T i₀).rescale (2 * σc + 4 * σb)).toConvexSpaceBody :=
      ((T i₀).rescale (2 * σc)).toConvexBody_cthickening_eq (4 * σb)
    _ ≤ (P.rescale (8 * σc)).toConvexSpaceBody :=
      Tube.rescale_le_rescale_of_body_le (T i₀) P (hδσc.trans le_self_add) hradius hi₀P

/-- **The grid never drops below the leaf scale.**  For `k ≤ N` the grid scale `ρ_k` is at least
`δ = ρ_N`. -/
private theorem delta_le_gridScale {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N k : ℕ}
    (hN : 0 < N) (hk : k ≤ N) : δ ≤ gridScale δ N k := by -- (extracted by Fuse golfer)
  have h := gridScale_antitone hδ hδ1 N hk
  rwa [gridScale_self δ hN] at h

/-- **The reverse transport, node side.**  The density of an exact-scale `ρ_c`-fibre of leaves
thickened to `ρ_b`, in any test body, is at most `C N_{ρ_b}` times the density of the `b`-nodes of
the container in that test body thickened by `4ρ_b`. -/
theorem densityIn_fibre_le_mul_branchingN_mul_densityIn_nodesIn {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hNpos : 0 < N)
    (𝒰 : UniformTubeSet s T N C) {b c : ℕ} (hb : b ≤ N) (hcb : c ≤ b) {j j' i₀ : ι}
    (hi₀ : i₀ ∈ coverClass s (𝒰.cover.assign b) j)
    (hjj' : (𝒰.cover.tube b j).toConvexSpaceBody ≤ (𝒰.cover.tube c j').toConvexSpaceBody)
    (K' : ConvexSpaceBody E) :
    Kakeya.densityIn (Kakeya.StickyKakeya.fibreIndex s T δ (gridScale δ N c) i₀)
        (fibreBodies T (gridScale δ N b)) K'
      ≤ (tubeVolRatio (E := E) : ENNReal) * (C : ENNReal)
          * (thickenVolConstN (E := E) 4 : ENNReal) * (𝒰.branchingN b : ENNReal)
          * Kakeya.densityIn
              (𝒰.nodesIn b
                (((𝒰.cover.tube c j').rescale (8 * gridScale δ N c)).toConvexSpaceBody))
              (fun w => (𝒰.cover.tube b w).toConvexSpaceBody)
              (thickenBody K' (4 * gridScale δ N b)) := by
  classical
  set σb : NNReal := gridScale δ N b
  set σc : NNReal := gridScale δ N c
  set Kc : ConvexSpaceBody E := ((𝒰.cover.tube c j').rescale (8 * σc)).toConvexSpaceBody
  set NB : ι → ConvexSpaceBody E := fun w => (𝒰.cover.tube b w).toConvexSpaceBody
  set W : ι → ConvexSpaceBody E := fibreBodies T σb
  set Fib : Finset ι := Kakeya.StickyKakeya.fibreIndex s T δ σc i₀
  set nodes : Finset ι := 𝒰.nodesIn b Kc
  set Fib' : Finset ι := Fib.filter (fun i => W i ≤ K')
  set nodes' : Finset ι := nodes.filter (fun w => NB w ≤ thickenBody K' (4 * σb))
  set L : ENNReal := ∑ i ∈ Fib', volume (W i).carrier
  set B : ENNReal := ∑ w ∈ nodes', volume (NB w).carrier
  set u : ENNReal := volume K'.carrier
  set tvol : ENNReal := volume (thickenBody K' (4 * σb)).carrier
  set TVR : ENNReal := (tubeVolRatio (E := E) : ENNReal)
  set BN : ENNReal := (𝒰.branchingN b : ENNReal)
  set TC4 : ENNReal := (thickenVolConstN (E := E) 4 : ENNReal)
  set P : ENNReal := TVR * (C : ENNReal) * BN
  have hdL : Kakeya.densityIn Fib W K' = L / u := rfl
  have hdR : Kakeya.densityIn nodes NB (thickenBody K' (4 * σb)) = B / tvol := rfl
  have hσb1 : σb ≤ 1 := gridScale_le_one hδ1 N b
  have hδσb : δ ≤ σb := delta_le_gridScale hδ hδ1 hNpos hb
  have hdisj : (nodes' : Set ι).PairwiseDisjoint
      (fun w => coverClass s (𝒰.cover.assign b) w) := fun w₁ _ w₂ _ hne => by
    simp only [Function.onFun, Finset.disjoint_left, coverClass, Finset.mem_filter]
    rintro i ⟨-, rfl⟩ ⟨-, h⟩
    exact hne h
  by_cases hFibEmpty : Fib' = ∅
  · rw [hdL, show L = 0 from by simp [L, Fib', hFibEmpty]]
    simp
  · obtain ⟨i, hiFib'⟩ := Finset.nonempty_iff_ne_empty.mpr hFibEmpty
    have hWK : W i ≤ K' := (Finset.mem_filter.mp hiFib').2
    have hFib'_nodes' : Fib' ⊆ nodes'.biUnion (fun w => coverClass s (𝒰.cover.assign b) w) := by
      intro i' hiF'
      obtain ⟨hiFib'2, hWK'⟩ := Finset.mem_filter.mp hiF'
      have hiF'_mem : i' ∈ s ∧
          (T i').toConvexSpaceBody ≤ ((T i₀).rescale σc).toConvexSpaceBody := by
        simpa [Fib, fibreIndex_self] using hiFib'2
      have hNBw' : NB (𝒰.cover.assign b i') ≤ thickenBody K' (4 * σb) :=
        (Tube.rescale_le_of_le (T i') (𝒰.cover.tube b (𝒰.cover.assign b i'))
              (𝒰.cover.le_tube_assign b hb i' hiF'_mem.1)).trans
          (rescale_le_thickenBody (T i') (4 * σb)
            ((Tube.le_rescale (T i') hδσb).trans hWK'))
      exact Finset.mem_biUnion.mpr ⟨𝒰.cover.assign b i', Finset.mem_filter.mpr
        ⟨assign_mem_nodesIn_of_mem_fibre hδ hδ1 hNpos 𝒰 hb hcb hi₀ hjj' hiFib'2, hNBw'⟩,
        Finset.mem_filter.mpr ⟨hiF'_mem.1, rfl⟩⟩
    have hposV : 0 < volume ((T i).rescale σb).carrier :=
      lt_of_lt_of_le (ENNReal.coe_pos.mpr (mul_pos (Tube.le_volume.c_pos _)
          (pow_pos (gridScale_pos hδ N b) _)))
        (by simpa using Tube.le_volume ((T i).rescale σb))
    have hWKr : ((T i).rescale σb).toConvexSpaceBody ≤ K' := hWK
    have hposu : 0 < u := hposV.trans_le (measure_mono hWKr)
    have hu_le_tvol : u ≤ tvol := measure_mono (le_thickenBody K' (4 * σb))
    have htvolQ : tvol ≤ TC4 * u :=
      volume_thickenBody_le_nsmul ((T i).rescale σb) hWKr (ρ := 4 * σb) (m := 4) (by simp)
    have hsumClass : ∀ w ∈ nodes',
        (∑ i' ∈ coverClass s (𝒰.cover.assign b) w, volume (W i').carrier)
          ≤ TVR * (C : ENNReal) * BN * volume (NB w).carrier := by
      intro w hw'
      have hclsCardE : ((coverClass s (𝒰.cover.assign b) w).card : ENNReal)
          ≤ (C : ENNReal) * BN := by
        simpa [BN, ENNReal.coe_mul] using ENNReal.coe_le_coe.mpr (𝒰.card_class_le b hb w
          ((𝒰.mem_nodesIn_iff b Kc w).mp (Finset.mem_filter.mp hw').1).1)
      have hvol_i : ∀ i' ∈ coverClass s (𝒰.cover.assign b) w,
          volume (W i').carrier ≤ TVR * volume (NB w).carrier := fun i' _ => by
        simpa [W, TVR, NB, fibreBodies] using
          volume_rescale_le_mul_volume_rescale_of_le (T i') (𝒰.cover.tube b w) le_rfl hσb1
      calc
        (∑ i' ∈ coverClass s (𝒰.cover.assign b) w, volume (W i').carrier)
            ≤ ∑ _i' ∈ coverClass s (𝒰.cover.assign b) w, TVR * volume (NB w).carrier :=
              Finset.sum_le_sum hvol_i
        _ = (coverClass s (𝒰.cover.assign b) w).card * (TVR * volume (NB w).carrier) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ TVR * (C : ENNReal) * BN * volume (NB w).carrier :=
              (mul_le_mul_left hclsCardE _).trans_eq (by ring)
    have hmain1 : L ≤ P * B := by
      calc
        L ≤ ∑ i' ∈ nodes'.biUnion (fun w => coverClass s (𝒰.cover.assign b) w),
              volume (W i').carrier := Finset.sum_le_sum_of_subset hFib'_nodes'
        _ = ∑ w ∈ nodes', ∑ i' ∈ coverClass s (𝒰.cover.assign b) w,
              volume (W i').carrier := by
              rw [Finset.sum_biUnion hdisj]
        _ ≤ ∑ w ∈ nodes', TVR * (C : ENNReal) * BN * volume (NB w).carrier :=
              Finset.sum_le_sum hsumClass
        _ = P * B := by rw [← Finset.mul_sum]
    have hmain2 : L * tvol ≤ P * TC4 * B * u :=
      (mul_le_mul' hmain1 htvolQ).trans_eq (by ring)
    have hdensity : Kakeya.densityIn Fib W K' ≤ P * TC4
        * Kakeya.densityIn nodes NB (thickenBody K' (4 * σb)) := by
      rw [hdL, hdR, ← mul_div_assoc]
      refine (ENNReal.le_div_iff_mul_le (Or.inl (hposu.trans_le hu_le_tvol).ne')
        (Or.inl (thickenBody K' (4 * σb)).isCompact.measure_ne_top)).mpr ?_
      calc L / u * tvol = L * tvol / u := by
            rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
        _ ≤ P * TC4 * B := (ENNReal.div_le_iff_le_mul (Or.inl hposu.ne')
              (Or.inl K'.isCompact.measure_ne_top)).mpr hmain2
    exact hdensity.trans_eq (by dsimp only [P]; ring)

/-- The constant of `branchingN_mul_densityIn_nodesIn_le`. -/
noncomputable def nodeReverseConst : NNReal :=
  tubeVolRatio (E := E) ^ 3 * gapCoverCardN (E := E) 12

/-- **The reverse transport, anchor side.**  The density of the `b`-nodes of the container in the
container itself, weighted by the branching number, is at most the density of the exact-scale
`ρ_c`-fibre of `i₀` in its doubled anchor.  Finiteness comes from `card_fibreIndex_inflated_le`
together with the clumping hypothesis via `branchingN_le_mul_card_fibreIndex_of_clumped`. -/
theorem branchingN_mul_densityIn_nodesIn_le {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hNpos : 0 < N) (_hC : 1 ≤ C)
    (𝒰 : UniformTubeSet s T N C) {b c : ℕ} (hb : b ≤ N) (hc : c ≤ N) (hcb : c ≤ b)
    (h2δ : 2 * δ ≤ gridScale δ N c) {j j' i₀ : ι}
    (hi₀ : i₀ ∈ coverClass s (𝒰.cover.assign b) j)
    (hjj' : (𝒰.cover.tube b j).toConvexSpaceBody ≤ (𝒰.cover.tube c j').toConvexSpaceBody)
    (hclump : ∃ i₂, coverClass s (𝒰.cover.assign c) (𝒰.cover.assign c i₀)
        ⊆ Kakeya.StickyKakeya.fibreIndex s T δ (gridScale δ N c / 4) i₂) :
    (𝒰.branchingN b : ENNReal)
        * Kakeya.densityIn
            (𝒰.nodesIn b
              (((𝒰.cover.tube c j').rescale (8 * gridScale δ N c)).toConvexSpaceBody))
            (fun w => (𝒰.cover.tube b w).toConvexSpaceBody)
            (((𝒰.cover.tube c j').rescale (8 * gridScale δ N c)).toConvexSpaceBody)
      ≤ (nodeReverseConst (E := E) : ENNReal) * (C : ENNReal) ^ 4
          * Kakeya.densityIn (Kakeya.StickyKakeya.fibreIndex s T δ (gridScale δ N c) i₀)
              (fibreBodies T (gridScale δ N b))
              ((T i₀).rescale (2 * gridScale δ N c)).toConvexSpaceBody := by
  classical
  set σb : NNReal := gridScale δ N b
  set σc : NNReal := gridScale δ N c
  set P : Tube σc E := 𝒰.cover.tube c j'
  set K : ConvexSpaceBody E := (P.rescale (8 * σc)).toConvexSpaceBody
  set NB : ι → ConvexSpaceBody E := fun w => (𝒰.cover.tube b w).toConvexSpaceBody
  set Fib : Finset ι := Kakeya.StickyKakeya.fibreIndex s T δ σc i₀
  set FB : ι → ConvexSpaceBody E := fun i => (Kakeya.StickyKakeya.fibreBodies T σb) i
  set Kf : ConvexSpaceBody E := ((T i₀).rescale (2 * σc)).toConvexSpaceBody
  set nds : Finset ι := 𝒰.nodesIn b K
  set U : Finset ι := nds.biUnion (fun w => coverClass s (𝒰.cover.assign b) w)
  set L : ENNReal := ∑ w ∈ nds, volume (NB w).carrier
  set S : ENNReal := ∑ i ∈ U, volume (FB i).carrier
  set RF : ENNReal := ∑ i ∈ Fib, volume (FB i).carrier
  set BN : ENNReal := (𝒰.branchingN b : ENNReal)
  set tvr : ENNReal := (tubeVolRatio (E := E) : ENNReal)
  set gap : ENNReal := (gapCoverCardN (E := E) 12 : ENNReal) with hgap
  set Ce : ENNReal := (C : ENNReal) with hCe
  set volK : ENNReal := volume K.carrier
  set volKf : ENNReal := volume Kf.carrier
  have hδσb : δ ≤ σb := delta_le_gridScale hδ hδ1 hNpos hb
  have hδσc : δ ≤ σc := delta_le_gridScale hδ hδ1 hNpos hc
  have hσbσc : σb ≤ σc := gridScale_antitone hδ hδ1 N hcb
  have hσb1 : σb ≤ 1 := gridScale_le_one hδ1 N b
  obtain ⟨hi₀s, hassign₀⟩ := Finset.mem_filter.mp hi₀
  have hi₀P : (T i₀).toConvexSpaceBody ≤ P.toConvexSpaceBody :=
    (hassign₀ ▸ 𝒰.cover.le_tube_assign b hb i₀ hi₀s).trans hjj'
  have vol_comp : ∀ i j : ι, volume (FB i).carrier ≤ tvr * volume (FB j).carrier := fun i j =>
    volume_rescale_le_mul_volume_rescale_of_le (T i) (T j) (le_refl σb) hσb1
  have hmem : ∀ w ∈ nds, NB w ≤ K := fun w hw => ((𝒰.mem_nodesIn_iff b K w).mp hw).2
  have ht₀ : nds ⊆ 𝒰.cover.indexSet b := fun w hw => ((𝒰.mem_nodesIn_iff b K w).mp hw).1
  have hdL : Kakeya.densityIn nds NB K = L / volK := by
    unfold Kakeya.densityIn
    dsimp [L, volK]
    rw [Finset.filter_eq_self.mpr hmem]
  have hdR : Kakeya.densityIn Fib FB Kf = RF / volKf := by
    unfold Kakeya.densityIn
    dsimp [RF, volKf]
    have hmemR : ∀ i ∈ Fib, FB i ≤ Kf := fun i hi =>
      Tube.rescale_le_rescale_of_body_le (T i) ((T i₀).rescale σc) hδσb
        (by rw [two_mul]; exact add_le_add_right hσbσc σc)
        (by dsimp only [Fib] at hi; rw [fibreIndex_self, Finset.mem_filter] at hi; exact hi.2)
    rw [Finset.filter_eq_self.mpr hmemR]
  have h2 : BN * L ≤ tvr * Ce * S :=
    (sum_volume_nodes_mul_branchingN_le hδ hδ1 𝒰 hb ht₀).trans_eq' (mul_comm L BN)
  have hinc : U ⊆ Kakeya.StickyKakeya.fibreIndex s T δ (12 * σc) i₀ := by
    intro i hiU
    obtain ⟨w, hwnds, hiU'⟩ := Finset.mem_biUnion.mp hiU
    obtain ⟨his, hassign⟩ := Finset.mem_filter.mp hiU'
    have hTi_K : (T i).toConvexSpaceBody ≤ (P.rescale (8 * σc)).toConvexSpaceBody :=
      (hassign ▸ 𝒰.cover.le_tube_assign b hb i his).trans (hmem w hwnds)
    have hPB : (P.rescale (8 * σc)).toConvexSpaceBody
        ≤ ((T i₀).rescale (12 * σc)).toConvexSpaceBody :=
      Tube.rescale_le_rescale_of_body_le P ((T i₀).rescale (4 * σc))
        (le_mul_of_one_le_left zero_le (by norm_num)) (le_of_eq (by ring))
        (by simpa using (Tube.rescale_le_of_le (T i₀) P hi₀P))
    rw [Kakeya.StickyKakeya.fibreIndex_self]
    exact Finset.mem_filter.mpr ⟨his, hTi_K.trans hPB⟩
  have hCardU : (U.card : NNReal) ≤ gapCoverCardN (E := E) 12 * C ^ 2 * 𝒰.branchingN c :=
    (by exact_mod_cast Finset.card_le_card hinc : (U.card : NNReal) ≤
        (Kakeya.StickyKakeya.fibreIndex s T δ (12 * σc) i₀).card).trans
      (by simpa only [Nat.cast_ofNat] using
        card_fibreIndex_inflated_le hδ 𝒰 hc h2δ (by norm_num : (1 : ℕ) ≤ 12) i₀)
  have hBnc : 𝒰.branchingN c ≤ C * (Fib.card : NNReal) :=
    branchingN_le_mul_card_fibreIndex_of_clumped 𝒰 hc hi₀s hclump
  have hScentral : S ≤ gap * Ce ^ 3 * tvr ^ 2 * RF := by
    let hf₀ : ENNReal := volume (FB i₀).carrier
    have hS_le : S ≤ (U.card : ENNReal) * (tvr * hf₀) := by
      dsimp only [S]
      exact (Finset.sum_le_sum fun i _ => vol_comp i i₀).trans_eq
        (by rw [Finset.sum_const, nsmul_eq_mul])
    have hF_le : (Fib.card : ENNReal) * hf₀ ≤ tvr * RF := by
      rw [show (Fib.card : ENNReal) * hf₀ = ∑ _i ∈ Fib, hf₀ from
        by rw [Finset.sum_const, nsmul_eq_mul]]
      exact (Finset.sum_le_sum fun i _ => vol_comp i₀ i).trans_eq
        (by dsimp only [RF]; rw [Finset.mul_sum])
    have hRU : (U.card : ENNReal) ≤ gap * Ce ^ 2 * (𝒰.branchingN c : ENNReal) := by
      rw [hgap, hCe]; exact_mod_cast hCardU
    have hBc : (𝒰.branchingN c : ENNReal) ≤ Ce * (Fib.card : ENNReal) := by
      rw [hCe]; exact_mod_cast hBnc
    calc
      S ≤ (U.card : ENNReal) * (tvr * hf₀) := hS_le
      _ ≤ (gap * Ce ^ 2 * (Ce * (Fib.card : ENNReal))) * (tvr * hf₀) :=
          mul_le_mul_left (hRU.trans (mul_le_mul_right hBc _)) _
      _ = gap * Ce ^ 3 * tvr * ((Fib.card : ENNReal) * hf₀) := by ring
      _ ≤ gap * Ce ^ 3 * tvr * (tvr * RF) := mul_le_mul_right hF_le _
      _ = gap * Ce ^ 3 * tvr ^ 2 * RF := by ring
  have hKf_le_K : volKf ≤ volK :=
    measure_mono (SetLike.coe_subset_coe.mpr (Tube.rescale_le_rescale_of_body_le (T i₀) P
      (σ := 2 * σc) (θ := 8 * σc) (hδσc.trans (le_mul_of_one_le_left zero_le (by norm_num)))
      (by rw [show σc + 2 * σc = 3 * σc from by ring]; exact mul_le_mul_left (by norm_num) σc)
      hi₀P))
  rw [hdL, hdR]
  calc
    BN * (L / volK) = (BN * L) / volK := (mul_div_assoc _ _ _).symm
    _ ≤ (tvr * Ce * (gap * Ce ^ 3 * tvr ^ 2 * RF)) / volK :=
        ENNReal.div_le_div_right (h2.trans (mul_le_mul_right hScentral (tvr * Ce))) volK
    _ ≤ (tvr ^ 3 * gap * Ce ^ 4 * RF) / volKf := by
        rw [show tvr * Ce * (gap * Ce ^ 3 * tvr ^ 2 * RF)
          = tvr ^ 3 * gap * Ce ^ 4 * RF from by ring]
        exact ENNReal.div_le_div le_rfl hKf_le_K
    _ = (tvr ^ 3 * gap * Ce ^ 4) * (RF / volKf) := mul_div_assoc _ _ _
    _ = (nodeReverseConst (E := E) : ENNReal) * (C : ENNReal) ^ 4 * (RF / volKf) := by
            simp [nodeReverseConst, tvr, gap, Ce]

/-- The constant of `frostmanConstant_fibre_le_mul_frostmanConstant_nodesIn`. -/
noncomputable def fibreFromNodeConst : NNReal :=
  tubeVolRatio (E := E) * thickenVolConstN (E := E) 4 * nodeReverseConst (E := E)

/-- **Alternative (ii)-3, translated.**  The leaf-anchored fibre Frostman constant is at most a
constant times the node Frostman constant on the dilated container, so a lower bound on the former
gives one on the latter.

The two reverse transports supply numerator and denominator, and `N_{ρ_b}` cancels between them. -/
theorem frostmanConstant_fibre_le_mul_frostmanConstant_nodesIn {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hNpos : 0 < N) (hC : 1 ≤ C)
    (𝒰 : UniformTubeSet s T N C) {b c : ℕ} (hb : b ≤ N) (hc : c ≤ N) (hcb : c ≤ b)
    (h2δ : 2 * δ ≤ gridScale δ N c) {j j' i₀ : ι}
    (hi₀ : i₀ ∈ coverClass s (𝒰.cover.assign b) j)
    (hjj' : (𝒰.cover.tube b j).toConvexSpaceBody ≤ (𝒰.cover.tube c j').toConvexSpaceBody)
    (hclump : ∃ i₂, coverClass s (𝒰.cover.assign c) (𝒰.cover.assign c i₀)
        ⊆ Kakeya.StickyKakeya.fibreIndex s T δ (gridScale δ N c / 4) i₂) :
    ConvexSpaceBody.frostmanConstant
        (Kakeya.StickyKakeya.fibreIndex s T δ (gridScale δ N c) i₀)
        (fibreBodies T (gridScale δ N b))
        ((T i₀).rescale (2 * gridScale δ N c)).toConvexSpaceBody
      ≤ (fibreFromNodeConst (E := E) : ENNReal) * (C : ENNReal) ^ 5
          * ConvexSpaceBody.frostmanConstant
              (𝒰.nodesIn b
                (((𝒰.cover.tube c j').rescale (8 * gridScale δ N c)).toConvexSpaceBody))
              (fun w => (𝒰.cover.tube b w).toConvexSpaceBody)
              (((𝒰.cover.tube c j').rescale (8 * gridScale δ N c)).toConvexSpaceBody) := by
  classical
  set σb : NNReal := gridScale δ N b
  set σc : NNReal := gridScale δ N c
  set K : ConvexSpaceBody E :=
    ((𝒰.cover.tube c j').rescale (8 * gridScale δ N c)).toConvexSpaceBody
  set NB : ι → ConvexSpaceBody E := fun w => (𝒰.cover.tube b w).toConvexSpaceBody
  set Nod : Finset ι := 𝒰.nodesIn b K
  set Fib : Finset ι := Kakeya.StickyKakeya.fibreIndex s T δ σc i₀
  set Kf : ConvexSpaceBody E := ((T i₀).rescale (2 * σc)).toConvexSpaceBody
  set A : ENNReal := ConvexSpaceBody.frostmanConstant Nod NB K
  set TV : ENNReal := (tubeVolRatio (E := E) : ENNReal)
  set CEn : ENNReal := (C : ENNReal)
  set TCN4 : ENNReal := (thickenVolConstN (E := E) 4 : ENNReal)
  set BN : ENNReal := (𝒰.branchingN b : ENNReal)
  set NRC : ENNReal := (nodeReverseConst (E := E) : ENNReal)
  have hA : ConvexSpaceBody.IsFrostmanIn Nod NB K A :=
    ConvexSpaceBody.isFrostmanIn_frostmanConstant
  have hσ : σb ≤ σc := gridScale_antitone hδ hδ1 N hcb
  have hδσc : δ ≤ 2 * σc :=
    (le_mul_of_one_le_left hδ.le one_le_two).trans
      (h2δ.trans (le_mul_of_one_le_left (zero_le : (0 : NNReal) ≤ σc) one_le_two))
  have hi₀pair : i₀ ∈ s ∧ 𝒰.cover.assign b i₀ = j := Finset.mem_filter.mp hi₀
  have hi₀P : (T i₀).toConvexSpaceBody ≤ (𝒰.cover.tube c j').toConvexSpaceBody :=
    le_trans (hi₀pair.2 ▸ 𝒰.cover.le_tube_assign b hb i₀ hi₀pair.1) hjj'
  have hFC : (fibreFromNodeConst (E := E) : ENNReal) = TV * TCN4 * NRC := by
    simp [fibreFromNodeConst, TV, TCN4, NRC, mul_assoc]
  apply ConvexSpaceBody.frostmanConstant_le_of_isFrostmanIn
  intro K' hK'
  have hd : BN * densityIn Nod NB K ≤ NRC * CEn ^ 4 * densityIn Fib (fibreBodies T σb) Kf :=
    branchingN_mul_densityIn_nodesIn_le hδ hδ1 hNpos hC 𝒰 hb hc hcb h2δ hi₀ hjj' hclump
  calc
    densityIn Fib (fibreBodies T σb) K'
        ≤ TV * CEn * TCN4 * BN * densityIn Nod NB (thickenBody K' (4 * σb)) :=
        densityIn_fibre_le_mul_branchingN_mul_densityIn_nodesIn hδ hδ1 hNpos 𝒰 hb hcb hi₀ hjj' K'
    _ ≤ TV * CEn * TCN4 * BN * (A * densityIn Nod NB K) :=
        mul_le_mul_right (hA _ (thickenBody_le_container hσ hi₀P hδσc hK')) _
    _ = TV * CEn * TCN4 * A * (BN * densityIn Nod NB K) := by ring
    _ ≤ TV * CEn * TCN4 * A * (NRC * CEn ^ 4 * densityIn Fib (fibreBodies T σb) Kf) :=
        mul_le_mul_right hd _
    _ = (fibreFromNodeConst (E := E) : ENNReal) * CEn ^ 5 * A
        * densityIn Fib (fibreBodies T σb) Kf := by
        rw [hFC]
        ring

end MultiScaleFac

end Kakeya
