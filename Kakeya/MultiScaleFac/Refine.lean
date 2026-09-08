/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.Stopping

/-!
# The per-node split test and the majority side of a split

The stopping-time design preceding the current GWZ Lemma 7.7(A)
(`Kakeya.MultiScaleFac.dividingScalesFrostman`) runs the block-level test
`Kakeya.MultiScaleFac.SplitTest`, which is `∃ c ∀ i₀`: one cut index carrying the block bound
simultaneously at *every* anchor.  Its negation therefore supplies only one anchor per scale,
which is why that form's alternative (ii) has an existential lower bound — too weak for the
consumer in GWZ §8.

The refined form `Kakeya.MultiScaleFac.dividingScalesFrostman` runs the *per-node* test
`NodeSplitTest` instead, which is `∃ c` for one fixed anchor.  Its negation is available at every
node of the failing side simultaneously, which is what turns the lower bound universal.  The price
is that the passing side no longer shares a cut index; `exists_common_cut_of_forall_nodeSplitTest`
buys one back by a pigeonhole over the at most `N + 1` admissible grid indices, at the cost of
passing to a subset — the refinement of the conclusion.

That pigeonhole is over grid *indices*, not over real scales: the Lean `SplitTest` already encodes
the blueprint's test window as a pair of margin inequalities on `c : ℕ`, so the loss is the
`δ`-independent factor `N + 1` rather than the blueprint's `1 + log₂(1/δ)`, and no rounding of a
real witness scale to the grid is needed.

Three notions of index set occur and must not be conflated.  In `BlockFrostmanOn t P …` the set
`t` is the family in which the *fibres* are formed and `P` is the set of *anchors* carrying the
bound; `Kakeya.MultiScaleFac.BlockFrostman` is the diagonal case `P = t`.  Shrinking `t` changes
the fibres and hence the Frostman constants: an upper bound descends to a proportional subfamily
at a bounded cost, a lower bound descends in no generality at all.
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
  {ι : Type*}

/-- **The block bound at a prescribed set of anchors.**  `BlockFrostmanOn t P T N C ζ a b` says that
`BlockFrostmanAt t T N C ζ a b i₀` holds at every anchor `i₀ ∈ P`, the fibres being formed inside
`t`.  The two index sets play different roles: `t` determines the *fibres*, hence the Frostman
constants, while `P` only selects which anchors are asserted. -/
def BlockFrostmanOn {δ : NNReal} (t P : Finset ι) (T : ι → Tube δ E) (N : ℕ) (C : NNReal) (ζ : ℝ)
    (a b : ℕ) : Prop :=
  ∀ i₀ ∈ P, BlockFrostmanAt t T N C ζ a b i₀

/-! ### The node test as a parameter

Both halves of GWZ Lemma 7.7 run the same machine on top of a per-node block bound: a pass/fail
split of the current index set according to whether *some* admissible cut index carries the bound at
that node, and a pigeonhole exchanging `∀ i₀ ∃ c` for `∃ c ∀ i₀` at the price of a subset.  Only the
tested predicate differs — `Kakeya.MultiScaleFac.BlockFrostmanAt` read on the fine half `(c,b)` in
half (A), `Kakeya.MultiScaleFac.BlockKatzTaoAt` read on the coarse half `(a,c)` in half (B), the
opposite half in each case because the two constants are inherited in opposite directions.

The machine is therefore stated once for an arbitrary family of node predicates
`Q : ℕ → ι → Prop` indexed by the candidate cut index and an arbitrary margin `M : ℕ`, and both
halves are instances: `NodeSplitTest` and `Kakeya.MultiScaleFac.NodeSplitTestKT` are
`NodeSplitTestOf` at their own `Q`, with `M = ⌈ε(b-a)⌉`. -/

/-- **The abstract per-node split test.**  The node `i₀` passes if some index `c` at margin `M` from
both ends of the block `(a,b)` satisfies the node predicate `Q c`. -/
def NodeSplitTestOf (Q : ℕ → ι → Prop) (M a b : ℕ) (i₀ : ι) : Prop :=
  ∃ c : ℕ, a + M ≤ c ∧ c + M ≤ b ∧ Q c i₀

/-- **The passing side of an abstract split.**  The nodes of `t` that pass `NodeSplitTestOf Q M a
b`. -/
noncomputable def passingNodesOf (t : Finset ι) (Q : ℕ → ι → Prop) (M a b : ℕ) : Finset ι :=
  open scoped Classical in
  t.filter (fun i₀ => NodeSplitTestOf Q M a b i₀)

/-- **The failing side of an abstract split.**  The nodes of `t` that fail `NodeSplitTestOf Q M a
b`; this is the side whose members all carry the negation of the test, one node at a time. -/
noncomputable def failingNodesOf (t : Finset ι) (Q : ℕ → ι → Prop) (M a b : ℕ) : Finset ι :=
  open scoped Classical in
  t.filter (fun i₀ => ¬ NodeSplitTestOf Q M a b i₀)

/-- The passing side is a subset of the index set it is cut from. -/
theorem passingNodesOf_subset (t : Finset ι) (Q : ℕ → ι → Prop) (M a b : ℕ) :
    passingNodesOf t Q M a b ⊆ t := by
  classical exact Finset.filter_subset _ _

/-- The failing side is a subset of the index set it is cut from. -/
theorem failingNodesOf_subset (t : Finset ι) (Q : ℕ → ι → Prop) (M a b : ℕ) :
    failingNodesOf t Q M a b ⊆ t := by
  classical exact Finset.filter_subset _ _

/-- Membership in the passing side of an abstract split. -/
theorem mem_passingNodesOf {t : Finset ι} {Q : ℕ → ι → Prop} {M a b : ℕ} {i₀ : ι} :
    i₀ ∈ passingNodesOf t Q M a b ↔ i₀ ∈ t ∧ NodeSplitTestOf Q M a b i₀ := by
  classical exact Finset.mem_filter

/-- Membership in the failing side of an abstract split. -/
theorem mem_failingNodesOf {t : Finset ι} {Q : ℕ → ι → Prop} {M a b : ℕ} {i₀ : ι} :
    i₀ ∈ failingNodesOf t Q M a b ↔ i₀ ∈ t ∧ ¬ NodeSplitTestOf Q M a b i₀ := by
  classical exact Finset.mem_filter

/-- **The majority side of an abstract split.**  A finite set is at most twice one of the two parts
of any partition of it, and the pass/fail split of a node test is such a partition.  Since the
property separating the two sides is a property of *individual nodes*, whichever side survives
carries that property universally over the retained index set. -/
theorem card_le_two_mul_card_passingNodesOf_or_failingNodesOf (t : Finset ι) (Q : ℕ → ι → Prop)
    (M a b : ℕ) :
    t.card ≤ 2 * (passingNodesOf t Q M a b).card ∨
      t.card ≤ 2 * (failingNodesOf t Q M a b).card := by
  classical
  have hsum : (passingNodesOf t Q M a b).card + (failingNodesOf t Q M a b).card = t.card :=
    Finset.card_filter_add_card_filter_not (s := t) (fun i₀ => NodeSplitTestOf Q M a b i₀)
  omega

/-- **A common cut index for the passing side of an abstract split.**  If every node of `P` passes
`NodeSplitTestOf Q M a b`, a pigeonhole over the at most `N + 1` grid indices below `b` produces a
*single* index `c`, still at margin `M` from both ends, with `Q c` holding at every node of a subset
`P' ⊆ P` satisfying `|P| ≤ (N+1) |P'|`.  The loss `N + 1` is `δ`-independent. -/
theorem exists_common_cut_of_forall_nodeSplitTestOf {P : Finset ι} {Q : ℕ → ι → Prop}
    {M N a b : ℕ} (hb : b ≤ N) (hP : P.Nonempty) (h : ∀ i₀ ∈ P, NodeSplitTestOf Q M a b i₀) :
    ∃ c : ℕ, a + M ≤ c ∧ c + M ≤ b ∧
      ∃ P' ⊆ P, P'.Nonempty ∧ P.card ≤ (N + 1) * P'.card ∧ ∀ i₀ ∈ P', Q c i₀ := by
  classical
  let f : ι → ℕ := fun i₀ =>
    if hw : ∃ c : ℕ, a + M ≤ c ∧ c + M ≤ b ∧ Q c i₀ then hw.choose else 0
  have hf : ∀ i₀ ∈ P, a + M ≤ f i₀ ∧ f i₀ + M ≤ b ∧ Q (f i₀) i₀ := by
    intro i₀ hi₀
    have hw : ∃ c : ℕ, a + M ≤ c ∧ c + M ≤ b ∧ Q c i₀ := h i₀ hi₀
    dsimp only [f]
    rw [dif_pos hw]
    exact hw.choose_spec
  have hfN : ∀ i₀ ∈ P, f i₀ ∈ Finset.range (N + 1) := fun i₀ hi₀ =>
    Finset.mem_range.mpr (by have := (hf i₀ hi₀).2.1; omega)
  have hpigeon :
      ∃ c ∈ Finset.range (N + 1), P.card ≤ (N + 1) * (P.filter (fun i => f i = c)).card := by
    by_contra hn
    push Not at hn
    have hfib : (∑ c ∈ Finset.range (N + 1), (P.filter (fun i => f i = c)).card) = P.card := by
      simpa using (Finset.card_eq_sum_card_fiberwise hfN).symm
    have hlt := Finset.sum_lt_sum_of_nonempty
      (⟨0, Finset.mem_range.mpr N.succ_pos⟩ : (Finset.range (N + 1)).Nonempty) hn
    rw [← Finset.mul_sum, hfib, Finset.sum_const, Finset.card_range, smul_eq_mul] at hlt
    exact absurd hlt (lt_irrefl _)
  obtain ⟨c, -, hcard⟩ := hpigeon
  obtain ⟨i₁, hi₁⟩ : (P.filter (fun i => f i = c)).Nonempty :=
    Finset.card_pos.mp (Nat.pos_of_mul_pos_left (lt_of_lt_of_le hP.card_pos hcard))
  obtain ⟨hi₁P, hfib⟩ := Finset.mem_filter.mp hi₁
  refine ⟨c, ?_, ?_, P.filter (fun i => f i = c), Finset.filter_subset _ _, ⟨i₁, hi₁⟩, hcard, ?_⟩
  · simpa [hfib] using (hf i₁ hi₁P).1
  · simpa [hfib] using (hf i₁ hi₁P).2.1
  · intro i₀ hi₀
    obtain ⟨hi₀P, hfib₀⟩ := Finset.mem_filter.mp hi₀
    simpa [hfib₀] using (hf i₀ hi₀P).2.2

/-! ### The Frostman instance -/

omit [Nontrivial E] in
/-- **The per-node split test.**  The node `i₀` passes the split test of the block `(a,b)` at
constant `C` and exponent `ζ` *relative to `t`* if some grid index `c` at relative depth at least
`ε` from both ends of the block carries the block bound at `i₀`, the fibre being formed inside `t`.
This is `Kakeya.MultiScaleFac.SplitTest` with the anchor fixed, not universally quantified. -/
def NodeSplitTest {δ : NNReal} (t : Finset ι) (T : ι → Tube δ E) (N : ℕ) (C : NNReal) (ε ζ : ℝ)
    (a b : ℕ) (i₀ : ι) : Prop :=
  NodeSplitTestOf (fun c => BlockFrostmanAt t T N C ζ c b) ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ a b i₀

omit [Nontrivial E] in
/-- **The passing side of a block.**  The nodes of `t` that pass the per-node split test of the
block `(a,b)` at `(C, ζ)` relative to `t`. -/
noncomputable def passingNodes {δ : NNReal} (t : Finset ι) (T : ι → Tube δ E) (N : ℕ) (C : NNReal)
    (ε ζ : ℝ) (a b : ℕ) : Finset ι :=
  passingNodesOf t (fun c => BlockFrostmanAt t T N C ζ c b) ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ a b

/-- **The failing side of a block.**  The nodes of `t` that fail the per-node split test of the
block `(a,b)` at `(C, ζ)` relative to `t`.  This is the set `F` of alternative (ii) of the refined
GWZ Lemma 7.7(A): every one of its members carries the lower bound, relative to `t` itself. -/
noncomputable def failingNodes {δ : NNReal} (t : Finset ι) (T : ι → Tube δ E) (N : ℕ) (C : NNReal)
    (ε ζ : ℝ) (a b : ℕ) : Finset ι :=
  failingNodesOf t (fun c => BlockFrostmanAt t T N C ζ c b) ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ a b

omit [Nontrivial E] in
/-- The failing side is a subset of the state it is cut from. -/
theorem failingNodes_subset {δ : NNReal} (t : Finset ι) (T : ι → Tube δ E) (N : ℕ) (C : NNReal)
    (ε ζ : ℝ) (a b : ℕ) : failingNodes t T N C ε ζ a b ⊆ t :=
  failingNodesOf_subset t _ _ a b

omit [Nontrivial E] in
/-- Membership in the failing side. -/
theorem mem_failingNodes {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    {ε ζ : ℝ} {a b : ℕ} {i₀ : ι} :
    i₀ ∈ failingNodes t T N C ε ζ a b ↔ i₀ ∈ t ∧ ¬ NodeSplitTest t T N C ε ζ a b i₀ :=
  mem_failingNodesOf

omit [Nontrivial E] in
/-- **The majority side of a split** (blueprint `lem:splitTest_majority_side`).  A finite set is at
most twice one of the two parts of any partition of it; applied to the pass/fail partition of the
per-node split test, whichever side survives carries its defining property universally over the
retained index set. -/
theorem card_le_two_mul_card_passingNodes_or_failingNodes {δ : NNReal} (t : Finset ι)
    (T : ι → Tube δ E) (N : ℕ) (C : NNReal) (ε ζ : ℝ) (a b : ℕ) :
    t.card ≤ 2 * (passingNodes t T N C ε ζ a b).card ∨
      t.card ≤ 2 * (failingNodes t T N C ε ζ a b).card :=
  card_le_two_mul_card_passingNodesOf_or_failingNodesOf t _ _ a b

omit [Nontrivial E] in
/-- **A common cut index for the passing side** (blueprint `lem:splitTest_common_cut_scale`).  If
every node of `P` passes the per-node split test of the block `(a,b)` relative to `t`, a pigeonhole
over the at most `N + 1` admissible grid indices produces a *single* index `c`, still at relative
depth `ε` from both ends, carrying the block bound at every node of a subset `P' ⊆ P` with
`|P| ≤ (N+1) |P'|`. -/
theorem exists_common_cut_of_forall_nodeSplitTest {δ : NNReal} {t P : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} {ε ζ : ℝ} {a b : ℕ} (hb : b ≤ N) (hP : P.Nonempty)
    (h : ∀ i₀ ∈ P, NodeSplitTest t T N C ε ζ a b i₀) :
    ∃ c : ℕ, a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c ∧ c + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b ∧
      ∃ P' ⊆ P, P'.Nonempty ∧ P.card ≤ (N + 1) * P'.card ∧
        BlockFrostmanOn t P' T N C ζ c b :=
  exists_common_cut_of_forall_nodeSplitTestOf hb hP h

/-! ### Absorbing the accumulated polylogarithmic loss -/

/-! ### Descent of an upper bound to a subfamily -/

omit [Nontrivial E] in
/-- **Frostman upper bounds pass to a proportional subfamily**
(blueprint `lem:frostmanConstant_le_of_subfamily`).  If `u ⊆ t` and the anchor density of `t`
exceeds that of `u` by at most `A`, then `C_F(u,K) ≤ A · C_F(t,K)`.  The density hypothesis cannot
be dropped: `C_F` is **not** monotone in the index set, a subfamily being able to have a strictly
larger Frostman constant than the family it sits in. -/
theorem frostmanConstant_le_of_subfamily {ι' : Type*} {u t : Finset ι'}
    {W : ι' → ConvexSpaceBody E} {K : ConvexSpaceBody E} {A : ENNReal} (hut : u ⊆ t)
    (htK : ∀ i ∈ t, W i ≤ K) (hA : A ≠ ⊤) (hdu : 0 < Kakeya.densityIn u W K)
    (hdt : 0 < Kakeya.densityIn t W K)
    (hband : Kakeya.densityIn t W K ≤ A * Kakeya.densityIn u W K) :
    ConvexSpaceBody.frostmanConstant u W K ≤ A * ConvexSpaceBody.frostmanConstant t W K := by
  rw [← one_mul (ConvexSpaceBody.frostmanConstant u W K)]
  exact frostmanConstant_le_of_densityIn_band (t := u) (u := t) (K := K) (K' := K) (a := 1) (b := A)
    hut (fun i hi => htK i (hut hi)) htK one_pos ENNReal.one_ne_top hA hdu hdt (by rwa [one_mul])

/-- **The global Frostman bound descends to a subfamily** (blueprint
`lem:globalFrostman_descends_to_subfamily`).  The anchor is `B_1` and the index set shrinks from `s`
to `t`, so the only input is the *global* proportion `|s| ≤ A |t|`; no per-fibre hypothesis is
needed, and the extra factor is the tube-volume comparison ratio `C_n / c_n`. -/
theorem frostmanConstant_unitBall_le_of_subfamily {δ : NNReal} {s t : Finset ι}
    {T : ι → Tube δ E} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hts : t ⊆ s) (ht : t.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    {A : NNReal} (hcard : (s.card : NNReal) ≤ A * (t.card : NNReal)) :
    ConvexSpaceBody.frostmanConstant t (fibreBodies T δ) ConvexSpaceBody.closedUnitBall
      ≤ ((A * (Tube.volume_le.C (Module.finrank ℝ E)
              / Tube.le_volume.c (Module.finrank ℝ E)) : NNReal) : ENNReal)
          * ConvexSpaceBody.frostmanConstant s (fibreBodies T δ)
              ConvexSpaceBody.closedUnitBall := by
  set n := Module.finrank ℝ E
  let W : ι → ConvexSpaceBody E := fibreBodies T δ
  let K : ConvexSpaceBody E := ConvexSpaceBody.closedUnitBall
  let Cn : NNReal := Tube.volume_le.C n
  let cn : NNReal := Tube.le_volume.c n
  let ratio : ENNReal := ((Cn / cn : NNReal) : ENNReal)
  let A' : ENNReal := ((A * (Cn / cn : NNReal) : NNReal) : ENNReal)
  let vlo : ENNReal := ((cn * δ ^ (n - 1) : NNReal) : ENNReal)
  let vhi : ENNReal := ((Cn * δ ^ (n - 1) : NNReal) : ENNReal)
  have hcn_ne : cn ≠ 0 := (Tube.le_volume.c_pos n).ne'
  have htK : ∀ i ∈ s, W i ≤ K := by
    intro i hi
    dsimp [W, K]
    rw [fibreBodies_self, ← SetLike.coe_subset_coe]
    change (T i).carrier ⊆ Metric.closedBall (0 : E) 1
    exact hball i hi
  have hvolW : ∀ i : ι, 0 < volume (W i).carrier := fun i =>
    lt_of_lt_of_le (ENNReal.coe_pos.mpr (mul_pos (Tube.le_volume.c_pos n) (pow_pos hδ (n - 1))))
      (Tube.le_volume ((T i).rescale δ))
  obtain ⟨i₀, hi₀⟩ := ht
  have hdu : 0 < Kakeya.densityIn t W K :=
    (Kakeya.densityIn_pos_iff t W K).mpr ⟨i₀, hi₀, hvolW i₀, htK i₀ (hts hi₀)⟩
  have hdt : 0 < Kakeya.densityIn s W K :=
    (Kakeya.densityIn_pos_iff s W K).mpr ⟨i₀, hts hi₀, hvolW i₀, htK i₀ (hts hi₀)⟩
  have hvhi : vhi = vlo * ratio := by
    change ((Cn * δ ^ (n - 1) : NNReal) : ENNReal)
      = ((cn * δ ^ (n - 1) : NNReal) : ENNReal) * ((Cn / cn : NNReal) : ENNReal)
    rw [← ENNReal.coe_mul]
    exact_mod_cast (by field_simp [hcn_ne] :
      (Cn * δ ^ (n - 1) : NNReal) = cn * δ ^ (n - 1) * (Cn / cn))
  have hA' : A' = (A : ENNReal) * ratio := ENNReal.coe_mul A (Cn / cn)
  have hS : (∑ i ∈ s, volume (W i).carrier) ≤ A' * ∑ i ∈ t, volume (W i).carrier := by
    calc
      (∑ i ∈ s, volume (W i).carrier) ≤ (s.card : ENNReal) * vhi := by
        rw [← nsmul_eq_mul]
        exact Finset.sum_le_card_nsmul s _ _ fun i _ => Tube.volume_le hδ1 ((T i).rescale δ)
      _ ≤ (A : ENNReal) * (t.card : ENNReal) * vhi := mul_le_mul' (by exact_mod_cast hcard) le_rfl
      _ = A' * ((t.card : ENNReal) * vlo) := by rw [hvhi, hA']; ring
      _ ≤ A' * ∑ i ∈ t, volume (W i).carrier := by
        refine mul_le_mul' le_rfl ?_
        rw [← nsmul_eq_mul]
        exact Finset.card_nsmul_le_sum t _ _ fun i _ => Tube.le_volume ((T i).rescale δ)
  have hband : Kakeya.densityIn s W K ≤ A' * Kakeya.densityIn t W K := by
    rw [densityIn_of_all_le htK, densityIn_of_all_le (fun i hi => htK i (hts hi)),
      ← mul_div_assoc]
    exact ENNReal.div_le_div_right hS _
  exact frostmanConstant_le_of_subfamily (ι' := ι) (u := t) (t := s)
    (W := W) (K := K) (A := A') hts htK (show A' ≠ ⊤ from ENNReal.coe_ne_top) hdu hdt hband

/-- **A leaf-indexed fibre Frostman bound descends to a subfamily**
(blueprint `lem:blockBound_descends_to_subfamily`, analytic half).  The anchor is fixed and the
index set shrinks from `t` to `t'`; since the two test bodies coincide, the loss is only the
tube-volume ratio `C_n/c_n` on top of the count ratio `A`.  The hypothesis compares *leaf counts*
inside the one fibre of `i₀`. -/
private theorem frostmanConstant_blockFibre_le_of_subfamily {δ : NNReal} {t t' : Finset ι}
    {T : ι → Tube δ E} {σ ρ : NNReal} (hδ : 0 < δ) (hδσ : δ ≤ σ) (hσ1 : σ ≤ 1) (hσρ : σ ≤ ρ)
    (htt' : t' ⊆ t) {A : ENNReal} (hA : A ≠ ⊤) {i₀ : ι} (hi₀ : i₀ ∈ t')
    (hcard : ((fibreIndex t T δ ρ i₀).card : ENNReal)
      ≤ A * ((fibreIndex t' T δ ρ i₀).card : ENNReal)) :
    ConvexSpaceBody.frostmanConstant (fibreIndex t' T δ ρ i₀) (fibreBodies T σ)
        ((T i₀).rescale (2 * ρ)).toConvexSpaceBody
      ≤ A * ((Tube.volume_le.C (Module.finrank ℝ E)
            / Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
          * ConvexSpaceBody.frostmanConstant (fibreIndex t T δ ρ i₀) (fibreBodies T σ)
              ((T i₀).rescale (2 * ρ)).toConvexSpaceBody := by
  set n := Module.finrank ℝ E
  set p := n - 1
  let cn : NNReal := Tube.le_volume.c n
  let Cn : NNReal := Tube.volume_le.C n
  let ratio : ENNReal := ((Cn / cn : NNReal) : ENNReal)
  let v := fibreIndex t' T δ ρ i₀
  let u := fibreIndex t T δ ρ i₀
  let W := fibreBodies T σ
  let K := ((T i₀).rescale (2 * ρ)).toConvexSpaceBody
  let V : ENNReal := volume K.carrier
  let Δv : ENNReal := Kakeya.densityIn v W K
  let Δu : ENNReal := Kakeya.densityIn u W K
  let kv : ENNReal := (v.card : ENNReal)
  let ku : ENNReal := (u.card : ENNReal)
  let vlo : ENNReal := ((cn * σ ^ p : NNReal) : ENNReal)
  let vhi : ENNReal := ((Cn * σ ^ p : NNReal) : ENNReal)
  have hσ : 0 < σ := lt_of_lt_of_le hδ hδσ
  have hρ : 0 < ρ := lt_of_lt_of_le hσ hσρ
  have hδρ : δ ≤ ρ := le_trans hδσ hσρ
  have hθ : ρ + σ ≤ 2 * ρ := by rw [two_mul]; exact add_le_add le_rfl hσρ
  have hvu : v ⊆ u := Finset.filter_subset_filter _ htt'
  have hK : ∀ r : Finset ι, ∀ i ∈ fibreIndex r T δ ρ i₀, W i ≤ K := by
    intro r i hi
    have hle : fibreBodies T δ i ≤ ((T i₀).rescale ρ).toConvexSpaceBody :=
      (Finset.mem_filter.mp hi).2
    rw [fibreBodies_self] at hle
    exact Tube.rescale_le_rescale_of_body_le (T i) ((T i₀).rescale ρ) (σ := σ) (θ := 2 * ρ)
      hδσ hθ hle
  have htKv : ∀ i ∈ v, W i ≤ K := hK t'
  have huK : ∀ i ∈ u, W i ≤ K := hK t
  have hfam_v : Kakeya.familyIn v W K = v := Finset.filter_eq_self.mpr htKv
  have hfam_u : Kakeya.familyIn u W K = u := Finset.filter_eq_self.mpr huK
  have hvolW_pos : 0 < volume (W i₀).carrier :=
    lt_of_lt_of_le (ENNReal.coe_pos.mpr (mul_pos (Tube.le_volume.c_pos n) (pow_pos hσ p)))
      (Tube.le_volume ((T i₀).rescale σ))
  have hiv : i₀ ∈ v := mem_fibreIndex_self hδρ hi₀
  have hiu : i₀ ∈ u := mem_fibreIndex_self hδρ (htt' hi₀)
  have hdtv : 0 < Kakeya.densityIn v W K :=
    (Kakeya.densityIn_pos_iff v W K).mpr ⟨i₀, hiv, hvolW_pos, htKv i₀ hiv⟩
  have hdu : 0 < Kakeya.densityIn u W K :=
    (Kakeya.densityIn_pos_iff u W K).mpr ⟨i₀, hiu, hvolW_pos, huK i₀ hiu⟩
  have hV_ne0 : V ≠ 0 :=
    (lt_of_lt_of_le (ENNReal.coe_pos.mpr (mul_pos (Tube.le_volume.c_pos n)
      (pow_pos (mul_pos (by norm_num : (0 : NNReal) < 2) hρ) p)))
      (Tube.le_volume ((T i₀).rescale (2 * ρ)))).ne'
  have hV_ne_top : V ≠ ⊤ := K.isCompact'.measure_ne_top
  have hcn_ne : cn ≠ 0 := (Tube.le_volume.c_pos n).ne'
  have hW_u : ∀ i ∈ u, volume (W i).carrier ≤ vhi := fun i _ =>
    Tube.volume_le hσ1 ((T i).rescale σ)
  have hW_v : ∀ i ∈ v, vlo ≤ volume (W i).carrier := fun i _ =>
    Tube.le_volume ((T i).rescale σ)
  have hband1 : Δu * V ≤ ku * vhi := by
    simpa only [hfam_u] using densityIn_mul_le_of_volume_band u W K (vlo := V) hW_u le_rfl
  have hband2 : kv * vlo ≤ Δv * V := by
    simpa only [hfam_v] using le_densityIn_mul_of_volume_band v W K (vhi := V) hW_v le_rfl
  have hvhi : vhi = vlo * ratio := by
    change ((Cn * σ ^ p : NNReal) : ENNReal)
      = ((cn * σ ^ p : NNReal) : ENNReal) * ((Cn / cn : NNReal) : ENNReal)
    rw [← ENNReal.coe_mul]
    exact_mod_cast (by field_simp [hcn_ne] : (Cn * σ ^ p : NNReal) = cn * σ ^ p * (Cn / cn))
  have hchain : Δu * V ≤ A * ratio * Δv * V :=
    calc
      Δu * V ≤ ku * vhi := hband1
      _ = ku * (vlo * ratio) := by rw [hvhi]
      _ ≤ A * kv * (vlo * ratio) := mul_le_mul' (hcard : ku ≤ A * kv) le_rfl
      _ = A * ratio * (kv * vlo) := by ring
      _ ≤ A * ratio * (Δv * V) := mul_le_mul' le_rfl hband2
      _ = A * ratio * Δv * V := (mul_assoc _ _ _).symm
  have hband' : 1 * Δu ≤ (A * ratio) * Δv := by
    rw [one_mul]
    refine (ENNReal.mul_le_mul_iff_right hV_ne0 hV_ne_top).mp ?_
    rw [mul_comm V Δu, mul_comm V (A * ratio * Δv)]
    exact hchain
  simpa only [one_mul] using frostmanConstant_le_of_densityIn_band
    (ι' := ι) (t := v) (u := u) (W := W) (K := K) (K' := K) (a := 1) (b := A * ratio)
    hvu htKv huK one_pos ENNReal.one_ne_top (ENNReal.mul_ne_top hA ENNReal.coe_ne_top)
    hdtv hdu hband'

/-- **A block bound descends to a proportional subfamily**
(blueprint `lem:blockBound_descends_to_subfamily`).  `Kakeya.MultiScaleFac.BlockFrostmanAt` read in
the smaller family `t'`, given the leaf-count comparison in the fibre of `i₀` at the coarse grid
anchor.  This is the `hdescend` hypothesis of `exists_maximal_cuts_abstract_state`. -/
theorem BlockFrostmanAt.of_subfamily {δ : NNReal} {t t' : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {C A : NNReal} {ζ : ℝ} {a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    (htt' : t' ⊆ t) {i₀ : ι} (hi₀ : i₀ ∈ t')
    (hcard : ((fibreIndex t T δ (gridScale δ N a) i₀).card : ENNReal)
      ≤ (A : ENNReal) * ((fibreIndex t' T δ (gridScale δ N a) i₀).card : ENNReal))
    (h : BlockFrostmanAt t T N C ζ a b i₀) :
    BlockFrostmanAt t' T N
      (A * (Tube.volume_le.C (Module.finrank ℝ E)
        / Tube.le_volume.c (Module.finrank ℝ E)) * C) ζ a b i₀ := by
  classical
  have hδσ : δ ≤ gridScale δ N b := by
    rcases Nat.eq_zero_or_pos N with rfl | hNpos
    · simpa [Nat.le_zero.mp hbN] using hδ1
    · exact (gridScale_self δ hNpos).symm.trans_le (gridScale_antitone hδ hδ1 N hbN)
  have h1 := frostmanConstant_blockFibre_le_of_subfamily (t := t) (t' := t') hδ hδσ
    (gridScale_le_one hδ1 N b) (gridScale_antitone hδ hδ1 N hab) htt'
    (A := (A : ENNReal)) ENNReal.coe_ne_top hi₀ hcard
  unfold BlockFrostmanAt
  refine (h1.trans (mul_le_mul' le_rfl h)).trans ?_
  simp [ENNReal.coe_mul, mul_assoc]

end MultiScaleFac

end Kakeya
