/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.NonSlabAngle
public import Kakeya.Uniform

/-!
# The `ρ₂*`-fibres of the non-slab case of Main Lemma 2

The inner factor of the non-slab splitting is the multiplicity of a single fibre
`𝕋[T_{ρ₂*}]` of the parent family `𝕋_{ρ₂*}` of blueprint `uniformSetOfTubes`. This file
collects everything that is needed *about the fibres themselves*, before any Katz–Tao input
is consumed:

* the two purely combinatorial inputs, blueprint `lem:coverCardEqDisjoint` (a finite cover of
  exact total size is a partition) and blueprint `lem:mediantSelect` (mediant selection),
  neither of which is in Mathlib;
* blueprint `lem:ml2fullnessOfPartition`, the fullness of a family split over a partition;
* blueprint `lem:ml2tubeScaleCompare`, the comparison `|𝕋_ρ| ≤ (ρ'/ρ)² |𝕋_{ρ'}|` of the
  parent families at two angular scales — an *assumption*, see the note on its statement;
* blueprint `lem:ml2nonslabFibreCount`, the resulting bound
  `|𝕋[T_{ρ₂*}]| ≤ K · Ccnt · ρ₂^{2+ζ}|𝕋|` at the hierarchy constant `K` and the count constant
  `Ccnt` (both explicit parameters), and the fibre count `|𝕋_{ρ₂*}| · |𝕋[T_{ρ₂*}]| ≤ Cu² |𝕋|` as a theorem of
  `Tube.UniformTubeSet`;
* blueprint `lem:ml2nonslabFibrePartition` and `lem:ml2nonslabFullFibre`, which use the
  hierarchy assignment classes to partition `𝕋` and select a fibre at least as full as `𝕋`.

The last of these is what discharges the fullness hypothesis of
`Kakeya.VeryNotSticky.nonslabKKT`: fullness is not inherited by an arbitrary subfamily, but
the fibres partition `𝕋`, so at least one of them is at least as full as `𝕋`.
-/

@[expose] public section

namespace Kakeya

section Combinatorics

/-- **A finite cover of exact total size is a partition** (blueprint
`lem:coverCardEqDisjoint`).

If the finite sets `f j`, `j ∈ J`, are contained in `A`, cover `A`, and satisfy
`∑_{j ∈ J} |f j| = |A|`, then they are pairwise disjoint.

Double counting gives `∑_j |f j| = ∑_{x ∈ A} #{j ∈ J : x ∈ f j}`, the covering hypothesis
makes each summand at least `1`, and the cardinality hypothesis makes the total equal to
`|A| = ∑_{x ∈ A} 1`; hence each summand is exactly `1`.

This is the converse direction of `Finset.card_biUnion`, which passes from pairwise
disjointness to the cardinality identity. The converse is not in Mathlib, so it is recorded
here. -/
theorem pairwiseDisjoint_of_sum_card_eq {α κ : Type*} [DecidableEq α]
    {A : Finset α} {J : Finset κ} {f : κ → Finset α}
    (hsub : ∀ j ∈ J, f j ⊆ A) (hcov : A ⊆ J.biUnion f)
    (hcard : ∑ j ∈ J, (f j).card = A.card) :
    (J : Set κ).PairwiseDisjoint f := by
  classical
  have hcount_j : ∀ j ∈ J, (f j).card = (∑ x ∈ A, if x ∈ f j then 1 else 0) := by
    intro j hj
    rw [Finset.card_eq_sum_ones]
    calc
      (∑ x ∈ f j, 1) = (∑ x ∈ f j, if x ∈ f j then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [hx]
      _ = (∑ x ∈ A, if x ∈ f j then 1 else 0) := by
          rw [Finset.sum_subset (hsub j hj)]
          intro x hA hnot
          simp [hnot]
  have hdouble : (∑ j ∈ J, (f j).card) = (∑ x ∈ A, (J.filter fun j => x ∈ f j).card) := by
    calc
      (∑ j ∈ J, (f j).card) = ∑ j ∈ J, (∑ x ∈ A, if x ∈ f j then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hcount_j j hj
      _ = ∑ x ∈ A, (∑ j ∈ J, if x ∈ f j then 1 else 0) := by
          rw [Finset.sum_comm]
      _ = ∑ x ∈ A, (J.filter fun j => x ∈ f j).card := by
          apply Finset.sum_congr rfl
          intro x hxA
          simp [Finset.sum_boole]
  let m : α → ℕ := fun x => (J.filter fun j => x ∈ f j).card
  have hm_sum : (∑ x ∈ A, m x) = A.card := by
    rw [← hdouble]
    exact hcard
  have hm_ge : ∀ x ∈ A, 1 ≤ m x := by
    intro x hxA
    have hxi : x ∈ J.biUnion f := hcov hxA
    rcases Finset.mem_biUnion.mp hxi with ⟨j, hj, hxj⟩
    have hf : j ∈ J.filter (fun a => x ∈ f a) := by
      simp [hj, hxj]
    have hpos : 0 < (J.filter fun a => x ∈ f a).card :=
      Finset.card_pos.mpr (by exact ⟨j, hf⟩)
    dsimp [m]
    omega
  have hm_eq : ∀ x ∈ A, m x = 1 := by
    have hiff := Finset.sum_eq_sum_iff_of_le (s := A) (f := fun _ : α => 1) (g := m)
      (fun x hx => hm_ge x hx)
    have hsums : (∑ x ∈ A, 1) = (∑ x ∈ A, m x) := by
      calc
        (∑ x ∈ A, 1) = A.card := (Finset.card_eq_sum_ones A).symm
        _ = (∑ x ∈ A, m x) := hm_sum.symm
    intro x hxA
    exact (hiff.mp hsums x hxA).symm
  change ∀ ⦃j : κ⦄, j ∈ J → ∀ ⦃k : κ⦄, k ∈ J → j ≠ k → Disjoint (f j) (f k)
  intro j kj k kk hjk
  rw [Finset.disjoint_left]
  intro x hxj hxk
  have hxA : x ∈ A := hsub j kj hxj
  have h_one_lt : 1 < (J.filter fun j => x ∈ f j).card := by
    rw [Finset.one_lt_card_iff]
    exact ⟨j, k, by simp [kj, hxj], by simp [kk, hxk], hjk⟩
  have h1 : m x = 1 := hm_eq x hxA
  dsimp [m] at h1
  omega

/-- **Mediant selection** (blueprint `lem:mediantSelect`).

For nonnegative `p j` and finite positive `q j` over a finite nonempty index set, some index
beats the mediant: `(∑ p) / (∑ q) ≤ p j / q j` for some `j`.

Writing `L` for the left-hand side one has `∑_j L * q j = ∑_j p j`, so
`Finset.exists_le_of_sum_le` supplies a `j` with `L * q j ≤ p j`, and dividing by `q j` gives
the claim. Mathlib has no mediant selection lemma, so it is recorded here.

The statement is in `ℝ≥0∞` rather than in `ℝ`, because that is the type of the numerator and
denominator of `ShadedBody.fullness'`, which is where it is consumed; the hypotheses
`q j ≠ 0` and `q j ≠ ⊤` are the blueprint's `0 < q_j < ∞`. -/
theorem exists_sum_div_sum_le {κ : Type*} {J : Finset κ} (hJ : J.Nonempty)
    (p q : κ → ENNReal) (hq0 : ∀ j ∈ J, q j ≠ 0) (hqtop : ∀ j ∈ J, q j ≠ ⊤) :
    ∃ j ∈ J, (∑ k ∈ J, p k) / (∑ k ∈ J, q k) ≤ p j / q j := by
  classical
  let Sp : ENNReal := ∑ k ∈ J, p k
  let Sq : ENNReal := ∑ k ∈ J, q k
  let L : ENNReal := Sp / Sq
  have hSq0 : Sq ≠ 0 := by
    intro hSq0
    rcases hJ with ⟨j, hj⟩
    have hqj0 : q j = 0 := by
      have hle : q j ≤ Sq := by
        dsimp [Sq]
        exact Finset.single_le_sum (fun x _ => zero_le) hj
      rw [hSq0] at hle
      exact le_antisymm hle zero_le
    exact hq0 j hj hqj0
  have hSqt : Sq ≠ ⊤ := by
    dsimp [Sq]
    exact (ENNReal.sum_ne_top (s := J) (f := q)).2 (fun k hk => hqtop k hk)
  have hL : L * Sq = Sp := by
    dsimp [L]
    rw [ENNReal.div_mul_cancel hSq0 hSqt]
  have hsum_eq : (∑ k ∈ J, L * q k) = Sp := by
    calc
      (∑ k ∈ J, L * q k) = L * (∑ k ∈ J, q k) := by rw [Finset.mul_sum]
      _ = L * Sq := rfl
      _ = Sp := hL
  rcases ENNReal.exists_le_of_sum_le hJ (f := fun k => L * q k) (g := p) (by
      exact le_of_eq (by rw [hsum_eq])) with ⟨j, hj, hLqle⟩
  refine ⟨j, hj, ?_⟩
  rw [ENNReal.le_div_iff_mul_le (Or.inl (hq0 j hj)) (Or.inl (hqtop j hj))]
  exact hLqle

/-- **Markov on densities**, division-free form.

If `d` is any *lower* bound for the aggregate density in the sense that `d · ∑ v ≤ ∑ m`, then the
blocks whose own density beats `κ d`, that is `{j ∈ J | κ · d · v j ≤ m j}`, carry all but a `κ`
fraction of the mass `∑ m`.

This is the form that `Kakeya.le_sum_filter_dense` --- the blueprint statement
`lem:densityMarkov`, with `d = M / V` --- is deduced from, and the form that is easiest to
consume downstream, since no division occurs in it. -/
theorem le_sum_filter_of_mul_sum_le {ι : Type*} {J : Finset ι} {m v : ι → ENNReal}
    {d κ : ENNReal} (hm : ∑ j ∈ J, m j ≠ ⊤) (_hκ : κ ≤ 1)
    (hd : d * ∑ j ∈ J, v j ≤ ∑ j ∈ J, m j) :
    (1 - κ) * ∑ j ∈ J, m j ≤ ∑ j ∈ {j ∈ J | κ * d * v j ≤ m j}, m j := by
  let M : ENNReal := ∑ j ∈ J, m j
  let S : Finset ι := {j ∈ J | κ * d * v j ≤ m j}
  let T : Finset ι := J.filter (fun j => ¬ κ * d * v j ≤ m j)
  have hmM : M ≠ ⊤ := by simpa [M] using hm
  have hTJ : T ⊆ J := by
    simp [T]
  have hsplit : M = (∑ j ∈ S, m j) + (∑ j ∈ T, m j) := by
    unfold M S T
    rw [← Finset.sum_filter_add_sum_filter_not J (fun j => κ * d * v j ≤ m j) (fun j => m j)]
  have hTm : ∀ j ∈ T, m j ≤ κ * d * v j := by
    intro j hj
    exact le_of_lt (not_le.mp (Finset.mem_filter.mp hj).2)
  have hsumT : (∑ j ∈ T, m j) ≤ κ * M := by
    calc
      (∑ j ∈ T, m j) ≤ ∑ j ∈ T, κ * d * v j := Finset.sum_le_sum hTm
      _ = κ * d * (∑ j ∈ T, v j) := by
        rw [← Finset.mul_sum]
      _ ≤ κ * d * (∑ j ∈ J, v j) :=
        mul_le_mul_right (Finset.sum_le_sum_of_subset hTJ) (κ * d)
      _ ≤ κ * M := by
        calc
          κ * d * (∑ j ∈ J, v j) = κ * (d * (∑ j ∈ J, v j)) := by rw [mul_assoc]
          _ ≤ κ * M := mul_le_mul_right hd κ
  have hle : M ≤ (∑ j ∈ S, m j) + κ * M := by
    calc
      M = (∑ j ∈ S, m j) + (∑ j ∈ T, m j) := hsplit
      _ ≤ (∑ j ∈ S, m j) + κ * M := by
        simpa [add_comm, add_left_comm, add_assoc] using
          (add_le_add_left hsumT (∑ j ∈ S, m j))
  have hsub : (1 - κ) * M = M - κ * M := by
    calc
      (1 - κ) * M = 1 * M - κ * M := ENNReal.sub_mul (fun _ _ => hmM)
      _ = M - κ * M := by rw [one_mul]
  rw [hsub, tsub_le_iff_right]
  exact hle

/-- **Markov on densities: the dense blocks carry almost all the mass** (blueprint
`lem:densityMarkov`).

For finite families `(m j)` and `(v j)` with `M = ∑ m`, `V = ∑ v > 0` and `0 < κ ≤ 1`, the dense
blocks `J_dens = {j ∈ J | m j ≥ κ (M / V) v j}` satisfy `∑_{j ∈ J_dens} m j ≥ (1 - κ) M`.

The statement is in `ℝ≥0∞` rather than in `ℝ`, as `Kakeya.exists_sum_div_sum_le` is and for the
same reason: that is the type of the numerator and denominator of `ShadedBody.fullness'`, which
is where it is consumed. The hypotheses `V ≠ 0` and `V ≠ ⊤` are the blueprint's `0 < V < ∞`, and
`M ≠ ⊤` is needed because the truncated subtraction `M - κ M` of the proof is otherwise
uninformative. The blueprint's `0 < κ` is not needed: at `κ = 0` the selected set is all of `J`
and the conclusion is an identity. -/
theorem le_sum_filter_dense {ι : Type*} {J : Finset ι} {m v : ι → ENNReal} {κ : ENNReal}
    (hm : ∑ j ∈ J, m j ≠ ⊤) (hv : ∑ j ∈ J, v j ≠ 0) (hvtop : ∑ j ∈ J, v j ≠ ⊤) (hκ : κ ≤ 1) :
    (1 - κ) * ∑ j ∈ J, m j ≤
      ∑ j ∈ {j ∈ J | κ * ((∑ k ∈ J, m k) / (∑ k ∈ J, v k)) * v j ≤ m j}, m j := by
  have hd : ((∑ k ∈ J, m k) / (∑ k ∈ J, v k)) * (∑ j ∈ J, v j) ≤ ∑ j ∈ J, m j := by
    rw [ENNReal.div_mul_cancel (a := (∑ j ∈ J, v j)) (b := (∑ j ∈ J, m j)) hv hvtop]
  exact le_sum_filter_of_mul_sum_le (d := (∑ k ∈ J, m k) / (∑ k ∈ J, v k)) hm hκ hd

end Combinatorics

end Kakeya

namespace ShadedBody

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Fullness of a partitioned family** (blueprint `lem:ml2fullnessOfPartition`).

If the subfamilies `f j`, `j ∈ J`, are pairwise disjoint, then both the numerator and the
denominator of the fullness of their union split over the partition; this is
`Finset.sum_biUnion` applied to `V ↦ |Y(V)|` and to `V ↦ |V|`. -/
theorem fullness'_biUnion {ι κ : Type*} [DecidableEq ι] {J : Finset κ} {f : κ → Finset ι}
    (V : ι → ShadedBody E) (hdisj : (J : Set κ).PairwiseDisjoint f) :
    fullness' (J.biUnion f) V =
      (∑ j ∈ J, ∑ i ∈ f j, volume (V i).shade) /
        (∑ j ∈ J, ∑ i ∈ f j, volume (V i).carrier) := by
  classical
  unfold fullness'
  rw [Finset.sum_biUnion hdisj, Finset.sum_biUnion hdisj]

end ShadedBody

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set ShadedBody

open scoped Classical in
/-- The fibre `𝕋[T_ρ]` of a node in the uniform tube hierarchy: the tubes assigned to the node
indexed by `j` at grid level `k`. -/
noncomputable def tubeFibre (cfg : VeryNotSticky) {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C)
    (k : ℕ) (j : cfg.ι) : Finset cfg.ι :=
  Tube.coverClass cfg.s (𝒰.cover.assign k) j

lemma tubeFibre_subset (cfg : VeryNotSticky) {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C)
    (k : ℕ) (j : cfg.ι) : cfg.tubeFibre 𝒰 k j ⊆ cfg.s := by
  simp [tubeFibre, Tube.coverClass]

open scoped Classical in
/-- The nodes at level `k` that have a nonempty assignment class. -/
noncomputable def activeTubeNodes (cfg : VeryNotSticky) {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C)
    (k : ℕ) : Finset cfg.ι :=
  (𝒰.cover.indexSet k).filter fun j ↦ (cfg.tubeFibre 𝒰 k j).Nonempty

open scoped Classical in
/-- **Comparing the parent families at two angular scales** (blueprint
`lem:ml2tubeScaleCompare`).

For `δ ≤ ρ ≤ ρ' ≤ 1` the parent families of blueprint `uniformSetOfTubes` at the two scales
satisfy `|𝕋_ρ| ≤ (ρ'/ρ)² |𝕋_{ρ'}|`, because each `ρ'`-node contains at most `(ρ'/ρ)²` of the
`ρ`-nodes. This Lean statement isolates that sentence: `par` is the ancestry map sending a
level-`k` node to the level-`k'` node above it, and `hbranch` is the per-parent packing count.
Given those two inputs the comparison is the fibrewise cardinality identity
`Finset.card_eq_sum_card_fiberwise` followed by a termwise bound.

**Why the two inputs are hypotheses and not consequences of `𝒰`.** The previous form of this
statement took only `δ ≤ ρ ≤ ρ' ≤ 1` over a `Tube.UniformTubeSet`, and *in that form it
is false*. That bundle records no relation between `(cover.indexSet k).card` and
`(cover.indexSet k').card`: its only cross-level fields, `cover.nested` and `cover.tube_nested`,
run the other way, and `card_class_le`/`le_card_class` give only
`#IndexSet k ≤ C² (branchingN k' / branchingN k) #IndexSet k'`, with nothing tying that ratio to
`(ρ'/ρ)²`. For a counterexample take `N = 1`, `k = 1`, `k' = 0`, so the two scales are `δ` and
`1`; let level `1` be the discrete hierarchy (`IndexSet 1 = cfg.s`, `assign 1 = id`, node tubes
the leaves rescaled to radius `δ`) and level `0` the single node given by the unit tube
containing `B₁`. All fields hold, with exact branching (so even at `C = 1`, provided the leaf
axes are distinct), yet the conclusion asserts `#cfg.s ≤ δ⁻²`, which fails in the intended
regime `#cfg.s ≈ δ^(-2-η)` that `cfg.maxDensity_le` permits. The scale hypotheses did not even
force `k' ≤ k`: at `δ = 1` all grid scales coincide and the old statement asserted equality of
every pair of index-set cardinalities.

Amending `Tube.UniformTubeSet` instead was rejected: the packing input is directional
separation of the node directions inside a `ρ'`-cap, and the bundle's `boundedOverlap` field
deliberately *replaces* pairwise essential distinctness, which its own docstring records as
unsatisfiable while preserving cardinality. Carrying `par` and `hbranch` as explicit arguments
keeps the geometric debt visible at the one place it is owed, exactly as
`Kakeya.VeryNotSticky.nonslabKKT` keeps the resulting count as its free hypothesis `hcount`.

Nothing currently consumes this declaration:
`Kakeya.VeryNotSticky.SplitInputs.fibreScaleCount` carries the count as a hypothesis instead,
at the carried constant `Ccnt ≤ δ^{-18η}` of `Kakeya.VeryNotSticky.SplitInputs.countConstant` — which is precisely the price this comparison would have had to
pay, and the reason the δ-free form was unreachable. -/
theorem tubeScaleCompare (cfg : VeryNotSticky) {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C)
    {k k' : ℕ} (par : cfg.ι → cfg.ι)
    (hpar : ∀ j ∈ 𝒰.cover.indexSet k, par j ∈ 𝒰.cover.indexSet k')
    (hbranch : ∀ j' ∈ 𝒰.cover.indexSet k',
      (((𝒰.cover.indexSet k).filter fun j ↦ par j = j').card : ℝ) ≤
        ((Tube.gridScale cfg.δ N k' : ℝ) /
          (Tube.gridScale cfg.δ N k : ℝ)) ^ 2) :
    ((𝒰.cover.indexSet k).card : ℝ) ≤
      ((Tube.gridScale cfg.δ N k' : ℝ) /
        (Tube.gridScale cfg.δ N k : ℝ)) ^ 2 *
          ((𝒰.cover.indexSet k').card : ℝ) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (s := 𝒰.cover.indexSet k)
    (t := 𝒰.cover.indexSet k') (f := par) hpar]
  rw [Nat.cast_sum]
  calc
    (∑ j' ∈ 𝒰.cover.indexSet k',
        (((𝒰.cover.indexSet k).filter fun j ↦ par j = j').card : ℝ))
        ≤ ∑ _ ∈ 𝒰.cover.indexSet k',
            ((Tube.gridScale cfg.δ N k' : ℝ) /
              (Tube.gridScale cfg.δ N k : ℝ)) ^ 2 := by
          exact Finset.sum_le_sum (fun j' hj' => hbranch j' hj')
    _ = ((Tube.gridScale cfg.δ N k' : ℝ) /
              (Tube.gridScale cfg.δ N k : ℝ)) ^ 2 *
          ((𝒰.cover.indexSet k').card : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **Counting the tubes in a `ρ₂*`-fibre** (blueprint `lem:ml2nonslabFibreCount`).

Here `N = |𝕋_{ρ₂*}|` and `sub = 𝕋[T_{ρ₂*}]`. The hypothesis `hfib` is item (iii) of blueprint
`uniformSetOfTubes` — GWZ Def 2.1(iii), "`|𝕋[T_ρ]|` is constant up to a factor `∼ 1`"
(`gwz.txt` l.183) — in the inequality shape `N |𝕋[T_{ρ₂*}]| ≤ K |𝕋|` with the hierarchy
constant `K`, which is all this
bound needs; the hypothesis `hcount` is the lower bound
`ρ₂^{-2-ζ} ≤ Ccnt · N` at a **general** count constant `Ccnt` (fixing `Ccnt = (2 C_{lem:ml2bodyAngle}(C₀))²`, which no producer of
`Kakeya.VeryNotSticky.SplitInputs.fibreScaleCount` can supply —  — so the constant
is now a parameter and the numeral lives at the call site only). In the blueprint that lower
bound comes from `rho2_range` at the scale `ρ₂` and from
`Kakeya.VeryNotSticky.tubeScaleCompare` at `(ρ₂, ρ₂*)`, whose ratio is exactly
`2 C_{lem:ml2bodyAngle}(C₀)`; the existing producer
`Kakeya.VeryNotSticky.exists_fibreScaleCount_of_rhoParentData` reaches it instead at
`Ccnt ≤ δ^{-18 η}`.

The *undilated* `ρ₂` appears on the right because `rho2_range` is not available at `ρ₂*`,
which may exceed `δ^{exscal}`; the ratio `ρ₂*/ρ₂` is fixed once `C₀` is, so this costs only
the displayed constant. This is the second display of blueprint `lem:ml2nonslabKKT`, stated on
its own rather than as a conjunct of `Kakeya.VeryNotSticky.nonslabKKT`, so that the consumers
of the counting bound do not have to carry the Katz–Tao hypothesis. -/
theorem nonslabFibreCount (cfg : VeryNotSticky)
    (hrho2 : 0 < cfg.rho2) {sub : Finset cfg.ι} (N : ℕ) {K Ccnt : NNReal}
    (hfib : (N : ℝ) * (sub.card : ℝ) ≤ (K : ℝ) * (cfg.s.card : ℝ))
    (hcount : (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) * (N : ℝ)) :
    (sub.card : ℝ) ≤ (K : ℝ) * (Ccnt : ℝ) *
      (cfg.rho2 : ℝ) ^ (2 + cfg.ζ) * (cfg.s.card : ℝ) := by
  let ρ : ℝ := (cfg.rho2 : ℝ)
  let C : ℝ := (Ccnt : ℝ)
  have hCnonneg : (0 : ℝ) ≤ C := Ccnt.coe_nonneg
  have hρgt : 0 < ρ := by
    dsimp [ρ]
    exact_mod_cast hrho2
  have hρnonneg : 0 ≤ ρ := le_of_lt hρgt
  have h1 : ρ ^ (2 + cfg.ζ) * ρ ^ (-2 - cfg.ζ) = 1 := by
    rw [← Real.rpow_add hρgt]
    have hexp : (2 + cfg.ζ) + (-2 - cfg.ζ) = 0 := by ring
    rw [hexp, Real.rpow_zero]
  have hstep1 : (1 : ℝ) ≤ C * ρ ^ (2 + cfg.ζ) * (N : ℝ) := by
    rw [← h1]
    calc
      ρ ^ (2 + cfg.ζ) * ρ ^ (-2 - cfg.ζ) ≤ ρ ^ (2 + cfg.ζ) * (C * (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (by simpa [ρ, C] using hcount)
          (Real.rpow_nonneg hρnonneg (2 + cfg.ζ))
      _ = C * ρ ^ (2 + cfg.ζ) * (N : ℝ) := by ring
  calc
    (sub.card : ℝ) = 1 * (sub.card : ℝ) := by rw [one_mul]
    _ ≤ (C * ρ ^ (2 + cfg.ζ) * (N : ℝ)) * (sub.card : ℝ) := by
      exact mul_le_mul_of_nonneg_right hstep1 (Nat.cast_nonneg sub.card)
    _ = C * ρ ^ (2 + cfg.ζ) * ((N : ℝ) * (sub.card : ℝ)) := by ring
    _ ≤ C * ρ ^ (2 + cfg.ζ) * ((K : ℝ) * (cfg.s.card : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hfib
        (mul_nonneg hCnonneg (Real.rpow_nonneg hρnonneg (2 + cfg.ζ)))
    _ = (K : ℝ) * C * ρ ^ (2 + cfg.ζ) * (cfg.s.card : ℝ) := by ring

/-- **The fibre count in powered form** (blueprint `lem:ml2nonslabFibreCountPow`).

Raising the count `|𝕋[T_{ρ₂*}]| ≤ K Ccnt ρ₂^{2+ζ}|𝕋|` of
`Kakeya.VeryNotSticky.nonslabFibreCount` to the `β`-th power costs `(K Ccnt)^β`, and
`(K Ccnt)^β ≤ (δ^{-Mη})^β = δ^{-Mηβ} ≤ δ^{-Mη}` by `hCδ` together with `β ≤ 1`, `0 ≤ M` and
`δ ≤ 1`; this is the only use of `β ≤ 1` in the non-slab chain. `K` is the constant of the
fibre count, `Cu²` for the hierarchy constant `Cu` of `Tube.UniformTubeSet`, and `Ccnt` is the constant of the count clause, a parameter.

`M` is likewise a parameter, not a numeral: the numeral is fixed at each call site, `M = 19` at
`Kakeya.VeryNotSticky.nonslabSplitBound` (`19 = 1` for the hierarchy constant `Cu²` inside
`Kakeya.VeryNotSticky.SplitInputs.fibreConstant` plus `18` for
`Kakeya.VeryNotSticky.SplitInputs.countConstant`) and `M = 1` at `Kakeya.KKTResidual.nonslabKKTPow_of_fibreKTData`.

That absorption is the hypothesis `hCδ`, blueprint `fibreConstantThreshold`. It is a genuine
extra assumption, not a consequence of the others — `δ = 1` falsifies the statement without
it — and it is a fixed-scale threshold of the same kind as the four fields of
`Kakeya.VeryNotSticky.CaseScale` without being one of them: it does not follow from
`rho2Star_le_one` together with `2η < exscal`, which bounds
`2 C_{lem:ml2bodyAngle}(C₀) δ^{exscal}` and says nothing about `C_{lem:ml2bodyAngle}(C₀)²`
alone. No lower bound on `K Ccnt` is assumed: a separate binder `1 ≤ K Ccnt` is unnecessary because `Kakeya.VeryNotSticky.SplitInputs` carries only the upper bound
`countConstant`, so the powered step is routed through `hCδ` and `0 ≤ M` instead — a strictly
weaker side condition, discharged by `norm_num` at both call sites.

The hypothesis is stated over `ℝ`, as `nonslabFibreCount` produces it, and the conclusion
over `ℝ≥0∞`, as `nonslabKKTPow` consumes it. -/
theorem nonslabFibreCountPow (cfg : VeryNotSticky) (hβ1 : cfg.β ≤ 1)
    {K Ccnt : NNReal} {M : ℝ} (hM : 0 ≤ M)
    (hCδ : (K : ENNReal) * (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(M * cfg.η)))
    {sub : Finset cfg.ι}
    (hcard : (sub.card : ℝ) ≤ (K : ℝ) * (Ccnt : ℝ) *
      (cfg.rho2 : ℝ) ^ (2 + cfg.ζ) * (cfg.s.card : ℝ)) :
    (sub.card : ENNReal) ^ cfg.β ≤ (cfg.δ : ENNReal) ^ (-(M * cfg.η)) *
      ((cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)) ^ cfg.β := by
  let P : ENNReal := (cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal)
  let KC : ENNReal := (K : ENNReal) * (Ccnt : ENNReal)
  have hβ0 : 0 ≤ cfg.β := cfg.hβ.le
  have hρζ : 0 ≤ 2 + cfg.ζ := by linarith [cfg.hζ]
  have hδ1e : (cfg.δ : ENNReal) ≤ 1 := by exact_mod_cast cfg.hδ1
  -- transport `hcard` to `ENNReal`
  have hcardN : (sub.card : NNReal) ≤
      K * Ccnt * (cfg.rho2 ^ (2 + cfg.ζ) : NNReal) * (cfg.s.card : NNReal) := by
    exact_mod_cast hcard
  have hcardE : (sub.card : ENNReal) ≤ (K : ENNReal) * (Ccnt : ENNReal) *
      (cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) * (cfg.s.card : ENNReal) := by
    have h := ENNReal.coe_le_coe.mpr hcardN
    simpa [ENNReal.coe_rpow_of_nonneg cfg.rho2 hρζ] using h
  -- `(K Ccnt)^β ≤ (δ^{-Mη})^β = δ^{-Mηβ} ≤ δ^{-Mη}`
  have hKCδ : KC ^ cfg.β ≤ (cfg.δ : ENNReal) ^ (-(M * cfg.η)) := by
    have hstep : KC ^ cfg.β ≤ ((cfg.δ : ENNReal) ^ (-(M * cfg.η))) ^ cfg.β :=
      ENNReal.rpow_le_rpow (by simpa [KC] using hCδ) hβ0
    have hmulr : ((cfg.δ : ENNReal) ^ (-(M * cfg.η))) ^ cfg.β =
        (cfg.δ : ENNReal) ^ (-(M * cfg.η) * cfg.β) := by
      rw [← ENNReal.rpow_mul]
    have hmono : (cfg.δ : ENNReal) ^ (-(M * cfg.η) * cfg.β) ≤
        (cfg.δ : ENNReal) ^ (-(M * cfg.η)) := by
      apply ENNReal.rpow_le_rpow_of_exponent_ge hδ1e
      nlinarith [mul_nonneg (mul_nonneg hM cfg.hη.le) (sub_nonneg.mpr hβ1)]
    exact hstep.trans (by rw [hmulr]; exact hmono)
  have hbound : KC * P = (K : ENNReal) * (Ccnt : ENNReal) * (cfg.rho2 : ENNReal) ^ (2 + cfg.ζ)
      * (cfg.s.card : ENNReal) := by
    simp [KC, P, mul_assoc]
  calc
    (sub.card : ENNReal) ^ cfg.β ≤
        ((K : ENNReal) * (Ccnt : ENNReal) * (cfg.rho2 : ENNReal) ^ (2 + cfg.ζ) *
            (cfg.s.card : ENNReal)) ^ cfg.β :=
        ENNReal.rpow_le_rpow hcardE hβ0
    _ = (KC * P) ^ cfg.β := by
        rw [← hbound]
    _ = KC ^ cfg.β * P ^ cfg.β := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hβ0]
    _ ≤ (cfg.δ : ENNReal) ^ (-(M * cfg.η)) * P ^ cfg.β := by
        have hm : P ^ cfg.β * KC ^ cfg.β ≤
            P ^ cfg.β * (cfg.δ : ENNReal) ^ (-(M * cfg.η)) :=
          mul_le_mul_right hKCδ (P ^ cfg.β)
        convert hm using 1 <;> ac_rfl

open scoped Classical in
/-- **The `ρ₂*`-fibres partition `𝕋`** (blueprint `lem:ml2nonslabFibrePartition`).

The active nodes at the `ρ₂*` grid level are nonempty, their assignment classes are pairwise
disjoint, and their union is `𝕋`. This is now structural: `GridCoverSystem.assign_mem` assigns
each leaf to a node, and `coverClass` is a fibre of the assignment function. No exact fibre-count
hypothesis is needed, and the angular-scale pin `ρ₂* ≤ δ^{k/N} ≤ δ^{-η} ρ₂*` — two binders,
two-sided, in lockstep with the fields
`Kakeya.VeryNotSticky.SplitInputs.gridScale_ge` and `gridScale_le` — is received for the
statement's shape only and is not used. -/
theorem nonslabFibrePartition (cfg : VeryNotSticky) {N : ℕ} {C₀ C : NNReal}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C)
    (k : ℕ) (hk : k ≤ N)
    (_hscale_ge : cfg.rho2Star C₀ ≤ Tube.gridScale cfg.δ N k)
    (_hscale_le : Tube.gridScale cfg.δ N k ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star C₀)
    (hs : cfg.s.Nonempty) :
    (cfg.activeTubeNodes 𝒰 k).Nonempty ∧
      (cfg.activeTubeNodes 𝒰 k : Set cfg.ι).PairwiseDisjoint (cfg.tubeFibre 𝒰 k) ∧
        (cfg.activeTubeNodes 𝒰 k).biUnion (cfg.tubeFibre 𝒰 k) = cfg.s := by
  classical
  let J := cfg.activeTubeNodes 𝒰 k
  change J.Nonempty ∧ (J : Set cfg.ι).PairwiseDisjoint (cfg.tubeFibre 𝒰 k) ∧
    J.biUnion (cfg.tubeFibre 𝒰 k) = cfg.s
  have hcov : cfg.s ⊆ J.biUnion (cfg.tubeFibre 𝒰 k) := by
    intro i hi
    have hj : 𝒰.cover.assign k i ∈ 𝒰.cover.indexSet k := 𝒰.cover.assign_mem k hk i hi
    have hinf : i ∈ cfg.tubeFibre 𝒰 k (𝒰.cover.assign k i) := by
      simp [tubeFibre, Tube.coverClass, hi]
    have hactive : 𝒰.cover.assign k i ∈ J := by
      simp only [J, activeTubeNodes, Finset.mem_filter]
      exact ⟨hj, ⟨i, hinf⟩⟩
    exact Finset.mem_biUnion.mpr ⟨𝒰.cover.assign k i, hactive, hinf⟩
  have hJ : J.Nonempty := by
    rcases hs with ⟨i, hi⟩
    refine ⟨𝒰.cover.assign k i, ?_⟩
    simp only [J, activeTubeNodes, Finset.mem_filter]
    exact ⟨𝒰.cover.assign_mem k hk i hi, ⟨i, by
      simp [tubeFibre, Tube.coverClass, hi]⟩⟩
  refine ⟨hJ, ?_, ?_⟩
  · change ∀ ⦃j⦄, j ∈ J → ∀ ⦃j'⦄, j' ∈ J → j ≠ j' →
      Disjoint (cfg.tubeFibre 𝒰 k j) (cfg.tubeFibre 𝒰 k j')
    intro j hj j' hj' hjj'
    rw [Finset.disjoint_left]
    intro i hij hij'
    have hj_eq : 𝒰.cover.assign k i = j := by
      simp only [tubeFibre, Tube.coverClass, Finset.mem_filter] at hij
      exact hij.2
    have hj'_eq : 𝒰.cover.assign k i = j' := by
      simp only [tubeFibre, Tube.coverClass, Finset.mem_filter] at hij'
      exact hij'.2
    exact hjj' (hj_eq.symm.trans hj'_eq)
  · apply Finset.Subset.antisymm
    · intro i hi
      rcases Finset.mem_biUnion.mp hi with ⟨j, hj, hji⟩
      exact Kakeya.VeryNotSticky.tubeFibre_subset cfg 𝒰 k j hji
    · exact hcov

open scoped Classical in
/-- **The fibre count at the hierarchy constant is a theorem of `uniform`** (GWZ Def 2.1(iii),
`gwz.txt` l.183: "`|𝕋[T_ρ]|` is constant up to a factor `∼ 1`").

At every node `j` of the level `k`, `|𝕋_{ρ}| · |𝕋[T_ρ]| ≤ Cu² |𝕋|`: the assignment classes
partition `𝕋` (`Tube.GridCoverSystem.assign_mem`, `Finset.card_eq_sum_card_fiberwise`), each
has at least `N_k / Cu` members (`Tube.UniformTubeSet.le_card_class`), so
`|𝕋_ρ| · N_k ≤ Cu |𝕋|`, and the class of `j` has at most `Cu · N_k` members
(`Tube.UniformTubeSet.card_class_le`). This is the clause the field
`Kakeya.VeryNotSticky.SplitInputs.fibreCount` carries, and what a producer of that structure
populates it with. -/
theorem card_indexSet_mul_card_tubeFibre_le (cfg : VeryNotSticky) {N : ℕ} {Cu : NNReal}
    (uniform : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N Cu) (k : ℕ)
    (hk : k ≤ N) :
    ∀ j ∈ uniform.cover.indexSet k,
      ((uniform.cover.indexSet k).card : ℝ) * ((cfg.tubeFibre uniform k j).card : ℝ) ≤
        ((Cu : ℝ) ^ 2) * (cfg.s.card : ℝ) := by
  intro j hj
  have hpart : (cfg.s.card : ℝ) =
      ∑ j' ∈ uniform.cover.indexSet k, ((cfg.tubeFibre uniform k j').card : ℝ) := by
    have h := Finset.card_eq_sum_card_fiberwise (s := cfg.s) (t := uniform.cover.indexSet k)
      (f := uniform.cover.assign k) (fun i hi => uniform.cover.assign_mem k hk i hi)
    rw [h]
    push_cast
    refine Finset.sum_congr rfl fun j' _ => ?_
    congr 2
  have hup : ((cfg.tubeFibre uniform k j).card : ℝ) ≤ (Cu : ℝ) * (uniform.branchingN k : ℝ) := by
    have h := uniform.card_class_le k hk j hj
    exact_mod_cast h
  have hlo : ∀ j' ∈ uniform.cover.indexSet k,
      (uniform.branchingN k : ℝ) ≤ (Cu : ℝ) * ((cfg.tubeFibre uniform k j').card : ℝ) := by
    intro j' hj'
    have h := uniform.le_card_class k hk j' hj'
    exact_mod_cast h
  have hsum : ((uniform.cover.indexSet k).card : ℝ) * (uniform.branchingN k : ℝ) ≤
      (Cu : ℝ) * (cfg.s.card : ℝ) := by
    rw [hpart, Finset.mul_sum]
    have := Finset.sum_le_sum hlo
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hCu : (0 : ℝ) ≤ (Cu : ℝ) := NNReal.coe_nonneg _
  have hidx : (0 : ℝ) ≤ ((uniform.cover.indexSet k).card : ℝ) := Nat.cast_nonneg _
  calc ((uniform.cover.indexSet k).card : ℝ) * ((cfg.tubeFibre uniform k j).card : ℝ)
      ≤ ((uniform.cover.indexSet k).card : ℝ) * ((Cu : ℝ) * (uniform.branchingN k : ℝ)) :=
        mul_le_mul_of_nonneg_left hup hidx
    _ = (Cu : ℝ) * (((uniform.cover.indexSet k).card : ℝ) * (uniform.branchingN k : ℝ)) := by
        ring
    _ ≤ (Cu : ℝ) * ((Cu : ℝ) * (cfg.s.card : ℝ)) := mul_le_mul_of_nonneg_left hsum hCu
    _ = (Cu : ℝ) ^ 2 * (cfg.s.card : ℝ) := by ring

open scoped Classical in
/-- **The hierarchy constant is at least one once some class is nonempty.** At an active node
`j` of the level `k` the class has `1 ≤ |𝕋[T_ρ]| ≤ Cu · N_k ≤ Cu² · |𝕋[T_ρ]|`
(`Tube.UniformTubeSet.card_class_le`, `le_card_class`), whence `1 ≤ Cu²`; the structure
`Tube.UniformTubeSet` carries no lower bound on its constant.

This used to be what let the constant `K = Cu²` of
`Kakeya.VeryNotSticky.SplitInputs.fibreCount` be fed to
`Kakeya.VeryNotSticky.nonslabKKTPow`, whose absorption step needed `1 ≤ K`. The estimate proceeds through the threshold `hCδ` and `0 ≤ M` instead — a
strictly weaker side condition, forced because
`Kakeya.VeryNotSticky.SplitInputs.countConstant` bounds the count constant only from above — so
this lemma **currently has no term-level users**. It is kept as the record of the fact about
`Tube.UniformTubeSet` ( (e)); removing it is a coherence question, not a proof
obligation. -/
theorem one_le_sq_of_mem_activeTubeNodes (cfg : VeryNotSticky) {N : ℕ} {Cu : NNReal}
    (uniform : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N Cu) {k : ℕ}
    (hk : k ≤ N) {j : cfg.ι} (hj : j ∈ cfg.activeTubeNodes uniform k) : 1 ≤ Cu ^ 2 := by
  have hjIdx : j ∈ uniform.cover.indexSet k := (Finset.mem_filter.mp hj).1
  have hne : (cfg.tubeFibre uniform k j).Nonempty := (Finset.mem_filter.mp hj).2
  have hpos : (0 : NNReal) < ((cfg.tubeFibre uniform k j).card : NNReal) := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hup : ((cfg.tubeFibre uniform k j).card : NNReal) ≤ Cu * uniform.branchingN k := by
    simpa [tubeFibre] using uniform.card_class_le k hk j hjIdx
  have hlo : uniform.branchingN k ≤ Cu * ((cfg.tubeFibre uniform k j).card : NNReal) := by
    simpa [tubeFibre] using uniform.le_card_class k hk j hjIdx
  have h : 1 * ((cfg.tubeFibre uniform k j).card : NNReal) ≤
      Cu ^ 2 * ((cfg.tubeFibre uniform k j).card : NNReal) := by
    calc
      1 * ((cfg.tubeFibre uniform k j).card : NNReal)
          = ((cfg.tubeFibre uniform k j).card : NNReal) := one_mul _
      _ ≤ Cu * uniform.branchingN k := hup
      _ ≤ Cu * (Cu * ((cfg.tubeFibre uniform k j).card : NNReal)) :=
          mul_le_mul_of_nonneg_left hlo (by positivity)
      _ = Cu ^ 2 * ((cfg.tubeFibre uniform k j).card : NNReal) := by ring
  exact le_of_mul_le_mul_right h hpos

/-- **Some `ρ₂*`-fibre is full** (blueprint `lem:ml2nonslabFullFibre`).

In the situation of `Kakeya.VeryNotSticky.nonslabFibrePartition` there is a fibre at least as
full as `𝕋` itself, hence full at the threshold `δ^η` of (C1).

Write `p(T_{ρ₂*}) = ∑_{T ∈ 𝕋[T_{ρ₂*}]} |Y(T)|` and `q(T_{ρ₂*}) = ∑_{T ∈ 𝕋[T_{ρ₂*}]} |T|`. The
fibres partition `𝕋`, so `Kakeya.ShadedBody.fullness'_biUnion` gives
`λ(𝕋, Y) = (∑ p) / (∑ q)`, and each `q` lies in `(0, ∞)` because a fibre is nonempty by
construction, while
each `δ`-tube has positive finite volume. `Kakeya.exists_sum_div_sum_le` then
supplies the fibre.

This is what discharges the fullness hypothesis `hfull` of
`Kakeya.VeryNotSticky.nonslabKKT` and `Kakeya.VeryNotSticky.nonslabKKTPow`: fullness is not
inherited by an arbitrary subfamily.

The node is returned in `Kakeya.VeryNotSticky.activeTubeNodes`, not merely in
`𝒰.cover.indexSet k`, and that matters downstream. A level-`k` node with an empty assignment
class has `μ(𝕋[T_{ρ₂*}], Y) = 0`, so any hypothesis comparing the angular multiplicity `μ(ρ₂*)`
with that multiplicity *uniformly over `IndexSet k`* would force `μ(ρ₂*) = 0` and hence be
unsatisfiable — see the field `Kakeya.VeryNotSticky.SplitInputs.angularFibre_le_fibreMult`, which is
therefore quantified over the active nodes. The selection already runs over
`activeTubeNodes`, so recording it in the conclusion costs nothing. -/
theorem exists_full_fibre (cfg : VeryNotSticky) {N : ℕ} {C₀ C : NNReal}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C)
    (k : ℕ) (hk : k ≤ N)
    (hscale_ge : cfg.rho2Star C₀ ≤ Tube.gridScale cfg.δ N k)
    (hscale_le : Tube.gridScale cfg.δ N k ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star C₀)
    (hs : cfg.s.Nonempty) :
    ∃ j ∈ cfg.activeTubeNodes 𝒰 k,
      fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody) ≤
          fullness (cfg.tubeFibre 𝒰 k j) (fun i ↦ (cfg.T i).toShadedBody) ∧
        cfg.δ ^ (2 * cfg.η) ≤ fullness (cfg.tubeFibre 𝒰 k j) (fun i ↦ (cfg.T i).toShadedBody) := by
  classical
  let V : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) := fun i ↦ (cfg.T i).toShadedBody
  let p : cfg.ι → ENNReal := fun j ↦ ∑ i ∈ cfg.tubeFibre 𝒰 k j, volume (V i).shade
  let q : cfg.ι → ENNReal := fun j ↦ ∑ i ∈ cfg.tubeFibre 𝒰 k j, volume (V i).carrier
  rcases nonslabFibrePartition cfg 𝒰 k hk hscale_ge hscale_le hs with ⟨hne, hdisj, hbUnion⟩
  -- `λ(𝕋, Y) = (∑ p) / (∑ q)`, by fullness over the partition.
  let J := cfg.activeTubeNodes 𝒰 k
  have hfull'_s : fullness' cfg.s V =
      (∑ j ∈ J, p j) / (∑ j ∈ J, q j) := by
    have hb := ShadedBody.fullness'_biUnion (J := J)
      (f := cfg.tubeFibre 𝒰 k) V hdisj
    rw [hbUnion] at hb
    simpa [p, q] using hb
  -- Each `q j` is nonzero and finite.
  have hq0 : ∀ j ∈ J, q j ≠ 0 := by
    intro j hj
    have hfib_nonempty : (cfg.tubeFibre 𝒰 k j).Nonempty := by
      simp only [J, activeTubeNodes, Finset.mem_filter] at hj
      exact hj.2
    obtain ⟨i0, hi0⟩ := hfib_nonempty
    have hpos : volume (V i0).carrier ≠ 0 := by
      change volume (cfg.T i0).carrier ≠ 0
      set n := Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) with hn
      have hLpos : (Tube.le_volume.c n : ENNReal) * (cfg.δ : ENNReal) ^ (n - 1) ≠ 0 :=
        mul_ne_zero (by exact_mod_cast (Tube.le_volume.c_pos n).ne')
          (pow_ne_zero _ (by exact_mod_cast cfg.hδ.ne'))
      exact (lt_of_lt_of_le (pos_iff_ne_zero.mpr hLpos) (Tube.le_volume (cfg.T i0).toTube)).ne'
    dsimp [q]
    intro hqj
    apply hpos
    have hle : volume (V i0).carrier ≤ (∑ i ∈ cfg.tubeFibre 𝒰 k j, volume (V i).carrier) := by
      exact Finset.single_le_sum (fun x _ => (zero_le : 0 ≤ volume (V x).carrier)) hi0
    exact le_antisymm (by simpa [hqj] using hle) (zero_le : 0 ≤ volume (V i0).carrier)
  have hqtop : ∀ j ∈ J, q j ≠ ⊤ := by
    intro j hj
    dsimp [q]
    exact (ENNReal.sum_ne_top (s := cfg.tubeFibre 𝒰 k j) (f := fun i => volume (V i).carrier)).2
      (by
        intro i hi
        change volume (cfg.T i).carrier ≠ ⊤
        exact (cfg.T i).isCompact.measure_lt_top.ne)
  -- Mediant selection gives a fibre at least as full as 𝕋.
  rcases exists_sum_div_sum_le hne p q hq0 hqtop with ⟨j, hj, hle⟩
  have hfull'_le : fullness' cfg.s V ≤ fullness' (cfg.tubeFibre 𝒰 k j) V := by
    calc
      fullness' cfg.s V =
          (∑ j ∈ J, p j) / (∑ j ∈ J, q j) := hfull'_s
      _ ≤ p j / q j := hle
      _ = fullness' (cfg.tubeFibre 𝒰 k j) V := rfl
  have hfull : fullness cfg.s V ≤ fullness (cfg.tubeFibre 𝒰 k j) V := by
    have hcoe : (fullness cfg.s V : ENNReal) ≤ (fullness (cfg.tubeFibre 𝒰 k j) V : ENNReal) := by
      rw [coe_fullness (s := cfg.s) (V := V), coe_fullness (s := cfg.tubeFibre 𝒰 k j) (V := V)]
      exact hfull'_le
    exact ENNReal.coe_le_coe.1 hcoe
  refine ⟨j, hj, ?_, ?_⟩
  · exact hfull
  · have hge : cfg.δ ^ (2 * cfg.η) ≤ fullness cfg.s V := by
      simpa [V] using cfg.fullness_ge
    exact hge.trans hfull

end Kakeya.VeryNotSticky
