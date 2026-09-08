/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ChainUniform
public import Kakeya.MultiScaleFac.FibreDensity
public import Kakeya.Frostman
public import Kakeya.GridScale
public import Kakeya.MultiScaleFac.Product
public import Kakeya.Sticky
public import Kakeya.Tube.Basic
public import Kakeya.Uniform
public import Kakeya.MultiScaleFac.Branching
public import Kakeya.MultiScaleFac.Chain
public import Mathlib.Tactic.NormNum.RealSqrt

/-!
# The stopping-time framework of GWZ §7.5–7.7

This file builds the combinatorial skeleton that GWZ Lemma 7.7(A) runs on: the geometric grid
of scales `δ^{k/M}`, the stopping-time test that decides whether a block of grid indices should
be split, and the maximal set of cut points produced by iterating that test.

**Two natural-number parameters, deliberately kept apart.**  `M` is the **grid length**: block
indices range over `0..M` and the scales are `gridScale δ M k = δ^{k/M}`, as in GWZ
Definition 2.1.  `N` is the **step budget**: it bounds the number of stopping-time steps and
indexes the exponent chain `η : ℕ → ℝ`, and GWZ obtain it from `∏ δ_j ≈ δ` together with
`δ_j < δ^{ε²}`, without reference to the grid.  The two used to be one parameter, tied to `ε` by
`ε = 1/√N`; the grid-side lemmas below now ask only for facts about `ε` and `M`, such as
`0 < ε`, `ε ≤ 1/4` and the threshold `4 ≤ ε · M`, so that the grid may be taken as long as one
likes.  The only link this file can supply is combinatorial — each cut consumes a grid point, so
at most `M - 1` cuts occur — and it appears as an explicit hypothesis `M ≤ N` of the two
stopping-time theorems.

The pieces are:

* `gridScale δ M k = δ^{k/M}` with the arithmetic the chain needs — the endpoints
  `gridScale δ M 0 = 1` and `gridScale δ M M = δ`, antitonicity in `k`, the ratio formula, and
  the `16`-separation of consecutive grid scales that
  `MultiScaleFac.frostmanConstant_fibre_le_prod` requires (valid once `δ ≤ 16^{-M}`).

* `BlockFrostman`, the per-block Frostman bound `C_F(𝕋_{σ_b∣σ_a}[i₀]) ≤ C · (σ_a/σ_b)^ζ`, and
  `SplitTest`, the stopping-time test: the block `(a,b)` splits if some grid index `c` well
  inside the block already carries the block bound on its fine half.  The multiplicative
  constant `C` is carried explicitly: the analytic steps that move a block bound between
  sub-blocks (`BlockRestrictStep`, `exists_blockFrostman_truncate`) genuinely lose a
  `δ`-independent factor, and pretending otherwise would make those steps false.

* `exists_maximal_cuts_abstract`, the stopping time itself, stated for abstract predicates on
  pairs of indices so that the induction is pure combinatorics on `Finset ℕ`.  Its output is a
  cut set `S` whose adjacent blocks all satisfy the block bound and are either short or fail the
  test.

* `cutChain`, which reads a cut set `S` as the decreasing chain `σ : Fin (J+3) → ℝ≥0` of scales
  demanded by `MultiScaleFac.frostmanConstant_fibre_le_prod`, together with the verification of
  every hypothesis of that theorem and the resulting product bound
  `frostmanConstant_fibre_le_prod_of_cuts`.

The analytic step that transfers a block bound from a block to its coarse sub-block (GWZ's
appeal to the inherited upward property, `ConvexSpaceBody.IsFrostmanIn.inherited_upwards_uniform`)
is packaged as the predicate `BlockRestrictStep` and enters `exists_maximal_cuts` as the
hypothesis `hrestrict`.  Keeping it a hypothesis is what makes the stopping time itself
independent of the geometry; it is the only interface this file leaves open, and it is where the
exponent gap `η k ≤ ε · η (k+1)` of Lemma 7.7(A) is spent.

Because `ConvexSpaceBody.IsFrostmanIn.inherited_upwards_uniform` concludes at the constant
`C' * C` rather than at `C`, each cut multiplies the block constant by a fixed `δ`-independent
factor `C'`.  After `m` cuts the constant is `C' ^ m`, and `m < N` bounds it by `C' ^ N`; that
uniform bound is precisely the source of the existentially quantified constant `C` in the
statement of GWZ Lemma 7.7(A).

`⪅` does not appear: every bound carries an explicit constant, as required by.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace Kakeya

open StickyKakeya
open MultiScaleFac

namespace MultiScaleFac

open _root_.StickyKakeya

universe u

/-! ### The stopping time -/

/-- **A set of grid indices with pairwise gaps at least `w` is small.**  If any two distinct
elements of `S ⊆ [0, M]` differ by at least `w`, then `x ↦ x / w` is injective on `S` and lands in
`[0, M / w]`, so `S` has at most `M / w + 1` elements.  This replaces the crude "each cut consumes a
grid point" bound of `exists_maximal_cuts_abstract`. -/
private theorem card_le_div_succ_of_gap {w M : ℕ} (hw : 0 < w) {S : Finset ℕ}
    (hsub : S ⊆ Finset.range (M + 1))
    (hgap : ∀ x ∈ S, ∀ y ∈ S, x < y → x + w ≤ y) :
    S.card ≤ M / w + 1 := by
  classical
  have key : ∀ x ∈ S, ∀ y ∈ S, x < y → x / w + 1 ≤ y / w := by
    intro x hx y hy hxy
    rw [← Nat.add_div_right x hw]
    exact Nat.div_le_div_right (hgap x hx y hy hxy)
  have hcard := Finset.card_le_card_of_injOn (t := Finset.range (M / w + 1)) (fun x => x / w)
    (fun x hx => Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Nat.div_le_div_right (Nat.le_of_lt_succ (Finset.mem_range.mp (hsub hx))))))
    (fun x hx y hy h => by
      have h' : x / w = y / w := h
      rcases lt_trichotomy x y with hxy | hxy | hxy
      · have := key x hx y hy hxy; omega
      · exact hxy
      · have := key y hy x hx hxy; omega)
  simpa using hcard

/-- **A `w`-separated cut set of `[0,M]` has at most `N` cuts** when `M ≤ w N`.
`card_le_div_succ_of_gap` bounds `S.card` by `M / w + 1`, so `S.card = m + 2` gives `m + 1 ≤ M / w`;
multiplying by `w` and using `(M / w) w ≤ M ≤ w N` gives `(m+1) w ≤ N w`, whence `m + 1 ≤ N`. -/
private theorem succ_le_of_card_gap {M N w m : ℕ} (hw : 0 < w) (hwN : M ≤ w * N)
    {S : Finset ℕ} (hsub : S ⊆ Finset.range (M + 1))
    (hgap : ∀ x ∈ S, ∀ y ∈ S, x < y → x + w ≤ y) (hcard : S.card = m + 2) :
    m + 1 ≤ N := by
  have hcnt : S.card ≤ M / w + 1 := card_le_div_succ_of_gap hw hsub hgap
  have hm1 : m + 1 ≤ M / w := by omega
  have hmw : (m + 1) * w ≤ (M / w) * w := Nat.mul_le_mul_right w hm1
  have hdivM : (M / w) * w ≤ M := Nat.div_mul_le_self M w
  have hmwN : (m + 1) * w ≤ w * N := le_trans (le_trans hmw hdivM) hwN
  have hmwN' : (m + 1) * w ≤ N * w := by
    calc
      (m + 1) * w ≤ w * N := hmwN
      _ = N * w := mul_comm w N
  exact Nat.le_of_mul_le_mul_right hmwN' hw

/-- **Inserting a cut that sits `w` inside its block keeps the cut set `w`-separated.**

The new point `c` lies in the adjacent block `(a,b)` at distance at least `w` from both ends, and
`(a,b)` contains no old point, so every old point is either `≤ a` or `≥ b`; the gap to `c` is
therefore at least `w` on both sides, and gaps between old points are unchanged. -/
private theorem gap_insert_of_cut {w a b c : ℕ} {S : Finset ℕ}
    (hadj : ∀ x ∈ S, ¬(a < x ∧ x < b))
    (hac : a + w ≤ c) (hcb : c + w ≤ b) (hac' : a < c) (hcb' : c < b)
    (hgap : ∀ x ∈ S, ∀ y ∈ S, x < y → x + w ≤ y) :
    ∀ x ∈ insert c S, ∀ y ∈ insert c S, x < y → x + w ≤ y := by
  intro x hx y hy hxy
  rcases Finset.mem_insert.mp hx with hxc | hxS
  · rw [hxc] at hxy ⊢
    rcases Finset.mem_insert.mp hy with hyc | hyS
    · rw [hyc] at hxy ⊢
      exact (lt_irrefl c hxy).elim
    · have hby : b ≤ y := by
        by_contra h
        have hyltb : y < b := Nat.lt_of_not_ge h
        have hacy : a < y := lt_trans hac' hxy
        exact hadj y hyS ⟨hacy, hyltb⟩
      exact le_trans hcb hby
  · rcases Finset.mem_insert.mp hy with hyc | hyS
    · rw [hyc] at hxy ⊢
      have hxa : x ≤ a := by
        by_contra h
        have halt : a < x := Nat.lt_of_not_ge h
        have hxlb : x < b := lt_trans hxy hcb'
        exact hadj x hxS ⟨halt, hxlb⟩
      exact le_trans (Nat.add_le_add_right hxa w) hac
    · exact hgap x hxS y hyS hxy

/-- **The block-bound invariant survives one cut, in the stateful form.**  After inserting `c` into
`S`, an adjacent pair of `insert c S` is either one of the two halves `(a,c)`, `(c,b)` of the block
that was cut — where the split supplies the bound at the new state — or an untouched adjacent pair
of `S`, whose old bound is raised by `hmono` and then transported by `hdescend`. -/
private theorem invState_insert_of_cut {σ : Type*} {Good : ℕ → ℕ → ℕ → σ → Prop}
    {Rel : ℕ → σ → σ → Prop} {M N : ℕ}
    (hmono : ∀ j j' : ℕ, j ≤ j' → j' ≤ N → ∀ a b : ℕ, a < b → ∀ x : σ, Good j a b x → Good j' a b x)
    (hdescend : ∀ j a b : ℕ, a < b → b ≤ M → ∀ x y : σ, Rel 1 x y → Good j a b x → Good j a b y)
    {S : Finset ℕ} {m : ℕ} {x y : σ} {a b c : ℕ}
    (hsub : S ⊆ Finset.range (M + 1)) (haS : a ∈ S) (hbS : b ∈ S)
    (hadj : ∀ z ∈ S, ¬(a < z ∧ z < b)) (hac : a < c) (hcb : c < b) (hle1 : m + 1 ≤ N)
    (hxy : Rel 1 x y) (gac : Good (m + 1) a c y) (gcb : Good (m + 1) c b y)
    (hINV : ∀ p ∈ S, ∀ q ∈ S, p < q → (∀ z ∈ S, ¬(p < z ∧ z < q)) → Good m p q x) :
    ∀ p ∈ insert c S, ∀ q ∈ insert c S, p < q → (∀ z ∈ insert c S, ¬(p < z ∧ z < q)) →
      Good (m + 1) p q y := by
  intro a' ha' b' hb' hab' hadj'
  rcases Finset.mem_insert.mp ha' with ha'c | haS'
  · rw [ha'c] at hab' hadj'
    have hbS' : b' ∈ S := by
      rcases Finset.mem_insert.mp hb' with hb'c | hbS''
      · rw [hb'c] at hab'
        exact (lt_irrefl c hab').elim
      · exact hbS''
    have hb_le_b' : b ≤ b' := by
      by_contra h
      have hb'ltb : b' < b := Nat.lt_of_not_ge h
      have ha_lt_b' : a < b' := lt_trans hac hab'
      exact hadj b' hbS' ⟨ha_lt_b', hb'ltb⟩
    have hb'_le_b : b' ≤ b := by
      by_contra h
      have hblt : b < b' := Nat.lt_of_not_ge h
      exact hadj' b (Finset.mem_insert.mpr (Or.inr hbS)) ⟨hcb, hblt⟩
    have hb'_eq : b' = b := Nat.le_antisymm hb'_le_b hb_le_b'
    rw [ha'c, hb'_eq]
    exact gcb
  · rcases Finset.mem_insert.mp hb' with hb'c | hbS'
    · rw [hb'c] at hab' hadj'
      have ha_le_a' : a ≤ a' := by
        by_contra h
        have ha'lt : a' < a := Nat.lt_of_not_ge h
        exact hadj' a (Finset.mem_insert.mpr (Or.inr haS)) ⟨ha'lt, hac⟩
      have ha'_le_a : a' ≤ a := by
        by_contra h
        have halt : a < a' := Nat.lt_of_not_ge h
        have ha'ltb : a' < b := lt_trans hab' hcb
        exact hadj a' haS' ⟨halt, ha'ltb⟩
      have ha'_eq : a' = a := Nat.le_antisymm ha'_le_a ha_le_a'
      rw [ha'_eq, hb'c]
      exact gac
    · have hadjS : ∀ y ∈ S, ¬(a' < y ∧ y < b') := by
        intro z hz hmid
        exact hadj' z (Finset.mem_insert.mpr (Or.inr hz)) hmid
      have hgS : Good m a' b' x := hINV a' haS' b' hbS' hab' hadjS
      have hgS1 : Good (m + 1) a' b' x :=
        hmono m (m + 1) (Nat.le_succ m) hle1 a' b' hab' x hgS
      have hb'M : b' ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp (hsub hbS'))
      exact hdescend (m + 1) a' b' hab' hb'M x y hxy hgS1

/-- **The induction behind `exists_maximal_cuts_abstract_state_margin`.**  The loop of
`exists_maximal_cuts_abstract_state` run with the extra invariant that the cut points are pairwise
`w`-separated, so that the terminal index is bounded through `succ_le_of_card_gap` rather than
through a hypothesis `M ≤ N`.  The recursion is on `n = M + 1 - S.card`. -/
private theorem exists_maximal_cuts_abstract_state_margin_aux {σ : Type*} (M N w : ℕ)
    (hw : 0 < w) (hwN : M ≤ w * N)
    (Good Test : ℕ → ℕ → ℕ → σ → Prop) (Long : ℕ → ℕ → Prop) (Rel : ℕ → σ → σ → Prop) (x₀ : σ)
    (hcomp : ∀ (k l : ℕ) (x y z : σ), Rel k x y → Rel l y z → Rel (k + l) x z)
    (hmono : ∀ j j' : ℕ, j ≤ j' → j' ≤ N → ∀ a b : ℕ, a < b → ∀ x : σ, Good j a b x → Good j' a b x)
    (hdescend : ∀ j a b : ℕ, a < b → b ≤ M → ∀ x y : σ, Rel 1 x y → Good j a b x → Good j a b y)
    (hsplit : ∀ j a b : ℕ, j + 1 ≤ N → a < b → b ≤ M → Long a b → ∀ x : σ, Good j a b x →
      Test (j + 1) a b x →
      ∃ (y : σ) (c : ℕ), Rel 1 x y ∧ a + w ≤ c ∧ c + w ≤ b ∧
        Good (j + 1) a c y ∧ Good (j + 1) c b y) :
    ∀ n : ℕ, ∀ S : Finset ℕ, ∀ m : ℕ, ∀ x : σ,
      0 ∈ S → M ∈ S → S ⊆ Finset.range (M + 1) → S.card = m + 2 →
      (∀ p ∈ S, ∀ q ∈ S, p < q → p + w ≤ q) → Rel m x₀ x →
      (∀ a ∈ S, ∀ b ∈ S, a < b → (∀ y ∈ S, ¬(a < y ∧ y < b)) → Good m a b x) →
      n = M + 1 - S.card →
      ∃ (S' : Finset ℕ) (m' : ℕ) (x' : σ), m' < N ∧ Rel m' x₀ x' ∧ 0 ∈ S' ∧ M ∈ S' ∧
        S' ⊆ Finset.range (M + 1) ∧ S'.card = m' + 2 ∧
        ∀ a ∈ S', ∀ b ∈ S', a < b → (∀ y ∈ S', ¬(a < y ∧ y < b)) →
          Good m' a b x' ∧ (¬ Long a b ∨ ¬ Test (m' + 1) a b x') := by
  classical
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih S m x h0 hMmem hsub hcard hgap hRel hINV hn
  have hle1 : m + 1 ≤ N := succ_le_of_card_gap hw hwN hsub hgap hcard
  by_cases hsplit_case : ∃ a ∈ S, ∃ b ∈ S, a < b ∧
      (∀ y ∈ S, ¬(a < y ∧ y < b)) ∧ Long a b ∧ Test (m + 1) a b x
  · rcases hsplit_case with ⟨a, haS, b, hbS, hab, hadj, hlong, htest⟩
    have hbM : b ≤ M := by
      exact Nat.le_of_lt_succ (Finset.mem_range.mp (hsub hbS))
    have hg : Good m a b x := hINV a haS b hbS hab hadj
    have hgm : Good (m + 1) a b x := hmono m (m + 1) (Nat.le_succ m) hle1 a b hab x hg
    rcases hsplit m a b hle1 hab hbM hlong x hg htest with ⟨y, c, hxy, hac, hcb, gac, gcb⟩
    have hac' : a < c := by omega
    have hcb' : c < b := by omega
    have hc_notS : c ∉ S := by
      intro hcS
      exact hadj c hcS ⟨hac', hcb'⟩
    have hcR : c ∈ Finset.range (M + 1) := by
      exact Finset.mem_range.mpr (by omega)
    have hS'card : (insert c S).card = (m + 1) + 2 := by
      simpa [hcard] using (Finset.card_insert_of_notMem hc_notS)
    have hS'Sub : insert c S ⊆ Finset.range (M + 1) := by
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hxS
      · exact hcR
      · exact hsub hxS
    have h0in : 0 ∈ insert c S := Finset.mem_insert.mpr (Or.inr h0)
    have hMin : M ∈ insert c S := Finset.mem_insert.mpr (Or.inr hMmem)
    have hRel' : Rel (m + 1) x₀ y := (hcomp m 1 x₀ x y) hRel hxy
    have hINV' : ∀ p ∈ insert c S, ∀ q ∈ insert c S, p < q →
        (∀ z ∈ insert c S, ¬(p < z ∧ z < q)) → Good (m + 1) p q y := by
      exact invState_insert_of_cut hmono hdescend hsub haS hbS hadj hac' hcb' hle1 hxy gac gcb hINV
    have hgap' : ∀ p ∈ insert c S, ∀ q ∈ insert c S, p < q → p + w ≤ q := by
      exact gap_insert_of_cut hadj hac hcb hac' hcb' hgap
    have hle_card : (insert c S).card ≤ M + 1 := by
      have hle2 : (insert c S).card ≤ (Finset.range (M + 1)).card :=
        Finset.card_le_card hS'Sub
      simpa [Finset.card_range] using hle2
    have hmeasure : M + 1 - (insert c S).card < n := by
      have hci : (insert c S).card = S.card + 1 := Finset.card_insert_of_notMem hc_notS
      omega
    exact (ih (M + 1 - (insert c S).card) hmeasure) (insert c S) (m + 1) y h0in hMin hS'Sub
      hS'card hgap' hRel' hINV' rfl
  · refine ⟨S, m, x, by omega, hRel, h0, hMmem, hsub, hcard, ?_⟩
    intro a haS b hbS hab hadj
    constructor
    · exact hINV a haS b hbS hab hadj
    · by_cases hl : Long a b
      · right
        intro ht
        exact hsplit_case ⟨a, haS, b, hbS, hab, hadj, hl, ht⟩
      · exact Or.inl hl

/-- **The maximal cut set with a refining state, with the step bound decoupled from the grid
length.**  The common refinement of `exists_maximal_cuts_abstract_state` and
`exists_maximal_cuts_abstract_margin`: the stopping time carries a state refined at every cut, *and*
the number of cuts is bounded through the margin `w` rather than through the crude `M ≤ N`.  This is
what the refined Lemma 7.7(A) needs on the diverging grid of GWZ Definition 2.1. -/
theorem exists_maximal_cuts_abstract_state_margin {σ : Type*} (M N w : ℕ)
    (hw : 0 < w) (hwM : w ≤ M) (hwN : M ≤ w * N)
    (Good Test : ℕ → ℕ → ℕ → σ → Prop) (Long : ℕ → ℕ → Prop) (Rel : ℕ → σ → σ → Prop) (x₀ : σ)
    (hrefl : ∀ x : σ, Rel 0 x x)
    (hcomp : ∀ (k l : ℕ) (x y z : σ), Rel k x y → Rel l y z → Rel (k + l) x z)
    (hGood : Good 0 0 M x₀)
    (hmono : ∀ j j' : ℕ, j ≤ j' → j' ≤ N → ∀ a b : ℕ, a < b → ∀ x : σ, Good j a b x → Good j' a b x)
    (hdescend : ∀ j a b : ℕ, a < b → b ≤ M → ∀ x y : σ, Rel 1 x y → Good j a b x → Good j a b y)
    (hsplit : ∀ j a b : ℕ, j + 1 ≤ N → a < b → b ≤ M → Long a b → ∀ x : σ, Good j a b x →
      Test (j + 1) a b x →
      ∃ (y : σ) (c : ℕ), Rel 1 x y ∧ a + w ≤ c ∧ c + w ≤ b ∧
        Good (j + 1) a c y ∧ Good (j + 1) c b y) :
    ∃ (S : Finset ℕ) (m : ℕ) (x : σ), m < N ∧ Rel m x₀ x ∧ 0 ∈ S ∧ M ∈ S ∧
      S ⊆ Finset.range (M + 1) ∧ S.card = m + 2 ∧
      ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ y ∈ S, ¬(a < y ∧ y < b)) →
        Good m a b x ∧ (¬ Long a b ∨ ¬ Test (m + 1) a b x) := by
  refine exists_maximal_cuts_abstract_state_margin_aux M N w hw hwN Good Test Long Rel x₀ hcomp
    hmono hdescend hsplit
    (M + 1 - ({0, M} : Finset ℕ).card) ({0, M} : Finset ℕ) 0 x₀ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl
  · simp
  · simp
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxN
    · exact Finset.mem_range.mpr (by omega)
    · have hxeq : x = M := by simpa using hxN
      rw [hxeq]
      exact Finset.mem_range.mpr (by omega)
  · have h0neN : (0 : ℕ) ≠ M := by omega
    have h0mn : 0 ∉ ({M} : Finset ℕ) := by
      intro h
      exact h0neN (by simpa using h)
    simp [Finset.card_insert_of_notMem h0mn]
  · intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with rfl | hxM
    · rcases Finset.mem_insert.mp hy with rfl | hyM
      · exact (lt_irrefl 0 hxy).elim
      · have hyeq : y = M := by simpa using hyM
        rw [hyeq]
        simpa using hwM
    · have hxeq : x = M := by simpa using hxM
      rw [hxeq] at hxy ⊢
      rcases Finset.mem_insert.mp hy with rfl | hyM
      · simp at hxy
      · have hyeq : y = M := by simpa using hyM
        rw [hyeq] at hxy
        exact (lt_irrefl M hxy).elim
  · exact hrefl x₀
  · intro a ha b hb hab hadj
    have ha_eq : a = 0 := by
      rcases Finset.mem_insert.mp ha with h0 | hN0
      · exact h0
      · exfalso
        have haN : a = M := by simpa using hN0
        rcases Finset.mem_insert.mp hb with hb0 | hbN
        · omega
        · have hbN' : b = M := by simpa using hbN
          omega
    have hb_eq : b = M := by
      rcases Finset.mem_insert.mp hb with hb0 | hbN
      · exfalso
        omega
      · simpa using hbN
    rw [ha_eq, hb_eq]
    exact hGood

section Geometry

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-- **The per-block Frostman bound at a single anchor.**  `BlockFrostmanAt s T M C ζ a b i₀` says
that the fibre family `𝕋[T_{i₀}^{(σ_a)}] = {i : T_i ⊆ T_{i₀}^{(σ_a)}}`, with its members thickened
to the fine grid scale `σ_b`, has Frostman constant at most `C · (σ_a/σ_b)^ζ` in the doubled anchor
`T_{i₀}^{(2σ_a)}`.  Here `M` is the **grid length**, `σ_k = gridScale δ M k = δ^{k/M}`, and the
index set is fixed at the leaf scale, which is GWZ's own convention. -/
def BlockFrostmanAt {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E) (M : ℕ) (C : NNReal) (ζ : ℝ)
    (a b : ℕ) (i₀ : ι) : Prop :=
  ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (gridScale δ M a) i₀)
      (fibreBodies T (gridScale δ M b))
      ((T i₀).rescale (2 * gridScale δ M a)).toConvexSpaceBody
    ≤ (C : ENNReal) * ENNReal.ofReal (((gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)) ^ ζ)

/-- **The per-block Frostman bound.**  `BlockFrostman s T M C ζ a b` says that for every anchor
`i₀ ∈ s` the fibre family `𝕋_{σ_b∣σ_a}[i₀]` of tubes thickened to the fine grid scale `σ_b` and
contained in `T_{i₀}^{(σ_a)}` has Frostman constant at most `C · (σ_a/σ_b)^ζ`, where
`σ_k = gridScale δ M k`.  This is the quantity GWZ Lemma 7.7(A) tracks along the dividing scales. -/
def BlockFrostman {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E) (M : ℕ) (C : NNReal) (ζ : ℝ)
    (a b : ℕ) : Prop :=
  ∀ i₀ ∈ s, BlockFrostmanAt s T M C ζ a b i₀

omit [Nontrivial E] in
/-- **The block bound at a single anchor weakens as the constant and the exponent grow.**  The
one-anchor form of `BlockFrostman.mono`; the ratio `σ_a/σ_b` is at least `1`, so raising the
exponent enlarges the right-hand side. -/
private theorem BlockFrostmanAt.mono {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {s : Finset ι}
    {T : ι → Tube δ E} {M : ℕ} {C C' : NNReal} {ζ ζ' : ℝ} (hCC' : C ≤ C') (_hζ : 0 ≤ ζ)
    (hζζ' : ζ ≤ ζ') {a b : ℕ} (hab : a ≤ b) {i₀ : ι}
    (h : BlockFrostmanAt s T M C ζ a b i₀) : BlockFrostmanAt s T M C' ζ' a b i₀ := by
  let r : ℝ := (gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)
  have hb_pos : 0 < (gridScale δ M b : ℝ) := by
    exact_mod_cast (gridScale_pos hδ M b)
  have hblea : gridScale δ M b ≤ gridScale δ M a := gridScale_antitone hδ hδ1 M hab
  have hr1 : (1 : ℝ) ≤ r := by
    dsimp [r]
    exact (one_le_div hb_pos).mpr (by exact_mod_cast hblea)
  calc
    ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (gridScale δ M a) i₀)
        (fibreBodies T (gridScale δ M b))
        ((T i₀).rescale (2 * gridScale δ M a)).toConvexSpaceBody
        ≤ (C : ENNReal) * ENNReal.ofReal (((gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)) ^ ζ) :=
        h
    _ ≤ (C' : ENNReal) * ENNReal.ofReal (r ^ ζ) := by
      dsimp [r]
      exact mul_le_mul' (ENNReal.coe_le_coe.mpr hCC') le_rfl
    _ ≤ (C' : ENNReal) * ENNReal.ofReal (r ^ ζ') := by
      exact mul_le_mul' le_rfl
        (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hr1 hζζ'))

omit [Nontrivial E] in
/-- **The block bound weakens as the constant and the exponent grow.**  Since `a ≤ b` makes the
ratio `σ_a/σ_b` at least `1`, raising the exponent enlarges the right-hand side; raising the
constant obviously does.  This is the `hmono` hypothesis of `exists_maximal_cuts_abstract`: the
blocks that a split does not touch keep their bound when the stopping time's constant and
exponent indices advance. -/
theorem BlockFrostman.mono {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {s : Finset ι}
    {T : ι → Tube δ E} {M : ℕ} {C C' : NNReal} {ζ ζ' : ℝ} (hCC' : C ≤ C') (hζ : 0 ≤ ζ)
    (hζζ' : ζ ≤ ζ') {a b : ℕ} (hab : a ≤ b)
    (h : BlockFrostman s T M C ζ a b) : BlockFrostman s T M C' ζ' a b := by
  intro i₀ hi₀
  exact (h i₀ hi₀).mono hδ hδ1 hCC' hζ hζζ' hab

end Geometry

/-- **A block is long** if its length exceeds `⌈εM⌉`, the threshold at which GWZ's stopping
time still bothers to test it.  Here `M` is the **grid length**, so that a long block spans a
scale ratio of at least `δ^{-ε}`; it is not the bound on the number of stopping-time steps. -/
def IsLongBlock (M : ℕ) (ε : ℝ) (a b : ℕ) : Prop := ⌈ε * (M : ℝ)⌉₊ + a < b

/-! ### Arithmetic of the sampling exponent `ε = 1/√N`

Three throwaway facts about `ε = 1 / Real.sqrt N` under `16 ≤ N`.  They exist so that the
grid-side lemmas below can be stated in terms of `ε` and the grid length alone, and every call
site that still carries `16 ≤ N` and `ε = 1/√N` can discharge them in one step. -/

/-- **`ε = 1/√N` is positive** once `N` is positive (here: `16 ≤ N`). -/
theorem eps_pos_of_eq_one_div_sqrt {N : ℕ} (hN : 16 ≤ N) {ε : ℝ}
    (hε : ε = 1 / Real.sqrt (N : ℝ)) : 0 < ε := by
  have hN_real : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h4le : (4 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    have := Real.sqrt_le_sqrt hN_real
    rwa [show Real.sqrt (16 : ℝ) = 4 by norm_num] at this
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) h4le
  rw [hε]
  exact one_div_pos.mpr hsqrt_pos

/-- **`ε = 1/√N` squares to `1/N`:** `ε² · N = 1`.  This is the identity that the exponent
budget of alternative (i) is spent against; stating it separately lets the consumers ask only for
the inequality `1 ≤ ε² · M` against an arbitrary grid length `M`. -/
theorem eps_sq_mul_eq_one_of_eq_one_div_sqrt {N : ℕ} (hN : 0 < N) {ε : ℝ}
    (hε : ε = 1 / Real.sqrt (N : ℝ)) : ε ^ 2 * (N : ℝ) = 1 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [hε, div_pow, one_pow, Real.sq_sqrt (le_of_lt hNpos)]
  field_simp

/-- **The test interval of a long block is nonempty.**  With `ε ≤ 1/4` and a grid long enough
that `ε · M ≥ 4`, a long block has length at least `⌈εM⌉ + 1 ≥ 5`; hence the margin `⌈ε(b-a)⌉`
fits twice inside the block.  This is the role of the hypothesis `16 ≤ N` in GWZ Lemma 7.7(A),
here split off from the sampling exponent: only the grid length `M` and `ε` enter. -/
theorem two_mul_ceil_add_le_of_isLongBlock {M : ℕ} {ε : ℝ} (hεpos : 0 < ε)
    (hε4 : ε ≤ 1 / 4) (hM : (4 : ℝ) ≤ ε * (M : ℝ)) {a b : ℕ} (_hb : b ≤ M)
    (hlong : IsLongBlock M ε a b) :
    a + 2 * ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b := by
  have hlong' : ⌈ε * (M : ℝ)⌉₊ + a < b := hlong
  have hceilN : (4 : ℕ) ≤ ⌈ε * (M : ℝ)⌉₊ := by
    exact_mod_cast hM.trans (Nat.le_ceil (ε * (M : ℝ)))
  have hL : (b : ℝ) - (a : ℝ) = ((b - a : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : a ≤ b)]
  have h4 : (4 : ℝ) ≤ ((b - a : ℕ) : ℝ) := by exact_mod_cast (by omega : (4 : ℕ) ≤ b - a)
  rw [hL]
  have hεL : ε * ((b - a : ℕ) : ℝ) ≤ ((b - a : ℕ) : ℝ) / 4 := by nlinarith
  have hm_le : (⌈ε * ((b - a : ℕ) : ℝ)⌉₊ : ℝ) ≤ ((b - a : ℕ) : ℝ) / 4 + 1 :=
    le_trans (by exact_mod_cast Nat.ceil_le_ceil hεL)
      (Nat.ceil_lt_add_one (by linarith)).le
  have hnat : 2 * ⌈ε * ((b - a : ℕ) : ℝ)⌉₊ ≤ b - a := by
    have : ((2 * ⌈ε * ((b - a : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) ≤ ((b - a : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  omega

/-! ### The exponent chain -/

section Geometry2

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-- **The coarse-side restriction step of GWZ Lemma 7.7(A), as a predicate.**
`BlockRestrictStep s T M ε C'` says: whenever the block `(a,b)` carries the bound at constant `C`
and exponent `ζ`, and `c` is a cut point at relative depth at least `ε` from the coarse end `a`,
then the coarse sub-block `(a,c)` carries the bound at constant `C' * C` and at the weaker exponent
`ζ'`, provided `ζ ≤ ε · ζ'`.  This is the step that spends the gap `η_j ≤ ε · η_{j+1}`. -/
def BlockRestrictStep {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E) (M : ℕ) (ε : ℝ)
    (C' : NNReal) : Prop :=
  ∀ (C : NNReal) (ζ ζ' : ℝ), 0 ≤ ζ → ζ ≤ ε * ζ' → ∀ a c b : ℕ,
    a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c → c < b → b ≤ M →
    BlockFrostman s T M C ζ a b → BlockFrostman s T M (C' * C) ζ' a c

end Geometry2

section GeometryUniform

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- **The coarse-side half of a cut.**  See `BlockRestrictStep`.  Thickening the members of the
block family from the fine scale `σ_b` up to the cut scale `σ_c` preserves the Frostman bound up to
a `δ`-independent factor: in the leaf-indexed convention the index set and the test body are the
same on both sides, so only the member bodies change.  The exponent arithmetic that makes the two
sides match is `σ_a/σ_c ≥ (σ_a/σ_b)^ε`, valid because `c - a ≥ ε(b-a)`. -/
theorem gridScale_ratio_rpow_le_of_cut {δ : NNReal} (hδ : 0 < δ) (hδ1 : (δ : ℝ) ≤ 1) (M : ℕ)
    {ε ζ ζ' : ℝ} (hεpos : 0 < ε) (hζ : 0 ≤ ζ) (hgap : ζ ≤ ε * ζ') {a c b : ℕ}
    (hac : a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c) (hcb : c < b) :
    ((gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)) ^ ζ
      ≤ ((gridScale δ M a : ℝ) / (gridScale δ M c : ℝ)) ^ ζ' := by
  by_cases hN0 : M = 0
  · subst M
    simp [gridScale]
  · have hδpos : 0 < (δ : ℝ) := by exact_mod_cast hδ
    have hδnonneg : 0 ≤ (δ : ℝ) := le_of_lt hδpos
    have hNpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hN0)
    have hratio_b : (gridScale δ M a : ℝ) / (gridScale δ M b : ℝ) =
        (δ : ℝ) ^ (-(((b : ℝ) - (a : ℝ)) / (M : ℝ))) := by
      rw [← NNReal.coe_div, gridScale_div_gridScale hδ M a b, NNReal.coe_rpow]
    have hratio_c : (gridScale δ M a : ℝ) / (gridScale δ M c : ℝ) =
        (δ : ℝ) ^ (-(((c : ℝ) - (a : ℝ)) / (M : ℝ))) := by
      rw [← NNReal.coe_div, gridScale_div_gridScale hδ M a c, NNReal.coe_rpow]
    rw [hratio_b, hratio_c]
    rw [← Real.rpow_mul hδnonneg, ← Real.rpow_mul hδnonneg]
    apply Real.rpow_le_rpow_of_exponent_ge hδpos hδ1
    have ha_le_c : a ≤ c := by omega
    have hbc0 : (0 : ℝ) ≤ (b : ℝ) - (a : ℝ) :=
      sub_nonneg.mpr (by exact_mod_cast (by omega : a ≤ b))
    have hζ'0 : 0 ≤ ζ' :=
      nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hζ.trans hgap) hεpos
    have hceil_le : ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c - a := by omega
    have h₁ : (⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ : ℝ) ≤ (c : ℝ) - (a : ℝ) := by exact_mod_cast hceil_le
    have hεba_le_ca : ε * ((b : ℝ) - (a : ℝ)) ≤ (c : ℝ) - (a : ℝ) := (Nat.le_ceil _).trans h₁
    have hkey : ((b : ℝ) - (a : ℝ)) / (M : ℝ) * ζ ≤ ((c : ℝ) - (a : ℝ)) / (M : ℝ) * ζ' := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hNpos]
      linarith [mul_le_mul_of_nonneg_right hgap hbc0, mul_le_mul_of_nonneg_left hεba_le_ca hζ'0]
    linarith

theorem exists_blockRestrictStep (Cu : NNReal) (_hCu : 1 ≤ Cu) :
    ∃ C' : NNReal, 1 ≤ C' ∧
      ∀ (M : ℕ), 0 < M → ∀ {ε : ℝ}, 0 < ε →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 →
      δ ≤ (16 : NNReal) ^ (-(M : ℝ)) →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      UniformTubeSet s T M Cu →
      ComparableFibreCounts s T (gridScales δ M) Cu →
      BlockRestrictStep s T M ε C' := by
  classical
  let Cvol : NNReal :=
    (Tube.volume_le.C (Module.finrank ℝ E) / Tube.le_volume.c (Module.finrank ℝ E)) ^ 2
  let C' : NNReal := max 1 Cvol
  refine ⟨C', le_max_left 1 Cvol, ?_⟩
  intro M hM ε hεpos ι δ hδ hδ1 hδ16 s T hball huniform hcmp
  dsimp [BlockRestrictStep]
  intro C ζ ζ' hζ0 hgap a c b hcut hcb hbN hgood
  dsimp [BlockFrostman] at hgood
  intro i₀ hi₀
  dsimp [BlockFrostmanAt] at hgood ⊢
  have hNpos : 0 < M := hM
  have hδ1nn : δ ≤ 1 := by exact_mod_cast hδ1
  have hσa1 : gridScale δ M a ≤ 1 := gridScale_le_one hδ1nn M a
  have hδσb : δ ≤ gridScale δ M b := by
    calc
      δ = gridScale δ M M := (gridScale_self δ hNpos).symm
      _ ≤ gridScale δ M b := gridScale_antitone hδ hδ1nn M hbN
  have hσbσc : gridScale δ M b ≤ gridScale δ M c :=
    gridScale_antitone hδ hδ1nn M (le_of_lt hcb)
  have hac : a ≤ c := by omega
  have hσcσa : gridScale δ M c ≤ gridScale δ M a :=
    gridScale_antitone hδ hδ1nn M hac
  have h1 := frostmanConstant_blockFibre_member_le (E := E) (s := s) (T := T)
    (σ := gridScale δ M b) (σ' := gridScale δ M c) (ρ := gridScale δ M a)
    (i₀ := i₀) hδ hδσb hσbσc hσcσa hσa1 hi₀
  have hgt : ((gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)) ^ ζ
      ≤ ((gridScale δ M a : ℝ) / (gridScale δ M c : ℝ)) ^ ζ' :=
    gridScale_ratio_rpow_le_of_cut hδ hδ1 M hεpos hζ0 hgap hcut hcb
  have hofReal : ENNReal.ofReal (((gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)) ^ ζ) ≤
      ENNReal.ofReal (((gridScale δ M a : ℝ) / (gridScale δ M c : ℝ)) ^ ζ') :=
    ENNReal.ofReal_le_ofReal hgt
  have hMmax : (Cvol : ENNReal) ≤ ((max 1 Cvol : NNReal) : ENNReal) :=
    ENNReal.coe_le_coe.mpr (le_max_right 1 Cvol)
  calc
    ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (gridScale δ M a) i₀)
        (fibreBodies T (gridScale δ M c))
        ((T i₀).rescale (2 * gridScale δ M a)).toConvexSpaceBody
        ≤ ((Cvol : NNReal) : ENNReal) *
            ConvexSpaceBody.frostmanConstant (fibreIndex s T δ (gridScale δ M a) i₀)
              (fibreBodies T (gridScale δ M b))
              ((T i₀).rescale (2 * gridScale δ M a)).toConvexSpaceBody := by
          simpa [Cvol] using h1
    _ ≤ ((Cvol : NNReal) : ENNReal) * ((C : ENNReal) *
          ENNReal.ofReal (((gridScale δ M a : ℝ) / (gridScale δ M b : ℝ)) ^ ζ)) :=
          mul_le_mul' le_rfl (hgood i₀ hi₀)
    _ ≤ ((C' : NNReal) : ENNReal) * (C : ENNReal) *
          ENNReal.ofReal (((gridScale δ M a : ℝ) / (gridScale δ M c : ℝ)) ^ ζ') := by
          rw [← mul_assoc]
          exact mul_le_mul' (mul_le_mul' hMmax le_rfl) hofReal
    _ = (((C' * C : NNReal) : ENNReal) *
          ENNReal.ofReal (((gridScale δ M a : ℝ) / (gridScale δ M c : ℝ)) ^ ζ')) := by
          rw [← ENNReal.coe_mul]

/- Removed: `exists_blockFrostman_truncate`.  Reaching a grid index interior to a block is now
done directly in `MultiScaleFac.frostmanConstant_gridScale_le_of_cuts` by anchor deflation
(`MultiScaleFac.anchorGraded_of_isUniformAtScale` followed by
`MultiScaleFac.frostmanConstant_fibre_le_of_card_le_sharp`), which is the same mechanism with an
honest exponent: the loss is a power of `σ_a/σ_k` that no `δ`-independent constant can absorb,
so it belongs in that lemma's conclusion rather than in a separate block-bound step. -/

/- **The block bound descends to a fine sub-block, at the cost of a `δ`-independent factor and
of the ratio by which the parent shrank.**

`BlockRestrictStep` shrinks the *fine* end of a block; this lemma shrinks the *coarse* end,
replacing the parent thickening `T_{i₀}^{(σ_a)}` by the smaller `T_{i₀}^{(σ_k)}` for `a ≤ k < b`.
It is what reaches a grid index lying strictly inside a block, and nothing else in this
development provides that direction.

The fibre index set shrinks (`fibreIndex` is monotone in the parent scale) and the anchor body
shrinks with it, so the numerator `Δ_max` only decreases; the denominator
`Δ(𝕋_{σ_b∣σ_k}, T^{(σ_k)})` is comparable to `Δ(𝕋_{σ_b∣σ_a}, T^{(σ_a)})` up to a factor controlled
by the uniformity constant `Cu`, because the number of `σ_b`-tubes in a `σ_a`-parent is the number
in a `σ_k`-parent times the `σ_k`-branching, which the packing bound compares to the volume ratio
`(σ_a/σ_k)^{n-1}`.  Hence the loss is `Cl · (σ_a/σ_k)^ζ`, the second factor being pure rebasing of
the right-hand side from `(σ_a/σ_b)^ζ` to `(σ_k/σ_b)^ζ`.

The rebasing factor is why alternative (i) of GWZ Lemma 7.7(A) needs every block to be *short*:
`(σ_a/σ_k)^ζ ≤ (σ_a/σ_b)^ζ ≤ δ^{-εζ}` holds exactly for a short block, and a factor `δ^{-εζ}` is
affordable only against the `5ε` exponent budget, never against a `δ`-independent constant.

**How the anchor-shrinking count is reached.**  Unwinding both sides through
`ConvexSpaceBody.frostmanConstant_eq_maxDensity_div`, the numerator `Δ_max` only decreases (the
`σ_k`-fibre is a subset of the `σ_a`-fibre), so the whole content is the denominator, and it
reduces to the count comparison

`|s_{σ_b∣σ_a}(i₀)| ≤ Cl · (σ_a/σ_k)^{2n} · |s_{σ_b∣σ_k}(i₀)|`.

That is exactly `MultiScaleFac.anchorGraded_of_isUniformAtScale`, applied at a grid scale below
`σ_k` — the `8`-fold inflation it leaves on the right is absorbed by the `16`-separation of the
grid.  The exponent is `2n`, not the `n-1` one might expect from the anchor volumes: the tube
parameters are direction, transverse offset and longitudinal offset, each ranging over an
interval of length `σ_a`, so `2n-1` is already forced and `2n` is what the `L¹` endpoint-metric
packing count delivers.  The surplus is harmless because the ratio `σ_a/σ_k` is at most
`δ^{-(1+ε)/N}` for a short block, so the whole loss is `δ^{-O(1/N)} = δ^{-O(ε²)}`. -/

/-- **Every unit fibre carries a fixed proportion of the family.**  A maximal `1/2`-separated
subfamily `F ⊆ s` in the `L¹` endpoint metric has dimensional cardinality, and by maximality its
unit fibres cover `s`; pigeonholing gives one anchor whose unit fibre has at least `|s|/|F|`
members, and `ComparableFibreCounts` at the grid scale `1` transfers that to *every* anchor. -/
theorem card_le_mul_card_fibreIndex_one (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ K : NNReal, 1 ≤ K ∧
      ∀ (N : ℕ), 0 < N →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 → 16 * δ ≤ 1 →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      ComparableFibreCounts s T (gridScales δ N) Cu →
      ∀ i₀ ∈ s, (s.card : ℝ) ≤ (K : ℝ) * ((fibreIndex s T δ 1 i₀).card : ℝ) := by
  classical
  set n := Module.finrank ℝ E with hn
  let netConst : NNReal := (17 : NNReal) ^ (2 * n)
  let K : NNReal := netConst * Cu
  refine ⟨K, ?_, ?_⟩
  · have hnet_one : 1 ≤ netConst := by
      dsimp [netConst]
      exact one_le_pow₀ (by norm_num : (1 : NNReal) ≤ 17)
    dsimp [K]
    exact le_trans hnet_one (le_mul_of_one_le_right' hCu)
  · intro N hN ι δ hδ hδ1 hδ16 s T hball hcmp i₀ hi₀
    have hs_nonempty : s.Nonempty := ⟨i₀, hi₀⟩
    obtain ⟨s', f, hs'sub, hf_mem, hcontain, hcard⟩ :=
      exists_tube_net s hs_nonempty T hball (θ := (1 / 2 : NNReal)) (by norm_num)
    have hδ_le_three_quarters : (δ : ℝ) + ((1 / 2 : NNReal) : ℝ) / 2 ≤ 1 := by
      have hδ16' : (16 : ℝ) * (δ : ℝ) ≤ 1 := by exact_mod_cast hδ16
      norm_num
      linarith
    have hcover : s ⊆ s'.biUnion (fun a => fibreIndex s T δ 1 a) := by
      intro i hi
      have hbody : ((T i).rescale δ).toConvexSpaceBody ≤ ((T (f i)).rescale 1).toConvexSpaceBody :=
        hcontain δ 1 hδ_le_three_quarters i hi
      have hmem : i ∈ fibreIndex s T δ 1 (f i) := by
        rw [fibreIndex_self s T 1 (f i)]
        exact Finset.mem_filter.mpr ⟨hi, by simpa using hbody⟩
      exact Finset.mem_biUnion.mpr ⟨f i, hf_mem i hi, hmem⟩
    have hcard_net : (s'.card : NNReal) ≤ netConst := by
      dsimp [netConst]
      have hcalc : ((1 + ((1 / 2 : NNReal) : ℝ) / 8) / (((1 / 2 : NNReal) : ℝ) / 8)) ^ (2 * n) =
          (17 : ℝ) ^ (2 * n) := by
        norm_num
      rw [hcalc] at hcard
      exact_mod_cast hcard
    have h1_mem : (1 : NNReal) ∈ gridScales δ N := by
      simpa using gridScale_mem_gridScales δ (N := N) (k := 0) (hk := by omega)
    have hcount : (s.card : NNReal) ≤ K * ((fibreIndex s T δ 1 i₀).card : NNReal) := by
      calc
        (s.card : NNReal) ≤ ((s'.biUnion (fun a => fibreIndex s T δ 1 a)).card : NNReal) :=
          Nat.cast_le.mpr (Finset.card_le_card hcover)
        _ ≤ ∑ a ∈ s', ((fibreIndex s T δ 1 a).card : NNReal) := by
          exact_mod_cast Finset.card_biUnion_le (s := s') (t := fun a => fibreIndex s T δ 1 a)
        _ ≤ ∑ _a ∈ s', (Cu * ((fibreIndex s T δ 1 i₀).card : NNReal)) :=
          Finset.sum_le_sum (fun a ha => hcmp (1 : NNReal) h1_mem a (hs'sub ha) i₀ hi₀)
        _ = (s'.card : NNReal) * (Cu * ((fibreIndex s T δ 1 i₀).card : NNReal)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ netConst * (Cu * ((fibreIndex s T δ 1 i₀).card : NNReal)) :=
          mul_le_mul_of_nonneg_right hcard_net zero_le
        _ = K * ((fibreIndex s T δ 1 i₀).card : NNReal) := by
          dsimp [K]; ring
    exact_mod_cast hcount

/-- **The block bound of the whole grid, with the anchor transfer at scale `1` made explicit.**
This turns the Frostman hypothesis `C_F(𝕋, B_1) ≤ δ^{-ζ}` of GWZ Lemma 7.7(A) into the block bound
on the whole grid, the starting invariant of the stopping time.  The passage from the anchor
`ConvexSpaceBody.closedUnitBall` to `T_{i₀}^{(1)}` costs a factor `C₀` depending on the ambient
dimension and on `Cu` only, never on `δ` and never on the grid length. -/
theorem blockFrostman_zero_right (Cu : NNReal) (hCu : 1 ≤ Cu) :
    ∃ C₀ : NNReal, 1 ≤ C₀ ∧
      ∀ (N : ℕ), 0 < N →
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → (δ : ℝ) ≤ 1 → 16 * δ ≤ 1 →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      UniformTubeSet s T N Cu →
      ComparableFibreCounts s T (gridScales δ N) Cu →
      ∀ ζ : ℝ, 0 ≤ ζ → ∀ B : NNReal,
      ConvexSpaceBody.frostmanConstant s (fibreBodies T δ) ConvexSpaceBody.closedUnitBall
          ≤ (B : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-ζ)) →
      BlockFrostman s T N (C₀ * B) ζ 0 N := by
  classical
  set n := Module.finrank ℝ E with hn
  obtain ⟨Knet, hKnet1, hKnet⟩ := card_le_mul_card_fibreIndex_one (E := E) Cu hCu
  let c : NNReal := Tube.le_volume.c n
  let C : NNReal := Tube.volume_le.C n
  let vBall : NNReal := (volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier).toNNReal
  let Kc : NNReal := Knet
  let C₀' : NNReal := (2 * Kc * C * C) / (c * vBall)
  let Cinfl : NNReal := (volume (Metric.closedBall (0 : E) 3)).toNNReal / c
  let C₀ : NNReal := max (Cinfl * C₀') 1
  refine ⟨C₀, le_max_right _ _, ?_⟩
  intro N hN ι δ hδ hδ1 hδ16 s T hball hu hcmp ζ hζ B hFrost i₀ hi₀
  let t : Finset ι := fibreIndex s T δ 1 i₀
  let W : ι → ConvexSpaceBody E := fibreBodies T δ
  let K : ConvexSpaceBody E := ((T i₀).rescale 1).toConvexSpaceBody
  let K' : ConvexSpaceBody E := ConvexSpaceBody.closedUnitBall
  let p : ℕ := n - 1
  let cE : ENNReal := (c : ENNReal)
  let CE : ENNReal := (C : ENNReal)
  let vBallE : ENNReal := (vBall : ENNReal)
  let δp : ENNReal := (δ : ENNReal) ^ p
  let S_s : ENNReal := ∑ i ∈ s, volume (W i).carrier
  let S_f : ENNReal := ∑ i ∈ t, volume (W i).carrier
  let Vb : ENNReal := volume K'.carrier
  let Va : ENNReal := volume K.carrier
  let D_s : ENNReal := densityIn s W K'
  let D_f : ENNReal := densityIn t W K
  let aE : ENNReal := ((c * vBall : NNReal) : ENNReal)
  let bE : ENNReal := ((2 * Kc * C * C : NNReal) : ENNReal)
  have hδ_le_one_nn : δ ≤ 1 := by exact_mod_cast hδ1
  have hvBall_pos : 0 < vBall :=
    ENNReal.toNNReal_pos (ConvexSpaceBody.closedUnitBall_volume_pos (E := E)).ne'
      (ConvexSpaceBody.closedUnitBall (E := E)).isCompact.measure_ne_top
  have hvBall_ne0 : vBall ≠ 0 := hvBall_pos.ne'
  have hvBall_ne_top : volume (ConvexSpaceBody.closedUnitBall (E := E)).carrier ≠ ⊤ :=
    (ConvexSpaceBody.closedUnitBall (E := E)).isCompact.measure_ne_top
  have hc_pos : 0 < c := Tube.le_volume.c_pos n
  have hC_pos : 0 < C := Tube.volume_le.C_pos n
  have hcvBall_ne0 : c * vBall ≠ 0 := mul_ne_zero hc_pos.ne' hvBall_ne0
  have hvBallE_le_Vb : vBallE ≤ Vb := by
    dsimp [vBallE, Vb, K', vBall]
    rw [ENNReal.coe_toNNReal hvBall_ne_top]
  have haE_pos : 0 < aE := ENNReal.coe_pos.mpr (mul_pos hc_pos hvBall_pos)
  have haE_ne_top : aE ≠ ⊤ := ENNReal.coe_ne_top
  have hbE_ne_top : bE ≠ ⊤ := ENNReal.coe_ne_top
  have hcount : (s.card : NNReal) ≤ Kc * (t.card : NNReal) := by
    dsimp [t, Kc]
    exact hKnet N hN hδ hδ1 hδ16 s T hball hcmp i₀ hi₀
  have hcountE : (s.card : ENNReal) ≤ ((Kc * (t.card : NNReal) : NNReal) : ENNReal) := by
    rw [← ENNReal.coe_natCast]
    exact ENNReal.coe_le_coe.mpr hcount
  have htu : t ⊆ s := by
    dsimp [t]
    rw [fibreIndex_self s T 1 i₀]
    exact Finset.filter_subset _ _
  have htK : ∀ i ∈ t, W i ≤ K := by
    intro i hi
    dsimp [W, K]
    change i ∈ fibreIndex s T δ 1 i₀ at hi
    rw [fibreIndex_self s T 1 i₀] at hi
    simpa using (Finset.mem_filter.mp hi).2
  have huK' : ∀ i ∈ s, W i ≤ K' := by
    intro i hi
    dsimp [W, K']
    rw [fibreBodies_self, ← SetLike.coe_subset_coe]
    exact hball i hi
  have hdt : 0 < D_f := densityIn_fibre_pos hδ hδ_le_one_nn hi₀
  have hdu : 0 < D_s := by
    dsimp [D_s]
    rw [densityIn_pos_iff s W K']
    refine ⟨i₀, hi₀, ?_, huK' i₀ hi₀⟩
    exact lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.coe_pos.mpr hc_pos).ne'
      (ENNReal.pow_pos (ENNReal.coe_pos.mpr hδ) (n - 1)).ne')
      (Tube.le_volume ((T i₀).rescale δ))
  have hD_s_eq : D_s = S_s / Vb := by
    dsimp [D_s, S_s, Vb]
    rw [densityIn_of_all_le huK']
  have hD_f_eq : D_f = S_f / Va := by
    dsimp [D_f, S_f, Va]
    rw [densityIn_of_all_le htK]
  have hS_s_le : S_s ≤ ((Kc * (t.card : NNReal) * C : NNReal) : ENNReal) * δp := by
    have hvol : ∀ i ∈ s, volume ((T i).rescale δ).carrier ≤ CE * δp :=
      fun i _ => Tube.volume_le hδ1 ((T i).rescale δ)
    have hsum : S_s ≤ (s.card : ENNReal) * (CE * δp) := by
      dsimp [S_s, W]
      rw [← nsmul_eq_mul]
      exact Finset.sum_le_card_nsmul s _ (CE * δp) hvol
    calc
      S_s ≤ (s.card : ENNReal) * (CE * δp) := hsum
      _ ≤ ((Kc * (t.card : NNReal) : NNReal) : ENNReal) * (CE * δp) := mul_le_mul' hcountE le_rfl
      _ = ((Kc * (t.card : NNReal) * C : NNReal) : ENNReal) * δp := by
        simp only [CE, ENNReal.coe_mul, mul_assoc]
  have hS_f_ge : (((t.card : NNReal) * c : NNReal) : ENNReal) * δp ≤ S_f := by
    have hvol : ∀ i ∈ t, (cE * δp) ≤ volume ((T i).rescale δ).carrier :=
      fun i _ => Tube.le_volume ((T i).rescale δ)
    dsimp [S_f, W]
    calc
      (((t.card : NNReal) * c : NNReal) : ENNReal) * δp = (t.card : ENNReal) * (cE * δp) := by
        simp only [cE, ENNReal.coe_mul, ENNReal.coe_natCast, mul_assoc]
      _ = t.card • (cE * δp) := (nsmul_eq_mul _ _).symm
      _ ≤ ∑ i ∈ t, volume ((T i).rescale δ).carrier :=
        Finset.card_nsmul_le_sum t _ (cE * δp) hvol
  have hVa_le : Va ≤ ((2 * C : NNReal) : ENNReal) := by
    dsimp [Va, K]
    calc
      Va ≤ (C : ENNReal) := by
        simpa only [C, ENNReal.coe_one, one_pow, mul_one] using
          Tube.volume_le (le_rfl : (1 : NNReal) ≤ 1) ((T i₀).rescale 1)
      _ ≤ ((2 * C : NNReal) : ENNReal) :=
        ENNReal.coe_le_coe.mpr (le_mul_of_one_le_left (α := NNReal) zero_le one_le_two)
  have hVa_pos : 0 < Va :=
    lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.coe_pos.mpr hc_pos).ne'
      (ENNReal.pow_pos (ENNReal.coe_pos.mpr one_pos) (n - 1)).ne')
      (Tube.le_volume ((T i₀).rescale 1))
  have hVa_ne0 : Va ≠ 0 := hVa_pos.ne'
  have hVa_ne_top : Va ≠ ⊤ := ((T i₀).rescale 1).isCompact.measure_lt_top.ne
  have hVb_ne0 : Vb ≠ 0 := (ConvexSpaceBody.closedUnitBall_volume_pos (E := E)).ne'
  have hVb_ne_top : Vb ≠ ⊤ := hvBall_ne_top
  have hband' : aE * S_s * Va ≤ bE * S_f * Vb := by
    calc
      aE * S_s * Va ≤ aE * ((((Kc * (t.card : NNReal) * C : NNReal) : ENNReal) * δp))
          * ((2 * C : NNReal) : ENNReal) := mul_le_mul' (mul_le_mul' le_rfl hS_s_le) hVa_le
      _ = ((c * vBall * Kc * (t.card : NNReal) * C * (2 * C) : NNReal) : ENNReal) * δp := by
          simp only [aE, ENNReal.coe_mul]; ring
      _ = bE * ((((t.card : NNReal) * c : NNReal) : ENNReal) * δp) * vBallE := by
          simp only [bE, vBallE, ENNReal.coe_mul]; ring
      _ ≤ bE * S_f * Vb := mul_le_mul' (mul_le_mul' le_rfl hS_f_ge) hvBallE_le_Vb
  have hband : aE * D_s ≤ bE * D_f := by
    rw [hD_s_eq, hD_f_eq]
    simp only [← mul_div_assoc]
    rw [ENNReal.le_div_iff_mul_le (Or.inl hVa_ne0) (Or.inl hVa_ne_top)]
    have hreassoc : aE * S_s / Vb * Va = aE * S_s * Va / Vb := by
      simp only [div_eq_mul_inv]; ring
    rw [hreassoc, ENNReal.div_le_iff hVb_ne0 hVb_ne_top]
    exact hband'
  have hfr : aE * ConvexSpaceBody.frostmanConstant t W K
      ≤ bE * ConvexSpaceBody.frostmanConstant s W K' :=
    frostmanConstant_le_of_densityIn_band (ι' := ι) (t := t) (u := s)
      (W := W) (K := K) (K' := K') (a := aE) (b := bE)
      htu htK huK' haE_pos haE_ne_top hbE_ne_top hdt hdu hband
  have hcoediv : bE / aE = (C₀' : ENNReal) := by
    dsimp only [bE, aE, C₀']
    rw [← ENNReal.coe_div hcvBall_ne0]
  have hC₀'le : Cinfl * C₀' ≤ C₀ := le_max_left _ _
  have h2 : ConvexSpaceBody.frostmanConstant t W K
      ≤ ((C₀' * B : NNReal) : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-ζ)) := by
    calc
      ConvexSpaceBody.frostmanConstant t W K
          ≤ (bE * ConvexSpaceBody.frostmanConstant s W K') / aE := by
            rw [ENNReal.le_div_iff_mul_le (Or.inl haE_pos.ne') (Or.inl haE_ne_top)]
            rwa [mul_comm]
      _ = (C₀' : ENNReal) * ConvexSpaceBody.frostmanConstant s W K' := by
            rw [← hcoediv, div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
      _ ≤ (C₀' : ENNReal) * ((B : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-ζ))) :=
        mul_le_mul' le_rfl hFrost
      _ = ((C₀' * B : NNReal) : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-ζ)) := by
        simp only [ENNReal.coe_mul, mul_assoc]
  set K₂ : ConvexSpaceBody E := ((T i₀).rescale (2 * 1)).toConvexSpaceBody with hK₂
  have hKK₂ : K ≤ K₂ := by
    simpa [K, K₂] using
      (Tube.rescale_le_rescale_of_radius_le (T i₀) (by norm_num : (1 : NNReal) ≤ 2 * 1))
  have hmemK₂ : ∀ i ∈ t, W i ≤ K₂ := fun i hi => le_trans (htK i hi) hKK₂
  have hvol2 : volume K₂.carrier ≤ (Cinfl : ENNReal) * volume K.carrier := by
    have hK₂_sub : K₂.carrier ⊆ Metric.closedBall (0 : E) 3 := by
      have hδ_le_21 : δ ≤ 2 * 1 := le_trans hδ_le_one_nn (by norm_num : (1 : NNReal) ≤ 2 * 1)
      dsimp [K₂]
      calc
        ((T i₀).rescale (2 * 1)).carrier
            = Metric.cthickening ((2 * 1 - δ : NNReal) : ℝ) (T i₀).carrier := by
              have h_eq := (T i₀).cthickening_carrier (2 * 1 - δ)
              rw [add_tsub_cancel_of_le hδ_le_21] at h_eq
              rw [← h_eq]
        _ ⊆ Metric.cthickening ((2 * 1 - δ : NNReal) : ℝ) (Metric.closedBall (0 : E) 1) :=
              Metric.cthickening_subset_of_subset _ (hball i₀ hi₀)
        _ = Metric.closedBall (0 : E) (((2 * 1 - δ : NNReal) : ℝ) + 1) := by
              rw [cthickening_closedBall (2 * 1 - δ : NNReal).coe_nonneg zero_le_one (0 : E)]
        _ ⊆ Metric.closedBall (0 : E) 3 := by
              refine Metric.closedBall_subset_closedBall ?_
              have htsub : (2 * 1 - δ : NNReal) ≤ (2 : NNReal) := by simp
              have hco : ((2 * 1 - δ : NNReal) : ℝ) ≤ (2 : ℝ) := by exact_mod_cast htsub
              linarith
    have hc_le_Va : (c : ENNReal) ≤ volume K.carrier := by
      dsimp [K]
      simpa only [c, ENNReal.coe_one, one_pow, mul_one] using
        Tube.le_volume ((T i₀).rescale 1)
    calc
      volume K₂.carrier ≤ volume (Metric.closedBall (0 : E) 3) := MeasureTheory.measure_mono hK₂_sub
      _ = (Cinfl : ENNReal) * (c : ENNReal) := by
        dsimp [Cinfl]
        rw [ENNReal.coe_div hc_pos.ne',
          ENNReal.coe_toNNReal MeasureTheory.measure_closedBall_lt_top.ne,
          ENNReal.div_mul_cancel (ENNReal.coe_pos.mpr hc_pos).ne' ENNReal.coe_ne_top]
      _ ≤ (Cinfl : ENNReal) * volume K.carrier := mul_le_mul' le_rfl hc_le_Va
  have h3 : ConvexSpaceBody.frostmanConstant t W K₂
      ≤ ((C₀ * B : NNReal) : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-ζ)) := by
    calc
      ConvexSpaceBody.frostmanConstant t W K₂
          ≤ (Cinfl : ENNReal) * ConvexSpaceBody.frostmanConstant t W K :=
            frostmanConstant_mono_anchor htK hmemK₂ hvol2 ENNReal.coe_ne_top
      _ ≤ (Cinfl : ENNReal) * (((C₀' * B : NNReal) : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-ζ))) :=
        mul_le_mul' le_rfl h2
      _ = ((Cinfl * C₀' * B : NNReal) : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-ζ)) := by
        simp only [ENNReal.coe_mul, mul_assoc]
      _ ≤ ((C₀ * B : NNReal) : ENNReal) * ENNReal.ofReal ((δ : ℝ) ^ (-ζ)) :=
        mul_le_mul' (ENNReal.coe_le_coe.mpr (mul_le_mul_left hC₀'le B)) le_rfl
  have hpow : (((1 : NNReal) : ℝ) / (δ : ℝ)) ^ ζ = (δ : ℝ) ^ (-ζ) := by
    rw [NNReal.coe_one, Real.rpow_neg_eq_inv_rpow, one_div]
  dsimp only [BlockFrostmanAt]
  rw [gridScale_zero, gridScale_self δ hN, hpow]
  exact h3

end GeometryUniform

/-! ### From a cut set to the chain of scales -/

/-- Consecutive values of the order isomorphism `Fin (n+1) ≃o S` are adjacent in `S`: they are
strictly increasing and nothing of `S` lies strictly between them. -/
theorem orderIsoOfFin_castSucc_lt_succ {S : Finset ℕ} {n : ℕ} (hcard : S.card = n + 1)
    (m : Fin n) :
    ((S.orderIsoOfFin hcard m.castSucc : ℕ) < (S.orderIsoOfFin hcard m.succ : ℕ)) ∧
      ∀ x ∈ S, ¬((S.orderIsoOfFin hcard m.castSucc : ℕ) < x ∧
        x < (S.orderIsoOfFin hcard m.succ : ℕ)) := by
  constructor
  · simp
  · intro x hx hlt
    let j : Fin (n + 1) := (S.orderIsoOfFin hcard).symm ⟨x, hx⟩
    have huS : (S.orderIsoOfFin hcard m.castSucc : S) < (⟨x, hx⟩ : S) := hlt.1
    have hj1 : m.castSucc < j := by
      simpa [j] using (S.orderIsoOfFin hcard).symm.lt_iff_lt.mpr huS
    have hvS : (⟨x, hx⟩ : S) < (S.orderIsoOfFin hcard m.succ : S) := hlt.2
    have hj2 : j < m.succ := by
      simpa [j] using (S.orderIsoOfFin hcard).symm.lt_iff_lt.mpr hvS
    have hj3 : ¬ (m.castSucc < j ∧ j < m.succ) := by
      intro hb
      have hb1 : (m.castSucc : ℕ) < (j : ℕ) := (Fin.lt_def).mp hb.1
      have hb2 : (j : ℕ) < (m.succ : ℕ) := (Fin.lt_def).mp hb.2
      have h1 : m.val < (j : ℕ) := by
        simpa [Fin.val_castSucc] using hb1
      have h2 : (j : ℕ) < m.val + 1 := by
        simpa [Fin.val_succ] using hb2
      omega
    exact hj3 ⟨hj1, hj2⟩

/-- The smallest element of a cut set containing `0` is `0`. -/
theorem orderIsoOfFin_zero_eq {S : Finset ℕ} {n : ℕ} (hcard : S.card = n + 1) (h0 : 0 ∈ S) :
    (S.orderIsoOfFin hcard 0 : ℕ) = 0 := by
  let e : Fin (n + 1) ≃o (S : Set ℕ) := S.orderIsoOfFin hcard
  let j : Fin (n + 1) := e.symm ⟨0, h0⟩
  have hzero : (e j : ℕ) = 0 := by
    change ((e (e.symm ⟨0, h0⟩) : (S : Set ℕ)) : ℕ) = 0
    rw [OrderIso.apply_symm_apply]
  have hle : (e 0 : ℕ) ≤ (e j : ℕ) := by
    exact (OrderIso.le_iff_le e).mpr (Fin.zero_le j)
  rw [hzero] at hle
  exact le_antisymm hle (Nat.zero_le _)

/-- The largest element of a cut set inside `[0,N]` containing `N` is `N`. -/
theorem orderIsoOfFin_last_eq {S : Finset ℕ} {n N : ℕ} (hcard : S.card = n + 1) (hN : N ∈ S)
    (hsub : S ⊆ Finset.range (N + 1)) :
    (S.orderIsoOfFin hcard (Fin.last n) : ℕ) = N := by
  let e : Fin (n + 1) ≃o (S : Set ℕ) := S.orderIsoOfFin hcard
  let j : Fin (n + 1) := e.symm ⟨N, hN⟩
  have hN_val : (e j : ℕ) = N := by
    change ((e (e.symm ⟨N, hN⟩) : (S : Set ℕ)) : ℕ) = N
    rw [OrderIso.apply_symm_apply]
  have hle_sub : (e j : ℕ) ≤ (e (Fin.last n) : ℕ) := by
    exact (OrderIso.le_iff_le e).mpr (Fin.le_last j)
  rw [hN_val] at hle_sub
  have hv : (e (Fin.last n) : ℕ) ∈ S := (e (Fin.last n)).property
  have hvrange : (e (Fin.last n) : ℕ) ∈ Finset.range (N + 1) := hsub hv
  have hupper : (e (Fin.last n) : ℕ) ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hvrange)
  exact le_antisymm hupper hle_sub

/-- Every element of a cut set inside `[0,N]` is at most `N`. -/
theorem orderIsoOfFin_le {S : Finset ℕ} {n N : ℕ} (hcard : S.card = n + 1)
    (hsub : S ⊆ Finset.range (N + 1)) (k : Fin (n + 1)) :
    (S.orderIsoOfFin hcard k : ℕ) ≤ N := by
  have hv : (S.orderIsoOfFin hcard k : ℕ) ∈ S :=
    (S.orderIsoOfFin hcard k).property
  have hvrange : (S.orderIsoOfFin hcard k : ℕ) ∈ Finset.range (N + 1) := hsub hv
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hvrange)

/-- **The chain of scales attached to a cut set.**  Reading the cut set `S` in increasing order
and applying `gridScale` turns it into the decreasing chain `1 = σ₀ ≥ σ₁ ≥ … ≥ σ_{J+2} = δ`
that `MultiScaleFac.frostmanConstant_fibre_le_prod` consumes. -/
noncomputable def cutChain (δ : NNReal) (N J : ℕ) (S : Finset ℕ) (hcard : S.card = J + 3) :
    Fin (J + 3) → NNReal :=
  fun k => gridScale δ N (S.orderIsoOfFin hcard k)

/-- Unfolding `cutChain`: the chain is the grid read along the increasing enumeration of `S`. -/
theorem cutChain_apply (δ : NNReal) (N J : ℕ) (S : Finset ℕ) (hcard : S.card = J + 3)
    (k : Fin (J + 3)) :
    cutChain δ N J S hcard k = gridScale δ N (S.orderIsoOfFin hcard k) := rfl

/-! ### Reindexing a cut set as a chain

`MultiScaleFac.exists_maximal_cuts` returns a cut set with `S.card = m + 2`, whereas `cutChain`
and `MultiScaleFac.frostmanConstant_fibre_le_prod_of_cuts` are indexed by `Fin (J + 3)`.  The two
match with `J = m - 1`, which needs `1 ≤ m`; the degenerate case `m = 0` is the two-element cut
set `S = {0, N}`, which is handled by the long-block alternative instead (see
`Kakeya.MultiScaleFac.Assembly`).  The next three lemmas are the whole bridge. -/

/-! ### Restricting a cut set to reach an interior cut scale

`frostmanConstant_fibre_le_prod_of_cuts` only ever bounds the fibre Frostman constant at the
*second* scale of the chain, `cutChain δ N J S hcard 1`, whereas
`Kakeya.MultiScaleFac.Assembly.frostmanConstant_cutScale_le_of_cuts` needs it at an arbitrary cut
index `k ∈ S`.  The bridge is to run the chain not on `S` but on `restrictCuts S k`: discarding
every cut strictly below `k` makes `k` itself the second element, so the chain's index `1` is
`σ_k`, while the blocks that survive are exactly the adjacent blocks of `S` lying above `k` and
therefore still carry the block bound.  The discarded part collapses into the single gap
`(0, k)`, which costs nothing because `MultiScaleFac.frostmanConstant_fibre_le_prod` requires no
Frostman hypothesis on its `m = 0` gap (only `1 ≤ X 0`).

This is what makes the *sharp* exponent `(σ_k/δ)^ζ` of `frostmanConstant_cutScale_le_of_cuts`
reachable: taking `X 0 = 1` and `X m = (σ_m/σ_{m+1})^ζ` for `m ≠ 0` telescopes to `(σ_k/δ)^ζ`
rather than to `(1/δ)^ζ`. -/

/-- **The cut set restricted to the scales at or below `k`.**  Discard every cut strictly
between `0` and `k`, keeping `0` as the mandatory coarse endpoint of the chain. -/
def restrictCuts (S : Finset ℕ) (k : ℕ) : Finset ℕ := insert 0 (S.filter (fun x => k ≤ x))

/-- The restricted cut set still contains the coarse endpoint `0`. -/
theorem zero_mem_restrictCuts (S : Finset ℕ) (k : ℕ) : 0 ∈ restrictCuts S k :=
  Finset.mem_insert_self _ _

/-- The restricted cut set still contains the fine endpoint `N`. -/
theorem mem_restrictCuts_of_le {S : Finset ℕ} {k N : ℕ} (hN : N ∈ S) (hkN : k ≤ N) :
    N ∈ restrictCuts S k :=
  Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hN, hkN⟩)

/-- The restricted cut set contains the index it was restricted at. -/
private theorem mem_restrictCuts_self {S : Finset ℕ} {k : ℕ} (hk : k ∈ S) :
    k ∈ restrictCuts S k :=
  Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hk, le_rfl⟩)

/-- The restricted cut set still lies inside `[0,N]`. -/
theorem restrictCuts_subset_range {S : Finset ℕ} {k N : ℕ} (hsub : S ⊆ Finset.range (N + 1)) :
    restrictCuts S k ⊆ Finset.range (N + 1) := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx'
  · exact Finset.mem_range.mpr (Nat.succ_pos N)
  · exact hsub (Finset.mem_filter.mp hx').1

/-- **`k` is the second element of the restricted cut set.**  Everything of `restrictCuts S k`
other than `0` is at least `k`, so nothing lies strictly between `0` and `k`; together with
`mem_restrictCuts_self` this is what puts `σ_k` at chain index `1`. -/
private theorem adjacent_zero_restrictCuts (S : Finset ℕ) (k : ℕ) :
    ∀ x ∈ restrictCuts S k, ¬(0 < x ∧ x < k) := by
  intro x hx hlt
  rcases Finset.mem_insert.mp hx with rfl | hx'
  · exact absurd hlt.1 (lt_irrefl 0)
  · exact absurd (Finset.mem_filter.mp hx').2 (not_le.mpr hlt.2)

/-- **Adjacency above `k` is inherited from the original cut set.**  A pair `a < b` of the
restricted cut set with `k ≤ a` and no restricted cut in between is an adjacent pair of `S` itself,
so the block bound carried by `S` applies to it verbatim.  The hypothesis `0 < k` is needed because
the artificial element `0` of `restrictCuts S k` need not belong to `S`. -/
theorem adjacent_of_adjacent_restrictCuts {S : Finset ℕ} {k a b : ℕ} (hk0 : 0 < k)
    (ha : a ∈ restrictCuts S k) (hb : b ∈ restrictCuts S k) (hka : k ≤ a) (hab : a < b)
    (hadj : ∀ x ∈ restrictCuts S k, ¬(a < x ∧ x < b)) :
    a ∈ S ∧ b ∈ S ∧ ∀ x ∈ S, ¬(a < x ∧ x < b) := by
  have h0a : 0 < a := lt_of_lt_of_le hk0 hka
  have ha_ne0 : a ≠ 0 := ne_of_gt h0a
  have haS : a ∈ S := by
    rcases Finset.mem_insert.mp ha with ha0 | haf
    · exact False.elim (ha_ne0 ha0)
    · exact (Finset.mem_filter.mp haf).1
  have h0b : 0 < b := lt_trans h0a hab
  have hb_ne0 : b ≠ 0 := ne_of_gt h0b
  have hbS : b ∈ S := by
    rcases Finset.mem_insert.mp hb with hb0 | hbf
    · exact False.elim (hb_ne0 hb0)
    · exact (Finset.mem_filter.mp hbf).1
  refine ⟨haS, hbS, ?_⟩
  intro x hxS hlt
  have hxR : x ∈ restrictCuts S k :=
    Finset.mem_insert_of_mem
      (Finset.mem_filter.mpr ⟨hxS, le_of_lt (lt_of_le_of_lt hka hlt.1)⟩)
  exact hadj x hxR hlt

/-- **Cardinality of the restricted cut set.**  It is one more than the number of cuts at or
above `k`.  Combined with `0 < k` and `k < N` this is what supplies the `J + 3 ≥ 3` scales that
`MultiScaleFac.frostmanConstant_fibre_le_prod` demands. -/
theorem card_restrictCuts {S : Finset ℕ} {k : ℕ} (hk0 : 0 < k) :
    (restrictCuts S k).card = (S.filter (fun x => k ≤ x)).card + 1 := by
  rw [restrictCuts]
  exact Finset.card_insert_of_notMem (by
    intro h
    have hk : k ≤ 0 := (Finset.mem_filter.mp h).2
    omega)

/-- **The chain of the restricted cut set has `σ_k` at index `1`.**  This is the statement that
lets `frostmanConstant_fibre_le_prod_of_cuts` be read as a bound at the cut scale `σ_k`. -/
theorem cutChain_restrictCuts_one (δ : NNReal) (N J : ℕ) {S : Finset ℕ} {k : ℕ} (hk : k ∈ S)
    (hk0 : 0 < k) (hcard : (restrictCuts S k).card = J + 3) :
    cutChain δ N J (restrictCuts S k) hcard 1 = gridScale δ N k := by
  rw [cutChain_apply]
  congr 1
  let R := restrictCuts S k
  let f : Fin (J + 3) ≃o R := R.orderIsoOfFin hcard
  have hf0 : (f 0 : ℕ) = 0 := by
    simpa [f, R] using orderIsoOfFin_zero_eq (n := J + 2) hcard (zero_mem_restrictCuts S k)
  let j : Fin (J + 3) := f.symm ⟨k, mem_restrictCuts_self hk⟩
  have hf_j : (f j : ℕ) = k := by
    simp [j]
  have hj0 : j ≠ 0 := by
    intro h0j
    have hk0' : k = 0 := by
      calc
        k = (f j : ℕ) := hf_j.symm
        _ = (f 0 : ℕ) := by rw [h0j]
        _ = 0 := hf0
    exact (Nat.ne_of_gt hk0) hk0'
  have hjval : 0 < (j : ℕ) := by
    exact Nat.pos_of_ne_zero (by
      intro hj0n
      apply hj0
      exact Fin.ext (by simpa using hj0n))
  have h1j : (1 : Fin (J + 3)) ≤ j := Fin.one_le_of_ne_zero hj0
  have hfle : (f 1 : ℕ) ≤ (f j : ℕ) := by
    simpa using (show f (1 : Fin (J + 3)) ≤ f j from (f.le_iff_le).mpr h1j)
  have hfl : (f 1 : ℕ) ≤ k := by
    calc
      (f 1 : ℕ) ≤ (f j : ℕ) := hfle
      _ = k := hf_j
  have hv1 : ((1 : Fin (J + 3)) : ℕ) = 1 := by
    rw [Fin.val_one' (J + 3)]
    exact Nat.mod_eq_of_lt (by omega : (1 : ℕ) < J + 3)
  have hone : (1 : Fin (J + 3)) ≠ 0 := by
    intro h
    have hv0 : ((0 : Fin (J + 3)) : ℕ) = 0 := by simp
    have hv := congrArg (fun z : Fin (J + 3) => (z : ℕ)) h
    have : (1 : ℕ) = 0 := by
      calc
        (1 : ℕ) = ((1 : Fin (J + 3)) : ℕ) := hv1.symm
        _ = ((0 : Fin (J + 3)) : ℕ) := hv
        _ = 0 := hv0
    omega
  have hf1ne0 : (f 1 : ℕ) ≠ 0 := by
    intro hz
    have hz' : (f 1 : ℕ) = (f 0 : ℕ) := by simpa [hf0] using hz
    have hfeq : f 1 = f 0 := Subtype.ext hz'
    have h10 : (1 : Fin (J + 3)) = 0 := f.injective hfeq
    exact hone h10
  have hf1gt : 0 < (f 1 : ℕ) := Nat.pos_of_ne_zero hf1ne0
  have hadj := adjacent_zero_restrictCuts S k ((f 1 : R) : ℕ)
  have hmemR : ((f 1 : R) : ℕ) ∈ R := (f 1 : R).2
  have hnot : ¬(0 < ((f 1 : R) : ℕ) ∧ ((f 1 : R) : ℕ) < k) := hadj hmemR
  have hk_le : k ≤ (f 1 : ℕ) := by
    by_contra h
    have hlt : (f 1 : ℕ) < k := by omega
    exact hnot ⟨hf1gt, hlt⟩
  exact (le_antisymm hfl hk_le : (f 1 : ℕ) = k)

/-- The chain starts at the coarse scale `1`. -/
theorem cutChain_zero {δ : NNReal} {N J : ℕ} {S : Finset ℕ} (hcard : S.card = J + 3)
    (h0 : 0 ∈ S) : cutChain δ N J S hcard 0 = 1 := by
  rw [cutChain_apply, orderIsoOfFin_zero_eq hcard h0]
  simp

/-- The chain ends at the fine scale `δ`. -/
theorem cutChain_last {δ : NNReal} {N J : ℕ} {S : Finset ℕ} (hcard : S.card = J + 3)
    (hN : 0 < N) (hNS : N ∈ S) (hsub : S ⊆ Finset.range (N + 1)) :
    cutChain δ N J S hcard (Fin.last (J + 2)) = δ := by
  rw [cutChain_apply, orderIsoOfFin_last_eq hcard hNS hsub]
  exact gridScale_self δ hN

/-- The chain is decreasing. -/
theorem cutChain_antitone {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N J : ℕ} {S : Finset ℕ}
    (hcard : S.card = J + 3) : Antitone (cutChain δ N J S hcard) := by
  intro x y hxy
  rw [cutChain_apply, cutChain_apply]
  have hkl : (S.orderIsoOfFin hcard x : ℕ) ≤ (S.orderIsoOfFin hcard y : ℕ) := by
    change (S.orderIsoOfFin hcard x : {t // t ∈ S}) ≤ (S.orderIsoOfFin hcard y : {t // t ∈ S})
    exact (S.orderIsoOfFin hcard).le_iff_le.2 hxy
  exact gridScale_antitone hδ hδ1 N hkl

/-- Consecutive scales of the chain are `16`-separated, the gap hypothesis of
`MultiScaleFac.frostmanConstant_fibre_le_prod`. -/
theorem cutChain_gap {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {N J : ℕ}
    (hδ0 : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) {S : Finset ℕ} (hcard : S.card = J + 3)
    (hsub : S ⊆ Finset.range (N + 1)) (m : Fin (J + 2)) :
    16 * cutChain δ N J S hcard m.succ ≤ cutChain δ N J S hcard m.castSucc := by
  rw [cutChain_apply, cutChain_apply]
  exact sixteen_mul_gridScale_le hδ hδ1 hδ0
    (orderIsoOfFin_castSucc_lt_succ hcard m).1
    (orderIsoOfFin_le hcard hsub m.succ)

/-- Every scale of the chain is a grid scale, so the uniformity hypotheses of GWZ Lemma 7.7(A)
project onto the chain. -/
theorem cutChain_mem_gridScales {δ : NNReal} {N J : ℕ} {S : Finset ℕ} (hcard : S.card = J + 3)
    (hsub : S ⊆ Finset.range (N + 1)) (k : Fin (J + 3)) :
    cutChain δ N J S hcard k ∈ gridScales δ N := by
  rw [cutChain_apply]
  exact gridScale_mem_gridScales δ (orderIsoOfFin_le hcard hsub k)

/-- The per-gap factors of the product bound: `X m = (σ_m / σ_{m+1})^ζ`. -/
noncomputable def cutChainFactor (δ : NNReal) (N J : ℕ) (S : Finset ℕ) (hcard : S.card = J + 3)
    (ζ : ℝ) : Fin (J + 2) → ENNReal :=
  fun m => ENNReal.ofReal (((cutChain δ N J S hcard m.castSucc : ℝ) /
    (cutChain δ N J S hcard m.succ : ℝ)) ^ ζ)

/-- The per-gap factors are finite. -/
theorem cutChainFactor_ne_top (δ : NNReal) (N J : ℕ) (S : Finset ℕ) (hcard : S.card = J + 3)
    (ζ : ℝ) (m : Fin (J + 2)) : cutChainFactor δ N J S hcard ζ m ≠ ⊤ := by
  unfold cutChainFactor
  exact ENNReal.ofReal_ne_top

section Package

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- **A cut chain is a subchain of the grid, bundle-side.**  Since `cutChain δ N J S hcard` is
`gridScale δ N ∘ S.orderIsoOfFin hcard`, `ChainUniformTubeSet.restrict` along that increasing
enumeration turns a bundled grid hierarchy into a bundled hierarchy along the cut chain, clamped at
the last chain index by `MultiScaleFac.finChain`. -/
noncomputable def chainUniformCutChain {ι : Type u} {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N J : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T N Cu)
    {S : Finset ℕ} (hcard : S.card = J + 3) (hsub : S ⊆ Finset.range (N + 1)) :
    ChainUniformTubeSet s T (J + 2) (finChain (cutChain δ N J S hcard)) Cu := by
  classical
  have hlt : ∀ m : ℕ, min m (J + 2) < J + 3 := fun m => by omega
  have hcmono : ∀ m, m + 1 ≤ J + 2 →
      (S.orderIsoOfFin hcard ⟨min m (J + 2), hlt m⟩ : ℕ)
        ≤ (S.orderIsoOfFin hcard ⟨min (m + 1) (J + 2), hlt (m + 1)⟩ : ℕ) := by
    intro m hm
    have hle : (⟨min m (J + 2), hlt m⟩ : Fin (J + 3))
        ≤ ⟨min (m + 1) (J + 2), hlt (m + 1)⟩ := by
      rw [Fin.mk_le_mk]
      omega
    exact (S.orderIsoOfFin hcard).monotone hle
  have hcN : ∀ m, m ≤ J + 2 → (S.orderIsoOfFin hcard ⟨min m (J + 2), hlt m⟩ : ℕ) ≤ N := by
    intro m _
    exact Nat.le_of_lt_succ (Finset.mem_range.mp
      (hsub (S.orderIsoOfFin hcard ⟨min m (J + 2), hlt m⟩).property))
  exact 𝒰.toChain.restrict
    (fun m => (S.orderIsoOfFin hcard ⟨min m (J + 2), hlt m⟩ : ℕ)) (J + 2) hcmono hcN

end Package

end MultiScaleFac

end Kakeya

-- touch
