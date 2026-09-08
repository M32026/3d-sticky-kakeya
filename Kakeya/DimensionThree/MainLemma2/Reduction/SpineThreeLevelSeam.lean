/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoarseSeam

/-!
# The three-level seam, and fibre-completeness at `(p, b)`

's "cheap route", tested: **it works.**

The map proposed that the four-way split's seam need not be a new pigeonhole.
`Kakeya.ML2Core.exists_coarseParentSeam` already runs **one** pigeonhole, at the coarsest level `a`
(`Kakeya.ML2Core.exists_parentSeam`), and then *defines* the level-`b` retained set as the coarse
cell's descendants.  A three-level seam is the same single pigeonhole with **two** descendant sets,
one at the genuine parent level `p` and one at `b`.

And then the clause `0-E` was chartered to supply — retention of **complete** `(p,b)`-fibres,
source l.4443-4444 — **is true by construction and needs no mass-coupled selection**:
`Kakeya.ML2Core.threeLevelSeam_fibre_complete`.  If `k` is a retained `p`-cell and `j` is *any*
active level-`b` node whose `(p,b)`-parent is `k`, then `j`'s `(a,b)`-parent is `k`'s `(a,p)`-parent
by `Kakeya.ML2Core.coarseNode_trans`, which is in `t₀`, so `j` is retained.  The seam keeps whole
tagged thread cells because it never selected at `b` in the first place.

## Family / shading / level pair

 §SPEC.1 makes this column part of the statement.

* `Kakeya.ML2Core.coarseNode_mem_activeNodes`, `Kakeya.ML2Core.coarseNode_trans` —
  **family:** the chain cover `𝒞` on `(s, T)`, no shading; **level pairs:** `(a,b)` and the
  composite `(a,p) ∘ (p,b)`.
* `Kakeya.ML2Core.exists_threeLevelParentSeam` — **family:** `(s, T)` with the seam's translate `v`,
  no shading (the shading enters later, at the one-scale applications);
  **level triple:** `a ≤ p ≤ b`, with retained sets `t₀ ⊆ activeNodes a`, `tp ⊆ activeNodes p`,
  `t₁ ⊆ activeNodes b`.
* `Kakeya.ML2Core.threeLevelSeam_fibre_complete` — **family:** the same; **level pair:** `(p, b)`,
  which is the source's middle-factor pair (`δ̃ = ρ_b/(2ρ_p)`, l.4506) and the one `hfac` does not
  have.

**What this does NOT do.**  It does not touch `hfac`, whose seam is still at `coarseNode 𝒞 a b`;
moving that is the guarded re-cut.  It does not supply the mass-coupled fullness selection
(l.4486-4500) as a *shaded* statement — the fullness and `Δ_max` clauses of `𝕌_b` are still owed.
What it removes is the need for a **new pigeonhole** to get fibre-completeness.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section Transitivity

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → NNReal}

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The coarse parent of an active node is active.**

**Family:** `(s, T)` through the chain `𝒞`.  **Level pair:** `(a, b)`. -/
theorem coarseNode_mem_activeNodes (𝒞 : Tube.ChainCoverSystem s T N σ) {a b : ℕ}
    (hab : a ≤ b) (hbN : b ≤ N) {j : ι} (hj : j ∈ ML2Reduction.activeNodes 𝒞 b) :
    ML2Reduction.coarseNode 𝒞 a b j ∈ ML2Reduction.activeNodes 𝒞 a := by
  classical
  obtain ⟨i, hi⟩ : (Tube.coverClass s (𝒞.assign b) j).Nonempty := (Finset.mem_filter.mp hj).2
  simp only [Tube.coverClass, Finset.mem_filter] at hi
  obtain ⟨his, hij⟩ := hi
  rw [← hij, coarseNode_assign 𝒞 hab hbN his]
  exact ML2Reduction.assign_mem_activeNodes 𝒞 (hab.trans hbN) his

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Transitivity of the coarse-parent map on active nodes.**

`coarseNode 𝒞 a p ∘ coarseNode 𝒞 p b = coarseNode 𝒞 a b`, the compatibility
 calls "a short consequence of `coarseNode_assign`".  It is
what makes one pigeonhole at `a` define a *coherent* pair of descendant sets at `p` and `b`.

**Family:** `(s, T)` through `𝒞`.  **Level pairs:** `(a,p)`, `(p,b)`, `(a,b)`. -/
theorem coarseNode_trans (𝒞 : Tube.ChainCoverSystem s T N σ) {a p b : ℕ}
    (hap : a ≤ p) (hpb : p ≤ b) (hbN : b ≤ N) {j : ι}
    (hj : j ∈ ML2Reduction.activeNodes 𝒞 b) :
    ML2Reduction.coarseNode 𝒞 a p (ML2Reduction.coarseNode 𝒞 p b j)
      = ML2Reduction.coarseNode 𝒞 a b j := by
  classical
  obtain ⟨i, hi⟩ : (Tube.coverClass s (𝒞.assign b) j).Nonempty := (Finset.mem_filter.mp hj).2
  simp only [Tube.coverClass, Finset.mem_filter] at hi
  obtain ⟨his, hij⟩ := hi
  have hpN : p ≤ N := hpb.trans hbN
  rw [← hij, coarseNode_assign 𝒞 hpb hbN his, coarseNode_assign 𝒞 hap hpN his,
    coarseNode_assign 𝒞 (hap.trans hpb) hbN his]

end Transitivity

section ThreeLevel

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
/-- **The three-level seam: one pigeonhole at `a`, two descendant sets.**

`Kakeya.ML2Core.exists_coarseParentSeam` with a second descendant set at the genuine parent level
`p`, `a ≤ p ≤ b`.  The pigeonhole, the side condition `σ a ≤ 1/4` and the cardinality retention are
the coarse seam's, unchanged and unpaid-for a second time; everything at `p` and at `b` is defined
from `t₀`.

**Family/shading:** `(s, T)` with the seam's translate `v`; no shading.
**Level triple:** `a ≤ p ≤ b`.  The two `coarseNode` rows are at `(a,p)` and `(p,b)`, and their
composite is `(a,b)` by `Kakeya.ML2Core.coarseNode_trans`.

The last two clauses are the ones the map wanted and `hfac` lacks: **fibre-completeness** of the
retained sets, at `(p,b)` and at `(a,p)`. -/
theorem exists_threeLevelParentSeam :
    ∃ M : ℕ, 0 < M ∧
      ∀ {δ : NNReal} {κ : Type u} {s : Finset κ} {T : κ → Tube δ E} {N : ℕ} {σ : ℕ → NNReal}
        (𝒞 : Tube.ChainCoverSystem s T N σ) {a p b : ℕ} {Cu Bn : NNReal},
        a ≤ p → p ≤ b → b ≤ N → (σ a : ℝ) ≤ 1 / 4 →
        (∀ j ∈ 𝒞.indexSet a, ((Tube.coverClass s (𝒞.assign a) j).card : NNReal) ≤ Cu * Bn) →
        (∀ j ∈ 𝒞.indexSet a, Bn ≤ Cu * ((Tube.coverClass s (𝒞.assign a) j).card : NNReal)) →
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
        ∃ (v : E) (t₀ tp t₁ : Finset κ),
          t₀ ⊆ ML2Reduction.activeNodes 𝒞 a ∧
          tp ⊆ ML2Reduction.activeNodes 𝒞 p ∧
          t₁ ⊆ ML2Reduction.activeNodes 𝒞 b ∧
          (∀ k ∈ t₀, ((𝒞.tube a k).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (∀ k ∈ tp, ((𝒞.tube p k).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (∀ j ∈ t₁, ((𝒞.tube b j).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (∀ i ∈ ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset κ),
            ((T i).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) ∧
          (∀ k ∈ tp, ML2Reduction.coarseNode 𝒞 a p k ∈ t₀) ∧
          (∀ j ∈ t₁, ML2Reduction.coarseNode 𝒞 p b j ∈ tp) ∧
          (∀ j ∈ t₁, ML2Reduction.coarseNode 𝒞 a b j ∈ t₀) ∧
          (∀ k ∈ tp, ∀ j ∈ ML2Reduction.activeNodes 𝒞 b,
            ML2Reduction.coarseNode 𝒞 p b j = k → j ∈ t₁) ∧
          (∀ l ∈ t₀, ∀ k ∈ ML2Reduction.activeNodes 𝒞 p,
            ML2Reduction.coarseNode 𝒞 a p k = l → k ∈ tp) ∧
          (s.card : NNReal) ≤ (M : NNReal) * Cu * Cu
            * (({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset κ).card : NNReal) := by
  classical
  obtain ⟨M, hM0, hseam⟩ := exists_parentSeam (E := E)
  refine ⟨M, hM0, ?_⟩
  intro δ κ s T N σ 𝒞 a p b Cu Bn hap hpb hbN hσ4 hup hlo hball
  have hab : a ≤ b := hap.trans hpb
  have haN : a ≤ N := hab.trans hbN
  have hpN : p ≤ N := hpb.trans hbN
  obtain ⟨v, t₀, ht₀, hballt₀, hballs₀, hcard₀⟩ := hseam 𝒞 haN hσ4 hup hlo hball
  set tp : Finset κ :=
    {k ∈ ML2Reduction.activeNodes 𝒞 p | ML2Reduction.coarseNode 𝒞 a p k ∈ t₀} with htpdef
  set t₁ : Finset κ :=
    {j ∈ ML2Reduction.activeNodes 𝒞 b | ML2Reduction.coarseNode 𝒞 a b j ∈ t₀} with ht₁def
  have htpsub : tp ⊆ ML2Reduction.activeNodes 𝒞 p := Finset.filter_subset _ _
  have ht₁sub : t₁ ⊆ ML2Reduction.activeNodes 𝒞 b := Finset.filter_subset _ _
  have hcoarseP : ∀ k ∈ tp, ML2Reduction.coarseNode 𝒞 a p k ∈ t₀ :=
    fun k hk => (Finset.mem_filter.mp hk).2
  have hcoarseB : ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒞 a b j ∈ t₀ :=
    fun j hj => (Finset.mem_filter.mp hj).2
  have hstep : ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒞 p b j ∈ tp := by
    intro j hj
    refine Finset.mem_filter.mpr ⟨coarseNode_mem_activeNodes 𝒞 hpb hbN (ht₁sub hj), ?_⟩
    rw [coarseNode_trans 𝒞 hap hpb hbN (ht₁sub hj)]
    exact hcoarseB j hj
  have hsets : ({i ∈ s | 𝒞.assign b i ∈ t₁} : Finset κ)
      = ({i ∈ s | 𝒞.assign a i ∈ t₀} : Finset κ) := by
    ext i
    simp only [Finset.mem_filter, ht₁def]
    constructor
    · rintro ⟨his, _hact, hcn⟩
      rw [coarseNode_assign 𝒞 hab hbN his] at hcn
      exact ⟨his, hcn⟩
    · rintro ⟨his, hcn⟩
      refine ⟨his, ML2Reduction.assign_mem_activeNodes 𝒞 hbN his, ?_⟩
      rw [coarseNode_assign 𝒞 hab hbN his]
      exact hcn
  refine ⟨v, t₀, tp, t₁, ht₀, htpsub, ht₁sub, hballt₀, ?_, ?_, ?_, hcoarseP, hstep, hcoarseB,
    ?_, ?_, ?_⟩
  · intro k hk
    refine subset_trans ?_ (hballt₀ _ (hcoarseP k hk))
    exact Set.image_mono (ML2Reduction.tube_le_coarseNode 𝒞 hap hpN (htpsub hk))
  · intro j hj
    refine subset_trans ?_ (hballt₀ _ (hcoarseB j hj))
    exact Set.image_mono (ML2Reduction.tube_le_coarseNode 𝒞 hab hbN (ht₁sub hj))
  · rw [hsets]; exact hballs₀
  · intro k hk j hjact hjk
    refine Finset.mem_filter.mpr ⟨hjact, ?_⟩
    rw [← coarseNode_trans 𝒞 hap hpb hbN hjact, hjk]
    exact hcoarseP k hk
  · intro l hl k hkact hkl
    exact Finset.mem_filter.mpr ⟨hkact, by rw [hkl]; exact hl⟩
  · rw [hsets]; exact hcard₀

open Classical in
/-- **`0-E`, closed for the seam: the retained level-`b` set contains COMPLETE `(p,b)`-fibres.**

Source l.4443-4444, "*retain whole tagged thread cells*", at the pair the middle factor runs at.
This is the `⊆` direction  §SPEC.3(i) asked for and
 corrected — and it is **true here**, because the seam never selected at
level `b`: it selected once at `a` and took descendants.  So no mass-coupled pigeonhole is needed
for *this* clause; what remains owed of l.4486-4500 is the shaded half (`λ ≥ δ^{5η_c}`,
`Δ_max ≤ t^{-η_J}`), not the retention.

**Family:** `(s, T)` through `𝒞`; the retained sets of
`Kakeya.ML2Core.exists_threeLevelParentSeam`.  **Level pair:** `(p, b)`. -/
theorem threeLevelSeam_fibre_complete {ι : Type*} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {σ : ℕ → NNReal} (𝒞 : Tube.ChainCoverSystem s T N σ) {a p b : ℕ}
    (hap : a ≤ p) (hpb : p ≤ b) (hbN : b ≤ N) {t₀ : Finset ι} {k : ι}
    (hk : ML2Reduction.coarseNode 𝒞 a p k ∈ t₀) :
    ({j ∈ ML2Reduction.activeNodes 𝒞 b |
        ML2Reduction.coarseNode 𝒞 p b j = k} : Finset ι)
      ⊆ ({j ∈ ({j ∈ ML2Reduction.activeNodes 𝒞 b |
            ML2Reduction.coarseNode 𝒞 a b j ∈ t₀} : Finset ι) |
          ML2Reduction.coarseNode 𝒞 p b j = k} : Finset ι) := by
  classical
  intro j hj
  obtain ⟨hjact, hjk⟩ := Finset.mem_filter.mp hj
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hjact, ?_⟩, hjk⟩
  rw [← coarseNode_trans 𝒞 hap hpb hbN hjact, hjk]
  exact hk

end ThreeLevel

end Kakeya.ML2Core

end
