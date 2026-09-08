/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Thickness.ConvexSpaceBody
public import Kakeya.ChainUniform
public import Kakeya.FibreCommon
public import Kakeya.Sticky
public import Kakeya.Uniform
public import Mathlib.Tactic.Linarith.NNRealPreprocessor -- for `linarith` over `NNReal`

/-!
# Branching numbers and leaf counts

The multiscale engine `Tube.ParentBodyDensity.maxDensity_le_prod_of_uniform_at_scales` (GWZ Lemma
7.4) consumes *node-indexed* Katz–Tao data: its per-level families are the tube sets
`𝕋_{ρ_m}[T_{ρ_{m-1}}]` of GWZ Definition 2.1, which are multiplicity free.  The per-gap
Frostman hypotheses supplied by the stopping-time argument of GWZ Lemma 7.7, on the other
hand, are *leaf indexed*: they live on `fibreIndex s T σ ρ i₀`, which counts a coarse tube
once for every `δ`-tube of `s` inside it.

Passing between the two pictures is a counting problem, and the exchange rate is the
branching number `ChainUniformTubeSet.branchingN`.

The uniformity hypothesis of every counting lemma below is the bundle
`Tube.ChainUniformTubeSet s T N σ Cu` together with `1 ≤ Cu` and a level bound
`k ≤ N`; each proof consumes the per-scale reading `ChainUniformTubeSet.uniformAt`, whose constant
is `Cu ^ 2`, and that is why the constants below are powers of `Cu ^ 2` rather than of `Cu`.
This file collects the counting lemmas:

* `parent_card_mul_branchingN_le` — the incidence double count: nodes dominated by a container,
  weighted by the branching number, are `≤ (Cu²)²` times the leaves dominated by that container.
* `card_fibreIndex_le_mul_branchingN` — a *matched-scale* fibre has at most `(Cu²)² · N_k` leaves.
* `branchingN_le_mul_card_fibreIndex` — conversely `N_k ≤ Cu² ·` the leaf count of the fibre at
  the inflated scale `4 σ k`.  The factor `4` is `Tube.rescale_le_of_le`, and it is why the grid
  scales in the multiscale chain are taken `16`-separated.
* `node_card_mul_branchingN_le_mul_branchingN` — the node-count ratio across a gap:
  `#{σ_kb-nodes in a σ_ka-tube} · N_kb ≤ (Cu²)⁴ · N_ka`.
* `fibreIndex_subset_two_mul_of_member_le` — the two fibre conventions (index set fixed at the
  `δ` level versus at the member scale) differ only by doubling the anchor radius.
* `comparableFibreCounts_of_isUniformAtScale` — GWZ Definition 2.1(iii) in the thickening
  convention is a *theorem*: `|s_{τ∣σ k}(i₀)| ≤ (Cu²)³ · |s_{τ∣8 σ k}(i₁)|` for any two anchors.

together with the two scale-slop containment lemmas that every step of the node chain needs,

* `Tube.rescale_le_rescale_of_body_le` — `A ⊆ B` implies `A^{(σ)} ⊆ B^{(θ)}` once `δ_B + σ ≤ θ`;
* `node_rescale_le_node_rescale_of_shared_tube` — a fine node and a coarse node sharing a
  `δ`-tube satisfy `V_b^{(r)} ⊆ V_a^{(θ)}` once `σ_a + 4σ_b + r ≤ θ`.  This is exactly the
  chain-projection hypothesis of `Tube.ParentBodyDensity.maxDensity_le_prod_of_uniform_at_scales`
  for the node chain `tb k j := (parentTube j).rescale (2 * σ k)`;

and the convex-body thickening bound `volume_cthickening_nat_mul_le_of_ball`, which is what lets
a Frostman hypothesis be evaluated at a *fattened* test body at the cost of a dimensional
constant.
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

/-! ### Thickening a convex body that contains a ball -/

omit [Nontrivial E] in
/-- **Iterated convex-body thickening.**  If a convex compact set `K` contains a closed ball of
radius `r`, then the `(j · r)`-cthickening of `K` has volume at most `(2 ^ n) ^ j · vol K`; so
fattening a test body costs only a dimensional constant, nothing scale-dependent. -/
theorem volume_cthickening_nat_mul_le_of_ball
    (K : Set E) (hK_conv : Convex ℝ K) (hK_compact : IsCompact K)
    (p : E) {r : ℝ} (hr : 0 ≤ r) (hp : Metric.closedBall p r ⊆ K) (j : ℕ) :
    volume (Metric.cthickening ((j : ℝ) * r) K)
      ≤ (ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℝ E)) ^ j * volume K := by
  set c := ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℝ E) with hc
  induction j with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, pow_zero, one_mul]
    rw [Metric.cthickening_zero, hK_compact.isClosed.closure_eq]
  | succ k IH =>
    have hkr : (0 : ℝ) ≤ (k : ℝ) * r := mul_nonneg (Nat.cast_nonneg k) hr
    have heq : Metric.cthickening (((k + 1 : ℕ) : ℝ) * r) K
        = Metric.cthickening r (Metric.cthickening ((k : ℝ) * r) K) := by
      rw [cthickening_cthickening hr hkr]
      congr 1; push_cast; ring
    rw [heq]
    calc volume (Metric.cthickening r (Metric.cthickening ((k : ℝ) * r) K))
        ≤ c * volume (Metric.cthickening ((k : ℝ) * r) K) :=
          Kakeya.convexBody_cthickening_volume_le_2pow_of_ball _ (hK_conv.cthickening _)
            hK_compact.cthickening p hr (hp.trans (Metric.self_subset_cthickening _))
      _ ≤ c * (c ^ k * volume K) := mul_le_mul_right IH _
      _ = c ^ (k + 1) * volume K := by rw [pow_succ]; ring

/-! ### Rescaling and containment -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The node-chain projection step.**  If some `δ`-tube lies in both a fine (`σb`-scale) node
`Vb` and a coarse (`σa`-scale) node `Va`, then the `r`-rescale of `Vb` lies in the `θ`-rescale of
`Va`, provided `σa + 4 * σb + r ≤ θ`.  The geometric input is `Tube.rescale_le_of_le`. -/
theorem node_rescale_le_node_rescale_of_shared_tube
    {δ σa σb : NNReal} (Va : Tube σa E) (Vb : Tube σb E) (Tl : Tube δ E) {r θ : NNReal}
    (hδb : δ ≤ 4 * σb) (hbr : σb ≤ r) (hθ : σa + 4 * σb + r ≤ θ)
    (hib : Tl.toConvexSpaceBody ≤ Vb.toConvexSpaceBody)
    (hia : Tl.toConvexSpaceBody ≤ Va.toConvexSpaceBody) :
    (Vb.rescale r).toConvexSpaceBody ≤ (Va.rescale θ).toConvexSpaceBody := by
  have hVb_Va : Vb.toConvexSpaceBody ≤ (Va.rescale (σa + 4 * σb)).toConvexSpaceBody :=
    (Tube.rescale_le_of_le Tl Vb hib).trans
      (Tube.rescale_le_rescale_of_body_le Tl Va hδb le_rfl hia)
  refine (Tube.rescale_le_rescale_of_body_le Vb (Va.rescale (σa + 4 * σb)) hbr hθ
    hVb_Va).trans_eq ?_
  simpa using congrArg (·.toConvexSpaceBody) (Tube.rescale_rescale Va (σa + 4 * σb) θ)

/-! ### The incidence double count -/

section Branching

variable {ι : Type*} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {ρ Cu : NNReal}

/-! ### The per-scale forms of the leaf counts -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Step 1, upper bound, per-scale form.**  At a scale `ρ` at which the family is `Cu`-uniform,
the fibre `𝕋_{δ∣ρ}[i₀]` has at most `Cu² · N_ρ` leaves: bounded overlap lets at most `Cu` nodes
meet `T_{i₀}^{(ρ)}`, and each node carries at most `Cu · N_ρ` leaves. -/
theorem card_fibreIndex_le_mul_branchingN_atScale
    (h : Tube.IsUniformAtScale s T ρ Cu) (i₀ : ι) :
    ((fibreIndex s T δ ρ i₀).card : NNReal) ≤ Cu ^ 2 * h.branchingN := by
  classical
  set F : ι → Finset ι :=
    fun j => s.filter (fun i => (T i).toConvexSpaceBody ≤ (h.parentTube j).toConvexSpaceBody)
    with hF
  set P := h.parent.filter (fun j => ∃ i ∈ s,
    (T i).toConvexSpaceBody ≤ (h.parentTube j).toConvexSpaceBody ∧
    (T i).toConvexSpaceBody ≤ ((T i₀).rescale ρ).toConvexSpaceBody) with hP
  have hsub : fibreIndex s T δ ρ i₀ ⊆ P.biUnion F := by
    intro i hi
    rw [fibreIndex_self, Finset.mem_filter] at hi
    obtain ⟨j, hj, hle⟩ := h.exists_le_rescale hi.1
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, i, hi.1, hle, hi.2⟩,
      Finset.mem_filter.mpr ⟨hi.1, hle⟩⟩
  calc ((fibreIndex s T δ ρ i₀).card : NNReal)
      ≤ ((P.biUnion F).card : NNReal) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ((∑ j ∈ P, (F j).card : ℕ) : NNReal) := Nat.cast_le.mpr Finset.card_biUnion_le
    _ = ∑ j ∈ P, ((F j).card : NNReal) := Nat.cast_sum _ _
    _ ≤ ∑ j ∈ P, Cu * h.branchingN :=
        Finset.sum_le_sum fun j hj => by
          simpa only [hF, Finset.filter_congr_decidable] using
            h.card_filter_le (Finset.mem_filter.mp (hP ▸ hj)).1
    _ = (P.card : NNReal) * (Cu * h.branchingN) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Cu * (Cu * h.branchingN) :=
        mul_le_mul_left (by
          simpa only [hP, Finset.filter_congr_decidable] using
            h.boundedOverlap ((T i₀).rescale ρ)) _
    _ = Cu ^ 2 * h.branchingN := by ring

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Step 1, upper bound.**  At a chain scale `σ k` of a `Cu`-uniform hierarchy `𝒰` the fibre
`𝕋_{δ∣σ k}[i₀]` has at most `(Cu²)² · N_k` leaves.  This is
`card_fibreIndex_le_mul_branchingN_atScale` read at the per-scale reading
`ChainUniformTubeSet.uniformAt`, whose own constant is `Cu²`. -/
theorem card_fibreIndex_le_mul_branchingN {N : ℕ} {σ : ℕ → NNReal}
    (𝒰 : ChainUniformTubeSet s T N σ Cu) (hCu : 1 ≤ Cu) {k : ℕ} (hk : k ≤ N) (i₀ : ι) :
    ((fibreIndex s T δ (σ k) i₀).card : NNReal) ≤ (Cu ^ 2) ^ 2 * 𝒰.branchingN k :=
  card_fibreIndex_le_mul_branchingN_atScale (𝒰.uniformAt hCu hk) i₀

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Step 1, lower bound, per-scale form.**  The branching number at scale `ρ` is at most `Cu`
times the leaf count of the fibre at the inflated scale `4ρ`, for every `i₀ ∈ s`: the node
containing `T_{i₀}` lies inside `T_{i₀}^{(4ρ)}` and carries at least `N_ρ / Cu` leaves. -/
theorem branchingN_le_mul_card_fibreIndex_atScale
    (h : Tube.IsUniformAtScale s T ρ Cu) {i₀ : ι} (hi₀ : i₀ ∈ s) :
    h.branchingN ≤ Cu * ((fibreIndex s T δ (4 * ρ) i₀).card : NNReal) := by
  classical
  obtain ⟨j, hj, hsub⟩ := h.exists_le_rescale hi₀
  have hsub' : (h.parentTube j).toConvexSpaceBody ≤ ((T i₀).rescale (4 * ρ)).toConvexSpaceBody :=
    Tube.rescale_le_of_le (T i₀) (h.parentTube j) hsub
  have hcard : ((s.filter (fun i =>
        (T i).toConvexSpaceBody ≤ (h.parentTube j).toConvexSpaceBody)).card : NNReal)
      ≤ ((fibreIndex s T δ (4 * ρ) i₀).card : NNReal) := by
    rw [fibreIndex_self]
    refine Nat.cast_le.mpr (Finset.card_le_card fun i hi => ?_)
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.trans hsub'⟩
  exact (h.le_mul_card_filter hj).trans (mul_le_mul_right hcard Cu)

/-! ### Node counts across a gap -/

/-! ### Monotonicity and inflation of the fibre index -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Member monotonicity.**  Thinning the members can only enlarge the fibre: the index set
`s_{σ∣ρ}(i₀)` grows as the member scale `σ` decreases. -/
theorem fibreIndex_subset_of_member_le {σ σ' : NNReal} (hσ : σ' ≤ σ) (i₀ : ι) :
    fibreIndex s T σ ρ i₀ ⊆ fibreIndex s T σ' ρ i₀ := by
  classical
  intro i hi
  simp only [fibreIndex, Kakeya.familyIn, fibreBodies, Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, (Tube.rescale_le_rescale_of_radius_le (T i) hσ).trans hi.2⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Member-scale inflation: the two fibre conventions differ by a factor `2` on the anchor.**
GWZ fixes the index set of a fibre at the `δ` level and thickens its members afterwards, whereas
`fibreIndex` fixes the index set at the member scale `σ`.  The two conventions are interchangeable
at the price of doubling the *anchor* radius, and no uniformity is needed. -/
theorem fibreIndex_subset_two_mul_of_member_le {σ σ' : NNReal}
    (hδσ : δ ≤ σ) (hδσ' : δ ≤ σ') (hσ'ρ : σ' ≤ ρ) (i₀ : ι) :
    fibreIndex s T σ ρ i₀ ⊆ fibreIndex s T σ' (2 * ρ) i₀ := by
  classical
  intro i hi
  simp only [fibreIndex, Kakeya.familyIn, fibreBodies, Finset.mem_filter] at hi ⊢
  have hTi_le : (T i).toConvexSpaceBody ≤ ((T i₀).rescale ρ).toConvexSpaceBody :=
    le_trans (by simpa using Tube.rescale_le_rescale_of_radius_le (T i) hδσ) hi.2
  have hθ : ρ + σ' ≤ 2 * ρ := by linarith [hσ'ρ]
  exact ⟨hi.1, Tube.rescale_le_rescale_of_body_le (T i) ((T i₀).rescale ρ) hδσ' hθ hTi_le⟩

/-! ### Comparable thickening counts -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Comparable fibre counts at a general member scale, per-scale form.**  For a family that is
`Cu`-uniform at the single scale `ρ`, the fibre of *any* anchor `i₀` at member scale `σ` is at most
`Cu³` times the fibre of *any other* anchor `i₁ ∈ s` at the same member scale and the `8`-inflated
anchor scale.  This is GWZ Definition 2.1(iii) in the thickening convention of GWZ §7. -/
theorem comparableFibreCounts_of_isUniformAtScale_atScale {σ : NNReal}
    (h : Tube.IsUniformAtScale s T ρ Cu) (hδσ : δ ≤ σ) (hσρ : σ ≤ 4 * ρ)
    (i₀ : ι) {i₁ : ι} (hi₁ : i₁ ∈ s) :
    ((fibreIndex s T σ ρ i₀).card : NNReal)
      ≤ Cu ^ 3 * ((fibreIndex s T σ (8 * ρ) i₁).card : NNReal) := by
  classical
  have h4 : fibreIndex s T δ (4 * ρ) i₁ ⊆ fibreIndex s T σ (8 * ρ) i₁ := by
    simpa [show 2 * (4 * ρ) = 8 * ρ by ring]
      using fibreIndex_subset_two_mul_of_member_le (σ := δ) (σ' := σ) (ρ := 4 * ρ)
        le_rfl hδσ hσρ i₁
  calc
    ((fibreIndex s T σ ρ i₀).card : NNReal)
        ≤ ((fibreIndex s T δ ρ i₀).card : NNReal) :=
          Nat.cast_le.mpr (Finset.card_le_card (fibreIndex_subset_of_member_le hδσ i₀))
    _ ≤ Cu ^ 2 * h.branchingN := card_fibreIndex_le_mul_branchingN_atScale h i₀
    _ ≤ Cu ^ 2 * (Cu * ((fibreIndex s T δ (4 * ρ) i₁).card : NNReal)) :=
        mul_le_mul_right (branchingN_le_mul_card_fibreIndex_atScale h hi₁) _
    _ = Cu ^ 3 * ((fibreIndex s T δ (4 * ρ) i₁).card : NNReal) := by ring
    _ ≤ Cu ^ 3 * ((fibreIndex s T σ (8 * ρ) i₁).card : NNReal) :=
        mul_le_mul_right (Nat.cast_le.mpr (Finset.card_le_card h4)) _

end Branching

end MultiScaleFac

end Kakeya
