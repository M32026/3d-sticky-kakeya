/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.IsUniformAtScale
public import Kakeya.Density
public import Kakeya.Frostman
public import Kakeya.Shading
public import Kakeya.StickyKakeya.Lemma75.Calibration

/-!
# GWZ Lemma 7.5, part 2: the Minkowski-sum chain of translations

The outer body of `Kakeya.StickyKakeya.subStickyFrostmanLemma`: the recursive construction of the
prefix chain `R_partial : Fin (M+1) → Finset E` of accumulated translation sets, its prefix-sum
description, the genericity clause that makes the decomposition of a prefix offset unique, and the
resulting cardinality bound with its constant `Kakeya.StickyKakeya.qCardConst`.
-/

@[expose] public section

open MeasureTheory Real Metric ConvexSpaceBody
open scoped Topology
open Tube

namespace Kakeya


namespace StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

open scoped Classical in
omit [Nontrivial E] in
omit [MeasurableSpace E] [BorelSpace E] in
/-- Bridge 1 of the outer `subStickyFrostmanLemma` body: derive the `closedBall 0 4` containment for
rescaled parent tubes from leaf-`B_1` and the non-degeneracy `1 ≤ branchingN`.  A leaf witness
`i ∈ s` inside `(T j).rescale ρ` pins a point of `segment_j` within `1+ρ` of `0`, so
`segment_j ⊆ B_{2+ρ}` and the `ρ`-thickening lies in `B_{2+2ρ} ⊆ B_4` for `ρ ≤ 1`. -/
lemma subStickyFrostmanLemma.outerBody.bridge1_parentBall
    {ι : Type*} (s : Finset ι) {δ : NNReal} (T : ι → Tube δ E)
    (hT_in_unit : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (M : ℕ) (ρ : Fin (M + 1) → NNReal) (hρ_anti : StrictAnti ρ)
    (hρ_0 : ρ 0 = 1)
    (C_uniform : NNReal)
    (h_uni : (k : Fin (M + 1)) → Tube.IsUniformAtScale s T (ρ k) C_uniform)
    (hNonDegen : ∀ k : Fin (M + 1), (1 : NNReal) ≤ (h_uni k).branchingN) :
    ∀ k : Fin (M + 1), ∀ j ∈ (h_uni k).parent,
      ((h_uni k).parentTube j).carrier ⊆ Metric.closedBall (0 : E) 4 := by
  intro k j hj
  set Tpar : Tube (ρ k) E := (h_uni k).parentTube j with hTpar_def
  have hρk_le_one : (ρ k : ℝ) ≤ 1 := by
    have h_le : ρ k ≤ ρ 0 := hρ_anti.antitone (Fin.zero_le k)
    have : (ρ k : ℝ) ≤ (ρ 0 : ℝ) := by exact_mod_cast h_le
    rw [hρ_0] at this
    simpa using this
  have h_le_filter := (h_uni k).le_mul_card_filter hj
  have h_one_le : (1 : NNReal) ≤ C_uniform *
      ({ i ∈ s |
        (T i).toConvexSpaceBody ≤ Tpar.toConvexSpaceBody}.card : NNReal) :=
    (hNonDegen k).trans h_le_filter
  have h_card_pos :
      0 < { i ∈ s |
        (T i).toConvexSpaceBody ≤ Tpar.toConvexSpaceBody}.card := by
    by_contra h_neg
    have h_neg : ({ i ∈ s |
          (T i).toConvexSpaceBody ≤ Tpar.toConvexSpaceBody}.card) ≤ 0 :=
      Nat.le_zero.mpr (Nat.eq_zero_of_not_pos h_neg)
    have h_zero :
        ({ i ∈ s |
          (T i).toConvexSpaceBody ≤
            Tpar.toConvexSpaceBody}.card : NNReal) = 0 := by
      simp [Nat.le_zero.mp h_neg]
    rw [h_zero, mul_zero] at h_one_le
    exact absurd h_one_le (by norm_num)
  obtain ⟨i, hi_mem⟩ :
      Finset.Nonempty
        ({ i ∈ s | (T i).toConvexSpaceBody ≤ Tpar.toConvexSpaceBody}) :=
    Finset.card_pos.mp h_card_pos
  rw [Finset.mem_filter] at hi_mem
  obtain ⟨hi_s, hi_le⟩ := hi_mem
  have hi_subset : (T i).carrier ⊆ Tpar.carrier :=
    SetLike.coe_subset_coe.mpr hi_le
  have hTix_mem_carrier : (T i).x ∈ (T i).carrier := by
    rw [(T i).carrier_eq]
    refine Set.mem_iUnion₂.mpr ?_
    exact ⟨(T i).x, left_mem_segment ℝ (T i).x (T i).y,
      Metric.mem_closedBall_self δ.coe_nonneg⟩
  have hTix_ball : (T i).x ∈ Metric.closedBall (0 : E) 1 :=
    hT_in_unit i hi_s hTix_mem_carrier
  have hTix_norm : dist (T i).x (0 : E) ≤ 1 := by
    rw [Metric.mem_closedBall] at hTix_ball
    exact hTix_ball
  have hTix_in_Tj : (T i).x ∈ Tpar.carrier :=
    hi_subset hTix_mem_carrier
  have h_rescale_carrier :
      Tpar.carrier =
        ⋃ z ∈ segment ℝ Tpar.x Tpar.y, Metric.closedBall z (ρ k) :=
    Tpar.carrier_eq
  rw [h_rescale_carrier] at hTix_in_Tj
  obtain ⟨z₀, hz₀_seg, hz₀_dist⟩ := Set.mem_iUnion₂.mp hTix_in_Tj
  rw [Metric.mem_closedBall] at hz₀_dist
  have hz₀_norm : dist z₀ (0 : E) ≤ 1 + (ρ k : ℝ) := by
    calc dist z₀ (0 : E)
        ≤ dist z₀ (T i).x + dist (T i).x (0 : E) := dist_triangle _ _ _
      _ ≤ (ρ k : ℝ) + 1 := by
          have h1 : dist z₀ (T i).x ≤ (ρ k : ℝ) := by
            rw [dist_comm]; exact hz₀_dist
          linarith
      _ = 1 + (ρ k : ℝ) := by ring
  intro x hx
  rw [h_rescale_carrier] at hx
  obtain ⟨w, hw_seg, hw_dist⟩ := Set.mem_iUnion₂.mp hx
  rw [Metric.mem_closedBall] at hw_dist
  have hw_z₀_dist : dist w z₀ ≤ 1 := by
    rw [segment_eq_image'] at hw_seg hz₀_seg
    obtain ⟨sParam, hs_mem, hs_eq⟩ := hw_seg
    obtain ⟨tParam, ht_mem, ht_eq⟩ := hz₀_seg
    subst hs_eq
    subst ht_eq
    rw [dist_eq_norm]
    have h_eq : Tpar.x + sParam • (Tpar.y - Tpar.x)
        - (Tpar.x + tParam • (Tpar.y - Tpar.x))
        = (sParam - tParam) • (Tpar.y - Tpar.x) := by module
    rw [h_eq, norm_smul]
    rw [Set.mem_Icc] at hs_mem ht_mem
    have h_abs : |sParam - tParam| ≤ 1 := by
      rcases le_or_gt sParam tParam with h_st | h_st
      · rw [abs_of_nonpos (by linarith)]
        linarith [hs_mem.1, ht_mem.2]
      · rw [abs_of_pos (by linarith)]
        linarith [hs_mem.2, ht_mem.1]
    have h_norm_sub : ‖Tpar.y - Tpar.x‖ = 1 := by
      rw [← dist_eq_norm, dist_comm]
      exact Tpar.dist_eq_one
    rw [h_norm_sub, mul_one, Real.norm_eq_abs]
    exact h_abs
  rw [Metric.mem_closedBall]
  calc dist x (0 : E)
      ≤ dist x w + dist w (0 : E) := dist_triangle _ _ _
    _ ≤ dist x w + (dist w z₀ + dist z₀ (0 : E)) := by
        have : dist w (0 : E) ≤ dist w z₀ + dist z₀ (0 : E) := dist_triangle _ _ _
        linarith
    _ ≤ (ρ k : ℝ) + (1 + (1 + (ρ k : ℝ))) := by
        have h1 : dist x w ≤ (ρ k : ℝ) := hw_dist
        have h2 : dist w z₀ ≤ 1 := hw_z₀_dist
        have h3 : dist z₀ (0 : E) ≤ 1 + (ρ k : ℝ) := hz₀_norm
        linarith
    _ = 2 + 2 * (ρ k : ℝ) := by ring
    _ ≤ 4 := by linarith [hρk_le_one]

open scoped Classical in
omit [Nontrivial E] in
/-- Bridge 6 of the outer `subStickyFrostmanLemma` body: derive the
per-parent (bracket) Δ_max from the outer un-bracket Δ_max via
`maxDensity` monotonicity on `Finset.filter`.  The filtered family
is a subfamily of the image, so its `maxDensity` is bounded by the
image's `maxDensity` (≤ `(ρ_cs/ρ_succ)^ε` by hypothesis). -/
lemma subStickyFrostmanLemma.outerBody.bridge6_bracketDeltaMax
    {ι : Type*} (ε : ℝ) (M : ℕ) (s : Finset ι)
    {δ : NNReal} (T : ι → Tube δ E)
    (ρ : Fin (M + 1) → NNReal) (C_uniform : NNReal)
    (h_uni : (k : Fin (M + 1)) → Tube.IsUniformAtScale s T (ρ k) C_uniform)
    (hΔ_input : ∀ k : Fin M,
        Kakeya.maxDensity
            ((h_uni k.succ).parent.image
              (fun j => (h_uni k.succ).parentTube j))
            (fun u : Tube (ρ k.succ) E => u.toConvexSpaceBody)
          ≤ ENNReal.ofReal (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε)) :
    ∀ k : Fin M, ∀ _j ∈ (h_uni k.castSucc).parent,
      Kakeya.maxDensity
          (((h_uni k.succ).parent.image
              (fun i => (h_uni k.succ).parentTube i)).filter
            (fun w : Tube (ρ k.succ) E =>
              w.toConvexSpaceBody ≤
                ((h_uni k.castSucc).parentTube _j).toConvexSpaceBody))
          (fun w : Tube (ρ k.succ) E => w.toConvexSpaceBody)
        ≤ ENNReal.ofReal (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ε) := by
  intro k _j _
  exact le_trans (Kakeya.maxDensity_mono _ (Finset.filter_subset _ _))
    (hΔ_input k)

open scoped Classical in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E] in
/-- Build `R_partial : Fin (M + 1) → Finset E` recursively from the per-scale
sets `R_per : Fin M → Finset E` as the Minkowski-sum chain
`R_partial 0 = {0}`, `R_partial k.succ = (R_partial k.castSucc ×ˢ R_per k).image (· + ·)`,
together with nonemptiness of `R_partial (Fin.last M)` (under the assumption
that every `R_per k` is nonempty). -/
lemma subStickyFrostmanLemma.outerBody.buildRPartial
    (M : ℕ) (R_per : Fin M → Finset E)
    (hR_per_nonempty : ∀ k : Fin M, (R_per k).Nonempty) :
    ∃ R_partial : Fin (M + 1) → Finset E,
      R_partial 0 = {0} ∧
      (∀ k : Fin M, R_partial k.succ =
        (R_partial k.castSucc ×ˢ R_per k).image (fun p : E × E => p.1 + p.2)) ∧
      (R_partial (Fin.last M)).Nonempty := by
  classical
  set R_partial : Fin (M + 1) → Finset E :=
    Fin.induction (motive := fun _ => Finset E) ({0} : Finset E)
      (fun k acc => (acc ×ˢ R_per k).image (fun p : E × E => p.1 + p.2))
    with hR_partial
  refine ⟨R_partial, ?_, ?_, ?_⟩
  · simp [hR_partial]
  · intro k
    simp [hR_partial]
  · have h : ∀ k : Fin (M + 1), (R_partial k).Nonempty := by
      intro k
      induction k using Fin.induction with
      | zero =>
          simp [hR_partial]
      | succ j ih =>
          have hs : R_partial j.succ =
              (R_partial j.castSucc ×ˢ R_per j).image (fun p : E × E => p.1 + p.2) := by
            simp [hR_partial]
          rw [hs]
          obtain ⟨v, hv⟩ := ih
          obtain ⟨w, hw⟩ := hR_per_nonempty j
          refine ⟨v + w, ?_⟩
          exact Finset.mem_image.mpr
            ⟨(v, w), Finset.mem_product.mpr ⟨hv, hw⟩, rfl⟩
    exact h (Fin.last M)

open scoped Classical in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E] in
/-- **Prefix-sum description of the Minkowski-sum chain.**  An element of `R_partial k` is
exactly a sum `∑_{l < k} v l` of per-scale translations, one drawn from each `R_per l`
with `l < k`.  (The values of the tuple at `l ≥ k` are irrelevant, which is why the
existential quantifies over *all* of `Fin M`; this makes the statement directly usable
for the direct-sum argument, where the tail has to be completed to a full path.) -/
private lemma subStickyFrostmanLemma.outerBody.mem_RPartial_iff
    (M : ℕ) (R_per : Fin M → Finset E)
    (hR_per_nonempty : ∀ k : Fin M, (R_per k).Nonempty)
    (R_partial : Fin (M + 1) → Finset E)
    (hR_partial_zero : R_partial 0 = {0})
    (hR_partial_succ : ∀ k : Fin M, R_partial k.succ =
      (R_partial k.castSucc ×ˢ R_per k).image (fun p : E × E => p.1 + p.2))
    (k : Fin (M + 1)) (w : E) :
    w ∈ R_partial k ↔ ∃ v : Fin M → E, (∀ l : Fin M, v l ∈ R_per l) ∧
      w = ∑ l ∈ (Finset.univ : Finset (Fin M)).filter (fun l : Fin M => (l : ℕ) < (k : ℕ)),
            v l := by
  classical
  refine (Fin.induction (motive := fun k => ∀ w : E, w ∈ R_partial k ↔
    ∃ v : Fin M → E, (∀ l : Fin M, v l ∈ R_per l) ∧
      w = ∑ l ∈ (Finset.univ : Finset (Fin M)).filter
        (fun l : Fin M => (l : ℕ) < (k : ℕ)),
      v l) ?_ ?_ k) w
  · intro w
    constructor
    · intro h
      rw [hR_partial_zero] at h
      have hw : w = 0 := by simpa using h
      let v : Fin M → E := fun l => (hR_per_nonempty l).choose
      have hv_mem : ∀ l : Fin M, v l ∈ R_per l := fun l => (hR_per_nonempty l).choose_spec
      refine ⟨v, hv_mem, ?_⟩
      have hfilter_empty : (Finset.univ : Finset (Fin M)).filter
          (fun l : Fin M => (l : ℕ) < (0 : ℕ)) = ∅ := by
        ext l; simp
      simp [hw]
    · intro h
      rcases h with ⟨v, hv, hw⟩
      rw [hR_partial_zero]
      have hw' : w = 0 := by simpa using hw
      subst hw'
      simp
  · intro j ih w
    constructor
    · intro h
      rw [hR_partial_succ j] at h
      rcases (Finset.mem_image.1 h) with ⟨p, hp, hw⟩
      rcases Finset.mem_product.1 hp with ⟨ha, hb⟩
      rcases p with ⟨a, b⟩
      have hw' : a + b = w := by simpa using hw
      rcases (ih a).mp ha with ⟨v, hv, ha_sum⟩
      let v' := Function.update v j b
      have hv'_mem : ∀ l : Fin M, v' l ∈ R_per l := by
        intro l
        by_cases hl : l = j
        · subst hl; simp [v', hb]
        · simp [v', hl, hv l]
      have hfilter_eq : (Finset.univ : Finset (Fin M)).filter
          (fun l : Fin M => (l : ℕ) < (j.succ : ℕ)) =
          insert j ((Finset.univ : Finset (Fin M)).filter
            (fun l : Fin M => (l : ℕ) < (j.castSucc : ℕ))) := by
        ext l; simp [Fin.val_succ, Fin.val_castSucc]; omega
      have hj_not_mem : j ∉ (Finset.univ : Finset (Fin M)).filter
        (fun l : Fin M => (l : ℕ) < (j.castSucc : ℕ)) := by
        simp [Fin.val_castSucc]
      have hsum_v'_eq_v : (∑ l ∈ (Finset.univ : Finset (Fin M)).filter
          (fun l : Fin M => (l : ℕ) < (j.castSucc : ℕ)), v' l) =
          (∑ l ∈ (Finset.univ : Finset (Fin M)).filter
            (fun l : Fin M => (l : ℕ) < (j.castSucc : ℕ)), v l) := by
        refine Finset.sum_congr rfl fun l hl => ?_
        have hlj : l ≠ j := by
          intro h_eq
          have h_val_lt : (l : ℕ) < (j : ℕ) := by
            have := (Finset.mem_filter.mp hl).2
            simpa [Fin.val_castSucc] using this
          have h_val_eq : (l : ℕ) = (j : ℕ) := by
              simpa using congrArg (fun (x : Fin M) => (x : ℕ)) h_eq
          omega
        simp [v', hlj]
      refine ⟨v', hv'_mem, ?_⟩
      calc
        w = a + b := hw'.symm
        _ = (∑ l ∈ (Finset.univ : Finset (Fin M)).filter
          (fun l : Fin M => (l : ℕ) < (j.castSucc : ℕ)), v l) + b := by rw [ha_sum]
        _ = (∑ l ∈ (Finset.univ : Finset (Fin M)).filter
          (fun l : Fin M => (l : ℕ) < (j.castSucc : ℕ)), v' l) + b := by rw [hsum_v'_eq_v]
        _ = (∑ l ∈ (Finset.univ : Finset (Fin M)).filter
          (fun l : Fin M => (l : ℕ) < (j.castSucc : ℕ)), v' l) + v' j := by simp [v']
        _ = ∑ l ∈ insert j ((Finset.univ : Finset (Fin M)).filter
          (fun l : Fin M => (l : ℕ) < (j.castSucc : ℕ))), v' l := by
          rw [Finset.sum_insert hj_not_mem, add_comm]
        _ = ∑ l ∈ (Finset.univ : Finset (Fin M)).filter
          (fun l : Fin M => (l : ℕ) < (j.succ : ℕ)), v' l := by
          rw [hfilter_eq]
    · intro h
      rcases h with ⟨v, hv, hw⟩
      have hfilter_eq : (Finset.univ : Finset (Fin M)).filter
          (fun l : Fin M => (l : ℕ) < (j.succ : ℕ)) =
          insert j ((Finset.univ : Finset (Fin M)).filter
            (fun l : Fin M => (l : ℕ) < (j.castSucc : ℕ))) := by
        ext l; simp [Fin.val_succ, Fin.val_castSucc]; omega
      have hj_not_mem : j ∉ (Finset.univ : Finset (Fin M)).filter
        (fun l : Fin M => (l : ℕ) < (j.castSucc : ℕ)) := by
        simp [Fin.val_castSucc]
      have hsum_split : ∑ l ∈ (Finset.univ : Finset (Fin M)).filter
          (fun l : Fin M => (l : ℕ) < (j.succ : ℕ)), v l =
          (∑ l ∈ (Finset.univ : Finset (Fin M)).filter
            (fun l : Fin M => (l : ℕ) < (j.castSucc : ℕ)), v l) + v j := by
        calc
          ∑ l ∈ (Finset.univ : Finset (Fin M)).filter
            (fun l : Fin M => (l : ℕ) < (j.succ : ℕ)), v l
              = ∑ l ∈ insert j ((Finset.univ : Finset (Fin M)).filter
            (fun l : Fin M => (l : ℕ) < (j.castSucc : ℕ))), v l := by
            rw [hfilter_eq]
          _ = v j + ∑ l ∈ (Finset.univ : Finset (Fin M)).filter
              (fun l : Fin M => (l : ℕ) < (j.castSucc : ℕ)), v l :=
            Finset.sum_insert hj_not_mem
          _ = (∑ l ∈ (Finset.univ : Finset (Fin M)).filter
              (fun l : Fin M => (l : ℕ) < (j.castSucc : ℕ)), v l) + v j := add_comm _ _
      rw [hsum_split] at hw
      have ha_mem : (∑ l ∈ (Finset.univ : Finset (Fin M)).filter
          (fun l : Fin M => (l : ℕ) < (j.castSucc : ℕ)), v l) ∈ R_partial j.castSucc :=
        (ih (∑ l ∈ (Finset.univ : Finset (Fin M)).filter
          (fun l : Fin M => (l : ℕ) < (j.castSucc : ℕ)), v l)).mpr ⟨v, hv, rfl⟩
      have hb_mem : v j ∈ R_per j := hv j
      rw [hR_partial_succ j]
      apply Finset.mem_image.mpr
      refine ⟨(∑ l ∈ (Finset.univ : Finset (Fin M)).filter
                (fun l : Fin M => (l : ℕ) < (j.castSucc : ℕ)), v l, v j),
        Finset.mem_product.mpr ⟨ha_mem, hb_mem⟩, ?_⟩
      simpa using hw.symm

open scoped Classical in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E] in
/-- **Unique decomposition of a prefix offset.**  Under the genericity clause `hdirect` — distinct
full paths have distinct total sums, the sharp form of GWZ Lemma 7.6's essential-distinctness
statement — the splitting of an element of `R_partial k.succ` into a prefix offset in
`R_partial k.castSucc` plus a step in `R_per k` is unique. -/
lemma subStickyFrostmanLemma.outerBody.RPartial_add_inj
    (M : ℕ) (R_per : Fin M → Finset E)
    (hR_per_nonempty : ∀ k : Fin M, (R_per k).Nonempty)
    (R_partial : Fin (M + 1) → Finset E)
    (hR_partial_zero : R_partial 0 = {0})
    (hR_partial_succ : ∀ k : Fin M, R_partial k.succ =
      (R_partial k.castSucc ×ˢ R_per k).image (fun p : E × E => p.1 + p.2))
    (hdirect : ∀ v v' : Fin M → E, (∀ l : Fin M, v l ∈ R_per l) →
      (∀ l : Fin M, v' l ∈ R_per l) →
      ∑ l : Fin M, v l = ∑ l : Fin M, v' l → ∀ l : Fin M, v l = v' l)
    (k : Fin M) {u u' x x' : E}
    (hu : u ∈ R_partial k.castSucc) (hu' : u' ∈ R_partial k.castSucc)
    (hx : x ∈ R_per k) (hx' : x' ∈ R_per k)
    (hsum : u + x = u' + x') : u = u' ∧ x = x' := by
  have hmem_iff := subStickyFrostmanLemma.outerBody.mem_RPartial_iff M R_per hR_per_nonempty
      R_partial hR_partial_zero hR_partial_succ (k.castSucc : Fin (M + 1))
  obtain ⟨a, ha, hu_eq⟩ := (hmem_iff _).mp hu
  obtain ⟨a', ha', hu'_eq⟩ := (hmem_iff _).mp hu'
  have hk_val_eq : (k.castSucc : ℕ) = (k : ℕ) := by
    simp
  let Lo := (Finset.univ : Finset (Fin M)).filter (fun l : Fin M => (l : ℕ) < (k : ℕ))
  have hu_eq' : u = ∑ l ∈ Lo, a l := by
    simpa [hk_val_eq, Lo] using hu_eq
  have hu'_eq' : u' = ∑ l ∈ Lo, a' l := by
    simpa [hk_val_eq, Lo] using hu'_eq
  have h_tail : ∀ l : Fin M, ∃ (z : E), z ∈ R_per l := hR_per_nonempty
  choose t ht using h_tail
  let Hi := (Finset.univ : Finset (Fin M)).filter (fun l : Fin M => (k : ℕ) < (l : ℕ))
  let w : Fin M → E := fun l =>
    if hlt : (l : ℕ) < (k : ℕ) then a l
    else if h_eq : l = k then x
    else t l
  let w' : Fin M → E := fun l =>
    if hlt : (l : ℕ) < (k : ℕ) then a' l
    else if h_eq : l = k then x'
    else t l
  have hw_mem : ∀ l : Fin M, w l ∈ R_per l := by
    intro l
    dsimp [w]
    by_cases hlt : (l : ℕ) < (k : ℕ)
    · simp [hlt, ha l]
    · by_cases h_eq : l = k
      · simp [h_eq, hx]
      · simp [hlt, h_eq, ht l]
  have hw'_mem : ∀ l : Fin M, w' l ∈ R_per l := by
    intro l
    dsimp [w']
    by_cases hlt : (l : ℕ) < (k : ℕ)
    · simp [hlt, ha' l]
    · by_cases h_eq : l = k
      · simp [h_eq, hx']
      · simp [hlt, h_eq, ht l]
  have h_disjoint_Lo_k : Disjoint Lo ({k} : Finset (Fin M)) := by
    apply Finset.disjoint_left.mpr
    intro l hl
    have hlt : (l : ℕ) < (k : ℕ) := (Finset.mem_filter.mp hl).2
    intro hmem
    have : l = k := Finset.mem_singleton.mp hmem
    have : (l : ℕ) = (k : ℕ) := congrArg Fin.val this
    omega
  have h_disjoint_union_Hi : Disjoint (Lo ∪ ({k} : Finset (Fin M))) Hi := by
    apply Finset.disjoint_left.mpr
    intro l hl
    rcases Finset.mem_union.mp hl with (hl' | hl')
    · intro hmem
      have hlt : (l : ℕ) < (k : ℕ) := (Finset.mem_filter.mp hl').2
      rcases Finset.mem_filter.mp hmem with ⟨_, hgt⟩
      omega
    · intro hmem
      have h_eq : l = k := Finset.mem_singleton.mp hl'
      subst h_eq
      rcases Finset.mem_filter.mp hmem with ⟨_, hgt⟩
      omega
  have h_univ_partition : (Finset.univ : Finset (Fin M)) = Lo ∪ ({k} : Finset (Fin M)) ∪ Hi := by
    ext l
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter,
      Finset.mem_singleton, Lo, Hi]
    have htri := Nat.lt_trichotomy (l : ℕ) (k : ℕ)
    rcases htri with (hlt | heq | hgt)
    · simp [hlt]
    · simp [Fin.ext heq]
    · simp [hgt]
  have h_w_on_Lo : ∀ l ∈ Lo, w l = a l := by
    intro l hl
    have hlt : (l : ℕ) < (k : ℕ) := (Finset.mem_filter.mp hl).2
    dsimp [w]
    rw [if_pos hlt]
  have h_w_on_k : (∑ l ∈ ({k} : Finset (Fin M)), w l) = x := by
    simp [w]
  have h_w_on_Hi : ∀ l ∈ Hi, w l = t l := by
    intro l hl
    have hgt : (k : ℕ) < (l : ℕ) := (Finset.mem_filter.mp hl).2
    have h_not_lt : ¬ ((l : ℕ) < (k : ℕ)) := by omega
    have h_ne : l ≠ k := by
      intro h_eq; have : (l : ℕ) = (k : ℕ) := congrArg Fin.val h_eq; omega
    dsimp [w]
    rw [if_neg h_not_lt, if_neg h_ne]
  have h_w'_on_Lo : ∀ l ∈ Lo, w' l = a' l := by
    intro l hl
    have hlt : (l : ℕ) < (k : ℕ) := (Finset.mem_filter.mp hl).2
    dsimp [w']
    rw [if_pos hlt]
  have h_w'_on_k : (∑ l ∈ ({k} : Finset (Fin M)), w' l) = x' := by
    simp [w']
  have h_w'_on_Hi : ∀ l ∈ Hi, w' l = t l := by
    intro l hl
    have hgt : (k : ℕ) < (l : ℕ) := (Finset.mem_filter.mp hl).2
    have h_not_lt : ¬ ((l : ℕ) < (k : ℕ)) := by omega
    have h_ne : l ≠ k := by
      intro h_eq; have : (l : ℕ) = (k : ℕ) := congrArg Fin.val h_eq; omega
    dsimp [w']
    rw [if_neg h_not_lt, if_neg h_ne]
  have hsum_w : ∑ l : Fin M, w l = (∑ l ∈ Lo, a l) + x + (∑ l ∈ Hi, t l) := by
    calc
      ∑ l : Fin M, w l = ∑ l ∈ (Lo ∪ ({k} : Finset (Fin M)) ∪ Hi), w l := by rw [h_univ_partition]
      _ = (∑ l ∈ (Lo ∪ ({k} : Finset (Fin M))), w l) + (∑ l ∈ Hi, w l) := by
        rw [Finset.sum_union h_disjoint_union_Hi]
      _ = ((∑ l ∈ Lo, w l) + (∑ l ∈ ({k} : Finset (Fin M)), w l)) + (∑ l ∈ Hi, w l) := by
        rw [Finset.sum_union h_disjoint_Lo_k]
      _ = ((∑ l ∈ Lo, a l) + x) + (∑ l ∈ Hi, t l) := by
        rw [Finset.sum_congr rfl (fun l hl => h_w_on_Lo l hl), h_w_on_k,
          Finset.sum_congr rfl (fun l hl => h_w_on_Hi l hl)]
      _ = (∑ l ∈ Lo, a l) + x + (∑ l ∈ Hi, t l) := by abel
  have hsum_w' : ∑ l : Fin M, w' l = (∑ l ∈ Lo, a' l) + x' + (∑ l ∈ Hi, t l) := by
    calc
      ∑ l : Fin M, w' l = ∑ l ∈ (Lo ∪ ({k} : Finset (Fin M)) ∪ Hi), w' l := by rw [h_univ_partition]
      _ = (∑ l ∈ (Lo ∪ ({k} : Finset (Fin M))), w' l) + (∑ l ∈ Hi, w' l) := by
        rw [Finset.sum_union h_disjoint_union_Hi]
      _ = ((∑ l ∈ Lo, w' l) + (∑ l ∈ ({k} : Finset (Fin M)), w' l)) + (∑ l ∈ Hi, w' l) := by
        rw [Finset.sum_union h_disjoint_Lo_k]
      _ = ((∑ l ∈ Lo, a' l) + x') + (∑ l ∈ Hi, t l) := by
        rw [Finset.sum_congr rfl (fun l hl => h_w'_on_Lo l hl), h_w'_on_k,
          Finset.sum_congr rfl (fun l hl => h_w'_on_Hi l hl)]
      _ = (∑ l ∈ Lo, a' l) + x' + (∑ l ∈ Hi, t l) := by abel
  have htotal_sum : ∑ l : Fin M, w l = ∑ l : Fin M, w' l := by
    rw [hsum_w, hsum_w']
    have hsum_eq : (∑ l ∈ Lo, a l) + x = (∑ l ∈ Lo, a' l) + x' := by
      calc
        (∑ l ∈ Lo, a l) + x = u + x := by rw [hu_eq']
        _ = u' + x' := hsum
        _ = (∑ l ∈ Lo, a' l) + x' := by rw [hu'_eq']
    rw [hsum_eq]
  have h_all_eq : ∀ l : Fin M, w l = w' l :=
    hdirect w w' hw_mem hw'_mem htotal_sum
  have hx_eq : x = x' := by
    have hwk : w k = w' k := h_all_eq k
    dsimp [w, w'] at hwk
    have h_not_lt : ¬ ((k : ℕ) < (k : ℕ)) := by omega
    simp only [h_not_lt] at hwk
    exact hwk
  have hu_eq_final : u = u' := by
    have h_lo_eq : ∀ l ∈ Lo, a l = a' l := by
      intro l hl
      have hwl : w l = w' l := h_all_eq l
      dsimp [w, w'] at hwl
      have hlt : (l : ℕ) < (k : ℕ) := (Finset.mem_filter.mp hl).2
      simp only [hlt] at hwl
      exact hwl
    calc
      u = ∑ l ∈ Lo, a l := hu_eq'
      _ = ∑ l ∈ Lo, a' l := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [h_lo_eq l hl]
      _ = u' := by rw [hu'_eq']
  exact ⟨hu_eq_final, hx_eq⟩

/-- **Constant in the `|q|` cardinality bound of Lemma 7.5** (`subStickyFrostmanLemma`, paper L109):
the `δ`-independent factor in `|q| ≤ C · δ^{-ε} · max{1, (|s|·|T_δ|)⁻¹}`.  The telescoped product
`∏_m max{1, x_m}` picks up one factor of `C_R · Cn` per scale plus the leaf-count product constant
`C_prod`; the irreducible `δ^{-ε}` of the mixed regime is carried separately in the conclusion.
Downstream only `1 ≤ C` and `C ≤ qCardConst` are used, never the value. -/
noncomputable def qCardConst (_n M : ℕ) (Cn C_prod : ℝ) : ℝ :=
  (2 * max 1 Cn) ^ M * max 1 C_prod + 2

lemma one_le_qCardConst (n M : ℕ) (Cn C_prod : ℝ) : 1 ≤ qCardConst n M Cn C_prod := by
  unfold qCardConst
  have h1 : (0 : ℝ) ≤ (2 * max 1 Cn) ^ M * max 1 C_prod := by
    have hCn : (1 : ℝ) ≤ max 1 Cn := le_max_left _ _
    have hCp : (1 : ℝ) ≤ max 1 C_prod := le_max_left _ _
    positivity
  linarith

lemma qCardConst_pos (n M : ℕ) (Cn C_prod : ℝ) : 0 < qCardConst n M Cn C_prod :=
  lt_of_lt_of_le zero_lt_one (one_le_qCardConst n M Cn C_prod)

open scoped Classical in
omit [MeasurableSpace E] [BorelSpace E] in
/-- Cardinality upper bound on the Minkowski-sum chain `R_partial (Fin.last M)` (blueprint
`lem:composed_translation_family`, paper L109).  From `|R_partial (last)| ≤ ∏_k |R_per k|` the
blueprint telescoping turns `∏_k max{1, x_k}` into
`Cn^M · δ^{-ε} · C_prod · max{1, (|s| · δ^{n-1})⁻¹}`; the `δ^{-ε}` is the irreducible price of the
mixed regime, in which some scales have `x_k ≤ 1` and others `x_k ≥ 1`. -/
lemma subStickyFrostmanLemma.outerBody.cardUB
    {ε : ℝ} (hε : 0 < ε) (M : ℕ) {ι : Type*} (s : Finset ι) (hs_ne : s.Nonempty) {δ : NNReal}
    (hδ_pos : 0 < (δ : ℝ)) (hδ_le_one : (δ : ℝ) ≤ 1)
    (ρ : Fin (M + 1) → NNReal)
    (hρ_pos : ∀ k, 0 < (ρ k : ℝ)) (hρ0 : (ρ 0 : ℝ) ≤ 1) (hρ_M : ρ (Fin.last M) = δ)
    (hρ_anti : ∀ k : Fin M, (ρ k.succ : ℝ) ≤ (ρ k.castSucc : ℝ))
    (N₂ : Fin M → ℕ) (hN₂_pos : ∀ k, 0 < N₂ k)
    {Cn : ℝ} (hCn_ge_one : 1 ≤ Cn)
    (hN₂_xm : ∀ k : Fin M, (N₂ k : ℝ)
      ≤ Cn * ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ))
          ^ (((Module.finrank ℝ E : ℝ) - 1) + ε))
    {C_prod : ℝ} (hC_prod_pos : 0 < C_prod)
    (hN₂_prod : (s.card : ℝ) ≤ C_prod * ∏ k : Fin M, (N₂ k : ℝ))
    (R_per : Fin M → Finset E)
    (hRk_card : ∀ k : Fin M,
      ((R_per k).card : ℝ) ≤
        2 * max 1 (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^
          ((Module.finrank ℝ E : ℝ) - 1) / (N₂ k : ℝ)))
    (R_partial : Fin (M + 1) → Finset E)
    (hR_partial_zero : R_partial 0 = {0})
    (hR_partial_succ : ∀ k : Fin M, R_partial k.succ =
      (R_partial k.castSucc ×ˢ R_per k).image (fun p : E × E => p.1 + p.2)) :
    ∃ C_card : ℝ, 0 < C_card ∧
      C_card ≤ qCardConst (Module.finrank ℝ E) M Cn C_prod ∧
      ((R_partial (Fin.last M)).card : ℝ) ≤ C_card * (δ : ℝ) ^ (-ε) *
          max 1
            ((s.card : ℝ) *
                (δ : ℝ) ^ ((Module.finrank ℝ E : ℝ) - 1))⁻¹ := by
  set n := Module.finrank ℝ E with hn_def
  have hn_pos : 0 < n := Module.finrank_pos
  have h_exp_nonneg : 0 ≤ (n : ℝ) - 1 := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
    linarith
  have hε_nonneg : 0 ≤ ε := by linarith
  set x := fun k : Fin M =>
    ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ((n : ℝ) - 1) / (N₂ k : ℝ) with hx_def
  have hx_nonneg : ∀ k : Fin M, 0 ≤ x k := by
    intro k
    dsimp [x]
    have hΛ_nonneg : 0 ≤ ((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^ ((n : ℝ) - 1) :=
      Real.rpow_nonneg (div_nonneg (by positivity) (by positivity)) _
    have hN₂_nonneg : (0 : ℝ) ≤ (N₂ k : ℝ) := by exact_mod_cast (hN₂_pos k).le
    positivity
  have h_max_nonneg : ∀ k : Fin M, 0 ≤ max 1 (x k) := fun k =>
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)
  have h_max_nonneg_prod : 0 ≤ ∏ k : Fin M, max 1 (x k) :=
    Finset.prod_nonneg fun k _ => h_max_nonneg k
  have hx_nonneg_prod : 0 ≤ ∏ k : Fin M, x k :=
    Finset.prod_nonneg fun k _ => hx_nonneg k
  have hCn_nonneg : 0 ≤ Cn := by linarith
  have hCn_M_nonneg : 0 ≤ Cn ^ M := pow_nonneg hCn_nonneg M
  have hδ_pow_nonneg : 0 ≤ (δ : ℝ) ^ (-ε) :=
    Real.rpow_nonneg (by positivity : 0 ≤ (δ : ℝ)) _
  have h_max_prod_nonneg : 0 ≤ max 1 (∏ k : Fin M, x k) :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)
  set S := fun (k : Fin (M+1)) =>
    Finset.filter (fun (i : Fin M) => (i : ℕ) < (k : ℕ)) Finset.univ with hS_def
  have hcard_S_succ : ∀ (j : Fin M), S j.succ = insert j (S j.castSucc) := by
    intro j
    ext i
    constructor
    · intro hi
      have hi_mem : i ∈ Finset.univ := (Finset.mem_filter.mp hi).1
      have hi_val_lt : (i : ℕ) < (j.succ : ℕ) := (Finset.mem_filter.mp hi).2
      have hi_val_le_j : (i : ℕ) ≤ (j : ℕ) := by
        have : (j.succ : ℕ) = (j : ℕ) + 1 := by simp
        omega
      by_cases hi_eq_j : i = j
      · subst hi_eq_j; exact Finset.mem_insert.mpr (Or.inl rfl)
      · have hi_val_lt_j : (i : ℕ) < (j : ℕ) := by
          refine lt_of_le_of_ne hi_val_le_j ?_
          intro h_eq
          apply hi_eq_j
          exact Fin.ext h_eq
        apply Finset.mem_insert_of_mem
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simpa [Fin.val_castSucc] using hi_val_lt_j
    · intro hi
      rcases Finset.mem_insert.mp hi with (rfl | hi)
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simp
      · have hi_mem : i ∈ S j.castSucc := hi
        have hi_val_lt : (i : ℕ) < (j.castSucc : ℕ) := (Finset.mem_filter.mp hi_mem).2
        have hi_val_lt_succ : (i : ℕ) < (j.succ : ℕ) := by
          calc
            (i : ℕ) < (j.castSucc : ℕ) := hi_val_lt
            _ = (j : ℕ) := by simp
            _ < (j : ℕ) + 1 := by omega
            _ = (j.succ : ℕ) := by simp
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi_val_lt_succ⟩
  have hcard_nat_nonneg : ∀ (k : Fin (M+1)), 0 ≤ ∏ i ∈ S k, ((R_per i).card : ℝ) :=
    fun k => Finset.prod_nonneg (fun i _ => by exact_mod_cast (Nat.zero_le _))
  have hcard_chain : ∀ k : Fin (M+1), ((R_partial k).card : ℝ) ≤ ∏ i ∈ S k, ((R_per i).card : ℝ)
    := by
    intro k
    induction k using Fin.induction with
    | zero =>
        simp [hS_def, hR_partial_zero]
    | succ j ih =>
        have hcard_bound : ((R_partial j.succ).card : ℝ) ≤
            ((R_partial j.castSucc).card : ℝ) * ((R_per j).card : ℝ) := by
          calc
            ((R_partial j.succ).card : ℝ) ≤ ((R_partial j.castSucc ×ˢ R_per j).card : ℝ) := by
              rw [hR_partial_succ j]
              exact_mod_cast Finset.card_image_le
            _ = ((R_partial j.castSucc).card : ℝ) * ((R_per j).card : ℝ) := by
              simp [Finset.card_product]
        calc
          ((R_partial j.succ).card : ℝ) ≤ ((R_partial j.castSucc).card : ℝ) * ((R_per j).card : ℝ)
              :=
            hcard_bound
          _ ≤ (∏ i ∈ S j.castSucc, ((R_per i).card : ℝ)) * ((R_per j).card : ℝ) :=
            mul_le_mul_of_nonneg_right ih (by exact_mod_cast Nat.zero_le _)
          _ = (∏ i ∈ insert j (S j.castSucc), ((R_per i).card : ℝ)) := by
            rw [Finset.prod_insert (by
              intro h
              have hmem : j ∈ S j.castSucc := h
              have h_val_lt : (j : ℕ) < (j.castSucc : ℕ) := (Finset.mem_filter.mp hmem).2
              have : (j.castSucc : ℕ) = (j : ℕ) := by simp
              rw [this] at h_val_lt
              exact lt_irrefl _ h_val_lt), mul_comm]
          _ = (∏ i ∈ S j.succ, ((R_per i).card : ℝ)) := by rw [hcard_S_succ j]
  have hcard_last : ((R_partial (Fin.last M)).card : ℝ) ≤ ∏ i : Fin M, ((R_per i).card : ℝ) := by
    calc
      ((R_partial (Fin.last M)).card : ℝ) ≤ ∏ i ∈ S (Fin.last M), ((R_per i).card : ℝ) :=
        hcard_chain (Fin.last M)
      _ = ∏ i : Fin M, ((R_per i).card : ℝ) := by
        simp [hS_def, Fin.last]
  have h_prod_Rper : ∏ i : Fin M, ((R_per i).card : ℝ) ≤ (2^M : ℝ) * ∏ i : Fin M, max 1 (x i) := by
    have h_factor : ∀ k : Fin M, ((R_per k).card : ℝ) ≤ 2 * max 1 (x k) := by
      intro k
      calc
        ((R_per k).card : ℝ) ≤ 2 * max 1 (((ρ k.castSucc : ℝ) / (ρ k.succ : ℝ)) ^
            ((n : ℝ) - 1) / (N₂ k : ℝ)) := hRk_card k
        _ = 2 * max 1 (x k) := by rfl
    have h_nonneg : ∀ k : Fin M, 0 ≤ ((R_per k).card : ℝ) := fun k =>
      by exact_mod_cast (Nat.zero_le _)
    have h_nonneg_mul : ∀ k : Fin M, 0 ≤ 2 * max 1 (x k) := by
      intro k; positivity
    calc
      ∏ i : Fin M, ((R_per i).card : ℝ) ≤ ∏ i : Fin M, (2 * max 1 (x i)) :=
        Finset.prod_le_prod (fun k _ => h_nonneg k) (fun k _ => h_factor k)
      _ = (∏ i : Fin M, (2 : ℝ)) * (∏ i : Fin M, max 1 (x i)) := by
        rw [Finset.prod_mul_distrib]
      _ = (2^M : ℝ) * (∏ i : Fin M, max 1 (x i)) := by
        simp [Finset.prod_const]
  have h_prod_max_x : ∏ i : Fin M, max 1 (x i) ≤
      Cn ^ M * (δ : ℝ) ^ (-ε) * max 1 (∏ i : Fin M, x i) := by
    exact prod_max_le M hε hCn_ge_one hδ_pos hδ_le_one ρ hρ_pos hρ0 hρ_M hρ_anti N₂ hN₂_pos hN₂_xm
  have h_prod_x : ∏ i : Fin M, x i ≤ C_prod * ((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹ := by
    exact prod_x_le M hδ_pos hδ_le_one ρ hρ_pos hρ0 hρ_M N₂ hN₂_pos s hs_ne hC_prod_pos hN₂_prod
  have h_max_prod : max 1 (∏ i : Fin M, x i) ≤ max 1 C_prod
        * max 1 (((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹) := by
    have h_nonneg_prod : 0 ≤ ∏ i : Fin M, x i := hx_nonneg_prod
    have h_nonneg_C_prod : 0 ≤ C_prod := hC_prod_pos.le
    have h_nonneg_inv : 0 ≤ ((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹ := by
      have hpos : 0 < (s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1) := by
        have hcard_pos : 0 < (s.card : ℝ) := by
          have hcard_nat_pos : 0 < s.card := Finset.card_pos.mpr hs_ne
          exact_mod_cast hcard_nat_pos
        have hδ_pow_pos : 0 < (δ : ℝ) ^ ((n : ℝ) - 1) := Real.rpow_pos_of_pos hδ_pos _
        positivity
      positivity
    have hprod_le : ∏ i : Fin M, x i ≤ C_prod * ((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹
      := h_prod_x
    have hmax_le : max 1 (∏ i : Fin M, x i)
      ≤ max 1 (C_prod * ((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹) :=
      max_le_max (le_refl 1) hprod_le
    have hmax_mul : max 1 (C_prod * ((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹) ≤
        max 1 C_prod * max 1 (((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹) := by
      have h_nonneg_mul : 0 ≤ C_prod * ((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹ :=
        mul_nonneg h_nonneg_C_prod h_nonneg_inv
      by_cases hmul : C_prod * ((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹ ≤ 1
      · have hLHS : max 1 (C_prod * ((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹) = 1 := by
          rw [max_eq_left hmul]
        rw [hLHS]
        have h1 : (1 : ℝ) ≤ max 1 C_prod := le_max_left _ _
        have h2 : (1 : ℝ) ≤ max 1 (((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹) := le_max_left _ _
        nlinarith
      · push Not at hmul
        have hLHS : max 1 (C_prod * ((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹) =
            C_prod * ((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹ := by
          rw [max_eq_right (by linarith : 1 ≤ C_prod * ((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹)]
        rw [hLHS]
        have hC_prod : C_prod ≤ max 1 C_prod := le_max_right _ _
        have hinv : ((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹ ≤
            max 1 (((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹) := le_max_right _ _
        have h_nonneg_maxC : 0 ≤ max 1 C_prod :=
            le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)
        exact mul_le_mul hC_prod hinv h_nonneg_inv h_nonneg_maxC
    exact le_trans hmax_le hmax_mul
  set C_card : ℝ := (2 * max 1 Cn) ^ M * max 1 C_prod + 1 with hC_card_def
  have hC_card_pos : 0 < C_card := by
    rw [hC_card_def]
    have h_nonneg : 0 ≤ (2 * max 1 Cn) ^ M * max 1 C_prod := by
      positivity
    positivity
  have hC_card_le_qCardConst : C_card ≤ qCardConst (Module.finrank ℝ E) M Cn C_prod := by
    rw [hC_card_def, qCardConst]
    have h_nonneg : 0 ≤ (2 * max 1 Cn) ^ M * max 1 C_prod := by
      positivity
    nlinarith
  have hCardMain : ((R_partial (Fin.last M)).card : ℝ) ≤ C_card * (δ : ℝ) ^ (-ε) *
      max 1 (((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹) := by
    calc
      ((R_partial (Fin.last M)).card : ℝ) ≤ ∏ i : Fin M, ((R_per i).card : ℝ) := hcard_last
      _ ≤ (2^M : ℝ) * ∏ i : Fin M, max 1 (x i) := h_prod_Rper
      _ = (2^M : ℝ) * (∏ i : Fin M, max 1 (x i)) := rfl
      _ ≤ (2^M : ℝ) * (Cn ^ M * (δ : ℝ) ^ (-ε) * max 1 (∏ i : Fin M, x i)) :=
        mul_le_mul_of_nonneg_left h_prod_max_x (by positivity)
      _ = (2^M * Cn ^ M) * (δ : ℝ) ^ (-ε) * max 1 (∏ i : Fin M, x i) := by ring
      _ = ((2 * Cn) ^ M) * (δ : ℝ) ^ (-ε) * max 1 (∏ i : Fin M, x i) := by
        rw [mul_pow]
      _ = ((2 * max 1 Cn) ^ M) * (δ : ℝ) ^ (-ε) * max 1 (∏ i : Fin M, x i) := by
        have hmaxCn : max 1 Cn = Cn := by
          have hCn_ge_one' : 1 ≤ Cn := hCn_ge_one
          simp [hCn_ge_one']
        simp [hmaxCn]
      _ ≤ ((2 * max 1 Cn) ^ M * max 1 C_prod + 1) * (δ : ℝ) ^ (-ε) *
          max 1 (((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹) := by
        have h_nonneg_base : 0 ≤ (2 * max 1 Cn) ^ M := by positivity
        have h_nonneg_δ : 0 ≤ (δ : ℝ) ^ (-ε) := hδ_pow_nonneg
        have h_nonneg_maxProd : 0 ≤ max 1 (∏ i : Fin M, x i) := h_max_prod_nonneg
        have h_ineq : (2 * max 1 Cn) ^ M * max 1 (∏ i : Fin M, x i) ≤
            ((2 * max 1 Cn) ^ M * max 1 C_prod + 1) *
              max 1 (((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹) := by
          calc
            (2 * max 1 Cn) ^ M * max 1 (∏ i : Fin M, x i)
                ≤ (2 * max 1 Cn) ^ M
                  * (max 1 C_prod * max 1 (((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹)) :=
                  mul_le_mul_of_nonneg_left h_max_prod (by positivity)
            _ = ((2 * max 1 Cn) ^ M * max 1 C_prod) *
                max 1 (((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹) := by ring
            _ ≤ ((2 * max 1 Cn) ^ M * max 1 C_prod + 1) *
                max 1 (((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹) := by
              refine mul_le_mul_of_nonneg_right ?_ (by
                have h_nonneg_inv : 0 ≤ max 1 (((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹) :=
                  le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)
                exact h_nonneg_inv)
              nlinarith
        calc
          ((2 * max 1 Cn) ^ M) * (δ : ℝ) ^ (-ε) * max 1 (∏ i : Fin M, x i)
              = (δ : ℝ) ^ (-ε) * ((2 * max 1 Cn) ^ M * max 1 (∏ i : Fin M, x i)) := by ring
          _ ≤ (δ : ℝ) ^ (-ε) * (((2 * max 1 Cn) ^ M * max 1 C_prod + 1) *
              max 1 (((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹)) :=
            mul_le_mul_of_nonneg_left h_ineq hδ_pow_nonneg
          _ = ((2 * max 1 Cn) ^ M * max 1 C_prod + 1) * (δ : ℝ) ^ (-ε) *
              max 1 (((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹) := by ring
      _ = C_card * (δ : ℝ) ^ (-ε) * max 1 (((s.card : ℝ) * (δ : ℝ) ^ ((n : ℝ) - 1))⁻¹) := by rfl
  refine ⟨C_card, hC_card_pos, hC_card_le_qCardConst, ?_⟩
  simpa [hn_def] using hCardMain
end StickyKakeya

end Kakeya
