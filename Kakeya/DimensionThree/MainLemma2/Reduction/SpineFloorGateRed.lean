/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factorization
public import Kakeya.Tube.Basic
public import Kakeya.Tube.Dilate
public import Kakeya.Thickness.Projection

/-!
# G3, red half: the biased factorization's retained subfamily can lose `Δ_max` polynomially

`ConvexSpaceBody.nonempty_biasedFactorization` (GWZ Lemma 9.2, refined `lemmafactmaxbias`) returns a
subfamily `s' ⊆ s` retaining **volume** (`Σ_s |V| ≤ L · Σ_{s'} |V|`) and carrying a biased
factorization.  The probe G3  asked whether such an `s'` also retains
`Δ_max` up to a subpolynomial factor.  **It cannot be added to the conclusion**: this file exhibits,
at every `δ ≤ 1/64`, a family `s` satisfying every hypothesis of the theorem, and a subfamily `s'`
satisfying every clause of its conclusion, with `Δ_max(s') ≤ 1` and `Δ_max(s) ≥ ⌊1/(24δ)⌋` — a
polynomial collapse `δ^{-1}`.

The family: `k = ⌊1/(24δ)⌋` identical copies of one central `δ`-tube (density `≥ k` inside that
tube) together with `k` pairwise disjoint translates of it along `e₀` at spacing `3δ`; the retained
subfamily is the translates alone, with the singleton partition as its biased factorization.
This is
the source's own reason for alternative (D) of `lem:ml2-window-refinement` (l.4116–4128): a
mass-weighted selection can delete the members inside the concentrating body.

The green half — that the count floor's derivation does not need the retained subfamily at all — is
`Kakeya.ML2Core.exists_biasedMaximizer_densityIn_ge` in `Reduction/SpineFloorGate.lean`.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Elementary tools, kept upstream of the Section-9 leaves -/

/-- A family of pairwise disjoint bodies has maximal density at most `1`. -/
theorem maxDensity_le_one_of_pairwiseDisjoint' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (h : (s : Set ι).PairwiseDisjoint (fun i => (W i).carrier)) :
    Kakeya.maxDensity s W ≤ 1 := by
  classical
  rw [Kakeya.maxDensity_le_iff]
  intro K
  unfold Kakeya.densityIn
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul]
  have hpd : (((s.filter fun i => W i ≤ K) : Finset ι) : Set ι).PairwiseDisjoint
      (fun i => (W i).carrier) := by
    refine h.subset ?_
    intro i hi
    exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).1
  rw [← measure_biUnion_finset hpd (fun i _ => (W i).isCompact.isClosed.measurableSet)]
  refine measure_mono ?_
  refine Set.iUnion₂_subset fun i hi => ?_
  exact (Finset.mem_filter.mp hi).2

/-- Translation is a `1`-Lipschitz affine self-map of `ℝ³`. -/
theorem lipschitzWith_constVAdd' (v : E3) :
    LipschitzWith 1 ((AffineEquiv.constVAdd ℝ E3 v).toAffineMap : E3 → E3) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  have h : ((AffineEquiv.constVAdd ℝ E3 v).toAffineMap : E3 → E3) = fun x => v + x := rfl
  rw [h, NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm,
    show v + y - (v + z) = y - z by abel]

/-- `ethickness` is translation invariant. -/
theorem ethickness_constVAdd_image' (v : E3) (X : Set E3) (k : ℕ) :
    Metric.ethickness ℝ ((fun x => v + x) '' X) k = Metric.ethickness ℝ X k := by
  have key : ∀ (w : E3) (Y : Set E3),
      Metric.ethickness ℝ ((fun x => w + x) '' Y) k ≤ Metric.ethickness ℝ Y k := by
    intro w Y
    have h := (LipschitzWith.ethickness_image_le
      (f := (AffineEquiv.constVAdd ℝ E3 w).toAffineMap) (C := 1)
      (lipschitzWith_constVAdd' w) Y) k
    have hf : ((AffineEquiv.constVAdd ℝ E3 w).toAffineMap : E3 → E3) = fun x => w + x := rfl
    rw [hf] at h
    simpa [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul] using h
  refine le_antisymm (key v X) ?_
  have hback : (fun x : E3 => -v + x) '' ((fun x : E3 => v + x) '' X) = X := by
    rw [Set.image_image]
    simp
  calc Metric.ethickness ℝ X k
      = Metric.ethickness ℝ ((fun x : E3 => -v + x) '' ((fun x : E3 => v + x) '' X)) k := by
        rw [hback]
    _ ≤ Metric.ethickness ℝ ((fun x : E3 => v + x) '' X) k := key _ _

/-- The carrier of a translated tube is the translated carrier. -/
theorem translate_carrier_eq_image {δ : NNReal} (T : Tube δ E3) (v : E3) :
    (T.translate v).carrier = (fun x => v + x) '' T.carrier := by
  rw [Tube.translate_carrier, Set.image_add_left]

/-! ## The family -/

/-- The axis direction `e₂` and the translation direction `e₀`. -/
noncomputable def redE (k : Fin 3) : E3 := EuclideanSpace.single k (1 : ℝ)

theorem norm_redE (k : Fin 3) : ‖redE k‖ = 1 := by simp [redE]

theorem inner_redE_of_ne {k l : Fin 3} (h : k ≠ l) : inner ℝ (redE k) (redE l) = 0 := by
  simp [redE, EuclideanSpace.inner_single_left, h]

/-- The central `δ`-tube: midpoint `0`, direction `e₂`. -/
noncomputable def redTube (δ : NNReal) : Tube δ E3 :=
  Tube.ofMidpointDirection δ 0 (redE 2) (norm_redE 2)

/-- The `n`-th translate, offset `3δ n` along `e₀`. -/
noncomputable def redLeaf (δ : NNReal) (n : ℕ) : Tube δ E3 :=
  (redTube δ).translate ((3 * (δ : ℝ) * n) • redE 0)

/-- The bodies: `inl _` is the central tube (repeated), `inr n` the `n`-th translate. -/
noncomputable def redBody (δ : NNReal) : ℕ ⊕ ℕ → ConvexSpaceBody E3
  | Sum.inl _ => (redTube δ).toConvexSpaceBody
  | Sum.inr n => (redLeaf δ n).toConvexSpaceBody

theorem redBody_inl (δ : NNReal) (n : ℕ) : redBody δ (Sum.inl n) = (redTube δ).toConvexSpaceBody :=
  rfl

theorem redBody_inr (δ : NNReal) (n : ℕ) :
    redBody δ (Sum.inr n) = (redLeaf δ n).toConvexSpaceBody :=
  rfl

/-- Two distinct translates are disjoint: for a common point `p = w_n + q = w_m + q'`, the
difference `w_n − w_m = q' − q` is orthogonal to the axis, so `‖w_n − w_m‖² ≤ 2δ ‖w_n − w_m‖`,
against `‖w_n − w_m‖ = 3δ|n − m| ≥ 3δ`. -/
theorem disjoint_redLeaf {δ : NNReal} (hδ : 0 < δ) {n m : ℕ} (h : n ≠ m) :
    Disjoint (redLeaf δ n).carrier (redLeaf δ m).carrier := by
  rw [Set.disjoint_left]
  intro p hp hp'
  simp only [redLeaf, Tube.translate_carrier, Set.mem_preimage] at hp hp'
  set q : E3 := -((3 * (δ : ℝ) * n) • redE 0) + p with hq_def
  set q' : E3 := -((3 * (δ : ℝ) * m) • redE 0) + p with hq'_def
  have hq : q ∈ (redTube δ).carrier := hp
  have hq' : q' ∈ (redTube δ).carrier := hp'
  rw [(redTube δ).carrier_eq] at hq hq'
  obtain ⟨z, hz, hqz⟩ := Set.mem_iUnion₂.mp hq
  obtain ⟨z', hz', hqz'⟩ := Set.mem_iUnion₂.mp hq'
  have hseg : ∀ w ∈ segment ℝ (redTube δ).x (redTube δ).y, ∃ t : ℝ, w = t • redE 2 := by
    intro w hw
    rw [segment_eq_image] at hw
    obtain ⟨θ, -, rfl⟩ := hw
    refine ⟨θ - 1 / 2, ?_⟩
    simp only [redTube, Tube.ofMidpointDirection_x, Tube.ofMidpointDirection_y]
    module
  obtain ⟨t, rfl⟩ := hseg z hz
  obtain ⟨t', rfl⟩ := hseg z' hz'
  rw [Metric.mem_closedBall, dist_eq_norm] at hqz hqz'
  set d : E3 := (3 * (δ : ℝ) * n) • redE 0 - (3 * (δ : ℝ) * m) • redE 0 with hd
  have hdq : d = q' - q := by
    rw [hd, hq_def, hq'_def]
    abel
  have hinner : inner ℝ d (t' • redE 2 - t • redE 2) = 0 := by
    rw [inner_sub_right, inner_smul_right, inner_smul_right, hd, inner_sub_left,
      inner_smul_left, inner_smul_left, inner_redE_of_ne (by decide)]
    simp
  have hnorm : ‖d‖ ^ 2 ≤ ‖d‖ * (2 * (δ : ℝ)) := by
    have hself : ‖d‖ ^ 2 = inner ℝ d d := (real_inner_self_eq_norm_sq d).symm
    rw [hself]
    have hsplit : d = ((q' - t' • redE 2) - (q - t • redE 2)) + (t' • redE 2 - t • redE 2) := by
      rw [hdq]; abel
    calc inner ℝ d d
        = inner ℝ d (((q' - t' • redE 2) - (q - t • redE 2))
          + (t' • redE 2 - t • redE 2)) := congrArg (inner ℝ d) hsplit
      _ = inner ℝ d ((q' - t' • redE 2) - (q - t • redE 2))
          + inner ℝ d (t' • redE 2 - t • redE 2) := inner_add_right _ _ _
      _ = inner ℝ d ((q' - t' • redE 2) - (q - t • redE 2)) := by rw [hinner, add_zero]
      _ ≤ ‖d‖ * ‖(q' - t' • redE 2) - (q - t • redE 2)‖ := real_inner_le_norm _ _
      _ ≤ ‖d‖ * (2 * (δ : ℝ)) := by
          gcongr
          calc ‖(q' - t' • redE 2) - (q - t • redE 2)‖
              ≤ ‖q' - t' • redE 2‖ + ‖q - t • redE 2‖ := norm_sub_le _ _
            _ ≤ (δ : ℝ) + (δ : ℝ) := add_le_add hqz' hqz
            _ = 2 * (δ : ℝ) := by ring
  -- `‖d‖ = 3δ|n − m| ≥ 3δ`
  have hd3 : 3 * (δ : ℝ) ≤ ‖d‖ := by
    have hdiff : d = (3 * (δ : ℝ) * ((n : ℝ) - m)) • redE 0 := by
      rw [hd, ← sub_smul]; congr 1; ring
    rw [hdiff, norm_smul, norm_redE, mul_one, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 * (δ : ℝ))]
    have h1 : (1 : ℝ) ≤ |(n : ℝ) - m| := by
      rcases Nat.lt_or_gt_of_ne h with hlt | hlt
      · have : (n : ℝ) + 1 ≤ m := by exact_mod_cast hlt
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      · have : (m : ℝ) + 1 ≤ n := by exact_mod_cast hlt
        rw [abs_of_nonneg (by linarith)]
        linarith
    have hδr : (0 : ℝ) ≤ 3 * (δ : ℝ) := by positivity
    nlinarith
  have hδr : (0 : ℝ) < δ := hδ
  have hpos : 0 < ‖d‖ := lt_of_lt_of_le (by positivity) hd3
  have h2 : ‖d‖ ≤ 2 * (δ : ℝ) := by
    have := hnorm
    rw [sq] at this
    exact le_of_mul_le_mul_left this hpos
  linarith

/-- The translates lie in the unit ball once `3δn + 1/2 + δ ≤ 1`. -/
theorem redLeaf_carrier_subset_ball (δ : NNReal) (n : ℕ)
    (h : 3 * (δ : ℝ) * n + (1 / 2 + (δ : ℝ)) ≤ 1) :
    (redLeaf δ n).carrier ⊆ Metric.closedBall (0 : E3) 1 := by
  have hmid : midpoint ℝ (redLeaf δ n).x (redLeaf δ n).y = (3 * (δ : ℝ) * n) • redE 0 := by
    rw [midpoint_eq_smul_add]
    simp only [redLeaf, redTube, Tube.translate_x, Tube.translate_y,
      Tube.ofMidpointDirection_x, Tube.ofMidpointDirection_y, invOf_eq_inv]
    module
  refine (Kakeya.Tube.carrier_subset_closedBall_midpoint (E := EuclideanSpace ℝ (Fin 3))
    (redLeaf δ n)).trans ?_
  rw [hmid]
  refine Metric.closedBall_subset_closedBall' ?_
  rw [dist_zero_right, norm_smul, norm_redE, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  linarith

theorem redTube_carrier_subset_ball (δ : NNReal) (h : 1 / 2 + (δ : ℝ) ≤ 1) :
    (redTube δ).carrier ⊆ Metric.closedBall (0 : E3) 1 := by
  have hmid : midpoint ℝ (redTube δ).x (redTube δ).y = 0 := by
    rw [midpoint_eq_smul_add]
    simp only [redTube, Tube.ofMidpointDirection_x, Tube.ofMidpointDirection_y, invOf_eq_inv]
    module
  refine (Kakeya.Tube.carrier_subset_closedBall_midpoint (E := EuclideanSpace ℝ (Fin 3))
    (redTube δ)).trans ?_
  rw [hmid]
  exact Metric.closedBall_subset_closedBall h

/-! ## The constants of `nonempty_biasedFactorization`, from below -/

/-- The factoring constant is at least `2` (replicating the private `two_le_C`). -/
theorem two_le_biasedC {ϖ : ℝ} (hϖ : 0 ≤ ϖ) :
    (2 : ENNReal) ≤ (nonempty_biasedFactorization.C 3 ϖ : ENNReal) := by
  have hc : (Metric.lt_volume_convexHull.c 3 : ℝ) ≤ 1 := by
    calc (Metric.lt_volume_convexHull.c 3 : ℝ) = ((Nat.factorial 3 : ℝ)⁻¹) := by
          simp [Metric.lt_volume_convexHull.c]
      _ ≤ 1 := Nat.cast_inv_le_one (Nat.factorial 3)
  have hcpos : (0 : ℝ) < Metric.lt_volume_convexHull.c 3 := by
    exact_mod_cast Metric.lt_volume_convexHull.c_pos 3
  have h1 : (1 : NNReal) ≤ Metric.volume_comparison.C 3 := by
    rw [← NNReal.coe_le_coe]
    have : (Metric.volume_comparison.C 3 : ℝ)
        = (4 : ℝ) ^ 3 / (Metric.lt_volume_convexHull.c 3 : ℝ) := by
      simp [Metric.volume_comparison.C]
    rw [this, NNReal.coe_one, le_div_iff₀ hcpos]
    nlinarith
  have h2 : (1 : NNReal) ≤ Metric.volume_comparison.C 3 ^ ϖ := NNReal.one_le_rpow h1 hϖ
  have h3 : (2 : NNReal) ≤ nonempty_biasedFactorization.C 3 ϖ := by
    change (2 : NNReal) ≤ 2 * Metric.volume_comparison.C 3 ^ ϖ
    calc (2 : NNReal) = 2 * 1 := (mul_one 2).symm
      _ ≤ 2 * Metric.volume_comparison.C 3 ^ ϖ := by gcongr
  exact_mod_cast h3

/-- The pigeonholing loss is at least `2` once `δ ≤ 1/2` (its second factor is
`(1 + log₂(1/δ))³ ≥ 8`). -/
theorem two_le_biasedL {δ : NNReal} (hδ0 : 0 < δ) (hδ : (δ : ℝ) ≤ 1 / 2) {ϖ : ℝ} (hϖ : 0 < ϖ)
    {card : ℕ} (hcard : 1 ≤ card) :
    (2 : ENNReal) ≤ nonempty_biasedFactorization.L 3 card δ ϖ := by
  have hδr : (0 : ℝ) < δ := hδ0
  have hδ1 : δ ≤ 1 := by
    have : (δ : ℝ) ≤ 1 := hδ.trans (by norm_num)
    exact_mod_cast this
  have hA : (1 : ENNReal) ≤ ENNReal.ofReal (1 + Real.logb 2 ((card : ℝ) *
      ((2 : ℝ) ^ 3 / ((Metric.lt_volume_convexHull.c 3 : ℝ) * (δ : ℝ) ^ 3)) ^ ϖ)) := by
    rw [ENNReal.one_le_ofReal]
    have := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
      (nonempty_biasedFactorization.one_le_range_ratio (dim := 3) hδ0 hδ1 hϖ hcard)
    linarith
  have hB : (2 : ENNReal) ≤ ENNReal.ofReal (1 + Real.logb 2 (1 / (δ : ℝ))) := by
    have h2 : (2 : ℝ) ≤ 1 / (δ : ℝ) := by
      rw [le_div_iff₀ hδr]; linarith
    have hl : (1 : ℝ) ≤ Real.logb 2 (1 / (δ : ℝ)) := by
      have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by norm_num) h2
      rwa [Real.logb_self_eq_one (by norm_num)] at this
    have : (2 : ENNReal) = ENNReal.ofReal 2 := by simp
    rw [this]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc (2 : ENNReal) = 1 * 2 := (one_mul 2).symm
    _ ≤ 1 * (ENNReal.ofReal (1 + Real.logb 2 (1 / (δ : ℝ)))) ^ 3 := by
        gcongr
        calc (2 : ENNReal) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) (by norm_num)
          _ ≤ (ENNReal.ofReal (1 + Real.logb 2 (1 / (δ : ℝ)))) ^ 3 := by gcongr
    _ ≤ nonempty_biasedFactorization.L 3 card δ ϖ := by
        unfold nonempty_biasedFactorization.L
        gcongr

/-! ## The counterexample -/

/-- **G3, red half.**  At every `δ ≤ 1/64` and every bias `ϖ > 0` there are a family `s` (in
`B₁`, thickness `≥ δ`, nonempty — every hypothesis of `nonempty_biasedFactorization`) and a
subfamily `s'` satisfying **every clause of that theorem's conclusion** (mass retention at its own
loss `L`, a biased factorization at its own constant `C`) with `Δ_max(s') ≤ 1` and
`Δ_max(s) ≥ ⌊1/(24δ)⌋`.  So no `Δ_max`-retention at any subpolynomial rate can be a consequence
of the theorem's conclusion: the retained subfamily may lose `Δ_max` by the polynomial factor
`δ^{-1}` while keeping the volume. -/
theorem not_biasedFactorization_retains_maxDensity {ϖ : ℝ} (hϖ : 0 < ϖ) {δ : NNReal}
    (hδ0 : 0 < δ) (hδ : (δ : ℝ) ≤ 1 / 64) :
    ∃ (s s' : Finset (ℕ ⊕ ℕ)),
      s.Nonempty ∧
      (∀ i ∈ s, (redBody δ i).carrier ⊆ Metric.closedBall (0 : E3) 1) ∧
      (∀ i ∈ s, (δ : ENNReal) ≤ Metric.ethickness.scale ℝ (redBody δ i).carrier) ∧
      s' ⊆ s ∧
      (∑ i ∈ s, volume (redBody δ i).carrier
        ≤ nonempty_biasedFactorization.L (Module.finrank ℝ E3) s.card δ ϖ
          * ∑ i ∈ s', volume (redBody δ i).carrier) ∧
      Nonempty (BiasedFactorization s' (redBody δ) ConvexSpaceBody.closedUnitBall ϖ
        (nonempty_biasedFactorization.C (Module.finrank ℝ E3) ϖ)) ∧
      Kakeya.maxDensity s' (redBody δ) ≤ 1 ∧
      ((⌊1 / (24 * (δ : ℝ))⌋₊ : ℕ) : ENNReal) ≤ Kakeya.maxDensity s (redBody δ) := by
  classical
  have hδr : (0 : ℝ) < δ := hδ0
  have hfr : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
  set k : ℕ := ⌊1 / (24 * (δ : ℝ))⌋₊ with hk
  have hkle : (k : ℝ) ≤ 1 / (24 * (δ : ℝ)) := Nat.floor_le (by positivity)
  have hk2 : 2 ≤ k := by
    rw [hk]
    refine Nat.le_floor ?_
    rw [le_div_iff₀ (by positivity)]
    push_cast
    linarith
  have hkpos : 0 < k := by omega
  -- the index sets
  set A : Finset (ℕ ⊕ ℕ) := (Finset.range k).map ⟨Sum.inl, Sum.inl_injective⟩ with hA
  set B : Finset (ℕ ⊕ ℕ) := (Finset.range k).map ⟨Sum.inr, Sum.inr_injective⟩ with hB
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [hA, hB, Finset.mem_map, Function.Embedding.coeFn_mk] at hxA hxB
    obtain ⟨a, -, rfl⟩ := hxA
    obtain ⟨b, -, hb⟩ := hxB
    exact Sum.inl_ne_inr hb.symm
  have hcardA : A.card = k := by simp [hA]
  have hcardB : B.card = k := by simp [hB]
  have hball : ∀ i ∈ A ∪ B, (redBody δ i).carrier ⊆ Metric.closedBall (0 : E3) 1 := by
    intro i hi
    rcases i with n | n
    · rw [redBody_inl]
      exact redTube_carrier_subset_ball δ (by linarith)
    · rw [redBody_inr]
      have hn : n < k := by
        rcases Finset.mem_union.mp hi with h | h
        · simp [hA] at h
        · simpa [hB] using h
      refine redLeaf_carrier_subset_ball δ n ?_
      have hnk : (n : ℝ) ≤ k := by exact_mod_cast hn.le
      have : 3 * (δ : ℝ) * n ≤ 1 / 8 := by
        calc 3 * (δ : ℝ) * n ≤ 3 * (δ : ℝ) * k := by gcongr
          _ ≤ 3 * (δ : ℝ) * (1 / (24 * (δ : ℝ))) := by gcongr
          _ = 1 / 8 := by field_simp; ring
      linarith
  have hmaxB : Kakeya.maxDensity B (redBody δ) ≤ 1 := by
    refine maxDensity_le_one_of_pairwiseDisjoint' _ _ ?_
    intro i hi j hj hij
    simp only [hB, Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image,
      Finset.mem_coe] at hi hj
    obtain ⟨n, -, rfl⟩ := hi
    obtain ⟨m, -, rfl⟩ := hj
    have hnm : n ≠ m := fun h => hij (by rw [h])
    exact disjoint_redLeaf hδ0 hnm
  have hvpos : 0 < volume (redTube δ).carrier := by
    refine lt_of_lt_of_le ?_ (Tube.le_volume (redTube δ))
    have hc := Tube.le_volume.c_pos (Module.finrank ℝ E3)
    refine ENNReal.mul_pos ?_ ?_
    · simpa using ne_of_gt hc
    · simp only [ne_eq, pow_eq_zero_iff', not_and, not_not]
      intro h0
      exact absurd (by exact_mod_cast h0 : δ = 0) (ne_of_gt hδ0)
  have hvtop : volume (redTube δ).carrier ≠ ⊤ :=
    (redTube δ).toConvexSpaceBody.isCompact.measure_ne_top
  have hvol : ∀ i, volume (redBody δ i).carrier = volume (redTube δ).carrier := by
    intro i
    rcases i with n | n
    · rfl
    · exact Tube.volume_carrier_eq_volume_carrier (redLeaf δ n) (redTube δ)
  refine ⟨A ∪ B, B, ?_, hball, ?_, Finset.subset_union_right, ?_, ?_, hmaxB, ?_⟩
  · -- nonempty
    refine ⟨Sum.inl 0, Finset.mem_union_left _ ?_⟩
    simp [hA, hkpos]
  · -- thickness at least `δ`
    intro i _
    rcases i with n | n
    · exact Tube.le_ethickness_scale (redTube δ)
    · exact Tube.le_ethickness_scale (redLeaf δ n)
  · -- mass retention at the theorem's own loss
    have hsumA : ∑ i ∈ A, volume (redBody δ i).carrier = k * volume (redTube δ).carrier := by
      rw [Finset.sum_congr rfl (fun i _ => hvol i), Finset.sum_const, hcardA, nsmul_eq_mul]
    have hsumB : ∑ i ∈ B, volume (redBody δ i).carrier = k * volume (redTube δ).carrier := by
      rw [Finset.sum_congr rfl (fun i _ => hvol i), Finset.sum_const, hcardB, nsmul_eq_mul]
    rw [Finset.sum_union hAB, hsumA, hsumB, hfr]
    have hL := two_le_biasedL hδ0 (hδ.trans (by norm_num)) hϖ (card := (A ∪ B).card)
      (Finset.card_pos.mpr ⟨Sum.inl 0, Finset.mem_union_left _ (by simp [hA, hkpos])⟩)
    calc (k : ENNReal) * volume (redTube δ).carrier + k * volume (redTube δ).carrier
        = 2 * (k * volume (redTube δ).carrier) := by ring
      _ ≤ nonempty_biasedFactorization.L 3 (A ∪ B).card δ ϖ
          * (k * volume (redTube δ).carrier) := by gcongr
  · -- the biased factorization: singleton parts
    rw [hfr]
    set parts0 : Finset (Finset (ℕ ⊕ ℕ)) := B.image (fun i => ({i} : Finset (ℕ ⊕ ℕ)))
      with hparts0
    have hdisj0 : (parts0 : Set (Finset (ℕ ⊕ ℕ))).PairwiseDisjoint id := by
      intro t ht t' ht' htt'
      simp only [hparts0, Finset.coe_image, Set.mem_image, Finset.mem_coe] at ht ht'
      obtain ⟨i, -, rfl⟩ := ht
      obtain ⟨j, -, rfl⟩ := ht'
      have hij : i ≠ j := fun h => htt' (by rw [h])
      exact Finset.disjoint_singleton.mpr hij
    have hsup0 : parts0.sup id = B := by
      ext i
      simp only [Finset.mem_sup, hparts0, Finset.mem_image, id]
      constructor
      · rintro ⟨t, ⟨j, hj, rfl⟩, hi⟩
        rw [Finset.mem_singleton] at hi
        rw [hi]; exact hj
      · intro hi
        exact ⟨{i}, ⟨i, hi, rfl⟩, Finset.mem_singleton_self i⟩
    set P : Finpartition B := (Finpartition.ofPairwiseDisjoint parts0 hdisj0).copy hsup0 with hP
    have hPparts : P.parts = parts0.erase ⊥ := rfl
    have hmem : ∀ t ∈ P.parts, ∃ n, n < k ∧ t = {Sum.inr n} := by
      intro t ht
      rw [hPparts, Finset.mem_erase] at ht
      obtain ⟨-, ht⟩ := ht
      simp only [hparts0, Finset.mem_image] at ht
      obtain ⟨i, hi, rfl⟩ := ht
      simp only [hB, Finset.mem_map, Function.Embedding.coeFn_mk] at hi
      obtain ⟨n, hn, rfl⟩ := hi
      exact ⟨n, Finset.mem_range.mp hn, rfl⟩
    have hC2 : (2 : ENNReal) ≤ (nonempty_biasedFactorization.C 3 ϖ : ENNReal) :=
      two_le_biasedC hϖ.le
    have hC1 : (1 : ENNReal) ≤ (nonempty_biasedFactorization.C 3 ϖ : ENNReal) :=
      le_trans (by norm_num) hC2
    have hBvol : volume (ConvexSpaceBody.closedUnitBall (E := E3)).carrier ≠ ⊤ :=
      ConvexSpaceBody.closedUnitBall.isCompact.measure_ne_top
    have hcont : ∀ i ∈ B, redBody δ i ≤ ConvexSpaceBody.closedUnitBall := fun i hi =>
      SetLike.coe_subset_coe.mpr (hball i (Finset.mem_union_right _ hi))
    -- the density of a singleton inside its own body is `1`
    have hself : ∀ i, Kakeya.densityIn {i} (redBody δ) (redBody δ i) = 1 := by
      intro i
      unfold Kakeya.densityIn
      rw [Finset.filter_singleton, if_pos le_rfl, Finset.sum_singleton]
      rw [hvol i]
      exact ENNReal.div_self hvpos.ne' hvtop
    -- and inside any body it is at most `1`
    have hle1 : ∀ i K, Kakeya.densityIn {i} (redBody δ) K ≤ 1 := by
      intro i K
      unfold Kakeya.densityIn
      by_cases h : redBody δ i ≤ K
      · rw [Finset.filter_singleton, if_pos h, Finset.sum_singleton]
        refine ENNReal.div_le_of_le_mul ?_
        rw [one_mul]
        exact measure_mono (SetLike.coe_subset_coe.mpr h)
      · rw [Finset.filter_singleton, if_neg h, Finset.sum_empty, ENNReal.zero_div]
        exact zero_le
    have hratio_le : ∀ i ∈ B, (volume (redBody δ i).carrier
        / volume (ConvexSpaceBody.closedUnitBall (E := E3)).carrier) ≤ 1 := by
      intro i hi
      refine ENNReal.div_le_of_le_mul ?_
      rw [one_mul]
      exact measure_mono (SetLike.coe_subset_coe.mpr (hcont i hi))
    refine ⟨{ P with
      contained := hcont
      densityIn_le_biased := ?_
      maxDensity_le_densityIn_biased := ?_
      isKatzTao := ?_
      simDims := ?_ }⟩
    · intro t ht K
      obtain ⟨n, -, rfl⟩ := hmem t ht
      rw [Finset.convexHull_biUnion_singleton, hself]
      by_cases h : redBody δ (Sum.inr n) ≤ K
      · have h1 : (1 : ENNReal) ≤ volume K.carrier / volume (redBody δ (Sum.inr n)).carrier := by
          rw [ENNReal.le_div_iff_mul_le (Or.inl (by rw [hvol]; exact hvpos.ne'))
            (Or.inl (by rw [hvol]; exact hvtop)), one_mul]
          exact measure_mono (SetLike.coe_subset_coe.mpr h)
        have h2 : (1 : ENNReal)
            ≤ (volume K.carrier / volume (redBody δ (Sum.inr n)).carrier) ^ ϖ := by
          rw [← ENNReal.one_rpow ϖ]
          exact ENNReal.rpow_le_rpow h1 hϖ.le
        calc Kakeya.densityIn {Sum.inr n} (redBody δ) K ≤ 1 := hle1 _ _
          _ = 1 * 1 * 1 := by norm_num
          _ ≤ _ := by gcongr
      · unfold Kakeya.densityIn
        rw [Finset.filter_singleton, if_neg h, Finset.sum_empty, ENNReal.zero_div]
        exact zero_le
    · intro t ht
      obtain ⟨n, hn, rfl⟩ := hmem t ht
      rw [Finset.convexHull_biUnion_singleton, hself]
      have hnB : Sum.inr n ∈ B := by simp [hB, hn]
      have hinv : (nonempty_biasedFactorization.C 3 ϖ : ENNReal)⁻¹ ≤ 1 :=
        ENNReal.inv_le_one.mpr hC1
      have hr : (volume (redBody δ (Sum.inr n)).carrier
          / volume (ConvexSpaceBody.closedUnitBall (E := E3)).carrier) ^ ϖ ≤ 1 := by
        rw [← ENNReal.one_rpow ϖ]
        exact ENNReal.rpow_le_rpow (hratio_le _ hnB) hϖ.le
      calc _ ≤ (1 : ENNReal) * 1 * 1 := by gcongr
        _ = 1 := by norm_num
    · intro t ht
      obtain ⟨n, hn, rfl⟩ := hmem t ht
      rw [IsKatzTao_def, Finset.convexHull_biUnion_singleton]
      have hnB : Sum.inr n ∈ B := by simp [hB, hn]
      have hpd : (P.parts : Set (Finset (ℕ ⊕ ℕ))).PairwiseDisjoint
          (fun t' => (t'.convexHull_biUnion (redBody δ)).carrier) := by
        intro t₁ ht₁ t₂ ht₂ hne
        obtain ⟨n₁, -, rfl⟩ := hmem t₁ ht₁
        obtain ⟨n₂, -, rfl⟩ := hmem t₂ ht₂
        have hn12 : n₁ ≠ n₂ := fun h => hne (by rw [h])
        change Disjoint (({Sum.inr n₁} : Finset (ℕ ⊕ ℕ)).convexHull_biUnion (redBody δ)).carrier
          (({Sum.inr n₂} : Finset (ℕ ⊕ ℕ)).convexHull_biUnion (redBody δ)).carrier
        rw [Finset.convexHull_biUnion_singleton, Finset.convexHull_biUnion_singleton]
        exact disjoint_redLeaf hδ0 hn12
      refine (maxDensity_le_one_of_pairwiseDisjoint' _ _ hpd).trans ?_
      have hr : (1 : ENNReal) ≤ (volume (redBody δ (Sum.inr n)).carrier
          / volume (ConvexSpaceBody.closedUnitBall (E := E3)).carrier) ^ (-ϖ) := by
        rw [ENNReal.rpow_neg, ENNReal.one_le_inv, ← ENNReal.one_rpow ϖ]
        exact ENNReal.rpow_le_rpow (hratio_le _ hnB) hϖ.le
      exact one_le_mul hC1 hr
    · intro t ht t' ht'
      obtain ⟨n, -, rfl⟩ := hmem t ht
      obtain ⟨m, -, rfl⟩ := hmem t' ht'
      rw [Finset.convexHull_biUnion_singleton, Finset.convexHull_biUnion_singleton]
      have heth : ∀ j, Metric.ethickness ℝ (redBody δ (Sum.inr j)).carrier
          = Metric.ethickness ℝ (redTube δ).carrier := by
        intro j
        funext l
        rw [redBody_inr]
        change Metric.ethickness ℝ (redLeaf δ j).carrier l = _
        rw [redLeaf, translate_carrier_eq_image, ethickness_constVAdd_image']
      rw [heth n, heth m]
      intro l
      rw [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul]
      exact le_mul_of_one_le_left zero_le hC1
  · -- `Δ_max(s) ≥ k`: the `k` copies of the central tube fill it `k` times
    refine le_trans ?_ (Kakeya.le_maxDensity (A ∪ B) (redBody δ) (redTube δ).toConvexSpaceBody)
    unfold Kakeya.densityIn
    rw [ENNReal.le_div_iff_mul_le (Or.inl hvpos.ne') (Or.inl hvtop)]
    have hAsub : A ⊆ {i ∈ A ∪ B | redBody δ i ≤ (redTube δ).toConvexSpaceBody} := by
      intro i hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_union_left _ hi, ?_⟩
      simp only [hA, Finset.mem_map, Function.Embedding.coeFn_mk] at hi
      obtain ⟨n, -, rfl⟩ := hi
      rw [redBody_inl]
    calc (k : ENNReal) * volume (redTube δ).carrier
        = ∑ i ∈ A, volume (redBody δ i).carrier := by
          rw [Finset.sum_congr rfl (fun i hi => ?_), Finset.sum_const, hcardA, nsmul_eq_mul]
          simp only [hA, Finset.mem_map, Function.Embedding.coeFn_mk] at hi
          obtain ⟨n, -, rfl⟩ := hi
          rfl
      _ ≤ ∑ i ∈ {i ∈ A ∪ B | redBody δ i ≤ (redTube δ).toConvexSpaceBody},
            volume (redBody δ i).carrier :=
          Finset.sum_le_sum_of_subset_of_nonneg hAsub (fun _ _ _ => zero_le)

end Kakeya.ML2Core

end
