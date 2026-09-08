/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.PartialEstimates

/-!
# The monotone envelope of the admissible drops of Main Lemma 2

GWZ Main Lemma 2 (`Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate`) asks for a
*single* function `ν : ℝ → ℝ`, monotone and positive on `(0,1]`, such that `K_KT(β)` and `K_F(β)`
imply `K_KT(β - ν β)` for every `β ∈ (0,1]`.  Two quantifier orders are hidden in that statement
and neither is present in the source:

* `ν` is produced **before the accuracy `ε`** hidden inside `Kakeya.KatzTaoEstimate`.  GWZ open
  their proof with "fix `ε > 0`" and close it with "`ν = η₁`".  Prof. Hong Wang's clarification
  (2026-08-30) resolves the discrepancy: it is a typo in the published proof, and the correct
  reading applies Theorem 7.3 with an **absolute** accuracy `ε₀`, so that the whole chain
  `ε₀ → ε₁ → ε₂ → (N, η_i) → ν` depends on `β` only.  See
  `Kakeya/DimensionThree/MainLemma2/Reduction/Core.lean`.
* `ν` is produced **before `β`**, and must be monotone in it.

This file handles the second of the two, by the same device that
`Kakeya/DimensionThree/MainLemma1/Envelope.lean` uses for Part (A): the set of admissible drops
above a threshold is downward closed in the drop and increasing in the threshold, so the halved
supremum is a monotone, positive, admissible drop function.  What is left over is one hypothesis,

```
∀ β₀ ∈ Set.Ioc 0 1, (Kakeya.ML2Reduction.katzTaoDropSet β₀).Nonempty
```

("above every threshold there is *one* drop that works for every exponent in `[β₀,1]`"), which is
the honest content of the monotonicity requirement.

The file also records the accuracy-restriction device
(`Kakeya.ML2Reduction.katzTaoEstimate_of_forall_le`: it suffices to produce the witnesses of
`Kakeya.KatzTaoEstimate` at small `ε`) and the two pieces of `[0,∞]` arithmetic by which the two
alternatives of the Section 9 dichotomy are converted into a drop in the exponent of `|𝕋|`.

Everything in this file is proved.
-/

@[expose] public section

open MeasureTheory Topology ConvexSpaceBody Filter ShadedBody

namespace Kakeya

namespace ML2Reduction

universe u

/-! ### The drop set and its monotone envelope -/

/-- The set of **admissible uniform drops above the threshold `β₀`**: those `c ∈ (0,1]` such that
for *every* exponent `β ∈ [β₀, 1]`, the two partial estimates `K_KT(β)` and `K_F(β)` imply the
improved Katz–Tao estimate `K_KT(β - c)`.

As in `Kakeya.frostmanStepSet`, the two partial estimates sit *inside* the defining condition
rather than being hypotheses of the definition; this is what lets the drop be produced before any
family of tubes, and indeed before `β`, exists.

Quantifying over all `β ∈ [β₀,1]` rather than over `β₀` alone is what makes the set increasing in
`β₀` (`Kakeya.ML2Reduction.katzTaoDropSet_subset`), hence what makes the envelope monotone. -/
def katzTaoDropSet (β₀ : ℝ) : Set ℝ :=
  {c | c ∈ Set.Ioc (0 : ℝ) 1 ∧ ∀ β ∈ Set.Icc β₀ 1,
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
    FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
    KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - c)}

/-- The drop set is downward closed: a smaller drop lands at a larger exponent, and
`Kakeya.KatzTaoEstimate.mono` is monotone in the exponent. -/
theorem katzTaoDropSet_downwardClosed {β₀ c c' : ℝ}
    (hc : c ∈ katzTaoDropSet.{u} β₀) (hc'_pos : 0 < c') (hc'_le : c' ≤ c) :
    c' ∈ katzTaoDropSet.{u} β₀ := by
  obtain ⟨hc_Ioc, hc_forall⟩ := hc
  refine ⟨⟨hc'_pos, hc'_le.trans hc_Ioc.2⟩, ?_⟩
  intro β hβ hKT hKF
  exact KatzTaoEstimate.mono (sub_le_sub_left hc'_le β) (hc_forall β hβ hKT hKF)

/-- The drop set is increasing in the threshold: raising `β₀` shrinks the interval `[β₀,1]` that
the defining condition quantifies over. -/
theorem katzTaoDropSet_subset {β₀ β₁ : ℝ} (h : β₀ ≤ β₁) :
    katzTaoDropSet.{u} β₀ ⊆ katzTaoDropSet.{u} β₁ := by
  intro c hc
  obtain ⟨hc_Ioc, hc_forall⟩ := hc
  exact ⟨hc_Ioc, fun β hβ => hc_forall β (Set.Icc_subset_Icc h le_rfl hβ)⟩

/-- **The monotone envelope, membership form.**  If above every threshold `β₀ ∈ (0,1]` there is at
least one admissible uniform drop, then there is a single drop function `ν`, monotone and strictly
positive on `(0,1]`, whose value at `β` is itself an admissible uniform drop above `β`.

The witness is `ν β = sSup (katzTaoDropSet β) / 2`; halving the supremum is what makes the value
attained, through `Kakeya.ML2Reduction.katzTaoDropSet_downwardClosed`. -/
theorem exists_monotoneOn_mem_katzTaoDropSet
    (hne : ∀ β₀ ∈ Set.Ioc (0 : ℝ) 1, (katzTaoDropSet.{u} β₀).Nonempty) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧ (∀ β ∈ Set.Ioc (0 : ℝ) 1, 0 < ν β) ∧
      (∀ β ∈ Set.Ioc (0 : ℝ) 1, ν β ∈ katzTaoDropSet.{u} β) := by
  set ν := fun β : ℝ => sSup (katzTaoDropSet.{u} β) / 2 with hν_def
  have hbdd : ∀ β : ℝ, BddAbove (katzTaoDropSet.{u} β) := fun β => ⟨1, fun c hc => hc.1.2⟩
  refine ⟨ν, ?_, ?_, ?_⟩
  · intro β₁ hβ₁ β₂ _ hβ₁₂
    have hcsSup : sSup (katzTaoDropSet.{u} β₁) ≤ sSup (katzTaoDropSet.{u} β₂) :=
      csSup_le_csSup (hbdd β₂) (hne β₁ hβ₁) (katzTaoDropSet_subset hβ₁₂)
    simp only [hν_def]
    linarith
  · intro β hβ
    obtain ⟨c, hc⟩ := hne β hβ
    have hle : c ≤ sSup (katzTaoDropSet.{u} β) := le_csSup (hbdd β) hc
    have hcpos : 0 < c := hc.1.1
    simp only [hν_def]
    linarith
  · intro β hβ
    obtain ⟨c, hc⟩ := hne β hβ
    have hle_c_sup : c ≤ sSup (katzTaoDropSet.{u} β) := le_csSup (hbdd β) hc
    have hcpos : 0 < c := hc.1.1
    have hMpos : 0 < sSup (katzTaoDropSet.{u} β) := lt_of_lt_of_le hcpos hle_c_sup
    have h_exists : ∃ c' ∈ katzTaoDropSet.{u} β, sSup (katzTaoDropSet.{u} β) / 2 < c' := by
      by_contra! h
      have h_sup_le : sSup (katzTaoDropSet.{u} β) ≤ sSup (katzTaoDropSet.{u} β) / 2 :=
        csSup_le (hne β hβ) (fun c' hc' => h c' hc')
      linarith
    obtain ⟨c', hc', hlt⟩ := h_exists
    have hmem : sSup (katzTaoDropSet.{u} β) / 2 ∈ katzTaoDropSet.{u} β :=
      katzTaoDropSet_downwardClosed hc' (by linarith) hlt.le
    simpa [hν_def] using hmem

/-- **The monotone envelope, in exactly the shape of GWZ Main Lemma 2.**

This is `Kakeya.KatzTaoEstimate.katzTaoEstimate_sub_of_frostmanEstimate` with the mathematics
replaced by the single hypothesis `hne`. -/
theorem katzTaoEstimate_sub_of_nonempty_katzTaoDropSet
    (hne : ∀ β₀ ∈ Set.Ioc (0 : ℝ) 1, (katzTaoDropSet.{u} β₀).Nonempty) :
    ∃ ν : ℝ → ℝ, MonotoneOn ν (Set.Ioc 0 1) ∧
      (∀ β : ℝ, 0 < β → β ≤ 1 → 0 < ν β) ∧
      ∀ β : ℝ, 0 < β → β ≤ 1 →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
        KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) (β - ν β) := by
  obtain ⟨ν, hmono, hpos, hmem⟩ := exists_monotoneOn_mem_katzTaoDropSet.{u} hne
  refine ⟨ν, hmono, fun β hβ hβ1 => hpos β ⟨hβ, hβ1⟩, ?_⟩
  intro β hβ hβ1 hKT hKF
  exact (hmem β ⟨hβ, hβ1⟩).2 β ⟨le_rfl, hβ1⟩ hKT hKF

/-! ### The accuracy-restriction device -/

section Accuracy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **It is enough to produce the witnesses of `Kakeya.KatzTaoEstimate` at small accuracies.**

The conclusion of `Kakeya.KatzTaoEstimate` weakens as `ε` grows (`δ ≤ 1`, so
`δ ^ (-ε') ≤ δ ^ (-ε)` for `ε' ≤ ε`), so a witness `η` at accuracy `min ε ε♯` serves at accuracy
`ε` as well.

This is the device that lets the Section 9 chain be run once, at the *absolute* accuracy
`ε₀ = ε₀(β)` of Prof. Wang's clarification, instead of once per `ε`. -/
theorem katzTaoEstimate_of_forall_le (E) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {γ εSharp : ℝ} (hεSharp : 0 < εSharp)
    (h : ∀ ε > (0 : ℝ), ε ≤ εSharp → ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) (δ ^ (- η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        ∑ i ∈ s, volume (T i).shade
          ≤ δ ^ (- ε) * s.card ^ γ * volume (⋃ i ∈ s, (T i).shade)) :
    KatzTaoEstimate.{u} E γ := by
  intro ε hε
  obtain ⟨η, hη, hmain⟩ := h (min ε εSharp) (lt_min hε hεSharp) (min_le_right _ _)
  refine ⟨η, hη, ?_⟩
  have hδ1 : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, δ ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hδ
    exact hδ.2.le
  filter_upwards [hmain, hδ1] with δ hδmain hδle1
  intro ι s T hball hKT hfull
  refine (hδmain s T hball hKT hfull).trans ?_
  have hcoe : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδle1
  have hpow : (δ : ENNReal) ^ (-min ε εSharp) ≤ (δ : ENNReal) ^ (-ε) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hcoe (by simp)
  gcongr

end Accuracy

/-! ### The two arithmetic conversions of the Section 9 dichotomy -/

/-- `δ ^ (-γ) ≤ N ^ γ` when `δ⁻¹ ≤ N` and `γ ≥ 0`: the elementary form of "a bound at an absolute
accuracy is paid for by the size of the family". -/
theorem rpow_neg_le_natCast_rpow {δ : NNReal} (hδ0 : 0 < δ) {γ : ℝ} (hγ : 0 ≤ γ) {N : ℕ}
    (hN : ((δ : ℝ))⁻¹ ≤ (N : ℝ)) :
    (δ : ENNReal) ^ (-γ) ≤ (N : ENNReal) ^ γ := by
  have hδR : (0 : ℝ) < (δ : ℝ) := hδ0
  have hδinv : ((δ : ENNReal))⁻¹ ≤ (N : ENNReal) := by
    have h1 : ((δ : ENNReal))⁻¹ = ENNReal.ofReal ((δ : ℝ))⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hδR, ENNReal.ofReal_coe_nnreal]
    have h2 : ((N : ℕ) : ENNReal) = ENNReal.ofReal ((N : ℕ) : ℝ) := by
      simp
    rw [h1, h2]
    exact ENNReal.ofReal_le_ofReal hN
  calc (δ : ENNReal) ^ (-γ) = ((δ : ENNReal))⁻¹ ^ γ := by
        rw [ENNReal.inv_rpow, ENNReal.rpow_neg]
    _ ≤ (N : ENNReal) ^ γ := ENNReal.rpow_le_rpow hδinv hγ

/-- **Alternative (i) of the Section 9 dichotomy, paid for by the size of `𝕋`.**

Theorem 7.3(B) is applied at the *absolute* accuracy `ε₀ = ε₀(β)`, so the bound it returns,
`μ ≤ δ ^ (-ε₀)`, is generally **weaker** than the goal `μ ≤ δ ^ (-ε) * |𝕋| ^ γ` when `ε < ε₀`.
The only currency available is `|𝕋| ^ γ`, and it suffices exactly when `|𝕋| ≥ δ⁻¹`, which forces
`|𝕋| ^ γ ≥ δ ^ (-γ)`, together with the budget `ε₀ ≤ ε + γ`.

This is the sole place in the reduction where the lower bound `|𝕋| > δ⁻¹` of Prof. Wang's
clarification is spent. -/
theorem le_rpow_mul_rpow_of_card_ge {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {μ : ENNReal}
    {ε ε₀ γ : ℝ} {N : ℕ} (hγ : 0 ≤ γ) (hbudget : ε₀ ≤ ε + γ)
    (hN : ((δ : ℝ))⁻¹ ≤ (N : ℝ)) (hμ : μ ≤ (δ : ENNReal) ^ (-ε₀)) :
    μ ≤ (δ : ENNReal) ^ (-ε) * (N : ENNReal) ^ γ := by
  have hδE0 : (0 : ENNReal) < (δ : ENNReal) := by exact_mod_cast hδ0
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  calc μ ≤ (δ : ENNReal) ^ (-ε₀) := hμ
    _ ≤ (δ : ENNReal) ^ (-(ε + γ)) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
    _ = (δ : ENNReal) ^ (-ε) * (δ : ENNReal) ^ (-γ) := by
        rw [← ENNReal.rpow_add _ _ hδE0.ne' ENNReal.coe_ne_top]
        ring_nf
    _ ≤ (δ : ENNReal) ^ (-ε) * (N : ENNReal) ^ γ := by
        gcongr
        exact rpow_neg_le_natCast_rpow hδ0 hγ hN

/-- **Alternative (ii) of the Section 9 dichotomy: a positive `δ`-gain becomes a drop in the
exponent of `|𝕋|`.**

The window branch returns `μ ≤ δ ^ g * |𝕋| ^ β` with `g = g(β) > 0`, and the crude counting bound
`|𝕋| ≤ δ ^ (-K)` converts `|𝕋| ^ c` into `δ ^ (-K c)`; the budget `K * c ≤ g + ε` closes it.

No lower bound on `|𝕋|` is needed here — this is the branch that is genuinely improved, and its
gain is what the drop `ν(β)` is made of. -/
theorem le_rpow_mul_rpow_of_gain {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {μ : ENNReal}
    {ε g c β K : ℝ} {N : ℕ} (hN1 : 1 ≤ N) (hc : 0 ≤ c)
    (hbudget : K * c ≤ g + ε)
    (hcard : (N : ℝ) ≤ ((δ : ℝ)) ^ (-K))
    (hμ : μ ≤ (δ : ENNReal) ^ g * (N : ENNReal) ^ β) :
    μ ≤ (δ : ENNReal) ^ (-ε) * (N : ENNReal) ^ (β - c) := by
  have hδR : (0 : ℝ) < (δ : ℝ) := hδ0
  have hδE0 : (0 : ENNReal) < (δ : ENNReal) := by exact_mod_cast hδ0
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hNE0 : (0 : ENNReal) < (N : ENNReal) := by exact_mod_cast hN1
  have hNEtop : ((N : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top N
  -- `N ≤ δ ^ (-K)` in `[0,∞]`
  have hbase : (N : ENNReal) ≤ (δ : ENNReal) ^ (-K) := by
    have h1 : (δ : ENNReal) ^ (-K) = ENNReal.ofReal (((δ : ℝ)) ^ (-K)) := by
      rw [← ENNReal.ofReal_rpow_of_pos hδR, ENNReal.ofReal_coe_nnreal]
    have h2 : ((N : ℕ) : ENNReal) = ENNReal.ofReal ((N : ℕ) : ℝ) := by simp
    rw [h1, h2]
    exact ENNReal.ofReal_le_ofReal hcard
  have hNc : (N : ENNReal) ^ c ≤ (δ : ENNReal) ^ (-(K * c)) := by
    calc (N : ENNReal) ^ c ≤ ((δ : ENNReal) ^ (-K)) ^ c := ENNReal.rpow_le_rpow hbase hc
      _ = (δ : ENNReal) ^ (-(K * c)) := by
          rw [← ENNReal.rpow_mul]
          ring_nf
  have hsplit : (N : ENNReal) ^ β = (N : ENNReal) ^ (β - c) * (N : ENNReal) ^ c := by
    rw [← ENNReal.rpow_add _ _ hNE0.ne' hNEtop]
    ring_nf
  calc μ ≤ (δ : ENNReal) ^ g * (N : ENNReal) ^ β := hμ
    _ = (δ : ENNReal) ^ g * (N : ENNReal) ^ c * (N : ENNReal) ^ (β - c) := by
        rw [hsplit]; ring
    _ ≤ (δ : ENNReal) ^ g * (δ : ENNReal) ^ (-(K * c)) * (N : ENNReal) ^ (β - c) := by
        gcongr
    _ = (δ : ENNReal) ^ (g - K * c) * (N : ENNReal) ^ (β - c) := by
        rw [← ENNReal.rpow_add _ _ hδE0.ne' ENNReal.coe_ne_top]
        ring_nf
    _ ≤ (δ : ENNReal) ^ (-ε) * (N : ENNReal) ^ (β - c) := by
        have hstep : (δ : ENNReal) ^ (g - K * c) ≤ (δ : ENNReal) ^ (-ε) :=
          ENNReal.rpow_le_rpow_of_exponent_ge (x := (δ : ENNReal)) (y := g - K * c)
            (z := -ε) hδE1 (by linarith)
        exact mul_le_mul_right' hstep _

end ML2Reduction

end Kakeya
