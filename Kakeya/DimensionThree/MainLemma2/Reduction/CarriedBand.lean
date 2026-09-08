/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.BandSqueeze
public import Kakeya.DimensionThree.Plank.Prop66ARepaired
public import Kakeya.DimensionThree.MainLemma2.Reduction.AssemblyPointwise

/-!
# Carrying the cardinality band into the inducted statement

steps.

`Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy` derives Main Lemma 2's conclusion from two
inputs: the GWZ dichotomy on the band `δ⁻¹ ≤ |𝕋|`, and `Kakeya.ML2Assembly.SmallCard`, the
*complement* of that band.  `Kakeya.ML2Squeeze.forall_cut_circular` proves the complement is the
goal itself, at every threshold, so the reduction is circular; three repairs that **remove or
split on** the cardinality content have since been refuted, all (`Kakeya.ML2Squeeze.forall_cut_circular`, `Kakeya.ML2Squeeze.residue_of_banded`, and the
`GainOnly` line).

This file does the one thing that is not "remove or split": it **carries** the band into the
inducted statement, so there is no complement to discharge.

## What is proved

* `Kakeya.ML2Carried.CarriedBand` — `K_KT(γ)` with `δ⁻¹ ≤ |𝕋|` as a *hypothesis*, at the price of
  a density parameter `M` (the family is only `M·δ^{-η}` Katz--Tao) and the covariant conclusion
  `δ^{-ε} · M^{1-γ} · |𝕋|^γ`.
* `Kakeya.ML2Carried.katzTaoEstimate_of_carriedBand` — **Main Lemma 2's conclusion follows**, with
  no complement and no residue.  The transport is `R`-fold duplication with `R = ⌈δ⁻¹⌉`, and it is
  *lossless*: duplication multiplies the shade mass, the cardinality and the maximal density each
  by exactly `R`, leaves the union and the fullness alone, and `M^{1-γ}|𝕋|^γ` is the unique
  normalisation covariant for that scaling.
* `Kakeya.ML2Carried.carriedBand_of_katzTaoEstimate` — the converse, from **GWZ Lemma 3.7**
  (`Kakeya.KatzTaoEstimate.multiplicity_bound`, which is already `μ ≤ δ^{-ε}Δ_max^{1-γ}|𝕋|^γ` with
  no Katz--Tao hypothesis).  Hence `Kakeya.ML2Carried.carriedBand_iff`: the carried statement is
  the goal **re-encoded**, not strengthened.  The acceptance filter is applied to it explicitly in
  `Kakeya.ML2Carried.carriedBand_is_producer_of_goal`, and reported rather than hidden.
* `Kakeya.ML2Carried.katzTaoEstimateGE_of_carriedBand` — at `M = 1` the carried statement is
  exactly `Kakeya.ML2Squeeze.KatzTaoEstimateGE 1 γ`, what the GWZ route delivers.  So `M` is the
  entire distance from the route's output to the goal.

## Where it stops, exactly

The transport is applied to the dichotomy's two alternatives in
`Kakeya.ML2Carried.accuracy_branch_after_transport` and
`Kakeya.ML2Carried.gain_branch_after_transport`.  Both say the same thing: **a branch's closure
condition is invariant under the transport.**

* For the **gain** that is harmless: `Kakeya.ML2Carried.gain_branch_closes` discharges the
  invariant condition at the assembly's own `ε`-free budget `4c ≤ g`, using only the crude
  cardinality bound `|𝕋| ≤ δ^{-4}`.  The gain branch survives the re-encoding untouched.
* For the **accuracy** the invariant condition is a band on `|𝕋| / M`
  (`Kakeya.ML2Carried.accuracy_branch_closes_of_dedup_band`, whose budget `ε₀ ≤ ε + γ` is exactly
  `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy`'s `2c ≤ β`), and that is fatal.
  Read without the covariance factor the branch is **false**
  (`Kakeya.ML2Carried.not_strongAccuracyBand`, witnessed by `R` copies of one fully shaded central
  tube).  Read with it, its invariant closure condition is `δ^{-ε₀} ≤ δ^{-ε}|𝕋|^γ` on the
  *original* count — i.e. **the band on the de-duplicated count** — and at the image of a
  one-tube family this reads `ε₀ ≤ ε`
  (`Kakeya.ML2Carried.accuracy_branch_after_transport_fails`).  Since `ε₀` must be `ε`-free while
  `ε → 0`, it fails for every positive `ε₀`.

So the verdict of steps  is: **the carried-cardinality induction does yield Main Lemma 2 —
`Kakeya.ML2Carried.katzTaoEstimate_of_carriedBand` is the missing step, and it is unconditional —
but the GWZ dichotomy cannot produce `CarriedBand`, because the band its accuracy branch consumes
is a band on `|𝕋| / M`, which duplication provably leaves fixed.**  The obstruction is no longer
"the residue is the goal"; it is the single inequality `ε₀ ≤ ε`, which is the `ε`-freeness
tension of GWZ §9 (`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy'`) reappearing on the carried
side as a hard budget.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology

open Kakeya.ML2Squeeze (Space3)

namespace Kakeya.ML2Carried

universe u

section Duplication

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {ι : Type*}

/-- The index set of the `R`-fold duplicate of a family indexed by `s`. -/
def dupFinset (s : Finset ι) (R : ℕ) : Finset (ι × Fin R) := s ×ˢ Finset.univ

@[simp] theorem dupFinset_card (s : Finset ι) (R : ℕ) :
    (dupFinset s R).card = s.card * R := by
  simp [dupFinset]

@[simp] theorem mem_dupFinset {s : Finset ι} {R : ℕ} {p : ι × Fin R} :
    p ∈ dupFinset s R ↔ p.1 ∈ s := by
  simp [dupFinset]

/-- Summing a first-coordinate function over the duplicate multiplies the sum by `R`. -/
theorem sum_dupFinset {s : Finset ι} {R : ℕ} (f : ι → ENNReal) :
    ∑ p ∈ dupFinset s R, f p.1 = R * ∑ i ∈ s, f i := by
  classical
  rw [dupFinset, Finset.sum_product]
  simp [Finset.sum_const, ← Finset.sum_mul, mul_comm]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
/-- The union over the duplicate is the original union, provided `R ≠ 0`. -/
theorem iUnion_dupFinset {s : Finset ι} {R : ℕ} (hR : R ≠ 0) (g : ι → Set E) :
    ⋃ p ∈ dupFinset s R, g p.1 = ⋃ i ∈ s, g i := by
  have : Nonempty (Fin R) := ⟨⟨0, Nat.pos_of_ne_zero hR⟩⟩
  ext x
  simp only [Set.mem_iUnion, mem_dupFinset, exists_prop]
  constructor
  · rintro ⟨p, hp, hx⟩; exact ⟨p.1, hp, hx⟩
  · rintro ⟨i, hi, hx⟩
    exact ⟨(i, Classical.arbitrary (Fin R)), hi, hx⟩

/-- The Katz--Tao filter of a duplicate is the duplicate of the Katz--Tao filter. -/
theorem filter_dupFinset {s : Finset ι} {R : ℕ} (P : ι → Prop) [DecidablePred P] :
    (dupFinset s R).filter (fun p ↦ P p.1) = dupFinset (s.filter P) R := by
  ext p
  simp [mem_dupFinset, Finset.mem_filter]

/-- **Duplication scales the maximal density by exactly the duplication factor.**
Densities are sums of volumes over a containment filter, and duplicating repeats every
summand `R` times without changing which bodies are contained in a given `K`. -/
theorem isKatzTao_dupFinset {s : Finset ι} {R : ℕ} {W : ι → ConvexSpaceBody E} {C : ENNReal}
    (h : ConvexSpaceBody.IsKatzTao s W C) :
    ConvexSpaceBody.IsKatzTao (dupFinset s R) (fun p ↦ W p.1) ((R : ENNReal) * C) := by
  classical
  rw [ConvexSpaceBody.isKatzTao_iff]
  intro K
  have hfil : ((dupFinset s R).filter (fun p ↦ W p.1 ≤ K))
      = dupFinset (s.filter (fun i ↦ W i ≤ K)) R := by
    ext p; simp [mem_dupFinset, Finset.mem_filter]
  calc ∑ p ∈ (dupFinset s R).filter (fun p ↦ W p.1 ≤ K), volume (W p.1).carrier
      = ∑ p ∈ dupFinset (s.filter (fun i ↦ W i ≤ K)) R, volume (W p.1).carrier := by rw [hfil]
    _ = (R : ENNReal) * ∑ i ∈ s.filter (fun i ↦ W i ≤ K), volume (W i).carrier :=
        sum_dupFinset (fun i ↦ volume (W i).carrier)
    _ ≤ (R : ENNReal) * (C * volume K.carrier) := by
        gcongr
        exact (ConvexSpaceBody.isKatzTao_iff s W C).mp h K
    _ = (R : ENNReal) * C * volume K.carrier := by rw [mul_assoc]

/-- **Duplication does not change the fullness.**  Fullness is the ratio of the total shade mass
to the total carrier mass, and duplication multiplies both by `R`. -/
theorem fullness_dupFinset {s : Finset ι} {R : ℕ} (hR : R ≠ 0) (V : ι → ShadedBody E) :
    ShadedBody.fullness (dupFinset s R) (fun p ↦ V p.1) = ShadedBody.fullness s V := by
  have hR0 : (R : ENNReal) ≠ 0 := by exact_mod_cast hR
  have hRt : (R : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top R
  have h : ShadedBody.fullness' (dupFinset s R) (fun p ↦ V p.1)
      = ShadedBody.fullness' s V := by
    show (∑ p ∈ dupFinset s R, volume (V p.1).shade)
        / (∑ p ∈ dupFinset s R, volume (V p.1).carrier)
      = (∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier)
    rw [sum_dupFinset (fun i ↦ volume (V i).shade),
      sum_dupFinset (fun i ↦ volume (V i).carrier),
      ENNReal.mul_div_mul_left _ _ hR0 hRt]
  unfold ShadedBody.fullness
  rw [h]

end Duplication

/-! ## The inducted statement, with the cardinality lower bound carried -/

/-- **`K_KT(γ)` with the cardinality band `δ⁻¹ ≤ |𝕋|` carried in the hypothesis.**

`Kakeya.ML2Assembly.Dichotomy` — and, per Prof. Hong Wang's clarification of 2026-08-30, the
blueprint proof of Main Lemma 2 itself — is stated under the standing assumption
`δ⁻¹ ≤ |𝕋|`, which `Kakeya.KatzTaoEstimate` does not supply.  The existing reduction
discharges the *complement* of that assumption through `Kakeya.ML2Assembly.SmallCard`, and
`Kakeya.ML2Squeeze.forall_cut_circular` shows the complement is the goal itself, at every
threshold.

This predicate carries the band instead of splitting on it.  The price is one extra parameter:
the family is only asked to be `M · δ^{-η}` Katz--Tao, and the conclusion is weakened by
`M ^ (1 - γ)`.  Both changes are forced, and they are forced by the *same* scaling: an `R`-fold
duplication of a family multiplies the shade mass, the cardinality and the maximal density each
by exactly `R`, and leaves the union and the fullness alone
(`Kakeya.ML2Carried.sum_dupFinset`, `Kakeya.ML2Carried.dupFinset_card`,
`Kakeya.ML2Carried.isKatzTao_dupFinset`, `Kakeya.ML2Carried.iUnion_dupFinset`,
`Kakeya.ML2Carried.fullness_dupFinset`).  `M ^ (1-γ) · |𝕋| ^ γ` is the unique normalisation of
`|𝕋| ^ γ` that is covariant for that scaling, and `Kakeya.ML2Carried.katzTaoEstimate_of_carriedBand`
is the proof that covariance is exactly what removes the complement.

At `M = 1` this is `Kakeya.ML2Squeeze.KatzTaoEstimateGE 1 γ`, the banded estimate the GWZ route
delivers. -/
def CarriedBand (γ : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), η ≤ 1 ∧
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3) (M : ENNReal),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        1 ≤ M → M ≠ ⊤ →
        ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody)
          (M * (δ : ENNReal) ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
        ∑ i ∈ s, volume (T i).shade
          ≤ (δ : ENNReal) ^ (-ε) * M ^ (1 - γ) * (s.card : ENNReal) ^ γ
              * volume (⋃ i ∈ s, (T i).shade)

/-- The exponent identity behind the duplication transport: `M ^ (1-γ)` and `|𝕋| ^ γ` recombine
to a single factor of the duplication factor `R`. -/
theorem rpow_dup_cancel {R n : ℕ} {γ : ℝ} (hγ : 0 ≤ γ) (hR : R ≠ 0) :
    (R : ENNReal) ^ (1 - γ) * ((n * R : ℕ) : ENNReal) ^ γ
      = (R : ENNReal) * (n : ENNReal) ^ γ := by
  have hR0 : (R : ENNReal) ≠ 0 := by exact_mod_cast hR
  have hRt : (R : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top R
  have hcast : ((n * R : ℕ) : ENNReal) = (n : ENNReal) * (R : ENNReal) := by push_cast; ring
  rw [hcast, ENNReal.mul_rpow_of_nonneg _ _ hγ]
  calc (R : ENNReal) ^ (1 - γ) * ((n : ENNReal) ^ γ * (R : ENNReal) ^ γ)
      = ((R : ENNReal) ^ (1 - γ) * (R : ENNReal) ^ γ) * (n : ENNReal) ^ γ := by ring
    _ = (R : ENNReal) ^ ((1 : ℝ) - γ + γ) * (n : ENNReal) ^ γ := by
        rw [ENNReal.rpow_add _ _ hR0 hRt]
    _ = (R : ENNReal) * (n : ENNReal) ^ γ := by
        rw [show (1 : ℝ) - γ + γ = 1 by ring, ENNReal.rpow_one]

/-- **The carried induction yields Main Lemma 2's conclusion: no complement, no residue.**

`CarriedBand γ` implies the *unbanded* `K_KT(γ)`.  The transport is `R`-fold duplication with
`R = ⌈δ⁻¹⌉`: it moves an arbitrary family into the band `δ⁻¹ ≤ |𝕋|` and the loss is *exactly*
zero, because the duplication factor `R` that appears in the conclusion through
`M ^ (1-γ) · |𝕋| ^ γ` is the same `R` that multiplies the shade mass on the left.

This is the step `Kakeya.ML2Assembly.SmallCard` cannot take: a bare cardinality band is not
attainable by any transport, since `Kakeya.ML2Squeeze.forall_cut_circular` makes the complement
of *every* threshold equivalent to the goal.  What makes this one work is that duplication is
lossless simultaneously in all five quantities the hypothesis and the conclusion mention. -/
theorem katzTaoEstimate_of_carriedBand {γ : ℝ} (hγ : 0 ≤ γ) (h : CarriedBand.{u} γ) :
    Kakeya.KatzTaoEstimate.{u} Space3 γ := by
  intro ε hε
  obtain ⟨η, hη0, _hη1, hev⟩ := h ε hε
  refine ⟨η, hη0, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hδev hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  intro ι s T hball hKT hfull
  rcases Nat.eq_zero_or_pos s.card with hcard0 | hcardpos
  · rw [Finset.card_eq_zero.mp hcard0]
    simp
  -- the duplication factor
  have hδ0' : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  obtain ⟨R, hRpos, hRle⟩ : ∃ R : ℕ, 0 < R ∧ (δ : ℝ)⁻¹ ≤ (R : ℝ) :=
    ⟨⌈(δ : ℝ)⁻¹⌉₊, Nat.ceil_pos.mpr (inv_pos.mpr hδ0'), Nat.le_ceil _⟩
  have hRne : R ≠ 0 := hRpos.ne'
  have hR0 : (R : ENNReal) ≠ 0 := by exact_mod_cast hRne
  have hRt : (R : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top R
  have hR1 : (1 : ENNReal) ≤ (R : ENNReal) := by exact_mod_cast hRpos
  -- the duplicated family is in the band
  have hband : (δ : ℝ)⁻¹ ≤ (((dupFinset s R).card : ℕ) : ℝ) := by
    rw [dupFinset_card]
    have h1 : (1 : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hcardpos
    have hR0' : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
    have : (R : ℝ) ≤ ((s.card : ℝ) * (R : ℝ)) := by nlinarith
    calc (δ : ℝ)⁻¹ ≤ (R : ℝ) := hRle
      _ ≤ (s.card : ℝ) * (R : ℝ) := this
      _ = ((s.card * R : ℕ) : ℝ) := by push_cast; ring
  have hdup := hδev (ι := ι × Fin R) (dupFinset s R) (fun p ↦ T p.1) (R : ENNReal)
    (fun p hp ↦ hball p.1 (mem_dupFinset.mp hp)) hR1 hRt
    (isKatzTao_dupFinset (R := R) (W := fun i ↦ (T i).toConvexSpaceBody) hKT)
    (by rw [fullness_dupFinset (R := R) hRne (fun i ↦ (T i).toShadedBody)]; exact hfull)
    hband
  rw [sum_dupFinset (fun i ↦ volume (T i).shade),
    iUnion_dupFinset hRne (fun i ↦ (T i).shade), dupFinset_card,
    mul_assoc ((δ : ENNReal) ^ (-ε)), rpow_dup_cancel hγ hRne] at hdup
  have hrw : (δ : ENNReal) ^ (-ε) * ((R : ENNReal) * (s.card : ENNReal) ^ γ)
      * volume (⋃ i ∈ s, (T i).shade)
      = (R : ENNReal) * ((δ : ENNReal) ^ (-ε) * (s.card : ENNReal) ^ γ
          * volume (⋃ i ∈ s, (T i).shade)) := by ring
  rw [hrw] at hdup
  exact (ENNReal.mul_le_mul_iff_right hR0 hRt).mp hdup


/-- **The assembly, with the `Kakeya.ML2Assembly.SmallCard` slot deleted.**

Compare `Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy`, which needs
`hsmall : Kakeya.ML2Assembly.SmallCard (β - c)` alongside the dichotomy.  Here there is no second
slot and no cardinality case split: one obligation, stated on the band, delivers the conclusion. -/
theorem katzTaoEstimate_sub_of_carriedBand {β c : ℝ} (hβc : 0 ≤ β - c)
    (h : CarriedBand.{u} (β - c)) : Kakeya.KatzTaoEstimate.{u} Space3 (β - c) :=
  katzTaoEstimate_of_carriedBand hβc h

/-! ## The re-encoding is exact: `CarriedBand γ` is *not* stronger than `K_KT γ` -/

/-- **GWZ Lemma 3.7 already supplies the carried form.**

`Kakeya.KatzTaoEstimate.multiplicity_bound` is exactly `μ ≤ δ^{-ε} · Δ_max^{1-γ} · |𝕋|^γ`, with
**no** Katz--Tao hypothesis on the family, so a family that is only `M · δ^{-η}` Katz--Tao still
gets `μ ≤ δ^{-ε} · M^{1-γ} · |𝕋|^γ` once `η (1-γ) ≤ ε`, which the goal's own quantifier order
allows because `η` is chosen after `ε`.

Together with `Kakeya.ML2Carried.katzTaoEstimate_of_carriedBand` this makes
`CarriedBand γ ↔ K_KT γ`: carrying the band is a *re-encoding*, not a strengthening, and in
particular the reduction that consumes it is not deferring the difficulty into a harder lemma.
The band hypothesis of `CarriedBand` is not used here — the converse holds without it. -/
theorem carriedBand_of_katzTaoEstimate {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (h : Kakeya.KatzTaoEstimate.{u} Space3 γ) : CarriedBand.{u} γ := by
  classical
  intro ε hε
  obtain ⟨η₀, hη₀, hev⟩ :=
    KatzTaoEstimate.multiplicity_bound (E := Space3) hγ0 h (ε / 2) (by linarith)
  refine ⟨min η₀ (min 1 (ε / 2)), lt_min hη₀ (lt_min one_pos (by linarith)),
    le_trans (min_le_right _ _) (min_le_left _ _), ?_⟩
  set η : ℝ := min η₀ (min 1 (ε / 2)) with hηdef
  have hηη₀ : η ≤ η₀ := min_le_left _ _
  have hηε : η ≤ ε / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hη0 : 0 < η := lt_min hη₀ (lt_min one_pos (by linarith))
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hδev hδ
  obtain ⟨hδ0, hδ1⟩ := hδ
  intro ι s T M hball hM1 hMt hKT hfull _hband
  have hδ0' : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδ1' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1.le
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1.le
  have hδne0 : (δ : ENNReal) ≠ 0 := by
    simpa using hδ0.ne'
  have hδnetop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  -- totalize the tube map, as in `Kakeya.FrostmanEstimate.multiplicity_bound_of_mem`
  obtain ⟨i₀, hi₀⟩ := hs
  set T' : ι → ShadedTube δ Space3 := fun i ↦ if i ∈ s then T i else T i₀ with hT'def
  have hT' : ∀ i ∈ s, T' i = T i := fun i hi ↦ by simp [hT'def, hi]
  have hball' : ∀ i, (T' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i
    by_cases hi : i ∈ s
    · simpa [hT' i hi] using hball i hi
    · simpa [hT'def, hi] using hball i₀ hi₀
  have hshadeSum : (∑ i ∈ s, volume (T' i).shade) = ∑ i ∈ s, volume (T i).shade :=
    Finset.sum_congr rfl fun i hi ↦ by rw [hT' i hi]
  have hcarrierSum : (∑ i ∈ s, volume (T' i).carrier) = ∑ i ∈ s, volume (T i).carrier :=
    Finset.sum_congr rfl fun i hi ↦ by rw [hT' i hi]
  have hunion : (⋃ i ∈ s, (T' i).shade) = ⋃ i ∈ s, (T i).shade :=
    Set.iUnion_congr fun i ↦ Set.iUnion_congr fun hi ↦ by rw [hT' i hi]
  have hfullEq : ShadedBody.fullness s (fun i ↦ (T' i).toShadedBody)
      = ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) := by
    rw [← ENNReal.coe_inj, ShadedBody.fullness_def, ShadedBody.fullness_def,
      hshadeSum, hcarrierSum]
  -- the fullness hypothesis of Lemma 3.7, in its real form and at the exponent `η₀`
  have hfull' : (ShadedBody.fullness s (fun i ↦ (T' i).toShadedBody) : ℝ) ≥ (δ : ℝ) ^ η₀ := by
    have h1 : (δ : ℝ) ^ η₀ ≤ (δ : ℝ) ^ η := Real.rpow_le_rpow_of_exponent_ge hδ0' hδ1' hηη₀
    have h2 : ((δ ^ η : NNReal) : ℝ) ≤ (ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) : ℝ) :=
      by exact_mod_cast hfull
    rw [hfullEq]
    rw [NNReal.coe_rpow] at h2
    linarith
  -- the Katz--Tao bound transfers to the totalised family
  have hKT' : ConvexSpaceBody.IsKatzTao s (fun i ↦ (T' i).toConvexSpaceBody)
      (M * (δ : ENNReal) ^ (-η)) := by
    rw [ConvexSpaceBody.isKatzTao_iff]
    intro K
    have hsum : ∑ i ∈ s with (T' i).toConvexSpaceBody ≤ K, volume (T' i).carrier
        = ∑ i ∈ s with (T i).toConvexSpaceBody ≤ K, volume (T i).carrier := by
      rw [Finset.sum_filter, Finset.sum_filter]
      exact Finset.sum_congr rfl fun i hi ↦ by rw [hT' i hi]
    rw [hsum]
    exact (ConvexSpaceBody.isKatzTao_iff s (fun i ↦ (T i).toConvexSpaceBody) _).mp hKT K
  have hΔ : Kakeya.maxDensity s (fun i ↦ (T' i).toConvexSpaceBody) ≤ M * (δ : ENNReal) ^ (-η) :=
    hKT'
  -- Lemma 3.7, then the density substitution
  have hmb := hδev s T' hball' hfull'
  have hmulteq : ShadedBody.multiplicity s (fun i ↦ (T' i).toShadedBody)
      = ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) := by
    rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div, hshadeSum, hunion]
  rw [hmulteq] at hmb
  have h1γ : (0 : ℝ) ≤ 1 - γ := by linarith
  have hpow : (Kakeya.maxDensity s (fun i ↦ (T' i).toConvexSpaceBody)) ^ (1 - γ)
      ≤ M ^ (1 - γ) * (δ : ENNReal) ^ (-(ε / 2)) := by
    calc (Kakeya.maxDensity s (fun i ↦ (T' i).toConvexSpaceBody)) ^ (1 - γ)
        ≤ (M * (δ : ENNReal) ^ (-η)) ^ (1 - γ) := ENNReal.rpow_le_rpow hΔ h1γ
      _ = M ^ (1 - γ) * ((δ : ENNReal) ^ (-η)) ^ (1 - γ) :=
          ENNReal.mul_rpow_of_nonneg _ _ h1γ
      _ = M ^ (1 - γ) * (δ : ENNReal) ^ (-η * (1 - γ)) := by rw [← ENNReal.rpow_mul]
      _ ≤ M ^ (1 - γ) * (δ : ENNReal) ^ (-(ε / 2)) := by
          refine mul_le_mul_right (ENNReal.rpow_le_rpow_of_exponent_ge hδE1 ?_) _
          nlinarith
  -- assemble
  rw [ShadedBody.multiplicity_le_iff] at hmb
  refine hmb.trans ?_
  gcongr ?_ * volume (⋃ i ∈ s, (T i).shade)
  calc (δ : ENNReal) ^ (-(ε / 2))
        * (Kakeya.maxDensity s (fun i ↦ (T' i).toConvexSpaceBody)) ^ (1 - γ)
        * (s.card : ENNReal) ^ γ
      ≤ (δ : ENNReal) ^ (-(ε / 2)) * (M ^ (1 - γ) * (δ : ENNReal) ^ (-(ε / 2)))
          * (s.card : ENNReal) ^ γ := by gcongr
    _ = ((δ : ENNReal) ^ (-(ε / 2)) * (δ : ENNReal) ^ (-(ε / 2))) * M ^ (1 - γ)
          * (s.card : ENNReal) ^ γ := by ring
    _ = (δ : ENNReal) ^ (-ε) * M ^ (1 - γ) * (s.card : ENNReal) ^ γ := by
        rw [← ENNReal.rpow_add _ _ hδne0 hδnetop, show -(ε / 2) + -(ε / 2) = -ε by ring]

/-- **`CarriedBand` is the goal, re-encoded so that the band is a hypothesis.**

Left to right is `Kakeya.ML2Carried.katzTaoEstimate_of_carriedBand` (duplication);
right to left is `Kakeya.ML2Carried.carriedBand_of_katzTaoEstimate` (GWZ Lemma 3.7). -/
theorem carriedBand_iff {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    CarriedBand.{u} γ ↔ Kakeya.KatzTaoEstimate.{u} Space3 γ :=
  ⟨katzTaoEstimate_of_carriedBand hγ0, carriedBand_of_katzTaoEstimate hγ0 hγ1⟩

/-- **The acceptance filter, applied to `CarriedBand` itself.**

`Kakeya.ML2Squeeze.producer_of_smallCardCut_is_producer_of_goal` says that any `P` producing the
small-cardinality fragment produces the goal.  `CarriedBand` does produce it, so `CarriedBand` is
*not* an obligation weaker than Main Lemma 2's conclusion.  This is recorded, not hidden: the
claim made for the carried route is that it removes the **complement**, not that it makes the
theorem easier.  Nothing can make it easier — `Kakeya.ML2Squeeze.forall_cut_circular` already
shows the complement is the theorem. -/
theorem carriedBand_is_producer_of_goal {γ θ : ℝ} (hγ0 : 0 ≤ γ) (_hθ : 0 < θ) :
    (CarriedBand.{u} γ → Kakeya.ML2Squeeze.SmallCardCut.{u} θ γ)
      ∧ (CarriedBand.{u} γ → Kakeya.KatzTaoEstimate.{u} Space3 γ) := by
  refine ⟨fun hc ↦ ?_, katzTaoEstimate_of_carriedBand hγ0⟩
  exact Kakeya.ML2Squeeze.smallCardCut_of_katzTaoEstimate (katzTaoEstimate_of_carriedBand hγ0 hc)

/-- **At `M = 1` the carried statement is exactly the banded estimate the GWZ route delivers.**

So the density parameter `M` is the *entire* difference between
`Kakeya.ML2Squeeze.KatzTaoEstimateGE 1 γ` — what `Kakeya.ML2Assembly.Dichotomy` produces — and
`CarriedBand γ`, which by `Kakeya.ML2Carried.carriedBand_iff` is the goal. -/
theorem katzTaoEstimateGE_of_carriedBand {γ : ℝ} (h : CarriedBand.{u} γ) :
    Kakeya.ML2Squeeze.KatzTaoEstimateGE.{u} 1 γ := by
  intro ε hε
  obtain ⟨η, hη0, _hη1, hev⟩ := h ε hε
  refine ⟨η, hη0, ?_⟩
  filter_upwards [hev, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)] with δ hδev hδ
  obtain ⟨hδ0, _hδ1⟩ := hδ
  intro ι s T hball hKT hfull hcard
  have hδ0' : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hcard' : (δ : ℝ)⁻¹ ≤ (s.card : ℝ) := by
    rwa [Real.rpow_neg_one] at hcard
  have := hδev s T 1 hball le_rfl (by simp) (by simpa using hKT) hfull hcard'
  simpa using this

/-! ## What the transport does to the two branches of the GWZ dichotomy

`Kakeya.ML2Assembly.Dichotomy` offers, on the band, either

* **(i)** the absolute-accuracy bound `∑ |Y| ≤ δ^{-ε₀} |⋃ Y|` from the every-scale branch, or
* **(ii)** the `δ`-gain `∑ |Y| ≤ δ^{g} |𝕋|^β |⋃ Y|` from the window branch.

Duplication multiplies `∑ |Y|` and `|𝕋|` by `R` and leaves `|⋃ Y|` alone, so the only forms of
(i) and (ii) that can survive it are the covariant ones, `M · δ^{-ε₀}` and `M^{1-β} δ^{g} |𝕋|^β`.
The two theorems below compute what each of those becomes at the transport
`(M, |𝕋|) = (1, n) ↦ (R, n R)` used by `Kakeya.ML2Carried.katzTaoEstimate_of_carriedBand`.

The answer is the same for both, and it is the point of this file: **the closure condition of a
branch is transport-invariant.**  For the gain that is harmless — its condition is met by the
crude cardinality bound at every `n`.  For the accuracy it is fatal — its condition *is* the band
`δ^{-1} ≤ n` on the *original* count, which is exactly what the transport was supposed to supply
and provably does not. -/

/-- **The accuracy branch after the transport: the closure condition is unchanged.** -/
theorem accuracy_branch_after_transport {γ ε ε₀ : ℝ} (hγ : 0 ≤ γ) {R n : ℕ} (hR : R ≠ 0)
    {δ : NNReal} :
    ((R : ENNReal) * (δ : ENNReal) ^ (-ε₀)
        ≤ (δ : ENNReal) ^ (-ε) * (R : ENNReal) ^ (1 - γ) * ((n * R : ℕ) : ENNReal) ^ γ)
      ↔ ((δ : ENNReal) ^ (-ε₀) ≤ (δ : ENNReal) ^ (-ε) * (n : ENNReal) ^ γ) := by
  have hR0 : (R : ENNReal) ≠ 0 := by exact_mod_cast hR
  have hRt : (R : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top R
  rw [mul_assoc ((δ : ENNReal) ^ (-ε)), rpow_dup_cancel hγ hR,
    show (δ : ENNReal) ^ (-ε) * ((R : ENNReal) * (n : ENNReal) ^ γ)
      = (R : ENNReal) * ((δ : ENNReal) ^ (-ε) * (n : ENNReal) ^ γ) from by ring]
  exact ENNReal.mul_le_mul_iff_right hR0 hRt

/-- **The gain branch after the transport: the closure condition is unchanged.** -/
theorem gain_branch_after_transport {β γ ε g : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) {R n : ℕ}
    (hR : R ≠ 0) {δ : NNReal} :
    ((R : ENNReal) ^ (1 - β) * (δ : ENNReal) ^ g * ((n * R : ℕ) : ENNReal) ^ β
        ≤ (δ : ENNReal) ^ (-ε) * (R : ENNReal) ^ (1 - γ) * ((n * R : ℕ) : ENNReal) ^ γ)
      ↔ ((δ : ENNReal) ^ g * (n : ENNReal) ^ β
        ≤ (δ : ENNReal) ^ (-ε) * (n : ENNReal) ^ γ) := by
  have hR0 : (R : ENNReal) ≠ 0 := by exact_mod_cast hR
  have hRt : (R : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top R
  rw [show (R : ENNReal) ^ (1 - β) * (δ : ENNReal) ^ g * ((n * R : ℕ) : ENNReal) ^ β
      = (δ : ENNReal) ^ g * ((R : ENNReal) ^ (1 - β) * ((n * R : ℕ) : ENNReal) ^ β) from by ring,
    rpow_dup_cancel hβ hR, mul_assoc ((δ : ENNReal) ^ (-ε)), rpow_dup_cancel hγ hR,
    show (δ : ENNReal) ^ g * ((R : ENNReal) * (n : ENNReal) ^ β)
      = (R : ENNReal) * ((δ : ENNReal) ^ g * (n : ENNReal) ^ β) from by ring,
    show (δ : ENNReal) ^ (-ε) * ((R : ENNReal) * (n : ENNReal) ^ γ)
      = (R : ENNReal) * ((δ : ENNReal) ^ (-ε) * (n : ENNReal) ^ γ) from by ring]
  exact ENNReal.mul_le_mul_iff_right hR0 hRt

/-- **The gain branch closes, at the assembly's own `ε`-free budget `4c ≤ g`.**

`Kakeya.ML2Assembly.card_le_rpow_neg_four` supplies `n ≤ δ^{-4}` for every admissible family, so
the transport-invariant condition of `Kakeya.ML2Carried.gain_branch_after_transport` holds
unconditionally.  Nothing about the gain branch changes in the carried route. -/
theorem gain_branch_closes {β c g ε : ℝ} (hc : 0 < c) (hg : 4 * c ≤ g) (hε : 0 ≤ ε)
    (_hβc : 0 ≤ β - c) {n : ℕ} {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 0 < n)
    (hcard : (n : ENNReal) ≤ (δ : ENNReal) ^ (-4 : ℝ)) :
    (δ : ENNReal) ^ g * (n : ENNReal) ^ β
      ≤ (δ : ENNReal) ^ (-ε) * (n : ENNReal) ^ (β - c) := by
  have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast hn.ne'
  have hnt : (n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hsplit : (n : ENNReal) ^ β = (n : ENNReal) ^ (β - c) * (n : ENNReal) ^ c := by
    rw [← ENNReal.rpow_add _ _ hn0 hnt, show β - c + c = β by ring]
  have hnc : (n : ENNReal) ^ c ≤ (δ : ENNReal) ^ (-(4 * c)) := by
    calc (n : ENNReal) ^ c ≤ ((δ : ENNReal) ^ (-4 : ℝ)) ^ c := ENNReal.rpow_le_rpow hcard hc.le
      _ = (δ : ENNReal) ^ (-(4 * c)) := by rw [← ENNReal.rpow_mul]; ring_nf
  calc (δ : ENNReal) ^ g * (n : ENNReal) ^ β
      = (δ : ENNReal) ^ g * (n : ENNReal) ^ c * (n : ENNReal) ^ (β - c) := by
        rw [hsplit]; ring
    _ ≤ (δ : ENNReal) ^ g * (δ : ENNReal) ^ (-(4 * c)) * (n : ENNReal) ^ (β - c) := by gcongr
    _ = (δ : ENNReal) ^ (g - 4 * c) * (n : ENNReal) ^ (β - c) := by
        rw [← ENNReal.rpow_add _ _ (by simpa using hδ0.ne') ENNReal.coe_ne_top]
        ring_nf
    _ ≤ (δ : ENNReal) ^ (-ε) * (n : ENNReal) ^ (β - c) :=
        mul_le_mul_left (ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)) _

/-- **The accuracy branch does close — above a band on the *de-duplicated* count `|𝕋| / M`.**

This is the exact sufficient condition, and at `M = 1` it is the assembly's own situation: with
`ε₀ = β/2` and `γ = β - c` the budget `ε₀ ≤ ε + γ` is `β/2 ≤ β - c`, i.e.
`Kakeya.ML2Assembly.katzTaoEstimate_sub_of_dichotomy`'s `2 * c ≤ β`.  So nothing has been lost in
the re-encoding: the accuracy branch needs precisely what it always needed, a lower bound on
`|𝕋| / M`.  What has changed is that `|𝕋| / M`, not `|𝕋|`, is the quantity — and
`Kakeya.ML2Carried.accuracy_branch_after_transport` shows duplication leaves it fixed. -/
theorem accuracy_branch_closes_of_dedup_band {γ ε ε₀ : ℝ} (hγ : 0 ≤ γ) {n : ℕ} {δ : NNReal}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : (δ : ℝ)⁻¹ ≤ (n : ℝ)) (hbudget : ε₀ ≤ ε + γ) :
    (δ : ENNReal) ^ (-ε₀) ≤ (δ : ENNReal) ^ (-ε) * (n : ENNReal) ^ γ := by
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hinv : (δ : ENNReal) ^ (-1 : ℝ) ≤ (n : ENNReal) := by
    have h1 : ((δ⁻¹ : NNReal) : ℝ) ≤ (n : ℝ) := by rw [NNReal.coe_inv]; exact hn
    have h2 : (δ⁻¹ : NNReal) ≤ (n : NNReal) := by exact_mod_cast h1
    have h3 : ((δ⁻¹ : NNReal) : ENNReal) ≤ (n : ENNReal) := by exact_mod_cast h2
    rwa [ENNReal.rpow_neg_one, ← ENNReal.coe_inv hδ0.ne']
  have hpow : (δ : ENNReal) ^ (-γ) ≤ (n : ENNReal) ^ γ := by
    calc (δ : ENNReal) ^ (-γ) = ((δ : ENNReal) ^ (-1 : ℝ)) ^ γ := by
          rw [← ENNReal.rpow_mul]; ring_nf
      _ ≤ (n : ENNReal) ^ γ := ENNReal.rpow_le_rpow hinv hγ
  calc (δ : ENNReal) ^ (-ε₀) ≤ (δ : ENNReal) ^ (-(ε + γ)) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hδE1 (by linarith)
    _ = (δ : ENNReal) ^ (-ε) * (δ : ENNReal) ^ (-γ) := by
        rw [← ENNReal.rpow_add _ _ (by simpa using hδ0.ne') ENNReal.coe_ne_top]; ring_nf
    _ ≤ (δ : ENNReal) ^ (-ε) * (n : ENNReal) ^ γ := mul_le_mul_right hpow _

/-- **The accuracy branch does not close, and the transport cannot make it.**

At the image of a *one-tube* family under the transport — `R` copies of a single fully shaded
tube, which is in the band because `R = ⌈δ⁻¹⌉` — the transport-invariant closure condition of
`Kakeya.ML2Carried.accuracy_branch_after_transport` reads `δ^{-ε₀} ≤ δ^{-ε}`, i.e. `ε₀ ≤ ε`.

Since `ε₀` must be `ε`-free (that is the whole content of
`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy'`, and the reason
`Kakeya.ML2Assembly.Dichotomy` reads Theorem 7.3(B) at the absolute accuracy `β/2`) while `ε` is
universally quantified and tends to `0`, this fails for every positive `ε₀`. -/
theorem accuracy_branch_after_transport_fails {γ ε ε₀ : ℝ} (hγ : 0 ≤ γ) {R : ℕ} (hR : R ≠ 0)
    {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hεε₀ : ε < ε₀) :
    ¬ ((R : ENNReal) * (δ : ENNReal) ^ (-ε₀)
        ≤ (δ : ENNReal) ^ (-ε) * (R : ENNReal) ^ (1 - γ) * ((1 * R : ℕ) : ENNReal) ^ γ) := by
  rw [accuracy_branch_after_transport hγ hR]
  have hδpos : (0 : ENNReal) < (δ : ENNReal) := by exact_mod_cast hδ0
  have hδlt1 : (δ : ENNReal) < 1 := by exact_mod_cast hδ1
  have hlt : (δ : ENNReal) ^ (-ε) < (δ : ENNReal) ^ (-ε₀) :=
    ENNReal.rpow_lt_rpow_of_exponent_gt hδpos hδlt1 (by linarith)
  simp only [Nat.cast_one, ENNReal.one_rpow, mul_one]
  exact not_le.mpr hlt

/-! ## Non-vacuity: the branch that dies is the one that fires

`Kakeya.ML2Carried.accuracy_branch_after_transport_fails` is arithmetic.  This section shows the
arithmetic is about a real configuration: `R` copies of one fully shaded central `δ`-tube, with
`R = ⌈δ⁻¹⌉`.  It satisfies **every** hypothesis of the carried statement — ball containment,
fullness `1`, `M · δ^{-η}` Katz--Tao at `M = |𝕋|`, and the band `δ⁻¹ ≤ |𝕋|` — and its
multiplicity is exactly `|𝕋|`.

Consequences, in the two possible readings of the every-scale branch:

* read **non-covariantly** (`μ ≤ δ^{-ε₀}`, the form `Kakeya.ML2Assembly.Dichotomy` has at `M = 1`),
  it is **false** on this configuration — `Kakeya.ML2Carried.not_strongAccuracyBand`;
* read **covariantly** (`μ ≤ M·δ^{-ε₀}`, the only form duplication permits), it is true on this
  configuration but does not close the carried target —
  `Kakeya.ML2Carried.accuracy_branch_after_transport_fails`.

The carried target *is* satisfied by this configuration
(`Kakeya.ML2Carried.repeatFam_meets_carried_target`), as it must be, since
`Kakeya.ML2Carried.carriedBand_iff` makes `CarriedBand` a true statement.  What fails is only the
route to it through the accuracy branch. -/

section Witness

variable {δ : NNReal} {R : ℕ}

/-- `R` copies of one fully shaded central `δ`-tube, indexed in `Type u`. -/
noncomputable def repeatFam (δ : NNReal) (R : ℕ) : ULift.{u} (Fin R) → ShadedTube δ Space3 :=
  fun _ ↦ Kakeya.fullyShadedTube (Kakeya.centralUnitTube δ)

/-- The index set of `Kakeya.ML2Carried.repeatFam` has exactly `R` elements. -/
@[simp] theorem repeatFam_card :
    (Finset.univ : Finset (ULift.{u} (Fin R))).card = R := by simp

theorem repeatFam_sum :
    ∑ i ∈ (Finset.univ : Finset (ULift.{u} (Fin R))), volume (repeatFam.{u} δ R i).shade
      = (R : ENNReal) * volume (Kakeya.centralUnitTube δ).carrier := by
  simp [repeatFam, Kakeya.fullyShadedTube, Finset.sum_const, nsmul_eq_mul]

theorem repeatFam_carrierSum :
    ∑ i ∈ (Finset.univ : Finset (ULift.{u} (Fin R))), volume (repeatFam.{u} δ R i).carrier
      = (R : ENNReal) * volume (Kakeya.centralUnitTube δ).carrier := by
  simp [repeatFam, Kakeya.fullyShadedTube, Finset.sum_const, nsmul_eq_mul]

theorem repeatFam_union (hR : R ≠ 0) :
    (⋃ i ∈ (Finset.univ : Finset (ULift.{u} (Fin R))), (repeatFam.{u} δ R i).shade)
      = (Kakeya.centralUnitTube δ).carrier := by
  have hne : Nonempty (ULift.{u} (Fin R)) := ⟨⟨⟨0, Nat.pos_of_ne_zero hR⟩⟩⟩
  simp only [repeatFam, Kakeya.fullyShadedTube, Finset.mem_univ, Set.iUnion_true]
  exact Set.iUnion_const _

theorem repeatFam_fullness (hR : R ≠ 0) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ShadedBody.fullness (Finset.univ : Finset (ULift.{u} (Fin R)))
      (fun i ↦ (repeatFam.{u} δ R i).toShadedBody) = 1 := by
  obtain ⟨hv0, hvt⟩ := Tube.volume_pos_and_lt_top hδ0 hδ1 (Kakeya.centralUnitTube δ)
  have hR0 : (R : ENNReal) ≠ 0 := by exact_mod_cast hR
  have hRt : (R : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top R
  have h : ShadedBody.fullness' (Finset.univ : Finset (ULift.{u} (Fin R)))
      (fun i ↦ (repeatFam.{u} δ R i).toShadedBody) = 1 := by
    show (∑ i ∈ (Finset.univ : Finset (ULift.{u} (Fin R))), volume (repeatFam.{u} δ R i).shade)
        / (∑ i ∈ (Finset.univ : Finset (ULift.{u} (Fin R))), volume (repeatFam.{u} δ R i).carrier)
      = 1
    rw [repeatFam_sum, repeatFam_carrierSum, ENNReal.div_self
      (by simp [hR0, hv0.ne'])
      (by
        refine (ENNReal.mul_ne_top hRt hvt.ne)) ]
  unfold ShadedBody.fullness
  rw [h]
  rfl

/-- **The every-scale branch, read without the covariance factor `M`.**

This is alternative (i) of `Kakeya.ML2Assembly.Dichotomy` transplanted verbatim to the carried
setting: the accuracy `δ^{-ε₀}` with no `M`. -/
def StrongAccuracyBand (ε₀ η : ℝ) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3) (M : ENNReal),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      1 ≤ M → M ≠ ⊤ →
      ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody)
        (M * (δ : ENNReal) ^ (-η)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      (δ : ℝ)⁻¹ ≤ (s.card : ℝ) →
      ∑ i ∈ s, volume (T i).shade
        ≤ (δ : ENNReal) ^ (-ε₀) * volume (⋃ i ∈ s, (T i).shade)

/-- **The non-covariant accuracy branch is false on the band.**

`R` copies of one fully shaded central tube, `R = ⌈δ⁻¹⌉`, satisfy every hypothesis and have
`μ = R ≥ δ⁻¹`, which exceeds `δ^{-ε₀}` for every `ε₀ < 1`.  This is the exact analogue, for the
accuracy alternative, of the duplication refutations of the gain alternative: what
kills it is duplication, and duplication is unavoidable because it is the only transport into the
band. -/
theorem not_strongAccuracyBand {ε₀ η : ℝ} (hε₀1 : ε₀ < 1) (hη : 0 ≤ η) :
    ¬ StrongAccuracyBand.{u} ε₀ η := by
  intro h
  obtain ⟨δ, hδev, hδmem⟩ :=
    (h.and (Ioo_mem_nhdsGT (show (0 : NNReal) < 1 / 2 by norm_num))).exists
  obtain ⟨hδ0, hδhalf⟩ := hδmem
  have hδ0' : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδhalf' : (δ : ℝ) < 1 / 2 := by exact_mod_cast hδhalf
  have hδ1 : δ ≤ 1 := by
    have : (δ : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  have hδlt1 : δ < 1 := by
    have : (δ : ℝ) < 1 := by linarith
    exact_mod_cast this
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hδEpos : (0 : ENNReal) < (δ : ENNReal) := by exact_mod_cast hδ0
  have hδElt1 : (δ : ENNReal) < 1 := by exact_mod_cast hδlt1
  obtain ⟨R, hRpos, hRle⟩ : ∃ R : ℕ, 0 < R ∧ (δ : ℝ)⁻¹ ≤ (R : ℝ) :=
    ⟨⌈(δ : ℝ)⁻¹⌉₊, Nat.ceil_pos.mpr (inv_pos.mpr hδ0'), Nat.le_ceil _⟩
  have hRne : R ≠ 0 := hRpos.ne'
  have hR1 : (1 : ENNReal) ≤ (R : ENNReal) := by exact_mod_cast hRpos
  have hRt : (R : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top R
  obtain ⟨hv0, hvt⟩ := Tube.volume_pos_and_lt_top hδ0 hδ1 (Kakeya.centralUnitTube δ)
  -- `δ^{-η} ≥ 1`
  have hpowη : (1 : ENNReal) ≤ (δ : ENNReal) ^ (-η) := by
    have := ENNReal.rpow_le_rpow_of_exponent_ge (x := (δ : ENNReal)) hδE1
      (show -η ≤ (0 : ℝ) by linarith)
    simpa using this
  -- the hypotheses of `StrongAccuracyBand` on the witness
  have hball : ∀ i ∈ (Finset.univ : Finset (ULift.{u} (Fin R))),
      (repeatFam.{u} δ R i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i _
    exact Kakeya.centralUnitTube_carrier_subset_closedBall (by exact_mod_cast hδhalf.le)
  have hKT : ConvexSpaceBody.IsKatzTao (Finset.univ : Finset (ULift.{u} (Fin R)))
      (fun i ↦ (repeatFam.{u} δ R i).toConvexSpaceBody)
      ((R : ENNReal) * (δ : ENNReal) ^ (-η)) := by
    refine le_trans (Kakeya.maxDensity_le_card _ _) ?_
    rw [repeatFam_card]
    simpa using mul_le_mul_right hpowη (R : ENNReal)
  have hfull : ShadedBody.fullness (Finset.univ : Finset (ULift.{u} (Fin R)))
      (fun i ↦ (repeatFam.{u} δ R i).toShadedBody) ≥ δ ^ η := by
    rw [repeatFam_fullness hRne hδ0 hδ1]
    exact NNReal.rpow_le_one hδ1 hη
  have hband : (δ : ℝ)⁻¹ ≤ ((Finset.univ : Finset (ULift.{u} (Fin R))).card : ℝ) := by
    rw [repeatFam_card]; exact hRle
  have hconc := hδev (Finset.univ : Finset (ULift.{u} (Fin R))) (repeatFam.{u} δ R)
    (R : ENNReal) hball hR1 hRt hKT hfull hband
  rw [repeatFam_sum, repeatFam_union hRne] at hconc
  -- cancel the tube volume
  have hRle' : (R : ENNReal) ≤ (δ : ENNReal) ^ (-ε₀) :=
    (ENNReal.mul_le_mul_iff_left hv0.ne' hvt.ne).mp hconc
  -- but `R ≥ δ^{-1} > δ^{-ε₀}`
  have hinv : (δ : ENNReal) ^ (-1 : ℝ) ≤ (R : ENNReal) := by
    have h1 : ((δ⁻¹ : NNReal) : ℝ) ≤ (R : ℝ) := by
      rw [NNReal.coe_inv]; exact hRle
    have h2 : (δ⁻¹ : NNReal) ≤ (R : NNReal) := by exact_mod_cast h1
    have h3 : ((δ⁻¹ : NNReal) : ENNReal) ≤ (R : ENNReal) := by exact_mod_cast h2
    rwa [ENNReal.rpow_neg_one, ← ENNReal.coe_inv hδ0.ne'] 
  have hstrict : (δ : ENNReal) ^ (-ε₀) < (δ : ENNReal) ^ (-1 : ℝ) :=
    ENNReal.rpow_lt_rpow_of_exponent_gt hδEpos hδElt1 (by linarith)
  exact absurd (le_trans hinv hRle') (not_le.mpr hstrict)

/-- The witness does **not** refute the carried statement, as it cannot: `CarriedBand` is true.
Its multiplicity `R` is exactly the value `M^{1-γ} |𝕋|^γ = R` that the carried target allows. -/
theorem repeatFam_meets_carried_target {γ ε : ℝ} (hε : 0 ≤ ε) (hR : R ≠ 0) (_hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    ∑ i ∈ (Finset.univ : Finset (ULift.{u} (Fin R))), volume (repeatFam.{u} δ R i).shade
      ≤ (δ : ENNReal) ^ (-ε) * (R : ENNReal) ^ (1 - γ)
        * ((Finset.univ : Finset (ULift.{u} (Fin R))).card : ENNReal) ^ γ
        * volume (⋃ i ∈ (Finset.univ : Finset (ULift.{u} (Fin R))),
            (repeatFam.{u} δ R i).shade) := by
  have hR0 : (R : ENNReal) ≠ 0 := by exact_mod_cast hR
  have hRt : (R : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top R
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hpow : (1 : ENNReal) ≤ (δ : ENNReal) ^ (-ε) := by
    have := ENNReal.rpow_le_rpow_of_exponent_ge (x := (δ : ENNReal)) hδE1
      (show -ε ≤ (0 : ℝ) by linarith)
    simpa using this
  rw [repeatFam_sum, repeatFam_union hR, repeatFam_card,
    show (δ : ENNReal) ^ (-ε) * (R : ENNReal) ^ (1 - γ) * (R : ENNReal) ^ γ
      = (δ : ENNReal) ^ (-ε) * ((R : ENNReal) ^ ((1 : ℝ) - γ + γ)) from by
        rw [ENNReal.rpow_add _ _ hR0 hRt]; ring,
    show (1 : ℝ) - γ + γ = 1 from by ring, ENNReal.rpow_one]
  have hstep : (R : ENNReal) ≤ (δ : ENNReal) ^ (-ε) * (R : ENNReal) := by
    calc (R : ENNReal) = 1 * (R : ENNReal) := (one_mul _).symm
      _ ≤ (δ : ENNReal) ^ (-ε) * (R : ENNReal) := mul_le_mul_left hpow _
  exact mul_le_mul_left hstep _

end Witness


/-! This section
prices both. **Both close**, and the second closes by a budget that is *not* the one GWZ's own
chain gives, so it is recorded here rather than inherited.

### Direction 1 — read the every-scale branch at the outer `ε`

The escape would be: `Kakeya.ML2Assembly.Dichotomy`'s accuracy slot is `β/2`
(`Kakeya.ML2Spine.absAccuracy`); read Theorem 7.3(B) at the *outer* `ε` instead and the accuracy
branch closes with no band at all (`Kakeya.ML2Carried.accuracy_branch_closes_of_dedup_band` at
`ε₀ = ε` needs only `n ≥ 1`).  **It fails, because the two branches share one exponent.**

`Kakeya.ML2Assembly.GeometricCoreAt` produces
`Dichotomy β (β/2) (4 * Kakeya.ML2Spine.spineNu β ϖ ε₁ gain dens) η`: the **gain slot is `4ν`**,
and `ν` is a function of the very exponent `ε₁` at which the every-scale branch is read
(`Kakeya.ML2Spine.spineNu`'s argument list, and `Kakeya.ML2Spine.exists_ml2SpineParams` which
instantiates it at `ε₁ = E (Kakeya.ML2Spine.absAccuracy β)`).
`Kakeya.ML2Carried.spineNu_le_everyScale` below is the link `ν ≤ ε₁/25`, so buying a
smaller accuracy in branch (i) is paid for, one for one, in branch (ii)'s gain.

### Direction 2 — a floor on the de-duplicated count `|𝕋|/M`

's `no_unconditional_dedup_floor` (its worktree; **not on the branch** at `2c1753597`)
refutes an *unconditional* floor with a single fully shaded tube, `|𝕋| = Δ_max = 1`.
`Kakeya.ML2Carried.singleton_dedup_is_trivial` records why that witness is **inert against the
carried route**: at `n_d = 1` the carried target is closed by the trivial bound `μ ≤ |𝕋|`, so the
witness sits strictly inside the region the route never needed a floor on.  The shape that
survives is therefore a floor **above the trivial region**, and
`Kakeya.ML2Carried.gap_thresholds_meet_iff` says exactly how far above it must reach.

### And then both directions close at once

`Kakeya.ML2Carried.no_epsFree_drop_of_carried_budgets` is the capstone: the gain budget and the
carried closure budget are jointly unsatisfiable by any `ε`-free drop, **even when the accuracy at
which Theorem 7.3(B) is read is chosen adaptively per `ε`** — the one strategy the re-encoding had
left open. -/

section Budgets

-- selective, so nothing here can shadow a library name
open Kakeya.ML2Spine (spineNu spineAux spineRung spineDiv spineEps₂ spineAux_antitone
  spineDiv_le spineEps₂_le_everyScale)

/-- **The gain the assembly asks for is chained to the exponent the every-scale branch is read
at.**  `ν = η₀ = spineAux N` and `spineAux 0 = e = spineDiv`, and `spineAux` is antitone, so
`ν ≤ e ≤ ε₂/5 ≤ ε₁/25`.

This is the mechanical content behind "one dividing-scales run, one `ε₂`": `ε₁` is both the
Katz--Tao-at-every-scale exponent of conclusion (i) and the top of the ladder that prices
conclusion (ii). -/
theorem spineNu_le_everyScale {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁) (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ)
    (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    spineNu β ϖ ε₁ gain dens ≤ ε₁ / 25 := by
  have hanti : Antitone (spineAux β ϖ ε₁ gain dens) :=
    spineAux_antitone hβ hβ1 hϖ hε₁ hgain hdens
  have htop : spineNu β ϖ ε₁ gain dens ≤ spineAux β ϖ ε₁ gain dens 0 := by
    unfold spineNu spineRung
    exact hanti (Nat.zero_le _)
  have h0 : spineAux β ϖ ε₁ gain dens 0 = spineDiv ϖ ε₁ := rfl
  have hdiv : spineDiv ϖ ε₁ ≤ spineEps₂ ϖ ε₁ / 5 := spineDiv_le hϖ hε₁
  have heps : spineEps₂ ϖ ε₁ ≤ ε₁ / 5 := spineEps₂_le_everyScale
  rw [h0] at htop
  linarith

/-- **Direction 1 closes.**  No `ε`-free drop survives the assembly's own gain budget `4c ≤ g`
once the gain slot `g = 4ν` is read at an exponent `ε₁` that must be driven to `0`.

Contrast `Kakeya.ML2Assembly.GeometricCoreAt` as it stands, where `ε₁ = E(β/2)` is a fixed
`β`-only number and nothing here fires. -/
theorem no_epsFree_drop_of_outer_everyScale {β ϖ : ℝ} {gain dens : ℝ → ℝ} (hβ : 0 < β)
    (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ)
    (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ ε₁ : ℝ, 0 < ε₁ → 4 * c ≤ 4 * spineNu β ϖ ε₁ gain dens := by
  rintro ⟨c, hc, hall⟩
  have h := hall c hc
  have hle := spineNu_le_everyScale (β := β) (ϖ := ϖ) (ε₁ := c) (gain := gain) (dens := dens)
    hβ hβ1 hϖ hc hgain hdens
  linarith

/-- **The link, : the gain the assembly obtains is priced by the exponent the every-scale
branch is read at.**

`Kakeya.ML2Assembly.GeometricCoreAt` delivers `Kakeya.ML2Assembly.Dichotomy` with the gain slot
`4 * Kakeya.ML2Spine.spineNu β ϖ ε₁ gain dens`, where `ε₁` is the Katz--Tao-at-every-scale
exponent of conclusion (i).  This theorem consumes it and returns that gain together with the
bound `g ≤ 4 ε₁ / 25`, so the dependence is checked by the compiler rather than read off a
docstring.  `Kakeya.ML2Spine.exists_ml2SpineParams` is where `ε₁` is instantiated: at
`E (Kakeya.ML2Spine.absAccuracy β)`, the output of Theorem 7.3(B) at the reading accuracy. -/
theorem gain_of_geometricCoreAt_le (h : Kakeya.ML2Assembly.GeometricCoreAt.{u})
    {β ϖ : ℝ} {gain dens : ℝ → ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hp : Kakeya.ML2Assembly.Lemma91ParamsAt.{u} β ϖ gain dens)
    (hKT : Kakeya.KatzTaoEstimate.{u} Space3 β)
    (hKF : Kakeya.FrostmanEstimate.{u} Space3 β) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      Kakeya.ML2Assembly.Dichotomy.{u} β (β / 2)
        (4 * spineNu β ϖ ε₁ gain dens) η ∧
      4 * spineNu β ϖ ε₁ gain dens ≤ 4 * ε₁ / 25 := by
  obtain ⟨ε₁, hε₁, η, hη0, hη1, hdich⟩ := h β ϖ gain dens hβ hβ1 hp hKT hKF
  refine ⟨ε₁, hε₁, η, hη0, hη1, hdich, ?_⟩
  have := spineNu_le_everyScale (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain) (dens := dens)
    hβ hβ1 hp.window_pos hε₁ hp.gain_pos hp.dens_pos
  linarith

/-- **Direction 1 closes, on the tree's own constants.**

If Theorem 7.3(B) must be read at an accuracy `a` that shrinks with the goal's `ε` — which is
exactly what makes the *accuracy* branch close without a band
(`Kakeya.ML2Carried.accuracy_branch_closes_of_dedup_band` at `ε₀ = ε`) — then the drop
`Kakeya.ML2Spine.spineNu β ϖ (E a) gain dens` it leaves is at most `a/25 ≤ ε/25`, and no positive
`ε`-free drop survives.

The normalisation `E a ≤ a` is the harmless one  uses: a Katz--Tao exponent may always be
shrunk. -/
theorem no_epsFree_drop_of_shrinking_readAccuracy {β ϖ : ℝ} {gain dens : ℝ → ℝ} {E : ℝ → ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ)
    (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) (hEpos : ∀ a : ℝ, 0 < a → 0 < E a)
    (hE : ∀ a : ℝ, 0 < a → E a ≤ a) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε →
        ∃ a : ℝ, 0 < a ∧ a ≤ ε ∧ c ≤ spineNu β ϖ (E a) gain dens := by
  rintro ⟨c, hc, hall⟩
  obtain ⟨a, ha, hae, hcle⟩ := hall c hc
  have hEa : 0 < E a := hEpos a ha
  have hle := spineNu_le_everyScale (β := β) (ϖ := ϖ) (ε₁ := E a) (gain := gain) (dens := dens)
    hβ hβ1 hϖ hEa hgain hdens
  have : E a ≤ a := hE a ha
  linarith

/-- **The trivial bound `μ ≤ |𝕋|`, transported.**  Like the accuracy and the gain, its closure
condition is invariant. -/
theorem trivial_branch_after_transport {γ : ℝ} (hγ : 0 ≤ γ) {R n : ℕ} (hR : R ≠ 0)
    {δ : NNReal} {ε : ℝ} :
    (((n * R : ℕ) : ENNReal)
        ≤ (δ : ENNReal) ^ (-ε) * (R : ENNReal) ^ (1 - γ) * ((n * R : ℕ) : ENNReal) ^ γ)
      ↔ ((n : ENNReal) ≤ (δ : ENNReal) ^ (-ε) * (n : ENNReal) ^ γ) := by
  have hR0 : (R : ENNReal) ≠ 0 := by exact_mod_cast hR
  have hRt : (R : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top R
  rw [mul_assoc ((δ : ENNReal) ^ (-ε)), rpow_dup_cancel hγ hR,
    show ((n * R : ℕ) : ENNReal) = (R : ENNReal) * (n : ENNReal) from by push_cast; ring,
    show (δ : ENNReal) ^ (-ε) * ((R : ENNReal) * (n : ENNReal) ^ γ)
      = (R : ENNReal) * ((δ : ENNReal) ^ (-ε) * (n : ENNReal) ^ γ) from by ring]
  exact ENNReal.mul_le_mul_iff_right hR0 hRt

/-- **The trivial bound closes the carried target on the small-de-duplicated-count region.**

`μ ≤ |𝕋|` gives the carried target as soon as `n_d ≤ δ^{-ε/(1-γ)}`.  This is the left edge of the
open window, and it is where 's single-tube witness lives. -/
theorem trivial_branch_closes_of_small_dedup {γ ε : ℝ} (hγ1 : γ < 1) {n : ℕ}
    {δ : NNReal} (hn : (n : ENNReal) ≤ (δ : ENNReal) ^ (-ε / (1 - γ))) :
    (n : ENNReal) ≤ (δ : ENNReal) ^ (-ε) * (n : ENNReal) ^ γ := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast hpos.ne'
  have hnt : (n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n
  have h1γ : (0 : ℝ) < 1 - γ := by linarith
  have hsplit : (n : ENNReal) = (n : ENNReal) ^ (1 - γ) * (n : ENNReal) ^ γ := by
    rw [← ENNReal.rpow_add _ _ hn0 hnt, show (1 : ℝ) - γ + γ = 1 by ring, ENNReal.rpow_one]
  have hpow : (n : ENNReal) ^ (1 - γ) ≤ (δ : ENNReal) ^ (-ε) := by
    calc (n : ENNReal) ^ (1 - γ) ≤ ((δ : ENNReal) ^ (-ε / (1 - γ))) ^ (1 - γ) :=
          ENNReal.rpow_le_rpow hn h1γ.le
      _ = (δ : ENNReal) ^ (-ε) := by
          rw [← ENNReal.rpow_mul, div_mul_cancel₀ _ h1γ.ne']
  calc (n : ENNReal) = (n : ENNReal) ^ (1 - γ) * (n : ENNReal) ^ γ := hsplit
    _ ≤ (δ : ENNReal) ^ (-ε) * (n : ENNReal) ^ γ := mul_le_mul_left hpow _

/-- **'s single-tube witness is inert against the carried route.**

`no_unconditional_dedup_floor` refutes an unconditional floor on `|𝕋|/Δ_max` with the family
`|𝕋| = Δ_max = 1`.  At `n_d = 1` the carried target is closed by the trivial bound alone, with no
floor and no branch of the dichotomy, so that witness constrains only devices asked to fire
*inside* the open window — where `n_d > δ^{-ε/(1-γ)}` — and says nothing against the
re-encoding. -/
theorem singleton_dedup_is_trivial {γ ε : ℝ} {δ : NNReal} (hε : 0 ≤ ε)
    (hδ1 : δ ≤ 1) :
    ((1 : ℕ) : ENNReal) ≤ (δ : ENNReal) ^ (-ε) * ((1 : ℕ) : ENNReal) ^ γ := by
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hpow : (1 : ENNReal) ≤ (δ : ENNReal) ^ (-ε) := by
    have := ENNReal.rpow_le_rpow_of_exponent_ge (x := (δ : ENNReal)) hδE1
      (show -ε ≤ (0 : ℝ) by linarith)
    simpa using this
  simpa using hpow

/-- **GWZ Lemma 3.7 at `β` closes the carried target further out than the trivial bound.**

The hypothesis `K_KT β` of Main Lemma 2 gives `μ ≤ δ^{-ε'}·Δ_max^{1-β}·|𝕋|^β`
(`Kakeya.ML2Carried.carriedBand_of_katzTaoEstimate` is the carried form), whose transported
closure condition is `δ^{-ε'}·n^β ≤ δ^{-ε}·n^γ`.  It holds out to `n_d ≤ δ^{-(ε-ε')/c}`, and `ε'`
may be taken as small as one likes, so the reach is `δ^{-ε/c}` in the limit.  Which of this and
the trivial bound's `δ^{-ε/(1-γ)}` is larger depends on `β`: for `β` bounded away from `1` the
Lemma 3.7 edge is further out, at `β = 1` the trivial one is.  The left edge of the open window is
the larger of the two, and the budget below is stated at the Lemma 3.7 edge, which is the one that
still moves as `ε' → 0`. -/
theorem lemma37_branch_closes_of_small_dedup {β γ c ε ε' : ℝ} (hc : 0 < c) (hγ : γ = β - c)
    (_hεε' : ε' ≤ ε) {n : ℕ} (hpos : 0 < n) {δ : NNReal} (hδ0 : 0 < δ)
    (hn : (n : ENNReal) ≤ (δ : ENNReal) ^ (-(ε - ε') / c)) :
    (δ : ENNReal) ^ (-ε') * (n : ENNReal) ^ β
      ≤ (δ : ENNReal) ^ (-ε) * (n : ENNReal) ^ γ := by
  subst hγ
  have hn0 : (n : ENNReal) ≠ 0 := by exact_mod_cast hpos.ne'
  have hnt : (n : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hsplit : (n : ENNReal) ^ β = (n : ENNReal) ^ (β - c) * (n : ENNReal) ^ c := by
    rw [← ENNReal.rpow_add _ _ hn0 hnt, show β - c + c = β by ring]
  have hnc : (n : ENNReal) ^ c ≤ (δ : ENNReal) ^ (-(ε - ε')) := by
    calc (n : ENNReal) ^ c ≤ ((δ : ENNReal) ^ (-(ε - ε') / c)) ^ c :=
          ENNReal.rpow_le_rpow hn hc.le
      _ = (δ : ENNReal) ^ (-(ε - ε')) := by
          rw [← ENNReal.rpow_mul, div_mul_cancel₀ _ hc.ne']
  calc (δ : ENNReal) ^ (-ε') * (n : ENNReal) ^ β
      = (δ : ENNReal) ^ (-ε') * (n : ENNReal) ^ c * (n : ENNReal) ^ (β - c) := by
        rw [hsplit]; ring
    _ ≤ (δ : ENNReal) ^ (-ε') * (δ : ENNReal) ^ (-(ε - ε')) * (n : ENNReal) ^ (β - c) := by
        gcongr
    _ = (δ : ENNReal) ^ (-ε) * (n : ENNReal) ^ (β - c) := by
        rw [← ENNReal.rpow_add _ _ (by simpa using hδ0.ne') ENNReal.coe_ne_top,
          show -ε' + -(ε - ε') = -ε by ring]

/-- **The two thresholds meet exactly at `c ε₀ ≤ β ε − (β−c) ε'`.**

Left edge (`Kakeya.ML2Carried.lemma37_branch_closes_of_small_dedup`, reading the hypothesis
`K_KT β` at accuracy `ε'`): `n_d ≤ δ^{-(ε-ε')/c}`.  Right edge
(`Kakeya.ML2Carried.accuracy_branch_closes_of_dedup_band`): `n_d ≥ δ^{-(ε₀-ε)/γ}`.  They cover the
whole range iff the inequality below holds, and letting `ε' → 0` — legitimate, since `K_KT β` may
be invoked at any positive accuracy — gives the most generous form `c ε₀ ≤ β ε`.

This is what pins the budget used by `Kakeya.ML2Carried.no_epsFree_drop_of_carried_budgets`; it is
not an invented interface. -/
theorem gap_thresholds_meet_iff {β c ε ε' ε₀ : ℝ} (hc : 0 < c) (hγ : 0 < β - c) :
    ((ε₀ - ε) / (β - c) ≤ (ε - ε') / c) ↔ c * ε₀ ≤ β * ε - (β - c) * ε' := by
  rw [div_le_div_iff₀ hγ hc]
  constructor <;> intro h <;> nlinarith

/-- ⭐ **THE CARRIED ROUTE'S OBSTRUCTION, AS A SINGLE SCALAR IMPOSSIBILITY.**

Two budgets must hold simultaneously for an `ε`-free drop `c > 0`:

* **the gain budget** `25 c ≤ E ε₀` — `4c ≤ g` with `g = 4ν` and `ν ≤ ε₁/25 = E(ε₀)/25`
  (`Kakeya.ML2Carried.spineNu_le_everyScale`), where `ε₀` is the accuracy Theorem 7.3(B) is read
  at and `E` its Katz--Tao-exponent output;
* **the carried closure budget** `c ε₀ ≤ β ε` — the two thresholds of
  `Kakeya.ML2Carried.gap_thresholds_meet_iff` meeting, for the goal's accuracy `ε`.  This is the
  budget in its **most generous** form (`ε' → 0`); every attainable form is strictly stronger, so
  refuting this one refutes all of them.

They are jointly unsatisfiable, on the single normalisation `E a ≤ a` (one may always shrink a
Katz--Tao exponent), **even when `ε₀` is chosen adaptively per `ε`.**

That last clause is what makes this different from
`Kakeya.ML2Spine.not_epsFree_of_outerAccuracy'` and from 's `not_gwzDropDominationFree`,
both of which fix the reading accuracy and then watch the drop shrink.  Here the reading accuracy
is existentially quantified *inside* `∀ ε`, so the strategy "read 7.3(B) at whatever accuracy the
goal's `ε` can afford" — the only strategy the carried re-encoding left open — is closed too.
The mechanism is that the two budgets pull `ε₀` in opposite directions: the gain budget forces
`ε₀ ≥ 25c`, and the closure budget then forces `ε ≥ 25c²/β`, which fails for small `ε`. -/
theorem no_epsFree_drop_of_carried_budgets {β : ℝ} (hβ : 0 < β) {E : ℝ → ℝ}
    (hE : ∀ a : ℝ, 0 < a → E a ≤ a) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ ε₀ : ℝ, 0 < ε₀ ∧
        25 * c ≤ E ε₀ ∧ c * ε₀ ≤ β * ε := by
  rintro ⟨c, hc, hall⟩
  obtain ⟨ε₀, hε₀, hgainbudget, hclose⟩ := hall (12 * c ^ 2 / β) (by positivity)
  have hEle : E ε₀ ≤ ε₀ := hE ε₀ hε₀
  have hε₀ge : 25 * c ≤ ε₀ := le_trans hgainbudget hEle
  have hkey : c * (25 * c) ≤ c * ε₀ := by nlinarith
  have hrhs : β * (12 * c ^ 2 / β) = 12 * c ^ 2 := by field_simp
  rw [hrhs] at hclose
  nlinarith [hkey, hclose]

end Budgets

end Kakeya.ML2Carried

end
