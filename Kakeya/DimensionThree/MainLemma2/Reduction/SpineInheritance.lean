/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.AffineMap
public import Kakeya.Frostman
public import Kakeya.KatzTao
public import Kakeya.Thickness.Volume

/-!
# The Section-9 spine: inheritance of the two non-clustering conditions

Main Lemma 2 (blueprint `section9.tex`) uses GWZ Remark 3.3
(blueprint `inheritedDownwardsUpwardsRemark`, stated in `section3.tex`) twice, and the two uses
are of *opposite* kinds:

* **(B), downwards, Katz-Tao.** `section9.tex:74`: from `Δ_max(𝕋) ≤ δ^{-η}`, for each
  `T_τ ∈ 𝕋_τ` one gets `C_KT(𝕋[T_τ], T_τ) ≤ δ^{-η}`.
* **(A), upwards, Frostman.** `section9.tex:178`: from `C_F(𝕋̃_ρ, T_b) ≲ δ^{-η'}` one gets
  `C_F(𝕋̃_σ, T_b) ≲ δ^{-η'}` for the coarser families `𝕋̃_σ`, `σ ∈ [ρ, b]`.

Both halves of the remark are **already in the tree**, at the general convex-body level:

* (B) is `ConvexSpaceBody.IsKatzTao.subset` (`Kakeya/KatzTao.lean`);
* (A) is `ConvexSpaceBody.IsFrostmanIn.inherited_upwards`, its ambient-radius version
  `ConvexSpaceBody.IsFrostmanIn.inherited_upwards'`, and the uniform-fibre version
  `ConvexSpaceBody.IsFrostmanIn.inherited_upwards_uniform` (`Kakeya/Frostman.lean`).

This file supplies only the *adapters* between those and the shapes the Section-9 reduction
reads, and the two `Δ`-comparison facts of the non-eccentric case. Nothing here is new
mathematics; everything is bookkeeping around the two named lemmas.

## What is here

### The anchored reading of (B)

`C_KT(𝕍, K)` is `Δ_max` of the family after the affine change of variables that takes `K` to
the unit ball, and `Kakeya.maxDensity` is exactly invariant under such a change
(`Kakeya.maxDensity_affineImage`). So the anchor carries no information and (B) is a statement
about `Kakeya.maxDensity` of a subfamily: `Kakeya.ML2Spine.isKatzTao_familyIn` and
`Kakeya.ML2Spine.maxDensity_familyIn_le` read it at the subfamily `𝕋[K]` that the Section-9
call site names, and `Kakeya.ML2Spine.isKatzTao_familyIn_affineImage` records that rescaling
`K` to `B₁` first changes nothing.

### The parent-map reading of (A)

`ConvexSpaceBody.IsFrostmanIn.inherited_upwards'` consumes a `Finpartition` and produces a
family indexed by a subset of its *parts*. Section 9 has instead a *parent map*
`par : ι → κ` sending each `ρ`-tube to the `σ`-tube containing it, and wants the conclusion
indexed by a subset of the coarse index set `κ`.
`Kakeya.ML2Spine.exists_subset_isFrostmanIn_parents'` performs that translation once and for
all: it builds the fibre partition, transports the coarse bodies to the parts
(`Kakeya.ML2Spine.parentBody`), applies `inherited_upwards'`, and reindexes back along
`ConvexSpaceBody.IsFrostmanIn.reindex`.

The conclusion keeps the explicit dyadic-pigeonhole loss
`ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C'` of the underlying lemma; it is a
logarithm of `|q| / δ^n`, not a constant, and absorbing it into a small negative power of the
scale is the caller's business (compare the docstring of
`Kakeya.ml1Boot.exists_frostmanConstIn_coarse_le`, which makes the same choice on the
Main-Lemma-1 side).

The subfamily `out' ⊆ out` cannot be dispensed with: without a comparability hypothesis on the
fibre densities the remark is only true after passing to a dyadic class, which is precisely
what GWZ's `\lessapprox` conclusion means. The all-parents version, at the price of that
hypothesis, is the existing `ConvexSpaceBody.isFrostmanIn_parents_of_uniform_fibres`.

### The retained-mass bound, and why the conclusion is worthless without it

`ConvexSpaceBody.IsFrostmanIn s W K C` unfolds to
`∀ K' ≤ K, densityIn s W K' ≤ C * densityIn s W K`, which at `s = ∅` reads `0 ≤ C * 0` and
therefore holds for **every** `C`, including `C = 0`. So a conclusion of the bare shape
`∃ out' ⊆ out, IsFrostmanIn out' W K …` is provable from *no* hypotheses at all by taking
`out' = ∅`: it says nothing. The mathematics that is missing from such a statement is not
missing from the proof — the dyadic pigeonhole `ENNReal.dyadic_pigeonhole₁''` inside
`ConvexSpaceBody.IsFrostmanIn.inherited_upwards'` *proves* that the retained parts carry a
definite fraction of the total mass, and that lemma then discards the fact.

Every existential statement in this file therefore carries the pigeonhole's own retained-mass
bound alongside the Frostman conclusion:
`∑_{i ∈ q} |V i| ≤ L · ∑_{i ∈ q, par i ∈ out'} |V i|`, with
`L = Kakeya.ML2Spine.inheritedMassLoss`, the exact `1 + log₂(range ratio)` factor charged by the
pigeonhole (and exactly half of `inherited_upwards.C'`, see
`Kakeya.ML2Spine.two_mul_inheritedMassLoss`). Since `δ > 0` forces every `|V i| > 0`, this bound
fails outright at `out' = ∅` whenever `q` is nonempty
(`Kakeya.ML2Spine.filter_nonempty_of_massBound`), so the `∅` witness no longer discharges the
goal. `Kakeya.ML2Spine.exists_subset_mass_isFrostmanIn_parts` is the partition-level lemma that
keeps `hsum`; it is a mass-tracking restatement of
`ConvexSpaceBody.IsFrostmanIn.inherited_upwards'`, proved the same way.

For the Section-9 consumer the mass bound is not decoration. At `section9.tex:178`
(`goodFrostmanBoundTTRhoInsideTb`) the Frostman bound on the coarse family is combined with the
lower bound `lowerBdOnDeltaMaxTTSigmaTb` on the maximal density of the coarse family inside
`T_b` to produce the cardinality estimate `TTSigmaBigCardinalityV1`. A coarse subfamily carrying
none of the mass carries none of the density either, and the comparison degenerates.

### The two `Δ` comparisons of the non-eccentric case

`section9.tex:181` and `section9.tex:190` need, for `V ⊆ T_b` convex bodies,
`Δ(𝕋_ρ, T_b) ≥ (|V|/|T_b|) · Δ(𝕋_ρ, V)` and `Δ_max(𝕋_b) ≤ (|T_b|/|V|) · Δ_max(𝕍)`. These are
`Kakeya.ML2Spine.volume_div_mul_densityIn_le` and
`Kakeya.ML2Spine.maxDensity_le_ratio_mul_maxDensity`. Neither is in `Kakeya/Density.lean`: the
density lemmas there are monotone in the *index set* (`Kakeya.densityIn_mono`,
`Kakeya.maxDensity_mono`) or compare a family with itself under a change of test body
(`Kakeya.densityIn_mul_le_of_volume_band`), whereas these two compare *two different families*
across a containment, so they are proved here from
`Kakeya.sum_volume_eq_densityIn_mul_volume` and `Kakeya.maxDensity_le_of_forall_sum_le`.
-/

@[expose] public section

open MeasureTheory Metric Kakeya

namespace Kakeya.ML2Spine

section KatzTaoDownwards

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- **GWZ Remark 3.3(B) at the Section-9 anchor** (`section9.tex:74`).

`Δ_max` of the subfamily `𝕎[K] = {i ∈ s : W i ⊆ K}` is at most `Δ_max` of the whole family.
This is `Kakeya.maxDensity_mono` at the containment subfamily; it is the form in which the
Katz-Tao half of the remark is used, since the Section-9 call site names the subfamily by its
anchor `T_τ` rather than by an abstract subset of the index set. -/
theorem maxDensity_familyIn_le (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) :
    maxDensity (familyIn s W K) W ≤ maxDensity s W :=
  maxDensity_mono W (Finset.filter_subset _ _)

/-- **GWZ Remark 3.3(B), anchored form.** If `𝕎` is `C`-Katz-Tao then so is the subfamily
`𝕎[K]` of its members contained in `K`. Immediate from `ConvexSpaceBody.IsKatzTao.subset`. -/
theorem isKatzTao_familyIn {s : Finset ι} {W : ι → ConvexSpaceBody E} {C : ENNReal}
    (h : ConvexSpaceBody.IsKatzTao s W C) (K : ConvexSpaceBody E) :
    ConvexSpaceBody.IsKatzTao (familyIn s W K) W C :=
  h.subset (Finset.filter_subset _ _)

/-- **The anchor in `C_KT(𝕎[K], K)` carries no information.**

`C_KT(𝕍, K)` means `Δ_max` of `𝕍` read after the affine change of variables taking `K` to the
unit ball, and `Kakeya.maxDensity` is exactly invariant under an affine equivalence
(`Kakeya.maxDensity_affineImage`). Hence the Section-9 conclusion `C_KT(𝕋[T_τ], T_τ) ≤ δ^{-η}`
is `Kakeya.ML2Spine.isKatzTao_familyIn` read through any rescaling one likes. -/
theorem isKatzTao_familyIn_affineImage {s : Finset ι} {W : ι → ConvexSpaceBody E} {C : ENNReal}
    (h : ConvexSpaceBody.IsKatzTao s W C) (K : ConvexSpaceBody E)
    (L : E ≃ᵃ[ℝ] E) (hcont : Continuous L) :
    ConvexSpaceBody.IsKatzTao (familyIn s W K)
      (fun i ↦ (W i).affineImage L.toAffineMap hcont) C := by
  have := isKatzTao_familyIn h K
  rwa [ConvexSpaceBody.IsKatzTao, maxDensity_affineImage]

end KatzTaoDownwards

section DensityComparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι κ : Type*}

/-- Enlarging the test body can only add members to the containment subfamily, so it can only
increase the unnormalised mass `∑_{W i ⊆ K} |W i|`. -/
theorem sum_volume_familyIn_le_of_le {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {V K : ConvexSpaceBody E} (hVK : V ≤ K) :
    ∑ i ∈ s with W i ≤ V, volume (W i).carrier ≤
      ∑ i ∈ s with W i ≤ K, volume (W i).carrier :=
  Finset.sum_le_sum_of_subset fun i hi ↦ by
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.trans hVK⟩

/-- **Division-free form of `Δ(𝕎, K) ≥ (|V|/|K|) · Δ(𝕎, V)`** for `V ⊆ K`
(blueprint `section9.tex:190`). Both sides are the unnormalised masses
`∑_{W i ⊆ V} |W i| ≤ ∑_{W i ⊆ K} |W i|` after
`Kakeya.sum_volume_eq_densityIn_mul_volume`, so no nonvanishing hypothesis is needed. -/
theorem densityIn_mul_volume_le_of_le {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {V K : ConvexSpaceBody E} (hVK : V ≤ K) :
    densityIn s W V * volume V.carrier ≤ densityIn s W K * volume K.carrier := by
  rw [← sum_volume_eq_densityIn_mul_volume, ← sum_volume_eq_densityIn_mul_volume]
  exact sum_volume_familyIn_le_of_le hVK

/-- **`Δ(𝕎, K) ≥ (|V|/|K|) · Δ(𝕎, V)` for `V ⊆ K`** (blueprint `section9.tex:190`, the
estimate `Δ(𝕋̃_ρ, T_b) ≥ (|V|/|T_b|) Δ(𝕋̃_ρ, V)` of the non-eccentric case).

This is pure convex-body bookkeeping: the members of `𝕎` counted by `Δ(𝕎, V)` are among those
counted by `Δ(𝕎, K)`, and the two normalisations differ by `|V|/|K|`. -/
theorem volume_div_mul_densityIn_le {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {V K : ConvexSpaceBody E} (hVK : V ≤ K) (hK : volume K.carrier ≠ 0) :
    volume V.carrier / volume K.carrier * densityIn s W V ≤ densityIn s W K := by
  have hKtop : volume K.carrier ≠ ⊤ := K.isCompact.measure_ne_top
  calc volume V.carrier / volume K.carrier * densityIn s W V
      = densityIn s W V * volume V.carrier / volume K.carrier := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm, mul_comm (volume V.carrier)]
    _ ≤ densityIn s W K * volume K.carrier / volume K.carrier :=
        ENNReal.div_le_div_right (densityIn_mul_volume_le_of_le hVK) _
    _ = densityIn s W K := by
        rw [mul_div_assoc, ENNReal.div_self hK hKtop, mul_one]

/-- **`Δ_max` of a coarse family is controlled by `Δ_max` of an inscribed fine family.**

Let `g` inject the coarse index set `u` into the fine index set `t`, with the fine body
`V (g j)` contained in the coarse body `W j` and with `|W j| ≤ c · |V (g j)|`. Then
`Δ_max(𝕎) ≤ c · Δ_max(𝕍)`.

The proof is the only thing the containment is for: a coarse body inside a test body `K`
carries its inscribed fine body inside `K` too, so the coarse mass in `K` is dominated by
`c` times the fine mass in `K`, which `Kakeya.sum_volume_le_maxDensity_mul_volume` bounds. -/
theorem maxDensity_le_mul_of_injOn [DecidableEq ι] {u : Finset κ} {t : Finset ι}
    {W : κ → ConvexSpaceBody E} {V : ι → ConvexSpaceBody E} {g : κ → ι} {c : ENNReal}
    (hg : ∀ j ∈ u, g j ∈ t) (hginj : ∀ a ∈ u, ∀ b ∈ u, g a = g b → a = b)
    (hVW : ∀ j ∈ u, V (g j) ≤ W j)
    (hvol : ∀ j ∈ u, volume (W j).carrier ≤ c * volume (V (g j)).carrier) :
    maxDensity u W ≤ c * maxDensity t V := by
  classical
  refine maxDensity_le_of_forall_sum_le fun K ↦ ?_
  calc ∑ j ∈ u with W j ≤ K, volume (W j).carrier
      ≤ ∑ j ∈ u with W j ≤ K, c * volume (V (g j)).carrier :=
        Finset.sum_le_sum fun j hj ↦ hvol j (Finset.mem_filter.mp hj).1
    _ = c * ∑ j ∈ u with W j ≤ K, volume (V (g j)).carrier := by rw [Finset.mul_sum]
    _ = c * ∑ i ∈ (u.filter fun j ↦ W j ≤ K).image g, volume (V i).carrier := by
        congr 1
        refine (Finset.sum_image (s := u.filter fun j ↦ W j ≤ K) (g := g)
          (f := fun i ↦ volume (V i).carrier) ?_).symm
        intro a ha b hb hab
        exact hginj a (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).1 b
          (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).1 hab
    _ ≤ c * ∑ i ∈ t with V i ≤ K, volume (V i).carrier := by
        gcongr
        intro i hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨hju, hjK⟩ := Finset.mem_filter.mp hj
        exact Finset.mem_filter.mpr ⟨hg j hju, (hVW j hju).trans hjK⟩
    _ ≤ c * (maxDensity t V * volume K.carrier) := by
        gcongr
        exact sum_volume_le_maxDensity_mul_volume t V K
    _ = c * maxDensity t V * volume K.carrier := (mul_assoc _ _ _).symm

/-- **`Δ_max(𝕋_b) ≤ (|T_b|/|V|) · Δ_max(𝕍)`** (blueprint `section9.tex:181`, the estimate
`Δ_max(𝕋̃_b) ≤ (|T_b|/|V|) Δ_max(𝕍)` of the non-eccentric case).

The volume band is the way the Section-9 call site has the hypothesis: every coarse body has
volume at most `vhi ~ |T_b|` and every inscribed fine body has volume at least `vlo ~ |V|`.
Specialisation of `Kakeya.ML2Spine.maxDensity_le_mul_of_injOn` with `c = vhi / vlo`. -/
theorem maxDensity_le_ratio_mul_maxDensity [DecidableEq ι] {u : Finset κ} {t : Finset ι}
    {W : κ → ConvexSpaceBody E} {V : ι → ConvexSpaceBody E} {g : κ → ι} {vhi vlo : ENNReal}
    (hg : ∀ j ∈ u, g j ∈ t) (hginj : ∀ a ∈ u, ∀ b ∈ u, g a = g b → a = b)
    (hVW : ∀ j ∈ u, V (g j) ≤ W j)
    (hvhi : ∀ j ∈ u, volume (W j).carrier ≤ vhi)
    (hvlo : ∀ j ∈ u, vlo ≤ volume (V (g j)).carrier)
    (hvlo0 : vlo ≠ 0) (hvlotop : vlo ≠ ⊤) :
    maxDensity u W ≤ vhi / vlo * maxDensity t V := by
  refine maxDensity_le_mul_of_injOn hg hginj hVW fun j hj ↦ ?_
  calc volume (W j).carrier ≤ vhi := hvhi j hj
    _ = vhi / vlo * vlo := (ENNReal.div_mul_cancel hvlo0 hvlotop).symm
    _ ≤ vhi / vlo * volume (V (g j)).carrier := by gcongr; exact hvlo j hj

end DensityComparison

section MassTrackingInheritance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- **The density floor of the dyadic pigeonhole** inside
`ConvexSpaceBody.IsFrostmanIn.inherited_upwards'`: a convex body whose `ethickness.scale` is at
least `δ`, sitting inside an ambient body contained in `B(0, R)`, has density at least this. -/
@[nolint defsWithUnderscore]
noncomputable abbrev inheritedFloor (n : ℕ) (δ R : NNReal) : NNReal :=
  lt_volume_convexHull.c n * δ ^ n / (2 * R) ^ n

/-- **The retained-mass loss** charged by the dyadic pigeonhole inside
`ConvexSpaceBody.IsFrostmanIn.inherited_upwards'`: the `1 + log₂(range ratio)` count of dyadic
classes, i.e. exactly half of `ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C'`, whose other
factor `2` is the width of the dyadic window itself
(`Kakeya.ML2Spine.two_mul_inheritedMassLoss`). -/
@[nolint defsWithUnderscore]
noncomputable abbrev inheritedMassLoss (n card : ℕ) (δ R : NNReal) : NNReal :=
  Real.toNNReal (1 + Real.logb 2
    ((card : ℝ) * (2 * R : ℝ) ^ n / ((lt_volume_convexHull.c n : ℝ) * (δ : ℝ) ^ n)))

/-- `inherited_upwards.C'` is exactly twice the retained-mass loss. -/
theorem two_mul_inheritedMassLoss (n card : ℕ) (δ R : NNReal) :
    2 * inheritedMassLoss n card δ R =
      ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C' n card δ R := rfl

/-- The `R = 1` reading of `Kakeya.ML2Spine.two_mul_inheritedMassLoss`. -/
theorem two_mul_inheritedMassLoss_one (n card : ℕ) (δ : NNReal) :
    2 * inheritedMassLoss n card δ 1 =
      ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C n card δ := by
  rw [ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C_eq_C'_one,
    ← two_mul_inheritedMassLoss]

/-- The retained-mass loss is dominated by the Frostman loss, so a consumer that only wants one
constant may use `inherited_upwards.C'` throughout. -/
theorem inheritedMassLoss_le_C' (n card : ℕ) (δ R : NNReal) :
    inheritedMassLoss n card δ R ≤
      ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C' n card δ R := by
  rw [← two_mul_inheritedMassLoss]
  exact le_mul_of_one_le_left zero_le one_le_two

/-- The retained-mass loss written in the shape `ENNReal.dyadic_pigeonhole₁''` produces it. -/
theorem inheritedMassLoss_coe (n card : ℕ) (δ R : NNReal) :
    ((inheritedMassLoss n card δ R : NNReal) : ENNReal) =
      ENNReal.ofReal (1 + Real.logb 2
        (((card : NNReal) : ℝ) / ((inheritedFloor n δ R : NNReal) : ℝ))) := by
  change ENNReal.ofReal _ = ENNReal.ofReal _
  congr 2
  push_cast
  rw [div_div_eq_mul_div]

/-- Bookkeeping form of `Kakeya.ML2Spine.two_mul_inheritedMassLoss`, the analogue of the private
`ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C_mul_eq'`. -/
theorem C'_mul_eq_two_mul (n card : ℕ) (δ R : NNReal) (C : ENNReal) :
    ((ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C' n card δ R : NNReal) : ENNReal) * C =
      2 * (C * ((inheritedMassLoss n card δ R : NNReal) : ENNReal)) := by
  rw [← two_mul_inheritedMassLoss]
  push_cast
  ring

/-- The closed ball of radius `R` about the origin has volume at most `(2R) ^ n`. -/
private lemma volume_closedBall_le_two_mul_pow (R : NNReal) :
    volume (Metric.closedBall (0 : E) (R : ℝ)) ≤
      ((2 * R : NNReal) : ENNReal) ^ Module.finrank ℝ E := by
  rw [Measure.addHaar_closedBall' volume (0 : E) (R.coe_nonneg)]
  calc
    ENNReal.ofReal ((R : ℝ) ^ Module.finrank ℝ E) * volume (Metric.closedBall (0 : E) 1)
        ≤ ENNReal.ofReal ((R : ℝ) ^ Module.finrank ℝ E) * 2 ^ Module.finrank ℝ E := by
          gcongr
          exact volume_closedBall_le_two_pow_finrank (E := E)
    _ = ((2 * R : NNReal) : ENNReal) ^ Module.finrank ℝ E := by
      rw [ENNReal.ofReal_pow R.coe_nonneg, ← mul_pow]
      congr 1
      norm_num [mul_comm]

/-- The uniform density floor of the pigeonhole: local copy of the private
`ConvexSpaceBody.IsFrostmanIn.le_densityIn_of_le_scale`. -/
private lemma le_densityIn_of_scale [Nontrivial E] {s : Finset ι}
    {V : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E} {δ R : NNReal} (hR : 0 < R)
    (hV : ∀ i ∈ s, (δ : ENNReal) ≤ Metric.ethickness.scale ℝ (V i).carrier)
    (hVK : ∀ i ∈ s, V i ≤ K) (hK : K.carrier ⊆ Metric.closedBall 0 (R : ℝ))
    {i : ι} (hi : i ∈ s) :
    ((inheritedFloor (Module.finrank ℝ E) δ R : NNReal) : ENNReal) ≤ densityIn s V K := by
  have hvol_K : volume K.carrier ≤ ((2 * R : NNReal) : ENNReal) ^ Module.finrank ℝ E :=
    (measure_mono hK).trans (volume_closedBall_le_two_mul_pow R)
  have hvol_Vi : (lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal)
      * (δ : ENNReal) ^ (Module.finrank ℝ E) ≤ volume (V i).carrier := by
    calc
      _  ≤ (lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal)
          * Metric.ethickness.scale ℝ (V i).carrier ^ (Module.finrank ℝ E) := by
          gcongr; exact hV i hi
      _ ≤ volume (V i).carrier := (V i).convex.le_volume_of_pow_scale
  have hc_coe : ((inheritedFloor (Module.finrank ℝ E) δ R : NNReal) : ENNReal) =
      (lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal) * (δ : ENNReal) ^ Module.finrank ℝ E
        / ((2 * R : NNReal) : ENNReal) ^ Module.finrank ℝ E := by
    unfold inheritedFloor
    rw [ENNReal.coe_div (pow_ne_zero _ (by positivity)), ENNReal.coe_mul,
      ENNReal.coe_pow, ENNReal.coe_pow]
  rw [hc_coe]
  exact (ENNReal.div_le_div hvol_Vi hvol_K).trans (le_densityIn s V K hi (hVK i hi))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Local copy of the private `ConvexSpaceBody.IsFrostmanIn.all_le_of_partition`. -/
private lemma all_le_of_partition [DecidableEq ι] {s : Finset ι} (P : Finpartition s)
    {V : ι → ConvexSpaceBody E} {W : Finset ι → ConvexSpaceBody E} {K : ConvexSpaceBody E}
    (hWK : ∀ t ∈ P.parts, W t ≤ K) (hVW : ∀ t ∈ P.parts, ∀ i ∈ t, V i ≤ W t) :
    ∀ i ∈ s, V i ≤ K := fun i hi ↦ by
  rw [← P.sup_parts, Finset.sup_eq_biUnion, Finset.mem_biUnion] at hi
  obtain ⟨t, ht, hit⟩ := hi
  exact le_trans (hVW t ht i hit) (hWK t ht)

/-- **`ConvexSpaceBody.IsFrostmanIn.inherited_upwards'` with the retained-mass bound kept.**

The proof of `inherited_upwards'` runs `ENNReal.dyadic_pigeonhole₁''` on the parts of `P`,
weighted by the fine mass `t ↦ ∑_{i ∈ t} |V i|` and classified by the fibre density
`t ↦ Δ(V|_t, W t)`.  The pigeonhole returns three things: the retained parts, the statement
that they carry all but a factor `L` of the mass, and the dyadic uniformity of their densities.
`inherited_upwards'` uses the last two and **discards the mass bound**, which makes its
conclusion true of `parts' = ∅`.  This restatement keeps it.

The constant `L` is `Kakeya.ML2Spine.inheritedMassLoss`, exactly half of the Frostman loss
`ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C'`; nothing here is stronger than what
`inherited_upwards'` already proves internally. -/
theorem exists_subset_mass_isFrostmanIn_parts [Nontrivial E] [DecidableEq ι] {s : Finset ι}
    {V : ι → ConvexSpaceBody E} {W : Finset ι → ConvexSpaceBody E} {K : ConvexSpaceBody E}
    {P : Finpartition s} {C : ENNReal} {δ R : NNReal} (hδ : 0 < δ) (hR : 0 < R)
    (h : ConvexSpaceBody.IsFrostmanIn s V K C)
    (hV : ∀ i ∈ s, (δ : ENNReal) ≤ Metric.ethickness.scale ℝ (V i).carrier)
    (hVW : ∀ t ∈ P.parts, ∀ i ∈ t, V i ≤ W t)
    (hWK : ∀ t ∈ P.parts, W t ≤ K)
    (hK : K.carrier ⊆ Metric.closedBall 0 (R : ℝ)) :
    ∃ parts' ⊆ P.parts,
      (∑ i ∈ s, volume (V i).carrier ≤
          ((inheritedMassLoss (Module.finrank ℝ E) s.card δ R : NNReal) : ENNReal) *
            ∑ u ∈ parts', ∑ i ∈ u, volume (V i).carrier) ∧
        ConvexSpaceBody.IsFrostmanIn parts' W K
          ((ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C'
            (Module.finrank ℝ E) s.card δ R : NNReal) * C) := by
  classical
  set n := Module.finrank ℝ E with hn_def
  have ha_pos : 0 < inheritedFloor n δ R :=
    div_pos (mul_pos (lt_volume_convexHull.c_pos n) (pow_pos hδ n))
      (pow_pos (mul_pos two_pos hR) n)
  have hf_Icc : ∀ t ∈ P.parts,
      (fun t => densityIn t V (W t)) t ∈
        Set.Icc ((inheritedFloor n δ R : NNReal) : ENNReal) (((s.card : NNReal) : ENNReal)) :=
    fun t ht => by
      obtain ⟨i₀, hi₀⟩ := P.nonempty_of_mem_parts ht
      constructor
      · exact le_densityIn_of_scale hR (fun i hi => hV i (P.subset ht hi)) (hVW t ht)
          ((SetLike.coe_subset_coe.mpr (hWK t ht)).trans hK) hi₀
      · push_cast
        exact (densityIn_le_card t V (W t)).trans (mod_cast Finset.card_le_card (P.subset ht))
  obtain ⟨parts', hparts'_sub, hsum, hunif⟩ :=
    ENNReal.dyadic_pigeonhole₁'' P.parts (fun t => ∑ i ∈ t, volume (V i).carrier)
      (fun t => densityIn t V (W t)) ha_pos hf_Icc
  rw [← inheritedMassLoss_coe] at hsum
  refine ⟨parts', hparts'_sub, ?_, ?_⟩
  · rw [P.sum_eq_sum_parts_sum (fun i => volume (V i).carrier)]
    exact hsum
  · set s' := parts'.sup id with hs'_def
    have hs'_sub_s : s' ⊆ s :=
      P.sup_parts ▸ (Finset.sup_mono hparts'_sub : parts'.sup id ≤ P.parts.sup id)
    let P' : Finpartition s' := P.ofSubset hparts'_sub rfl
    rw [C'_mul_eq_two_mul]
    apply ConvexSpaceBody.IsFrostmanIn.inherited_upwards_uniform (P := P')
    · apply h.of_le_of_subset (all_le_of_partition P hWK hVW) hs'_sub_s
      rw [P.sum_eq_sum_parts_sum (fun i => volume (V i).carrier),
        P'.sum_eq_sum_parts_sum (fun i => volume (V i).carrier)]
      exact hsum
    · intro i hi
      apply (V i).convex.volume_pos_of_scale_ne_zero
      exact ne_bot_of_le_ne_bot (by simpa using hδ.ne') (hV i (hs'_sub_s hi))
    · exact fun t ht => hWK t (hparts'_sub ht)
    · exact fun t ht i hi => hVW t (hparts'_sub ht) i hi
    · exact hunif

end MassTrackingInheritance

section FrostmanUpwards

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι κ : Type*}

/-- Frostman control depends on the family only through its values on the index set. -/
theorem isFrostmanIn_congr {s : Finset ι} {W W' : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} {C : ENNReal} (h : ∀ i ∈ s, W i = W' i)
    (hFr : ConvexSpaceBody.IsFrostmanIn s W K C) :
    ConvexSpaceBody.IsFrostmanIn s W' K C := by
  intro K' hK'
  rw [← densityIn_congr h, ← densityIn_congr h]
  exact hFr K' hK'

variable [DecidableEq ι] [DecidableEq κ]

/-- The fibre of a parent map `par : ι → κ` over `j`, inside the index set `q`. -/
def parentFibre (q : Finset ι) (par : ι → κ) (j : κ) : Finset ι := {i ∈ q | par i = j}

theorem mem_parentFibre {q : Finset ι} {par : ι → κ} {j : κ} {i : ι} :
    i ∈ parentFibre q par j ↔ i ∈ q ∧ par i = j := Finset.mem_filter

theorem parentFibre_subset {q : Finset ι} {par : ι → κ} (j : κ) :
    parentFibre q par j ⊆ q := Finset.filter_subset _ _

/-- Fibres over distinct parents that are both inhabited are distinct; hence `parentFibre` is
injective on any index set all of whose fibres are nonempty. -/
theorem parentFibre_injOn {q : Finset ι} {par : ι → κ} {out : Finset κ}
    (hne : ∀ j ∈ out, (parentFibre q par j).Nonempty) :
    Set.InjOn (parentFibre q par) ↑out := by
  intro a ha b hb hab
  obtain ⟨i, hi⟩ := hne a (Finset.mem_coe.mp ha)
  have hib : i ∈ parentFibre q par b := hab ▸ hi
  exact (mem_parentFibre.mp hi).2.symm.trans (mem_parentFibre.mp hib).2

/-- The coarse body attached to a *part* of the fibre partition: the body of the parent of any
member of the part. Off the fibres it is the ambient body `K`, a choice that is never read. -/
noncomputable def parentBody (par : ι → κ) (W : κ → ConvexSpaceBody E) (K : ConvexSpaceBody E)
    (a : Finset ι) : ConvexSpaceBody E :=
  if h : a.Nonempty then W (par h.choose) else K

theorem parentBody_parentFibre {q : Finset ι} {par : ι → κ} {W : κ → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} {j : κ} (h : (parentFibre q par j).Nonempty) :
    parentBody par W K (parentFibre q par j) = W j := by
  rw [parentBody, dif_pos h, (mem_parentFibre.mp h.choose_spec).2]

/-- The fibres of a parent map form a `Finpartition` of the index set. -/
def parentFinpartition {q : Finset ι} {out : Finset κ} {par : ι → κ}
    (hpar : ∀ i ∈ q, par i ∈ out)
    (hne : ∀ j ∈ out, (parentFibre q par j).Nonempty) : Finpartition q :=
  Finpartition.mk (out.image (parentFibre q par))
    (by
      rw [Finset.supIndep_iff_pairwiseDisjoint]
      intro a ha b hb hab
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
      obtain ⟨j', _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
      refine Finset.disjoint_left.mpr fun i hi hi' ↦ hab ?_
      have hjj' : j = j' := (mem_parentFibre.mp hi).2.symm.trans (mem_parentFibre.mp hi').2
      rw [hjj'])
    (by
      ext i
      constructor
      · intro hi
        obtain ⟨a, ha, hia⟩ := Finset.mem_sup.mp hi
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
        exact (mem_parentFibre.mp hia).1
      · intro hi
        exact Finset.mem_sup.mpr ⟨parentFibre q par (par i),
          Finset.mem_image.mpr ⟨par i, hpar i hi, rfl⟩,
          mem_parentFibre.mpr ⟨hi, rfl⟩⟩)
    (by
      intro hmem
      obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hmem
      rw [Finset.bot_eq_empty] at hje
      exact Finset.nonempty_iff_ne_empty.mp (hne j hj) hje)

theorem parentFinpartition_parts {q : Finset ι} {out : Finset κ} {par : ι → κ}
    (hpar : ∀ i ∈ q, par i ∈ out)
    (hne : ∀ j ∈ out, (parentFibre q par j).Nonempty) :
    (parentFinpartition hpar hne).parts = out.image (parentFibre q par) := rfl

/-- Summing block by block over the fibres of `par` above a set `out'` of parents is the same as
summing over the children of those parents. -/
theorem sum_parentFibre_eq_sum_filter {q : Finset ι} {par : ι → κ} (out' : Finset κ)
    (f : ι → ENNReal) :
    ∑ j ∈ out', ∑ i ∈ parentFibre q par j, f i = ∑ i ∈ q with par i ∈ out', f i := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := {i ∈ q | par i ∈ out'}) (t := out') (g := par)
      (fun i hi => (Finset.mem_filter.mp hi).2) f]
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [parentFibre, Finset.mem_filter]
  constructor
  · rintro ⟨hiq, rfl⟩
    exact ⟨⟨hiq, hj⟩, rfl⟩
  · rintro ⟨⟨hiq, _⟩, rfl⟩
    exact ⟨hiq, rfl⟩

/-- **The retained-mass bound has teeth.**

If `q` is nonempty and every `V i` has `ethickness.scale` at least `δ > 0` — hence positive
volume — then the retained-mass bound of `Kakeya.ML2Spine.exists_subset_isFrostmanIn_parents'`
forces the retained children `{i ∈ q | par i ∈ out'}` to be nonempty, for **any** finite loss
`L`.  In particular the conclusion of that theorem is *not* dischargeable by `out' = ∅`, which
is exactly what the bare Frostman conclusion was. -/
theorem filter_nonempty_of_massBound [Nontrivial E] {q : Finset ι} {out' : Finset κ}
    {V : ι → ConvexSpaceBody E} {par : ι → κ} {δ : NNReal} {L : ENNReal}
    (hδ : 0 < δ) (hq : q.Nonempty)
    (hV : ∀ i ∈ q, (δ : ENNReal) ≤ Metric.ethickness.scale ℝ (V i).carrier)
    (hmass : ∑ i ∈ q, volume (V i).carrier ≤
      L * ∑ i ∈ q with par i ∈ out', volume (V i).carrier) :
    ({i ∈ q | par i ∈ out'} : Finset ι).Nonempty := by
  classical
  obtain ⟨i₀, hi₀⟩ := hq
  have hpos : 0 < volume (V i₀).carrier :=
    (V i₀).convex.volume_pos_of_scale_ne_zero
      (ne_bot_of_le_ne_bot (by simpa using hδ.ne') (hV i₀ hi₀))
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  rw [hempty] at hmass
  simp only [Finset.sum_empty, mul_zero, nonpos_iff_eq_zero] at hmass
  exact hpos.ne' (le_antisymm (hmass ▸ Finset.single_le_sum_of_canonicallyOrdered
    (f := fun i => volume (V i).carrier) hi₀) zero_le)

/-- The parent form of `Kakeya.ML2Spine.filter_nonempty_of_massBound`: the retained parent set
itself is nonempty. -/
theorem nonempty_of_massBound [Nontrivial E] {q : Finset ι} {out' : Finset κ}
    {V : ι → ConvexSpaceBody E} {par : ι → κ} {δ : NNReal} {L : ENNReal}
    (hδ : 0 < δ) (hq : q.Nonempty)
    (hV : ∀ i ∈ q, (δ : ENNReal) ≤ Metric.ethickness.scale ℝ (V i).carrier)
    (hmass : ∑ i ∈ q, volume (V i).carrier ≤
      L * ∑ i ∈ q with par i ∈ out', volume (V i).carrier) :
    out'.Nonempty := by
  obtain ⟨i, hi⟩ := filter_nonempty_of_massBound hδ hq hV hmass
  exact ⟨par i, (Finset.mem_filter.mp hi).2⟩

/-- **GWZ Remark 3.3(A) in parent-map form** (blueprint `inheritedDownwardsUpwardsRemark`, first
clause), the shape used at `section9.tex:178`.

Let `𝕍 = (V i)_{i ∈ q}` be `C`-Frostman inside `K`, with every `V i` of thickness at least `δ`,
and let `par : ι → κ` assign to each `i ∈ q` a parent index `par i ∈ out` whose body
`W (par i) ⊆ K` contains `V i`. Then some subfamily `out' ⊆ out` of the parents is

* **large**: its children carry all but a factor `L = Kakeya.ML2Spine.inheritedMassLoss` of the
  total mass `∑_{i ∈ q} |V i|`, and
* `L' · C`-Frostman in `K`, where `L' = inherited_upwards.C' n |q| δ R = 2L` is the
  dyadic-pigeonhole loss of `ConvexSpaceBody.IsFrostmanIn.inherited_upwards'` and `R` is any
  radius with `K ⊆ B(0, R)`.

Both clauses come from the *same* application of `ENNReal.dyadic_pigeonhole₁''`, through
`Kakeya.ML2Spine.exists_subset_mass_isFrostmanIn_parts`; the `Finpartition` bookkeeping is
performed here: the fibres of `par` partition `q`, `Kakeya.ML2Spine.parentBody` transports the
coarse bodies to those parts, and `ConvexSpaceBody.IsFrostmanIn.reindex` carries the Frostman
conclusion back to the coarse index set.

**The mass clause is not optional.** Without it the statement is provable from none of its
hypotheses by taking `out' = ∅`, because `IsFrostmanIn ∅ W K C` is `0 ≤ C * 0` for every `C`.
With it, `Kakeya.ML2Spine.nonempty_of_massBound` shows `out'` is nonempty as soon as `q` is.

The hypothesis `hne` is not a restriction: a parent with no children may simply be deleted
from `out`. -/
theorem exists_subset_isFrostmanIn_parents' [Nontrivial E]
    {q : Finset ι} {out : Finset κ}
    {V : ι → ConvexSpaceBody E} {W : κ → ConvexSpaceBody E} {par : ι → κ}
    {K : ConvexSpaceBody E} {C : ENNReal} {δ R : NNReal}
    (hδ : 0 < δ) (hR : 0 < R)
    (hFr : ConvexSpaceBody.IsFrostmanIn q V K C)
    (hV : ∀ i ∈ q, (δ : ENNReal) ≤ Metric.ethickness.scale ℝ (V i).carrier)
    (hpar : ∀ i ∈ q, par i ∈ out)
    (hne : ∀ j ∈ out, ∃ i ∈ q, par i = j)
    (hVW : ∀ i ∈ q, V i ≤ W (par i))
    (hWK : ∀ j ∈ out, W j ≤ K)
    (hK : K.carrier ⊆ Metric.closedBall 0 (R : ℝ)) :
    ∃ out' ⊆ out,
      (∑ i ∈ q, volume (V i).carrier ≤
          ((inheritedMassLoss (Module.finrank ℝ E) q.card δ R : NNReal) : ENNReal) *
            ∑ i ∈ q with par i ∈ out', volume (V i).carrier) ∧
        ConvexSpaceBody.IsFrostmanIn out' W K
          ((ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C'
            (Module.finrank ℝ E) q.card δ R : NNReal) * C) := by
  classical
  have hFne : ∀ j ∈ out, (parentFibre q par j).Nonempty := fun j hj ↦ by
    obtain ⟨i, hiq, hij⟩ := hne j hj
    exact ⟨i, mem_parentFibre.mpr ⟨hiq, hij⟩⟩
  have hFinj : Set.InjOn (parentFibre q par) ↑out := parentFibre_injOn hFne
  set P : Finpartition q := parentFinpartition hpar hFne with hPdef
  set Wp : Finset ι → ConvexSpaceBody E := parentBody par W K with hWpdef
  have hparts : P.parts = out.image (parentFibre q par) := rfl
  have hWp : ∀ j ∈ out, Wp (parentFibre q par j) = W j := fun j hj ↦
    parentBody_parentFibre (hFne j hj)
  have hVW' : ∀ a ∈ P.parts, ∀ i ∈ a, V i ≤ Wp a := by
    intro a ha i hi
    rw [hparts] at ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    rw [hWp j hj, ← (mem_parentFibre.mp hi).2]
    exact hVW i (mem_parentFibre.mp hi).1
  have hWK' : ∀ a ∈ P.parts, Wp a ≤ K := by
    intro a ha
    rw [hparts] at ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    rw [hWp j hj]
    exact hWK j hj
  obtain ⟨parts', hsub, hmass, hFr'⟩ :=
    exists_subset_mass_isFrostmanIn_parts (E := E) (ι := ι) (s := q)
      (V := V) (W := Wp) (K := K) (P := P) (C := C) (δ := δ) (R := R)
      hδ hR hFr hV hVW' hWK' hK
  have himg : ({j ∈ out | parentFibre q par j ∈ parts'} : Finset κ).image (parentFibre q par)
      = parts' := by
    ext a
    constructor
    · intro ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_filter.mp hj).2
    · intro ha
      have ha' : a ∈ P.parts := hsub ha
      rw [hparts] at ha'
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha'
      exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, ha⟩, rfl⟩
  refine ⟨{j ∈ out | parentFibre q par j ∈ parts'}, Finset.filter_subset _ _, ?_, ?_⟩
  · refine hmass.trans (le_of_eq ?_)
    congr 1
    conv_lhs => rw [← himg]
    rw [Finset.sum_image (fun a ha b hb hab =>
        hFinj (Finset.mem_coe.mpr (Finset.mem_filter.mp ha).1)
          (Finset.mem_coe.mpr (Finset.mem_filter.mp hb).1) hab),
      sum_parentFibre_eq_sum_filter]
  · have hbij : Set.BijOn (parentFibre q par)
        ↑({j ∈ out | parentFibre q par j ∈ parts'} : Finset κ) ↑parts' := by
      refine ⟨?_, ?_, ?_⟩
      · intro j hj
        exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
      · intro a ha b hb hab
        exact hFinj (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).1)
          (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).1) hab
      · intro a ha
        have ha' : a ∈ P.parts := hsub (Finset.mem_coe.mp ha)
        rw [hparts] at ha'
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha'
        exact ⟨j, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hj, Finset.mem_coe.mp ha⟩), rfl⟩
    have hre := (ConvexSpaceBody.IsFrostmanIn.reindex (s := parts') (W := Wp) (K := K)
      (C := ((ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C'
        (Module.finrank ℝ E) q.card δ R : NNReal) : ENNReal) * C)
      (t := ({j ∈ out | parentFibre q par j ∈ parts'} : Finset κ))
      (e := parentFibre q par) hbij).mpr hFr'
    refine isFrostmanIn_congr (fun j hj ↦ ?_) hre
    exact hWp j (Finset.mem_filter.mp hj).1

/-- **GWZ Remark 3.3(A) in parent-map form, inside the unit ball.** The `R = 1` case of
`Kakeya.ML2Spine.exists_subset_isFrostmanIn_parents'`, retained-mass clause included. -/
theorem exists_subset_isFrostmanIn_parents [Nontrivial E]
    {q : Finset ι} {out : Finset κ}
    {V : ι → ConvexSpaceBody E} {W : κ → ConvexSpaceBody E} {par : ι → κ}
    {K : ConvexSpaceBody E} {C : ENNReal} {δ : NNReal}
    (hδ : 0 < δ)
    (hFr : ConvexSpaceBody.IsFrostmanIn q V K C)
    (hV : ∀ i ∈ q, (δ : ENNReal) ≤ Metric.ethickness.scale ℝ (V i).carrier)
    (hpar : ∀ i ∈ q, par i ∈ out)
    (hne : ∀ j ∈ out, ∃ i ∈ q, par i = j)
    (hVW : ∀ i ∈ q, V i ≤ W (par i))
    (hWK : ∀ j ∈ out, W j ≤ K)
    (hK : K.carrier ⊆ Metric.closedBall 0 1) :
    ∃ out' ⊆ out,
      (∑ i ∈ q, volume (V i).carrier ≤
          ((inheritedMassLoss (Module.finrank ℝ E) q.card δ 1 : NNReal) : ENNReal) *
            ∑ i ∈ q with par i ∈ out', volume (V i).carrier) ∧
        ConvexSpaceBody.IsFrostmanIn out' W K
          ((ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C
            (Module.finrank ℝ E) q.card δ : NNReal) * C) := by
  rw [ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C_eq_C'_one (Module.finrank ℝ E) q.card δ]
  exact exists_subset_isFrostmanIn_parents' hδ zero_lt_one hFr hV hpar hne hVW hWK
    (by simpa using hK)

/-- **The Frostman-constant reading of the parent-map form.** The Section-9 call site
(`section9.tex:178`) states its conclusion as an upper bound on `C_F(𝕋̃_σ, T_b)`, which is
`ConvexSpaceBody.frostmanConstIn` of the coarse family in the anchor.

The retained-mass clause is carried through unchanged: without it the statement would again be
provable by `out' = ∅`, since `ConvexSpaceBody.frostmanConstIn ∅ W K = 0`
(`ConvexSpaceBody.frostmanConstIn_empty`). -/
theorem exists_subset_frostmanConstIn_parents' [Nontrivial E]
    {q : Finset ι} {out : Finset κ}
    {V : ι → ConvexSpaceBody E} {W : κ → ConvexSpaceBody E} {par : ι → κ}
    {K : ConvexSpaceBody E} {C : ENNReal} {δ R : NNReal}
    (hδ : 0 < δ) (hR : 0 < R)
    (hFr : ConvexSpaceBody.IsFrostmanIn q V K C)
    (hV : ∀ i ∈ q, (δ : ENNReal) ≤ Metric.ethickness.scale ℝ (V i).carrier)
    (hpar : ∀ i ∈ q, par i ∈ out)
    (hne : ∀ j ∈ out, ∃ i ∈ q, par i = j)
    (hVW : ∀ i ∈ q, V i ≤ W (par i))
    (hWK : ∀ j ∈ out, W j ≤ K)
    (hK : K.carrier ⊆ Metric.closedBall 0 (R : ℝ)) :
    ∃ out' ⊆ out,
      (∑ i ∈ q, volume (V i).carrier ≤
          ((inheritedMassLoss (Module.finrank ℝ E) q.card δ R : NNReal) : ENNReal) *
            ∑ i ∈ q with par i ∈ out', volume (V i).carrier) ∧
        ConvexSpaceBody.frostmanConstIn out' W K ≤
          ((ConvexSpaceBody.IsFrostmanIn.inherited_upwards.C'
            (Module.finrank ℝ E) q.card δ R : NNReal) : ENNReal) * C := by
  obtain ⟨out', hout', hmass, hFr'⟩ :=
    exists_subset_isFrostmanIn_parents' hδ hR hFr hV hpar hne hVW hWK hK
  exact ⟨out', hout', hmass, ConvexSpaceBody.frostmanConstIn_le hFr'⟩

end FrostmanUpwards

end Kakeya.ML2Spine
