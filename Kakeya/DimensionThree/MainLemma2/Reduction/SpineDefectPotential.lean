/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Uniform
public import Kakeya.Density
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineParams

/-!
# The defect potential on the geometric footprint 

The refined source's outer loop is driven by the potential (l.5763–5790, restated l.3977–3995)

```
 D_{k,l}(𝕊) = max_{R ∈ π_k(𝕊)} Δ_max(𝕊_l⟨R⟩),
 d_{k,l}(𝕊) = log max{1, D_{k,l}(𝕊)} / log(1/δ),
 Φ_h(𝕊)    = Σ_{0 ≤ k < l ≤ M} ⌈ d_{k,l}(𝕊)/h ⌉,
```

with the two properties the descent lives on: *"Passing to a nonempty subfamily can only decrease
every `D_{k,l}` and hence can only decrease `Φ_h`.  Moreover, if one normalized profile drops by at
least `2h`, then `Φ_h` drops by at least one."* (l.5779–5782.)

## The design point: the footprint, not the class

`D_{k,l}` is rendered here on the **geometric footprint** — the nodes of the hierarchy that
*contain* a member of the family — and never on `Tube.coverClass` or on
`Tube.GridCoverSystem.assign`.  The descent performs **two** restrictions, not one: it passes to a
subfamily `𝕊* ⊆ 𝕊`, and (if it ever re-enters the stopping run) it keeps the *nodes* while dropping
node *indices*.  A profile stated on the assignment is monotone under the first and **not** under
the second.  A profile stated on containment is monotone under both:
`Kakeya.ML2Core.pairProfile_mono_family` and `Kakeya.ML2Core.pairProfile_mono_cover`, whose
hypotheses are exactly the two clauses the stopping run's cut step exports
(`indexSet' ⊆ indexSet`, `tube' = tube`).  That is compatibility `T-D4`.

## Three points of the condition, recorded where they are paid

* `Kakeya.ML2Core.footprint` and `Kakeya.ML2Core.pairProfile` are classical: `∃ i ∈ S, _ ≤ _` and
  `_ ≤ _` on `ConvexSpaceBody` are undecidable, and `Tube.coverClass` uses the same idiom.
* `Kakeya.ML2Core.profileExp` sends `⊤` to the **ceiling** `4`, not to `0`.  `(⊤ : ℝ≥0∞).toReal`
  is `0`, so the naive `log (max 1 x.toReal)` would score an *infinite* profile as `0` and the
  descent could launder through it.  `Kakeya.ML2Core.pairProfile_ne_top` shows the branch is dead.
* `Kakeya.ML2Core.potential_le_Pmax` is **derived** from a cardinality binder, never asserted; and
  the binder it actually needs is on the **footprint**, not on the family — see the note on
  `Kakeya.ML2Core.card_footprint_le`.

## Contents

* `footprint`, `pairProfile`, `profileExp`, `potential`, `potentialCeil`, `Pmax`;
* monotonicity: `footprint_mono_family`, `footprint_mono_cover`, `pairProfile_mono_family`,
  `pairProfile_mono_cover`, `potential_mono_family`, `potential_mono_cover`;
* the ceiling: `pairProfile_le_card_footprint`, `pairProfile_ne_top`, `card_footprint_le`,
  `profileExp_le_of_toReal_le`, `card_pairs_lt`, `potential_le_potentialCeil`, `potential_le_Pmax`.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

/-! ## The footprint and the two-level profile -/

section Profile

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

open scoped Classical in
/-- **The footprint of a subfamily at a level** — the level-`l` nodes of `𝒰` that geometrically
contain a member of `S`.  Stated by containment, never through `𝒰.cover.assign`, so that it is
monotone under *both* restrictions the descent performs: shrinking `S`, and shrinking the cover's
own index sets.  Refined `D_{k,l}`, l.5763-5766. -/
noncomputable def footprint {ι : Type*} {δ Cu : NNReal} {u : Finset ι} {T : ι → Tube δ E}
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) (S : Finset ι) (l : ℕ) : Finset ι :=
  (𝒰.cover.indexSet l).filter
    (fun j => ∃ i ∈ S, (T i).toConvexSpaceBody ≤ (𝒰.cover.tube l j).toConvexSpaceBody)

open scoped Classical in
/-- **`D_{k,l}` on footprints** (refined l.5763-5766): the largest, over level-`k` footprint nodes,
of the maximal density of the level-`l` footprint nodes inside it. -/
noncomputable def pairProfile {ι : Type*} {δ Cu : NNReal} {u : Finset ι} {T : ι → Tube δ E}
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) (S : Finset ι) (k l : ℕ) : ENNReal :=
  (footprint 𝒰 S k).sup (fun j =>
    Kakeya.maxDensity
      ((footprint 𝒰 S l).filter
        (fun j' => (𝒰.cover.tube l j').toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody))
      (fun j' => (𝒰.cover.tube l j').toConvexSpaceBody))

/-- **`d_{k,l}`** (refined l.5768-5769).  `⊤` is sent to the *ceiling* `4`, not to `0`: the profile
is bounded by the block's own `#u ≤ δ^{-4}` binder, so `⊤` never occurs, but a definition that
silently scored an infinite profile as zero would be an anti-laziness defect and would make the
potential unsound. -/
noncomputable def profileExp (δ : NNReal) (x : ENNReal) : ℝ :=
  if x = ⊤ then 4 else Real.log (max 1 x.toReal) / Real.log (1 / (δ : ℝ))

/-- **`Φ_h`** (refined l.5771-5776), summed over `0 ≤ k < l ≤ ssfGridLen δ`. -/
noncomputable def potential {ι : Type*} {δ Cu : NNReal} {u : Finset ι} {T : ι → Tube δ E}
    (h : ℝ) (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) (S : Finset ι) : ℕ :=
  ∑ p ∈ (Finset.range (Tube.ssfGridLen δ + 1) ×ˢ Finset.range (Tube.ssfGridLen δ + 1)).filter
      (fun p => p.1 < p.2),
    ⌈profileExp δ (pairProfile 𝒰 S p.1 p.2) / h⌉₊

/-- The ceiling of the potential at a bound `D` on the normalized profiles. -/
noncomputable def potentialCeil (h D : ℝ) (δ : NNReal) : ℕ :=
  (Tube.ssfGridLen δ * (Tube.ssfGridLen δ + 1) / 2) * ⌈D / h⌉₊

/-- **`P_max`** (refined l.5785-5788).  The source's numerator is `5`; the tree's is `4`, because
the tree's cardinality binder `(u.card : NNReal) ≤ δ ^ (-(4:ℝ))` is a clean power, whereas the
source's `#𝕋 ≤ 2^{11}A₀δ^{-4}` needs one extra `δ^{-1}` to swallow `2^{11}A₀` (l.5780-5784).

**Measured caveat, recorded at the definition** : the profile lives
on the *footprint*, and the footprint exceeds the family by the uniformity constant
(`Kakeya.ML2Core.card_footprint_le`), so the binder that actually yields `d ≤ 4` is
`Cu · #u ≤ δ^{-4}` and not `#u ≤ δ^{-4}` alone.  `Kakeya.ML2Core.potential_le_potentialCeil` is
stated at a free `D` for exactly that reason; `Pmax` is `potentialCeil` at `D = 4`.

**The live ceiling is `D = 5`, not this one.**  Measured over the tree: `potentialCeil _ 5` has
eleven use sites against one for `potentialCeil _ 4`, so `Pmax` is the legacy reading and the
descent runs at `D = 5`.  Read `Kakeya.ML2Core.potential_le_potentialCeil` at the `D` its consumer
passes, not at `Pmax`'s. -/
noncomputable def Pmax (h : ℝ) (δ : NNReal) : ℕ :=
  (Tube.ssfGridLen δ * (Tube.ssfGridLen δ + 1) / 2) * ⌈(4 : ℝ) / h⌉₊

theorem Pmax_eq_potentialCeil (h : ℝ) (δ : NNReal) : Pmax h δ = potentialCeil h 4 δ := rfl

end Profile

/-! ## Monotonicity in the family -/

section MonoFamily

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ Cu : NNReal} {u : Finset ι} {T : ι → Tube δ E}

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem footprint_mono_family (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    {S S' : Finset ι} (hS : S' ⊆ S) (l : ℕ) : footprint 𝒰 S' l ⊆ footprint 𝒰 S l := by
  classical
  intro j hj
  simp only [footprint, Finset.mem_filter] at hj ⊢
  obtain ⟨hjidx, i, hi, hle⟩ := hj
  exact ⟨hjidx, i, hS hi, hle⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem footprintUnder_mono_family (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    {S S' : Finset ι} (hS : S' ⊆ S) (k l : ℕ) (j : ι) :
    (footprint 𝒰 S' l).filter
        (fun j' => (𝒰.cover.tube l j').toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody)
      ⊆ (footprint 𝒰 S l).filter
        (fun j' => (𝒰.cover.tube l j').toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody) :=
  Finset.filter_subset_filter _ (footprint_mono_family 𝒰 hS l)

omit [Nontrivial E] in
/-- **The source's "passing to a subfamily can only decrease every `D_{k,l}`"** (l.5779–5780). -/
theorem pairProfile_mono_family (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    {S S' : Finset ι} (hS : S' ⊆ S) (k l : ℕ) :
    pairProfile 𝒰 S' k l ≤ pairProfile 𝒰 S k l := by
  classical
  refine Finset.sup_le fun j hj => ?_
  refine le_trans (Kakeya.maxDensity_mono _ (footprintUnder_mono_family 𝒰 hS k l j)) ?_
  exact Finset.le_sup (f := fun j => Kakeya.maxDensity
    ((footprint 𝒰 S l).filter
      (fun j' => (𝒰.cover.tube l j').toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody))
    (fun j' => (𝒰.cover.tube l j').toConvexSpaceBody)) (footprint_mono_family 𝒰 hS k hj)

end MonoFamily

/-! ## Monotonicity in the hierarchy -/

section MonoCover

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ Cu Cu' : NNReal} {u u' : Finset ι} {T : ι → Tube δ E}

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The footprint is monotone under the cut step's own cover clauses.**

`hidx` and `htube` are, in this order, exactly the two conclusions that
`Kakeya.MultiScaleFac.exists_hoisted_cutsKT_run_band` exports: the index sets
only shrink, and the *nodes* are the same tubes. -/
theorem footprint_mono_cover {𝒰' : Tube.UniformTubeSet u' T (Tube.ssfGridLen δ) Cu'}
    {𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu}
    (hidx : ∀ n ≤ Tube.ssfGridLen δ, 𝒰'.cover.indexSet n ⊆ 𝒰.cover.indexSet n)
    (htube : ∀ n, 𝒰'.cover.tube n = 𝒰.cover.tube n)
    (S : Finset ι) {l : ℕ} (hl : l ≤ Tube.ssfGridLen δ) :
    footprint 𝒰' S l ⊆ footprint 𝒰 S l := by
  classical
  intro j hj
  simp only [footprint, Finset.mem_filter] at hj ⊢
  obtain ⟨hjidx, i, hi, hle⟩ := hj
  exact ⟨hidx l hl hjidx, i, hi, by rwa [htube l] at hle⟩

omit [Nontrivial E] in
/-- **compatibility `T-D4`: the profile is monotone under the hierarchy restriction.**

The hypotheses are exactly `exists_hoisted_cutsKT_run_band`'s two exported clauses, in its own
order, so the interface composes syntactically.  This is the clause that would silently vanish if
`Kakeya.ML2Core.pairProfile` were ever restated on `Tube.coverClass` or on
`Tube.GridCoverSystem.assign`. -/
theorem pairProfile_mono_cover {𝒰' : Tube.UniformTubeSet u' T (Tube.ssfGridLen δ) Cu'}
    {𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu}
    (hidx : ∀ n ≤ Tube.ssfGridLen δ, 𝒰'.cover.indexSet n ⊆ 𝒰.cover.indexSet n)
    (htube : ∀ n, 𝒰'.cover.tube n = 𝒰.cover.tube n)
    (S : Finset ι) {k l : ℕ} (hk : k ≤ Tube.ssfGridLen δ) (hl : l ≤ Tube.ssfGridLen δ) :
    pairProfile 𝒰' S k l ≤ pairProfile 𝒰 S k l := by
  classical
  refine Finset.sup_le fun j hj => ?_
  have hbody : (fun j' => (𝒰'.cover.tube l j').toConvexSpaceBody)
      = fun j' => (𝒰.cover.tube l j').toConvexSpaceBody := by rw [htube l]
  have hsub : (footprint 𝒰' S l).filter
        (fun j' => (𝒰'.cover.tube l j').toConvexSpaceBody ≤ (𝒰'.cover.tube k j).toConvexSpaceBody)
      ⊆ (footprint 𝒰 S l).filter
        (fun j' =>
          (𝒰.cover.tube l j').toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody) := by
    intro j' hj'
    simp only [Finset.mem_filter] at hj' ⊢
    refine ⟨footprint_mono_cover hidx htube S hl hj'.1, ?_⟩
    have := hj'.2
    rwa [htube l, htube k] at this
  rw [hbody]
  refine le_trans (Kakeya.maxDensity_mono _ hsub) ?_
  exact Finset.le_sup (f := fun j => Kakeya.maxDensity
    ((footprint 𝒰 S l).filter
      (fun j' => (𝒰.cover.tube l j').toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody))
    (fun j' => (𝒰.cover.tube l j').toConvexSpaceBody))
    (footprint_mono_cover hidx htube S hk hj)

end MonoCover

/-! ## The normalized profile -/

section Normalized

variable {δ : NNReal}

theorem profileExp_of_ne_top {x : ℝ≥0∞} (hx : x ≠ ⊤) :
    profileExp δ x = Real.log (max 1 x.toReal) / Real.log (1 / (δ : ℝ)) := if_neg hx

theorem log_one_div_pos (hδ0 : 0 < δ) (hδ1 : δ < 1) : 0 < Real.log (1 / (δ : ℝ)) := by
  refine Real.log_pos ?_
  rw [lt_div_iff₀ (by exact_mod_cast hδ0)]
  simpa using (by exact_mod_cast hδ1 : (δ : ℝ) < 1)

theorem profileExp_nonneg (hδ0 : 0 < δ) (hδ1 : δ < 1) (x : ℝ≥0∞) : 0 ≤ profileExp δ x := by
  by_cases hx : x = ⊤
  · simp [profileExp, hx]
  · rw [profileExp_of_ne_top hx]
    exact div_nonneg (Real.log_nonneg (le_max_left _ _)) (log_one_div_pos hδ0 hδ1).le

/-- **The normalized profile is monotone.**  This is what carries
`Kakeya.ML2Core.pairProfile_mono_family` and `Kakeya.ML2Core.pairProfile_mono_cover` to the
potential. -/
theorem profileExp_mono (hδ0 : 0 < δ) (hδ1 : δ < 1) {x y : ℝ≥0∞} (hy : y ≠ ⊤) (hxy : x ≤ y) :
    profileExp δ x ≤ profileExp δ y := by
  have hx : x ≠ ⊤ := fun h => hy (top_unique (h ▸ hxy))
  rw [profileExp_of_ne_top hx, profileExp_of_ne_top hy]
  have hreal : x.toReal ≤ y.toReal := ENNReal.toReal_mono hy hxy
  have hnum : Real.log (max 1 x.toReal) ≤ Real.log (max 1 y.toReal) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (max_le_max le_rfl hreal)
  exact div_le_div_of_nonneg_right hnum (log_one_div_pos hδ0 hδ1).le

/-- **A cardinality bound is an exponent bound.**  `x ≤ (1/δ)^D` gives `d ≤ D`; this is how the
ceiling is read off the family's own crude cardinality bound, and it is the only route by which
`Kakeya.ML2Core.potential_le_potentialCeil` obtains its `D`. -/
theorem profileExp_le_of_toReal_le (hδ0 : 0 < δ) (hδ1 : δ < 1) {x : ℝ≥0∞} (hx : x ≠ ⊤) {D : ℝ}
    (hD : 0 ≤ D) (hle : x.toReal ≤ (1 / (δ : ℝ)) ^ D) : profileExp δ x ≤ D := by
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hone : (1 : ℝ) < 1 / (δ : ℝ) := by
    rw [lt_div_iff₀ hδR]
    simpa using (by exact_mod_cast hδ1 : (δ : ℝ) < 1)
  have hlog : 0 < Real.log (1 / (δ : ℝ)) := Real.log_pos hone
  have hmax : max 1 x.toReal ≤ (1 / (δ : ℝ)) ^ D :=
    max_le (Real.one_le_rpow hone.le hD) hle
  have hnum : Real.log (max 1 x.toReal) ≤ D * Real.log (1 / (δ : ℝ)) := by
    refine le_trans (Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hmax) ?_
    rw [Real.log_rpow (by positivity)]
  rw [profileExp_of_ne_top hx, div_le_iff₀ hlog]
  exact hnum

end Normalized

/-! ## The pair count of the grid -/

section PairCount

theorem two_mul_sum_range_sub (n : ℕ) :
    2 * (∑ a ∈ Finset.range (n + 1), (n - a)) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hcongr : ∑ a ∈ Finset.range (n + 1), (n + 1 - a)
        = (∑ a ∈ Finset.range (n + 1), (n - a)) + (n + 1) := by
      have h1 : ∀ a ∈ Finset.range (n + 1), (n + 1 - a) = (n - a) + 1 := by
        intro a ha
        simp only [Finset.mem_range] at ha
        omega
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
      simp
    rw [hcongr]
    simp only [Nat.sub_self, Nat.add_zero]
    rw [Nat.mul_add, ih]
    ring

/-- **The number of ordered level pairs is exactly `N(N+1)/2`** — so
`Kakeya.ML2Core.Pmax`'s own pair count is the true one, and the ceiling below is not slack. -/
theorem card_pairs_lt (n : ℕ) :
    (((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter (fun p => p.1 < p.2)).card
      = n * (n + 1) / 2 := by
  classical
  rw [Finset.card_filter, Finset.sum_product]
  have hinner : ∀ a ∈ Finset.range (n + 1),
      (∑ b ∈ Finset.range (n + 1), if a < b then 1 else 0) = n - a := by
    intro a ha
    simp only [Finset.mem_range] at ha
    rw [← Finset.card_filter]
    have hIoo : (Finset.range (n + 1)).filter (fun b => a < b) = Finset.Ioo a (n + 1) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
      tauto
    rw [hIoo, Nat.card_Ioo]
    omega
  rw [Finset.sum_congr rfl hinner]
  have hgoal : (Finset.range (n + 1)).sum (fun a => n - a) = n * (n + 1) / 2 := by
    have h2 : 2 * ((Finset.range (n + 1)).sum (fun a => n - a)) = n * (n + 1) :=
      two_mul_sum_range_sub n
    exact (Nat.div_eq_of_eq_mul_left (by norm_num) (by omega)).symm
  exact hgoal

end PairCount

/-! ## The ceiling -/

section Ceiling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ Cu : NNReal} {u : Finset ι} {T : ι → Tube δ E}

omit [Nontrivial E] in
/-- `D_{k,l}` never exceeds the number of level-`l` cells of the footprint (`Δ_max ≤ #`). -/
theorem pairProfile_le_card_footprint (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (S : Finset ι) (k l : ℕ) :
    pairProfile 𝒰 S k l ≤ ((footprint 𝒰 S l).card : ℝ≥0∞) := by
  classical
  refine Finset.sup_le fun j _ => ?_
  refine le_trans (Kakeya.maxDensity_le_card _ _) ?_
  exact_mod_cast Nat.cast_le.mpr (Finset.card_filter_le _ _)

omit [Nontrivial E] in
/-- **The `⊤` branch of `Kakeya.ML2Core.profileExp` is provably dead**. -/
theorem pairProfile_ne_top (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (S : Finset ι) (k l : ℕ) : pairProfile 𝒰 S k l ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (pairProfile_le_card_footprint 𝒰 S k l)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The footprint is at most `Cu` times the family** — and **not** at most the family.

Every level-`l` node of the footprint contains some `i ∈ S`; the nodes that do so for a *fixed* `i`
all meet `i`'s own node, so `Tube.UniformTubeSet.card_meetingNodes_le` caps that fibre by `Cu`,
never by `1`.  This is the factor that makes the honest normalized-profile ceiling
`4 + log Cu / log(1/δ)` rather than `4` — the tree's analogue of the source's own extra unit
(l.5780–5784, where it swallows `2^{11}A₀` instead). -/
theorem card_footprint_le (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) {S : Finset ι}
    (hS : S ⊆ u) {l : ℕ} (hl : l ≤ Tube.ssfGridLen δ) :
    ((footprint 𝒰 S l).card : NNReal) ≤ Cu * S.card := by
  classical
  have hsub : footprint 𝒰 S l
      ⊆ S.biUnion (fun i => 𝒰.meetingNodes l (𝒰.cover.tube l (𝒰.cover.assign l i))) := by
    intro j hj
    simp only [footprint, Finset.mem_filter] at hj
    obtain ⟨hjidx, i, hi, hle⟩ := hj
    refine Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩
    simp only [Tube.UniformTubeSet.meetingNodes, Finset.mem_filter]
    exact ⟨hjidx, i, hS hi, hle, 𝒰.cover.le_tube_assign l hl i (hS hi)⟩
  calc ((footprint 𝒰 S l).card : NNReal)
      ≤ ((S.biUnion (fun i => 𝒰.meetingNodes l (𝒰.cover.tube l (𝒰.cover.assign l i)))).card :
          NNReal) := by exact_mod_cast Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ((∑ i ∈ S,
        (𝒰.meetingNodes l (𝒰.cover.tube l (𝒰.cover.assign l i))).card : ℕ) : NNReal) := by
        exact_mod_cast Nat.cast_le.mpr Finset.card_biUnion_le
    _ = ∑ i ∈ S, ((𝒰.meetingNodes l (𝒰.cover.tube l (𝒰.cover.assign l i))).card : NNReal) := by
        push_cast; rfl
    _ ≤ ∑ _i ∈ S, Cu := Finset.sum_le_sum fun i _ => 𝒰.card_meetingNodes_le hl _
    _ = Cu * S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

omit [Nontrivial E] in
/-- **The derived ceiling**.  The exponent `D` is a parameter and
the hypothesis is a *footprint* cardinality binder, so the `4` of `Kakeya.ML2Core.Pmax` is never
asserted: a call site chooses the `D` it can pay. -/
theorem potential_le_potentialCeil (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (S : Finset ι) {h D : ℝ} (hh : 0 < h) (hD : 0 ≤ D) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hcard : ∀ l ≤ Tube.ssfGridLen δ, ((footprint 𝒰 S l).card : ℝ) ≤ (1 / (δ : ℝ)) ^ D) :
    potential h 𝒰 S ≤ potentialCeil h D δ := by
  classical
  have hterm : ∀ p ∈ ((Finset.range (Tube.ssfGridLen δ + 1))
        ×ˢ (Finset.range (Tube.ssfGridLen δ + 1))).filter (fun p => p.1 < p.2),
      ⌈profileExp δ (pairProfile 𝒰 S p.1 p.2) / h⌉₊ ≤ ⌈D / h⌉₊ := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    refine Nat.ceil_le_ceil ?_
    have hexp : profileExp δ (pairProfile 𝒰 S p.1 p.2) ≤ D := by
      refine profileExp_le_of_toReal_le hδ0 hδ1 (pairProfile_ne_top 𝒰 S p.1 p.2) hD ?_
      refine le_trans ?_ (hcard p.2 (by omega))
      have hle := pairProfile_le_card_footprint 𝒰 S p.1 p.2
      have := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hle
      simpa using this
    exact div_le_div_of_nonneg_right hexp hh.le
  calc potential h 𝒰 S ≤ ∑ _p ∈ ((Finset.range (Tube.ssfGridLen δ + 1))
          ×ˢ (Finset.range (Tube.ssfGridLen δ + 1))).filter (fun p => p.1 < p.2), ⌈D / h⌉₊ :=
        Finset.sum_le_sum hterm
    _ = potentialCeil h D δ := by
        rw [Finset.sum_const, smul_eq_mul, card_pairs_lt, potentialCeil]

end Ceiling

/-! ## The potential is monotone -/

section MonoPotential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ Cu Cu' : NNReal} {u u' : Finset ι} {T : ι → Tube δ E}

omit [Nontrivial E] in
/-- **The source's "passing to a subfamily can only decrease `Φ_h`"** (l.5779–5781). -/
theorem potential_mono_family (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    {S S' : Finset ι} (hS : S' ⊆ S) {h : ℝ} (hh : 0 < h) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    potential h 𝒰 S' ≤ potential h 𝒰 S := by
  classical
  refine Finset.sum_le_sum fun p _ => Nat.ceil_le_ceil ?_
  refine div_le_div_of_nonneg_right ?_ hh.le
  exact profileExp_mono hδ0 hδ1 (pairProfile_ne_top 𝒰 S p.1 p.2)
    (pairProfile_mono_family 𝒰 hS p.1 p.2)

omit [Nontrivial E] in
/-- **compatibility `T-D4`, at the potential.**  The hypotheses are exactly the two clauses the stopping
run's cut step exports, in its own order. -/
theorem potential_mono_cover {𝒰' : Tube.UniformTubeSet u' T (Tube.ssfGridLen δ) Cu'}
    {𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu}
    (hidx : ∀ n ≤ Tube.ssfGridLen δ, 𝒰'.cover.indexSet n ⊆ 𝒰.cover.indexSet n)
    (htube : ∀ n, 𝒰'.cover.tube n = 𝒰.cover.tube n)
    (S : Finset ι) {h : ℝ} (hh : 0 < h) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    potential h 𝒰' S ≤ potential h 𝒰 S := by
  classical
  refine Finset.sum_le_sum fun p hp => Nat.ceil_le_ceil ?_
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
  refine div_le_div_of_nonneg_right ?_ hh.le
  exact profileExp_mono hδ0 hδ1 (pairProfile_ne_top 𝒰 S p.1 p.2)
    (pairProfile_mono_cover hidx htube S (by omega) (by omega))

end MonoPotential

/-! ## `Φ_h ≤ P_max`, derived -/

section PmaxDerived

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ Cu : NNReal} {u : Finset ι} {T : ι → Tube δ E}

theorem one_div_rpow_eq (δ : NNReal) (D : ℝ) : (1 / (δ : ℝ)) ^ D = (δ : ℝ) ^ (-D) := by
  have hδR : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  rw [one_div, Real.inv_rpow hδR, Real.rpow_neg hδR]

omit [Nontrivial E] in
/-- **`Φ_h ≤ P_max`, derived from a cardinality binder** —, correction 3.

The binder is on `Cu · #u`, **not** on `#u` alone.  That is not a weakening: the profile lives on
the footprint, and `Kakeya.ML2Core.card_footprint_le` is the only bound available between the
footprint and the family.  `Kakeya.ML2Core.potential_le_potentialCeil_five` is the same statement
read off the tree's own block binder `(u.card : NNReal) ≤ δ ^ (-(4:ℝ))`, at the source's own
exponent `5`. -/
theorem potential_le_Pmax (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) {S : Finset ι}
    (hS : S ⊆ u) {h : ℝ} (hh : 0 < h) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hcard : (Cu : ℝ) * (u.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ))) :
    potential h 𝒰 S ≤ Pmax h δ := by
  rw [Pmax_eq_potentialCeil]
  refine potential_le_potentialCeil 𝒰 S hh (by norm_num) hδ0 hδ1 (fun l hl => ?_)
  rw [one_div_rpow_eq δ]
  calc ((footprint 𝒰 S l).card : ℝ) ≤ (Cu : ℝ) * (S.card : ℝ) := by
        exact_mod_cast card_footprint_le 𝒰 hS hl
    _ ≤ (Cu : ℝ) * (u.card : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_le_card hS) Cu.coe_nonneg
    _ ≤ (δ : ℝ) ^ (-(4 : ℝ)) := hcard

omit [Nontrivial E] in
/-- **`Φ_h ≤ P_max` at the source's own exponent `5`, from the tree's own binders.**

`(u.card : NNReal) ≤ δ ^ (-(4:ℝ))` is the block's cardinality binder verbatim
(`Kakeya.ML2Assembly.card_le_rpow_neg_four`); `Cu ≤ δ^{-1}` is a `δ`-threshold on the `δ`-free
hierarchy constant, available because `Cu ≤ Cu₀` with `Cu₀` chosen before `δ`.  The extra unit is
the source's own (l.5780–5784), spent here on the footprint-versus-family multiplicity instead of
on `2^{11}A₀`. -/
theorem potential_le_potentialCeil_five (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    {S : Finset ι} (hS : S ⊆ u) {h : ℝ} (hh : 0 < h) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hCu : (Cu : ℝ) ≤ (δ : ℝ) ^ (-(1 : ℝ))) (hu : (u.card : ℝ) ≤ (δ : ℝ) ^ (-(4 : ℝ))) :
    potential h 𝒰 S ≤ potentialCeil h 5 δ := by
  have hδR : (0 : ℝ) < (δ : ℝ) := hδ0
  refine potential_le_potentialCeil 𝒰 S hh (by norm_num) hδ0 hδ1 (fun l hl => ?_)
  rw [one_div_rpow_eq δ]
  have hprod : (δ : ℝ) ^ (-(1 : ℝ)) * (δ : ℝ) ^ (-(4 : ℝ)) = (δ : ℝ) ^ (-(5 : ℝ)) := by
    rw [← Real.rpow_add hδR]
    norm_num
  calc ((footprint 𝒰 S l).card : ℝ) ≤ (Cu : ℝ) * (S.card : ℝ) := by
        exact_mod_cast card_footprint_le 𝒰 hS hl
    _ ≤ (δ : ℝ) ^ (-(1 : ℝ)) * (δ : ℝ) ^ (-(4 : ℝ)) := by
        refine mul_le_mul hCu (le_trans ?_ hu) (by positivity) (by positivity)
        exact_mod_cast Finset.card_le_card hS
    _ = (δ : ℝ) ^ (-(5 : ℝ)) := hprod

end PmaxDerived

/-! ## The two spine-derived constants of the descent, named once -/

section Constants

/-- **`h`, the potential's step** (refined l.4007: `h = η₁ε²/8`).

`ML2Spine.spineRung β ϖ ε₁ gain dens 1` is the tree's `η₁` and `ML2Spine.spineDiv ϖ ε₁` its `ε`;
both are `δ`-free, so `h` is fixed before `δ` exactly as the source requires.  Named here, beside
`Kakeya.ML2Core.Pmax`, so that the two blocks cannot each choose their own. -/
noncomputable def defectH (β ϖ ε₁ : ℝ) (gain dens : ℝ → ℝ) : ℝ :=
  ML2Spine.spineRung β ϖ ε₁ gain dens 1 * ML2Spine.spineDiv ϖ ε₁ ^ 2 / 8

/-- **`α`, the descent's margin** (the source's `a₀`, refined l.5946).

`Λ^{P_max+1} ≤ δ^{-α}` is what the ledger absorbs, and `α` is paid **once**: out of the `(G₁)`
budget on the left and out of the terminal gain on the right.  It is `δ`-free and chosen before
`δ`, like `h`. -/
noncomputable def defectMargin (β ϖ ε₁ : ℝ) (gain dens : ℝ → ℝ) : ℝ :=
  ML2Spine.spineNu β ϖ ε₁ gain dens

theorem defectMargin_pos {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} (hβ : 0 < β) (hϖ : 0 < ϖ)
    (hε₁ : 0 < ε₁) (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ) :
    0 < defectMargin β ϖ ε₁ gain dens :=
  ML2Spine.spineNu_pos hβ hϖ hε₁ hgain hdens

/-- The margin **is** `ν`; `Kakeya.ML2Core.defectMargin_le_budget`
(`Reduction/SpineDefectDichotomy.lean`) is where it is checked against the `(G₁)` budget, the
inequality `ν ≤ β/48000` living downstream of this leaf. -/
theorem defectMargin_eq (β ϖ ε₁ : ℝ) (gain dens : ℝ → ℝ) :
    defectMargin β ϖ ε₁ gain dens = ML2Spine.spineNu β ϖ ε₁ gain dens := rfl

end Constants

end Kakeya.ML2Core
