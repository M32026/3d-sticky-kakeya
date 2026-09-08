/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FibreCommon
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectConstantLedger

/-!
# `P6` — the `(D)` exit: a destroyed lower concentration is a potential drop

The refined source, l.4118–4131, verbatim:

```
 If a required lower concentration fails after the restrictions, then for one m ∈ W the old value
 is larger than ½Θ_m^τ, while the new value is smaller than ½Θ_m^{τ/2}.  Hence
   d_{a,m}(S') − d_{a,m}(S*) ≥ τε²/4 ≥ 2h.
 Every other D_{k,l} is monotone under restriction, so the corresponding ceiling drops by at
 least one and no other ceiling increases.  This is (D).
```

together with `log Θ_m / log(1/δ) ≥ ε²/2` (l.4116–4118) and `h = η₁ε²/8` (l.4007).

## The alignment `D-R1`, and why it works — the first item, as a named lemma

 names the risk: the source's two concentration bounds are on
`Δ_max(𝕊_m⟨S⟩)`, the **assignment fibre**, whereas `Kakeya.ML2Core.pairProfile` is on
**footprints**.  The upper bound transfers downwards for free; the lower bound is the direction
that needs work.

The resolution is `Kakeya.ML2Core.pairProfile_ambient`: **on the ambient family the two objects are
literally equal.**  Every node of the hierarchy is occupied — that is
`Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent`, which is exactly where Definition
2.1(iii)'s lower half earns its keep — so `footprint 𝒰 u l = 𝒰.cover.indexSet l` and the level-`l`
footprint under a level-`a` node **is** `Tube.UniformTubeSet.nodesUnder`.  Hence
`Kakeya.ML2Core.le_mul_pairProfile_of_level_clause`: the window's own level clause, which is stated
on `nodesUnder` (`ML2Reduction.IsKatzTaoDividingWindowLevels.le_level_maxDensity`, the containment
form `W1`), gives the *before* bound on `pairProfile` directly.  That is the source's reading — the
lower concentration is tested **before** the restrictions — and it is why the order of l.4392–4395
is essential.

## The arithmetic, and a measurement the source's sketch leaves implicit

Writing `L = log(1/δ)`, `A = ½Θ^{τ/2}` and `B = ½Θ^τ`,

```
 log A / L + 2h ≤ log B / L    ⟺    2h ≤ (τ/2)·(log Θ / L),
```

because **`log 2` occurs on both sides and cancels**.  So the trigger costs *no* `δ`-threshold at
all: with `log Θ / L ≥ ε²/2` the requirement is `2h ≤ τε²/4`, which is the source's own inequality
and is exactly `h = η₁ε²/8` together with `τ = η_{J+1} ≥ η₁`.  The factor `½` — which one would
expect to have to absorb — is free.

## Contents

* the alignment: `footprint_ambient`, `pairProfile_ambient`, `le_mul_pairProfile_of_level_clause`;
* the arithmetic: `profileExp_drop_of_bounds`;
* the descent step: `potential_drop_of_profileExp_drop`;
* **the exit: `profileDrop_of_concentration_destroyed`.**
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

/-! ## `D-R1`: the footprint profile at the ambient family is the source's `D_{k,l}` -/

section Alignment

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ Cu : NNReal} {u : Finset ι} {T : ι → Tube δ E}

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Every node is occupied, so the ambient footprint is the whole index set.**

This is where GWZ Definition 2.1(iii)'s *lower* half earns its keep: it is what
`Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent` consumes. -/
theorem footprint_ambient (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) (hu : u.Nonempty)
    {l : ℕ} (hl : l ≤ Tube.ssfGridLen δ) : footprint 𝒰 u l = 𝒰.cover.indexSet l := by
  classical
  refine Finset.Subset.antisymm (Finset.filter_subset _ _) fun j hj => ?_
  obtain ⟨i, hi⟩ := Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent 𝒰 hl hu hj
  simp only [Tube.coverClass, Finset.mem_filter] at hi
  refine Finset.mem_filter.mpr ⟨hj, i, hi.1, ?_⟩
  have hle := 𝒰.cover.le_tube_assign l hl i hi.1
  rwa [hi.2] at hle

omit [Nontrivial E] in
/-- **The alignment `D-R1`.**  On the ambient family the footprint profile *is* the source's
`D_{a,m}`: a supremum, over the level-`a` nodes, of the maximal density of
`Tube.UniformTubeSet.nodesUnder` — which is precisely the family the window's level clause `W1`
bounds below. -/
theorem pairProfile_ambient (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) (hu : u.Nonempty)
    {a m : ℕ} (ha : a ≤ Tube.ssfGridLen δ) (hm : m ≤ Tube.ssfGridLen δ) :
    pairProfile 𝒰 u a m
      = (𝒰.cover.indexSet a).sup fun j =>
          Kakeya.maxDensity (𝒰.nodesUnder m a j)
            fun j' => (𝒰.cover.tube m j').toConvexSpaceBody := by
  classical
  rw [pairProfile, footprint_ambient 𝒰 hu ha]
  refine Finset.sup_congr rfl fun j _ => ?_
  congr 1
  rw [footprint_ambient 𝒰 hu hm]
  rfl

omit [Nontrivial E] in
/-- **The window's level clause, read on the potential's own profile.**

`hlevel` is exactly the shape of `ML2Reduction.IsKatzTaoDividingWindowLevels.le_level_maxDensity`
at the level `m`: a lower bound on `Cstar · Δ_max(𝕋_m[T_a])`, universal in the level-`a` node.  It
transfers to `Kakeya.ML2Core.pairProfile` with no loss at all, because the profile is a supremum
over exactly those nodes. -/
theorem le_mul_pairProfile_of_level_clause (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (hu : u.Nonempty) {a m : ℕ} (ha : a ≤ Tube.ssfGridLen δ) (hm : m ≤ Tube.ssfGridLen δ)
    {Cstar x : ℝ≥0∞}
    (hlevel : ∀ j ∈ 𝒰.cover.indexSet a, x ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder m a j)
      fun j' => (𝒰.cover.tube m j').toConvexSpaceBody) :
    x ≤ Cstar * pairProfile 𝒰 u a m := by
  classical
  obtain ⟨i, hi⟩ := hu
  have hj : 𝒰.cover.assign a i ∈ 𝒰.cover.indexSet a := 𝒰.cover.assign_mem a ha i hi
  refine le_trans (hlevel _ hj) ?_
  refine mul_le_mul' le_rfl ?_
  rw [pairProfile_ambient 𝒰 ⟨i, hi⟩ ha hm]
  exact Finset.le_sup (f := fun j => Kakeya.maxDensity (𝒰.nodesUnder m a j)
    fun j' => (𝒰.cover.tube m j').toConvexSpaceBody) hj

omit [Nontrivial E] in
/-- **: the window clause read on the RESTRICTED hierarchy.**

`Kakeya.ML2Core.pairProfile_ambient` identifies the footprint profile with the source's `D_{a,m}`
only at the family the hierarchy is built on.  In the descent the current family is `S ⊊ u`, so the
producer reads `W1` on `Tube.UniformTubeSet.restrictOccupied 𝒰 hS hhom` — the *same* nodes and the
*same* constant `Cu` (`C-D1`), with the index sets shrunk to the nodes `S` occupies.

The lower bound then transfers **upwards** to the ambient profile, which is the direction
`hbefore` needs: the restricted footprint is contained in the ambient one, so
`pairProfile (restrictOccupied …) S a m ≤ pairProfile 𝒰 S a m`
(`Kakeya.ML2Core.pairProfile_mono_cover` at `restrictOccupied_cover`'s two clauses).  The potential
itself stays on the fixed `𝒰`, as `C-D1` requires. -/
theorem le_mul_pairProfile_of_level_clause_restricted
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) {S : Finset ι} (hS : S ⊆ u)
    (hhom : IsClassHomogeneousOn 𝒰 S) (hSne : S.Nonempty)
    {a m : ℕ} (ha : a ≤ Tube.ssfGridLen δ) (hm : m ≤ Tube.ssfGridLen δ)
    {Cstar x : ℝ≥0∞}
    (hlevel : ∀ j ∈ (𝒰.restrictOccupied hS hhom).cover.indexSet a,
      x ≤ Cstar * Kakeya.maxDensity ((𝒰.restrictOccupied hS hhom).nodesUnder m a j)
        fun j' => ((𝒰.restrictOccupied hS hhom).cover.tube m j').toConvexSpaceBody) :
    x ≤ Cstar * pairProfile 𝒰 S a m := by
  have h1 := le_mul_pairProfile_of_level_clause (𝒰.restrictOccupied hS hhom) hSne ha hm hlevel
  obtain ⟨hidx, htube⟩ := restrictOccupied_cover 𝒰 hS hhom
  exact h1.trans (mul_le_mul' le_rfl (pairProfile_mono_cover hidx htube S ha hm))

end Alignment

/-! ## The arithmetic of the trigger -/

section Arithmetic

variable {δ : NNReal}

/-- **The normalized profile drops by `2h`.**

`x` is the profile before the restrictions, bounded below by `B`; `y` is the profile after, bounded
above by `A`; `hgap` is the source's `d(S') − d(S*) ≥ 2h` written on the two bounds.  Both `A` and
`B` are asked to be at least `1` because `d` is `log max{1, ·}`. -/
theorem profileExp_drop_of_bounds (hδ0 : 0 < δ) (hδ1 : δ < 1) {x y : ℝ≥0∞}
    (hx : x ≠ ⊤) (hy : y ≠ ⊤) {A B h : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hbefore : ENNReal.ofReal B ≤ x) (hafter : y ≤ ENNReal.ofReal A)
    (hgap : Real.log A / Real.log (1 / (δ : ℝ)) + 2 * h
      ≤ Real.log B / Real.log (1 / (δ : ℝ))) :
    profileExp δ y + 2 * h ≤ profileExp δ x := by
  have hL : 0 < Real.log (1 / (δ : ℝ)) := log_one_div_pos hδ0 hδ1
  -- the after bound
  have hyA : Real.log (max 1 y.toReal) ≤ Real.log A := by
    have hyR : y.toReal ≤ A := ENNReal.toReal_le_of_le_ofReal (le_trans zero_le_one hA) hafter
    exact Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (max_le hA hyR)
  -- the before bound
  have hxB : Real.log B ≤ Real.log (max 1 x.toReal) := by
    have hxR : B ≤ x.toReal := (ENNReal.ofReal_le_iff_le_toReal hx).mp hbefore
    exact Real.log_le_log (lt_of_lt_of_le zero_lt_one hB) (le_trans hxR (le_max_right _ _))
  rw [profileExp_of_ne_top hx, profileExp_of_ne_top hy]
  have h1 : Real.log (max 1 y.toReal) / Real.log (1 / (δ : ℝ))
      ≤ Real.log A / Real.log (1 / (δ : ℝ)) := div_le_div_of_nonneg_right hyA hL.le
  have h2 : Real.log B / Real.log (1 / (δ : ℝ))
      ≤ Real.log (max 1 x.toReal) / Real.log (1 / (δ : ℝ)) := div_le_div_of_nonneg_right hxB hL.le
  linarith

end Arithmetic

/-! ## The descent step -/

section Step

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ Cu : NNReal} {u : Finset ι} {T : ι → Tube δ E}

omit [Nontrivial E] in
/-- **One profile drop of `2h` costs one unit of `Φ_h`** (refined l.5781–5782, l.4128–4131).

Every other pair is monotone under restriction (`Kakeya.ML2Core.pairProfile_mono_family`), and the
failing pair's own ceiling drops by two; so the sum drops by at least one. -/
theorem potential_drop_of_profileExp_drop (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    {S S' : Finset ι} (hS : S' ⊆ S) {h : ℝ} (hh : 0 < h) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {a m : ℕ} (ham : a < m) (hm : m ≤ Tube.ssfGridLen δ)
    (hdrop : profileExp δ (pairProfile 𝒰 S' a m) + 2 * h
      ≤ profileExp δ (pairProfile 𝒰 S a m)) :
    potential h 𝒰 S' + 1 ≤ potential h 𝒰 S := by
  classical
  set F := ((Finset.range (Tube.ssfGridLen δ + 1)) ×ˢ (Finset.range (Tube.ssfGridLen δ + 1))).filter
    (fun p => p.1 < p.2) with hF
  have hmem : (a, m) ∈ F := by
    simp only [hF, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by omega, by omega⟩, ham⟩
  have hmono : ∀ p ∈ F, ⌈profileExp δ (pairProfile 𝒰 S' p.1 p.2) / h⌉₊
      ≤ ⌈profileExp δ (pairProfile 𝒰 S p.1 p.2) / h⌉₊ := by
    intro p _
    refine Nat.ceil_le_ceil (div_le_div_of_nonneg_right ?_ hh.le)
    exact profileExp_mono hδ0 hδ1 (pairProfile_ne_top 𝒰 S p.1 p.2)
      (pairProfile_mono_family 𝒰 hS p.1 p.2)
  have hstrict : ⌈profileExp δ (pairProfile 𝒰 S' a m) / h⌉₊
      < ⌈profileExp δ (pairProfile 𝒰 S a m) / h⌉₊ := by
    have hnn : 0 ≤ profileExp δ (pairProfile 𝒰 S' a m) / h :=
      div_nonneg (profileExp_nonneg hδ0 hδ1 _) hh.le
    have hsplit : (profileExp δ (pairProfile 𝒰 S' a m) + 2 * h) / h
        = profileExp δ (pairProfile 𝒰 S' a m) / h + ((2 : ℕ) : ℝ) := by
      field_simp
      ring
    have hceil : ⌈profileExp δ (pairProfile 𝒰 S' a m) / h⌉₊ + 2
        ≤ ⌈profileExp δ (pairProfile 𝒰 S a m) / h⌉₊ := by
      have hmono2 : ⌈(profileExp δ (pairProfile 𝒰 S' a m) + 2 * h) / h⌉₊
          ≤ ⌈profileExp δ (pairProfile 𝒰 S a m) / h⌉₊ :=
        Nat.ceil_le_ceil (div_le_div_of_nonneg_right hdrop hh.le)
      rwa [hsplit, Nat.ceil_add_natCast hnn] at hmono2
    omega
  have hlt : ∑ p ∈ F, ⌈profileExp δ (pairProfile 𝒰 S' p.1 p.2) / h⌉₊
      < ∑ p ∈ F, ⌈profileExp δ (pairProfile 𝒰 S p.1 p.2) / h⌉₊ :=
    Finset.sum_lt_sum hmono ⟨(a, m), hmem, hstrict⟩
  simpa [potential, hF] using hlt

end Step

/-! ## The `(D)` exit -/

section Exit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ Cu : NNReal} {u : Finset ι} {T : ι → Tube δ E}

omit [Nontrivial E] in
/-- **`(D)`: a destroyed lower concentration is a potential drop** (refined l.4118–4131).

`hbefore` is *"the old value is larger than ½Θ^τ"*, `hafter` is *"the new value is smaller than
½Θ^{τ/2}"*, and `hgap` is *"`τε²/4 ≥ 2h`"* — read through `log Θ / log(1/δ) ≥ ε²/2`, which is the
window's own scale arithmetic.  The factor `½` cancels between the two bounds and costs nothing.

`hΘ2` is the only side condition beyond the source's: `½Θ^{τ/2} ≥ 1`, i.e. `Θ^{τ/2} ≥ 2`.  It is
automatic below a `δ`-threshold, since `hgap` forces `Θ ≥ (1/δ)^{4h/τ}`; it is a hypothesis here
so that the threshold is spent at the call site rather than inside the exit. -/
theorem profileDrop_of_concentration_destroyed
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) {S S' : Finset ι} (hS : S' ⊆ S)
    {h τ Θ : ℝ} (hh : 0 < h) (hΘ0 : 0 < Θ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {a m : ℕ} (ham : a < m) (hm : m ≤ Tube.ssfGridLen δ)
    (hΘ2 : 2 ≤ Θ ^ (τ / 2))
    (hbefore : ENNReal.ofReal (Θ ^ τ / 2) ≤ pairProfile 𝒰 S a m)
    (hafter : pairProfile 𝒰 S' a m ≤ ENNReal.ofReal (Θ ^ (τ / 2) / 2))
    (hgap : 2 * h ≤ (τ / 2) * (Real.log Θ / Real.log (1 / (δ : ℝ)))) :
    potential h 𝒰 S' + 1 ≤ potential h 𝒰 S := by
  have hL : 0 < Real.log (1 / (δ : ℝ)) := log_one_div_pos hδ0 hδ1
  have hhalf : Θ ^ τ = Θ ^ (τ / 2) * Θ ^ (τ / 2) := by
    rw [← Real.rpow_add hΘ0]
    ring_nf
  have hA : (1 : ℝ) ≤ Θ ^ (τ / 2) / 2 := by linarith
  have hB : (1 : ℝ) ≤ Θ ^ τ / 2 := by nlinarith
  -- the two logarithms, with the `½` cancelling
  have hlogA : Real.log (Θ ^ (τ / 2) / 2) = (τ / 2) * Real.log Θ - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hΘ0]
  have hlogB : Real.log (Θ ^ τ / 2) = τ * Real.log Θ - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hΘ0]
  have hgapLog : Real.log (Θ ^ (τ / 2) / 2) / Real.log (1 / (δ : ℝ)) + 2 * h
      ≤ Real.log (Θ ^ τ / 2) / Real.log (1 / (δ : ℝ)) := by
    rw [hlogA, hlogB, div_add' _ _ _ hL.ne', div_le_div_iff_of_pos_right hL]
    have hsplit : (τ / 2) * (Real.log Θ / Real.log (1 / (δ : ℝ)))
        * Real.log (1 / (δ : ℝ)) = (τ / 2) * Real.log Θ := by
      field_simp
    nlinarith [hgap, hL]
  refine potential_drop_of_profileExp_drop 𝒰 hS hh hδ0 hδ1 ham hm ?_
  exact profileExp_drop_of_bounds hδ0 hδ1 (pairProfile_ne_top 𝒰 S a m)
    (pairProfile_ne_top 𝒰 S' a m) hA hB hbefore hafter hgapLog

end Exit

/-! ## Non-vacuity of the trigger -/

section NonVacuity

/-- **The trigger's hypotheses are jointly satisfiable** — the anti-vacuity control on
`Kakeya.ML2Core.profileDrop_of_concentration_destroyed`.

`δ = 1/2`, `Θ = 4`, `τ = 2`, `h = 1/100`: the normalized profile of `Θ` is `log 4 / log 2 = 2`, so
`(τ/2)·2 = 2 ≥ 2h`, `Θ^{τ/2} = 4 ≥ 2`, and the *before* bound `Θ^τ/2 = 8` is strictly above the
*after* bound `Θ^{τ/2}/2 = 2`.  Without this, every hypothesis of the `(D)` exit could be
contradictory and the exit would prove nothing. -/
theorem exists_concentration_destroyed_witness :
    ∃ (δ : NNReal) (Θ τ h : ℝ),
      0 < δ ∧ δ < 1 ∧ 0 < h ∧ 0 < Θ ∧
      2 ≤ Θ ^ (τ / 2) ∧
      2 * h ≤ (τ / 2) * (Real.log Θ / Real.log (1 / (δ : ℝ))) ∧
      (1 : ℝ) ≤ Θ ^ (τ / 2) / 2 ∧
      Θ ^ (τ / 2) / 2 < Θ ^ τ / 2 := by
  refine ⟨1 / 2, 4, 2, 1 / 100, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · norm_num
  · have hlog : Real.log 4 / Real.log 2 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have h2 : Real.log 2 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
      field_simp
      norm_num
    norm_num
    linarith [hlog]
  · norm_num
  · have h16 : ((4 : ℝ) ^ (2 : ℝ)) = 16 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    norm_num [h16]

end NonVacuity

end Kakeya.ML2Core
