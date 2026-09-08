/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Shading
public import Kakeya.Density
public import Kakeya.FactorFamily.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.Floor.Extended
public import Kakeya.Mathlib.Algebra.Div
public import Kakeya.Mathlib.MeasureTheory.Action

/-! In this file we collect stuffs about multiplicity, `μ` in [GWZ] -/

@[expose] public section
open MeasureTheory Convexity

namespace Finset

variable {α σ ι : Type*} (s : Finset ι) (A : ι → σ) (x : α) [SetLike σ α]

noncomputable instance : DecidablePred fun i ↦ x ∈ A i := Classical.decPred _

/-- The number of members of `s` whose associated set `A i` contains the point `x`. -/
noncomputable abbrev multiplicityAt := {i ∈ s | x ∈ A i}.card

lemma multiplicityAt_le_card : multiplicityAt s A x ≤ s.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

lemma multiplicityAt_eq_zero_iff : multiplicityAt s A x = 0 ↔ ∀ i ∈ s, x ∉ A i := by
  simp [multiplicityAt]

lemma multiplicityAt_pos_iff : 0 < multiplicityAt s A x ↔ ∃ i ∈ s, x ∈ A i := by
  simp [multiplicityAt, Finset.card_pos, Finset.Nonempty, Finset.mem_filter]

end Finset

namespace ShadedBody

section Multiplicity

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}
  (s : Finset ι) (V : ι → ShadedBody E)

/-- `µ(W, Y)` defined in [GWZ, Eq (7)]: multiplicity of a shaded family.
    This is `(∑ |Y(W)|) / |U(W, Y)|`. -/
noncomputable def multiplicity : ENNReal :=
  (∑ i ∈ s, volume (V i).shade) / volume (⋃ i ∈ s, (V i).shade)

lemma multiplicity_eq_div : multiplicity s V =
    (∑ i ∈ s, volume (V i).shade) / volume (⋃ i ∈ s, (V i).shade) := rfl

lemma volume_iUnion_shade_ne_top : volume (⋃ i ∈ s, (V i).shade) ≠ ⊤ := by
  refine measure_biUnion_ne_top (by simp) fun i _ => ?_
  exact ne_top_of_le_ne_top (V i).isCompact.measure_ne_top (measure_mono (V i).shade_subset)

/-- If the union of shades has zero measure then every shade volume in the sum is zero. -/
private lemma sum_volume_shade_eq_zero (h : volume (⋃ i ∈ s, (V i).shade) = 0) :
    ∑ i ∈ s, volume (V i).shade = 0 := -- (extracted by Fuse golfer)
  Finset.sum_eq_zero fun i hi => measure_mono_null (fun _ hx => Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩) h

lemma le_multiplicity_iff {c : ENNReal} (hne : volume (⋃ i ∈ s, (V i).shade) ≠ 0) :
    c ≤ multiplicity s V ↔
      c * volume (⋃ i ∈ s, (V i).shade) ≤ ∑ i ∈ s, volume (V i).shade :=
  ENNReal.le_div_iff_mul_le (.inl hne) (.inl <| volume_iUnion_shade_ne_top _ _)

lemma multiplicity_le_iff {c : ENNReal} : multiplicity s V ≤ c ↔
      ∑ i ∈ s, volume (V i).shade ≤ c * volume (⋃ i ∈ s, (V i).shade) := by
  by_cases h : volume (⋃ i ∈ s, (V i).shade) = 0
  · rw [multiplicity_eq_div, sum_volume_shade_eq_zero s V h, ENNReal.zero_div, h, mul_zero]
    exact iff_of_true zero_le le_rfl
  · exact ENNReal.div_le_iff h (volume_iUnion_shade_ne_top _ _)

lemma multiplicity_mul_union : multiplicity s V * volume (⋃ i ∈ s, (V i).shade) =
      ∑ i ∈ s, volume (V i).shade := by
  unfold multiplicity
  by_cases h : volume (⋃ i ∈ s, (V i).shade) = 0
  · rw [h, mul_zero]; exact (sum_volume_shade_eq_zero s V h).symm
  · exact ENNReal.div_mul_cancel h <| volume_iUnion_shade_ne_top _ _

@[simp]
lemma multiplicity_empty {V : ι → ShadedBody E} :
    multiplicity ∅ V = 0 := by simp [multiplicity]

/-- Either multiplicity ≥ 1 or every shade has zero measure. -/
lemma one_le_multiplicity (hne : ¬ ∀ i ∈ s, volume (V i).shade = 0) :
    1 ≤ multiplicity s V := by
  unfold multiplicity
  rw [ENNReal.le_div_iff_mul_le (.inr ?_) (.inl <| volume_iUnion_shade_ne_top _ _), one_mul]
  · exact measure_biUnion_finset_le s _
  · rwa [← Finset.sum_eq_zero_iff] at hne

lemma sum_shade_eq_multiplicity_mul_union :
    ∑ i ∈ s, volume (V i).shade = multiplicity s V * volume (⋃ i ∈ s, (V i).shade) :=
  (multiplicity_mul_union s V).symm

/-- **Positive fullness forces positive total shade mass.**  `fullness` is
`(∑ |Y|) / (∑ |carrier|)`, so a vanishing numerator makes it `0`. -/
lemma sum_volume_shade_ne_zero_of_fullness_pos (h : 0 < fullness s V) :
    (∑ i ∈ s, volume (V i).shade) ≠ 0 := by
  intro h0
  have hfull : (fullness s V : ENNReal) = 0 := by
    rw [fullness_def, h0, ENNReal.zero_div]
  exact (ENNReal.coe_ne_zero.mpr h.ne') hfull

/-! ### Ported from `wjq/lem5.1-section8-integration` (commit `3ebe3079b`) -/
/-- **Positive fullness forces positive multiplicity.**

Not a monotonicity statement: it goes through the total shade mass.  Positive fullness makes some
shade have positive volume, and `ShadedBody.one_le_multiplicity` then bounds the multiplicity below
by `1`.  No finiteness or nonvanishing hypothesis on the carriers is needed, because the shade sum
already carries the information. -/
lemma multiplicity_pos_of_fullness_pos (h : 0 < fullness s V) : 0 < multiplicity s V := by
  exact lt_of_lt_of_le zero_lt_one
    (one_le_multiplicity s V (fun hall => (sum_volume_shade_ne_zero_of_fullness_pos s V h)
      (Finset.sum_eq_zero hall)))

/-- The total carrier mass of a finite family of shaded bodies is finite: the carriers are
compact. -/
lemma sum_volume_carrier_ne_top : (∑ i ∈ s, volume (V i).carrier) ≠ ⊤ := by
  rw [ENNReal.sum_ne_top]
  intro i hi
  exact (V i).isCompact.measure_ne_top

/-- Shades sit inside carriers, so a nonvanishing shade mass forces a nonvanishing carrier mass. -/
lemma sum_volume_carrier_ne_zero_of_sum_shade_ne_zero
    (h : (∑ i ∈ s, volume (V i).shade) ≠ 0) :
    (∑ i ∈ s, volume (V i).carrier) ≠ 0 := by
  intro hcar
  have hle : (∑ i ∈ s, volume (V i).shade) ≤ ∑ i ∈ s, volume (V i).carrier :=
    Finset.sum_le_sum fun i hi => measure_mono (V i).shade_subset
  exact h (le_zero_iff.mp (hle.trans (by simp [hcar])))

/-- **A `c`-refinement with `c ≠ 0` retains a nonvanishing shade mass.**  This is the mass half of
`ShadedBody.IsCRefinement` read contrapositively. -/
lemma sum_volume_shade_ne_zero_of_isCRefinement {s' : Finset ι} {V' : ι → ShadedBody E}
    {c : NNReal} (h : IsCRefinement s' V' s V c) (hc : c ≠ 0)
    (hs : (∑ i ∈ s, volume (V i).shade) ≠ 0) :
    (∑ i ∈ s', volume (V' i).shade) ≠ 0 := by
  intro hsz
  have hle0 := h.2
  have hle : (c : ENNReal) * (∑ i ∈ s, volume (V i).shade) ≤ 0 := by
    rwa [hsz] at hle0
  have hprod0 : (c : ENNReal) * (∑ i ∈ s, volume (V i).shade) = 0 :=
    le_antisymm hle zero_le
  have hprod_ne : (c : ENNReal) * (∑ i ∈ s, volume (V i).shade) ≠ 0 :=
    mul_ne_zero (ENNReal.coe_ne_zero.mpr hc) hs
  exact hprod_ne hprod0

lemma multiplicity_le_card : multiplicity s V ≤ s.card := by
  rw [multiplicity_le_iff]
  calc ∑ i ∈ s, volume (V i).shade
      ≤ ∑ _ ∈ s, volume (⋃ j ∈ s, (V j).shade) :=
        Finset.sum_le_sum fun i hi => measure_mono fun x hx => Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩
    _ = s.card * volume (⋃ j ∈ s, (V j).shade) := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Multiplicity is bounded by total carrier mass divided by shading-union mass. -/
lemma multiplicity_le_sum_carrier_div :
    multiplicity s V ≤ (∑ i ∈ s, volume (V i).carrier) / volume (⋃ i ∈ s, (V i).shade) := by
  rw [multiplicity_eq_div]
  gcongr with i hi
  exact (V i).shade_subset

/-- Compare multiplicities of two families with the same shading union. -/
lemma multiplicity_le_mul_of_sum_shade_le
    {ι₂ : Type*} (s₂ : Finset ι₂) (V₂ : ι₂ → ShadedBody E) (K : ENNReal)
    (hU : (⋃ i ∈ s, (V i).shade) = ⋃ j ∈ s₂, (V₂ j).shade)
    (hnum : ∑ i ∈ s, volume (V i).shade ≤ K * ∑ j ∈ s₂, volume (V₂ j).shade) :
    multiplicity s V ≤ K * multiplicity s₂ V₂ := by
  rw [multiplicity_eq_div, multiplicity_eq_div, hU, ← mul_div_assoc]
  exact ENNReal.div_le_div_right hnum _

/-- Compare multiplicities when the second shading union is contained in the first. -/
lemma multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset
    {ι₂ : Type*} (s₂ : Finset ι₂) (V₂ : ι₂ → ShadedBody E) (K : ENNReal)
    (hU : (⋃ j ∈ s₂, (V₂ j).shade) ⊆ ⋃ i ∈ s, (V i).shade)
    (hnum : ∑ i ∈ s, volume (V i).shade ≤ K * ∑ j ∈ s₂, volume (V₂ j).shade) :
    multiplicity s V ≤ K * multiplicity s₂ V₂ := by
  rw [multiplicity_le_iff]
  calc
    ∑ i ∈ s, volume (V i).shade
        ≤ K * ∑ j ∈ s₂, volume (V₂ j).shade := hnum
    _ = K * (multiplicity s₂ V₂ * volume (⋃ j ∈ s₂, (V₂ j).shade)) := by
      rw [sum_shade_eq_multiplicity_mul_union s₂ V₂]
    _ ≤ K * (multiplicity s₂ V₂ * volume (⋃ i ∈ s, (V i).shade)) := by
      gcongr
    _ = (K * multiplicity s₂ V₂) * volume (⋃ i ∈ s, (V i).shade) := by
      rw [mul_assoc]

/-- A `c`-refinement has multiplicity at least `c` times the original multiplicity. -/
lemma multiplicity_le_of_isCRefinement {s' : Finset ι} {V' : ι → ShadedBody E} {c : NNReal}
    (hc : c ≠ 0) (h : IsCRefinement s' V' s V c) :
    multiplicity s V ≤ (c : ENNReal)⁻¹ * multiplicity s' V' := by
  have hUsub : (⋃ i ∈ s', (V' i).shade) ⊆ ⋃ i ∈ s, (V i).shade := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, h.1.1 hi, (h.1.2 i hi).2 hxi⟩
  have hvol : volume (⋃ i ∈ s', (V' i).shade) ≤ volume (⋃ i ∈ s, (V i).shade) :=
    measure_mono hUsub
  have hc0 : (c : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hc
  have hctop : (c : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  rw [← ENNReal.mul_le_iff_le_inv hc0 hctop]
  rw [multiplicity_eq_div, multiplicity_eq_div]
  have h1 : (c : ENNReal) * (∑ i ∈ s, volume (V i).shade) ≤
      ∑ i ∈ s', volume (V' i).shade := h.2
  calc
    (c : ENNReal) * ((∑ i ∈ s, volume (V i).shade) / volume (⋃ i ∈ s, (V i).shade))
        = ((c : ENNReal) * (∑ i ∈ s, volume (V i).shade)) /
            volume (⋃ i ∈ s, (V i).shade) := by rw [mul_div_assoc]
    _ ≤ (∑ i ∈ s', volume (V' i).shade) / volume (⋃ i ∈ s, (V i).shade) :=
      ENNReal.div_le_div_right h1 _
    _ ≤ (∑ i ∈ s', volume (V' i).shade) / volume (⋃ i ∈ s', (V' i).shade) :=
      ENNReal.div_le_div_left hvol _

end Multiplicity

section PointwiseMultiplicity

variable
  {E : Type*} [TopologicalSpace E] [ConvexSpace ℝ E] [MeasurableSpace E]
  {ι : Type*}
  (s : Finset ι) (V : ι → ShadedBody E) (x : E)

noncomputable instance : DecidablePred fun i ↦ x ∈ (V i).shade := Classical.decPred _

/-- The pointwise multiplicity `μ(𝒱, Y)(x) = |𝒱_Y(x)|` at a point `x`: the number of
shadings `(V i).shade` that contain `x`. See [GWZ, Definition of pointwise multiplicity]. -/
noncomputable abbrev pointwiseMultiplicity : ℕ := {i ∈ s | x ∈ (V i).shade}.card

lemma pointwiseMultiplicity_le_card : pointwiseMultiplicity s V x ≤ s.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

lemma pointwiseMultiplicity_eq_zero_iff :
    pointwiseMultiplicity s V x = 0 ↔ ∀ i ∈ s, x ∉ (V i).shade := by
  simp [pointwiseMultiplicity]

lemma pointwiseMultiplicity_pos_iff :
    0 < pointwiseMultiplicity s V x ↔ ∃ i ∈ s, x ∈ (V i).shade := by
  simp [pointwiseMultiplicity, Finset.card_pos, Finset.Nonempty, Finset.mem_filter]

/-- Pointwise multiplicity is a measurable natural-valued function. -/
theorem measurable_pointwiseMultiplicity : Measurable (pointwiseMultiplicity s V) := by
  classical
  change Measurable fun x => {i ∈ s | x ∈ (V i).shade}.card
  have hcard : (fun x => {i ∈ s | x ∈ (V i).shade}.card) =
      fun x => ∑ i ∈ s, if x ∈ (V i).shade then 1 else 0 := by
    funext x
    simp
  rw [hcard]
  exact Finset.measurable_sum s fun i _ =>
    measurable_const.piecewise (V i).measurableSet_shade measurable_const

/-- **Pointwise multiplicity is the sum of the fiberwise multiplicities** (blueprint
`lem:pointwiseMultiplicityFiberwise`).

If the partition map `p` sends `s` into `t`, then the pointwise multiplicity of `𝒱 = (V i)_{i ∈ s}`
is the sum over `j ∈ t` of the pointwise multiplicities of the fibers
`𝒱_j = (V i)_{i ∈ s, p i = j}`. Both sides count the same finite set `{i ∈ s | x ∈ Y i}`, the
right-hand side after fibering it over `p`.

The hypothesis `hp` cannot be dropped: for `t = ∅` the right-hand side is `0` while the left-hand
side need not be. -/
theorem pointwiseMultiplicity_eq_sum_fiberwise {κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (p : ι → κ)
    (V : ι → ShadedBody E) (x : E) (hp : ∀ i ∈ s, p i ∈ t) :
    pointwiseMultiplicity s V x
      = ∑ j ∈ t, pointwiseMultiplicity {i ∈ s | p i = j} V x := by
  have hMapsTo : (({i ∈ s | x ∈ (V i).shade} : Finset ι) : Set ι).MapsTo p t :=
    fun i hi => hp i (Finset.mem_filter.mp hi).1
  rw [show pointwiseMultiplicity s V x = {i ∈ s | x ∈ (V i).shade}.card from rfl,
    Finset.card_eq_sum_card_fiberwise hMapsTo]
  exact Finset.sum_congr rfl fun j _ => by
    simp [pointwiseMultiplicity, Finset.filter_filter, and_comm]

end PointwiseMultiplicity

section ConstantMultiplicity

variable
  {E : Type*} [TopologicalSpace E] [ConvexSpace ℝ E] [MeasurableSpace E]
  {ι : Type*}
  (s : Finset ι) (V : ι → ShadedBody E)

/--
`(𝒱, Y)` has constant multiplicity
if the pointwise multiplicity `μ(𝒱, Y)(x)`
is roughly the same for all `x ∈ U(𝒱, Y) = ⋃_i (V i).shade`:
precisely, there exists a
constant `C` such that `μ(𝒱, Y)(x) ≤ C · μ(𝒱, Y)(y)` for all `x, y ∈ U(𝒱, Y)`.
(Morally, `C` should depend only on the ambient dimension.)

In this case, we just provide an abstract C as an argument.

See [GWZ, Definition of constant multiplicity]. -/
def HasCConstantMultiplicity (C : NNReal) : Prop :=
  ∀ ⦃x⦄, x ∈ ⋃ i ∈ s, (V i).shade →
    ∀ ⦃y⦄, y ∈ ⋃ i ∈ s, (V i).shade →
      pointwiseMultiplicity s V x ≤
        C * pointwiseMultiplicity s V y

/--
`(𝒱, Y)` has `C`-constant multiplicity *with value `M`* if the pointwise
multiplicity `μ(𝒱, Y)(x)` at every point `x` lies in `{0} ∪ [M, C · M]`:
either `x` is covered by no shade, or its multiplicity is comparable to `M`
up to the factor `C`.

This refines `HasCConstantMultiplicity` by pinning down the common scale `M`
of the multiplicity on `U(𝒱, Y)`. -/
def HasCConstantMultiplicityWith (C M : NNReal) : Prop :=
  ∀ x, (pointwiseMultiplicity s V x : NNReal) = 0 ∨
    (M ≤ pointwiseMultiplicity s V x ∧ pointwiseMultiplicity s V x ≤ C * M)

/-- Having `C`-constant multiplicity with some value `M` implies having `C`-constant
multiplicity. This is the `⇐` direction of
`hasCConstantMultiplicity_iff_exists_hasCConstantMultiplicityWith`, packaged for reuse. -/
theorem HasCConstantMultiplicityWith.hasCConstantMultiplicity {C M : NNReal}
    (h : HasCConstantMultiplicityWith s V C M) : HasCConstantMultiplicity s V C := by
  intro x hx y hy
  have hxpos : 0 < pointwiseMultiplicity s V x := by
    rw [pointwiseMultiplicity_pos_iff s V x]
    rcases Set.mem_iUnion₂.mp hx with ⟨i, hi, hxi⟩
    exact ⟨i, hi, hxi⟩
  have hypos : 0 < pointwiseMultiplicity s V y := by
    rw [pointwiseMultiplicity_pos_iff s V y]
    rcases Set.mem_iUnion₂.mp hy with ⟨i, hi, hyi⟩
    exact ⟨i, hi, hyi⟩
  have hyM : M ≤ (pointwiseMultiplicity s V y : NNReal) := by
    rcases h y with (hzero | ⟨hMle, _⟩)
    · exfalso
      exact hypos.ne' (by exact_mod_cast hzero)
    · exact hMle
  have hxCx : (pointwiseMultiplicity s V x : NNReal) ≤ C * M := by
    rcases h x with (hzero | ⟨_, hle⟩)
    · exfalso
      exact hxpos.ne' (by exact_mod_cast hzero)
    · exact hle
  calc
    (pointwiseMultiplicity s V x : NNReal) ≤ C * M := hxCx
    _ ≤ C * (pointwiseMultiplicity s V y : NNReal) := by
      gcongr

/-- A family has `C`-constant multiplicity if and only if it has `C`-constant
multiplicity with value `M` for some `M`. -/
theorem hasCConstantMultiplicity_iff_exists_hasCConstantMultiplicityWith (C : NNReal) :
    HasCConstantMultiplicity s V C ↔ ∃ M, HasCConstantMultiplicityWith s V C M := by
  refine ⟨fun hconst => ?_, fun ⟨_, h⟩ => h.hasCConstantMultiplicity⟩
  -- Take `M` to be the least *positive* value attained by the pointwise multiplicity
  -- (`sInf ∅ = 0` handles the degenerate case where no such value exists).
  have hmem : ∀ z, 0 < pointwiseMultiplicity s V z → z ∈ ⋃ i ∈ s, (V i).shade := fun z hz => by
    obtain ⟨i, hi, hzi⟩ := (pointwiseMultiplicity_pos_iff s V z).mp hz
    exact Set.mem_iUnion₂.mpr ⟨i, hi, hzi⟩
  let S : Set ℕ := {n | 0 < n ∧ ∃ x, pointwiseMultiplicity s V x = n}
  refine ⟨(sInf S : ℕ), fun x => ?_⟩
  rcases Nat.eq_zero_or_pos (pointwiseMultiplicity s V x) with h0 | hxpos
  · exact Or.inl (by exact_mod_cast h0)
  · obtain ⟨hpos, x₀, hx₀⟩ := Nat.sInf_mem (s := S) ⟨_, hxpos, x, rfl⟩
    refine Or.inr ⟨Nat.cast_le.mpr (Nat.sInf_le ⟨hxpos, x, rfl⟩), ?_⟩
    rw [← hx₀]
    exact hconst (hmem x hxpos) (hmem x₀ (by rwa [hx₀]))

/-- `C`-constant multiplicity is monotone in the constant `C`. -/
theorem HasCConstantMultiplicity.mono {C C' : NNReal} (hCC' : C ≤ C')
    (h : HasCConstantMultiplicity s V C) : HasCConstantMultiplicity s V C' := by
  intro x hx y hy
  calc
    (pointwiseMultiplicity s V x : NNReal) ≤ C * (pointwiseMultiplicity s V y : NNReal) := h hx hy
    _ ≤ C' * (pointwiseMultiplicity s V y : NNReal) := by
      gcongr

/-- `C`-constant multiplicity with value `M` is monotone in the constant `C`. -/
theorem HasCConstantMultiplicityWith.mono {C C' M : NNReal} (hCC' : C ≤ C')
    (h : HasCConstantMultiplicityWith s V C M) : HasCConstantMultiplicityWith s V C' M := by
  intro x
  rcases h x with (hzero | ⟨hMle, hle⟩)
  · left
    exact hzero
  · right
    refine ⟨hMle, ?_⟩
    calc
      (pointwiseMultiplicity s V x : NNReal) ≤ C * M := hle
      _ ≤ C' * M := mul_le_mul_left hCC' M

/-- Constant multiplicity is preserved when every shade is transported by the same bijection. -/
theorem HasCConstantMultiplicity.congr_image {s : Finset ι} {V V' : ι → ShadedBody E}
    (g : E ≃ E) (hg : ∀ i ∈ s, (V' i).shade = g '' (V i).shade) {C : NNReal}
    (h : HasCConstantMultiplicity s V C) : HasCConstantMultiplicity s V' C := by
  have hmem : ∀ x i, i ∈ s → (g x ∈ (V' i).shade ↔ x ∈ (V i).shade) := by
    intro x i hi
    rw [hg i hi, Equiv.image_eq_preimage_symm]
    change g.symm (g x) ∈ (V i).shade ↔ x ∈ (V i).shade
    rw [g.symm_apply_apply]
  have hpm : ∀ x, pointwiseMultiplicity s V' (g x) = pointwiseMultiplicity s V x := by
    intro x
    unfold pointwiseMultiplicity
    apply congrArg Finset.card
    apply Finset.ext
    intro i
    by_cases hi : i ∈ s
    · simp [hi, hmem x i hi]
    · simp [hi]
  intro x hx y hy
  have hx0 : g.symm x ∈ ⋃ i ∈ s, (V i).shade := by
    rcases Set.mem_iUnion₂.mp hx with ⟨i, hi, hxi⟩
    rw [hg i hi] at hxi
    rcases hxi with ⟨z, hz, hgz⟩
    refine Set.mem_iUnion₂.mpr ⟨i, hi, ?_⟩
    simpa [← hgz] using hz
  have hy0 : g.symm y ∈ ⋃ i ∈ s, (V i).shade := by
    rcases Set.mem_iUnion₂.mp hy with ⟨i, hi, hyi⟩
    rw [hg i hi] at hyi
    rcases hyi with ⟨z, hz, hgz⟩
    refine Set.mem_iUnion₂.mpr ⟨i, hi, ?_⟩
    simpa [← hgz] using hz
  rw [← g.apply_symm_apply x, ← g.apply_symm_apply y, hpm, hpm]
  exact h hx0 hy0


end ConstantMultiplicity

section BasicMultiplicity

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}
  (s : Finset ι) (V : ι → ShadedBody E)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurableSet_iUnion_shade : MeasurableSet (⋃ i ∈ s, (V i).shade) :=
  Finset.measurableSet_biUnion s (fun i _ => (V i).measurableSet_shade)

/-- The integral identity underlying GWZ Lemma 5.6 (blueprint `lemmabasicmult`):
the total shade volume `∑ᵢ |Y(Vᵢ)|` equals the integral over the ambient space of the
pointwise multiplicity `μ(𝒱, Y)(x)`. Proved by writing each volume as the integral of an
indicator, swapping sum and integral, and recognising the sum of indicators as the count
of shades containing `x`. -/
lemma sum_volume_shade_eq_lintegral_pointwiseMultiplicity :
    ∑ i ∈ s, volume (V i).shade
      = ∫⁻ x, (pointwiseMultiplicity s V x : ENNReal) := by
  calc ∑ i ∈ s, volume (V i).shade
      = ∑ i ∈ s, ∫⁻ x, (V i).shade.indicator (1 : E → ENNReal) x :=
        Finset.sum_congr rfl fun i _ => (lintegral_indicator_one (V i).measurableSet_shade).symm
    _ = ∫⁻ x, ∑ i ∈ s, (V i).shade.indicator (1 : E → ENNReal) x :=
        (lintegral_finsetSum s fun i _ =>
          measurable_const.indicator (V i).measurableSet_shade).symm
    _ = ∫⁻ x, (pointwiseMultiplicity s V x : ENNReal) :=
        lintegral_congr fun x => by
          simp only [Set.indicator_apply, Pi.one_apply, Finset.sum_boole, pointwiseMultiplicity]

/-- GWZ Lemma 5.6, lower bound (blueprint `lemmabasicmult`).
If the pointwise multiplicity `μ(𝒱, Y)(x)` is at least `c` for every `x ∈ U(𝒱, Y)`, and the
union `U(𝒱, Y)` has positive measure, then the global multiplicity `μ(𝒱, Y)` is at least `c`.

The hypothesis `volume (⋃ i ∈ s, (V i).shade) ≠ 0` is the nondegeneracy condition needed for
the lower bound: with `ENNReal` division semantics, if the union has zero measure then
`multiplicity s V = 0`, so no positive lower bound could hold. -/
lemma le_multiplicity_of_le_pointwiseMultiplicity {c : ENNReal}
    (hne : volume (⋃ i ∈ s, (V i).shade) ≠ 0)
    (h : ∀ x ∈ ⋃ i ∈ s, (V i).shade, c ≤ (pointwiseMultiplicity s V x : ENNReal)) :
    c ≤ multiplicity s V := by
  rw [le_multiplicity_iff s V hne]
  calc c * volume (⋃ i ∈ s, (V i).shade)
      = ∫⁻ x, (⋃ i ∈ s, (V i).shade).indicator (fun _ => c) x :=
        (lintegral_indicator_const (measurableSet_iUnion_shade s V) c).symm
    _ ≤ ∫⁻ x, (pointwiseMultiplicity s V x : ENNReal) := lintegral_mono (Set.indicator_le h)
    _ = ∑ i ∈ s, volume (V i).shade :=
        (sum_volume_shade_eq_lintegral_pointwiseMultiplicity s V).symm

/-- An almost-everywhere pointwise lower bound gives the same lower bound for the global
multiplicity.  This is the null-set-stable form of
`le_multiplicity_of_le_pointwiseMultiplicity`, used after discarding fibers whose shaded unions
have zero volume. -/
lemma le_multiplicity_of_ae_le_pointwiseMultiplicity {c : ENNReal}
    (hne : volume (⋃ i ∈ s, (V i).shade) ≠ 0)
    (h : ∀ᵐ x ∂volume, x ∈ ⋃ i ∈ s, (V i).shade →
      c ≤ (pointwiseMultiplicity s V x : ENNReal)) :
    c ≤ multiplicity s V := by
  rw [le_multiplicity_iff s V hne]
  calc
    c * volume (⋃ i ∈ s, (V i).shade) =
        ∫⁻ x, (⋃ i ∈ s, (V i).shade).indicator (fun _ ↦ c) x :=
      (lintegral_indicator_const (measurableSet_iUnion_shade s V) c).symm
    _ ≤ ∫⁻ x, (pointwiseMultiplicity s V x : ENNReal) := by
      apply lintegral_mono_ae
      filter_upwards [h] with x hx
      by_cases hxU : x ∈ ⋃ i ∈ s, (V i).shade
      · simpa [Set.indicator_of_mem hxU] using hx hxU
      · simp [Set.indicator, hxU]
    _ = ∑ i ∈ s, volume (V i).shade :=
      (sum_volume_shade_eq_lintegral_pointwiseMultiplicity s V).symm

/-- GWZ Lemma 5.6, upper bound (blueprint `lemmabasicmult`).
If the pointwise multiplicity `μ(𝒱, Y)(x)` is at most `c` for every `x ∈ U(𝒱, Y)`, then the
global multiplicity `μ(𝒱, Y)` is at most `c`.

No nondegeneracy hypothesis is required here: if the union has zero measure then
`multiplicity s V = 0 ≤ c` automatically. -/
lemma multiplicity_le_of_pointwiseMultiplicity_le {c : ENNReal}
    (h : ∀ x ∈ ⋃ i ∈ s, (V i).shade, (pointwiseMultiplicity s V x : ENNReal) ≤ c) :
    multiplicity s V ≤ c := by
  rw [multiplicity_le_iff s V]
  calc ∑ i ∈ s, volume (V i).shade
      = ∫⁻ x, (pointwiseMultiplicity s V x : ENNReal) :=
        sum_volume_shade_eq_lintegral_pointwiseMultiplicity s V
    _ ≤ ∫⁻ x, (⋃ i ∈ s, (V i).shade).indicator (fun _ => c) x :=
        lintegral_mono <| Set.le_indicator h fun x hx => by
          rw [nonpos_iff_eq_zero, Nat.cast_eq_zero, pointwiseMultiplicity_eq_zero_iff]
          exact fun i hi hxi => hx (Set.mem_iUnion₂.mpr ⟨i, hi, hxi⟩)
    _ = c * volume (⋃ i ∈ s, (V i).shade) :=
        lintegral_indicator_const (measurableSet_iUnion_shade s V) c

/-- **Constant multiplicity converts the pointwise multiplicity into the global one**
(blueprint `def:constantMultiplicity`, `lemmabasicmult`).

If `(𝒱, Y)` has `C`-constant multiplicity and `U(𝒱, Y)` has positive measure, then the
pointwise multiplicity at *every* point of the ambient space is at most `C · μ(𝒱, Y)`.

The point is that `C`-constancy makes `μ(𝒱, Y)(x)/C` a *uniform* lower bound for the
pointwise multiplicity on `U(𝒱, Y)`, so
`Kakeya.ShadedBody.le_multiplicity_of_le_pointwiseMultiplicity` turns it into a lower bound for
`μ(𝒱, Y)`. No membership hypothesis on `x` is needed: off `U(𝒱, Y)` the pointwise multiplicity
vanishes.

This is the direction the splitting argument of blueprint `lem:ml2nonslabPointwiseMult`
consumes, where the outer factor of the product bound has to be a multiplicity rather than a
pointwise count. -/
lemma pointwiseMultiplicity_le_mul_multiplicity {C : NNReal} (hC : 0 < C)
    (hne : volume (⋃ i ∈ s, (V i).shade) ≠ 0)
    (hconst : HasCConstantMultiplicity s V C) (x : E) :
    (pointwiseMultiplicity s V x : ENNReal) ≤ (C : ENNReal) * multiplicity s V := by
  by_cases hx : x ∈ ⋃ i ∈ s, (V i).shade
  · have hC0 : (C : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt hC)
    have hCt : (C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hc :
        (pointwiseMultiplicity s V x : ENNReal) / (C : ENNReal) ≤ multiplicity s V := by
      refine le_multiplicity_of_le_pointwiseMultiplicity s V hne ?_
      intro y hy
      rw [ENNReal.div_le_iff_le_mul
        (a := (pointwiseMultiplicity s V x : ENNReal)) (b := (C : ENNReal))
        (c := (pointwiseMultiplicity s V y : ENNReal))
        (Or.inl hC0) (Or.inl hCt)]
      have hm : (pointwiseMultiplicity s V x : ENNReal) ≤
          (C : ENNReal) * (pointwiseMultiplicity s V y : ENNReal) := by
        exact_mod_cast hconst hx hy
      simpa [mul_comm] using hm
    calc
      (pointwiseMultiplicity s V x : ENNReal)
          ≤ multiplicity s V * (C : ENNReal) :=
            (ENNReal.div_le_iff_le_mul
              (a := (pointwiseMultiplicity s V x : ENNReal)) (b := (C : ENNReal))
              (c := multiplicity s V) (Or.inl hC0) (Or.inl hCt)).mp hc
      _ = (C : ENNReal) * multiplicity s V := by rw [mul_comm]
  · have hpu : (pointwiseMultiplicity s V x : ENNReal) = 0 := by
      have hz : pointwiseMultiplicity s V x = 0 :=
        (pointwiseMultiplicity_eq_zero_iff s V x).mpr (by
          intro i hi hxi
          exact hx (Set.mem_iUnion₂.mpr ⟨i, hi, hxi⟩))
      exact_mod_cast hz
    rw [hpu]
    exact zero_le

/-- **Mass from a pointwise lower bound on a measurable set, with a factor**: if
`c ≤ M · μ(s, V)(x)` at every point of a measurable set `A`, then
`c · |A| ≤ M · ∑_{i ∈ s} |Y(V i)|`.

The factor `M` is carried because the comparisons this is applied to, the lower halves of Items
3 and 4 of GWZ Proposition 5.1, are dyadic and so come with the factor `2`. No relation between
`A` and the shaded union is needed: off that union the pointwise multiplicity vanishes, so the
hypothesis then forces `c = 0`. -/
theorem mul_volume_le_mul_sum_volume_shade_of_le_mul_pointwiseMultiplicity
    {c M : ENNReal} {A : Set E} (hA : MeasurableSet A)
    (h : ∀ x ∈ A, c ≤ M * (pointwiseMultiplicity s V x : ENNReal)) :
    c * volume A ≤ M * ∑ i ∈ s, volume (V i).shade := by
  classical
  calc
    c * volume A = ∫⁻ x, A.indicator (fun _ => c) x := by
      rw [lintegral_indicator_const hA c]
    _ ≤ ∫⁻ x, M * (pointwiseMultiplicity s V x : ENNReal) := by
      apply lintegral_mono
      intro x
      by_cases hxA : x ∈ A
      · rw [Set.indicator_apply, if_pos hxA]
        exact h x hxA
      · rw [Set.indicator_apply, if_neg hxA]
        apply zero_le
    _ = M * ∫⁻ x, (pointwiseMultiplicity s V x : ENNReal) := by
      have hMb : MeasurableEmbedding (Nat.cast : ℕ → ENNReal) := MeasurableEmbedding.natCast
      have hmeas : Measurable (fun x : E => (pointwiseMultiplicity s V x : ENNReal)) :=
        hMb.measurable.comp (ShadedBody.measurable_pointwiseMultiplicity s V)
      rw [lintegral_const_mul M hmeas]
    _ = M * ∑ i ∈ s, volume (V i).shade := by
      rw [← ShadedBody.sum_volume_shade_eq_lintegral_pointwiseMultiplicity]

/-- **Mass bound from a pointwise lower bound on a subset** (blueprint
`lem:massBoundFromPointwiseLowerBoundOnSubset`).

This is the half of GWZ Lemma 5.6 (`le_multiplicity_of_le_pointwiseMultiplicity`) that survives
when the pointwise lower bound is known only on a measurable subset `A` of the ambient space: one
still gets a bound on the total shaded mass `∑ i ∈ s, |Y (V i)|`, but no longer on the global
multiplicity.

Neither `A ⊆ U(𝒱, Y)` nor `volume A ≠ 0` is needed: points of `A` outside `U(𝒱, Y)` contribute
`0 ≤ pointwiseMultiplicity s V x` to the comparison, and `volume A = 0` makes the left-hand side
vanish. -/
lemma mul_volume_le_sum_volume_shade_of_le_pointwiseMultiplicity {c : ENNReal} {A : Set E}
    (hA : MeasurableSet A)
    (h : ∀ x ∈ A, c ≤ (pointwiseMultiplicity s V x : ENNReal)) :
    c * volume A ≤ ∑ i ∈ s, volume (V i).shade := by
  simpa using mul_volume_le_mul_sum_volume_shade_of_le_mul_pointwiseMultiplicity s V
    (M := 1) hA (by simpa using h)

/-- **Averaged form of a pointwise lower bound**: a bound `c ≤ M · μ(s, V)(x)` holding only on a
measurable set `A` that carries all but a factor `K` of the shaded union passes to the averaged
multiplicity, at the composite loss `K · M`.

The nonvanishing hypothesis is what allows the common factor `|⋃ shade|` to be cancelled. -/
theorem le_mul_multiplicity_of_le_mul_pointwiseMultiplicity
    {c M K : ENNReal} {A : Set E} (hA : MeasurableSet A)
    (hne : volume (⋃ i ∈ s, (V i).shade) ≠ 0)
    (hcov : volume (⋃ i ∈ s, (V i).shade) ≤ K * volume A)
    (h : ∀ x ∈ A, c ≤ M * (pointwiseMultiplicity s V x : ENNReal)) :
    c ≤ K * M * multiplicity s V := by
  classical
  let U : Set E := ⋃ i ∈ s, (V i).shade
  have hu0 : volume U ≠ 0 := by simpa [U] using hne
  have htop : volume U ≠ ⊤ := by
    simpa [U] using ShadedBody.volume_iUnion_shade_ne_top s V
  have hcov' : volume U ≤ K * volume A := by simpa [U] using hcov
  have hstep : c * volume A ≤ M * (∑ i ∈ s, volume (V i).shade) :=
    mul_volume_le_mul_sum_volume_shade_of_le_mul_pointwiseMultiplicity s V hA h
  have hchan : c * volume U ≤ (K * M * multiplicity s V) * volume U := by
    calc
      c * volume U ≤ c * (K * volume A) := by
          exact mul_le_mul_right hcov' c
      _ = K * (c * volume A) := mul_left_comm c K (volume A)
      _ ≤ K * (M * (∑ i ∈ s, volume (V i).shade)) := by
          exact mul_le_mul_right hstep K
      _ = K * M * (multiplicity s V * volume U) := by
          rw [sum_shade_eq_multiplicity_mul_union]
          ring
      _ = (K * M * multiplicity s V) * volume U := by ring
  exact (ENNReal.mul_le_mul_iff_right hu0 htop).mp (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hchan)

end BasicMultiplicity

section MultiplicityTranslate

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-- Multiplicity is invariant under translation of all bodies by the same vector. -/
lemma multiplicity_translate_const (s : Finset ι) (V : ι → ShadedBody E) (v : E) :
    multiplicity s (fun i => (V i).translate v) = multiplicity s V :=
  div_eq_div_of_eq_eq (Finset.sum_congr rfl fun i _ => measure_image_add volume v (V i).shade)
    (by
      simp only [ShadedBody.translate_shade, ← Set.preimage_iUnion₂, measure_preimage_add])

end MultiplicityTranslate

section RefinementMultiplicity

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}
  (s' : Finset ι) (V' : ι → ShadedBody E) (s : Finset ι) (V : ι → ShadedBody E)

/--
[GWZ, Lemma 5.5] A mild refinement cannot substantially decrease multiplicity:
if `(𝒱', Y')` is a `c`-refinement of `(𝒱, Y)`, then `c * μ(𝒱, Y) ≤ μ(𝒱', Y')`.

This is stated in the multiplication form `c * μ(𝒱, Y) ≤ μ(𝒱', Y')` rather than the
blueprint's inverse form `μ(𝒱, Y) ≤ c⁻¹ * μ(𝒱', Y')` so that it holds without a
`0 < c` side condition (at `c = 0` the inverse form would be vacuous). -/
theorem IsCRefinement.mul_multiplicity_le {c : NNReal}
    (h : IsCRefinement s' V' s V c) :
    (c : ENNReal) * multiplicity s V ≤ multiplicity s' V' := by
  obtain ⟨⟨hss', hshade⟩, hmass⟩ := h
  rw [multiplicity, multiplicity, ← mul_div_assoc]
  exact ENNReal.div_le_div hmass (measure_mono (Set.iUnion₂_subset fun i hi =>
    (hshade i hi).2.trans (Set.subset_iUnion₂ (s := fun i _ => (V i).shade) i (hss' hi))))

end RefinementMultiplicity

section FullnessAndFactorFamily

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*}

/-- **A `c`-refinement is at least `c` times as full**: refining multiplies the shading mass by at
least `c` and can only shrink the total carrier volume, so the quotient defining
`ShadedBody.fullness` drops by at most `c`.

This is the density form of `ShadedBody.IsCRefinement`: a Córdoba-type estimate consumes a
*fullness*, not a mass. -/
theorem IsCRefinement.coe_mul_fullness_le {s s' : Finset ι} {V V' : ι → ShadedBody E} {c : NNReal}
    (h : IsCRefinement s' V' s V c) :
    (c : ENNReal) * (fullness s V : ENNReal) ≤ (fullness s' V' : ENNReal) := by
  rcases h with ⟨href, hc⟩
  rcases href with ⟨hss, hcar⟩
  rw [coe_fullness s V, coe_fullness s' V']
  have hTle : (∑ i ∈ s', volume (V' i).carrier) ≤ ∑ i ∈ s, volume (V i).carrier := by
    calc
      (∑ i ∈ s', volume (V' i).carrier) = ∑ i ∈ s', volume (V i).carrier := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact congrArg (fun W : ConvexSpaceBody E => volume W.carrier) (hcar i hi).1
      _ ≤ ∑ i ∈ s, volume (V i).carrier := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hss
          (fun i _ => by simp)
  calc
    (c : ENNReal) * ((∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier))
        = ((c : ENNReal) * ∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
    _ ≤ (∑ i ∈ s', volume (V' i).shade) / (∑ i ∈ s', volume (V' i).carrier) := by
        exact ENNReal.div_le_div hc hTle

/-- **A uniform blockwise density bound is a fullness bound**: if `a |W j| ≤ b |Y(W j)|` for every
block of a finite family whose total carrier volume is positive and finite, then the fullness of
the family is at least `a / b`. -/
theorem le_fullness_of_forall_mul_volume_carrier_le {t : Finset κ} {W : κ → ShadedBody E}
    {a b : ENNReal} (hb : b ≠ 0) (hb' : b ≠ ⊤)
    (ht0 : ∑ j ∈ t, volume (W j).carrier ≠ 0) (ht : ∑ j ∈ t, volume (W j).carrier ≠ ⊤)
    (h : ∀ j ∈ t, a * volume (W j).carrier ≤ b * volume (W j).shade) :
    a / b ≤ (fullness t W : ENNReal) := by
  rw [fullness_def]
  have hsum : (∑ j ∈ t, a * volume (W j).carrier) ≤
      (∑ j ∈ t, b * volume (W j).shade) :=
    Finset.sum_le_sum (fun j hj => h j hj)
  -- factor `a` (resp. `b`) out of the sums
  have hfac : a * (∑ j ∈ t, volume (W j).carrier) ≤
      b * (∑ j ∈ t, volume (W j).shade) := by
    simpa [Finset.mul_sum] using hsum
  apply (ENNReal.le_div_iff_mul_le (a := a / b)
    (b := ∑ j ∈ t, volume (W j).carrier) (c := ∑ j ∈ t, volume (W j).shade)
    (Or.inl ht0) (Or.inl ht)).mpr
  apply (ENNReal.mul_le_mul_iff_left (a := a / b * (∑ j ∈ t, volume (W j).carrier))
      (b := ∑ j ∈ t, volume (W j).shade) hb hb').mp
  rw [mul_assoc, mul_comm (∑ j ∈ t, volume (W j).carrier) b, ← mul_assoc,
    ENNReal.div_mul_cancel hb hb', mul_comm (∑ j ∈ t, volume (W j).shade) b]
  exact hfac

/-- **A fullness-to-fullness lower bound becomes a `lam` lower bound at the cost of `Cd`.**

`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate` (`Kakeya/Factoring/RhoTubes.lean`)
concludes `C⁻¹ · λ(𝕋, Y) ≤ λ(𝕋_ρ', Y_{𝕋_ρ}')`, comparing one *fullness* with another. Consumers
such as `Kakeya.ml1Boot.exists_factorOneScale` want instead a lower bound by the density
*parameter* `lam` of the inner shading. This lemma is that conversion, and it prices it: the
constant acquires a factor `Cd`, the two-sided comparison constant of the density hypothesis, and
the nondegeneracy side condition `hs0` appears. Neither is removable by any choice of `C` — see
the note "GWZ Lemma 5.11 for undilated `ρ`-tubes is no longer stated here" further down this
file, and the docstring of
`ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam`, which is the consumer.

Only the lower density bound is used; the matching upper bound plays no role. -/
theorem le_fullness_of_le_fullness_of_forall_density
    {s : Finset ι} {V : ι → ShadedBody E} {t : Finset κ} {W : κ → ShadedBody E}
    {lam Cd C : NNReal} (hCd : Cd ≠ 0)
    (hs0 : ∑ i ∈ s, volume (V i).carrier ≠ 0)
    (hlam_lb : ∀ i ∈ s, (Cd : ENNReal)⁻¹ * ((lam : ENNReal) * volume (V i).carrier)
      ≤ volume (V i).shade)
    (hfull : C⁻¹ * fullness s V ≤ fullness t W) :
    (Cd * C)⁻¹ * lam ≤ fullness t W := by
  have hcd0 : (Cd : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hCd
  have hcdt : (Cd : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsum_ne_top : ∑ i ∈ s, volume (V i).carrier ≠ ⊤ := by
    intro h
    rcases ENNReal.sum_eq_top.1 h with ⟨i, _, hf⟩
    exact (V i).isCompact.measure_ne_top hf
  have hlam' : ∀ i ∈ s, (lam : ENNReal) * volume (V i).carrier ≤
      (Cd : ENNReal) * volume (V i).shade := by
    intro i hi
    calc
      (lam : ENNReal) * volume (V i).carrier
          = (Cd : ENNReal) * ((Cd : ENNReal)⁻¹ * ((lam : ENNReal) * volume (V i).carrier)) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel hcd0 hcdt, one_mul]
      _ ≤ (Cd : ENNReal) * volume (V i).shade := by
        gcongr
        exact hlam_lb i hi
  have hstep : (lam : ENNReal) / (Cd : ENNReal) ≤ (fullness s V : ENNReal) :=
    le_fullness_of_forall_mul_volume_carrier_le (t := s) (W := V)
      (a := (lam : ENNReal)) (b := (Cd : ENNReal)) hcd0 hcdt hs0 hsum_ne_top hlam'
  have hlam_nn : lam / Cd ≤ fullness s V := by
    apply ENNReal.coe_le_coe.1
    rw [ENNReal.coe_div hCd]
    exact hstep
  calc
    (Cd * C)⁻¹ * lam = C⁻¹ * (lam / Cd) := by
      rw [mul_inv, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm Cd⁻¹]
    _ ≤ C⁻¹ * fullness s V := by
      gcongr
    _ ≤ fullness t W := hfull

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **The inner shaded union of a shaded factor family lies in its outer shaded union**: the union
form of the `shade_subset_parent` field. -/
theorem ShadedFactorFamily.iUnionShade_inner_subset_outer (S : ShadedFactorFamily E ι κ) :
    (⋃ i ∈ S.innerSet, (S.innerBody i).shade) ⊆ ⋃ j ∈ S.outerSet, (S.outerBody j).shade := by
  intro x hx
  rcases Set.mem_iUnion₂.mp hx with ⟨i, hi, hxi⟩
  exact Set.mem_iUnion₂.mpr ⟨S.parent i, S.parent_mem i hi, S.shade_subset_parent i hi hxi⟩

omit [FiniteDimensional ℝ E] [BorelSpace E] in
open Classical in
/-- **A pointwise multiplicity factors through the fibers**: if the outer count at `x` is at most
`a` and every fiber whose shaded union contains `x` has fiber count at most `b`, then the inner
count at `x` is at most `a · b`.

The shading containment of a shaded factor family is what bounds the number of contributing
fibers by the outer count. -/
theorem ShadedFactorFamily.pointwiseMultiplicity_le_mul (S : ShadedFactorFamily E ι κ)
    {x : E} {a b : ENNReal}
    (houter : (pointwiseMultiplicity S.outerSet S.outerBody x : ENNReal) ≤ a)
    (hinner : ∀ j ∈ S.outerSet, x ∈ (⋃ i ∈ S.fiber j, (S.innerBody i).shade) →
      (pointwiseMultiplicity (S.fiber j) S.innerBody x : ENNReal) ≤ b) :
    (pointwiseMultiplicity S.innerSet S.innerBody x : ENNReal) ≤ a * b := by
  classical
  let T : Finset κ := {j ∈ S.outerSet | x ∈ ⋃ i ∈ S.fiber j, (S.innerBody i).shade}
  let mf : κ → ℕ := fun j => pointwiseMultiplicity (S.fiber j) S.innerBody x
  have hfiber : ∀ j ∈ S.outerSet,
      pointwiseMultiplicity {i ∈ S.innerSet | S.parent i = j} S.innerBody x = mf j := by
    intro j _
    dsimp [mf]
    simp [ShadedFactorFamily.fiber]
  have hsum : pointwiseMultiplicity S.innerSet S.innerBody x = ∑ j ∈ S.outerSet, mf j := by
    rw [pointwiseMultiplicity_eq_sum_fiberwise S.innerSet S.outerSet S.parent S.innerBody x
      S.parent_mem]
    exact Finset.sum_congr rfl hfiber
  have hTS : T ⊆ S.outerSet := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hzero : ∀ j ∈ S.outerSet, j ∉ T → mf j = 0 := by
    intro j hj hnotT
    have hmem : ∀ i ∈ S.fiber j, x ∉ (S.innerBody i).shade := by
      intro i hi hxi
      exact hnotT (Finset.mem_filter.mpr ⟨hj, Set.mem_iUnion₂.mpr ⟨i, hi, hxi⟩⟩)
    simpa [mf] using
      (pointwiseMultiplicity_eq_zero_iff (S.fiber j) S.innerBody x).2 hmem
  have hzeroENN : ∀ j ∈ S.outerSet, j ∉ T → (mf j : ENNReal) = 0 := by
    intro j hj hnotT
    simp [hzero j hj hnotT]
  have hsumT : ∑ j ∈ T, (mf j : ENNReal) = ∑ j ∈ S.outerSet, (mf j : ENNReal) :=
    Finset.sum_subset hTS hzeroENN
  have hT_le_b : ∀ j ∈ T, (mf j : ENNReal) ≤ b := by
    intro j hj
    exact hinner j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
  have hsum_le : ∑ j ∈ T, (mf j : ENNReal) ≤ T.card • b := by
    exact Finset.sum_le_card_nsmul T (fun j => (mf j : ENNReal)) b hT_le_b
  have hT_sub : T ⊆ S.outerSet.filter (fun j => x ∈ (S.outerBody j).shade) := by
    intro j hj
    rcases (Finset.mem_filter.mp hj) with ⟨hjo, hxIn⟩
    rcases Set.mem_iUnion₂.mp hxIn with ⟨i, hiF, hxi⟩
    have hiI : i ∈ S.innerSet := (Finset.mem_filter.mp hiF).1
    have hpar : S.parent i = j := (Finset.mem_filter.mp hiF).2
    exact Finset.mem_filter.mpr ⟨hjo, by simpa [hpar] using S.shade_subset_parent i hiI hxi⟩
  have hcardT : T.card ≤ pointwiseMultiplicity S.outerSet S.outerBody x := by
    simpa [pointwiseMultiplicity] using Finset.card_le_card hT_sub
  have hcT : (T.card : ENNReal) ≤ (pointwiseMultiplicity S.outerSet S.outerBody x : ENNReal) := by
    exact_mod_cast hcardT
  have hcTa : (T.card : ENNReal) ≤ a := le_trans hcT houter
  have hTbmul : T.card • b ≤ a * b := by
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcTa (by positivity)
  have hsumENN : (pointwiseMultiplicity S.innerSet S.innerBody x : ENNReal)
      = ∑ j ∈ S.outerSet, (mf j : ENNReal) := by
    rw [hsum]
    exact (Nat.cast_sum S.outerSet mf)
  calc
    (pointwiseMultiplicity S.innerSet S.innerBody x : ENNReal)
        = ∑ j ∈ S.outerSet, (mf j : ENNReal) := hsumENN
    _ = ∑ j ∈ T, (mf j : ENNReal) := hsumT.symm
    _ ≤ T.card • b := hsum_le
    _ ≤ a * b := hTbmul

end FullnessAndFactorFamily

/-! ### GWZ Lemma 5.8

GWZ Lemma 5.8 asserted that a pointwise multiplicity lower bound holding on `U(𝒱, Y)` passes to
the global multiplicity of the induced-shading family. That statement is not used by the corrected
factoring construction. Aggregate fullness is obtained from the summed Córdoba estimate, while the
outer multiplicity needed in the product estimate is obtained from local solid balls in the thick
shading. Exact constant multiplicity is asserted only for the separate counting shading.
-/

/-!
## GWZ Lemma 5.11 for undilated `ρ`-tubes

The undilated estimates are in `Kakeya/Factoring/RhoTubesUndilated.lean` and
follow from `ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate` at `c = 1`.

* `ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated` has a
  fullness-to-fullness conclusion with loss
  `shadingMultiplicityEstimateForRhoTubesDilate.C (Module.finrank ℝ E) F.innerSet.card δ 1`.
* `ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam` includes
  the further factor `Cd` and assumes
  `∑ i ∈ F.innerSet, volume (F.innerBody i).carrier ≠ 0`.

Both features are necessary. At constant `1`, an outer bound
`C⁻¹ · lam ≤ fullness G.outerSet G.outerBody`, together with
`ShadedBody.fullness_le_one`, would force `lam ≤ 1`; `Cd = 4`, `lam = 2` and
half-shaded inner tubes refute this bound. For any nonzero constant, empty
inner and outer families force zero output fullness, which cannot dominate
a positive `C⁻¹ · lam`. The nonzero-mass hypothesis excludes that case.

The estimates belong downstream because `Kakeya/Factoring/RhoTubes.lean`
already imports this module through `Kakeya.Factoring.Pipeline` and
`Kakeya.Factoring.Step2`. The two helper lemmas
`ShadedBody.le_fullness_of_forall_mul_volume_carrier_le` and
`ShadedBody.le_fullness_of_le_fullness_of_forall_density` are defined here.
-/

end ShadedBody

/-!
# Indexed-family multiplicity helpers
-/

@[expose] public section

open MeasureTheory ShadedBody


namespace Kakeya

variable
  (E : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `multiplicity` only depends on the bodies indexed by `s`. -/
lemma multiplicity_eq_of_eqOn
    {ι : Type*} (s : Finset ι) {V W : ι → ShadedBody E}
    (h : ∀ i ∈ s, V i = W i) :
    multiplicity s V = multiplicity s W := by
  unfold ShadedBody.multiplicity
  rw [Finset.sum_congr rfl fun i hi => by rw [h i hi],
    Set.iUnion₂_congr fun i hi => by rw [h i hi]]

/-- If `β ≥ 1`, the trivial multiplicity bound `μ ≤ #s` implies the corresponding
max-density bound, since `Δ_max ≤ #s` and `1 - β ≤ 0`. -/
lemma multiplicity_le_trivial_of_one_le [Nontrivial E] {β : ℝ} (hβ : 1 ≤ β)
    {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) (W : ι → ConvexSpaceBody E) :
    multiplicity s V ≤ maxDensity s W ^ (1 - β) * (s.card : ENNReal) ^ β := by
  rcases eq_or_ne s ∅ with rfl | hs
  · simp [ShadedBody.multiplicity_empty]
  · set Δ := maxDensity s W
    set N := (s.card : ENNReal)
    have hN_card : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
    have hN_ne_zero : N ≠ 0 := by simpa [N] using hN_card.ne'
    have hN_ne_top : N ≠ ⊤ := by simp [N]
    have hN_split : N = N ^ (1 - β) * N ^ β := by
      rw [← ENNReal.rpow_add (1 - β) β hN_ne_zero hN_ne_top]
      norm_num
    have hΔ_le_N : Δ ≤ N := maxDensity_le_card s W
    have hNpow_le : N ^ (1 - β) ≤ Δ ^ (1 - β) := by
      have hΔp : Δ ^ (β - 1) ≤ N ^ (β - 1) :=
        ENNReal.rpow_le_rpow hΔ_le_N (by linarith)
      rw [show 1 - β = -(β - 1) by ring, ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr hΔp
    calc
      multiplicity s V ≤ N := ShadedBody.multiplicity_le_card s V
      _ = N ^ (1 - β) * N ^ β := hN_split
      _ ≤ Δ ^ (1 - β) * N ^ β := by gcongr

/-- Multiplicity-pigeonhole transfer: if `s' ⊆ s` and the shade-mass on
`s` is bounded by `M` times the shade-mass on `s'`, then
`multiplicity s V ≤ M · multiplicity s' V`. -/
lemma multiplicity_pigeon_transfer
    {ι : Type*} {s s' : Finset ι} (hs' : s' ⊆ s)
    (V : ι → ShadedBody E) {M : ENNReal}
    (h_pig : (∑ i ∈ s, volume (V i).shade) ≤
      M * (∑ i ∈ s', volume (V i).shade)) :
    multiplicity s V ≤ M * multiplicity s' V := by
  rw [ShadedBody.multiplicity_le_iff]
  refine h_pig.trans ?_
  rw [ShadedBody.sum_shade_eq_multiplicity_mul_union, mul_assoc]
  refine mul_le_mul_right (mul_le_mul_right (measure_mono fun x hx => ?_) _) _
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨i, hs' hi, hxi⟩

end Kakeya

namespace Kakeya

open scoped Classical in
/-- The fibre `𝒫_Y(x)` of a shaded family over a point `x`: the indices `i ∈ s` whose shading
contains `x`. Its cardinality is `ShadedBody.pointwiseMultiplicity s Y x`. -/
noncomputable def shadeFibre {ι E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [ConvexSpace ℝ E] (s : Finset ι) (Y : ι → ShadedBody E) (x : E) : Finset ι :=
  {i ∈ s | x ∈ (Y i).shade}

lemma mem_shadeFibre {ι E : Type*} [TopologicalSpace E] [MeasurableSpace E] [ConvexSpace ℝ E]
    (s : Finset ι) (Y : ι → ShadedBody E) (x : E) (i : ι) :
    i ∈ shadeFibre s Y x ↔ i ∈ s ∧ x ∈ (Y i).shade := by
  classical
  simp only [shadeFibre, Finset.mem_filter]

end Kakeya
