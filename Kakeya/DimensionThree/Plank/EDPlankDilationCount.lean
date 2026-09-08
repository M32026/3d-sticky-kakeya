/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ConvexBody.Counting
public import Kakeya.DimensionThree.Plank
public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.DimensionThree.Volume

/-!
# An anisotropic (two-width) packing count for essentially distinct planks

`Kakeya/Tube/EDPacking/PositionCount.lean` counts pairwise essentially distinct `δ`-tubes at a
*single* radius. GWZ 6.6(B) needs the same count for `a × b × 1` planks, i.e. at **two** transverse
widths, and needs it with a bound that does **not** degrade with the aspect ratio `b / a`:

`Kakeya.card_le_edPlankDilationCount` — for planks of one fixed pair of half-widths `a ≤ b ≤ 1`
with `0 < a`, pairwise essentially distinct and all contained in the `Λ`-dilation of one of them,
the cardinality is at most `Kakeya.edPlankDilationCount Λ`, which depends on `Λ` **alone**: not on
`a`, not on `b`, not on `δ`, and not on the family.

## Why the two widths cost nothing

The count is a *ratio* statement, and both widths cancel out of the ratio. A plank has volume
`8 a b` (`Prism3D.volume_carrier` at `c = 1`), its `Λ`-dilation has volume `Λ³ · 8 a b`
(`PrismNDim.volume_dilation`), so every member of the family occupies the fixed fraction
`α = Λ⁻³` of the container **whatever `a` and `b` are**. That is exactly the hypothesis of
`Kakeya.card_le_of_pairwise_essDistinct_in_prism`, whose constant depends only on the ambient
dimension and on `α`. No direction cap, no transverse geometry and no angular argument is needed;
the anisotropy is absorbed by the affine equivalence that
`Kakeya.card_le_of_pairwise_essDistinct_in_prism` applies internally, which carries the container
prism to a cube and is *not* required to be an isometry.

## `0 < a` is not a convenience hypothesis

At `a = 0` the statement is **false**, and `Kakeya.exists_degenerate_ED_plank_family_card_gt` is
the counterexample: a degenerate plank has volume `0`, so `IsEssentiallyDistinct` holds for *every*
pair of degenerate planks — including a plank and itself — and an arbitrarily long constant family
satisfies both hypotheses. This is the same degeneracy that
`Kakeya.card_le_of_pairwise_essDistinct_in_prism` guards against with `0 < volume R.carrier`.

## The count is not the trivial bound `1`

An upper bound whose hypotheses were satisfiable only at `card ≤ 1` would be true and useless, and
a vacuity check that only checks inhabitedness would not see it.
`Kakeya.exists_two_ED_planks_in_dilation` rules that out by exhibiting a two-member family at
`a = b = 1/2`, `Λ = 11`.

## Size of the constant, stated honestly

`Kakeya.cardEssDistinctConvexInPrismConstant 3 α` is `2 ^ ⌈(2 + 6/ε(α))³⌉` with `ε(α)` a fixed
positive multiple of `α`, so it is of size `2 ^ Θ(α⁻³)`. For the intended use `Λ = 11` this is
irrelevant — `α`
is absolute, hence so is the count, and that is the whole content of the lemma. It *is* relevant
if one tries to reuse `Kakeya.card_le_of_pairwise_ED_plank_subset_prism` with a container whose
volume ratio degenerates: the general-container form below is stated with `α` explicit precisely so
that the caller can see what it is paying. In particular this route does **not** produce a bound
*linear* in `1/α`, so it does not by itself give the `φ`-graded clause of
`Plank.IsThickeningNonconcentrated` at `φ` above the endpoint `a / b`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace Kakeya

variable {ι : Type*}

/-- **Counting pairwise essentially distinct `a × b × 1` planks inside a prism container.**

The volume ratio `α` is an explicit parameter: the hypothesis `hαR` says that the plank volume
`8 a b` is at least the fraction `α` of the container volume. Nothing here is anisotropic — the
two half-widths enter only through the product `a b`, which is the plank's volume up to the
absolute factor `8`.

`0 < a` is needed: a degenerate plank has volume `0` and is essentially distinct from itself
(`Kakeya.exists_degenerate_ED_plank_family_card_gt`). -/
theorem card_le_of_pairwise_ED_plank_subset_prism
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (ha : 0 < a)
    (R : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)))
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hαR : ENNReal.ofReal α * volume (R.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ 8 * (a : ENNReal) * b)
    (s : Finset ι) (P : ι → Plank a b hab hb1)
    (hsub : ∀ i ∈ s, ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (R.carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hED : (s : Set ι).Pairwise fun i j => IsEssentiallyDistinct
      ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    s.card ≤ cardEssDistinctConvexInPrismConstant 3 α := by
  rcases Finset.eq_empty_or_nonempty s with rfl | ⟨i₁, hi₁⟩
  · simp
  · have hvolP : ∀ i : ι,
        volume ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3))) = 8 * (a : ENNReal) * b := by
      intro i
      rw [Prism3D.volume_carrier]
      simp
    have hRpos : 0 < volume (R.carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
      lt_of_lt_of_le (Prism3D.volume_pos_of_pos (P i₁) ha) (measure_mono (hsub i₁ hi₁))
    refine card_le_of_pairwise_essDistinct_in_prism (m := 3) (by norm_num) hα hα1 R hRpos s
      (fun i => (P i).toPrismNDim.toConvexSpaceBody) hsub ?_ hED
    intro j _
    exact le_of_le_of_eq hαR (hvolP j).symm

/-- **The absolute constant of the anisotropic plank packing count.**

It depends on the dilation factor `Λ` alone. Unfolded, it is
`Kakeya.cardEssDistinctConvexInPrismConstant 3 (Λ⁻³)`, of size `2 ^ Θ(Λ⁹)`; it is deliberately
crude and nothing downstream should read anything but its finiteness and its argument list. -/
def edPlankDilationCount (Λ : ℝ≥0) : ℕ :=
  cardEssDistinctConvexInPrismConstant 3 (((Λ : ℝ)) ^ 3)⁻¹

/-- **The anisotropic (two-width) essential-distinctness packing count for planks, with the
constant explicit.**

Pairwise essentially distinct planks of one fixed pair of half-widths `a ≤ b ≤ 1`, `0 < a`, all
contained in the `Λ`-dilation of one of them, number at most `Kakeya.edPlankDilationCount Λ`.

The bound is **absolute** in the only sense that matters here: it involves neither `a` nor `b` nor
any scale `δ`, so it does not degrade as the aspect ratio `b / a` blows up. -/
theorem card_le_edPlankDilationCount {Λ : ℝ≥0} (hΛ : 1 ≤ Λ)
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (ha : 0 < a)
    (s : Finset ι) (P : ι → Plank a b hab hb1) (i₀ : ι)
    (hED : (s : Set ι).Pairwise fun i j => IsEssentiallyDistinct
      ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hsub : ∀ i ∈ s, ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (((P i₀).toPrismNDim.dilation Λ).carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    s.card ≤ edPlankDilationCount Λ := by
  have hΛ0 : (0 : ℝ≥0) < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hΛR : (0 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ0
  have hΛR1 : (1 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ
  have hα0 : 0 < (((Λ : ℝ)) ^ 3)⁻¹ := by positivity
  have hα1 : (((Λ : ℝ)) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hΛR1)
  have hkey : ENNReal.ofReal (((Λ : ℝ)) ^ 3)⁻¹ * ((Λ : ℝ≥0) : ENNReal) ^ 3 = 1 := by
    have h1 : ((Λ : ℝ≥0) : ENNReal) ^ 3 = ENNReal.ofReal ((Λ : ℝ) ^ 3) := by
      rw [ENNReal.ofReal_pow hΛR.le, ENNReal.ofReal_coe_nnreal]
    rw [h1, ← ENNReal.ofReal_mul hα0.le, inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one]
  refine card_le_of_pairwise_ED_plank_subset_prism ha ((P i₀).toPrismNDim.dilation Λ) hα0 hα1
    ?_ s P hsub hED
  rw [PrismNDim.volume_dilation, ← mul_assoc, hkey, one_mul, Prism3D.volume_carrier]
  simp

/-- **The dispatched shape of the count**, with the constant existentially
quantified and the degeneracy hypothesis `0 < a` made explicit.

`C` is absolute: it is produced before `a`, `b`, `ι`, the family and the index are seen. -/
theorem exists_ED_plank_dilation_card_bound (Λ : ℝ≥0) (hΛ : 1 ≤ Λ) :
    ∃ C : ℕ, ∀ {ι : Type*} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (_ha : 0 < a)
      (s : Finset ι) (P : ι → Plank a b hab hb1) (i₀ : ι),
      (s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct
        ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
      (∀ i ∈ s, ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ (((P i₀).toPrismNDim.dilation Λ).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
      s.card ≤ C :=
  ⟨edPlankDilationCount Λ, fun ha s P i₀ hED hsub =>
    card_le_edPlankDilationCount hΛ ha s P i₀ hED hsub⟩

open scoped Classical in
/-- **The endpoint clause of `Plank.IsThickeningNonconcentrated`, at `φ = a / b`.**

`Plank.thickened (a / b)` of an `a × b × 1` plank *is* that plank again: its half-widths are
`![(a / b) * b, b, 1] = ![a, b, 1]` as soon as `b ≠ 0`, and it keeps the centre and the frame. So
the `Λ`-dilated `φ = a / b` thickening is the `Λ`-dilation of the plank itself, and
`Kakeya.card_le_edPlankDilationCount` bounds the counted set by the absolute constant. Equivalently:
this is the `φ = a / b` instance of `Plank.IsThickeningNonconcentrated s V Λ M` at
`M = Kakeya.edPlankDilationCount Λ * (b / a)`, since `M * (a / b) = Kakeya.edPlankDilationCount Λ`.

It is **only** the endpoint instance, and that is the honest boundary of this file. The clause at
`φ > a / b` counts planks inside a `Λφb × Λb × Λ` container, where the volume ratio is
`α = a / (Λ³ φ b)`; the bound it needs is `M φ`, i.e. *linear* in `1 / α`, whereas
`Kakeya.cardEssDistinctConvexInPrismConstant 3 α` is `2 ^ Θ(α⁻³)`. That gap is where
the aspect ratio `b / a` re-enters, and closing it needs a genuine transverse packing count, not a
volume-ratio count. -/
theorem card_filter_subset_dilation_thickened_self {Λ : ℝ≥0} (hΛ : 1 ≤ Λ)
    {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} (ha : 0 < a) (hφ1 : a / b ≤ 1)
    (s : Finset ι) (V : ι → Plank a b hab hb1) (i : ι)
    (hED : (s : Set ι).Pairwise fun x y => IsEssentiallyDistinct
      ((V x).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ((V y).carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    (s.filter fun j => ((V j).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ (((Plank.thickened (V i) (a / b) hφ1).toPrismNDim.dilation Λ).carrier :
            Set (EuclideanSpace ℝ (Fin 3)))).card
      ≤ edPlankDilationCount Λ := by
  classical
  have hb0 : b ≠ 0 := (lt_of_lt_of_le ha hab).ne'
  have hthick : ∀ k, ((Plank.thickened (V i) (a / b) hφ1).thicknesses k) = (V i).thicknesses k := by
    intro k
    rw [(Plank.thickened (V i) (a / b) hφ1).thicknesses_eq, (V i).thicknesses_eq]
    fin_cases k <;> simp [div_mul_cancel₀ _ hb0]
  have hcar : (((Plank.thickened (V i) (a / b) hφ1).toPrismNDim.dilation Λ).carrier :
      Set (EuclideanSpace ℝ (Fin 3)))
      = (((V i).toPrismNDim.dilation Λ).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    ext x
    rw [PrismNDim.mem_carrier_iff, PrismNDim.mem_carrier_iff]
    simp only [PrismNDim.dilation_thicknesses, PrismNDim.dilation_center,
      PrismNDim.dilation_basis, Plank.thickened_center, Plank.thickened_basis, hthick]
  refine card_le_edPlankDilationCount hΛ ha _ V i
    (Set.Pairwise.mono (Finset.coe_subset.mpr (Finset.filter_subset _ s)) hED) ?_
  intro j hj
  have hj' := (Finset.mem_filter.mp hj).2
  rwa [hcar] at hj'

/-! ### The count is not the trivial bound `1`

A `card = 2` witness, so that "absolute `C`" is not absolute because the hypotheses secretly force
`C = 1`: two axis-aligned `1/2 × 1/2 × 1` planks offset by exactly one half-width along their thin
axis. Their intersection is contained in a box of exactly half the plank volume, so they are
essentially distinct (with equality, which `IsEssentiallyDistinct` allows), and both lie in the
`11`-dilation of the first. -/
/-- A `1/2 × 1/2 × 1` plank with axis-aligned frame, centred on the first axis at `t`. -/
def edPlankWitness (t : ℝ) : Plank (1/2) (1/2) le_rfl (by norm_num) where
  toPrismNDim := PrismNDim.mk'
    (EuclideanSpace.single 0 t : EuclideanSpace ℝ (Fin 3))
    (EuclideanSpace.basisFun (Fin 3) ℝ) ![1/2, 1/2, 1]
  thicknesses_eq := rfl

theorem mem_edPlankWitness_iff (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ (edPlankWitness t).carrier ↔
      |x 0 - t| ≤ 1/2 ∧ |x 1| ≤ 1/2 ∧ |x 2| ≤ 1 := by
  rw [(edPlankWitness t).mem_carrier_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have := h 0; simpa [edPlankWitness, PrismNDim.mk', PiLp.single_apply] using this
    · have := h 1; simpa [edPlankWitness, PrismNDim.mk', PiLp.single_apply] using this
    · have := h 2; simpa [edPlankWitness, PrismNDim.mk', PiLp.single_apply] using this
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · simpa [edPlankWitness, PrismNDim.mk', PiLp.single_apply] using h0
    · simpa [edPlankWitness, PrismNDim.mk', PiLp.single_apply] using h1
    · simpa [edPlankWitness, PrismNDim.mk', PiLp.single_apply] using h2

/-- Bounding box for `Kakeya.edPlankWitness 0 ∩ Kakeya.edPlankWitness (1/2)`: half the volume of
either, which is what makes the two witnesses essentially distinct. -/
def edPlankWitnessBox : Prism3D (1/4) (1/2) 1
    (by rw [← NNReal.coe_le_coe]; push_cast; norm_num) (by norm_num) where
  toPrismNDim := PrismNDim.mk'
    (EuclideanSpace.single 0 (1/4 : ℝ) : EuclideanSpace ℝ (Fin 3))
    (EuclideanSpace.basisFun (Fin 3) ℝ) ![1/4, 1/2, 1]
  thicknesses_eq := rfl

theorem mem_edPlankWitnessBox_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ edPlankWitnessBox.carrier ↔ |x 0 - 1/4| ≤ 1/4 ∧ |x 1| ≤ 1/2 ∧ |x 2| ≤ 1 := by
  rw [edPlankWitnessBox.mem_carrier_iff]
  constructor
  · intro h
    exact ⟨by simpa [edPlankWitnessBox, PrismNDim.mk', PiLp.single_apply] using h 0,
      by simpa [edPlankWitnessBox, PrismNDim.mk', PiLp.single_apply] using h 1,
      by simpa [edPlankWitnessBox, PrismNDim.mk', PiLp.single_apply] using h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · simpa [edPlankWitnessBox, PrismNDim.mk', PiLp.single_apply] using h0
    · simpa [edPlankWitnessBox, PrismNDim.mk', PiLp.single_apply] using h1
    · simpa [edPlankWitnessBox, PrismNDim.mk', PiLp.single_apply] using h2

theorem volume_edPlankWitnessBox :
    volume (edPlankWitnessBox.carrier : Set (EuclideanSpace ℝ (Fin 3))) = 1 := by
  rw [Prism3D.volume_carrier]
  rw [show (8 : ENNReal) = ((8 : ℝ≥0) : ENNReal) by simp, ← ENNReal.coe_mul, ← ENNReal.coe_mul,
    ← ENNReal.coe_mul, show ((8 : ℝ≥0) * (1/4) * (1/2) * 1) = 1 by
      rw [← NNReal.coe_inj]; push_cast; norm_num]
  simp

theorem volume_edPlankWitness (t : ℝ) :
    volume ((edPlankWitness t).carrier : Set (EuclideanSpace ℝ (Fin 3))) = 2 := by
  rw [Prism3D.volume_carrier]
  rw [show (8 : ENNReal) = ((8 : ℝ≥0) : ENNReal) by simp, ← ENNReal.coe_mul, ← ENNReal.coe_mul,
    ← ENNReal.coe_mul, show ((8 : ℝ≥0) * (1/2) * (1/2) * 1) = 2 by
      rw [← NNReal.coe_inj]; push_cast; norm_num]
  simp

theorem mem_edPlankWitness_dilation_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ (((edPlankWitness 0).toPrismNDim.dilation 11).carrier :
        Set (EuclideanSpace ℝ (Fin 3))) ↔
      |x 0| ≤ 11/2 ∧ |x 1| ≤ 11/2 ∧ |x 2| ≤ 11 := by
  rw [PrismNDim.mem_carrier_iff]
  constructor
  · intro h
    exact ⟨by simpa [edPlankWitness, PrismNDim.mk', PiLp.single_apply, div_eq_mul_inv] using h 0,
      by simpa [edPlankWitness, PrismNDim.mk', PiLp.single_apply, div_eq_mul_inv] using h 1,
      by simpa [edPlankWitness, PrismNDim.mk', PiLp.single_apply, div_eq_mul_inv] using h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · simpa [edPlankWitness, PrismNDim.mk', PiLp.single_apply, div_eq_mul_inv] using h0
    · simpa [edPlankWitness, PrismNDim.mk', PiLp.single_apply, div_eq_mul_inv] using h1
    · simpa [edPlankWitness, PrismNDim.mk', PiLp.single_apply, div_eq_mul_inv] using h2

theorem edPlankWitness_subset_dilation (t : ℝ) (ht : |t| ≤ 1) :
    ((edPlankWitness t).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (((edPlankWitness 0).toPrismNDim.dilation 11).carrier :
          Set (EuclideanSpace ℝ (Fin 3))) := by
  intro x hx
  rw [mem_edPlankWitness_iff] at hx
  rw [mem_edPlankWitness_dilation_iff]
  obtain ⟨h0, h1, h2⟩ := hx
  rw [abs_le] at h0 h1 h2 ht
  refine ⟨?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;>
    linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, ht.1, ht.2]

theorem inter_edPlankWitness_subset_box :
    ((edPlankWitness 0).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ (edPlankWitness (1/2)).carrier
      ⊆ (edPlankWitnessBox.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  rintro x ⟨hx0, hx1⟩
  rw [mem_edPlankWitness_iff] at hx0 hx1
  rw [mem_edPlankWitnessBox_iff]
  obtain ⟨a0, a1, a2⟩ := hx0
  obtain ⟨b0, -, -⟩ := hx1
  rw [abs_le] at a0 b0
  refine ⟨?_, a1, a2⟩
  rw [abs_le]
  constructor <;> linarith [a0.1, a0.2, b0.1, b0.2]

theorem edPlankWitness_isEssentiallyDistinct :
    IsEssentiallyDistinct ((edPlankWitness 0).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ((edPlankWitness (1/2)).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
  rw [IsEssentiallyDistinct, volume_edPlankWitness, volume_edPlankWitness, max_self]
  calc volume (((edPlankWitness 0).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ∩ (edPlankWitness (1/2)).carrier)
      ≤ volume (edPlankWitnessBox.carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
        measure_mono inter_edPlankWitness_subset_box
    _ = 1 := volume_edPlankWitnessBox
    _ = (1 / 2 : ENNReal) * 2 := by
        rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num)]

/-- **Non-vacuity of the count.** The hypotheses of
`Kakeya.exists_ED_plank_dilation_card_bound` are satisfiable with two distinct members at
`a = b = 1/2`, `Λ = 11`, so the absolute bound is not the trivial bound `1`. -/
theorem exists_two_ED_planks_in_dilation :
    ∃ (s : Finset (Fin 2)) (P : Fin 2 → Plank (1/2) (1/2) le_rfl (by norm_num)) (i₀ : Fin 2),
      (s : Set (Fin 2)).Pairwise (fun i j => IsEssentiallyDistinct
        ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∧
      (∀ i ∈ s, ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ (((P i₀).toPrismNDim.dilation 11).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∧
      s.card = 2 := by
  refine ⟨Finset.univ, ![edPlankWitness 0, edPlankWitness (1/2)], 0, ?_, ?_, by simp⟩
  · intro i _ j _ hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | exact edPlankWitness_isEssentiallyDistinct
        | exact isEssentiallyDistinct_symm edPlankWitness_isEssentiallyDistinct
  · intro i _
    fin_cases i
    · exact edPlankWitness_subset_dilation 0 (by norm_num)
    · exact edPlankWitness_subset_dilation (1/2) (by norm_num)

/-! ### `0 < a` cannot be dropped -/

/-- A degenerate `0 × 1 × 1` plank: the unit square in the plane `x₀ = 0`. -/
def degeneratePlank : Plank 0 1 (by norm_num : (0:ℝ≥0) ≤ 1) le_rfl where
  toPrismNDim := PrismNDim.mk' (0 : EuclideanSpace ℝ (Fin 3))
    (EuclideanSpace.basisFun (Fin 3) ℝ) ![0, 1, 1]
  thicknesses_eq := rfl

theorem volume_degeneratePlank :
    volume (degeneratePlank.carrier : Set (EuclideanSpace ℝ (Fin 3))) = 0 := by
  rw [Prism3D.volume_carrier]
  simp

/-- **Refutation of the `a = 0` case.**

For every `Λ ≥ 1` and every candidate bound `C` there is a family of `C + 1` planks — of
half-widths `0 ≤ 1 ≤ 1` — that is pairwise essentially distinct and entirely contained in the
`Λ`-dilation of one of its members. So no bound of the shape of
`Kakeya.exists_ED_plank_dilation_card_bound` can hold without `0 < a`.

The mechanism is not a packing failure but a definitional one: `IsEssentiallyDistinct U V` asks
`volume (U ∩ V) ≤ ½ max (volume U) (volume V)`, which every pair of null sets satisfies — a
degenerate plank is essentially distinct even from itself. The family below is constant. -/
theorem exists_degenerate_ED_plank_family_card_gt (Λ : ℝ≥0) (hΛ : 1 ≤ Λ) (C : ℕ) :
    ∃ (ι : Type) (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1)
      (s : Finset ι) (P : ι → Plank a b hab hb1) (i₀ : ι),
      ((s : Set ι).Pairwise (fun i j => IsEssentiallyDistinct
        ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3))))) ∧
      (∀ i ∈ s, ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ (((P i₀).toPrismNDim.dilation Λ).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∧
      C < s.card := by
  refine ⟨Fin (C + 1), 0, 1, (by norm_num : (0 : ℝ≥0) ≤ 1), le_rfl, Finset.univ,
    fun _ => degeneratePlank, 0, ?_, ?_, ?_⟩
  · intro i _ j _ _
    simp [IsEssentiallyDistinct, volume_degeneratePlank]
  · intro i _
    exact PrismNDim.self_subset_dilation degeneratePlank.toPrismNDim hΛ
  · simp

end Kakeya

end

end
