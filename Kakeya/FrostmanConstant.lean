/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ConvexBody
public import Kakeya.Density
public import Kakeya.Frostman
public import Kakeya.Shading
public import Kakeya.Thickness.Volume
public import Kakeya.Tube.Basic

/-!
# The scalar Frostman constant of a finite family

`Kakeya.frostmanConstant s W K` is the *scalar* form of `ConvexSpaceBody.IsFrostmanIn`: the least
`C` for which `Δ_max(𝕎) ≤ C · (∑_{i ∈ s} |W i|) / |K|`. Equivalently, in the division-free form
`Δ_max(𝕎) · |K| ≤ C · ∑_{i ∈ s} |W i|`.

The denominator is the *unfiltered* total mass `∑_{i ∈ s} |W i|`, not
`Kakeya.densityIn s W K = (∑_{i ∈ s, W i ≤ K} |W i|) / |K|`. This is deliberate: the families that
Section 6 tests against a slab `S` are only known to lie in a controlled *dilation* of `S`
(`Plank.SlabFibreGeometry.subset_slab`), so the filtered sum can be empty while the family still
carries almost all of the mass near `S`. With the unfiltered normalisation the quantity remains the
honest "density of the family relative to `|K|`" in exactly that situation.

The definition and its elementary division-free interfaces are dimension-independent. Geometric
normalisation windows belong to the corresponding geometric modules.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal

namespace Kakeya

noncomputable section

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [MeasureSpace E]
  {ι : Type*}

/-- The **Frostman constant** of the finite family `W` indexed by `s`, relative to the reference
body `K`: the least `C` with `Δ_max(𝕎) · |K| ≤ C · ∑_{i ∈ s} |W i|`.

See the module docstring for why the normalising mass is the unfiltered `∑_{i ∈ s} |W i|` rather
than `Kakeya.densityIn s W K`. -/
def frostmanConstant (s : Finset ι) (W : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E) :
    ENNReal :=
  maxDensity s W * volume K.carrier / ∑ i ∈ s, volume (W i).carrier

/-- **Division-free reading of `Kakeya.frostmanConstant s W K ≤ C`.** -/
theorem maxDensity_mul_volume_le_of_frostmanConstant_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ι : Type*}
    {s : Finset ι} {W : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E} {C : ENNReal}
    (hmass : ∑ i ∈ s, volume (W i).carrier ≠ 0)
    (h : frostmanConstant s W K ≤ C) :
    maxDensity s W * volume K.carrier ≤ C * ∑ i ∈ s, volume (W i).carrier := by
  have hsum_top : (∑ i ∈ s, volume (W i).carrier) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i _ => (W i).isCompact.measure_ne_top
  unfold frostmanConstant at h
  rwa [ENNReal.div_le_iff hmass hsum_top] at h

/-- A division-free sufficient condition for the Frostman predicate. -/
theorem isFrostmanIn_of_maxDensity_mul_volume_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ι : Type*}
    {s : Finset ι} {W : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E} {C : ENNReal}
    (hWK : ∀ i ∈ s, W i ≤ K) (hK0 : volume K.carrier ≠ 0)
    (h : maxDensity s W * volume K.carrier ≤ C * ∑ i ∈ s, volume (W i).carrier) :
    ConvexSpaceBody.IsFrostmanIn s W K C := by
  have hKtop : volume K.carrier ≠ ⊤ := K.isCompact.measure_ne_top
  apply ConvexSpaceBody.IsFrostmanIn.of_maxDensity_le
  rw [densityIn_of_all_le hWK]
  have hrw : C * ((∑ i ∈ s, volume (W i).carrier) / volume K.carrier)
      = (C * ∑ i ∈ s, volume (W i).carrier) / volume K.carrier := by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
  rw [hrw, ENNReal.le_div_iff_mul_le (Or.inl hK0) (Or.inl hKtop)]
  exact h

end

end Kakeya

end

/-!
## Canonical constants for tube families

For a family of `δ`-tubes in the unit ball, the canonical Frostman constant is at least one when
the family is nonempty, and is bounded by an explicit dimensional polynomial envelope.
-/

@[expose] public section

open MeasureTheory Metric Kakeya

noncomputable section

namespace ConvexSpaceBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- **The Frostman constant is at least `1`** whenever the family has positive density in the
reference body. This is the `sInf`-level companion of `ConvexSpaceBody.IsFrostmanIn.one_le`; the
positive-density hypothesis is necessary, since a family with no member inside `K` has Frostman
constant `0`. -/
theorem one_le_frostmanConstant {s : Finset ι} {W : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} (hd : 0 < densityIn s W K) :
    1 ≤ frostmanConstant s W K :=
  isFrostmanIn_frostmanConstant.one_le hd

end ConvexSpaceBody

namespace Tube

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {ι : Type*}

/-- The universal Frostman envelope for a family of `δ`-tubes in the unit ball: the volume of the
ambient ball divided by the least possible volume of a single tube. Depends only on the dimension
and on `δ`. -/
def frostmanEnvelope (n : ℕ) (δ : NNReal) : ENNReal :=
  volume (closedBall (0 : E) 1) * ((le_volume.c n : ENNReal) * (δ : ENNReal) ^ (n - 1))⁻¹

omit [Nontrivial E] in
theorem frostmanEnvelope_ne_top {δ : NNReal} (hδ : 0 < δ) :
    frostmanEnvelope (E := E) (Module.finrank ℝ E) δ ≠ ⊤ := by
  unfold frostmanEnvelope
  apply ENNReal.mul_ne_top
  · exact ne_top_of_le_ne_top
      (ENNReal.pow_ne_top (by simp))
      (volume_closedBall_le_two_pow_finrank (E := E))
  · rw [ENNReal.inv_ne_top]
    exact ne_of_gt (ENNReal.mul_pos
      (ENNReal.coe_ne_zero.mpr (ne_of_gt (le_volume.c_pos (Module.finrank ℝ E))))
      (pow_ne_zero (Module.finrank ℝ E - 1) (ENNReal.coe_ne_zero.mpr (ne_of_gt hδ))))

/-- **Every family of `δ`-tubes in `B₁` is Frostman with the universal envelope constant.**
No essential distinctness, no bound on `s.card`, no nonemptiness, and not even `0 < δ` is required:
when `δ = 0` the envelope is `⊤`. -/
theorem isFrostmanIn_frostmanEnvelope {δ : NNReal}
    (s : Finset ι) (T : ι → Tube δ E)
    (hT : ∀ i ∈ s, (T i).carrier ⊆ closedBall (0 : E) 1) :
    ConvexSpaceBody.IsFrostmanIn s (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall
      (frostmanEnvelope (E := E) (Module.finrank ℝ E) δ) := by
  classical
  let W : ι → ConvexSpaceBody E := fun i => (T i).toConvexSpaceBody
  let B₁ : ConvexSpaceBody E := ConvexSpaceBody.closedUnitBall
  let n : ℕ := Module.finrank ℝ E
  let c : ENNReal := (le_volume.c n : ENNReal)
  let d : ENNReal := (δ : ENNReal) ^ (n - 1)
  let v : ENNReal := volume B₁.carrier
  intro K' hK'
  change densityIn s W K' ≤ frostmanEnvelope (E := E) n δ * densityIn s W B₁
  set A : ENNReal := ∑ i ∈ s with W i ≤ K', volume (W i).carrier with hAdef
  set B : ENNReal := ∑ i ∈ s, volume (W i).carrier with hBdef
  by_cases hA0 : A = 0
  · have hdK' : densityIn s W K' = 0 := by
      change A / volume K'.carrier = 0
      rw [hA0, ENNReal.zero_div]
    rw [hdK']
    exact zero_le
  · have hne : (s.filter fun i => W i ≤ K').Nonempty := by
      by_contra h
      apply hA0
      rw [hAdef]
      simp [Finset.not_nonempty_iff_eq_empty.mp h]
    obtain ⟨i, hi⟩ := hne
    have hi_mem : i ∈ s := (Finset.mem_filter.mp hi).1
    have hiWK' : W i ≤ K' := (Finset.mem_filter.mp hi).2
    have hWB : ∀ j ∈ s, W j ≤ B₁ := by
      intro j hj
      change (T j).carrier ⊆ Metric.closedBall (0 : E) 1
      exact hT j hj
    have hvolK' : c * d ≤ volume K'.carrier := by
      calc
        c * d ≤ volume (W i).carrier := by
          simpa [W, n, c, d] using (Tube.le_volume (T i))
        _ ≤ volume K'.carrier := measure_mono hiWK'
    have hAB : A ≤ B := by
      rw [hAdef, hBdef]
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset (s := s) fun i => W i ≤ K')
    have hv0 : v ≠ 0 := by
      dsimp [v, B₁]
      exact (Metric.measure_closedBall_pos volume (0 : E) one_pos).ne'
    have hvtop : v ≠ ⊤ := by
      dsimp [v, B₁]
      exact MeasureTheory.measure_closedBall_lt_top.ne
    have hmain : A / volume K'.carrier ≤ B / (c * d) := by
      calc
        A / volume K'.carrier ≤ B / volume K'.carrier := ENNReal.div_le_div_right hAB _
        _ ≤ B / (c * d) := ENNReal.div_le_div_left hvolK' B
    have hrewrite : B / (c * d) = frostmanEnvelope (E := E) n δ * (B / v) := by
      rw [show frostmanEnvelope (E := E) n δ = v * (c * d)⁻¹ by rfl]
      simp only [div_eq_mul_inv]
      calc
        B * (c * d)⁻¹ = B * (c * d)⁻¹ * (v * v⁻¹) := by
          rw [ENNReal.mul_inv_cancel hv0 hvtop, mul_one]
        _ = (v * (c * d)⁻¹) * (B * v⁻¹) := by ring
    rw [densityIn_of_all_le hWB]
    change A / volume K'.carrier ≤ frostmanEnvelope (E := E) n δ * (B / v)
    exact hmain.trans_eq hrewrite

/-- **The canonical Frostman constant of a `δ`-tube family in `B₁` is polynomially bounded.**
This is the quantitative form of finiteness that lets `ConvexSpaceBody.frostmanConstant` be used as
the constant in GWZ Lemma 3.9. -/
theorem frostmanConstant_le_frostmanEnvelope {δ : NNReal}
    (s : Finset ι) (T : ι → Tube δ E)
    (hT : ∀ i ∈ s, (T i).carrier ⊆ closedBall (0 : E) 1) :
    ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall
      ≤ frostmanEnvelope (E := E) (Module.finrank ℝ E) δ :=
  ConvexSpaceBody.frostmanConstant_le_of_isFrostmanIn
    (isFrostmanIn_frostmanEnvelope s T hT)

/-- The canonical Frostman constant of a `δ`-tube family in `B₁` is finite. -/
theorem frostmanConstant_ne_top {δ : NNReal} (hδ : 0 < δ)
    (s : Finset ι) (T : ι → Tube δ E)
    (hT : ∀ i ∈ s, (T i).carrier ⊆ closedBall (0 : E) 1) :
    ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall ≠ ⊤ :=
  ne_top_of_le_ne_top (frostmanEnvelope_ne_top hδ)
    (frostmanConstant_le_frostmanEnvelope s T hT)

end Tube

namespace Kakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A nonempty family of `δ`-tubes inside `B₁` has positive density in `B₁`, hence canonical
Frostman constant at least `1`. -/
theorem one_le_frostmanConstant_of_tubes [Nontrivial E] {δ : NNReal} (hδ : 0 < δ)
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E) (hs : s.Nonempty)
    (hB : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) :
    1 ≤ ConvexSpaceBody.frostmanConstant s (fun i ↦ (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall := by
  let W : ι → ConvexSpaceBody E := fun i => (T i).toConvexSpaceBody
  let B1 : ConvexSpaceBody E := ConvexSpaceBody.closedUnitBall
  have hDpos : 0 < Kakeya.densityIn s W B1 := by
    rw [Kakeya.densityIn_pos_iff]
    obtain ⟨i, hi⟩ := hs
    refine ⟨i, hi, ?_, ?_⟩
    · have hP0 : (δ : ENNReal) ^ (Module.finrank ℝ E - 1) ≠ 0 :=
        pow_ne_zero (Module.finrank ℝ E - 1)
          (ENNReal.coe_ne_zero.mpr (ne_of_gt hδ))
      have hcp0 : (0 : ENNReal) <
          ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
                * (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
        lt_of_le_of_ne zero_le (mul_ne_zero
          (ENNReal.coe_ne_zero.mpr (ne_of_gt (Tube.le_volume.c_pos (Module.finrank ℝ E))))
          hP0).symm
      exact lt_of_lt_of_le hcp0 (by
        simpa [W] using (Tube.le_volume (T i).toTube))
    · exact SetLike.coe_subset_coe.mp (by
        calc
          (W i : Set E) = (T i).carrier := rfl
          _ ⊆ Metric.closedBall (0 : E) 1 := hB i hi
          _ = (B1 : Set E) := rfl)
  have hFC : (1 : ENNReal) ≤ ConvexSpaceBody.frostmanConstant s W B1 :=
    ConvexSpaceBody.one_le_frostmanConstant hDpos
  simpa [W, B1] using hFC

end Kakeya

end

end
