/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Projective direction caps and their cone sectors

GWZ Appendix A equation (106) bounds `P[R(T) ⊆ 100 T₀]` for a random *rigid motion* `R` by
`|T_δ|²`. One factor of `|T_δ| ≈ δ^(n-1)` is the translation estimate already available from
`Kakeya.HasUniformTranslation`; the other is the probability that the rotation part aligns the axis
of `T` with that of `T₀` to within `δ`. This file provides the geometric workhorse for that second
factor.

## What is proved here

For a unit vector `d₀` and `0 < r ≤ 1`, the **cone sector**

`capSector d₀ r = {x ∈ B₁ | x ≠ 0 ∧ projective distance from x/‖x‖ to d₀ is ≤ r}`

has Lebesgue measure `≲ r^(n-1)` (`Kakeya.volume_capSector_le`). Consequently the *uniform measure
on the sphere* — Mathlib's `MeasureTheory.Measure.toSphere`, whose defining identity
`toSphere_apply'` expresses a spherical set's measure as `n ·` the volume of its cone sector inside
`B₁` — assigns a projective cap of radius `r` measure `≲ r^(n-1)`
(`Kakeya.toSphere_projectiveCap_le`).

Directions are compared *projectively*, via `min ‖u - d₀‖ ‖u + d₀‖`, because a tube axis is
unoriented: `Tube.direction` and its negation describe the same tube. This matches the convention
used throughout `Kakeya/Tube/EDPacking/` (e.g. the `_h_dir_class` hypothesis of
`Kakeya.position_count_le_of_bad_directionClass'`) and in
`Kakeya.card_le_of_projective_separated_in_cap`.

## Method

The sector is contained in a cylinder of radius `r` and half-length `1` about the `d₀`-axis: if
`‖x‖ ≤ 1` and `x/‖x‖` is within `r` of `±d₀`, then the component of `x` orthogonal to `d₀` has norm
at most `r ‖x‖ ≤ r`, because orthogonal projection onto `d₀ᗮ` is a contraction killing `d₀`. That
cylinder is covered by the two `r`-tubes about the unit segments `[-d₀, 0]` and `[0, d₀]`, so
`Tube.volume_le` supplies the bound with the explicit constant `2 · 2^(n+1)`.

No sharpness is attempted; only the exponent `n - 1` matters downstream.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped Pointwise

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

/-- The **projective direction cap** of radius `r` about the unit vector `d₀`, as a set of unit
vectors. Projective, i.e. `d₀` and `-d₀` give the same cap, because tube axes are unoriented. -/
def projectiveCap (d₀ : E) (r : ℝ) : Set E :=
  {u | ‖u‖ = 1 ∧ min ‖u - d₀‖ ‖u + d₀‖ ≤ r}

/-- The **cone sector** over `projectiveCap d₀ r`, intersected with the closed unit ball. This is
the set whose Lebesgue measure controls the uniform sphere measure of the cap, via
`MeasureTheory.Measure.toSphere_apply'`. -/
def capSector (d₀ : E) (r : ℝ) : Set E :=
  {x | x ≠ 0 ∧ min ‖‖x‖⁻¹ • x - d₀‖ ‖‖x‖⁻¹ • x + d₀‖ ≤ r} ∩ closedBall 0 1

/-- The cylinder of radius `r` and half-length `1` about the `d₀`-axis. -/
def axisCylinder (d₀ : E) (r : ℝ) : Set E :=
  {x | |inner ℝ d₀ x| ≤ 1 ∧ ‖x - (inner ℝ d₀ x) • d₀‖ ≤ r}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- **The cone sector sits inside the cylinder.** The orthogonal projection onto `d₀ᗮ` is a
contraction annihilating `d₀`, so a point of the unit ball whose direction is within `r` of `±d₀`
has orthogonal component of norm at most `r`. -/
theorem capSector_subset_axisCylinder (d₀ : E) (hd₀ : ‖d₀‖ = 1) {r : ℝ} (hr : 0 ≤ r) :
    capSector d₀ r ⊆ axisCylinder d₀ r := by
  intro x hx
  rcases hx with ⟨⟨hx0, hxmin⟩, hxball⟩
  have hxnorm : ‖x‖ ≤ 1 := by
    simpa using (mem_closedBall_iff_norm.mp hxball)
  set u : E := ‖x‖⁻¹ • x with hxu0
  have hxu : x = ‖x‖ • u := by
    rw [hxu0, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx0), one_smul]
  have hPadd : ∀ y z : E,
      (y + z) - (inner ℝ d₀ (y + z)) • d₀ =
        (y - (inner ℝ d₀ y) • d₀) + (z - (inner ℝ d₀ z) • d₀) := by
    intro y z
    rw [inner_add_right, add_smul]
    abel
  have hPsmul : ∀ y : E, ∀ s : ℝ,
      (s • y) - (inner ℝ d₀ (s • y)) • d₀ = s • (y - (inner ℝ d₀ y) • d₀) := by
    intro y s
    rw [real_inner_smul_right, ← smul_smul, smul_sub]
  have hPd₀ : d₀ - (‖d₀‖ ^ 2) • d₀ = 0 := by
    simp [hd₀]
  have hcontract : ∀ y : E, ‖y - (inner ℝ d₀ y) • d₀‖ ≤ ‖y‖ := by
    intro y
    have hnorm : ‖(inner ℝ d₀ y) • d₀‖ ^ 2 = (inner ℝ d₀ y) ^ 2 := by
      rw [norm_smul, hd₀]
      simp
    have hinner : inner ℝ y ((inner ℝ d₀ y) • d₀) =
        (inner ℝ d₀ y) * (inner ℝ d₀ y) := by
      rw [real_inner_smul_right, real_inner_comm d₀ y]
    have hsq : (‖y - (inner ℝ d₀ y) • d₀‖) ^ 2 ≤ ‖y‖ ^ 2 := by
      calc
        (‖y - (inner ℝ d₀ y) • d₀‖) ^ 2
            = ‖y‖ ^ 2 - 2 * inner ℝ y ((inner ℝ d₀ y) • d₀)
              + ‖(inner ℝ d₀ y) • d₀‖ ^ 2 := by
              rw [norm_sub_sq_real]
        _ = ‖y‖ ^ 2 - 2 * ((inner ℝ d₀ y) * (inner ℝ d₀ y))
            + (inner ℝ d₀ y) ^ 2 := by
              rw [hinner, hnorm]
        _ = ‖y‖ ^ 2 - (inner ℝ d₀ y) ^ 2 := by
              ring
        _ ≤ ‖y‖ ^ 2 := by
              nlinarith [sq_nonneg (inner ℝ d₀ y)]
    exact le_of_sq_le_sq hsq (norm_nonneg y)
  have h₁ : |inner ℝ d₀ x| ≤ 1 := by
    calc
      |inner ℝ d₀ x| ≤ ‖d₀‖ * ‖x‖ := abs_real_inner_le_norm d₀ x
      _ = ‖x‖ := by rw [hd₀, one_mul]
      _ ≤ 1 := hxnorm
  rcases (min_le_iff.mp hxmin) with hdu | hdv
  · refine ⟨h₁, ?_⟩
    have hPuEq : u - (inner ℝ d₀ u) • d₀ =
        (u - d₀) - (inner ℝ d₀ (u - d₀)) • d₀ := by
      simpa [hPd₀, real_inner_self_eq_norm_sq, sub_add_cancel] using
        hPadd (u - d₀) d₀
    have hPx : x - (inner ℝ d₀ x) • d₀ =
        ‖x‖ • ((u - d₀) - (inner ℝ d₀ (u - d₀)) • d₀) := by
      calc
        x - (inner ℝ d₀ x) • d₀ = ‖x‖ • (u - (inner ℝ d₀ u) • d₀) := by
          conv_lhs => rw [hxu]
          rw [hPsmul]
        _ = ‖x‖ • ((u - d₀) - (inner ℝ d₀ (u - d₀)) • d₀) := by
          rw [hPuEq]
    calc
      ‖x - (inner ℝ d₀ x) • d₀‖
          = ‖x‖ * ‖(u - d₀) - (inner ℝ d₀ (u - d₀)) • d₀‖ := by
            rw [hPx, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
      _ ≤ ‖x‖ * ‖u - d₀‖ := by
            exact mul_le_mul_of_nonneg_left (hcontract (u - d₀))
              (norm_nonneg x)
      _ ≤ ‖x‖ * r := by
            exact mul_le_mul_of_nonneg_left hdu (norm_nonneg x)
      _ ≤ r := by
            calc
              ‖x‖ * r ≤ 1 * r := mul_le_mul_of_nonneg_right hxnorm hr
              _ = r := one_mul r
  · refine ⟨h₁, ?_⟩
    have hPuEq : u - (inner ℝ d₀ u) • d₀ =
        (u + d₀) - (inner ℝ d₀ (u + d₀)) • d₀ := by
      simpa [hPd₀, real_inner_self_eq_norm_sq] using (hPadd u d₀).symm
    have hPx : x - (inner ℝ d₀ x) • d₀ =
        ‖x‖ • ((u + d₀) - (inner ℝ d₀ (u + d₀)) • d₀) := by
      calc
        x - (inner ℝ d₀ x) • d₀ = ‖x‖ • (u - (inner ℝ d₀ u) • d₀) := by
          conv_lhs => rw [hxu]
          rw [hPsmul]
        _ = ‖x‖ • ((u + d₀) - (inner ℝ d₀ (u + d₀)) • d₀) := by
          rw [hPuEq]
    calc
      ‖x - (inner ℝ d₀ x) • d₀‖
          = ‖x‖ * ‖(u + d₀) - (inner ℝ d₀ (u + d₀)) • d₀‖ := by
            rw [hPx, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
      _ ≤ ‖x‖ * ‖u + d₀‖ := by
        exact mul_le_mul_of_nonneg_left (hcontract (u + d₀)) (norm_nonneg x)
      _ ≤ ‖x‖ * r := by
        exact mul_le_mul_of_nonneg_left hdv (norm_nonneg x)
      _ ≤ r := by
        calc
          ‖x‖ * r ≤ 1 * r := mul_le_mul_of_nonneg_right hxnorm hr
          _ = r := one_mul r

/-- **The cone sector over a projective cap of radius `r` has volume `≲ r^(n-1)`.** -/
theorem volume_capSector_le [Nontrivial E] (d₀ : E) (hd₀ : ‖d₀‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    volume (capSector d₀ r)
      ≤ 2 * ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
          * ((r.toNNReal : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1) := by
  let δ : NNReal := r.toNNReal
  have hδr : (δ : ℝ) = r := by
    dsimp [δ]
    exact Real.coe_toNNReal r hr.le
  have hδ_le_one : δ ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    rw [hδr]
    exact hr1
  let T₁ : Tube δ E := Tube.mk' δ (x := -d₀) (y := 0) (by
    simpa [dist_eq_norm] using hd₀)
  let T₂ : Tube δ E := Tube.mk' δ (x := 0) (y := d₀) (by
    simpa [dist_eq_norm] using hd₀)
  have h_cyl_sub : axisCylinder d₀ r ⊆ T₁.carrier ∪ T₂.carrier := by
    intro x hx
    change |inner ℝ d₀ x| ≤ 1 ∧ ‖x - (inner ℝ d₀ x) • d₀‖ ≤ r at hx
    let t : ℝ := inner ℝ d₀ x
    have ht1 : |t| ≤ 1 := hx.1
    have htd : ‖x - t • d₀‖ ≤ r := by simpa [t] using hx.2
    have hball : x ∈ closedBall (t • d₀) δ := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      simpa [hδr] using htd
    rcases le_total t 0 with htneg | htpos
    · have h1 : (0 : ℝ) ≤ -t := by linarith
      have h2 : (0 : ℝ) ≤ 1 + t := by linarith [abs_le.mp ht1 |>.1]
      have hseg : t • d₀ ∈ segment ℝ (-d₀) (0 : E) := by
        refine ⟨-t, 1 + t, h1, h2, by ring, ?_⟩
        simp [smul_neg]
      have hT1 : x ∈ T₁.carrier := by
        rw [T₁.carrier_eq]
        exact Set.mem_iUnion₂.mpr ⟨t • d₀, hseg, hball⟩
      exact Or.inl hT1
    · have h1 : (0 : ℝ) ≤ 1 - t := by linarith [abs_le.mp ht1 |>.2]
      have hseg : t • d₀ ∈ segment ℝ (0 : E) d₀ := by
        refine ⟨1 - t, t, h1, htpos, by ring, ?_⟩
        simp
      have hT2 : x ∈ T₂.carrier := by
        rw [T₂.carrier_eq]
        exact Set.mem_iUnion₂.mpr ⟨t • d₀, hseg, hball⟩
      exact Or.inr hT2
  calc
    volume (capSector d₀ r)
        ≤ volume (axisCylinder d₀ r) :=
        measure_mono (capSector_subset_axisCylinder d₀ hd₀ hr.le)
    _ ≤ volume (T₁.carrier ∪ T₂.carrier) := measure_mono h_cyl_sub
    _ ≤ volume T₁.carrier + volume T₂.carrier := measure_union_le T₁.carrier T₂.carrier
    _ ≤ 2 * ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
          * ((r.toNNReal : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1) := by
      have h₁ : volume T₁.carrier ≤ (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
          * (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
        Tube.volume_le hδ_le_one T₁
      have h₂ : volume T₂.carrier ≤ (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
          * (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
        Tube.volume_le hδ_le_one T₂
      calc
        volume T₁.carrier + volume T₂.carrier
            ≤ (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
                * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)
              + (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
                * (δ : ENNReal) ^ (Module.finrank ℝ E - 1) := add_le_add h₁ h₂
        _ = 2 * (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal)
              * (δ : ENNReal) ^ (Module.finrank ℝ E - 1) := by
          rw [← two_mul, ← mul_assoc]

/-- **Spherical-cap estimate for the uniform measure on the sphere.**
Mathlib's `MeasureTheory.Measure.toSphere` is the rotation-invariant measure on the unit sphere
induced from Lebesgue measure by polar decomposition; its total mass is
`n · volume (ball 0 1)` (`MeasureTheory.Measure.toSphere_apply_univ`). Any measurable set of unit
vectors all lying within projective distance `r` of a fixed axis `d₀` has `toSphere`-measure
`≲ r^(n-1)`.

This is the rotational factor of GWZ Appendix A equation (106): the law of the axis of a randomly
rotated tube is exactly this uniform sphere measure, so the probability of falling in a `δ`-cap
about a fixed test axis is `≲ δ^(n-1)`. -/
theorem toSphere_projectiveCap_le [Nontrivial E] (d₀ : E) (hd₀ : ‖d₀‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {s : Set (sphere (0 : E) 1)} (hs : MeasurableSet s)
    (hsub : ∀ u ∈ s, min ‖(u : E) - d₀‖ ‖(u : E) + d₀‖ ≤ r) :
    (volume : Measure E).toSphere s
      ≤ (Module.finrank ℝ E)
          * (2 * ((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
              * ((r.toNNReal : NNReal) : ENNReal) ^ (Module.finrank ℝ E - 1)) := by
  have hcontain : Ioo (0 : ℝ) 1 • ((↑) '' s) ⊆ capSector d₀ r := by
    intro x hx
    rw [Set.mem_smul] at hx
    rcases hx with ⟨c, hc, u', hu', hcu⟩
    rw [Set.mem_image] at hu'
    rcases hu' with ⟨u₀, hu₀, rfl⟩
    have hu₀norm : ‖(u₀ : E)‖ = 1 := by
      exact mem_sphere_zero_iff_norm.mp u₀.2
    have hxnorm : ‖x‖ = c := by
      calc
        ‖x‖ = ‖c • (u₀ : E)‖ := by rw [← hcu]
        _ = |c| * ‖(u₀ : E)‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ = c * 1 := by rw [abs_of_pos hc.1, hu₀norm]
        _ = c := by rw [mul_one]
    have hx0 : x ≠ 0 := by
      intro hx0
      have hz : ‖x‖ = 0 := by simp [hx0]
      rw [hxnorm] at hz
      exact (ne_of_gt hc.1) hz
    have hxinv : ‖x‖⁻¹ • x = (u₀ : E) := by
      rw [hxnorm, ← hcu, smul_smul, inv_mul_cancel₀ (ne_of_gt hc.1), one_smul]
    have hxmin : min ‖‖x‖⁻¹ • x - d₀‖ ‖‖x‖⁻¹ • x + d₀‖ ≤ r := by
      simpa [hxinv] using hsub u₀ hu₀
    have hxball : x ∈ closedBall (0 : E) 1 := by
      rw [mem_closedBall_iff_norm]
      simpa [hxnorm] using le_of_lt hc.2
    simp only [capSector, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨⟨hx0, hxmin⟩, hxball⟩
  rw [Measure.toSphere_apply' (volume : Measure E) hs]
  exact mul_le_mul_right
    (le_trans (measure_mono hcontain) (volume_capSector_le d₀ hd₀ hr hr1))
    (Module.finrank ℝ E : ENNReal)

end

end Kakeya

end
