/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Shading

/-! # Refinement bookkeeping

This file collects the elementary bookkeeping used by the factoring construction of GWZ
Proposition 5.1 (see `Kakeya.Factoring.Step1`), corresponding to the blueprint subsection
`subsec:refinementToolkit` ("Refinement bookkeeping"). The purely combinatorial fiberwise
summation identities of the blueprint subsection `subsec:fiberwiseSum` are
`Finset.sum_fiberwise_eq_sum_filter`, `Finset.sum_fiberwise_of_maps_to` and
`Finset.disjiUnion_filter_eq` from Mathlib, together with `Finset.filter_mem_filter_eq` in
`Kakeya.Mathlib.Finset`.

Nothing here is specific to that construction, to the ambient dimension, or to convexity: every
statement manipulates only the volumes `|V i|` and `|Y (V i)|` together with the partition map
`p : ι → κ`.

## Main statements

* discarding bodies of low relative shading: `ShadedBody.discardLowShading` together with
  `ShadedBody.sum_volume_shade_sdiff_discardLowShading_le`,
  `ShadedBody.le_volume_shade_of_mem_discardLowShading`,
  `ShadedBody.one_sub_mul_sum_volume_shade_le_sum_discardLowShading` and
  `ShadedBody.isCRefinement_discardLowShading`;
* selecting blocks of a partition: `ShadedBody.isCRefinement_filter_mem`.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal ENNReal

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*}

/-! ### Discarding bodies of low relative shading -/

/-- The bodies kept by the discard step at level `c` (blueprint `discardLowShadingSet`): the
indices `i ∈ s` whose shading satisfies `|Y (V i)| ≥ c * λ(𝒱, Y) * |V i|`, where
`λ(𝒱, Y) = fullness s V`. -/
noncomputable def discardLowShading (s : Finset ι) (V : ι → ShadedBody E) (c : ℝ≥0) : Finset ι :=
  {i ∈ s |
    (c : ℝ≥0∞) * (fullness s V : ℝ≥0∞) * volume (V i).carrier ≤ volume (V i).shade}

theorem discardLowShading_subset (s : Finset ι) (V : ι → ShadedBody E) (c : ℝ≥0) :
    discardLowShading s V c ⊆ s := by
  unfold discardLowShading
  exact Finset.filter_subset _ _

/-- **The discarded shading mass** (blueprint `lem:discardLowShadingComplement`): the bodies
thrown away by the discard step at level `c` carry at most a `c` fraction of the total shading
mass. -/
theorem sum_volume_shade_sdiff_discardLowShading_le [DecidableEq ι]
    (s : Finset ι) (V : ι → ShadedBody E) (c : ℝ≥0) :
    ∑ i ∈ s \ discardLowShading s V c, volume (V i).shade
      ≤ (c : ℝ≥0∞) * ∑ i ∈ s, volume (V i).shade := by
  -- For i in the complement, the inequality defining discardLowShading fails
  have hmem : ∀ i ∈ s \ discardLowShading s V c,
      volume (V i).shade < (c : ℝ≥0∞) * (fullness s V : ℝ≥0∞) * volume (V i).carrier := by
    intro i hi
    rcases Finset.mem_sdiff.1 hi with ⟨hi_s, hi_not⟩
    have h_not_ineq :
        ¬ ((c : ℝ≥0∞) * (fullness s V : ℝ≥0∞) * volume (V i).carrier
          ≤ volume (V i).shade) := by
      intro h
      apply hi_not
      rw [discardLowShading, Finset.mem_filter]
      exact ⟨hi_s, h⟩
    exact lt_of_not_ge h_not_ineq
  calc
    ∑ i ∈ s \ discardLowShading s V c, volume (V i).shade
        ≤ ∑ i ∈ s \ discardLowShading s V c,
          ((c : ℝ≥0∞) * (fullness s V : ℝ≥0∞) * volume (V i).carrier) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact (hmem i hi).le
    _ = (c : ℝ≥0∞) * (fullness s V : ℝ≥0∞) *
          ∑ i ∈ s \ discardLowShading s V c, volume (V i).carrier := by
      simp [Finset.mul_sum, mul_assoc]
    _ ≤ (c : ℝ≥0∞) * (fullness s V : ℝ≥0∞) * ∑ i ∈ s, volume (V i).carrier := by
      refine mul_le_mul_right (Finset.sum_le_sum_of_subset
        (Finset.sdiff_subset (s := s) (t := discardLowShading s V c))) _
    _ = (c : ℝ≥0∞) * (∑ i ∈ s, volume (V i).shade) := by
      rw [mul_assoc, (sum_volumeReal_shade_eq_fullness_mul s V).symm]

/-- **Bodies kept by the discard step** (blueprint `lem:discardLowShadingMem`): every kept index
satisfies `|Y (V i)| ≥ c * λ(𝒱, Y) * |V i|`. The same then holds for every index in any subset of
`discardLowShading s V c`. -/
theorem le_volume_shade_of_mem_discardLowShading {s : Finset ι} {V : ι → ShadedBody E} {c : ℝ≥0}
    {i : ι} (hi : i ∈ discardLowShading s V c) :
    (c : ℝ≥0∞) * (fullness s V : ℝ≥0∞) * volume (V i).carrier ≤ volume (V i).shade := by
  rw [discardLowShading] at hi
  exact (Finset.mem_filter.mp hi).2

/-- **The mass kept by the discard step** (blueprint `lem:discardLowShadingMass`): for
`c < 1`, the kept bodies carry at least a `1 - c` fraction of the total shading mass. -/
theorem one_sub_mul_sum_volume_shade_le_sum_discardLowShading
    (s : Finset ι) (V : ι → ShadedBody E) {c : ℝ≥0} (hc1 : c < 1) :
    ((1 - c : ℝ≥0) : ℝ≥0∞) * ∑ i ∈ s, volume (V i).shade
      ≤ ∑ i ∈ discardLowShading s V c, volume (V i).shade := by
  classical
  set T := ∑ i ∈ s, volume (V i).shade
  set K := ∑ i ∈ discardLowShading s V c, volume (V i).shade
  set D := ∑ i ∈ s \ discardLowShading s V c, volume (V i).shade
  have hsubset : discardLowShading s V c ⊆ s := discardLowShading_subset s V c
  have hsplit : D + K = T := by
    simpa [D, K, T] using
      Finset.sum_sdiff (discardLowShading_subset s V c) (f := fun i => volume (V i).shade)
  have hD : D ≤ (c : ℝ≥0∞) * T :=
    sum_volume_shade_sdiff_discardLowShading_le s V c
  have hDne : D ≠ ⊤ := by
    have hmem : ∀ i ∈ s \ discardLowShading s V c, volume (V i).shade ≠ ∞ := by
      intro i hi
      rcases Finset.mem_sdiff.1 hi with ⟨hi_s, hi_not⟩
      have h_not_ineq :
          ¬ ((c : ℝ≥0∞) * (fullness s V : ℝ≥0∞) * volume (V i).carrier
            ≤ volume (V i).shade) := by
        intro h
        apply hi_not
        rw [discardLowShading, Finset.mem_filter]
        exact ⟨hi_s, h⟩
      have h_lt : volume (V i).shade < (c : ℝ≥0∞) * (fullness s V : ℝ≥0∞) * volume (V i).carrier :=
        lt_of_not_ge h_not_ineq
      have h_lt_top : volume (V i).shade < ∞ := h_lt.trans_le le_top
      exact h_lt_top.ne_top
    exact ENNReal.sum_ne_top.mpr hmem
  by_cases hT : T = ⊤
  · -- Case T = ⊤: the goal holds trivially because the RHS is ⊤
    have hK : K = ⊤ := (ENNReal.add_eq_top.mp (hsplit ▸ hT)).resolve_left hDne
    simp [hT, hK]
  · -- Case hT : T ≠ ⊤: algebraic rearrangement
    have hc_one : (c : ℝ≥0∞) ≤ (1 : ℝ≥0∞) := by exact_mod_cast hc1.le
    have h_sub_mul : ((1 : ℝ≥0∞) - (c : ℝ≥0∞)) * T = T - (c : ℝ≥0∞) * T := by
      calc
        ((1 : ℝ≥0∞) - (c : ℝ≥0∞)) * T = (1 : ℝ≥0∞) * T - (c : ℝ≥0∞) * T :=
          ENNReal.sub_mul (fun _ _ => hT)
        _ = T - (c : ℝ≥0∞) * T := by simp
    calc
      ((1 - c : ℝ≥0) : ℝ≥0∞) * T = ((1 : ℝ≥0∞) - (c : ℝ≥0∞)) * T := by simp
      _ = T - (c : ℝ≥0∞) * T := by rw [h_sub_mul]
      _ ≤ K := by
        have htemp : T ≤ K + (c : ℝ≥0∞) * T := by
          calc
            T = D + K := Eq.symm hsplit
            _ = K + D := add_comm _ _
            _ ≤ K + (c : ℝ≥0∞) * T := add_le_add_right hD K
        exact (tsub_le_iff_right.mpr htemp)

/-- **Discarding bodies of low relative shading** (blueprint `lem:discardLowShading`): for
`c < 1`, the kept subfamily is a `1 - c` refinement of `(𝒱, Y)`. -/
theorem isCRefinement_discardLowShading
    (s : Finset ι) (V : ι → ShadedBody E) {c : ℝ≥0} (hc1 : c < 1) :
    IsCRefinement (discardLowShading s V c) V s V (1 - c) := by
  refine ⟨?_, ?_⟩
  · refine ⟨discardLowShading_subset s V c, ?_⟩
    intro i hi
    exact ⟨rfl, Set.Subset.refl _⟩
  · simpa using one_sub_mul_sum_volume_shade_le_sum_discardLowShading s V hc1

/-! ### Selecting blocks of a partition -/

/-- **A heavy set of blocks selects a `c` refinement** (blueprint
`lem:blockSelectionCRefinement`).

Let `p : ι → κ` be a partition map and let `t₀` contain the image of `u` under `p`. If a set of
blocks `t'` carries a `K⁻¹` fraction of the block weights
`w j = ∑_{i ∈ u, p i = j} |Y (V i)|`, then `(𝒱_{u'}, Y)` is a `K⁻¹` refinement of `(𝒱_u, Y)`,
where `u' = {i ∈ u | p i ∈ t'}`.

No relation between `t'` and `t₀` is needed: the `t'` side of the hypothesis is the fiberwise
decomposition of `∑_{i ∈ u'} |Y (V i)|`, which holds for an arbitrary `t'`. Nor is `K ≠ 0`
needed: for `K = 0` the hypothesis forces `∑_{i ∈ u} |Y (V i)| = 0` and `K⁻¹ = 0`. -/
theorem isCRefinement_filter_mem [DecidableEq κ]
    {u : Finset ι} {V : ι → ShadedBody E} {t₀ t' : Finset κ} {p : ι → κ}
    (hp : ∀ i ∈ u, p i ∈ t₀) {K : ℝ≥0}
    (hheavy : ∑ j ∈ t₀, ∑ i ∈ {i ∈ u | p i = j}, volume (V i).shade
      ≤ (K : ℝ≥0∞) * ∑ j ∈ t', ∑ i ∈ {i ∈ u | p i = j}, volume (V i).shade) :
    IsCRefinement {i ∈ u | p i ∈ t'} V u V K⁻¹ := by
  -- Refinement part: u' ⊆ u and each body is unchanged
  have hsub : {i ∈ u | p i ∈ t'} ⊆ u := Finset.filter_subset _ _
  have href : ∀ i ∈ {i ∈ u | p i ∈ t'},
      (V i).toConvexSpaceBody = (V i).toConvexSpaceBody ∧ (V i).shade ⊆ (V i).shade := by
    intro i hi
    exact ⟨rfl, Set.Subset.refl _⟩
  -- Mass part: rewrite the sums in hheavy
  have hsum_total : ∑ j ∈ t₀, ∑ i ∈ {i ∈ u | p i = j}, volume (V i).shade
      = ∑ i ∈ u, volume (V i).shade := by
    simpa using Finset.sum_fiberwise_of_maps_to hp (fun i => volume (V i).shade)
  have hsum_filt : ∑ j ∈ t', ∑ i ∈ {i ∈ u | p i = j}, volume (V i).shade
      = ∑ i ∈ {i ∈ u | p i ∈ t'}, volume (V i).shade := by
    simpa using Finset.sum_fiberwise_eq_sum_filter u t' p (fun i => volume (V i).shade)
  have hA' :
      ∑ i ∈ u, volume (V i).shade
        ≤ (K : ℝ≥0∞) * ∑ i ∈ {i ∈ u | p i ∈ t'}, volume (V i).shade := by
    simpa [hsum_total, hsum_filt] using hheavy
  have hmass : ((K⁻¹ : ℝ≥0) : ℝ≥0∞) * ∑ i ∈ u, volume (V i).shade
      ≤ ∑ i ∈ {i ∈ u | p i ∈ t'}, volume (V i).shade := by
    by_cases hK : K = 0
    · subst hK
      have hA_zero : ∑ i ∈ u, volume (V i).shade = 0 := by
        have hA_nonpos : ∑ i ∈ u, volume (V i).shade ≤ 0 := by
          calc
            ∑ i ∈ u, volume (V i).shade
                ≤ (0 : ℝ≥0∞) *
                  ∑ i ∈ {i ∈ u | p i ∈ t'}, volume (V i).shade := hA'
            _ = 0 := by simp
        have hA_nonneg : 0 ≤ ∑ i ∈ u, volume (V i).shade :=
          Finset.sum_nonneg fun i _ => by positivity
        exact le_antisymm hA_nonpos hA_nonneg
      simp [hA_zero]
    · have hKpos : (K : ℝ≥0∞) ≠ 0 := by exact_mod_cast hK
      have hKinf : (K : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
      calc
        ((K⁻¹ : ℝ≥0) : ℝ≥0∞) * ∑ i ∈ u, volume (V i).shade
            = ((K : ℝ≥0∞)⁻¹) * ∑ i ∈ u, volume (V i).shade := by
          simp [ENNReal.coe_inv hK]
        _ ≤ ((K : ℝ≥0∞)⁻¹) *
              ((K : ℝ≥0∞) * ∑ i ∈ {i ∈ u | p i ∈ t'}, volume (V i).shade) :=
          mul_le_mul_right hA' _
        _ = (((K : ℝ≥0∞)⁻¹) * (K : ℝ≥0∞)) *
              ∑ i ∈ {i ∈ u | p i ∈ t'}, volume (V i).shade := by
          rw [mul_assoc]
        _ = (1 : ℝ≥0∞) * ∑ i ∈ {i ∈ u | p i ∈ t'}, volume (V i).shade := by
          rw [ENNReal.inv_mul_cancel hKpos hKinf]
        _ = ∑ i ∈ {i ∈ u | p i ∈ t'}, volume (V i).shade := by simp
  simpa [IsCRefinement] using ⟨⟨hsub, href⟩, hmass⟩

end ShadedBody
