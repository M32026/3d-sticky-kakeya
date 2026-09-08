/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Thickness.Basic
public import Mathlib.Topology.EMetricSpace.Diam

/-!
# Thickness at diameter
-/

@[expose] public section

namespace Metric

section
variable
  {𝕜} [Ring 𝕜]
  {V} [AddCommGroup V] [Module 𝕜 V]
  {P} [AddTorsor V P] [PseudoEMetricSpace P]

theorem ethickness_zero_le_ediam [Nontrivial 𝕜] (s : Set P) : ethickness 𝕜 s 0 ≤ ediam s := by
  by_cases hs : s = ∅
  · simp [hs]
  by_cases h : ediam s = ⊤
  · simp [h]
  · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hs
    have hd {y} (hy : y ∈ s) := edist_le_ediam_of_mem hy hx
    lift ediam s to NNReal using h with r
    apply ethickness_le_of_cthickening (A := affineSpan 𝕜 {x} )
    · rw [direction_affineSpan, vectorSpan_singleton]
      simp
    · intro y hy
      simpa using hd hy

theorem ediam_le_two_mul_ethickness_zero [IsDomain 𝕜] [Module.IsTorsionFree 𝕜 V] (s : Set P) :
    ediam s ≤ 2 * ethickness 𝕜 s 0 := by
  rw [le_mul_ethickness_iff _ _ _ (by norm_num) (by norm_num)]
  intro r A hA hs
  rw [ediam_le_iff]
  intro x hx
  obtain ⟨p, hp⟩ : (A : Set P).Nonempty := by
    by_contra! hAe
    rw [hAe, cthickening_empty] at hs
    exact hs hx
  have hA_eq : (A : Set P) = {p} := by
    rw [Set.eq_singleton_iff_unique_mem]
    constructor
    · exact hp
    · intro q hq
      rw [← vsub_eq_zero_iff_eq, ← Submodule.mem_bot 𝕜]
      convert AffineSubspace.vsub_mem_direction hq hp
      symm
      rw [← Submodule.rank_eq_zero]
      apply le_antisymm hA
      simp only [Nat.cast_zero, zero_le]
  suffices ∀ x ∈ s, edist x p ≤ r by
    intro y hy
    apply this at hx
    apply this at hy
    apply (edist_triangle x p y).trans
    rw [edist_comm _ y, two_mul]
    apply add_le_add hx hy
  intro x hx
  simpa [hA_eq] using hs hx

end

section
variable
  {𝕜} [Ring 𝕜]
  {V} [AddCommGroup V] [Module 𝕜 V]
  {P} [AddTorsor V P] [PseudoMetricSpace P]

/-- If a set contains two points, then its rank-zero `ethickness` is at least half
the distance between them. -/
theorem half_dist_le_ethickness_zero [IsDomain 𝕜] [Module.IsTorsionFree 𝕜 V]
    {s : Set P} {x y : P} (hx : x ∈ s) (hy : y ∈ s) :
    ENNReal.ofReal (dist x y / 2) ≤ ethickness 𝕜 s 0 := by
  have h1 : edist x y ≤ 2 * ethickness 𝕜 s 0 :=
    (edist_le_ediam_of_mem hx hy).trans (ediam_le_two_mul_ethickness_zero (𝕜 := 𝕜) s)
  rw [edist_dist] at h1
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2),
    show (ENNReal.ofReal 2 : ENNReal) = 2 from by simp,
    ENNReal.div_le_iff (by norm_num) (by norm_num), mul_comm]
  exact h1

/-- The rank-zero affine thickness of a bounded set is at most its diameter. -/
theorem thickness_zero_le_diam [Nontrivial 𝕜] {s : Set P} (h : Bornology.IsBounded s) :
    thickness 𝕜 s 0 ≤ Metric.diam s := by
  have hle := ethickness_zero_le_ediam (𝕜 := 𝕜) s
  rw [ethickness_thickness' h 0] at hle
  rw [← ENNReal.toReal_ofReal (thickness_nonneg s 0)]
  exact ENNReal.toReal_mono h.ediam_ne_top hle

end

end Metric
