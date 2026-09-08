/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ConvexBody
public import Kakeya.Tube.IntersectionVolume
public import Mathlib.Tactic.Push

/-!
# ED implies midpoint perpendicular δ-separation

Given two essentially-distinct δ-tubes whose directions lie in a common
`c_slide·δ`-cap and whose midpoint axial projection is bounded, their
perpendicular midpoint offset must exceed `c_slide·δ`.
-/

@[expose] public section

open MeasureTheory Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace Kakeya

noncomputable section
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

/-- **ED-to-midpoint-perp-separation (midpoint-only form).**

Given two essentially-distinct δ-tubes `T1, T2` whose directions lie in a
common `c_slide·δ`-cap (in `min ‖d1 ∓ d2‖` norm) and whose midpoint axial
projection on `T2.direction` is bounded by `1/2 - κ`, their **perpendicular**
midpoint offset must exceed `c_slide·δ`.

This is the direct contrapositive of `Tube.nearly_parallel_sliding`: if all three
preconditions held and additionally the perp offset were small, then
`nearly_parallel_sliding` would yield `¬ IsEssentiallyDistinct`, contradicting
the ED hypothesis.

The existentially-bound constants `c_slide, κ, δ₀` are inherited verbatim from
`Tube.nearly_parallel_sliding`: witnesses are `c_slide = 1/(8n)`, `κ = 1/4`,
`δ₀ = 1/32`. -/
lemma ed_midpoint_perp_separation (hn : 1 < Module.finrank ℝ E) :
    ∃ (c_slide κ δ₀ : ℝ),
      0 < c_slide ∧ 0 < κ ∧ κ < 1/2 ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal} (_ : 0 < δ) (_ : (δ : ℝ) ≤ δ₀)
        (T1 T2 : Tube δ E),
        IsEssentiallyDistinct T1.carrier T2.carrier →
        min ‖T1.direction - T2.direction‖ ‖T1.direction + T2.direction‖
          ≤ c_slide * (δ : ℝ) →
        |inner ℝ (T1.midpoint - T2.midpoint) T2.direction| ≤ 1/2 - κ →
        c_slide * (δ : ℝ)
          < ‖T1.midpoint - T2.midpoint -
              (inner ℝ (T1.midpoint - T2.midpoint) T2.direction) •
                T2.direction‖ := by
  obtain ⟨c_slide, κ, δ₀, hc_pos, hκ_pos, hκ_lt, hδ₀_pos, hδ₀_le, hslide⟩
      := Tube.nearly_parallel_sliding hn
  refine ⟨c_slide, κ, δ₀, hc_pos, hκ_pos, hκ_lt, hδ₀_pos, hδ₀_le, ?_⟩
  intro δ hδ hδ_le T1 T2 hED h_dir h_axial
  by_contra h_perp_close
  push Not at h_perp_close
  exact (hslide hδ hδ_le T1 T2 h_dir h_perp_close h_axial) hED

end -- close noncomputable section
end Kakeya
