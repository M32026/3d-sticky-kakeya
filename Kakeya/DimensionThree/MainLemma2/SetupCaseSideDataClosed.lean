/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SetupSideDataGeneral

/-!
# The last Section-9 leaf, closed

`Kakeya.VeryNotSticky.exists_setup_caseSideData_closed` has **exactly** the type of the frozen leaf
`Kakeya.VeryNotSticky.exists_setup_caseSideData` (D6 text) — the type is
written as `SetupCaseSideDataAt …`, the leaf's binders and conclusion kept at the leaf's former place in
`VeryNotStickyCase.lean`; the relocated leaf (`VeryNotStickyClosed.lean`) unfolds it, so the two cannot drift — and is proved by
`Kakeya.VeryNotSticky.exists_setup_caseSideData_general`, whose three producer binders are theorems
(`eventually_slabPackage_general_of_lattice'`, `eventually_hAngular_general_of_centred`, and the
produced ball data's degree bound from `ballDataGeneralTarget_edDegree`), with the four parameter
binders discharged by explicit choices (A.4): `C₀bd := edSegmentsConstant`, `D := ballCoverConstant`,
`c₁ := (edDensityConstant · ballCoverConstant)⁻¹`,
`εg := thresholdExponent β exscal η τ / 2`
(`thresholdExponent_pos`).

It lives here, downstream of the whole general chain, because that chain imports
`VeryNotStickyCase.lean` (fourteen of its declarations, and `Reduction/Assembly`), so the frozen
leaf's own file cannot import the general theorem: making the frozen leaf's body *this* theorem is a
file-placement change , not a proof step.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

universe u

open Filter Topology

/-- **`exists_setup_caseSideData`, proved** — at its frozen type, from the general boundary with
every producer a theorem and every parameter binder an explicit choice. -/
theorem exists_setup_caseSideData_closed {β ζ exscal ϱ η τ τ' : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hζ : 0 < ζ) (hexscal : 0 < exscal) (hϱ : 0 < ϱ) (hη : 0 < η)
    (params : CaseParams β ζ exscal ϱ η τ τ')
    (hplankF : PlankFrostmanBudget.{u} β ϱ τ η)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (w : Kakeya.CoarseKTWindow.{u} β ϱ η exscal) :
    SetupCaseSideDataAt.{u} hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w := by
  have hε : 0 < thresholdExponent β exscal η τ := thresholdExponent_pos hη params
  have hbc : (0 : NNReal) < (ballCoverConstant : NNReal) := by
    exact_mod_cast (show 0 < ballCoverConstant by decide)
  have hed : (0 : NNReal) < edDensityConstant :=
    lt_of_lt_of_le (by norm_num) four_le_edDensityConstant
  have hprod : edDensityConstant * (ballCoverConstant : NNReal) ≠ 0 := (mul_pos hed hbc).ne'
  refine exists_setup_caseSideData_general.{u} hβ hβ1 hζ hexscal hϱ hη params hplankF hKT hF w
    (C₀bd := edSegmentsConstant) le_rfl (D := ballCoverConstant) le_rfl
    (c₁ := (edDensityConstant * (ballCoverConstant : NNReal))⁻¹) (inv_pos.mpr (mul_pos hed hbc)) ?_
    (εg := thresholdExponent β exscal η τ / 2) (half_pos hε) (half_lt_self hε)
  calc edDensityConstant * (edDensityConstant * (ballCoverConstant : NNReal))⁻¹ *
        (ballCoverConstant : NNReal)
      = (edDensityConstant * (ballCoverConstant : NNReal)) *
          (edDensityConstant * (ballCoverConstant : NNReal))⁻¹ := by ring
    _ = 1 := mul_inv_cancel₀ hprod
    _ ≤ 1 := le_rfl

end Kakeya.VeryNotSticky

end
