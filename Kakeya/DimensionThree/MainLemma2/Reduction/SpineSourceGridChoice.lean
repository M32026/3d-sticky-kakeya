/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineParams

/-!
# Numerical source grid choice on the canonical spine

The structural and Sticky input ceilings are fixed before this numerical
choice. No source tower integer or runtime preparation is constructed here.
-/

@[expose] public section

namespace Kakeya.ML2Spine

/-- The source coarse count uses the nonnegative natural ceiling. -/
noncomputable def sourceCoarseCount (beta : Real) : Nat :=
  max 5 (Nat.ceil (16 / (beta / 20) ^ 2))

/-- All numerical caps and count/divisor conclusions for the actual canonical grid. -/
structure SourceGridChoiceBounds (beta varpi etaA epsSt eps1 : Real) : Prop where
  eps_le_sticky : eps1 <= epsSt
  eps_le_structural : eps1 <= etaA
  eps_le_beta : eps1 <= beta / 4
  count_ge_4096 : 4096 <= spineCount varpi eps1
  div_pos : 0 < spineDiv varpi eps1
  div_le_eps : spineDiv varpi eps1 <= eps1 / 25
  source_count : max (max 5 (Nat.ceil (100 / etaA ^ 2))) (sourceCoarseCount beta) <=
    spineCount varpi eps1
  div_le_coarse : 4 * spineDiv varpi eps1 <= beta / 20
  count_real_lower : 625 / eps1 ^ 2 <= (spineCount varpi eps1 : Real)

/-- Choose a positive canonical-grid accuracy below both independently fixed input ceilings. -/
theorem sourceSpine_exists_grid_choice {beta varpi etaA epsSt : Real}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1) (hvarpi : 0 < varpi)
    (hetaA : 0 < etaA) (hepsSt : 0 < epsSt) :
    exists eps1 : Real, 0 < eps1 /\ SourceGridChoiceBounds beta varpi etaA epsSt eps1 := by
  let eps1 := min epsSt (min etaA (beta / 4))
  have heps1 : 0 < eps1 := lt_min hepsSt (lt_min hetaA (by positivity))
  have hepsSt' : eps1 <= epsSt := min_le_left _ _
  have hepsA : eps1 <= etaA := (min_le_right _ _).trans (min_le_left _ _)
  have hepsB : eps1 <= beta / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have htpos := spineEps₂_pos hvarpi heps1
  have htcap : spineEps₂ varpi eps1 <= eps1 / 5 := spineEps₂_le_everyScale
  have htcap_sq := mul_self_le_mul_self htpos.le htcap
  have hepsA_sq := mul_self_le_mul_self heps1.le hepsA
  have hepsB_sq := mul_self_le_mul_self heps1.le hepsB
  have hreal : 625 / eps1 ^ 2 <= (spineCount varpi eps1 : Real) := by
    calc
      625 / eps1 ^ 2 <= 25 / spineEps₂ varpi eps1 ^ 2 := by
        apply (div_le_div_iff₀ (sq_pos_of_pos heps1) (sq_pos_of_pos htpos)).2
        nlinarith [htcap_sq]
      _ <= (spineCount varpi eps1 : Real) := Nat.le_ceil _
  have hstruct : Nat.ceil (100 / etaA ^ 2) <= spineCount varpi eps1 := by
    apply Nat.ceil_le.mpr
    apply le_trans _ hreal
    apply (div_le_div_iff₀ (sq_pos_of_pos hetaA) (sq_pos_of_pos heps1)).2
    nlinarith [hepsA_sq, sq_nonneg etaA]
  have hcoarse : Nat.ceil (16 / (beta / 20) ^ 2) <= spineCount varpi eps1 := by
    apply Nat.ceil_le.mpr
    apply le_trans _ hreal
    apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos heps1)).2
    nlinarith [hepsB_sq, sq_nonneg beta]
  have hcount := four_thousand_le_spineCount hvarpi heps1
  have hfive : 5 <= spineCount varpi eps1 := by omega
  have hdiv : spineDiv varpi eps1 <= eps1 / 25 := by
    have := spineDiv_le hvarpi heps1
    linarith
  refine ⟨eps1, heps1, ?_⟩
  exact {
    eps_le_sticky := hepsSt'
    eps_le_structural := hepsA
    eps_le_beta := hepsB
    count_ge_4096 := hcount
    div_pos := spineDiv_pos hvarpi heps1
    div_le_eps := hdiv
    source_count := max_le (max_le hfive hstruct) (max_le hfive hcoarse)
    div_le_coarse := by linarith
    count_real_lower := hreal }

end Kakeya.ML2Spine
