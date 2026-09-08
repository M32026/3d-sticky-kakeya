/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceParameterChoice
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectPotential
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceSmallness

/-!
# Full source indices and the source potential anchor

Source indices range from one to N + 1. The total natural-index function below
is not the separately chosen source input exponent called eta_0.
-/

@[expose] public section

namespace Kakeya.ML2Assembly

universe u

/-- The source ladder eta_j = q_(j-1), used on one through N + 1. -/
noncomputable def sourceChoiceLadder (beta varpi eps1 : Real)
    (rawGain rawDens : Real -> Real) (j : Nat) : Real :=
  ML2Spine.spineRung beta varpi eps1
    (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (j - 1)

/-- The source anchor is q_0 times e squared over eight. -/
noncomputable def sourceChoicePotential (beta varpi eps1 : Real)
    (rawGain rawDens : Real -> Real) : Real :=
  ML2Spine.spineRung beta varpi eps1
    (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) 0 *
      ML2Spine.spineDiv varpi eps1 ^ 2 / 8

/-- The full finite index map and both endpoint pairs. -/
structure SourceIndexBookkeeping (N : Nat) (q eta : Nat -> Real) : Prop where
  count_pos : 1 <= N
  window_index_iff : forall m : Nat,
    Iff (m < N) (And (1 <= m + 1) (m + 1 <= N))
  window_inverse_iff : forall J : Nat,
    Iff (And (1 <= J) (J <= N)) (And (J - 1 < N) ((J - 1) + 1 = J))
  ladder_index_iff : forall j : Nat,
    Iff (And (1 <= j) (j <= N + 1)) (And (j - 1 <= N) ((j - 1) + 1 = j))
  ladder_identification : forall j : Nat, 1 <= j -> j <= N + 1 -> eta j = q (j - 1)
  selected_pair : forall m : Nat, m < N ->
    (eta (m + 1), eta (m + 2)) = (q m, q (m + 1))
  bottom_pair : (eta 1, eta 2) = (q 0, q 1)
  top_pair : (eta N, eta (N + 1)) = (q (N - 1), q N)

/-- Source-indexed ladder properties and the two separately identified anchors. -/
structure SourceLadderAnchorBounds (beta e : Real) (N : Nat) (eta : Nat -> Real)
    (hSrc oldH : Real) : Prop where
  count_pos : 1 <= N
  div_pos : 0 < e
  ladder_pos : forall j : Nat, 1 <= j -> j <= N + 1 -> 0 < eta j
  ladder_mono : MonotoneOn eta (Set.Icc 1 (N + 1))
  ladder_top : eta (N + 1) = e
  ladder_le_div : forall j : Nat, 1 <= j -> j <= N + 1 -> eta j <= e
  ladder_separation : forall J : Nat, 1 <= J -> J <= N ->
    eta J <= e ^ 2 * eta (J + 1) / 100
  source_anchor_formula : hSrc = eta 1 * e ^ 2 / 8
  source_anchor_pos : 0 < hSrc
  old_anchor_formula : oldH = eta 2 * e ^ 2 / 8

/-- The source range corresponds to every admissible canonical index, including zero. -/
theorem sourceChoice_indexBookkeeping {beta varpi eps1 : Real}
    {rawGain rawDens : Real -> Real}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1) (heps1 : 0 < eps1)
    (hp : Lemma91ParamsAt.{u} beta varpi rawGain rawDens) :
    SourceIndexBookkeeping (ML2Spine.spineCount varpi eps1)
      (ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens))
      (sourceChoiceLadder beta varpi eps1 rawGain rawDens) := by
  exact {
    count_pos := ML2Spine.one_le_spineCount hp.window_pos heps1
    window_index_iff := by intro m; omega
    window_inverse_iff := by intro J; omega
    ladder_index_iff := by intro j; omega
    ladder_identification := by intro j _ _; rfl
    selected_pair := by
      intro m _
      simp only [sourceChoiceLadder, Nat.add_sub_cancel,
        show m + 2 - 1 = m + 1 by omega]
    bottom_pair := rfl
    top_pair := by simp only [sourceChoiceLadder, Nat.add_sub_cancel] }

/-- The source potential is positive and the old potential keeps its next-rung formula. -/
theorem sourceChoice_ladderAnchorBounds {beta varpi eps1 : Real}
    {rawGain rawDens : Real -> Real}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1) (heps1 : 0 < eps1)
    (hp : Lemma91ParamsAt.{u} beta varpi rawGain rawDens) :
    SourceLadderAnchorBounds beta (ML2Spine.spineDiv varpi eps1)
      (ML2Spine.spineCount varpi eps1) (sourceChoiceLadder beta varpi eps1 rawGain rawDens)
      (sourceChoicePotential beta varpi eps1 rawGain rawDens)
      (ML2Core.defectH beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens)) := by
  have hchoice := sourceParameterChoice hbeta0 hbeta1 hp
  have hsp := ML2Spine.spineRung_isSpine hbeta0 hbeta1 hp.window_pos heps1
    hchoice.params.gain_pos hchoice.params.dens_pos
  have hindex := sourceChoice_indexBookkeeping hbeta0 hbeta1 heps1 hp
  exact {
    count_pos := hindex.count_pos
    div_pos := hsp.div_pos
    ladder_pos := by
      intro j _ _
      exact hsp.rung_pos (j - 1)
    ladder_mono := by
      intro a _ b _ hab
      exact hsp.rung_mono (by omega)
    ladder_top := by
      simpa only [sourceChoiceLadder, Nat.add_sub_cancel] using hsp.rung_top
    ladder_le_div := by
      intro j _ _
      exact hsp.rung_le_div (j - 1)
    ladder_separation := by
      intro J hJ hJN
      have hJindices := (hindex.window_inverse_iff J).mp (And.intro hJ hJN)
      have hsmall := (sourceSpine_six_smallness hbeta0 hbeta1 heps1 hp
        (J - 1) hJindices.1).geometric
      simpa only [sourceChoiceLadder, Nat.add_sub_cancel, hJindices.2] using hsmall
    source_anchor_formula := rfl
    source_anchor_pos :=
      div_pos (mul_pos (hsp.rung_pos 0) (sq_pos_of_pos hsp.div_pos)) (by norm_num)
    old_anchor_formula := rfl }

end Kakeya.ML2Assembly
