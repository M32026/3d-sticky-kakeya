/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectPaidFloor

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core
open ML2Assembly
universe u

set_option maxHeartbeats 4000000 in
theorem source_exists_direct_floor_exit
    {beta varpi eps1 s : Real} {rawGain rawDens : Real -> Real}
    {acc : SourceLocalAccuracyData}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1) (heps1 : 0 < eps1)
    (hp : Lemma91ParamsAt.{u} beta varpi rawGain rawDens)
    (hvarpi : varpi < 1 / 2)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace Real (Fin 3)) beta)
    (hF : FrostmanEstimate.{u} (EuclideanSpace Real (Fin 3)) beta)
    (hbudget : SourceLocalBudget beta varpi eps1 rawGain rawDens s acc)
    (M M1 Mc : Nat)
    (hmesh : SourceTowerMesh (ML2Spine.spineCount varpi eps1) M1 Mc M
      (ML2Spine.spineNu beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens))
      (sourceTerminalParent beta varpi eps1 rawGain rawDens)) :
    exists (eta : Real) (K : Nat), 0 < eta /\ eta <= s /\ 1 <= K /\
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall {iota : Type u} (S : Finset iota)
          (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
          (Q : SourceThreadedTower S T M sourceThreadConstant)
          (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        SourceFixedTowerInput Q sourceBottomED sourceLevelED eta ->
        SourceTowerStatistics Q Z ->
        delta ^ eta <= ShadedBody.fullness S (fun i => (Z i).toShadedBody) ->
        forall (m a b : Nat), m < ML2Spine.spineCount varpi eps1 ->
        SourceParentUpperWindow Q sourceBottomED sourceLevelED
          (ML2Spine.spineCount varpi eps1) (sourceZeroLadder beta varpi eps1 rawGain rawDens)
          (ML2Spine.spineDiv varpi eps1) a b (m + 1) ->
        SourceDirectFloor Q (ML2Spine.spineDiv varpi eps1)
          (sourceZeroLadder beta varpi eps1 rawGain rawDens (m + 2))
          (sourceTerminalParent beta varpi eps1 rawGain rawDens m) a b ->
        ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
          sourceFixedPreparationLoss K delta *
            (delta : ENNReal) ^ sourceZeroFloorGain (ML2Spine.spineDiv varpi eps1)
              (rawGain (sourceZeroLadder beta varpi eps1 rawGain rawDens (m + 2) / 16)) *
            (S.card : ENNReal) ^ beta := by
  obtain ⟨eta, K, heta, hetas, hthin, hK, hmargin, hgeometry⟩ :=
    source_exists_direct_paid_floor_geometry hbeta0 hbeta1 heps1 hp hvarpi
      hKT hF hbudget M M1 Mc hmesh
  refine ⟨eta, K, heta, hetas, hK, ?_⟩
  filter_upwards [hgeometry,
    VeryNotSticky.eventually_ennreal_le_rpow_neg
      (K := (16 : ENNReal) ^ beta) (by finiteness) hbudget.accuracy_pos,
    Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)] with delta hgeometry hconstant hd
  intro iota S T Q Z hinput hstats hfull m a b hm hupper P
  obtain ⟨F, hstage, hlambda, hsplit, hanalysis⟩ :=
    hgeometry S T Q Z hinput hstats hfull m a b hm hupper P
  have hbound := source_retained_fourFactor_ledger Q hd.1 hbeta0.le F
  have hd0 : (delta : ENNReal) ≠ 0 := by exact_mod_cast hd.1.ne'
  have hdtop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hd1 : (delta : ENNReal) <= 1 := by exact_mod_cast hd.2.le
  have hpow : ENNReal.ofReal ((delta : Real) ^ (-2 * eta)) =
      (delta : ENNReal) ^ (-2 * eta) := by
    rw [← ENNReal.ofReal_rpow_of_pos (show (0 : Real) < delta by exact_mod_cast hd.1)]
    simp only [ENNReal.ofReal_coe_nnreal]
  rw [hpow] at hsplit
  calc _ <= (sourceFixedPreparationLoss K delta * (delta : ENNReal) ^ (-2 * eta)) *
      (delta : ENNReal) ^ (-s) *
      (delta : ENNReal) ^ (sourceTerminalNetGain beta varpi eps1 rawGain rawDens m -
        acc.epsf m - acc.epsp m -
        (acc.epsc m + sourceZeroLadder beta varpi eps1 rawGain rawDens (m + 1))) *
      (S.card : ENNReal) ^ beta :=
        hbound.trans (mul_le_mul' (mul_le_mul' (mul_le_mul' hsplit hconstant) le_rfl) le_rfl)
    _ = sourceFixedPreparationLoss K delta *
      (delta : ENNReal) ^ (sourceTerminalNetGain beta varpi eps1 rawGain rawDens m -
        acc.epsf m - acc.epsp m -
        (acc.epsc m + sourceZeroLadder beta varpi eps1 rawGain rawDens (m + 1)) - s - 2 * eta) *
      (S.card : ENNReal) ^ beta := by
        rw [mul_assoc (sourceFixedPreparationLoss K delta),
          ← ENNReal.rpow_add _ _ hd0 hdtop,
          mul_assoc (sourceFixedPreparationLoss K delta),
          ← ENNReal.rpow_add _ _ hd0 hdtop]
        congr 3 <;> ring
    _ <= _ := mul_le_mul' (mul_le_mul' le_rfl
      (ENNReal.rpow_le_rpow_of_exponent_ge hd1 (by linarith only [hmargin m hm]))) le_rfl

end Kakeya.ML2Core
