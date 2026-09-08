/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceEccentricFactorTransportData

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- The exact assigned datum in the proved Part-B chain. It uses the existing
canonical enumerated factorization and the original Q.place m assignment.
No branching floor is added; the positive n from the real count bin suffices. -/
structure SourceEccentricAssignedDatum (Q : SourceThreadedTower S T M C)
    {Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
    {a m : Nat} {Lout : NNReal} {O : SourceEccentricOuterSplit Q Z a Lout}
    {Rnorm : Real} {Cgeom cParent : NNReal}
    {Nrm : SourceEccentricCellNormalization Q O m Rnorm Cgeom cParent}
    {etaParent bias : Real} {D aw bw cw : NNReal}
    {E : SourceZeroEccentricFactors Q Z a m etaParent bias D aw bw cw}
    {Lsel Ccount H : NNReal}
    {P : SourceEccentricAssignedSelection Q O Nrm E Lsel Ccount}
    (F : SourceEccentricFactorTransport Q P H) where
  datum : Kakeya.Section6PartBData F.factors.uniformThin F.factors.uniformMid
    F.factors.uniformThin_le_uniformMid (F.factors.uniformMid_le_one P.parent_ball)
    P.leaves P.shading P.parents Nrm.parent P.n P.Cfib
    (Kakeya.GlobalPlankFactorization.partBFrostmanConst F.Cw F.Czero) F.Czero
  assignment_eq : datum.decomp.assign = Q.place m
  factor_eq : datum.factor = F.factors.toSection6PartBFactorisationFin F.Cw_one
    F.middle_le_one (lt_of_lt_of_le F.short_pos F.short_le_middle)
    Nrm.parent_pos F.factors_nonempty P.parent_ball
  coarse_fibres_nonempty : forall x, x ∈ datum.factor.cells ->
    (datum.factor.coarseFibre x).Nonempty
  dimensions : forall x, x ∈ datum.factor.cells ->
    Kakeya.IsPlankOfDimensions
      (Kakeya.plankReadingConst F.Cw F.Czero ^ 2)
      F.factors.uniformThin F.factors.uniformMid (datum.factor.body x)
  capture : forall x, x ∈ datum.factor.cells ->
    Kakeya.maxDensity P.parents (fun k => (Nrm.parent k).toConvexSpaceBody) <=
      (F.Czero : ENNReal) * Kakeya.densityIn (datum.factor.coarseFibre x)
        (fun k => (Nrm.parent k).toConvexSpaceBody) (datum.factor.body x)
  parent_le_thin : sourceEccentricParentScale delta M a m cParent <= F.factors.uniformThin
  aspect : F.factors.uniformThin / F.factors.uniformMid <= 3 * H ^ 3 * (aw / bw)
  frostman_budget : Kakeya.GlobalPlankFactorization.partBFrostmanConst F.Cw F.Czero <=
    11664 * H ^ 12
  dimensions_budget : Kakeya.plankReadingConst F.Cw F.Czero ^ 2 <=
    9 * H ^ 4

theorem source_exists_eccentric_assigned_partB_datum (Q : SourceThreadedTower S T M C)
    {Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
    {a m : Nat} {Lout : NNReal} {O : SourceEccentricOuterSplit Q Z a Lout}
    {Rnorm : Real} {Cgeom cParent : NNReal}
    {Nrm : SourceEccentricCellNormalization Q O m Rnorm Cgeom cParent}
    {etaParent bias : Real} {D aw bw cw : NNReal}
    {E : SourceZeroEccentricFactors Q Z a m etaParent bias D aw bw cw}
    {Lsel Ccount H : NNReal}
    {P : SourceEccentricAssignedSelection Q O Nrm E Lsel Ccount}
    (F : SourceEccentricFactorTransport Q P H) :
    Nonempty (SourceEccentricAssignedDatum Q F) := by
  classical
  let datum : Kakeya.Section6PartBData F.factors.uniformThin F.factors.uniformMid
      F.factors.uniformThin_le_uniformMid (F.factors.uniformMid_le_one P.parent_ball)
      P.leaves P.shading P.parents Nrm.parent P.n P.Cfib
      (Kakeya.GlobalPlankFactorization.partBFrostmanConst F.Cw F.Czero) F.Czero :=
    { decomp :=
        { assign := Q.place m
          assign_mem := fun i hi => by
            rw [P.parents_eq]
            exact Finset.mem_image_of_mem _ hi
          leaf_le_parent := fun i hi => by
            change (P.shading i).toTube.toConvexSpaceBody <= _
            rw [P.same_tubes]
            exact Nrm.fine_parent i (P.leaves_subset hi)
          one_le_Cfib := P.Cfib_one
          m_pos := P.n_positive
          fibre_nonempty := P.fibre_nonempty
          le_card_fibre := P.fibre_lower
          card_fibre_le := P.fibre_upper }
      factor := F.factors.toSection6PartBFactorisationFin F.Cw_one F.middle_le_one
        (lt_of_lt_of_le F.short_pos F.short_le_middle) Nrm.parent_pos
        F.factors_nonempty P.parent_ball }
  have hbase : F.Cw * max 1 F.Czero <= H ^ 2 := by
    rw [pow_two]
    exact mul_le_mul' F.Cw_bound (max_le F.bound_one F.Czero_bound)
  have hreading : Kakeya.plankReadingConst F.Cw F.Czero <= 3 * H ^ 2 :=
    (Kakeya.GlobalPlankFactorization.plankReadingConst_le F.Cw_one).trans
      (mul_le_mul' le_rfl hbase)
  refine ⟨{ datum := datum
            assignment_eq := rfl
            factor_eq := rfl
            coarse_fibres_nonempty := ?_
            dimensions := ?_
            capture := ?_
            parent_le_thin := F.factors.le_uniformThin F.factors_nonempty
            aspect := ?_
            frostman_budget := ?_
            dimensions_budget := ?_ }⟩
  · intro j _
    change ((F.factors.toSection6PartBFactorisationFin F.Cw_one F.middle_le_one
      (lt_of_lt_of_le F.short_pos F.short_le_middle) Nrm.parent_pos
      F.factors_nonempty P.parent_ball).coarseFibre j).Nonempty
    rw [Kakeya.GlobalPlankFactorization.coarseFibre_toSection6PartBFactorisationFin]
    exact F.factors.nonempty_of_mem_parts (F.factors.cellEquiv j).2
  · intro j _
    change Kakeya.IsPlankOfDimensions (Kakeya.plankReadingConst F.Cw F.Czero ^ 2)
      F.factors.uniformThin F.factors.uniformMid
      (Kakeya.GlobalPlankFactorization.cellBody (F.factors.cellEquiv j).1 Nrm.parent)
    exact F.factors.isPlankOfDimensions_cellBody_uniform F.Cw_one F.middle_le_one
      F.factors_nonempty (F.factors.cellEquiv j).2
  · intro j _
    change Kakeya.maxDensity P.parents (fun k => (Nrm.parent k).toConvexSpaceBody) <=
      (F.Czero : ENNReal) * Kakeya.densityIn
        ((F.factors.toSection6PartBFactorisationFin F.Cw_one F.middle_le_one
          (lt_of_lt_of_le F.short_pos F.short_le_middle) Nrm.parent_pos
          F.factors_nonempty P.parent_ball).coarseFibre j)
        (fun k => (Nrm.parent k).toConvexSpaceBody)
        (Kakeya.GlobalPlankFactorization.cellBody (F.factors.cellEquiv j).1 Nrm.parent)
    rw [Kakeya.GlobalPlankFactorization.coarseFibre_toSection6PartBFactorisationFin]
    exact F.factors.maxDensity_le_mul (F.factors.cellEquiv j).1 (F.factors.cellEquiv j).2
  · have hmid : 0 < F.factors.uniformMid :=
      Nrm.parent_pos.trans_le ((F.factors.le_uniformThin F.factors_nonempty).trans
        F.factors.uniformThin_le_uniformMid)
    have hmiddle : 0 < F.middle := F.short_pos.trans_le F.short_le_middle
    have hratio : F.factors.uniformThin / F.factors.uniformMid <=
        Kakeya.plankReadingConst F.Cw F.Czero * (F.short / F.middle) := by
      calc
        F.factors.uniformThin / F.factors.uniformMid <=
            (Kakeya.plankReadingConst F.Cw F.Czero * F.short) / F.middle := by
          apply (div_le_div_iff₀ hmid hmiddle).mpr
          simpa only [mul_assoc] using F.factors.uniformThin_mul_le F.Cw_one
            F.middle_le_one F.factors_nonempty
        _ = Kakeya.plankReadingConst F.Cw F.Czero * (F.short / F.middle) :=
          mul_div_assoc _ _ _
    calc
      F.factors.uniformThin / F.factors.uniformMid <=
          Kakeya.plankReadingConst F.Cw F.Czero * (F.short / F.middle) := hratio
      _ <= (3 * H ^ 2) * (H * (aw / bw)) := mul_le_mul' hreading F.aspect
      _ = 3 * H ^ 3 * (aw / bw) := by ring
  · calc
      Kakeya.GlobalPlankFactorization.partBFrostmanConst F.Cw F.Czero <=
          11664 * (F.Cw * max 1 F.Czero) ^ 6 :=
        Kakeya.GlobalPlankFactorization.partBFrostmanConst_le F.Cw_one
      _ <= 11664 * (H ^ 2) ^ 6 := by gcongr
      _ = 11664 * H ^ 12 := by ring
  · calc
      Kakeya.plankReadingConst F.Cw F.Czero ^ 2 <= (3 * H ^ 2) ^ 2 := by gcongr
      _ = 9 * H ^ 4 := by ring

end Kakeya.ML2Core
