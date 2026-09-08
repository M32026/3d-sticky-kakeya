/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectWindowConstruction
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceEccentricNormalization
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceEccentricFactorTransport
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectSelectorAdapters

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

open ML2Assembly

universe u

section

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- All actual analytic inputs on one paid same-Q terminal subfamily. The
displayed mass, fullness and density rows are outputs of the construction. -/
structure SourceEccentricAssignedConstruction (Q : SourceThreadedTower S T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    {a m : Nat} {etaParent bias : Real} {D aw bw cw : NNReal}
    (E : SourceZeroEccentricFactors Q Z a m etaParent bias D aw bw cw)
    (Rnorm : Real) (Cgeom cParent A : NNReal) (p K : Nat) (etaPlank zeta : Real) where
  outer : SourceEccentricOuterSplit Q Z a (sourceEccentricLogLoss K delta)
  outer_normalization : SourceEccentricOuterNormalization Q outer Cgeom
  normalization : SourceEccentricCellNormalization Q outer m Rnorm Cgeom cParent
  selection : SourceEccentricAssignedSelection Q outer normalization E
    (sourceEccentricSelectionCost A p K delta etaPlank zeta)
    (A * delta ^ (-(p : Real) * zeta))
  factor_transport : SourceEccentricFactorTransport Q selection
    (sourceEccentricTransportCost A
      (sourceEccentricSelectionCost A p K delta etaPlank zeta) p delta bias)
  assigned : SourceEccentricAssignedDatum Q factor_transport
  normalized_scale_positive : 0 < sourceEccentricFineScale delta M a
  normalized_scale_lower : 10 * delta <= sourceEccentricFineScale delta M a
  fine_ball : forall i, i ∈ selection.leaves -> (selection.shading i).carrier <= Metric.closedBall 0 1
  fine_density : Kakeya.maxDensity selection.leaves (fun i => (selection.shading i).toConvexSpaceBody) <=
    (A : ENNReal) * (delta : ENNReal) ^ (-etaPlank)
  fine_fullness : delta ^ etaPlank /
    (A * sourceEccentricLogLoss K delta * sourceEccentricSelectionCost A p K delta etaPlank zeta) <=
    ShadedBody.fullness selection.leaves (fun i => (selection.shading i).toShadedBody)
  outer_fullness : delta ^ etaPlank / sourceEccentricLogLoss K delta <=
    ShadedBody.fullness outer.outer (fun i => (outer.outerShade i).toShadedBody)
  card_product : (outer.outer.card : ENNReal) * (selection.leaves.card : ENNReal) <=
    2 * (S.card : ENNReal)
  multiplicity : ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
    (sourceEccentricLogLoss K delta : ENNReal) *
      (sourceEccentricSelectionCost A p K delta etaPlank zeta : ENNReal) *
      ShadedBody.multiplicity outer.outer (fun i => (outer.outerShade i).toShadedBody) *
      ShadedBody.multiplicity selection.leaves (fun i => (selection.shading i).toShadedBody)

end

set_option maxHeartbeats 4000000 in
/-- Direct P geometry constructs the existing full assigned Part-B datum.
The input consists of the one actual ordinary factorization level and the
upper window; retained lower concentration is not an input of this source
alternative. The component GeometryV2 normalization and transport obligations
are still required to construct X. -/
theorem source_exists_direct_plank_construction
    (N M J : Nat) (e : Real) (eta : Nat -> Real) (etaParent : Real)
    (hwindow : SourceZeroWindowSchedule N M J e eta etaParent)
    (D : NNReal) (hD : 1 <= D) :
    exists (Rnorm : Real) (Cgeom cParent A : NNReal) (p K : Nat),
      64 <= Rnorm /\ 1 <= Cgeom /\ 1 <= cParent /\ Cgeom <= A /\
      1 <= A /\ 1 <= p /\ 1 <= K /\
      forall etaPlank zeta : Real, 0 < etaPlank -> etaPlank <= 1 -> 0 < zeta ->
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall bias : Real, 0 < bias -> bias <= min (etaParent / 16) (etaPlank / 8) ->
        forall {iota : Type u} (S : Finset iota)
          (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
          (Q : SourceThreadedTower S T M sourceThreadConstant)
          (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        SourceFixedTowerInput Q sourceBottomED sourceLevelED etaPlank ->
        SourceTowerStatistics Q Z ->
        delta ^ etaPlank <= ShadedBody.fullness S (fun i => (Z i).toShadedBody) ->
        forall (a b m : Nat) (aw bw cw : NNReal),
        SourceParentUpperWindow Q sourceBottomED sourceLevelED N eta e a b J ->
        SourceTowerWindow delta M e a b m ->
        forall P : SourceDirectPlankFactors Q Z a m etaParent bias D aw bw cw,
        exists E : SourceZeroEccentricFactors Q Z a m etaParent bias D aw bw cw,
          (forall j, forall hj : j ∈ Q.indexSet a,
            (E.factor j hj).parts = (P.factor j hj).parts) /\
          exists X : SourceEccentricAssignedConstruction Q Z E
            Rnorm Cgeom cParent A p K etaPlank zeta,
            SourceEccentricScaleBounds delta M e a b m cParent := by
  classical
  have hN : (4 : Real) < N := by exact_mod_cast hwindow.count_bound
  have he : 0 < e := by
    rw [hwindow.window_exponent]
    exact Real.rpow_pos_of_pos (by linarith) _
  have hehalf : e < 1 / 2 := by
    rw [hwindow.window_exponent]
    have h := Real.rpow_lt_rpow_of_neg (by norm_num : (0 : Real) < 4) hN
      (by norm_num : -(1 : Real) / 2 < 0)
    convert h using 1 <;> norm_num [Real.rpow_neg, Real.sqrt_eq_rpow]
  obtain ⟨Cout, Kout, hCout, hKout, hout⟩ :=
    source_exists_eccentric_outer_split M hwindow.level_bound
  obtain ⟨Rnorm, Cin, cParent, hR, hCin, hc, hnorm⟩ :=
    source_exists_eccentric_cell_normalization M hwindow.level_bound e he hehalf
  let Cgeom := max Cout Cin
  have hC : 1 <= Cgeom := hCout.trans (le_max_left _ _)
  have hCo : Cout <= Cgeom := le_max_left _ _
  have hCi : Cin <= Cgeom := le_max_right _ _
  obtain ⟨Asel, psel, K, hCAs, hAs, hps, hKs, hselect⟩ :=
    source_exists_eccentric_ED_assigned_refinement M hwindow.level_bound
      Rnorm hR Cgeom cParent hC hc D hD Kout hKout
  obtain ⟨Afac, pfac, hCAf, hAf, hpf, hfactor⟩ :=
    source_exists_eccentric_factor_transport Rnorm hR Cgeom cParent D hC hc hD
  let A := max Asel Afac
  let p := max psel pfac
  have hAsA : Asel <= A := le_max_left _ _
  have hAfA : Afac <= A := le_max_right _ _
  have hpsp : psel <= p := le_max_left _ _
  have hpfp : pfac <= p := le_max_right _ _
  have hA : 1 <= A := hAs.trans hAsA
  have hp : 1 <= p := hps.trans hpsp
  have hK : 1 <= K := hKout.trans hKs
  refine ⟨Rnorm, Cgeom, cParent, A, p, K, hR, hC, hc,
    hCAs.trans hAsA, hA, hp, hK, ?_⟩
  intro etaPlank zeta heta heta1 hzeta
  filter_upwards [hout, hnorm,
    hselect etaPlank zeta etaParent heta heta1 hzeta hwindow.parent_positive,
    source_eccentric_normalized_scale_bounds M hwindow.level_bound e he hehalf
      cParent (lt_of_lt_of_le zero_lt_one hc),
    Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)] with delta hout hnorm hselect hscale hd
  have hd0 := hd.1
  have hd1 := hd.2.le
  have hlogBase : (1 : Real) <= 2 + Real.logb 2 (1 / (delta : Real)) := by
    have hdReal : 0 < (delta : Real) := by exact_mod_cast hd0
    have h1 : (1 : Real) <= 1 / (delta : Real) :=
      (le_div_iff₀ hdReal).mpr (by simpa only [one_mul] using (show (delta : Real) <= 1 by exact_mod_cast hd1))
    have hlog := Real.logb_nonneg (by norm_num : (1 : Real) < 2) h1
    linarith
  have hLout : 1 <= sourceEccentricLogLoss Kout delta := by
    exact Real.one_le_toNNReal.mpr (one_le_pow₀ hlogBase)
  have hL : 1 <= sourceEccentricLogLoss K delta := by
    exact Real.one_le_toNNReal.mpr (one_le_pow₀ hlogBase)
  have hLmono : sourceEccentricLogLoss Kout delta <= sourceEccentricLogLoss K delta := by
    exact Real.toNNReal_mono (pow_le_pow_right₀ hlogBase hKs)
  let Lsel := sourceEccentricSelectionCost A p K delta etaPlank zeta
  let Lsmall := sourceEccentricSelectionCost Asel psel K delta etaPlank zeta
  have hselOne : 1 <= Lsel := by
    exact one_le_mul (one_le_mul hA hL)
      (NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hd0 hd1
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _))
          (add_nonneg heta.le hzeta.le)))
  have hsmallOne : 1 <= Lsmall := by
    exact one_le_mul (one_le_mul hAs hL)
      (NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hd0 hd1
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _))
          (add_nonneg heta.le hzeta.le)))
  have hselMono : Lsmall <= Lsel := by
    exact mul_le_mul' (mul_le_mul' hAsA le_rfl)
      (NNReal.rpow_le_rpow_of_exponent_ge hd0 hd1
        (mul_le_mul_of_nonneg_right (neg_le_neg (by exact_mod_cast hpsp))
          (add_nonneg heta.le hzeta.le)))
  have hcountMono : Asel * delta ^ (-(psel : Real) * zeta) <=
      A * delta ^ (-(p : Real) * zeta) := by
    exact mul_le_mul' hAsA (NNReal.rpow_le_rpow_of_exponent_ge hd0 hd1
      (mul_le_mul_of_nonneg_right (neg_le_neg (by exact_mod_cast hpsp)) hzeta.le))
  intro bias hbias hbiasBound iota S T Q Z hinput hstats hfull a b m aw bw cw hupper hwindowM Pdirect
  obtain ⟨hconstant, E, hparts⟩ := source_direct_plank_eccentric_data Q Z Pdirect
  refine ⟨E, hparts, ?_⟩
  have scales := hscale a b m hupper.fine_bound hupper.separation hwindowM
  have haM : a < M := scales.outer_lt_middle.trans (scales.middle_lt_inner.trans_le scales.inner_bound)
  have hmM : m < M := scales.middle_lt_inner.trans_le scales.inner_bound
  obtain ⟨O0, ⟨ON0⟩⟩ := hout S T Q Z hinput.geometry hstats E.shade_floor a haM
  obtain ⟨N0⟩ := hnorm S T Q Z hinput.geometry a b m
    (sourceEccentricLogLoss Kout delta) scales O0
  let Nrm0 : SourceEccentricCellNormalization Q O0 m Rnorm Cgeom cParent :=
    { N0 with
      comparison_one := hC
      outer_replacement_cost := N0.outer_replacement_cost.trans hCi
      fine_volume := fun i hi => (N0.fine_volume i hi).trans (by gcongr)
      parent_volume := fun k hk => (N0.parent_volume k hk).trans (by gcongr)
      fullness := (by gcongr : _ <= _).trans N0.fullness
      maximal_density := N0.maximal_density.trans (by gcongr)
      part_volume_upper := fun part hn hp => (N0.part_volume_upper part hn hp).trans (by gcongr)
      part_thickness_lower := fun part hn hp rank hr =>
        (by gcongr : _ <= _).trans (N0.part_thickness_lower part hn hp rank hr)
      part_thickness_upper := fun part hn hp rank hr =>
        (N0.part_thickness_upper part hn hp rank hr).trans (by gcongr) }
  obtain ⟨P0⟩ := hselect bias hbias hbiasBound S T Q Z hinput hstats hfull
    a m aw bw cw hmM O0 Nrm0 E
  have hLoutPos : 0 < sourceEccentricLogLoss Kout delta := zero_lt_one.trans_le hLout
  have hSmallPos : 0 < Lsmall := zero_lt_one.trans_le hsmallOne
  let O : SourceEccentricOuterSplit Q Z a (sourceEccentricLogLoss K delta) :=
    { O0 with
      fine_refinement := ShadedBody.IsCRefinement.mono (by gcongr) O0.fine_refinement
      refined_mass := O0.refined_mass.trans (by gcongr)
      outer_fullness := (by gcongr : _ <= _).trans O0.outer_fullness
      inner_fullness := (by gcongr : _ <= _).trans O0.inner_fullness
      split_multiplicity := O0.split_multiplicity.trans (by gcongr) }
  let ON : SourceEccentricOuterNormalization Q O Cgeom :=
    { ON0 with
      volume_comparison := fun i hi => (ON0.volume_comparison i hi).trans (by gcongr)
      fullness := (by gcongr : _ <= _).trans ON0.fullness
      maximal_density := ON0.maximal_density.trans (by gcongr) }
  let Nrm : SourceEccentricCellNormalization Q O m Rnorm Cgeom cParent :=
    { Nrm0 with affine := Nrm0.affine }
  let P : SourceEccentricAssignedSelection Q O Nrm E Lsel
      (A * delta ^ (-(p : Real) * zeta)) :=
    { P0 with
      refinement := ShadedBody.IsCRefinement.mono (by gcongr) P0.refinement
      mass := P0.mass.trans (by gcongr)
      fullness := (by gcongr : _ <= _).trans P0.fullness
      multiplicity := P0.multiplicity.trans (by gcongr)
      Cfib_bound := P0.Cfib_bound.trans hcountMono
      part_retention_bound := P0.part_retention_bound.trans hselMono
      part_mass_retention := fun part hp => (P0.part_mass_retention part hp).trans (by gcongr) }
  obtain ⟨F0⟩ := hfactor hd0 hd1 S T M sourceThreadConstant Q Z a m
    (sourceEccentricLogLoss K delta) etaParent bias aw bw cw hbias O Nrm E
    Lsel (A * delta ^ (-(p : Real) * zeta)) hselOne P
  have hB : 1 <= sourceZeroPlankConstant delta bias := by
    apply one_le_mul
    · apply Real.one_le_toNNReal.mpr
      have h3 : (1 : Real) <= 3 ^ ((9 : Real) / 2) :=
        Real.one_le_rpow (by norm_num) (by norm_num)
      nlinarith only [h3]
    · exact NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hd0 hd1
        (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hbias.le)
  let H := sourceEccentricTransportCost A Lsel p delta bias
  have hH : sourceEccentricTransportCost Afac Lsel pfac delta bias <= H := by
    exact mul_le_mul' (mul_le_mul' hAfA (pow_le_pow_right₀ hselOne hpfp))
      (pow_le_pow_right₀ hB hpfp)
  let F : SourceEccentricFactorTransport Q P H :=
    { F0 with
      bound_one := F0.bound_one.trans hH
      Cw_bound := F0.Cw_bound.trans hH
      Czero_bound := F0.Czero_bound.trans hH
      aspect := F0.aspect.trans (by gcongr)
      dimensions := fun part hp => by
        rcases F0.dimensions part hp with ⟨hl0, hu0, hl1, hu1, hl2, hu2⟩
        exact ⟨(by gcongr : _ <= _).trans hl0, hu0.trans (by gcongr),
          (by gcongr : _ <= _).trans hl1, hu1.trans (by gcongr),
          (by gcongr : _ <= _).trans hl2, hu2.trans (by gcongr)⟩
      old_hull_volume := fun part hp => (F0.old_hull_volume part hp).trans (by gcongr)
      new_hull_volume := fun part hp => (F0.new_hull_volume part hp).trans (by gcongr)
      original_test_body := fun V => by
        obtain ⟨W, hW, hcover⟩ := F0.original_test_body V
        exact ⟨W, hW.trans (by gcongr), hcover⟩ }
  obtain ⟨datum⟩ := source_exists_eccentric_assigned_partB_datum Q F
  refine ⟨{ outer := O
            outer_normalization := ON
            normalization := Nrm
            selection := P
            factor_transport := F
            assigned := datum
            normalized_scale_positive := scales.fine_positive
            normalized_scale_lower := scales.fine_global_lower
            fine_ball := ?_
            fine_density := ?_
            fine_fullness := ?_
            outer_fullness := ?_
            card_product := ?_
            multiplicity := ?_ }, scales⟩
  · intro i hi
    change (P.shading i).toTube.carrier <= _
    rw [P.same_tubes]
    exact (Nrm.fine_ball i (P.leaves_subset hi)).trans
      (Metric.closedBall_subset_closedBall (by norm_num))
  · have hbody : forall i, (P.shading i).toConvexSpaceBody =
        (Nrm.fine i).toConvexSpaceBody := fun i =>
      congrArg Tube.toConvexSpaceBody (P.same_tubes i)
    rw [Kakeya.maxDensity_congr (fun i _ => hbody i)]
    calc
      Kakeya.maxDensity P.leaves (fun i => (Nrm.fine i).toConvexSpaceBody) <=
          Kakeya.maxDensity (Q.cell a O.chosen) (fun i => (Nrm.fine i).toConvexSpaceBody) :=
        Kakeya.maxDensity_mono _ P.leaves_subset
      _ <= (Cgeom : ENNReal) * Kakeya.maxDensity S (fun i => (T i).toConvexSpaceBody) :=
        Nrm.maximal_density.trans (by
          gcongr
          exact Kakeya.maxDensity_mono _ (Finset.filter_subset _ _))
      _ <= (A : ENNReal) * (delta : ENNReal) ^ (-etaPlank) := by
        have hpow : ENNReal.ofReal ((delta : Real) ^ (-etaPlank)) =
            (delta : ENNReal) ^ (-etaPlank) := by
          rw [← ENNReal.ofReal_rpow_of_pos (show (0 : Real) < delta by exact_mod_cast hd0)]
          simp only [ENNReal.ofReal_coe_nnreal]
        exact mul_le_mul' (by exact_mod_cast hCAs.trans hAsA)
          (hinput.maximal_density.trans_eq hpow)
  · calc
      delta ^ etaPlank / (A * sourceEccentricLogLoss K delta * Lsel) <=
          delta ^ etaPlank / (Cgeom * sourceEccentricLogLoss K delta * Lsel) := by
        gcongr
        exact hCAs.trans hAsA
      _ = ((delta ^ etaPlank / sourceEccentricLogLoss K delta) / Cgeom) / Lsel := by
        simp only [div_div, mul_comm Cgeom]
      _ <= ((ShadedBody.fullness S (fun i => (Z i).toShadedBody) /
          sourceEccentricLogLoss K delta) / Cgeom) / Lsel := by gcongr
      _ <= (ShadedBody.fullness (Q.cell a O.chosen)
          (fun i => (O.innerShade i).toShadedBody) / Cgeom) / Lsel := by
        gcongr
        exact O.inner_fullness
      _ <= ShadedBody.fullness (Q.cell a O.chosen)
          (fun i => (Nrm.fine i).toShadedBody) / Lsel := by
        gcongr
        exact Nrm.fullness
      _ <= ShadedBody.fullness P.leaves (fun i => (P.shading i).toShadedBody) := P.fullness
  · exact (by gcongr : delta ^ etaPlank / sourceEccentricLogLoss K delta <=
      ShadedBody.fullness S (fun i => (Z i).toShadedBody) /
        sourceEccentricLogLoss K delta).trans O.outer_fullness
  · exact (mul_le_mul_right (by exact_mod_cast Finset.card_le_card P.leaves_subset)
      (O.outer.card : ENNReal)).trans O.card_product
  · calc
      ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
          (sourceEccentricLogLoss K delta : ENNReal) *
            ShadedBody.multiplicity O.outer (fun i => (O.outerShade i).toShadedBody) *
            ShadedBody.multiplicity (Q.cell a O.chosen)
              (fun i => (Nrm.fine i).toShadedBody) := by
        rw [Nrm.multiplicity]
        exact O.split_multiplicity
      _ <= (sourceEccentricLogLoss K delta : ENNReal) *
            ShadedBody.multiplicity O.outer (fun i => (O.outerShade i).toShadedBody) *
            ((Lsel : ENNReal) * ShadedBody.multiplicity P.leaves
              (fun i => (P.shading i).toShadedBody)) := by
        gcongr
        exact P.multiplicity
      _ = _ := by ring

set_option maxHeartbeats 4000000 in
/-- The source P estimate, with the exact ordinary coefficient and one fixed
comparison D. This is the reviewed zero-defect analytic use; it does not
erase the positive omega factor of the distinct defect theorem. -/
theorem source_exists_direct_plank_exit
    {beta etaParent nuPlank kappa : Real}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace Real (Fin 3)) beta)
    (hF : FrostmanEstimate.{u} (EuclideanSpace Real (Fin 3)) beta)
    (hparent : 0 < etaParent) (hnu : 0 < nuPlank)
    (hnu_upper : nuPlank <= etaParent * beta / 4)
    (hkappa : 0 <= kappa) (hdensity_budget : kappa * (1 - beta) <= nuPlank / 4)
    (N M J : Nat) (e : Real) (eta : Nat -> Real)
    (hwindow : SourceZeroWindowSchedule N M J e eta etaParent)
    (D : NNReal) (hD : 1 <= D) :
    exists (etaPlank : Real) (K : Nat), 0 < etaPlank /\ 1 <= K /\
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall bias : Real, 0 < bias ->
        bias <= min (etaParent / 16) (etaPlank / 8) ->
        forall {iota : Type u} (S : Finset iota)
          (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
          (Q : SourceThreadedTower S T M sourceThreadConstant)
          (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        SourceFixedTowerInput Q sourceBottomED sourceLevelED etaPlank ->
        SourceTowerStatistics Q Z ->
        delta ^ etaPlank <= ShadedBody.fullness S (fun i => (Z i).toShadedBody) ->
        forall (a b m : Nat) (aw bw cw : NNReal),
        SourceParentUpperWindow Q sourceBottomED sourceLevelED N eta e a b J ->
        SourceTowerWindow delta M e a b m ->
        SourceDirectPlankFactors Q Z a m etaParent bias D aw bw cw ->
        Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) <=
          (delta : ENNReal) ^ (-kappa) ->
        (sourceParentPlankConstant delta bias : ENNReal) <= (delta : ENNReal) ^ (-etaPlank) /\
        ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
          sourceFixedPreparationLoss K delta * (delta : ENNReal) ^ nuPlank *
            (S.card : ENNReal) ^ beta := by
  classical
  have hN : (4 : Real) < N := by exact_mod_cast hwindow.count_bound
  have he : 0 < e := by
    rw [hwindow.window_exponent]
    exact Real.rpow_pos_of_pos (by linarith) _
  have hehalf : e < 1 / 2 := by
    rw [hwindow.window_exponent]
    have h := Real.rpow_lt_rpow_of_neg (by norm_num : (0 : Real) < 4) hN
      (by norm_num : -(1 : Real) / 2 < 0)
    convert h using 1 <;> norm_num [Real.rpow_neg, Real.sqrt_eq_rpow]
  let G := etaParent * beta
  have hG : 0 < G := mul_pos hparent hbeta0
  obtain ⟨Rnorm, Cgeom, cParent, A, p, K, hR, hC, hc, hCA, hA, hp, hK, hconstruct⟩ :=
    source_exists_direct_plank_construction N M J e eta etaParent hwindow D hD
  obtain ⟨eta66, h66, sigma0, hsigma0, hsigma1, hpartB⟩ :=
    source_prop66B_of_assigned_coarse_data.{u, u, u}
      hbeta0 hbeta1 hKT (show 0 < e / 2 by positivity)
      (show e / 2 <= 1 by linarith) (G / 64) (by positivity)
  obtain ⟨etaOuter, hOuter, houter⟩ := source_exists_eccentric_outer_estimate
    hbeta0 hbeta1 hKT M hwindow.level_bound Cgeom hC (G / 64) (by positivity)
  obtain ⟨etaPlank, zeta, hetaPlank, heta1, hzeta, hledger⟩ :=
    source_exists_eccentric_fixed_loss_ledger hbeta0 hbeta1 hG he hehalf h66 hOuter
      A hA p K hp hK
  let C0 : NNReal := Real.toNNReal (4 * (3 : Real) ^ ((9 : Real) / 2) * 2 ^ 6)
  obtain ⟨d0, hd0, hd01, hconst⟩ := ML2Shaded.exists_threshold_const_le_rpow_neg'
    (C0 : Real) (show 0 < etaPlank / 2 by positivity)
  have hcut : (0 : NNReal) < sigma0 ^ (1 / e) := by positivity
  refine ⟨etaPlank, K, hetaPlank, hK, ?_⟩
  filter_upwards [hconstruct etaPlank zeta hetaPlank heta1 hzeta, houter, hledger,
    Ioo_mem_nhdsGT hd0, Ioo_mem_nhdsGT hcut] with delta hconstruct houter hledger hd hdcut
  intro bias hbias hbiasUpper iota S T Q Z hinput hstats hfull a b m aw bw cw
    hupper hwindowM P houterDensity
  have hdeltapos := hd.1
  have hdelta0 : (delta : ENNReal) ≠ 0 := by exact_mod_cast hd.1.ne'
  have hdeltaTop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hdelta1 : delta <= 1 := hd.2.le.trans hd01
  have hdelta1E : (delta : ENNReal) <= 1 := by exact_mod_cast hdelta1
  have hC0 : (C0 : ENNReal) <= (delta : ENNReal) ^ (-(etaPlank / 2)) := by
    have hc := hconst hd.1 hd.2.le
    have hnn : C0 <= delta ^ (-(etaPlank / 2)) := by exact_mod_cast hc
    have hcoe := ENNReal.coe_le_coe.mpr hnn
    simpa only [ENNReal.coe_rpow_of_ne_zero hd.1.ne'] using hcoe
  have hCP : (sourceParentPlankConstant delta bias : ENNReal) <=
      (delta : ENNReal) ^ (-etaPlank) := by
    change ((C0 * delta ^ (-3 * bias) : NNReal) : ENNReal) <= _
    rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hd.1.ne']
    calc (C0 : ENNReal) * (delta : ENNReal) ^ (-3 * bias) <=
          (delta : ENNReal) ^ (-(etaPlank / 2)) * (delta : ENNReal) ^ (-3 * bias) :=
            mul_le_mul' hC0 le_rfl
      _ = (delta : ENNReal) ^ (-(etaPlank / 2) + -3 * bias) :=
        (ENNReal.rpow_add _ _ hdelta0 hdeltaTop).symm
      _ <= (delta : ENNReal) ^ (-etaPlank) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hdelta1E
          (by have := hbiasUpper.trans (min_le_right _ _); linarith only [this, hetaPlank])
  obtain ⟨E, hparts, X, scales⟩ := hconstruct bias hbias hbiasUpper S T Q Z
    hinput hstats hfull a b m aw bw cw hupper hwindowM P
  let sigma := sourceEccentricFineScale delta M a
  let L := sourceEccentricSelectionCost A p K delta etaPlank zeta
  let H := sourceEccentricTransportCost A L p delta bias
  have hsigma : sigma <= sigma0 := by
    have hpow := NNReal.rpow_le_rpow hdcut.2.le he.le
    rw [← NNReal.rpow_mul, one_div_mul_cancel he.ne', NNReal.rpow_one] at hpow
    exact scales.fine_global_upper.trans ((div_le_self (by positivity) (by norm_num)).trans hpow)
  obtain ⟨hL, hH, hcost, hcount, hCF, hdim, hfinefull, houterfull, hscalar⟩ :=
    hledger bias hbias (hbiasUpper.trans (min_le_right _ _)) sigma
      scales.fine_global_lower scales.fine_global_upper
  have hB := hpartB X.selection.leaves scales.fine_positive X.selection.shading hsigma
    X.fine_ball X.selection.essentially_distinct (hfinefull.trans X.fine_fullness)
    (sourceEccentricParentScale delta M a m cParent)
    X.factor_transport.factors.uniformThin X.factor_transport.factors.uniformMid
    X.factor_transport.factors.uniformThin_le_uniformMid
    (X.factor_transport.factors.uniformMid_le_one X.selection.parent_ball)
    X.selection.parents X.normalization.parent X.selection.n X.selection.Cfib
    (Kakeya.GlobalPlankFactorization.partBFrostmanConst X.factor_transport.Cw X.factor_transport.Czero)
    X.factor_transport.Czero (Kakeya.plankReadingConst X.factor_transport.Cw X.factor_transport.Czero ^ 2)
    (X.factor_transport.Czero_bound.trans hcost) (X.assigned.frostman_budget.trans hCF)
    (X.selection.Cfib_bound.trans hcount) (X.assigned.dimensions_budget.trans hdim)
    scales.coarse_scale_lower X.assigned.parent_le_thin X.assigned.datum
    X.assigned.coarse_fibres_nonempty X.assigned.dimensions X.assigned.capture
  have hO := houter S T Q Z hinput.geometry a (sourceEccentricLogLoss K delta)
    (scales.outer_lt_middle.trans (scales.middle_lt_inner.trans_le scales.inner_bound))
    X.outer X.outer_normalization (houterfull.trans X.outer_fullness)
  have haspect : (X.factor_transport.factors.uniformThin : ENNReal) /
      (X.factor_transport.factors.uniformMid : ENNReal) <=
      3 * (H : ENNReal) ^ 3 * ((aw : ENNReal) / (bw : ENNReal)) := by
    have hbpos : 0 < bw := P.short_positive.trans_le P.short_le_middle
    have hmidpos : 0 < X.factor_transport.factors.uniformMid :=
      scales.parent_positive.trans_le (X.assigned.parent_le_thin.trans
        X.factor_transport.factors.uniformThin_le_uniformMid)
    have hh := ENNReal.coe_le_coe.mpr X.assigned.aspect
    simpa only [ENNReal.coe_div hmidpos.ne', ENNReal.coe_mul, ENNReal.coe_pow,
      ENNReal.coe_ofNat, ENNReal.coe_div hbpos.ne'] using hh
  have hinner : ShadedBody.multiplicity X.selection.leaves
      (fun i => (X.selection.shading i).toShadedBody) <=
      (sigma : ENNReal) ^ (-(G / 64)) *
        ((A : ENNReal) * (delta : ENNReal) ^ (-etaPlank)) ^ (1 - beta) *
        (3 * (H : ENNReal) ^ 3) ^ beta *
        ((aw : ENNReal) / (bw : ENNReal)) ^ beta *
        (X.selection.leaves.card : ENNReal) ^ beta := by
    calc _ <= (sigma : ENNReal) ^ (-(G / 64)) *
          ((A : ENNReal) * (delta : ENNReal) ^ (-etaPlank)) ^ (1 - beta) *
          (3 * (H : ENNReal) ^ 3 * ((aw : ENNReal) / (bw : ENNReal))) ^ beta *
          (X.selection.leaves.card : ENNReal) ^ beta := by
            exact hB.trans (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl
              (ENNReal.rpow_le_rpow X.fine_density (sub_nonneg.mpr hbeta1)))
              (ENNReal.rpow_le_rpow haspect hbeta0.le)) le_rfl)
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hbeta0.le]; ring
  have hcard : (X.outer.outer.card : ENNReal) ^ beta *
      (X.selection.leaves.card : ENNReal) ^ beta <=
      (2 : ENNReal) ^ beta * (S.card : ENNReal) ^ beta := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hbeta0.le,
      ← ENNReal.mul_rpow_of_nonneg _ _ hbeta0.le]
    exact ENNReal.rpow_le_rpow X.card_product hbeta0.le
  have hraw : ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
      (delta : ENNReal) ^ (-(G / 2)) *
        Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) ^
          (1 - beta) * ((aw : ENNReal) / (bw : ENNReal)) ^ beta *
        (S.card : ENNReal) ^ beta := by
    calc _ <= (sourceEccentricLogLoss K delta : ENNReal) * (L : ENNReal) *
        ((delta : ENNReal) ^ (-(G / 64)) *
          Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) ^
            (1 - beta) * (X.outer.outer.card : ENNReal) ^ beta) *
        ((sigma : ENNReal) ^ (-(G / 64)) *
          ((A : ENNReal) * (delta : ENNReal) ^ (-etaPlank)) ^ (1 - beta) *
          (3 * (H : ENNReal) ^ 3) ^ beta *
          ((aw : ENNReal) / (bw : ENNReal)) ^ beta *
          (X.selection.leaves.card : ENNReal) ^ beta) :=
            X.multiplicity.trans (mul_le_mul' (mul_le_mul' le_rfl hO) hinner)
      _ = ((sourceEccentricLogLoss K delta : ENNReal) * (L : ENNReal) *
          (delta : ENNReal) ^ (-(G / 64)) * (sigma : ENNReal) ^ (-(G / 64)) *
          ((A : ENNReal) * (delta : ENNReal) ^ (-etaPlank)) ^ (1 - beta) *
          (3 * (H : ENNReal) ^ 3) ^ beta) *
          Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) ^
            (1 - beta) * ((aw : ENNReal) / (bw : ENNReal)) ^ beta *
          ((X.outer.outer.card : ENNReal) ^ beta *
            (X.selection.leaves.card : ENNReal) ^ beta) := by ring
      _ <= ((sourceEccentricLogLoss K delta : ENNReal) * (L : ENNReal) *
          (delta : ENNReal) ^ (-(G / 64)) * (sigma : ENNReal) ^ (-(G / 64)) *
          ((A : ENNReal) * (delta : ENNReal) ^ (-etaPlank)) ^ (1 - beta) *
          (3 * (H : ENNReal) ^ 3) ^ beta) *
          Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) ^
            (1 - beta) * ((aw : ENNReal) / (bw : ENNReal)) ^ beta *
          ((2 : ENNReal) ^ beta * (S.card : ENNReal) ^ beta) := by gcongr
      _ = ((sourceEccentricLogLoss K delta : ENNReal) * (L : ENNReal) *
          (delta : ENNReal) ^ (-(G / 64)) * (sigma : ENNReal) ^ (-(G / 64)) *
          ((A : ENNReal) * (delta : ENNReal) ^ (-etaPlank)) ^ (1 - beta) *
          (3 * (H : ENNReal) ^ 3) ^ beta * (2 : ENNReal) ^ beta) *
          Kakeya.maxDensity (Q.indexSet a) (fun i => (Q.tube a i).toConvexSpaceBody) ^
            (1 - beta) * ((aw : ENNReal) / (bw : ENNReal)) ^ beta *
          (S.card : ENNReal) ^ beta := by ring
      _ <= _ := mul_le_mul' (mul_le_mul' (mul_le_mul' hscalar le_rfl) le_rfl) le_rfl
  have hratio : (aw : ENNReal) / (bw : ENNReal) <= (delta : ENNReal) ^ etaParent := by
    have hcoe := ENNReal.coe_le_coe.mpr P.eccentric
    simpa only [ENNReal.coe_div (P.short_positive.trans_le P.short_le_middle).ne',
      ENNReal.coe_rpow_of_ne_zero hd.1.ne'] using hcoe
  have hgain : ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
      (delta : ENNReal) ^ nuPlank * (S.card : ENNReal) ^ beta := by
    calc _ <= (delta : ENNReal) ^ (-(G / 2)) *
          ((delta : ENNReal) ^ (-kappa)) ^ (1 - beta) *
          ((delta : ENNReal) ^ etaParent) ^ beta * (S.card : ENNReal) ^ beta :=
            hraw.trans (mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl
              (ENNReal.rpow_le_rpow houterDensity (sub_nonneg.mpr hbeta1)))
              (ENNReal.rpow_le_rpow hratio hbeta0.le)) le_rfl)
      _ = (delta : ENNReal) ^ (etaParent * beta / 2 - kappa * (1 - beta)) *
          (S.card : ENNReal) ^ beta := by
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_add _ _ hdelta0 hdeltaTop,
          ← ENNReal.rpow_add _ _ hdelta0 hdeltaTop]
        dsimp [G]
        congr 2 <;> ring
      _ <= _ := mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hdelta1E
        (by nlinarith only [hnu_upper, hdensity_budget, hnu])) le_rfl
  refine ⟨hCP, hgain.trans ?_⟩
  have hLone : 1 <= sourceFixedPreparationLoss K delta := by
    change 1 <= (sourceEccentricLogLoss K delta : ENNReal)
    apply ENNReal.coe_le_coe.mpr
    apply Real.one_le_toNNReal.mpr
    apply one_le_pow₀
    have hdReal : 0 < (delta : Real) := by exact_mod_cast hd.1
    have h1 : (1 : Real) <= 1 / (delta : Real) :=
      (le_div_iff₀ hdReal).mpr (by simpa only [one_mul] using
        (show (delta : Real) <= 1 by exact_mod_cast hdelta1))
    have := Real.logb_nonneg (by norm_num : (1 : Real) < 2) h1
    linarith
  simpa only [one_mul] using mul_le_mul' (mul_le_mul' hLone
    (le_refl ((delta : ENNReal) ^ nuPlank))) (le_refl ((S.card : ENNReal) ^ beta))

end Kakeya.ML2Core
