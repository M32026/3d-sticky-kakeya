/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceStickyInterpolation

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

/-- A finite reindexing includes every occupied leaf and every grid node. It
preserves the actual SSF hierarchy, shading and all quantities used by Sticky. -/
structure SourceStickyFiniteReindex {iota : Type u} {delta Cu : NNReal}
    (R : Finset iota) (W : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (U : ShadedUniformTubeSet R W (ssfGridLen delta) Cu) where
  size : Nat
  decode : Fin size -> iota
  decode_injective : Function.Injective decode
  support : Finset (Fin size)
  shading : Fin size -> ShadedTube delta (EuclideanSpace Real (Fin 3))
  uniform : ShadedUniformTubeSet support shading (ssfGridLen delta) Cu
  support_identity : (open scoped Classical in support.image decode) = R
  shading_identity : ∀ j, shading j = W (decode j)
  nodes_identity : ∀ k, k <= ssfGridLen delta ->
    (open scoped Classical in (uniform.tubeUniform.cover.indexSet k).image decode) =
      U.tubeUniform.cover.indexSet k
  assignment_identity : ∀ k, k <= ssfGridLen delta -> ∀ j ∈ support,
    decode (uniform.tubeUniform.cover.assign k j) = U.tubeUniform.cover.assign k (decode j)
  node_tube_identity : ∀ k, k <= ssfGridLen delta ->
    ∀ j ∈ uniform.tubeUniform.cover.indexSet k,
      uniform.tubeUniform.cover.tube k j = U.tubeUniform.cover.tube k (decode j)
  tube_branching_identity : uniform.tubeUniform.branchingN = U.tubeUniform.branchingN
  shade_branching_identity : uniform.branchingN = U.branchingN
  local_branching_identity : uniform.localN = U.localN
  cardinality_identity : support.card = R.card
  mass_identity : (∑ j ∈ support, volume (shading j).shade) = ∑ i ∈ R, volume (W i).shade
  union_identity : (⋃ j ∈ support, (shading j).shade) = (⋃ i ∈ R, (W i).shade)
  fullness_identity : ShadedBody.fullness' support (fun j => (shading j).toShadedBody) =
    ShadedBody.fullness' R (fun i => (W i).toShadedBody)
  multiplicity_identity : ShadedBody.multiplicity support (fun j => (shading j).toShadedBody) =
    ShadedBody.multiplicity R (fun i => (W i).toShadedBody)
  density_identity : Kakeya.maxDensity support (fun j => (shading j).toConvexSpaceBody) =
    Kakeya.maxDensity R (fun i => (W i).toConvexSpaceBody)
  every_scale_identity : ∀ A : ENNReal,
    uniform.tubeUniform.IsKatzTaoAtEveryScale A ↔ U.tubeUniform.IsKatzTaoAtEveryScale A

theorem source_exists_sticky_finite_reindex {iota : Type u} {delta Cu : NNReal}
    (R : Finset iota) (W : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (U : ShadedUniformTubeSet R W (ssfGridLen delta) Cu) :
    Nonempty (SourceStickyFiniteReindex R W U) := by
  classical
  let F : Finset iota := R ∪ (Finset.range (ssfGridLen delta + 1)).biUnion
    (fun k => U.tubeUniform.cover.indexSet k)
  have hRF : R <= F := Finset.subset_union_left
  have hidx : ∀ k, k <= ssfGridLen delta -> U.tubeUniform.cover.indexSet k <= F := by
    intro k hk
    exact (Finset.subset_biUnion_of_mem _ (Finset.mem_range.mpr (by omega))).trans
      Finset.subset_union_right
  rcases F.eq_empty_or_nonempty with hFe | ⟨i0, hi0⟩
  · have hRe : R = ∅ := Finset.subset_empty.mp (hFe ▸ hRF)
    have hnode : ∀ k, k <= ssfGridLen delta -> U.tubeUniform.cover.indexSet k = ∅ :=
      fun k hk => Finset.subset_empty.mp (hFe ▸ hidx k hk)
    let dec : Fin 0 -> iota := Fin.elim0
    let V : Fin 0 -> ShadedTube delta (EuclideanSpace Real (Fin 3)) := fun j => W (dec j)
    let G : GridCoverSystem (∅ : Finset (Fin 0)) (fun j => (V j).toTube) (ssfGridLen delta) := {
      indexSet := fun _ => ∅
      assign := fun _ j => j
      tube := fun _ j => Fin.elim0 j
      assign_mem := by simp
      le_tube_assign := by simp
      nested := by simp
      tube_nested := by simp
    }
    let Ut : UniformTubeSet (∅ : Finset (Fin 0)) (fun j => (V j).toTube) (ssfGridLen delta) Cu := {
      cover := G
      branchingN := U.tubeUniform.branchingN
      tube_injOn := fun _ _ j => Fin.elim0 j
      boundedOverlap := by simp [G]
      card_class_le := by simp [G]
      le_card_class := by simp [G]
    }
    let U' : ShadedUniformTubeSet (∅ : Finset (Fin 0)) V (ssfGridLen delta) Cu := {
      tubeUniform := Ut
      branchingN := U.branchingN
      localN := U.localN
      card_shadeClass_le := by simp
      le_card_shadeClass := by simp
      branchingN_le := by simp
      le_branchingN := by simp
    }
    refine ⟨⟨0, dec, fun i => Fin.elim0 i, ∅, V, U', ?_, fun _ => rfl, ?_, ?_, ?_,
      rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simp [hRe]
    · intro k hk
      simp [U', Ut, G, hnode k hk]
    · simp
    · intro k hk j
      exact Fin.elim0 j
    · simp [hRe]
    · simp [hRe]
    · simp [hRe]
    · simp [hRe, ShadedBody.fullness']
    · simp [hRe, ShadedBody.multiplicity]
    · simp [hRe, Kakeya.maxDensity_empty]
    · intro A
      simp [UniformTubeSet.IsKatzTaoAtEveryScale, U', Ut, G, hnode, Kakeya.maxDensity_empty]
      intro k hk
      simp [hnode k hk, Kakeya.maxDensity_empty]
  · let E := Kakeya.Reindex.Retract.ofFinset F i0 hi0
    have himage : ∀ S : Finset iota, S <= F -> (E.idx S).image E.toFun = S := by
      intro S hS
      ext i
      constructor
      · rintro hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        exact (Kakeya.Reindex.Retract.mem_idx hS).mp hj
      · intro hi
        exact Finset.mem_image.mpr ⟨E.invFun i, Kakeya.Reindex.Retract.invFun_mem_idx hi,
          E.right_inv i (hS hi)⟩
    let V : Fin F.card -> ShadedTube delta (EuclideanSpace Real (Fin 3)) := fun j => W (E.toFun j)
    let U' := E.shadedUniformTubeSet U hRF hidx
    refine ⟨⟨F.card, E.toFun, E.toFun_injective, E.idx R, V, U', himage R hRF,
      fun _ => rfl, ?_, ?_, fun _ _ _ _ => rfl, rfl, rfl, rfl,
      Kakeya.Reindex.Retract.card_idx hRF,
      Kakeya.Reindex.Retract.sum_idx hRF (fun i => volume (W i).shade),
      Kakeya.Reindex.Retract.biUnion_idx hRF (fun i => (W i).shade),
      Kakeya.Reindex.Retract.fullness'_idx hRF (fun i => (W i).toShadedBody),
      Kakeya.Reindex.Retract.multiplicity_idx hRF (fun i => (W i).toShadedBody),
      Kakeya.Reindex.Retract.maxDensity_idx hRF (fun i => (W i).toConvexSpaceBody), ?_⟩⟩
    · intro k hk
      exact himage _ (hidx k hk)
    · intro k hk j hj
      exact E.right_inv _ (hidx k hk
        (U.tubeUniform.cover.assign_mem k hk _ ((Kakeya.Reindex.Retract.mem_idx hRF).mp hj)))
    · intro A
      constructor
      · intro h k hk
        have hh := h k hk
        change Kakeya.maxDensity (E.idx (U.tubeUniform.cover.indexSet k))
          (fun j => (U.tubeUniform.cover.tube k (E.toFun j)).toConvexSpaceBody) <= A at hh
        rwa [Kakeya.Reindex.Retract.maxDensity_idx (R := E) (hidx k hk)
          (fun j => (U.tubeUniform.cover.tube k j).toConvexSpaceBody)] at hh
      · exact Kakeya.Reindex.Retract.isKatzTaoAtEveryScale_idx U.tubeUniform hRF hidx

/-- A literal parameter choice ed SSF Katz--Tao consequence.
This proposition is an OUTPUT of the parameter producer, never a new axiom. -/
def SourceRecordedStickyParameters (eps eta delta0 : Real) : Prop :=
  ∀ {delta : NNReal}, 0 < delta -> (delta : Real) <= delta0 ->
  ∀ {iota : Type u} (R : Finset iota)
    (W : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
    (∀ i ∈ R, (W i).carrier <= Metric.closedBall 0 1) ->
  ∀ {Cu : NNReal} (U : ShadedUniformTubeSet R W (ssfGridLen delta) Cu),
    ENNReal.ofReal ((delta : Real) ^ eta) <=
      ShadedBody.fullness' R (fun i => (W i).toShadedBody) ->
    ConvexSpaceBody.IsKatzTao R (fun i => (W i).toConvexSpaceBody)
      (ENNReal.ofReal ((delta : Real) ^ (-eta))) ->
    U.tubeUniform.IsKatzTaoAtEveryScale (ENNReal.ofReal ((delta : Real) ^ (-eta))) ->
    ShadedBody.multiplicity R (fun i => (W i).toShadedBody) <=
      ENNReal.ofReal ((delta : Real) ^ (-eps))

/-- The exact usable SSF Katz--Tao conclusion in every finite-family universe.
Its Sticky Frostman input is explicit and supplied by the proved producer at the
final compatibility boundary.  The baseline Type-only Katz--Tao API requires an
explicit finite reindexing. -/
theorem source_exists_recorded_stickyKatzTao_parameters
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace Real (Fin 3)))
    {eps : Real} (heps : 0 < eps) :
    ∃ eta delta0 : Real, 0 < eta /\ 0 < delta0 /\
      ∀ {delta : NNReal}, 0 < delta -> (delta : Real) <= delta0 ->
      ∀ {iota : Type u} (R : Finset iota)
        (W : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        (∀ i ∈ R, (W i).carrier <= Metric.closedBall 0 1) ->
      ∀ {Cu : NNReal} (U : ShadedUniformTubeSet R W (ssfGridLen delta) Cu),
        ENNReal.ofReal ((delta : Real) ^ eta) <=
          ShadedBody.fullness' R (fun i => (W i).toShadedBody) ->
        ConvexSpaceBody.IsKatzTao R (fun i => (W i).toConvexSpaceBody)
          (ENNReal.ofReal ((delta : Real) ^ (-eta))) ->
        U.tubeUniform.IsKatzTaoAtEveryScale
          (ENNReal.ofReal ((delta : Real) ^ (-eta))) ->
        ShadedBody.multiplicity R (fun i => (W i).toShadedBody) <=
          ENNReal.ofReal ((delta : Real) ^ (-eps)) := by
  exact StickyKakeya.stickyKatzTaoEstimate_apply.{u, 0}
    (E := EuclideanSpace Real (Fin 3))
    (StickyKakeya.stickyKatzTaoEstimate_of_stickyFrostmanEstimate
      hSFE) eps heps

/-- Pay terminal preparation exactly once on the same actual shaded family. -/
theorem source_sticky_terminal_payment {iota : Type u} {delta : NNReal}
    {R : Finset iota} {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))}
    {M C : Nat} (Q : SourceThreadedTower R T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    {a epsSticky : Real} (P : SourceStickySSFPreparation Q Z a)
    (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    (hsticky : ShadedBody.multiplicity P.retained (fun i => (P.shading i).toShadedBody) <=
      ENNReal.ofReal ((delta : Real) ^ (-epsSticky))) :
    ShadedBody.multiplicity R (fun i => (Z i).toShadedBody) <=
      ENNReal.ofReal ((delta : Real) ^ (-(epsSticky + a))) /\
    (∑ i ∈ R, volume (Z i).shade) <=
      ENNReal.ofReal ((delta : Real) ^ (-(epsSticky + a))) *
        volume (⋃ i ∈ R, (Z i).shade) := by
  have hmul : ShadedBody.multiplicity R (fun i => (Z i).toShadedBody) <=
      ENNReal.ofReal ((delta : Real) ^ (-(epsSticky + a))) := by
    calc
      _ <= ENNReal.ofReal ((delta : Real) ^ (-a)) *
          ENNReal.ofReal ((delta : Real) ^ (-epsSticky)) :=
        P.multiplicity.trans (mul_le_mul_left' hsticky _)
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add (by exact_mod_cast hdelta0)]
        congr 2
        ring
  exact ⟨hmul, (ShadedBody.multiplicity_le_iff R (fun i => (Z i).toShadedBody)).mp hmul⟩

/-- New fixed-M theorem derived from the recorded SSF boundary, not a new
external version of source part (A). M1 and etaB precede every later M and delta.
The endpoint retains a strict positive margin after the one terminal loss. -/
theorem source_exists_fixed_sticky_parameters (C A0 A1 : Nat)
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace Real (Fin 3)))
    (hC : 1 <= C) (hA0 : 1 <= A0) (hA1 : 1 <= A1)
    {eps : Real} (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ (M1 : Nat) (etaB epsSticky a etaSSF deltaSSF : Real),
      2 <= M1 /\ 0 < etaB /\ 0 < epsSticky /\ 0 < a /\
      0 < etaSSF /\ 0 < deltaSSF /\ epsSticky + a < eps /\
      etaB + a < etaSSF /\ SourceRecordedStickyParameters.{u} epsSticky etaSSF deltaSSF /\
      ∀ M : Nat, 2 <= M -> M1 ∣ M ->
      ∃ delta0 : NNReal, 0 < delta0 /\ delta0 <= 1 /\
        (delta0 : Real) <= deltaSSF /\
        delta0 <= (400 : NNReal) ^ (-(M : Real)) /\
        ∀ {iota : Type u} {delta : NNReal} {R : Finset iota}
          {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))},
          0 < delta -> delta < delta0 ->
        ∀ (Q : SourceThreadedTower R T M C)
          (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
          SourceFixedTowerInput Q A0 A1 etaB -> SourceTowerStatistics Q Z ->
          ENNReal.ofReal ((delta : Real) ^ etaB) <=
            ShadedBody.fullness' R (fun i => (Z i).toShadedBody) ->
          (∀ k, k <= M -> Kakeya.maxDensity (Q.indexSet k)
            (fun j => (Q.tube k j).toConvexSpaceBody) <=
              ENNReal.ofReal ((delta : Real) ^ (-etaB))) ->
        ∃ P : SourceStickySSFPreparation Q Z a,
          ENNReal.ofReal ((delta : Real) ^ etaSSF) <=
            ShadedBody.fullness' P.retained (fun i => (P.shading i).toShadedBody) /\
          ConvexSpaceBody.IsKatzTao P.retained (fun i => (P.shading i).toConvexSpaceBody)
            (ENNReal.ofReal ((delta : Real) ^ (-etaSSF))) /\
          P.uniform.tubeUniform.IsKatzTaoAtEveryScale
            (ENNReal.ofReal ((delta : Real) ^ (-etaSSF))) /\
          ShadedBody.multiplicity P.retained (fun i => (P.shading i).toShadedBody) <=
            ENNReal.ofReal ((delta : Real) ^ (-epsSticky)) /\
          ShadedBody.multiplicity R (fun i => (Z i).toShadedBody) <=
            ENNReal.ofReal ((delta : Real) ^ (-(epsSticky + a))) /\
          (∑ i ∈ R, volume (Z i).shade) <=
            ENNReal.ofReal ((delta : Real) ^ (-(epsSticky + a))) *
              volume (⋃ i ∈ R, (Z i).shade) := by
  classical
  obtain ⟨etaSSF, deltaSSF, heta, hdssf, hrecord⟩ :=
    source_exists_recorded_stickyKatzTao_parameters hSFE (eps := eps / 2) (by linarith)
  obtain ⟨K, J, hK, hJ, hinterp⟩ :=
    source_exists_sticky_density_interpolation_constants C A0 A1 hC hA0 hA1
  let etaB : Real := min (etaSSF / 8) (1 / 2)
  let a : Real := min (eps / 4) (etaSSF / 8)
  have hetaB : 0 < etaB := lt_min (by positivity) (by norm_num)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have hBa : etaB + a < etaSSF := by
    have hB := min_le_left (etaSSF / 8) (1 / 2 : Real)
    have hA := min_le_right (eps / 4) (etaSSF / 8)
    dsimp [etaB, a]
    linarith
  have hacc : eps / 2 + a < eps := by
    have hh := min_le_left (eps / 4) (etaSSF / 8)
    dsimp [a]
    linarith
  let M1 : Nat := max 2 (Nat.ceil (4 * (J : Real) / etaSSF))
  have hM1 : 2 <= M1 := le_max_left _ _
  have hsize : 4 * (J : Real) / etaSSF <= (M1 : Real) :=
    (Nat.le_ceil _).trans (by
      have hh : Nat.ceil (4 * (J : Real) / etaSSF) <= M1 := le_max_right _ _
      exact_mod_cast hh)
  obtain ⟨dPrep, hdPrep, hdPrep1, hPrep⟩ := source_exists_terminal_ssf_preparation 4 ha
  obtain ⟨dK, hdK, hdK1, hKabs⟩ := ML2Reduction.exists_threshold_const_le_rpow
    (A := K) (g := etaSSF / 4) (by positivity)
  obtain ⟨dCard, hdCard, hdCard1, hCardAbs⟩ := ML2Reduction.exists_threshold_const_le_rpow
    (A := ((Tube.card_le_of_densityIn_le.C 3 : NNReal) : Real)) (g := 1) (by norm_num)
  refine ⟨M1, etaB, eps / 2, a, etaSSF, deltaSSF, hM1, hetaB, by linarith,
    ha, heta, hdssf, hacc, hBa, hrecord, ?_⟩
  intro M hM hdiv
  have hMpos : 0 < (M : Real) := by exact_mod_cast (show 0 < M by omega)
  have hMge : M1 <= M := Nat.le_of_dvd (by omega) hdiv
  have hJM : (J : Real) / (M : Real) <= etaSSF / 4 := by
    have hh : 4 * (J : Real) / etaSSF <= (M : Real) := hsize.trans (by exact_mod_cast hMge)
    rw [div_le_iff₀ heta] at hh
    rw [div_le_iff₀ hMpos]
    nlinarith
  let dS : NNReal := ⟨deltaSSF, hdssf.le⟩
  let dKr : NNReal := ⟨dK, hdK.le⟩
  let dCr : NNReal := ⟨dCard, hdCard.le⟩
  let d0 : NNReal := min dPrep (min dS (min dKr (min dCr ((400 : NNReal) ^ (-(M : Real))))))
  have hd00 : 0 < d0 := lt_min hdPrep (lt_min hdssf (lt_min hdK (lt_min hdCard (by positivity))))
  have hd0p : d0 <= dPrep := min_le_left _ _
  have hd0s : d0 <= dS := (min_le_right _ _).trans (min_le_left _ _)
  have hd0k : d0 <= dKr := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hd0c : d0 <= dCr := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hd0t : d0 <= (400 : NNReal) ^ (-(M : Real)) := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨d0, hd00, hd0p.trans hdPrep1, by exact_mod_cast hd0s, hd0t, ?_⟩
  intro iota delta R T hd0 hdd0 Q Z hinput hstats hfull hlevels
  have hd1 : delta <= 1 := (hdd0.le.trans hd0p).trans hdPrep1
  have hdpos : (0 : Real) < (delta : Real) := by exact_mod_cast hd0
  have hdle1 : (delta : Real) <= 1 := by exact_mod_cast hd1
  have hZbody : ∀ i, (Z i).toConvexSpaceBody = (T i).toConvexSpaceBody := fun i =>
    congrArg Tube.toConvexSpaceBody (hstats.same_tubes i)
  have hball : ∀ i ∈ R, (Z i).carrier <= Metric.closedBall 0 1 := by
    intro i hi
    change (Z i).toConvexSpaceBody.carrier <= _
    rw [hZbody i]
    exact (hinput.geometry.original_ball i hi).trans (Metric.closedBall_subset_closedBall (by norm_num))
  have hZd : Kakeya.maxDensity R (fun i => (Z i).toConvexSpaceBody) <=
      ENNReal.ofReal ((delta : Real) ^ (-etaB)) := by
    simpa only [hZbody] using hinput.maximal_density
  have hcardraw : (R.card : Real) <=
      ((Tube.card_le_of_densityIn_le.C 3 : NNReal) : Real) *
        (delta : Real) ^ (-etaB) * (delta : Real) ^ (-(2 : Real)) := by
    have hZd' : Kakeya.maxDensity R (fun i => (Z i).toConvexSpaceBody) <=
        (delta : ENNReal) ^ (-etaB) := by
      rw [← ENNReal.ofReal_rpow_of_pos hdpos] at hZd
      simpa only [ENNReal.ofReal_coe_nnreal] using hZd
    have hraw := Tube.card_le_of_densityIn_le (E := EuclideanSpace Real (Fin 3))
      (δ := delta) (s := R) (T := fun i => (Z i).toTube) hd0.ne' hball
      ((Kakeya.le_maxDensity R (fun i => (Z i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall).trans hZd')
    have hn : Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3 := by simp
    rw [hn] at hraw
    norm_num at hraw
    have hzpow : (delta : ENNReal) ^ (-2 : Int) = (delta : ENNReal) ^ (-2 : Real) := by
      rw [← ENNReal.rpow_intCast]
      norm_num
    rw [hzpow, ← ENNReal.coe_rpow_of_ne_zero hd0.ne' (-etaB),
      ← ENNReal.coe_rpow_of_ne_zero hd0.ne' (-2 : Real), ← ENNReal.coe_mul,
      ← ENNReal.coe_mul, show (R.card : ENNReal) = ((R.card : NNReal) : ENNReal) by simp,
      ENNReal.coe_le_coe, ← NNReal.coe_le_coe] at hraw
    simpa [NNReal.coe_rpow] using hraw
  have hcard : (R.card : Real) <= (delta : Real) ^ (-(4 : Real)) := by
    have hconst := hCardAbs (delta : Real) hdpos (by exact_mod_cast hdd0.le.trans hd0c)
    have hB1 : etaB <= 1 := (min_le_right _ _).trans (by norm_num)
    calc
      _ <= ((Tube.card_le_of_densityIn_le.C 3 : NNReal) : Real) *
          (delta : Real) ^ (-etaB) * (delta : Real) ^ (-(2 : Real)) := hcardraw
      _ <= (delta : Real) ^ (-(1 : Real)) * (delta : Real) ^ (-etaB) *
          (delta : Real) ^ (-(2 : Real)) := by gcongr
      _ = (delta : Real) ^ (-(3 + etaB)) := by
        rw [← Real.rpow_add hdpos, ← Real.rpow_add hdpos]
        congr 1
        ring
      _ <= _ := Real.rpow_le_rpow_of_exponent_ge hdpos hdle1 (by linarith)
  have hmass : 0 < ∑ i ∈ R, volume (Z i).shade := by
    have hfp : 0 < ShadedBody.fullness' R (fun i => (Z i).toShadedBody) :=
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdpos _)).trans_le hfull
    exact pos_iff_ne_zero.mpr fun hz => by simp [ShadedBody.fullness', hz] at hfp
  obtain ⟨P⟩ := hPrep hd0 (hdd0.trans_le hd0p) hinput.geometry.nonempty Q Z hstats hball
    (by simpa using hcard) hmass
  have hPlower : ENNReal.ofReal ((delta : Real) ^ (etaB + a)) <=
      ShadedBody.fullness' P.retained (fun i => (P.shading i).toShadedBody) := by
    have hh := mul_le_mul_right (hfull.trans P.fullness)
      (ENNReal.ofReal ((delta : Real) ^ a))
    have hcancel : ENNReal.ofReal ((delta : Real) ^ a) *
        ENNReal.ofReal ((delta : Real) ^ (-a)) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hdpos]
      simp
    rw [← mul_assoc, hcancel, one_mul] at hh
    simpa only [← ENNReal.ofReal_mul (by positivity : (0 : Real) <= (delta : Real) ^ a),
      ← Real.rpow_add hdpos, add_comm a etaB] using hh
  have hPfull : ENNReal.ofReal ((delta : Real) ^ etaSSF) <=
      ShadedBody.fullness' P.retained (fun i => (P.shading i).toShadedBody) :=
    (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hdpos hdle1 hBa.le)).trans hPlower
  have hPbody : ∀ i, (P.shading i).toConvexSpaceBody = (T i).toConvexSpaceBody := fun i =>
    congrArg Tube.toConvexSpaceBody (P.tube_identity i)
  have hPd : ConvexSpaceBody.IsKatzTao P.retained (fun i => (P.shading i).toConvexSpaceBody)
      (ENNReal.ofReal ((delta : Real) ^ (-etaSSF))) := by
    rw [ConvexSpaceBody.IsKatzTao_def]
    simp only [hPbody]
    refine ((Kakeya.maxDensity_mono _ P.subset).trans hinput.maximal_density).trans ?_
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hdpos hdle1 (by linarith [ha]))
  have hH1 : (1 : ENNReal) <= ENNReal.ofReal ((delta : Real) ^ (-etaB)) := by
    have hh := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdpos hdle1 (neg_nonpos.mpr hetaB.le)
    simpa using ENNReal.ofReal_le_ofReal hh
  have hPi := hinterp hM hd0 (hdd0.trans_le hd0t) Q hinput.geometry
    (ENNReal.ofReal ((delta : Real) ^ (-etaB))) hH1 ENNReal.ofReal_ne_top hlevels
    P.retained P.subset P.shading P.tube_identity P.uniform P.occupied
  have hPscale : P.uniform.tubeUniform.IsKatzTaoAtEveryScale
      (ENNReal.ofReal ((delta : Real) ^ (-etaSSF))) := by
    refine hPi.mono ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hconst := hKabs (delta : Real) hdpos (by exact_mod_cast hdd0.le.trans hd0k)
    calc
      _ <= ((delta : Real) ^ (-(etaSSF / 4)) *
          (delta : Real) ^ (-((J : Real) / (M : Real)))) * (delta : Real) ^ (-etaB) := by gcongr
      _ = (delta : Real) ^ (-(etaSSF / 4 + (J : Real) / (M : Real) + etaB)) := by
        rw [← Real.rpow_add hdpos, ← Real.rpow_add hdpos]
        congr 1
        ring
      _ <= _ := Real.rpow_le_rpow_of_exponent_ge hdpos hdle1 (by
        have hh : etaB <= etaSSF / 8 := min_le_left _ _
        linarith)
  have hPsticky := hrecord hd0 (by exact_mod_cast hdd0.le.trans hd0s)
    P.retained P.shading P.ball P.uniform hPfull hPd hPscale
  have hpaid := source_sticky_terminal_payment Q Z P hd0 hd1 hPsticky
  exact ⟨P, hPfull, hPd, hPscale, hPsticky, hpaid.1, hpaid.2⟩

/-- Actual absolute-accuracy exit from the SAME fixed-Q assigned good array.
The finite B-power is absorbed only after N, B and the positive exponent margin
are fixed; neither the tower nor its potential is replaced at a restart. -/
theorem source_exists_assigned_good_sticky_exit (C A0 A1 : Nat)
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace Real (Fin 3)))
    (hC : 1 <= C) (hA0 : 1 <= A0) (hA1 : 1 <= A1)
    {accuracy : Real} (haccuracy : 0 < accuracy) (haccuracy1 : accuracy < 1) :
    ∃ (M1 : Nat) (etaB : Real), 2 <= M1 /\ 0 < etaB /\
      ∀ M : Nat, 2 <= M -> M1 ∣ M ->
      ∀ (N : Nat) (B : NNReal) (e eta0 : Real),
        1 <= B -> 0 < e -> 5 * e < etaB -> 0 < eta0 -> 3 * eta0 <= etaB ->
      ∃ delta0 : NNReal, 0 < delta0 /\ delta0 <= 1 /\
        delta0 <= (400 : NNReal) ^ (-(M : Real)) /\
        ∀ {iota : Type u} {delta : NNReal} {R : Finset iota}
          {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))},
          0 < delta -> delta < delta0 ->
        ∀ (Q : SourceThreadedTower R T M C)
          (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
          SourceFixedTowerInput Q A0 A1 eta0 -> SourceTowerStatistics Q Z ->
          ENNReal.ofReal ((delta : Real) ^ (3 * eta0)) <=
            ShadedBody.fullness' R (fun i => (Z i).toShadedBody) ->
          SourceFixedKTArrayGood Q B N e ->
          ShadedBody.multiplicity R (fun i => (Z i).toShadedBody) <=
            ENNReal.ofReal ((delta : Real) ^ (-accuracy)) /\
          (∑ i ∈ R, volume (Z i).shade) <=
            ENNReal.ofReal ((delta : Real) ^ (-accuracy)) *
              volume (⋃ i ∈ R, (Z i).shade) := by
  obtain ⟨M1, etaB, epsSticky, a, etaSSF, deltaSSF, hM1, hetaB, hepsSticky, ha,
    hetaSSF, hdeltaSSF, hmargin, hgapSSF, hrecord, hfixed⟩ :=
    source_exists_fixed_sticky_parameters C A0 A1 hSFE hC hA0 hA1 haccuracy haccuracy1
  refine ⟨M1, etaB, hM1, hetaB, ?_⟩
  intro M hM hdiv N B e eta0 hB he hegap heta0 hetagap
  obtain ⟨d0, hd0, hd1, hdSSF, hdtower, happly⟩ := hfixed M hM hdiv
  let L : NNReal := (1280 ^ 6 : NNReal) * B ^ (N + 1)
  obtain ⟨dB, hdB, hdB1, hBabs⟩ := ML2Reduction.exists_threshold_const_le_rpow
    (A := (L : Real)) (g := etaB - 5 * e) (by linarith)
  let dBN : NNReal := ⟨dB, hdB.le⟩
  refine ⟨min d0 dBN, lt_min hd0 hdB, (min_le_left _ _).trans hd1,
    (min_le_left _ _).trans hdtower, ?_⟩
  intro iota delta R T hdelta0 hdelta Q Z hinput hstats hfull hgood
  have hdelta1 : delta <= 1 := (hdelta.le.trans (min_le_left _ _)).trans hd1
  have hdpos : (0 : Real) < (delta : Real) := by exact_mod_cast hdelta0
  have hdle1 : (delta : Real) <= 1 := by exact_mod_cast hdelta1
  have hinput' : SourceFixedTowerInput Q A0 A1 etaB := {
    geometry := hinput.geometry
    neighbour_sharing := hinput.neighbour_sharing
    maximal_density := hinput.maximal_density.trans
      (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hdpos hdle1 (by linarith)))
  }
  have hfull' : ENNReal.ofReal ((delta : Real) ^ etaB) <=
      ShadedBody.fullness' R (fun i => (Z i).toShadedBody) :=
    (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hdpos hdle1 hetagap)).trans hfull
  have hlevels := source_sticky_level_density_of_assigned_good Q hM hinput.geometry hB he.le
    hdelta0 hdelta1 hgood
  have hlevels' : ∀ k, k <= M -> Kakeya.maxDensity (Q.indexSet k)
      (fun i => (Q.tube k i).toConvexSpaceBody) <= ENNReal.ofReal ((delta : Real) ^ (-etaB)) := by
    intro k hk
    refine (hlevels k hk).trans ?_
    have hconst := hBabs (delta : Real) hdpos (by exact_mod_cast hdelta.le.trans (min_le_right _ _))
    have hbound : (L : Real) * (delta : Real) ^ (-(5 * e)) <= (delta : Real) ^ (-etaB) := by
      calc
        _ <= (delta : Real) ^ (-(etaB - 5 * e)) * (delta : Real) ^ (-(5 * e)) := by gcongr
        _ = _ := by
          rw [← Real.rpow_add hdpos]
          congr 1
          ring
    have hLE : ENNReal.ofReal (L : Real) = (1280 ^ 6 : ENNReal) * (B : ENNReal) ^ (N + 1) := by
      simp [L]
    rw [← hLE, ← ENNReal.ofReal_mul (NNReal.coe_nonneg L)]
    exact ENNReal.ofReal_le_ofReal hbound
  obtain ⟨P, hPfull, hPd, hPscale, hPsticky, hmult, hmass⟩ :=
    happly hdelta0 (hdelta.trans_le (min_le_left _ _)) Q Z hinput' hstats hfull' hlevels'
  have hpay : ENNReal.ofReal ((delta : Real) ^ (-(epsSticky + a))) <=
      ENNReal.ofReal ((delta : Real) ^ (-accuracy)) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hdpos hdle1 (by linarith))
  exact ⟨hmult.trans hpay, hmass.trans (mul_le_mul_left hpay _)⟩

/-- Explicit room for later main-entrance and finite-descent payments. -/
theorem source_sticky_absolute_accuracy_margin {delta : NNReal}
    {beta c accuracy paid : Real} (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    (hmargin : accuracy + paid < beta / 2 - c) :
    ENNReal.ofReal ((delta : Real) ^ (-paid)) *
      ENNReal.ofReal ((delta : Real) ^ (-accuracy)) <=
        ENNReal.ofReal ((delta : Real) ^ (-(beta / 2 - c))) := by
  rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add (by exact_mod_cast hdelta0)]
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hdelta0)
    (by exact_mod_cast hdelta1)
  linarith

end Kakeya.ML2Core
