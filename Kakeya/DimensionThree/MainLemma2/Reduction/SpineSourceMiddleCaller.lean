/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceMediantSeam
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceMiddleCalibration
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceNormalizedRetention
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineMiddleProducer

@[expose] public section

open MeasureTheory Kakeya.ML2Core Kakeya.ML2Reduction Kakeya.VeryNotSticky
open scoped NNReal ENNReal

namespace Kakeya.ML2Assembly

universe u

section Runtime

variable {iota : Type u} {delta Cu : NNReal} {u : Finset iota}
  {T : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
  (U : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen delta) Cu)

open Classical in
noncomputable def sourceMiddleLeaf (t1 : Finset iota) (b : Nat) : Finset iota :=
  {i ∈ u | U.cover.assign b i ∈ t1}

open Classical in
noncomputable def sourceMiddleFibre (t1 tTau : Finset iota) (p b : Nat) (jp : iota) :
    Finset iota := {j ∈ tTau | coarseNode (retainedLeafChain U t1 b) p b j = jp}

noncomputable def sourceMiddleFullness (t1 tTau : Finset iota) (b : Nat)
    (shift : EuclideanSpace Real (Fin 3)) : NNReal :=
  (spineScaleLoss 3 (sourceMiddleLeaf U t1 b).card delta *
      spineScaleLoss 3 tTau.card (Tube.gridScale delta (Tube.ssfGridLen delta) b))⁻¹ *
    ShadedBody.fullness (sourceMiddleLeaf U t1 b) (fun i => ((T i).translate shift).toShadedBody)

/-- C0's positive original shaded mass gives the positive mediant denominator. -/
theorem sourceMiddle_fullness_pos {t1 tTau : Finset iota} {b : Nat}
    {shift : EuclideanSpace Real (Fin 3)}
    (hdelta : 0 < delta) (hdelta1 : delta <= 1) (hb : b <= Tube.ssfGridLen delta)
    (htTau : tTau.Nonempty)
    (hmass : 0 < ∑ i ∈ sourceMiddleLeaf U t1 b, volume ((T i).translate shift).shade) :
    0 < sourceMiddleFullness U t1 tTau b shift := by
  classical
  have hne : (sourceMiddleLeaf U t1 b).Nonempty := by
    by_contra hh
    simp [Finset.not_nonempty_iff_eq_empty.mp hh] at hmass
  have hfinite := (Kakeya.StickyKakeya.sum_volume_carrier_pos_ne_top hdelta
    (sourceMiddleLeaf U t1 b) (fun i => (T i).translate shift) hne).2
  apply mul_pos
  · apply inv_pos.mpr
    exact mul_pos (zero_lt_one.trans_le (one_le_spineScaleLoss _ _ _))
      (zero_lt_one.trans_le (one_le_spineScaleLoss _ _ _))
  · exact ML2Shaded.fullness_pos_of_sum_shade_ne_zero hmass.ne' hfinite

/-- C0 supplies this jp; C2 supplies only its scalar rows. No normalized row is assumed. -/
structure SourceMiddleOriginalInput (t1 tTau : Finset iota) (a p b m N : Nat)
    (shift : EuclideanSpace Real (Fin 3))
    (Z : iota -> ShadedTube (Tube.gridScale delta (Tube.ssfGridLen delta) b)
      (EuclideanSpace Real (Fin 3))) (jp : iota)
    {rho : NNReal} {R : Real}
    (hsit : Tube.IsRescalingSituation (Tube.gridScale delta (Tube.ssfGridLen delta) p)
      (Tube.gridScale delta (Tube.ssfGridLen delta) b) rho R 3) (hR : 0 < R)
    (e q gamma etaD : Real) (K0 : Nat) (Cstar : ENNReal) (rung : Nat -> Real) : Prop where
  delta_pos : 0 < delta
  delta_le_one : delta <= 1
  ancestor_le_parent : a <= p
  parent_le_middle : p <= b
  middle_le_grid : b <= Tube.ssfGridLen delta
  middle_subset : tTau ⊆ activeNodes (retainedLeafChain U t1 b) b
  parent_active : jp ∈ activeNodes (retainedLeafChain U t1 b) p
  original_tubes : forall j,
    (Z j).toTube = ((retainedLeafChain U t1 b).tube b j).translate shift
  window : IsKatzTaoDividingWindow U Cstar rung e N a b m
  mediant_positive : 0 < sourceMiddleFullness U t1 tTau b shift
  mediant : sourceMiddleFullness U t1 tTau b shift <=
    ShadedBody.fullness (sourceMiddleFibre U t1 tTau p b jp) (fun i => (Z i).toShadedBody)
  rho_eq : rho = midScale delta (Tube.ssfGridLen delta) p b
  rho_pos : 0 < rho
  rho_le_one : rho <= 1
  div_pos : 0 < e
  scale_lower : 20 * delta <= rho
  scale_upper : (rho : Real) <= (delta : Real) ^ (e / 2) / 2
  card_power : 4 <= e * (K0 : Real) / 2
  ambient_card : (u.card : Real) <= (delta : Real) ^ (-(4 : Real))
  radius_ge_one : 1 <= R
  scale_ratio : (Tube.gridScale delta (Tube.ssfGridLen delta) b : Real) /
      (Tube.gridScale delta (Tube.ssfGridLen delta) p : Real) <= 4 * (rho : Real)
  fullness_scalar : rho ^ gamma <=
    (outerLoss R)⁻¹ * sourceMiddleFullness U t1 tTau b shift
  normalized_density_scalar : (outerLoss R : ENNReal) *
      (Cstar * ENNReal.ofReal
        (((Tube.gridScale delta (Tube.ssfGridLen delta) a : Real) /
          (Tube.gridScale delta (Tube.ssfGridLen delta) b : Real)) ^ rung m)) <=
    (rho : ENNReal) ^ (-q)
  original_density_scalar : Cstar * ENNReal.ofReal
      (((Tube.gridScale delta (Tube.ssfGridLen delta) a : Real) /
        (Tube.gridScale delta (Tube.ssfGridLen delta) b : Real)) ^ rung m) <=
    (rho : ENNReal) ^ (-(etaD - q))

/-- Actual ancestor, fibre and indexed normalization identities, all on the chosen jp. -/
structure SourceMiddleOriginalRows (t1 tTau : Finset iota) (a p b : Nat)
    (shift : EuclideanSpace Real (Fin 3))
    (Z : iota -> ShadedTube (Tube.gridScale delta (Tube.ssfGridLen delta) b)
      (EuclideanSpace Real (Fin 3))) (jp : iota)
    {rho : NNReal} {R : Real}
    (hsit : Tube.IsRescalingSituation (Tube.gridScale delta (Tube.ssfGridLen delta) p)
      (Tube.gridScale delta (Tube.ssfGridLen delta) b) rho R 3) (hR : 0 < R)
    (q gamma etaD : Real) (K0 : Nat) : Prop where
  ancestor_mem : coarseNode (retainedLeafChain U t1 b) a p jp ∈ U.cover.indexSet a
  ancestor_contains : (U.cover.tube p jp).toConvexSpaceBody <=
    (U.cover.tube a (coarseNode (retainedLeafChain U t1 b) a p jp)).toConvexSpaceBody
  fibre_under_ancestor : sourceMiddleFibre U t1 tTau p b jp ⊆
    U.nodesUnder b a (coarseNode (retainedLeafChain U t1 b) a p jp)
  nonempty : (sourceMiddleFibre U t1 tTau p b jp).Nonempty
  contained : forall i, i ∈ sourceMiddleFibre U t1 tTau p b jp ->
    (Z i).carrier ⊆ (((retainedLeafChain U t1 b).tube p jp).translate shift).carrier
  card_leaf : (sourceMiddleFibre U t1 tTau p b jp).card <= (sourceMiddleLeaf U t1 b).card
  leaf_card : (sourceMiddleLeaf U t1 b).card <= u.card
  card_power : ((sourceMiddleFibre U t1 tTau p b jp).card : Real) <=
    (rho : Real) ^ (-(K0 : Real))
  original_density : Kakeya.maxDensity (sourceMiddleFibre U t1 tTau p b jp)
      (fun i => (Z i).toConvexSpaceBody) <= (rho : ENNReal) ^ (-(etaD - q))
  normalized_density : Kakeya.maxDensity (sourceMiddleFibre U t1 tTau p b jp)
      (fun i => (outerFamily hsit.pos_ambient
        (((retainedLeafChain U t1 b).tube p jp).translate shift) hR rho Z i).toConvexSpaceBody) <=
    (rho : ENNReal) ^ (-q)
  normalized_fullness : (rho : ENNReal) ^ gamma <=
    ShadedBody.fullness (sourceMiddleFibre U t1 tTau p b jp)
      (fun i => (outerFamily hsit.pos_ambient
        (((retainedLeafChain U t1 b).tube p jp).translate shift) hR rho Z i).toShadedBody)
  normalized_shade : forall i, i ∈ sourceMiddleFibre U t1 tTau p b jp ->
    (outerFamily hsit.pos_ambient (((retainedLeafChain U t1 b).tube p jp).translate shift)
      hR rho Z i).shade =
      spineRescaleUnit hsit.pos_ambient (((retainedLeafChain U t1 b).tube p jp).translate shift)
        hR '' (Z i).shade
  normalized_multiplicity : ShadedBody.multiplicity (sourceMiddleFibre U t1 tTau p b jp)
      (fun i => (outerFamily hsit.pos_ambient
        (((retainedLeafChain U t1 b).tube p jp).translate shift) hR rho Z i).toShadedBody) =
    ShadedBody.multiplicity (sourceMiddleFibre U t1 tTau p b jp) (fun i => (Z i).toShadedBody)
  normalized_map :
    (spineRescaleUnit hsit.pos_ambient
      (((retainedLeafChain U t1 b).tube p jp).translate shift) hR).toAffineMap =
      (((retainedLeafChain U t1 b).tube p jp).translate shift).rescaleMap R
  jacobian_value : Kakeya.affineJacobian (spineRescaleUnit hsit.pos_ambient
      (((retainedLeafChain U t1 b).tube p jp).translate shift) hR) =
    ENNReal.ofReal ((4 * R)⁻¹ ^ (3 : Nat)) *
      (Tube.gridScale delta (Tube.ssfGridLen delta) p : ENNReal)⁻¹ ^ (2 : Nat)
  jacobian_pos : 0 < Kakeya.affineJacobian (spineRescaleUnit hsit.pos_ambient
    (((retainedLeafChain U t1 b).tube p jp).translate shift) hR)
  jacobian_finite : Kakeya.affineJacobian (spineRescaleUnit hsit.pos_ambient
    (((retainedLeafChain U t1 b).tube p jp).translate shift) hR) < (⊤ : ENNReal)
  normalized_mass : forall I : Finset iota, I ⊆ sourceMiddleFibre U t1 tTau p b jp ->
    (∑ i ∈ I, volume (outerFamily hsit.pos_ambient
      (((retainedLeafChain U t1 b).tube p jp).translate shift) hR rho Z i).shade) =
      Kakeya.affineJacobian (spineRescaleUnit hsit.pos_ambient
        (((retainedLeafChain U t1 b).tube p jp).translate shift) hR) *
        ∑ i ∈ I, volume (Z i).shade
  normalized_union : forall I : Finset iota, I ⊆ sourceMiddleFibre U t1 tTau p b jp ->
    volume (⋃ i ∈ I, (outerFamily hsit.pos_ambient
      (((retainedLeafChain U t1 b).tube p jp).translate shift) hR rho Z i).shade) =
      Kakeya.affineJacobian (spineRescaleUnit hsit.pos_ambient
        (((retainedLeafChain U t1 b).tube p jp).translate shift) hR) *
        volume (⋃ i ∈ I, (Z i).shade)

/-- The actual C0 mediant and C2 scalars produce the original R4 antecedents. -/
theorem sourceMiddle_original_rows {t1 tTau : Finset iota} {a p b m N : Nat}
    {shift : EuclideanSpace Real (Fin 3)}
    {Z : iota -> ShadedTube (Tube.gridScale delta (Tube.ssfGridLen delta) b)
      (EuclideanSpace Real (Fin 3))} {jp : iota} {rho : NNReal} {R : Real}
    {hsit : Tube.IsRescalingSituation (Tube.gridScale delta (Tube.ssfGridLen delta) p)
      (Tube.gridScale delta (Tube.ssfGridLen delta) b) rho R 3} {hR : 0 < R}
    {e q gamma etaD : Real} {K0 : Nat} {Cstar : ENNReal} {rung : Nat -> Real}
    (hinput : SourceMiddleOriginalInput U t1 tTau a p b m N shift Z jp hsit hR
      e q gamma etaD K0 Cstar rung) :
    SourceMiddleOriginalRows U t1 tTau a p b shift Z jp hsit hR q gamma etaD K0 := by
  classical
  let C := retainedLeafChain U t1 b
  let F := sourceMiddleFibre U t1 tTau p b jp
  let jtheta := coarseNode C a p jp
  let T0 := (C.tube p jp).translate shift
  let A := spineRescaleUnit hsit.pos_ambient T0 hR
  have hpN := hinput.parent_le_middle.trans hinput.middle_le_grid
  have haN := hinput.ancestor_le_parent.trans hpN
  have hjtheta : jtheta ∈ U.cover.indexSet a := coarseNode_mem C haN hinput.parent_active
  have hparent : (U.cover.tube p jp).toConvexSpaceBody <=
      (U.cover.tube a jtheta).toConvexSpaceBody :=
    tube_le_coarseNode C hinput.ancestor_le_parent hpN hinput.parent_active
  have hbody (i : iota) : (Z i).toConvexSpaceBody = ((C.tube b i).translate shift).toConvexSpaceBody :=
    congrArg Tube.toConvexSpaceBody (hinput.original_tubes i)
  have hunder : F ⊆ U.nodesUnder b a jtheta := by
    intro i hi
    obtain ⟨hit, hip⟩ := Finset.mem_filter.mp hi
    have hactive := hinput.middle_subset hit
    have hle := tube_le_coarseNode C hinput.parent_le_middle hinput.middle_le_grid hactive
    rw [hip] at hle
    rw [Tube.UniformTubeSet.nodesUnder_eq_nodesIn, Tube.UniformTubeSet.mem_nodesIn_iff]
    exact ⟨(activeNodes_subset C b) hactive, hle.trans hparent⟩
  have hcontained : forall i, i ∈ F -> (Z i).carrier ⊆ T0.carrier := by
    intro i hi
    obtain ⟨hit, hip⟩ := Finset.mem_filter.mp hi
    have hh := tube_le_coarseNode C hinput.parent_le_middle hinput.middle_le_grid
      (hinput.middle_subset hit)
    rw [hip] at hh
    have ht := tube_translate_le_translate _ _ shift hh
    change (Z i).toConvexSpaceBody <= T0.toConvexSpaceBody
    rw [hbody i]
    exact ht
  have hne : F.Nonempty := by
    have hp := hinput.mediant_positive.trans_le hinput.mediant
    by_contra hh
    change 0 < ShadedBody.fullness F (fun i => (Z i).toShadedBody) at hp
    simp [Finset.not_nonempty_iff_eq_empty.mp hh, ShadedBody.fullness, ShadedBody.fullness'] at hp
  have hcard : F.card <= (sourceMiddleLeaf U t1 b).card :=
    card_coarseFibre_le C hinput.middle_subset jp
  have hleaf : (sourceMiddleLeaf U t1 b).card <= u.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hcardPower : (F.card : Real) <= (rho : Real) ^ (-(K0 : Real)) := by
    have hd0 : (0 : Real) < delta := by exact_mod_cast hinput.delta_pos
    have hd1 : (delta : Real) <= 1 := by exact_mod_cast hinput.delta_le_one
    have hr0 : (0 : Real) < rho := by exact_mod_cast hinput.rho_pos
    have hrs : (rho : Real) <= (delta : Real) ^ (e / 2) :=
      hinput.scale_upper.trans (by exact div_le_self (Real.rpow_nonneg delta.coe_nonneg _) (by norm_num))
    calc (F.card : Real) <= (u.card : Real) := by exact_mod_cast hcard.trans hleaf
      _ <= (delta : Real) ^ (-(4 : Real)) := hinput.ambient_card
      _ <= (delta : Real) ^ ((e / 2) * (-(K0 : Real))) :=
        Real.rpow_le_rpow_of_exponent_ge hd0 hd1 (by nlinarith [hinput.card_power])
      _ = ((delta : Real) ^ (e / 2)) ^ (-(K0 : Real)) := Real.rpow_mul hd0.le _ _
      _ <= (rho : Real) ^ (-(K0 : Real)) :=
        Real.rpow_le_rpow_of_nonpos hr0 hrs (neg_nonpos.mpr (Nat.cast_nonneg K0))
  have hdensity : Kakeya.maxDensity F (fun i => (Z i).toConvexSpaceBody) <=
      Cstar * ENNReal.ofReal
        (((Tube.gridScale delta (Tube.ssfGridLen delta) a : Real) /
          (Tube.gridScale delta (Tube.ssfGridLen delta) b : Real)) ^ rung m) :=
    (maxDensity_le_of_translate_subset hunder hinput.original_tubes).trans
      (hinput.window.middle_maxDensity_le jtheta hjtheta)
  have hn : Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3 := by simp
  have hshade : forall i, i ∈ F ->
      (outerFamily hsit.pos_ambient T0 hR rho Z i).shade = A '' (Z i).shade :=
    outerFamily_shade_eq hn hsit hR hinput.scale_ratio hcontained
  have hjac : Kakeya.affineJacobian A = ENNReal.ofReal ((4 * R)⁻¹ ^ (3 : Nat)) *
      (Tube.gridScale delta (Tube.ssfGridLen delta) p : ENNReal)⁻¹ ^ (2 : Nat) := by
    let B := (ConvexSpaceBody.closedUnitBall (E := EuclideanSpace Real (Fin 3))).carrier
    have hB0 : volume B ≠ 0 := (ConvexSpaceBody.closedUnitBall_volume_pos).ne'
    have hBt : volume B ≠ ⊤ :=
      (ConvexSpaceBody.closedUnitBall (E := EuclideanSpace Real (Fin 3))).isCompact'.measure_lt_top.ne
    apply (ENNReal.mul_left_inj hB0 hBt).mp
    rw [← Kakeya.volume_image_affineEquiv]
    have hm : (A : EuclideanSpace Real (Fin 3) -> EuclideanSpace Real (Fin 3)) = T0.rescaleMap R :=
      spineRescaleUnit_coe hsit.pos_ambient T0 hR
    rw [hm, Tube.volume_image_rescaleMap hsit.pos_ambient hR T0 B, hn]
    norm_num [mul_assoc]
  refine {
    ancestor_mem := hjtheta
    ancestor_contains := hparent
    fibre_under_ancestor := hunder
    nonempty := hne
    contained := hcontained
    card_leaf := hcard
    leaf_card := hleaf
    card_power := hcardPower
    original_density := hdensity.trans hinput.original_density_scalar
    normalized_density := (outerFamily_maxDensity_le hn hsit hR hinput.radius_ge_one
      hinput.scale_ratio hcontained).trans
        ((mul_le_mul_right hdensity _).trans hinput.normalized_density_scalar)
    normalized_fullness := ?_
    normalized_shade := hshade
    normalized_multiplicity := outerFamily_multiplicity hn hsit hR hinput.scale_ratio hcontained
    normalized_map := spineRescaleUnit_toAffineMap hsit.pos_ambient T0 hR
    jacobian_value := hjac
    jacobian_pos := pos_iff_ne_zero.mpr (Kakeya.affineJacobian_ne_zero A)
    jacobian_finite := lt_top_iff_ne_top.mpr (Kakeya.affineJacobian_ne_top A)
    normalized_mass := ?_
    normalized_union := ?_ }
  · have hh := hinput.fullness_scalar.trans ((mul_le_mul_right hinput.mediant _).trans
      (outerFamily_le_fullness hn hsit hR hinput.radius_ge_one hinput.scale_ratio hcontained))
    have hc : ((rho ^ gamma : NNReal) : ENNReal) <=
        (ShadedBody.fullness F (fun i => (outerFamily hsit.pos_ambient T0 hR rho Z i).toShadedBody) : ENNReal) := by
      exact_mod_cast hh
    simpa only [ENNReal.coe_rpow_of_ne_zero hinput.rho_pos.ne'] using hc
  · intro I hI
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hshade i (hI hi)]
    exact Kakeya.volume_image_affineEquiv A _
  · intro I hI
    have heq : (⋃ i ∈ I, (outerFamily hsit.pos_ambient T0 hR rho Z i).shade) =
        A '' (⋃ i ∈ I, (Z i).shade) := by
      simp only [Set.image_iUnion]
      apply Set.iUnion_congr
      intro i
      apply Set.iUnion_congr
      intro hi
      exact hshade i (hI hi)
    rw [heq]
    exact Kakeya.volume_image_affineEquiv A _

end Runtime

/-- All retention projections on the one E/U1 returned by the verified R4 producer. -/
structure SourceMiddleActualRetention {b deltaTube rho : NNReal} {R : Real}
    (hsit : Tube.IsRescalingSituation b deltaTube rho R 3) (hR : 0 < R)
    (T0 : Tube b (EuclideanSpace Real (Fin 3))) (A q gamma alpha alphaPrime etaD varpi zeta : Real)
    {iota : Type u} (F D E : Finset iota)
    (Z : iota -> ShadedTube deltaTube (EuclideanSpace Real (Fin 3)))
    (U0 U1 : iota -> ShadedTube rho (EuclideanSpace Real (Fin 3))) : Prop where
  paid : SourcePaidRetentionData hsit hR T0 A q gamma alpha alphaPrime F D E Z U0 U1
  count : CountTransport hsit hR T0 0 varpi zeta E Z U1
  subset : E ⊆ F
  nonempty : E.Nonempty
  cardinality_retained : (rho : Real) ^ A * (F.card : Real) <= (E.card : Real)
  cardinality_upper : E.card <= F.card
  mass_retained : (∑ i ∈ F, volume (outerFamily hsit.pos_ambient T0 hR rho Z i).shade) / 512 <=
    (rho : ENNReal) ^ (-(3 * q)) * ∑ i ∈ E, volume (U1 i).shade
  original_fullness : (rho : ENNReal) ^ gamma <=
    ShadedBody.fullness F (fun i => (outerFamily hsit.pos_ambient T0 hR rho Z i).toShadedBody)
  original_density : Kakeya.maxDensity F (fun i => (Z i).toConvexSpaceBody) <=
    (rho : ENNReal) ^ (-(etaD - q))
  retained_fullness : (rho : ENNReal) ^ (3 * q) <=
    ShadedBody.fullness E (fun i => (U1 i).toShadedBody)
  vns_fullness : (rho : ENNReal) ^ etaD <= ShadedBody.fullness E (fun i => (U1 i).toShadedBody)
  retained_density : Kakeya.maxDensity E (fun i => (U1 i).toConvexSpaceBody) <=
    (rho : ENNReal) ^ (-(2 * q))
  uniform : Nonempty (ShadedTube.ShadedUniformTubeSet E U1 (Tube.ssfGridLen rho)
    (ShadedTube.ssfUniformConst 3))
  normalized_multiplicity :
    ShadedBody.multiplicity F (fun i => (outerFamily hsit.pos_ambient T0 hR rho Z i).toShadedBody) =
      ShadedBody.multiplicity F (fun i => (Z i).toShadedBody)
  multiplicity_retained : ShadedBody.multiplicity F (fun i => (Z i).toShadedBody) <=
    (rho : ENNReal) ^ (-(3 * q)) * ShadedBody.multiplicity E (fun i => (U1 i).toShadedBody)

/-- Fix the threshold before U and its seam; apply R4 once to this exact chosen jp. -/
theorem sourceMiddle_exists_actual_retention (A q gamma alpha alphaPrime etaD : Real)
    (hA : 0 < A) (hq : 0 < q) (hgamma : 0 < gamma) (halpha : 0 < alpha)
    (halphaPrime : 0 < alphaPrime) (hgammaq : gamma <= q)
    (hcardgap : gamma + alpha < A) (hmassgap : gamma + alpha + alphaPrime < 3 * q)
    (hetaD : 3 * q <= etaD) (K0 : Nat) (hK0 : 0 < K0) :
    exists rho0 : NNReal, 0 < rho0 ∧ rho0 <= 1 / 20 ∧
      forall {iota : Type u} {delta Cu : NNReal} {u : Finset iota}
        {T : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
        (U : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen delta) Cu)
        (t1 tTau : Finset iota) (a p b m N : Nat) (shift : EuclideanSpace Real (Fin 3))
        (Z : iota -> ShadedTube (Tube.gridScale delta (Tube.ssfGridLen delta) b)
          (EuclideanSpace Real (Fin 3))) (jp : iota) {rho : NNReal} {R : Real}
        (hsit : Tube.IsRescalingSituation (Tube.gridScale delta (Tube.ssfGridLen delta) p)
          (Tube.gridScale delta (Tube.ssfGridLen delta) b) rho R 3) (hR : 0 < R)
        (e : Real) (Cstar : ENNReal) (rung : Nat -> Real),
        SourceMiddleOriginalInput U t1 tTau a p b m N shift Z jp hsit hR
          e q gamma etaD K0 Cstar rung -> rho <= rho0 ->
        forall varpi zeta : Real, 0 <= varpi -> 0 <= 2 + zeta -> rho ^ varpi <= 1 / 2 ->
        exists (D E : Finset iota)
          (U0 U1 : iota -> ShadedTube rho (EuclideanSpace Real (Fin 3))),
          SourceMiddleOriginalRows U t1 tTau a p b shift Z jp hsit hR q gamma etaD K0 ∧
          SourceMiddleActualRetention hsit hR
            (((retainedLeafChain U t1 b).tube p jp).translate shift)
            A q gamma alpha alphaPrime etaD varpi zeta
            (sourceMiddleFibre U t1 tTau p b jp) D E Z U0 U1 := by
  obtain ⟨rho0, hrho0, hrho20, hret⟩ := sourceRetention_exists_normalizedRetention A q hA hq
    gamma alpha alphaPrime hgamma halpha halphaPrime hgammaq hcardgap hmassgap K0 hK0
  refine ⟨rho0, hrho0, hrho20, ?_⟩
  intro iota delta Cu u T U t1 tTau a p b m N shift Z jp rho R hsit hR e Cstar rung
    hin hrho varpi zeta hvarpi hzeta hwindow
  have hrows := sourceMiddle_original_rows U hin
  obtain ⟨D, E, U0, U1, hp, hcount⟩ := hret hsit hR hin.scale_ratio hin.rho_pos hrho
    (((retainedLeafChain U t1 b).tube p jp).translate shift)
    (sourceMiddleFibre U t1 tTau p b jp) Z hrows.nonempty hrows.contained hrows.card_power
    hrows.normalized_density hrows.normalized_fullness varpi zeta hvarpi hzeta hwindow
  refine ⟨D, E, U0, U1, hrows, {
    paid := hp
    count := hcount
    subset := hp.handBack.subset
    nonempty := hp.prepared.nonempty
    cardinality_retained := ?_
    cardinality_upper := Finset.card_le_card hp.handBack.subset
    mass_retained := ?_
    original_fullness := hrows.normalized_fullness
    original_density := hrows.original_density
    retained_fullness := hp.handBack.fullness_ge
    vns_fullness := ?_
    retained_density := hp.handBack.maxDensity_le
    uniform := hp.prepared.uniform
    normalized_multiplicity := hrows.normalized_multiplicity
    multiplicity_retained := ?_ }⟩
  · have hh := mul_le_mul_of_nonneg_left hp.card_paid
      (Real.rpow_nonneg rho.coe_nonneg A)
    have hr : (0 : Real) < rho := by exact_mod_cast hin.rho_pos
    simpa [← mul_assoc, ← Real.rpow_add hr, Real.rpow_zero] using hh
  · simpa [ENNReal.div_eq_inv_mul, ENNReal.ofReal_div_of_pos (by norm_num : (0 : Real) < 512)]
      using hp.mass_paid
  · have hr1 : (rho : ENNReal) <= 1 := by exact_mod_cast hin.rho_le_one
    exact (ENNReal.rpow_le_rpow_of_exponent_ge hr1 hetaD).trans hp.handBack.fullness_ge
  · rw [← hrows.normalized_multiplicity]
    exact hp.handBack.multiplicity_le

end Kakeya.ML2Assembly
