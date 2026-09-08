/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factorization
public import Kakeya.DimensionThree.MainLemma2.BallFactoringLemma92

/-! # Weighted biased factoring on complete descendant fibres -/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Assembly

universe u v w x

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {iota : Type u} [DecidableEq iota]

/-- The first, score-only factor of the existing biased loss L. -/
noncomputable def sourceBiasedScoreLoss (n card : Nat) (d : NNReal) (bias : Real) : ENNReal :=
  ENNReal.ofReal (1 + Real.logb 2 ((card : Real) *
    ((2 : Real) ^ n / ((Metric.lt_volume_convexHull.c n : Real) * (d : Real) ^ n)) ^ bias))

/-- The chosen score bin consists of entire original greedy parts. -/
structure SourceWeightedScoreBin (I : Finset iota) (V : iota -> ConvexSpaceBody E)
    (d : NNReal) (bias : Real) (weight : iota -> ENNReal)
    (A : Finset (Finset iota)) : Prop where
  subset : A ⊆ (Kakeya.greedyPartitionScore (Kakeya.biasedScore V bias) I).parts
  nonempty : A.Nonempty
  loss : (∑ t ∈ (Kakeya.greedyPartitionScore (Kakeya.biasedScore V bias) I).parts,
    ∑ i ∈ t, weight i) <= sourceBiasedScoreLoss (Module.finrank Real E) I.card d bias *
      ∑ t ∈ A, ∑ i ∈ t, weight i
  scores : forall t, t ∈ A -> forall t', t' ∈ A ->
    Kakeya.biasedScore V bias t <= 2 * Kakeya.biasedScore V bias t'
  weight_pos : 0 < ∑ t ∈ A, ∑ i ∈ t, weight i
  weight_finite : (∑ t ∈ A, ∑ i ∈ t, weight i) < (⊤ : ENNReal)
  score_range : forall t,
    t ∈ (Kakeya.greedyPartitionScore (Kakeya.biasedScore V bias) I).parts ->
    Kakeya.biasedScore V bias t ∈ Set.Icc
      ((2 : ENNReal) ^ (-(Module.finrank Real E : Real) * bias))
      ((I.card : ENNReal) * ((Metric.lt_volume_convexHull.c (Module.finrank Real E) : ENNReal) *
        (d : ENNReal) ^ Module.finrank Real E) ^ (-bias))

/-- Both bins, the original parts and hulls, and the actual biased factorization. -/
structure SourceWeightedBiasedSelection (I : Finset iota) (V : iota -> ConvexSpaceBody E)
    (d : NNReal) (bias : Real) (weight : iota -> ENNReal) where
  scoreParts : Finset (Finset iota)
  parts : Finset (Finset iota)
  selected : Finset iota
  factor : BiasedFactorization selected V closedUnitBall bias
    (nonempty_biasedFactorization.C (Module.finrank Real E) bias)
  score_bin : SourceWeightedScoreBin I V d bias weight scoreParts
  parts_subset : parts ⊆ scoreParts
  parts_nonempty : parts.Nonempty
  selected_eq : selected = parts.sup id
  selected_subset : selected ⊆ I
  selected_nonempty : selected.Nonempty
  factor_parts : factor.parts = parts
  dimensions : forall t, t ∈ parts -> forall t', t' ∈ parts ->
    forall k : Fin (Module.finrank Real E),
      ethickness Real (t.convexHull_biUnion V).carrier k <=
        2 * ethickness Real (t'.convexHull_biUnion V).carrier k
  dimension_loss : (∑ t ∈ scoreParts, ∑ i ∈ t, weight i) <=
    ENNReal.ofReal (1 + Real.logb 2 (1 / d)) ^ Module.finrank Real E *
      ∑ t ∈ parts, ∑ i ∈ t, weight i
  weight_loss : (∑ i ∈ I, weight i) <=
    nonempty_biasedFactorization.L (Module.finrank Real E) I.card d bias *
      ∑ i ∈ selected, weight i
  selected_weight_pos : 0 < ∑ i ∈ selected, weight i
  selected_weight_finite : (∑ i ∈ selected, weight i) < (⊤ : ENNReal)
  part_disjoint : (parts : Set (Finset iota)).PairwiseDisjoint id
  exact_fibre : forall t, t ∈ parts -> factor.toFactorFamily.fiber t = t
  exact_hull : forall t, t ∈ parts -> factor.toFactorFamily.outerBody t = t.convexHull_biUnion V
  hull_volume_pos : forall t, t ∈ parts -> 0 < volume (t.convexHull_biUnion V).carrier
  hull_volume_finite : forall t, t ∈ parts ->
    volume (t.convexHull_biUnion V).carrier < (⊤ : ENNReal)

/-- An actual labelled partition into full descendant cells, before selection. -/
structure SourceDescendantPartition {kappa : Type v} [DecidableEq kappa]
    (F : Finset iota) (I : Finset kappa) where
  cells : kappa -> Finset iota
  assign : iota -> kappa
  assigned_mem : forall i, i ∈ F -> assign i ∈ I
  cells_eq : forall j, j ∈ I -> cells j = {i ∈ F | assign i = j}
  cells_nonempty : forall j, j ∈ I -> (cells j).Nonempty
  union_eq : I.biUnion cells = F
  disjoint : (I : Set kappa).PairwiseDisjoint cells

/-- The weight is the unchanged shading mass of the entire assigned cell. -/
noncomputable def sourceDescendantWeight {kappa : Type v} [DecidableEq kappa]
    {F : Finset iota} {I : Finset kappa} (p : SourceDescendantPartition F I)
    (Z : iota -> ShadedBody E) (j : kappa) : ENNReal :=
  ∑ i ∈ p.cells j, volume (Z i).shade

/-- Selected cells retain their whole assigned leaf fibres. -/
def sourceDescendantUnion {kappa : Type v} [DecidableEq kappa]
    {F : Finset iota} {I : Finset kappa} (p : SourceDescendantPartition F I)
    (I' : Finset kappa) : Finset iota := I'.biUnion p.cells

/-- Exact leaf identities and the same single cell-weight loss. -/
structure SourceDescendantMassLift {kappa : Type v} [DecidableEq kappa]
    {F : Finset iota} {I : Finset kappa} (p : SourceDescendantPartition F I)
    (Z : iota -> ShadedBody E) (I' : Finset kappa) (loss : ENNReal) : Prop where
  subset : sourceDescendantUnion p I' ⊆ F
  nonempty : (sourceDescendantUnion p I').Nonempty
  fibre_eq : forall j, j ∈ I ->
    {i ∈ sourceDescendantUnion p I' | p.assign i = j} = if j ∈ I' then p.cells j else ∅
  cell_inter : forall j, j ∈ I ->
    sourceDescendantUnion p I' ∩ p.cells j = if j ∈ I' then p.cells j else ∅
  grouped_fibre : forall T : Finset kappa, T ⊆ I' ->
    {i ∈ sourceDescendantUnion p I' | p.assign i ∈ T} = sourceDescendantUnion p T
  disjoint : (I' : Set kappa).PairwiseDisjoint p.cells
  original_mass_eq : (∑ i ∈ F, volume (Z i).shade) = ∑ j ∈ I, sourceDescendantWeight p Z j
  retained_mass_eq : (∑ i ∈ sourceDescendantUnion p I', volume (Z i).shade) =
    ∑ j ∈ I', sourceDescendantWeight p Z j
  mass_loss : (∑ i ∈ F, volume (Z i).shade) <=
    loss * ∑ i ∈ sourceDescendantUnion p I', volume (Z i).shade
  retained_mass_pos : 0 < ∑ i ∈ sourceDescendantUnion p I', volume (Z i).shade
  retained_mass_finite : (∑ i ∈ sourceDescendantUnion p I', volume (Z i).shade) < (⊤ : ENNReal)

/-- The actual reference container, without identifying it with the source parent. -/
noncomputable def sourceAffineReference (f : E ≃ᵃ[Real] E) : ConvexSpaceBody E :=
  closedUnitBall.mapAffine f.symm

/-- One parent's constructed selection, complete leaves, and transported biased rows. -/
structure SourceAffineWeightedParent {kappa : Type v} [DecidableEq kappa]
    {F : Finset iota} {I : Finset kappa} (p : SourceDescendantPartition F I)
    (Z : iota -> ShadedBody E) (V : kappa -> ConvexSpaceBody E)
    (parent : ConvexSpaceBody E) (f : E ≃ᵃ[Real] E)
    (comparison d : NNReal) (bias : Real) where
  selection : SourceWeightedBiasedSelection I (fun j => (V j).mapAffine f)
    d bias (sourceDescendantWeight p Z)
  lift : SourceDescendantMassLift p Z selection.selected
    (nonempty_biasedFactorization.L (Module.finrank Real E) I.card d bias)
  factor_leaf_union : sourceDescendantUnion p selection.selected =
    selection.parts.biUnion (fun t => sourceDescendantUnion p t)
  factor_leaf_disjoint : (selection.parts : Set (Finset kappa)).PairwiseDisjoint
    (fun t => sourceDescendantUnion p t)
  factor_leaf_fibre : forall t, t ∈ selection.parts ->
    {i ∈ sourceDescendantUnion p selection.selected |
      selection.factor.toFactorFamily.parent (p.assign i) = t} = sourceDescendantUnion p t
  factor_leaf_mass : forall t, t ∈ selection.parts ->
    (∑ i ∈ sourceDescendantUnion p t, volume (Z i).shade) =
      ∑ j ∈ t, sourceDescendantWeight p Z j
  parent_in_reference : parent <= sourceAffineReference f
  reference_map : (sourceAffineReference f).mapAffine f = closedUnitBall
  reference_volume : volume (sourceAffineReference f).carrier <=
    (comparison : ENNReal) * volume parent.carrier
  reference_pos : 0 < volume (sourceAffineReference f).carrier
  reference_finite : volume (sourceAffineReference f).carrier < (⊤ : ENNReal)
  parent_pos : 0 < volume parent.carrier
  parent_finite : volume parent.carrier < (⊤ : ENNReal)
  jacobian_pos : 0 < Kakeya.affineJacobian f
  jacobian_finite : Kakeya.affineJacobian f < ⊤
  hull_map : forall t, t ∈ selection.parts ->
    (t.convexHull_biUnion V).mapAffine f = t.convexHull_biUnion (fun j => (V j).mapAffine f)
  hull_contained : forall t, t ∈ selection.parts -> t.convexHull_biUnion V <= parent
  hull_pos : forall t, t ∈ selection.parts -> 0 < volume (t.convexHull_biUnion V).carrier
  hull_finite : forall t, t ∈ selection.parts ->
    volume (t.convexHull_biUnion V).carrier < (⊤ : ENNReal)
  hull_volume_map : forall t, t ∈ selection.parts ->
    volume (t.convexHull_biUnion (fun j => (V j).mapAffine f)).carrier =
      Kakeya.affineJacobian f * volume (t.convexHull_biUnion V).carrier
  reference_volume_map : volume (closedUnitBall (E := E)).carrier =
    Kakeya.affineJacobian f * volume (sourceAffineReference f).carrier
  ratio_map : forall t, t ∈ selection.parts ->
    volume (t.convexHull_biUnion (fun j => (V j).mapAffine f)).carrier /
        volume (closedUnitBall (E := E)).carrier =
      volume (t.convexHull_biUnion V).carrier / volume (sourceAffineReference f).carrier
  density : forall t, t ∈ selection.parts -> forall K : ConvexSpaceBody E,
    Kakeya.densityIn t V K <=
      (nonempty_biasedFactorization.C (Module.finrank Real E) bias : ENNReal) *
        (volume K.carrier / volume (t.convexHull_biUnion V).carrier) ^ bias *
          Kakeya.densityIn t V (t.convexHull_biUnion V)
  capture_reference : forall t, t ∈ selection.parts ->
    (nonempty_biasedFactorization.C (Module.finrank Real E) bias : ENNReal)⁻¹ *
      (volume (t.convexHull_biUnion V).carrier / volume (sourceAffineReference f).carrier) ^ bias *
        Kakeya.maxDensity selection.selected V <= Kakeya.densityIn t V (t.convexHull_biUnion V)
  outer_katzTao : forall t, t ∈ selection.parts ->
    ConvexSpaceBody.IsKatzTao selection.parts (fun t' => t'.convexHull_biUnion V)
      ((nonempty_biasedFactorization.C (Module.finrank Real E) bias : ENNReal) *
        (volume (t.convexHull_biUnion V).carrier / volume (sourceAffineReference f).carrier) ^ (-bias))
  capture_parent_paid : forall t, t ∈ selection.parts ->
    (nonempty_biasedFactorization.C (Module.finrank Real E) bias : ENNReal)⁻¹ *
      (comparison : ENNReal) ^ (-bias) *
        (volume (t.convexHull_biUnion V).carrier / volume parent.carrier) ^ bias *
          Kakeya.maxDensity selection.selected V <= Kakeya.densityIn t V (t.convexHull_biUnion V)

/-- B1: select a biased score bin using arbitrary positive finite weight. -/
theorem sourceBiased_exists_weightedScoreBin (I : Finset iota) (hI : I.Nonempty)
    (V : iota -> ConvexSpaceBody E) {d : NNReal} (hd : 0 < d)
    {bias : Real} (hbias : 0 < bias)
    (hball : forall i, i ∈ I -> (V i).carrier ⊆ closedBall (0 : E) 1)
    (hthick : forall i, i ∈ I -> (d : ENNReal) <= ethickness.scale Real (V i).carrier)
    (weight : iota -> ENNReal) (hweight : 0 < ∑ i ∈ I, weight i)
    (hfinite : (∑ i ∈ I, weight i) < (⊤ : ENNReal)) :
    exists A : Finset (Finset iota), SourceWeightedScoreBin I V d bias weight A := by
  classical
  let P0 := Kakeya.greedyPartitionScore (Kakeya.biasedScore V bias) I
  have hzero : Kakeya.biasedScore V bias (∅ : Finset iota) = 0 := by
    simp [Kakeya.biasedScore]
  have hd1 : d ≤ 1 := ethickness.le_of_le_scale_of_subset hball hthick hI
  let n := Module.finrank Real E
  let c := Metric.lt_volume_convexHull.c n
  let a := (2 : Real) ^ (-(n : Real) * bias)
  let b := (I.card : Real) * ((c : Real) * (d : Real) ^ n) ^ (-bias)
  have ha : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
  have hc : 0 < (c : Real) * (d : Real) ^ n :=
    mul_pos (mod_cast Metric.lt_volume_convexHull.c_pos n) (pow_pos (mod_cast hd) n)
  have hcalc : b / a = (I.card : Real) *
      ((2 : Real) ^ n / ((c : Real) * (d : Real) ^ n)) ^ bias := by
    dsimp [a, b]
    rw [neg_mul, Real.rpow_neg (by norm_num : (0 : Real) ≤ 2),
      Real.rpow_mul (by norm_num : (0 : Real) ≤ 2), Real.rpow_natCast,
      Real.rpow_neg hc.le, Real.div_rpow (by positivity) hc.le]
    simp only [div_eq_mul_inv, inv_inv]
    ring
  have hab : a ≤ b := (one_le_div ha).mp (by
    rw [hcalc]
    exact nonempty_biasedFactorization.one_le_range_ratio hd hd1 hbias
      (Finset.one_le_card.mpr hI))
  have hrange : ∀ t ∈ P0.parts, Kakeya.biasedScore V bias t ∈ Set.Icc
      ((2 : ENNReal) ^ (-(n : Real) * bias))
      ((I.card : ENNReal) * ((c : ENNReal) * (d : ENNReal) ^ n) ^ (-bias)) := by
    intro t ht
    have hmax : ∀ t' ⊆ t, Kakeya.biasedScore V bias t' ≤ Kakeya.biasedScore V bias t :=
      fun _ hsub => (Kakeya.le_maxScore _ hsub).trans_eq
        (Kakeya.score_eq_maxScore_of_mem_greedyPartition hzero ht).symm
    exact ⟨Kakeya.biasedScore_lower_bound hd hbias hball hthick
      (P0.nonempty_of_mem_parts ht) (P0.subset ht) hmax,
      Kakeya.biasedScore_upper_bound hd hbias hthick
        (P0.nonempty_of_mem_parts ht) (P0.subset ht)⟩
  have hrange' : ∀ t ∈ P0.parts,
      Kakeya.biasedScore V bias t ∈ Set.Icc (ENNReal.ofReal a) (ENNReal.ofReal b) := by
    intro t ht
    have hlo := (hrange t ht).1
    have hhi := (hrange t ht).2
    constructor
    · simpa [a, ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : Real) < 2)] using hlo
    · dsimp [b]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_rpow_of_pos hc,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
      simpa using hhi
  obtain ⟨A, hA, hloss, hscore⟩ := ENNReal.dyadic_pigeonhole₁ P0.parts
    (fun t => ∑ i ∈ t, weight i) (Kakeya.biasedScore V bias) ha hab hrange'
  rw [hcalc] at hloss
  have htotal := P0.sum_eq_sum_parts_sum weight
  have hpos : 0 < ∑ t ∈ A, ∑ i ∈ t, weight i := by
    by_contra h
    have hz := le_antisymm (le_of_not_gt h) zero_le
    rw [hz, mul_zero, ← htotal] at hloss
    exact (not_lt_of_ge hloss) hweight
  exact ⟨A, hA, by
    by_contra h
    simp [Finset.not_nonempty_iff_eq_empty.mp h] at hpos,
    hloss, hscore, hpos,
    (Finset.sum_le_sum_of_subset hA).trans_lt (htotal ▸ hfinite), hrange⟩

/-- B2: perform both weighted bins and produce the original-constant biased factoring. -/
theorem sourceBiased_exists_weightedFactorization (I : Finset iota) (hI : I.Nonempty)
    (V : iota -> ConvexSpaceBody E) {d : NNReal} (hd : 0 < d)
    {bias : Real} (hbias : 0 < bias)
    (hball : forall i, i ∈ I -> (V i).carrier ⊆ closedBall (0 : E) 1)
    (hthick : forall i, i ∈ I -> (d : ENNReal) <= ethickness.scale Real (V i).carrier)
    (weight : iota -> ENNReal) (hweight : 0 < ∑ i ∈ I, weight i)
    (hfinite : (∑ i ∈ I, weight i) < (⊤ : ENNReal)) :
    Nonempty (SourceWeightedBiasedSelection I V d bias weight) := by
  classical
  let P0 := Kakeya.greedyPartitionScore (Kakeya.biasedScore V bias) I
  obtain ⟨A, hA⟩ := sourceBiased_exists_weightedScoreBin I hI V hd hbias
    hball hthick weight hweight hfinite
  have hrange : ∀ t ∈ A, ∀ k : Fin (Module.finrank Real E),
      ethickness Real (t.convexHull_biUnion V).carrier k ∈ Set.Icc (d : ENNReal) 1 := by
    intro t ht k
    exact ethickness_convexHullBiUnion_mem_Icc hball hthick
      (P0.nonempty_of_mem_parts (hA.subset ht)) (P0.subset (hA.subset ht)) k.2
  obtain ⟨P, hPA, hdimloss, hdims⟩ := exists_subset_ethickness_pigeonhole A
    (fun t => t.convexHull_biUnion V) (fun t => ∑ i ∈ t, weight i)
    hd (ethickness.le_of_le_scale_of_subset hball hthick hI) hrange
  have hP : P ⊆ P0.parts := hPA.trans hA.subset
  have hsub : P.sup id ⊆ I := (Finset.sup_mono hP).trans P0.sup_parts.le
  have hdis : (P : Set (Finset iota)).PairwiseDisjoint id := P0.disjoint.subset hP
  have hsum := Finset.sum_sum_eq_sum_sup_id hdis weight
  have hloss : (∑ i ∈ I, weight i) ≤
      nonempty_biasedFactorization.L (Module.finrank Real E) I.card d bias *
        ∑ i ∈ P.sup id, weight i := by
    rw [P0.sum_eq_sum_parts_sum weight, ← hsum]
    exact hA.loss.trans ((mul_assoc _ _ _).ge.trans' (mul_le_mul_right hdimloss _))
  have hpos : 0 < ∑ i ∈ P.sup id, weight i := by
    by_contra h
    have hz := le_antisymm (le_of_not_gt h) zero_le
    rw [hz, mul_zero] at hloss
    exact (not_lt_of_ge hloss) hweight
  have hselected : (P.sup id).Nonempty := by
    by_contra h
    simp [Finset.not_nonempty_iff_eq_empty.mp h] at hpos
  have hPne : P.Nonempty := by
    by_contra h
    simp [Finset.not_nonempty_iff_eq_empty.mp h] at hselected
  have hscores : ∀ t ∈ P, ∀ t' ∈ P,
      Kakeya.biasedScore V bias t ≤ 2 * Kakeya.biasedScore V bias t' :=
    fun t ht t' ht' => hA.scores t (hPA ht) t' (hPA ht')
  have htwo : (2 : ENNReal) ≤
      (nonempty_biasedFactorization.C (Module.finrank Real E) bias : ENNReal) := by
    have hc : (1 : ENNReal) ≤ (Metric.volume_comparison.C (Module.finrank Real E) : ENNReal) := by
      apply ENNReal.coe_le_coe.mpr
      have hval : (Metric.volume_comparison.C (Module.finrank Real E) : Real) =
          (4 : Real) ^ Module.finrank Real E * (Nat.factorial (Module.finrank Real E) : Real) := by
        dsimp [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
        push_cast
        field_simp
      have hp : (1 : Real) ≤ (4 : Real) ^ Module.finrank Real E := one_le_pow₀ (by norm_num)
      have hf : (1 : Real) ≤ (Nat.factorial (Module.finrank Real E) : Real) :=
        mod_cast Nat.succ_le_of_lt (Nat.factorial_pos _)
      have hh : (1 : Real) ≤ Metric.volume_comparison.C (Module.finrank Real E) := by
        rw [hval]
        exact one_le_mul_of_one_le_of_one_le hp hf
      exact mod_cast hh
    change 2 ≤ ((2 * Metric.volume_comparison.C (Module.finrank Real E) ^ bias : NNReal) : ENNReal)
    rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero (Metric.volume_comparison.C_pos _).ne',
      ENNReal.coe_ofNat]
    calc
      (2 : ENNReal) = 2 * (1 : ENNReal) ^ bias := by simp
      _ ≤ _ := mul_le_mul_right (ENNReal.rpow_le_rpow hc hbias.le) _
  let B : BiasedFactorization (P.sup id) V closedUnitBall bias
      (nonempty_biasedFactorization.C (Module.finrank Real E) bias) := {
    toFinpartition := P0.ofSubset hP rfl
    contained := fun i hi => SetLike.coe_subset_coe.mpr (hball i (hsub hi))
    densityIn_le_biased := fun t ht K =>
      (nonempty_biasedFactorization.densityIn_le_biased hd hbias hball hthick hP hscores
        (ht : t ∈ P) K).trans (by gcongr)
    maxDensity_le_densityIn_biased := fun t ht =>
      le_trans (by gcongr) (nonempty_biasedFactorization.maxDensity_le_mul_biased
        hd hbias hball hthick hP hscores (ht : t ∈ P))
    isKatzTao := fun t ht => nonempty_biasedFactorization.maxDensity_parts_le_biased
      hd hbias hball hthick hP hscores hdims (ht : t ∈ P)
    simDims := fun t ht t' ht' k => by
      by_cases hk : k < Module.finrank Real E
      · exact (hdims t ht t' ht' ⟨k, hk⟩).trans (mul_le_mul_left htwo _)
      · simp [ethickness_eq_zero_of_finrank_le (Nat.le_of_not_gt hk)] }
  refine ⟨{
    scoreParts := A, parts := P, selected := P.sup id, factor := B
    score_bin := hA, parts_subset := hPA, parts_nonempty := hPne
    selected_eq := rfl, selected_subset := hsub, selected_nonempty := hselected
    factor_parts := rfl, dimensions := hdims, dimension_loss := hdimloss
    weight_loss := hloss, selected_weight_pos := hpos
    selected_weight_finite := (Finset.sum_le_sum_of_subset hsub).trans_lt hfinite
    part_disjoint := hdis, exact_fibre := fun _ ht => B.toFactorFamily_fiber ht
    exact_hull := fun _ _ => rfl
    hull_volume_pos := ?_, hull_volume_finite := fun t _ => (t.convexHull_biUnion V).isCompact.measure_lt_top }⟩
  intro t ht
  exact lt_of_lt_of_le (ENNReal.mul_pos
    (ENNReal.coe_pos.mpr (Metric.lt_volume_convexHull.c_pos _)).ne'
    (pow_ne_zero _ (ENNReal.coe_pos.mpr hd).ne'))
    (Kakeya.volume_convexHullBiUnion_mem_Icc hball hthick
      (P0.nonempty_of_mem_parts (hP ht)) (P0.subset (hP ht))).1

/-- B3: only a nonempty union of whole parts is restricted; all retained hulls stay exact. -/
theorem sourceBiased_restrict_wholeParts {I : Finset iota} {V : iota -> ConvexSpaceBody E}
    {U : ConvexSpaceBody E} {bias : Real} {C : NNReal}
    (B : BiasedFactorization I V U bias C) (Q : Finset (Finset iota))
    (hQ : Q ⊆ B.parts) (hQne : Q.Nonempty) :
    exists B' : BiasedFactorization (Q.sup id) V U bias C,
      B'.parts = Q ∧ B'.parts.Nonempty ∧ Q.sup id ⊆ I ∧
      Kakeya.maxDensity (Q.sup id) V <= Kakeya.maxDensity I V ∧
      (forall t, t ∈ Q -> B'.toFactorFamily.fiber t = B.toFactorFamily.fiber t ∧
        B'.toFactorFamily.outerBody t = B.toFactorFamily.outerBody t) := by
  classical
  have hsub : Q.sup id ⊆ I := (Finset.sup_mono hQ).trans B.sup_parts.le
  have hmax : Kakeya.maxDensity (Q.sup id) V ≤ Kakeya.maxDensity I V :=
    Kakeya.maxDensity_mono V hsub
  let B' : BiasedFactorization (Q.sup id) V U bias C := {
    toFinpartition := B.toFinpartition.ofSubset hQ rfl
    contained := fun i hi => B.contained i (hsub hi)
    densityIn_le_biased := fun t ht => B.densityIn_le_biased t (hQ ht)
    maxDensity_le_densityIn_biased := fun t ht =>
      (mul_le_mul_right hmax _).trans (B.maxDensity_le_densityIn_biased t (hQ ht))
    isKatzTao := fun t ht => (B.isKatzTao t (hQ ht)).subset hQ
    simDims := fun t ht t' ht' => B.simDims t (hQ ht) t' (hQ ht') }
  refine ⟨B', rfl, hQne, hsub, hmax, ?_⟩
  intro t ht
  exact ⟨(B'.toFactorFamily_fiber ht).trans (B.toFactorFamily_fiber (hQ ht)).symm, rfl⟩

/-- B4: lift a paid cell-weight row to exactly its complete assigned leaf family. -/
theorem sourceBiased_completeDescendant_massLift {kappa : Type v} [DecidableEq kappa]
    {F : Finset iota} {I : Finset kappa} (p : SourceDescendantPartition F I)
    (Z : iota -> ShadedBody E) (I' : Finset kappa) (hI' : I' ⊆ I)
    (loss : ENNReal) (hloss : loss < ⊤)
    (hweight : 0 < ∑ j ∈ I, sourceDescendantWeight p Z j)
    (hpaid : (∑ j ∈ I, sourceDescendantWeight p Z j) <=
      loss * ∑ j ∈ I', sourceDescendantWeight p Z j) :
    SourceDescendantMassLift p Z I' loss := by
  classical
  have hmem : ∀ T ⊆ I, ∀ i,
      i ∈ sourceDescendantUnion p T ↔ i ∈ F ∧ p.assign i ∈ T := by
    intro T hT i
    simp only [sourceDescendantUnion, Finset.mem_biUnion]
    constructor
    · rintro ⟨j, hj, hij⟩
      rw [p.cells_eq j (hT hj)] at hij
      obtain ⟨hi, heq⟩ := Finset.mem_filter.mp hij
      exact ⟨hi, heq ▸ hj⟩
    · rintro ⟨hi, hj⟩
      refine ⟨p.assign i, hj, ?_⟩
      rw [p.cells_eq _ (hT hj)]
      exact Finset.mem_filter.mpr ⟨hi, rfl⟩
  have hmass : ∀ T ⊆ I,
      (∑ i ∈ sourceDescendantUnion p T, volume (Z i).shade) =
        ∑ j ∈ T, sourceDescendantWeight p Z j := by
    intro T hT
    exact Finset.sum_biUnion (p.disjoint.subset hT)
  have horiginal : (∑ i ∈ F, volume (Z i).shade) =
      ∑ j ∈ I, sourceDescendantWeight p Z j := by
    simpa only [sourceDescendantUnion, p.union_eq] using hmass I Finset.Subset.rfl
  have hretained := hmass I' hI'
  have hpos : 0 < ∑ i ∈ sourceDescendantUnion p I', volume (Z i).shade := by
    rw [hretained]
    by_contra h
    have hz := le_antisymm (le_of_not_gt h) zero_le
    rw [hz, mul_zero] at hpaid
    exact (not_lt_of_ge hpaid) hweight
  refine {
    subset := fun i hi => ((hmem I' hI' i).mp hi).1
    nonempty := ?_
    fibre_eq := ?_
    cell_inter := ?_
    grouped_fibre := ?_
    disjoint := p.disjoint.subset hI'
    original_mass_eq := horiginal
    retained_mass_eq := hretained
    mass_loss := by rwa [horiginal, hretained]
    retained_mass_pos := hpos
    retained_mass_finite := ?_ }
  · by_contra h
    simp [Finset.not_nonempty_iff_eq_empty.mp h] at hpos
  · intro j hj
    ext i
    by_cases hj' : j ∈ I'
    · simp [hj', hmem I' hI', p.cells_eq j hj]
      aesop
    · simp [hj', hmem I' hI']
      intro _ hm heq
      exact hj' (heq ▸ hm)
  · intro j hj
    ext i
    by_cases hj' : j ∈ I'
    · simp [hj', hmem I' hI', p.cells_eq j hj]
      aesop
    · simp [hj', hmem I' hI', p.cells_eq j hj]
      intro _ hm _ heq
      exact hj' (heq ▸ hm)
  · intro T hT
    ext i
    simp only [Finset.mem_filter, hmem I' hI', hmem T (hT.trans hI')]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hT h.2⟩, h.2⟩⟩
  · apply ENNReal.sum_lt_top.mpr
    intro i hi
    exact (measure_mono (Z i).shade_subset).trans_lt
      (Z i).isCompact'.measure_lt_top

/-- B5: independently construct each parent selection and sum with one common loss. -/
theorem sourceBiased_exists_parentAggregation
    {kappa : Type v} [DecidableEq kappa] {jota : Type x} [DecidableEq jota]
    (J : Finset jota) (hJ : J.Nonempty) (F : jota -> Finset iota) (I : jota -> Finset kappa)
    (p : forall j, SourceDescendantPartition (F j) (I j))
    (hdisjoint : (J : Set jota).PairwiseDisjoint F)
    (Z : iota -> ShadedBody E) (V : jota -> kappa -> ConvexSpaceBody E)
    (parent : jota -> ConvexSpaceBody E) (f : jota -> E ≃ᵃ[Real] E)
    (comparison d : jota -> NNReal) (bias : Real) (hbias : 0 < bias)
    (L0 : ENNReal) (hL0 : L0 < ⊤)
    (hweight : forall j, j ∈ J -> 0 < ∑ i ∈ F j, volume (Z i).shade)
    (hd : forall j, j ∈ J -> 0 < d j)
    (hcontained : forall j, j ∈ J -> forall i, i ∈ I j -> V j i <= parent j)
    (hball : forall j, j ∈ J -> (parent j).mapAffine (f j) <= closedUnitBall)
    (hthick : forall j, j ∈ J -> forall i, i ∈ I j ->
      (d j : ENNReal) <= ethickness.scale Real ((V j i).mapAffine (f j)).carrier)
    (hcomparison : forall j, j ∈ J -> 1 <= comparison j ∧
      volume (sourceAffineReference (f j)).carrier <=
        (comparison j : ENNReal) * volume (parent j).carrier)
    (hbound : forall j, j ∈ J ->
      nonempty_biasedFactorization.L (Module.finrank Real E) (I j).card (d j) bias <= L0) :
    exists (D : (j : {j // j ∈ J}) -> SourceAffineWeightedParent (p j.val) Z (V j.val)
        (parent j.val) (f j.val) (comparison j.val) (d j.val) bias)
      (F' : Finset iota),
      F' = J.attach.biUnion (fun j => sourceDescendantUnion (p j.val) (D j).selection.selected) ∧
      F' ⊆ J.biUnion F ∧ F'.Nonempty ∧
      (forall j : {j // j ∈ J}, F' ∩ F j.val =
        sourceDescendantUnion (p j.val) (D j).selection.selected) ∧
      ((J.attach : Set {j // j ∈ J}).PairwiseDisjoint
        (fun j => sourceDescendantUnion (p j.val) (D j).selection.selected)) ∧
      (∑ i ∈ J.biUnion F, volume (Z i).shade) = ∑ j ∈ J, ∑ i ∈ F j, volume (Z i).shade ∧
      (∑ i ∈ F', volume (Z i).shade) =
        ∑ j ∈ J.attach, ∑ i ∈ sourceDescendantUnion (p j.val) (D j).selection.selected,
          volume (Z i).shade ∧
      (∑ i ∈ J.biUnion F, volume (Z i).shade) <= L0 * ∑ i ∈ F', volume (Z i).shade := by
  classical
  have hmassfinite : ∀ T : Finset iota, (∑ i ∈ T, volume (Z i).shade) < (⊤ : ENNReal) := by
    intro T
    exact ENNReal.sum_lt_top.mpr fun i _ =>
      (measure_mono (Z i).shade_subset).trans_lt (Z i).isCompact'.measure_lt_top
  have hparent : ∀ j : {j // j ∈ J}, Nonempty (SourceAffineWeightedParent (p j.val) Z
      (V j.val) (parent j.val) (f j.val) (comparison j.val) (d j.val) bias) := by
    intro j
    have hm : (∑ i ∈ F j.val, volume (Z i).shade) =
        ∑ i ∈ I j.val, sourceDescendantWeight (p j.val) Z i := by
      conv_lhs => rw [← (p j.val).union_eq]
      exact Finset.sum_biUnion (p j.val).disjoint
    have hwp : 0 < ∑ i ∈ I j.val, sourceDescendantWeight (p j.val) Z i :=
      hm ▸ hweight j.val j.property
    have hwf : (∑ i ∈ I j.val, sourceDescendantWeight (p j.val) Z i) < ⊤ :=
      hm ▸ hmassfinite (F j.val)
    have hIne : (I j.val).Nonempty := by
      by_contra h
      simp [Finset.not_nonempty_iff_eq_empty.mp h] at hwp
    obtain ⟨S⟩ := sourceBiased_exists_weightedFactorization (I j.val) hIne
      (fun i => (V j.val i).mapAffine (f j.val)) (hd j.val j.property) hbias
      (fun i hi => ((mapAffine_le_mapAffine_iff (f j.val)).mpr
        (hcontained j.val j.property i hi)).trans (hball j.val j.property))
      (hthick j.val j.property) (sourceDescendantWeight (p j.val) Z) hwp hwf
    have hlift := sourceBiased_completeDescendant_massLift (p j.val) Z S.selected
      S.selected_subset _ nonempty_biasedFactorization.L_lt_top hwp S.weight_loss
    have hpart : ∀ t ∈ S.parts, t ⊆ S.selected := by
      intro t ht
      rw [S.selected_eq]
      exact Finset.le_sup (f := id) ht
    have hne : ∀ t ∈ S.parts, t.Nonempty := by
      intro t ht
      exact S.factor.nonempty_of_mem_parts (S.factor_parts ▸ ht)
    have hmem : ∀ T ⊆ I j.val, ∀ i,
        i ∈ sourceDescendantUnion (p j.val) T ↔ i ∈ F j.val ∧ (p j.val).assign i ∈ T := by
      intro T hT i
      simp only [sourceDescendantUnion, Finset.mem_biUnion]
      constructor
      · rintro ⟨k, hk, hik⟩
        rw [(p j.val).cells_eq k (hT hk)] at hik
        obtain ⟨hi, heq⟩ := Finset.mem_filter.mp hik
        exact ⟨hi, heq ▸ hk⟩
      · rintro ⟨hi, hk⟩
        refine ⟨(p j.val).assign i, hk, ?_⟩
        rw [(p j.val).cells_eq _ (hT hk)]
        exact Finset.mem_filter.mpr ⟨hi, rfl⟩
    have hmap : ∀ t ∈ S.parts, (t.convexHull_biUnion (V j.val)).mapAffine (f j.val) =
        t.convexHull_biUnion (fun i => (V j.val i).mapAffine (f j.val)) := by
      intro t ht
      apply le_antisymm
      · apply (mapAffine_le_mapAffine_iff (f j.val).symm).mp
        rw [mapAffine_symm_mapAffine]
        apply ((hne t ht).convexHull_biUnion_le_iff _ _).mpr
        intro i hi
        have hh := (mapAffine_le_mapAffine_iff (f j.val).symm).mpr
          (Finset.le_convexHull_biUnion (fun i => (V j.val i).mapAffine (f j.val)) hi)
        simpa only [mapAffine_symm_mapAffine] using hh
      · apply ((hne t ht).convexHull_biUnion_le_iff _ _).mpr
        intro i hi
        exact (mapAffine_le_mapAffine_iff (f j.val)).mpr
          (Finset.le_convexHull_biUnion (V j.val) hi)
    have hcont : ∀ t ∈ S.parts, t.convexHull_biUnion (V j.val) ≤ parent j.val := by
      intro t ht
      exact ((hne t ht).convexHull_biUnion_le_iff _ _).mpr
        fun i hi => hcontained j.val j.property i (S.selected_subset (hpart t ht hi))
    have hvolmap : ∀ t ∈ S.parts,
        volume (t.convexHull_biUnion (fun i => (V j.val i).mapAffine (f j.val))).carrier =
          Kakeya.affineJacobian (f j.val) * volume (t.convexHull_biUnion (V j.val)).carrier := by
      intro t ht
      rw [← hmap t ht, volume_mapAffine]
    have hvpos : ∀ t ∈ S.parts, 0 < volume (t.convexHull_biUnion (V j.val)).carrier := by
      intro t ht
      have hh := S.hull_volume_pos t ht
      rw [hvolmap t ht] at hh
      exact pos_iff_ne_zero.mpr fun hz => by simp [hz] at hh
    have hrefmap : (sourceAffineReference (f j.val)).mapAffine (f j.val) = closedUnitBall :=
      symm_mapAffine_mapAffine _ _
    have hrefvolmap : volume (closedUnitBall (E := E)).carrier =
        Kakeya.affineJacobian (f j.val) * volume (sourceAffineReference (f j.val)).carrier := by
      rw [← hrefmap, volume_mapAffine]
    have hrefpos : 0 < volume (sourceAffineReference (f j.val)).carrier := by
      have hh := closedUnitBall_volume_pos (E := E)
      rw [hrefvolmap] at hh
      exact pos_iff_ne_zero.mpr fun hz => by simp [hz] at hh
    have hparpos : 0 < volume (parent j.val).carrier := by
      obtain ⟨t, ht⟩ := S.parts_nonempty
      exact (hvpos t ht).trans_le (measure_mono (hcont t ht))
    have hratio : ∀ t ∈ S.parts,
        volume (t.convexHull_biUnion (fun i => (V j.val i).mapAffine (f j.val))).carrier /
          volume (closedUnitBall (E := E)).carrier =
        volume (t.convexHull_biUnion (V j.val)).carrier /
          volume (sourceAffineReference (f j.val)).carrier := by
      intro t ht
      rw [hvolmap t ht, hrefvolmap]
      exact ENNReal.mul_div_mul_left _ _ (Kakeya.affineJacobian_ne_zero _)
        (Kakeya.affineJacobian_ne_top _)
    have hcapture : ∀ t ∈ S.parts,
        (nonempty_biasedFactorization.C (Module.finrank Real E) bias : ENNReal)⁻¹ *
          (volume (t.convexHull_biUnion (V j.val)).carrier /
            volume (sourceAffineReference (f j.val)).carrier) ^ bias *
          Kakeya.maxDensity S.selected (V j.val) ≤
            Kakeya.densityIn t (V j.val) (t.convexHull_biUnion (V j.val)) := by
      intro t ht
      have hh := S.factor.maxDensity_le_densityIn_biased t (S.factor_parts ▸ ht)
      rw [hratio t ht, ← hmap t ht, Kakeya.densityIn_mapAffine, Kakeya.maxDensity_mapAffine] at hh
      exact hh
    refine ⟨{
      selection := S, lift := hlift
      factor_leaf_union := ?_
      factor_leaf_disjoint := ?_
      factor_leaf_fibre := ?_
      factor_leaf_mass := ?_
      parent_in_reference := ?_
      reference_map := hrefmap
      reference_volume := (hcomparison j.val j.property).2
      reference_pos := hrefpos
      reference_finite := (sourceAffineReference (f j.val)).isCompact.measure_lt_top
      parent_pos := hparpos
      parent_finite := (parent j.val).isCompact.measure_lt_top
      jacobian_pos := pos_iff_ne_zero.mpr (Kakeya.affineJacobian_ne_zero _)
      jacobian_finite := lt_top_iff_ne_top.mpr (Kakeya.affineJacobian_ne_top _)
      hull_map := hmap, hull_contained := hcont, hull_pos := hvpos
      hull_finite := fun t _ => (t.convexHull_biUnion (V j.val)).isCompact.measure_lt_top
      hull_volume_map := hvolmap, reference_volume_map := hrefvolmap, ratio_map := hratio
      density := ?_, capture_reference := hcapture, outer_katzTao := ?_
      capture_parent_paid := ?_ }⟩
    · ext i
      simp only [Finset.mem_biUnion, hmem S.selected S.selected_subset]
      constructor
      · rintro ⟨hi, hm⟩
        rw [S.selected_eq] at hm
        obtain ⟨t, ht, hit⟩ := Finset.mem_sup.mp hm
        exact ⟨t, ht, (hmem t ((hpart t ht).trans S.selected_subset) i).mpr ⟨hi, hit⟩⟩
      · rintro ⟨t, ht, hi⟩
        obtain ⟨hiF, hit⟩ := (hmem t ((hpart t ht).trans S.selected_subset) i).mp hi
        exact ⟨hiF, hpart t ht hit⟩
    · intro t ht t' ht' hneq
      apply Finset.disjoint_left.mpr
      intro i hi hi'
      exact Finset.disjoint_left.mp (S.part_disjoint ht ht' hneq)
        ((hmem t ((hpart t ht).trans S.selected_subset) i).mp hi).2
        ((hmem t' ((hpart t' ht').trans S.selected_subset) i).mp hi').2
    · intro t ht
      rw [← hlift.grouped_fibre t (hpart t ht)]
      apply Finset.filter_congr
      intro i hi
      have ha := ((hmem S.selected S.selected_subset i).mp hi).2
      have hf := S.exact_fibre t ht
      have hm := Finset.ext_iff.mp hf ((p j.val).assign i)
      simp only [ConvexSpaceBody.FactorFamily.fiber, Finset.mem_filter] at hm
      change (((p j.val).assign i ∈ S.selected ∧
        S.factor.toFactorFamily.parent ((p j.val).assign i) = t) ↔ (p j.val).assign i ∈ t) at hm
      simpa only [ha, true_and] using hm
    · intro t ht
      exact Finset.sum_biUnion ((p j.val).disjoint.subset
        ((hpart t ht).trans S.selected_subset))
    · apply (mapAffine_le_mapAffine_iff (f j.val)).mp
      rw [hrefmap]
      exact hball j.val j.property
    · intro t ht
      apply Kakeya.VeryNotSticky.densityIn_le_biased_of_mapAffine t (V j.val)
        (t.convexHull_biUnion (V j.val)) (f j.val)
      rw [hmap t ht]
      exact S.factor.densityIn_le_biased t (S.factor_parts ▸ ht)
    · intro t ht
      have hh := S.factor.isKatzTao t (S.factor_parts ▸ ht)
      change Kakeya.maxDensity S.parts _ ≤ _
      rw [← Kakeya.maxDensity_mapAffine S.parts (fun t' => t'.convexHull_biUnion (V j.val))
        (f j.val)]
      have heq : Kakeya.maxDensity S.parts
          (fun t' => (t'.convexHull_biUnion (V j.val)).mapAffine (f j.val)) =
          Kakeya.maxDensity S.parts (fun t' => t'.convexHull_biUnion
            (fun i => (V j.val i).mapAffine (f j.val))) := by
        apply Kakeya.maxDensity_congr
        exact hmap
      rw [heq]
      simpa only [ConvexSpaceBody.IsKatzTao, S.factor_parts, hratio t ht] using hh
    · intro t ht
      have hcp : (comparison j.val : ENNReal) ≠ 0 := by
        apply ne_of_gt
        exact lt_of_lt_of_le zero_lt_one (mod_cast (hcomparison j.val j.property).1)
      have hpay : (comparison j.val : ENNReal) ^ (-bias) *
          (volume (t.convexHull_biUnion (V j.val)).carrier / volume (parent j.val).carrier) ^ bias ≤
          (volume (t.convexHull_biUnion (V j.val)).carrier /
            volume (sourceAffineReference (f j.val)).carrier) ^ bias := by
        calc
          _ = (volume (t.convexHull_biUnion (V j.val)).carrier /
              ((comparison j.val : ENNReal) * volume (parent j.val).carrier)) ^ bias := by
            rw [ENNReal.rpow_neg, ENNReal.div_rpow_of_nonneg _ _ hbias.le,
              ENNReal.div_rpow_of_nonneg _ _ hbias.le,
              ENNReal.mul_rpow_of_nonneg _ _ hbias.le, div_eq_mul_inv, div_eq_mul_inv,
              ENNReal.mul_inv (Or.inl (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hcp)
                ENNReal.coe_ne_top).ne')
                (Or.inl (ENNReal.rpow_ne_top_of_nonneg hbias.le ENNReal.coe_ne_top))]
            ring
          _ ≤ _ := ENNReal.rpow_le_rpow
            (ENNReal.div_le_div_left (hcomparison j.val j.property).2 _) hbias.le
      have hpaid := mul_le_mul_left (mul_le_mul_right hpay
        ((nonempty_biasedFactorization.C (Module.finrank Real E) bias : ENNReal)⁻¹))
        (Kakeya.maxDensity S.selected (V j.val))
      have hpaid' := hpaid.trans (hcapture t ht)
      simpa only [mul_assoc] using hpaid'
  let D := fun j => Classical.choice (hparent j)
  let G := fun j : {j // j ∈ J} => sourceDescendantUnion (p j.val) (D j).selection.selected
  have hGsub : ∀ j, G j ⊆ F j.val := fun j => (D j).lift.subset
  have hGdis : (J.attach : Set {j // j ∈ J}).PairwiseDisjoint G := by
    intro j hj k hk hneq
    exact (hdisjoint j.property k.property (fun h => hneq (Subtype.ext h))).mono (hGsub j) (hGsub k)
  have hmoriginal : (∑ i ∈ J.biUnion F, volume (Z i).shade) =
      ∑ j ∈ J, ∑ i ∈ F j, volume (Z i).shade := Finset.sum_biUnion hdisjoint
  have hmselected : (∑ i ∈ J.attach.biUnion G, volume (Z i).shade) =
      ∑ j ∈ J.attach, ∑ i ∈ G j, volume (Z i).shade := Finset.sum_biUnion hGdis
  refine ⟨D, J.attach.biUnion G, rfl, ?_, ?_, ?_, hGdis, hmoriginal, hmselected, ?_⟩
  · intro i hi
    obtain ⟨j, hj, hi⟩ := Finset.mem_biUnion.mp hi
    exact Finset.mem_biUnion.mpr ⟨j.val, j.property, hGsub j hi⟩
  · obtain ⟨j, hj⟩ := hJ
    obtain ⟨i, hi⟩ := (D ⟨j, hj⟩).lift.nonempty
    exact ⟨i, Finset.mem_biUnion.mpr ⟨⟨j, hj⟩, Finset.mem_attach _ _, hi⟩⟩
  · intro j
    apply Finset.Subset.antisymm
    · intro i hi
      obtain ⟨hiG, hiF⟩ := Finset.mem_inter.mp hi
      obtain ⟨k, hk, hik⟩ := Finset.mem_biUnion.mp hiG
      by_cases heq : k = j
      · simpa [heq] using hik
      · exact False.elim (Finset.disjoint_left.mp
          (hdisjoint k.property j.property (fun h => heq (Subtype.ext h))) (hGsub k hik) hiF)
    · intro i hi
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨j, Finset.mem_attach _ _, hi⟩, hGsub j hi⟩
  · rw [hmoriginal, hmselected, Finset.mul_sum]
    rw [← Finset.sum_attach J (fun j => ∑ i ∈ F j, volume (Z i).shade)]
    apply Finset.sum_le_sum
    intro j hj
    exact (D j).lift.mass_loss.trans (mul_le_mul_left (hbound j.val j.property) _)

end Kakeya.ML2Assembly
