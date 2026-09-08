/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceWeightedBiasedFactoring
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSiteClosure

/-! # The actual biased-factor loss at a polynomially controlled normalized scale -/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Assembly

universe u v w x y

/-- Fixed data chosen before the runtime scale and all parent families. -/
structure SourceBiasedLossParameters where
  bias : Real
  bias_pos : 0 < bias
  cardCoefficient : NNReal
  cardCoefficient_one_le : 1 <= cardCoefficient
  thicknessCoefficient : NNReal
  thicknessCoefficient_pos : 0 < thicknessCoefficient
  thicknessCoefficient_le_one : thicknessCoefficient <= 1
  cardPower : NNReal
  thicknessPower : NNReal

/-- The geometric caller's exact polynomial cardinality and thickness bounds. -/
structure SourceBiasedPolynomialScale (P : SourceBiasedLossParameters)
    (delta : NNReal) (card : Nat) (d : NNReal) : Prop where
  delta_pos : 0 < delta
  delta_le_one : delta <= 1
  card_pos : 0 < card
  card_le : (card : Real) <= (P.cardCoefficient : Real) *
    (delta : Real) ^ (-(P.cardPower : Real))
  thickness_pos : 0 < d
  thickness_le_one : d <= 1
  thickness_ge : (P.thicknessCoefficient : Real) *
    (delta : Real) ^ (P.thicknessPower : Real) <= (d : Real)

/-- E1: the exact API loss has fixed logarithmic degree `n + 1`. -/
theorem sourceBiased_exists_loss_coefficient (n : Nat) (P : SourceBiasedLossParameters) :
    exists C : NNReal, 1 <= C ∧
      forall (delta d : NNReal) (card : Nat), SourceBiasedPolynomialScale P delta card d ->
        nonempty_biasedFactorization.L n card d P.bias <=
          (C : ENNReal) * Kakeya.ML2Core.polylogLoss (n + 1) delta := by
  let l2 : Real := Real.log 2
  let A : Real := (Real.log (P.cardCoefficient : Real) + P.bias *
    ((n : Real) * l2 - Real.log (Metric.lt_volume_convexHull.c n : Real) -
      (n : Real) * Real.log (P.thicknessCoefficient : Real))) / l2
  let B : Real := ((P.cardPower : Real) + P.bias * n * (P.thicknessPower : Real)) / l2
  let C1 : Real := 1 + |A| + |B|
  let C2 : Real := 1 + |Real.log (P.thicknessCoefficient : Real) / l2| +
    |(P.thicknessPower : Real) / l2|
  have hC1 : 1 <= C1 := by dsimp only [C1]; linarith [abs_nonneg A, abs_nonneg B]
  have hC2 : 1 <= C2 := by
    dsimp only [C2]
    linarith [abs_nonneg (Real.log (P.thicknessCoefficient : Real) / l2),
      abs_nonneg ((P.thicknessPower : Real) / l2)]
  have hcoef : 1 <= C1 * C2 ^ n := one_le_mul_of_one_le_of_one_le hC1 (one_le_pow₀ hC2)
  refine ⟨Real.toNNReal (C1 * C2 ^ n), ?_, ?_⟩
  · rw [← Real.toNNReal_one]
    exact Real.toNNReal_le_toNNReal hcoef
  intro delta d card hs
  have hd0 : (0 : Real) < d := by exact_mod_cast hs.thickness_pos
  have hdelta0 : (0 : Real) < delta := by exact_mod_cast hs.delta_pos
  have hcard0 : (0 : Real) < card := by exact_mod_cast hs.card_pos
  have hc0 : (0 : Real) < P.cardCoefficient := by
    exact_mod_cast (zero_lt_one.trans_le P.cardCoefficient_one_le)
  have ht0 : (0 : Real) < P.thicknessCoefficient := by exact_mod_cast P.thicknessCoefficient_pos
  have hv0 : (0 : Real) < Metric.lt_volume_convexHull.c n := by
    exact_mod_cast Metric.lt_volume_convexHull.c_pos n
  have hl20 : 0 < l2 := Real.log_pos (by norm_num)
  have hlogdelta : Real.log (delta : Real) <= 0 :=
    Real.log_nonpos hdelta0.le (by exact_mod_cast hs.delta_le_one)
  let X : Real := 1 - Real.log (delta : Real)
  have hX : 1 <= X := by dsimp [X]; linarith
  have hlogcard : Real.log (card : Real) <= Real.log (P.cardCoefficient : Real) -
      (P.cardPower : Real) * Real.log (delta : Real) := by
    have hh := Real.log_le_log hcard0 hs.card_le
    rw [Real.log_mul hc0.ne' (Real.rpow_pos_of_pos hdelta0 _).ne', Real.log_rpow hdelta0] at hh
    simpa [sub_eq_add_neg] using hh
  have hlogd : Real.log (P.thicknessCoefficient : Real) +
      (P.thicknessPower : Real) * Real.log (delta : Real) <= Real.log (d : Real) := by
    have hh := Real.log_le_log (mul_pos ht0 (Real.rpow_pos_of_pos hdelta0 _)) hs.thickness_ge
    rwa [Real.log_mul ht0.ne' (Real.rpow_pos_of_pos hdelta0 _).ne', Real.log_rpow hdelta0] at hh
  have hfirst : 1 + Real.logb 2 ((card : Real) *
      ((2 : Real) ^ n / ((Metric.lt_volume_convexHull.c n : Real) * (d : Real) ^ n)) ^ P.bias)
      <= C1 * X := by
    have hn : (0 : Real) <= n := Nat.cast_nonneg n
    have hh : Real.log (card : Real) + P.bias *
        ((n : Real) * l2 - (Real.log (Metric.lt_volume_convexHull.c n : Real) +
          (n : Real) * Real.log (d : Real))) <= A * l2 - B * l2 * Real.log (delta : Real) := by
      have hscale := mul_le_mul_of_nonneg_left hlogd (mul_nonneg P.bias_pos.le hn)
      dsimp [A, B]
      field_simp [hl20.ne']
      nlinarith
    have hlog : Real.logb 2 ((card : Real) *
        ((2 : Real) ^ n / ((Metric.lt_volume_convexHull.c n : Real) * (d : Real) ^ n)) ^ P.bias)
        <= A + B * (-Real.log (delta : Real)) := by
      rw [Real.logb, Real.log_mul hcard0.ne' (Real.rpow_pos_of_pos (by positivity) _).ne',
        Real.log_rpow (by positivity), Real.log_div (by positivity) (by positivity),
        Real.log_mul hv0.ne' (pow_pos hd0 n).ne', Real.log_pow, Real.log_pow]
      apply (div_le_iff₀ hl20).2
      dsimp [l2] at hh ⊢
      nlinarith
    have habsA := le_abs_self A
    have habsB := le_abs_self B
    have hhB := mul_le_mul_of_nonneg_right habsB (neg_nonneg.mpr hlogdelta)
    calc
      _ <= 1 + |A| + |B| * (-Real.log (delta : Real)) := by linarith only [hlog, habsA, hhB]
      _ <= C1 * X := by
        dsimp only [C1, X]
        nlinarith only [hlogdelta, abs_nonneg B,
          mul_nonneg (abs_nonneg A) (neg_nonneg.mpr hlogdelta)]
  have hsecond : 1 + Real.logb 2 (1 / (d : Real)) <= C2 * X := by
    have hh : Real.logb 2 (1 / (d : Real)) <=
        -(Real.log (P.thicknessCoefficient : Real) / l2) +
          ((P.thicknessPower : Real) / l2) * (-Real.log (delta : Real)) := by
      rw [Real.logb, one_div, Real.log_inv]
      apply (div_le_iff₀ hl20).2
      dsimp [l2]
      field_simp [hl20.ne']
      linarith
    have hca := neg_le_abs (Real.log (P.thicknessCoefficient : Real) / l2)
    have hcb := mul_le_mul_of_nonneg_right (le_abs_self ((P.thicknessPower : Real) / l2))
      (neg_nonneg.mpr hlogdelta)
    dsimp [C2, X]
    nlinarith [abs_nonneg (Real.log (P.thicknessCoefficient : Real) / l2),
      abs_nonneg ((P.thicknessPower : Real) / l2),
      mul_nonneg (abs_nonneg (Real.log (P.thicknessCoefficient : Real) / l2))
        (neg_nonneg.mpr hlogdelta)]
  have hX0 : 0 <= X := zero_le_one.trans hX
  calc
    nonempty_biasedFactorization.L n card d P.bias <=
        ENNReal.ofReal (C1 * X) * ENNReal.ofReal (C2 * X) ^ n := by
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hfirst)
        (pow_le_pow_left' (ENNReal.ofReal_le_ofReal hsecond) n)
    _ = ENNReal.ofReal (C1 * C2 ^ n) * ENNReal.ofReal (X ^ (n + 1)) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hX0,
        ENNReal.ofReal_pow (by positivity), mul_pow, pow_succ]
      ring
    _ <= _ := by
      have hp : ENNReal.ofReal (X ^ (n + 1)) <= Kakeya.ML2Core.polylogLoss (n + 1) delta :=
        ENNReal.ofReal_le_ofReal (le_max_right _ _)
      exact mul_le_mul' (le_refl (ENNReal.ofReal (C1 * C2 ^ n))) hp

/-- E2: one further fixed logarithmic power absorbs that coefficient at a positive threshold. -/
theorem sourceBiased_exists_polylog_threshold (n : Nat) (P : SourceBiasedLossParameters) :
    exists delta0 : NNReal, 0 < delta0 ∧ delta0 <= 1 ∧
      forall (delta d : NNReal) (card : Nat), delta < delta0 ->
        SourceBiasedPolynomialScale P delta card d ->
        1 <= nonempty_biasedFactorization.L n card d P.bias ∧
        nonempty_biasedFactorization.L n card d P.bias < ⊤ ∧
        nonempty_biasedFactorization.L n card d P.bias <=
          Kakeya.ML2Core.polylogLoss (n + 2) delta := by
  obtain ⟨C, hC, hbound⟩ := sourceBiased_exists_loss_coefficient n P
  let delta0 : NNReal := Real.toNNReal (Real.exp (-(C : Real)))
  have hzero : 0 < delta0 := Real.toNNReal_pos.mpr (Real.exp_pos _)
  have hone : delta0 <= 1 := by
    apply Real.toNNReal_le_one.mpr
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr C.coe_nonneg)
  refine ⟨delta0, hzero, hone, ?_⟩
  intro delta d card hsmall hs
  refine ⟨nonempty_biasedFactorization.one_le_L hs.thickness_pos hs.thickness_le_one
    P.bias_pos hs.card_pos, nonempty_biasedFactorization.L_lt_top, (hbound delta d card hs).trans ?_⟩
  have hdelta : (0 : Real) < delta := by exact_mod_cast hs.delta_pos
  have hdexp : (delta : Real) <= Real.exp (-(C : Real)) := by
    have hh : (delta : Real) < (delta0 : Real) := by exact_mod_cast hsmall
    simpa [delta0, Real.toNNReal_of_nonneg (Real.exp_pos _).le] using hh.le
  have hlog := Real.log_le_log hdelta hdexp
  rw [Real.log_exp] at hlog
  have hX : (C : Real) <= 1 - Real.log (delta : Real) := by linarith
  have hX0 : 0 <= 1 - Real.log (delta : Real) := C.coe_nonneg.trans hX
  have heq (k : Nat) : Kakeya.ML2Core.polylogLoss k delta =
      ENNReal.ofReal ((1 - Real.log (delta : Real)) ^ k) := by
    rw [Kakeya.ML2Core.polylogLoss, max_eq_right (Kakeya.ML2Core.one_le_polylog hs.delta_le_one k)]
  rw [heq, heq]
  calc (C : ENNReal) * ENNReal.ofReal ((1 - Real.log (delta : Real)) ^ (n + 1)) <=
      ENNReal.ofReal (1 - Real.log (delta : Real)) *
        ENNReal.ofReal ((1 - Real.log (delta : Real)) ^ (n + 1)) := by
        apply mul_le_mul_left
        simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hX
    _ = ENNReal.ofReal ((1 - Real.log (delta : Real)) ^ (n + 2)) := by
      rw [show n + 2 = (n + 1) + 1 by omega,
        pow_succ (1 - Real.log (delta : Real)) (n + 1),
        ENNReal.ofReal_mul (pow_nonneg hX0 (n + 1))]
      exact mul_comm _ _

/-- E3: fixed finitely many rung parameters share one exponent and one positive threshold. -/
theorem sourceBiased_exists_finite_polylog_threshold
    {theta : Type y} [DecidableEq theta] (T : Finset theta)
    (n : theta -> Nat) (P : theta -> SourceBiasedLossParameters) :
    exists (K : Nat) (delta0 : NNReal), 1 <= K ∧ 0 < delta0 ∧ delta0 <= 1 ∧
      (forall t, t ∈ T -> n t + 2 <= K) ∧
      forall (delta : NNReal), delta < delta0 -> forall t, t ∈ T ->
        forall (d : NNReal) (card : Nat), SourceBiasedPolynomialScale (P t) delta card d ->
          1 <= nonempty_biasedFactorization.L (n t) card d (P t).bias ∧
          nonempty_biasedFactorization.L (n t) card d (P t).bias < ⊤ ∧
          nonempty_biasedFactorization.L (n t) card d (P t).bias <=
            Kakeya.ML2Core.polylogLoss K delta := by
  classical
  choose threshold hpos hone hbound using fun t => sourceBiased_exists_polylog_threshold (n t) (P t)
  let ceilings : Finset NNReal := insert 1 (T.image threshold)
  have hne : ceilings.Nonempty := ⟨1, by simp [ceilings]⟩
  let delta0 := ceilings.min' hne
  have hd0 : 0 < delta0 := by
    change 0 < ceilings.min' hne
    have hh := ceilings.min'_mem hne
    rcases Finset.mem_insert.mp hh with hh | hh
    · simpa [hh]
    · obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hh
      rw [← ht]
      exact hpos t
  let K := max 1 (T.sup fun t => n t + 2)
  have hK (t : theta) (ht : t ∈ T) : n t + 2 <= K :=
    (Finset.le_sup (f := fun t => n t + 2) ht).trans (le_max_right _ _)
  refine ⟨K, delta0, le_max_left _ _, hd0,
    ceilings.min'_le _ (Finset.mem_insert_self _ _), hK, ?_⟩
  intro delta hdelta t ht d card hs
  have hdt : delta < threshold t := hdelta.trans_le
    (ceilings.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, ht, rfl⟩)))
  obtain ⟨hL1, hLt, hL⟩ := hbound t delta d card hdt hs
  refine ⟨hL1, hLt, hL.trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  apply max_le_max_left
  apply pow_le_pow_right₀ ?_ (hK t ht)
  have hl := Real.log_nonpos (show (0 : Real) <= delta from delta.coe_nonneg)
    (show (delta : Real) <= 1 by exact_mod_cast hs.delta_le_one)
  linarith

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {iota : Type u} [DecidableEq iota]
  {kappa : Type v} [DecidableEq kappa] {jota : Type x} [DecidableEq jota]

/-- The unchanged geometric inputs of B5, with no loss-bound field. -/
structure SourceBiasedParentGeometry
    (J : Finset jota) (F : jota -> Finset iota) (I : jota -> Finset kappa)
    (Z : iota -> ShadedBody E) (V : jota -> kappa -> ConvexSpaceBody E)
    (parent : jota -> ConvexSpaceBody E) (f : jota -> E ≃ᵃ[Real] E)
    (comparison d : jota -> NNReal) : Prop where
  parents_nonempty : J.Nonempty
  parent_fibres_disjoint : (J : Set jota).PairwiseDisjoint F
  mass_pos : forall j, j ∈ J -> 0 < ∑ i ∈ F j, volume (Z i).shade
  thickness_pos : forall j, j ∈ J -> 0 < d j
  contained : forall j, j ∈ J -> forall i, i ∈ I j -> V j i <= parent j
  normalized_ball : forall j, j ∈ J -> (parent j).mapAffine (f j) <= closedUnitBall
  normalized_thickness : forall j, j ∈ J -> forall i, i ∈ I j ->
    (d j : ENNReal) <= ethickness.scale Real ((V j i).mapAffine (f j)).carrier
  comparison_one_le : forall j, j ∈ J -> 1 <= comparison j
  reference_comparison : forall j, j ∈ J ->
    volume (sourceAffineReference (f j)).carrier <=
      (comparison j : ENNReal) * volume (parent j).carrier

/-- B5's actual selections, full affine data and unchanged eight aggregate conclusions. -/
structure SourceBiasedParentAggregation
    (J : Finset jota) {F : jota -> Finset iota} {I : jota -> Finset kappa}
    (p : forall j, SourceDescendantPartition (F j) (I j))
    (Z : iota -> ShadedBody E) (V : jota -> kappa -> ConvexSpaceBody E)
    (parent : jota -> ConvexSpaceBody E) (f : jota -> E ≃ᵃ[Real] E)
    (comparison d : jota -> NNReal) (bias : Real) (L0 : ENNReal) where
  data : (j : {j // j ∈ J}) -> SourceAffineWeightedParent (p j.val) Z (V j.val)
    (parent j.val) (f j.val) (comparison j.val) (d j.val) bias
  retained : Finset iota
  retained_eq : retained =
    J.attach.biUnion (fun j => sourceDescendantUnion (p j.val) (data j).selection.selected)
  retained_subset : retained ⊆ J.biUnion F
  retained_nonempty : retained.Nonempty
  exact_parent_inter : forall j : {j // j ∈ J}, retained ∩ F j.val =
    sourceDescendantUnion (p j.val) (data j).selection.selected
  retained_disjoint : ((J.attach : Set {j // j ∈ J}).PairwiseDisjoint
    (fun j => sourceDescendantUnion (p j.val) (data j).selection.selected))
  original_mass_eq : (∑ i ∈ J.biUnion F, volume (Z i).shade) =
    ∑ j ∈ J, ∑ i ∈ F j, volume (Z i).shade
  retained_mass_eq : (∑ i ∈ retained, volume (Z i).shade) =
    ∑ j ∈ J.attach, ∑ i ∈ sourceDescendantUnion (p j.val) (data j).selection.selected,
      volume (Z i).shade
  mass_loss : (∑ i ∈ J.biUnion F, volume (Z i).shade) <=
    L0 * ∑ i ∈ retained, volume (Z i).shade

/-- E4: positive mass, complete cells and the actual normalization give the scalar side conditions. -/
theorem sourceBiased_parent_polynomialScale
    (P : SourceBiasedLossParameters) {delta : NNReal} (hdelta : 0 < delta)
    (hdelta1 : delta <= 1)
    (J : Finset jota) (F : jota -> Finset iota) (I : jota -> Finset kappa)
    (p : forall j, SourceDescendantPartition (F j) (I j))
    (Z : iota -> ShadedBody E) (V : jota -> kappa -> ConvexSpaceBody E)
    (parent : jota -> ConvexSpaceBody E) (f : jota -> E ≃ᵃ[Real] E)
    (comparison d : jota -> NNReal)
    (hgeometry : SourceBiasedParentGeometry J F I Z V parent f comparison d)
    (hcard : forall j, j ∈ J -> ((I j).card : Real) <=
      (P.cardCoefficient : Real) * (delta : Real) ^ (-(P.cardPower : Real)))
    (hthickness : forall j, j ∈ J -> (P.thicknessCoefficient : Real) *
      (delta : Real) ^ (P.thicknessPower : Real) <= (d j : Real)) :
    forall j, j ∈ J -> SourceBiasedPolynomialScale P delta (I j).card (d j) := by
  intro j hj
  have hF : (F j).Nonempty := by
    by_contra hh
    have hpos := hgeometry.mass_pos j hj
    simp [Finset.not_nonempty_iff_eq_empty.mp hh] at hpos
  have hI : (I j).Nonempty := by
    by_contra hh
    have heq := (p j).union_eq
    simp [Finset.not_nonempty_iff_eq_empty.mp hh] at heq
    exact hF.ne_empty heq.symm
  obtain ⟨i, hi⟩ := hI
  have hball : ((V j i).mapAffine (f j)).carrier ⊆ Metric.closedBall (0 : E) 1 :=
    ((mapAffine_le_mapAffine_iff (f j)).mpr (hgeometry.contained j hj i hi)).trans
      (hgeometry.normalized_ball j hj)
  have hd1 : d j <= 1 := by
    have hn : 0 < Module.finrank Real E := Module.finrank_pos
    have hscale : ethickness.scale Real ((V j i).mapAffine (f j)).carrier <=
        ethickness Real ((V j i).mapAffine (f j)).carrier 0 :=
      Finset.inf_le (Finset.mem_range.mpr hn)
    have hh := ((hgeometry.normalized_thickness j hj i hi).trans hscale).trans
      (Metric.ethickness_le_of_subset_closedBall (𝕜 := Real) 1 hball 0)
    exact_mod_cast hh
  exact ⟨hdelta, hdelta1, Finset.card_pos.mpr ⟨i, hi⟩, hcard j hj,
    hgeometry.thickness_pos j hj, hd1, hthickness j hj⟩

/-- E5: construct every parent selection with the produced common loss, uniformly in the family. -/
theorem sourceBiased_exists_polylogParentAggregation (P : SourceBiasedLossParameters)
    (comparison : jota -> NNReal) :
    exists delta0 : NNReal, 0 < delta0 ∧ delta0 <= 1 ∧
      forall (delta : NNReal), 0 < delta -> delta < delta0 ->
      forall (J : Finset jota) (F : jota -> Finset iota) (I : jota -> Finset kappa)
        (p : forall j, SourceDescendantPartition (F j) (I j))
        (Z : iota -> ShadedBody E) (V : jota -> kappa -> ConvexSpaceBody E)
        (parent : jota -> ConvexSpaceBody E) (f : jota -> E ≃ᵃ[Real] E)
        (d : jota -> NNReal),
        SourceBiasedParentGeometry J F I Z V parent f comparison d ->
        (forall j, j ∈ J -> ((I j).card : Real) <=
          (P.cardCoefficient : Real) * (delta : Real) ^ (-(P.cardPower : Real))) ->
        (forall j, j ∈ J -> (P.thicknessCoefficient : Real) *
          (delta : Real) ^ (P.thicknessPower : Real) <= (d j : Real)) ->
        Nonempty (SourceBiasedParentAggregation J p Z V parent f comparison d P.bias
          (Kakeya.ML2Core.polylogLoss (Module.finrank Real E + 2) delta)) := by
  obtain ⟨delta0, hd0, hd1, hbound⟩ :=
    sourceBiased_exists_polylog_threshold (Module.finrank Real E) P
  refine ⟨delta0, hd0, hd1, ?_⟩
  intro delta hdelta hdelta0 J F I p Z V parent f d hg hc ht
  have hscale := sourceBiased_parent_polynomialScale P hdelta (hdelta0.le.trans hd1)
    J F I p Z V parent f comparison d hg hc ht
  obtain ⟨D, F', heq, hsub, hne, hinter, hdisj, hmass, hmass', hloss⟩ :=
    sourceBiased_exists_parentAggregation J hg.parents_nonempty F I p hg.parent_fibres_disjoint
      Z V parent f comparison d P.bias P.bias_pos
      (Kakeya.ML2Core.polylogLoss (Module.finrank Real E + 2) delta)
      (lt_top_iff_ne_top.mpr (Kakeya.ML2Core.polylogLoss_ne_top _ _))
      hg.mass_pos hg.thickness_pos hg.contained hg.normalized_ball hg.normalized_thickness
      (fun j hj => ⟨hg.comparison_one_le j hj, hg.reference_comparison j hj⟩)
      (fun j hj => (hbound delta (d j) (I j).card hdelta0 (hscale j hj)).2.2)
  exact ⟨⟨D, F', heq, hsub, hne, hinter, hdisj, hmass, hmass', hloss⟩⟩

end Kakeya.ML2Assembly
