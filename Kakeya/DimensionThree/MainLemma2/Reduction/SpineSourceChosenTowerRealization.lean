/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceFixedPreparation
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceUnselectedNestedTower

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

/-- The once-only canonical cover cost in S:6009-6022. -/
noncomputable def sourceCentringCost (delta : NNReal) (q : Real) : ENNReal :=
  100 * (5000 : ENNReal) ^ 6 * (delta : ENNReal) ^ (-q)

/-- The fixed-M tower selection cost, before simultaneous additional statistics. -/
noncomputable def sourceTowerSelectionLoss (M card : Nat) : ENNReal :=
  ((Nat.ceil (Real.logb 2 (card : Real)) + 1 : Nat) : ENNReal) ^ (M + 1)

/-- The actual canonical cover and induced shading at d=delta/2.
The representatives lie in S, and pi is an onto map from S to I, not an injection. -/
structure SourceCanonicalNormalization {iota : Type u} {delta : NNReal}
    (S I : Finset iota) (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (Y : iota -> ShadedTube (delta / 2) (EuclideanSpace Real (Fin 3)))
    (pi : iota -> iota) (q : Real) : Prop where
  representatives : I <= S
  nonempty : I.Nonempty
  image : (open scoped Classical in S.image pi) = I
  body_injective : Set.InjOn (fun j => (Y j).toConvexSpaceBody) (I : Set iota)
  centred : ∀ j ∈ I, (Y j).toTube.IsCentred
  ball : ∀ j ∈ I, (Y j).carrier <= Metric.closedBall 0 (3 / 4)
  ed : Kakeya.VeryNotSticky.IsLineEssDistinct sourceBottomED I (fun j => (Y j).toTube)
  image_carrier : ∀ i ∈ S,
    Kakeya.VeryNotSticky.centringDilate '' (Z i).carrier <= (Y (pi i)).carrier
  shade_formula : ∀ j ∈ I, (Y j).shade =
    ⋃ i ∈ S, ⋃ (_h : pi i = j), Kakeya.VeryNotSticky.centringDilate '' (Z i).shade
  fibre_bound : ∀ j ∈ I,
    (open scoped Classical in ((S.filter (fun i => pi i = j)).card : ENNReal)) <=
      sourceCentringCost delta q
  tube_volume : ∀ i ∈ S,
    volume (Y (pi i)).carrier <= (384 / 512 : ENNReal) * volume (Z i).carrier
  card_upper : I.card <= S.card
  card_lower : (S.card : ENNReal) <= sourceCentringCost delta q * (I.card : ENNReal)
  union_volume : volume (⋃ j ∈ I, (Y j).shade) =
    (1 / 512 : ENNReal) * volume (⋃ i ∈ S, (Z i).shade)
  mass_upper : (∑ j ∈ I, volume (Y j).shade) <=
    (1 / 512 : ENNReal) * ∑ i ∈ S, volume (Z i).shade
  mass_lower : (1 / 512 : ENNReal) * (∑ i ∈ S, volume (Z i).shade) <=
    sourceCentringCost delta q * ∑ j ∈ I, volume (Y j).shade
  multiplicity_lower : ShadedBody.multiplicity I (fun j => (Y j).toShadedBody) <=
    ShadedBody.multiplicity S (fun i => (Z i).toShadedBody)
  multiplicity_upper : ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
    sourceCentringCost delta q * ShadedBody.multiplicity I (fun j => (Y j).toShadedBody)
  fullness : ShadedBody.fullness' S (fun i => (Z i).toShadedBody) <=
    (384 * sourceCentringCost delta q) * ShadedBody.fullness' I (fun j => (Y j).toShadedBody)
  density : Kakeya.maxDensity I (fun j => (Y j).toConvexSpaceBody) <=
    384 * (delta : ENNReal) ^ (-q)

/-- Source S:5990-6025 supplies a chosen centred family from original unit-ball data.
The map is the actual rho=1 map x/8, and the radius/cover costs stay explicit. -/
theorem source_exists_canonical_normalization {iota : Type u} {delta : NNReal}
    {q : Real} (hq : 0 < q) (hdelta0 : 0 < delta) (hdelta1 : delta <= 1 / 200)
    (S : Finset iota) (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (hS : S.Nonempty) (hball : ∀ i ∈ S, (Z i).carrier <= Metric.closedBall 0 1)
    (hdens : Kakeya.maxDensity S (fun i => (Z i).toConvexSpaceBody) <= (delta : ENNReal) ^ (-q))
    (hfull : (delta : ENNReal) ^ q <= ShadedBody.fullness' S (fun i => (Z i).toShadedBody)) :
    ∃ (I : Finset iota) (Y : iota -> ShadedTube (delta / 2) (EuclideanSpace Real (Fin 3)))
      (pi : iota -> iota), SourceCanonicalNormalization S I Z Y pi q := by
  set_option maxHeartbeats 1800000 in
    classical
    let rho : NNReal := delta / 2
    have hrho : 0 < rho := div_pos hdelta0 (by norm_num)
    have hdeltaR : (delta : Real) <= 1 / 200 := by exact_mod_cast hdelta1
    have hrhoR : (rho : Real) = (delta : Real) / 2 := by simp [rho]
    let X (i : iota) := Kakeya.VeryNotSticky.centringDilate '' (Z i).carrier
    let p (i : iota) := Kakeya.VeryNotSticky.centringDilate (Z i).toTube.midpoint
    let d (i : iota) := (Z i).toTube.direction
    have hd (i : iota) : ‖d i‖ = 1 := (Z i).toTube.norm_direction
    have hXball (i : iota) (hi : i ∈ S) : X i <= Metric.closedBall 0 (1 / 8) := by
      rintro z ⟨x, hx, rfl⟩
      have hxn : ‖x‖ <= 1 := by simpa using hball i hi hx
      simp only [Metric.mem_closedBall, dist_zero_right,
        Kakeya.VeryNotSticky.centringDilate, norm_smul, Real.norm_eq_abs]
      norm_num
      linarith
    have hXline (i : iota) : X i <= Metric.cthickening ((rho : Real) / 4)
        (Set.range fun t : Real => p i + t • d i) := by
      have hline := Kakeya.VeryNotSticky.centringDilate_image_subset_lineNbhd (Z i).toTube
      change X i ⊆ Metric.cthickening ((rho : Real) / 4)
        (Set.range fun t : Real => p i + t • d i)
      simpa only [X, p, d, hrhoR, div_div, show (2 : Real) * 4 = 8 by norm_num] using hline
    have hfoot (i : iota) :
        inner Real (Tube.lineFoot (p i) (d i)) (d i) = 0 := by
      rw [Tube.lineFoot, inner_sub_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq, hd i]
      ring
    have hfootn (i : iota) (hi : i ∈ S) : ‖Tube.lineFoot (p i) (d i)‖ <= (1 / 5 : Real) := by
      have hm : p i ∈ X i := ⟨(Z i).toTube.midpoint,
        Tube.midpoint_mem_carrier hdelta0 (Z i).toTube, rfl⟩
      have hpn : ‖p i‖ <= 1 / 8 := by simpa using hXball i hi hm
      have heq := norm_sub_sq_real (p i) ((inner Real (p i) (d i)) • d i)
      rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, hd i, mul_one, sq_abs] at heq
      change ‖p i - (inner Real (p i) (d i)) • d i‖ <= (1 / 5 : Real)
      nlinarith [norm_nonneg (p i), norm_nonneg (p i - (inner Real (p i) (d i)) • d i),
        sq_nonneg (inner Real (p i) (d i))]
    obtain ⟨G0, hGcen, hGmid, hGsep, hGcover⟩ :=
      Tube.exists_centred_net (E := EuclideanSpace Real (Fin 3)) rho (1 / 5)
        (ε := (rho : Real) / 4) (by positivity)
    have hchoice : ∀ i, ∃ W : Tube rho (EuclideanSpace Real (Fin 3)), i ∈ S ->
        W ∈ G0 /\ ‖Tube.lineFoot (p i) (d i) - W.midpoint‖ <= (rho : Real) / 2 /\
          ‖d i - W.direction‖ <= (rho : Real) / 2 := by
      intro i
      by_cases hi : i ∈ S
      · obtain ⟨W, hW, hm, he⟩ := hGcover _ _ (hfoot i) (hd i) (hfootn i hi)
        refine ⟨W, fun _ => ⟨hW, ?_, ?_⟩⟩ <;> linarith
      · exact ⟨Tube.ofMidpointDirection rho 0 (d i) (hd i), fun his => (hi his).elim⟩
    choose cover hcover using hchoice
    let G := S.image cover
    have hGsub : G <= G0 := by
      intro W hW
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
      exact (hcover i hi).1
    have hcontain (i : iota) (hi : i ∈ S) : X i <= (cover i).carrier := by
      intro z hz
      obtain ⟨_, hm, he⟩ := hcover i hi
      let f := Tube.lineFoot (p i) (d i)
      let t : Real := inner Real (z - f) (d i)
      have hzline : z ∈ Metric.cthickening ((rho : Real) / 4)
          (Set.range fun t : Real => f + t • d i) := by
        have hrange : (Set.range fun t : Real => f + t • d i) =
            Set.range (fun t : Real => p i + t • d i) := by
          ext x
          constructor
          · rintro ⟨a, rfl⟩
            refine ⟨a - inner Real (p i) (d i), ?_⟩
            dsimp [f, Tube.lineFoot]
            module
          · rintro ⟨a, rfl⟩
            refine ⟨a + inner Real (p i) (d i), ?_⟩
            dsimp [f, Tube.lineFoot]
            module
        rw [hrange]
        exact hXline i hz
      have hperp : ‖z - (f + t • d i)‖ <= (rho : Real) / 4 := by
        rw [show t = inner Real (z - f) (d i) from rfl, Tube.norm_sub_foot_eq f (d i) z (hd i)]
        exact (Tube.mem_cthickening_line_iff (hd i) (by positivity)).mp hzline
      have hzn : ‖z‖ <= 1 / 8 := by simpa using hXball i hi hz
      have ht : |t| <= (1 / 8 : Real) := by
        have ht' : t = inner Real z (d i) := by
          dsimp [t]
          rw [inner_sub_left, hfoot i, sub_zero]
        rw [ht']
        exact (abs_real_inner_le_norm z (d i)).trans (by rw [hd i, mul_one]; exact hzn)
      refine (cover i).mem_carrier_of_dist_le
        ((cover i).midpoint_add_smul_mem_segment (ht.trans (by norm_num))) ?_
      rw [dist_eq_norm]
      have he' : |t| * ‖d i - (cover i).direction‖ <= (1 / 8 : Real) * ((rho : Real) / 2) :=
        mul_le_mul ht he (norm_nonneg _) (by norm_num)
      calc ‖z - ((cover i).midpoint + t • (cover i).direction)‖ =
            ‖(z - (f + t • d i)) + ((f - (cover i).midpoint) + t • (d i - (cover i).direction))‖ := by
              congr 1
              module
        _ <= ‖z - (f + t • d i)‖ +
            (‖f - (cover i).midpoint‖ + |t| * ‖d i - (cover i).direction‖) := by
              have hn := norm_add_le (f - (cover i).midpoint) (t • (d i - (cover i).direction))
              rw [norm_smul, Real.norm_eq_abs] at hn
              exact (norm_add_le _ _).trans (add_le_add_right hn _)
        _ <= (rho : Real) := by linarith
    have hcoverball (W : Tube rho (EuclideanSpace Real (Fin 3))) (hW : W ∈ G) :
        W.carrier <= Metric.closedBall 0 (3 / 4) := by
      intro z hz
      rw [W.carrier_eq] at hz
      obtain ⟨x, hx, hz⟩ := Set.mem_iUnion₂.mp hz
      obtain ⟨t, ht, rfl⟩ := W.exists_param_of_mem_segment hx
      have hm := hGmid W (hGsub hW)
      have hzt : dist z (W.midpoint + t • W.direction) <= (rho : Real) := hz
      have hcore : ‖W.midpoint + t • W.direction‖ <= 1 / 5 + 1 / 2 := by
        calc ‖W.midpoint + t • W.direction‖ <= ‖W.midpoint‖ + ‖t • W.direction‖ := norm_add_le _ _
          _ <= 1 / 5 + 1 / 2 := by
            have htdir : ‖t • W.direction‖ = |t| := by
              rw [norm_smul, Real.norm_eq_abs, W.norm_direction, mul_one]
            rw [htdir]
            exact add_le_add hm ht
      simp only [Metric.mem_closedBall, dist_zero_right]
      have hb := dist_triangle z (W.midpoint + t • W.direction) (0 : EuclideanSpace Real (Fin 3))
      rw [dist_zero_right, dist_zero_right] at hb
      rw [hrhoR] at hzt
      linarith
    have hcoverED : Kakeya.VeryNotSticky.IsLineEssDistinct sourceBottomED G
        (fun W : Tube rho (EuclideanSpace Real (Fin 3)) => W) := by
      intro o e he
      have hb := Tube.card_filter_line_le_of_centred_sep G hrho
        (fun W : Tube rho (EuclideanSpace Real (Fin 3)) => W)
        (fun W hW => hGcen W (hGsub hW)) (by norm_num : (0 : Real) <= 1 / 5)
        (fun W hW => hGmid W (hGsub hW)) (m := 4) (by norm_num)
        (fun a ha b hb hab => hGsep a (hGsub ha) b (hGsub hb) hab)
        (K := 5) (by norm_num) o e he
      have hconst : Tube.linePackingConstant 3 (1 / 5) 5 4 <= (sourceBottomED : Real) := by
        norm_num [Tube.linePackingConstant, sourceBottomED]
      rw [Kakeya.VeryNotSticky.lineNbhd_eq_cthickening_range]
      have hb' : ((G.filter fun W => W.carrier <=
          Metric.cthickening (5 * (rho : Real)) (Set.range fun t : Real => o + t • e)).card : Real)
          <= (sourceBottomED : Real) := by
        have hb'' : ((G.filter fun W => W.carrier <=
            Metric.cthickening (5 * (rho : Real)) (Set.range fun t : Real => o + t • e)).card : Real)
            <= Tube.linePackingConstant 3 (1 / 5) 5 4 := by
          simpa using hb
        exact hb''.trans hconst
      exact_mod_cast hb'
    have hbottomVolume (U : Tube delta (EuclideanSpace Real (Fin 3))) :
        (3 : ENNReal) * (delta : ENNReal) ^ 2 <= volume U.carrier := by
      have hdir : U.direction ≠ 0 := by
        intro heq
        have hn := U.norm_direction
        rw [heq, norm_zero] at hn
        norm_num at hn
      have hdim : Module.finrank Real
          (((Real ∙ U.direction)ᗮ : Submodule Real (EuclideanSpace Real (Fin 3)))) = 2 := by
        apply Submodule.finrank_add_finrank_orthogonal'
        rw [finrank_span_singleton hdir]
        norm_num
      letI : Nontrivial
          (((Real ∙ U.direction)ᗮ : Submodule Real (EuclideanSpace Real (Fin 3)))) :=
        Module.nontrivial_of_finrank_pos (R := Real) (by rw [hdim]; norm_num)
      have hcross : volume (Metric.closedBall
          (0 : ((Real ∙ U.direction)ᗮ : Submodule Real (EuclideanSpace Real (Fin 3)))) (delta : Real)) =
          (delta : ENNReal) ^ 2 * ENNReal.ofReal Real.pi := by
        rw [InnerProductSpace.volume_closedBall_of_dim_even (k := 1) hdim, hdim]
        norm_num
      have hcyl := volume_cylinder U.norm_direction U.midpoint (-(1 / 2)) (1 / 2) (delta : Real)
      rw [hcross] at hcyl
      norm_num only [sub_neg_eq_add, show (1 / 2 : Real) + 1 / 2 = 1 by norm_num,
        ENNReal.ofReal_one, one_mul] at hcyl
      have hsub := U.cylinder_subset_carrier_self
        (a := -(1 / 2)) (b := 1 / 2) (r := (delta : Real)) (le_refl _) (le_refl _) (le_refl _)
      calc (3 : ENNReal) * (delta : ENNReal) ^ 2 <= ENNReal.ofReal Real.pi * (delta : ENNReal) ^ 2 := by
            gcongr
            exact (by norm_num : (3 : ENNReal) = ENNReal.ofReal (3 : Real)).trans_le
              (ENNReal.ofReal_le_ofReal Real.pi_gt_three.le)
        _ = volume (_root_.cylinder U.midpoint U.direction (-(1 / 2)) (1 / 2) (delta : Real)) := by
            rw [hcyl]
            ac_rfl
        _ <= volume U.carrier := measure_mono hsub
    have hvolume (W : Tube rho (EuclideanSpace Real (Fin 3)))
        (U : Tube delta (EuclideanSpace Real (Fin 3))) :
        volume W.carrier <= (384 / 512 : ENNReal) * volume U.carrier := by
      have hrhoSmall : rho <= (1 / 8 : NNReal) := by
        rw [← NNReal.coe_le_coe]
        norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
        rw [hrhoR]
        linarith
      have hv := Tube.volume_le_of_le hrhoSmall W
      have hv' : volume W.carrier <= (9 / 4 : ENNReal) * (delta : ENNReal) ^ 2 := by
        convert hv using 1 <;>
          norm_num [rho, ENNReal.coe_div, mul_div_assoc, div_eq_mul_inv]
        rw [mul_pow, ← ENNReal.inv_pow]
        norm_num
        ring
      calc volume W.carrier <= (9 / 4 : ENNReal) * (delta : ENNReal) ^ 2 := hv'
        _ = (384 / 512 : ENNReal) * ((3 : ENNReal) * (delta : ENNReal) ^ 2) := by
            have hn : (9 / 4 : ENNReal) = (384 / 512 : ENNReal) * 3 := by
              apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
              norm_num [ENNReal.toReal_div, ENNReal.toReal_mul]
            rw [hn, mul_assoc]
        _ <= (384 / 512 : ENNReal) * volume U.carrier := mul_le_mul_right (hbottomVolume U) _
    letI : Nonempty iota := ⟨hS.choose⟩
    let pi : iota -> iota := Tube.carrierRep S cover
    let I : Finset iota := S.image pi
    have hIS : I <= S := Tube.carrierRep_image_subset
    have hI : I.Nonempty := Tube.carrierRep_image_nonempty hS
    have hpi (i : iota) (hi : i ∈ S) : pi i ∈ I := Finset.mem_image_of_mem _ hi
    have hpiCarrier (i : iota) (hi : i ∈ S) :
        (cover (pi i)).carrier = (cover i).carrier := Tube.carrierRep_carrier hi
    have hIinj : Set.InjOn (fun i => (cover i).toConvexSpaceBody) (I : Set iota) := by
      intro i hi j hj heq
      exact Tube.carrierRep_injOn_image hi hj (congrArg ConvexSpaceBody.carrier heq)
    have hcoverinj : Set.InjOn cover (I : Set iota) := by
      intro i hi j hj heq
      exact hIinj hi hj (congrArg Tube.toConvexSpaceBody heq)
    have hDfun : (Kakeya.VeryNotSticky.centringDilate : EuclideanSpace Real (Fin 3) -> _) =
        AffineMap.homothety (0 : EuclideanSpace Real (Fin 3)) (1 / 8 : Real) := by
      funext x
      simp [Kakeya.VeryNotSticky.centringDilate, AffineMap.homothety_apply]
    have hDvol (A : Set (EuclideanSpace Real (Fin 3))) :
        volume (Kakeya.VeryNotSticky.centringDilate '' A) = (1 / 512 : ENNReal) * volume A := by
      rw [hDfun, MeasureTheory.Measure.addHaar_image_homothety]
      norm_num [ENNReal.ofReal_div_of_pos]
    let B (j : iota) := ⋃ i ∈ S, ⋃ (_h : pi i = j),
      Kakeya.VeryNotSticky.centringDilate '' (Z i).shade
    have hBsub (j : iota) : B j <= (cover j).carrier := by
      intro x hx
      obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨hij, hx⟩ := Set.mem_iUnion.mp hx
      rw [← hij, hpiCarrier i hi]
      exact hcontain i hi (Set.image_mono (Z i).shade_subset hx)
    have hBmeas (j : iota) : MeasurableSet (B j) := by
      refine S.measurableSet_biUnion fun i hi => MeasurableSet.iUnion fun _ => ?_
      rw [hDfun]
      exact (Kakeya.measurableEmbedding_homothety (0 : EuclideanSpace Real (Fin 3))
        (by norm_num : (1 / 8 : Real) ≠ 0)).measurableSet_image' (Z i).measurableSet_shade
    let Y (j : iota) : ShadedTube rho (EuclideanSpace Real (Fin 3)) :=
      { toTube := cover j
        shade := B j
        measurableSet_shade := hBmeas j
        shade_subset := hBsub j }
    have hYED : Kakeya.VeryNotSticky.IsLineEssDistinct sourceBottomED I
        (fun i => (Y i).toTube) := by
      intro o e he
      let P (W : Tube rho (EuclideanSpace Real (Fin 3))) := W.carrier <=
        Kakeya.VeryNotSticky.lineNbhd o e (5 * (rho : Real))
      have hcard : (I.filter (fun i => P (cover i))).card <= (G.filter P).card := by
        apply Finset.card_le_card_of_injOn cover
        · intro i hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (hIS (Finset.mem_filter.mp hi).1),
            (Finset.mem_filter.mp hi).2⟩
        · intro i hi j hj heq
          exact hcoverinj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 heq
      exact hcard.trans (hcoverED o e he)
    have hYunion : (⋃ j ∈ I, (Y j).shade) =
        Kakeya.VeryNotSticky.centringDilate '' (⋃ i ∈ S, (Z i).shade) := by
      rw [Set.image_iUnion₂]
      ext x
      constructor
      · rintro hx
        obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.mp hx
        obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp hx
        obtain ⟨_, hx⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion₂.mpr ⟨i, hi, hx⟩
      · intro hx
        obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp hx
        exact Set.mem_iUnion₂.mpr ⟨pi i, hpi i hi,
          Set.mem_iUnion₂.mpr ⟨i, hi, Set.mem_iUnion.mpr ⟨rfl, hx⟩⟩⟩
    have hvolUnion : volume (⋃ j ∈ I, (Y j).shade) =
        (1 / 512 : ENNReal) * volume (⋃ i ∈ S, (Z i).shade) := by
      rw [hYunion, hDvol]
    let N (i : iota) := (Z i).toConvexSpaceBody.homothety 0 (1 / 8 : Real)
    have hNcarrier (i : iota) : (N i).carrier = X i := by
      change AffineMap.homothety (0 : EuclideanSpace Real (Fin 3)) (1 / 8 : Real) ''
        (Z i).carrier = X i
      rw [← hDfun]
    have hNvol (i : iota) : volume (N i).carrier = (1 / 512 : ENNReal) * volume (Z i).carrier := by
      rw [hNcarrier]
      exact hDvol _
    have hNmax : Kakeya.maxDensity S N <= (delta : ENNReal) ^ (-q) := by
      rw [show Kakeya.maxDensity S N = Kakeya.maxDensity S (fun i => (Z i).toConvexSpaceBody) from
        Kakeya.maxDensity_homothety S (fun i => (Z i).toConvexSpaceBody) 0 (by norm_num)]
      exact hdens
    have hNvolCover (W : Tube rho (EuclideanSpace Real (Fin 3))) (i : iota) :
        volume W.carrier <= 384 * volume (N i).carrier := by
      rw [hNvol]
      have heq : (384 / 512 : ENNReal) = 384 * (1 / 512 : ENNReal) := by
        simp only [div_eq_mul_inv, one_mul]
      simpa only [heq, mul_assoc] using hvolume W (Z i).toTube
    have hYdensity : Kakeya.maxDensity I (fun i => (Y i).toConvexSpaceBody) <=
        384 * (delta : ENNReal) ^ (-q) := by
      have hn := Kakeya.maxDensity_le_of_subset_of_volume_le I N
        (fun i => (Y i).toConvexSpaceBody)
        (fun i hi => by rw [hNcarrier]; exact hcontain i (hIS hi))
        (fun i _ => hNvolCover (cover i) i)
      exact hn.trans (mul_le_mul_right ((Kakeya.maxDensity_mono N hIS).trans hNmax) 384)
    let F (j : iota) := S.filter fun i => pi i = j
    have hFsub (j : iota) : F j <= S := Finset.filter_subset _ _
    let i0 := hS.choose
    have hi0 : i0 ∈ S := hS.choose_spec
    let v : ENNReal := volume (N i0).carrier
    have hv0 : v ≠ 0 := by
      dsimp [v]
      rw [hNvol]
      exact mul_ne_zero (by norm_num)
        (ML2Shaded.volume_carrier_ne_zero hdelta0 (Z i0).toTube)
    have hvtop : v ≠ ⊤ := (N i0).isCompact.measure_ne_top
    have hNv (i : iota) : volume (N i).carrier = v := by
      dsimp [v]
      rw [hNvol, hNvol, Tube.volume_carrier_eq_volume_carrier (Z i).toTube (Z i0).toTube]
    have hFcard384 (j : iota) : ((F j).card : ENNReal) <= 384 * (delta : ENNReal) ^ (-q) := by
      apply (ENNReal.mul_le_mul_iff_left hv0 hvtop).mp
      calc ((F j).card : ENNReal) * v = ∑ i ∈ F j, volume (N i).carrier := by
            simp only [hNv, Finset.sum_const, nsmul_eq_mul]
        _ <= Kakeya.maxDensity (F j) N * volume (cover j).carrier := by
            apply Kakeya.sum_volume_le_maxDensity_mul_volume'
            intro i hi
            obtain ⟨his, hij⟩ := Finset.mem_filter.mp hi
            change (N i).carrier <= (cover j).carrier
            rw [hNcarrier, ← hij, hpiCarrier i his]
            exact hcontain i his
        _ <= (delta : ENNReal) ^ (-q) * volume (cover j).carrier :=
            mul_le_mul_left ((Kakeya.maxDensity_mono N (hFsub j)).trans hNmax) _
        _ <= (delta : ENNReal) ^ (-q) * (384 * v) :=
            mul_le_mul_right (hNvolCover (cover j) i0) _
        _ = (384 * (delta : ENNReal) ^ (-q)) * v := by ac_rfl
    have hFcard (j : iota) : ((F j).card : ENNReal) <= sourceCentringCost delta q := by
      refine (hFcard384 j).trans ?_
      unfold sourceCentringCost
      apply mul_le_mul_left
      norm_num
    have hFshade (j : iota) : (Y j).shade =
        ⋃ i ∈ F j, Kakeya.VeryNotSticky.centringDilate '' (Z i).shade := by
      ext x
      change x ∈ B j ↔ x ∈ ⋃ i ∈ F j,
        Kakeya.VeryNotSticky.centringDilate '' (Z i).shade
      constructor
      · intro hx
        obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp hx
        obtain ⟨hij, hx⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hij⟩, hx⟩
      · intro hx
        obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp hx
        obtain ⟨his, hij⟩ := Finset.mem_filter.mp hi
        exact Set.mem_iUnion₂.mpr ⟨i, his, Set.mem_iUnion.mpr ⟨hij, hx⟩⟩
    have hFmass (f : iota -> ENNReal) : (∑ j ∈ I, ∑ i ∈ F j, f i) = ∑ i ∈ S, f i := by
      exact Finset.sum_fiberwise_of_maps_to hpi f
    have hmassUpper : (∑ j ∈ I, volume (Y j).shade) <=
        (1 / 512 : ENNReal) * ∑ i ∈ S, volume (Z i).shade := by
      calc (∑ j ∈ I, volume (Y j).shade) <=
            ∑ j ∈ I, ∑ i ∈ F j, volume (Kakeya.VeryNotSticky.centringDilate '' (Z i).shade) := by
              apply Finset.sum_le_sum
              intro j hj
              rw [hFshade]
              exact measure_biUnion_finset_le (F j) _
        _ = ∑ i ∈ S, volume (Kakeya.VeryNotSticky.centringDilate '' (Z i).shade) := hFmass _
        _ = (1 / 512 : ENNReal) * ∑ i ∈ S, volume (Z i).shade := by
              simp only [hDvol, Finset.mul_sum]
    have hmassLower : (1 / 512 : ENNReal) * (∑ i ∈ S, volume (Z i).shade) <=
        sourceCentringCost delta q * ∑ j ∈ I, volume (Y j).shade := by
      calc (1 / 512 : ENNReal) * (∑ i ∈ S, volume (Z i).shade) =
            ∑ i ∈ S, volume (Kakeya.VeryNotSticky.centringDilate '' (Z i).shade) := by
              simp only [hDvol, Finset.mul_sum]
        _ = ∑ j ∈ I, ∑ i ∈ F j, volume (Kakeya.VeryNotSticky.centringDilate '' (Z i).shade) := (hFmass _).symm
        _ <= ∑ j ∈ I, ((F j).card : ENNReal) * volume (Y j).shade := by
              apply Finset.sum_le_sum
              intro j hj
              rw [← nsmul_eq_mul, ← Finset.sum_const]
              apply Finset.sum_le_sum
              intro i hi
              apply measure_mono
              rw [hFshade]
              exact Set.subset_iUnion₂_of_subset i hi subset_rfl
        _ <= ∑ j ∈ I, sourceCentringCost delta q * volume (Y j).shade :=
              Finset.sum_le_sum fun j _ => mul_le_mul_left (hFcard j) _
        _ = sourceCentringCost delta q * ∑ j ∈ I, volume (Y j).shade := (Finset.mul_sum _ _ _).symm
    have hcardLower : (S.card : ENNReal) <= sourceCentringCost delta q * (I.card : ENNReal) := by
      calc (S.card : ENNReal) = ∑ j ∈ I, ((F j).card : ENNReal) := by
            exact_mod_cast Finset.card_eq_sum_card_image pi S
        _ <= ∑ j ∈ I, sourceCentringCost delta q := Finset.sum_le_sum fun j _ => hFcard j
        _ = sourceCentringCost delta q * (I.card : ENNReal) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hJ0 : (1 / 512 : ENNReal) ≠ 0 := by norm_num
    have hJtop : (1 / 512 : ENNReal) ≠ ⊤ := by norm_num
    have hmultLower : ShadedBody.multiplicity I (fun i => (Y i).toShadedBody) <=
        ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) := by
      apply (ShadedBody.multiplicity_le_iff I (fun i => (Y i).toShadedBody)).mpr
      calc (∑ i ∈ I, volume (Y i).shade) <=
            (1 / 512 : ENNReal) * ∑ i ∈ S, volume (Z i).shade := hmassUpper
        _ = ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) *
            volume (⋃ i ∈ I, (Y i).shade) := by
              rw [hvolUnion, ShadedBody.sum_shade_eq_multiplicity_mul_union S
                (fun i => (Z i).toShadedBody)]
              ac_rfl
    have hmultUpper : ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
        sourceCentringCost delta q * ShadedBody.multiplicity I (fun i => (Y i).toShadedBody) := by
      apply (ShadedBody.multiplicity_le_iff S (fun i => (Z i).toShadedBody)).mpr
      apply (ENNReal.mul_le_mul_iff_right hJ0 hJtop).mp
      calc (1 / 512 : ENNReal) * (∑ i ∈ S, volume (Z i).shade) <=
            sourceCentringCost delta q * ∑ i ∈ I, volume (Y i).shade := hmassLower
        _ = (1 / 512 : ENNReal) * ((sourceCentringCost delta q *
            ShadedBody.multiplicity I (fun i => (Y i).toShadedBody)) *
            volume (⋃ i ∈ S, (Z i).shade)) := by
              rw [ShadedBody.sum_shade_eq_multiplicity_mul_union I
                (fun i => (Y i).toShadedBody), hvolUnion]
              ac_rfl
    let DZ : ENNReal := ∑ i ∈ S, volume (Z i).carrier
    let DY : ENNReal := ∑ i ∈ I, volume (Y i).carrier
    have hDZ0 : DZ ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr
        (ML2Shaded.volume_carrier_ne_zero hdelta0 (Z i0).toTube))
        (Finset.single_le_sum (f := fun i => volume (Z i).carrier) (fun _ _ => zero_le) hi0))
    have hDZtop : DZ ≠ ⊤ := by
      exact ENNReal.sum_ne_top.mpr fun i _ => (Z i).isCompact'.measure_ne_top
    have hDsum : DY <= 384 * ((1 / 512 : ENNReal) * DZ) := by
      calc DY <= ∑ i ∈ I, 384 * volume (N i).carrier :=
            Finset.sum_le_sum fun i _ => hNvolCover (cover i) i
        _ <= ∑ i ∈ S, 384 * volume (N i).carrier :=
            Finset.sum_le_sum_of_subset_of_nonneg hIS (fun _ _ _ => zero_le)
        _ = 384 * ((1 / 512 : ENNReal) * DZ) := by
            simp only [hNvol, Finset.mul_sum, DZ]
    have hZmass : (∑ i ∈ S, volume (Z i).shade) =
        ShadedBody.fullness' S (fun i => (Z i).toShadedBody) * DZ := by
      simpa only [ShadedBody.coe_fullness] using
        ShadedBody.sum_volumeReal_shade_eq_fullness_mul S (fun i => (Z i).toShadedBody)
    have hYmass : (∑ i ∈ I, volume (Y i).shade) =
        ShadedBody.fullness' I (fun i => (Y i).toShadedBody) * DY := by
      simpa only [ShadedBody.coe_fullness] using
        ShadedBody.sum_volumeReal_shade_eq_fullness_mul I (fun i => (Y i).toShadedBody)
    have hfullness : ShadedBody.fullness' S (fun i => (Z i).toShadedBody) <=
        (384 * sourceCentringCost delta q) * ShadedBody.fullness' I (fun i => (Y i).toShadedBody) := by
      apply (ENNReal.mul_le_mul_iff_left (mul_ne_zero hJ0 hDZ0)
        (ENNReal.mul_ne_top hJtop hDZtop)).mp
      calc ShadedBody.fullness' S (fun i => (Z i).toShadedBody) * ((1 / 512 : ENNReal) * DZ) =
            (1 / 512 : ENNReal) * ∑ i ∈ S, volume (Z i).shade := by rw [hZmass]; ac_rfl
        _ <= sourceCentringCost delta q * ∑ i ∈ I, volume (Y i).shade := hmassLower
        _ = (sourceCentringCost delta q * ShadedBody.fullness' I
            (fun i => (Y i).toShadedBody)) * DY := by rw [hYmass, mul_assoc]
        _ <= (sourceCentringCost delta q * ShadedBody.fullness' I
            (fun i => (Y i).toShadedBody)) * (384 * ((1 / 512 : ENNReal) * DZ)) :=
              mul_le_mul_right hDsum _
        _ = ((384 * sourceCentringCost delta q) * ShadedBody.fullness' I
            (fun i => (Y i).toShadedBody)) * ((1 / 512 : ENNReal) * DZ) := by ac_rfl
    refine ⟨I, Y, pi, {
      representatives := hIS
      nonempty := hI
      image := rfl
      body_injective := hIinj
      centred := ?_
      ball := ?_
      ed := hYED
      image_carrier := ?_
      shade_formula := fun _ _ => rfl
      fibre_bound := fun j _ => hFcard j
      tube_volume := fun i _ => hvolume (cover (pi i)) (Z i).toTube
      card_upper := Finset.card_le_card hIS
      card_lower := hcardLower
      union_volume := hvolUnion
      mass_upper := hmassUpper
      mass_lower := hmassLower
      multiplicity_lower := hmultLower
      multiplicity_upper := hmultUpper
      fullness := hfullness
      density := hYdensity }⟩
    · intro j hj
      exact hGcen (cover j) ((hcover j (hIS hj)).1)
    · intro j hj
      exact hcoverball (cover j) (Finset.mem_image_of_mem _ (hIS hj))
    · intro i hi
      change X i <= (cover (pi i)).carrier
      rw [hpiCarrier i hi]
      exact hcontain i hi

/-- Source propthreadedtower constructs its own tower with the weighted retained family.
Its parent and placement maps are outputs; no comparison with an unrelated SSF tower is asserted. -/
theorem source_exists_weighted_chosen_fixedTower (M : Nat) (hM : 2 <= M) :
    ∃ (delta0 : NNReal) (C3 : Real), 0 < delta0 /\ delta0 <= (400 : NNReal) ^ (-(M : Real)) /\
      1 <= C3 /\ ∀ delta : NNReal, 0 < delta -> delta < delta0 ->
      ∀ {iota : Type u} (S : Finset iota)
        (T : iota -> Tube delta (EuclideanSpace Real (Fin 3))),
        S.Nonempty -> Set.InjOn (fun i => (T i).toConvexSpaceBody) (S : Set iota) ->
        (∀ i ∈ S, (T i).IsCentred) ->
        (∀ i ∈ S, (T i).carrier <= Metric.closedBall 0 (3 / 4)) ->
        Kakeya.VeryNotSticky.IsLineEssDistinct sourceBottomED S T ->
      ∀ w : iota -> ENNReal, 0 < ∑ i ∈ S, w i -> (∑ i ∈ S, w i) ≠ ⊤ ->
      ∃ (R : Finset iota) (Q : SourceThreadedTower R T M sourceThreadConstant),
        R <= S /\ R.Nonempty /\ SourceTowerGeometry Q sourceBottomED sourceLevelED /\
        (∑ i ∈ S, w i) <= sourceTowerSelectionLoss M S.card * ∑ i ∈ R, w i /\
        (∃ D : Nat -> Real, ∀ k, k <= M -> 0 < D k /\
          ∀ j ∈ Q.indexSet k, D k <= ((Q.cell k j).card : Real) /\
            ((Q.cell k j).card : Real) < 2 * D k /\
            (open scoped Classical in
              D k <= ((R.filter (fun i => (T i).toConvexSpaceBody <=
                (Q.tube k j).toConvexSpaceBody)).card : Real) /\
              ((R.filter (fun i => (T i).toConvexSpaceBody <=
                (Q.tube k j).toConvexSpaceBody)).card : Real) < 2 * sourceThreadConstant * D k)) /\
        (∀ a b, a < b -> b < M -> ∀ j ∈ Q.indexSet a,
          ((Q.fibre a b j).card : Real) <= C3 *
            ((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M b : Real)) ^ 6) := by
  classical
  have hselect : ∀ {delta : NNReal} {iota : Type u} {S : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))}
      (Q : SourceThreadedTower S T M sourceThreadConstant) (w : iota -> ENNReal),
      (∑ i ∈ S, w i) ≠ 0 ->
      ∃ R : Finset iota, R <= S /\ R.Nonempty /\
        (∑ i ∈ S, w i) <= sourceTowerSelectionLoss M S.card * ∑ i ∈ R, w i /\
        (∃ D : Nat -> Real, ∀ k, k <= M -> 0 < D k /\ ∀ i ∈ R,
          D k <= ((R.filter (fun j => Q.place k j = Q.place k i)).card : Real) /\
          ((R.filter (fun j => Q.place k j = Q.place k i)).card : Real) < 2 * D k) := by
    intro delta iota S T Q w hw
    have hcoarse (b : Nat) (hb : b <= M) : ∀ a, a <= b -> ∀ i ∈ S, ∀ j ∈ S,
        Q.place b i = Q.place b j -> Q.place a i = Q.place a j := by
      induction b with
      | zero =>
          intro a ha i hi j hj heq
          simpa only [Nat.eq_zero_of_le_zero ha] using heq
      | succ b ih =>
          intro a ha i hi j hj heq
          by_cases hab : a = b + 1
          · simpa only [hab] using heq
          · apply ih (by omega) a (by omega) i hi j hj
            rw [Q.parent_composition b (by omega) i hi, Q.parent_composition b (by omega) j hj, heq]
    let cell (k : Nat) (R : Finset iota) (i : iota) := R.filter fun j => Q.place k j = Q.place k i
    let stat (k : Nat) (R : Finset iota) (i : iota) :=
      ENNReal.ofReal (((cell k R i).card : Real) - 1 / 2)
    let bucket (k : Nat) (R : Finset iota) (i : iota) := dyadicBandIndex (cell k R i).card
    let L := Nat.ceil (Real.logb 2 (S.card : Real)) + 1
    have hcellpos (k : Nat) {R : Finset iota} {i : iota} (hi : i ∈ R) : 1 <= (cell k R i).card :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
    have hstatpos (k : Nat) {R : Finset iota} {i : iota} (hi : i ∈ R) :
        0 <= ((cell k R i).card : Real) - 1 / 2 := by
      have hc : (1 : Real) <= (cell k R i).card := by exact_mod_cast hcellpos k hi
      linarith
    have hbc (k : Nat) (R : Finset iota) (i j : iota) (hij : Q.place k i = Q.place k j) :
        bucket k R i = bucket k R j := by simp only [bucket, cell, hij]
    have hlocal (k : Nat) : LeafLocalStat (Q.place k) (stat k) := by
      intro R R' i heq
      change cell k R i = cell k R' i at heq
      simp only [stat, heq]
    have hbucketBound (k : Nat) {R : Finset iota} (hR : R <= S) (i : iota) : bucket k R i < L := by
      have hc : (cell k R i).card <= S.card := (Finset.card_filter_le R _).trans (Finset.card_le_card hR)
      have hlog : Nat.log 2 S.card <= Nat.ceil (Real.logb 2 (S.card : Real)) := by
        exact_mod_cast (Real.natLog_le_logb S.card 2).trans (Nat.le_ceil (Real.logb 2 (S.card : Real)))
      exact Nat.lt_succ_of_le ((Nat.log_mono_right hc).trans hlog)
    have hpair (k : Nat) {R : Finset iota} (i : iota) (hi : i ∈ R)
        (j : iota) (hj : j ∈ R) (heq : bucket k R i = bucket k R j) :
        stat k R j <= 2 * stat k R i := by
      have hcp := hcellpos k hi
      have hc := within_factor_two_of_dyadicBandIndex_eq (by omega : (cell k R i).card ≠ 0) heq
      have hcr : ((cell k R j).card : Real) + 1 <= 2 * ((cell k R i).card : Real) := by
        exact_mod_cast Nat.succ_le_of_lt hc
      change ENNReal.ofReal (((cell k R j).card : Real) - 1 / 2) <=
        2 * ENNReal.ofReal (((cell k R i).card : Real) - 1 / 2)
      rw [show (2 : ENNReal) = ENNReal.ofReal (2 : Real) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    obtain ⟨R, hRS, hRne, hmass, -, Phi, hPhi⟩ :=
      exists_multiLevel_band_wt (n := 1) (γ := iota) S w hw (fun p => Q.place (M - p))
        (fun p q hpq i hi j hj heq => hcoarse (M - p) (Nat.sub_le _ _) (M - q)
          (Nat.sub_le_sub_left hpq M) i hi j hj heq)
        (fun p _ R i => stat (M - p) R i) (fun p _ => hlocal (M - p))
        (fun p _ R i => bucket (M - p) R i) (fun p _ R i j hij => hbc (M - p) R i j hij)
        L (by dsimp [L]; omega) (fun p _ R hR i _ => hbucketBound (M - p) hR i)
        (fun p _ R _ i hi j hj heq => hpair (M - p) i hi j hj heq)
        (fun _ _ => 0) 1 (by norm_num) (fun _ _ _ => by norm_num) (fun _ _ _ _ => rfl) M
    have hband (k : Nat) (hk : k <= M) (i : iota) (hi : i ∈ R) :
        Phi (M - k) 0 <= stat k R i /\ stat k R i <= 2 * Phi (M - k) 0 := by
      have hb := hPhi (M - k) (Nat.sub_le _ _) 0 i hi
      simpa only [Nat.sub_sub_self hk] using hb
    have hPhiTop (k : Nat) (hk : k <= M) : Phi (M - k) 0 ≠ ⊤ := by
      obtain ⟨i, hi⟩ := hRne
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hband k hk i hi).1
    refine ⟨R, hRS, hRne, ?_, fun k => (Phi (M - k) 0).toReal + 1 / 2, ?_⟩
    · simpa only [Nat.cast_one, one_mul, pow_one, L, sourceTowerSelectionLoss] using hmass
    · intro k hk
      refine ⟨by positivity, ?_⟩
      intro i hi
      have hb := hband k hk i hi
      have hlo := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb.1
      have hhi := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) (hPhiTop k hk)) hb.2
      simp only [stat, ENNReal.toReal_ofReal (hstatpos k hi), ENNReal.toReal_mul,
        ENNReal.toReal_ofNat] at hlo hhi
      change (Phi (M - k) 0).toReal + 1 / 2 <= ((cell k R i).card : Real) /\
        ((cell k R i).card : Real) < 2 * ((Phi (M - k) 0).toReal + 1 / 2)
      constructor <;> linarith
  have hrestrict : ∀ {delta : NNReal} {iota : Type u} {S : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))}
      (Q : SourceThreadedTower S T M sourceThreadConstant),
      SourceTowerGeometry Q sourceBottomED sourceLevelED -> SourceTowerNeighbourSharing Q ->
      ∀ R : Finset iota, R <= S -> R.Nonempty ->
      ∃ Q' : SourceThreadedTower R T M sourceThreadConstant,
        SourceTowerRestriction Q Q' /\ SourceTowerGeometry Q' sourceBottomED sourceLevelED /\
          SourceTowerNeighbourSharing Q' := by
    intro delta iota S T Q hgeom hnear R hR hRne
    have hocc (k : Nat) (hk : k <= M) : Q.assignedFootprint R k <= Q.indexSet k := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact Q.place_mem k hk i (hR hi)
    let Q' : SourceThreadedTower R T M sourceThreadConstant := {
      indexSet := Q.assignedFootprint R
      place := Q.place
      parent := Q.parent
      tube := Q.tube
      tube_injective := fun k hk i hi j hj => Q.tube_injective k hk (hocc k hk hi) (hocc k hk hj)
      place_mem := fun k _ i hi => Finset.mem_image_of_mem _ hi
      place_surjective := fun k _ j hj => Finset.mem_image.mp hj
      leaf_containment := fun k hk i hi => Q.leaf_containment k hk i (hR hi)
      parent_mem := by
        intro k hk j hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
        rw [← Q.parent_composition k hk i (hR hi)]
        exact Finset.mem_image_of_mem _ hi
      parent_composition := fun k hk i hi => Q.parent_composition k hk i (hR hi)
      parent_containment := fun k hk j hj => Q.parent_containment k hk j (hocc (k + 1) (by omega) hj)
      bottom_index := by
        ext i
        constructor
        · intro hi
          obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
          rw [Q.bottom_place j (hR hj)] at hji
          exact hji ▸ hj
        · intro hi
          exact Finset.mem_image.mpr ⟨i, hi, Q.bottom_place i (hR hi)⟩
      bottom_place := fun i hi => Q.bottom_place i (hR hi)
      bottom_body := fun i hi => Q.bottom_body i (hR hi)
      containment_multiplicity := by
        intro k hk i hi
        exact (Finset.card_le_card (Finset.filter_subset_filter _ (hocc k hk))).trans
          (Q.containment_multiplicity k hk i (hR hi)) }
    refine ⟨Q', {
      subset := hR
      assignment := rfl
      parent := rfl
      tubes := rfl
      occupied := fun _ _ => rfl
      full_retained_fibres := fun _ _ _ => rfl }, {
      nonempty := hRne
      original_centred := fun i hi => hgeom.original_centred i (hR hi)
      original_ball := fun i hi => hgeom.original_ball i (hR hi)
      original_ed := hgeom.original_ed.subset hR
      coarse_centred := fun k hk j hj => hgeom.coarse_centred k hk j (hocc k hk.le hj)
      coarse_ball := fun k hk j hj => hgeom.coarse_ball k hk j (hocc k hk.le hj)
      coarse_ed := fun k hk => (hgeom.coarse_ed k hk).subset (hocc k hk.le)
      coarse_card := ?_
      segment_sharing := ?_ }, ?_⟩
    · intro k hk
      calc ((Q.assignedFootprint R k).card : Real) <= ((Q.indexSet k).card : Real) := by
            exact_mod_cast Finset.card_le_card (hocc k hk.le)
        _ <= (32 / (sourceTowerRadius delta M k : Real)) ^ 6 := hgeom.coarse_card k hk
    · intro k hk x y hxy
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (hocc k hk.le))).trans
        (hgeom.segment_sharing k hk x y hxy)
    · intro k hk j hj
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (hocc k hk.le))).trans
        (hnear k hk j (hocc k hk.le hj))
  have hgeometric : ∀ {delta : NNReal} {iota : Type u} {R : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))}
      (Q : SourceThreadedTower R T M sourceThreadConstant),
      SourceTowerGeometry Q sourceBottomED sourceLevelED -> SourceTowerNeighbourSharing Q ->
      ∀ D : Nat -> Real, D M = 1 ->
      (∀ k, k <= M -> 0 < D k /\ ∀ j ∈ Q.indexSet k,
        D k <= ((Q.cell k j).card : Real) /\ ((Q.cell k j).card : Real) < 2 * D k) ->
      ∀ k, k <= M -> ∀ j ∈ Q.indexSet k,
        D k <= ((R.filter (fun i => (T i).toConvexSpaceBody <=
          (Q.tube k j).toConvexSpaceBody)).card : Real) /\
        ((R.filter (fun i => (T i).toConvexSpaceBody <=
          (Q.tube k j).toConvexSpaceBody)).card : Real) < 2 * sourceThreadConstant * D k := by
    intro delta iota R T Q hgeom hnear D hDM hD k hk j hj
    let G := R.filter (fun i => (T i).toConvexSpaceBody <= (Q.tube k j).toConvexSpaceBody)
    have hcellG : Q.cell k j <= G := by
      intro i hi
      obtain ⟨hi, hplace⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_filter.mpr ⟨hi, ?_⟩
      simpa only [hplace] using Q.leaf_containment k hk i hi
    refine ⟨((hD k hk).2 j hj).1.trans (by exact_mod_cast Finset.card_le_card hcellG), ?_⟩
    change (G.card : Real) < 2 * sourceThreadConstant * D k
    by_cases hkM : k = M
    · subst k
      have hjR : j ∈ R := Q.bottom_index ▸ hj
      have hsub : G <= R.filter (fun i => (T i).carrier <=
          Kakeya.VeryNotSticky.lineNbhd (T j).x (T j).direction (5 * (delta : Real))) := by
        intro i hi
        obtain ⟨hiR, hiT⟩ := Finset.mem_filter.mp hi
        rw [Q.bottom_body j hjR] at hiT
        refine Finset.mem_filter.mpr ⟨hiR, ?_⟩
        rw [Kakeya.VeryNotSticky.lineNbhd_eq_cthickening_range]
        exact Set.Subset.trans hiT ((T j).carrier_subset_cthickening_line_self (by norm_num))
      have hc := (Finset.card_le_card hsub).trans
        (hgeom.original_ed (T j).x (T j).direction (T j).norm_direction)
      have hcr : (G.card : Real) <= sourceBottomED := by exact_mod_cast hc
      rw [hDM]
      exact hcr.trans_lt (by norm_num [sourceBottomED, sourceThreadConstant])
    · have hk' : k < M := by omega
      let H := (Q.indexSet k).filter (fun j' => ∃ x y : EuclideanSpace Real (Fin 3),
        dist x y = 1 /\ segment Real x y <= (Q.tube k j).carrier /\
          segment Real x y <= (Q.tube k j').carrier)
      have hHj : j ∈ H := Finset.mem_filter.mpr ⟨hj, (Q.tube k j).x,
        (Q.tube k j).y, (Q.tube k j).dist_eq_one,
        fun _ hx => (Q.tube k j).mem_carrier_of_mem_segment hx,
        fun _ hx => (Q.tube k j).mem_carrier_of_mem_segment hx⟩
      have hmap : (G : Set iota).MapsTo (Q.place k) H := by
        intro i hi
        obtain ⟨hiR, hiG⟩ := Finset.mem_filter.mp hi
        refine Finset.mem_filter.mpr ⟨Q.place_mem k hk i hiR,
          (T i).x, (T i).y, (T i).dist_eq_one, ?_, ?_⟩
        · exact Set.Subset.trans (fun _ hx => (T i).mem_carrier_of_mem_segment hx) hiG
        · exact Set.Subset.trans (fun _ hx => (T i).mem_carrier_of_mem_segment hx)
            (Q.leaf_containment k hk i hiR)
      have hcount : (G.card : Real) <= ∑ j' ∈ H, ((Q.cell k j').card : Real) := by
        have heq := Finset.card_eq_sum_card_fiberwise hmap
        rw [heq, Nat.cast_sum]
        apply Finset.sum_le_sum
        intro j' hj'
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))
      have hstrict : (∑ j' ∈ H, ((Q.cell k j').card : Real)) < ∑ _j' ∈ H, 2 * D k := by
        apply Finset.sum_lt_sum_of_nonempty ⟨j, hHj⟩
        intro j' hj'
        exact ((hD k hk).2 j' (Finset.mem_filter.mp hj').1).2
      have hHcard : (H.card : Real) <= sourceThreadConstant := by
        exact_mod_cast hnear k hk' j hj
      calc (G.card : Real) <= ∑ j' ∈ H, ((Q.cell k j').card : Real) := hcount
        _ < ∑ _j' ∈ H, 2 * D k := hstrict
        _ = (H.card : Real) * (2 * D k) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ <= (sourceThreadConstant : Real) * (2 * D k) :=
          mul_le_mul_of_nonneg_right hHcard (by have := (hD k hk).1; positivity)
        _ = 2 * sourceThreadConstant * D k := by ring
  have hrealize : ∀ {delta : NNReal} {iota : Type u} {S : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))}
      (Q : SourceThreadedTower S T M sourceThreadConstant),
      SourceTowerGeometry Q sourceBottomED sourceLevelED -> SourceTowerNeighbourSharing Q ->
      ∀ C3 : Real,
      (∀ a b, a < b -> b < M -> ∀ j ∈ Q.indexSet a,
        ((Q.fibre a b j).card : Real) <= C3 *
          ((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M b : Real)) ^ 6) ->
      ∀ w : iota -> ENNReal, (∑ i ∈ S, w i) ≠ 0 ->
      ∃ (R : Finset iota) (Q' : SourceThreadedTower R T M sourceThreadConstant),
        R <= S /\ R.Nonempty /\ SourceTowerGeometry Q' sourceBottomED sourceLevelED /\
        (∑ i ∈ S, w i) <= sourceTowerSelectionLoss M S.card * ∑ i ∈ R, w i /\
        (∃ D : Nat -> Real, ∀ k, k <= M -> 0 < D k /\
          ∀ j ∈ Q'.indexSet k, D k <= ((Q'.cell k j).card : Real) /\
            ((Q'.cell k j).card : Real) < 2 * D k /\
            D k <= ((R.filter (fun i => (T i).toConvexSpaceBody <=
              (Q'.tube k j).toConvexSpaceBody)).card : Real) /\
            ((R.filter (fun i => (T i).toConvexSpaceBody <=
              (Q'.tube k j).toConvexSpaceBody)).card : Real) < 2 * sourceThreadConstant * D k) /\
        (∀ a b, a < b -> b < M -> ∀ j ∈ Q'.indexSet a,
          ((Q'.fibre a b j).card : Real) <= C3 *
            ((sourceTowerRadius delta M a : Real) / (sourceTowerRadius delta M b : Real)) ^ 6) := by
    intro delta iota S T Q hgeom hnear C3 hpack w hw
    obtain ⟨R, hRS, hRne, hmass, D, hD⟩ := hselect Q w hw
    obtain ⟨Q', hrest, hgeom', hnear'⟩ := hrestrict Q hgeom hnear R hRS hRne
    let D' : Nat -> Real := fun k => if k = M then 1 else D k
    have hD' (k : Nat) (hk : k <= M) : 0 < D' k /\ ∀ j ∈ Q'.indexSet k,
        D' k <= ((Q'.cell k j).card : Real) /\ ((Q'.cell k j).card : Real) < 2 * D' k := by
      by_cases hkM : k = M
      · subst k
        refine ⟨by norm_num [D'], ?_⟩
        intro j hj
        have hjR : j ∈ R := Q'.bottom_index ▸ hj
        have hcell : Q'.cell M j = {j} := by
          ext i
          simp only [SourceThreadedTower.cell, Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hi, hip⟩
            rwa [Q'.bottom_place i hi] at hip
          · intro hij
            subst i
            exact ⟨hjR, Q'.bottom_place j hjR⟩
        rw [hcell]
        norm_num [D']
      · refine ⟨by simpa only [D', if_neg hkM] using (hD k hk).1, ?_⟩
        intro j hj
        obtain ⟨i, hi, hip⟩ := Q'.place_surjective k hk j hj
        rw [hrest.assignment] at hip
        have hcell : Q'.cell k j = R.filter (fun l => Q.place k l = Q.place k i) := by
          rw [SourceThreadedTower.cell, hrest.assignment, hip]
        rw [hcell]
        simpa only [D', if_neg hkM] using (hD k hk).2 i hi
    have hgeo := hgeometric Q' hgeom' hnear' D' (by simp [D']) hD'
    refine ⟨R, Q', hRS, hRne, hgeom', hmass, ⟨D', ?_⟩, ?_⟩
    · intro k hk
      refine ⟨(hD' k hk).1, ?_⟩
      intro j hj
      exact ⟨((hD' k hk).2 j hj).1, ((hD' k hk).2 j hj).2, hgeo k hk j hj⟩
    · intro a b hab hb j hj
      have hjQ : j ∈ Q.indexSet a := by
        rw [hrest.occupied a (by omega)] at hj
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
        exact Q.place_mem a (by omega) i (hRS hi)
      have hsub : Q'.fibre a b j <= Q.fibre a b j := by
        rw [hrest.full_retained_fibres a b j]
        exact Finset.image_subset_image (Finset.filter_subset_filter _ hRS)
      exact (show ((Q'.fibre a b j).card : Real) <= ((Q.fibre a b j).card : Real) by
        exact_mod_cast Finset.card_le_card hsub).trans (hpack a b hab hb j hjQ)
  obtain ⟨delta0, C3, hd0, hdM, hC3, hraw⟩ := source_exists_unselected_nested_fixedTower M hM
  refine ⟨delta0, C3, hd0, hdM, hC3, ?_⟩
  intro delta hdelta hsmall iota S T hS hinj hcen hball hed w hw hfinite
  obtain ⟨Q, hgeom, hnear, hpack⟩ := hraw delta hdelta hsmall S T hS hinj hcen hball hed
  exact hrealize Q hgeom hnear C3 hpack w hw.ne'

/-- The source's chosen tower domain retains the additional neighbour-sharing obligation
needed by the one-trial caller, separate from the weighted proposition's fixed-segment row. -/
def SourceChosenTowerNeighbourRealization (M : Nat) : Prop :=
  ∀ᶠ delta : NNReal in 𝓝[>] 0,
    ∀ {iota : Type u} (S : Finset iota)
      (T : iota -> Tube delta (EuclideanSpace Real (Fin 3))),
      S.Nonempty -> Set.InjOn (fun i => (T i).toConvexSpaceBody) (S : Set iota) ->
      (∀ i ∈ S, (T i).IsCentred) ->
      (∀ i ∈ S, (T i).carrier <= Metric.closedBall 0 (3 / 4)) ->
      Kakeya.VeryNotSticky.IsLineEssDistinct sourceBottomED S T ->
    ∀ w : iota -> ENNReal, 0 < ∑ i ∈ S, w i -> (∑ i ∈ S, w i) ≠ ⊤ ->
    ∃ (R : Finset iota) (Q : SourceThreadedTower R T M sourceThreadConstant),
      R <= S /\ R.Nonempty /\ SourceTowerGeometry Q sourceBottomED sourceLevelED /\
      SourceTowerNeighbourSharing Q /\
      (∑ i ∈ S, w i) <= sourceTowerSelectionLoss M S.card * ∑ i ∈ R, w i

/-- Source S:6030-6098: one normalization and one chosen fixed tower, with all four
outer-preparation estimates on the SAME retained family and unchanged normalized shading.
The source neighbour-sharing row remains the separately named realization obligation above. -/
theorem source_exists_onceCentred_fixedTower (M : Nat) (hM : 2 <= M)
    {q eta0 : Real} (hq : 0 < q) (hbudget : 4 * q <= eta0) :
    ∃ delta0 : NNReal, 0 < delta0 /\ delta0 <= 1 / 200 /\
      ∀ delta : NNReal, 0 < delta -> delta < delta0 ->
      ∀ {iota : Type u} (S : Finset iota)
        (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        S.Nonempty -> (∀ i ∈ S, (Z i).carrier <= Metric.closedBall 0 1) ->
        Kakeya.maxDensity S (fun i => (Z i).toConvexSpaceBody) <= (delta : ENNReal) ^ (-q) ->
        (delta : ENNReal) ^ q <= ShadedBody.fullness' S (fun i => (Z i).toShadedBody) ->
      ∃ (I R : Finset iota) (Y : iota -> ShadedTube (delta / 2) (EuclideanSpace Real (Fin 3)))
        (pi : iota -> iota)
        (Q : SourceThreadedTower R (fun i => (Y i).toTube) M sourceThreadConstant),
        SourceCanonicalNormalization S I Z Y pi q /\ R <= I /\ R.Nonempty /\
        SourceTowerGeometry Q sourceBottomED sourceLevelED /\
        (∑ i ∈ I, volume (Y i).shade) <=
          sourceTowerSelectionLoss M I.card * ∑ i ∈ R, volume (Y i).shade /\
        sourceCentringCost delta q * sourceTowerSelectionLoss M I.card <=
          ((delta / 2 : NNReal) : ENNReal) ^ (-(3 * q)) /\
        ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
          ((delta / 2 : NNReal) : ENNReal) ^ (-(3 * q)) *
            ShadedBody.multiplicity R (fun i => (Y i).toShadedBody) /\
        R.card <= S.card /\
        Kakeya.maxDensity R (fun i => (Y i).toConvexSpaceBody) <=
          ((delta / 2 : NNReal) : ENNReal) ^ (-eta0) /\
        ((delta / 2 : NNReal) : ENNReal) ^ eta0 <=
          ShadedBody.fullness' R (fun i => (Y i).toShadedBody) := by
  classical
  have heta0 : 0 < eta0 := by linarith
  obtain ⟨dt, C3, hdt, hdtM, hC3, htower⟩ := source_exists_weighted_chosen_fixedTower M hM
  let C0 : ENNReal := 100 * (5000 : ENNReal) ^ 6
  have hC0 : 1 <= C0 := by norm_num [C0]
  have hselection : ∀ᶠ delta : NNReal in 𝓝[>] 0, ∀ n : Nat, 1 <= n ->
      (n : ENNReal) <= (delta : ENNReal) ^ (-(q + 3)) ->
      sourceTowerSelectionLoss M n <= (delta : ENNReal) ^ (-q) := by
    filter_upwards [Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (K := ENNReal.ofReal (q + 5) ^ (M + 1)) (by finiteness) (by positivity : 0 < q / 2),
      ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg (by positivity : 0 < q / 2) (M + 1),
      Ioo_mem_nhdsGT (by norm_num : (0 : NNReal) < 1)] with delta hc hl hd
    intro n hn hncard
    have hdreal : (0 : Real) < delta := by exact_mod_cast hd.1
    have hd1 : (delta : Real) <= 1 := by exact_mod_cast hd.2.le
    have hd0 : (delta : ENNReal) ≠ 0 := by exact_mod_cast hd.1.ne'
    have hnr : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
    have hcardReal : (n : Real) <= (delta : Real) ^ (-(q + 3)) := by
      have ht := ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_ne_zero hd0 ENNReal.coe_ne_top) hncard
      simpa only [← ENNReal.toReal_rpow, ENNReal.coe_toReal, ENNReal.toReal_natCast] using ht
    let l : Real := Real.logb 2 (1 / (delta : Real))
    have hl0 : 0 <= l := Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hdreal]; linarith)
    have hlogcard : Real.logb 2 (n : Real) <= (q + 3) * l := by
      have hb := Real.logb_le_logb_of_le (by norm_num : (1 : Real) < 2) hnr hcardReal
      rw [Real.logb_rpow_eq_mul_logb_of_pos hdreal] at hb
      dsimp [l]
      rw [one_div, Real.logb_inv]
      nlinarith
    have hlog0 : 0 <= Real.logb 2 (n : Real) := Real.logb_nonneg (by norm_num) (by exact_mod_cast hn)
    have hceil : ((Nat.ceil (Real.logb 2 (n : Real)) + 1 : Nat) : Real) <= (q + 5) * (1 + l) := by
      have hb := Nat.ceil_lt_add_one hlog0
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith
    have hbound : sourceTowerSelectionLoss M n <=
        ENNReal.ofReal (q + 5) ^ (M + 1) * ENNReal.ofReal (1 + l) ^ (M + 1) := by
      have hb := ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hceil (M + 1))
      simpa only [sourceTowerSelectionLoss,
        ENNReal.ofReal_pow (by positivity : (0 : Real) <= ((Nat.ceil (Real.logb 2 (n : Real)) + 1 : Nat) : Real)),
        ENNReal.ofReal_pow (by positivity : (0 : Real) <= (q + 5) * (1 + l)),
        ENNReal.ofReal_pow (by positivity : (0 : Real) <= q + 5),
        ENNReal.ofReal_pow (by positivity : (0 : Real) <= 1 + l),
        ENNReal.ofReal_mul (by positivity : (0 : Real) <= (q + 5) ^ (M + 1)),
        ENNReal.ofReal_natCast, ENNReal.ofReal_mul (by positivity : (0 : Real) <= q + 5), mul_pow] using hb
    calc sourceTowerSelectionLoss M n <=
          ENNReal.ofReal (q + 5) ^ (M + 1) * ENNReal.ofReal (1 + l) ^ (M + 1) := hbound
      _ <= (delta : ENNReal) ^ (-(q / 2)) * (delta : ENNReal) ^ (-(q / 2)) := mul_le_mul' hc hl
      _ = (delta : ENNReal) ^ (-q) := by
          rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
          congr 1
          ring
  let ccard : ENNReal := Kakeya.Tube.card_le_of_densityIn_le.C 3
  have hevent : ∀ᶠ delta : NNReal in 𝓝[>] 0,
      ccard <= (delta : ENNReal) ^ (-1 : Real) /\
      384 * C0 <= (delta : ENNReal) ^ (-q) /\
      (∀ n : Nat, 1 <= n -> (n : ENNReal) <= (delta : ENNReal) ^ (-(q + 3)) ->
        sourceTowerSelectionLoss M n <= (delta : ENNReal) ^ (-q)) := by
    filter_upwards [Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (K := ccard) ENNReal.coe_ne_top (by norm_num : (0 : Real) < 1),
      Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg (K := 384 * C0) (by finiteness) hq,
      hselection] with delta hc hC hs
    exact ⟨hc, hC, hs⟩
  obtain ⟨eps, heps, hall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  let delta0 := min eps (min dt (1 / 200))
  have hdelta00 : 0 < delta0 := lt_min heps (lt_min hdt (by norm_num))
  have hdelta01 : delta0 <= 1 / 200 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨delta0, hdelta00, hdelta01, ?_⟩
  intro delta hdelta hdeltaBound iota S Z hS hball hdens hfull
  have hsmall : delta <= 1 / 200 := hdeltaBound.le.trans hdelta01
  have hdelta1 : delta <= 1 := hsmall.trans (by
    norm_num [div_le_iff₀ (show (0 : NNReal) < 200 by norm_num)])
  have hd0 : (delta : ENNReal) ≠ 0 := by exact_mod_cast hdelta.ne'
  have hd1 : (delta : ENNReal) <= 1 := by exact_mod_cast hdelta1
  obtain ⟨hcardδ, hCδ, hselδ⟩ := hall ⟨hdelta, hdeltaBound.trans_le (min_le_left _ _)⟩
  have hcardS : (S.card : ENNReal) <= (delta : ENNReal) ^ (-(q + 3)) := by
    have hc := Kakeya.Tube.card_le_of_densityIn_le hdelta.ne' hball
      ((Kakeya.le_maxDensity S (fun i => (Z i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall).trans hdens)
    have hc' : (S.card : ENNReal) <= ccard * (delta : ENNReal) ^ (-q) * (delta : ENNReal) ^ (-2 : Real) := by
      rw [show (-2 : Real) = ((-2 : Int) : Real) by norm_num, ENNReal.rpow_intCast]
      simpa only [show Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3 by simp,
        Nat.cast_ofNat, show -((3 : Int) - 1) = -2 by norm_num] using hc
    calc (S.card : ENNReal) <= ccard * (delta : ENNReal) ^ (-q) * (delta : ENNReal) ^ (-2 : Real) := hc'
      _ <= (delta : ENNReal) ^ (-1 : Real) * (delta : ENNReal) ^ (-q) * (delta : ENNReal) ^ (-2 : Real) :=
          mul_le_mul_left (mul_le_mul_left hcardδ _) _
      _ = (delta : ENNReal) ^ (-(q + 3)) := by
          rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top, ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
          congr 1
          ring
  obtain ⟨I, Y, pi, hnorm⟩ := source_exists_canonical_normalization hq hdelta hsmall S Z hS hball hdens hfull
  have hmassS0 : (∑ i ∈ S, volume (Z i).shade) ≠ 0 := by
    intro hzero
    have hfzero : ShadedBody.fullness' S (fun i => (Z i).toShadedBody) = 0 := by
      simp only [ShadedBody.fullness', hzero, ENNReal.zero_div]
    exact (ENNReal.rpow_pos (by exact_mod_cast hdelta) ENNReal.coe_ne_top).ne'
      (le_antisymm (hfzero ▸ hfull) zero_le)
  have hmassI0 : (∑ i ∈ I, volume (Y i).shade) ≠ 0 := by
    intro hzero
    have hb := hnorm.mass_lower
    rw [hzero, mul_zero] at hb
    exact mul_ne_zero (by norm_num : (1 / 512 : ENNReal) ≠ 0) hmassS0 (le_antisymm hb zero_le)
  have hmassItop : (∑ i ∈ I, volume (Y i).shade) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i _ => ne_top_of_le_ne_top
      (Y i).isCompact'.measure_ne_top (measure_mono (Y i).shade_subset)
  have hrho : 0 < delta / 2 := div_pos hdelta (by norm_num)
  have hrhole : delta / 2 <= delta := div_le_self zero_le (by norm_num)
  have hrhodt : delta / 2 < dt := hrhole.trans_lt
    (hdeltaBound.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨R, Q, hRI, hRne, hgeom, hmass, -, -⟩ := htower (delta / 2) hrho hrhodt I
    (fun i => (Y i).toTube) hnorm.nonempty hnorm.body_injective hnorm.centred hnorm.ball hnorm.ed
    (fun i => volume (Y i).shade) (pos_iff_ne_zero.mpr hmassI0) hmassItop
  have hIc : (I.card : ENNReal) <= (S.card : ENNReal) := by exact_mod_cast hnorm.card_upper
  have hL : sourceTowerSelectionLoss M I.card <= (delta : ENNReal) ^ (-q) :=
    hselδ I.card (Finset.card_pos.mpr hnorm.nonempty)
      (hIc.trans hcardS)
  have hcombined : 384 * sourceCentringCost delta q * sourceTowerSelectionLoss M I.card <=
      (delta : ENNReal) ^ (-(3 * q)) := by
    calc 384 * sourceCentringCost delta q * sourceTowerSelectionLoss M I.card =
          (384 * C0) * (delta : ENNReal) ^ (-q) * sourceTowerSelectionLoss M I.card := by
            dsimp [sourceCentringCost, C0]
            ac_rfl
      _ <= (delta : ENNReal) ^ (-q) * (delta : ENNReal) ^ (-q) * (delta : ENNReal) ^ (-q) :=
          mul_le_mul' (mul_le_mul_left hCδ _) hL
      _ = (delta : ENNReal) ^ (-(3 * q)) := by
          rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top, ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
          congr 1
          ring
  have hnegative (p : Real) (hp : 0 <= p) : (delta : ENNReal) ^ (-p) <=
      ((delta / 2 : NNReal) : ENNReal) ^ (-p) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (by exact_mod_cast hrhole) hp)
  have hcost : sourceCentringCost delta q * sourceTowerSelectionLoss M I.card <=
      ((delta / 2 : NNReal) : ENNReal) ^ (-(3 * q)) := by
    calc sourceCentringCost delta q * sourceTowerSelectionLoss M I.card <=
          384 * sourceCentringCost delta q * sourceTowerSelectionLoss M I.card := by
            gcongr
            exact le_mul_of_one_le_left zero_le (by norm_num : (1 : ENNReal) <= 384)
      _ <= (delta : ENNReal) ^ (-(3 * q)) := hcombined
      _ <= ((delta / 2 : NNReal) : ENNReal) ^ (-(3 * q)) := hnegative _ (by positivity)
  have hmultIR : ShadedBody.multiplicity I (fun i => (Y i).toShadedBody) <=
      sourceTowerSelectionLoss M I.card * ShadedBody.multiplicity R (fun i => (Y i).toShadedBody) := by
    apply ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset I
      (fun i => (Y i).toShadedBody) R (fun i => (Y i).toShadedBody) _ _ hmass
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, hRI hi, hxi⟩
  have hfullIR : ShadedBody.fullness' I (fun i => (Y i).toShadedBody) <=
      sourceTowerSelectionLoss M I.card * ShadedBody.fullness' R (fun i => (Y i).toShadedBody) := by
    change (∑ i ∈ I, volume (Y i).shade) / (∑ i ∈ I, volume (Y i).carrier) <=
      sourceTowerSelectionLoss M I.card * ((∑ i ∈ R, volume (Y i).shade) / (∑ i ∈ R, volume (Y i).carrier))
    calc (∑ i ∈ I, volume (Y i).shade) / (∑ i ∈ I, volume (Y i).carrier) <=
          (sourceTowerSelectionLoss M I.card * ∑ i ∈ R, volume (Y i).shade) / (∑ i ∈ I, volume (Y i).carrier) :=
            ENNReal.div_le_div_right hmass _
      _ = sourceTowerSelectionLoss M I.card * ((∑ i ∈ R, volume (Y i).shade) / (∑ i ∈ I, volume (Y i).carrier)) :=
          mul_div_assoc _ _ _
      _ <= sourceTowerSelectionLoss M I.card * ((∑ i ∈ R, volume (Y i).shade) / (∑ i ∈ R, volume (Y i).carrier)) :=
          mul_le_mul_right (ENNReal.div_le_div_left
            (Finset.sum_le_sum_of_subset_of_nonneg hRI (fun _ _ _ => zero_le)) _) _
  refine ⟨I, R, Y, pi, Q, hnorm, hRI, hRne, hgeom, hmass, hcost, ?_,
    (Finset.card_le_card hRI).trans hnorm.card_upper, ?_, ?_⟩
  · calc ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
          sourceCentringCost delta q * ShadedBody.multiplicity I (fun i => (Y i).toShadedBody) := hnorm.multiplicity_upper
      _ <= sourceCentringCost delta q * (sourceTowerSelectionLoss M I.card *
          ShadedBody.multiplicity R (fun i => (Y i).toShadedBody)) := mul_le_mul_right hmultIR _
      _ <= ((delta / 2 : NNReal) : ENNReal) ^ (-(3 * q)) *
          ShadedBody.multiplicity R (fun i => (Y i).toShadedBody) := by
            rw [← mul_assoc]
            exact mul_le_mul_left hcost _
  · calc Kakeya.maxDensity R (fun i => (Y i).toConvexSpaceBody) <=
          384 * (delta : ENNReal) ^ (-q) := (Kakeya.maxDensity_mono _ hRI).trans hnorm.density
      _ <= (384 * C0) * (delta : ENNReal) ^ (-q) := by
          apply mul_le_mul_left
          exact le_mul_of_one_le_right zero_le hC0
      _ <= (delta : ENNReal) ^ (-q) * (delta : ENNReal) ^ (-q) := mul_le_mul_left hCδ _
      _ = (delta : ENNReal) ^ (-(2 * q)) := by
          rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
          congr 1
          ring
      _ <= (delta : ENNReal) ^ (-eta0) := ENNReal.rpow_le_rpow_of_exponent_ge hd1 (by linarith)
      _ <= ((delta / 2 : NNReal) : ENNReal) ^ (-eta0) := hnegative _ heta0.le
  · have hfloor : (delta : ENNReal) ^ q <= (delta : ENNReal) ^ (-(3 * q)) *
        ShadedBody.fullness' R (fun i => (Y i).toShadedBody) := by
      calc (delta : ENNReal) ^ q <= ShadedBody.fullness' S (fun i => (Z i).toShadedBody) := hfull
        _ <= (384 * sourceCentringCost delta q) * ShadedBody.fullness' I (fun i => (Y i).toShadedBody) := hnorm.fullness
        _ <= (384 * sourceCentringCost delta q) * (sourceTowerSelectionLoss M I.card *
            ShadedBody.fullness' R (fun i => (Y i).toShadedBody)) := mul_le_mul_right hfullIR _
        _ <= (delta : ENNReal) ^ (-(3 * q)) * ShadedBody.fullness' R (fun i => (Y i).toShadedBody) := by
            rw [← mul_assoc]
            exact mul_le_mul_left hcombined _
    calc ((delta / 2 : NNReal) : ENNReal) ^ eta0 <= (delta : ENNReal) ^ eta0 :=
          ENNReal.rpow_le_rpow (by exact_mod_cast hrhole) heta0.le
      _ <= (delta : ENNReal) ^ (4 * q) := ENNReal.rpow_le_rpow_of_exponent_ge hd1 hbudget
      _ = (delta : ENNReal) ^ (3 * q) * (delta : ENNReal) ^ q := by
          rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
          congr 1
          ring
      _ <= (delta : ENNReal) ^ (3 * q) * ((delta : ENNReal) ^ (-(3 * q)) *
          ShadedBody.fullness' R (fun i => (Y i).toShadedBody)) := mul_le_mul_right hfloor _
      _ = ShadedBody.fullness' R (fun i => (Y i).toShadedBody) := by
          rw [← mul_assoc, ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
          simp

end Kakeya.ML2Core
