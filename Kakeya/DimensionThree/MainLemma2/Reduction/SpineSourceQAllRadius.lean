/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceQMiddleSelection

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Kakeya.ML2Core Kakeya.ML2Reduction Kakeya.VeryNotSticky
open scoped NNReal ENNReal

namespace Kakeya.ML2Assembly

universe u

/-- All scalar choices precede delta. The strict last margin absorbs fixed
normalization, cover extraction and 56/10^30 bridge constants. -/
structure SourceQCoverParameters (M A0 A1 C : Nat) (e varpi zeta etaC R : Real) : Prop where
  levels : 2 <= M
  bottom_ed : 1 <= A0
  level_ed : 1 <= A1
  threads : 1 <= C
  window_pos : 0 < e
  window_upper : e <= varpi / 8
  vns_window_pos : 0 < varpi
  vns_window_upper : varpi < 1 / 2
  excess_pos : 0 < zeta
  excess_upper : zeta <= 1 / 4
  input_pos : 0 < etaC
  radius_lower : 2 <= R
  normalization : (Tube.normalization.C 3 : Real) <= R
  mesh_margin : 1 / (M : Real) < e * varpi / 100
  count_margin : 6 * etaC + 3 / (M : Real) < e * varpi * zeta / 4

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- The original (a,b) source window, its actual parent and the same selected F.
No arbitrary-cover or analytic row occurs in this input. -/
structure SourceQCoverInput (Q : SourceThreadedTower S T M C)
    (a p b : Nat) (jp : iota) (F : Finset iota)
    (Z : iota -> ShadedTube (sourceTowerRadius delta M b) (EuclideanSpace Real (Fin 3)))
    (rho : NNReal) (e zeta etaC : Real) : Prop where
  delta_pos : 0 < delta
  delta_small : delta < (40 : NNReal) ^ (-(M : Real))
  coarse_le_parent : a <= p
  parent_lt_middle : p < b
  middle_bound : b <= M
  parent_member : jp ∈ Q.indexSet p
  family_nonempty : F.Nonempty
  family_subset : F <= Q.fibre p b jp
  family_tubes : forall i, (Z i).toTube = Q.tube b i
  same_parent_retention : (delta : Real) ^ (6 * etaC) *
    ((Q.fibre p b jp).card : Real) <= (F.card : Real)
  rho_eq : rho = sourceTowerRadius delta M b / (2 * sourceTowerRadius delta M p)
  rho_lower : 20 * delta <= rho
  rho_upper : (rho : Real) <= (delta : Real) ^ (e / 2) / 2
  original_window_separation :
    (sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M a : Real) <=
      (delta : Real) ^ e
  parent_ratio : (sourceTowerRadius delta M b : Real) /
      (sourceTowerRadius delta M p : Real) <= (delta : Real) ^ (-2 / (M : Real)) *
      ((sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M a : Real)) ^ (1 - e)
  parent_before_window : forall k, SourceTowerWindow delta M e a b k -> p < k
  count_floor : forall k, SourceTowerWindow delta M e a b k ->
    ((sourceTowerRadius delta M p : Real) / (sourceTowerRadius delta M k : Real)) ^
      (2 + 4 * zeta) <= ((Q.fibre p k jp).card : Real)

/-- All-radius downstairs covers are covers of the actual affine images. -/
def SourceQImageCovered {b tau rho : NNReal} {R : Real}
    (hsit : Tube.IsRescalingSituation b tau rho R 3) (hR : 0 < R)
    (T0 : Tube b (EuclideanSpace Real (Fin 3))) (E : Finset iota)
    (Z : iota -> ShadedTube tau (EuclideanSpace Real (Fin 3)))
    {kappa : Type u} {sigma : NNReal} (W : Finset kappa)
    (V : kappa -> Tube sigma (EuclideanSpace Real (Fin 3))) : Prop :=
  forall i, i ∈ E -> exists j, j ∈ W /\
    (spineFamily (spineRescaleUnit hsit.pos_ambient T0 hR) Z i).toConvexSpaceBody <=
      (V j).toConvexSpaceBody

open scoped Classical in
/-- The complete finite counting diagram, including geometric charge placement.
Every surviving ancestor has an actual E-child assigned to its charged cover. -/
structure SourceQCoverCharge (Q : SourceThreadedTower S T M C)
    (a p b : Nat) (jp : iota) (E : Finset iota) (e G : Real)
    {kappa : Type u} {sigma : NNReal} (W : Finset kappa)
    (V : kappa -> Tube sigma (EuclideanSpace Real (Fin 3))) where
  level : Nat
  descendants : Nat
  charge : iota -> kappa
  child : iota -> iota
  linePoint : kappa -> EuclideanSpace Real (Fin 3)
  lineDirection : kappa -> EuclideanSpace Real (Fin 3)
  level_window : SourceTowerWindow delta M e a b level
  parent_before : p < level
  descendants_pos : 0 < descendants
  descendant_lower : forall j, j ∈ Q.fibre p level jp -> descendants <=
    ((Q.fibre p b jp).filter (fun i => sourceQAncestor Q level b i = j)).card
  descendant_upper : forall j, j ∈ Q.fibre p level jp ->
    ((Q.fibre p b jp).filter (fun i => sourceQAncestor Q level b i = j)).card <=
      2 * descendants
  grid_lower : G * (sourceTowerRadius delta M p : Real) * (sigma : Real) <=
    (sourceTowerRadius delta M level : Real)
  grid_upper : (sourceTowerRadius delta M level : Real) <
    G * (sourceTowerRadius delta M p : Real) * (sigma : Real) /
      (delta : Real) ^ (1 / (M : Real))
  child_member : forall j, j ∈ E.image (sourceQAncestor Q level b) -> child j ∈ E
  child_ancestor : forall j, j ∈ E.image (sourceQAncestor Q level b) ->
    sourceQAncestor Q level b (child j) = j
  charge_member : forall j, j ∈ E.image (sourceQAncestor Q level b) -> charge j ∈ W
  direction_unit : forall w, w ∈ W -> norm (lineDirection w) = 1
  ancestor_placement : forall j, j ∈ E.image (sourceQAncestor Q level b) ->
    (Q.tube level j).carrier <= lineNbhd (linePoint (charge j)) (lineDirection (charge j))
      (5 * (sourceTowerRadius delta M level : Real))

set_option maxHeartbeats 8000000 in
open scoped Classical in
/-- S:4597-4630 and 5484-5672, now including the missing geometry.
G is the fixed transverse constant for the actual rescaleMap R. At R=2 the
source formula has 56; the endpoint-centred map differs only by a translation.
No operator-norm pullback or fixed-radius interpolation is assumed. -/
theorem sourceQ_exists_allRadius_charge (M A0 A1 C : Nat)
    (e varpi zeta etaC R : Real)
    (hp : SourceQCoverParameters M A0 A1 C e varpi zeta etaC R) :
    exists G : Real, 56 <= G /\
    ∀ᶠ delta : NNReal in 𝓝[>] 0,
      forall {iota : Type u} (S : Finset iota)
        (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
        (Q : SourceThreadedTower S T M C)
        (Y : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
      SourceTowerGeometry Q A0 A1 -> SourceTowerStatistics Q Y ->
      forall (a p b : Nat) (jp : iota) (F E : Finset iota)
        (Z : iota -> ShadedTube (sourceTowerRadius delta M b) (EuclideanSpace Real (Fin 3)))
        (rho : NNReal), SourceQCoverInput Q a p b jp F Z rho e zeta etaC ->
      E <= F -> (rho : Real) ^ (varpi * zeta / 16) * (F.card : Real) <= (E.card : Real) ->
      forall (hsit : Tube.IsRescalingSituation (sourceTowerRadius delta M p)
          (sourceTowerRadius delta M b) rho R 3) (hR : 0 < R)
        (sigma : NNReal),
      sigma ∈ Set.Icc (rho ^ (1 - varpi / 2)) (rho ^ (varpi / 2)) ->
      forall {kappa : Type u} (W : Finset kappa)
        (V : kappa -> Tube sigma (EuclideanSpace Real (Fin 3))),
      SourceQImageCovered hsit hR (Q.tube p jp) E Z W V ->
      exists B : SourceQCoverCharge Q a p b jp E e G W V,
        (forall j, j ∈ E.image (sourceQAncestor Q B.level b) ->
          (spineFamily (spineRescaleUnit hsit.pos_ambient (Q.tube p jp) hR)
            Z (B.child j)).toConvexSpaceBody <= (V (B.charge j)).toConvexSpaceBody) /\
        (forall w, w ∈ W ->
          ((E.image (sourceQAncestor Q B.level b)).filter (fun j => B.charge j = w)).card <= A1) /\
        (rho : Real) ^ (varpi * zeta / 16) * (sigma : Real) ^ (-2 - 2 * zeta) <=
          (W.card : Real) := by
  set_option maxHeartbeats 8000000 in
  exact (by
    classical
    have hgrid (M A0 A1 C : Nat) (e varpi zeta etaC R G : Real)
        (hp : SourceQCoverParameters M A0 A1 C e varpi zeta etaC R) (hG : 56 <= G) :
        ∀ᶠ delta : NNReal in 𝓝[>] 0,
          forall {iota : Type u} (S : Finset iota)
            (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
            (Q : SourceThreadedTower S T M C)
            (a p b : Nat) (jp : iota) (F : Finset iota)
            (Z : iota -> ShadedTube (sourceTowerRadius delta M b) (EuclideanSpace Real (Fin 3)))
            (rho sigma : NNReal),
            SourceQCoverInput Q a p b jp F Z rho e zeta etaC ->
            sigma ∈ Set.Icc (rho ^ (1 - varpi / 2)) (rho ^ (varpi / 2)) ->
            exists k, SourceTowerWindow delta M e a b k /\ p < k /\
              G * (sourceTowerRadius delta M p : Real) * (sigma : Real) <=
                (sourceTowerRadius delta M k : Real) /\
              (sourceTowerRadius delta M k : Real) <
                G * (sourceTowerRadius delta M p : Real) * (sigma : Real) /
                  (delta : Real) ^ (1 / (M : Real)) := by
      classical
      have he := hp.window_pos
      have hv := hp.vns_window_pos
      have he1 : e < 1 / 4 := by linarith [hp.window_upper, hp.vns_window_upper]
      have hve : 0 < varpi / 2 - e := by linarith [hp.window_upper]
      have hcost : 0 < e * (varpi / 2 - e) - 1 / (M : Real) := by
        nlinarith [hp.mesh_margin, mul_nonneg he.le (sub_nonneg.mpr hp.window_upper), mul_pos he hv]
      have hA : 0 < varpi / 2 * (1 - e) - e := by
        nlinarith [hp.window_upper, mul_nonneg hv.le (sub_nonneg.mpr he1.le)]
      have hmargin : 0 <= e * (varpi / 2 * (1 - e) - e) -
          varpi / (M : Real) := by
        have hm := mul_lt_mul_of_pos_left hp.mesh_margin hv
        have h1 := mul_nonneg he.le (sub_nonneg.mpr hp.window_upper)
        have h2 := mul_nonneg (mul_nonneg he.le hv.le) (sub_nonneg.mpr he1.le)
        have h3 := mul_nonneg (mul_nonneg he.le hv.le)
          (sub_nonneg.mpr hp.vns_window_upper.le)
        simp only [div_eq_mul_inv] at hm ⊢
        nlinarith only [hm, h1, h2, h3, mul_pos he hv]
      obtain ⟨d0, hd0, hd01, hconst⟩ := ML2Shaded.exists_threshold_const_le_rpow_neg' G hcost
      filter_upwards [Ioo_mem_nhdsGT hd0,
        source_eventually_fixed_tower_radius_conditions M hp.levels he] with delta hd hrad
      intro iota S T Q a p b jp F Z rho sigma hi hsigma
      have hap := hi.coarse_le_parent
      have hpb := hi.parent_lt_middle
      have hbM := hi.middle_bound
      have hdR : (0 : Real) < delta := by exact_mod_cast hd.1
      have hd1 : (delta : Real) <= 1 := by exact_mod_cast hd.2.le.trans hd01
      have hM : 0 < M := by have := hp.levels; omega
      have hM0 : (0 : Real) < M := by exact_mod_cast hM
      have hradEq (k : Nat) : (sourceTowerRadius delta M k : Real) =
          bridgeGrid M (delta : Real) k := by
        simp only [sourceTowerRadius, bridgeGrid]
        split <;> simp only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_one,
          NNReal.coe_ofNat, NNReal.coe_rpow]
      have hrpos (k : Nat) : (0 : Real) < sourceTowerRadius delta M k := by
        rw [hradEq]
        exact bridgeGrid_pos hdR k
      have hra0 := hrpos a
      have hrp0 := hrpos p
      have hrb0 := hrpos b
      have hG0 : 0 < G := by linarith
      have hmono : Antitone (fun k : Nat => (sourceTowerRadius delta M k : Real)) := by
        apply antitone_nat_of_succ_le
        intro k
        by_cases hk : k < M
        · have hh := hrad.2.2.2.2.2 k hk
          have hhR : (sourceTowerRadius delta M (k + 1) : Real) <=
              (sourceTowerRadius delta M k : Real) / 2 := by exact_mod_cast hh
          linarith [hrpos k]
        · simp only [sourceTowerRadius, if_neg hk, if_neg (show ¬ k + 1 < M by omega)]
          rfl
      let t : Real := (sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M a : Real)
      let x : Real := (sourceTowerRadius delta M b : Real) / (sourceTowerRadius delta M p : Real)
      let q : Real := (delta : Real) ^ (1 / (M : Real))
      have ht0 : 0 < t := div_pos (hrpos b) (hrpos a)
      have hx0 : 0 < x := div_pos (hrpos b) (hrpos p)
      have hq0 : 0 < q := Real.rpow_pos_of_pos hdR _
      have ht1 : t <= 1 := (div_le_one (hrpos a)).2 (hmono (by omega))
      have hx1 : x <= 1 := (div_le_one (hrpos p)).2 (hmono hi.parent_lt_middle.le)
      have htx : t <= x := div_le_div_of_nonneg_left (hrpos b).le (hrpos p)
        (hmono hi.coarse_le_parent)
      have hrho : (rho : Real) = x / 2 := by
        rw [hi.rho_eq]
        push_cast
        dsimp [x]
        ring
      have hrho0 : (0 : Real) < rho := by rw [hrho]; positivity
      have hrho1 : (rho : Real) <= 1 := by rw [hrho]; linarith
      have hslo : (x / 2) ^ (1 - varpi / 2) <= (sigma : Real) := by
        simpa only [NNReal.coe_rpow, hrho] using
          (show ((rho ^ (1 - varpi / 2) : NNReal) : Real) <= sigma by exact_mod_cast hsigma.1)
      have hshi : (sigma : Real) <= (x / 2) ^ (varpi / 2) := by
        simpa only [NNReal.coe_rpow, hrho] using
          (show (sigma : Real) <= ((rho ^ (varpi / 2) : NNReal) : Real) by exact_mod_cast hsigma.2)
      have hs0 : (0 : Real) < sigma := (Real.rpow_pos_of_pos (by positivity : 0 < x / 2) _).trans_le hslo
      have hslo' : x / 2 <= (sigma : Real) := by
        calc x / 2 = (x / 2) ^ (1 : Real) := (Real.rpow_one _).symm
          _ <= (x / 2) ^ (1 - varpi / 2) :=
            Real.rpow_le_rpow_of_exponent_ge (by positivity) (by linarith) (by linarith)
          _ <= _ := hslo
      have hfixed : G * (delta : Real) ^ (e * (varpi / 2 - e)) <= q := by
        have hc := hconst hd.1 hd.2.le
        calc G * (delta : Real) ^ (e * (varpi / 2 - e)) <=
              (delta : Real) ^ (-(e * (varpi / 2 - e) - 1 / (M : Real))) *
                (delta : Real) ^ (e * (varpi / 2 - e)) :=
              mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hdR.le _)
          _ = q := by rw [← Real.rpow_add hdR]; congr 1 <;> ring
      have htest : G * (sigma : Real) * t ^ (1 - e) <= q * x := by
        have htpow : t ^ (varpi / 2 - e) <= (delta : Real) ^ (e * (varpi / 2 - e)) := by
          rw [Real.rpow_mul hdR.le]
          exact Real.rpow_le_rpow ht0.le hi.original_window_separation hve.le
        have hratio : x ^ (varpi / 2) * t ^ (1 - e) <= x * t ^ (varpi / 2 - e) := by
          have hcomp := Real.rpow_le_rpow ht0.le htx
            (show 0 <= 1 - varpi / 2 by linarith [hp.vns_window_upper])
          have heq : t ^ (1 - e) = t ^ (1 - varpi / 2) * t ^ (varpi / 2 - e) := by
            rw [← Real.rpow_add ht0]; congr 1 <;> ring
          rw [heq, ← mul_assoc]
          calc x ^ (varpi / 2) * t ^ (1 - varpi / 2) * t ^ (varpi / 2 - e) <=
                x ^ (varpi / 2) * x ^ (1 - varpi / 2) * t ^ (varpi / 2 - e) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcomp
                    (Real.rpow_nonneg hx0.le _)) (Real.rpow_nonneg ht0.le _)
            _ = _ := by rw [← Real.rpow_add hx0]; simp
        have hsx := hshi.trans (Real.rpow_le_rpow (by positivity : 0 <= x / 2)
          (by linarith : x / 2 <= x) (by linarith : 0 <= varpi / 2))
        calc G * (sigma : Real) * t ^ (1 - e) <=
              G * (x ^ (varpi / 2) * t ^ (1 - e)) := by
                rw [mul_assoc]
                exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsx
                  (Real.rpow_nonneg ht0.le _)) (by linarith)
          _ <= G * (x * t ^ (varpi / 2 - e)) := mul_le_mul_of_nonneg_left hratio (by linarith)
          _ <= G * (x * (delta : Real) ^ (e * (varpi / 2 - e))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htpow hx0.le) (by linarith)
          _ = (G * (delta : Real) ^ (e * (varpi / 2 - e))) * x := by ring
          _ <= q * x := mul_le_mul_of_nonneg_right hfixed hx0.le
      have hxpow : x ^ (varpi / 2) <= t ^ e := by
        have htA : t ^ (varpi / 2 * (1 - e) - e) <=
            (delta : Real) ^ (e * (varpi / 2 * (1 - e) - e)) := by
          rw [Real.rpow_mul hdR.le]
          exact Real.rpow_le_rpow ht0.le hi.original_window_separation hA.le
        have hcombine : (delta : Real) ^ (-varpi / (M : Real)) *
            t ^ (varpi / 2 * (1 - e) - e) <= 1 := by
          calc (delta : Real) ^ (-varpi / (M : Real)) * t ^ (varpi / 2 * (1 - e) - e) <=
                (delta : Real) ^ (-varpi / (M : Real)) *
                  (delta : Real) ^ (e * (varpi / 2 * (1 - e) - e)) :=
                    mul_le_mul_of_nonneg_left htA (Real.rpow_nonneg hdR.le _)
            _ = (delta : Real) ^ (e * (varpi / 2 * (1 - e) - e) - varpi / (M : Real)) := by
              rw [← Real.rpow_add hdR]; congr 1 <;> ring
            _ <= 1 := Real.rpow_le_one hdR.le hd1 hmargin
        calc x ^ (varpi / 2) <= ((delta : Real) ^ (-2 / (M : Real)) * t ^ (1 - e)) ^ (varpi / 2) :=
              Real.rpow_le_rpow hx0.le hi.parent_ratio (by linarith)
          _ = ((delta : Real) ^ (-varpi / (M : Real)) *
                t ^ (varpi / 2 * (1 - e) - e)) * t ^ e := by
            rw [Real.mul_rpow (Real.rpow_nonneg hdR.le _) (Real.rpow_nonneg ht0.le _),
              ← Real.rpow_mul hdR.le, ← Real.rpow_mul ht0.le, mul_assoc, ← Real.rpow_add ht0]
            congr 2 <;> ring
          _ <= 1 * t ^ e := mul_le_mul_of_nonneg_right hcombine (Real.rpow_nonneg ht0.le _)
          _ = _ := one_mul _
      let cut : Real := G * (sourceTowerRadius delta M p : Real) * (sigma : Real)
      have hcut0 : 0 < cut := by dsimp [cut]; positivity
      have hcutb : (sourceTowerRadius delta M b : Real) < cut := by
        dsimp [x] at hslo'
        rw [div_div, div_le_iff₀ (by positivity)] at hslo'
        dsimp [cut]
        nlinarith only [hslo', mul_pos hrp0 hs0,
          mul_nonneg (sub_nonneg.mpr hG) (mul_nonneg hrp0.le hs0.le)]
      have hnext : cut <= (sourceTowerRadius delta M (a + 1) : Real) := by
        have hstep := (bridgeGrid_step hM hdR (show a < M by omega)).1
        rw [← hradEq, ← hradEq] at hstep
        have htlow : t <= t ^ (1 - e) := by
          simpa using Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (show 1 - e <= 1 by linarith)
        have hsmall : G * (sigma : Real) * t <= q * x :=
          (mul_le_mul_of_nonneg_left htlow (by positivity)).trans htest
        dsimp [t, x] at hsmall
        have hbound : cut <= q * (sourceTowerRadius delta M a : Real) := by
          dsimp [cut]
          apply (mul_le_mul_iff_of_pos_right (hrpos b)).mp
          rw [← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ hra0 hrp0] at hsmall
          nlinarith only [hsmall]
        exact hbound.trans hstep
      let candidates := (Finset.range (b + 1)).filter
        (fun k => cut <= (sourceTowerRadius delta M k : Real))
      have hmemnext : a + 1 ∈ candidates := Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hnext⟩
      have hne : candidates.Nonempty := ⟨a + 1, hmemnext⟩
      let k := candidates.max' hne
      have hkmem := candidates.max'_mem hne
      obtain ⟨hkb', hklo⟩ := Finset.mem_filter.mp hkmem
      change k ∈ Finset.range (b + 1) at hkb'
      change cut <= (sourceTowerRadius delta M k : Real) at hklo
      have hkb : k < b := by
        have hkle : k <= b := by have := Finset.mem_range.mp hkb'; omega
        have hne : k ≠ b := by intro h; rw [h] at hklo; exact (not_le.mpr hcutb) hklo
        omega
      have hak : a < k := by have := candidates.le_max' (a + 1) hmemnext; omega
      have hmax : (sourceTowerRadius delta M (k + 1) : Real) < cut := by
        by_contra h
        have hmem : k + 1 ∈ candidates := Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), le_of_not_gt h⟩
        have := candidates.le_max' (k + 1) hmem
        omega
      have hkupper : (sourceTowerRadius delta M k : Real) < cut / q := by
        rw [lt_div_iff₀ hq0]
        have hstep := (bridgeGrid_step hM hdR (show k < M by omega)).1
        rw [← hradEq, ← hradEq] at hstep
        exact (by simpa only [mul_comm] using hstep.trans_lt hmax)
      have hwindow : SourceTowerWindow delta M e a b k := by
        refine ⟨hak, hkb, ?_, ?_⟩
        · have hratio : t ^ (1 - e) <= (sourceTowerRadius delta M b : Real) / (cut / q) := by
            rw [le_div_iff₀ (div_pos hcut0 hq0), ← mul_div_assoc, div_le_iff₀ hq0]
            have ht : G * (sigma : Real) * t ^ (1 - e) *
                (sourceTowerRadius delta M p : Real) <= q * (sourceTowerRadius delta M b : Real) := by
              apply (le_div_iff₀ hrp0).mp
              simpa only [x, mul_div_assoc] using htest
            dsimp [cut]
            nlinarith only [ht]
          exact hratio.trans (div_le_div_of_nonneg_left (hrpos b).le (hrpos k) hkupper.le)
        · have hratio : (sourceTowerRadius delta M b : Real) / cut <= x / (56 * (sigma : Real)) := by
            dsimp [cut, x]
            rw [div_div]
            apply div_le_div_of_nonneg_left (hrpos b).le (by positivity)
            nlinarith only [mul_nonneg (sub_nonneg.mpr hG) (mul_nonneg hrp0.le hs0.le)]
          exact (div_le_div_of_nonneg_left (hrpos b).le hcut0 hklo).trans
            (hratio.trans ((bridgeGrid_window_upper hs0 hx0 hx1 (by linarith)
              (by linarith [hp.vns_window_upper]) le_rfl hslo).trans hxpow))
      exact ⟨k, hwindow, hi.parent_before_window k hwindow, hklo, hkupper⟩
    have hpullback {theta tau rho sigma : NNReal} {R : Real}
        (hsit : Tube.IsRescalingSituation theta tau rho R 3) (hR : 0 < R) (hR1 : 1 <= R)
        (T0 : Tube theta (EuclideanSpace Real (Fin 3)))
        (T : Tube tau (EuclideanSpace Real (Fin 3)))
        (V : Tube sigma (EuclideanSpace Real (Fin 3)))
        (hsigma : (sigma : Real) <= 1 / 4) (hsigma0 : 0 < sigma)
        (hT : T.carrier <= T0.carrier)
        (hcovered : T0.rescaleMap R '' T.carrier <= V.carrier) :
        T0.rescaleMap R ⁻¹' V.carrier <=
          lineNbhd T.center T.direction (1024 * R ^ 2 * (theta : Real) * (sigma : Real)) := by
      have hxy := rescaleMap_x_ne_rescaleMap_y hsit.pos_ambient T0 hR T
      let U : Tube sigma (EuclideanSpace Real (Fin 3)) := Tube.centredExtension sigma hxy
      have hlen := Tube.normalization_core_length hsit.pos_ambient hsit.ambient_le_one T0 T hT
      have hdim : Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3 := by simp
      have hlength : dist (T0.rescaleMap R T.x) (T0.rescaleMap R T.y) <= 1 := by
        rw [Tube.dist_rescaleMap T0 hR]
        apply (div_le_iff₀ (by positivity : 0 < 4 * R)).2
        rw [hdim] at hlen
        linarith [hsit.normalizationConst_le_radius]
      have hlengthLower : 2 / (5 * (2 * R)) <=
          dist (T0.rescaleMap R T.x) (T0.rescaleMap R T.y) := by
        rw [Tube.dist_rescaleMap T0 hR]
        apply (le_div_iff₀ (by positivity : 0 < 4 * R)).2
        have heq : 2 / (5 * (2 * R)) * (4 * R) = (4 / 5 : Real) := by
          field_simp
        rw [heq]
        linarith [hlen.1]
      have hxU : T0.rescaleMap R T.x ∈ U.carrier :=
        Tube.cthickening_subset_centredExtension hxy hlength
          (Metric.self_subset_cthickening _ (left_mem_segment Real _ _))
      have hyU : T0.rescaleMap R T.y ∈ U.carrier :=
        Tube.cthickening_subset_centredExtension hxy hlength
          (Metric.self_subset_cthickening _ (right_mem_segment Real _ _))
      have hxT : T.x ∈ T.carrier := by
        rw [T.carrier_eq_cthickening]
        exact Metric.self_subset_cthickening _ (left_mem_segment Real _ _)
      have hyT : T.y ∈ T.carrier := by
        rw [T.carrier_eq_cthickening]
        exact Metric.self_subset_cthickening _ (right_mem_segment Real _ _)
      have hVU : V.carrier <= (Kakeya.Tube.dilate U (32 * (2 * R))).carrier :=
        Tube.subset_dilate_of_common_chord_at (by linarith) (by linarith : 1 <= 2 * R)
          V U (hcovered (Set.mem_image_of_mem _ hxT)) (hcovered (Set.mem_image_of_mem _ hyT))
          hxU hyU hlengthLower
      let T' := T.rescale (theta * sigma)
      have hnew : Tube.IsRescalingSituation theta (theta * sigma) sigma R 3 := {
        pos_ambient := hsit.pos_ambient
        inner_le_ambient := by
          have hs : sigma <= 1 := by exact_mod_cast (show (sigma : Real) <= 1 by linarith)
          simpa using mul_le_mul_left' hs theta
        ambient_le_one := hsit.ambient_le_one
        pos_out := hsigma0
        out_le_quarter := hsigma
        out_le_ratio := by
          push_cast
          rw [mul_div_cancel_left₀ _ (by exact_mod_cast hsit.pos_ambient.ne')]
        normalizationConst_le_radius := hsit.normalizationConst_le_radius }
      have hperp : ‖T'.direction - (inner Real T0.direction T'.direction : Real) • T0.direction‖ <=
          2 * (theta : Real) := by
        exact Tube.perp_norm_direction_le_of_subset T0 T hT
      have hpre := Tube.preimage_rescale_dilate_subset_dilate hnew (by norm_num : (0 : Real) <= 2)
        (by nlinarith : 1 <= 32 * (2 * R)) T0 T' hperp hxy
      intro x hx
      have hxd := hpre (hVU hx)
      have hcpos : 0 < 4 * ((2 : Real) + 2) * R * (32 * (2 * R)) := by positivity
      have hdist := (Tube.abs_inner_and_perp_le_of_mem_dilate T' hcpos hxd).2
      have heq : T'.center = T.center := rfl
      have hdir : T'.direction = T.direction := rfl
      rw [heq, hdir] at hdist
      push_cast at hdist
      apply mem_lineNbhd_of_dist_le (inner Real T.direction (x - T.center))
      rw [dist_eq_norm, sub_add_eq_sub_sub]
      convert hdist using 1 <;> ring
    have hcharge {iota kappa : Type u} {delta rho sigma : NNReal} {M C A0 A1 a p b k : Nat}
        {S : Finset iota} {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))}
        (Q : SourceThreadedTower S T M C)
        (Y : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
        {jp : iota} {F E : Finset iota}
        (Z : iota -> ShadedTube (sourceTowerRadius delta M b) (EuclideanSpace Real (Fin 3)))
        {e zeta etaC G R : Real}
        (hi : SourceQCoverInput Q a p b jp F Z rho e zeta etaC)
        (hgeom : SourceTowerGeometry Q A0 A1) (hstats : SourceTowerStatistics Q Y)
        (hE : E.Nonempty) (hEF : E <= F)
        (hsit : Tube.IsRescalingSituation (sourceTowerRadius delta M p)
          (sourceTowerRadius delta M b) rho R 3) (hR : 0 < R)
        (W : Finset kappa) (V : kappa -> Tube sigma (EuclideanSpace Real (Fin 3)))
        (hcovered : SourceQImageCovered hsit hR (Q.tube p jp) E Z W V)
        (hk : SourceTowerWindow delta M e a b k) (hpk : p < k)
        (hlo : G * (sourceTowerRadius delta M p : Real) * (sigma : Real) <=
          (sourceTowerRadius delta M k : Real))
        (hhi : (sourceTowerRadius delta M k : Real) <
          G * (sourceTowerRadius delta M p : Real) * (sigma : Real) /
            (delta : Real) ^ (1 / (M : Real)))
        (hG0 : 0 <= G)
        (hpre : forall i, i ∈ E -> forall w, w ∈ W ->
          (Q.tube p jp).rescaleMap R '' (Q.tube b i).carrier <= (V w).carrier ->
          (Q.tube p jp).rescaleMap R ⁻¹' (V w).carrier <=
            lineNbhd (Q.tube b i).center (Q.tube b i).direction
              (G * (sourceTowerRadius delta M p : Real) * (sigma : Real))) :
        exists B : SourceQCoverCharge Q a p b jp E e G W V,
          (forall j, j ∈ E.image (sourceQAncestor Q B.level b) ->
            (spineFamily (spineRescaleUnit hsit.pos_ambient (Q.tube p jp) hR)
              Z (B.child j)).toConvexSpaceBody <= (V (B.charge j)).toConvexSpaceBody) /\
          (forall w, w ∈ W ->
            ((E.image (sourceQAncestor Q B.level b)).filter (fun j => B.charge j = w)).card <= A1) := by
      classical
      have hkb := hk.2.1
      have hbM := hi.middle_bound
      have hkM : k <= M := hkb.le.trans hbM
      have hpb := hi.parent_lt_middle
      have hpkid := sourceQ_ancestor_fibre_identities Q hpk.le hkM
      have hkbid := sourceQ_ancestor_fibre_identities Q hkb.le hbM
      have hpbid := sourceQ_ancestor_fibre_identities Q hpb.le hbM
      have hTmindex {j : iota} (hj : j ∈ Q.fibre p k jp) : j ∈ Q.indexSet k := by
        rw [hpkid.2.2.2 jp hi.parent_member] at hj
        exact (Finset.mem_filter.mp hj).1
      have hTbindex {i : iota} (hi' : i ∈ Q.fibre p b jp) : i ∈ Q.indexSet b := by
        rw [hpbid.2.2.2 jp hi.parent_member] at hi'
        exact (Finset.mem_filter.mp hi').1
      have hcomp {i : iota} (hi' : i ∈ Q.indexSet b) :
          sourceQAncestor Q p k (sourceQAncestor Q k b i) = sourceQAncestor Q p b i := by
        obtain ⟨l, hl, rfl⟩ := Q.place_surjective b hbM i hi'
        rw [hkbid.1 l hl, hpkid.1 l hl, hpbid.1 l hl]
      have hfibre {j : iota} (hj : j ∈ Q.fibre p k jp) :
          (Q.fibre p b jp).filter (fun i => sourceQAncestor Q k b i = j) = Q.fibre k b j := by
        have hjk := hTmindex hj
        have hjp : sourceQAncestor Q p k j = jp := by
          rw [hpkid.2.2.2 jp hi.parent_member] at hj
          exact (Finset.mem_filter.mp hj).2
        rw [hpbid.2.2.2 jp hi.parent_member, hkbid.2.2.2 j hjk]
        ext i
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hib, _⟩, hij⟩
          exact ⟨hib, hij⟩
        · rintro ⟨hib, hij⟩
          refine ⟨⟨hib, ?_⟩, hij⟩
          rw [← hcomp hib, hij, hjp]
      have hTmne : (Q.fibre p k jp).Nonempty := by
        obtain ⟨l, hl, hlp⟩ := Q.place_surjective p (hpb.le.trans hbM) jp hi.parent_member
        exact ⟨Q.place k l, Finset.mem_image.mpr
          ⟨l, Finset.mem_filter.mpr ⟨hl, hlp⟩, rfl⟩⟩
      let counts := (Q.fibre p k jp).image (fun j => (Q.fibre k b j).card)
      have hcounts : counts.Nonempty := hTmne.image _
      let D := counts.min' hcounts
      obtain ⟨jmin, hjmin, hD⟩ := Finset.mem_image.mp (counts.min'_mem hcounts)
      change (Q.fibre k b jmin).card = D at hD
      have hDpos : 0 < D := by
        rw [← hD]
        apply Finset.card_pos.mpr
        obtain ⟨l, hl, hlk⟩ := Q.place_surjective k hkM jmin (hTmindex hjmin)
        exact ⟨Q.place b l, Finset.mem_image.mpr
          ⟨l, Finset.mem_filter.mpr ⟨hl, hlk⟩, rfl⟩⟩
      have hDlo {j : iota} (hj : j ∈ Q.fibre p k jp) : D <=
          ((Q.fibre p b jp).filter (fun i => sourceQAncestor Q k b i = j)).card := by
        rw [hfibre hj]
        exact counts.min'_le _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
      have hDhi {j : iota} (hj : j ∈ Q.fibre p k jp) :
          ((Q.fibre p b jp).filter (fun i => sourceQAncestor Q k b i = j)).card <= 2 * D := by
        rw [hfibre hj, ← hD]
        have hh := hstats.two_level_count k b hkb hbM j (hTmindex hj) jmin (hTmindex hjmin)
        exact_mod_cast hh
      obtain ⟨i0, hi0⟩ := hE
      obtain ⟨w0, hw0, hcov0⟩ := hcovered i0 hi0
      let cover : iota -> kappa := fun i => if h : i ∈ E then (hcovered i h).choose else w0
      have hcover (i : iota) (hei : i ∈ E) : cover i ∈ W /\
          (spineFamily (spineRescaleUnit hsit.pos_ambient (Q.tube p jp) hR) Z i).toConvexSpaceBody <=
            (V (cover i)).toConvexSpaceBody := by
        simp only [cover, dif_pos hei]
        exact (hcovered i hei).choose_spec
      have hcoverBody (i : iota) (hei : i ∈ E) :
          (Q.tube p jp).rescaleMap R '' (Q.tube b i).carrier <= (V (cover i)).carrier := by
        have hh := (hcover i hei).2
        change (spineRescaleUnit hsit.pos_ambient (Q.tube p jp) hR) '' (Z i).carrier <=
          (V (cover i)).carrier at hh
        rw [spineRescaleUnit_coe] at hh
        rw [show (Z i).carrier = (Q.tube b i).carrier from
          congrArg (fun U : Tube (sourceTowerRadius delta M b) (EuclideanSpace Real (Fin 3)) =>
            U.carrier) (hi.family_tubes i)] at hh
        exact hh
      let anc := E.image (sourceQAncestor Q k b)
      let child : iota -> iota := fun j => if h : j ∈ anc then
        (Finset.mem_image.mp h).choose else i0
      have hchild (j : iota) (hj : j ∈ anc) : child j ∈ E /\ sourceQAncestor Q k b (child j) = j := by
        simp only [child, dif_pos hj]
        exact (Finset.mem_image.mp hj).choose_spec
      let charge : iota -> kappa := fun j => cover (child j)
      let reference : kappa -> iota := fun w => if h : exists i, i ∈ E /\ cover i = w then
        h.choose else i0
      have href {w : kappa} (hw : exists i, i ∈ E /\ cover i = w) :
          reference w ∈ E /\ cover (reference w) = w := by
        simp only [reference, dif_pos hw]
        exact hw.choose_spec
      have hancindex (j : iota) (hj : j ∈ anc) : j ∈ Q.indexSet k := by
        rw [← (hchild j hj).2]
        exact hkbid.2.1 _ (hTbindex (hi.family_subset (hEF (hchild j hj).1)))
      have hplacement (j : iota) (hj : j ∈ anc) :
          (Q.tube k j).carrier <=
            lineNbhd (Q.tube b (reference (charge j))).center
              (Q.tube b (reference (charge j))).direction (5 * (sourceTowerRadius delta M k : Real)) := by
        have hc := hchild j hj
        have hw := (hcover (child j) hc.1).1
        have hreff := href ⟨child j, hc.1, rfl⟩
        have hrefcov := hcoverBody _ hreff.1
        rw [hreff.2] at hrefcov
        have hpull := hpre _ hreff.1 _ hw hrefcov
        have hcore : segment Real (Q.tube b (child j)).x (Q.tube b (child j)).y <=
            lineNbhd (Q.tube b (reference (charge j))).center
              (Q.tube b (reference (charge j))).direction
                (G * (sourceTowerRadius delta M p : Real) * (sigma : Real)) := by
          intro x hx
          apply hpull
          apply hcoverBody _ hc.1
          refine ⟨x, ?_, rfl⟩
          rw [(Q.tube b (child j)).carrier_eq_cthickening]
          exact Metric.self_subset_cthickening _ hx
        have hsub : (Q.tube b (child j)).carrier <= (Q.tube k j).carrier := by
          have hh := hkbid.2.2.1 _ (hTbindex (hi.family_subset (hEF hc.1)))
          rw [hc.2] at hh
          exact hh
        have hreverse := Tube.le_rescale_of_subset (Q.tube b (child j)) (Q.tube k j) hsub
        intro x hx
        have hh := hreverse hx
        change x ∈ ((Q.tube b (child j)).rescale (4 * sourceTowerRadius delta M k)).carrier at hh
        rw [Tube.carrier_eq_cthickening] at hh
        change x ∈ Metric.cthickening (4 * (sourceTowerRadius delta M k : Real))
          (segment Real (Q.tube b (child j)).x (Q.tube b (child j)).y) at hh
        have hth := Metric.cthickening_subset_of_subset (4 * (sourceTowerRadius delta M k : Real)) hcore hh
        have hadd := Metric.cthickening_cthickening_subset
          (show 0 <= 4 * (sourceTowerRadius delta M k : Real) by positivity)
          (show 0 <= G * (sourceTowerRadius delta M p : Real) * (sigma : Real) by positivity)
          (lineSet (Q.tube b (reference (charge j))).center
            (Q.tube b (reference (charge j))).direction) hth
        exact Metric.cthickening_mono (by linarith only [hlo]) _ hadd
      let B : SourceQCoverCharge Q a p b jp E e G W V := {
        level := k
        descendants := D
        charge := charge
        child := child
        linePoint := fun w => (Q.tube b (reference w)).center
        lineDirection := fun w => (Q.tube b (reference w)).direction
        level_window := hk
        parent_before := hpk
        descendants_pos := hDpos
        descendant_lower := fun j hj => hDlo hj
        descendant_upper := fun j hj => hDhi hj
        grid_lower := hlo
        grid_upper := hhi
        child_member := fun j hj => (hchild j hj).1
        child_ancestor := fun j hj => (hchild j hj).2
        charge_member := fun j hj => (hcover _ (hchild j hj).1).1
        direction_unit := fun w _ => (Q.tube b (reference w)).norm_direction
        ancestor_placement := hplacement }
      refine ⟨B, ?_, ?_⟩
      · intro j hj
        exact (hcover _ (hchild j hj).1).2
      · intro w hw
        have hed := hgeom.coarse_ed k (hkb.trans_le hbM)
          (B.linePoint w) (B.lineDirection w) (B.direction_unit w hw)
        apply (Finset.card_le_card ?_).trans hed
        intro j hj
        obtain ⟨hj, hjw⟩ := Finset.mem_filter.mp hj
        refine Finset.mem_filter.mpr ⟨hancindex j hj, ?_⟩
        have hh := B.ancestor_placement j hj
        rw [hjw] at hh
        exact hh
    have hcount (M A0 A1 C : Nat) (e varpi zeta etaC R G : Real)
        (hp : SourceQCoverParameters M A0 A1 C e varpi zeta etaC R) (hG : 56 <= G) :
        ∀ᶠ delta : NNReal in 𝓝[>] 0,
          forall {iota kappa : Type u} (S : Finset iota)
            (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
            (Q : SourceThreadedTower S T M C)
            (a p b : Nat) (jp : iota) (F E : Finset iota)
            (Z : iota -> ShadedTube (sourceTowerRadius delta M b) (EuclideanSpace Real (Fin 3)))
            (rho sigma : NNReal),
            SourceQCoverInput Q a p b jp F Z rho e zeta etaC ->
            E <= F -> (rho : Real) ^ (varpi * zeta / 16) * (F.card : Real) <= (E.card : Real) ->
            sigma ∈ Set.Icc (rho ^ (1 - varpi / 2)) (rho ^ (varpi / 2)) ->
            forall (W : Finset kappa) (V : kappa -> Tube sigma (EuclideanSpace Real (Fin 3)))
              (B : SourceQCoverCharge Q a p b jp E e G W V),
            (forall w, w ∈ W ->
              ((E.image (sourceQAncestor Q B.level b)).filter (fun j => B.charge j = w)).card <= A1) ->
            (rho : Real) ^ (varpi * zeta / 16) * (sigma : Real) ^ (-2 - 2 * zeta) <=
              (W.card : Real) := by
      classical
      have hG0 : 0 < G := by linarith
      have hA10 : (0 : Real) < A1 := by exact_mod_cast hp.level_ed
      have hcost : 0 < e * varpi * zeta / 2 - (6 * etaC + 3 / (M : Real)) := by
        nlinarith [hp.count_margin, mul_pos (mul_pos hp.window_pos hp.vns_window_pos) hp.excess_pos]
      obtain ⟨d0, hd0, hd01, hconst⟩ := ML2Shaded.exists_threshold_const_le_rpow_neg'
        (2 * (A1 : Real) * G ^ (3 : Nat)) hcost
      filter_upwards [Ioo_mem_nhdsGT hd0] with delta hd
      intro iota kappa S T Q a p b jp F E Z rho sigma hi hEF hretain hsigma W V B hcharged
      have hdR : (0 : Real) < delta := by exact_mod_cast hd.1
      have hd1 : (delta : Real) <= 1 := by exact_mod_cast hd.2.le.trans hd01
      have hM : (0 : Real) < M := by exact_mod_cast (show 0 < M by have := hp.levels; omega)
      have hrho0 : (0 : Real) < rho := by
        have hh : 20 * (delta : Real) <= rho := by exact_mod_cast hi.rho_lower
        linarith
      have hs0 : (0 : Real) < sigma := by
        have hh : (rho : Real) ^ (1 - varpi / 2) <= sigma := by exact_mod_cast hsigma.1
        exact (Real.rpow_pos_of_pos hrho0 _).trans_le hh
      let q : Real := (delta : Real) ^ (1 / (M : Real))
      let q' : Real := 56 * q / G
      have hq0 : 0 < q := Real.rpow_pos_of_pos hdR _
      have hq1 : q <= 1 := Real.rpow_le_one hdR.le hd1 (by positivity)
      have hq'0 : 0 < q' := by dsimp [q']; positivity
      have hq'1 : q' <= 1 := by dsimp [q']; rw [div_le_one hG0]; nlinarith only [hq1, hG]
      have hsupper : (sigma : Real) <= (delta : Real) ^ (e * varpi / 4) := by
        have hs := (show (sigma : Real) <= (rho : Real) ^ (varpi / 2) by exact_mod_cast hsigma.2)
        have hr : (rho : Real) <= (delta : Real) ^ (e / 2) := by
          have hh := hi.rho_upper
          have hz := Real.rpow_pos_of_pos hdR (e / 2)
          linarith
        calc (sigma : Real) <= (rho : Real) ^ (varpi / 2) := hs
          _ <= ((delta : Real) ^ (e / 2)) ^ (varpi / 2) :=
            Real.rpow_le_rpow hrho0.le hr (by linarith [hp.vns_window_pos])
          _ = _ := by rw [← Real.rpow_mul hdR.le]; congr 1 <;> ring
      have hsPower : (sigma : Real) ^ (2 * zeta) <= (delta : Real) ^ (e * varpi * zeta / 2) := by
        calc (sigma : Real) ^ (2 * zeta) <= ((delta : Real) ^ (e * varpi / 4)) ^ (2 * zeta) :=
              Real.rpow_le_rpow hs0.le hsupper (by linarith [hp.excess_pos])
          _ = _ := by rw [← Real.rpow_mul hdR.le]; congr 1 <;> ring
      have hpayment : (sigma : Real) ^ (2 * zeta) <=
          (delta : Real) ^ (6 * etaC + 3 / (M : Real)) / (2 * (A1 : Real) * G ^ (3 : Nat)) := by
        rw [le_div_iff₀ (by positivity)]
        calc (sigma : Real) ^ (2 * zeta) * (2 * (A1 : Real) * G ^ (3 : Nat)) <=
              (delta : Real) ^ (e * varpi * zeta / 2) *
                (delta : Real) ^ (-(e * varpi * zeta / 2 - (6 * etaC + 3 / (M : Real)))) :=
              mul_le_mul hsPower (hconst hd.1 hd.2.le) (by positivity) (Real.rpow_nonneg hdR.le _)
          _ = _ := by rw [← Real.rpow_add hdR]; congr 1 <;> ring
      have hqpow : q ^ (3 : Real) = (delta : Real) ^ (3 / (M : Real)) := by
        dsimp [q]
        rw [← Real.rpow_mul hdR.le]
        congr 1
        ring
      have htest : (sigma : Real) ^ (2 * zeta) <=
          (delta : Real) ^ (6 * etaC) * q' ^ (3 : Real) /
            (bridgeScaleTestConstant 1 * 1 * (A1 : Real)) := by
        apply hpayment.trans_eq
        rw [Real.rpow_add hdR, ← hqpow]
        dsimp [q', bridgeScaleTestConstant]
        rw [show (3 : Real) = ((3 : Nat) : Real) by norm_num]
        simp only [Real.rpow_natCast]
        rw [div_pow]
        field_simp
        <;> ring
      have hradpos (k : Nat) : (0 : Real) < sourceTowerRadius delta M k := by
        simp only [sourceTowerRadius]
        split <;> push_cast <;> positivity
      have hgrid : q' / (56 * (sigma : Real)) <=
          (sourceTowerRadius delta M p : Real) / (sourceTowerRadius delta M B.level : Real) := by
        have hrp := hradpos p
        have hrk := hradpos B.level
        have hh := B.grid_upper
        change (sourceTowerRadius delta M B.level : Real) <
          G * (sourceTowerRadius delta M p : Real) * (sigma : Real) / q at hh
        rw [lt_div_iff₀ hq0] at hh
        have heq : q' / (56 * (sigma : Real)) = q / (G * (sigma : Real)) := by
          dsimp [q']
          field_simp
        rw [heq, div_le_div_iff₀ (by positivity) hrk]
        nlinarith only [hh]
      have hancmaps (i : iota) (hii : i ∈ Q.fibre p b jp) :
          sourceQAncestor Q B.level b i ∈ Q.fibre p B.level jp := by
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hii
        have hlS := (Finset.mem_filter.mp hl).1
        rw [(sourceQ_ancestor_fibre_identities Q B.level_window.2.1.le hi.middle_bound).1 l hlS]
        exact Finset.mem_image.mpr ⟨l, hl, rfl⟩
      have hfilter : F.filter (fun i => id i ∈ E) = E := by
        ext i
        simp only [Finset.mem_filter, id_eq]
        exact ⟨fun h => h.2, fun h => ⟨hEF h, h⟩⟩
      apply defectCoveringBridge' (F := 1) (C := bridgeScaleTestConstant 1)
        (Q.fibre p b jp) F F E id (Q.fibre p B.level jp)
        (sourceQAncestor Q B.level b) W B.charge 1 A1 B.descendants
        hi.family_subset hi.same_parent_retention (fun _ h => h) (fun i h => ⟨i, h, rfl⟩)
        (fun i _ => ?_) (by norm_num) (by norm_num) le_rfl hEF hretain
        hancmaps B.descendant_lower B.descendant_upper
        (by simpa only [hfilter] using B.charge_member)
        (by simpa only [hfilter] using hcharged)
        (hi.count_floor B.level B.level_window) hgrid htest B.descendants_pos (by norm_num)
        (by have := hp.level_ed; omega)
        (Real.rpow_pos_of_pos hrho0 _) (Real.rpow_pos_of_pos hdR _)
        hs0 hp.excess_pos hp.excess_upper hq'0 hq'1 (by norm_num)
      apply Finset.card_le_one.mpr
      intro x hx y hy
      exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    let G : Real := 1024 * R ^ (2 : Nat)
    have hR1 : 1 <= R := by linarith only [hp.radius_lower]
    have hG : 56 <= G := by dsimp [G]; nlinarith only [hp.radius_lower]
    have hsmall := hgrid M A0 A1 C e varpi zeta etaC R G hp hG
    have hsmallCount := hcount M A0 A1 C e varpi zeta etaC R G hp hG
    have hexp : 0 < e * varpi / 4 := by have := hp.window_pos; have := hp.vns_window_pos; positivity
    obtain ⟨d0, hd0, hd01, hquarter⟩ := ML2Shaded.exists_threshold_const_le_rpow_neg' 4 hexp
    refine ⟨G, hG, ?_⟩
    filter_upwards [hsmall, hsmallCount, Ioo_mem_nhdsGT hd0] with delta hgridDelta hcountDelta hd
    intro iota S T Q Y hgeom hstats a p b jp F E Z rho hi hEF hretain hsit hR sigma hsigma
      kappa W V hcovered
    have hdR : (0 : Real) < delta := by exact_mod_cast hd.1
    have hrho0 : (0 : Real) < rho := by
      have hh : 20 * (delta : Real) <= rho := by exact_mod_cast hi.rho_lower
      linarith only [hh, hdR]
    have hsigma0 : 0 < sigma := by
      have hh : (rho : Real) ^ (1 - varpi / 2) <= sigma := by exact_mod_cast hsigma.1
      exact_mod_cast (Real.rpow_pos_of_pos hrho0 _).trans_le hh
    have hsigmaQuarter : (sigma : Real) <= 1 / 4 := by
      have hs := (show (sigma : Real) <= (rho : Real) ^ (varpi / 2) by exact_mod_cast hsigma.2)
      have hr : (rho : Real) <= (delta : Real) ^ (e / 2) := by
        have hh := hi.rho_upper
        have hz := Real.rpow_pos_of_pos hdR (e / 2)
        linarith only [hh, hz]
      have hpow : (delta : Real) ^ (e * varpi / 4) <= 1 / 4 := by
        have hc := hquarter hd.1 hd.2.le
        rw [Real.rpow_neg hdR.le, ← one_div] at hc
        have hm := (le_div_iff₀ (Real.rpow_pos_of_pos hdR (e * varpi / 4))).mp hc
        linarith only [hm]
      calc (sigma : Real) <= (rho : Real) ^ (varpi / 2) := hs
        _ <= ((delta : Real) ^ (e / 2)) ^ (varpi / 2) :=
          Real.rpow_le_rpow hrho0.le hr (by linarith only [hp.vns_window_pos])
        _ = (delta : Real) ^ (e * varpi / 4) := by
          rw [← Real.rpow_mul hdR.le]
          congr 1
          ring
        _ <= 1 / 4 := hpow
    have hE : E.Nonempty := by
      have hFpos : (0 : Real) < F.card := by exact_mod_cast Finset.card_pos.mpr hi.family_nonempty
      have hh := (mul_pos (Real.rpow_pos_of_pos hrho0 (varpi * zeta / 16)) hFpos).trans_le hretain
      exact Finset.card_pos.mp (by exact_mod_cast hh)
    have hsub (i : iota) (hei : i ∈ E) : (Q.tube b i).carrier <= (Q.tube p jp).carrier := by
      have hids := sourceQ_ancestor_fibre_identities Q hi.parent_lt_middle.le hi.middle_bound
      have hii := hi.family_subset (hEF hei)
      rw [hids.2.2.2 jp hi.parent_member] at hii
      obtain ⟨hib, hip⟩ := Finset.mem_filter.mp hii
      have hh := hids.2.2.1 i hib
      rw [hip] at hh
      exact hh
    obtain ⟨k, hk, hpk, hlo, hhi⟩ := hgridDelta S T Q a p b jp F Z rho sigma hi hsigma
    obtain ⟨B, hcov, hcharged⟩ := hcharge Q Y Z hi hgeom hstats hE hEF hsit hR W V hcovered
      hk hpk hlo hhi (by linarith only [hG] : 0 <= G) (fun i hei w _ himage =>
        hpullback hsit hR hR1 (Q.tube p jp) (Q.tube b i) (V w)
          hsigmaQuarter hsigma0 (hsub i hei) himage)
    exact ⟨B, hcov, hcharged,
      hcountDelta S T Q a p b jp F E Z rho sigma hi hEF hretain hsigma W V B hcharged⟩)

/-- The precise antecedent of the already proved CountTransport, at every radius.
The body spells out the affine images, radius contraction, ED and count constant. -/
def SourceMiddleDownstairsCount {b tau rho : NNReal} {R : Real}
    (hsit : Tube.IsRescalingSituation b tau rho R 3) (hR : 0 < R)
    (T0 : Tube b (EuclideanSpace Real (Fin 3))) (varpi zeta : Real)
    (E : Finset iota) (Z : iota -> ShadedTube tau (EuclideanSpace Real (Fin 3))) : Prop :=
  forall sigma : NNReal, sigma ∈ Set.Icc (rho ^ (1 - varpi)) (rho ^ varpi) ->
    exists (kappa : Type u) (W : Finset kappa)
      (V : kappa -> Tube (sigma / centringCoverRadiusConstant) (EuclideanSpace Real (Fin 3))),
      ((W : Set kappa).Pairwise
        (fun j k => _root_.IsEssentiallyDistinct (V j).carrier (V k).carrier)) /\
      (forall j, j ∈ W -> exists i, i ∈ E /\
        (spineFamily (spineRescaleUnit hsit.pos_ambient T0 hR) Z i).toConvexSpaceBody <=
          (V j).toConvexSpaceBody) /\
      (centringCountLossConstant R : Real) *
        ((sigma / centringCoverRadiusConstant : NNReal) : Real) ^ (-2 - zeta) <= (W.card : Real)

/-- S:4597-4655, on the retained indices themselves. An actual maximal ED
extraction and its enlarged covering family pay their fixed constants on a
smaller threshold. The original zeta floor is never changed to 3*zeta/2. -/
theorem sourceQ_exists_downstairs_count (M A0 A1 C : Nat)
    (e varpi zeta etaC R : Real)
    (hp : SourceQCoverParameters M A0 A1 C e varpi zeta etaC R) :
    ∀ᶠ delta : NNReal in 𝓝[>] 0,
      forall {iota : Type u} (S : Finset iota)
        (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
        (Q : SourceThreadedTower S T M C)
        (Y : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
      SourceTowerGeometry Q A0 A1 -> SourceTowerStatistics Q Y ->
      forall (a p b : Nat) (jp : iota) (F E : Finset iota)
        (Z : iota -> ShadedTube (sourceTowerRadius delta M b) (EuclideanSpace Real (Fin 3)))
        (rho : NNReal), SourceQCoverInput Q a p b jp F Z rho e zeta etaC ->
      E <= F -> (rho : Real) ^ (varpi * zeta / 16) * (F.card : Real) <= (E.card : Real) ->
      forall (hsit : Tube.IsRescalingSituation (sourceTowerRadius delta M p)
          (sourceTowerRadius delta M b) rho R 3) (hR : 0 < R),
        SourceQNormalizedRows hsit hR (Q.tube p jp) F Z /\
        SourceMiddleDownstairsCount hsit hR (Q.tube p jp) varpi zeta E Z := by
  classical
  have hradii (varpi zeta D L : Real) (hv : 0 < varpi) (hv1 : varpi < 1 / 2)
      (hz : 0 < zeta) (hD : 1 <= D) (hL : 0 <= L) :
      ∀ᶠ rho : NNReal in 𝓝[>] 0,
        forall sigma : NNReal, sigma ∈ Set.Icc (rho ^ (1 - varpi)) (rho ^ varpi) ->
          rho <= sigma / centringCoverRadiusConstant /\
          sigma / centringCoverRadiusConstant <= 1 /\
          Real.toNNReal D * sigma ∈
            Set.Icc (rho ^ (1 - varpi / 2)) (rho ^ (varpi / 2)) /\
          L * ((sigma / centringCoverRadiusConstant : NNReal) : Real) ^ (-2 - zeta) <=
            (rho : Real) ^ (varpi * zeta / 16) *
              ((Real.toNNReal D * sigma : NNReal) : Real) ^ (-2 - 2 * zeta) := by
    have hD0 : 0 < D := zero_lt_one.trans_le hD
    let C : Real := L * (2 : Real) ^ (2 + zeta) * D ^ (2 + 2 * zeta)
    have hC0 : 0 <= C := by dsimp [C]; positivity
    obtain ⟨d1, hd1, hd11, hconstD⟩ :=
      ML2Shaded.exists_threshold_const_le_rpow_neg' D (by linarith : 0 < varpi / 2)
    obtain ⟨d2, hd2, hd21, hconst2⟩ :=
      ML2Shaded.exists_threshold_const_le_rpow_neg' 2 hv
    obtain ⟨d3, hd3, hd31, hconstC⟩ :=
      ML2Shaded.exists_threshold_const_le_rpow_neg' C (by positivity : 0 < 15 * varpi * zeta / 16)
    filter_upwards [Ioo_mem_nhdsGT hd1, Ioo_mem_nhdsGT hd2, Ioo_mem_nhdsGT hd3]
      with rho hr1 hr2 hr3
    intro sigma hs
    have hr0 : (0 : Real) < rho := by exact_mod_cast hr1.1
    have hrle1 : (rho : Real) <= 1 := by exact_mod_cast hr1.2.le.trans hd11
    have hslo : (rho : Real) ^ (1 - varpi) <= sigma := by exact_mod_cast hs.1
    have hshi : (sigma : Real) <= (rho : Real) ^ varpi := by exact_mod_cast hs.2
    have hs0 : (0 : Real) < sigma := (Real.rpow_pos_of_pos hr0 _).trans_le hslo
    have hs1 : (sigma : Real) <= 1 := hshi.trans (Real.rpow_le_one hr0.le hrle1 hv.le)
    have htwo : 2 * (rho : Real) <= (sigma : Real) := by
      calc 2 * (rho : Real) <= (rho : Real) ^ (-varpi) * (rho : Real) :=
            mul_le_mul_of_nonneg_right (hconst2 hr2.1 hr2.2.le) hr0.le
        _ = (rho : Real) ^ (1 - varpi) := by
          calc _ = (rho : Real) ^ (-varpi) * (rho : Real) ^ (1 : Real) := by rw [Real.rpow_one]
            _ = _ := by
              rw [← Real.rpow_add hr0]
              congr 1
              ring
        _ <= sigma := hslo
    have hwideLo : (rho : Real) ^ (1 - varpi / 2) <= D * (sigma : Real) := by
      calc (rho : Real) ^ (1 - varpi / 2) <= (rho : Real) ^ (1 - varpi) :=
            Real.rpow_le_rpow_of_exponent_ge hr0 hrle1 (by linarith only [hv])
        _ <= sigma := hslo
        _ <= D * (sigma : Real) := by nlinarith only [mul_nonneg (sub_nonneg.mpr hD) hs0.le]
    have hwideHi : D * (sigma : Real) <= (rho : Real) ^ (varpi / 2) := by
      calc D * (sigma : Real) <= (rho : Real) ^ (- (varpi / 2)) * (rho : Real) ^ varpi :=
            mul_le_mul (hconstD hr1.1 hr1.2.le) hshi hs0.le
              (Real.rpow_nonneg hr0.le _)
        _ = (rho : Real) ^ (varpi / 2) := by
          rw [← Real.rpow_add hr0]
          congr 1
          ring
    have hpay : C * (sigma : Real) ^ zeta <= (rho : Real) ^ (varpi * zeta / 16) := by
      calc C * (sigma : Real) ^ zeta <=
            (rho : Real) ^ (-(15 * varpi * zeta / 16)) *
              ((rho : Real) ^ varpi) ^ zeta :=
            mul_le_mul (hconstC hr3.1 hr3.2.le)
              (Real.rpow_le_rpow hs0.le hshi hz.le)
              (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg hr0.le _)
        _ = (rho : Real) ^ (varpi * zeta / 16) := by
          rw [← Real.rpow_mul hr0.le, ← Real.rpow_add hr0]
          congr 1
          ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · change rho <= sigma / 2
      exact_mod_cast (by linarith only [htwo] : (rho : Real) <= (sigma : Real) / 2)
    · change sigma / 2 <= 1
      exact_mod_cast (by linarith only [hs1] : (sigma : Real) / 2 <= 1)
    · constructor
      · apply NNReal.coe_le_coe.mp
        simpa only [NNReal.coe_rpow, NNReal.coe_mul, Real.coe_toNNReal D hD0.le] using hwideLo
      · apply NNReal.coe_le_coe.mp
        simpa only [NNReal.coe_rpow, NNReal.coe_mul, Real.coe_toNNReal D hD0.le] using hwideHi
    · change L * ((sigma : Real) / 2) ^ (-2 - zeta) <=
        (rho : Real) ^ (varpi * zeta / 16) *
          ((Real.toNNReal D : Real) * (sigma : Real)) ^ (-2 - 2 * zeta)
      rw [Real.coe_toNNReal D hD0.le]
      apply (mul_le_mul_iff_left₀
        (Real.rpow_pos_of_pos (mul_pos hD0 hs0) (2 + 2 * zeta))).mp
      have hleft : (L * ((sigma : Real) / 2) ^ (-2 - zeta)) *
          (D * (sigma : Real)) ^ (2 + 2 * zeta) = C * (sigma : Real) ^ zeta := by
        rw [Real.div_rpow hs0.le (by norm_num), Real.mul_rpow hD0.le hs0.le,
          div_eq_mul_inv]
        have htwoPow : ((2 : Real) ^ (-2 - zeta))⁻¹ = (2 : Real) ^ (2 + zeta) := by
          rw [← Real.rpow_neg (by norm_num : (0 : Real) <= 2)]
          congr 1
          ring
        rw [htwoPow]
        calc _ = C * ((sigma : Real) ^ (-2 - zeta) * (sigma : Real) ^ (2 + 2 * zeta)) := by
              dsimp [C]
              ring
          _ = _ := by
            rw [← Real.rpow_add hs0]
            congr 2
            ring
      have hright : ((rho : Real) ^ (varpi * zeta / 16) *
          (D * (sigma : Real)) ^ (-2 - 2 * zeta)) *
          (D * (sigma : Real)) ^ (2 + 2 * zeta) = (rho : Real) ^ (varpi * zeta / 16) := by
        rw [mul_assoc, ← Real.rpow_add (mul_pos hD0 hs0)]
        have he : (-2 - 2 * zeta) + (2 + 2 * zeta) = (0 : Real) := by ring
        rw [he, Real.rpow_zero, mul_one]
      rw [hleft, hright]
      exact hpay
  have hunit {sigma : NNReal} (T : Tube sigma (EuclideanSpace Real (Fin 3)))
      (D : Real) (hD : 0 < D) :
      exists V : Tube (Real.toNNReal D * sigma) (EuclideanSpace Real (Fin 3)),
        (Tube.dilate T D).carrier ∩ Metric.closedBall 0 (1 / 4 : Real) <= V.carrier := by
    let f := Tube.lineFoot T.center T.direction
    let V := Tube.ofMidpointDirection (Real.toNNReal D * sigma) f T.direction T.norm_direction
    refine ⟨V, ?_⟩
    intro z hz
    have hperp := (Tube.abs_inner_and_perp_le_of_mem_dilate T hD hz.1).2
    have hzNorm : norm z <= 1 / 4 := by simpa using Metric.mem_closedBall.mp hz.2
    let t : Real := inner Real z T.direction
    have ht : |t| <= 1 / 2 := by
      have hh := abs_real_inner_le_norm z T.direction
      rw [T.norm_direction, mul_one] at hh
      exact hh.trans (by linarith only [hzNorm])
    have hmid : V.midpoint = f := Tube.midpoint_ofMidpointDirection' _ _ _
    have hdir : V.direction = T.direction := Tube.direction_ofMidpointDirection' _ _ _
    apply V.mem_carrier_of_dist_le (V.midpoint_add_smul_mem_segment ht)
    rw [hmid, hdir, dist_eq_norm]
    have heq : z - (f + t • T.direction) =
        z - T.center - inner Real T.direction (z - T.center) • T.direction := by
      change z - (T.center - inner Real T.center T.direction • T.direction +
        inner Real z T.direction • T.direction) = _
      rw [real_inner_comm (z - T.center) T.direction, inner_sub_left]
      module
    rw [heq]
    simpa only [NNReal.coe_mul, Real.coe_toNNReal D hD.le] using hperp
  have hedcover {iota : Type u} {b tau rho s : NNReal} {R : Real}
      (hsit : Tube.IsRescalingSituation b tau rho R 3) (hR : 0 < R)
      (T0 : Tube b (EuclideanSpace Real (Fin 3))) (E : Finset iota)
      (Z : iota -> ShadedTube tau (EuclideanSpace Real (Fin 3)))
      (hratio : (tau : Real) / (b : Real) <= 4 * (rho : Real))
      (hsub : forall i, i ∈ E -> (Z i).carrier <= T0.carrier)
      (hsrho : rho <= s) (hs1 : s <= 1)
      (hunit : forall (U : Tube s (EuclideanSpace Real (Fin 3))) (D : Real), 0 < D ->
        exists V : Tube (Real.toNNReal D * s) (EuclideanSpace Real (Fin 3)),
          (Tube.dilate U D).carrier ∩ Metric.closedBall 0 (1 / 4 : Real) <= V.carrier) :
      exists (W : Finset iota) (V : iota -> Tube s (EuclideanSpace Real (Fin 3)))
        (Vc : iota -> Tube (2 * Real.toNNReal (Tube.tubeOverlapCoreClose.C 3) * s)
          (EuclideanSpace Real (Fin 3))),
        W <= E /\
        ((W : Set iota).Pairwise (fun j k =>
          _root_.IsEssentiallyDistinct (V j).carrier (V k).carrier)) /\
        (forall j, j ∈ W ->
          (spineFamily (spineRescaleUnit hsit.pos_ambient T0 hR) Z j).toConvexSpaceBody <=
            (V j).toConvexSpaceBody) /\
        SourceQImageCovered hsit hR T0 E Z W Vc := by
    classical
    let O : iota -> Tube rho (EuclideanSpace Real (Fin 3)) := fun i =>
      (outerFamily hsit.pos_ambient T0 hR rho Z i).toTube
    let V : iota -> Tube s (EuclideanSpace Real (Fin 3)) := fun i => (O i).rescale s
    have hV (i : iota) (hi : i ∈ E) :
        (spineFamily (spineRescaleUnit hsit.pos_ambient T0 hR) Z i).toConvexSpaceBody <=
          (V i).toConvexSpaceBody :=
      (spineImage_le_outerShadedTube (by simp) hsit hR hratio T0 (Z i) (hsub i hi)).trans
        ((O i).le_rescale hsrho)
    have hs0 : 0 < s := hsit.pos_out.trans_le hsrho
    obtain ⟨W, hWE, hED, hcover⟩ := Tube.exists_essDistinct_dilateCover hs0 hs1 E V
    let D : Real := Tube.tubeOverlapCoreClose.C 3
    have hD0 : 0 < D := lt_trans zero_lt_one (Tube.tubeOverlapCoreClose.one_lt_C 3)
    let U : iota -> Tube (Real.toNNReal D * s) (EuclideanSpace Real (Fin 3)) :=
      fun i => (hunit (V i) D hD0).choose
    let Vc : iota -> Tube (2 * Real.toNNReal D * s) (EuclideanSpace Real (Fin 3)) :=
      fun i => (U i).rescale (2 * Real.toNNReal D * s)
    have hUc (i : iota) : (U i).toConvexSpaceBody <= (Vc i).toConvexSpaceBody := by
      apply (U i).le_rescale
      nlinarith only [show (0 : NNReal) <= Real.toNNReal D * s from zero_le]
    refine ⟨W, V, Vc, hWE, hED, fun j hj => hV j (hWE hj), ?_⟩
    intro i hi
    obtain ⟨j, hj, hij⟩ := hcover i hi
    refine ⟨j, hj, ?_⟩
    intro x hx
    apply hUc j
    apply (hunit (V j) D hD0).choose_spec
    refine ⟨?_, ?_⟩
    · have hxV := hV i hi hx
      simpa [D] using hij hxV
    · have hball := Tube.rescale_image_ambient_subset_closedBall hsit.pos_ambient
        hsit.ambient_le_one hR (by simpa using hsit.normalizationConst_le_radius) T0
      apply hball
      change x ∈ spineRescaleUnit hsit.pos_ambient T0 hR '' (Z i).carrier at hx
      rw [spineRescaleUnit_coe] at hx
      exact (Set.image_mono (hsub i hi)) hx
  let D : Real := Tube.tubeOverlapCoreClose.C 3
  have hD1 : 1 <= D := (Tube.tubeOverlapCoreClose.one_lt_C 3).le
  have hD0 : 0 < D := zero_lt_one.trans_le hD1
  have hscalar := hradii varpi zeta D (centringCountLossConstant R)
    hp.vns_window_pos hp.vns_window_upper hp.excess_pos hD1 (by positivity)
  obtain ⟨eps, heps, hscalarEps⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hscalar
  obtain ⟨d0, hd0, hd01, hconst⟩ := ML2Shaded.exists_threshold_const_le_rpow_neg'
    (1 / (eps : Real)) (by linarith only [hp.window_pos] : 0 < e / 2)
  obtain ⟨G, hG, hall⟩ := sourceQ_exists_allRadius_charge M A0 A1 C e varpi zeta etaC R hp
  filter_upwards [hall, Ioo_mem_nhdsGT hd0] with delta hallDelta hd
  intro iota S T Q Y hgeom hstats a p b jp F E Z rho hi hEF hretain hsit hR
  have hsubF (i : iota) (hfi : i ∈ F) : (Z i).carrier <= (Q.tube p jp).carrier := by
    have hids := sourceQ_ancestor_fibre_identities Q hi.parent_lt_middle.le hi.middle_bound
    have hii := hi.family_subset hfi
    rw [hids.2.2.2 jp hi.parent_member] at hii
    obtain ⟨hib, hip⟩ := Finset.mem_filter.mp hii
    have hh := hids.2.2.1 i hib
    rw [hip] at hh
    change (Z i).toTube.carrier <= (Q.tube p jp).carrier
    rw [hi.family_tubes i]
    exact hh
  have hratio : (sourceTowerRadius delta M b : Real) /
      (sourceTowerRadius delta M p : Real) <= 4 * (rho : Real) := by
    have heq : (rho : Real) = (sourceTowerRadius delta M b : Real) /
        (2 * (sourceTowerRadius delta M p : Real)) := by exact_mod_cast hi.rho_eq
    have hp0 : (0 : Real) < sourceTowerRadius delta M p := by exact_mod_cast hsit.pos_ambient
    have heq2 : (sourceTowerRadius delta M b : Real) /
        (sourceTowerRadius delta M p : Real) = 2 * (rho : Real) := by
      rw [heq]
      field_simp
    rw [heq2]
    nlinarith only [rho.coe_nonneg]
  refine ⟨sourceQ_normalized_rows hsit hR (Q.tube p jp) F Z hratio hsubF, ?_⟩
  have hrhoeps : rho < eps := by
    have hepsR : (0 : Real) < eps := by exact_mod_cast heps
    have hdR : (0 : Real) < delta := by exact_mod_cast hd.1
    have hc := hconst hd.1 hd.2.le
    rw [Real.rpow_neg hdR.le, ← one_div] at hc
    have hpowe : (delta : Real) ^ (e / 2) <= eps := by
      simpa only [one_mul] using
        (div_le_div_iff₀ hepsR (Real.rpow_pos_of_pos hdR (e / 2))).mp hc
    have hr := hi.rho_upper
    exact_mod_cast (by linarith only [hpowe, hr, hepsR] : (rho : Real) < eps)
  intro sigma hsigma
  obtain ⟨hsmall, hs1, hwide, hpaid⟩ := hscalarEps ⟨hsit.pos_out, hrhoeps⟩ sigma hsigma
  obtain ⟨W, V, Vc, hWE, hED, hused, hcovered⟩ := hedcover hsit hR (Q.tube p jp) E Z
    hratio (fun i hi' => hsubF i (hEF hi')) hsmall hs1 hunit
  let sigma' : NNReal := Real.toNNReal D * sigma
  let Vc' : iota -> Tube sigma' (EuclideanSpace Real (Fin 3)) :=
    fun i => (Vc i).rescale sigma'
  have hscale : 2 * Real.toNNReal (Tube.tubeOverlapCoreClose.C 3) *
      (sigma / centringCoverRadiusConstant) = sigma' := by
    dsimp [sigma', D, centringCoverRadiusConstant]
    ring
  have hcover' : SourceQImageCovered hsit hR (Q.tube p jp) E Z W Vc' := by
    intro i hi'
    obtain ⟨j, hj, hij⟩ := hcovered i hi'
    exact ⟨j, hj, hij.trans ((Vc j).le_rescale hscale.le)⟩
  obtain ⟨B, _, _, hcount⟩ := hallDelta S T Q Y hgeom hstats a p b jp F E Z rho hi
    hEF hretain hsit hR sigma' hwide W Vc' hcover'
  exact ⟨iota, W, V, hED, fun j hj => ⟨j, hWE hj, hused j hj⟩, hpaid.trans hcount⟩

open scoped Classical in
/-- The actual deduplicated outer-tube image of the original finite indices. -/
noncomputable def sourceQOuterImage {b tau rho : NNReal} {R : Real}
    (hsit : Tube.IsRescalingSituation b tau rho R 3) (hR : 0 < R)
    (T0 : Tube b (EuclideanSpace Real (Fin 3))) (F : Finset iota)
    (Z : iota -> ShadedTube tau (EuclideanSpace Real (Fin 3))) :
    Finset (Tube rho (EuclideanSpace Real (Fin 3))) :=
  F.image (fun i => (outerFamily hsit.pos_ambient T0 hR rho Z i).toTube)

open scoped Classical in
/-- This is the actual quotient diagram of outerFamily. Nothing identifies
its index set or cardinality with F; the actual image map is recorded. -/
theorem sourceQ_outer_image_diagram {b tau rho : NNReal} {R : Real}
    (hsit : Tube.IsRescalingSituation b tau rho R 3) (hR : 0 < R)
    (T0 : Tube b (EuclideanSpace Real (Fin 3))) (F E : Finset iota)
    (Z : iota -> ShadedTube tau (EuclideanSpace Real (Fin 3))) (hEF : E <= F) :
    sourceQOuterImage hsit hR T0 E Z <= sourceQOuterImage hsit hR T0 F Z /\
    (sourceQOuterImage hsit hR T0 F Z).card <= F.card /\
    (forall v, v ∈ sourceQOuterImage hsit hR T0 F Z -> exists i, i ∈ F /\
      (outerFamily hsit.pos_ambient T0 hR rho Z i).toTube = v) /\
    (forall v, v ∈ sourceQOuterImage hsit hR T0 E Z -> exists i, i ∈ E /\
      (outerFamily hsit.pos_ambient T0 hR rho Z i).toTube = v) /\
    (forall B : Nat, (forall v, v ∈ sourceQOuterImage hsit hR T0 E Z ->
      (E.filter (fun i => (outerFamily hsit.pos_ambient T0 hR rho Z i).toTube = v)).card <= B) ->
      E.card <= B * (sourceQOuterImage hsit hR T0 E Z).card) := by
  refine ⟨Finset.image_subset_image hEF, Finset.card_image_le, ?_, ?_, ?_⟩
  · intro v hv
    exact Finset.mem_image.mp hv
  · intro v hv
    exact Finset.mem_image.mp hv
  · intro B hB
    exact Finset.card_le_mul_card_image E B hB

end Kakeya.ML2Assembly
