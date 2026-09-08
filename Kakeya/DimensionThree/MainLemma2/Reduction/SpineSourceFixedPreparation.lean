/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceAssignedProfile
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceFixedTowerGeometryData

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

/-- Source eqvectorbinloss, with its actual fixed level and statistic dependence. -/
noncomputable def sourceVectorBinLoss (M K0 : Nat) (rangeBound : Real) : ENNReal :=
  ENNReal.ofReal (((K0 : Real) * (2 + 2 * Real.logb 2 rangeBound) ^ K0) ^ (M + 1))

/-- The source uses log base two and fixes K before delta. -/
noncomputable def sourceFixedPreparationLoss (K : Nat) (delta : NNReal) : ENNReal :=
  ENNReal.ofReal ((2 + Real.logb 2 (1 / (delta : Real))) ^ K)

section FixedTower

variable {iota : Type u} {delta : NNReal} {ambient : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- The fixed source tower's input is centred/ED source data, not arbitrary SSF uniformity. -/
structure SourceFixedTowerInput (Q : SourceThreadedTower ambient T M C)
    (A0 A1 : Nat) (eta0 : Real) : Prop where
  geometry : SourceTowerGeometry Q A0 A1
  neighbour_sharing : SourceTowerNeighbourSharing Q
  maximal_density : Kakeya.maxDensity ambient (fun i => (T i).toConvexSpaceBody) <=
    ENNReal.ofReal ((delta : Real) ^ (-eta0))

/-- One source preparation ledger on the original named fixed-M tower, with unchanged Z. -/
structure SourceFixedPreparationLedger (Q : SourceThreadedTower ambient T M C)
    (S R : Finset iota) (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (eta0 h : Real) (loss : ENNReal) : Prop where
  subset : R <= S
  nonempty : R.Nonempty
  original_subset : S <= ambient
  original_tubes : ∀ i, (Z i).toTube = T i
  mass : (∑ i ∈ S, volume (Z i).shade) <= loss * ∑ i ∈ R, volume (Z i).shade
  multiplicity : ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
    loss * ShadedBody.multiplicity R (fun i => (Z i).toShadedBody)
  fullness : ShadedBody.fullness' S (fun i => (Z i).toShadedBody) <=
    loss * ShadedBody.fullness' R (fun i => (Z i).toShadedBody)
  fullness_floor : ENNReal.ofReal ((delta : Real) ^ (3 * eta0)) <=
    ShadedBody.fullness' R (fun i => (Z i).toShadedBody)
  density : Kakeya.maxDensity R (fun i => (Z i).toConvexSpaceBody) <=
    ENNReal.ofReal ((delta : Real) ^ (-eta0))
  leaf_mass_floor : ∀ i ∈ R,
    (delta : ENNReal) ^ (10 : Real) * volume (T i).carrier <= volume (Z i).shade
  shade_in_carrier : ∀ i ∈ R, (Z i).shade <= (T i).carrier
  source_potential : Q.assignedPotential h R <= Q.assignedPotential h S

end FixedTower

/-- Source S:4338-4363,4914-4928, on the already fixed source tower.
The finite statistic count, range exponent, polylog power and threshold precede delta.
No SSF hierarchy, prepared window or source/runtime comparison is an input or hidden output. -/
theorem source_exists_fixedTower_preparation (M A0 A1 C : Nat)
    (hM : 2 <= M) (hC : 1 <= C) (hA0 : 1 <= A0) (hA1 : 1 <= A1)
    {eta0 h : Real} (heta0 : 0 < eta0) (hthin : 2 * eta0 < 10) (hh : 0 < h) :
    ∃ (K0 K : Nat) (B : Real) (delta0 : NNReal),
      1 <= K0 /\ 1 <= K /\ 0 < B /\ 0 < delta0 /\ delta0 <= 1 /\
      delta0 <= (400 : NNReal) ^ (-(M : Real)) /\
      ∀ delta : NNReal, 0 < delta -> delta < delta0 ->
      ∀ {iota : Type u} (ambient : Finset iota)
        (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
        (Q : SourceThreadedTower ambient T M C),
        SourceFixedTowerInput Q A0 A1 eta0 ->
      ∀ S : Finset iota, S <= ambient -> S.Nonempty ->
      ∀ Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)),
        (∀ i, (Z i).toTube = T i) ->
        ENNReal.ofReal ((delta : Real) ^ (2 * eta0)) <=
          ShadedBody.fullness' S (fun i => (Z i).toShadedBody) ->
      ∃ (R : Finset iota) (Q' : SourceThreadedTower R T M C),
        SourceTowerRestriction Q Q' /\ SourceFixedTowerInput Q' A0 A1 eta0 /\
        SourceTowerStatistics Q' Z /\
        SourceFixedPreparationLedger Q S R Z eta0 h
          (2 * sourceVectorBinLoss M K0 ((delta : Real) ^ (-B))) /\
        2 * sourceVectorBinLoss M K0 ((delta : Real) ^ (-B)) <=
          sourceFixedPreparationLoss K delta := by
  classical
  have hrestrict : ∀ {delta : NNReal} {iota : Type u} {ambient : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))}
      (Q : SourceThreadedTower ambient T M C), SourceFixedTowerInput Q A0 A1 eta0 ->
      ∀ R : Finset iota, R <= ambient -> R.Nonempty ->
      ∃ Q' : SourceThreadedTower R T M C,
        SourceTowerRestriction Q Q' /\ SourceFixedTowerInput Q' A0 A1 eta0 := by
    intro delta iota ambient T Q hQ R hR hRne
    have hocc (k : Nat) (hk : k <= M) : Q.assignedFootprint R k <= Q.indexSet k := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact Q.place_mem k hk i (hR hi)
    let Q' : SourceThreadedTower R T M C := {
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
    have hrest : SourceTowerRestriction Q Q' := {
      subset := hR
      assignment := rfl
      parent := rfl
      tubes := rfl
      occupied := fun _ _ => rfl
      full_retained_fibres := fun _ _ _ => rfl }
    refine ⟨Q', hrest, {
      geometry := {
        nonempty := hRne
        original_centred := fun i hi => hQ.geometry.original_centred i (hR hi)
        original_ball := fun i hi => hQ.geometry.original_ball i (hR hi)
        original_ed := hQ.geometry.original_ed.subset hR
        coarse_centred := fun k hk j hj => hQ.geometry.coarse_centred k hk j (hocc k hk.le hj)
        coarse_ball := fun k hk j hj => hQ.geometry.coarse_ball k hk j (hocc k hk.le hj)
        coarse_ed := fun k hk => (hQ.geometry.coarse_ed k hk).subset (hocc k hk.le)
        coarse_card := by
          intro k hk
          calc ((Q.assignedFootprint R k).card : Real) <= ((Q.indexSet k).card : Real) := by
                exact_mod_cast Finset.card_le_card (hocc k hk.le)
            _ <= (32 / (sourceTowerRadius delta M k : Real)) ^ 6 := hQ.geometry.coarse_card k hk
        segment_sharing := ?_ }
      neighbour_sharing := ?_
      maximal_density := (Kakeya.maxDensity_mono (fun i => (T i).toConvexSpaceBody) hR).trans
        hQ.maximal_density }⟩
    · intro k hk x y hxy
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (hocc k hk.le))).trans
        (hQ.geometry.segment_sharing k hk x y hxy)
    · intro k hk j hj
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (hocc k hk.le))).trans
        (hQ.neighbour_sharing k hk j (hocc k hk.le hj))
  have hregular : ∀ {delta : NNReal}, 0 < delta ->
      ∀ {iota : Type u} {ambient : Finset iota}
        {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))}
        (Q : SourceThreadedTower ambient T M C), SourceFixedTowerInput Q A0 A1 eta0 ->
      ∀ (S : Finset iota), S <= ambient -> S.Nonempty ->
      ∀ (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        (∀ i, (Z i).toTube = T i) ->
      ∀ (v m : ENNReal), v ≠ 0 -> v ≠ ⊤ -> m ≠ 0 -> m <= 1 ->
        (∀ i ∈ ambient, volume (T i).carrier = v) ->
        (∀ i ∈ S, m * v <= volume (Z i).shade) ->
      ∀ J : Nat, (ambient.card : ENNReal) <= 2 ^ J * m ->
      ∃ (R : Finset iota) (Q' : SourceThreadedTower R T M C),
        R <= S /\ R.Nonempty /\ SourceTowerRestriction Q Q' /\
        SourceFixedTowerInput Q' A0 A1 eta0 /\ SourceTowerStatistics Q' Z /\
        (∑ i ∈ S, volume (Z i).shade) <=
          (((J + 1 : Nat) : ENNReal) ^ (2 * M + 4)) ^ (M + 1) * ∑ i ∈ R, volume (Z i).shade := by
    intro delta hdelta iota ambient T Q hQ S hS hSne Z hZT v m hv0 hvtop hm0 hm1 hvol hfloor J hJ
    have hcoarse (b : Nat) (hb : b <= M) : ∀ a, a <= b -> ∀ i ∈ ambient, ∀ j ∈ ambient,
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
    have hradius (k : Nat) : 0 < sourceTowerRadius delta M k := by
      unfold sourceTowerRadius
      split
      · positivity
      · exact hdelta
    let cell (k : Nat) (R : Finset iota) (i : iota) := R.filter fun j => Q.place k j = Q.place k i
    let fib (k b : Nat) (R : Finset iota) (i : iota) := (cell k R i).image (Q.place b)
    let mass (k : Nat) (R : Finset iota) (i : iota) := (∑ j ∈ cell k R i, volume (Z j).shade) / v
    let row (k q : Nat) (R : Finset iota) (i : iota) : ENNReal :=
      if q < M + 1 then Kakeya.maxDensity (fib k q R i) (fun j => (Q.tube q j).toConvexSpaceBody)
      else if q < 2 * M + 2 then ((fib k (q - (M + 1)) R i).card : ENNReal)
      else if q < 2 * M + 3 then ((cell k R i).card : ENNReal)
      else mass k R i
    have hcellmem (k : Nat) {R : Finset iota} {i : iota} (hi : i ∈ R) : i ∈ cell k R i :=
      Finset.mem_filter.mpr ⟨hi, rfl⟩
    have hcellsub (k : Nat) (R : Finset iota) (i : iota) : cell k R i <= R := Finset.filter_subset _ _
    have hfibcard (k b : Nat) (R : Finset iota) (i : iota) : (fib k b R i).card <= R.card :=
      Finset.card_image_le.trans (Finset.card_le_card (hcellsub k R i))
    have hmasslo (k : Nat) {R : Finset iota} (hR : R <= S) {i : iota} (hi : i ∈ R) :
        m <= mass k R i := by
      apply (ENNReal.le_div_iff_mul_le (.inl hv0) (.inl hvtop)).mpr
      exact (hfloor i (hR hi)).trans
        (Finset.single_le_sum (f := fun j => volume (Z j).shade) (fun _ _ => zero_le) (hcellmem k hi))
    have hmasshi (k : Nat) {R : Finset iota} (hR : R <= S) (i : iota) :
        mass k R i <= (ambient.card : ENNReal) := by
      apply (ENNReal.div_le_iff hv0 hvtop).mpr
      calc (∑ j ∈ cell k R i, volume (Z j).shade) <= ∑ j ∈ cell k R i, v := by
            apply Finset.sum_le_sum
            intro j hj
            have hzv : volume (Z j).carrier = v := by
              change volume (Z j).toTube.carrier = v
              rw [hZT j]
              exact hvol j (hS (hR (hcellsub k R i hj)))
            exact hzv ▸ measure_mono (Z j).shade_subset
        _ = ((cell k R i).card : ENNReal) * v := by rw [Finset.sum_const, nsmul_eq_mul]
        _ <= (ambient.card : ENNReal) * v := by
            apply mul_le_mul_left
            exact_mod_cast Finset.card_le_card ((hcellsub k R i).trans (hR.trans hS))
    have hrowlo (k q : Nat) {R : Finset iota} (hR : R <= S) {i : iota} (hi : i ∈ R) :
        m <= row k q R i := by
      unfold row
      split
      · apply hm1.trans
        apply Kakeya.one_le_maxDensity
        refine ⟨Q.place q i, Finset.mem_image_of_mem _ (hcellmem k hi), ?_⟩
        exact pos_iff_ne_zero.mpr (ML2Shaded.volume_carrier_ne_zero (hradius q) (Q.tube q (Q.place q i)))
      · split
        · apply hm1.trans
          exact_mod_cast Finset.card_pos.mpr ⟨Q.place (q - (M + 1)) i,
            Finset.mem_image_of_mem _ (hcellmem k hi)⟩
        · split
          · apply hm1.trans
            exact_mod_cast Finset.card_pos.mpr ⟨i, hcellmem k hi⟩
          · exact hmasslo k hR hi
    have hrowhi (k q : Nat) {R : Finset iota} (hR : R <= S) (i : iota) :
        row k q R i <= (ambient.card : ENNReal) := by
      have hRc : R.card <= ambient.card := Finset.card_le_card (hR.trans hS)
      unfold row
      split
      · exact (Kakeya.maxDensity_le_card _ _).trans (by exact_mod_cast (hfibcard k q R i).trans hRc)
      · split
        · exact_mod_cast (hfibcard k (q - (M + 1)) R i).trans hRc
        · split
          · exact_mod_cast (Finset.card_le_card (hcellsub k R i)).trans hRc
          · exact hmasshi k hR i
    have hrowlocal (k q : Nat) : LeafLocalStat (Q.place k) (row k q) := by
      intro R R' i heq
      change cell k R i = cell k R' i at heq
      simp only [row, fib, mass, heq]
    have hroweq (k q : Nat) (R : Finset iota) (i j : iota) (hij : Q.place k i = Q.place k j) :
        row k q R i = row k q R j := by
      have heq : cell k R i = cell k R j := by simp only [cell, hij]
      simp only [row, fib, mass, heq]
    have hmass0 : (∑ i ∈ S, volume (Z i).shade) ≠ 0 := by
      obtain ⟨i, hi⟩ := hSne
      intro hzero
      have hizero := Finset.sum_eq_zero_iff.mp hzero i hi
      exact mul_ne_zero hm0 hv0 (le_antisymm (hizero ▸ hfloor i hi) zero_le)
    obtain ⟨R, hRS, hRne, hmassR, -, Phi, hPhi⟩ :=
      exists_multiLevel_band_wt (n := 2 * M + 4) (γ := iota) S
        (fun i => volume (Z i).shade) hmass0 (fun p => Q.place (M - p))
        (fun p q hpq i hi j hj heq => hcoarse (M - p) (Nat.sub_le _ _) (M - q)
          (Nat.sub_le_sub_left hpq M) i (hS hi) j (hS hj) heq)
        (fun p q R i => row (M - p) q R i)
        (fun p q => hrowlocal (M - p) q)
        (fun p q R i => dyadicScaleBucket m (row (M - p) q R i))
        (fun p q R i j hij => congrArg (dyadicScaleBucket m) (hroweq (M - p) q R i j hij))
        (J + 1) (Nat.succ_pos J)
        (fun p q R hR i _ => dyadicScaleBucket_lt_succ ((hrowhi (M - p) q hR i).trans hJ))
        (fun p q R hR i hi j hj heq => le_two_mul_of_dyadicScaleBucket_eq
          ⟨J, (hrowhi (M - p) q hR i).trans hJ⟩
          ⟨J, (hrowhi (M - p) q hR j).trans hJ⟩ (hrowlo (M - p) q hR hi) heq)
        (fun _ _ => 0) 1 (by norm_num) (fun _ _ _ => by norm_num) (fun _ _ _ _ => rfl) M
    obtain ⟨Q', hrest, hQ'⟩ := hrestrict Q hQ R (hRS.trans hS) hRne
    have hband (k : Nat) (hk : k <= M) (q : Fin (2 * M + 4))
        (i : iota) (hi : i ∈ R) (j : iota) (hj : j ∈ R) :
        row k q R i <= 2 * row k q R j := by
      have hi' := hPhi (M - k) (Nat.sub_le _ _) q i hi
      have hj' := hPhi (M - k) (Nat.sub_le _ _) q j hj
      rw [Nat.sub_sub_self hk] at hi' hj'
      exact hi'.2.trans (mul_le_mul_right hj'.1 2)
    have hcellEq (k : Nat) (i : iota) : cell k R i = Q'.cell k (Q'.place k i) := by
      simp only [cell, SourceThreadedTower.cell, hrest.assignment]
    have hfibEq (k b : Nat) (i : iota) : fib k b R i = Q'.fibre k b (Q'.place k i) := by
      simp only [fib, SourceThreadedTower.fibre, hcellEq, hrest.assignment]
    refine ⟨R, Q', hRS, hRne, hrest, hQ', {
      same_tubes := hZT
      descendant_count := ?_
      two_level_count := ?_
      two_level_density := ?_
      fibre_mass := ?_ }, by simpa only [Nat.cast_one, one_mul] using hmassR⟩
    · intro k hk j hj j' hj'
      obtain ⟨i, hi, rfl⟩ := Q'.place_surjective k hk j hj
      obtain ⟨i', hi', rfl⟩ := Q'.place_surjective k hk j' hj'
      have hband' := hband k hk ⟨2 * M + 2, by omega⟩ i hi i' hi'
      simpa only [row, show ¬ 2 * M + 2 < M + 1 by omega, if_false,
        show ¬ 2 * M + 2 < 2 * M + 2 by omega, show 2 * M + 2 < 2 * M + 3 by omega,
        if_true, hcellEq] using hband'
    · intro a b hab hb j hj j' hj'
      obtain ⟨i, hi, rfl⟩ := Q'.place_surjective a (by omega) j hj
      obtain ⟨i', hi', rfl⟩ := Q'.place_surjective a (by omega) j' hj'
      have hband' := hband a (by omega) ⟨M + 1 + b, by omega⟩ i hi i' hi'
      simpa only [row, show ¬ M + 1 + b < M + 1 by omega, if_false,
        show M + 1 + b < 2 * M + 2 by omega, if_true, Nat.add_sub_cancel_left, hfibEq] using hband'
    · intro a b hab hb j hj j' hj'
      obtain ⟨i, hi, rfl⟩ := Q'.place_surjective a (by omega) j hj
      obtain ⟨i', hi', rfl⟩ := Q'.place_surjective a (by omega) j' hj'
      have hband' := hband a (by omega) ⟨b, by omega⟩ i hi i' hi'
      simpa only [row, show b < M + 1 by omega, if_true, hfibEq, hrest.tubes] using hband'
    · intro k hk j hj j' hj'
      obtain ⟨i, hi, rfl⟩ := Q'.place_surjective k hk j hj
      obtain ⟨i', hi', rfl⟩ := Q'.place_surjective k hk j' hj'
      have hband' := hband k hk ⟨2 * M + 3, by omega⟩ i hi i' hi'
      simp only [row, show ¬ 2 * M + 3 < M + 1 by omega, if_false,
        show ¬ 2 * M + 3 < 2 * M + 2 by omega, show ¬ 2 * M + 3 < 2 * M + 3 by omega,
        mass, hcellEq] at hband'
      simpa only [mul_assoc, ENNReal.div_mul_cancel hv0 hvtop] using mul_le_mul_left hband' v
  have hcut : ∀ {delta : NNReal}, 0 < delta ->
      ∀ {iota : Type u} (S : Finset iota), S.Nonempty ->
      ∀ (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))) {m : ENNReal},
        m ≠ 0 -> 2 * m <= ShadedBody.fullness' S (fun i => (Z i).toShadedBody) ->
      ∃ S' : Finset iota, S' <= S /\ S'.Nonempty /\
        (∑ i ∈ S, volume (Z i).shade) <= 2 * ∑ i ∈ S', volume (Z i).shade /\
        ∀ i ∈ S', m * volume (Z i).carrier <= volume (Z i).shade := by
    intro delta hdelta iota S hS Z m hm0 hm
    let P (i : iota) := m * volume (Z i).carrier <= volume (Z i).shade
    let G := S.filter P
    let B := S.filter fun i => ¬ P i
    have hsplit : (∑ i ∈ G, volume (Z i).shade) + (∑ i ∈ B, volume (Z i).shade) =
        ∑ i ∈ S, volume (Z i).shade := Finset.sum_filter_add_sum_filter_not S P _
    have hbad : 2 * (∑ i ∈ B, volume (Z i).shade) <= ∑ i ∈ S, volume (Z i).shade := by
      calc 2 * (∑ i ∈ B, volume (Z i).shade) <= 2 * ∑ i ∈ B, m * volume (Z i).carrier := by
            apply mul_le_mul_right
            exact Finset.sum_le_sum fun i hi => (not_le.mp (Finset.mem_filter.mp hi).2).le
        _ <= 2 * ∑ i ∈ S, m * volume (Z i).carrier := by
            apply mul_le_mul_right
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => zero_le)
        _ = (2 * m) * ∑ i ∈ S, volume (Z i).carrier := by rw [← Finset.mul_sum, ← mul_assoc]
        _ <= ShadedBody.fullness' S (fun i => (Z i).toShadedBody) * ∑ i ∈ S, volume (Z i).carrier :=
            mul_le_mul_left hm _
        _ = ∑ i ∈ S, volume (Z i).shade := by
            simpa only [ShadedBody.coe_fullness] using
              (ShadedBody.sum_volumeReal_shade_eq_fullness_mul S (fun i => (Z i).toShadedBody)).symm
    have hBtop : (∑ i ∈ B, volume (Z i).shade) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr fun i _ => ne_top_of_le_ne_top
        (Z i).isCompact'.measure_ne_top (measure_mono (Z i).shade_subset)
    have hBG : (∑ i ∈ B, volume (Z i).shade) <= ∑ i ∈ G, volume (Z i).shade := by
      apply ENNReal.le_of_add_le_add_right hBtop
      simpa only [two_mul, hsplit] using hbad
    have hmass : (∑ i ∈ S, volume (Z i).shade) <= 2 * ∑ i ∈ G, volume (Z i).shade := by
      rw [← hsplit, two_mul]
      exact add_le_add_right hBG _
    have hmass0 : (∑ i ∈ S, volume (Z i).shade) ≠ 0 := by
      intro hzero
      have hfzero : ShadedBody.fullness' S (fun i => (Z i).toShadedBody) = 0 := by
        simp only [ShadedBody.fullness', hzero, ENNReal.zero_div]
      exact mul_ne_zero (by norm_num : (2 : ENNReal) ≠ 0) hm0
        (le_antisymm (hfzero ▸ hm) zero_le)
    refine ⟨G, Finset.filter_subset _ _, ?_, hmass, fun i hi => (Finset.mem_filter.mp hi).2⟩
    by_contra hempty
    have hG : G = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    simp only [hG, Finset.sum_empty, mul_zero] at hmass
    exact hmass0 (le_antisymm hmass zero_le)
  let K0 := 2 * M + 4
  have hK0 : 1 <= K0 := by omega
  have hpoly : ∃ K : Nat, 1 <= K /\ ∀ delta : NNReal, 0 < delta -> delta <= 1 ->
      2 * sourceVectorBinLoss M K0 ((delta : Real) ^ (-40 : Real)) <=
        sourceFixedPreparationLoss K delta := by
    let A : Real := 2 * ((K0 : Real) * 80 ^ K0) ^ (M + 1)
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt A (by norm_num : (1 : Real) < 2)
    have hKM : 1 <= K0 * (M + 1) := Nat.mul_pos hK0 (by omega)
    refine ⟨K0 * (M + 1) + N, by omega, ?_⟩
    intro delta hdelta hdelta1
    have hd : (0 : Real) < delta := by exact_mod_cast hdelta
    have hd1 : (delta : Real) <= 1 := by exact_mod_cast hdelta1
    have hl : 0 <= Real.logb 2 (1 / (delta : Real)) :=
      Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hd]; linarith)
    have hlog : Real.logb 2 ((delta : Real) ^ (-40 : Real)) =
        40 * Real.logb 2 (1 / (delta : Real)) := by
      rw [Real.logb_rpow_eq_mul_logb_of_pos hd, one_div, Real.logb_inv]
      ring
    let x : Real := 2 + Real.logb 2 (1 / (delta : Real))
    have hx : 2 <= x := by dsimp [x]; linarith
    have hlog0 : 0 <= Real.logb 2 ((delta : Real) ^ (-40 : Real)) := by rw [hlog]; positivity
    have hreal : 2 * ((K0 : Real) * (2 + 2 * Real.logb 2 ((delta : Real) ^ (-40 : Real))) ^ K0) ^ (M + 1) <=
        x ^ (K0 * (M + 1) + N) := by
      calc 2 * ((K0 : Real) * (2 + 2 * Real.logb 2 ((delta : Real) ^ (-40 : Real))) ^ K0) ^ (M + 1) <=
            2 * ((K0 : Real) * (80 * x) ^ K0) ^ (M + 1) := by
              gcongr
              rw [hlog]
              dsimp [x]
              linarith
        _ = A * x ^ (K0 * (M + 1)) := by simp only [A, mul_pow, pow_mul]; ring
        _ <= x ^ N * x ^ (K0 * (M + 1)) :=
            mul_le_mul_of_nonneg_right (hN.le.trans (pow_le_pow_left₀ (by norm_num) hx N)) (by positivity)
        _ = x ^ (K0 * (M + 1) + N) := by rw [pow_add]; ring
    unfold sourceVectorBinLoss sourceFixedPreparationLoss
    rw [show (2 : ENNReal) = ENNReal.ofReal (2 : Real) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hreal
  obtain ⟨K, hK, hKbound⟩ := hpoly
  have hloss : ∀ᶠ delta : NNReal in 𝓝[>] 0,
      sourceFixedPreparationLoss K delta <= (delta : ENNReal) ^ (-eta0) := by
    filter_upwards [Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (K := (2 : ENNReal) ^ K) (by finiteness) (by positivity : 0 < eta0 / 2),
      ENNReal.eventually_ofReal_one_add_logb_pow_le_rpow_neg (by positivity : 0 < eta0 / 2) K,
      Ioo_mem_nhdsGT (by norm_num : (0 : NNReal) < 1)] with delta hc hl hd
    have hdelta0 : (delta : ENNReal) ≠ 0 := by exact_mod_cast hd.1.ne'
    have hdreal : (0 : Real) < delta := by exact_mod_cast hd.1
    have hdreal1 : (delta : Real) <= 1 := by exact_mod_cast hd.2.le
    have hlog : 0 <= Real.logb 2 (1 / (delta : Real)) :=
      Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hdreal]; linarith)
    calc sourceFixedPreparationLoss K delta <=
          ENNReal.ofReal ((2 * (1 + Real.logb 2 (1 / (delta : Real)))) ^ K) := by
            apply ENNReal.ofReal_le_ofReal
            gcongr
            linarith
      _ = (2 : ENNReal) ^ K * ENNReal.ofReal (1 + Real.logb 2 (1 / (delta : Real))) ^ K := by
            rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num), mul_pow]
            norm_num
      _ <= (delta : ENNReal) ^ (-(eta0 / 2)) * (delta : ENNReal) ^ (-(eta0 / 2)) := mul_le_mul' hc hl
      _ = (delta : ENNReal) ^ (-eta0) := by
            rw [← ENNReal.rpow_add _ _ hdelta0 ENNReal.coe_ne_top]
            congr 1
            ring
  have hthinEvent : ∀ᶠ delta : NNReal in 𝓝[>] 0,
      2 * (delta : ENNReal) ^ (10 : Real) <= (delta : ENNReal) ^ (2 * eta0) := by
    filter_upwards [Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
      (K := 2) (by norm_num) (by linarith : 0 < 10 - 2 * eta0),
      self_mem_nhdsWithin] with delta hc hd
    have hd0 : (delta : ENNReal) ≠ 0 := by exact_mod_cast (show delta ≠ 0 from ne_of_gt hd)
    calc 2 * (delta : ENNReal) ^ (10 : Real) <=
          (delta : ENNReal) ^ (-(10 - 2 * eta0)) * (delta : ENNReal) ^ (10 : Real) := mul_le_mul_left hc _
      _ = (delta : ENNReal) ^ (2 * eta0) := by
            rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
            congr 1
            ring
  let ccard : ENNReal := Kakeya.Tube.card_le_of_densityIn_le.C 3
  have hcardEvent : ∀ᶠ delta : NNReal in 𝓝[>] 0, ccard <= (delta : ENNReal) ^ (-1 : Real) :=
    Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg ENNReal.coe_ne_top (by norm_num)
  have hevent : ∀ᶠ delta : NNReal in 𝓝[>] 0,
      sourceFixedPreparationLoss K delta <= (delta : ENNReal) ^ (-eta0) /\
      2 * (delta : ENNReal) ^ (10 : Real) <= (delta : ENNReal) ^ (2 * eta0) /\
      ccard <= (delta : ENNReal) ^ (-1 : Real) := by
    filter_upwards [hloss, hthinEvent, hcardEvent] with delta hl ht hc
    exact ⟨hl, ht, hc⟩
  obtain ⟨eps, heps, hforall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  let delta0 := min eps (min 1 ((400 : NNReal) ^ (-(M : Real))))
  have hdelta00 : 0 < delta0 := lt_min heps (lt_min (by norm_num) (by positivity))
  have hdelta01 : delta0 <= 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hdelta0M : delta0 <= (400 : NNReal) ^ (-(M : Real)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨K0, K, 40, delta0, hK0, hK, by norm_num, hdelta00, hdelta01, hdelta0M, ?_⟩
  intro delta hdelta hdeltaBound iota ambient T Q hQ S hS hSne Z hZT hfull
  have hdelta1 : delta <= 1 := hdeltaBound.le.trans hdelta01
  have hd : (0 : Real) < delta := by exact_mod_cast hdelta
  have hd1 : (delta : Real) <= 1 := by exact_mod_cast hdelta1
  have hd0 : (delta : ENNReal) ≠ 0 := by exact_mod_cast hdelta.ne'
  have hd1e : (delta : ENNReal) <= 1 := by exact_mod_cast hdelta1
  have hepow (x : Real) : ENNReal.ofReal ((delta : Real) ^ x) = (delta : ENNReal) ^ x := by
    rw [← ENNReal.ofReal_rpow_of_pos hd]
    simp only [ENNReal.ofReal_coe_nnreal]
  obtain ⟨hlossδ, hthinδ, hcardδ⟩ := hforall ⟨hdelta, hdeltaBound.trans_le (min_le_left _ _)⟩
  have hcard : (ambient.card : ENNReal) <= (delta : ENNReal) ^ (-8 : Real) := by
    have hc := Kakeya.Tube.card_le_of_densityIn_le hdelta.ne'
      (fun i hi => (hQ.geometry.original_ball i hi).trans
        (Metric.closedBall_subset_closedBall (by norm_num : (3 / 4 : Real) <= 1)))
      ((Kakeya.le_maxDensity ambient (fun i => (T i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall).trans hQ.maximal_density)
    have hc' : (ambient.card : ENNReal) <= ccard * (delta : ENNReal) ^ (-eta0) *
        (delta : ENNReal) ^ (-2 : Real) := by
      rw [show (-2 : Real) = ((-2 : Int) : Real) by norm_num, ENNReal.rpow_intCast]
      simpa only [hepow, show Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3 by simp,
        Nat.cast_ofNat, show -((3 : Int) - 1) = -2 by norm_num, ENNReal.rpow_intCast] using hc
    calc (ambient.card : ENNReal) <= ccard * (delta : ENNReal) ^ (-eta0) *
          (delta : ENNReal) ^ (-2 : Real) := hc'
      _ <= (delta : ENNReal) ^ (-1 : Real) * (delta : ENNReal) ^ (-eta0) *
          (delta : ENNReal) ^ (-2 : Real) := mul_le_mul_left (mul_le_mul_left hcardδ _) _
      _ = (delta : ENNReal) ^ (-(eta0 + 3)) := by
            rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top, ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
            congr 1
            ring
      _ <= (delta : ENNReal) ^ (-8 : Real) := ENNReal.rpow_le_rpow_of_exponent_ge hd1e (by linarith)
  let m : ENNReal := (delta : ENNReal) ^ (10 : Real)
  have hm0 : m ≠ 0 := (ENNReal.rpow_pos (by exact_mod_cast hdelta) ENNReal.coe_ne_top).ne'
  have hm1 : m <= 1 := ENNReal.rpow_le_one hd1e (by norm_num)
  obtain ⟨S1, hS1, hS1ne, hcutmass, hfloor⟩ := hcut hdelta S hSne Z hm0
    (hthinδ.trans ((hepow (2 * eta0)) ▸ hfull))
  obtain ⟨i0, hi0⟩ := hSne
  let v := volume (T i0).carrier
  have hv0 : v ≠ 0 := ML2Shaded.volume_carrier_ne_zero hdelta (T i0)
  have hvtop : v ≠ ⊤ := ML2Shaded.volume_carrier_ne_top (T i0)
  have hvol (i : iota) (_hi : i ∈ ambient) : volume (T i).carrier = v :=
    Tube.volume_carrier_eq_volume_carrier (T i) (T i0)
  let L : Real := Real.logb 2 ((delta : Real) ^ (-40 : Real))
  let J : Nat := Nat.ceil L
  have hL0 : 0 <= L := Real.logb_nonneg (by norm_num)
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (by norm_num))
  have hJpow : (delta : ENNReal) ^ (-40 : Real) <= (2 : ENNReal) ^ J := by
    have hpow : (delta : Real) ^ (-40 : Real) <= (2 : Real) ^ J := by
      calc (delta : Real) ^ (-40 : Real) = (2 : Real) ^ L :=
            (Real.rpow_logb (by norm_num) (by norm_num) (by positivity)).symm
        _ <= (2 : Real) ^ (J : Real) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil L)
        _ = (2 : Real) ^ J := Real.rpow_natCast _ _
    have he := ENNReal.ofReal_le_ofReal hpow
    simpa only [hepow, ENNReal.ofReal_pow (by norm_num : (0 : Real) <= 2), ENNReal.ofReal_ofNat] using he
  have hJrange : (ambient.card : ENNReal) <= 2 ^ J * m := by
    calc (ambient.card : ENNReal) <= (delta : ENNReal) ^ (-8 : Real) := hcard
      _ <= (delta : ENNReal) ^ (-30 : Real) := ENNReal.rpow_le_rpow_of_exponent_ge hd1e (by norm_num)
      _ = (delta : ENNReal) ^ (-40 : Real) * m := by
            rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
            norm_num
      _ <= 2 ^ J * m := mul_le_mul_left hJpow _
  obtain ⟨R, Q', hRS1, hRne, hrest, hQ', hstats, hregmass⟩ := hregular hdelta Q hQ S1
    (hS1.trans hS) hS1ne Z hZT v m hv0 hvtop hm0 hm1 hvol
    (fun i hi => by
      have hzv : volume (Z i).carrier = v := by
        change volume (Z i).toTube.carrier = v
        rw [hZT i]
        exact hvol i (hS (hS1 hi))
      simpa only [hzv] using hfloor i hi) J hJrange
  let loss := 2 * sourceVectorBinLoss M K0 ((delta : Real) ^ (-40 : Real))
  have hbin : (((J + 1 : Nat) : ENNReal) ^ K0) ^ (M + 1) <=
      sourceVectorBinLoss M K0 ((delta : Real) ^ (-40 : Real)) := by
    have hJle : ((J + 1 : Nat) : Real) <= 2 + 2 * L := by
      have hc := Nat.ceil_lt_add_one hL0
      simp only [Nat.cast_add, Nat.cast_one]
      dsimp [J]
      linarith
    have hb : ((J + 1 : Nat) : Real) ^ K0 <= (K0 : Real) * (2 + 2 * L) ^ K0 := by
      calc ((J + 1 : Nat) : Real) ^ K0 <= (2 + 2 * L) ^ K0 := by gcongr
        _ <= (K0 : Real) * (2 + 2 * L) ^ K0 := by
              exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast hK0)
    have hp := pow_le_pow_left₀ (by positivity) hb (M + 1)
    have he := ENNReal.ofReal_le_ofReal hp
    simpa only [ENNReal.ofReal_pow (by positivity : (0 : Real) <= ((J + 1 : Nat) : Real)),
      ENNReal.ofReal_pow (by positivity : (0 : Real) <= ((J + 1 : Nat) : Real) ^ K0),
      ENNReal.ofReal_natCast, sourceVectorBinLoss, L] using he
  have hRS : R <= S := hRS1.trans hS1
  have hmass : (∑ i ∈ S, volume (Z i).shade) <= loss * ∑ i ∈ R, volume (Z i).shade := by
    calc (∑ i ∈ S, volume (Z i).shade) <= 2 * ∑ i ∈ S1, volume (Z i).shade := hcutmass
      _ <= 2 * ((((J + 1 : Nat) : ENNReal) ^ K0) ^ (M + 1) * ∑ i ∈ R, volume (Z i).shade) :=
          mul_le_mul_right hregmass 2
      _ <= 2 * (sourceVectorBinLoss M K0 ((delta : Real) ^ (-40 : Real)) * ∑ i ∈ R, volume (Z i).shade) :=
          mul_le_mul_right (mul_le_mul_left hbin _) 2
      _ = loss * ∑ i ∈ R, volume (Z i).shade := by rw [mul_assoc]
  have hfullness : ShadedBody.fullness' S (fun i => (Z i).toShadedBody) <=
      loss * ShadedBody.fullness' R (fun i => (Z i).toShadedBody) := by
    change (∑ i ∈ S, volume (Z i).shade) / (∑ i ∈ S, volume (Z i).carrier) <=
      loss * ((∑ i ∈ R, volume (Z i).shade) / (∑ i ∈ R, volume (Z i).carrier))
    calc (∑ i ∈ S, volume (Z i).shade) / (∑ i ∈ S, volume (Z i).carrier) <=
          (loss * ∑ i ∈ R, volume (Z i).shade) / (∑ i ∈ S, volume (Z i).carrier) :=
            ENNReal.div_le_div_right hmass _
      _ = loss * ((∑ i ∈ R, volume (Z i).shade) / (∑ i ∈ S, volume (Z i).carrier)) := mul_div_assoc _ _ _
      _ <= loss * ((∑ i ∈ R, volume (Z i).shade) / (∑ i ∈ R, volume (Z i).carrier)) := by
            apply mul_le_mul_right
            exact ENNReal.div_le_div_left
              (Finset.sum_le_sum_of_subset_of_nonneg hRS (fun _ _ _ => zero_le)) _
  have hsmall : loss <= (delta : ENNReal) ^ (-eta0) := (hKbound delta hdelta hdelta1).trans hlossδ
  have hfullfloor : ENNReal.ofReal ((delta : Real) ^ (3 * eta0)) <=
      ShadedBody.fullness' R (fun i => (Z i).toShadedBody) := by
    rw [hepow]
    calc (delta : ENNReal) ^ (3 * eta0) = (delta : ENNReal) ^ eta0 * (delta : ENNReal) ^ (2 * eta0) := by
          rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
          congr 1
          ring
      _ <= (delta : ENNReal) ^ eta0 * (loss * ShadedBody.fullness' R (fun i => (Z i).toShadedBody)) :=
          mul_le_mul_right (((hepow (2 * eta0)) ▸ hfull).trans hfullness) _
      _ <= (delta : ENNReal) ^ eta0 * ((delta : ENNReal) ^ (-eta0) *
          ShadedBody.fullness' R (fun i => (Z i).toShadedBody)) := mul_le_mul_right (mul_le_mul_left hsmall _) _
      _ = ShadedBody.fullness' R (fun i => (Z i).toShadedBody) := by
          rw [← mul_assoc, ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
          simp
  refine ⟨R, Q', hrest, hQ', hstats, {
    subset := hRS
    nonempty := hRne
    original_subset := hS
    original_tubes := hZT
    mass := hmass
    multiplicity := ?_
    fullness := hfullness
    fullness_floor := hfullfloor
    density := ?_
    leaf_mass_floor := ?_
    shade_in_carrier := ?_
    source_potential := source_assignedPotential_mono Q hRS hh hdelta
      (hdeltaBound.trans_le hdelta01) }, hKbound delta hdelta hdelta1⟩
  · apply ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset S
      (fun i => (Z i).toShadedBody) R (fun i => (Z i).toShadedBody) loss _ hmass
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨i, hRS hi, hxi⟩
  · have hdens := (Kakeya.maxDensity_mono (fun i => (T i).toConvexSpaceBody) (hRS.trans hS)).trans
      hQ.maximal_density
    have heq : (fun i => (Z i).toConvexSpaceBody) = (fun i => (T i).toConvexSpaceBody) := by
      funext i
      exact congrArg Tube.toConvexSpaceBody (hZT i)
    rw [heq]
    exact hdens
  · intro i hi
    have hh' := hfloor i (hRS1 hi)
    change m * (volume (Z i).toTube.carrier) <= volume (Z i).shade at hh'
    simpa only [hZT i] using hh'
  · intro i hi
    have hs := (Z i).shade_subset
    change (Z i).shade <= (Z i).toTube.carrier at hs
    simpa only [hZT i] using hs

/-- Source all-leaf mass regularity gives the caller's dense/comparable scalar rows.
The extra factor two is displayed rather than folded invisibly into lambda. -/
theorem source_dense_comparable_of_fixed_statistics
    {iota : Type u} {delta : NNReal} {R : Finset iota}
    {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
    (Q : SourceThreadedTower R T M C)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3)))
    (hdelta : 0 < delta) (hR : R.Nonempty) (hstats : SourceTowerStatistics Q Z)
    (hmass : 0 < ∑ i ∈ R, volume (Z i).shade) :
    0 < ShadedBody.fullness R (fun i => (Z i).toShadedBody) / 2 /\
    ML2Shaded.HasDenseShading
      (ShadedBody.fullness R (fun i => (Z i).toShadedBody) / 2) R
      (fun i => (Z i).toShadedBody) /\
    ML2Shaded.HasComparableDensities 2 R (fun i => (Z i).toShadedBody) := by
  classical
  have hcell (j : iota) (hj : j ∈ R) : Q.cell M j = {j} := by
    ext i
    simp only [SourceThreadedTower.cell, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hi, hij⟩
      simpa only [Q.bottom_place i hi] using hij
    · intro hij
      subst i
      exact ⟨hj, Q.bottom_place j hj⟩
  have hleaf (i : iota) (hi : i ∈ R) (j : iota) (hj : j ∈ R) :
      volume (Z i).shade <= 2 * volume (Z j).shade := by
    have hi' : i ∈ Q.indexSet M := Q.bottom_index.symm ▸ hi
    have hj' : j ∈ Q.indexSet M := Q.bottom_index.symm ▸ hj
    simpa only [hcell i hi, hcell j hj, Finset.sum_singleton] using
      hstats.fibre_mass M (le_refl M) i hi' j hj'
  have hcomp : ML2Shaded.HasComparableDensities 2 R
      (fun i => (Z i).toShadedBody) := by
    intro i hi j hj
    have hvol := Tube.volume_carrier_eq_volume_carrier (Z i).toTube (Z j).toTube
    change volume (Z i).shade * volume (Z j).carrier <=
      (2 : ENNReal) * (volume (Z j).shade * volume (Z i).carrier)
    rw [hvol, ← mul_assoc]
    exact mul_le_mul_left (hleaf i hi j hj) _
  have hD0 : (∑ i ∈ R, volume (Z i).carrier) ≠ 0 := by
    obtain ⟨i, hi⟩ := hR
    intro hzero
    exact ML2Shaded.volume_carrier_ne_zero hdelta (Z i).toTube
      (Finset.sum_eq_zero_iff.mp hzero i hi)
  have hDtop : (∑ i ∈ R, volume (Z i).carrier) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i _ => ML2Shaded.volume_carrier_ne_top (Z i).toTube)
  refine ⟨div_pos (ML2Shaded.fullness_pos_of_sum_shade_ne_zero hmass.ne' hDtop)
    (by norm_num), ?_, hcomp⟩
  intro i hi
  have hsum : (∑ j ∈ R, volume (Z j).shade) * volume (Z i).carrier <=
      (2 * volume (Z i).shade) * ∑ j ∈ R, volume (Z j).carrier := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj => by
      simpa only [mul_assoc, ENNReal.coe_two] using hcomp j hj i hi
  have hbound : ShadedBody.fullness' R (fun j => (Z j).toShadedBody) *
      volume (Z i).carrier <= 2 * volume (Z i).shade := by
    apply (ENNReal.mul_le_mul_iff_left hD0 hDtop).mp
    calc (ShadedBody.fullness' R (fun j => (Z j).toShadedBody) *
          volume (Z i).carrier) * ∑ j ∈ R, volume (Z j).carrier =
          ((ShadedBody.fullness R (fun j => (Z j).toShadedBody) : NNReal) : ENNReal) *
            (∑ j ∈ R, volume (Z j).carrier) * volume (Z i).carrier := by
              rw [ShadedBody.coe_fullness]
              ac_rfl
      _ = (∑ j ∈ R, volume (Z j).shade) * volume (Z i).carrier := by
            rw [← ShadedBody.sum_volumeReal_shade_eq_fullness_mul R
              (fun j => (Z j).toShadedBody)]
      _ <= (2 * volume (Z i).shade) * ∑ j ∈ R, volume (Z j).carrier := hsum
  change (((ShadedBody.fullness R (fun j => (Z j).toShadedBody) / 2 : NNReal) : ENNReal) *
    volume (Z i).carrier) <= volume (Z i).shade
  rw [ENNReal.coe_div (by norm_num), ENNReal.coe_two, ShadedBody.coe_fullness,
    div_eq_mul_inv]
  calc ShadedBody.fullness' R (fun j => (Z j).toShadedBody) * (2 : ENNReal)⁻¹ *
      volume (Z i).carrier =
      (2 : ENNReal)⁻¹ * (ShadedBody.fullness' R (fun j => (Z j).toShadedBody) *
        volume (Z i).carrier) := by ac_rfl
    _ <= (2 : ENNReal)⁻¹ * (2 * volume (Z i).shade) := mul_le_mul_right hbound _
    _ = volume (Z i).shade := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

end Kakeya.ML2Core
