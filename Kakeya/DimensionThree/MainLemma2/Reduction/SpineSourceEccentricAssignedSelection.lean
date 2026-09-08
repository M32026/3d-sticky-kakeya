/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceEccentricNormalizationData
public import Kakeya.Tube.EssentiallyDistinctShadeSelection

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- One actual fine ED/count selection, with its genuine occupied parents and
the retained fractions in every kept old factor. These are private terminal
restrictions; no inherited Q statistics are claimed for the selected leaves. -/
structure SourceEccentricAssignedSelection (Q : SourceThreadedTower S T M C)
    {Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
    {a m : Nat} {Lout : NNReal} (O : SourceEccentricOuterSplit Q Z a Lout)
    {Rnorm : Real} {Cgeom cParent : NNReal}
    (Nrm : SourceEccentricCellNormalization Q O m Rnorm Cgeom cParent)
    {etaParent bias : Real} {D aw bw cw : NNReal}
    (E : SourceZeroEccentricFactors Q Z a m etaParent bias D aw bw cw)
    (Lsel Ccount : NNReal) where
  edLeaves : Finset iota
  ed_subset : edLeaves <= Q.cell a O.chosen
  ed_pairwise : (edLeaves : Set iota).Pairwise
    (fun i j => _root_.IsEssentiallyDistinct (Nrm.fine i).carrier (Nrm.fine j).carrier)
  ed_mass_price : (∑ i ∈ Q.cell a O.chosen, volume (Nrm.fine i).shade) <=
    (1 + Tube.refineToEssDistinctLeaves.C 3 *
      Kakeya.maxDensity (Q.cell a O.chosen) (fun i => (Nrm.fine i).toConvexSpaceBody)) *
      ∑ i ∈ edLeaves, volume (Nrm.fine i).shade
  leaves : Finset iota
  leaves_subset_ed : leaves <= edLeaves
  leaves_subset : leaves <= Q.cell a O.chosen
  leaves_nonempty : leaves.Nonempty
  shading : iota -> ShadedTube (sourceEccentricFineScale delta M a) (EuclideanSpace Real (Fin 3))
  same_tubes : forall i, (shading i).toTube = (Nrm.fine i).toTube
  subshade : forall i, (shading i).shade <= (Nrm.fine i).shade
  essentially_distinct : (leaves : Set iota).Pairwise
    (fun i j => _root_.IsEssentiallyDistinct (shading i).carrier (shading j).carrier)
  refinement : ShadedBody.IsCRefinement leaves (fun i => (shading i).toShadedBody)
    (Q.cell a O.chosen) (fun i => (Nrm.fine i).toShadedBody) Lsel⁻¹
  mass : (∑ i ∈ Q.cell a O.chosen, volume (Nrm.fine i).shade) <=
    (Lsel : ENNReal) * ∑ i ∈ leaves, volume (shading i).shade
  union_subset : (⋃ i ∈ leaves, (shading i).shade) <=
    ⋃ i ∈ Q.cell a O.chosen, (Nrm.fine i).shade
  fullness : ShadedBody.fullness (Q.cell a O.chosen) (fun i => (Nrm.fine i).toShadedBody) / Lsel <=
    ShadedBody.fullness leaves (fun i => (shading i).toShadedBody)
  multiplicity : ShadedBody.multiplicity (Q.cell a O.chosen) (fun i => (Nrm.fine i).toShadedBody) <=
    (Lsel : ENNReal) * ShadedBody.multiplicity leaves (fun i => (shading i).toShadedBody)
  parents : Finset iota
  parents_eq : parents = leaves.image (Q.place m)
  parents_subset : parents <= Q.fibre a m O.chosen
  parents_nonempty : parents.Nonempty
  parent_ball : forall k, k ∈ parents -> (Nrm.parent k).carrier <= Metric.closedBall 0 1
  n : NNReal
  Cfib : NNReal
  n_positive : 0 < n
  Cfib_one : 1 <= Cfib
  Cfib_bound : Cfib <= Ccount
  fibre_nonempty : forall k, k ∈ parents ->
    (leaves.filter (fun i => Q.place m i = k)).Nonempty
  fibre_lower : forall k, k ∈ parents ->
    n / Cfib <= ((leaves.filter (fun i => Q.place m i = k)).card : NNReal)
  fibre_upper : forall k, k ∈ parents ->
    ((leaves.filter (fun i => Q.place m i = k)).card : NNReal) <= Cfib * n
  keptParts : Finset (Finset iota)
  kept_parts_subset : keptParts <= (E.factor O.chosen (O.outer_subset O.chosen_mem)).parts
  kept_parts_nonempty : keptParts.Nonempty
  kept_intersection_nonempty : forall part, part ∈ keptParts -> (part ∩ parents).Nonempty
  kept_cover : keptParts.biUnion (fun part => part ∩ parents) = parents
  partRetention : NNReal
  part_retention_one : 1 <= partRetention
  part_retention_bound : partRetention <= Lsel
  part_card_retention : forall part, part ∈ keptParts ->
    (part.card : NNReal) <= partRetention * ((part ∩ parents).card : NNReal)
  part_volume_retention : forall part, part ∈ keptParts ->
    (∑ k ∈ part, volume (Q.tube m k).carrier) <=
      (partRetention : ENNReal) * ∑ k ∈ part ∩ parents, volume (Q.tube m k).carrier
  part_mass_retention : forall part, part ∈ keptParts ->
    (∑ i ∈ (Q.cell a O.chosen).filter (fun i => Q.place m i ∈ part),
      volume (Nrm.fine i).shade) <=
      (Lsel : ENNReal) * ∑ i ∈ leaves.filter (fun i => Q.place m i ∈ part), volume (shading i).shade

/-- Actual ED, comparable assigned counts, full shaded mass and per-old-part
retention are constructed together. No one of these output rows is an added
premise of the final raw estimate. The cutoff is uniform in the later bias. -/
theorem source_exists_eccentric_ED_assigned_refinement
    (M : Nat) (hM : 2 <= M) (Rnorm : Real) (hR : 64 <= Rnorm)
    (Cgeom cParent : NNReal) (hC : 1 <= Cgeom) (hc : 1 <= cParent)
    (D : NNReal) (hD : 1 <= D) (Kout : Nat) (hKout : 1 <= Kout) :
    exists (A : NNReal) (p K : Nat), Cgeom <= A /\ 1 <= A /\ 1 <= p /\ Kout <= K /\
      forall etaPlank zeta etaParent : Real, 0 < etaPlank -> etaPlank <= 1 ->
      0 < zeta -> 0 < etaParent ->
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall bias : Real, 0 < bias -> bias <= min (etaParent / 16) (etaPlank / 8) ->
        forall {iota : Type u} (S : Finset iota)
          (T : iota -> Tube delta (EuclideanSpace Real (Fin 3)))
          (Q : SourceThreadedTower S T M sourceThreadConstant)
          (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
        SourceFixedTowerInput Q sourceBottomED sourceLevelED etaPlank ->
        SourceTowerStatistics Q Z ->
        delta ^ etaPlank <= ShadedBody.fullness S (fun i => (Z i).toShadedBody) ->
        forall (a m : Nat) (aw bw cw : NNReal), m < M ->
        forall (O : SourceEccentricOuterSplit Q Z a (sourceEccentricLogLoss Kout delta))
          (Nrm : SourceEccentricCellNormalization Q O m Rnorm Cgeom cParent)
          (E : SourceZeroEccentricFactors Q Z a m etaParent bias D aw bw cw),
        Nonempty (SourceEccentricAssignedSelection Q O Nrm E
          (sourceEccentricSelectionCost A p K delta etaPlank zeta)
          (A * delta ^ (-(p : Real) * zeta))) := by
  set_option maxHeartbeats 2000000 in
  classical
  have hbin {iota : Type u} {kappa : Type u} (s : Finset iota) (assign : iota -> kappa)
      (w : iota -> ENNReal) (hmass : 0 < ∑ i ∈ s, w i) :
      exists r : Finset kappa, r <= s.image assign /\ r.Nonempty /\
        (∑ i ∈ s, w i) <= ENNReal.ofReal (1 + Real.logb 2 (s.card : Real)) *
          ∑ i ∈ s.filter (fun i => assign i ∈ r), w i /\
        exists n : NNReal, 0 < n /\ forall k, k ∈ r ->
          n / 2 <= (((s.filter (fun i => assign i ∈ r)).filter
            (fun i => assign i = k)).card : NNReal) /\
          (((s.filter (fun i => assign i ∈ r)).filter
            (fun i => assign i = k)).card : NNReal) <= 2 * n := by
    classical
    let fibre := fun k => s.filter (fun i => assign i = k)
    have hne : s.Nonempty := by
      by_contra h
      simp [Finset.not_nonempty_iff_eq_empty.mp h] at hmass
    have hrange : forall k, k ∈ s.image assign ->
        ((fibre k).card : ENNReal) ∈ Set.Icc (1 : ENNReal) (s.card : ENNReal) := by
      intro k hk
      obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hk
      have hpos : 0 < (fibre k).card := Finset.card_pos.mpr
        ⟨i, Finset.mem_filter.mpr ⟨hi, hik⟩⟩
      constructor
      · exact_mod_cast Nat.one_le_iff_ne_zero.mpr hpos.ne'
      · exact_mod_cast Finset.card_le_card (Finset.filter_subset _ s)
    obtain ⟨r, hrs, hrmass, hrcompare⟩ := ENNReal.dyadic_pigeonhole₁
      (s.image assign) (fun k => ∑ i ∈ fibre k, w i) (fun k => ((fibre k).card : ENNReal))
      (a := 1) (b := s.card) (by norm_num) (by exact_mod_cast hne.card_pos) (by
        simpa using hrange)
    have hsum : (∑ k ∈ s.image assign, ∑ i ∈ fibre k, w i) = ∑ i ∈ s, w i := by
      exact Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem assign hi) w
    have hselected : (∑ k ∈ r, ∑ i ∈ fibre k, w i) =
        ∑ i ∈ s.filter (fun i => assign i ∈ r), w i := by
      exact Finset.sum_fiberwise_eq_sum_filter s r assign w
    rw [hsum, hselected] at hrmass
    simp only [div_one] at hrmass
    have hrne : r.Nonempty := by
      by_contra h
      simp only [Finset.not_nonempty_iff_eq_empty.mp h, Finset.notMem_empty,
        Finset.filter_false, Finset.sum_empty, mul_zero] at hrmass
      exact (not_le_of_gt hmass) hrmass
    obtain ⟨k0, hk0⟩ := hrne
    refine ⟨r, hrs, ⟨k0, hk0⟩, hrmass, ((fibre k0).card : NNReal), ?_, ?_⟩
    · have h := (hrange k0 (hrs hk0)).1
      exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) h
    · intro k hk
      have heq : (s.filter (fun i => assign i ∈ r)).filter (fun i => assign i = k) =
          fibre k := by
        ext i
        simp only [Finset.mem_filter, fibre]
        aesop
      rw [heq]
      constructor
      · apply (div_le_iff₀ (by norm_num : (0 : NNReal) < 2)).mpr
        have h := hrcompare k0 hk0 k hk
        have hn : ((fibre k0).card : NNReal) <= 2 * ((fibre k).card : NNReal) := by
          exact_mod_cast h
        simpa only [mul_comm] using hn
      · exact_mod_cast hrcompare k hk k0 hk0
  have hcore {iota : Type u} {delta : NNReal} {S : Finset iota}
      {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
      (Q : SourceThreadedTower S T M C)
      {Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
      {a m : Nat} {Lout : NNReal} (O : SourceEccentricOuterSplit Q Z a Lout)
      {Rnorm : Real} {Cgeom cParent : NNReal}
      (Nrm : SourceEccentricCellNormalization Q O m Rnorm Cgeom cParent)
      {etaParent bias : Real} {D aw bw cw : NNReal}
      (E : SourceZeroEccentricFactors Q Z a m etaParent bias D aw bw cw)
      (hstats : SourceTowerStatistics Q Z)
      (ed q0 : Finset iota) (heds : ed <= Q.cell a O.chosen) (hq0ed : q0 <= ed)
      (hed : (ed : Set iota).Pairwise (fun i j =>
        _root_.IsEssentiallyDistinct (Nrm.fine i).carrier (Nrm.fine j).carrier))
      (hedmass : (∑ i ∈ Q.cell a O.chosen, volume (Nrm.fine i).shade) <=
        (1 + Tube.refineToEssDistinctLeaves.C 3 *
          Kakeya.maxDensity (Q.cell a O.chosen) (fun i => (Nrm.fine i).toConvexSpaceBody)) *
          ∑ i ∈ ed, volume (Nrm.fine i).shade)
      (n L Ccount : NNReal) (hn : 0 < n) (hL : 1 <= L) (hCcount : 2 <= Ccount)
      (hcounts : forall k, k ∈ q0.image (Q.place m) ->
        n / 2 <= ((q0.filter (fun i => Q.place m i = k)).card : NNReal) /\
        ((q0.filter (fun i => Q.place m i = k)).card : NNReal) <= 2 * n)
      (hbudget : 4 * (∑ i ∈ Q.cell a O.chosen, volume (Nrm.fine i).carrier) <=
        (L : ENNReal) * ∑ i ∈ q0, volume (Nrm.fine i).shade) :
      Nonempty (SourceEccentricAssignedSelection Q O Nrm E L Ccount) := by
    classical
    have hcross {iota : Type u} {kappa : Type u} (s q : Finset iota) (assign : iota -> kappa)
        (hqs : q <= s) (part : Finset kappa)
        (hcounts : forall k, k ∈ part -> forall l, l ∈ part ->
          ((s.filter (fun i => assign i = k)).card : ENNReal) <=
            2 * ((s.filter (fun i => assign i = l)).card : ENNReal)) :
        (part.card : ENNReal) * ((q.filter (fun i => assign i ∈ part)).card : ENNReal) <=
          2 * ((part ∩ q.image assign).card : ENNReal) *
            ((s.filter (fun i => assign i ∈ part)).card : ENNReal) := by
      classical
      let r := part ∩ q.image assign
      have hqsum : ((q.filter (fun i => assign i ∈ part)).card : ENNReal) =
          ∑ k ∈ r, ((q.filter (fun i => assign i = k)).card : ENNReal) := by
        have heq : q.filter (fun i => assign i ∈ part) = q.filter (fun i => assign i ∈ r) := by
          ext i
          simp only [Finset.mem_filter, r, Finset.mem_inter]
          constructor
          · rintro ⟨hi, hp⟩
            exact ⟨hi, hp, Finset.mem_image_of_mem _ hi⟩
          · rintro ⟨hi, hp, _⟩
            exact ⟨hi, hp⟩
        rw [heq]
        simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
          (Finset.sum_fiberwise_eq_sum_filter q r assign (fun _ => (1 : ENNReal))).symm
      have hssum : ((s.filter (fun i => assign i ∈ part)).card : ENNReal) =
          ∑ k ∈ part, ((s.filter (fun i => assign i = k)).card : ENNReal) := by
        simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
          (Finset.sum_fiberwise_eq_sum_filter s part assign (fun _ => (1 : ENNReal))).symm
      have hfibre : forall k, ((q.filter (fun i => assign i = k)).card : ENNReal) <=
          ((s.filter (fun i => assign i = k)).card : ENNReal) := by
        intro k
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hqs)
      rw [hqsum, hssum]
      calc
        (part.card : ENNReal) * ∑ k ∈ r, ((q.filter (fun i => assign i = k)).card : ENNReal) =
            ∑ l ∈ part, ∑ k ∈ r, ((q.filter (fun i => assign i = k)).card : ENNReal) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ <= ∑ l ∈ part, ∑ k ∈ r,
            2 * ((s.filter (fun i => assign i = l)).card : ENNReal) := by
          apply Finset.sum_le_sum
          intro l hl
          apply Finset.sum_le_sum
          intro k hk
          exact (hfibre k).trans (hcounts k (Finset.mem_inter.mp hk).1 l hl)
        _ = 2 * ((part ∩ q.image assign).card : ENNReal) *
            ∑ l ∈ part, ((s.filter (fun i => assign i = l)).card : ENNReal) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          change (r.card : ENNReal) * (2 * _) = 2 * (r.card : ENNReal) * _
          ring

    have hparts {iota : Type u} {kappa : Type u} [DecidableEq kappa]
        (q : Finset iota) (r : Finset kappa) (assign : iota -> kappa)
        (hassign : forall i, i ∈ q -> assign i ∈ r) (F : Finpartition r)
        (w : iota -> ENNReal) (v : kappa -> ENNReal) (t c : ENNReal)
        (hc : 0 < c) (hmass : 0 < ∑ i ∈ q, w i)
        (hfin : t * ∑ k ∈ r, v k ≠ ⊤)
        (hbudget : c * (∑ i ∈ q, w i) + t * ∑ k ∈ r, v k <= ∑ i ∈ q, w i) :
        exists g : Finset (Finset kappa), g <= F.parts /\ g.Nonempty /\
          c * (∑ i ∈ q, w i) <= ∑ i ∈ q.filter (fun i => assign i ∈ g.biUnion id), w i /\
          forall part, part ∈ g ->
            t * (∑ k ∈ part, v k) <=
              ∑ i ∈ (q.filter (fun i => assign i ∈ g.biUnion id)).filter
                (fun i => assign i ∈ part), w i := by
      classical
      let wp := fun part : Finset kappa => ∑ i ∈ q.filter (fun i => assign i ∈ part), w i
      let vp := fun part : Finset kappa => ∑ k ∈ part, v k
      let g := F.parts.filter (fun part => t * vp part <= wp part)
      have hgp : g <= F.parts := Finset.filter_subset _ _
      have hpSum (part : Finset kappa) : wp part =
          ∑ k ∈ part, ∑ i ∈ q.filter (fun i => assign i = k), w i :=
        (Finset.sum_fiberwise_eq_sum_filter q part assign w).symm
      have htotalW : (∑ part ∈ F.parts, wp part) = ∑ i ∈ q, w i := by
        simp_rw [hpSum]
        rw [← F.sum_eq_sum_parts_sum]
        exact Finset.sum_fiberwise_of_maps_to hassign w
      have htotalV : (∑ part ∈ F.parts, vp part) = ∑ k ∈ r, v k :=
        (F.sum_eq_sum_parts_sum v).symm
      have hselectedW : (∑ part ∈ g, wp part) =
          ∑ i ∈ q.filter (fun i => assign i ∈ g.biUnion id), w i := by
        simp_rw [hpSum]
        calc
          _ = ∑ k ∈ g.biUnion id, ∑ i ∈ q.filter (fun i => assign i = k), w i := by
            simpa using (Finset.sum_biUnion (F.disjoint.subset hgp)
              (f := fun k => ∑ i ∈ q.filter (fun i => assign i = k), w i)).symm
          _ = _ := Finset.sum_fiberwise_eq_sum_filter q (g.biUnion id) assign w
      have hsplit : (∑ part ∈ F.parts, wp part) <=
          (∑ part ∈ g, wp part) + t * ∑ part ∈ F.parts, vp part := by
        rw [← Finset.sum_filter_add_sum_filter_not F.parts (fun part => t * vp part <= wp part) wp]
        gcongr
        calc
          (∑ part ∈ F.parts.filter (fun part => ¬ t * vp part <= wp part), wp part) <=
              ∑ part ∈ F.parts.filter (fun part => ¬ t * vp part <= wp part), t * vp part := by
            exact Finset.sum_le_sum fun part hp =>
              le_of_lt (not_le.mp (Finset.mem_filter.mp hp).2)
          _ = t * ∑ part ∈ F.parts.filter (fun part => ¬ t * vp part <= wp part), vp part := by
            rw [Finset.mul_sum]
          _ <= t * ∑ part ∈ F.parts, vp part :=
            mul_le_mul_right (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)) t
      rw [htotalW, htotalV] at hsplit
      have hkeep : c * (∑ i ∈ q, w i) <= ∑ part ∈ g, wp part :=
        ENNReal.le_of_add_le_add_right hfin (hbudget.trans hsplit)
      have hgne : g.Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hkeep
        exact (not_le_of_gt (ENNReal.mul_pos hc.ne' hmass.ne')) hkeep
      refine ⟨g, hgp, hgne, hselectedW ▸ hkeep, ?_⟩
      intro part hp
      have heq : (q.filter (fun i => assign i ∈ g.biUnion id)).filter
          (fun i => assign i ∈ part) = q.filter (fun i => assign i ∈ part) := by
        ext i
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hi, _⟩, hp⟩
          exact ⟨hi, hp⟩
        · rintro ⟨hi, hip⟩
          exact ⟨⟨hi, Finset.mem_biUnion.mpr ⟨part, hp, hip⟩⟩, hip⟩
      rw [heq]
      exact (Finset.mem_filter.mp hp).2

    have hpaid (A B P R t L : NNReal) (V mass : ENNReal)
        (hA : 0 < A) (hV : V ≠ 0) (hVfin : V ≠ ⊤)
        (hlow : (t : ENNReal) * (V * (A : ENNReal)) <= mass)
        (hupp : mass <= V * (B : ENNReal))
        (hcard : P * B <= 2 * R * A) (hLt : 2 <= L * t) : P <= L * R := by
      have hVA : V * (A : ENNReal) ≠ 0 :=
        mul_ne_zero hV (ENNReal.coe_ne_zero.mpr hA.ne')
      have hVAfin : V * (A : ENNReal) ≠ ⊤ :=
        ENNReal.mul_ne_top hVfin ENNReal.coe_ne_top
      have hscaled : ((t : ENNReal) * (P : ENNReal)) * (V * (A : ENNReal)) <=
          (2 * (R : ENNReal)) * (V * (A : ENNReal)) := by
        calc
          ((t : ENNReal) * (P : ENNReal)) * (V * (A : ENNReal)) =
              ((t : ENNReal) * (V * (A : ENNReal))) * (P : ENNReal) := by ring
          _ <= mass * (P : ENNReal) := mul_le_mul_left hlow _
          _ <= (V * (B : ENNReal)) * (P : ENNReal) := mul_le_mul_left hupp _
          _ = V * ((P : ENNReal) * (B : ENNReal)) := by ring
          _ <= V * (2 * (R : ENNReal) * (A : ENNReal)) :=
            mul_le_mul_right (by exact_mod_cast hcard) V
          _ = (2 * (R : ENNReal)) * (V * (A : ENNReal)) := by ring
      have hpaid : t * P <= 2 * R := by
        exact_mod_cast (ENNReal.mul_le_mul_iff_left hVA hVAfin).mp hscaled
      have hfinal : 2 * P <= 2 * (L * R) := by
        calc
          2 * P <= (L * t) * P := mul_le_mul_left hLt P
          _ = L * (t * P) := by ring
          _ <= L * (2 * R) := mul_le_mul_right hpaid L
          _ = 2 * (L * R) := by ring
      exact (mul_le_mul_iff_right₀ (by norm_num : (0 : NNReal) < 2)).mp hfinal
    let s := Q.cell a O.chosen
    let assign := Q.place m
    let r := Q.fibre a m O.chosen
    let F := (E.factor O.chosen (O.outer_subset O.chosen_mem)).toFinpartition
    let w := fun i => volume (Nrm.fine i).shade
    let v := fun k => ∑ i ∈ s.filter (fun i => assign i = k), volume (Nrm.fine i).carrier
    let t : NNReal := 2 / L
    have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
    have htpos : 0 < t := div_pos (by norm_num) hLpos
    have hLt : L * t = 2 := by
      dsimp [t]
      rw [← mul_div_assoc]
      exact (div_eq_iff hLpos.ne').mpr (mul_comm L 2)
    have hq0s : q0 <= s := hq0ed.trans heds
    have has : forall i, i ∈ s -> assign i ∈ r :=
      fun i hi => Finset.mem_image_of_mem _ hi
    have haq : forall i, i ∈ q0 -> assign i ∈ r := fun i hi => has i (hq0s hi)
    have hsumv : (∑ k ∈ r, v k) = ∑ i ∈ s, volume (Nrm.fine i).carrier :=
      Finset.sum_fiberwise_of_maps_to has _
    obtain ⟨i0, hi0⟩ := O.chosen_cell_nonempty
    have hsigma1 : sourceEccentricFineScale delta M a <= 1 := by
      exact_mod_cast Nrm.fine_situation.out_le_quarter.trans (by norm_num : (1 / 4 : Real) <= 1)
    let V := volume (Nrm.fine i0).carrier
    have hVpos : 0 < V :=
      (Tube.volume_pos_and_lt_top Nrm.fine_pos hsigma1 (Nrm.fine i0).toTube).1
    have hVfin : V ≠ ⊤ := (Nrm.fine i0).isCompact.measure_ne_top
    have hvol (i : iota) : volume (Nrm.fine i).carrier = V :=
      Tube.volume_carrier_eq_volume_carrier (Nrm.fine i).toTube (Nrm.fine i0).toTube
    have hcarrier : 0 < ∑ i ∈ s, volume (Nrm.fine i).carrier := by
      exact lt_of_lt_of_le (hvol i0 ▸ hVpos) (Finset.single_le_sum (fun _ _ => zero_le) hi0)
    have hcarfin : (∑ i ∈ s, volume (Nrm.fine i).carrier) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr fun i _ => (Nrm.fine i).isCompact.measure_ne_top
    have hqmass : 0 < ∑ i ∈ q0, w i := by
      by_contra h
      have hz := le_antisymm (le_of_not_gt h) zero_le
      change (∑ i ∈ q0, volume (Nrm.fine i).shade) = 0 at hz
      rw [hz, mul_zero] at hbudget
      exact (not_le_of_gt (ENNReal.mul_pos (by norm_num) hcarrier.ne')) hbudget
    have hhalfFour : (1 / 2 : ENNReal) * 4 = 2 := by
      rw [one_div, show (4 : ENNReal) = 2 * 2 by norm_num, ← mul_assoc,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
    have hhalfAdd : (1 / 2 : ENNReal) + 1 / 2 = 1 := by
      simpa only [one_div] using ENNReal.inv_two_add_inv_two
    have hsmall : (t : ENNReal) * ∑ k ∈ r, v k <= (1 / 2 : ENNReal) * ∑ i ∈ q0, w i := by
      rw [hsumv]
      have hL0 : (L : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hLpos.ne'
      apply (ENNReal.mul_le_mul_iff_right hL0 ENNReal.coe_ne_top).mp
      calc
        (L : ENNReal) * ((t : ENNReal) * ∑ i ∈ s, volume (Nrm.fine i).carrier) =
            2 * ∑ i ∈ s, volume (Nrm.fine i).carrier := by
          rw [← mul_assoc, ← ENNReal.coe_mul, hLt]
          norm_num
        _ = (1 / 2 : ENNReal) * (4 * ∑ i ∈ s, volume (Nrm.fine i).carrier) := by
          rw [← mul_assoc, hhalfFour]
        _ <= (1 / 2 : ENNReal) * ((L : ENNReal) * ∑ i ∈ q0, w i) :=
          mul_le_mul_right hbudget _
        _ = (L : ENNReal) * ((1 / 2 : ENNReal) * ∑ i ∈ q0, w i) := by ring
    have hhalf : (1 / 2 : ENNReal) * (∑ i ∈ q0, w i) +
        (t : ENNReal) * ∑ k ∈ r, v k <= ∑ i ∈ q0, w i := by
      calc
        _ <= (1 / 2 : ENNReal) * (∑ i ∈ q0, w i) +
            (1 / 2 : ENNReal) * (∑ i ∈ q0, w i) := add_le_add_right hsmall _
        _ = ∑ i ∈ q0, w i := by rw [← add_mul, hhalfAdd, one_mul]
    obtain ⟨g, hgp, hgne, hkeep, hgpart⟩ := hparts q0 r assign haq F w v
      (t : ENNReal) (1 / 2) (by norm_num) hqmass
      (by rw [hsumv]; exact ENNReal.mul_ne_top ENNReal.coe_ne_top hcarfin) hhalf
    let q := q0.filter (fun i => assign i ∈ g.biUnion id)
    let parents := q.image assign
    have hqq0 : q <= q0 := Finset.filter_subset _ _
    have hqs : q <= s := hqq0.trans hq0s
    have hqmasspos : 0 < ∑ i ∈ q, w i :=
      (ENNReal.mul_pos (by norm_num) hqmass.ne').trans_le hkeep
    have hqne : q.Nonempty := by
      by_contra h
      simp [Finset.not_nonempty_iff_eq_empty.mp h] at hqmasspos
    have hparentne : parents.Nonempty := hqne.image _
    have hparentr : parents <= r := Finset.image_subset_iff.mpr fun i hi => has i (hqs hi)
    have hparent0 : parents <= q0.image assign := Finset.image_subset_image hqq0
    have hfibre (k : iota) (hk : k ∈ parents) :
        q.filter (fun i => assign i = k) = q0.filter (fun i => assign i = k) := by
      obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp hk
      have hkg : k ∈ g.biUnion id := hjk ▸ (Finset.mem_filter.mp hj).2
      ext i
      simp only [q, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hi, _⟩, heq⟩
        exact ⟨hi, heq⟩
      · rintro ⟨hi, heq⟩
        exact ⟨⟨hi, heq ▸ hkg⟩, heq⟩
    have hmass : (∑ i ∈ s, volume (Nrm.fine i).shade) <=
        (L : ENNReal) * ∑ i ∈ q, volume (Nrm.fine i).shade := by
      calc
        _ <= ∑ i ∈ s, volume (Nrm.fine i).carrier :=
          Finset.sum_le_sum fun i _ => measure_mono (Nrm.fine i).shade_subset
        _ <= 2 * ∑ i ∈ s, volume (Nrm.fine i).carrier := by
          simpa only [one_mul] using mul_le_mul_left
            (by norm_num : (1 : ENNReal) <= 2) (∑ i ∈ s, volume (Nrm.fine i).carrier)
        _ = (1 / 2 : ENNReal) * (4 * ∑ i ∈ s, volume (Nrm.fine i).carrier) := by
          rw [← mul_assoc, hhalfFour]
        _ <= (1 / 2 : ENNReal) * ((L : ENNReal) * ∑ i ∈ q0, w i) :=
          mul_le_mul_right hbudget _
        _ = (L : ENNReal) * ((1 / 2 : ENNReal) * ∑ i ∈ q0, w i) := by ring
        _ <= (L : ENNReal) * ∑ i ∈ q, w i := mul_le_mul_right hkeep _
    have href : ShadedBody.IsCRefinement q (fun i => (Nrm.fine i).toShadedBody)
        s (fun i => (Nrm.fine i).toShadedBody) L⁻¹ :=
      ShadedBody.isCRefinement_of_isRefinement_of_sum_le _ _ _ _
        ⟨hqs, fun _ _ => ⟨rfl, le_rfl⟩⟩ hmass
    have hvpart (part : Finset iota) : (∑ k ∈ part, v k) =
        V * ((s.filter (fun i => assign i ∈ part)).card : ENNReal) := by
      dsimp [v]
      rw [Finset.sum_fiberwise_eq_sum_filter s part assign (fun i => volume (Nrm.fine i).carrier)]
      rw [Tube.sum_volume_carrier_eq_card_mul (fun i => (Nrm.fine i).toTube)
        (Nrm.fine i0).toTube]
      exact mul_comm _ _
    have hdescNe (part : Finset iota) (hp : part ∈ F.parts) :
        (s.filter (fun i => assign i ∈ part)).Nonempty := by
      obtain ⟨k, hk⟩ := F.nonempty_of_mem_parts hp
      have hkr : k ∈ r := F.subset hp hk
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hkr
      refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩⟩
      change Q.place m i ∈ part
      rw [heq]
      exact hk
    have hpartLower (part : Finset iota) (hp : part ∈ g) :
        (t : ENNReal) * (V * ((s.filter (fun i => assign i ∈ part)).card : ENNReal)) <=
          ∑ i ∈ q.filter (fun i => assign i ∈ part), w i := by
      simpa only [hvpart] using hgpart part hp
    have hpartUpper (part : Finset iota) : (∑ i ∈ q.filter (fun i => assign i ∈ part), w i) <=
        V * ((q.filter (fun i => assign i ∈ part)).card : ENNReal) := by
      calc
        _ <= ∑ i ∈ q.filter (fun i => assign i ∈ part), volume (Nrm.fine i).carrier :=
          Finset.sum_le_sum fun i _ => measure_mono (Nrm.fine i).shade_subset
        _ = V * ((q.filter (fun i => assign i ∈ part)).card : ENNReal) := by
          simp_rw [hvol]
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hpartsNe : forall part, part ∈ g -> (part ∩ parents).Nonempty := by
      intro part hp
      have hmasspart : 0 < ∑ i ∈ q.filter (fun i => assign i ∈ part), w i :=
        (ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr htpos.ne')
          (mul_ne_zero hVpos.ne' (by exact_mod_cast (hdescNe part (hgp hp)).card_pos.ne'))).trans_le
            (hpartLower part hp)
      have hnonempty : (q.filter (fun i => assign i ∈ part)).Nonempty := by
        by_contra h
        simp [Finset.not_nonempty_iff_eq_empty.mp h] at hmasspart
      obtain ⟨i, hi⟩ := hnonempty
      exact ⟨assign i, Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hi).2,
        Finset.mem_image_of_mem _ (Finset.mem_filter.mp hi).1⟩⟩
    have hancestor : forall b, a <= b -> b <= M -> forall i, i ∈ S -> forall j, j ∈ S ->
        Q.place b i = Q.place b j -> Q.place a i = Q.place a j := by
      intro b hab
      induction b, hab using Nat.le_induction with
      | base => intro _ i _ j _ heq; exact heq
      | succ b hab ih =>
        intro hb i hi j hj heq
        apply ih (Nat.le_of_succ_le hb) i hi j hj
        rw [Q.parent_composition b (Nat.lt_of_succ_le hb) i hi,
          Q.parent_composition b (Nat.lt_of_succ_le hb) j hj, heq]
    have hwholecell (k : iota) (hk : k ∈ r) :
        s.filter (fun i => assign i = k) = Q.cell m k := by
      obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp hk
      ext i
      simp only [s, SourceThreadedTower.cell, Finset.mem_filter, assign] at hj ⊢
      constructor
      · rintro ⟨⟨hi, _⟩, heq⟩
        exact ⟨hi, heq⟩
      · rintro ⟨hi, heq⟩
        refine ⟨⟨hi, ?_⟩, heq⟩
        exact (hancestor m E.coarse_lt_middle.le E.middle_bound i hi j hj.1
          (heq.trans hjk.symm)).trans hj.2
    have hindex (k : iota) (hk : k ∈ r) : k ∈ Q.indexSet m := by
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hk
      exact heq ▸ Q.place_mem m E.middle_bound i (Finset.mem_filter.mp hi).1
    have hpartCard : forall part, part ∈ g ->
        (part.card : NNReal) <= L * ((part ∩ parents).card : NNReal) := by
      intro part hp
      apply hpaid ((s.filter (fun i => assign i ∈ part)).card : NNReal)
        ((q.filter (fun i => assign i ∈ part)).card : NNReal)
        (part.card : NNReal) ((part ∩ parents).card : NNReal) t L V
        (∑ i ∈ q.filter (fun i => assign i ∈ part), w i)
        (by exact_mod_cast (hdescNe part (hgp hp)).card_pos) hVpos.ne' hVfin
        (by simpa using hpartLower part hp) (by simpa using hpartUpper part) ?_ hLt.symm.le
      have hcross' := hcross s q assign hqs part (by
        intro k hk l hl
        rw [hwholecell k (F.subset (hgp hp) hk), hwholecell l (F.subset (hgp hp) hl)]
        exact hstats.descendant_count m E.middle_bound k
          (hindex k (F.subset (hgp hp) hk)) l (hindex l (F.subset (hgp hp) hl)))
      exact_mod_cast hcross'
    have hpartMass : forall part, part ∈ g ->
        (∑ i ∈ s.filter (fun i => assign i ∈ part), volume (Nrm.fine i).shade) <=
          (L : ENNReal) * ∑ i ∈ q.filter (fun i => assign i ∈ part), volume (Nrm.fine i).shade := by
      intro part hp
      calc
        _ <= ∑ i ∈ s.filter (fun i => assign i ∈ part), volume (Nrm.fine i).carrier :=
          Finset.sum_le_sum fun i _ => measure_mono (Nrm.fine i).shade_subset
        _ = ∑ k ∈ part, v k :=
          (Finset.sum_fiberwise_eq_sum_filter s part assign (fun i => volume (Nrm.fine i).carrier)).symm
        _ <= 2 * ∑ k ∈ part, v k := by
          simpa only [one_mul] using mul_le_mul_left
            (by norm_num : (1 : ENNReal) <= 2) (∑ k ∈ part, v k)
        _ = (L : ENNReal) * ((t : ENNReal) * ∑ k ∈ part, v k) := by
          rw [← mul_assoc, ← ENNReal.coe_mul, hLt]
          norm_num
        _ <= (L : ENNReal) * ∑ i ∈ q.filter (fun i => assign i ∈ part), w i :=
          mul_le_mul_right (hgpart part hp) _
    refine ⟨{ edLeaves := ed
              ed_subset := heds
              ed_pairwise := hed
              ed_mass_price := hedmass
              leaves := q
              leaves_subset_ed := hqq0.trans hq0ed
              leaves_subset := hqs
              leaves_nonempty := hqne
              shading := Nrm.fine
              same_tubes := fun _ => rfl
              subshade := fun _ => le_rfl
              essentially_distinct := hed.mono (hqq0.trans hq0ed)
              refinement := href
              mass := hmass
              union_subset := ?_
              fullness := ?_
              multiplicity := ?_
              parents := parents
              parents_eq := rfl
              parents_subset := hparentr
              parents_nonempty := hparentne
              parent_ball := fun k hk => Nrm.parent_ball k (hparentr hk)
              n := n
              Cfib := 2
              n_positive := hn
              Cfib_one := by norm_num
              Cfib_bound := hCcount
              fibre_nonempty := ?_
              fibre_lower := ?_
              fibre_upper := ?_
              keptParts := g
              kept_parts_subset := hgp
              kept_parts_nonempty := hgne
              kept_intersection_nonempty := hpartsNe
              kept_cover := ?_
              partRetention := L
              part_retention_one := hL
              part_retention_bound := le_rfl
              part_card_retention := hpartCard
              part_volume_retention := ?_
              part_mass_retention := hpartMass }⟩
    · exact Set.iUnion₂_subset fun i hi => Set.subset_iUnion₂
        (s := fun i _ => (Nrm.fine i).shade) i (hqs hi)
    · simpa only [div_eq_mul_inv, mul_comm] using
        ShadedBody.IsCRefinement.mul_fullness_le _ _ _ _ hcarrier href
    · have hmul := ShadedBody.IsCRefinement.mul_multiplicity_le _ _ _ _ href
      rw [ENNReal.coe_inv hLpos.ne'] at hmul
      exact (ENNReal.inv_mul_le_iff (ENNReal.coe_ne_zero.mpr hLpos.ne') ENNReal.coe_ne_top).mp hmul
    · intro k hk
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hk
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, heq⟩⟩
    · intro k hk
      rw [hfibre k hk]
      exact (hcounts k (hparent0 hk)).1
    · intro k hk
      rw [hfibre k hk]
      exact (hcounts k (hparent0 hk)).2
    · ext k
      simp only [Finset.mem_biUnion, Finset.mem_inter]
      constructor
      · rintro ⟨part, _, _, hk⟩
        exact hk
      · intro hk
        obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hk
        have hkg : k ∈ g.biUnion id := heq ▸ (Finset.mem_filter.mp hi).2
        obtain ⟨part, hp, hkp⟩ := Finset.mem_biUnion.mp hkg
        exact ⟨part, hp, hkp, Finset.mem_image.mpr ⟨i, hi, heq⟩⟩
    · intro part hp
      rw [Tube.sum_volume_carrier_eq_card_mul (Q.tube m) (Q.tube m i0),
        Tube.sum_volume_carrier_eq_card_mul (Q.tube m) (Q.tube m i0)]
      calc
        _ <= ((L : ENNReal) * ((part ∩ parents).card : ENNReal)) *
            volume (Q.tube m i0).carrier := by
          exact mul_le_mul_left (by exact_mod_cast hpartCard part hp) _
        _ = _ := by ring
  let A : NNReal := max Cgeom 2
  let edConstant : ENNReal := 1 + Tube.refineToEssDistinctLeaves.C 3 * (Cgeom : ENNReal)
  let paidConstant : ENNReal := 4 * (Cgeom : ENNReal) * edConstant
  have hA : 1 <= A := (by norm_num : (1 : NNReal) <= 2).trans (le_max_right _ _)
  have hAC : Cgeom <= A := le_max_left _ _
  have hA2 : 2 <= A := le_max_right _ _
  have hCpos : 0 < Cgeom := lt_of_lt_of_le (by norm_num) hC
  have hEDfinite : edConstant ≠ ⊤ := by
    apply ENNReal.add_ne_top.mpr
    refine ⟨by norm_num, ENNReal.mul_ne_top ?_ ENNReal.coe_ne_top⟩
    exact ENNReal.div_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top)
      (ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos 3).ne')
  have hPaidFinite : paidConstant ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top) hEDfinite
  refine ⟨A, 4, Kout, hAC, hA, by norm_num, le_rfl, ?_⟩
  intro etaPlank zeta etaParent heta heta1 hzeta hParent
  have hcardEvent : ∀ᶠ delta : NNReal in 𝓝[>] 0,
      (Kakeya.Tube.card_le_of_densityIn_le.C 3 : ENNReal) <= (delta : ENNReal) ^ (-1 : Real) :=
    Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg ENNReal.coe_ne_top (by norm_num)
  have hPaidEvent : ∀ᶠ delta : NNReal in 𝓝[>] 0,
      paidConstant <= (delta : ENNReal) ^ (-zeta) :=
    Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg hPaidFinite hzeta
  have hLogEvent := Kakeya.VeryNotSticky.eventually_ofReal_polylog_pow_le_rpow_neg
    (A := 1) (B := 4) (by norm_num) (by norm_num) 1 hzeta
  have hUnitEvent : ∀ᶠ delta : NNReal in 𝓝[>] 0, delta < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
  filter_upwards [hcardEvent, hPaidEvent, hLogEvent, self_mem_nhdsWithin,
    hUnitEvent] with
    delta hCardConstant hPaid hLog hdelta hdelta1
  intro bias hbias hBiasBound iota S T Q Z hQ hstats hfull a m aw bw cw hm O Nrm E
  have hdR : (0 : Real) < delta := hdelta
  have hd1R : (delta : Real) <= 1 := hdelta1.le
  have hd0 : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hdelta.ne'
  have hd1e : (delta : ENNReal) <= 1 := by exact_mod_cast hdelta1.le
  have hpow (x : Real) : ENNReal.ofReal ((delta : Real) ^ x) = (delta : ENNReal) ^ x := by
    rw [← ENNReal.ofReal_rpow_of_pos hdR]
    simp only [ENNReal.ofReal_coe_nnreal]
  have hone (x : Real) (hx : 0 <= x) : 1 <= (delta : ENNReal) ^ (-x) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hdelta.ne']
    exact_mod_cast NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta1.le (neg_nonpos.mpr hx)
  have hCard : (S.card : ENNReal) <= (delta : ENNReal) ^ (-4 : Real) := by
    have hc := Kakeya.Tube.card_le_of_densityIn_le hdelta.ne'
      (fun i hi => (hQ.geometry.original_ball i hi).trans
        (Metric.closedBall_subset_closedBall (by norm_num : (3 / 4 : Real) <= 1)))
      ((Kakeya.le_maxDensity S (fun i => (T i).toConvexSpaceBody)
        ConvexSpaceBody.closedUnitBall).trans hQ.maximal_density)
    have hc' : (S.card : ENNReal) <= (Kakeya.Tube.card_le_of_densityIn_le.C 3 : ENNReal) *
        (delta : ENNReal) ^ (-etaPlank) * (delta : ENNReal) ^ (-2 : Real) := by
      rw [show (-2 : Real) = ((-2 : Int) : Real) by norm_num, ENNReal.rpow_intCast]
      simpa only [hpow, show Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3 by simp,
        Nat.cast_ofNat, show -((3 : Int) - 1) = -2 by norm_num, ENNReal.rpow_intCast] using hc
    calc
      _ <= (delta : ENNReal) ^ (-1 : Real) * (delta : ENNReal) ^ (-etaPlank) *
          (delta : ENNReal) ^ (-2 : Real) :=
        hc'.trans (mul_le_mul_left (mul_le_mul_left hCardConstant _) _)
      _ = (delta : ENNReal) ^ (-(etaPlank + 3)) := by
        rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top,
          ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
        congr 1 <;> ring
      _ <= (delta : ENNReal) ^ (-4 : Real) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hd1e (by linarith)
  have hsigma1 : sourceEccentricFineScale delta M a <= 1 := by
    exact_mod_cast Nrm.fine_situation.out_le_quarter.trans (by norm_num : (1 / 4 : Real) <= 1)
  let s := Q.cell a O.chosen
  let mass := fun i => volume (Nrm.fine i).shade
  let carrier := fun i => volume (Nrm.fine i).carrier
  have hmasspos : 0 < ∑ i ∈ s, mass i := by
    rw [show (∑ i ∈ s, mass i) =
      affineJacobian Nrm.affine * ∑ i ∈ s, volume (O.innerShade i).shade from
        Nrm.mass_image s le_rfl]
    exact ENNReal.mul_pos Nrm.jacobian_pos.ne' O.inner_mass_pos.ne'
  have hdensity : Kakeya.maxDensity s (fun i => (Nrm.fine i).toConvexSpaceBody) <=
      (Cgeom : ENNReal) * (delta : ENNReal) ^ (-etaPlank) := by
    apply Nrm.maximal_density.trans
    apply mul_le_mul_right
    exact (Kakeya.maxDensity_mono _ (Finset.filter_subset _ _)).trans
      (by simpa only [hpow] using hQ.maximal_density)
  let cost := 1 + Tube.refineToEssDistinctLeaves.C 3 *
    Kakeya.maxDensity s (fun i => (Nrm.fine i).toConvexSpaceBody)
  have hcost : cost <= edConstant * (delta : ENNReal) ^ (-etaPlank) := by
    calc
      _ <= 1 + Tube.refineToEssDistinctLeaves.C 3 *
          ((Cgeom : ENNReal) * (delta : ENNReal) ^ (-etaPlank)) := by
        exact add_le_add_right (mul_le_mul_right hdensity _) 1
      _ <= (delta : ENNReal) ^ (-etaPlank) + Tube.refineToEssDistinctLeaves.C 3 *
          ((Cgeom : ENNReal) * (delta : ENNReal) ^ (-etaPlank)) :=
        add_le_add_left (hone etaPlank heta.le) _
      _ = edConstant * (delta : ENNReal) ^ (-etaPlank) := by dsimp [edConstant]; ring
  obtain ⟨ed, heds, hed, hedmass⟩ := Kakeya.exists_pairwise_essDistinct_subfamily_sum_shade_le
    Nrm.fine_pos hsigma1 s Nrm.fine le_rfl
  have hedmass' : (∑ i ∈ s, mass i) <= cost * ∑ i ∈ ed, mass i := by
    simpa [cost, show Module.finrank Real (EuclideanSpace Real (Fin 3)) = 3 by simp] using hedmass
  have hedpos : 0 < ∑ i ∈ ed, mass i := by
    by_contra h
    rw [le_antisymm (le_of_not_gt h) zero_le, mul_zero] at hedmass'
    exact (not_le_of_gt hmasspos) hedmass'
  obtain ⟨r, hrs, hrne, hrmass, n, hn, hcounts⟩ := hbin ed (Q.place m) mass hedpos
  let q0 := ed.filter (fun i => Q.place m i ∈ r)
  have hq0ed : q0 <= ed := Finset.filter_subset _ _
  have hq0r : q0.image (Q.place m) = r := by
    ext k
    constructor
    · rintro hk
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hk
      exact heq ▸ (Finset.mem_filter.mp hi).2
    · intro hk
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp (hrs hk)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, heq.symm ▸ hk⟩, heq⟩
  have hqcounts : forall k, k ∈ q0.image (Q.place m) ->
      n / 2 <= ((q0.filter (fun i => Q.place m i = k)).card : NNReal) /\
      ((q0.filter (fun i => Q.place m i = k)).card : NNReal) <= 2 * n := by
    simpa only [hq0r] using hcounts
  have hLo : 1 <= sourceEccentricLogLoss Kout delta := by
    apply Real.one_le_toNNReal.mpr
    have hinv : 1 <= (1 / (delta : Real)) := (one_le_div hdR).mpr hd1R
    have hl := Real.logb_nonneg (by norm_num : (1 : Real) < 2) hinv
    exact one_le_pow₀ (by linarith : (1 : Real) <= 2 + Real.logb 2 (1 / (delta : Real)))
  let L := sourceEccentricSelectionCost A 4 Kout delta etaPlank zeta
  have hL : 1 <= L := by
    have hp : 1 <= delta ^ (-(4 : Real) * (etaPlank + zeta)) :=
      NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta1.le (by linarith)
    simpa only [L, sourceEccentricSelectionCost, Nat.cast_ofNat, mul_one] using
      mul_le_mul' (mul_le_mul' hA hLo) hp
  have hCount : 2 <= A * delta ^ (-(4 : Real) * zeta) := by
    apply hA2.trans
    have h : 1 <= delta ^ (-(4 : Real) * zeta) := by
      exact NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta hdelta1.le (by linarith)
    simpa only [mul_one] using mul_le_mul_right h A
  apply hcore Q O Nrm E hstats ed q0 heds hq0ed hed hedmass' n L
    (A * delta ^ (-(4 : Real) * zeta)) hn hL hCount hqcounts
  have hedne : ed.Nonempty := by
    by_contra h
    simp [Finset.not_nonempty_iff_eq_empty.mp h] at hedpos
  have hedCard : (ed.card : ENNReal) <= (delta : ENNReal) ^ (-4 : Real) := by
    have hh : (ed.card : ENNReal) <= S.card := by
      exact_mod_cast Finset.card_le_card (heds.trans (Finset.filter_subset _ _))
    exact hh.trans hCard
  have hedCardR : (ed.card : Real) <= (delta : Real) ^ (-4 : Real) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : Real) <= (delta : Real) ^ (-4 : Real))).mp
    simpa only [hpow, ENNReal.ofReal_natCast] using hedCard
  let binLoss := ENNReal.ofReal (1 + Real.logb 2 (ed.card : Real))
  have hbinLoss : binLoss <= (delta : ENNReal) ^ (-zeta) := by
    apply le_trans (b := ENNReal.ofReal (1 + 4 * Real.logb 2 ((delta : Real)⁻¹)))
    · apply ENNReal.ofReal_le_ofReal
      have hh := Real.logb_le_logb_of_le (by norm_num : (1 : Real) < 2)
        (by exact_mod_cast hedne.card_pos : (0 : Real) < ed.card) hedCardR
      rw [Real.logb_rpow_eq_mul_logb_of_pos hdR] at hh
      rw [Real.logb_inv]
      linarith
    · simpa only [pow_one] using hLog
  have hLoc : 0 < sourceEccentricLogLoss Kout delta := lt_of_lt_of_le (by norm_num) hLo
  have hfullFine : delta ^ etaPlank / (sourceEccentricLogLoss Kout delta * Cgeom) <=
      ShadedBody.fullness s (fun i => (Nrm.fine i).toShadedBody) := by
    calc
      _ = (delta ^ etaPlank / sourceEccentricLogLoss Kout delta) / Cgeom := (div_div _ _ _).symm
      _ <= (ShadedBody.fullness S (fun i => (Z i).toShadedBody) /
          sourceEccentricLogLoss Kout delta) / Cgeom := by gcongr
      _ <= ShadedBody.fullness s (fun i => (O.innerShade i).toShadedBody) / Cgeom := by
        gcongr
        exact O.inner_fullness
      _ <= _ := Nrm.fullness
  let cFull : ENNReal :=
    (sourceEccentricLogLoss Kout delta : ENNReal) * (Cgeom : ENNReal) * (delta : ENNReal) ^ (-etaPlank)
  have hlc0 : ((sourceEccentricLogLoss Kout delta : ENNReal) * (Cgeom : ENNReal)) ≠ 0 :=
    mul_ne_zero (ENNReal.coe_ne_zero.mpr hLoc.ne') (ENNReal.coe_ne_zero.mpr hCpos.ne')
  have hlcfin : (sourceEccentricLogLoss Kout delta : ENNReal) * (Cgeom : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hfullFineE : (delta : ENNReal) ^ etaPlank /
      ((sourceEccentricLogLoss Kout delta : ENNReal) * (Cgeom : ENNReal)) <=
      (ShadedBody.fullness s (fun i => (Nrm.fine i).toShadedBody) : ENNReal) := by
    have hh := ENNReal.coe_le_coe.mpr hfullFine
    simpa only [ENNReal.coe_div (mul_pos hLoc hCpos).ne', ENNReal.coe_mul,
      ENNReal.coe_rpow_of_ne_zero hdelta.ne'] using hh
  have hcFull : 1 <= cFull *
      (ShadedBody.fullness s (fun i => (Nrm.fine i).toShadedBody) : ENNReal) := by
    calc
      1 = cFull * ((delta : ENNReal) ^ etaPlank /
          ((sourceEccentricLogLoss Kout delta : ENNReal) * (Cgeom : ENNReal))) := by
        dsimp [cFull]
        rw [div_eq_mul_inv]
        have heq : ((sourceEccentricLogLoss Kout delta : ENNReal) * (Cgeom : ENNReal) *
            (delta : ENNReal) ^ (-etaPlank)) *
            ((delta : ENNReal) ^ etaPlank *
              ((sourceEccentricLogLoss Kout delta : ENNReal) * (Cgeom : ENNReal))⁻¹) =
            (((sourceEccentricLogLoss Kout delta : ENNReal) * (Cgeom : ENNReal)) *
              ((sourceEccentricLogLoss Kout delta : ENNReal) * (Cgeom : ENNReal))⁻¹) *
              ((delta : ENNReal) ^ (-etaPlank) * (delta : ENNReal) ^ etaPlank) := by ring
        rw [heq, ENNReal.mul_inv_cancel hlc0 hlcfin,
          ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
        simp
      _ <= _ := mul_le_mul_right hfullFineE _
  have hcarMass : (∑ i ∈ s, carrier i) <= cFull * ∑ i ∈ s, mass i := by
    calc
      _ = 1 * ∑ i ∈ s, carrier i := (one_mul _).symm
      _ <= (cFull * (ShadedBody.fullness s (fun i => (Nrm.fine i).toShadedBody) : ENNReal)) *
          ∑ i ∈ s, carrier i := mul_le_mul_left hcFull _
      _ = cFull * ∑ i ∈ s, mass i := by
        rw [mul_assoc, ← ShadedBody.sum_volumeReal_shade_eq_fullness_mul]
  have hcoeff : 4 * cFull * cost * binLoss <= (L : ENNReal) := by
    calc
      _ <= 4 * cFull * (edConstant * (delta : ENNReal) ^ (-etaPlank)) *
          (delta : ENNReal) ^ (-zeta) := by gcongr
      _ = paidConstant * (sourceEccentricLogLoss Kout delta : ENNReal) *
          ((delta : ENNReal) ^ (-etaPlank) * (delta : ENNReal) ^ (-etaPlank)) *
          (delta : ENNReal) ^ (-zeta) := by dsimp [paidConstant, cFull]; ring
      _ <= (delta : ENNReal) ^ (-zeta) * (sourceEccentricLogLoss Kout delta : ENNReal) *
          ((delta : ENNReal) ^ (-etaPlank) * (delta : ENNReal) ^ (-etaPlank)) *
          (delta : ENNReal) ^ (-zeta) := by gcongr
      _ = (sourceEccentricLogLoss Kout delta : ENNReal) *
          (delta : ENNReal) ^ (-(2 * etaPlank + 2 * zeta)) := by
        calc
          _ = (sourceEccentricLogLoss Kout delta : ENNReal) *
              (((delta : ENNReal) ^ (-zeta) * (delta : ENNReal) ^ (-etaPlank)) *
                (delta : ENNReal) ^ (-etaPlank) * (delta : ENNReal) ^ (-zeta)) := by ring
          _ = _ := by
            rw [← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top,
              ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top,
              ← ENNReal.rpow_add _ _ hd0 ENNReal.coe_ne_top]
            congr 2 <;> ring
      _ <= (A : ENNReal) * (sourceEccentricLogLoss Kout delta : ENNReal) *
          (delta : ENNReal) ^ (-(4 : Real) * (etaPlank + zeta)) := by
        have hexp := ENNReal.rpow_le_rpow_of_exponent_ge hd1e
          (show -(4 : Real) * (etaPlank + zeta) <= -(2 * etaPlank + 2 * zeta) by linarith)
        have hAA : (sourceEccentricLogLoss Kout delta : ENNReal) <=
            (A : ENNReal) * (sourceEccentricLogLoss Kout delta : ENNReal) := by
          simpa only [ENNReal.coe_one, one_mul] using mul_le_mul_left (ENNReal.coe_le_coe.mpr hA) _
        exact mul_le_mul' hAA hexp
      _ = (L : ENNReal) := by
        simp only [L, sourceEccentricSelectionCost, ENNReal.coe_mul,
          ENNReal.coe_rpow_of_ne_zero hdelta.ne', Nat.cast_ofNat]
  calc
    _ <= 4 * (cFull * ∑ i ∈ s, mass i) := mul_le_mul_right hcarMass _
    _ <= 4 * (cFull * (cost * ∑ i ∈ ed, mass i)) :=
      mul_le_mul_right (mul_le_mul_right hedmass' _) _
    _ <= 4 * (cFull * (cost * (binLoss * ∑ i ∈ q0, mass i))) :=
      mul_le_mul_right (mul_le_mul_right (mul_le_mul_right hrmass _) _) _
    _ = (4 * cFull * cost * binLoss) * ∑ i ∈ q0, mass i := by ring
    _ <= (L : ENNReal) * ∑ i ∈ q0, mass i := mul_le_mul_left hcoeff _

end Kakeya.ML2Core
