/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceLateChoice
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceFactorCeilings
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineHfacProducer

@[expose] public section

open Filter Kakeya.ML2Reduction
open scoped NNReal ENNReal Topology

namespace Kakeya.ML2Assembly

universe u

noncomputable def sourceMiddleCardBudget (varpi zeta : Real) : Real := varpi * zeta / 16

noncomputable def sourceMiddleSmallLoss (varpi zeta v d : Real) : Real :=
  min (sourceMiddleCardBudget varpi zeta) (sourceMiddleCenter v d) / 8

noncomputable def sourceMiddleCardPower (e : Real) : Nat := Nat.ceil (8 / e) + 1

noncomputable def sourceMiddleDensityExponent (e kappa r : Real) (M : Nat) : Real :=
  2 * kappa / e + r / (1 - e) * (1 + 4 / (e * M))

noncomputable def sourceMiddleNextZeta (beta varpi eps1 : Real)
    (rawGain rawDens : Real -> Real) (m : Nat) : Real :=
  ML2Spine.spineRung beta varpi eps1
    (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1) / 16

/-- The earlier source choices in the finite minimum labelled ml2-nonc-input. -/
structure SourceMiddleSourceCaps (N : Nat) where
  nuC : Real
  epsSc : Real
  etaOne : Real
  hOne : Real
  hTwo : Real
  etaFine : Nat -> Real
  etaParent : Nat -> Real
  nuC_pos : 0 < nuC
  epsSc_pos : 0 < epsSc
  etaOne_pos : 0 < etaOne
  hOne_pos : 0 < hOne
  hTwo_pos : 0 < hTwo
  etaFine_pos : forall m, m < N -> 0 < etaFine m
  etaParent_pos : forall m, m < N -> 0 < etaParent m

/-- Each finite source ceiling and all three strict R4 gaps on its actual rung. -/
structure SourceMiddleFiniteChoices (N : Nat) (e varpi : Real)
    (zeta v d : Nat -> Real) (caps : SourceMiddleSourceCaps N) (etaC : Real) : Prop where
  input_ceiling_pos : 0 < etaC
  nonsticky_gain : etaC <= caps.nuC / 100
  scale_accuracy : etaC <= e * caps.epsSc * caps.etaOne / 224
  auxiliary_one : etaC <= caps.hOne / 100
  auxiliary_two : etaC <= caps.hTwo / 100
  first_rung : etaC <= caps.etaOne / 2
  raw_density : forall m, m < N -> etaC <= e * d m / 28
  fine_input : forall m, m < N -> etaC <= caps.etaFine m
  parent_input : forall m, m < N -> etaC <= caps.etaParent m / 4
  middle_fullness : forall m, m < N ->
    etaC <= e * sourceMiddleSmallLoss varpi (zeta m) (v m) (d m) / 24
  middle_retention : forall m, m < N -> etaC <= e * varpi * zeta m / 100
  card_budget_pos : forall m, m < N -> 0 < sourceMiddleCardBudget varpi (zeta m)
  center_pos : forall m, m < N -> 0 < sourceMiddleCenter (v m) (d m)
  small_loss_pos : forall m, m < N ->
    0 < sourceMiddleSmallLoss varpi (zeta m) (v m) (d m)
  small_loss_le_center : forall m, m < N ->
    sourceMiddleSmallLoss varpi (zeta m) (v m) (d m) <= sourceMiddleCenter (v m) (d m)
  card_gap : forall m, m < N ->
    2 * sourceMiddleSmallLoss varpi (zeta m) (v m) (d m) <
      sourceMiddleCardBudget varpi (zeta m)
  mass_gap : forall m, m < N ->
    3 * sourceMiddleSmallLoss varpi (zeta m) (v m) (d m) <
      3 * sourceMiddleCenter (v m) (d m)
  card_power_pos : 0 < sourceMiddleCardPower e
  card_power_bound : 4 <= e * (sourceMiddleCardPower e : Real) / 2

/-- M can satisfy all extra finite lower bounds at its original integer-choice stage. -/
theorem sourceMiddle_exists_fixed_integer (N Mstar : Nat) (hMstar : 0 < Mstar)
    (e varpi : Real) (he : 0 < e) (hvarpi : 0 < varpi)
    (zeta : Nat -> Real) (hzeta : forall m, m < N -> 0 < zeta m)
    (B : Real) :
    exists M : Nat, 0 < M ∧ Mstar ∣ M ∧ B <= (M : Real) ∧
      4 / e <= (M : Real) ∧
      (forall m, m < N -> 3 / (M : Real) <= e * varpi * zeta m / 4) ∧
      0 < sourceMiddleCardPower e ∧ 4 <= e * (sourceMiddleCardPower e : Real) / 2 := by
  classical
  let bounds : Finset Real := insert B (insert (4 / e)
    ((Finset.range N).image fun m => 12 / (e * varpi * zeta m)))
  have hbounds : bounds.Nonempty := ⟨B, by simp [bounds]⟩
  let k : Nat := Nat.ceil (max 1 (bounds.max' hbounds)) + 1
  have hk : (max 1 (bounds.max' hbounds)) < (k : Real) := by
    dsimp [k]
    push_cast
    linarith [Nat.le_ceil (max 1 (bounds.max' hbounds))]
  have hk0 : 0 < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hk.le))
  have hM : (bounds.max' hbounds) <= ((Mstar * k : Nat) : Real) := by
    have hstar : (1 : Real) <= Mstar := by exact_mod_cast hMstar
    have hkreal : 0 <= (k : Real) := Nat.cast_nonneg k
    norm_num only [Nat.cast_mul]
    nlinarith [le_max_right 1 (bounds.max' hbounds)]
  have hbound (x : Real) (hx : x ∈ bounds) : x <= ((Mstar * k : Nat) : Real) :=
    (bounds.le_max' x hx).trans hM
  have heK : 8 <= e * (sourceMiddleCardPower e : Real) := by
    have hc := Nat.le_ceil (8 / e)
    have hceil : 8 / e <= (sourceMiddleCardPower e : Real) := by
      dsimp [sourceMiddleCardPower]
      push_cast
      linarith
    simpa [mul_comm] using (div_le_iff₀ he).mp hceil
  refine ⟨Mstar * k, Nat.mul_pos hMstar hk0, dvd_mul_right _ _,
    hbound B (by simp [bounds]), hbound (4 / e) (by simp [bounds]), ?_, by
      unfold sourceMiddleCardPower; omega, by linarith⟩
  intro m hm
  have hz := hzeta m hm
  have hden : 0 < e * varpi * zeta m := by positivity
  have hb := hbound (12 / (e * varpi * zeta m)) (Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm, rfl⟩)))
  have hM0 : (0 : Real) < ((Mstar * k : Nat) : Real) := by
    exact_mod_cast Nat.mul_pos hMstar hk0
  apply (div_le_iff₀ hM0).2
  have hh := (div_le_iff₀ hden).1 hb
  nlinarith

open Classical in
/-- Actual factor ceilings and L4 are bound once, before every later runtime state. -/
theorem sourceMiddle_exists_finite_choices {beta varpi eps1 : Real}
    {rawGain rawDens : Real -> Real}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1) (heps1 : 0 < eps1)
    (hp : Lemma91ParamsAt.{u} beta varpi rawGain rawDens)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace Real (Fin 3)) beta) :
    exists s : Real, exists a : SourceLocalAccuracyData, exists x : SourceFactorCeilingData,
      SourceLocalPreparation.{u} beta varpi eps1 rawGain rawDens ∧
      SourceLocalBudget beta varpi eps1 rawGain rawDens s a ∧
      SourceFactorCores.{u} (EuclideanSpace Real (Fin 3)) beta s s s x ∧
      forall (caps : SourceMiddleSourceCaps (ML2Spine.spineCount varpi eps1)) (Hpre : Finset Real),
        (forall h, h ∈ Hpre -> 0 < h) ->
        exists etaC etaL etaIn eta aL : Real,
          SourceMiddleFiniteChoices (ML2Spine.spineCount varpi eps1)
            (ML2Spine.spineDiv varpi eps1) varpi
            (sourceMiddleNextZeta beta varpi eps1 rawGain rawDens)
            (fun m => rawGain (sourceMiddleNextZeta beta varpi eps1 rawGain rawDens m))
            (fun m => rawDens (sourceMiddleNextZeta beta varpi eps1 rawGain rawDens m)) caps etaC ∧
          SourceLateInputBounds beta varpi eps1 rawGain rawDens s a
            (insert etaC (sourceFactorCeilingSet x ∪ Hpre)) etaL etaIn eta aL ∧
          SourceScheduledFactorBodies.{u} (EuclideanSpace Real (Fin 3))
            beta varpi eps1 rawGain rawDens a etaL x := by
  obtain ⟨s, a, hprep, hbudget, hlate⟩ :=
    sourceSpine_localReserve_after_ceilings hbeta0 hbeta1 heps1 hp
  obtain ⟨x, hcores, hsched⟩ :=
    sourceSpine_exists_factor_ceilings_at_budget (E := EuclideanSpace Real (Fin 3))
      hbeta0 hbeta1 heps1 hp hKT hbudget
  refine ⟨s, a, x, hprep, hbudget, hcores, ?_⟩
  intro caps Hpre hHpre
  let N := ML2Spine.spineCount varpi eps1
  let e := ML2Spine.spineDiv varpi eps1
  let z := sourceMiddleNextZeta beta varpi eps1 rawGain rawDens
  let v := fun m => rawGain (z m)
  let d := fun m => rawDens (z m)
  let g := fun m => sourceMiddleSmallLoss varpi (z m) (v m) (d m)
  have he : 0 < e := ML2Spine.spineDiv_pos hp.window_pos heps1
  have hz (m : Nat) (hm : m < N) : 0 < z m := (hprep.middle m hm).tolerance_pos
  have hd (m : Nat) (hm : m < N) : 0 < d m := hp.dens_pos _ (hz m hm)
  have hv (m : Nat) (hm : m < N) : 0 < v m := hp.gain_pos _ (hz m hm)
  have hA (m : Nat) (hm : m < N) : 0 < sourceMiddleCardBudget varpi (z m) := by
    unfold sourceMiddleCardBudget
    exact div_pos (mul_pos hp.window_pos (hz m hm)) (by norm_num)
  have hq (m : Nat) (hm : m < N) : 0 < sourceMiddleCenter (v m) (d m) :=
    (hprep.middle m hm).center_pos
  have hg (m : Nat) (hm : m < N) : 0 < g m := by
    exact div_pos (lt_min (hA m hm) (hq m hm)) (by norm_num)
  let initial : Finset Real := {caps.nuC / 100, e * caps.epsSc * caps.etaOne / 224,
    caps.hOne / 100, caps.hTwo / 100, caps.etaOne / 2}
  let perRung := fun m => min (e * d m / 28) (min (caps.etaFine m)
    (min (caps.etaParent m / 4) (min (e * g m / 24) (e * varpi * z m / 100))))
  let ceilings := initial ∪ (Finset.range N).image perRung
  have hinitial : forall y, y ∈ initial -> 0 < y := by
    intro y hy
    simp only [initial, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact div_pos caps.nuC_pos (by norm_num)
    · exact div_pos (mul_pos (mul_pos he caps.epsSc_pos) caps.etaOne_pos) (by norm_num)
    · exact div_pos caps.hOne_pos (by norm_num)
    · exact div_pos caps.hTwo_pos (by norm_num)
    · exact div_pos caps.etaOne_pos (by norm_num)
  have hceil : forall y, y ∈ ceilings -> 0 < y := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hinitial y hy
    · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hy
      have hm' := Finset.mem_range.mp hm
      exact lt_min (div_pos (mul_pos he (hd m hm')) (by norm_num))
        (lt_min (caps.etaFine_pos m hm') (lt_min (div_pos (caps.etaParent_pos m hm')
          (by norm_num)) (lt_min (div_pos (mul_pos he (hg m hm')) (by norm_num))
            (div_pos (mul_pos (mul_pos he hp.window_pos) (hz m hm')) (by norm_num)))))
  have hne : ceilings.Nonempty := ⟨caps.nuC / 100, by simp [ceilings, initial]⟩
  let etaC := ceilings.min' hne
  have hetaC : 0 < etaC := hceil _ (ceilings.min'_mem hne)
  have hinit (y : Real) (hy : y ∈ initial) : etaC <= y :=
    ceilings.min'_le _ (Finset.mem_union_left _ hy)
  have hrung (m : Nat) (hm : m < N) : etaC <= perRung m :=
    ceilings.min'_le _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm, rfl⟩))
  have hc : SourceMiddleFiniteChoices N e varpi z v d caps etaC := {
    input_ceiling_pos := hetaC
    nonsticky_gain := hinit _ (by simp [initial])
    scale_accuracy := hinit _ (by simp [initial])
    auxiliary_one := hinit _ (by simp [initial])
    auxiliary_two := hinit _ (by simp [initial])
    first_rung := hinit _ (by simp [initial])
    raw_density := fun m hm => (le_min_iff.mp (hrung m hm)).1
    fine_input := fun m hm => (le_min_iff.mp (le_min_iff.mp (hrung m hm)).2).1
    parent_input := fun m hm => (le_min_iff.mp (le_min_iff.mp (le_min_iff.mp (hrung m hm)).2).2).1
    middle_fullness := fun m hm => (le_min_iff.mp (le_min_iff.mp (le_min_iff.mp
      (le_min_iff.mp (hrung m hm)).2).2).2).1
    middle_retention := fun m hm => (le_min_iff.mp (le_min_iff.mp (le_min_iff.mp
      (le_min_iff.mp (hrung m hm)).2).2).2).2
    card_budget_pos := hA
    center_pos := hq
    small_loss_pos := hg
    small_loss_le_center := by
      intro m hm
      have hle := min_le_right (sourceMiddleCardBudget varpi (z m)) (sourceMiddleCenter (v m) (d m))
      dsimp [sourceMiddleSmallLoss]
      linarith [hq m hm]
    card_gap := by
      intro m hm
      have hle := min_le_left (sourceMiddleCardBudget varpi (z m)) (sourceMiddleCenter (v m) (d m))
      dsimp [sourceMiddleSmallLoss]
      linarith [hA m hm]
    mass_gap := by
      intro m hm
      have hle := min_le_right (sourceMiddleCardBudget varpi (z m)) (sourceMiddleCenter (v m) (d m))
      dsimp [sourceMiddleSmallLoss]
      linarith [hq m hm]
    card_power_pos := by unfold sourceMiddleCardPower; omega
    card_power_bound := by
      have hh := (div_le_iff₀ he).mp (Nat.le_ceil (8 / e))
      dsimp [sourceMiddleCardPower]
      push_cast
      nlinarith }
  obtain ⟨etaL, etaIn, eta, aL, hinputs⟩ :=
    hlate (insert etaC (sourceFactorCeilingSet x ∪ Hpre)) (by
      intro h hh
      rcases Finset.mem_insert.mp hh with rfl | hh
      · exact hetaC
      · rcases Finset.mem_union.mp hh with hh | hh
        · exact hcores.ceilings_pos h hh
        · exact hHpre h hh)
  refine ⟨etaC, etaL, etaIn, eta, aL, hc, hinputs, hsched etaL
    (hinputs.input_pos.trans hinputs.input_lt_loss) ?_⟩
  intro h hh
  exact hinputs.loss_le_ceilings h (Finset.mem_insert_of_mem (Finset.mem_union_left _ hh))

/-- The original lambda ledger supplies the middle fullness before normalization. -/
theorem sourceMiddle_fullness_calibration {delta rho : NNReal}
    {e etaIn etaC gamma : Real} {lam Lpre L1 L2 outer f : NNReal}
    (hdelta : 0 < delta) (hdelta1 : delta <= 1) (hrho : 0 < rho)
    (he : 0 < e) (hetaIn : 0 <= etaIn) (heta : etaIn <= etaC)
    (hgamma : 0 < gamma) (hgap : 6 * etaC <= e * gamma / 2)
    (hrhoScale : (rho : Real) <= (delta : Real) ^ (e / 2))
    (hpre : 0 < Lpre) (hL1 : 0 < L1) (hL2 : 0 < L2) (houter : 0 < outer)
    (hlam : delta ^ etaIn / 2 <= lam) (hfull : lam / Lpre <= f)
    (hpreBound : 2 * Lpre <= delta ^ (-(2 * etaC)))
    (hL1Bound : L1 <= delta ^ (-etaC)) (hL2Bound : L2 <= delta ^ (-etaC))
    (houterBound : outer <= delta ^ (-etaC)) :
    delta ^ (3 * etaC) <= f ∧
      delta ^ (6 * etaC) <= outer⁻¹ * ((L1 * L2)⁻¹ * f) ∧
      rho ^ gamma <= outer⁻¹ * ((L1 * L2)⁻¹ * f) := by
  have hd0 : delta ≠ 0 := hdelta.ne'
  have hetaC : 0 <= etaC := hetaIn.trans heta
  have hbase : delta ^ etaIn <= 2 * Lpre * f := by
    have h1 := (div_le_iff₀ (by norm_num : (0 : NNReal) < 2)).1 hlam
    have h2 := (div_le_iff₀ hpre).1 hfull
    nlinarith
  have h3 : delta ^ (3 * etaC) <= f := by
    have hpow : delta ^ (3 * etaC) * delta ^ (-(2 * etaC)) <= delta ^ etaIn := by
      rw [← NNReal.rpow_add hd0]
      apply NNReal.rpow_le_rpow_of_exponent_ge hdelta hdelta1
      linarith
    have hf := hbase.trans (mul_le_mul_right' hpreBound f)
    exact (mul_le_mul_iff_left₀ (NNReal.rpow_pos (p := -(2 * etaC)) hdelta)).1 (by
      calc delta ^ (3 * etaC) * delta ^ (-(2 * etaC)) <= delta ^ etaIn := hpow
           _ <= f * delta ^ (-(2 * etaC)) := by simpa [mul_comm] using hf)
  have h6 : delta ^ (6 * etaC) <= outer⁻¹ * ((L1 * L2)⁻¹ * f) := by
    have hloss : outer * (L1 * L2) <= delta ^ (-(3 * etaC)) := by
      calc outer * (L1 * L2) <= delta ^ (-etaC) * (delta ^ (-etaC) * delta ^ (-etaC)) :=
        mul_le_mul' houterBound (mul_le_mul' hL1Bound hL2Bound)
        _ = delta ^ (-(3 * etaC)) := by rw [← NNReal.rpow_add hd0, ← NNReal.rpow_add hd0]; congr 1 <;> ring
    have hh : delta ^ (6 * etaC) * (outer * (L1 * L2)) <= f := by
      calc delta ^ (6 * etaC) * (outer * (L1 * L2)) <=
          delta ^ (6 * etaC) * delta ^ (-(3 * etaC)) := mul_le_mul_left' hloss _
        _ = delta ^ (3 * etaC) := by rw [← NNReal.rpow_add hd0]; congr 1 <;> ring
        _ <= f := h3
    apply (le_div_iff₀ (mul_pos houter (mul_pos hL1 hL2))).2 at hh
    simpa [div_eq_mul_inv, mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh
  refine ⟨h3, h6, le_trans ?_ h6⟩
  have hscale' : rho <= delta ^ (e / 2) := by exact_mod_cast hrhoScale
  calc rho ^ gamma <= (delta ^ (e / 2)) ^ gamma := NNReal.rpow_le_rpow hscale' hgamma.le
    _ = delta ^ (e * gamma / 2) := by rw [← NNReal.rpow_mul]; congr 1 <;> ring
    _ <= delta ^ (6 * etaC) := NNReal.rpow_le_rpow_of_exponent_ge hdelta hdelta1 hgap

/-- The site uses its own positive input gap and the complete three-loss ledger. -/
theorem sourceMiddle_site_fullness_calibration {delta : NNReal}
    {etaL etaIn : Real} {lam Lpre L1 L2 L3 f : NNReal}
    (hdelta : 0 < delta) (hgap : etaIn < etaL)
    (hpre : 0 < Lpre) (hL1 : 0 < L1) (hL2 : 0 < L2) (hL3 : 0 < L3)
    (hlam : delta ^ etaIn / 2 <= lam) (hfull : lam / Lpre <= f)
    (hloss : 2 * Lpre * L1 * L2 * L3 <= delta ^ (-(etaL - etaIn))) :
    delta ^ etaL <= (L1 * L2 * L3)⁻¹ * f := by
  have hbase : delta ^ etaIn <= 2 * Lpre * f := by
    have h1 := (div_le_iff₀ (by norm_num : (0 : NNReal) < 2)).1 hlam
    have h2 := (div_le_iff₀ hpre).1 hfull
    nlinarith
  have hmul : delta ^ etaL * (2 * Lpre * L1 * L2 * L3) <= delta ^ etaIn := by
    calc delta ^ etaL * (2 * Lpre * L1 * L2 * L3) <=
        delta ^ etaL * delta ^ (-(etaL - etaIn)) := mul_le_mul_left' hloss _
      _ = delta ^ etaIn := by rw [← NNReal.rpow_add hdelta.ne']; congr 1 <;> ring
  have hpay : delta ^ etaL * (L1 * L2 * L3) <= f := by
    apply (mul_le_mul_iff_right₀ (mul_pos (by norm_num : (0 : NNReal) < 2) hpre)).1
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul.trans hbase
  have hh := (le_div_iff₀ (mul_pos (mul_pos hL1 hL2) hL3)).2 hpay
  simpa [div_eq_mul_inv, mul_comm] using hh

/-- Both original and outer density charges are paid from the actual ratio row. -/
theorem sourceMiddle_density_calibration {delta rho rhoA rhoB rhoP : NNReal}
    {e beta r kappa P v d : Real} {M : Nat} {Cstar : ENNReal} {outer : NNReal}
    (hdelta : 0 < delta) (hdelta1 : delta <= 1)
    (hrho : 0 < rho) (hrho1 : rho <= 1)
    (hA : 0 < rhoA) (hB : 0 < rhoB) (hP : 0 < rhoP)
    (he : 0 < e) (heHalf : e <= 1 / 2) (hbeta : 0 < beta) (hbeta1 : beta <= 1)
    (hr : 0 <= r) (hkappa : 0 <= kappa) (hP0 : 0 < P)
    (hv : 0 < v) (hd : 0 < d) (hM : 4 / e <= (M : Real))
    (hkP : kappa <= P / 100) (hrP : r <= beta * P / 100)
    (hPv : P <= e * min v d / 1000)
    (hscale : (rho : Real) <= (delta : Real) ^ (e / 2))
    (hratio : rho = rhoB / (2 * rhoP))
    (hwindowRatio : (rhoB : Real) / (rhoP : Real) <=
      (delta : Real) ^ (-2 / (M : Real)) * ((rhoB : Real) / (rhoA : Real)) ^ (1 - e))
    (hC : Cstar <= (delta : ENNReal) ^ (-kappa))
    (houter : outer <= rho ^ (-(sourceMiddleCenter v d / 2))) :
    sourceMiddleDensityExponent e kappa r M < sourceMiddleCenter v d / 2 ∧
      sourceMiddleDensityExponent e kappa r M <= sourceMiddleDensity d - sourceMiddleCenter v d ∧
      Cstar * ENNReal.ofReal (((rhoA : Real) / (rhoB : Real)) ^ r) <=
        (rho : ENNReal) ^ (-sourceMiddleDensityExponent e kappa r M) ∧
      Cstar * ENNReal.ofReal (((rhoA : Real) / (rhoB : Real)) ^ r) <=
        (rho : ENNReal) ^ (-(sourceMiddleDensity d - sourceMiddleCenter v d)) ∧
      (outer : ENNReal) *
          (Cstar * ENNReal.ofReal (((rhoA : Real) / (rhoB : Real)) ^ r)) <=
        (rho : ENNReal) ^ (-sourceMiddleCenter v d) ∧
      outer <= rho ^ (-sourceMiddleCenter v d) := by
  have hd0 : (0 : Real) < delta := by exact_mod_cast hdelta
  have hd1 : (delta : Real) <= 1 := by exact_mod_cast hdelta1
  have hr0 : (0 : Real) < rho := by exact_mod_cast hrho
  have hr1 : (rho : Real) <= 1 := by exact_mod_cast hrho1
  have ha0 : (0 : Real) < rhoA := by exact_mod_cast hA
  have hb0 : (0 : Real) < rhoB := by exact_mod_cast hB
  have hp0 : (0 : Real) < rhoP := by exact_mod_cast hP
  have he1 : 0 < 1 - e := by linarith only [heHalf]
  have hMn : (0 : Real) < M := (div_pos (by norm_num) he).trans_le hM
  have heM : 0 < e * (M : Real) := mul_pos he hMn
  have hfour : 4 <= e * (M : Real) := by
    have hh := (div_le_iff₀ he).mp hM
    nlinarith only [hh]
  have hmesh : 4 / (e * (M : Real)) <= 1 := (div_le_one heM).mpr hfour
  have hmin0 : 0 < min v d := lt_min hv hd
  have hrP' : r <= P / 100 := by nlinarith only [hrP, mul_le_mul_of_nonneg_right hbeta1 hP0.le]
  have hkbound : 2 * kappa / e <= min v d / 50000 := by
    apply (div_le_iff₀ he).mpr
    nlinarith only [hkP, hPv]
  have hrbound : r <= min v d / 100000 := by
    have hP' : P <= min v d / 1000 := by
      nlinarith only [hPv, mul_le_mul_of_nonneg_right (show e <= 1 by linarith only [heHalf]) hmin0.le]
    linarith only [hP', hrP']
  have hrdiv : r / (1 - e) <= 2 * r := by
    apply (div_le_iff₀ he1).mpr
    nlinarith only [hr, heHalf]
  have hrterm : r / (1 - e) * (1 + 4 / (e * (M : Real))) <= 4 * r := by
    have hfirst : 0 <= r / (1 - e) := div_nonneg hr he1.le
    nlinarith only [hrdiv, mul_le_mul_of_nonneg_left hmesh hfirst]
  have hexp : sourceMiddleDensityExponent e kappa r M <= 3 * min v d / 50000 := by
    dsimp [sourceMiddleDensityExponent]
    nlinarith only [hkbound, hrterm, hrbound]
  have hstrict : sourceMiddleDensityExponent e kappa r M < sourceMiddleCenter v d / 2 := by
    dsimp [sourceMiddleCenter]
    linarith only [hexp, hmin0]
  have hdenexp : sourceMiddleDensityExponent e kappa r M <=
      sourceMiddleDensity d - sourceMiddleCenter v d := by
    have hh := hstrict
    dsimp [sourceMiddleDensity, sourceMiddleCenter] at hh ⊢
    linarith only [hh, min_le_right v d, hmin0]
  have hlogdelta : Real.log (delta : Real) <= 0 := Real.log_nonpos hd0.le hd1
  have hlogrho : Real.log (rho : Real) <= 0 := Real.log_nonpos hr0.le hr1
  have hlogscale : Real.log (rho : Real) <= e / 2 * Real.log (delta : Real) := by
    have hh := Real.log_le_log hr0 hscale
    rwa [Real.log_rpow hd0] at hh
  have hlogratio : Real.log ((rhoB : Real) / (rhoP : Real)) =
      Real.log 2 + Real.log (rho : Real) := by
    have heq : (rhoB : Real) / (rhoP : Real) = 2 * (rho : Real) := by
      have hh : (rho : Real) = (rhoB : Real) / (2 * (rhoP : Real)) := by exact_mod_cast hratio
      rw [hh]
      field_simp
    rw [heq, Real.log_mul (by norm_num) hr0.ne']
  have hlogwindow : (1 - e) * Real.log ((rhoA : Real) / (rhoB : Real)) <=
      -2 / (M : Real) * Real.log (delta : Real) - Real.log (rho : Real) := by
    have hh := Real.log_le_log (div_pos hb0 hp0) hwindowRatio
    rw [Real.log_mul (Real.rpow_pos_of_pos hd0 _).ne'
      (Real.rpow_pos_of_pos (div_pos hb0 ha0) _).ne', Real.log_rpow hd0,
      Real.log_rpow (div_pos hb0 ha0), hlogratio,
      Real.log_div hb0.ne' ha0.ne'] at hh
    rw [Real.log_div ha0.ne' hb0.ne']
    nlinarith only [hh, Real.log_pos (by norm_num : (1 : Real) < 2)]
  have hlogdeltaBound : -2 / (M : Real) * Real.log (delta : Real) <=
      -(4 / (e * (M : Real))) * Real.log (rho : Real) := by
    apply (mul_le_mul_iff_right₀ heM).1
    field_simp [he.ne', hMn.ne']
    nlinarith only [hlogscale]
  have hlogAB : Real.log ((rhoA : Real) / (rhoB : Real)) <=
      -((1 + 4 / (e * (M : Real))) / (1 - e)) * Real.log (rho : Real) := by
    have hh := hlogwindow.trans (sub_le_sub_right hlogdeltaBound (Real.log (rho : Real)))
    calc
      _ <= (-(4 / (e * (M : Real))) * Real.log (rho : Real) - Real.log (rho : Real)) / (1 - e) := by
        apply (le_div_iff₀ he1).2
        nlinarith only [hh]
      _ = _ := by ring
  have hratioPower : ((rhoA : Real) / (rhoB : Real)) ^ r <=
      (rho : Real) ^ (-(r / (1 - e) * (1 + 4 / (e * (M : Real))))) := by
    rw [Real.rpow_def_of_pos (div_pos ha0 hb0), Real.rpow_def_of_pos hr0]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hlogAB hr
    calc Real.log ((rhoA : Real) / (rhoB : Real)) * r <=
        -((1 + 4 / (e * (M : Real))) / (1 - e)) * Real.log (rho : Real) * r := hh
      _ = _ := by ring
  have hCPower : (delta : Real) ^ (-kappa) <= (rho : Real) ^ (-(2 * kappa / e)) := by
    rw [Real.rpow_def_of_pos hd0, Real.rpow_def_of_pos hr0]
    apply Real.exp_le_exp.mpr
    apply (mul_le_mul_iff_right₀ he).1
    have hh := mul_le_mul_of_nonneg_left hlogscale hkappa
    field_simp [he.ne']
    nlinarith only [hh]
  have hrE0 : (rho : ENNReal) ≠ 0 := by exact_mod_cast hrho.ne'
  have hrE1 : (rho : ENNReal) <= 1 := by exact_mod_cast hrho1
  have hrealENN (x : NNReal) (hx : 0 < x) (t : Real) :
      ENNReal.ofReal ((x : Real) ^ t) = (x : ENNReal) ^ t := by
    rw [← NNReal.coe_rpow, ENNReal.ofReal_coe_nnreal, ENNReal.coe_rpow_of_ne_zero hx.ne']
  have hC' : Cstar <= (rho : ENNReal) ^ (-(2 * kappa / e)) :=
    hC.trans (by simpa only [hrealENN delta hdelta, hrealENN rho hrho] using ENNReal.ofReal_le_ofReal hCPower)
  have hpower : Cstar * ENNReal.ofReal (((rhoA : Real) / (rhoB : Real)) ^ r) <=
      (rho : ENNReal) ^ (-sourceMiddleDensityExponent e kappa r M) := by
    have habE : ENNReal.ofReal (((rhoA : Real) / (rhoB : Real)) ^ r) <=
        (rho : ENNReal) ^ (-(r / (1 - e) * (1 + 4 / (e * (M : Real))))) := by
      simpa only [hrealENN rho hrho] using ENNReal.ofReal_le_ofReal hratioPower
    calc _ <= (rho : ENNReal) ^ (-(2 * kappa / e)) *
        (rho : ENNReal) ^ (-(r / (1 - e) * (1 + 4 / (e * (M : Real))))) := mul_le_mul' hC' habE
      _ = _ := by
        rw [← ENNReal.rpow_add _ _ hrE0 ENNReal.coe_ne_top]
        congr 1
        dsimp [sourceMiddleDensityExponent]
        ring
  refine ⟨hstrict, hdenexp, hpower,
    hpower.trans (ENNReal.rpow_le_rpow_of_exponent_ge hrE1 (by linarith only [hdenexp])), ?_, ?_⟩
  · have ho : (outer : ENNReal) <= (rho : ENNReal) ^ (-(sourceMiddleCenter v d / 2)) := by
      have hc := ENNReal.coe_le_coe.mpr houter
      rwa [ENNReal.coe_rpow_of_ne_zero hrho.ne'] at hc
    calc _ <= (rho : ENNReal) ^ (-(sourceMiddleCenter v d / 2)) *
        (rho : ENNReal) ^ (-sourceMiddleDensityExponent e kappa r M) := mul_le_mul' ho hpower
      _ = (rho : ENNReal) ^ (-(sourceMiddleCenter v d / 2) - sourceMiddleDensityExponent e kappa r M) := by
        rw [← ENNReal.rpow_add _ _ hrE0 ENNReal.coe_ne_top]; rfl
      _ <= _ := ENNReal.rpow_le_rpow_of_exponent_ge hrE1 (by linarith only [hstrict])
  · apply houter.trans
    apply NNReal.rpow_le_rpow_of_exponent_ge hrho hrho1
    dsimp [sourceMiddleCenter]
    linarith only [hmin0]

/-- All thresholds precede delta and the uniformly bounded cardinalities and scales.
The preparation owner must prove the exact Lpre subpower row for its fixed tower. -/
theorem sourceMiddle_exists_uniform_threshold (N : Nat) {e etaC etaL etaIn R : Real}
    (he : 0 < e) (hetaC : 0 < etaC) (hgap : etaIn < etaL) (hR : 1 <= R)
    (q etaD : Nat -> Real) (hq : forall m, m < N -> 0 < q m)
    (hetaD : forall m, m < N -> 0 < etaD m)
    (beta varpi : Real) (zeta gain : Nat -> Real)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace Real (Fin 3)) beta)
    (hFrostman : FrostmanEstimate.{u} (EuclideanSpace Real (Fin 3)) beta)
    (hVNS : forall m, m < N -> VNSBody.{u} beta varpi (zeta m) (gain m) (etaD m))
    (rhoCeiling : Nat -> NNReal) (hceil : forall m, m < N -> 0 < rhoCeiling m)
    (Lpre : NNReal -> NNReal)
    (hpre : forall kappa : Real, 0 < kappa ->
      ∀ᶠ delta : NNReal in 𝓝[>] 0, Lpre delta <= delta ^ (-kappa)) :
    exists delta0 : NNReal, 0 < delta0 ∧ delta0 <= 1 ∧
      forall delta : NNReal, 0 < delta -> delta <= delta0 ->
        2 * Lpre delta <= delta ^ (-(2 * etaC)) ∧
        outerLoss R <= delta ^ (-etaC) ∧
        (forall (n : Nat), 0 < n -> (n : NNReal) <= delta ^ (-(4 : Real)) ->
          forall sigma : NNReal, delta <= sigma -> sigma <= 1 ->
            spineScaleLoss 3 n sigma <= delta ^ (-etaC)) ∧
        (forall n1 n2 n3 : Nat, 0 < n1 -> 0 < n2 -> 0 < n3 ->
          (n1 : NNReal) <= delta ^ (-(4 : Real)) ->
          (n2 : NNReal) <= delta ^ (-(4 : Real)) ->
          (n3 : NNReal) <= delta ^ (-(4 : Real)) ->
          forall sigma1 sigma2 sigma3 : NNReal,
            delta <= sigma1 -> sigma1 <= 1 -> delta <= sigma2 -> sigma2 <= 1 ->
            delta <= sigma3 -> sigma3 <= 1 ->
            2 * Lpre delta * spineScaleLoss 3 n1 sigma1 * spineScaleLoss 3 n2 sigma2 *
              spineScaleLoss 3 n3 sigma3 <= delta ^ (-(etaL - etaIn))) ∧
        (forall m, m < N -> forall rho : NNReal, 0 < rho ->
          (rho : Real) <= (delta : Real) ^ (e / 2) / 2 ->
          rho <= rhoCeiling m ∧ rho <= 1 / 20 ∧
            outerLoss R <= rho ^ (-(q m / 2)) ∧
            ShadedTube.ssfUniformConst 3 <= rho ^ (-(etaD m)) ∧
            Lemma91At.{u} beta varpi (zeta m) (gain m) (etaD m) rho) := by
  classical
  let k : Real := (etaL - etaIn) / 5
  have hk : 0 < k := by dsimp [k]; linarith
  have hconst (C : NNReal) (alpha : Real) (ha : 0 < alpha) :
      ∀ᶠ delta : NNReal in 𝓝[>] 0, C <= delta ^ (-alpha) := by
    obtain ⟨d0, hd0, hbound⟩ := exists_threshold_const_le_rpow_neg (C := max 1 C)
      (le_max_left _ _) ha
    filter_upwards [Ioo_mem_nhdsGT hd0] with delta hdelta
    exact (le_max_right _ _).trans (hbound delta hdelta.1 hdelta.2.le)
  have hrows (m : Nat) (hm : m < N) :
      ∀ᶠ delta : NNReal in 𝓝[>] 0,
        forall rho : NNReal, 0 < rho ->
          (rho : Real) <= (delta : Real) ^ (e / 2) / 2 ->
          rho <= rhoCeiling m ∧ rho <= 1 / 20 ∧
            outerLoss R <= rho ^ (-(q m / 2)) ∧
            ShadedTube.ssfUniformConst 3 <= rho ^ (-(etaD m)) ∧
            Lemma91At.{u} beta varpi (zeta m) (gain m) (etaD m) rho := by
    obtain ⟨ro, hro, ho⟩ := exists_threshold_const_le_rpow_neg
      (C := outerLoss R) (one_le_outerLoss hR) (div_pos (hq m hm) (by norm_num : (0 : Real) < 2))
    obtain ⟨ru, hru, hu⟩ := exists_threshold_const_le_rpow_neg
      (C := max 1 (ShadedTube.ssfUniformConst 3)) (le_max_left _ _) (hetaD m hm)
    obtain ⟨rv, hrv, h91⟩ := exists_threshold_lemma91At (hVNS m hm) hKT hFrostman
    let r0 := min (rhoCeiling m) (min (1 / 20) (min ro (min ru rv)))
    have hr0 : 0 < r0 := lt_min (hceil m hm) (lt_min (by norm_num)
      (lt_min hro (lt_min hru hrv)))
    have hd0 : 0 < r0 ^ (2 / e) := NNReal.rpow_pos hr0
    filter_upwards [Ioo_mem_nhdsGT hd0] with delta hdelta
    intro rho hrho hscale
    have hp : delta ^ (e / 2) <= r0 := by
      calc delta ^ (e / 2) <= (r0 ^ (2 / e)) ^ (e / 2) :=
        NNReal.rpow_le_rpow hdelta.2.le (by positivity)
        _ = r0 := by
          rw [← NNReal.rpow_mul, show 2 / e * (e / 2) = 1 by field_simp, NNReal.rpow_one]
    have hs : rho <= r0 := by
      have hs' : (rho : Real) <= (delta : Real) ^ (e / 2) :=
        hscale.trans (div_le_self (Real.rpow_nonneg delta.coe_nonneg _) (by norm_num))
      have hs'' : rho <= delta ^ (e / 2) := by exact_mod_cast hs'
      exact hs''.trans hp
    have h0 := (le_min_iff.mp hs).1
    have h1 := le_min_iff.mp (le_min_iff.mp hs).2
    have h2 := le_min_iff.mp h1.2
    have h3 := le_min_iff.mp h2.2
    exact ⟨h0, h1.1, ho rho hrho h2.1,
      (le_max_right _ _).trans (hu rho hrho h3.1), h91 rho hrho h3.2⟩
  have hall : ∀ᶠ delta : NNReal in 𝓝[>] 0, forall m, m < N ->
      forall rho : NNReal, 0 < rho -> (rho : Real) <= (delta : Real) ^ (e / 2) / 2 ->
        rho <= rhoCeiling m ∧ rho <= 1 / 20 ∧ outerLoss R <= rho ^ (-(q m / 2)) ∧
          ShadedTube.ssfUniformConst 3 <= rho ^ (-(etaD m)) ∧
          Lemma91At.{u} beta varpi (zeta m) (gain m) (etaD m) rho := by
    have hh := (Filter.eventually_all.mpr (fun m : Fin N => hrows m.val m.isLt))
    filter_upwards [hh] with delta hdelta
    intro m hm
    exact hdelta ⟨m, hm⟩
  have hevent := (hpre etaC hetaC).and ((hpre k hk).and
    ((ML2Core.eventually_spineScaleLoss_le 3 hetaC).and
      ((ML2Core.eventually_spineScaleLoss_le 3 hk).and
        ((hconst 2 etaC hetaC).and ((hconst 2 k hk).and
          ((hconst (outerLoss R) etaC hetaC).and hall))))))
  have hfinal : ∀ᶠ delta : NNReal in 𝓝[>] 0,
      delta <= 1 ∧
      2 * Lpre delta <= delta ^ (-(2 * etaC)) ∧ outerLoss R <= delta ^ (-etaC) ∧
      (forall (n : Nat), 0 < n -> (n : NNReal) <= delta ^ (-(4 : Real)) ->
        forall sigma : NNReal, delta <= sigma -> sigma <= 1 ->
          spineScaleLoss 3 n sigma <= delta ^ (-etaC)) ∧
      (forall n1 n2 n3 : Nat, 0 < n1 -> 0 < n2 -> 0 < n3 ->
        (n1 : NNReal) <= delta ^ (-(4 : Real)) -> (n2 : NNReal) <= delta ^ (-(4 : Real)) ->
        (n3 : NNReal) <= delta ^ (-(4 : Real)) -> forall sigma1 sigma2 sigma3 : NNReal,
          delta <= sigma1 -> sigma1 <= 1 -> delta <= sigma2 -> sigma2 <= 1 ->
          delta <= sigma3 -> sigma3 <= 1 ->
          2 * Lpre delta * spineScaleLoss 3 n1 sigma1 * spineScaleLoss 3 n2 sigma2 *
            spineScaleLoss 3 n3 sigma3 <= delta ^ (-(etaL - etaIn))) ∧
      (forall m, m < N -> forall rho : NNReal, 0 < rho ->
        (rho : Real) <= (delta : Real) ^ (e / 2) / 2 ->
          rho <= rhoCeiling m ∧ rho <= 1 / 20 ∧ outerLoss R <= rho ^ (-(q m / 2)) ∧
          ShadedTube.ssfUniformConst 3 <= rho ^ (-(etaD m)) ∧
          Lemma91At.{u} beta varpi (zeta m) (gain m) (etaD m) rho) := by
    filter_upwards [hevent, Ioo_mem_nhdsGT (zero_lt_one : (0 : NNReal) < 1)] with delta hs hd
    obtain ⟨hpreC, hpreK, hsplitC, hsplitK, h2C, h2K, houter, hrow⟩ := hs
    refine ⟨hd.2.le, ?_, houter, hsplitC, ?_, hrow⟩
    · calc 2 * Lpre delta <= delta ^ (-etaC) * delta ^ (-etaC) := mul_le_mul' h2C hpreC
        _ = _ := by rw [← NNReal.rpow_add hd.1.ne']; congr 1; ring
    · intro n1 n2 n3 hn1 hn2 hn3 hc1 hc2 hc3 s1 s2 s3 hs1 hs11 hs2 hs21 hs3 hs31
      calc 2 * Lpre delta * spineScaleLoss 3 n1 s1 * spineScaleLoss 3 n2 s2 * spineScaleLoss 3 n3 s3 <=
          delta ^ (-k) * delta ^ (-k) * delta ^ (-k) * delta ^ (-k) * delta ^ (-k) :=
        mul_le_mul' (mul_le_mul' (mul_le_mul' (mul_le_mul' h2K hpreK)
          (hsplitK n1 hn1 hc1 s1 hs1 hs11)) (hsplitK n2 hn2 hc2 s2 hs2 hs21))
            (hsplitK n3 hn3 hc3 s3 hs3 hs31)
        _ = _ := by
          rw [← NNReal.rpow_add hd.1.ne', ← NNReal.rpow_add hd.1.ne',
            ← NNReal.rpow_add hd.1.ne', ← NNReal.rpow_add hd.1.ne']
          congr 1
          dsimp [k]
          ring
  obtain ⟨delta0, hd0, hbound⟩ := exists_threshold_of_eventually_nhdsGT hfinal
  refine ⟨delta0, hd0, (hbound delta0 hd0 le_rfl).1, ?_⟩
  intro delta hdelta hsmall
  exact (hbound delta hdelta hsmall).2

end Kakeya.ML2Assembly
