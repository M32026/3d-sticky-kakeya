import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.StickyMultiplicity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.HighMultiplicityMassBound
import Mathlib.Tactic

/-!
# Paper high-multiplicity refinement for the Pure hierarchy

This is the dyadic high/low-band argument used in the WZ1 one-scale proof,
with the paper-body mass floor supplied explicitly.
-/

noncomputable section

open MeasureTheory Set Finset

namespace Kakeya.Assouad

private lemma pureWZ2_realRpowENN_mul {delta a b : ℝ} (hdelta : 0 < delta) :
    Kakeya.realRpowENN delta a * Kakeya.realRpowENN delta b =
    Kakeya.realRpowENN delta (a + b) := by
  simp only [Kakeya.realRpowENN]
  have h1 : Real.rpow delta (a + b) =
      Real.rpow delta a * Real.rpow delta b :=
    Real.rpow_add hdelta a b
  have ha : 0 ≤ Real.rpow delta a :=
    Real.rpow_nonneg hdelta.le a
  have h_main : ENNReal.ofReal (Real.rpow delta (a + b)) =
      ENNReal.ofReal (Real.rpow delta a) *
        ENNReal.ofReal (Real.rpow delta b) := by
    rw [h1]
    exact ENNReal.ofReal_mul ha
  exact h_main.symm

private lemma pureWZ2_low_multiplicity_mass_bound
    {BF : Kakeya.Streamlined.BodyFamily}
    (Y : Kakeya.Streamlined.Shading BF)
    (S : Set Point3) (hS : MeasurableSet S)
    (M : ENNReal)
    (hM : ∀ p ∈ S, (Y.pointMultiplicity p : ENNReal) ≤ M) :
    ∑ i : Fin BF.card, volume (Y.carrier i ∩ S) ≤ M * volume S := by
  rw [sum_volume_inter_eq_setLIntegral_pointMultiplicity Y hS]
  calc
    (∫⁻ p in S, (Y.pointMultiplicity p : ENNReal)) ≤
        ∫⁻ _p in S, M := setLIntegral_mono' hS hM
    _ = M * volume S := by rw [setLIntegral_const]

private lemma pureWZ2_paperDyadicBands_disjoint
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading family}
    {first second : ℕ} (hne : first ≠ second) :
    Disjoint (wz1PaperDyadicMultiplicityBand Y first)
      (wz1PaperDyadicMultiplicityBand Y second) := by
  apply Set.disjoint_left.mpr
  intro point hfirst hsecond
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hpowers : (2 ^ (first + 1) : ENNReal) ≤ (2 ^ second : ENNReal) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
    exact (not_le_of_gt hfirst.2) (hpowers.trans hsecond.1)
  · have hpowers : (2 ^ (second + 1) : ENNReal) ≤ (2 ^ first : ENNReal) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
    exact (not_le_of_gt hsecond.2) (hpowers.trans hfirst.1)

lemma pureWZ2_paper_fine_multiplicity_refinement_with_band
    {delta sigma epsilon eta : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hepsilon : 0 < epsilon)
    (heta : 0 < eta) (heta_3le : 3 * eta < epsilon)
    {family : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading family}
    (hfamily_nonempty : family.Nonempty)
    (hfamily_mass_lower : Kakeya.realRpowENN delta (2 * eta) ≤
      (wz1PaperBodyFamily family).mass)
    (hfamily_mass_ne_top : (wz1PaperBodyFamily family).mass ≠ ⊤)
    (hY_cubical : WZ1PaperIsCubicalShading Y)
    (hY_dense :
      Y.IsLambdaDense (Kakeya.realRpowENN delta eta))
    (hY_vol_upper :
      MeasureTheory.volume Y.union ≤
        Kakeya.realRpowENN delta (sigma - eta))
    (h_card_bound : 2 * (Nat.log 2 family.card + 1 : ENNReal) ≤
        Kakeya.realRpowENN delta (eta - epsilon))
    (h_mass_ineq : Kakeya.realRpowENN delta (3 * eta) ≥
        4 * Kakeya.realRpowENN delta (epsilon - eta)) :
    ∃ (refined : WZ1PaperTubeShading family) (m level : ℕ),
      PureWZ2PaperIsSubshading refined Y ∧
      WZ1PaperIsCubicalShading refined ∧
      0 < m ∧
      m = 2 ^ level ∧
      refined.HasConstantMultiplicity m (2 * m) ∧
      Kakeya.realRpowENN delta (-sigma + epsilon) ≤ (m : ENNReal) ∧
      refined.mass ≥ Kakeya.realRpowENN delta epsilon *
        (wz1PaperBodyFamily family).mass ∧
      refined = wz1PaperDyadicBandSubshading Y level := by
  let hdelta_pos := hdelta
  let hdelta_le_one := hdelta_one

  have hY_mass_lower : Kakeya.realRpowENN delta eta * (wz1PaperBodyFamily family).mass ≤ Y.mass := hY_dense
  have hY_vol_upper' : volume Y.union ≤ Kakeya.realRpowENN delta (sigma - eta) := hY_vol_upper

  let M : ENNReal := Kakeya.realRpowENN delta (-sigma + epsilon)

  have h_M_vol_le : M * volume Y.union ≤ Kakeya.realRpowENN delta (epsilon - eta) := by
    calc
      M * volume Y.union
        ≤ M * Kakeya.realRpowENN delta (sigma - eta) := by gcongr
      _ = Kakeya.realRpowENN delta (epsilon - eta) := by
        rw [pureWZ2_realRpowENN_mul hdelta_pos] <;> ring_nf

  have hN_pos : 0 < family.card := hfamily_nonempty
  let K : ℕ := Nat.log 2 family.card
  have hK_le : (2 : ℕ) ^ K ≤ family.card :=
    Nat.pow_log_le_self 2 hN_pos.ne'
  have hK_lt : family.card < (2 : ℕ) ^ (K + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) family.card

  let highBands := (Finset.range (K + 1)).filter (fun l => M ≤ (2 ^ l : ENNReal))
  let lowBands := (Finset.range (K + 1)).filter (fun l => ¬(M ≤ (2 ^ l : ENNReal)))

  have h_disj : Disjoint highBands lowBands := by
    rw [Finset.disjoint_left]
    intro l hl1 hl2
    have h1 := (Finset.mem_filter.mp hl1).2
    have h2 := (Finset.mem_filter.mp hl2).2
    exact h2 h1

  have h_union : highBands ∪ lowBands = Finset.range (K + 1) := by
    ext l
    simp only [highBands, lowBands, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    <;> by_cases h : M ≤ (2 ^ l : ENNReal) <;> simp [h] <;> tauto

  have h_bands_cover : ∑ l ∈ Finset.range (K + 1), (wz1PaperDyadicBandSubshading Y l).mass = Y.mass :=
    (paperDyadicBands_mass_sum (shading := Y)).symm

  -- Each low band has mass ≤ 2M * volume(band)
  have h_each_low_le : ∀ l ∈ lowBands,
      (wz1PaperDyadicBandSubshading Y l).mass ≤ 2 * M * volume (wz1PaperDyadicMultiplicityBand Y l) := by
    intro l hl
    have h_lt : (2 ^ l : ENNReal) < M := lt_of_not_ge (Finset.mem_filter.mp hl).2
    have h_up : (2 ^ (l + 1) : ENNReal) ≤ 2 * M := by
      calc (2 ^ (l + 1) : ENNReal) = 2 * (2 ^ l : ENNReal) := by simp [pow_succ] <;> ring
           _ ≤ 2 * M := by gcongr
    let S := wz1PaperDyadicMultiplicityBand Y l
    have hS_meas : MeasurableSet S :=
      wz1PaperDyadicMultiplicityBand_measurable Y l
    have h_mult_le : ∀ p ∈ S, (Y.pointMultiplicity p : ENNReal) ≤ 2 * M := by
      intro p hp
      have h : (Y.pointMultiplicity p : ENNReal) < (2 ^ (l + 1) : ENNReal) := hp.2
      exact (h.trans_le h_up).le
    have h := pureWZ2_low_multiplicity_mass_bound Y S hS_meas (2 * M) h_mult_le
    simpa [S, wz1PaperDyadicBandSubshading,
      Kakeya.Streamlined.Shading.mass] using h

  -- Low-band total mass ≤ 2M * volume(Y.union) ≤ 2δ^(ε-η)
  have h_low_band_mass_le :
      ∑ l ∈ lowBands, (wz1PaperDyadicBandSubshading Y l).mass ≤ 2 * Kakeya.realRpowENN delta (epsilon - eta) := by
    have h1 : ∑ l ∈ lowBands, (wz1PaperDyadicBandSubshading Y l).mass ≤
        ∑ l ∈ lowBands, (2 * M * volume (wz1PaperDyadicMultiplicityBand Y l)) := by
      apply Finset.sum_le_sum
      intro l hl
      exact h_each_low_le l hl
    have h2 : ∑ l ∈ lowBands, (2 * M * volume (wz1PaperDyadicMultiplicityBand Y l)) =
        2 * M * ∑ l ∈ lowBands, volume (wz1PaperDyadicMultiplicityBand Y l) := by
      rw [Finset.mul_sum]
      <;> rfl
    rw [h2] at h1
    have h3 : ∑ l ∈ lowBands, volume (wz1PaperDyadicMultiplicityBand Y l) ≤ volume Y.union := by
      have h_disj2 : Set.PairwiseDisjoint (lowBands : Set ℕ) (fun l => wz1PaperDyadicMultiplicityBand Y l) := by
        intro l _ m _ hne; exact pureWZ2_paperDyadicBands_disjoint hne
      have h4 : volume (⋃ l ∈ lowBands, wz1PaperDyadicMultiplicityBand Y l) =
          ∑ l ∈ lowBands, volume (wz1PaperDyadicMultiplicityBand Y l) := by
        rw [MeasureTheory.measure_biUnion_finset h_disj2
          (fun l _ => wz1PaperDyadicMultiplicityBand_measurable Y l)]
        <;> rfl
      have h5 : (⋃ l ∈ lowBands, wz1PaperDyadicMultiplicityBand Y l) ⊆ Y.union := by
        intro p hp
        rcases Set.mem_iUnion₂.mp hp with ⟨l, _, hband⟩
        have h_pos_mult : 0 < Y.pointMultiplicity p := by
          have h1 : (2 ^ l : ENNReal) ≤ (Y.pointMultiplicity p : ENNReal) := hband.1
          have h2 : (0 : ENNReal) < (2 ^ l : ENNReal) := by positivity
          exact_mod_cast h2.trans_le h1
        classical
        let S := Finset.univ.filter (fun i : Fin family.card => p ∈ Y.carrier i)
        have hS : Y.pointMultiplicity p = S.card := by rfl
        have hS_pos : 0 < S.card := by rw [←hS]; exact h_pos_mult
        have hS_nonempty : S.Nonempty := Finset.card_pos.mp hS_pos
        rcases hS_nonempty with ⟨i, hi⟩
        have h_i : p ∈ Y.carrier i := (Finset.mem_filter.mp hi).2
        simpa [Kakeya.Streamlined.Shading.union] using ⟨i, h_i⟩
      calc
        ∑ l ∈ lowBands, volume (wz1PaperDyadicMultiplicityBand Y l)
          = volume (⋃ l ∈ lowBands, wz1PaperDyadicMultiplicityBand Y l) := h4.symm
        _ ≤ volume Y.union := by gcongr
    calc
      ∑ l ∈ lowBands, (wz1PaperDyadicBandSubshading Y l).mass
        ≤ 2 * M * ∑ l ∈ lowBands, volume (wz1PaperDyadicMultiplicityBand Y l) := h1
      _ ≤ 2 * M * volume Y.union := by gcongr
      _ = 2 * (M * volume Y.union) := by ring
      _ ≤ 2 * Kakeya.realRpowENN delta (epsilon - eta) := by gcongr

  -- Main argument: either a good high band exists, or contradiction
  by_cases h_goal : ∃ k ∈ highBands,
      (wz1PaperDyadicBandSubshading Y k).mass ≥ Kakeya.realRpowENN delta epsilon * (wz1PaperBodyFamily family).mass
  · -- Good case
    rcases h_goal with ⟨k, hk_in, h_mass⟩
    have h_k_lower : M ≤ (2 ^ k : ENNReal) := (Finset.mem_filter.mp hk_in).2
    let refined := wz1PaperDyadicBandSubshading Y k
    let m : ℕ := 2 ^ k
    have h_subshading : PureWZ2PaperIsSubshading refined Y := wz1PaperDyadicBandSubshading_isSubshading Y k
    have h_m_pos : 0 < m := by positivity
    have h_mult_eq : ∀ p ∈ refined.union, refined.pointMultiplicity p = Y.pointMultiplicity p := by
      intro p hp
      rcases hp with ⟨i, hi⟩
      have hband : p ∈ wz1PaperDyadicMultiplicityBand Y k := hi.2
      classical
      simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
      congr 1
      apply Finset.filter_congr
      intro j _
      simp [refined, wz1PaperDyadicBandSubshading, hband]
    have h_const_mult : refined.HasConstantMultiplicity m (2 * m) := by
      intro p hp
      have hband : p ∈ wz1PaperDyadicMultiplicityBand Y k := by rcases hp with ⟨i, hi⟩; exact hi.2
      have h_eq : refined.pointMultiplicity p = Y.pointMultiplicity p := h_mult_eq p hp
      rw [h_eq]
      have h1 : m ≤ Y.pointMultiplicity p := by exact_mod_cast hband.1
      have h2 : Y.pointMultiplicity p ≤ 2 * m := by
        have h3 : (Y.pointMultiplicity p : ENNReal) < (2 ^ (k + 1) : ENNReal) := hband.2
        have h4 : (2 ^ (k + 1) : ENNReal) = (2 * m : ENNReal) := by simp [m, pow_succ] <;> ring
        rw [h4] at h3; exact_mod_cast h3.le
      exact ⟨h1, h2⟩
    have h_mult_lower : M ≤ (m : ENNReal) := by simpa [m] using h_k_lower
    have h_refined_mass : refined.mass =
        (wz1PaperDyadicBandSubshading Y k).mass := rfl
    exact ⟨refined, m, k, h_subshading,
      hY_cubical.dyadicBandSubshading k, h_m_pos, rfl, h_const_mult,
      h_mult_lower, by rw [h_refined_mass]; exact h_mass, rfl⟩
  · -- Contradiction case
    have h_all_small : ∀ k ∈ highBands,
        (wz1PaperDyadicBandSubshading Y k).mass < Kakeya.realRpowENN delta epsilon * (wz1PaperBodyFamily family).mass := by
      intro k hk; by_contra h; exact h_goal ⟨k, hk, le_of_not_gt h⟩
    let highSum := ∑ l ∈ highBands, (wz1PaperDyadicBandSubshading Y l).mass
    let lowSum := ∑ l ∈ lowBands, (wz1PaperDyadicBandSubshading Y l).mass
    let A := (K + 1 : ENNReal) * Kakeya.realRpowENN delta epsilon * (wz1PaperBodyFamily family).mass
    let B := 2 * Kakeya.realRpowENN delta (epsilon - eta)

    have hK_log : K = Nat.log 2 family.card := by
      have h1 : K ≤ Nat.log 2 family.card := by
        have h_not_lt : ¬(Nat.log 2 family.card < K) := by
          rw [Nat.log_lt_iff_lt_pow (by norm_num) (show family.card ≠ 0 from by linarith)]
          exact not_lt.mpr hK_le
        omega
      have h2 : Nat.log 2 family.card ≤ K := by
        have h_lt : Nat.log 2 family.card < K + 1 := by
          rw [Nat.log_lt_iff_lt_pow (by norm_num) (show family.card ≠ 0 from by linarith)]
          exact hK_lt
        omega
      omega

    have h3 : 2 * (K + 1 : ENNReal) ≤ Kakeya.realRpowENN delta (eta - epsilon) := by
      simpa [hK_log] using h_card_bound

    have hfin_rpow : ∀ (x : ℝ), Kakeya.realRpowENN delta x ≠ ⊤ := by
      intro x; simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]

    have hF_mass_fin : (wz1PaperBodyFamily family).mass ≠ ⊤ :=
      hfamily_mass_ne_top

    have hA_fin : A ≠ ⊤ := by
      dsimp only [A]
      apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top <;> simp [hfin_rpow]
      · exact hF_mass_fin

    have hB_fin : B ≠ ⊤ := by
      dsimp only [B]
      apply ENNReal.mul_ne_top
      · simp
      · exact hfin_rpow (epsilon - eta)

    have hK1_pos : 0 < (K + 1 : ENNReal) := by positivity
    have heps_pos : 0 < Kakeya.realRpowENN delta epsilon := by
      apply ENNReal.ofReal_pos.mpr
      exact Real.rpow_pos_of_pos hdelta_pos epsilon

    have h_high_lt_A : highSum < A := by
      by_cases hne : highBands.Nonempty
      · have h_sum_const : ∑ i ∈ highBands, (Kakeya.realRpowENN delta epsilon * (wz1PaperBodyFamily family).mass) =
            (highBands.card : ENNReal) * Kakeya.realRpowENN delta epsilon * (wz1PaperBodyFamily family).mass := by
          rw [Finset.sum_const, mul_assoc] <;> ring
        have h1 : highSum < (highBands.card : ENNReal) * Kakeya.realRpowENN delta epsilon * (wz1PaperBodyFamily family).mass := by
          have h1' := ENNReal.sum_lt_sum_of_nonempty hne h_all_small
          rw [h_sum_const] at h1'
          exact h1'
        have h2 : (highBands.card : ENNReal) ≤ (K + 1 : ENNReal) := by
          have h_sub : highBands ⊆ Finset.range (K + 1) := by
            simp [highBands] <;> tauto
          have h_card : highBands.card ≤ (Finset.range (K + 1)).card := Finset.card_le_card h_sub
          have h_range : (Finset.range (K + 1)).card = K + 1 := Finset.card_range (K + 1)
          rw [h_range] at h_card
          exact_mod_cast h_card
        have h3 : (highBands.card : ENNReal) * Kakeya.realRpowENN delta epsilon * (wz1PaperBodyFamily family).mass ≤ A := by
          dsimp only [A]; gcongr
        exact h1.trans_le h3
      · have h_empty : highBands = ∅ := by simpa [Finset.nonempty_iff_ne_empty] using hne
        have h4 : highSum = 0 := by
          dsimp only [highSum]
          rw [h_empty]
          simp
        rw [h4]
        dsimp only [A]
        have h_pos3 : 0 < (wz1PaperBodyFamily family).mass := by
          have h : Kakeya.realRpowENN delta (2 * eta) ≤
              (wz1PaperBodyFamily family).mass := hfamily_mass_lower
          have h' : 0 < Kakeya.realRpowENN delta (2 * eta) := by
            apply ENNReal.ofReal_pos.mpr
            exact Real.rpow_pos_of_pos hdelta_pos (2 * eta)
          exact h'.trans_le h
        have h4 : ((K + 1 : ENNReal) * Kakeya.realRpowENN delta epsilon) ≠ 0 := by
          have h10 : ((K + 1 : ENNReal) * Kakeya.realRpowENN delta epsilon) ≤ (0 : ENNReal) * Kakeya.realRpowENN delta epsilon ↔
              (K + 1 : ENNReal) ≤ (0 : ENNReal) :=
            ENNReal.mul_le_mul_iff_left (c := Kakeya.realRpowENN delta epsilon)
              (a := (K + 1 : ENNReal)) (b := (0 : ENNReal)) heps_pos.ne' (hfin_rpow epsilon)
          have h9 : ((K + 1 : ENNReal) * Kakeya.realRpowENN delta epsilon) = 0 ↔ (K + 1 : ENNReal) = 0 := by
            simpa [zero_mul, le_zero_iff] using h10
          exact h9.not.mpr hK1_pos.ne'
        have h5 : (((K + 1 : ENNReal) * Kakeya.realRpowENN delta epsilon) * (wz1PaperBodyFamily family).mass) ≠ 0 := by
          have h12 : (((K + 1 : ENNReal) * Kakeya.realRpowENN delta epsilon) * (wz1PaperBodyFamily family).mass) ≤ (0 : ENNReal) * (wz1PaperBodyFamily family).mass ↔
              ((K + 1 : ENNReal) * Kakeya.realRpowENN delta epsilon) ≤ (0 : ENNReal) :=
            ENNReal.mul_le_mul_iff_left (c := (wz1PaperBodyFamily family).mass)
              (a := ((K + 1 : ENNReal) * Kakeya.realRpowENN delta epsilon)) (b := (0 : ENNReal))
              h_pos3.ne' hF_mass_fin
          have h11 : (((K + 1 : ENNReal) * Kakeya.realRpowENN delta epsilon) * (wz1PaperBodyFamily family).mass) = 0 ↔
              ((K + 1 : ENNReal) * Kakeya.realRpowENN delta epsilon) = 0 := by
            simpa [zero_mul, le_zero_iff] using h12
          exact h11.not.mpr h4
        have h_posA : 0 < A := by
          dsimp only [A]
          exact lt_of_le_of_ne (show (0 : ENNReal) ≤ A from by simp) h5.symm
        exact h_posA

    have h_low_fin : lowSum ≠ ⊤ := ne_top_of_le_ne_top hB_fin h_low_band_mass_le

    have h_sum_total : highSum + lowSum = Y.mass := by
      have h : (∑ l ∈ (highBands ∪ lowBands), (wz1PaperDyadicBandSubshading Y l).mass) = highSum + lowSum :=
        Finset.sum_union h_disj
      rw [h_union] at h
      exact h.symm.trans h_bands_cover

    have h_strict_add : highSum + lowSum < A + B := by
      have h_high_fin : highSum ≠ ⊤ := ne_top_of_lt h_high_lt_A
      have h_ac : highSum + lowSum ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨h_high_fin, h_low_fin⟩
      have h_bd : A + B ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hA_fin, hB_fin⟩
      have h_goal : (highSum + lowSum).toReal < (A + B).toReal := by
        rw [ENNReal.toReal_add h_high_fin h_low_fin, ENNReal.toReal_add hA_fin hB_fin]
        have h1' : highSum.toReal < A.toReal := (ENNReal.toReal_lt_toReal h_high_fin hA_fin).mpr h_high_lt_A
        have h2' : lowSum.toReal ≤ B.toReal := (ENNReal.toReal_le_toReal h_low_fin hB_fin).mpr h_low_band_mass_le
        linarith
      exact (ENNReal.toReal_lt_toReal h_ac h_bd).mp h_goal

    have h4 : A ≤ (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta * (wz1PaperBodyFamily family).mass := by
      dsimp only [A]
      have h5 : (K + 1 : ENNReal) * Kakeya.realRpowENN delta epsilon ≤
          (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta := by
        have h6 : (K + 1 : ENNReal) ≤ (1 / 2 : ENNReal) * Kakeya.realRpowENN delta (eta - epsilon) := by
          have h_eq : (1 / 2 : ENNReal) * (2 * (K + 1 : ENNReal)) = (K + 1 : ENNReal) := by
            have h7 : (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ := by
              simp [div_eq_mul_inv] <;> norm_num
            rw [h7]
            have h8 : (2 : ENNReal)⁻¹ * (2 * (K + 1 : ENNReal)) = (K + 1 : ENNReal) :=
              ENNReal.inv_mul_cancel_left (by simp) (by simp)
            exact h8
          rw [←h_eq]
          have h_gcongr := ENNReal.mul_le_mul_iff_right (a := (1 / 2 : ENNReal))
            (b := (2 * (K + 1 : ENNReal))) (c := Kakeya.realRpowENN delta (eta - epsilon))
            (by norm_num) (by simp)
          exact h_gcongr.mpr h3
        have h7 : (K + 1 : ENNReal) * Kakeya.realRpowENN delta epsilon ≤
            ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta (eta - epsilon)) * Kakeya.realRpowENN delta epsilon := by
          have h8 := ENNReal.mul_le_mul_iff_left (c := Kakeya.realRpowENN delta epsilon)
            (a := (K + 1 : ENNReal)) (b := (1 / 2 : ENNReal) * Kakeya.realRpowENN delta (eta - epsilon))
            heps_pos.ne' (hfin_rpow epsilon)
          exact h8.mpr h6
        have h9 : ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta (eta - epsilon)) * Kakeya.realRpowENN delta epsilon =
            (1 / 2 : ENNReal) * (Kakeya.realRpowENN delta (eta - epsilon) * Kakeya.realRpowENN delta epsilon) := by
          rw [mul_assoc]
        have h10 : Kakeya.realRpowENN delta (eta - epsilon) * Kakeya.realRpowENN delta epsilon =
            Kakeya.realRpowENN delta ((eta - epsilon) + epsilon) := pureWZ2_realRpowENN_mul hdelta_pos
        have h11 : (eta - epsilon) + epsilon = eta := by ring
        rw [h9, h10, h11] at h7
        exact h7
      calc (K + 1 : ENNReal) * Kakeya.realRpowENN delta epsilon * (wz1PaperBodyFamily family).mass
        = ((K + 1 : ENNReal) * Kakeya.realRpowENN delta epsilon) * (wz1PaperBodyFamily family).mass := by ring
      _ ≤ ((1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta) * (wz1PaperBodyFamily family).mass := by gcongr
      _ = (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta * (wz1PaperBodyFamily family).mass := by ring

    have h5 : B ≤ (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta * (wz1PaperBodyFamily family).mass := by
      dsimp only [B]
      have h6 : Kakeya.realRpowENN delta (3 * eta) ≤
          Kakeya.realRpowENN delta eta *
            (wz1PaperBodyFamily family).mass := by
        have h_eq2 : Kakeya.realRpowENN delta (3 * eta) =
            Kakeya.realRpowENN delta eta *
              Kakeya.realRpowENN delta (2 * eta) := by
          have h_add : (3 * eta) = eta + 2 * eta := by ring
          rw [h_add]
          exact (pureWZ2_realRpowENN_mul hdelta_pos).symm
        rw [h_eq2]
        gcongr
      have h7 : 4 * Kakeya.realRpowENN delta (epsilon - eta) ≤ Kakeya.realRpowENN delta eta * (wz1PaperBodyFamily family).mass :=
        h_mass_ineq.trans h6
      have h8 : (1 / 2 : ENNReal) * (4 * Kakeya.realRpowENN delta (epsilon - eta)) ≤
          (1 / 2 : ENNReal) * (Kakeya.realRpowENN delta eta * (wz1PaperBodyFamily family).mass) := by gcongr
      have h9 : (1 / 2 : ENNReal) * (4 * Kakeya.realRpowENN delta (epsilon - eta)) =
          2 * Kakeya.realRpowENN delta (epsilon - eta) := by
        have h10 : (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ := by
          simp [div_eq_mul_inv] <;> norm_num
        rw [h10]
        have h11 : (4 * Kakeya.realRpowENN delta (epsilon - eta)) =
            (2 : ENNReal) * (2 * Kakeya.realRpowENN delta (epsilon - eta)) := by
          let x := Kakeya.realRpowENN delta (epsilon - eta)
          have h4_eq : (4 : ENNReal) = (2 : ENNReal) + (2 : ENNReal) := by
            exact_mod_cast (show (4 : ℕ) = 2 + 2 from by norm_num)
          calc (4 : ENNReal) * x
            = ((2 : ENNReal) + (2 : ENNReal)) * x := by rw [h4_eq]
          _ = (2 : ENNReal) * x + (2 : ENNReal) * x := by rw [add_mul]
          _ = (2 : ENNReal) * ((2 : ENNReal) * x) := by rw [←two_mul]
        rw [h11]
        exact ENNReal.inv_mul_cancel_left (by simp) (by simp)
      rw [h9] at h8
      simpa [mul_assoc] using h8

    have h_final : Y.mass < Kakeya.realRpowENN delta eta * (wz1PaperBodyFamily family).mass := by
      rw [←h_sum_total]
      calc highSum + lowSum
        < A + B := h_strict_add
      _ ≤ (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta * (wz1PaperBodyFamily family).mass +
            (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta * (wz1PaperBodyFamily family).mass := by
          exact add_le_add h4 h5
      _ = Kakeya.realRpowENN delta eta * (wz1PaperBodyFamily family).mass := by
          let C := (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta * (wz1PaperBodyFamily family).mass
          have h13 : C + C = Kakeya.realRpowENN delta eta * (wz1PaperBodyFamily family).mass := by
            have h14 : C + C = ((1 / 2 : ENNReal) + (1 / 2 : ENNReal)) * (Kakeya.realRpowENN delta eta * (wz1PaperBodyFamily family).mass) := by
              rw [add_mul] <;> ring
            rw [h14]
            have h15 : (1 / 2 : ENNReal) + (1 / 2 : ENNReal) = 1 := by
              have h16 : (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ := by
                simp [div_eq_mul_inv] <;> norm_num
              rw [h16]
              have h17 : (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ = (2 : ENNReal) * (2 : ENNReal)⁻¹ := by
                exact (two_mul _).symm
              rw [h17]
              have h18 : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 := by
                rw [mul_comm]
                exact ENNReal.inv_mul_cancel (by simp) (by simp)
              exact h18
            rw [h15, one_mul]
          exact h13

    exact False.elim (not_le.mpr h_final hY_mass_lower)


end Kakeya.Assouad

end
