import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.FrostmanToKatzTaoNoSep

/-!
# Frostman to Katz--Tao extraction with weighted cardinality

Paper Lemma 7.10 supplies a Frostman constant `C` and cardinality at the
natural scale `delta^(-s) / C`.  This is the exact input needed by the
maximal-subset proof.
-/

noncomputable section

open Classical Kakeya.Assouad DiscreteSet Metric Set Finset

namespace Kakeya.Assouad

/-- Explicit absolute constant in the weighted-cardinality extraction. -/
def weightedFrostmanToKatzTaoConstant (s : ℝ) : ENNReal :=
  ENNReal.ofReal ((99 + Real.rpow 5 s) / 99)

/--
Weighted-cardinality version of the no-separation Frostman-to-Katz--Tao
extraction.
-/
def FrostmanToKatzTaoWeightedCardStatement : Prop :=
  ∀ n : ℕ, ∀ s : ℝ, 0 < s → s ≤ n →
    let L := weightedFrostmanToKatzTaoConstant s
    1 ≤ L ∧ L ≠ ⊤ ∧
      ∀ delta : ℝ, ∀ C : ENNReal,
        0 < delta → delta < 1 →
        1 ≤ C → C ≠ ⊤ →
        ∀ A : DiscreteSet n,
          A.Nonempty →
          A.IsInUnitBall →
          A.IsFrostman delta s C →
          Kakeya.realRpowENN delta (-s) ≤
            C * A.enncard →
          ∃ A' : DiscreteSet n,
            A'.Nonempty ∧
              A' ⊆ A ∧
              A'.IsKatzTao delta s 100 ∧
              Kakeya.realRpowENN delta (-s) ≤
                L * ENNReal.ofReal (1 + Real.log delta⁻¹) *
                  C * A'.enncard

lemma DiscreteSet.IsFrostman.weighted_cardinality
    {n : ℕ}
    {A : DiscreteSet n}
    {delta s : ℝ}
    {C : ENNReal}
    (hFrostman : A.IsFrostman delta s C)
    (hA : A.Nonempty)
    (hdelta : 0 < delta)
    (hdelta_one : delta ≤ 1) :
    Kakeya.realRpowENN delta (-s) ≤
      C * A.enncard := by
  rcases hA with ⟨point, hpoint⟩
  have hpoint_ball :
      point ∈ A.filter
        (fun candidate => dist candidate point ≤ delta) := by
    exact Finset.mem_filter.mpr
      ⟨hpoint, by simp; linarith⟩
  have hone :
      (1 : ENNReal) ≤ A.ballCount point delta := by
    simp only [DiscreteSet.ballCount]
    exact_mod_cast
      (Finset.one_le_card.mpr ⟨point, hpoint_ball⟩)
  have hbound :
      (1 : ENNReal) ≤
        C * Kakeya.realRpowENN delta s *
          A.enncard :=
    hone.trans
      (hFrostman point delta le_rfl hdelta_one)
  have hcancel :
      Kakeya.realRpowENN delta (-s) *
          Kakeya.realRpowENN delta s =
        1 := by
    rw [← realRpowENN_add hdelta]
    simp [Kakeya.realRpowENN]
  calc
    Kakeya.realRpowENN delta (-s) =
        Kakeya.realRpowENN delta (-s) * 1 := by
          simp
    _ ≤
        Kakeya.realRpowENN delta (-s) *
          (C * Kakeya.realRpowENN delta s *
            A.enncard) := by
      gcongr
    _ =
        C *
          (Kakeya.realRpowENN delta (-s) *
            Kakeya.realRpowENN delta s) *
          A.enncard := by ring
    _ = C * A.enncard := by rw [hcancel]; simp

theorem frostman_to_katz_tao_weighted_card :
    FrostmanToKatzTaoWeightedCardStatement := by
  intro n s hs_pos hsn
  let L : ENNReal := weightedFrostmanToKatzTaoConstant s
  have hL_one : 1 ≤ L := by
    have h1 : 0 < Real.rpow 5 s :=
      Real.rpow_pos_of_pos (by norm_num) s
    rw [show L =
      ENNReal.ofReal ((99 + Real.rpow 5 s) / 99) by rfl,
      ENNReal.one_le_ofReal]
    linarith
  have hL_top : L ≠ ⊤ := by
    exact ENNReal.ofReal_ne_top
  refine ⟨hL_one, hL_top, ?_⟩
  intro delta C hdelta hdelta_one hC_one hC_top
    A hA_nonempty hA_unit hA_frost hA_card
  rcases exists_maximal_katz_tao
      hdelta hs_pos hA_nonempty with
    ⟨A', hsub, hA'_nonempty, hkt, hmax⟩
  have hmax_insert :
      ∀ x ∈ A \ A',
        ¬(insert x A').IsKatzTao delta s 100 := by
    intro x hx
    have h_eq : insert x A' = A' ∪ {x} := by
      ext z
      simp [Finset.mem_insert, Finset.mem_union]
    rw [h_eq]
    exact hmax x hx
  by_cases h_eq : A' = A
  · subst h_eq
    have hlog :
        (1 : ENNReal) ≤
          ENNReal.ofReal (1 + Real.log delta⁻¹) := by
      rw [ENNReal.one_le_ofReal]
      have h_inv : 1 < delta⁻¹ := by
        calc
          delta⁻¹ = 1 / delta := by
            field_simp [hdelta.ne']
          _ > 1 / 1 := by gcongr
          _ = 1 := by norm_num
      have hlog_pos : 0 < Real.log delta⁻¹ :=
        Real.log_pos h_inv
      linarith
    have hbound :
        Kakeya.realRpowENN delta (-s) ≤
          L * ENNReal.ofReal (1 + Real.log delta⁻¹) *
            C * A'.enncard := by
      calc
      Kakeya.realRpowENN delta (-s)
          ≤ C * A'.enncard := hA_card
      _ =
          (1 : ENNReal) * (1 : ENNReal) *
            C * A'.enncard := by ring
      _ ≤
          L * ENNReal.ofReal (1 + Real.log delta⁻¹) *
            C * A'.enncard := by
        gcongr
    exact ⟨A', hA'_nonempty, hsub, hkt, hbound⟩
  · have hmain :
        (A.card : ℝ) ≤
          (A'.card : ℝ) *
            (1 + Real.rpow 5 s * C.toReal *
              (A.card : ℝ) * Real.rpow delta s / 99) := by
      simpa [mul_assoc] using
        (vitali_covering_step
          hdelta hs_pos hC_one hC_top hA_frost hA_unit
          hsub hkt hmax_insert)
    set N : ℝ := (A.card : ℝ) with hN
    set N' : ℝ := (A'.card : ℝ) with hN'
    set c : ℝ := C.toReal with hc
    set a : ℝ := Real.rpow 5 s with ha
    have hc_one : 1 ≤ c := by
      exact
        (ENNReal.toReal_le_toReal
          (by simp) hC_top).2 hC_one
    have hc_pos : 0 < c := by linarith
    have hN_nonneg : 0 ≤ N := by positivity
    have hN_pos : 0 < N := by
      dsimp only [N]
      exact_mod_cast hA_nonempty.card_pos
    have ha_pos : 0 < a := by
      exact Real.rpow_pos_of_pos (by norm_num) s
    have hcard_real :
        Real.rpow delta (-s) ≤ c * N := by
      have hleft :
          Kakeya.realRpowENN delta (-s) =
            ENNReal.ofReal (Real.rpow delta (-s)) := rfl
      have hright :
          C * A.enncard = ENNReal.ofReal (c * N) := by
        rw [show C = ENNReal.ofReal c by
          rw [hc, ENNReal.ofReal_toReal hC_top]]
        have hc_nonneg : 0 ≤ c := by linarith
        rw [show A.enncard = ENNReal.ofReal N by
          simp [DiscreteSet.enncard, hN]]
        exact (ENNReal.ofReal_mul hc_nonneg).symm
      rw [hleft, hright] at hA_card
      exact
        (ENNReal.ofReal_le_ofReal_iff
          (mul_nonneg (by linarith) hN_nonneg)).1 hA_card
    have hdelta_cancel :
        Real.rpow delta (-s) *
            Real.rpow delta s = 1 := by
      calc
        Real.rpow delta (-s) *
              Real.rpow delta s =
            Real.rpow delta (-s + s) :=
          (Real.rpow_add hdelta (-s) s).symm
        _ = 1 := by simp
    have hM_one :
        1 ≤ c * N * Real.rpow delta s := by
      calc
        1 = Real.rpow delta (-s) *
              Real.rpow delta s := hdelta_cancel.symm
        _ ≤ (c * N) * Real.rpow delta s := by
          exact mul_le_mul_of_nonneg_right hcard_real
            (Real.rpow_nonneg hdelta.le s)
        _ = c * N * Real.rpow delta s := by ring
    let M := c * N * Real.rpow delta s
    have hmain' :
        N ≤ N' * (1 + a * M / 99) := by
      simpa [N, N', c, a, M, mul_assoc] using hmain
    have hdenom :
        99 + a * M ≤ (99 + a) * M := by
      dsimp only [M] at hM_one ⊢
      nlinarith
    have hdenom_pos : 0 < 99 + a * M := by positivity
    have hbound_N' :
        99 * N / ((99 + a) * M) ≤ N' := by
      have hcross : 99 * N ≤ N' * (99 + a * M) := by
        nlinarith
      calc
        99 * N / ((99 + a) * M)
            ≤ 99 * N / (99 + a * M) := by
          apply div_le_div_of_nonneg_left
          · positivity
          · exact hdenom_pos
          · exact hdenom
        _ ≤ N' := by
          exact (div_le_iff₀ hdenom_pos).2
            (by simpa [mul_comm] using hcross)
    have hM_eq :
        N / M = Real.rpow delta (-s) / c := by
      dsimp only [M]
      have hrpow_pos : 0 < Real.rpow delta s :=
        Real.rpow_pos_of_pos hdelta s
      calc
        N / (c * N * Real.rpow delta s) =
            1 / (c * Real.rpow delta s) := by
          field_simp [hN_pos.ne', hc_pos.ne', hrpow_pos.ne']
        _ = Real.rpow delta (-s) / c := by
          have hinv :
              Real.rpow delta (-s) =
                (Real.rpow delta s)⁻¹ :=
            Real.rpow_neg hdelta.le s
          rw [hinv]
          field_simp [hc_pos.ne', hrpow_pos.ne']
    have hreal :
        Real.rpow delta (-s) ≤
          ((99 + a) / 99) * c * N' := by
      have hcoeff_pos : 0 < (99 + a) * c := by positivity
      have hratio_eq :
          99 * Real.rpow delta (-s) /
                ((99 + a) * c) =
            99 * N / ((99 + a) * M) := by
        calc
          99 * Real.rpow delta (-s) /
                ((99 + a) * c) =
              (99 / (99 + a)) *
                (Real.rpow delta (-s) / c) := by
            field_simp [hc_pos.ne']
          _ = (99 / (99 + a)) * (N / M) := by
            rw [hM_eq]
          _ = 99 * N / ((99 + a) * M) := by
            field_simp
      calc
        Real.rpow delta (-s)
            = ((99 + a) * c / 99) *
                (99 * Real.rpow delta (-s) /
                  ((99 + a) * c)) := by
              field_simp [hcoeff_pos.ne']
        _ = ((99 + a) * c / 99) *
              (99 * N / ((99 + a) * M)) := by
          rw [hratio_eq]
        _ ≤ ((99 + a) * c / 99) * N' := by
          gcongr
        _ = ((99 + a) / 99) * c * N' := by ring
    have hlog_real : 1 ≤ 1 + Real.log delta⁻¹ := by
      have h_inv : 1 < delta⁻¹ := by
        calc
          delta⁻¹ = 1 / delta := by field_simp [hdelta.ne']
          _ > 1 / 1 := by gcongr
          _ = 1 := by norm_num
      linarith [Real.log_pos h_inv]
    have hreal' :
        Real.rpow delta (-s) ≤
          ((99 + a) / 99) *
            (1 + Real.log delta⁻¹) * c * N' := by
      calc
        Real.rpow delta (-s)
            ≤ ((99 + a) / 99) * c * N' := hreal
        _ =
            ((99 + a) / 99) * 1 * c * N' := by ring
        _ ≤
            ((99 + a) / 99) *
              (1 + Real.log delta⁻¹) * c * N' := by
          gcongr
    have hENN :
        Kakeya.realRpowENN delta (-s) ≤
          L * ENNReal.ofReal (1 + Real.log delta⁻¹) *
            C * A'.enncard := by
      have hL_eq :
          L = ENNReal.ofReal ((99 + a) / 99) := by
        rfl
      have hC_eq : C = ENNReal.ofReal c := by
        exact (ENNReal.ofReal_toReal hC_top).symm.trans
          (by rfl)
      have hN'_eq :
          A'.enncard = ENNReal.ofReal N' := by
        simp [DiscreteSet.enncard, N']
      rw [hL_eq, hC_eq, hN'_eq]
      have hfirst_nonneg : 0 ≤ (99 + a) / 99 := by
        positivity
      have hlog_nonneg : 0 ≤ 1 + Real.log delta⁻¹ := by
        linarith
      have hc_nonneg : 0 ≤ c := by linarith
      have hN'_nonneg : 0 ≤ N' := by
        dsimp only [N']
        exact_mod_cast Nat.zero_le A'.card
      have hmul1 :
          ENNReal.ofReal
              (((99 + a) / 99) *
                (1 + Real.log delta⁻¹)) =
            ENNReal.ofReal ((99 + a) / 99) *
              ENNReal.ofReal (1 + Real.log delta⁻¹) := by
        exact ENNReal.ofReal_mul hfirst_nonneg
      have hmul2 :
          ENNReal.ofReal
              ((((99 + a) / 99) *
                (1 + Real.log delta⁻¹)) * c) =
            ENNReal.ofReal
                (((99 + a) / 99) *
                  (1 + Real.log delta⁻¹)) *
              ENNReal.ofReal c := by
        exact ENNReal.ofReal_mul
          (mul_nonneg hfirst_nonneg hlog_nonneg)
      have hmul3 :
          ENNReal.ofReal
              (((((99 + a) / 99) *
                (1 + Real.log delta⁻¹)) * c) * N') =
            ENNReal.ofReal
                ((((99 + a) / 99) *
                  (1 + Real.log delta⁻¹)) * c) *
              ENNReal.ofReal N' := by
        exact ENNReal.ofReal_mul
          (mul_nonneg
            (mul_nonneg hfirst_nonneg hlog_nonneg)
            hc_nonneg)
      calc
        ENNReal.ofReal (Real.rpow delta (-s))
            ≤ ENNReal.ofReal
              (((99 + a) / 99) *
                (1 + Real.log delta⁻¹) * c * N') :=
          ENNReal.ofReal_mono hreal'
        _ =
            ENNReal.ofReal ((99 + a) / 99) *
              ENNReal.ofReal (1 + Real.log delta⁻¹) *
              ENNReal.ofReal c * ENNReal.ofReal N' := by
          rw [hmul3, hmul2, hmul1]
    exact ⟨A', hA'_nonempty, hsub, hkt, hENN⟩

end Kakeya.Assouad
