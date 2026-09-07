import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.FrostmanToKatzTao
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Frostman to Katz--Tao extraction without separation

The Vitali/maximal-subset proof does not use delta separation.  This closed
variant is the form consumed by the collapsed-parameter Section 7 route.
-/

noncomputable section

open Classical Kakeya.Assouad DiscreteSet Metric Set Finset

namespace Kakeya.Assouad

/-- Frostman-to-Katz--Tao extraction without a separation premise. -/
def FrostmanToKatzTaoNoSepStatement : Prop :=
  ∀ n : ℕ, ∀ s : ℝ, 0 < s → s ≤ n →
    ∃ L : ENNReal, 1 ≤ L ∧ L ≠ ⊤ ∧
      ∀ delta : ℝ, ∀ C : ENNReal,
        0 < delta → delta < 1 →
        1 ≤ C → C ≠ ⊤ →
        ∀ A : DiscreteSet n,
          A.Nonempty →
          A.IsInUnitBall →
          A.IsFrostman delta s C →
          Kakeya.realRpowENN delta (-s) ≤ A.enncard →
          ∃ A' : DiscreteSet n,
            A'.Nonempty ∧
              A' ⊆ A ∧
              A'.IsKatzTao delta s 100 ∧
              Kakeya.realRpowENN delta (-s) ≤
                L * ENNReal.ofReal (1 + Real.log delta⁻¹) *
                  C * A'.enncard

theorem frostman_to_katz_tao_no_sep :
    FrostmanToKatzTaoNoSepStatement := by
  intro n s hs_pos hsn
  let L : ENNReal := ENNReal.ofReal ((99 + Real.rpow 5 s) / 99)
  use L
  constructor
  · have h1 : 0 < Real.rpow 5 s :=
      Real.rpow_pos_of_pos (by norm_num) s
    have h2 : (99 + Real.rpow 5 s) / 99 ≥ 1 := by
      have h3 : 99 + Real.rpow 5 s ≥ 99 := by linarith
      have h4 : (99 + Real.rpow 5 s) / 99 ≥ 99 / 99 := by gcongr
      linarith
    have h5 :
        (1 : ENNReal) ≤
          ENNReal.ofReal ((99 + Real.rpow 5 s) / 99) := by
      rw [ENNReal.one_le_ofReal]
      linarith
    exact h5
  constructor
  · exact ENNReal.ofReal_ne_top
  intro δ C hδ_pos hδ_lt_one hC_one hC_top
    A hA_nonempty hA_unit hA_frost hA_card
  rcases exists_maximal_katz_tao hδ_pos hs_pos hA_nonempty with
    ⟨A', h_sub, hA'_nonempty, h_kt, h_max_union⟩
  have h_max_insert :
      ∀ x ∈ A \ A', ¬ (insert x A').IsKatzTao δ s 100 := by
    intro x hx
    have h_eq : insert x A' = A' ∪ {x} := by
      ext z
      simp [Finset.mem_insert, Finset.mem_union] <;> tauto
    rw [h_eq]
    exact h_max_union x hx
  by_cases h_eq : A' = A
  · subst h_eq
    have h_bound :
        Kakeya.realRpowENN δ (-s) ≤
          L * ENNReal.ofReal (1 + Real.log δ⁻¹) *
            C * A'.enncard := by
      have h1 : Kakeya.realRpowENN δ (-s) ≤ A'.enncard := hA_card
      have h2 : (1 : ENNReal) ≤ L := by
        have h1 : 0 < Real.rpow 5 s :=
          Real.rpow_pos_of_pos (by norm_num) s
        have h2 : (99 + Real.rpow 5 s) / 99 ≥ 1 := by linarith
        rw [ENNReal.one_le_ofReal]
        linarith
      have h3 :
          (1 : ENNReal) ≤ ENNReal.ofReal (1 + Real.log δ⁻¹) := by
        have h_log_pos : 0 < Real.log δ⁻¹ := by
          apply Real.log_pos
          have h : 1 < δ⁻¹ := by
            have h_pos : 0 < δ := hδ_pos
            calc
              δ⁻¹ = 1 / δ := by field_simp [h_pos.ne'] <;> ring
              _ > 1 / 1 := by gcongr
              _ = 1 := by norm_num
          exact h
        have h4 : 1 ≤ 1 + Real.log δ⁻¹ := by linarith
        rw [ENNReal.one_le_ofReal]
        linarith
      have h4 :
          A'.enncard ≤
            L * ENNReal.ofReal (1 + Real.log δ⁻¹) *
              C * A'.enncard := by
        calc
          A'.enncard =
              (1 : ENNReal) * (1 : ENNReal) *
                (1 : ENNReal) * A'.enncard := by ring
          _ ≤ L * ENNReal.ofReal (1 + Real.log δ⁻¹) *
              C * A'.enncard := by gcongr <;> tauto
      exact le_trans h1 h4
    exact ⟨A', hA'_nonempty, h_sub, h_kt, h_bound⟩
  · have h_main_real :
        (A.card : ℝ) ≤
          (A'.card : ℝ) *
            (1 + Real.rpow 5 s * C.toReal *
              (A.card : ℝ) * Real.rpow δ s / 99) := by
      have h :=
        vitali_covering_step hδ_pos hs_pos hC_one hC_top
          hA_frost hA_unit h_sub h_kt h_max_insert
      simpa [mul_assoc] using h
    have h_bound :
        Kakeya.realRpowENN δ (-s) ≤
          L * ENNReal.ofReal (1 + Real.log δ⁻¹) *
            C * A'.enncard :=
      final_lifting hδ_pos hδ_lt_one hs_pos hC_one hC_top
        h_main_real hA_card
    exact ⟨A', hA'_nonempty, h_sub, h_kt, h_bound⟩

end Kakeya.Assouad
