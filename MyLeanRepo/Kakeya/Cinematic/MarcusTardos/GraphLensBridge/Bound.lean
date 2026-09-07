import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.GraphLensBridge.Sequences

/-!
# The graph-lens bound from the total sequence bound

All graph-strip lenses are counted once by the moon-face sequences.  The
lens-face and inverse-face sequence families are empty in the PYZ closure.
-/

noncomputable section

namespace Kakeya.Cinematic.GraphLensBridge

open Kakeya.Cinematic

local instance : DecidableEq C2Function := Classical.decEq _

theorem graph_lens_bound_from_sequences_closed :
    GraphLensBoundFromSequencesStatement := by
  intro hsequence
  rcases hsequence C2Function with ⟨Cseq, hCseq, hbound⟩
  let logTwo := Real.log 2
  let C := Cseq * (1 + logTwo⁻¹)
  refine ⟨C, ?_, ?_⟩
  · have hlogTwo : 0 < logTwo := by
      dsimp [logTwo]
      exact Real.log_pos (by norm_num)
    positivity
  · intro curves hfamily lenses hsides hnonoverlap
    classical
    let curveEquiv : Fin curves.card ≃ curves := (curves.equivFin).symm
    let sequences : Fin curves.card → List C2Function :=
      fun i => moonSequence lenses (curveEquiv i)
    have hnodup : ∀ i, (sequences i).Nodup := by
      intro i
      exact moonSequence_nodup hfamily hsides hnonoverlap (curveEquiv i)
    have halphabet : ∀ i, ∀ symbol ∈ sequences i, symbol ∈ curves := by
      intro i symbol hsymbol
      let lens := lensForSymbol lenses (curveEquiv i) symbol hsymbol
      have hlens := lensForSymbol_mem_lenses lenses (curveEquiv i) symbol hsymbol
      have hlower := lower_lensForSymbol lenses (curveEquiv i) symbol hsymbol
      rw [← hlower]
      exact lower_mem_curves (hsides lens hlens)
    have hreverse :
        ∀ i j, i ≠ j →
          MarcusTardos.IsCyclicIntersectionReverse (sequences i) (sequences j) := by
      intro i j hij
      apply moonSequences_intersection_reverse hfamily hsides hnonoverlap
      intro h
      apply hij
      exact curveEquiv.injective (Subtype.ext h)
    have htotal := hbound curves.card curves.card curves rfl
      sequences hnodup halphabet hreverse
    have hsum :
        ∑ i, (sequences i).length =
          ∑ host ∈ curves, (moonSequence lenses host).length := by
      calc
        ∑ i, (sequences i).length =
            ∑ host : curves, (moonSequence lenses host).length := by
              exact Fintype.sum_equiv curveEquiv
                (fun i => (sequences i).length)
                (fun host : curves => (moonSequence lenses host).length)
                (fun _ => rfl)
        _ = ∑ host ∈ curves, (moonSequence lenses host).length := by
              exact Finset.sum_coe_sort curves
                (fun host => (moonSequence lenses host).length)
    rw [hsum, sum_moonSequence_length hsides] at htotal
    by_cases hn : curves.card = 0
    · simp [hn] at htotal ⊢
      exact htotal
    · have hnpos : 0 < curves.card := Nat.pos_of_ne_zero hn
      have hlogTwo : 0 < logTwo := by
        dsimp [logTwo]
        exact Real.log_pos (by norm_num)
      have hlog :
          logTwo ≤ Real.log (curves.card + 1) := by
        dsimp [logTwo]
        apply Real.log_le_log (by norm_num)
        exact_mod_cast Nat.succ_le_succ hnpos
      have hsqrt : 0 < Real.sqrt (curves.card : ℝ) :=
        Real.sqrt_pos.mpr (by positivity)
      have hnreal : (1 : ℝ) ≤ curves.card := by exact_mod_cast hnpos
      have hsqrt_le :
          Real.sqrt (curves.card : ℝ) ≤
            (curves.card : ℝ) * Real.sqrt (curves.card : ℝ) := by
        nlinarith
      have hrpow :
          Real.rpow curves.card (3 / 2 : ℝ) =
            (curves.card : ℝ) * Real.sqrt (curves.card : ℝ) := by
        calc
          Real.rpow curves.card (3 / 2 : ℝ) =
              Real.rpow curves.card (1 + 1 / 2 : ℝ) := by norm_num
          _ = Real.rpow curves.card 1 * Real.rpow curves.card (1 / 2 : ℝ) :=
            Real.rpow_add (by positivity) 1 (1 / 2)
          _ = (curves.card : ℝ) * Real.rpow curves.card (1 / 2 : ℝ) := by
            exact congrArg (fun value =>
              value * Real.rpow curves.card (1 / 2 : ℝ))
              (Real.rpow_one (curves.card : ℝ))
          _ = (curves.card : ℝ) * Real.sqrt (curves.card : ℝ) := by
            exact congrArg (fun value => (curves.card : ℝ) * value)
              (Real.sqrt_eq_rpow (curves.card : ℝ)).symm
      have hmain :
          (lenses.card : ℝ) ≤
            Cseq * ((curves.card : ℝ) * Real.sqrt curves.card *
              Real.log (curves.card + 1) +
              (curves.card : ℝ) * Real.sqrt curves.card) := by
        exact_mod_cast htotal
      rw [hrpow]
      dsimp [C, logTwo]
      have hlogPos : 0 < Real.log (curves.card + 1) :=
        lt_of_lt_of_le hlogTwo hlog
      let mass : ℝ := (curves.card : ℝ) * Real.sqrt curves.card
      have hmass : 0 ≤ mass := by
        dsimp [mass]
        positivity
      have hcoefficient : 0 ≤ (Real.log 2)⁻¹ * mass := by
        positivity
      have habsorb :
          mass ≤ (Real.log 2)⁻¹ * mass * Real.log (curves.card + 1) := by
        calc
          mass = (Real.log 2)⁻¹ * mass * Real.log 2 := by
            field_simp [ne_of_gt hlogTwo]
          _ ≤ (Real.log 2)⁻¹ * mass * Real.log (curves.card + 1) :=
            mul_le_mul_of_nonneg_left hlog hcoefficient
      calc
        (lenses.card : ℝ) ≤
            Cseq * (mass * Real.log (curves.card + 1) + mass) := by
          simpa [mass] using hmain
        _ ≤ Cseq *
            (mass * Real.log (curves.card + 1) +
              (Real.log 2)⁻¹ * mass * Real.log (curves.card + 1)) :=
          mul_le_mul_of_nonneg_left
            (by simpa [add_comm] using
              add_le_add_left habsorb (mass * Real.log (curves.card + 1)))
            hCseq.le
        _ = Cseq * (1 + (Real.log 2)⁻¹) * mass *
            Real.log (curves.card + 1) := by ring
        _ = Cseq * (1 + (Real.log 2)⁻¹) *
            ((curves.card : ℝ) * Real.sqrt curves.card) *
              Real.log (curves.card + 1) := by rfl

end Kakeya.Cinematic.GraphLensBridge
