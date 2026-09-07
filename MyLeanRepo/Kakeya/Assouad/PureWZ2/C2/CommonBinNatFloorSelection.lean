import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CommonBinDistinctIncidence

/-!
# Natural-number rounding for common-bin cell counts
-/

namespace Kakeya.Assouad.CommonBinRichSelection

/-- A finite extended nonnegative real at least one has a natural integer
between half of it and itself.  This is the rounding receipt used for the
uniform rich-cell count `K`. -/
theorem exists_natCast_between_half
    (X : ENNReal)
    (hX : 1 ≤ X)
    (hXtop : X ≠ ⊤) :
    ∃ K : ℕ, X / 2 ≤ K ∧ (K : ENNReal) ≤ X := by
  let x := X.toReal
  let K := Nat.floor x
  have hxNonneg : 0 ≤ x := ENNReal.toReal_nonneg
  have hxOne : 1 ≤ x := by
    have hreal :=
      (ENNReal.toReal_le_toReal (by norm_num) hXtop).mpr hX
    simpa [x] using hreal
  have hKPos : 0 < K := by
    apply Nat.floor_pos.mpr
    linarith
  have hKUpperReal : (K : ℝ) ≤ x :=
    Nat.floor_le hxNonneg
  have hxLt : x < K + 1 :=
    Nat.lt_floor_add_one x
  have hhalfLowerReal : x / 2 ≤ K := by
    have hKOne : (1 : ℝ) ≤ K := by
      exact_mod_cast hKPos
    linarith
  refine ⟨K, ?_, ?_⟩
  · apply
      (ENNReal.toReal_le_toReal
        (ENNReal.div_ne_top hXtop (by norm_num))
        (ENNReal.natCast_ne_top K)).mp
    simpa [x, ENNReal.toReal_div] using hhalfLowerReal
  · apply
      (ENNReal.toReal_le_toReal
        (ENNReal.natCast_ne_top K) hXtop).mp
    simpa [x] using hKUpperReal

end Kakeya.Assouad.CommonBinRichSelection
