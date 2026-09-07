import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23GoodHeights

/-!
# Fubini slice of an almost-full local grain in WZ1 Lemma 23

An almost-full local grain has volume at least `rho^(2 + 2*eta)` and lies in
one height interval of length `sqrt rho`.  Fubini therefore supplies a
genuine horizontal slice of area at least `rho^(3/2 + 2*eta)`.
-/

namespace Kakeya.Assouad

noncomputable section

open MeasureTheory Set

/--
Select the quantitative horizontal slice used in Lemma 23 Step 1.
-/
theorem wz1_lemma23_full_grain_fubini
    {E : Set Point3} (hE : MeasurableSet E)
    {rho eta left : ℝ}
    (hrho : 0 < rho)
    (hE_finite : volume E ≠ ⊤)
    (hheight :
      ∀ point ∈ E,
        point (2 : Fin 3) ∈
          Set.Ico left (left + Real.sqrt rho))
    (hvolume :
      Kakeya.realRpowENN rho (2 + 2 * eta) ≤
        volume E) :
    ∃ z ∈ Set.Ico left (left + Real.sqrt rho),
      Kakeya.realRpowENN rho (3 / 2 + 2 * eta) ≤
        volume (wz1Lemma23PlanarSlice E z) := by
  have hsqrt : 0 < Real.sqrt rho :=
    Real.sqrt_pos.mpr hrho
  have hinterval :
      left < left + Real.sqrt rho := by
    linarith
  have hEinter :
      E ∩ {point : Point3 |
          point (2 : Fin 3) ∈
            Set.Ico left (left + Real.sqrt rho)} =
        E := by
    ext point
    constructor
    · intro hpoint
      exact hpoint.1
    · intro hpoint
      exact ⟨hpoint, hheight point hpoint⟩
  rcases
      wz1_lemma23_exists_good_height_in_slab
        hE hE_finite hinterval with
    ⟨z, hz, hslice⟩
  refine ⟨z, hz, ?_⟩
  rw [hEinter] at hslice
  have haverage :
      Kakeya.realRpowENN rho (2 + 2 * eta) /
          ENNReal.ofReal (Real.sqrt rho) ≤
        volume (wz1Lemma23PlanarSlice E z) :=
    (ENNReal.div_le_div_right hvolume
      (ENNReal.ofReal (Real.sqrt rho))).trans
      (by simpa using hslice)
  have hpower :
      Kakeya.realRpowENN rho (2 + 2 * eta) /
          ENNReal.ofReal (Real.sqrt rho) =
        Kakeya.realRpowENN rho (3 / 2 + 2 * eta) := by
    simp only [Kakeya.realRpowENN]
    rw [Real.sqrt_eq_rpow]
    rw [← ENNReal.ofReal_div_of_pos
      (Real.rpow_pos_of_pos hrho (1 / 2 : ℝ))]
    apply congrArg ENNReal.ofReal
    change
      Real.rpow rho (2 + 2 * eta) /
          Real.rpow rho (1 / 2 : ℝ) =
        Real.rpow rho (3 / 2 + 2 * eta)
    calc
      Real.rpow rho (2 + 2 * eta) /
            Real.rpow rho (1 / 2 : ℝ)
          = Real.rpow rho
              ((2 + 2 * eta) - (1 / 2 : ℝ)) :=
        (Real.rpow_sub hrho
          (2 + 2 * eta) (1 / 2 : ℝ)).symm
      _ = Real.rpow rho (3 / 2 + 2 * eta) := by
        congr 1
        ring
  rwa [hpower] at haverage

end

end Kakeya.Assouad
