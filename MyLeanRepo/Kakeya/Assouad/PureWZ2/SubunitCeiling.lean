import MyLeanRepo.Kakeya.Assouad.PureWZ2.Critical

/-!
# Pure WZ2 Wolff floor implies subunit admissibility ceiling

Elementary strict-power argument placing the critical exponent below one.

Given `PureWZ2WolffVolumeFloor`, the lower bound `δ^(1/2+ε) ≤ volume` at every
sufficiently small scale contradicts `PureWZ2Admissible σ` for any `σ` with
`1/2 < σ < 1`, because admissibility supplies a scale with `volume ≤ δ^σ` while
the floor supplies `volume ≥ δ^(1/2+ε)` for `ε` chosen so that
`1/2 + ε < σ`.  For `0 < δ < 1`, real powers are antitone in the exponent, so
`δ^σ < δ^(1/2+ε)`, a contradiction.

The concrete ceiling used here is `3/4`, with `ε = 1/8`.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Helper: from a Wolff volume floor, produce a concrete real ceiling `3/4 < 1`
for which `PureWZ2Admissible` fails.
-/
lemma concrete_ceiling_from_wolff_floor
    (h : PureWZ2WolffVolumeFloor) :
    ∃ ceiling : ℝ, ceiling < 1 ∧ ¬ PureWZ2Admissible ceiling := by
  use 3 / 4
  constructor
  · norm_num
  · intro h_adm
    -- Apply the floor with epsilon = 1/8, giving lower exponent 5/8.
    have h_floor_inst := h (1 / 8) (by norm_num)
    rcases h_floor_inst with ⟨eta, delta₀, h_eta_pos, h_d0_pos, h_d0_le_one, h_floor⟩
    -- Shrink delta₀ to guarantee the witness delta is strictly below 1.
    let delta₀' := min delta₀ (1 / 2)
    have h_d0'_pos : 0 < delta₀' := by positivity
    -- Admissibility at sigma = 3/4 produces a small-scale counterexample.
    have h_adm_inst := h_adm eta h_eta_pos delta₀' h_d0'_pos
    rcases h_adm_inst with
      ⟨delta, h_delta_pos, h_delta_le_d0', h_delta_le_one,
       family, shading, h_nonempty, h_cwa, h_dense, h_vol_le⟩
    have h_delta_le_d0 : delta ≤ delta₀ := by
      calc delta ≤ delta₀' := h_delta_le_d0'
           _ ≤ delta₀ := min_le_left _ _
    have h_delta_lt_one : delta < 1 := by
      calc delta ≤ delta₀' := h_delta_le_d0'
           _ ≤ 1 / 2 := min_le_right _ _
           _ < 1 := by norm_num
    -- Floor gives volume ≥ delta^(5/8).
    have h_vol_ge : Kakeya.realRpowENN delta (1 / 2 + (1 / 8 : ℝ)) ≤
        MeasureTheory.volume (Kakeya.Streamlined.Shading.union shading) :=
      h_floor delta h_delta_pos h_delta_le_d0 family h_nonempty h_cwa shading h_dense
    have h_exp : (1 / 2 + (1 / 8 : ℝ)) = (5 / 8 : ℝ) := by norm_num
    -- Chain: delta^(5/8) ≤ volume ≤ delta^(3/4).
    have h_chain : Kakeya.realRpowENN delta (5 / 8) ≤
        Kakeya.realRpowENN delta (3 / 4) := by
      rw [show Kakeya.realRpowENN delta (5 / 8) = Kakeya.realRpowENN delta (1 / 2 + (1 / 8 : ℝ)) by rw [h_exp]]
      exact le_trans h_vol_ge h_vol_le
    -- Strict antitone property: delta^(3/4) < delta^(5/8) for 0 < delta < 1.
    have h_rpow_pos58 : 0 < Real.rpow delta (5 / 8) :=
      Real.rpow_pos_of_pos h_delta_pos _
    have h_rpow_strict : Real.rpow delta (3 / 4) < Real.rpow delta (5 / 8) :=
      (Real.rpow_lt_rpow_left_iff_of_base_lt_one h_delta_pos h_delta_lt_one).mpr (by norm_num)
    -- Lift to ENNReal.
    have h_ennreal_strict :
        ENNReal.ofReal (Real.rpow delta (3 / 4)) <
        ENNReal.ofReal (Real.rpow delta (5 / 8)) :=
      (ENNReal.ofReal_lt_ofReal_iff h_rpow_pos58).mpr h_rpow_strict
    -- Contradiction: a < b and b ≤ a implies a < a.
    have h_a_lt_a : Kakeya.realRpowENN delta (3 / 4) < Kakeya.realRpowENN delta (3 / 4) :=
      lt_of_lt_of_le h_ennreal_strict h_chain
    exact lt_irrefl _ h_a_lt_a

/--
The Wolff volume floor implies existence of a ceiling below one for which
admissibility fails.  This is the elementary strict-power conjunct of the
pure WZ2 subunit package.
-/
theorem pure_wz2_wolff_floor_implies_subunit_ceiling :
    PureWZ2WolffFloorImpliesSubunitCeilingStatement := by
  intro h
  exact concrete_ceiling_from_wolff_floor h

end Kakeya.Assouad
