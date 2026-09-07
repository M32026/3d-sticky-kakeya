import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49UnitCircleFrostmanStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49RadialCirclePacking

/-!
WZ1 Lemma 49 unit-circle direction Frostman leaf.

For `tau ≤ r ≤ 1/2`, the local cap-packing bound gives
`#(directions ∩ B(x,r)) ≤ (4/√3 + 1) * r / tau`.
Normalizing by `kappa / tau ≤ #directions` yields the Frostman form
with constant `(4/√3 + 1) / kappa`.

For `1/2 ≤ r ≤ 1`, the trivial bound `#(directions ∩ B(x,r)) ≤ #directions`
suffices because the constant `2 + (4/√3 + 1)/kappa` exceeds `2`,
so `C * r ≥ 1` whenever `r ≥ 1/2`.
-/

namespace Kakeya.Assouad

theorem wz1_lemma49_unit_circle_frostman :
    WZ1Lemma49UnitCircleFrostmanStatement := by
  intro directions tau kappa htau htauHalf hkappa hunit hseparated hcard x r hrTau hrOne
  set c : ℝ := 2 + (4 / Real.sqrt 3 + 1) / kappa with hc_def
  have hc_pos : 0 < c := by
    dsimp only [c]
    positivity
  have hr : 0 < r := by linarith
  let cap := directions.filter fun y => dist y x ≤ r
  have hmain_real : (cap.card : ℝ) ≤ c * r * (directions.card : ℝ) := by
    by_cases hcase : r ≤ 1 / 2
    · -- Case r ≤ 1/2: use unit-circle cap packing
      have hpack : (cap.card : ℝ) ≤ (4 / Real.sqrt 3 + 1) * r / tau :=
        wz1_lemma49_unit_circle_cap_packing
          (hdelta := htau) (hr := hr) (hrHalf := hcase)
          (hunit := hunit) (hseparated := hseparated)
          (hdeltaR := hrTau)
      have h_inv : 1 / tau ≤ (directions.card : ℝ) / kappa := by
        have h_kap_pos : 0 < kappa := hkappa
        calc
          1 / tau = (kappa / tau) / kappa := by
            field_simp [h_kap_pos.ne']
          _ ≤ (directions.card : ℝ) / kappa := by gcongr
      have h4 : (4 / Real.sqrt 3 + 1) * r / tau ≤
          ((4 / Real.sqrt 3 + 1) / kappa) * r * (directions.card : ℝ) := by
        calc
          (4 / Real.sqrt 3 + 1) * r / tau
            = (4 / Real.sqrt 3 + 1) * r * (1 / tau) := by ring
          _ ≤ (4 / Real.sqrt 3 + 1) * r * ((directions.card : ℝ) / kappa) := by gcongr
          _ = ((4 / Real.sqrt 3 + 1) / kappa) * r * (directions.card : ℝ) := by ring
      have h5 : 0 ≤ r * (directions.card : ℝ) := by positivity
      have h6 : ((4 / Real.sqrt 3 + 1) / kappa) ≤ c := by
        dsimp only [c]; linarith
      calc
        (cap.card : ℝ) ≤ (4 / Real.sqrt 3 + 1) * r / tau := hpack
        _ ≤ ((4 / Real.sqrt 3 + 1) / kappa) * r * (directions.card : ℝ) := h4
        _ ≤ c * r * (directions.card : ℝ) := by
          nlinarith
    · -- Case r > 1/2: use total cardinality bound
      have hcase' : 1 / 2 ≤ r := by linarith
      have hsub : cap ⊆ directions := Finset.filter_subset _ _
      have hcard_le : (cap.card : ℝ) ≤ (directions.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have h_extra : 0 < (4 / Real.sqrt 3 + 1) / kappa := by positivity
      have h_gt_two : (2 : ℝ) < c := by
        dsimp only [c]; linarith [h_extra]
      have h6 : 1 ≤ c * r := by
        have h7 : 1 / 2 ≤ r := hcase'
        nlinarith
      calc
        (cap.card : ℝ) ≤ (directions.card : ℝ) := hcard_le
        _ = 1 * (directions.card : ℝ) := by ring
        _ ≤ c * r * (directions.card : ℝ) := by
          gcongr
  -- Lift the real inequality to ENNReal
  have hnonneg : 0 ≤ c * r * (directions.card : ℝ) := by positivity
  have h_ofReal_cap : ENNReal.ofReal ((cap.card : ℝ)) = (cap.card : ENNReal) := by
    norm_cast
  have h10 : ENNReal.ofReal ((cap.card : ℝ)) ≤
      ENNReal.ofReal (c * r * (directions.card : ℝ)) :=
    ENNReal.ofReal_le_ofReal hmain_real
  have henn_main : (cap.card : ENNReal) ≤
      ENNReal.ofReal (c * r * (directions.card : ℝ)) := by
    rw [←h_ofReal_cap]
    exact h10
  have h_rpow : Real.rpow r 1 = r := by
    have h : (r ^ (1 : ℝ)) = r := by
      rw [Real.rpow_one]
    exact h
  have hrpow : Kakeya.realRpowENN r 1 = ENNReal.ofReal r := by
    rw [Kakeya.realRpowENN, h_rpow]
  have h_pos12 : 0 ≤ c * r := by positivity
  have h_pos_card : 0 ≤ (directions.card : ℝ) := by positivity
  have h_eq : ENNReal.ofReal (c * r * (directions.card : ℝ)) =
      ENNReal.ofReal c * Kakeya.realRpowENN r 1 * directions.enncard := by
    rw [hrpow]
    have h1 : ENNReal.ofReal ((c * r) * (directions.card : ℝ)) =
        ENNReal.ofReal (c * r) * ENNReal.ofReal ((directions.card : ℝ)) := by
      rw [ENNReal.ofReal_mul h_pos12]
    have h2 : ENNReal.ofReal (c * r) =
        ENNReal.ofReal c * ENNReal.ofReal r := by
      rw [ENNReal.ofReal_mul (show 0 ≤ c by positivity)]
    have h3 : ENNReal.ofReal ((directions.card : ℝ)) = directions.enncard := by
      simp [DiscreteSet.enncard]
    calc
      ENNReal.ofReal (c * r * (directions.card : ℝ))
        = ENNReal.ofReal ((c * r) * (directions.card : ℝ)) := by rfl
      _ = ENNReal.ofReal (c * r) * ENNReal.ofReal ((directions.card : ℝ)) := h1
      _ = (ENNReal.ofReal c * ENNReal.ofReal r) *
            ENNReal.ofReal ((directions.card : ℝ)) := by rw [h2]
      _ = (ENNReal.ofReal c * ENNReal.ofReal r) * directions.enncard := by rw [h3]
      _ = ENNReal.ofReal c * ENNReal.ofReal r * directions.enncard := by rfl
  have h_unfold : directions.ballCount x r = (cap.card : ENNReal) := by
    simp [DiscreteSet.ballCount, cap]
  rw [h_unfold]
  have h_final : (cap.card : ENNReal) ≤
      ENNReal.ofReal c * Kakeya.realRpowENN r 1 * directions.enncard := by
    calc
      (cap.card : ENNReal)
        ≤ ENNReal.ofReal (c * r * (directions.card : ℝ)) := henn_main
      _ = ENNReal.ofReal c * Kakeya.realRpowENN r 1 * directions.enncard := h_eq
  exact h_final

end Kakeya.Assouad
