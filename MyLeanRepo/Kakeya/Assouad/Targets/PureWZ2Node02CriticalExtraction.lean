import MyLeanRepo.Kakeya.Assouad.PureWZ2.Critical
import MyLeanRepo.Kakeya.Assouad.ExtremalHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CriticalExtraction

/-!
# Pure WZ2 Node 2: critical extraction

From the Node 1 subunit package and failure of pure Theorem 5.2, construct
a critical exponent `0 < σ < 1` with an extremal sequence and the global
critical volume floor.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

theorem pure_wz2_node02_critical_extraction :
    PureWZ2CriticalExtractionStatement := by
  intro h_subunit h_not_theorem
  rcases h_subunit with
    ⟨_, _, _, _, ⟨a, ha_lt_one, ha_not_admissible⟩⟩
  rcases pure_wz2_failure_admissible h_not_theorem with
    ⟨ε₀, hε₀_pos, hε₀_adm⟩
  let S : Set ℝ := {s | PureWZ2Admissible s}
  have hS_downward : ∀ x ∈ S, ∀ y ≤ x, y ∈ S := by
    intro x hx y hy
    exact PureWZ2Admissible.mono hx hy
  have hS_nonempty : S.Nonempty := ⟨ε₀, hε₀_adm⟩
  have h_upper_bound : ∀ s ∈ S, s ≤ a := by
    intro s hs
    by_cases h : s ≤ a
    · exact h
    · have h' : a ≤ s := by linarith
      have ha : PureWZ2Admissible a :=
        PureWZ2Admissible.mono hs h'
      exact False.elim (ha_not_admissible ha)
  have hS_bdd : BddAbove S := ⟨a, h_upper_bound⟩
  let sigma : ℝ := sSup S
  have hsigma_pos : 0 < sigma := by
    have h1 : ε₀ ∈ S := hε₀_adm
    have h2 : ε₀ ≤ sigma := le_csSup hS_bdd h1
    linarith
  have hsigma_le_a : sigma ≤ a :=
    csSup_le hS_nonempty h_upper_bound
  have hsigma_lt_one : sigma < 1 :=
    hsigma_le_a.trans_lt ha_lt_one
  have h_not_admissible_above :
      ∀ loss : ℝ, 0 < loss →
        ¬ PureWZ2Admissible (sigma + loss) := by
    intro loss hloss h
    have hmem : sigma + loss ∈ S := h
    have hle : sigma + loss ≤ sigma :=
      le_csSup hS_bdd hmem
    linarith
  have h_extremal_sequence :
      ∀ loss delta₀ : ℝ, 0 < loss → 0 < delta₀ →
        ∃ delta : ℝ, 0 < delta ∧ delta ≤ delta₀ ∧
          Nonempty
            (PureWZ2ExtremalConfiguration sigma loss delta) := by
    intro loss delta₀ hloss hdelta₀
    have h1 : sigma - loss ∈ S := by
      have h_lt : sigma - loss < sigma := by linarith
      exact
        sSup_lt_mem hS_downward hS_nonempty hS_bdd h_lt
    rcases h1 loss hloss delta₀ hdelta₀ with
      ⟨delta, hdelta_pos, hdelta_le, hdelta_one, family, shading,
        hF_nonempty, hCWA, hDense, hVolume⟩
    let extremal :
        WZ2PaperPureIsExtremal sigma loss family shading :=
      { delta_pos := hdelta_pos
        delta_le_one := hdelta_one
        nonempty := hF_nonempty
        cwa_nearby_scales := hCWA
        dense := hDense
        volume_upper := hVolume }
    let config :
        PureWZ2ExtremalConfiguration sigma loss delta :=
      { family := family
        shading := shading
        extremal := extremal }
    exact ⟨delta, hdelta_pos, hdelta_le, ⟨config⟩⟩
  have h_critical_floor :
      PureWZ2CriticalVolumeFloor sigma := by
    intro floorLoss structuralBudget
      hfloorLoss hstructuralBudget
    have h_not_adm :
        ¬ PureWZ2Admissible (sigma + floorLoss) :=
      h_not_admissible_above floorLoss hfloorLoss
    rcases pure_wz2_non_admissible_spec h_not_adm with
      ⟨eta₀, heta₀_pos, delta₀, hdelta₀_pos,
        hdelta₀_one, h_lower⟩
    let structuralLoss := min eta₀ structuralBudget
    have hstructuralLoss_pos : 0 < structuralLoss := by
      positivity
    have hstructuralLoss_le_eta₀ :
        structuralLoss ≤ eta₀ :=
      min_le_left _ _
    have hstructuralLoss_le_budget :
        structuralLoss ≤ structuralBudget :=
      min_le_right _ _
    refine ⟨structuralLoss, delta₀, hstructuralLoss_pos,
      hstructuralLoss_le_budget, hdelta₀_pos, hdelta₀_one, ?_⟩
    intro delta hdelta_pos hdelta_le
      family hF_nonempty shading hCWA hDense
    have hdelta_one : delta ≤ 1 :=
      hdelta_le.trans hdelta₀_one
    have hCWA' :
        WZ2PaperPureCWAAtNearbyScales family
          (Kakeya.realRpowENN delta (-eta₀)) :=
      WZ2PaperPureCWAAtNearbyScales.mono_loss
        hdelta_pos hdelta_one hstructuralLoss_le_eta₀ hCWA
    have hDense' :
        shading.IsLambdaDense
          (Kakeya.realRpowENN delta eta₀) :=
      pure_wz2_dense_weaken hdelta_pos hdelta_one
        hstructuralLoss_le_eta₀ hDense
    have h_strict :
        Kakeya.realRpowENN delta (sigma + floorLoss) <
          MeasureTheory.volume shading.union :=
      h_lower delta hdelta_pos hdelta_le family hF_nonempty
        hCWA' shading hDense'
    exact le_of_lt h_strict
  let pkg : PureWZ2CriticalPackage sigma :=
    { sigma_pos := hsigma_pos
      sigma_lt_one := hsigma_lt_one
      extremal_sequence := h_extremal_sequence
      critical_floor := h_critical_floor }
  exact ⟨sigma, ⟨pkg⟩⟩

end Kakeya.Assouad

end
