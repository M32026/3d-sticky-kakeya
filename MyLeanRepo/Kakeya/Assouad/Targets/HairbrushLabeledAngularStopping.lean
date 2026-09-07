import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.MassRetention
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.MaxScoreTubesWitnessHalf
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.SphereCovering
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.DyadicPigeonhole
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.AngularStoppingHelpers
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.GlobalDirectionPacking
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.MeasurableLabel
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.NetAndLabel
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.TwoBroadness
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Tactic

/-!
# Main proof of hairbrush_labeled_angular_stopping

Uses max-score witnesses capped at radius 1/2, dyadic pigeonholing,
direction net rounding. Theta is always ≤ 1/2 by construction.
-/

noncomputable section

open MeasureTheory Metric Set Finset Real InnerProductGeometry

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-! ### Existence of delta₀ -/

/-- Bound: log(y) ≤ y^a / a for y ≥ 1, a > 0. -/
lemma log_le_rpow_div {y a : ℝ} (hy : 1 ≤ y) (ha : 0 < a) :
    Real.log y ≤ y^a / a := by
  have h_pos : 0 < y := by linarith
  have h1 : Real.log (y^a) ≤ y^a - 1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos h_pos a)
  have h2 : Real.log (y^a) = a * Real.log y := by rw [Real.log_rpow (by linarith)]
  have h3 : a * Real.log y ≤ y^a - 1 := by linarith
  have h4 : a * Real.log y ≤ y^a := by linarith
  have h5 : Real.log y ≤ y^a / a := by
    calc Real.log y = (a * Real.log y) / a := by field_simp [ha.ne'] <;> ring
    _ ≤ (y^a) / a := by gcongr
  exact h5

/-- Explicit delta₀ construction. -/
lemma angular_stopping_delta_exists (eta stopLoss epsilon2 eps : ℝ)
    (heta : 0 < eta) (hstop : eta < stopLoss)
    (hepsilon2_pos : 0 < epsilon2) (heps_pos : 0 < eps) :
    ∃ (delta₀ : ℝ), 0 < delta₀ ∧ delta₀ ≤ 1 / 2 ∧
      (∀ δ, 0 < δ → δ ≤ delta₀ →
        (δ ^ eps) * (Real.log (1 / δ) / Real.log 2 + 1) ≤ 1) ∧
      (∀ δ, 0 < δ → δ ≤ delta₀ → δ ^ epsilon2 ≤ 1 / 1000) := by
  have h_log2_pos : 0 < Real.log 2 := by positivity
  let c1 : ℝ := eps * Real.log 2 / 4
  have hc1_pos : 0 < c1 := by positivity
  let delta_a1 : ℝ := c1 ^ (2 / eps)
  let delta_a2 : ℝ := (1 / 2 : ℝ) ^ (1 / eps)
  let delta_b : ℝ := (1 / 1000 : ℝ) ^ (1 / epsilon2)
  let delta₀ : ℝ := min (min delta_a1 delta_a2) (min delta_b (1 / 2))
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_le1 : delta₀ ≤ 1 := by
    have h : delta₀ ≤ min delta_b (1 / 2) := min_le_right _ _
    have h2 : delta₀ ≤ 1 / 2 := h.trans (min_le_right _ _)
    linarith
  have hdelta₀_le_half : delta₀ ≤ 1 / 2 := by
    have h : delta₀ ≤ min delta_b (1 / 2) := min_le_right _ _
    exact h.trans (min_le_right _ _)
  have h_a1 : delta₀ ≤ delta_a1 := by
    have h : delta₀ ≤ min delta_a1 delta_a2 := min_le_left _ _
    exact h.trans (min_le_left _ _)
  have h_a2 : delta₀ ≤ delta_a2 := by
    have h : delta₀ ≤ min delta_a1 delta_a2 := min_le_left _ _
    exact h.trans (min_le_right _ _)
  have h_b : delta₀ ≤ delta_b := by
    have h : delta₀ ≤ min delta_b (1 / 2) := min_le_right _ _
    exact h.trans (min_le_left _ _)
  have h_rpow_comp : ∀ (x : ℝ) (hx : 0 < x) (a b : ℝ), (x ^ a) ^ b = x ^ (a * b) := by
    intro x hx a b
    exact (Real.rpow_mul hx.le a b).symm
  have h_pigeonhole_condition : ∀ δ, 0 < δ → δ ≤ delta₀ →
      (δ ^ eps) * (Real.log (1 / δ) / Real.log 2 + 1) ≤ 1 := by
    intro δ hδ hδle
    have hδ_le1 : δ ≤ 1 := by linarith
    have h_x_ge1 : 1 ≤ 1 / δ := one_le_one_div hδ hδ_le1
    have h_log_bound : Real.log (1 / δ) ≤ (1 / δ) ^ (eps / 2) / (eps / 2) :=
      log_le_rpow_div h_x_ge1 (by positivity)
    have h4 : (1 / δ) ^ (eps / 2) = 1 / (δ ^ (eps / 2)) := by
      rw [Real.div_rpow (by norm_num) (by linarith)]
      <;> simp
    have h3 : δ ^ eps * (1 / δ) ^ (eps / 2) = δ ^ (eps / 2) := by
      rw [h4]
      have h_div : δ ^ eps * (1 / δ ^ (eps / 2)) = δ ^ eps / δ ^ (eps / 2) := by ring
      rw [h_div]
      have h5 : δ ^ eps / δ ^ (eps / 2) = δ ^ (eps - eps / 2) := by
        rw [← Real.rpow_sub hδ] <;> ring
      rw [h5]
      have h6 : eps - eps / 2 = eps / 2 := by ring
      rw [h6]
    have h_log_bound2 : Real.log (1 / δ) / Real.log 2 + 1 ≤
        2 * (1 / δ) ^ (eps / 2) / (eps * Real.log 2) + 1 := by
      calc Real.log (1 / δ) / Real.log 2 + 1
        ≤ ((1 / δ) ^ (eps / 2) / (eps / 2)) / Real.log 2 + 1 := by gcongr
      _ = 2 * (1 / δ) ^ (eps / 2) / (eps * Real.log 2) + 1 := by
        field_simp [heps_pos.ne', h_log2_pos.ne'] <;> ring
    have h_d1 : δ ^ (eps / 2) ≤ c1 := by
      have h : δ ≤ delta_a1 := hδle.trans h_a1
      have h5 : δ ^ (eps / 2) ≤ delta_a1 ^ (eps / 2) := by gcongr <;> linarith
      have h6 : delta_a1 ^ (eps / 2) = c1 := by
        dsimp only [delta_a1]
        have h7 : (c1 ^ (2 / eps)) ^ (eps / 2) = c1 ^ ((2 / eps) * (eps / 2)) := h_rpow_comp c1 hc1_pos (2 / eps) (eps / 2)
        rw [h7]
        have h8 : (2 / eps) * (eps / 2) = 1 := by field_simp [heps_pos.ne'] <;> ring
        rw [h8, Real.rpow_one]
      rw [h6] at h5; exact h5
    have h_term1 : 2 * δ ^ (eps / 2) / (eps * Real.log 2) ≤ 1 / 2 := by
      calc 2 * δ ^ (eps / 2) / (eps * Real.log 2)
        ≤ 2 * c1 / (eps * Real.log 2) := by gcongr
      _ = 1 / 2 := by
        simp only [c1] <;> field_simp [heps_pos.ne', h_log2_pos.ne'] <;> ring
    have h_d2 : δ ^ eps ≤ 1 / 2 := by
      have h : δ ≤ delta_a2 := hδle.trans h_a2
      have h5 : δ ^ eps ≤ delta_a2 ^ eps := by gcongr <;> linarith
      have h6 : delta_a2 ^ eps = 1 / 2 := by
        dsimp only [delta_a2]
        have h7 : ((1 / 2 : ℝ) ^ (1 / eps)) ^ eps = (1 / 2 : ℝ) ^ ((1 / eps) * eps) :=
          h_rpow_comp (1 / 2 : ℝ) (by norm_num) (1 / eps) eps
        rw [h7]
        have h8 : (1 / eps) * eps = 1 := by field_simp [heps_pos.ne'] <;> ring
        rw [h8, Real.rpow_one]
      rw [h6] at h5; exact h5
    calc (δ ^ eps) * (Real.log (1 / δ) / Real.log 2 + 1)
      ≤ (δ ^ eps) * (2 * (1 / δ) ^ (eps / 2) / (eps * Real.log 2) + 1) := by gcongr
    _ = 2 * (δ ^ eps * (1 / δ) ^ (eps / 2)) / (eps * Real.log 2) + δ ^ eps := by ring
    _ = 2 * δ ^ (eps / 2) / (eps * Real.log 2) + δ ^ eps := by rw [h3]
    _ ≤ (1 / 2 : ℝ) + (1 / 2 : ℝ) := by gcongr
    _ = 1 := by norm_num
  have hδ_eps2 : ∀ δ, 0 < δ → δ ≤ delta₀ → δ ^ epsilon2 ≤ 1 / 1000 := by
    intro δ hδ hδle
    have h : δ ≤ delta_b := hδle.trans h_b
    have h5 : δ ^ epsilon2 ≤ delta_b ^ epsilon2 := by gcongr <;> linarith
    have h6 : delta_b ^ epsilon2 = 1 / 1000 := by
      dsimp only [delta_b]
      have h7 : ((1 / 1000 : ℝ) ^ (1 / epsilon2)) ^ epsilon2 = (1 / 1000 : ℝ) ^ ((1 / epsilon2) * epsilon2) :=
        h_rpow_comp (1 / 1000 : ℝ) (by norm_num) (1 / epsilon2) epsilon2
      rw [h7]
      have h8 : (1 / epsilon2) * epsilon2 = 1 := by field_simp [hepsilon2_pos.ne'] <;> ring
      rw [h8, Real.rpow_one]
    rw [h6] at h5; exact h5
  exact ⟨delta₀, hdelta₀_pos, hdelta₀_le_half, h_pigeonhole_condition, hδ_eps2⟩

/-! ### Main theorem -/

theorem hairbrush_labeled_angular_stopping :
    HairbrushLabeledAngularStoppingStatement := by
  intro eta stopLoss heta hstop
  set epsilon2 : ℝ := (stopLoss - eta) / 2 with hepsilon2_def
  set eps : ℝ := (stopLoss - eta) / 2 with heps_def
  have hepsilon2_pos : 0 < epsilon2 := by linarith
  have heps_pos : 0 < eps := by linarith
  have h_eps_eta : eps + eta = stopLoss - epsilon2 := by
    simp [heps_def, hepsilon2_def] <;> linarith

  rcases angular_stopping_delta_exists eta stopLoss epsilon2 eps
      heta hstop hepsilon2_pos heps_pos with
    ⟨delta₀, hdelta₀_pos, hdelta₀_le_half, h_pigeonhole_condition, hδ_eps2⟩
  have hdelta₀_le1 : delta₀ ≤ 1 := by linarith [hdelta₀_le_half]

  have h_absorb : ∀ δ, 0 < δ → δ ≤ delta₀ →
      (1 / 1000 : ENNReal) * Kakeya.realRpowENN δ (stopLoss - epsilon2) ≥
        Kakeya.realRpowENN δ stopLoss := by
    intro δ hδ hδle
    have h1 : δ ^ epsilon2 ≤ 1 / 1000 := hδ_eps2 δ hδ hδle
    have h2 : Kakeya.realRpowENN δ stopLoss =
        Kakeya.realRpowENN δ epsilon2 * Kakeya.realRpowENN δ (stopLoss - epsilon2) := by
      have h_add : δ ^ stopLoss = δ ^ epsilon2 * δ ^ (stopLoss - epsilon2) := by
        rw [← Real.rpow_add hδ] <;> ring
      simp [Kakeya.realRpowENN, h_add, ENNReal.ofReal_mul (show 0 ≤ δ ^ epsilon2 by positivity)] <;> rfl
    rw [h2]
    have h4 : Kakeya.realRpowENN δ epsilon2 ≤ (1 / 1000 : ENNReal) := by
      have h5 : Kakeya.realRpowENN δ epsilon2 = ENNReal.ofReal (δ ^ epsilon2) := by rfl
      rw [h5]
      have h6 : ENNReal.ofReal (δ ^ epsilon2) ≤ ENNReal.ofReal (1 / 1000 : ℝ) :=
        ENNReal.ofReal_le_ofReal h1
      have h8 : ENNReal.ofReal (1 / 1000 : ℝ) = (1 / 1000 : ENNReal) := by simp
      rw [h8] at h6
      exact h6
    exact mul_le_mul_right' h4 _

  refine ⟨delta₀, hdelta₀_pos, hdelta₀_le1, ?_⟩
  intro δ hδ hδ_le F Y

  have hδ_le1 : δ ≤ 1 := hδ_le.trans hdelta₀_le1

  -- ===== Trivial case: Y.mass = 0 =====
  by_cases hYmass : Y.mass = 0
  · let shading : Kakeya.Shading F :=
      { carrier := fun _ => ∅
        measurable_carrier := fun _ _ => MeasurableSet.empty
        subset_tube := fun _ _ => Set.empty_subset _ }
    have h_shading_mass : shading.mass = 0 := by simp [shading, Kakeya.Shading.mass]
    have h_shading_union_empty : shading.union = ∅ := by
      simp [shading, Kakeya.Shading.union] <;> rfl
    let labelCount := 1
    let center (_ : Fin labelCount) := stdBasis3 0
    let label (_ : Point3) : Fin labelCount := 0
    have h_center_unit : ∀ (j : Fin labelCount), ‖center j‖ = 1 := by
      intro j; fin_cases j <;> exact stdBasis3_norm 0
    have h_label_measurable : Measurable label := by fun_prop
    refine ⟨δ, by linarith, hδ_le1, δ, by linarith, by linarith, hδ_le1, shading,
      (fun T _ => Set.empty_subset _), ?_, labelCount, by norm_num, label,
      h_label_measurable, center, h_center_unit, ?_, ?_, ?_⟩
    · rw [h_shading_mass, hYmass] <;> simp
    · intro x hx; rw [h_shading_union_empty] at hx <;> simpa using hx
    · intro T _
      have h_empty : (Finset.univ.filter fun j : Fin labelCount =>
          ∃ x ∈ shading.carrier T, label x = j) = ∅ := by
        simp [shading, Finset.filter_true_of_mem]
        <;> aesop
      rw [h_empty] <;> simp
    · intro x hx; rw [h_shading_union_empty] at hx <;> simpa using hx

  -- ===== Main case: Y.mass > 0 =====
  have hYmass_pos : Y.mass ≠ 0 := hYmass
  have hδ_le_half : δ ≤ 1 / 2 := hδ_le.trans hdelta₀_le_half

  -- Witness data for each nonempty S
  let h_exists (S : Finset (Kakeya.DeltaTube δ)) (hS : S.Nonempty) :=
    max_score_broadness_tubes_with_witness_half hδ hδ_le_half heta hS
  let w_S (S : Finset (Kakeya.DeltaTube δ)) (hS : S.Nonempty) :=
    Classical.choose (h_exists S hS)
  let h1_S (S : Finset (Kakeya.DeltaTube δ)) (hS : S.Nonempty) :=
    Classical.choose_spec (h_exists S hS)
  let r_S (S : Finset (Kakeya.DeltaTube δ)) (hS : S.Nonempty) :=
    Classical.choose (h1_S S hS)
  let h2_S (S : Finset (Kakeya.DeltaTube δ)) (hS : S.Nonempty) :=
    Classical.choose_spec (h1_S S hS)
  let W_S (S : Finset (Kakeya.DeltaTube δ)) (hS : S.Nonempty) :=
    Classical.choose (h2_S S hS)
  let witness_spec (S : Finset (Kakeya.DeltaTube δ)) (hS : S.Nonempty) :=
    Classical.choose_spec (h2_S S hS)

  let w_S' (S : Finset (Kakeya.DeltaTube δ)) : Point3 :=
    if h : S.Nonempty then w_S S h else stdBasis3 0
  let r_S' (S : Finset (Kakeya.DeltaTube δ)) : ℝ :=
    if h : S.Nonempty then r_S S h else δ
  let W_S' (S : Finset (Kakeya.DeltaTube δ)) : Finset (Kakeya.DeltaTube δ) :=
    if h : S.Nonempty then W_S S h else ∅

  have h_w_spec : ∀ (S : Finset (Kakeya.DeltaTube δ)) (hS : S.Nonempty),
      ‖w_S S hS‖ = 1 ∧ δ ≤ r_S S hS ∧ r_S S hS ≤ 1 / 2 ∧
      W_S S hS = S.filter (fun T => hairbrushAcuteDirectionAngle T.direction (w_S S hS) ≤ r_S S hS) ∧
      (W_S S hS).Nonempty ∧
      (∀ (v : Point3), ‖v‖ = 1 → ∀ s : ℝ, δ ≤ s → s ≤ r_S S hS →
        ((W_S S hS).filter (fun T => hairbrushAcuteDirectionAngle T.direction v ≤ s)).card ≤
          Real.rpow (s / r_S S hS) eta * (W_S S hS).card) ∧
      (∀ (v' : Point3), ‖v'‖ = 1 → ∀ r' : ℝ, δ ≤ r' → r' ≤ 1 / 2 →
        (S.filter (fun T => hairbrushAcuteDirectionAngle T.direction v' ≤ r')).card ≤
          Real.rpow (r' / r_S S hS) eta * (W_S S hS).card) := by
    intro S hS; exact witness_spec S hS

  have h_r_S'_range : ∀ S ∈ F.powerset, δ ≤ r_S' S ∧ r_S' S ≤ 1 / 2 := by
    intro S hS
    by_cases h : S.Nonempty
    · have hspec := h_w_spec S h
      simp only [r_S', dif_pos h]
      exact ⟨hspec.2.1, hspec.2.2.1⟩
    · simp only [r_S', dif_neg h]
      exact ⟨le_refl δ, hδ_le_half⟩

  have h_w_S'_unit : ∀ S ∈ F.powerset, ‖w_S' S‖ = 1 := by
    intro S hS
    by_cases h : S.Nonempty
    · simp only [w_S', dif_pos h]; exact (h_w_spec S h).1
    · simp only [w_S', dif_neg h]; exact stdBasis3_norm 0

  -- Weighted mass
  let weightedMass (S : Finset (Kakeya.DeltaTube δ)) : ENNReal :=
    (W_S' S).card * volume (throughPattern Y S)
  let totalWeighted : ENNReal := ∑ S ∈ F.powerset, weightedMass S

  have h_total_weighted_lower :
      totalWeighted ≥ (1 / 1000 : ENNReal) * Kakeya.realRpowENN δ eta * Y.mass := by
    have h1 : ∀ S ∈ F.powerset, weightedMass S ≥
        (1 / 1000 : ENNReal) * Kakeya.realRpowENN δ eta * (S.card : ENNReal) * volume (throughPattern Y S) := by
      intro S hS
      by_cases hSne : S.Nonempty
      · have hspec := h_w_spec S hSne
        have h_card_bound : (W_S S hSne).card ≥
            (1 / 1000 : ENNReal) * ENNReal.ofReal (Real.rpow (r_S S hSne) eta) * (S.card : ENNReal) :=
          witness_cardinality_bound_half_ENNReal hδ hδ_le_half heta hSne
            (w_S S hSne) (r_S S hSne) (W_S S hSne)
            hspec.1 hspec.2.1 hspec.2.2.1 hspec.2.2.2.1 hspec.2.2.2.2.2.2
        have h_rpow_ge : ENNReal.ofReal (Real.rpow (r_S S hSne) eta) ≥ Kakeya.realRpowENN δ eta := by
          have h5 : δ ≤ r_S S hSne := hspec.2.1
          have h6 : Real.rpow δ eta ≤ Real.rpow (r_S S hSne) eta :=
            Real.rpow_le_rpow (by linarith) h5 heta.le
          exact ENNReal.ofReal_le_ofReal h6
        have h7 : (W_S' S).card = (W_S S hSne).card := by
          simp only [W_S', dif_pos hSne]
        simp only [weightedMass]
        rw [h7]
        calc (W_S S hSne).card * volume (throughPattern Y S)
          ≥ ((1 / 1000 : ENNReal) * ENNReal.ofReal (Real.rpow (r_S S hSne) eta) * (S.card : ENNReal)) * volume (throughPattern Y S) := by gcongr
        _ ≥ (1 / 1000 : ENNReal) * Kakeya.realRpowENN δ eta * (S.card : ENNReal) * volume (throughPattern Y S) := by
          gcongr <;> ring
      · have h_empty : S = ∅ := by simpa using hSne
        rw [h_empty]; simp [weightedMass, W_S'] <;> simp
    have h2 : totalWeighted ≥
        ∑ S ∈ F.powerset, ((1 / 1000 : ENNReal) * Kakeya.realRpowENN δ eta * (S.card : ENNReal) * volume (throughPattern Y S)) := by
      apply Finset.sum_le_sum; intro S hS; exact h1 S hS
    have h3 : ∑ S ∈ F.powerset, ((1 / 1000 : ENNReal) * Kakeya.realRpowENN δ eta * (S.card : ENNReal) * volume (throughPattern Y S)) =
        (1 / 1000 : ENNReal) * Kakeya.realRpowENN δ eta * Y.mass := by
      let a : ENNReal := (1 / 1000 : ENNReal)
      let b : ENNReal := Kakeya.realRpowENN δ eta
      have h_eq1 : ∑ S ∈ F.powerset, (a * b * (S.card : ENNReal) * volume (throughPattern Y S)) =
          ∑ S ∈ F.powerset, ((a * b) * ((S.card : ENNReal) * volume (throughPattern Y S))) := by
        apply Finset.sum_congr rfl
        intro S _; ring
      rw [h_eq1]
      have h_eq2 : ∑ S ∈ F.powerset, ((a * b) * ((S.card : ENNReal) * volume (throughPattern Y S))) =
          (a * b) * ∑ S ∈ F.powerset, ((S.card : ENNReal) * volume (throughPattern Y S)) := by
        rw [← Finset.mul_sum] <;> rfl
      rw [h_eq2]
      have h5 : Y.mass = ∑ S ∈ F.powerset, (S.card : ENNReal) * volume (throughPattern Y S) :=
        shading_mass_eq_sum_patterns Y
      rw [h5] <;> ring
    rw [h3] at h2; exact h2

  -- Index all patterns for pigeonhole
  let N_all : ℕ := F.powerset.card
  let e_all : Fin N_all ≃ {S // S ∈ F.powerset} := (Finset.equivFin F.powerset).symm
  let idx (i : Fin N_all) : Finset (Kakeya.DeltaTube δ) := (e_all i).val
  have h_idx_mem : ∀ i, idx i ∈ F.powerset := fun i => (e_all i).property
  let mass_i (i : Fin N_all) : ENNReal := weightedMass (idx i)
  let scale_i (i : Fin N_all) : ℝ := r_S' (idx i)
  have h_scales_i : ∀ i, δ ≤ scale_i i ∧ scale_i i ≤ 1 := by
    intro i
    have h := h_r_S'_range (idx i) (h_idx_mem i)
    exact ⟨h.1, by linarith⟩
  have h_sum_eq : totalWeighted = ∑ i : Fin N_all, mass_i i := by
    let g : {S // S ∈ F.powerset} → ENNReal := fun S => weightedMass S.val
    have h_eq1 : ∑ i : Fin N_all, mass_i i = ∑ i : Fin N_all, g (e_all i) := by
      apply Finset.sum_congr rfl; intro i _; rfl
    have h_sum1 : ∑ i : Fin N_all, g (e_all i) = ∑ S : {S // S ∈ F.powerset}, g S :=
      Equiv.sum_comp e_all g
    have h_sum2 : ∑ S : {S // S ∈ F.powerset}, g S = ∑ S ∈ F.powerset, weightedMass S := by
      rw [← Finset.sum_attach (s := F.powerset)] <;> rfl
    rw [h_eq1, h_sum1, h_sum2]

  -- Dyadic pigeonhole
  have h_pigeonhole_result : ∃ (theta : ℝ), δ ≤ theta ∧ theta ≤ 1 ∧
      (∃ k : ℕ, theta = (1 / 2 : ℝ) ^ k) ∧
      ENNReal.ofReal (δ ^ eps) * totalWeighted ≤
        ∑ i : Fin N_all, (if theta / 2 ≤ scale_i i ∧ scale_i i ≤ theta then mass_i i else 0) :=
    dyadic_pigeonhole_scale hδ hδ_le1 N_all mass_i scale_i h_scales_i
      totalWeighted (by rw [h_sum_eq]) eps heps_pos (h_pigeonhole_condition δ hδ hδ_le)
  let theta_raw : ℝ := Classical.choose h_pigeonhole_result
  have h_pigeonhole_spec : δ ≤ theta_raw ∧ theta_raw ≤ 1 ∧
      (∃ k : ℕ, theta_raw = (1 / 2 : ℝ) ^ k) ∧
      ENNReal.ofReal (δ ^ eps) * totalWeighted ≤
        ∑ i : Fin N_all, (if theta_raw / 2 ≤ scale_i i ∧ scale_i i ≤ theta_raw then mass_i i else 0) :=
    Classical.choose_spec h_pigeonhole_result
  have h_theta_rawδ : δ ≤ theta_raw := h_pigeonhole_spec.1
  have h_theta_raw1 : theta_raw ≤ 1 := h_pigeonhole_spec.2.1
  rcases h_pigeonhole_spec.2.2.1 with ⟨k0, h_theta_dyadic⟩
  have h_retained_raw : ENNReal.ofReal (δ ^ eps) * totalWeighted ≤
      ∑ i : Fin N_all, (if theta_raw / 2 ≤ scale_i i ∧ scale_i i ≤ theta_raw then mass_i i else 0) :=
    h_pigeonhole_spec.2.2.2

  -- Cap theta at 1/2: if pigeonhole gives theta > 1/2 (i.e. theta = 1),
  -- all retained scales equal 1/2, so theta = 1/2 retains at least as much mass.
  let theta : ℝ := min theta_raw (1 / 2)
  have h_thetaδ : δ ≤ theta := le_min h_theta_rawδ hδ_le_half
  have h_theta1 : theta ≤ 1 := by
    have h : theta ≤ 1 / 2 := min_le_right _ _
    linarith
  have h_theta_pos : 0 < theta := by linarith [hδ]
  have h_theta_le_half : theta ≤ 1 / 2 := min_le_right _ _

  -- Retained mass bound for capped theta
  have h_retained : ENNReal.ofReal (δ ^ eps) * totalWeighted ≤
      ∑ i : Fin N_all, (if theta / 2 ≤ scale_i i ∧ scale_i i ≤ theta then mass_i i else 0) := by
    by_cases h : theta_raw ≤ 1 / 2
    · have h_eq : theta = theta_raw := by
        exact min_eq_left h
      rw [h_eq]
      exact h_retained_raw
    · have h_gt : theta_raw > 1 / 2 := by linarith
      have h_k0_zero : k0 = 0 := by
        by_contra h'
        have h_pos : 0 < k0 := Nat.pos_of_ne_zero h'
        have h1 : theta_raw ≤ 1 / 2 := by
          rw [h_theta_dyadic]
          have h2 : (1 / 2 : ℝ) ^ k0 ≤ (1 / 2 : ℝ) ^ 1 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by linarith)
          simpa using h2
        linarith
      have h_raw_one : theta_raw = 1 := by
        rw [h_theta_dyadic, h_k0_zero] <;> norm_num
      have h_eq : theta = 1 / 2 := by
        exact min_eq_right (by linarith)
      have h_retained_one : ENNReal.ofReal (δ ^ eps) * totalWeighted ≤
          ∑ i : Fin N_all, (if (1 : ℝ) / 2 ≤ scale_i i ∧ scale_i i ≤ (1 : ℝ) then mass_i i else 0) := by
        rw [h_raw_one] at h_retained_raw
        exact h_retained_raw
      rw [h_eq]
      have h_sum_ineq : ∑ i : Fin N_all, (if (1 / 2 : ℝ) / 2 ≤ scale_i i ∧ scale_i i ≤ (1 / 2 : ℝ) then mass_i i else 0) ≥
          ∑ i : Fin N_all, (if (1 : ℝ) / 2 ≤ scale_i i ∧ scale_i i ≤ (1 : ℝ) then mass_i i else 0) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hcond : (1 : ℝ) / 2 ≤ scale_i i ∧ scale_i i ≤ (1 : ℝ)
        · have h_scale_half : scale_i i = 1 / 2 := by
            have h1 : scale_i i ≤ 1 / 2 := (h_r_S'_range (idx i) (h_idx_mem i)).2
            have h2 : (1 : ℝ) / 2 ≤ scale_i i := hcond.1
            linarith
          have hcond2 : (1 / 2 : ℝ) / 2 ≤ scale_i i ∧ scale_i i ≤ (1 / 2 : ℝ) := by
            rw [h_scale_half] <;> norm_num
          rw [if_pos hcond, if_pos hcond2]
        · rw [if_neg hcond] <;> simp
      exact le_trans h_retained_one h_sum_ineq

  -- Retained patterns
  let retainedPatterns : Finset (Finset (Kakeya.DeltaTube δ)) :=
    F.powerset.filter (fun S => theta / 2 ≤ r_S' S ∧ r_S' S ≤ theta)

  -- Helper: W_S' S ⊆ S
  have hW'_subset : ∀ (S : Finset (Kakeya.DeltaTube δ)), W_S' S ⊆ S := by
    intro S
    by_cases hSne : S.Nonempty
    · have hW_eq : W_S' S = S.filter (fun T => hairbrushAcuteDirectionAngle T.direction (w_S S hSne) ≤ r_S S hSne) := by
        simp only [W_S', dif_pos hSne]
        exact (h_w_spec S hSne).2.2.2.1
      rw [hW_eq]; exact Finset.filter_subset _ _
    · simp only [W_S', dif_neg hSne]; exact Finset.empty_subset _

  -- Retained shading
  let retainedShading : Kakeya.Shading F :=
    { carrier := fun T =>
        ⋃ S ∈ retainedPatterns.filter (fun S => T ∈ W_S' S), throughPattern Y S
      measurable_carrier := fun T _hT =>
        Finset.measurableSet_biUnion (retainedPatterns.filter (fun S => T ∈ W_S' S))
          (fun S hS => throughPattern_measurable Y
            (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1)
      subset_tube := fun T hT => by
        intro x hx
        have h_exists : ∃ (S : Finset (Kakeya.DeltaTube δ)),
            S ∈ retainedPatterns.filter (fun S => T ∈ W_S' S) ∧ x ∈ throughPattern Y S := by
          simpa using hx
        rcases h_exists with ⟨S, hS, hxS⟩
        have hS_retained : S ∈ retainedPatterns := (Finset.mem_filter.mp hS).1
        have hT_in_W : T ∈ W_S' S := (Finset.mem_filter.mp hS).2
        have h_sub : W_S' S ⊆ S := hW'_subset S
        have hT_in_S : T ∈ S := h_sub hT_in_W
        have h_filter_eq : F.filter (fun T' => x ∈ Y.carrier T') = S := hxS.2
        have hT_in_filter : T ∈ F.filter (fun T' => x ∈ Y.carrier T') := by
          rw [h_filter_eq]; exact hT_in_S
        have h_x_in_Y : x ∈ Y.carrier T := (Finset.mem_filter.mp hT_in_filter).2
        exact Y.subset_tube hT h_x_in_Y }

  have h_retained_mass : retainedShading.mass =
      ∑ S ∈ retainedPatterns, weightedMass S := by
    have h1 : retainedShading.mass = ∑ T ∈ F, volume (retainedShading.carrier T) := by rfl
    rw [h1]
    have h2 : ∀ T ∈ F, volume (retainedShading.carrier T) =
        ∑ S ∈ retainedPatterns.filter (fun S => T ∈ W_S' S), volume (throughPattern Y S) := by
      intro T _hT
      let sF : Finset (Finset (Kakeya.DeltaTube δ)) := retainedPatterns.filter (fun S => T ∈ W_S' S)
      have h_disj : Set.PairwiseDisjoint (sF : Set (Finset (Kakeya.DeltaTube δ))) (throughPattern Y) := by
        intro S hS T' hT' hne
        have hS_retained : S ∈ retainedPatterns := (Finset.mem_filter.mp hS).1
        have hT'_retained : T' ∈ retainedPatterns := (Finset.mem_filter.mp hT').1
        have hS_in : S ∈ F.powerset := (Finset.mem_filter.mp hS_retained).1
        have hT'_in : T' ∈ F.powerset := (Finset.mem_filter.mp hT'_retained).1
        exact (throughPattern_partition Y).1 hS_in hT'_in hne
      have h_meas : ∀ S ∈ sF, MeasurableSet (throughPattern Y S) := by
        intro S hS
        have hS_retained : S ∈ retainedPatterns := (Finset.mem_filter.mp hS).1
        exact throughPattern_measurable Y (Finset.mem_filter.mp hS_retained).1
      have h_eq : retainedShading.carrier T = ⋃ S ∈ sF, throughPattern Y S := by rfl
      rw [h_eq]
      exact MeasureTheory.measure_biUnion_finset h_disj h_meas
    have h_sum1 : ∑ T ∈ F, volume (retainedShading.carrier T) =
        ∑ T ∈ F, ∑ S ∈ retainedPatterns.filter (fun S => T ∈ W_S' S), volume (throughPattern Y S) := by
      apply Finset.sum_congr rfl
      intro T hT
      exact h2 T hT
    have h3 : ∑ T ∈ F, ∑ S ∈ retainedPatterns.filter (fun S => T ∈ W_S' S), volume (throughPattern Y S) =
        ∑ S ∈ retainedPatterns, (W_S' S).card * volume (throughPattern Y S) := by
      calc
        ∑ T ∈ F, ∑ S ∈ retainedPatterns.filter (fun S => T ∈ W_S' S), volume (throughPattern Y S)
          = ∑ T ∈ F, ∑ S ∈ retainedPatterns, (if T ∈ W_S' S then volume (throughPattern Y S) else 0) := by
            apply Finset.sum_congr rfl
            intro T _
            exact Finset.sum_filter (s := retainedPatterns) (p := fun S => T ∈ W_S' S) (f := fun S => volume (throughPattern Y S))
        _ = ∑ S ∈ retainedPatterns, ∑ T ∈ F, (if T ∈ W_S' S then volume (throughPattern Y S) else 0) := by
            rw [Finset.sum_comm]
        _ = ∑ S ∈ retainedPatterns, (W_S' S).card * volume (throughPattern Y S) := by
            apply Finset.sum_congr rfl
            intro S hS
            have hS_pow : S ∈ F.powerset := (Finset.mem_filter.mp hS).1
            have hW_sub_F : W_S' S ⊆ F := by
              have h1 : W_S' S ⊆ S := hW'_subset S
              have h2 : S ⊆ F := Finset.mem_powerset.mp hS_pow
              exact Finset.Subset.trans h1 h2
            have h_eq1 : ∑ T ∈ F, (if T ∈ W_S' S then volume (throughPattern Y S) else 0) =
                ∑ T ∈ W_S' S, volume (throughPattern Y S) := by
              have h_filter_eq : F.filter (fun T => T ∈ W_S' S) = W_S' S := by
                ext T
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                constructor
                · intro h; exact h.2
                · intro h; exact ⟨hW_sub_F h, h⟩
              have h_sum_filter : ∑ T ∈ F.filter (fun T => T ∈ W_S' S), volume (throughPattern Y S) =
                  ∑ T ∈ F, (if T ∈ W_S' S then volume (throughPattern Y S) else 0) :=
                Finset.sum_filter (s := F) (p := fun T => T ∈ W_S' S) (f := fun T => volume (throughPattern Y S))
              rw [← h_sum_filter, h_filter_eq]
            rw [h_eq1]
            rw [Finset.sum_const]
            <;> ring
    rw [h_sum1, h3]
    <;> rfl

  have h_retained_sum_eq : ∑ S ∈ retainedPatterns, weightedMass S =
      ∑ i : Fin N_all, (if theta / 2 ≤ scale_i i ∧ scale_i i ≤ theta then mass_i i else 0) := by
    have h4 : retainedPatterns = Finset.image idx (Finset.univ.filter (fun i : Fin N_all => theta / 2 ≤ scale_i i ∧ scale_i i ≤ theta)) := by
      ext S
      simp only [retainedPatterns, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro h
        have hS_pow : S ∈ F.powerset := h.1
        have h5 : ∃ (i : Fin N_all), idx i = S := by
          refine ⟨e_all.symm ⟨S, hS_pow⟩, ?_⟩
          simp [idx]
        rcases h5 with ⟨i, rfl⟩
        exact ⟨i, h.2, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨h_idx_mem i, hi⟩
    rw [h4]
    have h_inj : Set.InjOn idx (Finset.univ.filter (fun i : Fin N_all => theta / 2 ≤ scale_i i ∧ scale_i i ≤ theta)) := by
      intro i _ j _ h
      exact e_all.injective (Subtype.ext h)
    rw [Finset.sum_image h_inj]
    have h_rw : ∑ i : Fin N_all, (if theta / 2 ≤ scale_i i ∧ scale_i i ≤ theta then mass_i i else 0) =
        ∑ i ∈ (Finset.univ.filter (fun i : Fin N_all => theta / 2 ≤ scale_i i ∧ scale_i i ≤ theta)), mass_i i := by
      rw [Finset.sum_filter]
      <;> rfl
    rw [h_rw]
    <;> rfl

  have h_mass_retention : Kakeya.realRpowENN δ stopLoss * Y.mass ≤ retainedShading.mass := by
    rw [h_retained_mass, h_retained_sum_eq]
    have h1 : ENNReal.ofReal (δ ^ eps) * totalWeighted ≤ _ := h_retained
    have h2 : totalWeighted ≥ (1 / 1000 : ENNReal) * Kakeya.realRpowENN δ eta * Y.mass :=
      h_total_weighted_lower
    have h4 : ENNReal.ofReal (δ ^ eps) = Kakeya.realRpowENN δ eps := by rfl
    have h61 : δ ^ (eps + eta) = (δ ^ eps) * (δ ^ eta) := Real.rpow_add (by linarith) eps eta
    have h6 : Kakeya.realRpowENN δ eps * Kakeya.realRpowENN δ eta = Kakeya.realRpowENN δ (eps + eta) := by
      have hpos1 : 0 ≤ δ ^ eps := by positivity
      have hpos2 : 0 ≤ δ ^ eta := by positivity
      simp only [Kakeya.realRpowENN]
      calc ENNReal.ofReal (δ ^ eps) * ENNReal.ofReal (δ ^ eta)
          = ENNReal.ofReal ((δ ^ eps) * (δ ^ eta)) := (ENNReal.ofReal_mul hpos1).symm
        _ = ENNReal.ofReal (δ ^ (eps + eta)) := by rw [h61]
    have h9 : Kakeya.realRpowENN δ stopLoss ≤ (1 / 1000 : ENNReal) * Kakeya.realRpowENN δ (stopLoss - epsilon2) :=
      h_absorb δ hδ hδ_le
    have h_step1 : Kakeya.realRpowENN δ stopLoss * Y.mass ≤
        ((1 / 1000 : ENNReal) * Kakeya.realRpowENN δ (stopLoss - epsilon2)) * Y.mass := by
      gcongr
      <;> exact h9
    have h_step2 : ((1 / 1000 : ENNReal) * Kakeya.realRpowENN δ (stopLoss - epsilon2)) * Y.mass =
        ((1 / 1000 : ENNReal) * Kakeya.realRpowENN δ (eps + eta)) * Y.mass := by
      rw [show eps + eta = stopLoss - epsilon2 from h_eps_eta]
    have h_step3 : ((1 / 1000 : ENNReal) * Kakeya.realRpowENN δ (eps + eta)) * Y.mass =
        ((1 / 1000 : ENNReal) * (Kakeya.realRpowENN δ eps * Kakeya.realRpowENN δ eta)) * Y.mass := by
      rw [h6]
    have h_step4 : ((1 / 1000 : ENNReal) * (Kakeya.realRpowENN δ eps * Kakeya.realRpowENN δ eta)) * Y.mass =
        Kakeya.realRpowENN δ eps * ((1 / 1000 : ENNReal) * Kakeya.realRpowENN δ eta * Y.mass) := by
      simp [mul_assoc, mul_comm, mul_left_comm]
      <;> ac_rfl
    have h_step5 : Kakeya.realRpowENN δ eps * ((1 / 1000 : ENNReal) * Kakeya.realRpowENN δ eta * Y.mass) ≤
        Kakeya.realRpowENN δ eps * totalWeighted := by gcongr
    have h_step6 : Kakeya.realRpowENN δ eps * totalWeighted = ENNReal.ofReal (δ ^ eps) * totalWeighted := by
      rw [h4]
    calc
      Kakeya.realRpowENN δ stopLoss * Y.mass
        ≤ ((1 / 1000 : ENNReal) * Kakeya.realRpowENN δ (stopLoss - epsilon2)) * Y.mass := h_step1
      _ = ((1 / 1000 : ENNReal) * Kakeya.realRpowENN δ (eps + eta)) * Y.mass := h_step2
      _ = ((1 / 1000 : ENNReal) * (Kakeya.realRpowENN δ eps * Kakeya.realRpowENN δ eta)) * Y.mass := h_step3
      _ = Kakeya.realRpowENN δ eps * ((1 / 1000 : ENNReal) * Kakeya.realRpowENN δ eta * Y.mass) := h_step4
      _ ≤ Kakeya.realRpowENN δ eps * totalWeighted := h_step5
      _ = ENNReal.ofReal (δ ^ eps) * totalWeighted := h_step6
      _ ≤ _ := h1

  -- theta is always ≤ 1/2 by construction
  have h_theta_le_half' : theta ≤ 1 / 2 := h_theta_le_half

  -- r_S' = r_S by definition (no cap), so equalities are trivial
  have h_r_S_eq : ∀ S ∈ retainedPatterns, ∀ (hSne : S.Nonempty),
      r_S S hSne = r_S' S ∧ W_S' S = W_S S hSne ∧ w_S' S = w_S S hSne := by
    intro S _hS hSne
    exact ⟨by simp [r_S', hSne], by simp [W_S', hSne], by simp [w_S', hSne]⟩

  -- Centers finset
  let centers : Finset Point3 := retainedPatterns.image w_S'
  have h_centers_unit : ∀ v ∈ centers, ‖v‖ = 1 := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨S, hS, rfl⟩
    exact h_w_S'_unit S (Finset.mem_filter.mp hS).1

  -- Index retained patterns
  let N_retained : ℕ := retainedPatterns.card
  let e_retained : Fin N_retained ≃ {S // S ∈ retainedPatterns} :=
    (Finset.equivFin retainedPatterns).symm
  let idxR (i : Fin N_retained) := (e_retained i).val
  have h_idxR_mem : ∀ i, idxR i ∈ retainedPatterns := fun i => (e_retained i).property

  let patToCenter (i : Fin N_retained) : Point3 := w_S' (idxR i)
  have hpat : ∀ i, patToCenter i ∈ centers := by
    intro i
    exact Finset.mem_image.mpr ⟨idxR i, h_idxR_mem i, rfl⟩

  let A (i : Fin N_retained) : Set Point3 := throughPattern Y (idxR i)
  have hA : ∀ i, MeasurableSet (A i) := by
    intro i
    exact throughPattern_measurable Y (Finset.mem_filter.mp (h_idxR_mem i)).1
  have hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j) := by
    intro i j hne
    have hS_i : idxR i ∈ F.powerset := (Finset.mem_filter.mp (h_idxR_mem i)).1
    have hS_j : idxR j ∈ F.powerset := (Finset.mem_filter.mp (h_idxR_mem j)).1
    have h_ne : idxR i ≠ idxR j := by
      intro h
      have h' : i = j := by
        have h_inj : ∀ a b, idxR a = idxR b → a = b := by
          intro a b hab
          exact e_retained.injective (Subtype.ext hab)
        exact h_inj i j h
      exact hne h'
    exact (throughPattern_partition Y).1 hS_i hS_j h_ne

  -- Apply net_and_label
  rcases net_and_label centers h_centers_unit theta h_theta_pos h_theta_le_half'
      patToCenter hpat A hA hdisj with
    ⟨labelCount, hlabelCount_pos, label, center, h_label_measurable, h_center_unit, h_confinement, h_overlap⟩

  let capRadius : ℝ := 2 * theta
  have h_theta_le_cap : theta ≤ capRadius := by linarith
  have h_cap_le_six : capRadius ≤ 6 * theta := by linarith
  have h_cap_le_one : capRadius ≤ 1 := by linarith [h_theta_le_half]

  -- Pointwise confinement
  have h_pointwise_confined :
      ∀ x ∈ retainedShading.union, ∀ T ∈ F, x ∈ retainedShading.carrier T →
        hairbrushAcuteDirectionAngle T.direction (center (label x)) ≤ capRadius := by
    intro x hx T hT hxT
    have h_exists := by simpa [retainedShading] using hxT
    rcases h_exists with ⟨S, hS, hxS⟩
    have hS_retained : S ∈ retainedPatterns := hS.1
    have h_x_in_A : x ∈ A (e_retained.symm ⟨S, hS_retained⟩) := by
      simpa [A, idxR] using hxS
    have hT_in_W : T ∈ W_S' S := hS.2
    have hSne : S.Nonempty := by
      by_contra h
      have hW_empty : W_S' S = ∅ := by simp [W_S', h]
      rw [hW_empty] at hT_in_W
      simpa using hT_in_W
    have h_eq := h_r_S_eq S hS_retained hSne
    have h_angle_T : hairbrushAcuteDirectionAngle T.direction (w_S' S) ≤ theta := by
      have hW_eq : W_S' S = S.filter (fun T' => hairbrushAcuteDirectionAngle T'.direction (w_S S hSne) ≤ r_S S hSne) := by
        simp only [W_S', dif_pos hSne]
        exact (h_w_spec S hSne).2.2.2.1
      rw [hW_eq] at hT_in_W
      have h : hairbrushAcuteDirectionAngle T.direction (w_S S hSne) ≤ r_S S hSne :=
        (Finset.mem_filter.mp hT_in_W).2
      have h_r_le_theta : r_S S hSne ≤ theta := by
        have h5 : r_S' S ≤ theta := (Finset.mem_filter.mp hS_retained).2.2
        exact h_eq.1.symm ▸ h5
      rw [h_eq.2.2]
      exact h.trans h_r_le_theta
    have hT_dir_unit : ‖T.direction‖ = 1 := T.direction_unit
    have h_pat : patToCenter (e_retained.symm ⟨S, hS_retained⟩) = w_S' S := by
      simp [patToCenter, idxR] <;> rfl
    have h_angle_T' : hairbrushAcuteDirectionAngle T.direction (patToCenter (e_retained.symm ⟨S, hS_retained⟩)) ≤ theta := by
      rw [h_pat]
      exact h_angle_T
    exact h_confinement (e_retained.symm ⟨S, hS_retained⟩) x h_x_in_A T.direction hT_dir_unit h_angle_T'

  -- Label overlap
  have h_label_overlap :
      ∀ T ∈ F, ((Finset.univ.filter fun j : Fin labelCount =>
        ∃ x ∈ retainedShading.carrier T, label x = j).card : ENNReal) ≤ 1000 := by
    intro T _hT
    let J1 : Finset (Fin labelCount) := Finset.univ.filter (fun j =>
        ∃ x ∈ retainedShading.carrier T, label x = j)
    let J2 : Finset (Fin labelCount) := Finset.univ.filter (fun j =>
        hairbrushAcuteDirectionAngle (center j) T.direction ≤ capRadius)
    have h_sub : J1 ⊆ J2 := by
      intro j hj
      have h1 : ∃ x ∈ retainedShading.carrier T, label x = j :=
        (Finset.mem_filter.mp hj).2
      rcases h1 with ⟨x, hxT, rfl⟩
      have h2 : hairbrushAcuteDirectionAngle T.direction (center (label x)) ≤ capRadius :=
        h_pointwise_confined x (by
          have h3 : x ∈ retainedShading.carrier T := hxT
          exact ⟨T, ‹_›, h3⟩) T ‹_› hxT
      have h2' : hairbrushAcuteDirectionAngle (center (label x)) T.direction ≤ capRadius := by
        simpa [hairbrushAcuteDirectionAngle, real_inner_comm] using h2
      simpa [J2, Finset.mem_filter] using h2'
    have h3 : J1.card ≤ J2.card := Finset.card_le_card h_sub
    have h4 : J2.card ≤ 1000 := h_overlap T.direction T.direction_unit
    exact_mod_cast h3.trans h4

  -- Two-broadness
  have h_two_broad_main : ∀ (x : Point3), x ∈ retainedShading.union →
      ∃ (w : Point3) (r : ℝ) (Wx : Finset (Kakeya.DeltaTube δ)),
        ‖w‖ = 1 ∧ δ ≤ r ∧ theta / 2 ≤ r ∧ r ≤ theta ∧
        (∀ (v : Point3), ‖v‖ = 1 → ∀ (s : ℝ), δ ≤ s → s ≤ r →
          ((Wx.filter (fun T => hairbrushAcuteDirectionAngle T.direction v ≤ s)).card : ℝ) ≤
            Real.rpow (s / r) eta * (Wx.card : ℝ)) ∧
        (F.filter (fun T => x ∈ retainedShading.carrier T)) = Wx := by
    intro x hx
    rcases hx with ⟨T0, hT0, hxT0⟩
    have h_exists := by simpa [retainedShading] using hxT0
    rcases h_exists with ⟨S, hS, hxS⟩
    have hS_retained : S ∈ retainedPatterns := hS.1
    have hT0_in_W : T0 ∈ W_S' S := hS.2
    have hSne : S.Nonempty := by
      by_contra h
      have hW_empty : W_S' S = ∅ := by simp [W_S', h]
      rw [hW_empty] at hT0_in_W
      simpa using hT0_in_W
    have h_eq := h_r_S_eq S hS_retained hSne
    have hspec := h_w_spec S hSne
    let w := w_S S hSne
    let r := r_S S hSne
    let Wx := W_S S hSne
    have h_through_eq : F.filter (fun T => x ∈ retainedShading.carrier T) = Wx := by
      apply Finset.ext
      intro T
      have h_xin_pattern : x ∈ throughPattern Y S := hxS
      have h_iff : x ∈ retainedShading.carrier T ↔ T ∈ Wx := by
        constructor
        · intro hxt
          have h_exists_S' := by simpa [retainedShading] using hxt
          rcases h_exists_S' with ⟨S', hS', hxS'⟩
          have h_disj : S' = S := by
            have h1 : x ∈ throughPattern Y S' := hxS'
            have h2 : S' ∈ F.powerset := (Finset.mem_filter.mp hS'.1).1
            have h3 : S ∈ F.powerset := (Finset.mem_filter.mp hS_retained).1
            by_contra h4
            have h_disj' : Disjoint (throughPattern Y S') (throughPattern Y S) :=
              (throughPattern_partition Y).1 h2 h3 h4
            exact Set.disjoint_left.mp h_disj' h1 h_xin_pattern
          rw [h_disj] at hS'
          have hT_in_W : T ∈ W_S' S := hS'.2
          rw [h_eq.2.1] at hT_in_W
          exact hT_in_W
        · intro hTinW
          have h : T ∈ W_S' S := by simpa [W_S', hSne] using hTinW
          have h_mem : S ∈ retainedPatterns.filter (fun S => T ∈ W_S' S) :=
            Finset.mem_filter.mpr ⟨hS_retained, h⟩
          have h_goal : x ∈ ⋃ S' ∈ retainedPatterns.filter (fun S' => T ∈ W_S' S'), throughPattern Y S' := by
            exact Set.mem_iUnion₂.mpr ⟨S, h_mem, h_xin_pattern⟩
          exact h_goal
      have h_goal : T ∈ F.filter (fun T => x ∈ retainedShading.carrier T) ↔ T ∈ Wx := by
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨_, hxt⟩
          exact h_iff.mp hxt
        · intro hTinW
          have hW_sub_F : Wx ⊆ F := by
            have h1 : W_S' S ⊆ S := hW'_subset S
            have h2 : Wx = W_S' S := h_eq.2.1.symm
            rw [h2]
            have h3 : S ⊆ F := Finset.mem_powerset.mp (Finset.mem_filter.mp hS_retained).1
            exact Finset.Subset.trans h1 h3
          have hT_in_F : T ∈ F := hW_sub_F hTinW
          exact ⟨hT_in_F, h_iff.mpr hTinW⟩
      exact h_goal
    have h_r_in_interval : theta / 2 ≤ r ∧ r ≤ theta := by
      have h5 : theta / 2 ≤ r_S' S ∧ r_S' S ≤ theta := (Finset.mem_filter.mp hS_retained).2
      have h7 : r_S' S = r := h_eq.1.symm
      rw [h7] at h5
      exact h5
    exact ⟨w, r, Wx, hspec.1, hspec.2.1, h_r_in_interval.1, h_r_in_interval.2, hspec.2.2.2.2.2.1, h_through_eq⟩

  have h_two_broad : IsTwoBroadAtScale retainedShading theta eta :=
    two_broadness_small_scale retainedShading theta eta hδ heta h_two_broad_main

  -- Shading subset
  have h_shading_subset : ∀ T ∈ F, retainedShading.carrier T ⊆ Y.carrier T := by
    intro T hT x hx
    have h_exists := by simpa [retainedShading] using hx
    rcases h_exists with ⟨S, hS, hxS⟩
    have hS_retained : S ∈ retainedPatterns := hS.1
    have hT_in_W : T ∈ W_S' S := hS.2
    have h_sub : W_S' S ⊆ S := hW'_subset S
    have hT_in_S : T ∈ S := h_sub hT_in_W
    have h_filter_eq : F.filter (fun T' => x ∈ Y.carrier T') = S := hxS.2
    have hT_in_filter : T ∈ F.filter (fun T' => x ∈ Y.carrier T') := by
      rw [h_filter_eq]; exact hT_in_S
    exact (Finset.mem_filter.mp hT_in_filter).2

  -- Prove retainedPatterns.Nonempty
  have h_total_pos : 0 < totalWeighted := by
    have h1 : totalWeighted ≥ (1 / 1000 : ENNReal) * Kakeya.realRpowENN δ eta * Y.mass := h_total_weighted_lower
    have h2 : 0 < Y.mass := Ne.bot_lt hYmass_pos
    have h_eta_pos : 0 < δ ^ eta := Real.rpow_pos_of_pos hδ eta
    have h21 : 0 < Kakeya.realRpowENN δ eta := by
      simp only [Kakeya.realRpowENN]
      exact ENNReal.ofReal_pos.mpr h_eta_pos
    have h_pos1 : (1 / 1000 : ENNReal) ≠ 0 := by norm_num
    have h_pos2 : (Kakeya.realRpowENN δ eta) ≠ 0 := h21.ne'
    have h_pos3 : Y.mass ≠ 0 := h2.ne'
    have h_ne_zero : ((1 / 1000 : ENNReal) * Kakeya.realRpowENN δ eta * Y.mass) ≠ 0 :=
      mul_ne_zero (mul_ne_zero h_pos1 h_pos2) h_pos3
    have h3 : 0 < ((1 / 1000 : ENNReal) * Kakeya.realRpowENN δ eta * Y.mass) :=
      Ne.bot_lt h_ne_zero
    exact h3.trans_le h1
  have h_sum_pos : 0 < ∑ i : Fin N_all, (if theta / 2 ≤ scale_i i ∧ scale_i i ≤ theta then mass_i i else 0) := by
    have h_eps_pos : 0 < δ ^ eps := Real.rpow_pos_of_pos hδ eps
    have h41 : 0 < ENNReal.ofReal (δ ^ eps) := ENNReal.ofReal_pos.mpr h_eps_pos
    have h42 : ENNReal.ofReal (δ ^ eps) ≠ 0 := h41.ne'
    have h43 : totalWeighted ≠ 0 := h_total_pos.ne'
    have h44 : ENNReal.ofReal (δ ^ eps) * totalWeighted ≠ 0 := mul_ne_zero h42 h43
    have h4 : 0 < ENNReal.ofReal (δ ^ eps) * totalWeighted :=
      Ne.bot_lt h44
    exact h4.trans_le h_retained
  have h_exists_pos : ∃ (i : Fin N_all), (theta / 2 ≤ scale_i i ∧ scale_i i ≤ theta) ∧ 0 < mass_i i := by
    by_contra h
    push Not at h
    have h5 : ∑ i : Fin N_all, (if theta / 2 ≤ scale_i i ∧ scale_i i ≤ theta then mass_i i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases h6 : theta / 2 ≤ scale_i i ∧ scale_i i ≤ theta
      · have h7 : mass_i i = 0 := by
          have h8 : mass_i i ≤ 0 := h i h6
          simpa using h8
        rw [if_pos h6, h7]
      · rw [if_neg h6]
    rw [h5] at h_sum_pos
    exact lt_irrefl 0 h_sum_pos
  rcases h_exists_pos with ⟨i, hcond, _⟩
  have h_retained_nonempty : retainedPatterns.Nonempty := by
    refine ⟨idx i, ?_⟩
    simp only [retainedPatterns, Finset.mem_filter]
    exact ⟨h_idx_mem i, hcond⟩
  have h_labelCount_pos : 0 < labelCount := by
    by_contra h
    have h0 : labelCount = 0 := by omega
    have h1 : Fin labelCount := label (0 : Point3)
    rw [h0] at h1
    exact Fin.elim0 h1

  refine ⟨theta, h_thetaδ, h_theta1, capRadius, h_theta_le_cap, h_cap_le_six, h_cap_le_one,
    retainedShading, h_shading_subset, h_mass_retention, labelCount,
    h_labelCount_pos,
    label, h_label_measurable, center, h_center_unit, h_pointwise_confined,
    h_label_overlap, h_two_broad⟩

end Kakeya.Assouad
