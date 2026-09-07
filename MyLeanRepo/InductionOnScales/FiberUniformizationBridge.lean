module

public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.Pigeonhole
public import MyLeanRepo.InductionOnScales.UniformFibers
public import MyLeanRepo.InductionOnScales.FiberAwareTrimming
public import MyLeanRepo.InductionOnScales.NiceConfigHelpers
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Fiber Uniformization Bridge

Integrates `fiber_aware_trimming` into the coarse phase, producing
a fiber-uniform coarseConfig with all properties needed for Steps 5-14.

## Main result

`fiber_aware_coarse_phase`: Given per-Q coarse tube families with SSet,
incidence, and parameter strip, produces a fiber-uniform coarseConfig
where every tube has fiber size in `[NΔ, 4*NΔ)`.

## Loss factor

`K_loss = 2 * numDyadicLevels(config.tubes.card)^2 = O(log² |config.tubes|)`.
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace InductionOnScales

/-- Complete fiber-aware coarse phase. -/
lemma fiber_aware_coarse_phase
    {n m : ℕ} (hnm : m ≤ n)
    {s C₁ : ℝ} {M MΔ_orig : ℕ}
    (config : NiceConfiguration n s C₁ M)
    (QSet : Finset (DyadicSquare m))
    (coarseTubes_Q : DyadicSquare m → Finset (DyadicTube m))
    (hMΔ_orig_pos : 0 < MΔ_orig)
    (h_size_lower : ∀ Q ∈ QSet, MΔ_orig ≤ (coarseTubes_Q Q).card)
    (h_size_upper : ∀ Q ∈ QSet, (coarseTubes_Q Q).card < 2 * MΔ_orig)
    (C₂_Q : DyadicSquare m → ℝ)
    (h_sset_Q : ∀ Q ∈ QSet, IsFiniteTubeSSet s (C₂_Q Q) (coarseTubes_Q Q))
    (C₂_max : ℝ)
    (hC₂_max : ∀ Q ∈ QSet, C₂_Q Q ≤ C₂_max)
    (hC₂_max_one : 1 ≤ C₂_max)
    (h_fiber_pos : ∀ Q ∈ QSet, ∀ U ∈ coarseTubes_Q Q,
      0 < fiberSize hnm config.tubes U)
    (h_incidence : ∀ Q ∈ QSet, ∀ U ∈ coarseTubes_Q Q,
      (U.toSet ∩ Q.toSet).Nonempty)
    (h_strip : ∀ Q ∈ QSet, ∀ U ∈ coarseTubes_Q Q,
      U.IsInAllowedParameterStrip)
    (h_bounded : ∀ Q ∈ QSet, Q.toSet ⊆ unitSquare)
    (hQSet_nonempty : QSet.Nonempty) :
    ∃ (QSet' : Finset (DyadicSquare m))
      (MΔ_new : ℕ)
      (trimmedFamily : DyadicSquare m → Finset (DyadicTube m))
      (CΔ : ℝ)
      (coarseConfig : NiceConfiguration m s CΔ MΔ_new)
      (NΔ : ℕ)
      (K_loss : ℝ),
      1 ≤ K_loss ∧
      QSet' ⊆ QSet ∧
      (QSet.card : ℝ) ≤ K_loss * (QSet'.card : ℝ) ∧
      0 < MΔ_new ∧
      (MΔ_orig : ℝ) ≤ K_loss * (MΔ_new : ℝ) ∧
      CΔ = 2 * K_loss * C₂_max ∧
      (∀ Q ∈ QSet', (trimmedFamily Q).card = MΔ_new) ∧
      (∀ Q ∈ QSet', trimmedFamily Q ⊆ coarseTubes_Q Q) ∧
      (∀ Q ∈ QSet', ∀ U ∈ trimmedFamily Q,
        NΔ ≤ fiberSize hnm config.tubes U ∧
        fiberSize hnm config.tubes U < 4 * NΔ) ∧
      coarseConfig.points = QSet' ∧
      coarseConfig.tubes = QSet'.biUnion trimmedFamily ∧
      (∀ (Q : DyadicSquare m) (hQ : Q ∈ coarseConfig.points),
        coarseConfig.tubeFamily Q hQ = trimmedFamily Q) ∧
      (∀ Q ∈ QSet', ∀ U ∈ trimmedFamily Q,
        (U.toSet ∩ Q.toSet).Nonempty) ∧
      (∀ Q ∈ QSet', ∀ U ∈ trimmedFamily Q,
        U.IsInAllowedParameterStrip) ∧
      (∀ Q ∈ QSet', Q.toSet ⊆ unitSquare) ∧
      K_loss = 2 * (numDyadicLevels config.tubes.card : ℝ)^2 := by
  have hQSet_ne : QSet ≠ ∅ := by
    simpa [Finset.nonempty_iff_ne_empty] using hQSet_nonempty

  have h_config_tubes_pos : 0 < config.tubes.card := by
    rcases hQSet_nonempty with ⟨Q0, hQ0⟩
    have h1 : MΔ_orig ≤ (coarseTubes_Q Q0).card := h_size_lower Q0 hQ0
    have h2 : (coarseTubes_Q Q0).Nonempty := Finset.card_pos.mp (by omega)
    rcases h2 with ⟨U0, hU0⟩
    have h3 : 0 < fiberSize hnm config.tubes U0 := h_fiber_pos Q0 hQ0 U0 hU0
    have h4 : fiberSize hnm config.tubes U0 ≤ config.tubes.card := by
      simpa [fiberSize] using Finset.card_filter_le config.tubes _
    omega

  rcases InductionOnScales.fiber_aware_trimming hnm QSet coarseTubes_Q
      MΔ_orig hMΔ_orig_pos h_size_lower config.tubes h_config_tubes_pos h_fiber_pos
    with ⟨NΔ, QSet', trimmedFamily, MΔ_new, K_loss, h_main⟩
  rcases h_main with ⟨hK_loss_one, hQSet'_sub, hQSet'_cover, hMΔ_new_pos,
    h_trimmed_card, h_trimmed_sub, h_fiber_band, h_retention, hK_loss_eq⟩

  let CΔ : ℝ := 2 * K_loss * C₂_max
  have hCΔ_one : 1 ≤ CΔ := by
    have h1 : 1 ≤ K_loss := hK_loss_one
    have h2 : 1 ≤ C₂_max := hC₂_max_one
    dsimp only [CΔ]
    nlinarith

  have h_sset_trimmed : ∀ Q ∈ QSet',
      IsFiniteTubeSSet s CΔ (trimmedFamily Q) := by
    intro Q hQ
    let F := coarseTubes_Q Q
    let F' := trimmedFamily Q
    have hF'_sub : F' ⊆ F := h_trimmed_sub Q hQ
    have h_card_eq : F'.card = MΔ_new := h_trimmed_card Q hQ
    have hF'_nonempty : F'.Nonempty := by
      have h_pos : 0 < F'.card := by
        rw [h_card_eq] <;> exact hMΔ_new_pos
      exact Finset.card_pos.mp h_pos
    have h_card_F : (F.card : ℝ) < 2 * (MΔ_orig : ℝ) := by
      exact_mod_cast h_size_upper Q (hQSet'_sub hQ)
    have h_ret : (MΔ_orig : ℝ) ≤ K_loss * (MΔ_new : ℝ) := h_retention Q hQ
    have hK : (F.card : ℝ) ≤ (2 * K_loss) * (F'.card : ℝ) := by
      have h1 : (F.card : ℝ) < 2 * (MΔ_orig : ℝ) := h_card_F
      have h2 : (F.card : ℝ) ≤ 2 * (K_loss * (MΔ_new : ℝ)) := by linarith
      have h3 : (F'.card : ℝ) = (MΔ_new : ℝ) := by exact_mod_cast h_card_eq
      rw [h3] at *
      <;> linarith
    have h_orig_sset : IsFiniteTubeSSet s (C₂_Q Q) F := h_sset_Q Q (hQSet'_sub hQ)
    have h_result : IsFiniteTubeSSet s ((C₂_Q Q) * (2 * K_loss)) F' :=
      IsFiniteTubeSSet.subset_with_loss h_orig_sset hF'_sub hF'_nonempty hK
    have hKpos : 0 ≤ 2 * K_loss := by positivity
    have h_le : (C₂_Q Q) * (2 * K_loss) ≤ CΔ := by
      dsimp only [CΔ]
      have h : (C₂_Q Q) * (2 * K_loss) ≤ C₂_max * (2 * K_loss) := by
        exact mul_le_mul_of_nonneg_right (hC₂_max Q (hQSet'_sub hQ)) hKpos
      linarith
    exact IsFiniteTubeSSet.scale_C h_result h_le

  let tubes : Finset (DyadicTube m) := QSet'.biUnion trimmedFamily
  let tubeFamily (Q : DyadicSquare m) (hQ : Q ∈ QSet') : Finset (DyadicTube m) :=
    trimmedFamily Q

  have h_subset : ∀ Q hQ, tubeFamily Q hQ ⊆ tubes := by
    intro Q hQ
    exact Finset.subset_biUnion_of_mem trimmedFamily hQ

  have h_size : ∀ Q hQ, (tubeFamily Q hQ).card = MΔ_new := by
    intro Q hQ
    exact h_trimmed_card Q hQ

  have h_incidence' : ∀ Q hQ U, U ∈ tubeFamily Q hQ →
      (U.toSet ∩ Q.toSet).Nonempty := by
    intro Q hQ U hU
    exact h_incidence Q (hQSet'_sub hQ) U (h_trimmed_sub Q hQ hU)

  have h_bounded' : ∀ Q ∈ QSet', Q.toSet ⊆ unitSquare := by
    intro Q hQ
    exact h_bounded Q (hQSet'_sub hQ)

  have h_strip' : ∀ U ∈ tubes, U.IsInAllowedParameterStrip := by
    intro U hU
    rcases Finset.mem_biUnion.mp hU with ⟨Q, hQ, hU'⟩
    exact h_strip Q (hQSet'_sub hQ) U (h_trimmed_sub Q hQ hU')

  let coarseConfig : NiceConfiguration m s CΔ MΔ_new :=
    niceConfigBuilder QSet' tubes tubeFamily h_subset h_size h_sset_trimmed
      h_incidence' h_bounded' h_strip'

  have h_points : coarseConfig.points = QSet' := by rfl
  have h_tubes : coarseConfig.tubes = tubes := by rfl

  have hQSet'_nonempty : QSet'.Nonempty := by
    by_contra h
    have h_empty : QSet' = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using h
    have h_cont : (QSet.card : ℝ) ≤ 0 := by
      rw [h_empty] at hQSet'_cover
      simpa using hQSet'_cover
    have hQpos : 0 < (QSet.card : ℝ) := by exact_mod_cast hQSet_nonempty.card_pos
    linarith
  rcases hQSet'_nonempty with ⟨Q0, hQ0⟩
  have h_retention_bound : (MΔ_orig : ℝ) ≤ K_loss * (MΔ_new : ℝ) :=
    h_retention Q0 hQ0

  refine ⟨QSet', MΔ_new, trimmedFamily, CΔ, coarseConfig, NΔ, K_loss,
    hK_loss_one, hQSet'_sub, hQSet'_cover, hMΔ_new_pos, h_retention_bound,
    by dsimp only [CΔ] <;> ring,
    h_trimmed_card, h_trimmed_sub,
    (fun Q hQ U hU => h_fiber_band Q hQ U hU),
    h_points, h_tubes, ?_, ?_, ?_, ?_, hK_loss_eq⟩
  · intro Q hQ
    dsimp only [coarseConfig]
    <;> rfl
  · intro Q hQ U hU
    exact h_incidence Q (hQSet'_sub hQ) U (h_trimmed_sub Q hQ hU)
  · intro Q hQ U hU
    exact h_strip Q (hQSet'_sub hQ) U (h_trimmed_sub Q hQ hU)
  · exact h_bounded'

end InductionOnScales
