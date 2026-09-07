module

public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.UniformFibers
public import MyLeanRepo.InductionOnScales.Pigeonhole
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Fiber-Aware Trimming

Selects per-Q coarse tube families with uniform geometric fiber sizes.

For each Q, `select_uniform_fibers` gives [NΔ_Q, 2·NΔ_Q). Then pigeonhole
on NΔ_Q values finds a sub-band [B, 2B) shared by many Qs, yielding fibers
in [B, 4B). Each family is trimmed to uniform size MΔ'.

Total loss K_loss = 2·numBands² = O(log² |fineTubes|).
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace InductionOnScales

lemma fiber_aware_trimming
    {n m : ℕ} (hnm : m ≤ n)
    {Q : Type*} [DecidableEq Q]
    (QSet : Finset Q)
    (coarseTubes_Q : Q → Finset (DyadicTube m))
    (MΔ : ℕ) (hMΔ_pos : 0 < MΔ)
    (h_size : ∀ q ∈ QSet, MΔ ≤ (coarseTubes_Q q).card)
    (fineTubes : Finset (DyadicTube n))
    (h_fine_pos : 0 < fineTubes.card)
    (h_fiber_pos : ∀ q ∈ QSet, ∀ U ∈ coarseTubes_Q q,
      0 < fiberSize hnm fineTubes U) :
    ∃ (NΔ : ℕ) (QSet' : Finset Q)
      (trimmed_Q : Q → Finset (DyadicTube m))
      (MΔ' : ℕ) (K_loss : ℝ),
      1 ≤ K_loss ∧
      QSet' ⊆ QSet ∧
      (QSet.card : ℝ) ≤ K_loss * (QSet'.card : ℝ) ∧
      0 < MΔ' ∧
      (∀ q ∈ QSet', (trimmed_Q q).card = MΔ') ∧
      (∀ q ∈ QSet', trimmed_Q q ⊆ coarseTubes_Q q) ∧
      (∀ q ∈ QSet', ∀ U ∈ trimmed_Q q,
        NΔ ≤ fiberSize hnm fineTubes U ∧
        fiberSize hnm fineTubes U < 4 * NΔ) ∧
      (∀ q ∈ QSet', (MΔ : ℝ) ≤ K_loss * (MΔ' : ℝ)) ∧
      K_loss = 2 * (numDyadicLevels fineTubes.card : ℝ)^2 := by
  let numBands : ℕ := numDyadicLevels fineTubes.card
  have h_numBands_pos : 0 < numBands := by
    simp [numBands, numDyadicLevels] <;> omega
  have h_numBands_ge2 : 2 ≤ numBands := by
    simp [numBands, numDyadicLevels] <;> omega
  let fiberLoss : ℕ := 2 * numBands
  have h_fiberLoss_pos : 0 < fiberLoss := by positivity
  let K_loss : ℝ := 2 * (numBands : ℝ)^2
  have hK_loss_one : 1 ≤ K_loss := by
    dsimp only [K_loss]
    have h1 : 2 ≤ (numBands : ℝ) := by exact_mod_cast h_numBands_ge2
    nlinarith

  -- Per-Q fiber selection
  have h_choose : ∀ (q : Q), q ∈ QSet →
      ∃ (NΔ_q : ℕ) (S_q : Finset (DyadicTube m)),
        S_q ⊆ coarseTubes_Q q ∧
        S_q.Nonempty ∧
        (∀ U ∈ S_q, NΔ_q ≤ fiberSize hnm fineTubes U ∧
          fiberSize hnm fineTubes U < 2 * NΔ_q) ∧
        (coarseTubes_Q q).card ≤ fiberLoss * (S_q).card := by
    intro q hq
    have h1 : (coarseTubes_Q q).Nonempty := by
      have h2 : MΔ ≤ (coarseTubes_Q q).card := h_size q hq
      exact Finset.card_pos.mp (by omega)
    rcases select_uniform_fibers hnm fineTubes (coarseTubes_Q q) h1
        (h_fiber_pos q hq) with ⟨NΔ_q, S_q, h_sub, h_nonempty, h_lower, h_upper, h_card⟩
    have h_card' : (coarseTubes_Q q).card ≤ fiberLoss * (S_q).card := by
      exact_mod_cast h_card
    exact ⟨NΔ_q, S_q, h_sub, h_nonempty,
      (fun U hU => ⟨h_lower U hU, h_upper U hU⟩), h_card'⟩

  classical
  choose NΔ_q S_q hS_sub hS_nonempty hS_band hS_card using h_choose

  let NΔ_total (q : Q) : ℕ :=
    if hq : q ∈ QSet then NΔ_q q hq else 1

  have hNΔ_pos : ∀ q ∈ QSet, 0 < NΔ_total q := by
    intro q hq
    have h_eq : NΔ_total q = NΔ_q q hq := by simp [NΔ_total, hq]
    rw [h_eq]
    rcases hS_nonempty q hq with ⟨U, hU⟩
    have h2 : fiberSize hnm fineTubes U < 2 * NΔ_q q hq :=
      (hS_band q hq U hU).2
    have h3 : 0 < fiberSize hnm fineTubes U :=
      h_fiber_pos q hq U (hS_sub q hq hU)
    have h4 : 0 < 2 * NΔ_q q hq := by linarith
    omega

  have hNΔ_bound : ∀ q ∈ QSet, NΔ_total q ≤ fineTubes.card := by
    intro q hq
    have h_eq : NΔ_total q = NΔ_q q hq := by simp [NΔ_total, hq]
    rw [h_eq]
    rcases hS_nonempty q hq with ⟨U, hU⟩
    have h2 : NΔ_q q hq ≤ fiberSize hnm fineTubes U := (hS_band q hq U hU).1
    have h3 : fiberSize hnm fineTubes U ≤ fineTubes.card := by
      simpa [fiberSize] using Finset.card_filter_le fineTubes _
    exact le_trans h2 h3

  by_cases hQSet_empty : QSet = ∅
  · subst hQSet_empty
    have hK_loss_eq : K_loss = 2 * (numDyadicLevels fineTubes.card : ℝ)^2 := by
      rfl
    exact ⟨1, ∅, fun _ => ∅, 1, K_loss, hK_loss_one, by simp, by simp, by norm_num,
      by simp, by simp, by simp, by simp, hK_loss_eq⟩

  have hQSet_nonempty : QSet.Nonempty := by
    simpa [Finset.nonempty_iff_ne_empty] using hQSet_empty

  rcases exists_dyadic_size_subfamily QSet NΔ_total h_fine_pos hNΔ_bound hNΔ_pos
    with ⟨B, QSet'_raw, hQSet'_sub, h_band, hQSet'_card⟩

  -- Common retention bound lemma: MΔ ≤ K_loss * MΔ' where MΔ' = max 1 (MΔ / fiberLoss)
  have h_retention_bound : (MΔ : ℝ) ≤ K_loss * (max 1 (MΔ / fiberLoss) : ℕ) := by
    dsimp only [K_loss]
    by_cases h2 : MΔ < fiberLoss
    · have h3 : MΔ / fiberLoss = 0 := Nat.div_eq_of_lt h2
      have h4 : (max 1 (MΔ / fiberLoss) : ℕ) = 1 := by
        rw [h3] <;> simp
      rw [h4]
      have h5 : (MΔ : ℝ) < (fiberLoss : ℝ) := by exact_mod_cast h2
      have h5' : (MΔ : ℝ) < 2 * (numBands : ℝ) := by
        simpa [fiberLoss] using h5
      have h8 : 2 * (numBands : ℝ) ≤ 2 * (numBands : ℝ)^2 := by
        have h9 : 1 ≤ (numBands : ℝ) := by exact_mod_cast h_numBands_pos
        have h10 : 0 ≤ (numBands : ℝ) := by exact_mod_cast Nat.zero_le numBands
        have h11 : (numBands : ℝ) ≤ (numBands : ℝ)^2 := by
          calc
            (numBands : ℝ) = (numBands : ℝ) * 1 := by ring
            _ ≤ (numBands : ℝ) * (numBands : ℝ) := by gcongr <;> linarith
            _ = (numBands : ℝ)^2 := by ring
        nlinarith
      have h13 : (MΔ : ℝ) ≤ 2 * (numBands : ℝ)^2 := by
        have h14 : (MΔ : ℝ) < 2 * (numBands : ℝ) := h5'
        linarith [h8]
      simpa using h13
    · have h3 : fiberLoss ≤ MΔ := by omega
      have h4 : 1 ≤ MΔ / fiberLoss := by
        apply Nat.one_le_div_iff (by omega) |>.mpr
        exact h3
      have h5 : (max 1 (MΔ / fiberLoss) : ℕ) = MΔ / fiberLoss := by
        rw [max_eq_right h4]
      rw [h5]
      set q : ℕ := MΔ / fiberLoss with hq_def
      have hq_ge1 : 1 ≤ q := h4
      have h6 : (MΔ : ℝ) < (fiberLoss : ℝ) * (q : ℝ) + (fiberLoss : ℝ) := by
        have h7 : MΔ = fiberLoss * q + MΔ % fiberLoss := by
          exact (Nat.div_add_mod MΔ fiberLoss).symm
        have h8 : MΔ % fiberLoss < fiberLoss := Nat.mod_lt MΔ h_fiberLoss_pos
        exact_mod_cast (by linarith)
      have h_fl : (fiberLoss : ℝ) = 2 * (numBands : ℝ) := by
        simp [fiberLoss] <;> ring
      have h9 : (fiberLoss : ℝ) * (q : ℝ) + (fiberLoss : ℝ) ≤
          2 * (numBands : ℝ)^2 * (q : ℝ) := by
        rw [h_fl]
        have h10 : 2 ≤ (numBands : ℝ) := by exact_mod_cast h_numBands_ge2
        have h11 : 1 ≤ (q : ℝ) := by exact_mod_cast hq_ge1
        have h12 : 0 ≤ (numBands : ℝ) := by exact_mod_cast Nat.zero_le numBands
        have h13 : 0 ≤ (q : ℝ) := by exact_mod_cast Nat.zero_le q
        have h14 : (q : ℝ) + 1 ≤ (numBands : ℝ) * (q : ℝ) := by
          calc
            (q : ℝ) + 1 ≤ 2 * (q : ℝ) := by linarith
            _ ≤ (numBands : ℝ) * (q : ℝ) := by
              exact mul_le_mul_of_nonneg_right h10 h13
        have h15 : 2 * (numBands : ℝ) * ((q : ℝ) + 1) ≤
            2 * (numBands : ℝ) * ((numBands : ℝ) * (q : ℝ)) := by
          exact mul_le_mul_of_nonneg_left h14 (by linarith)
        have h16 : 2 * (numBands : ℝ) * ((q : ℝ) + 1) =
            2 * (numBands : ℝ) * (q : ℝ) + 2 * (numBands : ℝ) := by ring
        have h17 : 2 * (numBands : ℝ) * ((numBands : ℝ) * (q : ℝ)) =
            2 * (numBands : ℝ)^2 * (q : ℝ) := by ring
        rw [h16, h17] at h15
        exact h15
      linarith

  by_cases hQSet'_empty : QSet'_raw = ∅
  · -- QSet.card < numBands: pick any single q0 ∈ QSet
    let q0 : Q := Classical.choose hQSet_nonempty
    have hq0 : q0 ∈ QSet := Classical.choose_spec hQSet_nonempty
    let QSet' : Finset Q := {q0}
    let NΔ : ℕ := NΔ_q q0 hq0
    let MΔ' : ℕ := max 1 (MΔ / fiberLoss)

    have hS_ge_q0 : MΔ' ≤ (S_q q0 hq0).card := by
      dsimp only [MΔ']
      have h1 : (coarseTubes_Q q0).card ≤ fiberLoss * (S_q q0 hq0).card :=
        hS_card q0 hq0
      have h2 : MΔ ≤ (coarseTubes_Q q0).card := h_size q0 hq0
      have h3 : MΔ ≤ fiberLoss * (S_q q0 hq0).card := le_trans h2 h1
      by_cases h4 : MΔ < fiberLoss
      · have h5 : MΔ / fiberLoss = 0 := Nat.div_eq_of_lt h4
        have h6 : (max 1 (MΔ / fiberLoss) : ℕ) = 1 := by
          rw [h5] <;> simp
        rw [h6]
        exact (hS_nonempty q0 hq0).card_pos
      · have h6 : fiberLoss ≤ MΔ := by omega
        have h7 : 1 ≤ MΔ / fiberLoss := by
          apply Nat.one_le_div_iff (by omega) |>.mpr
          exact h6
        have h8 : (max 1 (MΔ / fiberLoss) : ℕ) = MΔ / fiberLoss := by
          rw [max_eq_right h7]
        rw [h8]
        exact Nat.div_le_of_le_mul h3

    let h_exists_q0 : ∃ (T : Finset (DyadicTube m)),
        T ⊆ S_q q0 hq0 ∧ T.card = MΔ' :=
      Finset.exists_subset_card_eq hS_ge_q0
    let trimmed_Q0 : Finset (DyadicTube m) := h_exists_q0.choose
    have htrim_sub0 : trimmed_Q0 ⊆ S_q q0 hq0 :=
      h_exists_q0.choose_spec.1
    have htrim_card0 : trimmed_Q0.card = MΔ' :=
      h_exists_q0.choose_spec.2

    let trimmed_Q (q : Q) : Finset (DyadicTube m) :=
      if hq : q = q0 then trimmed_Q0 else ∅

    have h_coverage : (QSet.card : ℝ) ≤ K_loss * (QSet'.card : ℝ) := by
      have h1 : QSet.card < numBands := by
        have h2 : QSet'_raw.card ≥ QSet.card / numBands := hQSet'_card
        rw [hQSet'_empty] at h2
        have h3 : QSet.card / numBands = 0 := by simpa using h2
        by_contra h4
        have h5 : numBands ≤ QSet.card := by omega
        have h6 : 0 < QSet.card / numBands := Nat.div_pos h5 h_numBands_pos
        rw [h3] at h6
        <;> omega
      have h4 : QSet'.card = 1 := by simp [QSet']
      rw [h4]
      dsimp only [K_loss]
      have h5 : (QSet.card : ℝ) < (numBands : ℝ) := by exact_mod_cast h1
      have h6 : 2 ≤ (numBands : ℝ) := by exact_mod_cast h_numBands_ge2
      have h7 : (QSet.card : ℝ) ≤ 2 * (numBands : ℝ)^2 := by
        have h8 : (numBands : ℝ) ≤ 2 * (numBands : ℝ)^2 := by
          have h9 : 1 ≤ (numBands : ℝ) := by exact_mod_cast h_numBands_pos
          nlinarith
        linarith
      simpa using h7

    have h_fiber_band : ∀ q ∈ QSet', ∀ U ∈ trimmed_Q q,
        NΔ ≤ fiberSize hnm fineTubes U ∧ fiberSize hnm fineTubes U < 4 * NΔ := by
      intro q hq U hU
      have hq_eq : q = q0 := by simpa [QSet'] using hq
      subst hq_eq
      have h_eq : trimmed_Q q0 = trimmed_Q0 := by simp [trimmed_Q]
      rw [h_eq] at hU
      have hU_in : U ∈ S_q q0 hq0 := htrim_sub0 hU
      have h1 := hS_band q0 hq0 U hU_in
      have h_pos : 0 < NΔ := by
        have h9 : 0 < NΔ_total q0 := hNΔ_pos q0 hq0
        simpa [NΔ_total, hq0] using h9
      exact ⟨h1.1, by linarith⟩

    have h_retention : ∀ q ∈ QSet', (MΔ : ℝ) ≤ K_loss * (MΔ' : ℝ) := by
      intro q _
      exact h_retention_bound

    have hQSet'_sub' : QSet' ⊆ QSet := by
      simp [QSet', hq0] <;> tauto

    have hK_loss_eq : K_loss = 2 * (numDyadicLevels fineTubes.card : ℝ)^2 := by rfl
    exact ⟨NΔ, QSet', trimmed_Q, MΔ', K_loss, hK_loss_one,
      hQSet'_sub', h_coverage, by
        dsimp only [MΔ'] <;> omega,
      (fun q hq => by
        have hq_eq : q = q0 := by simpa [QSet'] using hq
        subst hq_eq
        have h : trimmed_Q q0 = trimmed_Q0 := by simp [trimmed_Q]
        rw [h] <;> exact htrim_card0),
      (fun q hq => by
        have hq_eq : q = q0 := by simpa [QSet'] using hq
        subst hq_eq
        have h : trimmed_Q q0 = trimmed_Q0 := by simp [trimmed_Q]
        rw [h]
        exact Finset.Subset.trans htrim_sub0 (hS_sub q0 hq0)),
      h_fiber_band, h_retention, hK_loss_eq⟩

  · -- Main case: QSet'_raw nonempty
    let QSet' := QSet'_raw
    have hQSet'_nonempty : QSet'.Nonempty := by
      simpa [QSet', Finset.nonempty_iff_ne_empty] using hQSet'_empty
    have hQSet'_card_pos : 0 < QSet'.card := hQSet'_nonempty.card_pos

    let NΔ : ℕ := B
    let MΔ' : ℕ := max 1 (MΔ / fiberLoss)

    have hMΔ'_pos : 0 < MΔ' := by
      dsimp only [MΔ'] <;> omega

    have h_coverage : (QSet.card : ℝ) ≤ K_loss * (QSet'.card : ℝ) := by
      have h1 : QSet.card / numBands ≤ QSet'.card := hQSet'_card
      have h2 : QSet.card = numBands * (QSet.card / numBands) + QSet.card % numBands :=
        (Nat.div_add_mod QSet.card numBands).symm
      have h3 : QSet.card % numBands < numBands := Nat.mod_lt _ h_numBands_pos
      have h4 : QSet.card ≤ numBands * QSet'.card + (numBands - 1) := by
        calc
          QSet.card
            = numBands * (QSet.card / numBands) + QSet.card % numBands := h2
          _ ≤ numBands * QSet'.card + QSet.card % numBands := by
            gcongr
            <;> exact h1
          _ ≤ numBands * QSet'.card + (numBands - 1) := by
            have h41 : QSet.card % numBands ≤ numBands - 1 := by omega
            omega
      have h5 : numBands - 1 ≤ numBands * QSet'.card := by
        have h6 : numBands - 1 ≤ numBands := by omega
        have h7 : numBands ≤ numBands * QSet'.card := by
          apply Nat.le_mul_of_pos_right
          exact hQSet'_card_pos
        exact le_trans h6 h7
      have h8 : QSet.card ≤ 2 * numBands * QSet'.card := by
        calc
          QSet.card ≤ numBands * QSet'.card + (numBands - 1) := h4
          _ ≤ numBands * QSet'.card + numBands * QSet'.card := by gcongr
          _ = 2 * numBands * QSet'.card := by ring
      have h9 : (QSet.card : ℝ) ≤ 2 * (numBands : ℝ) * (QSet'.card : ℝ) := by
        exact_mod_cast h8
      dsimp only [K_loss]
      have h10 : 2 * (numBands : ℝ) * (QSet'.card : ℝ) ≤
          2 * (numBands : ℝ)^2 * (QSet'.card : ℝ) := by
        have h11 : 1 ≤ (numBands : ℝ) := by exact_mod_cast h_numBands_pos
        have h12 : 0 ≤ (numBands : ℝ) := by exact_mod_cast Nat.zero_le numBands
        have h13 : (numBands : ℝ) ≤ (numBands : ℝ)^2 := by
          calc
            (numBands : ℝ) = (numBands : ℝ) * 1 := by ring
            _ ≤ (numBands : ℝ) * (numBands : ℝ) := by gcongr <;> linarith
            _ = (numBands : ℝ)^2 := by ring
        have h14 : 0 ≤ (QSet'.card : ℝ) := by exact_mod_cast Nat.zero_le QSet'.card
        have h15 : (numBands : ℝ) * (QSet'.card : ℝ) ≤
            (numBands : ℝ)^2 * (QSet'.card : ℝ) := by
          exact mul_le_mul_of_nonneg_right h13 h14
        have h16 : 2 * ((numBands : ℝ) * (QSet'.card : ℝ)) ≤
            2 * ((numBands : ℝ)^2 * (QSet'.card : ℝ)) := by
          exact mul_le_mul_of_nonneg_left h15 (by norm_num)
        simpa [mul_assoc] using h16
      exact le_trans h9 h10

    have hS_ge : ∀ (q : Q) (hq : q ∈ QSet'), MΔ' ≤ (S_q q (hQSet'_sub hq)).card := by
      intro q hq
      have hq' : q ∈ QSet := hQSet'_sub hq
      have h1 : (coarseTubes_Q q).card ≤ fiberLoss * (S_q q hq').card := hS_card q hq'
      have h2 : MΔ ≤ (coarseTubes_Q q).card := h_size q hq'
      have h3 : MΔ ≤ fiberLoss * (S_q q hq').card := le_trans h2 h1
      dsimp only [MΔ']
      by_cases h4 : MΔ < fiberLoss
      · have h5 : MΔ / fiberLoss = 0 := Nat.div_eq_of_lt h4
        have h6 : (max 1 (MΔ / fiberLoss) : ℕ) = 1 := by
          rw [h5] <;> simp
        rw [h6]
        exact (hS_nonempty q hq').card_pos
      · have h6 : fiberLoss ≤ MΔ := by omega
        have h7 : 1 ≤ MΔ / fiberLoss := by
          apply Nat.one_le_div_iff (by omega) |>.mpr
          exact h6
        have h8 : (max 1 (MΔ / fiberLoss) : ℕ) = MΔ / fiberLoss := by
          rw [max_eq_right h7]
        rw [h8]
        exact Nat.div_le_of_le_mul h3

    have h_trim : ∀ (q : Q) (hq : q ∈ QSet'),
        ∃ (T_q : Finset (DyadicTube m)),
          T_q ⊆ S_q q (hQSet'_sub hq) ∧ T_q.card = MΔ' := by
      intro q hq
      exact Finset.exists_subset_card_eq (hS_ge q hq)

    choose trimmed_Q_raw htrim_sub htrim_card using h_trim

    let trimmed_Q (q : Q) : Finset (DyadicTube m) :=
      if hq : q ∈ QSet' then trimmed_Q_raw q hq else ∅

    have h_trimmed_card : ∀ q ∈ QSet', (trimmed_Q q).card = MΔ' := by
      intro q hq
      have h_eq : trimmed_Q q = trimmed_Q_raw q hq := by simp [trimmed_Q, hq]
      rw [h_eq]; exact htrim_card q hq

    have h_trimmed_sub : ∀ q ∈ QSet', trimmed_Q q ⊆ coarseTubes_Q q := by
      intro q hq
      have h_eq : trimmed_Q q = trimmed_Q_raw q hq := by simp [trimmed_Q, hq]
      rw [h_eq]
      exact Finset.Subset.trans (htrim_sub q hq) (hS_sub q (hQSet'_sub hq))

    have h_fiber_band : ∀ q ∈ QSet', ∀ U ∈ trimmed_Q q,
        NΔ ≤ fiberSize hnm fineTubes U ∧ fiberSize hnm fineTubes U < 4 * NΔ := by
      intro q hq U hU
      have hq' : q ∈ QSet := hQSet'_sub hq
      have h_eq : trimmed_Q q = trimmed_Q_raw q hq := by simp [trimmed_Q, hq]
      rw [h_eq] at hU
      have hU_in_S : U ∈ S_q q hq' := htrim_sub q hq hU
      have hNΔ_eq : NΔ_total q = NΔ_q q hq' := by simp [NΔ_total, hq']
      have h_band1 : B ≤ NΔ_total q := (h_band q hq).1
      have h_band2 : NΔ_total q < 2 * B := (h_band q hq).2
      have h1 : NΔ_q q hq' ≤ fiberSize hnm fineTubes U :=
        (hS_band q hq' U hU_in_S).1
      have h2 : fiberSize hnm fineTubes U < 2 * NΔ_q q hq' :=
        (hS_band q hq' U hU_in_S).2
      have h3 : B ≤ NΔ_q q hq' := by rw [←hNΔ_eq]; exact h_band1
      have h4 : NΔ_q q hq' < 2 * B := by rw [←hNΔ_eq]; exact h_band2
      exact ⟨by linarith, by linarith⟩

    have h_retention : ∀ q ∈ QSet', (MΔ : ℝ) ≤ K_loss * (MΔ' : ℝ) := by
      intro q _
      exact h_retention_bound

    have hK_loss_eq : K_loss = 2 * (numDyadicLevels fineTubes.card : ℝ)^2 := by rfl
    exact ⟨NΔ, QSet', trimmed_Q, MΔ', K_loss, hK_loss_one,
      hQSet'_sub, h_coverage, hMΔ'_pos, h_trimmed_card, h_trimmed_sub,
      h_fiber_band, h_retention, hK_loss_eq⟩

end InductionOnScales
