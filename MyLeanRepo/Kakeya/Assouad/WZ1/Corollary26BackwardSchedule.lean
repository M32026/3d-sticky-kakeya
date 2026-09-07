import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26RepairedStatements

namespace Kakeya.Assouad

/-!
# Backward-recursive loss schedule for WZ1 Corollary 26 anchored hierarchy

This module constructs a backward-recursive loss schedule from the two
WZ1 locally-linear producer hypotheses.

## Design

The terminal level (reversed index 0) uses `WZ1LocallyLinearTerminalScaleConclusion`
with `e = hierarchyLoss`.  Each intermediate level (reversed index i+1) uses
`WZ1LocallyLinearOneScaleConclusion` with
`e = min(prev.c, min(hierarchyLoss, 1/(2*N)))`.

The reversed index maps to forward level `j` via `i = N - 1 - j`.
-/

private abbrev TerminalProducerFn (sigma outputLoss c d : ℝ) : Prop :=
  ∀ (inputLoss : ℝ), 0 < inputLoss → inputLoss ≤ c →
    ∀ (delta : ℝ), 0 < delta → delta ≤ d →
      ∀ (source : WZ1PlaninessGraininessPackage sigma inputLoss delta),
        ∀ (rho : Kakeya.Streamlined.AdmissibleScale delta),
          (rho : ℝ) = delta →
          Nonempty (WZ1LocallyLinearOneScaleData source outputLoss rho)

private abbrev IntermediateProducerFn (sigma e c d : ℝ) : Prop :=
  ∀ (inputLoss : ℝ), 0 < inputLoss → inputLoss ≤ c →
    ∀ (delta : ℝ), 0 < delta → delta ≤ d →
      ∀ (source : WZ1PlaninessGraininessPackage sigma inputLoss delta),
        ∀ (rho : Kakeya.Streamlined.AdmissibleScale delta),
          Real.rpow delta (1 - e) ≤ (rho : ℝ) →
          (rho : ℝ) ≤ Real.rpow delta e →
          Nonempty (WZ1LocallyLinearOneScaleData source e rho)

private def finLast (N : ℕ) (h : 2 ≤ N) : Fin N := by
  refine ⟨N - 1, ?_⟩
  have h₁ : 0 < N := by linarith
  omega

/-- A complete backward-recursive loss schedule for N hierarchy levels. -/
structure BackwardScheduleData (N : ℕ) (sigma hierarchyLoss : ℝ) where
  hN_two : 2 ≤ N
  e : Fin N → ℝ
  c : Fin N → ℝ
  d : Fin N → ℝ
  produce_intermediate : ∀ (j : Fin N) (hj : (j : ℕ) + 1 < N),
    IntermediateProducerFn sigma (e j) (c j) (d j)
  targetLoss : ℝ
  targetLoss_pos : 0 < targetLoss
  targetLoss_le_hierarchyLoss : targetLoss ≤ hierarchyLoss
  produce_terminal : TerminalProducerFn sigma targetLoss
    (c (finLast N hN_two)) (d (finLast N hN_two))
  e_pos : ∀ (j : Fin N), 0 < e j
  c_pos : ∀ (j : Fin N), 0 < c j
  d_pos : ∀ (j : Fin N), 0 < d j
  d_le_one : ∀ (j : Fin N), d j ≤ 1
  c_le_e_div_100 : ∀ (j : Fin N), c j ≤ e j / 100
  e_last : e (finLast N hN_two) = targetLoss
  e_le_c_next : ∀ (j : Fin N) (hj : (j : ℕ) + 1 < N), e j ≤ c ⟨(j : ℕ) + 1, hj⟩
  e_le_targetLoss : ∀ (j : Fin N), e j ≤ targetLoss
  e_le_half_N : ∀ (j : Fin N) (hj : (j : ℕ) + 1 < N), e j ≤ 1 / (2 * (N : ℝ))

namespace BackwardScheduleData

variable {N : ℕ} {sigma hierarchyLoss : ℝ} (s : BackwardScheduleData N sigma hierarchyLoss)

private def finZero (N : ℕ) (h : 2 ≤ N) : Fin N := by
  refine ⟨0, ?_⟩; linarith

/-- The source loss ceiling at the coarsest level (level 0). -/
def sourceCeiling : ℝ := s.c (finZero N s.hN_two)

lemma sourceCeiling_pos : 0 < s.sourceCeiling := s.c_pos _

lemma sourceCeiling_le_hierarchyLoss_div_100 :
    s.sourceCeiling ≤ hierarchyLoss / 100 := by
  have h1 : s.sourceCeiling ≤ s.e (finZero N s.hN_two) / 100 := s.c_le_e_div_100 (finZero N s.hN_two)
  have h2 : s.e (finZero N s.hN_two) ≤ s.targetLoss := s.e_le_targetLoss (finZero N s.hN_two)
  have h3 : s.e (finZero N s.hN_two) / 100 ≤ s.targetLoss / 100 := by gcongr
  have h4 : s.targetLoss / 100 ≤ hierarchyLoss / 100 := by
    gcongr; exact s.targetLoss_le_hierarchyLoss
  exact le_trans h1 (le_trans h3 h4)

/-- Uniform delta threshold: minimum of all per-level thresholds. -/
noncomputable def d_min : ℝ :=
  let im : Finset ℝ := Finset.image s.d (Finset.univ : Finset (Fin N))
  have h_nonempty : im.Nonempty := by
    let j0 : Fin N := finZero N s.hN_two
    exact ⟨s.d j0, Finset.mem_image.mpr ⟨j0, Finset.mem_univ _, rfl⟩⟩
  Finset.min' im h_nonempty

lemma d_min_pos : 0 < s.d_min := by
  let im : Finset ℝ := Finset.image s.d (Finset.univ : Finset (Fin N))
  have h_nonempty : im.Nonempty := by
    let j0 : Fin N := finZero N s.hN_two
    exact ⟨s.d j0, Finset.mem_image.mpr ⟨j0, Finset.mem_univ _, rfl⟩⟩
  have h_mem : Finset.min' im h_nonempty ∈ im := Finset.min'_mem im h_nonempty
  have h_all_pos : ∀ x ∈ im, 0 < x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
    exact s.d_pos j
  exact h_all_pos _ h_mem

lemma d_min_le_d (j : Fin N) : s.d_min ≤ s.d j := by
  let im : Finset ℝ := Finset.image s.d (Finset.univ : Finset (Fin N))
  have h_nonempty : im.Nonempty := by
    let j0 : Fin N := finZero N s.hN_two
    exact ⟨s.d j0, Finset.mem_image.mpr ⟨j0, Finset.mem_univ _, rfl⟩⟩
  have h : s.d j ∈ im := by
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  exact Finset.min'_le im (s.d j) h

/-- Window lower bound: `delta^(1-e_j) ≤ delta^((j+1)/N)` for `0 < delta < 1`. -/
lemma window_lower (j : Fin N) (hj : (j : ℕ) + 1 < N)
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) :
    Real.rpow delta (1 - s.e j) ≤ Real.rpow delta (((j : ℝ) + 1) / (N : ℝ)) := by
  have hN_pos' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N from by omega)
  have h1 : s.e j ≤ 1 / (2 * (N : ℝ)) := s.e_le_half_N j hj
  have h_half_le : 1 / (2 * (N : ℝ)) ≤ 1 / (N : ℝ) := by
    apply one_div_le_one_div_of_le
    · positivity
    · linarith
  have h_e_le : s.e j ≤ 1 / (N : ℝ) := h1.trans h_half_le
  have h_j_nat2 : (j : ℕ) + 2 ≤ N := by omega
  have h_j_real2 : ((j : ℝ) + 2) ≤ (N : ℝ) := by exact_mod_cast h_j_nat2
  have h_num : ((j : ℝ) + 1) ≤ (N : ℝ) - 1 := by linarith
  have h2 : ((j : ℝ) + 1) / (N : ℝ) ≤ 1 - 1 / (N : ℝ) := by
    have h2a : ((j : ℝ) + 1) / (N : ℝ) ≤ ((N : ℝ) - 1) / (N : ℝ) := by
      apply div_le_div_of_nonneg_right h_num
      positivity
    have h2b : ((N : ℝ) - 1) / (N : ℝ) = 1 - 1 / (N : ℝ) := by
      field_simp [hN_pos'.ne']
    rw [h2b] at h2a
    exact h2a
  have h3 : 1 - 1 / (N : ℝ) ≤ 1 - s.e j := by linarith
  have h4 : ((j : ℝ) + 1) / (N : ℝ) ≤ 1 - s.e j := h2.trans h3
  exact Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_lt_one.le h4

/-- Window upper bound: `delta^((j+1)/N) ≤ delta^(e_j)` for `0 < delta < 1`. -/
lemma window_upper (j : Fin N) (hj : (j : ℕ) + 1 < N)
    {delta : ℝ} (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) :
    Real.rpow delta (((j : ℝ) + 1) / (N : ℝ)) ≤ Real.rpow delta (s.e j) := by
  have hN_pos' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N from by omega)
  have h1 : s.e j ≤ 1 / (2 * (N : ℝ)) := s.e_le_half_N j hj
  have h_half_le : 1 / (2 * (N : ℝ)) ≤ 1 / (N : ℝ) := by
    apply one_div_le_one_div_of_le
    · positivity
    · linarith
  have h_e_le : s.e j ≤ 1 / (N : ℝ) := h1.trans h_half_le
  have h_j_nat : 1 ≤ (j : ℕ) + 1 := by omega
  have h_j_real : (1 : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast h_j_nat
  have h2 : 1 / (N : ℝ) ≤ ((j : ℝ) + 1) / (N : ℝ) := by
    apply div_le_div_of_nonneg_right h_j_real
    positivity
  have h3 : s.e j ≤ ((j : ℝ) + 1) / (N : ℝ) := h_e_le.trans h2
  exact Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_lt_one.le h3

end BackwardScheduleData

namespace BackwardSchedule

/-! ## Private induction infrastructure -/

private inductive ReversedLevel (N : ℕ) (sigma targetLoss : ℝ) where
  | terminal (c d : ℝ)
      (produce : TerminalProducerFn sigma targetLoss c d)
      (hc_pos : 0 < c) (hd_pos : 0 < d) (hd_one : d ≤ 1)
      (hc_le : c ≤ targetLoss / 100)
  | intermediate (e c d : ℝ)
      (produce : IntermediateProducerFn sigma e c d)
      (he_pos : 0 < e) (hc_pos : 0 < c) (hd_pos : 0 < d)
      (hd_one : d ≤ 1) (hc_le : c ≤ e / 100)
      (he_le_target : e ≤ targetLoss)
      (he_le_half : e ≤ 1 / (2 * (N : ℝ)))

private def ReversedLevel.e {N sigma targetLoss}
    (rl : ReversedLevel N sigma targetLoss) : ℝ :=
  match rl with
  | .terminal _ _ _ _ _ _ _ => targetLoss
  | .intermediate e _ _ _ _ _ _ _ _ _ _ => e

private def ReversedLevel.c {N sigma targetLoss}
    (rl : ReversedLevel N sigma targetLoss) : ℝ :=
  match rl with
  | .terminal c _ _ _ _ _ _ => c
  | .intermediate _ c _ _ _ _ _ _ _ _ _ => c

private def ReversedLevel.d {N sigma targetLoss}
    (rl : ReversedLevel N sigma targetLoss) : ℝ :=
  match rl with
  | .terminal _ d _ _ _ _ _ => d
  | .intermediate _ _ d _ _ _ _ _ _ _ _ => d

private def ReversedLevel.isIntermediate {N sigma targetLoss}
    (rl : ReversedLevel N sigma targetLoss) : Bool :=
  match rl with
  | .terminal _ _ _ _ _ _ _ => false
  | .intermediate _ _ _ _ _ _ _ _ _ _ _ => true

private theorem ReversedLevel.getIntermediateProduce
    {N sigma targetLoss} (rl : ReversedLevel N sigma targetLoss)
    (h : rl.isIntermediate = true) :
    IntermediateProducerFn sigma rl.e rl.c rl.d := by
  cases rl with
  | terminal _ _ _ _ _ _ _ => contradiction
  | intermediate _ _ _ produce _ _ _ _ _ _ _ => exact produce

private theorem ReversedLevel.getTerminalProduce
    {N sigma targetLoss} (rl : ReversedLevel N sigma targetLoss)
    (h : rl.isIntermediate = false) :
    TerminalProducerFn sigma targetLoss rl.c rl.d := by
  cases rl with
  | terminal _ _ produce _ _ _ _ => exact produce
  | intermediate _ _ _ _ _ _ _ _ _ _ _ => contradiction

private lemma ReversedLevel.terminal_e
    {N sigma targetLoss} (rl : ReversedLevel N sigma targetLoss)
    (h : rl.isIntermediate = false) : rl.e = targetLoss := by
  cases rl with
  | terminal _ _ _ _ _ _ _ => rfl
  | intermediate _ _ _ _ _ _ _ _ _ _ _ => contradiction

private def ReversedLevel.valid {N sigma targetLoss}
    (rl : ReversedLevel N sigma targetLoss) : Prop :=
  0 < rl.c ∧ 0 < rl.d ∧ rl.d ≤ 1 ∧ rl.c ≤ rl.e / 100 ∧ 0 < rl.e ∧ rl.e ≤ targetLoss

private noncomputable def buildAllLevels
    {N : ℕ} {sigma targetLoss : ℝ}
    (h_intermediate : WZ1LocallyLinearOneScaleConclusion)
    (h_terminal : WZ1LocallyLinearTerminalScaleConclusion)
    (hFloor : HasWZ1CriticalVolumeFloor sigma)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (htargetLoss : 0 < targetLoss) (hN_two : 2 ≤ N) :
    ℕ → {rl : ReversedLevel N sigma targetLoss // rl.valid}
  | 0 => by
      let h_exists := h_terminal sigma targetLoss hsigma hsigma1 htargetLoss hFloor
      let c := Classical.choose h_exists
      let h1 := Classical.choose_spec h_exists
      let d := Classical.choose h1
      let h2 := Classical.choose_spec h1
      let hc_pos := h2.1
      let hc_le := h2.2.1
      let hd_pos := h2.2.2.1
      let hd_one := h2.2.2.2.1
      let produce := h2.2.2.2.2
      let rl : ReversedLevel N sigma targetLoss :=
        ReversedLevel.terminal c d produce hc_pos hd_pos hd_one hc_le
      have h_valid : rl.valid := by
        simp [ReversedLevel.valid, ReversedLevel.c, ReversedLevel.d, ReversedLevel.e]
        ; exact ⟨hc_pos, hd_pos, hd_one, hc_le, htargetLoss, by linarith⟩
      exact ⟨rl, h_valid⟩
  | i + 1 => by
      let prev_with_proof := buildAllLevels h_intermediate h_terminal hFloor hsigma hsigma1 htargetLoss hN_two i
      let prev := prev_with_proof.1
      let hprev := prev_with_proof.2
      let prev_c : ℝ := prev.c
      have h_prev_c_pos : 0 < prev_c := hprev.1
      let e : ℝ := min prev_c (min targetLoss (1 / (2 * (N : ℝ))))
      have h_e_pos : 0 < e := by
        have h2 : 0 < targetLoss := htargetLoss
        have h3 : 0 < (1 / (2 * (N : ℝ)) : ℝ) := by positivity
        exact lt_min h_prev_c_pos (lt_min h2 h3)
      let h_exists := h_intermediate sigma e hsigma hsigma1 h_e_pos hFloor
      let c := Classical.choose h_exists
      let h1 := Classical.choose_spec h_exists
      let d := Classical.choose h1
      let h2 := Classical.choose_spec h1
      let hc_pos := h2.1
      let hc_le := h2.2.1
      let hd_pos := h2.2.2.1
      let hd_one := h2.2.2.2.1
      let produce := h2.2.2.2.2
      have h_e_le_target : e ≤ targetLoss := by
        exact le_trans (min_le_right _ _) (min_le_left _ _)
      have h_e_le_half : e ≤ 1 / (2 * (N : ℝ)) := by
        exact le_trans (min_le_right _ _) (min_le_right _ _)
      let rl : ReversedLevel N sigma targetLoss :=
        ReversedLevel.intermediate e c d produce h_e_pos hc_pos hd_pos hd_one hc_le h_e_le_target h_e_le_half
      have h_valid : rl.valid := by
        simp [ReversedLevel.valid, ReversedLevel.c, ReversedLevel.d, ReversedLevel.e]
        ; exact ⟨hc_pos, hd_pos, hd_one, hc_le, h_e_pos, h_e_le_target⟩
      exact ⟨rl, h_valid⟩

/-! ## Properties of buildAllLevels -/

section BuildAllProps

variable
  {sigma targetLoss : ℝ}
  (h_intermediate : WZ1LocallyLinearOneScaleConclusion)
  (h_terminal : WZ1LocallyLinearTerminalScaleConclusion)
  (hFloor : HasWZ1CriticalVolumeFloor sigma)
  (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
  (htargetLoss : 0 < targetLoss)
  {N : ℕ} (hN_two : 2 ≤ N)

private lemma buildAllLevels_succ_e_le_prev_c (i : ℕ) :
    (buildAllLevels h_intermediate h_terminal hFloor hsigma hsigma1 htargetLoss hN_two (i + 1)).1.e ≤
    (buildAllLevels h_intermediate h_terminal hFloor hsigma hsigma1 htargetLoss hN_two i).1.c := by
  simp [buildAllLevels, ReversedLevel.e, ReversedLevel.c]

private lemma buildAllLevels_succ_e_le_half (i : ℕ) :
    (buildAllLevels h_intermediate h_terminal hFloor hsigma hsigma1 htargetLoss hN_two (i + 1)).1.e ≤
    1 / (2 * (N : ℝ)) := by
  simp [buildAllLevels, ReversedLevel.e]

private lemma buildAllLevels_succ_isIntermediate (i : ℕ) :
    ReversedLevel.isIntermediate (buildAllLevels h_intermediate h_terminal hFloor hsigma hsigma1 htargetLoss hN_two (i + 1)).1 = true := by
  simp [buildAllLevels, ReversedLevel.isIntermediate]

private lemma buildAllLevels_zero_isTerminal :
    ReversedLevel.isIntermediate (buildAllLevels h_intermediate h_terminal hFloor hsigma hsigma1 htargetLoss hN_two 0).1 = false := by
  simp [buildAllLevels, ReversedLevel.isIntermediate]

end BuildAllProps

/-! ## Main construction -/

/-- Construct a backward-recursive loss schedule with a specified terminal output loss. -/
noncomputable def construct_backward_schedule_with_target
    {sigma hierarchyLoss targetLoss : ℝ}
    (h_intermediate : WZ1LocallyLinearOneScaleConclusion)
    (h_terminal : WZ1LocallyLinearTerminalScaleConclusion)
    (hFloor : HasWZ1CriticalVolumeFloor sigma)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (htargetLoss : 0 < targetLoss) (htarget_le : targetLoss ≤ hierarchyLoss)
    {N : ℕ} (hN_two : 2 ≤ N) :
    BackwardScheduleData N sigma hierarchyLoss := by
  let buildAll := buildAllLevels h_intermediate h_terminal hFloor hsigma hsigma1 htargetLoss hN_two
  let e (j : Fin N) : ℝ := (buildAll (N - 1 - (j : ℕ))).1.e
  let c (j : Fin N) : ℝ := (buildAll (N - 1 - (j : ℕ))).1.c
  let d (j : Fin N) : ℝ := (buildAll (N - 1 - (j : ℕ))).1.d
  have h_basic : ∀ (i : ℕ), (buildAll i).1.valid := fun i => (buildAll i).2
  have h_main_e_pos : ∀ (j : Fin N), 0 < e j := by
    intro j
    exact (h_basic (N - 1 - (j : ℕ))).2.2.2.2.1
  have h_main_c_pos : ∀ (j : Fin N), 0 < c j := by
    intro j
    exact (h_basic (N - 1 - (j : ℕ))).1
  have h_main_d_pos : ∀ (j : Fin N), 0 < d j := by
    intro j
    exact (h_basic (N - 1 - (j : ℕ))).2.1
  have h_main_d_one : ∀ (j : Fin N), d j ≤ 1 := by
    intro j
    exact (h_basic (N - 1 - (j : ℕ))).2.2.1
  have h_main_c_le : ∀ (j : Fin N), c j ≤ e j / 100 := by
    intro j
    exact (h_basic (N - 1 - (j : ℕ))).2.2.2.1
  have h_main_e_le_target : ∀ (j : Fin N), e j ≤ targetLoss := by
    intro j
    exact (h_basic (N - 1 - (j : ℕ))).2.2.2.2.2
  have h_main_e_last : e (finLast N hN_two) = targetLoss := by
    have h1 : (finLast N hN_two : ℕ) = N - 1 := by
      simp [finLast]
    have h2 : N - 1 - (finLast N hN_two : ℕ) = 0 := by
      rw [h1]; omega
    have h3 : e (finLast N hN_two) = (buildAll 0).1.e := by
      dsimp only [e]
      rw [h2]
    rw [h3]
    have h_term0 : ReversedLevel.isIntermediate (buildAll 0).1 = false :=
      buildAllLevels_zero_isTerminal h_intermediate h_terminal hFloor hsigma hsigma1 htargetLoss (hN_two := hN_two)
    have h4 : (buildAll 0).1.e = targetLoss :=
      ReversedLevel.terminal_e (buildAll 0).1 h_term0
    exact h4
  have h_main_e_le_c_next : ∀ (j : Fin N) (hj : (j : ℕ) + 1 < N),
      e j ≤ c ⟨(j : ℕ) + 1, hj⟩ := by
    intro j hj
    have h_i : ∃ i : ℕ, N - 1 - (j : ℕ) = i + 1 := by
      refine ⟨N - 2 - (j : ℕ), ?_⟩; omega
    rcases h_i with ⟨i, h_eq⟩
    have h_eq2 : N - 1 - ((j : ℕ) + 1) = i := by omega
    have h_ej : e j = (buildAll (i + 1)).1.e := by
      dsimp only [e]
      rw [h_eq]
    have h_cnext : c ⟨(j : ℕ) + 1, hj⟩ = (buildAll i).1.c := by
      dsimp only [c]
      rw [h_eq2]
    rw [h_ej, h_cnext]
    exact buildAllLevels_succ_e_le_prev_c h_intermediate h_terminal hFloor hsigma hsigma1 htargetLoss (hN_two := hN_two) i
  have h_main_e_le_half : ∀ (j : Fin N) (hj : (j : ℕ) + 1 < N),
      e j ≤ 1 / (2 * (N : ℝ)) := by
    intro j hj
    have h_i : ∃ i : ℕ, N - 1 - (j : ℕ) = i + 1 := by
      refine ⟨N - 2 - (j : ℕ), ?_⟩; omega
    rcases h_i with ⟨i, h_eq⟩
    have h_ej : e j = (buildAll (i + 1)).1.e := by
      dsimp only [e]
      rw [h_eq]
    rw [h_ej]
    exact buildAllLevels_succ_e_le_half h_intermediate h_terminal hFloor hsigma hsigma1 htargetLoss (hN_two := hN_two) i
  let produce_intermediate : ∀ (j : Fin N) (hj : (j : ℕ) + 1 < N),
      IntermediateProducerFn sigma (e j) (c j) (d j) := by
    intro j hj
    have h_i : ∃ i : ℕ, N - 1 - (j : ℕ) = i + 1 := by
      refine ⟨N - 2 - (j : ℕ), ?_⟩; omega
    rcases h_i with ⟨i, h_eq⟩
    have h_inter : ReversedLevel.isIntermediate (buildAll (N - 1 - (j : ℕ))).1 = true := by
      rw [h_eq]
      exact buildAllLevels_succ_isIntermediate h_intermediate h_terminal hFloor hsigma hsigma1 htargetLoss (hN_two := hN_two) i
    exact ReversedLevel.getIntermediateProduce (buildAll (N - 1 - (j : ℕ))).1 h_inter
  let produce_terminal : TerminalProducerFn sigma targetLoss
      (c (finLast N hN_two)) (d (finLast N hN_two)) := by
    have h_term : ReversedLevel.isIntermediate (buildAll 0).1 = false :=
      buildAllLevels_zero_isTerminal h_intermediate h_terminal hFloor hsigma hsigma1 htargetLoss (hN_two := hN_two)
    have h1 : (finLast N hN_two : ℕ) = N - 1 := by simp [finLast]
    have h_last : N - 1 - (finLast N hN_two : ℕ) = 0 := by rw [h1]; omega
    have hc : c (finLast N hN_two) = (buildAll 0).1.c := by dsimp only [c]; rw [h_last]
    have hd : d (finLast N hN_two) = (buildAll 0).1.d := by dsimp only [d]; rw [h_last]
    rw [hc, hd]
    exact ReversedLevel.getTerminalProduce (buildAll 0).1 h_term
  exact
    { hN_two := hN_two
      targetLoss := targetLoss
      targetLoss_pos := htargetLoss
      targetLoss_le_hierarchyLoss := htarget_le
      e := e
      c := c
      d := d
      produce_intermediate := produce_intermediate
      produce_terminal := produce_terminal
      e_pos := h_main_e_pos
      c_pos := h_main_c_pos
      d_pos := h_main_d_pos
      d_le_one := h_main_d_one
      c_le_e_div_100 := h_main_c_le
      e_last := h_main_e_last
      e_le_c_next := h_main_e_le_c_next
      e_le_targetLoss := h_main_e_le_target
      e_le_half_N := h_main_e_le_half }

/-- Construct a backward-recursive loss schedule from the two producer hypotheses.
Uses `hierarchyLoss` as the terminal output loss. -/
noncomputable def construct_backward_schedule
    {sigma hierarchyLoss : ℝ}
    (h_intermediate : WZ1LocallyLinearOneScaleConclusion)
    (h_terminal : WZ1LocallyLinearTerminalScaleConclusion)
    (hFloor : HasWZ1CriticalVolumeFloor sigma)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1)
    (hhierarchyLoss : 0 < hierarchyLoss) {N : ℕ} (hN_two : 2 ≤ N) :
    BackwardScheduleData N sigma hierarchyLoss :=
  construct_backward_schedule_with_target h_intermediate h_terminal hFloor
    hsigma hsigma1 hhierarchyLoss (by linarith) (hN_two := hN_two)

end BackwardSchedule

end Kakeya.Assouad
