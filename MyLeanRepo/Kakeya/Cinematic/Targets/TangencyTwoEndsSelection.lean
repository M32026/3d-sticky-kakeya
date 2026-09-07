import MyLeanRepo.Kakeya.Cinematic.Statements

/-!
# Tangency-scale two-ends selection

This is the second two-ends argument in PYZ Section 5. It selects the typical
tangency scale `Delta` after the first metric-diameter localization.
-/

namespace Kakeya.Cinematic

theorem tangency_two_ends_selection :
    TangencyTwoEndsSelectionStatement := by
  classical
  intro eta delta T heta hdelta hdeltaT I F hF_nonempty htangency
  let S : Finset C2Function := F.toFinset
  have hS_nonempty : S.Nonempty := by
    exact F.finite.toFinset_nonempty.mpr hF_nonempty
  let candidates : Finset (C2Function × C2Function) := S ×ˢ S
  have hcandidates_nonempty : candidates.Nonempty :=
    hS_nonempty.product hS_nonempty
  let scale : C2Function × C2Function → ℝ :=
    fun pair => max delta (tangencyParameterOn I pair.2 pair.1)
  let sublevelCard : C2Function × C2Function → ℕ :=
    fun pair =>
      (F.carrier ∩
        {f | tangencyParameterOn I f pair.1 ≤ scale pair}).ncard
  let score : C2Function × C2Function → ℝ :=
    fun pair => (sublevelCard pair : ℝ) / Real.rpow (scale pair) eta
  obtain ⟨chosen, hchosen, hchosen_max⟩ :=
    Finset.exists_max_image candidates score hcandidates_nonempty
  let Delta : ℝ := scale chosen
  let k : C2Function := chosen.1
  let G : FiniteFunctionFamily :=
    { carrier :=
        F.carrier ∩
          {f | tangencyParameterOn I f k ≤ Delta}
      finite := F.finite.inter_of_left _ }
  have hchosen_first : chosen.1 ∈ F.carrier := by
    exact F.finite.mem_toFinset.mp (Finset.mem_product.mp hchosen).1
  have hchosen_second : chosen.2 ∈ F.carrier := by
    exact F.finite.mem_toFinset.mp (Finset.mem_product.mp hchosen).2
  have hDelta_pos : 0 < Delta := by
    exact lt_of_lt_of_le hdelta (le_max_left _ _)
  have hDelta_lower : delta ≤ Delta := le_max_left _ _
  have hDelta_upper : Delta ≤ T := by
    dsimp only [Delta, scale]
    exact max_le hdeltaT (htangency hchosen_second hchosen_first).2
  have heta_nonneg : 0 ≤ eta := heta.le
  have hT_pos : 0 < T := lt_of_lt_of_le hdelta hdeltaT
  have hG_card :
      (G.card : ℝ) =
        ((F.carrier ∩
          {f | tangencyParameterOn I f k ≤ Delta}).ncard : ℝ) := by
    rfl
  have h_retention :
      Real.rpow (Delta / T) eta * (F.card : ℝ) ≤
        2 * (G.card : ℝ) := by
    obtain ⟨anchor, hanchor⟩ := hF_nonempty
    have hanchor_S : anchor ∈ S := F.finite.mem_toFinset.mpr hanchor
    obtain ⟨far, hfar_S, hfar_max⟩ :=
      Finset.exists_max_image S
        (fun f => tangencyParameterOn I f anchor) hS_nonempty
    have hfar : far ∈ F.carrier := F.finite.mem_toFinset.mp hfar_S
    let comparison : C2Function × C2Function := (anchor, far)
    let Delta₀ : ℝ := scale comparison
    have hcomparison_mem : comparison ∈ candidates := by
      exact Finset.mem_product.mpr ⟨hanchor_S, hfar_S⟩
    have hDelta₀_pos : 0 < Delta₀ := by
      exact lt_of_lt_of_le hdelta (le_max_left _ _)
    have hDelta₀_upper : Delta₀ ≤ T := by
      dsimp only [Delta₀, scale, comparison]
      exact max_le hdeltaT (htangency hfar hanchor).2
    have hsublevel_all :
        F.carrier ∩
            {f | tangencyParameterOn I f anchor ≤ Delta₀} =
          F.carrier := by
      apply Set.inter_eq_left.mpr
      intro f hf
      have hfS : f ∈ S := F.finite.mem_toFinset.mpr hf
      exact (hfar_max f hfS).trans (le_max_right _ _)
    have hcomparison_score :
        (F.card : ℝ) / Real.rpow Delta₀ eta ≤
          (G.card : ℝ) / Real.rpow Delta eta := by
      have hmax := hchosen_max comparison hcomparison_mem
      dsimp only [score, sublevelCard] at hmax
      rw [show scale comparison = Delta₀ by rfl,
        show scale chosen = Delta by rfl, hsublevel_all] at hmax
      simpa [FiniteFunctionFamily.card, k, hG_card] using hmax
    have hDelta₀_pow_le :
        Real.rpow Delta₀ eta ≤ Real.rpow T eta :=
      Real.rpow_le_rpow hDelta₀_pos.le hDelta₀_upper heta_nonneg
    have hcard_nonneg : 0 ≤ (F.card : ℝ) := by positivity
    have hcompare_T :
        (F.card : ℝ) / Real.rpow T eta ≤
          (G.card : ℝ) / Real.rpow Delta eta := by
      calc
        (F.card : ℝ) / Real.rpow T eta
            ≤ (F.card : ℝ) / Real.rpow Delta₀ eta := by
              exact div_le_div_of_nonneg_left hcard_nonneg
                (Real.rpow_pos_of_pos hDelta₀_pos eta) hDelta₀_pow_le
        _ ≤ (G.card : ℝ) / Real.rpow Delta eta :=
          hcomparison_score
    have hmul :
        ((F.card : ℝ) / Real.rpow T eta) *
            Real.rpow Delta eta ≤ (G.card : ℝ) :=
      (le_div_iff₀ (Real.rpow_pos_of_pos hDelta_pos eta)).mp hcompare_T
    calc
      Real.rpow (Delta / T) eta * (F.card : ℝ)
          = ((F.card : ℝ) / Real.rpow T eta) *
              Real.rpow Delta eta := by
                change (Delta / T) ^ eta * (F.card : ℝ) =
                  ((F.card : ℝ) / T ^ eta) * Delta ^ eta
                rw [Real.div_rpow hDelta_pos.le hT_pos.le]
                ring
      _ ≤ (G.card : ℝ) := hmul
      _ ≤ 2 * (G.card : ℝ) := by
            have hG_nonneg : 0 ≤ (G.card : ℝ) := by positivity
            linarith
  refine ⟨Delta, k, G, hDelta_lower, hDelta_upper, hchosen_first, rfl,
    h_retention, ?_⟩
  intro g hg lambda hlambda_lower hlambda_upper
  have hlambda_pos : 0 < lambda := by
    have hdelta_div_pos : 0 < delta / Delta :=
      div_pos hdelta hDelta_pos
    exact hdelta_div_pos.trans hlambda_lower
  let A : Set C2Function :=
    F.carrier ∩
      {f | tangencyParameterOn I f g ≤ lambda * Delta}
  have hA_finite : A.Finite := F.finite.inter_of_left _
  by_cases hA_empty : A = ∅
  · rw [show
      F.carrier ∩
          {f | tangencyParameterOn I f g ≤ lambda * Delta} = ∅
        from hA_empty]
    simp
    positivity
  · have hA_nonempty : A.Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hA_empty
    obtain ⟨far, hfarA, hfar_max⟩ :=
      Finset.exists_max_image hA_finite.toFinset
        (fun f => tangencyParameterOn I f g)
        (hA_finite.toFinset_nonempty.mpr hA_nonempty)
    have hfarF : far ∈ F.carrier :=
      (hA_finite.mem_toFinset.mp hfarA).1
    have hfar_upper :
        tangencyParameterOn I far g ≤ lambda * Delta :=
      (hA_finite.mem_toFinset.mp hfarA).2
    have hdelta_lt_lambda_Delta : delta < lambda * Delta := by
      exact (div_lt_iff₀ hDelta_pos).mp hlambda_lower
    let comparison : C2Function × C2Function := (g, far)
    let Delta' : ℝ := scale comparison
    have hcomparison_mem : comparison ∈ candidates := by
      exact Finset.mem_product.mpr
        ⟨F.finite.mem_toFinset.mpr hg,
          F.finite.mem_toFinset.mpr hfarF⟩
    have hDelta'_pos : 0 < Delta' :=
      lt_of_lt_of_le hdelta (le_max_left _ _)
    have hDelta'_upper : Delta' ≤ lambda * Delta := by
      dsimp only [Delta', scale, comparison]
      exact max_le hdelta_lt_lambda_Delta.le hfar_upper
    have hA_sublevel :
        A =
          F.carrier ∩
            {f | tangencyParameterOn I f g ≤ Delta'} := by
      apply Set.Subset.antisymm
      · intro f hfA
        have hfA' := hA_finite.mem_toFinset.mpr hfA
        exact ⟨hfA.1,
          (hfar_max f hfA').trans (le_max_right _ _)⟩
      · intro f hf
        exact ⟨hf.1, hf.2.trans hDelta'_upper⟩
    have hscore := hchosen_max comparison hcomparison_mem
    have hscore' :
        (A.ncard : ℝ) / Real.rpow Delta' eta ≤
          (G.card : ℝ) / Real.rpow Delta eta := by
      dsimp only [score, sublevelCard] at hscore
      rw [show scale comparison = Delta' by rfl,
        show scale chosen = Delta by rfl, ← hA_sublevel] at hscore
      simpa [k, hG_card] using hscore
    have hmul :
        (A.ncard : ℝ) * Real.rpow Delta eta ≤
          (G.card : ℝ) * Real.rpow Delta' eta := by
      exact (div_le_div_iff₀
        (Real.rpow_pos_of_pos hDelta'_pos eta)
        (Real.rpow_pos_of_pos hDelta_pos eta)).mp hscore'
    have hcard_A :
        (A.ncard : ℝ) ≤
          (Real.rpow Delta' eta / Real.rpow Delta eta) *
            (G.card : ℝ) := by
      calc
        (A.ncard : ℝ)
            ≤ ((G.card : ℝ) * Real.rpow Delta' eta) /
                Real.rpow Delta eta := by
              exact (le_div_iff₀
                (Real.rpow_pos_of_pos hDelta_pos eta)).2 hmul
        _ = (Real.rpow Delta' eta / Real.rpow Delta eta) *
              (G.card : ℝ) := by ring
    have hratio_nonneg : 0 ≤ Delta' / Delta := by positivity
    have hratio_upper : Delta' / Delta ≤ lambda := by
      exact (div_le_iff₀ hDelta_pos).mpr hDelta'_upper
    have hpow_ratio :
        Real.rpow Delta' eta / Real.rpow Delta eta ≤
          Real.rpow lambda eta := by
      have heq :
          Real.rpow Delta' eta / Real.rpow Delta eta =
            Real.rpow (Delta' / Delta) eta := by
        change Delta' ^ eta / Delta ^ eta = (Delta' / Delta) ^ eta
        exact (Real.div_rpow hDelta'_pos.le hDelta_pos.le eta).symm
      rw [heq]
      exact Real.rpow_le_rpow hratio_nonneg hratio_upper heta_nonneg
    have hG_nonneg : 0 ≤ (G.card : ℝ) := by positivity
    calc
      (((F.carrier ∩
          {f | tangencyParameterOn I f g ≤ lambda * Delta}).ncard :
            ℕ) : ℝ)
          = (A.ncard : ℝ) := rfl
      _ ≤ (Real.rpow Delta' eta / Real.rpow Delta eta) *
            (G.card : ℝ) := hcard_A
      _ ≤ Real.rpow lambda eta * (G.card : ℝ) := by
            exact mul_le_mul_of_nonneg_right hpow_ratio hG_nonneg
      _ ≤ 2 * Real.rpow lambda eta * (G.card : ℝ) := by
            have hpow_nonneg : 0 ≤ Real.rpow lambda eta :=
              Real.rpow_nonneg hlambda_pos.le _
            nlinarith

end Kakeya.Cinematic
