import MyLeanRepo.Kakeya.Cinematic.Statements

/-!
# Finite two-ends selection

This is the repaired finite metric selection used at the start of PYZ
Section 5. The explicit diameter hypothesis rules out the counterexample to
the earlier over-general statement.
-/

namespace Kakeya.Cinematic

theorem two_ends_selection :
    TwoEndsSelectionStatement := by
  classical
  intro epsilon delta K hepsilon hdelta hdeltaK F hF_nonempty hdiam
  let S : Finset C2Function := F.toFinset
  have hS_nonempty : S.Nonempty := by
    exact F.finite.toFinset_nonempty.mpr hF_nonempty
  let candidates : Finset (C2Function × C2Function) := S ×ˢ S
  have hcandidates_nonempty : candidates.Nonempty :=
    hS_nonempty.product hS_nonempty
  let radius : C2Function × C2Function → ℝ :=
    fun pair => max delta (dist pair.1 pair.2)
  let ballCard : C2Function × C2Function → ℕ :=
    fun pair => (F.carrier ∩ c2Ball pair.1 (radius pair)).ncard
  let score : C2Function × C2Function → ℝ :=
    fun pair => (ballCard pair : ℝ) / Real.rpow (radius pair) epsilon
  obtain ⟨chosen, hchosen, hchosen_max⟩ :=
    Finset.exists_max_image candidates score hcandidates_nonempty
  let t : ℝ := radius chosen
  let center : C2Function := chosen.1
  let G : FiniteFunctionFamily :=
    { carrier := F.carrier ∩ c2Ball center t
      finite := F.finite.inter_of_left _ }
  have hchosen_first : chosen.1 ∈ F.carrier := by
    exact F.finite.mem_toFinset.mp (Finset.mem_product.mp hchosen).1
  have hchosen_second : chosen.2 ∈ F.carrier := by
    exact F.finite.mem_toFinset.mp (Finset.mem_product.mp hchosen).2
  have ht_pos : 0 < t := by
    exact lt_of_lt_of_le hdelta (le_max_left _ _)
  have ht_lower : delta ≤ t := le_max_left _ _
  have ht_upper : t ≤ K := by
    dsimp only [t, radius]
    exact max_le hdeltaK (hdiam hchosen_first hchosen_second)
  have hepsilon_nonneg : 0 ≤ epsilon := hepsilon.le
  have hK_pos : 0 < K := lt_of_lt_of_le hdelta hdeltaK
  have hG_card :
      (G.card : ℝ) =
        ((F.carrier ∩ c2Ball center t).ncard : ℝ) := by
    rfl
  have h_retention :
      Real.rpow (t / K) epsilon * (F.card : ℝ) ≤ (G.card : ℝ) := by
    obtain ⟨anchor, hanchor⟩ := hF_nonempty
    have hanchor_S : anchor ∈ S := F.finite.mem_toFinset.mpr hanchor
    obtain ⟨far, hfar_S, hfar_max⟩ :=
      Finset.exists_max_image S (fun f => dist anchor f) hS_nonempty
    have hfar : far ∈ F.carrier := F.finite.mem_toFinset.mp hfar_S
    let comparison : C2Function × C2Function := (anchor, far)
    let r₀ : ℝ := radius comparison
    have hcomparison_mem : comparison ∈ candidates := by
      exact Finset.mem_product.mpr ⟨hanchor_S, hfar_S⟩
    have hr₀_pos : 0 < r₀ := by
      exact lt_of_lt_of_le hdelta (le_max_left _ _)
    have hr₀_upper : r₀ ≤ K := by
      dsimp only [r₀, radius, comparison]
      exact max_le hdeltaK (hdiam hanchor hfar)
    have hball_all :
        F.carrier ∩ c2Ball anchor r₀ = F.carrier := by
      apply Set.inter_eq_left.mpr
      intro f hf
      have hfS : f ∈ S := F.finite.mem_toFinset.mpr hf
      have hdist_far : dist anchor f ≤ dist anchor far := hfar_max f hfS
      have hdist_radius : dist anchor f ≤ r₀ := by
        exact hdist_far.trans (le_max_right _ _)
      rw [mem_c2Ball]
      simpa [c2Distance_eq_dist, dist_comm] using hdist_radius
    have hcomparison_score :
        (F.card : ℝ) / Real.rpow r₀ epsilon ≤
          (G.card : ℝ) / Real.rpow t epsilon := by
      have hmax := hchosen_max comparison hcomparison_mem
      dsimp only [score, ballCard] at hmax
      rw [show radius comparison = r₀ by rfl,
        show radius chosen = t by rfl, hball_all] at hmax
      simpa [FiniteFunctionFamily.card, hG_card] using hmax
    have hr₀_pow_le : Real.rpow r₀ epsilon ≤ Real.rpow K epsilon :=
      Real.rpow_le_rpow hr₀_pos.le hr₀_upper hepsilon_nonneg
    have hcard_nonneg : 0 ≤ (F.card : ℝ) := by positivity
    have hcompare_K :
        (F.card : ℝ) / Real.rpow K epsilon ≤
          (G.card : ℝ) / Real.rpow t epsilon := by
      calc
        (F.card : ℝ) / Real.rpow K epsilon
            ≤ (F.card : ℝ) / Real.rpow r₀ epsilon := by
              exact div_le_div_of_nonneg_left hcard_nonneg
                (Real.rpow_pos_of_pos hr₀_pos epsilon) hr₀_pow_le
        _ ≤ (G.card : ℝ) / Real.rpow t epsilon := hcomparison_score
    have hmul :
        ((F.card : ℝ) / Real.rpow K epsilon) *
            Real.rpow t epsilon ≤ (G.card : ℝ) :=
      (le_div_iff₀ (Real.rpow_pos_of_pos ht_pos epsilon)).mp hcompare_K
    calc
      Real.rpow (t / K) epsilon * (F.card : ℝ)
          = ((F.card : ℝ) / Real.rpow K epsilon) *
              Real.rpow t epsilon := by
                change (t / K) ^ epsilon * (F.card : ℝ) =
                  ((F.card : ℝ) / K ^ epsilon) * t ^ epsilon
                rw [Real.div_rpow ht_pos.le hK_pos.le]
                ring
      _ ≤ (G.card : ℝ) := hmul
  refine ⟨t, center, G, ht_lower, ht_upper, ?_, h_retention, ?_⟩
  · intro f hf
    exact hf
  · intro g lambda hlambda_lower hlambda_upper
    have hlambda_pos : 0 < lambda := by
      have hdelta_div_pos : 0 < delta / t := div_pos hdelta ht_pos
      exact hdelta_div_pos.trans hlambda_lower
    let A : Set C2Function := G.carrier ∩ c2Ball g (lambda * t)
    have hA_finite : A.Finite := G.finite.inter_of_left _
    by_cases hA_empty : A = ∅
    · rw [show G.carrier ∩ c2Ball g (lambda * t) = ∅ from hA_empty]
      simp
      positivity
    · have hA_nonempty : A.Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hA_empty
      obtain ⟨h, hhA⟩ := hA_nonempty
      have hhG : h ∈ G.carrier := hhA.1
      have hhF : h ∈ F.carrier := hhG.1
      have hdelta_lt_lambda_t : delta < lambda * t := by
        exact (div_lt_iff₀ ht_pos).mp hlambda_lower
      let B : Set C2Function :=
        F.carrier ∩ c2Ball h (2 * lambda * t)
      have hB_finite : B.Finite := F.finite.inter_of_left _
      have hhB : h ∈ B := by
        refine ⟨hhF, ?_⟩
        rw [mem_c2Ball]
        simp [show 0 ≤ 2 * lambda * t by positivity]
      have hB_nonempty : B.Nonempty := ⟨h, hhB⟩
      obtain ⟨far, hfarB, hfar_max⟩ :=
        Finset.exists_max_image hB_finite.toFinset
          (fun f => dist h f)
          (hB_finite.toFinset_nonempty.mpr hB_nonempty)
      have hfarF : far ∈ F.carrier :=
        (hB_finite.mem_toFinset.mp hfarB).1
      let comparison : C2Function × C2Function := (h, far)
      let r : ℝ := radius comparison
      have hcomparison_mem : comparison ∈ candidates := by
        exact Finset.mem_product.mpr
          ⟨F.finite.mem_toFinset.mpr hhF,
            F.finite.mem_toFinset.mpr hfarF⟩
      have hr_pos : 0 < r :=
        lt_of_lt_of_le hdelta (le_max_left _ _)
      have hfar_radius : dist h far ≤ 2 * lambda * t := by
        have := (hB_finite.mem_toFinset.mp hfarB).2
        rw [mem_c2Ball] at this
        simpa [c2Distance_eq_dist, dist_comm] using this
      have hr_upper : r ≤ 2 * lambda * t := by
        dsimp only [r, radius, comparison]
        exact max_le (by nlinarith [hdelta_lt_lambda_t])
          (hfar_radius.trans_eq (by ring))
      have hA_subset_B : A ⊆ B := by
        intro f hfA
        have hfG : f ∈ G.carrier := hfA.1
        have hfF : f ∈ F.carrier := hfG.1
        have hfg : dist f g ≤ lambda * t := by
          have hfg_ball : f ∈ c2Ball g (lambda * t) := by
            exact hfA.2
          rw [mem_c2Ball] at hfg_ball
          simpa [c2Distance_eq_dist] using hfg_ball
        have hhg : dist h g ≤ lambda * t := by
          have hhg_ball : h ∈ c2Ball g (lambda * t) := by
            exact hhA.2
          rw [mem_c2Ball] at hhg_ball
          simpa [c2Distance_eq_dist] using hhg_ball
        have hfh : dist f h ≤ 2 * lambda * t := by
          calc
            dist f h ≤ dist f g + dist g h := dist_triangle _ _ _
            _ ≤ lambda * t + lambda * t := by
              gcongr
              simpa [dist_comm] using hhg
            _ = 2 * lambda * t := by ring
        exact ⟨hfF, by rwa [mem_c2Ball]⟩
      have hB_ball :
          B = F.carrier ∩ c2Ball h r := by
        apply Set.Subset.antisymm
        · intro f hfB
          have hfB' := hB_finite.mem_toFinset.mpr hfB
          have hdist_far : dist h f ≤ dist h far := hfar_max f hfB'
          have hdist_r : dist h f ≤ r :=
            hdist_far.trans (le_max_right _ _)
          exact ⟨hfB.1, by
            rw [mem_c2Ball]
            simpa [c2Distance_eq_dist, dist_comm] using hdist_r⟩
        · intro f hf
          have hdist_r : dist h f ≤ r := by
            have hf_ball : f ∈ c2Ball h r := hf.2
            rw [mem_c2Ball] at hf_ball
            simpa [c2Distance_eq_dist, dist_comm] using hf_ball
          exact ⟨hf.1, by
            rw [mem_c2Ball]
            simpa [c2Distance_eq_dist, dist_comm] using
              hdist_r.trans hr_upper⟩
      have hcard_A_B : (A.ncard : ℝ) ≤ (B.ncard : ℝ) := by
        exact_mod_cast Set.ncard_le_ncard hA_subset_B hB_finite
      have hscore :=
        hchosen_max comparison hcomparison_mem
      have hscore' :
          (B.ncard : ℝ) / Real.rpow r epsilon ≤
            (G.card : ℝ) / Real.rpow t epsilon := by
        dsimp only [score, ballCard] at hscore
        rw [show radius comparison = r by rfl,
          show radius chosen = t by rfl, ← hB_ball] at hscore
        simpa [hG_card] using hscore
      have hmul :
          (B.ncard : ℝ) * Real.rpow t epsilon ≤
            (G.card : ℝ) * Real.rpow r epsilon := by
        exact (div_le_div_iff₀
          (Real.rpow_pos_of_pos hr_pos epsilon)
          (Real.rpow_pos_of_pos ht_pos epsilon)).mp hscore'
      have hcard_B :
          (B.ncard : ℝ) ≤
            (Real.rpow r epsilon / Real.rpow t epsilon) *
              (G.card : ℝ) := by
        calc
          (B.ncard : ℝ)
              ≤ ((G.card : ℝ) * Real.rpow r epsilon) /
                  Real.rpow t epsilon := by
                exact (le_div_iff₀
                  (Real.rpow_pos_of_pos ht_pos epsilon)).2 hmul
          _ = (Real.rpow r epsilon / Real.rpow t epsilon) *
                (G.card : ℝ) := by ring
      have hratio_nonneg : 0 ≤ r / t := by positivity
      have hratio_upper : r / t ≤ 2 * lambda := by
        exact (div_le_iff₀ ht_pos).mpr (by simpa [mul_assoc] using hr_upper)
      have hpow_ratio :
          Real.rpow r epsilon / Real.rpow t epsilon ≤
            Real.rpow (2 * lambda) epsilon := by
        have heq :
            Real.rpow r epsilon / Real.rpow t epsilon =
              Real.rpow (r / t) epsilon := by
          change r ^ epsilon / t ^ epsilon = (r / t) ^ epsilon
          exact (Real.div_rpow hr_pos.le ht_pos.le epsilon).symm
        rw [heq]
        exact Real.rpow_le_rpow hratio_nonneg hratio_upper hepsilon_nonneg
      have hG_nonneg : 0 ≤ (G.card : ℝ) := by positivity
      calc
        ((G.carrier ∩ c2Ball g (lambda * t)).ncard : ℝ)
            = (A.ncard : ℝ) := rfl
        _ ≤ (B.ncard : ℝ) := hcard_A_B
        _ ≤ (Real.rpow r epsilon / Real.rpow t epsilon) *
              (G.card : ℝ) := hcard_B
        _ ≤ Real.rpow (2 * lambda) epsilon * (G.card : ℝ) := by
              exact mul_le_mul_of_nonneg_right hpow_ratio hG_nonneg
        _ ≤ 4 * Real.rpow (2 * lambda) epsilon * (G.card : ℝ) := by
              have hpow_nonneg :
                  0 ≤ Real.rpow (2 * lambda) epsilon :=
                Real.rpow_nonneg (by positivity) _
              nlinarith

end Kakeya.Cinematic
