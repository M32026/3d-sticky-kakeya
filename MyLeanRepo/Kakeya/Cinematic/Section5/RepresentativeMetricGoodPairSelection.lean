import MyLeanRepo.Kakeya.Cinematic.Section5.RepresentativeMetricGoodPairInputs

/-!
# Metric-good pairs at the common representative scale
-/

namespace Kakeya.Cinematic

theorem representative_metric_good_pair_selection :
    RepresentativeMetricGoodPairSelectionStatement := by
  unfold RepresentativeMetricGoodPairSelectionStatement
  intro hCounting family E K delta diameter epsilon eta tRep DeltaRep C_R
    hdelta data p metricCut
    hmetricCut_pos hmetricCut_lt hmetricScale
    hcompat
  dsimp only
  classical
  let G := data.assignment.fiber p
  let F := data.metricFiber p
  let t := data.exactT p
  let cert := data.certificate p
  let S := G.toFinset
  have ht : 0 < t := hdelta.trans_le cert.delta_le_t
  have hGF : G.carrier ⊆ F.carrier := data.fiber_subset_metric p
  have hmetricRetention :
      12 * Real.rpow (2 * metricCut) epsilon * (F.card : ℝ) ≤
        (G.card : ℝ) := by
    have hcompat' :
        12 * Real.rpow (2 * metricCut) epsilon ≤
          (1 / 2 : ℝ) *
            Real.rpow
              (data.exactDelta p / (4 * data.exactT p)) eta := by
      linarith
    calc
      12 * Real.rpow (2 * metricCut) epsilon * (F.card : ℝ) ≤
          ((1 / 2 : ℝ) *
            Real.rpow
              (data.exactDelta p / (4 * data.exactT p)) eta) *
            (F.card : ℝ) := by
        gcongr
      _ ≤ (1 / 2 : ℝ) * (2 * (G.card : ℝ)) := by
        have hret :
            Real.rpow
                  (data.exactDelta p / (4 * data.exactT p)) eta *
                (F.card : ℝ) ≤
              2 * (G.card : ℝ) := by
          have h_eq : data.tangencyFiber p = G := by
            exact (data.assignment_fiber p).symm
          simpa [F, h_eq] using cert.tangency_retention
        have hscaled :=
          mul_le_mul_of_nonneg_left hret
            (show (0 : ℝ) ≤ 1 / 2 by norm_num)
        calc
          ((1 / 2 : ℝ) *
                Real.rpow
                  (data.exactDelta p / (4 * data.exactT p)) eta) *
              (F.card : ℝ) =
            (1 / 2 : ℝ) *
              (Real.rpow
                  (data.exactDelta p / (4 * data.exactT p)) eta *
                (F.card : ℝ)) := by ring
          _ ≤ (1 / 2 : ℝ) * (2 * (G.card : ℝ)) := hscaled
      _ = (G.card : ℝ) := by ring
  have hBadMetric : ∀ g ∈ G.carrier,
      3 * ((G.carrier ∩ c2Ball g (metricCut * t)).ncard : ℝ) ≤
        (G.card : ℝ) := by
    intro g hg
    have hMetricSubset :
        G.carrier ∩ c2Ball g (metricCut * t) ⊆
          F.carrier ∩ c2Ball g (metricCut * t) := by
      intro f hf
      exact ⟨hGF hf.1, hf.2⟩
    have hMetricCard :
        ((G.carrier ∩ c2Ball g (metricCut * t)).ncard : ℝ) ≤
          ((F.carrier ∩ c2Ball g (metricCut * t)).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hMetricSubset
        (F.finite.subset Set.inter_subset_left)
    have hNonconc :
        ((F.carrier ∩ c2Ball g (metricCut * t)).ncard : ℝ) ≤
          4 * Real.rpow (2 * metricCut) epsilon * (F.card : ℝ) :=
      cert.metric_nonconcentration g metricCut hmetricScale hmetricCut_lt
    calc
      3 * ((G.carrier ∩ c2Ball g (metricCut * t)).ncard : ℝ) ≤
          3 * ((F.carrier ∩ c2Ball g (metricCut * t)).ncard : ℝ) :=
        mul_le_mul_of_nonneg_left hMetricCard (by norm_num)
      _ ≤ 3 *
          (4 * Real.rpow (2 * metricCut) epsilon * (F.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hNonconc (by norm_num)
      _ = 12 * Real.rpow (2 * metricCut) epsilon * (F.card : ℝ) := by
        ring
      _ ≤ (G.card : ℝ) := hmetricRetention
  let bad₁ : C2Function → Finset C2Function := fun g =>
    S.filter (fun h => c2Distance h g ≤ metricCut * t)
  let bad₂ : C2Function → Finset C2Function := fun _ =>
    (∅ : Finset C2Function)
  have hS_coe : (S : Set C2Function) = G.carrier := by
    simp [S, FiniteFunctionFamily.toFinset]
  have hG_card : G.card = S.card := by
    have h1 : G.card = G.carrier.ncard := by rfl
    have h2 : (S : Set C2Function).ncard = S.card :=
      Set.ncard_coe_finset S
    have h3 : G.carrier.ncard = (S : Set C2Function).ncard := by
      rw [hS_coe]
    rw [h1, h3, h2]
  have hbad₁ : ∀ g ∈ S, 3 * (S ∩ bad₁ g).card ≤ S.card := by
    intro g hg
    have hg' : g ∈ G.carrier := by
      rw [← hS_coe]
      exact hg
    have hbound :
        3 * ((G.carrier ∩ c2Ball g (metricCut * t)).ncard : ℝ) ≤
          (G.card : ℝ) :=
      hBadMetric g hg'
    have hsub : bad₁ g ⊆ S := Finset.filter_subset _ _
    have h_inter : S ∩ bad₁ g = bad₁ g :=
      Finset.inter_eq_right.mpr hsub
    have h_set :
        ((bad₁ g : Finset C2Function) : Set C2Function) =
          G.carrier ∩ c2Ball g (metricCut * t) := by
      ext h
      simp only [bad₁, Finset.mem_coe, Finset.mem_filter]
      have h6 : h ∈ S ↔ h ∈ G.carrier := by
        have h7 : h ∈ (S : Set C2Function) ↔ h ∈ G.carrier := by
          rw [hS_coe]
        simpa [Finset.mem_coe] using h7
      rw [h6]
      simp [mem_c2Ball, Set.mem_inter_iff]
    have h_card :
        (bad₁ g).card =
          (G.carrier ∩ c2Ball g (metricCut * t)).ncard := by
      have h :
          (G.carrier ∩ c2Ball g (metricCut * t)).ncard =
            (bad₁ g).card := by
        rw [← h_set]
        simp
      exact h.symm
    have h_goal : 3 * (bad₁ g).card ≤ S.card := by
      have h' : 3 * ((bad₁ g).card : ℝ) ≤ (G.card : ℝ) := by
        rw [h_card]
        exact hbound
      rw [hG_card] at h'
      exact_mod_cast h'
    rw [h_inter]
    exact h_goal
  have hbad₂ : ∀ g ∈ S, 3 * (S ∩ bad₂ g).card ≤ S.card := by
    intro g _
    simp [bad₂]
  have hmain :
      S.card ^ 2 ≤
        3 * ((S.product S).filter
          (fun pair : C2Function × C2Function =>
            pair.2 ∉ bad₁ pair.1 ∧ pair.2 ∉ bad₂ pair.1)).card :=
    hCounting C2Function S bad₁ bad₂ hbad₁ hbad₂
  have h_pred_iff :
      ∀ (pair : C2Function × C2Function)
        (h1 : pair.1 ∈ S) (h2 : pair.2 ∈ S),
        (pair.2 ∉ bad₁ pair.1 ∧ pair.2 ∉ bad₂ pair.1) ↔
          metricCut * t < c2Distance pair.2 pair.1 := by
    intro pair h1 h2
    have hbad2_empty : pair.2 ∉ bad₂ pair.1 := by
      simp [bad₂]
    have hbad1_iff :
        pair.2 ∈ bad₁ pair.1 ↔
          c2Distance pair.2 pair.1 ≤ metricCut * t := by
      have h :
          pair.2 ∈ bad₁ pair.1 ↔
            pair.2 ∈ S ∧
              c2Distance pair.2 pair.1 ≤ metricCut * t := by
        simp [bad₁]
      rw [h]
      simp [h2]
    constructor
    · rintro ⟨hnot1, _⟩
      exact not_le.mp (fun hle => hnot1 (hbad1_iff.mpr hle))
    · intro hdist
      have hnot1 : pair.2 ∉ bad₁ pair.1 := by
        intro h
        have hle :
            c2Distance pair.2 pair.1 ≤ metricCut * t :=
          hbad1_iff.mp h
        exact not_le.mpr hdist hle
      exact ⟨hnot1, hbad2_empty⟩
  have h_ext :
      ((S.product S).filter
        (fun pair : C2Function × C2Function =>
          pair.2 ∉ bad₁ pair.1 ∧ pair.2 ∉ bad₂ pair.1)) =
        (S.product S).filter
          (fun pair => metricCut * t < c2Distance pair.2 pair.1) := by
    ext pair
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hmem, hcond⟩
      have h1 : pair.1 ∈ S := (Finset.mem_product.mp hmem).1
      have h2 : pair.2 ∈ S := (Finset.mem_product.mp hmem).2
      exact ⟨hmem, (h_pred_iff pair h1 h2).mp hcond⟩
    · rintro ⟨hmem, hcond⟩
      have h1 : pair.1 ∈ S := (Finset.mem_product.mp hmem).1
      have h2 : pair.2 ∈ S := (Finset.mem_product.mp hmem).2
      exact ⟨hmem, (h_pred_iff pair h1 h2).mpr hcond⟩
  rw [h_ext] at hmain
  have h_metric :
      metricCut * tRep / 8 ≤ metricCut * t := by
    have h : tRep ≤ 8 * t := data.rep_le_eight_exactT p
    have h' : metricCut * tRep ≤ metricCut * (8 * t) :=
      mul_le_mul_of_nonneg_left h hmetricCut_pos.le
    linarith
  let pointwiseGoodPairs := (S.product S).filter fun pair =>
    metricCut * t < c2Distance pair.2 pair.1
  let representativeGoodPairs := (S.product S).filter fun pair =>
    metricCut * tRep / 8 < c2Distance pair.2 pair.1
  have h_subset : pointwiseGoodPairs ⊆ representativeGoodPairs := by
    intro pair hpair
    simp only [pointwiseGoodPairs, representativeGoodPairs,
      Finset.mem_filter] at hpair ⊢
    rcases hpair with ⟨hmem, hcond⟩
    refine ⟨hmem, ?_⟩
    calc
      metricCut * tRep / 8 ≤ metricCut * t := h_metric
      _ < c2Distance pair.2 pair.1 := hcond
  have h_card :
      pointwiseGoodPairs.card ≤ representativeGoodPairs.card :=
    Finset.card_le_card h_subset
  have h_final :
      G.card ^ 2 ≤ 3 * representativeGoodPairs.card := by
    have h : G.card = S.card := hG_card
    rw [h]
    exact hmain.trans
      (mul_le_mul_of_nonneg_left h_card (by norm_num))
  exact h_final

end Kakeya.Cinematic
