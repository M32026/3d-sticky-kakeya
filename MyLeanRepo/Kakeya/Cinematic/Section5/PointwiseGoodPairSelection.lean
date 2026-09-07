import MyLeanRepo.Kakeya.Cinematic.Section5.PointwiseGoodPairInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.Lemma45BadSetBounds

/-!
# Pointwise good-pair selection
-/

namespace Kakeya.Cinematic

theorem pointwise_good_pair_selection :
    PointwiseGoodPairSelectionStatement := by
  classical
  intro hPointwise hCounting family E K delta diameter epsilon eta tRep DeltaRep C_R
    hdelta data p metricCut tangencyCut
    hmetricCut_pos hmetricCut_lt hmetricScale
    htangencyCut_pos htangencyCut_lt htangencyScale
    hcompat htangencySmall
  dsimp only
  let G := data.assignment.fiber p
  let S := G.toFinset
  let t := data.exactT p
  let Delta := data.exactDelta p
  let I := data.interval
  have hBad : ∀ g ∈ G.carrier,
      3 * ((G.carrier ∩ c2Ball g (metricCut * t)).ncard : ℝ) ≤ (G.card : ℝ) ∧
      3 * ((G.carrier ∩ {f | tangencyParameterOn I f g + delta <
        tangencyCut * Delta}).ncard : ℝ) ≤ (G.card : ℝ) :=
    hPointwise lemma45_bad_set_bounds hdelta data p metricCut tangencyCut
      hmetricCut_pos hmetricCut_lt hmetricScale
      htangencyCut_pos htangencyCut_lt htangencyScale
      hcompat htangencySmall
  let bad₁ : C2Function → Finset C2Function := fun g =>
    S.filter (fun h => c2Distance h g ≤ metricCut * t)
  let bad₂ : C2Function → Finset C2Function := fun g =>
    S.filter (fun h => tangencyParameterOn I h g + delta < tangencyCut * Delta)
  have hS_coe : (S : Set C2Function) = G.carrier := by
    simp [S, FiniteFunctionFamily.toFinset]
  have hG_card : G.card = S.card := by
    have h1 : G.card = G.carrier.ncard := by rfl
    have h2 : (S : Set C2Function).ncard = S.card := Set.ncard_coe_finset S
    have h3 : G.carrier.ncard = (S : Set C2Function).ncard := by rw [hS_coe]
    rw [h1, h3, h2]
  have hbad₁ : ∀ g ∈ S, 3 * (S ∩ bad₁ g).card ≤ S.card := by
    intro g hg
    have hg' : g ∈ G.carrier := by
      rw [← hS_coe]
      exact hg
    have hbound :
        3 * ((G.carrier ∩ c2Ball g (metricCut * t)).ncard : ℝ) ≤ (G.card : ℝ) :=
      (hBad g hg').1
    have hsub : bad₁ g ⊆ S := Finset.filter_subset _ _
    have h_inter : S ∩ bad₁ g = bad₁ g :=
      Finset.inter_eq_right.mpr hsub
    have h_set :
        ((bad₁ g : Finset C2Function) : Set C2Function) =
          G.carrier ∩ c2Ball g (metricCut * t) := by
      ext h
      simp only [bad₁, Finset.mem_coe, Finset.mem_filter]
      have h6 : h ∈ S ↔ h ∈ G.carrier := by
        have h7 : h ∈ (S : Set C2Function) ↔ h ∈ G.carrier := by rw [hS_coe]
        simpa [Finset.mem_coe] using h7
      rw [h6]
      simp [mem_c2Ball, Set.mem_inter_iff]
    have h_card :
        (bad₁ g).card = (G.carrier ∩ c2Ball g (metricCut * t)).ncard := by
      have h :
          (G.carrier ∩ c2Ball g (metricCut * t)).ncard = (bad₁ g).card := by
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
    intro g hg
    have hg' : g ∈ G.carrier := by
      rw [← hS_coe]
      exact hg
    have hbound :
        3 * ((G.carrier ∩ {f | tangencyParameterOn I f g + delta <
          tangencyCut * Delta}).ncard : ℝ) ≤ (G.card : ℝ) :=
      (hBad g hg').2
    have hsub : bad₂ g ⊆ S := Finset.filter_subset _ _
    have h_inter : S ∩ bad₂ g = bad₂ g :=
      Finset.inter_eq_right.mpr hsub
    have h_set :
        ((bad₂ g : Finset C2Function) : Set C2Function) =
          G.carrier ∩
            {f | tangencyParameterOn I f g + delta < tangencyCut * Delta} := by
      ext h
      simp only [bad₂, Finset.mem_coe, Finset.mem_filter]
      have h6 : h ∈ S ↔ h ∈ G.carrier := by
        have h7 : h ∈ (S : Set C2Function) ↔ h ∈ G.carrier := by rw [hS_coe]
        simpa [Finset.mem_coe] using h7
      rw [h6]
      simp [Set.mem_inter_iff]
    have h_card :
        (bad₂ g).card =
          (G.carrier ∩
            {f | tangencyParameterOn I f g + delta < tangencyCut * Delta}).ncard := by
      have h :
          (G.carrier ∩
            {f | tangencyParameterOn I f g + delta <
              tangencyCut * Delta}).ncard = (bad₂ g).card := by
        rw [← h_set]
        simp
      exact h.symm
    have h_goal : 3 * (bad₂ g).card ≤ S.card := by
      have h' : 3 * ((bad₂ g).card : ℝ) ≤ (G.card : ℝ) := by
        rw [h_card]
        exact hbound
      rw [hG_card] at h'
      exact_mod_cast h'
    rw [h_inter]
    exact h_goal
  have h_pred_iff :
      ∀ (pair : C2Function × C2Function) (h1 : pair.1 ∈ S) (h2 : pair.2 ∈ S),
        (pair.2 ∉ bad₁ pair.1 ∧ pair.2 ∉ bad₂ pair.1) ↔
          (metricCut * t < c2Distance pair.2 pair.1 ∧
            tangencyCut * Delta ≤
              tangencyParameterOn I pair.2 pair.1 + delta) := by
    intro pair h1 h2
    have hbad1_iff :
        pair.2 ∈ bad₁ pair.1 ↔
          c2Distance pair.2 pair.1 ≤ metricCut * t := by
      have h :
          pair.2 ∈ bad₁ pair.1 ↔
            pair.2 ∈ S ∧ c2Distance pair.2 pair.1 ≤ metricCut * t := by
        simp [bad₁]
      rw [h]
      simp [h2]
    have hbad2_iff :
        pair.2 ∈ bad₂ pair.1 ↔
          tangencyParameterOn I pair.2 pair.1 + delta <
            tangencyCut * Delta := by
      have h :
          pair.2 ∈ bad₂ pair.1 ↔
            pair.2 ∈ S ∧
              tangencyParameterOn I pair.2 pair.1 + delta <
                tangencyCut * Delta := by
        simp [bad₂]
      rw [h]
      simp [h2]
    constructor
    · rintro ⟨hnot1, hnot2⟩
      have hdist : metricCut * t < c2Distance pair.2 pair.1 := by
        exact not_le.mp (fun hle => hnot1 (hbad1_iff.mpr hle))
      have htang :
          tangencyCut * Delta ≤
            tangencyParameterOn I pair.2 pair.1 + delta := by
        exact not_lt.mp (fun hlt => hnot2 (hbad2_iff.mpr hlt))
      exact ⟨hdist, htang⟩
    · rintro ⟨hdist, htang⟩
      have hnot1 : pair.2 ∉ bad₁ pair.1 := by
        intro h
        have hle :
            c2Distance pair.2 pair.1 ≤ metricCut * t := hbad1_iff.mp h
        exact not_le.mpr hdist hle
      have hnot2 : pair.2 ∉ bad₂ pair.1 := by
        intro h
        have hlt :
            tangencyParameterOn I pair.2 pair.1 + delta <
              tangencyCut * Delta := hbad2_iff.mp h
        exact not_lt.mpr htang hlt
      exact ⟨hnot1, hnot2⟩
  have h_ext :
      ((S.product S).filter (fun pair : C2Function × C2Function =>
        pair.2 ∉ bad₁ pair.1 ∧ pair.2 ∉ bad₂ pair.1)) =
        (S.product S).filter (fun pair =>
          metricCut * t < c2Distance pair.2 pair.1 ∧
            tangencyCut * Delta ≤
              tangencyParameterOn I pair.2 pair.1 + delta) := by
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
  have hmain :
      S.card ^ 2 ≤
        3 * ((S.product S).filter (fun pair : C2Function × C2Function =>
          pair.2 ∉ bad₁ pair.1 ∧ pair.2 ∉ bad₂ pair.1)).card :=
    hCounting C2Function S bad₁ bad₂ hbad₁ hbad₂
  rw [h_ext] at hmain
  have h_final :
      G.card ^ 2 ≤
        3 * ((S.product S).filter (fun pair =>
          metricCut * t < c2Distance pair.2 pair.1 ∧
            tangencyCut * Delta ≤
              tangencyParameterOn I pair.2 pair.1 + delta)).card := by
    have h : G.card = S.card := hG_card
    rw [h]
    exact hmain
  exact h_final

end Kakeya.Cinematic
