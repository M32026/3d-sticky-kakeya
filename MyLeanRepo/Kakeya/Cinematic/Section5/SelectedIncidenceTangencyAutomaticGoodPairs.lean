import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedIncidenceTangencyAutomaticGoodPairsInputs

/-!
# Tangency-automatic good pairs in one selected incidence fiber
-/

namespace Kakeya.Cinematic

theorem selected_incidence_tangency_automatic_good_pairs :
    SelectedIncidenceTangencyAutomaticGoodPairsStatement := by
  classical
  intro hCounting
  intro family E K delta diameter epsilon eta tRep DeltaRep C_R hdelta
    data p selected hselected metricCut
    hmetricCut_pos hmetricCut_lt hmetricScale
    hmetricBudget
  let S := selected
  let I := data.interval
  let t := data.exactT p
  let MF := data.metricFiber p
  have hS_sub_MF : (S : Set C2Function) ⊆ MF.carrier :=
    hselected.trans (data.fiber_subset_metric p)
  let bad₁ : C2Function → Finset C2Function := fun g =>
    S.filter fun h =>
      c2Distance h g ≤ metricCut * tRep / 8
  let bad₂ : C2Function → Finset C2Function := fun _ =>
    (∅ : Finset C2Function)
  have h_tRep_le :
      metricCut * tRep / 8 ≤ metricCut * t := by
    have h : tRep ≤ 8 * t := data.rep_le_eight_exactT p
    have h2 :
        metricCut * tRep ≤ 8 * (metricCut * t) := by
      calc
        metricCut * tRep ≤ metricCut * (8 * t) :=
          mul_le_mul_of_nonneg_left h hmetricCut_pos.le
        _ = 8 * (metricCut * t) := by ring
    linarith
  have hbad₁ :
      ∀ g ∈ S, 3 * (S ∩ bad₁ g).card ≤ S.card := by
    intro g hg
    have hg_MF : g ∈ MF.carrier := hS_sub_MF hg
    have hsub : bad₁ g ⊆ S := Finset.filter_subset _ _
    have h_inter : S ∩ bad₁ g = bad₁ g :=
      Finset.inter_eq_right.mpr hsub
    have h_set_sub :
        (bad₁ g : Set C2Function) ⊆
          MF.carrier ∩ c2Ball g (metricCut * t) := by
      intro h hh
      have h1 : h ∈ S := (Finset.mem_filter.mp hh).1
      have h2 :
          c2Distance h g ≤ metricCut * tRep / 8 :=
        (Finset.mem_filter.mp hh).2
      have h3 : h ∈ MF.carrier := hS_sub_MF h1
      have h4 : c2Distance h g ≤ metricCut * t :=
        h2.trans h_tRep_le
      exact ⟨h3, h4⟩
    have h_card :
        ((bad₁ g).card : ℝ) ≤
          ((MF.carrier ∩
            c2Ball g (metricCut * t)).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard h_set_sub
        (MF.finite.subset Set.inter_subset_left)
    have h_nonconc :
        ((MF.carrier ∩
            c2Ball g (metricCut * t)).ncard : ℝ) ≤
          4 * Real.rpow (2 * metricCut) epsilon *
            (MF.card : ℝ) :=
      (data.certificate p).metric_nonconcentration
        g metricCut hmetricScale hmetricCut_lt
    have h_main :
        3 * ((bad₁ g).card : ℝ) ≤ (S.card : ℝ) := by
      calc
        3 * ((bad₁ g).card : ℝ) ≤
            3 * ((MF.carrier ∩
              c2Ball g (metricCut * t)).ncard : ℝ) := by
          gcongr
        _ ≤ 3 *
            (4 * Real.rpow (2 * metricCut) epsilon *
              (MF.card : ℝ)) := by
          gcongr
        _ = 12 * Real.rpow (2 * metricCut) epsilon *
            (MF.card : ℝ) := by ring
        _ ≤ (S.card : ℝ) := hmetricBudget
    rw [h_inter]
    exact_mod_cast h_main
  have hbad₂ :
      ∀ g ∈ S, 3 * (S ∩ bad₂ g).card ≤ S.card := by
    intro g _
    simp [bad₂]
  have hmain :=
    hCounting C2Function S bad₁ bad₂ hbad₁ hbad₂
  have h_pred_iff :
      ∀ (pair : C2Function × C2Function)
        (h1 : pair.1 ∈ S) (h2 : pair.2 ∈ S),
        (pair.2 ∉ bad₁ pair.1 ∧
            pair.2 ∉ bad₂ pair.1) ↔
          metricCut * tRep / 8 <
              c2Distance pair.2 pair.1 := by
    intro pair h1 h2
    have hbad1_iff :
        pair.2 ∈ bad₁ pair.1 ↔
          c2Distance pair.2 pair.1 ≤
            metricCut * tRep / 8 := by
      have h :
          pair.2 ∈ bad₁ pair.1 ↔
            pair.2 ∈ S ∧
              c2Distance pair.2 pair.1 ≤
                metricCut * tRep / 8 := by
        simp [bad₁, Finset.mem_filter]
      rw [h]
      simp [h2]
    have hbad2_iff : pair.2 ∉ bad₂ pair.1 := by
      simp [bad₂]
    constructor
    · rintro ⟨hnot1, _⟩
      exact not_le.mp fun hle => hnot1 (hbad1_iff.mpr hle)
    · intro hdist
      have hnot1 : pair.2 ∉ bad₁ pair.1 := by
        intro h
        have hle :
            c2Distance pair.2 pair.1 ≤
              metricCut * tRep / 8 :=
          hbad1_iff.mp h
        exact not_le.mpr hdist hle
      exact ⟨hnot1, hbad2_iff⟩
  have h_ext :
      ((S.product S).filter fun pair : C2Function × C2Function =>
          pair.2 ∉ bad₁ pair.1 ∧ pair.2 ∉ bad₂ pair.1) =
        (S.product S).filter fun pair =>
          metricCut * tRep / 8 <
              c2Distance pair.2 pair.1 := by
    ext pair
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hmem, hcond⟩
      have h1 : pair.1 ∈ S :=
        (Finset.mem_product.mp hmem).1
      have h2 : pair.2 ∈ S :=
        (Finset.mem_product.mp hmem).2
      exact ⟨hmem, (h_pred_iff pair h1 h2).mp hcond⟩
    · rintro ⟨hmem, hcond⟩
      have h1 : pair.1 ∈ S :=
        (Finset.mem_product.mp hmem).1
      have h2 : pair.2 ∈ S :=
        (Finset.mem_product.mp hmem).2
      exact ⟨hmem, (h_pred_iff pair h1 h2).mpr hcond⟩
  rw [h_ext] at hmain
  exact hmain

end Kakeya.Cinematic
