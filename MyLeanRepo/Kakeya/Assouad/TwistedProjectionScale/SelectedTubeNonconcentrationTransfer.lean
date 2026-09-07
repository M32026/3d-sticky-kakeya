import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SelectedScaleStatements

/-!
WZ2 Section 7: transfer Tube-Wolff and indexed parameter-Frostman bounds to
one selected tube subfamily with an explicit cardinality fraction.

Contained indices and parameter-cluster indices inject into the corresponding
ambient index sets via the selected-family reindexing equivalence. The sole
normalization loss is the inverse of the retained indexed-cardinality fraction.
-/

namespace Kakeya.Assouad

theorem selected_tube_nonconcentration_transfer :
    SelectedTubeNonconcentrationTransferStatement := by
  classical
  intro rho F selected cardinalityFraction hcf_nonzero hcf_top hcard
    tubeConstant parameterConstant hTube hParam
  let S := selectedTubeFamily F selected
  let f : Fin S.card → Fin F.card := fun k => (selected.equivFin.symm k).1
  have hf_inj : Function.Injective f := by
    intro k1 k2 h
    have h' : selected.equivFin.symm k1 = selected.equivFin.symm k2 := by
      apply Subtype.ext
      exact h
    exact selected.equivFin.symm.injective h'
  have h_tube : ∀ k : Fin S.card, S.tube k = F.tube (f k) := by
    intro k
    rfl
  have h_params : ∀ k : Fin S.card,
      @tubeParams rho S k = @tubeParams rho F (f k) := by
    intro k
    simp [tubeParams, h_tube k]
  have h2 : cardinalityFraction⁻¹ * cardinalityFraction = 1 :=
    ENNReal.inv_mul_cancel hcf_nonzero hcf_top
  have h_norm : F.enncard ≤ cardinalityFraction⁻¹ * S.enncard := by
    calc
      F.enncard
        = (cardinalityFraction⁻¹ * cardinalityFraction) * F.enncard := by
          rw [h2, one_mul]
      _ = cardinalityFraction⁻¹ * (cardinalityFraction * F.enncard) := by
          rw [mul_assoc]
      _ ≤ cardinalityFraction⁻¹ * S.enncard := by gcongr
  have h_wolff : TubeWolffBound S (tubeConstant * cardinalityFraction⁻¹) := by
    intro r hdr hr1 T
    let A := S.toBodyFamily.containedIndices T.carrier
    let B := F.toBodyFamily.containedIndices T.carrier
    have h_sub : Finset.image f A ⊆ B := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
      have h_cont : (S.tube k).carrier ⊆ T.carrier :=
        (Finset.mem_filter.mp hk).2
      have h_cont2 : (F.tube (f k)).carrier ⊆ T.carrier := by
        rw [←h_tube k]
        exact h_cont
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ (f k), h_cont2⟩
    have h_card : A.card ≤ B.card := by
      have h3 : (Finset.image f A).card = A.card :=
        Finset.card_image_of_injective A hf_inj
      rw [←h3]
      exact Finset.card_le_card h_sub
    have h4 : (A.card : ENNReal) ≤ (B.card : ENNReal) := by
      exact_mod_cast h_card
    have hS : S.toBodyFamily.containedCount T.carrier = (A.card : ENNReal) := by
      rfl
    have hF : F.toBodyFamily.containedCount T.carrier = (B.card : ENNReal) := by
      rfl
    calc
      S.toBodyFamily.containedCount T.carrier
        = (A.card : ENNReal) := hS
      _ ≤ (B.card : ENNReal) := h4
      _ = F.toBodyFamily.containedCount T.carrier := hF.symm
      _ ≤ tubeConstant * Kakeya.realRpowENN r 2 * F.enncard := hTube r hdr hr1 T
      _ ≤ tubeConstant * Kakeya.realRpowENN r 2 *
          (cardinalityFraction⁻¹ * S.enncard) := by
            gcongr
      _ = (tubeConstant * cardinalityFraction⁻¹) *
          Kakeya.realRpowENN r 2 * S.enncard := by
            simp only [mul_assoc, mul_left_comm]
  have h_frostman :
      TubeParameterFrostmanBound S
        (parameterConstant * cardinalityFraction⁻¹) := by
    intro r hdr hr1 reference
    let i : Fin F.card := f reference
    let A_S := Finset.univ.filter (fun k : Fin S.card =>
      |(@tubeParams rho S k).a - (@tubeParams rho S reference).a| ≤ r ∧
      |(@tubeParams rho S k).b - (@tubeParams rho S reference).b| ≤ r ∧
      |(@tubeParams rho S k).c - (@tubeParams rho S reference).c| ≤ r ∧
      |(@tubeParams rho S k).d - (@tubeParams rho S reference).d| ≤ r)
    let A_F := Finset.univ.filter (fun j : Fin F.card =>
      |(@tubeParams rho F j).a - (@tubeParams rho F i).a| ≤ r ∧
      |(@tubeParams rho F j).b - (@tubeParams rho F i).b| ≤ r ∧
      |(@tubeParams rho F j).c - (@tubeParams rho F i).c| ≤ r ∧
      |(@tubeParams rho F j).d - (@tubeParams rho F i).d| ≤ r)
    have h_sub : Finset.image f A_S ⊆ A_F := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
      have h_cond := (Finset.mem_filter.mp hk).2
      have h_eq1 : @tubeParams rho S k = @tubeParams rho F (f k) := h_params k
      have h_eq2 : @tubeParams rho S reference = @tubeParams rho F i :=
        h_params reference
      simp only [h_eq1, h_eq2] at h_cond
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ (f k), h_cond⟩
    have h_card : A_S.card ≤ A_F.card := by
      have h3 : (Finset.image f A_S).card = A_S.card :=
        Finset.card_image_of_injective A_S hf_inj
      rw [←h3]
      exact Finset.card_le_card h_sub
    have h5 : (A_S.card : ENNReal) ≤ (A_F.card : ENNReal) := by
      exact_mod_cast h_card
    have h_goal : (A_S.card : ENNReal) ≤
        (parameterConstant * cardinalityFraction⁻¹) *
          Kakeya.realRpowENN r 2 * S.enncard := by
      calc
        (A_S.card : ENNReal)
          ≤ (A_F.card : ENNReal) := h5
        _ ≤ parameterConstant * Kakeya.realRpowENN r 2 * F.enncard :=
          hParam r hdr hr1 i
        _ ≤ parameterConstant * Kakeya.realRpowENN r 2 *
            (cardinalityFraction⁻¹ * S.enncard) := by
              gcongr
        _ = (parameterConstant * cardinalityFraction⁻¹) *
            Kakeya.realRpowENN r 2 * S.enncard := by
              simp only [mul_assoc, mul_left_comm]
    simpa [A_S, TubeParameterFrostmanBound] using h_goal
  exact ⟨h_wolff, h_frostman⟩

end Kakeya.Assouad
