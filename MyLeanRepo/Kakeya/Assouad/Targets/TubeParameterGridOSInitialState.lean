import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridOSInitialStateStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridOSStateConstruction
import MyLeanRepo.Kakeya.Assouad.Hairbrush.TubeVolumeLower

/-!
WZ2 Proposition 7.1: assemble the corrected terminal state on a delta-grid
four-parameter OS tree.
-/

namespace Kakeya.Assouad

theorem tube_parameter_grid_os_initial_state :
    TubeParameterGridOSInitialStateStatement := by
  intro hParamSel hPrune hFiberReg hReps hOSLift hSelTransfer hNonconc
  intro eta heta
  rcases hParamSel eta heta with ⟨base, hbase3, delta₀, hdelta₀_pos, hdelta₀_lt1, hSelLevels⟩
  refine ⟨base, hbase3, delta₀, hdelta₀_pos, hdelta₀_lt1, ?_⟩
  intro delta hdelta hdelta₀ family hfamily_nonempty hvertical hbounds hcard
    sourceConstant hsource1 hsource_top hfrostman shading hdense hslope
  classical

  rcases hPrune delta eta hdelta (by linarith) heta family shading hdense with
    ⟨pruned, hsub, _hhalfMass, hmass, hperTube, _hwhole⟩

  let lambda := terminalCellInitialDensity delta eta
  let active := positiveMassIndices pruned

  have hreal_pos : 0 < Real.rpow delta eta := Real.rpow_pos_of_pos hdelta eta
  have hlambda_pos' : 0 < lambda := by
    simp [lambda, terminalCellInitialDensity, hreal_pos]
    <;> exact ENNReal.ofReal_pos.mpr hreal_pos
  have htube_vol_pos : ∀ (i : Fin family.card), 0 < (family.tube i).volume := by
    intro i
    have h : (family.tube i).volume ≥ ENNReal.ofReal (delta^2 / 8) :=
      tube_volume_lower hdelta (by linarith) (family.tube i)
    have h2 : 0 < ENNReal.ofReal (delta^2 / 8) := by positivity
    exact h2.trans_le h
  have hfmass_pos : 0 < family.toBodyFamily.mass := by
    have hne : ∃ (i : Fin family.card), True := by
      exact ⟨⟨0, hfamily_nonempty⟩, trivial⟩
    rcases hne with ⟨i, _⟩
    have h3 : (family.toBodyFamily.body i).volume > 0 := htube_vol_pos i
    have h4 : family.toBodyFamily.mass ≥ (family.toBodyFamily.body i).volume := by
      apply Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ i)
    exact h3.trans_le h4
  have hmass_pos : 0 < pruned.mass := by
    have h1 : lambda * family.toBodyFamily.mass ≠ 0 :=
      mul_ne_zero hlambda_pos'.ne' hfmass_pos.ne'
    have h2 : 0 < lambda * family.toBodyFamily.mass := bot_lt_iff_ne_bot.mpr h1
    exact lt_of_lt_of_le h2 hmass
  have hactive_nonempty : active.Nonempty := by
    by_contra h
    have h' : active = ∅ := by simpa using h
    have h'' : ∀ i : Fin family.card, MeasureTheory.volume (pruned.carrier i) = 0 := by
      intro i
      by_contra h3
      have h4 : i ∈ active := by
        simp [active, positiveMassIndices, h3] <;> tauto
      rw [h'] at h4 <;> simp at h4
    have h3 : pruned.mass = 0 := by
      have h4 : pruned.mass =
          ∑ i : Fin family.card, MeasureTheory.volume (pruned.carrier i) := rfl
      rw [h4]
      rw [Finset.sum_congr rfl (fun i _ => h'' i)]
      simp
    exact ne_of_gt hmass_pos h3

  have hactive_sub : active ⊆ Finset.univ := by
    simp [active, positiveMassIndices] <;> tauto
  have huniv_card : (Finset.univ : Finset (Fin family.card)).card = family.card := by
    simp
  have hactive_card_le : active.card ≤ family.card := by
    have h : active.card ≤ (Finset.univ : Finset (Fin family.card)).card :=
      Finset.card_le_card hactive_sub
    rw [huniv_card] at h
    exact h

  have hcard' : (active.card : ENNReal) ≤ Kakeya.realRpowENN delta (-3) := by
    calc
      (active.card : ENNReal) ≤ (family.card : ENNReal) := by
        exact_mod_cast hactive_card_le
      _ = family.enncard := by
        simp [Kakeya.Streamlined.TubeFamily.enncard]
        <;> rfl
      _ ≤ Kakeya.realRpowENN delta (-3) := hcard

  rcases hSelLevels delta hdelta hdelta₀ active.card hcard' with
    ⟨levels, hmesh_lower, hmesh_upper, hloss_bound⟩
  rcases hFiberReg family active hactive_nonempty base levels with ⟨terminal⟩
  rcases hReps family active base levels terminal with ⟨representatives⟩
  have hbase2 : 2 ≤ base := by linarith
  rcases hOSLift family active base levels hbase2 terminal representatives with ⟨uniform⟩

  let selectedFamily := selectedTubeFamily family uniform.selected
  let selectedShading := selectedTubeShading pruned uniform.selected

  have hmass' : lambda * family.toBodyFamily.mass ≤ pruned.mass := hmass
  rcases hSelTransfer hdelta (by linarith) family pruned lambda lambda hperTube hmass'
      base levels terminal representatives uniform with
    ⟨hsel_nonempty, hsel_dense, hsel_card⟩

  let loss := tubeParameterTerminalCellOSLoss active.card base levels
  have hloss_eq : loss = tubeParameterGridInitialLoss active.card base levels := by rfl
  have hloss_bound' : loss ≤ Kakeya.realRpowENN delta (-eta) := by
    rw [hloss_eq]
    exact hloss_bound

  have hloss_ne_zero : loss ≠ 0 := by
    simp [loss, tubeParameterTerminalCellOSLoss, hactive_nonempty]
    <;> norm_num <;> omega
  have hloss_ne_top : loss ≠ ⊤ := by
    simp [loss, tubeParameterTerminalCellOSLoss]
    <;> exact ENNReal.coe_ne_top

  let cardinalityFraction := lambda * loss⁻¹

  have hlambda_pos : 0 < lambda := hlambda_pos'
  have hlambda_ne_zero : lambda ≠ 0 := ne_of_gt hlambda_pos
  have hlambda_ne_top : lambda ≠ ⊤ := by
    have h1 : Real.rpow delta eta < 1 := by
      apply Real.rpow_lt_one (by linarith) (by linarith) heta
    have h2 : Kakeya.realRpowENN delta eta ≠ ⊤ := by
      simp [Kakeya.realRpowENN, h1.ne]
      <;> exact ENNReal.coe_ne_top
    have h3 : (1 / 2 : ENNReal) ≠ ⊤ := by norm_num
    exact ENNReal.mul_ne_top h3 h2

  have hcf_ne_zero : cardinalityFraction ≠ 0 := by
    exact mul_ne_zero hlambda_ne_zero (ENNReal.inv_ne_zero.mpr hloss_ne_top)
  have hcf_ne_top : cardinalityFraction ≠ ⊤ := by
    have h1 : loss⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hloss_ne_zero
    exact ENNReal.mul_ne_top hlambda_ne_top h1

  have htop_wolff : TubeWolffBound family (⊤) := by
    intro rho _ _ T
    have hrho_pos : 0 < rho := by linarith
    have hpos1 : 0 < Kakeya.realRpowENN rho 2 := by
      have h : 0 < Real.rpow rho 2 := Real.rpow_pos_of_pos hrho_pos 2
      exact ENNReal.ofReal_pos.mpr h
    have hpos2 : 0 < family.enncard := by
      simp [Kakeya.Streamlined.TubeFamily.enncard, hfamily_nonempty]
      <;> exact_mod_cast hfamily_nonempty
    have htop :
        (⊤ : ENNReal) * Kakeya.realRpowENN rho 2 * family.enncard = (⊤ : ENNReal) := by
      have hne : Kakeya.realRpowENN rho 2 ≠ 0 := hpos1.ne'
      have h : (⊤ : ENNReal) * Kakeya.realRpowENN rho 2 = (⊤ : ENNReal) := by
        rw [ENNReal.top_mul hne]
      rw [h]
      have hne2 : family.enncard ≠ 0 := hpos2.ne'
      rw [ENNReal.top_mul hne2]
    rw [htop]
    <;> exact le_top
  rcases hNonconc family uniform.selected cardinalityFraction hcf_ne_zero hcf_ne_top
      hsel_card (⊤) sourceConstant htop_wolff hfrostman with
    ⟨_, hparam_frostman⟩

  let parameterConstant := sourceConstant * cardinalityFraction⁻¹

  have hparam_one : 1 ≤ parameterConstant := by
    have h4 : lambda ≤ 1 := by
      have h5 : Real.rpow delta eta ≤ 1 :=
        (Real.rpow_lt_one (by linarith) (by linarith) heta).le
      have h6 : Kakeya.realRpowENN delta eta ≤ 1 := by
        have h7 : Kakeya.realRpowENN delta eta =
            ENNReal.ofReal (Real.rpow delta eta) := by rfl
        rw [h7]
        exact ENNReal.ofReal_le_one.mpr h5
      have h8 : lambda = (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta := by
        simp [lambda, terminalCellInitialDensity] <;> rfl
      rw [h8]
      calc
        (1 / 2 : ENNReal) * Kakeya.realRpowENN delta eta
            ≤ (1 / 2 : ENNReal) * 1 := by gcongr
        _ = (1 / 2 : ENNReal) := by simp
        _ ≤ 1 := by norm_num
    have h6 : loss⁻¹ ≤ 1 := by
      have h7 : 1 ≤ loss := by
        have h_nat :
            2 ≤ (Nat.log 2 active.card + 1) * 2 *
              ((2 * (Nat.log 2 ((base + 1) ^ 4) + 1)) ^ levels) := by
          have h1 : 1 ≤ Nat.log 2 active.card + 1 := by omega
          have h2 : 1 ≤ (2 * (Nat.log 2 ((base + 1) ^ 4) + 1)) ^ levels := by
            apply Nat.one_le_pow <;> omega
          nlinarith
        have h_enr : (2 : ENNReal) ≤ loss := by
          simp [loss, tubeParameterTerminalCellOSLoss]
          <;> exact_mod_cast h_nat
        have h_one_le_two : (1 : ENNReal) ≤ (2 : ENNReal) := by norm_num
        exact le_trans h_one_le_two h_enr
      exact ENNReal.inv_le_one.mpr h7
    have h3 : cardinalityFraction ≤ 1 := by
      calc
        cardinalityFraction = lambda * loss⁻¹ := by rfl
        _ ≤ 1 * 1 := by gcongr <;> tauto
        _ = 1 := by simp
    have h2 : 1 ≤ cardinalityFraction⁻¹ := by
      have h4 : cardinalityFraction⁻¹ ≥ (1 : ENNReal) := by
        have h5 : cardinalityFraction ≤ (1 : ENNReal) := h3
        have h6 : (1 : ENNReal)⁻¹ ≤ cardinalityFraction⁻¹ :=
          ENNReal.inv_le_inv.mpr h5
        simpa using h6
      exact h4
    have h5 : 1 ≤ sourceConstant * cardinalityFraction⁻¹ := by
      calc
        1 = 1 * 1 := by simp
        _ ≤ sourceConstant * cardinalityFraction⁻¹ := by
          exact mul_le_mul hsource1 h2 (by simp) (by simp)
    simpa [parameterConstant] using h5

  have hparam_top : parameterConstant ≠ ⊤ := by
    have h1 : cardinalityFraction⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hcf_ne_zero
    exact ENNReal.mul_ne_top hsource_top h1

  have hselected_vertical : IsInVerticalChart selectedFamily :=
    selectedTubeFamily_isInVerticalChart family uniform.selected hvertical

  have hselected_bounds : ∀ (index : Fin selectedFamily.card),
      |(tubeParams index).a| ≤ 12 ∧ |(tubeParams index).b| ≤ 12 ∧
      |(tubeParams index).c| ≤ 2 ∧ |(tubeParams index).d| ≤ 2 := by
    intro j
    let i : Fin family.card := uniform.selected.equivFin.symm j
    exact hbounds i

  have hselected_slope : IsInSlopeWindow selectedShading := by
    have h1 : selectedShading.union ⊆ pruned.union :=
      selectedTubeShading_union_subset pruned uniform.selected
    have h2 : pruned.union ⊆ shading.union := by
      intro x hx
      rcases hx with ⟨i, hi⟩
      exact ⟨i, hsub i hi⟩
    have h3 : shading.union ⊆ horizontalSlab (-1) 1 := hslope
    simpa [IsInSlopeWindow] using h1.trans (h2.trans h3)

  have hdelta_le_one : delta ≤ 1 := by linarith

  let state := build_terminal_grid_os_state
    terminal representatives uniform selectedFamily rfl selectedShading
    lambda hsel_dense parameterConstant hparam_frostman
    hselected_vertical hselected_bounds hselected_slope
    hlambda_ne_zero hlambda_ne_top hparam_one hparam_top
    hdelta hdelta_le_one

  refine ⟨{
    base := base
    base_ge_three := hbase3
    levels := levels
    mesh_lower := hmesh_lower
    mesh_upper := hmesh_upper
    pruned := pruned
    pruned_subshading := hsub
    pruned_mass := hmass
    pruned_full := hperTube
    active := active
    active_eq := by rfl
    terminal := terminal
    representatives := representatives
    uniform := uniform
    selectedFamily := selectedFamily
    selectedFamily_eq := by rfl
    selectedShading := selectedShading
    selectedShading_eq := by rfl
    loss := loss
    loss_eq := by rfl
    loss_bound := hloss_bound'
    cardinalityFraction := cardinalityFraction
    cardinalityFraction_eq := by rfl
    cardinalityFraction_ne_zero := hcf_ne_zero
    cardinalityFraction_ne_top := hcf_ne_top
    selected_cardinality := hsel_card
    parameterConstant := parameterConstant
    parameterConstant_eq := by rfl
    state := state
    state_density_eq := by rfl
    state_parameter_eq := by rfl
  }, rfl⟩

end Kakeya.Assouad
