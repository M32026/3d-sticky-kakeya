import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterClusterFrostmanStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterClusterCoverPacking
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterClusterDyadic
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterClusterFrostmanCard
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterClusterAssemblyHelpers
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterClusterImbalance
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import Mathlib.Tactic

/-!
# Final assembly for tube_parameter_cluster_frostman

Wires together: cover → pruning → dyadic regularization → Frostman transfer.
-/

noncomputable section

open MeasureTheory Set Finset

namespace Kakeya.Assouad

/--
Final assembly: produce TubeParameterClusterFrostmanData from all inputs.
-/
theorem tube_parameter_cluster_frostman_assembly
    {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta)
    (hF_nonempty : F.Nonempty)
    (h_params : ∀ i : Fin F.card,
      |(tubeParams i).a| ≤ 12 ∧ |(tubeParams i).b| ≤ 12 ∧
      |(tubeParams i).c| ≤ 2 ∧ |(tubeParams i).d| ≤ 2)
    (C : ENNReal) (hC_one : 1 ≤ C) (hC_top : C ≠ ⊤)
    (hFrost : TubeParameterFrostmanBound F C)
    (w : ℝ) (hw_pos : 0 < w) (hw_delta : delta ≤ w) (hw100 : 100 * w ≤ 1)
    (Y : Kakeya.Streamlined.TubeShading F)
    (c0 : ℝ)
    (hwindow : ∀ i, Y.carrier i ≠ ∅ → |(tubeParams i).c - c0| ≤ w / 2)
    (lambda : ENNReal) (hlambda_zero : lambda ≠ 0) (hlambda_top : lambda ≠ ⊤)
    (hlambda_dense : Y.IsLambdaDense lambda) :
    Nonempty (TubeParameterClusterFrostmanData F Y C lambda w) := by
  classical
  -- Step 1: Maximal w-separated cover
  let cover : ParameterClusterCoverData F Y w :=
    parameter_cluster_cover Y h_params w hw_pos hw100

  -- Step 2: Prune low-mass clusters and bound imbalance (bacon's lemma)
  have h_main := cluster_imbalance_prune_clean
      hF_nonempty hC_one hC_top hw_pos hw_delta hw100 hwindow
      hlambda_zero hlambda_top hlambda_dense hFrost h_params cover
  rcases h_main with ⟨surviving, shading0, imbalance, base_mass, h_props⟩
  have hsurv_nonempty : surviving.Nonempty := h_props.1
  have hsurv_subset : surviving ⊆ cover.centers := h_props.2.1
  have hsub0 : IsSubshading shading0 Y := h_props.2.2.1
  have himb_pos : 0 < imbalance := h_props.2.2.2.1
  have himb_bound : (imbalance : ENNReal) ≤ 1000000 * C * lambda⁻¹ * Kakeya.realRpowENN w (-1) + 1 := h_props.2.2.2.2.1
  have hmass_retention0 : (2 : ENNReal)⁻¹ * Y.mass ≤ shading0.mass := h_props.2.2.2.2.2.1
  have hassign_mem0 : ∀ i, shading0.carrier i ≠ ∅ → cover.assign i ∈ surviving := h_props.2.2.2.2.2.2.1
  have hassign_converse0 : ∀ i, cover.assign i ∈ surviving → shading0.carrier i = Y.carrier i := h_props.2.2.2.2.2.2.2.1
  have hassign_close0 : ∀ i, shading0.carrier i ≠ ∅ → dist (tubeParameterPoint3 i) (cover.assign i) ≤ w := h_props.2.2.2.2.2.2.2.2.1
  have hbase_pos : 0 < base_mass := h_props.2.2.2.2.2.2.2.2.2.1
  have hbase_top : base_mass ≠ ⊤ := h_props.2.2.2.2.2.2.2.2.2.2.1
  have hmass_lower0 : ∀ p ∈ surviving, base_mass ≤ tubeParameterAssignedClusterMass shading0 cover.assign p := h_props.2.2.2.2.2.2.2.2.2.2.2.1
  have hmass_upper0 : ∀ p ∈ surviving, tubeParameterAssignedClusterMass shading0 cover.assign p ≤ (imbalance : ENNReal) * base_mass := h_props.2.2.2.2.2.2.2.2.2.2.2.2

  let assign := cover.assign

  -- Step 3: Dyadic regularization on surviving centers
  rcases dyadic_regularization surviving
      (tubeParameterAssignedClusterMass shading0 assign)
      base_mass imbalance
      hsurv_nonempty hbase_pos hbase_top himb_pos hmass_lower0 hmass_upper0
      (fun p hp => ne_top_of_le_ne_top
        (ENNReal.mul_ne_top (by simp) hbase_top)
        (hmass_upper0 p hp))
    with ⟨selected, clusterMass, hsel_nonempty, hsel_subset, hcm_bounds, hsel_mass⟩

  let points : DiscreteSet 3 := selected
  let L : ENNReal := (Nat.log 2 (2 * imbalance) + 1 : ENNReal)
  let regularizationLoss : ENNReal := 4 * L

  have hLoss_one : 1 ≤ regularizationLoss := regularizationLoss_one imbalance himb_pos
  have hLoss_top : regularizationLoss ≠ ⊤ := regularizationLoss_ne_top imbalance
  have hLoss_pos : 0 < regularizationLoss := lt_of_lt_of_le (by norm_num) hLoss_one

  -- Step 4: Restrict shading0 to selected centers
  let shading : Kakeya.Streamlined.TubeShading F :=
    restrictShadingToCenters shading0 assign points

  have hsub : IsSubshading shading Y := by
    intro i
    by_cases h : assign i ∈ points
    · have h1 : shading.carrier i = shading0.carrier i := by
        simp [shading, restrictShadingToCenters, h]
      rw [h1]
      exact hsub0 i
    · have h1 : shading.carrier i = ∅ := by
        simp [shading, restrictShadingToCenters, h]
      rw [h1]
      exact Set.empty_subset _

  have hwhole :
      ∀ i, shading.carrier i = Y.carrier i ∨
        shading.carrier i = ∅ := by
    intro i
    by_cases h : assign i ∈ points
    · have hsurv : assign i ∈ surviving :=
        hsel_subset h
      have h0 : shading0.carrier i = Y.carrier i :=
        hassign_converse0 i hsurv
      have h1 : shading.carrier i = shading0.carrier i := by
        simp [shading, restrictShadingToCenters, h]
      exact Or.inl (h1.trans h0)
    · exact Or.inr (by
        simp [shading, restrictShadingToCenters, h])

  have hassign_mem : ∀ i, shading.carrier i ≠ ∅ → assign i ∈ points := by
    intro i hi
    by_contra hne
    have h1 : shading.carrier i = ∅ := by
      simp [shading, restrictShadingToCenters, hne]
    rw [h1] at hi <;> tauto

  have hassign_close : ∀ i, shading.carrier i ≠ ∅ →
      dist (tubeParameterPoint3 i) (assign i) ≤ w := by
    intro i hi
    have h_in : assign i ∈ points := hassign_mem i hi
    have hY0 : shading0.carrier i ≠ ∅ := by
      have h1 : shading.carrier i = shading0.carrier i := by
        simp [shading, restrictShadingToCenters, h_in]
      rw [h1] at hi; exact hi
    exact hassign_close0 i hY0

  -- Cluster mass bounds transfer: for p ∈ points, shading and shading0 give same cluster mass
  have h_mass_eq : ∀ p ∈ points,
      tubeParameterAssignedClusterMass shading assign p =
      tubeParameterAssignedClusterMass shading0 assign p := by
    intro p hp
    simp only [tubeParameterAssignedClusterMass]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : assign i = p
    · have h_in : assign i ∈ points := by rw [h] <;> exact hp
      have h1 : shading.carrier i = shading0.carrier i := by
        simp [shading, restrictShadingToCenters, h_in]
      rw [if_pos h, if_pos h, h1]
    · rw [if_neg h, if_neg h]
  have hcm_lower : ∀ p ∈ points, clusterMass ≤ tubeParameterAssignedClusterMass shading assign p := by
    intro p hp
    have h1 : clusterMass ≤ tubeParameterAssignedClusterMass shading0 assign p :=
      (hcm_bounds p hp).1
    rw [h_mass_eq p hp]
    exact h1
  have hcm_upper : ∀ p ∈ points, tubeParameterAssignedClusterMass shading assign p ≤ 2 * clusterMass := by
    intro p hp
    have h1 : tubeParameterAssignedClusterMass shading0 assign p ≤ 2 * clusterMass :=
      (hcm_bounds p hp).2
    rw [h_mass_eq p hp]
    exact h1

  -- Mass retention: combine pruning retention with dyadic selection
  have h_shading0_mass_eq : shading0.mass = ∑ p ∈ surviving, tubeParameterAssignedClusterMass shading0 assign p := by
    simp only [Kakeya.Streamlined.Shading.mass, tubeParameterAssignedClusterMass]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : shading0.carrier i ≠ ∅
    · have hassign : assign i ∈ surviving := hassign_mem0 i hi
      have h_sum : ∑ p ∈ surviving, (if assign i = p then MeasureTheory.volume (shading0.carrier i) else 0) =
          MeasureTheory.volume (shading0.carrier i) := by
        have h_comm : ∀ (p : Point 3), (if assign i = p then MeasureTheory.volume (shading0.carrier i) else 0) =
            (if p = assign i then MeasureTheory.volume (shading0.carrier i) else 0) := by
          intro p
          by_cases h : p = assign i
          · rw [h] <;> simp
          · have h' : assign i ≠ p := by tauto
            rw [if_neg h', if_neg h] <;> rfl
        have h12 : ∑ p ∈ surviving, (if assign i = p then MeasureTheory.volume (shading0.carrier i) else 0) =
            ∑ p ∈ surviving, (if p = assign i then MeasureTheory.volume (shading0.carrier i) else 0) := by
          apply Finset.sum_congr rfl; intro p _; exact h_comm p
        rw [h12, Finset.sum_ite_eq']
        <;> simp [hassign]
      exact h_sum.symm
    · have h_empty : shading0.carrier i = ∅ := by tauto
      rw [h_empty] <;> simp
  have h_shading_mass_eq : shading.mass = ∑ p ∈ points, tubeParameterAssignedClusterMass shading assign p := by
    simp only [Kakeya.Streamlined.Shading.mass, tubeParameterAssignedClusterMass]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : shading.carrier i ≠ ∅
    · have hassign : assign i ∈ points := hassign_mem i hi
      have h_sum : ∑ p ∈ points, (if assign i = p then MeasureTheory.volume (shading.carrier i) else 0) =
          MeasureTheory.volume (shading.carrier i) := by
        have h_comm : ∀ (p : Point 3), (if assign i = p then MeasureTheory.volume (shading.carrier i) else 0) =
            (if p = assign i then MeasureTheory.volume (shading.carrier i) else 0) := by
          intro p
          by_cases h : p = assign i
          · rw [h] <;> simp
          · have h' : assign i ≠ p := by tauto
            rw [if_neg h', if_neg h] <;> rfl
        have h12 : ∑ p ∈ points, (if assign i = p then MeasureTheory.volume (shading.carrier i) else 0) =
            ∑ p ∈ points, (if p = assign i then MeasureTheory.volume (shading.carrier i) else 0) := by
          apply Finset.sum_congr rfl; intro p _; exact h_comm p
        rw [h12, Finset.sum_ite_eq']
        <;> simp [hassign]
      exact h_sum.symm
    · have h_empty : shading.carrier i = ∅ := by tauto
      rw [h_empty] <;> simp
  have hretention : (2 * regularizationLoss)⁻¹ * Y.mass ≤ shading.mass := by
    dsimp only [regularizationLoss]
    have h1 : (2 * (4 * L))⁻¹ * Y.mass = (8 : ENNReal)⁻¹ * Y.mass * L⁻¹ := by
      have h2 : (2 * (4 * L)) = (8 : ENNReal) * L := by
        calc
          (2 * (4 * L)) = (2 * 4 : ENNReal) * L := by rw [mul_assoc]
          _ = (8 : ENNReal) * L := by norm_num
      rw [h2]
      have h3 : ((8 : ENNReal) * L)⁻¹ = (8 : ENNReal)⁻¹ * L⁻¹ := by
        rw [ENNReal.mul_inv] <;> simp
      rw [h3]
      <;> simp only [mul_assoc, mul_left_comm, mul_comm]
    rw [h1]
    have h_survive' : (2 : ENNReal)⁻¹ * Y.mass ≤ shading0.mass := hmass_retention0
    have h_dyadic : (∑ p ∈ surviving, tubeParameterAssignedClusterMass shading0 assign p) * L⁻¹ ≤
        ∑ p ∈ points, tubeParameterAssignedClusterMass shading0 assign p := by
      simpa [div_eq_mul_inv] using hsel_mass
    calc
      (8 : ENNReal)⁻¹ * Y.mass * L⁻¹
        ≤ (2 : ENNReal)⁻¹ * Y.mass * L⁻¹ := by gcongr <;> norm_num
      _ ≤ shading0.mass * L⁻¹ := by gcongr
      _ = (∑ p ∈ surviving, tubeParameterAssignedClusterMass shading0 assign p) * L⁻¹ := by
        rw [h_shading0_mass_eq]
      _ ≤ ∑ p ∈ points, tubeParameterAssignedClusterMass shading0 assign p := h_dyadic
      _ = ∑ p ∈ points, tubeParameterAssignedClusterMass shading assign p := by
        apply Finset.sum_congr rfl
        intro p hp
        exact (h_mass_eq p hp).symm
      _ = shading.mass := h_shading_mass_eq.symm

  have hclusterMass_pos : 0 < clusterMass := by
    rcases hsel_nonempty with ⟨p, hp⟩
    have h1 : clusterMass ≤ tubeParameterAssignedClusterMass shading0 assign p :=
      (hcm_bounds p hp).1
    have h2 : 0 < tubeParameterAssignedClusterMass shading0 assign p :=
      hbase_pos.trans_le (hmass_lower0 p (hsel_subset hp))
    have h3 : tubeParameterAssignedClusterMass shading0 assign p ≤ 2 * clusterMass :=
      (hcm_bounds p hp).2
    have h4 : 0 < 2 * clusterMass := h2.trans_le h3
    have h5 : 0 < clusterMass := by
      by_contra h6
      have h7 : clusterMass = 0 := by simpa using h6
      rw [h7] at h4 <;> simp at h4 <;> exact h4
    exact h5

  have hclusterMass_top : clusterMass ≠ ⊤ := by
    rcases hsel_nonempty with ⟨p, hp⟩
    have h1 : clusterMass ≤ tubeParameterAssignedClusterMass shading0 assign p :=
      (hcm_bounds p hp).1
    have h2 : tubeParameterAssignedClusterMass shading0 assign p ≠ ⊤ :=
      ne_top_of_le_ne_top
        (ENNReal.mul_ne_top (by simp) hbase_top)
        (hmass_upper0 p (hsel_subset hp))
    exact ne_top_of_le_ne_top h2 h1

  -- Window transfer
  have hwindow' : ∀ i, shading.carrier i ≠ ∅ → |(tubeParams i).c - c0| ≤ w / 2 := by
    intro i hi
    have hY0 : shading0.carrier i ≠ ∅ := by
      have h_in : assign i ∈ points := hassign_mem i hi
      have h1 : shading.carrier i = shading0.carrier i := by
        simp [shading, restrictShadingToCenters, h_in]
      rw [h1] at hi; exact hi
    have hY : Y.carrier i ≠ ∅ := by
      have h_sub : shading0.carrier i ⊆ Y.carrier i := hsub0 i
      intro h_empty
      have h_sub2 : shading0.carrier i ⊆ ∅ := by
        rw [h_empty] at h_sub <;> exact h_sub
      have h_eq : shading0.carrier i = ∅ := Set.Subset.antisymm h_sub2 (Set.empty_subset _)
      exact hY0 h_eq
    exact hwindow i hY

  -- lambda ≤ 1 from density
  have hdelta_pos : 0 < delta := delta_pos_from_frostman hF_nonempty hFrost
  have hdelta_le_one : delta ≤ 1 := by linarith [hw_delta, hw100]
  have hlambda_le_one : lambda ≤ 1 := by
    have hY_le_F : Y.mass ≤ F.toBodyFamily.mass := by
      simp only [Kakeya.Streamlined.Shading.mass]
      apply Finset.sum_le_sum
      intro i _
      exact MeasureTheory.measure_mono (Y.subset_body i)
    have hFmass_pos' : 0 < F.toBodyFamily.mass := by
      have h1 : F.toBodyFamily.mass = F.enncard * Kakeya.deltaTubeVolume delta :=
        tubeFamily_mass_eq_nominal F
      rw [h1]
      have h2 : 0 < F.enncard := by
        have h_card : 0 < F.card :=
          Nat.zero_lt_of_lt hF_nonempty
        simpa [Kakeya.Streamlined.TubeFamily.enncard] using h_card
      have h3 : 0 < Kakeya.deltaTubeVolume delta := deltaTubeVolume_pos hdelta_pos hdelta_le_one
      exact ENNReal.mul_pos h2.ne' h3.ne'
    have hFmass_ne_zero : F.toBodyFamily.mass ≠ 0 := hFmass_pos'.ne'
    have hFmass_ne_top : F.toBodyFamily.mass ≠ ⊤ := by
      have h1 : F.toBodyFamily.mass = F.enncard * Kakeya.deltaTubeVolume delta :=
        tubeFamily_mass_eq_nominal F
      rw [h1]
      apply ENNReal.mul_ne_top
      · simp [Kakeya.Streamlined.TubeFamily.enncard] <;> exact ENNReal.natCast_ne_top _
      · exact (tube_volume_scaling.2.1 delta hdelta_pos hdelta_le_one).2
    have h : lambda * F.toBodyFamily.mass ≤ F.toBodyFamily.mass :=
      le_trans hlambda_dense hY_le_F
    have h' : lambda * F.toBodyFamily.mass ≤ (1 : ENNReal) * F.toBodyFamily.mass := by
      simpa [one_mul] using h
    exact (ENNReal.mul_le_mul_iff_left hFmass_ne_zero hFmass_ne_top).mp h'

  have hfrostman_const_one : 1 ≤ tubeParameterClusterFrostmanConstant C regularizationLoss lambda :=
    clusterFrostmanConstant_one C regularizationLoss lambda hC_one hLoss_one hlambda_le_one
  have hfrostman_const_top : tubeParameterClusterFrostmanConstant C regularizationLoss lambda ≠ ⊤ :=
    clusterFrostmanConstant_ne_top C regularizationLoss lambda hC_top hLoss_top hlambda_zero

  -- Step 5: Frostman transfer and cardinality lower bound
  have h_frostman_card := cluster_frostman_and_card
    (F := F) (Y := Y) (shading := shading) (C := C) (lambda := lambda)
    (regularizationLoss := regularizationLoss) (clusterMass := clusterMass) (w := w) (c0 := c0)
    (points := points) (assign := assign)
    (hF_nonempty := hF_nonempty) (hδ_le_w := hw_delta)
    (hC := hC_one) (hC_top := hC_top)
    (hlambda_ne_zero := hlambda_zero) (hlambda_ne_top := hlambda_top)
    (hLoss_one := hLoss_one) (hLoss_top := hLoss_top)
    (hw := hw_pos) (hw100 := hw100)
    (hFrost := hFrost) (hwindow := hwindow') (hdense := hlambda_dense)
    (hsub := hsub) (hretention := hretention)
    (hpoints_nonempty := hsel_nonempty)
    (hassign_mem := hassign_mem) (hassign_close := hassign_close)
    (hcm_pos := hclusterMass_pos) (hcm_top := hclusterMass_top)
    (hcm_lower := hcm_lower) (hcm_upper := hcm_upper)

  have hpoints_frostman := h_frostman_card.1
  have hpoints_card_lower := h_frostman_card.2

  -- Point source: every selected center comes from an active tube
  have hpoint_source : ∀ p ∈ points, ∃ i : Fin F.card,
      shading.carrier i ≠ ∅ ∧
        assign i = p ∧
        tubeParameterPoint3 i = p := by
    intro p hp
    have hp_surv : p ∈ surviving := hsel_subset hp
    have hp_center : p ∈ cover.centers := hsurv_subset hp_surv
    have h1 : p ∈ cover.active.image tubeParameterPoint3 := cover.centers_subset_image hp_center
    rcases Finset.mem_image.mp h1 with ⟨i, hi_active, hpt⟩
    have hY : Y.carrier i ≠ ∅ := (cover.active_positiveMass i).mp hi_active
    have h2 : assign i = tubeParameterPoint3 i := cover.assign_self i hi_active (hpt ▸ hp_center)
    have h3 : assign i = p := by rw [h2, hpt]
    have h4 : assign i ∈ surviving := by rw [h3] <;> exact hp_surv
    have h5 : shading0.carrier i = Y.carrier i := hassign_converse0 i h4
    have h6 : assign i ∈ points := by rw [h3] <;> exact hp
    have h7 : shading.carrier i = shading0.carrier i := by
      simp [shading, restrictShadingToCenters, h6]
    refine ⟨i, ?_, h3, hpt⟩
    rw [h7, h5] <;> exact hY

  have hpoints_in_unitBall : points.IsInUnitBall := by
    intro p hp
    have h1 : p ∈ surviving := hsel_subset hp
    have h2 : p ∈ cover.centers := hsurv_subset h1
    exact cover.centers_in_unitBall p h2

  have hpoints_separated : points.IsDeltaSeparated w := by
    intro p hp q hq hne
    have hp' : p ∈ cover.centers := hsurv_subset (hsel_subset hp)
    have hq' : q ∈ cover.centers := hsurv_subset (hsel_subset hq)
    exact cover.centers_separated hp' hq' hne

  have hpoints_card_upper : points.enncard ≤ 100000 * Kakeya.realRpowENN w (-3) := by
    have h1 : points ⊆ cover.centers := by
      intro p hp
      exact hsurv_subset (hsel_subset hp)
    have h2 : (points.card : ENNReal) ≤ (cover.centers.card : ENNReal) := by
      exact_mod_cast Finset.card_le_card h1
    have h3 : points.enncard ≤ cover.centers.enncard := by
      simpa [DiscreteSet.enncard] using h2
    exact h3.trans cover.centers_card_upper

  exact ⟨{
    regularizationLoss := regularizationLoss
    regularizationLoss_one := hLoss_one
    regularizationLoss_ne_top := hLoss_top
    imbalance := imbalance
    imbalance_pos := himb_pos
    imbalance_bound := himb_bound
    regularizationLoss_eq := by rfl
    shading := shading
    subshading := hsub
    whole_tube := hwhole
    mass_retention := hretention
    points := points
    points_nonempty := hsel_nonempty
    points_in_unitBall := hpoints_in_unitBall
    points_separated := hpoints_separated
    points_card_upper := hpoints_card_upper
    frostmanConstant_one := hfrostman_const_one
    frostmanConstant_ne_top := hfrostman_const_top
    points_frostman := hpoints_frostman
    points_card_lower := hpoints_card_lower
    assign := assign
    assign_mem := hassign_mem
    assign_close := hassign_close
    clusterMass := clusterMass
    clusterMass_pos := hclusterMass_pos
    clusterMass_ne_top := hclusterMass_top
    cluster_mass_lower := hcm_lower
    cluster_mass_upper := hcm_upper
    point_source := hpoint_source
  }⟩

end Kakeya.Assouad
