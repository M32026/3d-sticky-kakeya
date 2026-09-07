import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterClusterFrostmanStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectionFrostmanHelpers
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterClusterCoverPacking
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterClusterAssemblyHelpers
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling

/-!
# Cluster mass weighting and imbalance bound (clean version)

Given a cluster cover, Frostman control, c-window, and lambda-density,
prune low-mass clusters and produce an imbalance bound for surviving clusters.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Upper bound on the mass of one cluster using the four-parameter Frostman bound.
-/
lemma cluster_mass_frostman_upper_clean
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F} {C : ENNReal}
    (hFrost : TubeParameterFrostmanBound F C)
    {w : ℝ} (hw_pos : 0 < w) (hw_delta : delta ≤ w) (hw100 : 100 * w ≤ 1)
    (c0 : ℝ)
    (hwindow : ∀ i, Y.carrier i ≠ ∅ → |(tubeParams i).c - c0| ≤ w / 2)
    (assign : Fin F.card → Point 3)
    (hassign_close : ∀ i, Y.carrier i ≠ ∅ → dist (tubeParameterPoint3 i) (assign i) ≤ w)
    (p : Point 3)
    (h_witness : ∃ i, Y.carrier i ≠ ∅ ∧ assign i = p) :
    tubeParameterAssignedClusterMass Y assign p ≤
      C * Kakeya.realRpowENN (48 * w) 2 * F.toBodyFamily.mass := by
  classical
  rcases h_witness with ⟨i0, hi0_nonempty, h_i0_eq⟩
  let frostSet := Finset.univ.filter fun i : Fin F.card =>
    |(tubeParams i).a - (tubeParams i0).a| ≤ 48 * w ∧
    |(tubeParams i).b - (tubeParams i0).b| ≤ 48 * w ∧
    |(tubeParams i).c - (tubeParams i0).c| ≤ 48 * w ∧
    |(tubeParams i).d - (tubeParams i0).d| ≤ 48 * w
  let activeAtP := Finset.univ.filter fun i : Fin F.card =>
    assign i = p ∧ Y.carrier i ≠ ∅
  have h_subset : activeAtP ⊆ frostSet := by
    intro i hi
    have h_i_assign : assign i = p := (Finset.mem_filter.mp hi).2.1
    have h_i_nonempty : Y.carrier i ≠ ∅ := (Finset.mem_filter.mp hi).2.2
    have h_dist_i : dist (tubeParameterPoint3 i) p ≤ w := by
      rw [←h_i_assign]
      exact hassign_close i h_i_nonempty
    have h_dist_i0 : dist (tubeParameterPoint3 i0) p ≤ w := by
      rw [←h_i0_eq]
      exact hassign_close i0 hi0_nonempty
    have h_dist : dist (tubeParameterPoint3 i) (tubeParameterPoint3 i0) ≤ 2 * w := by
      calc
        dist (tubeParameterPoint3 i) (tubeParameterPoint3 i0)
          ≤ dist (tubeParameterPoint3 i) p + dist p (tubeParameterPoint3 i0) := dist_triangle _ _ _
        _ ≤ dist (tubeParameterPoint3 i) p + dist (tubeParameterPoint3 i0) p := by
          rw [dist_comm p (tubeParameterPoint3 i0)]
        _ ≤ w + w := by gcongr
        _ = 2 * w := by ring
    have h_params := param_diff_from_point_dist i i0 (2 * w) h_dist
    have h_c : |(tubeParams i).c - (tubeParams i0).c| ≤ w := by
      have h_ci : |(tubeParams i).c - c0| ≤ w / 2 := hwindow i h_i_nonempty
      have h_ci0 : |(tubeParams i0).c - c0| ≤ w / 2 := hwindow i0 hi0_nonempty
      have h_tri : |(tubeParams i).c - (tubeParams i0).c| ≤
          |(tubeParams i).c - c0| + |c0 - (tubeParams i0).c| := abs_sub_le _ _ _
      rw [show |c0 - (tubeParams i0).c| = |(tubeParams i0).c - c0| by rw [abs_sub_comm]] at h_tri
      linarith
    have ha : |(tubeParams i).a - (tubeParams i0).a| ≤ 48 * w := by
      have h := h_params.1
      ring_nf at h ⊢; exact h
    have hb : |(tubeParams i).b - (tubeParams i0).b| ≤ 48 * w := by
      have h := h_params.2.1
      ring_nf at h ⊢; exact h
    have hd8 : |(tubeParams i).d - (tubeParams i0).d| ≤ 8 * w := by
      have h := h_params.2.2
      ring_nf at h ⊢; exact h
    have hd : |(tubeParams i).d - (tubeParams i0).d| ≤ 48 * w := by
      calc
        |(tubeParams i).d - (tubeParams i0).d| ≤ 8 * w := hd8
        _ ≤ 48 * w := by linarith
    have hc : |(tubeParams i).c - (tubeParams i0).c| ≤ 48 * w := by
      calc
        |(tubeParams i).c - (tubeParams i0).c| ≤ w := h_c
        _ ≤ 48 * w := by linarith
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, ha, hb, hc, hd⟩
  have h48w_one : 48 * w ≤ 1 := by linarith
  have hdelta_48w : delta ≤ 48 * w := by linarith
  have h_frost : (frostSet.card : ENNReal) ≤
      C * Kakeya.realRpowENN (48 * w) 2 * F.enncard :=
    hFrost (48 * w) hdelta_48w h48w_one i0
  have h_count : (activeAtP.card : ENNReal) ≤ (frostSet.card : ENNReal) := by
    exact_mod_cast Finset.card_le_card h_subset
  have h_pointwise : ∀ i : Fin F.card,
      (if assign i = p then MeasureTheory.volume (Y.carrier i) else 0) ≤
      (if assign i = p ∧ Y.carrier i ≠ ∅ then Kakeya.deltaTubeVolume delta else 0) := by
    intro i
    by_cases h : assign i = p
    · rw [if_pos h]
      by_cases h2 : Y.carrier i ≠ ∅
      · rw [if_pos ⟨h, h2⟩]
        have h3 : Y.carrier i ⊆ (F.tube i).carrier := Y.subset_body i
        have h4 : MeasureTheory.volume (Y.carrier i) ≤ MeasureTheory.volume ((F.tube i).carrier) :=
          MeasureTheory.measure_mono h3
        have h5 : MeasureTheory.volume ((F.tube i).carrier) = Kakeya.deltaTubeVolume delta :=
          tube_volume_scaling.1 delta (F.tube i)
        rw [h5] at h4
        exact h4
      · rw [if_neg (by tauto)]
        have h_empty : Y.carrier i = ∅ := by tauto
        rw [h_empty]; simp
    · rw [if_neg h, if_neg (by tauto)]
  have h_sum1 : tubeParameterAssignedClusterMass Y assign p ≤
      ∑ i : Fin F.card, (if assign i = p ∧ Y.carrier i ≠ ∅ then Kakeya.deltaTubeVolume delta else 0) := by
    simp only [tubeParameterAssignedClusterMass]
    exact Finset.sum_le_sum (fun i _ => h_pointwise i)
  have h_sum2 : ∑ i : Fin F.card, (if assign i = p ∧ Y.carrier i ≠ ∅ then Kakeya.deltaTubeVolume delta else 0) =
      (activeAtP.card : ENNReal) * Kakeya.deltaTubeVolume delta := by
    have h : ∑ i : Fin F.card, (if assign i = p ∧ Y.carrier i ≠ ∅ then Kakeya.deltaTubeVolume delta else 0) =
        ∑ i ∈ activeAtP, Kakeya.deltaTubeVolume delta := by
      rw [Finset.sum_ite]; simp [activeAtP]
    rw [h]
    simp [Finset.sum_const]
  have h_F_mass : F.toBodyFamily.mass = F.enncard * Kakeya.deltaTubeVolume delta :=
    tubeFamily_mass_eq_nominal F
  calc
    tubeParameterAssignedClusterMass Y assign p
      ≤ (activeAtP.card : ENNReal) * Kakeya.deltaTubeVolume delta := by
        rw [h_sum2] at h_sum1; exact h_sum1
    _ ≤ (frostSet.card : ENNReal) * Kakeya.deltaTubeVolume delta := by gcongr
    _ ≤ (C * Kakeya.realRpowENN (48 * w) 2 * F.enncard) * Kakeya.deltaTubeVolume delta := by gcongr
    _ = C * Kakeya.realRpowENN (48 * w) 2 * F.toBodyFamily.mass := by
      rw [h_F_mass]; ring

/--
Sum of cluster masses over all centers equals total shaded mass.
-/
lemma sum_cluster_mass_eq_total_clean
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F} {w : ℝ}
    (cover : ParameterClusterCoverData F Y w)
    (assign : Fin F.card → Point 3)
    (hassign_mem : ∀ i, i ∈ cover.active → assign i ∈ cover.centers) :
    ∑ p ∈ cover.centers, tubeParameterAssignedClusterMass Y assign p = Y.mass := by
  classical
  simp only [tubeParameterAssignedClusterMass, Kakeya.Streamlined.Shading.mass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ cover.active
  · have hassign : assign i ∈ cover.centers := hassign_mem i hi
    let f : Point 3 → ENNReal := fun p =>
      if assign i = p then MeasureTheory.volume (Y.carrier i) else 0
    have h_sum : ∑ p ∈ cover.centers, f p = f (assign i) :=
      Finset.sum_eq_single_of_mem (assign i) hassign
        (fun p _ hne => by simp [f, hne.symm])
    have h_fa : f (assign i) = MeasureTheory.volume (Y.carrier i) := by simp [f]
    have h : ∑ p ∈ cover.centers, (if assign i = p then MeasureTheory.volume (Y.carrier i) else 0) =
        MeasureTheory.volume (Y.carrier i) := by
      exact h_sum.trans h_fa
    exact h
  · have h_empty : Y.carrier i = ∅ := by
      have h : ¬(Y.carrier i ≠ ∅) := (cover.active_positiveMass i).not.mp hi
      simpa using h
    rw [h_empty]; simp

/--
Prune centers below half the average mass and prove mass retention.
-/
lemma prune_half_average_retention_clean
    {centers : DiscreteSet 3} {M : Point 3 → ENNReal} {T : ENNReal}
    (h_total : ∑ p ∈ centers, M p = T)
    (hN_ne_zero : centers.enncard ≠ 0)
    (hN_ne_top : centers.enncard ≠ ⊤)
    (hT_ne_top : T ≠ ⊤) :
    let A := T * centers.enncard⁻¹
    let surviving := centers.filter (fun p => (2 : ENNReal)⁻¹ * A ≤ M p)
    (2 : ENNReal)⁻¹ * T ≤ ∑ p ∈ surviving, M p := by
  classical
  let A := T * centers.enncard⁻¹
  let surviving := centers.filter (fun p => (2 : ENNReal)⁻¹ * A ≤ M p)
  let discarded := centers.filter (fun p => ¬((2 : ENNReal)⁻¹ * A ≤ M p))
  have h_partition : centers = surviving ∪ discarded := by
    ext p
    simp only [surviving, discarded, Finset.mem_union, Finset.mem_filter]; tauto
  have h_disj : Disjoint surviving discarded := by
    simp [surviving, discarded, Finset.disjoint_left]; tauto
  have h_sum : ∑ p ∈ centers, M p = ∑ p ∈ surviving, M p + ∑ p ∈ discarded, M p := by
    rw [h_partition, Finset.sum_union h_disj]
  have h_discarded_le : ∀ p ∈ discarded, M p ≤ (2 : ENNReal)⁻¹ * A := by
    intro p hp
    have h9 : ¬((2 : ENNReal)⁻¹ * A ≤ M p) := (Finset.mem_filter.mp hp).2
    exact not_le.mp h9 |>.le
  have h_sum_discarded : ∑ p ∈ discarded, (2 : ENNReal)⁻¹ * A =
      (discarded.card : ENNReal) * ((2 : ENNReal)⁻¹ * A) := by
    rw [Finset.sum_const]; simp
  have h_discarded_mass : ∑ p ∈ discarded, M p ≤ (2 : ENNReal)⁻¹ * T := by
    calc
      ∑ p ∈ discarded, M p
        ≤ ∑ p ∈ discarded, (2 : ENNReal)⁻¹ * A := Finset.sum_le_sum h_discarded_le
      _ = (discarded.card : ENNReal) * ((2 : ENNReal)⁻¹ * A) := h_sum_discarded
      _ ≤ (centers.card : ENNReal) * ((2 : ENNReal)⁻¹ * A) := by
        have h_card_le : discarded.card ≤ centers.card := Finset.card_le_card (Finset.filter_subset _ _)
        exact mul_le_mul_of_nonneg_right (mod_cast h_card_le) (by positivity)
      _ = (2 : ENNReal)⁻¹ * T := by
        dsimp only [A]
        have h_card : (centers.card : ENNReal) = centers.enncard := by
          simp [DiscreteSet.enncard]
        rw [h_card]
        have h4 : centers.enncard * ((2 : ENNReal)⁻¹ * (T * centers.enncard⁻¹)) =
            (2 : ENNReal)⁻¹ * T := by
          have h5 : centers.enncard * ((2 : ENNReal)⁻¹ * (T * centers.enncard⁻¹)) =
              (2 : ENNReal)⁻¹ * (centers.enncard * (T * centers.enncard⁻¹)) := by ring
          rw [h5]
          have h6 : centers.enncard * (T * centers.enncard⁻¹) = T := by
            calc
              centers.enncard * (T * centers.enncard⁻¹)
                = (centers.enncard * centers.enncard⁻¹) * T := by ring
              _ = 1 * T := by rw [ENNReal.mul_inv_cancel hN_ne_zero hN_ne_top]
              _ = T := by simp
          rw [h6]
        exact h4
  have hT : T = ∑ p ∈ surviving, M p + ∑ p ∈ discarded, M p := by
    rw [←h_sum, h_total]
  have h_main : T ≤ ∑ p ∈ surviving, M p + (2 : ENNReal)⁻¹ * T := by
    calc
      T = ∑ p ∈ surviving, M p + ∑ p ∈ discarded, M p := hT
      _ ≤ ∑ p ∈ surviving, M p + (2 : ENNReal)⁻¹ * T :=
        add_le_add_right h_discarded_mass _
  have h_halfT_ne_top : (2 : ENNReal)⁻¹ * T ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hT_ne_top
  have h_double : (2 : ENNReal)⁻¹ * T + (2 : ENNReal)⁻¹ * T = T := by
    have h1 : (2 : ENNReal)⁻¹ * T + (2 : ENNReal)⁻¹ * T =
        (2 : ENNReal) * ((2 : ENNReal)⁻¹ * T) := by
      simp [two_mul]
    rw [h1]
    have h2 : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 := by
      rw [ENNReal.mul_inv_cancel] <;> norm_num
    rw [←mul_assoc, h2, one_mul]
  have h6 : (2 : ENNReal)⁻¹ * T + (2 : ENNReal)⁻¹ * T ≤
      ∑ p ∈ surviving, M p + (2 : ENNReal)⁻¹ * T := by
    rw [h_double]; exact h_main
  exact (ENNReal.add_le_add_iff_right h_halfT_ne_top).mp h6

/--
Helper: derive `0 < delta` from Frostman bound at `r = 0`.
-/
lemma delta_pos_from_frostman
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (hF_nonempty : F.Nonempty)
    {C : ENNReal} (hFrost : TubeParameterFrostmanBound F C) :
    0 < delta := by
  classical
  by_contra h
  have h' : delta ≤ 0 := by linarith
  let i0 : Fin F.card := ⟨0, hF_nonempty⟩
  have hFrost0 := hFrost 0 h' (by norm_num) i0
  have h_rpow : Kakeya.realRpowENN (0 : ℝ) 2 = 0 := by
    simp [Kakeya.realRpowENN]
    <;> norm_num
  rw [h_rpow] at hFrost0
  have h_in : i0 ∈ Finset.univ.filter (fun i : Fin F.card =>
      |(tubeParams i).a - (tubeParams i0).a| ≤ 0 ∧
      |(tubeParams i).b - (tubeParams i0).b| ≤ 0 ∧
      |(tubeParams i).c - (tubeParams i0).c| ≤ 0 ∧
      |(tubeParams i).d - (tubeParams i0).d| ≤ 0) := by
    simp
    <;> exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have h_card_pos : 0 < (Finset.univ.filter (fun i : Fin F.card =>
      |(tubeParams i).a - (tubeParams i0).a| ≤ 0 ∧
      |(tubeParams i).b - (tubeParams i0).b| ≤ 0 ∧
      |(tubeParams i).c - (tubeParams i0).c| ≤ 0 ∧
      |(tubeParams i).d - (tubeParams i0).d| ≤ 0)).card :=
    Finset.card_pos.mpr ⟨i0, h_in⟩
  have h_contra : (Finset.univ.filter (fun i : Fin F.card =>
      |(tubeParams i).a - (tubeParams i0).a| ≤ 0 ∧
      |(tubeParams i).b - (tubeParams i0).b| ≤ 0 ∧
      |(tubeParams i).c - (tubeParams i0).c| ≤ 0 ∧
      |(tubeParams i).d - (tubeParams i0).d| ≤ 0)).card = 0 := by
    simpa using hFrost0
  rw [h_contra] at h_card_pos
  <;> simp at h_card_pos

/--
Helper: `0 < deltaTubeVolume delta` when `0 < delta`.
-/
lemma deltaTubeVolume_pos {delta : ℝ} (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1) :
    0 < Kakeya.deltaTubeVolume delta := by
  exact (tube_volume_scaling.2.1 delta hdelta hdelta_le_one).1

/--
ENNReal ratio helper: `2304 * C * w² * λ⁻¹ * T ≤ X * (T * N⁻¹ / 2)`
when `N ≤ 64 * w⁻³` and `X = 294912 * C * λ⁻¹ * w⁻¹`.
-/
lemma cluster_ratio_helper
    {C lambda T N : ENNReal} {w : ℝ}
    (hw_pos : 0 < w)
    (hN : N ≤ 64 * Kakeya.realRpowENN w (-3)) :
    2304 * C * Kakeya.realRpowENN w 2 * lambda⁻¹ * T ≤
    (294912 * C * lambda⁻¹ * Kakeya.realRpowENN w (-1)) *
      ((2 : ENNReal)⁻¹ * T * N⁻¹) := by
  have h_w3_pos : 0 < Kakeya.realRpowENN w (-3) := by
    simp [Kakeya.realRpowENN, hw_pos.ne'] <;> positivity
  have h_w3_top : Kakeya.realRpowENN w (-3) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_w_mul : Kakeya.realRpowENN w (-1) * Kakeya.realRpowENN w 3 = Kakeya.realRpowENN w 2 := by
    have h := realRpowENN_add hw_pos (-1 : ℝ) (3 : ℝ)
    have h_sum : (-1 : ℝ) + (3 : ℝ) = (2 : ℝ) := by norm_num
    rw [h_sum] at h; exact h.symm
  have h_w3_mul : Kakeya.realRpowENN w (-3) * Kakeya.realRpowENN w 3 = 1 := by
    have h := realRpowENN_add hw_pos (-3 : ℝ) (3 : ℝ)
    have h_sum : (-3 : ℝ) + (3 : ℝ) = (0 : ℝ) := by norm_num
    rw [h_sum] at h
    have h0 : Kakeya.realRpowENN w 0 = 1 := by simp [Kakeya.realRpowENN] <;> norm_num
    rw [h0] at h; exact h.symm
  have h_w3_inv : (Kakeya.realRpowENN w (-3))⁻¹ = Kakeya.realRpowENN w 3 := by
    have h_pos : Kakeya.realRpowENN w (-3) ≠ 0 := h_w3_pos.ne'
    have h_top : Kakeya.realRpowENN w (-3) ≠ ⊤ := h_w3_top
    have h1 : (Kakeya.realRpowENN w (-3))⁻¹ * Kakeya.realRpowENN w (-3) = 1 :=
      ENNReal.inv_mul_cancel h_pos h_top
    calc
      (Kakeya.realRpowENN w (-3))⁻¹
        = (Kakeya.realRpowENN w (-3))⁻¹ * 1 := by simp
      _ = (Kakeya.realRpowENN w (-3))⁻¹ * (Kakeya.realRpowENN w (-3) * Kakeya.realRpowENN w 3) := by rw [h_w3_mul]
      _ = ((Kakeya.realRpowENN w (-3))⁻¹ * Kakeya.realRpowENN w (-3)) * Kakeya.realRpowENN w 3 := by ring
      _ = 1 * Kakeya.realRpowENN w 3 := by rw [h1]
      _ = Kakeya.realRpowENN w 3 := by simp
  have h64_ne_zero : (64 : ENNReal) ≠ 0 := by norm_num
  have h64_ne_top : (64 : ENNReal) ≠ ⊤ := by norm_num
  have h64_inv : ((64 : ENNReal) * Kakeya.realRpowENN w (-3))⁻¹ =
      (64 : ENNReal)⁻¹ * Kakeya.realRpowENN w 3 := by
    have h : ((64 : ENNReal) * Kakeya.realRpowENN w (-3))⁻¹ =
        (64 : ENNReal)⁻¹ * (Kakeya.realRpowENN w (-3))⁻¹ := by
      apply ENNReal.mul_inv
      · exact Or.inl h64_ne_zero
      · exact Or.inl h64_ne_top
    rw [h, h_w3_inv]
  have hN_inv : (64 : ENNReal)⁻¹ * Kakeya.realRpowENN w 3 ≤ N⁻¹ := by
    have h1 : ((64 : ENNReal) * Kakeya.realRpowENN w (-3))⁻¹ ≤ N⁻¹ :=
      ENNReal.inv_le_inv' hN
    rw [h64_inv] at h1
    exact h1
  let A := (294912 : ENNReal) * C * lambda⁻¹ * Kakeya.realRpowENN w (-1)
  let B := (2 : ENNReal)⁻¹ * T
  let C64 := (64 : ENNReal)⁻¹ * Kakeya.realRpowENN w 3
  have hN' : B * C64 ≤ B * N⁻¹ :=
    mul_le_mul_of_nonneg_left hN_inv (by positivity)
  have h2 : A * (B * C64) ≤ A * (B * N⁻¹) :=
    mul_le_mul_of_nonneg_left hN' (by positivity)
  have h3 : A * (B * C64) = 2304 * C * Kakeya.realRpowENN w 2 * lambda⁻¹ * T := by
    have h4 : (294912 : ENNReal) * (2 : ENNReal)⁻¹ * (64 : ENNReal)⁻¹ = (2304 : ENNReal) := by
      have h_div2 : (294912 : ENNReal) * (2 : ENNReal)⁻¹ = (147456 : ENNReal) := by
        have h_eq : (294912 : ENNReal) = (147456 : ENNReal) * (2 : ENNReal) := by norm_num
        rw [h_eq, mul_assoc]
        have h_cancel : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 :=
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
        rw [h_cancel, mul_one]
      have h_div64 : (147456 : ENNReal) * (64 : ENNReal)⁻¹ = (2304 : ENNReal) := by
        have h_eq : (147456 : ENNReal) = (2304 : ENNReal) * (64 : ENNReal) := by norm_num
        rw [h_eq, mul_assoc]
        have h_cancel : (64 : ENNReal) * (64 : ENNReal)⁻¹ = 1 :=
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
        rw [h_cancel, mul_one]
      calc
        (294912 : ENNReal) * (2 : ENNReal)⁻¹ * (64 : ENNReal)⁻¹
          = ((294912 : ENNReal) * (2 : ENNReal)⁻¹) * (64 : ENNReal)⁻¹ := by
            simp only [mul_assoc]
        _ = (147456 : ENNReal) * (64 : ENNReal)⁻¹ := by rw [h_div2]
        _ = (2304 : ENNReal) := h_div64
    dsimp only [A, B, C64]
    calc
      (294912 : ENNReal) * C * lambda⁻¹ * Kakeya.realRpowENN w (-1) *
          (((2 : ENNReal)⁻¹ * T) * ((64 : ENNReal)⁻¹ * Kakeya.realRpowENN w 3))
        = ((294912 : ENNReal) * (2 : ENNReal)⁻¹ * (64 : ENNReal)⁻¹) * C * lambda⁻¹ *
            (Kakeya.realRpowENN w (-1) * Kakeya.realRpowENN w 3) * T := by
          simp only [mul_assoc, mul_left_comm, mul_comm] <;> norm_num
      _ = (2304 : ENNReal) * C * lambda⁻¹ * (Kakeya.realRpowENN w (-1) * Kakeya.realRpowENN w 3) * T := by rw [h4]
      _ = (2304 : ENNReal) * C * lambda⁻¹ * Kakeya.realRpowENN w 2 * T := by rw [h_w_mul]
      _ = 2304 * C * Kakeya.realRpowENN w 2 * lambda⁻¹ * T := by
          simp only [mul_assoc, mul_left_comm, mul_comm]
  have h4 : 2304 * C * Kakeya.realRpowENN w 2 * lambda⁻¹ * T ≤ A * (B * N⁻¹) :=
    h3 ▸ h2
  exact h4

/--
Main cluster imbalance pruning lemma.

Produces surviving centers, restricted shading, imbalance, and base_mass
with all required properties.
-/
lemma cluster_imbalance_prune_clean
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (hF_nonempty : F.Nonempty)
    {C : ENNReal} (hC_one : 1 ≤ C) (hC_top : C ≠ ⊤)
    {w : ℝ} (hw_pos : 0 < w) (hw_delta : delta ≤ w) (hw100 : 100 * w ≤ 1)
    {Y : Kakeya.Streamlined.TubeShading F}
    {c0 : ℝ} (hwindow : ∀ i, Y.carrier i ≠ ∅ → |(tubeParams i).c - c0| ≤ w / 2)
    {lambda : ENNReal} (hlambda_zero : lambda ≠ 0) (hlambda_top : lambda ≠ ⊤)
    (hlambda_dense : Y.IsLambdaDense lambda)
    (hFrost : TubeParameterFrostmanBound F C)
    (h_params : ∀ i : Fin F.card,
      |(tubeParams i).a| ≤ 12 ∧ |(tubeParams i).b| ≤ 12 ∧
      |(tubeParams i).c| ≤ 2 ∧ |(tubeParams i).d| ≤ 2)
    (cover : ParameterClusterCoverData F Y w) :
    ∃ (surviving : DiscreteSet 3)
      (shading : Kakeya.Streamlined.TubeShading F)
      (imbalance : ℕ)
      (base_mass : ENNReal),
      surviving.Nonempty ∧
      surviving ⊆ cover.centers ∧
      IsSubshading shading Y ∧
      (0 < imbalance) ∧
      ((imbalance : ENNReal) ≤ 1000000 * C * lambda⁻¹ * Kakeya.realRpowENN w (-1) + 1) ∧
      ((2 : ENNReal)⁻¹ * Y.mass ≤ shading.mass) ∧
      (∀ i, shading.carrier i ≠ ∅ → cover.assign i ∈ surviving) ∧
      (∀ i, cover.assign i ∈ surviving → shading.carrier i = Y.carrier i) ∧
      (∀ i, shading.carrier i ≠ ∅ → dist (tubeParameterPoint3 i) (cover.assign i) ≤ w) ∧
      (0 < base_mass) ∧ (base_mass ≠ ⊤) ∧
      (∀ p ∈ surviving, base_mass ≤ tubeParameterAssignedClusterMass shading cover.assign p) ∧
      (∀ p ∈ surviving, tubeParameterAssignedClusterMass shading cover.assign p ≤ (imbalance : ENNReal) * base_mass) := by
  classical
  let assign := cover.assign
  let M := fun p : Point 3 => tubeParameterAssignedClusterMass Y assign p
  let N := cover.centers.enncard
  let T := Y.mass

  have hdelta_pos : 0 < delta := delta_pos_from_frostman hF_nonempty hFrost
  have hdelta_le_one : delta ≤ 1 := by linarith
  have hvol_pos : 0 < Kakeya.deltaTubeVolume delta := deltaTubeVolume_pos hdelta_pos hdelta_le_one

  -- T > 0 from lambda-density
  have hFmass_pos : 0 < F.toBodyFamily.mass := by
    have h1 : F.toBodyFamily.mass = F.enncard * Kakeya.deltaTubeVolume delta :=
      tubeFamily_mass_eq_nominal F
    rw [h1]
    have h2 : 0 < (F.card : ENNReal) := by exact_mod_cast hF_nonempty
    have h2' : 0 < F.enncard := by simpa [Kakeya.Streamlined.TubeFamily.enncard] using h2
    exact ENNReal.mul_pos h2'.ne' hvol_pos.ne'
  have hT_pos : 0 < T := by
    have h1 : lambda * F.toBodyFamily.mass ≤ T := hlambda_dense
    have h2 : 0 < lambda * F.toBodyFamily.mass := ENNReal.mul_pos hlambda_zero hFmass_pos.ne'
    exact h2.trans_le h1
  have hT_top : T ≠ ⊤ := by
    have h1 : T ≤ F.toBodyFamily.mass := by
      simp only [Kakeya.Streamlined.Shading.mass, Kakeya.Streamlined.BodyFamily.mass]
      apply Finset.sum_le_sum
      intro i _
      exact MeasureTheory.measure_mono (Y.subset_body i)
    have h2 : F.toBodyFamily.mass ≠ ⊤ := by
      have h3 : F.toBodyFamily.mass = F.enncard * Kakeya.deltaTubeVolume delta :=
        tubeFamily_mass_eq_nominal F
      rw [h3]
      apply ENNReal.mul_ne_top
      · simp [Kakeya.Streamlined.TubeFamily.enncard]
      · have h4 : Kakeya.deltaTubeVolume delta ≠ ⊤ :=
          (tube_volume_scaling.2.1 delta hdelta_pos (by linarith)).2
        exact h4
    exact ne_top_of_le_ne_top h2 h1

  -- N ≠ 0 from T > 0
  have h_active_nonempty : ∃ i, Y.carrier i ≠ ∅ := by
    by_contra h
    have h2 : ∀ i, Y.carrier i = ∅ := by
      intro i
      by_contra h3
      exact h ⟨i, h3⟩
    have h3 : Y.mass = 0 := by
      simp [Kakeya.Streamlined.Shading.mass, h2]
    have h4 : T = 0 := by
      dsimp only [T]
      exact h3
    rw [h4] at hT_pos
    simp at hT_pos
  rcases h_active_nonempty with ⟨i, hi⟩
  have hi_active : i ∈ cover.active := (cover.active_positiveMass i).mpr hi
  have hN_pos : N ≠ 0 := by
    have h4 : assign i ∈ cover.centers := cover.assign_mem i hi_active
    have h5 : cover.centers.Nonempty := ⟨assign i, h4⟩
    have h6 : 0 < cover.centers.card := Finset.Nonempty.card_pos h5
    have h7 : (cover.centers.card : ENNReal) ≠ 0 := by exact_mod_cast h6.ne'
    dsimp only [N, DiscreteSet.enncard]
    exact h7
  have hN_top : N ≠ ⊤ := by
    simp [DiscreteSet.enncard]
    <;> exact ENNReal.natCast_ne_top _

  -- Average and base mass
  let A := T * N⁻¹
  let base_mass := (2 : ENNReal)⁻¹ * A
  have hA_pos : 0 < A := ENNReal.mul_pos hT_pos.ne' (ENNReal.inv_pos.mpr hN_top).ne'
  have hA_top : A ≠ ⊤ := ENNReal.mul_ne_top hT_top (ENNReal.inv_ne_top.mpr hN_pos)
  have hbase_pos : 0 < base_mass := by
    dsimp only [base_mass]
    exact ENNReal.mul_pos (by simp) hA_pos.ne'
  have hbase_top : base_mass ≠ ⊤ := ENNReal.mul_ne_top (by simp) hA_top

  -- Total cluster mass = T
  have h_total : ∑ p ∈ cover.centers, M p = T :=
    sum_cluster_mass_eq_total_clean cover assign cover.assign_mem

  -- Prune
  let surviving := cover.centers.filter (fun p => base_mass ≤ M p)
  have h_survive : (2 : ENNReal)⁻¹ * T ≤ ∑ p ∈ surviving, M p :=
    prune_half_average_retention_clean h_total hN_pos hN_top hT_top
  have h_surviving_nonempty : surviving.Nonempty := by
    by_contra h
    have h' : surviving = ∅ := by simpa using h
    rw [h'] at h_survive
    simp at h_survive <;> exact hT_pos.ne' h_survive

  -- Shading restricted to surviving centers
  let shading : Kakeya.Streamlined.TubeShading F :=
    restrictShadingToCenters Y assign surviving
  have h_subshading : IsSubshading shading Y :=
    restrictShadingToCenters_subshading Y assign surviving
  have h_shading_mass : shading.mass = ∑ p ∈ surviving, M p :=
    restrictShadingToCenters_mass Y assign surviving
  have h_mass_retention : (2 : ENNReal)⁻¹ * Y.mass ≤ shading.mass := by
    rw [h_shading_mass]
    exact h_survive

  -- Assign properties for shading
  have h_assign_mem : ∀ i, shading.carrier i ≠ ∅ → assign i ∈ surviving := by
    intro i hni
    by_contra h
    have h2 : shading.carrier i = ∅ := by
      simp [shading, restrictShadingToCenters, h]
    rw [h2] at hni <;> tauto
  have h_assign_close : ∀ i, shading.carrier i ≠ ∅ →
      dist (tubeParameterPoint3 i) (assign i) ≤ w := by
    intro i hni
    have h1 : assign i ∈ surviving := h_assign_mem i hni
    have h2 : i ∈ cover.active := by
      by_contra h3
      have h4 : Y.carrier i = ∅ := by
        have h5 : ¬(Y.carrier i ≠ ∅) := (cover.active_positiveMass i).not.mp h3
        simpa using h5
      have h6 : shading.carrier i = ∅ := by
        simp [shading, restrictShadingToCenters, h1, h4]
      rw [h6] at hni <;> tauto
    exact cover.assign_close i h2

  -- Cluster mass equality: for p ∈ surviving, shading cluster mass = Y cluster mass
  have h_mass_eq : ∀ p ∈ surviving,
      tubeParameterAssignedClusterMass shading assign p = M p := by
    intro p hp
    simp only [tubeParameterAssignedClusterMass]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : assign i = p
    · have h_i_in_surv : assign i ∈ surviving := by
        rw [h]; exact hp
      have h_shading_carrier : shading.carrier i = Y.carrier i := by
        simp [shading, restrictShadingToCenters, h_i_in_surv]
      rw [if_pos h, if_pos h, h_shading_carrier]
    · rw [if_neg h, if_neg h]
      <;> simp [shading, restrictShadingToCenters]

  -- Cluster mass lower bound (by definition of surviving)
  have h_lower : ∀ p ∈ surviving, base_mass ≤ M p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2

  -- Cluster mass upper bound via Frostman
  have h_cluster_upper : ∀ p ∈ cover.centers, M p ≤
      C * Kakeya.realRpowENN (48 * w) 2 * F.toBodyFamily.mass := by
    intro p hp
    have h1 : p ∈ cover.active.image tubeParameterPoint3 := cover.centers_subset_image hp
    rcases Finset.mem_image.mp h1 with ⟨i, hi, h_eq⟩
    have hY_pos : Y.carrier i ≠ ∅ := (cover.active_positiveMass i).mp hi
    have h_point_in_centers : tubeParameterPoint3 i ∈ cover.centers := by
      exact h_eq ▸ hp
    have h_assign_eq : assign i = tubeParameterPoint3 i :=
      cover.assign_self i hi h_point_in_centers
    have h_assign_eq_p : assign i = p := by
      rw [h_assign_eq, h_eq]
    have h_witness : ∃ j, Y.carrier j ≠ ∅ ∧ assign j = p :=
      ⟨i, hY_pos, h_assign_eq_p⟩
    exact cluster_mass_frostman_upper_clean hFrost hw_pos hw_delta hw100 c0 hwindow
      assign (fun j hnj => cover.assign_close j ((cover.active_positiveMass j).mpr hnj))
      p h_witness

  -- Tight packing: N ≤ 64 * w^(-3)
  have h_box : ∀ p ∈ cover.centers, |p 0| ≤ 1 / 2 ∧ |p 1| ≤ 1 / 2 ∧ |p 2| ≤ 1 / 2 := by
    intro p hp
    have h_p_in_S : p ∈ cover.active.image tubeParameterPoint3 := cover.centers_subset_image hp
    rcases Finset.mem_image.mp h_p_in_S with ⟨i, hi, rfl⟩
    have hpa := h_params i
    dsimp only [tubeParameterPoint3, point3]
    have ha : |(tubeParams i).a / 24| ≤ 1 / 2 := by
      have h : |(tubeParams i).a| ≤ 12 := hpa.1
      calc |(tubeParams i).a / 24|
          = |(tubeParams i).a| / 24 := by simp [abs_div]
        _ ≤ 12 / 24 := by gcongr
        _ = 1 / 2 := by norm_num
    have hb : |(tubeParams i).b / 24| ≤ 1 / 2 := by
      have h : |(tubeParams i).b| ≤ 12 := hpa.2.1
      calc |(tubeParams i).b / 24|
          = |(tubeParams i).b| / 24 := by simp [abs_div]
        _ ≤ 12 / 24 := by gcongr
        _ = 1 / 2 := by norm_num
    have hd : |(tubeParams i).d / 4| ≤ 1 / 2 := by
      have h : |(tubeParams i).d| ≤ 2 := hpa.2.2.2
      calc |(tubeParams i).d / 4|
          = |(tubeParams i).d| / 4 := by simp [abs_div]
        _ ≤ 2 / 4 := by gcongr
        _ = 1 / 2 := by norm_num
    exact ⟨by simpa [tubeParameterPoint3, point3] using ha,
      by simpa [tubeParameterPoint3, point3] using hb,
      by simpa [tubeParameterPoint3, point3] using hd⟩
  have hN64 : N ≤ 64 * Kakeya.realRpowENN w (-3) :=
    separated3_packing_bound hw_pos (by linarith) cover.centers_separated h_box

  -- Ratio upper bound: M(p) ≤ X * base_mass
  let X : ENNReal := 294912 * C * lambda⁻¹ * Kakeya.realRpowENN w (-1)
  have hX_top : X ≠ ⊤ := by
    dsimp only [X]
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · norm_num
        · exact hC_top
      · simpa [ENNReal.inv_eq_top] using hlambda_zero
    · exact ENNReal.ofReal_ne_top
  have hX_pos : 0 < X := by
    dsimp only [X]
    have h1 : 0 < C := lt_of_lt_of_le (by norm_num) hC_one
    have h2 : 0 < lambda⁻¹ := ENNReal.inv_pos.mpr hlambda_top
    have h3 : 0 < Kakeya.realRpowENN w (-1) := by
      simp [Kakeya.realRpowENN, hw_pos.ne'] <;> positivity
    positivity
  have h_ratio : ∀ p ∈ surviving, M p ≤ X * base_mass := by
    intro p hp
    have h_p_in_centers : p ∈ cover.centers := Finset.mem_filter.mp hp |>.1
    have h_rpow48 : Kakeya.realRpowENN (48 * w) 2 = 2304 * Kakeya.realRpowENN w 2 := by
      have h1 : Real.rpow (48 * w) 2 = 2304 * Real.rpow w 2 := by
        have h2 : Real.rpow (48 * w) 2 = (48 * w) ^ 2 := by simp
        have h3 : Real.rpow w 2 = w ^ 2 := by simp
        rw [h2, h3] <;> ring
      have h_ofReal2304 : ENNReal.ofReal (2304 : ℝ) = (2304 : ENNReal) := by norm_cast
      have h4 : ENNReal.ofReal (Real.rpow (48 * w) 2) = 2304 * ENNReal.ofReal (Real.rpow w 2) := by
        rw [h1]
        have h5 : ENNReal.ofReal (2304 * Real.rpow w 2) =
            ENNReal.ofReal (2304 : ℝ) * ENNReal.ofReal (Real.rpow w 2) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2304)]
        rw [h5, h_ofReal2304]
      simpa [Kakeya.realRpowENN] using h4
    have hM1 : M p ≤ 2304 * C * Kakeya.realRpowENN w 2 * F.toBodyFamily.mass := by
      have h : M p ≤ C * Kakeya.realRpowENN (48 * w) 2 * F.toBodyFamily.mass :=
        h_cluster_upper p h_p_in_centers
      rw [h_rpow48] at h
      have h' : C * (2304 * Kakeya.realRpowENN w 2) * F.toBodyFamily.mass =
          2304 * C * Kakeya.realRpowENN w 2 * F.toBodyFamily.mass := by ring
      rw [h'] at h
      exact h
    have hFmass_le : F.toBodyFamily.mass ≤ lambda⁻¹ * T := by
      have h1 : lambda * F.toBodyFamily.mass ≤ T := hlambda_dense
      have h2 : lambda⁻¹ * (lambda * F.toBodyFamily.mass) ≤ lambda⁻¹ * T := by gcongr
      have h3 : lambda⁻¹ * (lambda * F.toBodyFamily.mass) = F.toBodyFamily.mass := by
        calc
          lambda⁻¹ * (lambda * F.toBodyFamily.mass)
            = (lambda⁻¹ * lambda) * F.toBodyFamily.mass := by ring
          _ = 1 * F.toBodyFamily.mass := by rw [ENNReal.inv_mul_cancel hlambda_zero hlambda_top]
          _ = F.toBodyFamily.mass := by simp
      rw [h3] at h2
      exact h2
    have hM2 : M p ≤ 2304 * C * Kakeya.realRpowENN w 2 * lambda⁻¹ * T := by
      calc
        M p ≤ 2304 * C * Kakeya.realRpowENN w 2 * F.toBodyFamily.mass := hM1
        _ ≤ 2304 * C * Kakeya.realRpowENN w 2 * (lambda⁻¹ * T) := by gcongr
        _ = 2304 * C * Kakeya.realRpowENN w 2 * lambda⁻¹ * T := by
          simp only [mul_assoc, mul_left_comm, mul_comm]
    have h_main : 2304 * C * Kakeya.realRpowENN w 2 * lambda⁻¹ * T ≤ X * base_mass := by
      dsimp only [X, base_mass, A]
      have h_helper : 2304 * C * Kakeya.realRpowENN w 2 * lambda⁻¹ * T ≤
          (294912 * C * lambda⁻¹ * Kakeya.realRpowENN w (-1)) *
            ((2 : ENNReal)⁻¹ * T * N⁻¹) :=
        cluster_ratio_helper (C := C) (lambda := lambda) (T := T) (N := N) hw_pos hN64
      have h_goal : (294912 * C * lambda⁻¹ * Kakeya.realRpowENN w (-1)) *
          ((2 : ENNReal)⁻¹ * T * N⁻¹) =
        (294912 * C * lambda⁻¹ * Kakeya.realRpowENN w (-1)) *
          ((2 : ENNReal)⁻¹ * (T * N⁻¹)) := by
        congr 1
        <;> ring
      rw [h_goal] at h_helper
      exact h_helper
    exact hM2.trans h_main

  -- Pick imbalance : ℕ
  have h_exists : ∃ (n : ℕ), X ≤ (n : ENNReal) := by
    have h1 : X < ⊤ := lt_top_iff_ne_top.mpr hX_top
    have h2 : ∃ (r : NNReal), X = ↑r := by
      refine ⟨X.toNNReal, ?_⟩
      simp [ENNReal.coe_toNNReal hX_top]
    rcases h2 with ⟨r, hr⟩
    have h3 : ∃ (n : ℕ), (r : ENNReal) ≤ (n : ENNReal) := by
      obtain ⟨n, hn⟩ := exists_nat_ge r
      exact ⟨n, by exact_mod_cast hn⟩
    rcases h3 with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hr]
    exact hn
  let imbalance : ℕ := Nat.find h_exists
  have h_imbalance_spec : X ≤ (imbalance : ENNReal) := Nat.find_spec h_exists
  have h_imbalance_bound : (imbalance : ENNReal) ≤ X + 1 := by
    by_cases h0 : imbalance = 0
    · rw [h0]; simp
    · have h_pos : 0 < imbalance := Nat.pos_of_ne_zero h0
      have h_prev : ¬(X ≤ ((imbalance - 1 : ℕ) : ENNReal)) :=
        Nat.find_min h_exists (by omega)
      have h_lt : ((imbalance - 1 : ℕ) : ENNReal) < X := by
        exact not_le.mp h_prev
      have h_eq : (imbalance : ENNReal) = ((imbalance - 1 : ℕ) : ENNReal) + 1 := by
        have h : imbalance = (imbalance - 1) + 1 := by omega
        rw [h]
        <;> simp
        <;> norm_cast
      have h_goal : ((imbalance - 1 : ℕ) : ENNReal) + (1 : ENNReal) ≤ X + (1 : ENNReal) :=
        add_le_add_left h_lt.le (1 : ENNReal)
      rw [h_eq]
      exact h_goal
  have h_imbalance_pos : 0 < imbalance := by
    by_contra h
    have h0 : imbalance = 0 := by omega
    have h1 : X ≤ 0 := by
      rw [h0] at h_imbalance_spec
      simpa using h_imbalance_spec
    have h2 : X = 0 := by simpa using h1
    rw [h2] at hX_pos <;> simp at hX_pos

  refine ⟨surviving, shading, imbalance, base_mass, ?_⟩
  exact ⟨
    h_surviving_nonempty,
    Finset.filter_subset _ _,
    h_subshading,
    h_imbalance_pos,
    by
      have h : X ≤ 1000000 * C * lambda⁻¹ * Kakeya.realRpowENN w (-1) := by
        dsimp only [X]
        gcongr <;> norm_num
      calc
        (imbalance : ENNReal) ≤ X + 1 := h_imbalance_bound
        _ ≤ 1000000 * C * lambda⁻¹ * Kakeya.realRpowENN w (-1) + 1 := by gcongr,
    h_mass_retention,
    h_assign_mem,
    (fun i hi => by
      dsimp only [shading, restrictShadingToCenters]
      rw [if_pos hi]),
    h_assign_close,
    hbase_pos,
    hbase_top,
    fun p hp => by
      rw [h_mass_eq p hp]
      exact h_lower p hp,
    fun p hp => by
      rw [h_mass_eq p hp]
      have h1 : M p ≤ X * base_mass := h_ratio p hp
      have h2 : X ≤ (imbalance : ENNReal) := h_imbalance_spec
      calc
        M p ≤ X * base_mass := h1
        _ ≤ (imbalance : ENNReal) * base_mass := by gcongr
  ⟩

end Kakeya.Assouad
