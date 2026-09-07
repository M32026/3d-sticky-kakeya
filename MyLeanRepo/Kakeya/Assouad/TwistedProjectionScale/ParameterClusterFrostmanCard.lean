import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterClusterFrostmanStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectionFrostmanHelpers
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import Mathlib.Tactic

/-!
# Frostman transfer and cardinality lower bound for weighted clusters

Converts indexed four-parameter Frostman control plus two-sided cluster masses
into an unweighted Frostman bound and a cardinality lower bound.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Finset

/--
Lower bound on clusterMass from mass retention, lambda-density, and the
upper cluster mass bound.

    clusterMass ≥ lambda * F.toBodyFamily.mass / (4 * regLoss * points.enncard)
-/
lemma cluster_mass_lower_from_retention
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y shading : Kakeya.Streamlined.TubeShading F}
    {lambda regularizationLoss clusterMass : ENNReal}
    {points : DiscreteSet 3}
    {assign : Fin F.card → Point 3}
    (hsub : IsSubshading shading Y)
    (hdense : Y.IsLambdaDense lambda)
    (hretention : (2 * regularizationLoss)⁻¹ * Y.mass ≤ shading.mass)
    (hcm_upper : ∀ p ∈ points,
      tubeParameterAssignedClusterMass shading assign p ≤ 2 * clusterMass)
    (hassign_mem : ∀ i, shading.carrier i ≠ ∅ → assign i ∈ points)
    (hpoints_nonempty : points.Nonempty)
    (hLoss_pos : 0 < regularizationLoss)
    (hLoss_top : regularizationLoss ≠ ⊤)
    (hlambda_ne_zero : lambda ≠ 0)
    (hlambda_ne_top : lambda ≠ ⊤) :
    lambda * F.toBodyFamily.mass ≤ 4 * regularizationLoss * clusterMass * points.enncard := by
  classical
  have h_mass_eq : shading.mass =
      ∑ p ∈ points, tubeParameterAssignedClusterMass shading assign p := by
    simp only [Kakeya.Streamlined.Shading.mass, tubeParameterAssignedClusterMass]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : shading.carrier i = ∅
    · have hvol : MeasureTheory.volume (shading.carrier i) = 0 := by
        rw [hi]; simp
      simp [hvol]
    · have hassign : assign i ∈ points := hassign_mem i hi
      simp [hassign]
  have h_upper : shading.mass ≤ 2 * clusterMass * points.enncard := by
    rw [h_mass_eq]
    have h : ∑ p ∈ points, tubeParameterAssignedClusterMass shading assign p ≤
        ∑ p ∈ points, (2 * clusterMass) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hcm_upper p hp
    have h' : ∑ p ∈ points, (2 * clusterMass) = 2 * clusterMass * points.enncard := by
      simp [DiscreteSet.enncard, Finset.sum_const, mul_assoc] <;> ring
    exact le_trans h h'.le
  have h_dense2 : lambda * F.toBodyFamily.mass ≤ Y.mass := hdense
  have h3 : (2 * regularizationLoss)⁻¹ * lambda * F.toBodyFamily.mass ≤ shading.mass := by
    calc
      (2 * regularizationLoss)⁻¹ * lambda * F.toBodyFamily.mass
        = (2 * regularizationLoss)⁻¹ * (lambda * F.toBodyFamily.mass) := by ring
      _ ≤ (2 * regularizationLoss)⁻¹ * Y.mass := by gcongr
      _ ≤ shading.mass := hretention
  have h4 : (2 * regularizationLoss)⁻¹ * lambda * F.toBodyFamily.mass ≤
      2 * clusterMass * points.enncard :=
    le_trans h3 h_upper
  have h5 : 0 < 2 * regularizationLoss := by positivity
  have h6 : (2 * regularizationLoss) ≠ 0 := h5.ne'
  have h7 : (2 * regularizationLoss) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) hLoss_top
  have h_inv_cancel : (2 * regularizationLoss) * (2 * regularizationLoss)⁻¹ = 1 := by
    apply ENNReal.mul_inv_cancel <;> tauto
  have h8 : (2 * regularizationLoss) * ((2 * regularizationLoss)⁻¹ * lambda * F.toBodyFamily.mass) ≤
      (2 * regularizationLoss) * (2 * clusterMass * points.enncard) := by
    gcongr
  have h9 : (2 * regularizationLoss) * ((2 * regularizationLoss)⁻¹ * lambda * F.toBodyFamily.mass) =
      lambda * F.toBodyFamily.mass := by
    have h91 : (2 * regularizationLoss) * ((2 * regularizationLoss)⁻¹ * lambda * F.toBodyFamily.mass) =
        ((2 * regularizationLoss) * (2 * regularizationLoss)⁻¹) * (lambda * F.toBodyFamily.mass) := by ring
    rw [h91, h_inv_cancel, one_mul]
  rw [h9] at h8
  have h10 : (2 * regularizationLoss) * (2 * clusterMass * points.enncard) =
      4 * regularizationLoss * clusterMass * points.enncard := by ring
  rw [h10] at h8
  exact h8

/--
Indexed parameter Frostman control at radius zero forces `0 < delta`.

If `delta ≤ 0`, applying the bound at `r = 0` gives card ≥ 1 (the reference
tube itself) but RHS = `C * 0 * F.enncard = 0`, a contradiction.
-/
lemma frostman_imp_delta_pos
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (hF_nonempty : F.Nonempty)
    (hFrost : TubeParameterFrostmanBound F C) :
    0 < delta := by
  by_contra h
  have h' : delta ≤ 0 := by linarith
  have hcard : 0 < F.card := hF_nonempty
  let i0 : Fin F.card := ⟨0, hcard⟩
  let S : Finset (Fin F.card) := Finset.univ.filter fun i : Fin F.card =>
    |(tubeParams i).a - (tubeParams i0).a| ≤ 0 ∧
    |(tubeParams i).b - (tubeParams i0).b| ≤ 0 ∧
    |(tubeParams i).c - (tubeParams i0).c| ≤ 0 ∧
    |(tubeParams i).d - (tubeParams i0).d| ≤ 0
  have hi0 : i0 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    <;> simp [abs_nonneg] <;> norm_num
  have hS_nonempty : S.Nonempty := ⟨i0, hi0⟩
  have h1 : 0 < S.card := Finset.Nonempty.card_pos hS_nonempty
  have h2 : (1 : ENNReal) ≤ (S.card : ENNReal) := by
    have h21 : 1 ≤ S.card := by omega
    exact_mod_cast h21
  have h3 := hFrost 0 h' (by norm_num) i0
  have h4 : Kakeya.realRpowENN 0 2 = 0 := by
    simp [Kakeya.realRpowENN, Real.rpow_zero] <;> norm_num
  rw [h4] at h3
  have h5 : C * (0 : ENNReal) * F.enncard = 0 := by simp
  rw [h5] at h3
  have h_cont : (1 : ENNReal) ≤ 0 := le_trans h2 h3
  simpa using h_cont

/--
Frostman transfer and cardinality lower bound.

Given clustered points with two-sided mass bounds, indexed Frostman control,
and lambda-density, proves the unweighted Frostman bound and the cardinality
lower bound required by `TubeParameterClusterFrostmanData`.
-/
lemma cluster_frostman_and_card
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y shading : Kakeya.Streamlined.TubeShading F}
    {C lambda regularizationLoss clusterMass : ENNReal}
    {w c0 : ℝ}
    {points : DiscreteSet 3}
    {assign : Fin F.card → Point 3}
    (hF_nonempty : F.Nonempty)
    (hδ_le_w : delta ≤ w)
    (hC : 1 ≤ C) (hC_top : C ≠ ⊤)
    (hlambda_ne_zero : lambda ≠ 0) (hlambda_ne_top : lambda ≠ ⊤)
    (hLoss_one : 1 ≤ regularizationLoss) (hLoss_top : regularizationLoss ≠ ⊤)
    (hw : 0 < w) (hw100 : 100 * w ≤ 1)
    (hFrost : TubeParameterFrostmanBound F C)
    (hwindow : ∀ i, shading.carrier i ≠ ∅ → |(tubeParams i).c - c0| ≤ w / 2)
    (hdense : Y.IsLambdaDense lambda)
    (hsub : IsSubshading shading Y)
    (hretention : (2 * regularizationLoss)⁻¹ * Y.mass ≤ shading.mass)
    (hpoints_nonempty : points.Nonempty)
    (hassign_mem : ∀ i, shading.carrier i ≠ ∅ → assign i ∈ points)
    (hassign_close : ∀ i, shading.carrier i ≠ ∅ →
      dist (tubeParameterPoint3 i) (assign i) ≤ w)
    (hcm_pos : 0 < clusterMass) (hcm_top : clusterMass ≠ ⊤)
    (hcm_lower : ∀ p ∈ points,
      clusterMass ≤ tubeParameterAssignedClusterMass shading assign p)
    (hcm_upper : ∀ p ∈ points,
      tubeParameterAssignedClusterMass shading assign p ≤ 2 * clusterMass) :
    points.IsFrostman w 1
      (100000 * C * regularizationLoss * lambda⁻¹) ∧
    lambda ≤ 100000 * regularizationLoss *
      (C * Kakeya.realRpowENN w 2) * points.enncard := by
  classical
  have hdelta : 0 < delta := frostman_imp_delta_pos hF_nonempty hFrost
  set V : ENNReal := Kakeya.deltaTubeVolume delta with hV_def
  have hTV := tube_volume_scaling.2.1 delta hdelta (by linarith)
  have hV_pos : 0 < V := hTV.1
  have hV_ne_zero : V ≠ 0 := hV_pos.ne'
  have hV_ne_top : V ≠ ⊤ := hTV.2
  have hFmass : F.toBodyFamily.mass = F.nominalMass :=
    tubeFamily_mass_eq_nominal F
  have hFmass_pos : 0 < F.toBodyFamily.mass := by
    rw [hFmass]
    have h1 : 0 < F.enncard := by
      dsimp only [Kakeya.Streamlined.TubeFamily.enncard]
      exact_mod_cast hF_nonempty
    exact ENNReal.mul_pos h1.ne' hV_pos.ne'
  have hFmass_ne_zero : F.toBodyFamily.mass ≠ 0 := hFmass_pos.ne'
  have hFmass_ne_top : F.toBodyFamily.mass ≠ ⊤ := by
    rw [hFmass]
    exact ENNReal.mul_ne_top (by simp [Kakeya.Streamlined.TubeFamily.enncard]) hV_ne_top
  have hlambda_le_one : lambda ≤ 1 := by
    have hY_le_F : Y.mass ≤ F.toBodyFamily.mass := by
      simp only [Kakeya.Streamlined.Shading.mass]
      apply Finset.sum_le_sum
      intro i _
      exact MeasureTheory.measure_mono (Y.subset_body i)
    have h : lambda * F.toBodyFamily.mass ≤ 1 * F.toBodyFamily.mass := by
      have h' : lambda * F.toBodyFamily.mass ≤ F.toBodyFamily.mass := le_trans hdense hY_le_F
      simpa using h'
    exact (ENNReal.mul_le_mul_iff_left hFmass_ne_zero hFmass_ne_top).mp h
  have hLoss_pos : 0 < regularizationLoss := lt_of_lt_of_le (by norm_num) hLoss_one
  have h_cm_lower : lambda * F.toBodyFamily.mass ≤
      4 * regularizationLoss * clusterMass * points.enncard :=
    cluster_mass_lower_from_retention hsub hdense hretention hcm_upper
      hassign_mem hpoints_nonempty hLoss_pos hLoss_top hlambda_ne_zero hlambda_ne_top

  -- Helper: every center has a tube with nonempty carrier assigned to it
  have h_center_has_tube : ∀ p ∈ points,
      ∃ (i : Fin F.card), shading.carrier i ≠ ∅ ∧ assign i = p := by
    intro p hp
    have h_pos : 0 < tubeParameterAssignedClusterMass shading assign p :=
      hcm_pos.trans_le (hcm_lower p hp)
    simp only [tubeParameterAssignedClusterMass] at h_pos
    rcases Finset.sum_pos_iff.mp h_pos with ⟨i, _, hi_pos⟩
    have h_assign_eq : assign i = p := by
      by_contra hne
      simp [hne] at hi_pos
    have hi_nonempty : shading.carrier i ≠ ∅ := by
      intro h
      rw [h] at hi_pos
      simp at hi_pos
    exact ⟨i, hi_nonempty, h_assign_eq⟩

  -- Helper: mass of tubes whose assigned center is in P
  let assignedMass (P : Finset (Point 3)) : ENNReal :=
    ∑ p ∈ P, tubeParameterAssignedClusterMass shading assign p

  have h_assignedMass_sum : ∀ (P : Finset (Point 3)),
      assignedMass P = ∑ i ∈ (Finset.univ.filter fun i => assign i ∈ P),
        MeasureTheory.volume (shading.carrier i) := by
    intro P
    simp only [assignedMass, tubeParameterAssignedClusterMass]
    have h1 : ∑ p ∈ P, ∑ i : Fin F.card,
        (if assign i = p then MeasureTheory.volume (shading.carrier i) else 0) =
        ∑ i : Fin F.card, ∑ p ∈ P,
        (if assign i = p then MeasureTheory.volume (shading.carrier i) else 0) := by
      rw [Finset.sum_comm]
    rw [h1]
    have h2 : ∀ (i : Fin F.card), ∑ p ∈ P,
        (if assign i = p then MeasureTheory.volume (shading.carrier i) else 0) =
        if assign i ∈ P then MeasureTheory.volume (shading.carrier i) else 0 := by
      intro i
      by_cases h : assign i ∈ P
      · rw [if_pos h]
        have h3 : ∑ p ∈ P, (if assign i = p then MeasureTheory.volume (shading.carrier i) else 0) =
            MeasureTheory.volume (shading.carrier i) := by
          rw [Finset.sum_eq_single (assign i)] <;> simp [h] <;> tauto
        exact h3
      · rw [if_neg h]
        apply Finset.sum_eq_zero
        intro p hp
        have h4 : assign i ≠ p := by intro h5; rw [h5] at h; exact h hp
        simp [h4]
    have h3 : ∑ i : Fin F.card, ∑ p ∈ P,
        (if assign i = p then MeasureTheory.volume (shading.carrier i) else 0) =
        ∑ i : Fin F.card,
        (if assign i ∈ P then MeasureTheory.volume (shading.carrier i) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      exact h2 i
    rw [h3]
    rw [Finset.sum_ite]
    <;> simp

  have h_tube_vol : ∀ i, MeasureTheory.volume (shading.carrier i) ≤ V := by
    intro i
    have h1 : MeasureTheory.volume (shading.carrier i) ≤
        MeasureTheory.volume ((F.tube i).carrier) :=
      MeasureTheory.measure_mono (shading.subset_body i)
    have h2 : MeasureTheory.volume ((F.tube i).carrier) = V := by
      have h3 : (F.tube i).volume = V := tube_volume_scaling.1 delta (F.tube i)
      simpa [Kakeya.DeltaTube.volume] using h3
    rw [h2] at h1
    exact h1

  -- === FROSTMAN BOUND ===
  have h_frostman : points.IsFrostman w 1
      (100000 * C * regularizationLoss * lambda⁻¹) := by
    intro x r hr_w hr_one
    let P : Finset (Point 3) := points.filter (fun p => dist p x ≤ r)
    have hP_subset : P ⊆ points := Finset.filter_subset _ _
    by_cases hP_empty : P = ∅
    · have hball : points.ballCount x r = 0 := by
        simpa [DiscreteSet.ballCount, P] using congr_arg Finset.card hP_empty
      rw [hball]
      exact bot_le
    · have hP_nonempty : P.Nonempty := by
        simpa [Finset.nonempty_iff_ne_empty] using hP_empty
      rcases hP_nonempty with ⟨p0, hp0⟩
      have hp0_in_points : p0 ∈ points := hP_subset hp0
      rcases h_center_has_tube p0 hp0_in_points with ⟨i0, hi0_nonempty, hassign_i0⟩
      let R : ℝ := 48 * (r + w)
      have hR_pos : 0 < R := by
        dsimp only [R]
        linarith [hw]
      have h_w_le_r : w ≤ r := hr_w
      -- Show tubes assigned to P are in parameter box of radius R around i0
      let frostSet : Finset (Fin F.card) := Finset.univ.filter fun i =>
        |(tubeParams i).a - (tubeParams i0).a| ≤ R ∧
        |(tubeParams i).b - (tubeParams i0).b| ≤ R ∧
        |(tubeParams i).c - (tubeParams i0).c| ≤ R ∧
        |(tubeParams i).d - (tubeParams i0).d| ≤ R
      let activeAssigned : Finset (Fin F.card) :=
        Finset.univ.filter fun i => assign i ∈ P ∧ shading.carrier i ≠ ∅
      have h_subset_frost : activeAssigned ⊆ frostSet := by
        intro i hi
        have h_i_in_P : assign i ∈ P := (Finset.mem_filter.mp hi).2.1
        have h_i_nonempty : shading.carrier i ≠ ∅ := (Finset.mem_filter.mp hi).2.2
        have h_dist1 : dist (tubeParameterPoint3 i) (assign i) ≤ w :=
          hassign_close i h_i_nonempty
        have h_dist2 : dist (assign i) x ≤ r := (Finset.mem_filter.mp h_i_in_P).2
        have h_dist3 : dist (tubeParameterPoint3 i0) (assign i0) ≤ w :=
          hassign_close i0 hi0_nonempty
        have h_dist4 : dist (assign i0) x ≤ r := by
          have h : dist p0 x ≤ r := (Finset.mem_filter.mp hp0).2
          simpa [hassign_i0] using h
        have h_dist_i : dist (tubeParameterPoint3 i) x ≤ r + w := by
          calc
            dist (tubeParameterPoint3 i) x
              ≤ dist (tubeParameterPoint3 i) (assign i) + dist (assign i) x :=
              dist_triangle _ _ _
            _ ≤ w + r := by linarith
            _ = r + w := by ring
        have h_dist_i0 : dist (tubeParameterPoint3 i0) x ≤ r + w := by
          calc
            dist (tubeParameterPoint3 i0) x
              ≤ dist (tubeParameterPoint3 i0) (assign i0) + dist (assign i0) x :=
              dist_triangle _ _ _
            _ ≤ w + r := by linarith
            _ = r + w := by ring
        have h_dist_both : dist (tubeParameterPoint3 i) (tubeParameterPoint3 i0) ≤ 2 * (r + w) := by
          calc
            dist (tubeParameterPoint3 i) (tubeParameterPoint3 i0)
              ≤ dist (tubeParameterPoint3 i) x + dist x (tubeParameterPoint3 i0) :=
              dist_triangle _ _ _
            _ = dist (tubeParameterPoint3 i) x + dist (tubeParameterPoint3 i0) x := by
              rw [dist_comm x (tubeParameterPoint3 i0)]
            _ ≤ (r + w) + (r + w) := by gcongr
            _ = 2 * (r + w) := by ring
        have h_params := param_diff_from_point_dist i i0 (2 * (r + w)) h_dist_both
        have hc : |(tubeParams i).c - (tubeParams i0).c| ≤ w := by
          have hci : |(tubeParams i).c - c0| ≤ w / 2 := hwindow i h_i_nonempty
          have hci0 : |(tubeParams i0).c - c0| ≤ w / 2 := hwindow i0 hi0_nonempty
          have h_abs : |(tubeParams i).c - (tubeParams i0).c| ≤
              |(tubeParams i).c - c0| + |c0 - (tubeParams i0).c| :=
            abs_sub_le (tubeParams i).c c0 (tubeParams i0).c
          have h_eq : |c0 - (tubeParams i0).c| = |(tubeParams i0).c - c0| := by
            exact abs_sub_comm c0 (tubeParams i0).c
          calc
            |(tubeParams i).c - (tubeParams i0).c|
              ≤ |(tubeParams i).c - c0| + |c0 - (tubeParams i0).c| := h_abs
            _ = |(tubeParams i).c - c0| + |(tubeParams i0).c - c0| := by rw [h_eq]
            _ ≤ w / 2 + w / 2 := by gcongr
            _ = w := by ring
        have hR_ge_w : w ≤ R := by
          dsimp only [R]
          have h : 0 < r + w := by linarith
          linarith
        have hR_eq : 24 * (2 * (r + w)) = R := by
          dsimp only [R] <;> ring
        have hR_d : 4 * (2 * (r + w)) ≤ R := by
          dsimp only [R] <;> linarith
        have ha : |(tubeParams i).a - (tubeParams i0).a| ≤ R := by
          calc
            |(tubeParams i).a - (tubeParams i0).a| ≤ 24 * (2 * (r + w)) := h_params.1
            _ = R := hR_eq
        have hb : |(tubeParams i).b - (tubeParams i0).b| ≤ R := by
          calc
            |(tubeParams i).b - (tubeParams i0).b| ≤ 24 * (2 * (r + w)) := h_params.2.1
            _ = R := hR_eq
        have hd : |(tubeParams i).d - (tubeParams i0).d| ≤ R := by
          calc
            |(tubeParams i).d - (tubeParams i0).d| ≤ 4 * (2 * (r + w)) := h_params.2.2
            _ ≤ R := hR_d
        simp only [frostSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨ha, hb, hc.trans hR_ge_w, hd⟩
      have h_mass_le : assignedMass P ≤ (frostSet.card : ENNReal) * V := by
        rw [h_assignedMass_sum P]
        have h1a : activeAssigned ⊆ (Finset.univ.filter fun i => assign i ∈ P) := by
          intro i hi
          have h2 : assign i ∈ P := (Finset.mem_filter.mp hi).2.1
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h2⟩
        have h1 : ∑ i ∈ (Finset.univ.filter fun i => assign i ∈ P),
            MeasureTheory.volume (shading.carrier i) =
            ∑ i ∈ activeAssigned, MeasureTheory.volume (shading.carrier i) := by
          rw [← Finset.sum_sdiff h1a]
          have h1b : ∑ i ∈ ((Finset.univ.filter fun i => assign i ∈ P) \ activeAssigned),
              MeasureTheory.volume (shading.carrier i) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have h2 : assign i ∈ P := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).2
            have h3 : i ∉ activeAssigned := (Finset.mem_sdiff.mp hi).2
            have h4 : shading.carrier i = ∅ := by
              by_contra h5
              exact h3 (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h2, h5⟩)
            rw [h4]
            simp
          rw [h1b, zero_add]
        rw [h1]
        have h2 : ∑ i ∈ activeAssigned, MeasureTheory.volume (shading.carrier i) ≤
            ∑ i ∈ frostSet, MeasureTheory.volume (shading.carrier i) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg h_subset_frost
          intro _ _ _; exact bot_le
        have h3 : ∑ i ∈ frostSet, MeasureTheory.volume (shading.carrier i) ≤
            ∑ i ∈ frostSet, V := by
          apply Finset.sum_le_sum
          intro i _; exact h_tube_vol i
        have h4 : ∑ i ∈ frostSet, V = (frostSet.card : ENNReal) * V := by
          simp [Finset.sum_const] <;> ring
        calc
          _ ≤ ∑ i ∈ frostSet, MeasureTheory.volume (shading.carrier i) := h2
          _ ≤ ∑ i ∈ frostSet, V := h3
          _ = (frostSet.card : ENNReal) * V := h4
      -- Frostman count bound or trivial
      have h_count_bound : (frostSet.card : ENNReal) ≤ C * Kakeya.realRpowENN R 2 * F.enncard := by
        by_cases hR_le_one : R ≤ 1
        · have hδ_le_R : delta ≤ R := by
            dsimp only [R]
            linarith [hδ_le_w]
          exact hFrost R hδ_le_R hR_le_one i0
        · have hR_gt_one : 1 < R := by linarith
          have h11 : frostSet.card ≤ F.card := by
            have h12 : frostSet.card ≤ Fintype.card (Fin F.card) := Finset.card_le_univ frostSet
            simpa using h12
          have h1 : (frostSet.card : ENNReal) ≤ F.enncard := by
            have h13 : (frostSet.card : ENNReal) ≤ (F.card : ENNReal) := by exact_mod_cast h11
            simpa [Kakeya.Streamlined.TubeFamily.enncard] using h13
          have h2 : 1 ≤ Kakeya.realRpowENN R 2 := by
            simp only [Kakeya.realRpowENN]
            have h21 : 1 < R := hR_gt_one
            have h22 : (0 : ℝ) < 2 := by norm_num
            have h23 : (1 : ℝ) < Real.rpow R 2 := Real.one_lt_rpow h21 h22
            have h24 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (Real.rpow R 2) :=
              ENNReal.ofReal_le_ofReal h23.le
            have h25 : ENNReal.ofReal (1 : ℝ) = (1 : ENNReal) := by simp
            rw [h25] at h24
            exact h24
          have h3 : (1 : ENNReal) ≤ C * Kakeya.realRpowENN R 2 := by
            calc
              (1 : ENNReal) = 1 * 1 := by ring
              _ ≤ C * Kakeya.realRpowENN R 2 := by gcongr
          have h4 : F.enncard ≤ C * Kakeya.realRpowENN R 2 * F.enncard := by
            calc
              F.enncard = 1 * F.enncard := by ring
              _ ≤ C * Kakeya.realRpowENN R 2 * F.enncard := by gcongr
          exact le_trans h1 h4
      have h_mass_bound : assignedMass P ≤ C * Kakeya.realRpowENN R 2 * F.toBodyFamily.mass := by
        have hnom : F.enncard * V = F.nominalMass := by
          simp [Kakeya.Streamlined.TubeFamily.nominalMass, hV_def] <;> ring
        have hmass' : F.enncard * V = F.toBodyFamily.mass := by
          rw [hnom, ←hFmass]
        calc
          assignedMass P ≤ (frostSet.card : ENNReal) * V := h_mass_le
          _ ≤ (C * Kakeya.realRpowENN R 2 * F.enncard) * V := by gcongr
          _ = C * Kakeya.realRpowENN R 2 * (F.enncard * V) := by ring
          _ = C * Kakeya.realRpowENN R 2 * F.toBodyFamily.mass := by rw [hmass']
      have h_P_card_lower : (P.card : ENNReal) * clusterMass ≤ assignedMass P := by
        have h : ∑ p ∈ P, clusterMass ≤ assignedMass P := by
          have h2 : ∑ p ∈ P, clusterMass ≤
              ∑ p ∈ P, tubeParameterAssignedClusterMass shading assign p := by
            apply Finset.sum_le_sum
            intro p hp
            exact hcm_lower p (hP_subset hp)
          simpa [assignedMass] using h2
        simpa [DiscreteSet.enncard, Finset.sum_const, mul_comm] using h
      have h_main_chain : (P.card : ENNReal) ≤
          4 * C * regularizationLoss * lambda⁻¹ * Kakeya.realRpowENN R 2 * points.enncard := by
        have h1 : (P.card : ENNReal) * clusterMass ≤
            C * Kakeya.realRpowENN R 2 * F.toBodyFamily.mass := h_P_card_lower.trans h_mass_bound
        have h2 : lambda * F.toBodyFamily.mass ≤
            4 * regularizationLoss * clusterMass * points.enncard := h_cm_lower
        have hcm_ne_zero : clusterMass ≠ 0 := hcm_pos.ne'
        have hcm_ne_top : clusterMass ≠ ⊤ := hcm_top
        have h3 : (P.card : ENNReal) * lambda * F.toBodyFamily.mass ≤
            (C * Kakeya.realRpowENN R 2 * F.toBodyFamily.mass) *
            (4 * regularizationLoss * points.enncard) := by
          calc
            (P.card : ENNReal) * lambda * F.toBodyFamily.mass
              = (P.card : ENNReal) * (lambda * F.toBodyFamily.mass) := by ring
            _ ≤ (P.card : ENNReal) *
                (4 * regularizationLoss * clusterMass * points.enncard) := by gcongr
            _ = 4 * regularizationLoss * points.enncard *
                ((P.card : ENNReal) * clusterMass) := by ring
            _ ≤ 4 * regularizationLoss * points.enncard *
                (C * Kakeya.realRpowENN R 2 * F.toBodyFamily.mass) := by gcongr
            _ = (C * Kakeya.realRpowENN R 2 * F.toBodyFamily.mass) *
                (4 * regularizationLoss * points.enncard) := by ring
        have h4 : F.toBodyFamily.mass ≠ 0 := hFmass_ne_zero
        have h5 : F.toBodyFamily.mass ≠ ⊤ := hFmass_ne_top
        have h3' : F.toBodyFamily.mass * ((P.card : ENNReal) * lambda) ≤
            F.toBodyFamily.mass * (C * Kakeya.realRpowENN R 2 * (4 * regularizationLoss * points.enncard)) := by
          have h_eq1 : F.toBodyFamily.mass * ((P.card : ENNReal) * lambda) =
              (P.card : ENNReal) * lambda * F.toBodyFamily.mass := by ring
          have h_eq2 : F.toBodyFamily.mass * (C * Kakeya.realRpowENN R 2 * (4 * regularizationLoss * points.enncard)) =
              (C * Kakeya.realRpowENN R 2 * F.toBodyFamily.mass) * (4 * regularizationLoss * points.enncard) := by ring
          rw [h_eq1, h_eq2]
          exact h3
        have h6 : (P.card : ENNReal) * lambda ≤
            C * Kakeya.realRpowENN R 2 * (4 * regularizationLoss * points.enncard) :=
          (ENNReal.mul_le_mul_iff_right h4 h5).mp h3'
        have h7 : lambda ≠ 0 := hlambda_ne_zero
        have h8 : lambda ≠ ⊤ := hlambda_ne_top
        have h_lambda_inv : lambda * lambda⁻¹ = 1 := by
          apply ENNReal.mul_inv_cancel <;> tauto
        have h9 : (P.card : ENNReal) * lambda * lambda⁻¹ ≤
            (C * Kakeya.realRpowENN R 2 * (4 * regularizationLoss * points.enncard)) * lambda⁻¹ := by
          gcongr
        have h10 : (P.card : ENNReal) * lambda * lambda⁻¹ = (P.card : ENNReal) := by
          have h11 : (P.card : ENNReal) * lambda * lambda⁻¹ =
              (P.card : ENNReal) * (lambda * lambda⁻¹) := by ring
          rw [h11, h_lambda_inv, mul_one]
        rw [h10] at h9
        have h11 : (C * Kakeya.realRpowENN R 2 * (4 * regularizationLoss * points.enncard)) * lambda⁻¹ =
            4 * C * regularizationLoss * lambda⁻¹ * Kakeya.realRpowENN R 2 * points.enncard := by ring
        rw [h11] at h9
        exact h9
      have h_rpow2 : ∀ (x : ℝ), 0 ≤ x → Real.rpow x 2 = x ^ 2 := by
        intro x hx
        have h1 : Real.rpow x ((2 : ℕ) : ℝ) = x ^ (2 : ℕ) := Real.rpow_natCast x 2
        have h2 : Real.rpow x 2 = x ^ 2 := by
          convert h1 using 1 <;> norm_num
        exact h2
      have hR2 : Kakeya.realRpowENN R 2 = ENNReal.ofReal (R ^ 2) := by
        simp [Kakeya.realRpowENN, h_rpow2 R (by linarith)]
      have h11 : R ^ 2 ≤ 9216 * r ^ 2 := by
        have h12 : w ≤ r := h_w_le_r
        nlinarith
      have h13 : Kakeya.realRpowENN R 2 ≤ 9216 * Kakeya.realRpowENN r 2 := by
        have hRpow : Kakeya.realRpowENN R 2 = ENNReal.ofReal (R ^ 2) := by
          simp [Kakeya.realRpowENN, h_rpow2 R (by linarith)]
        have hrpow : Kakeya.realRpowENN r 2 = ENNReal.ofReal (r ^ 2) := by
          simp [Kakeya.realRpowENN, h_rpow2 r (by linarith)]
        rw [hRpow, hrpow]
        have h14 : ENNReal.ofReal (R ^ 2) ≤ ENNReal.ofReal (9216 * r ^ 2) :=
          ENNReal.ofReal_mono (by nlinarith)
        have h15 : ENNReal.ofReal (9216 * r ^ 2) = 9216 * ENNReal.ofReal (r ^ 2) := by
          rw [ENNReal.ofReal_mul (by norm_num)] <;> norm_cast
        rw [h15] at h14
        exact h14
      have h16 : (P.card : ENNReal) ≤
          4 * C * regularizationLoss * lambda⁻¹ * (9216 * Kakeya.realRpowENN r 2) * points.enncard := by
        calc
          (P.card : ENNReal)
            ≤ 4 * C * regularizationLoss * lambda⁻¹ * Kakeya.realRpowENN R 2 * points.enncard := h_main_chain
          _ ≤ 4 * C * regularizationLoss * lambda⁻¹ * (9216 * Kakeya.realRpowENN r 2) * points.enncard := by gcongr
      have h17 : 4 * C * regularizationLoss * lambda⁻¹ * (9216 * Kakeya.realRpowENN r 2) * points.enncard =
          36864 * C * regularizationLoss * lambda⁻¹ * Kakeya.realRpowENN r 2 * points.enncard := by ring
      rw [h17] at h16
      have h18 : Kakeya.realRpowENN r 2 ≤ Kakeya.realRpowENN r 1 := by
        simp only [Kakeya.realRpowENN]
        exact ENNReal.ofReal_mono
          (Real.rpow_le_rpow_of_exponent_ge (by linarith) hr_one (by norm_num))
      have h19 : (P.card : ENNReal) ≤
          100000 * C * regularizationLoss * lambda⁻¹ * Kakeya.realRpowENN r 1 * points.enncard := by
        calc
          (P.card : ENNReal)
            ≤ 36864 * C * regularizationLoss * lambda⁻¹ * Kakeya.realRpowENN r 2 * points.enncard := h16
          _ ≤ 36864 * C * regularizationLoss * lambda⁻¹ * Kakeya.realRpowENN r 1 * points.enncard := by gcongr
          _ ≤ 100000 * C * regularizationLoss * lambda⁻¹ * Kakeya.realRpowENN r 1 * points.enncard := by
            have h20 : (36864 : ENNReal) ≤ 100000 := by norm_num
            gcongr
      simpa [DiscreteSet.ballCount, P] using h19

  -- === CARDINALITY LOWER BOUND ===
  have h_card_lower : lambda ≤ 100000 * regularizationLoss *
      (C * Kakeya.realRpowENN w 2) * points.enncard := by
    rcases hpoints_nonempty with ⟨p0, hp0⟩
    rcases h_center_has_tube p0 hp0 with ⟨i0, hi0_nonempty, hassign_i0⟩
    let R96 : ℝ := 96 * w
    have hR96_le_one : R96 ≤ 1 := by
      dsimp only [R96]
      linarith
    have hδ_le_R96 : delta ≤ R96 := by
      dsimp only [R96]
      linarith [hδ_le_w]
    let frostSet96 : Finset (Fin F.card) := Finset.univ.filter fun i =>
      |(tubeParams i).a - (tubeParams i0).a| ≤ R96 ∧
      |(tubeParams i).b - (tubeParams i0).b| ≤ R96 ∧
      |(tubeParams i).c - (tubeParams i0).c| ≤ R96 ∧
      |(tubeParams i).d - (tubeParams i0).d| ≤ R96
    let activeAtP0 : Finset (Fin F.card) :=
      Finset.univ.filter fun i => assign i = p0 ∧ shading.carrier i ≠ ∅
    have h_subset96 : activeAtP0 ⊆ frostSet96 := by
      intro i hi
      have h_i_assign : assign i = p0 := (Finset.mem_filter.mp hi).2.1
      have h_i_nonempty : shading.carrier i ≠ ∅ := (Finset.mem_filter.mp hi).2.2
      have h_dist1 : dist (tubeParameterPoint3 i) (assign i) ≤ w :=
        hassign_close i h_i_nonempty
      have h_dist2 : dist (tubeParameterPoint3 i0) (assign i0) ≤ w :=
        hassign_close i0 hi0_nonempty
      have h_dist_both : dist (tubeParameterPoint3 i) (tubeParameterPoint3 i0) ≤ 2 * w := by
        calc
          dist (tubeParameterPoint3 i) (tubeParameterPoint3 i0)
            ≤ dist (tubeParameterPoint3 i) (assign i) + dist (assign i) (tubeParameterPoint3 i0) :=
            dist_triangle _ _ _
          _ = dist (tubeParameterPoint3 i) (assign i) + dist (tubeParameterPoint3 i0) (assign i0) := by
            rw [dist_comm (assign i) (tubeParameterPoint3 i0), h_i_assign, hassign_i0]
          _ ≤ w + w := by gcongr
          _ = 2 * w := by ring
      have h_params := param_diff_from_point_dist i i0 (2 * w) h_dist_both
      have hc : |(tubeParams i).c - (tubeParams i0).c| ≤ w := by
        have hci : |(tubeParams i).c - c0| ≤ w / 2 := hwindow i h_i_nonempty
        have hci0 : |(tubeParams i0).c - c0| ≤ w / 2 := hwindow i0 hi0_nonempty
        have h_abs : |(tubeParams i).c - (tubeParams i0).c| ≤
            |(tubeParams i).c - c0| + |c0 - (tubeParams i0).c| :=
          abs_sub_le (tubeParams i).c c0 (tubeParams i0).c
        have h_eq : |c0 - (tubeParams i0).c| = |(tubeParams i0).c - c0| := by
          exact abs_sub_comm c0 (tubeParams i0).c
        calc
          |(tubeParams i).c - (tubeParams i0).c|
            ≤ |(tubeParams i).c - c0| + |c0 - (tubeParams i0).c| := h_abs
          _ = |(tubeParams i).c - c0| + |(tubeParams i0).c - c0| := by rw [h_eq]
          _ ≤ w / 2 + w / 2 := by gcongr
          _ = w := by ring
      have hR96_ge_w : w ≤ R96 := by
        dsimp only [R96]; linarith
      have hR96_eq : 24 * (2 * w) ≤ R96 := by
        dsimp only [R96]; linarith
      have hR96_d : 4 * (2 * w) ≤ R96 := by
        dsimp only [R96]; linarith
      simp only [frostSet96, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h_params.1.trans hR96_eq,
        h_params.2.1.trans hR96_eq,
        hc.trans hR96_ge_w,
        h_params.2.2.trans hR96_d⟩
    have h_frost96 : (frostSet96.card : ENNReal) ≤
        C * Kakeya.realRpowENN R96 2 * F.enncard :=
      hFrost R96 hδ_le_R96 hR96_le_one i0
    have h_cluster_mass_le : tubeParameterAssignedClusterMass shading assign p0 ≤
        (frostSet96.card : ENNReal) * V := by
      have h1 : tubeParameterAssignedClusterMass shading assign p0 =
          ∑ i ∈ activeAtP0, MeasureTheory.volume (shading.carrier i) := by
        simp only [tubeParameterAssignedClusterMass]
        have h_eq : ∀ (i : Fin F.card),
            (if assign i = p0 then MeasureTheory.volume (shading.carrier i) else 0) =
            if i ∈ activeAtP0 then MeasureTheory.volume (shading.carrier i) else 0 := by
          intro i
          by_cases h : i ∈ activeAtP0
          · have h4 : assign i = p0 := (Finset.mem_filter.mp h).2.1
            have h5 : shading.carrier i ≠ ∅ := (Finset.mem_filter.mp h).2.2
            simp [h, h4, h5]
          · have h6 : ¬(assign i = p0 ∧ shading.carrier i ≠ ∅) := by
              simpa [activeAtP0, Finset.mem_filter] using h
            by_cases h7 : assign i = p0
            · have h8 : shading.carrier i = ∅ := by tauto
              simp [h7, h8, h]
            · simp [h7, h]
        have h_sum : ∑ i : Fin F.card, (if assign i = p0 then MeasureTheory.volume (shading.carrier i) else 0) =
            ∑ i : Fin F.card, (if i ∈ activeAtP0 then MeasureTheory.volume (shading.carrier i) else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          exact h_eq i
        rw [h_sum]
        have h_sum2 : ∑ i : Fin F.card, (if i ∈ activeAtP0 then MeasureTheory.volume (shading.carrier i) else 0) =
            ∑ i ∈ activeAtP0, MeasureTheory.volume (shading.carrier i) := by
          rw [Finset.sum_ite]
          <;> simp
          <;> rfl
        exact h_sum2
      rw [h1]
      have h2 : ∑ i ∈ activeAtP0, MeasureTheory.volume (shading.carrier i) ≤
          ∑ i ∈ frostSet96, MeasureTheory.volume (shading.carrier i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg h_subset96
        intro _ _ _; exact bot_le
      have h3 : ∑ i ∈ frostSet96, MeasureTheory.volume (shading.carrier i) ≤
          ∑ i ∈ frostSet96, V := by
        apply Finset.sum_le_sum
        intro i _; exact h_tube_vol i
      have h4 : ∑ i ∈ frostSet96, V = (frostSet96.card : ENNReal) * V := by
        simp [Finset.sum_const] <;> ring
      calc
        _ ≤ ∑ i ∈ frostSet96, MeasureTheory.volume (shading.carrier i) := h2
        _ ≤ ∑ i ∈ frostSet96, V := h3
        _ = (frostSet96.card : ENNReal) * V := h4
    have h4 : clusterMass ≤ tubeParameterAssignedClusterMass shading assign p0 :=
      hcm_lower p0 hp0
    have h5 : clusterMass ≤ C * Kakeya.realRpowENN R96 2 * F.toBodyFamily.mass := by
      calc
        clusterMass ≤ tubeParameterAssignedClusterMass shading assign p0 := h4
        _ ≤ (frostSet96.card : ENNReal) * V := h_cluster_mass_le
        _ ≤ (C * Kakeya.realRpowENN R96 2 * F.enncard) * V := by gcongr
        _ = C * Kakeya.realRpowENN R96 2 * F.toBodyFamily.mass := by
          have hnom : F.enncard * V = F.nominalMass := by
            simp [Kakeya.Streamlined.TubeFamily.nominalMass, hV_def] <;> ring
          have hmass' : F.enncard * V = F.toBodyFamily.mass := by
            rw [hnom, ←hFmass]
          have h_eq : (C * Kakeya.realRpowENN R96 2 * F.enncard) * V =
              C * Kakeya.realRpowENN R96 2 * (F.enncard * V) := by ring
          rw [h_eq, hmass']
    have h6 : Kakeya.realRpowENN R96 2 = 9216 * Kakeya.realRpowENN w 2 := by
      simp only [Kakeya.realRpowENN]
      have h_rpow2' : ∀ (x : ℝ), 0 ≤ x → Real.rpow x 2 = x ^ 2 := by
        intro x hx
        have h1 : Real.rpow x ((2 : ℕ) : ℝ) = x ^ (2 : ℕ) := Real.rpow_natCast x 2
        have h2 : Real.rpow x 2 = x ^ 2 := by
          convert h1 using 1 <;> norm_num
        exact h2
      have hR96_rpow : Real.rpow R96 2 = R96 ^ 2 := h_rpow2' R96 (by linarith)
      have hw_rpow : Real.rpow w 2 = w ^ 2 := h_rpow2' w (by linarith)
      rw [hR96_rpow, hw_rpow]
      have h23 : ENNReal.ofReal (R96 ^ 2) = 9216 * ENNReal.ofReal (w ^ 2) := by
        have h24 : R96 ^ 2 = 9216 * w ^ 2 := by
          dsimp only [R96] <;> ring
        rw [h24, ENNReal.ofReal_mul (by norm_num)] <;> norm_cast
      exact h23
    rw [h6] at h5
    have h7 : clusterMass ≤ 9216 * C * Kakeya.realRpowENN w 2 * F.toBodyFamily.mass := by
      have h_eq : C * (9216 * Kakeya.realRpowENN w 2) * F.toBodyFamily.mass =
          9216 * C * Kakeya.realRpowENN w 2 * F.toBodyFamily.mass := by ring
      rw [h_eq] at h5
      exact h5
    have h8 : lambda * F.toBodyFamily.mass ≤
        4 * regularizationLoss * clusterMass * points.enncard := h_cm_lower
    have h9 : lambda * F.toBodyFamily.mass ≤
        36864 * regularizationLoss * (C * Kakeya.realRpowENN w 2) * points.enncard * F.toBodyFamily.mass := by
      calc
        lambda * F.toBodyFamily.mass
          ≤ 4 * regularizationLoss * clusterMass * points.enncard := h8
        _ ≤ 4 * regularizationLoss * (9216 * C * Kakeya.realRpowENN w 2 * F.toBodyFamily.mass) * points.enncard := by gcongr
        _ = 36864 * regularizationLoss * (C * Kakeya.realRpowENN w 2) * points.enncard * F.toBodyFamily.mass := by ring
    have h11 : lambda ≤ 36864 * regularizationLoss * (C * Kakeya.realRpowENN w 2) * points.enncard := by
      exact (ENNReal.mul_le_mul_iff_left hFmass_ne_zero hFmass_ne_top).mp h9
    have h12 : 36864 * regularizationLoss * (C * Kakeya.realRpowENN w 2) * points.enncard ≤
        100000 * regularizationLoss * (C * Kakeya.realRpowENN w 2) * points.enncard := by
      have h13 : (36864 : ENNReal) ≤ 100000 := by norm_num
      gcongr
    exact h11.trans h12

  exact ⟨h_frostman, h_card_lower⟩

end Kakeya.Assouad
