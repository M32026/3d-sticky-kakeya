import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterProjectionFiberStatement

/-!
# Helpers for the collapsed-parameter Frostman transfer
-/

namespace Kakeya.Assouad

section FiberSum

variable {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
variable (selected : Finset (Fin F.card)) (f : Fin F.card → Point 3)

lemma fiber_sum_card_disjoint :
    Set.PairwiseDisjoint ((selected.image f) : Set (Point 3))
      (fun p : Point 3 => selected.filter (fun i => f i = p)) := by
  intro p _ q _ hne
  simp only [Finset.disjoint_left]
  intro i hi1 hi2
  have h4 : f i = p := (Finset.mem_filter.mp hi1).2
  have h5 : f i = q := (Finset.mem_filter.mp hi2).2
  have h6 : p = q := by rw [← h4, h5]
  exact hne h6

lemma fiber_sum_card :
    selected.card =
      ∑ p ∈ selected.image f,
        (selected.filter (fun i => f i = p)).card := by
  let fiber : Point 3 → Finset (Fin F.card) :=
    fun p => selected.filter (fun i => f i = p)
  let image := selected.image f
  have h_disj := fiber_sum_card_disjoint selected f
  have h_biUnion : image.biUnion fiber = selected := by
    ext i
    simp only [Finset.mem_biUnion, fiber, Finset.mem_filter]
    constructor
    · rintro ⟨p, _, hi, _⟩
      exact hi
    · intro hi
      exact ⟨f i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, hi, rfl⟩
  have h :
      (image.biUnion fiber).card =
        ∑ p ∈ image, (fiber p).card :=
    Finset.card_biUnion h_disj
  rw [h_biUnion] at h
  exact h

lemma fiber_lower_bound (fm : ℕ)
    (h : ∀ p ∈ selected.image f,
      fm ≤ (selected.filter (fun i => f i = p)).card) :
    fm * (selected.image f).card ≤ selected.card := by
  let image := selected.image f
  let fiber : Point 3 → Finset (Fin F.card) :=
    fun p => selected.filter (fun i => f i = p)
  have h_card :
      selected.card = ∑ p ∈ image, (fiber p).card :=
    fiber_sum_card selected f
  rw [h_card]
  have h_sum :
      ∑ p ∈ image, fm ≤ ∑ p ∈ image, (fiber p).card :=
    Finset.sum_le_sum (fun p hp => h p hp)
  simpa [Finset.sum_const, mul_comm] using h_sum

lemma fiber_upper_bound (fm : ℕ)
    (h : ∀ p ∈ selected.image f,
      (selected.filter (fun i => f i = p)).card < 2 * fm) :
    selected.card ≤ 2 * fm * (selected.image f).card := by
  let image := selected.image f
  let fiber : Point 3 → Finset (Fin F.card) :=
    fun p => selected.filter (fun i => f i = p)
  have h_card :
      selected.card = ∑ p ∈ image, (fiber p).card :=
    fiber_sum_card selected f
  rw [h_card]
  have h_sum :
      ∑ p ∈ image, (fiber p).card ≤ ∑ p ∈ image, 2 * fm :=
    Finset.sum_le_sum (fun p hp => (h p hp).le)
  simpa [Finset.sum_const, mul_comm] using h_sum

end FiberSum

section CoordinateDist

lemma coord_le_norm' {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    |x k| ≤ ‖x‖ := by
  have h2 : ∀ i ∈ Finset.univ, 0 ≤ (x i) ^ 2 := by
    intro i _
    positivity
  have h1 : (x k) ^ 2 ≤ ∑ i : Fin n, (x i) ^ 2 :=
    Finset.single_le_sum h2 (Finset.mem_univ k)
  have h_sum_nonneg : 0 ≤ ∑ i : Fin n, (x i) ^ 2 := by positivity
  have h3 : ‖x‖ ^ 2 = ∑ i : Fin n, (x i) ^ 2 := by
    have h4 : ‖x‖ = Real.sqrt (∑ i : Fin n, (x i) ^ 2) := by
      simp [EuclideanSpace.norm_eq]
    rw [h4, Real.sq_sqrt h_sum_nonneg]
  have h4 : (x k) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [h3]
    exact h1
  have h5 : |x k| ^ 2 = (x k) ^ 2 := by rw [sq_abs]
  have h6 : |x k| ^ 2 ≤ ‖x‖ ^ 2 := by simpa [h5] using h4
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp h6

lemma coord_diff_le_dist {n : ℕ}
    (x y : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    |x k - y k| ≤ dist x y := by
  have h1 : |(x - y) k| ≤ ‖x - y‖ := coord_le_norm' (x - y) k
  simpa [dist_eq_norm] using h1

end CoordinateDist

section ParamDiff

variable {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}

lemma param_diff_from_point_dist (i j : Fin F.card) (R : ℝ)
    (h : dist (tubeParameterPoint3 i) (tubeParameterPoint3 j) ≤ R) :
    |(tubeParams i).a - (tubeParams j).a| ≤ 24 * R ∧
    |(tubeParams i).b - (tubeParams j).b| ≤ 24 * R ∧
    |(tubeParams i).d - (tubeParams j).d| ≤ 4 * R := by
  set pi := tubeParameterPoint3 i with hpi
  set pj := tubeParameterPoint3 j with hpj
  have ha_coord : |pi 0 - pj 0| ≤ dist pi pj :=
    coord_diff_le_dist pi pj 0
  have hb_coord : |pi 1 - pj 1| ≤ dist pi pj :=
    coord_diff_le_dist pi pj 1
  have hd_coord : |pi 2 - pj 2| ≤ dist pi pj :=
    coord_diff_le_dist pi pj 2
  have hR_nonneg : 0 ≤ R := by
    have h0 : 0 ≤ dist pi pj := dist_nonneg
    exact le_trans h0 h
  have ha : |(tubeParams i).a - (tubeParams j).a| ≤ 24 * R := by
    have h_eq :
        pi 0 - pj 0 =
          ((tubeParams i).a - (tubeParams j).a) / 24 := by
      simp [pi, pj, tubeParameterPoint3, point3]
      ring
    rw [h_eq] at ha_coord
    have h4 : |((tubeParams i).a - (tubeParams j).a) / 24| ≤ R := by
      exact le_trans ha_coord h
    have h5 : |(tubeParams i).a - (tubeParams j).a| / 24 ≤ R := by
      simpa [abs_div] using h4
    calc
      |(tubeParams i).a - (tubeParams j).a|
          = 24 * (|(tubeParams i).a - (tubeParams j).a| / 24) := by ring
      _ ≤ 24 * R := by gcongr
  have hb : |(tubeParams i).b - (tubeParams j).b| ≤ 24 * R := by
    have h_eq :
        pi 1 - pj 1 =
          ((tubeParams i).b - (tubeParams j).b) / 24 := by
      simp [pi, pj, tubeParameterPoint3, point3]
      ring
    rw [h_eq] at hb_coord
    have h4 : |((tubeParams i).b - (tubeParams j).b) / 24| ≤ R := by
      exact le_trans hb_coord h
    have h5 : |(tubeParams i).b - (tubeParams j).b| / 24 ≤ R := by
      simpa [abs_div] using h4
    calc
      |(tubeParams i).b - (tubeParams j).b|
          = 24 * (|(tubeParams i).b - (tubeParams j).b| / 24) := by ring
      _ ≤ 24 * R := by gcongr
  have hd : |(tubeParams i).d - (tubeParams j).d| ≤ 4 * R := by
    have h_eq :
        pi 2 - pj 2 =
          ((tubeParams i).d - (tubeParams j).d) / 4 := by
      simp [pi, pj, tubeParameterPoint3, point3]
      ring
    rw [h_eq] at hd_coord
    have h4 : |((tubeParams i).d - (tubeParams j).d) / 4| ≤ R := by
      exact le_trans hd_coord h
    have h5 : |(tubeParams i).d - (tubeParams j).d| / 4 ≤ R := by
      simpa [abs_div] using h4
    calc
      |(tubeParams i).d - (tubeParams j).d|
          = 4 * (|(tubeParams i).d - (tubeParams j).d| / 4) := by ring
      _ ≤ 4 * R := by gcongr
  exact ⟨ha, hb, hd⟩

lemma selected_preimages_in_ball_subset_box
    (selected : Finset (Fin F.card))
    (B : Finset (Point 3))
    (i0 : Fin F.card)
    (_hi0 : i0 ∈ selected)
    (R : ℝ)
    (h_ball : ∀ i ∈ selected, tubeParameterPoint3 i ∈ B →
      dist (tubeParameterPoint3 i) (tubeParameterPoint3 i0) ≤ 2 * R)
    (h_c : ∀ i ∈ selected,
      |(tubeParams i).c - (tubeParams i0).c| ≤ R) :
    selected.filter (fun i => tubeParameterPoint3 i ∈ B) ⊆
      Finset.univ.filter (fun i =>
        |(tubeParams i).a - (tubeParams i0).a| ≤ 48 * R ∧
        |(tubeParams i).b - (tubeParams i0).b| ≤ 48 * R ∧
        |(tubeParams i).c - (tubeParams i0).c| ≤ 48 * R ∧
        |(tubeParams i).d - (tubeParams i0).d| ≤ 48 * R) := by
  intro i hi
  have h_i_sel : i ∈ selected := (Finset.mem_filter.mp hi).1
  have h_i_B : tubeParameterPoint3 i ∈ B := (Finset.mem_filter.mp hi).2
  have h_dist :
      dist (tubeParameterPoint3 i) (tubeParameterPoint3 i0) ≤ 2 * R :=
    h_ball i h_i_sel h_i_B
  have h_params := param_diff_from_point_dist i i0 (2 * R) h_dist
  have hR_nonneg : 0 ≤ R := by
    have h0 : 0 ≤ dist (tubeParameterPoint3 i) (tubeParameterPoint3 i0) :=
      dist_nonneg
    linarith
  have ha : |(tubeParams i).a - (tubeParams i0).a| ≤ 48 * R := by
    have h := h_params.1
    ring_nf at h ⊢
    exact h
  have hb : |(tubeParams i).b - (tubeParams i0).b| ≤ 48 * R := by
    have h := h_params.2.1
    ring_nf at h ⊢
    exact h
  have hd : |(tubeParams i).d - (tubeParams i0).d| ≤ 48 * R := by
    calc
      |(tubeParams i).d - (tubeParams i0).d| ≤ 4 * (2 * R) :=
        h_params.2.2
      _ ≤ 48 * R := by linarith
  have hc48 : |(tubeParams i).c - (tubeParams i0).c| ≤ 48 * R := by
    exact (h_c i h_i_sel).trans (by linarith)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, ha, hb, hc48, hd⟩

end ParamDiff

section ConstantBounds

lemma half_coords_implies_unitBall (p : Point 3)
    (h : |p 0| ≤ 1 / 2 ∧ |p 1| ≤ 1 / 2 ∧ |p 2| ≤ 1 / 2) :
    dist p 0 ≤ 1 := by
  have h0 : (p 0) ^ 2 ≤ 1 / 4 := by
    have h1 : |p 0| ≤ 1 / 2 := h.1
    have h3 : |p 0| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by gcongr
    have h4 : (p 0) ^ 2 = |p 0| ^ 2 := by rw [sq_abs]
    rw [h4]
    norm_num at h3 ⊢
    exact h3
  have h1 : (p 1) ^ 2 ≤ 1 / 4 := by
    have h2 : |p 1| ≤ 1 / 2 := h.2.1
    have h4 : |p 1| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by gcongr
    have h5 : (p 1) ^ 2 = |p 1| ^ 2 := by rw [sq_abs]
    rw [h5]
    norm_num at h4 ⊢
    exact h4
  have h2 : (p 2) ^ 2 ≤ 1 / 4 := by
    have h3 : |p 2| ≤ 1 / 2 := h.2.2
    have h5 : |p 2| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by gcongr
    have h6 : (p 2) ^ 2 = |p 2| ^ 2 := by rw [sq_abs]
    rw [h6]
    norm_num at h5 ⊢
    exact h5
  have h4 : ‖p‖ ^ 2 = ∑ i : Fin 3, (p i) ^ 2 :=
    EuclideanSpace.real_norm_sq_eq p
  have h5 : ‖p‖ ^ 2 ≤ 3 / 4 := by
    rw [h4]
    simp [Fin.sum_univ_succ]
    linarith
  have h6 : ‖p‖ ≤ 1 := by nlinarith [norm_nonneg p]
  simpa [dist_zero_right] using h6

lemma lambda_le_one {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (hF : F.Nonempty) (active : Finset (Fin F.card))
    (lambda : ENNReal)
    (h : lambda * F.enncard ≤ (active.card : ENNReal)) :
    lambda ≤ 1 := by
  have h_active_le : active.card ≤ F.card := by
    simpa using Finset.card_le_univ active
  have h2 : lambda * F.enncard ≤ F.enncard := by
    have h_active_le' :
        (active.card : ENNReal) ≤ (F.card : ENNReal) := by
      exact_mod_cast h_active_le
    exact h.trans h_active_le'
  have h3 : F.enncard ≠ 0 := by
    simpa [Kakeya.Streamlined.TubeFamily.enncard] using hF.ne'
  have h4 : F.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  exact
    (ENNReal.mul_le_mul_iff_left h3 h4).mp
      (by simpa using h2)

lemma frostmanConstant_lower (C : ENNReal) (hC : 1 ≤ C)
    (n : ℕ) (_hn : 0 < n) (lambda : ENNReal) (hlambda : lambda ≤ 1) :
    1 ≤ 5000 * C * (Nat.log 2 n + 1 : ENNReal) * lambda⁻¹ := by
  have hlog : 1 ≤ (Nat.log 2 n + 1 : ENNReal) := by
    exact_mod_cast Nat.le_add_left 1 (Nat.log 2 n)
  have hinv : 1 ≤ lambda⁻¹ := ENNReal.one_le_inv.mpr hlambda
  calc
    1 ≤ C := hC
    _ ≤ 5000 * C := by
      exact le_mul_of_one_le_left (by positivity) (by norm_num)
    _ ≤ 5000 * C * (Nat.log 2 n + 1 : ENNReal) :=
      le_mul_of_one_le_right (by positivity) hlog
    _ ≤ 5000 * C * (Nat.log 2 n + 1 : ENNReal) * lambda⁻¹ :=
      le_mul_of_one_le_right (by positivity) hinv

lemma frostmanConstant_ne_top (C : ENNReal) (hC : C ≠ ⊤)
    (n : ℕ) (lambda : ENNReal) (hlambda : lambda ≠ 0) :
    5000 * C * (Nat.log 2 n + 1 : ENNReal) * lambda⁻¹ ≠ ⊤ := by
  exact
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) hC) (by simp))
      (by simpa [ENNReal.inv_eq_top] using hlambda)

lemma rpow2_le_rpow1 (r : ℝ) (hr1 : 0 ≤ r) (hr2 : r ≤ 1) :
    Kakeya.realRpowENN r 2 ≤ Kakeya.realRpowENN r 1 := by
  by_cases h0 : r = 0
  · simp [h0, Kakeya.realRpowENN]
  · exact
      ENNReal.ofReal_mono
        (Real.rpow_le_rpow_of_exponent_ge
          (lt_of_le_of_ne hr1 (Ne.symm h0)) hr2 (by norm_num))

end ConstantBounds

section ENNRealCalculations

lemma realRpowENN_scaling (r : ℝ) (hr_nonneg : 0 ≤ r) :
    Kakeya.realRpowENN (48 * r) 2 =
      2304 * Kakeya.realRpowENN r 2 := by
  have h_eq1 : Real.rpow (48 * r) 2 = 2304 * Real.rpow r 2 := by
    have h2 : Real.rpow (48 * r) 2 = (48 * r) ^ 2 := by simp
    have h3 : Real.rpow r 2 = r ^ 2 := by simp
    rw [h2, h3]
    ring
  simp only [Kakeya.realRpowENN]
  rw [h_eq1]
  have h4 : 0 ≤ r ^ 2 := by positivity
  rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2304 by norm_num)]
  norm_cast

lemma ennreal_chain_calculation
    (C logTerm fm lambda F_enncard ballCount points_enncard : ENNReal)
    (r : ℝ) (hr_nonneg : 0 ≤ r)
    (hfm_pos : fm ≠ 0) (hfm_top : fm ≠ ⊤)
    (h1 : fm * ballCount ≤
      C * Kakeya.realRpowENN (48 * r) 2 * F_enncard)
    (h2 : F_enncard ≤
      2 * logTerm * fm * points_enncard * lambda⁻¹) :
    ballCount ≤
      4608 * C * logTerm * lambda⁻¹ *
        Kakeya.realRpowENN r 2 * points_enncard := by
  have h3 : fm * ballCount ≤
      C * (2304 * Kakeya.realRpowENN r 2) *
        (2 * logTerm * fm * points_enncard * lambda⁻¹) := by
    calc
      fm * ballCount ≤
          C * Kakeya.realRpowENN (48 * r) 2 * F_enncard := h1
      _ = C * (2304 * Kakeya.realRpowENN r 2) * F_enncard := by
        rw [realRpowENN_scaling r hr_nonneg]
      _ ≤ C * (2304 * Kakeya.realRpowENN r 2) *
          (2 * logTerm * fm * points_enncard * lambda⁻¹) := by
        gcongr
  have h4 :
      C * (2304 * Kakeya.realRpowENN r 2) *
          (2 * logTerm * fm * points_enncard * lambda⁻¹) =
        fm * (4608 * C * logTerm * lambda⁻¹ *
          Kakeya.realRpowENN r 2 * points_enncard) := by
    ring
  rw [h4] at h3
  exact (ENNReal.mul_le_mul_iff_right hfm_pos hfm_top).mp h3

lemma enncard_ne_zero_of_nonempty {n : ℕ}
    {A : DiscreteSet n} (h : A.Nonempty) :
    A.enncard ≠ 0 := by
  simpa [DiscreteSet.enncard] using
    (Nat.pos_iff_ne_zero.mp (Finset.Nonempty.card_pos h))

lemma ennreal_4608_le_5000 : (4608 : ENNReal) ≤ 5000 := by norm_num

lemma large_radius_frostman_constant
    (C logTerm lambda : ENNReal) (r : ℝ)
    (hC : 1 ≤ C) (hlog : 1 ≤ logTerm) (hlambda : lambda ≤ 1)
    (hr : 1 / 48 ≤ r) :
    1 ≤ 5000 * C * logTerm * lambda⁻¹ *
      Kakeya.realRpowENN r 1 := by
  have h2 : 1 ≤ C * logTerm * lambda⁻¹ := by
    calc
      1 ≤ C := hC
      _ ≤ C * logTerm := le_mul_of_one_le_right (by positivity) hlog
      _ ≤ C * logTerm * lambda⁻¹ :=
        le_mul_of_one_le_right (by positivity)
          (ENNReal.one_le_inv.mpr hlambda)
  have h4 : 1 ≤ 5000 * Kakeya.realRpowENN (1 / 48) 1 := by
    rw [show Kakeya.realRpowENN (1 / 48) 1 =
      ENNReal.ofReal (1 / 48 : ℝ) by simp [Kakeya.realRpowENN]]
    have h5 :
        (5000 : ENNReal) * ENNReal.ofReal (1 / 48 : ℝ) =
          ENNReal.ofReal ((5000 : ℝ) * (1 / 48 : ℝ)) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_cast
    rw [h5]
    norm_num
  calc
    1 ≤ 5000 * Kakeya.realRpowENN (1 / 48) 1 := h4
    _ ≤ 5000 * (C * logTerm * lambda⁻¹) *
        Kakeya.realRpowENN (1 / 48) 1 := by
      have h7 : 5000 ≤ 5000 * (C * logTerm * lambda⁻¹) :=
        le_mul_of_one_le_right (by positivity) h2
      gcongr
    _ = 5000 * C * logTerm * lambda⁻¹ *
        Kakeya.realRpowENN (1 / 48) 1 := by ring
    _ ≤ 5000 * C * logTerm * lambda⁻¹ *
        Kakeya.realRpowENN r 1 := by
      gcongr
      exact
        ENNReal.ofReal_mono
          (Real.rpow_le_rpow (by norm_num) hr (by norm_num))

lemma cardinality_chain_for_frostman
    (lambda F_enncard selected_card fm points_enncard logTerm : ENNReal)
    (h1 : lambda * F_enncard ≤ logTerm * selected_card)
    (h2 : selected_card ≤ 2 * fm * points_enncard)
    (hlambda_ne_zero : lambda ≠ 0)
    (hlambda_ne_top : lambda ≠ ⊤) :
    F_enncard ≤ 2 * logTerm * fm * points_enncard * lambda⁻¹ := by
  have h3 :
      lambda * F_enncard ≤ 2 * logTerm * fm * points_enncard := by
    calc
      lambda * F_enncard ≤ logTerm * selected_card := h1
      _ ≤ logTerm * (2 * fm * points_enncard) := by gcongr
      _ = 2 * logTerm * fm * points_enncard := by ring
  have h4 :
      lambda⁻¹ * (lambda * F_enncard) ≤
        lambda⁻¹ * (2 * logTerm * fm * points_enncard) := by
    gcongr
  have h6 : lambda⁻¹ * (lambda * F_enncard) = F_enncard := by
    rw [← mul_assoc, ENNReal.inv_mul_cancel hlambda_ne_zero hlambda_ne_top,
      one_mul]
  rw [h6] at h4
  simpa [mul_assoc, mul_comm, mul_left_comm] using h4

end ENNRealCalculations

end Kakeya.Assouad
