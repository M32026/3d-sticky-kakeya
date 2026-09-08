import MyLeanRepo.Kakeya.Streamlined.DividingScales.SurjectiveDilatedCoverComposition

noncomputable section

namespace Kakeya.Streamlined

open GeometricLemmas

/-- Explicit dilation loss for composing an `A`-cover with an `E`-cover. -/
def composedDilatedCoverDilation (A E : ℝ) : ℝ :=
  2 * A * E + 6 * A + 6 * E + 5

lemma one_le_composedDilatedCoverDilation
    {A E : ℝ} (hA : 1 ≤ A) (hE : 1 ≤ E) :
    1 ≤ composedDilatedCoverDilation A E := by
  dsimp only [composedDilatedCoverDilation]
  nlinarith [mul_nonneg (zero_le_one.trans hA) (zero_le_one.trans hE)]

lemma composedDilatedCoverDilation_mono_right
    {A E₁ E₂ : ℝ} (hA : 0 ≤ A) (hE : E₁ ≤ E₂) :
    composedDilatedCoverDilation A E₁ ≤
      composedDilatedCoverDilation A E₂ := by
  dsimp only [composedDilatedCoverDilation]
  nlinarith

lemma dilated_containment_transitive
    {delta rho sigma A E : ℝ} (hA : 1 ≤ A) (hE : 1 ≤ E)
    (hdelta : 0 < delta) (hdelta_rho : delta ≤ rho) (hrho_pos : 0 < rho)
    (hrs : rho ≤ sigma) (hsigma_pos : 0 < sigma) (hsigma_one : sigma ≤ 1)
    (f : Kakeya.DeltaTube delta) (m : Kakeya.DeltaTube rho)
    (c : Kakeya.DeltaTube sigma)
    (hf_ball : f.IsInUnitBall)
    (h1 : f.carrier ⊆ dilatedTubeCarrier A m)
    (h2 : m.carrier ⊆ dilatedTubeCarrier E c) :
    f.carrier ⊆
      dilatedTubeCarrier (2 * A * E + 6 * A + 6 * E + 5) c := by
  have hA_pos : 0 < A := by linarith
  have hE_pos : 0 < E := by linarith
  have hrho_nonneg : 0 ≤ rho := hrho_pos.le
  have hsigma_nonneg : 0 ≤ sigma := hsigma_pos.le
  have hrho_one : rho ≤ 1 := hrs.trans hsigma_one
  have hdelta_sigma : delta ≤ sigma := le_trans hdelta_rho hrs
  rcases
      exists_oriented_dilated_parent_direction_close
        hA_pos hrho_nonneg f m h1 with
    ⟨om, hOmCarrier, hOmMidpoint, hOmDilation, hOmDir⟩
  have hOm_contained_c :
      om.carrier ⊆ dilatedTubeCarrier E c := by
    rw [hOmCarrier]
    exact h2
  rcases
      exists_oriented_dilated_parent_direction_close
        hE_pos hsigma_nonneg om c hOm_contained_c with
    ⟨oc, hOcCarrier, hOcMidpoint, hOcDilation, hOcDir⟩
  set mf := tubeMidpoint f with hmf_def
  set mm := tubeMidpoint om with hmm_def
  set mc := tubeMidpoint oc with hmc_def
  set df := f.direction with hdf_def
  set dm := om.direction with hdm_def
  set dc := oc.direction with hdc_def
  have h_df_dm : ‖df - dm‖ ≤ 4 * A * rho :=
    hOmDir
  have h_dm_dc : ‖dm - dc‖ ≤ 4 * E * sigma :=
    hOcDir
  have h_df_dc :
      ‖df - dc‖ ≤ 4 * (A + E) * sigma := by
    have h_eq : df - dc = (df - dm) + (dm - dc) := by
      abel
    rw [h_eq]
    calc
      ‖(df - dm) + (dm - dc)‖
          ≤ ‖df - dm‖ + ‖dm - dc‖ :=
        norm_add_le _ _
      _ ≤ 4 * A * rho + 4 * E * sigma :=
        add_le_add h_df_dm h_dm_dc
      _ ≤ 4 * A * sigma + 4 * E * sigma := by
        gcongr <;> linarith
      _ = 4 * (A + E) * sigma := by ring
  have h_inner_dc : inner ℝ dc dc = 1 := by
    rw [real_inner_self_eq_norm_sq, oc.direction_unit]
    norm_num
  have h_trans_dir_eq :
      df - inner ℝ df dc • dc =
        (df - dc) - inner ℝ (df - dc) dc • dc := by
    rw [inner_sub_left, h_inner_dc]
    module
  have h_trans_dir :
      ‖df - inner ℝ df dc • dc‖ ≤
        4 * (A + E) * sigma := by
    rw [h_trans_dir_eq]
    exact
      (norm_transverse_le oc.direction_unit (df - dc)).trans
        h_df_dc
  have h_mm_norm :
      ‖mm‖ ≤ 1 + 3 * A / 2 := by
    have h :=
      dilated_parent_midpoint_norm_le
        hA_pos hrho_nonneg hrho_one f m hf_ball h1
    simpa [mm, hOmMidpoint] using h
  have h_mm_in_oc :
      mm ∈ dilatedTubeCarrier E oc := by
    have h_mm_om : mm ∈ om.carrier :=
      tubeMidpoint_mem_carrier om
    have h :
        om.carrier ⊆ dilatedTubeCarrier E oc := by
      rw [hOcDilation E]
      exact hOm_contained_c
    exact h h_mm_om
  rcases
      exists_extended_axis_point_dist_le
        hE_pos hsigma_nonneg oc h_mm_in_oc with
    ⟨t, ht_abs, hdist_t⟩
  let q := mc + t • dc
  have h_q_dist :
      dist mm q ≤ E * sigma := by
    simpa [q, dist_comm] using hdist_t
  have h_mc_norm :
      ‖mc‖ ≤ 1 + 3 * A / 2 + 3 * E / 2 := by
    have h_eq : mc = (mc - q) + (q - mm) + mm := by
      abel
    have h_chain :
        ‖mc‖ ≤ ‖mc - q‖ + ‖q - mm‖ + ‖mm‖ := by
      have h_norm_eq :
          ‖mc‖ = ‖(mc - q) + (q - mm) + mm‖ :=
        congrArg norm h_eq
      rw [h_norm_eq]
      have h_first :
          ‖(mc - q) + (q - mm) + mm‖ ≤
            ‖(mc - q) + (q - mm)‖ + ‖mm‖ :=
        norm_add_le _ _
      have h_second :
          ‖(mc - q) + (q - mm)‖ ≤
            ‖mc - q‖ + ‖q - mm‖ :=
        norm_add_le _ _
      exact
        h_first.trans
          (add_le_add h_second le_rfl)
    have h_mcq : ‖mc - q‖ = |t| := by
      have h : mc - q = -(t • dc) := by
        dsimp only [q]
        module
      calc
        ‖mc - q‖ = ‖-(t • dc)‖ := by rw [h]
        _ = ‖t • dc‖ := by rw [norm_neg]
        _ = |t| * ‖dc‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        _ = |t| * 1 := by rw [oc.direction_unit]
        _ = |t| := by rw [mul_one]
    have h_qmm : ‖q - mm‖ ≤ E * sigma := by
      have h : ‖q - mm‖ = ‖mm - q‖ := by
        rw [norm_sub_rev]
      rw [h]
      have hdist : ‖mm - q‖ = dist mm q := by
        rw [← dist_eq_norm]
      rw [hdist]
      exact h_q_dist
    rw [h_mcq] at h_chain
    have h_sigma : E * sigma ≤ E :=
      mul_le_of_le_one_right hE_pos.le hsigma_one
    calc
      ‖mc‖ ≤ |t| + ‖q - mm‖ + ‖mm‖ :=
        h_chain
      _ ≤ E / 2 + E * sigma + ‖mm‖ := by
        linarith
      _ ≤ E / 2 + E + (1 + 3 * A / 2) := by
        linarith
      _ = 1 + 3 * A / 2 + 3 * E / 2 := by ring
  let C := 1 + 3 * A / 2 + 3 * E / 2
  have hC_nonneg : 0 ≤ C := by positivity
  have h_mf_norm_C : ‖mf‖ ≤ C := by
    have h : ‖mf‖ ≤ 1 :=
      tubeMidpoint_norm_le_one hf_ball
    have h' : (1 : ℝ) ≤ C := by
      dsimp only [C]
      linarith
    exact h.trans h'
  have h_mc_norm_C : ‖mc‖ ≤ C := by
    simpa [C] using h_mc_norm
  have h_mf_in_om :
      mf ∈ dilatedTubeCarrier A om := by
    have h_mf_f : mf ∈ f.carrier :=
      tubeMidpoint_mem_carrier f
    have h :
        f.carrier ⊆ dilatedTubeCarrier A om := by
      rw [hOmDilation A]
      exact h1
    exact h h_mf_f
  rcases
      exists_extended_axis_point_dist_le
        hA_pos hrho_nonneg om h_mf_in_om with
    ⟨s, hs_abs, hdist_s⟩
  let p := mm + s • dm
  have h_p_dist :
      dist mf p ≤ A * rho := by
    simpa [p, dist_comm] using hdist_s
  let trans : Point3 → Point3 :=
    fun v => v - inner ℝ v dc • dc
  have h_trans_add :
      ∀ v w : Point3, trans (v + w) = trans v + trans w := by
    intro v w
    dsimp only [trans]
    rw [inner_add_left, add_smul]
    abel
  have h_trans_smul :
      ∀ (a : ℝ) (v : Point3), trans (a • v) = a • trans v := by
    intro a v
    dsimp only [trans]
    rw [inner_smul_left]
    simp only [RCLike.conj_to_real, smul_eq_mul, smul_sub, smul_smul]
  have h_trans_neg :
      ∀ v : Point3, trans (-v) = -trans v := by
    intro v
    have h : -v = (-1 : ℝ) • v := by
      ext i
      simp
    rw [h, h_trans_smul]
    simp
  have h_trans_sub :
      ∀ v w : Point3, trans (v - w) = trans v - trans w := by
    intro v w
    rw [sub_eq_add_neg, h_trans_add, h_trans_neg]
    rfl
  have h_trans_dc : trans dc = 0 := by
    dsimp only [trans]
    rw [h_inner_dc, one_smul]
    exact sub_self dc
  have h_trans_norm :
      ∀ v : Point3, ‖trans v‖ ≤ ‖v‖ :=
    norm_transverse_le oc.direction_unit
  have h_decomp :
      mf - mc =
        (mf - p) + (s • dm) + (mm - q) + (t • dc) := by
    dsimp only [p, q]
    abel
  have h_trans_decomp :
      trans (mf - mc) =
        trans (mf - p) + s • trans dm + trans (mm - q) := by
    rw [h_decomp, h_trans_add, h_trans_add, h_trans_add,
      h_trans_smul, h_trans_smul, h_trans_dc]
    simp
  have h_norm1 :
      ‖trans (mf - p)‖ ≤ ‖mf - p‖ :=
    h_trans_norm (mf - p)
  have h_norm2 :
      ‖s • trans dm‖ = |s| * ‖trans dm‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have h_norm3 :
      ‖trans (mm - q)‖ ≤ ‖mm - q‖ :=
    h_trans_norm (mm - q)
  have h_norm4 :
      ‖trans dm‖ ≤ ‖dm - dc‖ := by
    have h_eq :
        trans dm =
          (dm - dc) - inner ℝ (dm - dc) dc • dc := by
      dsimp only [trans]
      rw [inner_sub_left, h_inner_dc]
      module
    rw [h_eq]
    exact norm_transverse_le oc.direction_unit (dm - dc)
  have h_mp : ‖mf - p‖ ≤ A * rho := by
    simpa [p, dist_eq_norm, dist_comm] using h_p_dist
  have h_mq : ‖mm - q‖ ≤ E * sigma := by
    simpa [q, dist_eq_norm, dist_comm] using h_q_dist
  have h_trans_mid :
      ‖trans (mf - mc)‖ ≤
        (A + 2 * A * E + E) * sigma := by
    rw [h_trans_decomp]
    have h_sum :
        ‖trans (mf - p) + s • trans dm + trans (mm - q)‖ ≤
          ‖trans (mf - p)‖ +
            ‖s • trans dm‖ + ‖trans (mm - q)‖ := by
      calc
        ‖trans (mf - p) + s • trans dm + trans (mm - q)‖
            ≤ ‖trans (mf - p) + s • trans dm‖ +
                ‖trans (mm - q)‖ :=
          norm_add_le _ _
        _ ≤
            (‖trans (mf - p)‖ + ‖s • trans dm‖) +
              ‖trans (mm - q)‖ := by
          gcongr
          exact norm_add_le _ _
    calc
      ‖trans (mf - p) + s • trans dm + trans (mm - q)‖
          ≤ ‖trans (mf - p)‖ +
              ‖s • trans dm‖ + ‖trans (mm - q)‖ :=
        h_sum
      _ ≤ ‖mf - p‖ + |s| * ‖trans dm‖ + ‖mm - q‖ := by
        rw [h_norm2]
        linarith
      _ ≤ A * rho + (A / 2) * ‖trans dm‖ + E * sigma := by
        have h :
            |s| * ‖trans dm‖ ≤
              (A / 2) * ‖trans dm‖ := by
          gcongr
        linarith
      _ ≤ A * rho + (A / 2) * ‖dm - dc‖ + E * sigma := by
        gcongr
      _ ≤ A * rho + (A / 2) * (4 * E * sigma) + E * sigma := by
        gcongr
      _ = A * rho + 2 * A * E * sigma + E * sigma := by ring
      _ ≤ A * sigma + 2 * A * E * sigma + E * sigma := by
        gcongr
      _ = (A + 2 * A * E + E) * sigma := by ring
  let D := 2 * A * E + 6 * A + 6 * E + 5
  have hD_ge : 4 * C + 1 ≤ D := by
    dsimp only [D, C]
    nlinarith [mul_nonneg hA_pos.le hE_pos.le]
  have h_trans_criterion :
      ‖(tubeMidpoint (withRadius sigma f) - tubeMidpoint oc) -
          inner ℝ
              (tubeMidpoint (withRadius sigma f) - tubeMidpoint oc)
              dc • dc‖ +
          (1 / 2 : ℝ) *
            ‖(withRadius sigma f).direction -
              inner ℝ (withRadius sigma f).direction dc • dc‖
        ≤ (D - 1) * sigma := by
    rw [withRadius_midpoint, withRadius_direction]
    have h :
        ‖trans (mf - mc)‖ +
            (1 / 2 : ℝ) * ‖trans df‖
          ≤ (D - 1) * sigma := by
      calc
        ‖trans (mf - mc)‖ +
              (1 / 2 : ℝ) * ‖trans df‖
            ≤
              (A + 2 * A * E + E) * sigma +
                (1 / 2 : ℝ) * (4 * (A + E) * sigma) := by
          gcongr
        _ = (2 * A * E + 3 * A + 3 * E) * sigma := by ring
        _ ≤ (D - 1) * sigma := by
          dsimp only [D]
          gcongr <;> linarith
    simpa [trans] using h
  have h_lifted :
      (withRadius sigma f).carrier ⊆
        dilatedTubeCarrier D oc :=
    tube_contained_in_dilated_transverse_general
      hsigma_pos hsigma_one D C hD_ge hC_nonneg
      (withRadius sigma f) oc
      h_mf_norm_C h_mc_norm_C h_trans_criterion
  have hf_lifted :
      f.carrier ⊆ (withRadius sigma f).carrier :=
    carrier_subset_withRadius hdelta_sigma f
  have hcarrier :
      dilatedTubeCarrier D oc =
        dilatedTubeCarrier D c :=
    hOcDilation D
  intro x hx
  exact hcarrier ▸ h_lifted (hf_lifted hx)

/-- Two covers compose with the explicit dilation used by the production
wrapper. -/
theorem surjective_dilated_cover_composition_explicit
    (A E : ℝ) (hA : 1 ≤ A) (hE : 1 ≤ E)
    {delta rho sigma : ℝ}
    (hdelta : 0 < delta)
    (hdelta_rho : delta ≤ rho)
    (hrs : rho ≤ sigma)
    (hsigma_one : sigma ≤ 1)
    {fine : TubeFamily delta}
    (hfine_ball : fine.IsInUnitBall)
    {middle : TubeFamily rho}
    {coarse : TubeFamily sigma}
    (inner : DilatedTubeCover A fine middle)
    (outer : DilatedTubeCover E middle coarse) :
    Nonempty
      (DilatedTubeCover
        (composedDilatedCoverDilation A E) fine coarse) := by
  have hrho_pos : 0 < rho :=
    lt_of_lt_of_le hdelta hdelta_rho
  have hsigma_pos : 0 < sigma :=
    lt_of_lt_of_le hrho_pos hrs
  let parent : Fin fine.card → Fin coarse.card :=
    fun i => outer.parent (inner.parent i)
  have hparent_surj : Function.Surjective parent := by
    intro k
    rcases outer.parent_surjective k with ⟨j, hj⟩
    rcases inner.parent_surjective j with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    simpa [parent, hi] using hj
  have hnested :
      ∀ i,
        (fine.tube i).carrier ⊆
          dilatedTubeCarrier
            (composedDilatedCoverDilation A E)
            (coarse.tube (parent i)) := by
    intro i
    exact
      dilated_containment_transitive
        hA hE hdelta hdelta_rho hrho_pos hrs
        hsigma_pos hsigma_one
        (fine.tube i)
        (middle.tube (inner.parent i))
        (coarse.tube (outer.parent (inner.parent i)))
        (hfine_ball i) (inner.nested i)
        (outer.nested (inner.parent i))
  exact
    ⟨{
      parent := parent
      parent_surjective := hparent_surj
      nested := hnested
    }⟩

theorem surjective_dilated_cover_composition :
    SurjectiveDilatedCoverCompositionStatement := by
  intro A E hA hE
  refine
    ⟨composedDilatedCoverDilation A E, ?_, ?_⟩
  · exact one_le_composedDilatedCoverDilation hA hE
  intro delta rho sigma hdelta hdelta_rho hrs hsigma_one
    fine hfine_ball middle coarse inner outer
  exact
    surjective_dilated_cover_composition_explicit
      A E hA hE hdelta hdelta_rho hrs hsigma_one
      hfine_ball inner outer

end Kakeya.Streamlined
