module

/-
  s-energy bound helpers for EuclideanPlane.

  - plane_packing_bound: arbitrary δ-separated set in 2δ-ball has bounded cardinality
  - plane_ball_counting: ball-counting condition from IsDeltaSSet
  - s_energy_bound_plane: discrete s-energy bound
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.PotentialTheory
public import MyLeanRepo.OSWPrelude

@[expose] public section


open scoped ENNReal NNReal

namespace DirecretisedFurstenbergEstimate.MainAppendix

open DirecretisedFurstenbergEstimate

/-- δ-independent packing constant for EuclideanPlane.
    Obtained directly from `exists_packing_constant_general (R := 2)`. -/
noncomputable def plane_packing_constant : ℕ :=
  Classical.choose (exists_packing_constant_general (V := EuclideanPlane) (R := 2) (by norm_num))

/-- The fixed packing constant satisfies the bound for any scale δ. -/
lemma plane_packing_constant_bound (δ : ℝ) (hδ_pos : 0 < δ) :
    ∀ (z : EuclideanPlane) (T : Set EuclideanPlane),
      Set.Pairwise T (fun x y => δ ≤ dist x y) →
      T ⊆ Metric.closedBall z (2 * δ) →
      T.Finite ∧ T.encard ≤ (plane_packing_constant : ENat) := by
  let hK := Classical.choose_spec (exists_packing_constant_general (V := EuclideanPlane) (R := 2) (by norm_num))
  intro z T hT_sep hT_sub
  let f : EuclideanPlane → EuclideanPlane := fun y => (δ⁻¹ : ℝ) • (y - z)
  let T' : Set EuclideanPlane := f '' T
  have hT'_sub : T' ⊆ Metric.closedBall (0 : EuclideanPlane) 2 := by
    intro y' hy'
    rcases hy' with ⟨y, hy, rfl⟩
    have h_dist : dist y z ≤ 2 * δ := hT_sub hy
    have h_norm : ‖f y‖ ≤ 2 := by
      have h1 : ‖f y‖ = δ⁻¹ * ‖y - z‖ := by
        have h2 : ‖f y‖ = ‖(δ⁻¹ : ℝ)‖ * ‖y - z‖ := norm_smul _ _
        rw [h2]
        have h3 : ‖(δ⁻¹ : ℝ)‖ = δ⁻¹ := by rw [Real.norm_eq_abs, abs_of_pos (show 0 < δ⁻¹ by positivity)]
        rw [h3] <;> ring
      rw [h1]
      have h4 : ‖y - z‖ = dist y z := by rw [dist_eq_norm]
      rw [h4]
      have h5 : δ⁻¹ * dist y z ≤ 2 := by
        calc δ⁻¹ * dist y z ≤ δ⁻¹ * (2 * δ) := by gcongr
          _ = 2 := by field_simp [hδ_pos.ne'] <;> ring
      exact h5
    simpa [Metric.mem_closedBall] using h_norm
  have hT'_sep : Set.Pairwise T' (fun a b => (1 : ℝ) ≤ dist a b) := by
    intro a ha b hb hne
    rcases ha with ⟨y, hy, rfl⟩
    rcases hb with ⟨w, hw, rfl⟩
    have hyw : y ≠ w := by intro h; apply hne; simp [h]
    have h_dist : δ ≤ dist y w := hT_sep hy hw hyw
    have h_pos : 0 < δ⁻¹ := by positivity
    have h5 : ‖f y - f w‖ = δ⁻¹ * dist y w := by
      have h_eq : f y - f w = (δ⁻¹ : ℝ) • (y - w) := by simp [f, smul_sub] <;> abel
      rw [h_eq]
      have h1 : ‖(δ⁻¹ : ℝ) • (y - w)‖ = ‖(δ⁻¹ : ℝ)‖ * ‖y - w‖ := norm_smul _ _
      rw [h1]
      have h2 : ‖(δ⁻¹ : ℝ)‖ = δ⁻¹ := by rw [Real.norm_eq_abs, abs_of_pos h_pos]
      rw [h2, dist_eq_norm] <;> ring
    have h6 : (1 : ℝ) ≤ ‖f y - f w‖ := by
      rw [h5]
      have h7 : δ⁻¹ * dist y w ≥ 1 := by
        have h8 : δ⁻¹ * dist y w ≥ δ⁻¹ * δ := by gcongr
        have h9 : δ⁻¹ * δ = 1 := by field_simp [hδ_pos.ne'] <;> ring
        linarith
      exact h7
    simpa [dist_eq_norm] using h6
  have h_result := hK 0 T' hT'_sub hT'_sep
  have hT'_fin : T'.Finite := h_result.1
  have h_inj : Set.InjOn f T := by
    intro y _ w _ h
    have h' : (δ⁻¹ : ℝ) • (y - z) = (δ⁻¹ : ℝ) • (w - z) := h
    have h'' : y - z = w - z := by
      have h_sub : (δ⁻¹ : ℝ) • ((y - z) - (w - z)) = 0 := by
        rw [smul_sub] <;> exact sub_eq_zero.mpr h'
      have h' : (δ⁻¹ : ℝ) = 0 ∨ (y - z) - (w - z) = 0 := smul_eq_zero.mp h_sub
      have h_eq_zero : (y - z) - (w - z) = 0 := h'.resolve_left (by positivity)
      simpa [sub_eq_zero] using h_eq_zero
    simpa [sub_eq_sub_iff_sub_eq_sub] using h''
  have hT_fin : T.Finite := Set.Finite.of_finite_image hT'_fin h_inj
  let Tfin : Finset EuclideanPlane := hT_fin.toFinset
  have hTfin_eq : (Tfin : Set EuclideanPlane) = T := hT_fin.coe_toFinset
  have h_inj' : Set.InjOn f (Tfin : Set EuclideanPlane) := by
    rw [hTfin_eq]
    exact h_inj
  have h_encard : T.encard = T'.encard := by
    have h1 : T.encard = ↑Tfin.card := by
      rw [← hTfin_eq] <;> simp
    have h2 : T' = (Tfin.image f : Set EuclideanPlane) := by
      ext y
      simp only [T', Set.mem_image, Finset.mem_image, Finset.mem_coe]
      <;> aesop
    rw [h1, h2]
    have h3 : (Tfin.image f : Set EuclideanPlane).encard = ↑(Tfin.image f).card := by
      exact Set.encard_coe_eq_coe_finsetCard (Finset.image f Tfin)
    rw [h3]
    have h4 : (Tfin.image f).card = Tfin.card := Finset.card_image_of_injOn h_inj'
    rw [h4] <;> rfl
  have h10 : T'.encard ≤ (plane_packing_constant : ENat) := h_result.2
  rw [h_encard]
  exact ⟨hT_fin, h10⟩

/-- General plane packing bound (kept for backward compatibility).
    Uses the δ-independent `plane_packing_constant`. -/
lemma plane_packing_bound (δ : ℝ) (hδ_pos : 0 < δ) :
    ∃ (K : ℕ), ∀ (z : EuclideanPlane) (T : Set EuclideanPlane),
      Set.Pairwise T (fun x y => δ ≤ dist x y) →
      T ⊆ Metric.closedBall z (2 * δ) →
      T.Finite ∧ T.encard ≤ (K : ENat) :=
  ⟨plane_packing_constant, plane_packing_constant_bound δ hδ_pos⟩

/-- The packing constant K_pack for the plane (δ-independent).
    Kept for backward compatibility; always equals `plane_packing_constant`. -/
noncomputable def plane_energy_K_pack (δ : ℝ) (hδ_pos : 0 < δ) : ℕ :=
  plane_packing_constant

/-- The plane packing constant is positive. -/
lemma plane_packing_constant_pos : 0 < plane_packing_constant := by
  have h1 := plane_packing_constant_bound (1 : ℝ) (by norm_num)
  let x : EuclideanPlane := 0
  let T : Set EuclideanPlane := {x}
  have hT_sep : Set.Pairwise T (fun a b => (1 : ℝ) ≤ dist a b) := by
    intro a ha b hb hne
    have ha' : a = x := by simpa [T] using ha
    have hb' : b = x := by simpa [T] using hb
    rw [ha', hb'] at hne
    simp [T] at hne
  have hT_sub : T ⊆ Metric.closedBall x (2 * (1 : ℝ)) := by
    intro y hy
    have hy' : y = x := by simpa [T] using hy
    rw [hy']
    simp [dist_self] <;> norm_num
  have h2 := h1 x T hT_sep hT_sub
  have h3 : T.encard = 1 := by simp [T]
  rw [h3] at h2
  have h4 : (1 : ENat) ≤ (plane_packing_constant : ENat) := h2.2
  exact_mod_cast h4

/-- The uniform energy constant for the plane, depending only on s, t, R (not δ). -/
noncomputable def plane_energy_constant (s t R : ℝ) : ℝ :=
  let ratio : ℝ := (2 : ℝ) ^ (s - t)
  (plane_packing_constant : ℝ) * ((2 * R) ^ t + (2 : ℝ) ^ s / (1 - ratio))

/-- Ball-counting condition for EuclideanPlane:
    For a δ-separated (δ,t,C)-set P, |P ∩ B(x,r)| ≤ K_pack * C * r^t * |P|. -/
lemma plane_ball_counting {δ t C : ℝ} (hδ_pos : 0 < δ) (ht_nonneg : 0 ≤ t) (hC_pos : 0 < C)
    {P : Finset EuclideanPlane}
    (hP_sep : Set.Pairwise (P : Set EuclideanPlane) (fun p p' => δ ≤ dist p p'))
    (hP_set : IsDeltaSSet δ t C (P : Set EuclideanPlane)) :
    ∀ (x : EuclideanPlane) (r : ℝ), δ ≤ r →
      ((P.filter (fun y => dist y x ≤ r)).card : ℝ) ≤
        (C * (plane_energy_K_pack δ hδ_pos : ℝ)) * r ^ t * (P.card : ℝ) := by
  let K_pack : ℕ := plane_energy_K_pack δ hδ_pos
  have h_pack_general := plane_packing_constant_bound δ hδ_pos
  intro x r hr
  classical
  have h_rpos : 0 < r := by linarith
  let A : Finset EuclideanPlane := P.filter (fun y => dist y x ≤ r)
  have hA_eq : (A : Set EuclideanPlane) = (P : Set EuclideanPlane) ∩ Metric.closedBall x r := by
    ext y; simp [A, Metric.mem_closedBall] <;> tauto
  have h_cover_S : Metric.IsCover δ.toNNReal (P : Set EuclideanPlane) (P : Set EuclideanPlane) := by
    intro y hy
    have h_edist : edist y y ≤ ↑δ.toNNReal := by
      rw [edist_dist, dist_self] <;> simp [hδ_pos.le] <;> exact zero_le _
    exact ⟨y, hy, h_edist⟩
  have h_covS_le : (Metric.externalCoveringNumber δ.toNNReal (P : Set EuclideanPlane) : ENNReal) ≤ (↑P.card : ENNReal) := by
    have h1 : Metric.externalCoveringNumber δ.toNNReal (P : Set EuclideanPlane) ≤ (P : Set EuclideanPlane).encard :=
      h_cover_S.externalCoveringNumber_le_encard
    have h2 : (P : Set EuclideanPlane).encard = ↑P.card := by simp
    rw [h2] at h1
    exact_mod_cast h1
  have h_main1 : (Metric.externalCoveringNumber δ.toNNReal (A : Set EuclideanPlane) : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (↑P.card : ENNReal) := by
    have h1_raw := hP_set.2.2.2.2 x r hr
    have hA_eq2 : (Metric.externalCoveringNumber δ.toNNReal (A : Set EuclideanPlane) : ENNReal) =
        Metric.externalCoveringNumber δ.toNNReal ((P : Set EuclideanPlane) ∩ Metric.closedBall x r) := by
      rw [hA_eq]
    rw [hA_eq2]
    calc (Metric.externalCoveringNumber δ.toNNReal ((P : Set EuclideanPlane) ∩ Metric.closedBall x r) : ENNReal)
      ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (Metric.externalCoveringNumber δ.toNNReal (P : Set EuclideanPlane) : ENNReal) := h1_raw
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (↑P.card : ENNReal) := by gcongr
  have h_finA : (Metric.externalCoveringNumber δ.toNNReal (A : Set EuclideanPlane) : ENNReal) < ⊤ := by
    have hcov : Metric.IsCover δ.toNNReal (A : Set EuclideanPlane) (A : Set EuclideanPlane) := by
      intro y hy; have h : edist y y ≤ ↑δ.toNNReal := by
        rw [edist_dist, dist_self] <;> simp [hδ_pos.le] <;> exact zero_le _
      exact ⟨y, hy, h⟩
    have h_le1 : Metric.externalCoveringNumber δ.toNNReal (A : Set EuclideanPlane) ≤ (A : Set EuclideanPlane).encard :=
      hcov.externalCoveringNumber_le_encard
    have h_le2 : (A : Set EuclideanPlane).encard = ↑A.card := by simp
    rw [h_le2] at h_le1
    have h : (Metric.externalCoveringNumber δ.toNNReal (A : Set EuclideanPlane) : ENNReal) ≤ (↑A.card : ENNReal) := by exact_mod_cast h_le1
    have h' : (↑A.card : ENNReal) < ⊤ := by exact ENNReal.natCast_lt_top A.card
    exact h.trans_lt h'
  let δnn : NNReal := δ.toNNReal
  have hδnn_eq : (δnn : ℝ) = δ := by simp [δnn, hδ_pos.le] <;> linarith
  have h_pack' : ∀ (z : EuclideanPlane) (T : Set EuclideanPlane),
      Set.Pairwise T (fun x y => (δnn : ℝ) ≤ dist x y) →
      T ⊆ Metric.closedBall z (2 * (δnn : ℝ)) →
      T.Finite ∧ T.encard ≤ (K_pack : ENat) := by
    intro z T hT_sep hT_sub
    have hT_sep' : Set.Pairwise T (fun x y => δ ≤ dist x y) := by simpa [hδnn_eq] using hT_sep
    have hT_sub' : T ⊆ Metric.closedBall z (2 * δ) := by simpa [hδnn_eq] using hT_sub
    exact h_pack_general z T hT_sep' hT_sub'
  have hA_sep' : Set.Pairwise (A : Set EuclideanPlane) (fun x y => (δnn : ℝ) ≤ dist x y) := by
    have hA_sep : Set.Pairwise (A : Set EuclideanPlane) (fun a b => δ ≤ dist a b) :=
      hP_sep.mono (fun x hx => (Finset.mem_filter.mp hx).1)
    simpa [hδnn_eq] using hA_sep
  have h_card : ((A : Set EuclideanPlane).encard : ENNReal) ≤
      (K_pack : ENNReal) * (Metric.externalCoveringNumber δnn (A : Set EuclideanPlane) : ENNReal) :=
    separated_set_card_le_covering hA_sep' K_pack h_pack' h_finA
  have h6 : ((A : Set EuclideanPlane).encard : ENNReal) ≤
      (K_pack : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (↑P.card : ENNReal)) := by
    calc ((A : Set EuclideanPlane).encard : ENNReal)
      ≤ (K_pack : ENNReal) * (Metric.externalCoveringNumber δnn (A : Set EuclideanPlane) : ENNReal) := h_card
    _ ≤ (K_pack : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (↑P.card : ENNReal)) := by
      gcongr
  have h_rpow : (ENNReal.ofReal r) ^ t = ENNReal.ofReal (r ^ t) :=
    ENNReal.ofReal_rpow_of_nonneg (by linarith) (by linarith)
  have hNpack : (K_pack : ENNReal) = ENNReal.ofReal (K_pack : ℝ) := by simp
  have hPcard : (↑P.card : ENNReal) = ENNReal.ofReal (P.card : ℝ) := by simp
  rw [hNpack, hPcard, h_rpow] at h6
  have h_posall : 0 ≤ (C * (K_pack : ℝ)) * r ^ t * (P.card : ℝ) := by positivity
  have h7 : ENNReal.ofReal (K_pack : ℝ) * (ENNReal.ofReal C * ENNReal.ofReal (r ^ t) * ENNReal.ofReal (P.card : ℝ)) =
      ENNReal.ofReal ((C * (K_pack : ℝ)) * r ^ t * (P.card : ℝ)) := by
    have h1 : 0 ≤ C := by linarith
    have h2 : 0 ≤ r ^ t := by positivity
    have h3 : 0 ≤ (P.card : ℝ) := by positivity
    have h4 : 0 ≤ (K_pack : ℝ) := by positivity
    simp [ENNReal.ofReal_mul, h1, h2, h3, h4, mul_assoc]
    <;> ring_nf <;> simp [mul_assoc]
  rw [h7] at h6
  have h8 : ENNReal.ofReal (A.card : ℝ) ≤ ENNReal.ofReal ((C * (K_pack : ℝ)) * r ^ t * (P.card : ℝ)) := by
    have h9 : ((A : Set EuclideanPlane).encard : ENNReal) = ENNReal.ofReal (A.card : ℝ) := by simp
    rw [h9] at h6
    exact h6
  have h10 : (A.card : ℝ) ≤ (C * (K_pack : ℝ)) * r ^ t * (P.card : ℝ) := by
    have h11 : ENNReal.ofReal (A.card : ℝ) ≤ ENNReal.ofReal ((C * (K_pack : ℝ)) * r ^ t * (P.card : ℝ)) := h8
    exact (ENNReal.ofReal_le_ofReal_iff h_posall).mp h8
  exact h10

/-- Discrete s-energy bound for a δ-separated (δ,t,C_P)-set in a ball of radius R.
    Returns ∃ K_energy > 0 such that Σ_{p≠p'} dist(p,p')^{-s} ≤ K_energy * C_P * |P|².
    The constant K_energy depends only on s, t, R, not on δ, C_P, or P. -/
theorem s_energy_bound_plane_exists
    {δ s t C_P R : ℝ}
    (hδ_pos : 0 < δ) (hs_pos : 0 < s) (hst : s < t)
    (hR_pos : 0 < R) (hCP_pos : 0 < C_P)
    {P : Finset EuclideanPlane}
    (hP_sep : Set.Pairwise (P : Set EuclideanPlane) (fun p p' => δ ≤ dist p p'))
    (hP_set : IsDeltaSSet δ t C_P (P : Set EuclideanPlane))
    (hP_bdd : ∀ p ∈ P, ‖p‖ ≤ R) :
    ∃ (K_energy : ℝ), 0 < K_energy ∧
      K_energy ≥ (2 * R) ^ t ∧
      K_energy = plane_energy_constant s t R ∧
      ∑ p ∈ P, ∑ p' ∈ P.erase p, Real.rpow (dist p p') (-s) ≤
        K_energy * C_P * (P.card : ℝ)^2 := by
  let K_pack : ℕ := plane_energy_K_pack δ hδ_pos
  have h_ball := plane_ball_counting hδ_pos (by linarith) hCP_pos hP_sep hP_set
  let C' : ℝ := C_P * (K_pack : ℝ)
  have hC'_nonneg : 0 ≤ C' := by positivity
  have h_ball' : ∀ (p : EuclideanPlane), p ∈ P → ∀ (r : ℝ), δ ≤ r →
      ((P.filter (fun q => dist p q ≤ r)).card : ℝ) ≤ C' * r ^ t * (P.card : ℝ) := by
    intro p hp r hr
    have h := h_ball p r hr
    have h_comm : (P.filter (fun y : EuclideanPlane => dist y p ≤ r)) =
        (P.filter (fun q : EuclideanPlane => dist p q ≤ r)) := by
      ext q
      simp [dist_comm]
    rw [h_comm] at h
    exact h
  have hP_sep' : ∀ (p : EuclideanPlane), p ∈ P → ∀ (q : EuclideanPlane), q ∈ P → p ≠ q → δ ≤ dist p q := by
    intro p hp q hq hne
    exact hP_sep hp hq hne
  -- (We re-prove the discrete bound directly below; no need for finite_set_energy_bound.)
  -- The Riesz energy bound implies the discrete sum bound.
  -- finite_set_energy_bound's proof establishes h_point_bound directly.
  -- We reconstruct it here.
  let ratio : ℝ := (2 : ℝ) ^ (s - t)
  have h_ratio_lt_one : ratio < 1 := by
    have h2 : s - t < 0 := by linarith
    have h3 : (2 : ℝ) ^ (s - t) < (2 : ℝ) ^ (0 : ℝ) := by
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
      exact h2
    norm_num at h3 ⊢
    exact h3
  have h_ratio_pos : 0 < ratio := by positivity
  let M0 : ℝ := C' * ((2 * R) ^ t + (2 : ℝ) ^ s / (1 - ratio))
  have hM0_pos : 0 < M0 := by
    dsimp only [M0]
    have h1 : 0 < (2 * R) ^ t := Real.rpow_pos_of_pos (by linarith) t
    have h2 : 0 < (2 : ℝ) ^ s / (1 - ratio) := by positivity
    have h3 : 0 < (2 * R) ^ t + (2 : ℝ) ^ s / (1 - ratio) := by linarith
    have h4 : 0 < C' := by
      have hP_nonempty : P.Nonempty := hP_set.1
      rcases hP_nonempty with ⟨p, hp⟩
      have h5 : p ∈ P.filter (fun q => dist p q ≤ δ) := by
        have h51 : dist p p ≤ δ := by
          have h52 : dist p p = 0 := by simp
          rw [h52] <;> linarith
        exact Finset.mem_filter.mpr ⟨hp, h51⟩
      have h6 : 0 < (P.filter (fun q => dist p q ≤ δ)).card := Finset.card_pos.mpr ⟨p, h5⟩
      have h7 : ((P.filter (fun q => dist p q ≤ δ)).card : ℝ) ≤ C' * δ ^ t * (P.card : ℝ) := h_ball' p hp δ (by linarith)
      have h8 : (0 : ℝ) < ((P.filter (fun q => dist p q ≤ δ)).card : ℝ) := by exact_mod_cast h6
      have h9 : 0 < δ ^ t := Real.rpow_pos_of_pos hδ_pos t
      have h10 : 0 < (P.card : ℝ) := by
        exact_mod_cast (Finset.card_pos.mpr hP_set.1)
      have h11 : 0 < δ ^ t * (P.card : ℝ) := mul_pos h9 h10
      have h12 : 0 < C' * (δ ^ t * (P.card : ℝ)) := by
        calc 0 < ((P.filter (fun q => dist p q ≤ δ)).card : ℝ) := h8
             _ ≤ C' * δ ^ t * (P.card : ℝ) := h7
             _ = C' * (δ ^ t * (P.card : ℝ)) := by ring
      exact (mul_pos_iff_of_pos_right h11).mp h12
    exact mul_pos h4 h3
  have hK_exists : ∃ (K : ℕ), (2 : ℝ)^(-(K : ℝ)) < δ := by
    have h1pos2 : 0 < 1 / δ := by positivity
    have h1 : ∃ (n : ℕ), (n : ℝ) > Real.logb 2 (1 / δ) := exists_nat_gt (Real.logb 2 (1 / δ))
    rcases h1 with ⟨K, hK⟩
    have h2 : (K : ℝ) > Real.logb 2 (1 / δ) := by exact_mod_cast hK
    have h3 : -(K : ℝ) < Real.logb 2 δ := by
      have h4 : Real.logb 2 (1 / δ) = -Real.logb 2 δ := by
        simp [Real.logb, Real.log_div (by positivity) (by positivity)] <;> ring
      linarith
    have h5 : (2 : ℝ)^(-(K : ℝ)) < (2 : ℝ)^(Real.logb 2 δ) := by
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
      exact h3
    have h6 : (2 : ℝ)^(Real.logb 2 δ) = δ := by
      have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h_eq : Real.logb 2 δ * Real.log 2 = Real.log δ := by
        simp only [Real.logb]
        field_simp [h_log2_pos.ne'] <;> ring
      have h1 : (2 : ℝ)^(Real.logb 2 δ) = Real.exp (Real.log 2 * Real.logb 2 δ) :=
        (Real.rpow_def_of_pos (show (0 : ℝ) < 2 from by norm_num)) (Real.logb 2 δ)
      have h_comm : Real.log 2 * Real.logb 2 δ = Real.logb 2 δ * Real.log 2 := by ring
      rw [h1, h_comm, h_eq, Real.exp_log hδ_pos]
    rw [h6] at h5
    exact ⟨K, h5⟩
  rcases hK_exists with ⟨K, hK2⟩
  have h_point_bound : ∀ p ∈ P,
      ∑ p' ∈ P.erase p, Real.rpow (dist p p') (-s) ≤ M0 * (P.card : ℝ) := by
    intro p hp
    let A (k : ℕ) := P.filter (fun q =>
      (2 : ℝ)^(-(k+1 : ℝ)) < dist p q ∧ dist p q ≤ (2 : ℝ)^(-(k : ℝ)))
    let Binf := P.filter (fun q => 1 < dist p q)
    have hA_card : ∀ k : ℕ, ((A k).card : ℝ) ≤ C' * ((2 : ℝ)^(-(k : ℝ)))^t * (P.card : ℝ) := by
      intro k
      by_cases h : δ ≤ (2 : ℝ)^(-(k : ℝ))
      · have h1 : A k ⊆ P.filter (fun q => dist p q ≤ (2 : ℝ)^(-(k : ℝ))) := by
          intro q hq
          simp only [A, Finset.mem_filter] at hq ⊢
          exact ⟨hq.1, hq.2.2⟩
        have h2 : (A k).card ≤ (P.filter (fun q => dist p q ≤ (2 : ℝ)^(-(k : ℝ)))).card :=
          Finset.card_le_card h1
        have h3 : ((A k).card : ℝ) ≤ ↑((P.filter (fun q => dist p q ≤ (2 : ℝ)^(-(k : ℝ)))).card) := by
          exact_mod_cast h2
        have h4 := h_ball' p hp ((2 : ℝ)^(-(k : ℝ))) h
        exact le_trans h3 h4
      · have h' : (2 : ℝ)^(-(k : ℝ)) < δ := by linarith
        have h3 : A k = ∅ := by
          have h4 : (A k).card = 0 := by
            by_contra h5
            have h6 : 0 < (A k).card := Nat.pos_of_ne_zero h5
            rcases Finset.card_pos.mp h6 with ⟨q, hq⟩
            rcases Finset.mem_filter.mp hq with ⟨hqS, h_aj1, h_aj2⟩
            have h5' : dist p q < δ := lt_of_le_of_lt h_aj2 h'
            have h6' : p ≠ q := by
              intro h7
              rw [h7] at h_aj1
              have h_cont : (2 : ℝ)^(-(k + 1 : ℝ)) < 0 := by simpa using h_aj1
              have h_pos : 0 < (2 : ℝ)^(-(k + 1 : ℝ)) := by positivity
              exact False.elim (lt_irrefl 0 (h_pos.trans h_cont))
            have h7 : δ ≤ dist p q := hP_sep' p hp q hqS h6'
            have h_cont : δ < δ := h7.trans_lt h5'
            exact False.elim (lt_irrefl δ h_cont)
          exact Finset.card_eq_zero.mp h4
        rw [h3] <;> simp <;> positivity
    have h_cover : ∀ q ∈ P.erase p, q ∈ Binf ∨ ∃ k < K, q ∈ A k := by
      intro q hq
      have hqS : q ∈ P := (Finset.mem_erase.mp hq).2
      have hqne : q ≠ p := (Finset.mem_erase.mp hq).1
      have hpos : 0 < dist p q := dist_pos.mpr (Ne.symm hqne)
      by_cases hbig : 1 < dist p q
      · left; simp only [Binf, Finset.mem_filter]; exact ⟨hqS, hbig⟩
      · have hle : dist p q ≤ 1 := by linarith
        rcases DiscretisedFurstenbergEstimate.PotentialTheory.exists_annulus_index hpos hle with ⟨j, h_aj1, h_aj2⟩
        have h_j_lt_K : j < K := by
          by_contra h
          have h9 : j ≥ K := by omega
          have h10 : (2 : ℝ)^(-(j : ℝ)) ≤ (2 : ℝ)^(-(K : ℝ)) := by
            apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
            have h11 : -(j : ℝ) ≤ -(K : ℝ) := by
              have h12 : (K : ℝ) ≤ (j : ℝ) := by exact_mod_cast h9
              linarith
            exact h11
          have h11 : dist p q < δ := by linarith [h_aj2, h10, hK2]
          have h12 : δ ≤ dist p q := hP_sep' p hp q hqS hqne.symm
          linarith
        right; refine ⟨j, h_j_lt_K, ?_⟩
        simp only [A, Finset.mem_filter]; exact ⟨hqS, h_aj1, h_aj2⟩
    have hBinf_sum : ∑ q ∈ Binf, Real.rpow (dist p q) (-s) ≤ (Binf.card : ℝ) := by
      have h9 : ∀ q ∈ Binf, Real.rpow (dist p q) (-s) ≤ 1 := by
        intro q hq
        have h10 : 1 < dist p q := (Finset.mem_filter.mp hq).2
        have h11 : 0 ≤ s := by linarith
        have h12 : 1 ≤ dist p q := by linarith
        have h13 : 1 ≤ Real.rpow (dist p q) s := Real.one_le_rpow h12 h11
        have h14 : Real.rpow (dist p q) (-s) = (Real.rpow (dist p q) s)⁻¹ := by
          have h_nonneg : 0 ≤ dist p q := by linarith
          exact Real.rpow_neg h_nonneg s
        rw [h14]
        have h15 : (Real.rpow (dist p q) s)⁻¹ ≤ 1 := by
          have h16 : 1 ≤ Real.rpow (dist p q) s := h13
          have h17 : 0 < Real.rpow (dist p q) s := by positivity
          have h18 : 1 / Real.rpow (dist p q) s ≤ 1 := (div_le_one h17).mpr h16
          simpa using h18
        exact h15
      calc ∑ q ∈ Binf, Real.rpow (dist p q) (-s)
        ≤ ∑ q ∈ Binf, (1 : ℝ) := Finset.sum_le_sum h9
      _ = (Binf.card : ℝ) := by simp [Finset.sum_const] <;> ring
    have h_geom_sum : ∀ (N : ℕ), ∑ k ∈ Finset.range N, ratio ^ k ≤ 1 / (1 - ratio) := by
      have h_formula : ∀ N, ∑ k ∈ Finset.range N, ratio ^ k = (1 - ratio ^ N) / (1 - ratio) := by
        intro N
        induction N with
        | zero => simp
        | succ N ih =>
          rw [Finset.sum_range_succ, ih]
          field_simp [h_ratio_pos.ne', (show (1 - ratio : ℝ) ≠ 0 by linarith)] <;> ring
      intro N
      rw [h_formula N]
      have h_pos : 0 < 1 - ratio := by linarith
      have h_nonneg : 0 ≤ ratio ^ N := by positivity
      have h : (1 - ratio ^ N) / (1 - ratio) ≤ 1 / (1 - ratio) := by
        apply div_le_div_of_nonneg_right <;> linarith
      exact h
    have h_annulus_sum : ∑ k ∈ Finset.range K, ∑ q ∈ A k, Real.rpow (dist p q) (-s) ≤
        C' * (P.card : ℝ) * (2 : ℝ) ^ s / (1 - ratio) := by
      have h1 : ∀ k ∈ Finset.range K, ∑ q ∈ A k, Real.rpow (dist p q) (-s) ≤
          ((A k).card : ℝ) * ((2 : ℝ)^(-(k + 1 : ℝ)))^(-s) := by
        intro k _
        have h2 : ∀ q ∈ A k, Real.rpow (dist p q) (-s) ≤ ((2 : ℝ)^(-(k + 1 : ℝ)))^(-s) := by
          intro q hq
          have h3 : (2 : ℝ)^(-(k + 1 : ℝ)) < dist p q := (Finset.mem_filter.mp hq).2.1
          have h4 : -s < 0 := by linarith
          have h_pos1 : 0 < (2 : ℝ)^(-(k + 1 : ℝ)) := by positivity
          have h_pos2 : 0 < dist p q := by linarith [h3, h_pos1]
          have h5 : Real.rpow (dist p q) (-s) < Real.rpow ((2 : ℝ)^(-(k + 1 : ℝ))) (-s) := by
            have h6 : Real.rpow (dist p q) (-s) = (Real.rpow (dist p q) s)⁻¹ := by
              exact Real.rpow_neg (by linarith) s
            have h7 : Real.rpow ((2 : ℝ)^(-(k + 1 : ℝ))) (-s) = (Real.rpow ((2 : ℝ)^(-(k + 1 : ℝ))) s)⁻¹ := by
              exact Real.rpow_neg (by positivity) s
            rw [h6, h7]
            have h8 : Real.rpow ((2 : ℝ)^(-(k + 1 : ℝ))) s < Real.rpow (dist p q) s :=
              Real.rpow_lt_rpow h_pos1.le h3 (by linarith)
            have h9 : 0 < Real.rpow ((2 : ℝ)^(-(k + 1 : ℝ))) s := Real.rpow_pos_of_pos h_pos1 s
            have h10 : 0 < Real.rpow (dist p q) s := Real.rpow_pos_of_pos h_pos2 s
            have h11 : (Real.rpow (dist p q) s)⁻¹ < (Real.rpow ((2 : ℝ)^(-(k + 1 : ℝ))) s)⁻¹ := by
              have h12 : (Real.rpow (dist p q) s)⁻¹ = 1 / Real.rpow (dist p q) s := by simp
              have h13 : (Real.rpow ((2 : ℝ)^(-(k + 1 : ℝ))) s)⁻¹ = 1 / Real.rpow ((2 : ℝ)^(-(k + 1 : ℝ))) s := by simp
              rw [h12, h13]
              exact one_div_lt_one_div_of_lt h9 h8
            exact h11
          exact h5.le
        calc ∑ q ∈ A k, Real.rpow (dist p q) (-s)
          ≤ ∑ q ∈ A k, ((2 : ℝ)^(-(k + 1 : ℝ)))^(-s) := Finset.sum_le_sum h2
        _ = ((A k).card : ℝ) * ((2 : ℝ)^(-(k + 1 : ℝ)))^(-s) := by
          simp [Finset.sum_const] <;> ring
      calc ∑ k ∈ Finset.range K, ∑ q ∈ A k, Real.rpow (dist p q) (-s)
        ≤ ∑ k ∈ Finset.range K, ((A k).card : ℝ) * ((2 : ℝ)^(-(k + 1 : ℝ)))^(-s) :=
          Finset.sum_le_sum h1
      _ ≤ ∑ k ∈ Finset.range K, (C' * (P.card : ℝ) * ((2 : ℝ)^(-(k : ℝ)))^t * ((2 : ℝ)^(-(k + 1 : ℝ)))^(-s)) := by
          apply Finset.sum_le_sum
          intro k _
          have h5 := hA_card k
          have h5' : ((A k).card : ℝ) * ((2 : ℝ)^(-(k + 1 : ℝ)))^(-s) ≤
              (C' * (P.card : ℝ) * ((2 : ℝ)^(-(k : ℝ)))^t) * ((2 : ℝ)^(-(k + 1 : ℝ)))^(-s) := by
            have h_pos : 0 ≤ ((2 : ℝ)^(-(k + 1 : ℝ)))^(-s) := by positivity
            have h5'' : ((A k).card : ℝ) ≤ C' * (P.card : ℝ) * ((2 : ℝ)^(-(k : ℝ)))^t := by
              have h := hA_card k
              linarith
            exact mul_le_mul_of_nonneg_right h5'' h_pos
          exact h5'
      _ = C' * (P.card : ℝ) * (2 : ℝ) ^ s * ∑ k ∈ Finset.range K, ratio ^ k := by
          have h6 : ∀ k : ℕ, ((2 : ℝ)^(-(k : ℝ)))^t * ((2 : ℝ)^(-(k + 1 : ℝ)))^(-s) =
              (2 : ℝ) ^ s * ratio ^ k := by
            intro k
            have h_pos1 : 0 < (2 : ℝ) := by norm_num
            have h_eq1 : ((2 : ℝ)^(-(k : ℝ)))^t = (2 : ℝ)^(-(k : ℝ) * t) := by
              rw [← Real.rpow_mul (by norm_num)] <;> ring
            have h_eq2 : ((2 : ℝ)^(-(k + 1 : ℝ)))^(-s) = (2 : ℝ)^((k + 1 : ℝ) * s) := by
              rw [← Real.rpow_mul (by norm_num)] <;> ring_nf <;> ring
            rw [h_eq1, h_eq2]
            have h_eq3 : (2 : ℝ)^(-(k : ℝ) * t) * (2 : ℝ)^((k + 1 : ℝ) * s) =
                (2 : ℝ)^(-(k : ℝ) * t + (k + 1 : ℝ) * s) := by
              rw [← Real.rpow_add h_pos1] <;> ring
            rw [h_eq3]
            have h_eq4 : -(k : ℝ) * t + (k + 1 : ℝ) * s = s + (k : ℝ) * (s - t) := by ring
            rw [h_eq4]
            have h_eq5 : (2 : ℝ)^(s + (k : ℝ) * (s - t)) = (2 : ℝ)^s * (2 : ℝ)^((k : ℝ) * (s - t)) := by
              rw [← Real.rpow_add h_pos1] <;> ring
            rw [h_eq5]
            have h_eq6 : (2 : ℝ)^((k : ℝ) * (s - t)) = ratio ^ k := by
              have h_comm : (k : ℝ) * (s - t) = (s - t) * (k : ℝ) := by ring
              rw [h_comm]
              have h_rpow_mul : (2 : ℝ)^((s - t) * (k : ℝ)) = ((2 : ℝ)^(s - t)) ^ (k : ℝ) := by
                rw [Real.rpow_mul (by norm_num)] <;> ring
              rw [h_rpow_mul]
              have h_nat : ((2 : ℝ)^(s - t)) ^ (k : ℝ) = ((2 : ℝ)^(s - t)) ^ k :=
                Real.rpow_natCast ((2 : ℝ)^(s - t)) k
              rw [h_nat]
              <;> rfl
            rw [h_eq6] <;> ring
          have h7 : ∀ k ∈ Finset.range K,
              C' * (P.card : ℝ) * ((2 : ℝ)^(-(k : ℝ)))^t * ((2 : ℝ)^(-(k + 1 : ℝ)))^(-s) =
              (C' * (P.card : ℝ) * (2 : ℝ) ^ s) * ratio ^ k := by
            intro k _
            have h8 := h6 k
            have h9 : C' * (P.card : ℝ) * ((2 : ℝ)^(-(k : ℝ)))^t * ((2 : ℝ)^(-(k + 1 : ℝ)))^(-s) =
                C' * (P.card : ℝ) * (((2 : ℝ)^(-(k : ℝ)))^t * ((2 : ℝ)^(-(k + 1 : ℝ)))^(-s)) := by ring
            rw [h9, h8] <;> ring
          have h10 : ∑ k ∈ Finset.range K, C' * (P.card : ℝ) * ((2 : ℝ)^(-(k : ℝ)))^t * ((2 : ℝ)^(-(k + 1 : ℝ)))^(-s) =
              ∑ k ∈ Finset.range K, (C' * (P.card : ℝ) * (2 : ℝ) ^ s) * ratio ^ k :=
            Finset.sum_congr rfl h7
          rw [h10, Finset.mul_sum] <;> ring
      _ ≤ C' * (P.card : ℝ) * (2 : ℝ) ^ s * (1 / (1 - ratio)) := by
          gcongr
          exact h_geom_sum K
      _ = C' * (P.card : ℝ) * (2 : ℝ) ^ s / (1 - ratio) := by ring
    have h_disj : ∀ q ∈ P.erase p, q ∈ Binf ∨ ∃ k < K, q ∈ A k := h_cover
    have h_main_sum : ∑ q ∈ P.erase p, Real.rpow (dist p q) (-s) ≤
        (Binf.card : ℝ) + C' * (P.card : ℝ) * (2 : ℝ) ^ s / (1 - ratio) := by
      have h_partition : P.erase p ⊆ Binf ∪ Finset.biUnion (Finset.range K) A := by
        intro q hq
        rcases h_disj q hq with (h | ⟨k, hk, hqA⟩)
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk, hqA⟩)
      have h_no_overlap : Disjoint Binf (Finset.biUnion (Finset.range K) A) := by
        rw [Finset.disjoint_left]
        intro q hqB hqU
        rcases Finset.mem_biUnion.mp hqU with ⟨k, _, hqA⟩
        have h1 : 1 < dist p q := (Finset.mem_filter.mp hqB).2
        have h2 : dist p q ≤ (2 : ℝ)^(-(k : ℝ)) := (Finset.mem_filter.mp hqA).2.2
        have h3 : (2 : ℝ)^(-(k : ℝ)) ≤ 1 := by
          have h4 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
          have h5 : -(k : ℝ) ≤ 0 := by exact neg_nonpos.mpr h4
          have h6 : (2 : ℝ)^(-(k : ℝ)) ≤ (2 : ℝ)^(0 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h5
          norm_num at h6 ⊢
          exact h6
        linarith
      have hA_disj : ∀ k ∈ Finset.range K, ∀ j ∈ Finset.range K, k ≠ j → Disjoint (A k) (A j) := by
        intro k hk j hj hkj
        have h_lt : k < j ∨ j < k := by omega
        rcases h_lt with (h_lt | h_lt)
        · -- k < j: 2^(-(k+1)) ≥ 2^(-j)
          have h6 : (k + 1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr h_lt
          have h7 : (2 : ℝ)^(-(k + 1 : ℝ)) ≥ (2 : ℝ)^(-(j : ℝ)) := by
            gcongr <;> linarith
          simp only [A, Finset.disjoint_left, Finset.mem_filter]
          rintro q ⟨_, hqk2, _⟩ ⟨_, _, hqj3⟩
          have h9 : (2 : ℝ)^(-(j : ℝ)) < dist p q := by
            calc (2 : ℝ)^(-(j : ℝ)) ≤ (2 : ℝ)^(-(k + 1 : ℝ)) := h7
              _ < dist p q := hqk2
          linarith
        · -- j < k: 2^(-(j+1)) ≥ 2^(-k)
          have h6 : (j + 1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr h_lt
          have h7 : (2 : ℝ)^(-(j + 1 : ℝ)) ≥ (2 : ℝ)^(-(k : ℝ)) := by
            gcongr <;> linarith
          simp only [A, Finset.disjoint_left, Finset.mem_filter]
          rintro q ⟨_, _, hqk3⟩ ⟨_, hqj2, _⟩
          have h9 : (2 : ℝ)^(-(k : ℝ)) < dist p q := by
            calc (2 : ℝ)^(-(k : ℝ)) ≤ (2 : ℝ)^(-(j + 1 : ℝ)) := h7
              _ < dist p q := hqj2
          linarith
      have h_nonneg : ∀ q ∈ Binf ∪ Finset.biUnion (Finset.range K) A, 0 ≤ Real.rpow (dist p q) (-s) := by
        intro q _
        exact Real.rpow_nonneg (by positivity) _
      calc ∑ q ∈ P.erase p, Real.rpow (dist p q) (-s)
        ≤ ∑ q ∈ Binf ∪ Finset.biUnion (Finset.range K) A, Real.rpow (dist p q) (-s) :=
          Finset.sum_le_sum_of_subset_of_nonneg h_partition (fun q _ _ => h_nonneg q ‹_›)
      _ = ∑ q ∈ Binf, Real.rpow (dist p q) (-s) +
            ∑ q ∈ Finset.biUnion (Finset.range K) A, Real.rpow (dist p q) (-s) := by
          rw [Finset.sum_union h_no_overlap]
      _ = ∑ q ∈ Binf, Real.rpow (dist p q) (-s) +
            ∑ k ∈ Finset.range K, ∑ q ∈ A k, Real.rpow (dist p q) (-s) := by
          rw [Finset.sum_biUnion hA_disj]
      _ ≤ (Binf.card : ℝ) + ∑ k ∈ Finset.range K, ∑ q ∈ A k, Real.rpow (dist p q) (-s) :=
          add_le_add hBinf_sum (le_refl _)
      _ ≤ (Binf.card : ℝ) + C' * (P.card : ℝ) * (2 : ℝ) ^ s / (1 - ratio) := by linarith
    have hBinf_card : (Binf.card : ℝ) ≤ C' * (2 * R) ^ t * (P.card : ℝ) := by
      by_cases h2 : δ ≤ 2 * R
      · have h1 : Binf ⊆ P.filter (fun q => dist p q ≤ 2 * R) := by
          intro q hq
          have hqS : q ∈ P := (Finset.mem_filter.mp hq).1
          have h2 : dist p q ≤ ‖p‖ + ‖q‖ := dist_le_norm_add_norm p q
          have h3 : ‖p‖ ≤ R := hP_bdd p hp
          have h4 : ‖q‖ ≤ R := hP_bdd q hqS
          have h5 : dist p q ≤ 2 * R := by linarith
          exact Finset.mem_filter.mpr ⟨hqS, h5⟩
        have h6 : Binf.card ≤ (P.filter (fun q => dist p q ≤ 2 * R)).card := Finset.card_le_card h1
        have h7 : (Binf.card : ℝ) ≤ ((P.filter (fun q => dist p q ≤ 2 * R)).card : ℝ) := by exact_mod_cast h6
        have h8 := h_ball' p hp (2 * R) h2
        exact le_trans h7 h8
      · have h8 : 2 * R < δ := by linarith
        have h9 : Binf = ∅ := by
          by_contra h10
          have h10' : Binf.card ≠ 0 := by simpa [Finset.card_eq_zero] using h10
          have h11 : 0 < Binf.card := Nat.pos_of_ne_zero h10'
          rcases Finset.card_pos.mp h11 with ⟨q, hq⟩
          have hqS : q ∈ P := (Finset.mem_filter.mp hq).1
          have hqne : q ≠ p := by
            intro h
            have h15 : dist p q = 0 := by rw [h] <;> simp
            have h16 : 1 < dist p q := (Finset.mem_filter.mp hq).2
            rw [h15] at h16 <;> norm_num at h16
          have h12 : δ ≤ dist p q := hP_sep' p hp q hqS (Ne.symm hqne)
          have h13 : dist p q ≤ 2 * R := by
            have h14 : dist p q ≤ ‖p‖ + ‖q‖ := dist_le_norm_add_norm p q
            linarith [hP_bdd p hp, hP_bdd q hqS]
          linarith
        rw [h9] <;> simp <;> positivity
    have h_final : (Binf.card : ℝ) + C' * (P.card : ℝ) * (2 : ℝ) ^ s / (1 - ratio) ≤
        M0 * (P.card : ℝ) := by
      dsimp only [M0]
      have h1 : C' * (P.card : ℝ) * (2 : ℝ) ^ s / (1 - ratio) =
          C' * ((2 : ℝ) ^ s / (1 - ratio)) * (P.card : ℝ) := by ring
      rw [h1]
      have h2 : (Binf.card : ℝ) ≤ C' * (2 * R) ^ t * (P.card : ℝ) := hBinf_card
      linarith
    exact le_trans h_main_sum h_final
  have h_total : ∑ p ∈ P, ∑ p' ∈ P.erase p, Real.rpow (dist p p') (-s) ≤
      M0 * (P.card : ℝ)^2 := by
    calc ∑ p ∈ P, ∑ p' ∈ P.erase p, Real.rpow (dist p p') (-s)
      ≤ ∑ p ∈ P, M0 * (P.card : ℝ) := Finset.sum_le_sum (fun p hp => h_point_bound p hp)
    _ = M0 * (P.card : ℝ)^2 := by
      have h_sum : ∑ p ∈ P, M0 * (P.card : ℝ) = M0 * (P.card : ℝ) * (P.card : ℝ) := by
        have h : ∑ p ∈ P, M0 * (P.card : ℝ) = (P.card : ℝ) * (M0 * (P.card : ℝ)) := by
          simpa [Finset.sum_const, smul_eq_mul] using rfl
        rw [h] <;> ring
      rw [h_sum] <;> ring
  have hK_pack_pos : 0 < K_pack := by
    have hC'_pos : 0 < C' := by
      have hP_nonempty : P.Nonempty := hP_set.1
      rcases hP_nonempty with ⟨p, hp⟩
      have h5 : p ∈ P.filter (fun q => dist p q ≤ δ) := by
        have h51 : dist p p ≤ δ := by
          have h52 : dist p p = 0 := by simp
          rw [h52] <;> linarith
        exact Finset.mem_filter.mpr ⟨hp, h51⟩
      have h6 : 0 < (P.filter (fun q => dist p q ≤ δ)).card := Finset.card_pos.mpr ⟨p, h5⟩
      have h7 : ((P.filter (fun q => dist p q ≤ δ)).card : ℝ) ≤ C' * δ ^ t * (P.card : ℝ) := h_ball' p hp δ (by linarith)
      have h8 : (0 : ℝ) < ((P.filter (fun q => dist p q ≤ δ)).card : ℝ) := by exact_mod_cast h6
      have h9 : 0 < δ ^ t := Real.rpow_pos_of_pos hδ_pos t
      have h10 : 0 < (P.card : ℝ) := by exact_mod_cast (Finset.card_pos.mpr hP_set.1)
      have h11 : 0 < δ ^ t * (P.card : ℝ) := mul_pos h9 h10
      have h12 : 0 < C' * (δ ^ t * (P.card : ℝ)) := by
        calc 0 < ((P.filter (fun q => dist p q ≤ δ)).card : ℝ) := h8
           _ ≤ C' * δ ^ t * (P.card : ℝ) := h7
           _ = C' * (δ ^ t * (P.card : ℝ)) := by ring
      exact (mul_pos_iff_of_pos_right h11).mp h12
    have h : C' = C_P * (K_pack : ℝ) := by rfl
    rw [h] at hC'_pos
    have hK_pack_pos' : 0 < (K_pack : ℝ) := (mul_pos_iff_of_pos_left hCP_pos).mp hC'_pos
    exact Nat.cast_pos.mp hK_pack_pos'
  have hK_lower : (M0 / C_P) ≥ (2 * R) ^ t := by
    dsimp only [M0, C']
    have h1 : (M0 / C_P) = (K_pack : ℝ) * ((2 * R) ^ t + (2 : ℝ) ^ s / (1 - ratio)) := by
      field_simp [hCP_pos.ne'] <;> ring
    rw [h1]
    have h2 : (K_pack : ℝ) ≥ 1 := by exact_mod_cast (Nat.succ_le_iff.mpr hK_pack_pos)
    have h3 : (2 : ℝ) ^ s / (1 - ratio) ≥ 0 := by positivity
    have h4 : (K_pack : ℝ) * ((2 * R) ^ t + (2 : ℝ) ^ s / (1 - ratio)) ≥
        1 * ((2 * R) ^ t) := by gcongr <;> linarith
    simpa using h4
  have hK_eq : M0 / C_P = plane_energy_constant s t R := by
    have h1 : M0 / C_P = (K_pack : ℝ) * ((2 * R) ^ t + (2 : ℝ) ^ s / (1 - ratio)) := by
      dsimp only [M0, C']
      field_simp [hCP_pos.ne'] <;> ring
    have h2 : plane_energy_constant s t R = (K_pack : ℝ) * ((2 * R) ^ t + (2 : ℝ) ^ s / (1 - ratio)) := by
      simp [plane_energy_constant, plane_energy_K_pack]
      <;> rfl
    rw [h1, h2]
  refine ⟨M0 / C_P, by positivity, hK_lower, hK_eq, ?_⟩
  · -- Total bound
    have h_final2 : M0 * (P.card : ℝ)^2 ≤ (M0 / C_P) * C_P * (P.card : ℝ)^2 := by
      have h_div : (M0 / C_P) * C_P = M0 := by
        field_simp [hCP_pos.ne'] <;> ring
      rw [h_div]
      <;> exact le_refl _
    exact le_trans h_total h_final2

end DirecretisedFurstenbergEstimate.MainAppendix
