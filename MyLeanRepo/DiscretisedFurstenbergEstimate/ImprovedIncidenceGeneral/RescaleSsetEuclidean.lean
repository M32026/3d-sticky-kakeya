module

/-
  S-set rescaling for EuclideanPlane, including translation.

  Provides:
  1. `rescale_sset_euclidean`: pure scaling c•P
  2. `translate_sset_euclidean`: translation by a vector
  3. `transfer_sset_ballToSquare`: specific map (p+1)/2

  This fills the transfer_sset_ballToSquare gap in Step1_2_Assembly.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.Basics
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal


noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CoveringUtils

/-- Covering number is invariant under scaling: covering at scale c*δ of c•A
    equals covering at scale δ of A. -/
lemma externalCoveringNumber_smul' {c : ℝ} (hc_pos : 0 < c) {δ : ℝ} (hδ_pos : 0 < δ)
    {A : Set E2} :
    Metric.externalCoveringNumber (c * δ).toNNReal ((fun x : E2 => c • x) '' A) =
    Metric.externalCoveringNumber δ.toNNReal A := by
  set f : E2 → E2 := fun x => c • x with hf_def
  set g : E2 → E2 := fun x => c⁻¹ • x with hg_def
  let K : NNReal := ⟨c, hc_pos.le⟩
  let Kinv : NNReal := ⟨c⁻¹, by positivity⟩
  have hK_coe : (K : ℝ) = c := by exact_mod_cast rfl
  have hKinv_coe : (Kinv : ℝ) = c⁻¹ := by exact_mod_cast rfl
  have h_lip1 : LipschitzWith K f :=
    LipschitzWith.of_dist_le_mul fun x y => by
      have h : dist (f x) (f y) = c * dist x y := by
        have h1 : f x - f y = c • (x - y) := by
          simp [hf_def, smul_sub] <;> abel
        rw [dist_eq_norm, dist_eq_norm, h1, norm_smul]
        <;> rw [Real.norm_eq_abs, abs_of_pos hc_pos] <;> ring
      rw [h]
      <;> simp [hK_coe] <;> ring
  have h_lip2 : LipschitzWith Kinv g :=
    LipschitzWith.of_dist_le_mul fun x y => by
      have h : dist (g x) (g y) = c⁻¹ * dist x y := by
        have h1 : g x - g y = c⁻¹ • (x - y) := by
          simp [hg_def, smul_sub] <;> abel
        rw [dist_eq_norm, dist_eq_norm, h1, norm_smul]
        <;> rw [Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < c⁻¹ from by positivity)] <;> ring
      rw [h] <;> simp [hKinv_coe] <;> ring
  have hKδ : K * δ.toNNReal = (c * δ).toNNReal := by
    apply NNReal.coe_injective
    simp [hK_coe, Real.toNNReal_of_nonneg hδ_pos.le,
          Real.toNNReal_of_nonneg (mul_pos hc_pos hδ_pos).le] <;> ring
  have h1 : Metric.externalCoveringNumber (c * δ).toNNReal (f '' A) ≤
      Metric.externalCoveringNumber δ.toNNReal A := by
    rw [← hKδ]
    exact externalCoveringNumber_image_lipschitz (hf := h_lip1)
  have h2 : Metric.externalCoveringNumber δ.toNNReal A ≤
      Metric.externalCoveringNumber (c * δ).toNNReal (f '' A) := by
    have hgf : ∀ (x : E2), g (f x) = x := by
      intro x
      have h1 : g (f x) = c⁻¹ • (c • x) := by
        simp [hf_def, hg_def] <;> rfl
      rw [h1]
      have h2 : c⁻¹ • (c • x) = (c⁻¹ * c) • x := by rw [smul_smul]
      rw [h2]
      have h3 : c⁻¹ * c = 1 := by field_simp [hc_pos.ne'] <;> ring
      rw [h3]
      simp
    have h3 : g '' (f '' A) = A := by
      ext z
      simp only [Set.mem_image]
      constructor
      · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        rw [hgf x] <;> exact hx
      · intro hz
        exact ⟨f z, ⟨z, hz, rfl⟩, hgf z⟩
    have h4 : Metric.externalCoveringNumber (Kinv * (c * δ).toNNReal) (g '' (f '' A)) ≤
        Metric.externalCoveringNumber (c * δ).toNNReal (f '' A) :=
      externalCoveringNumber_image_lipschitz (hf := h_lip2)
    have h5 : Kinv * (c * δ).toNNReal = δ.toNNReal := by
      apply NNReal.coe_injective
      have h_coe_mul : (↑(Kinv * (c * δ).toNNReal) : ℝ) =
          (↑Kinv : ℝ) * (↑(c * δ).toNNReal : ℝ) :=
        NNReal.coe_mul Kinv (c * δ).toNNReal
      have h_coe1 : (↑Kinv : ℝ) = c⁻¹ := hKinv_coe
      have h_coe2 : (↑(c * δ).toNNReal : ℝ) = c * δ := by
        simp [Real.toNNReal_of_nonneg (mul_pos hc_pos hδ_pos).le]
      have h_coe3 : (↑δ.toNNReal : ℝ) = δ := by
        simp [Real.toNNReal_of_nonneg hδ_pos.le]
      calc (↑(Kinv * (c * δ).toNNReal) : ℝ)
        = (↑Kinv : ℝ) * (↑(c * δ).toNNReal : ℝ) := h_coe_mul
      _ = c⁻¹ * (c * δ) := by rw [h_coe1, h_coe2]
      _ = δ := by field_simp [hc_pos.ne'] <;> ring
      _ = (↑δ.toNNReal : ℝ) := h_coe3.symm
    rw [h5] at h4
    rw [h3] at h4
    exact h4
  exact le_antisymm h1 h2

/-- Intersection of scaled set with closed ball. -/
lemma smul_closedBall_inter' {c : ℝ} (hc_pos : 0 < c) {P : Set E2} {y : E2} {r : ℝ}
    (hr : 0 ≤ r) :
    ((fun x : E2 => c • x) '' P) ∩ Metric.closedBall y r =
    (fun x : E2 => c • x) '' (P ∩ Metric.closedBall (c⁻¹ • y) (r / c)) := by
  set f : E2 → E2 := fun x => c • x with hf_def
  have h_smul_inv : ∀ (z : E2), c • (c⁻¹ • z) = z := by
    intro z
    have h : c • (c⁻¹ • z) = (c * c⁻¹) • z := by
      rw [smul_smul]
    rw [h]
    have h2 : c * c⁻¹ = 1 := by
      field_simp [hc_pos.ne'] <;> ring
    rw [h2, one_smul]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hball⟩
    have hdist : dist (f x) y ≤ r := by simpa [Metric.mem_closedBall] using hball
    have h_eq : dist (f x) y = c * dist x (c⁻¹ • y) := by
      have h1 : f x - y = c • (x - c⁻¹ • y) := by
        have h2 : f x = c • x := by simp [hf_def]
        rw [h2]
        have h3 : c • x - y = c • x - c • (c⁻¹ • y) := by rw [h_smul_inv y]
        rw [h3, ← smul_sub]
      rw [dist_eq_norm, dist_eq_norm, h1, norm_smul]
      <;> rw [Real.norm_eq_abs, abs_of_pos hc_pos] <;> ring
    have h4 : c * dist x (c⁻¹ • y) ≤ r := by rw [h_eq] at hdist; exact hdist
    have h5 : dist x (c⁻¹ • y) ≤ r / c := by
      calc dist x (c⁻¹ • y)
        = (c * dist x (c⁻¹ • y)) / c := by field_simp [hc_pos.ne'] <;> ring
      _ ≤ r / c := by gcongr
    exact ⟨x, ⟨hx, by simpa [Metric.mem_closedBall] using h5⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hball⟩, rfl⟩
    have hdist : dist x (c⁻¹ • y) ≤ r / c := by simpa [Metric.mem_closedBall] using hball
    have h_eq : dist (f x) y = c * dist x (c⁻¹ • y) := by
      have h1 : f x - y = c • (x - c⁻¹ • y) := by
        have h2 : f x = c • x := by simp [hf_def]
        rw [h2]
        have h3 : c • x - y = c • x - c • (c⁻¹ • y) := by rw [h_smul_inv y]
        rw [h3, ← smul_sub]
      rw [dist_eq_norm, dist_eq_norm, h1, norm_smul]
      <;> rw [Real.norm_eq_abs, abs_of_pos hc_pos] <;> ring
    have h5 : dist (f x) y ≤ r := by
      rw [h_eq]
      have h6 : c * dist x (c⁻¹ • y) ≤ c * (r / c) := by gcongr
      have h7 : c * (r / c) = r := by
        field_simp [hc_pos.ne'] <;> ring
      rw [h7] at h6
      exact h6
    exact ⟨⟨x, hx, rfl⟩, by simpa [Metric.mem_closedBall] using h5⟩

/-- If P is a (δ,s,C)-set in EuclideanSpace ℝ (Fin 2), then c•P is a
    (cδ, s, C·c^{-s})-set for c > 0. -/
lemma rescale_sset_euclidean {δ s C : ℝ} {P : Set E2} {c : ℝ}
    (hc_pos : 0 < c) (hP : IsDeltaSSet δ s C P) :
    IsDeltaSSet (c * δ) s (C * c ^ (-s)) ((fun x : E2 => c • x) '' P) := by
  rcases hP with ⟨hP_nonempty, hδ_pos, hC_pos, hs_nonneg, hmain⟩
  have hcδ_pos : 0 < c * δ := mul_pos hc_pos hδ_pos
  have hC'_pos : 0 < C * c ^ (-s) := by positivity
  set f : E2 → E2 := fun x => c • x with hf_def
  set P' := f '' P with hP'_def
  have hP'_nonempty : P'.Nonempty := hP_nonempty.image f

  have h_cover_eq : ∀ (A : Set E2),
      Metric.externalCoveringNumber (c * δ).toNNReal (f '' A) =
      Metric.externalCoveringNumber δ.toNNReal A := by
    intro A
    exact externalCoveringNumber_smul' hc_pos hδ_pos (A := A)

  have h_inter_eq : ∀ (y : E2) (r : ℝ), 0 ≤ r →
      P' ∩ Metric.closedBall y r =
      f '' (P ∩ Metric.closedBall (c⁻¹ • y) (r / c)) := by
    intro y r hr
    exact smul_closedBall_inter' hc_pos (hr := hr)

  refine' ⟨hP'_nonempty, hcδ_pos, hC'_pos, hs_nonneg, _⟩
  intro y r hr
  have h_r_nonneg : 0 ≤ r := by linarith [hcδ_pos]
  have h_inter : P' ∩ Metric.closedBall y r =
      f '' (P ∩ Metric.closedBall (c⁻¹ • y) (r / c)) :=
    h_inter_eq y r h_r_nonneg
  rw [h_inter]
  have h3 : Metric.externalCoveringNumber (c * δ).toNNReal
      (f '' (P ∩ Metric.closedBall (c⁻¹ • y) (r / c))) =
      Metric.externalCoveringNumber δ.toNNReal
        (P ∩ Metric.closedBall (c⁻¹ • y) (r / c)) :=
    h_cover_eq (P ∩ Metric.closedBall (c⁻¹ • y) (r / c))
  rw [h3]
  have h4 : δ ≤ r / c := by
    have h41 : (c * δ) / c ≤ r / c := by
      apply div_le_div_of_nonneg_right hr (by linarith)
    have h42 : (c * δ) / c = δ := by
      field_simp [hc_pos.ne'] <;> ring
    rw [h42] at h41
    exact h41
  have h5 : Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall (c⁻¹ • y) (r / c)) ≤
      ENNReal.ofReal C * (ENNReal.ofReal (r / c)) ^ s *
      Metric.externalCoveringNumber δ.toNNReal P := hmain (c⁻¹ • y) (r / c) h4
  have h6 : Metric.externalCoveringNumber δ.toNNReal P =
      Metric.externalCoveringNumber (c * δ).toNNReal P' := by
    rw [← h_cover_eq P] <;> rfl
  have h7 : Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall (c⁻¹ • y) (r / c)) ≤
      ENNReal.ofReal (C * c ^ (-s)) * (ENNReal.ofReal r) ^ s *
      Metric.externalCoveringNumber (c * δ).toNNReal P' := by
    calc Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall (c⁻¹ • y) (r / c))
      ≤ ENNReal.ofReal C * (ENNReal.ofReal (r / c)) ^ s *
          Metric.externalCoveringNumber δ.toNNReal P := h5
    _ = ENNReal.ofReal C * (ENNReal.ofReal (r / c)) ^ s *
          Metric.externalCoveringNumber (c * δ).toNNReal P' := by rw [h6]
    _ = ENNReal.ofReal (C * c ^ (-s)) * (ENNReal.ofReal r) ^ s *
          Metric.externalCoveringNumber (c * δ).toNNReal P' := by
        have h10 : ENNReal.ofReal C * (ENNReal.ofReal (r / c)) ^ s =
            ENNReal.ofReal (C * c ^ (-s)) * (ENNReal.ofReal r) ^ s := by
          have h_div : r / c = r * c⁻¹ := by
            field_simp [hc_pos.ne'] <;> ring
          have h11 : ENNReal.ofReal (r / c) = ENNReal.ofReal r * ENNReal.ofReal (c⁻¹) := by
            rw [h_div]
            exact ENNReal.ofReal_mul (show 0 ≤ r from by linarith)
          rw [h11]
          have h12 : (ENNReal.ofReal r * ENNReal.ofReal (c⁻¹)) ^ s =
              (ENNReal.ofReal r) ^ s * (ENNReal.ofReal (c⁻¹)) ^ s :=
            ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal r) (ENNReal.ofReal (c⁻¹)) hs_nonneg
          rw [h12]
          have h13 : c ^ (-s) = (c⁻¹) ^ s := by
            have h131 : c ^ (-s) = (c ^ s)⁻¹ := by
              rw [Real.rpow_neg (by linarith)] <;> ring
            have h132 : (c⁻¹) ^ s = (c ^ s)⁻¹ := by
              rw [← Real.inv_rpow (by linarith)] <;> ring
            rw [h131, h132]
          have h14 : ENNReal.ofReal (c ^ (-s)) = (ENNReal.ofReal (c⁻¹)) ^ s := by
            rw [h13]
            exact (ENNReal.ofReal_rpow_of_pos (show 0 < c⁻¹ from by positivity)).symm
          have h15 : ENNReal.ofReal (C * c ^ (-s)) =
              ENNReal.ofReal C * ENNReal.ofReal (c ^ (-s)) :=
            ENNReal.ofReal_mul (show 0 ≤ C from by linarith)
          rw [h15, h14] <;> ring
        rw [h10] <;> ring
  exact h7

/-- Translation by a fixed vector preserves the S-set property. -/
lemma translate_sset_euclidean {δ s C : ℝ} {P : Set E2} {v : E2}
    (hP : IsDeltaSSet δ s C P) :
    IsDeltaSSet δ s C ((fun x : E2 => x + v) '' P) := by
  rcases hP with ⟨hP_nonempty, hδ_pos, hC_pos, hs_nonneg, hmain⟩
  set t : E2 → E2 := fun x => x + v with ht_def
  set tinv : E2 → E2 := fun y => y - v with htinv_def
  set P' := t '' P with hP'_def
  have hP'_nonempty : P'.Nonempty := hP_nonempty.image t

  have h_dist_t : ∀ (x y : E2), dist (t x) (t y) = dist x y := by
    intro x y
    simp [ht_def, dist_eq_norm] <;> abel
  have h_dist_tinv : ∀ (x y : E2), dist (tinv x) (tinv y) = dist x y := by
    intro x y
    simp [htinv_def, dist_eq_norm] <;> abel

  let K1 : NNReal := 1
  have h_lip1 : LipschitzWith K1 t :=
    LipschitzWith.of_dist_le_mul fun x y => by
      have h : (K1 : ℝ) * dist x y = dist x y := by simp [K1]
      rw [h_dist_t x y, h]
  have h_lip2 : LipschitzWith K1 tinv :=
    LipschitzWith.of_dist_le_mul fun x y => by
      have h : (K1 : ℝ) * dist x y = dist x y := by simp [K1]
      rw [h_dist_tinv x y, h]

  have h_cover_eq : ∀ (A : Set E2),
      Metric.externalCoveringNumber δ.toNNReal (t '' A) =
      Metric.externalCoveringNumber δ.toNNReal A := by
    intro A
    have h1 : Metric.externalCoveringNumber (K1 * δ.toNNReal) (t '' A) ≤
        Metric.externalCoveringNumber δ.toNNReal A :=
      externalCoveringNumber_image_lipschitz (hf := h_lip1)
    have hK1 : K1 * δ.toNNReal = δ.toNNReal := by simp [K1]
    rw [hK1] at h1
    have h2 : Metric.externalCoveringNumber (K1 * δ.toNNReal) (tinv '' (t '' A)) ≤
        Metric.externalCoveringNumber δ.toNNReal (t '' A) :=
      externalCoveringNumber_image_lipschitz (hf := h_lip2)
    rw [hK1] at h2
    have h3 : tinv '' (t '' A) = A := by
      ext z
      simp only [Set.mem_image]
      constructor
      · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        simpa [ht_def, htinv_def] using hx
      · intro hz
        exact ⟨t z, ⟨z, hz, rfl⟩, by simp [ht_def, htinv_def]⟩
    rw [h3] at h2
    exact le_antisymm h1 h2

  have h_inter_eq : ∀ (y : E2) (r : ℝ),
      P' ∩ Metric.closedBall y r =
      t '' (P ∩ Metric.closedBall (y - v) r) := by
    intro y r
    ext z
    simp only [Set.mem_inter_iff, Set.mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hball⟩
      have hdist : dist (t x) y ≤ r := by simpa [Metric.mem_closedBall] using hball
      have h4 : dist x (y - v) ≤ r := by
        have h : dist (t x) y = ‖x + v - y‖ := by
          simp [ht_def, dist_eq_norm] <;> abel
        rw [h] at hdist
        have h_eq1 : x + v - y = x - (y - v) := by abel
        rw [h_eq1] at hdist
        simpa [dist_eq_norm] using hdist
      exact ⟨x, ⟨hx, by simpa [Metric.mem_closedBall] using h4⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hball⟩, rfl⟩
      have hdist : dist x (y - v) ≤ r := by simpa [Metric.mem_closedBall] using hball
      have h5 : dist (t x) y ≤ r := by
        have h : dist x (y - v) = ‖x - (y - v)‖ := by
          simp [dist_eq_norm]
        rw [h] at hdist
        have h_eq2 : x + v - y = x - (y - v) := by abel
        have h' : dist (t x) y = ‖x + v - y‖ := by
          simp [ht_def, dist_eq_norm] <;> abel
        rw [h']
        rw [h_eq2]
        exact hdist
      exact ⟨⟨x, hx, rfl⟩, by simpa [Metric.mem_closedBall] using h5⟩

  refine' ⟨hP'_nonempty, hδ_pos, hC_pos, hs_nonneg, _⟩
  intro y r hr
  have h_inter : P' ∩ Metric.closedBall y r =
      t '' (P ∩ Metric.closedBall (y - v) r) := h_inter_eq y r
  rw [h_inter]
  have h3 := h_cover_eq (P ∩ Metric.closedBall (y - v) r)
  rw [h3]
  have h4 := hmain (y - v) r hr
  have h5 := h_cover_eq P
  rw [h5] at *
  exact h4

/-- Transfer S-set under ballToSquareMap f(p) = (p + 1) / 2.
    If P is a (δ,t,C)-set, then f(P) is a (δ/2, t, C·2^t)-set. -/
lemma transfer_sset_ballToSquare {δ t C : ℝ} {P : Set E2}
    (hP : IsDeltaSSet δ t C P) :
    IsDeltaSSet (δ / 2) t (C * (2 : ℝ) ^ t)
      ((fun x : E2 => (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • onesVec) '' P) := by
  let Q : Set E2 := (fun x : E2 => x + onesVec) '' P
  have hQ_sset : IsDeltaSSet δ t C Q := translate_sset_euclidean hP
  have h_c_pos : (0 : ℝ) < 1 / 2 := by norm_num
  have h_rescale := rescale_sset_euclidean h_c_pos hQ_sset
  have h_scale_eq : (1 / 2 : ℝ) * δ = δ / 2 := by ring
  have h_const_eq : C * (1 / 2 : ℝ) ^ (-t) = C * (2 : ℝ) ^ t := by
    have h : (1 / 2 : ℝ) ^ (-t) = (2 : ℝ) ^ t := by
      have h1 : (1 / 2 : ℝ) ^ (-t) = ((1 / 2 : ℝ) ^ t)⁻¹ := by
        rw [Real.rpow_neg (by norm_num)] <;> ring
      have h2 : (2 : ℝ) ^ t = ((1 / 2 : ℝ) ^ t)⁻¹ := by
        have h_pos : 0 ≤ (1 / 2 : ℝ) := by norm_num
        have h22 : ((1 / 2 : ℝ)⁻¹) ^ t = ((1 / 2 : ℝ) ^ t)⁻¹ := Real.inv_rpow h_pos t
        have h_eq : (2 : ℝ) = (1 / 2 : ℝ)⁻¹ := by norm_num
        have h23 : (2 : ℝ) ^ t = ((1 / 2 : ℝ)⁻¹) ^ t :=
          congr_arg (fun x : ℝ => x ^ t) h_eq
        rw [h23, h22]
      rw [h1, h2]
    rw [h]
  rw [h_scale_eq, h_const_eq] at h_rescale
  have h_eq : ((fun x : E2 => (1 / 2 : ℝ) • x) '' Q) =
      ((fun x : E2 => (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • onesVec) '' P) := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, hy, hz⟩
      rcases hy with ⟨x, hx, rfl⟩
      refine' ⟨x, hx, _⟩
      have h_smul : (1 / 2 : ℝ) • (x + onesVec) = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • onesVec :=
        smul_add (1 / 2 : ℝ) x onesVec
      have h_goal : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • onesVec = z := by
        calc (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • onesVec
          = (1 / 2 : ℝ) • (x + onesVec) := h_smul.symm
        _ = z := hz
      exact h_goal
    · rintro ⟨x, hx, hz⟩
      refine' ⟨x + onesVec, ⟨x, hx, rfl⟩, _⟩
      have h_smul : (1 / 2 : ℝ) • (x + onesVec) = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • onesVec :=
        smul_add (1 / 2 : ℝ) x onesVec
      have h_goal : (1 / 2 : ℝ) • (x + onesVec) = z := by
        calc (1 / 2 : ℝ) • (x + onesVec)
          = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • onesVec := h_smul
        _ = z := hz
      exact h_goal
  rw [h_eq] at h_rescale
  exact h_rescale

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
