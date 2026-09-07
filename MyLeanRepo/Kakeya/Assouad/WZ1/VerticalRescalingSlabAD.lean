import MyLeanRepo.Kakeya.Assouad.WZ1.VerticalRescalingSlabADStatement
import MyLeanRepo.Kakeya.Assouad.WZ1.VerticalRescalingADProof

/-!
WZ1 Proposition 21: transport the paper-faithful global slab AD certificate
through the centered vertical rescaling.
-/

namespace Kakeya.Assouad

open Matrix

-- ===== Helper lemmas =====

private lemma slab_inner_product_identity
    (g : SlopeFunction) (c h M : ℝ) (hh : 0 < h) (p : Point3) :
    inner ℝ (wz1VerticalRescalingMap c h M p)
        (globalGrainDirection ((wz1VerticalRescaledSlope g c h M)
          ((wz1VerticalRescalingMap c h M p) (2 : Fin 3)))) =
    inner ℝ p (globalGrainDirection (g (p (2 : Fin 3)))) / M^2 := by
  let Φ := wz1VerticalRescalingMap c h M
  let gNew := wz1VerticalRescaledSlope g c h M
  have hΦ2 : (Φ p) (2 : Fin 3) = (p (2 : Fin 3) - c) / h := by
    simp [Φ, wz1VerticalRescalingMap, point3]
  have h_affine : c + h * ((Φ p) (2 : Fin 3)) = p (2 : Fin 3) := by
    rw [hΦ2]; field_simp [hh.ne']; ring
  have h_slope : gNew ((Φ p) (2 : Fin 3)) = g (p (2 : Fin 3)) / M := by
    have h1 : gNew ((Φ p) (2 : Fin 3)) = g (c + h * ((Φ p) (2 : Fin 3))) / M := by
      rfl
    rw [h1, h_affine]
  have h_eval : ∀ (q : Point3) (m : ℝ),
      inner ℝ q (globalGrainDirection m) = q 0 + m * q 1 := by
    intro q m
    have h_linearity : inner ℝ q (globalGrainDirection m) =
        inner ℝ q (EuclideanSpace.single (0 : Fin 3) 1) +
        m * inner ℝ q (EuclideanSpace.single (1 : Fin 3) 1) := by
      simp [globalGrainDirection, inner_add_right, inner_smul_right]
    have h_basis0 : (EuclideanSpace.basisFun (Fin 3) ℝ) 0 = EuclideanSpace.single (0 : Fin 3) 1 :=
      EuclideanSpace.basisFun_apply (Fin 3) ℝ 0
    have h_basis1 : (EuclideanSpace.basisFun (Fin 3) ℝ) 1 = EuclideanSpace.single (1 : Fin 3) 1 :=
      EuclideanSpace.basisFun_apply (Fin 3) ℝ 1
    have h_coord0 : inner ℝ q (EuclideanSpace.single (0 : Fin 3) 1) = q 0 := by
      rw [←h_basis0]; exact EuclideanSpace.inner_basisFun_real (Fin 3) q 0
    have h_coord1 : inner ℝ q (EuclideanSpace.single (1 : Fin 3) 1) = q 1 := by
      rw [←h_basis1]; exact EuclideanSpace.inner_basisFun_real (Fin 3) q 1
    rw [h_linearity, h_coord0, h_coord1]
  have h_p0 : (Φ p) 0 = p 0 / M^2 := by
    simp [Φ, wz1VerticalRescalingMap, point3]
  have h_p1 : (Φ p) 1 = p 1 / M := by
    simp [Φ, wz1VerticalRescalingMap, point3]
  let m_new := gNew ((Φ p) (2 : Fin 3))
  let m_old := g (p (2 : Fin 3))
  have hm : m_new = m_old / M := h_slope
  calc
    inner ℝ (Φ p) (globalGrainDirection m_new)
      = (Φ p) 0 + m_new * (Φ p) 1 := h_eval _ _
    _ = p 0 / M^2 + (m_old / M) * (p 1 / M) := by
      rw [h_p0, h_p1, hm]
    _ = (p 0 + m_old * p 1) / M^2 := by ring
    _ = inner ℝ p (globalGrainDirection m_old) / M^2 := by
      rw [h_eval p m_old]

private lemma rescaling_map_injective
    (c h M : ℝ) (hh : 0 < h) (hM : 1 ≤ M) :
    Function.Injective (wz1VerticalRescalingMap c h M) := by
  intro x y heq
  have hM2_pos : 0 < M^2 := by positivity
  have hM_pos : 0 < M := by linarith
  have h0 : x 0 = y 0 := by
    have h := congr_arg (fun q : Point3 => q 0) heq
    have h' : x 0 / M^2 = y 0 / M^2 := by simpa [wz1VerticalRescalingMap, point3] using h
    field_simp [hM2_pos.ne'] at h' ⊢ <;> linarith
  have h1 : x 1 = y 1 := by
    have h := congr_arg (fun q : Point3 => q 1) heq
    have h' : x 1 / M = y 1 / M := by simpa [wz1VerticalRescalingMap, point3] using h
    field_simp [hM_pos.ne'] at h' ⊢ <;> linarith
  have h2 : x 2 = y 2 := by
    have h_eq1 : (x 2 - c) / h = (y 2 - c) / h := by
      have h := congr_arg (fun q : Point3 => q 2) heq
      simpa [wz1VerticalRescalingMap, point3] using h
    field_simp [hh.ne'] at h_eq1 ⊢ <;> linarith
  have h_all : ∀ (j : Fin 3), x j = y j := by
    intro j; fin_cases j <;> assumption
  have h_eq : x = y := by
    ext j
    exact h_all j
  exact h_eq

private lemma slab_pullback
    (_g : SlopeFunction) (c h M delta : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 1 ≤ M) (hdelta : 0 < delta)
    (h_window : ∀ t ∈ Set.Icc (-1 : ℝ) 1, c + h * t ∈ Set.Icc (-1 : ℝ) 1)
    (E : Set Point3) (t : ℝ) (p : Point3)
    (hq_slab : wz1VerticalRescalingMap c h M p ∈
      globalGrainSlab (wz1VerticalRescalingMap c h M '' E) t (delta / M^2)) :
    p ∈ globalGrainSlab E (c + h * t) delta := by
  let Φ := wz1VerticalRescalingMap c h M
  let delta' := delta / M^2
  have hM2_pos : 0 < M^2 := by positivity
  have hΦ2 : ∀ (x : Point3), (Φ x) (2 : Fin 3) = (x (2 : Fin 3) - c) / h := by
    intro x; simp [Φ, wz1VerticalRescalingMap, point3]
  have h_inj : Function.Injective Φ := rescaling_map_injective c h M hh hM
  rcases hq_slab with ⟨⟨h_q_in_image, h_q_height_mem⟩, h_q_window_mem⟩
  have h_q_height : t - delta' ≤ (Φ p) 2 ∧ (Φ p) 2 ≤ t + delta' := by
    simpa [Set.mem_setOf_eq] using h_q_height_mem
  have h_q_window : -1 ≤ (Φ p) 2 ∧ (Φ p) 2 ≤ 1 := by
    simpa [Set.mem_setOf_eq] using h_q_window_mem
  have h_pE : p ∈ E := by
    rcases h_q_in_image with ⟨p', hp'E, hq_eq'⟩
    have h_p_eq : p = p' := h_inj hq_eq'.symm
    rw [h_p_eq]; exact hp'E
  have h_q2 : (Φ p) 2 = (p 2 - c) / h := hΦ2 p
  have h_lower1 : t - delta' ≤ (p 2 - c) / h := by
    rw [←h_q2]; exact h_q_height.1
  have h_upper1 : (p 2 - c) / h ≤ t + delta' := by
    rw [←h_q2]; exact h_q_height.2
  have h_p2_bounds : c + h * t - h * delta' ≤ p 2 ∧ p 2 ≤ c + h * t + h * delta' := by
    constructor
    · calc p 2
        = c + h * ((p 2 - c) / h) := by field_simp [hh.ne'] <;> ring
      _ ≥ c + h * (t - delta') := by gcongr
      _ = c + h * t - h * delta' := by ring
    · calc p 2
        = c + h * ((p 2 - c) / h) := by field_simp [hh.ne'] <;> ring
      _ ≤ c + h * (t + delta') := by gcongr
      _ = c + h * t + h * delta' := by ring
  have h_hdelta'_le : h * delta' ≤ delta := by
    dsimp only [delta']
    have h1 : h * (delta / M^2) ≤ delta := by
      have h2 : h / M^2 ≤ 1 := by
        have h3 : h ≤ 1 := hh1
        have h4 : 1 ≤ M^2 := by nlinarith
        have h5 : 1 / M^2 ≤ 1 := by
          apply (div_le_one (by positivity)).mpr
          nlinarith
        calc h / M^2 ≤ 1 / M^2 := by gcongr
             _ ≤ 1 := h5
      calc h * (delta / M^2) = (h / M^2) * delta := by ring
           _ ≤ 1 * delta := by gcongr
           _ = delta := by ring
    exact h1
  have h_p2_slab : p 2 ∈ Set.Icc (c + h * t - delta) (c + h * t + delta) := by
    have h_lower : c + h * t - delta ≤ p 2 := by
      calc c + h * t - delta ≤ c + h * t - h * delta' := by gcongr
           _ ≤ p 2 := h_p2_bounds.1
    have h_upper : p 2 ≤ c + h * t + delta := by
      calc p 2 ≤ c + h * t + h * delta' := h_p2_bounds.2
           _ ≤ c + h * t + delta := by gcongr
    exact ⟨h_lower, h_upper⟩
  have h_cm1 : -1 ≤ c - h := by
    have hwin := h_window (-1) (by norm_num)
    have h' : -1 ≤ c + h * (-1 : ℝ) := hwin.1
    have h_eq : c + h * (-1 : ℝ) = c - h := by ring
    rw [h_eq] at h'
    exact h'
  have h_cp1 : c + h ≤ 1 := by
    have hwin := h_window 1 (by norm_num)
    have h' : c + h * (1 : ℝ) ≤ 1 := hwin.2
    have h_eq : c + h * (1 : ℝ) = c + h := by ring
    rw [h_eq] at h'
    exact h'
  have h_p2_window : p 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    have h_eq : (Φ p) 2 = (p 2 - c) / h := hΦ2 p
    rw [h_eq] at h_q_window
    have h_lower : -1 ≤ (p 2 - c) / h := h_q_window.1
    have h_upper : (p 2 - c) / h ≤ 1 := h_q_window.2
    have h_p2_lower : c - h ≤ p 2 := by
      calc p 2
        = c + h * ((p 2 - c) / h) := by field_simp [hh.ne'] <;> ring
      _ ≥ c + h * (-1) := by gcongr
      _ = c - h := by ring
    have h_p2_upper : p 2 ≤ c + h := by
      calc p 2
        = c + h * ((p 2 - c) / h) := by field_simp [hh.ne'] <;> ring
      _ ≤ c + h * 1 := by gcongr
      _ = c + h := by ring
    exact ⟨by linarith, by linarith⟩
  exact ⟨⟨h_pE, h_p2_slab⟩, h_p2_window⟩

-- ===== Main theorem =====

theorem wz1_vertical_rescaling_slab_ad :
    WZ1VerticalRescalingSlabADStatement := by
  intro g c h M delta sigma C hh hh1 hM hdelta hdelta1 hsigma_pos hsigma_lt_one h_window E hAD
  let delta' : ℝ := delta / M^2
  let Φ := wz1VerticalRescalingMap c h M
  let gNew := wz1VerticalRescaledSlope g c h M
  have hM_pos : 0 < M := by linarith
  have hM2_pos : 0 < M^2 := by positivity
  have hdelta'_pos : 0 < delta' := by positivity
  have h_inj : Function.Injective Φ := rescaling_map_injective c h M hh hM
  have h_inner_id : ∀ (p : Point3),
      inner ℝ (Φ p) (globalGrainDirection (gNew ((Φ p) 2))) =
      inner ℝ p (globalGrainDirection (g (p 2))) / M^2 :=
    fun p => slab_inner_product_identity g c h M hh p
  have h_containment : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      globalGrainProjection gNew (globalGrainSlab (Φ '' E) t delta') ⊆
      (fun u : ℝ => u / M^2) '' globalGrainProjection g (globalGrainSlab E (c + h * t) delta) := by
    intro t ht
    intro y hy
    rcases hy with ⟨q, hq_slab, rfl⟩
    rcases hq_slab.1.1 with ⟨p, hpE, rfl⟩
    have h_p_slab : p ∈ globalGrainSlab E (c + h * t) delta :=
      slab_pullback g c h M delta hh hh1 hM hdelta h_window E t p
        (by exact hq_slab)
    have h_eq : inner ℝ (Φ p) (globalGrainDirection (gNew ((Φ p) 2))) =
        inner ℝ p (globalGrainDirection (g (p 2))) / M^2 := h_inner_id p
    refine ⟨inner ℝ p (globalGrainDirection (g (p 2))), ⟨p, h_p_slab, rfl⟩, ?_⟩
    exact h_eq.symm
  have h_AD : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1 (globalGrainProjection gNew (globalGrainSlab (Φ '' E) t delta'))
        delta' (1 - sigma) (10 * C) := by
    intro t ht
    let z := c + h * t
    let S := globalGrainProjection g (globalGrainSlab E z delta)
    have hz : z ∈ Set.Icc (-1 : ℝ) 1 := h_window t ht
    have h_old : IsADSet1 S delta (1 - sigma) C := hAD z hz
    have h_image_div : IsADSet1 ((fun u : ℝ => u / M^2) '' S) delta' (1 - sigma) (10 * C) :=
      h_old.image_div_sq hM hdelta hsigma_pos hsigma_lt_one
    have h_sub : globalGrainProjection gNew (globalGrainSlab (Φ '' E) t delta') ⊆
        (fun u : ℝ => u / M^2) '' S := h_containment t ht
    exact h_image_div.mono h_sub
  exact ⟨h_containment, h_AD⟩

end Kakeya.Assouad
