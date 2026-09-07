import MyLeanRepo.Kakeya.Assouad.WZ1.OSWCommonSimilarityTransportStatement
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# WZ1 OSW common similarity transport

Transports Frostman and discrete thin-tube certificates through the common
homothety stored in `WZ1OSWSupportNormalizationData`.

The scale lies in `[1/2, 2]`, so Frostman constants lose at most a factor 2,
and thin-tube constants lose at most `2^beta ≤ 2` for `0 ≤ beta ≤ 1`.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal
open Classical

variable {delta : ℝ} {G₁ G₂ : DiscreteSet 2}
  (D : WZ1OSWSupportNormalizationData delta G₁ G₂)

private lemma scale_rpow_neg_bound {s beta : ℝ}
    (hs : 1 / 2 ≤ s) (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1) :
    s ^ (-beta) ≤ 2 := by
  have hs_pos : 0 < s := by linarith
  have h1 : s ^ beta ≥ 1 / 2 := by
    by_cases h : s ≥ 1
    · have h2 : s ^ beta ≥ s ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h hbeta0
      have h3 : s ^ (0 : ℝ) = 1 := by simp
      rw [h3] at h2
      exact le_trans (by norm_num) h2
    · have h' : s < 1 := by linarith
      have h2 : s ^ beta ≥ s ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) hbeta1
      have h3 : s ^ (1 : ℝ) = s := by simp
      rw [h3] at h2
      exact le_trans hs h2
  have h4 : s ^ (-beta) = 1 / (s ^ beta) := by
    rw [Real.rpow_neg hs_pos.le] <;> ring
  rw [h4]
  have h5 : 0 < s ^ beta := Real.rpow_pos_of_pos hs_pos beta
  have h6 : 1 / (s ^ beta) ≤ 1 / (1 / 2 : ℝ) := by gcongr
  have h7 : (1 / (1 / 2 : ℝ)) = 2 := by norm_num
  rw [h7] at h6
  exact h6

private lemma scale_rpow_pos_bound {s beta : ℝ}
    (hs0 : 0 ≤ s) (hs2 : s ≤ 2) (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1) :
    s ^ beta ≤ 2 := by
  by_cases h : s ≤ 1
  · have h2 : s ^ beta ≤ 1 := Real.rpow_le_one hs0 h hbeta0
    exact h2.trans (by norm_num)
  · have h' : 1 ≤ s := by linarith
    have h2 : s ^ beta ≤ s ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h' hbeta1
    have h3 : s ^ (1 : ℝ) = s := by simp
    rw [h3] at h2
    exact h2.trans hs2

private def midpoint : Point2 :=
  (2 : ℝ)⁻¹ • (D.center₁ + D.center₂)

private def f_hom (x : Point2) : Point2 :=
  D.scale • (x - midpoint D)

private def f_inv (y : Point2) : Point2 :=
  (D.scale)⁻¹ • y + midpoint D

private lemma scale_pos : 0 < D.scale := by
  linarith [D.scale_lower]

private lemma f_hom_eq :
    f_hom D = wz1OSWPairNormalize D.center₁ D.center₂ := by
  funext x
  simp [f_hom, midpoint, wz1OSWPairNormalize, D.scale_eq]

private lemma f_dist (x y : Point2) :
    dist (f_hom D x) (f_hom D y) = D.scale * dist x y := by
  have h1 : f_hom D x - f_hom D y = D.scale • (x - y) := by
    simp [f_hom, midpoint, smul_sub] <;> abel
  have hnorm : ‖D.scale‖ = D.scale := by
    simpa [Real.norm_eq_abs] using abs_of_pos (scale_pos D)
  calc
    dist (f_hom D x) (f_hom D y)
        = ‖f_hom D x - f_hom D y‖ := by rw [dist_eq_norm]
    _ = ‖D.scale • (x - y)‖ := by rw [h1]
    _ = ‖D.scale‖ * ‖x - y‖ := by rw [norm_smul]
    _ = D.scale * ‖x - y‖ := by rw [hnorm]
    _ = D.scale * dist x y := by rw [dist_eq_norm]

private lemma f_injective : Function.Injective (f_hom D) := by
  intro x y h
  have h6 : dist (f_hom D x) (f_hom D y) = 0 := by
    rw [h]
    simp
  have h7 : D.scale * dist x y = 0 := by
    rwa [f_dist D x y] at h6
  have h8 : dist x y = 0 := (mul_eq_zero.mp h7).resolve_left (scale_pos D).ne'
  exact dist_eq_zero.mp h8

private lemma f_left_inv (x : Point2) : f_inv D (f_hom D x) = x := by
  have hsp : 0 < D.scale := scale_pos D
  have h9 : (D.scale)⁻¹ * D.scale = 1 := by field_simp [hsp.ne']
  simp [f_inv, f_hom, midpoint, smul_smul, h9] <;> abel

private lemma f_right_inv (y : Point2) : f_hom D (f_inv D y) = y := by
  have hsp : 0 < D.scale := scale_pos D
  have h9 : D.scale * (D.scale)⁻¹ = 1 := by field_simp [hsp.ne']
  simp [f_inv, f_hom, midpoint, smul_smul, h9] <;> abel

private lemma f_inv_injective : Function.Injective (f_inv D) := by
  intro x y h
  have h9 := congr_arg (f_hom D) h
  rw [f_right_inv D x, f_right_inv D y] at h9
  exact h9

private lemma f_surjective : Function.Surjective (f_hom D) := by
  intro y
  exact ⟨f_inv D y, f_right_inv D y⟩

private def homothetyEquiv : Point2 ≃ᵃ[ℝ] Point2 :=
  let e' : Point2 ≃ₗ[ℝ] Point2 :=
    { toFun := fun x => D.scale • x
      invFun := fun y => (D.scale)⁻¹ • y
      left_inv := fun x => by
        simp only [smul_smul]
        field_simp [(scale_pos D).ne']
        simp
      right_inv := fun y => by
        simp only [smul_smul]
        field_simp [(scale_pos D).ne']
        simp
      map_add' := smul_add D.scale
      map_smul' := fun c x => by
        simp only [smul_comm D.scale c, smul_smul]
        rfl }
  let e : Point2 → Point2 := f_hom D
  have h_em : e (midpoint D) = 0 := by
    simp [e, f_hom, sub_self, smul_zero]
  have h : ∀ (x : Point2), e x = e' (x - midpoint D) + e (midpoint D) := by
    intro x
    rw [h_em, add_zero]
    rfl
  AffineEquiv.mk' e e' (midpoint D) h

private lemma coe_map_affineEquiv (e : Point2 ≃ᵃ[ℝ] Point2)
    (ℓ : AffineSubspace ℝ Point2) :
    (AffineSubspace.map (e : Point2 →ᵃ[ℝ] Point2) ℓ : Set Point2) =
      (e : Point2 → Point2) '' (ℓ : Set Point2) := by
  exact AffineSubspace.coe_map _ _

private lemma finrank_map_affineEquiv (e : Point2 ≃ᵃ[ℝ] Point2)
    (ℓ : AffineSubspace ℝ Point2) :
    Module.finrank ℝ (AffineSubspace.map (e : Point2 →ᵃ[ℝ] Point2) ℓ).direction =
    Module.finrank ℝ ℓ.direction := by
  rw [AffineSubspace.map_direction]
  exact LinearEquiv.finrank_map_eq e.linear ℓ.direction

private lemma finrank_comap_affineEquiv (e : Point2 ≃ᵃ[ℝ] Point2)
    (ℓ : AffineSubspace ℝ Point2) :
    Module.finrank ℝ (AffineSubspace.comap (e : Point2 →ᵃ[ℝ] Point2) ℓ).direction =
    Module.finrank ℝ ℓ.direction := by
  have h : AffineSubspace.comap (e : Point2 →ᵃ[ℝ] Point2) ℓ =
      AffineSubspace.map (e.symm : Point2 →ᵃ[ℝ] Point2) ℓ := by
    ext x
    simp only [AffineSubspace.mem_comap, AffineSubspace.mem_map]
    constructor
    · intro hx
      refine ⟨e x, hx, ?_⟩
      exact e.left_inv x
    · rintro ⟨y, hy, hxy⟩
      have h_eq : e x = y := by
        have h9 : e (e.symm y) = y := e.right_inv y
        have h10 : e.symm y = x := hxy
        rw [h10] at h9
        exact h9
      exact h_eq ▸ hy
  rw [h]
  exact finrank_map_affineEquiv e.symm ℓ

private lemma image_thickening (s : Set Point2) (r : ℝ) :
    f_hom D '' Metric.thickening r s =
      Metric.thickening (D.scale * r) (f_hom D '' s) := by
  ext z
  simp only [Set.mem_image, Metric.mem_thickening_iff]
  constructor
  · rintro ⟨x, ⟨y, hy, hxy⟩, rfl⟩
    refine ⟨f_hom D y, ⟨y, hy, rfl⟩, ?_⟩
    rw [f_dist D]
    exact mul_lt_mul_of_pos_left hxy (scale_pos D)
  · rintro ⟨y', ⟨y, hy, rfl⟩, hzy'⟩
    rcases f_surjective D z with ⟨x, rfl⟩
    have h10 : D.scale * dist x y < D.scale * r := by
      simpa [f_dist D] using hzy'
    have h11 : dist x y < r := by nlinarith [scale_pos D]
    exact ⟨x, ⟨y, hy, h11⟩, rfl⟩

private lemma image_card (A : DiscreteSet 2) :
    (A.image (f_hom D)).card = A.card :=
  Finset.card_image_of_injective _ (f_injective D)

private lemma image_enncard (A : DiscreteSet 2) :
    DiscreteSet.enncard (A.image (f_hom D)) = A.enncard := by
  simp [DiscreteSet.enncard, image_card D A]

private lemma filter_image (A : DiscreteSet 2) (P : Point2 → Prop) [DecidablePred P] :
    (A.image (f_hom D)).filter P =
      (A.filter (fun z => P (f_hom D z))).image (f_hom D) := by
  ext z'
  simp only [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hP⟩
    exact ⟨z, ⟨hz, hP⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hP⟩, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, hP⟩

private lemma ballCount_image (A : DiscreteSet 2) (y : Point2) (r : ℝ) :
    DiscreteSet.ballCount (A.image (f_hom D)) y r =
    DiscreteSet.ballCount A (f_inv D y) (r / D.scale) := by
  have hsp : 0 < D.scale := scale_pos D
  have h17 : f_hom D (f_inv D y) = y := f_right_inv D y
  have h_filter_eq : A.filter (fun z : Point2 => dist (f_hom D z) y ≤ r) =
      A.filter (fun z : Point2 => dist z (f_inv D y) ≤ r / D.scale) := by
    ext z
    simp only [Finset.mem_filter]
    have h_iff :
        dist (f_hom D z) y ≤ r ↔ dist z (f_inv D y) ≤ r / D.scale := by
      rw [show dist (f_hom D z) y =
        dist (f_hom D z) (f_hom D (f_inv D y)) by rw [h17]]
      rw [f_dist D]
      constructor
      · intro h
        calc
          dist z (f_inv D y)
              = (D.scale * dist z (f_inv D y)) / D.scale := by
                  field_simp [hsp.ne'] <;> ring
          _ ≤ r / D.scale := by gcongr
      · intro h
        calc
          D.scale * dist z (f_inv D y)
              ≤ D.scale * (r / D.scale) := by gcongr
          _ = r := by field_simp [hsp.ne'] <;> ring
    tauto
  have h_eq : (A.image (f_hom D)).filter (fun z' => dist z' y ≤ r) =
      (A.filter (fun z => dist z (f_inv D y) ≤ r / D.scale)).image (f_hom D) := by
    rw [filter_image D A (fun z' => dist z' y ≤ r), h_filter_eq]
  rw [DiscreteSet.ballCount, h_eq]
  rw [Finset.card_image_of_injective _ (f_injective D)]
  <;> rfl

private def pair_image (E : Finset (Point2 × Point2)) : Finset (Point2 × Point2) :=
  E.image (fun p : Point2 × Point2 => (f_hom D p.1, f_hom D p.2))

private lemma pair_image_card (E : Finset (Point2 × Point2)) :
    (pair_image D E).card = E.card := by
  apply Finset.card_image_of_injective
  intro p q h
  have h1 : f_hom D p.1 = f_hom D q.1 := by
    simp [Prod.ext_iff] at h
    tauto
  have h2 : f_hom D p.2 = f_hom D q.2 := by
    simp [Prod.ext_iff] at h
    tauto
  have h3 : p.1 = q.1 := f_injective D h1
  have h4 : p.2 = q.2 := f_injective D h2
  exact Prod.ext h3 h4

private lemma pair_image_subset {A B : DiscreteSet 2}
    (E : Finset (Point2 × Point2)) (hE : E ⊆ A ×ˢ B) :
    pair_image D E ⊆ (A.image (f_hom D)) ×ˢ (B.image (f_hom D)) := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
  have hq1 : q.1 ∈ A := (Finset.mem_product.mp (hE hq)).1
  have hq2 : q.2 ∈ B := (Finset.mem_product.mp (hE hq)).2
  simp only [Finset.mem_product]
  exact
    ⟨Finset.mem_image.mpr ⟨q.1, hq1, rfl⟩,
      Finset.mem_image.mpr ⟨q.2, hq2, rfl⟩⟩

private lemma frostman_transport (C : ENNReal) (hC : 1 ≤ C)
    {A : DiscreteSet 2} (hF : A.IsFrostman delta 1 C) :
    DiscreteSet.IsFrostman (A.image (f_hom D)) D.normalizedDelta 1 (2 * C) := by
  intro y r hr1 hr2
  have hsp : 0 < D.scale := scale_pos D
  have h_delta_scale : D.normalizedDelta = D.scale * delta := D.normalizedDelta_eq
  have hr_scale : delta ≤ r / D.scale := by
    have h : D.normalizedDelta ≤ r := hr1
    rw [h_delta_scale] at h
    calc
      delta = (D.scale * delta) / D.scale := by field_simp [hsp.ne'] <;> ring
      _ ≤ r / D.scale := by gcongr
  have h_enncard : DiscreteSet.enncard (A.image (f_hom D)) = A.enncard :=
    image_enncard D A
  rw [ballCount_image D A y r, h_enncard]
  by_cases h_case : r / D.scale ≤ 1
  · have hF' := hF (f_inv D y) (r / D.scale) hr_scale h_case
    have h_rpow : realRpowENN (r / D.scale) 1 =
        ENNReal.ofReal (r / D.scale) := by
      simp [realRpowENN] <;> norm_num
    rw [h_rpow] at hF'
    have h_div : ENNReal.ofReal (r / D.scale) =
        ENNReal.ofReal r / ENNReal.ofReal D.scale := by
      rw [ENNReal.ofReal_div_of_pos hsp] <;> rfl
    rw [h_div] at hF'
    have h_scale_half : (1 / 2 : ENNReal) ≤ ENNReal.ofReal D.scale := by
      have h9 : (1 / 2 : ℝ) ≤ D.scale := D.scale_lower
      have h10 : ENNReal.ofReal (1 / 2 : ℝ) ≤ ENNReal.ofReal D.scale :=
        ENNReal.ofReal_le_ofReal h9
      have h11 : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 2 by norm_num)] <;>
          norm_num
      rw [h11]
      exact h10
    have h_inv_le : (ENNReal.ofReal D.scale)⁻¹ ≤ 2 := by
      have h2 : (ENNReal.ofReal D.scale)⁻¹ ≤ (1 / 2 : ENNReal)⁻¹ :=
        ENNReal.inv_le_inv' h_scale_half
      have h3 : (1 / 2 : ENNReal)⁻¹ = 2 := by norm_num
      rw [h3] at h2
      exact h2
    have h4 : C / ENNReal.ofReal D.scale ≤ 2 * C := by
      have h5 : C / ENNReal.ofReal D.scale =
          C * (ENNReal.ofReal D.scale)⁻¹ := by
        rw [div_eq_mul_inv]
      rw [h5]
      have h6 : C * (ENNReal.ofReal D.scale)⁻¹ ≤ C * 2 := by gcongr
      have h7 : C * 2 = 2 * C := by ring
      rw [h7] at h6
      exact h6
    have h_alg : C * (ENNReal.ofReal r / ENNReal.ofReal D.scale) * A.enncard =
        (C / ENNReal.ofReal D.scale) * ENNReal.ofReal r * A.enncard := by
      have hdiv : ENNReal.ofReal r / ENNReal.ofReal D.scale =
          ENNReal.ofReal r * (ENNReal.ofReal D.scale)⁻¹ := by
        rw [div_eq_mul_inv]
      simp only [hdiv, div_eq_mul_inv]
      <;> simp [mul_comm, mul_assoc, mul_left_comm]
    have h_final :
        (C / ENNReal.ofReal D.scale) * ENNReal.ofReal r * A.enncard ≤
        (2 * C) * ENNReal.ofReal r * A.enncard := by
      gcongr
    have h_rpow2 : realRpowENN r 1 = ENNReal.ofReal r := by
      simp [realRpowENN] <;> norm_num
    have h_goal :
        C * (ENNReal.ofReal r / ENNReal.ofReal D.scale) * A.enncard ≤
        (2 * C) * realRpowENN r 1 * A.enncard := by
      rw [h_rpow2]
      exact Eq.trans_le h_alg h_final
    exact le_trans hF' h_goal
  · have h_gt : 1 < r / D.scale := by exact lt_of_not_ge h_case
    have h_r_gt : (1 / 2 : ℝ) < r := by
      have h2 : r > D.scale := by
        calc
          r = (r / D.scale) * D.scale := by field_simp [hsp.ne'] <;> ring
          _ > 1 * D.scale := by gcongr
          _ = D.scale := by ring
      linarith [D.scale_lower]
    have h_one : (1 : ENNReal) ≤ (2 * C) * ENNReal.ofReal r := by
      have hC2 : (2 : ENNReal) ≤ 2 * C := by
        calc
          (2 : ENNReal) = 2 * 1 := by simp
          _ ≤ 2 * C := mul_le_mul_right hC 2
      have hr2 : (1 / 2 : ENNReal) ≤ ENNReal.ofReal r := by
        have h9 : (1 / 2 : ℝ) ≤ r := by linarith [h_r_gt]
        have h10 : ENNReal.ofReal (1 / 2 : ℝ) ≤ ENNReal.ofReal r :=
          ENNReal.ofReal_le_ofReal h9
        have h11 : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
          rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 2 by norm_num)] <;>
            norm_num
        rw [h11]
        exact h10
      have h : (2 : ENNReal) * (1 / 2 : ENNReal) ≤
          (2 * C) * ENNReal.ofReal r := by
        gcongr
      have h_eq : (1 : ENNReal) = (2 : ENNReal) * (1 / 2 : ENNReal) := by
        have h1 : (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ := by norm_num
        rw [h1, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)] <;> norm_num
      rw [h_eq]
      exact h
    have h_ball_le :
        DiscreteSet.ballCount A (f_inv D y) (r / D.scale) ≤ A.enncard := by
      simp [DiscreteSet.ballCount, DiscreteSet.enncard]
      <;> exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have h_rpow : realRpowENN r 1 = ENNReal.ofReal r := by
      simp [realRpowENN] <;> norm_num
    have h_mul : (1 : ENNReal) * A.enncard ≤
        (2 * C) * realRpowENN r 1 * A.enncard := by
      rw [h_rpow]
      have h : (1 : ENNReal) * A.enncard ≤
          ((2 * C) * ENNReal.ofReal r) * A.enncard := by
        apply mul_le_mul_of_nonneg_right h_one
        positivity
      exact h
    calc
      DiscreteSet.ballCount A (f_inv D y) (r / D.scale)
          ≤ A.enncard := h_ball_le
      _ = (1 : ENNReal) * A.enncard := by simp
      _ ≤ (2 * C) * realRpowENN r 1 * A.enncard := h_mul

private lemma thin_forward {A B : DiscreteSet 2}
    (beta K c : ℝ) (hbeta2 : beta ≤ 1)
    (h : HasDiscreteThinTubes delta beta K c A B) :
    HasDiscreteThinTubes D.normalizedDelta beta (2 * K) c
      (A.image (f_hom D)) (B.image (f_hom D)) := by
  rcases h with ⟨hbeta1, hK, hc, E, hE_sub, hE_mass, h_thin⟩
  let E' := pair_image D E
  let N₁ := A.image (f_hom D)
  let N₂ := B.image (f_hom D)
  have hE'_sub : E' ⊆ N₁ ×ˢ N₂ := pair_image_subset D E hE_sub
  have hE'_card : (E'.card : ENNReal) = (E.card : ENNReal) := by
    exact_mod_cast pair_image_card D E
  have hN1_card : (N₁.card : ENNReal) = (A.card : ENNReal) := by
    exact_mod_cast image_card D A
  have hN2_card : (N₂.card : ENNReal) = (B.card : ENNReal) := by
    exact_mod_cast image_card D B
  have hE'_mass :
      (1 - ENNReal.ofReal c) * (N₁.card : ENNReal) * (N₂.card : ENNReal) ≤
        (E'.card : ENNReal) := by
    rw [hN1_card, hN2_card, hE'_card]
    exact hE_mass
  let e : Point2 ≃ᵃ[ℝ] Point2 := homothetyEquiv D
  have h_main : ∀ (b₁' : Point2), b₁' ∈ N₁ →
      ∀ (ℓ' : AffineSubspace ℝ Point2), b₁' ∈ (ℓ' : Set Point2) →
        Module.finrank ℝ ℓ'.direction = 1 →
        ∀ (r : ℝ), D.normalizedDelta ≤ r →
          ((N₂.filter fun b₂' =>
              b₂' ∈ Metric.thickening r (ℓ' : Set Point2) ∧
              (b₁', b₂') ∈ E').card : ENNReal) ≤
            ENNReal.ofReal ((2 * K) * r ^ beta) * (N₂.card : ENNReal) := by
    intro b₁' hb₁' ℓ' hb₁'_line hfin r hr
    let b₁ := f_inv D b₁'
    have hb₁ : b₁ ∈ A := by
      rcases Finset.mem_image.mp hb₁' with ⟨x, hx, hfx⟩
      have h : x = b₁ := by
        have h2 : f_hom D x = f_hom D b₁ := by
          exact hfx.trans (f_right_inv D b₁').symm
        exact f_injective D h2
      exact h ▸ hx
    let ℓ := AffineSubspace.comap (e : Point2 →ᵃ[ℝ] Point2) ℓ'
    have hb₁_ℓ : b₁ ∈ (ℓ : Set Point2) := by
      have h : (e : Point2 → Point2) b₁ = b₁' := by
        change f_hom D (f_inv D b₁') = b₁'
        exact f_right_inv D b₁'
      have h_mem : (e : Point2 → Point2) b₁ ∈ (ℓ' : Set Point2) := by
        rw [h]
        exact hb₁'_line
      have h_iff :
          b₁ ∈ (ℓ : Set Point2) ↔
            (e : Point2 → Point2) b₁ ∈ (ℓ' : Set Point2) := by
        simp [ℓ, AffineSubspace.mem_comap]
      exact h_iff.mpr h_mem
    have h_finrank : Module.finrank ℝ ℓ.direction = 1 := by
      have h := finrank_comap_affineEquiv e ℓ'
      rw [h, hfin]
    have h_image_set : f_hom D '' (ℓ : Set Point2) = (ℓ' : Set Point2) := by
      have h_e_eq : (e : Point2 → Point2) = f_hom D := by rfl
      have h1 : (ℓ : Set Point2) =
          (e : Point2 → Point2) ⁻¹' (ℓ' : Set Point2) := by
        rw [AffineSubspace.coe_comap (e : Point2 →ᵃ[ℝ] Point2) ℓ'] <;> rfl
      rw [h1, ←h_e_eq]
      ext z
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨y, hY, rfl⟩
        exact hY
      · intro hz
        rcases e.surjective z with ⟨y, rfl⟩
        exact ⟨y, hz, rfl⟩
    have hr_scale : delta ≤ r / D.scale := by
      have h : D.normalizedDelta ≤ r := hr
      have h2 : D.normalizedDelta = D.scale * delta := D.normalizedDelta_eq
      rw [h2] at h
      have hsp : 0 < D.scale := scale_pos D
      calc
        delta = (D.scale * delta) / D.scale := by
          field_simp [hsp.ne'] <;> ring
        _ ≤ r / D.scale := by gcongr
    have h_thickening :
        f_hom D '' Metric.thickening (r / D.scale) (ℓ : Set Point2) =
          Metric.thickening r (ℓ' : Set Point2) := by
      rw [image_thickening D (ℓ : Set Point2) (r / D.scale), h_image_set]
      have hsp : 0 < D.scale := scale_pos D
      have h : D.scale * (r / D.scale) = r := by
        field_simp [hsp.ne'] <;> ring
      rw [h]
    have h_filter :
        N₂.filter (fun b₂' =>
            b₂' ∈ Metric.thickening r (ℓ' : Set Point2) ∧
            (b₁', b₂') ∈ E') =
          (B.filter (fun b₂ =>
            b₂ ∈ Metric.thickening (r / D.scale) (ℓ : Set Point2) ∧
            (b₁, b₂) ∈ E)).image (f_hom D) := by
      have h_N2_eq : N₂ = B.image (f_hom D) := by rfl
      rw [h_N2_eq]
      rw [filter_image D B (fun b₂' =>
        b₂' ∈ Metric.thickening r (ℓ' : Set Point2) ∧ (b₁', b₂') ∈ E')]
      apply congr_arg (fun s : Finset Point2 => s.image (f_hom D))
      apply Finset.filter_congr
      intro b₂ _
      have h1 :
          f_hom D b₂ ∈ Metric.thickening r (ℓ' : Set Point2) ↔
            b₂ ∈ Metric.thickening (r / D.scale) (ℓ : Set Point2) := by
        rw [←h_thickening]
        simp only [Set.mem_image]
        constructor
        · rintro ⟨z, hz, hfz⟩
          have h_eq : z = b₂ := f_injective D hfz
          rw [h_eq] at hz
          exact hz
        · intro hz
          exact ⟨b₂, hz, rfl⟩
      have h2 : (b₁', f_hom D b₂) ∈ E' ↔ (b₁, b₂) ∈ E := by
        simp only [E', pair_image, Finset.mem_image]
        constructor
        · rintro ⟨p, hp, h_eq⟩
          have h3 : f_hom D p.1 = f_hom D b₁ := by
            have h5 : f_hom D p.1 = b₁' := congr_arg Prod.fst h_eq
            exact h5.trans (f_right_inv D b₁').symm
          have h4 : f_hom D p.2 = f_hom D b₂ := congr_arg Prod.snd h_eq
          have h5 : p.1 = b₁ := f_injective D h3
          have h6 : p.2 = b₂ := f_injective D h4
          have hpe : p = (b₁, b₂) := Prod.ext h5 h6
          rw [hpe] at hp
          exact hp
        · intro h
          have h_eq :
              (f_hom D b₁, f_hom D b₂) = (b₁', f_hom D b₂) := by
            have h9 : f_hom D b₁ = b₁' := f_right_inv D b₁'
            exact Prod.ext h9 rfl
          exact ⟨(b₁, b₂), h, h_eq⟩
      tauto
    rw [h_filter]
    rw [Finset.card_image_of_injective _ (f_injective D)]
    have h_orig :=
      h_thin b₁ hb₁ ℓ hb₁_ℓ h_finrank (r / D.scale) hr_scale
    have hsp : 0 < D.scale := scale_pos D
    have hr_pos : 0 < r := by
      have h_pos : 0 < D.normalizedDelta := D.normalizedDelta_pos
      have h_le : D.normalizedDelta ≤ r := hr
      linarith
    have h_pow : K * (r / D.scale) ^ beta ≤ (2 * K) * r ^ beta := by
      have h2 : r / D.scale = r * (D.scale)⁻¹ := by
        field_simp [hsp.ne'] <;> ring
      have hr_nonneg : 0 ≤ r := by linarith [hr_pos]
      have hinv_nonneg : 0 ≤ (D.scale)⁻¹ := by positivity
      have h_inv_pow : ((D.scale)⁻¹) ^ beta = (D.scale) ^ (-beta) := by
        have h3 : (D.scale)⁻¹ = (D.scale) ^ (-1 : ℝ) := by
          rw [Real.rpow_neg_one]
          <;> ring
        rw [h3]
        rw [←Real.rpow_mul (by linarith)]
        <;> ring
      have h1 :
          (r / D.scale) ^ beta = r ^ beta * (D.scale) ^ (-beta) := by
        rw [h2, Real.mul_rpow hr_nonneg hinv_nonneg, h_inv_pow] <;> ring
      rw [h1]
      have h3 : (D.scale) ^ (-beta) ≤ 2 :=
        scale_rpow_neg_bound D.scale_lower hbeta1 hbeta2
      have h4 : K ≥ 0 := by linarith
      have h5 : r ^ beta ≥ 0 := by positivity
      have h6 :
          K * (r ^ beta * (D.scale) ^ (-beta)) ≤ (2 * K) * r ^ beta := by
        have h7 :
            K * (r ^ beta * (D.scale) ^ (-beta)) =
              K * r ^ beta * (D.scale) ^ (-beta) := by ring
        rw [h7]
        have h8 :
            K * r ^ beta * (D.scale) ^ (-beta) ≤ K * r ^ beta * 2 := by
          gcongr <;> linarith
        have h9 : K * r ^ beta * 2 = (2 * K) * r ^ beta := by ring
        rw [h9] at h8
        exact h8
      exact h6
    have h6 :
        ENNReal.ofReal (K * (r / D.scale) ^ beta) ≤
          ENNReal.ofReal ((2 * K) * r ^ beta) := by
      exact ENNReal.ofReal_le_ofReal h_pow
    calc
      ((B.filter (fun b₂ =>
          b₂ ∈ Metric.thickening (r / D.scale) (ℓ : Set Point2) ∧
          (b₁, b₂) ∈ E)).card : ENNReal)
          ≤ ENNReal.ofReal (K * (r / D.scale) ^ beta) *
              (B.card : ENNReal) := h_orig
      _ ≤ ENNReal.ofReal ((2 * K) * r ^ beta) * (B.card : ENNReal) := by
        gcongr
      _ = ENNReal.ofReal ((2 * K) * r ^ beta) * (N₂.card : ENNReal) := by
        rw [←hN2_card]
  exact ⟨hbeta1, by linarith, hc, E', hE'_sub, hE'_mass, h_main⟩

private lemma thin_backward {A B : DiscreteSet 2}
    (beta K c : ℝ) (hbeta2 : beta ≤ 1)
    (h : HasDiscreteThinTubes D.normalizedDelta beta K c
      (A.image (f_hom D)) (B.image (f_hom D))) :
    HasDiscreteThinTubes delta beta (2 * K) c A B := by
  rcases h with ⟨hbeta1, hK, hc, E', hE'_sub, hE'_mass, h_thin⟩
  let N₁ := A.image (f_hom D)
  let N₂ := B.image (f_hom D)
  let E : Finset (Point2 × Point2) :=
    E'.image (fun p' : Point2 × Point2 => (f_inv D p'.1, f_inv D p'.2))
  have hE_sub : E ⊆ A ×ˢ B := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨p', hp', rfl⟩
    have h1 : p' ∈ N₁ ×ˢ N₂ := hE'_sub hp'
    have h2 : p'.1 ∈ N₁ := (Finset.mem_product.mp h1).1
    have h3 : p'.2 ∈ N₂ := (Finset.mem_product.mp h1).2
    rcases Finset.mem_image.mp h2 with ⟨x, hx, _⟩
    rcases Finset.mem_image.mp h3 with ⟨y, hy, _⟩
    have h4 : f_inv D p'.1 = x := by
      have h5 : f_hom D x = p'.1 := by tauto
      have h6 : f_inv D (f_hom D x) = x := f_left_inv D x
      rw [h5] at h6
      exact h6
    have h7 : f_inv D p'.2 = y := by
      have h8 : f_hom D y = p'.2 := by tauto
      have h9 : f_inv D (f_hom D y) = y := f_left_inv D y
      rw [h8] at h9
      exact h9
    simp only [Finset.mem_product]
    exact ⟨by rw [h4] <;> exact hx, by rw [h7] <;> exact hy⟩
  let f_pair : Point2 × Point2 → Point2 × Point2 :=
    fun p' => (f_inv D p'.1, f_inv D p'.2)
  have hE_def : E = E'.image f_pair := by rfl
  have h_inj : Function.Injective f_pair := by
    intro p q h
    have h1 : f_inv D p.1 = f_inv D q.1 := by
      simp [Prod.ext_iff] at h
      tauto
    have h2 : f_inv D p.2 = f_inv D q.2 := by
      simp [Prod.ext_iff] at h
      tauto
    have h3 : p.1 = q.1 := by
      have h4 : f_hom D (f_inv D p.1) = f_hom D (f_inv D q.1) := by rw [h1]
      rw [f_right_inv D p.1, f_right_inv D q.1] at h4
      exact h4
    have h5 : p.2 = q.2 := by
      have h6 : f_hom D (f_inv D p.2) = f_hom D (f_inv D q.2) := by rw [h2]
      rw [f_right_inv D p.2, f_right_inv D q.2] at h6
      exact h6
    exact Prod.ext h3 h5
  have hE_card : E.card = E'.card := by
    rw [hE_def]
    exact Finset.card_image_of_injective E' h_inj
  have hE_card' : (E.card : ENNReal) = (E'.card : ENNReal) := by
    exact_mod_cast hE_card
  have hN1_card : (N₁.card : ENNReal) = (A.card : ENNReal) := by
    exact_mod_cast image_card D A
  have hN2_card : (N₂.card : ENNReal) = (B.card : ENNReal) := by
    exact_mod_cast image_card D B
  have hE_mass :
      (1 - ENNReal.ofReal c) * (A.card : ENNReal) * (B.card : ENNReal) ≤
        (E.card : ENNReal) := by
    rw [hE_card', ←hN1_card, ←hN2_card]
    exact hE'_mass
  let e : Point2 ≃ᵃ[ℝ] Point2 := homothetyEquiv D
  have h_main : ∀ (b₁ : Point2), b₁ ∈ A →
      ∀ (ℓ : AffineSubspace ℝ Point2), b₁ ∈ (ℓ : Set Point2) →
        Module.finrank ℝ ℓ.direction = 1 →
        ∀ (r : ℝ), delta ≤ r →
          ((B.filter fun b₂ =>
              b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧
              (b₁, b₂) ∈ E).card : ENNReal) ≤
            ENNReal.ofReal ((2 * K) * r ^ beta) * (B.card : ENNReal) := by
    intro b₁ hb₁ ℓ hb₁_ℓ hfin r hr
    let b₁' := f_hom D b₁
    have hb₁' : b₁' ∈ N₁ := Finset.mem_image.mpr ⟨b₁, hb₁, rfl⟩
    let ℓ' := AffineSubspace.map (e : Point2 →ᵃ[ℝ] Point2) ℓ
    have hℓ'_set : (ℓ' : Set Point2) = f_hom D '' (ℓ : Set Point2) := by
      exact coe_map_affineEquiv e ℓ
    have hb₁'_ℓ : b₁' ∈ (ℓ' : Set Point2) := by
      rw [hℓ'_set]
      exact ⟨b₁, hb₁_ℓ, rfl⟩
    have h_finrank : Module.finrank ℝ ℓ'.direction = 1 := by
      have h := finrank_map_affineEquiv e ℓ
      rw [h, hfin]
    have hr_scale : D.normalizedDelta ≤ D.scale * r := by
      have h2 : D.normalizedDelta = D.scale * delta := D.normalizedDelta_eq
      rw [h2]
      have hsp : 0 < D.scale := scale_pos D
      gcongr
    have h_thickening :
        f_hom D '' Metric.thickening r (ℓ : Set Point2) =
          Metric.thickening (D.scale * r) (ℓ' : Set Point2) := by
      rw [image_thickening D (ℓ : Set Point2) r, hℓ'_set]
    have h_filter :
        B.filter (fun b₂ =>
            b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧ (b₁, b₂) ∈ E) =
          (N₂.filter (fun b₂' =>
            b₂' ∈ Metric.thickening (D.scale * r) (ℓ' : Set Point2) ∧
            (b₁', b₂') ∈ E')).image (f_inv D) := by
      have hE_iff : ∀ (b₂ : Point2),
          (b₁, b₂) ∈ E ↔ (b₁', f_hom D b₂) ∈ E' := by
        intro b₂
        simp only [E, Finset.mem_image]
        constructor
        · rintro ⟨p', hp', h_eq⟩
          have h1 : f_inv D p'.1 = b₁ := congr_arg Prod.fst h_eq
          have h2 : f_inv D p'.2 = b₂ := congr_arg Prod.snd h_eq
          have h3 : p'.1 = b₁' := by
            have h4 : f_hom D (f_inv D p'.1) = f_hom D b₁ := by rw [h1]
            have h5 : f_hom D (f_inv D p'.1) = p'.1 := f_right_inv D p'.1
            have h6 : p'.1 = f_hom D b₁ := h5.symm.trans h4
            have h7 : f_hom D b₁ = b₁' := by simp [b₁']
            rw [h7] at h6
            exact h6
          have h8 : p'.2 = f_hom D b₂ := by
            have h9 : f_hom D (f_inv D p'.2) = f_hom D b₂ := by rw [h2]
            have h10 : f_hom D (f_inv D p'.2) = p'.2 := f_right_inv D p'.2
            exact h10.symm.trans h9
          have hpe : p' = (b₁', f_hom D b₂) := Prod.ext h3 h8
          rw [hpe] at hp'
          exact hp'
        · intro h
          refine ⟨(b₁', f_hom D b₂), h, ?_⟩
          have h9 : f_inv D b₁' = b₁ := f_left_inv D b₁
          have h10 : f_inv D (f_hom D b₂) = b₂ := f_left_inv D b₂
          exact Prod.ext h9 h10
      ext b₂
      simp only [Finset.mem_image]
      constructor
      · intro h
        have h5 : b₂ ∈ B ∧ _ := Finset.mem_filter.mp h
        rcases h5 with ⟨hb₂, hthick, hE⟩
        have h1 : f_hom D b₂ ∈ N₂ :=
          Finset.mem_image.mpr ⟨b₂, hb₂, rfl⟩
        have h2 :
            f_hom D b₂ ∈
              Metric.thickening (D.scale * r) (ℓ' : Set Point2) := by
          have h21 :
              f_hom D b₂ ∈
                f_hom D '' Metric.thickening r (ℓ : Set Point2) :=
            ⟨b₂, hthick, rfl⟩
          rw [h_thickening] at h21
          exact h21
        have h3 : (b₁', f_hom D b₂) ∈ E' := (hE_iff b₂).mp hE
        have h4 :
            f_hom D b₂ ∈ N₂.filter (fun b₂' =>
              b₂' ∈ Metric.thickening (D.scale * r) (ℓ' : Set Point2) ∧
              (b₁', b₂') ∈ E') := by
          rw [Finset.mem_filter]
          exact ⟨h1, h2, h3⟩
        exact ⟨f_hom D b₂, h4, f_left_inv D b₂⟩
      · rintro ⟨b₂', hb2'_filter, h_eq⟩
        have h5 : b₂' ∈ N₂ ∧ _ := Finset.mem_filter.mp hb2'_filter
        rcases h5 with ⟨hb2'_mem, hb2'_thick, hb2'_E⟩
        rcases Finset.mem_image.mp hb2'_mem with ⟨y, hy, hfy⟩
        have h_y_eq : y = b₂ := by
          have h2 : f_inv D (f_hom D y) = y := f_left_inv D y
          have h1 : f_inv D b₂' = y := by
            rw [hfy] at h2
            exact h2
          exact h1.symm.trans h_eq
        have hthick2 : y ∈ Metric.thickening r (ℓ : Set Point2) := by
          have hthick :
              f_hom D y ∈
                Metric.thickening (D.scale * r) (ℓ' : Set Point2) := by
            have h : b₂' = f_hom D y := hfy.symm
            rw [h] at hb2'_thick
            exact hb2'_thick
          rw [←h_thickening] at hthick
          rcases hthick with ⟨z, hz, hfz⟩
          have h_eq2 : z = y := f_injective D hfz
          rw [h_eq2] at hz
          exact hz
        have hE2 : (b₁, y) ∈ E := by
          have hE' : (b₁', f_hom D y) ∈ E' := by
            have h : b₂' = f_hom D y := hfy.symm
            rw [h] at hb2'_E
            exact hb2'_E
          exact (hE_iff y).mpr hE'
        have hB : b₂ ∈ B := h_y_eq ▸ hy
        have hthick3 : b₂ ∈ Metric.thickening r (ℓ : Set Point2) :=
          h_y_eq ▸ hthick2
        have hE3 : (b₁, b₂) ∈ E := h_y_eq ▸ hE2
        simpa [Finset.mem_filter] using ⟨hB, hthick3, hE3⟩
    have h_card :
        ((B.filter (fun b₂ =>
            b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧
            (b₁, b₂) ∈ E)).card : ENNReal) =
          ((N₂.filter (fun b₂' =>
            b₂' ∈ Metric.thickening (D.scale * r) (ℓ' : Set Point2) ∧
            (b₁', b₂') ∈ E')).card : ENNReal) := by
      rw [h_filter]
      exact_mod_cast
        Finset.card_image_of_injective (N₂.filter _) (f_inv_injective D)
    have h_orig :=
      h_thin b₁' hb₁' ℓ' hb₁'_ℓ h_finrank (D.scale * r) hr_scale
    have hsp : 0 < D.scale := scale_pos D
    have hr_pos : 0 < r := by
      have h1 : 0 < D.scale * delta := by
        rw [←D.normalizedDelta_eq]
        exact D.normalizedDelta_pos
      have h2 : 0 < delta := by nlinarith
      linarith [hr, h2]
    have h_pow : K * (D.scale * r) ^ beta ≤ (2 * K) * r ^ beta := by
      have h1 :
          (D.scale * r) ^ beta = (D.scale) ^ beta * r ^ beta := by
        rw [Real.mul_rpow (by linarith [scale_pos D]) (by linarith)] <;> ring
      rw [h1]
      have h3 : (D.scale) ^ beta ≤ 2 :=
        scale_rpow_pos_bound (by linarith [scale_pos D])
          D.scale_upper hbeta1 hbeta2
      have h4 : K ≥ 0 := by linarith
      have h5 : r ^ beta ≥ 0 := by positivity
      have h6 :
          K * ((D.scale) ^ beta * r ^ beta) ≤ (2 * K) * r ^ beta := by
        have h7 :
            K * ((D.scale) ^ beta * r ^ beta) =
              K * r ^ beta * (D.scale) ^ beta := by ring
        rw [h7]
        have h8 :
            K * r ^ beta * (D.scale) ^ beta ≤ K * r ^ beta * 2 := by
          gcongr <;> linarith
        have h9 : K * r ^ beta * 2 = (2 * K) * r ^ beta := by ring
        rw [h9] at h8
        exact h8
      exact h6
    have h7 :
        ENNReal.ofReal (K * (D.scale * r) ^ beta) ≤
          ENNReal.ofReal ((2 * K) * r ^ beta) := by
      exact ENNReal.ofReal_le_ofReal h_pow
    calc
      ((B.filter (fun b₂ =>
          b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧
          (b₁, b₂) ∈ E)).card : ENNReal)
          = ((N₂.filter (fun b₂' =>
            b₂' ∈ Metric.thickening (D.scale * r) (ℓ' : Set Point2) ∧
            (b₁', b₂') ∈ E')).card : ENNReal) := h_card
      _ ≤ ENNReal.ofReal (K * (D.scale * r) ^ beta) *
          (N₂.card : ENNReal) := h_orig
      _ ≤ ENNReal.ofReal ((2 * K) * r ^ beta) * (N₂.card : ENNReal) := by
        gcongr
      _ = ENNReal.ofReal ((2 * K) * r ^ beta) * (B.card : ENNReal) := by
        rw [←hN2_card]
  exact ⟨hbeta1, by linarith, hc, E, hE_sub, hE_mass, h_main⟩

theorem wz1_osw_common_similarity_transport :
    WZ1OSWCommonSimilarityTransportStatement := by
  intro delta G₁ G₂ D C hC hF1 hF2
  have hN1_eq : G₁.image (f_hom D) = D.normalized₁ := by
    rw [f_hom_eq D, ←D.normalized₁_eq]
  have hN2_eq : G₂.image (f_hom D) = D.normalized₂ := by
    rw [f_hom_eq D, ←D.normalized₂_eq]
  have h_frost1 :
      D.normalized₁.IsFrostman D.normalizedDelta 1 (2 * C) := by
    exact hN1_eq ▸ frostman_transport D C hC hF1
  have h_frost2 :
      D.normalized₂.IsFrostman D.normalizedDelta 1 (2 * C) := by
    exact hN2_eq ▸ frostman_transport D C hC hF2
  refine' ⟨{
    normalized₁_frostman := h_frost1,
    normalized₂_frostman := h_frost2,
    thin_forward₁₂ := by
      intro beta K c hbeta2 h
      have h_main := thin_forward D (A := G₁) (B := G₂) beta K c hbeta2 h
      rw [hN1_eq, hN2_eq] at h_main
      exact h_main,
    thin_forward₂₁ := by
      intro beta K c hbeta2 h
      have h_main := thin_forward D (A := G₂) (B := G₁) beta K c hbeta2 h
      rw [hN2_eq, hN1_eq] at h_main
      exact h_main,
    thin_backward₁₂ := by
      intro beta K c hbeta2 h
      have h' : HasDiscreteThinTubes D.normalizedDelta beta K c
          (G₁.image (f_hom D)) (G₂.image (f_hom D)) := by
        rw [hN1_eq.symm, hN2_eq.symm] at h
        exact h
      exact thin_backward D (A := G₁) (B := G₂) beta K c hbeta2 h',
    thin_backward₂₁ := by
      intro beta K c hbeta2 h
      have h' : HasDiscreteThinTubes D.normalizedDelta beta K c
          (G₂.image (f_hom D)) (G₁.image (f_hom D)) := by
        rw [hN2_eq.symm, hN1_eq.symm] at h
        exact h
      exact thin_backward D (A := G₂) (B := G₁) beta K c hbeta2 h',
  }⟩

end Kakeya.Assouad
