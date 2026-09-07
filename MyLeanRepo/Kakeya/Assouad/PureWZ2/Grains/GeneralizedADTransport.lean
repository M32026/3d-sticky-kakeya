import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADTransport
import Mathlib.Tactic

/-!
# Generalized AD transport for 20-Lip slope

Generalizes `global_ad_transport` and `local_ad_transport` to work with
arbitrary slope functions (no Lipschitz constraint), enabling dilation by 20
from the 20-Lip anchored transport output.
-/

namespace Kakeya.Assouad

open Metric Set

private lemma scalarProjection_mono' {v : Point3} {A B : Set Point3} (h : A ⊆ B) :
    scalarProjection v A ⊆ scalarProjection v B := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

private lemma horizontalSlice_dilate' {E : Set Point3} {s z : ℝ} (hs : 0 < s) :
    horizontalSlice ((fun p : Point3 => s • p) '' E) z =
      (fun p : Point3 => s • p) '' horizontalSlice E (z / s) := by
  ext x
  simp only [horizontalSlice, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hz⟩
    have hp2 : p (2 : Fin 3) = z / s := by
      have hz2 : (s • p) (2 : Fin 3) = z := hz
      have h : s * p (2 : Fin 3) = z := by simpa [Pi.smul_apply] using hz2
      have h' : p (2 : Fin 3) = z / s := by
        calc p (2 : Fin 3) = (s * p (2 : Fin 3)) / s := by field_simp [hs.ne']
          _ = z / s := by rw [h]
      exact h'
    exact ⟨p, ⟨hp, hp2⟩, rfl⟩
  · rintro ⟨p, ⟨hp, hp2⟩, rfl⟩
    have hz : (s • p) (2 : Fin 3) = z := by
      simp [Pi.smul_apply, hp2] <;> field_simp [hs.ne']
    exact ⟨⟨p, hp, rfl⟩, hz⟩

private lemma scalarProjection_dilate' {E : Set Point3} {s : ℝ} {v : Point3} (hs : 0 < s) :
    scalarProjection v ((fun p : Point3 => s • p) '' E) =
      (fun x : ℝ => s * x) '' scalarProjection v E := by
  calc scalarProjection v ((fun p : Point3 => s • p) '' E)
    = (fun x : Point3 => inner ℝ x v) '' ((fun p : Point3 => s • p) '' E) := by rfl
  _ = (fun p : Point3 => inner ℝ (s • p) v) '' E := by
      rw [Set.image_image] <;> rfl
  _ = (fun p : Point3 => s * inner ℝ p v) '' E := by
      congr with p; simp [inner_smul_left]
  _ = (fun x : ℝ => s * x) '' ((fun p : Point3 => inner ℝ p v) '' E) := by
      rw [← Set.image_image] <;> rfl
  _ = (fun x : ℝ => s * x) '' scalarProjection v E := by rfl

/-- Generalized global AD transport: works with any slope function, no Lip constraint. -/
lemma global_ad_transport_general
    {sigma loss loss_src delta' : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta'}
    {shading : WZ1PaperTubeShading family}
    (slope : ℝ → ℝ)
    (global_ad : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope z))
          (horizontalSlice shading.union z))
        delta' (1 - sigma) (Kakeya.realRpowENN delta' (-loss_src)))
    {s : ℝ} (hs_pos : 0 < s) (hs_one : 1 ≤ s)
    {targetUnion : Set Point3}
    (h_target_sub : targetUnion ⊆ (fun p : Point3 => s • p) '' shading.union)
    (targetSlope : ℝ → ℝ)
    (h_slope_eq : ∀ z, targetSlope z = slope (z / s))
    (hloss_src : 0 < loss_src) (hloss_lt : loss_src < loss)
    (hsmall : Real.rpow delta' (loss - loss_src) ≤ Real.rpow s (-loss))
    (hdelta'_pos : 0 < delta')
    (hsigma : 0 < 1 - sigma) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (targetSlope z))
          (horizontalSlice targetUnion z))
        (s * delta') (1 - sigma) (Kakeya.realRpowENN (s * delta') (-loss)) := by
  intro z hz
  have hz1 : z / s ∈ Set.Icc (-1 : ℝ) 1 := by
    have h1 : -1 ≤ z := hz.1
    have h2 : z ≤ 1 := hz.2
    have h3 : -1 ≤ z / s := by
      have h4 : -s ≤ z := by linarith
      have h5 : -1 ≤ z / s := by
        calc -1 = (-s) / s := by field_simp [hs_pos.ne']
          _ ≤ z / s := by gcongr
      exact h5
    have h7 : z / s ≤ 1 := by
      have h8 : z ≤ s := by linarith
      calc z / s ≤ s / s := by gcongr
        _ = 1 := by field_simp [hs_pos.ne']
    exact ⟨h3, h7⟩
  let v := globalGrainDirection (slope (z / s))
  have hv : v = globalGrainDirection (targetSlope z) := by
    rw [h_slope_eq z]
  let sourceSet := scalarProjection v (horizontalSlice shading.union (z / s))
  have h_source_ad : PureWZ2PaperADSet1 sourceSet delta' (1 - sigma)
      (Kakeya.realRpowENN delta' (-loss_src)) :=
    global_ad (z / s) hz1
  let dilatedSet := (fun x : ℝ => s * x) '' sourceSet
  have h_dilated_ad : PureWZ2PaperADSet1 dilatedSet (s * delta') (1 - sigma)
      (Kakeya.realRpowENN delta' (-loss_src)) :=
    h_source_ad.smul hs_pos
  have h_const_le : Kakeya.realRpowENN delta' (-loss_src) ≤
      Kakeya.realRpowENN (s * delta') (-loss) :=
    ad_constant_comparison hdelta'_pos hs_pos hloss_lt hsmall
  have h_const_ne_top : Kakeya.realRpowENN (s * delta') (-loss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
  have h_dilated_ad2 : PureWZ2PaperADSet1 dilatedSet (s * delta') (1 - sigma)
      (Kakeya.realRpowENN (s * delta') (-loss)) :=
    h_dilated_ad.mono_const h_const_le h_const_ne_top
  let targetSet := scalarProjection (globalGrainDirection (targetSlope z))
      (horizontalSlice targetUnion z)
  have h_slice_sub : horizontalSlice targetUnion z ⊆
      horizontalSlice ((fun p : Point3 => s • p) '' shading.union) z := by
    intro x hx
    exact ⟨h_target_sub hx.1, hx.2⟩
  have h_proj_sub : scalarProjection (globalGrainDirection (targetSlope z))
        (horizontalSlice targetUnion z) ⊆
      scalarProjection (globalGrainDirection (targetSlope z))
        (horizontalSlice ((fun p : Point3 => s • p) '' shading.union) z) :=
    scalarProjection_mono' h_slice_sub
  have h_target_sub2 : targetSet ⊆ dilatedSet := by
    have h_eq1 : scalarProjection (globalGrainDirection (targetSlope z))
          (horizontalSlice ((fun p : Point3 => s • p) '' shading.union) z) =
        scalarProjection v
          (horizontalSlice ((fun p : Point3 => s • p) '' shading.union) z) := by
      rw [← hv]
    rw [h_eq1] at h_proj_sub
    have h_eq2 : scalarProjection v
          (horizontalSlice ((fun p : Point3 => s • p) '' shading.union) z) =
        (fun x : ℝ => s * x) '' scalarProjection v
          (horizontalSlice shading.union (z / s)) := by
      rw [horizontalSlice_dilate' hs_pos, scalarProjection_dilate' hs_pos]
    rw [h_eq2] at h_proj_sub
    exact h_proj_sub
  exact h_dilated_ad2.mono_set h_target_sub2

/-- Generalized local AD transport: works with any planeMap, no Lip constraint. -/
lemma local_ad_transport_general
    {sigma loss loss_src delta' : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta'}
    {shading : WZ1PaperTubeShading family}
    (planeMap : {point : Point3 // point ∈ shading.union} → Point3)
    (local_ad : ∀ rho : ℝ, delta' ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ shading.union},
        PureWZ2PaperADSet1
          (scalarProjection (planeMap point)
            (shading.union ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)))
          rho (1 - sigma) (Kakeya.realRpowENN delta' (-loss_src)))
    {s : ℝ} (hs_pos : 0 < s) (hs_one : 1 ≤ s)
    {targetUnion : Set Point3}
    (h_target_sub : targetUnion ⊆ (fun p : Point3 => s • p) '' shading.union)
    (targetPlaneMap : {point : Point3 // point ∈ targetUnion} → Point3)
    (h_planeMap_eq : ∀ (point : {point : Point3 // point ∈ targetUnion}),
        targetPlaneMap point = planeMap
          ⟨(1 / s : ℝ) • (point : Point3),
            dilate_point_in_union hs_pos h_target_sub point⟩)
    (hloss_src : 0 < loss_src) (hloss_lt : loss_src < loss)
    (hsmall : Real.rpow delta' (loss - loss_src) ≤ Real.rpow s (-loss))
    (hdelta'_pos : 0 < delta')
    (hsigma : 0 < 1 - sigma) :
    ∀ rho : ℝ, s * delta' ≤ rho → rho ≤ 1 →
      ∀ point : {point : Point3 // point ∈ targetUnion},
        PureWZ2PaperADSet1
          (scalarProjection (targetPlaneMap point)
            (targetUnion ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)))
          rho (1 - sigma) (Kakeya.realRpowENN (s * delta') (-loss)) := by
  intro rho hrho_ge hrho_le point
  have hrho_nonneg : 0 ≤ rho := by
    have h : 0 < s * delta' := mul_pos hs_pos hdelta'_pos
    linarith
  let rho' := rho / s
  have h_rho'_ge : delta' ≤ rho' := by
    have h : s * delta' ≤ rho := hrho_ge
    calc delta' = (s * delta') / s := by field_simp [hs_pos.ne']
      _ ≤ rho / s := by gcongr
  have h_rho'_le : rho' ≤ 1 := by
    have h : rho ≤ 1 := hrho_le
    have h' : rho / s ≤ 1 / s := by gcongr
    have h'' : 1 / s ≤ 1 := by
      rw [div_le_one hs_pos] <;> linarith
    linarith
  let p' : Point3 := (1 / s : ℝ) • (point : Point3)
  have hp'_in : p' ∈ shading.union :=
    dilate_point_in_union hs_pos h_target_sub point
  let sourceBallSet := shading.union ∩ Metric.closedBall p' (Real.sqrt rho')
  have h_ball_contain : targetUnion ∩ Metric.closedBall (point : Point3) (Real.sqrt rho) ⊆
      (fun p : Point3 => s • p) '' sourceBallSet := by
    intro x hx
    have hx_in : x ∈ targetUnion := hx.1
    have hx_dist : dist x (point : Point3) ≤ Real.sqrt rho := hx.2
    let q : Point3 := (1 / s : ℝ) • x
    have hq_in : q ∈ shading.union := by
      have h : x ∈ (fun p : Point3 => s • p) '' shading.union := h_target_sub hx_in
      rcases h with ⟨p, hp, hpeq⟩
      have h_eq : q = p := by
        ext k
        have h5 : (s • p) k = x k :=
          congr_arg (fun y : Point3 => y k) hpeq
        have h6 : s * p k = x k := by simpa [Pi.smul_apply] using h5
        have h7 : (1 / s : ℝ) * x k = p k := by
          field_simp [hs_pos.ne'] <;> linarith
        simpa [q, Pi.smul_apply] using h7
      rw [h_eq] <;> exact hp
    have hq_dist : dist q p' ≤ Real.sqrt rho' := by
      have h1 : dist q p' = (1 / s : ℝ) * dist x (point : Point3) := by
        have h_dist_smul : dist ((1 / s : ℝ) • x) ((1 / s : ℝ) • (point : Point3)) =
            ‖(1 / s : ℝ)‖ * dist x (point : Point3) := dist_smul₀ (1 / s : ℝ) x (point : Point3)
        have h_norm : ‖(1 / s : ℝ)‖ = 1 / s := by
          have h_pos : 0 < (1 / s : ℝ) := by positivity
          rw [Real.norm_eq_abs, abs_of_pos h_pos]
        rw [h_dist_smul, h_norm] <;> rfl
      rw [h1]
      have h2 : (1 / s : ℝ) * dist x (point : Point3) ≤ (1 / s : ℝ) * Real.sqrt rho := by gcongr
      have h3 : (1 / s : ℝ) * Real.sqrt rho ≤ Real.sqrt (rho / s) := by
        have h4 : Real.sqrt (rho / s) = Real.sqrt rho / Real.sqrt s := by
          rw [Real.sqrt_div (by linarith)]
        rw [h4]
        have h6 : 1 / s ≤ 1 / Real.sqrt s := by
          have h7 : Real.sqrt s ≤ s := by
            have h8 : 1 ≤ s := by linarith
            have h9 : 0 ≤ s := by linarith
            nlinarith [Real.sqrt_nonneg s, Real.sq_sqrt h9]
          gcongr
        have h10 : (1 / s : ℝ) * Real.sqrt rho ≤ (1 / Real.sqrt s) * Real.sqrt rho := by
          gcongr
        have h11 : (1 / Real.sqrt s) * Real.sqrt rho = Real.sqrt rho / Real.sqrt s := by
          field_simp
        exact h10.trans h11.le
      exact h2.trans h3
    have hq_in_ball : q ∈ sourceBallSet := ⟨hq_in, hq_dist⟩
    have h_image : (fun p : Point3 => s • p) q = x := by
      have h : (s • q) = x := by
        rw [show q = (1 / s : ℝ) • x from rfl]
        rw [smul_smul]
        have h9 : s * (1 / s : ℝ) = 1 := by field_simp [hs_pos.ne']
        rw [h9, one_smul]
      exact h
    exact ⟨q, hq_in_ball, h_image⟩
  let v := planeMap ⟨p', hp'_in⟩
  let sourceSet := scalarProjection v sourceBallSet
  have h_source_ad : PureWZ2PaperADSet1 sourceSet rho' (1 - sigma)
      (Kakeya.realRpowENN delta' (-loss_src)) :=
    local_ad rho' h_rho'_ge h_rho'_le ⟨p', hp'_in⟩
  let dilatedSet := (fun x : ℝ => s * x) '' sourceSet
  have h_dilated_ad : PureWZ2PaperADSet1 dilatedSet (s * rho') (1 - sigma)
      (Kakeya.realRpowENN delta' (-loss_src)) :=
    h_source_ad.smul hs_pos
  have h_rho_eq : s * rho' = rho := by
    dsimp only [rho']
    field_simp [hs_pos.ne'] <;> ring
  have h_dilated_ad' : PureWZ2PaperADSet1 dilatedSet rho (1 - sigma)
      (Kakeya.realRpowENN delta' (-loss_src)) := by
    rw [h_rho_eq] at h_dilated_ad
    exact h_dilated_ad
  have h_const_le : Kakeya.realRpowENN delta' (-loss_src) ≤
      Kakeya.realRpowENN (s * delta') (-loss) :=
    ad_constant_comparison hdelta'_pos hs_pos hloss_lt hsmall
  have h_const_ne_top : Kakeya.realRpowENN (s * delta') (-loss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
  have h_dilated_ad2 : PureWZ2PaperADSet1 dilatedSet rho (1 - sigma)
      (Kakeya.realRpowENN (s * delta') (-loss)) :=
    h_dilated_ad'.mono_const h_const_le h_const_ne_top
  have hv : targetPlaneMap point = v := h_planeMap_eq point
  have h_target_set_sub : scalarProjection (targetPlaneMap point)
        (targetUnion ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)) ⊆
      dilatedSet := by
    have h_eq1 : scalarProjection (targetPlaneMap point)
          (targetUnion ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)) =
        scalarProjection v
          (targetUnion ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)) := by
      rw [hv]
    rw [h_eq1]
    have h_proj_sub : scalarProjection v
          (targetUnion ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)) ⊆
        scalarProjection v
          ((fun p : Point3 => s • p) '' sourceBallSet) :=
      scalarProjection_mono' h_ball_contain
    have h_eq2 : scalarProjection v
          ((fun p : Point3 => s • p) '' sourceBallSet) =
        (fun x : ℝ => s * x) '' scalarProjection v sourceBallSet := by
      rw [scalarProjection_dilate' hs_pos]
    rw [h_eq2] at h_proj_sub
    exact h_proj_sub
  exact h_dilated_ad2.mono_set h_target_set_sub

end Kakeya.Assouad
