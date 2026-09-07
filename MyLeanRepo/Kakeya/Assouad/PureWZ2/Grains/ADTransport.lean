import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PreGrainData
import Mathlib.Tactic

/-!
# AD set transport under isotropic dilation and subset

Core lemmas for transporting `PureWZ2PaperADSet1` bounds from source preGrains
to the dilated target configuration.

## Key results

1. `PureWZ2PaperADSet1.mono_set`: subsets inherit AD.
2. `PureWZ2PaperADSet1.mono_const`: monotone in constant.
3. `externalCoveringNumber_smul`: covering number decreases under dilation.
4. `PureWZ2PaperADSet1.smul`: AD transports under isotropic dilation.
5. `ad_constant_comparison`: loss-adjusted constant comparison.
6. `global_ad_transport`: full global grain AD transport.
7. `local_ad_transport`: full local grain AD transport.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- `PureWZ2PaperADSet1` is monotone in the set: if S ⊆ T and T has AD, then S has AD. -/
lemma PureWZ2PaperADSet1.mono_set {S T : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 T delta alpha C) (hST : S ⊆ T) :
    PureWZ2PaperADSet1 S delta alpha C := by
  rcases hAD with ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  intro rho hrho hdelta left length hlen
  have h7 : (↑(Metric.externalCoveringNumber ⟨rho, hrho⟩
          (S ∩ Set.Icc left (left + length))) : ENNReal) ≤
        (↑(Metric.externalCoveringNumber ⟨rho, hrho⟩
          (T ∩ Set.Icc left (left + length))) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set
      (Set.inter_subset_inter_left _ hST)
  exact h7.trans (h6 rho hrho hdelta left length hlen)

/-- `PureWZ2PaperADSet1` is monotone in the constant. -/
lemma PureWZ2PaperADSet1.mono_const {S : Set ℝ} {delta alpha : ℝ} {C C' : ENNReal}
    (hAD : PureWZ2PaperADSet1 S delta alpha C) (hC : C ≤ C') (hC'_ne_top : C' ≠ ⊤) :
    PureWZ2PaperADSet1 S delta alpha C' := by
  rcases hAD with ⟨h1, h2, h3, h4, h5, h6⟩
  have h4' : 1 ≤ C' := le_trans h4 hC
  refine ⟨h1, h2, h3, h4', hC'_ne_top, ?_⟩
  intro rho hrho hdelta left length hlen
  have h7 := h6 rho hrho hdelta left length hlen
  have h8 : C * Kakeya.realRpowENN (length / rho) alpha ≤
      C' * Kakeya.realRpowENN (length / rho) alpha := by
    gcongr
  exact h7.trans h8

/-- External covering number scales under dilation of ℝ.

If `s > 0`, then `externalCoveringNumber (s*ε) (s • A) ≤ externalCoveringNumber ε A`. -/
lemma externalCoveringNumber_smul {s : ℝ} (hs : 0 < s) {ε : NNReal} {T : Set ℝ} :
    Metric.externalCoveringNumber (⟨s * ε, by positivity⟩ : NNReal) ((fun x : ℝ => s * x) '' T) ≤
    Metric.externalCoveringNumber ε T := by
  let f : ℝ → ℝ := fun x => s * x
  let K : NNReal := ⟨s, le_of_lt hs⟩
  have hK : (K : ℝ) = s := by
    change ↑(⟨s, le_of_lt hs⟩ : NNReal) = s <;> simp
  have h_lip : LipschitzWith K f := by
    intro x y
    have h1 : edist (f x) (f y) = ENNReal.ofReal (dist (f x) (f y)) := edist_dist (f x) (f y)
    rw [h1]
    have h2 : dist (f x) (f y) = s * dist x y := by
      have h21 : dist (f x) (f y) = |f x - f y| := by rfl
      rw [h21]
      have h22 : |f x - f y| = |s| * |x - y| := by
        have h23 : f x - f y = s * (x - y) := by simp [f] <;> ring
        rw [h23, abs_mul]
      rw [h22]
      have h24 : |s| = s := abs_of_pos hs
      rw [h24]
      have h25 : dist x y = |x - y| := by rfl
      rw [h25]
    rw [h2]
    have h3 : ENNReal.ofReal (s * dist x y) = ENNReal.ofReal s * ENNReal.ofReal (dist x y) := by
      rw [ENNReal.ofReal_mul (by positivity)]
    rw [h3]
    have h41 : (K : ENNReal) = ENNReal.ofReal (K : ℝ) := ENNReal.coe_nnreal_eq K
    have h4 : ENNReal.ofReal s = (K : ENNReal) := by
      rw [h41, hK]
    rw [h4]
    have h5 : edist x y = ENNReal.ofReal (dist x y) := edist_dist x y
    rw [h5]
  have h_key : K * ε = (⟨s * ε, by positivity⟩ : NNReal) := by
    ext; simp [K, NNReal.coe_mul] <;> norm_cast
  set a : ENat := Metric.externalCoveringNumber (K * ε) (f '' T) with ha_def
  have h_main : ∀ (C : Set ℝ), IsCover ε T C → a ≤ C.encard := by
    intro C hC
    have h_image_cover : IsCover (K * ε) (f '' T) (f '' C) := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      have h1 : ∃ y ∈ C, edist x y ≤ ε := hC hx
      rcases h1 with ⟨y, hy, hedist⟩
      refine ⟨f y, Set.mem_image_of_mem f hy, ?_⟩
      have h2 : edist (f x) (f y) ≤ (K : ENNReal) * edist x y := h_lip x y
      have h3 : (K : ENNReal) * edist x y ≤ (K : ENNReal) * (ε : ENNReal) := by gcongr
      have h4 : edist (f x) (f y) ≤ ↑(K * ε) := by simpa using h2.trans h3
      exact h4
    have h1 : a ≤ (f '' C).encard := by
      rw [ha_def]
      exact IsCover.externalCoveringNumber_le_encard h_image_cover
    have h2 : (f '' C).encard ≤ C.encard := Set.encard_image_le f C
    exact h1.trans h2
  have h_forall : ∀ (C : Set ℝ), a ≤ iInf (fun h : IsCover ε T C => C.encard) := by
    intro C
    by_cases hC : IsCover ε T C
    · have h_inner : iInf (fun h : IsCover ε T C => C.encard) = C.encard := by
        exact iInf_pos hC
      rw [h_inner]
      exact h_main C hC
    · have h_empty : IsEmpty (IsCover ε T C) := ⟨hC⟩
      have h_inner : iInf (fun h : IsCover ε T C => C.encard) = ⊤ := by
        exact iInf_neg hC
      rw [h_inner]
      exact le_top
  have h_goal : a ≤ Metric.externalCoveringNumber ε T := by
    have h : Metric.externalCoveringNumber ε T = iInf (fun C : Set ℝ => iInf (fun h : IsCover ε T C => C.encard)) := by rfl
    rw [h]
    exact le_iInf_iff.mpr h_forall
  rw [ha_def, h_key] at h_goal
  exact h_goal

/-- Dilation of a real interval: `s • Icc a b = Icc (s*a) (s*b)` for `s > 0`. -/
private lemma smul_Icc {s a b : ℝ} (hs : 0 < s) :
    (fun x : ℝ => s * x) '' Set.Icc a b = Set.Icc (s * a) (s * b) := by
  ext y
  simp only [Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    exact ⟨by gcongr, by gcongr⟩
  · rintro ⟨hy1, hy2⟩
    refine ⟨y / s, ⟨?_, ?_⟩, ?_⟩
    · have : s * a ≤ y := hy1
      calc a = (s * a) / s := by field_simp [hs.ne']
        _ ≤ y / s := by gcongr
    · have : y ≤ s * b := hy2
      calc y / s ≤ (s * b) / s := by gcongr
        _ = b := by field_simp [hs.ne']
    · field_simp [hs.ne']

/-- `PureWZ2PaperADSet1` transports under isotropic dilation of ℝ.

If `S` has AD at scale `delta` with constant `C`, then `s • S` has AD
at scale `s * delta` with the same constant `C`. -/
lemma PureWZ2PaperADSet1.smul {S : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 S delta alpha C) {s : ℝ} (hs : 0 < s) :
    PureWZ2PaperADSet1 ((fun x : ℝ => s * x) '' S) (s * delta) alpha C := by
  rcases hAD with ⟨h1, h2, h3, h4, h5, h6⟩
  have hsd : 0 < s * delta := mul_pos hs h1
  let f : ℝ → ℝ := fun x => s * x
  refine ⟨hsd, h2, h3, h4, h5, ?_⟩
  intro rho hrho hdelta left length hlen
  let eps : NNReal := ⟨rho / s, by positivity⟩
  have h_eps_nonneg : 0 ≤ s * (eps : ℝ) := by
    have h1 : 0 ≤ s := by linarith
    have h2 : 0 ≤ (eps : ℝ) := eps.prop
    exact mul_nonneg h1 h2
  let target_eps : NNReal := ⟨s * (eps : ℝ), h_eps_nonneg⟩
  have h14 : (⟨rho, hrho⟩ : NNReal) = target_eps := by
    apply NNReal.coe_injective
    change rho = s * (rho / s)
    field_simp [hs.ne']
  have h_eps_delta : delta ≤ rho / s := by
    have h : s * delta ≤ rho := hdelta
    calc delta = (s * delta) / s := by field_simp [hs.ne']
      _ ≤ rho / s := by gcongr
  have h_len : rho / s ≤ length / s := by gcongr
  have h_image_inter : f '' (S ∩ Set.Icc (left / s) (left / s + length / s)) =
      (f '' S) ∩ Set.Icc left (left + length) := by
    have h_inj : Function.Injective f := by
      intro x y h; apply mul_left_cancel₀ hs.ne'; exact h
    rw [Set.image_inter h_inj, smul_Icc hs]
    have h12 : s * (left / s) = left := by field_simp [hs.ne']
    have h13 : s * (left / s + length / s) = left + length := by
      field_simp [hs.ne']
    rw [h12, h13]
  have hcov : (↑(Metric.externalCoveringNumber ⟨rho, hrho⟩
          (f '' (S ∩ Set.Icc (left / s) (left / s + length / s)))) : ENNReal) ≤
      (↑(Metric.externalCoveringNumber eps
          (S ∩ Set.Icc (left / s) (left / s + length / s))) : ENNReal) := by
    rw [h14]
    exact_mod_cast externalCoveringNumber_smul (hs := hs) (ε := eps)
  rw [← h_image_inter]
  have h_src := h6 (rho / s) (by positivity) h_eps_delta (left / s) (length / s) h_len
  have h_ratio : (length / s) / (rho / s) = length / rho := by
    field_simp [hs.ne']
  rw [h_ratio] at h_src
  exact hcov.trans h_src

/-- Constant comparison for AD transport.

Given `s > 0`, `loss_src < loss`, and
`(delta')^(loss - loss_src) ≤ s^(-loss)`, we have
`realRpowENN delta' (-loss_src) ≤ realRpowENN (s * delta') (-loss)`. -/
lemma ad_constant_comparison {delta' s loss loss_src : ℝ}
    (hdelta'_pos : 0 < delta') (hs_pos : 0 < s)
    (hloss_lt : loss_src < loss)
    (hsmall : Real.rpow delta' (loss - loss_src) ≤ Real.rpow s (-loss)) :
    Kakeya.realRpowENN delta' (-loss_src) ≤ Kakeya.realRpowENN (s * delta') (-loss) := by
  set a := Real.rpow delta' (loss - loss_src) with ha_def
  set b := Real.rpow s (-loss) with hb_def
  set c := Real.rpow delta' (-loss) with hc_def
  have ha_pos : 0 < a := Real.rpow_pos_of_pos hdelta'_pos _
  have hb_pos : 0 < b := Real.rpow_pos_of_pos hs_pos _
  have hc_pos : 0 < c := Real.rpow_pos_of_pos hdelta'_pos _
  have h_ab : a ≤ b := hsmall
  have h_rpow_add : Real.rpow delta' ((loss - loss_src) + (-loss)) =
      Real.rpow delta' (loss - loss_src) * Real.rpow delta' (-loss) :=
    Real.rpow_add hdelta'_pos (loss - loss_src) (-loss)
  have h_exp_eq : (loss - loss_src) + (-loss) = -loss_src := by ring
  have h_src : Real.rpow delta' (-loss_src) = a * c := by
    have h : Real.rpow delta' (-loss_src) = Real.rpow delta' ((loss - loss_src) + (-loss)) := by
      rw [h_exp_eq]
    rw [h, h_rpow_add]
  have h_mul_rpow : Real.rpow (s * delta') (-loss) = b * c := by
    have h : Real.rpow (s * delta') (-loss) = Real.rpow s (-loss) * Real.rpow delta' (-loss) :=
      Real.mul_rpow (hx := by positivity) (hy := by positivity)
    exact h
  have h_ineq : a * c ≤ b * c := by
    exact mul_le_mul_of_nonneg_right h_ab (by positivity)
  have h6 : Real.rpow delta' (-loss_src) ≤ Real.rpow (s * delta') (-loss) := by
    rw [h_src, h_mul_rpow] <;> exact h_ineq
  have h_enn : ENNReal.ofReal (Real.rpow delta' (-loss_src)) ≤
      ENNReal.ofReal (Real.rpow (s * delta') (-loss)) :=
    ENNReal.ofReal_le_ofReal h6
  simpa [Kakeya.realRpowENN] using h_enn

/-- Helper: horizontal slice of dilated set. -/
private lemma horizontalSlice_dilate {E : Set Point3} {s z : ℝ} (hs : 0 < s) :
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

/-- Helper: scalar projection of dilated set. -/
private lemma scalarProjection_dilate {E : Set Point3} {s : ℝ} {v : Point3} (hs : 0 < s) :
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

/-- Helper: inverse dilation of a point in targetUnion lies in shading.union. -/
lemma dilate_point_in_union
    {s : ℝ} (hs_pos : 0 < s) {targetUnion : Set Point3}
    {shading_union : Set Point3}
    (h_target_sub : targetUnion ⊆ (fun p : Point3 => s • p) '' shading_union)
    (point : {point : Point3 // point ∈ targetUnion}) :
    (1 / s : ℝ) • (point : Point3) ∈ shading_union := by
  have h : (point : Point3) ∈ (fun p : Point3 => s • p) '' shading_union :=
    h_target_sub point.prop
  rcases h with ⟨p, hp, hpeq⟩
  have h_eq : (1 / s : ℝ) • (point : Point3) = p := by
    ext k
    have h5 : (s • p) k = (point : Point3) k :=
      congr_arg (fun x : Point3 => x k) hpeq
    have h6 : s * p k = (point : Point3) k := by simpa [Pi.smul_apply] using h5
    have h7 : (1 / s : ℝ) * (point : Point3) k = p k := by
      field_simp [hs_pos.ne'] <;> linarith
    simpa [Pi.smul_apply] using h7
  rw [h_eq] <;> exact hp

/-- Helper: monotonicity of scalarProjection in the set argument. -/
private lemma scalarProjection_mono {v : Point3} {A B : Set Point3} (h : A ⊆ B) :
    scalarProjection v A ⊆ scalarProjection v B := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

/-- Global AD transport under isotropic dilation. -/
lemma global_ad_transport
    {sigma loss loss_src delta' : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta'}
    {shading : WZ1PaperTubeShading family}
    (preGrains : PureWZ2PreGrainData shading sigma loss_src)
    {s : ℝ} (hs_pos : 0 < s) (hs_six : 6 ≤ s)
    {targetUnion : Set Point3}
    (h_target_sub : targetUnion ⊆ (fun p : Point3 => s • p) '' shading.union)
    (targetSlope : ℝ → ℝ)
    (h_slope_eq : ∀ z, targetSlope z = preGrains.slope (z / s))
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
  let v := globalGrainDirection (preGrains.slope (z / s))
  have hv : v = globalGrainDirection (targetSlope z) := by
    rw [h_slope_eq z]
  let sourceSet := scalarProjection v (horizontalSlice shading.union (z / s))
  have h_source_ad : PureWZ2PaperADSet1 sourceSet delta' (1 - sigma)
      (Kakeya.realRpowENN delta' (-loss_src)) :=
    preGrains.global_ad (z / s) hz1
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
    scalarProjection_mono h_slice_sub
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
      rw [horizontalSlice_dilate hs_pos, scalarProjection_dilate hs_pos]
    rw [h_eq2] at h_proj_sub
    exact h_proj_sub
  exact h_dilated_ad2.mono_set h_target_sub2

/-- Local AD transport under isotropic dilation. -/
lemma local_ad_transport
    {sigma loss loss_src delta' : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta'}
    {shading : WZ1PaperTubeShading family}
    (preGrains : PureWZ2PreGrainData shading sigma loss_src)
    {s : ℝ} (hs_pos : 0 < s) (hs_six : 6 ≤ s)
    {targetUnion : Set Point3}
    (h_target_sub : targetUnion ⊆ (fun p : Point3 => s • p) '' shading.union)
    (targetPlaneMap : {point : Point3 // point ∈ targetUnion} → Point3)
    (h_planeMap_eq : ∀ (point : {point : Point3 // point ∈ targetUnion}),
        targetPlaneMap point = preGrains.planeMap
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
  let v := targetPlaneMap point
  have hv_eq : v = preGrains.planeMap ⟨p', hp'_in⟩ := h_planeMap_eq point
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
  let sourceSet := scalarProjection (preGrains.planeMap ⟨p', hp'_in⟩) sourceBallSet
  have h_source_ad : PureWZ2PaperADSet1 sourceSet rho' (1 - sigma)
      (Kakeya.realRpowENN delta' (-loss_src)) :=
    preGrains.local_ad rho' h_rho'_ge h_rho'_le ⟨p', hp'_in⟩
  let dilatedSet := (fun x : ℝ => s * x) '' sourceSet
  have h_dilated_ad : PureWZ2PaperADSet1 dilatedSet (s * rho') (1 - sigma)
      (Kakeya.realRpowENN delta' (-loss_src)) :=
    h_source_ad.smul hs_pos
  have h_s_rho' : s * rho' = rho := by
    simp [rho'] <;> field_simp [hs_pos.ne']
  rw [h_s_rho'] at h_dilated_ad
  have h_const_le : Kakeya.realRpowENN delta' (-loss_src) ≤
      Kakeya.realRpowENN (s * delta') (-loss) :=
    ad_constant_comparison hdelta'_pos hs_pos hloss_lt hsmall
  have h_const_ne_top : Kakeya.realRpowENN (s * delta') (-loss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
  have h_dilated_ad2 : PureWZ2PaperADSet1 dilatedSet rho (1 - sigma)
      (Kakeya.realRpowENN (s * delta') (-loss)) :=
    h_dilated_ad.mono_const h_const_le h_const_ne_top
  let targetSet := scalarProjection v
      (targetUnion ∩ Metric.closedBall (point : Point3) (Real.sqrt rho))
  have h_proj_sub : scalarProjection v
        (targetUnion ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)) ⊆
      scalarProjection v ((fun p : Point3 => s • p) '' sourceBallSet) :=
    scalarProjection_mono h_ball_contain
  have h_target_sub2 : targetSet ⊆ dilatedSet := by
    have h_v : v = preGrains.planeMap ⟨p', hp'_in⟩ := hv_eq
    have h_eq1 : scalarProjection v ((fun p : Point3 => s • p) '' sourceBallSet) =
        (fun x : ℝ => s * x) '' scalarProjection v sourceBallSet := by
      rw [scalarProjection_dilate hs_pos]
    have h2 : targetSet ⊆ (fun x : ℝ => s * x) '' scalarProjection v sourceBallSet :=
      h_proj_sub.trans (h_eq1 ▸ Subset.refl _)
    rw [h_v] at h2
    simpa [targetSet, dilatedSet, sourceSet, h_v] using h2
  exact h_dilated_ad2.mono_set h_target_sub2

/-- `PureWZ2PaperADSet1` is inverse-closed under dilation: if `s • S` has AD
at scale `delta` with `s ≥ 1`, then `S` has AD at the same scale.

Proof: dilate by `1/s` to get AD at scale `delta/s`, then weaken the scale
since `delta/s ≤ delta`. -/
lemma PureWZ2PaperADSet1.of_smul
    {S : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    {s : ℝ} (hs : 1 ≤ s)
    (hAD : PureWZ2PaperADSet1 ((fun x : ℝ => s * x) '' S) delta alpha C) :
    PureWZ2PaperADSet1 S delta alpha C := by
  have hs_pos : 0 < s := by linarith
  have hdelta_pos : 0 < delta := hAD.1
  let t : ℝ := 1 / s
  have ht_pos : 0 < t := by positivity
  let g : ℝ → ℝ := fun x => t * x
  have h1 : PureWZ2PaperADSet1 (g '' ((fun x : ℝ => s * x) '' S)) (t * delta) alpha C :=
    PureWZ2PaperADSet1.smul hAD (s := t) ht_pos
  have h_scale_eq : t * delta = delta / s := by
    simp [t] <;> ring
  have h_image_eq : g '' ((fun x : ℝ => s * x) '' S) = S := by
    ext y
    simp only [g, Set.mem_image]
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      have h : (1 / s) * (s * x) = x := by
        field_simp [hs_pos.ne'] <;> ring
      rw [h] <;> exact hx
    · intro hy
      refine ⟨s * y, ⟨y, hy, by ring⟩, ?_⟩
      have h : t * (s * y) = y := by
        simp only [t]
        field_simp [hs_pos.ne'] <;> ring
      exact h
  rw [h_image_eq, h_scale_eq] at h1
  rcases h1 with ⟨hd_pos, h2, h3, h4, h5, h6⟩
  refine ⟨by linarith, h2, h3, h4, h5, ?_⟩
  intro rho hrho hdelta left length hlen
  have h_delta_s_le_delta : delta / s ≤ delta := by
    have h4 : 0 ≤ delta := hdelta_pos.le
    have h5 : 1 / s ≤ 1 := by
      have h6 : 0 < s := hs_pos
      have h7 : 1 ≤ s := hs
      calc 1 / s ≤ 1 / 1 := by gcongr
        _ = 1 := by norm_num
    calc delta / s = delta * (1 / s) := by ring
      _ ≤ delta * 1 := by gcongr
      _ = delta := by ring
  have h_delta_s_le_rho : delta / s ≤ rho := by
    calc delta / s ≤ delta := h_delta_s_le_delta
      _ ≤ rho := hdelta
  exact h6 rho hrho h_delta_s_le_rho left length hlen

/-- Global AD restriction from a shading to its subshading.

If `Z.union ⊆ Y.union` and `Y` has global AD with a given slope, then `Z`
has global AD with the same slope. The proof uses `PureWZ2PaperADSet1.mono_set`
on each horizontal slice, since the scalar projection of a subset is a subset
of the scalar projection. -/
lemma global_ad_restrict_to_subshading
    {delta sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y Z : WZ1PaperTubeShading F}
    (hsub : Z.union ⊆ Y.union)
    (slope : ℝ → ℝ)
    (C : ENNReal)
    (hAD_Y : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        PureWZ2PaperADSet1
          (scalarProjection (globalGrainDirection (slope z))
            (horizontalSlice Y.union z))
          delta (1 - sigma) C) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope z))
          (horizontalSlice Z.union z))
        delta (1 - sigma) C := by
  intro z hz
  let v := globalGrainDirection (slope z)
  have h1 : horizontalSlice Z.union z ⊆ horizontalSlice Y.union z := by
    intro p hp
    exact ⟨hsub hp.1, hp.2⟩
  have h2 : scalarProjection v (horizontalSlice Z.union z) ⊆
      scalarProjection v (horizontalSlice Y.union z) := by
    intro t ht
    rcases ht with ⟨p, hp, rfl⟩
    exact ⟨p, h1 hp, rfl⟩
  exact PureWZ2PaperADSet1.mono_set (hAD_Y z hz) h2

/-- Local grain data restriction from a shading to its subshading.

Given local grain data on `Y` and `Z` is a subshading of `Y`, restrict the
planeMap to the smaller domain and transfer all properties (Lipschitz, unit,
incidence, local AD) using subset monotonicity. -/
def local_grain_data_restrict
    {delta sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y Z : WZ1PaperTubeShading F}
    (hsub : PaperIsSubshading Z Y)
    (C : ENNReal)
    (data_Y : PureWZ2LocalGrainData Y sigma C) :
    PureWZ2LocalGrainData Z sigma C :=
  let hsub_union : Z.union ⊆ Y.union := by
    intro p hp
    rcases hp with ⟨i, hi⟩
    exact ⟨i, hsub i hi⟩
  let planeMap_Z : {point : Point3 // point ∈ Z.union} → Point3 :=
    fun p => data_Y.planeMap ⟨p, hsub_union p.prop⟩
  let incl : {point : Point3 // point ∈ Z.union} → {point : Point3 // point ∈ Y.union} :=
    fun p => ⟨p, hsub_union p.prop⟩
  have h_incl_lip : LipschitzWith 1 incl := by
    intro x y
    have h : edist (incl x) (incl y) = edist x y := by
      simp [incl, Subtype.edist_eq]
    rw [h]
    <;> simp
  have h_comp : LipschitzWith 1 planeMap_Z := by
    have h := LipschitzWith.comp data_Y.planeMap_lipschitz h_incl_lip
    have h_eq : planeMap_Z = data_Y.planeMap ∘ incl := by
      funext p
      <;> rfl
    rw [h_eq] at *
    simpa [mul_one] using h
  { planeMap := planeMap_Z
  , planeMap_lipschitz := h_comp
  , planeMap_unit := fun p => data_Y.planeMap_unit ⟨p, hsub_union p.prop⟩
  , planeMap_incidence := by
      intro index point hpoint
      exact data_Y.planeMap_incidence index point (hsub index hpoint)
  , local_ad := by
      intro rho hrho_delta hrho_one point
      let p_Y : {point : Point3 // point ∈ Y.union} := ⟨point, hsub_union point.prop⟩
      have h_set : (Z.union ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)) ⊆
          (Y.union ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)) := by
        intro x hx
        exact ⟨hsub_union hx.1, hx.2⟩
      have h_proj : scalarProjection (planeMap_Z point)
            (Z.union ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)) ⊆
          scalarProjection (data_Y.planeMap p_Y)
            (Y.union ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)) := by
        intro t ht
        rcases ht with ⟨x, hx, rfl⟩
        exact ⟨x, h_set hx, rfl⟩
      exact PureWZ2PaperADSet1.mono_set
        (data_Y.local_ad rho hrho_delta hrho_one p_Y) h_proj }

end Kakeya.Assouad

end
