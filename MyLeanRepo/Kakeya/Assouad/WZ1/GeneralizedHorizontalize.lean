import MyLeanRepo.Kakeya.Assouad.WZ1.ADAffineThickeningTransport
import MyLeanRepo.Kakeya.Assouad.WZ1.GeneralizedThickening
import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import Mathlib.Tactic

/-!
# Generalized horizontalization with large vertical component

The standard `per_cell_horizontalize_ad_transport` requires `|normal 2| ≤ 1/10`.
For the coarse plane map we only have `|normal 2| ≤ 1/2`.

This module provides a generalized version that works with `|normal 2| ≤ 1/2`
by using a larger thickening factor (2*δ instead of δ) and the thickening
transport lemma.

The horizontalization error is:
  |grain_proj(p) - affine(normal_proj(p))| ≤ |n2|/|n0| * |p2 - z|
≤ (1/2)/(1/3) * δ = 3/2 * δ

So the grain projection is contained in the (3/2*δ)-thickening of the affine
normal projection, which is within the 2*δ-thickening.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/--
Transport AD through an affine transform followed by an arbitrary thickening.

Unlike `generalized_thickening`, this does NOT require the intermediate
affine image to be bounded by `Icc (-4) 4`. It uses `affine_image_covering`
directly for the covering bound.
-/
lemma affine_generalized_thickening_transport
    {E B : Set ℝ} {δ α ε : ℝ} {C : ENNReal}
    {a b : ℝ}
    (hAD : IsADSet1 E δ α C)
    (ha_lower : 1 / 4 ≤ |a|)
    (ha_upper : |a| ≤ 4)
    (hthick : B ⊆ Metric.cthickening ε ((fun u : ℝ => a * u + b) '' E))
    (hB_bounded : B ⊆ Set.Icc (-4 : ℝ) 4)
    (hδ_pos : 0 < δ)
    (hα_pos : 0 < α)
    (hα_one : α ≤ 1)
    (hε_pos : 0 < ε) :
    IsADSet1 B δ α
      ((2 * (Nat.ceil (ε / δ) + 1) : ENNReal) ^ 2 * (10 * C)) := by
  let S : Set ℝ := (fun u : ℝ => a * u + b) '' E
  have h_affine_cover : ∀ (rho : ℝ) (hrho : 0 ≤ rho) (hdelta_rho : δ ≤ rho) (hrho_one : rho ≤ 1)
      (x : ℝ) (r : ℝ) (hrho_r : rho ≤ r) (hr_one : r ≤ 1),
      (↑(externalCoveringNumber ⟨rho, hrho⟩ (S ∩ Metric.closedBall x r)) : ENNReal) ≤
        (10 * C) * Kakeya.realRpowENN (r / rho) α :=
    hAD.affine_image_covering ha_lower ha_upper
  rcases hAD with ⟨hδ, hα, hα_one, hC_one, hE_bounded, hcover⟩
  let k : ℕ := Nat.ceil (ε / δ)
  let K : ℕ := 2 * (k + 1)
  have hK_pos : 0 < K := by positivity
  have h10C_one : (1 : ENNReal) ≤ 10 * C := by
    have h1 : (1 : ENNReal) ≤ C := hC_one
    have h2 : (1 : ENNReal) ≤ 10 := by norm_num
    calc (1 : ENNReal) ≤ 10 := by norm_num
         _ ≤ 10 * C := le_mul_of_one_le_right' h1
  have hC_target :
      (1 : ENNReal) ≤
        (2 * (Nat.ceil (ε / δ) + 1) : ENNReal) ^ 2 * (10 * C) := by
    have h_pos : 0 < 2 * (Nat.ceil (ε / δ) + 1) := by omega
    have h3 : (1 : ENNReal) ≤ (2 * (Nat.ceil (ε / δ) + 1) : ENNReal) := by
      exact_mod_cast h_pos
    have h4 : (1 : ENNReal) ≤ (2 * (Nat.ceil (ε / δ) + 1) : ENNReal) ^ 2 := by
      calc (1 : ENNReal) = 1 * 1 := by ring
           _ ≤ _ * _ := mul_le_mul' h3 h3
           _ = _ := by ring
    exact h4.trans (le_mul_of_one_le_right' h10C_one)
  refine ⟨hδ, hα, hα_one, hC_target, hB_bounded, ?_⟩
  intro ρ hρ hδ_ρ hρ_one x r hρ_r hr_one
  have hρ_pos : 0 < ρ := by linarith
  have hr_pos : 0 < r := by linarith
  set eps_nn : NNReal := ⟨ρ, by linarith⟩
  have h_kr : ε ≤ (k : ℝ) * δ := by
    have h : (k : ℝ) ≥ ε / δ := Nat.le_ceil (ε / δ)
    calc
      ε = (ε / δ) * δ := by field_simp [hδ.ne'] <;> ring
      _ ≤ (k : ℝ) * δ := by gcongr
  let k' : ℕ := Nat.ceil (ε / ρ)
  have hk'_le : k' ≤ k := by
    have h1 : ε / ρ ≤ ε / δ := by gcongr
    have h2 : ε / δ ≤ (k : ℝ) := Nat.le_ceil (ε / δ)
    exact Nat.ceil_le.mpr (h1.trans h2)
  let centers : Finset ℕ := Finset.range (2 * k + 2)
  let S_j : ℕ → Set ℝ := fun j =>
    S ∩ Metric.closedBall (x - 2 * ε - r + 2 * (j : ℝ) * r) r
  have hδ_r : δ ≤ r := hδ_ρ.trans hρ_r
  let S1 : Set ℝ := S ∩ Metric.closedBall x (r + 2 * ε)
  let S2 : Set ℝ := ⋃ j ∈ centers, S_j j
  have h_split_ball :
      Metric.closedBall x (r + 2 * ε) ⊆
        ⋃ j ∈ centers,
          Metric.closedBall (x - 2 * ε - r + 2 * (j : ℝ) * r) r :=
    closedBall_split_2k2 hr_pos hδ_r (by linarith) h_kr
  have h_split1 : S1 ⊆ S2 := by
    intro z hz
    rcases Set.mem_iUnion₂.mp (h_split_ball hz.2) with ⟨j, hj, hzj⟩
    exact Set.mem_iUnion₂.mpr ⟨j, hj, ⟨hz.1, hzj⟩⟩
  have h_contain :
      B ∩ Metric.closedBall x r ⊆ Metric.cthickening ε S1 :=
    thickening_inter_containment_general hε_pos hthick
  have h_cthick_union :
      Metric.cthickening ε S1 ⊆
        ⋃ j ∈ centers, Metric.cthickening ε (S_j j) := by
    have h1 : Metric.cthickening ε S1 ⊆ Metric.cthickening ε S2 := by
      intro y hy
      have h_inf : ∀ z ∈ S1, infEDist y S2 ≤ edist y z := by
        intro z hz
        exact Metric.infEDist_le_edist_of_mem (h_split1 hz)
      have h2 : infEDist y S2 ≤ infEDist y S1 := by
        simpa [Metric.infEDist, le_iInf_iff] using h_inf
      have h3 : infEDist y S1 ≤ ENNReal.ofReal ε := by
        simpa [Metric.cthickening] using hy
      exact h2.trans h3
    have h4 : Metric.cthickening ε S2 ⊆ ⋃ j ∈ centers, Metric.cthickening ε (S_j j) := by
      have h_union_eq : ∀ (s : Finset ℕ), Metric.cthickening ε (⋃ j ∈ s, S_j j) ⊆ ⋃ j ∈ s, Metric.cthickening ε (S_j j) := by
        intro s
        induction s using Finset.induction with
        | empty => simp
        | @insert a s ha ih =>
          have h1 : (⋃ j ∈ insert a s, S_j j) = S_j a ∪ (⋃ j ∈ s, S_j j) := by
            ext x; simp [ha, Finset.mem_insert, Set.mem_iUnion] <;> tauto
          have h2 : (⋃ j ∈ insert a s, Metric.cthickening ε (S_j j)) = Metric.cthickening ε (S_j a) ∪ (⋃ j ∈ s, Metric.cthickening ε (S_j j)) := by
            ext x; simp [ha, Finset.mem_insert, Set.mem_iUnion] <;> tauto
          rw [h1, Metric.cthickening_union, h2]
          exact Set.union_subset_union (Set.Subset.refl _) ih
      exact h_union_eq centers
    exact h1.trans h4
  have hB_sub :
      B ∩ Metric.closedBall x r ⊆
        ⋃ j ∈ centers, Metric.cthickening ε (S_j j) :=
    h_contain.trans h_cthick_union
  have h_finite_union :
      (↑(externalCoveringNumber eps_nn
          (⋃ j ∈ centers, Metric.cthickening ε (S_j j))) : ENNReal) ≤
        ∑ j ∈ centers,
          (↑(externalCoveringNumber eps_nn (Metric.cthickening ε (S_j j))) : ENNReal) :=
    externalCoveringNumber_finite_union_le centers (fun j => Metric.cthickening ε (S_j j))
  have h_main1 :
      externalCoveringNumber eps_nn (B ∩ Metric.closedBall x r) ≤
        externalCoveringNumber eps_nn (⋃ j ∈ centers, Metric.cthickening ε (S_j j)) :=
    externalCoveringNumber_mono_set hB_sub
  have h_each : ∀ j ∈ centers,
      (↑(externalCoveringNumber eps_nn (Metric.cthickening ε (S_j j))) : ENNReal) ≤
        (2 * k' + 2 : ENNReal) * (10 * C) *
          Kakeya.realRpowENN (r / ρ) α := by
    intro j _
    have h_thick :
        (↑(externalCoveringNumber eps_nn (Metric.cthickening ε (S_j j))) : ENNReal) ≤
          (2 * k' + 2 : ENNReal) * ↑(externalCoveringNumber eps_nn (S_j j)) := by
      exact_mod_cast externalCoveringNumber_cthickening_general hε_pos hρ_pos
    have h_AD :
        (↑(externalCoveringNumber eps_nn (S_j j)) : ENNReal) ≤
          (10 * C) * Kakeya.realRpowENN (r / ρ) α :=
      h_affine_cover ρ hρ hδ_ρ hρ_one
        (x - 2 * ε - r + 2 * (j : ℝ) * r) r hρ_r hr_one
    exact h_thick.trans (by
      calc
        (2 * k' + 2 : ENNReal) * ↑(externalCoveringNumber eps_nn (S_j j)) ≤
          (2 * k' + 2 : ENNReal) * ((10 * C) * Kakeya.realRpowENN (r / ρ) α) := by gcongr
        _ = _ := by ring)
  have h_sum :
      ∑ j ∈ centers,
          (↑(externalCoveringNumber eps_nn (Metric.cthickening ε (S_j j))) : ENNReal) ≤
        (centers.card : ENNReal) * (2 * k' + 2 : ENNReal) * (10 * C) *
          Kakeya.realRpowENN (r / ρ) α := by
    calc
      _ ≤ ∑ _j ∈ centers,
            ((2 * k' + 2 : ENNReal) * (10 * C) * Kakeya.realRpowENN (r / ρ) α) :=
        Finset.sum_le_sum h_each
      _ = _ := by simp [centers, Finset.sum_const] <;> ring
  have h_centers_card : centers.card = 2 * k + 2 := by
    simp [centers] <;> omega
  have hK_eq :
      (K : ENNReal) = (2 * (Nat.ceil (ε / δ) + 1) : ENNReal) := by
    simp [K, k] <;> norm_cast
  have h_final :
      (centers.card : ENNReal) * (2 * k' + 2 : ENNReal) ≤ (K : ENNReal) ^ 2 := by
    have h_card' : (centers.card : ENNReal) = 2 * (k : ENNReal) + 2 := by
      rw [h_centers_card] <;> norm_cast <;> ring
    rw [h_card']
    have h1 :
        (2 * (k : ENNReal) + 2) * (2 * (k' : ENNReal) + 2) ≤
          (2 * (k : ENNReal) + 2) * (2 * (k : ENNReal) + 2) := by
      gcongr <;> exact_mod_cast hk'_le
    have h2 : 2 * (k : ENNReal) + 2 = (K : ENNReal) := by
      simp [K] <;> norm_cast <;> ring
    calc
      (2 * (k : ENNReal) + 2) * (2 * (k' : ENNReal) + 2) ≤
          (2 * (k : ENNReal) + 2) * (2 * (k : ENNReal) + 2) := h1
      _ = (K : ENNReal) ^ 2 := by rw [h2, pow_two]
  calc
    (↑(externalCoveringNumber eps_nn (B ∩ Metric.closedBall x r)) : ENNReal) ≤
      ↑(externalCoveringNumber eps_nn (⋃ j ∈ centers, Metric.cthickening ε (S_j j))) := by
        exact_mod_cast h_main1
    _ ≤ ∑ j ∈ centers,
          (↑(externalCoveringNumber eps_nn (Metric.cthickening ε (S_j j))) : ENNReal) :=
      h_finite_union
    _ ≤ (centers.card : ENNReal) * (2 * k' + 2 : ENNReal) * (10 * C) *
          Kakeya.realRpowENN (r / ρ) α := h_sum
    _ ≤ (K : ENNReal) ^ 2 * (10 * C) * Kakeya.realRpowENN (r / ρ) α := by
      gcongr
    _ = (2 * (Nat.ceil (ε / δ) + 1) : ENNReal) ^ 2 * (10 * C) *
          Kakeya.realRpowENN (r / ρ) α := by
      rw [hK_eq] <;> ring

/--
Generalized horizontalization inequality: the grain projection is within
`(|n2|/|n0|) * |p2-z|` of an affine transform of the normal projection.
-/
lemma generalized_horizontalize_slab_containment
    {E : Set Point3} {normal : Point3} {z delta : ℝ}
    (hnorm : ‖normal‖ = 1)
    (hn0 : 1 / 3 ≤ |normal 0|)
    (hn2 : |normal 2| ≤ 1 / 2)
    (hslab : ∀ p ∈ E, p 2 ∈ Set.Icc (z - delta) (z + delta))
    (hdelta : 0 < delta) :
    scalarProjection (globalGrainDirection (normal 1 / normal 0)) E ⊆
    Metric.cthickening (2 * delta)
      ((fun u : ℝ => u / normal 0 - normal 2 * z / normal 0) ''
        (scalarProjection normal E)) := by
  have hn0_pos : 0 < |normal 0| := by linarith
  have hn0_ne : normal 0 ≠ 0 := abs_ne_zero.mp hn0_pos.ne'
  have h_ratio : |normal 2| / |normal 0| ≤ 3 / 2 := by
    calc
      |normal 2| / |normal 0| ≤ (1 / 2 : ℝ) / |normal 0| := by gcongr
      _ ≤ (1 / 2 : ℝ) / (1 / 3 : ℝ) := by gcongr
      _ = 3 / 2 := by norm_num
  intro y hy
  rcases hy with ⟨p, hp, rfl⟩
  let u : ℝ := inner ℝ p normal
  have hu : u ∈ scalarProjection normal E := ⟨p, hp, rfl⟩
  let x : ℝ := u / normal 0 - normal 2 * z / normal 0
  have hx : x ∈ (fun u : ℝ => u / normal 0 - normal 2 * z / normal 0) ''
      (scalarProjection normal E) := ⟨u, hu, rfl⟩
  have h_sum3 : ∀ (a b : Point3), inner ℝ a b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
    intro a b
    rw [PiLp.inner_apply]
    simp [Fin.sum_univ_succ, mul_comm] <;> ring
  have h_inner_dir : inner ℝ p (globalGrainDirection (normal 1 / normal 0)) =
      p 0 + (normal 1 / normal 0) * p 1 := by
    rw [h_sum3] <;> simp [globalGrainDirection] <;> ring
  have h_inner_normal1 : inner ℝ p normal =
      normal 0 * p 0 + normal 1 * p 1 + normal 2 * p 2 := by
    rw [h_sum3] <;> ring
  have h_inner_normal : u = normal 0 * p 0 + normal 1 * p 1 + normal 2 * p 2 :=
    h_inner_normal1
  have h_x_eq : x = p 0 + (normal 1 / normal 0) * p 1 + (normal 2 / normal 0) * (p 2 - z) := by
    have h : x = (u - normal 2 * z) / normal 0 := by
      simp only [x] <;> ring
    rw [h, h_inner_normal]
    field_simp [hn0_ne] <;> ring
  have h_main : |inner ℝ p (globalGrainDirection (normal 1 / normal 0)) - x| ≤ 2 * delta := by
    rw [h_inner_dir, h_x_eq]
    have h5 : (p 0 + (normal 1 / normal 0) * p 1) -
          (p 0 + (normal 1 / normal 0) * p 1 + (normal 2 / normal 0) * (p 2 - z)) =
        -((normal 2 / normal 0) * (p 2 - z)) := by ring
    rw [h5]
    have h_abs : |-((normal 2 / normal 0) * (p 2 - z))| =
        |normal 2| / |normal 0| * |p 2 - z| := by
      calc
        |-((normal 2 / normal 0) * (p 2 - z))|
          = |(normal 2 / normal 0) * (p 2 - z)| := by rw [abs_neg]
        _ = |normal 2 / normal 0| * |p 2 - z| := by rw [abs_mul]
        _ = |normal 2| / |normal 0| * |p 2 - z| := by rw [abs_div]
    rw [h_abs]
    have h8 : p 2 ∈ Set.Icc (z - delta) (z + delta) := hslab p hp
    have h7 : |p 2 - z| ≤ delta := by
      have h73 : -delta ≤ p 2 - z := by linarith [h8.1]
      have h74 : p 2 - z ≤ delta := by linarith [h8.2]
      exact abs_le.mpr ⟨h73, h74⟩
    have h9 : |normal 2| / |normal 0| * |p 2 - z| ≤ (3 / 2 : ℝ) * delta := by
      calc
        |normal 2| / |normal 0| * |p 2 - z|
          ≤ (3 / 2 : ℝ) * |p 2 - z| := by gcongr
        _ ≤ (3 / 2 : ℝ) * delta := by gcongr
    have h10 : (3 / 2 : ℝ) * delta ≤ 2 * delta := by linarith
    exact h9.trans h10
  let affine_set : Set ℝ := (fun u : ℝ => u / normal 0 - normal 2 * z / normal 0) ''
      (scalarProjection normal E)
  exact Metric.mem_cthickening_of_dist_le
    (inner ℝ p (globalGrainDirection (normal 1 / normal 0))) x (2 * delta)
    affine_set hx h_main

/--
Generalized per-cell horizontalization AD transport.

Works with `|normal 2| ≤ 1/2` (instead of `1/10`) by using a 2*δ thickening.
Constant blowup: affine factor 10 × thickening factor 36 = 360.
-/
lemma generalized_per_cell_horizontalize_ad
    {E : Set Point3} {normal : Point3} {z delta alpha : ℝ} {C : ENNReal}
    (hdelta : 0 < delta)
    (hdelta_one : delta ≤ 1)
    (halpha : 0 < alpha)
    (halpha_one : alpha ≤ 1)
    (hnorm : ‖normal‖ = 1)
    (hn0 : 1 / 3 ≤ |normal 0|)
    (hn2 : |normal 2| ≤ 1 / 2)
    (hslab : ∀ p ∈ E, p 2 ∈ Set.Icc (z - delta) (z + delta))
    (hE_unitBall : E ⊆ Metric.closedBall (0 : Point3) 1)
    (hAD : IsADSet1 (scalarProjection normal E) delta alpha C) :
    IsADSet1 (scalarProjection (globalGrainDirection (normal 1 / normal 0)) E)
      delta alpha (360 * C) := by
  let a : ℝ := 1 / normal 0
  let b : ℝ := -normal 2 * z / normal 0
  let affine_image : Set ℝ := (fun u : ℝ => u / normal 0 - normal 2 * z / normal 0) '' (scalarProjection normal E)
  let target : Set ℝ := scalarProjection (globalGrainDirection (normal 1 / normal 0)) E
  have hn0_le_one : |normal 0| ≤ 1 := by
    have h : |normal 0| ≤ ‖normal‖ := PiLp.norm_apply_le normal 0
    rw [hnorm] at h
    exact h
  have haLower : 1 / 4 ≤ |a| := by
    have h1 : |a| = 1 / |normal 0| := by
      have h_eq : a = 1 / normal 0 := by rfl
      rw [h_eq, abs_div] <;> simp
    rw [h1]
    have h2 : 1 ≤ 1 / |normal 0| := by
      calc 1 / |normal 0| ≥ 1 / (1 : ℝ) := by gcongr
           _ = 1 := by norm_num
    linarith
  have haUpper : |a| ≤ 4 := by
    have h1 : |a| = 1 / |normal 0| := by
      have h_eq : a = 1 / normal 0 := by rfl
      rw [h_eq, abs_div] <;> simp
    rw [h1]
    have h2 : 1 / |normal 0| ≤ 1 / (1 / 3 : ℝ) := by gcongr
    norm_num at h2 ⊢ <;> linarith
  have htargetBound : target ⊆ Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨p, hp, rfl⟩
    have hpNorm : ‖p‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hE_unitBall hp
    let direction := globalGrainDirection (normal 1 / normal 0)
    have hdir_norm : ‖direction‖ ≤ 4 := by
      let e0 : Point3 := EuclideanSpace.single 0 (1 : ℝ)
      let e1 : Point3 := EuclideanSpace.single 1 (1 : ℝ)
      have heq : direction = e0 + (normal 1 / normal 0) • e1 := by
        ext i; fin_cases i <;> simp [direction, globalGrainDirection, e0, e1] <;> norm_num
      rw [heq]
      have he0 : ‖e0‖ = 1 := by rw [PiLp.norm_single] <;> norm_num
      have he1 : ‖e1‖ = 1 := by rw [PiLp.norm_single] <;> norm_num
      have hslope : |normal 1 / normal 0| ≤ 3 := by
        rw [abs_div]
        have h1 : |normal 1| ≤ 1 := by
          let e1_local : Point3 := EuclideanSpace.single 1 (1 : ℝ)
          have hinner : inner ℝ normal e1_local = normal 1 := by
            rw [EuclideanSpace.inner_single_right] <;> simp
          have hnorm1 : ‖e1_local‖ = 1 := by rw [PiLp.norm_single] <;> norm_num
          have hbound : |inner ℝ normal e1_local| ≤ ‖normal‖ * ‖e1_local‖ := abs_real_inner_le_norm normal e1_local
          rw [hinner, hnorm, hnorm1] at hbound
          simpa using hbound
        calc |normal 1| / |normal 0| ≤ 1 / |normal 0| := by gcongr
             _ ≤ 1 / (1 / 3 : ℝ) := by gcongr
             _ = 3 := by norm_num
      calc ‖e0 + (normal 1 / normal 0) • e1‖
          ≤ ‖e0‖ + ‖(normal 1 / normal 0) • e1‖ := norm_add_le _ _
        _ = 1 + |normal 1 / normal 0| := by rw [he0, norm_smul, he1] <;> simp only [mul_one, Real.norm_eq_abs]
        _ ≤ 1 + 3 := by gcongr
        _ = 4 := by norm_num
    have hinner : |inner ℝ p direction| ≤ ‖p‖ * ‖direction‖ := abs_real_inner_le_norm p direction
    have hbound : |inner ℝ p direction| ≤ 4 := by
      calc |inner ℝ p direction| ≤ ‖p‖ * ‖direction‖ := hinner
           _ ≤ 1 * 4 := by gcongr
           _ = 4 := by ring
    exact (abs_le.mp hbound)
  have hthick : target ⊆ Metric.cthickening (2 * delta) affine_image := by
    simpa [target, affine_image, a, b] using generalized_horizontalize_slab_containment hnorm hn0 hn2 hslab hdelta
  have h_affine_eq : (fun u : ℝ => a * u + b) = (fun u : ℝ => u / normal 0 - normal 2 * z / normal 0) := by
    funext u; simp [a, b] <;> ring
  have hthick2 : target ⊆ Metric.cthickening (2 * delta) ((fun u : ℝ => a * u + b) '' scalarProjection normal E) := by
    rw [h_affine_eq]
    exact hthick
  have h2δ_pos : 0 < 2 * delta := by positivity
  have h_final : IsADSet1 target delta alpha
      ((2 * (Nat.ceil ((2 * delta) / delta) + 1) : ENNReal) ^ 2 * (10 * C)) :=
    affine_generalized_thickening_transport
      (E := scalarProjection normal E) (B := target) (δ := delta) (α := alpha) (ε := 2 * delta)
      (C := C) (a := a) (b := b)
      hAD haLower haUpper hthick2 htargetBound hdelta halpha halpha_one h2δ_pos
  have h_ceil : Nat.ceil ((2 * delta) / delta) = 2 := by
    have hdiv : (2 * delta) / delta = 2 := by
      field_simp [hdelta.ne'] <;> ring
    rw [hdiv] <;> norm_num
  rw [h_ceil] at h_final
  have h_eq : ((2 * (2 + 1) : ENNReal) ^ 2 * (10 * C)) = (360 * C) := by
    have h1 : (2 * (2 + 1) : ENNReal) = 6 := by norm_num
    rw [h1]
    have h2 : (6 : ENNReal) ^ 2 = 36 := by norm_num
    rw [h2]
    have h3 : (36 : ENNReal) * (10 * C) = 360 * C := by
      calc (36 : ENNReal) * (10 * C) = (36 * (10 : ENNReal)) * C := by rw [mul_assoc]
        _ = (360 : ENNReal) * C := by norm_cast
        _ = 360 * C := by rfl
    exact h3
  exact h_eq ▸ h_final

end Kakeya.Assouad
