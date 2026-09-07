import MyLeanRepo.Kakeya.Assouad.WZ1.VerticalRescalingADStatement
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.Cover

/-!
# Final theorem assembly for WZ1 vertical rescaling AD transport

This file proves `wz1_vertical_rescaling_ad` using:
- Derivative chain-rule helpers for `gNew.IsNormalized`
- Scalar projection set equality for conclusion 2
- ADSet1 dilation lemma for conclusion 3
-/

noncomputable section

namespace Kakeya.Assouad

open Matrix

-- ===== Derivative helpers =====

lemma deriv_rescaled_slope (g : SlopeFunction) (c h M : ℝ) (t : ℝ) :
    deriv (fun t => g (c + h * t) / M) t = h * deriv g (c + h * t) / M := by
  have h_cd : ContDiff ℝ 2 g := g.contDiff
  have h_diff : Differentiable ℝ g := h_cd.differentiable (by norm_num)
  have h1 : HasDerivAt g (deriv g (c + h * t)) (c + h * t) :=
    h_diff.differentiableAt.hasDerivAt
  have h_const_h : HasDerivAt (fun x : ℝ => h) 0 t := hasDerivAt_const t h
  have h_id : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
  have h_mul : HasDerivAt (fun x : ℝ => h * x) (0 * t + h * 1) t :=
    HasDerivAt.mul h_const_h h_id
  have h_mul' : HasDerivAt (fun x : ℝ => h * x) h t := by
    have h_eq : 0 * t + h * 1 = h := by ring
    rw [h_eq] at h_mul
    exact h_mul
  have h_const_c : HasDerivAt (fun x : ℝ => c) 0 t := hasDerivAt_const t c
  have h2 : HasDerivAt (fun x : ℝ => c + h * x) h t := by
    have h_add : HasDerivAt (fun x => c + h * x) (0 + h) t :=
      HasDerivAt.add h_const_c h_mul'
    have h_eq : 0 + h = h := by ring
    rw [h_eq] at h_add
    exact h_add
  have hcomp : HasDerivAt (g ∘ (fun t : ℝ => c + h * t)) (deriv g (c + h * t) * h) t :=
    HasDerivAt.comp t h1 h2
  have hcomp' : HasDerivAt (fun t => g (c + h * t)) (deriv g (c + h * t) * h) t := by
    convert hcomp using 1; funext x; rfl
  have h_const_1M : HasDerivAt (fun x : ℝ => 1 / M) 0 t := hasDerivAt_const t (1 / M)
  have hdiv : HasDerivAt (fun t => g (c + h * t) * (1 / M))
      ((deriv g (c + h * t) * h) * (1 / M) + g (c + h * t) * 0) t :=
    HasDerivAt.mul hcomp' h_const_1M
  have hdiv' : HasDerivAt (fun t => g (c + h * t) / M) (deriv g (c + h * t) * h / M) t := by
    have h_eq1 : (fun t : ℝ => g (c + h * t) * (1 / M)) = (fun t => g (c + h * t) / M) := by
      funext x; ring
    have h_eq2 : (deriv g (c + h * t) * h) * (1 / M) + g (c + h * t) * 0 =
        deriv g (c + h * t) * h / M := by ring
    rw [h_eq1] at hdiv
    rw [h_eq2] at hdiv
    exact hdiv
  have h5 : deriv g (c + h * t) * h / M = h * deriv g (c + h * t) / M := by ring
  rw [h5] at hdiv'
  exact hdiv'.deriv

lemma second_deriv_rescaled_slope (g : SlopeFunction) (c h M : ℝ) (t : ℝ) :
    deriv (deriv (fun t => g (c + h * t) / M)) t =
    h^2 * deriv (deriv g) (c + h * t) / M := by
  have h_cd : ContDiff ℝ 2 g := g.contDiff
  have h_cd1 : ContDiff ℝ 1 (deriv g) := ContDiff.deriv' h_cd
  have h_diff2 : Differentiable ℝ (deriv g) := h_cd1.differentiable (by norm_num)
  have h_deriv1 : (deriv (fun t : ℝ => g (c + h * t) / M)) =
      fun t => h * deriv g (c + h * t) / M := by
    funext x
    exact deriv_rescaled_slope g c h M x
  rw [h_deriv1]
  have h1 : HasDerivAt (deriv g) (deriv (deriv g) (c + h * t)) (c + h * t) :=
    h_diff2.differentiableAt.hasDerivAt
  have h_const_h : HasDerivAt (fun x : ℝ => h) 0 t := hasDerivAt_const t h
  have h_id : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
  have h_mul : HasDerivAt (fun x : ℝ => h * x) (0 * t + h * 1) t :=
    HasDerivAt.mul h_const_h h_id
  have h_mul' : HasDerivAt (fun x : ℝ => h * x) h t := by
    have h_eq : 0 * t + h * 1 = h := by ring
    rw [h_eq] at h_mul
    exact h_mul
  have h_const_c : HasDerivAt (fun x : ℝ => c) 0 t := hasDerivAt_const t c
  have h2 : HasDerivAt (fun x : ℝ => c + h * x) h t := by
    have h_add : HasDerivAt (fun x => c + h * x) (0 + h) t :=
      HasDerivAt.add h_const_c h_mul'
    have h_eq : 0 + h = h := by ring
    rw [h_eq] at h_add
    exact h_add
  have hcomp : HasDerivAt ((deriv g) ∘ (fun t : ℝ => c + h * t))
      (deriv (deriv g) (c + h * t) * h) t :=
    HasDerivAt.comp t h1 h2
  have hcomp' : HasDerivAt (fun t => deriv g (c + h * t))
      (deriv (deriv g) (c + h * t) * h) t := by
    convert hcomp using 1; funext x; rfl
  have h_const_1M : HasDerivAt (fun x : ℝ => 1 / M) 0 t := hasDerivAt_const t (1 / M)
  have hdiv : HasDerivAt (fun t => deriv g (c + h * t) * (1 / M))
      ((deriv (deriv g) (c + h * t) * h) * (1 / M) + deriv g (c + h * t) * 0) t :=
    HasDerivAt.mul hcomp' h_const_1M
  have hdiv' : HasDerivAt (fun t => deriv g (c + h * t) / M)
      (deriv (deriv g) (c + h * t) * h / M) t := by
    have h_eq1 : (fun t : ℝ => deriv g (c + h * t) * (1 / M)) = (fun t => deriv g (c + h * t) / M) := by
      funext x; ring
    have h_eq2 : (deriv (deriv g) (c + h * t) * h) * (1 / M) + deriv g (c + h * t) * 0 =
        deriv (deriv g) (c + h * t) * h / M := by ring
    rw [h_eq1] at hdiv
    rw [h_eq2] at hdiv
    exact hdiv
  have h_const_h2 : HasDerivAt (fun x : ℝ => h) 0 t := hasDerivAt_const t h
  have hscale : HasDerivAt (fun t => h * (deriv g (c + h * t) / M))
      (0 * (deriv g (c + h * t) / M) + h * (deriv (deriv g) (c + h * t) * h / M)) t :=
    HasDerivAt.mul h_const_h2 hdiv'
  have hscale' : HasDerivAt (fun t => h * deriv g (c + h * t) / M)
      (h * (deriv (deriv g) (c + h * t) * h) / M) t := by
    have h_eq1 : (fun t : ℝ => h * (deriv g (c + h * t) / M)) = (fun t => h * deriv g (c + h * t) / M) := by
      funext x; ring
    have h_eq2 : 0 * (deriv g (c + h * t) / M) + h * (deriv (deriv g) (c + h * t) * h / M) =
        h * (deriv (deriv g) (c + h * t) * h) / M := by ring
    rw [h_eq1] at hscale
    rw [h_eq2] at hscale
    exact hscale
  have hfinal : h * (deriv (deriv g) (c + h * t) * h) / M =
      h^2 * deriv (deriv g) (c + h * t) / M := by ring
  rw [hfinal] at hscale'
  exact hscale'.deriv

-- ===== Set equality helpers =====

private lemma slice_image_eq (c h M : ℝ) (hh : 0 < h) (E : Set Point3) (t : ℝ) :
    (wz1VerticalRescalingMap c h M) '' horizontalSlice E (c + h * t) =
    horizontalSlice ((wz1VerticalRescalingMap c h M) '' E) t := by
  have hΦ2 : ∀ (p : Point3),
      (wz1VerticalRescalingMap c h M p) (2 : Fin 3) = (p (2 : Fin 3) - c) / h := by
    intro p
    simp [wz1VerticalRescalingMap, point3]
  ext q
  simp only [Set.mem_image, horizontalSlice, Set.mem_setOf_eq]
  constructor
  · rintro ⟨p, ⟨hpE, hpz⟩, rfl⟩
    refine ⟨⟨p, hpE, rfl⟩, ?_⟩
    have h : (wz1VerticalRescalingMap c h M p) (2 : Fin 3) = t := by
      rw [hΦ2 p, hpz]
      field_simp [hh.ne']; ring
    exact h
  · rintro ⟨⟨p, hpE, rfl⟩, hqz⟩
    have h_z : (p (2 : Fin 3) - c) / h = t := by
      have h_eq : (wz1VerticalRescalingMap c h M p) (2 : Fin 3) = t := hqz
      rw [hΦ2 p] at h_eq
      exact h_eq
    have hpz : p (2 : Fin 3) = c + h * t := by
      have h' : p (2 : Fin 3) - c = h * t := by
        field_simp [hh.ne'] at h_z ⊢; linarith
      linarith
    exact ⟨p, ⟨hpE, hpz⟩, rfl⟩

private lemma inner_product_identity (g : SlopeFunction) (c h M : ℝ) (t : ℝ) (p : Point3) :
    inner ℝ (wz1VerticalRescalingMap c h M p)
        (globalGrainDirection ((wz1VerticalRescaledSlope g c h M) t)) =
    inner ℝ p (globalGrainDirection (g (c + h * t))) / M^2 := by
  let m_new := (wz1VerticalRescaledSlope g c h M) t
  let m_old := g (c + h * t)
  have hm : m_new = m_old / M := by rfl
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
      rw [←h_basis0]
      exact EuclideanSpace.inner_basisFun_real (Fin 3) q 0
    have h_coord1 : inner ℝ q (EuclideanSpace.single (1 : Fin 3) 1) = q 1 := by
      rw [←h_basis1]
      exact EuclideanSpace.inner_basisFun_real (Fin 3) q 1
    rw [h_linearity, h_coord0, h_coord1]
  have h_p0 : (wz1VerticalRescalingMap c h M p) 0 = p 0 / M^2 := by
    simp [wz1VerticalRescalingMap, point3]
  have h_p1 : (wz1VerticalRescalingMap c h M p) 1 = p 1 / M := by
    simp [wz1VerticalRescalingMap, point3]
  calc
    inner ℝ (wz1VerticalRescalingMap c h M p) (globalGrainDirection m_new)
      = (wz1VerticalRescalingMap c h M p) 0 + m_new * (wz1VerticalRescalingMap c h M p) 1 :=
        h_eval _ _
    _ = p 0 / M^2 + (m_old / M) * (p 1 / M) := by
      rw [h_p0, h_p1, hm]
    _ = (p 0 + m_old * p 1) / M^2 := by ring
    _ = inner ℝ p (globalGrainDirection m_old) / M^2 := by
      rw [h_eval p m_old]

lemma scalar_projection_equality (g : SlopeFunction) (c h M : ℝ) (hh : 0 < h)
    (E : Set Point3) (t : ℝ) :
    scalarProjection (globalGrainDirection ((wz1VerticalRescaledSlope g c h M) t))
        (horizontalSlice ((wz1VerticalRescalingMap c h M) '' E) t) =
    (fun u : ℝ => u / M^2) ''
      scalarProjection (globalGrainDirection (g (c + h * t)))
        (horizontalSlice E (c + h * t)) := by
  let Φ := wz1VerticalRescalingMap c h M
  let v := globalGrainDirection ((wz1VerticalRescaledSlope g c h M) t)
  let w := globalGrainDirection (g (c + h * t))
  let S := horizontalSlice E (c + h * t)
  have h3 : Φ '' S = horizontalSlice (Φ '' E) t := slice_image_eq c h M hh E t
  have h4 : ∀ (p : Point3), inner ℝ (Φ p) v = inner ℝ p w / M^2 :=
    fun p => inner_product_identity g c h M t p
  have h_img : (fun p : Point3 => inner ℝ (Φ p) v) '' S =
      (fun x : Point3 => inner ℝ x v) '' (Φ '' S) := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨Φ p, ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
  have h_img2 : (fun p : Point3 => (inner ℝ p w) / M^2) '' S =
      (fun u : ℝ => u / M^2) '' ((fun p : Point3 => inner ℝ p w) '' S) := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨inner ℝ p w, ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
  calc
    scalarProjection v (horizontalSlice (Φ '' E) t)
      = (fun x : Point3 => inner ℝ x v) '' horizontalSlice (Φ '' E) t := by rfl
    _ = (fun x : Point3 => inner ℝ x v) '' (Φ '' S) := by rw [h3]
    _ = (fun p : Point3 => inner ℝ (Φ p) v) '' S := by rw [h_img]
    _ = (fun p : Point3 => (inner ℝ p w) / M^2) '' S := by
      apply Set.image_congr
      intro p _
      exact h4 p
    _ = (fun u : ℝ => u / M^2) '' ((fun p : Point3 => inner ℝ p w) '' S) := by rw [h_img2]
    _ = (fun u : ℝ => u / M^2) '' scalarProjection w S := by rfl

-- ===== Covering number helpers =====

open Metric Set

private lemma externalCoveringNumber_exists
    {X : Type*} [PseudoEMetricSpace X] {ε : NNReal} {A : Set X}
    (_h : externalCoveringNumber ε A ≠ ⊤) :
    ∃ C : Set X, IsCover ε A C ∧ C.encard = externalCoveringNumber ε A := by
  have h_nonempty : Nonempty {s : Set X // IsCover ε A s} :=
    ⟨⟨A, IsCover.refl ε A⟩⟩
  obtain ⟨C, hC⟩ := ENat.exists_eq_iInf
    (fun C : {s : Set X // IsCover ε A s} => (C : Set X).encard)
  have h_eq : (C : Set X).encard = externalCoveringNumber ε A := by
    simpa [externalCoveringNumber, iInf_subtype] using hC
  exact ⟨(C : Set X), C.property, h_eq⟩

private lemma externalCoveringNumber_dilation_eq {a : ℝ} (ha : 0 < a)
    {ε : NNReal} {A : Set ℝ} :
    externalCoveringNumber ⟨a * ε, by positivity⟩ ((fun x => a * x) '' A) =
    externalCoveringNumber ε A := by
  let f : ℝ → ℝ := fun x => a * x
  let g : ℝ → ℝ := fun y => y / a
  have h_a_nn : 0 ≤ a := by linarith
  have h_inv_nn : 0 ≤ 1 / a := by positivity
  have hf_lip : LipschitzWith (Real.toNNReal a) f := by
    apply LipschitzWith.of_dist_le'
    intro x y
    have h : |a * x - a * y| = a * |x - y| := by
      have h1 : a * x - a * y = a * (x - y) := by ring
      rw [h1, abs_mul, abs_of_pos ha]
    simpa [f, dist_eq_norm] using le_of_eq h
  have hg_lip : LipschitzWith (Real.toNNReal (1 / a)) g := by
    apply LipschitzWith.of_dist_le'
    intro x y
    have h : |x / a - y / a| = (1 / a) * |x - y| := by
      have h1 : x / a - y / a = (1 / a) * (x - y) := by ring
      rw [h1, abs_mul, abs_of_pos (show (0 : ℝ) < 1 / a by positivity)]
    simpa [g, dist_eq_norm] using le_of_eq h
  have hgf : ∀ x, g (f x) = x := by
    intro x
    have h : g (f x) = (a * x) / a := by simp [f, g]
    rw [h]; field_simp [ha.ne']
  have h_coe_a : (Real.toNNReal a : ℝ) = a := by
    have h3 : (Real.toNNReal a : ℝ) = max a 0 := by simp [Real.toNNReal]
    rw [h3, max_eq_left h_a_nn]
  have h_coe_inv : (Real.toNNReal (1 / a) : ℝ) = 1 / a := by
    have h3 : (Real.toNNReal (1 / a) : ℝ) = max (1 / a) 0 := by simp [Real.toNNReal]
    rw [h3, max_eq_left h_inv_nn]
  have h_radius1 : Real.toNNReal a * ε = ⟨a * ε, by positivity⟩ := by
    have h_main : ((Real.toNNReal a * ε : NNReal) : ℝ) = a * (ε : ℝ) := by
      rw [NNReal.coe_mul, h_coe_a]
    let target : NNReal := ⟨a * ε, by positivity⟩
    have h4 : (target : ℝ) = a * ε := Subtype.coe_mk (a * ε) (by positivity)
    have h5 : ((Real.toNNReal a * ε : NNReal) : ℝ) = (target : ℝ) := by rw [h_main, h4]
    exact NNReal.coe_injective h5
  have h_radius2 : Real.toNNReal (1 / a) * ⟨a * ε, by positivity⟩ = ε := by
    let target : NNReal := ⟨a * ε, by positivity⟩
    have h4 : (target : ℝ) = a * ε := Subtype.coe_mk (a * ε) (by positivity)
    have h_main : ((Real.toNNReal (1 / a) * target : NNReal) : ℝ) = (ε : ℝ) := by
      rw [NNReal.coe_mul, h_coe_inv, h4]; field_simp [ha.ne']
    exact NNReal.coe_injective h_main
  have h1 : externalCoveringNumber ⟨a * ε, by positivity⟩ (f '' A) ≤ externalCoveringNumber ε A := by
    simp only [externalCoveringNumber, le_iInf_iff]
    intro C hC
    have hcover : IsCover (Real.toNNReal a * ε) (f '' A) (f '' C) := hC.image_lipschitz hf_lip
    rw [h_radius1] at hcover
    exact iInf_le_of_le (f '' C) (iInf_le_of_le hcover (encard_image_le f C))
  have h2 : externalCoveringNumber ε A ≤ externalCoveringNumber ⟨a * ε, by positivity⟩ (f '' A) := by
    simp only [externalCoveringNumber, le_iInf_iff]
    intro C hC
    have hcover : IsCover (Real.toNNReal (1 / a) * ⟨a * ε, by positivity⟩) (g '' (f '' A)) (g '' C) :=
      hC.image_lipschitz hg_lip
    rw [h_radius2] at hcover
    have h_image : g '' (f '' A) = A := by
      ext y; simp only [Set.mem_image]
      constructor
      · rintro ⟨z, hz, rfl⟩; rcases hz with ⟨x, hx, rfl⟩; have h4 : g (f x) = x := hgf x; rw [h4]; exact hx
      · intro hy; refine ⟨f y, ⟨y, hy, rfl⟩, ?_⟩; exact hgf y
    rw [h_image] at hcover
    exact iInf_le_of_le (g '' C) (iInf_le_of_le hcover (encard_image_le g C))
  exact le_antisymm h1 h2

private lemma externalCoveringNumber_union_le {ε : NNReal} {A B : Set ℝ} :
    (↑(externalCoveringNumber ε (A ∪ B)) : ENNReal) ≤
    (↑(externalCoveringNumber ε A) : ENNReal) + (↑(externalCoveringNumber ε B) : ENNReal) := by
  by_cases hA : externalCoveringNumber ε A = ⊤
  · rw [hA]; simp
  · by_cases hB : externalCoveringNumber ε B = ⊤
    · rw [hB]; simp
    · rcases externalCoveringNumber_exists hA with ⟨CA, hCA, eCA⟩
      rcases externalCoveringNumber_exists hB with ⟨CB, hCB, eCB⟩
      have h_union_cover : IsCover ε (A ∪ B) (CA ∪ CB) := by
        intro x hx; rcases hx with (hxA | hxB)
        · rcases hCA hxA with ⟨c, hc, hdist⟩; exact ⟨c, Or.inl hc, hdist⟩
        · rcases hCB hxB with ⟨c, hc, hdist⟩; exact ⟨c, Or.inr hc, hdist⟩
      have h_le : externalCoveringNumber ε (A ∪ B) ≤ (CA ∪ CB).encard :=
        IsCover.externalCoveringNumber_le_encard h_union_cover
      have h_encard : (CA ∪ CB).encard ≤ CA.encard + CB.encard := Set.encard_union_le CA CB
      have h_main : (↑(externalCoveringNumber ε (A ∪ B)) : ENNReal) ≤
          (↑(CA.encard) : ENNReal) + (↑(CB.encard) : ENNReal) := by
        have h5 : (↑(externalCoveringNumber ε (A ∪ B)) : ENNReal) ≤ (↑((CA ∪ CB).encard) : ENNReal) := by exact_mod_cast h_le
        have h6 : (↑((CA ∪ CB).encard) : ENNReal) ≤ (↑(CA.encard) : ENNReal) + (↑(CB.encard) : ENNReal) := by exact_mod_cast h_encard
        exact h5.trans h6
      rw [eCA, eCB] at h_main; exact h_main

private lemma externalCoveringNumber_four_union_le
    {ε : NNReal} {A1 A2 A3 A4 : Set ℝ} :
    (↑(externalCoveringNumber ε (A1 ∪ A2 ∪ A3 ∪ A4)) : ENNReal) ≤
    (↑(externalCoveringNumber ε A1) : ENNReal) + (↑(externalCoveringNumber ε A2) : ENNReal) +
    (↑(externalCoveringNumber ε A3) : ENNReal) + (↑(externalCoveringNumber ε A4) : ENNReal) := by
  let B1 := A1 ∪ A2; let B2 := A3 ∪ A4
  have h4 : A1 ∪ A2 ∪ A3 ∪ A4 = B1 ∪ B2 := by ext z; simp [B1, B2]; tauto
  rw [h4]
  have h1 : (↑(externalCoveringNumber ε (B1 ∪ B2)) : ENNReal) ≤
      (↑(externalCoveringNumber ε B1) : ENNReal) + (↑(externalCoveringNumber ε B2) : ENNReal) :=
    externalCoveringNumber_union_le (ε := ε) (A := B1) (B := B2)
  have h2 : (↑(externalCoveringNumber ε B1) : ENNReal) ≤
      (↑(externalCoveringNumber ε A1) : ENNReal) + (↑(externalCoveringNumber ε A2) : ENNReal) := by
    simpa [B1] using externalCoveringNumber_union_le (ε := ε) (A := A1) (B := A2)
  have h3 : (↑(externalCoveringNumber ε B2) : ENNReal) ≤
      (↑(externalCoveringNumber ε A3) : ENNReal) + (↑(externalCoveringNumber ε A4) : ENNReal) := by
    simpa [B2] using externalCoveringNumber_union_le (ε := ε) (A := A3) (B := A4)
  calc
    _ ≤ (↑(externalCoveringNumber ε B1) : ENNReal) + (↑(externalCoveringNumber ε B2) : ENNReal) := h1
    _ ≤ (↑(externalCoveringNumber ε A1) : ENNReal) + (↑(externalCoveringNumber ε A2) : ENNReal) +
          (↑(externalCoveringNumber ε A3) : ENNReal) + (↑(externalCoveringNumber ε A4) : ENNReal) := by
      have h4 := add_le_add h2 h3
      simpa [add_assoc] using h4

private lemma icc_four_four_cover_by_four_balls :
    IsCover (1 : NNReal) (Set.Icc (-4 : ℝ) 4) ({-3, -1, 1, 3} : Set ℝ) := by
  intro x hx
  have h1 : -4 ≤ x := hx.1
  have h2 : x ≤ 4 := hx.2
  have h_main : ∃ (c : ℝ), c ∈ ({-3, -1, 1, 3} : Set ℝ) ∧ dist x c ≤ 1 := by
    by_cases h3 : x ≤ -2
    · refine ⟨-3, by simp, ?_⟩
      rw [Real.dist_eq, sub_eq_add_neg]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · by_cases h4 : x ≤ 0
      · refine ⟨-1, by simp, ?_⟩
        rw [Real.dist_eq, sub_eq_add_neg]
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · by_cases h5 : x ≤ 2
        · refine ⟨1, by simp, ?_⟩
          rw [Real.dist_eq]
          exact abs_le.mpr ⟨by linarith, by linarith⟩
        · refine ⟨3, by simp, ?_⟩
          rw [Real.dist_eq]
          exact abs_le.mpr ⟨by linarith, by linarith⟩
  rcases h_main with ⟨c, hc, hdist⟩
  have h_edist : edist x c ≤ ↑(1 : NNReal) := by
    rw [edist_dist]
    have h7 : ENNReal.ofReal (dist x c) ≤ ENNReal.ofReal (1 : ℝ) := ENNReal.ofReal_le_ofReal hdist
    have h8 : ENNReal.ofReal (1 : ℝ) = ↑(1 : NNReal) := by simp
    rw [h8] at h7
    exact h7
  exact ⟨c, hc, h_edist⟩

private lemma dilation_inter_closedBall
    {a : ℝ} (ha : 0 < a) {S : Set ℝ} {x r : ℝ} :
    (fun u : ℝ => a * u) '' (S ∩ Metric.closedBall x r) =
    ((fun u : ℝ => a * u) '' S) ∩ Metric.closedBall (a * x) (a * r) := by
  have h_inj : Function.Injective (fun u : ℝ => a * u) := by
    intro u v h; apply mul_left_cancel₀ ha.ne'; exact h
  have h1 : (fun u : ℝ => a * u) '' (S ∩ Metric.closedBall x r) =
      ((fun u : ℝ => a * u) '' S) ∩ ((fun u : ℝ => a * u) '' Metric.closedBall x r) := by
    rw [Set.image_inter h_inj]
  rw [h1]
  have h2 : (fun u : ℝ => a * u) '' Metric.closedBall x r = Metric.closedBall (a * x) (a * r) := by
    ext y; simp only [Set.mem_image, Metric.mem_closedBall]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h3 : dist z x ≤ r := hz
      have h4 : dist (a * z) (a * x) ≤ a * r := by
        have h5 : dist (a * z) (a * x) = a * dist z x := by
          rw [Real.dist_eq, Real.dist_eq]
          have h6 : |a * z - a * x| = a * |z - x| := by
            have h7 : a * z - a * x = a * (z - x) := by ring
            rw [h7, abs_mul, abs_of_pos ha]
          rw [h6]
        rw [h5]; exact mul_le_mul_of_nonneg_left h3 (by linarith)
      simpa [Metric.mem_closedBall] using h4
    · intro h3
      use y / a
      constructor
      · have h4 : dist (y / a) x ≤ r := by
          have h5 : dist (y / a) x = dist y (a * x) / a := by
            rw [Real.dist_eq, Real.dist_eq]
            have h6 : |y / a - x| = |y - a * x| / a := by
              have h7 : y / a - x = (y - a * x) / a := by field_simp [ha.ne']
              rw [h7, abs_div, abs_of_pos ha]
            rw [h6]
          rw [h5]
          have h6 : dist y (a * x) ≤ a * r := h3
          have h7 : dist y (a * x) / a ≤ r := by
            calc dist y (a * x) / a ≤ (a * r) / a := by gcongr
                 _ = r := by field_simp [ha.ne']
          exact h7
        simpa [Metric.mem_closedBall] using h4
      · field_simp [ha.ne']
  rw [h2]

private lemma dilation_image_closedBall {a : ℝ} (ha : 0 < a) {x r : ℝ} :
    (fun u : ℝ => a * u) '' Metric.closedBall x r = Metric.closedBall (a * x) (a * r) := by
  have h_surj : (fun u : ℝ => a * u) '' Set.univ = Set.univ := by
    ext y; simp; exact ⟨y / a, by field_simp [ha.ne']⟩
  have h_univ : (Set.univ ∩ Metric.closedBall x r) = Metric.closedBall x r := by simp
  have h := dilation_inter_closedBall (ha := ha) (S := Set.univ) (x := x) (r := r)
  rw [h_univ] at h
  rw [h, h_surj, Set.univ_inter]

private lemma realRpowENN_mono_base
    {x y : ℝ} {s : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hs : 0 ≤ s) :
    Kakeya.realRpowENN x s ≤ Kakeya.realRpowENN y s := by
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow hx hxy hs

private lemma realRpowENN_ge_one {x : ℝ} {s : ℝ} (hx : 1 ≤ x) (hs : 0 ≤ s) :
    (1 : ENNReal) ≤ Kakeya.realRpowENN x s := by
  have h1 : Real.rpow 1 s ≤ Real.rpow x s := Real.rpow_le_rpow (by norm_num) hx hs
  have h2 : Real.rpow 1 s = 1 := by simp
  have h3 : (1 : ℝ) ≤ Real.rpow x s := by linarith [h1, h2]
  have h4 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (Real.rpow x s) := ENNReal.ofReal_le_ofReal h3
  have h5 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
  rw [h5]
  exact h4

/--
Dilating a one-dimensional AD set by `M⁻²` transports its base scale from
`delta` to `delta / M²`, with one fixed covering constant.
-/
lemma IsADSet1.image_div_sq
    {S : Set ℝ} {delta sigma : ℝ} {C : ENNReal} {M : ℝ}
    (hM : 1 ≤ M) (hdelta : 0 < delta) (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hAD : IsADSet1 S delta (1 - sigma) C) :
    IsADSet1 ((fun u : ℝ => u / M^2) '' S) (delta / M^2) (1 - sigma) (10 * C) := by
  rcases hAD with ⟨hδ, hα, hα1, hC, hS_bounded, hcover⟩
  let a : ℝ := 1 / M^2
  have ha_pos : 0 < a := by positivity
  have hM2_pos : 0 < M^2 := by positivity
  let S' := (fun u : ℝ => u / M^2) '' S
  have hM2_ge_one : 1 ≤ M^2 := by nlinarith
  have hS'_bounded : S' ⊆ Set.Icc (-4 : ℝ) 4 := by
    intro y hy
    rcases hy with ⟨u, hu, rfl⟩
    have h1 : -4 ≤ u := (hS_bounded hu).1
    have h2 : u ≤ 4 := (hS_bounded hu).2
    have h_pos : 0 < M^2 := by positivity
    have h3 : -4 ≤ u / M^2 := by
      have h_ineq : -4 * M^2 ≤ u := by nlinarith
      have h_eq : (-4 * M^2) / M^2 = -4 := by
        field_simp [h_pos.ne']
      have h_goal : (-4 * M^2) / M^2 ≤ u / M^2 :=
        div_le_div_of_nonneg_right h_ineq (by positivity)
      rw [h_eq] at h_goal
      exact h_goal
    have h4 : u / M^2 ≤ 4 := by
      have h_ineq : u ≤ 4 * M^2 := by nlinarith
      have h_eq : (4 * M^2) / M^2 = 4 := by
        field_simp [h_pos.ne']
      have h_goal : u / M^2 ≤ (4 * M^2) / M^2 :=
        div_le_div_of_nonneg_right h_ineq (by positivity)
      rw [h_eq] at h_goal
      exact h_goal
    exact ⟨h3, h4⟩
  have h10C : (1 : ENNReal) ≤ 10 * C := by
    have h1 : (1 : ENNReal) ≤ C := hC
    have h2 : (1 : ENNReal) ≤ 10 := by norm_num
    have h3 : (1 : ENNReal) ≤ 10 * C := by
      calc (1 : ENNReal) = 1 * 1 := by simp
           _ ≤ 10 * C := by gcongr
    exact h3
  refine ⟨by positivity, hα, hα1, h10C, hS'_bounded, ?_⟩
  intro rho' hrho' hdelta' hrho'_one x' r' hrho'_r hr'_one
  set rho : ℝ := M^2 * rho' with hrho_def
  set r : ℝ := M^2 * r' with hr_def
  set x : ℝ := M^2 * x' with hx_def
  have h_rho_nonneg : 0 ≤ rho := by positivity
  have h_delta_rho : delta ≤ rho := by
    have h : delta / M^2 ≤ rho' := hdelta'
    have h2 : delta ≤ M^2 * rho' := by
      have h_eq : delta = (delta / M^2) * M^2 := by
        field_simp [hM2_pos.ne']
      rw [h_eq]
      have h3 : (delta / M^2) * M^2 ≤ rho' * M^2 := by gcongr
      have h4 : rho' * M^2 = M^2 * rho' := by ring
      rw [h4] at h3
      exact h3
    exact h2
  have h_rho_r : rho ≤ r := by
    rw [hrho_def, hr_def]; exact mul_le_mul_of_nonneg_left hrho'_r (by positivity)
  have h_a_eq : a = 1 / M^2 := by rfl
  have h_image_eq : S' ∩ Metric.closedBall x' r' =
      (fun u : ℝ => a * u) '' (S ∩ Metric.closedBall x r) := by
    have h_f : (fun u : ℝ => u / M^2) = (fun u : ℝ => a * u) := by
      funext u
      simp [a, h_a_eq]; field_simp [hM2_pos.ne']
    have h1 : S' = (fun u : ℝ => a * u) '' S := by
      rw [show S' = (fun u : ℝ => u / M^2) '' S from rfl, h_f]
    have h_ax : a * x = x' := by
      rw [hx_def]; simp [a]; field_simp [hM2_pos.ne']
    have h_ar : a * r = r' := by
      rw [hr_def]; simp [a]; field_simp [hM2_pos.ne']
    have h2 := dilation_inter_closedBall (ha := ha_pos) (S := S) (x := x) (r := r)
    rw [h_ax, h_ar] at h2
    rw [h1]
    exact h2.symm
  have h_cover_eq : externalCoveringNumber ⟨rho', hrho'⟩ (S' ∩ Metric.closedBall x' r') =
      externalCoveringNumber ⟨rho, h_rho_nonneg⟩ (S ∩ Metric.closedBall x r) := by
    rw [h_image_eq]
    let eps : NNReal := ⟨rho, h_rho_nonneg⟩
    have h_eps_coe : (eps : ℝ) = rho := by
      exact Subtype.coe_mk rho h_rho_nonneg
    have h_radius : a * (eps : ℝ) = rho' := by
      rw [h_eps_coe]
      dsimp only [a]
      have h : a * rho = rho' := by
        simp only [a, hrho_def]
        <;> field_simp [hM2_pos.ne']
      exact h
    let eps2 : NNReal := ⟨a * (eps : ℝ), by positivity⟩
    have h_nn : eps2 = ⟨rho', hrho'⟩ := by
      apply NNReal.coe_injective
      have h_coe2 : (eps2 : ℝ) = a * (eps : ℝ) := by
        exact Subtype.coe_mk (a * (eps : ℝ)) (by positivity)
      rw [h_coe2]
      exact h_radius
    have h_dilation : externalCoveringNumber eps2 ((fun u : ℝ => a * u) '' (S ∩ Metric.closedBall x r)) =
        externalCoveringNumber eps (S ∩ Metric.closedBall x r) := by
      exact externalCoveringNumber_dilation_eq (a := a) (ha := ha_pos) (ε := eps) (A := S ∩ Metric.closedBall x r)
    rw [h_nn] at h_dilation
    exact h_dilation
  have h_exp_pos : 0 ≤ 1 - sigma := by linarith
  by_cases h_r1 : r ≤ 1
  · -- Case 1: r ≤ 1
    rw [h_cover_eq]
    have h_rho1 : rho ≤ 1 := by linarith
    have h_old := hcover rho h_rho_nonneg h_delta_rho h_rho1 x r h_rho_r h_r1
    have h_ratio : r / rho = r' / rho' := by
      rw [hr_def, hrho_def]
      field_simp [hM2_pos.ne']
    rw [h_ratio] at h_old
    have h : C * Kakeya.realRpowENN (r' / rho') (1 - sigma) ≤
        (10 * C) * Kakeya.realRpowENN (r' / rho') (1 - sigma) := by
      have hC_le_10C : C ≤ 10 * C := by
        have h1 : (1 : ENNReal) ≤ 10 := by norm_num
        have h2 : (1 : ENNReal) * C ≤ 10 * C := mul_le_mul_left h1 C
        simpa using h2
      exact mul_le_mul_left hC_le_10C
        (Kakeya.realRpowENN (r' / rho') (1 - sigma))
    exact h_old.trans h
  · -- r > 1
    have h_r_gt_one : 1 < r := by linarith
    by_cases h_rho1 : rho ≤ 1
    · -- Case 2: r > 1, rho ≤ 1
      rw [h_cover_eq]
      let A1 := S ∩ Metric.closedBall (-3 : ℝ) 1
      let A2 := S ∩ Metric.closedBall (-1 : ℝ) 1
      let A3 := S ∩ Metric.closedBall (1 : ℝ) 1
      let A4 := S ∩ Metric.closedBall (3 : ℝ) 1
      have hS_cover : S ⊆ A1 ∪ A2 ∪ A3 ∪ A4 := by
        intro p hp
        have h_p_in_Icc : p ∈ Set.Icc (-4 : ℝ) 4 := hS_bounded hp
        rcases icc_four_four_cover_by_four_balls h_p_in_Icc with ⟨c, hc, hdist⟩
        have h_in_ball : p ∈ Metric.closedBall c 1 := by
          simpa [Metric.mem_closedBall, edist_dist] using hdist
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        rcases hc with (rfl | rfl | rfl | rfl)
        · have h_goal : p ∈ A1 := ⟨hp, h_in_ball⟩
          simp [A1, A2, A3, A4, h_goal]
        · have h_goal : p ∈ A2 := ⟨hp, h_in_ball⟩
          simp [A1, A2, A3, A4, h_goal]
        · have h_goal : p ∈ A3 := ⟨hp, h_in_ball⟩
          simp [A1, A2, A3, A4, h_goal]
        · have h_goal : p ∈ A4 := ⟨hp, h_in_ball⟩
          simp [A1, A2, A3, A4, h_goal]
      have h_sub : S ∩ Metric.closedBall x r ⊆ A1 ∪ A2 ∪ A3 ∪ A4 := by
        intro p hp; exact hS_cover hp.1
      have h_mono : externalCoveringNumber ⟨rho, h_rho_nonneg⟩ (S ∩ Metric.closedBall x r) ≤
          externalCoveringNumber ⟨rho, h_rho_nonneg⟩ (A1 ∪ A2 ∪ A3 ∪ A4) :=
        externalCoveringNumber_mono_set h_sub
      have h_union := externalCoveringNumber_four_union_le (ε := ⟨rho, h_rho_nonneg⟩) (A1 := A1) (A2 := A2) (A3 := A3) (A4 := A4)
      have h_old1 := hcover rho h_rho_nonneg h_delta_rho h_rho1 (-3) 1 (by linarith) (by norm_num)
      have h_old2 := hcover rho h_rho_nonneg h_delta_rho h_rho1 (-1) 1 (by linarith) (by norm_num)
      have h_old3 := hcover rho h_rho_nonneg h_delta_rho h_rho1 1 1 (by linarith) (by norm_num)
      have h_old4 := hcover rho h_rho_nonneg h_delta_rho h_rho1 3 1 (by linarith) (by norm_num)
      have h_sum : (↑(externalCoveringNumber ⟨rho, h_rho_nonneg⟩ (A1 ∪ A2 ∪ A3 ∪ A4)) : ENNReal) ≤
          4 * (C * Kakeya.realRpowENN (1 / rho) (1 - sigma)) := by
        calc
          _ ≤ _ + _ + _ + _ := h_union
          _ ≤ 4 * (C * Kakeya.realRpowENN (1 / rho) (1 - sigma)) := by
            let X := C * Kakeya.realRpowENN (1 / rho) (1 - sigma)
            have h1 : (↑(externalCoveringNumber ⟨rho, h_rho_nonneg⟩ A1) : ENNReal) ≤ X := h_old1
            have h2 : (↑(externalCoveringNumber ⟨rho, h_rho_nonneg⟩ A2) : ENNReal) ≤ X := h_old2
            have h3 : (↑(externalCoveringNumber ⟨rho, h_rho_nonneg⟩ A3) : ENNReal) ≤ X := h_old3
            have h4 : (↑(externalCoveringNumber ⟨rho, h_rho_nonneg⟩ A4) : ENNReal) ≤ X := h_old4
            calc
              _ ≤ X + X + X + X := by gcongr
              _ = (4 : ENNReal) * X := by
                have h21 : X + X = (2 : ENNReal) * X := by rw [two_mul]
                have h_assoc : X + X + X + X = (X + X) + (X + X) := by simp only [add_assoc]
                rw [h_assoc, h21]
                have h22 : (2 : ENNReal) * X + (2 : ENNReal) * X = ((2 : ENNReal) + (2 : ENNReal)) * X := by rw [add_mul]
                rw [h22]
                have h23 : (2 : ENNReal) + (2 : ENNReal) = (4 : ENNReal) := by norm_num
                rw [h23]
      have h_ratio : 1 / rho ≤ r' / rho' := by
        have h1 : 1 < r := h_r_gt_one
        have h2 : 1 / M^2 < r' := by
          have h3 : 1 < M^2 * r' := by simpa [hr_def] using h1
          calc 1 / M^2 = (1 : ℝ) / M^2 := by ring
               _ < (M^2 * r') / M^2 := by gcongr
               _ = r' := by field_simp [hM2_pos.ne']
        rw [hrho_def]
        calc 1 / (M^2 * rho') = (1 / M^2) / rho' := by field_simp [hM2_pos.ne']
             _ ≤ r' / rho' := by gcongr
      have h_rpow : Kakeya.realRpowENN (1 / rho) (1 - sigma) ≤
          Kakeya.realRpowENN (r' / rho') (1 - sigma) :=
        realRpowENN_mono_base (by positivity) h_ratio h_exp_pos
      have h_final : 4 * (C * Kakeya.realRpowENN (1 / rho) (1 - sigma)) ≤
          (10 * C) * Kakeya.realRpowENN (r' / rho') (1 - sigma) := by
        calc
          4 * (C * Kakeya.realRpowENN (1 / rho) (1 - sigma))
            ≤ 4 * (C * Kakeya.realRpowENN (r' / rho') (1 - sigma)) := by gcongr
          _ = (4 * C) * Kakeya.realRpowENN (r' / rho') (1 - sigma) := by simp [mul_assoc]
          _ ≤ (10 * C) * Kakeya.realRpowENN (r' / rho') (1 - sigma) := by
            let X := Kakeya.realRpowENN (r' / rho') (1 - sigma)
            have h5 : (4 : ENNReal) * C ≤ (10 : ENNReal) * C := by
              have h6 : (4 : ENNReal) ≤ 10 := by norm_num
              exact mul_le_mul_left h6 C
            have h9 : ((4 * C) * X) ≤ ((10 * C) * X) :=
              mul_le_mul_left h5 X
            exact h9
      have h_mono' : (↑(externalCoveringNumber ⟨rho, h_rho_nonneg⟩ (S ∩ Metric.closedBall x r)) : ENNReal) ≤
          (↑(externalCoveringNumber ⟨rho, h_rho_nonneg⟩ (A1 ∪ A2 ∪ A3 ∪ A4)) : ENNReal) := by
        exact_mod_cast h_mono
      exact h_mono'.trans (h_sum.trans h_final)
    · -- Case 3: rho > 1
      have h_rho_gt_one : 1 < rho := by linarith
      let B1 := (fun u : ℝ => a * u) '' Metric.closedBall (-3 : ℝ) 1
      let B2 := (fun u : ℝ => a * u) '' Metric.closedBall (-1 : ℝ) 1
      let B3 := (fun u : ℝ => a * u) '' Metric.closedBall (1 : ℝ) 1
      let B4 := (fun u : ℝ => a * u) '' Metric.closedBall (3 : ℝ) 1
      have hS'_cover : S' ⊆ B1 ∪ B2 ∪ B3 ∪ B4 := by
        intro y hy
        rcases hy with ⟨u, hu, hy_eq⟩
        have h_p_in_Icc : u ∈ Set.Icc (-4 : ℝ) 4 := hS_bounded hu
        rcases icc_four_four_cover_by_four_balls h_p_in_Icc with ⟨c, hc, hdist⟩
        have h_in_ball : u ∈ Metric.closedBall c 1 := by
          simpa [Metric.mem_closedBall, edist_dist] using hdist
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        have h_au_eq_y : a * u = y := by
          have h1 : u / M^2 = y := hy_eq
          have h2 : a * u = u / M^2 := by
            simp [a]; field_simp [hM2_pos.ne']
          linarith
        rcases hc with (rfl | rfl | rfl | rfl)
        · have h_goal : y ∈ B1 := ⟨u, h_in_ball, h_au_eq_y⟩
          simp [B1, B2, B3, B4, h_goal]
        · have h_goal : y ∈ B2 := ⟨u, h_in_ball, h_au_eq_y⟩
          simp [B1, B2, B3, B4, h_goal]
        · have h_goal : y ∈ B3 := ⟨u, h_in_ball, h_au_eq_y⟩
          simp [B1, B2, B3, B4, h_goal]
        · have h_goal : y ∈ B4 := ⟨u, h_in_ball, h_au_eq_y⟩
          simp [B1, B2, B3, B4, h_goal]
      have h_sub : S' ∩ Metric.closedBall x' r' ⊆ B1 ∪ B2 ∪ B3 ∪ B4 := by
        intro p hp; exact hS'_cover hp.1
      have h_B1 : B1 = Metric.closedBall (a * (-3)) a := by
        have h := dilation_image_closedBall (a := a) (ha := ha_pos) (x := -3) (r := 1)
        simpa [mul_one] using h
      have h_B2 : B2 = Metric.closedBall (a * (-1)) a := by
        have h := dilation_image_closedBall (a := a) (ha := ha_pos) (x := -1) (r := 1)
        simpa [mul_one] using h
      have h_B3 : B3 = Metric.closedBall (a * 1) a := by
        have h := dilation_image_closedBall (a := a) (ha := ha_pos) (x := 1) (r := 1)
        simpa [mul_one] using h
      have h_B4 : B4 = Metric.closedBall (a * 3) a := by
        have h := dilation_image_closedBall (a := a) (ha := ha_pos) (x := 3) (r := 1)
        simpa [mul_one] using h
      have h_a_lt_rho' : a < rho' := by
        have h1 : 1 < rho := h_rho_gt_one
        have h2 : 1 / M^2 < rho' := by
          have h3 : 1 < M^2 * rho' := by simpa [hrho_def] using h1
          calc 1 / M^2 = (1 : ℝ) / M^2 := by ring
               _ < (M^2 * rho') / M^2 := by gcongr
               _ = rho' := by field_simp [hM2_pos.ne']
        simpa [a] using h2
      let eps' : NNReal := ⟨rho', hrho'⟩
      have h_cover4 : externalCoveringNumber eps' (B1 ∪ B2 ∪ B3 ∪ B4) ≤ 4 := by
        rw [h_B1, h_B2, h_B3, h_B4]
        have h_a_le_rho' : a ≤ rho' := by linarith
        have h_coe : (eps' : ENNReal) = ENNReal.ofReal rho' := by
          have h1 : (eps' : ℝ) = rho' := Subtype.coe_mk rho' hrho'
          have h2 : (eps' : ENNReal) = ENNReal.ofReal (eps' : ℝ) :=
            ENNReal.coe_nnreal_eq eps'
          rw [h2, h1]
        have h_center_cover : ∀ (c : ℝ) (y : ℝ), y ∈ Metric.closedBall (a * c) a →
            edist y (a * c) ≤ (eps' : ENNReal) := by
          intro c y hyc
          have h_dist : dist y (a * c) ≤ a := by simpa [Metric.mem_closedBall] using hyc
          have h_edist : edist y (a * c) = ENNReal.ofReal (dist y (a * c)) :=
            edist_dist y (a * c)
          rw [h_edist, h_coe]
          exact ENNReal.ofReal_le_ofReal (h_dist.trans h_a_le_rho')
        have h5 : IsCover eps' (Metric.closedBall (a * (-3)) a ∪ Metric.closedBall (a * (-1)) a ∪
            Metric.closedBall (a * 1) a ∪ Metric.closedBall (a * 3) a)
            ({a * (-3), a * (-1), a * 1, a * 3} : Set ℝ) := by
          intro y hy
          simp only [Set.mem_union] at hy
          have h_union : y ∈ Metric.closedBall (a * (-3)) a ∨ y ∈ Metric.closedBall (a * (-1)) a ∨
              y ∈ Metric.closedBall (a * 1) a ∨ y ∈ Metric.closedBall (a * 3) a := by tauto
          rcases h_union with (h | h | h | h)
          · exact ⟨a * (-3), by simp, h_center_cover (-3) y h⟩
          · exact ⟨a * (-1), by simp, h_center_cover (-1) y h⟩
          · exact ⟨a * 1, by simp, h_center_cover 1 y h⟩
          · exact ⟨a * 3, by simp, h_center_cover 3 y h⟩
        have h6 : externalCoveringNumber eps' _ ≤
            ({a * (-3), a * (-1), a * 1, a * 3} : Set ℝ).encard :=
          IsCover.externalCoveringNumber_le_encard h5
        have h7 : ({a * (-3), a * (-1), a * 1, a * 3} : Set ℝ).encard ≤ 4 := by
          let s : Finset ℝ := {a * (-3), a * (-1), a * 1, a * 3}
          have h9 : (s : Set ℝ) = ({a * (-3), a * (-1), a * 1, a * 3} : Set ℝ) := by simp [s]
          rw [←h9]
          have h10 : (s : Set ℝ).encard = ↑s.card := Set.encard_coe_eq_coe_finsetCard s
          rw [h10]
          have h11 : s.card ≤ 4 := by
            dsimp only [s]
            exact Finset.card_le_four
          have h13 : (↑s.card : ENat) ≤ 4 := by exact_mod_cast h11
          exact h13
        exact h6.trans h7
      have h_mono : externalCoveringNumber ⟨rho', hrho'⟩ (S' ∩ Metric.closedBall x' r') ≤
          externalCoveringNumber ⟨rho', hrho'⟩ (B1 ∪ B2 ∪ B3 ∪ B4) :=
        externalCoveringNumber_mono_set h_sub
      have h_final : (4 : ENNReal) ≤ (10 * C) * Kakeya.realRpowENN (r' / rho') (1 - sigma) := by
        have h1 : 1 ≤ r' / rho' := by
          have h_rho'_pos : 0 < rho' := by
            have h_pos2 : 0 < delta / M^2 := by positivity
            linarith [hdelta']
          calc 1 = rho' / rho' := by field_simp [h_rho'_pos.ne']
               _ ≤ r' / rho' := by gcongr
        have h2 : (1 : ENNReal) ≤ Kakeya.realRpowENN (r' / rho') (1 - sigma) :=
          realRpowENN_ge_one h1 h_exp_pos
        have h3 : (4 : ENNReal) ≤ 10 * C := by
          have h4 : (1 : ENNReal) ≤ C := hC
          have h5 : (10 : ENNReal) ≤ 10 * C := by
            have h6 : (10 : ENNReal) = 10 * (1 : ENNReal) := by simp
            rw [h6]
            exact le_mul_of_one_le_right' hC
          have h7 : (4 : ENNReal) ≤ 10 := by norm_num
          exact h7.trans h5
        calc (4 : ENNReal) ≤ 10 * C := h3
             _ ≤ (10 * C) * Kakeya.realRpowENN (r' / rho') (1 - sigma) := by
              have h10 : (1 : ENNReal) ≤ Kakeya.realRpowENN (r' / rho') (1 - sigma) := h2
              have h11 : (10 * C) * (1 : ENNReal) ≤
                  (10 * C) * Kakeya.realRpowENN (r' / rho') (1 - sigma) :=
                mul_le_mul_right h10 (10 * C)
              simpa using h11
      have h_mono' : (↑(externalCoveringNumber ⟨rho', hrho'⟩ (S' ∩ Metric.closedBall x' r')) : ENNReal) ≤
          (↑(externalCoveringNumber ⟨rho', hrho'⟩ (B1 ∪ B2 ∪ B3 ∪ B4)) : ENNReal) := by
        exact_mod_cast h_mono
      have h_cover4' : (↑(externalCoveringNumber ⟨rho', hrho'⟩ (B1 ∪ B2 ∪ B3 ∪ B4)) : ENNReal) ≤ (4 : ENNReal) := by
        exact_mod_cast h_cover4
      exact h_mono'.trans (h_cover4'.trans h_final)

-- ===== Main theorem =====

theorem wz1_vertical_rescaling_ad : WZ1VerticalRescalingADStatement := by
  intro g c h M delta sigma C hh hh1 hM hdelta hsigma_pos hsigma_lt_one h_window h_bounds E hAD
  let gNew := wz1VerticalRescaledSlope g c h M
  have hM_pos : 0 < M := by linarith
  -- Part 1: gNew.IsNormalized
  have h_norm : gNew.IsNormalized := by
    intro t ht
    have hz : c + h * t ∈ Set.Icc (-1 : ℝ) 1 := h_window t ht
    have hbounds := h_bounds (c + h * t) hz
    rcases hbounds with ⟨h1, h2, h3⟩
    have h_abs1 : |gNew t| ≤ 1 := by
      have h : |g (c + h * t) / M| ≤ 1 := by
        calc
          |g (c + h * t) / M| = |g (c + h * t)| / |M| := by
            rw [abs_div]
          _ ≤ M / |M| := by gcongr
          _ = 1 := by
            have hM' : |M| = M := abs_of_pos hM_pos
            rw [hM']; field_simp [hM_pos.ne']
      simpa [gNew, wz1VerticalRescaledSlope] using h
    have h_deriv1 : deriv gNew t = h * deriv g (c + h * t) / M :=
      deriv_rescaled_slope g c h M t
    have h_abs2 : |deriv gNew t| ≤ 1 := by
      rw [h_deriv1]
      have h_h_abs : |h| ≤ 1 := by
        rw [abs_of_pos hh]; linarith
      calc
        |h * deriv g (c + h * t) / M|
          = |h * deriv g (c + h * t)| / |M| := by rw [abs_div]
        _ = |h| * |deriv g (c + h * t)| / |M| := by rw [abs_mul]
        _ ≤ 1 * M / |M| := by
          gcongr
        _ = 1 := by
          have hM' : |M| = M := abs_of_pos hM_pos
          rw [hM']; field_simp [hM_pos.ne']
    have h_deriv2 : deriv (deriv gNew) t = h^2 * deriv (deriv g) (c + h * t) / M :=
      second_deriv_rescaled_slope g c h M t
    have h_abs3 : |deriv (deriv gNew) t| ≤ 1 := by
      rw [h_deriv2]
      have h_h_abs : |h| ≤ 1 := by
        rw [abs_of_pos hh]; linarith
      have h_h2_abs : |h^2| ≤ 1 := by
        calc
          |h^2| = |h|^2 := by rw [abs_pow]
          _ ≤ 1^2 := by gcongr
          _ = 1 := by norm_num
      calc
        |h^2 * deriv (deriv g) (c + h * t) / M|
          = |h^2 * deriv (deriv g) (c + h * t)| / |M| := by rw [abs_div]
        _ = |h^2| * |deriv (deriv g) (c + h * t)| / |M| := by rw [abs_mul]
        _ ≤ 1 * M / |M| := by
          gcongr
        _ = 1 := by
          have hM' : |M| = M := abs_of_pos hM_pos
          rw [hM']; field_simp [hM_pos.ne']
    exact ⟨h_abs1, h_abs2, h_abs3⟩
  -- Part 2: scalar projection set equality
  have h_set_eq : ∀ (t : ℝ),
      scalarProjection (globalGrainDirection (gNew t))
          (horizontalSlice (wz1VerticalRescalingMap c h M '' E) t) =
      (fun u : ℝ => u / M^2) ''
        scalarProjection (globalGrainDirection (g (c + h * t)))
          (horizontalSlice E (c + h * t)) := by
    intro t
    exact scalar_projection_equality g c h M hh E t
  -- Part 3: transported AD set
  have h_AD_new : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (gNew t))
          (horizontalSlice (wz1VerticalRescalingMap c h M '' E) t))
        (delta / M^2) (1 - sigma) (10 * C) := by
    intro t ht
    let z := c + h * t
    let S := scalarProjection (globalGrainDirection (g z)) (horizontalSlice E z)
    have hz : z ∈ Set.Icc (-1 : ℝ) 1 := h_window t ht
    have h_old : IsADSet1 S delta (1 - sigma) C := hAD z hz
    have h_eq : scalarProjection (globalGrainDirection (gNew t))
          (horizontalSlice (wz1VerticalRescalingMap c h M '' E) t) =
        (fun u : ℝ => u / M^2) '' S := h_set_eq t
    rw [h_eq]
    exact h_old.image_div_sq hM hdelta hsigma_pos hsigma_lt_one
  exact ⟨h_norm, h_set_eq, h_AD_new⟩

end Kakeya.Assouad
