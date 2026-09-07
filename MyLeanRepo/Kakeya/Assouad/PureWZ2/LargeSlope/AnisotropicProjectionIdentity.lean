import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Anisotropic rescaling projection identity

Core geometric lemma for Node 6 global_ad transfer.

For p with p 2 = z and t = 2*(z-c)/(d-c) - 1:
  inner (Φ p) (globalGrainDirection (f t))
  = inner p (globalGrainDirection (g z))
-/

noncomputable section

namespace Kakeya.Assouad

variable (g : SlopeFunction) (c d m : ℝ)

/-- Translate the values of a smooth slope by a constant.  This changes no
derivative and is the internal witness needed when the affine shear is not
centered at the source midpoint. -/
def SlopeFunction.addConstant (slope : SlopeFunction) (offset : ℝ) :
    SlopeFunction where
  toFun t := slope t + offset
  contDiff := slope.contDiff.add contDiff_const

@[simp] theorem SlopeFunction.addConstant_apply
    (slope : SlopeFunction) (offset t : ℝ) :
    slope.addConstant offset t = slope t + offset := rfl

@[simp] theorem SlopeFunction.deriv_addConstant
    (slope : SlopeFunction) (offset t : ℝ) :
    deriv (slope.addConstant offset) t = deriv slope t := by
  change deriv (fun x => slope x + offset) t = deriv slope t
  simpa only [sub_neg_eq_add] using
    (deriv_sub_const (f := fun x : ℝ => slope x) (x := t) (-offset))

@[simp] theorem SlopeFunction.deriv_deriv_addConstant
    (slope : SlopeFunction) (offset t : ℝ) :
    deriv (deriv (slope.addConstant offset)) t =
      deriv (deriv slope) t := by
  congr 1
  funext x
  exact slope.deriv_addConstant offset x

/-- Constant value translation preserves the nonsingular derivative bounds. -/
theorem SlopeFunction.addConstant_isNonsingular
    {slope : SlopeFunction} (hslope : slope.IsNonsingular) (offset : ℝ) :
    (slope.addConstant offset).IsNonsingular := by
  intro t ht
  simpa using hslope t ht

/-- Rescale the source slope after an arbitrary horizontal shear.  The
centered formula is the special case in which `shearSlope` is the source
slope at the selected midpoint. -/
def anisotropicRescaledSlopeWithShear
    (sourceSlope : ℝ → ℝ) (c d m shearSlope t : ℝ) : ℝ :=
  sourceSlope (c + (d - c) / 2 * (t + 1)) / (m * (d - c) / 2) -
    shearSlope / (m * (d - c) / 2)

/-- The rescaled slope formula. -/
def anisotropicRescaledSlope (g : ℝ → ℝ) (c d m t : ℝ) : ℝ :=
  g (c + (d - c) / 2 * (t + 1)) / (m * (d - c) / 2)
  - g (c + (d - c) / 2) / (m * (d - c) / 2)

/-- First derivative of the exact anisotropically transported slope. -/
theorem anisotropicRescaledSlope_deriv
    (g : SlopeFunction) {c d m : ℝ} (hcd : c < d) (hm : 0 < m)
    (t : ℝ) :
    deriv (fun s => anisotropicRescaledSlope g c d m s) t =
      deriv g (c + (d - c) / 2 * (t + 1)) / m := by
  let phi : ℝ → ℝ := fun s => c + (d - c) / 2 * (s + 1)
  have hphiAlt : phi = fun s : ℝ =>
      (c + (d - c) / 2) + ((d - c) / 2) * s := by
    funext s
    dsimp only [phi]
    ring
  have hphi : HasDerivAt phi ((d - c) / 2) t := by
    rw [hphiAlt]
    exact (hasDerivAt_const_mul ((d - c) / 2)).const_add
      (c + (d - c) / 2)
  have hg : DifferentiableAt ℝ g (phi t) :=
    (g.contDiff.differentiable (by norm_num)).differentiableAt
  have hdenom : m * (d - c) / 2 ≠ 0 := by positivity
  have hmain := ((hg.hasDerivAt.comp t hphi).div_const
    (m * (d - c) / 2)).sub_const
      (g (c + (d - c) / 2) / (m * (d - c) / 2))
  change deriv (fun s =>
      g (c + (d - c) / 2 * (s + 1)) / (m * (d - c) / 2) -
        g (c + (d - c) / 2) / (m * (d - c) / 2)) t = _
  have hvalue : deriv (fun s =>
      g (c + (d - c) / 2 * (s + 1)) / (m * (d - c) / 2) -
        g (c + (d - c) / 2) / (m * (d - c) / 2)) t =
      deriv g (phi t) * ((d - c) / 2) /
        (m * (d - c) / 2) := by
    simpa only [Function.comp_def, phi] using hmain.deriv
  rw [hvalue]
  dsimp only [phi]
  field_simp [hdenom, hm.ne', sub_ne_zero.mpr hcd.ne']

/-- Second derivative of the exact anisotropically transported slope. -/
theorem anisotropicRescaledSlope_second_deriv
    (g : SlopeFunction) {c d m : ℝ} (hcd : c < d) (hm : 0 < m)
    (t : ℝ) :
    deriv (deriv (fun s => anisotropicRescaledSlope g c d m s)) t =
      deriv (deriv g) (c + (d - c) / 2 * (t + 1)) *
        (d - c) / (2 * m) := by
  have hfirst : deriv (fun s => anisotropicRescaledSlope g c d m s) =
      fun s => deriv g (c + (d - c) / 2 * (s + 1)) / m := by
    funext s
    exact anisotropicRescaledSlope_deriv g hcd hm s
  rw [hfirst]
  let phi : ℝ → ℝ := fun s => c + (d - c) / 2 * (s + 1)
  have hphiAlt : phi = fun s : ℝ =>
      (c + (d - c) / 2) + ((d - c) / 2) * s := by
    funext s
    dsimp only [phi]
    ring
  have hphi : HasDerivAt phi ((d - c) / 2) t := by
    rw [hphiAlt]
    exact (hasDerivAt_const_mul ((d - c) / 2)).const_add
      (c + (d - c) / 2)
  have hg : DifferentiableAt ℝ (deriv g) (phi t) :=
    (g.contDiff.deriv').differentiable_one.differentiableAt
  have hmain := (hg.hasDerivAt.comp t hphi).div_const m
  change deriv (fun s =>
      deriv g (c + (d - c) / 2 * (s + 1)) / m) t = _
  have hvalue : deriv (fun s =>
      deriv g (c + (d - c) / 2 * (s + 1)) / m) t =
      deriv (deriv g) (phi t) * ((d - c) / 2) / m := by
    simpa only [Function.comp_def, phi] using hmain.deriv
  rw [hvalue]
  dsimp only [phi]
  field_simp [hm.ne']

theorem anisotropicRescaledSlope_eq_withShear
    (sourceSlope : ℝ → ℝ) (c d m t : ℝ) :
    anisotropicRescaledSlope sourceSlope c d m t =
      anisotropicRescaledSlopeWithShear sourceSlope c d m
        (sourceSlope (c + (d - c) / 2)) t := rfl

private lemma point3_coord (x y z : ℝ) :
    (point3 x y z) 0 = x ∧ (point3 x y z) 1 = y ∧ (point3 x y z) 2 = z := by
  simp [point3] <;> aesop

private lemma inner_globalGrain (p : Point3) (m : ℝ) :
    inner ℝ p (globalGrainDirection m) = p 0 + m * p 1 := by
  simp [globalGrainDirection, point3, Fin.sum_univ_succ, inner] <;> ring

/-- Pointwise projection identity. -/
lemma anisotropic_projection_pointwise
    (hcd : c < d) (hm : 0 < m) (t : ℝ) (p : Point3)
    (hz : p 2 = c + (d - c) / 2 * (t + 1)) :
    inner ℝ (anisotropicRescalingMap g c d m p)
      (globalGrainDirection (anisotropicRescaledSlope g c d m t)) =
    inner ℝ p (globalGrainDirection (g (p 2))) := by
  set z : ℝ := p 2 with hz_def
  set hh : ℝ := d - c with hh_def
  set center : ℝ := c + hh / 2 with center_def
  have h_h_pos : 0 < hh := by linarith
  have h_pos : 0 < m * hh / 2 := by positivity
  have hz' : z = c + hh / 2 * (t + 1) := by
    simpa [hz_def, hh_def] using hz
  set f_t : ℝ := anisotropicRescaledSlope g c d m t with hf_t_def
  have h_arg1 : c + hh / 2 * (t + 1) = z := hz'.symm
  have h_arg2 : c + hh / 2 = center := by simp [center_def]
  have h_f_formula : f_t * (m * hh / 2) = g z - g center := by
    have h_expand : f_t =
        (g (c + hh / 2 * (t + 1)) - g center) / (m * hh / 2) := by
      simp only [hf_t_def, anisotropicRescaledSlope, hh_def, center_def]
      <;> ring_nf
    rw [h_expand, h_arg1]
    field_simp [h_pos.ne'] <;> ring
  let q := anisotropicRescalingMap g c d m p
  have hq0 : q 0 = p 0 + g center * p 1 := by
    have h : q 0 = p 0 + g (c + (d - c) / 2) * p 1 := by
      simp [q, anisotropicRescalingMap, point3_coord] <;> ring
    exact h
  have hq1 : q 1 = (m * hh / 2) * p 1 := by
    have h : q 1 = m * (d - c) / 2 * p 1 := by
      simp [q, anisotropicRescalingMap, point3_coord] <;> ring
    exact h
  have h_main : inner ℝ q (globalGrainDirection f_t) = q 0 + f_t * q 1 :=
    inner_globalGrain q f_t
  have h5 : f_t * q 1 = (g z - g center) * p 1 := by
    rw [hq1]
    have h6 : f_t * ((m * hh / 2) * p 1) = (f_t * (m * hh / 2)) * p 1 := by ring
    rw [h6, h_f_formula] <;> ring
  have h_goal : q 0 + f_t * q 1 = p 0 + g z * p 1 := by
    rw [hq0, h5] <;> ring
  have h6 : inner ℝ p (globalGrainDirection (g z)) = p 0 + g z * p 1 :=
    inner_globalGrain p (g z)
  calc
    inner ℝ q (globalGrainDirection f_t)
      = q 0 + f_t * q 1 := h_main
    _ = p 0 + g z * p 1 := h_goal
    _ = inner ℝ p (globalGrainDirection (g z)) := h6.symm

/-- Projection covariance when the affine map uses a global geometric
representative while the transported slope is only an ordinary function.
Only their values at the selected midpoint must agree. -/
lemma anisotropic_projection_pointwise_of_midpoint_eq
    (geometrySlope : SlopeFunction) (sourceSlope : ℝ → ℝ)
    (hmidpoint : geometrySlope (c + (d - c) / 2) =
      sourceSlope (c + (d - c) / 2))
    (hcd : c < d) (hm : 0 < m) (t : ℝ) (p : Point3)
    (hz : p 2 = c + (d - c) / 2 * (t + 1)) :
    inner ℝ (anisotropicRescalingMap geometrySlope c d m p)
      (globalGrainDirection (anisotropicRescaledSlope sourceSlope c d m t)) =
    inner ℝ p (globalGrainDirection (sourceSlope (p 2))) := by
  set z : ℝ := p 2
  set center : ℝ := c + (d - c) / 2
  set scale : ℝ := m * (d - c) / 2
  have hscale : 0 < scale := by
    dsimp only [scale]
    positivity
  have hz' : c + (d - c) / 2 * (t + 1) = z := by
    simpa [z] using hz.symm
  have hcenter' : c + (d - c) / 2 = center := rfl
  have hslope : anisotropicRescaledSlope sourceSlope c d m t * scale =
      sourceSlope z - sourceSlope center := by
    simp only [anisotropicRescaledSlope, hz', hcenter']
    change (sourceSlope z / scale - sourceSlope center / scale) * scale = _
    field_simp [hscale.ne']
  have hmapZero : (anisotropicRescalingMap geometrySlope c d m p) 0 =
      p 0 + sourceSlope center * p 1 := by
    unfold anisotropicRescalingMap
    rw [(point3_coord _ _ _).1]
    rw [hcenter', hmidpoint]
  have hmapOne : (anisotropicRescalingMap geometrySlope c d m p) 1 =
      scale * p 1 := by
    unfold anisotropicRescalingMap
    rw [(point3_coord _ _ _).2.1]
  rw [show inner ℝ (anisotropicRescalingMap geometrySlope c d m p)
        (globalGrainDirection
          (anisotropicRescaledSlope sourceSlope c d m t)) =
      (anisotropicRescalingMap geometrySlope c d m p) 0 +
        anisotropicRescaledSlope sourceSlope c d m t *
          (anisotropicRescalingMap geometrySlope c d m p) 1 by
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]]
  rw [hmapZero, hmapOne, show sourceSlope (p 2) = sourceSlope z by rfl]
  rw [show anisotropicRescaledSlope sourceSlope c d m t * (scale * p 1) =
      (anisotropicRescaledSlope sourceSlope c d m t * scale) * p 1 by ring,
    hslope]
  simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

/-- Projection covariance for an arbitrary horizontal shear.  The target
slope is allowed a nonzero intercept; only its first and second derivatives
enter the Proposition-6.5 nonsingularity condition. -/
lemma anisotropic_projection_pointwise_withShear
    (geometrySlope : SlopeFunction) (sourceSlope : ℝ → ℝ)
    (hcd : c < d) (hm : 0 < m) (t : ℝ) (p : Point3)
    (hz : p 2 = c + (d - c) / 2 * (t + 1)) :
    inner ℝ (anisotropicRescalingMap geometrySlope c d m p)
      (globalGrainDirection
        (anisotropicRescaledSlopeWithShear sourceSlope c d m
          (geometrySlope (c + (d - c) / 2)) t)) =
    inner ℝ p (globalGrainDirection (sourceSlope (p 2))) := by
  set z : ℝ := p 2
  set center : ℝ := c + (d - c) / 2
  set scale : ℝ := m * (d - c) / 2
  have hscale : 0 < scale := by
    dsimp only [scale]
    positivity
  have hz' : c + (d - c) / 2 * (t + 1) = z := by
    simpa [z] using hz.symm
  have hcenter' : c + (d - c) / 2 = center := rfl
  have hslope :
      anisotropicRescaledSlopeWithShear sourceSlope c d m
          (geometrySlope center) t * scale =
        sourceSlope z - geometrySlope center := by
    simp only [anisotropicRescaledSlopeWithShear, hz', hcenter']
    change (sourceSlope z / scale - geometrySlope center / scale) * scale = _
    field_simp [hscale.ne']
  have hmapZero : (anisotropicRescalingMap geometrySlope c d m p) 0 =
      p 0 + geometrySlope center * p 1 := by
    unfold anisotropicRescalingMap
    rw [(point3_coord _ _ _).1]
  have hmapOne : (anisotropicRescalingMap geometrySlope c d m p) 1 =
      scale * p 1 := by
    unfold anisotropicRescalingMap
    rw [(point3_coord _ _ _).2.1]
  rw [show inner ℝ (anisotropicRescalingMap geometrySlope c d m p)
        (globalGrainDirection
          (anisotropicRescaledSlopeWithShear sourceSlope c d m
            (geometrySlope center) t)) =
      (anisotropicRescalingMap geometrySlope c d m p) 0 +
        anisotropicRescaledSlopeWithShear sourceSlope c d m
            (geometrySlope center) t *
          (anisotropicRescalingMap geometrySlope c d m p) 1 by
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]]
  rw [hmapZero, hmapOne, show sourceSlope (p 2) = sourceSlope z by rfl]
  rw [show anisotropicRescaledSlopeWithShear sourceSlope c d m
          (geometrySlope center) t * (scale * p 1) =
      (anisotropicRescaledSlopeWithShear sourceSlope c d m
          (geometrySlope center) t * scale) * p 1 by ring, hslope]
  simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

/-- Helper: z-coordinate relation. -/
private lemma z_rel (hcd : c < d) (t : ℝ) (p : Point3) :
    (anisotropicRescalingMap g c d m p) 2 = t ↔
    p 2 = c + (d - c) / 2 * (t + 1) := by
  set hh : ℝ := d - c with hh_def
  have h_h_pos : 0 < hh := by linarith
  have h1 : (anisotropicRescalingMap g c d m p) 2 = 2 * (p 2 - c) / hh - 1 := by
    simp [anisotropicRescalingMap, point3_coord] <;> ring
  rw [h1]
  constructor
  · intro h_eq
    have h' : p 2 = c + hh / 2 * (t + 1) := by
      have h_eq2 : 2 * (p 2 - c) / hh - 1 = t := h_eq
      field_simp [h_h_pos.ne'] at h_eq2 ⊢ <;> linarith
    simpa [hh_def] using h'
  · intro h_eq
    rw [h_eq]
    field_simp [h_h_pos.ne'] <;> ring

/-- Set-level projection identity for horizontal slices. -/
lemma anisotropic_projection_set
    (hcd : c < d) (hm : 0 < m) (E : Set Point3) (t : ℝ) :
    scalarProjection (globalGrainDirection (anisotropicRescaledSlope g c d m t))
      (horizontalSlice (anisotropicRescalingMap g c d m '' E) t) =
    scalarProjection (globalGrainDirection (g (c + (d - c) / 2 * (t + 1))))
      (horizontalSlice E (c + (d - c) / 2 * (t + 1))) := by
  set z : ℝ := c + (d - c) / 2 * (t + 1) with hz_def
  set hh : ℝ := d - c with hh_def
  set Φ : Point3 → Point3 := anisotropicRescalingMap g c d m with Φ_def
  set v : Point3 := globalGrainDirection (anisotropicRescaledSlope g c d m t) with v_def
  set w : Point3 := globalGrainDirection (g z) with w_def
  let S : Set Point3 := {p | p ∈ E ∧ p 2 = z}
  have h_z_rel : ∀ p : Point3, (Φ p) 2 = t ↔ p 2 = z :=
    fun p => z_rel g c d m hcd t p
  have h_slice_image : horizontalSlice (Φ '' E) t = Φ '' S := by
    ext q
    simp only [horizontalSlice, S, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hqin, hq2⟩
      rcases hqin with ⟨p, hpE, hq_eq⟩
      have hp2 : p 2 = z := (h_z_rel p).mp (by rw [hq_eq] <;> exact hq2)
      exact ⟨p, ⟨hpE, hp2⟩, hq_eq⟩
    · rintro ⟨p, ⟨hpE, hp2⟩, hq_eq⟩
      have hq2 : (Φ p) 2 = t := (h_z_rel p).mpr hp2
      have hq3 : q 2 = t := by
        rw [←hq_eq]
        exact hq2
      exact ⟨⟨p, hpE, hq_eq⟩, hq3⟩
  have h_pointwise : ∀ p ∈ S, inner ℝ (Φ p) v = inner ℝ p w := by
    intro p hp
    have hp2 : p 2 = z := hp.2
    have h := anisotropic_projection_pointwise g c d m hcd hm t p hp2
    have h9 : g (p 2) = g z := by rw [hp2]
    have h10 : inner ℝ (Φ p) v = inner ℝ (anisotropicRescalingMap g c d m p) (globalGrainDirection (anisotropicRescaledSlope g c d m t)) := by
      congr <;> simp [Φ_def, v_def]
    have h11 : inner ℝ p (globalGrainDirection (g (p 2))) = inner ℝ p w := by
      congr <;> simp [w_def, h9]
    rw [h10, h, h11]
  have h_proj : (fun q : Point3 => inner ℝ q v) '' (Φ '' S) =
      (fun p : Point3 => inner ℝ p w) '' S := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨q, hq, hy⟩
      rcases hq with ⟨p, hp, hq_eq⟩
      have h_id : inner ℝ (Φ p) v = inner ℝ p w := h_pointwise p hp
      have h_y : inner ℝ p w = y := by
        have h7 : inner ℝ (Φ p) v = y := by
          rw [hq_eq] <;> exact hy
        exact h_id.symm.trans h7
      exact ⟨p, hp, h_y⟩
    · rintro ⟨p, hp, hy⟩
      have h_id : inner ℝ (Φ p) v = inner ℝ p w := h_pointwise p hp
      have h_y : inner ℝ (Φ p) v = y := h_id.trans hy
      exact ⟨Φ p, ⟨p, hp, rfl⟩, h_y⟩
  have h_main : scalarProjection v (horizontalSlice (Φ '' E) t) =
      (fun q : Point3 => inner ℝ q v) '' (horizontalSlice (Φ '' E) t) := by
    rfl
  rw [h_main, h_slice_image, h_proj]
  <;> rfl

end Kakeya.Assouad
