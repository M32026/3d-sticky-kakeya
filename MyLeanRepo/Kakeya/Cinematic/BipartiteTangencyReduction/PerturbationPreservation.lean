import MyLeanRepo.Kakeya.Cinematic.PreliminaryDichotomy
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# Perturbation preservation and pseudo-circle family (clean rewrite)

Infrastructure lemmas for the robust unit-multiplicity graph-lens core:

1. **Vertical translate simp lemmas**
2. **Perturbation preservation**: vertical translations preserve
   `IsLambdaTangent` up to an explicit error, and approximately preserve
   `c2Distance`.
3. **Two-zeros level-set bound**: on a short interval, two functions from an
   `IsCinematicFamily` can take a sufficiently small level at most twice,
   via the preliminary dichotomy (PYZ Lemma 13).
4. **Transversality** after a `FiniteTangencyPerturbation`.

## Proof route

* Perturbation preservation is a direct triangle inequality.
* The two-zeros bound uses `preliminary_dichotomy`:
  - If `|f-g| ≥ d/(6K)` everywhere, no level `c` with `|c| < d/(6K)` is attained.
  - If `|f-g| < d/(3K)` and `|f'-g'| ≥ d/(6K)` everywhere, Rolle gives at most 1 solution.
  - If both `|f-g|` and `|f'-g'|` are small, then `|f''-g''| ≥ d/(6K)` everywhere,
    and Rolle twice gives at most 2 solutions.
* Transversality follows directly from `HasNoExactTangenciesOn`.

## Whiteprint nodes

* `robust_unit_core/perturbation_preservation`
* `robust_unit_core/pseudo_circle`
-/

noncomputable section

namespace Kakeya.Cinematic

open Set

/-! ### Vertical translation simp lemmas -/

@[simp]
lemma verticalTranslate_apply (f : C2Function) (c : ℝ) (x : UnitPoint) :
    (f.verticalTranslate c) x = f x + c := by
  rfl

@[simp]
lemma verticalTranslate_firstDeriv (f : C2Function) (c : ℝ) :
    (f.verticalTranslate c).firstDeriv = f.firstDeriv := by
  rfl

@[simp]
lemma verticalTranslate_secondDeriv (f : C2Function) (c : ℝ) :
    (f.verticalTranslate c).secondDeriv = f.secondDeriv := by
  rfl

/-- Vertical translations compose additively. -/
lemma verticalTranslate_compose (f : C2Function) (c1 c2 : ℝ) :
    (f.verticalTranslate c1).verticalTranslate c2 = f.verticalTranslate (c1 + c2) := by
  apply C2Function.toJet_injective
  simp [C2Function.toJet]
  <;> ext x <;> simp [verticalTranslate_apply] <;> ring

/-! ### Perturbation preservation -/

/--
Vertical translation preserves `IsLambdaTangent` with a relaxed constant:
if `|c| ≤ epsilon` and `0 < δ`, then `λ`-tangency becomes
`(λ + epsilon/δ)`-tangency.
-/
lemma isLambdaTangent_verticalTranslate {δ t : ℝ} (hδ : 0 < δ)
    {R : CurvilinearRectangle δ t} {f : C2Function} {lambda epsilon : ℝ}
    (h : R.IsLambdaTangent f lambda) {c : ℝ} (hc : |c| ≤ epsilon) :
    R.IsLambdaTangent (f.verticalTranslate c) (lambda + epsilon / δ) := by
  intro p hp
  have h1 : |p.2 - f p.1| ≤ lambda * δ := h p hp
  have h2 : p.2 - (f.verticalTranslate c) p.1 = (p.2 - f p.1) - c := by
    simp [verticalTranslate_apply] <;> ring
  rw [h2]
  calc
    |(p.2 - f p.1) - c| ≤ |p.2 - f p.1| + |c| := by
      exact abs_sub _ _
    _ ≤ lambda * δ + epsilon := by linarith
    _ = (lambda + epsilon / δ) * δ := by
      field_simp [hδ.ne'] <;> ring

/-- Expand `c2Distance` into the max of three component distances. -/
lemma c2Distance_expand (f g : C2Function) :
    c2Distance f g = max (dist f.value g.value)
      (max (dist f.firstDeriv g.firstDeriv)
        (dist f.secondDeriv g.secondDeriv)) := by
  have h1 : c2Distance f g = dist (C2Function.toJet f) (C2Function.toJet g) := by
    simp [c2Distance_eq_dist] <;> rfl
  rw [h1]
  simp [C2Function.toJet, Prod.dist_eq] <;> rfl

/-- Vertical translation by the same amount preserves `c2Distance`. -/
lemma c2Distance_verticalTranslate_same (f g : C2Function) (c : ℝ) :
    c2Distance (f.verticalTranslate c) (g.verticalTranslate c) =
        c2Distance f g := by
  let Z : C(UnitPoint, ℝ) := ContinuousMap.const UnitPoint c
  have h_val : dist (f.verticalTranslate c).value (g.verticalTranslate c).value =
      dist f.value g.value := by
    have h : dist (f.value + Z) (g.value + Z) = dist f.value g.value := by
      exact dist_add_right f.value g.value Z
    exact h
  have h_deriv1 : dist (f.verticalTranslate c).firstDeriv
      (g.verticalTranslate c).firstDeriv = dist f.firstDeriv g.firstDeriv := by
    simp
  have h_deriv2 : dist (f.verticalTranslate c).secondDeriv
      (g.verticalTranslate c).secondDeriv = dist f.secondDeriv g.secondDeriv := by
    simp
  rw [c2Distance_expand (f.verticalTranslate c) (g.verticalTranslate c),
      c2Distance_expand f g]
  rw [h_val, h_deriv1, h_deriv2]

/-- Distance from a function to its vertical translate is `|c|`. -/
lemma c2Distance_verticalTranslate_self (f : C2Function) (c : ℝ) :
    c2Distance f (f.verticalTranslate c) = |c| := by
  rw [c2Distance_expand f (f.verticalTranslate c)]
  let Z : C(UnitPoint, ℝ) := ContinuousMap.const UnitPoint c
  have h_val : dist f.value (f.verticalTranslate c).value = |c| := by
    have h_eq : (f.verticalTranslate c).value = f.value + Z := by rfl
    rw [h_eq]
    have h_dist : dist f.value (f.value + Z) = ‖Z‖ := by
      rw [dist_eq_norm]
      have h_sub : f.value - (f.value + Z) = -Z := by ext x; simp
      rw [h_sub, norm_neg]
    rw [h_dist]
    have hZ : ‖Z‖ = |c| := by
      let x0 : UnitPoint := ⟨0, by simp [unitInterval] <;> norm_num⟩
      have h_iff : ‖Z‖ ≤ |c| ↔ ∀ (x : UnitPoint), ‖Z x‖ ≤ |c| :=
        ContinuousMap.norm_le (f := Z) (C := |c|) (C0 := abs_nonneg c)
      have h_le : ‖Z‖ ≤ |c| := h_iff.mpr (fun x => by simp [Z, Real.norm_eq_abs])
      have h_ge : |c| ≤ ‖Z‖ := by
        have h : ‖Z x0‖ ≤ ‖Z‖ := ContinuousMap.norm_coe_le_norm Z x0
        have h4 : ‖Z x0‖ = |c| := by simp [Z, Real.norm_eq_abs]
        rw [h4] at h
        exact h
      exact le_antisymm h_le h_ge
    rw [hZ]
  have h1 : dist f.firstDeriv (f.verticalTranslate c).firstDeriv = 0 := by simp
  have h2 : dist f.secondDeriv (f.verticalTranslate c).secondDeriv = 0 := by simp
  rw [h_val, h1, h2]
  have h3 : 0 ≤ |c| := abs_nonneg c
  simp [h3] <;> linarith

/-- Vertical translation by the same amount preserves `jetGap`. -/
lemma jetGap_verticalTranslate_same (f g : C2Function) (c : ℝ)
    (x : UnitPoint) :
    jetGap (f.verticalTranslate c) (g.verticalTranslate c) x = jetGap f g x := by
  have h1 : (f.verticalTranslate c) x - (g.verticalTranslate c) x = f x - g x := by
    simp [verticalTranslate_apply] <;> ring
  have h2 : (f.verticalTranslate c).firstDeriv x = f.firstDeriv x := by simp
  have h3 : (g.verticalTranslate c).firstDeriv x = g.firstDeriv x := by simp
  have h4 : (f.verticalTranslate c).secondDeriv x = f.secondDeriv x := by simp
  have h5 : (g.verticalTranslate c).secondDeriv x = g.secondDeriv x := by simp
  simp [jetGap, h1, h2, h3, h4, h5]

/--
Vertical translations by different amounts decrease `c2Distance` by at
most the difference in shifts.
-/
lemma c2Distance_verticalTranslate_lower (f g : C2Function)
    (c_f c_g : ℝ) :
    c2Distance (f.verticalTranslate c_f) (g.verticalTranslate c_g) ≥
        c2Distance f g - |c_f - c_g| := by
  have h1 : c2Distance f g =
      c2Distance (f.verticalTranslate c_f) (g.verticalTranslate c_f) :=
    (c2Distance_verticalTranslate_same f g c_f).symm
  have h2 : c2Distance (f.verticalTranslate c_f) (g.verticalTranslate c_f) ≤
      c2Distance (f.verticalTranslate c_f) (g.verticalTranslate c_g) +
      c2Distance (g.verticalTranslate c_g) (g.verticalTranslate c_f) :=
    dist_triangle _ _ _
  have h3 : c2Distance (g.verticalTranslate c_g) (g.verticalTranslate c_f) =
      c2Distance g (g.verticalTranslate (c_f - c_g)) := by
    have h_same := c2Distance_verticalTranslate_same
      (g.verticalTranslate c_g) (g.verticalTranslate c_f) (-c_g)
    have h_comp1 : (g.verticalTranslate c_g).verticalTranslate (-c_g) = g := by
      rw [verticalTranslate_compose]
      have hsum : c_g + (-c_g) = (0 : ℝ) := by ring
      rw [hsum]
      apply C2Function.toJet_injective
      simp [C2Function.toJet] <;> ext x <;> simp [verticalTranslate_apply]
    have h_comp2 : (g.verticalTranslate c_f).verticalTranslate (-c_g) =
        g.verticalTranslate (c_f - c_g) := by
      rw [verticalTranslate_compose]
      have hsum : c_f + (-c_g) = c_f - c_g := by ring
      rw [hsum]
    rw [h_comp1, h_comp2] at h_same
    exact h_same.symm
  have h4 : c2Distance g (g.verticalTranslate (c_f - c_g)) = |c_f - c_g| :=
    c2Distance_verticalTranslate_self g (c_f - c_g)
  have h5 : c2Distance (g.verticalTranslate c_g) (g.verticalTranslate c_f) = |c_f - c_g| := by
    rw [h3, h4]
  have h6 : c2Distance f g ≤ c2Distance (f.verticalTranslate c_f) (g.verticalTranslate c_g) + |c_f - c_g| := by
    calc c2Distance f g
      = c2Distance (f.verticalTranslate c_f) (g.verticalTranslate c_f) := h1
    _ ≤ c2Distance (f.verticalTranslate c_f) (g.verticalTranslate c_g) + c2Distance (g.verticalTranslate c_g) (g.verticalTranslate c_f) := h2
    _ = c2Distance (f.verticalTranslate c_f) (g.verticalTranslate c_g) + |c_f - c_g| := by rw [h5]
  linarith

/-! ### Two-zeros level-set bound via preliminary dichotomy -/

/--
On a short interval, two distinct functions from an `IsCinematicFamily`
cannot take the same value `c` three times, provided `|c| < d/(6K)` where
`d = c2Distance f g`.

Proof via `preliminary_dichotomy` (PYZ Lemma 13):
1. If `|f-g| ≥ d/(6K)` everywhere, no solution exists.
2. If `|f-g| < d/(3K)` and `|f'-g'| ≥ d/(6K)` everywhere, Rolle gives at most 1.
3. If both are small, `|f''-g''| ≥ d/(6K)` everywhere, and Rolle twice gives at most 2.
-/
lemma two_zeros_level_via_dichotomy
    {K D : ℝ} (hK : 1 ≤ K) (hD : 1 ≤ D)
    {family : Set C2Function} (hfam : IsCinematicFamily family K D)
    {I : ParameterInterval} (hI : I.IsShort K)
    {f g : C2Function} (hf : f ∈ family) (hg : g ∈ family)
    (hne : f ≠ g)
    {c : ℝ} (hc : |c| < c2Distance f g / (6 * K))
    {x₁ x₂ x₃ : UnitPoint}
    (hx₁ : x₁ ∈ I.carrier) (hx₂ : x₂ ∈ I.carrier) (hx₃ : x₃ ∈ I.carrier)
    (h12 : (x₁ : ℝ) < x₂) (h23 : (x₂ : ℝ) < x₃)
    (h1 : f x₁ - g x₁ = c) (h2 : f x₂ - g x₂ = c) (h3 : f x₃ - g x₃ = c) :
    False := by
  set d : ℝ := c2Distance f g with hd_def
  have hK_pos : 0 < K := by linarith
  have h6K_pos : 0 < 6 * K := by linarith
  have h_d_pos : 0 < d := by
    by_contra h
    have h' : d ≤ 0 := by linarith
    have h_nn : 0 ≤ c2Distance f g := dist_nonneg
    have h'' : d = 0 := by
      simp only [hd_def] at *
      <;> linarith
    have hdist : dist f g = 0 := by
      simpa [c2Distance_eq_dist, hd_def] using h''
    have hfg : f = g := by
      simpa [dist_eq_zero] using hdist
    exact hne hfg
  let h_ext : ℝ → ℝ := fun x => f.extension x - g.extension x
  let h1_ext : ℝ → ℝ := deriv h_ext
  let h2_ext : ℝ → ℝ := deriv h1_ext
  have h_cont : Continuous h_ext :=
    (f.extension_contDiff.sub g.extension_contDiff).continuous
  have h_cd2 : ContDiff ℝ 2 h_ext := f.extension_contDiff.sub g.extension_contDiff
  have h1_cd : ContDiff ℝ 1 h1_ext := by
    have h' : ContDiff ℝ (1 + 1) h_ext := h_cd2
    exact h'.deriv'
  have h1_cont : Continuous h1_ext := h1_cd.continuous
  have h_eval : ∀ (x : UnitPoint), h_ext (x : ℝ) = f x - g x := by
    intro x; simp [h_ext]
  have h1_eval : ∀ (x : UnitPoint), h1_ext (x : ℝ) = f.firstDeriv x - g.firstDeriv x := by
    intro x
    have hderiv : deriv h_ext (x : ℝ) =
        deriv f.extension (x : ℝ) - deriv g.extension (x : ℝ) := by
      have h_eq : h_ext = f.extension - g.extension := by funext y; rfl
      rw [h_eq]
      exact deriv_sub
        (f.extension_contDiff.differentiable (by norm_num)).differentiableAt
        (g.extension_contDiff.differentiable (by norm_num)).differentiableAt
    have h_id : h1_ext (x : ℝ) = deriv h_ext (x : ℝ) := by rfl
    rw [h_id, hderiv]
    rw [f.deriv_extension_eq_firstDeriv x, g.deriv_extension_eq_firstDeriv x]
  have h2_eval : ∀ (x : UnitPoint), h2_ext (x : ℝ) = f.secondDeriv x - g.secondDeriv x := by
    intro x
    have h1_eq : h1_ext = deriv f.extension - deriv g.extension := by
      funext y
      have h : deriv h_ext y = deriv f.extension y - deriv g.extension y := by
        have h_eq2 : h_ext = f.extension - g.extension := by funext z; rfl
        rw [h_eq2]
        exact deriv_sub
          (f.extension_contDiff.differentiable (by norm_num)).differentiableAt
          (g.extension_contDiff.differentiable (by norm_num)).differentiableAt
      exact h
    have h_fc1 : ContDiff ℝ 1 (deriv f.extension) := by
      have h' : ContDiff ℝ (1 + 1) f.extension := f.extension_contDiff
      exact h'.deriv'
    have h_gc1 : ContDiff ℝ 1 (deriv g.extension) := by
      have h' : ContDiff ℝ (1 + 1) g.extension := g.extension_contDiff
      exact h'.deriv'
    have hderiv2 : deriv h1_ext (x : ℝ) =
        deriv (deriv f.extension) (x : ℝ) - deriv (deriv g.extension) (x : ℝ) := by
      rw [h1_eq]
      exact deriv_sub
        (h_fc1.differentiable (by norm_num)).differentiableAt
        (h_gc1.differentiable (by norm_num)).differentiableAt
    have h_id : h2_ext (x : ℝ) = deriv h1_ext (x : ℝ) := by rfl
    rw [h_id, hderiv2]
    rw [f.secondDeriv_extension_eq_secondDeriv x, g.secondDeriv_extension_eq_secondDeriv x]
  rcases preliminary_dichotomy K D hK hD family hfam I hI f hf g hg with
    ⟨h_dich1, h_dich2, h_curv3⟩
  rcases h_dich1 with (hS1 | hL1)
  · rcases h_dich2 with (hS2 | hL2)
    · have hL3 : ∀ x ∈ I.carrier, (6 * K)⁻¹ * d ≤ |f.secondDeriv x - g.secondDeriv x| :=
        h_curv3 ⟨hS1, hS2⟩
      have h_eq1 : h_ext (x₁ : ℝ) = h_ext (x₂ : ℝ) := by
        rw [h_eval x₁, h_eval x₂, h1, h2]
      have h_eq2 : h_ext (x₂ : ℝ) = h_ext (x₃ : ℝ) := by
        rw [h_eval x₂, h_eval x₃, h2, h3]
      rcases exists_deriv_eq_zero h12 h_cont.continuousOn h_eq1 with
        ⟨y₁, hy₁_in, hy₁_eq⟩
      rcases exists_deriv_eq_zero h23 h_cont.continuousOn h_eq2 with
        ⟨y₂, hy₂_in, hy₂_eq⟩
      have h_y1_lt_y2 : y₁ < y₂ := by
        linarith [hy₁_in.1, hy₁_in.2, hy₂_in.1, hy₂_in.2]
      have h1_eq : h1_ext y₁ = h1_ext y₂ := by
        have hya : h1_ext y₁ = 0 := by simpa [h1_ext] using hy₁_eq
        have hyb : h1_ext y₂ = 0 := by simpa [h1_ext] using hy₂_eq
        rw [hya, hyb]
      rcases exists_deriv_eq_zero h_y1_lt_y2 h1_cont.continuousOn h1_eq with
        ⟨z, hz_in, hz_eq⟩
      have h_z_gt_x1 : (x₁ : ℝ) < z := by linarith [hy₁_in.1, hz_in.1]
      have h_z_lt_x3 : z < (x₃ : ℝ) := by linarith [hz_in.2, hy₂_in.2]
      have hz_in01 : z ∈ Set.Icc (0 : ℝ) 1 := by
        have h_x1_0 : (0 : ℝ) ≤ (x₁ : ℝ) := x₁.property.1
        have h_x3_1 : (x₃ : ℝ) ≤ (1 : ℝ) := x₃.property.2
        exact ⟨by linarith, by linarith⟩
      let zp : UnitPoint := ⟨z, hz_in01⟩
      have hz_in_I : zp ∈ I.carrier := by
        have h_ileft : I.left ≤ (x₁ : ℝ) := hx₁.1
        have h_iright : (x₃ : ℝ) ≤ I.right := hx₃.2
        exact ⟨by linarith, by linarith⟩
      have hz2_eq : h2_ext z = 0 := by simpa [h2_ext] using hz_eq
      have h_bound : (6 * K)⁻¹ * d ≤ |f.secondDeriv zp - g.secondDeriv zp| :=
        hL3 zp hz_in_I
      have h2_eq : f.secondDeriv zp - g.secondDeriv zp = h2_ext z := by
        have h : h2_ext (zp : ℝ) = f.secondDeriv zp - g.secondDeriv zp := h2_eval zp
        exact h.symm
      rw [h2_eq] at h_bound
      rw [hz2_eq] at h_bound
      have h_pos : 0 < (6 * K)⁻¹ * d := by positivity
      linarith
    · have h_eq1 : h_ext (x₁ : ℝ) = h_ext (x₂ : ℝ) := by
        rw [h_eval x₁, h_eval x₂, h1, h2]
      rcases exists_deriv_eq_zero h12 h_cont.continuousOn h_eq1 with
        ⟨y, hy_in, hy_eq⟩
      have h_y_gt_x1 : (x₁ : ℝ) < y := hy_in.1
      have h_y_lt_x2 : y < (x₂ : ℝ) := hy_in.2
      have hy_in01 : y ∈ Set.Icc (0 : ℝ) 1 := by
        have h_x1_0 : (0 : ℝ) ≤ (x₁ : ℝ) := x₁.property.1
        have h_x2_1 : (x₂ : ℝ) ≤ (1 : ℝ) := x₂.property.2
        exact ⟨by linarith, by linarith⟩
      let yp : UnitPoint := ⟨y, hy_in01⟩
      have hy_in_I : yp ∈ I.carrier := by
        have h_ileft : I.left ≤ (x₁ : ℝ) := hx₁.1
        have h_iright : (x₂ : ℝ) ≤ I.right := hx₂.2
        exact ⟨by linarith, by linarith⟩
      have h_bound : (6 * K)⁻¹ * d ≤ |f.firstDeriv yp - g.firstDeriv yp| :=
        hL2 yp hy_in_I
      have hy1_eq : h1_ext y = 0 := by simpa [h1_ext] using hy_eq
      have h1_eq : f.firstDeriv yp - g.firstDeriv yp = h1_ext y := by
        have h : h1_ext (yp : ℝ) = f.firstDeriv yp - g.firstDeriv yp := h1_eval yp
        exact h.symm
      rw [h1_eq] at h_bound
      rw [hy1_eq] at h_bound
      have h_pos : 0 < (6 * K)⁻¹ * d := by positivity
      linarith
  · have h_bound1 : (6 * K)⁻¹ * d ≤ |f x₁ - g x₁| := hL1 x₁ hx₁
    rw [h1] at h_bound1
    have h_c' : |c| < (6 * K)⁻¹ * d := by
      have h_eq : (6 * K)⁻¹ * d = d / (6 * K) := by
        field_simp [h6K_pos.ne'] <;> ring
      rw [h_eq]; exact hc
    linarith

/-! ### Pseudo-circle properties after perturbation -/

/--
After sufficiently small vertical shifts, two functions from an
`IsCinematicFamily` have at most two intersections on a short interval.

This is the level-set lemma with `c = shift g - shift f`.
-/
lemma perturbed_at_most_two_intersections
    {K D : ℝ} (hK : 1 ≤ K) (hD : 1 ≤ D)
    {family : Set C2Function} (hfam : IsCinematicFamily family K D)
    {I : ParameterInterval} (hI : I.IsShort K)
    {f g : C2Function} (hf : f ∈ family) (hg : g ∈ family)
    (hne : f ≠ g)
    {shift : C2Function → ℝ}
    (h_shift : |shift f - shift g| < c2Distance f g / (6 * K))
    {x₁ x₂ x₃ : UnitPoint}
    (hx₁ : x₁ ∈ I.carrier) (hx₂ : x₂ ∈ I.carrier) (hx₃ : x₃ ∈ I.carrier)
    (h12 : (x₁ : ℝ) < x₂) (h23 : (x₂ : ℝ) < x₃)
    (h1 : (f.verticalTranslate (shift f)) x₁ =
        (g.verticalTranslate (shift g)) x₁)
    (h2 : (f.verticalTranslate (shift f)) x₂ =
        (g.verticalTranslate (shift g)) x₂)
    (h3 : (f.verticalTranslate (shift f)) x₃ =
        (g.verticalTranslate (shift g)) x₃) : False := by
  let c := shift g - shift f
  have hc1 : f x₁ - g x₁ = c := by
    have h : f x₁ + shift f = g x₁ + shift g := h1
    linarith
  have hc2 : f x₂ - g x₂ = c := by
    have h : f x₂ + shift f = g x₂ + shift g := h2
    linarith
  have hc3 : f x₃ - g x₃ = c := by
    have h : f x₃ + shift f = g x₃ + shift g := h3
    linarith
  have h_c : |c| < c2Distance f g / (6 * K) := by
    have h_abs : |shift g - shift f| = |shift f - shift g| := by
      rw [abs_sub_comm]
    simpa [c, h_abs] using h_shift
  exact two_zeros_level_via_dichotomy hK hD hfam hI hf hg hne h_c
    hx₁ hx₂ hx₃ h12 h23 hc1 hc2 hc3

/--
After a perturbation with `HasNoExactTangenciesOn`, every intersection of
two shifted functions on `I.carrier` is transverse (first derivatives
differ).
-/
lemma perturbed_intersections_transverse
    {I : ParameterInterval} {F : FiniteFunctionFamily}
    {shift : C2Function → ℝ}
    (h_tang : F.HasNoExactTangenciesOn I shift)
    {f g : C2Function} (hf : f ∈ F.carrier) (hg : g ∈ F.carrier)
    (hne : f ≠ g) {x : UnitPoint} (hx : x ∈ I.carrier)
    (h_eq : (f.verticalTranslate (shift f)) x =
        (g.verticalTranslate (shift g)) x) :
    (f.verticalTranslate (shift f)).firstDeriv x ≠
        (g.verticalTranslate (shift g)).firstDeriv x := by
  have h := h_tang hf hg hne x hx
  rcases h with (h | h)
  · exfalso; exact h h_eq
  · exact h

end Kakeya.Cinematic
