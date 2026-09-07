import MyLeanRepo.Kakeya.Assouad.ProjectionNormalization
import MyLeanRepo.Kakeya.Assouad.DerivativeBracketing
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Centered rescaling of a normalized slope

This is the one-variable part of the anisotropic rescaling in WZ2 Section 6.
The output formula is explicit so downstream projection arguments can transport
the associated tube and shading data rather than using a bare existence result.
-/

noncomputable section

namespace Kakeya.Assouad

/--
If a normalized slope has derivative between `m` and `2m` on a sufficiently
short interval, affine reparametrization and vertical scaling produce a
nonsingular slope centered at zero.
-/
lemma slope_rescaling_to_centered_nonsingular_of_second
    (g : SlopeFunction)
    {c d m : ℝ} (hcd : c < d) (hm_pos : 0 < m)
    (h_sub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (h_deriv : ∀ x ∈ Set.Icc c d,
      m ≤ |deriv g x| ∧ |deriv g x| ≤ 2 * m)
    (h_second : ∀ x ∈ Set.Icc c d,
      |deriv (deriv g) x| ≤ 1)
    (h_len : d - c ≤ m / 50) :
    ∃ f : SlopeFunction,
      f.IsNonsingular ∧
      f 0 = 0 ∧
      ∀ t : ℝ,
        f t =
          g (c + (d - c) / 2 * (t + 1)) / (m * (d - c) / 2) -
            g (c + (d - c) / 2) / (m * (d - c) / 2) := by
  set ell : ℝ := d - c with hell_def
  have hell_pos : 0 < ell := by linarith
  set K : ℝ := m * ell / 2 with hK_def
  have hK_pos : 0 < K := by positivity
  set phi : ℝ → ℝ := fun t => c + ell / 2 * (t + 1) with hphi_def
  let gphi : ℝ → ℝ := g ∘ phi
  set fRaw : ℝ → ℝ := fun t => gphi t / K with hfRaw_def

  have hg_cd : ContDiff ℝ 2 g := g.contDiff
  have h_id : ContDiff ℝ 2 (fun t : ℝ => t) := contDiff_id
  have h_const_one : ContDiff ℝ 2 (fun _ : ℝ => (1 : ℝ)) := contDiff_const
  have h_t_add_one : ContDiff ℝ 2 (fun t : ℝ => t + 1) :=
    h_id.add h_const_one
  have h_const_half : ContDiff ℝ 2 (fun _ : ℝ => ell / 2) := contDiff_const
  have h_mul : ContDiff ℝ 2 (fun t : ℝ => ell / 2 * (t + 1)) :=
    h_const_half.mul h_t_add_one
  have h_const_c : ContDiff ℝ 2 (fun _ : ℝ => c) := contDiff_const
  have hphi_cd : ContDiff ℝ 2 phi := by
    have h : ContDiff ℝ 2 (fun t : ℝ => c + ell / 2 * (t + 1)) :=
      h_const_c.add h_mul
    simpa [hphi_def] using h
  have hgphi_cd : ContDiff ℝ 2 gphi := hg_cd.comp hphi_cd
  have hfRaw_cd : ContDiff ℝ 2 fRaw := by
    have h : ContDiff ℝ 2 (fun t => gphi t / K) :=
      hgphi_cd.div_const K
    simpa [hfRaw_def] using h

  have hg_diff : Differentiable ℝ g :=
    hg_cd.differentiable (by norm_num)
  have hg_deriv_cd : ContDiff ℝ 1 (deriv g) := hg_cd.deriv'
  have hg_deriv_diff : Differentiable ℝ (deriv g) :=
    hg_deriv_cd.differentiable_one
  have hgphi_diff : Differentiable ℝ gphi :=
    hgphi_cd.differentiable (by norm_num)
  have hphi_diff : ∀ t, DifferentiableAt ℝ phi t :=
    fun t => (hphi_cd.differentiable (by norm_num)).differentiableAt

  have hphi_alt :
      phi = fun t : ℝ => (c + ell / 2) + (ell / 2) * t := by
    funext t
    simp only [hphi_def]
    ring
  have hphi_deriv : ∀ t, deriv phi t = ell / 2 := by
    intro t
    have hder : HasDerivAt phi (ell / 2) t := by
      rw [hphi_alt]
      exact (hasDerivAt_const_mul (ell / 2)).const_add (c + ell / 2)
    exact hder.deriv

  set firstExpected : ℝ → ℝ :=
    fun t => deriv g (phi t) / m with hfirstExpected_def
  set secondExpected : ℝ → ℝ :=
    fun t => deriv (deriv g) (phi t) * ell / (2 * m)
      with hsecondExpected_def

  have hderiv_first : ∀ t, deriv fRaw t = firstExpected t := by
    intro t
    have hgphi_at : DifferentiableAt ℝ gphi t :=
      hgphi_diff.differentiableAt
    have hraw :
        deriv fRaw t = deriv gphi t / K :=
      (hgphi_at.hasDerivAt.div_const K).deriv
    have hcomp :
        deriv gphi t = deriv g (phi t) * deriv phi t :=
      deriv_comp t hg_diff.differentiableAt (hphi_diff t)
    rw [hraw, hcomp, hphi_deriv t]
    dsimp only [firstExpected]
    rw [hK_def]
    field_simp [hK_pos.ne']

  have hderiv_first_eq : deriv fRaw = firstExpected := by
    funext t
    exact hderiv_first t

  let gDerivPhi : ℝ → ℝ := (deriv g) ∘ phi
  have hgDerivPhi_diff : Differentiable ℝ gDerivPhi :=
    hg_deriv_diff.comp hphi_diff
  have hderiv_second :
      ∀ t, deriv firstExpected t = secondExpected t := by
    intro t
    have hgDerivPhi_at : DifferentiableAt ℝ gDerivPhi t :=
      hgDerivPhi_diff.differentiableAt
    have hraw :
        deriv firstExpected t = deriv gDerivPhi t / m :=
      (hgDerivPhi_at.hasDerivAt.div_const m).deriv
    have hcomp :
        deriv gDerivPhi t =
          deriv (deriv g) (phi t) * deriv phi t :=
      deriv_comp t hg_deriv_diff.differentiableAt (hphi_diff t)
    rw [hraw, hcomp, hphi_deriv t]
    dsimp only [secondExpected]
    ring
  have hderiv_second_eq :
      deriv (deriv fRaw) = secondExpected := by
    rw [hderiv_first_eq]
    funext t
    exact hderiv_second t

  have hphi_maps :
      ∀ t ∈ Set.Icc (-1 : ℝ) 1, phi t ∈ Set.Icc c d := by
    intro t ht
    constructor
    · simp only [hphi_def]
      have : 0 ≤ t + 1 := by linarith [ht.1]
      have : 0 ≤ ell / 2 * (t + 1) := by positivity
      linarith
    · simp only [hphi_def, hell_def]
      have ht_two : t + 1 ≤ 2 := by linarith [ht.2]
      have hprod :
          ell / 2 * (t + 1) ≤ ell / 2 * 2 := by
        gcongr
      rw [show ell / 2 * 2 = ell by ring] at hprod
      linarith

  let raw : SlopeFunction := ⟨fRaw, hfRaw_cd⟩
  have hraw_nonsingular : raw.IsNonsingular := by
    intro t ht
    have hphi_mem : phi t ∈ Set.Icc c d := hphi_maps t ht
    have hbracket := h_deriv (phi t) hphi_mem
    have hfirst :
        |deriv raw t| = |deriv g (phi t)| / m := by
      change |deriv fRaw t| = _
      rw [hderiv_first_eq]
      simp only [firstExpected]
      rw [abs_div, abs_of_pos hm_pos]
    rw [hfirst]
    constructor
    · calc
        1 = m / m := by field_simp [hm_pos.ne']
        _ ≤ |deriv g (phi t)| / m := by
          exact div_le_div_of_nonneg_right hbracket.1 hm_pos.le
    constructor
    · calc
        |deriv g (phi t)| / m ≤ (2 * m) / m := by
          exact div_le_div_of_nonneg_right hbracket.2 hm_pos.le
        _ = 2 := by field_simp [hm_pos.ne']
    · have hphi_norm : phi t ∈ Set.Icc (-1 : ℝ) 1 :=
        h_sub hphi_mem
      have hsecond :
          |deriv (deriv raw) t| =
            |deriv (deriv g) (phi t)| * ell / (2 * m) := by
        change |deriv (deriv fRaw) t| = _
        rw [hderiv_second_eq]
        simp only [secondExpected]
        have hden_pos : 0 < 2 * m := by positivity
        rw [abs_div, abs_mul, abs_of_pos hell_pos,
          abs_of_pos hden_pos]
      rw [hsecond]
      calc
        |deriv (deriv g) (phi t)| * ell / (2 * m)
            ≤ 1 * ell / (2 * m) := by
          gcongr
          exact h_second (phi t) hphi_mem
        _ = ell / (2 * m) := by ring
        _ ≤ (m / 50) / (2 * m) := by
          exact div_le_div_of_nonneg_right h_len (by positivity)
        _ = 1 / 100 := by
          field_simp [hm_pos.ne']
          ring

  refine ⟨raw.centered, SlopeFunction.centered_isNonsingular hraw_nonsingular,
    raw.centered_zero, ?_⟩
  intro t
  simp only [SlopeFunction.centered_apply, raw]
  change fRaw t - fRaw 0 = _
  simp only [hfRaw_def, gphi, Function.comp_apply, hphi_def, hK_def,
    hell_def, zero_add, one_mul, mul_one]

/-- Backward-compatible wrapper for a globally normalized slope. -/
lemma slope_rescaling_to_centered_nonsingular
    (g : SlopeFunction) (hg_norm : g.IsNormalized)
    {c d m : ℝ} (hcd : c < d) (hm_pos : 0 < m)
    (h_sub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (h_deriv : ∀ x ∈ Set.Icc c d,
      m ≤ |deriv g x| ∧ |deriv g x| ≤ 2 * m)
    (h_len : d - c ≤ m / 50) :
    ∃ f : SlopeFunction,
      f.IsNonsingular ∧
      f 0 = 0 ∧
      ∀ t : ℝ,
        f t =
          g (c + (d - c) / 2 * (t + 1)) / (m * (d - c) / 2) -
            g (c + (d - c) / 2) / (m * (d - c) / 2) := by
  apply slope_rescaling_to_centered_nonsingular_of_second g hcd hm_pos
    h_sub h_deriv
  · intro x hx
    exact (hg_norm x (h_sub hx)).2.2
  · exact h_len

/--
Combined bracketing and rescaling bridge used after the large-slope step.

The input interval has derivative magnitude between `L` and one and second
derivative at most one.  The output chooses a still shorter subinterval, so
the exact centered rescaling satisfies the projection API.
-/
lemma large_slope_to_centered_nonsingular
    (g : SlopeFunction) (hg_norm : g.IsNormalized)
    {a b L : ℝ}
    (hab : a < b) (hL : 0 < L)
    (h_sub : Set.Icc a b ⊆ Set.Icc (-1 : ℝ) 1)
    (h_length : L / 4 ≤ b - a)
    (h_low : ∀ x ∈ Set.Icc a b, L ≤ |deriv g x|)
    (h_high : ∀ x ∈ Set.Icc a b, |deriv g x| ≤ 1) :
    ∃ c d m : ℝ,
      a ≤ c ∧ c < d ∧ d ≤ b ∧
      0 < m ∧ L ≤ m ∧ m ≤ 1 ∧
      d - c = L / 50 ∧
      ∃ f : SlopeFunction,
        f.IsNonsingular ∧
        f 0 = 0 ∧
        ∀ t : ℝ,
          f t =
            g (c + (d - c) / 2 * (t + 1)) /
                (m * (d - c) / 2) -
              g (c + (d - c) / 2) /
                (m * (d - c) / 2) := by
  have hsecond :
      ∀ x ∈ Set.Icc a b, |deriv (deriv g) x| ≤ 1 := by
    intro x hx
    exact (hg_norm x (h_sub hx)).2.2
  rcases derivative_bracketing g.contDiff hsecond hab hL h_length
      h_low h_high with
    ⟨c0, d0, m, hc0, hc0d0, hd0, hlen0, hm_pos, hm_low, hm_high,
      hbracket⟩
  let c : ℝ := c0
  let d : ℝ := c0 + L / 50
  have hLd_pos : 0 < L / 50 := by positivity
  have hshort : L / 50 ≤ d0 - c0 := by
    calc
      L / 50 ≤ L / 4 := by linarith
      _ ≤ d0 - c0 := hlen0
  have hc : a ≤ c := hc0
  have hcd : c < d := by
    dsimp only [c, d]
    linarith
  have hd : d ≤ b := by
    dsimp only [c, d]
    have : c0 + L / 50 ≤ d0 := by linarith
    exact this.trans hd0
  have hcd_len : d - c = L / 50 := by
    dsimp only [c, d]
    ring
  have hcd_sub : Set.Icc c d ⊆ Set.Icc c0 d0 := by
    intro x hx
    exact ⟨by simpa [c] using hx.1, by
      have hd_d0 : d ≤ d0 := by
        dsimp only [c, d]
        linarith
      exact hx.2.trans hd_d0⟩
  have hbracket' :
      ∀ x ∈ Set.Icc c d,
        m ≤ |deriv g x| ∧ |deriv g x| ≤ 2 * m := by
    intro x hx
    exact hbracket x (hcd_sub hx)
  have hshort_for_rescale : d - c ≤ m / 50 := by
    rw [hcd_len]
    exact div_le_div_of_nonneg_right hm_low (by norm_num)
  have hcd_window : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1 :=
    fun _ hx => h_sub
      ⟨hc0.trans (hcd_sub hx).1, (hcd_sub hx).2.trans hd0⟩
  rcases slope_rescaling_to_centered_nonsingular g hg_norm hcd hm_pos
      hcd_window hbracket' hshort_for_rescale with
    ⟨f, hf, hf0, hformula⟩
  exact ⟨c, d, m, hc, hcd, hd, hm_pos, hm_low, hm_high, hcd_len,
    f, hf, hf0, hformula⟩

end Kakeya.Assouad
