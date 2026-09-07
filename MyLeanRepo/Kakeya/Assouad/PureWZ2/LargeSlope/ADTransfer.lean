import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# AD transfer under affine scalar maps

If `S ⊆ ℝ` satisfies `PureWZ2PaperADSet1 S delta alpha C` and `f(x) = a*x + b`
with `a > 0`, then `f '' S` satisfies `PureWZ2PaperADSet1 (f '' S) (a*delta) alpha C`.

This is the key lemma for transferring local AD through the anisotropic
rescaling: the exact projection identity gives an affine scalar map between
the original and rescaled projections.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- Covering number scales under Lipschitz maps.

If `f` is Lipschitz with constant `L`, then covering `f '' A` by balls of radius
`L*ε` is no harder than covering `A` by balls of radius `ε`. -/
lemma externalCoveringNumber_lipschitz_image
    {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {f : X → Y} {L : NNReal} (hL : LipschitzWith L f)
    {A : Set X} {ε : NNReal} :
    Metric.externalCoveringNumber (L * ε) (f '' A) ≤
    Metric.externalCoveringNumber ε A := by
  simp only [Metric.externalCoveringNumber, le_iInf_iff]
  intro C hC
  have h1 : IsCover (L * ε) (f '' A) (f '' C) :=
    IsCover.image_lipschitz hC hL
  have h4 : Metric.externalCoveringNumber (L * ε) (f '' A) ≤ (f '' C).encard :=
    IsCover.externalCoveringNumber_le_encard h1
  have h5 : (f '' C).encard ≤ C.encard := Set.encard_image_le f C
  exact h4.trans h5

/-- Covering number equality under positive affine scaling on ℝ.

If `f(x) = a*x + b` with `a > 0`, then
`externalCoveringNumber (a*ε) (f '' A) = externalCoveringNumber ε A`. -/
lemma externalCoveringNumber_affine_scaling
    {A : Set ℝ} {a b : ℝ} (ha : 0 < a) {ε : NNReal} :
    Metric.externalCoveringNumber ⟨a * (ε : ℝ), by positivity⟩ ((fun x : ℝ => a * x + b) '' A) =
    Metric.externalCoveringNumber ε A := by
  let f : ℝ → ℝ := fun x => a * x + b
  let g : ℝ → ℝ := fun y => (y - b) / a
  let aNN : NNReal := ⟨a, ha.le⟩
  let invANN : NNReal := ⟨1 / a, by positivity⟩
  have hfL : LipschitzWith aNN f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h : dist (f x) (f y) = a * dist x y := by
      simp only [f, dist_eq_norm, Real.norm_eq_abs]
      have h_eq : a * x + b - (a * y + b) = a * (x - y) := by ring
      rw [h_eq]
      have h' : |a * (x - y)| = a * |x - y| := by
        rw [abs_mul, abs_of_pos ha]
      exact h'
    rw [h] <;> rfl
  have hgL : LipschitzWith invANN g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h : dist (g x) (g y) = (1 / a) * dist x y := by
      simp only [g, dist_eq_norm, Real.norm_eq_abs]
      have h' : |(x - b) / a - (y - b) / a| = (1 / a) * |x - y| := by
        calc |(x - b) / a - (y - b) / a|
          = |(x - y) / a| := by rw [show (x - b) / a - (y - b) / a = (x - y) / a by ring]
        _ = |x - y| / |a| := by rw [abs_div]
        _ = |x - y| / a := by rw [abs_of_pos ha]
        _ = (1 / a) * |x - y| := by ring
      exact h'
    rw [h] <;> rfl
  have hfg : ∀ x, g (f x) = x := by
    intro x; simp [f, g]; field_simp [ha.ne'] <;> ring
  let ε' : NNReal := ⟨a * (ε : ℝ), by positivity⟩
  have h1 : Metric.externalCoveringNumber ε' (f '' A) ≤
      Metric.externalCoveringNumber ε A :=
    externalCoveringNumber_lipschitz_image (hL := hfL)
  have h2 : g '' (f '' A) = A := by
    rw [Set.image_image]
    ext x; simp [hfg] <;> tauto
  have h_mul : invANN * ε' = ε := by
    have h_coe : ((↑(invANN * ε') : ℝ)) = (↑ε : ℝ) := by
      have h : (↑(invANN * ε') : ℝ) = (↑invANN : ℝ) * (↑ε' : ℝ) := by
        exact NNReal.coe_mul invANN ε'
      rw [h]
      have h_inv : (↑invANN : ℝ) = 1 / a := by rfl
      have h_eps : (↑ε' : ℝ) = a * (↑ε : ℝ) := by rfl
      rw [h_inv, h_eps]
      <;> field_simp [ha.ne'] <;> ring
    exact_mod_cast h_coe
  have h3 : Metric.externalCoveringNumber ε A ≤
      Metric.externalCoveringNumber ε' (f '' A) := by
    have h4 := externalCoveringNumber_lipschitz_image (hL := hgL) (A := f '' A) (ε := ε')
    rw [h_mul] at h4
    rw [h2] at h4
    exact h4
  exact le_antisymm h1 h3

/-- Image of an interval under a positive affine map. -/
lemma image_affine_Icc {a b c d : ℝ} (ha : 0 < a) :
    (fun x : ℝ => a * x + b) '' Set.Icc c d =
    Set.Icc (a * c + b) (a * d + b) := by
  ext y
  simp only [Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨x, ⟨hxc, hxd⟩, rfl⟩
    constructor
    · have h : a * c + b ≤ a * x + b := by gcongr
      exact h
    · have h : a * x + b ≤ a * d + b := by gcongr
      exact h
  · rintro ⟨h1, h2⟩
    have h3 : c ≤ (y - b) / a := by
      have h4 : a * c ≤ y - b := by linarith
      have h5 : c ≤ (y - b) / a := by
        calc c = (a * c) / a := by field_simp [ha.ne'] <;> ring
          _ ≤ (y - b) / a := by gcongr
      exact h5
    have h4 : (y - b) / a ≤ d := by
      have h5 : y - b ≤ a * d := by linarith
      calc (y - b) / a
        ≤ (a * d) / a := by gcongr
      _ = d := by field_simp [ha.ne'] <;> ring
    refine ⟨(y - b) / a, ⟨h3, h4⟩, by field_simp [ha.ne'] <;> ring⟩

/-- AD transfers under positive affine scalar maps.

If `PureWZ2PaperADSet1 S delta alpha C` and `a > 0`, then
`PureWZ2PaperADSet1 ((fun x => a*x + b) '' S) (a*delta) alpha C`.

The scale parameter is multiplied by `a`; the exponent and constant are unchanged. -/
lemma PureWZ2PaperADSet1.affine_transfer
    {S : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 S delta alpha C)
    {a b : ℝ} (ha : 0 < a) :
    PureWZ2PaperADSet1 ((fun x : ℝ => a * x + b) '' S) (a * delta) alpha C := by
  have hdelta_pos : 0 < delta := hAD.1
  have halpha_pos : 0 < alpha := hAD.2.1
  have halpha_one : alpha ≤ 1 := hAD.2.2.1
  have hC_one : 1 ≤ C := hAD.2.2.2.1
  have hC_top : C ≠ ⊤ := hAD.2.2.2.2.1
  let f : ℝ → ℝ := fun x => a * x + b
  have hcover := hAD.2.2.2.2.2
  refine ⟨by positivity, halpha_pos, halpha_one, hC_one, hC_top, ?_⟩
  intro rho' hrho' hdelta_rho' left' length' hrho_length'
  have h_rho'_pos : 0 < rho' := by
    have h : 0 < a * delta := mul_pos ha hdelta_pos
    linarith
  set rho : ℝ := rho' / a with hrho_def
  have hrho_nonneg : 0 ≤ rho := by positivity
  have hdelta_rho : delta ≤ rho := by
    rw [hrho_def]
    have h : a * delta ≤ rho' := hdelta_rho'
    have h2 : delta ≤ rho' / a := by
      calc delta
        = (a * delta) / a := by field_simp [ha.ne'] <;> ring
      _ ≤ rho' / a := by gcongr
    exact h2
  set left : ℝ := (left' - b) / a with hleft_def
  set length : ℝ := length' / a with hlength_def
  have hrho_length : rho ≤ length := by
    rw [hrho_def, hlength_def] <;> gcongr
  have h_image_inter : f '' (S ∩ Set.Icc left (left + length)) =
      (f '' S) ∩ Set.Icc left' (left' + length') := by
    have h1 : f '' Set.Icc left (left + length) = Set.Icc left' (left' + length') := by
      rw [image_affine_Icc ha]
      have h_end1 : a * left + b = left' := by
        rw [hleft_def]
        <;> field_simp [ha.ne'] <;> ring
      have h_end2 : a * (left + length) + b = left' + length' := by
        rw [hleft_def, hlength_def]
        <;> field_simp [ha.ne'] <;> ring
      rw [h_end1, h_end2]
    have h_inj : Function.Injective f := fun x y h => by
      have h' : a * x + b = a * y + b := h
      have h'' : a * x = a * y := by linarith
      exact (mul_right_inj' ha.ne').mp h''
    have h2 : f '' (S ∩ Set.Icc left (left + length)) = (f '' S) ∩ f '' Set.Icc left (left + length) :=
      Set.image_inter h_inj
    rw [h2, h1]
  have h_cover : (↑(Metric.externalCoveringNumber ⟨rho, hrho_nonneg⟩
        (S ∩ Set.Icc left (left + length))) : ENNReal) ≤
      C * Kakeya.realRpowENN (length / rho) alpha :=
    hcover rho hrho_nonneg hdelta_rho left length hrho_length
  let rhoNN : NNReal := ⟨rho, hrho_nonneg⟩
  let rho'NN : NNReal := ⟨rho', hrho'⟩
  have h_scale : (⟨a * rho, by positivity⟩ : NNReal) = rho'NN := by
    apply Subtype.ext
    have h : a * rho = rho' := by
      rw [hrho_def]
      <;> field_simp [ha.ne'] <;> ring
    exact h
  have h_f_eq : f = (fun x : ℝ => a * x + b) := by rfl
  have h_main : (↑(Metric.externalCoveringNumber rho'NN
        ((f '' S) ∩ Set.Icc left' (left' + length'))) : ENNReal) =
      (↑(Metric.externalCoveringNumber rhoNN
        (S ∩ Set.Icc left (left + length))) : ENNReal) := by
    have h_goal : (f '' S) ∩ Set.Icc left' (left' + length') =
        (fun x : ℝ => a * x + b) '' (S ∩ Set.Icc left (left + length)) := by
      rw [h_f_eq]
      exact h_image_inter.symm
    rw [h_goal]
    have h_eq := externalCoveringNumber_affine_scaling
      (A := S ∩ Set.Icc left (left + length))
      (a := a) (b := b) (ha := ha) (ε := rhoNN)
    have h_rho_coe : (↑rhoNN : ℝ) = rho := by rfl
    have h_real_eq : a * (↑rhoNN : ℝ) = rho' := by
      calc a * (↑rhoNN : ℝ)
        = a * rho := by rw [h_rho_coe]
      _ = a * (rho' / a) := by rw [hrho_def]
      _ = rho' := by field_simp [ha.ne'] <;> ring
    have h_scale2 : (⟨a * (↑rhoNN : ℝ), by positivity⟩ : NNReal) = rho'NN := by
      exact Subtype.mk.congr_simp (a * ↑rhoNN) rho' h_real_eq
        (mul_nonneg (le_of_lt ha) (NNReal.coe_nonneg rhoNN))
    rw [h_scale2] at h_eq
    exact_mod_cast h_eq
  rw [h_main]
  have h_ratio : length / rho = length' / rho' := by
    rw [hlength_def, hrho_def]
    <;> field_simp [ha.ne'] <;> ring
  have h_cover' : (↑(Metric.externalCoveringNumber rhoNN
        (S ∩ Set.Icc left (left + length))) : ENNReal) ≤
      C * Kakeya.realRpowENN (length' / rho') alpha := by
    rw [←h_ratio]
    exact h_cover
  exact h_cover'

end Kakeya.Assouad

end
