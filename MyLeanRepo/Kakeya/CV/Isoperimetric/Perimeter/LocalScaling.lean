import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.PerimeterDefinition
import Mathlib.Tactic

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.Perimeter

variable {n : ℕ}

/-- Translation invariance of local perimeter:
`P(S + v; Ω + v) = P(S; Ω)`. -/
theorem perimeterIn_translation (S Ω : Set (E n)) (v : E n) :
    perimeterIn (translateSet S v) (translateSet Ω v) = perimeterIn S Ω := by
  let h_homeo : Homeomorph (E n) (E n) :=
    { toFun := fun x => x + v
      invFun := fun x => x - v
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have h_me : MeasurableEmbedding (fun x : E n => x + v) :=
    h_homeo.measurableEmbedding
  have h_mp : MeasurePreserving (fun x : E n => x + v) volume volume :=
    measurePreserving_add_right volume v
  have h1 : perimeterIn (translateSet S v) (translateSet Ω v) ≤ perimeterIn S Ω := by
    apply iSup_le
    intro Φ
    let Ψ : TestVectorField :=
      { toFun := fun x => Φ.val.toFun (x + v)
        smooth := Φ.val.smooth.comp (contDiff_id.add contDiff_const)
        compact := by
          have h_sub : Function.support (fun x : E n => Φ.val.toFun (x + v)) ⊆
              (fun x : E n => x - v) '' tsupport Φ.val.toFun := by
            intro x hx
            have h2 : x + v ∈ Function.support Φ.val.toFun := hx
            have h3 : x + v ∈ tsupport Φ.val.toFun := subset_tsupport (f := Φ.val.toFun) h2
            refine ⟨x + v, h3, ?_⟩
            simp
          have h_img_compact : IsCompact ((fun x : E n => x - v) '' tsupport Φ.val.toFun) :=
            Φ.val.compact.image (continuous_id.sub continuous_const)
          have h_closed : IsClosed ((fun x : E n => x - v) '' tsupport Φ.val.toFun) :=
            h_img_compact.isClosed
          have h_ts : tsupport (fun x : E n => Φ.val.toFun (x + v)) ⊆
              (fun x : E n => x - v) '' tsupport Φ.val.toFun :=
            closure_minimal h_sub h_closed
          exact h_img_compact.of_isClosed_subset (isClosed_tsupport _) h_ts
        bound := fun x => Φ.val.bound (x + v) }
    have hΨ_supp : Function.support Ψ.toFun ⊆ Ω := by
      intro x hx
      have h2 : x + v ∈ Function.support Φ.val.toFun := hx
      have h3 : x + v ∈ translateSet Ω v := Φ.property h2
      rcases h3 with ⟨w, hw, h_eq⟩
      have h4 : w + v = x + v := h_eq
      have h5 : x = w := by simpa using h4.symm
      rw [h5]; exact hw
    let Ψ' : {Ψ : TestVectorField // Function.support Ψ.toFun ⊆ Ω} := ⟨Ψ, hΨ_supp⟩
    have hdiv : divergence Ψ.toFun = fun x => divergence Φ.val.toFun (x + v) :=
      divergence_comp_translation Φ.val.smooth v
    have h_change : ∫ x in translateSet S v, divergence Φ.val.toFun x =
        ∫ x in S, divergence Ψ.toFun x := by
      have h : ∫ x in translateSet S v, divergence Φ.val.toFun x =
          ∫ x in S, divergence Φ.val.toFun (x + v) := by
        rw [show translateSet S v = (fun x : E n => x + v) '' S from rfl]
        exact h_mp.setIntegral_image_emb h_me (divergence Φ.val.toFun) S
      rw [h]
      have h2 : ∫ x in S, divergence Φ.val.toFun (x + v) = ∫ x in S, divergence Ψ.toFun x := by
        apply integral_congr_ae; exact ae_of_all _ (fun x => by rw [hdiv])
      exact h2
    rw [h_change]
    exact le_iSup (fun (θ : {Ψ : TestVectorField // Function.support Ψ.toFun ⊆ Ω}) =>
      ENNReal.ofReal |∫ x in S, divergence θ.val.toFun x|) Ψ'
  have h2 : perimeterIn S Ω ≤ perimeterIn (translateSet S v) (translateSet Ω v) := by
    apply iSup_le
    intro Ψ
    let Φ : TestVectorField :=
      { toFun := fun x => Ψ.val.toFun (x - v)
        smooth := Ψ.val.smooth.comp (contDiff_id.sub contDiff_const)
        compact := by
          have h_sub : Function.support (fun x : E n => Ψ.val.toFun (x - v)) ⊆
              (fun x : E n => x + v) '' tsupport Ψ.val.toFun := by
            intro x hx
            have h2 : x - v ∈ Function.support Ψ.val.toFun := hx
            have h3 : x - v ∈ tsupport Ψ.val.toFun := subset_tsupport (f := Ψ.val.toFun) h2
            refine ⟨x - v, h3, ?_⟩
            simp
          have h_img_compact : IsCompact ((fun x : E n => x + v) '' tsupport Ψ.val.toFun) :=
            Ψ.val.compact.image (continuous_id.add continuous_const)
          have h_closed : IsClosed ((fun x : E n => x + v) '' tsupport Ψ.val.toFun) :=
            h_img_compact.isClosed
          have h_ts : tsupport (fun x : E n => Ψ.val.toFun (x - v)) ⊆
              (fun x : E n => x + v) '' tsupport Ψ.val.toFun :=
            closure_minimal h_sub h_closed
          exact h_img_compact.of_isClosed_subset (isClosed_tsupport _) h_ts
        bound := fun x => Ψ.val.bound (x - v) }
    have hΦ_supp : Function.support Φ.toFun ⊆ translateSet Ω v := by
      intro x hx
      have h2 : x - v ∈ Function.support Ψ.val.toFun := hx
      have h3 : x - v ∈ Ω := Ψ.property h2
      exact ⟨x - v, h3, by simp⟩
    let Φ' : {Φ : TestVectorField // Function.support Φ.toFun ⊆ translateSet Ω v} := ⟨Φ, hΦ_supp⟩
    have hdiv : divergence Φ.toFun = fun x => divergence Ψ.val.toFun (x - v) := by
      have h_eq1 : Φ.toFun = (fun x : E n => Ψ.val.toFun (x + (-v))) := by
        funext x; simp [Φ, sub_eq_add_neg]
      rw [h_eq1]
      have h := divergence_comp_translation Ψ.val.smooth (-v)
      simpa [sub_eq_add_neg] using h
    have h_change : ∫ x in S, divergence Ψ.val.toFun x =
        ∫ x in translateSet S v, divergence Φ.toFun x := by
      have h : ∫ x in translateSet S v, divergence Φ.toFun x =
          ∫ x in S, divergence Φ.toFun (x + v) := by
        rw [show translateSet S v = (fun x : E n => x + v) '' S from rfl]
        exact h_mp.setIntegral_image_emb h_me (divergence Φ.toFun) S
      have h2 : ∫ x in S, divergence Φ.toFun (x + v) = ∫ x in S, divergence Ψ.val.toFun x := by
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by rw [hdiv] <;> simp)
      rw [h, h2]
    rw [h_change]
    exact le_iSup (fun (θ : {Φ : TestVectorField // Function.support Φ.toFun ⊆ translateSet Ω v}) =>
      ENNReal.ofReal |∫ x in translateSet S v, divergence θ.val.toFun x|) Φ'
  exact le_antisymm h1 h2

/-- Local perimeter scales as `t^(n-1)`:
`P(t • S; t • Ω) = t^(n-1) · P(S; Ω)`. -/
theorem perimeterIn_scaling (S Ω : Set (E n)) (hS : MeasurableSet S)
    {t : ℝ} (ht : 0 < t) (hn : 1 ≤ n) :
    perimeterIn (scaleSet t S) (scaleSet t Ω) =
      (ENNReal.ofReal (t ^ (n - 1))) * perimeterIn S Ω := by
  have hfinrank : Module.finrank ℝ (E n) = n := by simp
  have ht_ne : t ≠ 0 := ht.ne'
  have h_pow : t ^ n = t * t ^ (n - 1) := by
    cases n with
    | zero => contradiction
    | succ n' => simp [pow_succ] <;> ring
  let hmap_inv : E n → E n := fun x => t⁻¹ • x
  let hmap_fwd : E n → E n := fun x => t • x

  have h_compact_scaled : ∀ (Φ : TestVectorField),
      Function.support Φ.toFun ⊆ scaleSet t Ω →
      HasCompactSupport (fun x : E n => Φ.toFun (t • x)) := by
    intro Φ hΦ
    have h_sub : Function.support (fun x : E n => Φ.toFun (t • x)) ⊆
        hmap_inv '' tsupport Φ.toFun := by
      intro x hx
      have h1 : t • x ∈ Function.support Φ.toFun := hx
      have h2 : t • x ∈ tsupport Φ.toFun := subset_tsupport (f := Φ.toFun) h1
      refine ⟨t • x, h2, ?_⟩
      have h3 : hmap_inv (t • x) = x := by
        simp [hmap_inv, smul_smul] <;> field_simp [ht_ne] <;> simp [one_smul]
      exact h3
    have h_img_compact : IsCompact (hmap_inv '' tsupport Φ.toFun) :=
      Φ.compact.image (continuous_id.const_smul (t⁻¹))
    have h_closed : IsClosed (hmap_inv '' tsupport Φ.toFun) := h_img_compact.isClosed
    have h_ts : tsupport (fun x : E n => Φ.toFun (t • x)) ⊆ hmap_inv '' tsupport Φ.toFun :=
      closure_minimal h_sub h_closed
    exact h_img_compact.of_isClosed_subset (isClosed_tsupport _) h_ts

  have h_compact_unscaled : ∀ (Ψ : TestVectorField),
      Function.support Ψ.toFun ⊆ Ω →
      HasCompactSupport (fun x : E n => Ψ.toFun (t⁻¹ • x)) := by
    intro Ψ hΨ
    have h_sub : Function.support (fun x : E n => Ψ.toFun (t⁻¹ • x)) ⊆
        hmap_fwd '' tsupport Ψ.toFun := by
      intro x hx
      have h1 : t⁻¹ • x ∈ Function.support Ψ.toFun := hx
      have h2 : t⁻¹ • x ∈ tsupport Ψ.toFun := subset_tsupport (f := Ψ.toFun) h1
      refine ⟨t⁻¹ • x, h2, ?_⟩
      have h3 : hmap_fwd (t⁻¹ • x) = x := by
        simp [hmap_fwd, smul_smul] <;> field_simp [ht_ne] <;> simp [one_smul]
      exact h3
    have h_img_compact : IsCompact (hmap_fwd '' tsupport Ψ.toFun) :=
      Ψ.compact.image (continuous_id.const_smul t)
    have h_closed : IsClosed (hmap_fwd '' tsupport Ψ.toFun) := h_img_compact.isClosed
    have h_ts : tsupport (fun x : E n => Ψ.toFun (t⁻¹ • x)) ⊆ hmap_fwd '' tsupport Ψ.toFun :=
      closure_minimal h_sub h_closed
    exact h_img_compact.of_isClosed_subset (isClosed_tsupport _) h_ts

  have h1 : perimeterIn (scaleSet t S) (scaleSet t Ω) ≤
      (ENNReal.ofReal (t ^ (n - 1))) * perimeterIn S Ω := by
    apply iSup_le
    intro Φ
    have hΦ_supp : Function.support Φ.val.toFun ⊆ scaleSet t Ω := Φ.property
    let Ψ : TestVectorField :=
      { toFun := fun x => Φ.val.toFun (t • x)
        smooth := Φ.val.smooth.comp (contDiff_id.const_smul t)
        compact := h_compact_scaled Φ.val hΦ_supp
        bound := fun x => Φ.val.bound (t • x) }
    have hΨ_supp : Function.support Ψ.toFun ⊆ Ω := by
      intro x hx
      have h2 : t • x ∈ Function.support Φ.val.toFun := hx
      have h3 : t • x ∈ scaleSet t Ω := hΦ_supp h2
      rcases h3 with ⟨w, hw, h_eq⟩
      have h4 : t • w = t • x := h_eq
      have h5 : x = w := by
        have h_inj : t • w = t • x → w = x := by
          intro h
          have h' : t⁻¹ • (t • w) = t⁻¹ • (t • x) := by rw [h]
          simpa [smul_smul, ht_ne] using h'
        exact (h_inj h4).symm
      rw [h5]; exact hw
    let Ψ' : {Ψ : TestVectorField // Function.support Ψ.toFun ⊆ Ω} := ⟨Ψ, hΨ_supp⟩
    have hdiv : divergence Ψ.toFun = fun x => t * divergence Φ.val.toFun (t • x) :=
      divergence_comp_smul Φ.val.smooth ht_ne
    have h_change : ∫ x in scaleSet t S, divergence Φ.val.toFun x =
        (t ^ (n - 1)) * (∫ x in S, divergence Ψ.toFun x) := by
      have h : ∫ x in S, divergence Φ.val.toFun (t • x) =
          (t ^ n)⁻¹ * ∫ x in scaleSet t S, divergence Φ.val.toFun x := by
        rw [MeasureTheory.Measure.setIntegral_comp_smul volume (divergence Φ.val.toFun) S ht_ne]
        rw [hfinrank]
        have h_abs : |(t ^ n)⁻¹| = (t ^ n)⁻¹ := by
          rw [abs_of_nonneg] <;> positivity
        rw [h_abs] <;> rfl
      have h' : ∫ x in scaleSet t S, divergence Φ.val.toFun x =
          (t ^ n) * ∫ x in S, divergence Φ.val.toFun (t • x) := by
        rw [h] <;> field_simp [ht_ne] <;> ring
      have h2 : ∫ x in S, divergence Ψ.toFun x = ∫ x in S, t * divergence Φ.val.toFun (t • x) := by
        rw [hdiv] <;> rfl
      rw [h', h2, integral_const_mul, h_pow] <;> ring
    rw [h_change]
    have h_abs : |t ^ (n - 1) * ∫ x in S, divergence Ψ.toFun x| =
        t ^ (n - 1) * |∫ x in S, divergence Ψ.toFun x| := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
    have h3 : ENNReal.ofReal |t ^ (n - 1) * ∫ x in S, divergence Ψ.toFun x| =
        ENNReal.ofReal (t ^ (n - 1)) * ENNReal.ofReal |∫ x in S, divergence Ψ.toFun x| := by
      rw [h_abs, ← ENNReal.ofReal_mul (by positivity)] <;> simp
    rw [h3]
    exact mul_le_mul_of_nonneg_left
      (le_iSup (fun (θ : {Ψ : TestVectorField // Function.support Ψ.toFun ⊆ Ω}) =>
        ENNReal.ofReal |∫ x in S, divergence θ.val.toFun x|) Ψ')
      (by positivity)

  have h2 : (ENNReal.ofReal (t ^ (n - 1))) * perimeterIn S Ω ≤
      perimeterIn (scaleSet t S) (scaleSet t Ω) := by
    have h_iSup : (ENNReal.ofReal (t ^ (n - 1))) * perimeterIn S Ω =
        iSup fun (Ψ : {Ψ : TestVectorField // Function.support Ψ.toFun ⊆ Ω}) =>
          ENNReal.ofReal (t ^ (n - 1)) * ENNReal.ofReal |∫ x in S, divergence Ψ.val.toFun x| := by
      rw [perimeterIn, ENNReal.mul_iSup] <;> rfl
    rw [h_iSup]
    apply iSup_le
    intro Ψ
    have hΨ_supp : Function.support Ψ.val.toFun ⊆ Ω := Ψ.property
    let Φ : TestVectorField :=
      { toFun := fun x => Ψ.val.toFun (t⁻¹ • x)
        smooth := Ψ.val.smooth.comp (contDiff_id.const_smul t⁻¹)
        compact := h_compact_unscaled Ψ.val hΨ_supp
        bound := fun x => Ψ.val.bound (t⁻¹ • x) }
    have hΦ_supp : Function.support Φ.toFun ⊆ scaleSet t Ω := by
      intro x hx
      have h2 : t⁻¹ • x ∈ Function.support Ψ.val.toFun := hx
      have h3 : t⁻¹ • x ∈ Ω := Ψ.property h2
      exact ⟨t⁻¹ • x, h3, by simp [hmap_fwd, smul_smul] <;> field_simp [ht_ne] <;> simp [one_smul]⟩
    let Φ' : {Φ : TestVectorField // Function.support Φ.toFun ⊆ scaleSet t Ω} := ⟨Φ, hΦ_supp⟩
    have hdiv : divergence Φ.toFun = fun x => t⁻¹ * divergence Ψ.val.toFun (t⁻¹ • x) :=
      divergence_comp_smul Ψ.val.smooth (inv_ne_zero ht_ne)
    have h_change : ∫ x in scaleSet t S, divergence Φ.toFun x =
        (t ^ (n - 1)) * (∫ x in S, divergence Ψ.val.toFun x) := by
      have h : ∫ x in S, divergence Φ.toFun (t • x) =
          (t ^ n)⁻¹ * ∫ x in scaleSet t S, divergence Φ.toFun x := by
        rw [MeasureTheory.Measure.setIntegral_comp_smul volume (divergence Φ.toFun) S ht_ne]
        rw [hfinrank]
        have h_abs : |(t ^ n)⁻¹| = (t ^ n)⁻¹ := by
          rw [abs_of_nonneg] <;> positivity
        rw [h_abs] <;> rfl
      have h' : ∫ x in scaleSet t S, divergence Φ.toFun x =
          (t ^ n) * ∫ x in S, divergence Φ.toFun (t • x) := by
        rw [h] <;> field_simp [ht_ne] <;> ring
      have h3 : ∀ x, divergence Φ.toFun (t • x) = t⁻¹ * divergence Ψ.val.toFun x := by
        intro x
        have h4 : divergence Φ.toFun (t • x) = t⁻¹ * divergence Ψ.val.toFun (t⁻¹ • (t • x)) := by
          rw [hdiv] <;> rfl
        rw [h4]
        have h5 : t⁻¹ • (t • x) = x := by
          simp [smul_smul] <;> field_simp [ht_ne] <;> simp [one_smul]
        rw [h5]
      have h4int : ∫ x in S, divergence Φ.toFun (t • x) = t⁻¹ * ∫ x in S, divergence Ψ.val.toFun x := by
        have h41 : ∀ x, divergence Φ.toFun (t • x) = t⁻¹ * divergence Ψ.val.toFun x := h3
        have h : ∫ x in S, divergence Φ.toFun (t • x) = ∫ x in S, t⁻¹ * divergence Ψ.val.toFun x := by
          apply integral_congr_ae; exact ae_of_all _ h41
        rw [h, integral_const_mul]
      rw [h', h4int]
      have h : t ^ n * (t⁻¹ * ∫ x in S, divergence Ψ.val.toFun x) =
          (t ^ (n - 1)) * (∫ x in S, divergence Ψ.val.toFun x) := by
        calc
          t ^ n * (t⁻¹ * ∫ x in S, divergence Ψ.val.toFun x)
            = (t ^ n * t⁻¹) * ∫ x in S, divergence Ψ.val.toFun x := by ring
          _ = (t * t ^ (n - 1)) * t⁻¹ * ∫ x in S, divergence Ψ.val.toFun x := by rw [h_pow]
          _ = t ^ (n - 1) * (t * t⁻¹) * ∫ x in S, divergence Ψ.val.toFun x := by ring
          _ = t ^ (n - 1) * ∫ x in S, divergence Ψ.val.toFun x := by
            have h_t : t * t⁻¹ = 1 := by field_simp [ht_ne]
            rw [h_t] <;> ring
      exact h
    have h_abs2 : |(t ^ (n - 1)) * (∫ x in S, divergence Ψ.val.toFun x)| =
        (t ^ (n - 1)) * |∫ x in S, divergence Ψ.val.toFun x| := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
    have h5 : ENNReal.ofReal (t ^ (n - 1)) * ENNReal.ofReal |∫ x in S, divergence Ψ.val.toFun x| =
        ENNReal.ofReal |∫ x in scaleSet t S, divergence Φ.toFun x| := by
      have h6 : ENNReal.ofReal (t ^ (n - 1)) * ENNReal.ofReal |∫ x in S, divergence Ψ.val.toFun x| =
          ENNReal.ofReal ((t ^ (n - 1)) * |∫ x in S, divergence Ψ.val.toFun x|) := by
        rw [← ENNReal.ofReal_mul (by positivity)] <;> simp
      rw [h6]
      have h7 : (t ^ (n - 1)) * |∫ x in S, divergence Ψ.val.toFun x| =
          |(t ^ (n - 1)) * (∫ x in S, divergence Ψ.val.toFun x)| := by rw [h_abs2]
      rw [h7, h_change]
    rw [h5]
    exact le_iSup (fun (θ : {Φ : TestVectorField // Function.support Φ.toFun ⊆ scaleSet t Ω}) =>
      ENNReal.ofReal |∫ x in scaleSet t S, divergence θ.val.toFun x|) Φ'
  exact le_antisymm h1 h2

end Geometry.Perimeter
