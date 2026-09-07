module

public import MyLeanRepo.AllScaleFrostman
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ENNReal Set Classical
open scoped Pointwise

namespace WeakTwoEndsSumProduct

variable {d : ℕ}

/-- Spherical measure of the belt `{θ ∈ S^{d-1} : |θ·v| < t}` is at most
`d * volume(strip)`, where the strip is `{x | |x·v| < t, ‖x‖ < 1}`. -/
lemma belt_spherical_measure_le_cone_volume {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht : 0 ≤ t)
    (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) :
    volume.toSphere {θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 |
      |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v| < t} ≤
    (↑d : ENNReal) * volume {x : EuclideanSpace ℝ (Fin d) | |inner ℝ x v| < t ∧ ‖x‖ < 1} := by
  let E : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    {θ | |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v| < t}
  have h_cont : Continuous (fun (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) =>
      inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v) :=
    Continuous.inner (continuous_subtype_val) continuous_const
  have h_cont_abs : Continuous (fun (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) =>
      |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v|) :=
    Continuous.abs h_cont
  have hE_meas : MeasurableSet E := by
    have h1 : E = (fun (θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) =>
        |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v|) ⁻¹' (Set.Iio t) := by
      ext θ
      simp [E, Set.mem_preimage] <;> rfl
    rw [h1]
    exact h_cont_abs.isOpen_preimage _ isOpen_Iio |>.measurableSet
  let cone : Set (EuclideanSpace ℝ (Fin d)) :=
    Set.image2 (· • ·) (Set.Ioo (0 : ℝ) 1) ((↑) '' E)
  let strip : Set (EuclideanSpace ℝ (Fin d)) :=
    {x | |inner ℝ x v| < t ∧ ‖x‖ < 1}
  have h1 : cone ⊆ strip := by
    intro x hx
    rcases Set.mem_image2.mp hx with ⟨r, hr, y, hy, rfl⟩
    rcases hy with ⟨θ, hθ, rfl⟩
    have h2 : 0 < r := hr.1
    have h3 : r < 1 := hr.2
    have h4 : |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v| < t := hθ
    have h5 : |inner ℝ (r • (θ : EuclideanSpace ℝ (Fin d))) v| =
        r * |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v| := by
      have h6 : inner ℝ (r • (θ : EuclideanSpace ℝ (Fin d))) v =
          r * inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v := by
        simp [inner_smul_left] <;> ring
      rw [h6]
      have h7 : |r * inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v| =
          |r| * |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v| := by exact abs_mul r (inner ℝ (↑θ) v)
      rw [h7]
      have h8 : |r| = r := abs_of_pos h2
      rw [h8] <;> ring
    have h7 : ‖(θ : EuclideanSpace ℝ (Fin d))‖ = 1 := by
      have h71 : dist (θ : EuclideanSpace ℝ (Fin d)) 0 = 1 := Metric.mem_sphere.mp θ.prop
      simpa [dist_zero_right] using h71
    have h8 : ‖r • (θ : EuclideanSpace ℝ (Fin d))‖ = r := by
      have h91 : ‖r • (θ : EuclideanSpace ℝ (Fin d))‖ = |r| * ‖(θ : EuclideanSpace ℝ (Fin d))‖ := norm_smul r (θ : EuclideanSpace ℝ (Fin d))
      rw [h91, h7]
      have h92 : |r| = r := abs_of_pos h2
      rw [h92] <;> ring
    have h9 : r * |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v| < t := by
      calc r * |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v|
        < r * t := mul_lt_mul_of_pos_left h4 h2
      _ ≤ t := by nlinarith
    constructor
    · rw [h5] <;> exact h9
    · rw [h8] <;> exact h3
  have h2 : volume cone ≤ volume strip := measure_mono h1
  have h_finrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
  have h3 : volume.toSphere E = (↑d : ENNReal) * volume cone := by
    have h4 : volume.toSphere E = (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ENNReal) * volume cone :=
      MeasureTheory.Measure.toSphere_apply' volume hE_meas
    rw [h4, h_finrank] <;> norm_cast
  rw [h3]
  gcongr



/-- Volume of the strip `{x ∈ B^d : |x·v| < t}` is at most `2t * volume(B^{d-1})`. -/
lemma strip_volume_bound {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht : 0 ≤ t)
    (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) :
    volume {x : EuclideanSpace ℝ (Fin d) | |inner ℝ x v| < t ∧ ‖x‖ < 1} ≤
    ENNReal.ofReal (2 * t) *
      volume (Metric.ball (0 : {x : EuclideanSpace ℝ (Fin d) // x ∈ (Submodule.span ℝ {v})ᗮ}) 1) := by
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := Submodule.span ℝ {v}
  let Kperp : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := Kᗮ
  let e : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] WithLp 2 (K × Kperp) := K.orthogonalDecomposition
  let ofLpEquiv : WithLp 2 (K × Kperp) ≃ₗ[ℝ] K × Kperp := WithLp.linearEquiv 2 ℝ (K × Kperp)
  have h_ofLp_cont : Continuous ofLpEquiv := by exact continuous_iff_le_induced.mpr fun U a => a
  have h_ofLp_symm_cont : Continuous ofLpEquiv.symm := by exact LinearEquiv.continuous_symm ofLpEquiv h_ofLp_cont
  let ofLpME : WithLp 2 (K × Kperp) ≃ᵐ K × Kperp :=
    ⟨ofLpEquiv.toEquiv, h_ofLp_cont.measurable, h_ofLp_symm_cont.measurable⟩
  let gEquiv : EuclideanSpace ℝ (Fin d) ≃ᵐ K × Kperp :=
    e.toMeasurableEquiv.trans ofLpME

  let strip : Set (EuclideanSpace ℝ (Fin d)) := {x | |inner ℝ x v| < t ∧ ‖x‖ < 1}
  let setK : Set K := {a | ‖a‖ < t}
  let setKperp : Set Kperp := Metric.ball 0 1
  let target : Set (K × Kperp) := setK ×ˢ setKperp

  have h_strip_open : IsOpen strip := by
    have h1 : Continuous (fun x : EuclideanSpace ℝ (Fin d) => |inner ℝ x v|) := by fun_prop
    exact h1.isOpen_preimage (Set.Iio t) isOpen_Iio |>.inter
      (continuous_norm.isOpen_preimage (Set.Iio 1) isOpen_Iio)
  have h_strip_meas : MeasurableSet strip := h_strip_open.measurableSet

  have h_mp_g : MeasurePreserving gEquiv volume volume := by
    convert (WithLp.volume_preserving_ofLp (U := K) (V := Kperp)).comp e.measurePreserving
    <;> rfl

  have h_image_subset : gEquiv '' strip ⊆ target := by
    intro p hp
    have h_exists : ∃ (x : EuclideanSpace ℝ (Fin d)), x ∈ strip ∧ gEquiv x = p := by
      simpa [Set.mem_image] using hp
    rcases h_exists with ⟨x, hx, rfl⟩
    have h_inner : |inner ℝ x v| < t := hx.1
    have h_x_norm : ‖x‖ < 1 := hx.2
    have h_gx : gEquiv x = ofLpEquiv (e x) := by
      exact DFunLike.congr_arg gEquiv rfl
    have h_fst : (gEquiv x).1 = K.orthogonalProjectionOnto x := by
      rw [h_gx]
      have h : (ofLpEquiv (e x)).1 = (e x).fst := by rfl
      rw [h, Submodule.fst_orthogonalDecomposition_apply K x]
    have h_snd : (gEquiv x).2 = Kperp.orthogonalProjectionOnto x := by
      rw [h_gx]
      have h : (ofLpEquiv (e x)).2 = (e x).snd := by rfl
      rw [h, Submodule.snd_orthogonalDecomposition_apply K x]
    have h_proj : (K.orthogonalProjectionOnto x : EuclideanSpace ℝ (Fin d)) = inner ℝ x v • v := by
      have h1 : (K.orthogonalProjectionOnto x : EuclideanSpace ℝ (Fin d)) = K.starProjection x :=
        Submodule.coe_orthogonalProjectionOnto_apply K x
      rw [h1, Submodule.starProjection_unit_singleton ℝ hv x]
      have h3 : inner ℝ v x = inner ℝ x v := by exact real_inner_comm x v
      rw [h3]
    have h_norm_fst : ‖(gEquiv x).1‖ < t := by
      rw [h_fst]
      have h4 : ‖(K.orthogonalProjectionOnto x : EuclideanSpace ℝ (Fin d))‖ = |inner ℝ x v| := by
        rw [h_proj]
        have h41 : ‖(inner ℝ x v) • v‖ = |inner ℝ x v| * ‖v‖ := norm_smul (inner ℝ x v) v
        rw [h41, hv] <;> ring
      have h5 : ‖K.orthogonalProjectionOnto x‖ = ‖(K.orthogonalProjectionOnto x : EuclideanSpace ℝ (Fin d))‖ := by rfl
      rw [h5, h4] <;> exact h_inner
    have h_sum : ‖x‖ ^ 2 = ‖K.orthogonalProjectionOnto x‖ ^ 2 + ‖Kperp.orthogonalProjectionOnto x‖ ^ 2 :=
      K.norm_sq_eq_add_norm_sq_projection x
    have h_norm_snd : ‖(gEquiv x).2‖ < 1 := by
      rw [h_snd]
      have h_pos1_sq : 0 ≤ ‖K.orthogonalProjectionOnto x‖ ^ 2 := by positivity
      have h9 : ‖Kperp.orthogonalProjectionOnto x‖ ^ 2 ≤ ‖x‖ ^ 2 := by linarith [h_sum, h_pos1_sq]
      have h_pos2 : 0 ≤ ‖Kperp.orthogonalProjectionOnto x‖ := by positivity
      have h10 : ‖x‖ ^ 2 < 1 := by
        have h11 : 0 ≤ ‖x‖ := by positivity
        nlinarith [h_x_norm]
      nlinarith
    have h_goal1 : (gEquiv x).1 ∈ setK := by
      simpa [setK] using h_norm_fst
    have h_goal2 : (gEquiv x).2 ∈ setKperp := by
      simpa [setKperp, Metric.mem_ball] using h_norm_snd
    exact ⟨h_goal1, h_goal2⟩

  have h1 : volume (gEquiv '' strip) = volume strip := by
    have h_map : Measure.map gEquiv volume = volume := by exact h_mp_g.map_eq
    have h2 : MeasurableSet (gEquiv '' strip) := by
      have h_eq : gEquiv '' strip = gEquiv.symm ⁻¹' strip := by
        ext y
        simp only [Set.mem_image, Set.mem_preimage]
        constructor
        · rintro ⟨x, hx, rfl⟩
          simpa [gEquiv.apply_symm_apply] using hx
        · intro hy
          refine ⟨gEquiv.symm y, hy, ?_⟩
          simp
      rw [h_eq]
      exact h_strip_meas.preimage gEquiv.symm.measurable
    have h3 : (Measure.map gEquiv volume) (gEquiv '' strip) = volume (gEquiv ⁻¹' (gEquiv '' strip)) :=
      Measure.map_apply gEquiv.measurable h2
    have h4 : gEquiv ⁻¹' (gEquiv '' strip) = strip := Set.preimage_image_eq _ gEquiv.injective
    rw [h_map] at h3
    rw [h3, h4]

  have h2 : volume (gEquiv '' strip) ≤ volume target := measure_mono h_image_subset

  have h_setK_open : IsOpen setK := continuous_norm.isOpen_preimage (Set.Iio t) isOpen_Iio
  have h_setK_meas : MeasurableSet setK := h_setK_open.measurableSet
  have h_prod : volume target = volume setK * volume setKperp := by
    rw [MeasureTheory.Measure.volume_eq_prod K Kperp]
    exact Measure.prod_prod setK setKperp

  let eK : ℝ ≃ₗᵢ[ℝ] K := LinearIsometryEquiv.toSpanUnitSingleton v hv
  have h_mp_eK : MeasurePreserving eK volume volume := eK.measurePreserving

  have h_eK_apply : ∀ (c : ℝ), (eK c : EuclideanSpace ℝ (Fin d)) = c • v := by
    intro c
    have h : eK c = ⟨c • v, _⟩ := LinearIsometryEquiv.toSpanUnitSingleton_apply v hv c
    have h' : (eK c : EuclideanSpace ℝ (Fin d)) = c • v := by
      calc
        (eK c : EuclideanSpace ℝ (Fin d))
          = ((⟨c • v, _⟩ : K) : EuclideanSpace ℝ (Fin d)) := by rw [h]
        _ = c • v := by exact Subtype.coe_mk (c • v) _
    exact h'

  have h_setK_preimage : eK ⁻¹' setK = Set.Ioo (-t) t := by
    ext c
    simp only [setK, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ioo]
    have h_norm : ‖eK c‖ = |c| := by
      have h : ‖(eK c : EuclideanSpace ℝ (Fin d))‖ = |c| := by
        have h_eq : (eK c : EuclideanSpace ℝ (Fin d)) = c • v := h_eK_apply c
        rw [h_eq]
        have h2 : ‖c • v‖ = |c| * ‖v‖ := by
          have h21 : ‖c • v‖ = ‖c‖ * ‖v‖ := norm_smul c v
          have h22 : ‖c‖ = |c| := by exact Real.norm_eq_abs c
          rw [h21, h22]
        rw [h2, hv]
        <;> ring
      have h5 : ‖eK c‖ = ‖(eK c : EuclideanSpace ℝ (Fin d))‖ := by rfl
      rw [h5, h]
    rw [h_norm]
    constructor
    · intro h
      have h5 : |c| < t := h
      have h6 : -t < c := by linarith [abs_lt.mp h5]
      have h7 : c < t := by linarith [abs_lt.mp h5]
      exact ⟨h6, h7⟩
    · rintro ⟨h1, h2⟩
      have h5 : |c| < t := by
        rw [abs_lt] <;> exact ⟨by linarith, by linarith⟩
      exact h5

  have hK : volume setK = ENNReal.ofReal (2 * t) := by
    have h_map : Measure.map eK volume = volume := by exact h_mp_eK.map_eq
    have h_apply : (Measure.map eK volume) setK = volume (eK ⁻¹' setK) :=
      Measure.map_apply eK.continuous.measurable h_setK_meas
    have h7 : volume setK = volume (eK ⁻¹' setK) := by
      rw [h_map] at h_apply
      exact h_apply
    rw [h7, h_setK_preimage, Real.volume_Ioo]
    <;> ring_nf <;> norm_cast

  calc volume strip
    = volume (gEquiv '' strip) := h1.symm
  _ ≤ volume target := h2
  _ = volume setK * volume setKperp := h_prod
  _ = ENNReal.ofReal (2 * t) * volume setKperp := by rw [hK]
  _ = ENNReal.ofReal (2 * t) * volume (Metric.ball (0 : Kperp) 1) := by rfl

/-- Combined belt measure bound. -/
lemma belt_spherical_measure_bound {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht : 0 ≤ t)
    (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) :
    volume.toSphere {θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 |
      |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v| < t} ≤
    (↑d : ENNReal) * ENNReal.ofReal (2 * t) *
      volume (Metric.ball (0 : {x : EuclideanSpace ℝ (Fin d) // x ∈ (Submodule.span ℝ {v})ᗮ}) 1) := by
  have h1 := belt_spherical_measure_le_cone_volume hd ht v hv
  have h2 := strip_volume_bound hd ht v hv
  calc volume.toSphere _
    ≤ (↑d : ENNReal) * volume {x : EuclideanSpace ℝ (Fin d) | |inner ℝ x v| < t ∧ ‖x‖ < 1} := h1
  _ ≤ (↑d : ENNReal) * (ENNReal.ofReal (2 * t) * volume (Metric.ball (0 : {x : EuclideanSpace ℝ (Fin d) // x ∈ (Submodule.span ℝ {v})ᗮ}) 1)) :=
      mul_le_mul_left' h2 _
  _ = (↑d : ENNReal) * ENNReal.ofReal (2 * t) * volume (Metric.ball (0 : {x : EuclideanSpace ℝ (Fin d) // x ∈ (Submodule.span ℝ {v})ᗮ}) 1) := by
      rw [mul_assoc]

end WeakTwoEndsSumProduct
