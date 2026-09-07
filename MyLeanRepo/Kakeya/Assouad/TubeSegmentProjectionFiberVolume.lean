import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling

/-! WZ Lemma 30: volume captured by one scalar projection ball.

## Proof sketch

Rotate via a reflection so the tube axis aligns with the first coordinate
axis.  The scalar-projection direction `v` rotates to `v'`, whose first
coordinate has absolute value `tau = |inner direction v|`.  A point in the
`delta`-tube whose projection lies within `rho` of `c` has its axial
coordinate confined to an interval of length at most
`2 * (rho + delta) / tau + 2 * delta`, while the two transverse coordinates
each vary by at most `2 * delta`.  The resulting box has volume
`8 * delta^2 * ((rho + delta) / tau + delta)`, which is bounded by
`1000 * delta^2 * rho / tau` using `delta ≤ rho` and `tau ≤ 1`.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Assouad

private lemma IsometryEquiv.cthickening_image {α β : Type*}
    [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    (e : α ≃ᵢ β) (delta : ℝ) (s : Set α) :
    e '' Metric.cthickening delta s =
      Metric.cthickening delta (e '' s) := by
  ext y
  simp only [Metric.mem_cthickening_iff, Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Metric.infEDist_image e.isometry]
    exact hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    have himage : e.symm '' (e '' s) = s := by
      rw [← Set.image_comp]
      simp
    have hdist := Metric.infEDist_image e.symm.isometry
      (x := y) (t := e '' s)
    rw [himage] at hdist
    rw [hdist]
    exact hy

private lemma volume_box3 (lo hi : Fin 3 → ℝ) (hlohi : ∀ i, lo i ≤ hi i) :
    volume ((WithLp.toLp 2) '' Set.Icc lo hi) =
      ENNReal.ofReal ((hi 0 - lo 0) * (hi 1 - lo 1) * (hi 2 - lo 2)) := by
  let toLp : (Fin 3 → ℝ) → Point3 := WithLp.toLp 2
  have hpreserving : MeasurePreserving toLp volume volume :=
    PiLp.volume_preserving_toLp (ι := Fin 3)
  have hinjective : Function.Injective toLp := by
    intro x y hxy
    simpa [toLp, WithLp.toLp_injective] using hxy
  have hcontinuous : Continuous toLp :=
    PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)
  have himage_measurable : MeasurableSet (toLp '' Set.Icc lo hi) := by
    have himage : toLp '' Set.Icc lo hi =
        (fun x : Point3 => x.ofLp) ⁻¹' Set.Icc lo hi := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [WithLp.ofLp_toLp] using hx
      · intro hy
        exact ⟨y.ofLp, hy, WithLp.toLp_ofLp (2 : ENNReal) y⟩
    rw [himage]
    exact (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable
      measurableSet_Icc
  have hvolume : volume (toLp '' Set.Icc lo hi) = volume (Set.Icc lo hi) := by
    calc
      volume (toLp '' Set.Icc lo hi)
          = Measure.map toLp volume (toLp '' Set.Icc lo hi) := by
            rw [hpreserving.map_eq]
      _ = volume (toLp ⁻¹' (toLp '' Set.Icc lo hi)) :=
        Measure.map_apply hcontinuous.measurable himage_measurable
      _ = volume (Set.Icc lo hi) := by
        rw [Set.preimage_image_eq _ hinjective]
  rw [hvolume, Real.volume_Icc_pi]
  simp [Fin.prod_univ_succ, ← ENNReal.ofReal_mul,
    sub_nonneg.mpr (hlohi 0), sub_nonneg.mpr (hlohi 1)]
  <;> ring_nf

theorem tube_segment_projection_fiber_volume :
    TubeSegmentProjectionFiberVolumeStatement := by
  intro delta rho start c hdelta hdelta_rho hrho_one
    base direction v hdir hv htau
  let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  have he0 : ‖e0‖ = 1 := by simp [e0]
  have hnorm : ‖direction‖ = ‖e0‖ := by rw [hdir, he0]
  let A : Point3 ≃ₗᵢ[ℝ] Point3 :=
    Submodule.reflection (ℝ ∙ (direction - e0))ᗮ
  have hA_dir : A direction = e0 := Submodule.reflection_sub hnorm
  set v' : Point3 := A v with hv'_def
  set b : Point3 := A base with hb_def
  have hv'_norm : ‖v'‖ = 1 := by
    have h : ‖v'‖ = ‖v‖ := A.norm_map v
    rw [h, hv]
  let tau : ℝ := |inner ℝ direction v|
  have hrho_pos : 0 < rho := by linarith
  have htau_pos : 0 < tau := by
    have hsqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho_pos
    linarith [htau]
  have htau_le_one : tau ≤ 1 := by
    have h : |inner ℝ direction v| ≤ ‖direction‖ * ‖v‖ :=
      abs_real_inner_le_norm _ _
    rw [hdir, hv] at h
    <;> norm_num at h ⊢ <;> exact h
  have hv'0 : inner ℝ e0 v' = v' 0 := by
    have h_e0_eq : e0 = (EuclideanSpace.basisFun (Fin 3) ℝ) 0 := by
      rw [EuclideanSpace.basisFun_apply] <;> rfl
    rw [h_e0_eq]
    exact EuclideanSpace.basisFun_inner (Fin 3) ℝ v' 0
  have htau' : |v' 0| = tau := by
    have h : inner ℝ e0 v' = inner ℝ direction v := by
      have h2 : inner ℝ (A direction) (A v) = inner ℝ direction v :=
        A.inner_map_map direction v
      simpa [hA_dir, hv'_def] using h2
    have h1 : v' 0 = inner ℝ e0 v' := hv'0.symm
    have h3 : |v' 0| = |inner ℝ direction v| := by
      rw [h1, h]
    simpa [tau] using h3
  have hv'0_ne_zero : v' 0 ≠ 0 := by
    rw [← abs_pos]
    rw [htau']
    exact htau_pos
  have hA_inner : ∀ (p : Point3), inner ℝ (A p) v' = inner ℝ p v := by
    intro p
    have h : inner ℝ (A p) (A v) = inner ℝ p v :=
      A.inner_map_map p v
    simpa [hv'_def] using h
  have hA_preserving : MeasurePreserving A volume volume :=
    A.measurePreserving
  let S : Set Point3 :=
    {p | p ∈ tubeSegmentCarrier delta base direction start rho ∧
      dist (inner ℝ p v) c ≤ rho}
  have hS_meas : MeasurableSet S := by
    apply MeasurableSet.inter
    · exact isClosed_cthickening.measurableSet
    · have hcont : Continuous (fun p : Point3 => inner ℝ p v) := by
        fun_prop
      exact hcont.measurable measurableSet_closedBall
  let A_meas : Point3 ≃ᵐ Point3 :=
    { toFun := A, invFun := A.symm,
      left_inv := A.left_inv, right_inv := A.right_inv,
      measurable_toFun := A.continuous.measurable,
      measurable_invFun := A.symm.continuous.measurable }
  have hA_symm_preserving : MeasurePreserving A.symm volume volume :=
    hA_preserving.symm A_meas
  let S' := A '' S
  have hpreimage : A.symm ⁻¹' S = S' := by
    ext z
    simp only [Set.mem_preimage, S', Set.mem_image]
    constructor
    · intro hz
      exact ⟨A.symm z, hz, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
  have hvol : volume S' = volume S := by
    have h2 : volume (A.symm ⁻¹' S) = volume S :=
      hA_symm_preserving.measure_preimage hS_meas.nullMeasurableSet
    rw [hpreimage] at h2
    exact h2
  let axis : Set Point3 :=
    (fun t : ℝ => base + t • direction) ''
      Set.Icc start (start + Real.sqrt rho)
  let axis' : Set Point3 :=
    (fun t : ℝ => b + t • e0) ''
      Set.Icc start (start + Real.sqrt rho)
  have haxis' : A '' axis = axis' := by
    ext y
    simp only [axis, axis', Set.mem_image]
    constructor
    · rintro ⟨x, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨t, ht, ?_⟩
      simp [hb_def, hA_dir, A.map_smul] <;> abel
    · rintro ⟨t, ht, rfl⟩
      refine ⟨base + t • direction, ⟨t, ht, rfl⟩, ?_⟩
      simp [hb_def, hA_dir, A.map_smul] <;> abel
  have htube' : A '' tubeSegmentCarrier delta base direction start rho =
      Metric.cthickening delta axis' := by
    have h_unfold : tubeSegmentCarrier delta base direction start rho =
        Metric.cthickening delta axis := by rfl
    rw [h_unfold]
    have h : A '' Metric.cthickening delta axis =
        Metric.cthickening delta (A '' axis) :=
      IsometryEquiv.cthickening_image (A.toIsometryEquiv) delta axis
    rw [h, haxis']
  have hcompact : IsCompact axis' := by
    apply IsCompact.image isCompact_Icc
    fun_prop
  let center_t : ℝ := (c - inner ℝ b v') / v' 0
  let x_lo : ℝ := b 0 + center_t - (rho + delta) / tau - delta
  let x_hi : ℝ := b 0 + center_t + (rho + delta) / tau + delta
  let y_lo : ℝ := b 1 - delta
  let y_hi : ℝ := b 1 + delta
  let z_lo : ℝ := b 2 - delta
  let z_hi : ℝ := b 2 + delta
  let lo : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => x_lo
    | 1 => y_lo
    | 2 => z_lo
  let hi : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => x_hi
    | 1 => y_hi
    | 2 => z_hi
  have hlohi : ∀ i, lo i ≤ hi i := by
    have h_nonneg : 0 ≤ (rho + delta) / tau := by positivity
    intro i
    fin_cases i <;> simp [lo, hi, x_lo, x_hi, y_lo, y_hi, z_lo, z_hi] <;> linarith
  let toLp : (Fin 3 → ℝ) → Point3 := WithLp.toLp 2
  have hbox : S' ⊆ toLp '' Set.Icc lo hi := by
    intro p' hp'
    rcases hp' with ⟨p, hp, rfl⟩
    have h1 : p ∈ tubeSegmentCarrier delta base direction start rho := hp.1
    have h2 : dist (inner ℝ p v) c ≤ rho := hp.2
    have h1' : A p ∈ Metric.cthickening delta axis' := by
      rw [← htube']
      exact Set.mem_image_of_mem A h1
    have h2' : dist (inner ℝ (A p) v') c ≤ rho := by
      rw [hA_inner p]
      exact h2
    rw [hcompact.cthickening_eq_biUnion_closedBall hdelta.le] at h1'
    rcases Set.mem_iUnion₂.mp h1' with ⟨q, hq, hpq⟩
    rcases hq with ⟨t, _ht, rfl⟩
    let q : Point3 := b + t • e0
    have hdist : dist (A p) q ≤ delta := hpq
    have hcoord0 : |(A p) 0 - q 0| ≤ delta := by
      have h := PiLp.dist_apply_le (A p) q (0 : Fin 3)
      exact h.trans hdist
    have hcoord1 : |(A p) 1 - q 1| ≤ delta := by
      have h := PiLp.dist_apply_le (A p) q (1 : Fin 3)
      exact h.trans hdist
    have hcoord2 : |(A p) 2 - q 2| ≤ delta := by
      have h := PiLp.dist_apply_le (A p) q (2 : Fin 3)
      exact h.trans hdist
    have hq0 : q 0 = b 0 + t := by
      simp [q, e0, EuclideanSpace.single_apply] <;> ring
    have hq1 : q 1 = b 1 := by
      simp [q, e0, EuclideanSpace.single_apply]
    have hq2 : q 2 = b 2 := by
      simp [q, e0, EuclideanSpace.single_apply]
    have hinner_diff : |inner ℝ (A p) v' - inner ℝ q v'| ≤ delta := by
      have h : inner ℝ (A p) v' - inner ℝ q v' = inner ℝ (A p - q) v' := by
        rw [← inner_sub_left] <;> rfl
      rw [h]
      have h2 : |inner ℝ (A p - q) v'| ≤ ‖A p - q‖ * ‖v'‖ :=
        abs_real_inner_le_norm _ _
      rw [hv'_norm] at h2
      have h3 : ‖A p - q‖ = dist (A p) q := by
        rw [dist_eq_norm]
      rw [h3] at h2
      have h2' : |inner ℝ (A p - q) v'| ≤ dist (A p) q := by
        simpa [mul_one] using h2
      exact h2'.trans hdist
    have h3 : |inner ℝ q v' - c| ≤ rho + delta := by
      have h4 : |inner ℝ q v' - c| ≤
          |inner ℝ q v' - inner ℝ (A p) v'| + |inner ℝ (A p) v' - c| := by
        set a := inner ℝ q v' - inner ℝ (A p) v' with ha
        set b := inner ℝ (A p) v' - c with hb
        have h_eq : inner ℝ q v' - c = a + b := by ring
        rw [h_eq]
        exact abs_add_le a b
      have h5 : |inner ℝ q v' - inner ℝ (A p) v'| =
          |inner ℝ (A p) v' - inner ℝ q v'| := by
        rw [show inner ℝ q v' - inner ℝ (A p) v' =
            -(inner ℝ (A p) v' - inner ℝ q v') by ring]
        rw [abs_neg]
      rw [h5] at h4
      have h6 : |inner ℝ (A p) v' - c| ≤ rho := h2'
      linarith [hinner_diff]
    have hinner_q : inner ℝ q v' = inner ℝ b v' + t * (v' 0) := by
      calc
        inner ℝ q v'
            = inner ℝ (b + t • e0) v' := by rfl
        _ = inner ℝ b v' + inner ℝ (t • e0) v' := by
          rw [inner_add_left]
        _ = inner ℝ b v' + t * inner ℝ e0 v' := by
          have hsmul : inner ℝ (t • e0) v' = t * inner ℝ e0 v' :=
            real_inner_smul_left e0 v' t
          rw [hsmul]
        _ = inner ℝ b v' + t * (v' 0) := by rw [← hv'0]
    rw [hinner_q] at h3
    have h7 : |t * v' 0 - (c - inner ℝ b v')| ≤ rho + delta := by
      have h_eq : inner ℝ b v' + t * (v' 0) - c = t * v' 0 - (c - inner ℝ b v') := by ring
      rw [h_eq] at h3
      exact h3
    have h8 : |t - center_t| ≤ (rho + delta) / tau := by
      have h9 : |t * v' 0 - (c - inner ℝ b v')| =
          |v' 0| * |t - center_t| := by
        calc
          |t * v' 0 - (c - inner ℝ b v')|
              = |v' 0 * (t - (c - inner ℝ b v') / v' 0)| := by
                field_simp [hv'0_ne_zero] <;> ring
          _ = |v' 0| * |t - center_t| := by
            rw [abs_mul] <;> rfl
      rw [h9] at h7
      have h10 : |v' 0| * |t - center_t| ≤ rho + delta := h7
      have h11 : |t - center_t| ≤ (rho + delta) / |v' 0| := by
        calc
          |t - center_t|
              = (|v' 0| * |t - center_t|) / |v' 0| := by
                field_simp [hv'0_ne_zero] <;> ring
          _ ≤ (rho + delta) / |v' 0| := by gcongr
      rwa [htau'] at h11
    have hx_bound : |(A p) 0 - (b 0 + center_t)| ≤
        (rho + delta) / tau + delta := by
      calc
        |(A p) 0 - (b 0 + center_t)|
            = |((A p) 0 - q 0) + (t - center_t)| := by
              rw [hq0] <;> abel_nf
        _ ≤ |(A p) 0 - q 0| + |t - center_t| := abs_add_le _ _
        _ ≤ delta + ((rho + delta) / tau) := by gcongr
        _ = (rho + delta) / tau + delta := by ring
    have hy_bound : |(A p) 1 - b 1| ≤ delta := by
      rw [hq1] at hcoord1
      exact hcoord1
    have hz_bound : |(A p) 2 - b 2| ≤ delta := by
      rw [hq2] at hcoord2
      exact hcoord2
    let x : Fin 3 → ℝ := (A p).ofLp
    have hx_lo : lo 0 ≤ x 0 := by
      simp [x, lo, x_lo, abs_le] at hx_bound ⊢ <;> linarith
    have hx_hi : x 0 ≤ hi 0 := by
      simp [x, lo, hi, x_hi, abs_le] at hx_bound ⊢ <;> linarith
    have hy_lo : lo 1 ≤ x 1 := by
      simp [x, lo, y_lo, abs_le] at hy_bound ⊢ <;> linarith
    have hy_hi : x 1 ≤ hi 1 := by
      simp [x, hi, y_hi, abs_le] at hy_bound ⊢ <;> linarith
    have hz_lo : lo 2 ≤ x 2 := by
      simp [x, lo, z_lo, abs_le] at hz_bound ⊢ <;> linarith
    have hz_hi : x 2 ≤ hi 2 := by
      simp [x, hi, z_hi, abs_le] at hz_bound ⊢ <;> linarith
    have hlo' : lo ≤ x := by
      intro i
      fin_cases i <;> tauto
    have hhi' : x ≤ hi := by
      intro i
      fin_cases i <;> tauto
    have hxin : x ∈ Set.Icc lo hi := ⟨hlo', hhi'⟩
    have h_eq : toLp x = A p := WithLp.toLp_ofLp (2 : ENNReal) (A p)
    exact ⟨x, hxin, h_eq⟩
  have hbox_vol : volume S' ≤
      ENNReal.ofReal (1000 * delta ^ 2 * rho / tau) := by
    calc
      volume S'
          ≤ volume (toLp '' Set.Icc lo hi) := measure_mono hbox
      _ = ENNReal.ofReal ((hi 0 - lo 0) * (hi 1 - lo 1) * (hi 2 - lo 2)) :=
        volume_box3 lo hi hlohi
      _ = ENNReal.ofReal (8 * delta ^ 2 * ((rho + delta) / tau + delta)) := by
        congr 1
        have h_len0 : hi 0 - lo 0 = 2 * ((rho + delta) / tau + delta) := by
          simp [lo, hi, x_hi, x_lo] <;> ring
        have h_len1 : hi 1 - lo 1 = 2 * delta := by
          simp [lo, hi, y_hi, y_lo] <;> ring
        have h_len2 : hi 2 - lo 2 = 2 * delta := by
          simp [lo, hi, z_hi, z_lo] <;> ring
        rw [h_len0, h_len1, h_len2] <;> ring
      _ ≤ ENNReal.ofReal (1000 * delta ^ 2 * rho / tau) := by
        apply ENNReal.ofReal_mono
        have hreal : 8 * delta ^ 2 * ((rho + delta) / tau + delta) ≤
            1000 * delta ^ 2 * rho / tau := by
          have hdelta2_pos : 0 < delta ^ 2 := by positivity
          have h : 8 * ((rho + delta) / tau + delta) ≤
              1000 * rho / tau := by
            have h2 : 0 < tau := htau_pos
            have h3 : 8 * (rho + delta) + 8 * delta * tau ≤ 1000 * rho := by
              nlinarith [hdelta_rho, htau_le_one, hrho_pos]
            have h4 : 8 * ((rho + delta) / tau + delta) * tau ≤
                (1000 * rho / tau) * tau := by
              calc
                8 * ((rho + delta) / tau + delta) * tau
                    = 8 * (rho + delta) + 8 * delta * tau := by
                      field_simp [h2.ne'] <;> ring
                _ ≤ 1000 * rho := h3
                _ = (1000 * rho / tau) * tau := by
                  field_simp [h2.ne'] <;> ring
            exact le_of_mul_le_mul_right h4 h2
          have h5 : delta ^ 2 * (8 * ((rho + delta) / tau + delta)) ≤
              delta ^ 2 * (1000 * rho / tau) :=
            mul_le_mul_of_nonneg_left h (by positivity)
          have h6 : 8 * delta ^ 2 * ((rho + delta) / tau + delta) =
              delta ^ 2 * (8 * ((rho + delta) / tau + delta)) := by ring
          have h7 : 1000 * delta ^ 2 * rho / tau =
              delta ^ 2 * (1000 * rho / tau) := by ring
          rw [h6, h7]
          exact h5
        exact hreal
  rw [← hvol]
  exact hbox_vol

end Kakeya.Assouad
