import MyLeanRepo.Kakeya.Streamlined.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Volume and dimension helper lemmas for plank Frostman proof
-/

noncomputable section

open MeasureTheory Metric

namespace Kakeya.Streamlined

/-! ### 1. Volume of axisBox -/

/-- The axisBox is measurable. -/
theorem measurableSet_axisBox (a b c : ℝ) : MeasurableSet (axisBox a b c) := by
  have h_cont0 : Continuous (fun x : Point3 => x (0 : Fin 3)) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0
  have h_cont1 : Continuous (fun x : Point3 => x (1 : Fin 3)) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1
  have h_cont2 : Continuous (fun x : Point3 => x (2 : Fin 3)) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2
  have h1 : IsClosed {x : Point3 | |x (0 : Fin 3)| ≤ a / 2} :=
    isClosed_le (h_cont0.abs) continuous_const
  have h2 : IsClosed {x : Point3 | |x (1 : Fin 3)| ≤ b / 2} :=
    isClosed_le (h_cont1.abs) continuous_const
  have h3 : IsClosed {x : Point3 | |x (2 : Fin 3)| ≤ c / 2} :=
    isClosed_le (h_cont2.abs) continuous_const
  have h_set_eq : axisBox a b c =
      {x : Point3 | |x (0 : Fin 3)| ≤ a / 2} ∩
      ({x : Point3 | |x (1 : Fin 3)| ≤ b / 2} ∩
       {x : Point3 | |x (2 : Fin 3)| ≤ c / 2}) := by
    ext x
    simp [axisBox]
  rw [h_set_eq]
  exact (h1.inter (h2.inter h3)).measurableSet

/-- An axis-parallel box is convex. -/
theorem convex_axisBox (a b c : ℝ) : Convex ℝ (axisBox a b c) := by
  let proj0 : Point3 →ₗ[ℝ] ℝ :=
    { toFun := fun x => x (0 : Fin 3)
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl }
  let proj1 : Point3 →ₗ[ℝ] ℝ :=
    { toFun := fun x => x (1 : Fin 3)
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl }
  let proj2 : Point3 →ₗ[ℝ] ℝ :=
    { toFun := fun x => x (2 : Fin 3)
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl }
  have h0 : Convex ℝ (proj0 ⁻¹' Set.Icc (-(a / 2)) (a / 2)) :=
    (convex_Icc (-(a / 2)) (a / 2)).linear_preimage proj0
  have h1 : Convex ℝ (proj1 ⁻¹' Set.Icc (-(b / 2)) (b / 2)) :=
    (convex_Icc (-(b / 2)) (b / 2)).linear_preimage proj1
  have h2 : Convex ℝ (proj2 ⁻¹' Set.Icc (-(c / 2)) (c / 2)) :=
    (convex_Icc (-(c / 2)) (c / 2)).linear_preimage proj2
  have h_set_eq : axisBox a b c =
      (proj0 ⁻¹' Set.Icc (-(a / 2)) (a / 2)) ∩
      ((proj1 ⁻¹' Set.Icc (-(b / 2)) (b / 2)) ∩
        (proj2 ⁻¹' Set.Icc (-(c / 2)) (c / 2))) := by
    ext x
    simp only [axisBox, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc, abs_le]
    rfl
  rw [h_set_eq]
  exact h0.inter (h1.inter h2)

/-- The axisBox volume is a*b*c. -/
theorem volume_axisBox (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    MeasureTheory.volume (axisBox a b c) = ENNReal.ofReal (a * b * c) := by
  let lo : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => -a / 2
    | 1 => -b / 2
    | 2 => -c / 2
  let hi : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => a / 2
    | 1 => b / 2
    | 2 => c / 2
  let S : Set (Fin 3 → ℝ) := Set.Icc lo hi
  let toLp : (Fin 3 → ℝ) → Point3 := WithLp.toLp 2
  have h_toLp_coord : ∀ (y : Fin 3 → ℝ) (i : Fin 3), (toLp y) i = y i := by
    intro y i
    rfl
  have h_eq : toLp '' S = axisBox a b c := by
    ext x
    simp only [Set.mem_image, S, Set.mem_Icc, axisBox, toLp]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h_lo : lo ≤ y := hy.1
      have h_hi : y ≤ hi := hy.2
      have h0 : |(toLp y) (0 : Fin 3)| ≤ a / 2 := by
        rw [h_toLp_coord]
        have hlo1 : lo 0 ≤ y 0 := h_lo 0
        have hlo2 : lo 0 = -(a / 2) := by simp [lo] <;> ring
        have hhi1 : y 0 ≤ hi 0 := h_hi 0
        have hhi2 : hi 0 = a / 2 := by simp [hi] <;> ring
        rw [hlo2] at hlo1
        rw [hhi2] at hhi1
        exact abs_le.mpr ⟨hlo1, hhi1⟩
      have h1 : |(toLp y) (1 : Fin 3)| ≤ b / 2 := by
        rw [h_toLp_coord]
        have hlo1 : lo 1 ≤ y 1 := h_lo 1
        have hlo2 : lo 1 = -(b / 2) := by simp [lo] <;> ring
        have hhi1 : y 1 ≤ hi 1 := h_hi 1
        have hhi2 : hi 1 = b / 2 := by simp [hi] <;> ring
        rw [hlo2] at hlo1
        rw [hhi2] at hhi1
        exact abs_le.mpr ⟨hlo1, hhi1⟩
      have h2 : |(toLp y) (2 : Fin 3)| ≤ c / 2 := by
        rw [h_toLp_coord]
        have hlo1 : lo 2 ≤ y 2 := h_lo 2
        have hlo2 : lo 2 = -(c / 2) := by simp [lo] <;> ring
        have hhi1 : y 2 ≤ hi 2 := h_hi 2
        have hhi2 : hi 2 = c / 2 := by simp [hi] <;> ring
        rw [hlo2] at hlo1
        rw [hhi2] at hhi1
        exact abs_le.mpr ⟨hlo1, hhi1⟩
      exact ⟨h0, h1, h2⟩
    · intro hx
      have h0 : |x (0 : Fin 3)| ≤ a / 2 := hx.1
      have h1 : |x (1 : Fin 3)| ≤ b / 2 := hx.2.1
      have h2 : |x (2 : Fin 3)| ≤ c / 2 := hx.2.2
      have h0' : -(a / 2) ≤ x 0 ∧ x 0 ≤ a / 2 := abs_le.mp h0
      have h1' : -(b / 2) ≤ x 1 ∧ x 1 ≤ b / 2 := abs_le.mp h1
      have h2' : -(c / 2) ≤ x 2 ∧ x 2 ≤ c / 2 := abs_le.mp h2
      have h_lo : lo ≤ x.ofLp := by
        intro i
        have h_eq : x.ofLp i = x i := by rfl
        rw [h_eq]
        fin_cases i
        · have h : -a / 2 ≤ x 0 := by linarith [h0'.1]
          simpa [lo] using h
        · have h : -b / 2 ≤ x 1 := by linarith [h1'.1]
          simpa [lo] using h
        · have h : -c / 2 ≤ x 2 := by linarith [h2'.1]
          simpa [lo] using h
      have h_hi : x.ofLp ≤ hi := by
        intro i
        have h_eq : x.ofLp i = x i := by rfl
        rw [h_eq]
        fin_cases i
        · have h : x 0 ≤ a / 2 := by linarith [h0'.2]
          simpa [hi] using h
        · have h : x 1 ≤ b / 2 := by linarith [h1'.2]
          simpa [hi] using h
        · have h : x 2 ≤ c / 2 := by linarith [h2'.2]
          simpa [hi] using h
      refine ⟨x.ofLp, ⟨h_lo, h_hi⟩, ?_⟩
      simp [WithLp.ofLp_toLp]
  have h_mp : MeasureTheory.MeasurePreserving toLp := PiLp.volume_preserving_toLp (ι := Fin 3)
  have h_inj : Function.Injective toLp := by
    intro a b h
    simpa [toLp, WithLp.toLp_injective] using h
  have h_cont : Continuous toLp := PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)
  have h_meas : Measurable toLp := h_cont.measurable
  have h_S_meas : MeasurableSet S := measurableSet_Icc
  have h_img_meas : MeasurableSet (toLp '' S) := by
    have h : toLp '' S = (fun x : Point3 => x.ofLp) ⁻¹' S := by
      ext y
      simp only [toLp, Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [WithLp.ofLp_toLp] using hx
      · intro hy
        refine ⟨y.ofLp, hy, ?_⟩
        simp [WithLp.ofLp_toLp]
    rw [h]
    have h_cont2 : Continuous (fun x : Point3 => x.ofLp) := PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ)
    exact h_cont2.measurable h_S_meas
  have h_map : MeasureTheory.Measure.map toLp MeasureTheory.volume = MeasureTheory.volume := h_mp.map_eq
  have h_vol1 : MeasureTheory.volume (toLp '' S) = MeasureTheory.volume S := by
    calc MeasureTheory.volume (toLp '' S)
      = MeasureTheory.Measure.map toLp MeasureTheory.volume (toLp '' S) := by rw [h_map]
    _ = MeasureTheory.volume (toLp ⁻¹' (toLp '' S)) := MeasureTheory.Measure.map_apply h_meas h_img_meas
    _ = MeasureTheory.volume S := by rw [Set.preimage_image_eq S h_inj]
  rw [← h_eq, h_vol1]
  have h_pi : MeasureTheory.volume S = ∏ i : Fin 3, ENNReal.ofReal (hi i - lo i) :=
    Real.volume_Icc_pi
  rw [h_pi]
  have h_prod : (∏ i : Fin 3, ENNReal.ofReal (hi i - lo i)) =
      ENNReal.ofReal (a * b * c) := by
    have h_simp : ∀ (x : ℝ), x / 2 - -x / 2 = x := by intro x; ring
    simp [lo, hi, Fin.prod_univ_succ, h_simp]
    have h1 : ENNReal.ofReal a * (ENNReal.ofReal b * ENNReal.ofReal c) =
        ENNReal.ofReal (a * b * c) := by
      have h2 : ENNReal.ofReal b * ENNReal.ofReal c = ENNReal.ofReal (b * c) := by
        exact Eq.symm (ENNReal.ofReal_mul (show 0 ≤ b by linarith))
      rw [h2]
      have h3 : ENNReal.ofReal a * ENNReal.ofReal (b * c) = ENNReal.ofReal (a * (b * c)) := by
        exact Eq.symm (ENNReal.ofReal_mul (show 0 ≤ a by linarith))
      rw [h3]
      <;> ring
    exact h1
  exact h_prod

/-! ### 2. Volume bounds from HasDimensionsInFrame -/

/-- An affine isometry equivalence preserves Lebesgue volume of a measurable set. -/
theorem AffineIsometryEquiv.volume_image (e : Point3 ≃ᵃⁱ[ℝ] Point3)
    (s : Set Point3) (hs : MeasurableSet s) :
    MeasureTheory.volume (e '' s) = MeasureTheory.volume s := by
  have h_lin : MeasureTheory.MeasurePreserving (e.linearIsometryEquiv : Point3 → Point3) :=
    LinearIsometryEquiv.measurePreserving e.linearIsometryEquiv
  let p : Point3 := e 0
  have h_trans : MeasureTheory.MeasurePreserving (fun x : Point3 => x + p) :=
    measurePreserving_add_right volume p
  have h_decomp : (e : Point3 → Point3) = (fun x : Point3 => x + p) ∘ e.linearIsometryEquiv := by
    funext x
    have h4 : e ((x : Point3) +ᵥ (0 : Point3)) = e.linearIsometryEquiv x +ᵥ p := by
      exact e.map_vadd (0 : Point3) x
    simpa using h4
  have h_comp : MeasureTheory.MeasurePreserving ((fun x : Point3 => x + p) ∘ e.linearIsometryEquiv) :=
    h_trans.comp h_lin
  have h_mp : MeasureTheory.MeasurePreserving (e : Point3 → Point3) := by
    rw [h_decomp]
    exact h_comp
  have h_inj : Function.Injective (e : Point3 → Point3) := e.injective
  have h_meas : Measurable (e : Point3 → Point3) := e.continuous.measurable
  have h_symm_meas : Measurable (e.symm : Point3 → Point3) := e.symm.continuous.measurable
  have h_img_meas : MeasurableSet (e '' s) := by
    have h : e '' s = (e.symm : Point3 → Point3) ⁻¹' s := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro hy
        refine ⟨e.symm y, hy, ?_⟩
        simp
    rw [h]
    exact h_symm_meas hs
  have h_map : MeasureTheory.Measure.map e MeasureTheory.volume = MeasureTheory.volume := h_mp.map_eq
  calc MeasureTheory.volume (e '' s)
    = MeasureTheory.Measure.map e MeasureTheory.volume (e '' s) := by rw [h_map]
  _ = MeasureTheory.volume (e ⁻¹' (e '' s)) := MeasureTheory.Measure.map_apply h_meas h_img_meas
  _ = MeasureTheory.volume s := by rw [Set.preimage_image_eq s h_inj]

/-- Lower volume bound from HasDimensionsInFrame. -/
theorem hasDimensionsInFrame_volume_lower {K : Body} {frame : Point3 ≃ᵃⁱ[ℝ] Point3}
    {a b c A : ℝ} (h : K.HasDimensionsInFrame frame a b c A) :
    ENNReal.ofReal (a * b * c) ≤ K.volume := by
  have ha : 0 < a := h.1
  have h_ab : a ≤ b := h.2.1
  have h_bc : b ≤ c := h.2.2.1
  have hb : 0 < b := lt_of_lt_of_le ha h_ab
  have hc : 0 < c := lt_of_lt_of_le hb h_bc
  have h_inner : frame '' axisBox a b c ⊆ K.carrier := h.2.2.2.2.1
  have h_vol_img : MeasureTheory.volume (frame '' axisBox a b c) =
      MeasureTheory.volume (axisBox a b c) :=
    AffineIsometryEquiv.volume_image frame (axisBox a b c) (measurableSet_axisBox a b c)
  have h_vol_box : MeasureTheory.volume (axisBox a b c) =
      ENNReal.ofReal (a * b * c) := volume_axisBox a b c ha hb hc
  have h : MeasureTheory.volume (frame '' axisBox a b c) ≤ K.volume :=
    measure_mono h_inner
  rw [h_vol_img, h_vol_box] at h
  exact h

/-- Upper volume bound from HasDimensionsInFrame. -/
theorem hasDimensionsInFrame_volume_upper {K : Body} {frame : Point3 ≃ᵃⁱ[ℝ] Point3}
    {a b c A : ℝ} (h : K.HasDimensionsInFrame frame a b c A) :
    K.volume ≤ ENNReal.ofReal (A ^ 3 * a * b * c) := by
  have ha : 0 < a := h.1
  have h_ab : a ≤ b := h.2.1
  have h_bc : b ≤ c := h.2.2.1
  have hb : 0 < b := lt_of_lt_of_le ha h_ab
  have hc : 0 < c := lt_of_lt_of_le hb h_bc
  have hA : 1 ≤ A := h.2.2.2.1
  have h_outer : K.carrier ⊆ frame '' axisBox (A * a) (A * b) (A * c) := h.2.2.2.2.2
  have h_pos1 : 0 < A * a := mul_pos (by linarith) ha
  have h_pos2 : 0 < A * b := mul_pos (by linarith) hb
  have h_pos3 : 0 < A * c := mul_pos (by linarith) hc
  have h_vol_img : MeasureTheory.volume (frame '' axisBox (A * a) (A * b) (A * c)) =
      MeasureTheory.volume (axisBox (A * a) (A * b) (A * c)) :=
    AffineIsometryEquiv.volume_image frame (axisBox (A * a) (A * b) (A * c)) (measurableSet_axisBox (A * a) (A * b) (A * c))
  have h_vol_box : MeasureTheory.volume (axisBox (A * a) (A * b) (A * c)) =
      ENNReal.ofReal ((A * a) * (A * b) * (A * c)) :=
    volume_axisBox (A * a) (A * b) (A * c) h_pos1 h_pos2 h_pos3
  have h_mul : (A * a) * (A * b) * (A * c) = A ^ 3 * a * b * c := by ring
  have h : K.volume ≤ MeasureTheory.volume (frame '' axisBox (A * a) (A * b) (A * c)) :=
    measure_mono h_outer
  rw [h_vol_img, h_vol_box, h_mul] at h
  exact h

/-! ### 3. Plank volume bounds -/

/-- Lower volume bound for a plank body. -/
theorem PlankFamily.volume_lower {a b A : ℝ} (P : PlankFamily a b A)
    (i : Fin P.family.card) :
    ENNReal.ofReal (a * b) ≤ (P.family.body i).volume := by
  have h_dim : (P.family.body i).HasDimensionsInFrame (P.frame i) a b 1 A :=
    P.dimensions i
  have h := hasDimensionsInFrame_volume_lower h_dim
  have h1 : a * b * (1 : ℝ) = a * b := by ring
  rw [h1] at h
  exact h

/-- Upper volume bound for a plank body. -/
theorem PlankFamily.volume_upper {a b A : ℝ} (P : PlankFamily a b A)
    (i : Fin P.family.card) :
    (P.family.body i).volume ≤ ENNReal.ofReal (A ^ 3 * a * b) := by
  have h_dim : (P.family.body i).HasDimensionsInFrame (P.frame i) a b 1 A :=
    P.dimensions i
  have h := hasDimensionsInFrame_volume_upper h_dim
  have h1 : A ^ 3 * a * b * (1 : ℝ) = A ^ 3 * a * b := by ring
  rw [h1] at h
  exact h

/-! ### 4. Volume scaling under linear map -/

/-- Volume of image under a continuous linear map with nonzero determinant. -/
theorem volume_linear_image (f : Point3 →L[ℝ] Point3)
    (hf : LinearMap.det (f : Point3 →ₗ[ℝ] Point3) ≠ 0)
    (K : Set Point3) :
    MeasureTheory.volume (f '' K) =
    ENNReal.ofReal (|LinearMap.det (f : Point3 →ₗ[ℝ] Point3)|) * MeasureTheory.volume K :=
  MeasureTheory.Measure.addHaar_image_continuousLinearMap
    MeasureTheory.volume f K

/-! ### 5. Thickened convex set volume -/

/-- Trivial lower bound: thickening has at least the original volume. -/
theorem volume_cthickening_lower (K : Set Point3) (r : ℝ) (hr : 0 ≤ r) :
    MeasureTheory.volume K ≤ MeasureTheory.volume (Metric.cthickening r K) := by
  have h_sub : K ⊆ Metric.cthickening r K := by
    intro x hx
    have h0 : Metric.infEDist x K = 0 := Metric.infEDist_zero_of_mem hx
    have h1 : Metric.infEDist x K ≤ ENNReal.ofReal r := by
      rw [h0]
      simp [hr]
    simpa [Metric.cthickening_eq_preimage_infEDist] using h1
  exact measure_mono h_sub

/-- Convexity of thickening. -/
theorem cthickening_convex {K : Set Point3} (hK : Convex ℝ K) (r : ℝ) :
    Convex ℝ (Metric.cthickening r K) :=
  Convex.cthickening hK r

/-! ### 6. Frostman constant lower bound -/

/-- The Frostman constant is at least 1 when the family has positive, finite density in U. -/
theorem frostmanConstantIn_ge_one {F : BodyFamily} {U : Set Point3}
    (hU : Convex ℝ U) (hvol_ne_zero : MeasureTheory.volume U ≠ 0)
    (hvol_ne_top : MeasureTheory.volume U ≠ ⊤)
    (hmass_ne_zero : F.containedMass U ≠ 0)
    (hmass_ne_top : F.containedMass U ≠ ⊤) :
    1 ≤ F.frostmanConstantIn U := by
  have h_density_pos : F.density U ≠ 0 := by
    have h : F.density U = F.containedMass U / MeasureTheory.volume U := by rfl
    rw [h]
    exact ENNReal.div_ne_zero.mpr ⟨hmass_ne_zero, hvol_ne_top⟩
  have h_density_top : F.density U ≠ ⊤ := by
    have h : F.density U = F.containedMass U / MeasureTheory.volume U := by rfl
    rw [h]
    exact ENNReal.div_ne_top hmass_ne_top hvol_ne_zero
  have h1 : F.density U / F.density U = 1 := ENNReal.div_self h_density_pos h_density_top
  let S : Set ENNReal := {c | ∃ K : Set Point3, Convex ℝ K ∧ K ⊆ U ∧ c = F.density K / F.density U}
  have h2 : (1 : ENNReal) ∈ S := by
    refine ⟨U, hU, Set.Subset.refl U, ?_⟩
    simpa [S] using Eq.symm h1
  have h_bdd : BddAbove S := ⟨⊤, fun _ _ => le_top⟩
  exact le_csSup h_bdd h2

end Kakeya.Streamlined
