import MyLeanRepo.Kakeya.CV.PolynomialCylinder.RegularCover
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.PatchImageMeasurability
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.GraphPatchIntegralMeasurability
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.FamilyMeasurability
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.DirectionalGraphAreaWeighted
import MyLeanRepo.Kakeya.CV.GeometricMeasure.GraphAreaWeightedOnOpen
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.DirectionalGraphWeight
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Equality for a single graph-patch contribution

For a measurable subset of one regular graph patch, this module converts the
weighted Hausdorff integral into a Lebesgue integral on the graph base.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real Classical

namespace Kakeya.CV

variable {k : ℕ} {P : PolynomialParameterization k}

/-- `dirGraphMap dir f y = dirGraphMap dir f' y'` implies `y = y'`. -/
lemma dirGraphMap_injective (dir : Fin 3)
    {f f' : Point 2 → ℝ} {y y' : Point 2} :
    dirGraphMap dir f y = dirGraphMap dir f' y' → y = y' := by
  fin_cases dir
  · intro h
    have h0 := congr_arg (fun z : Point 3 => z 2) h
    have h1 := congr_arg (fun z : Point 3 => z 1) h
    ext i
    fin_cases i <;> simp at h0 h1 ⊢ <;> tauto
  · intro h
    have h0 := congr_arg (fun z : Point 3 => z 0) h
    have h1 := congr_arg (fun z : Point 3 => z 2) h
    ext i
    fin_cases i <;> simp at h0 h1 ⊢ <;> tauto
  · intro h
    have h0 := congr_arg (fun z : Point 3 => z 0) h
    have h1 := congr_arg (fun z : Point 3 => z 1) h
    ext i
    fin_cases i <;> simp at h0 h1 ⊢ <;> tauto

/-- Pointwise weight identity for a single regular graph patch. -/
lemma single_patch_pointwise_weight
    {k : ℕ} {P : PolynomialParameterization k}
    (patch : CoverPatch k P) (u : Point 3)
    (F : CoefficientSpace P.dim × Point 3 → ENNReal)
    (hF_eq : ∀ x z, F (x, z) =
      ENNReal.ofReal ‖inner ℝ u
        (polynomialUnitNormal (parameterPolynomial P x) z)‖)
    (x : CoefficientSpace P.dim) (hxV : x ∈ patch.V)
    (y : Point 2) (hyA : y ∈ patch.A)
    (directionalFactor : CoefficientSpace P.dim → Point 2 → ℝ)
    (hdf_eq : ∀ x ∈ patch.V, ∀ y ∈ patch.A,
      directionalFactor x y =
        ‖inner ℝ u (polynomialGradient (parameterPolynomial P x)
          (dirGraphMap patch.dir (patch.g x) y))‖ /
        |(polynomialGradient (parameterPolynomial P x)
          (dirGraphMap patch.dir (patch.g x) y)) patch.dir|) :
    F (x, dirGraphMap patch.dir (patch.g x) y) *
        areaFactor (patch.g x) y =
      planeConstant * ENNReal.ofReal (directionalFactor x y) := by
  let dir := patch.dir
  let g : Point 2 → ℝ := patch.g x
  have hg_on : ContDiffOn ℝ 1 g patch.A := by
    have h2 : ContDiffOn ℝ 1 (fun y : Point 2 => (x, y)) patch.A := by
      fun_prop
    exact patch.hg_smooth.comp h2 (by
      intro y hy
      exact ⟨hxV, hy⟩)
  have h_zero :
      polynomialValue (parameterPolynomial P x) (dirGraphMap dir g y) = 0 :=
    patch.h_zero x hxV y hyA
  have h_reg :
      (polynomialGradient (parameterPolynomial P x)
        (dirGraphMap dir g y)) dir ≠ 0 :=
    patch.h_reg x hxV y hyA
  have h_zero_local : ∀ᶠ w : Point 2 in nhds y,
      polynomialValue (parameterPolynomial P x) (dirGraphMap dir g w) = 0 := by
    have h1 : patch.A ∈ nhds y := patch.hA_open.mem_nhds hyA
    filter_upwards [h1] with w hw
    exact patch.h_zero x hxV w hw
  have hg_diff : DifferentiableAt ℝ g y :=
    (hg_on.contDiffAt (patch.hA_open.mem_nhds hyA)).differentiableAt
      (by norm_num)
  have h_main_wi : ∀ d : Fin 3,
      polynomialValue (parameterPolynomial P x) (dirGraphMap d g y) = 0 →
      (∀ᶠ w : Point 2 in nhds y,
        polynomialValue (parameterPolynomial P x) (dirGraphMap d g w) = 0) →
      (polynomialGradient (parameterPolynomial P x)
        (dirGraphMap d g y)) d ≠ 0 →
      ‖inner ℝ u (polynomialUnitNormal (parameterPolynomial P x)
        (dirGraphMap d g y))‖ *
          Real.sqrt (1 + ‖fderiv ℝ g y‖ ^ 2) =
        ‖inner ℝ u (polynomialGradient (parameterPolynomial P x)
          (dirGraphMap d g y))‖ /
        |(polynomialGradient (parameterPolynomial P x)
          (dirGraphMap d g y)) d| := by
    intro d
    fin_cases d
    · exact fun hz hzl hr =>
        graph_weight_identity_x hz hzl hr hg_diff
    · exact fun hz hzl hr =>
        graph_weight_identity_y hz hzl hr hg_diff
    · exact fun hz hzl hr =>
        graph_weight_identity_z hz hzl hr hg_diff
  have hwi := h_main_wi dir h_zero h_zero_local h_reg
  have h1 : F (x, dirGraphMap dir g y) =
      ENNReal.ofReal ‖inner ℝ u
        (polynomialUnitNormal (parameterPolynomial P x)
          (dirGraphMap dir g y))‖ :=
    hF_eq x (dirGraphMap dir g y)
  have h2 : areaFactor g y =
      planeConstant *
        ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ g y‖ ^ 2)) := by
    rfl
  rw [h1, h2]
  set a : ℝ := ‖inner ℝ u
    (polynomialUnitNormal (parameterPolynomial P x)
      (dirGraphMap dir g y))‖ with ha
  set b : ℝ := Real.sqrt (1 + ‖fderiv ℝ g y‖ ^ 2) with hb
  have ha_nonneg : 0 ≤ a := by positivity
  have h_mul :
      ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal (a * b) :=
    (ENNReal.ofReal_mul ha_nonneg).symm
  have h3 :
      ENNReal.ofReal a * (planeConstant * ENNReal.ofReal b) =
        planeConstant * ENNReal.ofReal (a * b) := by
    calc
      ENNReal.ofReal a * (planeConstant * ENNReal.ofReal b) =
          planeConstant * (ENNReal.ofReal a * ENNReal.ofReal b) := by
            ac_rfl
      _ = planeConstant * ENNReal.ofReal (a * b) := by rw [h_mul]
  have h4 : a * b =
      ‖inner ℝ u (polynomialGradient (parameterPolynomial P x)
        (dirGraphMap dir g y))‖ /
      |(polynomialGradient (parameterPolynomial P x)
        (dirGraphMap dir g y)) dir| := by
    simpa [ha, hb] using hwi
  have h5 : a * b = directionalFactor x y :=
    h4.trans (hdf_eq x hxV y hyA).symm
  rw [h3, h5]

/-- The weighted Hausdorff integral over one patch section equals the
corresponding Lebesgue integral on its base. -/
lemma single_patch_equality
    {k : ℕ} {P : PolynomialParameterization k}
    (patch : CoverPatch k P)
    {U : Set (Point 3)} (hU : MeasurableSet U)
    (u : Point 3)
    (D : Set (CoefficientSpace P.dim × Point 3))
    (hD : MeasurableSet D)
    (hD_sub : D ⊆ coverPatchImage patch)
    (F : CoefficientSpace P.dim × Point 3 → ENNReal)
    (hF_meas : Measurable F)
    (hF_def : ∀ x z, F (x, z) =
      ENNReal.ofReal ‖inner ℝ u
        (polynomialUnitNormal (parameterPolynomial P x) z)‖)
    (graphPoint : CoefficientSpace P.dim → Point 2 → Point 3)
    (hgraph : Measurable
      (fun p : CoefficientSpace P.dim × Point 2 => graphPoint p.1 p.2))
    (directionalFactor : CoefficientSpace P.dim → Point 2 → ℝ)
    (hdirectionalFactor_nonneg : ∀ x y, 0 ≤ directionalFactor x y)
    (hdf_eq : ∀ x ∈ patch.V, ∀ y ∈ patch.A,
      directionalFactor x y =
        ‖inner ℝ u (polynomialGradient (parameterPolynomial P x)
          (dirGraphMap patch.dir (patch.g x) y))‖ /
        |(polynomialGradient (parameterPolynomial P x)
          (dirGraphMap patch.dir (patch.g x) y)) patch.dir|)
    (B_set : Set (CoefficientSpace P.dim × Point 2))
    (hB_set : B_set =
      {p | (p.1, graphPoint p.1 p.2) ∈ D})
    (hgraphPoint_form : ∀ x y, ∃ f,
      graphPoint x y = dirGraphMap patch.dir f y)
    (h_agree : ∀ p ∈ patch.V ×ˢ patch.A,
      graphPoint p.1 p.2 =
        dirGraphMap patch.dir (patch.g p.1) p.2) :
    ∀ x : CoefficientSpace P.dim,
      (∫⁻ z : Point 3,
        Set.indicator {z : Point 3 | (x, z) ∈ D}
            (1 : Point 3 → ENNReal) z *
          Set.indicator U (1 : Point 3 → ENNReal) z *
          F (x, z) ∂μH[2]) =
      planeConstant * (∫⁻ y : Point 2,
        B_set.indicator (fun _ => (1 : ENNReal)) (x, y) *
          U.indicator (fun _ => (1 : ENNReal)) (graphPoint x y) *
          ENNReal.ofReal |directionalFactor x y| ∂volume) := by
  intro x
  let dir := patch.dir
  by_cases hxV : x ∈ patch.V
  · let g : Point 2 → ℝ := patch.g x
    have hg_on : ContDiffOn ℝ 1 g patch.A := by
      have h2 : ContDiffOn ℝ 1 (fun y : Point 2 => (x, y)) patch.A := by
        fun_prop
      exact patch.hg_smooth.comp h2 (by
        intro y hy
        exact ⟨hxV, hy⟩)
    let B : Set (Point 2) :=
      {y | (x, graphPoint x y) ∈ D ∧ graphPoint x y ∈ U}
    have h_graph_x : Measurable (fun y : Point 2 => graphPoint x y) :=
      hgraph.comp (Measurable.prodMk measurable_const measurable_id)
    have hB_sub_A : B ⊆ patch.A := by
      intro y hy
      have h_in_W := hD_sub hy.1
      rcases h_in_W with ⟨_, y', hy'A, heq⟩
      simp at heq
      rcases hgraphPoint_form x y with ⟨f, hf⟩
      have h_eq :
          dirGraphMap dir f y =
            dirGraphMap dir (patch.g x) y' :=
        hf.symm.trans heq.symm
      exact (dirGraphMap_injective dir h_eq) ▸ hy'A
    have hB_meas : MeasurableSet B := by
      exact (hD.preimage (measurable_const.prodMk h_graph_x)).inter
        (hU.preimage h_graph_x)
    have h_image :
        dirGraphMap dir g '' B =
          {z : Point 3 | (x, z) ∈ D ∧ z ∈ U} := by
      ext z
      simp only [Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hyA := hB_sub_A hy
        have h_eq_graph := h_agree (x, y) ⟨hxV, hyA⟩
        exact ⟨by simpa only [h_eq_graph] using hy.1,
          by simpa only [h_eq_graph] using hy.2⟩
      · rintro ⟨h_in_D, h_in_U⟩
        rcases hD_sub h_in_D with ⟨_, y, hyA, heq⟩
        simp at heq
        have h_eq_graph := h_agree (x, y) ⟨hxV, hyA⟩
        have h_z_eq : z = graphPoint x y :=
          heq.symm.trans h_eq_graph.symm
        exact ⟨y, ⟨h_z_eq ▸ h_in_D, h_z_eq ▸ h_in_U⟩,
          heq⟩
    have hF_sec : Measurable (fun z : Point 3 => F (x, z)) :=
      hF_meas.comp (Measurable.prodMk measurable_const measurable_id)
    have h_main_eq :
        ∫⁻ z in dirGraphMap dir g '' B, F (x, z) ∂μH[2] =
          planeConstant *
            ∫⁻ y in B, ENNReal.ofReal (directionalFactor x y) ∂volume := by
      rw [dir_graph_area_formula_weighted_on_open
        dir g patch.hA_open hg_on hB_meas hB_sub_A hF_sec]
      have h_weight : ∀ y ∈ B,
          F (x, dirGraphMap dir g y) * areaFactor g y =
            planeConstant * ENNReal.ofReal (directionalFactor x y) := by
        intro y hy
        exact single_patch_pointwise_weight patch u F hF_def
          x hxV y (hB_sub_A hy) directionalFactor hdf_eq
      rw [MeasureTheory.setLIntegral_congr_fun hB_meas h_weight]
      exact MeasureTheory.lintegral_const_mul'
        planeConstant (fun y => ENNReal.ofReal (directionalFactor x y))
        planeConstant_ne_top
    have hLHS :
        (∫⁻ z : Point 3,
          Set.indicator {z : Point 3 | (x, z) ∈ D}
              (1 : Point 3 → ENNReal) z *
            Set.indicator U (1 : Point 3 → ENNReal) z *
            F (x, z) ∂μH[2]) =
          ∫⁻ z in {z : Point 3 | (x, z) ∈ D ∧ z ∈ U},
            F (x, z) ∂μH[2] := by
      have h_ind : ∀ z : Point 3,
          Set.indicator {z : Point 3 | (x, z) ∈ D}
              (1 : Point 3 → ENNReal) z *
            Set.indicator U (1 : Point 3 → ENNReal) z *
            F (x, z) =
          Set.indicator {z : Point 3 | (x, z) ∈ D ∧ z ∈ U}
            (fun z => F (x, z)) z := by
        intro z
        by_cases h1 : (x, z) ∈ D <;>
          by_cases h2 : z ∈ U <;> simp [h1, h2]
      rw [lintegral_congr h_ind]
      exact MeasureTheory.lintegral_indicator
        ((hD.preimage (measurable_const.prodMk measurable_id)).inter hU) _
    have hRHS :
        (∫⁻ y : Point 2,
          B_set.indicator (fun _ => (1 : ENNReal)) (x, y) *
            U.indicator (fun _ => (1 : ENNReal)) (graphPoint x y) *
            ENNReal.ofReal |directionalFactor x y| ∂volume) =
          ∫⁻ y in B, ENNReal.ofReal (directionalFactor x y) ∂volume := by
      have h_ind : ∀ y : Point 2,
          B_set.indicator (fun _ => (1 : ENNReal)) (x, y) *
              U.indicator (fun _ => (1 : ENNReal)) (graphPoint x y) *
              ENNReal.ofReal |directionalFactor x y| =
            Set.indicator B
              (fun _ => ENNReal.ofReal (directionalFactor x y)) y := by
        intro y
        have hB_iff :
            (x, y) ∈ B_set ↔ (x, graphPoint x y) ∈ D := by
          rw [hB_set]
          simp
        by_cases h_in_Bset : (x, y) ∈ B_set
        · by_cases h_in_U : graphPoint x y ∈ U
          · have hyB : y ∈ B := ⟨hB_iff.mp h_in_Bset, h_in_U⟩
            have h6 := hdirectionalFactor_nonneg x y
            simp [h_in_Bset, h_in_U, hyB, abs_of_nonneg h6]
          · have hyB : y ∉ B := fun hy => h_in_U hy.2
            simp [h_in_Bset, h_in_U, hyB]
        · have hyB : y ∉ B :=
            fun hy => h_in_Bset (hB_iff.mpr hy.1)
          simp [h_in_Bset, hyB]
      rw [lintegral_congr h_ind]
      exact MeasureTheory.lintegral_indicator hB_meas _
    rw [hLHS, hRHS, ← h_image, h_main_eq]
  · have h_section_empty : {z : Point 3 | (x, z) ∈ D} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hz
      exact hxV (hD_sub hz).1
    have hLHS_zero :
        (∫⁻ z : Point 3,
          Set.indicator {z : Point 3 | (x, z) ∈ D}
              (1 : Point 3 → ENNReal) z *
            Set.indicator U (1 : Point 3 → ENNReal) z *
            F (x, z) ∂μH[2]) = 0 := by
      simp [h_section_empty]
    have hRHS_zero :
        (∫⁻ y : Point 2,
          B_set.indicator (fun _ => (1 : ENNReal)) (x, y) *
            U.indicator (fun _ => (1 : ENNReal)) (graphPoint x y) *
            ENNReal.ofReal |directionalFactor x y| ∂volume) = 0 := by
      have h2 : ∀ y : Point 2, (x, y) ∉ B_set := by
        intro y hxy
        rw [hB_set] at hxy
        exact hxV (hD_sub hxy).1
      have h_all_zero : ∀ y : Point 2,
          B_set.indicator (fun _ => (1 : ENNReal)) (x, y) *
            U.indicator (fun _ => (1 : ENNReal)) (graphPoint x y) *
            ENNReal.ofReal |directionalFactor x y| = 0 := by
        intro y
        simp [h2 y]
      rw [lintegral_congr h_all_zero, lintegral_zero]
    rw [hLHS_zero, hRHS_zero]
    simp

end Kakeya.CV
