import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.ImplicitDerivative
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.GraphAreaSmooth
import Mathlib.Tactic

/-!
# Local Graph Slice for Coarea Formula (weakened hypotheses)

Version of `coarea_graph_slice` that only requires the C¹ extension `g_t` to agree
with the implicit function on an open neighborhood of `B_t`, not everywhere.
-/

open MeasureTheory Metric Set ENNReal
open scoped MeasureTheory

namespace Geometry

variable {m : ℕ} [Nonempty (Fin m)]

/-- Modified graph slice: g_t only needs to agree with the implicit function
on an open set U containing B_t. -/
lemma coarea_graph_slice_local
    (f : E (m + 1) → ℝ)
    (hf : ContDiff ℝ 1 f)
    (φ : OpenPartialHomeomorph (E (m + 1)) (E (m + 1)))
    (hφ_coe : (φ : E (m + 1) → E (m + 1)) =
        fun y => projHCL y + f y • (eLast : E (m + 1)))
    {V : Set (E (m + 1))}
    (hV_source : V ⊆ φ.source)
    (hV_reg : ∀ y ∈ V, (fderiv ℝ f y) (eLast : E (m + 1)) ≠ 0)
    (A : Set (E (m + 1)))
    (hA : MeasurableSet A)
    (hA_sub : A ⊆ V)
    (t : ℝ)
    (g_t : E m → ℝ)
    (hgt_diff : ContDiff ℝ 1 g_t)
    (U : Set (E m))
    (hU_open : IsOpen U)
    (B_t : Set (E m))
    (hB_sub : B_t ⊆ U)
    (hgt_eq_on : EqOn g_t (fun z : E m => coordECL (φ.symm (unsplit z t))) U)
    (hB_def : B_t = {z : E m | unsplit z t ∈ φ '' A}) :
    μHE[m] (A ∩ {y | f y = t}) =
    ∫⁻ z in B_t,
      ENNReal.ofReal (‖fderiv ℝ f (φ.symm (unsplit z t))‖ /
        |(fderiv ℝ f (φ.symm (unsplit z t))) (eLast : E (m + 1))|) := by
  let implicit_fun : E m → ℝ := fun z => coordECL (φ.symm (unsplit z t))
  have hgt_eq_at : ∀ z ∈ B_t, g_t z = implicit_fun z :=
    fun z hz => hgt_eq_on (hB_sub hz)

  -- B_t is measurable
  have h_image_meas : MeasurableSet (φ '' A) := by
    have h1 : φ '' A = φ.target ∩ (φ.symm ⁻¹' A) := by
      ext y
      constructor
      · rintro ⟨x, hxA, rfl⟩
        have hx_src : x ∈ φ.source := hV_source (hA_sub hxA)
        have h_in_tgt : φ x ∈ φ.target := φ.mapsTo hx_src
        have h_symm : φ.symm (φ x) = x := φ.left_inv hx_src
        have h_goal : φ.symm (φ x) ∈ A := by rw [h_symm]; exact hxA
        exact ⟨h_in_tgt, by simpa [Set.mem_preimage] using h_goal⟩
      · rintro ⟨hy_tgt, hyA⟩
        refine ⟨φ.symm y, hyA, φ.right_inv hy_tgt⟩
    rw [h1]
    have h2 : MeasurableSet φ.target := φ.open_target.measurableSet
    have h3 : ContinuousOn φ.symm φ.target := φ.continuousOn_symm
    let g : φ.target → E (m + 1) := fun x => φ.symm x
    have hg_cont : Continuous g := continuousOn_iff_continuous_restrict.mp h3
    have hg_meas : Measurable g := hg_cont.measurable
    have h4 : MeasurableSet (g ⁻¹' A) := hA.preimage hg_meas
    have h5 : MeasurableSet (Subtype.val '' (g ⁻¹' A)) :=
      MeasurableSet.subtype_image h2 h4
    have h6 : Subtype.val '' (g ⁻¹' A) = φ.target ∩ φ.symm ⁻¹' A := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff]
      constructor
      · rintro ⟨x, hxA, rfl⟩
        have hxt : (x : E (m + 1)) ∈ φ.target := x.prop
        exact ⟨hxt, hxA⟩
      · rintro ⟨hyt, hyA⟩
        refine ⟨(⟨y, hyt⟩ : φ.target), hyA, rfl⟩
    rw [←h6]
    exact h5
  have h_cont_unsplit : Continuous (fun z : E m => unsplit z t) := by
    have h : (fun z : E m => unsplit z t) = fun z => inclEm z + scaleE t := by
      funext z; exact unsplit_eq t z
    rw [h]; fun_prop
  have hB_meas : MeasurableSet B_t := by
    rw [hB_def]; exact h_cont_unsplit.measurable h_image_meas

  -- Set equality
  have h_set_eq : A ∩ {y | f y = t} =
      GraphAreaFormula.graph g_t ∩ GraphAreaFormula.cylinder B_t := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, GraphAreaFormula.graph,
      GraphAreaFormula.cylinder]
    constructor
    · rintro ⟨hyA, hyft⟩
      let z : E m := GraphAreaFormula.proj y
      have h_y_src : y ∈ φ.source := hV_source (hA_sub hyA)
      have h_phi_y : φ y = unsplit z t := by
        have h1 : φ y = projHCL y + f y • (eLast : E (m + 1)) := by rw [hφ_coe]
        rw [h1]
        have h2 : projHCL y = inclEm z := by
          ext i
          by_cases hlt : i.val < m
          · let j : Fin m := ⟨i.val, hlt⟩
            have hi : i = Fin.castSucc j := by apply Fin.ext; simp [j] <;> omega
            rw [hi]
            have h4 : (projHCL y) (Fin.castSucc j) = y (Fin.castSucc j) := by
              simp [projHCL, coordECL, eLast, EuclideanSpace.single_apply, add_apply]
            have h5 : (inclEm z) (Fin.castSucc j) = z j :=
              GraphAreaFormula.F_lin_apply_castSucc (0 : E m →L[ℝ] ℝ) z j
            have h6 : z j = y (Fin.castSucc j) := by
              have h7 : z = GraphAreaFormula.proj y := by rfl
              rw [h7, GraphAreaFormula.proj_apply y j]
            rw [h4, h5, h6]
          · have hlast : i = Fin.last m := by apply Fin.ext; simp [hlt] <;> omega
            rw [hlast]
            have h_coord : coordECL y = y (Fin.last m) := by rfl
            have h_elast1 : (eLast : E (m + 1)) (Fin.last m) = 1 := by
              simp [eLast, EuclideanSpace.single_apply] <;> omega
            have h_projHCL : (projHCL y) (Fin.last m) = 0 := by
              simp [projHCL, h_coord, h_elast1, add_apply] <;> ring
            have h_incl : (inclEm z) (Fin.last m) = 0 := by
              have h_incl_def : inclEm z = GraphAreaFormula.F_lin (0 : E m →L[ℝ] ℝ) z := by rfl
              rw [h_incl_def]
              exact GraphAreaFormula.F_lin_apply_last (0 : E m →L[ℝ] ℝ) z
            rw [h_projHCL, h_incl]
        have h3 : inclEm z + f y • (eLast : E (m + 1)) = unsplit z (f y) := by
          rw [unsplit_eq (f y) z] <;> rfl
        rw [h2, h3, hyft]
      have hzB : z ∈ B_t := by
        rw [hB_def]
        have h5 : φ y ∈ φ '' A := ⟨y, hyA, rfl⟩
        rw [h_phi_y] at h5
        exact h5
      have h6 : φ.symm (unsplit z t) = y := by
        have h7 : φ.symm (φ y) = y := φ.left_inv h_y_src
        rw [h_phi_y] at h7
        exact h7
      have h7 : y (Fin.last m) = g_t z := by
        have h8 : y (Fin.last m) = coordECL y := by rfl
        rw [h8]
        have h9 : coordECL y = coordECL (φ.symm (unsplit z t)) := by rw [h6]
        have h10 : coordECL y = g_t z := by
          calc coordECL y
            = coordECL (φ.symm (unsplit z t)) := h9
          _ = implicit_fun z := by rfl
          _ = g_t z := (hgt_eq_at z hzB).symm
        exact h10
      exact ⟨h7, hzB⟩
    · rintro ⟨h10, h11⟩
      let z : E m := GraphAreaFormula.proj y
      have hzB : z ∈ B_t := h11
      have hzB' : z ∈ {z | unsplit z t ∈ φ '' A} := by
        simpa [hB_def] using hzB
      rcases hzB' with ⟨y', hy'A, hφy'⟩
      have h14 : y' ∈ φ.source := hV_source (hA_sub hy'A)
      have h15 : φ y' = unsplit z t := hφy'
      have h16 : φ.symm (unsplit z t) = y' := by
        have h17 : φ.symm (φ y') = y' := φ.left_inv h14
        rw [h15] at h17
        exact h17
      have h19 : g_t z = coordECL y' := by
        have h191 : g_t z = implicit_fun z := hgt_eq_at z hzB
        have h192 : implicit_fun z = coordECL (φ.symm (unsplit z t)) := by rfl
        have h193 : coordECL (φ.symm (unsplit z t)) = coordECL y' := by rw [h16]
        rw [h191, h192, h193]
      have h21 : f y' = t := by
        have h22 : φ y' = unsplit z t := h15
        have h23 : coordECL (φ y') = f y' := by
          have h24 : φ y' = projHCL y' + f y' • (eLast : E (m + 1)) := by rw [hφ_coe]
          rw [h24]
          simp [coordECL_projHCL, coordECL_eLast] <;> ring
        have h25 : coordECL (unsplit z t) = t := by
          rw [unsplit_eq t z]
          have h26 := coordECL.map_add (inclEm z) (scaleE t : E (m + 1))
          rw [h26]
          have h27 : coordECL (inclEm z) = 0 := by
            simp [coordECL, inclEm, GraphAreaFormula.F_lin_apply_last]
          have h28 : coordECL (scaleE t : E (m + 1)) = t := by
            have h_scaleE : (scaleE t : E (m + 1)) = t • (eLast : E (m + 1)) := by rfl
            rw [h_scaleE]
            have h_smul : coordECL (t • (eLast : E (m + 1))) = t * coordECL (eLast : E (m + 1)) :=
              coordECL.map_smul t (eLast : E (m + 1))
            rw [h_smul, coordECL_eLast] <;> ring
          rw [h27, h28] <;> ring
        have h_eq : f y' = coordECL (unsplit z t) := by rw [←h23, h22]
        rw [h_eq, h25]
      have h_proj_y' : GraphAreaFormula.proj y' = z := by
        have h27 : GraphAreaFormula.proj (φ y') = GraphAreaFormula.proj y' := by
          ext i
          have h1 : (GraphAreaFormula.proj (φ y')) i = (φ y') (Fin.castSucc i) :=
            GraphAreaFormula.proj_apply (φ y') i
          rw [h1]
          have h2 : (φ y') (Fin.castSucc i) = y' (Fin.castSucc i) := by
            have h3 : φ y' = projHCL y' + f y' • (eLast : E (m + 1)) := by rw [hφ_coe]
            rw [h3]
            simp [projHCL, coordECL, eLast, EuclideanSpace.single_apply, add_apply] <;> ring
          rw [h2]
          exact (GraphAreaFormula.proj_apply y' i).symm
        have h28 : GraphAreaFormula.proj (φ y') = z := by
          rw [h15]
          have h29 : GraphAreaFormula.proj (unsplit z t) = z := by
            exact GraphAreaFormula.graphMap_proj (fun _ => t) z
          exact h29
        rw [←h27, h28]
      have h26 : y = y' := by
        ext i
        by_cases hlt2 : i.val < m
        · let j : Fin m := ⟨i.val, hlt2⟩
          have hi : i = Fin.castSucc j := by apply Fin.ext; simp [j] <;> omega
          rw [hi]
          have h31 : y (Fin.castSucc j) = (GraphAreaFormula.proj y) j := by
            exact GraphAreaFormula.proj_apply y j
          have h32 : y' (Fin.castSucc j) = (GraphAreaFormula.proj y') j := by
            exact GraphAreaFormula.proj_apply y' j
          rw [h31, h32, h_proj_y'] <;> rfl
        · have hlast : i = Fin.last m := by apply Fin.ext; simp [hlt2] <;> omega
          rw [hlast]
          have h33 : y (Fin.last m) = g_t z := h10
          have h34 : y' (Fin.last m) = coordECL y' := by rfl
          have h35 : coordECL y' = g_t z := h19.symm
          rw [h33, h34, h35]
      exact ⟨by rw [h26]; exact hy'A, by rw [h26]; exact h21⟩

  -- Derivative equality on B_t (since g_t = implicit_fun on open U ⊇ B_t)
  have h_fderiv_eq : ∀ z ∈ B_t,
      fderiv ℝ g_t z = fderiv ℝ implicit_fun z := by
    intro z hz
    have hzU : z ∈ U := hB_sub hz
    have h_nhds : U ∈ nhds z := hU_open.mem_nhds hzU
    have h_diff : DifferentiableAt ℝ g_t z :=
      hgt_diff.differentiable (by norm_num) |>.differentiableAt
    have h_eq : implicit_fun =ᶠ[nhds z] g_t :=
      (hgt_eq_on.eventuallyEq_of_mem h_nhds).symm
    have h : HasFDerivAt implicit_fun (fderiv ℝ g_t z) z :=
      h_diff.hasFDerivAt.congr_of_eventuallyEq h_eq
    exact h.fderiv.symm

  -- Apply graph_area_smooth
  have h_area : μHE[m] (GraphAreaFormula.graph g_t ∩ GraphAreaFormula.cylinder B_t) =
      ∫⁻ z in B_t, ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ g_t z‖ ^ 2)) :=
    GraphAreaFormula.graph_area_smooth g_t hgt_diff hgt_diff B_t hB_meas

  -- Pointwise identity
  have h_pointwise : ∀ z ∈ B_t,
      ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ g_t z‖ ^ 2)) =
      ENNReal.ofReal (‖fderiv ℝ f (φ.symm (unsplit z t))‖ /
        |(fderiv ℝ f (φ.symm (unsplit z t))) (eLast : E (m + 1))|) := by
    intro z hz
    have h13 : unsplit z t ∈ φ.target := by
      have hzB' : z ∈ {z | unsplit z t ∈ φ '' A} := by simpa [hB_def] using hz
      rcases hzB' with ⟨y', hy'A, hφy'⟩
      have h14 : y' ∈ φ.source := hV_source (hA_sub hy'A)
      have h15 : φ y' ∈ φ.target := φ.mapsTo h14
      rw [hφy'] at h15
      exact h15
    have h14 : φ.symm (unsplit z t) ∈ V := by
      have hzB' : z ∈ {z | unsplit z t ∈ φ '' A} := by simpa [hB_def] using hz
      rcases hzB' with ⟨y', hy'A, hφy'⟩
      have h15 : φ.symm (unsplit z t) = y' := by
        have h16 : y' ∈ φ.source := hV_source (hA_sub hy'A)
        have h17 : φ.symm (φ y') = y' := φ.left_inv h16
        rw [hφy'] at h17
        exact h17
      exact h15 ▸ hA_sub hy'A
    rw [h_fderiv_eq z hz]
    exact (implicit_derivative_identity f hf φ hφ_coe hV_source hV_reg t z h13 h14).symm

  have h_ae : ∀ᵐ (z : E m) ∂(volume.restrict B_t),
      ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ g_t z‖ ^ 2)) =
      ENNReal.ofReal (‖fderiv ℝ f (φ.symm (unsplit z t))‖ /
        |(fderiv ℝ f (φ.symm (unsplit z t))) (eLast : E (m + 1))|) := by
    filter_upwards [ae_restrict_mem hB_meas] with z hz
    exact h_pointwise z hz

  have h_integral : ∫⁻ z in B_t, ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ g_t z‖ ^ 2)) =
      ∫⁻ z in B_t, ENNReal.ofReal (‖fderiv ℝ f (φ.symm (unsplit z t))‖ /
        |(fderiv ℝ f (φ.symm (unsplit z t))) (eLast : E (m + 1))|) :=
    lintegral_congr_ae h_ae

  rw [h_set_eq, h_area, h_integral]

end Geometry
