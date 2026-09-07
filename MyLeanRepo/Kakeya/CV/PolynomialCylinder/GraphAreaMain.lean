import MyLeanRepo.Kakeya.CV.PolynomialCylinder.GraphAreaBounds

/-!
# Graph area: main theorem

Assembles the graph area inequality from convex-region bounds and a countable
ball cover. Given a graph lying in a polynomial zero set with non-vanishing
z-gradient, its directional surface area is bounded by `12 * planeConstant`
times the volume of its projection onto the xy-plane.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

-- Helper lemmas
lemma proj2_graphMap_eq (f : R2 → ℝ) (y : R2) : proj2 (graphMap f y) = y := by
  ext i
  fin_cases i <;> simp [proj2, graphMap]

lemma graphMap_proj2_eq {U : Set R2} {f : R2 → ℝ} {x : R3} (hx : x ∈ zGraph U f) :
    graphMap f (proj2 x) = x := by
  ext i
  fin_cases i
  · simp [graphMap, proj2]
  · simp [graphMap, proj2]
  · have h : x 2 = f (proj2 x) := hx.2
    simpa [graphMap] using h.symm

lemma graph_area_inequality_z {U : Set R2} {f : R2 → ℝ} {p : MvPolynomial (Fin 3) ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (h_zero : zGraph U f ⊆ polynomialZeroSet p)
    (h_reg : ∀ x ∈ zGraph U f, (polynomialGradient p x) 2 ≠ 0)
    {A : Set R3} (hA : A ⊆ zGraph U f)
    (hB_meas : MeasurableSet (proj2 '' A)) :
    directionalSurfaceArea e3 p A ≤ 12 * planeConstant * volume (proj2 '' A) := by
  let B := proj2 '' A
  let w := graphAreaW p

  -- Convert h_zero and h_reg to pointwise conditions on U
  have h_zero' : ∀ y ∈ U, polynomialValue p (graphMap f y) = 0 := by
    intro y hy
    have h_proj : proj2 (graphMap f y) = y := proj2_graphMap_eq f y
    have h1 : graphMap f y ∈ zGraph U f := by
      simp only [zGraph, Set.mem_setOf_eq]
      constructor
      · rw [h_proj]; exact hy
      · have h2 : (graphMap f y) 2 = f y := by simp [graphMap]
        rw [h2, h_proj]
    have h2 : graphMap f y ∈ polynomialZeroSet p := h_zero h1
    simpa [polynomialZeroSet] using h2

  have h_reg' : ∀ y ∈ U, (polynomialGradient p (graphMap f y)) 2 ≠ 0 := by
    intro y hy
    have h_proj : proj2 (graphMap f y) = y := proj2_graphMap_eq f y
    have h1 : graphMap f y ∈ zGraph U f := by
      simp only [zGraph, Set.mem_setOf_eq]
      constructor
      · rw [h_proj]; exact hy
      · have h2 : (graphMap f y) 2 = f y := by simp [graphMap]
        rw [h2, h_proj]
    exact h_reg (graphMap f y) h1

  have hf' : DifferentiableOn ℝ f U := hf.differentiableOn (by norm_num)

  -- A = graphMap f '' B
  have hA_eq : A = graphMap f '' B := by
    apply Set.Subset.antisymm
    · intro x hx
      have h_x_in : x ∈ zGraph U f := hA hx
      have h_eq : graphMap f (proj2 x) = x := graphMap_proj2_eq h_x_in
      have h_y_in_B : proj2 x ∈ B := ⟨x, hx, rfl⟩
      exact ⟨proj2 x, h_y_in_B, h_eq⟩
    · intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      rcases hy with ⟨x, hx, hpy⟩
      have h_x_in : x ∈ zGraph U f := hA hx
      have h_eq : graphMap f (proj2 x) = x := graphMap_proj2_eq h_x_in
      have h_zy : graphMap f y = x := by rw [←hpy]; exact h_eq
      rw [h_zy]; exact hx

  -- Continuity of graphMap f on U
  have h_cont_graphMap : ContinuousOn (graphMap f) U := by
    have h1 : ContinuousOn f U := hf'.continuousOn
    have h_proj0 : Continuous (fun x : R2 => x 0) := by fun_prop
    have h_proj1 : Continuous (fun x : R2 => x 1) := by fun_prop
    have h_vec : ContinuousOn (fun x : R2 => ![x 0, x 1, f x]) U := by
      rw [continuousOn_pi]
      intro i
      fin_cases i
      · exact h_proj0.continuousOn
      · exact h_proj1.continuousOn
      · exact h1
    have h_equiv : Continuous (EuclideanSpace.equiv (Fin 3) ℝ).symm := by fun_prop
    exact h_equiv.comp_continuousOn h_vec

  -- B ⊆ U
  have hB_sub_U : B ⊆ U := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact (hA hx).1

  -- directionalSurfaceArea = ∫ in A, w
  have h_dir : directionalSurfaceArea e3 p A = ∫⁻ x in A, w x ∂μH[2] := by rfl
  have h_proj_image : proj2 '' (graphMap f '' B) = B := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨z, ⟨x, hx, hz⟩, hpy⟩
      have h1 : proj2 z = x := by
        rw [←hz]
        exact proj2_graphMap_eq f x
      have h2 : y = x := by
        rw [←hpy, h1]
      exact h2 ▸ hx
    · intro hy
      refine ⟨graphMap f y, ⟨y, hy, rfl⟩, ?_⟩
      exact proj2_graphMap_eq f y
  rw [h_dir, hA_eq]
  rw [h_proj_image]

  -- Continuity of fderiv on U (from ContDiffOn ℝ 1)
  have h_fderiv_cont : ContinuousOn (fderiv ℝ f) U :=
    (hf.fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn

  let gx : R2 → ℝ := fun y => (fderiv ℝ f y e02)^2
  let gy : R2 → ℝ := fun y => (fderiv ℝ f y e12)^2

  have h_eval0 : Continuous (fun (g : R2 →L[ℝ] ℝ) => g e02) := by fun_prop
  have h_eval1 : Continuous (fun (g : R2 →L[ℝ] ℝ) => g e12) := by fun_prop
  have h_gx_cont : ContinuousOn gx U := by
    have h2 : ContinuousOn (fun y => fderiv ℝ f y e02) U :=
      h_eval0.comp_continuousOn h_fderiv_cont
    exact h2.pow 2
  have h_gy_cont : ContinuousOn gy U := by
    have h2 : ContinuousOn (fun y => fderiv ℝ f y e12) U :=
      h_eval1.comp_continuousOn h_fderiv_cont
    exact h2.pow 2

  -- Define open gradient regions
  let Sx_open : Set R2 := {y ∈ U | gx y > (81 / 100 : ℝ) * gy y ∧
                                  gx y > (9025 / 10000 : ℝ)}
  let Sy_open : Set R2 := {y ∈ U | gy y > (81 / 100 : ℝ) * gx y ∧
                                  gy y > (9025 / 10000 : ℝ)}
  let W0 : Set R2 := {y ∈ U | gx y < (3 / 2 : ℝ) ∧ gy y < (3 / 2 : ℝ)}

  -- These sets are open
  have hSx_open : IsOpen Sx_open := by
    have h1 : ContinuousOn (fun y : R2 => gx y - (81 / 100 : ℝ) * gy y) U :=
      ContinuousOn.sub h_gx_cont (h_gy_cont.const_mul (81 / 100 : ℝ))
    have h3 : IsOpen (U ∩ (fun y : R2 => gx y - (81 / 100 : ℝ) * gy y) ⁻¹' (Ioi 0)) :=
      h1.isOpen_inter_preimage hU isOpen_Ioi
    have h4 : IsOpen (U ∩ gx ⁻¹' (Ioi (9025 / 10000 : ℝ))) :=
      h_gx_cont.isOpen_inter_preimage hU isOpen_Ioi
    have h5 : Sx_open = (U ∩ (fun y : R2 => gx y - (81 / 100 : ℝ) * gy y) ⁻¹' (Ioi 0)) ∩
                        (U ∩ gx ⁻¹' (Ioi (9025 / 10000 : ℝ))) := by
      ext y; simp [Sx_open, Set.mem_setOf_eq, sub_pos] <;> aesop
    rw [h5]
    exact h3.inter h4

  have hSy_open : IsOpen Sy_open := by
    have h1 : ContinuousOn (fun y : R2 => gy y - (81 / 100 : ℝ) * gx y) U :=
      ContinuousOn.sub h_gy_cont (h_gx_cont.const_mul (81 / 100 : ℝ))
    have h3 : IsOpen (U ∩ (fun y : R2 => gy y - (81 / 100 : ℝ) * gx y) ⁻¹' (Ioi 0)) :=
      h1.isOpen_inter_preimage hU isOpen_Ioi
    have h4 : IsOpen (U ∩ gy ⁻¹' (Ioi (9025 / 10000 : ℝ))) :=
      h_gy_cont.isOpen_inter_preimage hU isOpen_Ioi
    have h5 : Sy_open = (U ∩ (fun y : R2 => gy y - (81 / 100 : ℝ) * gx y) ⁻¹' (Ioi 0)) ∩
                        (U ∩ gy ⁻¹' (Ioi (9025 / 10000 : ℝ))) := by
      ext y; simp [Sy_open, Set.mem_setOf_eq, sub_pos] <;> aesop
    rw [h5]
    exact h3.inter h4

  have hW0_open : IsOpen W0 := by
    have h3 : IsOpen (U ∩ gx ⁻¹' (Iio (3 / 2 : ℝ))) :=
      (continuousOn_open_iff hU).mp h_gx_cont (Iio (3 / 2 : ℝ)) isOpen_Iio
    have h4 : IsOpen (U ∩ gy ⁻¹' (Iio (3 / 2 : ℝ))) :=
      (continuousOn_open_iff hU).mp h_gy_cont (Iio (3 / 2 : ℝ)) isOpen_Iio
    have h5 : W0 = (U ∩ gx ⁻¹' (Iio (3 / 2 : ℝ))) ∩ (U ∩ gy ⁻¹' (Iio (3 / 2 : ℝ))) := by
      ext y; simp [W0, Set.mem_setOf_eq] <;> tauto
    rw [h5]
    exact h3.inter h4

  -- Cover: U ⊆ Sx_open ∪ Sy_open ∪ W0
  have h_cover : U ⊆ Sx_open ∪ Sy_open ∪ W0 := by
    intro y hy
    set a : ℝ := gx y with ha
    set b : ℝ := gy y with hb
    have ha_nonneg : 0 ≤ a := by positivity
    have hb_nonneg : 0 ≤ b := by positivity
    by_cases h_x : a > (81 / 100 : ℝ) * b ∧ a > (9025 / 10000 : ℝ)
    · have h_in : y ∈ Sx_open := by
        simp only [Sx_open, Set.mem_setOf_eq]; exact ⟨hy, h_x.1, h_x.2⟩
      exact Or.inl (Or.inl h_in)
    · by_cases h_y : b > (81 / 100 : ℝ) * a ∧ b > (9025 / 10000 : ℝ)
      · have h_in : y ∈ Sy_open := by
          simp only [Sy_open, Set.mem_setOf_eq]; exact ⟨hy, h_y.1, h_y.2⟩
        exact Or.inl (Or.inr h_in)
      · -- Not in Sx_open or Sy_open: show a < 3/2 and b < 3/2
        have h_not_x : ¬(a > (81 / 100 : ℝ) * b ∧ a > (9025 / 10000 : ℝ)) := h_x
        have h_not_y : ¬(b > (81 / 100 : ℝ) * a ∧ b > (9025 / 10000 : ℝ)) := h_y
        have h_a_lt : a < (3 / 2 : ℝ) := by
          by_contra h_a_ge
          have h_a_ge' : a ≥ (3 / 2 : ℝ) := by linarith
          have h1 : a > (9025 / 10000 : ℝ) := by norm_num at * <;> linarith
          have h2 : a > (81 / 100 : ℝ) * b := by
            have h3 : b ≤ a := by
              by_contra h4; have h5 : b > a := by linarith
              have h6 : b > (9025 / 10000 : ℝ) := by linarith
              have h7 : b > (81 / 100 : ℝ) * a := by
                have h8 : (81 / 100 : ℝ) * a < a := by nlinarith
                linarith
              exact h_not_y ⟨h7, h6⟩
            nlinarith
          exact h_not_x ⟨h2, h1⟩
        have h_b_lt : b < (3 / 2 : ℝ) := by
          by_contra h_b_ge
          have h_b_ge' : b ≥ (3 / 2 : ℝ) := by linarith
          have h1 : b > (9025 / 10000 : ℝ) := by norm_num at * <;> linarith
          have h2 : b > (81 / 100 : ℝ) * a := by
            have h3 : a ≤ b := by
              by_contra h4; have h5 : a > b := by linarith
              have h6 : a > (9025 / 10000 : ℝ) := by linarith
              have h7 : a > (81 / 100 : ℝ) * b := by
                have h8 : (81 / 100 : ℝ) * b < b := by nlinarith
                linarith
              exact h_not_x ⟨h7, h6⟩
            nlinarith
          exact h_not_y ⟨h2, h1⟩
        have h_in : y ∈ W0 := by
          simp only [W0, Set.mem_setOf_eq]; exact ⟨hy, h_a_lt, h_b_lt⟩
        exact Or.inr h_in

  -- Decompose B into measurable sets
  let Bx := B ∩ Sx_open
  let By := B ∩ Sy_open
  let B0 := B \ (Sx_open ∪ Sy_open)
  have hBx_meas : MeasurableSet Bx := hB_meas.inter hSx_open.measurableSet
  have hBy_meas : MeasurableSet By := hB_meas.inter hSy_open.measurableSet
  have hB0_meas : MeasurableSet B0 := hB_meas.diff (hSx_open.measurableSet.union hSy_open.measurableSet)
  have hB0_sub_W0 : B0 ⊆ W0 := by
    intro x hx
    have h_x_in_B : x ∈ B := hx.1
    have h_x_not_in : x ∉ Sx_open ∪ Sy_open := hx.2
    have h_x_in_U : x ∈ U := hB_sub_U h_x_in_B
    have h : x ∈ (Sx_open ∪ Sy_open) ∪ W0 := h_cover h_x_in_U
    rcases h with (h | h)
    · rcases h with (h | h)
      · exact False.elim (h_x_not_in (Or.inl h))
      · exact False.elim (h_x_not_in (Or.inr h))
    · exact h

  have hB_decomp : B = Bx ∪ By ∪ B0 := by
    ext x
    simp only [Bx, By, B0, Set.mem_union, Set.mem_diff, Set.mem_inter_iff]
    tauto

  have h_image_decomp : graphMap f '' B = (graphMap f '' Bx) ∪ (graphMap f '' By) ∪ (graphMap f '' B0) := by
    rw [hB_decomp, Set.image_union, Set.image_union] <;> rfl

  -- Subadditivity of lintegral
  set S1 := graphMap f '' Bx
  set S2 := graphMap f '' By
  set S3 := graphMap f '' B0
  have h_subadd : ∫⁻ x in graphMap f '' B, w x ∂μH[2] ≤
      ∫⁻ x in S1, w x ∂μH[2] + ∫⁻ x in S2, w x ∂μH[2] + ∫⁻ x in S3, w x ∂μH[2] := by
    rw [h_image_decomp]
    have h_union_eq : (S1 ∪ S2 ∪ S3) = S1 ∪ (S2 ∪ S3) := by
      ext x; simp [Set.mem_union] <;> tauto
    rw [h_union_eq]
    have h1 : ∫⁻ x in S1 ∪ (S2 ∪ S3), w x ∂μH[2] ≤
        ∫⁻ x in S1, w x ∂μH[2] + ∫⁻ x in (S2 ∪ S3), w x ∂μH[2] := by
      exact lintegral_union_le w S1 (S2 ∪ S3)
    have h2 : ∫⁻ x in (S2 ∪ S3), w x ∂μH[2] ≤
        ∫⁻ x in S2, w x ∂μH[2] + ∫⁻ x in S3, w x ∂μH[2] := by
      exact lintegral_union_le w S2 S3
    calc ∫⁻ x in S1 ∪ (S2 ∪ S3), w x ∂μH[2]
      ≤ ∫⁻ x in S1, w x ∂μH[2] + ∫⁻ x in (S2 ∪ S3), w x ∂μH[2] := h1
    _ ≤ ∫⁻ x in S1, w x ∂μH[2] + (∫⁻ x in S2, w x ∂μH[2] + ∫⁻ x in S3, w x ∂μH[2]) := by gcongr
    _ = ∫⁻ x in S1, w x ∂μH[2] + ∫⁻ x in S2, w x ∂μH[2] + ∫⁻ x in S3, w x ∂μH[2] := by ring

  -- Bound for Bx using apply_cover_bound with graph_area_bound_on_convex
  have h_boundx : ∀ (V : Set R2), Convex ℝ V → V ⊆ Sx_open → ∀ (T : Set R2), T ⊆ V → MeasurableSet T →
      ∫⁻ x in graphMap f '' T, w x ∂μH[2] ≤ (4 : ENNReal) * planeConstant * volume T := by
    intro V hV_conv hV_sub T hT_sub hT_meas
    have h1 : ∀ y ∈ V, (fderiv ℝ f y e02)^2 ≥ (81 / 100 : ℝ) * (fderiv ℝ f y e12)^2 := by
      intro y hy
      have h : y ∈ Sx_open := hV_sub hy
      exact (h.2.1).le
    have h2 : ∀ y ∈ V, (fderiv ℝ f y e02)^2 ≥ (9025 / 10000 : ℝ) := by
      intro y hy
      have h : y ∈ Sx_open := hV_sub hy
      exact (h.2.2).le
    have hV_sub_U : V ⊆ U := subset_trans hV_sub (fun x hx => hx.1)
    exact graph_area_bound_on_convex hU hf' V hV_conv hV_sub_U h1 h2 h_zero' h_reg' T hT_sub hT_meas

  have hx_bound : ∫⁻ x in graphMap f '' Bx, w x ∂μH[2] ≤ (4 : ENNReal) * planeConstant * volume Bx :=
    apply_cover_bound hSx_open w Bx (show Bx ⊆ Sx_open from by simp [Bx]) hBx_meas (4 : ENNReal) h_boundx

  -- Bound for By using apply_cover_bound with graph_area_bound_on_convex'
  have h_boundy : ∀ (V : Set R2), Convex ℝ V → V ⊆ Sy_open → ∀ (T : Set R2), T ⊆ V → MeasurableSet T →
      ∫⁻ x in graphMap f '' T, w x ∂μH[2] ≤ (4 : ENNReal) * planeConstant * volume T := by
    intro V hV_conv hV_sub T hT_sub hT_meas
    have h1 : ∀ y ∈ V, (fderiv ℝ f y e12)^2 ≥ (81 / 100 : ℝ) * (fderiv ℝ f y e02)^2 := by
      intro y hy
      have h : y ∈ Sy_open := hV_sub hy
      exact (h.2.1).le
    have h2 : ∀ y ∈ V, (fderiv ℝ f y e12)^2 ≥ (9025 / 10000 : ℝ) := by
      intro y hy
      have h : y ∈ Sy_open := hV_sub hy
      exact (h.2.2).le
    have hV_sub_U : V ⊆ U := subset_trans hV_sub (fun x hx => hx.1)
    exact graph_area_bound_on_convex' hU hf' V hV_conv hV_sub_U h1 h2 h_zero' h_reg' T hT_sub hT_meas

  have hy_bound : ∫⁻ x in graphMap f '' By, w x ∂μH[2] ≤ (4 : ENNReal) * planeConstant * volume By :=
    apply_cover_bound hSy_open w By (show By ⊆ Sy_open from by simp [By]) hBy_meas (4 : ENNReal) h_boundy

  -- Bound for B0 using relaxed flat bound via flat_region_bound_gen (factor 4)
  have h_bound0 : ∀ (V : Set R2), Convex ℝ V → V ⊆ W0 → ∀ (T : Set R2), T ⊆ V → MeasurableSet T →
      ∫⁻ x in graphMap f '' T, w x ∂μH[2] ≤ (4 : ENNReal) * planeConstant * volume T := by
    intro V hV_conv hV_sub T hT_sub hT_meas
    have hfx : ∀ y ∈ V, (fderiv ℝ f y e02)^2 ≤ (3 / 2 : ℝ) := by
      intro y hy
      have h : y ∈ W0 := hV_sub hy
      exact h.2.1.le
    have hfy : ∀ y ∈ V, (fderiv ℝ f y e12)^2 ≤ (3 / 2 : ℝ) := by
      intro y hy
      have h : y ∈ W0 := hV_sub hy
      exact h.2.2.le
    have hV_sub_U : V ⊆ U := subset_trans hV_sub (fun x hx => hx.1)
    have h_main := flat_region_bound_gen (p := p) hU hf' V hV_conv hV_sub_U
      (3 / 2 : ℝ) (3 / 2 : ℝ) (by norm_num) (by norm_num) hfx hfy T hT_sub hT_meas
    have h_factor : ENNReal.ofReal (1 + (3 / 2 : ℝ) + (3 / 2 : ℝ)) = (4 : ENNReal) := by
      norm_num
    rw [h_factor] at h_main
    exact h_main

  have h0_bound : ∫⁻ x in graphMap f '' B0, w x ∂μH[2] ≤ (4 : ENNReal) * planeConstant * volume B0 :=
    apply_cover_bound hW0_open w B0 hB0_sub_W0 hB0_meas (4 : ENNReal) h_bound0

  -- Each Bi ⊆ B, so volume Bi ≤ volume B
  have h_volBx : volume Bx ≤ volume B := volume.mono (by simp [Bx])
  have h_volBy : volume By ≤ volume B := volume.mono (by simp [By])
  have h_volB0 : volume B0 ≤ volume B := volume.mono (by simp [B0])
  have h_vol : volume Bx + volume By + volume B0 ≤ 3 * volume B := by
    calc volume Bx + volume By + volume B0
      ≤ volume B + volume By + volume B0 := by gcongr
    _ ≤ volume B + volume B + volume B0 := by gcongr
    _ ≤ volume B + volume B + volume B := by gcongr
    _ = 3 * volume B := by
      have h6 : volume B + volume B + volume B = (3 : ENNReal) * volume B := by
        have h7 : volume B + volume B + volume B = (1 + 1 + 1 : ENNReal) * volume B := by
          rw [add_mul, add_mul] <;> simp
        rw [h7] <;> norm_cast
      exact h6

  calc ∫⁻ x in graphMap f '' B, w x ∂μH[2]
    ≤ ∫⁻ x in S1, w x ∂μH[2] + ∫⁻ x in S2, w x ∂μH[2] + ∫⁻ x in S3, w x ∂μH[2] := h_subadd
  _ ≤ (4 : ENNReal) * planeConstant * volume Bx +
        (4 : ENNReal) * planeConstant * volume By +
        (4 : ENNReal) * planeConstant * volume B0 := by gcongr
  _ = (4 : ENNReal) * planeConstant * (volume Bx + volume By + volume B0) := by
    rw [mul_add, mul_add] <;> ring
  _ ≤ (4 : ENNReal) * planeConstant * (3 * volume B) := by gcongr
  _ = 12 * planeConstant * volume (proj2 '' A) := by
    dsimp only [B]
    have h1 : (4 : ENNReal) * (3 : ENNReal) = (12 : ENNReal) := by norm_num
    have h2 : (4 : ENNReal) * planeConstant * (3 * volume (proj2 '' A)) =
        (4 : ENNReal) * (3 : ENNReal) * planeConstant * volume (proj2 '' A) := by
      simp [mul_assoc, mul_comm, mul_left_comm]
      <;> ac_rfl
    rw [h2, h1]
    <;> rfl

end Kakeya.CV
