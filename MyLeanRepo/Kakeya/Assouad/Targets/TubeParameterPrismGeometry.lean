import MyLeanRepo.Kakeya.Assouad.Statements

/-!
WZ2 parameter non-concentration: convexity and quadratic volume of the affine
tube-parameter prism.
-/

open MeasureTheory

namespace Kakeya.Assouad

theorem tube_parameter_prism_geometry :
    TubeParameterPrismGeometryStatement := by
  intro params radius hr

  have h_point3 : ∀ (x y z : ℝ) (i : Fin 3),
      (point3 x y z) i =
        match i with
        | 0 => x
        | 1 => y
        | 2 => z := by
    intro x y z i
    fin_cases i <;> simp [point3] <;> ring

  -- Part 1: Convexity
  let f1 : Point3 →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 2
  let f2 : Point3 →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 0 - params.c • EuclideanSpace.projₗ 2
  let f3 : Point3 →ₗ[ℝ] ℝ := EuclideanSpace.projₗ 1 - params.d • EuclideanSpace.projₗ 2

  let S1 : Set Point3 := {p | p 2 ∈ Set.Icc (-1 : ℝ) 1}
  let S2 : Set Point3 := {p | p 0 - params.c * p 2 ∈ Set.Icc (params.a - radius) (params.a + radius)}
  let S3 : Set Point3 := {p | p 1 - params.d * p 2 ∈ Set.Icc (params.b - radius) (params.b + radius)}

  have hS1 : S1 = (f1.toAffineMap) ⁻¹' Set.Icc (-1 : ℝ) 1 := by
    ext p; simp [S1, f1]
  have hS2 : S2 = (f2.toAffineMap) ⁻¹' Set.Icc (params.a - radius) (params.a + radius) := by
    ext p; simp [S2, f2]
  have hS3 : S3 = (f3.toAffineMap) ⁻¹' Set.Icc (params.b - radius) (params.b + radius) := by
    ext p; simp [S3, f3]

  have h1 : Convex ℝ S1 := by
    rw [hS1]; exact Convex.affine_preimage f1.toAffineMap (convex_Icc _ _)
  have h2 : Convex ℝ S2 := by
    rw [hS2]; exact Convex.affine_preimage f2.toAffineMap (convex_Icc _ _)
  have h3 : Convex ℝ S3 := by
    rw [hS3]; exact Convex.affine_preimage f3.toAffineMap (convex_Icc _ _)

  have h_set_eq : tubeParameterPrism params radius = S1 ∩ S2 ∩ S3 := by
    ext p
    have h_forward : p ∈ tubeParameterPrism params radius → p ∈ S1 ∩ S2 ∩ S3 := by
      rintro ⟨hz, hx, hy⟩
      have hx1 : params.a - radius ≤ p 0 - params.c * p 2 := by
        have h : -radius ≤ p 0 - (params.a + params.c * p 2) := (abs_le.mp hx).1
        linarith
      have hx2 : p 0 - params.c * p 2 ≤ params.a + radius := by
        have h : p 0 - (params.a + params.c * p 2) ≤ radius := (abs_le.mp hx).2
        linarith
      have hy1 : params.b - radius ≤ p 1 - params.d * p 2 := by
        have h : -radius ≤ p 1 - (params.b + params.d * p 2) := (abs_le.mp hy).1
        linarith
      have hy2 : p 1 - params.d * p 2 ≤ params.b + radius := by
        have h : p 1 - (params.b + params.d * p 2) ≤ radius := (abs_le.mp hy).2
        linarith
      exact ⟨⟨hz, ⟨hx1, hx2⟩⟩, ⟨hy1, hy2⟩⟩
    have h_backward : p ∈ S1 ∩ S2 ∩ S3 → p ∈ tubeParameterPrism params radius := by
      rintro ⟨⟨hz, ⟨hx1, hx2⟩⟩, ⟨hy1, hy2⟩⟩
      have hx' : |p 0 - (params.a + params.c * p 2)| ≤ radius := by
        have h_eq : p 0 - (params.a + params.c * p 2) = p 0 - params.c * p 2 - params.a := by ring
        rw [h_eq, abs_le] <;> constructor <;> linarith
      have hy' : |p 1 - (params.b + params.d * p 2)| ≤ radius := by
        have h_eq : p 1 - (params.b + params.d * p 2) = p 1 - params.d * p 2 - params.b := by ring
        rw [h_eq, abs_le] <;> constructor <;> linarith
      exact ⟨hz, hx', hy'⟩
    constructor
    · exact h_forward
    · exact h_backward

  have h_conv : Convex ℝ (tubeParameterPrism params radius) := by
    rw [h_set_eq]
    exact (h1.inter h2).inter h3

  -- Part 2: Volume bound
  let a : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => -radius
    | 1 => -radius
    | 2 => -1
  let b : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => radius
    | 1 => radius
    | 2 => 1
  let M : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, params.c; 0, 1, params.d; 0, 0, 1]

  -- EuclideanSpace equiv for box volume transfer
  let e_eq : Point3 ≃L[ℝ] (Fin 3 → ℝ) := EuclideanSpace.equiv (Fin 3) ℝ
  have h_e_eq_id : ∀ (p : Point3) (i : Fin 3), e_eq p i = p i := by
    intro p i
    rfl
  have h_mp : MeasurePreserving e_eq volume volume :=
    PiLp.volume_preserving_ofLp (Fin 3)

  let B : Set Point3 := {p | p 0 ∈ Set.Icc (-radius) radius ∧ p 1 ∈ Set.Icc (-radius) radius ∧ p 2 ∈ Set.Icc (-1) 1}

  have hB_def : ∀ (p : Point3), p ∈ B ↔
      p 0 ∈ Set.Icc (-radius) radius ∧
      p 1 ∈ Set.Icc (-radius) radius ∧
      p 2 ∈ Set.Icc (-1) 1 := by
    intro p
    simp [B] <;> rfl

  have h_preimage_B : e_eq ⁻¹' (Set.Icc a b : Set (Fin 3 → ℝ)) = B := by
    ext p
    have h_iff : e_eq p ∈ Set.Icc a b ↔ p ∈ B := by
      simp only [Set.mem_Icc]
      constructor
      · rintro ⟨h_left, h_right⟩
        have h01 : a 0 ≤ p 0 := by simpa [h_e_eq_id] using h_left 0
        have h02 : p 0 ≤ b 0 := by simpa [h_e_eq_id] using h_right 0
        have h11 : a 1 ≤ p 1 := by simpa [h_e_eq_id] using h_left 1
        have h12 : p 1 ≤ b 1 := by simpa [h_e_eq_id] using h_right 1
        have h21 : a 2 ≤ p 2 := by simpa [h_e_eq_id] using h_left 2
        have h22 : p 2 ≤ b 2 := by simpa [h_e_eq_id] using h_right 2
        rw [hB_def p]
        simp [a, b, h01, h02, h11, h12, h21, h22] <;> tauto
      · intro h
        rw [hB_def p] at h
        rcases h with ⟨h0, h1, h2⟩
        have h01 : -radius ≤ p 0 := h0.1
        have h02 : p 0 ≤ radius := h0.2
        have h11 : -radius ≤ p 1 := h1.1
        have h12 : p 1 ≤ radius := h1.2
        have h21 : -1 ≤ p 2 := h2.1
        have h22 : p 2 ≤ 1 := h2.2
        constructor
        · intro i
          fin_cases i <;> simp [a, h_e_eq_id, h01, h11, h21] <;> linarith
        · intro i
          fin_cases i <;> simp [b, h_e_eq_id, h02, h12, h22] <;> linarith
    simpa [Set.mem_preimage] using h_iff

  have h_box_vol : volume B = ENNReal.ofReal (8 * radius ^ 2) := by
    have h1 : volume B = volume (e_eq ⁻¹' (Set.Icc a b : Set (Fin 3 → ℝ))) := by
      rw [h_preimage_B]
    rw [h1]
    have h_Icc_meas : MeasurableSet (Set.Icc a b : Set (Fin 3 → ℝ)) :=
      isCompact_Icc.measurableSet
    have h2 : volume (e_eq ⁻¹' (Set.Icc a b : Set (Fin 3 → ℝ))) =
        volume (Set.Icc a b : Set (Fin 3 → ℝ)) :=
      h_mp.measure_preimage h_Icc_meas.nullMeasurableSet
    rw [h2]
    rw [Real.volume_Icc_pi]
    have h_pos0 : 0 ≤ b 0 - a 0 := by simp [a, b] <;> linarith
    have h_pos1 : 0 ≤ b 1 - a 1 := by simp [a, b] <;> linarith
    have h_val : (b 0 - a 0) * (b 1 - a 1) * (b 2 - a 2) = 8 * radius ^ 2 := by
      simp [a, b] <;> ring
    have h_assoc : (b 0 - a 0) * (b 1 - a 1) * (b 2 - a 2) =
        (b 0 - a 0) * ((b 1 - a 1) * (b 2 - a 2)) := by ring
    have h_goal : ENNReal.ofReal ((b 0 - a 0) * ((b 1 - a 1) * (b 2 - a 2))) =
        (∏ i : Fin 3, ENNReal.ofReal (b i - a i)) := by
      rw [ENNReal.ofReal_mul (hp := h_pos0), ENNReal.ofReal_mul (hp := h_pos1)]
      <;> simp [Fin.prod_univ_succ]
      <;> rfl
    have h_eq1 : ENNReal.ofReal ((b 0 - a 0) * ((b 1 - a 1) * (b 2 - a 2))) =
        ENNReal.ofReal ((b 0 - a 0) * (b 1 - a 1) * (b 2 - a 2)) := by
      apply congr_arg; exact h_assoc.symm
    have h_eq2 : ENNReal.ofReal ((b 0 - a 0) * (b 1 - a 1) * (b 2 - a 2)) =
        ENNReal.ofReal (8 * radius ^ 2) := by
      apply congr_arg; exact h_val
    exact h_goal.symm.trans (h_eq1.trans h_eq2)

  let L : Point3 →ₗ[ℝ] Point3 :=
    { toFun := fun p => point3 (p 0 + params.c * p 2) (p 1 + params.d * p 2) (p 2)
      map_add' := by
        intro x y
        ext i
        fin_cases i <;> simp [h_point3] <;> ring
      map_smul' := by
        intro c x
        ext i
        fin_cases i <;> simp [h_point3] <;> ring }

  let v : Point3 := point3 params.a params.b 0
  let e : Point3 → Point3 := fun p => v + L p

  have hv0 : v 0 = params.a := by simp [v, h_point3]
  have hv1 : v 1 = params.b := by simp [v, h_point3]
  have hv2 : v 2 = 0 := by simp [v, h_point3]
  have hL0 : ∀ (p : Point3), (L p) 0 = p 0 + params.c * p 2 := by
    intro p; simp [L, h_point3] <;> ring
  have hL1 : ∀ (p : Point3), (L p) 1 = p 1 + params.d * p 2 := by
    intro p; simp [L, h_point3] <;> ring
  have hL2 : ∀ (p : Point3), (L p) 2 = p 2 := by
    intro p; simp [L, h_point3] <;> ring

  have h_image : tubeParameterPrism params radius = e '' B := by
    ext q
    simp only [Set.mem_image]
    constructor
    · rintro ⟨hz, hx, hy⟩
      let p : Point3 := point3 (q 0 - params.a - params.c * q 2) (q 1 - params.b - params.d * q 2) (q 2)
      have hpe0 : p 0 = q 0 - (params.a + params.c * q 2) := by
        simp [p, h_point3] <;> ring
      have hpe1 : p 1 = q 1 - (params.b + params.d * q 2) := by
        simp [p, h_point3] <;> ring
      have hpe2 : p 2 = q 2 := by
        simp [p, h_point3] <;> ring
      have hpx : -radius ≤ p 0 ∧ p 0 ≤ radius := by
        rw [hpe0]; exact abs_le.mp hx
      have hpy : -radius ≤ p 1 ∧ p 1 ≤ radius := by
        rw [hpe1]; exact abs_le.mp hy
      have hpz : -1 ≤ p 2 ∧ p 2 ≤ 1 := by
        rw [hpe2]; exact hz
      have hB : p ∈ B := by
        rw [hB_def p]
        exact ⟨⟨hpx.1, hpx.2⟩, ⟨hpy.1, hpy.2⟩, ⟨hpz.1, hpz.2⟩⟩
      have h_eq : e p = q := by
        ext i
        fin_cases i
        · simp [e, hL0, hv0, hpe0, hpe2] <;> ring
        · simp [e, hL1, hv1, hpe1, hpe2] <;> ring
        · simp [e, hL2, hv2, hpe2] <;> ring
      exact ⟨p, hB, h_eq⟩
    · rintro ⟨p, hB, rfl⟩
      have hpb := (hB_def p).mp hB
      rcases hpb with ⟨hp0, hp1, hp2⟩
      have hq2 : (v + L p) 2 = p 2 := by
        simp [hL2, hv2] <;> ring
      have hq0 : (v + L p) 0 - (params.a + params.c * (v + L p) 2) = p 0 := by
        simp [hL0, hv0, hL2, hv2] <;> ring
      have hq1 : (v + L p) 1 - (params.b + params.d * (v + L p) 2) = p 1 := by
        simp [hL1, hv1, hL2, hv2] <;> ring
      exact ⟨by rw [hq2]; exact hp2, by rw [hq0]; exact abs_le.mpr hp0, by rw [hq1]; exact abs_le.mpr hp1⟩

  -- Determinant of L is 1
  let basis : Module.Basis (Fin 3) ℝ Point3 :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have h_basis_j : ∀ (j : Fin 3), basis j = EuclideanSpace.single j 1 := by
    intro j
    simp [basis, EuclideanSpace.basisFun_toBasis] <;> rfl

  have h_mat : LinearMap.toMatrix basis basis L = M := by
    ext i j
    have h_apply : (LinearMap.toMatrix basis basis L) i j = (L (basis j)) i := by
      rw [LinearMap.toMatrix_apply] <;> rfl
    rw [h_apply, h_basis_j j]
    fin_cases i <;> fin_cases j <;>
      simp [L, h_point3, M, Matrix.cons_val'] <;>
      (try norm_num) <;> (try ring)

  have h_det : LinearMap.det L = 1 := by
    have h2 : (LinearMap.toMatrix basis basis L).det = LinearMap.det L :=
      LinearMap.det_toMatrix basis L
    have h3 : M.det = 1 := by
      simp [M, Matrix.det_fin_three] <;> ring
    rw [←h2, h_mat]
    exact h3

  -- Translation preserves volume via MeasurableEquiv (no NullMeasurableSet needed)
  let t : Point3 → Point3 := fun x => v + x
  let t_inv : Point3 → Point3 := fun x => x - v
  let t_me : Point3 ≃ᵐ Point3 :=
    { toFun := t_inv,
      invFun := t,
      left_inv := by intro x; dsimp only [t, t_inv]; abel,
      right_inv := by intro x; dsimp only [t, t_inv]; abel }
  have h_trans_inv : MeasurePreserving t_inv volume volume := by
    have h : MeasurePreserving (fun x : Point3 => -v + x) volume volume :=
      measurePreserving_add_left volume (-v)
    convert h using 1
    funext x
    simp [t_inv] <;> abel

  have h_vol1 : volume (e '' B) = volume (L '' B) := by
    have h_eq_set : e '' B = t '' (L '' B) := by
      ext y
      simp only [e, t, Set.mem_image]
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact ⟨L p, ⟨p, hp, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨p, hp, rfl⟩
    rw [h_eq_set]
    have h_pre : t '' (L '' B) = t_me ⁻¹' (L '' B) := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage, t_me, t, t_inv]
      constructor
      · rintro ⟨x, hx, rfl⟩; simpa using hx
      · intro hy; exact ⟨t_inv y, hy, by dsimp only [t, t_inv]; abel⟩
    rw [h_pre]
    have h_trans_inv' : MeasurePreserving (↑t_me) volume volume := by
      convert h_trans_inv <;> rfl
    exact h_trans_inv'.measure_preimage_equiv (s := (L '' B))

  -- Linear map volume
  have h_vol2 : volume (L '' B) =
      ENNReal.ofReal |LinearMap.det L| * volume B :=
    MeasureTheory.Measure.addHaar_image_linearMap volume L B

  have h_vol : volume (tubeParameterPrism params radius) ≤
      ENNReal.ofReal (8 * radius ^ 2) := by
    rw [h_image, h_vol1, h_vol2, h_det, h_box_vol]
    have h_abs : |(1 : ℝ)| = 1 := by norm_num
    rw [h_abs]
    have h_main : ENNReal.ofReal (1 : ℝ) * ENNReal.ofReal (8 * radius ^ 2) =
        ENNReal.ofReal (8 * radius ^ 2) := by
      simp [ENNReal.ofReal_one]
    rw [h_main] <;> exact le_refl _

  exact ⟨h_conv, h_vol⟩

end Kakeya.Assouad
