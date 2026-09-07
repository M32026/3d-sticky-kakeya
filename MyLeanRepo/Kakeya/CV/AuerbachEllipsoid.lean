import MyLeanRepo.Kakeya.CV.Geometry
import Mathlib.Tactic

/-!
# Auerbach ellipsoid approximation

Replaces the John ellipsoid black box with an elementary Auerbach-basis
construction.
-/

noncomputable section

open scoped Pointwise Real

namespace Kakeya.CV

/-- Standard basis vector in `Point 3`. -/
def stdBasis3 (i : Fin 3) : Point 3 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ) i

/-- Equivalence between `Point 3` and `Fin 3 → ℝ`. -/
def eucEquiv : Point 3 ≃L[ℝ] (Fin 3 → ℝ) :=
  EuclideanSpace.equiv (Fin 3) ℝ

/-- If `S` is convex, symmetric about 0, contains 0, and `Σ|tᵢ| ≤ 1`
with `xᵢ ∈ S`, then `Σ tᵢ•xᵢ ∈ S`. -/
lemma absConvex_sum {S : Set (Point 3)} (hconv : Convex ℝ S)
    (hsym : ∀ x ∈ S, -x ∈ S) (h0 : 0 ∈ S)
    (t : Fin 3 → ℝ) (x : Fin 3 → Point 3)
    (hx : ∀ i, x i ∈ S) (hsum : ∑ i : Fin 3, |t i| ≤ 1) :
    ∑ i : Fin 3, t i • x i ∈ S := by
  let T : ℝ := ∑ i : Fin 3, |t i|
  have hT_nonneg : 0 ≤ T := by positivity
  have hT_le_one : T ≤ 1 := hsum
  by_cases hT0 : T = 0
  · have h_all_zero : ∀ i, t i = 0 := by
      intro i
      have h_nonneg : ∀ j, 0 ≤ |t j| := fun j => abs_nonneg (t j)
      have h6 : |t i| ≤ ∑ j : Fin 3, |t j| := Finset.single_le_sum (fun j _ => h_nonneg j) (Finset.mem_univ i)
      have h_sum : ∑ j : Fin 3, |t j| = 0 := hT0
      rw [h_sum] at h6
      have h7 : |t i| = 0 := by linarith [h_nonneg i]
      simpa using h7
    have h5 : ∑ i : Fin 3, t i • x i = 0 := by
      have h6 : ∀ i ∈ Finset.univ, t i • x i = 0 := by
        intro i _; rw [h_all_zero i, zero_smul]
      rw [Finset.sum_congr rfl h6]; simp
    rw [h5]; exact h0
  · have hT_pos : 0 < T := by
      have h : T ≠ 0 := hT0
      exact lt_of_le_of_ne hT_nonneg h.symm
    let y : Fin 3 → Point 3 := fun i => if 0 ≤ t i then x i else -x i
    have hy : ∀ i, y i ∈ S := by
      intro i
      by_cases h : 0 ≤ t i
      · have hyi : y i = x i := by rw [show y i = x i from if_pos h]
        rw [hyi]; exact hx i
      · have hneg : t i < 0 := by linarith
        have hyi : y i = -x i := by rw [show y i = -x i from if_neg (by linarith)]
        rw [hyi]; exact hsym (x i) (hx i)
    have h1 : ∀ i, t i • x i = |t i| • y i := by
      intro i
      by_cases h : 0 ≤ t i
      · have h2 : |t i| = t i := abs_of_nonneg h
        have hyi : y i = x i := by rw [show y i = x i from if_pos h]
        rw [h2, hyi] <;> rfl
      · have hneg : t i < 0 := by linarith
        have h2 : |t i| = -t i := abs_of_neg hneg
        have hyi : y i = -x i := by rw [show y i = -x i from if_neg (by linarith)]
        rw [h2, hyi] <;> simp [smul_neg] <;> abel
    let w : Fin 3 → ℝ := fun i => |t i| / T
    have hw_nonneg : ∀ i, 0 ≤ w i := by
      intro i; apply div_nonneg <;> positivity
    have hw_sum : ∑ i : Fin 3, w i = 1 := by
      have h : ∑ i : Fin 3, w i = (∑ i : Fin 3, |t i|) / T := by
        rw [Finset.sum_div] <;> rfl
      rw [h, div_self hT_pos.ne']
    let z : Point 3 := ∑ i : Fin 3, w i • y i
    have hz_in_S : z ∈ S := hconv.sum_mem (fun i _ => hw_nonneg i) hw_sum (fun i _ => hy i)
    have h2 : ∑ i : Fin 3, t i • x i = T • z := by
      calc
        ∑ i : Fin 3, t i • x i
          = ∑ i : Fin 3, |t i| • y i := by
            apply Finset.sum_congr rfl; intro i _; exact h1 i
        _ = ∑ i : Fin 3, T • (w i • y i) := by
            apply Finset.sum_congr rfl; intro i _
            have h3 : |t i| = T * w i := by
              simp [w]; field_simp [hT_pos.ne'] <;> ring
            rw [h3]; rw [mul_smul]
        _ = T • z := by rw [←Finset.smul_sum] <;> rfl
    rw [h2]
    have h3 : T • z + (1 - T) • (0 : Point 3) ∈ S :=
      hconv hz_in_S h0 (by linarith) (by linarith) (by linarith)
    simpa using h3

/-- If `S` is convex, symmetric about 0, has nonempty interior, and
contains 0, then 0 is in the interior of `S`. -/
lemma zero_in_interior_of_symmetric {S : Set (Point 3)}
    (hconv : Convex ℝ S) (hsym : ∀ x ∈ S, -x ∈ S)
    (hint : (interior S).Nonempty) (h0 : 0 ∈ S) :
    0 ∈ interior S := by
  rcases hint with ⟨x, hx_int⟩
  have hneg_int : -x ∈ interior S := by
    let negHomeo : Point 3 ≃ₜ Point 3 :=
      { toFun := fun v => -v
        invFun := fun v => -v
        left_inv := by intro v; simp
        right_inv := by intro v; simp
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    have h1 : negHomeo '' S = S := by
      ext y
      simp only [Set.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hneg : negHomeo x = -x := by simp [negHomeo]
        rw [hneg]
        exact hsym x hx
      · intro hy
        refine ⟨-y, hsym y hy, ?_⟩
        have h : negHomeo (-y) = y := by
          simp [negHomeo]
        exact h
    have h2 : negHomeo '' interior S = interior (negHomeo '' S) := Homeomorph.image_interior negHomeo S
    have h3 : negHomeo '' interior S = interior S := by
      rw [h2, h1]
    have h4 : -x ∈ negHomeo '' interior S := by
      refine ⟨x, hx_int, ?_⟩
      simp [negHomeo]
    rw [h3] at h4
    exact h4
  have h_int_convex : Convex ℝ (interior S) := hconv.interior
  have h : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-x) ∈ interior S :=
    h_int_convex hx_int hneg_int (by norm_num) (by norm_num) (by norm_num)
  simpa using h

/-- Auerbach basis for a compact convex symmetric body S with 0 ∈ interior S.
Returns a linear equivalence A whose standard basis images are in S and
whose coordinate functionals are bounded by 1 on S. -/
lemma auerbach_basis {S : Set (Point 3)}
    (hcompact : IsCompact S) (hconv : Convex ℝ S)
    (hsym : ∀ x ∈ S, -x ∈ S) (hint : (interior S).Nonempty) (h0 : 0 ∈ S) :
    ∃ (A : Point 3 ≃ₗ[ℝ] Point 3),
      (∀ i, A (stdBasis3 i) ∈ S) ∧
      (∀ (x : Point 3), x ∈ S → ∀ i, |(A.symm x) i| ≤ 1) := by
  have h0_int : 0 ∈ interior S := zero_in_interior_of_symmetric hconv hsym hint h0
  let P : Set (Fin 3 → Point 3) := Set.pi Set.univ (fun _ => S)
  have hP_compact : IsCompact P := by
    exact isCompact_univ_pi (fun (_ : Fin 3) => hcompact)
  have hP_nonempty : P.Nonempty := by
    have h_witness : (fun _ : Fin 3 => (0 : Point 3)) ∈ P := by
      simp only [P, Set.mem_univ_pi, Set.mem_univ, forall_true_left]
      intro i; exact h0
    exact ⟨_, h_witness⟩
  let f : (Fin 3 → Point 3) → ℝ := tripleVolume
  have hf_cont : Continuous f := by
    have h_matrix_cont : Continuous (fun v : (Fin 3 → Point 3) => (fun i j : Fin 3 => v i j)) := by fun_prop
    have h_det_cont : Continuous (fun M : Matrix (Fin 3) (Fin 3) ℝ => M.det) := by
      simpa [Matrix.det_fin_three] using by fun_prop
    exact h_det_cont.comp h_matrix_cont |>.abs
  rcases hP_compact.exists_isMaxOn hP_nonempty hf_cont.continuousOn with ⟨e, heP, he_max⟩
  have heS : ∀ i, e i ∈ S := by
    have h : e ∈ P := heP
    simpa [P, Set.mem_univ_pi] using h
  -- Positive determinant triple
  rcases Metric.isOpen_iff.mp isOpen_interior 0 h0_int with ⟨ε, hε_pos, hε_sub⟩
  let ε' := ε / 2
  have hε'_pos : 0 < ε' := by positivity
  have hε'_lt : ε' < ε := by
    exact half_lt_self hε_pos
  let v : Fin 3 → Point 3 := fun i => ε' • stdBasis3 i
  have h_std_coord : ∀ (i j : Fin 3), (stdBasis3 i) j = if i = j then (1 : ℝ) else 0 := by
    intro i j
    have h1 : stdBasis3 i = (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis i := by rfl
    rw [h1]
    let std : Module.Basis (Fin 3) ℝ (Point 3) := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    have h2 : std.repr (std i) = Finsupp.single i (1 : ℝ) := std.repr_self i
    have h3 : (std.repr (std i)) j = (std i) j := (EuclideanSpace.basisFun_repr (Fin 3) ℝ (std i) j).symm
    rw [←h3, h2]
    simp [Finsupp.single_apply]
    <;> split_ifs <;> simp
  have hv_in_S : ∀ i, v i ∈ S := by
    intro i
    have h_norm : ‖(v i : Point 3)‖ = ε' := by
      have h1 : ‖(stdBasis3 i : Point 3)‖ = 1 := by
        rw [EuclideanSpace.norm_eq]
        have h := h_std_coord i
        have h' : ∀ j : Fin 3, ‖(stdBasis3 i) j‖ ^ 2 = if i = j then (1 : ℝ) else 0 := by
          intro j
          rw [h j] <;> simp [abs_of_nonneg] <;> norm_num
        have hsum1 : ∑ j : Fin 3, ‖(stdBasis3 i) j‖ ^ 2 = ∑ j : Fin 3, (if i = j then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl; intro j _; exact h' j
        have hsum2 : ∑ j : Fin 3, (if i = j then (1 : ℝ) else 0) = 1 := by
          fin_cases i <;> simp [Fin.sum_univ_succ] <;> norm_num
        rw [hsum1, hsum2] <;> norm_num
      simp [v, norm_smul, h1, abs_of_pos hε'_pos] <;> ring
    have h_in_ball : v i ∈ Metric.ball (0 : Point 3) ε := by
      simp [Metric.mem_ball, h_norm, hε'_lt]
    exact interior_subset (hε_sub h_in_ball)
  have hvP : v ∈ P := by
    simpa [P, Set.mem_univ_pi] using hv_in_S
  have h_det_pos : 0 < tripleVolume v := by
    have hM : (fun i j : Fin 3 => v i j) = ε' • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
      ext i j
      have h1 : (v i) j = ε' * (stdBasis3 i) j := by
        simp [v] <;> rfl
      rw [h1, h_std_coord i j]
      simp [Matrix.one_apply] <;> split_ifs <;> ring
    rw [tripleVolume, hM]
    simp [Matrix.det_smul, Finset.card_fin] <;> positivity
  have h_vol_pos : 0 < tripleVolume e := by
    have h : tripleVolume v ≤ tripleVolume e := he_max hvP
    linarith
  let M : Matrix (Fin 3) (Fin 3) ℝ := fun i j => e i j
  have hdet : M.det ≠ 0 := by
    have h1 : |M.det| = tripleVolume e := by rfl
    have h2 : 0 < |M.det| := by
      rw [h1]; exact h_vol_pos
    have h3 : |M.det| ≠ 0 := h2.ne'
    exact (abs_ne_zero).mp h3
  have hli_pi : LinearIndependent ℝ (fun i : Fin 3 => M i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have h_eq_family : (fun i : Fin 3 => eucEquiv.symm (M i)) = e := by
    funext i
    apply eucEquiv.symm_apply_apply
  have hli : LinearIndependent ℝ e := by
    rw [←h_eq_family]
    have h_ker : (eucEquiv.symm.toLinearMap).ker = ⊥ := eucEquiv.symm.ker
    exact (hli_pi.map' eucEquiv.symm.toLinearMap) h_ker
  have hsp_eq : Submodule.span ℝ (Set.range e) = ⊤ := by
    have hdim : Module.finrank ℝ (Point 3) = 3 := by simp
    have hcard : Fintype.card (Fin 3) = 3 := by simp
    apply LinearIndependent.span_eq_top_of_card_eq_finrank hli
    <;> simp
  have hsp : (⊤ : Submodule ℝ (Point 3)) ≤ Submodule.span ℝ (Set.range e) :=
    le_of_eq hsp_eq.symm
  let bA : Module.Basis (Fin 3) ℝ (Point 3) := Module.Basis.mk (hli := hli) (hsp := hsp)
  have hbA_apply : ∀ i, bA i = e i := by
    intro i
    exact Module.Basis.mk_apply (hli := hli) (hsp := hsp) i
  let std : Module.Basis (Fin 3) ℝ (Point 3) :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let A : Point 3 ≃ₗ[ℝ] Point 3 :=
    eucEquiv.toLinearEquiv.trans bA.equivFun.symm
  have hA_apply : ∀ (y : Point 3), A y = ∑ i : Fin 3, y i • e i := by
    intro y
    have h1 : A y = bA.equivFun.symm (eucEquiv y) := by rfl
    rw [h1]
    have h2 : bA.equivFun.symm (eucEquiv y) = ∑ i : Fin 3, (eucEquiv y) i • bA i := by
      exact bA.equivFun_symm_apply (eucEquiv y)
    rw [h2]
    have h3 : ∑ i : Fin 3, (eucEquiv y) i • bA i = ∑ i : Fin 3, y i • e i := by
      apply Finset.sum_congr rfl
      intro i _
      have h4 : (eucEquiv y) i = y i := by rfl
      rw [h4, hbA_apply i]
    exact h3
  have hA_std : ∀ i, A (stdBasis3 i) = e i := by
    intro i
    rw [hA_apply (stdBasis3 i)]
    fin_cases i <;> simp [h_std_coord, Fin.sum_univ_succ] <;> abel
  have h_main : ∀ (x : Point 3), x ∈ S → ∀ i, |(A.symm x) i| ≤ 1 := by
    intro x hx i
    let c : Fin 3 → ℝ := bA.equivFun x
    have hc_coord : ∀ k, c k = (A.symm x) k := by
      intro k
      have h1 : A.symm x = eucEquiv.symm (bA.equivFun x) := by
        ext j
        <;> rfl
      rw [h1]
      <;> rfl
    have h_expansion : x = ∑ k : Fin 3, c k • e k := by
      have h1 : x = ∑ k : Fin 3, c k • bA k := by
        exact (bA.sum_repr x).symm
      rw [h1]
      apply Finset.sum_congr rfl
      intro k _
      rw [hbA_apply k]
    have h_expansion_pi : eucEquiv x = ∑ k : Fin 3, c k • (fun j : Fin 3 => M k j) := by
      rw [h_expansion]
      have h5 : eucEquiv (∑ k : Fin 3, c k • e k) = ∑ k : Fin 3, c k • eucEquiv (e k) := by
        have h51 : eucEquiv (∑ k : Fin 3, c k • e k) = ∑ k : Fin 3, eucEquiv (c k • e k) := by
          simp [Fin.sum_univ_succ, eucEquiv.map_add]
          <;> rfl
        rw [h51]
        apply Finset.sum_congr rfl
        intro k _
        exact eucEquiv.map_smul (c k) (e k)
      rw [h5]
      apply Finset.sum_congr rfl
      intro k _
      ext j
      <;> rfl
    have h_det_eq : (M.updateRow i (eucEquiv x)).det = c i * M.det := by
      rw [h_expansion_pi]
      exact Matrix.det_updateRow_sum M i c
    let e' : Fin 3 → Point 3 := Function.update e i x
    have he'P : e' ∈ P := by
      have h : ∀ j, e' j ∈ S := by
        intro j
        by_cases hji : j = i
        · rw [hji]; simpa [e'] using hx
        · simp [e', hji]; exact heS j
      simpa [P, Set.mem_univ_pi] using h
    have h4 : tripleVolume e' = |c i * M.det| := by
      have h5 : (fun j k => e' j k) = M.updateRow i (eucEquiv x) := by
        apply Matrix.ext
        intro j k
        by_cases hji : j = i
        · have h_eq : j = i := hji
          rw [h_eq]
          have h6 : e' i = x := Function.update_self i x e
          simp [Matrix.updateRow_apply, h6]
          <;> rfl
        · simp [e', hji, Matrix.updateRow_apply] <;> rfl
      rw [tripleVolume, h5, h_det_eq] <;> rfl
    have h6 : tripleVolume e' ≤ tripleVolume e := he_max he'P
    have h7 : |c i * M.det| ≤ |M.det| := by rw [h4] at h6; exact h6
    have h8 : 0 < |M.det| := abs_pos.mpr hdet
    have h9 : |c i| ≤ 1 := by
      have h10 : |c i * M.det| = |c i| * |M.det| := by rw [abs_mul]
      rw [h10] at h7
      nlinarith
    have h11 : (A.symm x) i = c i := (hc_coord i).symm
    rw [h11]
    exact h9
  exact ⟨A, fun i => by rw [hA_std i]; exact heS i, h_main⟩

/-- Every centrally symmetric convex body has a √3-close ellipsoid centered
at the symmetry center, constructed via an Auerbach basis. -/
lemma symmetric_body_ellipsoid_approx
    {K : Set (Point 3)} {z : Point 3}
    (hK : JohnEllipsoid.IsConvexBody K)
    (h_sym : ∀ x, x ∈ K → z + (z - x) ∈ K) :
    ∃ (A : Point 3 ≃ₗ[ℝ] Point 3),
        dilateAbout z (Real.sqrt 3)⁻¹ K ⊆ JohnEllipsoid.ellipsoid z A ∧
        JohnEllipsoid.ellipsoid z A ⊆ dilateAbout z (Real.sqrt 3) K := by
  let S : Set (Point 3) := {v | z + v ∈ K}
  have hK_conv : Convex ℝ K := hK.1
  have hK_compact : IsCompact K := hK.2.1
  have hK_int : (interior K).Nonempty := hK.2.2
  have hS_eq : S = (fun x : Point 3 => x - z) '' K := by
    ext v; simp [S] <;> constructor
    · intro h; exact ⟨z + v, h, by simp⟩
    · rintro ⟨x, hx, rfl⟩; simpa using hx
  have hS_compact : IsCompact S := by
    rw [hS_eq]; exact hK_compact.image (by fun_prop)
  have hS_convex : Convex ℝ S := by
    intro v1 hv1 v2 hv2 a b ha hb hab
    have h1 : z + v1 ∈ K := hv1
    have h2 : z + v2 ∈ K := hv2
    have h3 : a • (z + v1) + b • (z + v2) ∈ K := hK_conv h1 h2 ha hb hab
    have h4 : a • (z + v1) + b • (z + v2) = z + (a • v1 + b • v2) := by
      have h5 : a • (z + v1) = a • z + a • v1 := by rw [smul_add]
      have h6 : b • (z + v2) = b • z + b • v2 := by rw [smul_add]
      rw [h5, h6]
      have h7 : a • z + b • z = (a + b) • z := by rw [←add_smul]
      have h8 : a • z + a • v1 + (b • z + b • v2) = (a • z + b • z) + (a • v1 + b • v2) := by abel
      rw [h8, h7, hab]
      <;> simp [add_assoc] <;> abel
    rw [h4] at h3; exact h3
  have hS_sym : ∀ v ∈ S, -v ∈ S := by
    intro v hv
    have h1 : z + v ∈ K := hv
    have h2 : z + (z - (z + v)) ∈ K := h_sym (z + v) h1
    have h3 : z + (z - (z + v)) = z - v := by simp [vadd_vadd] <;> abel
    rw [h3] at h2
    simpa [S, sub_eq_add_neg] using h2
  have hz_in_K : z ∈ K := by
    rcases hK_int with ⟨x, hx_int⟩
    have hx_in_K : x ∈ K := interior_subset hx_int
    have h2 : z + (z - x) ∈ K := h_sym x hx_in_K
    have ha : (0 : ℝ) ≤ 1 / 2 := by norm_num
    have hb : (0 : ℝ) ≤ 1 / 2 := by norm_num
    have hab : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
    have h3 : z = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (z + (z - x)) := by
      have h4 : (1 / 2 : ℝ) • (z + (z - x)) = (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • (z - x) := by rw [smul_add]
      have h5 : (1 / 2 : ℝ) • (z - x) = (1 / 2 : ℝ) • z - (1 / 2 : ℝ) • x := by rw [smul_sub]
      rw [h4, h5]
      have h6 : (1 / 2 : ℝ) • x + ((1 / 2 : ℝ) • z + ((1 / 2 : ℝ) • z - (1 / 2 : ℝ) • x)) = z := by
        have h7 : (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • z = z := by
          rw [←add_smul] <;> norm_num
        have h8 : (1 / 2 : ℝ) • x + ((1 / 2 : ℝ) • z + ((1 / 2 : ℝ) • z - (1 / 2 : ℝ) • x)) =
                  (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • z := by
          simp [sub_eq_add_neg, add_assoc]
          <;> abel
        rw [h8, h7]
      exact h6.symm
    rw [h3]
    exact hK_conv hx_in_K h2 ha hb hab
  have hS_0 : 0 ∈ S := by simpa [S] using hz_in_K
  have hS_int : (interior S).Nonempty := by
    rcases hK_int with ⟨x, hx_int⟩
    let transl : Point 3 ≃ₜ Point 3 :=
      { toFun := fun v => v - z
        invFun := fun v => v + z
        left_inv := by intro v; simp <;> abel
        right_inv := by intro v; simp <;> abel
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    have h_S_eq : S = transl '' K := by
      ext v
      simp only [S, Set.mem_image, Set.mem_setOf_eq]
      constructor
      · intro h; exact ⟨z + v, h, by simp [transl]⟩
      · rintro ⟨x, hx, rfl⟩; simpa [transl] using hx
    have h_int_img : transl '' interior K = interior S := by
      have h : transl '' interior K = interior (transl '' K) := by
        exact Homeomorph.image_interior transl K
      rw [h, h_S_eq]
    refine ⟨transl x, ?_⟩
    rw [←h_int_img]
    exact ⟨x, hx_int, rfl⟩
  rcases auerbach_basis hS_compact hS_convex hS_sym hS_int hS_0 with ⟨A, hA_in_S, hcoord⟩
  have h_sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h_norm2_eq : ∀ (x : Point 3), ‖x‖ ^ 2 = ∑ i : Fin 3, (x i) ^ 2 := by
    intro x
    have h1 : ‖x‖ = Real.sqrt (∑ i : Fin 3, |x i| ^ 2) := by
      simpa [EuclideanSpace.norm_eq] using EuclideanSpace.norm_eq x
    rw [h1]
    have h2 : ∑ i : Fin 3, |x i| ^ 2 = ∑ i : Fin 3, (x i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      have h3 : |x i| ^ 2 = (x i) ^ 2 := by rw [sq_abs]
      exact h3
    rw [h2]
    rw [Real.sq_sqrt] <;> positivity
  have h_cs : ∀ (a : Fin 3 → ℝ), (∑ i : Fin 3, |a i|) ^ 2 ≤ 3 * ∑ i : Fin 3, (a i) ^ 2 := by
    intro a
    set x := |a 0| with hx
    set y := |a 1| with hy
    set z := |a 2| with hz
    have hx' : 0 ≤ x := by positivity
    have hy' : 0 ≤ y := by positivity
    have hz' : 0 ≤ z := by positivity
    have h_expand1 : ∑ i : Fin 3, |a i| = x + y + z := by
      simp [Fin.sum_univ_succ, hx, hy, hz] <;> abel
    have h_expand2 : ∑ i : Fin 3, (a i) ^ 2 = (a 0) ^ 2 + (a 1) ^ 2 + (a 2) ^ 2 := by
      simp [Fin.sum_univ_succ] <;> ring
    rw [h_expand1, h_expand2]
    have h_ineq : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    have h_x2 : x ^ 2 = (a 0) ^ 2 := by rw [show x = |a 0| from by simp [hx], sq_abs]
    have h_y2 : y ^ 2 = (a 1) ^ 2 := by rw [show y = |a 1| from by simp [hy], sq_abs]
    have h_z2 : z ^ 2 = (a 2) ^ 2 := by rw [show z = |a 2| from by simp [hz], sq_abs]
    rw [h_x2, h_y2, h_z2] at h_ineq
    exact h_ineq
  have h_sum_abs_le : ∀ (y : Point 3), ∑ i : Fin 3, |y i| ≤ Real.sqrt 3 * ‖y‖ := by
    intro y
    have h1 : (∑ i : Fin 3, |y i|) ^ 2 ≤ 3 * ∑ i : Fin 3, (y i) ^ 2 := h_cs y
    have h2 : ∑ i : Fin 3, (y i) ^ 2 = ‖y‖ ^ 2 := (h_norm2_eq y).symm
    rw [h2] at h1
    have h3 : (∑ i : Fin 3, |y i|) ^ 2 ≤ (Real.sqrt 3 * ‖y‖) ^ 2 := by
      have h4 : (Real.sqrt 3 * ‖y‖) ^ 2 = 3 * ‖y‖ ^ 2 := by
        have h5 : (Real.sqrt 3) ^ 2 = 3 := by rw [Real.sq_sqrt] <;> norm_num
        nlinarith
      rw [h4]; exact h1
    have h6 : 0 ≤ ∑ i : Fin 3, |y i| := by positivity
    have h7 : 0 ≤ Real.sqrt 3 * ‖y‖ := by positivity
    exact (sq_le_sq₀ h6 h7).mp h3
  let std : Module.Basis (Fin 3) ℝ (Point 3) := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have h_std_eq : stdBasis3 = std := by funext i; rfl
  -- Inclusion 1
  have h1 : dilateAbout z (Real.sqrt 3)⁻¹ K ⊆ JohnEllipsoid.ellipsoid z A := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    let v : Point 3 := y - z
    have hzv : z + v = y := by simp [v] <;> abel
    have hvS : v ∈ S := by
      have h' : z + v ∈ K := by rw [hzv]; exact hy
      simpa [S] using h'
    have h_goal1 : ∀ i, |(A.symm v) i| ≤ 1 := hcoord v hvS
    have h_norm2 : ∑ i : Fin 3, ((A.symm v) i) ^ 2 ≤ 3 := by
      have h : ∀ i, ((A.symm v) i) ^ 2 ≤ 1 := by
        intro i
        have h2 : |(A.symm v) i| ≤ 1 := h_goal1 i
        have h4 : -1 ≤ (A.symm v) i ∧ (A.symm v) i ≤ 1 := abs_le.mp h2
        have h3 : ((A.symm v) i) ^ 2 ≤ 1 := by nlinarith
        exact h3
      have h3 : ∑ i : Fin 3, ((A.symm v) i) ^ 2 ≤ ∑ i : Fin 3, (1 : ℝ) := by
        apply Finset.sum_le_sum; intro i _; exact h i
      simpa using h3
    have h4 : ‖A.symm v‖ ≤ Real.sqrt 3 := by
      have h5 : ‖A.symm v‖ ^ 2 ≤ 3 := by
        have h51 : ‖A.symm v‖ ^ 2 = ∑ i : Fin 3, ((A.symm v) i) ^ 2 := h_norm2_eq (A.symm v)
        rw [h51]; exact h_norm2
      have h6 : ‖A.symm v‖ ^ 2 ≤ (Real.sqrt 3) ^ 2 := by
        have h7 : (Real.sqrt 3) ^ 2 = 3 := by rw [Real.sq_sqrt] <;> norm_num
        rw [h7]; exact h5
      have h8 : 0 ≤ ‖A.symm v‖ := by positivity
      nlinarith
    let w : Point 3 := A.symm ((Real.sqrt 3)⁻¹ • v)
    have h_pos : 0 < (Real.sqrt 3)⁻¹ := by positivity
    have h7 : ‖w‖ ≤ 1 := by
      have h8 : w = (Real.sqrt 3)⁻¹ • A.symm v := A.symm.map_smul _ _
      rw [h8]
      have h9 : ‖(Real.sqrt 3)⁻¹ • A.symm v‖ = (Real.sqrt 3)⁻¹ * ‖A.symm v‖ := by
        calc
          ‖(Real.sqrt 3)⁻¹ • A.symm v‖
            = ‖(Real.sqrt 3)⁻¹‖ * ‖A.symm v‖ := norm_smul _ _
          _ = |(Real.sqrt 3)⁻¹| * ‖A.symm v‖ := by rw [Real.norm_eq_abs]
          _ = (Real.sqrt 3)⁻¹ * ‖A.symm v‖ := by rw [abs_of_pos h_pos]
      rw [h9]
      have h10 : (Real.sqrt 3)⁻¹ * ‖A.symm v‖ ≤ 1 := by
        have h11 : ‖A.symm v‖ ≤ Real.sqrt 3 := h4
        have h12 : (Real.sqrt 3)⁻¹ * ‖A.symm v‖ ≤ (Real.sqrt 3)⁻¹ * Real.sqrt 3 := by gcongr
        have h13 : (Real.sqrt 3)⁻¹ * Real.sqrt 3 = 1 := by
          field_simp [h_sqrt3_pos.ne'] <;> ring
        rw [h13] at h12; exact h12
      exact h10
    have hAw : A w = (Real.sqrt 3)⁻¹ • v := A.apply_symm_apply _
    have h_goal : (Real.sqrt 3)⁻¹ • v ∈ A '' Metric.closedBall (0 : Point 3) 1 :=
      ⟨w, by simpa [Metric.mem_closedBall] using h7, hAw⟩
    have h_hom : AffineMap.homothety z (Real.sqrt 3)⁻¹ y = z +ᵥ (Real.sqrt 3)⁻¹ • v := by
      simp [AffineMap.homothety_apply, vadd_eq_add, v]
      <;> abel
    rw [h_hom]
    have h_final : z +ᵥ (Real.sqrt 3)⁻¹ • v ∈ z +ᵥ (A '' Metric.closedBall (0 : Point 3) 1) := by
      exact ⟨(Real.sqrt 3)⁻¹ • v, h_goal, rfl⟩
    simpa [JohnEllipsoid.ellipsoid] using h_final
  -- Inclusion 2
  have h2 : JohnEllipsoid.ellipsoid z A ⊆ dilateAbout z (Real.sqrt 3) K := by
    intro x hx
    rcases hx with ⟨w, hw, rfl⟩
    rcases hw with ⟨y, hy_ball, rfl⟩
    have h_ball : ‖y‖ ≤ 1 := by
      have h : y ∈ Metric.closedBall (0 : Point 3) 1 := hy_ball
      have h' : ‖y - (0 : Point 3)‖ ≤ 1 := by simpa [Metric.mem_closedBall] using h
      simpa using h'
    let t : Fin 3 → ℝ := fun i => (Real.sqrt 3)⁻¹ * y i
    have h_sum_abs : ∑ i : Fin 3, |t i| ≤ 1 := by
      have h1 : ∑ i : Fin 3, |t i| = (Real.sqrt 3)⁻¹ * ∑ i : Fin 3, |y i| := by
        have h2 : ∀ i, |t i| = (Real.sqrt 3)⁻¹ * |y i| := by
          intro i
          have h3 : t i = (Real.sqrt 3)⁻¹ * y i := by simp [t]
          rw [h3]
          have h_pos : 0 < (Real.sqrt 3)⁻¹ := by positivity
          have h4 : |(Real.sqrt 3)⁻¹ * y i| = (Real.sqrt 3)⁻¹ * |y i| := by
            calc
              |(Real.sqrt 3)⁻¹ * y i|
                = |(Real.sqrt 3)⁻¹| * |y i| := abs_mul _ _
              _ = (Real.sqrt 3)⁻¹ * |y i| := by
                have h5 : |(Real.sqrt 3)⁻¹| = (Real.sqrt 3)⁻¹ := abs_of_pos h_pos
                rw [h5]
          exact h4
        have h3 : ∑ i : Fin 3, |t i| = ∑ i : Fin 3, ((Real.sqrt 3)⁻¹ * |y i|) := by
          apply Finset.sum_congr rfl
          intro i _; exact h2 i
        rw [h3, Finset.mul_sum]
      rw [h1]
      have h3 : ∑ i : Fin 3, |y i| ≤ Real.sqrt 3 * ‖y‖ := h_sum_abs_le y
      have h4 : (Real.sqrt 3)⁻¹ * ∑ i : Fin 3, |y i| ≤ (Real.sqrt 3)⁻¹ * (Real.sqrt 3 * ‖y‖) := by gcongr
      have h5 : (Real.sqrt 3)⁻¹ * (Real.sqrt 3 * ‖y‖) = ‖y‖ := by
        field_simp [h_sqrt3_pos.ne'] <;> ring
      rw [h5] at h4
      linarith
    let e_std : Fin 3 → Point 3 := fun i => A (stdBasis3 i)
    let v : Point 3 := ∑ i : Fin 3, t i • e_std i
    have hvS : v ∈ S := absConvex_sum hS_convex hS_sym hS_0 t e_std hA_in_S h_sum_abs
    have hz_v_in_K : z + v ∈ K := by simpa [S] using hvS
    have h_expand_y : y = ∑ i : Fin 3, y i • stdBasis3 i := by
      let b := EuclideanSpace.basisFun (Fin 3) ℝ
      have h_repr : ∀ i, (b.toBasis.repr y) i = y i := by
        intro i
        exact EuclideanSpace.basisFun_repr (Fin 3) ℝ y i
      have h_sum : ∑ i : Fin 3, (b.toBasis.repr y) i • b.toBasis i = y := b.toBasis.sum_repr y
      have h_eq1 : ∑ i : Fin 3, (b.toBasis.repr y) i • b.toBasis i = ∑ i : Fin 3, y i • b.toBasis i := by
        apply Finset.sum_congr rfl
        intro i _; rw [h_repr i]
      have h_eq2 : ∑ i : Fin 3, y i • b.toBasis i = ∑ i : Fin 3, y i • stdBasis3 i := by
        apply Finset.sum_congr rfl
        intro i _; rfl
      have h_final : ∑ i : Fin 3, y i • stdBasis3 i = y := by
        rw [←h_eq2, ←h_eq1, h_sum]
      exact h_final.symm
    have h9 : A y = Real.sqrt 3 • v := by
      have h10 : A y = ∑ i : Fin 3, y i • e_std i := by
        have h101 : A y = A (∑ i : Fin 3, y i • stdBasis3 i) := congr_arg A h_expand_y
        rw [h101]
        have h102 : A (∑ i : Fin 3, y i • stdBasis3 i) = ∑ i : Fin 3, A (y i • stdBasis3 i) := by
          simp [Fin.sum_univ_succ, A.map_add]
          <;> rfl
        rw [h102]
        apply Finset.sum_congr rfl
        intro i _
        have h103 : A (y i • stdBasis3 i) = y i • A (stdBasis3 i) := A.map_smul (y i) (stdBasis3 i)
        rw [h103] <;> rfl
      rw [h10]
      have h11 : ∑ i : Fin 3, y i • e_std i = Real.sqrt 3 • v := by
        have h12 : ∀ i, y i • e_std i = Real.sqrt 3 • (t i • e_std i) := by
          intro i
          have h13 : y i = Real.sqrt 3 * t i := by
            simp [t] <;> field_simp [h_sqrt3_pos.ne'] <;> ring
          rw [h13, mul_smul] <;> rfl
        rw [Finset.sum_congr rfl (fun i _ => h12 i)]
        rw [←Finset.smul_sum] <;> rfl
      exact h11
    have h10 : z +ᵥ A y = AffineMap.homothety z (Real.sqrt 3) (z + v) := by
      rw [h9]
      have h11 : z +ᵥ (Real.sqrt 3 • v) = z + (Real.sqrt 3 • v) := by rfl
      rw [h11]
      have h12 : AffineMap.homothety z (Real.sqrt 3) (z + v) = z + Real.sqrt 3 • v := by
        rw [AffineMap.homothety_apply]
        have h14 : (z + v) -ᵥ z = v := by
          simp
          <;> abel
        rw [h14]
        <;> simp
        <;> abel
      rw [h12] <;> abel
    exact ⟨z + v, hz_v_in_K, h10.symm⟩
  exact ⟨A, h1, h2⟩

end Kakeya.CV
