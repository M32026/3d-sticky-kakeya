import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperInfrastructure
import MyLeanRepo.Kakeya.Assouad.WZ1.UnitRescaling
import MyLeanRepo.Kakeya.Assouad.TubeAlignmentGeometry
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section

namespace Kakeya.Assouad

open Finset

attribute [local instance] Classical.propDecidable

private lemma greedy_step
    {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ENNReal)
    (adj : α → α → Prop) [∀ x y, Decidable (adj x y)]
    (hrefl : ∀ x, adj x x)
    (hsymm : ∀ x y, adj x y → adj y x)
    (C : ℕ)
    (hC : ∀ x, (Finset.univ.filter (adj x)).card ≤ C)
    (V : Finset α)
    (ih : ∀ (X : Finset α), X ⊂ V →
      ∃ (S : Finset α), S ⊆ X ∧
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ adj x y) ∧
        (C : ENNReal) * ∑ i ∈ S, w i ≥ ∑ i ∈ X, w i) :
    ∃ (S : Finset α), S ⊆ V ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ adj x y) ∧
      (C : ENNReal) * ∑ i ∈ S, w i ≥ ∑ i ∈ V, w i := by
  by_cases hVempty : V = ∅
  · rw [hVempty]; exact ⟨∅, by simp, by simp, by simp⟩
  · have hVne : V.Nonempty := Finset.nonempty_iff_ne_empty.mpr hVempty
    rcases Finset.exists_max_image V w hVne with ⟨v, hvV, hvmax⟩
    let N : Finset α := V.filter (adj v)
    have hvN : v ∈ N := by
      simp only [N, Finset.mem_filter, hvV, hrefl v, true_and]
    have hN_sub : N ⊆ Finset.univ.filter (adj v) := by
      intro x hx
      have h3 : adj v x := (Finset.mem_filter.mp hx).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h3
    have hNcard : N.card ≤ C := by
      calc
        N.card ≤ (Finset.univ.filter (adj v)).card :=
          Finset.card_le_card hN_sub
        _ ≤ C := hC v
    let V' : Finset α := V \ N
    have hV'sub : V' ⊆ V := by
      intro x hx
      exact (Finset.mem_sdiff.mp hx).1
    have hv_notin_V' : v ∉ V' := by
      intro h
      exact (Finset.mem_sdiff.mp h).2 hvN
    have hV'lt : V' ⊂ V := by
      constructor
      · exact hV'sub
      · intro h
        exact hv_notin_V' (h hvV)
    rcases ih V' hV'lt with ⟨S', hS'sub, hS'indep, hS'mass⟩
    have h_S'_notin_N : ∀ x ∈ S', x ∉ N := by
      intro x hx
      have h_xinV' : x ∈ V' := hS'sub hx
      exact (Finset.mem_sdiff.mp h_xinV').2
    let S : Finset α := insert v S'
    have hv_notin_S' : v ∉ S' := by
      intro h
      exact hv_notin_V' (hS'sub h)
    have hSsub : S ⊆ V := by
      intro x hx
      have h5 : x = v ∨ x ∈ S' := by
        simp only [S, Finset.mem_insert] at hx
        tauto
      rcases h5 with (hxv | h5)
      · rw [hxv]
        exact hvV
      · exact hV'sub (hS'sub h5)
    have hSindep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ adj x y := by
      intro x hx y hy hne
      have hx5 : x = v ∨ x ∈ S' := by
        simp only [S, Finset.mem_insert] at hx
        tauto
      have hy5 : y = v ∨ y ∈ S' := by
        simp only [S, Finset.mem_insert] at hy
        tauto
      rcases hx5 with (hxv | hx5)
      · rcases hy5 with (hyv | hy5)
        · exfalso
          exact hne (by rw [hxv, hyv])
        · have h_yinV : y ∈ V := hV'sub (hS'sub hy5)
          have h_ynotN : y ∉ N := h_S'_notin_N y hy5
          have h : ¬ adj v y := by
            by_contra h6
            have h7 : y ∈ N := by
              simp only [N, Finset.mem_filter, h_yinV, h6, true_and]
            exact h_ynotN h7
          rw [hxv] at *
          exact h
      · rcases hy5 with (hyv | hy5)
        · have h_xinV : x ∈ V := hV'sub (hS'sub hx5)
          have h_xnotN : x ∉ N := h_S'_notin_N x hx5
          have h : ¬ adj v x := by
            by_contra h6
            have h7 : x ∈ N := by
              simp only [N, Finset.mem_filter, h_xinV, h6, true_and]
            exact h_xnotN h7
          have h_goal : ¬ adj x y := by
            rw [hyv]
            exact fun h4 => h (hsymm x v h4)
          exact h_goal
        · exact hS'indep x hx5 y hy5 hne
    have hNmass : ∑ i ∈ N, w i ≤ (C : ENNReal) * w v := by
      have h1 : ∑ i ∈ N, w i ≤ ∑ i ∈ N, w v := by
        apply Finset.sum_le_sum
        intro i hi
        exact hvmax i (Finset.mem_filter.mp hi).1
      have h2 : ∑ i ∈ N, w v = (N.card : ENNReal) * w v := by
        rw [Finset.sum_const]
        ring
      rw [h2] at h1
      have h4 : (N.card : ENNReal) ≤ (C : ENNReal) := by
        exact_mod_cast hNcard
      have h3 : (N.card : ENNReal) * w v ≤ (C : ENNReal) * w v :=
        mul_le_mul_right' h4 (w v)
      exact h1.trans h3
    have h_disj : Disjoint N V' := by
      simp [V', N, Finset.disjoint_left] <;> tauto
    have h_union : N ∪ V' = V := by
      ext x
      simp [V', N] <;> tauto
    have hmass : (C : ENNReal) * ∑ i ∈ S, w i ≥ ∑ i ∈ V, w i := by
      have hSsum : ∑ i ∈ S, w i = w v + ∑ i ∈ S', w i := by
        rw [Finset.sum_insert hv_notin_S']
      rw [hSsum]
      have h : ∑ i ∈ V, w i = ∑ i ∈ N, w i + ∑ i ∈ V', w i := by
        rw [← h_union, Finset.sum_union h_disj]
      rw [h]
      calc
        ∑ i ∈ N, w i + ∑ i ∈ V', w i
            ≤ (C : ENNReal) * w v + ∑ i ∈ V', w i := by
              gcongr
        _ ≤ (C : ENNReal) * w v +
              (C : ENNReal) * ∑ i ∈ S', w i := by
              gcongr
        _ = (C : ENNReal) * (w v + ∑ i ∈ S', w i) := by
              ring
    exact ⟨S, hSsub, hSindep, hmass⟩

theorem exists_independent_set_mass_retention
    {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ENNReal)
    (adj : α → α → Prop) [∀ x y, Decidable (adj x y)]
    (hrefl : ∀ x, adj x x)
    (hsymm : ∀ x y, adj x y → adj y x)
    (C : ℕ)
    (hC : ∀ x, (Finset.univ.filter (adj x)).card ≤ C) :
    ∃ (S : Finset α),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ adj x y) ∧
      (C : ENNReal) * ∑ i ∈ S, w i ≥ ∑ i : α, w i := by
  have h_induction : ∀ (V : Finset α), ∃ (S : Finset α), S ⊆ V ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ adj x y) ∧
      (C : ENNReal) * ∑ i ∈ S, w i ≥ ∑ i ∈ V, w i := by
    intro V
    induction V using Finset.strongInduction with
    | H V ih => exact greedy_step w adj hrefl hsymm C hC V ih
  rcases h_induction Finset.univ with ⟨S, _, hindep, hmass⟩
  exact ⟨S, hindep, hmass⟩

def packingConstant1000 : ℕ := 16001 ^ 5

/--
A conservative absolute packing constant used by the WZ2 literal recursive
selection.  It also remains a valid upper bound for the historical
`10000 * delta` packing lemma.
-/
def packingConstant10000 : ℕ := 192000001 ^ 5

private lemma coord_le_norm (x : Point3) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have h1 : (x i)^2 ≤ ‖x‖^2 := by
    have h2 : ‖x‖^2 = ∑ j : Fin 3, (x j)^2 :=
      EuclideanSpace.real_norm_sq_eq x
    rw [h2]
    have h3 : ∀ j ∈ Finset.univ, 0 ≤ (x j)^2 := by
      intro j _
      positivity
    exact Finset.single_le_sum h3 (Finset.mem_univ i)
  have h4 : 0 ≤ |x i| := by positivity
  have h5 : |x i|^2 ≤ ‖x‖^2 := by
    have h6 : |x i|^2 = (x i)^2 := by rw [sq_abs]
    rw [h6]
    exact h1
  nlinarith [norm_nonneg x]

private lemma unit_norm_sub_le_angle {u v : Point3}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖u - v‖ ≤ InnerProductGeometry.angle u v := by
  set θ : ℝ := InnerProductGeometry.angle u v
  have hθ_nonneg : 0 ≤ θ := InnerProductGeometry.angle_nonneg u v
  have h_inner : inner ℝ u v = Real.cos θ := by
    have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm u v
    rw [hu, hv] at h
    linarith
  have h_uu : inner ℝ u u = ‖u‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K] <;> simp
  have h_vv : inner ℝ v v = ‖v‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K] <;> simp
  have h_vu : inner ℝ v u = inner ℝ u v :=
    (real_inner_comm v u).symm
  have h_norm_sq : ‖u - v‖ ^ 2 = 2 - 2 * Real.cos θ := by
    have h1 : ‖u - v‖ ^ 2 = inner ℝ (u - v) (u - v) := by
      rw [inner_self_eq_norm_sq_to_K] <;> simp
    have h21 : inner ℝ (u - v) (u - v) =
        inner ℝ u (u - v) - inner ℝ v (u - v) := by
      rw [inner_sub_left]
    have h22 : inner ℝ u (u - v) = inner ℝ u u - inner ℝ u v := by
      rw [inner_sub_right]
    have h23 : inner ℝ v (u - v) = inner ℝ v u - inner ℝ v v := by
      rw [inner_sub_right]
    have h2 : inner ℝ (u - v) (u - v) =
        inner ℝ u u - inner ℝ u v - inner ℝ v u + inner ℝ v v := by
      rw [h21, h22, h23]
      ring
    rw [h1, h2, h_uu, h_vv, h_vu, hu, hv, h_inner] <;>
      norm_num <;> ring
  have h_cos_double : Real.cos θ =
      1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h2 : Real.cos (2 * (θ / 2)) =
        2 * Real.cos (θ / 2) ^ 2 - 1 :=
      Real.cos_two_mul (θ / 2)
    have h3 : Real.cos (2 * (θ / 2)) = Real.cos θ := by ring_nf
    have h4 : Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 = 1 :=
      Real.cos_sq_add_sin_sq (θ / 2)
    linarith
  have h_sin_sq : ‖u - v‖ ^ 2 =
      4 * Real.sin (θ / 2) ^ 2 := by
    rw [h_norm_sq, h_cos_double]
    ring
  have h_sin_nonneg : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_mem_Icc
      ⟨by linarith,
        by linarith [InnerProductGeometry.angle_le_pi u v]⟩
  have h_sq2 : ‖u - v‖ ^ 2 =
      (2 * Real.sin (θ / 2)) ^ 2 := by
    rw [h_sin_sq]
    ring
  have h_eq : ‖u - v‖ = 2 * Real.sin (θ / 2) := by
    nlinarith [norm_nonneg (u - v)]
  have h_abs : |Real.sin (θ / 2)| ≤ |θ / 2| :=
    Real.abs_sin_le_abs (x := θ / 2)
  have h_sin_le : Real.sin (θ / 2) ≤ θ / 2 := by
    have h1 : 0 ≤ Real.sin (θ / 2) := h_sin_nonneg
    have h2 : 0 ≤ θ / 2 := by linarith
    have h3 : |Real.sin (θ / 2)| = Real.sin (θ / 2) :=
      abs_of_nonneg h1
    have h4 : |θ / 2| = θ / 2 := abs_of_nonneg h2
    rw [h3, h4] at h_abs
    exact h_abs
  rw [h_eq]
  linarith

private lemma angle_le_pi2_mul_norm_sub_local {u v : Point3}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    InnerProductGeometry.angle u v ≤ (Real.pi / 2) * ‖u - v‖ := by
  set theta : ℝ := InnerProductGeometry.angle u v
  have htheta_nonneg : 0 ≤ theta :=
    InnerProductGeometry.angle_nonneg u v
  have htheta_le_pi : theta ≤ Real.pi :=
    InnerProductGeometry.angle_le_pi u v
  have hinner : inner ℝ u v = Real.cos theta := by
    have h :=
      InnerProductGeometry.cos_angle_mul_norm_mul_norm u v
    rw [hu, hv] at h
    simpa [theta] using h.symm
  have hnorm_sq :
      ‖u - v‖ ^ 2 =
        (2 * Real.sin (theta / 2)) ^ 2 := by
    have hnorm :
        ‖u - v‖ ^ 2 =
          ‖u‖ ^ 2 - 2 * inner ℝ u v + ‖v‖ ^ 2 :=
      norm_sub_sq_real u v
    have hcos :
        Real.cos theta =
          1 - 2 * Real.sin (theta / 2) ^ 2 := by
      have htwo := Real.cos_two_mul (theta / 2)
      have htrig :=
        Real.sin_sq_add_cos_sq (theta / 2)
      have harg : 2 * (theta / 2) = theta := by ring
      rw [harg] at htwo
      nlinarith
    rw [hnorm, hu, hv, hinner, hcos]
    ring
  have hsin_nonneg : 0 ≤ Real.sin (theta / 2) :=
    Real.sin_nonneg_of_mem_Icc
      ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hnorm :
      ‖u - v‖ = 2 * Real.sin (theta / 2) := by
    nlinarith [norm_nonneg (u - v)]
  have hhalf_le : theta / 2 ≤ Real.pi / 2 := by
    linarith
  have hsin_lower :
      theta / 2 ≤
        (Real.pi / 2) * Real.sin (theta / 2) :=
    le_pi2_mul_sin (theta / 2) (by linarith) hhalf_le
  rw [hnorm]
  nlinarith [Real.pi_pos]

private lemma grid1d_close {r : ℝ} (hr : 0 < r) {x y : ℝ}
    (h : ⌊x / r⌋ = ⌊y / r⌋) : |x - y| < r := by
  have h3 : |x / r - y / r| < 1 :=
    Int.abs_sub_lt_one_of_floor_eq_floor h
  have h4 : |(x - y) / r| < 1 := by
    have h5 : (x - y) / r = x / r - y / r := by ring
    rw [h5]
    exact h3
  have h6 : |x - y| / r < 1 := by
    have h7 : |(x - y) / r| = |x - y| / r := by
      rw [abs_div]
      simp [abs_of_pos hr]
    rw [h7] at h4
    exact h4
  calc
    |x - y| = (|x - y| / r) * r := by
      field_simp [hr.ne'] <;> ring
    _ < 1 * r := by gcongr
    _ = r := by ring

private lemma norm_lt_sqrt3_of_coord_lt {p : Point3} {r : ℝ}
    (hr : 0 < r) (h : ∀ i : Fin 3, |p i| < r) :
    ‖p‖ < Real.sqrt 3 * r := by
  have h_sum : ‖p‖ ^ 2 = ∑ i : Fin 3, (p i) ^ 2 :=
    EuclideanSpace.real_norm_sq_eq p
  have h_sq_lt : ∀ i : Fin 3, (p i) ^ 2 < r ^ 2 := by
    intro i
    have h9 : |p i| < r := h i
    have h11 : |p i| ^ 2 < r ^ 2 := by
      nlinarith [abs_nonneg (p i)]
    have h12 : (p i) ^ 2 = |p i| ^ 2 := by rw [sq_abs]
    rw [h12]
    exact h11
  have h9 : ∑ i : Fin 3, (p i) ^ 2 < 3 * r ^ 2 := by
    have h10 : ∑ i : Fin 3, (p i) ^ 2 =
        (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 := by
      simp [Fin.sum_univ_succ]
      ring
    rw [h10]
    linarith [h_sq_lt 0, h_sq_lt 1, h_sq_lt 2]
  have h14 : ‖p‖ ^ 2 < 3 * r ^ 2 := by
    rw [h_sum]
    exact h9
  have h15 : 0 ≤ Real.sqrt 3 * r := by positivity
  nlinarith [norm_nonneg p, h15, Real.sqrt_nonneg 3,
    Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

lemma tube_packing_bound_general
    {delta : ℝ} {fine : Kakeya.Streamlined.TubeFamily delta}
    (hed : WZ1PaperIsEssentiallyDistinct fine)
    (hline : WZ1PaperIsLineClass fine)
    (hdelta : 0 < delta)
    (sep : ℝ) (hsep_pos : 0 < sep)
    (i : Fin fine.card) :
    (Finset.univ.filter fun j =>
      wz1PaperLineDistance (fine.tube j) (fine.tube i) ≤ sep).card ≤
      (2 * Nat.ceil (8 * sep / delta) + 1)^5 := by
  let c : ℝ := delta / 8
  have hc_pos : 0 < c := by positivity
  let K : ℕ := Nat.ceil (8 * sep / delta)
  have hK : (8 * sep / delta : ℝ) ≤ (K : ℝ) := Nat.le_ceil _
  let zp (j : Fin fine.card) : Point3 :=
    wz1TubeAxisZeroPoint (fine.tube j)
  let dir (j : Fin fine.card) : Point3 :=
    wz1PaperDirection (fine.tube j)
  have hdir_norm : ∀ j, ‖dir j‖ = 1 :=
    fun j => wz1PaperDirection_norm (fine.tube j)
  have h_zp_z : ∀ j, (zp j) 2 = 0 := by
    intro j
    exact wz1TubeAxisZeroPoint_coord_two
      (fine.tube j) (hline j).vertical
  let N : Finset (Fin fine.card) := Finset.univ.filter fun j =>
    wz1PaperLineDistance (fine.tube j) (fine.tube i) ≤ sep
  have hN_dist : ∀ j ∈ N, dist (zp j) (zp i) ≤ sep := by
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    have h2 : dist (zp j) (zp i) +
        InnerProductGeometry.angle (dir j) (dir i) ≤ sep := by
      simpa [wz1PaperLineDistance] using h
    linarith [InnerProductGeometry.angle_nonneg (dir j) (dir i)]
  have hN_angle : ∀ j ∈ N,
      InnerProductGeometry.angle (dir j) (dir i) ≤ sep := by
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    have h2 : dist (zp j) (zp i) +
        InnerProductGeometry.angle (dir j) (dir i) ≤ sep := by
      simpa [wz1PaperLineDistance] using h
    linarith [dist_nonneg (x := zp j) (y := zp i)]
  have hN_dir_dist : ∀ j ∈ N, ‖dir j - dir i‖ ≤ sep := by
    intro j hj
    exact (unit_norm_sub_le_angle (hdir_norm j) (hdir_norm i)).trans
      (hN_angle j hj)
  let encode (j : Fin fine.card) : ℤ × ℤ × ℤ × ℤ × ℤ :=
    (⌊((zp j - zp i) 0) / c⌋, ⌊((zp j - zp i) 1) / c⌋,
      ⌊((dir j - dir i) 0) / c⌋, ⌊((dir j - dir i) 1) / c⌋,
      ⌊((dir j - dir i) 2) / c⌋)
  have h_inj : Set.InjOn encode (N : Set (Fin fine.card)) := by
    intro j hj k hk h_eq
    by_contra h_ne
    have h_zp0 : ⌊((zp j - zp i) 0) / c⌋ =
        ⌊((zp k - zp i) 0) / c⌋ := by
      simp [encode, Prod.ext_iff] at h_eq <;> tauto
    have h_zp1 : ⌊((zp j - zp i) 1) / c⌋ =
        ⌊((zp k - zp i) 1) / c⌋ := by
      simp [encode, Prod.ext_iff] at h_eq <;> tauto
    have h_dir0 : ⌊((dir j - dir i) 0) / c⌋ =
        ⌊((dir k - dir i) 0) / c⌋ := by
      simp [encode, Prod.ext_iff] at h_eq <;> tauto
    have h_dir1 : ⌊((dir j - dir i) 1) / c⌋ =
        ⌊((dir k - dir i) 1) / c⌋ := by
      simp [encode, Prod.ext_iff] at h_eq <;> tauto
    have h_dir2 : ⌊((dir j - dir i) 2) / c⌋ =
        ⌊((dir k - dir i) 2) / c⌋ := by
      simp [encode, Prod.ext_iff] at h_eq <;> tauto
    have h_zp_close0 : |(zp j - zp k) 0| < c := by
      have h_eq2 : (zp j - zp k) 0 =
          (zp j - zp i) 0 - (zp k - zp i) 0 := by
        simp [Pi.sub_apply] <;> ring
      exact h_eq2 ▸ grid1d_close hc_pos h_zp0
    have h_zp_close1 : |(zp j - zp k) 1| < c := by
      have h_eq2 : (zp j - zp k) 1 =
          (zp j - zp i) 1 - (zp k - zp i) 1 := by
        simp [Pi.sub_apply] <;> ring
      exact h_eq2 ▸ grid1d_close hc_pos h_zp1
    have h_zp_close2 : |(zp j - zp k) 2| < c := by
      have h_eq2 : (zp j - zp k) 2 = 0 := by
        simp [h_zp_z j, h_zp_z k]
      rw [h_eq2]
      simp [hc_pos]
    have h_zp_close : ∀ l : Fin 3, |(zp j - zp k) l| < c := by
      intro l
      fin_cases l <;> tauto
    have h_dir_close0 : |(dir j - dir k) 0| < c := by
      have h_eq2 : (dir j - dir k) 0 =
          (dir j - dir i) 0 - (dir k - dir i) 0 := by
        simp [Pi.sub_apply] <;> ring
      exact h_eq2 ▸ grid1d_close hc_pos h_dir0
    have h_dir_close1 : |(dir j - dir k) 1| < c := by
      have h_eq2 : (dir j - dir k) 1 =
          (dir j - dir i) 1 - (dir k - dir i) 1 := by
        simp [Pi.sub_apply] <;> ring
      exact h_eq2 ▸ grid1d_close hc_pos h_dir1
    have h_dir_close2 : |(dir j - dir k) 2| < c := by
      have h_eq2 : (dir j - dir k) 2 =
          (dir j - dir i) 2 - (dir k - dir i) 2 := by
        simp [Pi.sub_apply] <;> ring
      exact h_eq2 ▸ grid1d_close hc_pos h_dir2
    have h_dir_close : ∀ l : Fin 3, |(dir j - dir k) l| < c := by
      intro l
      fin_cases l <;> tauto
    have h_zp_dist : ‖zp j - zp k‖ < Real.sqrt 3 * c :=
      norm_lt_sqrt3_of_coord_lt hc_pos h_zp_close
    have h_dir_dist : ‖dir j - dir k‖ < Real.sqrt 3 * c :=
      norm_lt_sqrt3_of_coord_lt hc_pos h_dir_close
    have h_angle : InnerProductGeometry.angle (dir j) (dir k) ≤
        (Real.pi / 2) * ‖dir j - dir k‖ :=
      angle_le_pi2_mul_norm_sub_local (hdir_norm j) (hdir_norm k)
    have h_line_lt :
        wz1PaperLineDistance (fine.tube j) (fine.tube k) < delta := by
      change dist (zp j) (zp k) +
          InnerProductGeometry.angle (dir j) (dir k) < delta
      have h_bound :
          ‖zp j - zp k‖ +
              InnerProductGeometry.angle (dir j) (dir k) < delta := by
        calc
          ‖zp j - zp k‖ +
                InnerProductGeometry.angle (dir j) (dir k)
              ≤ ‖zp j - zp k‖ +
                (Real.pi / 2) * ‖dir j - dir k‖ := by
                  gcongr
          _ < Real.sqrt 3 * c +
                (Real.pi / 2) * (Real.sqrt 3 * c) := by
                  gcongr
          _ = Real.sqrt 3 * c * (1 + Real.pi / 2) := by ring
          _ = Real.sqrt 3 * (delta / 8) *
                (1 + Real.pi / 2) := by rfl
          _ ≤ delta := by
            have hpi : Real.pi ≤ 4 := Real.pi_le_four
            have hsqrt3 : Real.sqrt 3 ≤ 2 := by
              nlinarith [Real.sqrt_nonneg 3,
                Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
            have h' : Real.sqrt 3 * (1 + Real.pi / 2) ≤ 8 := by
              nlinarith [Real.sqrt_nonneg 3, Real.pi_nonneg]
            calc
              Real.sqrt 3 * (delta / 8) *
                    (1 + Real.pi / 2)
                  = delta *
                    (Real.sqrt 3 * (1 + Real.pi / 2) / 8) := by ring
              _ ≤ delta * 1 := by gcongr <;> linarith
              _ = delta := by ring
      simpa [dist_eq_norm] using h_bound
    have h_ed :
        delta < wz1PaperLineDistance (fine.tube j) (fine.tube k) :=
      hed j k h_ne
    exact not_le.mpr h_ed (le_of_lt h_line_lt)
  let B : ℤ := (K : ℤ)
  let S_int : Finset ℤ := Finset.Icc (-B) B
  have h_coord_bound : ∀ (x : ℝ), |x| ≤ sep → ⌊x / c⌋ ∈ S_int := by
    intro x hx
    have h1 : -sep ≤ x := by linarith [abs_le.mp hx]
    have h2 : x ≤ sep := by linarith [abs_le.mp hx]
    have h3 : -sep / c ≤ x / c := by gcongr
    have h4 : x / c ≤ sep / c := by gcongr
    have h5 : sep / c = 8 * sep / delta := by
      simp [c] <;> field_simp [hdelta.ne'] <;> ring
    rw [h5] at h4
    have h6 : -sep / c = -(8 * sep / delta) := by
      simp [c] <;> field_simp [hdelta.ne'] <;> ring
    rw [h6] at h3
    have h7 : (-B : ℤ) ≤ ⌊x / c⌋ := by
      have h_negK : (-B : ℝ) = -(K : ℝ) := by simp [B]
      have h9 : -(K : ℝ) ≤ -(8 * sep / delta) := by linarith [hK]
      have h8 : (-B : ℝ) ≤ x / c := by
        rw [h_negK]
        exact h9.trans h3
      have h8' : (↑(-B) : ℝ) ≤ x / c := by
        have h_eq : (↑(-B) : ℝ) = -↑B := by simp
        rw [h_eq]
        exact h8
      exact Int.le_floor.mpr h8'
    have h9 : ⌊x / c⌋ ≤ B := by
      have h10 : (⌊x / c⌋ : ℝ) ≤ x / c := Int.floor_le _
      have h11 : (⌊x / c⌋ : ℝ) ≤ (K : ℝ) := by linarith
      have h12 : (⌊x / c⌋ : ℝ) ≤ (B : ℝ) := by
        simpa [B] using h11
      exact_mod_cast h12
    exact Finset.mem_Icc.mpr ⟨h7, h9⟩
  let S5 : Finset (ℤ × ℤ × ℤ × ℤ × ℤ) :=
    S_int ×ˢ S_int ×ˢ S_int ×ˢ S_int ×ˢ S_int
  have h_encode_in_range : ∀ j ∈ N, encode j ∈ S5 := by
    intro j hj
    have h_zp0 : |(zp j - zp i) 0| ≤ sep := by
      exact (coord_le_norm (zp j - zp i) 0).trans (by
        simpa [dist_eq_norm] using hN_dist j hj)
    have h_zp1 : |(zp j - zp i) 1| ≤ sep := by
      exact (coord_le_norm (zp j - zp i) 1).trans (by
        simpa [dist_eq_norm] using hN_dist j hj)
    have h_dir0 : |(dir j - dir i) 0| ≤ sep :=
      (coord_le_norm (dir j - dir i) 0).trans (hN_dir_dist j hj)
    have h_dir1 : |(dir j - dir i) 1| ≤ sep :=
      (coord_le_norm (dir j - dir i) 1).trans (hN_dir_dist j hj)
    have h_dir2 : |(dir j - dir i) 2| ≤ sep :=
      (coord_le_norm (dir j - dir i) 2).trans (hN_dir_dist j hj)
    simp only [S5, Finset.mem_product]
    exact ⟨h_coord_bound _ h_zp0, h_coord_bound _ h_zp1,
      h_coord_bound _ h_dir0, h_coord_bound _ h_dir1,
      h_coord_bound _ h_dir2⟩
  have h_image_subset : Finset.image encode N ⊆ S5 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨j, hj, rfl⟩
    exact h_encode_in_range j hj
  have h_card_image : (Finset.image encode N).card = N.card := by
    rw [Finset.card_image_of_injOn h_inj]
  have h_card_S5 : S5.card = S_int.card ^ 5 := by
    simp [S5, Finset.card_product] <;> ring
  have h_card_Sint : S_int.card = 2 * K + 1 := by
    have hB_nonneg : 0 ≤ B := by
      simp [B, K] <;> exact Nat.cast_nonneg K
    have h_le : (-B : ℤ) ≤ B + 1 := by linarith
    have h' : (S_int.card : ℤ) = B + 1 - (-B) :=
      Int.card_Icc_of_le (-B) B h_le
    have h_eq1 : B + 1 - (-B) = 2 * (B : ℤ) + 1 := by ring
    have h_card_int : (S_int.card : ℤ) = 2 * (B : ℤ) + 1 := by
      rw [h', h_eq1]
    have h3 : (S_int.card : ℤ) = ↑(2 * K + 1) := by
      simpa [B] using h_card_int
    exact_mod_cast h3
  calc
    N.card = (Finset.image encode N).card := h_card_image.symm
    _ ≤ S5.card := Finset.card_le_card h_image_subset
    _ = S_int.card ^ 5 := h_card_S5
    _ = (2 * K + 1) ^ 5 := by rw [h_card_Sint]

lemma tube_packing_bound1000
    {delta : ℝ} {fine : Kakeya.Streamlined.TubeFamily delta}
    (hed : WZ1PaperIsEssentiallyDistinct fine)
    (hline : WZ1PaperIsLineClass fine)
    (hdelta : 0 < delta)
    (i : Fin fine.card) :
    (Finset.univ.filter fun j =>
      wz1PaperLineDistance (fine.tube j) (fine.tube i) ≤
        1000 * delta).card ≤ packingConstant1000 := by
  have h := tube_packing_bound_general hed hline hdelta
    (1000 * delta) (by positivity) i
  have hK : Nat.ceil (8 * (1000 * delta) / delta) = 8000 := by
    have h1 : 8 * (1000 * delta) / delta = 8000 := by
      field_simp [hdelta.ne']
      ring
    rw [h1]
    norm_num
  rw [hK] at h
  simpa [packingConstant1000] using h

lemma tube_packing_bound10000
    {delta : ℝ} {fine : Kakeya.Streamlined.TubeFamily delta}
    (hed : WZ1PaperIsEssentiallyDistinct fine)
    (hline : WZ1PaperIsLineClass fine)
    (hdelta : 0 < delta)
    (i : Fin fine.card) :
    (Finset.univ.filter fun j =>
      wz1PaperLineDistance (fine.tube j) (fine.tube i) ≤
        10000 * delta).card ≤ packingConstant10000 := by
  have h := tube_packing_bound_general hed hline hdelta
    (10000 * delta) (by positivity) i
  have hK : Nat.ceil (8 * (10000 * delta) / delta) = 80000 := by
    have h1 : 8 * (10000 * delta) / delta = 80000 := by
      field_simp [hdelta.ne']
      ring
    rw [h1]
    norm_num
  rw [hK] at h
  exact h.trans (by
    norm_num [packingConstant10000])

theorem wz1PaperPackingRefinementGeneral
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    (sep : ℝ) (C : ℕ)
    (hC_bound : ∀ i : Fin fine.card,
      (Finset.univ.filter fun j =>
        wz1PaperLineDistance (fine.tube j) (fine.tube i) ≤ sep).card ≤ C)
    (hsep_nonneg : 0 ≤ sep) :
    ∃ (selected : Kakeya.Streamlined.TubeSubfamily fine)
      (refined : WZ1PaperTubeShading selected.family),
      (∀ i j, i ≠ j →
        wz1PaperLineDistance
          (selected.family.tube i) (selected.family.tube j) > sep) ∧
      (∀ i, refined.carrier i ⊆
        shading.carrier (selected.embedding i)) ∧
      (C : ENNReal) * refined.mass ≥ shading.mass := by
  let w : Fin fine.card → ENNReal :=
    fun i => MeasureTheory.volume (shading.carrier i)
  let adj : Fin fine.card → Fin fine.card → Prop :=
    fun i j =>
      wz1PaperLineDistance (fine.tube i) (fine.tube j) ≤ sep
  have hdir_ne_zero :
      ∀ k : Fin fine.card, wz1PaperDirection (fine.tube k) ≠ 0 := by
    intro k h
    have hnorm := wz1PaperDirection_norm (fine.tube k)
    rw [h] at hnorm
    norm_num at hnorm
  have hrefl : ∀ i, adj i i := by
    intro i
    have h0 : wz1PaperLineDistance (fine.tube i) (fine.tube i) = 0 := by
      simp [wz1PaperLineDistance, dist_self]
      <;> rw [InnerProductGeometry.angle_self (hdir_ne_zero i)] <;> simp
    simp only [adj, h0] <;> linarith
  have hsymm : ∀ i j, adj i j → adj j i := by
    intro i j h
    simpa [adj, wz1PaperLineDistance, dist_comm,
      InnerProductGeometry.angle_comm] using h
  have hC : ∀ i, (Finset.univ.filter (adj i)).card ≤ C := by
    intro i
    have h_eq : (Finset.univ.filter (adj i)) =
        Finset.univ.filter (fun j =>
          wz1PaperLineDistance (fine.tube j) (fine.tube i) ≤ sep) := by
      ext j
      simp only [adj, Finset.mem_filter, Finset.mem_univ, true_and]
      have h_sym :
          wz1PaperLineDistance (fine.tube i) (fine.tube j) =
            wz1PaperLineDistance (fine.tube j) (fine.tube i) := by
        simp [wz1PaperLineDistance, dist_comm,
          InnerProductGeometry.angle_comm] <;> rfl
      rw [h_sym]
    rw [h_eq]
    exact hC_bound i
  rcases exists_independent_set_mass_retention
      w adj hrefl hsymm C hC with ⟨S, hindep, hmass⟩
  let selected := Kakeya.Streamlined.TubeSubfamily.fromFinset fine S
  let refined : WZ1PaperTubeShading selected.family :=
    { carrier := fun i => shading.carrier (selected.embedding i)
      measurable_carrier := fun i =>
        shading.measurable_carrier (selected.embedding i)
      subset_body := fun i => by
        have h := shading.subset_body (selected.embedding i)
        have h_eq : selected.family.tube i =
            fine.tube (selected.embedding i) := selected.tube_eq i
        rw [h_eq] at *
        exact h }
  have h_emb_range :
      ∀ i : Fin selected.family.card, selected.embedding i ∈ S := by
    intro i
    exact Finset.orderEmbOfFin_mem S rfl i
  have h_sep : ∀ i j : Fin selected.family.card, i ≠ j →
      wz1PaperLineDistance
        (selected.family.tube i) (selected.family.tube j) > sep := by
    intro i j hne
    have h1 : selected.embedding i ≠ selected.embedding j :=
      fun h => hne (selected.embedding.inj' h)
    have h2 : ¬ adj (selected.embedding i) (selected.embedding j) :=
      hindep (selected.embedding i) (h_emb_range i)
        (selected.embedding j) (h_emb_range j) h1
    simpa [adj, selected.tube_eq] using not_le.mp h2
  have h_image : Finset.image selected.embedding Finset.univ = S := by
    have h1 : Finset.image selected.embedding Finset.univ ⊆ S := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      exact h_emb_range i
    have h2 : (Finset.image selected.embedding Finset.univ).card = S.card := by
      calc
        (Finset.image selected.embedding Finset.univ).card =
            (Finset.univ : Finset (Fin selected.family.card)).card :=
          Finset.card_image_of_injective _ selected.embedding.inj'
        _ = selected.family.card := by simp
        _ = S.card := rfl
    exact Finset.eq_of_subset_of_card_le h1 (le_of_eq h2.symm)
  have h_mass : refined.mass = ∑ i ∈ S, w i := by
    calc
      refined.mass =
          ∑ i : Fin selected.family.card,
            w (selected.embedding i) := rfl
      _ = ∑ j ∈ Finset.image selected.embedding Finset.univ, w j := by
        rw [Finset.sum_image]
        exact fun _ _ _ _ h => selected.embedding.inj' h
      _ = ∑ i ∈ S, w i := by rw [h_image]
  refine ⟨selected, refined, h_sep, fun _ => Set.Subset.rfl, ?_⟩
  rw [h_mass]
  exact hmass

theorem wz1PaperPackingRefinement1000
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    (hed : WZ1PaperIsEssentiallyDistinct fine)
    (hline : WZ1PaperIsLineClass fine)
    (hdelta : 0 < delta)
    (_hdelta_small : delta ≤ 1 / 10000) :
    ∃ (selected : Kakeya.Streamlined.TubeSubfamily fine)
      (refined : WZ1PaperTubeShading selected.family),
      (∀ i j, i ≠ j →
        wz1PaperLineDistance
          (selected.family.tube i) (selected.family.tube j) >
            1000 * delta) ∧
      (∀ i, refined.carrier i ⊆
        shading.carrier (selected.embedding i)) ∧
      (packingConstant1000 : ENNReal) * refined.mass ≥ shading.mass :=
  wz1PaperPackingRefinementGeneral
    (1000 * delta) packingConstant1000
    (fun i => tube_packing_bound1000 hed hline hdelta i)
    (by positivity)

theorem wz1PaperPackingRefinement10000
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    (hed : WZ1PaperIsEssentiallyDistinct fine)
    (hline : WZ1PaperIsLineClass fine)
    (hdelta : 0 < delta)
    (_hdelta_small : delta ≤ 1 / 10000) :
    ∃ (selected : Kakeya.Streamlined.TubeSubfamily fine)
      (refined : WZ1PaperTubeShading selected.family),
      (∀ i j, i ≠ j →
        wz1PaperLineDistance
          (selected.family.tube i) (selected.family.tube j) >
            10000 * delta) ∧
      (∀ i, refined.carrier i ⊆
        shading.carrier (selected.embedding i)) ∧
      (packingConstant10000 : ENNReal) * refined.mass ≥ shading.mass :=
  wz1PaperPackingRefinementGeneral
    (10000 * delta) packingConstant10000
    (fun i => tube_packing_bound10000 hed hline hdelta i)
    (by positivity)

end Kakeya.Assouad
