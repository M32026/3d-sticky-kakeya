import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowDotSpreadFromConcentration
import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowTripleConcentratedStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.AngleGeometryBase
import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowConcentrationArithmetic

namespace Kakeya.Assouad

/-- Dual norm bound: if two unit vectors are sufficiently transverse, the sum of absolute inner products controls the Euclidean norm. -/
lemma dual_norm_bound (u direction : Point2) (hu : ‖u‖ = 1) (hdir : ‖direction‖ = 1)
    (h_angle : |inner ℝ u direction| ≤ 1 / Real.sqrt 2) :
    ∀ (d : Point2), ‖d‖ ≤ 2 * (|inner ℝ d u| + |inner ℝ d direction|) := by
  intro d
  let p := wz1Perp2 u
  have hp_norm : ‖p‖ = 1 := by
    have hsq : ‖p‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [norm2_sq, norm2_sq]
      have hpc := wz1Perp2_coords u
      rw [hpc.1, hpc.2] <;> ring
    have h12 : (‖p‖ - ‖u‖) * (‖p‖ + ‖u‖) = 0 := by linarith
    have h13 : 0 < ‖p‖ + ‖u‖ := by positivity
    have h14 : ‖p‖ - ‖u‖ = 0 := (mul_eq_zero.mp h12).resolve_right h13.ne'
    have h15 : ‖p‖ = ‖u‖ := by linarith
    rw [h15, hu]
  have hdecomp : d = (inner ℝ d u) • u + (inner ℝ d p) • p := orthonormal_decomp d u hu
  set a := inner ℝ d u with ha
  set c := inner ℝ d p with hc
  set b := inner ℝ d direction with hb
  set cuw := inner ℝ u direction with hcuw_def
  set cpw := inner ℝ p direction with hcpw_def
  have h1 : cuw^2 + cpw^2 = 1 := by
    have h := norm_cross_identity direction u hu
    have hdir2 : ‖direction‖ ^ 2 = 1 := by rw [hdir] <;> norm_num
    have hcuw' : inner ℝ direction u = cuw := by
      simp [cuw, real_inner_comm]
    have hpc := wz1Perp2_coords u
    have h_cpw_eq : cpw = u 0 * direction 1 - u 1 * direction 0 := by
      simp [cpw, p, inner2_eq, hpc.1, hpc.2] <;> ring
    have h_cross_eq : cross2 direction u = direction 0 * u 1 - direction 1 * u 0 := by rfl
    have hcross : cross2 direction u = -cpw := by
      rw [h_cross_eq, h_cpw_eq] <;> ring
    rw [hdir2, hcuw', hcross] at h
    have h' : (1 : ℝ) = cuw ^ 2 + (-cpw) ^ 2 := h
    have h'' : (-cpw) ^ 2 = cpw ^ 2 := by ring
    rw [h''] at h'
    exact h'.symm
  have hcuw_abs : |cuw| ≤ 1 / Real.sqrt 2 := by
    simpa [cuw] using h_angle
  have h_sqrt2_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h11 : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    calc
      (1 / Real.sqrt 2) ^ 2 = 1 / (Real.sqrt 2) ^ 2 := by ring
      _ = 1 / 2 := by rw [h_sqrt2_sq]
  have hcuw_sq : cuw^2 ≤ 1 / 2 := by
    have h9 : |cuw| ^ 2 ≤ (1 / Real.sqrt 2) ^ 2 := by gcongr
    have h10 : |cuw| ^ 2 = cuw^2 := by simp [sq_abs]
    rw [h10, h11] at h9
    exact h9
  have h2 : cpw^2 ≥ 1 / 2 := by linarith [h1, hcuw_sq]
  have hcpw_ne : cpw ≠ 0 := by
    intro hz
    rw [hz] at h2
    norm_num at h2
  have h3 : b = a * cuw + c * cpw := by
    calc
      b = inner ℝ d direction := by simp [hb]
      _ = inner ℝ (a • u + c • p) direction := by rw [hdecomp]
      _ = a * inner ℝ u direction + c * inner ℝ p direction := by
        rw [inner_add_left, inner_smul_left, inner_smul_left]
        simp [mul_comm] <;> ring
      _ = a * cuw + c * cpw := by
        simp [hcuw_def, hcpw_def] <;> ring
  have h_eq : b - a * cuw = c * cpw := by linarith [h3]
  have h4 : c = (b - a * cuw) / cpw := by
    calc
      c = (c * cpw) / cpw := by field_simp [hcpw_ne] <;> ring
      _ = (b - a * cuw) / cpw := by rw [h_eq]
  have h_abs_cpw : |cpw| ≥ 1 / Real.sqrt 2 := by
    have h7 : cpw^2 ≥ 1 / 2 := h2
    have h8 : |cpw| ^ 2 ≥ (1 / Real.sqrt 2) ^ 2 := by
      rw [h11] at * <;> simpa [sq_abs] using h7
    have h9 : 0 ≤ |cpw| := abs_nonneg cpw
    have h10 : 0 ≤ 1 / Real.sqrt 2 := by positivity
    nlinarith
  have h5 : |c| ≤ |a| + Real.sqrt 2 * |b| := by
    rw [h4]
    have h9 : |b - a * cuw| ≤ |b| + |a * cuw| := abs_sub _ _
    have h10 : |a * cuw| = |a| * |cuw| := by rw [abs_mul]
    have h11 : |cuw| ≤ 1 / Real.sqrt 2 := hcuw_abs
    have h_num : |b| + |a| * |cuw| ≤ |b| + |a| * (1 / Real.sqrt 2) := by
      have h : |a| * |cuw| ≤ |a| * (1 / Real.sqrt 2) :=
        mul_le_mul_of_nonneg_left h11 (abs_nonneg a)
      linarith
    calc
      |(b - a * cuw) / cpw|
        = |b - a * cuw| / |cpw| := by rw [abs_div]
      _ ≤ (|b| + |a| * |cuw|) / |cpw| := by
        rw [h10] at h9
        exact div_le_div_of_nonneg_right h9 (abs_nonneg cpw)
      _ ≤ (|b| + |a| * (1 / Real.sqrt 2)) / |cpw| := by
        gcongr
      _ ≤ (|b| + |a| * (1 / Real.sqrt 2)) / (1 / Real.sqrt 2) := by
        set N := |b| + |a| * (1 / Real.sqrt 2) with hN_def
        have hN_nonneg : 0 ≤ N := by positivity
        have h1 : 0 < 1 / Real.sqrt 2 := by positivity
        have h2 : 1 / |cpw| ≤ 1 / (1 / Real.sqrt 2) := by
          apply one_div_le_one_div_of_le
          · positivity
          · exact h_abs_cpw
        have h3 : N / |cpw| = N * (1 / |cpw|) := by ring
        have h4 : N / (1 / Real.sqrt 2) = N * (1 / (1 / Real.sqrt 2)) := by ring
        rw [h3, h4]
        exact mul_le_mul_of_nonneg_left h2 hN_nonneg
      _ = |a| + Real.sqrt 2 * |b| := by
        field_simp <;> ring
  have h6 : ‖d‖ ≤ |a| + |c| := by
    rw [hdecomp]
    have h_norm1 : ‖a • u‖ = |a| := by
      rw [norm_smul, hu]
      have h : ‖a‖ = |a| := by simp
      rw [h] <;> ring
    have h_norm2 : ‖c • p‖ = |c| := by
      rw [norm_smul, hp_norm]
      have h : ‖c‖ = |c| := by simp
      rw [h] <;> ring
    calc
      ‖a • u + c • p‖ ≤ ‖a • u‖ + ‖c • p‖ := norm_add_le _ _
      _ = |a| + |c| := by rw [h_norm1, h_norm2]
  have h7 : ‖d‖ ≤ 2 * (|a| + |b|) := by
    calc
      ‖d‖ ≤ |a| + |c| := h6
      _ ≤ |a| + (|a| + Real.sqrt 2 * |b|) := by gcongr
      _ = 2 * |a| + Real.sqrt 2 * |b| := by ring
      _ ≤ 2 * (|a| + |b|) := by
        have h8 : Real.sqrt 2 ≤ 2 := by
          nlinarith [Real.sqrt_nonneg 2, h_sqrt2_sq]
        have h9 : 0 ≤ |b| := abs_nonneg b
        have h10 : Real.sqrt 2 * |b| ≤ 2 * |b| := mul_le_mul_of_nonneg_right h8 h9
        have h11 : 2 * |a| + Real.sqrt 2 * |b| ≤ 2 * (|a| + |b|) := by
          calc
            2 * |a| + Real.sqrt 2 * |b|
              ≤ 2 * |a| + 2 * |b| := by gcongr
            _ = 2 * (|a| + |b|) := by ring
        exact h11
  simpa [ha, hb] using h7

/-- Grid packing bound for a δ-separated set in a coordinate rectangle. -/
lemma grid_packing_bound
    (X : Finset Point2) (delta s : ℝ) (hdelta_pos : 0 < delta) (hs_pos : 0 < s)
    (u v : Point2)
    (h_dual : ∀ (d : Point2), ‖d‖ ≤ 2 * (|inner ℝ d u| + |inner ℝ d v|))
    (h_sep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → delta ≤ dist x y)
    (c_u R_u R_v : ℝ)
    (hR_u_nonneg : 0 ≤ R_u) (hR_v_nonneg : 0 ≤ R_v)
    (h_bound_u : ∀ x ∈ X, |inner ℝ x u - c_u| ≤ R_u)
    (h_bound_v : ∀ x ∈ X, |inner ℝ x v| ≤ R_v)
    (h_small : 4 * s < delta) :
    (X.card : ℝ) ≤ (2 * R_u / s + 1) * (2 * R_v / s + 1) := by
  -- Shifted coordinates: lower endpoint is 0, so floor values start at 0
  let i_of (x : Point2) : ℤ := Int.floor ((inner ℝ x u - (c_u - R_u)) / s)
  let j_of (x : Point2) : ℤ := Int.floor ((inner ℝ x v + R_v) / s)
  have h_inj : Set.InjOn (fun x : Point2 => (i_of x, j_of x)) (X : Set Point2) := by
    intro x hx y hy h_eq
    by_contra hne
    have h_i_eq : i_of x = i_of y := congrArg Prod.fst h_eq
    have h_j_eq : j_of x = j_of y := congrArg Prod.snd h_eq
    have h1 : |inner ℝ x u - inner ℝ y u| ≤ s := by
      set vx := (inner ℝ x u - (c_u - R_u)) / s with hvx
      set vy := (inner ℝ y u - (c_u - R_u)) / s with hvy
      have h_i1 : (i_of x : ℝ) ≤ vx := Int.floor_le _
      have h_i2 : vx < (i_of x : ℝ) + 1 := Int.lt_floor_add_one _
      have h_i3 : (i_of y : ℝ) ≤ vy := Int.floor_le _
      have h_i4 : vy < (i_of y : ℝ) + 1 := Int.lt_floor_add_one _
      rw [h_i_eq] at *
      have h5 : |vx - vy| < 1 := by rw [abs_lt] <;> constructor <;> linarith
      have h_eq2 : vx - vy = (inner ℝ x u - inner ℝ y u) / s := by
        simp [hvx, hvy] <;> ring
      rw [h_eq2] at h5
      have h6 : |(inner ℝ x u - inner ℝ y u) / s| < 1 := h5
      have h7 : |inner ℝ x u - inner ℝ y u| < s := by
        have h8 : |(inner ℝ x u - inner ℝ y u) / s| = |inner ℝ x u - inner ℝ y u| / s := by
          rw [abs_div, abs_of_pos hs_pos]
        rw [h8] at h6
        exact (div_lt_one hs_pos).mp h6
      exact le_of_lt h7
    have h2 : |inner ℝ x v - inner ℝ y v| ≤ s := by
      set vx := (inner ℝ x v + R_v) / s with hvx
      set vy := (inner ℝ y v + R_v) / s with hvy
      have h_j1 : (j_of x : ℝ) ≤ vx := Int.floor_le _
      have h_j2 : vx < (j_of x : ℝ) + 1 := Int.lt_floor_add_one _
      have h_j3 : (j_of y : ℝ) ≤ vy := Int.floor_le _
      have h_j4 : vy < (j_of y : ℝ) + 1 := Int.lt_floor_add_one _
      rw [h_j_eq] at *
      have h5 : |vx - vy| < 1 := by rw [abs_lt] <;> constructor <;> linarith
      have h_eq2 : vx - vy = (inner ℝ x v - inner ℝ y v) / s := by
        simp [hvx, hvy] <;> ring
      rw [h_eq2] at h5
      have h6 : |(inner ℝ x v - inner ℝ y v) / s| < 1 := h5
      have h7 : |inner ℝ x v - inner ℝ y v| < s := by
        have h8 : |(inner ℝ x v - inner ℝ y v) / s| = |inner ℝ x v - inner ℝ y v| / s := by
          rw [abs_div, abs_of_pos hs_pos]
        rw [h8] at h6
        exact (div_lt_one hs_pos).mp h6
      exact le_of_lt h7
    have h3 : ‖x - y‖ < delta := by
      have h4 : ‖x - y‖ ≤ 2 * (|inner ℝ (x - y) u| + |inner ℝ (x - y) v|) := h_dual (x - y)
      have h5 : |inner ℝ (x - y) u| ≤ s := by
        have h6 : inner ℝ (x - y) u = inner ℝ x u - inner ℝ y u := by rw [inner_sub_left]
        rw [h6]; exact h1
      have h7 : |inner ℝ (x - y) v| ≤ s := by
        have h8 : inner ℝ (x - y) v = inner ℝ x v - inner ℝ y v := by rw [inner_sub_left]
        rw [h8]; exact h2
      calc
        ‖x - y‖ ≤ 2 * (s + s) := by linarith [h4, h5, h7]
        _ = 4 * s := by ring
        _ < delta := h_small
    have h9 : delta ≤ dist x y := h_sep x hx y hy hne
    have h10 : dist x y = ‖x - y‖ := by simp [dist_eq_norm]
    rw [h10] at h9
    linarith
  let img : Finset (ℤ × ℤ) := X.image (fun x => (i_of x, j_of x))
  have h_img_card : img.card = X.card := by
    rw [Finset.card_image_of_injOn h_inj]
  have h_i_range : ∀ x ∈ X, 0 ≤ i_of x ∧ (i_of x : ℝ) ≤ 2 * R_u / s := by
    intro x hx
    have h1 : 0 ≤ inner ℝ x u - (c_u - R_u) := by
      have h := (abs_le.mp (h_bound_u x hx)).1
      linarith
    have h2 : inner ℝ x u - (c_u - R_u) ≤ 2 * R_u := by
      have h := (abs_le.mp (h_bound_u x hx)).2
      linarith
    have h3 : 0 ≤ (inner ℝ x u - (c_u - R_u)) / s := by positivity
    have h4 : (inner ℝ x u - (c_u - R_u)) / s ≤ 2 * R_u / s := by gcongr
    exact ⟨Int.floor_nonneg.mpr h3, by
      have h5 : (i_of x : ℝ) ≤ (inner ℝ x u - (c_u - R_u)) / s := Int.floor_le _
      linarith⟩
  have h_j_range : ∀ x ∈ X, 0 ≤ j_of x ∧ (j_of x : ℝ) ≤ 2 * R_v / s := by
    intro x hx
    have h1 : 0 ≤ inner ℝ x v + R_v := by
      have h := (abs_le.mp (h_bound_v x hx)).1
      linarith
    have h2 : inner ℝ x v + R_v ≤ 2 * R_v := by
      have h := (abs_le.mp (h_bound_v x hx)).2
      linarith
    have h3 : 0 ≤ (inner ℝ x v + R_v) / s := by positivity
    have h4 : (inner ℝ x v + R_v) / s ≤ 2 * R_v / s := by gcongr
    exact ⟨Int.floor_nonneg.mpr h3, by
      have h5 : (j_of x : ℝ) ≤ (inner ℝ x v + R_v) / s := Int.floor_le _
      linarith⟩
  by_cases hX : X.Nonempty
  · have hR_u_nonneg : 0 ≤ R_u := by
      rcases hX with ⟨x, hx⟩
      have h1 : 0 ≤ |inner ℝ x u - c_u| := abs_nonneg _
      have h2 : |inner ℝ x u - c_u| ≤ R_u := h_bound_u x hx
      linarith
    have hR_v_nonneg : 0 ≤ R_v := by
      rcases hX with ⟨x, hx⟩
      have h1 : 0 ≤ |inner ℝ x v| := abs_nonneg _
      have h2 : |inner ℝ x v| ≤ R_v := h_bound_v x hx
      linarith
    let hi_i : ℤ := Int.floor (2 * R_u / s)
    let hi_j : ℤ := Int.floor (2 * R_v / s)
    have h_hi_i_nonneg : 0 ≤ hi_i := by
      have h : 0 ≤ 2 * R_u / s := by positivity
      exact Int.floor_nonneg.mpr h
    have h_hi_j_nonneg : 0 ≤ hi_j := by
      have h : 0 ≤ 2 * R_v / s := by positivity
      exact Int.floor_nonneg.mpr h
    let N1 : ℕ := hi_i.toNat + 1
    let N2 : ℕ := hi_j.toNat + 1
    let i_of' (x : Point2) : ℕ := (i_of x).toNat
    let j_of' (x : Point2) : ℕ := (j_of x).toNat
    have h_i'_range : ∀ x ∈ X, i_of' x < N1 := by
      intro x hx
      have h1 : 0 ≤ i_of x := (h_i_range x hx).1
      have h2 : (i_of x : ℝ) ≤ 2 * R_u / s := (h_i_range x hx).2
      have h3 : i_of x ≤ hi_i := by
        have h4 : i_of x ≤ Int.floor (2 * R_u / s) := by
          rw [Int.le_floor] <;> exact h2
        simpa [hi_i] using h4
      have h4 : (i_of' x : ℤ) = i_of x := Int.toNat_of_nonneg h1
      have h5 : (hi_i.toNat : ℤ) = hi_i := Int.toNat_of_nonneg h_hi_i_nonneg
      omega
    have h_j'_range : ∀ x ∈ X, j_of' x < N2 := by
      intro x hx
      have h1 : 0 ≤ j_of x := (h_j_range x hx).1
      have h2 : (j_of x : ℝ) ≤ 2 * R_v / s := (h_j_range x hx).2
      have h3 : j_of x ≤ hi_j := by
        have h4 : j_of x ≤ Int.floor (2 * R_v / s) := by
          rw [Int.le_floor] <;> exact h2
        simpa [hi_j] using h4
      have h4 : (j_of' x : ℤ) = j_of x := Int.toNat_of_nonneg h1
      have h5 : (hi_j.toNat : ℤ) = hi_j := Int.toNat_of_nonneg h_hi_j_nonneg
      omega
    have h_inj' : Set.InjOn (fun x : Point2 => (i_of' x, j_of' x)) (X : Set Point2) := by
      intro x hx y hy h_eq
      have h_i_eq' : i_of' x = i_of' y := congrArg Prod.fst h_eq
      have h_j_eq' : j_of' x = j_of' y := congrArg Prod.snd h_eq
      have h_i_eq : i_of x = i_of y := by
        have h1 : (i_of' x : ℤ) = (i_of' y : ℤ) := by exact_mod_cast h_i_eq'
        have h2 : (i_of' x : ℤ) = i_of x := by
          rw [Int.toNat_of_nonneg (h_i_range x hx).1]
        have h3 : (i_of' y : ℤ) = i_of y := by
          rw [Int.toNat_of_nonneg (h_i_range y hy).1]
        rw [h2, h3] at h1; exact h1
      have h_j_eq : j_of x = j_of y := by
        have h1 : (j_of' x : ℤ) = (j_of' y : ℤ) := by exact_mod_cast h_j_eq'
        have h2 : (j_of' x : ℤ) = j_of x := Int.toNat_of_nonneg (h_j_range x hx).1
        have h3 : (j_of' y : ℤ) = j_of y := Int.toNat_of_nonneg (h_j_range y hy).1
        rw [←h2, h1, h3]
      exact h_inj hx hy (Prod.ext h_i_eq h_j_eq)
    let img' : Finset (ℕ × ℕ) := X.image (fun x => (i_of' x, j_of' x))
    have h_img'_card : img'.card = X.card := by
      rw [Finset.card_image_of_injOn h_inj']
    have h_img'_subset : img' ⊆ Finset.product (Finset.range N1) (Finset.range N2) := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨x, hx, rfl⟩
      have h1 : i_of' x ∈ Finset.range N1 := by
        rw [Finset.mem_range]
        exact h_i'_range x hx
      have h2 : j_of' x ∈ Finset.range N2 := by
        rw [Finset.mem_range]
        exact h_j'_range x hx
      exact Finset.mem_product.mpr ⟨h1, h2⟩
    have h_prod_card : (Finset.product (Finset.range N1) (Finset.range N2)).card = N1 * N2 := by
      simp [Finset.card_product]
      <;> ring
    have h_card : img'.card ≤ N1 * N2 := by
      have h6 : img'.card ≤ (Finset.product (Finset.range N1) (Finset.range N2)).card :=
        Finset.card_le_card h_img'_subset
      rw [h_prod_card] at h6
      exact h6
    have hN1_le : (N1 : ℝ) ≤ 2 * R_u / s + 1 := by
      have h1 : (N1 : ℝ) = (hi_i.toNat : ℝ) + 1 := by simp [N1]
      rw [h1]
      have h2 : (hi_i.toNat : ℝ) = (hi_i : ℝ) := by
        have h3 : (hi_i.toNat : ℤ) = hi_i := Int.toNat_of_nonneg h_hi_i_nonneg
        exact_mod_cast h3
      rw [h2]
      have h3 : (hi_i : ℝ) ≤ 2 * R_u / s := Int.floor_le _
      linarith
    have hN2_le : (N2 : ℝ) ≤ 2 * R_v / s + 1 := by
      have h1 : (N2 : ℝ) = (hi_j.toNat : ℝ) + 1 := by simp [N2]
      rw [h1]
      have h2 : (hi_j.toNat : ℝ) = (hi_j : ℝ) := by
        have h3 : (hi_j.toNat : ℤ) = hi_j := Int.toNat_of_nonneg h_hi_j_nonneg
        exact_mod_cast h3
      rw [h2]
      have h3 : (hi_j : ℝ) ≤ 2 * R_v / s := Int.floor_le _
      linarith
    calc
      (X.card : ℝ) = (img'.card : ℝ) := by rw [h_img'_card]
      _ ≤ (N1 * N2 : ℝ) := by exact_mod_cast h_card
      _ ≤ (2 * R_u / s + 1) * (2 * R_v / s + 1) := by gcongr
  · have h_empty : X = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using hX
    rw [h_empty]
    have h1 : 0 ≤ 2 * R_u / s + 1 := by positivity
    have h2 : 0 ≤ 2 * R_v / s + 1 := by positivity
    simpa using mul_nonneg h1 h2

open scoped ENNReal

attribute [local instance] Classical.propDecidable

private theorem wz1_narrow_concentration_reduce_to
    {delta epsilon eta : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (parameters : WZ1Proposition8_9Parameters epsilon)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon < 1)
    (heta : 0 < eta) (hetaCap : eta ≤ epsilon / 20)
    (data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H)
    (hwidthQuarter : data.width ≤ 1 / 4)
    (hnarrow :
      data.width ≤ Real.rpow delta (1 - epsilon / 10))
    (hsmall :
      (1200000 : ℝ) *
          Real.rpow delta (7 * epsilon / 10) ≤ 1)
    (concentration :
      NarrowDotSpreadG1Concentrated
        delta epsilon data.width
        data.selectedF data.selectedG₁ data.selectedG₂
        data.refinedH data.direction)
    {Result : Prop}
    (hSpread :
      Nonempty
          (WZ1Proposition8_9NarrowDotSpreadData
            delta epsilon eta data.refinedH) →
        Result)
    (hObstruction :
      WZ1NarrowTripleConcentratedData
          parameters data concentration →
        Result) :
    Result := by

  let first := concentration.first
  let third := concentration.third
  let direction := data.direction
  let hdirection := data.direction_unit

  -- Pick second₀ ∈ concentration.points
  have hpoints_nonempty : concentration.points.Nonempty := by
    have h : (concentration.points.card : ENNReal) ≥ Kakeya.realRpowENN delta (epsilon - 1) :=
      calc
        Kakeya.realRpowENN delta (epsilon - 1) =
            1 * Kakeya.realRpowENN delta (epsilon - 1) := by
          simp
        _ ≤ 2 * Kakeya.realRpowENN delta (epsilon - 1) := by
          gcongr
          norm_num
        _ ≤ (concentration.points.card : ENNReal) :=
          concentration.card_lower
    have hpos : 0 < Kakeya.realRpowENN delta (epsilon - 1) := by
      simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hdelta]
    have hcard : 0 < concentration.points.card := by
      exact_mod_cast hpos.trans_le h
    exact Finset.card_pos.mp hcard
  rcases hpoints_nonempty with ⟨second₀, hsecond₀⟩
  have hsecond₀_in_G1 : second₀ ∈ data.selectedG₁ := concentration.subset hsecond₀
  have hedge₀ : (first, second₀, third) ∈ data.refinedH :=
    concentration.actual_edges second₀ hsecond₀

  -- Step 1: Third-fiber T over (first, second₀)
  let T : Finset Point2 := kaufmanThirdFiber data.refinedH first second₀
  have hT_nonempty : T.Nonempty := by
    refine ⟨third, ?_⟩
    simp only [T, kaufmanThirdFiber, Finset.mem_image, Finset.mem_filter]
    exact ⟨(first, second₀, third), ⟨hedge₀, by simp⟩, by simp⟩
  have hT_subset : T ⊆ data.selectedG₂ := by
    intro third' hthird'
    rcases Finset.mem_image.mp hthird' with ⟨edge, hedge, rfl⟩
    have hedgeH : edge ∈ data.refinedH := (Finset.mem_filter.mp hedge).1
    let enc := wz1TripleCoordinate edge
    have henc : enc ∈ wz1EncodeTriples data.refinedH :=
      Finset.mem_image.mpr ⟨edge, hedgeH, rfl⟩
    exact data.uniform.2.1 enc henc 2
  have hT_card : (T.card : ENNReal) ≥
      ((1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta) * data.selectedG₂.enncard :=
    uniform_density_third_fiber_bound data.uniform (first, second₀, third) hedge₀

  have hG2_card_lower : data.selectedG₂.enncard ≥
      Kakeya.realRpowENN delta (parameters.workingLambda - 1) :=
    frostman_workinglambda_lower_bound
      hdelta hdeltaOne parameters.workingLambda_pos
      (by linarith [parameters.workingLambda_le_epsilon, hepsilonOne])
      data.selectedG₂_separated data.selectedG₂_frostman
      data.selectedG₂_nonempty

  have hT_card_lower : (T.card : ℝ) ≥
      (1 / 256 : ℝ) * Real.rpow delta (eta + parameters.workingLambda - 1) := by
    exact
      narrow_dense_fiber_real_card_lower
        hdelta hG2_card_lower hT_card

  -- Step 2: Longitudinal pigeonhole T with radius L = delta / (8 * width)
  let L : ℝ := delta / (4 * data.width)
  have hwidth_nonneg : 0 ≤ data.width := data.width_pos.le
  have hL_pos : 0 < L := by
    dsimp only [L]
    exact div_pos hdelta (mul_pos (by norm_num) data.width_pos)
  have hL_le_half : L ≤ 1 / 2 := by
    dsimp only [L]
    have h2 : delta / (4 * data.width) ≤ data.width / (4 * data.width) := by
      gcongr
      exact data.delta_le_width
    have h3 : data.width / (4 * data.width) = 1 / 4 := by
      field_simp [data.width_pos.ne']
    rw [h3] at h2
    linarith
  let hball_T : ∀ b ∈ T, ‖b‖ ≤ 1 := by
    intro b hb
    have h : b ∈ data.selectedG₂ := hT_subset hb
    have h' : dist b 0 ≤ 1 := data.selectedG₂_ball b h
    simpa [dist_eq_norm] using h'
  rcases longitudinal_pigeonhole T (fun b : Point2 => b) hdirection hL_pos hball_T with
    ⟨longCenter, hlong⟩
  let T' : Finset Point2 := T.filter fun b =>
    |inner ℝ b direction - longCenter| ≤ L
  have hT'_subset : T' ⊆ T := Finset.filter_subset _ _
  have hT'_card : (T'.card : ℝ) ≥ (T.card : ℝ) * L / 3 := by
    have h1 : 2 + 2 * L ≤ 3 := by linarith [hL_le_half]
    calc (T'.card : ℝ)
        ≥ (T.card : ℝ) * L / (2 + 2 * L) := hlong
      _ ≥ (T.card : ℝ) * L / 3 := by gcongr
  have hT'_nonempty : T'.Nonempty := by
    have h_pos : 0 < (T.card : ℝ) * L / 3 := by positivity
    have h : 0 < (T'.card : ℝ) := h_pos.trans_le hT'_card
    exact Finset.card_pos.mp (by exact_mod_cast h)

  -- Step 3: Dot value range bound for T'
  have hdot_bound : ∀ third' ∈ T',
      -4 * data.width ≤ inner ℝ first (second₀ - third') ∧
      inner ℝ first (second₀ - third') ≤ 4 * data.width := by
    intro third' hthird'
    have hthird'_in_G2 : third' ∈ data.selectedG₂ := hT_subset (hT'_subset hthird')
    have hball_a : ‖first‖ ≤ 1 := by
      have h : dist first 0 ≤ 1 := data.selectedF_ball first concentration.first_mem
      simpa [dist_eq_norm] using h
    have hball1 : ‖second₀‖ ≤ 1 := by
      have h : dist second₀ 0 ≤ 1 := data.selectedG₁_ball second₀ hsecond₀_in_G1
      simpa [dist_eq_norm] using h
    have hball2 : ‖third'‖ ≤ 1 := by
      have h : dist third' 0 ≤ 1 := data.selectedG₂_ball third' hthird'_in_G2
      simpa [dist_eq_norm] using h
    have h1 : |inner ℝ first (second₀ - third')| ≤ 4 * data.width :=
      dot_value_range_bound
        (data.orthogonal_strip first concentration.first_mem)
        (data.first_strip second₀ hsecond₀_in_G1)
        (data.second_strip third' hthird'_in_G2)
        hball_a hball1 hball2 hdirection data.width_pos
    have h_abs : -4 * data.width ≤ inner ℝ first (second₀ - third') ∧
        inner ℝ first (second₀ - third') ≤ 4 * data.width := by
      have h4 := abs_le.mp h1
      exact ⟨by linarith, by linarith⟩
    exact h_abs

  -- Step 4: Dichotomy on dot values
  let K : ℝ := 16 * Real.rpow delta (epsilon - 1)
  have hK_pos : 0 < K := by
    dsimp only [K]
    have h1 : 0 < Real.rpow delta (epsilon - 1) := Real.rpow_pos_of_pos hdelta _
    exact mul_pos (by norm_num) h1
  let f : Point2 → ℝ := fun third' => inner ℝ first (second₀ - third')
  have h_dichotomy := point_separated_or_concentrated
      (α := Point2) (source := T') (value := f)
      (delta := delta) (lower := -4 * data.width) (upper := 4 * data.width) (K := K)
      hdelta (fun third' hthird' => hdot_bound third' hthird') hK_pos hT'_nonempty
  refine' Or.elim (Or.comm.mp h_dichotomy) _ _
  · intro h_spread
    -- Case 1: Spread dot values → dot spread data
    rcases h_spread with ⟨selected, hsel_subset, hsep, hcard⟩
    let values : Finset ℝ := selected.image f
    have h_inj : Set.InjOn f (selected : Set Point2) := by
      intro x hx y hy h_eq
      by_contra h_ne
      have h : 2 * delta < |f x - f y| := hsep x hx y hy h_ne
      rw [h_eq] at h
      have h10 : |f y - f y| = 0 := by simp
      rw [h10] at h
      linarith
    have h_values_card : values.card = selected.card := by
      rw [Finset.card_image_of_injOn h_inj]
    have h_values_dot : (values : Set ℝ) ⊆ wz1DotDifferenceSet data.refinedH := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨third', hthird', rfl⟩
      have hthird'_in_T : third' ∈ T := hT'_subset (hsel_subset hthird')
      have hedge : (first, second₀, third') ∈ data.refinedH :=
        kaufmanThirdFiber_actual_edge hthird'_in_T
      exact dot_value_mem hedge
    have h_lower_upper : values.Nonempty := by
      have h : selected.Nonempty := by
        have h_pos : 0 < (selected.card : ℝ) := by
          have h2 : 0 < (T'.card : ℝ) / (3 * K) := by positivity
          exact h2.trans_le hcard
        exact Finset.card_pos.mp (by exact_mod_cast h_pos)
      exact Finset.Nonempty.image h f
    let lower : ℝ := values.min' h_lower_upper
    let upper : ℝ := values.max' h_lower_upper
    have h_lower_mem : lower ∈ values := Finset.min'_mem _ _
    have h_upper_mem : upper ∈ values := Finset.max'_mem _ _
    have h_between : ∀ v ∈ values, lower ≤ v ∧ v ≤ upper := by
      intro v hv
      exact ⟨Finset.min'_le values v hv, Finset.le_max' values v hv⟩
    have h_range : upper - lower ≤ 8 * data.width := by
      rcases Finset.mem_image.mp h_lower_mem with ⟨lowerPoint, hlowerPoint, hlowerValue⟩
      rcases Finset.mem_image.mp h_upper_mem with ⟨upperPoint, hupperPoint, hupperValue⟩
      have h1 : lower ≥ -4 * data.width := by
        rw [← hlowerValue]
        exact (hdot_bound lowerPoint (hsel_subset hlowerPoint)).1
      have h2 : upper ≤ 4 * data.width := by
        rw [← hupperValue]
        exact (hdot_bound upperPoint (hsel_subset hupperPoint)).2
      linarith
    have h_sep2 : ∀ x ∈ values, ∀ y ∈ values, x ≠ y → 2 * delta < |x - y| := by
      intro x hx y hy hne
      rcases Finset.mem_image.mp hx with ⟨bx, hbx, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨by', hby, rfl⟩
      have hbx_ne : bx ≠ by' := by
        intro h
        apply hne
        rw [h]
      exact hsep bx hbx by' hby hbx_ne
    have h_card_lower : (values.card : ℝ) ≥
        Real.rpow delta (eta + parameters.workingLambda - 9 * epsilon / 10) / 147456 := by
      rw [h_values_card]
      have h1 : (selected.card : ℝ) ≥ (T'.card : ℝ) / (3 * K) := hcard
      have h2 : (T'.card : ℝ) ≥ (T.card : ℝ) * L / 3 := hT'_card
      have h3 : (T.card : ℝ) ≥
          (1 / 256 : ℝ) * Real.rpow delta (eta + parameters.workingLambda - 1) := hT_card_lower
      have h4 : (selected.card : ℝ) ≥
          ((1 / 256 : ℝ) * Real.rpow delta (eta + parameters.workingLambda - 1)) * L / 3 / (3 * K) := by
        calc (selected.card : ℝ)
            ≥ (T'.card : ℝ) / (3 * K) := h1
          _ ≥ ((T.card : ℝ) * L / 3) / (3 * K) := by gcongr
          _ ≥ ((1 / 256 : ℝ) * Real.rpow delta (eta + parameters.workingLambda - 1)) * L / 3 / (3 * K) := by gcongr
      dsimp only [K, L] at h4
      have h5 : ((1 / 256 : ℝ) * Real.rpow delta (eta + parameters.workingLambda - 1)) *
          (delta / (4 * data.width)) / 3 / (3 * (16 * Real.rpow delta (epsilon - 1))) ≥
          Real.rpow delta (eta + parameters.workingLambda - 9 * epsilon / 10) / 147456 := by
        have h6 : data.width ≤ Real.rpow delta (1 - epsilon / 10) := hnarrow
        have h7 : Real.rpow delta (eta + parameters.workingLambda - 1) * delta =
            Real.rpow delta (eta + parameters.workingLambda) := by
          calc
            Real.rpow delta (eta + parameters.workingLambda - 1) * delta =
                Real.rpow delta (eta + parameters.workingLambda - 1) * Real.rpow delta 1 := by simp
            _ = Real.rpow delta ((eta + parameters.workingLambda - 1) + 1) :=
              (Real.rpow_add hdelta _ _).symm
            _ = Real.rpow delta (eta + parameters.workingLambda) := by congr 1; ring
        calc ((1 / 256 : ℝ) * Real.rpow delta (eta + parameters.workingLambda - 1)) *
            (delta / (4 * data.width)) / 3 / (3 * (16 * Real.rpow delta (epsilon - 1)))
            = Real.rpow delta (eta + parameters.workingLambda) /
              (256 * 4 * data.width * 3 * 3 * 16 * Real.rpow delta (epsilon - 1)) := by
              rw [show
                (1 / 256 : ℝ) * Real.rpow delta (eta + parameters.workingLambda - 1) *
                    (delta / (4 * data.width)) =
                  (Real.rpow delta (eta + parameters.workingLambda - 1) * delta) / (256 * 4 * data.width) by ring]
              rw [h7]
              ring
          _ ≥ Real.rpow delta (eta + parameters.workingLambda) /
              (147456 * data.width * Real.rpow delta (epsilon - 1)) := by
              rw [show (256 : ℝ) * 4 * data.width * 3 * 3 * 16 * Real.rpow delta (epsilon - 1) =
                  147456 * data.width * Real.rpow delta (epsilon - 1) by ring]
          _ ≥ Real.rpow delta (eta + parameters.workingLambda) /
              (147456 * Real.rpow delta (1 - epsilon / 10) * Real.rpow delta (epsilon - 1)) := by
              exact div_le_div_of_nonneg_left
                (Real.rpow_nonneg hdelta.le _)
                (mul_pos (mul_pos (by norm_num) data.width_pos) (Real.rpow_pos_of_pos hdelta _))
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left h6 (by norm_num))
                  (Real.rpow_nonneg hdelta.le _))
          _ = Real.rpow delta (eta + parameters.workingLambda - 9 * epsilon / 10) / 147456 := by
              have h10 : Real.rpow delta (1 - epsilon / 10) * Real.rpow delta (epsilon - 1) =
                  Real.rpow delta (9 * epsilon / 10) := by
                calc
                  Real.rpow delta (1 - epsilon / 10) * Real.rpow delta (epsilon - 1) =
                      Real.rpow delta ((1 - epsilon / 10) + (epsilon - 1)) :=
                    (Real.rpow_add hdelta _ _).symm
                  _ = Real.rpow delta (9 * epsilon / 10) := by congr 1; ring
              rw [show 147456 * Real.rpow delta (1 - epsilon / 10) * Real.rpow delta (epsilon - 1) =
                  147456 * (Real.rpow delta (1 - epsilon / 10) * Real.rpow delta (epsilon - 1)) by ring, h10]
              have hsub := Real.rpow_sub hdelta (eta + parameters.workingLambda) (9 * epsilon / 10)
              calc
                Real.rpow delta (eta + parameters.workingLambda) /
                    (147456 * Real.rpow delta (9 * epsilon / 10)) =
                  (Real.rpow delta (eta + parameters.workingLambda) / Real.rpow delta (9 * epsilon / 10)) / 147456 := by ring
                _ = Real.rpow delta (eta + parameters.workingLambda - 9 * epsilon / 10) / 147456 :=
                  congrArg (fun value : ℝ => value / 147456) hsub.symm
      exact h5.trans h4
    let D : ℝ := upper - lower
    have hD_nonneg : 0 ≤ D := by exact sub_nonneg.mpr (h_between upper h_upper_mem).1
    have hD_le : D ≤ 8 * data.width := h_range
    have h_main_card := narrow_dot_spread_exponent_bound
        hdelta hdeltaOne hepsilon hepsilonOne heta
        parameters.workingLambda_le_epsilon hetaCap hnarrow hsmall
        (values.card : ℝ) h_card_lower D hD_nonneg hD_le
    have hbase :
        2 * max ((upper - lower) / 2) (Real.rpow delta (1 - eta) / 2) / delta =
          max D (Real.rpow delta (1 - eta)) / delta := by
      dsimp only [D]
      rw [show max ((upper - lower) / 2) (Real.rpow delta (1 - eta) / 2) =
          max (upper - lower) (Real.rpow delta (1 - eta)) / 2 by
        exact max_div_div_right (by norm_num) (upper - lower) (Real.rpow delta (1 - eta))]
      ring
    rw [← hbase] at h_main_card
    exact hSpread ⟨⟨values, lower, upper, h_lower_mem, h_upper_mem,
      h_sep2, h_values_dot, h_between,
      by simpa [ENNReal.ofReal_natCast] using h_main_card⟩⟩

  · intro h_conc
    -- Case 2: Concentrated dot values → G₂ transverse concentration
    rcases h_conc with ⟨t, ht_card⟩
    let C : Finset Point2 := T'.filter fun third' => |f third' - t| ≤ delta
    have hC_subset : C ⊆ T' := Finset.filter_subset _ _
    have hC_card : (C.card : ℝ) ≥ K := by exact_mod_cast ht_card
    have hC_nonempty : C.Nonempty := by
      have h_pos : 0 < K := hK_pos
      have h : 0 < (C.card : ℝ) := h_pos.trans_le hC_card
      exact Finset.card_pos.mp (by exact_mod_cast h)
    rcases hC_nonempty with ⟨third₀, hthird₀_in_C⟩
    let rawThirdAnchor := third₀
    have hthird₀_in_T' : third₀ ∈ T' := hC_subset hthird₀_in_C
    have hthird₀_in_T : third₀ ∈ T := hT'_subset hthird₀_in_T'
    have hthird₀_in_G2 : third₀ ∈ data.selectedG₂ := hT_subset hthird₀_in_T

    have ha0_perp : 3 / 7 ≤ |inner ℝ first (wz1Perp2 direction)| :=
      large_perp_component_three_sevenths hdirection
        (data.standardSeparation.2.2.2.2 first concentration.first_mem)
        (data.orthogonal_strip first concentration.first_mem) hwidthQuarter
    have h_a0_dir : |inner ℝ first direction| ≤ data.width := by
      have h2 : |inner ℝ (first - 0) (wz1Perp2 (wz1Perp2 direction))| ≤ data.width :=
        data.orthogonal_strip first concentration.first_mem
      have h3 : wz1Perp2 (wz1Perp2 direction) = -direction := by
        ext i
        fin_cases i <;> simp [wz1Perp2_coords]
      simpa [h3, inner_neg_right, abs_neg] using h2

    have h_transverse_bounds : ∀ third' ∈ C,
        |inner ℝ (third' - third₀) (wz1Perp2 direction)| ≤ 35 * delta / 6 := by
      intro third' hthird'
      have hthird'_in_T' : third' ∈ T' := hC_subset hthird'
      have h_dot1 : |f third' - t| ≤ delta := (Finset.mem_filter.mp hthird').2
      have h_dot2 : |f third₀ - t| ≤ delta := (Finset.mem_filter.mp hthird₀_in_C).2
      have h_dot_diff : |inner ℝ first (third' - third₀)| ≤ 2 * delta := by
        have h_eq : f third' - f third₀ = inner ℝ first (third₀ - third') := by
          dsimp only [f]
          have h : inner ℝ first (second₀ - third') - inner ℝ first (second₀ - third₀) =
              inner ℝ first ((second₀ - third') - (second₀ - third₀)) := by
            rw [← inner_sub_right]
          rw [h]
          have h3 : (second₀ - third') - (second₀ - third₀) = third₀ - third' := by
            ext i
            fin_cases i <;> simp
          rw [h3]
        have h_abs : |f third' - f third₀| ≤ |f third' - t| + |f third₀ - t| := by
          have h9 : f third' - f third₀ = (f third' - t) - (f third₀ - t) := by ring
          rw [h9]
          exact abs_sub _ _
        have h10 : |inner ℝ first (third' - third₀)| = |inner ℝ first (third₀ - third')| := by
          have h11 : inner ℝ first (third' - third₀) = -inner ℝ first (third₀ - third') := by
            rw [← inner_neg_right]
            <;> simp
          rw [h11, abs_neg]
        rw [h10, ← h_eq]
        linarith [h_dot1, h_dot2]
      have h_long1 : |inner ℝ (third' - third₀) direction| ≤ 2 * L := by
        have h1 : |inner ℝ third' direction - longCenter| ≤ L :=
          (Finset.mem_filter.mp hthird'_in_T').2
        have h2 : |inner ℝ third₀ direction - longCenter| ≤ L :=
          (Finset.mem_filter.mp hthird₀_in_T').2
        have h3 : inner ℝ (third' - third₀) direction =
            inner ℝ third' direction - inner ℝ third₀ direction := by
          simp [inner_sub_left]
        rw [h3]
        have h4 : |inner ℝ third' direction - inner ℝ third₀ direction| ≤
            |inner ℝ third' direction - longCenter| + |inner ℝ third₀ direction - longCenter| := by
          have h5 : inner ℝ third' direction - inner ℝ third₀ direction =
              (inner ℝ third' direction - longCenter) - (inner ℝ third₀ direction - longCenter) := by ring
          rw [h5]
          exact abs_sub _ _
        linarith [h1, h2]
      set v := third' - third₀ with hv
      set c_dir := inner ℝ v direction with hc_dir
      set c_perp := inner ℝ v (wz1Perp2 direction) with hc_perp
      have hdecomp : v = c_dir • direction + c_perp • wz1Perp2 direction :=
        orthonormal_decomp v direction hdirection
      have hinner : inner ℝ first v =
          (inner ℝ first direction) * c_dir +
          (inner ℝ first (wz1Perp2 direction)) * c_perp := by
        rw [hdecomp, inner_add_right, inner_smul_right, inner_smul_right]
        <;> ring
      have h_x_bound : |(inner ℝ first direction) * c_dir| ≤ delta / 2 := by
        have h_abs : |(inner ℝ first direction) * c_dir| =
            |inner ℝ first direction| * |c_dir| := by rw [abs_mul]
        rw [h_abs]
        have h_le : |inner ℝ first direction| * |c_dir| ≤ data.width * (2 * L) := by gcongr
        have h_eq : data.width * (2 * L) = delta / 2 := by
          dsimp only [L]
          field_simp [data.width_pos.ne']
          <;> ring
        rw [h_eq] at h_le
        exact h_le
      have h_main : |(inner ℝ first (wz1Perp2 direction)) * c_perp| ≤ 5 * delta / 2 := by
        have h_eq : (inner ℝ first (wz1Perp2 direction)) * c_perp =
            inner ℝ first v - (inner ℝ first direction) * c_dir := by
          rw [hinner] <;> ring
        rw [h_eq]
        have h_tri : |inner ℝ first v - (inner ℝ first direction) * c_dir| ≤
            |inner ℝ first v| + |(inner ℝ first direction) * c_dir| := abs_sub _ _
        linarith [h_dot_diff, h_x_bound]
      have h5 : |inner ℝ first (wz1Perp2 direction)| * |c_perp| ≤ 5 * delta / 2 := by
        have h6 : |(inner ℝ first (wz1Perp2 direction)) * c_perp| =
            |inner ℝ first (wz1Perp2 direction)| * |c_perp| := by rw [abs_mul]
        rw [← h6]
        exact h_main
      have h7 : 3 / 7 ≤ |inner ℝ first (wz1Perp2 direction)| := ha0_perp
      have h7_pos : 0 < |inner ℝ first (wz1Perp2 direction)| := by linarith
      have h8 : |c_perp| ≤ 35 * delta / 6 := by
        calc |c_perp|
            = (|inner ℝ first (wz1Perp2 direction)| * |c_perp|) /
              |inner ℝ first (wz1Perp2 direction)| := by
              field_simp [h7_pos.ne']
          _ ≤ (5 * delta / 2) / (3 / 7 : ℝ) := by gcongr
          _ = 35 * delta / 6 := by ring
      simpa [hc_perp] using h8
    have hC_card_threshold : (C.card : ℝ) ≥ 16 * Real.rpow delta (epsilon - 1) := by
      simpa [K] using hC_card
    rcases transverse_eight_cell_pigeonhole
        (anchor := third₀)
        hdelta hdirection hC_card_threshold
        (by
          intro point hpoint
          have h := h_transverse_bounds point hpoint
          linarith) with
      ⟨G2conc, hG2conc_subset, hG2conc_card, base2, h_strip2⟩
    have hG2conc_card2 : (G2conc.card : ENNReal) ≥
        2 * Kakeya.realRpowENN delta (epsilon - 1) := by
      rw [Kakeya.realRpowENN, ← ENNReal.ofReal_natCast]
      have hnonnegative :
          0 ≤ Real.rpow delta (epsilon - 1) :=
        Real.rpow_nonneg hdelta.le _
      rw [show
        (2 : ENNReal) *
            ENNReal.ofReal (Real.rpow delta (epsilon - 1)) =
          ENNReal.ofReal
            (2 * Real.rpow delta (epsilon - 1)) by
        rw [← ENNReal.ofReal_ofNat 2,
          ENNReal.ofReal_mul (by norm_num)]]
      exact ENNReal.ofReal_le_ofReal hG2conc_card
    have hG2conc_subset_G2 : G2conc ⊆ data.selectedG₂ := by
      intro b hb
      have hb_in_C : b ∈ C := hG2conc_subset hb
      have hb_in_T' : b ∈ T' := hC_subset hb_in_C
      have hb_in_T : b ∈ T := hT'_subset hb_in_T'
      exact hT_subset hb_in_T
    have hG2conc_actual :
        ∀ third' ∈ G2conc, (first, second₀, third') ∈ data.refinedH := by
      intro third' hthird'
      have hthird'_in_C : third' ∈ C := hG2conc_subset hthird'
      have hthird'_in_T' : third' ∈ T' := hC_subset hthird'_in_C
      have hthird'_in_T : third' ∈ T := hT'_subset hthird'_in_T'
      exact kaufmanThirdFiber_actual_edge hthird'_in_T

    -- Now we have G1conc and G2conc in transverse delta-strips
    let t1 : ℝ := inner ℝ concentration.base (wz1Perp2 direction)
    let t2 : ℝ := inner ℝ base2 (wz1Perp2 direction)

    -- Define first-fiber
    let kaufmanFirstFiber (H : Finset (Point2 × Point2 × Point2))
        (second third : Point2) : Finset Point2 :=
      (H.filter fun edge => edge.2.1 = second ∧ edge.2.2 = third).image
        fun edge => edge.1

    have h_first_fiber_bound : ∀ (edge : Point2 × Point2 × Point2),
        edge ∈ data.refinedH →
        ((kaufmanFirstFiber data.refinedH edge.2.1 edge.2.2).card : ENNReal) ≥
          ((1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta) * data.selectedF.enncard := by
      intro edge hedge
      let encoded : Fin 3 → Point2 := wz1TripleCoordinate edge
      have hencoded : encoded ∈ wz1EncodeTriples data.refinedH :=
        Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
      let fixed : Finset (Fin 3) := {1, 2}
      have hfiber := data.uniform.2.2 encoded hencoded fixed
      have hcomplement : (Finset.univ : Finset (Fin 3)) \ fixed = {0} := by decide
      have hproduct : wz1VertexCardProduct (wz1TripleVertexClasses data.selectedF data.selectedG₁ data.selectedG₂) ({0} : Finset (Fin 3)) = data.selectedF.enncard := by
        simp [wz1VertexCardProduct, wz1TripleVertexClasses] <;> rfl
      rw [hcomplement, hproduct] at hfiber
      let hypergraphFiber := wz1HypergraphFiber (wz1EncodeTriples data.refinedH) fixed encoded
      let projectFirst : (Fin 3 → Point2) → Point2 := fun current => current 0
      have hmaps : ∀ current ∈ hypergraphFiber, projectFirst current ∈ kaufmanFirstFiber data.refinedH edge.2.1 edge.2.2 := by
        intro current hcurrent
        have hgraph : current ∈ wz1EncodeTriples data.refinedH := (Finset.mem_filter.mp hcurrent).1
        have hfixed : ∀ index ∈ fixed, current index = encoded index := (Finset.mem_filter.mp hcurrent).2
        rcases Finset.mem_image.mp hgraph with ⟨source, hsource, rfl⟩
        have hsecond : source.2.1 = edge.2.1 := hfixed 1 (by simp [fixed])
        have hthird : source.2.2 = edge.2.2 := hfixed 2 (by simp [fixed])
        exact Finset.mem_image.mpr ⟨source, Finset.mem_filter.mpr ⟨hsource, hsecond, hthird⟩, rfl⟩
      have hinj : Set.InjOn projectFirst (hypergraphFiber : Set (Fin 3 → Point2)) := by
        intro first1 hfirst1 second1 hsecond1 heq
        have hfirst1_fixed : ∀ index ∈ fixed, first1 index = encoded index := (Finset.mem_filter.mp hfirst1).2
        have hsecond1_fixed : ∀ index ∈ fixed, second1 index = encoded index := (Finset.mem_filter.mp hsecond1).2
        funext index
        fin_cases index
        · exact heq
        · have h1 : first1 1 = encoded 1 := hfirst1_fixed 1 (by simp [fixed])
          have h2 : second1 1 = encoded 1 := hsecond1_fixed 1 (by simp [fixed])
          exact h1.trans h2.symm
        · have h1 : first1 2 = encoded 2 := hfirst1_fixed 2 (by simp [fixed])
          have h2 : second1 2 = encoded 2 := hsecond1_fixed 2 (by simp [fixed])
          exact h1.trans h2.symm
      have hcard : hypergraphFiber.card ≤ (kaufmanFirstFiber data.refinedH edge.2.1 edge.2.2).card := by
        rw [← Finset.card_image_of_injOn hinj]
        exact Finset.card_le_card (Finset.image_subset_iff.mpr hmaps)
      exact hfiber.trans (by exact_mod_cast hcard)

    -- Pick third₀ ∈ G2conc
    have hG2card := hG2conc_card2
    have hG2conc_nonempty : G2conc.Nonempty := by
      have hpos : 0 < Kakeya.realRpowENN delta (epsilon - 1) := by
        simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hdelta]
      have hcardPositive :
          0 < (G2conc.card : ENNReal) := by
        have hdouble :
            0 <
              2 * Kakeya.realRpowENN delta (epsilon - 1) := by
          positivity
        exact hdouble.trans_le hG2card
      have h : 0 < G2conc.card := by
        exact_mod_cast hcardPositive
      exact Finset.card_pos.mp h
    rcases hG2conc_nonempty with ⟨third₀, hthird₀⟩
    have hedge_new : (first, second₀, third₀) ∈ data.refinedH :=
      hG2conc_actual third₀ hthird₀

    -- First-fiber over (second₀, third₀)
    let F' : Finset Point2 := kaufmanFirstFiber data.refinedH second₀ third₀
    have hF'_subset : F' ⊆ data.selectedF := by
      intro f hf
      rcases Finset.mem_image.mp hf with ⟨edge, hedge, rfl⟩
      have hedgeH : edge ∈ data.refinedH := (Finset.mem_filter.mp hedge).1
      let enc := wz1TripleCoordinate edge
      have henc : enc ∈ wz1EncodeTriples data.refinedH := Finset.mem_image.mpr ⟨edge, hedgeH, rfl⟩
      exact data.uniform.2.1 enc henc 0
    have hF'_card : (F'.card : ENNReal) ≥
        ((1 / 256 : ENNReal) * Kakeya.realRpowENN delta eta) * data.selectedF.enncard :=
      h_first_fiber_bound (first, second₀, third₀) hedge_new

    have hF_card_lower : data.selectedF.enncard ≥
        Kakeya.realRpowENN delta (parameters.workingLambda - 1) :=
      frostman_workinglambda_lower_bound
        hdelta hdeltaOne parameters.workingLambda_pos
        (by linarith [parameters.workingLambda_le_epsilon, hepsilonOne])
        data.selectedF_separated data.selectedF_frostman
        data.selectedF_nonempty

    have hF'_card_lower : (F'.card : ℝ) ≥
        (1 / 256 : ℝ) * Real.rpow delta (eta + parameters.workingLambda - 1) := by
      exact
        narrow_dense_fiber_real_card_lower
          hdelta hF_card_lower hF'_card

    have hF'_nonempty : F'.Nonempty := by
      have h_pos : 0 < (F'.card : ℝ) := by
        have h : 0 < (1 / 256 : ℝ) * Real.rpow delta (eta + parameters.workingLambda - 1) :=
          mul_pos (by norm_num) (Real.rpow_pos_of_pos hdelta _)
        exact h.trans_le hF'_card_lower
      exact Finset.card_pos.mp (by exact_mod_cast h_pos)

    -- Dot value range for F'
    have hdot_bound_F : ∀ f' ∈ F',
        -4 * data.width ≤ inner ℝ f' (second₀ - third₀) ∧
        inner ℝ f' (second₀ - third₀) ≤ 4 * data.width := by
      intro f' hf'
      have hf'_in_F : f' ∈ data.selectedF := hF'_subset hf'
      have hball_a : ‖f'‖ ≤ 1 := by
        have h : dist f' 0 ≤ 1 := data.selectedF_ball f' hf'_in_F
        simpa [dist_eq_norm] using h
      have hball1 : ‖second₀‖ ≤ 1 := by
        have h : dist second₀ 0 ≤ 1 := data.selectedG₁_ball second₀ hsecond₀_in_G1
        simpa [dist_eq_norm] using h
      have hball2 : ‖third₀‖ ≤ 1 := by
        have h : dist third₀ 0 ≤ 1 := data.selectedG₂_ball third₀ (hG2conc_subset_G2 hthird₀)
        simpa [dist_eq_norm] using h
      have h1 : |inner ℝ f' (second₀ - third₀)| ≤ 4 * data.width :=
        dot_value_range_bound
          (data.orthogonal_strip f' hf'_in_F)
          (data.first_strip second₀ hsecond₀_in_G1)
          (data.second_strip third₀ (hG2conc_subset_G2 hthird₀))
          hball_a hball1 hball2 hdirection data.width_pos
      have h4 := abs_le.mp h1
      exact ⟨by linarith, by linarith⟩

    -- Apply dichotomy to F' dot values
    let K_F : ℝ := 192 * Real.rpow delta (9 * epsilon / 10 - 1)
    have hK_F_pos : 0 < K_F := by
      dsimp only [K_F]
      have h1 : 0 < Real.rpow delta (9 * epsilon / 10 - 1) := Real.rpow_pos_of_pos hdelta _
      exact mul_pos (by norm_num) h1
    let g : Point2 → ℝ := fun f' => inner ℝ f' (second₀ - third₀)
    have h_F_dichotomy := point_separated_or_concentrated
        (source := F') (value := g)
        (lower := -4 * data.width) (upper := 4 * data.width) (K := K_F)
        hdelta (fun f' hf' => hdot_bound_F f' hf') hK_F_pos hF'_nonempty
    refine' Or.elim (Or.comm.mp h_F_dichotomy) _ _
    · intro hF_spread
      -- Case F-spread: first-fiber dot values spread → dot spread data
      rcases hF_spread with ⟨selectedF', hselF_subset, hsepF, hcardF⟩
      let valuesF : Finset ℝ := selectedF'.image g
      have h_injF : Set.InjOn g (selectedF' : Set Point2) := by
        intro x hx y hy h_eq
        by_contra h_ne
        have h : 2 * delta < |g x - g y| := hsepF x hx y hy h_ne
        rw [h_eq] at h
        have h10 : |g y - g y| = 0 := by simp
        rw [h10] at h
        linarith
      have h_valuesF_card : valuesF.card = selectedF'.card := by
        rw [Finset.card_image_of_injOn h_injF]
      have h_valuesF_dot : (valuesF : Set ℝ) ⊆ wz1DotDifferenceSet data.refinedH := by
        intro v hv
        rcases Finset.mem_image.mp hv with ⟨f', hf', rfl⟩
        have hf'_in_F' : f' ∈ F' := hselF_subset hf'
        rcases Finset.mem_image.mp hf'_in_F' with ⟨edge, hedge, rfl⟩
        have hedgeH : edge ∈ data.refinedH := (Finset.mem_filter.mp hedge).1
        have hsecond : edge.2.1 = second₀ := (Finset.mem_filter.mp hedge).2.1
        have hthird : edge.2.2 = third₀ := (Finset.mem_filter.mp hedge).2.2
        simpa [hsecond, hthird] using dot_value_mem hedgeH
      have h_lower_upperF : valuesF.Nonempty := by
        have h : selectedF'.Nonempty := by
          have h_pos : 0 < (selectedF'.card : ℝ) := by
            have h2 : 0 < (F'.card : ℝ) / (3 * K_F) := by positivity
            exact h2.trans_le hcardF
          exact Finset.card_pos.mp (by exact_mod_cast h_pos)
        exact Finset.Nonempty.image h g
      let lowerF : ℝ := valuesF.min' h_lower_upperF
      let upperF : ℝ := valuesF.max' h_lower_upperF
      have h_lowerF_mem : lowerF ∈ valuesF := Finset.min'_mem _ _
      have h_upperF_mem : upperF ∈ valuesF := Finset.max'_mem _ _
      have h_betweenF : ∀ v ∈ valuesF, lowerF ≤ v ∧ v ≤ upperF := by
        intro v hv
        exact ⟨Finset.min'_le valuesF v hv, Finset.le_max' valuesF v hv⟩
      have h_rangeF : upperF - lowerF ≤ 8 * data.width := by
        rcases Finset.mem_image.mp h_lowerF_mem with ⟨lp, hlp, hlv⟩
        rcases Finset.mem_image.mp h_upperF_mem with ⟨up, hup, huv⟩
        have h1 : lowerF ≥ -4 * data.width := by
          rw [← hlv]
          exact (hdot_bound_F lp (hselF_subset hlp)).1
        have h2 : upperF ≤ 4 * data.width := by
          rw [← huv]
          exact (hdot_bound_F up (hselF_subset hup)).2
        linarith
      have h_sepF2 : ∀ x ∈ valuesF, ∀ y ∈ valuesF, x ≠ y → 2 * delta < |x - y| := by
        intro x hx y hy hne
        rcases Finset.mem_image.mp hx with ⟨bx, hbx, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨by', hby, rfl⟩
        have hbx_ne : bx ≠ by' := by
          intro h
          apply hne
          rw [h]
        exact hsepF bx hbx by' hby hbx_ne
      have h_cardF_lower : (valuesF.card : ℝ) ≥
          Real.rpow delta (eta + parameters.workingLambda - 9 * epsilon / 10) / 147456 := by
        rw [h_valuesF_card]
        have h1 : (selectedF'.card : ℝ) ≥ (F'.card : ℝ) / (3 * K_F) := hcardF
        have h2 : (F'.card : ℝ) ≥
            (1 / 256 : ℝ) * Real.rpow delta (eta + parameters.workingLambda - 1) := hF'_card_lower
        have h4 : (selectedF'.card : ℝ) ≥
            ((1 / 256 : ℝ) * Real.rpow delta (eta + parameters.workingLambda - 1)) / (3 * K_F) := by
          calc (selectedF'.card : ℝ)
              ≥ (F'.card : ℝ) / (3 * K_F) := h1
            _ ≥ ((1 / 256 : ℝ) * Real.rpow delta (eta + parameters.workingLambda - 1)) / (3 * K_F) := by gcongr
        dsimp only [K_F] at h4
        have h5 : ((1 / 256 : ℝ) * Real.rpow delta (eta + parameters.workingLambda - 1)) /
            (3 * (192 * Real.rpow delta (9 * epsilon / 10 - 1))) =
            Real.rpow delta (eta + parameters.workingLambda - 9 * epsilon / 10) / 147456 := by
          have h6 : Real.rpow delta (eta + parameters.workingLambda - 1) /
              Real.rpow delta (9 * epsilon / 10 - 1) =
              Real.rpow delta (eta + parameters.workingLambda - 9 * epsilon / 10) := by
            have h61 := Real.rpow_sub hdelta (eta + parameters.workingLambda - 1) (9 * epsilon / 10 - 1)
            have h62 : (eta + parameters.workingLambda - 1) - (9 * epsilon / 10 - 1) =
                eta + parameters.workingLambda - 9 * epsilon / 10 := by ring
            rw [h62] at h61
            exact h61.symm
          calc
            ((1 / 256 : ℝ) * Real.rpow delta (eta + parameters.workingLambda - 1)) /
                (3 * (192 * Real.rpow delta (9 * epsilon / 10 - 1)))
                = (Real.rpow delta (eta + parameters.workingLambda - 1) /
                    Real.rpow delta (9 * epsilon / 10 - 1)) / (256 * 3 * 192) := by ring
            _ = Real.rpow delta (eta + parameters.workingLambda - 9 * epsilon / 10) / 147456 := by
              rw [h6]
              <;> norm_num
        rw [h5] at h4
        exact h4
      let D_F : ℝ := upperF - lowerF
      have hD_F_nonneg : 0 ≤ D_F := by exact sub_nonneg.mpr (h_betweenF upperF h_upperF_mem).1
      have hD_F_le : D_F ≤ 8 * data.width := h_rangeF
      have h_main_cardF := narrow_dot_spread_exponent_bound
          hdelta hdeltaOne hepsilon hepsilonOne heta
          parameters.workingLambda_le_epsilon hetaCap hnarrow hsmall
          (valuesF.card : ℝ) h_cardF_lower D_F hD_F_nonneg hD_F_le
      have hbaseF :
          2 * max ((upperF - lowerF) / 2) (Real.rpow delta (1 - eta) / 2) / delta =
            max D_F (Real.rpow delta (1 - eta)) / delta := by
        dsimp only [D_F]
        rw [show max ((upperF - lowerF) / 2) (Real.rpow delta (1 - eta) / 2) =
            max (upperF - lowerF) (Real.rpow delta (1 - eta)) / 2 by
          exact max_div_div_right (by norm_num) (upperF - lowerF) (Real.rpow delta (1 - eta))]
        ring
      rw [← hbaseF] at h_main_cardF
      exact hSpread ⟨⟨valuesF, lowerF, upperF, h_lowerF_mem, h_upperF_mem,
        h_sepF2, h_valuesF_dot, h_betweenF,
        by simpa [ENNReal.ofReal_natCast] using h_main_cardF⟩⟩

    · intro hF_conc
      -- Case F-concentrated: first-fiber dot values concentrate
      rcases hF_conc with ⟨tF, htF_card⟩
      let CF : Finset Point2 := F'.filter fun f' => |g f' - tF| ≤ delta
      have hCF_subset : CF ⊆ F' := Finset.filter_subset _ _
      have hCF_card : (CF.card : ℝ) ≥ K_F := by exact_mod_cast htF_card
      have hCF_nonempty : CF.Nonempty := by
        have h_pos : 0 < K_F := hK_F_pos
        have h : 0 < (CF.card : ℝ) := h_pos.trans_le hCF_card
        exact Finset.card_pos.mp (by exact_mod_cast h)

      -- Case F-concentrated: grid packing contradiction when v transverse to direction
      let v : Point2 := second₀ - third₀
      have hthird₀_in_G2' : third₀ ∈ data.selectedG₂ := hG2conc_subset_G2 hthird₀
      have hv_norm_lower : (1 / 2 : ℝ) ≤ ‖v‖ := by
        have h : 1 / 2 ≤ dist second₀ third₀ :=
          data.standardSeparation.2.2.2.1 second₀ hsecond₀_in_G1 third₀ hthird₀_in_G2'
        simpa [dist_eq_norm] using h
      have hv_pos : 0 < ‖v‖ := by linarith
      let u : Point2 := (1 / ‖v‖) • v
      have hu_norm : ‖u‖ = 1 := by
        simp [u, norm_smul, hv_pos.ne'] <;> field_simp [hv_pos.ne'] <;> linarith
      have h_strip_u : ∀ f' ∈ CF, |inner ℝ f' u - tF / ‖v‖| ≤ delta / ‖v‖ := by
        intro f' hf'
        have h1 : |g f' - tF| ≤ delta := (Finset.mem_filter.mp hf').2
        have h2 : g f' = inner ℝ f' v := by rfl
        rw [h2] at h1
        have h3 : inner ℝ f' u = inner ℝ f' v / ‖v‖ := by
          simp [u, inner_smul_right] <;> ring
        have h4 : |inner ℝ f' u - tF / ‖v‖| = |inner ℝ f' v - tF| / ‖v‖ := by
          rw [h3]
          have h5 : |(inner ℝ f' v) / ‖v‖ - tF / ‖v‖| = |inner ℝ f' v - tF| / ‖v‖ := by
            have h6 : (inner ℝ f' v) / ‖v‖ - tF / ‖v‖ = (inner ℝ f' v - tF) / ‖v‖ := by ring
            rw [h6, abs_div, abs_of_nonneg (show 0 ≤ ‖v‖ from by linarith)]
          exact h5
        rw [h4]
        exact div_le_div_of_nonneg_right h1 (by linarith)
      have h_strip_dir : ∀ f' ∈ CF, |inner ℝ f' direction| ≤ data.width := by
        intro f' hf'
        have hf'_in_F' : f' ∈ F' := hCF_subset hf'
        rcases Finset.mem_image.mp hf'_in_F' with ⟨edge, hedge, rfl⟩
        have hedgeH : edge ∈ data.refinedH := (Finset.mem_filter.mp hedge).1
        have hfirst : edge.1 ∈ data.selectedF := data.uniform.2.1 (wz1TripleCoordinate edge)
          (Finset.mem_image.mpr ⟨edge, hedgeH, rfl⟩) 0
        have hstrip : edge.1 ∈ wz1LineNeighborhood 0 (wz1Perp2 direction) data.width :=
          data.orthogonal_strip edge.1 hfirst
        have h_perp2 : wz1Perp2 (wz1Perp2 direction) = -direction := by
          ext i
          fin_cases i <;> simp [wz1Perp2_coords] <;> ring
        simpa [wz1LineNeighborhood, h_perp2, inner_neg_right, abs_neg] using hstrip
      have hCF_in_selectedF : ∀ x ∈ CF, x ∈ data.selectedF := by
        intro x hx
        have h1 : x ∈ F' := hCF_subset hx
        rcases Finset.mem_image.mp h1 with ⟨edge, hedge, rfl⟩
        have hedgeH : edge ∈ data.refinedH := (Finset.mem_filter.mp hedge).1
        exact data.uniform.2.1 (wz1TripleCoordinate edge)
          (Finset.mem_image.mpr ⟨edge, hedgeH, rfl⟩) 0
      have hCF_sep : ∀ x ∈ CF, ∀ y ∈ CF, x ≠ y → delta ≤ dist x y := by
        intro x hx y hy hne
        exact data.selectedF_separated (hCF_in_selectedF x hx) (hCF_in_selectedF y hy) hne
      by_cases h_angle : |inner ℝ u direction| ≤ 1 / Real.sqrt 2
      · -- Transverse case: grid packing contradiction
        have h_dual_norm : ∀ (d : Point2), ‖d‖ ≤ 2 * (|inner ℝ d u| + |inner ℝ d direction|) :=
          dual_norm_bound u direction hu_norm hdirection h_angle
        let s : ℝ := 2 * delta / 9
        have hs_pos : 0 < s := by positivity
        have h_small : 4 * s < delta := by
          dsimp only [s]
          linarith
        have h_pack : (CF.card : ℝ) ≤ (2 * (delta / ‖v‖) / s + 1) * (2 * data.width / s + 1) :=
          have hR_u_nonneg : 0 ≤ delta / ‖v‖ := by positivity
          have hR_v_nonneg : 0 ≤ data.width := by linarith [data.delta_le_width]
          grid_packing_bound CF delta s hdelta hs_pos u direction h_dual_norm hCF_sep
            (tF / ‖v‖) (delta / ‖v‖) data.width
            hR_u_nonneg hR_v_nonneg
            h_strip_u h_strip_dir h_small
        have h_bound1 : 2 * (delta / ‖v‖) / s + 1 ≤ 19 := by
          dsimp only [s]
          have h_inv : 1 / ‖v‖ ≤ 2 := by
            have h_pos : 0 < ‖v‖ := hv_pos
            have h_half : (1 / 2 : ℝ) ≤ ‖v‖ := hv_norm_lower
            calc 1 / ‖v‖ ≤ 1 / (1 / 2 : ℝ) := by gcongr
              _ = 2 := by norm_num
          have h_eq : 2 * (delta / ‖v‖) / (2 * delta / 9) = 9 / ‖v‖ := by
            field_simp [hdelta.ne', hv_pos.ne'] <;> ring
          rw [h_eq]
          have h : 9 / ‖v‖ + 1 ≤ 19 := by
            have h2 : 9 / ‖v‖ ≤ 18 := by
              calc 9 / ‖v‖ = 9 * (1 / ‖v‖) := by ring
                _ ≤ 9 * 2 := by gcongr
                _ = 18 := by norm_num
            linarith
          exact h
        have h_bound2 : 2 * data.width / s + 1 ≤ 10 * data.width / delta := by
          dsimp only [s]
          have h_eq : 2 * data.width / (2 * delta / 9) = 9 * data.width / delta := by
            field_simp [hdelta.ne'] <;> ring
          rw [h_eq]
          have h_width_ratio : 1 ≤ data.width / delta := by
            have h1 : delta ≤ data.width := data.delta_le_width
            have h2 : 0 < delta := hdelta
            calc
              1 = delta / delta := by field_simp [h2.ne'] <;> ring
              _ ≤ data.width / delta := by gcongr
          calc
            9 * data.width / delta + 1 ≤ 9 * data.width / delta + data.width / delta := by
              have h : 1 ≤ data.width / delta := h_width_ratio
              linarith
            _ = 10 * data.width / delta := by ring
        have h3 : (CF.card : ℝ) ≤ 190 * data.width / delta := by
          calc
            (CF.card : ℝ) ≤ (2 * (delta / ‖v‖) / s + 1) * (2 * data.width / s + 1) := h_pack
            _ ≤ 19 * (2 * data.width / s + 1) := by gcongr <;> exact h_bound1
            _ ≤ 19 * (10 * data.width / delta) := by gcongr <;> exact h_bound2
            _ = 190 * data.width / delta := by ring
        have h4 : 190 * data.width / delta < K_F := by
          have h7 : Real.rpow delta (1 - epsilon / 10) / delta = Real.rpow delta (-epsilon / 10) := by
            have h8 : Real.rpow delta ((1 - epsilon / 10) - (1 : ℝ)) =
                Real.rpow delta (1 - epsilon / 10) / Real.rpow delta (1 : ℝ) :=
              Real.rpow_sub hdelta (1 - epsilon / 10) (1 : ℝ)
            have h9 : Real.rpow delta (1 : ℝ) = delta := by simp
            have h10 : (1 - epsilon / 10) - (1 : ℝ) = -epsilon / 10 := by ring
            rw [h10] at h8
            rw [h9] at h8
            exact h8.symm
          have h5 : data.width ≤ Real.rpow delta (1 - epsilon / 10) := hnarrow
          have h51 : data.width / delta ≤ Real.rpow delta (1 - epsilon / 10) / delta := by gcongr
          have h52 : data.width / delta ≤ Real.rpow delta (-epsilon / 10) := by
            calc
              data.width / delta ≤ Real.rpow delta (1 - epsilon / 10) / delta := h51
              _ = Real.rpow delta (-epsilon / 10) := h7
          have h6 : 190 * data.width / delta ≤ 190 * Real.rpow delta (-epsilon / 10) := by
            have h_eq : 190 * data.width / delta = 190 * (data.width / delta) := by ring
            rw [h_eq]
            gcongr
          have h10 : 190 * Real.rpow delta (-epsilon / 10) <
              (192 : ℝ) * Real.rpow delta (9 * epsilon / 10 - 1) := by
            have h11 : Real.rpow delta (1 - epsilon) < (96 : ℝ) / 95 := by
              have h12 : 0 < 1 - epsilon := by linarith
              have h13 : Real.rpow delta (1 - epsilon) ≤ 1 := Real.rpow_le_one hdelta.le hdeltaOne (by linarith)
              have h14 : (1 : ℝ) < (96 : ℝ) / 95 := by norm_num
              linarith
            have h15 : Real.rpow delta (-epsilon / 10) / Real.rpow delta (9 * epsilon / 10 - 1) =
                Real.rpow delta (1 - epsilon) := by
              have h16 : Real.rpow delta (-epsilon / 10) / Real.rpow delta (9 * epsilon / 10 - 1) =
                  Real.rpow delta ((-epsilon / 10) - (9 * epsilon / 10 - 1)) :=
                (Real.rpow_sub hdelta (-epsilon / 10) (9 * epsilon / 10 - 1)).symm
              have h17 : (-epsilon / 10) - (9 * epsilon / 10 - 1) = 1 - epsilon := by ring
              rw [h16, h17] <;> rfl
            have h18 : Real.rpow delta (-epsilon / 10) =
                Real.rpow delta (1 - epsilon) * Real.rpow delta (9 * epsilon / 10 - 1) := by
              have h_pos : 0 < Real.rpow delta (9 * epsilon / 10 - 1) := Real.rpow_pos_of_pos hdelta _
              exact (div_eq_iff h_pos.ne').mp h15
            rw [h18]
            have h19 : 0 < Real.rpow delta (9 * epsilon / 10 - 1) := Real.rpow_pos_of_pos hdelta _
            have h20 : 190 * Real.rpow delta (1 - epsilon) < 192 := by
              have h21 : Real.rpow delta (1 - epsilon) < (96 : ℝ) / 95 := h11
              linarith
            have h_goal : 190 * (Real.rpow delta (1 - epsilon) * Real.rpow delta (9 * epsilon / 10 - 1)) <
                (192 : ℝ) * Real.rpow delta (9 * epsilon / 10 - 1) := by
              have h23 : 190 * (Real.rpow delta (1 - epsilon) * Real.rpow delta (9 * epsilon / 10 - 1)) =
                  (190 * Real.rpow delta (1 - epsilon)) * Real.rpow delta (9 * epsilon / 10 - 1) := by ring
              rw [h23]
              exact mul_lt_mul_of_pos_right h20 h19
            exact h_goal
          dsimp only [K_F] at *
          <;> linarith
        linarith [h3, h4, hCF_card]
      · -- Non-transverse case: Alternative A (v nearly parallel to direction)
        have hfirstPoints_actual :
            ∀ f' ∈ CF,
              (f', second₀, third₀) ∈ data.refinedH := by
          intro f' hf'
          have hf'_in_F' : f' ∈ F' := hCF_subset hf'
          rcases Finset.mem_image.mp hf'_in_F' with
            ⟨edge, hedge, hedgeFirst⟩
          have hedgeH : edge ∈ data.refinedH :=
            (Finset.mem_filter.mp hedge).1
          have hedgeSecond : edge.2.1 = second₀ :=
            (Finset.mem_filter.mp hedge).2.1
          have hedgeThird : edge.2.2 = third₀ :=
            (Finset.mem_filter.mp hedge).2.2
          have hedgeEq :
              edge = (f', second₀, third₀) := by
            exact Prod.ext hedgeFirst
              (Prod.ext hedgeSecond hedgeThird)
          rw [← hedgeEq]
          exact hedgeH
        let obstruction :
            WZ1NarrowTripleConcentratedData
              parameters data concentration :=
          {
            second := second₀
            second_mem := hsecond₀
            thirdPoints := G2conc
            thirdPoints_subset := hG2conc_subset_G2
            thirdPoints_card := hG2conc_card2
            thirdBase := base2
            thirdPoints_strip := h_strip2
            thirdLongitudinalCenter := longCenter
            thirdPoints_longitudinal := by
              intro third' hthird'
              have hthird'_in_C : third' ∈ C :=
                hG2conc_subset hthird'
              have hthird'_in_T' : third' ∈ T' :=
                hC_subset hthird'_in_C
              exact (Finset.mem_filter.mp hthird'_in_T').2
            thirdDotCenter := t
            thirdPoints_dot_concentrated := by
              intro third' hthird'
              have hthird'_in_C : third' ∈ C :=
                hG2conc_subset hthird'
              exact (Finset.mem_filter.mp hthird'_in_C).2
            thirdPoints_actual := hG2conc_actual
            rawThirdMargin := {
              points := C
              selected_subset := hG2conc_subset
              subset := by
                intro third' hthird'
                exact hT_subset (hT'_subset (hC_subset hthird'))
              card_lower := by
                simpa [K] using hC_card
              transverseAnchor := rawThirdAnchor
              transverse := by
                intro third' hthird'
                simpa [rawThirdAnchor] using
                  h_transverse_bounds third' hthird'
              longitudinal := by
                intro third' hthird'
                have hthird'T' := hC_subset hthird'
                simpa [L] using (Finset.mem_filter.mp hthird'T').2
              actual_mem := by
                intro third' hthird'
                exact
                  kaufmanThirdFiber_actual_edge
                    (hT'_subset (hC_subset hthird'))
              dot_concentrated := by
                intro third' hthird'
                exact (Finset.mem_filter.mp hthird').2
            }
            third := third₀
            third_mem := hthird₀
            firstPoints := CF
            firstPoints_subset := hCF_in_selectedF
            firstPoints_card := hCF_card
            firstPoints_actual := hfirstPoints_actual
            firstDotCenter := tF
            firstPoints_dot_concentrated := by
              intro f' hf'
              exact (Finset.mem_filter.mp hf').2
            endpointDirection := u
            endpointDirection_eq := rfl
            endpointDirection_unit := hu_norm
            nontransverse := by
              exact lt_of_not_ge h_angle
          }
        exact hObstruction obstruction

/-- The closed fiber reductions expose either actual dot-spread evidence or
the full triple-concentrated obstruction package. -/
theorem wz1_narrow_triple_concentrated_production :
    WZ1NarrowTripleConcentratedProductionStatement := by
  intro delta epsilon eta F G₁ G₂ H parameters
    hdelta hdeltaOne hepsilon hepsilonOne heta hetaCap
    data hwidthQuarter hnarrow hsmall concentration
  apply
    wz1_narrow_concentration_reduce_to
      parameters hdelta hdeltaOne hepsilon hepsilonOne
      heta hetaCap data hwidthQuarter hnarrow hsmall concentration
  · exact Or.inl
  · intro obstruction
    exact Or.inr ⟨obstruction⟩

theorem wz1_narrow_concentration_reduction :
    WZ1NarrowConcentrationReductionStatement := by
  intro hResolve
  intro delta epsilon eta F G₁ G₂ H parameters
    hdelta hdeltaOne hepsilon hepsilonOne heta hetaCap
    data hwidthQuarter hnarrow hsmall concentration
  apply
    wz1_narrow_concentration_reduce_to
      parameters hdelta hdeltaOne hepsilon hepsilonOne
      heta hetaCap data hwidthQuarter hnarrow hsmall concentration
  · exact Or.inr
  · intro obstruction
    exact
      hResolve parameters hdelta hdeltaOne hepsilon hepsilonOne
        heta hetaCap data hwidthQuarter hnarrow hsmall
        concentration obstruction

end Kakeya.Assouad
