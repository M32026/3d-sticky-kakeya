module

/-
# Four-Sector Signed Permutation Chart Helpers

After BSG, raw scalar projection is U + x*V. Partition into four sectors.
Each sector uses only swapping and sign changes (preserving Cartesian products).

Repository convention: affine projection is t*a + b.

Sector 1 (0≤x≤1): S(U,V)=(V,U), t=x
Sector 2 (x≥1):    S(U,V)=(U,V), t=1/x
Sector 3 (-1≤x≤0): S(U,V)=(-V,U), t=-x
Sector 4 (x≤-1):   S(U,V)=(-U,V), t=-1/x
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.CubeIndexSet
public import MyLeanRepo.CoveringNumberScaling
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

namespace ProductLikeIncidence.FourSectorChart

open Set

abbrev e : (Fin 2 → ℝ) ≃ EuclideanSpace ℝ (Fin 2) :=
  (WithLp.equiv 2 _).symm

/-! ========================================================================
   Sector maps (signed coordinate permutations)
   ======================================================================== -/

def sec1Fn (f : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then f 1 else f 0

def sec3Fn (f : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then -(f 1) else f 0

def sec4Fn (f : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then -(f 0) else f 1

/-- sec3 inverse: sec3_inv(a,b)=(b,-a). -/
def sec3InvFn (f : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then f 1 else -(f 0)

def sec1 (p : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  e (sec1Fn ((WithLp.equiv 2 _) p))

def sec2 (p : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) := p

def sec3 (p : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  e (sec3Fn ((WithLp.equiv 2 _) p))

def sec4 (p : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  e (sec4Fn ((WithLp.equiv 2 _) p))

def sec3Inv (p : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  e (sec3InvFn ((WithLp.equiv 2 _) p))

/-! ========================================================================
   Coefficient identities: t*a + b relates to U + x*V
   ======================================================================== -/

lemma sector1_identity (U V x : ℝ) : x * V + U = U + x * V := by ring

lemma sector2_identity (U V x : ℝ) (hx : x ≠ 0) :
    (1 / x) * U + V = (1 / x) * (U + x * V) := by
  field_simp [hx]

lemma sector3_identity (U V x : ℝ) : (-x) * (-V) + U = U + x * V := by ring

lemma sector4_identity (U V x : ℝ) (hx : x ≠ 0) :
    (-1 / x) * (-U) + V = (1 / x) * (U + x * V) := by
  field_simp [hx]

/-! ========================================================================
   t ∈ [0,1] in each sector
   ======================================================================== -/

lemma sector1_t_in_Icc (x : ℝ) (h : 0 ≤ x ∧ x ≤ 1) : x ∈ Icc (0 : ℝ) 1 := h

lemma sector2_t_in_Icc (x : ℝ) (h : x ≥ 1) : 1 / x ∈ Icc (0 : ℝ) 1 := by
  have hpos : 0 < x := by linarith
  exact ⟨by positivity, by rw [div_le_one (by linarith)] <;> linarith⟩

lemma sector3_t_in_Icc (x : ℝ) (h : -1 ≤ x ∧ x ≤ 0) : -x ∈ Icc (0 : ℝ) 1 :=
  ⟨by linarith, by linarith⟩

lemma sector4_t_in_Icc (x : ℝ) (h : x ≤ -1) : -1 / x ∈ Icc (0 : ℝ) 1 := by
  have hneg : x < 0 := by linarith
  set y : ℝ := -x with hy_def
  have hy1 : y ≥ 1 := by linarith
  have h_eq : -1 / x = 1 / y := by
    field_simp [hneg.ne, hy_def] <;> ring
  rw [h_eq]
  have hpos : 0 < y := by linarith
  exact ⟨by positivity, by rw [div_le_one (by linarith)] <;> linarith⟩

/-! ========================================================================
   sec3 inverse: sec3Inv ∘ sec3 = id and sec3 ∘ sec3Inv = id
   ======================================================================== -/

lemma sec3_left_inv : ∀ p, sec3Inv (sec3 p) = p := by
  intro p
  apply (WithLp.equiv 2 _).injective
  ext i; fin_cases i <;> simp [sec3, sec3Inv, e, sec3Fn, sec3InvFn] <;> ring

lemma sec3_right_inv : ∀ p, sec3 (sec3Inv p) = p := by
  intro p
  apply (WithLp.equiv 2 _).injective
  ext i; fin_cases i <;> simp [sec3, sec3Inv, e, sec3Fn, sec3InvFn] <;> ring

lemma sec1_invol : ∀ p, sec1 (sec1 p) = p := by
  intro p
  apply (WithLp.equiv 2 _).injective
  ext i; fin_cases i <;> simp [sec1, e, sec1Fn] <;> tauto

lemma sec4_invol : ∀ p, sec4 (sec4 p) = p := by
  intro p
  apply (WithLp.equiv 2 _).injective
  ext i; fin_cases i <;> simp [sec4, e, sec4Fn] <;> ring

/-! ========================================================================
   Isometries via norm preservation
   ======================================================================== -/

lemma sec1Fn_sqsum (f : Fin 2 → ℝ) :
    (sec1Fn f 0)^2 + (sec1Fn f 1)^2 = (f 0)^2 + (f 1)^2 := by
  simp [sec1Fn] <;> ring

lemma sec3Fn_sqsum (f : Fin 2 → ℝ) :
    (sec3Fn f 0)^2 + (sec3Fn f 1)^2 = (f 0)^2 + (f 1)^2 := by
  simp [sec3Fn] <;> ring

lemma sec4Fn_sqsum (f : Fin 2 → ℝ) :
    (sec4Fn f 0)^2 + (sec4Fn f 1)^2 = (f 0)^2 + (f 1)^2 := by
  simp [sec4Fn] <;> ring

lemma sec1_sub (x y : EuclideanSpace ℝ (Fin 2)) :
    sec1 x - sec1 y = sec1 (x - y) := by
  ext i
  fin_cases i <;> simp [sec1, e, sec1Fn, WithLp.equiv_symm_apply] <;> ring

lemma sec3_sub (x y : EuclideanSpace ℝ (Fin 2)) :
    sec3 x - sec3 y = sec3 (x - y) := by
  ext i
  fin_cases i <;> simp [sec3, e, sec3Fn, WithLp.equiv_symm_apply] <;> ring

lemma sec4_sub (x y : EuclideanSpace ℝ (Fin 2)) :
    sec4 x - sec4 y = sec4 (x - y) := by
  ext i
  fin_cases i <;> simp [sec4, e, sec4Fn, WithLp.equiv_symm_apply] <;> ring

lemma isometry_of_sqsum (secMap : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hsub : ∀ x y, secMap x - secMap y = secMap (x - y))
    (hsq : ∀ (z : EuclideanSpace ℝ (Fin 2)),
      (secMap z 0)^2 + (secMap z 1)^2 = (z 0)^2 + (z 1)^2) :
    Isometry secMap := by
  apply Isometry.of_dist_eq
  intro x y
  have h_dist : dist (secMap x) (secMap y) = ‖secMap x - secMap y‖ := by
    rw [dist_eq_norm]
  rw [h_dist, hsub x y]
  have h1 : ‖secMap (x - y)‖ ^ 2 = ‖x - y‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    have hsum : ∀ (w : EuclideanSpace ℝ (Fin 2)),
        (∑ i : Fin 2, (w i)^2) = (w 0)^2 + (w 1)^2 := by
      intro w; simp [Fin.sum_univ_two]
    rw [hsum (secMap (x - y)), hsum (x - y)]
    exact hsq (x - y)
  have h2 : 0 ≤ ‖secMap (x - y)‖ := by positivity
  have h3 : 0 ≤ ‖x - y‖ := by positivity
  have h4 : ‖secMap (x - y)‖ = ‖x - y‖ := by nlinarith
  simpa [dist_eq_norm] using h4

lemma sec1_sqsum (z : EuclideanSpace ℝ (Fin 2)) :
    (sec1 z 0)^2 + (sec1 z 1)^2 = (z 0)^2 + (z 1)^2 := by
  simp [sec1, e, sec1Fn, WithLp.equiv_symm_apply] <;> ring

lemma sec3_sqsum (z : EuclideanSpace ℝ (Fin 2)) :
    (sec3 z 0)^2 + (sec3 z 1)^2 = (z 0)^2 + (z 1)^2 := by
  simp [sec3, e, sec3Fn, WithLp.equiv_symm_apply] <;> ring

lemma sec4_sqsum (z : EuclideanSpace ℝ (Fin 2)) :
    (sec4 z 0)^2 + (sec4 z 1)^2 = (z 0)^2 + (z 1)^2 := by
  simp [sec4, e, sec4Fn, WithLp.equiv_symm_apply] <;> ring

lemma sec1_isometry : Isometry sec1 :=
  isometry_of_sqsum sec1 sec1_sub sec1_sqsum

lemma sec2_isometry : Isometry sec2 := isometry_id

lemma sec3_isometry : Isometry sec3 :=
  isometry_of_sqsum sec3 sec3_sub sec3_sqsum

lemma sec4_isometry : Isometry sec4 :=
  isometry_of_sqsum sec4 sec4_sub sec4_sqsum

/-! ========================================================================
   Product preservation
   ======================================================================== -/

lemma sec1_product (B1 B2 : Set ℝ) :
    sec1 '' {p : EuclideanSpace ℝ (Fin 2) | p 0 ∈ B1 ∧ p 1 ∈ B2} =
    {p | p 0 ∈ B2 ∧ p 1 ∈ B1} := by
  ext p
  simp only [mem_image, mem_setOf_eq]
  constructor
  · rintro ⟨q, hq, rfl⟩
    have h1 : (sec1 q) 0 = q 1 := by simp [sec1, e, sec1Fn]
    have h2 : (sec1 q) 1 = q 0 := by simp [sec1, e, sec1Fn]
    exact ⟨by rw [h1]; exact hq.2, by rw [h2]; exact hq.1⟩
  · rintro ⟨h0, h1⟩
    refine' ⟨sec1 p, _, sec1_invol p⟩
    have h3 : (sec1 p) 0 = p 1 := by simp [sec1, e, sec1Fn]
    have h4 : (sec1 p) 1 = p 0 := by simp [sec1, e, sec1Fn]
    exact ⟨by rw [h3]; exact h1, by rw [h4]; exact h0⟩

lemma sec3_product (B1 B2 : Set ℝ) :
    sec3 '' {p : EuclideanSpace ℝ (Fin 2) | p 0 ∈ B1 ∧ p 1 ∈ B2} =
    {p | p 0 ∈ (fun x => -x) '' B2 ∧ p 1 ∈ B1} := by
  ext p
  simp only [mem_image, mem_setOf_eq]
  constructor
  · rintro ⟨q, hq, rfl⟩
    have h1 : (sec3 q) 0 = -(q 1) := by simp [sec3, e, sec3Fn]
    have h2 : (sec3 q) 1 = q 0 := by simp [sec3, e, sec3Fn]
    exact ⟨⟨q 1, hq.2, by rw [h1]⟩, by rw [h2]; exact hq.1⟩
  · rintro ⟨hleft, h1⟩
    rcases hleft with ⟨y, hy, hpy⟩
    let q : EuclideanSpace ℝ (Fin 2) := e ![p 1, y]
    have hq0 : q 0 = p 1 := by simp [q, e] <;> rfl
    have hq1 : q 1 = y := by simp [q, e] <;> rfl
    have hq : q 0 ∈ B1 ∧ q 1 ∈ B2 := by
      constructor
      · rw [hq0]; exact h1
      · rw [hq1]; exact hy
    have h_eq : sec3 q = p := by
      ext i; fin_cases i <;> simp [sec3, e, sec3Fn, q] <;> linarith
    exact ⟨q, hq, h_eq⟩

lemma sec4_product (B1 B2 : Set ℝ) :
    sec4 '' {p : EuclideanSpace ℝ (Fin 2) | p 0 ∈ B1 ∧ p 1 ∈ B2} =
    {p | p 0 ∈ (fun x => -x) '' B1 ∧ p 1 ∈ B2} := by
  ext p
  simp only [mem_image, mem_setOf_eq]
  constructor
  · rintro ⟨q, hq, rfl⟩
    have h1 : (sec4 q) 0 = -(q 0) := by simp [sec4, e, sec4Fn]
    have h2 : (sec4 q) 1 = q 1 := by simp [sec4, e, sec4Fn]
    exact ⟨⟨q 0, hq.1, by rw [h1]⟩, by rw [h2]; exact hq.2⟩
  · rintro ⟨hleft, h2⟩
    rcases hleft with ⟨y, hy, hpy⟩
    let q : EuclideanSpace ℝ (Fin 2) := e ![y, p 1]
    have hq0 : q 0 = y := by simp [q, e] <;> rfl
    have hq1 : q 1 = p 1 := by simp [q, e] <;> rfl
    have hq : q 0 ∈ B1 ∧ q 1 ∈ B2 := by
      constructor
      · rw [hq0]; exact hy
      · rw [hq1]; exact h2
    have h_eq : sec4 q = p := by
      ext i; fin_cases i <;> simp [sec4, e, sec4Fn, q] <;> linarith
    exact ⟨q, hq, h_eq⟩

/-! ========================================================================
   Difference sets under sign changes
   ======================================================================== -/

lemma neg_set_diff (A : Set ℝ) :
    image2 (· - ·) ((fun x => -x) '' A) ((fun x => -x) '' A) =
    (fun x => -x) '' (image2 (· - ·) A A) := by
  ext z
  simp only [mem_image2, mem_image]
  constructor
  · rintro ⟨a, ⟨x, hx, rfl⟩, b, ⟨y, hy, rfl⟩, rfl⟩
    refine' ⟨x - y, ⟨x, hx, y, hy, rfl⟩, by ring⟩
  · rintro ⟨w, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    refine' ⟨-x, ⟨x, hx, rfl⟩, -y, ⟨y, hy, rfl⟩, by ring⟩

lemma neg_set_sum (A B : Set ℝ) :
    image2 (· + ·) ((fun x => -x) '' A) ((fun x => -x) '' B) =
    (fun x => -x) '' (image2 (· + ·) A B) := by
  ext z
  simp only [mem_image2, mem_image]
  constructor
  · rintro ⟨a, ⟨x, hx, rfl⟩, b, ⟨y, hy, rfl⟩, rfl⟩
    refine' ⟨x + y, ⟨x, hx, y, hy, rfl⟩, by ring⟩
  · rintro ⟨w, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    refine' ⟨-x, ⟨x, hx, rfl⟩, -y, ⟨y, hy, rfl⟩, by ring⟩

/-! ========================================================================
   Lipschitz and co-Lipschitz bounds for t(x)
   ======================================================================== -/

/-- Sector 1: t(x)=x is an isometry on ℝ. -/
lemma sector1_lipschitz (x y : ℝ) :
    |x - y| ≤ |x - y| ∧ |x - y| ≤ |x - y| := by
  exact ⟨by rfl, by rfl⟩

/-- Sector 2: t(x)=1/x on [1,M]. -/
lemma sector2_lipschitz {M : ℝ} (hM : 0 ≤ M) {x y : ℝ}
    (hx1 : 1 ≤ x) (hy1 : 1 ≤ y) (hxM : x ≤ M) (hyM : y ≤ M) :
    |1 / x - 1 / y| ≤ |x - y| ∧ |x - y| ≤ M ^ 2 * |1 / x - 1 / y| := by
  have hx_pos : 0 < x := by linarith
  have hy_pos : 0 < y := by linarith
  have h_eq : 1 / x - 1 / y = (y - x) / (x * y) := by
    field_simp [hx_pos.ne', hy_pos.ne'] <;> ring
  have h_abs : |1 / x - 1 / y| = |x - y| / (x * y) := by
    rw [h_eq]
    have h : |(y - x) / (x * y)| = |x - y| / (x * y) := by
      rw [abs_div, abs_sub_comm]
      <;> rw [abs_of_pos (mul_pos hx_pos hy_pos)]
    exact h
  constructor
  · rw [h_abs]
    have h_denom : 1 ≤ x * y := by nlinarith
    have h : 1 / (x * y) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      <;> nlinarith
    calc
      |x - y| / (x * y) = |x - y| * (1 / (x * y)) := by ring
      _ ≤ |x - y| * 1 := by gcongr
      _ = |x - y| := by ring
  · rw [h_abs]
    have h : x * y ≤ M ^ 2 := by nlinarith
    calc
      |x - y| = |x - y| * (x * y) / (x * y) := by
        field_simp [hx_pos.ne', hy_pos.ne'] <;> ring
      _ ≤ |x - y| * M ^ 2 / (x * y) := by
        gcongr
        <;> nlinarith
      _ = M ^ 2 * (|x - y| / (x * y)) := by ring

/-- Sector 3: t(x)=-x is an isometry on ℝ. -/
lemma sector3_lipschitz (x y : ℝ) :
    |(-x) - (-y)| ≤ |x - y| ∧ |x - y| ≤ |(-x) - (-y)| := by
  have h : |(-x) - (-y)| = |x - y| := by
    have h2 : (-x) - (-y) = -(x - y) := by ring
    rw [h2, abs_neg]
  exact ⟨by rw [h], by rw [h]⟩

/-- Sector 4: t(x)=-1/x on [-M,-1]. -/
lemma sector4_lipschitz {M : ℝ} (hM : 0 ≤ M) {x y : ℝ}
    (hx1 : x ≤ -1) (hy1 : y ≤ -1) (hxM : -M ≤ x) (hyM : -M ≤ y) :
    |(-1 / x) - (-1 / y)| ≤ |x - y| ∧ |x - y| ≤ M ^ 2 * |(-1 / x) - (-1 / y)| := by
  have hx_neg : x < 0 := by linarith
  have hy_neg : y < 0 := by linarith
  set a : ℝ := -x with ha_def
  set b : ℝ := -y with hb_def
  have ha1 : 1 ≤ a := by linarith
  have hb1 : 1 ≤ b := by linarith
  have haM : a ≤ M := by linarith
  have hbM : b ≤ M := by linarith
  have h_t : (-1 / x) - (-1 / y) = 1 / a - 1 / b := by
    simp [ha_def, hb_def] <;> field_simp [hx_neg.ne, hy_neg.ne] <;> ring
  have h_xy : |x - y| = |a - b| := by
    have h : x - y = -(a - b) := by simp [ha_def, hb_def] <;> ring
    rw [h, abs_neg]
  rw [h_t, h_xy]
  exact sector2_lipschitz hM ha1 hb1 haM hbM

/-! ========================================================================
   Covering number: coordinate swap preserves Nplane exactly
   ======================================================================== -/

def swapK (k : Fin 2 → ℤ) : Fin 2 → ℤ :=
  fun i => if i = 0 then k 1 else k 0

lemma swapK_invol : ∀ k, swapK (swapK k) = k := by
  intro k; ext i; fin_cases i <;> simp [swapK] <;> tauto

lemma sec1_map_cube {δ : ℝ} {k : Fin 2 → ℤ} :
    sec1 '' dyadicCube δ k = dyadicCube δ (swapK k) := by
  ext p
  simp only [mem_image, dyadicCube, mem_setOf_eq]
  constructor
  · rintro ⟨q, hq, rfl⟩
    intro i
    fin_cases i <;> simp [sec1, e, sec1Fn, swapK] at * <;> tauto
  · intro hp
    refine' ⟨sec1 p, _, sec1_invol p⟩
    intro i
    fin_cases i <;> simp [sec1, e, sec1Fn, swapK] at * <;> tauto

lemma swap_preserves_Nplane {δ : ℝ} {P : Set (EuclideanSpace ℝ (Fin 2))} :
    Nplane δ (sec1 '' P) = Nplane δ P := by
  let F : Set (EuclideanSpace ℝ (Fin 2)) → Set (EuclideanSpace ℝ (Fin 2)) :=
    fun Q => sec1 '' Q
  have h_sec1_inj : Function.Injective sec1 := by
    intro a b h
    have h2 : sec1 (sec1 a) = sec1 (sec1 b) := by rw [h]
    rw [sec1_invol a, sec1_invol b] at h2
    exact h2
  have hF_inj : Function.Injective F := by
    intro Q1 Q2 h
    have h3 : sec1 '' Q1 = sec1 '' Q2 := h
    have h4 : Q1 = Q2 := by
      calc
        Q1 = sec1 '' (sec1 '' Q1) := by ext z; simp [sec1_invol] <;> tauto
        _ = sec1 '' (sec1 '' Q2) := by rw [h3]
        _ = Q2 := by ext z; simp [sec1_invol] <;> tauto
    exact h4
  have h_cube_map : ∀ (k : Fin 2 → ℤ),
      F (dyadicCube δ k) = dyadicCube δ (swapK k) := by
    intro k; exact sec1_map_cube
  have h_F_cube : ∀ Q, Q ∈ dyadicCubes (d := 2) δ → F Q ∈ dyadicCubes (d := 2) δ := by
    intro Q hQ
    rcases hQ with ⟨k, rfl⟩
    rw [h_cube_map k]
    exact ⟨swapK k, rfl⟩
  have h_F_invol_cube : ∀ Q, Q ∈ dyadicCubes (d := 2) δ → F (F Q) = Q := by
    intro Q hQ
    rcases hQ with ⟨k, rfl⟩
    have h1 : F (dyadicCube δ k) = dyadicCube δ (swapK k) := h_cube_map k
    rw [h1]
    have h2 : F (dyadicCube δ (swapK k)) = dyadicCube δ (swapK (swapK k)) := h_cube_map (swapK k)
    rw [h2, swapK_invol k]
  have h_meet : ∀ Q, Q ∈ dyadicCubes (d := 2) δ →
      ((Q ∩ P).Nonempty ↔ (F Q ∩ sec1 '' P).Nonempty) := by
    intro Q hQ
    constructor
    · rintro ⟨p, hpQ, hpP⟩
      exact ⟨sec1 p, ⟨p, hpQ, rfl⟩, ⟨p, hpP, rfl⟩⟩
    · rintro ⟨q, hqQ, hqP⟩
      rcases hqQ with ⟨p, hpQ, rfl⟩
      rcases hqP with ⟨p', hpP, h_eq⟩
      have h_p'_eq_p : p' = p := by
        have h : sec1 p' = sec1 p := h_eq
        calc p' = sec1 (sec1 p') := (sec1_invol p').symm
           _ = sec1 (sec1 p) := by rw [h]
           _ = p := sec1_invol p
      rw [h_p'_eq_p] at hpP
      exact ⟨p, hpQ, hpP⟩
  let S1 := dyadicCubesMeeting δ P
  let S2 := dyadicCubesMeeting δ (sec1 '' P)
  have h_mapsTo : F '' S1 ⊆ S2 := by
    intro Q hQ
    rcases hQ with ⟨Q0, hQ0, rfl⟩
    have hQ_cube : Q0 ∈ dyadicCubes (d := 2) δ := hQ0.1
    have hQ_meet : (Q0 ∩ P).Nonempty := hQ0.2
    have h_F_cube' : F Q0 ∈ dyadicCubes (d := 2) δ := h_F_cube Q0 hQ_cube
    have h_F_meet : (F Q0 ∩ sec1 '' P).Nonempty := (h_meet Q0 hQ_cube).mp hQ_meet
    exact ⟨h_F_cube', h_F_meet⟩
  have h_surjTo : S2 ⊆ F '' S1 := by
    intro Q hQ
    have hQ_cube : Q ∈ dyadicCubes (d := 2) δ := hQ.1
    have hQ_meet : (Q ∩ sec1 '' P).Nonempty := hQ.2
    let Q' := F Q
    have hQ'_cube : Q' ∈ dyadicCubes (d := 2) δ := h_F_cube Q hQ_cube
    have h_FQ' : F Q' = Q := h_F_invol_cube Q hQ_cube
    have hQ'_meet : (Q' ∩ P).Nonempty := by
      have h : (F Q' ∩ sec1 '' P).Nonempty := by
        rw [h_FQ']; exact hQ_meet
      exact (h_meet Q' hQ'_cube).mpr h
    exact ⟨Q', ⟨hQ'_cube, hQ'_meet⟩, h_FQ'⟩
  have h_image : F '' S1 = S2 := Set.Subset.antisymm h_mapsTo h_surjTo
  have h_encard : S2.encard = S1.encard := by
    rw [←h_image]
    exact hF_inj.encard_image S1
  simpa [Nplane, dyadicCoveringNumber] using h_encard

/-! ========================================================================
   Covering number: 1D negation preserves Nreal for δ-grid sets

   For sets on the δ-grid, negation maps cube index n to -n exactly,
   so the covering number is preserved.
   ======================================================================== -/

lemma neg_set_Nreal {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ}
    (hA_bdd : Bornology.IsBounded A)
    (hA : A ⊆ productLikeIntegerGrid δ) :
    Nreal δ ((fun x => -x) '' A) = Nreal δ A := by
  let negA := (fun x : ℝ => -x) '' A
  have hnegA_grid : negA ⊆ productLikeIntegerGrid δ := by
    rintro y ⟨x, hx, rfl⟩
    rcases hA hx with ⟨n, rfl⟩
    refine' ⟨-n, _⟩
    have h : -(δ * (n : ℝ)) = δ * ((-n : ℤ) : ℝ) := by
      simp [mul_comm] <;> ring
    exact h
  have hnegA_bdd : Bornology.IsBounded negA := by
    have h_lip : LipschitzWith 1 (fun x : ℝ => -x) := by
      intro x y
      simp [dist_eq_norm]
      <;> exact le_refl _
    have h_tmp : Bornology.IsBounded ((fun x : ℝ => -x) '' A) :=
      h_lip.isBounded_image hA_bdd
    convert h_tmp
    <;> simp [negA]
  have h_grid_idx : ∀ (S : Set ℝ), S ⊆ productLikeIntegerGrid δ →
      bourgain_projection_theorem.realCubeIndexSet δ S = {n : ℤ | δ * (n : ℝ) ∈ S} := by
    intro S hS_grid
    ext j
    simp only [bourgain_projection_theorem.realCubeIndexSet, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hxIco, hxS⟩
      have hx_grid : x ∈ productLikeIntegerGrid δ := hS_grid hxS
      rcases hx_grid with ⟨m, rfl⟩
      have h3 : δ * (j : ℝ) ≤ δ * (m : ℝ) := hxIco.1
      have h4 : δ * (m : ℝ) < δ * ((j : ℝ) + 1) := hxIco.2
      have h5 : (j : ℝ) ≤ (m : ℝ) := by nlinarith
      have h6 : (m : ℝ) < (j : ℝ) + 1 := by nlinarith
      have h_j_eq : j = m := by
        have h7 : j ≤ m := by exact_mod_cast h5
        have h8 : m < j + 1 := by exact_mod_cast h6
        omega
      rw [h_j_eq] at *
      exact hxS
    · intro h
      refine' ⟨δ * (j : ℝ), _ , h⟩
      constructor <;> simp [hδ]
  have h_idx_A : bourgain_projection_theorem.realCubeIndexSet δ A =
      {n : ℤ | δ * (n : ℝ) ∈ A} := h_grid_idx A hA
  have h_idx_neg : bourgain_projection_theorem.realCubeIndexSet δ negA =
      {n : ℤ | δ * (n : ℝ) ∈ negA} := h_grid_idx negA hnegA_grid
  have h_set_eq : {n : ℤ | δ * (n : ℝ) ∈ negA} =
      (fun n : ℤ => -n) '' {n : ℤ | δ * (n : ℝ) ∈ A} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro h
      rcases h with ⟨x, hxA, h_eq⟩
      rcases hA hxA with ⟨m, rfl⟩
      have h5 : n = -m := by
        have h6 : (n : ℝ) = -(m : ℝ) := by
          apply (mul_right_inj' (ne_of_gt hδ)).mp
          linarith
        exact_mod_cast h6
      exact ⟨m, by simpa using hxA, by linarith⟩
    · rintro ⟨m, hm, rfl⟩
      have h2 : δ * (m : ℝ) ∈ A := by simpa using hm
      have h3 : -δ * (m : ℝ) ∈ negA := ⟨δ * (m : ℝ), h2, by ring⟩
      simpa using h3
  have h_neg_inj : Function.Injective (fun n : ℤ => -n) := by
    intro a b h; simpa using h
  have h_encard : (bourgain_projection_theorem.realCubeIndexSet δ negA).encard =
      (bourgain_projection_theorem.realCubeIndexSet δ A).encard := by
    rw [h_idx_neg, h_set_eq, h_idx_A]
    exact h_neg_inj.encard_image _
  have h_main1 : Nreal δ negA =
      ENat.toENNReal (bourgain_projection_theorem.realCubeIndexSet δ negA).encard :=
    bourgain_projection_theorem.realCoveringNumber_eq_card hδ hnegA_bdd
  have h_main2 : Nreal δ A =
      ENat.toENNReal (bourgain_projection_theorem.realCubeIndexSet δ A).encard :=
    bourgain_projection_theorem.realCoveringNumber_eq_card hδ hA_bdd
  rw [h_main1, h_main2, h_encard]

/-! ========================================================================
   Quantitative four-sector chart with cross-ratio Lipschitz bounds
   ======================================================================== -/

/-- Cross-ratio coefficient x(y). -/
def chartCrossRatio (y1 y2 y3 y : ℝ) : ℝ :=
  ((y2 - y3) * (y - y1)) / ((y3 - y1) * (y2 - y))

/-- Sector t-map: normalized parameter in [0,1]. -/
def chartSectorT (i : Fin 4) (x : ℝ) : ℝ :=
  match i with
  | 0 => x
  | 1 => 1 / x
  | 2 => -x
  | 3 => -1 / x

@[simp] lemma chartSectorT_0 (x : ℝ) : chartSectorT 0 x = x := by
  unfold chartSectorT; rfl
@[simp] lemma chartSectorT_1 (x : ℝ) : chartSectorT 1 x = 1 / x := by
  unfold chartSectorT; rfl
@[simp] lemma chartSectorT_2 (x : ℝ) : chartSectorT 2 x = -x := by
  unfold chartSectorT; rfl
@[simp] lemma chartSectorT_3 (x : ℝ) : chartSectorT 3 x = -1 / x := by
  unfold chartSectorT; rfl

/-- Sector coordinate map: signed permutation of (U,V). -/
def chartSectorCoord (i : Fin 4) (U V : ℝ) : ℝ × ℝ :=
  match i with
  | 0 => (V, U)
  | 1 => (U, V)
  | 2 => (-V, U)
  | 3 => (-U, V)

/-- Sector predicate based on cross-ratio value. -/
def chartSectorPred (i : Fin 4) (x : ℝ) : Prop :=
  match i with
  | 0 => 0 ≤ x ∧ x ≤ 1
  | 1 => 1 < x
  | 2 => -1 ≤ x ∧ x < 0
  | 3 => x < -1

/-- Sector scalar: 1 for sectors 0,2; 1/x for sectors 1,3. -/
def chartSectorScalar (i : Fin 4) (x : ℝ) : ℝ :=
  if i = 0 ∨ i = 2 then 1 else 1 / x

/-- Full projection scalar: lam = (a3/a_y) * sectorScalar. -/
def chartFullLambda (y1 y2 y3 y : ℝ) (i : Fin 4) : ℝ :=
  ((y2 - y3) / (y2 - y)) * chartSectorScalar i (chartCrossRatio y1 y2 y3 y)

/-- Cross-ratio difference identity. -/
lemma chart_cross_ratio_difference {y1 y2 y3 y z : ℝ}
    (h13 : y1 < y3) (h32 : y3 < y2)
    (hy2 : y ≠ y2) (hz2 : z ≠ y2) :
    chartCrossRatio y1 y2 y3 y - chartCrossRatio y1 y2 y3 z =
      ((y2 - y3) * (y2 - y1) / (y3 - y1)) * (y - z) / ((y2 - y) * (y2 - z)) := by
  simp only [chartCrossRatio]
  have h31 : y3 - y1 ≠ 0 := by
    have h : 0 < y3 - y1 := by linarith
    exact h.ne'
  have h2y : y2 - y ≠ 0 := sub_ne_zero.mpr hy2.symm
  have h2z : y2 - z ≠ 0 := sub_ne_zero.mpr hz2.symm
  field_simp [h31, h2y, h2z] <;> ring

/-- t ∈ [0,1] in each sector. -/
lemma chart_sector_t_bounds (i : Fin 4) (x : ℝ) (h : chartSectorPred i x) :
    chartSectorT i x ∈ Set.Icc (0 : ℝ) 1 := by
  fin_cases i
  · simpa [chartSectorPred, chartSectorT] using h
  · have h1 : 1 < x := by simpa [chartSectorPred] using h
    have hpos : 0 < x := by linarith
    simp only [chartSectorT]
    have h_le : 1 / x ≤ 1 := by
      have h : 1 ≤ x := by linarith
      have h' : 1 / x ≤ x / x := by gcongr
      have h'' : x / x = 1 := by field_simp [hpos.ne'] <;> ring
      rw [h''] at h'
      exact h'
    exact ⟨by positivity, h_le⟩
  · have h2 : -1 ≤ x ∧ x < 0 := by simpa [chartSectorPred] using h
    simp only [chartSectorT]
    exact ⟨by linarith, by linarith⟩
  · have h3 : x < -1 := by simpa [chartSectorPred] using h
    have hneg : x < 0 := by linarith
    simp only [chartSectorT]
    have h4 : -1 / x = 1 / (-x) := by field_simp [hneg.ne] <;> ring
    rw [h4]
    have h5 : 0 < -x := by linarith
    have h_le : 1 / (-x) ≤ 1 := by
      have h6 : 1 ≤ -x := by linarith
      have h7 : 1 / (-x) ≤ (-x) / (-x) := by gcongr
      have h8 : (-x) / (-x) = 1 := by
        apply div_self
        linarith
      rw [h8] at h7
      exact h7
    exact ⟨by positivity, h_le⟩

/-- Projection identity. -/
lemma chart_sector_projection_identity (i : Fin 4) (x : ℝ)
    (h : chartSectorPred i x) (U V : ℝ) :
    chartSectorT i x * (chartSectorCoord i U V).1 + (chartSectorCoord i U V).2 =
      chartSectorScalar i x * (U + x * V) := by
  fin_cases i
  · simp [chartSectorPred, chartSectorT, chartSectorCoord, chartSectorScalar] at h ⊢ <;> ring
  · have hx_ne : x ≠ 0 := by
      have h1 : 1 < x := by simpa [chartSectorPred] using h
      linarith
    simp [chartSectorPred, chartSectorT, chartSectorCoord, chartSectorScalar, hx_ne]
    <;> field_simp [hx_ne] <;> ring
  · simp [chartSectorPred, chartSectorT, chartSectorCoord, chartSectorScalar] at h ⊢ <;> ring
  · have hx_ne : x ≠ 0 := by
      have h3 : x < -1 := by simpa [chartSectorPred] using h
      linarith
    simp [chartSectorPred, chartSectorT, chartSectorCoord, chartSectorScalar, hx_ne]
    <;> field_simp [hx_ne] <;> ring

/-- |sectorScalar| ≤ 1. -/
lemma chart_sector_scalar_bound (i : Fin 4) (x : ℝ) (h : chartSectorPred i x) :
    |chartSectorScalar i x| ≤ 1 := by
  fin_cases i
  · simp [chartSectorScalar, chartSectorPred] at * <;> norm_num
  · have h1 : 1 < x := by simpa [chartSectorPred] using h
    have hpos : 0 < x := by linarith
    have h_goal : |(1 / x : ℝ)| ≤ 1 := by
      rw [abs_of_pos (by positivity)]
      have h_le : 1 / x ≤ 1 := by
        have h : 1 ≤ x := by linarith
        have h' : 1 / x ≤ x / x := by gcongr
        have h'' : x / x = 1 := by field_simp [hpos.ne'] <;> ring
        rw [h''] at h'
        exact h'
      exact h_le
    simpa [chartSectorScalar, chartSectorPred] using h_goal
  · simp [chartSectorScalar, chartSectorPred] at * <;> norm_num
  · have h3 : x < -1 := by simpa [chartSectorPred] using h
    have h_pos : 0 < |x| := by
      apply abs_pos.mpr
      linarith
    have h_neg : x < 0 := by linarith
    have h9 : 1 ≤ |x| := by
      have h10 : |x| = -x := by
        rw [abs_of_neg h_neg] <;> ring
      rw [h10]
      linarith
    have h_goal : |(1 / x : ℝ)| ≤ 1 := by
      have h : |(1 / x : ℝ)| = 1 / |x| := by rw [abs_div, abs_one]
      rw [h]
      have h_le : 1 / |x| ≤ 1 := by
        have h10 : 1 / |x| ≤ |x| / |x| := by gcongr
        have h11 : |x| / |x| = 1 := by
          apply div_self
          exact h_pos.ne'
        rw [h11] at h10
        exact h10
      exact h_le
    simpa [chartSectorScalar, chartSectorPred] using h_goal

/-- Full lambda in reciprocal sectors equals (y3-y1)/(y-y1). -/
lemma chart_full_lambda_reciprocal {y1 y2 y3 y : ℝ}
    (h13 : y1 < y3) (h32 : y3 < y2)
    (hy2 : y ≠ y2) (hy1 : y ≠ y1) :
    chartFullLambda y1 y2 y3 y 1 = (y3 - y1) / (y - y1) ∧
    chartFullLambda y1 y2 y3 y 3 = (y3 - y1) / (y - y1) := by
  have h_pos31 : 0 < y3 - y1 := by linarith
  have h31 : y3 - y1 ≠ 0 := h_pos31.ne'
  have h2y : y2 - y ≠ 0 := sub_ne_zero.mpr hy2.symm
  have h1y : y - y1 ≠ 0 := sub_ne_zero.mpr hy1
  have h_pos23 : 0 < y2 - y3 := by linarith
  have h23 : y2 - y3 ≠ 0 := h_pos23.ne'
  constructor <;> simp [chartFullLambda, chartSectorScalar, chartCrossRatio, h31, h2y, h1y, h23]
    <;> field_simp [h31, h2y, h1y, h23] <;> ring

/-- Bound |fullLambda| ≤ 1/(d*r). -/
lemma chart_full_lambda_bound {y1 y2 y3 : ℝ} (h13 : y1 < y3) (h32 : y3 < y2)
    {r d : ℝ} (hr_pos : 0 < r) (hd_pos : 0 < d)
    (hd1 : d ≤ y3 - y1) (hd2 : d ≤ y2 - y3)
    (h_y1_nonneg : 0 ≤ y1) (h_y2_le_one : y2 ≤ 1)
    {i : Fin 4} {y : ℝ}
    (h_sector : chartSectorPred i (chartCrossRatio y1 y2 y3 y))
    (h_pole : r ≤ |y2 - y|) :
    |chartFullLambda y1 y2 y3 y i| ≤ 1 / (d * r) := by
  have h23_le1 : |y2 - y3| ≤ 1 := by
    have h' : 0 ≤ y2 - y3 := by linarith
    have h_abs : |y2 - y3| = y2 - y3 := abs_of_nonneg h'
    rw [h_abs]
    linarith
  have h2y_ge_r : r ≤ |y2 - y| := h_pole
  have h2y_pos : 0 < |y2 - y| := by linarith
  have h_scalar_le1 : |chartSectorScalar i (chartCrossRatio y1 y2 y3 y)| ≤ 1 :=
    chart_sector_scalar_bound i (chartCrossRatio y1 y2 y3 y) h_sector
  have h_d_le_one : d ≤ 1 := by
    have h : d ≤ y3 - y1 := hd1
    have h' : y3 - y1 ≤ 1 := by linarith
    linarith
  have h_main : |chartFullLambda y1 y2 y3 y i| ≤ 1 / r := by
    simp only [chartFullLambda]
    have h_abs : |((y2 - y3) / (y2 - y)) * chartSectorScalar i (chartCrossRatio y1 y2 y3 y)| =
        |y2 - y3| / |y2 - y| * |chartSectorScalar i (chartCrossRatio y1 y2 y3 y)| := by
      rw [abs_mul, abs_div] <;> ring
    rw [h_abs]
    calc
      |y2 - y3| / |y2 - y| * |chartSectorScalar i (chartCrossRatio y1 y2 y3 y)|
        ≤ 1 / |y2 - y| * 1 := by gcongr
      _ = 1 / |y2 - y| := by ring
      _ ≤ 1 / r := by gcongr
  have h_final : 1 / r ≤ 1 / (d * r) := by
    have h_pos : 0 < d * r := mul_pos hd_pos hr_pos
    have h_le : d * r ≤ r := by
      have h : d ≤ 1 := h_d_le_one
      nlinarith
    exact one_div_le_one_div_of_le (by positivity) h_le
  exact h_main.trans h_final

/-- Cross-ratio absolute difference bounds. -/
lemma chart_cross_ratio_abs_bounds {y1 y2 y3 y z : ℝ}
    (h13 : y1 < y3) (h32 : y3 < y2)
    {r : ℝ} (hr_pos : 0 < r)
    (hyr : r ≤ |y2 - y|) (hzr : r ≤ |y2 - z|)
    (hyb : |y2 - y| ≤ 1) (hzb : |y2 - z| ≤ 1) :
    let C_const := (y2 - y3) * (y2 - y1) / (y3 - y1)
    C_const * |y - z| ≤ |chartCrossRatio y1 y2 y3 y - chartCrossRatio y1 y2 y3 z| ∧
    |chartCrossRatio y1 y2 y3 y - chartCrossRatio y1 y2 y3 z| ≤ C_const / r^2 * |y - z| := by
  dsimp
  set C_const := (y2 - y3) * (y2 - y1) / (y3 - y1) with hC_def
  have h_num_pos : 0 < (y2 - y3) * (y2 - y1) := by
    have h1 : 0 < y2 - y3 := by linarith
    have h2 : 0 < y2 - y1 := by linarith
    exact mul_pos h1 h2
  have h_den_pos : 0 < y3 - y1 := by linarith
  have hC_pos : 0 < C_const := by
    rw [hC_def]; exact div_pos h_num_pos h_den_pos
  have hy2 : y ≠ y2 := by
    have h : 0 < |y2 - y| := by linarith
    have h' : y2 - y ≠ 0 := abs_pos.mp h
    exact (sub_ne_zero.mp h').symm
  have hz2 : z ≠ y2 := by
    have h : 0 < |y2 - z| := by linarith
    have h' : y2 - z ≠ 0 := abs_pos.mp h
    exact (sub_ne_zero.mp h').symm
  have h_diff := chart_cross_ratio_difference h13 h32 hy2 hz2
  have h_abs : |chartCrossRatio y1 y2 y3 y - chartCrossRatio y1 y2 y3 z| =
      C_const * |y - z| / |(y2 - y) * (y2 - z)| := by
    rw [h_diff]
    have h : |C_const * (y - z) / ((y2 - y) * (y2 - z))| =
        |C_const| * |y - z| / |(y2 - y) * (y2 - z)| := by
      simp [abs_mul, abs_div]
      <;> ring
    rw [h, abs_of_pos hC_pos] <;> ring
  have h_prod_pos : 0 < |(y2 - y) * (y2 - z)| := by positivity
  have h_prod_lower : r^2 ≤ |(y2 - y) * (y2 - z)| := by
    have h1 : 0 ≤ r := by linarith
    have h2 : r * r ≤ |y2 - y| * |y2 - z| := by
      exact mul_le_mul hyr hzr (by linarith) (by linarith)
    have h3 : r * r = r^2 := by ring
    rw [h3] at h2
    have h4 : |(y2 - y) * (y2 - z)| = |y2 - y| * |y2 - z| := by rw [abs_mul]
    rw [h4]
    exact h2
  have h_prod_upper : |(y2 - y) * (y2 - z)| ≤ 1 := by
    have h1 : |y2 - y| * |y2 - z| ≤ 1 := by
      have h2 : |y2 - y| ≤ 1 := hyb
      have h3 : |y2 - z| ≤ 1 := hzb
      have h4 : |y2 - y| * |y2 - z| ≤ 1 * 1 := by
        exact mul_le_mul h2 h3 (abs_nonneg _) (by linarith)
      simpa using h4
    have h5 : |(y2 - y) * (y2 - z)| = |y2 - y| * |y2 - z| := by rw [abs_mul]
    rw [h5]
    exact h1
  have h_a_nonneg : 0 ≤ C_const * |y - z| := by positivity
  constructor
  · rw [h_abs]
    have h : C_const * |y - z| / 1 ≤ C_const * |y - z| / |(y2 - y) * (y2 - z)| :=
      div_le_div_of_nonneg_left h_a_nonneg h_prod_pos h_prod_upper
    simpa using h
  · rw [h_abs]
    have h2 : 1 / |(y2 - y) * (y2 - z)| ≤ 1 / r^2 :=
      one_div_le_one_div_of_le (by positivity) h_prod_lower
    have h3 : C_const * |y - z| / |(y2 - y) * (y2 - z)| =
        C_const * (1 / |(y2 - y) * (y2 - z)|) * |y - z| := by ring
    rw [h3]
    have h4 : C_const * (1 / |(y2 - y) * (y2 - z)|) * |y - z| ≤
        C_const * (1 / r^2) * |y - z| := by gcongr
    have h5 : C_const * (1 / r^2) * |y - z| = C_const / r^2 * |y - z| := by ring
    rw [h5] at h4
    exact h4

/-- Reciprocal Lipschitz bounds. -/
lemma chart_reciprocal_lipschitz {x y M : ℝ} (hM : 1 ≤ M)
    (hx1 : 1 ≤ |x|) (hy1 : 1 ≤ |y|)
    (hxM : |x| ≤ M) (hyM : |y| ≤ M) :
    |1 / x - 1 / y| ≤ |x - y| ∧ |x - y| ≤ M^2 * |1 / x - 1 / y| := by
  have hx_ne : x ≠ 0 := by
    have h : 0 < |x| := by linarith
    exact abs_pos.mp h
  have hy_ne : y ≠ 0 := by
    have h : 0 < |y| := by linarith
    exact abs_pos.mp h
  have h_abs : |1 / x - 1 / y| = |x - y| / |x * y| := by
    have h_eq : 1 / x - 1 / y = (y - x) / (x * y) := by
      field_simp [hx_ne, hy_ne] <;> ring
    rw [h_eq, abs_div, abs_sub_comm, abs_mul]
  have h_prod_ge1 : 1 ≤ |x * y| := by
    have h : |x| * |y| ≥ 1 := by nlinarith [hx1, hy1]
    have h' : |x * y| = |x| * |y| := by rw [abs_mul]
    linarith
  have h_prod_leM2 : |x * y| ≤ M^2 := by
    have h : |x| * |y| ≤ M^2 := by nlinarith [hxM, hyM, hM]
    have h' : |x * y| = |x| * |y| := by rw [abs_mul]
    linarith
  have h_prod_pos : 0 < |x * y| := by linarith
  constructor
  · rw [h_abs]
    have h : |x - y| / |x * y| ≤ |x - y| / 1 := by gcongr
    simpa using h
  · rw [h_abs]
    by_cases hxy : |x - y| = 0
    · rw [hxy] <;> simp
    · have hxy_pos : 0 < |x - y| := by
        exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm hxy)
      have h12 : 1 ≤ M^2 / |x * y| := by
        rw [one_le_div h_prod_pos] <;> linarith
      calc |x - y|
        = 1 * |x - y| := by ring
      _ ≤ (M^2 / |x * y|) * |x - y| := by gcongr
      _ = M^2 * (|x - y| / |x * y|) := by ring

/-- Unified bound: |x - y| ≤ M^2 * |chartSectorT i x - chartSectorT i y| for all sectors. -/
private lemma sector_abs_unified_bound {i : Fin 4} {x y M : ℝ} (hM : 1 ≤ M)
    (hxM : |x| ≤ M) (hyM : |y| ≤ M)
    (h_sector_x : chartSectorPred i x) (h_sector_y : chartSectorPred i y) :
    |x - y| ≤ M^2 * |chartSectorT i x - chartSectorT i y| := by
  have hM2 : 1 ≤ M^2 := by nlinarith
  have h_direct : |x - y| ≤ M^2 * |x - y| := by
    have h : 1 * |x - y| ≤ M^2 * |x - y| := mul_le_mul_of_nonneg_right hM2 (abs_nonneg (x - y))
    simpa using h
  have h_main : ∀ (j : Fin 4), chartSectorPred j x → chartSectorPred j y →
      |x - y| ≤ M^2 * |chartSectorT j x - chartSectorT j y| := by
    intro j hx hy
    fin_cases j
    · have h_goal : |x - y| ≤ M^2 * |chartSectorT 0 x - chartSectorT 0 y| := by
        rw [chartSectorT_0 x, chartSectorT_0 y]
        exact h_direct
      exact h_goal
    · have hx1 : 1 ≤ |x| := by
        have h : 1 < x := hx
        have hpos : 0 < x := by linarith
        rw [abs_of_pos hpos] <;> linarith
      have hy1 : 1 ≤ |y| := by
        have h : 1 < y := hy
        have hpos : 0 < y := by linarith
        rw [abs_of_pos hpos] <;> linarith
      have h_recip := chart_reciprocal_lipschitz hM hx1 hy1 hxM hyM
      have h_goal : |x - y| ≤ M^2 * |chartSectorT 1 x - chartSectorT 1 y| := by
        rw [chartSectorT_1 x, chartSectorT_1 y]
        exact h_recip.2
      exact h_goal
    · have h_goal2 : |x - y| ≤ M^2 * |chartSectorT 2 x - chartSectorT 2 y| := by
        rw [chartSectorT_2 x, chartSectorT_2 y]
        have h_abs : |(-x) - (-y)| = |x - y| := by
          have h_eq : (-x) - (-y) = -(x - y) := by ring
          rw [h_eq, abs_neg]
        rw [h_abs]
        exact h_direct
      exact h_goal2
    · have hx3 : 1 ≤ |x| := by
        have h : x < -1 := hx
        have hneg : x < 0 := by linarith
        rw [abs_of_neg hneg] <;> linarith
      have hy3 : 1 ≤ |y| := by
        have h : y < -1 := hy
        have hneg : y < 0 := by linarith
        rw [abs_of_neg hneg] <;> linarith
      have h_recip3 := chart_reciprocal_lipschitz hM hx3 hy3 hxM hyM
      have h_goal : |x - y| ≤ M^2 * |chartSectorT 3 x - chartSectorT 3 y| := by
        rw [chartSectorT_3 x, chartSectorT_3 y]
        have h_abs : |(-1 / x) - (-1 / y)| = |1 / x - 1 / y| := by
          have h_eq : (-1 / x) - (-1 / y) = -(1 / x - 1 / y) := by ring
          rw [h_eq, abs_neg]
        rw [h_abs]
        exact h_recip3.2
      exact h_goal
  exact h_main i h_sector_x h_sector_y

/-- Helper for co-Lipschitz bound, extracted to avoid fin_cases timeout. -/
private lemma sector_colipschitz_helper
    {r d : ℝ} {i : Fin 4} {Theta_sec : Set ℝ}
    {x : ℝ → ℝ} {C_const C_chart M : ℝ}
    (hd_pos : 0 < d) (hr_pos : 0 < r) (hC_pos : 0 < C_const)
    (h_M2_bound : M^2 / C_const ≤ (1 / (d * r))^2 / (2 * d^2))
    (h_helper3 : 1 / (2 * d^4 * r^2) ≤ C_chart)
    (hM1 : 1 ≤ M) (h_xyM : ∀ y ∈ Theta_sec, |x y| ≤ M)
    (h_xzM : ∀ z ∈ Theta_sec, |x z| ≤ M)
    (h_sector : ∀ y ∈ Theta_sec, chartSectorPred i (x y))
    (y z : ℝ) (hy : y ∈ Theta_sec) (hz : z ∈ Theta_sec)
    (h_colip_helper : |y - z| ≤ (1 / C_const) * |x y - x z|) :
    |y - z| ≤ C_chart * |chartSectorT i (x y) - chartSectorT i (x z)| := by
  have h1 : |x y - x z| ≤ M^2 * |chartSectorT i (x y) - chartSectorT i (x z)| :=
    sector_abs_unified_bound hM1 (h_xyM y hy) (h_xzM z hz) (h_sector y hy) (h_sector z hz)
  have h2 : 0 ≤ 1 / C_const := by positivity
  have h3 : 0 ≤ |chartSectorT i (x y) - chartSectorT i (x z)| := abs_nonneg _
  have h4 : (1 / C_const) * (M^2 * |chartSectorT i (x y) - chartSectorT i (x z)|) =
      (M^2 / C_const) * |chartSectorT i (x y) - chartSectorT i (x z)| := by ring
  have h5 : (M^2 / C_const) * |chartSectorT i (x y) - chartSectorT i (x z)| ≤
      ((1 / (d * r))^2 / (2 * d^2)) * |chartSectorT i (x y) - chartSectorT i (x z)| :=
    mul_le_mul_of_nonneg_right h_M2_bound h3
  have h6 : ((1 / (d * r))^2 / (2 * d^2)) = 1 / (2 * d^4 * r^2) := by
    field_simp [hd_pos.ne', hr_pos.ne'] <;> ring
  calc |y - z|
    ≤ (1 / C_const) * |x y - x z| := h_colip_helper
  _ ≤ (1 / C_const) * (M^2 * |chartSectorT i (x y) - chartSectorT i (x z)|) :=
    mul_le_mul_of_nonneg_left h1 h2
  _ = (M^2 / C_const) * |chartSectorT i (x y) - chartSectorT i (x z)| := h4
  _ ≤ ((1 / (d * r))^2 / (2 * d^2)) * |chartSectorT i (x y) - chartSectorT i (x z)| := h5
  _ = (1 / (2 * d^4 * r^2)) * |chartSectorT i (x y) - chartSectorT i (x z)| := by rw [h6]
  _ ≤ C_chart * |chartSectorT i (x y) - chartSectorT i (x z)| :=
    mul_le_mul_of_nonneg_right h_helper3 h3

/-- Helper for `sector_chart_transport` with explicit return type to avoid `let`-binding `isDefEq` timeout. -/
private lemma sector_chart_transport_main
    {y1 y2 y3 : ℝ} (h13 : y1 < y3) (h32 : y3 < y2)
    (h_y1_nonneg : 0 ≤ y1) (h_y2_le_one : y2 ≤ 1)
    {r d : ℝ} (hr_pos : 0 < r) (hd_pos : 0 < d)
    (hd1 : d ≤ y3 - y1) (hd2 : d ≤ y2 - y3)
    (hd_le_one : d ≤ 1) (hr_le_one : r ≤ 1)
    {i : Fin 4} {Theta_sec : Set ℝ}
    (h_sector : ∀ y ∈ Theta_sec, chartSectorPred i (chartCrossRatio y1 y2 y3 y))
    (h_pole : ∀ y ∈ Theta_sec, r ≤ |y2 - y|)
    (h_bounded : ∀ y ∈ Theta_sec, |y2 - y| ≤ 1)
    (h_x_bound : ∀ y ∈ Theta_sec, |chartCrossRatio y1 y2 y3 y| ≤ 1 / (d * r))
    (y z : ℝ) (hy : y ∈ Theta_sec) (hz : z ∈ Theta_sec) :
    (chartSectorT i (chartCrossRatio y1 y2 y3 y) ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ U V : ℝ, chartSectorT i (chartCrossRatio y1 y2 y3 y) * (chartSectorCoord i U V).1 + (chartSectorCoord i U V).2 =
        chartSectorScalar i (chartCrossRatio y1 y2 y3 y) * (U + chartCrossRatio y1 y2 y3 y * V)) ∧
    (|chartFullLambda y1 y2 y3 y i| ≤ 1 / (d * r)) ∧
    (|y - z| ≤ (1 / (d^4 * r^2)) * |chartSectorT i (chartCrossRatio y1 y2 y3 y) - chartSectorT i (chartCrossRatio y1 y2 y3 z)|) ∧
    (|chartSectorT i (chartCrossRatio y1 y2 y3 y) - chartSectorT i (chartCrossRatio y1 y2 y3 z)| ≤ (1 / (d^4 * r^2)) * |y - z|) := by
  let x := chartCrossRatio y1 y2 y3
  let C_const := (y2 - y3) * (y2 - y1) / (y3 - y1)
  let C_chart := 1 / (d^4 * r^2)
  let M := 1 / (d * r)

  have h_num_pos : 0 < (y2 - y3) * (y2 - y1) := by
    have h1 : 0 < y2 - y3 := by linarith
    have h2 : 0 < y2 - y1 := by linarith
    exact mul_pos h1 h2
  have h_den_pos : 0 < y3 - y1 := by linarith
  have hC_pos : 0 < C_const := by
    dsimp only [C_const]; exact div_pos h_num_pos h_den_pos
  have hC_lower : C_const ≥ 2 * d^2 := by
    dsimp only [C_const]
    have h1 : y2 - y3 ≥ d := hd2
    have h2 : y2 - y1 ≥ 2 * d := by linarith
    have h3 : y3 - y1 ≤ 1 := by linarith
    have h4 : (y2 - y3) * (y2 - y1) ≥ d * (2 * d) := by
      exact mul_le_mul h1 h2 (by linarith) (by linarith)
    have h5 : (y2 - y3) * (y2 - y1) / (y3 - y1) ≥ (d * (2 * d)) / (y3 - y1) := by gcongr
    have h6 : (d * (2 * d)) / (y3 - y1) ≥ 2 * d^2 := by
      have h7 : 0 < y3 - y1 := h_den_pos
      have h8 : (d * (2 * d)) / (y3 - y1) = (2 * d^2) / (y3 - y1) := by ring
      rw [h8]
      have h9 : 1 ≤ 1 / (y3 - y1) := by
        have h10 : y3 - y1 ≤ 1 := by linarith
        rw [one_le_div h7] <;> linarith
      have h11 : (2 * d^2) / (y3 - y1) = (2 * d^2) * (1 / (y3 - y1)) := by ring
      rw [h11]; nlinarith
    linarith
  have hC_upper : C_const ≤ 1 / d := by
    dsimp only [C_const]
    have h1 : y2 - y3 ≤ 1 := by linarith
    have h2 : y2 - y1 ≤ 1 := by linarith
    have h3 : y3 - y1 ≥ d := hd1
    have h4 : (y2 - y3) * (y2 - y1) ≤ 1 := by nlinarith
    have h5 : (y2 - y3) * (y2 - y1) / (y3 - y1) ≤ 1 / (y3 - y1) := by gcongr
    have h6 : 1 / (y3 - y1) ≤ 1 / d := by
      apply one_div_le_one_div_of_le <;> linarith
    linarith

  have h_abs_bounds := chart_cross_ratio_abs_bounds h13 h32 hr_pos
    (h_pole y hy) (h_pole z hz) (h_bounded y hy) (h_bounded z hz)
  have h_lower : C_const * |y - z| ≤ |x y - x z| := h_abs_bounds.1
  have h_upper : |x y - x z| ≤ C_const / r^2 * |y - z| := h_abs_bounds.2

  have h_t_bounds : chartSectorT i (x y) ∈ Set.Icc (0 : ℝ) 1 :=
    chart_sector_t_bounds i (x y) (h_sector y hy)
  have h_proj : ∀ U V : ℝ, chartSectorT i (x y) * (chartSectorCoord i U V).1 + (chartSectorCoord i U V).2 =
      chartSectorScalar i (x y) * (U + x y * V) :=
    fun U V => chart_sector_projection_identity i (x y) (h_sector y hy) U V
  have h_lambda : |chartFullLambda y1 y2 y3 y i| ≤ 1 / (d * r) :=
    chart_full_lambda_bound h13 h32 hr_pos hd_pos hd1 hd2 h_y1_nonneg h_y2_le_one
      (h_sector y hy) (h_pole y hy)

  have hM1 : 1 ≤ M := by
    dsimp only [M]
    have h_pos : 0 < d * r := mul_pos hd_pos hr_pos
    have h_le : d * r ≤ 1 := by nlinarith
    have h3 : 1 ≤ 1 / (d * r) := by
      rw [one_le_div (by positivity)] <;> linarith
    exact h3
  have h_xyM : |x y| ≤ M := h_x_bound y hy
  have h_xzM : |x z| ≤ M := h_x_bound z hz

  have h_colip_helper : |y - z| ≤ (1 / C_const) * |x y - x z| := by
    have h : C_const * |y - z| ≤ |x y - x z| := h_lower
    have hpos : 0 < C_const := hC_pos
    calc |y - z|
      = (1 / C_const) * (C_const * |y - z|) := by field_simp [hpos.ne'] <;> ring
    _ ≤ (1 / C_const) * |x y - x z| := by gcongr

  have h_lip_helper1 : |x y - x z| ≤ (1 / d) / r^2 * |y - z| := by
    calc |x y - x z|
      ≤ C_const / r^2 * |y - z| := h_upper
    _ ≤ (1 / d) / r^2 * |y - z| := by gcongr

  have h_helper1 : 1 / (d * r^2) ≤ C_chart := by
    dsimp only [C_chart]
    have h1 : 0 < d * r^2 := by positivity
    have h2 : 0 < d^4 * r^2 := by positivity
    have h3 : d^4 * r^2 ≤ d * r^2 := by
      have h4 : d^4 ≤ d := by
        have h5 : 0 ≤ d := by linarith
        have h6 : d^3 ≤ 1 := by
          calc d^3 ≤ 1^3 := by gcongr
            _ = 1 := by norm_num
        have h7 : d^4 = d * d^3 := by ring
        rw [h7]; nlinarith
      nlinarith
    exact one_div_le_one_div_of_le (by positivity) h3

  have h_helper3 : 1 / (2 * d^4 * r^2) ≤ C_chart := by
    dsimp only [C_chart]
    have h1 : 0 < d^4 * r^2 := by positivity
    have h2 : d^4 * r^2 ≤ 2 * d^4 * r^2 := by
      have h3 : 0 ≤ d^4 * r^2 := by positivity
      nlinarith
    exact one_div_le_one_div_of_le (by positivity) h2

  have h_M2_bound : M^2 / C_const ≤ (1 / (d * r))^2 / (2 * d^2) := by
    have hM2 : M^2 = (1 / (d * r))^2 := by rfl
    have hC : 1 / C_const ≤ 1 / (2 * d^2) := one_div_le_one_div_of_le (by positivity) hC_lower
    have h_nonneg : 0 ≤ (1 / (d * r))^2 := by positivity
    have h : (1 / (d * r))^2 * (1 / C_const) ≤ (1 / (d * r))^2 * (1 / (2 * d^2)) :=
      mul_le_mul_of_nonneg_left hC h_nonneg
    have h1 : M^2 / C_const = (1 / (d * r))^2 * (1 / C_const) := by
      rw [hM2] <;> ring
    have h2 : (1 / (d * r))^2 / (2 * d^2) = (1 / (d * r))^2 * (1 / (2 * d^2)) := by ring
    rw [h1, h2]; exact h

  have h_abs_neg : ∀ (a b : ℝ), |(-a) - (-b)| = |a - b| := by
    intro a b
    have h : (-a) - (-b) = -(a - b) := by ring
    rw [h, abs_neg]
  have h_abs_neg_recip : ∀ (a b : ℝ), |(-1 / a) - (-1 / b)| = |1 / a - 1 / b| := by
    intro a b
    have h : (-1 / a) - (-1 / b) = -(1 / a - 1 / b) := by ring
    rw [h, abs_neg]

  have h_sector1_abs : ∀ (w : ℝ), chartSectorPred 1 w → 1 ≤ |w| := by
    intro w hw
    have h : 1 < w := by simpa [chartSectorPred] using hw
    have hpos : 0 < w := by linarith
    have habs : |w| = w := abs_of_pos hpos
    rw [habs]; linarith
  have h_sector3_abs : ∀ (w : ℝ), chartSectorPred 3 w → 1 ≤ |w| := by
    intro w hw
    have h : w < -1 := by simpa [chartSectorPred] using hw
    have hneg : w < 0 := by linarith
    have habs : |w| = -w := abs_of_neg hneg
    rw [habs]; linarith

  have h_main_lipschitz : |chartSectorT i (x y) - chartSectorT i (x z)| ≤ C_chart * |y - z| := by
    fin_cases i
    · -- Sector 0
      calc |x y - x z|
        ≤ (1 / d) / r^2 * |y - z| := h_lip_helper1
      _ = 1 / (d * r^2) * |y - z| := by ring
      _ ≤ C_chart * |y - z| := mul_le_mul_of_nonneg_right h_helper1 (abs_nonneg _)
    · -- Sector 1
      have h_xy1 : 1 ≤ |x y| := h_sector1_abs (x y) (h_sector y hy)
      have h_xz1 : 1 ≤ |x z| := h_sector1_abs (x z) (h_sector z hz)
      have h_recip := chart_reciprocal_lipschitz hM1 h_xy1 h_xz1 h_xyM h_xzM
      calc |1 / (x y) - 1 / (x z)|
        ≤ |x y - x z| := h_recip.1
      _ ≤ (1 / d) / r^2 * |y - z| := h_lip_helper1
      _ = 1 / (d * r^2) * |y - z| := by ring
      _ ≤ C_chart * |y - z| := mul_le_mul_of_nonneg_right h_helper1 (abs_nonneg _)
    · -- Sector 2
      have h_goal : |(-(x y)) - (-(x z))| ≤ C_chart * |y - z| := by
        have h_eq : |(-(x y)) - (-(x z))| = |x y - x z| := h_abs_neg (x y) (x z)
        rw [h_eq]
        calc |x y - x z|
          ≤ (1 / d) / r^2 * |y - z| := h_lip_helper1
        _ = 1 / (d * r^2) * |y - z| := by ring
        _ ≤ C_chart * |y - z| := mul_le_mul_of_nonneg_right h_helper1 (abs_nonneg _)
      simpa [chartSectorT] using h_goal
    · -- Sector 3
      have h_xy1 : 1 ≤ |x y| := h_sector3_abs (x y) (h_sector y hy)
      have h_xz1 : 1 ≤ |x z| := h_sector3_abs (x z) (h_sector z hz)
      have h_recip := chart_reciprocal_lipschitz hM1 h_xy1 h_xz1 h_xyM h_xzM
      have h_goal : |(-1 / (x y)) - (-1 / (x z))| ≤ C_chart * |y - z| := by
        have h_eq : |(-1 / (x y)) - (-1 / (x z))| = |1 / (x y) - 1 / (x z)| := h_abs_neg_recip (x y) (x z)
        rw [h_eq]
        calc |1 / (x y) - 1 / (x z)|
          ≤ |x y - x z| := h_recip.1
        _ ≤ (1 / d) / r^2 * |y - z| := h_lip_helper1
        _ = 1 / (d * r^2) * |y - z| := by ring
        _ ≤ C_chart * |y - z| := mul_le_mul_of_nonneg_right h_helper1 (abs_nonneg _)
      simpa [chartSectorT] using h_goal

  have h_main_colipschitz : |y - z| ≤ C_chart * |chartSectorT i (x y) - chartSectorT i (x z)| :=
    sector_colipschitz_helper hd_pos hr_pos hC_pos h_M2_bound h_helper3
      hM1 h_x_bound h_x_bound h_sector y z hy hz h_colip_helper

  exact ⟨h_t_bounds, h_proj, h_lambda, h_main_colipschitz, h_main_lipschitz⟩

/-- **Quantitative four-sector chart transport theorem**. -/
theorem sector_chart_transport
    {y1 y2 y3 : ℝ} (h13 : y1 < y3) (h32 : y3 < y2)
    (h_y1_nonneg : 0 ≤ y1) (h_y2_le_one : y2 ≤ 1)
    {r d : ℝ} (hr_pos : 0 < r) (hd_pos : 0 < d)
    (hd1 : d ≤ y3 - y1) (hd2 : d ≤ y2 - y3)
    (hd_le_one : d ≤ 1) (hr_le_one : r ≤ 1)
    {i : Fin 4} {Theta_sec : Set ℝ}
    (h_sector : ∀ y ∈ Theta_sec, chartSectorPred i (chartCrossRatio y1 y2 y3 y))
    (h_pole : ∀ y ∈ Theta_sec, r ≤ |y2 - y|)
    (h_bounded : ∀ y ∈ Theta_sec, |y2 - y| ≤ 1)
    (h_x_bound : ∀ y ∈ Theta_sec, |chartCrossRatio y1 y2 y3 y| ≤ 1 / (d * r)) :
    ∀ (y z : ℝ), y ∈ Theta_sec → z ∈ Theta_sec →
      let x := chartCrossRatio y1 y2 y3
      let t := fun w => chartSectorT i (x w)
      let lam := fun w => chartFullLambda y1 y2 y3 w i
      let C_chart := 1 / (d^4 * r^2)
      (t y ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ U V : ℝ, t y * (chartSectorCoord i U V).1 + (chartSectorCoord i U V).2 =
          chartSectorScalar i (x y) * (U + x y * V)) ∧
      (|lam y| ≤ 1 / (d * r)) ∧
      (|y - z| ≤ C_chart * |t y - t z|) ∧
      (|t y - t z| ≤ C_chart * |y - z|) := by
  intro y z hy hz
  exact sector_chart_transport_main h13 h32 h_y1_nonneg h_y2_le_one hr_pos hd_pos hd1 hd2 hd_le_one hr_le_one h_sector h_pole h_bounded h_x_bound y z hy hz

/-! ### Four-sector projection covering preservation -/

/-- Count integers in a half-open interval `(a, b]` of length at most `L`.
The bound is `Nat.ceil L`. -/
private lemma int_count_half_open {a b L : ℝ} (hL_nonneg : 0 ≤ L)
    (h_len : b - a ≤ L) (S : Finset ℤ)
    (hS : ∀ m ∈ S, a < (m : ℝ) ∧ (m : ℝ) ≤ b) :
    S.card ≤ Nat.ceil L := by
  let base : ℤ := Int.floor a + 1
  have h_base_le : ∀ m ∈ S, base ≤ m := by
    intro m hm
    have h1 : a < (m : ℝ) := (hS m hm).1
    have h2 : (Int.floor a : ℝ) < (m : ℝ) := by
      have h3 : (Int.floor a : ℝ) ≤ a := Int.floor_le a
      linarith
    have h4 : Int.floor a < m := by exact_mod_cast h2
    simp only [base] <;> linarith
  let g : ℤ → ℕ := fun m => (m - base).toNat
  have h_g_eq : ∀ m ∈ S, (g m : ℤ) = m - base := by
    intro m hm
    have h10 : 0 ≤ m - base := by linarith [h_base_le m hm]
    dsimp only [g]
    rw [Int.toNat_of_nonneg h10] <;> norm_cast
  have h_lt : ∀ m ∈ S, g m < Nat.ceil L := by
    intro m hm
    have h_m_le : (m : ℝ) ≤ b := (hS m hm).2
    have h1 : ((m - base : ℤ) : ℝ) < L := by
      dsimp only [base]
      have h_frac : a - (Int.floor a : ℝ) < 1 := Int.fract_lt_one a
      have h2 : ((m - (Int.floor a + 1) : ℤ) : ℝ) = (m : ℝ) - (Int.floor a : ℝ) - 1 := by
        rw [Int.cast_sub, Int.cast_add] <;> ring
      rw [h2]
      linarith [h_len, h_frac]
    have h3 : (g m : ℝ) = ((m - base : ℤ) : ℝ) := by
      have h4 : (g m : ℤ) = m - base := h_g_eq m hm
      exact_mod_cast h4
    have h5 : (g m : ℝ) < L := by rw [h3] <;> exact h1
    have h6 : (L : ℝ) ≤ (Nat.ceil L : ℝ) := Nat.le_ceil L
    have h7 : (g m : ℝ) < (Nat.ceil L : ℝ) := by linarith
    exact_mod_cast h7
  have h_inj : Set.InjOn g (S : Set ℤ) := by
    intro m1 hm1 m2 hm2 h
    have h10 : (g m1 : ℤ) = (g m2 : ℤ) := by exact_mod_cast h
    have h11 : (g m1 : ℤ) = m1 - base := h_g_eq m1 hm1
    have h12 : (g m2 : ℤ) = m2 - base := h_g_eq m2 hm2
    rw [h11, h12] at h10 <;> linarith
  have h_image : S.image g ⊆ Finset.range (Nat.ceil L) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨m, hm, rfl⟩
    exact Finset.mem_range.mpr (h_lt m hm)
  have h13 : S.card = (S.image g).card := by
    rw [Finset.card_image_of_injOn h_inj]
  rw [h13]
  have h14 : (S.image g).card ≤ (Finset.range (Nat.ceil L)).card := Finset.card_le_card h_image
  have h15 : (Finset.range (Nat.ceil L)).card = Nat.ceil L := Finset.card_range _
  rw [h15] at h14
  exact h14

/-- **Scalar covering bound**. For `|c| ≤ M`, scaling a real set by `c`
increases its dyadic covering number by at most `⌈M⌉ + 1`. -/
lemma scalar_covering_upper {δ c M : ℝ} (hδ_pos : 0 < δ) (hM_nonneg : 0 ≤ M)
    {A : Set ℝ} (hA_bdd : Bornology.IsBounded A) (hc_bound : |c| ≤ M) :
    Nreal δ (scaleSet c A) ≤ (Nat.ceil M + 1 : ENNReal) * Nreal δ A := by
  by_cases hc0 : c = 0
  · -- c = 0: scaleSet 0 A ⊆ {0}, so Nreal δ (scaleSet 0 A) ≤ 1
    have h_sub : scaleSet c A ⊆ ({0} : Set ℝ) := by
      rw [hc0]
      intro z hz
      rcases hz with ⟨x, _, rfl⟩
      simp
    have h_bdd : Bornology.IsBounded (scaleSet c A) := by
      have h : Bornology.IsBounded ({0} : Set ℝ) := by exact Bornology.isBounded_singleton
      exact h.subset h_sub
    have h_idx : ProductLikeIncidence.realCubeIndexSet δ (scaleSet c A) ⊆ {0} := by
      intro k hk
      have h2 := ProductLikeIncidence.realCubeIndexSet_mem_iff.mp hk
      rcases h2 with ⟨z, hz, hle, hlt⟩
      have hz0 : z = 0 := h_sub hz
      have h3 : δ * (k : ℝ) ≤ 0 := by rw [hz0] at hle; exact hle
      have h4 : (0 : ℝ) < δ * ((k : ℝ) + 1) := by rw [hz0] at hlt; exact hlt
      have h5 : (k : ℝ) ≤ 0 := by
        nlinarith
      have h6 : -1 < (k : ℝ) := by nlinarith
      have h7 : k = 0 := by
        have h8 : -1 < k := by exact_mod_cast h6
        have h9 : k ≤ 0 := by exact_mod_cast h5
        omega
      simpa using h7
    have h_enc : (ProductLikeIncidence.realCubeIndexSet δ (scaleSet c A)).encard ≤ 1 := by
      calc
        (ProductLikeIncidence.realCubeIndexSet δ (scaleSet c A)).encard
          ≤ ({0} : Set ℤ).encard := Set.encard_mono h_idx
        _ = 1 := by simp
    have h_eq1 : Nreal δ (scaleSet c A) = ENat.toENNReal ((ProductLikeIncidence.realCubeIndexSet δ (scaleSet c A)).encard) :=
      ProductLikeIncidence.realCoveringNumber_eq_card_ennreal hδ_pos h_bdd
    by_cases hA : A.Nonempty
    · rcases hA with ⟨x, hx⟩
      let k : ℤ := Int.floor (x / δ)
      have h2 : δ * (k : ℝ) ≤ x := by
        dsimp only [k]
        have h3 : (k : ℝ) ≤ x / δ := Int.floor_le (x / δ)
        have h4 : δ * (k : ℝ) ≤ δ * (x / δ) := by gcongr
        have h5 : δ * (x / δ) = x := by field_simp [hδ_pos.ne'] <;> ring
        rw [h5] at h4 <;> exact h4
      have h3 : x < δ * ((k : ℝ) + 1) := by
        dsimp only [k]
        have h4 : x / δ < (k : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
        have h5 : δ * (x / δ) < δ * ((k : ℝ) + 1) := by gcongr
        have h6 : δ * (x / δ) = x := by field_simp [hδ_pos.ne'] <;> ring
        rw [h6] at h5 <;> exact h5
      have h_idxA : k ∈ ProductLikeIncidence.realCubeIndexSet δ A :=
        ProductLikeIncidence.realCubeIndexSet_mem_iff.mpr ⟨x, hx, h2, h3⟩
      have h_finA : (ProductLikeIncidence.realCubeIndexSet δ A).Finite :=
        ProductLikeIncidence.realCubeIndexSet_finite hδ_pos hA_bdd
      have h_nonempty : (ProductLikeIncidence.realCubeIndexSet δ A).Nonempty := ⟨k, h_idxA⟩
      have h_pos_enc : 0 < (ProductLikeIncidence.realCubeIndexSet δ A).encard :=
        Set.encard_pos.mpr h_nonempty
      have h_eq2 : Nreal δ A = ENat.toENNReal ((ProductLikeIncidence.realCubeIndexSet δ A).encard) :=
        ProductLikeIncidence.realCoveringNumber_eq_card_ennreal hδ_pos hA_bdd
      have h7 : 1 ≤ Nreal δ A := by
        rw [h_eq2]
        have h8 : 1 ≤ (ProductLikeIncidence.realCubeIndexSet δ A).encard := Order.one_le_iff_pos.mpr h_pos_enc
        exact_mod_cast h8
      have h9 : 1 ≤ (Nat.ceil M + 1 : ENNReal) := by
        simp [hM_nonneg] <;> norm_cast <;> omega
      calc
        Nreal δ (scaleSet c A)
          = ENat.toENNReal ((ProductLikeIncidence.realCubeIndexSet δ (scaleSet c A)).encard) := h_eq1
        _ ≤ 1 := by exact_mod_cast h_enc
        _ ≤ (Nat.ceil M + 1 : ENNReal) * Nreal δ A := one_le_mul h9 h7
    · have h_empty : A = ∅ := by
        simpa [Set.not_nonempty_iff_eq_empty] using hA
      have h_img : scaleSet c A = (∅ : Set ℝ) := by
        rw [hc0, h_empty]
        simp [scaleSet]
      have h_goal : Nreal δ (scaleSet c A) = 0 := by
        rw [h_img]
        have h1 : realLineCopy (∅ : Set ℝ) = (∅ : Set (EuclideanSpace ℝ (Fin 1))) := by
          simp [realLineCopy]
        simp [Nreal, dyadicCoveringNumber, dyadicCubesMeeting, h1]
        <;> rfl
      have h_rhs : Nreal δ A = 0 := by
        rw [h_empty]
        have h1 : realLineCopy (∅ : Set ℝ) = (∅ : Set (EuclideanSpace ℝ (Fin 1))) := by
          simp [realLineCopy]
        simp [Nreal, dyadicCoveringNumber, dyadicCubesMeeting, h1]
        <;> rfl
      rw [h_goal, h_rhs]
      <;> simp
  · -- c ≠ 0
    let I_cA := ProductLikeIncidence.realCubeIndexSet δ (scaleSet c A)
    let I_A := ProductLikeIncidence.realCubeIndexSet δ A
    have h_bdd_cA : Bornology.IsBounded (scaleSet c A) := by exact WeakTwoEndsSumProduct.scaleSet_bounded hA_bdd
    have h_fin_cA : I_cA.Finite := ProductLikeIncidence.realCubeIndexSet_finite hδ_pos h_bdd_cA
    have h_fin_A : I_A.Finite := ProductLikeIncidence.realCubeIndexSet_finite hδ_pos hA_bdd
    let K_cA : Finset ℤ := h_fin_cA.toFinset
    let K_A : Finset ℤ := h_fin_A.toFinset
    have hK_cA : (K_cA : Set ℤ) = I_cA := Set.Finite.coe_toFinset h_fin_cA
    have hK_A : (K_A : Set ℤ) = I_A := Set.Finite.coe_toFinset h_fin_A
    have h_exists : ∀ (m : ℤ), m ∈ I_cA → ∃ (x : ℝ), x ∈ A ∧ δ * (m : ℝ) ≤ c * x ∧ c * x < δ * ((m : ℝ) + 1) := by
      intro m hm
      have h_mem := ProductLikeIncidence.realCubeIndexSet_mem_iff.mp hm
      rcases h_mem with ⟨y, hyS, h1, h2⟩
      rcases hyS with ⟨x, hxA, rfl⟩
      exact ⟨x, hxA, h1, h2⟩
    classical
    let x : ℤ → ℝ := fun m => if h : m ∈ I_cA then Classical.choose (h_exists m h) else 0
    let k : ℤ → ℤ := fun m => Int.floor (x m / δ)
    have h_x_prop : ∀ m ∈ I_cA, x m ∈ A ∧ δ * (m : ℝ) ≤ c * (x m) ∧ c * (x m) < δ * ((m : ℝ) + 1) := by
      intro m hm
      have h' := Classical.choose_spec (h_exists m hm)
      have h_x_def : x m = Classical.choose (h_exists m hm) := by
        dsimp only [x]
        rw [dif_pos hm]
      rw [h_x_def] <;> exact h'
    have h_k_in_A : ∀ m ∈ K_cA, k m ∈ K_A := by
      intro m hm
      have hm' : m ∈ I_cA := by rw [←hK_cA] <;> exact hm
      have hxp := h_x_prop m hm'
      have h1 : δ * (k m : ℝ) ≤ x m := by
        dsimp only [k]
        have h2 : (k m : ℝ) ≤ x m / δ := Int.floor_le (x m / δ)
        have h3 : δ * (k m : ℝ) ≤ δ * (x m / δ) := by gcongr
        have h4 : δ * (x m / δ) = x m := by field_simp [hδ_pos.ne'] <;> ring
        rw [h4] at h3 <;> exact h3
      have h2 : x m < δ * ((k m : ℝ) + 1) := by
        dsimp only [k]
        have h3 : x m / δ < (k m : ℝ) + 1 := Int.lt_floor_add_one (x m / δ)
        have h4 : δ * (x m / δ) < δ * ((k m : ℝ) + 1) := by gcongr
        have h5 : δ * (x m / δ) = x m := by field_simp [hδ_pos.ne'] <;> ring
        rw [h5] at h4 <;> exact h4
      have h6 : k m ∈ I_A := ProductLikeIncidence.realCubeIndexSet_mem_iff.mpr
        ⟨x m, hxp.1, h1, h2⟩
      have h7 : k m ∈ (K_A : Set ℤ) := by rw [hK_A] <;> exact h6
      exact h7
    have h_fiber : ∀ j ∈ K_A, (K_cA.filter (fun m => k m = j)).card ≤ Nat.ceil M + 1 := by
      intro j hj
      let S := K_cA.filter (fun m => k m = j)
      by_cases hc_pos : 0 < c
      · -- c > 0
        have hS : ∀ m ∈ S, c * (j : ℝ) - 1 < (m : ℝ) ∧ (m : ℝ) ≤ c * ((j : ℝ) + 1) := by
          intro m hm
          have h_m_in_cA : m ∈ I_cA := by
            have h : m ∈ K_cA := (Finset.mem_filter.mp hm).1
            rw [←hK_cA] <;> exact h
          have h_k_eq : k m = j := (Finset.mem_filter.mp hm).2
          have hxp := h_x_prop m h_m_in_cA
          have h1 : δ * (j : ℝ) ≤ x m := by
            have h2 : δ * (k m : ℝ) ≤ x m := by
              dsimp only [k]; have h3 : (k m : ℝ) ≤ x m / δ := Int.floor_le (x m / δ)
              have h4 : δ * (k m : ℝ) ≤ δ * (x m / δ) := by gcongr
              have h5 : δ * (x m / δ) = x m := by field_simp [hδ_pos.ne'] <;> ring
              rw [h5] at h4 <;> exact h4
            rw [h_k_eq] at h2 <;> exact h2
          have h2 : x m < δ * ((j : ℝ) + 1) := by
            have h3 : x m < δ * ((k m : ℝ) + 1) := by
              dsimp only [k]; have h4 : x m / δ < (k m : ℝ) + 1 := Int.lt_floor_add_one (x m / δ)
              have h5 : δ * (x m / δ) < δ * ((k m : ℝ) + 1) := by gcongr
              have h6 : δ * (x m / δ) = x m := by field_simp [hδ_pos.ne'] <;> ring
              rw [h6] at h5 <;> exact h5
            rw [h_k_eq] at h3 <;> exact h3
          have h3 : δ * (m : ℝ) ≤ c * (x m) := hxp.2.1
          have h4 : c * (x m) < δ * ((m : ℝ) + 1) := hxp.2.2
          constructor
          · nlinarith
          · nlinarith
        have h_len : c * ((j : ℝ) + 1) - (c * (j : ℝ) - 1) = |c| + 1 := by
          rw [abs_of_pos hc_pos] <;> ring
        have h_len2 : c * ((j : ℝ) + 1) - (c * (j : ℝ) - 1) ≤ M + 1 := by
          rw [h_len]; have h9 : |c| ≤ M := hc_bound; linarith
        have h : S.card ≤ Nat.ceil (M + 1) := int_count_half_open (by linarith) h_len2 S hS
        have h9 : Nat.ceil (M + 1) = Nat.ceil M + 1 := by
          have h10 : ∀ (x : ℝ), 0 ≤ x → Nat.ceil (x + 1) = Nat.ceil x + 1 := by
            intro x hx
            exact Nat.ceil_add_one hx
          exact h10 M hM_nonneg
        rw [h9] at h
        exact h
      · -- c < 0
        have hc_neg : c < 0 := by
          have h_le : c ≤ 0 := by exact Std.not_lt.mp hc_pos
          exact lt_of_le_of_ne h_le hc0
        have hS : ∀ m ∈ S, c * ((j : ℝ) + 1) - 1 < (m : ℝ) ∧ (m : ℝ) ≤ c * (j : ℝ) := by
          intro m hm
          have h_m_in_cA : m ∈ I_cA := by
            have h : m ∈ K_cA := (Finset.mem_filter.mp hm).1
            rw [←hK_cA] <;> exact h
          have h_k_eq : k m = j := (Finset.mem_filter.mp hm).2
          have hxp := h_x_prop m h_m_in_cA
          have h1 : δ * (j : ℝ) ≤ x m := by
            have h2 : δ * (k m : ℝ) ≤ x m := by
              dsimp only [k]; have h3 : (k m : ℝ) ≤ x m / δ := Int.floor_le (x m / δ)
              have h4 : δ * (k m : ℝ) ≤ δ * (x m / δ) := by gcongr
              have h5 : δ * (x m / δ) = x m := by field_simp [hδ_pos.ne'] <;> ring
              rw [h5] at h4 <;> exact h4
            rw [h_k_eq] at h2 <;> exact h2
          have h2 : x m < δ * ((j : ℝ) + 1) := by
            have h3 : x m < δ * ((k m : ℝ) + 1) := by
              dsimp only [k]; have h4 : x m / δ < (k m : ℝ) + 1 := Int.lt_floor_add_one (x m / δ)
              have h5 : δ * (x m / δ) < δ * ((k m : ℝ) + 1) := by gcongr
              have h6 : δ * (x m / δ) = x m := by field_simp [hδ_pos.ne'] <;> ring
              rw [h6] at h5 <;> exact h5
            rw [h_k_eq] at h3 <;> exact h3
          have h3 : δ * (m : ℝ) ≤ c * (x m) := hxp.2.1
          have h4 : c * (x m) < δ * ((m : ℝ) + 1) := hxp.2.2
          have h5 : c * (x m) ≤ c * (δ * (j : ℝ)) := by
            exact mul_le_mul_of_nonpos_left h1 (by linarith)
          have h6 : c * (δ * ((j : ℝ) + 1)) < c * (x m) := by
            exact mul_lt_mul_of_neg_left h2 hc_neg
          constructor
          · nlinarith
          · nlinarith
        have h_len : c * (j : ℝ) - (c * ((j : ℝ) + 1) - 1) = |c| + 1 := by
          rw [abs_of_neg hc_neg] <;> ring
        have h_len2 : c * (j : ℝ) - (c * ((j : ℝ) + 1) - 1) ≤ M + 1 := by
          rw [h_len]; have h9 : |c| ≤ M := hc_bound; linarith
        have h : S.card ≤ Nat.ceil (M + 1) := int_count_half_open (by linarith) h_len2 S hS
        have h9 : Nat.ceil (M + 1) = Nat.ceil M + 1 := by
          have h10 : Nat.ceil (M + 1) = Nat.ceil M + 1 := by
            exact Nat.ceil_add_one hM_nonneg
          exact h10
        rw [h9] at h
        exact h
    have h_main_card : K_cA.card ≤ (Nat.ceil M + 1) * K_A.card :=
      WeakTwoEndsSumProduct.finset_card_le_mul_of_bounded_fibers h_k_in_A h_fiber
    have h_enc_cA : (I_cA.encard : ENNReal) = ↑K_cA.card := by
      exact_mod_cast Set.Finite.encard_eq_coe_toFinset_card h_fin_cA
    have h_enc_A : (I_A.encard : ENNReal) = ↑K_A.card := by
      exact_mod_cast Set.Finite.encard_eq_coe_toFinset_card h_fin_A
    have h1 : Nreal δ (scaleSet c A) = (I_cA.encard : ENNReal) := by
      have h := ProductLikeIncidence.realCoveringNumber_eq_card_ennreal hδ_pos h_bdd_cA
      have h' : Nreal δ (scaleSet c A) =
          ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy (scaleSet c A))) := by rfl
      rw [h'] <;> exact h
    have h2 : Nreal δ A = (I_A.encard : ENNReal) := by
      have h := ProductLikeIncidence.realCoveringNumber_eq_card_ennreal hδ_pos hA_bdd
      have h' : Nreal δ A =
          ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A)) := by rfl
      rw [h'] <;> exact h
    rw [h1, h2, h_enc_cA, h_enc_A]
    exact_mod_cast h_main_card

/-- Pointwise sector coordinate transformation on Euclidean points.

Note: The sector chart takes parameters `(U, V)` where the raw projection is
`U + x*V`. Since `affineProjection x` gives `p 0 * x + p 1 = p 1 + x * p 0`,
we pass `U = p 1` and `V = p 0`. -/
def chartSectorCoordPoint (i : Fin 4) (p : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  let c := chartSectorCoord i (p 1) (p 0)
  (WithLp.equiv 2 _).symm fun j => if j = 0 then c.1 else c.2

/-- **Set-level projection identity**.

The affine projection at direction `chartSectorT i x` of the sector-transformed
point set equals `chartSectorScalar i x` times the affine projection at direction
`x` of the original point set. -/
lemma chart_sector_projection_set (i : Fin 4) (x : ℝ)
    (h : chartSectorPred i x) (S : Set (EuclideanSpace ℝ (Fin 2))) :
    affineProjection (chartSectorT i x) (chartSectorCoordPoint i '' S) =
    scaleSet (chartSectorScalar i x) (affineProjection x S) := by
  ext z
  simp only [affineProjection, Set.mem_image, scaleSet]
  constructor
  · -- Forward: LHS → RHS
    rintro ⟨q, hq, h_eq1⟩
    rcases hq with ⟨p, hp, rfl⟩
    let c := chartSectorCoord i (p 1) (p 0)
    have hq1 : (chartSectorCoordPoint i p) 0 = c.1 := by
      simp [chartSectorCoordPoint, c] <;> rfl
    have hq2 : (chartSectorCoordPoint i p) 1 = c.2 := by
      simp [chartSectorCoordPoint, c] <;> rfl
    have h_main : (chartSectorCoordPoint i p) 0 * chartSectorT i x + (chartSectorCoordPoint i p) 1 =
        chartSectorScalar i x * (p 0 * x + p 1) := by
      rw [hq1, hq2]
      have h_id := chart_sector_projection_identity i x h (p 1) (p 0)
      ring_nf at h_id ⊢
      exact h_id
    have h_goal : chartSectorScalar i x * (p 0 * x + p 1) = z := by
      rw [←h_main]
      exact h_eq1
    exact ⟨p 0 * x + p 1, ⟨p, hp, by ring⟩, h_goal⟩
  · -- Backward: RHS → LHS
    rintro ⟨w, ⟨p, hp, h_w⟩, h_z⟩
    let q := chartSectorCoordPoint i p
    let c := chartSectorCoord i (p 1) (p 0)
    have hq1 : q 0 = c.1 := by simp [q, chartSectorCoordPoint, c] <;> rfl
    have hq2 : q 1 = c.2 := by simp [q, chartSectorCoordPoint, c] <;> rfl
    have h_main : q 0 * chartSectorT i x + q 1 = chartSectorScalar i x * (p 0 * x + p 1) := by
      rw [hq1, hq2]
      have h_id := chart_sector_projection_identity i x h (p 1) (p 0)
      ring_nf at h_id ⊢
      exact h_id
    have h_goal : q 0 * chartSectorT i x + q 1 = z := by
      calc
        q 0 * chartSectorT i x + q 1
          = chartSectorScalar i x * (p 0 * x + p 1) := h_main
        _ = chartSectorScalar i x * w := by rw [h_w]
        _ = z := h_z
    exact ⟨q, ⟨p, hp, rfl⟩, h_goal⟩

/-- **Four-sector projection covering preservation**.

For any sector `i` and direction `x` satisfying `chartSectorPred i x`, the
dyadic covering number of the affine projection of the sector-transformed set
is at most `2` times that of the original projection.

This follows from `|chartSectorScalar i x| ≤ 1` and the scalar covering bound. -/
lemma four_sector_projection_preservation {δ : ℝ} (hδ_pos : 0 < δ)
    {i : Fin 4} {x : ℝ} {S : Set (EuclideanSpace ℝ (Fin 2))}
    (h : chartSectorPred i x) (hS_bdd : Bornology.IsBounded S) :
    Nreal δ (affineProjection (chartSectorT i x) (chartSectorCoordPoint i '' S)) ≤
    (2 : ENNReal) * Nreal δ (affineProjection x S) := by
  have h_scalar_bound : |chartSectorScalar i x| ≤ 1 := chart_sector_scalar_bound i x h
  have h_set_eq : affineProjection (chartSectorT i x) (chartSectorCoordPoint i '' S) =
      scaleSet (chartSectorScalar i x) (affineProjection x S) :=
    chart_sector_projection_set i x h S
  have hA_bdd : Bornology.IsBounded (affineProjection x S) := by exact projectionSet.bounded x hS_bdd
  have h_main : Nreal δ (scaleSet (chartSectorScalar i x) (affineProjection x S)) ≤
      (Nat.ceil (1 : ℝ) + 1 : ENNReal) * Nreal δ (affineProjection x S) :=
    scalar_covering_upper hδ_pos (by norm_num) hA_bdd h_scalar_bound
  have h_simp : (Nat.ceil (1 : ℝ) + 1 : ENNReal) = (2 : ENNReal) := by norm_num
  rw [h_simp] at h_main
  rw [h_set_eq]
  exact h_main

end ProductLikeIncidence.FourSectorChart
