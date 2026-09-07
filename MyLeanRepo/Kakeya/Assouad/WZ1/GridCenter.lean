import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Grid center helpers for WZ1 anisotropic Frostman rescaling

Maps each point in the plane to the center of its grid cell of side length `rho`.
Provides closeness, separation, and idempotence lemmas.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Round each coordinate to the center of its grid cell of side length `rho`. -/
noncomputable def gridCenter (rho : ℝ) (p : Point2) : Point2 :=
  WithLp.toLp 2 fun i : Fin 2 => ((Int.floor (p i / rho) : ℝ) + 1 / 2) * rho

lemma gridCenter_apply (rho : ℝ) (p : Point2) (i : Fin 2) :
    gridCenter rho p i = ((Int.floor (p i / rho) : ℝ) + 1 / 2) * rho := by
  rfl

lemma point2_coord_le_norm (v : Point2) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  have h1 : ‖v‖ ^ 2 = ∑ j : Fin 2, |v j| ^ 2 := by
    have h2 : ‖v‖ = Real.sqrt (∑ j : Fin 2, |v j| ^ 2) := PiLp.norm_eq_of_L2 v
    rw [h2]
    have h3 : 0 ≤ ∑ j : Fin 2, |v j| ^ 2 := by positivity
    rw [Real.sq_sqrt h3]
  have h_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ |v j| ^ 2 := by
    intro j _
    positivity
  have h4 : |v i| ^ 2 ≤ ∑ j : Fin 2, |v j| ^ 2 :=
    Finset.single_le_sum h_nonneg (Finset.mem_univ i)
  have h5 : 0 ≤ ‖v‖ := by positivity
  have h6 : 0 ≤ |v i| := by positivity
  nlinarith

lemma gridCenter_coord_close (rho : ℝ) (hrho : 0 < rho) (p : Point2) (i : Fin 2) :
    |p i - gridCenter rho p i| ≤ rho / 2 := by
  set x : ℝ := p i / rho with hx
  have hfloor1 : (Int.floor x : ℝ) ≤ x := Int.floor_le x
  have hfloor2 : x < (Int.floor x : ℝ) + 1 := Int.lt_floor_add_one x
  have h_center : gridCenter rho p i = ((Int.floor x : ℝ) + 1 / 2) * rho :=
    gridCenter_apply rho p i
  rw [h_center]
  have h_eq : p i = x * rho := by
    rw [hx]
    field_simp [hrho.ne']
  rw [h_eq]
  have h' : x * rho - (((Int.floor x : ℝ) + 1 / 2) * rho) = (x - (Int.floor x : ℝ) - 1 / 2) * rho := by ring
  rw [h']
  have h_abs : |(x - (Int.floor x : ℝ) - 1 / 2) * rho| = |x - (Int.floor x : ℝ) - 1 / 2| * rho := by
    rw [abs_mul, abs_of_pos hrho]
  rw [h_abs]
  have h2 : |x - (Int.floor x : ℝ) - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have h3 : |x - (Int.floor x : ℝ) - 1 / 2| * rho ≤ (1 / 2 : ℝ) * rho :=
    mul_le_mul_of_nonneg_right h2 (by linarith)
  linarith

lemma gridCenter_rho_close (rho : ℝ) (hrho : 0 < rho) (p : Point2) :
    dist p (gridCenter rho p) ≤ rho := by
  have h1 : ∀ i : Fin 2, |(p - gridCenter rho p) i| ≤ rho / 2 := by
    intro i
    have h2 : (p - gridCenter rho p) i = p i - gridCenter rho p i := by rfl
    rw [h2]
    exact gridCenter_coord_close rho hrho p i
  have h_norm2 : ‖p - gridCenter rho p‖ ^ 2 = ∑ i : Fin 2, |(p - gridCenter rho p) i| ^ 2 := by
    have h5 : ‖p - gridCenter rho p‖ = Real.sqrt (∑ i : Fin 2, |(p - gridCenter rho p) i| ^ 2) :=
      PiLp.norm_eq_of_L2 (p - gridCenter rho p)
    rw [h5]
    have h6 : 0 ≤ ∑ i : Fin 2, |(p - gridCenter rho p) i| ^ 2 := by positivity
    rw [Real.sq_sqrt h6]
  have h3 : ∑ i : Fin 2, |(p - gridCenter rho p) i| ^ 2 ≤ ∑ _i : Fin 2, (rho / 2) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    have h4 : |(p - gridCenter rho p) i| ≤ rho / 2 := h1 i
    gcongr
  have h4 : ∑ _i : Fin 2, (rho / 2) ^ 2 = 2 * (rho / 2) ^ 2 := by
    simp [Finset.sum_const]
  have h5 : ‖p - gridCenter rho p‖ ^ 2 ≤ rho ^ 2 := by
    rw [h_norm2]
    rw [h4] at h3
    nlinarith
  have h6 : 0 ≤ ‖p - gridCenter rho p‖ := by positivity
  have h7 : 0 ≤ rho := by linarith
  have h8 : ‖p - gridCenter rho p‖ ≤ rho := by nlinarith
  rw [dist_eq_norm]
  exact h8

lemma gridCenter_separated (rho : ℝ) (hrho : 0 < rho) (p q : Point2)
    (h : gridCenter rho p ≠ gridCenter rho q) :
    rho ≤ dist (gridCenter rho p) (gridCenter rho q) := by
  have hne : ∃ i : Fin 2, gridCenter rho p i ≠ gridCenter rho q i := by
    by_contra h'
    have h_all : ∀ i, gridCenter rho p i = gridCenter rho q i := by
      simpa using h'
    have h_eq : gridCenter rho p = gridCenter rho q := by
      ext i
      exact h_all i
    exact h h_eq
  rcases hne with ⟨i, hi⟩
  set fp : ℤ := Int.floor (p i / rho) with hfp
  set fq : ℤ := Int.floor (q i / rho) with hfq
  have hdiff : fp ≠ fq := by
    intro h_eq
    have h_floors : Int.floor (p i / rho) = Int.floor (q i / rho) := by
      calc
        Int.floor (p i / rho) = fp := hfp.symm
        _ = fq := h_eq
        _ = Int.floor (q i / rho) := hfq
    have h9 : gridCenter rho p i = gridCenter rho q i := by
      rw [gridCenter_apply, gridCenter_apply, h_floors]
    exact hi h9
  have h10 : |(fp : ℝ) - (fq : ℝ)| ≥ 1 := by
    have h101 : fp - fq ≠ 0 := by
      intro h
      apply hdiff
      omega
    by_cases hpos : 0 < fp - fq
    · have hge : fp - fq ≥ 1 := by omega
      have hpos' : (0 : ℝ) ≤ (fp : ℝ) - (fq : ℝ) := by
        exact_mod_cast (show 0 ≤ fp - fq from by omega)
      rw [abs_of_nonneg hpos']
      exact_mod_cast hge
    · have hle : fp - fq ≤ -1 := by omega
      have hneg' : (fp : ℝ) - (fq : ℝ) ≤ 0 := by
        exact_mod_cast (show fp - fq ≤ 0 from by omega)
      rw [abs_of_nonpos hneg']
      have hreal : (fp : ℝ) - (fq : ℝ) ≤ -1 := by exact_mod_cast hle
      have h : -((fp : ℝ) - (fq : ℝ)) ≥ 1 := by linarith
      exact h
  have h11a : gridCenter rho p i = ((fp : ℝ) + 1 / 2) * rho := by
    rw [gridCenter_apply, hfp]
  have h11b : gridCenter rho q i = ((fq : ℝ) + 1 / 2) * rho := by
    rw [gridCenter_apply, hfq]
  have h11 : gridCenter rho p i - gridCenter rho q i = ((fp : ℝ) - (fq : ℝ)) * rho := by
    rw [h11a, h11b]; ring
  have h12 : |gridCenter rho p i - gridCenter rho q i| ≥ rho := by
    rw [h11]
    have h13 : |((fp : ℝ) - (fq : ℝ)) * rho| = |(fp : ℝ) - (fq : ℝ)| * rho := by
      rw [abs_mul, abs_of_pos hrho]
    rw [h13]
    have h14 : |(fp : ℝ) - (fq : ℝ)| * rho ≥ rho := by
      calc
        |(fp : ℝ) - (fq : ℝ)| * rho ≥ 1 * rho := by gcongr
        _ = rho := by ring
    exact h14
  have h14 : |(gridCenter rho p - gridCenter rho q) i| ≥ rho := by
    simpa using h12
  have h15 : |(gridCenter rho p - gridCenter rho q) i| ≤ ‖gridCenter rho p - gridCenter rho q‖ :=
    point2_coord_le_norm (gridCenter rho p - gridCenter rho q) i
  have h22 : rho ≤ ‖gridCenter rho p - gridCenter rho q‖ := by
    linarith
  rw [dist_eq_norm]
  exact h22

lemma gridCenter_idempotent (rho : ℝ) (hrho : 0 < rho) (p : Point2) :
    gridCenter rho (gridCenter rho p) = gridCenter rho p := by
  ext i
  set fp : ℤ := Int.floor (p i / rho) with hfp
  have h1 : (gridCenter rho p) i / rho = (fp : ℝ) + 1 / 2 := by
    rw [gridCenter_apply]
    field_simp [hrho.ne']
    ring
  have h2 : Int.floor ((gridCenter rho p) i / rho) = fp := by
    rw [h1]
    have h3 : (fp : ℝ) ≤ (fp : ℝ) + (1 / 2 : ℝ) := by norm_num
    have h4 : (fp : ℝ) + (1 / 2 : ℝ) < (fp : ℝ) + 1 := by norm_num
    have h5 : Int.floor ((fp : ℝ) + (1 / 2 : ℝ)) = fp := by
      rw [Int.floor_eq_iff]
      exact ⟨h3, h4⟩
    exact h5
  have h4 : gridCenter rho (gridCenter rho p) i = ((Int.floor ((gridCenter rho p) i / rho) : ℝ) + 1 / 2) * rho :=
    gridCenter_apply rho (gridCenter rho p) i
  rw [h4, h2]
  have h5 : gridCenter rho p i = ((fp : ℝ) + 1 / 2) * rho := by
    rw [gridCenter_apply, hfp]
  exact h5.symm

end Kakeya.Assouad
