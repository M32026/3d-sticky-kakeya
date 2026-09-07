import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedCellStatements

/-!
WZ1 Lemma 23 spatial discretization: snap genuine shaded representatives to
canonical cell centers, recover exact y/z coincidences from grid indices, and
control the resulting local/global grain-coordinate errors.
-/

namespace Kakeya.Assouad

private lemma wz1Lemma23_abs_add (a b : ℝ) :
    |a + b| ≤ |a| + |b| := by
  by_cases h : 0 ≤ a + b
  · rw [abs_of_nonneg h]
    have h1 : a ≤ |a| := by
      cases' abs_cases a with h2 h2 <;> linarith
    have h2 : b ≤ |b| := by
      cases' abs_cases b with h3 h3 <;> linarith
    linarith
  · rw [abs_of_neg (by linarith)]
    have h1 : -a ≤ |a| := by
      cases' abs_cases a with h2 h2 <;> linarith
    have h2 : -b ≤ |b| := by
      cases' abs_cases b with h3 h3 <;> linarith
    linarith

private lemma wz1Lemma23_floor_coord_bound
    {s x : ℝ} {k : ℤ} (hs_pos : 0 < s)
    (h : ⌊x / s⌋ = k) :
    |x - ((k : ℝ) + 1 / 2) * s| ≤ s / 2 := by
  have h1 : (k : ℝ) ≤ x / s := by
    rw [← h]
    exact Int.floor_le _
  have h2 : x / s < (k : ℝ) + 1 := by
    rw [← h]
    exact Int.lt_floor_add_one _
  have h3 : (k : ℝ) * s ≤ x := by
    have h4 : (k : ℝ) * s ≤ (x / s) * s := by gcongr
    have h5 : (x / s) * s = x := by
      field_simp [hs_pos.ne']
    rw [h5] at h4
    exact h4
  have h6 : x < ((k : ℝ) + 1) * s := by
    have h7 : (x / s) * s < ((k : ℝ) + 1) * s := by gcongr
    have h8 : (x / s) * s = x := by
      field_simp [hs_pos.ne']
    rw [h8] at h7
    exact h7
  rw [abs_le]
  constructor <;> linarith

private lemma wz1Lemma23_gridSide_eq (rho : ℝ) :
    gridSide (rho / 2) = rho / Real.sqrt 3 := by
  simp [gridSide]
  ring

private lemma wz1Lemma23_dist_from_coord_bounds
    {p c : Point3} {s : ℝ} (hs_nonneg : 0 ≤ s)
    (h : ∀ i : Fin 3, |p i - c i| ≤ s / 2) :
    dist p c ≤ Real.sqrt 3 * (s / 2) := by
  have h_dist_sq :
      dist p c ^ 2 = ∑ i : Fin 3, (p i - c i) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    simp [Real.dist_eq]
  have h_each :
      ∀ i : Fin 3, (p i - c i) ^ 2 ≤ (s / 2) ^ 2 := by
    intro i
    calc
      (p i - c i) ^ 2 = |p i - c i| ^ 2 := by rw [sq_abs]
      _ ≤ (s / 2) ^ 2 := by
        nlinarith [h i, abs_nonneg (p i - c i)]
  have h_sum :
      ∑ i : Fin 3, (p i - c i) ^ 2 ≤
        3 * (s / 2) ^ 2 := by
    have h' :
        ∑ i : Fin 3, (p i - c i) ^ 2 ≤
          ∑ i : Fin 3, (s / 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact h_each i
    simpa [Fin.sum_univ_succ] using h'
  have h9 :
      (Real.sqrt 3 * (s / 2)) ^ 2 =
        3 * (s / 2) ^ 2 := by
    calc
      (Real.sqrt 3 * (s / 2)) ^ 2 =
          (Real.sqrt 3) ^ 2 * (s / 2) ^ 2 := by ring
      _ = 3 * (s / 2) ^ 2 := by
        rw [Real.sq_sqrt (by norm_num)]
  have h10 :
      dist p c ^ 2 ≤ (Real.sqrt 3 * (s / 2)) ^ 2 := by
    rw [h_dist_sq, h9]
    exact h_sum
  have h11 : 0 ≤ dist p c := dist_nonneg
  have h12 : 0 ≤ Real.sqrt 3 * (s / 2) := by
    have h13 : 0 ≤ s / 2 := by linarith
    positivity
  nlinarith

theorem wz1_lemma23_snapped_cell_geometry :
    WZ1Lemma23SnappedCellGeometryStatement := by
  intro rho hrho hrho_le_one
  set s : ℝ := gridSide (rho / 2) with hs
  have hs_pos : 0 < s := by
    simp [hs, gridSide]
    positivity
  have h_s_eq : s = rho / Real.sqrt 3 := by
    simpa [hs] using wz1Lemma23_gridSide_eq rho
  have h_sqrt3_ge_one : (1 : ℝ) ≤ Real.sqrt 3 := by
    have h : (1 : ℝ) ^ 2 ≤ (3 : ℝ) := by norm_num
    exact Real.le_sqrt_of_sq_le h
  have h_half_s_le : s / 2 ≤ rho / 2 := by
    rw [h_s_eq]
    have h : rho / Real.sqrt 3 ≤ rho := by
      apply div_le_self
      · linarith
      · linarith [h_sqrt3_ge_one]
    linarith
  have h_sqrt3_times_half_s :
      Real.sqrt 3 * (s / 2) = rho / 2 := by
    rw [h_s_eq]
    have hsqrt3_pos : 0 < Real.sqrt 3 :=
      Real.sqrt_pos.mpr (by norm_num)
    field_simp [hsqrt3_pos.ne']
  have h_floor_int_half :
      ∀ k : ℤ, Int.floor ((k : ℝ) + 1 / 2) = k := by
    intro k
    rw [Int.floor_eq_iff]
    norm_num <;> omega
  have h_abs_add :
      ∀ a b : ℝ, |a + b| ≤ |a| + |b| :=
    fun a b => wz1Lemma23_abs_add a b
  have h_coord_norm :
      ∀ (p : Point3) (i : Fin 3), |p i| ≤ ‖p‖ := by
    intro p i
    have h1 : (p i) ^ 2 ≤ ∑ j : Fin 3, (p j) ^ 2 := by
      have h_nonneg :
          ∀ j ∈ (Finset.univ : Finset (Fin 3)),
            0 ≤ (p j) ^ 2 := by
        intro j _
        positivity
      exact Finset.single_le_sum h_nonneg (Finset.mem_univ i)
    have h2 : ‖p‖ = Real.sqrt (∑ j : Fin 3, (p j) ^ 2) := by
      rw [PiLp.norm_eq_of_L2]
      congr with j
      simp [Real.norm_eq_abs, sq_abs]
    rw [h2]
    have h3 : |p i| = Real.sqrt ((p i) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h3]
    exact Real.sqrt_le_sqrt h1
  have h_part1 :
      ∀ idx : ℤ × ℤ × ℤ,
        wz1Lemma23CellIndex rho
            (wz1Lemma23CellCenter rho idx) = idx := by
    intro idx
    have h_center0 :
        (wz1Lemma23CellCenter rho idx) 0 =
          ((idx.1 : ℝ) + 1 / 2) * s := by
      simp [wz1Lemma23CellCenter, point3, hs]
    have h_center1 :
        (wz1Lemma23CellCenter rho idx) 1 =
          ((idx.2.1 : ℝ) + 1 / 2) * s := by
      simp [wz1Lemma23CellCenter, point3, hs]
    have h_center2 :
        (wz1Lemma23CellCenter rho idx) 2 =
          ((idx.2.2 : ℝ) + 1 / 2) * s := by
      simp [wz1Lemma23CellCenter, point3, hs]
    have h_floor0 :
        ⌊(wz1Lemma23CellCenter rho idx) 0 / s⌋ = idx.1 := by
      rw [h_center0]
      have hdiv :
          (((idx.1 : ℝ) + 1 / 2) * s) / s =
            (idx.1 : ℝ) + 1 / 2 := by
        field_simp [hs_pos.ne']
      rw [hdiv]
      exact h_floor_int_half idx.1
    have h_floor1 :
        ⌊(wz1Lemma23CellCenter rho idx) 1 / s⌋ =
          idx.2.1 := by
      rw [h_center1]
      have hdiv :
          (((idx.2.1 : ℝ) + 1 / 2) * s) / s =
            (idx.2.1 : ℝ) + 1 / 2 := by
        field_simp [hs_pos.ne']
      rw [hdiv]
      exact h_floor_int_half idx.2.1
    have h_floor2 :
        ⌊(wz1Lemma23CellCenter rho idx) 2 / s⌋ =
          idx.2.2 := by
      rw [h_center2]
      have hdiv :
          (((idx.2.2 : ℝ) + 1 / 2) * s) / s =
            (idx.2.2 : ℝ) + 1 / 2 := by
        field_simp [hs_pos.ne']
      rw [hdiv]
      exact h_floor_int_half idx.2.2
    have h_formula :
        wz1Lemma23CellIndex rho
            (wz1Lemma23CellCenter rho idx) =
          (⌊(wz1Lemma23CellCenter rho idx) 0 / s⌋,
            ⌊(wz1Lemma23CellCenter rho idx) 1 / s⌋,
            ⌊(wz1Lemma23CellCenter rho idx) 2 / s⌋) := by
      simp [wz1Lemma23CellIndex, rhoGridIndex, gridIndex, hs]
    rw [h_formula, h_floor0, h_floor1, h_floor2]
  have h_part2 :
      ∀ (idx : ℤ × ℤ × ℤ) (p : Point3),
        wz1Lemma23CellIndex rho p = idx →
          (∀ i : Fin 3,
            |p i - (wz1Lemma23CellCenter rho idx) i| ≤
              rho / 2) ∧
          dist p (wz1Lemma23CellCenter rho idx) ≤
            rho / 2 := by
    intro idx p h
    let c := wz1Lemma23CellCenter rho idx
    have h0 : ⌊p 0 / s⌋ = idx.1 := by
      simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex, hs]
        using congr_arg Prod.fst h
    have h1 : ⌊p 1 / s⌋ = idx.2.1 := by
      simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex, hs]
        using congr_arg (fun x : ℤ × ℤ × ℤ => x.2.1) h
    have h2 : ⌊p 2 / s⌋ = idx.2.2 := by
      simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex, hs]
        using congr_arg (fun x : ℤ × ℤ × ℤ => x.2.2) h
    have hc0 : c 0 = ((idx.1 : ℝ) + 1 / 2) * s := by
      simp [c, wz1Lemma23CellCenter, point3, hs]
    have hc1 : c 1 = ((idx.2.1 : ℝ) + 1 / 2) * s := by
      simp [c, wz1Lemma23CellCenter, point3, hs]
    have hc2 : c 2 = ((idx.2.2 : ℝ) + 1 / 2) * s := by
      simp [c, wz1Lemma23CellCenter, point3, hs]
    have hb0 : |p 0 - c 0| ≤ s / 2 := by
      rw [hc0]
      exact wz1Lemma23_floor_coord_bound hs_pos h0
    have hb1 : |p 1 - c 1| ≤ s / 2 := by
      rw [hc1]
      exact wz1Lemma23_floor_coord_bound hs_pos h1
    have hb2 : |p 2 - c 2| ≤ s / 2 := by
      rw [hc2]
      exact wz1Lemma23_floor_coord_bound hs_pos h2
    have h_coord_s :
        ∀ i : Fin 3, |p i - c i| ≤ s / 2 := by
      intro i
      fin_cases i <;> tauto
    have h_coord_rho :
        ∀ i : Fin 3, |p i - c i| ≤ rho / 2 := by
      intro i
      exact (h_coord_s i).trans h_half_s_le
    have h_dist : dist p c ≤ rho / 2 := by
      have h' :
          dist p c ≤ Real.sqrt 3 * (s / 2) :=
        wz1Lemma23_dist_from_coord_bounds
          (by linarith) h_coord_s
      rw [h_sqrt3_times_half_s] at h'
      exact h'
    exact ⟨h_coord_rho, h_dist⟩
  have h_part3 :
      ∀ first second : ℤ × ℤ × ℤ,
        first.2.1 = second.2.1 →
          (wz1Lemma23CellCenter rho first) 1 =
            (wz1Lemma23CellCenter rho second) 1 := by
    intro first second h
    simp [wz1Lemma23CellCenter, point3, h]
  have h_part4 :
      ∀ first second : ℤ × ℤ × ℤ,
        first.2.2 = second.2.2 →
          (wz1Lemma23CellCenter rho first) 2 =
            (wz1Lemma23CellCenter rho second) 2 := by
    intro first second h
    simp [wz1Lemma23CellCenter, point3, h]
  have h_part5 :
      ∀ (f g : ℝ → ℝ),
        LipschitzOnWith 1 f Set.univ →
        LipschitzOnWith 4 g Set.univ →
        (∀ z, |f z| ≤ 3) →
        (∀ y, |g y| ≤ 5) →
        ∀ p : Point3, ‖p‖ ≤ 1 →
          |wz1Lemma23GlobalCoordinate f p -
              wz1Lemma23GlobalCoordinate f
                (wz1Lemma23Snap rho p)| ≤ 4 * rho ∧
          |wz1Lemma23LocalCoordinate g p -
              wz1Lemma23LocalCoordinate g
                (wz1Lemma23Snap rho p)| ≤ 8 * rho := by
    intro f g hf_lip hg_lip hf_bound hg_bound p hp_norm
    let q := wz1Lemma23Snap rho p
    let idx := wz1Lemma23CellIndex rho p
    have h_idx : wz1Lemma23CellIndex rho p = idx := rfl
    have h_coord :
        ∀ i : Fin 3, |p i - q i| ≤ rho / 2 :=
      (h_part2 idx p h_idx).1
    have h_pi_bound : ∀ i : Fin 3, |p i| ≤ 1 := by
      intro i
      have h : |p i| ≤ ‖p‖ := h_coord_norm p i
      linarith
    have h_qi_bound : ∀ i : Fin 3, |q i| ≤ 3 / 2 := by
      intro i
      have h1 : |q i| ≤ |p i| + |q i - p i| := by
        calc
          |q i| = |p i + (q i - p i)| := by ring_nf
          _ ≤ |p i| + |q i - p i| :=
            h_abs_add (p i) (q i - p i)
      have h2 : |q i - p i| = |p i - q i| := by
        rw [abs_sub_comm]
      rw [h2] at h1
      linarith [h_pi_bound i, h_coord i, hrho_le_one]
    have hf_lip' :
        ∀ x y : ℝ, |f x - f y| ≤ |x - y| := by
      intro x y
      have h := hf_lip.dist_le_mul x (by simp) y (by simp)
      simpa [Real.dist_eq] using h
    have hg_lip' :
        ∀ x y : ℝ, |g x - g y| ≤ 4 * |x - y| := by
      intro x y
      have h := hg_lip.dist_le_mul x (by simp) y (by simp)
      simpa [Real.dist_eq] using h
    have h_global :
        |wz1Lemma23GlobalCoordinate f p -
          wz1Lemma23GlobalCoordinate f q| ≤ 4 * rho := by
      simp only [wz1Lemma23GlobalCoordinate]
      set a := p 0 - q 0 with ha
      set b := f (p 2) * p 1 - f (q 2) * q 1 with hb
      have h_main : |a + b| ≤ |a| + |b| :=
        h_abs_add a b
      have h_b_split :
          |b| ≤
            |f (p 2)| * |p 1 - q 1| +
              |f (p 2) - f (q 2)| * |q 1| := by
        have h_eq :
            b =
              f (p 2) * (p 1 - q 1) +
                (f (p 2) - f (q 2)) * q 1 := by
          simp [hb]
          ring
        rw [h_eq]
        have h4 :=
          h_abs_add
            (f (p 2) * (p 1 - q 1))
            ((f (p 2) - f (q 2)) * q 1)
        rw [abs_mul, abs_mul] at h4
        exact h4
      have h1 : |a| ≤ rho / 2 := by
        simpa [ha] using h_coord 0
      have h2 :
          |f (p 2)| * |p 1 - q 1| ≤ 3 * (rho / 2) := by
        gcongr
        · exact hf_bound (p 2)
        · exact h_coord 1
      have h3 :
          |f (p 2) - f (q 2)| * |q 1| ≤
            (rho / 2) * (3 / 2) := by
        calc
          |f (p 2) - f (q 2)| * |q 1| ≤
              |p 2 - q 2| * |q 1| := by
            exact mul_le_mul_of_nonneg_right
              (hf_lip' (p 2) (q 2)) (abs_nonneg _)
          _ ≤ (rho / 2) * (3 / 2) := by
            gcongr
            · exact h_coord 2
            · exact h_qi_bound 1
      have h_bound :
          |a + b| ≤
            rho / 2 +
              (3 * (rho / 2) + (rho / 2) * (3 / 2)) := by
        calc
          |a + b| ≤ |a| + |b| := h_main
          _ ≤
              |a| +
                (|f (p 2)| * |p 1 - q 1| +
                  |f (p 2) - f (q 2)| * |q 1|) := by
            exact add_le_add_right h_b_split |a|
          _ ≤
              rho / 2 +
                (3 * (rho / 2) + (rho / 2) * (3 / 2)) := by
            gcongr
      have h_final :
          rho / 2 +
              (3 * (rho / 2) + (rho / 2) * (3 / 2)) =
            11 * rho / 4 := by ring
      rw [h_final] at h_bound
      have h_eq :
          a + b =
            p 0 + f (p 2) * p 1 -
              (q 0 + f (q 2) * q 1) := by
        simp [ha, hb]
        ring
      rw [h_eq] at h_bound
      exact h_bound.trans (by linarith)
    have h_local :
        |wz1Lemma23LocalCoordinate g p -
          wz1Lemma23LocalCoordinate g q| ≤ 8 * rho := by
      simp only [wz1Lemma23LocalCoordinate]
      set a := p 0 - q 0 with ha
      set b := g (p 1) * p 2 - g (q 1) * q 2 with hb
      have h_main : |a + b| ≤ |a| + |b| :=
        h_abs_add a b
      have h_b_split :
          |b| ≤
            |g (p 1)| * |p 2 - q 2| +
              |g (p 1) - g (q 1)| * |q 2| := by
        have h_eq :
            b =
              g (p 1) * (p 2 - q 2) +
                (g (p 1) - g (q 1)) * q 2 := by
          simp [hb]
          ring
        rw [h_eq]
        have h4 :=
          h_abs_add
            (g (p 1) * (p 2 - q 2))
            ((g (p 1) - g (q 1)) * q 2)
        rw [abs_mul, abs_mul] at h4
        exact h4
      have h1 : |a| ≤ rho / 2 := by
        simpa [ha] using h_coord 0
      have h2 :
          |g (p 1)| * |p 2 - q 2| ≤
            5 * (rho / 2) := by
        gcongr
        · exact hg_bound (p 1)
        · exact h_coord 2
      have h3 :
          |g (p 1) - g (q 1)| * |q 2| ≤
            4 * (rho / 2) * (3 / 2) := by
        calc
          |g (p 1) - g (q 1)| * |q 2| ≤
              (4 * |p 1 - q 1|) * |q 2| := by
            gcongr
            exact hg_lip' (p 1) (q 1)
          _ ≤ 4 * (rho / 2) * (3 / 2) := by
            gcongr
            · exact h_coord 1
            · exact h_qi_bound 2
      have h_bound :
          |a + b| ≤
            rho / 2 +
              (5 * (rho / 2) +
                4 * (rho / 2) * (3 / 2)) := by
        calc
          |a + b| ≤ |a| + |b| := h_main
          _ ≤
              |a| +
                (|g (p 1)| * |p 2 - q 2| +
                  |g (p 1) - g (q 1)| * |q 2|) := by
            exact add_le_add_right h_b_split |a|
          _ ≤
              rho / 2 +
                (5 * (rho / 2) +
                  4 * (rho / 2) * (3 / 2)) := by
            gcongr
      have h_final :
          rho / 2 +
              (5 * (rho / 2) +
                4 * (rho / 2) * (3 / 2)) =
            6 * rho := by ring
      rw [h_final] at h_bound
      have h_eq :
          a + b =
            p 0 + g (p 1) * p 2 -
              (q 0 + g (q 1) * q 2) := by
        simp [ha, hb]
        ring
      rw [h_eq] at h_bound
      exact h_bound.trans (by linarith)
    exact ⟨h_global, h_local⟩
  exact ⟨h_part1, h_part2, h_part3, h_part4, h_part5⟩

/--
The global snapped-coordinate estimate only needs the literal paper crop's
coordinate bounds.  It does not require the stronger Euclidean unit-ball
containment used by the historical bundled statement.
-/
theorem wz1Lemma23_globalCoordinate_snap_of_coord_bound
    {rho : ℝ} (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (f : ℝ → ℝ)
    (hf : LipschitzOnWith 1 f Set.univ)
    (hf_bound : ∀ z, |f z| ≤ 3)
    (point : Point3)
    (hcoordPoint : ∀ coordinate : Fin 3, |point coordinate| ≤ 1) :
    |wz1Lemma23GlobalCoordinate f point -
        wz1Lemma23GlobalCoordinate f (wz1Lemma23Snap rho point)| ≤
      4 * rho := by
  let snapped := wz1Lemma23Snap rho point
  let idx := wz1Lemma23CellIndex rho point
  have hcoord :
      ∀ coordinate : Fin 3,
        |point coordinate - snapped coordinate| ≤ rho / 2 :=
    ((wz1_lemma23_snapped_cell_geometry rho hrho hrho_one).2.1
      idx point rfl).1
  have hsnapped :
      ∀ coordinate : Fin 3, |snapped coordinate| ≤ 3 / 2 := by
    intro coordinate
    have htriangle :
        |snapped coordinate| ≤
          |point coordinate| + |snapped coordinate - point coordinate| := by
      calc
        |snapped coordinate| =
            |point coordinate +
              (snapped coordinate - point coordinate)| := by ring_nf
        _ ≤ |point coordinate| +
              |snapped coordinate - point coordinate| := abs_add_le _ _
    rw [abs_sub_comm] at htriangle
    linarith [hcoordPoint coordinate, hcoord coordinate]
  have hf_lip :
      ∀ first second : ℝ, |f first - f second| ≤ |first - second| := by
    intro first second
    have h := hf.dist_le_mul first (by simp) second (by simp)
    simpa [Real.dist_eq] using h
  simp only [wz1Lemma23GlobalCoordinate]
  let firstError := point 0 - snapped 0
  let secondError :=
    f (point 2) * point 1 - f (snapped 2) * snapped 1
  have hsecond :
      |secondError| ≤
        |f (point 2)| * |point 1 - snapped 1| +
          |f (point 2) - f (snapped 2)| * |snapped 1| := by
    have heq :
        secondError =
          f (point 2) * (point 1 - snapped 1) +
            (f (point 2) - f (snapped 2)) * snapped 1 := by
      simp [secondError]
      ring
    rw [heq]
    calc
      |f (point 2) * (point 1 - snapped 1) +
          (f (point 2) - f (snapped 2)) * snapped 1|
          ≤ |f (point 2) * (point 1 - snapped 1)| +
              |(f (point 2) - f (snapped 2)) * snapped 1| :=
            abs_add_le _ _
      _ = |f (point 2)| * |point 1 - snapped 1| +
            |f (point 2) - f (snapped 2)| * |snapped 1| := by
          rw [abs_mul, abs_mul]
  have hfirst : |firstError| ≤ rho / 2 := by
    simpa [firstError] using hcoord 0
  have htermOne :
      |f (point 2)| * |point 1 - snapped 1| ≤ 3 * (rho / 2) := by
    gcongr
    · exact hf_bound (point 2)
    · exact hcoord 1
  have htermTwo :
      |f (point 2) - f (snapped 2)| * |snapped 1| ≤
        (rho / 2) * (3 / 2) := by
    calc
      |f (point 2) - f (snapped 2)| * |snapped 1|
          ≤ |point 2 - snapped 2| * |snapped 1| := by
        exact mul_le_mul_of_nonneg_right
          (hf_lip (point 2) (snapped 2)) (abs_nonneg _)
      _ ≤ (rho / 2) * (3 / 2) := by
        gcongr
        · exact hcoord 2
        · exact hsnapped 1
  have hsum :
      |firstError + secondError| ≤ 11 * rho / 4 := by
    calc
      |firstError + secondError| ≤ |firstError| + |secondError| :=
        abs_add_le _ _
      _ ≤ |firstError| +
          (|f (point 2)| * |point 1 - snapped 1| +
            |f (point 2) - f (snapped 2)| * |snapped 1|) := by
        gcongr
      _ ≤ rho / 2 + (3 * (rho / 2) + (rho / 2) * (3 / 2)) := by
        gcongr
      _ = 11 * rho / 4 := by ring
  have heq :
      firstError + secondError =
        point 0 + f (point 2) * point 1 -
          (snapped 0 + f (snapped 2) * snapped 1) := by
    simp [firstError, secondError]
    ring
  rw [heq] at hsum
  exact hsum.trans (by linarith)

end Kakeya.Assouad
