import MyLeanRepo.Kakeya.Assouad.Statements

/-!
WZ Lemma 8 rediscretization: quantitatively invert the exact affine transport
of the four vertical-chart line parameters.

The map is linear in `(a,b,c,d)`.  Writing `L = d-c`, `mid = c+L/2`,
`gmid = g(mid)`, the transformed differences are

    Δd' = (m L² / 4) Δd
    Δc' = (L / 2) (Δc + gmid Δd)
    Δb' = (m L / 2) (Δb + mid Δd)
    Δa' = Δa + gmid Δb + mid (Δc + gmid Δd)

Inverting and using `|gmid| ≤ 1`, `|mid| ≤ 1`, `m ≤ 1`, `L ≤ 1` gives
each source difference bounded by `9r / (m L²)`, well within the stated
`100r / (m L²)`.
-/

namespace Kakeya.Assouad

theorem anisotropic_tube_params_inverse_cluster :
    AnisotropicTubeParamsInverseClusterStatement := by
  intro g c d m r hcd hdc_le1 hwindow hm_pos hm_le1 hgmid_input hr p q
        ha' hb' hc' hd'
  set L : ℝ := d - c with hL
  set mid : ℝ := c + L / 2 with hmid
  set gmid : ℝ := g mid with hgmid_eq
  set K : ℝ := m * L / 2 with hK
  set C : ℝ := L / 2 with hC
  set D : ℝ := m * L^2 / 4 with hD

  have hL_pos : 0 < L := by linarith
  have hK_pos : 0 < K := by positivity
  have hC_pos : 0 < C := by positivity
  have hD_pos : 0 < D := by positivity
  have hgmid_abs : |gmid| ≤ 1 := by
    simpa [hgmid_eq] using hgmid_input
  have h_denom_pos : 0 < m * L^2 := by positivity

  have hmid_abs : |mid| ≤ 1 := by
    have hc1 : -1 ≤ c := (hwindow ⟨by linarith, by linarith⟩).1
    have hd1 : d ≤ 1 := (hwindow ⟨by linarith, by linarith⟩).2
    have h5 : -1 ≤ mid := by
      simp only [hmid] <;> linarith
    have h6 : mid ≤ 1 := by
      simp only [hmid] <;> linarith
    exact abs_le.mpr ⟨h5, h6⟩

  set da : ℝ := p.a - q.a with hda
  set db : ℝ := p.b - q.b with hdb
  set dc : ℝ := p.c - q.c with hdc
  set dd : ℝ := p.d - q.d with hdd

  set ra' : ℝ := (anisotropicTubeParams g c d m p).a - (anisotropicTubeParams g c d m q).a with hra'
  set rb' : ℝ := (anisotropicTubeParams g c d m p).b - (anisotropicTubeParams g c d m q).b with hrb'
  set rc' : ℝ := (anisotropicTubeParams g c d m p).c - (anisotropicTubeParams g c d m q).c with hrc'
  set rd' : ℝ := (anisotropicTubeParams g c d m p).d - (anisotropicTubeParams g c d m q).d with hrd'

  -- Component-wise formulas
  have hPd_d : (anisotropicTubeParams g c d m p).d = D * p.d := by
    simp only [anisotropicTubeParams, hD, hL] <;> ring
  have hQd_d : (anisotropicTubeParams g c d m q).d = D * q.d := by
    simp only [anisotropicTubeParams, hD, hL] <;> ring
  have hPd_c : (anisotropicTubeParams g c d m p).c = C * (p.c + gmid * p.d) := by
    simp only [anisotropicTubeParams, hC, hL, hgmid_eq, hmid] <;> ring
  have hQd_c : (anisotropicTubeParams g c d m q).c = C * (q.c + gmid * q.d) := by
    simp only [anisotropicTubeParams, hC, hL, hgmid_eq, hmid] <;> ring
  have hPd_b : (anisotropicTubeParams g c d m p).b = K * (p.b + mid * p.d) := by
    simp only [anisotropicTubeParams, hK, hL, hmid] <;> ring
  have hQd_b : (anisotropicTubeParams g c d m q).b = K * (q.b + mid * q.d) := by
    simp only [anisotropicTubeParams, hK, hL, hmid] <;> ring
  have hPd_a : (anisotropicTubeParams g c d m p).a =
      p.a + gmid * p.b + mid * (p.c + gmid * p.d) := by
    simp only [anisotropicTubeParams, hmid, hgmid_eq] <;> ring
  have hQd_a : (anisotropicTubeParams g c d m q).a =
      q.a + gmid * q.b + mid * (q.c + gmid * q.d) := by
    simp only [anisotropicTubeParams, hmid, hgmid_eq] <;> ring

  -- Difference formulas
  have hdd' : rd' = D * dd := by
    simp only [hrd', hdd]
    rw [hPd_d, hQd_d] <;> ring
  have hdc' : rc' = C * (dc + gmid * dd) := by
    simp only [hrc', hdc, hdd]
    rw [hPd_c, hQd_c] <;> ring
  have hdb' : rb' = K * (db + mid * dd) := by
    simp only [hrb', hdb, hdd]
    rw [hPd_b, hQd_b] <;> ring
  have hda' : ra' = da + gmid * db + mid * (dc + gmid * dd) := by
    simp only [hra', hda, hdb, hdc, hdd]
    rw [hPd_a, hQd_a] <;> ring

  -- Inverse formulas
  have hdd_inv : dd = rd' / D := by
    rw [hdd'] <;> field_simp [hD_pos.ne'] <;> ring
  have hsum_c : dc + gmid * dd = rc' / C := by
    rw [hdc'] <;> field_simp [hC_pos.ne'] <;> ring
  have hdc_inv : dc = rc' / C - gmid * dd := by
    linarith [hsum_c]
  have hsum_b : db + mid * dd = rb' / K := by
    rw [hdb'] <;> field_simp [hK_pos.ne'] <;> ring
  have hdb_inv : db = rb' / K - mid * dd := by
    linarith [hsum_b]
  have hda_inv : da = ra' - gmid * db - mid * (rc' / C) := by
    rw [hda', hsum_c] <;> ring

  -- Helper: triangle inequality
  have h_abs_add : ∀ (x y : ℝ), |x + y| ≤ |x| + |y| := by
    intro x y
    have h1 : -|x| ≤ x := neg_abs_le x
    have h2 : x ≤ |x| := le_abs_self x
    have h3 : -|y| ≤ y := neg_abs_le y
    have h4 : y ≤ |y| := le_abs_self y
    have h5 : -(|x| + |y|) ≤ x + y := by linarith
    have h6 : x + y ≤ |x| + |y| := by linarith
    exact abs_le.mpr ⟨h5, h6⟩

  -- Basic inequalities
  have hL_nonneg : 0 ≤ L := by linarith
  have hL2_le_L : L^2 ≤ L := by
    have h : L ≤ 1 := hdc_le1
    have h' : L * L ≤ L * 1 := mul_le_mul_of_nonneg_left h hL_nonneg
    have h'' : L^2 = L * L := by ring
    rw [h'']
    simpa using h'
  have h_mL_le1 : m * L ≤ 1 := by
    have h1 : m ≤ 1 := hm_le1
    have h2 : m * L ≤ 1 * L := by gcongr
    have h3 : 1 * L = L := by ring
    rw [h3] at h2
    linarith
  have h_mL2_le_mL : m * L^2 ≤ m * L := by
    have h : L^2 ≤ L := hL2_le_L
    have h' : 0 ≤ m := by linarith
    exact mul_le_mul_of_nonneg_left h h'
  have h_mL2_le1 : m * L^2 ≤ 1 := by
    calc m * L^2 ≤ m * L := h_mL2_le_mL
      _ ≤ 1 := h_mL_le1

  -- Bound on dd
  have h_dd_bound : |dd| ≤ 4 * r / (m * L^2) := by
    rw [hdd_inv]
    have h1 : |rd' / D| = |rd'| / D := by
      rw [abs_div, abs_of_pos hD_pos]
    rw [h1]
    have h2 : |rd'| ≤ r := hd'
    have h3 : |rd'| / D ≤ r / D := by gcongr
    have h4 : r / D = 4 * r / (m * L^2) := by
      simp only [hD, hL] <;> field_simp [hm_pos.ne', hL_pos.ne'] <;> ring
    rw [h4] at h3
    exact h3

  -- 2*r/L ≤ 2*r/(m*L^2) since m*L^2 ≤ L
  have h_mL2_le_L : m * L^2 ≤ L := by
    calc m * L^2 ≤ m * L := h_mL2_le_mL
      _ ≤ L := by
        have h : m * L ≤ L := by
          have h1 : m ≤ 1 := hm_le1
          have h2 : 0 ≤ L := hL_nonneg
          have h3 : m * L ≤ 1 * L := by gcongr
          simpa using h3
        exact h
  have h2L_le : 2 * r / L ≤ 2 * r / (m * L^2) := by
    exact div_le_div_of_nonneg_left (by linarith) h_denom_pos h_mL2_le_L

  -- 2*r/(m*L) ≤ 2*r/(m*L^2) since L ≤ 1
  have h2mL_le : 2 * r / (m * L) ≤ 2 * r / (m * L^2) := by
    have h_ineq : m * L^2 ≤ m * L := h_mL2_le_mL
    exact div_le_div_of_nonneg_left (by linarith) h_denom_pos h_ineq

  -- r ≤ r/(m*L^2) since m*L^2 ≤ 1
  have h_r_le : r ≤ r / (m * L^2) := by
    have h : r / 1 ≤ r / (m * L^2) := by
      exact div_le_div_of_nonneg_left hr h_denom_pos h_mL2_le1
    simpa using h

  -- Bound on dc
  have h_dc_bound : |dc| ≤ 6 * r / (m * L^2) := by
    rw [hdc_inv]
    have h1 : |rc' / C - gmid * dd| ≤ |rc'| / C + |gmid| * |dd| := by
      calc
        |rc' / C - gmid * dd| ≤ |rc' / C| + |gmid * dd| := by
          exact abs_sub (rc' / C) (gmid * dd)
        _ = |rc'| / C + |gmid| * |dd| := by
          rw [abs_div, abs_of_pos hC_pos, abs_mul]
    have h2a : |rc'| / C ≤ r / C := by gcongr
    have h2b : |gmid| * |dd| ≤ 4 * r / (m * L^2) := by
      calc
        |gmid| * |dd| ≤ 1 * |dd| := by gcongr
        _ = |dd| := by ring
        _ ≤ 4 * r / (m * L^2) := h_dd_bound
    have h2 : |rc'| / C + |gmid| * |dd| ≤ r / C + 4 * r / (m * L^2) := by
      linarith
    have h3 : r / C = 2 * r / L := by
      simp only [hC, hL] <;> field_simp [hL_pos.ne'] <;> ring
    have h4 : |rc' / C - gmid * dd| ≤ 2 * r / L + 4 * r / (m * L^2) := by
      calc
        |rc' / C - gmid * dd| ≤ |rc'| / C + |gmid| * |dd| := h1
        _ ≤ r / C + 4 * r / (m * L^2) := h2
        _ = 2 * r / L + 4 * r / (m * L^2) := by rw [h3]
    have h5 : 2 * r / L + 4 * r / (m * L^2) ≤ 6 * r / (m * L^2) := by
      have h6 : 2 * r / L ≤ 2 * r / (m * L^2) := h2L_le
      have h7 : 2 * r / L + 4 * r / (m * L^2) ≤ 2 * r / (m * L^2) + 4 * r / (m * L^2) := by
        exact add_le_add h6 (le_refl _)
      have h8 : 2 * r / (m * L^2) + 4 * r / (m * L^2) = 6 * r / (m * L^2) := by ring
      rw [h8] at h7
      exact h7
    exact h4.trans h5

  -- Bound on db
  have h_db_bound : |db| ≤ 6 * r / (m * L^2) := by
    rw [hdb_inv]
    have h1 : |rb' / K - mid * dd| ≤ |rb'| / K + |mid| * |dd| := by
      calc
        |rb' / K - mid * dd| ≤ |rb' / K| + |mid * dd| := by
          exact abs_sub (rb' / K) (mid * dd)
        _ = |rb'| / K + |mid| * |dd| := by
          rw [abs_div, abs_of_pos hK_pos, abs_mul]
    have h2a : |rb'| / K ≤ r / K := by gcongr
    have h2b : |mid| * |dd| ≤ 4 * r / (m * L^2) := by
      calc
        |mid| * |dd| ≤ 1 * |dd| := by gcongr
        _ = |dd| := by ring
        _ ≤ 4 * r / (m * L^2) := h_dd_bound
    have h2 : |rb'| / K + |mid| * |dd| ≤ r / K + 4 * r / (m * L^2) := by
      linarith
    have h3 : r / K = 2 * r / (m * L) := by
      simp only [hK, hL] <;> field_simp [hm_pos.ne', hL_pos.ne'] <;> ring
    have h4 : |rb' / K - mid * dd| ≤ 2 * r / (m * L) + 4 * r / (m * L^2) := by
      calc
        |rb' / K - mid * dd| ≤ |rb'| / K + |mid| * |dd| := h1
        _ ≤ r / K + 4 * r / (m * L^2) := h2
        _ = 2 * r / (m * L) + 4 * r / (m * L^2) := by rw [h3]
    have h5 : 2 * r / (m * L) + 4 * r / (m * L^2) ≤ 6 * r / (m * L^2) := by
      have h6 : 2 * r / (m * L) ≤ 2 * r / (m * L^2) := h2mL_le
      have h7 : 2 * r / (m * L) + 4 * r / (m * L^2) ≤ 2 * r / (m * L^2) + 4 * r / (m * L^2) := by
        exact add_le_add h6 (le_refl _)
      have h8 : 2 * r / (m * L^2) + 4 * r / (m * L^2) = 6 * r / (m * L^2) := by ring
      rw [h8] at h7
      exact h7
    exact h4.trans h5

  -- Bound on da
  have h_da_bound : |da| ≤ 9 * r / (m * L^2) := by
    rw [hda_inv]
    have h_eq : ra' - gmid * db - mid * (rc' / C) = ra' - (gmid * db + mid * (rc' / C)) := by ring
    rw [h_eq]
    have h11 : |ra' - (gmid * db + mid * (rc' / C))| ≤
        |ra'| + |gmid * db + mid * (rc' / C)| := by
      simpa using abs_sub ra' (gmid * db + mid * (rc' / C))
    have h12 : |gmid * db + mid * (rc' / C)| ≤
        |gmid * db| + |mid * (rc' / C)| := h_abs_add (gmid * db) (mid * (rc' / C))
    have h13 : |gmid * db| = |gmid| * |db| := by rw [abs_mul]
    have h14 : |mid * (rc' / C)| = |mid| * (|rc'| / C) := by
      rw [abs_mul, abs_div, abs_of_pos hC_pos]
    have h15 : |ra' - (gmid * db + mid * (rc' / C))| ≤
        |ra'| + |gmid| * |db| + |mid| * (|rc'| / C) := by
      calc
        |ra' - (gmid * db + mid * (rc' / C))|
          ≤ |ra'| + |gmid * db + mid * (rc' / C)| := h11
        _ ≤ |ra'| + (|gmid * db| + |mid * (rc' / C)|) := by gcongr
        _ = |ra'| + |gmid| * |db| + |mid| * (|rc'| / C) := by
          rw [h13, h14] <;> ring
    have h21 : |ra'| ≤ r := ha'
    have h22 : |gmid| * |db| ≤ 6 * r / (m * L^2) := by
      calc
        |gmid| * |db| ≤ 1 * |db| := by gcongr
        _ = |db| := by ring
        _ ≤ 6 * r / (m * L^2) := h_db_bound
    have h23 : |mid| * (|rc'| / C) ≤ r / C := by
      have h231 : |mid| ≤ 1 := hmid_abs
      have h232 : |rc'| ≤ r := hc'
      have h : |mid| * (|rc'| / C) ≤ 1 * (r / C) := by gcongr
      simpa using h
    have h2 : |ra'| + |gmid| * |db| + |mid| * (|rc'| / C) ≤
        r + 6 * r / (m * L^2) + r / C := by
      linarith
    have h3 : r / C = 2 * r / L := by
      simp only [hC, hL] <;> field_simp [hL_pos.ne'] <;> ring
    have h4 : r + 6 * r / (m * L^2) + r / C ≤ 9 * r / (m * L^2) := by
      rw [h3]
      have h7 : r + 6 * r / (m * L^2) + 2 * r / L ≤
          (r / (m * L^2)) + 6 * r / (m * L^2) + 2 * r / (m * L^2) := by
        have h71 : r ≤ r / (m * L^2) := h_r_le
        have h72 : 2 * r / L ≤ 2 * r / (m * L^2) := h2L_le
        linarith
      have h8 : (r / (m * L^2)) + 6 * r / (m * L^2) + 2 * r / (m * L^2) =
          9 * r / (m * L^2) := by ring
      rw [h8] at h7
      exact h7
    exact h15.trans (h2.trans h4)

  -- Final bounds with d-c instead of L
  have h_final9 : 9 * r / (m * L^2) ≤ 100 * r / (m * (d - c)^2) := by
    have h9 : L = d - c := by simp only [hL]
    rw [h9] <;> gcongr <;> norm_num
  have h_final6 : 6 * r / (m * L^2) ≤ 100 * r / (m * (d - c)^2) := by
    have h9 : L = d - c := by simp only [hL]
    rw [h9] <;> gcongr <;> norm_num
  have h_final4 : 4 * r / (m * L^2) ≤ 100 * r / (m * (d - c)^2) := by
    have h9 : L = d - c := by simp only [hL]
    rw [h9] <;> gcongr <;> norm_num

  have h_goal_a : |p.a - q.a| ≤ 100 * r / (m * (d - c)^2) := by
    have h : |da| ≤ 9 * r / (m * L^2) := h_da_bound
    have h' : |da| ≤ 100 * r / (m * (d - c)^2) := h.trans h_final9
    simpa [hda] using h'
  have h_goal_b : |p.b - q.b| ≤ 100 * r / (m * (d - c)^2) := by
    have h : |db| ≤ 6 * r / (m * L^2) := h_db_bound
    have h' : |db| ≤ 100 * r / (m * (d - c)^2) := h.trans h_final6
    simpa [hdb] using h'
  have h_goal_c : |p.c - q.c| ≤ 100 * r / (m * (d - c)^2) := by
    have h : |dc| ≤ 6 * r / (m * L^2) := h_dc_bound
    have h' : |dc| ≤ 100 * r / (m * (d - c)^2) := h.trans h_final6
    simpa [hdc] using h'
  have h_goal_d : |p.d - q.d| ≤ 100 * r / (m * (d - c)^2) := by
    have h : |dd| ≤ 4 * r / (m * L^2) := h_dd_bound
    have h' : |dd| ≤ 100 * r / (m * (d - c)^2) := h.trans h_final4
    simpa [hdd] using h'

  exact ⟨h_goal_a, h_goal_b, h_goal_c, h_goal_d⟩

end Kakeya.Assouad
