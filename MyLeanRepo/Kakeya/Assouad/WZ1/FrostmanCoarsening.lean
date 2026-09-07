import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.CellBalancing
import MyLeanRepo.Kakeya.Assouad.WZ1.FrostmanCoarseningHelpers
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
WZ1 Lemma 48: retain a logarithmic fraction with balanced rho-cell
occupancy and transfer the Frostman estimate to the coarser scale.
-/

noncomputable section

namespace Kakeya.Assouad

open EuclideanSpace

/-- Bound: (r + ρ/√2)^α ≤ 4 * r^α for r ≥ ρ > 0, 0 < α ≤ 2. -/
lemma coarsening_rpow_bound (r rho alpha : ℝ) (hrho_pos : 0 < rho) (hr : rho ≤ r)
    (halpha : 0 < alpha) (halpha2 : alpha ≤ 2) :
    Real.rpow (r + rho / Real.sqrt 2) alpha ≤ 4 * Real.rpow r alpha := by
  set b : ℝ := 1 + 1 / Real.sqrt 2 with hb_def
  have hb_gt_one : 1 < b := by
    have hpos : 0 < 1 / Real.sqrt 2 := by positivity
    simp [hb_def] <;> linarith
  have h_factor : r + rho / Real.sqrt 2 ≤ r * b := by
    have h2 : rho / Real.sqrt 2 ≤ r / Real.sqrt 2 := by gcongr
    have h3 : r + rho / Real.sqrt 2 ≤ r + r / Real.sqrt 2 := by linarith
    have h4 : r + r / Real.sqrt 2 = r * b := by
      simp [hb_def] <;> ring
    exact h3.trans (le_of_eq h4)
  have h_sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h_nonneg : 0 ≤ r + rho / Real.sqrt 2 := by
    have h : 0 < rho / Real.sqrt 2 := div_pos hrho_pos h_sqrt2_pos
    linarith
  have h4 : Real.rpow (r + rho / Real.sqrt 2) alpha ≤ Real.rpow (r * b) alpha :=
    Real.rpow_le_rpow h_nonneg h_factor halpha.le
  have h_pos1 : 0 ≤ r := by linarith
  have h_pos2 : 0 ≤ b := by linarith
  have h5 : Real.rpow (r * b) alpha = Real.rpow r alpha * Real.rpow b alpha :=
    Real.mul_rpow h_pos1 h_pos2
  have hsqrt2_le : Real.sqrt 2 ≤ 2 := by
    have h : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
    have h2 : Real.sqrt 4 = 2 := by
      rw [Real.sqrt_eq_cases] <;> norm_num
    rw [h2] at h; exact h
  have h_sq2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h10 : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    calc (1 / Real.sqrt 2) ^ 2
      = 1 / (Real.sqrt 2) ^ 2 := by ring
    _ = 1 / 2 := by rw [h_sq2] <;> norm_num
  have h12 : 2 / Real.sqrt 2 = Real.sqrt 2 := by
    have h13 : 2 / Real.sqrt 2 = (2 * Real.sqrt 2) / (Real.sqrt 2) ^ 2 := by
      field_simp [h_sqrt2_pos.ne'] <;> ring
    rw [h13, h_sq2] <;> ring
  have h9 : b ^ 2 = 3 / 2 + Real.sqrt 2 := by
    have h14 : b ^ 2 = 1 + 2 / Real.sqrt 2 + (1 / Real.sqrt 2) ^ 2 := by
      rw [hb_def] <;> ring
    rw [h14, h12, h10] <;> ring
  have h8 : b ^ 2 ≤ 4 := by
    rw [h9]
    linarith [hsqrt2_le]
  have h6 : Real.rpow b alpha ≤ Real.rpow b 2 :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) halpha2
  have h7 : Real.rpow b 2 = b ^ 2 := by simp
  have h9' : Real.rpow b alpha ≤ 4 := by
    calc Real.rpow b alpha ≤ Real.rpow b 2 := h6
      _ = b ^ 2 := h7
      _ ≤ 4 := h8
  have h10' : 0 ≤ Real.rpow r alpha := Real.rpow_nonneg (by linarith) _
  have h_main : Real.rpow (r + rho / Real.sqrt 2) alpha ≤ Real.rpow r alpha * Real.rpow b alpha :=
    h4.trans (le_of_eq h5)
  calc Real.rpow (r + rho / Real.sqrt 2) alpha
      ≤ Real.rpow r alpha * Real.rpow b alpha := h_main
    _ ≤ Real.rpow r alpha * 4 := mul_le_mul_of_nonneg_left h9' h10'
    _ = 4 * Real.rpow r alpha := by ring

theorem wz1_frostman_coarsening :
    WZ1FrostmanCoarseningStatement := by
  intro delta rho alpha hdelta hdelta2 hrho hrho1 halpha halpha2 E hE_nonempty hE_ball hE_sep C hC hE_frost

  set cells : Finset (ℤ × ℤ) := E.image (gridIndex2D rho) with hcells_def
  let occupancy (idx : ℤ × ℤ) : ENNReal :=
    ((E.filter (fun p => gridIndex2D rho p = idx)).card : ENNReal)
  let fiber (idx : ℤ × ℤ) : DiscreteSet 2 :=
    E.filter (fun p => gridIndex2D rho p = idx)

  -- Every occupied cell has occupancy ≥ 1
  have h_occ_min : ∀ idx ∈ cells, ENNReal.ofReal (1 : ℝ) ≤ occupancy idx := by
    intro idx hidx
    have h_exists : ∃ p ∈ E, gridIndex2D rho p = idx := by
      simpa [hcells_def, Finset.mem_image] using hidx
    rcases h_exists with ⟨p, hp, hgrid⟩
    have h1 : p ∈ fiber idx := by
      simp only [fiber, Finset.mem_filter]
      exact ⟨hp, hgrid⟩
    have h2 : 1 ≤ (fiber idx).card := Finset.one_le_card.mpr ⟨p, h1⟩
    have h3 : (1 : ENNReal) ≤ ↑((fiber idx).card) := by exact_mod_cast h2
    simpa [occupancy] using h3

  -- Occupancy is positive
  have h_occ_pos : ∀ idx ∈ cells, 0 < occupancy idx := by
    intro idx hidx
    have h := h_occ_min idx hidx
    have h' : (0 : ENNReal) < ENNReal.ofReal (1 : ℝ) := by positivity
    exact h'.trans_le h

  -- Max occupancy bound: 9*(rho/delta)^2 ≤ 100/delta^2 since rho ≤ 1
  have h_occ_max : ∀ idx ∈ cells, occupancy idx ≤ ENNReal.ofReal (100 / delta^2) := by
    intro idx hidx
    have h1 : ((fiber idx).card : ℝ) ≤ 9 * (rho / delta)^2 :=
      max_occupancy2D hdelta (by linarith) hrho hE_sep idx
    have h2 : 9 * (rho / delta)^2 ≤ 100 / delta^2 := by
      have h3 : rho^2 ≤ 1 := by nlinarith
      have h4 : 0 < delta^2 := by positivity
      calc 9 * (rho / delta)^2
        = 9 * rho^2 / delta^2 := by ring
      _ ≤ 100 / delta^2 := by gcongr <;> nlinarith
    have h3 : ((fiber idx).card : ℝ) ≤ 100 / delta^2 := h1.trans h2
    have h4 : occupancy idx ≤ ENNReal.ofReal (100 / delta^2) := by
      have h5 : occupancy idx = ↑((fiber idx).card) := by rfl
      rw [h5]
      have h6 : (↑((fiber idx).card) : ENNReal) = ENNReal.ofReal ((fiber idx).card : ℝ) := by
        have h_ne_top : (↑((fiber idx).card) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
        exact (ENNReal.ofReal_toReal h_ne_top).symm
      rw [h6]
      exact ENNReal.ofReal_le_ofReal h3
    exact h4

  let Vmin : ℝ := 1
  let Vmax : ℝ := 100 / delta^2
  have hVmin_pos : 0 < Vmin := by norm_num
  have hVmin_le_Vmax : Vmin ≤ Vmax := by
    have h : 0 < delta^2 := by positivity
    have h2 : (1 : ℝ) ≤ 100 / delta^2 := by
      have h3 : delta^2 ≤ 100 := by nlinarith
      have h4 : 0 < delta^2 := by positivity
      exact (one_le_div h4).mpr h3
    exact h2

  -- Apply cell balancing
  rcases cell_balance_pigeonhole cells occupancy Vmin Vmax h_occ_pos h_occ_max h_occ_min hVmin_pos hVmin_le_Vmax
    with ⟨M, t, ht_sub, ht_band, ht_sum⟩

  let logarithmicLoss : ℝ := Real.logb 2 (Vmax / Vmin) + 1
  let selected : DiscreteSet 2 := E.filter (fun p => gridIndex2D rho p ∈ t)
  let coarse : DiscreteSet 2 := t.image (cellCenter2D rho)
  let assignment (x : Point2) : Point2 := cellCenter2D rho (gridIndex2D rho x)

  -- t is nonempty
  have ht_nonempty : t.Nonempty := by
    by_contra h
    have h_empty : t = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using h
    have h_loss_pos : 0 < logarithmicLoss := by
      have h1 : 1 < Vmax / Vmin := by
        have h2 : Vmax / Vmin = 100 / delta^2 := by
          dsimp only [Vmin, Vmax] <;> ring
        rw [h2]
        have h3 : 0 < delta^2 := by positivity
        have h4 : 1 < 100 / delta^2 := by
          have h5 : delta^2 ≤ 100 := by nlinarith
          exact (one_lt_div h3).mpr (by nlinarith)
        exact h4
      have h5 : 0 < Real.logb 2 (Vmax / Vmin) := by
        apply Real.logb_pos <;> norm_num <;> linarith
      linarith
    have h_loss_ne_top : ENNReal.ofReal logarithmicLoss ≠ ⊤ := by simp
    have h_cells_nonempty : cells.Nonempty := by
      rcases hE_nonempty with ⟨p, hp⟩
      exact ⟨gridIndex2D rho p, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
    rcases h_cells_nonempty with ⟨idx, hidx⟩
    have h_pos_idx : 0 < occupancy idx := h_occ_pos idx hidx
    have h_sum_pos : 0 < ∑ i ∈ cells, occupancy i :=
      h_pos_idx.trans_le (Finset.single_le_sum (fun i _ => le_of_lt (h_occ_pos i ‹_›)) hidx)
    set B := ENNReal.ofReal logarithmicLoss with hB
    have h_contra : 0 < (∑ i ∈ cells, occupancy i) / B :=
      ENNReal.div_pos h_sum_pos.ne' h_loss_ne_top
    have h_loss_eq : logarithmicLoss = Real.logb 2 (Vmax / Vmin) + 1 := by
      simp [logarithmicLoss] <;> ring
    have h_contra2 : (∑ i ∈ t, occupancy i) ≥ (∑ i ∈ cells, occupancy i) / B := by
      have hB_eq : B = ENNReal.ofReal (Real.logb 2 (Vmax / Vmin) + 1) := by
        simp [hB, logarithmicLoss] <;> ring
      rw [hB_eq]
      exact ht_sum
    rw [h_empty] at h_contra2
    have h_contra3 : (∑ i ∈ cells, occupancy i) / B ≤ 0 := by simpa using h_contra2
    exact False.elim (lt_irrefl 0 (h_contra.trans_le h_contra3))

  -- selected is nonempty
  have hselected_nonempty : selected.Nonempty := by
    rcases ht_nonempty with ⟨idx, hidx⟩
    have h_idx_in_cells : idx ∈ cells := ht_sub hidx
    have h_exists : ∃ p ∈ E, gridIndex2D rho p = idx := by
      simpa [hcells_def, Finset.mem_image] using h_idx_in_cells
    rcases h_exists with ⟨p, hp, hgrid⟩
    have hpin : p ∈ selected := by
      simp only [selected, Finset.mem_filter]
      exact ⟨hp, by rw [hgrid]; exact hidx⟩
    exact ⟨p, hpin⟩

  -- selected ⊆ E
  have hselected_subset : selected ⊆ E := Finset.filter_subset _ _

  -- Disjoint fibers
  have h_disj_fibers : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Disjoint (fiber i) (fiber j) := by
    intro i _ j _ hne
    simp only [Finset.disjoint_left, fiber, Finset.mem_filter]
    intro x hx1 hx2
    exact hne (hx1.2.symm.trans hx2.2)

  have h_selected_union : selected = t.biUnion fiber := by
    apply Finset.ext
    intro p
    have h1 : p ∈ selected ↔ p ∈ E ∧ gridIndex2D rho p ∈ t := by
      rw [Finset.mem_filter] <;> rfl
    have h2 : p ∈ t.biUnion fiber ↔ ∃ idx ∈ t, p ∈ fiber idx := by
      rw [Finset.mem_biUnion] <;> rfl
    rw [h1, h2]
    constructor
    · rintro ⟨hp, hgrid⟩
      refine ⟨gridIndex2D rho p, hgrid, ?_⟩
      have h3 : p ∈ fiber (gridIndex2D rho p) := by
        rw [Finset.mem_filter] <;> exact ⟨hp, rfl⟩
      exact h3
    · rintro ⟨idx, hidx, hp⟩
      have h4 : p ∈ fiber idx := hp
      have h5 : p ∈ E := (Finset.mem_filter.mp h4).1
      have h6 : gridIndex2D rho p = idx := (Finset.mem_filter.mp h4).2
      have h7 : gridIndex2D rho p ∈ t := by
        rw [h6] <;> exact hidx
      exact ⟨h5, h7⟩

  have h_sum_selected : selected.enncard = ∑ idx ∈ t, occupancy idx := by
    have h : selected.card = ∑ idx ∈ t, (fiber idx).card := by
      rw [h_selected_union, Finset.card_biUnion h_disj_fibers]
    have h' : selected.enncard = ↑selected.card := by simp [DiscreteSet.enncard]
    rw [h', h]
    have h_sum : (↑(∑ idx ∈ t, (fiber idx).card) : ENNReal) = ∑ idx ∈ t, (↑((fiber idx).card) : ENNReal) := by
      rw [Nat.cast_sum]
    rw [h_sum]
    <;> rfl

  have h_disj_cells : ∀ i ∈ cells, ∀ j ∈ cells, i ≠ j → Disjoint (fiber i) (fiber j) := by
    intro i _ j _ hne
    simp only [Finset.disjoint_left, fiber, Finset.mem_filter]
    intro x hx1 hx2
    exact hne (hx1.2.symm.trans hx2.2)

  have h_E_union : E = cells.biUnion fiber := by
    ext p
    simp [hcells_def, fiber, Finset.mem_biUnion]
    <;> aesop

  have h_sum_E : E.enncard = ∑ idx ∈ cells, occupancy idx := by
    have h : E.card = ∑ idx ∈ cells, (fiber idx).card := by
      rw [h_E_union, Finset.card_biUnion h_disj_cells]
    have h' : E.enncard = ↑E.card := by simp [DiscreteSet.enncard]
    rw [h', h]
    have h_sum : (↑(∑ idx ∈ cells, (fiber idx).card) : ENNReal) = ∑ idx ∈ cells, (↑((fiber idx).card) : ENNReal) := by
      rw [Nat.cast_sum]
    rw [h_sum]
    <;> rfl

  -- Retention
  have hretention : E.enncard ≤ ENNReal.ofReal logarithmicLoss * selected.enncard := by
    have h_loss_pos : 0 < logarithmicLoss := by
      have h1 : 1 < Vmax / Vmin := by
        have h2 : Vmax / Vmin = 100 / delta^2 := by
          simp [Vmin, Vmax] <;> ring
        rw [h2]
        have h3 : 0 < delta^2 := by positivity
        have h4 : 1 < 100 / delta^2 := by
          have h5 : delta^2 ≤ 100 := by nlinarith
          exact (one_lt_div h3).mpr (by nlinarith)
        exact h4
      have h5 : 0 < Real.logb 2 (Vmax / Vmin) := by
        apply Real.logb_pos <;> norm_num <;> linarith
      linarith
    have hloss_ennreal_pos : (0 : ENNReal) < ENNReal.ofReal logarithmicLoss := by
      exact ENNReal.ofReal_pos.mpr h_loss_pos
    have hloss_ne_top : ENNReal.ofReal logarithmicLoss ≠ ⊤ := ENNReal.ofReal_ne_top
    have hdiv : (∑ i ∈ cells, occupancy i) / ENNReal.ofReal logarithmicLoss ≤ (∑ i ∈ t, occupancy i) := ht_sum
    set B := ENNReal.ofReal logarithmicLoss with hB
    have hB_pos : 0 < B := hloss_ennreal_pos
    have hB_top : B ≠ ⊤ := hloss_ne_top
    have hcancel : (∑ i ∈ cells, occupancy i) ≤ B * (∑ i ∈ t, occupancy i) := by
      have h3 : (∑ i ∈ cells, occupancy i) / B ≤ (∑ i ∈ t, occupancy i) := hdiv
      have h4 : ((∑ i ∈ cells, occupancy i) / B) * B ≤ (∑ i ∈ t, occupancy i) * B := by gcongr
      have h5 : ((∑ i ∈ cells, occupancy i) / B) * B = (∑ i ∈ cells, occupancy i) :=
        ENNReal.div_mul_cancel hB_pos.ne' hB_top
      rw [h5] at h4
      have h7 : (∑ i ∈ cells, occupancy i) ≤ (∑ i ∈ t, occupancy i) * B := h4
      have h8 : (∑ i ∈ t, occupancy i) * B = B * (∑ i ∈ t, occupancy i) := by ring
      rw [h8] at h7
      exact h7
    rw [h_sum_E, h_sum_selected]
    exact hcancel

  -- logarithmicLoss bound
  have hlog_bound : logarithmicLoss ≤ 20 * (1 + Real.log delta⁻¹) := by
    have h1 : logarithmicLoss = Real.logb 2 (100 / delta^2) + 1 := by
      simp [logarithmicLoss, Vmin, Vmax] <;> ring
    rw [h1]
    have h2 : Real.logb 2 (100 / delta^2) = Real.logb 2 100 + 2 * Real.logb 2 delta⁻¹ := by
      have h3 : Real.logb 2 (100 / delta^2) = Real.logb 2 100 + Real.logb 2 (delta⁻¹ ^ 2) := by
        have h_eq : (100 / delta^2) = 100 * delta⁻¹ ^ 2 := by
          field_simp [hdelta.ne'] <;> ring
        rw [h_eq]
        rw [Real.logb_mul] <;> norm_num <;> positivity
      rw [h3]
      have h4 : Real.logb 2 (delta⁻¹ ^ 2) = 2 * Real.logb 2 delta⁻¹ := by
        rw [Real.logb_pow] <;> ring
      rw [h4] <;> ring
    rw [h2]
    have h5 : Real.logb 2 100 < 7 := by
      have h6 : Real.logb 2 100 < Real.logb 2 128 := by
        apply Real.logb_lt_logb (b := (2 : ℝ)) <;> norm_num
      have h7 : Real.logb 2 128 = 7 := by
        rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
      linarith
    have h8 : 1 / 2 < Real.log 2 := by
      have h9 : Real.exp (1 / 2 : ℝ) < 2 := by
        have h10 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
        have h11 : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
          have h := Real.exp_nsmul (1 / 2 : ℝ) 2
          norm_num at h ⊢
          exact h.symm
        nlinarith [Real.exp_pos (1 / 2 : ℝ)]
      have h12 : 1 / 2 < Real.log 2 := by
        have h13 : Real.log (Real.exp (1 / 2 : ℝ)) < Real.log 2 := Real.log_lt_log (by positivity) h9
        have h14 : Real.log (Real.exp (1 / 2 : ℝ)) = 1 / 2 := Real.log_exp (1 / 2)
        rw [h14] at h13
        exact h13
      exact h12
    have h9 : Real.logb 2 delta⁻¹ < 2 * Real.log delta⁻¹ := by
      have h10 : Real.logb 2 delta⁻¹ = Real.log delta⁻¹ / Real.log 2 := by
        rw [Real.logb] <;> ring
      rw [h10]
      have h11 : 0 < Real.log 2 := by positivity
      have h13 : 0 < Real.log delta⁻¹ := by
        apply Real.log_pos
        have h14 : 1 < delta⁻¹ := by
          have h15 : delta ≤ 1 / 2 := hdelta2
          have h16 : 1 / delta ≥ 2 := by
            calc 1 / delta ≥ 1 / (1 / 2) := by gcongr
              _ = 2 := by norm_num
          have h17 : (1 / delta : ℝ) = delta⁻¹ := by simp
          rw [h17] at h16
          linarith
        exact h14
      calc Real.log delta⁻¹ / Real.log 2
          < Real.log delta⁻¹ / (1 / 2) := by gcongr
        _ = 2 * Real.log delta⁻¹ := by ring
    have h10 : 0 ≤ Real.log delta⁻¹ := by
      apply Real.log_nonneg
      have h11 : 1 ≤ delta⁻¹ := by
        have h12 : delta ≤ 1 / 2 := hdelta2
        have h13 : 1 / delta ≥ 2 := by
          calc 1 / delta ≥ 1 / (1 / 2) := by gcongr
            _ = 2 := by norm_num
        have h14 : (1 / delta : ℝ) = delta⁻¹ := by simp
        rw [h14] at h13
        linarith
      exact h11
    linarith

  have hlog_pos : 0 < logarithmicLoss := by
    have h1 : 1 < Vmax / Vmin := by
      have h2 : Vmax / Vmin = 100 / delta^2 := by
        simp [Vmin, Vmax] <;> ring
      rw [h2]
      have h3 : 0 < delta^2 := by positivity
      have h4 : 1 < 100 / delta^2 := by
        have h5 : delta^2 ≤ 100 := by nlinarith
        exact (one_lt_div h3).mpr (by nlinarith)
      exact h4
    have h5 : 0 < Real.logb 2 (Vmax / Vmin) := by
      apply Real.logb_pos <;> norm_num <;> linarith
    linarith

  -- coarse nonempty
  have hcoarse_nonempty : coarse.Nonempty := by
    rcases ht_nonempty with ⟨idx, hidx⟩
    have h : cellCenter2D rho idx ∈ coarse :=
      Finset.mem_image.mpr ⟨idx, hidx, rfl⟩
    exact ⟨cellCenter2D rho idx, h⟩

  -- coarse separated
  have hcoarse_separated : coarse.IsDeltaSeparated rho := by
    intro q1 hq1 q2 hq2 hne
    rcases Finset.mem_image.mp hq1 with ⟨idx1, h1, rfl⟩
    rcases Finset.mem_image.mp hq2 with ⟨idx2, h2, hq⟩
    have hidx_ne : idx1 ≠ idx2 := by
      intro h
      have h' : cellCenter2D rho idx1 = q2 := by
        have h1 : cellCenter2D rho idx1 = cellCenter2D rho idx2 := by
          exact congr_arg (cellCenter2D rho) h
        rw [h1]
        exact hq
      exact hne h'
    have hrho_pos2 : 0 < rho := by linarith
    rw [←hq]
    exact cell_centers_separated2D hrho_pos2 hidx_ne

  -- assignment properties
  have hassignment_mem : ∀ x ∈ selected, assignment x ∈ coarse := by
    intro x hx
    have hgrid : gridIndex2D rho x ∈ t := (Finset.mem_filter.mp hx).2
    exact Finset.mem_image.mpr ⟨gridIndex2D rho x, hgrid, rfl⟩

  have hassignment_close : ∀ x ∈ selected, dist x (assignment x) ≤ rho := by
    intro x _
    have h : dist x (cellCenter2D rho (gridIndex2D rho x)) ≤ rho / Real.sqrt 2 :=
      grid_cell_close2D (by linarith) rfl
    have h2 : rho / Real.sqrt 2 ≤ rho := by
      have h3 : 0 < rho := by linarith
      have h4 : 1 / Real.sqrt 2 ≤ 1 := by
        have h5 : 1 ≤ Real.sqrt 2 := by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        calc 1 / Real.sqrt 2 ≤ 1 / 1 := by gcongr
          _ = 1 := by norm_num
      calc rho / Real.sqrt 2
        = rho * (1 / Real.sqrt 2) := by ring
      _ ≤ rho * 1 := by gcongr
      _ = rho := by ring
    linarith

  have hassignment_surjective : ∀ q ∈ coarse, ∃ x ∈ selected, assignment x = q := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨idx, hidx, rfl⟩
    have h_idx_in_cells : idx ∈ cells := ht_sub hidx
    have h_exists : ∃ p ∈ E, gridIndex2D rho p = idx := by
      simpa [hcells_def, Finset.mem_image] using h_idx_in_cells
    rcases h_exists with ⟨p, hp, hgrid⟩
    have hpin : p ∈ selected := by
      have h1 : p ∈ E := hp
      have h2 : gridIndex2D rho p ∈ t := by
        rw [hgrid]
        exact hidx
      exact Finset.mem_filter.mpr ⟨h1, h2⟩
    refine ⟨p, hpin, ?_⟩
    simp only [assignment, hgrid]

  -- Fiber multiplicity
  have hM_pos : 0 < M := by
    rcases ht_nonempty with ⟨idx, hidx⟩
    have hband2 : occupancy idx ≤ 2 * M := (ht_band idx hidx).2
    have hpos : 0 < occupancy idx := h_occ_pos idx (ht_sub hidx)
    by_contra h
    have h0 : M = 0 := by simpa using h
    rw [h0] at hband2
    have h_contra : occupancy idx ≤ 0 := by simpa using hband2
    exact not_le.mpr hpos h_contra

  have hM_lt_top : M ≠ ⊤ := by
    rcases ht_nonempty with ⟨idx, hidx⟩
    have hband1 : M ≤ occupancy idx := (ht_band idx hidx).1
    have hfin : occupancy idx ≠ ⊤ := by
      simp [occupancy]
    by_contra h
    have h_eq : occupancy idx = ⊤ := top_le_iff.mp (h ▸ hband1)
    exact hfin h_eq

  let M_nat : ℕ := Nat.ceil (ENNReal.toReal M)

  have hM_nat_pos : 0 < M_nat := by
    have h1 : 0 < ENNReal.toReal M :=
      ENNReal.toReal_pos hM_pos.ne' hM_lt_top
    have h2 : 0 < Nat.ceil (ENNReal.toReal M) := Nat.ceil_pos.mpr (by linarith)
    exact h2

  -- Fiber comparable
  have hfiber_comparable : ∀ q ∈ coarse,
      M_nat ≤ (selected.filter (fun x => assignment x = q)).card ∧
        (selected.filter (fun x => assignment x = q)).card ≤ 2 * M_nat := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨idx, hidx, rfl⟩
    let q' := cellCenter2D rho idx
    have hfiber_eq : selected.filter (fun x => assignment x = q') = fiber idx := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hx, h_eq⟩
        have hxE : x ∈ E := (Finset.mem_filter.mp hx).1
        have hgrid : gridIndex2D rho x = idx := by
          have h_inj : cellCenter2D rho (gridIndex2D rho x) = cellCenter2D rho idx := h_eq
          exact cellCenter2D_injective (by linarith) h_inj
        simp only [fiber, Finset.mem_filter]
        exact ⟨hxE, hgrid⟩
      · intro h
        simp only [fiber, Finset.mem_filter] at h
        rcases h with ⟨hxE, hgrid⟩
        have h2 : gridIndex2D rho x ∈ t := by
          rw [hgrid] <;> exact hidx
        have h_in_selected : x ∈ selected := Finset.mem_filter.mpr ⟨hxE, h2⟩
        have h_assignment : assignment x = q' := by
          have h3 : assignment x = cellCenter2D rho (gridIndex2D rho x) := by rfl
          rw [h3, hgrid] <;> rfl
        exact ⟨h_in_selected, h_assignment⟩
    rw [hfiber_eq]
    have hband : M ≤ occupancy idx ∧ occupancy idx ≤ 2 * M := ht_band idx hidx
    have h_occ_top : occupancy idx ≠ ⊤ := by
      have h_eq : occupancy idx = ↑((fiber idx).card) := by rfl
      rw [h_eq]
      simp
    have h_toReal_occ : ENNReal.toReal (occupancy idx) = ((fiber idx).card : ℝ) := by
      have h_eq : occupancy idx = ↑((fiber idx).card) := by rfl
      rw [h_eq]
      have h51 : (↑((fiber idx).card) : ENNReal).toNNReal = (↑((fiber idx).card) : NNReal) :=
        ENNReal.toNNReal_coe (↑((fiber idx).card) : NNReal)
      have h52 : ENNReal.toReal (↑((fiber idx).card) : ENNReal) = ↑((↑((fiber idx).card) : ENNReal).toNNReal) := by rfl
      rw [h52, h51] <;> norm_cast
    have h2M_top : (2 * M) ≠ ⊤ := by
      exact ENNReal.mul_ne_top (by simp) hM_lt_top
    have h_real1 : ENNReal.toReal M ≤ ((fiber idx).card : ℝ) := by
      have h : M ≤ occupancy idx := hband.1
      have h_eq : occupancy idx = ↑((fiber idx).card) := by rfl
      rw [h_eq] at h
      exact ENNReal.toReal_le_coe_of_le_coe h
    have h_real2 : ((fiber idx).card : ℝ) ≤ 2 * ENNReal.toReal M := by
      have h : occupancy idx ≤ 2 * M := hband.2
      have h_eq : occupancy idx = ↑((fiber idx).card) := by rfl
      rw [h_eq] at h
      have h_occ_top' : (↑((fiber idx).card) : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
      have h' : ENNReal.toReal (↑((fiber idx).card)) ≤ ENNReal.toReal (2 * M) :=
        (ENNReal.toReal_le_toReal h_occ_top' h2M_top).mpr h
      have h5 : ENNReal.toReal (↑((fiber idx).card)) = ((fiber idx).card : ℝ) := by
        have h51 : (↑((fiber idx).card) : ENNReal).toNNReal = (↑((fiber idx).card) : NNReal) :=
          ENNReal.toNNReal_coe (↑((fiber idx).card) : NNReal)
        have h52 : ENNReal.toReal (↑((fiber idx).card) : ENNReal) = ↑((↑((fiber idx).card) : ENNReal).toNNReal) := by rfl
        rw [h52, h51] <;> norm_cast
      have h6 : ENNReal.toReal (2 * M) = 2 * ENNReal.toReal M := by
        have h7 : ENNReal.toReal (2 * M) = ENNReal.toReal (2 : ENNReal) * ENNReal.toReal M := ENNReal.toReal_mul
        rw [h7]
        have h8 : ENNReal.toReal (2 : ENNReal) = (2 : ℝ) := by simp
        rw [h8] <;> ring
      rw [h5, h6] at h'
      exact h'
    have h1 : M_nat ≤ (fiber idx).card := by
      have h : M_nat = Nat.ceil (ENNReal.toReal M) := rfl
      rw [h]
      exact Nat.ceil_le.mpr h_real1
    have h2 : (fiber idx).card ≤ 2 * M_nat := by
      have h3 : ((fiber idx).card : ℝ) ≤ 2 * (M_nat : ℝ) := by
        calc ((fiber idx).card : ℝ)
            ≤ 2 * ENNReal.toReal M := h_real2
          _ ≤ 2 * (M_nat : ℝ) := by
            have h4 : ENNReal.toReal M ≤ (M_nat : ℝ) := Nat.le_ceil _
            gcongr
      exact_mod_cast h3
    exact ⟨h1, h2⟩

  -- selected.enncard ≤ 2 * M_nat * coarse.enncard
  have hselected_le : selected.enncard ≤ (2 * (M_nat : ENNReal)) * coarse.enncard := by
    have h1 : selected.enncard = ∑ idx ∈ t, occupancy idx := h_sum_selected
    rw [h1]
    have h2 : ∀ idx ∈ t, occupancy idx ≤ 2 * (M_nat : ENNReal) := by
      intro idx hidx
      have hband : occupancy idx ≤ 2 * M := (ht_band idx hidx).2
      have hM_le : M ≤ (M_nat : ENNReal) := by
        have hM_real : M = ENNReal.ofReal (ENNReal.toReal M) := by
          rw [ENNReal.ofReal_toReal hM_lt_top]
        rw [hM_real]
        have h : ENNReal.toReal M ≤ (M_nat : ℝ) := Nat.le_ceil _
        have h6 : ENNReal.ofReal (ENNReal.toReal M) ≤ ENNReal.ofReal (M_nat : ℝ) := ENNReal.ofReal_le_ofReal h
        have h7 : ENNReal.ofReal (M_nat : ℝ) = (M_nat : ENNReal) := by simp
        rw [h7] at h6
        exact h6
      calc occupancy idx
          ≤ 2 * M := hband
        _ ≤ 2 * (M_nat : ENNReal) := by gcongr
    have h3 : ∑ idx ∈ t, occupancy idx ≤ ∑ idx ∈ t, (2 * (M_nat : ENNReal)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact h2 i hi
    have h4 : ∑ idx ∈ t, (2 * (M_nat : ENNReal)) = (2 * (M_nat : ENNReal)) * (t.card : ENNReal) := by
      simp [Finset.sum_const] <;> ring
    rw [h4] at h3
    have h5 : coarse.enncard = (t.card : ENNReal) := by
      have h6 : coarse.card = t.card := by
        rw [Finset.card_image_of_injective _ (cellCenter2D_injective (by linarith))]
      have h7 : coarse.enncard = ↑coarse.card := by simp [DiscreteSet.enncard]
      have h8 : (↑coarse.card : ENNReal) = ↑t.card := by rw [h6]
      rw [h7, h8]
    rw [h5]
    exact h3

  -- Frostman transfer
  have hcoarse_frostman : coarse.IsFrostman rho alpha (ENNReal.ofReal (100 * logarithmicLoss) * C) := by
    intro q r hr rho_le_r
    have hr_pos : 0 < r := by linarith
    let B : DiscreteSet 2 := coarse.filter (fun q' => dist q' q ≤ r)
    have hB_def : coarse.ballCount q r = (B.card : ENNReal) := by rfl

    let S : DiscreteSet 2 := selected.filter (fun x => assignment x ∈ B)
    have hS_sub : S ⊆ E :=
      Finset.Subset.trans (Finset.filter_subset _ _) hselected_subset
    have hS_ball : ∀ x ∈ S, dist x q ≤ r + rho / Real.sqrt 2 := by
      intro x hx
      have h1 : x ∈ selected := (Finset.mem_filter.mp hx).1
      have h2 : assignment x ∈ B := (Finset.mem_filter.mp hx).2
      have h3 : dist (assignment x) q ≤ r := (Finset.mem_filter.mp h2).2
      have h4 : dist x (assignment x) ≤ rho / Real.sqrt 2 :=
        grid_cell_close2D (by linarith) rfl
      calc dist x q
          ≤ dist x (assignment x) + dist (assignment x) q := dist_triangle _ _ _
        _ ≤ rho / Real.sqrt 2 + r := by linarith
        _ = r + rho / Real.sqrt 2 := by ring
    have h_disj : ∀ q1 ∈ B, ∀ q2 ∈ B, q1 ≠ q2 →
        Disjoint (selected.filter (fun x => assignment x = q1))
          (selected.filter (fun x => assignment x = q2)) := by
      intro q1 _ q2 _ hne
      simp only [Finset.disjoint_left, Finset.mem_filter]
      intro x hx1 hx2
      exact hne (hx1.2.symm.trans hx2.2)
    have h_union : S = B.biUnion (fun q' => selected.filter (fun x => assignment x = q')) := by
      ext x
      simp only [S, Finset.mem_filter, Finset.mem_biUnion]
      constructor
      · rintro ⟨hx, hq⟩
        exact ⟨assignment x, hq, hx, rfl⟩
      · rintro ⟨q', hq, hx, rfl⟩
        exact ⟨hx, hq⟩
    have hS_card : S.card ≥ M_nat * B.card := by
      rw [h_union, Finset.card_biUnion h_disj]
      have h : ∑ q' ∈ B, (selected.filter (fun x => assignment x = q')).card ≥ ∑ q' ∈ B, M_nat := by
        apply Finset.sum_le_sum
        intro q' hq'
        exact (hfiber_comparable q' (Finset.mem_filter.mp hq').1).1
      have h2 : ∑ q' ∈ B, M_nat = M_nat * B.card := by
        simp [Finset.sum_const, mul_comm]
        <;> ring
      rw [h2] at h
      exact h
    have hE_ball2 : S.card ≤ (E.filter (fun y => dist y q ≤ r + rho / Real.sqrt 2)).card := by
      apply Finset.card_le_card
      intro x hx
      have h1 : x ∈ E := hS_sub hx
      exact Finset.mem_filter.mpr ⟨h1, hS_ball x hx⟩
    have h_transfer : (M_nat : ENNReal) * (B.card : ENNReal) ≤
        E.ballCount q (r + rho / Real.sqrt 2) := by
      have h5 : (M_nat : ENNReal) * (B.card : ENNReal) ≤ (S.card : ENNReal) := by
        exact_mod_cast hS_card
      have h6 : (S.card : ENNReal) ≤ E.ballCount q (r + rho / Real.sqrt 2) := by
        have h7 : (S.card : ENNReal) ≤ ((E.filter (fun y => dist y q ≤ r + rho / Real.sqrt 2)).card : ENNReal) := by
          exact_mod_cast hE_ball2
        simpa [DiscreteSet.ballCount] using h7
      exact h5.trans h6

    -- Extended Frostman
    have hradius : delta ≤ r + rho / Real.sqrt 2 := by
      calc delta
        ≤ rho := hrho
        _ ≤ r := hr
        _ ≤ r + rho / Real.sqrt 2 := by
          have h1 : 0 < rho := by linarith
          have h2 : 0 < Real.sqrt 2 := by positivity
          have hpos : 0 ≤ rho / Real.sqrt 2 := div_nonneg h1.le h2.le
          linarith
    have h_ext : E.ballCount q (r + rho / Real.sqrt 2) ≤
        C * Kakeya.realRpowENN (r + rho / Real.sqrt 2) alpha * E.enncard :=
      hE_frost.extend hE_ball hC halpha.le q (r + rho / Real.sqrt 2) hradius

    -- Power bound
    have hpow : Kakeya.realRpowENN (r + rho / Real.sqrt 2) alpha ≤
        4 * Kakeya.realRpowENN r alpha := by
      have hreal : Real.rpow (r + rho / Real.sqrt 2) alpha ≤ 4 * Real.rpow r alpha :=
        coarsening_rpow_bound r rho alpha (by linarith) (by linarith) halpha halpha2
      simpa [Kakeya.realRpowENN] using ENNReal.ofReal_le_ofReal hreal

    have h9 : (M_nat : ENNReal) * coarse.ballCount q r ≤
        (M_nat : ENNReal) * (ENNReal.ofReal (100 * logarithmicLoss) * C * Kakeya.realRpowENN r alpha * coarse.enncard) := by
      calc (M_nat : ENNReal) * coarse.ballCount q r
          = (M_nat : ENNReal) * (B.card : ENNReal) := by rw [hB_def]
        _ ≤ E.ballCount q (r + rho / Real.sqrt 2) := h_transfer
        _ ≤ C * Kakeya.realRpowENN (r + rho / Real.sqrt 2) alpha * E.enncard := h_ext
        _ ≤ C * (4 * Kakeya.realRpowENN r alpha) * E.enncard := by gcongr
        _ = 4 * C * Kakeya.realRpowENN r alpha * E.enncard := by ring
        _ ≤ 4 * C * Kakeya.realRpowENN r alpha * (ENNReal.ofReal logarithmicLoss * selected.enncard) := by
            gcongr <;> exact hretention
        _ ≤ 4 * C * Kakeya.realRpowENN r alpha * (ENNReal.ofReal logarithmicLoss * ((2 * (M_nat : ENNReal)) * coarse.enncard)) := by
            gcongr <;> exact hselected_le
        _ = 8 * ENNReal.ofReal logarithmicLoss * C * Kakeya.realRpowENN r alpha * (M_nat : ENNReal) * coarse.enncard := by ring
        _ ≤ 100 * ENNReal.ofReal logarithmicLoss * C * Kakeya.realRpowENN r alpha * (M_nat : ENNReal) * coarse.enncard := by
            gcongr <;> norm_num
        _ = (M_nat : ENNReal) * (ENNReal.ofReal (100 * logarithmicLoss) * C * Kakeya.realRpowENN r alpha * coarse.enncard) := by
          have h_pos : 0 ≤ logarithmicLoss := by linarith [hlog_pos]
          have h100 : (100 : ENNReal) * ENNReal.ofReal logarithmicLoss = ENNReal.ofReal (100 * logarithmicLoss) := by
            have h : (100 : ENNReal) = ENNReal.ofReal 100 := by simp
            rw [h]
            rw [←ENNReal.ofReal_mul (by norm_num)]
            <;> norm_cast
          rw [h100]
          ring

    have hcancel : (M_nat : ENNReal) ≠ 0 := by
      exact_mod_cast hM_nat_pos.ne'
    have hcancel_top : (M_nat : ENNReal) ≠ ⊤ := by simp
    let X : ENNReal := ENNReal.ofReal (100 * logarithmicLoss) * C * Kakeya.realRpowENN r alpha * coarse.enncard
    have h_final : coarse.ballCount q r ≤ X :=
      (ENNReal.mul_le_mul_iff_right hcancel hcancel_top).mp h9
    exact h_final

  -- Construct the data
  exact ⟨selected, hselected_subset, hselected_nonempty,
    logarithmicLoss, hlog_pos, hlog_bound, hretention,
    coarse, hcoarse_nonempty, hcoarse_separated, hcoarse_frostman,
    assignment, hassignment_mem, hassignment_close, hassignment_surjective,
    M_nat, hM_nat_pos, hfiber_comparable⟩

end Kakeya.Assouad
