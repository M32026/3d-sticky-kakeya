import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23WindowedGlobalPackage
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedCellGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SpatialGrid
import MyLeanRepo.Kakeya.Assouad.WZ1.ADPigeonhole

/-!
# Tight height-window pigeonhole for WZ1 Lemma 23

Partition active cell-center heights into blocks of width `sqrt rho`.  One
complete-cell height window retains at least the exact fraction
`sqrt rho / (2 + rho + sqrt rho)`.  The denominator uses the actual
cell-center range `[-1-rho/2, 1+rho/2]`.
-/

namespace Kakeya.Assouad

open MeasureTheory Metric Set

lemma height_window_pigeonhole_tight_of_paper_window
    {delta rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 2)
    (hheight : ∀ point ∈ Y.union, |point (2 : Fin 3)| ≤ 1) :
    ∃ left : ℝ,
      volume (Y.union ∩ wz1Lemma23CellHeightWindowSet rho hrho left) ≥
        volume Y.union * ENNReal.ofReal (Real.sqrt rho) /
          ENNReal.ofReal (2 + rho + Real.sqrt rho) := by
  let activeCells := wz1Lemma23ActiveCells Y rho hrho
  let centerHeight (idx : ℤ × ℤ × ℤ) : ℝ :=
    (wz1Lemma23SnappedPoint rho idx) (2 : Fin 3)
  let heights : Finset ℝ := activeCells.image centerHeight
  by_cases h_empty : activeCells = ∅
  · have hcover : Y.union ⊆ (∅ : Set Point3) := by
      intro p hp
      have hnorm : ‖p‖ ≤ 2 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hball hp
      let idx := wz1Lemma23CellIndex rho p
      have hbounded : idx ∈ wz1Lemma23BoundedCells rho hrho :=
        wz1Lemma23_index_mem_bounded_two hrho hnorm
      have hactive : idx ∈ activeCells := by
        rw [wz1Lemma23_mem_active_iff Y hrho idx]
        exact ⟨hbounded, ⟨p, hp, rfl⟩⟩
      rw [h_empty] at hactive
      simp at hactive
    have h_empty_union : Y.union = ∅ := Set.subset_empty_iff.mp hcover
    refine ⟨0, ?_⟩
    rw [h_empty_union]
    simp
  · have hne : activeCells.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr h_empty
    have hheights_nonempty : heights.Nonempty := hne.image _
    let h_min := heights.min' hheights_nonempty
    let h_max := heights.max' hheights_nonempty
    have hmin_in : h_min ∈ heights := Finset.min'_mem _ _
    have hmax_in : h_max ∈ heights := Finset.max'_mem _ _
    have hcenter_bound :
        ∀ idx ∈ activeCells, |centerHeight idx| ≤ 1 + rho / 2 := by
      intro idx hidx
      have hgeom :=
        (wz1_lemma23_snapped_cell_geometry rho hrho hrho_one).2.1
      rcases (wz1Lemma23_mem_active_iff Y hrho idx).mp hidx with
        ⟨_, p, hp, hpointCell⟩
      have hcell : wz1Lemma23CellIndex rho p = idx := by
        simpa [wz1Lemma23Cell] using hpointCell
      have hcoord :
          ∀ i : Fin 3,
            |p i - (wz1Lemma23CellCenter rho idx) i| ≤ rho / 2 :=
        (hgeom idx p hcell).1
      have h2 : |p 2 - centerHeight idx| ≤ rho / 2 := hcoord 2
      have h_p2_abs : |p 2| ≤ 1 := hheight p hp
      rw [abs_le]
      constructor
      · have h1 : p 2 - centerHeight idx ≤ rho / 2 :=
          (abs_le.mp h2).2
        have hp2 : -1 ≤ p 2 := (abs_le.mp h_p2_abs).1
        linarith
      · have h1 : -(rho / 2) ≤ p 2 - centerHeight idx :=
          (abs_le.mp h2).1
        have hp2 : p 2 ≤ 1 := (abs_le.mp h_p2_abs).2
        linarith
    have hmin_ge : -(1 + rho / 2) ≤ h_min := by
      rcases Finset.mem_image.mp hmin_in with ⟨idx, hidx, heq⟩
      have h := (abs_le.mp (hcenter_bound idx hidx)).1
      rwa [heq] at h
    have hmax_le : h_max ≤ 1 + rho / 2 := by
      rcases Finset.mem_image.mp hmax_in with ⟨idx, hidx, heq⟩
      have h := (abs_le.mp (hcenter_bound idx hidx)).2
      rwa [heq] at h
    have hrange : h_max - h_min ≤ 2 + rho := by
      linarith
    let sqrtRho := Real.sqrt rho
    have hsqrt_pos : 0 < sqrtRho := Real.sqrt_pos.mpr hrho
    have hsqrt_one : sqrtRho ≤ 1 := Real.sqrt_le_one.mpr hrho_one
    have h_inj :
        ∀ a b : ENNReal,
          a ≠ ⊤ → b ≠ ⊤ → a.toReal = b.toReal → a = b := by
      intro a b ha hb h
      have h1 : a = ENNReal.ofReal a.toReal :=
        (ENNReal.ofReal_toReal ha).symm
      have h2 : b = ENNReal.ofReal b.toReal :=
        (ENNReal.ofReal_toReal hb).symm
      rw [h1, h2, h]
    let blockIndex (h : ℝ) : ℤ :=
      Int.floor ((h - h_min) / sqrtRho)
    let blocks : Finset ℤ := heights.image blockIndex
    let K := blocks.card
    have hK_le : (K : ENNReal) ≤
        ENNReal.ofReal (2 + rho + sqrtRho) /
          ENNReal.ofReal sqrtRho := by
      have h1 :
          ∀ k ∈ blocks, 0 ≤ k ∧
            (k : ℝ) ≤ (2 + rho) / sqrtRho := by
        intro k hk
        rcases Finset.mem_image.mp hk with ⟨h, hh, rfl⟩
        have hge : h_min ≤ h := Finset.min'_le heights h hh
        have hle : h ≤ h_max := Finset.le_max' heights h hh
        have hdiff : h - h_min ≤ 2 + rho := by linarith
        have h2 : 0 ≤ (h - h_min) / sqrtRho := by
          apply div_nonneg <;> linarith
        have h3 :
            (h - h_min) / sqrtRho ≤
              (2 + rho) / sqrtRho :=
          div_le_div_of_nonneg_right hdiff hsqrt_pos.le
        have h4 : 0 ≤ blockIndex h := Int.floor_nonneg.mpr h2
        have h5 : (blockIndex h : ℝ) ≤
            (h - h_min) / sqrtRho := Int.floor_le _
        exact ⟨h4, h5.trans h3⟩
      let bmax := Int.floor ((2 + rho) / sqrtRho)
      have hbmax_nonneg : 0 ≤ bmax := by
        apply Int.floor_nonneg.mpr
        positivity
      have hblocks_sub : blocks ⊆ Finset.Icc 0 bmax := by
        intro k hk
        have hk' := h1 k hk
        exact Finset.mem_Icc.mpr
          ⟨hk'.1, Int.le_floor.mpr hk'.2⟩
      have hcard : K ≤ (Finset.Icc 0 bmax).card :=
        Finset.card_le_card hblocks_sub
      have hcard2 :
          ((Finset.Icc 0 bmax).card : ℝ) = (bmax : ℝ) + 1 := by
        have h :
            (Finset.Icc 0 bmax).card = bmax.toNat + 1 := by
          simp [hbmax_nonneg, Finset.Icc_eq_empty_of_lt] <;> omega
        rw [h]
        have h' :
            ((bmax.toNat + 1 : ℕ) : ℝ) = (bmax : ℝ) + 1 := by
          have hb : (bmax.toNat : ℤ) = bmax :=
            Int.toNat_of_nonneg hbmax_nonneg
          simp [hb] <;> norm_cast
        exact h'
      have hK_real : (K : ℝ) ≤ (bmax : ℝ) + 1 := by
        have h :
            (K : ℝ) ≤ ((Finset.Icc 0 bmax).card : ℝ) := by
          exact_mod_cast hcard
        rwa [hcard2] at h
      have h_floor :
          (bmax : ℝ) ≤ (2 + rho) / sqrtRho :=
        Int.floor_le _
      have hK_le_real :
          (K : ℝ) ≤
            (2 + rho + sqrtRho) / sqrtRho := by
        calc
          (K : ℝ) ≤ (bmax : ℝ) + 1 := hK_real
          _ ≤ (2 + rho) / sqrtRho + 1 := by
            linarith [h_floor]
          _ = (2 + rho + sqrtRho) / sqrtRho := by
            field_simp [hsqrt_pos.ne'] <;> ring
      have h9 :
          (K : ENNReal) ≤
            ENNReal.ofReal
              ((2 + rho + sqrtRho) / sqrtRho) := by
        have h_eq : (K : ENNReal) = ENNReal.ofReal (K : ℝ) := by
          simp
        rw [h_eq]
        exact ENNReal.ofReal_le_ofReal hK_le_real
      have hsqrt_pos' : ENNReal.ofReal sqrtRho ≠ 0 :=
        (ENNReal.ofReal_pos.mpr hsqrt_pos).ne'
      have hsqrt_top : ENNReal.ofReal sqrtRho ≠ ⊤ := by simp
      have h12 :
          ENNReal.ofReal
              ((2 + rho + sqrtRho) / sqrtRho) =
            ENNReal.ofReal (2 + rho + sqrtRho) /
              ENNReal.ofReal sqrtRho := by
        have h_top1 :
            ENNReal.ofReal
              ((2 + rho + sqrtRho) / sqrtRho) ≠ ⊤ := by
          simp
        have h_top2 :
            ENNReal.ofReal (2 + rho + sqrtRho) /
                ENNReal.ofReal sqrtRho ≠ ⊤ := by
          intro h
          rcases (ENNReal.div_eq_top).mp h with
            (⟨_, h0⟩ | ⟨htop, _⟩)
          · exact hsqrt_pos' h0
          · simp at htop
        have h_pos1 :
            0 ≤ (2 + rho + sqrtRho) / sqrtRho := by
          positivity
        have h_pos2 : 0 ≤ 2 + rho + sqrtRho := by
          positivity
        have h_real1 :
            (ENNReal.ofReal
                ((2 + rho + sqrtRho) / sqrtRho)).toReal =
              (2 + rho + sqrtRho) / sqrtRho :=
          ENNReal.toReal_ofReal h_pos1
        have h_real2 :
            (ENNReal.ofReal (2 + rho + sqrtRho) /
                ENNReal.ofReal sqrtRho).toReal =
              (2 + rho + sqrtRho) / sqrtRho := by
          rw [ENNReal.toReal_div]
          simp [ENNReal.toReal_ofReal h_pos2,
            ENNReal.toReal_ofReal hsqrt_pos.le]
        exact h_inj _ _ h_top1 h_top2 (by rw [h_real1, h_real2])
      rw [h12] at h9
      exact h9
    let blockCells (k : ℤ) : Finset (ℤ × ℤ × ℤ) :=
      activeCells.filter fun idx => blockIndex (centerHeight idx) = k
    let blockUnion (k : ℤ) : Set Point3 :=
      ⋃ idx ∈ blockCells k, wz1Lemma23Cell rho idx
    have hdisjoint :
        ∀ k1 k2 : ℤ, k1 ≠ k2 →
          Disjoint (blockUnion k1) (blockUnion k2) := by
      intro k1 k2 hne
      rw [Set.disjoint_left]
      intro p hp1 hp2
      rcases Set.mem_iUnion₂.mp hp1 with ⟨idx1, h_idx1, hcell1⟩
      rcases Set.mem_iUnion₂.mp hp2 with ⟨idx2, h_idx2, hcell2⟩
      have h1 : blockIndex (centerHeight idx1) = k1 :=
        (Finset.mem_filter.mp h_idx1).2
      have h2 : blockIndex (centerHeight idx2) = k2 :=
        (Finset.mem_filter.mp h_idx2).2
      have h_eq1 : wz1Lemma23CellIndex rho p = idx1 := by
        simpa [wz1Lemma23Cell] using hcell1
      have h_eq2 : wz1Lemma23CellIndex rho p = idx2 := by
        simpa [wz1Lemma23Cell] using hcell2
      have hsame : idx1 = idx2 := h_eq1.symm.trans h_eq2
      have h1' : blockIndex (centerHeight idx2) = k1 := by
        rwa [hsame] at h1
      exact hne (h1'.symm.trans h2)
    have hcover_active :
        Y.union ⊆ ⋃ idx ∈ activeCells, wz1Lemma23Cell rho idx := by
      intro p hp
      have hnorm : ‖p‖ ≤ 2 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hball hp
      let idx := wz1Lemma23CellIndex rho p
      have hbounded : idx ∈ wz1Lemma23BoundedCells rho hrho :=
        wz1Lemma23_index_mem_bounded_two hrho hnorm
      have hactive : idx ∈ activeCells := by
        rw [wz1Lemma23_mem_active_iff Y hrho idx]
        exact ⟨hbounded, ⟨p, hp, rfl⟩⟩
      exact Set.mem_iUnion₂.mpr ⟨idx, hactive, rfl⟩
    have hcover : Y.union ⊆ ⋃ k ∈ blocks, blockUnion k := by
      intro p hp
      rcases Set.mem_iUnion₂.mp (hcover_active hp) with
        ⟨idx, hidx, hcell⟩
      let k := blockIndex (centerHeight idx)
      have hk : k ∈ blocks :=
        Finset.mem_image.mpr
          ⟨centerHeight idx, Finset.mem_image.mpr ⟨idx, hidx, rfl⟩, rfl⟩
      have hbc : idx ∈ blockCells k := by
        simp [blockCells, hidx]
        rfl
      exact Set.mem_iUnion₂.mpr
        ⟨k, hk, Set.mem_iUnion₂.mpr ⟨idx, hbc, hcell⟩⟩
    have hsum :
        volume Y.union ≤
          ∑ k ∈ blocks, volume (Y.union ∩ blockUnion k) := by
      have h1 :
          Y.union ⊆
            ⋃ k ∈ blocks, Y.union ∩ blockUnion k := by
        intro p hp
        rcases Set.mem_iUnion₂.mp (hcover hp) with ⟨k, hk, hp2⟩
        exact Set.mem_iUnion₂.mpr ⟨k, hk, ⟨hp, hp2⟩⟩
      calc
        volume Y.union
            ≤ volume (⋃ k ∈ blocks, Y.union ∩ blockUnion k) :=
          measure_mono h1
        _ ≤ ∑ k ∈ blocks, volume (Y.union ∩ blockUnion k) :=
          measure_biUnion_finset_le blocks _
    have hV_top : volume Y.union ≠ ⊤ := by
      have hballFinite :
          volume (Metric.closedBall (0 : Point3) 2) < ⊤ :=
        Metric.isBounded_closedBall.measure_lt_top
      exact ((measure_mono hball).trans_lt hballFinite).ne
    have hblocks_nonempty : blocks.Nonempty :=
      hheights_nonempty.image _
    have hK_pos : (K : ENNReal) ≠ 0 := by
      have h : 0 < K := Finset.card_pos.mpr hblocks_nonempty
      exact_mod_cast h.ne'
    have hK_top : (K : ENNReal) ≠ ⊤ := by simp
    have hpigeon :
        ∃ k ∈ blocks,
          volume Y.union / (K : ENNReal) ≤
            volume (Y.union ∩ blockUnion k) := by
      by_contra h
      push Not at h
      let b := volume Y.union / (K : ENNReal)
      have hb_top : b ≠ ⊤ := by
        have hdiv : b = volume Y.union * (K : ENNReal)⁻¹ := by rfl
        rw [hdiv]
        have hinv_top : (K : ENNReal)⁻¹ ≠ ⊤ := by
          simp [hK_pos, hK_top]
        exact ENNReal.mul_ne_top hV_top hinv_top
      have hfin :
          ∀ k ∈ blocks, volume (Y.union ∩ blockUnion k) ≠ ⊤ := by
        intro k _
        exact ne_top_of_le_ne_top hV_top
          (measure_mono Set.inter_subset_left)
      have h3 :
          ∑ k ∈ blocks, volume (Y.union ∩ blockUnion k) <
            (blocks.card : ENNReal) * b :=
        finset_sum_lt_card_mul_ennreal
          hblocks_nonempty hb_top hfin h
      have h4 : (blocks.card : ENNReal) * b = volume Y.union := by
        have hdiv : b = volume Y.union * (K : ENNReal)⁻¹ := by rfl
        rw [hdiv]
        have hmul : (K : ENNReal) * (K : ENNReal)⁻¹ = 1 :=
          ENNReal.mul_inv_cancel hK_pos hK_top
        have h9 :
            (K : ENNReal) *
                (volume Y.union * (K : ENNReal)⁻¹) =
              volume Y.union *
                ((K : ENNReal) * (K : ENNReal)⁻¹) := by
          rw [mul_left_comm]
        rw [h9, hmul, mul_one]
      rw [h4] at h3
      exact (Std.not_le.mpr h3) hsum
    rcases hpigeon with ⟨k, hk, hvol⟩
    let left := h_min + (k : ℝ) * sqrtRho
    have hwindow :
        blockUnion k ⊆
          wz1Lemma23CellHeightWindowSet rho hrho left := by
      intro p hp
      rcases Set.mem_iUnion₂.mp hp with ⟨idx, h_idx, hcell⟩
      have hblock : blockIndex (centerHeight idx) = k :=
        (Finset.mem_filter.mp h_idx).2
      have hbounded : idx ∈ wz1Lemma23BoundedCells rho hrho :=
        ((wz1Lemma23_mem_active_iff Y hrho idx).mp
          (Finset.mem_filter.mp h_idx).1).1
      have hfloor1 :
          (k : ℝ) ≤ (centerHeight idx - h_min) / sqrtRho := by
        rw [← hblock]
        exact Int.floor_le _
      have hfloor2 :
          (centerHeight idx - h_min) / sqrtRho < (k : ℝ) + 1 := by
        rw [← hblock]
        exact Int.lt_floor_add_one _
      have hleft1 : left ≤ centerHeight idx := by
        dsimp only [left]
        have h :
            (k : ℝ) * sqrtRho ≤ centerHeight idx - h_min := by
          have h'' :
              (k : ℝ) * sqrtRho ≤
                ((centerHeight idx - h_min) / sqrtRho) * sqrtRho := by
            gcongr
          have h_eq :
              ((centerHeight idx - h_min) / sqrtRho) * sqrtRho =
                centerHeight idx - h_min := by
            field_simp [hsqrt_pos.ne']
          rwa [h_eq] at h''
        linarith
      have hleft2 : centerHeight idx ≤ left + sqrtRho := by
        dsimp only [left]
        have h :
            centerHeight idx - h_min <
              ((k : ℝ) + 1) * sqrtRho := by
          have h'' :
              ((centerHeight idx - h_min) / sqrtRho) * sqrtRho <
                ((k : ℝ) + 1) * sqrtRho := by
            gcongr
          have h_eq :
              ((centerHeight idx - h_min) / sqrtRho) * sqrtRho =
                centerHeight idx - h_min := by
            field_simp [hsqrt_pos.ne']
          rwa [h_eq] at h''
        linarith
      have hfilter :
          idx ∈ wz1Lemma23CellHeightWindow rho hrho left := by
        simp only [wz1Lemma23CellHeightWindow, Finset.mem_filter]
        exact ⟨hbounded, ⟨hleft1, hleft2⟩⟩
      exact Set.mem_iUnion₂.mpr ⟨idx, hfilter, hcell⟩
    have hfinal :
        volume
            (Y.union ∩
              wz1Lemma23CellHeightWindowSet rho hrho left) ≥
          volume Y.union * ENNReal.ofReal sqrtRho /
            ENNReal.ofReal (2 + rho + sqrtRho) := by
      have hsub :
          Y.union ∩ blockUnion k ⊆
            Y.union ∩
              wz1Lemma23CellHeightWindowSet rho hrho left := by
        intro x hx
        exact ⟨hx.1, hwindow hx.2⟩
      calc
        volume
              (Y.union ∩
                wz1Lemma23CellHeightWindowSet rho hrho left)
            ≥ volume (Y.union ∩ blockUnion k) :=
          measure_mono hsub
        _ ≥ volume Y.union / (K : ENNReal) := hvol
        _ ≥ volume Y.union * ENNReal.ofReal sqrtRho /
              ENNReal.ofReal (2 + rho + sqrtRho) := by
          have hdiv :
              volume Y.union / (K : ENNReal) =
                volume Y.union * (K : ENNReal)⁻¹ := by
            rfl
          rw [hdiv]
          have hinv :
              (K : ENNReal)⁻¹ ≥
                (ENNReal.ofReal (2 + rho + sqrtRho) /
                  ENNReal.ofReal sqrtRho)⁻¹ :=
            ENNReal.inv_le_inv.mpr hK_le
          have hnum_pos :
              (0 : ENNReal) < ENNReal.ofReal sqrtRho :=
            ENNReal.ofReal_pos.mpr hsqrt_pos
          have hden_pos :
              (0 : ENNReal) <
                ENNReal.ofReal (2 + rho + sqrtRho) :=
            ENNReal.ofReal_pos.mpr (by positivity)
          set denominator :=
            ENNReal.ofReal (2 + rho + sqrtRho)
          set numerator := ENNReal.ofReal sqrtRho
          have hden_ne_zero : denominator ≠ 0 :=
            hden_pos.ne'
          have hnum_ne_zero : numerator ≠ 0 :=
            hnum_pos.ne'
          have hnum_ne_top : numerator ≠ ⊤ := by
            simp [numerator]
          have h9 :
              (denominator / numerator)⁻¹ =
                numerator / denominator := by
            have hquotient_ne_zero :
                denominator / numerator ≠ 0 :=
              ENNReal.div_ne_zero.mpr
                ⟨hden_ne_zero, hnum_ne_top⟩
            have hinv_ne_top :
                (denominator / numerator)⁻¹ ≠ ⊤ := by
              simpa [ENNReal.inv_eq_top] using
                hquotient_ne_zero
            have hreverse_ne_top :
                numerator / denominator ≠ ⊤ :=
              ENNReal.div_ne_top
                (by simp [numerator]) hden_ne_zero
            have h_real1 :
                ((denominator / numerator)⁻¹).toReal =
                  sqrtRho / (2 + rho + sqrtRho) := by
              rw [ENNReal.toReal_inv, ENNReal.toReal_div]
              simp [denominator, numerator,
                ENNReal.toReal_ofReal hsqrt_pos.le,
                ENNReal.toReal_ofReal
                  (by positivity :
                    0 ≤ 2 + rho + sqrtRho)]
            have h_real2 :
                (numerator / denominator).toReal =
                  sqrtRho / (2 + rho + sqrtRho) := by
              rw [ENNReal.toReal_div]
              simp [denominator, numerator,
                ENNReal.toReal_ofReal hsqrt_pos.le,
                ENNReal.toReal_ofReal
                  (by positivity :
                    0 ≤ 2 + rho + sqrtRho)]
            exact h_inj _ _ hinv_ne_top
              hreverse_ne_top
              (by rw [h_real1, h_real2])
          rw [h9] at hinv
          have h_assoc :
              volume Y.union * ENNReal.ofReal sqrtRho /
                  ENNReal.ofReal (2 + rho + sqrtRho) =
                volume Y.union *
                  (ENNReal.ofReal sqrtRho /
                    ENNReal.ofReal (2 + rho + sqrtRho)) := by
            rw [div_eq_mul_inv, div_eq_mul_inv,
              mul_assoc]
          rw [h_assoc]
          exact mul_le_mul_of_nonneg_left hinv (by positivity)
    exact ⟨left, hfinal⟩

/-- Unit-ball compatibility wrapper for the tight height window. -/
lemma height_window_pigeonhole_tight
    {delta rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1) :
    ∃ left : ℝ,
      volume (Y.union ∩ wz1Lemma23CellHeightWindowSet rho hrho left) ≥
        volume Y.union * ENNReal.ofReal (Real.sqrt rho) /
          ENNReal.ofReal (2 + rho + Real.sqrt rho) := by
  apply height_window_pigeonhole_tight_of_paper_window
    Y hrho hrho_one
  · intro point hpoint
    have h := hball hpoint
    simp only [Metric.mem_closedBall, dist_zero_right] at h ⊢
    linarith
  · intro point hpoint
    have hnorm : ‖point‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hball hpoint
    simpa [Real.norm_eq_abs] using
      (PiLp.norm_apply_le point (2 : Fin 3)).trans hnorm

/-- Compatibility form with the former denominator `4`. -/
lemma height_window_pigeonhole
    {delta rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1) :
    ∃ left : ℝ,
      volume
          (Y.union ∩
            wz1Lemma23CellHeightWindowSet rho hrho left) ≥
        volume Y.union *
            ENNReal.ofReal (Real.sqrt rho) / 4 := by
  rcases
      height_window_pigeonhole_tight
        Y hrho hrho_one hball with
    ⟨left, hleft⟩
  refine ⟨left, ?_⟩
  have hden :
      ENNReal.ofReal
          (2 + rho + Real.sqrt rho) ≤ 4 := by
    have hsqrt_one : Real.sqrt rho ≤ 1 :=
      Real.sqrt_le_one.mpr hrho_one
    simpa using ENNReal.ofReal_le_ofReal
      (by linarith :
        2 + rho + Real.sqrt rho ≤ 4)
  exact
    (ENNReal.div_le_div_left hden _).trans hleft

end Kakeya.Assouad
