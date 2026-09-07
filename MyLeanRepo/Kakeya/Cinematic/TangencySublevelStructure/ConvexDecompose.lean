import MyLeanRepo.Kakeya.Cinematic.TangencySublevelStructure.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Deriv

/-!
# Concise convex sublevel decomposition

Drops the boundary-value properties from `convex_sublevel_two_intervals'`.
-/

namespace Kakeya.Cinematic

lemma convex_sublevel_decompose
    {H : ℝ → ℝ} {a b c d δ : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hc : a ≤ c) (hd : d ≤ b)
    (H_cont : Continuous H)
    (H_conv : ConvexOn ℝ (Set.Icc a b) H)
    (hδ : 0 < δ) (hc0 : 0 ≤ c) (hd1 : d ≤ 1) :
    ∃ (pieces : IntervalFamily), pieces.card ≤ 2 ∧
      (∀ (x : UnitPoint), x ∈ pieces.union ↔
        (x : ℝ) ∈ Set.Icc c d ∧ |H (x : ℝ)| ≤ δ) ∧
      (∀ (j1 j2 : Fin pieces.card), j1 ≠ j2 →
        Disjoint (pieces.interval j1).carrier (pieces.interval j2).carrier) := by
  let S : Set ℝ := {x ∈ Set.Icc c d | |H x| ≤ δ}
  have hS_closed : IsClosed S :=
    isClosed_Icc.inter (IsClosed.preimage (continuous_abs.comp H_cont) isClosed_Iic)
  have hS_bddAbove : BddAbove S := ⟨d, fun r hr => hr.1.2⟩
  have hS_bddBelow : BddBelow S := ⟨c, fun r hr => hr.1.1⟩

  by_cases hS_empty : S = ∅
  · let pieces : IntervalFamily := ⟨0, Fin.elim0⟩
    refine' ⟨pieces, by norm_num, _⟩
    constructor
    · intro x
      have h1 : x ∉ pieces.union := by intro h; rcases h with ⟨i, _⟩; exact Fin.elim0 i
      have h2 : ¬((x : ℝ) ∈ Set.Icc c d ∧ |H (x : ℝ)| ≤ δ) := by
        intro h; have h3 : (x : ℝ) ∈ S := by simpa [S] using h
        rw [hS_empty] at h3; simpa using h3
      simp only [h1, h2]
    · intro j1 j2 hne; exfalso; exact hne (Fin.elim0 j1)

  · have hS_nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS_empty
    let l := sInf S
    let r := sSup S
    have hl_in : l ∈ S := hS_closed.csInf_mem hS_nonempty hS_bddBelow
    have hr_in : r ∈ S := hS_closed.csSup_mem hS_nonempty hS_bddAbove
    have h_lr : l ≤ r := Real.sInf_le_sSup S hS_bddBelow hS_bddAbove
    have h_l_cd : l ∈ Set.Icc c d := hl_in.1
    have h_r_cd : r ∈ Set.Icc c d := hr_in.1
    have h_l0 : 0 ≤ l := by linarith [hc0, h_l_cd.1]
    have h_l1 : l ≤ 1 := by linarith [hd1, h_l_cd.2]
    have h_r0 : 0 ≤ r := by linarith [hc0, h_r_cd.1]
    have h_r1 : r ≤ 1 := by linarith [hd1, h_r_cd.2]
    have h_lr_sub : Set.Icc l r ⊆ Set.Icc a b := by
      intro x hx
      exact ⟨by linarith [h_l_cd.1, hx.1], by linarith [h_r_cd.2, hx.2]⟩

    -- H(x) ≤ δ for x ∈ [l,r] by convexity
    have hH_le : ∀ x ∈ Set.Icc l r, H x ≤ δ := by
      intro x hx
      have h_l_in' : l ∈ Set.Icc a b := h_lr_sub ⟨by linarith [h_l_cd.1], by linarith [h_l_cd.2]⟩
      have h_r_in' : r ∈ Set.Icc a b := h_lr_sub ⟨by linarith [h_r_cd.1], by linarith [h_r_cd.2]⟩
      have hHl_le : H l ≤ δ := (abs_le.mp hl_in.2).2
      have hHr_le : H r ≤ δ := (abs_le.mp hr_in.2).2
      by_cases h_eq : l = r
      · have hx' : x = l := by
          have h1 : l ≤ x := hx.1
          have h2 : x ≤ r := hx.2
          have h3 : r = l := h_eq.symm
          rw [h3] at h2
          exact le_antisymm h2 h1
        rw [hx']
        exact hHl_le
      · have hlt : l < r := lt_of_le_of_ne h_lr h_eq
        set t : ℝ := (r - x) / (r - l) with ht_def
        have ht0 : 0 ≤ t := by
          rw [ht_def]
          apply div_nonneg
          · exact sub_nonneg.mpr hx.2
          · exact sub_nonneg.mpr hlt.le
        have h1t0 : 0 ≤ 1 - t := by
          have h_pos : 0 < r - l := by linarith
          have h_le : t ≤ 1 := by
            rw [ht_def]
            have h : r - x ≤ r - l := by linarith [hx.1]
            exact (div_le_one h_pos).mpr h
          linarith
        have h_sum : t + (1 - t) = 1 := by ring
        have h_eq2 : t * l + (1 - t) * r = x := by
          rw [ht_def]
          field_simp [hlt.ne'] <;> ring
        have h4 : H (t * l + (1 - t) * r) ≤ t * H l + (1 - t) * H r :=
          H_conv.2 h_l_in' h_r_in' ht0 h1t0 h_sum
        rw [h_eq2] at h4
        have h5 : t * H l + (1 - t) * H r ≤ δ := by
          have h6 : t * H l ≤ t * δ := by gcongr
          have h7 : (1 - t) * H r ≤ (1 - t) * δ := by gcongr
          linarith
        linarith

    let G : Set ℝ := {x ∈ Set.Ioo l r | H x < -δ}

    -- G is convex
    have hG_conv : Convex ℝ G := by
      intro x hx y hy u v hu hv huv
      have hz1 : u * x + v * y ∈ Set.Ioo l r :=
        (convex_Ioo l r) hx.1 hy.1 hu hv huv
      have h_x_Icc : x ∈ Set.Icc l r := ⟨le_of_lt hx.1.1, le_of_lt hx.1.2⟩
      have h_y_Icc : y ∈ Set.Icc l r := ⟨le_of_lt hy.1.1, le_of_lt hy.1.2⟩
      have h_x_ab : x ∈ Set.Icc a b := h_lr_sub h_x_Icc
      have h_y_ab : y ∈ Set.Icc a b := h_lr_sub h_y_Icc
      have hz2 : H (u * x + v * y) ≤ u * H x + v * H y :=
        H_conv.2 h_x_ab h_y_ab hu hv huv
      have h3 : u * H x + v * H y < -δ := by
        by_cases hu0 : u = 0
        · have v1 : v = 1 := by linarith [huv, hu0]
          rw [hu0, v1]; simpa using hy.2
        · by_cases hv0 : v = 0
          · have u1 : u = 1 := by linarith [huv, hv0]
            rw [hv0, u1]; simpa using hx.2
          · have hu_pos : 0 < u := by
              by_contra h
              have h' : u = 0 := by linarith
              exact hu0 h'
            have hv_pos : 0 < v := by
              by_contra h
              have h' : v = 0 := by linarith
              exact hv0 h'
            have h4 : u * H x < u * (-δ) := mul_lt_mul_of_pos_left hx.2 hu_pos
            have h5 : v * H y < v * (-δ) := mul_lt_mul_of_pos_left hy.2 hv_pos
            have h6 : u * (-δ) + v * (-δ) = -δ := by
              have h7 : u + v = 1 := huv
              calc u * (-δ) + v * (-δ) = -(u + v) * δ := by ring
                _ = -δ := by rw [h7] <;> ring
            have h8 : u * H x + v * H y < u * (-δ) + v * (-δ) := add_lt_add h4 h5
            rw [h6] at h8
            exact h8
      have h9 : H (u * x + v * y) < -δ := by
        calc H (u * x + v * y)
          ≤ u * H x + v * H y := hz2
        _ < -δ := h3
      exact ⟨hz1, h9⟩

    have hG_open : IsOpen G :=
      isOpen_Ioo.inter (IsOpen.preimage H_cont isOpen_Iio)

    by_cases hG_empty : G = ∅
    · -- Case G empty: S = [l,r], one interval
      have hS_eq : S = Set.Icc l r := by
        apply Set.Subset.antisymm
        · intro x hx
          have h1 : l ≤ x := csInf_le hS_bddBelow hx
          have h2 : x ≤ r := le_csSup hS_bddAbove hx
          exact ⟨h1, h2⟩
        · intro x hx
          have h_x_cd : x ∈ Set.Icc c d := by
            constructor
            · calc c ≤ l := h_l_cd.1
                 _ ≤ x := hx.1
            · calc x ≤ r := hx.2
                 _ ≤ d := h_r_cd.2
          have hH_le_x : H x ≤ δ := hH_le x hx
          have hH_ge : H x ≥ -δ := by
            by_contra h4
            have h5 : H x < -δ := by linarith
            have h6 : x ∈ Set.Ioo l r := by
              by_cases h7 : x = l
              · rw [h7] at h5
                have h8 : -δ ≤ H l := (abs_le.mp hl_in.2).1
                linarith
              · by_cases h9 : x = r
                · rw [h9] at h5
                  have h10 : -δ ≤ H r := (abs_le.mp hr_in.2).1
                  linarith
                · have h12 : l < x := by
                    have h13 : l ≤ x := hx.1
                    have h14 : l ≠ x := by intro h15; exact h7 h15.symm
                    exact lt_of_le_of_ne h13 h14
                  have h16 : x < r := by
                    have h17 : x ≤ r := hx.2
                    have h18 : r ≠ x := by intro h19; exact h9 h19.symm
                    exact lt_of_le_of_ne h17 h18.symm
                  exact ⟨h12, h16⟩
            have h7 : x ∈ G := ⟨h6, h5⟩
            rw [hG_empty] at h7
            simpa using h7
          have h_abs : |H x| ≤ δ := by
            rw [abs_le] <;> constructor <;> linarith
          exact ⟨h_x_cd, h_abs⟩
      let J : ParameterInterval := ⟨l, r, ⟨h_l0, h_l1⟩, ⟨h_r0, h_r1⟩, h_lr⟩
      let pieces : IntervalFamily := ⟨1, fun _ => J⟩
      have hJ_carrier : J.carrier = {x : UnitPoint | (x : ℝ) ∈ Set.Icc l r} := by
        ext x; simp [J, ParameterInterval.carrier]
      refine' ⟨pieces, by norm_num, _⟩
      constructor
      · intro x
        simp only [pieces, IntervalFamily.union, Set.mem_setOf_eq]
        constructor
        · rintro ⟨i, hi⟩
          have h_i0 : i = 0 := by
            have h : i.val < 1 := by simpa [pieces] using i.is_lt
            have h2 : i.val = 0 := by omega
            exact Fin.val_injective h2
          have h_hi : x ∈ J.carrier := by
            have h_interval : (pieces.interval i) = J := by
              rw [h_i0] <;> simp [pieces]
            exact h_interval ▸ hi
          have h_x_lr : (x : ℝ) ∈ Set.Icc l r := by
            rw [hJ_carrier] at h_hi; simpa using h_hi
          have h_x_S : (x : ℝ) ∈ S := by rw [hS_eq]; exact h_x_lr
          exact ⟨h_x_S.1, h_x_S.2⟩
        · rintro ⟨h_x_cd, h_abs⟩
          have h_x_S : (x : ℝ) ∈ S := ⟨h_x_cd, h_abs⟩
          have h_x_lr : (x : ℝ) ∈ Set.Icc l r := by rw [hS_eq] at h_x_S; exact h_x_S
          refine' ⟨0, _⟩
          rw [hJ_carrier]; simpa using h_x_lr
      · intro j1 j2 hne
        have h1 : j1 = j2 := by
          have h_j1_val : j1.val < 1 := by simpa [pieces] using j1.is_lt
          have h_j2_val : j2.val < 1 := by simpa [pieces] using j2.is_lt
          have h1 : j1.val = 0 := by omega
          have h2 : j2.val = 0 := by omega
          exact Fin.val_injective (by omega)
        exfalso; exact hne h1

    · -- Case G nonempty: S = [l,u] ∪ [v,r], two intervals
      have hG_nonempty : G.Nonempty := Set.nonempty_iff_ne_empty.mpr hG_empty
      let u := sInf G
      let v := sSup G
      have hG_bddBelow : BddBelow G := ⟨l, fun x hx => le_of_lt hx.1.1⟩
      have hG_bddAbove : BddAbove G := ⟨r, fun x hx => le_of_lt hx.1.2⟩

      have h_uv_lt : u < v := by
        rcases hG_nonempty with ⟨x, hx⟩
        rcases Metric.isOpen_iff.mp hG_open x hx with ⟨ε, hε_pos, hball⟩
        have h1 : x - ε / 2 ∈ G := hball (by
          simp only [Metric.mem_ball, Real.dist_eq]
          have h : dist (x - ε / 2) x < ε := by
            rw [Real.dist_eq]
            have h2 : (x - ε / 2) - x = -(ε / 2) := by ring
            rw [h2, abs_neg, abs_of_pos (by positivity)]
            linarith
          exact h)
        have h2 : x + ε / 2 ∈ G := hball (by
          simp only [Metric.mem_ball, Real.dist_eq]
          have h : dist (x + ε / 2) x < ε := by
            rw [Real.dist_eq]
            have h2 : (x + ε / 2) - x = ε / 2 := by ring
            rw [h2, abs_of_pos (by positivity)]
            linarith
          exact h)
        have h3 : u ≤ x - ε / 2 := csInf_le hG_bddBelow h1
        have h4 : x + ε / 2 ≤ v := le_csSup hG_bddAbove h2
        linarith

      have h_u_ge_l : l ≤ u := le_csInf hG_nonempty (fun x hx => le_of_lt hx.1.1)
      have h_v_le_r : v ≤ r := csSup_le hG_nonempty (fun x hx => le_of_lt hx.1.2)
      have h_u0 : 0 ≤ u := by linarith [h_l0, h_u_ge_l]
      have h_u1 : u ≤ 1 := by linarith [h_l1, h_u_ge_l]
      have h_v0 : 0 ≤ v := by linarith [h_r0, h_v_le_r]
      have h_v1 : v ≤ 1 := by linarith [h_r1, h_v_le_r]

      -- G = (u,v)
      have hG_eq : G = Set.Ioo u v := by
        apply Set.Subset.antisymm
        · intro x hx
          have h1 : u ≤ x := csInf_le hG_bddBelow hx
          have h2 : x ≤ v := le_csSup hG_bddAbove hx
          have h3 : u ≠ x := by
            intro h4
            have hux : u ∈ G := h4 ▸ hx
            rcases Metric.isOpen_iff.mp hG_open u hux with ⟨ε, hε_pos, hball⟩
            have h5 : u - ε / 2 ∈ G := hball (by
              simp only [Metric.mem_ball, Real.dist_eq]
              have h : dist (u - ε / 2) u < ε := by
                rw [Real.dist_eq]
                have h2 : (u - ε / 2) - u = -(ε / 2) := by ring
                rw [h2, abs_neg, abs_of_pos (by positivity)]
                linarith
              exact h)
            have h6 : u ≤ u - ε / 2 := csInf_le hG_bddBelow h5
            linarith
          have h4 : u < x := lt_of_le_of_ne h1 h3
          have h5 : x ≠ v := by
            intro h6
            have hvx : v ∈ G := h6 ▸ hx
            rcases Metric.isOpen_iff.mp hG_open v hvx with ⟨ε, hε_pos, hball⟩
            have h7 : v + ε / 2 ∈ G := hball (by
              simp only [Metric.mem_ball, Real.dist_eq]
              have h : dist (v + ε / 2) v < ε := by
                rw [Real.dist_eq]
                have h2 : (v + ε / 2) - v = ε / 2 := by ring
                rw [h2, abs_of_pos (by positivity)]
                linarith
              exact h)
            have h8 : v + ε / 2 ≤ v := le_csSup hG_bddAbove h7
            linarith
          have h6 : x < v := lt_of_le_of_ne h2 h5
          exact ⟨h4, h6⟩
        · intro x hx
          have h1 : ∃ p ∈ G, p < x := by
            by_contra h2
            have h3 : ∀ y ∈ G, x ≤ y := by
              intro y hy
              by_contra h4
              have h5 : y < x := by linarith
              exact h2 ⟨y, hy, h5⟩
            have h4 : x ≤ u := le_csInf hG_nonempty h3
            have h5 : u < x := hx.1
            linarith
          rcases h1 with ⟨p, hpG, hplx⟩
          have h2 : ∃ q ∈ G, x < q := by
            by_contra h3
            have h4 : ∀ y ∈ G, y ≤ x := by
              intro y hy
              by_contra h5
              have h6 : x < y := by linarith
              exact h3 ⟨y, hy, h6⟩
            have h5 : v ≤ x := csSup_le hG_nonempty h4
            have h6 : x < v := hx.2
            linarith
          rcases h2 with ⟨q, hqG, hxltq⟩
          let t : ℝ := (q - x) / (q - p)
          have ht0 : 0 ≤ t := by
            dsimp only [t]
            apply div_nonneg <;> linarith
          have h1t0 : 0 ≤ 1 - t := by
            dsimp only [t]
            have h_pos : 0 < q - p := by linarith
            have h_le : t ≤ 1 := by
              have h : q - x ≤ q - p := by linarith
              exact (div_le_one h_pos).mpr h
            linarith
          have h_sum : t + (1 - t) = 1 := by ring
          have h4 : t * p + (1 - t) * q = x := by
            dsimp only [t]
            field_simp [show q - p ≠ 0 by linarith] <;> ring
          have h5 : t * p + (1 - t) * q ∈ G :=
            hG_conv hpG hqG ht0 h1t0 h_sum
          rw [h4] at h5
          exact h5

      -- Boundary values H u, H v ≥ -δ
      have hHu_ge : H u ≥ -δ := by
        by_cases h_lu : l < u
        · by_contra h
          have h5 : H u < -δ := by linarith
          have h6 : u ∈ Set.Ioo l r := ⟨h_lu, by linarith⟩
          have h7 : u ∈ G := ⟨h6, h5⟩
          rw [hG_eq] at h7
          exact h7.1.false
        · have h_ul : u = l := by linarith
          rw [h_ul]
          exact (abs_le.mp hl_in.2).1
      have hHv_ge : H v ≥ -δ := by
        by_cases h_vr : v < r
        · by_contra h
          have h5 : H v < -δ := by linarith
          have h6 : v ∈ Set.Ioo l r := ⟨by linarith, h_vr⟩
          have h7 : v ∈ G := ⟨h6, h5⟩
          rw [hG_eq] at h7
          exact h7.2.false
        · have h_ve : v = r := by linarith
          rw [h_ve]
          exact (abs_le.mp hr_in.2).1

      -- S = [l,u] ∪ [v,r]
      have hS_eq : S = Set.Icc l u ∪ Set.Icc v r := by
        apply Set.Subset.antisymm
        · intro x hx
          have h1 : l ≤ x := csInf_le hS_bddBelow hx
          have h2 : x ≤ r := le_csSup hS_bddAbove hx
          by_cases h3 : x ≤ u
          · exact Or.inl ⟨h1, h3⟩
          · have h4 : u < x := by linarith
            by_cases h5 : v ≤ x
            · exact Or.inr ⟨h5, h2⟩
            · have h6 : x < v := by linarith
              have h7 : x ∈ Set.Ioo u v := ⟨h4, h6⟩
              have h8 : x ∈ G := by rw [hG_eq]; exact h7
              have h9 : H x < -δ := h8.2
              have h10 : |H x| > δ := by
                have h9' : H x < 0 := by linarith [hδ]
                have h11 : |H x| = -(H x) := abs_of_neg h9'
                rw [h11] <;> linarith
              have h12 : |H x| ≤ δ := hx.2
              linarith
        · intro x hx
          rcases hx with (hx | hx)
          · have h_x_cd : x ∈ Set.Icc c d := by
              constructor
              · calc c ≤ l := h_l_cd.1
                   _ ≤ x := hx.1
              · calc x ≤ u := hx.2
                   _ ≤ v := by linarith
                   _ ≤ r := h_v_le_r
                   _ ≤ d := h_r_cd.2
            have h_x_le_r : x ≤ r := by
              have h1 : x ≤ u := hx.2
              have h2 : u < v := h_uv_lt
              have h3 : v ≤ r := h_v_le_r
              linarith
            have hH_le_x : H x ≤ δ := hH_le x ⟨hx.1, h_x_le_r⟩
            have hH_ge : H x ≥ -δ := by
              by_cases h_xl : x = l
              · rw [h_xl]; exact (abs_le.mp hl_in.2).1
              · by_cases h_xu : x = u
                · rw [h_xu]; exact hHu_ge
                · have h_ltx : l < x := lt_of_le_of_ne hx.1 (Ne.symm h_xl)
                  have h_xtu : x < u := lt_of_le_of_ne hx.2 h_xu
                  have h_xIoo : x ∈ Set.Ioo l r := ⟨h_ltx, by linarith⟩
                  by_cases h : H x < -δ
                  · have h10 : x ∈ G := ⟨h_xIoo, h⟩
                    rw [hG_eq] at h10
                    have h11 : u < x := h10.1
                    have h_contra : x < u := h_xtu
                    linarith
                  · have h2 : H x ≥ -δ := by linarith
                    exact h2
            have h_abs : |H x| ≤ δ := by
              rw [abs_le] <;> constructor <;> linarith
            exact ⟨h_x_cd, h_abs⟩
          · have h_x_cd : x ∈ Set.Icc c d := by
              constructor
              · calc c ≤ l := h_l_cd.1
                   _ ≤ u := h_u_ge_l
                   _ ≤ v := by linarith
                   _ ≤ x := hx.1
              · calc x ≤ r := hx.2
                   _ ≤ d := h_r_cd.2
            have h_l_le_x : l ≤ x := by
              have h1 : l ≤ u := h_u_ge_l
              have h2 : u < v := h_uv_lt
              have h3 : v ≤ x := hx.1
              linarith
            have hH_le_x : H x ≤ δ := hH_le x ⟨h_l_le_x, hx.2⟩
            have hH_ge : H x ≥ -δ := by
              by_cases h_xv : x = v
              · rw [h_xv]; exact hHv_ge
              · by_cases h_xr : x = r
                · rw [h_xr]; exact (abs_le.mp hr_in.2).1
                · have h_vtx : v < x := lt_of_le_of_ne hx.1 (Ne.symm h_xv)
                  have h_xtr : x < r := lt_of_le_of_ne hx.2 h_xr
                  have h_xIoo : x ∈ Set.Ioo l r := ⟨by linarith, h_xtr⟩
                  by_cases h : H x < -δ
                  · have h10 : x ∈ G := ⟨h_xIoo, h⟩
                    rw [hG_eq] at h10
                    have h11 : x < v := h10.2
                    have h_contra : v < x := h_vtx
                    linarith
                  · have h2 : H x ≥ -δ := by linarith
                    exact h2
            have h_abs : |H x| ≤ δ := by
              rw [abs_le] <;> constructor <;> linarith
            exact ⟨h_x_cd, h_abs⟩

      let J1 : ParameterInterval := ⟨l, u, ⟨h_l0, h_l1⟩, ⟨h_u0, h_u1⟩, by linarith⟩
      let J2 : ParameterInterval := ⟨v, r, ⟨h_v0, h_v1⟩, ⟨h_r0, h_r1⟩, by linarith⟩
      let pieces : IntervalFamily := ⟨2, fun i => if i = 0 then J1 else J2⟩
      have h_f0 : pieces.interval 0 = J1 := by
        simp only [pieces, if_pos rfl, if_true]
      have h_f1 : pieces.interval 1 = J2 := by
        have h_ne : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
        simp only [pieces, if_neg h_ne, if_false]
      have hJ1_carrier : J1.carrier = {x : UnitPoint | (x : ℝ) ∈ Set.Icc l u} := by
        ext x; simp [J1, ParameterInterval.carrier]
      have hJ2_carrier : J2.carrier = {x : UnitPoint | (x : ℝ) ∈ Set.Icc v r} := by
        ext x; simp [J2, ParameterInterval.carrier]
      refine' ⟨pieces, by norm_num, _⟩
      constructor
      · intro x
        simp only [pieces, IntervalFamily.union, Set.mem_setOf_eq]
        constructor
        · rintro ⟨i, hi⟩
          have h_i2 : i.val < 2 := by simpa [pieces] using i.is_lt
          have h : i.val = 0 ∨ i.val = 1 := by omega
          rcases h with (h | h)
          · have h_eq : i = 0 := Fin.val_injective h
            have h_hi : x ∈ J1.carrier := by
              have h_if : (if i = 0 then J1 else J2) = J1 := by
                rw [if_pos h_eq]
              exact h_if ▸ hi
            have h_x_lr : (x : ℝ) ∈ Set.Icc l u := by
              rw [hJ1_carrier] at h_hi; simpa using h_hi
            have h_x_S : (x : ℝ) ∈ S := by rw [hS_eq]; exact Or.inl h_x_lr
            exact ⟨h_x_S.1, h_x_S.2⟩
          · have h_eq : i = 1 := Fin.val_injective h
            have h_hi : x ∈ J2.carrier := by
              have h_if : (if i = 0 then J1 else J2) = J2 := by
                have h_ne : i ≠ 0 := by
                  intro h_contra
                  rw [h_contra] at h_eq
                  <;> contradiction
                rw [if_neg h_ne]
              exact h_if ▸ hi
            have h_x_lr : (x : ℝ) ∈ Set.Icc v r := by
              rw [hJ2_carrier] at h_hi; simpa using h_hi
            have h_x_S : (x : ℝ) ∈ S := by rw [hS_eq]; exact Or.inr h_x_lr
            exact ⟨h_x_S.1, h_x_S.2⟩
        · rintro ⟨h_x_cd, h_abs⟩
          have h_x_S : (x : ℝ) ∈ S := ⟨h_x_cd, h_abs⟩
          have h_x_union : (x : ℝ) ∈ Set.Icc l u ∪ Set.Icc v r := by
            rw [hS_eq] at h_x_S; exact h_x_S
          rcases h_x_union with (h_x_lr | h_x_lr)
          · have h_goal : x ∈ J1.carrier := by rw [hJ1_carrier]; simpa using h_x_lr
            have h_if : (if (0 : Fin 2) = 0 then J1 else J2) = J1 := by
              rw [if_pos rfl]
            exact ⟨0, h_if ▸ h_goal⟩
          · have h_goal : x ∈ J2.carrier := by rw [hJ2_carrier]; simpa using h_x_lr
            have h_if : (if (1 : Fin 2) = 0 then J1 else J2) = J2 := by
              have h_ne : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
              rw [if_neg h_ne]
            exact ⟨1, h_if ▸ h_goal⟩
      · intro j1 j2 hne
        have h_j1_lt : j1.val < 2 := by simpa [pieces] using j1.is_lt
        have h_j2_lt : j2.val < 2 := by simpa [pieces] using j2.is_lt
        have h1 : j1 = 0 ∨ j1 = 1 := by
          have h : j1.val = 0 ∨ j1.val = 1 := by omega
          rcases h with (h | h)
          · left; exact Fin.val_injective h
          · right; exact Fin.val_injective h
        rcases h1 with (rfl | rfl)
        · have h2 : j2 = 0 ∨ j2 = 1 := by
            have h : j2.val = 0 ∨ j2.val = 1 := by omega
            rcases h with (h | h)
            · left; exact Fin.val_injective h
            · right; exact Fin.val_injective h
          rcases h2 with (rfl | rfl)
          · exfalso; exact hne rfl
          · have h_disj : Disjoint J1.carrier J2.carrier := by
              rw [Set.disjoint_left]
              intro x hx1 hx2
              have h1 : (x : ℝ) ∈ Set.Icc l u := by rw [hJ1_carrier] at hx1; simpa using hx1
              have h2 : (x : ℝ) ∈ Set.Icc v r := by rw [hJ2_carrier] at hx2; simpa using hx2
              have h_x_le_u : (x : ℝ) ≤ u := h1.2
              have h_v_le_x : v ≤ (x : ℝ) := h2.1
              linarith [h_uv_lt]
            simpa [pieces, h_f0, h_f1] using h_disj
        · have h2 : j2 = 0 ∨ j2 = 1 := by
            have h : j2.val = 0 ∨ j2.val = 1 := by omega
            rcases h with (h | h)
            · left; exact Fin.val_injective h
            · right; exact Fin.val_injective h
          rcases h2 with (rfl | rfl)
          · have h_disj : Disjoint J2.carrier J1.carrier := by
              rw [Set.disjoint_left]
              intro x hx1 hx2
              have h1 : (x : ℝ) ∈ Set.Icc v r := by rw [hJ2_carrier] at hx1; simpa using hx1
              have h2 : (x : ℝ) ∈ Set.Icc l u := by rw [hJ1_carrier] at hx2; simpa using hx2
              have h_x_le_u : (x : ℝ) ≤ u := h2.2
              have h_v_le_x : v ≤ (x : ℝ) := h1.1
              linarith [h_uv_lt]
            simpa [pieces, h_f0, h_f1] using h_disj
          · exfalso; exact hne rfl

end Kakeya.Cinematic
