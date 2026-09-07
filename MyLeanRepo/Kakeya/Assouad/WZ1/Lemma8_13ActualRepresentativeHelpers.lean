import MyLeanRepo.Kakeya.Assouad.WZ1.PackingHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.FrostmanCoarseningHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.GreedyColoring
import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization.HeavyColorClass

/-!
# Helper lemmas for WZ1 Lemma 8.13 actual representative selection

1. `heavy_separated_color_class`: color proximity graph, retain heavy 4δ-separated class
2. `frostman_transfer_near_bijection`: transfer Frostman through near-bijection
-/

noncomputable section

namespace Kakeya.Assouad

open Finset Metric

/-! ### Local packing degree bound -/

/--
A `coarseScale`-separated set has at most 81 points within distance
`4 * coarseScale` of any given point.

Specializes `delta_separated_ball_card_bound` with `R = 4 * coarseScale`,
`delta = coarseScale`, `n = 2`: `(2*4 + 1)^2 = 81`.
-/
lemma coarse_neighbor_bound
    {E : DiscreteSet 2} {coarseScale : ℝ}
    (hscale : 0 < coarseScale)
    (hsep : E.IsDeltaSeparated coarseScale)
    (c : Point2) :
    (E.filter (fun y => dist y c < 4 * coarseScale)).card ≤ 81 := by
  let E' : DiscreteSet 2 := E.filter (fun y => dist y c < 4 * coarseScale)
  have hsep' : E'.IsDeltaSeparated coarseScale := by
    intro x hx y hy hxy
    have hxE : x ∈ E := (Finset.mem_filter.mp hx).1
    have hyE : y ∈ E := (Finset.mem_filter.mp hy).1
    exact hsep hxE hyE hxy
  have hball : ∀ y ∈ E', dist y c ≤ 4 * coarseScale := by
    intro y hy
    have h : dist y c < 4 * coarseScale := (Finset.mem_filter.mp hy).2
    exact le_of_lt h
  have hR : 0 < (4 * coarseScale) := by positivity
  have h1 : E'.enncard ≤ ENNReal.ofReal ((2 * (4 * coarseScale) / coarseScale + 1) ^ 2) :=
    delta_separated_ball_card_bound hscale hR hsep' c hball
  have h2 : (2 * (4 * coarseScale) / coarseScale + 1) ^ 2 = 81 := by
    field_simp [hscale.ne']
    norm_num
  rw [h2] at h1
  have h3 : (E'.card : ENNReal) ≤ (81 : ENNReal) := by
    simpa [DiscreteSet.enncard] using h1
  have h4 : E'.card ≤ 81 := by exact_mod_cast h3
  exact h4

/-! ### Heavy separated color class -/

/--
Given a δ-separated finite set in the plane, color its proximity graph
(adjacent when distance < 4δ) with 81 colors and retain a heavy color class.

The retained class is nonempty, has at least a 1/81 fraction of the cardinality,
and is 4δ-separated (same-color vertices are never adjacent).
-/
lemma heavy_separated_color_class
    {V : DiscreteSet 2} {delta : ℝ}
    (hdelta : 0 < delta)
    (hV_nonempty : V.Nonempty)
    (hsep : V.IsDeltaSeparated delta) :
    ∃ (S : DiscreteSet 2),
      S ⊆ V ∧
      S.Nonempty ∧
      V.enncard ≤ 81 * S.enncard ∧
      S.IsDeltaSeparated (4 * delta) := by
  classical
  let X : Type _ := {x : Point2 // x ∈ V}
  let adj : X → X → Prop := fun x y => x ≠ y ∧ dist (x : Point2) (y : Point2) < 4 * delta
  have hsymm : Std.Symm adj := by
    refine' ⟨_⟩
    intro x y h
    exact ⟨h.1.symm, by rw [dist_comm]; exact h.2⟩
  have hloopless : Std.Irrefl adj := by
    refine' ⟨_⟩
    intro x h
    exact h.1 rfl
  let G : SimpleGraph X :=
    { Adj := adj, symm := hsymm, loopless := hloopless }
  have hdeg : ∀ (v : X), G.degree v ≤ 80 := by
    intro v
    let x : Point2 := v.val
    let B : DiscreteSet 2 := V.filter (fun y => dist y x ≤ 4 * delta)
    have hB_sub : B ⊆ V := Finset.filter_subset _ _
    have hB_sep : B.IsDeltaSeparated delta := by
      intro p hp q hq hne
      exact hsep (hB_sub hp) (hB_sub hq) hne
    have hB_pack : B.enncard ≤ (81 : ENNReal) := by
      have h : B.enncard ≤ ENNReal.ofReal ((2 * (4 * delta) / delta + 1) ^ 2) :=
        delta_separated_ball_card_bound hdelta (by linarith) hB_sep x
          (fun y hy => (Finset.mem_filter.mp hy).2)
      have h_eq : (2 * (4 * delta) / delta + 1) ^ 2 = 81 := by
        field_simp [hdelta.ne'] <;> norm_num
      rw [h_eq] at h
      simpa using h
    have hB_card : B.card ≤ 81 := by
      have h' : (B.card : ENNReal) ≤ 81 := by simpa [DiscreteSet.enncard] using hB_pack
      exact_mod_cast h'
    let N : DiscreteSet 2 := V.filter (fun y => dist y x < 4 * delta)
    have hN_sub_B : N ⊆ B := by
      intro y hy
      have h_yV : y ∈ V := (Finset.mem_filter.mp hy).1
      have h_dist : dist y x < 4 * delta := (Finset.mem_filter.mp hy).2
      exact Finset.mem_filter.mpr ⟨h_yV, by linarith⟩
    have hN_card : N.card ≤ 81 := Finset.card_le_card hN_sub_B |>.trans hB_card
    have hxN : x ∈ N := by
      have h_xV : x ∈ V := v.property
      have h_dist : dist x x < 4 * delta := by simp [hdelta]
      exact Finset.mem_filter.mpr ⟨h_xV, h_dist⟩
    let neighborPoints : Finset Point2 := (G.neighborFinset v).image Subtype.val
    have h_image_eq : neighborPoints = N.erase x := by
      ext y
      simp only [neighborPoints, Finset.mem_image, Finset.mem_erase]
      constructor
      · rintro ⟨w, hw, rfl⟩
        have h_adj : G.Adj v w := (G.mem_neighborFinset v w).mp hw
        have h_ne : v ≠ w := h_adj.1
        have h_dist : dist x (w : Point2) < 4 * delta := h_adj.2
        have h_wV : (w : Point2) ∈ V := w.property
        have h_yN : (w : Point2) ∈ N := Finset.mem_filter.mpr ⟨h_wV, by rw [dist_comm]; exact h_dist⟩
        have h_yne_x : (w : Point2) ≠ x := by
          intro h_eq
          exact h_ne (Subtype.ext h_eq.symm)
        exact ⟨h_yne_x, h_yN⟩
      · rintro ⟨h_yne_x, h_yN⟩
        have h_yV : y ∈ V := (Finset.mem_filter.mp h_yN).1
        have h_dist : dist y x < 4 * delta := (Finset.mem_filter.mp h_yN).2
        let w : X := ⟨y, h_yV⟩
        have h_ne : v ≠ w := by
          intro h_eq
          exact h_yne_x (Eq.symm (congr_arg Subtype.val h_eq))
        have h_adj : G.Adj v w := by
          dsimp only [G, adj]
          exact ⟨h_ne, by rw [dist_comm]; exact h_dist⟩
        have hw : w ∈ G.neighborFinset v := (G.mem_neighborFinset v w).mpr h_adj
        exact ⟨w, hw, rfl⟩
    have h_inj : Set.InjOn (Subtype.val : X → Point2) (G.neighborFinset v) := by
      intro a _ b _ h
      exact Subtype.ext h
    have h_card_eq : (G.neighborFinset v).card = (N.erase x).card := by
      calc
        (G.neighborFinset v).card
          = neighborPoints.card := by rw [← Finset.card_image_of_injOn h_inj]
        _ = (N.erase x).card := by rw [h_image_eq]
    have h_erase_card : (N.erase x).card = N.card - 1 := by
      rw [Finset.card_erase_of_mem hxN]
    have h_main : (G.neighborFinset v).card ≤ 80 := by
      rw [h_card_eq, h_erase_card]
      omega
    have h_degree_eq : G.degree v = (G.neighborFinset v).card := by
      exact (SimpleGraph.card_neighborFinset_eq_degree G v).symm
    rw [h_degree_eq]
    exact h_main
  have hcolorable : G.Colorable 81 := SimpleGraph.colorable_of_forall_degree_le hdeg
  rcases hcolorable with ⟨c⟩
  let f : X → Fin 81 := c
  have hf : ∀ {v w : X}, G.Adj v w → f v ≠ f w := by
    intro v w h
    exact c.map_rel' h
  let color : Point2 → Fin 81 := fun y =>
    if h : y ∈ V then f ⟨y, h⟩ else 0
  let weight : Point2 → ENNReal := fun _ => 1
  have hheavy := exists_heavy_color_class V 81 (by norm_num) color weight
  rcases hheavy with ⟨c_col, hc⟩
  let S : DiscreteSet 2 := V.filter (fun y => color y = c_col)
  have hS_sub : S ⊆ V := Finset.filter_subset _ _
  have h_sum1 : (∑ i ∈ V, weight i) = V.enncard := by
    have h : (∑ i ∈ V, weight i) = (V.card : ENNReal) := by
      rw [Finset.sum_const] <;> simp
    rw [h] <;> rfl
  have h_sum2 : (∑ i ∈ S, weight i) = S.enncard := by
    have h : (∑ i ∈ S, weight i) = (S.card : ENNReal) := by
      rw [Finset.sum_const] <;> simp
    rw [h] <;> rfl
  have h_retention : V.enncard ≤ 81 * S.enncard := by
    rw [h_sum1, h_sum2] at hc
    exact hc
  have hS_nonempty : S.Nonempty := by
    by_contra h
    have hS_card_zero : S.card = 0 := by
      exact Nat.eq_zero_of_not_pos (fun hpos => h (Finset.card_pos.mp hpos))
    have hV_card_pos : 0 < V.card := Finset.card_pos.mpr hV_nonempty
    have hV_pos : 0 < V.enncard := by
      have h_eq : V.enncard = (V.card : ENNReal) := by rfl
      rw [h_eq] <;> exact_mod_cast hV_card_pos
    have h9 : S.enncard = 0 := by
      have h10 : S.enncard = (S.card : ENNReal) := by rfl
      rw [h10, hS_card_zero] <;> norm_num
    have h11 : V.enncard ≤ 81 * S.enncard := h_retention
    rw [h9] at h11
    have h_contra : V.enncard ≤ 0 := by
      rw [mul_zero] at h11 <;> exact h11
    exact not_le.mpr hV_pos h_contra
  have hS_sep : S.IsDeltaSeparated (4 * delta) := by
    intro y hy z hz hne
    have h_yV : y ∈ V := (Finset.mem_filter.mp hy).1
    have h_zV : z ∈ V := (Finset.mem_filter.mp hz).1
    have h_color_y : color y = c_col := (Finset.mem_filter.mp hy).2
    have h_color_z : color z = c_col := (Finset.mem_filter.mp hz).2
    have h_f_y : f ⟨y, h_yV⟩ = c_col := by
      simp [color, h_yV] at h_color_y ⊢ <;> exact h_color_y
    have h_f_z : f ⟨z, h_zV⟩ = c_col := by
      simp [color, h_zV] at h_color_z ⊢ <;> exact h_color_z
    have h_f_eq : f ⟨y, h_yV⟩ = f ⟨z, h_zV⟩ := by
      rw [h_f_y, h_f_z]
    by_contra h_dist
    have h_lt : dist y z < 4 * delta := by linarith
    let y' : X := ⟨y, h_yV⟩
    let z' : X := ⟨z, h_zV⟩
    have h_ne' : y' ≠ z' := by
      intro h_eq
      exact hne (congr_arg Subtype.val h_eq)
    have h_adj : G.Adj y' z' := by
      dsimp only [G, adj]
      exact ⟨h_ne', h_lt⟩
    have h_f_ne : f y' ≠ f z' := hf h_adj
    exact h_f_ne h_f_eq
  exact ⟨S, hS_sub, hS_nonempty, h_retention, hS_sep⟩

/-! ### Frostman transfer via near-bijection -/

/--
Transfer Frostman property from `A` to `B` through a near-bijection `f`
where each point moves by at most `delta`.

The Frostman constant degrades by a factor of 2:
- For `r + delta ≤ 1`, the radius enlarges from `r` to `r + delta ≤ 2r`.
- For `r + delta > 1`, we have `r > 1/2` (since `delta ≤ r`), and the
  trivial bound `ballCount ≤ encard` is absorbed by `2*C*r ≥ 1`.
-/
lemma frostman_transfer_near_bijection
    {A B : DiscreteSet 2} {delta : ℝ} {C : ENNReal}
    (hA_frost : A.IsFrostman delta 1 C)
    (f : Point2 → Point2)
    (f_inj : Set.InjOn f A)
    (f_image : B = A.image f)
    (f_close : ∀ x ∈ A, dist x (f x) ≤ delta)
    (hdelta : 0 < delta) (_hdelta1 : delta ≤ 1)
    (hC_one : (1 : ENNReal) ≤ C)
    (_hC_big : (2 : ENNReal) * C ≠ ⊤) :
    B.IsFrostman delta 1 (2 * C) := by
  have h_card_eq : A.enncard = B.enncard := by
    have h : B = A.image f := f_image
    rw [h]
    have h2 : (A.image f).card = A.card := Finset.card_image_of_injOn f_inj
    simp [DiscreteSet.enncard, h2]
  intro x r hdr hr1
  let B_ball : DiscreteSet 2 := B.filter (fun y => dist y x ≤ r)
  let A_ball : DiscreteSet 2 := A.filter (fun z => dist z x ≤ r + delta)

  have h_preimage : ∀ y ∈ B_ball, ∃ a ∈ A, f a = y ∧ a ∈ A_ball := by
    intro y hy
    have h_yB : y ∈ B := (Finset.mem_filter.mp hy).1
    rw [f_image] at h_yB
    rcases Finset.mem_image.mp h_yB with ⟨a, ha, rfl⟩
    have h_dist : dist a x ≤ r + delta := by
      calc dist a x
          ≤ dist a (f a) + dist (f a) x := dist_triangle _ _ _
        _ ≤ delta + r := by
          have h1 : dist a (f a) ≤ delta := f_close a ha
          have h2 : dist (f a) x ≤ r := (Finset.mem_filter.mp hy).2
          linarith
        _ = r + delta := by ring
    exact ⟨a, ha, rfl, Finset.mem_filter.mpr ⟨ha, h_dist⟩⟩

  classical
  let preimage : Point2 → Point2 := fun y =>
    if hy : y ∈ B_ball then
      (h_preimage y hy).choose
    else
      (0 : Point2)
  have hpreimage_spec : ∀ y ∈ B_ball,
      (preimage y ∈ A) ∧ f (preimage y) = y ∧ preimage y ∈ A_ball := by
    intro y hy
    have h9 : preimage y = (h_preimage y hy).choose := by
      simp [preimage, hy]
    rw [h9]
    exact (h_preimage y hy).choose_spec
  have hpreimage1 : ∀ y ∈ B_ball, preimage y ∈ A_ball :=
    fun y hy => (hpreimage_spec y hy).2.2
  have hpreimage2 : ∀ y ∈ B_ball, f (preimage y) = y :=
    fun y hy => (hpreimage_spec y hy).2.1
  have hpreimage_inj : Set.InjOn preimage (↑B_ball : Set Point2) := by
    intro y1 hy1 y2 hy2 h_eq
    have h1 : f (preimage y1) = y1 := hpreimage2 y1 hy1
    have h2 : f (preimage y2) = y2 := hpreimage2 y2 hy2
    have h3 : preimage y1 = preimage y2 := h_eq
    rw [h3] at h1
    exact h1.symm.trans h2
  let img : Finset Point2 := B_ball.image preimage
  have h_image_subset : img ⊆ A_ball := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    exact hpreimage1 y hy
  have h_card_le : B_ball.card ≤ A_ball.card := by
    have h3 : img.card = B_ball.card := Finset.card_image_of_injOn hpreimage_inj
    have h4 : img.card ≤ A_ball.card := Finset.card_le_card h_image_subset
    rw [h3] at h4
    exact h4

  have h_ballCount_le : B.ballCount x r ≤ A.ballCount x (r + delta) := by
    have h : (B_ball.card : ENNReal) ≤ (A_ball.card : ENNReal) := by exact_mod_cast h_card_le
    simpa [DiscreteSet.ballCount] using h

  by_cases h_case : r + delta ≤ 1
  · -- Case 1: r + delta ≤ 1
    have hA : A.ballCount x (r + delta) ≤
        C * Kakeya.realRpowENN (r + delta) 1 * A.enncard :=
      hA_frost x (r + delta) (by linarith) h_case
    have h_rpow : Kakeya.realRpowENN (r + delta) 1 ≤ 2 * Kakeya.realRpowENN r 1 := by
      have h1 : r + delta ≤ 2 * r := by linarith
      have h2 : 0 ≤ r := by linarith
      simp only [Kakeya.realRpowENN]
      have h3 : Real.rpow (r + delta) 1 ≤ Real.rpow (2 * r) 1 :=
        Real.rpow_le_rpow (by linarith) h1 (by norm_num)
      have h4 : Real.rpow (2 * r) 1 = 2 * r := by simp
      have h5 : Real.rpow r 1 = r := by simp
      have h6 : Real.rpow (r + delta) 1 ≤ 2 * r := by
        calc Real.rpow (r + delta) 1 ≤ Real.rpow (2 * r) 1 := h3
             _ = 2 * r := h4
      have h7 : ENNReal.ofReal (Real.rpow (r + delta) 1) ≤ ENNReal.ofReal (2 * r) :=
        ENNReal.ofReal_le_ofReal h6
      have h8 : ENNReal.ofReal (2 * r) = (2 : ENNReal) * ENNReal.ofReal r := by
        have h9 : ENNReal.ofReal (2 * r) = ENNReal.ofReal (r + r) := by ring_nf
        rw [h9]
        have h10 : ENNReal.ofReal (r + r) = ENNReal.ofReal r + ENNReal.ofReal r :=
          ENNReal.ofReal_add h2 h2
        rw [h10]
        ring
      rw [h8] at h7
      have h9 : ENNReal.ofReal r = Kakeya.realRpowENN r 1 := by
        simp [Kakeya.realRpowENN, Real.rpow_one]
      rw [h9] at h7
      exact h7
    calc B.ballCount x r
        ≤ A.ballCount x (r + delta) := h_ballCount_le
      _ ≤ C * Kakeya.realRpowENN (r + delta) 1 * A.enncard := hA
      _ ≤ C * (2 * Kakeya.realRpowENN r 1) * A.enncard := by gcongr
      _ = (2 * C) * Kakeya.realRpowENN r 1 * B.enncard := by
        rw [h_card_eq] <;> ring
  · -- Case 2: r + delta > 1
    have h_r_gt_half : 1 / 2 < r := by linarith
    have h_r_nonneg : 0 ≤ r := by linarith
    have h1 : (1 : ENNReal) ≤ (2 * C) * Kakeya.realRpowENN r 1 := by
      have h2 : Kakeya.realRpowENN r 1 = ENNReal.ofReal r := by
        simp [Kakeya.realRpowENN, Real.rpow_one]
      rw [h2]
      have h4 : (1 / 2 : ℝ) ≤ r := by linarith
      have h5 : (1 : ENNReal) ≤ (2 * C) * ENNReal.ofReal (1 / 2 : ℝ) := by
        have h6 : (2 * C) * ENNReal.ofReal (1 / 2 : ℝ) = C := by
          have h7 : (2 : ENNReal) * ENNReal.ofReal (1 / 2 : ℝ) = 1 := by
            have h72 : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ := by
              simp [ENNReal.ofReal_inv_of_pos]
            rw [h72]
            exact ENNReal.mul_inv_cancel (by norm_num) (by simp)
          calc
            (2 * C) * ENNReal.ofReal (1 / 2 : ℝ)
              = C * ((2 : ENNReal) * ENNReal.ofReal (1 / 2 : ℝ)) := by ring
            _ = C * 1 := by rw [h7]
            _ = C := by ring
        rw [h6]
        exact hC_one
      have h7 : ENNReal.ofReal (1 / 2 : ℝ) ≤ ENNReal.ofReal r :=
        ENNReal.ofReal_le_ofReal h4
      have h8 : (2 * C) * ENNReal.ofReal (1 / 2 : ℝ) ≤ (2 * C) * ENNReal.ofReal r :=
        (mul_le_mul_right h7) (2 * C)
      exact h5.trans h8
    have h_trivial : B.ballCount x r ≤ B.enncard := by
      simp only [DiscreteSet.ballCount, DiscreteSet.enncard]
      have h : (B.filter (fun y => dist y x ≤ r)).card ≤ B.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      exact_mod_cast h
    calc B.ballCount x r
        ≤ B.enncard := h_trivial
      _ ≤ (2 * C) * Kakeya.realRpowENN r 1 * B.enncard :=
        le_mul_of_one_le_left' h1

end Kakeya.Assouad
