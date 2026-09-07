import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameters
import MyLeanRepo.Kakeya.Streamlined.Families

/-!
# Mass-based c-window extraction for shadings
-/

noncomputable section

open MeasureTheory Set Finset

namespace Kakeya.Assouad

private lemma weighted_pigeonhole {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (hn_pos : 0 < n)
    (f : α → ℕ) (w : α → ENNReal)
    (h_range : ∀ x, f x ∈ Finset.range n) :
    ∃ k ∈ Finset.range n,
      (∑ x ∈ Finset.univ.filter (fun x => f x = k), w x) ≥ (n : ENNReal)⁻¹ * ∑ x : α, w x := by
  let fiber (k : ℕ) := Finset.univ.filter (fun x : α => f x = k)
  let binWeight (k : ℕ) : ENNReal := ∑ x ∈ fiber k, w x
  have h_total : ∑ k ∈ Finset.range n, binWeight k = ∑ x : α, w x := by
    have h1 : ∑ k ∈ Finset.range n, binWeight k =
        ∑ k ∈ Finset.range n, ∑ x : α, (if f x = k then w x else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [binWeight]
      have h : ∑ x : α, (if f x = k then w x else 0) = ∑ x ∈ fiber k, w x := by
        rw [Finset.sum_ite]
        have h2 : ∑ x ∈ Finset.univ.filter (fun x => ¬(f x = k)), (0 : ENNReal) = 0 := by simp
        rw [h2, add_zero]
      exact h.symm
    rw [h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    let a := f x
    have ha : a ∈ Finset.range n := h_range x
    have h_eq1 : ∑ k ∈ Finset.range n, (if f x = k then w x else 0) =
        ∑ k ∈ Finset.range n, (if k = a then w x else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      have h : (if f x = k then w x else 0) = (if k = a then w x else 0) := by
        simp [a, Eq.comm]
      exact h
    rw [h_eq1]
    have h4 : ∑ k ∈ Finset.range n, (if k = a then w x else 0) = w x := by
      rw [Finset.sum_ite_eq']; simp [ha]
    exact h4
  have h_ne : (Finset.range n).Nonempty := by
    have h : n ≠ 0 := by linarith
    simpa [Finset.nonempty_iff_ne_empty] using h
  rcases Finset.exists_max_image (Finset.range n) binWeight h_ne with ⟨k, hk_in, hmax⟩
  have h_sum_le : ∑ j ∈ Finset.range n, binWeight j ≤ (n : ENNReal) * binWeight k := by
    calc
      ∑ j ∈ Finset.range n, binWeight j ≤ ∑ j ∈ Finset.range n, binWeight k := by
        apply Finset.sum_le_sum; intro j hj; exact hmax j hj
      _ = (n : ENNReal) * binWeight k := by
        rw [Finset.sum_const, Finset.card_range]; ring
  have h_nz : (n : ENNReal) ≠ 0 := by exact_mod_cast hn_pos.ne'
  have h_ntop : (n : ENNReal) ≠ ⊤ := by simp
  have h_ge : (n : ENNReal)⁻¹ * ∑ x : α, w x ≤ binWeight k := by
    calc
      (n : ENNReal)⁻¹ * ∑ x : α, w x
        = (n : ENNReal)⁻¹ * (∑ j ∈ Finset.range n, binWeight j) := by rw [h_total]
      _ ≤ (n : ENNReal)⁻¹ * ((n : ENNReal) * binWeight k) := by gcongr
      _ = binWeight k := ENNReal.inv_mul_cancel_left h_nz h_ntop
  exact ⟨k, hk_in, h_ge⟩

lemma c_window_subshading_mass
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hvert : IsInVerticalChart F)
    (w : ℝ) (hw : 0 < w) (hw4 : w ≤ 4) :
    ∃ (c0 : ℝ) (Z : Kakeya.Streamlined.TubeShading F),
      IsSubshading Z Y ∧
      (∀ i, Z.carrier i ≠ ∅ → |(tubeParams i).c - c0| ≤ w / 2) ∧
      IsWholeTubeSubshading Z Y ∧
      Z.mass ≥ ENNReal.ofReal (w / 8) * Y.mass := by
  by_cases h_empty : F.card = 0
  · let Z : Kakeya.Streamlined.TubeShading F :=
      { carrier := fun _ => ∅
        measurable_carrier := by intro _; exact MeasurableSet.empty
        subset_body := by intro _; exact Set.empty_subset _ }
    have h_card0 : F.toBodyFamily.card = 0 := by
      simp [h_empty, Kakeya.Streamlined.TubeFamily.toBodyFamily]
    have hY_mass : Y.mass = 0 := by
      haveI : IsEmpty (Fin F.toBodyFamily.card) := by
        refine' ⟨fun i => Fin.elim0 (Fin.cast h_card0 i)⟩
      simp [Kakeya.Streamlined.Shading.mass]
    have hZ_mass : Z.mass = 0 := by
      haveI : IsEmpty (Fin F.toBodyFamily.card) := by
        refine' ⟨fun i => Fin.elim0 (Fin.cast h_card0 i)⟩
      simp [Z, Kakeya.Streamlined.Shading.mass]
    refine ⟨0, Z, ?_⟩
    constructor
    · intro i; simp [Z]
    · constructor
      · intro i h; simp [Z] at h
      · constructor
        · intro i
          exact Or.inr (by simp [Z])
        · rw [hZ_mass, hY_mass] <;> simp
  · have hN_pos : 0 < F.card := Nat.pos_of_ne_zero h_empty
    classical
    let n : ℕ := Nat.ceil (4 / w)
    have h_pos4 : 0 < (4 / w : ℝ) := by positivity
    have hn_pos : 0 < n := Nat.ceil_pos.mpr h_pos4
    have hn2 : (n : ℝ) ≤ 8 / w := by
      have h1 : (n : ℝ) ≤ 4 / w + 1 :=
        (Nat.ceil_lt_add_one (show 0 ≤ 4 / w from by positivity)).le
      have h2 : 4 / w + 1 ≤ 8 / w := by
        have h3 : 0 < w := hw
        field_simp [h3.ne'] <;> linarith
      linarith
    let binOf (c : ℝ) : ℕ :=
      if c = 2 then n - 1 else Nat.floor ((c + 2) / w)
    let binCenter (k : ℕ) : ℝ := -2 + ((k : ℝ) + 1 / 2) * w
    have h_binOf_lt_n : ∀ c ∈ Set.Icc (-2 : ℝ) 2, binOf c < n := by
      intro c hc
      by_cases hc2 : c = 2
      · have h_k : binOf c = n - 1 := by simp [binOf, hc2]
        rw [h_k] <;> omega
      · have h_k : binOf c = Nat.floor ((c + 2) / w) := by simp [binOf, hc2]
        rw [h_k]
        have h_lt : c < 2 := by
          have h_ne : c ≠ 2 := hc2
          have h_le : c ≤ 2 := hc.2
          exact lt_of_le_of_ne h_le h_ne
        have h5 : (c + 2) / w < 4 / w := by gcongr <;> linarith
        have h_pos4w : 0 < (4 / w : ℝ) := by positivity
        simpa [n] using Nat.floor_lt_ceil_of_lt_of_pos h5 h_pos4w
    let Idx := Fin F.toBodyFamily.card
    have h1 : ∀ (i : Idx), binOf (tubeParams i).c ∈ Finset.range n := by
      intro i
      have hc : (tubeParams i).c ∈ Set.Icc (-2 : ℝ) 2 := by
        have h_bounds := tubeParams_cd_bounds hvert i
        have h_abs : |(tubeParams i).c| ≤ 2 := h_bounds.1
        have h11 : -2 ≤ (tubeParams i).c := (abs_le.mp h_abs).1
        have h12 : (tubeParams i).c ≤ 2 := (abs_le.mp h_abs).2
        exact ⟨h11, h12⟩
      exact Finset.mem_range.mpr (h_binOf_lt_n (tubeParams i).c hc)
    have h_center_bound : ∀ (c : ℝ), c ∈ Set.Icc (-2 : ℝ) 2 →
        |c - binCenter (binOf c)| ≤ w / 2 := by
      intro c hc
      set k := binOf c with hk_def
      have hk_lt_n : k < n := h_binOf_lt_n c hc
      by_cases hc2 : c = 2
      · have h_k_eq : k = n - 1 := by simp [k, binOf, hc2]
        rw [h_k_eq, hc2]
        dsimp only [binCenter]
        have h9 : |(4 : ℝ) - ((n : ℝ) - 1 / 2) * w| ≤ w / 2 := by
          have h10 : 4 - w / 2 ≤ ((n : ℝ) - 1 / 2) * w := by
            have h11 : (n : ℝ) * w ≥ 4 := by
              have h111 : (4 / w : ℝ) ≤ (n : ℝ) := Nat.le_ceil (4 / w)
              calc (n : ℝ) * w ≥ (4 / w) * w := by gcongr
                _ = 4 := by field_simp [hw.ne']
            linarith
          have h12 : ((n : ℝ) - 1 / 2) * w < 4 + w / 2 := by
            have h13 : ((n : ℝ) - 1) * w < 4 := by
              have h131 : (n : ℝ) - 1 < 4 / w := by
                have h : (n : ℝ) < 4 / w + 1 := Nat.ceil_lt_add_one (show 0 ≤ 4 / w from by positivity)
                linarith
              calc ((n : ℝ) - 1) * w < (4 / w) * w := by gcongr
                _ = 4 := by field_simp [hw.ne']
            linarith
          have h14 : -(w / 2) ≤ 4 - ((n : ℝ) - 1 / 2) * w := by linarith
          have h15 : 4 - ((n : ℝ) - 1 / 2) * w ≤ w / 2 := by linarith
          exact abs_le.mpr ⟨h14, h15⟩
        have h10 : (2 : ℝ) - (-2 + (((n : ℝ) - 1 + 1 / 2) * w)) =
            4 - ((n : ℝ) - 1 / 2) * w := by ring
        have h_goal : |(2 : ℝ) - (-2 + (((n : ℝ) - 1 + 1 / 2) * w))| ≤ w / 2 := by
          rw [h10]; exact h9
        simpa [binCenter, Nat.cast_sub hn_pos] using h_goal
      · have h_k_eq : k = Nat.floor ((c + 2) / w) := by simp [k, binOf, hc2]
        have h_nonneg : 0 ≤ (c + 2) / w := by
          have h_c2 : -2 ≤ c := hc.1
          have h : 0 ≤ c + 2 := by linarith
          positivity
        have h1 : (k : ℝ) ≤ (c + 2) / w := by
          rw [h_k_eq]; exact Nat.floor_le h_nonneg
        have h2 : (c + 2) / w < (k : ℝ) + 1 := by
          rw [h_k_eq]; exact Nat.lt_floor_add_one ((c + 2) / w)
        have h3 : -2 + (k : ℝ) * w ≤ c := by
          calc
            -2 + (k : ℝ) * w ≤ -2 + (((c + 2) / w) * w) := by gcongr
            _ = c := by
              have h4 : ((c + 2) / w) * w = c + 2 := by
                field_simp [hw.ne']
              linarith
        have h4 : c < -2 + ((k : ℝ) + 1) * w := by
          calc
            c = -2 + (((c + 2) / w) * w) := by
              have h5 : ((c + 2) / w) * w = c + 2 := by
                field_simp [hw.ne']
              linarith
            _ < -2 + (((k : ℝ) + 1) * w) := by gcongr
        dsimp only [binCenter]
        have h5 : -(w / 2) ≤ c - (-2 + ((k : ℝ) + 1 / 2) * w) := by linarith
        have h6 : c - (-2 + ((k : ℝ) + 1 / 2) * w) ≤ w / 2 := by linarith
        exact abs_le.mpr ⟨h5, h6⟩
    let weight (i : Idx) : ENNReal := MeasureTheory.volume (Y.carrier i)
    rcases weighted_pigeonhole hn_pos (fun i : Idx => binOf (tubeParams i).c) weight h1
      with ⟨k, hk_in, hmass_ge⟩
    let c0 := binCenter k
    let fiber (k : ℕ) : Finset Idx :=
      Finset.univ.filter (fun i : Idx => binOf (tubeParams i).c = k)
    let Z : Kakeya.Streamlined.TubeShading F :=
      { carrier := fun i : Idx => if i ∈ fiber k then Y.carrier i else ∅
        measurable_carrier := by
          intro i
          by_cases h : i ∈ fiber k
          · have h4 : (if i ∈ fiber k then Y.carrier i else ∅) = Y.carrier i := by
              rw [if_pos h]
            rw [h4]; exact Y.measurable_carrier i
          · have h4 : (if i ∈ fiber k then Y.carrier i else ∅) = ∅ := by
              rw [if_neg h]
            rw [h4]; exact MeasurableSet.empty
        subset_body := by
          intro i
          by_cases h : i ∈ fiber k
          · have h4 : (if i ∈ fiber k then Y.carrier i else ∅) = Y.carrier i := by rw [if_pos h]
            rw [h4]
            exact Y.subset_body i
          · have h4 : (if i ∈ fiber k then Y.carrier i else ∅) = ∅ := by rw [if_neg h]
            rw [h4]
            exact Set.empty_subset _ }
    have hZ_sub : IsSubshading Z Y := by
      intro i
      by_cases h : i ∈ fiber k
      · have h4 : Z.carrier i = Y.carrier i := by
          dsimp only [Z]
          have h5 : (if i ∈ fiber k then Y.carrier i else ∅) = Y.carrier i := by rw [if_pos h]
          exact h5
        exact h4 ▸ Subset.refl _
      · have h4 : Z.carrier i = ∅ := by
          dsimp only [Z]
          have h5 : (if i ∈ fiber k then Y.carrier i else ∅) = ∅ := by rw [if_neg h]
          exact h5
        exact h4 ▸ Set.empty_subset _
    have hZ_window : ∀ i, Z.carrier i ≠ ∅ → |(tubeParams i).c - c0| ≤ w / 2 := by
      intro i hne
      have h_in : i ∈ fiber k := by
        by_contra h
        have h_empty : Z.carrier i = ∅ := by
          dsimp only [Z]
          have h5 : (if i ∈ fiber k then Y.carrier i else ∅) = ∅ := by rw [if_neg h]
          exact h5
        rw [h_empty] at hne <;> simp at hne
      have h_eq : binOf (tubeParams i).c = k := (Finset.mem_filter.mp h_in).2
      have hc : (tubeParams i).c ∈ Set.Icc (-2 : ℝ) 2 := by
        have h_bounds := tubeParams_cd_bounds hvert i
        have h_abs : |(tubeParams i).c| ≤ 2 := h_bounds.1
        have h11 : -2 ≤ (tubeParams i).c := (abs_le.mp h_abs).1
        have h12 : (tubeParams i).c ≤ 2 := (abs_le.mp h_abs).2
        exact ⟨h11, h12⟩
      have h11 : c0 = binCenter (binOf (tubeParams i).c) := by
        dsimp only [c0]; rw [h_eq]
      rw [h11]; exact h_center_bound (tubeParams i).c hc
    have hZ_mass : Z.mass = ∑ i ∈ fiber k, weight i := by
      dsimp only [Z, Kakeya.Streamlined.Shading.mass, weight]
      have h3 : ∀ (i : Idx), MeasureTheory.volume (Z.carrier i) =
          if i ∈ fiber k then MeasureTheory.volume (Y.carrier i) else 0 := by
        intro i
        by_cases h : i ∈ fiber k
        · have h4 : Z.carrier i = Y.carrier i := by
            dsimp only [Z]
            have h5 : (if i ∈ fiber k then Y.carrier i else ∅) = Y.carrier i := by rw [if_pos h]
            exact h5
          rw [h4, if_pos h]
        · have h4 : Z.carrier i = ∅ := by
            dsimp only [Z]
            have h5 : (if i ∈ fiber k then Y.carrier i else ∅) = ∅ := by rw [if_neg h]
            exact h5
          rw [h4, if_neg h] <;> simp
      have h4 : ∑ i : Idx, MeasureTheory.volume (Z.carrier i) =
          ∑ i : Idx, (if i ∈ fiber k then MeasureTheory.volume (Y.carrier i) else 0) := by
        apply Finset.sum_congr rfl; intro i _; exact h3 i
      rw [h4]
      rw [Finset.sum_ite] <;> simp
    have h_n_inv_ge : (n : ENNReal)⁻¹ ≥ ENNReal.ofReal (w / 8) := by
      have h_n_le : (n : ℝ) ≤ 8 / w := hn2
      have h_nz : (n : ENNReal) ≠ 0 := by
        simpa [ENNReal.coe_eq_zero] using hn_pos.ne'
      have h_pos8 : 0 < (8 / w : ℝ) := by positivity
      have h3 : (n : ENNReal) ≤ ENNReal.ofReal (8 / w) := by
        have h31 : (n : ℝ) ≤ 8 / w := h_n_le
        have h32 : 0 ≤ (n : ℝ) := by positivity
        have h33 : (n : ENNReal) ≤ ENNReal.ofReal (n : ℝ) := by simp
        have h34 : ENNReal.ofReal (n : ℝ) ≤ ENNReal.ofReal (8 / w) := by
          apply ENNReal.ofReal_le_ofReal; exact h31
        exact le_trans h33 h34
      have h4 : (ENNReal.ofReal (8 / w))⁻¹ = ENNReal.ofReal (w / 8) := by
        have h5 : 0 < (8 / w : ℝ) := h_pos8
        have h6 : (ENNReal.ofReal (8 / w))⁻¹ = ENNReal.ofReal ((8 / w)⁻¹) := by
          rw [ENNReal.ofReal_inv_of_pos h5]
        rw [h6]
        have h7 : (8 / w)⁻¹ = w / 8 := by field_simp [hw.ne']
        rw [h7]
      have h5 : (ENNReal.ofReal (8 / w))⁻¹ ≤ (n : ENNReal)⁻¹ := ENNReal.inv_le_inv.mpr h3
      rw [h4] at h5
      exact h5
    have h_final : Z.mass ≥ ENNReal.ofReal (w / 8) * Y.mass := by
      rw [hZ_mass]
      calc ∑ i ∈ fiber k, weight i
        ≥ (n : ENNReal)⁻¹ * ∑ i : Idx, weight i := hmass_ge
      _ = (n : ENNReal)⁻¹ * Y.mass := by rfl
      _ ≥ ENNReal.ofReal (w / 8) * Y.mass := by gcongr
    have hZ_whole : IsWholeTubeSubshading Z Y := by
      intro i
      by_cases h : i ∈ fiber k
      · exact Or.inl (by simp [Z, h])
      · exact Or.inr (by simp [Z, h])
    exact ⟨c0, Z, hZ_sub, hZ_window, hZ_whole, h_final⟩

end Kakeya.Assouad
