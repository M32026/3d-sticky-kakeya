import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.UniformFourBlockRelationDensityStatement

/-!
WZ2 Proposition 7.1: transfer fine shaded density through a factor-two
uniform relation-valued four-block cover.
-/

namespace Kakeya.Assouad

theorem uniform_four_block_relation_density :
    UniformFourBlockRelationDensityStatement := by
  intro hvol hpiece delta rho hdelta hdelta_rho hrho_one fine shading data lambda hY
  let V_delta := Kakeya.deltaTubeVolume delta
  let V_rho := Kakeya.deltaTubeVolume rho
  have hrho : 0 < rho := lt_of_lt_of_le hdelta hdelta_rho
  have hdelta_one : delta ≤ 1 := hdelta_rho.trans hrho_one
  have hV_delta_pos : 0 < V_delta :=
    (hvol.2.1 delta hdelta hdelta_one).1
  have hV_delta_ne_top : V_delta ≠ ⊤ :=
    (hvol.2.1 delta hdelta hdelta_one).2
  have hfine_vol : ∀ i, (fine.tube i).volume = V_delta :=
    fun i => hvol.1 delta (fine.tube i)
  have hcoarse_vol : ∀ q, (data.coarse.tube q).volume = V_rho :=
    fun q => hvol.1 rho (data.coarse.tube q)
  let Z := data.exactShading rho
  let m := data.fiberMultiplicity

  -- Step 2: Per-piece inequality
  have h_per_piece :
      ∀ (i : Fin fine.card) (k : Fin 4),
        ENNReal.ofReal (1 / 100 : ℝ) *
              MeasureTheory.volume
                (shading.carrier i ∩
                  (data.coarse.tube
                    (finProdFinEquiv (data.parent i, k))).carrier) *
              V_rho ≤
          V_delta * MeasureTheory.volume
            (Z.carrier (finProdFinEquiv (data.parent i, k))) := by
    intro i k
    set q : Fin data.coarse.card :=
      finProdFinEquiv (data.parent i, k)
    set E : Set Point3 :=
      shading.carrier i ∩ (data.coarse.tube q).carrier
    have hS_meas : MeasurableSet (data.coarse.tube q).carrier :=
      Metric.isClosed_cthickening.measurableSet
    have hE_meas : MeasurableSet E :=
      (shading.measurable_carrier i).inter hS_meas
    have hE_T : E ⊆ (fine.tube i).carrier :=
      Set.inter_subset_left.trans (shading.subset_body i)
    have hE_S : E ⊆ (data.coarse.tube q).carrier :=
      Set.inter_subset_right
    have h_main := hpiece hdelta hdelta_rho hrho_one
      (fine.tube i) (data.coarse.tube q) E hE_meas hE_T hE_S
    rw [hcoarse_vol q] at h_main
    have h_fixed : fixedBlockIndex q = data.parent i := by
      dsimp [q]
      exact fixedBlockIndex_finProdFinEquiv (data.parent i) k
    have hri : data.relation i q := h_fixed
    have h_thick_subset :
        (data.coarse.tube q).carrier ∩ Metric.cthickening rho E ⊆
          Z.carrier q := by
      intro x hx
      have hE_sub : E ⊆ shading.carrier i := Set.inter_subset_left
      have h4 : x ∈ Metric.cthickening rho (shading.carrier i) :=
        (Metric.cthickening_subset_of_subset rho hE_sub) hx.2
      have h5 : shading.carrier i ⊆
          {point : Point3 | ∃ i' : Fin fine.card,
            data.relation i' q ∧ point ∈ shading.carrier i'} := by
        intro y hy
        exact ⟨i, hri, hy⟩
      have h6 : x ∈ Metric.cthickening rho
          {point : Point3 | ∃ i' : Fin fine.card,
            data.relation i' q ∧ point ∈ shading.carrier i'} :=
        Metric.cthickening_subset_of_subset rho h5 h4
      exact ⟨hx.1, h6⟩
    have h_vol : MeasureTheory.volume
        ((data.coarse.tube q).carrier ∩ Metric.cthickening rho E) ≤
      MeasureTheory.volume (Z.carrier q) :=
      MeasureTheory.measure_mono h_thick_subset
    exact h_main.trans
      (mul_le_mul_of_nonneg_left h_vol (by positivity))

  -- Step 3: Cover argument
  have h_cover :
      ∀ i : Fin fine.card,
        shading.carrier i ⊆ ⋃ k : Fin 4,
          shading.carrier i ∩
            (data.coarse.tube
              (finProdFinEquiv (data.parent i, k))).carrier := by
    intro i x hx
    have h1 : x ∈ (data.block (data.parent i)).toBodyFamily.union :=
      data.shading_cover i hx
    rcases h1 with ⟨k, hk⟩
    change x ∈ ((data.block (data.parent i)).tube k).carrier at hk
    let slot : Fin 4 := Fin.cast (data.block_card (data.parent i)) k
    have h4 :
        x ∈ (data.coarse.tube
          (finProdFinEquiv (data.parent i, slot))).carrier := by
      change x ∈
        ((flattenFixedBlocks data.block data.block_card).tube
          (finProdFinEquiv (data.parent i, slot))).carrier
      rw [flattenFixedBlocks_tube]
      simpa [slot] using hk
    exact Set.mem_iUnion.mpr ⟨slot, ⟨hx, h4⟩⟩

  -- Step 4: Per-i inequality
  have h_per_i :
      ∀ i : Fin fine.card,
        ENNReal.ofReal (1 / 100 : ℝ) * V_rho *
              MeasureTheory.volume (shading.carrier i) ≤
          V_delta * ∑ k : Fin 4,
            MeasureTheory.volume
              (Z.carrier (finProdFinEquiv (data.parent i, k))) := by
    intro i
    let f k :=
      shading.carrier i ∩
        (data.coarse.tube
          (finProdFinEquiv (data.parent i, k))).carrier
    have h_iUnion :
        MeasureTheory.volume (⋃ k : Fin 4, f k) ≤
          ∑ k : Fin 4, MeasureTheory.volume (f k) :=
      MeasureTheory.measure_iUnion_fintype_le MeasureTheory.volume f
    have h_sum_cover :
        MeasureTheory.volume (shading.carrier i) ≤
          ∑ k : Fin 4, MeasureTheory.volume (f k) :=
      (MeasureTheory.measure_mono (h_cover i)).trans h_iUnion
    have h_sum :
        ∑ k : Fin 4,
            (ENNReal.ofReal (1 / 100 : ℝ) *
              MeasureTheory.volume (f k) * V_rho) ≤
          ∑ k : Fin 4,
            (V_delta * MeasureTheory.volume
              (Z.carrier (finProdFinEquiv (data.parent i, k)))) := by
      exact Finset.sum_le_sum fun k _ => h_per_piece i k
    let c := ENNReal.ofReal (1 / 100 : ℝ) * V_rho
    have h_left :
        c * MeasureTheory.volume (shading.carrier i) ≤
          c * ∑ k : Fin 4, MeasureTheory.volume (f k) := by
      gcongr
    have h_middle :
        c * ∑ k : Fin 4, MeasureTheory.volume (f k) =
          ∑ k : Fin 4, c * MeasureTheory.volume (f k) := by
      rw [Finset.mul_sum]
    rw [h_middle] at h_left
    have h_left2 :
        ∑ k : Fin 4, c * MeasureTheory.volume (f k) ≤
          ∑ k : Fin 4,
            ENNReal.ofReal (1 / 100 : ℝ) *
              MeasureTheory.volume (f k) * V_rho := by
      apply Finset.sum_le_sum
      intro k _
      have h_comm :
          c * MeasureTheory.volume (f k) =
            ENNReal.ofReal (1 / 100 : ℝ) *
              MeasureTheory.volume (f k) * V_rho := by
        simp [c, mul_comm, mul_assoc]
      exact le_of_eq h_comm
    have h_right :
        ∑ k : Fin 4,
            V_delta * MeasureTheory.volume
              (Z.carrier (finProdFinEquiv (data.parent i, k))) =
          V_delta * ∑ k : Fin 4,
            MeasureTheory.volume
              (Z.carrier (finProdFinEquiv (data.parent i, k))) := by
      rw [Finset.mul_sum]
    rw [h_right] at h_sum
    exact h_left.trans (h_left2.trans h_sum)

  -- Step 5: Sum over i and bound overcounting
  let g : Fin data.parentCount → ENNReal := fun j =>
    ∑ k : Fin 4,
      MeasureTheory.volume
        (Z.carrier (finProdFinEquiv (j, k)))

  have h_fiber_sum :
      ∑ i : Fin fine.card, g (data.parent i) =
        ∑ j : Fin data.parentCount,
          ((Finset.univ.filter fun i : Fin fine.card =>
            data.parent i = j).card : ENNReal) * g j := by
    have h1 : ∑ i : Fin fine.card, g (data.parent i) =
        ∑ j : Fin data.parentCount,
          ∑ i ∈ (Finset.univ.filter fun i : Fin fine.card => data.parent i = j),
            g (data.parent i) :=
      (Finset.sum_fiberwise Finset.univ data.parent
        (fun i => g (data.parent i))).symm
    rw [h1]
    apply Finset.sum_congr rfl
    intro j _
    let fiber := Finset.univ.filter fun i : Fin fine.card => data.parent i = j
    have h2 : ∀ i ∈ fiber, g (data.parent i) = g j := by
      intro i hi
      have h3 : data.parent i = j := (Finset.mem_filter.mp hi).2
      rw [h3]
    have h3 : ∑ i ∈ fiber, g (data.parent i) = (fiber.card : ENNReal) * g j := by
      rw [Finset.sum_congr rfl h2, Finset.sum_const]
      <;> ring
    exact h3

  have h_fiber_upper' :
      ∀ j : Fin data.parentCount,
        ((Finset.univ.filter fun i : Fin fine.card =>
          data.parent i = j).card : ENNReal) ≤ (2 * m : ENNReal) := by
    intro j
    have h : (Finset.univ.filter fun i : Fin fine.card =>
        data.parent i = j).card < 2 * m := data.fiber_upper j
    exact_mod_cast le_of_lt h

  have h_sum_bound :
      ∑ i : Fin fine.card, g (data.parent i) ≤
        (2 * (m : ENNReal)) * ∑ j : Fin data.parentCount, g j := by
    rw [h_fiber_sum]
    have h :
        ∑ j : Fin data.parentCount,
          ((Finset.univ.filter fun i : Fin fine.card =>
            data.parent i = j).card : ENNReal) * g j ≤
        ∑ j : Fin data.parentCount, (2 * (m : ENNReal)) * g j := by
      apply Finset.sum_le_sum
      intro j _
      gcongr
      exact h_fiber_upper' j
    rw [Finset.mul_sum] at *
    <;> exact h

  have h_Z_mass : ∑ j : Fin data.parentCount, g j = Z.mass := by
    dsimp only [g]
    have h_eq1 :
        ∑ j : Fin data.parentCount, ∑ k : Fin 4,
            MeasureTheory.volume
              (Z.carrier (finProdFinEquiv (j, k))) =
          ∑ pair : Fin data.parentCount × Fin 4,
            MeasureTheory.volume
              (Z.carrier (finProdFinEquiv pair)) := by
      rw [Fintype.sum_prod_type]
    rw [h_eq1]
    have h_eq2 :
        ∑ pair : Fin data.parentCount × Fin 4,
            MeasureTheory.volume
              (Z.carrier (finProdFinEquiv pair)) =
          ∑ q : Fin data.coarse.card,
            MeasureTheory.volume (Z.carrier q) :=
      Equiv.sum_comp finProdFinEquiv
        (fun q => MeasureTheory.volume (Z.carrier q))
    rw [h_eq2]
    rfl

  -- Step 5 continued: total inequality
  let c := ENNReal.ofReal (1 / 100 : ℝ) * V_rho
  have h_sum_left :
      ∑ i : Fin fine.card,
          c * MeasureTheory.volume (shading.carrier i) =
        c * shading.mass := by
    have h :
        ∑ i : Fin fine.card,
            c * MeasureTheory.volume (shading.carrier i) =
          c * ∑ i : Fin fine.card,
            MeasureTheory.volume (shading.carrier i) := by
      rw [Finset.mul_sum]
    rw [h]
    rfl

  have h_sum_right :
      ∑ i : Fin fine.card,
          V_delta * g (data.parent i) ≤
        V_delta * (2 * (m : ENNReal)) * Z.mass := by
    have h1 :
        ∑ i : Fin fine.card,
            V_delta * g (data.parent i) =
          V_delta * ∑ i : Fin fine.card, g (data.parent i) := by
      rw [Finset.mul_sum]
    rw [h1]
    have h2 : V_delta * ∑ i : Fin fine.card, g (data.parent i) ≤
        V_delta * ((2 * (m : ENNReal)) * ∑ j : Fin data.parentCount, g j) := by
      gcongr
    rw [h_Z_mass] at *
    <;> simpa [mul_assoc] using h2

  have h_total :
      c * shading.mass ≤ V_delta * (2 * (m : ENNReal)) * Z.mass := by
    have h_sum :
        ∑ i : Fin fine.card,
            c * MeasureTheory.volume (shading.carrier i) ≤
          ∑ i : Fin fine.card,
            V_delta * g (data.parent i) :=
      Finset.sum_le_sum fun i _ => h_per_i i
    rw [h_sum_left] at h_sum
    exact h_sum.trans h_sum_right

  -- Step 6: Use density and cardinality
  have h_fine_mass :
      fine.toBodyFamily.mass = (fine.card : ENNReal) * V_delta := by
    calc
      fine.toBodyFamily.mass =
          ∑ i : Fin fine.card,
            (fine.toBodyFamily.body i).volume := by rfl
      _ = ∑ _i : Fin fine.card, V_delta := by
        apply Finset.sum_congr rfl
        intro i _
        exact hfine_vol i
      _ = (fine.card : ENNReal) * V_delta := by simp

  have h_density :
      lambda * fine.toBodyFamily.mass ≤ shading.mass := hY
  rw [h_fine_mass] at h_density

  let a : ENNReal := c * lambda * (fine.card : ENNReal)
  have h_final1 : a * V_delta ≤ V_delta * (2 * (m : ENNReal)) * Z.mass := by
    calc
      a * V_delta =
          c * (lambda * ((fine.card : ENNReal) * V_delta)) := by
        dsimp [a, c]
        ac_rfl
      _ ≤ c * shading.mass := by gcongr
      _ ≤ V_delta * (2 * (m : ENNReal)) * Z.mass := h_total

  have h_cancel1 : a ≤ (2 * (m : ENNReal)) * Z.mass := by
    have h5 : V_delta ≠ 0 := hV_delta_pos.ne'
    have h6 : V_delta ≠ ⊤ := hV_delta_ne_top
    have h_eq : V_delta * (2 * (m : ENNReal)) * Z.mass =
        ((2 * (m : ENNReal)) * Z.mass) * V_delta := by
      simp [mul_assoc, mul_comm, mul_left_comm]
    have h_final1' : a * V_delta ≤ ((2 * (m : ENNReal)) * Z.mass) * V_delta := by
      rw [h_eq] at h_final1
      exact h_final1
    have h_div :
        a * V_delta / V_delta ≤
          ((2 * (m : ENNReal)) * Z.mass) * V_delta / V_delta := by
      gcongr
    have h7 : a * V_delta / V_delta = a :=
      ENNReal.mul_div_cancel_right h5 h6
    have h8 : ((2 * (m : ENNReal)) * Z.mass) * V_delta / V_delta =
        (2 * (m : ENNReal)) * Z.mass :=
      ENNReal.mul_div_cancel_right h5 h6
    rw [h7, h8] at h_div
    exact h_div

  -- Step 7: Lower bound on fine.card
  have h_card_sum :
      (fine.card : ENNReal) =
        ∑ j : Fin data.parentCount,
          ((Finset.univ.filter fun i : Fin fine.card =>
            data.parent i = j).card : ENNReal) := by
    have h_univ_card : (Finset.univ : Finset (Fin fine.card)).card = fine.card := by simp
    have h_eq : (Finset.univ : Finset (Fin fine.card)).card =
        ∑ j : Fin data.parentCount,
          (Finset.univ.filter fun i : Fin fine.card => data.parent i = j).card :=
      Finset.card_eq_sum_card_fiberwise
        (s := Finset.univ) (t := Finset.univ)
        (fun i _ => Finset.mem_univ (data.parent i))
    have h_nat : fine.card =
        ∑ j : Fin data.parentCount,
          (Finset.univ.filter fun i : Fin fine.card => data.parent i = j).card :=
      h_univ_card.symm.trans h_eq
    exact_mod_cast h_nat

  have h_fiber_lower' :
      ∀ j : Fin data.parentCount,
        (m : ENNReal) ≤
          ((Finset.univ.filter fun i : Fin fine.card =>
            data.parent i = j).card : ENNReal) := by
    intro j
    exact_mod_cast data.fiber_lower j

  have h_card_lower :
      (m : ENNReal) * (data.parentCount : ENNReal) ≤ (fine.card : ENNReal) := by
    rw [h_card_sum]
    have h :
        ∑ j : Fin data.parentCount, (m : ENNReal) ≤
          ∑ j : Fin data.parentCount,
            ((Finset.univ.filter fun i : Fin fine.card =>
              data.parent i = j).card : ENNReal) := by
      apply Finset.sum_le_sum
      intro j _
      exact h_fiber_lower' j
    have h2 : ∑ j : Fin data.parentCount, (m : ENNReal) =
        (m : ENNReal) * (data.parentCount : ENNReal) := by
      simp [Finset.sum_const]
      <;> ring
    rw [h2] at h
    exact h

  have hm_pos : (m : ENNReal) ≠ 0 := by
    exact_mod_cast data.fiberMultiplicity_pos.ne'
  have hm_top : (m : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top m

  set d : ENNReal := c * lambda * (data.parentCount : ENNReal) with hd_def
  have h9 : (m : ENNReal) * d ≤ (m : ENNReal) * (2 * Z.mass) := by
    have h10 : c * lambda * ((m : ENNReal) * (data.parentCount : ENNReal)) ≤
        c * lambda * (fine.card : ENNReal) := by
      gcongr
      <;> exact h_card_lower
    have h11 : c * lambda * (fine.card : ENNReal) ≤
        (2 * (m : ENNReal)) * Z.mass := h_cancel1
    have h12 : c * lambda * ((m : ENNReal) * (data.parentCount : ENNReal)) ≤
        (2 * (m : ENNReal)) * Z.mass := h10.trans h11
    have h13 : c * lambda * ((m : ENNReal) * (data.parentCount : ENNReal)) =
        (m : ENNReal) * d := by
      simp [hd_def, c, mul_comm, mul_left_comm]
      <;> ac_rfl
    rw [h13] at h12
    have h14 : (2 * (m : ENNReal)) * Z.mass = (m : ENNReal) * (2 * Z.mass) := by
      simp [mul_assoc, mul_comm]
    rw [h14] at h12
    exact h12
  have h_div_m : (m : ENNReal) * d / (m : ENNReal) ≤
        (m : ENNReal) * (2 * Z.mass) / (m : ENNReal) := by gcongr
  have h14 : (m : ENNReal) * d / (m : ENNReal) = d := by
    have h_comm : (m : ENNReal) * d = d * (m : ENNReal) := by ring
    rw [h_comm]
    exact ENNReal.mul_div_cancel_right hm_pos hm_top
  have h15 : (m : ENNReal) * (2 * Z.mass) / (m : ENNReal) = 2 * Z.mass := by
    have h_comm : (m : ENNReal) * (2 * Z.mass) = (2 * Z.mass) * (m : ENNReal) := by ring
    rw [h_comm]
    exact ENNReal.mul_div_cancel_right hm_pos hm_top
  have h_cancel2 : d ≤ 2 * Z.mass := by
    rw [h14, h15] at h_div_m
    exact h_div_m

  -- Step 8: Coarse mass calculation
  have h_coarse_card :
      data.coarse.card = data.parentCount * 4 :=
    flattenFixedBlocks_card data.block data.block_card

  have h_coarse_mass :
      data.coarse.toBodyFamily.mass =
        (4 : ENNReal) * (data.parentCount : ENNReal) * V_rho := by
    calc
      data.coarse.toBodyFamily.mass =
          ∑ q : Fin data.coarse.card,
            (data.coarse.toBodyFamily.body q).volume := by rfl
      _ = ∑ _q : Fin data.coarse.card, V_rho := by
        apply Finset.sum_congr rfl
        intro q _
        exact hcoarse_vol q
      _ = (data.coarse.card : ENNReal) * V_rho := by simp
      _ = ((data.parentCount * 4 : ℕ) : ENNReal) * V_rho := by
        rw [h_coarse_card]
      _ = (4 : ENNReal) * (data.parentCount : ENNReal) * V_rho := by
        have h2 : ((data.parentCount * 4 : ℕ) : ENNReal) =
            (4 : ENNReal) * (data.parentCount : ENNReal) := by
          rw [Nat.cast_mul]
          have h3 : (data.parentCount : ENNReal) * ((4 : ℕ) : ENNReal) =
              (4 : ENNReal) * (data.parentCount : ENNReal) := by
            simpa using mul_comm (data.parentCount : ENNReal) (4 : ENNReal)
          exact h3
        rw [h2]

  rw [h_coarse_mass]

  have h4 :
      ENNReal.ofReal (1 / 800 : ℝ) * (4 : ENNReal) =
        ENNReal.ofReal (1 / 200 : ℝ) := by
    have h_cast4 : (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) := by simp
    rw [h_cast4]
    have h_pos1 : 0 ≤ (1 / 800 : ℝ) := by norm_num
    have h_mul :
        ENNReal.ofReal (1 / 800 : ℝ) * ENNReal.ofReal (4 : ℝ) =
          ENNReal.ofReal ((1 / 800 : ℝ) * (4 : ℝ)) := by
      rw [← ENNReal.ofReal_mul h_pos1]
    rw [h_mul]
    norm_num

  have h_half :
      (2 : ENNReal) * ENNReal.ofReal (1 / 200 : ℝ) =
        ENNReal.ofReal (1 / 100 : ℝ) := by
    have h : (2 : ENNReal) * ENNReal.ofReal (1 / 200 : ℝ) =
        ENNReal.ofReal ((2 : ℝ) * (1 / 200 : ℝ)) := by
      have h2 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by simp
      rw [h2]
      rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [h]
    norm_num

  set b : ENNReal :=
      ENNReal.ofReal (1 / 200 : ℝ) * V_rho * lambda *
        (data.parentCount : ENNReal) with hb_def

  have h9b : (2 : ENNReal) * b ≤ (2 : ENNReal) * Z.mass := by
    have h10 : (2 : ENNReal) * b =
        ENNReal.ofReal (1 / 100 : ℝ) * V_rho * lambda *
          (data.parentCount : ENNReal) := by
      rw [hb_def, ← h_half] <;> ac_rfl
    rw [h10]
    have h11 : ENNReal.ofReal (1 / 100 : ℝ) * V_rho * lambda *
          (data.parentCount : ENNReal) = d := by
      simp [hd_def, c, mul_comm, mul_left_comm] <;> ac_rfl
    rw [h11]
    exact h_cancel2

  have h11 : (2 : ENNReal) ≠ 0 := by norm_num
  have h12 : (2 : ENNReal) ≠ ⊤ := by norm_num
  have h_div2 : (2 : ENNReal) * b / (2 : ENNReal) ≤
        (2 : ENNReal) * Z.mass / (2 : ENNReal) := by gcongr
  have h7 : (2 : ENNReal) * b / (2 : ENNReal) = b := by
    have h_comm : (2 : ENNReal) * b = b * (2 : ENNReal) := by ring
    rw [h_comm]
    exact ENNReal.mul_div_cancel_right h11 h12
  have h8 : (2 : ENNReal) * Z.mass / (2 : ENNReal) = Z.mass := by
    have h_comm : (2 : ENNReal) * Z.mass = Z.mass * (2 : ENNReal) := by ring
    rw [h_comm]
    exact ENNReal.mul_div_cancel_right h11 h12
  have h_b_le : b ≤ Z.mass := by
    rw [h7, h8] at h_div2
    exact h_div2

  have h_final :
      ENNReal.ofReal (1 / 800 : ℝ) * lambda *
          ((4 : ENNReal) * (data.parentCount : ENNReal) * V_rho) = b := by
    calc
      ENNReal.ofReal (1 / 800 : ℝ) * lambda *
          ((4 : ENNReal) * (data.parentCount : ENNReal) * V_rho)
        = (ENNReal.ofReal (1 / 800 : ℝ) * (4 : ENNReal)) * lambda *
            (data.parentCount : ENNReal) * V_rho := by
          simp [mul_assoc, mul_comm, mul_left_comm]
      _ = ENNReal.ofReal (1 / 200 : ℝ) * lambda *
            (data.parentCount : ENNReal) * V_rho := by
          rw [h4] <;> simp [mul_assoc, mul_comm, mul_left_comm]
      _ = b := by
          simpa [hb_def, mul_comm, mul_left_comm] using rfl
  rw [h_final]
  exact h_b_le

end Kakeya.Assouad
