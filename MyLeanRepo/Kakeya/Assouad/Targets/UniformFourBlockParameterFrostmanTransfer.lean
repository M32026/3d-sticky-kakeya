import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.UniformFourBlockParameterFrostmanTransferStatement

/-!
WZ2 Proposition 7.1: transfer indexed parameter Frostman control through one
factor-two uniform four-block parameter-cell coarsening.
-/

namespace Kakeya.Assouad

theorem uniform_four_block_parameter_frostman_transfer :
    UniformFourBlockParameterFrostmanTransferStatement := by
  intro delta rho hrho hdelta_rho fine shading data representative hrep
    hblock_params mesh hmesh_nonneg hmesh_le hmesh C hC_one hC_top hFrostman
  classical
  -- Goal: TubeParameterFrostmanBound data.coarse (8 * C)
  intro r hrho_r hr_one reference
  let p_ref := fixedBlockIndex reference
  let fine_ref := representative p_ref

  -- Key identity: coarse tube params come from the representative of their block.
  have h_coarse_params : ∀ (q : Fin data.coarse.card),
      tubeParams q = tubeParams (representative (fixedBlockIndex q)) := by
    intro q
    have h1 : data.coarse.tube q =
        (data.block (fixedBlockIndex q)).tube
          (Fin.cast (data.block_card (fixedBlockIndex q)).symm (fixedBlockSlot q)) :=
      flattenFixedBlocks_tube_block_slot data.block data.block_card q
    have h2 : tubeParamsOfTube (data.coarse.tube q) =
        tubeParams (representative (fixedBlockIndex q)) := by
      rw [h1]
      exact hblock_params (fixedBlockIndex q) _
    exact h2

  -- P: parent indices whose representative is in the r-box around fine_ref.
  let P : Finset (Fin data.parentCount) := Finset.univ.filter (fun p =>
    |(tubeParams (representative p)).a - (tubeParams fine_ref).a| ≤ r ∧
    |(tubeParams (representative p)).b - (tubeParams fine_ref).b| ≤ r ∧
    |(tubeParams (representative p)).c - (tubeParams fine_ref).c| ≤ r ∧
    |(tubeParams (representative p)).d - (tubeParams fine_ref).d| ≤ r)

  -- B_coarse: coarse indices in the r-box around reference.
  let B_coarse : Finset (Fin data.coarse.card) := Finset.univ.filter (fun q =>
    |(tubeParams q).a - (tubeParams reference).a| ≤ r ∧
    |(tubeParams q).b - (tubeParams reference).b| ≤ r ∧
    |(tubeParams q).c - (tubeParams reference).c| ≤ r ∧
    |(tubeParams q).d - (tubeParams reference).d| ≤ r)

  have h_coarse_card_eq : data.coarse.card = data.parentCount * 4 :=
    flattenFixedBlocks_card data.block data.block_card

  -- B_coarse = {q | fixedBlockIndex q ∈ P}
  have h_B_coarse_eq : B_coarse =
      Finset.univ.filter (fun (q : Fin data.coarse.card) => fixedBlockIndex q ∈ P) := by
    ext q
    have hq1 : tubeParams q = tubeParams (representative (fixedBlockIndex q)) :=
      h_coarse_params q
    have hq2 : tubeParams reference = tubeParams fine_ref := h_coarse_params reference
    simp [B_coarse, P, Finset.mem_filter, Finset.mem_univ, hq1, hq2]
    <;> rfl

  -- B_coarse.card = 4 * P.card
  have h_card : B_coarse.card = 4 * P.card := by
    rw [h_B_coarse_eq]
    let f : Fin data.parentCount × Fin 4 → Fin data.coarse.card := finProdFinEquiv
    have h1 : (Finset.univ.filter (fun (q : Fin data.coarse.card) => fixedBlockIndex q ∈ P)) =
        Finset.image f (P ×ˢ (Finset.univ : Finset (Fin 4))) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image, Finset.mem_product]
      constructor
      · intro hq
        refine ⟨(fixedBlockIndex q, fixedBlockSlot q), ⟨hq, by trivial⟩, ?_⟩
        dsimp only [f]
        exact finProdFinEquiv.apply_symm_apply q
      · rintro ⟨pair, hpair, h_eq⟩
        have hpe : pair.1 ∈ P := hpair.1
        have h_fbi : fixedBlockIndex q = pair.1 := by
          have h : f pair = q := h_eq
          rw [←h]
          dsimp only [f]
          simp [fixedBlockIndex]
          <;> rfl
        rw [h_fbi]
        exact hpe
    rw [h1]
    have h_inj : Function.Injective f := by
      dsimp only [f]
      exact finProdFinEquiv.injective
    rw [Finset.card_image_of_injective _ h_inj]
    rw [Finset.card_product, Finset.card_fin]
    <;> ring

  by_cases h_small : r ≤ 1 / 2
  · -- Case 1: r ≤ 1/2, use source Frostman at 2*r
    have h_mesh_le_r : mesh ≤ r := by
      calc mesh ≤ rho / 6 := hmesh_le
           _ ≤ r / 6 := by gcongr
           _ ≤ r := by linarith [hrho_r]

    -- S_fine: fine indices in 2*r-box around fine_ref.
    let S_fine : Finset (Fin fine.card) := Finset.univ.filter (fun i =>
      |(tubeParams i).a - (tubeParams fine_ref).a| ≤ 2 * r ∧
      |(tubeParams i).b - (tubeParams fine_ref).b| ≤ 2 * r ∧
      |(tubeParams i).c - (tubeParams fine_ref).c| ≤ 2 * r ∧
      |(tubeParams i).d - (tubeParams fine_ref).d| ≤ 2 * r)

    let fiber (p : Fin data.parentCount) : Finset (Fin fine.card) :=
      Finset.univ.filter (fun i => data.parent i = p)

    -- Triangle inequality helper.
    have h_abs : ∀ (x y z : ℝ), |x - z| ≤ |x - y| + |y - z| := by
      intro x y z
      apply abs_le.mpr
      constructor
      · linarith [neg_abs_le (x - y), neg_abs_le (y - z)]
      · linarith [le_abs_self (x - y), le_abs_self (y - z)]

    -- For p ∈ P, fiber p ⊆ S_fine.
    have h_fiber_subset : ∀ p ∈ P, fiber p ⊆ S_fine := by
      intro p hp i hi
      have h_parent : data.parent i = p := (Finset.mem_filter.mp hi).2
      have h_p_in_P := (Finset.mem_filter.mp hp).2
      have h_mesh_i := hmesh i
      rw [h_parent] at h_mesh_i
      rcases h_p_in_P with ⟨ha_p, hb_p, hc_p, hd_p⟩
      rcases h_mesh_i with ⟨ha_m, hb_m, hc_m, hd_m⟩
      simp only [S_fine, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨
        calc |(tubeParams i).a - (tubeParams fine_ref).a|
          ≤ |(tubeParams i).a - (tubeParams (representative p)).a| +
            |(tubeParams (representative p)).a - (tubeParams fine_ref).a| := h_abs _ _ _
        _ ≤ mesh + r := by linarith
        _ ≤ 2 * r := by linarith,
        calc |(tubeParams i).b - (tubeParams fine_ref).b|
          ≤ |(tubeParams i).b - (tubeParams (representative p)).b| +
            |(tubeParams (representative p)).b - (tubeParams fine_ref).b| := h_abs _ _ _
        _ ≤ mesh + r := by linarith
        _ ≤ 2 * r := by linarith,
        calc |(tubeParams i).c - (tubeParams fine_ref).c|
          ≤ |(tubeParams i).c - (tubeParams (representative p)).c| +
            |(tubeParams (representative p)).c - (tubeParams fine_ref).c| := h_abs _ _ _
        _ ≤ mesh + r := by linarith
        _ ≤ 2 * r := by linarith,
        calc |(tubeParams i).d - (tubeParams fine_ref).d|
          ≤ |(tubeParams i).d - (tubeParams (representative p)).d| +
            |(tubeParams (representative p)).d - (tubeParams fine_ref).d| := h_abs _ _ _
        _ ≤ mesh + r := by linarith
        _ ≤ 2 * r := by linarith
      ⟩

    -- Fibers over P are pairwise disjoint.
    have h_fiber_disj : Set.PairwiseDisjoint P fiber := by
      intro p _ q _ hne
      simp only [Finset.disjoint_left, fiber, Finset.mem_filter,
        Finset.mem_univ, true_and]
      intro i hpi hqi
      have h1 : data.parent i = p := hpi
      have h2 : data.parent i = q := hqi
      rw [h1] at h2
      exact hne h2

    -- P.card * fiberMultiplicity ≤ S_fine.card
    have h_main_nat : P.card * data.fiberMultiplicity ≤ S_fine.card := by
      calc
        P.card * data.fiberMultiplicity
          = ∑ p ∈ P, data.fiberMultiplicity := by
            rw [Finset.sum_const] <;> ring
        _ ≤ ∑ p ∈ P, (fiber p).card := by
            apply Finset.sum_le_sum
            intro p hp
            exact data.fiber_lower p
        _ = (P.biUnion fiber).card := by
            rw [Finset.card_biUnion h_fiber_disj]
        _ ≤ S_fine.card := by
            apply Finset.card_le_card
            intro i hi
            rcases Finset.mem_biUnion.mp hi with ⟨p, hp, hpi⟩
            exact h_fiber_subset p hp hpi

    -- Apply source Frostman at 2*r.
    have h_2r_le_one : 2 * r ≤ 1 := by linarith
    have h_delta_le_2r : delta ≤ 2 * r := by linarith
    have h_frostman_2r : (S_fine.card : ENNReal) ≤
        C * Kakeya.realRpowENN (2 * r) 2 * fine.enncard :=
      hFrostman (2 * r) h_delta_le_2r h_2r_le_one fine_ref

    have hr_nonneg : 0 ≤ r := by linarith
    have h_rpow : Kakeya.realRpowENN (2 * r) 2 = 4 * Kakeya.realRpowENN r 2 := by
      simp only [Kakeya.realRpowENN]
      have h1 : Real.rpow (2 * r) 2 = (2 * r) ^ 2 := by
        simp [Real.rpow_two]
      have h2 : Real.rpow r 2 = r ^ 2 := by
        simp [Real.rpow_two]
      rw [h1, h2]
      have h3 : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
      rw [h3]
      rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4 by norm_num)]
      <;> simp

    rw [h_rpow] at h_frostman_2r

    have h_main_ennreal : (P.card : ENNReal) * (data.fiberMultiplicity : ENNReal) ≤
        (S_fine.card : ENNReal) := by
      have h : (P.card * data.fiberMultiplicity : ℕ) ≤ S_fine.card := h_main_nat
      have h' : ((P.card * data.fiberMultiplicity : ℕ) : ENNReal) ≤ (S_fine.card : ENNReal) :=
        Nat.cast_le.mpr h
      have h'' : ((P.card * data.fiberMultiplicity : ℕ) : ENNReal) =
          (P.card : ENNReal) * (data.fiberMultiplicity : ENNReal) := by
        simp [Nat.cast_mul]
      rw [h''] at h'
      exact h'

    have hfm_pos : (data.fiberMultiplicity : ENNReal) ≠ 0 :=
      Nat.cast_ne_zero.mpr data.fiberMultiplicity_pos.ne'
    have hfm_top : (data.fiberMultiplicity : ENNReal) ≠ ⊤ := by simp

    have h_frostman_2r' : (S_fine.card : ENNReal) ≤
        4 * C * Kakeya.realRpowENN r 2 * fine.enncard := by
      have h_eq : C * (4 * Kakeya.realRpowENN r 2) * fine.enncard =
          4 * C * Kakeya.realRpowENN r 2 * fine.enncard := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      rw [h_eq] at h_frostman_2r
      exact h_frostman_2r

    have h_P_le : (P.card : ENNReal) ≤
        (4 * C * Kakeya.realRpowENN r 2 * fine.enncard) /
          (data.fiberMultiplicity : ENNReal) := by
      have h1 : (P.card : ENNReal) * (data.fiberMultiplicity : ENNReal) ≤
          4 * C * Kakeya.realRpowENN r 2 * fine.enncard :=
        le_trans h_main_ennreal h_frostman_2r'
      have h2 : (P.card : ENNReal) ≤
          (4 * C * Kakeya.realRpowENN r 2 * fine.enncard) *
            (data.fiberMultiplicity : ENNReal)⁻¹ := by
        calc
          (P.card : ENNReal)
            = (P.card : ENNReal) * (data.fiberMultiplicity : ENNReal) *
                (data.fiberMultiplicity : ENNReal)⁻¹ := by
              rw [mul_assoc, ENNReal.mul_inv_cancel hfm_pos hfm_top, mul_one]
          _ ≤ (4 * C * Kakeya.realRpowENN r 2 * fine.enncard) *
                (data.fiberMultiplicity : ENNReal)⁻¹ := by gcongr
      simpa [div_eq_mul_inv] using h2

    -- Sum of all fibers = fine.card.
    have h_fiber_union : (Finset.univ : Finset (Fin data.parentCount)).biUnion fiber =
        Finset.univ := by
      rw [Finset.eq_univ_iff_forall]
      intro i
      apply Finset.mem_biUnion.mpr
      refine ⟨data.parent i, Finset.mem_univ _, ?_⟩
      simp [fiber]
      <;> rfl

    have h_fiber_disj_all : Set.PairwiseDisjoint
        (Finset.univ : Finset (Fin data.parentCount)) fiber := by
      intro p _ q _ hne
      simp only [Finset.disjoint_left, fiber, Finset.mem_filter,
        Finset.mem_univ, true_and]
      intro i hpi hqi
      have h1 : data.parent i = p := hpi
      have h2 : data.parent i = q := hqi
      rw [h1] at h2
      exact hne h2

    have h_sum_fibers : ∑ p : Fin data.parentCount, (fiber p).card = fine.card := by
      have h : ∑ p ∈ (Finset.univ : Finset (Fin data.parentCount)), (fiber p).card =
          ((Finset.univ : Finset (Fin data.parentCount)).biUnion fiber).card := by
        rw [Finset.card_biUnion h_fiber_disj_all]
      rw [h, h_fiber_union]
      <;> simp

    -- fine.card ≤ 2 * parentCount * fiberMultiplicity.
    have h_fine_card_le : fine.card ≤ 2 * data.parentCount * data.fiberMultiplicity := by
      calc
        fine.card
          = ∑ p : Fin data.parentCount, (fiber p).card := h_sum_fibers.symm
        _ ≤ ∑ p : Fin data.parentCount, 2 * data.fiberMultiplicity := by
            apply Finset.sum_le_sum
            intro p _
            have h : (fiber p).card < 2 * data.fiberMultiplicity := data.fiber_upper p
            linarith
        _ = data.parentCount * (2 * data.fiberMultiplicity) := by
            simp [Finset.sum_const] <;> ring
        _ = 2 * data.parentCount * data.fiberMultiplicity := by ring

    have h_fine_ennreal : fine.enncard ≤
        2 * (data.parentCount : ENNReal) * (data.fiberMultiplicity : ENNReal) := by
      have h : fine.enncard = (fine.card : ENNReal) := by rfl
      rw [h]
      have h' : (fine.card : ENNReal) ≤
          (↑(2 * data.parentCount * data.fiberMultiplicity) : ENNReal) :=
        Nat.cast_le.mpr h_fine_card_le
      have h_cast : (↑(2 * data.parentCount * data.fiberMultiplicity) : ENNReal) =
          2 * (data.parentCount : ENNReal) * (data.fiberMultiplicity : ENNReal) := by
        simp [Nat.cast_mul]
        <;> norm_num
      rw [h_cast] at h'
      exact h'

    have h_coarse_enncard : data.coarse.enncard = 4 * (data.parentCount : ENNReal) := by
      have h1 : data.coarse.enncard = (data.coarse.card : ENNReal) := by rfl
      rw [h1]
      have h2 : (data.coarse.card : ENNReal) = ((data.parentCount * 4 : ℕ) : ENNReal) := by
        rw [h_coarse_card_eq]
      rw [h2]
      have h3 : ((data.parentCount * 4 : ℕ) : ENNReal) = 4 * (data.parentCount : ENNReal) := by
        calc
          ((data.parentCount * 4 : ℕ) : ENNReal)
            = (data.parentCount : ENNReal) * (4 : ENNReal) := by
              rw [Nat.cast_mul] <;> rfl
          _ = (4 : ENNReal) * (data.parentCount : ENNReal) := by rw [mul_comm]
          _ = 4 * (data.parentCount : ENNReal) := by rfl
      exact h3

    -- fine.enncard / fiberMultiplicity ≤ data.coarse.enncard / 2
    have h_fine_div : fine.enncard / (data.fiberMultiplicity : ENNReal) ≤
        data.coarse.enncard / 2 := by
      have h1 : fine.enncard / (data.fiberMultiplicity : ENNReal) ≤
          (2 * (data.parentCount : ENNReal) * (data.fiberMultiplicity : ENNReal)) /
            (data.fiberMultiplicity : ENNReal) := by
        gcongr
      have h2 : (2 * (data.parentCount : ENNReal) * (data.fiberMultiplicity : ENNReal)) /
            (data.fiberMultiplicity : ENNReal) = 2 * (data.parentCount : ENNReal) := by
        rw [div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel hfm_pos hfm_top, mul_one]
      have h3 : data.coarse.enncard / 2 = 2 * (data.parentCount : ENNReal) := by
        rw [h_coarse_enncard]
        have h4 : (4 * (data.parentCount : ENNReal)) / 2 = 2 * (data.parentCount : ENNReal) := by
          let x := (data.parentCount : ENNReal)
          rw [div_eq_mul_inv]
          have h_comm : (4 * x) * (2 : ENNReal)⁻¹ = (4 * (2 : ENNReal)⁻¹) * x := by
            have h1 : (4 * x) * (2 : ENNReal)⁻¹ = 4 * (x * (2 : ENNReal)⁻¹) := by rw [mul_assoc]
            rw [h1]
            have h2 : x * (2 : ENNReal)⁻¹ = (2 : ENNReal)⁻¹ * x := by rw [mul_comm]
            rw [h2]
            have h3 : 4 * ((2 : ENNReal)⁻¹ * x) = (4 * (2 : ENNReal)⁻¹) * x := by rw [mul_assoc]
            exact h3
          rw [h_comm]
          have h5 : (4 : ENNReal) * (2 : ENNReal)⁻¹ = (2 : ENNReal) := by
            have h6 : (4 : ENNReal) = (2 : ENNReal) * (2 : ENNReal) := by norm_num
            rw [h6, mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by simp)]
            <;> simp
          rw [h5] <;> rfl
        exact h4
      rw [h2] at h1
      rw [h3]
      exact h1

    -- Final calculation.
    have h_final : (B_coarse.card : ENNReal) ≤
        8 * C * Kakeya.realRpowENN r 2 * data.coarse.enncard := by
      have h_card' : (B_coarse.card : ENNReal) = 4 * (P.card : ENNReal) := by
        rw [h_card]
        <;> simp [Nat.cast_mul]
        <;> norm_num
      rw [h_card']
      calc
        4 * (P.card : ENNReal)
          ≤ 4 * ((4 * C * Kakeya.realRpowENN r 2 * fine.enncard) /
                    (data.fiberMultiplicity : ENNReal)) := by gcongr
        _ = 16 * C * Kakeya.realRpowENN r 2 *
              (fine.enncard / (data.fiberMultiplicity : ENNReal)) := by
          have h_eq : 4 * ((4 * C * Kakeya.realRpowENN r 2 * fine.enncard) /
                    (data.fiberMultiplicity : ENNReal)) =
              16 * C * Kakeya.realRpowENN r 2 *
                (fine.enncard / (data.fiberMultiplicity : ENNReal)) := by
            let R := Kakeya.realRpowENN r 2
            let F := fine.enncard
            let m := (data.fiberMultiplicity : ENNReal)
            have h1 : 4 * ((4 * C * R * F) / m) = (4 * (4 * C * R * F)) / m := by
              calc
                4 * ((4 * C * R * F) / m)
                  = 4 * ((4 * C * R * F) * m⁻¹) := by rw [div_eq_mul_inv]
                _ = (4 * (4 * C * R * F)) * m⁻¹ := by
                  exact (mul_assoc (4 : ENNReal) (4 * C * R * F) m⁻¹).symm
                _ = (4 * (4 * C * R * F)) / m := by rw [div_eq_mul_inv]
            rw [h1]
            have h2 : (4 * (4 * C * R * F)) = 16 * C * R * F := by
              have h21 : (4 * (4 * C * R * F)) = (4 * 4 : ENNReal) * (C * R * F) := by
                calc
                  4 * (4 * C * R * F)
                    = 4 * (4 * (C * R * F)) := by simp [mul_assoc]
                  _ = (4 * 4 : ENNReal) * (C * R * F) := by rw [←mul_assoc]
              rw [h21]
              have h22 : (4 * 4 : ENNReal) = (16 : ENNReal) := by norm_num
              rw [h22]
              <;> simp [mul_assoc]
            rw [h2]
            have h3 : (16 * C * R * F) / m = 16 * C * R * (F / m) := by
              simp only [div_eq_mul_inv]
              rw [mul_assoc] <;> rfl
            exact h3
          exact h_eq
        _ ≤ 16 * C * Kakeya.realRpowENN r 2 * (data.coarse.enncard / 2) := by gcongr
        _ = 8 * C * Kakeya.realRpowENN r 2 * data.coarse.enncard := by
          let Z := data.coarse.enncard / 2
          have h_comm : 16 * C * Kakeya.realRpowENN r 2 * Z =
              C * Kakeya.realRpowENN r 2 * (16 * Z) := by
            let R := Kakeya.realRpowENN r 2
            calc
              16 * C * R * Z
                = (16 * C) * (R * Z) := by rw [mul_assoc]
              _ = 16 * (C * (R * Z)) := by rw [mul_assoc]
              _ = C * (16 * (R * Z)) := by rw [mul_left_comm]
              _ = C * (R * (16 * Z)) := by
                have h : 16 * (R * Z) = R * (16 * Z) := by rw [mul_left_comm]
                rw [h]
              _ = C * R * (16 * Z) := by rw [mul_assoc]
          have h16 : 16 * Z = 8 * data.coarse.enncard := by
            dsimp only [Z]
            have h2 : data.coarse.enncard / 2 = (2 : ENNReal)⁻¹ * data.coarse.enncard := by
              rw [div_eq_mul_inv, mul_comm]
            rw [h2]
            have h3 : 16 * ((2 : ENNReal)⁻¹ * data.coarse.enncard) =
                (16 * (2 : ENNReal)⁻¹) * data.coarse.enncard := by
              rw [mul_assoc]
            rw [h3]
            have h4 : 16 * (2 : ENNReal)⁻¹ = 8 := by
              have h5 : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 :=
                ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
              have h6 : (16 : ENNReal) = 8 * (2 : ENNReal) := by norm_num
              calc
                (16 : ENNReal) * (2 : ENNReal)⁻¹
                  = (8 * (2 : ENNReal)) * (2 : ENNReal)⁻¹ := by rw [h6]
                _ = 8 * ((2 : ENNReal) * (2 : ENNReal)⁻¹) := by rw [mul_assoc]
                _ = 8 := by rw [h5] <;> simp
            rw [h4] <;> rfl
          calc
            16 * C * Kakeya.realRpowENN r 2 * Z
              = C * Kakeya.realRpowENN r 2 * (16 * Z) := h_comm
            _ = C * Kakeya.realRpowENN r 2 * (8 * data.coarse.enncard) := by rw [h16]
            _ = 8 * C * Kakeya.realRpowENN r 2 * data.coarse.enncard := by
              simp [mul_assoc, mul_comm, mul_left_comm] <;> rfl

    exact h_final

  · -- Case 2: r > 1/2, trivial total-cardinality bound.
    have h_r_gt_half : 1 / 2 < r := by linarith
    have hr_nonneg : 0 ≤ r := by linarith
    have h_r2_ge : (1 / 4 : ℝ) ≤ r ^ 2 := by nlinarith

    have h_rpow_eq : Kakeya.realRpowENN r 2 = ENNReal.ofReal (r ^ 2) := by
      simp [Kakeya.realRpowENN, Real.rpow_two]
      <;> rfl

    have h4 : (1 / 4 : ENNReal) ≤ Kakeya.realRpowENN r 2 := by
      rw [h_rpow_eq]
      have h5 : (1 / 4 : ℝ) ≤ r ^ 2 := h_r2_ge
      have h6 : (1 / 4 : ENNReal) = ENNReal.ofReal (1 / 4 : ℝ) := by
        simp
      rw [h6]
      exact ENNReal.ofReal_le_ofReal h5

    have h84 : (8 : ENNReal) * ENNReal.ofReal (1 / 4 : ℝ) = 2 := by
      have h_mul : (8 : ENNReal) * ENNReal.ofReal (1 / 4 : ℝ) =
          ENNReal.ofReal ((8 : ℝ) * (1 / 4 : ℝ)) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        <;> norm_cast
      rw [h_mul]
      have h_eq : (8 : ℝ) * (1 / 4 : ℝ) = 2 := by norm_num
      rw [h_eq]
      <;> simp

    have h_one_le : (1 : ENNReal) ≤ 8 * C * Kakeya.realRpowENN r 2 := by
      have hC : (1 : ENNReal) ≤ C := hC_one
      have h_rpow : Kakeya.realRpowENN r 2 = ENNReal.ofReal (r ^ 2) := h_rpow_eq
      rw [h_rpow]
      have h_ge : ENNReal.ofReal (1 / 4 : ℝ) ≤ ENNReal.ofReal (r ^ 2) :=
        ENNReal.ofReal_le_ofReal h_r2_ge
      have h_main : (2 : ENNReal) ≤ (8 : ENNReal) * C * ENNReal.ofReal (r ^ 2) := by
        calc
          (2 : ENNReal)
            = (8 : ENNReal) * ENNReal.ofReal (1 / 4 : ℝ) := h84.symm
          _ = (8 : ENNReal) * (1 : ENNReal) * ENNReal.ofReal (1 / 4 : ℝ) := by simp
          _ ≤ (8 : ENNReal) * C * ENNReal.ofReal (r ^ 2) := by gcongr
      have h1 : (1 : ENNReal) ≤ (2 : ENNReal) := by norm_num
      exact le_trans h1 h_main

    have h_subset : B_coarse ⊆ (Finset.univ : Finset (Fin data.coarse.card)) :=
      Finset.subset_univ B_coarse
    have h_univ_card : (Finset.univ : Finset (Fin data.coarse.card)).card = data.coarse.card := by
      simp
    have h_card_nat : B_coarse.card ≤ data.coarse.card := by
      have h : B_coarse.card ≤ (Finset.univ : Finset (Fin data.coarse.card)).card :=
        Finset.card_le_card h_subset
      rw [h_univ_card] at h
      exact h
    have h_card_le : (B_coarse.card : ENNReal) ≤ data.coarse.enncard := by
      have h1 : (B_coarse.card : ENNReal) ≤ (data.coarse.card : ENNReal) :=
        Nat.cast_le.mpr h_card_nat
      have h2 : data.coarse.enncard = (data.coarse.card : ENNReal) := by rfl
      rw [h2]
      exact h1

    calc
      (B_coarse.card : ENNReal)
        ≤ data.coarse.enncard := h_card_le
      _ = (1 : ENNReal) * data.coarse.enncard := by simp
      _ ≤ (8 * C * Kakeya.realRpowENN r 2) * data.coarse.enncard := by gcongr

end Kakeya.Assouad
