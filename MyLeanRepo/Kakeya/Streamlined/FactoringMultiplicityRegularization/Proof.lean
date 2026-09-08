import MyLeanRepo.Kakeya.Streamlined.FactoringMultiplicityRegularization
import MyLeanRepo.Kakeya.Streamlined.FactoringMultiplicityRegularization.Helpers
import MyLeanRepo.Kakeya.Streamlined.MaximalDensityFactoring.SubfamilyHelpers

/-!
# Proof of factoring multiplicity regularization
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

theorem factoring_multiplicity_regularization_main :
    FactoringMultiplicityRegularizationStatement := by
  dsimp only [FactoringMultiplicityRegularizationStatement]
  intro fine coarse P Y Z hY_pos hcompat
  classical

  set N : ℕ := fine.card with hN
  have hN_pos : 0 < N := by
    by_contra h
    have h' : N = 0 := by omega
    have h_fine_empty : fine.card = 0 := by
      rw [←hN, h']
    haveI : IsEmpty (Fin fine.card) := by
      rw [h_fine_empty] <;> infer_instance
    have hY_zero : Y.mass = 0 := by simp [Shading.mass]
    exact False.elim (hY_pos.ne' hY_zero)

  set L : ℕ := Nat.log 2 N + 1 with hL_def
  set L' : ENNReal := (L : ENNReal) with hL'
  have hL'_ne_zero : L' ≠ 0 := by
    simp [hL', hL_def, L] <;> norm_num <;> omega
  have hL'_ne_top : L' ≠ ⊤ := by
    simp [hL'] <;> exact ENNReal.coe_ne_top

  have h_coarse_card_le : coarse.card ≤ N := by
    have h1 : Finset.image P.parent (Finset.univ : Finset (Fin N)) =
        (Finset.univ : Finset (Fin coarse.card)) := by
      apply Finset.eq_univ_of_forall
      intro j
      rcases P.parent_surjective j with ⟨i, hi⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
    have h2 : (Finset.image P.parent (Finset.univ : Finset (Fin N))).card ≤
        (Finset.univ : Finset (Fin N)).card := Finset.card_image_le
    rw [h1] at h2
    have h3 : (Finset.univ : Finset (Fin coarse.card)).card = coarse.card :=
      Finset.card_fin coarse.card
    have h4 : (Finset.univ : Finset (Fin N)).card = N := Finset.card_fin N
    rw [h3, h4] at h2
    exact h2

  have h_stage1 : ∀ (j : Fin coarse.card),
      ∃ (k_j : ℕ) (Ω_j : Set Point3) (hΩ_j : MeasurableSet Ω_j),
        k_j ≤ Nat.log 2 N ∧
        (∀ x ∈ Ω_j, 2 ^ k_j ≤ P.fiberPointMultiplicity Y j x ∧
                      P.fiberPointMultiplicity Y j x < 2 ^ (k_j + 1)) ∧
        (∑ i ∈ P.fiberIndices j, volume (Y.carrier i ∩ Ω_j)) * L' ≥
          P.fiberShadedMass Y j := by
    intro j
    rcases P.fiber_multiplicity_pigeonhole Y hN_pos j with
      ⟨k_j, Ω_j, hΩ_j, h_k, h_mult, h_mass⟩
    have h_conv :
        (∑ i ∈ P.fiberIndices j, volume (Y.carrier i ∩ Ω_j)) * L' ≥
          P.fiberShadedMass Y j := by
      have h_eq : L' = (Nat.log 2 N + 1 : ENNReal) := by
        simp [hL', hL_def, L] <;> rfl
      rw [h_eq]
      exact h_mass
    exact ⟨k_j, Ω_j, hΩ_j, h_k, h_mult, h_conv⟩

  choose k Ω hΩ h_k_le h_mult1 h_mass1 using h_stage1

  let m : Fin coarse.card → ENNReal := fun j =>
    ∑ i ∈ P.fiberIndices j, volume (Y.carrier i ∩ Ω j)

  have h_k_bound : ∀ j, k j < L := by
    intro j
    have h1 : k j ≤ Nat.log 2 N := h_k_le j
    simp [hL_def, L] at * <;> omega

  have h_fiber_disj : ∀ (j1 j2 : Fin coarse.card), j1 ≠ j2 →
      Disjoint (P.fiberIndices j1) (P.fiberIndices j2) := by
    intro j1 j2 hne
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have h4 : P.parent i = j1 := (Finset.mem_filter.mp hi1).2
    have h5 : P.parent i = j2 := (Finset.mem_filter.mp hi2).2
    rw [h4] at h5
    exact hne h5

  have h_fiber_sum : ∑ j : Fin coarse.card, P.fiberShadedMass Y j = Y.mass := by
    dsimp only [Factoring.fiberShadedMass, Shading.mass]
    have h_union :
        (Finset.univ : Finset (Fin coarse.card)).biUnion P.fiberIndices =
          (Finset.univ : Finset (Fin N)) := by
      apply Finset.ext
      intro i
      constructor
      · intro _
        exact Finset.mem_univ i
      · intro _
        have h_i_in : i ∈ P.fiberIndices (P.parent i) := by
          simp [Factoring.fiberIndices] <;> tauto
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨P.parent i, h_i_in⟩
    have h_sum :
        ∑ j : Fin coarse.card, ∑ i ∈ P.fiberIndices j, volume (Y.carrier i) =
          ∑ i ∈ (Finset.univ : Finset (Fin N)), volume (Y.carrier i) := by
      rw [← Finset.sum_biUnion (fun j1 _ j2 _ => h_fiber_disj j1 j2), h_union]
    rw [h_sum] <;> simp

  have h_sum_mass : (∑ j : Fin coarse.card, m j) * L' ≥ Y.mass := by
    have h1 : ∀ j, m j * L' ≥ P.fiberShadedMass Y j := h_mass1
    have h2 : (∑ j : Fin coarse.card, m j) * L' =
        ∑ j : Fin coarse.card, (m j * L') := by
      rw [Finset.sum_mul] <;> rfl
    rw [h2]
    have h3 : ∑ j : Fin coarse.card, (m j * L') ≥
        ∑ j : Fin coarse.card, P.fiberShadedMass Y j := by
      apply Finset.sum_le_sum
      intro j _
      exact h1 j
    rw [h_fiber_sum] at *
    exact h3

  have h_stage2 := dominant_level_selection k m h_k_bound
  rcases h_stage2 with ⟨k_fiber, h_dom⟩

  let J : Finset (Fin coarse.card) :=
    Finset.univ.filter (fun j => k j = k_fiber)
  let I : Finset (Fin N) :=
    Finset.univ.filter (fun i => P.parent i ∈ J)

  have h_M : (∑ j ∈ J, m j) * L' ≥ ∑ j : Fin coarse.card, m j := by
    have h_eq : L' = (Nat.log 2 N + 1 : ENNReal) := by
      simp [hL', hL_def, L] <;> rfl
    have h : L' * (∑ j ∈ J, m j) ≥ ∑ j : Fin coarse.card, m j := by
      rw [h_eq]
      exact h_dom
    have h_comm : (∑ j ∈ J, m j) * L' = L' * (∑ j ∈ J, m j) := by ring
    rw [h_comm]
    exact h

  let S_fine := subfamilyFromFinset fine I
  let S_coarse := subfamilyFromFinset coarse J

  let Y' : Shading S_fine.family :=
    { carrier := fun i =>
        Y.carrier (S_fine.embedding i) ∩ Ω (P.parent (S_fine.embedding i))
      measurable_carrier := fun i =>
        (Y.measurable_carrier (S_fine.embedding i)).inter
          (hΩ (P.parent (S_fine.embedding i)))
      subset_body := fun i =>
        Set.inter_subset_left.trans (Y.subset_body (S_fine.embedding i)) }

  have h_parent_in_J : ∀ (i : Fin S_fine.family.card),
      P.parent (S_fine.embedding i) ∈ J := by
    intro i
    have h1 : S_fine.embedding i ∈ I :=
      subfamilyFromFinset_embedding_mem fine I i
    simpa [I, Finset.mem_filter] using h1

  have hY'_mass : Y'.mass = ∑ j ∈ J, m j := by
    dsimp only [Y', Shading.mass, m]
    let e : Fin S_fine.family.card ↪ Fin N := S_fine.embedding
    have h_image : Finset.image e Finset.univ = I := subfamilyFromFinset_image_eq
    have h_disj : ∀ j1 ∈ J, ∀ j2 ∈ J, j1 ≠ j2 →
        Disjoint (P.fiberIndices j1) (P.fiberIndices j2) := by
      intro j1 _ j2 _ hne
      exact h_fiber_disj j1 j2 hne
    have h_union : J.biUnion P.fiberIndices = I := by
      apply Finset.ext
      intro i
      constructor
      · intro h
        have h_exists : ∃ j ∈ J, i ∈ P.fiberIndices j := by
          simpa [Finset.mem_biUnion] using h
        rcases h_exists with ⟨j, hj, hfi⟩
        have h6 : P.parent i = j := (Finset.mem_filter.mp hfi).2
        have h7 : P.parent i ∈ J := by
          rw [h6]
          exact hj
        have h_goal : i ∈ I := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ i, h7⟩
        exact h_goal
      · intro h
        have hpi : P.parent i ∈ J := by
          have h_in_I : i ∈ I := h
          exact (Finset.mem_filter.mp h_in_I).2
        have h_i_in_fiber : i ∈ P.fiberIndices (P.parent i) := by
          simp [Factoring.fiberIndices] <;> tauto
        have h_goal : i ∈ J.biUnion P.fiberIndices := by
          apply Finset.mem_biUnion.mpr
          exact ⟨P.parent i, hpi, h_i_in_fiber⟩
        exact h_goal
    calc
      ∑ i : Fin S_fine.family.card,
          volume (Y.carrier (e i) ∩ Ω (P.parent (e i)))
        = ∑ idx ∈ Finset.image e Finset.univ,
            volume (Y.carrier idx ∩ Ω (P.parent idx)) := by
          have h_inj :
              Set.InjOn e (Finset.univ : Finset (Fin S_fine.family.card)) :=
            fun i _ j _ h => e.inj' h
          rw [Finset.sum_image h_inj]
      _ = ∑ idx ∈ I, volume (Y.carrier idx ∩ Ω (P.parent idx)) := by
          rw [h_image]
      _ = ∑ j ∈ J, ∑ i ∈ P.fiberIndices j,
          volume (Y.carrier i ∩ Ω (P.parent i)) := by
          rw [← h_union, Finset.sum_biUnion h_disj] <;> rfl
      _ = ∑ j ∈ J, ∑ i ∈ P.fiberIndices j,
          volume (Y.carrier i ∩ Ω j) := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro i hi
          have h6 : P.parent i = j := (Finset.mem_filter.mp hi).2
          rw [h6]

  let f : Point3 → ℕ := fun x =>
    (J.filter (fun j => x ∈ Z.carrier j)).card
  let w : Point3 → ENNReal := fun x => (Y'.pointMultiplicity x : ENNReal)

  have hf_meas : Measurable f := by
    have h1 : f = fun x =>
        ∑ j ∈ J, Set.indicator (Z.carrier j) (fun _ => (1 : ℕ)) x := by
      funext x
      classical
      simp [f, Finset.sum_boole, Set.indicator_apply] <;> rfl
    rw [h1]
    apply Finset.measurable_sum
    intro j _
    exact Measurable.indicator (by fun_prop) (Z.measurable_carrier j)

  have hw_meas : Measurable w := Y'.pointMultiplicity_measurable

  have h_f_bound : ∀ x, f x ≤ N := by
    intro x
    have h1 : f x ≤ J.card := by
      dsimp only [f]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    have h2 : J.card ≤ coarse.card := by
      have h21 : J ⊆ (Finset.univ : Finset (Fin coarse.card)) := by simp
      have h22 := Finset.card_le_card h21
      have h23 : (Finset.univ : Finset (Fin coarse.card)).card = coarse.card :=
        Finset.card_fin coarse.card
      rw [h23] at h22
      exact h22
    have h3 : J.card ≤ N := by linarith [h_coarse_card_le]
    exact le_trans h1 h3

  have h_support : ∀ x, w x ≠ 0 → 0 < f x := by
    intro x hwx
    have h_pos : 0 < Y'.pointMultiplicity x := by
      by_contra h
      have h' : Y'.pointMultiplicity x = 0 := by omega
      have h'' : w x = 0 := by
        simp [w, h']
      exact hwx h''
    have h_pos_card :
        0 < (Finset.univ.filter fun i : Fin S_fine.family.card =>
          x ∈ Y'.carrier i).card := by
      have h_eq : Y'.pointMultiplicity x =
          (Finset.univ.filter fun i : Fin S_fine.family.card =>
            x ∈ Y'.carrier i).card := by
        simp [Shading.pointMultiplicity] <;> congr
      rw [← h_eq]
      exact h_pos
    rcases Finset.card_pos.mp h_pos_card with ⟨i, hi⟩
    have h10 : x ∈ Y'.carrier i := (Finset.mem_filter.mp hi).2
    have h_in_Y : x ∈ Y.carrier (S_fine.embedding i) :=
      Set.inter_subset_left h10
    have h_in_Z : x ∈ Z.carrier (P.parent (S_fine.embedding i)) :=
      hcompat x (by exact ⟨S_fine.embedding i, h_in_Y⟩)
        (S_fine.embedding i) h_in_Y
    have h_parent_in_J' : P.parent (S_fine.embedding i) ∈ J := h_parent_in_J i
    have h4 : P.parent (S_fine.embedding i) ∈
        J.filter (fun j => x ∈ Z.carrier j) := by
      simp only [Finset.mem_filter]
      exact ⟨h_parent_in_J', h_in_Z⟩
    have h5 : 0 < (J.filter (fun j => x ∈ Z.carrier j)).card :=
      Finset.card_pos.mpr ⟨_, h4⟩
    exact h5

  rcases weighted_dyadic_pigeonhole hN_pos f hf_meas h_f_bound w hw_meas h_support
    with ⟨b, Ω_coarse, hΩ_coarse, h_mult_coarse, h_mass_coarse⟩

  let Y_final : Shading S_fine.family :=
    { carrier := fun i => Y'.carrier i ∩ Ω_coarse
      measurable_carrier := fun i =>
        (Y'.measurable_carrier i).inter hΩ_coarse
      subset_body := fun i =>
        Set.inter_subset_left.trans (Y'.subset_body i) }

  let Z_final : Shading S_coarse.family :=
    { carrier := fun j => Z.carrier (S_coarse.embedding j) ∩ Ω_coarse
      measurable_carrier := fun j =>
        (Z.measurable_carrier (S_coarse.embedding j)).inter hΩ_coarse
      subset_body := fun j =>
        Set.inter_subset_left.trans (Z.subset_body (S_coarse.embedding j)) }

  have h_map : ∀ (i : Fin S_fine.family.card),
      P.parent (S_fine.embedding i) ∈ Set.range S_coarse.embedding := by
    intro i
    have h1 : P.parent (S_fine.embedding i) ∈ J := h_parent_in_J i
    have h2 : J = Finset.image S_coarse.embedding Finset.univ :=
      Eq.symm subfamilyFromFinset_image_eq
    rw [h2] at h1
    rcases Finset.mem_image.mp h1 with ⟨j, _, h_eq⟩
    exact ⟨j, h_eq⟩

  have h_surj : ∀ (j : Fin S_coarse.family.card),
      ∃ (i : Fin S_fine.family.card),
        P.parent (S_fine.embedding i) = S_coarse.embedding j := by
    intro j
    have h1 : S_coarse.embedding j ∈ J :=
      subfamilyFromFinset_embedding_mem coarse J j
    rcases P.parent_surjective (S_coarse.embedding j) with ⟨i, hi⟩
    have h_i_in_I : i ∈ I := by
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hi]
      exact h1
    have h_exists :
        ∃ (i' : Fin S_fine.family.card), S_fine.embedding i' = i := by
      have h_image : Finset.image S_fine.embedding Finset.univ = I :=
        subfamilyFromFinset_image_eq
      have h_in_image : i ∈ Finset.image S_fine.embedding Finset.univ := by
        rw [h_image]
        exact h_i_in_I
      rcases Finset.mem_image.mp h_in_image with ⟨i', _, h_eq⟩
      exact ⟨i', h_eq⟩
    rcases h_exists with ⟨i', h_eq⟩
    refine ⟨i', ?_⟩
    rw [h_eq, hi]

  let P' := P.restrict S_fine S_coarse h_map h_surj

  let R_ref : Refinement Y :=
    { subfamily := S_fine
      shading := Y_final
      shading_subset := fun i =>
        Set.inter_subset_left.trans Set.inter_subset_left }

  let FR : FactoringRefinement P Y :=
    { fineRefinement := R_ref
      coarseSubfamily := S_coarse
      factoring := P'
      compatible := P.restrict_compatible S_fine S_coarse h_map h_surj
      coarseShading := Z_final }

  have h_mass3 : Y_final.mass * L' ≥ Y'.mass := by
    have h_eq1 : Y_final.mass = ∫⁻ x in Ω_coarse, w x := by
      dsimp only [Y_final]
      exact restrict_mass_eq_set_lintegral hΩ_coarse
    rw [h_eq1]
    have h_total : (∫⁻ x, w x) = Y'.mass :=
      lintegral_pointMultiplicity_eq_mass Y'
    rw [h_total] at h_mass_coarse
    have h_conv : (∫⁻ x in Ω_coarse, w x) * L' ≥ Y'.mass := by
      have hL_eq : L' = (Nat.log 2 N + 1 : ENNReal) := by
        simp [hL', hL_def, L] <;> norm_cast
      rw [hL_eq]
      exact h_mass_coarse
    exact h_conv

  have h_chain : Y_final.mass * (L' ^ 3) ≥ Y.mass := by
    calc
      Y_final.mass * (L' ^ 3)
        = (Y_final.mass * L') * L' * L' := by ring
      _ ≥ Y'.mass * L' * L' := by gcongr
      _ = (Y'.mass * L') * L' := by ring
      _ = (∑ j ∈ J, m j) * L' * L' := by rw [hY'_mass] <;> ring
      _ ≥ (∑ j : Fin coarse.card, m j) * L' := by
        exact mul_le_mul_right' h_M L'
      _ ≥ Y.mass := h_sum_mass

  have hL3_ne_zero : (L' ^ 3) ≠ 0 := by
    simp [hL'] <;> positivity
  have hL3_ne_top : (L' ^ 3) ≠ ⊤ := by
    exact ENNReal.coe_ne_top

  have h_retention : (L' ^ 3)⁻¹ * Y.mass ≤ Y_final.mass := by
    have h : Y_final.mass * (L' ^ 3) ≥ Y.mass := h_chain
    have h' : (L' ^ 3)⁻¹ * Y.mass ≤
        (L' ^ 3)⁻¹ * (Y_final.mass * (L' ^ 3)) := by
      gcongr
    have h'' : (L' ^ 3)⁻¹ * (Y_final.mass * (L' ^ 3)) = Y_final.mass := by
      have h3 : (L' ^ 3)⁻¹ * (Y_final.mass * (L' ^ 3)) =
          ((L' ^ 3)⁻¹ * (L' ^ 3)) * Y_final.mass := by ring
      rw [h3, ENNReal.inv_mul_cancel hL3_ne_zero hL3_ne_top, one_mul]
    rw [h''] at h'
    exact h'

  let mfiber : ℕ := 2 ^ k_fiber
  let Mfiber : ℕ := 2 ^ (k_fiber + 1) - 1
  let mcoarse : ℕ := 2 ^ b
  let Mcoarse : ℕ := 2 ^ (b + 1) - 1

  have h_mfiber_pos : 1 ≤ mfiber := by
    dsimp only [mfiber]
    apply Nat.one_le_pow
    <;> norm_num

  have h_Mfiber_le : (Mfiber : ENNReal) ≤ 2 * (mfiber : ENNReal) := by
    dsimp only [Mfiber, mfiber]
    have h : (2 ^ (k_fiber + 1) - 1 : ℕ) ≤ 2 * 2 ^ k_fiber := by omega
    exact_mod_cast h

  have h_mcoarse_pos : 1 ≤ mcoarse := by
    dsimp only [mcoarse]
    apply Nat.one_le_pow
    <;> norm_num

  have h_Mcoarse_le : (Mcoarse : ENNReal) ≤ 2 * (mcoarse : ENNReal) := by
    dsimp only [Mcoarse, mcoarse]
    have h : (2 ^ (b + 1) - 1 : ℕ) ≤ 2 * 2 ^ b := by omega
    exact_mod_cast h

  have h_coarse_mult : Z_final.HasConstantMultiplicity mcoarse Mcoarse := by
    intro x hx
    rcases hx with ⟨j, hj⟩
    have h_x_in_Ω : x ∈ Ω_coarse := Set.inter_subset_right hj
    have h1 : 2 ^ b ≤ f x ∧ f x < 2 ^ (b + 1) :=
      h_mult_coarse x h_x_in_Ω
    let e : Fin S_coarse.family.card ↪ Fin coarse.card := S_coarse.embedding
    have h_img : Finset.image e Finset.univ = J :=
      subfamilyFromFinset_image_eq
    have h_filter_eq :
        (Finset.univ.filter fun j' : Fin S_coarse.family.card =>
          x ∈ Z_final.carrier j') =
        Finset.univ.filter fun j' : Fin S_coarse.family.card =>
          x ∈ Z.carrier (e j') := by
      ext j'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h_eq : x ∈ Z_final.carrier j' ↔ x ∈ Z.carrier (e j') := by
        dsimp only [Z_final]
        simp [h_x_in_Ω] <;> tauto
      exact h_eq
    have h_card :
        (Finset.univ.filter fun j' : Fin S_coarse.family.card =>
          x ∈ Z.carrier (e j')).card =
        (J.filter (fun j => x ∈ Z.carrier j)).card := by
      let s := Finset.univ.filter fun j' : Fin S_coarse.family.card =>
        x ∈ Z.carrier (e j')
      have h_img2 : Finset.image e s =
          J.filter (fun j => x ∈ Z.carrier j) := by
        ext z
        simp only [Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨j', hj', rfl⟩
          have h_in_s : x ∈ Z.carrier (e j') :=
            (Finset.mem_filter.mp hj').2
          have h_in_J : e j' ∈ J := by
            rw [← h_img]
            exact Finset.mem_image_of_mem e (Finset.mem_univ j')
          exact ⟨h_in_J, h_in_s⟩
        · rintro ⟨hz1, hz2⟩
          have h_in_img : z ∈ Finset.image e Finset.univ := by
            exact h_img.symm ▸ hz1
          rcases Finset.mem_image.mp h_in_img with ⟨j', _, rfl⟩
          have h_in_s : j' ∈ s := by
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_univ j', hz2⟩
          exact ⟨j', h_in_s, rfl⟩
      have h_card1 : (Finset.image e s).card = s.card :=
        Finset.card_image_of_injective s e.inj'
      rw [← h_card1, h_img2]
    have h_pointmult : Z_final.pointMultiplicity x =
        (Finset.univ.filter fun j' : Fin S_coarse.family.card =>
          x ∈ Z_final.carrier j').card := by
      simp [Shading.pointMultiplicity] <;> congr
    have h2 : Z_final.pointMultiplicity x = f x := by
      rw [h_pointmult, h_filter_eq, h_card] <;> rfl
    rw [h2]
    have h_lower : mcoarse ≤ f x := by
      dsimp only [mcoarse]
      exact h1.1
    have h_upper : f x ≤ Mcoarse := by
      dsimp only [Mcoarse]
      omega
    exact ⟨h_lower, h_upper⟩

  have h_fiber_mult : ∀ (j : Fin S_coarse.family.card),
      P'.FiberHasConstantMultiplicity Y_final j mfiber Mfiber := by
    intro j
    let j_orig := S_coarse.embedding j
    have h_j_in_J : j_orig ∈ J :=
      subfamilyFromFinset_embedding_mem coarse J j
    have h_k_eq : k j_orig = k_fiber := by
      simp only [J, Finset.mem_filter] at h_j_in_J
      exact h_j_in_J.2

    intro x hx
    rcases hx with ⟨i, h_i_in_fiber, hxi⟩
    have h_x_in_Yfinal : x ∈ Y_final.carrier i := hxi
    have h_x_in_Y' : x ∈ Y'.carrier i :=
      Set.inter_subset_left h_x_in_Yfinal
    have h_x_in_Ω_coarse : x ∈ Ω_coarse :=
      Set.inter_subset_right h_x_in_Yfinal
    have h_parent_eq : P.parent (S_fine.embedding i) = j_orig := by
      have h4 : S_coarse.embedding (P'.parent i) =
          P.parent (S_fine.embedding i) :=
        P.restrict_compatible S_fine S_coarse h_map h_surj i
      have h5 : P'.parent i = j := h_i_in_fiber
      rw [h5] at h4
      exact h4.symm
    have h_x_in_Ωj : x ∈ Ω j_orig := by
      dsimp only [Y'] at h_x_in_Y'
      have h6 : x ∈ Ω (P.parent (S_fine.embedding i)) := h_x_in_Y'.2
      rw [h_parent_eq] at h6
      exact h6

    let e : Fin S_fine.family.card ↪ Fin N := S_fine.embedding
    have h_iff : ∀ (i : Fin S_fine.family.card),
        (P'.parent i = j ∧ x ∈ Y_final.carrier i) ↔
        (P.parent (e i) = j_orig ∧ x ∈ Y.carrier (e i)) := by
      intro i
      have h4 : S_coarse.embedding (P'.parent i) = P.parent (e i) :=
        P.restrict_compatible S_fine S_coarse h_map h_surj i
      constructor
      · rintro ⟨hpar, hcar⟩
        have hpe : P.parent (e i) = j_orig := by
          rw [← h4, hpar] <;> rfl
        have h6 : x ∈ Y.carrier (e i) := by
          dsimp only [Y_final, Y'] at hcar
          exact Set.inter_subset_left (Set.inter_subset_left hcar)
        exact ⟨hpe, h6⟩
      · rintro ⟨hpe, hcar⟩
        have hpar : P'.parent i = j := by
          have h5 : S_coarse.embedding (P'.parent i) =
              S_coarse.embedding j := by
            rw [h4, hpe]
          exact S_coarse.embedding.inj' h5
        have hcar' : x ∈ Y_final.carrier i := by
          dsimp only [Y_final, Y']
          have h_Ω : x ∈ Ω (P.parent (e i)) := by
            rw [hpe]
            exact h_x_in_Ωj
          exact ⟨⟨hcar, h_Ω⟩, h_x_in_Ω_coarse⟩
        exact ⟨hpar, hcar'⟩
    have h1 : P'.fiberPointMultiplicity Y_final j x =
        P.fiberPointMultiplicity Y j_orig x := by
      dsimp only [Factoring.fiberPointMultiplicity]
      have h_fib : P'.fiberIndices j =
          Finset.univ.filter (fun i => P'.parent i = j) := by
        ext i
        simp [Factoring.fiberIndices] <;> tauto
      have h3 : ∀ (i : Fin S_fine.family.card), P'.parent i = j ↔
          P.parent (S_fine.embedding i) = j_orig := by
        intro i
        have h4 : S_coarse.embedding (P'.parent i) =
            P.parent (S_fine.embedding i) :=
          P.restrict_compatible S_fine S_coarse h_map h_surj i
        constructor
        · intro h
          rw [h] at h4
          exact h4.symm
        · intro h
          have h5 : S_coarse.embedding (P'.parent i) =
              S_coarse.embedding j := by
            rw [h4, h]
          exact S_coarse.embedding.inj' h5
      have h4_eq :
          (Finset.univ.filter fun (i : Fin S_fine.family.card) =>
            P'.parent i = j) =
          Finset.univ.filter fun (i : Fin S_fine.family.card) =>
            P.parent (S_fine.embedding i) = j_orig := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact h3 i
      rw [h_fib, h4_eq]
      let e : Fin S_fine.family.card ↪ Fin N := S_fine.embedding
      have h6 : ∀ (i : Fin S_fine.family.card),
          x ∈ Y_final.carrier i ↔
            x ∈ Y.carrier (S_fine.embedding i) ∧
              x ∈ Ω (P.parent (S_fine.embedding i)) := by
        intro i
        dsimp only [Y_final, Y']
        simp [h_x_in_Ω_coarse, Set.mem_inter_iff] <;> tauto
      let s1 : Finset (Fin S_fine.family.card) :=
        (Finset.univ.filter fun (i : Fin S_fine.family.card) =>
          P.parent (S_fine.embedding i) = j_orig).filter
            (fun i => x ∈ Y_final.carrier i)
      let s2 : Finset (Fin S_fine.family.card) :=
        (Finset.univ.filter fun (i : Fin S_fine.family.card) =>
          P.parent (S_fine.embedding i) = j_orig).filter
            (fun i => x ∈ Y.carrier (S_fine.embedding i) ∧
              x ∈ Ω (P.parent (S_fine.embedding i)))
      have h_s1_s2 : s1.card = s2.card := by
        apply congr_arg Finset.card
        ext i
        dsimp only [s1, s2]
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, (h6 i).mp h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, (h6 i).mpr h2⟩
      have h_image : Finset.image e Finset.univ = I :=
        subfamilyFromFinset_image_eq
      have h9 : Finset.image e s2 =
          (P.fiberIndices j_orig).filter
            (fun i => x ∈ Y.carrier i ∧ x ∈ Ω j_orig) := by
        ext idx
        dsimp only [s2]
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, h_i_in, h_eq⟩
          rcases h_i_in with ⟨hpar, hcar, hΩ⟩
          have h10 : P.parent idx = j_orig := by
            rw [← h_eq]
            exact hpar
          have h11 : x ∈ Y.carrier idx := by
            rw [← h_eq]
            exact hcar
          have h12 : x ∈ Ω j_orig := by
            rw [hpar] at hΩ
            exact hΩ
          exact ⟨by simpa [Factoring.fiberIndices] using h10, h11, h12⟩
        · rintro ⟨h_in_fiber, hcar, hΩ⟩
          have h10 : P.parent idx = j_orig := by
            simpa [Factoring.fiberIndices] using h_in_fiber
          have h_in_I : idx ∈ I := by
            simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, h10]
            exact h_j_in_J
          have h_exists : ∃ (i : Fin S_fine.family.card), e i = idx := by
            have h_in_image : idx ∈ Finset.image e Finset.univ := by
              rw [h_image]
              exact h_in_I
            rcases Finset.mem_image.mp h_in_image with ⟨i, _, h_eq⟩
            exact ⟨i, h_eq⟩
          rcases h_exists with ⟨i, h_eq⟩
          have hpar : P.parent (e i) = j_orig := by
            rw [h_eq]
            exact h10
          have hcar' : x ∈ Y.carrier (e i) := by
            rw [h_eq]
            exact hcar
          have hΩ' : x ∈ Ω (P.parent (e i)) := by
            rw [hpar]
            exact hΩ
          have h_i_in_s2 : i ∈ s2 := by
            dsimp only [s2]
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hpar, hcar', hΩ'⟩
          exact ⟨i,
            by simpa [s2, Finset.mem_filter, Finset.mem_univ] using h_i_in_s2,
            h_eq⟩
      have h10 : (Finset.image e s2).card = s2.card :=
        Finset.card_image_of_injective s2 e.inj'
      have h11 :
          (P.fiberIndices j_orig).filter
              (fun i => x ∈ Y.carrier i ∧ x ∈ Ω j_orig) =
            (P.fiberIndices j_orig).filter (fun i => x ∈ Y.carrier i) := by
        ext i
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, h2.1⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, h2, h_x_in_Ωj⟩
      have h_main :
          s1.card =
            ((P.fiberIndices j_orig).filter (fun i => x ∈ Y.carrier i)).card := by
        calc
          s1.card = s2.card := h_s1_s2
          _ = (Finset.image e s2).card := h10.symm
          _ = ((P.fiberIndices j_orig).filter
              (fun i => x ∈ Y.carrier i ∧ x ∈ Ω j_orig)).card := by
                rw [h9]
          _ = ((P.fiberIndices j_orig).filter
              (fun i => x ∈ Y.carrier i)).card := by
                rw [h11]
      convert h_main <;> simp [s1, e, Finset.mem_filter] <;> tauto

    rw [h1]
    have h2 :
        2 ^ k_fiber ≤ P.fiberPointMultiplicity Y j_orig x ∧
          P.fiberPointMultiplicity Y j_orig x < 2 ^ (k_fiber + 1) := by
      have h3 := h_mult1 j_orig x h_x_in_Ωj
      rw [h_k_eq] at *
      exact h3
    have h_lower : mfiber ≤ P.fiberPointMultiplicity Y j_orig x := by
      dsimp only [mfiber]
      exact h2.1
    have h_upper : P.fiberPointMultiplicity Y j_orig x ≤ Mfiber := by
      dsimp only [Mfiber]
      omega
    exact ⟨h_lower, h_upper⟩

  have h_Z_subset : ∀ (j : Fin S_coarse.family.card),
      Z_final.carrier j ⊆ Z.carrier (S_coarse.embedding j) := by
    intro j
    dsimp only [Z_final]
    exact Set.inter_subset_left

  have h_compat_final : ∀ x ∈ Y_final.union,
      ∀ (i : Fin S_fine.family.card), x ∈ Y_final.carrier i →
        x ∈ Z_final.carrier (P'.parent i) := by
    intro x _ i hi
    have h_x_in_Y : x ∈ Y.carrier (S_fine.embedding i) := by
      dsimp only [Y_final, Y'] at hi
      exact Set.inter_subset_left (Set.inter_subset_left hi)
    have h_x_in_Ω : x ∈ Ω_coarse := by
      dsimp only [Y_final] at hi
      exact Set.inter_subset_right hi
    have h_in_Z : x ∈ Z.carrier (P.parent (S_fine.embedding i)) :=
      hcompat x (by exact ⟨S_fine.embedding i, h_x_in_Y⟩)
        (S_fine.embedding i) h_x_in_Y
    have h4 : S_coarse.embedding (P'.parent i) =
        P.parent (S_fine.embedding i) :=
      P.restrict_compatible S_fine S_coarse h_map h_surj i
    dsimp only [Z_final]
    rw [h4]
    exact ⟨h_in_Z, h_x_in_Ω⟩

  exact ⟨FR, mcoarse, Mcoarse, mfiber, Mfiber,
    h_retention, h_Z_subset, h_mcoarse_pos, h_Mcoarse_le, h_coarse_mult,
    h_mfiber_pos, h_Mfiber_le, h_fiber_mult, h_compat_final⟩

end Kakeya.Streamlined
