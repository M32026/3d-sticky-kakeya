import MyLeanRepo.Kakeya.Streamlined.DilatedCoverUniformization
import MyLeanRepo.Kakeya.Streamlined.OneScaleFiberUniformization

/-!
# One-scale uniformization of a dilated tube cover
-/

open MeasureTheory

namespace Kakeya.Streamlined

theorem assigned_dilated_cover_uniformization_main :
    AssignedDilatedCoverUniformizationStatement := by
  intro δ ρ A fine coarse P Y hY
  classical
  let I := Fin fine.card
  let w : I → ENNReal := fun i => volume (Y.carrier i)

  have h_card_pos : 0 < fine.card := by
    by_contra h
    have h' : fine.card = 0 := by omega
    have h_card0 : fine.toBodyFamily.card = 0 := by
      simpa [TubeFamily.toBodyFamily] using h'
    have h_isp : IsEmpty (Fin fine.toBodyFamily.card) := by
      rw [h_card0] <;> infer_instance
    letI : IsEmpty (Fin fine.toBodyFamily.card) := h_isp
    have hY0 : Y.mass = 0 := by
      dsimp only [Shading.mass] <;> simp
    exact hY.ne' hY0

  letI : Nonempty I := ⟨⟨0, h_card_pos⟩⟩
  have h_univ_nonempty : (Finset.univ : Finset I).Nonempty :=
    Finset.univ_nonempty

  rcases one_scale_on_finset (Finset.univ : Finset I) h_univ_nonempty P.parent w
    with ⟨I_sel, hI_subset, hI_union, hI_uniform, hI_mass⟩

  let S : TubeSubfamily fine := TubeSubfamily.fromFinset fine I_sel
  let eS : Fin S.family.card ↪ I := S.embedding

  have h_image_es : Finset.image eS Finset.univ = I_sel :=
    Finset.image_orderEmbOfFin_univ I_sel rfl

  have hS_mass : (S.restrictShading Y).mass = ∑ i ∈ I_sel, w i := by
    dsimp only [TubeSubfamily.restrictShading, Shading.mass]
    have h_sum : ∑ j ∈ Finset.image eS Finset.univ, volume (Y.carrier j) =
        ∑ i : Fin S.family.card, volume (Y.carrier (eS i)) :=
      Finset.sum_image (fun x _ y _ h => eS.inj' h)
    calc
      ∑ i : Fin S.family.card, volume (Y.carrier (eS i))
        = ∑ j ∈ Finset.image eS Finset.univ, volume (Y.carrier j) := h_sum.symm
      _ = ∑ j ∈ I_sel, volume (Y.carrier j) := by rw [h_image_es]

  have h_card_univ : (Finset.univ : Finset I).card = fine.card := by
    simp [I]

  have h_mass' : Y.mass ≤
      (Nat.log 2 fine.card + 1 : ENNReal) * (S.restrictShading Y).mass := by
    have h_Y : Y.mass = ∑ i ∈ (Finset.univ : Finset I), w i := by
      dsimp only [Shading.mass, w] <;> rfl
    rw [h_Y, hS_mass]
    have h1 : (∑ i ∈ I_sel, w i) * (Nat.log 2 fine.card + 1 : ENNReal) ≥
        ∑ i ∈ (Finset.univ : Finset I), w i := by
      rw [h_card_univ] at hI_mass
      exact hI_mass
    have h2 : (Nat.log 2 fine.card + 1 : ENNReal) * (∑ i ∈ I_sel, w i) ≥
        ∑ i ∈ (Finset.univ : Finset I), w i := by
      have h3 : (∑ i ∈ I_sel, w i) * (Nat.log 2 fine.card + 1 : ENNReal) =
          (Nat.log 2 fine.card + 1 : ENNReal) * (∑ i ∈ I_sel, w i) := by ring
      rw [h3] at h1
      exact h1
    exact h2

  have h_pos_mass : 0 < (S.restrictShading Y).mass := by
    by_contra h3
    have h4 : (S.restrictShading Y).mass = 0 := by simpa using h3
    rw [h4] at h_mass'
    have h5 : (Nat.log 2 fine.card + 1 : ENNReal) * 0 = 0 := by simp
    rw [h5] at h_mass'
    have h6 : Y.mass ≤ 0 := h_mass'
    have h7 : Y.mass = 0 := by simpa using h6
    exact hY.ne' h7

  have hI_nonempty : I_sel.Nonempty := by
    by_contra h
    have h' : I_sel = ∅ := by simpa using h
    rw [h'] at hS_mass
    have h_empty : (∑ i ∈ (∅ : Finset I), w i) = 0 := by simp
    rw [h_empty] at hS_mass
    rw [hS_mass] at h_pos_mass
    exact False.elim (lt_irrefl 0 h_pos_mass)

  have hS_nonempty : S.Nonempty := by
    have h_card_pos2 : 0 < I_sel.card := Finset.card_pos.mpr hI_nonempty
    dsimp only [TubeSubfamily.Nonempty, S, TubeSubfamily.fromFinset, TubeFamily.Nonempty]
    exact h_card_pos2

  let J_sel : Finset (Fin coarse.card) := Finset.image P.parent I_sel
  let C : TubeSubfamily coarse := TubeSubfamily.fromFinset coarse J_sel
  let eC : Fin C.family.card ↪ Fin coarse.card := C.embedding

  have h_image_ec : Finset.image eC Finset.univ = J_sel :=
    Finset.image_orderEmbOfFin_univ J_sel rfl

  let idxInCoarse (j_orig : Fin coarse.card) (hj : j_orig ∈ J_sel) :
      Fin C.family.card :=
    have h_in_image : j_orig ∈ Finset.image eC Finset.univ := by
      rw [h_image_ec] <;> exact hj
    Classical.choose (Finset.mem_image.mp h_in_image)

  have h_idxInCoarse_spec : ∀ (j_orig : Fin coarse.card) (hj : j_orig ∈ J_sel),
      eC (idxInCoarse j_orig hj) = j_orig := by
    intro j_orig hj
    have h_in_image : j_orig ∈ Finset.image eC Finset.univ := by
      rw [h_image_ec] <;> exact hj
    exact (Classical.choose_spec (Finset.mem_image.mp h_in_image)).2

  let Q_parent (i : Fin S.family.card) : Fin C.family.card :=
    let j_orig := P.parent (eS i)
    have hj : j_orig ∈ J_sel := by
      apply Finset.mem_image.mpr
      exact ⟨eS i, Finset.orderEmbOfFin_mem I_sel rfl i, rfl⟩
    idxInCoarse j_orig hj

  have hQ_parent_spec : ∀ i, eC (Q_parent i) = P.parent (eS i) := by
    intro i
    exact h_idxInCoarse_spec (P.parent (eS i)) (by
      apply Finset.mem_image.mpr
      exact ⟨eS i, Finset.orderEmbOfFin_mem I_sel rfl i, rfl⟩)

  have hQ_parent_surj : Function.Surjective Q_parent := by
    intro j'
    let j_orig := eC j'
    have hj_orig : j_orig ∈ J_sel := Finset.orderEmbOfFin_mem J_sel rfl j'
    rcases Finset.mem_image.mp hj_orig with ⟨i_orig, hi_orig, hpar⟩
    have h_exists_i : ∃ (i : Fin S.family.card), eS i = i_orig := by
      have h_in_image : i_orig ∈ Finset.image eS Finset.univ := by
        rw [h_image_es] <;> exact hi_orig
      rcases Finset.mem_image.mp h_in_image with ⟨i, _, h_eq⟩
      exact ⟨i, h_eq⟩
    rcases h_exists_i with ⟨i, h_emb⟩
    have h4 : Q_parent i = j' := by
      have h5 : eC (Q_parent i) = P.parent (eS i) := hQ_parent_spec i
      have h6 : P.parent (eS i) = j_orig := by rw [h_emb] <;> exact hpar
      have h7 : eC (Q_parent i) = eC j' := by rw [h5, h6] <;> rfl
      exact eC.injective h7
    exact ⟨i, h4⟩

  have hQ_nested : ∀ i, (S.family.tube i).carrier ⊆
      dilatedTubeCarrier A (C.family.tube (Q_parent i)) := by
    intro i
    have h1 : (S.family.tube i).carrier = (fine.tube (eS i)).carrier := by
      rw [S.tube_eq i]
    rw [h1]
    have h2 : (fine.tube (eS i)).carrier ⊆
        dilatedTubeCarrier A (coarse.tube (P.parent (eS i))) := P.nested (eS i)
    have h3 : C.family.tube (Q_parent i) = coarse.tube (eC (Q_parent i)) := by
      exact C.tube_eq (Q_parent i)
    rw [h3]
    have h4 : eC (Q_parent i) = P.parent (eS i) := hQ_parent_spec i
    rw [h4] at * <;> exact h2

  let Q : DilatedTubeCover A S.family C.family :=
    { parent := Q_parent
      parent_surjective := hQ_parent_surj
      nested := hQ_nested }

  have h_fiber_eq : ∀ (j' : Fin C.family.card),
      Q.toFactoring.fiberCount j' =
        ↑((I_sel.filter fun i => P.parent i = eC j').card) := by
    intro j'
    change
      ((Finset.univ.filter fun i : Fin S.family.card =>
        Q_parent i = j').card : ENNReal) =
        ((I_sel.filter fun i => P.parent i = eC j').card : ENNReal)
    let F_j := I_sel.filter fun i => P.parent i = eC j'
    have h_filter_eq :
        Finset.image eS (Finset.univ.filter fun i : Fin S.family.card => Q_parent i = j') = F_j := by
      ext x
      dsimp only [F_j]
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, h4, rfl⟩
        have h5 : P.parent (eS i) = eC j' := by
          have h6 : eC (Q_parent i) = P.parent (eS i) := hQ_parent_spec i
          have h7 : eC (Q_parent i) = eC j' := by rw [h4]
          rw [←h6, h7]
        have h_es_in : eS i ∈ I_sel := Finset.orderEmbOfFin_mem I_sel rfl i
        exact ⟨h_es_in, h5⟩
      · rintro ⟨hx, hpx⟩
        have h_in_image : x ∈ Finset.image eS Finset.univ := by
          rw [h_image_es] <;> exact hx
        rcases Finset.mem_image.mp h_in_image with ⟨i, _, h_eq⟩
        have h4 : Q_parent i = j' := by
          have h5 : eC (Q_parent i) = P.parent (eS i) := hQ_parent_spec i
          have h6 : P.parent (eS i) = eC j' := by rw [h_eq] <;> exact hpx
          have h7 : eC (Q_parent i) = eC j' := by rw [h5, h6]
          exact eC.injective h7
        exact ⟨i, h4, h_eq⟩
    have h_img_card : (Finset.image eS (Finset.univ.filter fun i => Q_parent i = j')).card = F_j.card := by
      rw [h_filter_eq]
    have h_filter_card : (Finset.image eS (Finset.univ.filter fun i => Q_parent i = j')).card =
        (Finset.univ.filter fun i => Q_parent i = j').card :=
      Finset.card_image_of_injective _ eS.inj'
    have h10 : (Finset.univ.filter fun i => Q_parent i = j').card = F_j.card := by
      rw [←h_filter_card, h_img_card]
    exact_mod_cast h10

  have h_uniform : Q.toFactoring.FibersAreCUniform 2 := by
    constructor
    · norm_num
    · intro j1' j2'
      let j1_orig := eC j1'
      let j2_orig := eC j2'

      have hj1 : j1_orig ∈ J_sel := Finset.orderEmbOfFin_mem J_sel rfl j1'
      have hj2 : j2_orig ∈ J_sel := Finset.orderEmbOfFin_mem J_sel rfl j2'

      let F1 := I_sel.filter fun i => P.parent i = j1_orig
      let F2 := I_sel.filter fun i => P.parent i = j2_orig

      have h_nonempty1 : 0 < F1.card := by
        rcases Finset.mem_image.mp hj1 with ⟨i, hi, hpar⟩
        have h_i_in_F1 : i ∈ F1 := by
          simp only [F1, Finset.mem_filter] <;> exact ⟨hi, hpar⟩
        exact Finset.card_pos.mpr ⟨i, h_i_in_F1⟩
      have h_nonempty2 : 0 < F2.card := by
        rcases Finset.mem_image.mp hj2 with ⟨i, hi, hpar⟩
        have h_i_in_F2 : i ∈ F2 := by
          simp only [F2, Finset.mem_filter] <;> exact ⟨hi, hpar⟩
        exact Finset.card_pos.mpr ⟨i, h_i_in_F2⟩

      have h_abs : (F1.card : ENNReal) ≤ 2 * (F2.card : ENNReal) :=
        hI_uniform j1_orig j2_orig h_nonempty1 h_nonempty2

      have h_fiber1 : Q.toFactoring.fiberCount j1' = ↑F1.card :=
        h_fiber_eq j1'
      have h_fiber2 : Q.toFactoring.fiberCount j2' = ↑F2.card :=
        h_fiber_eq j2'

      rw [h_fiber1, h_fiber2]
      exact h_abs

  exact ⟨S, hS_nonempty, h_mass', C, Q, h_uniform⟩

/-- Legacy compatibility theorem for internal assigned-cell consumers. -/
theorem legacy_dilated_cover_uniformization_main :
    LegacyDilatedCoverUniformizationStatement :=
  assigned_dilated_cover_uniformization_main

end Kakeya.Streamlined
