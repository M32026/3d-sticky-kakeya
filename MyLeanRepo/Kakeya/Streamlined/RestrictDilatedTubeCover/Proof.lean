import MyLeanRepo.Kakeya.Streamlined.RestrictDilatedTubeCover

/-!
# Restrict a dilated tube cover to a fine subfamily
-/

namespace Kakeya.Streamlined

theorem restrict_dilated_tube_cover_main :
    RestrictDilatedTubeCoverStatement := by
  intro δ ρ A fine coarse P S
  classical
  let eS : Fin S.family.card ↪ Fin fine.card := S.embedding
  let I_sel : Finset (Fin fine.card) := Finset.image eS Finset.univ
  let J_sel : Finset (Fin coarse.card) := Finset.image P.parent I_sel
  let C : TubeSubfamily coarse := TubeSubfamily.fromFinset coarse J_sel
  let eC : Fin C.family.card ↪ Fin coarse.card := C.embedding

  have h_image_es : Finset.image eS Finset.univ = I_sel := rfl
  have h_image_ec : Finset.image eC Finset.univ = J_sel :=
    Finset.image_orderEmbOfFin_univ J_sel rfl

  let idxInCoarse (j_orig : Fin coarse.card) (hj : j_orig ∈ J_sel) :
      Fin C.family.card :=
    have h_in_image : j_orig ∈ Finset.image eC Finset.univ := by
      rw [h_image_ec]; exact hj
    Classical.choose (Finset.mem_image.mp h_in_image)

  have h_idxInCoarse_spec : ∀ (j_orig : Fin coarse.card) (hj : j_orig ∈ J_sel),
      eC (idxInCoarse j_orig hj) = j_orig := by
    intro j_orig hj
    have h_in_image : j_orig ∈ Finset.image eC Finset.univ := by
      rw [h_image_ec]; exact hj
    exact (Classical.choose_spec (Finset.mem_image.mp h_in_image)).2

  let Q_parent (i : Fin S.family.card) : Fin C.family.card :=
    let j_orig := P.parent (eS i)
    have hj : j_orig ∈ J_sel := by
      apply Finset.mem_image.mpr
      exact ⟨eS i, Finset.mem_image_of_mem eS (Finset.mem_univ i), rfl⟩
    idxInCoarse j_orig hj

  have hQ_parent_spec : ∀ i, eC (Q_parent i) = P.parent (eS i) := by
    intro i
    exact h_idxInCoarse_spec (P.parent (eS i)) (by
      apply Finset.mem_image.mpr
      exact ⟨eS i, Finset.mem_image_of_mem eS (Finset.mem_univ i), rfl⟩)

  have hQ_parent_surj : Function.Surjective Q_parent := by
    intro j'
    let j_orig := eC j'
    have hj_orig : j_orig ∈ J_sel := Finset.orderEmbOfFin_mem J_sel rfl j'
    rcases Finset.mem_image.mp hj_orig with ⟨i_orig, hi_orig, hpar⟩
    have h_exists_i : ∃ (i : Fin S.family.card), eS i = i_orig := by
      have h_in_image : i_orig ∈ Finset.image eS Finset.univ := by
        rw [h_image_es]; exact hi_orig
      rcases Finset.mem_image.mp h_in_image with ⟨i, _, h_eq⟩
      exact ⟨i, h_eq⟩
    rcases h_exists_i with ⟨i, h_emb⟩
    have h4 : Q_parent i = j' := by
      have h5 : eC (Q_parent i) = P.parent (eS i) := hQ_parent_spec i
      have h6 : P.parent (eS i) = j_orig := by rw [h_emb]; exact hpar
      have h7 : eC (Q_parent i) = eC j' := by rw [h5, h6]
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
    have h3 : C.family.tube (Q_parent i) = coarse.tube (eC (Q_parent i)) :=
      C.tube_eq (Q_parent i)
    rw [h3]
    have h4 : eC (Q_parent i) = P.parent (eS i) := hQ_parent_spec i
    rw [h4] at *; exact h2

  let Q : DilatedTubeCover A S.family C.family :=
    { parent := Q_parent
      parent_surjective := hQ_parent_surj
      nested := hQ_nested }

  exact ⟨C, Q, fun i => hQ_parent_spec i⟩

end Kakeya.Streamlined
