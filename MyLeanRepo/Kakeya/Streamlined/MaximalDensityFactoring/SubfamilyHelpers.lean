import MyLeanRepo.Kakeya.Streamlined.Basic

/-!
# Helpers for constructing subfamilies

Given a `BodyFamily F` and a `Finset I` of indices, construct the
`Subfamily F` consisting of exactly those bodies.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- Build a `Subfamily F` from a `Finset` of indices. -/
def subfamilyFromFinset (F : BodyFamily) (I : Finset (Fin F.card)) : Subfamily F :=
  { family :=
    { card := I.card
      body := fun i => F.body (I.orderEmbOfFin rfl i) }
    embedding :=
      { toFun := fun i => I.orderEmbOfFin rfl i
        inj' := I.orderEmbOfFin rfl |>.injective }
    carrier_eq := fun _ => rfl }

@[simp]
lemma subfamilyFromFinset_card (F : BodyFamily) (I : Finset (Fin F.card)) :
    (subfamilyFromFinset F I).family.card = I.card := by
  rfl

lemma subfamilyFromFinset_embedding_mem (F : BodyFamily) (I : Finset (Fin F.card))
    (i : Fin I.card) :
    (subfamilyFromFinset F I).embedding i ∈ I :=
  Finset.orderEmbOfFin_mem I rfl i

lemma subfamilyFromFinset_body (F : BodyFamily) (I : Finset (Fin F.card))
    (i : Fin I.card) :
    (subfamilyFromFinset F I).family.body i = F.body ((subfamilyFromFinset F I).embedding i) := by
  rfl

/-- The mass of the subfamily equals the sum of volumes over the index set. -/
lemma subfamilyFromFinset_mass (F : BodyFamily) (I : Finset (Fin F.card)) :
    (subfamilyFromFinset F I).family.mass = ∑ i ∈ I, (F.body i).volume := by
  dsimp only [BodyFamily.mass, subfamilyFromFinset]
  let e : (Fin I.card) ↪ (Fin F.card) := (I.orderEmbOfFin rfl).toEmbedding
  have h_map : Finset.map e (Finset.univ : Finset (Fin I.card)) = I :=
    Finset.map_orderEmbOfFin_univ I (rfl)
  have h_main : ∑ i : Fin I.card, (F.body (e i)).volume = ∑ j ∈ I, (F.body j).volume := by
    calc
      ∑ i : Fin I.card, (F.body (e i)).volume
        = ∑ j ∈ Finset.map e (Finset.univ : Finset (Fin I.card)), (F.body j).volume := by
          rw [Finset.sum_map] <;> rfl
      _ = ∑ j ∈ I, (F.body j).volume := by rw [h_map]
  exact h_main

/-- Compatibility name used by the greedy decomposition modules. -/
abbrev subfamilyOfFinset (F : BodyFamily) (I : Finset (Fin F.card)) :
    Subfamily F :=
  subfamilyFromFinset F I

/-- Sum over a selected subfamily, under the greedy-module name. -/
lemma sum_subfamily_eq (F : BodyFamily) (I : Finset (Fin F.card)) :
    (subfamilyOfFinset F I).family.mass = ∑ i ∈ I, (F.body i).volume :=
  subfamilyFromFinset_mass F I

/-- Cross-multiply an inequality between two finite positive ENNReal ratios. -/
lemma ennreal_div_le_div_to_mul (a b c d : ENNReal)
    (hb_pos : b ≠ 0) (hb_top : b ≠ ⊤)
    (hd_pos : d ≠ 0) (hd_top : d ≠ ⊤)
    (h : a / b ≤ c / d) : a * d ≤ c * b := by
  have h1 : a ≤ b * (c / d) := (ENNReal.div_le_iff' hb_pos hb_top).mp h
  have h2 : a * d ≤ (b * (c / d)) * d := by gcongr
  have h3 : (b * (c / d)) * d = b * c := by
    simp only [div_eq_mul_inv]
    calc
      (b * (c * d⁻¹)) * d = b * ((c * d⁻¹) * d) := by rw [mul_assoc]
      _ = b * (c * (d⁻¹ * d)) := by rw [mul_assoc]
      _ = b * (c * 1) := by rw [ENNReal.inv_mul_cancel hd_pos hd_top]
      _ = b * c := by simp
  rw [h3, mul_comm b c] at h2
  exact h2

/-- The contained mass of a subfamily is at most that of the original. -/
lemma subfamily_containedMass_le {F : BodyFamily}
    (S : Subfamily F) (K : Set Point3) :
    S.family.containedMass K ≤ F.containedMass K := by
  classical
  let e := S.embedding
  let subIndices := S.family.containedIndices K
  have h_maps : ∀ i ∈ subIndices, e i ∈ F.containedIndices K := by
    intro i hi
    have h4 : (S.family.body i).carrier ⊆ K := by
      simpa [BodyFamily.containedIndices, Finset.mem_filter] using
        (Finset.mem_filter.mp hi).2
    have h5 : (F.body (e i)).carrier ⊆ K := by
      rw [← S.carrier_eq i]
      exact h4
    simpa [BodyFamily.containedIndices, Finset.mem_filter] using h5
  have h_image_subset :
      Finset.image e subIndices ⊆ F.containedIndices K := by
    rw [Finset.image_subset_iff]
    exact h_maps
  have h_eq1 :
      ∑ i ∈ subIndices, (S.family.body i).volume =
        ∑ i ∈ subIndices, (F.body (e i)).volume := by
    apply Finset.sum_congr rfl
    intro i _
    change MeasureTheory.volume (S.family.body i).carrier =
      MeasureTheory.volume (F.body (S.embedding i)).carrier
    rw [S.carrier_eq i]
  have h_eq2 :
      ∑ i ∈ subIndices, (F.body (e i)).volume =
        ∑ j ∈ Finset.image e subIndices, (F.body j).volume := by
    simpa [Finset.map_eq_image] using
      (Finset.sum_map (s := subIndices) (f := fun j => (F.body j).volume)
        (g := fun i => (F.body (e i)).volume) e rfl)
  calc
    S.family.containedMass K
        = ∑ i ∈ subIndices, (S.family.body i).volume := by rfl
    _ = ∑ i ∈ subIndices, (F.body (e i)).volume := h_eq1
    _ = ∑ j ∈ Finset.image e subIndices, (F.body j).volume := h_eq2
    _ ≤ ∑ j ∈ F.containedIndices K, (F.body j).volume := by
      apply Finset.sum_le_sum_of_subset_of_nonneg h_image_subset
      intro _ _ _
      simp
    _ = F.containedMass K := by rfl

/-- The maximal density of a subfamily is at most that of the original. -/
lemma subfamily_deltaMax_le {F : BodyFamily} (S : Subfamily F) :
    S.family.deltaMax ≤ F.deltaMax := by
  dsimp only [BodyFamily.deltaMax]
  apply csSup_le
    (by exact ⟨0, Set.univ, convex_univ, by simp [BodyFamily.density]⟩)
  intro d hd
  rcases hd with ⟨K, hK_conv, rfl⟩
  have h2 : S.family.containedMass K ≤ F.containedMass K :=
    subfamily_containedMass_le S K
  have h3 : S.family.density K ≤ F.density K := by
    dsimp only [BodyFamily.density]
    exact ENNReal.div_le_div h2 (le_refl _)
  have h4 : F.density K ≤ F.deltaMax := by
    apply le_csSup (⟨⊤, fun x _ => le_top⟩)
    exact ⟨K, hK_conv, rfl⟩
  exact le_trans h3 h4

end Kakeya.Streamlined
