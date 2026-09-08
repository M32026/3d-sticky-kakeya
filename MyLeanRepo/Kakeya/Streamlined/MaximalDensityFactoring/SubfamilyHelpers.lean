import MyLeanRepo.Kakeya.Streamlined.Basic

/-!
# Helpers for constructing subfamilies

Given a `BodyFamily F` and a `Finset I` of indices, construct the
`Subfamily F` consisting of exactly those bodies.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- Compose nested subfamilies while preserving the original ambient indices. -/
def Subfamily.comp {F : BodyFamily}
    (outer : Subfamily F)
    (inner : Subfamily outer.family) :
    Subfamily F where
  family := inner.family
  embedding := inner.embedding.trans outer.embedding
  carrier_eq i := by
    rw [inner.carrier_eq i, outer.carrier_eq (inner.embedding i)]
    rw [Function.Embedding.trans_apply]

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

/-- Mass of an arbitrary subfamily equals the sum over its image of indices. -/
lemma subfamily_mass_eq (F : BodyFamily) (S : Subfamily F) :
    S.family.mass = ∑ i ∈ Finset.image S.embedding Finset.univ, (F.body i).volume := by
  dsimp only [BodyFamily.mass]
  let e : (Fin S.family.card) ↪ (Fin F.card) := S.embedding
  have h_map : Finset.map e (Finset.univ : Finset (Fin S.family.card)) =
      Finset.image S.embedding Finset.univ := by
    rw [Finset.map_eq_image]
  have h1 : ∑ k : Fin S.family.card, (S.family.body k).volume =
      ∑ k : Fin S.family.card, (F.body (S.embedding k)).volume := by
    apply Finset.sum_congr rfl
    intro k _
    have h2 : (S.family.body k).carrier = (F.body (S.embedding k)).carrier := S.carrier_eq k
    simp [Body.volume, h2]
  rw [h1]
  have h2 : ∑ k : Fin S.family.card, (F.body (S.embedding k)).volume =
      ∑ i ∈ Finset.map e (Finset.univ : Finset (Fin S.family.card)), (F.body i).volume := by
    rw [Finset.sum_map]
    <;> rfl
  rw [h2, h_map]

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

/-- If the indices of `S` are a subset of `I`, then `S.family.containedMass K`
is at most that of the subfamily from `I`. -/
lemma containedMass_le_of_image_subset {F : BodyFamily} {S : Subfamily F}
    {I : Finset (Fin F.card)}
    (h : Finset.image S.embedding Finset.univ ⊆ I)
    (K : Set Point3) :
    S.family.containedMass K ≤ (subfamilyFromFinset F I).family.containedMass K := by
  classical
  let S2 := subfamilyFromFinset F I
  let e := S.embedding
  let e2 := S2.embedding
  let subIndices := S.family.containedIndices K
  let subIndices2 := S2.family.containedIndices K

  have h_image1 : Finset.image e subIndices =
      Finset.filter (fun idx : Fin F.card => (F.body idx).carrier ⊆ K)
        (Finset.image e Finset.univ) := by
    apply Finset.ext
    intro idx
    simp only [Finset.mem_image, subIndices, BodyFamily.containedIndices,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, h_i, h_eq⟩
      have h_car : (S.family.body i).carrier = (F.body (e i)).carrier := S.carrier_eq i
      have h_cont : (F.body (e i)).carrier ⊆ K := by
        rw [←h_car] <;> exact h_i
      have h_cont' : (F.body idx).carrier ⊆ K := by
        rw [←h_eq] <;> exact h_cont
      exact ⟨⟨i, h_eq⟩, h_cont'⟩
    · rintro ⟨h_exists, h_cont⟩
      rcases h_exists with ⟨i, h_eq⟩
      have h_car : (S.family.body i).carrier = (F.body (e i)).carrier := S.carrier_eq i
      have h_i : (S.family.body i).carrier ⊆ K := by
        rw [h_car, h_eq] <;> exact h_cont
      exact ⟨i, h_i, h_eq⟩

  have h_e2_univ : Finset.image e2 Finset.univ = I := by
    have h_map : Finset.map (I.orderEmbOfFin rfl).toEmbedding (Finset.univ : Finset (Fin I.card)) = I :=
      Finset.map_orderEmbOfFin_univ I (rfl : I.card = I.card)
    have h_eq : Finset.map (I.orderEmbOfFin rfl).toEmbedding (Finset.univ : Finset (Fin I.card)) =
        Finset.image e2 Finset.univ := by
      rw [Finset.map_eq_image]
      <;> rfl
    rw [h_eq] at h_map
    exact h_map

  have h_image2 : Finset.image e2 subIndices2 =
      Finset.filter (fun idx : Fin F.card => (F.body idx).carrier ⊆ K) I := by
    apply Finset.ext
    intro idx
    simp only [Finset.mem_image, subIndices2, BodyFamily.containedIndices,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, h_i, h_eq⟩
      have h_car : (S2.family.body i).carrier = (F.body (e2 i)).carrier := S2.carrier_eq i
      have h_cont : (F.body (e2 i)).carrier ⊆ K := by
        rw [←h_car] <;> exact h_i
      have h_in_I : e2 i ∈ I := by
        rw [←h_e2_univ] <;> exact Finset.mem_image_of_mem e2 (Finset.mem_univ i)
      exact ⟨by rw [h_eq] at * <;> exact h_in_I, by rw [h_eq] at * <;> exact h_cont⟩
    · rintro ⟨h_in_I, h_cont⟩
      have h_exists : ∃ (i : Fin I.card), e2 i = idx := by
        have h : idx ∈ Finset.image e2 Finset.univ := by
          rw [h_e2_univ] <;> exact h_in_I
        rcases Finset.mem_image.mp h with ⟨i, _, h_eq⟩
        exact ⟨i, h_eq⟩
      rcases h_exists with ⟨i, h_eq⟩
      have h_car : (S2.family.body i).carrier = (F.body (e2 i)).carrier := S2.carrier_eq i
      have h_i : (S2.family.body i).carrier ⊆ K := by
        rw [h_car, h_eq] <;> exact h_cont
      exact ⟨i, h_i, h_eq⟩

  have h_filter_subset :
      Finset.filter (fun idx : Fin F.card => (F.body idx).carrier ⊆ K)
        (Finset.image e Finset.univ) ⊆
      Finset.filter (fun idx : Fin F.card => (F.body idx).carrier ⊆ K) I := by
    apply Finset.filter_subset_filter
    exact h

  have h_eq1 : S.family.containedMass K =
      ∑ idx ∈ Finset.image e subIndices, (F.body idx).volume := by
    dsimp only [BodyFamily.containedMass]
    have h_body : ∀ i : Fin S.family.card, (S.family.body i).volume = (F.body (e i)).volume := by
      intro i
      have h_car : (S.family.body i).carrier = (F.body (S.embedding i)).carrier := S.carrier_eq i
      have h_eq : (F.body (S.embedding i)).carrier = (F.body (e i)).carrier := by rfl
      simp [Body.volume, h_car, h_eq]
    have h_sum1 : ∑ i ∈ subIndices, (S.family.body i).volume =
        ∑ i ∈ subIndices, (F.body (e i)).volume := by
      apply Finset.sum_congr rfl
      intro i _
      exact h_body i
    have h_sum2 : ∑ i ∈ subIndices, (F.body (e i)).volume =
        ∑ idx ∈ Finset.image e subIndices, (F.body idx).volume := by
      rw [Finset.sum_image] <;> intro i _ j _ hij <;> exact e.inj' hij
    rw [h_sum1, h_sum2]

  have h_eq2 : S2.family.containedMass K =
      ∑ idx ∈ Finset.image e2 subIndices2, (F.body idx).volume := by
    dsimp only [BodyFamily.containedMass]
    have h_body : ∀ i : Fin S2.family.card, (S2.family.body i).volume = (F.body (e2 i)).volume := by
      intro i
      have h_car : (S2.family.body i).carrier = (F.body (S2.embedding i)).carrier := S2.carrier_eq i
      have h_eq : (F.body (S2.embedding i)).carrier = (F.body (e2 i)).carrier := by rfl
      simp [Body.volume, h_car, h_eq]
    have h_sum1 : ∑ i ∈ subIndices2, (S2.family.body i).volume =
        ∑ i ∈ subIndices2, (F.body (e2 i)).volume := by
      apply Finset.sum_congr rfl
      intro i _
      exact h_body i
    have h_sum2 : ∑ i ∈ subIndices2, (F.body (e2 i)).volume =
        ∑ idx ∈ Finset.image e2 subIndices2, (F.body idx).volume := by
      rw [Finset.sum_image] <;> intro i _ j _ h2 <;> exact e2.inj' h2
    rw [h_sum1, h_sum2]

  rw [h_eq1, h_eq2, h_image1, h_image2]
  apply Finset.sum_le_sum_of_subset_of_nonneg h_filter_subset
  intro _ _ _
  simp

/-- If the indices of `S` are a subset of `I`, then `S.family.deltaMax`
is at most that of the subfamily from `I`. -/
lemma deltaMax_le_of_image_subset {F : BodyFamily} {S : Subfamily F}
    {I : Finset (Fin F.card)}
    (h : Finset.image S.embedding Finset.univ ⊆ I) :
    S.family.deltaMax ≤ (subfamilyFromFinset F I).family.deltaMax := by
  dsimp only [BodyFamily.deltaMax]
  apply csSup_le
    (by exact ⟨0, Set.univ, convex_univ, by simp [BodyFamily.density]⟩)
  intro d hd
  rcases hd with ⟨K, hK_conv, rfl⟩
  have h2 : S.family.containedMass K ≤ (subfamilyFromFinset F I).family.containedMass K :=
    containedMass_le_of_image_subset h K
  have h3 : S.family.density K ≤ (subfamilyFromFinset F I).family.density K := by
    dsimp only [BodyFamily.density]
    exact ENNReal.div_le_div h2 (le_refl _)
  have h4 : (subfamilyFromFinset F I).family.density K ≤
      (subfamilyFromFinset F I).family.deltaMax := by
    apply le_csSup (⟨⊤, fun x _ => le_top⟩)
    exact ⟨K, hK_conv, rfl⟩
  exact le_trans h3 h4

/-- The index image of `subfamilyFromFinset F I` is exactly `I`. -/
lemma subfamilyFromFinset_image_eq {F : BodyFamily} {I : Finset (Fin F.card)} :
    Finset.image (subfamilyFromFinset F I).embedding Finset.univ = I := by
  let e2 := (subfamilyFromFinset F I).embedding
  have h_map : Finset.map (I.orderEmbOfFin rfl).toEmbedding (Finset.univ : Finset (Fin I.card)) = I :=
    Finset.map_orderEmbOfFin_univ I rfl
  have h_eq : Finset.map (I.orderEmbOfFin rfl).toEmbedding (Finset.univ : Finset (Fin I.card)) =
      Finset.image e2 Finset.univ := by
    rw [Finset.map_eq_image] <;> rfl
  rw [h_eq] at h_map
  exact h_map

/-- If a subfamily has empty index image, its deltaMax is zero. -/
lemma subfamily_deltaMax_zero_of_image_empty {F : BodyFamily} {S : Subfamily F}
    (h : Finset.image S.embedding Finset.univ = (∅ : Finset (Fin F.card))) :
    S.family.deltaMax = 0 := by
  have h_card : S.family.card = 0 := by
    by_contra h2
    have h3 : 0 < S.family.card := Nat.pos_of_ne_zero h2
    let i : Fin S.family.card := ⟨0, h3⟩
    have h4 : S.embedding i ∈ Finset.image S.embedding Finset.univ :=
      Finset.mem_image_of_mem S.embedding (Finset.mem_univ i)
    rw [h] at h4
    simpa using h4
  have h1 : ∀ (K : Set Point3), S.family.containedMass K = 0 := by
    intro K
    dsimp only [BodyFamily.containedMass]
    have h2 : S.family.containedIndices K = ∅ := by
      haveI : IsEmpty (Fin S.family.card) := by rw [h_card] <;> infer_instance
      simp [BodyFamily.containedIndices]
    rw [h2] <;> simp
  have h3 : ∀ (K : Set Point3), S.family.density K = 0 := by
    intro K
    dsimp only [BodyFamily.density]
    rw [h1 K] <;> simp
  dsimp only [BodyFamily.deltaMax]
  have h4 : {d : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧ d = S.family.density K} = {0} := by
    ext d
    simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨K, hK, rfl⟩
      exact h3 K
    · intro h
      rw [h]
      exact ⟨Set.univ, convex_univ, (h3 Set.univ).symm⟩
  rw [h4] <;> simp

end Kakeya.Streamlined
