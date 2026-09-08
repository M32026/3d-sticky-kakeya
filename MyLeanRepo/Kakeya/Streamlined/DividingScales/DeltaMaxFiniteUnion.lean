import MyLeanRepo.Kakeya.Streamlined.Estimates
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement

/-!
# Finite-union bounds for `deltaMax`

If an index set is covered by finitely many index sets, the `deltaMax` of
the corresponding tube subfamily is at most the sum of the `deltaMax` values
of the covering subfamilies.  Overlaps among the covering sets are allowed.
-/

noncomputable section

namespace Kakeya.Streamlined

attribute [local instance] Classical.propDecidable

/-- Sum over an injective image may be reindexed by the source. -/
private lemma sum_image_eq
    {α β γ : Type*} [DecidableEq β] [AddCommMonoid γ]
    (e : α ↪ β) (s : Finset α) (f : β → γ) :
    ∑ i ∈ s, f (e i) = ∑ j ∈ Finset.image e s, f j := by
  have h_inj : Set.InjOn e (s : Set α) :=
    fun _ _ _ _ h => e.inj' h
  exact (Finset.sum_image h_inj).symm

/--
The contained mass of a `fromFinset` tube subfamily is the sum of the
ambient tube volumes over the selected indices whose carriers lie in `K`.
-/
private lemma tubeSubfamily_fromFinset_containedMass_eq
    {δ : ℝ} {G : TubeFamily δ}
    {I : Finset (Fin G.card)} {K : Set Point3} :
    (TubeSubfamily.fromFinset G I).family.toBodyFamily.containedMass K =
      ∑ j ∈ Finset.filter
          (fun j : Fin G.card => (G.tube j).carrier ⊆ K) I,
        (G.tube j).volume := by
  classical
  let S := TubeSubfamily.fromFinset G I
  let e := S.embedding
  let B := S.family.toBodyFamily
  let P : Fin G.card → Prop :=
    fun j => (G.tube j).carrier ⊆ K
  let Q : Fin S.family.card → Prop :=
    fun i => P (e i)
  have h_image_subset : Finset.image e Finset.univ ⊆ I := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    exact Finset.orderEmbOfFin_mem I rfl i
  have h_image_card :
      (Finset.image e Finset.univ).card = I.card := by
    have h_inj : Function.Injective e := e.inj'
    have h :
        (Finset.image e Finset.univ).card =
          (Finset.univ : Finset (Fin S.family.card)).card :=
      Finset.card_image_of_injective Finset.univ h_inj
    rw [h]
    have h_univ :
        (Finset.univ : Finset (Fin S.family.card)).card =
          S.family.card := by
      simp
    rw [h_univ]
    dsimp only [S, TubeSubfamily.fromFinset]
  have h_image_univ : Finset.image e Finset.univ = I :=
    Finset.eq_of_subset_of_card_le h_image_subset
      (by rw [h_image_card])
  have h_image_filter :
      Finset.image e (Finset.univ.filter Q) =
        Finset.filter P I := by
    ext j
    simp only [Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hiQ, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem I rfl i, hiQ⟩
    · rintro ⟨hjI, hjP⟩
      have h_in_image : j ∈ Finset.image e Finset.univ := by
        rw [h_image_univ]
        exact hjI
      rcases Finset.mem_image.mp h_in_image with
        ⟨i, _, h_eq⟩
      have hQ : Q i := by
        dsimp only [Q]
        rw [h_eq]
        exact hjP
      exact ⟨i, hQ, h_eq⟩
  have h_indices :
      B.containedIndices K = Finset.univ.filter Q := by
    ext i
    have h_carrier :
        (B.body i).carrier = (G.tube (e i)).carrier :=
      S.toBodySubfamily.carrier_eq i
    have h_mem :
        i ∈ B.containedIndices K ↔
          (B.body i).carrier ⊆ K :=
      BodyFamily.mem_containedIndices_iff
    have h_carrier_iff :
        (B.body i).carrier ⊆ K ↔
          (G.tube (e i)).carrier ⊆ K := by
      constructor
      · intro h
        rwa [← h_carrier]
      · intro h
        rwa [h_carrier]
    have h_Q :
        (G.tube (e i)).carrier ⊆ K ↔ Q i := by
      rfl
    have h_filter :
        i ∈ (Finset.univ.filter Q) ↔ Q i := by
      constructor
      · intro h
        exact (Finset.mem_filter.mp h).2
      · intro h
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ i, h⟩
    exact h_mem.trans
      (h_carrier_iff.trans (h_Q.trans h_filter.symm))
  have h_body_volume :
      ∀ i : Fin B.card,
        (B.body i).volume = (G.tube (e i)).volume := by
    intro i
    have h_carrier :
        (B.body i).carrier = (G.tube (e i)).carrier :=
      S.toBodySubfamily.carrier_eq i
    exact congr_arg MeasureTheory.volume h_carrier
  calc
    B.containedMass K
        = ∑ i ∈ B.containedIndices K,
            (B.body i).volume := by
          rfl
    _ = ∑ i ∈ Finset.univ.filter Q,
          (B.body i).volume := by
          exact congr_arg
            (fun s => ∑ i ∈ s, (B.body i).volume)
            h_indices
    _ = ∑ i ∈ Finset.univ.filter Q,
          (G.tube (e i)).volume := by
          exact Finset.sum_congr rfl
            (fun i _ => h_body_volume i)
    _ = ∑ j ∈ Finset.image e
          (Finset.univ.filter Q),
          (G.tube j).volume := by
          exact sum_image_eq e
            (Finset.univ.filter Q)
            (fun j => (G.tube j).volume)
    _ = ∑ j ∈ Finset.filter P I,
          (G.tube j).volume := by
          rw [h_image_filter]

/-- A sum over a finite union is at most the corresponding double sum. -/
private lemma sum_biUnion_le_sum
    {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : α → Finset β)
    (f : β → ENNReal) :
    ∑ x ∈ Finset.biUnion s t, f x ≤
      ∑ i ∈ s, ∑ x ∈ t i, f x := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      set u := t a
      set v := Finset.biUnion s t
      have h_union :
          ∑ x ∈ u ∪ v, f x ≤
            (∑ x ∈ u, f x) + ∑ x ∈ v, f x := by
        have h_eq :
            (∑ x ∈ u ∪ v, f x) +
                (∑ x ∈ u ∩ v, f x) =
              (∑ x ∈ u, f x) +
                (∑ x ∈ v, f x) :=
          Finset.fold_union_inter
            (op := (· + ·)) (f := f)
            (b₁ := 0) (b₂ := 0)
        have h_le :
            ∑ x ∈ u ∪ v, f x ≤
              (∑ x ∈ u ∪ v, f x) +
                ∑ x ∈ u ∩ v, f x :=
          le_add_of_nonneg_right (by positivity)
        rw [h_eq] at h_le
        exact h_le
      exact h_union.trans
        (add_le_add (le_refl (∑ x ∈ u, f x)) ih)

/--
If `I` is covered by the finite union of the `I_k`, then the `deltaMax` of
the subfamily indexed by `I` is at most the sum of the covering `deltaMax`
values.
-/
lemma deltaMax_finset_union_bound
    {δ : ℝ} {G : TubeFamily δ}
    {α : Type*} [DecidableEq α]
    (S : Finset α)
    (I : Finset (Fin G.card))
    (I_k : α → Finset (Fin G.card))
    (hcover : I ⊆ Finset.biUnion S I_k) :
    (TubeSubfamily.fromFinset G I).family.toBodyFamily.deltaMax ≤
      ∑ k ∈ S,
        (TubeSubfamily.fromFinset G
          (I_k k)).family.toBodyFamily.deltaMax := by
  classical
  let B_I :=
    (TubeSubfamily.fromFinset G I).family.toBodyFamily
  let B_k := fun k =>
    (TubeSubfamily.fromFinset G
      (I_k k)).family.toBodyFamily
  have h_main :
      ∀ J : Set Point3, Convex ℝ J →
        B_I.density J ≤
          ∑ k ∈ S, (B_k k).deltaMax := by
    intro J hJ
    let P := fun j : Fin G.card =>
      (G.tube j).carrier ⊆ J
    have h_filter_cover :
        Finset.filter P I ⊆
          Finset.biUnion S
            (fun k => Finset.filter P (I_k k)) := by
      intro j hj
      have hjI : j ∈ I := (Finset.mem_filter.mp hj).1
      have hjP : P j := (Finset.mem_filter.mp hj).2
      have h_union : j ∈ Finset.biUnion S I_k :=
        hcover hjI
      rcases Finset.mem_biUnion.mp h_union with
        ⟨k, hk, hjk⟩
      exact Finset.mem_biUnion.mpr
        ⟨k, hk, Finset.mem_filter.mpr ⟨hjk, hjP⟩⟩
    have h_mass :
        B_I.containedMass J ≤
          ∑ k ∈ S, (B_k k).containedMass J := by
      rw [tubeSubfamily_fromFinset_containedMass_eq]
      let f := fun j : Fin G.card =>
        (G.tube j).volume
      let J_k := fun k : α =>
        Finset.filter P (I_k k)
      have h_subset :
          ∑ j ∈ Finset.filter P I, f j ≤
            ∑ j ∈ Finset.biUnion S J_k, f j :=
        Finset.sum_le_sum_of_subset_of_nonneg
          h_filter_cover
          (fun _ _ _ => by positivity)
      have h_union :
          ∑ j ∈ Finset.biUnion S J_k, f j ≤
            ∑ k ∈ S, ∑ j ∈ J_k k, f j :=
        sum_biUnion_le_sum S J_k f
      have h_rewrite :
          ∑ k ∈ S, ∑ j ∈ J_k k, f j =
            ∑ k ∈ S, (B_k k).containedMass J := by
        apply Finset.sum_congr rfl
        intro k _
        exact
          tubeSubfamily_fromFinset_containedMass_eq
            (G := G) (I := I_k k) (K := J) |>.symm
      exact h_subset.trans
        (h_union.trans (le_of_eq h_rewrite))
    calc
      B_I.density J
          = B_I.containedMass J /
              MeasureTheory.volume J := by
            rfl
      _ ≤ (∑ k ∈ S, (B_k k).containedMass J) /
            MeasureTheory.volume J := by
            gcongr
      _ = ∑ k ∈ S,
            ((B_k k).containedMass J /
              MeasureTheory.volume J) := by
            simpa [div_eq_mul_inv, Finset.sum_mul]
              using rfl
      _ = ∑ k ∈ S, (B_k k).density J := by
            rfl
      _ ≤ ∑ k ∈ S, (B_k k).deltaMax := by
            apply Finset.sum_le_sum
            intro k _
            exact le_csSup
              (⟨⊤, fun _ _ => le_top⟩)
              ⟨J, hJ, rfl⟩
  dsimp only [BodyFamily.deltaMax]
  apply csSup_le
    (by
      exact ⟨0, Set.univ, convex_univ,
        by simp [BodyFamily.density]⟩)
  intro d hd
  rcases hd with ⟨J, hJ, rfl⟩
  exact h_main J hJ

end Kakeya.Streamlined
