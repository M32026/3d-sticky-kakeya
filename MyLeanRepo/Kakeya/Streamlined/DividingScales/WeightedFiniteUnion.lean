import MyLeanRepo.Kakeya.Streamlined.DividingScales.ParentEnvelopeCounting

/-!
# Weighted finite-union bound for contained mass

If an index set `I` is covered by `I_k` for `k ∈ S`, and each tube in `I_k`
is contained in a convex set `C_k`, then the contained mass in a convex test
set `K` is bounded by the sum of `deltaMax(I_k) * vol(K ∩ C_k)`.

This factors further as `(sup_k deltaMax(I_k)) * ∑_k vol(K ∩ C_k)`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

attribute [local instance] Classical.propDecidable

/-- Contained mass of a finset of tube indices in a set `W`. -/
def finsetContainedMass
    {δ : ℝ} {G : TubeFamily δ}
    (I : Finset (Fin G.card)) (W : Set Point3) : ENNReal :=
  ∑ j ∈ Finset.filter (fun j => (G.tube j).carrier ⊆ W) I,
    (G.tube j).volume

/-- The contained mass of a fromFinset subfamily equals the finset sum. -/
lemma subfamily_containedMass_eq
    {δ : ℝ} {G : TubeFamily δ}
    (I : Finset (Fin G.card)) (W : Set Point3) :
    (TubeSubfamily.fromFinset G I).family.toBodyFamily.containedMass W =
      finsetContainedMass I W := by
  classical
  let S := TubeSubfamily.fromFinset G I
  let B := S.family.toBodyFamily
  let e := S.embedding
  let P : Fin G.card → Prop := fun j => (G.tube j).carrier ⊆ W
  let Q : Fin S.family.card → Prop := fun i => P (e i)
  have h_image_univ : Finset.image e Finset.univ = I :=
    Finset.image_orderEmbOfFin_univ I rfl
  have h_image_filter :
      Finset.image e (Finset.univ.filter Q) = Finset.filter P I := by
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hiQ, rfl⟩
      have hI : e i ∈ I := by
        rw [← h_image_univ]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      exact ⟨hI, hiQ⟩
    · rintro ⟨hjI, hjP⟩
      have h_in_image : j ∈ Finset.image e Finset.univ := by
        rw [h_image_univ]
        exact hjI
      rcases Finset.mem_image.mp h_in_image with ⟨i, _, h_eq⟩
      have hQ : Q i := by
        simpa [Q, h_eq] using hjP
      exact ⟨i, hQ, h_eq⟩
  have h_indices : B.containedIndices W = Finset.univ.filter Q := by
    ext i
    have h_mem : i ∈ B.containedIndices W ↔ (B.body i).carrier ⊆ W :=
      BodyFamily.mem_containedIndices_iff
    have h_carrier : (B.body i).carrier = (G.tube (e i)).carrier :=
      S.toBodySubfamily.carrier_eq i
    rw [h_mem, h_carrier]
    simp [Q, Finset.mem_filter] <;> tauto
  have h_body_volume :
      ∀ i : Fin B.card, (B.body i).volume = (G.tube (e i)).volume := by
    intro i
    have h : (B.body i).carrier = (G.tube (e i)).carrier :=
      S.toBodySubfamily.carrier_eq i
    exact congr_arg volume h
  have h1 :
      B.containedMass W =
        ∑ i ∈ Finset.univ.filter Q, (B.body i).volume := by
    have h_def :
        B.containedMass W =
          ∑ i ∈ B.containedIndices W, (B.body i).volume := by
      rfl
    rw [h_def]
    exact congr_arg
      (fun s : Finset (Fin B.card) => ∑ i ∈ s, (B.body i).volume)
      h_indices
  have h2 :
      (∑ i ∈ Finset.univ.filter Q, (B.body i).volume) =
        ∑ i ∈ Finset.univ.filter Q, (G.tube (e i)).volume := by
    apply Finset.sum_congr rfl
    intro i _
    exact h_body_volume i
  have h3 :
      (∑ i ∈ Finset.univ.filter Q, (G.tube (e i)).volume) =
        ∑ j ∈ Finset.image e (Finset.univ.filter Q), (G.tube j).volume := by
    rw [Finset.sum_image]
    exact fun x _ y _ h => e.injective h
  rw [h1, h2, h3, h_image_filter]
  rfl

/--
If all tubes in `I` are contained in `C`, then the contained mass in `K`
equals the contained mass in `K ∩ C`.
-/
lemma containedMass_inter_eq
    {δ : ℝ} {G : TubeFamily δ}
    (I : Finset (Fin G.card))
    {K C : Set Point3}
    (hcontain : ∀ j ∈ I, (G.tube j).carrier ⊆ C) :
    finsetContainedMass I K = finsetContainedMass I (K ∩ C) := by
  classical
  have hfilter :
      Finset.filter (fun j : Fin G.card => (G.tube j).carrier ⊆ K) I =
        Finset.filter
          (fun j : Fin G.card => (G.tube j).carrier ⊆ K ∩ C) I := by
    ext j
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hjI, hK⟩
      exact ⟨hjI, fun x hx => ⟨hK hx, hcontain j hjI hx⟩⟩
    · rintro ⟨hjI, hKC⟩
      exact ⟨hjI, fun x hx => (hKC hx).1⟩
  rw [finsetContainedMass, finsetContainedMass, hfilter]

/--
Contained mass of a finset subfamily bounded by deltaMax times volume.
The zero-volume case is handled internally.
-/
lemma finsetContainedMass_le_deltaMax_mul_volume
    {δ : ℝ} {G : TubeFamily δ}
    (I : Finset (Fin G.card))
    {W : Set Point3} (hW : Convex ℝ W)
    (hW_top : volume W ≠ ⊤) :
    finsetContainedMass I W ≤
      (TubeSubfamily.fromFinset G I).family.toBodyFamily.deltaMax * volume W := by
  classical
  by_cases hW_zero : volume W = 0
  · have h_mass_zero : finsetContainedMass I W = 0 := by
      dsimp only [finsetContainedMass]
      apply Finset.sum_eq_zero
      intro j hj
      have hcarrier : (G.tube j).carrier ⊆ W :=
        (Finset.mem_filter.mp hj).2
      have hvol : (G.tube j).volume ≤ volume W := volume.mono hcarrier
      rw [hW_zero] at hvol
      simpa using hvol
    rw [h_mass_zero, hW_zero, mul_zero]
  · have h_eq :
        (TubeSubfamily.fromFinset G I).family.toBodyFamily.containedMass W =
          finsetContainedMass I W :=
      subfamily_containedMass_eq I W
    have h := BodyFamily.containedMass_le_deltaMax_mul_volume
      (TubeSubfamily.fromFinset G I).family.toBodyFamily hW hW_zero hW_top
    rw [h_eq] at h
    exact h

private lemma sum_biUnion_le
    {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (f : β → ENNReal) :
    ∑ x ∈ Finset.biUnion s t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
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
            (∑ x ∈ u ∪ v, f x) + (∑ x ∈ u ∩ v, f x) =
              (∑ x ∈ u, f x) + (∑ x ∈ v, f x) :=
          Finset.fold_union_inter
            (op := (· + ·)) (f := f) (b₁ := 0) (b₂ := 0)
        have h_le :
            ∑ x ∈ u ∪ v, f x ≤
              (∑ x ∈ u ∪ v, f x) + ∑ x ∈ u ∩ v, f x :=
          le_add_of_nonneg_right (by positivity)
        rw [h_eq] at h_le
        exact h_le
      exact h_union.trans (add_le_add (le_refl _) ih)

/-- If `I` is covered by a finite union of index sets, its contained mass is
at most the sum of their contained masses.  Overlap among the covering sets is
allowed. -/
lemma finsetContainedMass_le_sum_of_subset_biUnion
    {δ : ℝ} {G : TubeFamily δ}
    {α : Type*} [DecidableEq α]
    (S : Finset α)
    (I : Finset (Fin G.card))
    (I_h : α → Finset (Fin G.card))
    (hcover : I ⊆ Finset.biUnion S I_h)
    (K : Set Point3) :
    finsetContainedMass I K ≤
      ∑ h ∈ S, finsetContainedMass (I_h h) K := by
  classical
  let contained := fun J : Finset (Fin G.card) =>
    J.filter fun index => (G.tube index).carrier ⊆ K
  have hfiltered :
      contained I ⊆
        Finset.biUnion S fun h => contained (I_h h) := by
    intro index hindex
    have hdata := Finset.mem_filter.mp hindex
    rcases Finset.mem_biUnion.mp (hcover hdata.1) with
      ⟨h, hh, hindexPiece⟩
    exact Finset.mem_biUnion.mpr
      ⟨h, hh, Finset.mem_filter.mpr ⟨hindexPiece, hdata.2⟩⟩
  calc
    finsetContainedMass I K =
        ∑ index ∈ contained I, (G.tube index).volume := by rfl
    _ ≤ ∑ index ∈ Finset.biUnion S (fun h => contained (I_h h)),
          (G.tube index).volume :=
      Finset.sum_le_sum_of_subset_of_nonneg hfiltered
        (fun _ _ _ => by positivity)
    _ ≤ ∑ h ∈ S, ∑ index ∈ contained (I_h h),
          (G.tube index).volume :=
      sum_biUnion_le S (fun h => contained (I_h h))
        (fun index => (G.tube index).volume)
    _ = ∑ h ∈ S, finsetContainedMass (I_h h) K := by rfl

/--
If `I` is covered by `I_k` and every tube in `I_k` lies in a convex
container `C_k`, bound its contained mass by the weighted container
intersection volumes.
-/
lemma containedMass_weighted_finset_union
    {δ : ℝ} {G : TubeFamily δ}
    {α : Type*} [DecidableEq α]
    (S : Finset α)
    (I : Finset (Fin G.card))
    (I_k : α → Finset (Fin G.card))
    (C_k : α → Set Point3)
    (hcover : I ⊆ Finset.biUnion S I_k)
    (hC : ∀ k ∈ S, Convex ℝ (C_k k))
    (hcontain : ∀ k ∈ S, ∀ j ∈ I_k k, (G.tube j).carrier ⊆ C_k k)
    {K : Set Point3} (hK : Convex ℝ K)
    (hvol_top : ∀ k ∈ S, volume (K ∩ C_k k) ≠ ⊤) :
    finsetContainedMass I K ≤
      ∑ k ∈ S,
        (TubeSubfamily.fromFinset G (I_k k)).family.toBodyFamily.deltaMax *
          volume (K ∩ C_k k) := by
  classical
  let P := fun j : Fin G.card => (G.tube j).carrier ⊆ K
  have h_filter_cover :
      Finset.filter P I ⊆
        Finset.biUnion S (fun k => Finset.filter P (I_k k)) := by
    intro j hj
    have hjI : j ∈ I := (Finset.mem_filter.mp hj).1
    have hjP : P j := (Finset.mem_filter.mp hj).2
    rcases Finset.mem_biUnion.mp (hcover hjI) with ⟨k, hk, hjk⟩
    exact Finset.mem_biUnion.mpr
      ⟨k, hk, Finset.mem_filter.mpr ⟨hjk, hjP⟩⟩
  have h_mass :
      finsetContainedMass I K ≤
        ∑ k ∈ S, finsetContainedMass (I_k k) K := by
    rw [finsetContainedMass]
    have h_subset :
        ∑ j ∈ Finset.filter P I, (G.tube j).volume ≤
          ∑ j ∈ Finset.biUnion S (fun k => Finset.filter P (I_k k)),
            (G.tube j).volume :=
      Finset.sum_le_sum_of_subset_of_nonneg h_filter_cover
        (fun _ _ _ => by positivity)
    have h_union :
        ∑ j ∈ Finset.biUnion S (fun k => Finset.filter P (I_k k)),
            (G.tube j).volume ≤
          ∑ k ∈ S, ∑ j ∈ Finset.filter P (I_k k), (G.tube j).volume :=
      sum_biUnion_le S (fun k => Finset.filter P (I_k k))
        (fun j => (G.tube j).volume)
    exact h_subset.trans h_union
  have h_each :
      ∀ k ∈ S,
        finsetContainedMass (I_k k) K ≤
          (TubeSubfamily.fromFinset G (I_k k)).family.toBodyFamily.deltaMax *
            volume (K ∩ C_k k) := by
    intro k hk
    have h_inter_eq :
        finsetContainedMass (I_k k) K =
          finsetContainedMass (I_k k) (K ∩ C_k k) :=
      containedMass_inter_eq (I_k k)
        (fun j hj => hcontain k hk j hj)
    rw [h_inter_eq]
    have h_inter_conv : Convex ℝ (K ∩ C_k k) := hK.inter (hC k hk)
    exact finsetContainedMass_le_deltaMax_mul_volume
      (I_k k) h_inter_conv (hvol_top k hk)
  calc
    finsetContainedMass I K
        ≤ ∑ k ∈ S, finsetContainedMass (I_k k) K := h_mass
    _ ≤ ∑ k ∈ S,
          (TubeSubfamily.fromFinset G (I_k k)).family.toBodyFamily.deltaMax *
            volume (K ∩ C_k k) := by
      apply Finset.sum_le_sum
      intro k hk
      exact h_each k hk

/--
Weighted finite-union bound with the maximal piece `deltaMax` factored out.
-/
lemma containedMass_weighted_finset_union_sup
    {δ : ℝ} {G : TubeFamily δ}
    {α : Type*} [DecidableEq α]
    (S : Finset α)
    (hS : S.Nonempty)
    (I : Finset (Fin G.card))
    (I_k : α → Finset (Fin G.card))
    (C_k : α → Set Point3)
    (hcover : I ⊆ Finset.biUnion S I_k)
    (hC : ∀ k ∈ S, Convex ℝ (C_k k))
    (hcontain : ∀ k ∈ S, ∀ j ∈ I_k k, (G.tube j).carrier ⊆ C_k k)
    {K : Set Point3} (hK : Convex ℝ K)
    (hvol_top : ∀ k ∈ S, volume (K ∩ C_k k) ≠ ⊤) :
    finsetContainedMass I K ≤
      (S.sup' hS (fun k =>
          (TubeSubfamily.fromFinset G (I_k k)).family.toBodyFamily.deltaMax)) *
        ∑ k ∈ S, volume (K ∩ C_k k) := by
  let D := S.sup' hS (fun k =>
    (TubeSubfamily.fromFinset G (I_k k)).family.toBodyFamily.deltaMax)
  have h_each :
      ∀ k ∈ S,
        (TubeSubfamily.fromFinset G (I_k k)).family.toBodyFamily.deltaMax ≤ D :=
    fun k hk => Finset.le_sup'
      (fun k' =>
        (TubeSubfamily.fromFinset G (I_k k')).family.toBodyFamily.deltaMax)
      hk
  have h_main := containedMass_weighted_finset_union
    S I I_k C_k hcover hC hcontain hK hvol_top
  calc
    finsetContainedMass I K
        ≤ ∑ k ∈ S,
          (TubeSubfamily.fromFinset G (I_k k)).family.toBodyFamily.deltaMax *
            volume (K ∩ C_k k) := h_main
    _ ≤ ∑ k ∈ S, D * volume (K ∩ C_k k) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_left (h_each k hk) _
    _ = D * ∑ k ∈ S, volume (K ∩ C_k k) := by
      rw [Finset.mul_sum]

end Kakeya.Streamlined
