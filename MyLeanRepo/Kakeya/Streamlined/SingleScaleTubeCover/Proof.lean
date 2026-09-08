import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.SingleScaleCover
import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.SingleScaleCoverConstruction
import MyLeanRepo.Kakeya.Streamlined.CloseDistinctTubeCover
import MyLeanRepo.Kakeya.Streamlined.CombinatorialLemmas.EssentiallyDistinctSubfamily
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.SelfDilatedContainment
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.NonDistinctDilatedContainment
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.MidpointBound

/-!
Paper reference: GWZ Section 2, Items (i) and (ii) in the definition of a
uniform set of tubes, at one fixed scale, with the paper's absolute-constant
tube-enlargement convention made explicit.

## Proof outline

1. Use `construct_coarse_cover` to obtain an exact phase-space-grid cover of
   the fine family by a candidate coarse family.
2. Select a maximal essentially-distinct subfamily of the candidate coarse
   family using `exists_maximal_essentially_distinct_subfamily`.
3. Reassign every deleted candidate's fine fiber to a retained conflicting
   candidate.
4. If two candidate tubes are not essentially distinct, one carrier is
   contained in a universal homothetic dilation of the other.
5. Self-containment handles the case where the old and new coarse indices
   coincide.
-/

noncomputable section

namespace Kakeya.Streamlined

theorem close_distinct_tube_cover_main :
    CloseDistinctTubeCoverStatement := by
  use 2002
  constructor
  · norm_num
  intro δ ρ hδ hδρ hρ1 F hF_nonempty hF_ball hF_ed

  -- Full-tube shading for the construction
  let Y : TubeShading F :=
    { carrier := fun i => (F.tube i).carrier
      measurable_carrier := fun _ => Metric.isClosed_cthickening.measurableSet
      subset_body := fun _ => Set.Subset.rfl }

  -- Step 1: exact coarse cover from phase-space gridding
  rcases construct_coarse_cover hδ hδρ hρ1 F hF_ball Y with
    ⟨coarse, cover, _weight, _hweight, hmid_close, hdir_close⟩

  -- Step 2: maximal essentially-distinct subfamily
  rcases exists_maximal_essentially_distinct_subfamily coarse with
    ⟨I, hI_ed, hI_maximal⟩

  classical

  -- Step 3: conflict map — every coarse index maps to a member of I
  let f : Fin coarse.card → Fin coarse.card := fun j =>
    if hj : j ∈ I then j
    else Classical.choose (hI_maximal j hj)

  have h_f_in_I : ∀ j, f j ∈ I := by
    intro j
    by_cases hj : j ∈ I
    · simp [f, hj]
    · have h_spec := Classical.choose_spec (hI_maximal j hj)
      simp [f, hj]; exact h_spec.1

  have h_f_conflict : ∀ j, j ∉ I →
      ¬(coarse.tube j).EssentiallyDistinct (coarse.tube (f j)) := by
    intro j hj
    have h_spec := Classical.choose_spec (hI_maximal j hj)
    have h_f_eq : f j = Classical.choose (hI_maximal j hj) := by
      simp [f, hj]
    rw [h_f_eq]
    exact h_spec.2

  have h_f_id : ∀ j ∈ I, f j = j := by
    intro j hj
    simp [f, hj]

  let S : TubeSubfamily coarse := TubeSubfamily.fromFinset coarse I

  have h_image : Finset.map S.embedding Finset.univ = I :=
    Finset.map_orderEmbOfFin_univ I rfl

  have h_exists_preimage : ∀ (j : Fin coarse.card), j ∈ I →
      ∃ (k : Fin S.family.card), S.embedding k = j := by
    intro j hj
    have h_j_in_map : j ∈ Finset.map S.embedding Finset.univ := by
      rw [h_image]; exact hj
    rcases Finset.mem_map.mp h_j_in_map with ⟨k, _, hk⟩
    exact ⟨k, hk⟩

  let toSubfamily (j : Fin coarse.card) (hj : j ∈ I) : Fin S.family.card :=
    Classical.choose (h_exists_preimage j hj)

  have h_embedding_toSubfamily : ∀ (j : Fin coarse.card) (hj : j ∈ I),
      S.embedding (toSubfamily j hj) = j := by
    intro j hj
    exact Classical.choose_spec (h_exists_preimage j hj)

  -- New parent map: fine → subfamily
  let new_parent : Fin F.card → Fin S.family.card := fun i =>
    toSubfamily (f (cover.parent i)) (h_f_in_I (cover.parent i))

  have h_new_parent_spec : ∀ i,
      S.embedding (new_parent i) = f (cover.parent i) := by
    intro i
    exact h_embedding_toSubfamily (f (cover.parent i)) (h_f_in_I (cover.parent i))

  have hρ : 0 < ρ := lt_of_lt_of_le hδ hδρ

  -- Key geometric leaf with midpoint bounds
  let h_coarse_mid_bound : ∀ (j : Fin coarse.card),
      ‖GeometricLemmas.tubeMidpoint (coarse.tube j)‖ ≤ 3 :=
    GeometricLemmas.coarse_tube_midpoint_bound cover hF_ball hρ.le hρ1

  have h_geo_leaf : ∀ (j1 j2 : Fin coarse.card),
      ¬(coarse.tube j1).EssentiallyDistinct (coarse.tube j2) →
      ‖(GeometricLemmas.tubeMidpoint (coarse.tube j1) -
          GeometricLemmas.tubeMidpoint (coarse.tube j2)) -
        inner ℝ
          (GeometricLemmas.tubeMidpoint (coarse.tube j1) -
            GeometricLemmas.tubeMidpoint (coarse.tube j2))
          (coarse.tube j2).direction • (coarse.tube j2).direction‖ ≤
          1000 * ρ ∧
      (‖(coarse.tube j1).direction - (coarse.tube j2).direction‖ ≤
          1000 * ρ ∨
        ‖(coarse.tube j1).direction + (coarse.tube j2).direction‖ ≤
          1000 * ρ) ∧
      (coarse.tube j1).carrier ⊆
        dilatedTubeCarrier 1000 (coarse.tube j2) := by
    intro j1 j2 h_conflict
    let h_m1 := h_coarse_mid_bound j1
    let h_m2 := h_coarse_mid_bound j2
    exact GeometricLemmas.non_distinct_local_geometry
      hρ hρ1 (coarse.tube j1) (coarse.tube j2)
      h_m1 h_m2 h_conflict

  -- Step 4: nested containment
  have h_nested : ∀ i, (F.tube i).carrier ⊆
      dilatedTubeCarrier 1000 (S.family.tube (new_parent i)) := by
    intro i
    let old_j := cover.parent i
    let new_j := f old_j
    have h1 : (F.tube i).carrier ⊆ (coarse.tube old_j).carrier :=
      cover.nested i
    have h2 : (coarse.tube old_j).carrier ⊆
        dilatedTubeCarrier 1000 (coarse.tube new_j) := by
      by_cases h : old_j ∈ I
      · have h_eq : new_j = old_j := by
          simp [new_j, h_f_id old_j h]
        rw [h_eq]
        exact GeometricLemmas.self_dilated_containment 1000 (by norm_num) (coarse.tube old_j)
      · have h_conflict : ¬(coarse.tube old_j).EssentiallyDistinct (coarse.tube new_j) :=
          h_f_conflict old_j h
        exact (h_geo_leaf old_j new_j h_conflict).2.2
    have h3 : S.family.tube (new_parent i) = coarse.tube new_j := by
      have h4 : S.family.tube (new_parent i) = coarse.tube (S.embedding (new_parent i)) :=
        S.tube_eq (new_parent i)
      rw [h4, h_new_parent_spec]
    rw [h3]
    exact Set.Subset.trans h1 h2

  -- Step 5: surjectivity
  have h_surj : Function.Surjective new_parent := by
    intro k
    let j : Fin coarse.card := S.embedding k
    have hj : j ∈ I := Finset.orderEmbOfFin_mem I rfl k
    have h_f_j : f j = j := h_f_id j hj
    rcases cover.parent_surjective j with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have h5 : S.embedding (new_parent i) = f (cover.parent i) := h_new_parent_spec i
    rw [hi, h_f_j] at h5
    exact S.embedding.inj' h5

  let dilated_cover : DilatedTubeCover 1000 F S.family :=
    { parent := new_parent
      parent_surjective := h_surj
      nested := h_nested }

  have h_transverse : ∀ i,
      ‖(GeometricLemmas.tubeMidpoint (F.tube i) -
          GeometricLemmas.tubeMidpoint (S.family.tube (new_parent i))) -
        inner ℝ
          (GeometricLemmas.tubeMidpoint (F.tube i) -
            GeometricLemmas.tubeMidpoint (S.family.tube (new_parent i)))
          (S.family.tube (new_parent i)).direction •
            (S.family.tube (new_parent i)).direction‖ ≤ 2002 * ρ := by
    intro i
    let old_j := cover.parent i
    let new_j := f old_j
    rw [S.tube_eq (new_parent i), h_new_parent_spec]
    by_cases h : old_j ∈ I
    · have h_eq : new_j = old_j := h_f_id old_j h
      change ‖(GeometricLemmas.tubeMidpoint (F.tube i) -
          GeometricLemmas.tubeMidpoint (coarse.tube new_j)) -
        inner ℝ
          (GeometricLemmas.tubeMidpoint (F.tube i) -
            GeometricLemmas.tubeMidpoint (coarse.tube new_j))
          (coarse.tube new_j).direction •
            (coarse.tube new_j).direction‖ ≤ 2002 * ρ
      rw [h_eq]
      exact (GeometricLemmas.norm_transverse_le
        (coarse.tube old_j).direction_unit
        (GeometricLemmas.tubeMidpoint (F.tube i) -
          GeometricLemmas.tubeMidpoint (coarse.tube old_j))).trans (by
            nlinarith [hmid_close i])
    · have hlocal := h_geo_leaf old_j new_j (h_f_conflict old_j h)
      let trans := fun v : Point3 =>
        v - inner ℝ v (coarse.tube new_j).direction •
          (coarse.tube new_j).direction
      have hsum :
          trans (GeometricLemmas.tubeMidpoint (F.tube i) -
            GeometricLemmas.tubeMidpoint (coarse.tube new_j)) =
            trans (GeometricLemmas.tubeMidpoint (F.tube i) -
              GeometricLemmas.tubeMidpoint (coarse.tube old_j)) +
            trans (GeometricLemmas.tubeMidpoint (coarse.tube old_j) -
              GeometricLemmas.tubeMidpoint (coarse.tube new_j)) := by
        dsimp only [trans]
        simp only [inner_sub_left]
        module
      change ‖trans (GeometricLemmas.tubeMidpoint (F.tube i) -
        GeometricLemmas.tubeMidpoint (coarse.tube new_j))‖ ≤ _
      rw [hsum]
      calc
        ‖trans _ + trans _‖ ≤ ‖trans _‖ + ‖trans _‖ := norm_add_le _ _
        _ ≤ ‖GeometricLemmas.tubeMidpoint (F.tube i) -
              GeometricLemmas.tubeMidpoint (coarse.tube old_j)‖ +
            1000 * ρ := by
          apply add_le_add
          · exact GeometricLemmas.norm_transverse_le
              (coarse.tube new_j).direction_unit _
          · change
              ‖(GeometricLemmas.tubeMidpoint (coarse.tube old_j) -
                  GeometricLemmas.tubeMidpoint (coarse.tube new_j)) -
                inner ℝ
                  (GeometricLemmas.tubeMidpoint (coarse.tube old_j) -
                    GeometricLemmas.tubeMidpoint (coarse.tube new_j))
                  (coarse.tube new_j).direction •
                    (coarse.tube new_j).direction‖ ≤ 1000 * ρ
            exact hlocal.1
        _ ≤ 2002 * ρ := by nlinarith [hmid_close i]

  have h_direction : ∀ i,
      ‖(F.tube i).direction -
          (S.family.tube (new_parent i)).direction‖ ≤ 2002 * ρ ∨
        ‖(F.tube i).direction +
          (S.family.tube (new_parent i)).direction‖ ≤ 2002 * ρ := by
    intro i
    let old_j := cover.parent i
    let new_j := f old_j
    rw [S.tube_eq (new_parent i), h_new_parent_spec]
    by_cases h : old_j ∈ I
    · left
      rw [h_f_id old_j h]
      exact (hdir_close i).trans (by nlinarith)
    · rcases (h_geo_leaf old_j new_j (h_f_conflict old_j h)).2.1 with
        hsame | hopposite
      · left
        calc
          ‖(F.tube i).direction - (coarse.tube new_j).direction‖
              ≤ ‖(F.tube i).direction - (coarse.tube old_j).direction‖ +
                ‖(coarse.tube old_j).direction -
                  (coarse.tube new_j).direction‖ := by
            have htri := norm_add_le
              ((F.tube i).direction - (coarse.tube old_j).direction)
              ((coarse.tube old_j).direction -
                (coarse.tube new_j).direction)
            simpa only [sub_add_sub_cancel] using htri
          _ ≤ 2002 * ρ := by nlinarith [hdir_close i, hsame]
      · right
        have heq :
            (F.tube i).direction + (coarse.tube new_j).direction =
              ((F.tube i).direction - (coarse.tube old_j).direction) +
                ((coarse.tube old_j).direction +
                  (coarse.tube new_j).direction) := by
          module
        rw [heq]
        calc
          ‖((F.tube i).direction - (coarse.tube old_j).direction) +
              ((coarse.tube old_j).direction +
                (coarse.tube new_j).direction)‖
              ≤ ‖(F.tube i).direction - (coarse.tube old_j).direction‖ +
                ‖(coarse.tube old_j).direction +
                  (coarse.tube new_j).direction‖ := norm_add_le _ _
          _ ≤ 2002 * ρ := by nlinarith [hdir_close i, hopposite]

  let local_cover : LocalDilatedTubeCover 1000 2002 F S.family :=
    { toDilatedTubeCover := dilated_cover
      transverse_midpoint_close := h_transverse
      direction_close_or_reverse := h_direction }

  -- Step 6: the retained coarse family is essentially distinct
  have h_S_ed : S.family.IsEssentiallyDistinct := by
    intro i j hne
    let i' := S.embedding i
    let j' := S.embedding j
    have hi' : i' ∈ I := Finset.orderEmbOfFin_mem I rfl i
    have hj' : j' ∈ I := Finset.orderEmbOfFin_mem I rfl j
    have h_ne' : i' ≠ j' := by
      intro h; have : i = j := S.embedding.inj' h; exact hne this
    exact hI_ed i' hi' j' hj' h_ne'

  exact ⟨S.family, local_cover, h_S_ed⟩

/-- Compatibility export of the older dilated-cover statement. -/
theorem single_scale_tube_cover_main :
    SingleScaleTubeCoverStatement := by
  rcases close_distinct_tube_cover_main with ⟨C, _hC, hmain⟩
  refine ⟨1000, by norm_num, ?_⟩
  intro δ ρ hδ hδρ hρ1 F hF_nonempty hF_ball hF_ed
  rcases hmain δ ρ hδ hδρ hρ1 F hF_nonempty hF_ball hF_ed with
    ⟨coarse, localCover, hcoarse⟩
  exact ⟨coarse, localCover.toDilatedTubeCover, hcoarse⟩

end Kakeya.Streamlined
