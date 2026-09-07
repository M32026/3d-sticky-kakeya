module

/-
# Double Counting Helper for Phase 0

For fixed y, |X_y| * (1/2) C^{-1} δ^{-s} ≤ 7 * |T|.

Uses:
- covering_lower_bound for each Pz z
- Inline overlap bound ≤ 7 (from Phase0CompositionV2)
- Standard double counting via Finset
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.ProductLikeProof
public import MyLeanRepo.ProductLikeIncidence.Phase0.OverlapBound
public import MyLeanRepo.ProductLikeIncidence.CoveringLowerBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open ENNReal Set Bornology Classical Finset

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- Double counting bound: |X_y| * (1/2) C^{-1} δ^{-s} ≤ 7 * |T|. -/
lemma double_count_per_y
    {δ s C : ℝ} {Y : Set ℝ} {X : ℝ → Set ℝ}
    {Pz : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 2))}
    {y : ℝ} (hy : y ∈ Y) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hδ_pos : 0 < δ) (hC_pos : 0 < C)
    (hX_grid : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ)
    (hXy_delta : ∀ y ∈ Y, X y ⊆ productLikeUnitGrid δ ∧
      IsProductLikeRealDeltaSCSet δ s C (X y))
    (hPz_delta : ∀ z ∈ productLikeIncidenceSet Y X, IsDeltaSCSet (d := 2) δ s C (Pz z))
    (hPz_approx : ∀ z ∈ productLikeIncidenceSet Y X,
      ∀ p ∈ Pz z, |p 0 * (z 1) + p 1 - z 0| ≤ 2 * δ)
    (hPz_bounded : ∀ z ∈ productLikeIncidenceSet Y X, Bornology.IsBounded (Pz z))
    (hT : Set (Set (EuclideanSpace ℝ (Fin 2))))
    (hT_finite : hT.Finite)
    (hU_sub : (⋃ x ∈ X y, dyadicCubesMeeting δ (Pz (mkPoint2 x y))) ⊆ hT) :
    ((X y).encard : ENNReal) * ENNReal.ofReal ((1/2:ℝ) * C⁻¹ * δ ^ (-s)) ≤
      ENNReal.ofReal (7 : ℝ) * ENat.toENNReal hT.encard := by
  let Xy_fin : (X y).Finite :=
    Set.Finite.subset (productLikeUnitGrid_finite hδ_pos) (hXy_delta y hy).1
  let X_finset : Finset ℝ := Xy_fin.toFinset
  have hX_coe : (X_finset : Set ℝ) = X y := by simp [X_finset]

  let Cz : ℝ → Set (Set (EuclideanSpace ℝ (Fin 2))) := fun x =>
    dyadicCubesMeeting δ (Pz (mkPoint2 x y))

  have hCz_fin : ∀ x ∈ X y, (Cz x).Finite := by
    intro x hx
    let z := mkPoint2 x y
    have hz : z ∈ productLikeIncidenceSet Y X := by
      simp only [productLikeIncidenceSet, Set.mem_iUnion]
      refine ⟨y, hy, ?_⟩
      simp only [Set.mem_setOf_eq, mkPoint2_fst, mkPoint2_snd]
      exact ⟨hx, rfl⟩
    exact dyadicCubesMeeting_finite hδ_pos (hPz_bounded z hz)

  let Cz_finset (x : ℝ) : Finset (Set (EuclideanSpace ℝ (Fin 2))) :=
    if h : x ∈ X y then (hCz_fin x h).toFinset else ∅

  have hCz_finset_coe : ∀ (x : ℝ) (hx : x ∈ X y),
      (Cz_finset x : Set _) = Cz x := by
    intro x hx
    simp [Cz_finset, hx]
    <;> rfl

  let I_inc : Finset (ℝ × Set (EuclideanSpace ℝ (Fin 2))) :=
    X_finset.biUnion (fun x => ({x} : Finset ℝ) ×ˢ Cz_finset x)

  have hI_card : (I_inc.card : ENNReal) = ∑ x ∈ X_finset, (Cz_finset x).card := by
    rw [Finset.card_biUnion]
    · simp [I_inc, Finset.card_product, Finset.card_singleton, Finset.sum_const]
      <;> ring
    · intro a _ b _ hab
      apply Finset.disjoint_left.mpr
      intro p hp1 hp2
      have h1 : p.1 ∈ ({a} : Finset ℝ) := (Finset.mem_product.mp hp1).1
      have h1' : p.1 = a := by simpa using h1
      have h2 : p.1 ∈ ({b} : Finset ℝ) := (Finset.mem_product.mp hp2).1
      have h2' : p.1 = b := by simpa using h2
      rw [h1'] at h2'; exact hab h2'

  -- Lower bound: each Cz x has covering number ≥ C^{-1} δ^{-s}
  have h_lower_each : ∀ x ∈ X_finset,
      ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤ (Cz_finset x).card := by
    intro x hx
    have hx' : x ∈ X y := by rw [← hX_coe] <;> exact Finset.mem_coe.mp hx
    let z := mkPoint2 x y
    have hz : z ∈ productLikeIncidenceSet Y X := by
      simp only [productLikeIncidenceSet, Set.mem_iUnion]
      refine ⟨y, hy, ?_⟩
      simp only [Set.mem_setOf_eq, mkPoint2_fst, mkPoint2_snd]
      exact ⟨hx', rfl⟩
    have hPz : IsDeltaSCSet (d := 2) δ s C (Pz z) := hPz_delta z hz
    have h1 : ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤
        ENat.toENNReal (dyadicCoveringNumber δ (Pz z)) := covering_lower_bound hPz
    have h2 : (Cz_finset x : Set _) = Cz x := hCz_finset_coe x hx'
    have h3 : (Cz x).encard = ↑(Cz_finset x).card := by
      have h4 : (Cz_finset x : Set _) = Cz x := h2
      have h5 : (Cz x).encard = ↑(Cz_finset x).card := by
        rw [← h4]
        simp
      exact h5
    have h6 : ENat.toENNReal (dyadicCoveringNumber δ (Pz z)) = (Cz_finset x).card := by
      dsimp only [dyadicCoveringNumber]
      rw [h3]
      <;> simp
    rw [h6] at h1
    exact h1

  have hI_lower : (X_finset.card : ENNReal) * ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤
      (I_inc.card : ENNReal) := by
    rw [hI_card]
    have h_sum_cast : (∑ x ∈ X_finset, (Cz_finset x).card : ENNReal) =
        ∑ x ∈ X_finset, (Cz_finset x).card := by
      rw [Nat.cast_sum]
    have h_sum : ∑ x ∈ X_finset, ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤
        (∑ x ∈ X_finset, (Cz_finset x).card : ENNReal) :=
      Finset.sum_le_sum (fun i hi => h_lower_each i hi)
    rw [Finset.sum_const] at h_sum
    rw [h_sum_cast] at h_sum
    simpa [mul_comm] using h_sum

  -- Upper bound: overlap ≤ 7 (inline proof from Phase0CompositionV2)
  let U_set : Set (Set (EuclideanSpace ℝ (Fin 2))) :=
    ⋃ x ∈ X y, Cz x
  have hU_fin : U_set.Finite := by
    apply Set.Finite.biUnion Xy_fin
    intro x hx
    exact hCz_fin x hx
  let U_finset : Finset (Set (EuclideanSpace ℝ (Fin 2))) := hU_fin.toFinset
  have hU_coe : (U_finset : Set _) = U_set := by simp [U_finset]

  have h_overlap : ∀ Q ∈ U_set,
      ({x ∈ X y | Q ∈ Cz x}.Finite ∧ {x ∈ X y | Q ∈ Cz x}.encard ≤ 7) := by
    intro Q hQ
    rcases Set.mem_iUnion₂.mp hQ with ⟨x0, hx0, hQx⟩
    have hQ_dyadic : Q ∈ dyadicCubes 2 δ := hQx.1
    let S : Set ℝ := {x ∈ X y | Q ∈ Cz x}
    have hS_sub1 : S ⊆ productLikeIntegerGrid δ := by
      intro x hx
      have h_in_unit : x ∈ productLikeUnitGrid δ := (hXy_delta y hy).1 hx.1
      exact h_in_unit.1
    rcases hQ_dyadic with ⟨k, hQ_eq⟩
    let a : ℝ := δ * (k 0 : ℝ)
    let b : ℝ := δ * (k 1 : ℝ)
    have h_p_bounds : ∀ p ∈ Q,
        a ≤ p 0 ∧ p 0 < a + δ ∧ b ≤ p 1 ∧ p 1 < b + δ := by
      intro p hp
      have h_eq1 : a + δ = δ * ((k 0 : ℝ) + 1) := by dsimp only [a]; ring
      have h_eq2 : b + δ = δ * ((k 1 : ℝ) + 1) := by dsimp only [b]; ring
      have h : p ∈ dyadicCube δ k := by rw [hQ_eq] at hp; exact hp
      exact ⟨(h 0).1, by rw [h_eq1]; exact (h 0).2, (h 1).1, by rw [h_eq2]; exact (h 1).2⟩
    let raw_lo : ℝ := a * y + b
    let raw_hi : ℝ := (a + δ) * y + (b + δ)
    let lo : ℝ := raw_lo - 2 * δ
    let hi : ℝ := raw_hi + 2 * δ
    have h_len : hi - lo ≤ 6 * δ := by
      dsimp only [lo, hi, raw_lo, raw_hi]
      nlinarith [hy1]
    have hS_sub2 : S ⊆ Set.Icc lo hi := by
      intro x hx
      have hQ_in : Q ∈ dyadicCubesMeeting δ (Pz (mkPoint2 x y)) := hx.2
      have hQ_meet : (Q ∩ Pz (mkPoint2 x y)).Nonempty := hQ_in.2
      rcases hQ_meet with ⟨p, hpQ, hpPz⟩
      let z := mkPoint2 x y
      have hz : z ∈ productLikeIncidenceSet Y X := by
        simp only [productLikeIncidenceSet, Set.mem_iUnion]
        refine ⟨y, hy, ?_⟩
        simp only [Set.mem_setOf_eq, mkPoint2_fst, mkPoint2_snd]
        exact ⟨hx.1, rfl⟩
      have h_ineq : |p 0 * y + p 1 - x| ≤ 2 * δ := hPz_approx z hz p hpPz
      have hpb := h_p_bounds p hpQ
      have h5 : raw_lo ≤ p 0 * y + p 1 := by
        dsimp only [raw_lo]; nlinarith [hy0, hpb.1, hpb.2.2.1]
      have h6 : p 0 * y + p 1 ≤ raw_hi := by
        dsimp only [raw_hi]; nlinarith [hy0, hy1, hpb.2.1, hpb.2.2.2]
      have h7 : |x - (p 0 * y + p 1)| ≤ 2 * δ := by
        have h : x - (p 0 * y + p 1) = -(p 0 * y + p 1 - x) := by ring
        rw [h, abs_neg]; exact h_ineq
      have h8 : p 0 * y + p 1 - 2 * δ ≤ x := by linarith [abs_le.mp h7]
      have h9 : x ≤ p 0 * y + p 1 + 2 * δ := by linarith [abs_le.mp h7]
      have h10 : lo ≤ x := by dsimp only [lo]; linarith
      have h11 : x ≤ hi := by dsimp only [hi]; linarith
      exact ⟨h10, h11⟩
    exact grid_points_in_six_delta_interval hδ_pos hS_sub1 hS_sub2 h_len

  have hI_upper : (I_inc.card : ENNReal) ≤
      ENNReal.ofReal (7 : ℝ) * (U_finset.card : ENNReal) := by
    have h_disj : ∀ Q1 ∈ U_finset, ∀ Q2 ∈ U_finset, Q1 ≠ Q2 →
        Disjoint (I_inc.filter (fun p => p.2 = Q1))
          (I_inc.filter (fun p => p.2 = Q2)) := by
      intro Q1 _ Q2 _ hne
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have h1 : p.2 = Q1 := (Finset.mem_filter.mp hp1).2
      have h2 : p.2 = Q2 := (Finset.mem_filter.mp hp2).2
      rw [h1] at h2; exact hne h2
    have h_union : I_inc = U_finset.biUnion (fun Q => I_inc.filter (fun p => p.2 = Q)) := by
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro hp
        have hQ_in_U_set : p.2 ∈ U_set := by
          rcases Finset.mem_biUnion.mp hp with ⟨x, hx, hprod⟩
          have hQ_in_Cz : p.2 ∈ Cz_finset x := (Finset.mem_product.mp hprod).2
          have hx' : x ∈ X y := by rw [← hX_coe] <;> exact Finset.mem_coe.mp hx
          have hQ_in_set : p.2 ∈ Cz x := by
            rw [← hCz_finset_coe x hx'] <;> exact hQ_in_Cz
          exact Set.mem_iUnion₂.mpr ⟨x, hx', hQ_in_set⟩
        have hQ : p.2 ∈ U_finset := by
          have hQ' : p.2 ∈ (U_finset : Set _) := by
            rw [hU_coe] <;> exact hQ_in_U_set
          exact Finset.mem_coe.mp hQ'
        exact ⟨p.2, hQ, hp, rfl⟩
      · rintro ⟨Q, hQ, hp, _⟩
        exact hp
    have h_sum_card : I_inc.card = ∑ Q ∈ U_finset, (I_inc.filter (fun p => p.2 = Q)).card := by
      have h_card : (U_finset.biUnion (fun Q => I_inc.filter (fun p => p.2 = Q))).card =
          ∑ Q ∈ U_finset, (I_inc.filter (fun p => p.2 = Q)).card :=
        Finset.card_biUnion h_disj
      exact (congr_arg Finset.card h_union).trans h_card
    have h_sum : (I_inc.card : ENNReal) =
        ∑ Q ∈ U_finset, ((I_inc.filter (fun p => p.2 = Q)).card : ENNReal) := by
      rw [h_sum_card, Nat.cast_sum]
    rw [h_sum]
    have h_each : ∀ Q ∈ U_finset,
        ((I_inc.filter (fun p => p.2 = Q)).card : ENNReal) ≤ ENNReal.ofReal (7 : ℝ) := by
      intro Q hQ
      have hQ_in_U : Q ∈ U_set := by
        have h : Q ∈ (U_finset : Set _) := Finset.mem_coe.mpr hQ
        rw [hU_coe] at h
        exact h
      let S : Set ℝ := {x ∈ X y | Q ∈ Cz x}
      have hS_fin : S.Finite := (h_overlap Q hQ_in_U).1
      let S' : Finset ℝ := hS_fin.toFinset
      have hS_encard : S.encard ≤ 7 := (h_overlap Q hQ_in_U).2
      have hS'_card : (S'.card : ENNReal) ≤ ENNReal.ofReal (7 : ℝ) := by
        have h_eq : (S' : Set ℝ) = S := by simp [S']
        have h : S.encard = ↑S'.card := by
          rw [← h_eq] <;> simp
        rw [h] at hS_encard
        exact_mod_cast hS_encard
      let fiber_img : Finset (ℝ × Set (EuclideanSpace ℝ (Fin 2))) :=
        S'.image (fun x => (x, Q))
      have h_fiber_eq : I_inc.filter (fun p => p.2 = Q) = fiber_img := by
        ext p
        simp only [Finset.mem_filter, fiber_img, Finset.mem_image]
        constructor
        · rintro ⟨hp, h_eq⟩
          rcases Finset.mem_biUnion.mp hp with ⟨x', hx', h6'⟩
          have h_eq1 : p.1 = x' := by
            have h : p.1 ∈ ({x'} : Finset ℝ) := (Finset.mem_product.mp h6').1
            simpa using h
          have h8 : x' ∈ X y := by rw [← hX_coe] <;> exact Finset.mem_coe.mp hx'
          have h9 : p.2 ∈ Cz_finset x' := (Finset.mem_product.mp h6').2
          have h9' : Q ∈ Cz_finset x' := by rw [← h_eq]; exact h9
          have h10 : x' ∈ S' := by
            have h101 : x' ∈ S := by
              simp only [S, Set.mem_setOf_eq]
              exact ⟨h8, by rw [← hCz_finset_coe x' h8] <;> exact h9'⟩
            simpa [S'] using h101
          have h11 : (x', Q) = p := by
            ext <;> simp [h_eq1, h_eq]
          exact ⟨x', h10, h11⟩
        · rintro ⟨x, hx, rfl⟩
          have hxS : x ∈ S := by simpa [S'] using hx
          have hxX : x ∈ X y := hxS.1
          have hQ' : Q ∈ Cz x := hxS.2
          have h11 : Q ∈ Cz_finset x := by
            have h : Q ∈ (Cz_finset x : Set _) := by
              rw [hCz_finset_coe x hxX] <;> exact hQ'
            exact Finset.mem_coe.mp h
          have h_prod : (x, Q) ∈ ({x} : Finset ℝ) ×ˢ Cz_finset x := by
            simp [h11]
          have h' : x ∈ X_finset := by
            have h : x ∈ (X_finset : Set ℝ) := by
              rw [hX_coe] <;> exact hxX
            exact Finset.mem_coe.mp h
          have h12 : (x, Q) ∈ I_inc := by
            simp only [I_inc, Finset.mem_biUnion]
            exact ⟨x, h', h_prod⟩
          exact ⟨h12, rfl⟩
      rw [h_fiber_eq]
      have h_img_card : fiber_img.card = S'.card := by
        apply Finset.card_image_of_injective
        intro x1 x2 h
        exact Prod.ext_iff.mp h |>.1
      rw [h_img_card]
      exact hS'_card
    have h_sum_le : ∑ Q ∈ U_finset, ((I_inc.filter (fun p => p.2 = Q)).card : ENNReal) ≤
        ∑ Q ∈ U_finset, ENNReal.ofReal (7 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact h_each i ‹_›
    rw [Finset.sum_const] at h_sum_le
    simpa [mul_comm] using h_sum_le

  have hU_sub_T : (U_finset.card : ENNReal) ≤ ENat.toENNReal hT.encard := by
    let T_finset : Finset (Set (EuclideanSpace ℝ (Fin 2))) := hT_finite.toFinset
    have hT_coe : (T_finset : Set _) = hT := by simp [T_finset]
    have h1 : U_set ⊆ hT := hU_sub
    have h2 : (U_finset : Set _) ⊆ hT := by
      rw [hU_coe] <;> exact h1
    have h3 : U_finset.card ≤ T_finset.card := by
      apply Finset.card_le_card
      intro Q hQ
      have hQ_in_T : Q ∈ hT := h2 (Finset.mem_coe.mpr hQ)
      have h : Q ∈ (T_finset : Set _) := by
        rw [hT_coe] <;> exact hQ_in_T
      exact Finset.mem_coe.mp h
    have h5 : hT.encard = ↑T_finset.card := by
      rw [← hT_coe] <;> simp
    rw [h5]
    exact_mod_cast h3

  have hX_encard : ((X y).encard : ENNReal) = (X_finset.card : ENNReal) := by
    have h : (X y).encard = ↑X_finset.card := by
      rw [← hX_coe] <;> simp
    exact_mod_cast h

  have h_half_le : ENNReal.ofReal ((1/2:ℝ) * C⁻¹ * δ ^ (-s)) ≤
      ENNReal.ofReal (C⁻¹ * δ ^ (-s)) := by
    apply ENNReal.ofReal_le_ofReal
    have h_pos1 : 0 < C⁻¹ * δ ^ (-s) := by positivity
    linarith

  calc
    ((X y).encard : ENNReal) * ENNReal.ofReal ((1/2:ℝ) * C⁻¹ * δ ^ (-s))
      ≤ (X_finset.card : ENNReal) * ENNReal.ofReal (C⁻¹ * δ ^ (-s)) := by
        rw [hX_encard]
        gcongr
        <;> exact h_half_le
    _ ≤ (I_inc.card : ENNReal) := hI_lower
    _ ≤ ENNReal.ofReal (7 : ℝ) * (U_finset.card : ENNReal) := hI_upper
    _ ≤ ENNReal.ofReal (7 : ℝ) * ENat.toENNReal hT.encard := by
        gcongr
        <;> exact hU_sub_T

end ProductLikeIncidence.ProductReduction
