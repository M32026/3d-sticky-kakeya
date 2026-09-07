module

/-
# Delta-Set Translation by One

Preservation of `IsProductLikeRealDeltaSCSet` under translation by 1.
Needed to move B1 from [0,1] to A ⊆ [1,2] for the Ring theorem.

For dyadic δ = 2^{-N}, 1 = δ · 2^N. For any dyadic r = 2^{-m} with m ≤ N,
1 = r · 2^m. Thus translation by 1 maps dyadic cubes at every scale r ∈ [δ,1]
exactly to dyadic cubes, preserving covering numbers and δ-set properties.

## Results

1. `nreal_translate_by_one` — Nδ(A+1) = Nδ(A)
2. `isProductLikeRealDeltaSCSet_translate_by_one` — full δ-set preservation

## Whiteprint node
`delta_set_translation_by_one`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.StrongRingHelpers
public import MyLeanRepo.Fjord.RingExpansionLemma51
public import MyLeanRepo.CubeIndexSet
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ENNReal Set Classical

namespace ProductLikeIncidence

/-! ### Translation on Euclidean space -/

/-- Translate every coordinate by c. -/
private def translateEuclid {d : ℕ} (c : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm fun i => p i + c

/-- `(translateEuclid c p) i = p i + c`. -/
private lemma translateEuclid_apply {d : ℕ} (c : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    (translateEuclid c p) i = p i + c := by rfl

/-- Translation by -c is inverse of translation by c. -/
private lemma translateEuclid_left_inverse {d : ℕ} (c : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    translateEuclid (-c) (translateEuclid c p) = p := by
  apply (WithLp.equiv 2 (Fin d → ℝ)).injective
  funext i
  calc
    (WithLp.equiv 2 (Fin d → ℝ)) (translateEuclid (-c) (translateEuclid c p)) i
      = (translateEuclid (-c) (translateEuclid c p)) i := by rfl
    _ = (translateEuclid c p) i + (-c) := translateEuclid_apply (-c) _ i
    _ = (p i + c) + (-c) := by rw [translateEuclid_apply c p i]
    _ = p i := by ring
    _ = (WithLp.equiv 2 (Fin d → ℝ)) p i := by rfl

/-- Translation by c is inverse of translation by -c. -/
private lemma translateEuclid_right_inverse {d : ℕ} (c : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    translateEuclid c (translateEuclid (-c) p) = p := by
  have h := translateEuclid_left_inverse (-c) p
  have h2 : -(-c) = c := by ring
  rw [h2] at h
  exact h

/-- Translation by c = r·m maps dyadic cubes to dyadic cubes. -/
private lemma translate_cube {d : ℕ} {r : ℝ} {c : ℝ} {m : ℤ} (hc : c = r * (m : ℝ))
    (k : Fin d → ℤ) :
    translateEuclid c '' dyadicCube r k = dyadicCube r (fun i => k i + m) := by
  ext q
  simp only [Set.mem_image, dyadicCube, Set.mem_setOf_eq]
  constructor
  · rintro ⟨p, hp, rfl⟩
    intro i
    have h1 : (translateEuclid c p) i = p i + c := translateEuclid_apply c p i
    rw [h1]
    have h2 : p i ∈ Set.Ico (r * (k i : ℝ)) (r * ((k i : ℝ) + 1)) := hp i
    have hkm : ((k i + m : ℤ) : ℝ) = (k i : ℝ) + (m : ℝ) := by simp
    rw [hc, hkm]
    constructor <;> linarith [h2.1, h2.2]
  · intro hq
    refine ⟨translateEuclid (-c) q, ?_, translateEuclid_right_inverse c q⟩
    intro i
    have h1 : (translateEuclid (-c) q) i = q i - c := by
      rw [translateEuclid_apply (-c) q i] <;> ring
    rw [h1]
    have h2 : q i ∈ Set.Ico (r * ((k i + m : ℤ) : ℝ)) (r * (((k i + m : ℤ) : ℝ) + 1)) := hq i
    have hkm : ((k i + m : ℤ) : ℝ) = (k i : ℝ) + (m : ℝ) := by simp
    have h2' : q i ∈ Set.Ico (r * ((k i : ℝ) + (m : ℝ))) (r * ((k i : ℝ) + (m : ℝ) + 1)) := by
      simpa [hkm] using h2
    constructor <;> linarith [h2'.1, h2'.2, hc]

/-- Translation by c = δ·m preserves dyadic covering number. -/
private lemma covering_translate {d : ℕ} {δ : ℝ} (hδ_pos : 0 < δ)
    {c : ℝ} {m : ℤ} (hc : c = δ * (m : ℝ))
    {P : Set (EuclideanSpace ℝ (Fin d))} (hP_bdd : Bornology.IsBounded P) :
    dyadicCoveringNumber δ (translateEuclid c '' P) = dyadicCoveringNumber δ P := by
  let T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := translateEuclid c
  let Tinv : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := translateEuclid (-c)
  let mapCube (Q : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)) := T '' Q
  let S1 := dyadicCubesMeeting δ P
  let S2 := dyadicCubesMeeting δ (T '' P)
  have hT_cube : ∀ (k : Fin d → ℤ), mapCube (dyadicCube δ k) = dyadicCube δ (fun i => k i + m) :=
    translate_cube hc
  have h_neg_cast : -c = δ * ((-m : ℤ) : ℝ) := by
    have h1 : -c = -(δ * (m : ℝ)) := by rw [hc]
    have h2 : ((-m : ℤ) : ℝ) = -(m : ℝ) := by simp
    rw [h1, h2] <;> ring
  have hTinv_cube : ∀ (k : Fin d → ℤ), Tinv '' dyadicCube δ k = dyadicCube δ (fun i => k i - m) :=
    translate_cube h_neg_cast
  have h_meeting : ∀ (Q : Set (EuclideanSpace ℝ (Fin d))),
      Q ∈ dyadicCubes d δ → ((Q ∩ P).Nonempty ↔ (mapCube Q ∩ T '' P).Nonempty) := by
    intro Q hQ
    constructor
    · rintro ⟨p, hpQ, hpP⟩
      exact ⟨T p, ⟨p, hpQ, rfl⟩, ⟨p, hpP, rfl⟩⟩
    · rintro ⟨q, hqQ, hqP⟩
      rcases hqQ with ⟨p, hpQ, rfl⟩
      rcases hqP with ⟨p', hpP, h_eq⟩
      have h_p_eq : p' = p := by
        have h : T p' = T p := h_eq
        have h' : p' = p := by
          calc p' = Tinv (T p') := (translateEuclid_left_inverse c p').symm
               _ = Tinv (T p) := by rw [h]
               _ = p := translateEuclid_left_inverse c p
        exact h'
      rw [h_p_eq] at hpP
      exact ⟨p, hpQ, hpP⟩
  have h_mapsTo : mapCube '' S1 ⊆ S2 := by
    intro R hR
    rcases hR with ⟨Q, hQ, rfl⟩
    have hQ_cube : Q ∈ dyadicCubes d δ := hQ.1
    have hQ_meet : (Q ∩ P).Nonempty := hQ.2
    have h_map_cube : mapCube Q ∈ dyadicCubes d δ := by
      rcases hQ_cube with ⟨k, rfl⟩
      rw [hT_cube k]
      exact ⟨_, rfl⟩
    have h_map_meet : (mapCube Q ∩ T '' P).Nonempty := (h_meeting Q hQ_cube).mp hQ_meet
    exact ⟨h_map_cube, h_map_meet⟩
  have h_surjTo : S2 ⊆ mapCube '' S1 := by
    intro R hR
    have hR_cube : R ∈ dyadicCubes d δ := hR.1
    have hR_meet : (R ∩ T '' P).Nonempty := hR.2
    rcases hR_cube with ⟨k, hk⟩
    let Q := Tinv '' R
    have hQ_eq : Q = Tinv '' dyadicCube δ k := by
      dsimp only [Q]
      rw [hk]
    have hQ_cube : Q ∈ dyadicCubes d δ := by
      rw [hQ_eq, hTinv_cube k]
      exact ⟨_, rfl⟩
    have h_mapQ : mapCube Q = R := by
      dsimp only [Q, mapCube]
      have h : T '' (Tinv '' R) = R := by
        ext x
        simp only [Set.mem_image]
        constructor
        · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
          have h_right : T (Tinv z) = z := translateEuclid_right_inverse c z
          rw [h_right] <;> exact hz
        · intro hx
          exact ⟨Tinv x, ⟨x, hx, rfl⟩, translateEuclid_right_inverse c x⟩
      exact h
    have hQ_meet : (Q ∩ P).Nonempty := by
      have h : (mapCube Q ∩ T '' P).Nonempty := by
        rw [h_mapQ]
        exact hR_meet
      exact (h_meeting Q hQ_cube).mpr h
    exact ⟨Q, ⟨hQ_cube, hQ_meet⟩, h_mapQ⟩
  have h_injOn : Set.InjOn mapCube S1 := by
    intro Q1 hQ1 Q2 hQ2 h
    have h4 : Tinv '' (mapCube Q1) = Q1 := by
      ext x
      simp only [mapCube, Set.mem_image]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        have h_right : Tinv (T z) = z := translateEuclid_left_inverse c z
        rw [h_right]
        exact hz
      · intro hx
        exact ⟨T x, ⟨x, hx, rfl⟩, translateEuclid_left_inverse c x⟩
    have h5 : Tinv '' (mapCube Q2) = Q2 := by
      ext x
      simp only [mapCube, Set.mem_image]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        have h_right : Tinv (T z) = z := translateEuclid_left_inverse c z
        rw [h_right]
        exact hz
      · intro hx
        exact ⟨T x, ⟨x, hx, rfl⟩, translateEuclid_left_inverse c x⟩
    rw [← h4, ← h5, h]
  have h_image : mapCube '' S1 = S2 := Set.Subset.antisymm h_mapsTo h_surjTo
  have h_encard : S2.encard = S1.encard := by
    rw [← h_image]
    exact h_injOn.encard_image
  simpa [dyadicCoveringNumber] using h_encard

/-! ### Nreal translation by 1 -/

/-- Translation by 1 preserves `Nreal` for dyadic δ. -/
lemma nreal_translate_by_one {δ : ℝ} (hδ_dyadic : δ ∈ dyadicScales)
    {S : Set ℝ} (hS_bdd : Bornology.IsBounded S) :
    Nreal δ (ProductReduction.translateSet 1 S) = Nreal δ S := by
  rcases hδ_dyadic with ⟨n, rfl⟩
  have hc : (1 : ℝ) = (2 : ℝ) ^ (-(n : ℤ)) * ((2 ^ n : ℤ) : ℝ) := by
    simp [zpow_neg] <;> field_simp <;> ring
  exact ProductReduction.nreal_translation_by_delta_int (by positivity) hS_bdd hc

/-- Translation by any integer `c` preserves `Nreal` for dyadic δ.
Since δ = 2^{-n}, we have c = δ·(c·2^n), so translation by c maps
dyadic cubes exactly to dyadic cubes. -/
lemma nreal_translate_by_int {δ : ℝ} (hδ_dyadic : δ ∈ dyadicScales)
    {S : Set ℝ} (hS_bdd : Bornology.IsBounded S) (c : ℤ) :
    Nreal δ (ProductReduction.translateSet (c : ℝ) S) = Nreal δ S := by
  rcases hδ_dyadic with ⟨n, rfl⟩
  let m : ℤ := c * (2 ^ n)
  have hc : (c : ℝ) = (2 : ℝ) ^ (-(n : ℤ)) * (m : ℝ) := by
    simp [m, zpow_neg] <;> field_simp <;> ring
  exact ProductReduction.nreal_translation_by_delta_int (by positivity) hS_bdd hc

/-! ### Full δ-set preservation -/

/-- Translation by 1 preserves `IsProductLikeRealDeltaSCSet` for dyadic δ. -/
lemma isProductLikeRealDeltaSCSet_translate_by_one
    {δ s C : ℝ} {A : Set ℝ}
    (hδ_dyadic : δ ∈ dyadicScales) (hδ_pos : 0 < δ)
    (hA : IsProductLikeRealDeltaSCSet δ s C A) :
    IsProductLikeRealDeltaSCSet δ s C (ProductReduction.translateSet 1 A) := by
  dsimp only [IsProductLikeRealDeltaSCSet, productLikeRealLineCopy] at hA ⊢
  rcases hA with ⟨hA_bdd, hA_nonempty, h1d, hδ_dyadic', hδ_pos', hs_nonneg, hs_le_one, hC_pos, hA_bound⟩
  let T : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) := translateEuclid 1
  let Tinv : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) := translateEuclid (-1)
  let A1 := ProductReduction.translateSet 1 A
  have h_realLineCopy_eq : realLineCopy A1 = T '' realLineCopy A := by
    ext p
    simp only [realLineCopy, A1, ProductReduction.translateSet, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hxA, hpx⟩
      let q : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 (Fin 1 → ℝ)).symm fun _ => x
      have hq0 : q 0 = x := by rfl
      have hqA : q ∈ realLineCopy A := by
        simpa [realLineCopy, hq0] using hxA
      have hTq : T q = p := by
        apply (WithLp.equiv 2 (Fin 1 → ℝ)).injective
        funext i
        fin_cases i
        simp [T, translateEuclid, hq0, hpx] <;> ring
      exact ⟨q, hqA, hTq⟩
    · rintro ⟨q, hqA, rfl⟩
      have h : (T q) 0 = q 0 + 1 := translateEuclid_apply 1 q 0
      exact ⟨q 0, hqA, h⟩
  have h_isom : Isometry (translateEuclid (1 : ℝ) : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) := by
    refine' Isometry.of_dist_eq fun x y => _
    have h_sub : translateEuclid (1 : ℝ) x - translateEuclid (1 : ℝ) y = x - y := by
      apply (WithLp.equiv 2 (Fin 1 → ℝ)).injective
      funext i
      simp [translateEuclid, Pi.sub_apply] <;> ring
    rw [dist_eq_norm, dist_eq_norm, h_sub]
  have hA1_bdd : Bornology.IsBounded (realLineCopy A1) := by
    rw [h_realLineCopy_eq]
    have h_exists : ∃ (C : ℝ), ∀ (x : EuclideanSpace ℝ (Fin 1)), x ∈ realLineCopy A →
        ∀ (y : EuclideanSpace ℝ (Fin 1)), y ∈ realLineCopy A → dist x y ≤ C :=
      Metric.isBounded_iff.mp hA_bdd
    rcases h_exists with ⟨C, hC⟩
    apply Metric.isBounded_iff.mpr
    refine ⟨C, ?_⟩
    intro u hu v hv
    rcases hu with ⟨z, hz, rfl⟩
    rcases hv with ⟨w, hw, rfl⟩
    have h_dist : dist (translateEuclid 1 z) (translateEuclid 1 w) = dist z w := h_isom.dist_eq z w
    rw [h_dist]
    exact hC z hz w hw
  have hA1_nonempty : (realLineCopy A1).Nonempty := by
    rw [h_realLineCopy_eq]
    exact hA_nonempty.image T
  rcases hδ_dyadic with ⟨N, hδ_eq⟩
  let nδ : ℤ := 2 ^ N
  have h_one_multδ : (1 : ℝ) = δ * (nδ : ℝ) := by
    rw [hδ_eq]
    simp [nδ, zpow_neg] <;> field_simp <;> ring
  have hN_eq : dyadicCoveringNumber δ (realLineCopy A1) = dyadicCoveringNumber δ (realLineCopy A) := by
    rw [h_realLineCopy_eq]
    exact covering_translate hδ_pos h_one_multδ hA_bdd
  refine ⟨hA1_bdd, hA1_nonempty, h1d, hδ_dyadic', hδ_pos', hs_nonneg, hs_le_one, hC_pos, ?_⟩
  intro r Q hr_dyadic hQ hδ_le_r hr_le_one
  have hr_dyadic_copy := hr_dyadic
  rcases hr_dyadic_copy with ⟨M, hr_eq⟩
  let nr : ℤ := 2 ^ M
  have h_one_multr : (1 : ℝ) = r * (nr : ℝ) := by
    rw [hr_eq]
    simp [nr, zpow_neg] <;> field_simp <;> ring
  rcases hQ with ⟨k, hk⟩
  let k' : Fin 1 → ℤ := fun _ => k 0 - nr
  let Q' := dyadicCube r k'
  have hQ'_cube : Q' ∈ dyadicCubes 1 r := ⟨k', rfl⟩
  have h_k_add : ∀ (i : Fin 1), (k' i) + nr = k i := by
    intro i
    fin_cases i <;> simp [k'] <;> omega
  have h_T_Q : T '' Q' = Q := by
    have h := translate_cube h_one_multr k'
    have h9 : (fun i : Fin 1 => k' i + nr) = k := by
      ext i
      exact h_k_add i
    rw [h9] at h
    rw [h, hk]
  have h_Tinv_Q : Tinv '' Q = Q' := by
    have h_neg_cast : -(1 : ℝ) = r * ((-nr : ℤ) : ℝ) := by
      rw [h_one_multr] <;> simp <;> ring
    have h := translate_cube h_neg_cast k
    have h10 : (fun i : Fin 1 => k i + -nr) = k' := by
      ext i
      have h11 : k i + -nr = k i - nr := by ring
      have h12 : k i - nr = k' i := by
        fin_cases i <;> simp [k'] <;> omega
      rw [h11, h12]
    have h13 : Tinv '' Q = translateEuclid (-1) '' dyadicCube r k := by
      have h14 : Tinv = translateEuclid (-1) := by rfl
      rw [h14, hk]
    rw [h13]
    rw [h10] at h
    exact h
  have h_intersection : realLineCopy A1 ∩ Q = T '' (realLineCopy A ∩ Q') := by
    rw [h_realLineCopy_eq]
    ext x
    simp only [Set.mem_image, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h1 with ⟨y, hyA, rfl⟩
      have h3 : y ∈ realLineCopy A ∩ Q' := by
        constructor
        · exact hyA
        · have h4 : T y ∈ Q := h2
          have h5 : y ∈ Tinv '' Q := ⟨T y, h4, translateEuclid_left_inverse 1 y⟩
          rw [h_Tinv_Q] at h5
          exact h5
      exact ⟨y, h3, rfl⟩
    · rintro ⟨y, ⟨hyA, hyQ'⟩, rfl⟩
      constructor
      · exact ⟨y, hyA, rfl⟩
      · have h6 : T y ∈ T '' Q' := ⟨y, hyQ', rfl⟩
        rw [h_T_Q] at h6
        exact h6
  have h_sub : (realLineCopy A ∩ Q') ⊆ realLineCopy A := by
    intro x hx
    exact hx.1
  have h_bdd' : Bornology.IsBounded (realLineCopy A ∩ Q') := hA_bdd.subset h_sub
  have h_cov_eq : dyadicCoveringNumber δ (realLineCopy A1 ∩ Q) =
      dyadicCoveringNumber δ (realLineCopy A ∩ Q') := by
    rw [h_intersection]
    exact covering_translate hδ_pos h_one_multδ h_bdd'
  have h_bound := hA_bound (r := r) (Q := Q') hr_dyadic hQ'_cube hδ_le_r hr_le_one
  have h_cov_eq2 : dyadicCoveringNumber δ (realLineCopy (ProductReduction.translateSet 1 A) ∩ Q) =
      dyadicCoveringNumber δ (realLineCopy A ∩ Q') := by
    simpa [A1] using h_cov_eq
  have hN_eq2 : dyadicCoveringNumber δ (realLineCopy (ProductReduction.translateSet 1 A)) =
      dyadicCoveringNumber δ (realLineCopy A) := by
    simpa [A1] using hN_eq
  rw [h_cov_eq2, hN_eq2]
  exact h_bound

/-- Translation by any integer `c` preserves `IsProductLikeRealDeltaSCSet`
for dyadic δ. Since δ = 2^{-N}, we have c = δ·(c·2^N), so translation by c
maps dyadic cubes at every scale r ∈ [δ,1] exactly to dyadic cubes. -/
lemma isProductLikeRealDeltaSCSet_translate_by_int
    {δ s C : ℝ} {A : Set ℝ} (c : ℤ)
    (hδ_dyadic : δ ∈ dyadicScales) (hδ_pos : 0 < δ)
    (hA : IsProductLikeRealDeltaSCSet δ s C A) :
    IsProductLikeRealDeltaSCSet δ s C (ProductReduction.translateSet (c : ℝ) A) := by
  dsimp only [IsProductLikeRealDeltaSCSet, productLikeRealLineCopy] at hA ⊢
  rcases hA with ⟨hA_bdd, hA_nonempty, h1d, hδ_dyadic', hδ_pos', hs_nonneg, hs_le_one, hC_pos, hA_bound⟩
  let T : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) := translateEuclid (c : ℝ)
  let Tinv : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) := translateEuclid (-(c : ℝ))
  let A1 := ProductReduction.translateSet (c : ℝ) A
  have h_realLineCopy_eq : realLineCopy A1 = T '' realLineCopy A := by
    ext p
    simp only [realLineCopy, A1, ProductReduction.translateSet, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hxA, hpx⟩
      let q : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 (Fin 1 → ℝ)).symm fun _ => x
      have hq0 : q 0 = x := by rfl
      have hqA : q ∈ realLineCopy A := by
        simpa [realLineCopy, hq0] using hxA
      have hTq : T q = p := by
        apply (WithLp.equiv 2 (Fin 1 → ℝ)).injective
        funext i
        fin_cases i
        simp [T, translateEuclid, hq0]
        <;> exact hpx
      exact ⟨q, hqA, hTq⟩
    · rintro ⟨q, hqA, rfl⟩
      have h : (T q) 0 = q 0 + (c : ℝ) := translateEuclid_apply (c : ℝ) q 0
      exact ⟨q 0, hqA, h⟩
  have h_isom : Isometry (translateEuclid (c : ℝ) : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) := by
    refine' Isometry.of_dist_eq fun x y => _
    have h_sub : translateEuclid (c : ℝ) x - translateEuclid (c : ℝ) y = x - y := by
      apply (WithLp.equiv 2 (Fin 1 → ℝ)).injective
      funext i
      simp [translateEuclid, Pi.sub_apply] <;> ring
    rw [dist_eq_norm, dist_eq_norm, h_sub]
  have h_exists : ∃ (C0 : ℝ), ∀ (x : EuclideanSpace ℝ (Fin 1)), x ∈ realLineCopy A →
      ∀ (y : EuclideanSpace ℝ (Fin 1)), y ∈ realLineCopy A → dist x y ≤ C0 :=
    Metric.isBounded_iff.mp hA_bdd
  rcases h_exists with ⟨C0, hC0⟩
  have hA1_bdd : Bornology.IsBounded (realLineCopy A1) := by
    rw [h_realLineCopy_eq]
    apply Metric.isBounded_iff.mpr
    refine ⟨C0, ?_⟩
    intro u hu v hv
    rcases hu with ⟨z, hz, rfl⟩
    rcases hv with ⟨w, hw, rfl⟩
    have h_dist : dist (T z) (T w) = dist z w := h_isom.dist_eq z w
    rw [h_dist]
    exact hC0 z hz w hw
  have hA1_nonempty : (realLineCopy A1).Nonempty := by
    rw [h_realLineCopy_eq]
    exact hA_nonempty.image T
  rcases hδ_dyadic with ⟨N, hδ_eq⟩
  let nδ : ℤ := c * 2 ^ N
  have h_c_multδ : (c : ℝ) = δ * (nδ : ℝ) := by
    rw [hδ_eq]
    simp [nδ, zpow_neg] <;> field_simp <;> ring
  have hN_eq : dyadicCoveringNumber δ (realLineCopy A1) = dyadicCoveringNumber δ (realLineCopy A) := by
    rw [h_realLineCopy_eq]
    exact covering_translate hδ_pos h_c_multδ hA_bdd
  refine ⟨hA1_bdd, hA1_nonempty, h1d, hδ_dyadic', hδ_pos', hs_nonneg, hs_le_one, hC_pos, ?_⟩
  intro r Q hr_dyadic hQ hδ_le_r hr_le_one
  have hr_dyadic_copy := hr_dyadic
  rcases hr_dyadic_copy with ⟨M, hr_eq⟩
  let nr : ℤ := c * 2 ^ M
  have h_c_multr : (c : ℝ) = r * (nr : ℝ) := by
    rw [hr_eq]
    simp [nr, zpow_neg] <;> field_simp <;> ring
  rcases hQ with ⟨k, hk⟩
  let k' : Fin 1 → ℤ := fun _ => k 0 - nr
  let Q' := dyadicCube r k'
  have hQ'_cube : Q' ∈ dyadicCubes 1 r := ⟨k', rfl⟩
  have h_k_add : ∀ (i : Fin 1), (k' i) + nr = k i := by
    intro i
    fin_cases i <;> simp [k'] <;> omega
  have h_T_Q : T '' Q' = Q := by
    have h := translate_cube h_c_multr k'
    have h9 : (fun i : Fin 1 => k' i + nr) = k := by
      ext i
      exact h_k_add i
    rw [h9] at h
    rw [h, hk]
  have h_Tinv_Q : Tinv '' Q = Q' := by
    have h_neg_cast : -(c : ℝ) = r * ((-nr : ℤ) : ℝ) := by
      rw [h_c_multr] <;> simp <;> ring
    have h := translate_cube h_neg_cast k
    have h10 : (fun i : Fin 1 => k i + -nr) = k' := by
      ext i
      have h11 : k i + -nr = k i - nr := by ring
      have h12 : k i - nr = k' i := by
        fin_cases i <;> simp [k'] <;> omega
      rw [h11, h12]
    have h13 : Tinv '' Q = translateEuclid (-(c : ℝ)) '' dyadicCube r k := by
      have h14 : Tinv = translateEuclid (-(c : ℝ)) := by rfl
      rw [h14, hk]
    rw [h13]
    rw [h10] at h
    exact h
  have h_intersection : realLineCopy A1 ∩ Q = T '' (realLineCopy A ∩ Q') := by
    rw [h_realLineCopy_eq]
    ext x
    simp only [Set.mem_image, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h1 with ⟨y, hyA, rfl⟩
      have h3 : y ∈ realLineCopy A ∩ Q' := by
        constructor
        · exact hyA
        · have h4 : T y ∈ Q := h2
          have h5 : y ∈ Tinv '' Q := ⟨T y, h4, translateEuclid_left_inverse (c : ℝ) y⟩
          rw [h_Tinv_Q] at h5
          exact h5
      exact ⟨y, h3, rfl⟩
    · rintro ⟨y, ⟨hyA, hyQ'⟩, rfl⟩
      constructor
      · exact ⟨y, hyA, rfl⟩
      · have h6 : T y ∈ T '' Q' := ⟨y, hyQ', rfl⟩
        rw [h_T_Q] at h6
        exact h6
  have h_sub : (realLineCopy A ∩ Q') ⊆ realLineCopy A := by
    intro x hx
    exact hx.1
  have h_bdd' : Bornology.IsBounded (realLineCopy A ∩ Q') := hA_bdd.subset h_sub
  have h_cov_eq : dyadicCoveringNumber δ (realLineCopy A1 ∩ Q) =
      dyadicCoveringNumber δ (realLineCopy A ∩ Q') := by
    rw [h_intersection]
    exact covering_translate hδ_pos h_c_multδ h_bdd'
  have h_bound := hA_bound (r := r) (Q := Q') hr_dyadic hQ'_cube hδ_le_r hr_le_one
  have h_cov_eq2 : dyadicCoveringNumber δ (realLineCopy (ProductReduction.translateSet (c : ℝ) A) ∩ Q) =
      dyadicCoveringNumber δ (realLineCopy A ∩ Q') := by
    simpa [A1] using h_cov_eq
  have hN_eq2 : dyadicCoveringNumber δ (realLineCopy (ProductReduction.translateSet (c : ℝ) A)) =
      dyadicCoveringNumber δ (realLineCopy A) := by
    simpa [A1] using hN_eq
  rw [h_cov_eq2, hN_eq2]
  exact h_bound

/-- For any real translation `a`, `Nδ(S + a) ≤ 2·Nδ(S)`.
A shifted half-open cube can meet at most two adjacent cubes. -/
lemma nreal_translate_real_le_two {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ}
    (hS : Bornology.IsBounded S) (a : ℝ) :
    Nreal δ (ProductReduction.translateSet a S) ≤ 2 * Nreal δ S := by
  let q : ℤ := Int.floor (a / δ)
  have hq1 : (q : ℝ) ≤ a / δ := Int.floor_le (a / δ)
  have hq2 : a / δ < (q : ℝ) + 1 := Int.lt_floor_add_one (a / δ)
  let r : ℝ := a - δ * (q : ℝ)
  have hr1 : 0 ≤ r := by
    have h : δ * (q : ℝ) ≤ a := by
      calc δ * (q : ℝ) ≤ δ * (a / δ) := by gcongr
        _ = a := by field_simp [hδ.ne'] <;> ring
    linarith
  have hr2 : r < δ := by
    have h : a < δ * ((q : ℝ) + 1) := by
      calc a = δ * (a / δ) := by field_simp [hδ.ne'] <;> ring
        _ < δ * ((q : ℝ) + 1) := by gcongr
    linarith
  let IS := (realCubeIndexSet_finite hδ hS).toFinset
  have hSa : Bornology.IsBounded (ProductReduction.translateSet a S) := by
    have h_exists : ∃ (C0 : ℝ), ∀ (x : ℝ), x ∈ S → ∀ (y : ℝ), y ∈ S → dist x y ≤ C0 :=
      Metric.isBounded_iff.mp hS
    rcases h_exists with ⟨C0, hC0⟩
    apply Metric.isBounded_iff.mpr
    refine ⟨C0, ?_⟩
    intro u hu v hv
    rcases hu with ⟨x, hx, rfl⟩
    rcases hv with ⟨y, hy, rfl⟩
    have h_dist : dist (x + a) (y + a) = dist x y := by
      simp [Real.dist_eq] <;> ring
    rw [h_dist]
    exact hC0 x hx y hy
  let I_Sa := (realCubeIndexSet_finite hδ hSa).toFinset
  have hIS : (IS : Set ℤ) = realCubeIndexSet δ S := Set.Finite.coe_toFinset _
  have hI_Sa : (I_Sa : Set ℤ) = realCubeIndexSet δ (ProductReduction.translateSet a S) :=
    Set.Finite.coe_toFinset _
  have h_main : I_Sa ⊆ IS.image (fun k : ℤ => k + q) ∪ IS.image (fun k : ℤ => k + q + 1) := by
    apply Finset.coe_subset.mp
    rw [Finset.coe_union, Finset.coe_image, Finset.coe_image, hI_Sa, hIS]
    intro k hk
    simp only [realCubeIndexSet, Set.mem_setOf_eq, ProductReduction.translateSet, Set.mem_image] at hk
    rcases hk with ⟨y, hyIco, x, hxS, rfl⟩
    have h1 : δ * (k : ℝ) ≤ x + a := hyIco.1
    have h2 : x + a < δ * ((k : ℝ) + 1) := hyIco.2
    have h3 : δ * ((k : ℝ) - (q : ℝ)) - r ≤ x := by linarith
    have h4 : x < δ * (((k : ℝ) - (q : ℝ)) + 1) - r := by linarith
    have h5 : δ * ((k : ℝ) - (q : ℝ) - 1) < x := by linarith [hr2]
    have h7 : x < δ * (((k : ℝ) - (q : ℝ)) + 1) := by linarith [hr1]
    let j : ℤ := Int.floor (x / δ)
    have hj1 : δ * (j : ℝ) ≤ x := by
      have h : (j : ℝ) ≤ x / δ := Int.floor_le (x / δ)
      have h' : δ * (j : ℝ) ≤ δ * (x / δ) := by gcongr
      have h'' : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
      rw [h''] at h' <;> exact h'
    have hj2 : x < δ * ((j : ℝ) + 1) := by
      have h : x / δ < (j : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
      have h' : δ * (x / δ) < δ * ((j : ℝ) + 1) := by gcongr
      have h'' : δ * (x / δ) = x := by field_simp [hδ.ne'] <;> ring
      rw [h''] at h' <;> exact h'
    have hjS : j ∈ realCubeIndexSet δ S := by
      simp only [realCubeIndexSet, Set.mem_setOf_eq]
      exact ⟨x, ⟨hj1, hj2⟩, hxS⟩
    have h_j1 : (k : ℝ) - (q : ℝ) - 1 < (j : ℝ) + 1 := by
      have h9 : δ * ((k : ℝ) - (q : ℝ) - 1) < x := h5
      have h10 : x < δ * ((j : ℝ) + 1) := hj2
      nlinarith [hδ]
    have h_j2 : (j : ℝ) ≤ (k : ℝ) - (q : ℝ) := by
      by_contra h9
      have h10 : (j : ℝ) > (k : ℝ) - (q : ℝ) := by linarith
      have h11 : j > k - q := by exact_mod_cast h10
      have h12 : j ≥ k - q + 1 := by omega
      have h13 : (j : ℝ) ≥ (k : ℝ) - (q : ℝ) + 1 := by exact_mod_cast h12
      have h14 : δ * (j : ℝ) ≤ x := hj1
      nlinarith [h7, hδ]
    have h14 : (k : ℝ) - (q : ℝ) - 2 < (j : ℝ) := by linarith [h_j1]
    have h15 : (j : ℝ) ≤ (k : ℝ) - (q : ℝ) := h_j2
    have h16 : k - q - 2 < j := by exact_mod_cast h14
    have h17 : j ≤ k - q := by exact_mod_cast h15
    have h_k_eq : k = j + q ∨ k = j + q + 1 := by omega
    rcases h_k_eq with (rfl | rfl)
    · exact Or.inl ⟨j, hjS, by simp⟩
    · exact Or.inr ⟨j, hjS, by simp⟩
  have h_inj1 : Function.Injective (fun k : ℤ => k + q) := by
    intro a b h; simpa using h
  have h_inj2 : Function.Injective (fun k : ℤ => k + q + 1) := by
    intro a b h; simpa using h
  have h_card : I_Sa.card ≤ 2 * IS.card := by
    calc I_Sa.card
      ≤ (IS.image (fun k : ℤ => k + q) ∪ IS.image (fun k : ℤ => k + q + 1)).card :=
        Finset.card_le_card h_main
    _ ≤ (IS.image (fun k : ℤ => k + q)).card + (IS.image (fun k : ℤ => k + q + 1)).card :=
        Finset.card_union_le _ _
    _ = IS.card + IS.card := by
      rw [Finset.card_image_of_injective IS h_inj1, Finset.card_image_of_injective IS h_inj2] <;> ring
    _ = 2 * IS.card := by ring
  have hN_Sa := realCoveringNumber_eq_card hδ hSa
  have hNS := realCoveringNumber_eq_card hδ hS
  dsimp only [Nreal] at *
  rw [hN_Sa, hNS]
  have h_encard_Sa : (realCubeIndexSet δ (ProductReduction.translateSet a S)).encard = I_Sa.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ hSa)] <;> rfl
  have h_encard_S : (realCubeIndexSet δ S).encard = IS.card := by
    rw [← Set.Finite.encard_eq_coe_toFinset_card (realCubeIndexSet_finite hδ hS)] <;> rfl
  rw [h_encard_Sa, h_encard_S]
  norm_cast <;> exact_mod_cast h_card

/-- Also `Nδ(S) ≤ 2·Nδ(S + a)` by translating back. -/
lemma nreal_translate_real_le_two_symm {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ}
    (hS : Bornology.IsBounded S) (a : ℝ) :
    Nreal δ S ≤ 2 * Nreal δ (ProductReduction.translateSet a S) := by
  have hSa_bdd : Bornology.IsBounded (ProductReduction.translateSet a S) := by
    have h_exists : ∃ (C0 : ℝ), ∀ (x : ℝ), x ∈ S → ∀ (y : ℝ), y ∈ S → dist x y ≤ C0 :=
      Metric.isBounded_iff.mp hS
    rcases h_exists with ⟨C0, hC0⟩
    apply Metric.isBounded_iff.mpr
    refine ⟨C0, ?_⟩
    intro u hu v hv
    rcases hu with ⟨x, hx, rfl⟩
    rcases hv with ⟨y, hy, rfl⟩
    have h_dist : dist (x + a) (y + a) = dist x y := by
      simp [Real.dist_eq] <;> ring
    rw [h_dist]
    exact hC0 x hx y hy
  have h : ProductReduction.translateSet (-a) (ProductReduction.translateSet a S) = S := by
    ext x
    simp [ProductReduction.translateSet] <;> constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y + a, hy, by ring⟩
  have h_bound := nreal_translate_real_le_two hδ hSa_bdd (-a)
  rw [h] at h_bound
  exact h_bound

/-! ### Reflection (negation) -/

/-- Negate every coordinate. -/
private def negateEuclid {d : ℕ} (p : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  (WithLp.equiv 2 (Fin d → ℝ)).symm fun i => -p i

private lemma negateEuclid_apply {d : ℕ} (p : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    (negateEuclid p) i = -p i := by rfl

private lemma negateEuclid_invol {d : ℕ} (p : EuclideanSpace ℝ (Fin d)) :
    negateEuclid (negateEuclid p) = p := by
  apply (WithLp.equiv 2 (Fin d → ℝ)).injective
  funext i
  simp [negateEuclid] <;> ring

/-- For a grid-aligned set `S ⊆ δℤ`, the cube index set is exactly
`{j : ℤ | δ*j ∈ S}`. -/
private lemma grid_cube_index_set {δ : ℝ} (hδ_pos : 0 < δ) {S : Set ℝ}
    (hS_grid : S ⊆ productLikeIntegerGrid δ) :
    realCubeIndexSet δ S = {j : ℤ | δ * (j : ℝ) ∈ S} := by
  ext j
  simp only [realCubeIndexSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hxIco, hxS⟩
    have hx_grid : x ∈ productLikeIntegerGrid δ := hS_grid hxS
    rcases hx_grid with ⟨m, rfl⟩
    have h3 : (j : ℝ) ≤ (m : ℝ) := le_of_mul_le_mul_left hxIco.1 hδ_pos
    have h4 : (m : ℝ) < (j : ℝ) + 1 := lt_of_mul_lt_mul_left hxIco.2 hδ_pos.le
    have h3' : j ≤ m := by exact_mod_cast h3
    have h4' : m < j + 1 := by exact_mod_cast h4
    have h_j_eq : j = m := by omega
    rw [h_j_eq] at *
    exact hxS
  · intro h
    refine ⟨δ * (j : ℝ), ?_, h⟩
    constructor <;> simp [hδ_pos]

/-- Covering number is subadditive over union. -/
private lemma covering_union_le {d : ℕ} {δ : ℝ}
    {S T : Set (EuclideanSpace ℝ (Fin d))} :
    dyadicCoveringNumber δ (S ∪ T) ≤
      dyadicCoveringNumber δ S + dyadicCoveringNumber δ T := by
  have h : dyadicCubesMeeting δ (S ∪ T) ⊆
      dyadicCubesMeeting δ S ∪ dyadicCubesMeeting δ T := by
    intro Q hQ
    have hQ_cube : Q ∈ dyadicCubes d δ := hQ.1
    rcases hQ.2 with ⟨x, hxQ, hxST⟩
    cases hxST with
    | inl hxS => exact Or.inl ⟨hQ_cube, ⟨x, hxQ, hxS⟩⟩
    | inr hxT => exact Or.inr ⟨hQ_cube, ⟨x, hxQ, hxT⟩⟩
  have h2 : (dyadicCubesMeeting δ (S ∪ T)).encard ≤
      (dyadicCubesMeeting δ S ∪ dyadicCubesMeeting δ T).encard :=
    Set.encard_mono h
  have h3 : (dyadicCubesMeeting δ S ∪ dyadicCubesMeeting δ T).encard ≤
      (dyadicCubesMeeting δ S).encard + (dyadicCubesMeeting δ T).encard :=
    Set.encard_union_le _ _
  exact le_trans h2 h3

/-- For a grid-aligned set in Euclidean 1-space, negation preserves
dyadic covering number exactly. -/
private lemma covering_neg_grid_euclid {δ : ℝ} (hδ_pos : 0 < δ)
    {S : Set (EuclideanSpace ℝ (Fin 1))}
    (hS_grid : ∀ p ∈ S, ∃ k : ℤ, p 0 = δ * (k : ℝ))
    (hS_bdd : Bornology.IsBounded S) :
    dyadicCoveringNumber δ (negateEuclid '' S) = dyadicCoveringNumber δ S := by
  let S₁ : Set ℝ := (fun p : EuclideanSpace ℝ (Fin 1) => p 0) '' S
  have hS₁_grid : S₁ ⊆ productLikeIntegerGrid δ := by
    intro x hx
    rcases hx with ⟨p, hp, rfl⟩
    exact hS_grid p hp
  have h_exists : ∃ (C0 : ℝ), ∀ (x : EuclideanSpace ℝ (Fin 1)), x ∈ S →
      ∀ (y : EuclideanSpace ℝ (Fin 1)), y ∈ S → dist x y ≤ C0 :=
    Metric.isBounded_iff.mp hS_bdd
  rcases h_exists with ⟨C0, hC0⟩
  have hS₁_bdd : Bornology.IsBounded S₁ := by
    apply Metric.isBounded_iff.mpr
    refine ⟨C0, ?_⟩
    intro u hu v hv
    rcases hu with ⟨x, hx, rfl⟩
    rcases hv with ⟨y, hy, rfl⟩
    have h_dist : dist (x 0) (y 0) = dist x y := by
      have h1 : dist (x 0) (y 0) = |x 0 - y 0| := by rw [Real.dist_eq] <;> rfl
      have h2 : dist x y = ‖x - y‖ := by rw [dist_eq_norm]
      have h3 : ‖x - y‖ = |(x - y) 0| := by
        have h31 : ‖x - y‖ = Real.sqrt (((x - y) 0) ^ 2) := by
          simp [EuclideanSpace.norm_eq] <;> rfl
        rw [h31, Real.sqrt_sq_eq_abs]
      have h4 : (x - y) 0 = x 0 - y 0 := by rfl
      rw [h1, h2, h3, h4]
    rw [h_dist]
    exact hC0 x hx y hy
  have h_eq1 : S = realLineCopy S₁ := by
    ext p
    simp only [S₁, realLineCopy, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · intro hp
      exact ⟨p, hp, rfl⟩
    · rintro ⟨q, hq, h_eq⟩
      have h_p_eq_q : p = q := by
        apply (WithLp.equiv 2 (Fin 1 → ℝ)).injective
        funext i
        fin_cases i
        exact h_eq.symm
      rw [h_p_eq_q]
      exact hq
  let negS₁ : Set ℝ := (fun x : ℝ => -x) '' S₁
  have h_negS₁_bdd : Bornology.IsBounded negS₁ := by
    have h_def : negS₁ = (fun x : ℝ => -x) '' S₁ := by rfl
    rw [h_def]
    let negCLM : ℝ →L[ℝ] ℝ := -(ContinuousLinearMap.id ℝ ℝ)
    exact Bornology.IsBounded.image negCLM hS₁_bdd
  have hneg_grid : negS₁ ⊆ productLikeIntegerGrid δ := by
    intro x hx
    rcases hx with ⟨y, hyA, rfl⟩
    have hy_grid : y ∈ productLikeIntegerGrid δ := hS₁_grid hyA
    rcases hy_grid with ⟨j, rfl⟩
    refine ⟨-j, ?_⟩
    have h : -(δ * (j : ℝ)) = δ * ((-j : ℤ) : ℝ) := by
      have h' : ((-j : ℤ) : ℝ) = -(j : ℝ) := by simp
      rw [h']; ring
    exact h
  have h_neg_eq : negateEuclid '' S = realLineCopy negS₁ := by
    ext p
    simp only [negS₁, realLineCopy, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q 0, ⟨q, hq, rfl⟩, by simp [negateEuclid]⟩
    · rintro ⟨x, ⟨q, hq, rfl⟩, h_eq⟩
      have h : negateEuclid q = p := by
        apply (WithLp.equiv 2 (Fin 1 → ℝ)).injective
        funext i
        fin_cases i <;> simp [negateEuclid, h_eq] <;> ring
      exact ⟨q, hq, h⟩
  have h_idx_neg : realCubeIndexSet δ (negS₁) =
      {j : ℤ | δ * (j : ℝ) ∈ negS₁} :=
    grid_cube_index_set hδ_pos hneg_grid
  have h_idx_A : realCubeIndexSet δ S₁ = {j : ℤ | δ * (j : ℝ) ∈ S₁} :=
    grid_cube_index_set hδ_pos hS₁_grid
  have h_set_eq : {j : ℤ | δ * (j : ℝ) ∈ negS₁} =
      (fun k : ℤ => -k) '' {j : ℤ | δ * (j : ℝ) ∈ S₁} := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨x, hxA, h_eq⟩
      have hx_grid : x ∈ productLikeIntegerGrid δ := hS₁_grid hxA
      rcases hx_grid with ⟨m, rfl⟩
      have h5 : δ * (j : ℝ) = -δ * (m : ℝ) := by linarith
      have h6 : (j : ℝ) = -(m : ℝ) := by
        apply (mul_right_inj' hδ_pos.ne').mp
        linarith
      have h_j_eq : j = -m := by exact_mod_cast h6
      refine ⟨-j, ?_, by simp⟩
      have h7 : δ * ((-j : ℤ) : ℝ) = -δ * (j : ℝ) := by
        have h' : ((-j : ℤ) : ℝ) = -(j : ℝ) := by simp
        rw [h']; ring
      rw [h_j_eq] at *
      simpa [h7] using hxA
    · rintro ⟨k, hk, rfl⟩
      refine ⟨δ * (k : ℝ), hk, ?_⟩
      have h : -(δ * (k : ℝ)) = δ * ((-k : ℤ) : ℝ) := by
        have h' : ((-k : ℤ) : ℝ) = -(k : ℝ) := by simp
        rw [h']; ring
      exact h
  have h4 : realCubeIndexSet δ (negS₁) =
      (fun k : ℤ => -k) '' realCubeIndexSet δ S₁ := by
    rw [h_idx_neg, h_set_eq, h_idx_A]
  have h5 : (realCubeIndexSet δ (negS₁)).encard =
      (realCubeIndexSet δ S₁).encard := by
    rw [h4]
    exact Set.InjOn.encard_image (fun x _ y _ h => by simpa using h)
  have h_card1 : ENat.toENNReal (dyadicCoveringNumber δ S) =
      ENat.toENNReal (realCubeIndexSet δ S₁).encard := by
    simpa [h_eq1] using realCoveringNumber_eq_card hδ_pos hS₁_bdd
  have h_card2 : ENat.toENNReal (dyadicCoveringNumber δ (negateEuclid '' S)) =
      ENat.toENNReal (realCubeIndexSet δ (negS₁)).encard := by
    simpa [h_neg_eq] using realCoveringNumber_eq_card hδ_pos h_negS₁_bdd
  have h6 : ENat.toENNReal (dyadicCoveringNumber δ (negateEuclid '' S)) =
      ENat.toENNReal (dyadicCoveringNumber δ S) := by
    rw [h_card2, h_card1, h5]
  exact ENat.toENNReal_inj.mp h6

/-- For grid-aligned bounded real sets, reflection preserves `Nreal` exactly.

Note: The general statement without grid alignment is false for half-open cubes
(e.g. `Nδ([0, δ/2]) = 1` but `Nδ([-δ/2, 0]) = 2`). Grid alignment ensures each
point sits at a cube left-boundary, so reflection maps cube indices bijectively
`k ↦ -k`. -/
lemma nreal_reflection_eq {δ : ℝ} (hδ_pos : 0 < δ) {A : Set ℝ}
    (hA_grid : A ⊆ productLikeIntegerGrid δ) (hA_bdd : Bornology.IsBounded A) :
    Nreal δ (Set.image (fun x : ℝ => -x) A) = Nreal δ A := by
  let P := realLineCopy A
  let negA := Set.image (fun x : ℝ => -x) A
  let P' := realLineCopy negA
  have hP_grid : ∀ p ∈ P, ∃ k : ℤ, p 0 = δ * (k : ℝ) := by
    intro p hp
    have h : p 0 ∈ A := by simpa [P, realLineCopy] using hp
    have h2 : p 0 ∈ productLikeIntegerGrid δ := hA_grid h
    rcases h2 with ⟨k, hk⟩
    exact ⟨k, hk⟩
  have h_eq : P' = negateEuclid '' P := by
    ext p
    simp only [P', P, realLineCopy, negA, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hxA, hpx⟩
      let q : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 (Fin 1 → ℝ)).symm fun _ => x
      have hq0 : q 0 = x := by rfl
      have hqP : q ∈ P := by
        simp only [P, realLineCopy, Set.mem_setOf_eq]
        rw [hq0]
        exact hxA
      have hTq : negateEuclid q = p := by
        apply (WithLp.equiv 2 (Fin 1 → ℝ)).injective
        funext i
        fin_cases i
        have h1 : (negateEuclid q) 0 = -q 0 := negateEuclid_apply q 0
        have h_eq2 : (negateEuclid q) 0 = p 0 := by
          calc (negateEuclid q) 0
            = -q 0 := h1
          _ = -x := by rw [hq0]
          _ = p 0 := hpx
        exact h_eq2
      exact ⟨q, hqP, hTq⟩
    · rintro ⟨q, hqP, rfl⟩
      have hq0 : q 0 ∈ A := by simpa [P, realLineCopy] using hqP
      have h : (negateEuclid q) 0 = -q 0 := negateEuclid_apply q 0
      exact ⟨q 0, hq0, h⟩
  let f : ℝ → EuclideanSpace ℝ (Fin 1) := fun x =>
    (WithLp.equiv 2 (Fin 1 → ℝ)).symm fun _ => x
  have hf_isom : Isometry f := by
    refine' Isometry.of_dist_eq fun x y => _
    have h1 : dist (f x) (f y) = ‖f x - f y‖ := by rw [dist_eq_norm]
    have h2 : ‖f x - f y‖ = Real.sqrt (((f x - f y) 0)^2) := by
      simp [f, EuclideanSpace.norm_eq] <;> rfl
    have h3 : (f x - f y) 0 = x - y := by simp [f] <;> rfl
    have h4 : dist (f x) (f y) = |x - y| := by
      rw [h1, h2, h3, Real.sqrt_sq_eq_abs]
    rw [h4, Real.dist_eq] <;> rfl
  have hP_eq : P = f '' A := by
    ext p
    simp only [P, realLineCopy, f, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · intro hp
      exact ⟨p 0, hp, by
        apply (WithLp.equiv 2 (Fin 1 → ℝ)).injective
        funext i; fin_cases i <;> rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  have hP_bdd : Bornology.IsBounded P := by
    rw [hP_eq]
    rcases Metric.isBounded_iff.mp hA_bdd with ⟨C0, hC0⟩
    apply Metric.isBounded_iff.mpr
    refine ⟨C0, ?_⟩
    intro u hu v hv
    rcases hu with ⟨x, hx, rfl⟩
    rcases hv with ⟨y, hy, rfl⟩
    have h_dist : dist (f x) (f y) = dist x y := hf_isom.dist_eq x y
    rw [h_dist]
    exact hC0 hx hy
  have h_main : dyadicCoveringNumber δ P' = dyadicCoveringNumber δ P := by
    rw [h_eq]
    exact covering_neg_grid_euclid hδ_pos hP_grid hP_bdd
  dsimp only [Nreal]
  exact congr_arg ENat.toENNReal h_main

/-- The negation of an r-cube in 1D is contained in two adjacent r-cubes. -/
private lemma neg_cube_in_two {r : ℝ} (hr_pos : 0 < r) {k : Fin 1 → ℤ} :
    negateEuclid '' dyadicCube r k ⊆
      dyadicCube r (fun _ : Fin 1 => -(k 0 + 1)) ∪
      dyadicCube r (fun _ : Fin 1 => -(k 0)) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have h1 : x 0 ∈ Set.Ico (r * (k 0 : ℝ)) (r * ((k 0 : ℝ) + 1)) := hx 0
  have h21 : r * (k 0 : ℝ) ≤ x 0 := h1.1
  have h22 : x 0 < r * ((k 0 : ℝ) + 1) := h1.2
  by_cases h : x 0 = r * (k 0 : ℝ)
  · right
    have hneg : (negateEuclid x) 0 = -x 0 := negateEuclid_apply x 0
    have h5 : -x 0 = r * ((-(k 0) : ℤ) : ℝ) := by
      calc -x 0
        = -(r * (k 0 : ℝ)) := by rw [h]
      _ = r * ((-(k 0) : ℤ) : ℝ) := by simp <;> ring
    have h_goal : (negateEuclid x) 0 ∈ Set.Ico (r * ((-(k 0) : ℤ) : ℝ)) (r * (((-(k 0) : ℤ) : ℝ) + 1)) := by
      rw [hneg, h5]
      constructor <;> linarith
    intro i
    fin_cases i
    simpa using h_goal
  · left
    have hneg : (negateEuclid x) 0 = -x 0 := negateEuclid_apply x 0
    have h4 : r * (k 0 : ℝ) < x 0 := lt_of_le_of_ne h21 (Ne.symm h)
    have h_lower : r * ((-(k 0 + 1) : ℤ) : ℝ) ≤ -x 0 := by
      have h9 : r * ((-(k 0 + 1) : ℤ) : ℝ) = -r * ((k 0 : ℝ) + 1) := by simp <;> ring
      rw [h9] <;> linarith
    have h_upper : -x 0 < r * ((-(k 0) : ℤ) : ℝ) := by
      have h9 : r * ((-(k 0) : ℤ) : ℝ) = -r * (k 0 : ℝ) := by simp <;> ring
      rw [h9] <;> linarith
    have h_goal : (negateEuclid x) 0 ∈ Set.Ico (r * ((-(k 0 + 1) : ℤ) : ℝ)) (r * ((-(k 0) : ℤ) : ℝ)) := by
      rw [hneg]
      exact ⟨h_lower, h_upper⟩
    intro i
    fin_cases i
    simpa using h_goal

/-- Reflection preserves `IsProductLikeRealDeltaSCSet` with constant factor 2.
For grid sets, the only loss comes from the fact that the negation of an r-cube
spills into two adjacent r-cubes. -/
lemma isProductLikeRealDeltaSCSet_reflect
    {δ s C : ℝ} {B : Set ℝ}
    (hδ_dyadic : δ ∈ dyadicScales) (hδ_pos : 0 < δ)
    (hB_grid : B ⊆ productLikeUnitGrid δ)
    (hB : IsProductLikeRealDeltaSCSet δ s C B) :
    IsProductLikeRealDeltaSCSet δ s (2 * C) ((fun x : ℝ => -x) '' B) := by
  dsimp only [IsProductLikeRealDeltaSCSet, productLikeRealLineCopy] at hB ⊢
  rcases hB with ⟨hB_bdd, hB_nonempty, h1d, hδ_dyadic', hδ_pos', hs_nonneg, hs_le_one, hC_pos, hB_bound⟩
  let B' := (fun x : ℝ => -x) '' B
  have hB'_grid : B' ⊆ productLikeIntegerGrid δ := by
    intro x hx
    rcases hx with ⟨y, hyB, rfl⟩
    have hy_grid : y ∈ productLikeUnitGrid δ := hB_grid hyB
    have hy_int : y ∈ productLikeIntegerGrid δ := hy_grid.1
    rcases hy_int with ⟨j, rfl⟩
    refine ⟨-j, ?_⟩
    have h : -(δ * (j : ℝ)) = δ * ((-j : ℤ) : ℝ) := by
      simp <;> ring
    exact h
  let P := realLineCopy B
  let P' := realLineCopy B'
  have hP_grid : ∀ p ∈ P, ∃ k : ℤ, p 0 = δ * (k : ℝ) := by
    intro p hp
    have h : p 0 ∈ B := by simpa [P, realLineCopy] using hp
    have h2 : p 0 ∈ productLikeUnitGrid δ := hB_grid h
    have h3 : p 0 ∈ productLikeIntegerGrid δ := h2.1
    rcases h3 with ⟨k, hk⟩
    exact ⟨k, hk⟩
  have h_realLineCopy_eq : P' = negateEuclid '' P := by
    ext p
    simp only [P', P, realLineCopy, B', Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hxB, hpx⟩
      let q : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 (Fin 1 → ℝ)).symm fun _ => x
      have hq0 : q 0 = x := by rfl
      have hqP : q ∈ P := by
        simp only [P, realLineCopy, Set.mem_setOf_eq]
        rw [hq0]
        exact hxB
      have hTq : negateEuclid q = p := by
        apply (WithLp.equiv 2 (Fin 1 → ℝ)).injective
        funext i
        fin_cases i
        have h1 : (negateEuclid q) 0 = -q 0 := negateEuclid_apply q 0
        have hq0 : q 0 = x := by rfl
        have h_eq : (negateEuclid q) 0 = p 0 := by
          calc (negateEuclid q) 0
            = -q 0 := h1
          _ = -x := by rw [hq0]
          _ = p 0 := hpx
        exact h_eq
      exact ⟨q, hqP, hTq⟩
    · rintro ⟨q, hqP, rfl⟩
      have h : (negateEuclid q) 0 = -q 0 := negateEuclid_apply q 0
      exact ⟨q 0, hqP, h⟩
  have h_isom : Isometry (negateEuclid : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)) := by
    refine' Isometry.of_dist_eq fun x y => _
    have h_sub : negateEuclid x - negateEuclid y = -(x - y) := by
      apply (WithLp.equiv 2 (Fin 1 → ℝ)).injective
      funext i
      simp [negateEuclid, Pi.sub_apply] <;> ring
    rw [dist_eq_norm, dist_eq_norm, h_sub, norm_neg]
  have h_exists : ∃ (C0 : ℝ), ∀ (x : EuclideanSpace ℝ (Fin 1)), x ∈ P →
      ∀ (y : EuclideanSpace ℝ (Fin 1)), y ∈ P → dist x y ≤ C0 :=
    Metric.isBounded_iff.mp hB_bdd
  rcases h_exists with ⟨C0, hC0⟩
  have hP'_bdd : Bornology.IsBounded P' := by
    rw [h_realLineCopy_eq]
    apply Metric.isBounded_iff.mpr
    refine ⟨C0, ?_⟩
    intro u hu v hv
    rcases hu with ⟨z, hz, rfl⟩
    rcases hv with ⟨w, hw, rfl⟩
    have h_dist : dist (negateEuclid z) (negateEuclid w) = dist z w := h_isom.dist_eq z w
    rw [h_dist]
    exact hC0 z hz w hw
  have hP'_nonempty : P'.Nonempty := by
    rw [h_realLineCopy_eq]
    exact hB_nonempty.image negateEuclid
  have hN_eq : dyadicCoveringNumber δ P' = dyadicCoveringNumber δ P := by
    rw [h_realLineCopy_eq]
    exact covering_neg_grid_euclid hδ_pos hP_grid hB_bdd
  have hC2_pos : 0 < 2 * C := by linarith
  refine ⟨hP'_bdd, hP'_nonempty, h1d, hδ_dyadic', hδ_pos', hs_nonneg, hs_le_one, hC2_pos, ?_⟩
  intro r Q hr_dyadic hQ hδ_le_r hr_le_one
  rcases hQ with ⟨k, hk⟩
  let k' : Fin 1 → ℤ := fun _ => -(k 0 + 1)
  let k'' : Fin 1 → ℤ := fun _ => -(k 0)
  let Q' := dyadicCube r k'
  let Q'' := dyadicCube r k''
  have hQ'_cube : Q' ∈ dyadicCubes 1 r := ⟨k', rfl⟩
  have hQ''_cube : Q'' ∈ dyadicCubes 1 r := ⟨k'', rfl⟩
  have hr_pos : 0 < r := by
    rcases hr_dyadic with ⟨n, rfl⟩
    positivity
  have h_neg_cube : negateEuclid '' Q ⊆ Q' ∪ Q'' := by
    rw [hk]
    exact neg_cube_in_two hr_pos
  have h_intersection : P' ∩ Q = negateEuclid '' (P ∩ (negateEuclid '' Q)) := by
    rw [h_realLineCopy_eq]
    ext y
    simp only [Set.mem_image, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h1 with ⟨x, hxP, rfl⟩
      have h3 : x ∈ P ∩ (negateEuclid '' Q) := by
        constructor
        · exact hxP
        · have h4 : negateEuclid x ∈ Q := h2
          have h5 : x ∈ negateEuclid '' Q := ⟨negateEuclid x, h4, negateEuclid_invol x⟩
          exact h5
      exact ⟨x, h3, rfl⟩
    · rintro ⟨x, ⟨hxP, hxQ⟩, rfl⟩
      constructor
      · exact ⟨x, hxP, rfl⟩
      · rcases hxQ with ⟨q, hqQ, h_eq⟩
        have h7 : negateEuclid x = q := by
          calc negateEuclid x
            = negateEuclid (negateEuclid q) := by rw [h_eq]
          _ = q := negateEuclid_invol q
        rw [h7]
        exact hqQ
  have h_subset : P ∩ (negateEuclid '' Q) ⊆ (P ∩ Q') ∪ (P ∩ Q'') := by
    intro x hx
    have hxP : x ∈ P := hx.1
    have hxQ : x ∈ negateEuclid '' Q := hx.2
    have h_in_union : x ∈ Q' ∪ Q'' := h_neg_cube hxQ
    cases h_in_union with
    | inl hQ' => exact Or.inl ⟨hxP, hQ'⟩
    | inr hQ'' => exact Or.inr ⟨hxP, hQ''⟩
  have hS_sub : P ∩ (negateEuclid '' Q) ⊆ P := by
    intro x hx
    exact hx.1
  have hS_bdd : Bornology.IsBounded (P ∩ (negateEuclid '' Q)) :=
    Bornology.IsBounded.subset hB_bdd hS_sub
  have h_cov_eq : dyadicCoveringNumber δ (P' ∩ Q) =
      dyadicCoveringNumber δ (P ∩ (negateEuclid '' Q)) := by
    rw [h_intersection]
    exact covering_neg_grid_euclid hδ_pos (fun p hp => hP_grid p hp.1) hS_bdd
  have h_cov_le : dyadicCoveringNumber δ (P ∩ (negateEuclid '' Q)) ≤
      dyadicCoveringNumber δ (P ∩ Q') + dyadicCoveringNumber δ (P ∩ Q'') := by
    calc dyadicCoveringNumber δ (P ∩ (negateEuclid '' Q))
      ≤ dyadicCoveringNumber δ ((P ∩ Q') ∪ (P ∩ Q'')) :=
        dyadicCoveringNumber_mono h_subset
    _ ≤ dyadicCoveringNumber δ (P ∩ Q') + dyadicCoveringNumber δ (P ∩ Q'') :=
        covering_union_le
  have h_bound1 := hB_bound (r := r) (Q := Q') hr_dyadic hQ'_cube hδ_le_r hr_le_one
  have h_bound2 := hB_bound (r := r) (Q := Q'') hr_dyadic hQ''_cube hδ_le_r hr_le_one
  have h_main : ENat.toENNReal (dyadicCoveringNumber δ (P' ∩ Q)) ≤
      ENNReal.ofReal (2 * C) * ENat.toENNReal (dyadicCoveringNumber δ P') *
        ENNReal.ofReal (r ^ s) := by
    rw [h_cov_eq]
    have h9 : ENat.toENNReal (dyadicCoveringNumber δ (P ∩ (negateEuclid '' Q))) ≤
        ENat.toENNReal (dyadicCoveringNumber δ (P ∩ Q') + dyadicCoveringNumber δ (P ∩ Q'')) := by
      exact ENat.toENNReal_mono h_cov_le
    have h10 : ENat.toENNReal (dyadicCoveringNumber δ (P ∩ Q') + dyadicCoveringNumber δ (P ∩ Q'')) =
        ENat.toENNReal (dyadicCoveringNumber δ (P ∩ Q')) +
        ENat.toENNReal (dyadicCoveringNumber δ (P ∩ Q'')) := by
      exact ENat.toENNReal_add (dyadicCoveringNumber δ (P ∩ Q')) (dyadicCoveringNumber δ (P ∩ Q''))
    rw [h10] at h9
    calc ENat.toENNReal (dyadicCoveringNumber δ (P ∩ (negateEuclid '' Q)))
      ≤ ENat.toENNReal (dyadicCoveringNumber δ (P ∩ Q')) +
           ENat.toENNReal (dyadicCoveringNumber δ (P ∩ Q'')) := h9
    _ ≤ ENNReal.ofReal C * ENat.toENNReal (dyadicCoveringNumber δ P) * ENNReal.ofReal (r ^ s) +
           ENNReal.ofReal C * ENat.toENNReal (dyadicCoveringNumber δ P) * ENNReal.ofReal (r ^ s) := by
      exact add_le_add h_bound1 h_bound2
    _ = ENNReal.ofReal (2 * C) * ENat.toENNReal (dyadicCoveringNumber δ P) *
          ENNReal.ofReal (r ^ s) := by
      have h13 : ENNReal.ofReal (2 * C) = ENNReal.ofReal C + ENNReal.ofReal C := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        <;> ring_nf
      rw [h13]
      <;> ring
    _ = ENNReal.ofReal (2 * C) * ENat.toENNReal (dyadicCoveringNumber δ P') *
          ENNReal.ofReal (r ^ s) := by rw [hN_eq]
  exact h_main

end ProductLikeIncidence
