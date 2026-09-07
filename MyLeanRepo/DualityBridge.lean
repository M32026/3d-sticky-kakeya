module

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

open Set Bornology ENNReal

namespace ProductLikeIncidence.DualityBridge

/-! ## Lemma 1: Point membership criterion -/

lemma mem_tube_from_rectangle_iff {a b δ : ℝ} (_hδ : 0 < δ)
    {z : EuclideanSpace ℝ (Fin 2)} :
    z ∈ appendixDyadicTubeFromRectangle a b δ ↔
      ∃ (a' : ℝ), a' ∈ Set.Ico a (a + δ) ∧
        ∃ (b' : ℝ), b' ∈ Set.Ico b (b + δ) ∧
          z 0 = a' * z 1 + b' := by
  simp only [appendixDyadicTubeFromRectangle, appendixDualOfParameterSet,
    appendixDyadicParameterRectangle, appendixDualLineMap, appendixDualLine]
  constructor
  · rintro ⟨p, hp, hz⟩
    exact ⟨p 0, hp.1, p 1, hp.2, by simpa using hz⟩
  · rintro ⟨a', ha', b', hb', hz⟩
    let p : EuclideanSpace ℝ (Fin 2) :=
      EuclideanSpace.equiv (Fin 2) ℝ |>.symm fun i => if i = 0 then a' else b'
    have h1 : p 0 = a' := by simp [p]
    have h2 : p 1 = b' := by simp [p]
    exact ⟨p, ⟨by rw [h1]; exact ha', by rw [h2]; exact hb'⟩, by simpa [h1, h2] using hz⟩

/-! ## Lemma 2: x-coordinate bound -/

lemma tube_x_bound {a b δ x y : ℝ} (hδ : 0 < δ) (hy1 : 0 ≤ y) (hy2 : y ≤ 1)
    (a' b' : ℝ) (ha1 : a ≤ a') (ha2 : a' < a + δ)
    (hb1 : b ≤ b') (hb2 : b' < b + δ) (h_eq : x = a' * y + b') :
    a * y + b ≤ x ∧ x < a * y + b + 2 * δ := by
  have h_upper1 : a' * y + b' < (a + δ) * y + (b + δ) := by
    have h1 : a' * y ≤ (a + δ) * y := by
      have h2 : a' ≤ a + δ := by linarith
      nlinarith
    nlinarith
  have h_upper2 : (a + δ) * y + (b + δ) ≤ a * y + b + 2 * δ := by
    have h3 : (a + δ) * y + (b + δ) = a * y + b + δ * (1 + y) := by ring
    rw [h3]
    have h4 : δ * (1 + y) ≤ 2 * δ := by nlinarith
    nlinarith
  constructor
  · rw [h_eq]
    have h5 : a * y ≤ a' * y := by nlinarith
    nlinarith
  · rw [h_eq]
    nlinarith

/-! ## Lemma 3: At most two δ-grid points in interval of length ≤ 2δ -/

lemma grid_points_in_interval_le2 {δ : ℝ} (hδ : 0 < δ) {c d : ℝ} (hlen : d - c ≤ 2 * δ) :
    Set.encard {k : ℤ | (δ * (k : ℝ)) ∈ Set.Ico c d} ≤ 2 := by
  let S : Set ℤ := {k | (δ * (k : ℝ)) ∈ Set.Ico c d}
  have hS_fin : S.Finite := by
    have h1 : S ⊆ Set.Icc (⌊c / δ⌋ - 1) (⌈d / δ⌉ + 1) := by
      intro k hk
      have h2 : c ≤ δ * (k : ℝ) := (Set.mem_Ico.mp hk).1
      have h3 : δ * (k : ℝ) < d := (Set.mem_Ico.mp hk).2
      have h4 : (k : ℝ) ≥ c / δ - 1 := by
        have h5 : c / δ ≤ (k : ℝ) := by
          calc c / δ ≤ (δ * (k : ℝ)) / δ := by gcongr
            _ = (k : ℝ) := by field_simp [hδ.ne'] <;> ring
        linarith
      have h6 : (k : ℝ) ≤ d / δ + 1 := by
        have h7 : (k : ℝ) < d / δ := by
          calc (k : ℝ) = (δ * (k : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
            _ < d / δ := by gcongr
        linarith
      have h8 : (⌊c / δ⌋ - 1 : ℝ) ≤ (k : ℝ) := by
        have h9 : (⌊c / δ⌋ : ℝ) ≤ c / δ := Int.floor_le (c / δ)
        linarith
      have h10 : (k : ℝ) ≤ (⌈d / δ⌉ + 1 : ℝ) := by
        have h11 : (d / δ : ℝ) ≤ (⌈d / δ⌉ : ℝ) := Int.le_ceil (d / δ)
        linarith
      exact Set.mem_Icc.mpr ⟨by exact_mod_cast h8, by exact_mod_cast h10⟩
    exact Set.Finite.subset (Set.finite_Icc _ _) h1
  let s : Finset ℤ := hS_fin.toFinset
  have hsc : (s : Set ℤ) = S := by
    exact Finite.coe_toFinset hS_fin
  have h_card : S.encard = ↑s.card := by
    rw [← hsc]
    simp
  by_cases h : s.card ≤ 2
  · rw [h_card]; exact_mod_cast h
  · -- s.card ≥ 3, extract 3 distinct elements manually
    have hgt : s.card ≥ 3 := by omega
    have ha : ∃ a, a ∈ s := Finset.card_pos.mp (by omega)
    rcases ha with ⟨a, ha_mem⟩
    let s1 := s.erase a
    have hs1 : s1.card = s.card - 1 := by
      rw [Finset.card_erase_of_mem ha_mem] <;> omega
    have hb : ∃ b, b ∈ s1 := Finset.card_pos.mp (by omega)
    rcases hb with ⟨b, hb_mem⟩
    have hba : b ≠ a := (Finset.mem_erase.mp hb_mem).1
    have hb_s : b ∈ s := (Finset.mem_erase.mp hb_mem).2
    let s2 := s1.erase b
    have hs2 : s2.card = s1.card - 1 := by
      rw [Finset.card_erase_of_mem hb_mem] <;> omega
    have hc : ∃ c', c' ∈ s2 := Finset.card_pos.mp (by omega)
    rcases hc with ⟨c', hc_mem⟩
    have hca : c' ≠ a := by
      have h : c' ∈ s1 := (Finset.mem_erase.mp hc_mem).2
      exact (Finset.mem_erase.mp h).1
    have hcb : c' ≠ b := (Finset.mem_erase.mp hc_mem).1
    have hc_s : c' ∈ s := by
      have h : c' ∈ s1 := (Finset.mem_erase.mp hc_mem).2
      exact (Finset.mem_erase.mp h).2
    have haS : a ∈ S := by rw [←hsc]; exact ha_mem
    have hbS : b ∈ S := by rw [←hsc]; exact hb_s
    have hcS' : c' ∈ S := by rw [←hsc]; exact hc_s
    let lo := min a (min b c')
    let hi := max a (max b c')
    have hlo_is : lo = a ∨ lo = b ∨ lo = c' := by
      simp [lo, min_def] <;> split_ifs <;> omega
    have hhi_is : hi = a ∨ hi = b ∨ hi = c' := by
      simp [hi, max_def] <;> split_ifs <;> omega
    have hloS : lo ∈ S := by
      have h : lo = a ∨ lo = b ∨ lo = c' := hlo_is
      rcases h with (h | h | h)
      · rw [h]; exact haS
      · rw [h]; exact hbS
      · rw [h]; exact hcS'
    have hhiS : hi ∈ S := by
      have h : hi = a ∨ hi = b ∨ hi = c' := hhi_is
      rcases h with (h | h | h)
      · rw [h]; exact haS
      · rw [h]; exact hbS
      · rw [h]; exact hcS'
    have hlohi : lo < hi := by
      simp only [lo, hi, min_def, max_def] <;> split_ifs <;> omega
    have hdiff : (hi : ℝ) - (lo : ℝ) ≥ 2 := by exact_mod_cast (by omega)
    have h1 : c ≤ δ * (lo : ℝ) := (Set.mem_Ico.mp hloS).1
    have h2 : δ * (hi : ℝ) < d := (Set.mem_Ico.mp hhiS).2
    have h3 : δ * (hi : ℝ) - δ * (lo : ℝ) ≥ 2 * δ := by
      have h4 : (hi : ℝ) - (lo : ℝ) ≥ 2 := hdiff
      have h6 : δ * (hi : ℝ) - δ * (lo : ℝ) = δ * ((hi : ℝ) - (lo : ℝ)) := by ring
      rw [h6]
      nlinarith
    have h7 : δ * (hi : ℝ) < d := h2
    have h8 : c ≤ δ * (lo : ℝ) := h1
    have h9 : δ * (hi : ℝ) - δ * (lo : ℝ) < d - c := by
      calc δ * (hi : ℝ) - δ * (lo : ℝ)
        < d - δ * (lo : ℝ) := by nlinarith
      _ ≤ d - c := by nlinarith
    have h10 : d - c ≤ 2 * δ := hlen
    have h11 : δ * (hi : ℝ) - δ * (lo : ℝ) ≥ 2 * δ := h3
    nlinarith

/-! ## Lemma 4: Canonical cube correctness -/

lemma canonical_cube_correct {δ : ℝ} {T : Set (EuclideanSpace ℝ (Fin 2))}
    (hT : T ∈ appendixDyadicTubes δ) :
    productLikeAppendixDyadicTubeCanonicalParameterCube δ T ∈
      dyadicCubesMeeting (d := 2) δ appendixParameterStrip ∧
    appendixDualOfParameterSet
      (productLikeAppendixDyadicTubeCanonicalParameterCube δ T) = T := by
  dsimp only [productLikeAppendixDyadicTubeCanonicalParameterCube]
  rw [dif_pos hT]
  exact Classical.choose_spec hT

/-! ## Lemma 5: Parameter cubes near dual line -/

lemma parameter_cube_near_dual_line {a b δ x y : ℝ} (hδ : 0 < δ)
    (hy1 : 0 ≤ y) (hy2 : y ≤ 1)
    (a' b' : ℝ) (ha1 : a ≤ a') (ha2 : a' < a + δ)
    (hb1 : b ≤ b') (hb2 : b' < b + δ) (h_eq : x = a' * y + b') :
    0 ≤ x - a * y - b ∧ x - a * y - b < 2 * δ := by
  have h := tube_x_bound hδ hy1 hy2 a' b' ha1 ha2 hb1 hb2 h_eq
  constructor
  · linarith [h.1]
  · linarith [h.2]

/-! ## Corollary: Tube-grid intersection bound -/

/-- A δ-tube from rectangle [a,a+δ)×[b,b+δ) intersects X_y × {y}
    (with X_y ⊆ δℤ and y∈[0,1]) in at most 2 points. -/
lemma tube_grid_intersection_le2 {a b δ y : ℝ} (hδ : 0 < δ) (hy1 : 0 ≤ y) (hy2 : y ≤ 1)
    {Xy : Set ℝ} (hXy : Xy ⊆ productLikeIntegerGrid δ) :
    Set.encard {x : ℝ | x ∈ Xy ∧
      (EuclideanSpace.equiv (Fin 2) ℝ |>.symm (fun i : Fin 2 => if i = 0 then x else y))
        ∈ appendixDyadicTubeFromRectangle a b δ} ≤ 2 := by
  let S : Set ℝ := {x | x ∈ Xy ∧
      (EuclideanSpace.equiv (Fin 2) ℝ |>.symm (fun i : Fin 2 => if i = 0 then x else y))
        ∈ appendixDyadicTubeFromRectangle a b δ}
  let c := a * y + b
  let d := a * y + b + 2 * δ
  have hlen : d - c ≤ 2 * δ := by simp [c, d] <;> linarith
  let T : Set ℤ := {k | (δ * (k : ℝ)) ∈ Set.Ico c d}
  have h_encard_T : Set.encard T ≤ 2 := grid_points_in_interval_le2 hδ hlen
  have hS_to_T : S ⊆ (fun k : ℤ => δ * (k : ℝ)) '' T := by
    intro x hx
    have h1 : x ∈ Xy := hx.1
    have h2 : x ∈ productLikeIntegerGrid δ := hXy h1
    rcases h2 with ⟨k, hk⟩
    have h_eq : x = δ * (k : ℝ) := hk
    have hz0 : (EuclideanSpace.equiv (Fin 2) ℝ |>.symm (fun i : Fin 2 => if i = 0 then x else y)) 0 = x := by simp
    have hz1 : (EuclideanSpace.equiv (Fin 2) ℝ |>.symm (fun i : Fin 2 => if i = 0 then x else y)) 1 = y := by simp
    have h_mem := hx.2
    rw [mem_tube_from_rectangle_iff hδ] at h_mem
    rcases h_mem with ⟨a', ha', b', hb', h_eq2⟩
    rw [hz0, hz1] at h_eq2
    have h_bounds := tube_x_bound hδ hy1 hy2 a' b' ha'.1 ha'.2 hb'.1 hb'.2 h_eq2
    have h3 : c ≤ x := by simpa [c] using h_bounds.1
    have h4 : x < d := by simpa [d] using h_bounds.2
    rw [h_eq] at h3 h4
    have hkT : k ∈ T := by
      simp only [T, Set.mem_setOf_eq]
      exact ⟨h3, h4⟩
    exact ⟨k, hkT, h_eq.symm⟩
  have h_inj : Set.InjOn (fun k : ℤ => δ * (k : ℝ)) T := by
    intro k1 _ k2 _ h
    have h5 : δ * (k1 : ℝ) = δ * (k2 : ℝ) := h
    have h6 : (k1 : ℝ) = (k2 : ℝ) := by
      apply (mul_right_inj' hδ.ne').mp
      exact h5
    exact_mod_cast h6
  have h_encard_S : Set.encard S ≤ Set.encard T := by
    calc Set.encard S
      ≤ Set.encard ((fun k : ℤ => δ * (k : ℝ)) '' T) := Set.encard_mono hS_to_T
    _ = Set.encard T := by
      exact InjOn.encard_image h_inj
  exact h_encard_S.trans h_encard_T

/-! ## Covering-number-to-cardinality reduction -/

/-- Two distinct δ-dyadic cubes (same scale) are disjoint. -/
lemma dyadic_cubes_disjoint {δ : ℝ} (hδ : 0 < δ) {k k' : Fin 2 → ℤ} (h : k ≠ k') :
    Disjoint (dyadicCube δ k) (dyadicCube δ k') := by
  have h_i : ∃ i : Fin 2, k i ≠ k' i := by
    by_contra h2; push Not at h2; exact h (funext h2)
  rcases h_i with ⟨i, hne⟩
  by_cases h_lt : k i < k' i
  · rw [Set.disjoint_left]
    intro x hx hx'
    have h1 : x i < δ * ((k i : ℝ) + 1) := (hx i).2
    have h2 : δ * (k' i : ℝ) ≤ x i := (hx' i).1
    have h3 : (k i : ℝ) + 1 ≤ (k' i : ℝ) := by exact_mod_cast (by linarith)
    have h4 : δ * ((k i : ℝ) + 1) ≤ δ * (k' i : ℝ) := by gcongr <;> linarith
    linarith
  · have h_gt : k' i < k i := by omega
    rw [Set.disjoint_left]
    intro x hx hx'
    have h1 : x i < δ * ((k' i : ℝ) + 1) := (hx' i).2
    have h2 : δ * (k i : ℝ) ≤ x i := (hx i).1
    have h3 : (k' i : ℝ) + 1 ≤ (k i : ℝ) := by exact_mod_cast (by linarith)
    have h4 : δ * ((k' i : ℝ) + 1) ≤ δ * (k i : ℝ) := by gcongr <;> linarith
    linarith

/-- The δ-dyadic cubes meeting the parameter set of a tube family are exactly
the canonical parameter cubes of the tubes in the family. -/
lemma covering_cubes_eq_image {δ : ℝ} {𝒯 : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hδ : 0 < δ) (h𝒯 : 𝒯 ⊆ appendixDyadicTubes δ) :
    dyadicCubesMeeting (d := 2) δ (productLikeAppendixDyadicTubeParameterSet δ 𝒯) =
    productLikeAppendixDyadicTubeCanonicalParameterCube δ '' 𝒯 := by
  let f := productLikeAppendixDyadicTubeCanonicalParameterCube δ
  let P := productLikeAppendixDyadicTubeParameterSet δ 𝒯
  ext Q
  simp only [dyadicCubesMeeting, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hQ_cube, ⟨z, hzQ, hzP⟩⟩
    have hzP' : z ∈ P := hzP
    simp only [P, productLikeAppendixDyadicTubeParameterSet, Set.mem_sUnion] at hzP'
    rcases hzP' with ⟨Q1, ⟨T, hT, h_eq⟩, hzQ1⟩
    have hQ1_cube : Q1 ∈ dyadicCubes (d := 2) δ := by
      rw [←h_eq]
      exact (canonical_cube_correct (h𝒯 hT)).1.1
    rcases hQ_cube with ⟨k, rfl⟩
    rcases hQ1_cube with ⟨k1, rfl⟩
    have hQ_eq : dyadicCube δ k = dyadicCube δ k1 := by
      by_cases h : k = k1
      · rw [h]
      · exfalso
        have h_disj := dyadic_cubes_disjoint hδ h
        exact h_disj.le_bot ⟨hzQ, hzQ1⟩
    have h_ft : f T = dyadicCube δ k := by
      dsimp only [f]
      rw [h_eq, hQ_eq]
    exact ⟨T, hT, h_ft⟩
  · rintro ⟨T, hT, rfl⟩
    have h_correct := canonical_cube_correct (h𝒯 hT)
    have hQ_cube : f T ∈ dyadicCubes (d := 2) δ := h_correct.1.1
    have hQ_nonempty : (f T).Nonempty := by
      rcases hQ_cube with ⟨k, hk⟩
      rw [hk]
      exact dyadicCube_nonempty hδ k
    have hQ_sub : f T ⊆ P := by
      intro z hz
      simp only [P, productLikeAppendixDyadicTubeParameterSet, Set.mem_sUnion]
      exact ⟨f T, ⟨T, hT, rfl⟩, hz⟩
    have h_inter_nonempty : (f T ∩ P).Nonempty := by
      have h_eq : f T ∩ P = f T := Set.inter_eq_left.mpr hQ_sub
      rw [h_eq]
      exact hQ_nonempty
    exact ⟨hQ_cube, h_inter_nonempty⟩

/-- The dyadic covering number of the parameter set of a tube family equals
the cardinality of the tube family. This is the key reduction that transfers
a lower bound on the covering number to a lower bound on the tube count. -/
lemma covering_number_eq_tube_card {δ : ℝ} {𝒯 : Set (Set (EuclideanSpace ℝ (Fin 2)))}
    (hδ : 0 < δ) (h𝒯 : 𝒯 ⊆ appendixDyadicTubes δ) :
    dyadicCoveringNumber (d := 2) δ (productLikeAppendixDyadicTubeParameterSet δ 𝒯) = 𝒯.encard := by
  let f := productLikeAppendixDyadicTubeCanonicalParameterCube δ
  have h_eq := covering_cubes_eq_image hδ h𝒯
  rw [dyadicCoveringNumber, h_eq]
  have h_inj : Set.InjOn f 𝒯 := by
    intro T1 hT1 T2 hT2 h
    have h1 : appendixDualOfParameterSet (f T1) = T1 :=
      (canonical_cube_correct (h𝒯 hT1)).2
    have h2 : appendixDualOfParameterSet (f T2) = T2 :=
      (canonical_cube_correct (h𝒯 hT2)).2
    rw [h] at h1
    rw [h1] at h2
    exact h2
  exact h_inj.encard_image

end ProductLikeIncidence.DualityBridge
