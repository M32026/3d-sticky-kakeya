module

/-
# Union of Real Delta-Sets

A finite union of `(δ, κ, C_i)`-sets is a `(δ, κ, ∑ C_i)`-set.
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.IsRealDeltaSetInheritance
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Bornology Classical Finset

namespace robust_projection

/-- Helper: dyadic cubes meeting a finite set form a finite set. -/
lemma finite_dyadicCubesMeeting {δ : ℝ} (hδ : 0 < δ)
    {A : Set (EuclideanSpace ℝ (Fin 1))} (hA : Set.Finite A) :
    Set.Finite (dyadicCubesMeeting δ A) := by
  let f : EuclideanSpace ℝ (Fin 1) → Set (EuclideanSpace ℝ (Fin 1)) :=
    fun x => dyadicCube δ (fun _ : Fin 1 => ⌊x 0 / δ⌋)
  have h1 : ∀ (x : EuclideanSpace ℝ (Fin 1)), x ∈ f x := by
    intro x
    simp only [f, dyadicCube, Set.mem_setOf_eq]
    intro i
    fin_cases i
    have h2 : x 0 ∈ Set.Ico (δ * (⌊x 0 / δ⌋ : ℝ)) (δ * ((⌊x 0 / δ⌋ : ℝ) + 1)) := by
      have h3 : (⌊x 0 / δ⌋ : ℝ) ≤ x 0 / δ := Int.floor_le (x 0 / δ)
      have h4 : x 0 / δ < (⌊x 0 / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one (x 0 / δ)
      have h5 : δ * (⌊x 0 / δ⌋ : ℝ) ≤ x 0 := by
        calc δ * (⌊x 0 / δ⌋ : ℝ) ≤ δ * (x 0 / δ) := by gcongr
          _ = x 0 := by field_simp [hδ.ne'] <;> ring
      have h6 : x 0 < δ * ((⌊x 0 / δ⌋ : ℝ) + 1) := by
        calc x 0 = δ * (x 0 / δ) := by field_simp [hδ.ne'] <;> ring
          _ < δ * ((⌊x 0 / δ⌋ : ℝ) + 1) := by gcongr
      exact ⟨h5, h6⟩
    exact h2
  have h_unique : ∀ (x : EuclideanSpace ℝ (Fin 1)) (k : Fin 1 → ℤ),
      x ∈ dyadicCube δ k → k = (fun _ : Fin 1 => ⌊x 0 / δ⌋) := by
    intro x k hk
    have h2 : x 0 ∈ Set.Ico (δ * (k 0 : ℝ)) (δ * ((k 0 : ℝ) + 1)) := hk 0
    have h3 : (k 0 : ℝ) ≤ x 0 / δ := by
      have h4 : δ * (k 0 : ℝ) ≤ x 0 := h2.1
      calc (k 0 : ℝ) = (δ * (k 0 : ℝ)) / δ := by field_simp [hδ.ne'] <;> ring
        _ ≤ (x 0) / δ := by gcongr
    have h4 : x 0 / δ < (k 0 : ℝ) + 1 := by
      have h5 : x 0 < δ * ((k 0 : ℝ) + 1) := h2.2
      calc x 0 / δ < (δ * ((k 0 : ℝ) + 1)) / δ := by gcongr
        _ = (k 0 : ℝ) + 1 := by field_simp [hδ.ne'] <;> ring
    have h6 : ⌊x 0 / δ⌋ = k 0 := by
      rw [Int.floor_eq_iff]
      exact ⟨h3, h4⟩
    ext i
    fin_cases i
    exact h6.symm
  have h_eq : dyadicCubesMeeting δ A = f '' A := by
    ext Q
    simp only [dyadicCubesMeeting, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hQ_in, ⟨x, hxQ, hxA⟩⟩
      rcases hQ_in with ⟨k, rfl⟩
      have h7 : k = (fun _ : Fin 1 => ⌊x 0 / δ⌋) := h_unique x k hxQ
      refine ⟨x, hxA, ?_⟩
      rw [h7] <;> rfl
    · rintro ⟨x, hxA, rfl⟩
      have h7 : (f x ∩ A).Nonempty := ⟨x, h1 x, hxA⟩
      have h8 : f x ∈ dyadicCubes 1 δ := by
        refine ⟨(fun _ : Fin 1 => ⌊x 0 / δ⌋), rfl⟩
      exact ⟨h8, h7⟩
  rw [h_eq]
  exact hA.image f

/-- Helper: ENat.toENNReal preserves finite sums when all terms are finite. -/
lemma enat_toENNReal_sum {ι : Type*} {s : Finset ι} {f : ι → ENat}
    (hf : ∀ i ∈ s, f i ≠ ⊤) :
    ENat.toENNReal (∑ i ∈ s, f i) = ∑ i ∈ s, ENat.toENNReal (f i) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a t ha ih =>
    have hfa : f a ≠ ⊤ := hf a (Finset.mem_insert_self a t)
    have hft : ∀ i ∈ t, f i ≠ ⊤ := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    rw [ENat.toENNReal_add]
    rw [ih hft]
    <;> rfl

/-- Covering number of finite union ≤ sum of covering numbers. -/
lemma dyadicCoveringNumber_finite_union_le {δ : ℝ} {ι : Type*} {t : Finset ι}
    {A : ι → Set (EuclideanSpace ℝ (Fin 1))} :
    dyadicCoveringNumber δ (⋃ i ∈ t, A i) ≤ ∑ i ∈ t, dyadicCoveringNumber δ (A i) := by
  let f : ι → Set (Set (EuclideanSpace ℝ (Fin 1))) :=
    fun i => dyadicCubesMeeting δ (A i)
  have h1 : dyadicCubesMeeting δ (⋃ i ∈ t, A i) ⊆ ⋃ i ∈ t, f i := by
    intro c hc
    have hc' : c ∈ dyadicCubes 1 δ ∧ (c ∩ (⋃ i ∈ t, A i)).Nonempty := by
      simpa [dyadicCubesMeeting] using hc
    rcases hc' with ⟨hc1, hc2⟩
    rcases hc2 with ⟨x, hx⟩
    have hx_c : x ∈ c := hx.1
    have hx_union : x ∈ (⋃ i ∈ t, A i) := hx.2
    have h_exists : ∃ i ∈ t, x ∈ A i := by
      simpa [Set.mem_biUnion] using hx_union
    rcases h_exists with ⟨i, hi, hxi⟩
    have h3 : (c ∩ A i).Nonempty := by
      have h_in : x ∈ c ∩ A i := by
        exact ⟨hx_c, hxi⟩
      exact ⟨x, h_in⟩
    have h4 : c ∈ f i := by
      have h5 : c ∈ dyadicCubes 1 δ ∧ (c ∩ A i).Nonempty := ⟨hc1, h3⟩
      simpa [f, dyadicCubesMeeting] using h5
    have h_goal : ∃ (j : ι), j ∈ t ∧ c ∈ f j := by
      exact ⟨i, hi, h4⟩
    simpa [Set.mem_biUnion] using h_goal
  have h2 : Set.encard (dyadicCubesMeeting δ (⋃ i ∈ t, A i)) ≤
      Set.encard (⋃ i ∈ t, f i) := Set.encard_mono h1
  have h3 : Set.encard (⋃ i ∈ t, f i) ≤ ∑ i ∈ t, Set.encard (f i) := by
    exact set_encard_biUnion_le t f
  exact le_trans h2 h3

/-- A finite union of real delta-sets is a delta-set with summed constants. -/
lemma union_real_delta_sets
    {δ κ : ℝ} {ι : Type*} (t : Finset ι)
    (S : ι → Finset ℝ) (C : ι → ℝ)
    (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    (hκ_pos : 0 < κ) (hκ_le_one : κ ≤ 1)
    (hC_pos : ∀ i ∈ t, 0 < C i)
    (h_nonempty : (Finset.biUnion t S).Nonempty)
    (h_each : ∀ i ∈ t, IsRealDeltaSet δ κ (C i) ((S i : Set ℝ))) :
    IsRealDeltaSet δ κ (∑ i ∈ t, C i) ((Finset.biUnion t S) : Set ℝ) := by
  let U : Set ℝ := (Finset.biUnion t S : Set ℝ)
  let P : Set (EuclideanSpace ℝ (Fin 1)) := realLineCopy U

  have ht_nonempty : t.Nonempty := by
    by_contra h
    have h' : t = ∅ := by simpa using h
    rw [h'] at h_nonempty
    simp at h_nonempty <;> tauto

  have hC_sum_pos : 0 < ∑ i ∈ t, C i :=
    Finset.sum_pos hC_pos ht_nonempty

  have hU_finite : Set.Finite U := Finset.finite_toSet _

  let e : ℝ → EuclideanSpace ℝ (Fin 1) :=
    fun x => (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => x)

  have h_realLineCopy_image : ∀ (T : Finset ℝ),
      realLineCopy ((T : Set ℝ)) = e '' (T : Set ℝ) := by
    intro T
    ext y
    simp only [realLineCopy, Set.mem_image, e]
    constructor
    · intro hy
      refine ⟨y 0, hy, ?_⟩
      ext i
      fin_cases i <;> rfl
    · rintro ⟨x, hx, rfl⟩
      simpa [e] using hx

  have hP_eq : P = e '' U := by
    ext y
    simp only [P, realLineCopy, Set.mem_image, e]
    constructor
    · intro hy
      refine ⟨y 0, hy, ?_⟩
      ext i
      fin_cases i <;> rfl
    · rintro ⟨x, hx, rfl⟩
      simpa [e] using hx

  have hP_finite : Set.Finite P := by
    rw [hP_eq]
    exact hU_finite.image e
  have hP_bdd : Bornology.IsBounded P := hP_finite.isBounded

  have hP_nonempty : P.Nonempty := by
    rcases h_nonempty with ⟨x, hx⟩
    let p : EuclideanSpace ℝ (Fin 1) := e x
    have hp_in : p ∈ P := by
      rw [hP_eq]
      exact ⟨x, hx, rfl⟩
    exact ⟨p, hp_in⟩

  have h_mono : ∀ {A B : Set (EuclideanSpace ℝ (Fin 1))},
      A ⊆ B → dyadicCoveringNumber δ A ≤ dyadicCoveringNumber δ B :=
    fun {A B} h => dyadic_covering_number_mono h

  have h_nonneg_C : ∀ (i : ι), i ∈ t → 0 ≤ C i :=
    fun i hi => (hC_pos i hi).le

  have h_main_bound : ∀ (r : ℝ) (Q : Set (EuclideanSpace ℝ (Fin 1))),
      r ∈ dyadicScales → Q ∈ dyadicCubes 1 r → δ ≤ r → r ≤ 1 →
      ENat.toENNReal (dyadicCoveringNumber δ (P ∩ Q)) ≤
        ENNReal.ofReal (∑ i ∈ t, C i) * ENat.toENNReal (dyadicCoveringNumber δ P) *
          ENNReal.ofReal (r ^ κ) := by
    intro r Q hr hQ hδr hr1

    let A_i : ι → Set (EuclideanSpace ℝ (Fin 1)) :=
      fun i => realLineCopy ((S i : Set ℝ))

    have h_inter_union : P ∩ Q = ⋃ i ∈ t, (A_i i ∩ Q) := by
      ext x
      simp only [P, A_i, realLineCopy, Set.mem_inter_iff, Set.mem_biUnion]
      <;> constructor <;> intro h <;> aesop

    have h_union_cover : dyadicCoveringNumber δ (P ∩ Q) ≤
        ∑ i ∈ t, dyadicCoveringNumber δ (A_i i ∩ Q) := by
      have h_eq2 : dyadicCoveringNumber δ (P ∩ Q) = dyadicCoveringNumber δ (⋃ i ∈ t, (A_i i ∩ Q)) := by
        apply congr_arg
        exact h_inter_union
      rw [h_eq2]
      exact dyadicCoveringNumber_finite_union_le

    have h_fin_i : ∀ i ∈ t, dyadicCoveringNumber δ (A_i i ∩ Q) ≠ ⊤ := by
      intro i _
      have h1 : Set.Finite (A_i i) := by
        have h_eq : A_i i = realLineCopy ((S i : Set ℝ)) := by rfl
        rw [h_eq]
        rw [h_realLineCopy_image (S i)]
        exact (S i).finite_toSet.image e
      have h_sub : A_i i ∩ Q ⊆ A_i i := by simp
      have h2 : Set.Finite (A_i i ∩ Q) := h1.subset h_sub
      have h3 : Set.Finite (dyadicCubesMeeting δ (A_i i ∩ Q)) :=
        finite_dyadicCubesMeeting hδ h2
      exact h3.encard_lt_top.ne

    have h_mono_i : ∀ i ∈ t, ENat.toENNReal (dyadicCoveringNumber δ (A_i i)) ≤
        ENat.toENNReal (dyadicCoveringNumber δ P) := by
      intro i hi
      have h_sub : A_i i ⊆ P := by
        intro x hx
        have h2 : x 0 ∈ (S i : Set ℝ) := by simpa [A_i, realLineCopy] using hx
        have h3 : x 0 ∈ U := Finset.mem_biUnion.mpr ⟨i, hi, h2⟩
        simpa [P, realLineCopy] using h3
      exact ENat.toENNReal_mono (h_mono h_sub)

    have h_reg_i : ∀ i ∈ t, ENat.toENNReal (dyadicCoveringNumber δ (A_i i ∩ Q)) ≤
        ENNReal.ofReal (C i) * ENat.toENNReal (dyadicCoveringNumber δ (A_i i)) *
          ENNReal.ofReal (r ^ κ) := by
      intro i hi
      have h_i : IsRealDeltaSet δ κ (C i) ((S i : Set ℝ)) := h_each i hi
      rcases h_i with ⟨_, _, _, _, _, _, _, _, h_reg⟩
      exact h_reg hr hQ hδr hr1

    let K : ENNReal := ENat.toENNReal (dyadicCoveringNumber δ P)
    let R : ENNReal := ENNReal.ofReal (r ^ κ)

    have h_step1 : ENat.toENNReal (dyadicCoveringNumber δ (P ∩ Q)) ≤
        ∑ i ∈ t, ENat.toENNReal (dyadicCoveringNumber δ (A_i i ∩ Q)) := by
      calc
        ENat.toENNReal (dyadicCoveringNumber δ (P ∩ Q))
          ≤ ENat.toENNReal (∑ i ∈ t, dyadicCoveringNumber δ (A_i i ∩ Q)) :=
            ENat.toENNReal_mono h_union_cover
        _ = ∑ i ∈ t, ENat.toENNReal (dyadicCoveringNumber δ (A_i i ∩ Q)) :=
            enat_toENNReal_sum h_fin_i

    have h_step2 : ∑ i ∈ t, ENat.toENNReal (dyadicCoveringNumber δ (A_i i ∩ Q)) ≤
        ∑ i ∈ t, (ENNReal.ofReal (C i) * K * R) := by
      apply Finset.sum_le_sum
      intro i hi
      have h5 := h_reg_i i hi
      have h6 : ENNReal.ofReal (C i) * ENat.toENNReal (dyadicCoveringNumber δ (A_i i)) * R ≤
          ENNReal.ofReal (C i) * K * R := by
        have h7 : ENat.toENNReal (dyadicCoveringNumber δ (A_i i)) ≤ K := h_mono_i i hi
        gcongr
      exact le_trans h5 h6

    have h_sum_eq : ∑ i ∈ t, (ENNReal.ofReal (C i) * K * R) =
        (∑ i ∈ t, ENNReal.ofReal (C i)) * K * R := by
      have h10 : ∑ i ∈ t, (ENNReal.ofReal (C i) * K * R) =
          ∑ i ∈ t, (ENNReal.ofReal (C i) * (K * R)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [h10]
      have h11 : ∑ i ∈ t, (ENNReal.ofReal (C i) * (K * R)) =
          (∑ i ∈ t, ENNReal.ofReal (C i)) * (K * R) := by
        exact Eq.symm (sum_mul t (fun i => ENNReal.ofReal (C i)) (K * R))
      rw [h11] <;> ring

    have h_ofReal_sum : (∑ i ∈ t, ENNReal.ofReal (C i)) = ENNReal.ofReal (∑ i ∈ t, C i) :=
      (ENNReal.ofReal_sum_of_nonneg h_nonneg_C).symm

    calc
      ENat.toENNReal (dyadicCoveringNumber δ (P ∩ Q))
        ≤ ∑ i ∈ t, ENat.toENNReal (dyadicCoveringNumber δ (A_i i ∩ Q)) := h_step1
      _ ≤ ∑ i ∈ t, (ENNReal.ofReal (C i) * K * R) := h_step2
      _ = (∑ i ∈ t, ENNReal.ofReal (C i)) * K * R := h_sum_eq
      _ = ENNReal.ofReal (∑ i ∈ t, C i) * K * R := by rw [h_ofReal_sum] <;> ring

  have hκ_nonneg : 0 ≤ κ := by linarith

  refine' ⟨hP_bdd, hP_nonempty, by norm_num, hδ_dyadic, hδ, hκ_nonneg, by simpa using hκ_le_one,
    hC_sum_pos, _⟩
  exact fun ⦃r Q⦄ hr hQ hδr hr1 => h_main_bound r Q hr hQ hδr hr1

end robust_projection
