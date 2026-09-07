module

/-
# Blichfeldt Principle for the Dyadic Lattice (Arbitrary Dimension)

If a measurable set A ⊆ ℝⁿ has volume > N·δⁿ, then A contains N+1
distinct points whose pairwise differences lie in (δℤ)ⁿ.

## Main results

- `blichfeldt_lattice_points_n`: general N-point version in dimension n
- `blichfeldt_two_points_n`: N=1 specialization

## Proof approach

Count function:
- f(x) = #{k : Fin n → ℤ | x + latticePoint δ k ∈ A}
- ∫_F f(x) dx = volume(A)
- If volume(A) > N·δⁿ, some x has f(x) > N

Then transfer from Fin n → ℝ to EuclideanSpace.
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Measure Set Function

namespace BlichfeldtN

variable {n : ℕ}

/-- Fundamental domain [0,δ)ⁿ in `Fin n → ℝ`. -/
def fundamentalDomain (δ : ℝ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ : Fin n => Set.Ico 0 δ)

/-- Lattice point δ·k in `Fin n → ℝ`. -/
def latticePoint (δ : ℝ) (k : Fin n → ℤ) : Fin n → ℝ :=
  fun i => δ * (k i : ℝ)

/-- Dyadic lattice (δℤ)ⁿ in `Fin n → ℝ`. -/
def dyadicLattice (δ : ℝ) : AddSubgroup (Fin n → ℝ) :=
  { carrier := Set.range (latticePoint δ)
    zero_mem' := by
      refine ⟨fun _ => 0, ?_⟩
      ext i; simp [latticePoint]
    add_mem' := by
      rintro p q ⟨k, rfl⟩ ⟨m, rfl⟩
      refine ⟨fun i => k i + m i, ?_⟩
      ext i; simp [latticePoint, mul_add]
    neg_mem' := by
      rintro p ⟨k, rfl⟩
      refine ⟨fun i => -k i, ?_⟩
      ext i; simp [latticePoint] }

/-- Translate set by point. -/
def translateSet {α : Type*} [AddCommGroup α] (s : Set α) (v : α) : Set α :=
  (fun x => x + v) '' s

lemma latticePoint_injective (δ : ℝ) (hδ : 0 < δ) :
    Injective (latticePoint δ (n := n)) := by
  intro k m h
  have h1 : ∀ i, δ * (k i : ℝ) = δ * (m i : ℝ) := by
    intro i; exact congr_fun h i
  have h2 : ∀ i, k i = m i := by
    intro i
    have h3 : (k i : ℝ) = (m i : ℝ) := by
      apply (mul_right_inj' hδ.ne').mp; exact h1 i
    exact_mod_cast h3
  ext i; exact h2 i

section FinNProof

variable {δ : ℝ} (hδ : 0 < δ)

/-- Count lattice translates of x landing in A. -/
noncomputable def countFunction (δ : ℝ) (A : Set (Fin n → ℝ))
    (x : Fin n → ℝ) : ENNReal :=
  ∑' k : Fin n → ℤ, Set.indicator A (fun (_ : Fin n → ℝ) => (1 : ENNReal)) (x + latticePoint δ k)

lemma fundamentalDomain_measurable (δ : ℝ) :
    MeasurableSet (fundamentalDomain (n := n) δ) := by
  exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Ico)

lemma fundamentalDomain_volume (δ : ℝ) (hδ : 0 < δ) :
    volume (fundamentalDomain (n := n) δ) = ENNReal.ofReal (δ^n) := by
  let a : Fin n → ℝ := fun _ => 0
  let b : Fin n → ℝ := fun _ => δ
  have hIoo : Set.univ.pi (fun i : Fin n => Set.Ioo (a i) (b i)) ⊆ fundamentalDomain δ := by
    intro x hx
    have h_x_pi : ∀ i : Fin n, x i ∈ Set.Ioo (a i) (b i) := by
      simpa [Set.mem_univ_pi] using hx
    have h_goal : ∀ i : Fin n, x i ∈ Set.Ico (0 : ℝ) δ := by
      intro i
      have h : x i ∈ Set.Ioo (0 : ℝ) δ := by simpa [a, b] using h_x_pi i
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    simpa [fundamentalDomain, Set.mem_univ_pi] using h_goal
  have hIco_sub : fundamentalDomain δ ⊆ Set.Icc a b := by
    intro x hx
    have h1 : ∀ i : Fin n, a i ≤ x i := by
      intro i
      have h : x i ∈ Set.Ico (0 : ℝ) δ := hx i (by trivial)
      simp [a] <;> linarith [h.1]
    have h2 : ∀ i : Fin n, x i ≤ b i := by
      intro i
      have h : x i ∈ Set.Ico (0 : ℝ) δ := hx i (by trivial)
      simp [b] <;> linarith [h.2]
    exact ⟨h1, h2⟩
  have h_prod : ∏ i : Fin n, ENNReal.ofReal (b i - a i) = ENNReal.ofReal (δ ^ n) := by
    have h1 : ∏ i : Fin n, ENNReal.ofReal (b i - a i) = ∏ i : Fin n, ENNReal.ofReal δ := by
      apply Finset.prod_congr rfl
      intro i _
      simp [a, b] <;> ring
    rw [h1]
    have h2 : ∏ i : Fin n, ENNReal.ofReal δ = (ENNReal.ofReal δ) ^ n := by
      simp [Finset.prod_const]
      <;> ring
    rw [h2]
    have h3 : (ENNReal.ofReal δ) ^ n = ENNReal.ofReal (δ ^ n) := by
      rw [← ENNReal.ofReal_pow hδ.le]
      <;> rfl
    exact h3
  have h_vol_Ioo : volume (Set.univ.pi (fun i : Fin n => Set.Ioo (a i) (b i))) =
      ENNReal.ofReal (δ^n) := by
    rw [Real.volume_pi_Ioo]
    exact h_prod
  have h_vol_Icc : volume (Set.Icc a b) = ENNReal.ofReal (δ^n) := by
    rw [Real.volume_Icc_pi]
    exact h_prod
  have h_mono1 : volume (Set.univ.pi (fun i => Set.Ioo (a i) (b i))) ≤ volume (fundamentalDomain δ) :=
    measure_mono hIoo
  have h_mono2 : volume (fundamentalDomain δ) ≤ volume (Set.Icc a b) :=
    measure_mono hIco_sub
  rw [h_vol_Ioo] at h_mono1
  rw [h_vol_Icc] at h_mono2
  exact le_antisymm h_mono2 h_mono1

/-- Every y decomposes as x + latticePoint δ k with x ∈ F. -/
lemma fundamentalDomain_cover (δ : ℝ) (hδ : 0 < δ) (y : Fin n → ℝ) :
    ∃ (k : Fin n → ℤ), y ∈ translateSet (fundamentalDomain δ) (latticePoint δ k) := by
  let k : Fin n → ℤ := fun i => ⌊y i / δ⌋
  use k
  let x : Fin n → ℝ := fun i => y i - δ * (k i : ℝ)
  have hx : x ∈ fundamentalDomain δ := by
    intro i _
    have hki : (k i : ℝ) = ⌊y i / δ⌋ := by
      simp [k] <;> rfl
    have h21 : 0 ≤ y i / δ - (k i : ℝ) := by
      rw [hki]
      have h : (⌊y i / δ⌋ : ℝ) ≤ y i / δ := Int.floor_le (y i / δ)
      linarith
    have h22 : y i / δ - (k i : ℝ) < 1 := by
      rw [hki]
      have h : y i / δ < (⌊y i / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one (y i / δ)
      linarith
    have h3 : x i = δ * (y i / δ - (k i : ℝ)) := by
      have hdiv : δ * (y i / δ) = y i := by
        field_simp [hδ.ne'] <;> ring
      calc
        x i = y i - δ * (k i : ℝ) := by simp [x]
        _ = δ * (y i / δ) - δ * (k i : ℝ) := by rw [hdiv]
        _ = δ * (y i / δ - (k i : ℝ)) := by rw [mul_sub]
    rw [h3]
    exact ⟨mul_nonneg hδ.le h21, by
      have h : δ * (y i / δ - (k i : ℝ)) < δ := by
        have h' : (y i / δ - (k i : ℝ)) < 1 := h22
        have h'' : δ * (y i / δ - (k i : ℝ)) < δ * 1 := by gcongr
        simpa using h''
      exact h⟩
  have h4 : x + latticePoint δ k = y := by
    ext i
    have h5 : (x + latticePoint δ k) i = y i := by
      simp [x, latticePoint] <;> abel
    exact h5
  exact ⟨x, hx, h4⟩

lemma fundamentalDomain_disjoint (δ : ℝ) (hδ : 0 < δ)
    {k k' : Fin n → ℤ} (h : k ≠ k') :
    Disjoint (translateSet (fundamentalDomain δ) (latticePoint δ k))
      (translateSet (fundamentalDomain δ) (latticePoint δ k')) := by
  rw [Set.disjoint_left]
  intro y hy hy'
  rcases hy with ⟨x, hx, rfl⟩
  rcases hy' with ⟨x', hx', h_eq⟩
  have h_eq2 : x + latticePoint δ k = x' + latticePoint δ k' := h_eq.symm
  have h_diff : ∀ i, x i - x' i = δ * ((k' i : ℝ) - (k i : ℝ)) := by
    intro i
    have h4 : x i + δ * (k i : ℝ) = x' i + δ * (k' i : ℝ) := by
      simpa [latticePoint] using congr_fun h_eq2 i
    linarith
  have h_bounds : ∀ i, x i - x' i ∈ Set.Ioo (-δ) δ := by
    intro i
    have h5 : x i ∈ Set.Ico 0 δ := hx i (by trivial)
    have h6 : x' i ∈ Set.Ico 0 δ := hx' i (by trivial)
    have h51 : 0 ≤ x i := h5.1
    have h52 : x i < δ := h5.2
    have h61 : 0 ≤ x' i := h6.1
    have h62 : x' i < δ := h6.2
    have h7 : -δ < x i - x' i := by linarith
    have h8 : x i - x' i < δ := by linarith
    exact ⟨h7, h8⟩
  have h_int : ∀ i, k' i = k i := by
    intro i
    have h7 : δ * ((k' i : ℝ) - (k i : ℝ)) ∈ Set.Ioo (-δ) δ := by
      rw [← h_diff i]; exact h_bounds i
    have h10 : -1 < (k' i : ℝ) - (k i : ℝ) := by
      have h11 : -δ < δ * ((k' i : ℝ) - (k i : ℝ)) := h7.1
      nlinarith
    have h12 : (k' i : ℝ) - (k i : ℝ) < 1 := by
      have h13 : δ * ((k' i : ℝ) - (k i : ℝ)) < δ := h7.2
      nlinarith
    have h14 : (k' i - k i : ℤ) = 0 := by
      rw [← Int.cast_sub] at *
      <;> norm_cast at * <;> omega
    exact eq_of_sub_eq_zero h14
  have h13 : k' = k := by ext i; exact h_int i
  exact h h13.symm

variable {N : ℕ} {A : Set (Fin n → ℝ)} (hA : MeasurableSet A)

lemma countFunction_integral (δ : ℝ) (hδ : 0 < δ)
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    ∫⁻ x in fundamentalDomain (n := n) δ, countFunction δ A x = volume A := by
  let F := fundamentalDomain (n := n) δ
  let v : (Fin n → ℤ) → (Fin n → ℝ) := latticePoint δ
  let ind : (Fin n → ℝ) → ENNReal := fun _ => (1 : ENNReal)
  have hF_meas : MeasurableSet F := fundamentalDomain_measurable δ

  have h_meas : ∀ k : Fin n → ℤ,
      Measurable (fun x : Fin n → ℝ => Set.indicator A ind (x + v k)) := by
    intro k
    have h1 : Measurable (Set.indicator A ind) :=
      (measurable_const : Measurable ind).indicator hA
    have h2 : Measurable (fun x : Fin n → ℝ => x + v k) :=
      measurable_id.add measurable_const
    exact h1.comp h2

  have h1 : ∫⁻ x in F, countFunction δ A x =
      ∑' k : Fin n → ℤ, ∫⁻ x in F, Set.indicator A ind (x + v k) := by
    have h_expand : countFunction δ A = fun x =>
        ∑' k : Fin n → ℤ, Set.indicator A ind (x + v k) := by
      funext x; rfl
    rw [h_expand]
    have h_meas' : ∀ k, AEMeasurable (fun x : Fin n → ℝ => Set.indicator A ind (x + v k)) (volume.restrict F) :=
      fun k => (h_meas k).aemeasurable
    exact lintegral_tsum h_meas'

  rw [h1]

  have h2 : ∀ k : Fin n → ℤ, ∫⁻ x in F, Set.indicator A ind (x + v k) =
      volume (A ∩ translateSet F (v k)) := by
    intro k
    let f : (Fin n → ℝ) → (Fin n → ℝ) := fun x => x + v k
    let g : (Fin n → ℝ) → (Fin n → ℝ) := fun y => y - v k
    let S_full : Set (Fin n → ℝ) := f ⁻¹' A
    have h_f_meas : Measurable f := measurable_id.add measurable_const
    have hS_full_meas : MeasurableSet S_full := hA.preimage h_f_meas
    let S : Set (Fin n → ℝ) := F ∩ S_full
    have hS_meas : MeasurableSet S := hF_meas.inter hS_full_meas

    have h_eq_indicator : (fun x : Fin n → ℝ => Set.indicator A ind (f x)) = Set.indicator S_full ind := by
      funext x
      simp [S_full, Set.indicator, ind]
      <;> rfl

    have h_int : ∫⁻ x in F, Set.indicator A ind (f x) = volume S := by
      rw [h_eq_indicator]
      have h1 : ∫⁻ x in F, Set.indicator S_full ind x = volume (F ∩ S_full) := by
        rw [setLIntegral_indicator hS_full_meas ind]
        have h_comm : S_full ∩ F = F ∩ S_full := by rw [Set.inter_comm]
        rw [h_comm]
        have h_ind_const : ind = fun (_ : Fin n → ℝ) => (1 : ENNReal) := by funext y; simp [ind]
        rw [h_ind_const]
        rw [setLIntegral_const (F ∩ S_full) (1 : ENNReal)]
        <;> simp
      rw [h1]

    have h_mp_g : MeasurePreserving g volume volume :=
      measurePreserving_sub_right volume (v k)

    have h_fg_inverse : ∀ x, g (f x) = x := by
      intro x; simp [f, g] <;> abel
    have h_gf_inverse : ∀ y, f (g y) = y := by
      intro y; simp [f, g] <;> abel

    have h_image1 : f '' S = A ∩ translateSet F (v k) := by
      ext z
      simp only [S, S_full, translateSet, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨x, ⟨hxF, hxfA⟩, rfl⟩
        exact ⟨hxfA, ⟨x, hxF, rfl⟩⟩
      · rintro ⟨hzA, ⟨x, hxF, rfl⟩⟩
        exact ⟨x, ⟨hxF, hzA⟩, rfl⟩

    have h_image2 : f '' S = g ⁻¹' S := by
      ext z
      simp only [S, Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hxS, rfl⟩
        have h4 : g (f x) = x := h_fg_inverse x
        rw [h4]
        exact hxS
      · intro hz
        refine ⟨g z, hz, ?_⟩
        exact h_gf_inverse z

    have h_vol : volume (f '' S) = volume S := by
      rw [h_image2]
      exact h_mp_g.measure_preimage hS_meas.nullMeasurableSet

    rw [h_int, ←h_vol, h_image1]

  rw [tsum_congr h2]

  have h_univ : (⋃ k : Fin n → ℤ, translateSet F (v k)) = Set.univ := by
    apply Set.eq_univ_of_forall; intro y
    rcases fundamentalDomain_cover δ hδ y with ⟨k, hk⟩
    exact Set.mem_iUnion.mpr ⟨k, hk⟩

  have h_disj : Set.Pairwise (Set.univ : Set (Fin n → ℤ))
      (fun k k' => Disjoint (translateSet F (v k)) (translateSet F (v k'))) := by
    intro k _ k' _ hne
    exact fundamentalDomain_disjoint δ hδ hne

  have h_disj2 : Set.Pairwise (Set.univ : Set (Fin n → ℤ))
      (fun k k' => Disjoint (A ∩ translateSet F (v k)) (A ∩ translateSet F (v k'))) := by
    intro k _ k' _ hne
    have h : Disjoint (translateSet F (v k)) (translateSet F (v k')) :=
      h_disj (by simp) (by simp) hne
    rw [Set.disjoint_left] at h ⊢
    intro x hx1 hx2
    have hx3 : x ∈ translateSet F (v k) := hx1.2
    have hx4 : x ∈ translateSet F (v k') := hx2.2
    exact h hx3 hx4

  have hFk_meas : ∀ k, MeasurableSet (translateSet F (v k)) := by
    intro k
    let g : (Fin n → ℝ) → (Fin n → ℝ) := fun y => y - v k
    have hg : Measurable g := measurable_id.sub measurable_const
    have h_eq : translateSet F (v k) = g ⁻¹' F := by
      ext z
      simp only [translateSet, Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa [g] using hx
      · intro hz
        refine ⟨g z, hz, ?_⟩
        simp [g] <;> abel
    rw [h_eq]
    exact hF_meas.preimage hg

  let s : (Fin n → ℤ) → Set (Fin n → ℝ) := fun k => A ∩ translateSet F (v k)
  have hms : ∀ k, MeasurableSet (s k) := fun k => hA.inter (hFk_meas k)
  have hpd : Pairwise (fun i j : Fin n → ℤ => Disjoint (s i) (s j)) := by
    intro i j hne
    exact h_disj2 (by simp) (by simp) hne
  have h_eq1 : (⋃ k, s k) = A := by
    have h5 : (⋃ k, s k) = A ∩ (⋃ k, translateSet F (v k)) := by
      rw [Set.inter_iUnion] <;> rfl
    rw [h5, h_univ] <;> simp
  have h_partition : volume (⋃ k, s k) = ∑' k, volume (s k) :=
    measure_iUnion hpd hms
  have h_final : ∑' k, volume (A ∩ translateSet F (v k)) = volume A := by
    have h6 : ∑' k, volume (s k) = ∑' k, volume (A ∩ translateSet F (v k)) := by
      congr with k <;> rfl
    rw [←h6, ←h_partition, h_eq1]
  exact h_final

/-- Blichfeldt for Fin n → ℝ. -/
theorem blichfeldt_fin (δ : ℝ) (hδ : 0 < δ) {N : ℕ}
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A)
    (h : ENNReal.ofReal ((N : ℝ) * δ^n) < volume A) :
    ∃ (x : Fin n → ℝ) (ks : Fin (N + 1) → (Fin n → ℤ)),
      (∀ i, x + latticePoint δ (ks i) ∈ A) ∧
      (∀ i j, i ≠ j → ks i ≠ ks j) := by
  let F := fundamentalDomain (n := n) δ
  let f := countFunction δ A
  let ind : (Fin n → ℝ) → ENNReal := fun _ => (1 : ENNReal)
  have h_integral : ∫⁻ x in F, f x = volume A :=
    countFunction_integral δ hδ hA
  by_cases h_contra : (∀ x ∈ F, f x ≤ (N : ENNReal))
  · have h_bound : ∫⁻ x in F, f x ≤ (N : ENNReal) * volume F := by
      have h_indicator_bound2 : ∀ (x : Fin n → ℝ),
          Set.indicator F f x ≤ Set.indicator F (fun _ => (N : ENNReal)) x := by
        intro x
        by_cases hx : x ∈ F
        · simpa [Set.indicator, hx] using h_contra x hx
        · simp [Set.indicator, hx]
      have h_eq : ∫⁻ x in F, f x = ∫⁻ x, Set.indicator F f x :=
        (lintegral_indicator (fundamentalDomain_measurable δ) f).symm
      rw [h_eq]
      have h : ∫⁻ x, Set.indicator F f x ≤ ∫⁻ x, Set.indicator F (fun _ => (N : ENNReal)) x :=
        lintegral_mono h_indicator_bound2
      have h_eq2 : ∫⁻ x, Set.indicator F (fun _ => (N : ENNReal)) x = ∫⁻ x in F, (N : ENNReal) := by
        rw [lintegral_indicator (fundamentalDomain_measurable δ)]
        <;> rfl
      rw [h_eq2] at h
      have h_const : ∫⁻ x in F, (N : ENNReal) = (N : ENNReal) * volume F :=
        setLIntegral_const F (N : ENNReal)
      rw [h_const] at h
      exact h
    rw [h_integral, fundamentalDomain_volume δ hδ] at h_bound
    have h7 : (N : ENNReal) * ENNReal.ofReal (δ ^ n) =
        ENNReal.ofReal ((N : ℝ) * δ^n) := by
      rw [ENNReal.ofReal_mul (by positivity)] <;> norm_cast
    rw [h7] at h_bound
    exact False.elim (not_le.mpr h h_bound)
  · push Not at h_contra
    rcases h_contra with ⟨x, hxF, h_gt⟩
    let S : Set (Fin n → ℤ) := {k | x + latticePoint δ k ∈ A}
    have hS_def : ∀ k, k ∈ S ↔ x + latticePoint δ k ∈ A := by
      intro k; simp [S]
    have h_fx_def : f x = ∑' k : Fin n → ℤ, Set.indicator S (fun (_ : Fin n → ℤ) => (1 : ENNReal)) k := by
      simp [f, countFunction, hS_def] <;> rfl
    rw [h_fx_def] at h_gt

    have h_exists : ∃ (T : Finset (Fin n → ℤ)), (T : Set (Fin n → ℤ)) ⊆ S ∧ T.card = N + 1 := by
      by_cases hfin : S.Finite
      · let S' := hfin.toFinset
        have hS' : (S' : Set (Fin n → ℤ)) = S := hfin.coe_toFinset
        have h_ind_eq : Set.indicator S (fun (_ : Fin n → ℤ) => (1 : ENNReal)) =
            Set.indicator (↑S') (fun (_ : Fin n → ℤ) => (1 : ENNReal)) := by
          congr 1 <;> exact hS'.symm
        have h_sum : (∑' k : Fin n → ℤ, Set.indicator S (fun (_ : Fin n → ℤ) => (1 : ENNReal)) k) =
            (S'.card : ENNReal) := by
          rw [h_ind_eq]
          rw [tsum_eq_sum (s := S')]
          · have h_sum2 : ∑ k ∈ S', Set.indicator (↑S') (fun (_ : Fin n → ℤ) => (1 : ENNReal)) k =
                ∑ k ∈ S', (1 : ENNReal) := by
              apply Finset.sum_congr rfl
              intro k hk
              simp [Set.indicator, hk]
            rw [h_sum2]
            simp
          · intro k hk
            simp [Set.indicator, hk]
        rw [h_sum] at h_gt
        have h_gt2 : (S'.card : ENNReal) > (N : ENNReal) := h_gt
        have h_card_gt : N < S'.card := by exact_mod_cast h_gt2
        have h_card_ge : N + 1 ≤ S'.card := by omega
        rcases Finset.exists_subset_card_eq h_card_ge with ⟨T, hT_sub', hT_card⟩
        have hT_sub : (T : Set _) ⊆ S := by
          intro x hx
          have hx' : x ∈ T := by exact_mod_cast hx
          have h_in_S' : x ∈ S' := hT_sub' hx'
          have h_coe : x ∈ (S' : Set _) := by exact_mod_cast h_in_S'
          rw [hS'] at h_coe
          exact h_coe
        exact ⟨T, hT_sub, hT_card⟩
      · have hinf : Set.Infinite S := by
          intro h
          exact hfin h
        exact hinf.exists_subset_card_eq (N + 1)
    rcases h_exists with ⟨T, hT_sub, hT_card⟩
    have h_le : N + 1 ≤ T.card := by
      rw [hT_card] <;> omega
    let e' : Fin T.card ≃ {z : Fin n → ℤ // z ∈ T} := (Finset.equivFin T).symm
    let ks : Fin (N + 1) → (Fin n → ℤ) := fun i =>
      (e' (Fin.castLE h_le i)).val
    have h1 : ∀ i, x + latticePoint δ (ks i) ∈ A := by
      intro i
      have h2 : ks i ∈ S := hT_sub (e' (Fin.castLE h_le i)).property
      exact (hS_def (ks i)).mp h2
    have h3 : ∀ i j, i ≠ j → ks i ≠ ks j := by
      intro i j hne
      intro h_eq
      have h4 : (e' (Fin.castLE h_le i)) = (e' (Fin.castLE h_le j)) := by
        apply Subtype.ext
        simpa [ks] using h_eq
      have h5 : Fin.castLE h_le i = Fin.castLE h_le j := e'.injective h4
      have h6 : i = j := (Fin.castLE_injective h_le) h5
      exact hne h6
    exact ⟨x, ks, h1, h3⟩

end FinNProof

section EuclideanSpace

variable {δ : ℝ} (hδ : 0 < δ)

/-- Dyadic lattice in EuclideanSpace ℝ (Fin n). -/
noncomputable def euclideanDyadicLattice (δ : ℝ) :
    AddSubgroup (EuclideanSpace ℝ (Fin n)) :=
  { carrier := {p | (EuclideanSpace.equiv (Fin n) ℝ) p ∈ dyadicLattice δ}
    zero_mem' := by
      simp only [Set.mem_setOf_eq]
      exact ⟨fun _ => 0, by ext i; simp [latticePoint]⟩
    add_mem' := by
      intro p q hp hq
      have h : (EuclideanSpace.equiv (Fin n) ℝ) (p + q) =
          (EuclideanSpace.equiv (Fin n) ℝ) p + (EuclideanSpace.equiv (Fin n) ℝ) q :=
        map_add (EuclideanSpace.equiv (Fin n) ℝ) p q
      simp only [Set.mem_setOf_eq] at *
      rw [h]
      exact (dyadicLattice δ).add_mem hp hq
    neg_mem' := by
      intro p hp
      have h : (EuclideanSpace.equiv (Fin n) ℝ) (-p) =
          -(EuclideanSpace.equiv (Fin n) ℝ) p :=
        map_neg (EuclideanSpace.equiv (Fin n) ℝ) p
      simp only [Set.mem_setOf_eq] at *
      rw [h]
      exact (dyadicLattice δ).neg_mem hp }

/-- Lattice point in EuclideanSpace. -/
noncomputable def euclideanLatticePoint (δ : ℝ) (k : Fin n → ℤ) :
    EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (latticePoint δ k)

/-- **Blichfeldt's principle** for the dyadic lattice (δℤ)ⁿ.

If A ⊆ ℝⁿ is measurable with volume > N·δⁿ, then there exist N+1
distinct points in A whose pairwise differences lie in (δℤ)ⁿ. -/
theorem blichfeldt_lattice_points_n {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {N : ℕ}
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    (h : ENNReal.ofReal ((N : ℝ) * δ^n) < volume A) :
    ∃ (x : Fin (N + 1) → EuclideanSpace ℝ (Fin n)),
      Function.Injective x ∧ (∀ i, x i ∈ A) ∧
      (∀ i j, x i - x j ∈ euclideanDyadicLattice (n := n) δ) := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (Fin n) ℝ
  have h_meas_e : Measurable e := e.continuous.measurable
  have h_meas_e_symm : Measurable e.symm := e.symm.continuous.measurable
  let me : EuclideanSpace ℝ (Fin n) ≃ᵐ (Fin n → ℝ) :=
    ⟨e.toEquiv, h_meas_e, h_meas_e_symm⟩
  let A' : Set (Fin n → ℝ) := e '' A
  have hA'_meas : MeasurableSet A' := by
    have h : MeasurableSet (me '' A) := me.measurableSet_image.mpr hA
    have h_eq : (me '' A) = A' := by rfl
    rw [h_eq] at h
    exact h
  have h_mp : MeasurePreserving e volume volume := by
    convert PiLp.volume_preserving_ofLp (ι := Fin n) <;> rfl
  have h_map : Measure.map e volume = volume := by
    exact h_mp.map_eq
  have h_vol : volume A' = volume A := by
    have h5 : Measure.map e volume A' = volume (e ⁻¹' A') :=
      Measure.map_apply h_meas_e hA'_meas
    have h6 : e ⁻¹' A' = A := by
      ext x
      simp [A', e]
      <;> constructor <;> intro h <;> tauto
    rw [h_map] at h5
    rw [h6] at h5
    exact h5
  have h' : ENNReal.ofReal ((N : ℝ) * δ^n) < volume A' := by
    rw [h_vol]; exact h
  rcases blichfeldt_fin (n := n) δ hδ hA'_meas h' with ⟨x, ks, h1, h2⟩
  let x' : Fin (N + 1) → EuclideanSpace ℝ (Fin n) := fun i =>
    e.symm (x + latticePoint δ (ks i))
  have hx_in_A : ∀ i, x' i ∈ A := by
    intro i
    have h3 : x + latticePoint δ (ks i) ∈ A' := h1 i
    rcases h3 with ⟨z, hz, h_eq⟩
    have h4 : e (x' i) = e z := by
      have h5 : e (x' i) = x + latticePoint δ (ks i) := by simp [x'] <;> rfl
      rw [h5, h_eq]
    have h6 : x' i = z := e.injective h4
    rw [h6]; exact hz
  have hx_inj : Function.Injective x' := by
    intro i j h
    have h5 : e (x' i) = e (x' j) := by rw [h]
    have h6 : x + latticePoint δ (ks i) = x + latticePoint δ (ks j) := by
      simpa [x'] using h5
    have h7 : latticePoint δ (ks i) = latticePoint δ (ks j) := by simpa using h6
    have h8 : ks i = ks j := latticePoint_injective δ hδ h7
    have h9 : i = j := by
      by_contra h10; exact h2 i j h10 h8
    exact h9
  have hx_lattice : ∀ i j, x' i - x' j ∈ euclideanDyadicLattice (n := n) δ := by
    intro i j
    have h5 : e (x' i - x' j) = e (x' i) - e (x' j) :=
      e.map_sub (x' i) (x' j)
    have h6 : e (x' i) - e (x' j) = latticePoint δ (ks i) - latticePoint δ (ks j) := by
      simp [x'] <;> abel
    have h7 : e (x' i - x' j) = latticePoint δ (ks i) - latticePoint δ (ks j) := by
      rw [h5, h6]
    have h8 : latticePoint δ (ks i) - latticePoint δ (ks j) ∈ dyadicLattice δ := by
      exact (dyadicLattice δ).sub_mem ⟨ks i, rfl⟩ ⟨ks j, rfl⟩
    have h9 : e (x' i - x' j) ∈ dyadicLattice δ := by
      rw [h7]; exact h8
    have h10 : x' i - x' j ∈ euclideanDyadicLattice (n := n) δ := by
      have h_def : (x' i - x' j) ∈ euclideanDyadicLattice (n := n) δ ↔
          e (x' i - x' j) ∈ dyadicLattice δ := by
        simp [euclideanDyadicLattice, e, Set.mem_setOf_eq]
      exact h_def.mpr h9
    exact h10
  exact ⟨x', hx_inj, hx_in_A, hx_lattice⟩

/-- Specialization: if volume(A) > δⁿ, there are two distinct points in A
    whose difference is a nonzero dyadic lattice point. -/
theorem blichfeldt_two_points_n {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    (h : ENNReal.ofReal (δ^n) < volume A) :
    ∃ (x y : EuclideanSpace ℝ (Fin n)),
      x ∈ A ∧ y ∈ A ∧ x ≠ y ∧
      x - y ∈ euclideanDyadicLattice (n := n) δ ∧ x - y ≠ 0 := by
  have h' : ENNReal.ofReal (((1 : ℕ) : ℝ) * δ^n) < volume A := by
    simpa using h
  have h_main := blichfeldt_lattice_points_n (n := n) hδ hA (N := 1) h'
  rcases h_main with ⟨x, hx_inj, hx_A, hx_lat⟩
  let x0 := x 0; let x1 := x 1
  have hne : x0 ≠ x1 := by
    intro h; have h' : (0 : Fin 2) = 1 := hx_inj h; simp at h'
  have hnz : x0 - x1 ≠ 0 := by
    intro h
    have h' : x0 = x1 := sub_eq_zero.mp h
    exact hne h'
  exact ⟨x0, x1, hx_A 0, hx_A 1, hne, hx_lat 0 1, hnz⟩

end EuclideanSpace

end BlichfeldtN
