/-
# Convex hull utilities

Utility lemmas about convex hulls in finite-dimensional real vector spaces,
needed for the Löwner–John ellipsoid theorem.

## Main results

* `mem_convexHull_finite`: Carathéodory's theorem with explicit weights.
* `convexHull_compact`: the convex hull of a compact set is compact.
* `convex_combination_finite`: a finite convex combination lies in the convex hull.
* `convexHull_graph_decomp`: extracting component-wise convex combinations from
  membership in the convex hull of a graph `{(u, f u) | u ∈ S}`.
* `weighted_sum_in_convex`: a weighted sum with nonnegative coefficients summing
  to one lies in any convex set containing the points.
-/

import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.MinkowskiCaratheodory
import Mathlib.Analysis.Convex.StdSimplex

noncomputable section

open Set Finset

namespace JohnEllipsoid.ConvexHullUtils

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open JohnEllipsoid.MinkowskiCaratheodory.CaratheodoryFinite

/-- **Carathéodory's theorem** (explicit weights form): if `x ∈ convexHull ℝ S`,
there exists a finite subset `t ⊆ S` of cardinality at most `finrank ℝ E + 1`
and weights `w : E → ℝ` nonnegative on `t`, summing to `1` on `t`, such that
`x = ∑ y ∈ t, w y • y`. -/
theorem mem_convexHull_finite {S : Set E} {x : E}
    (hx : x ∈ convexHull ℝ S) :
    ∃ (t : Finset E), (↑t : Set E) ⊆ S ∧ t.card ≤ Module.finrank ℝ E + 1 ∧
      ∃ (w : E → ℝ), (∀ y ∈ t, 0 ≤ w y) ∧ ∑ y ∈ t, w y = 1 ∧ ∑ y ∈ t, w y • y = x := by
  have h_main : ∃ (t : Finset E), (↑t : Set E) ⊆ S ∧ t.card ≤ Module.finrank ℝ E + 1 ∧ x ∈ convexHull ℝ (↑t : Set E) :=
    caratheodory_finite_convexHull hx
  rcases h_main with ⟨t, htS, htcard, hxt⟩
  rw [Finset.mem_convexHull] at hxt
  rcases hxt with ⟨w, hw₀, hw₁, hxw⟩
  have hsum : ∑ y ∈ t, w y • y = x := by
    have h : t.centerMass w id = ∑ y ∈ t, w y • y := by
      rw [Finset.centerMass_eq_of_sum_1 _ id hw₁] <;> rfl
    rw [h] at hxw
    exact hxw
  exact ⟨t, htS, htcard, w, hw₀, hw₁, hsum⟩

-- Helper: extend a convex combination from m points to k points (k ≥ m)
private lemma extend_convex_combination {E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} {t : Finset E} {w : E → ℝ} {k m : ℕ} (hm_le_k : m ≤ k)
    (ht_card : t.card = m) (htS : (↑t : Set E) ⊆ S) (hw₀ : ∀ y ∈ t, 0 ≤ w y)
    (y₀ : E) (hy₀ : y₀ ∈ S) :
    ∃ (z : Fin k → E) (w' : Fin k → ℝ),
      (∀ i, z i ∈ S) ∧ (∀ i, 0 ≤ w' i) ∧
      (∑ i : Fin k, w' i = ∑ y ∈ t, w y) ∧
      (∑ i : Fin k, w' i • z i = ∑ y ∈ t, w y • y) := by
  let e0 : {y // y ∈ t} ≃ Fin t.card := Finset.equivFin t
  let e1 : Fin t.card ≃ Fin m := finCongr ht_card
  let e : {y // y ∈ t} ≃ Fin m := e0.trans e1
  let e' : Fin m ≃ {y // y ∈ t} := e.symm
  let g : Fin m → Fin k := fun j => ⟨j.val, by omega⟩
  have hg_inj : Function.Injective g := by
    intro a b h
    simpa [g, Fin.ext_iff] using h
  let s : Finset (Fin k) := Finset.filter (fun j => j.val < m) Finset.univ
  have hs_eq : s = Finset.image g Finset.univ := by
    ext j
    simp only [s, g, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      let i : Fin m := ⟨j.val, h⟩
      have hgi : g i = j := by
        simp [g, i, Fin.ext_iff] <;> rfl
      exact ⟨i, hgi⟩
    · rintro ⟨i, _, rfl⟩
      exact i.is_lt
  let z : Fin k → E := fun j =>
    if h : j.val < m then (e' ⟨j.val, h⟩ : E) else y₀
  let w' : Fin k → ℝ := fun j =>
    if h : j.val < m then w (e' ⟨j.val, h⟩) else 0
  have hzS : ∀ i, z i ∈ S := by
    intro i
    by_cases h : i.val < m
    · have h4 : (e' ⟨i.val, h⟩ : E) ∈ t := (e' ⟨i.val, h⟩).property
      have h5 : z i = (e' ⟨i.val, h⟩ : E) := by
        simp [z, h] <;> rfl
      rw [h5] <;> exact htS h4
    · have h6 : z i = y₀ := by simp [z, h] <;> omega
      rw [h6] <;> exact hy₀
  have hw'₀ : ∀ i, 0 ≤ w' i := by
    intro i
    by_cases h : i.val < m
    · have h4 : (e' ⟨i.val, h⟩ : E) ∈ t := (e' ⟨i.val, h⟩).property
      have h5 : w' i = w (e' ⟨i.val, h⟩ : E) := by simp [w', h] <;> rfl
      rw [h5] <;> exact hw₀ (e' ⟨i.val, h⟩) h4
    · have h6 : w' i = 0 := by simp [w', h] <;> omega
      rw [h6] <;> linarith
  have h_w'_g : ∀ j : Fin m, w' (g j) = w (e' j : E) := by
    intro j
    have h_val : (g j).val < m := j.is_lt
    simp [w', g, h_val] <;> rfl
  have h_z_g : ∀ j : Fin m, z (g j) = (e' j : E) := by
    intro j
    have h_val : (g j).val < m := j.is_lt
    simp [z, g, h_val] <;> rfl
  have h_inj_on : Set.InjOn g (Finset.univ : Finset (Fin m)) := fun _ _ _ _ h => hg_inj h
  have h_sum_s : ∑ i ∈ s, w' i = ∑ j : Fin m, w (e' j : E) := by
    rw [hs_eq, Finset.sum_image h_inj_on]
    apply Finset.sum_congr rfl
    intro j _
    exact h_w'_g j
  have h_sum_compl : ∑ i ∈ (Finset.univ \ s), w' i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have h_i_notin_s : i ∉ s := (Finset.mem_sdiff.mp hi).2
    have h_i_val_ge_m : ¬(i.val < m) := by
      simpa [s, Finset.mem_filter] using h_i_notin_s
    have h7 : w' i = 0 := by simp [w', h_i_val_ge_m] <;> omega
    rw [h7]
  have h_disj : Disjoint s (Finset.univ \ s) := Finset.disjoint_sdiff
  have h_univ : s ∪ (Finset.univ \ s) = Finset.univ := by simp
  have h_sum_w' : ∑ i : Fin k, w' i = ∑ i ∈ s, w' i := by
    have h : ∑ i : Fin k, w' i = ∑ i ∈ (s ∪ (Finset.univ \ s)), w' i := by rw [h_univ]
    rw [h, Finset.sum_union h_disj, h_sum_compl, add_zero]
  have h4 : ∑ j : Fin m, w (e' j : E) = ∑ y : {y // y ∈ t}, w (y : E) := by
    have h6 := Fintype.sum_equiv e' (fun j : Fin m => w (e' j : E))
    exact h6 (fun y : {y // y ∈ t} => w (y : E)) (fun _ => rfl)
  have h51 : (Finset.univ : Finset {y // y ∈ t}) = t.attach := by
    ext x <;> simp
  have h5 : ∑ y : {y // y ∈ t}, w (y : E) = ∑ y ∈ t, w y := by
    rw [h51]
    exact Finset.sum_attach t (fun y : E => w y)
  have h_sum_w'_total : ∑ i : Fin k, w' i = ∑ y ∈ t, w y := by
    rw [h_sum_w', h_sum_s, h4, h5]
  have h_sum_s2 : ∑ i ∈ s, w' i • z i = ∑ j : Fin m, w (e' j : E) • (e' j : E) := by
    rw [hs_eq, Finset.sum_image h_inj_on]
    apply Finset.sum_congr rfl
    intro j _
    rw [h_w'_g j, h_z_g j]
  have h_sum_compl2 : ∑ i ∈ (Finset.univ \ s), w' i • z i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have h_i_notin_s : i ∉ s := (Finset.mem_sdiff.mp hi).2
    have h_i_val_ge_m : ¬(i.val < m) := by
      simpa [s, Finset.mem_filter] using h_i_notin_s
    have h7 : w' i = 0 := by simp [w', h_i_val_ge_m] <;> omega
    rw [h7, zero_smul]
  have h_sum2 : ∑ i : Fin k, w' i • z i = ∑ i ∈ s, w' i • z i := by
    have h : ∑ i : Fin k, w' i • z i = ∑ i ∈ (s ∪ (Finset.univ \ s)), w' i • z i := by rw [h_univ]
    rw [h, Finset.sum_union h_disj, h_sum_compl2, add_zero]
  have h6 : ∑ j : Fin m, w (e' j : E) • (e' j : E) = ∑ y : {y // y ∈ t}, w (y : E) • (y : E) := by
    have h7 := Fintype.sum_equiv e' (fun j : Fin m => w (e' j : E) • (e' j : E))
    exact h7 (fun y : {y // y ∈ t} => w (y : E) • (y : E)) (fun _ => rfl)
  have h8 : ∑ y : {y // y ∈ t}, w (y : E) • (y : E) = ∑ y ∈ t, w y • y := by
    rw [h51]
    exact Finset.sum_attach t (fun y : E => w y • y)
  have h_sum2_total : ∑ i : Fin k, w' i • z i = ∑ y ∈ t, w y • y := by
    rw [h_sum2, h_sum_s2, h6, h8]
  exact ⟨z, w', hzS, hw'₀, h_sum_w'_total, h_sum2_total⟩

/-- The convex hull of a compact set in a finite-dimensional real normed space
is compact. -/
theorem convexHull_compact {S : Set E} (hS : IsCompact S) :
    IsCompact (convexHull ℝ S) := by
  by_cases hSempty : S = ∅
  · rw [hSempty]
    simpa using isCompact_empty
  · have hSnonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hSempty
    obtain ⟨y₀, hy₀⟩ := hSnonempty
    let k : ℕ := Module.finrank ℝ E + 1
    let D : Set ((Fin k → E) × (Fin k → ℝ)) :=
      (Set.univ.pi (fun (_ : Fin k) => S)) ×ˢ stdSimplex ℝ (Fin k)
    let f : ((Fin k → E) × (Fin k → ℝ)) → E :=
      fun p => ∑ i : Fin k, p.2 i • p.1 i
    have hD_compact : IsCompact D := by
      apply IsCompact.prod
      · exact isCompact_univ_pi (fun _ => hS)
      · exact isCompact_stdSimplex ℝ (Fin k)
    have hf_cont : Continuous f := by fun_prop
    have h_image_compact : IsCompact (f '' D) := hD_compact.image hf_cont
    have h_main : convexHull ℝ S = f '' D := by
      apply Set.Subset.antisymm
      · -- convexHull ℝ S ⊆ f '' D
        intro x hx
        rcases mem_convexHull_finite hx with ⟨t, htS, htcard, w, hw₀, hw₁, hxeq⟩
        let m : ℕ := t.card
        have hm_le_k : m ≤ k := htcard
        rcases extend_convex_combination hm_le_k rfl htS hw₀ y₀ hy₀ with ⟨z, w', hzS, hw'₀, h_sum_w', h_sum2⟩
        have h_sum_w'_one : ∑ i : Fin k, w' i = 1 := by
          rw [h_sum_w', hw₁]
        have h_sum2_x : ∑ i : Fin k, w' i • z i = x := by
          rw [h_sum2, hxeq]
        have h_w'_simplex : w' ∈ stdSimplex ℝ (Fin k) := ⟨hw'₀, h_sum_w'_one⟩
        have hz_pi : z ∈ Set.univ.pi (fun (_ : Fin k) => S) := by simpa using hzS
        have h_pair : (z, w') ∈ D := ⟨hz_pi, h_w'_simplex⟩
        have h3 : f (z, w') = x := h_sum2_x
        exact ⟨(z, w'), h_pair, h3⟩
      · -- f '' D ⊆ convexHull ℝ S
        intro x hx
        rcases hx with ⟨p, hp, rfl⟩
        let z : Fin k → E := p.1
        let w : Fin k → ℝ := p.2
        have hzS : ∀ i, z i ∈ S := by
          have h : z ∈ Set.univ.pi (fun (_ : Fin k) => S) := hp.1
          simpa using h
        have hw₀ : ∀ i, 0 ≤ w i := hp.2.1
        have hw₁ : ∑ i : Fin k, w i = 1 := hp.2.2
        exact mem_convexHull_of_exists_fintype w z hw₀ hw₁ hzS rfl
    rw [h_main]
    exact h_image_compact

-- Helper: sum over a finset where only one element may be nonzero
private lemma sum_eq_single' {α β : Type*} [DecidableEq α] [AddCommMonoid β] {s : Finset α} {a : α} {f : α → β}
    (ha : a ∈ s) (h : ∀ b ∈ s, b ≠ a → f b = 0) : ∑ i ∈ s, f i = f a := by
  have h9 : s = insert a (s.erase a) := by rw [Finset.insert_erase ha]
  rw [h9]
  have h_notin : a ∉ s.erase a := by
    intro h10
    exact (Finset.mem_erase.mp h10).1 rfl
  rw [Finset.sum_insert h_notin]
  have h10 : ∑ x ∈ s.erase a, f x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have h11 : x ∈ s := Finset.mem_of_mem_erase hx
    have h12 : x ≠ a := (Finset.mem_erase.mp hx).1
    exact h x h11 h12
  rw [h10, add_zero]

/-- A finite convex combination of points in `S` lies in `convexHull ℝ S`. -/
theorem convex_combination_finite {E' : Type*} [AddCommGroup E'] [Module ℝ E']
    {S : Set E'} {ι : Type*} [Fintype ι] {w : ι → ℝ} {z : ι → E'}
    (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1) (hz : ∀ i, z i ∈ S) :
    ∑ i, w i • z i ∈ convexHull ℝ S :=
  mem_convexHull_of_exists_fintype w z hw₀ hw₁ hz rfl

/-- If `(y, z)` belongs to the convex hull of the graph
`{(u, f u) | u ∈ S}`, then there exist a finite subset `t ⊆ S` and weights
`w : E → ℝ` nonnegative on `t`, summing to `1` on `t`, such that
`y = ∑ x ∈ t, w x • x` and `z = ∑ x ∈ t, w x • f x`. -/
theorem convexHull_graph_decomp {E' F : Type*} [AddCommGroup E'] [Module ℝ E']
    [AddCommGroup F] [Module ℝ F] [DecidableEq E']
    {S : Set E'} {f : E' → F} {y : E'} {z : F}
    (h : (y, z) ∈ convexHull ℝ ((fun u : E' => (u, f u)) '' S)) :
    ∃ (t : Finset E') (w : E' → ℝ),
      (↑t : Set E') ⊆ S ∧
      (∀ x ∈ t, 0 ≤ w x) ∧
      ∑ x ∈ t, w x = 1 ∧
      ∑ x ∈ t, w x • x = y ∧
      ∑ x ∈ t, w x • f x = z := by
  rw [mem_convexHull_iff_exists_fintype] at h
  rcases h with ⟨ι, _inst, w, q, hw₀, hw₁, hq, hsum⟩
  have hq' : ∀ i, ∃ (u : E'), u ∈ S ∧ (u, f u) = q i := by
    intro i
    have h1 : q i ∈ (fun u : E' => (u, f u)) '' S := hq i
    rcases h1 with ⟨u, hu, h_eq⟩
    exact ⟨u, hu, h_eq⟩
  choose u hu hqu using hq'
  let t : Finset E' := Finset.image u Finset.univ
  let w' : E' → ℝ := fun x => ∑ i ∈ Finset.univ, if u i = x then w i else 0
  have htS : (↑t : Set E') ⊆ S := by
    intro x hx
    have h_x_in_t : x ∈ t := by exact_mod_cast hx
    rcases Finset.mem_image.mp h_x_in_t with ⟨i, _, h_eq⟩
    have h_goal : u i = x := h_eq
    rw [←h_goal]
    exact hu i
  have hw'₀ : ∀ x ∈ t, 0 ≤ w' x := by
    intro x _
    apply Finset.sum_nonneg
    intro i _
    have h : 0 ≤ w i := hw₀ i
    by_cases h2 : u i = x
    · rw [if_pos h2] <;> exact h
    · rw [if_neg h2] <;> linarith
  have h_ui_in_t : ∀ i : ι, u i ∈ t := by
    intro i
    exact Finset.mem_image_of_mem u (Finset.mem_univ i)
  have h_sum_w' : ∑ x ∈ t, w' x = 1 := by
    have h : ∑ x ∈ t, w' x = ∑ i : ι, w i := by
      calc
        ∑ x ∈ t, w' x
          = ∑ x ∈ t, ∑ i : ι, if u i = x then w i else 0 := by rfl
        _ = ∑ i : ι, ∑ x ∈ t, if u i = x then w i else 0 := by rw [Finset.sum_comm]
        _ = ∑ i : ι, w i := by
          apply Finset.sum_congr rfl
          intro i _
          let f : E' → ℝ := fun x => if u i = x then w i else 0
          have h_f : ∀ (b : E'), b ∈ t → b ≠ u i → f b = 0 := by
            intro b _ hne
            have h9 : u i ≠ b := by tauto
            simp [f, h9] <;> tauto
          have h_eq : ∑ x ∈ t, f x = f (u i) := sum_eq_single' (h_ui_in_t i) h_f
          have h_f_ui : f (u i) = w i := by
            simp [f] <;> tauto
          rw [h_eq, h_f_ui]
    rw [h, hw₁]
  have h_prod_sum : ∑ i : ι, w i • q i = (∑ i : ι, w i • u i, ∑ i : ι, w i • f (u i)) := by
    have h4 : ∀ i, w i • q i = (w i • u i, w i • f (u i)) := by
      intro i
      have h5 : (u i, f (u i)) = q i := hqu i
      have h6 : q i = (u i, f (u i)) := h5.symm
      rw [h6] <;> simp
    have h6 : ∑ i : ι, w i • q i = ∑ i : ι, (w i • u i, w i • f (u i)) := by
      rw [Finset.sum_congr rfl (fun i _ => h4 i)]
    rw [h6]
    have h71 : (∑ i : ι, (w i • u i, w i • f (u i))).1 = ∑ i : ι, w i • u i := by
      exact Prod.fst_sum
    have h72 : (∑ i : ι, (w i • u i, w i • f (u i))).2 = ∑ i : ι, w i • f (u i) := by
      exact Prod.snd_sum
    exact Prod.ext h71 h72
  have h_sum1 : ∑ x ∈ t, w' x • x = y := by
    have h_dist : ∀ (x : E'), (∑ i : ι, if u i = x then w i else 0) • x = ∑ i : ι, if u i = x then w i • x else 0 := by
      intro x
      have h : (∑ i : ι, if u i = x then w i else 0) • x = ∑ i : ι, (if u i = x then w i else 0) • x := by
        rw [Finset.sum_smul]
      rw [h]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h2 : u i = x
      · rw [if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2, zero_smul]
    have h : ∑ x ∈ t, w' x • x = ∑ i : ι, w i • u i := by
      calc
        ∑ x ∈ t, w' x • x
          = ∑ x ∈ t, (∑ i : ι, if u i = x then w i else 0) • x := by rfl
        _ = ∑ x ∈ t, ∑ i : ι, if u i = x then w i • x else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          exact h_dist x
        _ = ∑ i : ι, ∑ x ∈ t, if u i = x then w i • x else 0 := by rw [Finset.sum_comm]
        _ = ∑ i : ι, w i • u i := by
          apply Finset.sum_congr rfl
          intro i _
          let f : E' → E' := fun x => if u i = x then w i • x else 0
          have h_f : ∀ (b : E'), b ∈ t → b ≠ u i → f b = 0 := by
            intro b _ hne
            have h9 : u i ≠ b := by tauto
            simp [f, h9] <;> tauto
          have h_eq : ∑ x ∈ t, f x = f (u i) := sum_eq_single' (h_ui_in_t i) h_f
          have h_f_ui : f (u i) = w i • u i := by
            simp [f] <;> tauto
          rw [h_eq, h_f_ui]
    rw [h]
    have h2 : ∑ i : ι, w i • q i = (y, z) := hsum
    rw [h_prod_sum] at h2
    exact Prod.ext_iff.mp h2 |>.1
  have h_sum2 : ∑ x ∈ t, w' x • f x = z := by
    have h_dist : ∀ (x : E'), (∑ i : ι, if u i = x then w i else 0) • f x = ∑ i : ι, if u i = x then w i • f x else 0 := by
      intro x
      have h : (∑ i : ι, if u i = x then w i else 0) • f x = ∑ i : ι, (if u i = x then w i else 0) • f x := by
        rw [Finset.sum_smul]
      rw [h]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h2 : u i = x
      · rw [if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2, zero_smul]
    have h : ∑ x ∈ t, w' x • f x = ∑ i : ι, w i • f (u i) := by
      calc
        ∑ x ∈ t, w' x • f x
          = ∑ x ∈ t, (∑ i : ι, if u i = x then w i else 0) • f x := by rfl
        _ = ∑ x ∈ t, ∑ i : ι, if u i = x then w i • f x else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          exact h_dist x
        _ = ∑ i : ι, ∑ x ∈ t, if u i = x then w i • f x else 0 := by rw [Finset.sum_comm]
        _ = ∑ i : ι, w i • f (u i) := by
          apply Finset.sum_congr rfl
          intro i _
          let f2 : E' → F := fun x => if u i = x then w i • f x else 0
          have h_f : ∀ (b : E'), b ∈ t → b ≠ u i → f2 b = 0 := by
            intro b _ hne
            have h9 : u i ≠ b := by tauto
            simp [f2, h9] <;> tauto
          have h_eq : ∑ x ∈ t, f2 x = f2 (u i) := sum_eq_single' (h_ui_in_t i) h_f
          have h_f_ui : f2 (u i) = w i • f (u i) := by
            simp [f2] <;> tauto
          rw [h_eq, h_f_ui]
    rw [h]
    have h2 : ∑ i : ι, w i • q i = (y, z) := hsum
    rw [h_prod_sum] at h2
    exact Prod.ext_iff.mp h2 |>.2
  exact ⟨t, w', htS, hw'₀, h_sum_w', h_sum1, h_sum2⟩

/-- A weighted sum with nonnegative coefficients summing to `1` lies in any
convex set containing the points. -/
theorem weighted_sum_in_convex {E' : Type*} [AddCommGroup E'] [Module ℝ E']
    {K : Set E'} {ι : Type*} {t : Finset ι} {w : ι → ℝ} {z : ι → E'}
    (hK : Convex ℝ K) (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : ∑ i ∈ t, w i = 1)
    (hz : ∀ i ∈ t, z i ∈ K) :
    ∑ i ∈ t, w i • z i ∈ K :=
  hK.sum_mem hw₀ hw₁ hz

end JohnEllipsoid.ConvexHullUtils
