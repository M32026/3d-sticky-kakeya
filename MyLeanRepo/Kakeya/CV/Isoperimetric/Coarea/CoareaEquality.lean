import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.LocalLipschitzCoarea
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaInequalityGlobalization
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.Eilenberg
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


/-!
# Coarea Equality for Lipschitz Functions with Unit Gradient

Combines the local upper and lower Lipschitz coarea bounds to prove
the coarea formula for Lipschitz functions with `‖fderiv f‖ = 1` a.e.

## Main result

`coarea_lipschitz_unitGradient`:
  volume {x ∈ A | a < f x ≤ b} = ∫⁻ s, μHE[n-1] {x ∈ A | f x = s}
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry

variable {n : ℕ} [Nonempty (Fin n)]

/-- Extend local upper bound from compact to measurable sets.

Given the local bound holds for all compact K ⊆ closedBall x₀ (r/2),
it also holds for all measurable C ⊆ closedBall x₀ (r/2),
by inner regularity of Lebesgue measure. -/
lemma local_coarea_lipschitz_upper_meas
    (f : E n → ℝ) (hf : LipschitzWith 1 f)
    (x₀ : E n) (h₁ : ‖fderiv ℝ f x₀‖ = 1)
    (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (hε2 : ε < 1)
    (h_grad_close : ∀ᵐ (x : E n) ∂volume.restrict (ball x₀ r),
      ‖fderiv ℝ f x - fderiv ℝ f x₀‖ ≤ ε)
    (C : Set (E n)) (hC : MeasurableSet C) (hC_sub : C ⊆ closedBall x₀ (r / 2))
    (a b : ℝ) (hab : a < b) :
    volume {x ∈ C | a < f x ∧ f x ≤ b} ≤
      ENNReal.ofReal (((1 + ε) ^ (n - 1 : ℕ)) / ((1 - ε) ^ n)) *
      ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s} := by
  let c_upper : ENNReal := ENNReal.ofReal (((1 + ε) ^ (n - 1 : ℕ)) / ((1 - ε) ^ n))
  let S : Set (E n) := {x ∈ C | a < f x ∧ f x ≤ b}
  have hS_meas : MeasurableSet S := by
    have h1 : MeasurableSet {x | a < f x} := measurableSet_Ioi.preimage hf.continuous.measurable
    have h2 : MeasurableSet {x | f x ≤ b} := measurableSet_Iic.preimage hf.continuous.measurable
    exact hC.inter (h1.inter h2)
  have hS_sub_C : S ⊆ C := by intro x hx; exact hx.1
  have hS_bdd : Bornology.IsBounded S :=
    Metric.isBounded_closedBall.subset (hS_sub_C.trans hC_sub)
  have hS_finite : volume S ≠ ⊤ := hS_bdd.measure_lt_top.ne
  have h_main : ∀ (K : Set (E n)), IsCompact K → K ⊆ S →
      volume K ≤ c_upper * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s} := by
    intro K hK_compact hK_sub_S
    have hK_sub_C : K ⊆ C := by
      intro x hx; exact (hK_sub_S hx).1
    have hK_sub_ball : K ⊆ closedBall x₀ (r / 2) := hK_sub_C.trans hC_sub
    have hK_slice_eq : {x ∈ K | a < f x ∧ f x ≤ b} = K := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · intro h; exact h.1
      · intro hx; exact ⟨hx, (hK_sub_S hx).2⟩
    have h_bound := local_coarea_lipschitz f hf x₀ h₁ r ε hr hε hε2 h_grad_close
      K hK_compact hK_sub_ball a b hab
    rw [hK_slice_eq] at h_bound
    have h_level_mono : ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ K | f x = s} ≤
        ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s} := by
      apply lintegral_mono
      intro s
      apply measure_mono
      intro x hx; exact ⟨hK_sub_C hx.1, hx.2⟩
    exact le_trans h_bound (mul_le_mul_left' h_level_mono c_upper)
  have h_inner_reg : volume S = ⨆ (K : Set (E n)) (_ : K ⊆ S) (_ : IsCompact K), volume K :=
    hS_meas.measure_eq_iSup_isCompact_of_ne_top hS_finite
  rw [h_inner_reg]
  exact iSup_le fun K => iSup_le fun hK_sub => iSup_le fun hK_compact => h_main K hK_compact hK_sub

/-- If `N` has Lebesgue volume zero, then the integral of `μHE[n-1]`
of its level sets under a 1-Lipschitz function is zero. -/
lemma null_set_levelsets_integral_zero
    {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n)
    {f : E n → ℝ} (hf : LipschitzWith 1 f)
    {N : Set (E n)} (hN : volume N = 0) :
    ∫⁻ s : ℝ, μHE[n - 1] {x ∈ N | f x = s} = 0 := by
  let d : ℕ := n - 1
  have hd_pos : 0 < d := by omega
  have h_ac : (μH[n] : Measure (E n)) ≪ (volume : Measure (E n)) :=
    MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure (μH[n]) volume
  have h_Hn_N : μH[n] N = 0 := h_ac hN
  have h_pos : 0 < (↑d : ℝ) := by exact_mod_cast hd_pos
  have h_eq1 : ((↑d : ℝ) + 1) = (n : ℝ) := by
    simp [d, hn] <;> norm_cast <;> omega
  have h_eil : ∫⁻ (t : ℝ), μH[d] (N ∩ f ⁻¹' {t}) ≤ μH[n] N := by
    have h := EilenbergInequality.eilenberg_inequality (f := f) (A := N) (d := (↑d : ℝ)) h_pos hf
    rw [h_eq1] at h
    simpa using h
  have h_int_H : ∫⁻ (t : ℝ), μH[d] (N ∩ f ⁻¹' {t}) = 0 := by
    rw [h_Hn_N] at h_eil <;> simpa using h_eil
  have h6 : ∀ s, {x ∈ N | f x = s} = N ∩ f ⁻¹' {s} := by
    intro s; ext x; simp [Set.mem_setOf_eq]
  set c : NNReal := MeasureTheory.Measure.addHaarScalarFactor
      (volume : Measure (E d)) (μH[d] : Measure (E d)) with hc_def
  have h_def2 : (μHE[d] : Measure (E n)) = c • μH[d] :=
    MeasureTheory.Measure.euclideanHausdorffMeasure_def (d := d)
  have h7 := congr_arg (fun μ : Measure (E n) => ∫⁻ (s : ℝ), μ (N ∩ f ⁻¹' {s})) h_def2
  have h_c_ne_top : (c : ENNReal) ≠ ⊤ := by simp
  have h_main : ∫⁻ (s : ℝ), μHE[d] (N ∩ f ⁻¹' {s}) = 0 := by
    rw [h7]
    have h8 : ∫⁻ (s : ℝ), (c • μH[d] : Measure (E n)) (N ∩ f ⁻¹' {s}) =
        ∫⁻ (s : ℝ), (c : ENNReal) * μH[d] (N ∩ f ⁻¹' {s}) := by
      apply lintegral_congr
      intro s
      simp [smul_apply] <;> rfl
    rw [h8]
    rw [MeasureTheory.lintegral_const_mul' (c : ENNReal) _ h_c_ne_top]
    rw [h_int_H] <;> simp
  have h_final : (fun s : ℝ => μHE[n - 1] {x ∈ N | f x = s}) =
      fun s : ℝ => μHE[d] (N ∩ f ⁻¹' {s}) := by
    funext s; rw [h6 s] <;> rfl
  rw [h_final]
  exact h_main

/-- Countable assembly of a local LOWER coarea inequality.

Given a countable open cover `U i` of `A` and a local lower bound on each
piece with constant `c`, assemble the global lower bound via disjointification. -/
lemma countable_coarea_lower_assembly
    {A : Set (E n)} (hA : MeasurableSet A)
    (f : E n → ℝ) (hf : Measurable f)
    (c : ENNReal)
    (a b : ℝ) (hab : a < b)
    (U : ℕ → Set (E n))
    (hU_open : ∀ i, IsOpen (U i))
    (h_cover : A ⊆ ⋃ i, U i)
    (h_local : ∀ i (C : Set (E n)), MeasurableSet C → C ⊆ U i →
      volume {x ∈ C | a < f x ∧ f x ≤ b} ≥
        c * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s})
    (h_level_meas : ∀ i, AEMeasurable (fun s : ℝ => μHE[n - 1] {x ∈ (A ∩ (U i \ ⋃ j ∈ Finset.range i, U j)) | f x = s}) (volume.restrict (Set.Ioc a b))) :
    volume {x ∈ A | a < f x ∧ f x ≤ b} ≥
      c * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A | f x = s} := by
  classical
  let V : ℕ → Set (E n) := fun i => U i \ ⋃ j ∈ Finset.range i, U j
  let S : ℕ → Set (E n) := fun i => A ∩ V i
  have hV_meas : ∀ i, MeasurableSet (V i) := by
    intro i
    have h1 : MeasurableSet (U i) := (hU_open i).measurableSet
    have h2 : MeasurableSet (⋃ j ∈ Finset.range i, U j) := by
      apply MeasurableSet.biUnion
      · exact Finset.countable_toSet _
      · intro j _; exact (hU_open j).measurableSet
    exact h1.diff h2
  have hS_meas : ∀ i, MeasurableSet (S i) := fun i => hA.inter (hV_meas i)
  have hS_sub_U : ∀ i, S i ⊆ U i := by
    intro i x hx; exact hx.2.1
  have h_disj : Pairwise (fun i j : ℕ => Disjoint (S i) (S j)) := by
    intro i j hne
    have hV_disj : Disjoint (V i) (V j) := by
      by_cases h : i < j
      · have h6 : V j ⊆ (U j) \ U i := by
          intro x hx
          have h7 : x ∈ U j := hx.1
          have h8 : x ∉ ⋃ k ∈ Finset.range j, U k := hx.2
          have h9 : x ∉ U i := by
            intro h10
            have h11 : x ∈ ⋃ k ∈ Finset.range j, U k := by
              apply Set.mem_iUnion₂.mpr
              exact ⟨i, Finset.mem_range.mpr h, h10⟩
            exact h8 h11
          exact ⟨h7, h9⟩
        have h7 : Disjoint (V i) ((U j) \ U i) := by
          rw [Set.disjoint_left]
          intro x hxi hxj
          have hV_sub_i : V i ⊆ U i := by intro z hz; exact hz.1
          exact hxj.2 (hV_sub_i hxi)
        exact h7.mono_right h6
      · have h' : j < i := by omega
        have h6 : V i ⊆ (U i) \ U j := by
          intro x hx
          have h7 : x ∈ U i := hx.1
          have h8 : x ∉ ⋃ k ∈ Finset.range i, U k := hx.2
          have h9 : x ∉ U j := by
            intro h10
            have h11 : x ∈ ⋃ k ∈ Finset.range i, U k := by
              apply Set.mem_iUnion₂.mpr
              exact ⟨j, Finset.mem_range.mpr h', h10⟩
            exact h8 h11
          exact ⟨h7, h9⟩
        have h7 : Disjoint (V j) ((U i) \ U j) := by
          rw [Set.disjoint_left]
          intro x hxj hxi
          have hV_sub_j : V j ⊆ U j := by intro z hz; exact hz.1
          exact hxi.2 (hV_sub_j hxj)
        exact (h7.mono_right h6).symm
    exact hV_disj.mono (fun x hx => hx.2) (fun x hx => hx.2)
  have hS_union : (⋃ i, S i) = A := by
    ext x
    constructor
    · intro hx; rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩; exact hi.1
    · intro hx
      have h2 : x ∈ ⋃ i, U i := h_cover hx
      let P : ℕ → Prop := fun j => x ∈ U j
      have hP : ∃ (k : ℕ), P k := by
        have h3 : x ∈ ⋃ (i : ℕ), U i := h2
        rcases Set.mem_iUnion.mp h3 with ⟨k, hk⟩
        exact ⟨k, hk⟩
      let k : ℕ := Nat.find hP
      have hk : P k := Nat.find_spec hP
      have hmin : ∀ j < k, ¬ P j := by intro j hj; exact Nat.find_min hP hj
      have hk2 : x ∈ V k := by
        constructor
        · exact hk
        · intro h2
          rcases Set.mem_iUnion₂.mp h2 with ⟨j, hj_range, hj_U⟩
          have h_j_lt_k : j < k := Finset.mem_range.mp hj_range
          exact hmin j h_j_lt_k hj_U
      have h3 : x ∈ S k := ⟨hx, hk2⟩
      exact Set.mem_iUnion.mpr ⟨k, h3⟩
  let A_slice : Set (E n) := {y ∈ A | a < f y ∧ f y ≤ b}
  let S_slice : ℕ → Set (E n) := fun i => {y ∈ S i | a < f y ∧ f y ≤ b}
  have hS_slice_meas : ∀ i, MeasurableSet (S_slice i) := by
    intro i
    have h1 : MeasurableSet {y | a < f y} := measurableSet_Ioi.preimage hf
    have h2 : MeasurableSet {y | f y ≤ b} := measurableSet_Iic.preimage hf
    exact (hS_meas i).inter (h1.inter h2)
  have hS_slice_disj : Pairwise (fun i j => Disjoint (S_slice i) (S_slice j)) := by
    intro i j hne
    have h : Disjoint (S i) (S j) := h_disj hne
    exact h.mono (fun x hx => hx.1) (fun x hx => hx.1)
  have hS_slice_union : (⋃ i, S_slice i) = A_slice := by
    ext x
    simp only [Set.mem_iUnion, S_slice, A_slice, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hxi⟩; exact ⟨hxi.1.1, hxi.2⟩
    · rintro ⟨hxA, hxf⟩
      have h2 : x ∈ ⋃ i, S i := by rw [hS_union]; exact hxA
      rcases Set.mem_iUnion.mp h2 with ⟨i, hxi⟩
      exact ⟨i, ⟨hxi, hxf⟩⟩
  have h_lhs : volume A_slice = ∑' i, volume (S_slice i) := by
    have h_eq : volume A_slice = volume (⋃ i, S_slice i) := by rw [hS_slice_union]
    rw [h_eq]
    exact MeasureTheory.measure_iUnion hS_slice_disj hS_slice_meas
  let level_slices : ℕ → ℝ → Set (E n) := fun i s => {y ∈ S i | f y = s}
  have h_level_set_meas : ∀ i s, MeasurableSet (level_slices i s) := by
    intro i s
    have h1 : MeasurableSet (S i) := hS_meas i
    have h2 : MeasurableSet {y | f y = s} := isClosed_singleton.measurableSet.preimage hf
    exact h1.inter h2
  have h_level_disj : ∀ s, Pairwise (fun i j => Disjoint (level_slices i s) (level_slices j s)) := by
    intro s i j hne
    have h : Disjoint (S i) (S j) := h_disj hne
    exact h.mono (fun x hx => hx.1) (fun x hx => hx.1)
  have h_union_levels : ∀ s, (⋃ i, level_slices i s) = {y ∈ A | f y = s} := by
    intro s
    ext x
    simp only [Set.mem_iUnion, level_slices, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, hxi⟩; exact ⟨hxi.1.1, hxi.2⟩
    · rintro ⟨hxA, hxf⟩
      have h2 : x ∈ ⋃ i, S i := by rw [hS_union]; exact hxA
      rcases Set.mem_iUnion.mp h2 with ⟨i, hxi⟩
      exact ⟨i, ⟨hxi, hxf⟩⟩
  have h_μHE_union : ∀ s, μHE[n - 1] (⋃ i, level_slices i s) =
      ∑' i, μHE[n - 1] (level_slices i s) := by
    intro s
    exact MeasureTheory.measure_iUnion (h_level_disj s) (h_level_set_meas · s)
  have h_rhs_eq : ∑' i, ∫⁻ s in Set.Ioc a b, μHE[n - 1] (level_slices i s) =
      ∫⁻ s in Set.Ioc a b, μHE[n - 1] {y ∈ A | f y = s} := by
    have h1 : (fun s : ℝ => μHE[n - 1] {y ∈ A | f y = s}) =
        fun s : ℝ => ∑' i, μHE[n - 1] (level_slices i s) := by
      funext s
      have h2 : {y ∈ A | f y = s} = ⋃ i, level_slices i s := (h_union_levels s).symm
      rw [h2, h_μHE_union s]
    rw [h1]
    have h3 : ∑' i, ∫⁻ s in Set.Ioc a b, μHE[n - 1] (level_slices i s) =
        ∫⁻ s in Set.Ioc a b, ∑' i, μHE[n - 1] (level_slices i s) := by
      rw [lintegral_tsum h_level_meas]
    rw [h3]
  have h_each : ∀ i, volume (S_slice i) ≥
      c * ∫⁻ s in Set.Ioc a b, μHE[n - 1] (level_slices i s) := by
    intro i
    have h1 : S_slice i = {y ∈ S i | a < f y ∧ f y ≤ b} := by rfl
    rw [h1]
    exact h_local i (S i) (hS_meas i) (hS_sub_U i)
  calc volume A_slice
      = ∑' i, volume (S_slice i) := h_lhs
    _ ≥ ∑' i, (c * ∫⁻ s in Set.Ioc a b, μHE[n - 1] (level_slices i s)) := by
        exact ENNReal.tsum_le_tsum h_each
    _ = c * ∑' i, (∫⁻ s in Set.Ioc a b, μHE[n - 1] (level_slices i s)) := by
        rw [ENNReal.tsum_mul_left]
    _ = c * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {y ∈ A | f y = s} := by
        rw [h_rhs_eq]

end Geometry
