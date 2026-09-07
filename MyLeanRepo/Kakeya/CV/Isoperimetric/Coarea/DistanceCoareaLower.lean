import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.DistanceCoareaUpper
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaEquality
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.LocalLipschitzCoarea
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaInequalityGlobalization
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.Eilenberg
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


/-!
# Distance Function Coarea Formula — Lower Bound

Provides the global lower bound:
`volume {x ∈ A | a < d x ≤ b} ≥ c_lower(ε) * ∫⁻ μHE[n-1](level sets)`

using `local_coarea_lipschitz_reverse` + Lindelöf covering +
`countable_coarea_lower_assembly` + absolute continuity of the coarea
measure with respect to volume.

## Main result

- `distance_coarea_lower`: global lower bound via Lindelöf covering
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry

variable {n : ℕ} [Nonempty (Fin n)]

/-- Local coarea lower bound extended from compact to measurable bounded sets.

Uses inner regularity + Eilenberg inequality. -/
lemma local_coarea_measurable_lower
    (hn : 2 ≤ n)
    {f : E n → ℝ} (hf : LipschitzWith 1 f)
    {x₀ : E n} (h₁ : ‖fderiv ℝ f x₀‖ = 1)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (hε2 : ε < 1)
    (h_grad_close : ∀ᵐ (x : E n) ∂volume.restrict (ball x₀ r),
      ‖fderiv ℝ f x - fderiv ℝ f x₀‖ ≤ ε)
    {C : Set (E n)} (hC : MeasurableSet C) (hC_sub : C ⊆ closedBall x₀ (r / 2))
    (hC_bdd : Bornology.IsBounded C)
    {a b : ℝ} (hab : a < b)
    (h_meas : ∀ (B : Set (E n)), MeasurableSet B → B ⊆ C →
      AEMeasurable (fun s : ℝ => μHE[n - 1] {x ∈ B | f x = s}) (volume.restrict (Set.Ioc a b))) :
    volume {x ∈ C | a < f x ∧ f x ≤ b} ≥
      ENNReal.ofReal (((1 - ε) ^ (n - 1 : ℕ)) / ((1 + ε) ^ n)) *
      ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s} := by
  let K_low : ENNReal := ENNReal.ofReal (((1 - ε) ^ (n - 1 : ℕ)) / ((1 + ε) ^ n))
  have hK_low_ne_top : K_low ≠ ⊤ := ENNReal.ofReal_ne_top
  have hK_low_pos : 0 < K_low := by
    apply ENNReal.ofReal_pos.mpr
    positivity
  let C_slice : Set (E n) := {x ∈ C | a < f x ∧ f x ≤ b}
  have hC_slice_meas : MeasurableSet C_slice := by
    have h1 : MeasurableSet {x : E n | a < f x} :=
      measurableSet_Ioi.preimage hf.continuous.measurable
    have h2 : MeasurableSet {x : E n | f x ≤ b} :=
      measurableSet_Iic.preimage hf.continuous.measurable
    exact hC.inter (h1.inter h2)
  have hC_slice_fin : volume C_slice ≠ ⊤ :=
    ne_top_of_le_ne_top hC_bdd.measure_lt_top.ne (measure_mono (fun x hx => hx.1))
  rcases eilenberg_μHE hn (hf := hf) (by simp) with ⟨C_eil, hC_eil_ne_top, hC_eil_pos, h_eilenberg⟩
  have h_eil_Ioc : ∀ (A : Set (E n)),
      ∫⁻ s in Set.Ioc a b, μHE[n - 1] (A ∩ f ⁻¹' {s}) ≤ C_eil * volume A := by
    intro A
    have h9 : ∫⁻ s in Set.Ioc a b, μHE[n - 1] (A ∩ f ⁻¹' {s}) ≤
        ∫⁻ (s : ℝ), μHE[n - 1] (A ∩ f ⁻¹' {s}) := by
      have h91 : ∫⁻ s in Set.Ioc a b, μHE[n - 1] (A ∩ f ⁻¹' {s}) ≤
          ∫⁻ s in (Set.univ : Set ℝ), μHE[n - 1] (A ∩ f ⁻¹' {s}) :=
        lintegral_mono_set (Set.subset_univ (Set.Ioc a b))
      have h92 : (∫⁻ s in (Set.univ : Set ℝ), μHE[n - 1] (A ∩ f ⁻¹' {s})) =
          ∫⁻ (s : ℝ), μHE[n - 1] (A ∩ f ⁻¹' {s}) := by
        rw [Measure.restrict_univ]
        <;> rfl
      rw [h92] at h91
      exact h91
    exact le_trans h9 (h_eilenberg A)
  have h_main : ∀ (δ : ℝ), 0 < δ →
      K_low * (∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s}) ≤
      volume C_slice + ENNReal.ofReal δ := by
    intro δ hδ
    let δ' : ENNReal := ENNReal.ofReal δ / (K_low * C_eil)
    have hdenom : K_low * C_eil ≠ 0 := by
      intro h
      have : K_low = 0 ∨ C_eil = 0 := mul_eq_zero.mp h
      cases this with
      | inl h => exact hK_low_pos.ne' h
      | inr h => exact hC_eil_pos h
    have h_ne_top : K_low * C_eil ≠ ⊤ := by
      apply ENNReal.mul_ne_top <;> tauto
    have hδ'_pos : 0 < δ' := by
      apply ENNReal.div_pos
      · exact ne_of_gt (ENNReal.ofReal_pos.mpr hδ)
      · exact h_ne_top
    have hδ'_ne_top : δ' ≠ ⊤ := by
      apply ENNReal.div_ne_top
      · exact ENNReal.ofReal_ne_top
      · exact hdenom
    have h_exists : ∃ (K : Set (E n)), IsCompact K ∧ K ⊆ C_slice ∧
        volume (C_slice \ K) < δ' := by
      have hε' : δ' ≠ 0 := hδ'_pos.ne'
      have h1 : ∃ (K : Set (E n)), K ⊆ C_slice ∧ IsCompact K ∧ volume C_slice < volume K + δ' :=
        hC_slice_meas.exists_isCompact_lt_add hC_slice_fin hε'
      rcases h1 with ⟨K, hK_sub, hK_comp, hK_lt⟩
      have hK_meas : MeasurableSet K := hK_comp.measurableSet
      have h2 : volume C_slice = volume K + volume (C_slice \ K) := by
        have h_disj_K : Disjoint K (C_slice \ K) := by
          rw [Set.disjoint_left]; intro x hx1 hx2; exact hx2.2 hx1
        have h_diff_meas : MeasurableSet (C_slice \ K) := hC_slice_meas.diff hK_meas
        have h_union : volume (K ∪ (C_slice \ K)) = volume K + volume (C_slice \ K) :=
          measure_union h_disj_K h_diff_meas
        have h_eq : K ∪ (C_slice \ K) = C_slice := by
          ext x; simp only [Set.mem_union, Set.mem_diff]
          constructor
          · rintro (h | ⟨h, _⟩); exact hK_sub h; exact h
          · intro hx; by_cases h : x ∈ K; exact Or.inl h; exact Or.inr ⟨hx, h⟩
        rw [h_eq] at h_union
        exact h_union
      have h3 : volume (C_slice \ K) < δ' := by
        have h4 : volume K + volume (C_slice \ K) < volume K + δ' := by
          rw [h2] at hK_lt; exact hK_lt
        have hK_ne_top : volume K ≠ ⊤ := ne_top_of_le_ne_top hC_slice_fin (measure_mono hK_sub)
        exact (ENNReal.add_lt_add_iff_left hK_ne_top).mp h4
      exact ⟨K, hK_comp, hK_sub, h3⟩
    rcases h_exists with ⟨K, hK_comp, hK_sub, hK_diff⟩
    have hK_meas : MeasurableSet K := hK_comp.measurableSet
    have hK_sub_C : K ⊆ C := fun x hx => (hK_sub hx).1
    have hK_sub2 : K ⊆ closedBall x₀ (r / 2) := subset_trans hK_sub_C hC_sub
    have hK_eq : {x ∈ K | a < f x ∧ f x ≤ b} = K := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨hx, _⟩; exact hx
      · intro hx; have h2 : x ∈ C_slice := hK_sub hx; exact ⟨hx, h2.2⟩
    have h_local := local_coarea_lipschitz_reverse f hf x₀ h₁ r ε hr hε hε2
      h_grad_close K hK_comp hK_sub2 a b hab
    have h1 : volume K ≥ K_low * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ K | f x = s} := by
      simpa [hK_eq] using h_local
    have h_ms_K : ∀ s, MeasurableSet {x ∈ K | f x = s} := by
      intro s; exact hK_meas.inter (isClosed_singleton.measurableSet.preimage hf.continuous.measurable)
    have h_ms_diff : ∀ s, MeasurableSet ((C_slice \ K) ∩ f ⁻¹' {s}) := by
      intro s; exact (hC_slice_meas.diff hK_meas).inter (isClosed_singleton.measurableSet.preimage hf.continuous.measurable)
    have h_level_eq_on : ∀ s ∈ Set.Ioc a b, {x ∈ C | f x = s} =
        {x ∈ K | f x = s} ∪ ((C_slice \ K) ∩ f ⁻¹' {s}) := by
      intro s hs
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
      constructor
      · rintro ⟨hyC, hyf⟩
        by_cases hK : y ∈ K
        · exact Or.inl ⟨hK, hyf⟩
        · have hys : y ∈ C_slice := ⟨hyC, by rw [hyf] <;> exact hs.1, by rw [hyf] <;> exact hs.2⟩
          exact Or.inr ⟨⟨hys, hK⟩, hyf⟩
      · rintro (⟨hK, hyf⟩ | ⟨⟨hyC, _⟩, hyf⟩)
        · exact ⟨hK_sub_C hK, hyf⟩
        · exact ⟨hyC.1, hyf⟩
    have h_disj : ∀ s, Disjoint {x ∈ K | f x = s} ((C_slice \ K) ∩ f ⁻¹' {s}) := by
      intro s; rw [Set.disjoint_left]; intro y h1 h2; exact h2.1.2 h1.1
    set I_C := (∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s}) with hI_C
    set I_K := (∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ K | f x = s}) with hI_K
    set I_D := (∫⁻ s in Set.Ioc a b, μHE[n - 1] ((C_slice \ K) ∩ f ⁻¹' {s})) with hI_D
    set Z := K_low * C_eil * volume (C_slice \ K) with hZ
    have hK_aemeas : AEMeasurable (fun s : ℝ => μHE[n - 1] {x ∈ K | f x = s}) (volume.restrict (Set.Ioc a b)) :=
      h_meas K hK_meas hK_sub_C
    have hD_aemeas : AEMeasurable (fun s : ℝ => μHE[n - 1] ((C_slice \ K) ∩ f ⁻¹' {s})) (volume.restrict (Set.Ioc a b)) :=
      h_meas (C_slice \ K) (hC_slice_meas.diff hK_meas)
        (show (C_slice \ K) ⊆ C from fun x hx => hx.1.1)
    have h_pointwise : ∀ s ∈ Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s} =
        μHE[n - 1] {x ∈ K | f x = s} + μHE[n - 1] ((C_slice \ K) ∩ f ⁻¹' {s}) := by
      intro s hs
      have h_eq : {x ∈ C | f x = s} = {x ∈ K | f x = s} ∪ ((C_slice \ K) ∩ f ⁻¹' {s}) :=
        h_level_eq_on s hs
      rw [h_eq]
      exact measure_union (h_disj s) (h_ms_diff s)
    have h_ae : ∀ᵐ (s : ℝ) ∂(volume.restrict (Set.Ioc a b)),
        μHE[n - 1] {x ∈ C | f x = s} =
        μHE[n - 1] {x ∈ K | f x = s} + μHE[n - 1] ((C_slice \ K) ∩ f ⁻¹' {s}) := by
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioc)] with s hs
      exact h_pointwise s hs
    have h2 : I_C = I_K + I_D := by
      rw [hI_C, hI_K, hI_D]
      let fK := hK_aemeas.mk
      let fD := hD_aemeas.mk
      have hfK_eq : (fun s : ℝ => μHE[n - 1] {x ∈ K | f x = s}) =ᵐ[volume.restrict (Set.Ioc a b)] fK :=
        hK_aemeas.ae_eq_mk
      have hfD_eq : (fun s : ℝ => μHE[n - 1] ((C_slice \ K) ∩ f ⁻¹' {s})) =ᵐ[volume.restrict (Set.Ioc a b)] fD :=
        hD_aemeas.ae_eq_mk
      have h_sum_eq : (fun s : ℝ => μHE[n - 1] {x ∈ C | f x = s}) =ᵐ[volume.restrict (Set.Ioc a b)] (fun s => fK s + fD s) := by
        filter_upwards [hfK_eq, hfD_eq, h_ae] with s hK_eq hD_eq hC_eq
        calc
          μHE[n - 1] {x ∈ C | f x = s}
            = μHE[n - 1] {x ∈ K | f x = s} + μHE[n - 1] ((C_slice \ K) ∩ f ⁻¹' {s}) := hC_eq
          _ = fK s + fD s := by rw [←hK_eq, ←hD_eq]
      have h_main : lintegral (volume.restrict (Set.Ioc a b)) (fun s : ℝ => μHE[n - 1] {x ∈ C | f x = s}) =
          lintegral (volume.restrict (Set.Ioc a b)) fK + lintegral (volume.restrict (Set.Ioc a b)) fD := by
        rw [lintegral_congr_ae h_sum_eq]
        have hfK_meas : Measurable fK := hK_aemeas.measurable_mk
        have hfD_meas : Measurable fD := hD_aemeas.measurable_mk
        simpa [Pi.add_apply] using MeasureTheory.lintegral_add_left hfK_meas fD
      have hK_eq : lintegral (volume.restrict (Set.Ioc a b)) fK = lintegral (volume.restrict (Set.Ioc a b)) (fun s : ℝ => μHE[n - 1] {x ∈ K | f x = s}) :=
        lintegral_congr_ae hfK_eq.symm
      have hD_eq : lintegral (volume.restrict (Set.Ioc a b)) fD = lintegral (volume.restrict (Set.Ioc a b)) (fun s : ℝ => μHE[n - 1] ((C_slice \ K) ∩ f ⁻¹' {s})) :=
        lintegral_congr_ae hfD_eq.symm
      rw [h_main, hK_eq, hD_eq]
    have h3 : I_D ≤ C_eil * volume (C_slice \ K) := h_eil_Ioc (C_slice \ K)
    have h_bound : K_low * I_D ≤ Z := by
      have h : K_low * I_D ≤ K_low * (C_eil * volume (C_slice \ K)) := mul_le_mul_left' h3 K_low
      simpa [hZ, mul_assoc] using h
    have h4 : K_low * I_C ≤ K_low * I_K + Z := by
      have h_distrib : K_low * (I_K + I_D) = K_low * I_K + K_low * I_D := left_distrib K_low I_K I_D
      have h2' : K_low * I_C = K_low * I_K + K_low * I_D := by
        have h : K_low * I_C = K_low * (I_K + I_D) := by rw [h2]
        rw [h, h_distrib]
      rw [h2']
      exact add_le_add (le_refl _) h_bound
    have h5 : Z < K_low * C_eil * δ' := by
      have h_ne_top : K_low * C_eil ≠ ⊤ := by
        apply ENNReal.mul_ne_top <;> tauto
      exact ENNReal.mul_lt_mul_right hdenom h_ne_top hK_diff
    have h6 : K_low * C_eil * δ' = ENNReal.ofReal δ := by
      have h7 : K_low * C_eil ≠ 0 := hdenom
      have h8 : K_low * C_eil ≠ ⊤ := by
        apply ENNReal.mul_ne_top <;> tauto
      simp [δ', ENNReal.mul_div_cancel h7 h8] <;> ring
    have h9 : K_low * I_K ≤ volume K := h1
    have hK_lt_top : volume K ≠ ⊤ := ne_top_of_le_ne_top hC_slice_fin (measure_mono hK_sub)
    have h10 : K_low * I_C ≤ volume C_slice + ENNReal.ofReal δ :=
      h4.trans <| (add_le_add_left h9 Z).trans <|
        (le_of_lt (ENNReal.add_lt_add_left hK_lt_top h5)).trans <|
          (le_of_eq (show volume K + K_low * C_eil * δ' = volume K + ENNReal.ofReal δ from by rw [h6])).trans
            (add_le_add_left (measure_mono hK_sub) (ENNReal.ofReal δ))
    exact h10
  have hC_slice_lt_top : volume C_slice < ⊤ := lt_top_iff_ne_top.mpr hC_slice_fin
  have h_main' : ∀ (ε : NNReal), 0 < ε → volume C_slice < ⊤ →
      K_low * (∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s}) ≤ volume C_slice + (ε : ENNReal) := by
    intro ε hε _
    have h10 : (ε : ENNReal) = ENNReal.ofReal (ε : ℝ) := by
      simp
    rw [h10]
    exact h_main (ε : ℝ) (by exact_mod_cast hε)
  have h_final : K_low * (∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s}) ≤
      volume C_slice := ENNReal.le_of_forall_pos_le_add h_main'
  simpa [C_slice] using h_final

/-- **Global distance coarea lower bound.**

For a nonempty closed `C`, bounded measurable `A ⊆ {d > 0}`, and `0 < ε < 1`:

```
volume {x ∈ A | a < d x ≤ b} ≥
  ((1-ε)^(n-1) / (1+ε)^n) * ∫⁻ s in Ioc a b, μHE[n-1] {x ∈ A | d x = s}
```

where `d(x) = infDist x C`. -/
abbrev CoareaLevelMeasurable (n : ℕ) : Prop :=
  ∀ (f : E n → ℝ) (L : NNReal) (hf : LipschitzWith L f) (B : Set (E n))
    (hB : MeasurableSet B) (a b : ℝ),
      AEMeasurable (fun s : ℝ => μHE[n - 1] {x ∈ B | f x = s}) (volume.restrict (Set.Ioc a b))

/-- Function-specific level-set AEMeasurability. -/
abbrev FunctionLevelMeasurable {n : ℕ} (f : E n → ℝ) : Prop :=
  ∀ (B : Set (E n)) (hB : MeasurableSet B) (a b : ℝ),
    AEMeasurable (fun s : ℝ => μHE[n - 1] {x ∈ B | f x = s}) (volume.restrict (Set.Ioc a b))

theorem distance_coarea_lower (hn : 2 ≤ n)
    {C : Set (E n)} (hC : IsClosed C) (hne : C.Nonempty)
    (h_d_meas : FunctionLevelMeasurable (fun x : E n => infDist x C))
    {A : Set (E n)} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (hA_sub : A ⊆ {x | 0 < infDist x C})
    {a b : ℝ} (hab : a < b) {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1) :
    volume {x ∈ A | a < infDist x C ∧ infDist x C ≤ b} ≥
      ENNReal.ofReal (((1 - ε) ^ (n - 1 : ℕ)) / ((1 + ε) ^ n)) *
      ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A | infDist x C = s} := by
  let d := fun x : E n => infDist x C
  let K_low : ℝ := ((1 - ε) ^ (n - 1 : ℕ)) / ((1 + ε) ^ n)
  have hK_low_pos : 0 < K_low := by positivity

  -- Differentiability set
  let D : Set (E n) := {x | DifferentiableAt ℝ d x}
  have hD_ae : ∀ᵐ x ∂volume, x ∈ D := infDist_lipschitz.ae_differentiableAt

  -- For each x ∈ D ∩ A, choose a ball with gradient closeness
  have h_ball_exists : ∀ (x : E n), x ∈ D ∩ A →
      ∃ (r : ℝ), 0 < r ∧ ball x (r / 2) ⊆ {z | 0 < d z} ∧
        ∀ᵐ (z : E n) ∂volume.restrict (ball x r),
          ‖fderiv ℝ d z - fderiv ℝ d x‖ ≤ ε := by
    intro x hx
    have hxD : DifferentiableAt ℝ d x := hx.1
    have hpos : 0 < d x := hA_sub hx.2
    rcases grad_close_ball hC hne hxD hpos hε with ⟨r, hr_pos, h_ball_sub, h_grad⟩
    refine ⟨r, hr_pos, ?_, h_grad⟩
    exact subset_trans (ball_subset_ball (by linarith)) h_ball_sub
  choose r hr_pos h_ball_sub h_grad_close using h_ball_exists

  -- Open cover of D ∩ A
  let idx : Type _ := {x : E n // x ∈ D ∩ A}
  let U_idx : idx → Set (E n) := fun i => ball i.val (r i.val i.property / 2)
  have hU_open : ∀ (i : idx), IsOpen (U_idx i) := fun _ => isOpen_ball
  have h_cover : (D ∩ A : Set (E n)) ⊆ ⋃ (i : idx), U_idx i := by
    intro x hx
    let i : idx := ⟨x, hx⟩
    have h2 : x ∈ U_idx i := by
      have h4 : 0 < r x hx / 2 := by linarith [hr_pos x hx]
      have h5 : dist x x < r x hx / 2 := by simpa using h4
      exact h5
    exact Set.mem_iUnion.mpr ⟨i, h2⟩
  have h_lindelof : IsLindelof (D ∩ A : Set (E n)) :=
    HereditarilyLindelofSpace.isLindelof (D ∩ A)
  rcases h_lindelof.elim_countable_subcover U_idx hU_open h_cover with ⟨S, hS_count, hS_cover⟩
  by_cases hDA_empty : (D ∩ A : Set (E n)) = ∅
  · -- D ∩ A is empty, so A has measure zero
    have h1 : A ⊆ {x | x ∉ D} := by
      intro x hx
      by_contra h2
      have h2' : x ∈ D := by simpa using h2
      have h3 : x ∈ D ∩ A := ⟨h2', hx⟩
      rw [hDA_empty] at h3 <;> simpa using h3
    have h4 : volume {x : E n | x ∉ D} = 0 := by
      have h5 : ∀ᵐ (x : E n) ∂volume, x ∈ D := hD_ae
      exact h5
    have hA_null : volume A = 0 := measure_mono_null h1 h4
    have h5 : ∫⁻ s : ℝ, μHE[n - 1] {x ∈ A | d x = s} = 0 :=
      null_set_levelsets_integral_zero hn (hf := infDist_lipschitz) hA_null
    have h6 : ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A | d x = s} = 0 := by
      have h7 : ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A | d x = s} ≤
          ∫⁻ (s : ℝ), μHE[n - 1] {x ∈ A | d x = s} := by
        have h71 : ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A | d x = s} ≤
            ∫⁻ s in (Set.univ : Set ℝ), μHE[n - 1] {x ∈ A | d x = s} :=
          lintegral_mono_set (Set.subset_univ (Set.Ioc a b))
        have h72 : (∫⁻ s in (Set.univ : Set ℝ), μHE[n - 1] {x ∈ A | d x = s}) =
            ∫⁻ (s : ℝ), μHE[n - 1] {x ∈ A | d x = s} := by simp
        rw [h72] at h71
        exact h71
      rw [h5] at h7; simpa using h7
    have h7 : volume {x ∈ A | a < d x ∧ d x ≤ b} = 0 :=
      measure_mono_null (fun x hx => hx.1) hA_null
    rw [h7, h6]
    <;> simp
    <;> exact zero_le _
  · -- D ∩ A is nonempty, hence S is nonempty
    have hDA_nonempty : (D ∩ A : Set (E n)).Nonempty := by
      rw [Set.nonempty_iff_ne_empty] <;> exact hDA_empty
    have hS_nonempty : S.Nonempty := by
      by_contra h
      have hS_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      rw [hS_empty] at hS_cover
      simp at hS_cover
      have hDA_empty2 : (D ∩ A : Set (E n)) = ∅ := by
        simpa using hS_cover
      exact Set.nonempty_iff_ne_empty.mp hDA_nonempty hDA_empty2
    rcases hS_count.exists_eq_range hS_nonempty with ⟨e : ℕ → idx, he_range⟩
    let U : ℕ → Set (E n) := fun k => U_idx (e k)
    have hU_open' : ∀ k, IsOpen (U k) := fun k => hU_open (e k)
    have hS_cover' : (D ∩ A : Set (E n)) ⊆ ⋃ k, U k := by
      calc
        (D ∩ A : Set (E n)) ⊆ ⋃ i ∈ S, U_idx i := hS_cover
        _ = ⋃ k, U k := by
          ext z
          simp only [Set.mem_iUnion, U, he_range] <;> aesop
    let A' := A ∩ (⋃ k, U k)
    have hA'_meas : MeasurableSet A' := hA.inter (MeasurableSet.iUnion (fun k => (hU_open' k).measurableSet))
    have hA'_sub : A' ⊆ ⋃ k, U k := fun x hx => hx.2
    have hA_diff_null : volume (A \ A') = 0 := by
      have h1 : A \ A' ⊆ {x | x ∉ D} := by
        intro x hx
        have hxA : x ∈ A := hx.1
        have h2 : x ∉ A' := hx.2
        by_contra h3
        have h3' : x ∈ D := by simpa using h3
        have h4 : x ∈ D ∩ A := ⟨h3', hxA⟩
        have h5 : x ∈ ⋃ k, U k := hS_cover' h4
        have h6 : x ∈ A' := ⟨hxA, h5⟩
        exact h2 h6
      have h7 : volume {x : E n | x ∉ D} = 0 := by
        have h8 : ∀ᵐ (x : E n) ∂volume, x ∈ D := hD_ae
        exact h8
      exact measure_mono_null h1 h7

    -- Local lower bound on each U k
    have h_local : ∀ (k : ℕ) (C' : Set (E n)), MeasurableSet C' → C' ⊆ U k →
        volume {x ∈ C' | a < d x ∧ d x ≤ b} ≥
          ENNReal.ofReal K_low * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C' | d x = s} := by
      intro k C' hC'_meas hC'_sub
      let i : idx := e k
      let x₀ : E n := i.val
      have hx₀_in : x₀ ∈ D ∩ A := i.property
      have hx₀_diff : DifferentiableAt ℝ d x₀ := by simpa [D] using hx₀_in.1
      have hx₀_pos : 0 < d x₀ := hA_sub hx₀_in.2
      let r₀ := r x₀ hx₀_in
      have hr₀_pos : 0 < r₀ := hr_pos x₀ hx₀_in
      have h_grad : ∀ᵐ (z : E n) ∂volume.restrict (ball x₀ r₀),
          ‖fderiv ℝ d z - fderiv ℝ d x₀‖ ≤ ε := h_grad_close x₀ hx₀_in
      have h₁ : ‖fderiv ℝ d x₀‖ = 1 := norm_fderiv_infDist_eq_one hC hne hx₀_diff hx₀_pos
      have hU_eq : U k = ball x₀ (r₀ / 2) := by
        dsimp only [U, U_idx] <;> rfl
      have hC'_sub2 : C' ⊆ closedBall x₀ (r₀ / 2) := by
        rw [hU_eq] at hC'_sub
        intro z hz
        have h3 : z ∈ ball x₀ (r₀ / 2) := hC'_sub hz
        have h4 : dist z x₀ < r₀ / 2 := by simpa [Metric.mem_ball] using h3
        simpa [Metric.mem_closedBall] using le_of_lt h4
      have hC'_bdd : Bornology.IsBounded C' := by
        rw [hU_eq] at hC'_sub
        have h_ball_bdd : Bornology.IsBounded (ball x₀ (r₀ / 2)) := Metric.isBounded_ball
        exact Bornology.IsBounded.subset h_ball_bdd hC'_sub
      have h_meas_local : ∀ (B : Set (E n)), MeasurableSet B → B ⊆ C' →
          AEMeasurable (fun s : ℝ => μHE[n - 1] {x ∈ B | d x = s}) (volume.restrict (Set.Ioc a b)) := by
        intro B hB_meas hB_sub
        exact h_d_meas B hB_meas a b
      have h_main := local_coarea_measurable_lower (hn := hn)
        (f := d) (hf := infDist_lipschitz) (x₀ := x₀) (h₁ := h₁)
        (r := r₀) (ε := ε) (hr := hr₀_pos) (hε := hε) (hε2 := hε2)
        (h_grad_close := h_grad) (C := C') (hC := hC'_meas) (hC_sub := hC'_sub2)
        (hC_bdd := hC'_bdd) (h_meas := h_meas_local) (a := a) (b := b) (hab := hab)
      exact h_main

    -- AEMeasurable for level set functions (needed by countable_coarea_lower_assembly)
    have h_level_meas : ∀ i, AEMeasurable (fun s : ℝ => μHE[n - 1] {x ∈ (A' ∩ (U i \ ⋃ j ∈ Finset.range i, U j)) | d x = s})
        (volume.restrict (Set.Ioc a b)) := by
      intro i
      have h1 : MeasurableSet (A' ∩ (U i \ ⋃ j ∈ Finset.range i, U j)) := by
        apply hA'_meas.inter
        have h2 : MeasurableSet (U i) := (hU_open' i).measurableSet
        have h3 : MeasurableSet (⋃ j ∈ Finset.range i, U j) := by
          apply MeasurableSet.biUnion
          · exact Finset.countable_toSet _
          · intro j _; exact (hU_open' j).measurableSet
        exact h2.diff h3
      have h2 : AEMeasurable (fun s : ℝ => μHE[n - 1] {x ∈ (A' ∩ (U i \ ⋃ j ∈ Finset.range i, U j)) | d x = s})
          (volume.restrict (Set.Ioc a b)) := by
        exact h_d_meas
          (A' ∩ (U i \ ⋃ j ∈ Finset.range i, U j))
          (hA'_meas.inter ((hU_open' i).measurableSet.diff
            (MeasurableSet.biUnion (Finset.countable_toSet _)
              (fun j _ => (hU_open' j).measurableSet)))) a b
      exact h2

    -- Apply lower assembly
    have h_assembly := countable_coarea_lower_assembly
      (hA := hA'_meas) (f := d) (hf := infDist_lipschitz.continuous.measurable)
      (c := ENNReal.ofReal K_low) (a := a) (b := b) (hab := hab)
      (U := U) (hU_open := hU_open') (h_cover := hA'_sub)
      (h_local := h_local) (h_level_meas := h_level_meas)

    let A_slice := {x ∈ A | a < d x ∧ d x ≤ b}
    let A'_slice := {x ∈ A' | a < d x ∧ d x ≤ b}

    have hA_slice_eq : volume A_slice = volume A'_slice := by
      have h1 : A_slice \ A'_slice ⊆ A \ A' := by
        intro x hx
        have hxA_slice : x ∈ A_slice := hx.1
        have hx_not_A'_slice : x ∉ A'_slice := hx.2
        have hxA : x ∈ A := hxA_slice.1
        have hxf : a < d x ∧ d x ≤ b := hxA_slice.2
        have hx_not_A' : x ∉ A' := by
          by_contra h3
          have h4 : x ∈ A'_slice := ⟨h3, hxf⟩
          exact hx_not_A'_slice h4
        exact ⟨hxA, hx_not_A'⟩
      have h2 : volume (A_slice \ A'_slice) = 0 := measure_mono_null h1 hA_diff_null
      have h_sub : A'_slice ⊆ A_slice := by
        intro x hx
        exact ⟨hx.1.1, hx.2⟩
      have h3 : A_slice = A'_slice ∪ (A_slice \ A'_slice) := by
        ext x; simp only [Set.mem_union, Set.mem_diff]
        constructor
        · intro hx; by_cases h4 : x ∈ A'_slice; exact Or.inl h4; exact Or.inr ⟨hx, h4⟩
        · rintro (h | ⟨h, _⟩); exact h_sub h; exact h
      rw [h3]
      have hIoc_meas : MeasurableSet (Set.Ioc a b) := by
        have h1 : MeasurableSet (Set.Ioi a) := isOpen_Ioi.measurableSet
        have h2 : MeasurableSet (Set.Iic b) := isClosed_Iic.measurableSet
        exact h1.inter h2
      have hpreim : MeasurableSet (d ⁻¹' (Set.Ioc a b)) :=
        hIoc_meas.preimage infDist_lipschitz.continuous.measurable
      have h_slice_meas : MeasurableSet A'_slice := hA'_meas.inter hpreim
      have h_diff_meas : MeasurableSet (A_slice \ A'_slice) :=
        (hA.inter hpreim).diff h_slice_meas
      have h_disj : Disjoint A'_slice (A_slice \ A'_slice) := by
        rw [Set.disjoint_left]; intro x hx1 hx2; exact hx2.2 hx1
      have h_union : volume (A'_slice ∪ (A_slice \ A'_slice)) =
          volume A'_slice + volume (A_slice \ A'_slice) := by
        have h_helper : ∀ (T1 T2 : Set (E n)), Disjoint T1 T2 → MeasurableSet T2 →
            volume (T1 ∪ T2) = volume T1 + volume T2 := by
          intro T1 T2 hD hM2
          exact measure_union hD hM2
        exact h_helper A'_slice (A_slice \ A'_slice) h_disj h_diff_meas
      rw [h_union, h2, add_zero]

    -- Level set integral equality: A' and A differ by a null set
    have h_level_eq : ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A' | d x = s} =
        ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A | d x = s} := by
      have h_null : ∫⁻ s : ℝ, μHE[n - 1] {x ∈ A \ A' | d x = s} = 0 :=
        null_set_levelsets_integral_zero hn (hf := infDist_lipschitz) hA_diff_null
      have h_null_restrict : ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A \ A' | d x = s} = 0 := by
        have h10 : ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A \ A' | d x = s} ≤
            ∫⁻ (s : ℝ), μHE[n - 1] {x ∈ A \ A' | d x = s} := by
          have h11 : ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A \ A' | d x = s} ≤
              ∫⁻ s in (Set.univ : Set ℝ), μHE[n - 1] {x ∈ A \ A' | d x = s} :=
            lintegral_mono_set (Set.subset_univ (Set.Ioc a b))
          simpa using h11
        rw [h_null] at h10
        simpa using h10
      -- Since the lintegral of the difference part is 0, it is 0 a.e.
      have h_g_zero : ∀ᵐ (s : ℝ) ∂(volume.restrict (Set.Ioc a b)),
          μHE[n - 1] {x ∈ A \ A' | d x = s} = 0 := by
        have h_meas : AEMeasurable (fun s : ℝ => μHE[n - 1] {x ∈ A \ A' | d x = s})
            (volume.restrict (Set.Ioc a b)) :=
          h_d_meas (A \ A') (hA.diff hA'_meas) a b
        have h_eq : (∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A \ A' | d x = s}) = 0 := h_null_restrict
        have h_iff := MeasureTheory.setLIntegral_eq_zero_iff' (measurableSet_Ioc) h_meas
        have h_ae : ∀ᵐ (s : ℝ) ∂(volume.restrict (Set.Ioc a b)),
            μHE[n - 1] {x ∈ A \ A' | d x = s} = 0 := by
          rw [ae_restrict_iff' measurableSet_Ioc]
          exact h_iff.mp h_eq
        exact h_ae
      have h_disj : ∀ s, Disjoint {x ∈ A' | d x = s} {x ∈ A \ A' | d x = s} := by
        intro s; rw [Set.disjoint_left]; intro x hx1 hx2; exact hx2.1.2 hx1.1
      have h_union : ∀ s, {x ∈ A | d x = s} = {x ∈ A' | d x = s} ∪ {x ∈ A \ A' | d x = s} := by
        intro s; ext x; simp [A']; tauto
      have h_ms1 : ∀ s, MeasurableSet {x ∈ A' | d x = s} := by
        intro s; exact hA'_meas.inter (isClosed_singleton.measurableSet.preimage infDist_lipschitz.continuous.measurable)
      have h_ms2 : ∀ s, MeasurableSet {x ∈ A \ A' | d x = s} := by
        intro s; exact (hA.diff hA'_meas).inter (isClosed_singleton.measurableSet.preimage infDist_lipschitz.continuous.measurable)
      have h_add : ∀ s, μHE[n - 1] {x ∈ A | d x = s} =
          μHE[n - 1] {x ∈ A' | d x = s} + μHE[n - 1] {x ∈ A \ A' | d x = s} := by
        intro s
        let S1 := {x ∈ A' | d x = s}
        let S2 := {x ∈ A \ A' | d x = s}
        have h_helper : ∀ (T1 T2 : Set (E n)), Disjoint T1 T2 → MeasurableSet T2 →
            μHE[n - 1] (T1 ∪ T2) = μHE[n - 1] T1 + μHE[n - 1] T2 := by
          intro T1 T2 hD hM2
          exact measure_union hD hM2
        have h_goal : μHE[n - 1] (S1 ∪ S2) = μHE[n - 1] S1 + μHE[n - 1] S2 :=
          h_helper S1 S2 (h_disj s) (h_ms2 s)
        have h_eq : {x ∈ A | d x = s} = S1 ∪ S2 := h_union s
        rw [h_eq]
        exact h_goal
      -- Therefore the A-level function equals the A'-level function a.e.
      have h_fg_eq : ∀ᵐ (s : ℝ) ∂(volume.restrict (Set.Ioc a b)),
          μHE[n - 1] {x ∈ A | d x = s} = μHE[n - 1] {x ∈ A' | d x = s} := by
        filter_upwards [h_g_zero] with s hs
        have h : μHE[n - 1] {x ∈ A | d x = s} =
            μHE[n - 1] {x ∈ A' | d x = s} + μHE[n - 1] {x ∈ A \ A' | d x = s} := h_add s
        rw [h, hs, add_zero]
      have h_int : ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A | d x = s} =
          ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A' | d x = s} :=
        lintegral_congr_ae h_fg_eq
      exact h_int.symm

    calc
      volume A_slice
        = volume A'_slice := hA_slice_eq
      _ ≥ ENNReal.ofReal K_low * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A' | d x = s} := h_assembly
      _ = ENNReal.ofReal K_low * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A | d x = s} := by
        rw [h_level_eq]

end Geometry
