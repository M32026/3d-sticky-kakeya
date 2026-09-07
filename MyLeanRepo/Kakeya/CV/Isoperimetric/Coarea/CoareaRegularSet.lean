import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaDirBounded
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.IFTPatch
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.CoareaCriticalSet
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry

variable {n : ℕ} [Nonempty (Fin n)]

/-!
# Regular Set Coarea Equality

Proves the exact coarea formula on `Rδ := {‖∇u‖ ≥ δ}` for a C¹ function
with compact support, using a finite cover by local coarea patches and
disjointification.
-/

/-- Basis expansion in Euclidean space. -/
lemma euclidean_basis_expand {n : ℕ} (v : E n) :
    v = ∑ i : Fin n, v i • EuclideanSpace.single i (1 : ℝ) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have h_repr : ∑ i : Fin n, (b.repr v i) • b i = v := b.sum_repr v
  have h1 : ∀ i, b.repr v i = v i := by
    intro i; simp [b, EuclideanSpace.basisFun]
  have h2 : ∀ i, b i = EuclideanSpace.single i (1 : ℝ) := by
    intro i
    simp [b, EuclideanSpace.basisFun]
    <;> rfl
  have h_my_sum : ∑ i : Fin n, v i • EuclideanSpace.single i (1 : ℝ) =
      ∑ i : Fin n, (b.repr v i) • b i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [h1 i, h2 i]
  have h3 : ∑ i : Fin n, v i • EuclideanSpace.single i (1 : ℝ) = v := by
    rw [h_my_sum, h_repr]
  exact h3.symm

/-- **Regular set coarea equality.**

On `Rδ := {‖∇u‖ ≥ δ}`, the exact coarea formula holds. -/
lemma regular_set_coarea_equality
    (u : E n → ℝ) (hu : ContDiff ℝ 1 u)
    (h_support : HasCompactSupport u)
    (δ : ℝ) (hδ_pos : 0 < δ) (hn : 2 ≤ n) :
    ∫⁻ (s : ℝ), μHE[n - 1] ({x | ‖fderiv ℝ u x‖ ≥ δ} ∩ {x | u x = s}) =
    ∫⁻ (x : E n) in {x | ‖fderiv ℝ u x‖ ≥ δ},
      ENNReal.ofReal ‖fderiv ℝ u x‖ := by
  cases n with
  | zero => omega
  | succ n' =>
    have hn' : 1 ≤ n' := by omega
    letI : Nonempty (Fin n') := ⟨⟨0, by omega⟩⟩

    let Rδ : Set (E (n' + 1)) := {x | ‖fderiv ℝ u x‖ ≥ δ}
    let K : Set (E (n' + 1)) := tsupport u

    have hK_compact : IsCompact K := by
      have h : IsCompact (tsupport u) := by exact HasCompactSupport.isCompact h_support
      exact h
    have hK_meas : MeasurableSet K := hK_compact.measurableSet

    -- Gradient is zero outside tsupport
    have h_outside : ∀ (x : E (n' + 1)), x ∉ K → fderiv ℝ u x = 0 := by
      intro x hx
      have h2 : IsOpen (Kᶜ) := hK_compact.isClosed.isOpen_compl
      have h3 : x ∈ Kᶜ := hx
      have h4 : ∀ᶠ y in nhds x, y ∈ Kᶜ := h2.mem_nhds h3
      have h5 : u =ᶠ[nhds x] 0 := by
        filter_upwards [h4] with y hy
        have h6 : u y = 0 := by
          by_contra h7
          have h8 : y ∈ closure {z | u z ≠ 0} := subset_closure h7
          have h10 : K = closure {z | u z ≠ 0} := by rfl
          rw [h10] at *
          exact hy h8
        exact h6
      rw [h5.fderiv_eq] <;> simp

    -- Rδ ⊆ K
    have hRδ_sub_K : Rδ ⊆ K := by
      intro x hx
      by_contra h
      have h6 : fderiv ℝ u x = 0 := h_outside x h
      have h7 : ‖fderiv ℝ u x‖ = 0 := by rw [h6] <;> simp
      have h8 : ‖fderiv ℝ u x‖ ≥ δ := by simpa [Rδ] using hx
      rw [h7] at h8
      exact not_le.mpr hδ_pos h8

    have hRδ_closed : IsClosed Rδ := by
      have h_cont : Continuous (fun x : E (n' + 1) => ‖fderiv ℝ u x‖) :=
        (hu.continuous_fderiv (by norm_num)).norm
      exact isClosed_Ici.preimage h_cont

    have hRδ_compact : IsCompact Rδ :=
      hK_compact.of_isClosed_subset hRδ_closed hRδ_sub_K
    have hRδ_meas : MeasurableSet Rδ := hRδ_compact.measurableSet
    have hRδ_bdd : Bornology.IsBounded Rδ := hRδ_compact.isBounded

    -- u is Lipschitz (C¹ with compact support)
    have h_cont_grad : Continuous (fun x : E (n' + 1) => ‖fderiv ℝ u x‖) :=
      (hu.continuous_fderiv (by norm_num)).norm
    have h_bdd_grad : BddAbove ((fun x : E (n' + 1) => ‖fderiv ℝ u x‖) '' K) :=
      hK_compact.bddAbove_image h_cont_grad.continuousOn
    rcases h_bdd_grad with ⟨M, hM⟩
    let M' : ℝ := max M 0
    have hM'_nonneg : 0 ≤ M' := le_max_right _ _
    have h1 : ∀ (x : E (n' + 1)), ‖fderiv ℝ u x‖ ≤ M' := by
      intro x
      by_cases hx : x ∈ K
      · have h2 : ‖fderiv ℝ u x‖ ≤ M := hM ⟨x, hx, rfl⟩
        exact le_trans h2 (le_max_left _ _)
      · have h3 : fderiv ℝ u x = 0 := h_outside x hx
        rw [h3] <;> simp <;> exact hM'_nonneg
    let M_nn : NNReal := ⟨M', hM'_nonneg⟩
    have h2 : ∀ (x : E (n' + 1)), ‖fderiv ℝ u x‖₊ ≤ M_nn := by
      intro x
      exact_mod_cast h1 x
    have h2' : ∀ (x : E (n' + 1)), x ∈ (Set.univ : Set (E (n' + 1))) → ‖fderiv ℝ u x‖₊ ≤ M_nn :=
      fun x _ => h2 x
    have h_diff : ∀ x ∈ (Set.univ : Set (E (n' + 1))), DifferentiableAt ℝ u x :=
      fun x _ => (hu.differentiable (by norm_num)).differentiableAt
    have h3 : LipschitzOnWith M_nn u Set.univ :=
      Convex.lipschitzOnWith_of_nnnorm_fderiv_le h_diff h2' convex_univ
    have h_lip : LipschitzWith M_nn u := by
      simpa [LipschitzOnWith, LipschitzWith] using h3

    -- At each x ∈ Rδ, some partial derivative is nonzero
    have h_dir : ∀ (x : E (n' + 1)), x ∈ Rδ →
        ∃ (j : Fin (n' + 1)), (fderiv ℝ u x) (EuclideanSpace.single j (1 : ℝ)) ≠ 0 := by
      intro x hx
      by_contra h
      push Not at h
      let L := fderiv ℝ u x
      have hL : ∀ (i : Fin (n' + 1)), L (EuclideanSpace.single i (1 : ℝ)) = 0 := h
      have h_basis : ∀ (v : E (n' + 1)), L v = 0 := by
        intro v
        have h_expand : v = ∑ i : Fin (n' + 1), v i • EuclideanSpace.single i (1 : ℝ) :=
          euclidean_basis_expand v
        rw [h_expand]
        have h_sum : L (∑ i : Fin (n' + 1), v i • EuclideanSpace.single i (1 : ℝ)) =
            ∑ i : Fin (n' + 1), L (v i • EuclideanSpace.single i (1 : ℝ)) := by
          exact map_sum L _ _
        rw [h_sum]
        rw [Finset.sum_congr rfl (fun i _ => by rw [L.map_smul, hL i])]
        <;> simp
      have h5 : L = 0 := by
        ext v
        exact h_basis v
      have h6 : ‖L‖ = 0 := by rw [h5] <;> simp
      have h7 : ‖fderiv ℝ u x‖ ≥ δ := by simpa [Rδ] using hx
      rw [h6] at h7
      exact not_le.mpr hδ_pos h7

    -- Total patch function
    have h_patch_total : ∀ (x : E (n' + 1)),
        ∃ (j : Fin (n' + 1)) (φ : OpenPartialHomeomorph (E (n' + 1)) (E (n' + 1)))
          (V : Set (E (n' + 1))),
          IsOpen V ∧ (x ∈ Rδ → x ∈ V ∧ V ⊆ φ.source ∧
            (φ : E (n' + 1) → E (n' + 1)) = patchMap j u ∧
            ContDiffOn ℝ 1 φ.symm φ.target ∧
            ∀ y ∈ V, (fderiv ℝ u y) (EuclideanSpace.single j (1 : ℝ)) ≠ 0) := by
      intro x
      by_cases hx : x ∈ Rδ
      · rcases h_dir x hx with ⟨j, hj⟩
        rcases ift_patch_dir (m := n') u hu j x hj with ⟨φ, V, hxV, hVopen, hVsource, hφcoe, hsymm, hVreg⟩
        refine ⟨j, φ, V, hVopen, fun _ => ⟨hxV, hVsource, hφcoe, hsymm, hVreg⟩⟩
      · let dummy_oph : OpenPartialHomeomorph (E (n' + 1)) (E (n' + 1)) :=
          (Homeomorph.refl (E (n' + 1))).toOpenPartialHomeomorph
        refine ⟨0, dummy_oph, Set.univ, isOpen_univ, fun h => False.elim (hx h)⟩

    choose j φ V hV_open h_patch_prop using h_patch_total

    let idx : Type _ := {x : E (n' + 1) // x ∈ Rδ}
    let U : idx → Set (E (n' + 1)) := fun i => V i.val
    have hU_open : ∀ (i : idx), IsOpen (U i) := fun i => hV_open i.val
    have hU_cover : Rδ ⊆ ⋃ (i : idx), U i := by
      intro y hy
      let i : idx := ⟨y, hy⟩
      have h_yin : y ∈ U i := (h_patch_prop y hy).1
      exact Set.mem_iUnion.mpr ⟨i, h_yin⟩

    rcases hRδ_compact.elim_finite_subcover U hU_open hU_cover with ⟨t, ht_cover⟩

    have h_meas_union : ∀ (s : Finset idx), MeasurableSet (⋃ i ∈ s, U i) := by
      intro s
      apply MeasurableSet.biUnion (Finset.countable_toSet s)
      intro j _
      exact (hU_open j).measurableSet

    have h_patch_data : ∀ (i : idx),
        U i ⊆ (φ i.val).source ∧
        ((φ i.val) : E (n' + 1) → E (n' + 1)) = patchMap (j i.val) u ∧
        ContDiffOn ℝ 1 (φ i.val).symm (φ i.val).target ∧
        ∀ y ∈ U i, (fderiv ℝ u y) (EuclideanSpace.single (j i.val) (1 : ℝ)) ≠ 0 := by
      intro i
      have hprops := (h_patch_prop i.val i.prop).2
      exact hprops

    let fgrad : E (n' + 1) → ENNReal := fun y => ENNReal.ofReal ‖fderiv ℝ u y‖
    have hfgrad_meas : Measurable fgrad := by
      have h_cont : Continuous (fun y : E (n' + 1) => ‖fderiv ℝ u y‖) :=
        (hu.continuous_fderiv (by norm_num)).norm
      exact h_cont.measurable.ennreal_ofReal

    have h_ae_helper : ∀ (S : Set (E (n' + 1))), MeasurableSet S → Bornology.IsBounded S →
        AEMeasurable (fun t : ℝ => μHE[n'] (S ∩ {y | u y = t})) volume := by
      intro S hS_meas hS_bdd
      exact levelSet_aemeasurable_lipschitz (by omega) h_lip hS_meas hS_bdd

    have h_u_meas : Measurable u := hu.continuous.measurable

    -- Induction: for every finite s, the coarea formula holds on Rδ ∩ ⋃ i ∈ s, U i
    have h_induction : ∀ (s : Finset idx),
        AEMeasurable (fun t : ℝ => μHE[n'] ((Rδ ∩ ⋃ i ∈ s, U i) ∩ {y | u y = t})) volume ∧
        ∫⁻ (t : ℝ), μHE[n'] ((Rδ ∩ ⋃ i ∈ s, U i) ∩ {y | u y = t}) =
        ∫⁻ (y : E (n' + 1)) in (Rδ ∩ ⋃ i ∈ s, U i), fgrad y := by
      intro s
      induction s using Finset.induction with
      | empty =>
        have h_empty : (Rδ ∩ ⋃ i ∈ (∅ : Finset idx), U i) = (∅ : Set (E (n' + 1))) := by
          simp
        constructor
        · rw [h_empty]
          simpa using measurable_const.aemeasurable
        · rw [h_empty]
          simp
      | @insert i s hi ih =>
        let A := Rδ ∩ ⋃ j ∈ s, U j
        let B := (Rδ ∩ U i) \ ⋃ j ∈ s, U j
        have hA_meas : MeasurableSet A := hRδ_meas.inter (h_meas_union s)
        have hB_meas : MeasurableSet B :=
          (hRδ_meas.inter (hU_open i).measurableSet).diff (h_meas_union s)
        have hA_bdd : Bornology.IsBounded A := hRδ_bdd.subset (inter_subset_left)
        have hB_bdd : Bornology.IsBounded B := hRδ_bdd.subset (by intro z hz; exact hz.1.1)
        have hB_sub_U : B ⊆ U i := by intro z hz; exact hz.1.2
        rcases h_patch_data i with ⟨hV_source, hφ_eq, hφ_symm, hV_reg⟩
        have hV_reg_B : ∀ y ∈ B, (fderiv ℝ u y) (EuclideanSpace.single (j i.val) (1 : ℝ)) ≠ 0 :=
          fun y hy => hV_reg y (hB_sub_U hy)
        have h_disj : Disjoint A B := by
          rw [Set.disjoint_left]
          intro z hz1 hz2
          exact hz2.2 (show z ∈ ⋃ j ∈ s, U j from hz1.2)
        let S_union := ⋃ j ∈ s, U j
        have h_union2 : (Rδ ∩ S_union) ∪ ((Rδ ∩ U i) \ S_union) =
            Rδ ∩ (S_union ∪ U i) := by
          ext z
          simp only [A, B, S_union, Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
          constructor
          · rintro (h | h)
            · rcases h with ⟨hR, hS⟩
              exact ⟨hR, Or.inl hS⟩
            · rcases h with ⟨⟨hR, hUi⟩, _⟩
              exact ⟨hR, Or.inr hUi⟩
          · rintro ⟨hR, h | h⟩
            · left; exact ⟨hR, h⟩
            · by_cases hS : z ∈ S_union
              · left; exact ⟨hR, hS⟩
              · right; exact ⟨⟨hR, h⟩, hS⟩
        have h_union3 : S_union ∪ U i = ⋃ j ∈ (insert i s), U j := by
          ext z
          simp only [S_union, Set.mem_union, Set.mem_iUnion, Finset.mem_insert]
          constructor
          · rintro (h | h)
            · rcases h with ⟨j, hj, hz⟩
              exact ⟨j, Or.inr hj, hz⟩
            · exact ⟨i, Or.inl rfl, h⟩
          · rintro ⟨j, (rfl | hj), hz⟩
            · exact Or.inr hz
            · exact Or.inl ⟨j, hj, hz⟩
        have h_union : A ∪ B = Rδ ∩ ⋃ j ∈ (insert i s), U j := by
          have h1 : A ∪ B = (Rδ ∩ S_union) ∪ ((Rδ ∩ U i) \ S_union) := by rfl
          rw [h1, h_union2, h_union3]
          <;> rw [Set.inter_distrib_right]
        rcases ih with ⟨hA_ae, hA_coarea⟩
        have hB_ae : AEMeasurable (fun t : ℝ => μHE[n'] (B ∩ {y | u y = t})) volume :=
          h_ae_helper B hB_meas hB_bdd
        have hφ_coe' : ((φ i.val) : E (n' + 1) → E (n' + 1)) =
            fun y => projDir (j i.val) y + u y • EuclideanSpace.single (j i.val) (1 : ℝ) := by
          have h : (φ i.val : E (n' + 1) → E (n' + 1)) = patchMap (j i.val) u := hφ_eq
          rw [h]
          <;> rfl
        have hB_coarea : ∫⁻ (t : ℝ), μHE[n'] (B ∩ {y | u y = t}) =
            ∫⁻ (y : E (n' + 1)) in B, fgrad y :=
          coarea_single_patch_dir_bounded (m := n') u hu (j i.val) (φ i.val)
            hφ_coe' hφ_symm (V := U i) hV_source hV_reg B hB_meas hB_sub_U hB_bdd
        have h_pointwise : ∀ (t : ℝ), μHE[n'] ((A ∪ B) ∩ {y | u y = t}) =
            μHE[n'] (A ∩ {y | u y = t}) + μHE[n'] (B ∩ {y | u y = t}) := by
          intro t
          have h_disj' : Disjoint (A ∩ {y | u y = t}) (B ∩ {y | u y = t}) :=
            h_disj.mono (fun _ h => h.1) (fun _ h => h.1)
          have h_meas1 : MeasurableSet (A ∩ {y | u y = t}) :=
            hA_meas.inter (h_u_meas (measurableSet_singleton t))
          have h_meas2 : MeasurableSet (B ∩ {y | u y = t}) :=
            hB_meas.inter (h_u_meas (measurableSet_singleton t))
          have h_eq : (A ∪ B) ∩ {y | u y = t} =
              (A ∩ {y | u y = t}) ∪ (B ∩ {y | u y = t}) := by
            rw [Set.union_inter_distrib_right]
          rw [h_eq]
          exact measure_union h_disj' h_meas2
        have h_ae_union : AEMeasurable (fun t : ℝ => μHE[n'] ((A ∪ B) ∩ {y | u y = t})) volume := by
          have h_eq_fun : (fun t : ℝ => μHE[n'] ((A ∪ B) ∩ {y | u y = t})) =
              fun t => μHE[n'] (A ∩ {y | u y = t}) + μHE[n'] (B ∩ {y | u y = t}) :=
            funext h_pointwise
          rw [h_eq_fun]
          exact hA_ae.add hB_ae
        rcases hA_ae with ⟨fA', hfA'_meas, hfA'_eq⟩
        rcases hB_ae with ⟨fB', hfB'_meas, hfB'_eq⟩
        have h_sum_ae : (fun t : ℝ => μHE[n'] (A ∩ {y | u y = t}) + μHE[n'] (B ∩ {y | u y = t})) =ᵐ[volume]
            (fA' + fB') := hfA'_eq.add hfB'_eq
        have h_lint_add : ∫⁻ (t : ℝ), μHE[n'] ((A ∪ B) ∩ {y | u y = t}) =
            (∫⁻ t, μHE[n'] (A ∩ {y | u y = t})) + (∫⁻ t, μHE[n'] (B ∩ {y | u y = t})) := by
          have h1 : (fun t : ℝ => μHE[n'] ((A ∪ B) ∩ {y | u y = t})) =
              fun t => μHE[n'] (A ∩ {y | u y = t}) + μHE[n'] (B ∩ {y | u y = t}) :=
            funext h_pointwise
          rw [h1]
          rw [lintegral_congr_ae h_sum_ae]
          have h_eqA : ∫⁻ (t : ℝ), μHE[n'] (A ∩ {y | u y = t}) = ∫⁻ (t : ℝ), fA' t :=
            lintegral_congr_ae hfA'_eq
          have h_eqB : ∫⁻ (t : ℝ), μHE[n'] (B ∩ {y | u y = t}) = ∫⁻ (t : ℝ), fB' t :=
            lintegral_congr_ae hfB'_eq
          rw [h_eqA, h_eqB]
          have h : ∫⁻ (a : ℝ), fA' a + fB' a = (∫⁻ (a : ℝ), fA' a) + (∫⁻ (a : ℝ), fB' a) :=
            MeasureTheory.lintegral_add_left (μ := volume) hfA'_meas fB'
          have h_eq1 : (fun a : ℝ => fA' a + fB' a) = (fA' + fB') := by funext a; rfl
          rw [← h_eq1]
          exact h
        have h_restrict : Measure.restrict volume (A ∪ B) =
            Measure.restrict volume A + Measure.restrict volume B := by
          rw [Measure.restrict_union h_disj hB_meas]
        have h_grad_add : ∫⁻ (y : E (n' + 1)) in (A ∪ B), fgrad y =
            (∫⁻ (y : E (n' + 1)) in A, fgrad y) + ∫⁻ (y : E (n' + 1)) in B, fgrad y := by
          rw [h_restrict]
          convert MeasureTheory.lintegral_add_measure fgrad
            (Measure.restrict volume A) (Measure.restrict volume B)
          <;> rfl
        have h_set_eq : (Rδ ∩ ⋃ j ∈ (insert i s), U j) = A ∪ B := h_union.symm
        have hA_coarea' : ∫⁻ t, μHE[n'] (A ∩ {y | u y = t}) = ∫⁻ y in A, fgrad y := by
          simpa [A] using hA_coarea
        refine' ⟨_, _⟩
        · rw [h_set_eq]
          exact h_ae_union
        · rw [h_set_eq]
          rw [h_lint_add, hA_coarea', hB_coarea, h_grad_add]

    have h_final := h_induction t
    have hS_eq : (Rδ ∩ ⋃ i ∈ t, U i) = Rδ := by
      rw [Set.inter_eq_left]
      exact ht_cover
    rcases h_final with ⟨_, h_main⟩
    rw [hS_eq] at h_main
    exact h_main

end Geometry
