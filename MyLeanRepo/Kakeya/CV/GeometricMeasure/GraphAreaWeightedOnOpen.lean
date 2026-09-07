import MyLeanRepo.Kakeya.CV.GeometricMeasure.GraphAreaWeighted
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Weighted graph area formula on an open domain

The global weighted graph-area formula extends to functions that are C¹ only
on an open set, provided the measured base set is contained in that domain.
The proof exhausts the open set by compact subsets and uses smooth cutoffs to
construct global C¹ extensions on the disjoint exhaustion pieces.
-/

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal Real

namespace Kakeya.CV

/-- Weighted graph area formula for a function that is C¹ on an open
neighborhood of the measured base set. -/
theorem graph_area_formula_weighted_on_open
    {g : R2 → ℝ} {A : Set R2} (hA : IsOpen A)
    (hg : ContDiffOn ℝ 1 g A)
    {B : Set R2} (hB : MeasurableSet B) (hB_sub : B ⊆ A)
    {f : R3 → ENNReal} (hf : Measurable f) :
    ∫⁻ z in graphMap g '' B, f z ∂μH[2] =
      ∫⁻ y in B, f (graphMap g y) * areaFactor g y ∂volume := by
  by_cases hA_univ : A = Set.univ
  · have hg' : ContDiff ℝ 1 g := by
      rw [hA_univ, contDiffOn_univ] at hg
      exact hg
    exact graph_area_formula_weighted g hg' hB hf
  · have hA_compl_nonempty : Aᶜ.Nonempty := by
      simpa [Set.nonempty_iff_ne_empty, compl_ne_univ] using hA_univ
    let C : ℕ → Set R2 := fun n =>
      closedBall (0 : R2) (n : ℝ) ∩
        {y | 1 / (n + 1 : ℝ) ≤ infDist y Aᶜ}
    have hC_closed : ∀ n, IsClosed (C n) := by
      intro n
      exact isClosed_closedBall.inter
        (isClosed_le continuous_const (Metric.continuous_infDist_pt Aᶜ))
    have hC_compact : ∀ n, IsCompact (C n) := by
      intro n
      exact (isCompact_closedBall (0 : R2) (n : ℝ)).inter_right
        (isClosed_le continuous_const (Metric.continuous_infDist_pt Aᶜ))
    have hC_meas : ∀ n, MeasurableSet (C n) :=
      fun n => (hC_closed n).measurableSet
    have hC_sub_A : ∀ n, C n ⊆ A := by
      intro n y hy
      have hthreshold : 0 < (1 : ℝ) / (n + 1) := by positivity
      have hdist : 0 < infDist y Aᶜ :=
        hthreshold.trans_le hy.2
      by_contra hyA
      have hyc : y ∈ Aᶜ := hyA
      rw [Metric.infDist_zero_of_mem hyc] at hdist
      exact lt_irrefl 0 hdist
    have hC_mono : Monotone C := by
      intro n m hnm y hy
      constructor
      · exact closedBall_subset_closedBall (by exact_mod_cast hnm) hy.1
      · have hnm' : (n + 1 : ℝ) ≤ m + 1 := by
          exact_mod_cast Nat.add_le_add_right hnm 1
        exact (one_div_le_one_div_of_le (by positivity) hnm').trans hy.2
    have hC_cover : A ⊆ ⋃ n, C n := by
      intro y hy
      have hyc : y ∉ Aᶜ := by simpa
      have hdist : 0 < infDist y Aᶜ :=
        ((hA.isClosed_compl.notMem_iff_infDist_pos hA_compl_nonempty).mp hyc)
      obtain ⟨n, hn⟩ :=
        exists_nat_gt (max ‖y‖ (1 / infDist y Aᶜ))
      have hnorm : ‖y‖ ≤ (n : ℝ) :=
        (le_max_left _ _).trans hn.le
      have hrecip : 1 / infDist y Aᶜ ≤ (n + 1 : ℝ) := by
        have hlt : 1 / infDist y Aᶜ < (n : ℝ) :=
          (le_max_right _ _).trans_lt hn
        linarith
      have hthreshold : 1 / (n + 1 : ℝ) ≤ infDist y Aᶜ :=
        (one_div_le (by positivity) hdist).2 hrecip
      exact Set.mem_iUnion.mpr
        ⟨n, ⟨by simpa [mem_closedBall, dist_zero_right] using hnorm,
          hthreshold⟩⟩
    have h_extension : ∀ n, ∃ (g' : R2 → ℝ) (U : Set R2),
        IsOpen U ∧ C n ⊆ U ∧ ContDiff ℝ 1 g' ∧
          EqOn g' g U ∧ EqOn (fderiv ℝ g') (fderiv ℝ g) U := by
      intro n
      let K := C n
      have hK_compact : IsCompact K := hC_compact n
      have hK_sub_A : K ⊆ A := hC_sub_A n
      have hlocal : ∀ y : K, ∃ r : ℝ,
          0 < r ∧ ball (y : R2) (3 * r) ⊆ A := by
        intro y
        have hnhds : A ∈ nhds (y : R2) :=
          hA.mem_nhds (hK_sub_A y.property)
        rcases Metric.mem_nhds_iff.mp hnhds with ⟨r, hr, hball⟩
        refine ⟨r / 3, by positivity, ?_⟩
        convert hball using 1 <;> ring_nf
      choose r hr hball using hlocal
      have hcover : K ⊆ ⋃ y : K, ball (y : R2) (r y) := by
        intro y hy
        exact Set.mem_iUnion.mpr
          ⟨⟨y, hy⟩, mem_ball_self (hr ⟨y, hy⟩)⟩
      rcases hK_compact.elim_finite_subcover
          (fun y : K => ball (y : R2) (r y))
          (fun _ => isOpen_ball) hcover with ⟨F, hF_cover⟩
      let bump : (y : K) → ContDiffBump (y : R2) := fun y =>
        ⟨r y, 2 * r y, hr y, by linarith [hr y]⟩
      let ψ : R2 → ℝ := fun z =>
        1 - ∏ y ∈ F, (1 - bump y z)
      have hψ_diff : ContDiff ℝ 1 ψ := by
        apply contDiff_const.sub
        apply contDiff_prod
        intro y _
        exact contDiff_const.sub (bump y).contDiff
      let U : Set R2 := ⋃ y ∈ F, ball (y : R2) (r y)
      have hU_open : IsOpen U := by
        apply isOpen_iUnion
        intro y
        apply isOpen_iUnion
        intro _
        exact isOpen_ball
      have hK_sub_U : K ⊆ U := hF_cover
      have hψ_one : EqOn ψ 1 U := by
        intro z hz
        rcases Set.mem_iUnion₂.mp hz with ⟨y, hyF, hz⟩
        have hyone : bump y z = 1 :=
          (bump y).one_of_mem_closedBall (ball_subset_closedBall hz)
        have hprod : ∏ y' ∈ F, (1 - bump y' z) = 0 := by
          apply Finset.prod_eq_zero hyF
          rw [hyone]
          norm_num
        simp [ψ, hprod]
      have hψ_tsupport : tsupport ψ ⊆ A := by
        have hsupp :
            Function.support ψ ⊆ ⋃ y ∈ F, ball (y : R2) (2 * r y) := by
          intro z hz
          by_contra hzunion
          have hzero : ∀ y ∈ F, bump y z = 0 := by
            intro y hyF
            have hzball : z ∉ ball (y : R2) (2 * r y) := by
              intro hzball
              exact hzunion (Set.mem_iUnion₂.mpr ⟨y, hyF, hzball⟩)
            have hout : 2 * r y ≤ dist z (y : R2) := by
              simpa [mem_ball, not_lt] using hzball
            exact (bump y).zero_of_le_dist hout
          have hprod : ∏ y ∈ F, (1 - bump y z) = 1 := by
            apply Finset.prod_eq_one
            intro y hyF
            rw [hzero y hyF]
            norm_num
          exact hz (by simp [ψ, hprod])
        have hsupp_closed :
            Function.support ψ ⊆
              ⋃ y ∈ F, closedBall (y : R2) (2 * r y) := by
          intro z hz
          rcases Set.mem_iUnion₂.mp (hsupp hz) with ⟨y, hyF, hzball⟩
          exact Set.mem_iUnion₂.mpr
            ⟨y, hyF, ball_subset_closedBall hzball⟩
        have hclosed :
            IsClosed (⋃ y ∈ F, closedBall (y : R2) (2 * r y)) :=
          isClosed_biUnion_finset fun _ _ => isClosed_closedBall
        have htsupp :
            tsupport ψ ⊆
              ⋃ y ∈ F, closedBall (y : R2) (2 * r y) := by
          exact closure_minimal hsupp_closed hclosed
        intro z hz
        rcases Set.mem_iUnion₂.mp (htsupp hz) with
          ⟨y, hyF, hzball⟩
        apply hball y
        exact (closedBall_subset_ball (by linarith [hr y])) hzball
      let g' : R2 → ℝ := fun z => ψ z * g z
      have hg'_diff : ContDiff ℝ 1 g' := by
        have h_inside : ContDiffOn ℝ 1 g' A :=
          hψ_diff.contDiffOn.mul hg
        have h_outside : ContDiffOn ℝ 1 g' (tsupport ψ)ᶜ := by
          have heq : EqOn g' 0 (tsupport ψ)ᶜ := by
            intro z hz
            have hψz : ψ z = 0 := by
              by_contra hne
              exact hz (subset_tsupport ψ hne)
            simp [g', hψz]
          exact contDiff_const.contDiffOn.congr heq
        have hunion : A ∪ (tsupport ψ)ᶜ = Set.univ := by
          apply Set.eq_univ_of_forall
          intro z
          by_cases hz : z ∈ A
          · exact Or.inl hz
          · exact Or.inr fun hzsupp => hz (hψ_tsupport hzsupp)
        have hglobal : ContDiffOn ℝ 1 g' (A ∪ (tsupport ψ)ᶜ) :=
          h_inside.union_of_isOpen h_outside hA
            (isClosed_tsupport ψ).isOpen_compl
        rw [hunion, contDiffOn_univ] at hglobal
        exact hglobal
      have hg'_eq : EqOn g' g U := by
        intro z hz
        simp [g', hψ_one hz]
      have hg'_fderiv :
          EqOn (fderiv ℝ g') (fderiv ℝ g) U := by
        intro z hz
        have heq : g' =ᶠ[nhds z] g := by
          filter_upwards [hU_open.mem_nhds hz] with w hw
          exact hg'_eq hw
        exact heq.fderiv_eq
      exact ⟨g', U, hU_open, hK_sub_U, hg'_diff, hg'_eq,
        hg'_fderiv⟩
    choose g' U hU_open hC_sub_U hg'_diff hg'_eq hg'_fderiv
      using h_extension
    let Q : ℕ → Set R2 := fun n => B ∩ C n
    let D : ℕ → Set R2 := disjointed Q
    have hQ_meas : ∀ n, MeasurableSet (Q n) :=
      fun n => hB.inter (hC_meas n)
    have hD_meas : ∀ n, MeasurableSet (D n) :=
      MeasurableSet.disjointed hQ_meas
    have hD_disjoint : Pairwise fun n m => Disjoint (D n) (D m) :=
      disjoint_disjointed Q
    have hQ_union : (⋃ n, Q n) = B := by
      apply Set.Subset.antisymm
      · intro y hy
        rcases Set.mem_iUnion.mp hy with ⟨n, hyn⟩
        exact hyn.1
      · intro y hy
        rcases Set.mem_iUnion.mp (hC_cover (hB_sub hy)) with ⟨n, hyn⟩
        exact Set.mem_iUnion.mpr ⟨n, ⟨hy, hyn⟩⟩
    have hD_union : (⋃ n, D n) = B := by
      change (⋃ n, disjointed Q n) = B
      rw [iUnion_disjointed, hQ_union]
    have hD_sub_C : ∀ n, D n ⊆ C n := by
      intro n
      exact (disjointed_subset Q n).trans inter_subset_right
    have h_per_piece : ∀ n,
        ∫⁻ z in graphMap g '' D n, f z ∂μH[2] =
          ∫⁻ y in D n,
            f (graphMap g y) * areaFactor g y ∂volume := by
      intro n
      have hsub : D n ⊆ U n :=
        (hD_sub_C n).trans (hC_sub_U n)
      have hgraph_eq :
          graphMap (g' n) '' D n = graphMap g '' D n := by
        apply Set.image_congr
        intro y hy
        simp [graphMap, hg'_eq n (hsub hy)]
      have hfactor_eq : ∀ y ∈ D n,
          areaFactor (g' n) y = areaFactor g y := by
        intro y hy
        simp [areaFactor, hg'_fderiv n (hsub hy)]
      have hglobal :=
        graph_area_formula_weighted (g' n) (hg'_diff n)
          (hD_meas n) hf
      rw [hgraph_eq] at hglobal
      refine hglobal.trans ?_
      apply MeasureTheory.setLIntegral_congr_fun (hD_meas n)
      intro y hy
      change f (graphMap (g' n) y) * areaFactor (g' n) y =
        f (graphMap g y) * areaFactor g y
      rw [show graphMap (g' n) y = graphMap g y by
        simp [graphMap, hg'_eq n (hsub hy)]]
      rw [hfactor_eq y hy]
    have hgraph_disjoint : Pairwise fun n m =>
        Disjoint (graphMap g '' D n) (graphMap g '' D m) := by
      intro n m hnm
      exact (hD_disjoint hnm).image
        (graphMap_injective g).injOn (subset_univ _) (subset_univ _)
    have hgraph_meas : ∀ n, MeasurableSet (graphMap g '' D n) := by
      intro n
      have hsub : D n ⊆ U n :=
        (hD_sub_C n).trans (hC_sub_U n)
      have hgraph_eq :
          graphMap g '' D n = graphMap (g' n) '' D n := by
        apply Set.image_congr
        intro y hy
        simp [graphMap, hg'_eq n (hsub hy)]
      rw [hgraph_eq]
      let h_emb :=
        graphMap_measurableEmbedding (hg'_diff n).continuous
      exact h_emb.measurableSet_image.mpr (hD_meas n)
    have himage_union :
        (⋃ n, graphMap g '' D n) = graphMap g '' B := by
      rw [← Set.image_iUnion, hD_union]
    have hlhs :
        ∫⁻ z in graphMap g '' B, f z ∂μH[2] =
          ∑' n, ∫⁻ z in graphMap g '' D n, f z ∂μH[2] := by
      rw [← himage_union]
      exact lintegral_iUnion hgraph_meas hgraph_disjoint f
    have hrhs :
        ∫⁻ y in B, f (graphMap g y) * areaFactor g y ∂volume =
          ∑' n, ∫⁻ y in D n,
            f (graphMap g y) * areaFactor g y ∂volume := by
      rw [← hD_union]
      exact lintegral_iUnion hD_meas hD_disjoint _
    rw [hlhs, hrhs]
    congr with n
    exact h_per_piece n

end Kakeya.CV
